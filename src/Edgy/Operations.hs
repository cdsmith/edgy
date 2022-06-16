{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneKindSignatures #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}

module Edgy.Operations where

import Control.Monad (forM_)
import Data.Binary (Binary)
import Data.Dependent.Map (DMap)
import qualified Data.Dependent.Map as DMap
import Data.Kind (Type)
import Data.List ((\\))
import Data.TCache
  ( STM,
    delDBRef,
    getDBRef,
    newDBRef,
    readDBRef,
    safeIOToSTM,
    writeDBRef,
  )
import Data.Type.Equality (testEquality, (:~:) (..))
import Data.Typeable (Proxy (..), Typeable)
import qualified Data.UUID as UUID
import qualified Data.UUID.V4 as UUID
import Edgy.Cardinality (KnownCardinality (..), Numerous)
import Edgy.Node
  ( AttributeKey (..),
    AttributeVal (..),
    Node (..),
    NodeImpl (..),
    Nodes (..),
    RelatedKey (..),
    RelatedVal (..),
    emptyNodeImpl,
    relatedKey,
  )
import Edgy.Schema
  ( AttributeSpec (..),
    AttributeType,
    Constructor,
    ExistenceSpec,
    HasAttribute,
    HasNode,
    HasRelation,
    KnownSchema,
    Mutability (..),
    NodeType (..),
    RelationName,
    RelationSpec (..),
    Schema,
    Target,
    TargetCardinality,
    UniversalSpec,
    attributeDefault,
    foldConstructor,
    foldRelations,
    mapConstructor,
  )
import GHC.TypeLits (KnownSymbol, Symbol, symbolVal)
import Type.Reflection (TypeRep, typeRep)

type Edgy :: Schema -> Type -> Type
newtype Edgy schema a = Edgy {runEdgy :: STM a}
  deriving (Functor, Applicative, Monad)

liftSTM :: forall (schema :: Schema) {a}. STM a -> Edgy schema a
liftSTM = Edgy

getEdges ::
  forall (spec :: RelationSpec) {nodeType :: NodeType} {schema :: Schema}.
  ( KnownSchema schema,
    Typeable nodeType,
    Typeable spec,
    KnownSymbol (RelationName spec),
    Typeable (Target spec)
  ) =>
  Node schema nodeType ->
  STM [Node schema (Target spec)]
getEdges (Node ref) =
  readDBRef ref >>= \case
    Just (NodeImpl uuid _ relations) -> do
      let result = DMap.lookup (RelatedKey (typeRep :: TypeRep spec)) relations
          nref = case result of
            Just (RelatedVal r) -> r
            Nothing -> getDBRef (relatedKey uuid (Proxy @spec))
      readDBRef nref >>= \case
        Just (Nodes _ ns) -> return ns
        Nothing -> return []
    Nothing -> error ("node not found: " ++ show ref)

modifyEdges ::
  forall (spec :: RelationSpec) {nodeType :: NodeType} {schema :: Schema}.
  ( KnownSchema schema,
    Typeable nodeType,
    Typeable spec,
    KnownSymbol (RelationName spec),
    Typeable (Target spec)
  ) =>
  Node schema nodeType ->
  ([Node schema (Target spec)] -> [Node schema (Target spec)]) ->
  STM ()
modifyEdges (Node ref) f =
  readDBRef ref >>= \case
    Just (NodeImpl uuid attrs relations) -> do
      let rkey = RelatedKey (typeRep :: TypeRep spec)
      nref <- case DMap.lookup rkey relations of
        Just (RelatedVal nref) -> return nref
        Nothing -> do
          let nref = getDBRef (relatedKey uuid (Proxy @spec))
          writeDBRef
            ref
            (NodeImpl uuid attrs (DMap.insert rkey (RelatedVal nref) relations))
          return nref
      readDBRef nref >>= \case
        Just (Nodes _ ns) -> writeDBRef nref (Nodes uuid (f ns))
        Nothing -> writeDBRef nref (Nodes uuid (f []))
    Nothing -> error ("node not found: " ++ show ref)

getUniverse :: KnownSchema schema => Edgy schema (Node schema Universe)
getUniverse = Edgy $ do
  let ref = getDBRef (show UUID.nil)
  readDBRef ref >>= \case
    Just _ -> return (Node ref)
    Nothing -> Node <$> newDBRef (emptyNodeImpl UUID.nil)

newNode ::
  forall (schema :: Schema) (typeName :: Symbol) {attrs :: [AttributeSpec]}.
  (KnownSymbol typeName, HasNode schema (DataNode typeName) attrs) =>
  Constructor attrs (Edgy schema (Node schema (DataNode typeName)))
newNode =
  mapConstructor (Proxy @(DataNode typeName)) (Proxy @attrs) mkNode $
    ( foldConstructor
        (Proxy @(DataNode typeName))
        (Proxy @attrs)
        setAttr
        DMap.empty
    )
  where
    setAttr ::
      forall (attr :: AttributeSpec).
      (Typeable attr, Binary (AttributeType attr)) =>
      Proxy attr ->
      AttributeType attr ->
      DMap (AttributeKey schema) (AttributeVal schema) ->
      DMap (AttributeKey schema) (AttributeVal schema)
    setAttr (_ :: Proxy attr) val attrs =
      DMap.insert (AttributeKey @attr @schema typeRep) (AttributeVal val) attrs

    mkNode attrs = Edgy @schema $ do
      uuid <- safeIOToSTM UUID.nextRandom
      node <- Node <$> newDBRef (NodeImpl uuid attrs DMap.empty)
      let universe = Node (getDBRef (show UUID.nil)) :: Node schema Universe
      modifyEdges @(ExistenceSpec typeName) universe (node :)
      modifyEdges @(UniversalSpec typeName) node (const [universe])
      return node

deleteNode ::
  forall (typeName :: Symbol) {schema :: Schema} {attrs :: [AttributeSpec]}.
  (KnownSymbol typeName, HasNode schema (DataNode typeName) attrs) =>
  Node schema (DataNode typeName) ->
  Edgy schema ()
deleteNode node@(Node ref) = Edgy $ do
  foldRelations
    (Proxy @schema)
    (Proxy @(DataNode typeName))
    ( \(_ :: Proxy relation) (_ :: Proxy inverse) delRemaining -> do
        case testEquality
          (typeRep @(DataNode typeName))
          (typeRep @(Target inverse)) of
          Just Refl -> do
            nodes <- getEdges @relation node
            forM_ nodes $ \n -> do
              modifyEdges @inverse n (filter (/= node))
          _ -> return ()
        delRemaining
    )
    (return ())
  delDBRef ref

getAttribute ::
  forall
    (name :: Symbol)
    {schema :: Schema}
    {nodeType :: NodeType}
    {attr :: AttributeSpec}.
  HasAttribute schema nodeType name attr =>
  Node schema nodeType ->
  Edgy schema (AttributeType attr)
getAttribute (Node ref) = Edgy $ do
  nodeImpl <- readDBRef ref
  case nodeImpl of
    Just (NodeImpl _ attrs _) ->
      case DMap.lookup (AttributeKey (typeRep :: TypeRep attr)) attrs of
        Just (AttributeVal val) -> return val
        Nothing -> case attributeDefault (Proxy @schema) (Proxy @nodeType) (Proxy @name) of
          Just def -> return def
          Nothing ->
            error
              ( "getAttribute: Required attribute not defined: "
                  ++ symbolVal (Proxy @name)
                  ++ " on "
                  ++ show ref
              )
    Nothing -> error ("getAttribute: node not found: " ++ show ref)

setAttribute ::
  forall
    (name :: Symbol)
    {schema :: Schema}
    {nodeType :: NodeType}
    {attr :: AttributeSpec}.
  HasAttribute schema nodeType name attr =>
  Node schema nodeType ->
  AttributeType attr ->
  Edgy schema ()
setAttribute (Node ref) value = Edgy $ do
  nodeImpl <- readDBRef ref
  case nodeImpl of
    Just (NodeImpl uuid attrs relations) ->
      writeDBRef
        ref
        ( NodeImpl
            uuid
            ( DMap.insert
                (AttributeKey (typeRep :: TypeRep attr))
                (AttributeVal value)
                attrs
            )
            relations
        )
    Nothing -> error ("setAttribute: node not found: " ++ show ref)

getRelated ::
  forall
    (relation :: Symbol)
    {schema :: Schema}
    {nodeType :: NodeType}
    {spec :: RelationSpec}
    {inverse :: RelationSpec}
    {mutability :: Mutability}.
  HasRelation schema nodeType relation spec inverse mutability =>
  Node schema nodeType ->
  Edgy schema (Numerous (TargetCardinality spec) (Node schema (Target spec)))
getRelated node = Edgy $ do
  listToNumerous @(TargetCardinality spec) <$> getEdges @spec node >>= \case
    Just result -> return result
    Nothing -> error "getRelated: bad cardinality"

isRelated ::
  forall
    (relation :: Symbol)
    {schema :: Schema}
    {nodeType :: NodeType}
    {spec :: RelationSpec}
    {inverse :: RelationSpec}
    {mutability :: Mutability}.
  HasRelation schema nodeType relation spec inverse mutability =>
  Node schema nodeType ->
  Node schema (Target spec) ->
  Edgy schema Bool
isRelated node target = Edgy $ elem target <$> getEdges @spec node

setRelated ::
  forall
    (relation :: Symbol)
    {schema :: Schema}
    {nodeType :: NodeType}
    {spec :: RelationSpec}
    {inverse :: RelationSpec}.
  HasRelation schema nodeType relation spec inverse Mutable =>
  Node schema nodeType ->
  Numerous (TargetCardinality spec) (Node schema (Target spec)) ->
  Edgy schema ()
setRelated a target = Edgy $ do
  oldNodes <- getEdges @spec a
  let newNodes = numerousToList @(TargetCardinality spec) target
  modifyEdges @spec a (const newNodes)
  forM_ (oldNodes \\ newNodes) $ \b -> modifyEdges @inverse b (filter (/= a))
  forM_ (newNodes \\ oldNodes) $ \b -> modifyEdges @inverse b (a :)

addRelated ::
  forall
    (relation :: Symbol)
    {schema :: Schema}
    {nodeType :: NodeType}
    {spec :: RelationSpec}
    {inverse :: RelationSpec}.
  HasRelation schema nodeType relation spec inverse Mutable =>
  Node schema nodeType ->
  Node schema (Target spec) ->
  Edgy schema ()
addRelated a b = Edgy $ do
  modifyEdges @spec a (b :)
  modifyEdges @inverse b (a :)

removeRelated ::
  forall
    (relation :: Symbol)
    {schema :: Schema}
    {nodeType :: NodeType}
    {spec :: RelationSpec}
    {inverse :: RelationSpec}.
  HasRelation schema nodeType relation spec inverse Mutable =>
  Node schema nodeType ->
  Node schema (Target spec) ->
  Edgy schema ()
removeRelated a b = Edgy $ do
  modifyEdges @spec a (filter (/= b))
  modifyEdges @inverse b (filter (/= a))

clearRelated ::
  forall
    (relation :: Symbol)
    {schema :: Schema}
    {nodeType :: NodeType}
    {spec :: RelationSpec}
    {inverse :: RelationSpec}.
  HasRelation schema nodeType relation spec inverse Mutable =>
  Node schema nodeType ->
  Edgy schema ()
clearRelated node = Edgy $ do
  nodes <- getEdges @spec node
  forM_ nodes $ \n -> do
    modifyEdges @inverse n (filter (/= node))
  modifyEdges @spec node (const [])

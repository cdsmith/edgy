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

module Edgy
  ( -- * The Edgy monad
    Edgy,
    runEdgy,

    -- * Nodes and operations
    Node,
    getUniverse,
    newNode,
    deleteNode,
    getAttribute,
    setAttribute,
    getRelated,
    isRelated,
    setRelated,
    addRelated,
    removeRelated,
    clearRelated,

    -- * Schema types
    NodeType (..),
    Schema,
    SchemaDef (..),
    Cardinality (..),
    Numerous,
    AttributeSpec (..),
    AttributeType,
    RelationSpec (..),
    Target,
    TargetCardinality,
    Mutability (..),
    HasNode,
    HasAttribute,
    HasRelation,
    SchemaValidator (..),
  )
where

import Edgy.Cardinality (Cardinality (..), Numerous)
import Edgy.Node (Node)
import Edgy.Operations
  ( Edgy (runEdgy),
    addRelated,
    clearRelated,
    deleteNode,
    getAttribute,
    getRelated,
    getUniverse,
    isRelated,
    newNode,
    removeRelated,
    setAttribute,
    setRelated,
  )
import Edgy.Schema
  ( AttributeSpec (..),
    AttributeType,
    HasAttribute,
    HasNode,
    HasRelation,
    Mutability (..),
    NodeType (..),
    RelationSpec (..),
    Schema,
    SchemaDef (..),
    SchemaValidator (..),
    Target,
    TargetCardinality,
  )

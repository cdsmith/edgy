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
    liftSTM,

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
    AttributeSpec (..),
    AttributeType,
    HasNode,
    HasAttribute,
    HasRelation,

    -- * The IsNode class
    IsNode (..),
  )
where

import Edgy.Cardinality (Cardinality (..))
import Edgy.IsNode (IsNode (..))
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
    liftSTM,
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
    NodeType (..),
    Schema,
    SchemaDef (..),
  )

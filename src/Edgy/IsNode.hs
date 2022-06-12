{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeFamilies #-}

module Edgy.IsNode where

import Edgy.Node (Node (..))
import Edgy.Operations (Edgy, newNode)
import Edgy.Schema (HasNode, NodeType (..))
import GHC.TypeLits (KnownSymbol, Symbol)

class
  HasNode schema (DataNode (NodeName schema record)) =>
  IsNode schema record
  where
  type NodeName schema record :: Symbol

  get ::
    Node schema (DataNode (NodeName schema record)) ->
    Edgy schema record
  set ::
    Node schema (DataNode (NodeName schema record)) ->
    record ->
    Edgy schema ()

  new ::
    KnownSymbol (NodeName schema record) =>
    record ->
    Edgy schema (Node schema (DataNode (NodeName schema record)))
  new record = do
    node <- newNode
    set node record
    return node

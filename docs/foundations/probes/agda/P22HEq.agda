-- Outcome on 2026-10-07 with Agda 2.8.0: rejected, [CoInfectiveImport] Importing module Relation.Binary.HeterogeneousEquality not using
{-# OPTIONS --safe --cubical-compatible #-}
module P22HEq where
-- stdlib's heterogeneous equality is a --with-K module
open import Relation.Binary.HeterogeneousEquality using (_≅_; refl)

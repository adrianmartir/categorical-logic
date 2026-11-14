/-
Copyright (c) 2026 Adrian Marti. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adrian Marti
-/

module

public import CategoricalLogic.Operad
public import CategoricalLogic.Designs.Bespoke.Cells
public import CategoricalLogic.Designs.Bespoke.Transport

/-!
# `Cat.freeMon` is a monad of profunctors

The instance `MonadProf Cat.freeMon` of the current design (`CategoricalLogic.Operad`), with all
fifteen laws. Every law is of the form `s = t.cast hF hG` and is reduced by
`Square.eq_cast_of_heq` (and its nullary and binary versions) to a pointwise `HEq`, proved in
`CategoricalLogic.Designs.Bespoke.Cells` by induction on the lists.
-/

@[expose] public section

namespace CategoryTheory

universe w v u

open Profunctor FreeMon FreeMon.ProfApp

instance Cat.freeMon.monadProf : MonadProf.{u, v, w} Cat.freeMon.{v, u} where
  mapProf P := prof P
  mapSquare _ _ s := FreeMon.mapSquare s
  mapNullary _ _ ν := FreeMon.mapNullary ν
  mapBinary _ _ β := FreeMon.mapBinary β
  mapSquare_id _ := Square.eq_cast_of_heq _ _ fun e => mapSq_id_heq e
  mapSquare_vComp s t := Square.eq_cast_of_heq _ _ fun e => mapSq_vComp_heq s t e
  mapNullary_vComp ν t := NullaryCell.eq_cast_of_heq _ _ fun A => mapNu_vComp_heq ν t A.as
  mapNullary_comap _ ν := NullaryCell.eq_cast_of_heq _ _ fun A => mapNu_comap_heq ν _ A.as
  mapBinary_vComp β t := BinaryCell.eq_cast_of_heq _ _ fun e e' => mapBi_vComp_heq β t e e'
  mapBinary_precomp s s' β :=
    BinaryCell.eq_cast_of_heq _ _ fun e e' => mapBi_precomp_heq β s s' e e'
  ηCell P := FreeMon.ηCell P
  μCell P := FreeMon.μCell P
  ηCell_square _ := Square.eq_cast_of_heq _ _ fun _ => HEq.rfl
  ηCell_nullary _ := NullaryCell.eq_cast_of_heq _ _ fun _ => HEq.rfl
  ηCell_binary _ := BinaryCell.eq_cast_of_heq _ _ fun _ _ => HEq.rfl
  μCell_square s := Square.eq_cast_of_heq _ _ fun e => flat_mapSq_heq s e
  μCell_nullary ν := NullaryCell.eq_cast_of_heq _ _ fun A => flat_mapNu_heq ν A.as
  μCell_binary β := BinaryCell.eq_cast_of_heq _ _ fun e e' => flat_mapBi_heq β e e'
  ηCell_μCell _ := Square.eq_cast_of_heq _ _ fun e => append_nil_heq e
  mapSquare_ηCell_μCell _ := Square.eq_cast_of_heq _ _ fun e => flat_mapSq_ηCell_heq e
  μCell_assoc _ := Square.eq_cast_of_heq _ _ fun e => flat_flat_heq e

end CategoryTheory

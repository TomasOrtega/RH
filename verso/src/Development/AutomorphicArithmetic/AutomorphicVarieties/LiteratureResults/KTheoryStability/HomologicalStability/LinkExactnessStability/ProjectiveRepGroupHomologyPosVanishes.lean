import Mathlib
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.PermRepSingle

open CategoryTheory CategoryTheory.Limits GlobalTheory.HomStab

namespace GlobalTheory.HomStab

/- English proof (translation)
Introduce `k G _ _ P hP n`. Set `S : Subgroup G` to `⊥`. Set `B : Rep k S` to `Rep.res S.subtype P`. Set `adj` to `Rep.indResAdjunction k S.subtype`. Set `ε : (Rep.indFunctor k S.subtype).obj B ⟶ P` to `adj.counit.app P`.

Establish `hε : Epi ε`. Rewrite using `[Rep.epi_iff_surjective]`. Introduce `x`. Use `⟨(adj.unit.app B).hom x, ?_⟩` and prove the remaining obligations. Establish `h2` using `congrArg (fun f => f.hom x) (adj.right_triangle_components P)`.

Conclude with `h2`. Set `s` to `Projective.factorThru (𝟙 P) ε`. Establish `hs : s ≫ ε = 𝟙 P` using `Projective.factorThru_comp _ _`. Establish `hZ : IsZero (groupHomology (Rep.ind S.subtype B) (n + 1))` using `(isZero_groupHomology_succ_of_subsingleton B n).of_iso (groupHomology.indIso S B (n + 1))`. Rewrite using `[IsZero.iff_id_eq_zero]`.

Establish `hid : (groupHomology.functor k G (n + 1)).map (s ≫ ε) = 𝟙 _`. Rewrite using `[hs]`. Conclude with `CategoryTheory.Functor.map_id _ _`. Use `Eq.trans hid.symm ?_` and prove the remaining obligations. Rewrite using `[CategoryTheory.Functor.map_comp, hZ.eq_of_tgt ((groupHomology.functor k G (n + 1)).map s) 0]`.

Conclude with `zero_comp`.
-/
theorem isZero_groupHomology_succ_of_projective : ∀ (k G : Type) [CommRing k] [Group G] (P : Rep k G), Projective P → ∀ n : ℕ, IsZero (groupHomology P (n + 1)) := by
  intro k G _ _ P hP n
  classical
  let S : Subgroup G := ⊥
  let B : Rep k S := Rep.res S.subtype P
  let adj := Rep.indResAdjunction k S.subtype
  let ε : (Rep.indFunctor k S.subtype).obj B ⟶ P := adj.counit.app P
  have hε : Epi ε := by
    rw [Rep.epi_iff_surjective]
    intro x
    refine ⟨(adj.unit.app B).hom x, ?_⟩
    have h2 := congrArg (fun f => f.hom x) (adj.right_triangle_components P)
    exact h2
  let s := Projective.factorThru (𝟙 P) ε
  have hs : s ≫ ε = 𝟙 P := Projective.factorThru_comp _ _
  have hZ : IsZero (groupHomology (Rep.ind S.subtype B) (n + 1)) :=
    (isZero_groupHomology_succ_of_subsingleton B n).of_iso
      (groupHomology.indIso S B (n + 1))
  rw [IsZero.iff_id_eq_zero]
  have hid : (groupHomology.functor k G (n + 1)).map (s ≫ ε) = 𝟙 _ := by
    rw [hs]
    exact CategoryTheory.Functor.map_id _ _
  refine Eq.trans hid.symm ?_
  rw [CategoryTheory.Functor.map_comp,
    hZ.eq_of_tgt ((groupHomology.functor k G (n + 1)).map s) 0]
  exact zero_comp

end GlobalTheory.HomStab

section
open CategoryTheory CategoryTheory.Limits GlobalTheory.HomStab
/- English proof (translation)
Use `first`. Consider the case `exact @GlobalTheory.HomStab.isZero_groupHomology_succ_of_projective`.
-/
theorem _root_.GlobalTheory.T.projective_rep_groupHomology_pos_vanishes : ∀ (k G : Type) [CommRing k] [Group G] (P : Rep k G), Projective P → ∀ n : ℕ, IsZero (groupHomology P (n + 1)) := by
  first
  | exact @GlobalTheory.HomStab.isZero_groupHomology_succ_of_projective
end

import Mathlib
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.HodgeWedgeFields.H1CommutesBaseChange

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CompanionTheory.Hodge.WedgeField

/- English proof (translation)
Establish `hinter : ∀ U W : X.Opens, IsAffineOpen U → IsAffineOpen W → IsAffineOpen (U ⊓ W)` using `fun U W hU hW => isAffineHom_diagonal_iff.mp (inferInstance : IsAffineHom (Limits.pullback.diagonal s)) ⊤ (isAffineOpen_top _) U le_top W le_top hU hW`. Establish `hcov : (Set.univ : Set X) ⊆ ⋃ U : X.affineOpens, (U.1 : Set X)` using `fun x _ => by`. Establish `hx : x ∈ (⨆ U : X.affineOpens, U.1 : X.Opens)`. Rewrite using `[iSup_affineOpens_eq_top]`. Discharge the goal by the elementary cases of `trivial`.

Take `⟨U, hU⟩` from `TopologicalSpace.Opens.mem_iSup.1 hx`. Conclude with `Set.mem_iUnion.2 ⟨U, hU⟩`. Take `⟨t, ht⟩` from `isCompact_univ.elim_finite_subcover (fun U : X.affineOpens => (U.1 : Set X)) (fun U => U.1.isOpen) hcov`. Set `A : Set X.Opens` to `(fun U : X.affineOpens => U.1) '' (t : Set X.affineOpens)`. Establish `hfin : (infClosure A).Finite` using `(t.finite_toSet.image _).infClosure`.

Establish `haff : infClosure A ⊆ {V : X.Opens | IsAffineOpen V}` using `infClosure_min (by rintro _ ⟨U, _, rfl⟩; exact U.2) fun a ha b hb => hinter a b ha hb`. Use `letI inst : SemilatticeInf (infClosure A) := Subtype.semilatticeInf fun x y hx hy => infClosed_infClosure hx hy`. Use `⟨infClosure A, inst, hfin.to_subtype, ⟨⟨fun p => ⟨p.1, haff p.2⟩, fun a b => rfl, ?_⟩⟩⟩` and prove the remaining obligations. Use `eq_top_iff.2 fun x _ => ?_` and prove the remaining obligations. Take `⟨U, hU, hx⟩` from `Set.mem_iUnion₂.1 (ht (Set.mem_univ x))`.

Conclude with `TopologicalSpace.Opens.mem_iSup.2 ⟨⟨U.1, subset_infClosure ⟨U, hU, rfl⟩⟩, hx⟩`.
-/
theorem exists_finite_sys {R : Type} [CommRing R] {X : Scheme.{0}} (s : X ⟶ Sp R) [IsSeparated s]
    [CompactSpace X] :
    ∃ (P : Type) (_ : SemilatticeInf P) (_ : Finite P), Nonempty (Sys X P) := by
  have hinter : ∀ U W : X.Opens, IsAffineOpen U → IsAffineOpen W → IsAffineOpen (U ⊓ W) :=
    fun U W hU hW => isAffineHom_diagonal_iff.mp
      (inferInstance : IsAffineHom (Limits.pullback.diagonal s)) ⊤ (isAffineOpen_top _) U le_top W le_top hU hW
  have hcov : (Set.univ : Set X) ⊆ ⋃ U : X.affineOpens, (U.1 : Set X) := fun x _ => by
    have hx : x ∈ (⨆ U : X.affineOpens, U.1 : X.Opens) := by
      rw [iSup_affineOpens_eq_top]; trivial
    obtain ⟨U, hU⟩ := TopologicalSpace.Opens.mem_iSup.1 hx
    exact Set.mem_iUnion.2 ⟨U, hU⟩
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover (fun U : X.affineOpens => (U.1 : Set X))
    (fun U => U.1.isOpen) hcov
  let A : Set X.Opens := (fun U : X.affineOpens => U.1) '' (t : Set X.affineOpens)
  have hfin : (infClosure A).Finite := (t.finite_toSet.image _).infClosure
  have haff : infClosure A ⊆ {V : X.Opens | IsAffineOpen V} :=
    infClosure_min (by rintro _ ⟨U, _, rfl⟩; exact U.2) fun a ha b hb => hinter a b ha hb
  letI inst : SemilatticeInf (infClosure A) :=
    Subtype.semilatticeInf fun x y hx hy => infClosed_infClosure hx hy
  refine ⟨infClosure A, inst, hfin.to_subtype, ⟨⟨fun p => ⟨p.1, haff p.2⟩, fun a b => rfl, ?_⟩⟩⟩
  refine eq_top_iff.2 fun x _ => ?_
  obtain ⟨U, hU, hx⟩ := Set.mem_iUnion₂.1 (ht (Set.mem_univ x))
  exact TopologicalSpace.Opens.mem_iSup.2
    ⟨⟨U.1, subset_infClosure ⟨U, hU, rfl⟩⟩, hx⟩

def sqEquiv {R : Type} [CommRing R] {M N : Type*} [AddCommGroup M] [Module R M] [AddCommGroup N]
    [Module R N] (E : M ≃ₗ[R] N) : ⋀[R]^2 M ≃ₗ[R] ⋀[R]^2 N :=
  LinearEquiv.ofLinear (exteriorPower.map 2 (E : M →ₗ[R] N)) (exteriorPower.map 2 (E.symm : N →ₗ[R] M))
    (by rw [← exteriorPower.map_comp]; simp [exteriorPower.map_id])
    (by rw [← exteriorPower.map_comp]; simp [exteriorPower.map_id])

/- English proof (translation)
Express the relevant statement in the definitionally equal form `exteriorPower.map 2 (E : M →ₗ[R] N) _ = _`. Rewrite using `[exteriorPower.map_apply_ιMulti]`. Use `congr 1`. Use function extensionality and compare the values at `i`. Apply the tactic sequence `fin_cases i <;> rfl`.
-/
theorem sqEquiv_ιMulti {R : Type} [CommRing R] {M N : Type*} [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] (E : M ≃ₗ[R] N) (a b : M) :
    sqEquiv E (exteriorPower.ιMulti R 2 ![a, b]) = exteriorPower.ιMulti R 2 ![E a, E b] := by
  change exteriorPower.map 2 (E : M →ₗ[R] N) _ = _
  rw [exteriorPower.map_apply_ιMulti]
  congr 1
  funext i
  fin_cases i <;> rfl

/- English proof (translation)
Take `⟨e, he⟩` from `h`. Set `E1 : H1 F ≃ₗ[R] H1 F'` to `LinearEquiv.ofBijective m.pull1 h1`. Set `E2 : H2 F ≃ₗ[R] H2 F'` to `LinearEquiv.ofBijective m.pull2 h2`. Use `⟨(sqEquiv E1).trans (e.trans E2.symm), fun a b => ?_⟩` and prove the remaining obligations. Rewrite using `[LinearEquiv.trans_apply, LinearEquiv.trans_apply, sqEquiv_ιMulti, he, LinearEquiv.symm_apply_eq]`.

Conclude with `(m.pullCohomologyTwo_cup a b).symm`.
-/
theorem wedge_of_bijective {R : Type} [CommRing R] {C C' : Type} [Category.{0} C] [Category.{0} C']
    {F : C ⥤ CommAlgCat.{0} R} {F' : C' ⥤ CommAlgCat.{0} R} (m : CoefMap (RingHom.id R) F F')
    (h1 : Function.Bijective m.pull1) (h2 : Function.Bijective m.pull2) (h : Wedge F') : Wedge F := by
  obtain ⟨e, he⟩ := h
  let E1 : H1 F ≃ₗ[R] H1 F' := LinearEquiv.ofBijective m.pull1 h1
  let E2 : H2 F ≃ₗ[R] H2 F' := LinearEquiv.ofBijective m.pull2 h2
  refine ⟨(sqEquiv E1).trans (e.trans E2.symm), fun a b => ?_⟩
  rw [LinearEquiv.trans_apply, LinearEquiv.trans_apply, sqEquiv_ιMulti, he, LinearEquiv.symm_apply_eq]
  exact (m.pullCohomologyTwo_cup a b).symm

/- English proof (translation)
Set `E1 : H1 F ≃ₗ[R] H1 F'` to `LinearEquiv.ofBijective m.pull1 h1`. Take `⟨hf, hp, hr⟩` from `h`. Use `⟨Module.Finite.equiv E1, Module.Projective.of_equiv E1, fun p => ?_⟩` and prove the remaining obligations. Rewrite using `[← Module.rankAtStalk_eq_of_equiv E1]`. Conclude with `hr p`.
-/
theorem vb_of_bijective {R : Type} [CommRing R] {C C' : Type} [Category.{0} C] [Category.{0} C']
    {F : C ⥤ CommAlgCat.{0} R} {F' : C' ⥤ CommAlgCat.{0} R} (m : CoefMap (RingHom.id R) F F')
    (h1 : Function.Bijective m.pull1) {n : ℕ} (h : VB R (H1 F) n) : VB R (H1 F') n := by
  let E1 : H1 F ≃ₗ[R] H1 F' := LinearEquiv.ofBijective m.pull1 h1
  obtain ⟨hf, hp, hr⟩ := h
  refine ⟨Module.Finite.equiv E1, Module.Projective.of_equiv E1, fun p => ?_⟩
  rw [← Module.rankAtStalk_eq_of_equiv E1]
  exact hr p

end GlobalTheory.CompanionTheory.Hodge.WedgeField

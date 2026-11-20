import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.PhiExact
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleLocalPropertyCalculusRulesStatement

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex GlobalTheory.EtC UpperTheory.Gal.TranscendenceTraces

/- English proof (translation)
Proceed by induction on `x using DirectSum.induction_on with`. Consider the case `zero => simp [Sec.map]`. Consider the case `of v a`. Establish `h` using `DS.map_inc p f v a`. Simplify using `only [inc, DirectSum.lof_eq_of] at h`.

Rewrite using `[h]`. Distinguish the cases in `hv : v = u`. Substitute `hv` using the available equality. Simplify using `[DirectSum.of_eq_same]`. Rewrite using `[DirectSum.of_eq_of_ne _ _ _ (Ne.symm hv), DirectSum.of_eq_of_ne _ _ _ (Ne.symm hv)]`.

Simplify using `[Sec.map]`. Consider the case `add x y hx hy => simp [map_add, hx, hy, Sec.map]`.
-/
private theorem DS_map_apply {R : Type} [CommRing R] {Z S : Scheme.{0}} (p : Z ⟶ S) {G G' : Shv R} (f : G ⟶ G')
    (U : Scheme.{0}) (x : DS p G U) (u : U ⟶ S) :
    (DS.map p f U x) u = Sec.map f (x u) := by
  classical
  induction x using DirectSum.induction_on with
  | zero => simp [Sec.map]
  | of v a =>
    have h := DS.map_inc p f v a
    simp only [inc, DirectSum.lof_eq_of] at h
    rw [h]
    by_cases hv : v = u
    · subst hv
      simp [DirectSum.of_eq_same]
    · rw [DirectSum.of_eq_of_ne _ _ _ (Ne.symm hv), DirectSum.of_eq_of_ne _ _ _ (Ne.symm hv)]
      simp [Sec.map]
  | add x y hx hy => simp [map_add, hx, hy, Sec.map]

/- English proof (translation)
Introduce `h1 R _ Z S p _ T hT U x hx`. Establish `hz : ∀ u, Sec.map T.g (x u) = 0`. Introduce `u`. Rewrite using `[← DS_map_apply, hx]`. Both sides reduce to the same expression.

Establish `hL` using `(GlobalTheory.T.etaleLocal_property_calculus_rules).2.2.2.2.2.1 U x.support (fun i V g => ∃ a, DS.map p T.f V a = DS.res p T.X₂ g (inc p T.X₂ i.1 (x i.1))) (fun i => h1 R p T hT U i.1 (x i.1) (hz i.1))`. Use `(GlobalTheory.T.etaleLocal_property_calculus_rules).2.1 U _ _ hL ?_` and prove the remaining obligations. Introduce `V g hg`. Use `choose a ha using hg`. Use `⟨∑ i : x.support, a i, ?_⟩` and prove the remaining obligations.

Rewrite using `[map_sum]`. Simplify using `only [ha]`. Rewrite using `[← map_sum]`. Use `congr 1`. Use `conv_rhs => rw [← DirectSum.sum_support_of x]`.

Simplify using `only [inc, DirectSum.lof_eq_of]`. Conclude with `Finset.sum_coe_sort x.support (fun i => DirectSum.of (fun i => Sec T.X₂ (pullback p i)) i (x i))`.
-/
theorem UpperTheory.Gal.TranscendenceTraces.dSLoc_of :
    DSOne → DSLoc := by
  intro h1 R _ Z S p _ T hT U x hx
  classical
  have hz : ∀ u, Sec.map T.g (x u) = 0 := by
    intro u
    rw [← DS_map_apply, hx]
    rfl
  have hL := (GlobalTheory.T.etaleLocal_property_calculus_rules).2.2.2.2.2.1 U x.support
    (fun i V g => ∃ a, DS.map p T.f V a = DS.res p T.X₂ g (inc p T.X₂ i.1 (x i.1)))
    (fun i => h1 R p T hT U i.1 (x i.1) (hz i.1))
  refine (GlobalTheory.T.etaleLocal_property_calculus_rules).2.1 U _ _ hL ?_
  intro V g hg
  choose a ha using hg
  refine ⟨∑ i : x.support, a i, ?_⟩
  rw [map_sum]
  simp only [ha]
  rw [← map_sum]
  congr 1
  conv_rhs => rw [← DirectSum.sum_support_of x]
  simp only [inc, DirectSum.lof_eq_of]
  exact Finset.sum_coe_sort x.support (fun i => DirectSum.of (fun i => Sec T.X₂ (pullback p i)) i (x i))

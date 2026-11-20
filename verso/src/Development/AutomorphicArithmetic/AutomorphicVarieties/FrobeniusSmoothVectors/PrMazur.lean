import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.PresDefs
import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.TanFinite
import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.PrDualb
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.ObsPres

open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.U3 UpperTheory.V.Fr

/- English proof (translation)
Introduce `O _ _ _ _ _ R _ _ _ H _ _ _ hob`. Take `⟨a, π, f, hπ, hker, hcard⟩` from `obs_pres O R H (by`. Introduce `A _ _ _ p hp hK κ _ ε hspan hmin`. Take `⟨ob, hob'⟩` from `hob A p hp hK`. Take `⟨co, hco⟩` from `pr_dualb O A (RingHom.ker p) κ ε hK hspan hmin`.

Use `⟨fun u => ob (co u), ?_⟩` and prove the remaining obligations. Introduce `c hc A' _ _ _ p' p'' η hp' hcomp hη hη0 hε`. Establish `hw0 : ob (∑ u, residue O (c u) • co u) = 0`. Rewrite using `[map_sum]`. Simplify using `only [map_smul]`.

Conclude with `hc`. Use `hob' _ hw0 A' p' p'' hcomp hp' ?_` and prove the remaining obligations. Introduce `y hy`. Take `⟨b, hb, hy'⟩` from `hco y`. Rewrite using `[hy', map_sum]`.

Simplify using `only [map_smul, hε, smul_smul]`. Rewrite using `[← Finset.sum_smul]`. Establish `hm : ∑ u, b u * c u ∈ maximalIdeal O`. Rewrite using `[← residue_eq_zero_iff, map_sum]`. Simplify using `only [map_mul, hb]`.

Simplify using `only [LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul] at hy`. Rewrite using `[← hy]`. Conclude with `Finset.sum_congr rfl (fun u _ => mul_comm _ _)`. Use `haveI := IsCO.isLocalHom (O := O) (R := A')`. Rewrite using `[Algebra.smul_def]`.

Conclude with `hη _ (map_nonunit (algebraMap O A') _ hm))`. Establish `hT` using `(pr_tan O R).2`. Use `haveI := (pr_tan O R).1`. Use `haveI := Fintype.ofFinite (ResidueField O)`. Use `haveI : Finite (Tan O R) := Module.finite_of_finite (ResidueField O)`.

Use `haveI := Fintype.ofFinite (Tan O R)`. Establish `h2 : 2 ≤ Fintype.card (ResidueField O)` using `Fintype.one_lt_card`. Establish `hTc : Nat.card (Tan O R) = Fintype.card (ResidueField O) ^ Module.finrank (ResidueField O) (Tan O R)`. Rewrite using `[Nat.card_eq_fintype_card]`. Conclude with `Module.card_eq_pow_finrank`.

Establish `ha : a = Module.finrank (ResidueField O) (Tan O R)`. Apply `Nat.pow_right_injective h2` to reduce the goal to its premises. Express the relevant statement in the definitionally equal form `Fintype.card (ResidueField O) ^ a = Fintype.card (ResidueField O) ^ _`. Rewrite using `[← hTc, ← hT, hcard, Nat.card_eq_fintype_card]`. Substitute `ha` using the available equality.

Conclude with `⟨π, f, hπ, hker⟩`.
-/
theorem UpperTheory.V.Fr.pr_mazur :
    ∀ (O : Type) [CommRing O] [IsLocalRing O] [IsNoetherianRing O] [IsAdicComplete (maximalIdeal O) O] [Finite (ResidueField O)] (R : Type) [CommRing R] [Algebra O R] [IsCO O R] (H : Type) [AddCommGroup H] [Module (ResidueField O) H] [Module.Finite (ResidueField O) H], HasObs O R H → ∃ (p : MvPowerSeries (Fin (Module.finrank (ResidueField O) (Tan O R))) O →ₐ[O] R) (f : Fin (Module.finrank (ResidueField O) H) → MvPowerSeries (Fin (Module.finrank (ResidueField O) (Tan O R))) O), Function.Surjective p ∧ RingHom.ker p = Ideal.span (Set.range f) := by
  intro O _ _ _ _ _ R _ _ _ H _ _ _ hob
  obtain ⟨a, π, f, hπ, hker, hcard⟩ := obs_pres O R H (by
    intro A _ _ _ p hp hK κ _ ε hspan hmin
    obtain ⟨ob, hob'⟩ := hob A p hp hK
    obtain ⟨co, hco⟩ := pr_dualb O A (RingHom.ker p) κ ε hK hspan hmin
    refine ⟨fun u => ob (co u), ?_⟩
    intro c hc A' _ _ _ p' p'' η hp' hcomp hη hη0 hε
    have hw0 : ob (∑ u, residue O (c u) • co u) = 0 := by
      rw [map_sum]
      simp only [map_smul]
      exact hc
    refine hob' _ hw0 A' p' p'' hcomp hp' ?_
    intro y hy
    obtain ⟨b, hb, hy'⟩ := hco y
    rw [hy', map_sum]
    simp only [map_smul, hε, smul_smul]
    rw [← Finset.sum_smul]
    have hm : ∑ u, b u * c u ∈ maximalIdeal O := by
      rw [← residue_eq_zero_iff, map_sum]
      simp only [map_mul, hb]
      simp only [LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul] at hy
      rw [← hy]
      exact Finset.sum_congr rfl (fun u _ => mul_comm _ _)
    haveI := IsCO.isLocalHom (O := O) (R := A')
    rw [Algebra.smul_def]
    exact hη _ (map_nonunit (algebraMap O A') _ hm))
  have hT := (pr_tan O R).2
  haveI := (pr_tan O R).1
  classical
  haveI := Fintype.ofFinite (ResidueField O)
  haveI : Finite (Tan O R) := Module.finite_of_finite (ResidueField O)
  haveI := Fintype.ofFinite (Tan O R)
  have h2 : 2 ≤ Fintype.card (ResidueField O) := Fintype.one_lt_card
  have hTc : Nat.card (Tan O R) =
      Fintype.card (ResidueField O) ^ Module.finrank (ResidueField O) (Tan O R) := by
    rw [Nat.card_eq_fintype_card]
    exact Module.card_eq_pow_finrank
  have ha : a = Module.finrank (ResidueField O) (Tan O R) := by
    apply Nat.pow_right_injective h2
    change Fintype.card (ResidueField O) ^ a = Fintype.card (ResidueField O) ^ _
    rw [← hTc, ← hT, hcard, Nat.card_eq_fintype_card]
  subst ha
  exact ⟨π, f, hπ, hker⟩

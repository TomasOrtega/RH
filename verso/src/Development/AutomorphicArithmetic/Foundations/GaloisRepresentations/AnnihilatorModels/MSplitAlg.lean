import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.OrdReadOf

open UpperTheory.Gal.crystallineComparison UpperTheory.Gal.crystallineComparison.Mod

/- English proof (translation)
Introduce `κ B Λ _ _ _ _ _ _ _ hcard ε g`. Establish `hli` using `linearIndependent_toLinearMap κ B κ`. Use `haveI : Finite (B →ₐ[κ] κ) := hli.finite`. Use `letI := Fintype.ofFinite (B →ₐ[κ] κ)`. Establish `hspan : Submodule.span κ (Set.range (AlgHom.toLinearMap : (B →ₐ[κ] κ) → B →ₗ[κ] κ)) = ⊤`.

Apply `hli.span_eq_top_of_card_eq_finrank'` to reduce the goal to its premises. Rewrite using `[← Nat.card_eq_fintype_card, hcard]`. Conclude with `(Subspace.dual_finrank_eq).symm`. Establish `h0 : ∀ x : B, (∀ φ : B →ₐ[κ] κ, φ x = 0) → x = 0`. Introduce `x hx`.

Rewrite using `[← Module.forall_dual_apply_eq_zero_iff κ x]`. Introduce `f`. Establish `hf : f ∈ Submodule.span κ (Set.range (AlgHom.toLinearMap : (B →ₐ[κ] κ) → B →ₗ[κ] κ))`. Rewrite using `[hspan]`. Conclude with `Submodule.mem_top`.

Proceed by induction on `hf using Submodule.span_induction with`. Consider the case `mem y hy`. Take `⟨φ, rfl⟩` from `hy`. Conclude with `hx φ`. Consider the case `zero => rfl`.

Consider the case `add y z _ _ hy hz => simp [hy, hz]`. Consider the case `smul a y _ hy => simp [hy]`. Establish `hunit : ∀ y : Λ, ε y ≠ 0 → IsUnit y`. Introduce `y hy`. Assume the negation of the conclusion as `h`.

Establish `hym : y ∈ IsLocalRing.maximalIdeal Λ` using `h`. Establish `hk : RingHom.ker ε.toRingHom ≤ IsLocalRing.maximalIdeal Λ` using `IsLocalRing.le_maximalIdeal (RingHom.ker_ne_top _)`. Establish `hd : y - algebraMap κ Λ (ε y) ∈ RingHom.ker ε.toRingHom`. Rewrite using `[RingHom.mem_ker]`. Simplify using the standard rewrite rules.

Establish `hm : algebraMap κ Λ (ε y) ∈ IsLocalRing.maximalIdeal Λ`. Use `Ideal.sub_mem _ hym (hk hd)` as an intermediate fact. Simplify using `using this`. Conclude with `hm ((isUnit_iff_ne_zero.mpr hy).map (algebraMap κ Λ))`. Use extensionality with `b`.

Simplify using `only [AlgHom.comp_apply, Algebra.ofId_apply]`. Use `set S : Finset κ := Finset.univ.image (fun φ : B →ₐ[κ] κ => φ b) with hS`. Use `set c := ε (g b) with hc`. Establish `hqb : Polynomial.aeval b (∏ s ∈ S, (Polynomial.X - Polynomial.C s)) = 0`. Apply `h0` to reduce the goal to its premises.

Introduce `φ`. Rewrite using `[← Polynomial.aeval_algHom_apply, Polynomial.coe_aeval_eq_eval, Polynomial.eval_prod]`. Apply `Finset.prod_eq_zero (i := φ b) (by simp [hS])` to reduce the goal to its premises. Simplify using the standard rewrite rules. Establish `hq : Polynomial.aeval (g b) (∏ s ∈ S, (Polynomial.X - Polynomial.C s)) = 0`.

Rewrite using `[Polynomial.aeval_algHom_apply, hqb, map_zero]`. Establish `hcS : c ∈ S`. Establish `h1` using `congrArg ε hq`. Rewrite `h1` using `[← Polynomial.aeval_algHom_apply, map_zero, Polynomial.coe_aeval_eq_eval, Polynomial.eval_prod, Finset.prod_eq_zero_iff]`. Take `⟨s, hs, hs0⟩` from `h1`.

Simplify using `only [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C, sub_eq_zero] at hs0`. Rewrite using `[hc, hs0]`. Conclude with `hs`. Rewrite `hq` using `[← Finset.mul_prod_erase S _ hcS, map_mul]`. Establish `hr : IsUnit (Polynomial.aeval (g b) (∏ s ∈ S.erase c, (Polynomial.X - Polynomial.C s)))`.

Apply `hunit` to reduce the goal to its premises. Rewrite using `[← Polynomial.aeval_algHom_apply, Polynomial.coe_aeval_eq_eval, Polynomial.eval_prod, Finset.prod_ne_zero_iff]`. Introduce `s hs`. Simplify using `only [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C]`. Conclude with `sub_ne_zero.mpr (Finset.ne_of_mem_erase hs).symm`.

Establish `h2` using `hr.mul_left_eq_zero.mp hq`. Simplify using `only [map_sub, Polynomial.aeval_X, Polynomial.aeval_C] at h2`. Conclude with `sub_eq_zero.mp h2`.
-/
theorem UpperTheory.Gal.crystallineComparison.Mod.splitAlg_of :
    SplitAlg := by
  classical
  intro κ B Λ _ _ _ _ _ _ _ hcard ε g
  have hli := linearIndependent_toLinearMap κ B κ
  haveI : Finite (B →ₐ[κ] κ) := hli.finite
  letI := Fintype.ofFinite (B →ₐ[κ] κ)
  have hspan : Submodule.span κ (Set.range (AlgHom.toLinearMap : (B →ₐ[κ] κ) → B →ₗ[κ] κ)) = ⊤ := by
    apply hli.span_eq_top_of_card_eq_finrank'
    rw [← Nat.card_eq_fintype_card, hcard]
    exact (Subspace.dual_finrank_eq).symm
  have h0 : ∀ x : B, (∀ φ : B →ₐ[κ] κ, φ x = 0) → x = 0 := by
    intro x hx
    rw [← Module.forall_dual_apply_eq_zero_iff κ x]
    intro f
    have hf : f ∈ Submodule.span κ (Set.range (AlgHom.toLinearMap : (B →ₐ[κ] κ) → B →ₗ[κ] κ)) := by
      rw [hspan]; exact Submodule.mem_top
    induction hf using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨φ, rfl⟩ := hy
      exact hx φ
    | zero => rfl
    | add y z _ _ hy hz => simp [hy, hz]
    | smul a y _ hy => simp [hy]
  have hunit : ∀ y : Λ, ε y ≠ 0 → IsUnit y := by
    intro y hy
    by_contra h
    have hym : y ∈ IsLocalRing.maximalIdeal Λ := h
    have hk : RingHom.ker ε.toRingHom ≤ IsLocalRing.maximalIdeal Λ :=
      IsLocalRing.le_maximalIdeal (RingHom.ker_ne_top _)
    have hd : y - algebraMap κ Λ (ε y) ∈ RingHom.ker ε.toRingHom := by
      rw [RingHom.mem_ker]
      simp
    have hm : algebraMap κ Λ (ε y) ∈ IsLocalRing.maximalIdeal Λ := by
      have := Ideal.sub_mem _ hym (hk hd)
      simpa using this
    exact hm ((isUnit_iff_ne_zero.mpr hy).map (algebraMap κ Λ))
  ext b
  simp only [AlgHom.comp_apply, Algebra.ofId_apply]
  set S : Finset κ := Finset.univ.image (fun φ : B →ₐ[κ] κ => φ b) with hS
  set c := ε (g b) with hc
  have hqb : Polynomial.aeval b (∏ s ∈ S, (Polynomial.X - Polynomial.C s)) = 0 := by
    apply h0
    intro φ
    rw [← Polynomial.aeval_algHom_apply, Polynomial.coe_aeval_eq_eval, Polynomial.eval_prod]
    apply Finset.prod_eq_zero (i := φ b) (by simp [hS])
    simp
  have hq : Polynomial.aeval (g b) (∏ s ∈ S, (Polynomial.X - Polynomial.C s)) = 0 := by
    rw [Polynomial.aeval_algHom_apply, hqb, map_zero]
  have hcS : c ∈ S := by
    have h1 := congrArg ε hq
    rw [← Polynomial.aeval_algHom_apply, map_zero, Polynomial.coe_aeval_eq_eval,
      Polynomial.eval_prod, Finset.prod_eq_zero_iff] at h1
    obtain ⟨s, hs, hs0⟩ := h1
    simp only [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C, sub_eq_zero] at hs0
    rw [hc, hs0]
    exact hs
  rw [← Finset.mul_prod_erase S _ hcS, map_mul] at hq
  have hr : IsUnit (Polynomial.aeval (g b) (∏ s ∈ S.erase c, (Polynomial.X - Polynomial.C s))) := by
    apply hunit
    rw [← Polynomial.aeval_algHom_apply, Polynomial.coe_aeval_eq_eval, Polynomial.eval_prod,
      Finset.prod_ne_zero_iff]
    intro s hs
    simp only [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C]
    exact sub_ne_zero.mpr (Finset.ne_of_mem_erase hs).symm
  have h2 := hr.mul_left_eq_zero.mp hq
  simp only [map_sub, Polynomial.aeval_X, Polynomial.aeval_C] at h2
  exact sub_eq_zero.mp h2

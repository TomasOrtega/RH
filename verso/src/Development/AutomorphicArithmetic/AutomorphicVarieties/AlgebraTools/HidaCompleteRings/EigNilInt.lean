import Mathlib
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.HidaCompleteRings.OrdBasic

open UpperTheory.V.AlgebraTools.AnnihilatorQuotientFinite TensorProduct

/- English proof (translation)
Introduce `O K _ _ _ _ M _ _ _ T hT μ y hy hμy hμ hint`. Take `⟨p, hmon, -, hcoef, hp⟩` from `LinearMap.exists_monic_and_natDegree_eq_and_coeff_mem_pow_and_aeval_eq_zero (f := T) (I := IsLocalRing.maximalIdeal O) (hI := hT)`. Establish `hK : Polynomial.aeval (T.baseChange K) p = 0`. Establish `e : T.baseChange K = Module.End.baseChangeHom O K M T` using `rfl`. Rewrite using `[e, Polynomial.aeval_algHom_apply, hp, map_zero]`.

Establish `hev : Module.End.HasEigenvector (T.baseChange K) μ y` using `Module.End.hasEigenvector_iff.mpr ⟨Module.End.mem_eigenspace_iff.mpr hμy, hy⟩`. Establish `hq : Polynomial.aeval μ p = 0`. Establish `h1` using `Module.End.aeval_apply_of_hasEigenvector (p := p.map (algebraMap O K)) hev`. Rewrite `h1` using `[Polynomial.aeval_map_algebraMap, Polynomial.eval_map_algebraMap, hK, LinearMap.zero_apply]`. Conclude with `(smul_eq_zero.mp h1.symm).resolve_right hy`.

Use `set n := p.natDegree with hn`. Use `set ν := μ⁻¹ with hνdef`. Establish `hνμ : ν * μ = 1` using `inv_mul_cancel₀ hμ`. Establish `key : (1 : K) + ∑ i ∈ Finset.range n, algebraMap O K (p.coeff i) * ν ^ (n - i) = 0`. Rewrite `hq` using `[Polynomial.aeval_eq_sum_range, Finset.sum_range_succ, hmon.coeff_natDegree, one_smul]`.

Establish `h2 : ν ^ n * (∑ i ∈ Finset.range n, p.coeff i • μ ^ i + μ ^ n) = 0`. Rewrite using `[hq, mul_zero]`. Rewrite `h2` using `[mul_add, Finset.mul_sum, ← mul_pow, hνμ, one_pow, add_comm]`. Rewrite using `[← h2]`. Use `congr 1`.

Use `Finset.sum_congr rfl fun i hi => ?_` and prove the remaining obligations. Establish `hin : i ≤ n` using `(Finset.mem_range.mp hi).le`. Establish `hp' : ν ^ n = ν ^ (n - i) * ν ^ i` using `by rw [← pow_add, Nat.sub_add_cancel hin]`. Establish `e : ν ^ i * μ ^ i = 1` using `by rw [← mul_pow, hνμ, one_pow]`. Rewrite using `[Algebra.smul_def, hp']`.

Combine the equalities or inequalities in the displayed calculation. Set `C` to `integralClosure O K`. Set `ν' : C` to `⟨ν, hint⟩`. Establish `hs : (1 : C) + ∑ i ∈ Finset.range n, algebraMap O C (p.coeff i) * ν' ^ (n - i) = 0`. Apply `Subtype.ext` to reduce the goal to its premises.

Simplify `key` using `[C, ν']`. Establish `hmem : ∑ i ∈ Finset.range n, algebraMap O C (p.coeff i) * ν' ^ (n - i) ∈ (IsLocalRing.maximalIdeal O).map (algebraMap O C)`. Use `Ideal.sum_mem _ fun i hi => Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ ?_)` and prove the remaining obligations. Establish `hin : i < n` using `Finset.mem_range.mp hi`. Conclude with `Ideal.pow_le_self (by omega) (hcoef i)`.

Establish `htop : (IsLocalRing.maximalIdeal O).map (algebraMap O C) = ⊤`. Rewrite using `[Ideal.eq_top_iff_one, eq_neg_of_add_eq_zero_left hs]`. Conclude with `(Ideal.neg_mem_iff _).mpr hmem`. Establish `hker : RingHom.ker (algebraMap O C) ≤ IsLocalRing.maximalIdeal O` using `IsLocalRing.le_maximalIdeal (RingHom.ker_ne_top _)`. Establish `hint' : (algebraMap O C).IsIntegral` using `fun x => Algebra.IsIntegral.isIntegral x`.

Conclude with `(IsLocalRing.maximalIdeal.isMaximal O).ne_top ((Ideal.map_eq_top_iff_of_ker_le _ hker hint').mp htop)`.
-/
theorem UpperTheory.V.AlgebraTools.AnnihilatorQuotientFinite.eigNilInt :
    ∀ {O K : Type*} [CommRing O] [Field K] [Algebra O K] [IsLocalRing O] {M : Type*} [AddCommGroup M] [Module O M] [Module.Finite O M] (T : Module.End O M), LinearMap.range T ≤ IsLocalRing.maximalIdeal O • ⊤ → ∀ (μ : K) (y : K ⊗[O] M), y ≠ 0 → T.baseChange K y = μ • y → μ ≠ 0 → ¬ IsIntegral O μ⁻¹ := by
  intro O K _ _ _ _ M _ _ _ T hT μ y hy hμy hμ hint
  obtain ⟨p, hmon, -, hcoef, hp⟩ :=
    LinearMap.exists_monic_and_natDegree_eq_and_coeff_mem_pow_and_aeval_eq_zero
      (f := T) (I := IsLocalRing.maximalIdeal O) (hI := hT)
  have hK : Polynomial.aeval (T.baseChange K) p = 0 := by
    have e : T.baseChange K = Module.End.baseChangeHom O K M T := rfl
    rw [e, Polynomial.aeval_algHom_apply, hp, map_zero]
  have hev : Module.End.HasEigenvector (T.baseChange K) μ y :=
    Module.End.hasEigenvector_iff.mpr ⟨Module.End.mem_eigenspace_iff.mpr hμy, hy⟩
  have hq : Polynomial.aeval μ p = 0 := by
    have h1 := Module.End.aeval_apply_of_hasEigenvector (p := p.map (algebraMap O K)) hev
    rw [Polynomial.aeval_map_algebraMap, Polynomial.eval_map_algebraMap, hK,
      LinearMap.zero_apply] at h1
    exact (smul_eq_zero.mp h1.symm).resolve_right hy
  set n := p.natDegree with hn
  set ν := μ⁻¹ with hνdef
  have hνμ : ν * μ = 1 := inv_mul_cancel₀ hμ
  have key : (1 : K) + ∑ i ∈ Finset.range n, algebraMap O K (p.coeff i) * ν ^ (n - i) = 0 := by
    rw [Polynomial.aeval_eq_sum_range, Finset.sum_range_succ, hmon.coeff_natDegree, one_smul] at hq
    have h2 : ν ^ n * (∑ i ∈ Finset.range n, p.coeff i • μ ^ i + μ ^ n) = 0 := by
      rw [hq, mul_zero]
    rw [mul_add, Finset.mul_sum, ← mul_pow, hνμ, one_pow, add_comm] at h2
    rw [← h2]
    congr 1
    refine Finset.sum_congr rfl fun i hi => ?_
    have hin : i ≤ n := (Finset.mem_range.mp hi).le
    have hp' : ν ^ n = ν ^ (n - i) * ν ^ i := by rw [← pow_add, Nat.sub_add_cancel hin]
    have e : ν ^ i * μ ^ i = 1 := by rw [← mul_pow, hνμ, one_pow]
    rw [Algebra.smul_def, hp']
    calc algebraMap O K (p.coeff i) * ν ^ (n - i)
        = algebraMap O K (p.coeff i) * ν ^ (n - i) * (ν ^ i * μ ^ i) := by rw [e, mul_one]
      _ = ν ^ (n - i) * ν ^ i * (algebraMap O K (p.coeff i) * μ ^ i) := by ring
  let C := integralClosure O K
  let ν' : C := ⟨ν, hint⟩
  have hs : (1 : C) + ∑ i ∈ Finset.range n, algebraMap O C (p.coeff i) * ν' ^ (n - i) = 0 := by
    apply Subtype.ext
    simpa [C, ν'] using key
  have hmem : ∑ i ∈ Finset.range n, algebraMap O C (p.coeff i) * ν' ^ (n - i) ∈
      (IsLocalRing.maximalIdeal O).map (algebraMap O C) := by
    refine Ideal.sum_mem _ fun i hi => Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ ?_)
    have hin : i < n := Finset.mem_range.mp hi
    exact Ideal.pow_le_self (by omega) (hcoef i)
  have htop : (IsLocalRing.maximalIdeal O).map (algebraMap O C) = ⊤ := by
    rw [Ideal.eq_top_iff_one, eq_neg_of_add_eq_zero_left hs]
    exact (Ideal.neg_mem_iff _).mpr hmem
  have hker : RingHom.ker (algebraMap O C) ≤ IsLocalRing.maximalIdeal O :=
    IsLocalRing.le_maximalIdeal (RingHom.ker_ne_top _)
  have hint' : (algebraMap O C).IsIntegral := fun x => Algebra.IsIntegral.isIntegral x
  exact (IsLocalRing.maximalIdeal.isMaximal O).ne_top
    ((Ideal.map_eq_top_iff_of_ker_le _ hker hint').mp htop)

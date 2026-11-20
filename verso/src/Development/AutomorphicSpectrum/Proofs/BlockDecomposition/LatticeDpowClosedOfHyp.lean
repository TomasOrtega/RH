import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.LevelChainValuations.LatDefs
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.SplittingFieldLattices.GrSplit
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MemLatticeIdealIffSumStatement

open DividedPowers CrystallineSemistableComparison.Pb

set_option autoImplicit false

namespace GlobalTheory.CompanionTheory.LatDP

variable {B : Type} [CommRing B] [Algebra ℚ B]

/- English proof (translation)
Establish `e : ((k.factorial : ℚ))⁻¹ • (z + w) ^ k = ∑ i ∈ Finset.range (k + 1), (((i.factorial : ℚ))⁻¹ • z ^ i) * ((((k - i).factorial : ℚ))⁻¹ • w ^ (k - i))`. Rewrite using `[add_pow, Finset.smul_sum]`. Use `Finset.sum_congr rfl fun i hi => ?_` and prove the remaining obligations. Establish `hik : i ≤ k` using `Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)`. Establish `hc : ((k.choose i : ℕ) : B) = ((k.choose i : ℕ) : ℚ) • (1 : B)`.

Rewrite using `[Algebra.smul_def, mul_one, map_natCast]`. Rewrite using `[hc, mul_smul_comm, mul_one, smul_smul, smul_mul_smul_comm, Nat.cast_choose ℚ hik]`. Use `congr 1`. Establish `h1 : (k.factorial : ℚ) ≠ 0` using `Nat.cast_ne_zero.2 k.factorial_ne_zero`. Establish `h2 : (i.factorial : ℚ) ≠ 0` using `Nat.cast_ne_zero.2 i.factorial_ne_zero`.

Establish `h3 : ((k - i).factorial : ℚ) ≠ 0` using `Nat.cast_ne_zero.2 (k - i).factorial_ne_zero`. Clear the denominators using the available nonvanishing facts. Rewrite using `[e]`. Conclude with `S.sum_mem fun i _ => S.mul_mem (hz i) (hw _)`.
-/
theorem inv_fact_smul_add_pow_mem (S : Subring B) {z w : B}
    (hz : ∀ k : ℕ, ((k.factorial : ℚ))⁻¹ • z ^ k ∈ S) (hw : ∀ k : ℕ, ((k.factorial : ℚ))⁻¹ • w ^ k ∈ S)
    (k : ℕ) : ((k.factorial : ℚ))⁻¹ • (z + w) ^ k ∈ S := by
  have e : ((k.factorial : ℚ))⁻¹ • (z + w) ^ k =
      ∑ i ∈ Finset.range (k + 1), (((i.factorial : ℚ))⁻¹ • z ^ i) * ((((k - i).factorial : ℚ))⁻¹ • w ^ (k - i)) := by
    rw [add_pow, Finset.smul_sum]
    refine Finset.sum_congr rfl fun i hi => ?_
    have hik : i ≤ k := Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)
    have hc : ((k.choose i : ℕ) : B) = ((k.choose i : ℕ) : ℚ) • (1 : B) := by
      rw [Algebra.smul_def, mul_one, map_natCast]
    rw [hc, mul_smul_comm, mul_one, smul_smul, smul_mul_smul_comm, Nat.cast_choose ℚ hik]
    congr 1
    have h1 : (k.factorial : ℚ) ≠ 0 := Nat.cast_ne_zero.2 k.factorial_ne_zero
    have h2 : (i.factorial : ℚ) ≠ 0 := Nat.cast_ne_zero.2 i.factorial_ne_zero
    have h3 : ((k - i).factorial : ℚ) ≠ 0 := Nat.cast_ne_zero.2 (k - i).factorial_ne_zero
    field_simp
  rw [e]
  exact S.sum_mem fun i _ => S.mul_mem (hz i) (hw _)

variable {W : Type} [CommRing W] (f : W →+* B) (ξ : W) (l M : ℕ)

/- English proof (translation)
Establish `hU : ((k.uniformBell j : ℕ) : ℚ) * (j.factorial : ℚ) ^ k * (k.factorial : ℚ) = ((k * j).factorial : ℚ)`. Conclude with `Nat.uniformBell_mul_eq k hj` after adjusting the coercions. Establish `hc : ((k.uniformBell j : ℕ) : B) = ((k.uniformBell j : ℕ) : ℚ) • (1 : B)`. Rewrite using `[Algebra.smul_def, mul_one, map_natCast]`. Establish `h1 : (k.factorial : ℚ) ≠ 0` using `Nat.cast_ne_zero.2 k.factorial_ne_zero`.

Establish `h2 : (j.factorial : ℚ) ≠ 0` using `Nat.cast_ne_zero.2 j.factorial_ne_zero`. Establish `h3 : ((k * j).factorial : ℚ) ≠ 0` using `Nat.cast_ne_zero.2 (k * j).factorial_ne_zero`. Rewrite using `[Lat.dpE, Lat.dpE, smul_pow, ← pow_mul, smul_smul, hc, smul_mul_assoc, one_mul, smul_smul, mul_comm j k]`. Use `congr 1`. Establish `h4 : (j.factorial : ℚ) ^ k ≠ 0` using `pow_ne_zero _ h2`.

Rewrite using `[eq_mul_inv_iff_mul_eq₀ h3, ← hU, inv_pow]`. Clear the denominators using the available nonvanishing facts.
-/
theorem inv_fact_smul_dpE_pow (j k : ℕ) (hj : j ≠ 0) :
    ((k.factorial : ℚ))⁻¹ • Lat.dpE f ξ l M j ^ k =
      ((k.uniformBell j : ℕ) : B) * Lat.dpE f ξ l M (k * j) := by
  have hU : ((k.uniformBell j : ℕ) : ℚ) * (j.factorial : ℚ) ^ k * (k.factorial : ℚ) = ((k * j).factorial : ℚ) := by
    exact_mod_cast Nat.uniformBell_mul_eq k hj
  have hc : ((k.uniformBell j : ℕ) : B) = ((k.uniformBell j : ℕ) : ℚ) • (1 : B) := by
    rw [Algebra.smul_def, mul_one, map_natCast]
  have h1 : (k.factorial : ℚ) ≠ 0 := Nat.cast_ne_zero.2 k.factorial_ne_zero
  have h2 : (j.factorial : ℚ) ≠ 0 := Nat.cast_ne_zero.2 j.factorial_ne_zero
  have h3 : ((k * j).factorial : ℚ) ≠ 0 := Nat.cast_ne_zero.2 (k * j).factorial_ne_zero
  rw [Lat.dpE, Lat.dpE, smul_pow, ← pow_mul, smul_smul, hc, smul_mul_assoc, one_mul, smul_smul, mul_comm j k]
  congr 1
  have h4 : (j.factorial : ℚ) ^ k ≠ 0 := pow_ne_zero _ h2
  rw [eq_mul_inv_iff_mul_eq₀ h3, ← hU, inv_pow]
  field_simp

/- English proof (translation)
Establish `e : ((k.factorial : ℚ))⁻¹ • (f c * Lat.dpE f ξ l M j) ^ k = f c ^ k * (((k.uniformBell j : ℕ) : B) * Lat.dpE f ξ l M (k * j))`. Rewrite using `[mul_pow, ← mul_smul_comm, inv_fact_smul_dpE_pow f ξ l M j k hj]`. Rewrite using `[e]`. Establish `hf : f c ∈ Lat.sub f ξ l M` using `Subring.subset_closure (Or.inl ⟨c, rfl⟩)`. Establish `hd : Lat.dpE f ξ l M (k * j) ∈ Lat.sub f ξ l M` using `Subring.subset_closure (Or.inr ⟨_, rfl⟩)`.

Conclude with `mul_mem (pow_mem hf _) (mul_mem (natCast_mem _ _) hd)`.
-/
theorem inv_fact_smul_term_mem (c : W) (j k : ℕ) (hj : j ≠ 0) :
    ((k.factorial : ℚ))⁻¹ • (f c * Lat.dpE f ξ l M j) ^ k ∈ Lat.sub f ξ l M := by
  have e : ((k.factorial : ℚ))⁻¹ • (f c * Lat.dpE f ξ l M j) ^ k =
      f c ^ k * (((k.uniformBell j : ℕ) : B) * Lat.dpE f ξ l M (k * j)) := by
    rw [mul_pow, ← mul_smul_comm, inv_fact_smul_dpE_pow f ξ l M j k hj]
  rw [e]
  have hf : f c ∈ Lat.sub f ξ l M := Subring.subset_closure (Or.inl ⟨c, rfl⟩)
  have hd : Lat.dpE f ξ l M (k * j) ∈ Lat.sub f ξ l M := Subring.subset_closure (Or.inr ⟨_, rfl⟩)
  exact mul_mem (pow_mem hf _) (mul_mem (natCast_mem _ _) hd)

/- English proof (translation)
Proceed by induction on `s using Finset.induction_on generalizing k with`. Consider the case `empty`. Break down `k with _ | k` into its components or cases. Simplify using `using (Lat.sub f ξ l M).one_mem`. Simplify using the standard rewrite rules.

Consider the case `insert a s ha ih`. Rewrite using `[Finset.sum_insert ha]`. Conclude with `inv_fact_smul_add_pow_mem _ (fun k => inv_fact_smul_term_mem f ξ l M _ _ k (Nat.succ_ne_zero _)) ih k`.
-/
theorem inv_fact_smul_sum_mem {n : ℕ} (c : Fin n → W) (s : Finset (Fin n)) (k : ℕ) :
    ((k.factorial : ℚ))⁻¹ • (∑ i ∈ s, f (c i) * Lat.dpE f ξ l M (i + 1)) ^ k ∈ Lat.sub f ξ l M := by
  classical
  induction s using Finset.induction_on generalizing k with
  | empty =>
    rcases k with _ | k
    · simpa using (Lat.sub f ξ l M).one_mem
    · simp
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact inv_fact_smul_add_pow_mem _ (fun k => inv_fact_smul_term_mem f ξ l M _ _ k (Nat.succ_ne_zero _)) ih k

/- English proof (translation)
Introduce `x hx k`. Take `⟨n, c, e⟩` from `(GlobalTheory.T.mem_lattice_ideal_iff_sum f ξ l M m h x).1 hx`. Use `⟨⟨_, inv_fact_smul_sum_mem f ξ l M c Finset.univ k⟩, ?_⟩` and prove the remaining obligations. Rewrite using `[RatAlgebra.dpow_eq_inv_fact_smul _ (Lat.γB f ξ) hx, e, Ring.inverse_eq_inv']`. Both sides reduce to the same expression.
-/
theorem dpClosed {W B : Type} [CommRing W] [CommRing B] [Algebra ℚ B] (f : W →+* B) (ξ : W) (l M : ℕ) (m : ℕ)
    (h : Lat.Hyp f ξ l m) : Lat.DPClosed (Lat.ι f ξ l M) (Lat.γB f ξ) := by
  intro x hx k
  obtain ⟨n, c, e⟩ := (GlobalTheory.T.mem_lattice_ideal_iff_sum f ξ l M m h x).1 hx
  refine ⟨⟨_, inv_fact_smul_sum_mem f ξ l M c Finset.univ k⟩, ?_⟩
  rw [RatAlgebra.dpow_eq_inv_fact_smul _ (Lat.γB f ξ) hx, e, Ring.inverse_eq_inv']
  rfl

end GlobalTheory.CompanionTheory.LatDP

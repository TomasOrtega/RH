import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
import Formalism.PairingDivisors.StatementH
import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators

namespace GlobalTheory.OrthoProdTheta

variable {D : D7}

/- English proof (translation)
Simplify using the standard rewrite rules.
-/
theorem coordB_add (T : Tor D) {N N' r : ℕ} (b : Fin r → Matrix (Fin N') (Fin N) D.host.E) (k : Fin r)
    (z x : VC D N N') : coordB D T b k (z + x) = coordB D T b k z + coordB D T b k x := by
  simp only [coordB, Pi.add_apply, add_mul, Finset.sum_add_distrib]

/- English proof (translation)
Introduce a local definition for the expression. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses.

Rewrite the conclusion using the stated equalities. Apply the first step, then apply the next step to every resulting obligation. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules.
-/
theorem coordB_sum (T : Tor D) {N N' r : ℕ} (b : Fin r → Matrix (Fin N') (Fin N) D.host.E)
    (hb : ∀ i j, coordB D T b i (embV D T (b j)) = if i = j then 1 else 0) (i : Fin r) (c : Fin r → ℂ) :
    coordB D T b i (∑ k, c k • embV D T (b k)) = c i := by
  let L : VC D N N' →ₗ[ℂ] ℂ :=
    { toFun := coordB D T b i
      map_add' := coordB_add T b i
      map_smul' := fun c x => by simp [coordB, Finset.mul_sum, mul_assoc] }
  have hL : ∀ z, coordB D T b i z = L z := fun _ => rfl
  rw [hL, map_sum]
  have h2 : ∀ k, L (c k • embV D T (b k)) = if i = k then c k else 0 := by
    intro k
    rw [map_smul, ← hL, hb]
    split_ifs <;> simp
  rw [Finset.sum_congr rfl fun k _ => h2 k]
  simp

/- English proof (translation)
Proceed by induction. Treat this case separately. Treat this case separately.
-/
theorem neg_one_zpow_sum {ι : Type} (s : Finset ι) (m : ι → ℤ) :
    (-1 : ℂ) ^ (∑ k ∈ s, m k) = ∏ k ∈ s, (-1 : ℂ) ^ m k := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.prod_insert ha, zpow_add₀ (by norm_num), ih]

/- English proof (translation)
Proceed by induction. Treat this case separately. Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. Consider separately whether the proposition holds or fails.

Substitute using the available equality. Simplify to obtain the desired conclusion from the available facts. Simplify using the standard rewrite rules. Apply the first step, then apply the next step to every resulting obligation. Treat this case separately.

Treat this case separately. Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Supply the required witnesses or components. Treat this case separately.

Extract witnesses or component facts from the available result. Supply the required witnesses or components.
-/
theorem exists_coord (T : Tor D) {a d r : ℕ}
    {b : Fin r → Matrix (Fin d) (Fin a) D.host.E} {x : VC D a d} (hx : x ∈ LaB D T b) :
    ∃ w : Fin r → ℂ, (∀ j, w j ∈ T.abelian₂) ∧ x = ∑ j, w j • embV D T (b j) := by
  induction hx using AddSubgroup.closure_induction with
  | mem x hx =>
    obtain ⟨w, hw, j, rfl⟩ := hx
    refine ⟨Pi.single j w, fun i => ?_, ?_⟩
    · by_cases h : i = j
      · subst h; simpa using hw
      · simp [h]
    · rw [Finset.sum_eq_single j] <;> simp +contextual
  | zero => exact ⟨0, fun _ => zero_mem _, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨w, hw, rfl⟩ := hx
    obtain ⟨w', hw', rfl⟩ := hy
    exact ⟨w + w', fun j => add_mem (hw j) (hw' j), by simp [add_smul, Finset.sum_add_distrib]⟩
  | neg x _ hx =>
    obtain ⟨w, hw, rfl⟩ := hx
    exact ⟨-w, fun j => neg_mem (hw j), by simp⟩

/- English proof (translation)
Replace the relevant objects with their definitions. Reduce the equality to equality of the corresponding arguments. Simplify using the standard rewrite rules. Use symmetry to reverse the relation. Rewrite the conclusion using the stated equalities.

Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem hf_sum (T : Tor D) {a d r : ℕ} (b : Fin r → Matrix (Fin d) (Fin a) D.host.E) (c : Fin r → ℂ)
    (z : VC D a d) :
    Hf D T z (∑ k, c k • embV D T (b k)) = (∑ k, coordB D T b k z * (starRingEnd ℂ) (c k)) / (area T.abelian₂ : ℂ) := by
  unfold Hf coordB
  congr 1
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, map_sum, map_mul, Finset.mul_sum, Finset.sum_mul, embV]
  symm
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun τ _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i' _ => Finset.sum_congr rfl fun k _ => ?_
  ring

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Reduce the conclusion to the remaining proof obligations. Replace the relevant objects with their definitions. Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result.

Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Establish an intermediate fact.

Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities.

Simplify using the standard rewrite rules. Reduce the equality to equality of the corresponding arguments. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Expand and normalize the polynomial expressions, which then agree.

Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem pullB_mem_ThSp : ∀ (D : D7) (T : Tor D) (N N' r : ℕ) (b : Fin r → Matrix (Fin N') (Fin N) D.host.E), (∀ i j, coordB D T b i (embV D T (b j)) = if i = j then 1 else 0) → ∀ g : ℂ → ℂ, Differentiable ℂ g → (∀ ω ∈ T.abelian₂, ∃ m : ℤ, q1 D T.abelian₂ ω = (m : ℝ) ∧ ∀ z, (-1 : ℂ) ^ m * U1 T.abelian₂ ω g z = g z) → pullB D T b g ∈ ThSp D T (LaB D T b) := by
  intro D T N N' r b hb g hg hq
  refine ⟨?_, ?_⟩
  · unfold pullB coordB
    fun_prop
  · intro x hx z
    obtain ⟨w, hw, rfl⟩ := exists_coord T hx
    choose m hm hU using fun k => hq _ (hw k)
    have hre : Real.sqrt D.host.d / 2 *
        (Hf D T (∑ k, w k • embV D T (b k)) (∑ k, w k • embV D T (b k))).re = ((∑ k, m k : ℤ) : ℝ) := by
      rw [hf_sum, Complex.div_ofReal_re, Complex.re_sum, Int.cast_sum, Finset.sum_div, Finset.mul_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [coordB_sum T b hb, ← hm k, q1, Complex.mul_conj, Complex.ofReal_re, Complex.normSq_eq_norm_sq]
    have hal : al D T (∑ k, w k • embV D T (b k)) = ∏ k, (-1 : ℂ) ^ m k := by
      unfold al
      rw [hre, round_intCast, neg_one_zpow_sum]
    have hUU : U D T (∑ k, w k • embV D T (b k)) (pullB D T b g) z = ∏ k, U1 T.abelian₂ (w k) g (coordB D T b k z) := by
      unfold U U1 pullB
      rw [hf_sum, hf_sum, Finset.prod_mul_distrib, ← Complex.exp_sum]
      simp only [coordB_add, coordB_sum T b hb]
      congr 2
      rw [Finset.sum_div, Finset.sum_div, Finset.mul_sum, Finset.mul_sum, Finset.sum_div, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun k _ => ?_
      ring
    rw [hal, hUU, ← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl fun k _ => hU k _

end GlobalTheory.OrthoProdTheta

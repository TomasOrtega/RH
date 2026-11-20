import Formalism.LocalToGlobal.SiegelLatticeTheory.CasimirReductionTheory.OneParameterDerivatives.AdmissibleCasimirScalars.CompactDerivativesBounded

open MeasureTheory Matrix Filter Topology
open scoped InnerProductSpace

set_option autoImplicit false

noncomputable section

namespace Formalism.L2.SG.Pf.admitted

open Formalism.MainNotions.S Formalism.REAL Formalism.MainNotions.BridgeCPX

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

namespace GeneratorWeights

variable {n : ℕ}

/- English proof (translation)
Unfold `sg`. Apply the tactic sequence `split_ifs <;> simp`.
-/
theorem sg_cases (ε : Fin n → Bool) (p : Fin n × Fin n) : sg ε p = 1 ∨ sg ε p = -1 := by
  unfold sg
  split_ifs <;> simp

/- English proof (translation)
Unfold `wt`. Apply the tactic sequence `split_ifs <;> norm_num`.
-/
theorem wt_ge (p : Fin n × Fin n) : 1 / 2 ≤ wt p := by
  unfold wt
  split_ifs <;> norm_num

/- English proof (translation)
Unfold `wt`. Apply the tactic sequence `split_ifs <;> norm_num`.
-/
theorem wt_le (p : Fin n × Fin n) : wt p ≤ 1 := by
  unfold wt
  split_ifs <;> norm_num

/- English proof (translation)
Take `⟨a, b⟩` from `p`. Establish `key : ∀ X : Matrix (Fin n) (Fin n) ℂ, (∀ i j, star (X j i) * (if ε j = true then 1 else -1) + (if ε i = true then 1 else -1) * X i j = 0) → inG ε X`. Introduce `X hX`. Unfold `inG`. Use extensionality with `i j`.

Simplify `hX i j` using `[Jm, Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.conjTranspose_apply]`. Apply `key` to reduce the goal to its premises. Introduce `i j`. Unfold `gen sg`. Distinguish the cases in `hab : a = b`.

Substitute `hab` using the available equality. Simplify using `only [if_true, Matrix.smul_apply, smul_eq_mul, Matrix.single_apply]`. Distinguish the cases in `h : a = i ∧ a = j`. Take `⟨rfl, rfl⟩` from `h`. Apply the tactic sequence `cases ha : ε a <;> simp [ha]`.

Establish `h' : ¬ (a = j ∧ a = i)` using `fun h2 => h ⟨h2.2, h2.1⟩`. Simplify using `[h, h']`. Establish `hba : ¬ b = a` using `Ne.symm hab`. Distinguish the cases in `hlt : a < b`. Simplify using `only [hab, hlt, if_false, if_true, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul, Matrix.single_apply]`.

Distinguish the cases in `h1 : a = i ∧ b = j`. Take `⟨rfl, rfl⟩` from `h1`. Apply the tactic sequence `cases ha : ε a <;> cases hb : ε b <;> simp [ha, hb, hab, hba]`. Distinguish the cases in `h2 : b = i ∧ a = j`. Take `⟨rfl, rfl⟩` from `h2`.

Apply the tactic sequence `cases ha : ε a <;> cases hb : ε b <;> simp [ha, hb, hab, hba]`. Establish `h1' : ¬ (a = j ∧ b = i)` using `fun h => h2 ⟨h.2, h.1⟩`. Establish `h2' : ¬ (b = j ∧ a = i)` using `fun h => h1 ⟨h.2, h.1⟩`. Simplify using `[h1, h2, h1', h2']`. Simplify using `only [hab, hlt, if_false, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Matrix.single_apply]`.

Distinguish the cases in `h1 : a = i ∧ b = j`. Take `⟨rfl, rfl⟩` from `h1`. Apply the tactic sequence `cases ha : ε a <;> cases hb : ε b <;> simp [ha, hb, hab, hba] <;> ring1`. Distinguish the cases in `h2 : b = i ∧ a = j`. Take `⟨rfl, rfl⟩` from `h2`.

Apply the tactic sequence `cases ha : ε a <;> cases hb : ε b <;> simp [ha, hb, hab, hba] <;> ring1`. Establish `h1' : ¬ (a = j ∧ b = i)` using `fun h => h2 ⟨h.2, h.1⟩`. Establish `h2' : ¬ (b = j ∧ a = i)` using `fun h => h1 ⟨h.2, h.1⟩`. Simplify using `[h1, h2, h1', h2']`.
-/
theorem gen_mem (ε : Fin n → Bool) (p : Fin n × Fin n) : inG ε (gen ε p) := by
  obtain ⟨a, b⟩ := p
  have key : ∀ X : Matrix (Fin n) (Fin n) ℂ, (∀ i j, star (X j i) * (if ε j = true then 1 else -1) +
      (if ε i = true then 1 else -1) * X i j = 0) → inG ε X := by
    intro X hX
    unfold inG
    ext i j
    simpa [Jm, Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.conjTranspose_apply] using hX i j
  apply key
  intro i j
  unfold gen sg
  by_cases hab : a = b
  · subst hab
    simp only [if_true, Matrix.smul_apply, smul_eq_mul, Matrix.single_apply]
    by_cases h : a = i ∧ a = j
    · obtain ⟨rfl, rfl⟩ := h
      cases ha : ε a <;> simp [ha]
    · have h' : ¬ (a = j ∧ a = i) := fun h2 => h ⟨h2.2, h2.1⟩
      simp [h, h']
  · have hba : ¬ b = a := Ne.symm hab
    by_cases hlt : a < b
    · simp only [hab, hlt, if_false, if_true, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul,
        Matrix.single_apply]
      by_cases h1 : a = i ∧ b = j
      · obtain ⟨rfl, rfl⟩ := h1
        cases ha : ε a <;> cases hb : ε b <;> simp [ha, hb, hab, hba]
      · by_cases h2 : b = i ∧ a = j
        · obtain ⟨rfl, rfl⟩ := h2
          cases ha : ε a <;> cases hb : ε b <;> simp [ha, hb, hab, hba]
        · have h1' : ¬ (a = j ∧ b = i) := fun h => h2 ⟨h.2, h.1⟩
          have h2' : ¬ (b = j ∧ a = i) := fun h => h1 ⟨h.2, h.1⟩
          simp [h1, h2, h1', h2']
    · simp only [hab, hlt, if_false, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul,
        Matrix.single_apply]
      by_cases h1 : a = i ∧ b = j
      · obtain ⟨rfl, rfl⟩ := h1
        cases ha : ε a <;> cases hb : ε b <;> simp [ha, hb, hab, hba] <;> ring1
      · by_cases h2 : b = i ∧ a = j
        · obtain ⟨rfl, rfl⟩ := h2
          cases ha : ε a <;> cases hb : ε b <;> simp [ha, hb, hab, hba] <;> ring1
        · have h1' : ¬ (a = j ∧ b = i) := fun h => h2 ⟨h.2, h.1⟩
          have h2' : ¬ (b = j ∧ a = i) := fun h => h1 ⟨h.2, h.1⟩
          simp [h1, h2, h1', h2']

variable {ε : Fin n → Bool} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} {D : Submodule ℂ H}

/- English proof (translation)
Establish `hgen : ∀ p, inG ε (gen ε p)` using `gen_mem ε`. Establish `key : ⟪Cas ε σ v, v⟫_ℂ = ∑ p, ((wt p * sg ε p * ‖dS σ (gen ε p) v‖ ^ 2 : ℝ) : ℂ)`. Unfold `Cas`. Rewrite using `[inner_neg_left, sum_inner, ← Finset.sum_neg_distrib]`. Use `Finset.sum_congr rfl fun p _ => ?_` and prove the remaining obligations.

Rewrite using `[inner_smul_left, hC.skew _ (hgen p) _ (hC.mem _ (hgen p) v hv) v hv, inner_self_eq_norm_sq_to_K]`. Apply the tactic sequence `apply Complex.ext <;> simp [Complex.mul_re, Complex.mul_im] <;> ring`. Establish `h2 : ((c * ‖v‖ ^ 2 : ℝ) : ℂ) = ((∑ p, wt p * sg ε p * ‖dS σ (gen ε p) v‖ ^ 2 : ℝ) : ℂ)`. Rewrite using `[Complex.ofReal_sum, ← key, hc v hv, inner_smul_left, inner_self_eq_norm_sq_to_K]`. Apply the tactic sequence `apply Complex.ext <;> simp [Complex.mul_re, Complex.mul_im] <;> ring`.

Conclude with `(Complex.ofReal_inj.1 h2).symm`.
-/
theorem sum_eq (hC : Calc ε σ D) {c : ℝ} (hc : ∀ v ∈ D, Cas ε σ v = (c : ℂ) • v) {v : H} (hv : v ∈ D) :
    ∑ p : Fin n × Fin n, wt p * sg ε p * ‖dS σ (gen ε p) v‖ ^ 2 = c * ‖v‖ ^ 2 := by
  have hgen : ∀ p, inG ε (gen ε p) := gen_mem ε
  have key : ⟪Cas ε σ v, v⟫_ℂ =
      ∑ p, ((wt p * sg ε p * ‖dS σ (gen ε p) v‖ ^ 2 : ℝ) : ℂ) := by
    unfold Cas
    rw [inner_neg_left, sum_inner, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [inner_smul_left, hC.skew _ (hgen p) _ (hC.mem _ (hgen p) v hv) v hv,
      inner_self_eq_norm_sq_to_K]
    apply Complex.ext <;> simp [Complex.mul_re, Complex.mul_im] <;> ring
  have h2 : ((c * ‖v‖ ^ 2 : ℝ) : ℂ) =
      ((∑ p, wt p * sg ε p * ‖dS σ (gen ε p) v‖ ^ 2 : ℝ) : ℂ) := by
    rw [Complex.ofReal_sum, ← key, hc v hv, inner_smul_left, inner_self_eq_norm_sq_to_K]
    apply Complex.ext <;> simp [Complex.mul_re, Complex.mul_im] <;> ring
  exact (Complex.ofReal_inj.1 h2).symm

end GeneratorWeights

open GeneratorWeights in
/- English proof (translation)
Introduce `n ε H _ _ _ σ D hC c hc W C hW`. Use `set K : ℝ := 2 * ((Fintype.card (Fin n × Fin n) : ℝ) * C ^ 2 + |c|) with hK`. Use `⟨max C (Real.sqrt K), fun p v hvD hvW => ?_⟩` and prove the remaining obligations. Establish `hv0 : 0 ≤ ‖v‖` using `norm_nonneg v`. Distinguish the cases in `hp : ε p.1 = ε p.2`.

Conclude with `(hW p hp v hvW).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hv0)`. Establish `hsum` using `sum_eq hC hc hvD`. Establish `hsgp : sg ε p = -1` using `by simp [sg, hp]`. Establish `hterm : ∀ q, wt q * sg ε q * ‖dS σ (gen ε q) v‖ ^ 2 ≤ C ^ 2 * ‖v‖ ^ 2`. Introduce `q`.

Establish `h3` using `wt_le q`. Establish `h4` using `wt_ge q`. Break down `sg_cases ε q with h | h` into its components or cases. Establish `hq : ε q.1 = ε q.2`. Assume the negation of the conclusion as `hne`.

Simplify using `[sg, hne] at h`. Evaluate the numerical expressions using `at h`. Establish `h1` using `hW q hq v hvW`. Establish `h2 : ‖dS σ (gen ε q) v‖ ^ 2 ≤ (C * ‖v‖) ^ 2` using `pow_le_pow_left₀ (norm_nonneg _) h1 2`. Rewrite using `[h, mul_one]`.

Establish `h5 : wt q * ‖dS σ (gen ε q) v‖ ^ 2 ≤ 1 * ‖dS σ (gen ε q) v‖ ^ 2` using `mul_le_mul_of_nonneg_right h3 (sq_nonneg _)`. Use polynomial arithmetic with `[h2, h5]`. Rewrite using `[h]`. Establish `h5 : 0 ≤ wt q * ‖dS σ (gen ε q) v‖ ^ 2` using `mul_nonneg (by linarith) (sq_nonneg _)`. Use polynomial arithmetic with `[sq_nonneg (C * ‖v‖), h5]`.

Establish `hsplit` using `Finset.add_sum_erase Finset.univ (fun q => wt q * sg ε q * ‖dS σ (gen ε q) v‖ ^ 2) (Finset.mem_univ p)`. Establish `hrest : ∑ q ∈ Finset.univ.erase p, wt q * sg ε q * ‖dS σ (gen ε q) v‖ ^ 2 ≤ (Fintype.card (Fin n × Fin n) : ℝ) * (C ^ 2 * ‖v‖ ^ 2)`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[Finset.sum_const, nsmul_eq_mul]`. Use `_ ≤ _ := mul_le_mul_of_nonneg_right (by exact_mod_cast (Finset.card_erase_le.trans (le_of_eq Finset.card_univ))) (by positivity)`.

Establish `hwp` using `wt_ge p`. Rewrite `hsplit` using `[hsgp]`. Establish `e2 : (1 / 2) * ‖dS σ (gen ε p) v‖ ^ 2 ≤ wt p * ‖dS σ (gen ε p) v‖ ^ 2` using `mul_le_mul_of_nonneg_right hwp (sq_nonneg _)`. Establish `e3 : -c * ‖v‖ ^ 2 ≤ |c| * ‖v‖ ^ 2` using `mul_le_mul_of_nonneg_right (neg_le_abs c) (sq_nonneg _)`. Establish `hsq : ‖dS σ (gen ε p) v‖ ^ 2 ≤ K * ‖v‖ ^ 2`.

Rewrite using `[hK]`. Use polynomial arithmetic with `[hsplit, hsum, hrest, e2, e3]`. Establish `hK0 : 0 ≤ K` using `by positivity`. Establish `hle : ‖dS σ (gen ε p) v‖ ≤ Real.sqrt K * ‖v‖`. Rewrite using `[← Real.sqrt_sq (norm_nonneg (dS σ (gen ε p) v)), ← Real.sqrt_sq hv0, ← Real.sqrt_mul hK0]`.

Conclude with `Real.sqrt_le_sqrt hsq`. Conclude with `hle.trans (mul_le_mul_of_nonneg_right (le_max_right _ _) hv0)`.
-/
theorem c4 : CasimirScalarBounded := by
  intro n ε H _ _ _ σ D hC c hc W C hW
  set K : ℝ := 2 * ((Fintype.card (Fin n × Fin n) : ℝ) * C ^ 2 + |c|) with hK
  refine ⟨max C (Real.sqrt K), fun p v hvD hvW => ?_⟩
  have hv0 : 0 ≤ ‖v‖ := norm_nonneg v
  by_cases hp : ε p.1 = ε p.2
  · exact (hW p hp v hvW).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hv0)
  · have hsum := sum_eq hC hc hvD
    have hsgp : sg ε p = -1 := by simp [sg, hp]
    have hterm : ∀ q, wt q * sg ε q * ‖dS σ (gen ε q) v‖ ^ 2 ≤ C ^ 2 * ‖v‖ ^ 2 := by
      intro q
      have h3 := wt_le q
      have h4 := wt_ge q
      rcases sg_cases ε q with h | h
      · have hq : ε q.1 = ε q.2 := by
          by_contra hne
          simp [sg, hne] at h
          norm_num at h
        have h1 := hW q hq v hvW
        have h2 : ‖dS σ (gen ε q) v‖ ^ 2 ≤ (C * ‖v‖) ^ 2 :=
          pow_le_pow_left₀ (norm_nonneg _) h1 2
        rw [h, mul_one]
        have h5 : wt q * ‖dS σ (gen ε q) v‖ ^ 2 ≤ 1 * ‖dS σ (gen ε q) v‖ ^ 2 :=
          mul_le_mul_of_nonneg_right h3 (sq_nonneg _)
        nlinarith [h2, h5]
      · rw [h]
        have h5 : 0 ≤ wt q * ‖dS σ (gen ε q) v‖ ^ 2 :=
          mul_nonneg (by linarith) (sq_nonneg _)
        nlinarith [sq_nonneg (C * ‖v‖), h5]
    have hsplit := Finset.add_sum_erase Finset.univ
      (fun q => wt q * sg ε q * ‖dS σ (gen ε q) v‖ ^ 2) (Finset.mem_univ p)
    have hrest : ∑ q ∈ Finset.univ.erase p, wt q * sg ε q * ‖dS σ (gen ε q) v‖ ^ 2 ≤
        (Fintype.card (Fin n × Fin n) : ℝ) * (C ^ 2 * ‖v‖ ^ 2) := by
      calc _ ≤ ∑ q ∈ Finset.univ.erase p, C ^ 2 * ‖v‖ ^ 2 :=
            Finset.sum_le_sum fun q _ => hterm q
        _ = ((Finset.univ.erase p).card : ℝ) * (C ^ 2 * ‖v‖ ^ 2) := by
            rw [Finset.sum_const, nsmul_eq_mul]
        _ ≤ _ := mul_le_mul_of_nonneg_right
            (by exact_mod_cast (Finset.card_erase_le.trans (le_of_eq Finset.card_univ)))
            (by positivity)
    have hwp := wt_ge p
    rw [hsgp] at hsplit
    have e2 : (1 / 2) * ‖dS σ (gen ε p) v‖ ^ 2 ≤ wt p * ‖dS σ (gen ε p) v‖ ^ 2 :=
      mul_le_mul_of_nonneg_right hwp (sq_nonneg _)
    have e3 : -c * ‖v‖ ^ 2 ≤ |c| * ‖v‖ ^ 2 :=
      mul_le_mul_of_nonneg_right (neg_le_abs c) (sq_nonneg _)
    have hsq : ‖dS σ (gen ε p) v‖ ^ 2 ≤ K * ‖v‖ ^ 2 := by
      rw [hK]
      nlinarith [hsplit, hsum, hrest, e2, e3]
    have hK0 : 0 ≤ K := by positivity
    have hle : ‖dS σ (gen ε p) v‖ ≤ Real.sqrt K * ‖v‖ := by
      rw [← Real.sqrt_sq (norm_nonneg (dS σ (gen ε p) v)), ← Real.sqrt_sq hv0,
        ← Real.sqrt_mul hK0]
      exact Real.sqrt_le_sqrt hsq
    exact hle.trans (mul_le_mul_of_nonneg_right (le_max_right _ _) hv0)

end Formalism.L2.SG.Pf.admitted

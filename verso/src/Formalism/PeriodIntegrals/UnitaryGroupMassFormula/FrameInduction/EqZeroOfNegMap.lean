import Formalism.FormalDegreeBessel.FormalDegreeRatio.GBasic

open Matrix Formalism.QuantumDeterminants Formalism.QuantumDeterminants.GBasic

noncomputable section
namespace PI.FrameInd.NegB

/- English proof (translation)
Unfold `herm`. Rewrite using `[← PJP k r, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, ← Matrix.star_mulVec]`. Simplify using `only [dotProduct, Formalism.REAL.Jm, Matrix.mulVec_diagonal, dK, Pi.star_apply]`.
-/
lemma herm_Pk (k r : ℕ) (x : Fin (2 * r + k + 1) → ℂ) :
    herm (Hpk k r) x x = ∑ i, star ((Pk k r *ᵥ x) i) * (dK k r i * (Pk k r *ᵥ x) i) := by
  unfold herm
  rw [← PJP k r, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec,
    ← Matrix.star_mulVec]
  simp only [dotProduct, Formalism.REAL.Jm, Matrix.mulVec_diagonal, dK, Pi.star_apply]

/- English proof (translation)
Rewrite using `[herm_Pk, Complex.re_sum]`. Use `Finset.sum_congr rfl (fun i _ => ?_)` and prove the remaining obligations. Apply the tactic sequence `by_cases h : i.val < r + k <;>`. Apply the tactic sequence `simp [h, dK, epsK, Complex.mul_re, Complex.normSq_apply, Complex.star_def] <;> ring`.
-/
lemma re_herm (k r : ℕ) (x : Fin (2 * r + k + 1) → ℂ) :
    (herm (Hpk k r) x x).re =
      ∑ i, (if i.val < r + k then (1 : ℝ) else -1) * Complex.normSq ((Pk k r *ᵥ x) i) := by
  rw [herm_Pk, Complex.re_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  by_cases h : i.val < r + k <;>
    simp [h, dK, epsK, Complex.mul_re, Complex.normSq_apply, Complex.star_def] <;> ring

/- English proof (translation)
Establish `hA : (Hpk k r * ((Pk k r)ᴴ * Formalism.REAL.Jm (epsK k r))) * Pk k r = 1`. Rewrite using `[Matrix.mul_assoc, PJP, Hpk_sq]`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[Matrix.mulVec_mulVec, hA]`. Use `_ = 0 := by rw [h, Matrix.mulVec_zero]`.
-/
lemma Pk_inj (k r : ℕ) (x : Fin (2 * r + k + 1) → ℂ) (h : Pk k r *ᵥ x = 0) : x = 0 := by
  have hA : (Hpk k r * ((Pk k r)ᴴ * Formalism.REAL.Jm (epsK k r))) * Pk k r = 1 := by
    rw [Matrix.mul_assoc, PJP, Hpk_sq]
  calc x = (1 : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) *ᵥ x := (Matrix.one_mulVec x).symm
    _ = (Hpk k r * ((Pk k r)ᴴ * Formalism.REAL.Jm (epsK k r))) *ᵥ (Pk k r *ᵥ x) := by
      rw [Matrix.mulVec_mulVec, hA]
    _ = 0 := by rw [h, Matrix.mulVec_zero]

def negMap (k r : ℕ) : (Fin (2 * r + k + 1) → ℂ) →ₗ[ℂ] (Fin (r + 1) → ℂ) :=
  (LinearMap.funLeft ℂ ℂ (fun a : Fin (r + 1) => (⟨r + k + a.val, by omega⟩ : Fin (2 * r + k + 1)))).comp
    (Matrix.mulVecLin (Pk k r))

/- English proof (translation)
Apply `Pk_inj k r x` to reduce the goal to its premises. Establish `hneg : ∀ i : Fin (2 * r + k + 1), ¬ i.val < r + k → (Pk k r *ᵥ x) i = 0`. Introduce `i hi`. Establish `h1` using `congrFun hx ⟨i.val - (r + k), by omega⟩`. Simplify using `only [negMap, LinearMap.comp_apply, LinearMap.funLeft_apply, Matrix.mulVecLin_apply, Pi.zero_apply] at h1`.

Establish `h2 : (⟨r + k + (i.val - (r + k)), by omega⟩ : Fin (2 * r + k + 1)) = i`. Use `ext`. Simplify using `only`. Use linear arithmetic over natural numbers and integers. Rewrite `h1` using `[h2]`.

Conclude with `h1`. Establish `hterm : ∀ i ∈ Finset.univ, 0 ≤ (if i.val < r + k then (1 : ℝ) else -1) * Complex.normSq ((Pk k r *ᵥ x) i)`. Introduce `i _`. Distinguish the cases in `h : i.val < r + k`. Rewrite using `[if_pos h, one_mul]`.

Conclude with `Complex.normSq_nonneg _`. Rewrite using `[if_neg h, hneg i h, map_zero, mul_zero]`. Establish `hsum` using `re_herm k r x`. Establish `hzero : ∑ i, (if i.val < r + k then (1 : ℝ) else -1) * Complex.normSq ((Pk k r *ᵥ x) i) = 0` using `le_antisymm (hsum ▸ hre) (Finset.sum_nonneg hterm)`. Use extensionality with `i`.

Distinguish the cases in `h : i.val < r + k`. Establish `h1` using `(Finset.sum_eq_zero_iff_of_nonneg hterm).mp hzero i (Finset.mem_univ i)`. Rewrite `h1` using `[if_pos h, one_mul]`. Simplify using `using Complex.normSq_eq_zero.mp h1`. Simplify using `using hneg i h`.
-/
lemma eq_zero_of_negMap (k r : ℕ) (x : Fin (2 * r + k + 1) → ℂ) (hx : negMap k r x = 0)
    (hre : (herm (Hpk k r) x x).re ≤ 0) : x = 0 := by
  apply Pk_inj k r x
  have hneg : ∀ i : Fin (2 * r + k + 1), ¬ i.val < r + k → (Pk k r *ᵥ x) i = 0 := by
    intro i hi
    have h1 := congrFun hx ⟨i.val - (r + k), by omega⟩
    simp only [negMap, LinearMap.comp_apply, LinearMap.funLeft_apply, Matrix.mulVecLin_apply,
      Pi.zero_apply] at h1
    have h2 : (⟨r + k + (i.val - (r + k)), by omega⟩ : Fin (2 * r + k + 1)) = i := by
      ext
      simp only
      omega
    rw [h2] at h1
    exact h1
  have hterm : ∀ i ∈ Finset.univ, 0 ≤ (if i.val < r + k then (1 : ℝ) else -1) *
      Complex.normSq ((Pk k r *ᵥ x) i) := by
    intro i _
    by_cases h : i.val < r + k
    · rw [if_pos h, one_mul]
      exact Complex.normSq_nonneg _
    · rw [if_neg h, hneg i h, map_zero, mul_zero]
  have hsum := re_herm k r x
  have hzero : ∑ i, (if i.val < r + k then (1 : ℝ) else -1) * Complex.normSq ((Pk k r *ᵥ x) i) = 0 :=
    le_antisymm (hsum ▸ hre) (Finset.sum_nonneg hterm)
  ext i
  by_cases h : i.val < r + k
  · have h1 := (Finset.sum_eq_zero_iff_of_nonneg hterm).mp hzero i (Finset.mem_univ i)
    rw [if_pos h, one_mul] at h1
    simpa using Complex.normSq_eq_zero.mp h1
  · simpa using hneg i h

/- English proof (translation)
Establish `hinj : Function.Injective ((negMap k r).comp W.subtype)`. Rewrite using `[injective_iff_map_eq_zero]`. Introduce `a ha`. Establish `h1 : (a : Fin (2 * r + k + 1) → ℂ) = 0` using `eq_zero_of_negMap k r a ha (hW a a.2)`. Conclude with `Subtype.ext h1`.

Establish `h` using `LinearMap.finrank_le_finrank_of_injective hinj`. Rewrite `h` using `[Module.finrank_fin_fun]`. Conclude with `h`.
-/
theorem negBound (k r : ℕ) (W : Submodule ℂ (Fin (2 * r + k + 1) → ℂ))
    (hW : ∀ x ∈ W, (herm (Hpk k r) x x).re ≤ 0) : Module.finrank ℂ W ≤ r + 1 := by
  have hinj : Function.Injective ((negMap k r).comp W.subtype) := by
    rw [injective_iff_map_eq_zero]
    intro a ha
    have h1 : (a : Fin (2 * r + k + 1) → ℂ) = 0 :=
      eq_zero_of_negMap k r a ha (hW a a.2)
    exact Subtype.ext h1
  have h := LinearMap.finrank_le_finrank_of_injective hinj
  rw [Module.finrank_fin_fun] at h
  exact h

end PI.FrameInd.NegB

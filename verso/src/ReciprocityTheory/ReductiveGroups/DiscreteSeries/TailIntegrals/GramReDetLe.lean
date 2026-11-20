import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TailIntegrals.LinIndToLp

noncomputable section

open Matrix InnerProductSpace
open scoped ComplexConjugate

namespace ReciprocityTheory.ChartRestriction.DS.Xi.GSB

open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B ReciprocityTheory.ChartRestriction.DS.Xi.GS

variable {n m : ℕ}

/- English proof (translation)
Rewrite `hw` using `[Fintype.not_linearIndependent_iff]`. Take `⟨g, hg, i, hi⟩` from `hw`. Apply `Matrix.exists_mulVec_eq_zero_iff.mp` to reduce the goal to its premises. Use `⟨g, fun h => hi (congrFun h i), ?_⟩` and prove the remaining obligations. Use function extensionality and compare the values at `a`.

Simplify using `only [mulVec, dotProduct, GS.gram, Matrix.of_apply, Pi.zero_apply]`. Establish `hs : ∑ b, inner ℂ (w a) (w b) * g b = inner ℂ (w a) (∑ b, g b • w b)`. Rewrite using `[inner_sum]`. Use `congr 1`. Use function extensionality and compare the values at `b`.

Rewrite using `[inner_smul_right]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[hs, hg, inner_zero_right]`.
-/
theorem gram_det_zero (w : Fin m → EuclideanSpace ℂ (Fin n)) (hw : ¬ LinearIndependent ℂ w) :
    (GS.gram w).det = 0 := by
  rw [Fintype.not_linearIndependent_iff] at hw
  obtain ⟨g, hg, i, hi⟩ := hw
  apply Matrix.exists_mulVec_eq_zero_iff.mp
  refine ⟨g, fun h => hi (congrFun h i), ?_⟩
  funext a
  simp only [mulVec, dotProduct, GS.gram, Matrix.of_apply, Pi.zero_apply]
  have hs : ∑ b, inner ℂ (w a) (w b) * g b = inner ℂ (w a) (∑ b, g b • w b) := by
    rw [inner_sum]
    congr 1
    funext b
    rw [inner_smul_right]
    ring
  rw [hs, hg, inner_zero_right]

/- English proof (translation)
Distinguish the cases in `hv : LinearIndependent ℂ v`. Take `⟨u, τ, hu, hτ, -, hwe, -⟩` from `gs_fac v hv`. Rewrite using `[det_gram_of v u τ hu hτ hwe, Complex.ofReal_re]`. Establish `hτj : ∀ j, ‖τ j j‖ ≤ M`. Introduce `j`.

Establish `h1 : inner ℂ (u j) (v j) = τ j j`. Rewrite using `[hwe j]`. Conclude with `hu.inner_right_fintype (fun b => τ b j) j`. Rewrite using `[← h1]`. Combine the equalities or inequalities in the displayed calculation.

Combine the equalities or inequalities in the displayed calculation. Rewrite using `[gram_det_zero v hv, Complex.zero_re]`. Distinguish the cases in `hm : m = 0`. Substitute `hm` using the available equality. Simplify using the standard rewrite rules.

Conclude with `pow_nonneg (sq_nonneg M) m`.
-/
theorem gram_re_det_le (v : Fin m → EuclideanSpace ℂ (Fin n)) (M : ℝ) (hM : ∀ j, ‖v j‖ ≤ M) :
    (GS.gram v).det.re ≤ (M ^ 2) ^ m := by
  by_cases hv : LinearIndependent ℂ v
  · obtain ⟨u, τ, hu, hτ, -, hwe, -⟩ := gs_fac v hv
    rw [det_gram_of v u τ hu hτ hwe, Complex.ofReal_re]
    have hτj : ∀ j, ‖τ j j‖ ≤ M := by
      intro j
      have h1 : inner ℂ (u j) (v j) = τ j j := by
        rw [hwe j]; exact hu.inner_right_fintype (fun b => τ b j) j
      rw [← h1]
      calc ‖inner ℂ (u j) (v j)‖ ≤ ‖u j‖ * ‖v j‖ := norm_inner_le_norm _ _
        _ = ‖v j‖ := by rw [hu.1 j, one_mul]
        _ ≤ M := hM j
    calc ∏ j, ‖τ j j‖ ^ 2 ≤ ∏ _j : Fin m, M ^ 2 :=
          Finset.prod_le_prod (fun j _ => by positivity) fun j _ => pow_le_pow_left₀ (norm_nonneg _) (hτj j) 2
      _ = (M ^ 2) ^ m := by simp
  · rw [gram_det_zero v hv, Complex.zero_re]
    by_cases hm : m = 0
    · subst hm; simp
    · exact pow_nonneg (sq_nonneg M) m

end ReciprocityTheory.ChartRestriction.DS.Xi.GSB

namespace ReciprocityTheory.ChartRestriction.DS.Xi.GSB

open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B ReciprocityTheory.ChartRestriction.DS.Xi.GS

def linA {k r : ℕ} (A : Mat k r) :
    EuclideanSpace ℂ (Fin (2 * r + k + 1)) →ₗ[ℂ] EuclideanSpace ℂ (Fin (2 * r + k + 1)) :=
  (WithLp.linearEquiv 2 ℂ (Fin (2 * r + k + 1) → ℂ)).symm.toLinearMap ∘ₗ Matrix.toLin' A ∘ₗ
    (WithLp.linearEquiv 2 ℂ (Fin (2 * r + k + 1) → ℂ)).toLinearMap

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem linA_apply {k r : ℕ} (A : Mat k r) (x : EuclideanSpace ℂ (Fin (2 * r + k + 1))) :
    linA A x = WithLp.toLp 2 (A *ᵥ WithLp.ofLp x) := rfl

/- English proof (translation)
Use extensionality with `a b`. Simplify using `only [GS.gram, Matrix.of_apply, Matrix.one_apply]`. Conclude with `orthonormal_iff_ite.mp hu a b`.
-/
theorem gram_one {m n : ℕ} (u : Fin m → EuclideanSpace ℂ (Fin n)) (hu : Orthonormal ℂ u) : GS.gram u = 1 := by
  ext a b
  simp only [GS.gram, Matrix.of_apply, Matrix.one_apply]
  exact orthonormal_iff_ite.mp hu a b

/- English proof (translation)
Rewrite using `[ga_eq, ga_eq]`. Use `set w : Fin (l.val + 1) → EuclideanSpace ℂ (Fin (2 * r + k + 1)) := fun a => WithLp.toLp 2 (Y (Fin.castLE (by omega) a)) with hwdef`. Establish `hAw : (fun a : Fin (l.val + 1) => (WithLp.toLp 2 (A *ᵥ Y (Fin.castLE (by omega) a)) : EuclideanSpace ℂ (Fin (2 * r + k + 1)))) = fun a => linA A (w a)`. Use function extensionality and compare the values at `a`. Rewrite using `[linA_apply]`.

Rewrite using `[hAw]`. Distinguish the cases in `hw : LinearIndependent ℂ w`. Take `⟨u, τ, hu, hτ, -, hwe, -⟩` from `gs_fac w hw`. Establish `h1 : (fun a => linA A (w a)) = fun a => ∑ b, τ b a • linA A (u b)`. Use function extensionality and compare the values at `a`.

Rewrite using `[hwe a, map_sum]`. Simplify using `only [map_smul]`. Establish `hgw : (GS.gram w).det = (τᴴ).det * τ.det`. Rewrite using `[show w = (fun a => ∑ b, τ b a • u b) from funext hwe, gram_comb, gram_one u hu, Matrix.mul_one, det_mul]`. Establish `hv : ∀ b, ‖linA A (u b)‖ ≤ gN A`.

Introduce `b`. Use `norm_mulVec_le A (WithLp.ofLp (u b))` as an intermediate fact. Rewrite `this` using `[WithLp.toLp_ofLp, hu.1 b, mul_one]`. Rewrite using `[linA_apply]`. Conclude with `this`.

Establish `hle` using `gram_re_det_le (fun b => linA A (u b)) (gN A) hv`. Establish `hX` using `det_gram_of w u τ hu hτ hwe`. Rewrite using `[h1, gram_comb, det_mul, det_mul]`. Establish `e1 : (τᴴ).det * (GS.gram fun b => linA A (u b)).det * τ.det = (GS.gram w).det * (GS.gram fun b => linA A (u b)).det` using `by rw [hgw]; ring`. Rewrite using `[e1, hX, Complex.re_ofReal_mul]`.

Establish `hnn : (0 : ℝ) ≤ ∏ j, ‖τ j j‖ ^ 2` using `Finset.prod_nonneg fun j _ => by positivity`. Rewrite using `[Complex.ofReal_re, mul_comm]`. Conclude with `mul_le_mul_of_nonneg_right hle hnn`. Establish `hw' : ¬ LinearIndependent ℂ (fun a => linA A (w a))` using `fun h => hw (h.of_comp (linA A))`. Rewrite using `[gram_det_zero _ hw', gram_det_zero _ hw, Complex.zero_re, mul_zero]`.
-/
theorem ga_mul_le (k r : ℕ) (A : Mat k r) (l : Fin (r + 1)) (Y : Fin (r + 1) → Fin (2 * r + k + 1) → ℂ) :
    Ga k r l (fun a => A *ᵥ Y a) ≤ (gN A ^ 2) ^ (l.val + 1) * Ga k r l Y := by
  rw [ga_eq, ga_eq]
  set w : Fin (l.val + 1) → EuclideanSpace ℂ (Fin (2 * r + k + 1)) :=
    fun a => WithLp.toLp 2 (Y (Fin.castLE (by omega) a)) with hwdef
  have hAw : (fun a : Fin (l.val + 1) =>
      (WithLp.toLp 2 (A *ᵥ Y (Fin.castLE (by omega) a)) : EuclideanSpace ℂ (Fin (2 * r + k + 1)))) =
      fun a => linA A (w a) := by
    funext a; rw [linA_apply]
  rw [hAw]
  by_cases hw : LinearIndependent ℂ w
  · obtain ⟨u, τ, hu, hτ, -, hwe, -⟩ := gs_fac w hw
    have h1 : (fun a => linA A (w a)) = fun a => ∑ b, τ b a • linA A (u b) := by
      funext a; rw [hwe a, map_sum]; simp only [map_smul]
    have hgw : (GS.gram w).det = (τᴴ).det * τ.det := by
      rw [show w = (fun a => ∑ b, τ b a • u b) from funext hwe, gram_comb, gram_one u hu, Matrix.mul_one, det_mul]
    have hv : ∀ b, ‖linA A (u b)‖ ≤ gN A := by
      intro b
      have := norm_mulVec_le A (WithLp.ofLp (u b))
      rw [WithLp.toLp_ofLp, hu.1 b, mul_one] at this
      rw [linA_apply]; exact this
    have hle := gram_re_det_le (fun b => linA A (u b)) (gN A) hv
    have hX := det_gram_of w u τ hu hτ hwe
    rw [h1, gram_comb, det_mul, det_mul]
    have e1 : (τᴴ).det * (GS.gram fun b => linA A (u b)).det * τ.det =
        (GS.gram w).det * (GS.gram fun b => linA A (u b)).det := by rw [hgw]; ring
    rw [e1, hX, Complex.re_ofReal_mul]
    have hnn : (0 : ℝ) ≤ ∏ j, ‖τ j j‖ ^ 2 := Finset.prod_nonneg fun j _ => by positivity
    rw [Complex.ofReal_re, mul_comm]
    exact mul_le_mul_of_nonneg_right hle hnn
  · have hw' : ¬ LinearIndependent ℂ (fun a => linA A (w a)) := fun h => hw (h.of_comp (linA A))
    rw [gram_det_zero _ hw', gram_det_zero _ hw, Complex.zero_re, mul_zero]

end ReciprocityTheory.ChartRestriction.DS.Xi.GSB

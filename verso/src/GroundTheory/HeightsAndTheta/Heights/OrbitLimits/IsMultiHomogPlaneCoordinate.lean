import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterRedC
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterRedF
import GroundTheory.HeightsAndTheta.Heights.Intersections.NoCommonComponentCoordinatesPlane
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Targets

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo
open scoped ContDiff

variable {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)]

def normSq (A : HermLine ι) (s : MRing ι) (z : (Σ k, ι k) → ℂ) : ℝ :=
  (‖eval z (map (Int.castRingHom ℂ) s)‖ / A.h z) ^ 2

def regLog (A : HermLine ι) (s : MRing ι) (ε : ℝ) (z : (Σ k, ι k) → ℂ) : ℝ :=
  Real.log (normSq A s z + ε) / 2

omit [∀ k, Fintype (ι k)] in
/- English proof (translation)
The claim follows from `sq_nonneg _`.
-/
theorem normSq_nonneg (A : HermLine ι) (s : MRing ι) (z : (Σ k, ι k) → ℂ) : 0 ≤ normSq A s z :=
  sq_nonneg _

/- English proof (translation)
Unfold `normSq`. Rewrite using `[eval_smul_of_isMultiHomog hs c z, A.smul c z hc, norm_mul, norm_prod]`. Establish `hC : (∏ k, ‖c k‖ ^ A.a k) = ∏ k, ‖c k ^ a k‖`. Use `Finset.prod_congr rfl fun k _ => ?_` and prove the remaining obligations. Rewrite using `[ha k, norm_pow, zpow_natCast]`.

Rewrite using `[hC, mul_div_mul_left _ _ (Finset.prod_ne_zero_iff.mpr fun k _ => norm_ne_zero_iff.mpr (pow_ne_zero _ (hc k)))]`.
-/
theorem normSq_smul {A : HermLine ι} {s : MRing ι} {a : K → ℕ} (ha : ∀ k, A.a k = a k)
    (hs : IsMultiHomog s a) (c : K → ℂ) (z : (Σ k, ι k) → ℂ) (hc : ∀ k, c k ≠ 0) :
    normSq A s (fun p => c p.1 * z p) = normSq A s z := by
  unfold normSq
  rw [eval_smul_of_isMultiHomog hs c z, A.smul c z hc, norm_mul, norm_prod]
  have hC : (∏ k, ‖c k‖ ^ A.a k) = ∏ k, ‖c k ^ a k‖ := by
    refine Finset.prod_congr rfl fun k _ => ?_
    rw [ha k, norm_pow, zpow_natCast]
  rw [hC, mul_div_mul_left _ _ (Finset.prod_ne_zero_iff.mpr fun k _ =>
    norm_ne_zero_iff.mpr (pow_ne_zero _ (hc k)))]

def regLine (A : HermLine ι) (s : MRing ι) (ε : ℝ) {a : K → ℕ} (ha : ∀ k, A.a k = a k)
    (hs : IsMultiHomog s a) : HermLine ι :=
  HermLine.ofWeight (fun z => -regLog A s ε z) fun c z hc => by
    simp only [regLog, normSq_smul ha hs c z hc]

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem regLine_a (A : HermLine ι) (s : MRing ι) (ε : ℝ) {a : K → ℕ} (ha : ∀ k, A.a k = a k)
    (hs : IsMultiHomog s a) : (regLine A s ε ha hs).a = 0 := rfl

/- English proof (translation)
Use function extensionality and compare the values at `z`. Simplify using `[regLine, HermLine.ofWeight, Real.log_exp]`.
-/
theorem log_regLine (A : HermLine ι) (s : MRing ι) (ε : ℝ) {a : K → ℕ} (ha : ∀ k, A.a k = a k)
    (hs : IsMultiHomog s a) : (fun z => Real.log ((regLine A s ε ha hs).h z)) = regLog A s ε := by
  funext z
  simp [regLine, HermLine.ofWeight, Real.log_exp]

/- English proof (translation)
Proceed by induction on `s using MvPolynomial.induction_on with`. Consider the case `C a => simpa only [map_C, eval_C] using contDiff_const`. Consider the case `add p q hp hq => simpa only [map_add, eval_add] using hp.add hq`. Consider the case `mul_X p i hp`. Simplify `hp.mul (contDiff_apply ℝ ℂ i)` using `only [map_mul, map_X, eval_mul, eval_X]`.
-/
theorem contDiff_evalC (s : MRing ι) :
    ContDiff ℝ ∞ (fun z : (Σ k, ι k) → ℂ => eval z (map (Int.castRingHom ℂ) s)) := by
  induction s using MvPolynomial.induction_on with
  | C a => simpa only [map_C, eval_C] using contDiff_const
  | add p q hp hq => simpa only [map_add, eval_add] using hp.add hq
  | mul_X p i hp =>
    simpa only [map_mul, map_X, eval_mul, eval_X] using hp.mul (contDiff_apply ℝ ℂ i)

/- English proof (translation)
Establish `hN : ContDiffOn ℝ ∞ (normSq A s) {z | ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0}`. Establish `h1` using `(((contDiff_norm_sq ℝ).comp (contDiff_evalC s)).contDiffOn (s := {z : (Σ k, ι k) → ℂ | ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0})).div (hA.pow 2) fun z hz => pow_ne_zero _ (A.pos z hz).ne'`. Conclude with `h1.congr fun z _ => by simp only [normSq, div_pow]; rfl`. Conclude with `((hN.add contDiffOn_const).log fun z _ => (add_pos_of_nonneg_of_pos (normSq_nonneg A s z) hε).ne').div_const 2`.
-/
theorem contDiffOn_regLog {A : HermLine ι} (hA : IsSmoothHerm A) (s : MRing ι) {ε : ℝ} (hε : 0 < ε) :
    ContDiffOn ℝ ∞ (regLog A s ε) {z | ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0} := by
  have hN : ContDiffOn ℝ ∞ (normSq A s) {z | ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0} := by
    have h1 := (((contDiff_norm_sq ℝ).comp (contDiff_evalC s)).contDiffOn (s := {z : (Σ k, ι k) → ℂ |
      ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0})).div (hA.pow 2) fun z hz => pow_ne_zero _ (A.pos z hz).ne'
    exact h1.congr fun z _ => by simp only [normSq, div_pow]; rfl
  exact ((hN.add contDiffOn_const).log fun z _ =>
    (add_pos_of_nonneg_of_pos (normSq_nonneg A s z) hε).ne').div_const 2

/- English proof (translation)
The claim follows from `Real.contDiff_exp.comp_contDiffOn (contDiffOn_regLog hA s hε).neg.neg`.
-/
theorem isSmoothHerm_regLine {A : HermLine ι} (hA : IsSmoothHerm A) {s : MRing ι} {ε : ℝ} (hε : 0 < ε)
    {a : K → ℕ} (ha : ∀ k, A.a k = a k) (hs : IsMultiHomog s a) :
    IsSmoothHerm (regLine A s ε ha hs) :=
  Real.contDiff_exp.comp_contDiffOn (contDiffOn_regLog hA s hε).neg.neg

/- English proof (translation)
Introduce `m hm k`. Rewrite `hm` using `[support_X, Finset.mem_singleton]`. Substitute `hm` using the available equality. Simplify using `[Finsupp.single_apply]`.
-/
theorem isMultiHomog_planeCoordinate (i : Fin 3) : IsMultiHomog (Xc 3 i) (fun _ => 1) := by
  intro m hm k
  rw [support_X, Finset.mem_singleton] at hm
  subst hm
  simp [Finsupp.single_apply]

def regularisedLogNormSecond : HermLine (PBlk 3) :=
  regLine (fsLine 3) (Xc 3 1) 1 (fun _ => rfl) (isMultiHomog_planeCoordinate 1)

end GroundTheory.Heights₂.Heights.Targets

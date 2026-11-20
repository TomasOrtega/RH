import Mathlib
import Development.AbelianVarietyTheory.Definitions.Jets.SideFam
import Development.AbelianVarietyTheory.Definitions.Jets.SumIoPr
import Formalism.HermitianCurvature.HermitianCurvatureProofs.DilationUnipotentWeylMeasure
import Formalism.HermitianCurvature.HermitianCurvatureProofs.NormDiagonalEntryDilationGeneratorLeOne
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.CkOnInCCCongrOnGroup
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.DiscreteSeriesUnitarySmoothBasic
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.MatrixCoefficientSmoothDerivatives
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.PolynomialProperness.ZhatNormLinearBound
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.KFiniteDerivativesFiniteSpan
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.SumNonneg
open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

namespace GlobalTheory
namespace CoefDecay

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {k r : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]

/- English proof (translation)
Establish `h1 : B.Rw v (0 : B.Mat k r → E) = 0`. Unfold `B.Rw`. Proceed by induction on `v with`. Consider the case `nil => rfl`. Consider the case `cons X v ih`.

Rewrite using `[List.foldr_cons, ih]`. Use function extensionality and compare the values at `g`. Simplify using `[Formalism.REAL.RdV]`. Unfold `B.dLR`. Rewrite using `[h1]`.

Proceed by induction on `u with`. Consider the case `nil => rfl`. Consider the case `cons X u ih`. Rewrite using `[List.foldr_cons, ih]`. Use function extensionality and compare the values at `g`.

Simplify using `[B.LdV]`.
-/
theorem dLR_zero (u v : List (B.Mat k r)) : B.dLR u v (0 : B.Mat k r → E) = 0 := by
  have h1 : B.Rw v (0 : B.Mat k r → E) = 0 := by
    unfold B.Rw
    induction v with
    | nil => rfl
    | cons X v ih =>
      rw [List.foldr_cons, ih]
      funext g
      simp [Formalism.REAL.RdV]
  unfold B.dLR
  rw [h1]
  induction u with
  | nil => rfl
  | cons X u ih =>
    rw [List.foldr_cons, ih]
    funext g
    simp [B.LdV]

/- English proof (translation)
Proceed by induction on `t using Finset.induction_on with`. Consider the case `empty`. Rewrite using `[Finset.sum_empty]`. Use `⟨fun g₀ _ => ⟨Set.univ, 0, isOpen_univ, trivial, contDiffOn_const, fun _ _ _ => rfl⟩, fun m => ⟨0, fun g₀ _ => ⟨Set.univ, 0, isOpen_univ, trivial, contDiffOn_const, fun _ _ _ => rfl⟩, ?_⟩⟩` and prove the remaining obligations. Introduce `u v _ _ _ g _`.

Simplify using `[dLR_zero]`. Consider the case `insert i t hi ih`. Rewrite using `[Finset.sum_insert hi]`. Take `⟨h1, h2⟩` from `hf i (Finset.mem_insert_self _ _)`. Take `⟨h3, h4⟩` from `ih fun j hj => hf j (Finset.mem_insert_of_mem hj)`.

Use `⟨Formalism.FourierDecayAlt.P.B4.ckOn_add h1 h3, fun m => ?_⟩` and prove the remaining obligations. Take `⟨c, hc⟩` from `h2 m`. Take `⟨c', hc'⟩` from `h4 m`. Conclude with `⟨_, (Formalism.FourierDecayAlt.P.matrix_coefficient_linear k r E A m _ _ c c' 1 hc hc').1⟩`.
-/
theorem sum_mem {ι : Type} (A : ℝ) (f : ι → B.Mat k r → E) (t : Finset ι)
    (hf : ∀ i ∈ t, B.CkOn ⊤ (B.GV k r) (f i) ∧ ∀ m : ℕ, B.InCC A m (f i)) :
    B.CkOn ⊤ (B.GV k r) (∑ i ∈ t, f i) ∧ ∀ m : ℕ, B.InCC A m (∑ i ∈ t, f i) := by
  classical
  induction t using Finset.induction_on with
  | empty =>
    rw [Finset.sum_empty]
    refine ⟨fun g₀ _ => ⟨Set.univ, 0, isOpen_univ, trivial, contDiffOn_const, fun _ _ _ => rfl⟩,
      fun m => ⟨0, fun g₀ _ => ⟨Set.univ, 0, isOpen_univ, trivial, contDiffOn_const, fun _ _ _ => rfl⟩, ?_⟩⟩
    intro u v _ _ _ g _
    simp [dLR_zero]
  | insert i t hi ih =>
    rw [Finset.sum_insert hi]
    obtain ⟨h1, h2⟩ := hf i (Finset.mem_insert_self _ _)
    obtain ⟨h3, h4⟩ := ih fun j hj => hf j (Finset.mem_insert_of_mem hj)
    refine ⟨Formalism.FourierDecayAlt.P.B4.ckOn_add h1 h3, fun m => ?_⟩
    obtain ⟨c, hc⟩ := h2 m
    obtain ⟨c', hc'⟩ := h4 m
    exact ⟨_, (Formalism.FourierDecayAlt.P.matrix_coefficient_linear k r E A m _ _ c c' 1 hc hc').1⟩

end CoefDecay

namespace CoefDecay

/- English proof (translation)
Take `⟨C, Ws, -, hb⟩` from `GlobalTheory.BesselDecay.decay_TK H k r ε mu h R hR hgap hok x hx`. Establish `hys : y ∈ R.sm` using `(GlobalTheory.rep_basic_of_isDS H.1.2.2.1 k r ε mu R hR).2.2.2.2.1 y hy`. Use `⟨C * (Ws.map fun W => ‖PI.UpqRep.dsigW (k := k) (r := r) R.σ W y‖).sum, fun g hg => ?_⟩` and prove the remaining obligations. Establish `pg` using `GlobalTheory.BesselDecay.gN_pos' hg`. Establish `h3 : B.gN g ^ (aOf r h - 1) * B.gN g ^ (1 - aOf r h) = 1`.

Rewrite using `[← Real.rpow_add pg]`. Simplify using the standard rewrite rules. Establish `pg' : 0 < B.gN g ^ (aOf r h - 1)` using `Real.rpow_pos_of_pos pg _`. Use `(mul_le_mul_of_nonneg_left (hb y hys g hg) pg'.le).trans (le_of_eq ?_)` and prove the remaining obligations. Rewrite using `[mul_left_comm, h3, mul_one]`.
-/
private theorem pair_bound (H : Hyps) {k r : ℕ} {ε : Fin (2 * r + k + 1) → Bool} {mu : Fin (2 * r + k + 1) → ℝ} {h : ℝ}
    (R : Rep k r) (hR : R.IsDS ε mu) (hgap : Formalism.QuantumDeterminants.GapAtLeast ε mu h) (hok : GapOK k r h)
    (x y : R.H) (hx : x ∈ R.TK) (hy : y ∈ R.TK) :
    ∃ c : ℝ, ∀ g ∈ GG k r, B.gN g ^ (aOf r h - 1) * ‖⟪x, R.σ g y⟫_ℂ‖ ≤ c := by
  obtain ⟨C, Ws, -, hb⟩ := GlobalTheory.BesselDecay.decay_TK H k r ε mu h R hR hgap hok x hx
  have hys : y ∈ R.sm := (GlobalTheory.rep_basic_of_isDS H.1.2.2.1 k r ε mu R hR).2.2.2.2.1 y hy
  refine ⟨C * (Ws.map fun W => ‖PI.UpqRep.dsigW (k := k) (r := r) R.σ W y‖).sum, fun g hg => ?_⟩
  have pg := GlobalTheory.BesselDecay.gN_pos' hg
  have h3 : B.gN g ^ (aOf r h - 1) * B.gN g ^ (1 - aOf r h) = 1 := by
    rw [← Real.rpow_add pg]; simp
  have pg' : 0 < B.gN g ^ (aOf r h - 1) := Real.rpow_pos_of_pos pg _
  refine (mul_le_mul_of_nonneg_left (hb y hys g hg) pg'.le).trans (le_of_eq ?_)
  rw [mul_left_comm, h3, mul_one]

/- English proof (translation)
Introduce `H k r ε mu h R hR hgap hok x hx y hy m`. Take `⟨M, xs, hxs, hxa⟩` from `GlobalTheory.UnitBoxWords.box_words H.1.2.2.1 k r ε mu R hR x hx m`. Take `⟨N, ys, hys, hyb⟩` from `GlobalTheory.UnitBoxWords.box_words H.1.2.2.1 k r ε mu R hR y hy m`. Use `choose c hc using fun (i : Fin M) (j : Fin N) => pair_bound H R hR hgap hok (xs i) (ys j) (hxs i) (hys j)`. Use `⟨∑ i, ∑ j, c i j, fun a b ha hb hl g hg => ?_⟩` and prove the remaining obligations.

Take `⟨co, hco, ea⟩` from `hxa a ha (by omega)`. Take `⟨co', hco', eb⟩` from `hyb b hb (by omega)`. Establish `pg' : 0 < B.gN g ^ (aOf r h - 1)` using `Real.rpow_pos_of_pos (GlobalTheory.BesselDecay.gN_pos' hg) _`. Rewrite using `[ea, eb, map_sum, sum_inner]`. Use `(mul_le_mul_of_nonneg_left (norm_sum_le _ _) pg'.le).trans ?_` and prove the remaining obligations.

Rewrite using `[Finset.mul_sum]`. Use `Finset.sum_le_sum fun i _ => ?_` and prove the remaining obligations. Rewrite using `[inner_sum]`. Use `(mul_le_mul_of_nonneg_left (norm_sum_le _ _) pg'.le).trans ?_` and prove the remaining obligations. Rewrite using `[Finset.mul_sum]`.

Use `Finset.sum_le_sum fun j _ => le_trans (mul_le_mul_of_nonneg_left ?_ pg'.le) (hc i j g hg)` and prove the remaining obligations. Rewrite using `[map_smul, inner_smul_left, inner_smul_right, norm_mul, norm_mul, RCLike.norm_conj, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs]`. Establish `n0` using `norm_nonneg ⟪xs i, R.σ g (ys j)⟫_ℂ`. Combine the equalities or inequalities in the displayed calculation. Conclude with `hco i`.

Conclude with `hco' j`. Use `_ = _ := by ring`.
-/
private theorem coef_bound : Hyps → ∀ (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (mu : Fin (2 * r + k + 1) → ℝ) (h : ℝ) (R : Rep k r), R.IsDS ε mu → Formalism.QuantumDeterminants.GapAtLeast ε mu h → GapOK k r h → ∀ x ∈ R.TK, ∀ y ∈ R.TK, ∀ m : ℕ, ∃ c : ℝ, ∀ a b : List (Mx k r), (∀ Y ∈ a, B.unitLie k r Y) → (∀ Y ∈ b, B.unitLie k r Y) → a.length + b.length ≤ m → ∀ g ∈ GG k r, B.gN g ^ (aOf r h - 1) * ‖⟪PI.UpqRep.dsigW (k := k) (r := r) R.σ a x, R.σ g (PI.UpqRep.dsigW (k := k) (r := r) R.σ b y)⟫_ℂ‖ ≤ c := by
  intro H k r ε mu h R hR hgap hok x hx y hy m
  obtain ⟨M, xs, hxs, hxa⟩ := GlobalTheory.UnitBoxWords.box_words H.1.2.2.1 k r ε mu R hR x hx m
  obtain ⟨N, ys, hys, hyb⟩ := GlobalTheory.UnitBoxWords.box_words H.1.2.2.1 k r ε mu R hR y hy m
  choose c hc using fun (i : Fin M) (j : Fin N) => pair_bound H R hR hgap hok (xs i) (ys j) (hxs i) (hys j)
  refine ⟨∑ i, ∑ j, c i j, fun a b ha hb hl g hg => ?_⟩
  obtain ⟨co, hco, ea⟩ := hxa a ha (by omega)
  obtain ⟨co', hco', eb⟩ := hyb b hb (by omega)
  have pg' : 0 < B.gN g ^ (aOf r h - 1) := Real.rpow_pos_of_pos (GlobalTheory.BesselDecay.gN_pos' hg) _
  rw [ea, eb, map_sum, sum_inner]
  refine (mul_le_mul_of_nonneg_left (norm_sum_le _ _) pg'.le).trans ?_
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun i _ => ?_
  rw [inner_sum]
  refine (mul_le_mul_of_nonneg_left (norm_sum_le _ _) pg'.le).trans ?_
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun j _ => le_trans (mul_le_mul_of_nonneg_left ?_ pg'.le) (hc i j g hg)
  rw [map_smul, inner_smul_left, inner_smul_right, norm_mul, norm_mul, RCLike.norm_conj, Complex.norm_real,
    Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs]
  have n0 := norm_nonneg ⟪xs i, R.σ g (ys j)⟫_ℂ
  calc _ ≤ 1 * (1 * ‖⟪xs i, R.σ g (ys j)⟫_ℂ‖) := by
        gcongr
        · exact hco i
        · exact hco' j
    _ = _ := by ring

end CoefDecay

/- English proof (translation)
Introduce `hH k r ε mu h R Wp _ _ _ _ Wq _ _ _ _ l l' F s hR hg hok hF`. Take `⟨n, x, y, X, hxy, hFe, -⟩` from `hF`. Establish `hK : PI.KFinSmooth` using `hH.1.2.2.1`. Establish `hsm : ∀ v ∈ R.TK, v ∈ R.sm` using `(GlobalTheory.rep_basic_of_isDS hK k r ε mu R hR).2.2.2.2.1`. Set `f : Fin n → B.Mat k r → (Wq →L[ℂ] Wp)` to `fun i g => ⟪x i, R.σ g (y i)⟫_ℂ • X i`.

Establish `hf : ∀ i ∈ (Finset.univ : Finset (Fin n)), B.CkOn ⊤ (B.GV k r) (f i) ∧ ∀ m : ℕ, B.InCC (aOf r h - 1) m (f i)`. Introduce `i _`. Take `⟨h1, h2⟩` from `GlobalTheory.CoeffDeriv.coeff_dLR hK k r ε mu R (Wq →L[ℂ] Wp) (X i) (f i) hR (x i) (hsm _ (hxy i).1) (y i) (hsm _ (hxy i).2) (fun g _ => rfl)`. Use `⟨h1, fun m => ?_⟩` and prove the remaining obligations. Take `⟨c, hc⟩` from `CoefDecay.coef_bound hH k r ε mu h R hR hg hok (x i) (hxy i).1 (y i) (hxy i).2 m`.

Use `⟨c * ‖X i‖, Formalism.FourierDecayAlt.P.B6.smooth_on_mono le_top h1, fun u v hu hv hlen g hgG => ?_⟩` and prove the remaining obligations. Rewrite using `[h2 u v (fun Y hY => (hu Y hY).1) (fun Y hY => (hv Y hY).1) g hgG, norm_smul, ← mul_assoc]`. Conclude with `mul_le_mul_of_nonneg_right (hc u v hu hv hlen g hgG) (norm_nonneg _)`. Take `⟨h1, h2⟩` from `CoefDecay.sum_mem (aOf r h - 1) f Finset.univ hf`. Establish `hc` using `GlobalTheory.ckOn_inCC_congr_on_group k r (Wq →L[ℂ] Wp) (aOf r h - 1) (∑ i, f i) F (fun g hgG => by rw [hFe g hgG, Finset.sum_apply])`.

Conclude with `⟨hc.1 h1, fun m => hc.2 m (h2 m)⟩`.
-/
theorem isCoef_ckOn_inCC : Hyps → ∀ (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (mu : Fin (2 * r + k + 1) → ℝ) (h : ℝ) (R : Rep k r) (Wp : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [CompleteSpace Wp] [FiniteDimensional ℂ Wp] (Wq : Type) [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [CompleteSpace Wq] [FiniteDimensional ℂ Wq] (l : R.H → Wp) (l' : R.H → Wq) (F : Mx k r → (Wq →L[ℂ] Wp)) (s : ℂ), R.IsDS ε mu → Formalism.QuantumDeterminants.GapAtLeast ε mu h → GapOK k r h → IsCoef R l l' F s → B.CkOn ⊤ (B.GV k r) F ∧ ∀ m : ℕ, B.InCC (aOf r h - 1) m F := by
  intro hH k r ε mu h R Wp _ _ _ _ Wq _ _ _ _ l l' F s hR hg hok hF
  obtain ⟨n, x, y, X, hxy, hFe, -⟩ := hF
  have hK : PI.KFinSmooth := hH.1.2.2.1
  have hsm : ∀ v ∈ R.TK, v ∈ R.sm := (GlobalTheory.rep_basic_of_isDS hK k r ε mu R hR).2.2.2.2.1
  let f : Fin n → B.Mat k r → (Wq →L[ℂ] Wp) := fun i g => ⟪x i, R.σ g (y i)⟫_ℂ • X i
  have hf : ∀ i ∈ (Finset.univ : Finset (Fin n)),
      B.CkOn ⊤ (B.GV k r) (f i) ∧ ∀ m : ℕ, B.InCC (aOf r h - 1) m (f i) := by
    intro i _
    obtain ⟨h1, h2⟩ := GlobalTheory.CoeffDeriv.coeff_dLR hK k r ε mu R (Wq →L[ℂ] Wp) (X i) (f i) hR (x i) (hsm _ (hxy i).1)
      (y i) (hsm _ (hxy i).2) (fun g _ => rfl)
    refine ⟨h1, fun m => ?_⟩
    obtain ⟨c, hc⟩ := CoefDecay.coef_bound hH k r ε mu h R hR hg hok (x i) (hxy i).1 (y i) (hxy i).2 m
    refine ⟨c * ‖X i‖, Formalism.FourierDecayAlt.P.B6.smooth_on_mono le_top h1, fun u v hu hv hlen g hgG => ?_⟩
    rw [h2 u v (fun Y hY => (hu Y hY).1) (fun Y hY => (hv Y hY).1) g hgG, norm_smul, ← mul_assoc]
    exact mul_le_mul_of_nonneg_right (hc u v hu hv hlen g hgG) (norm_nonneg _)
  obtain ⟨h1, h2⟩ := CoefDecay.sum_mem (aOf r h - 1) f Finset.univ hf
  have hc := GlobalTheory.ckOn_inCC_congr_on_group k r (Wq →L[ℂ] Wp) (aOf r h - 1) (∑ i, f i) F
    (fun g hgG => by rw [hFe g hgG, Finset.sum_apply])
  exact ⟨hc.1 h1, fun m => hc.2 m (h2 m)⟩

end GlobalTheory

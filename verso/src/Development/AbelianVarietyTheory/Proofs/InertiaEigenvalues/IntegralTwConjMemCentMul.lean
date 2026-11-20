import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TwConj
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.FourierMatch
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TwistedCentralizerIsNormOneTorus
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnitaryTwistInvolutionGLProperties
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsCommutantMulIntegralConjugate
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnitDiscriminantMatrixQuotientIsUnit

open GlobalTheory.Tw Matrix

namespace GlobalTheory.TwIntegral

section Basics

variable {E : Type} [NontriviallyNormedField E] [IsUltrametricDist E] {n : ℕ}

open Matrix in
variable {E : Type} [NontriviallyNormedField E] [IsUltrametricDist E] {n : ℕ} in
/- English proof (translation)
Introduce `i j`. Establish `hadj : ‖A.adjugate i j‖ ≤ 1`. Rewrite using `[adjugate_apply]`. Apply `_root_.GlobalTheory.norm_det_le_one_of_entries_le_one` to reduce the goal to its premises. Introduce `k l`.

Distinguish the cases in `hk : k = j`. Substitute `hk` using the available equality. Rewrite using `[updateRow_self]`. Distinguish the cases in `hl : l = i`. Substitute `hl` using the available equality.

Simplify using the standard rewrite rules. Simplify using `[Pi.single_apply, hl]`. Rewrite using `[updateRow_ne hk]`. Conclude with `hA k l`. Rewrite using `[inv_def, Ring.inverse_eq_inv', Matrix.smul_apply, smul_eq_mul, norm_mul, norm_inv, hd, inv_one, one_mul]`.

Conclude with `hadj`.
-/
theorem _root_.GlobalTheory.TwIntegral.intg_inv {A : Matrix (Fin n) (Fin n) E}
    (hA : ∀ i j, ‖A i j‖ ≤ 1) (hd : ‖A.det‖ = 1) :
    ∀ i j, ‖A⁻¹ i j‖ ≤ 1 := by
  intro i j
  have hadj : ‖A.adjugate i j‖ ≤ 1 := by
    rw [adjugate_apply]
    apply _root_.GlobalTheory.norm_det_le_one_of_entries_le_one
    intro k l
    by_cases hk : k = j
    · subst hk
      rw [updateRow_self]
      by_cases hl : l = i
      · subst hl; simp
      · simp [Pi.single_apply, hl]
    · rw [updateRow_ne hk]
      exact hA k l
  rw [inv_def, Ring.inverse_eq_inv', Matrix.smul_apply, smul_eq_mul, norm_mul, norm_inv, hd,
    inv_one, one_mul]
  exact hadj

open Matrix in
variable {E : Type} [NontriviallyNormedField E] [IsUltrametricDist E] {n : ℕ} in
/- English proof (translation)
Rewrite using `[isUnit_iff_isUnit_det]`. Use `isUnit_iff_ne_zero.mpr fun h => ?_` and prove the remaining obligations. Rewrite `hd` using `[h, norm_zero]`. Conclude with `zero_ne_one hd`.
-/
theorem _root_.GlobalTheory.TwIntegral.isUnit_of_norm_det {A : Matrix (Fin n) (Fin n) E} (hd : ‖A.det‖ = 1) :
    IsUnit A := by
  rw [isUnit_iff_isUnit_det]
  refine isUnit_iff_ne_zero.mpr fun h => ?_
  rw [h, norm_zero] at hd
  exact zero_ne_one hd

end Basics

open Matrix in
/- English proof (translation)
Use `haveI := _root_.GlobalTheory.JR.Unram.ultraE F (E := E)`. Establish `hΦ : ∀ i j, ‖_root_.GlobalTheory.Tw.Phi n E i j‖ ≤ 1`. Introduce `i j`. Rewrite using `[_root_.GlobalTheory.Tw.Model.Phi_apply']`. Apply the tactic sequence `split_ifs <;> simp`.

Establish `hΦt : ∀ i j, ‖(_root_.GlobalTheory.Tw.Phi n E)ᵀ i j‖ ≤ 1` using `fun i j => hΦ j i`. Establish `hinv` using `_root_.GlobalTheory.TwIntegral.intg_inv hg hd`. Establish `hH : ∀ i j, ‖(g⁻¹)ᴴ i j‖ ≤ 1`. Introduce `i j`. Rewrite using `[conjTranspose_apply, _root_.GlobalTheory.JR.Unram.norm_star F]`.

Conclude with `hinv j i`. Unfold `_root_.GlobalTheory.Tw.theta`. Use `⟨_root_.GlobalTheory.UnitDiscAlg.integ_mul (_root_.GlobalTheory.UnitDiscAlg.integ_mul hΦ hH) hΦt, ?_⟩` and prove the remaining obligations. Establish `h1 : (_root_.GlobalTheory.Tw.Phi n E).det * (_root_.GlobalTheory.Tw.Phi n E)ᵀ.det = 1`. Rewrite using `[← det_mul, _root_.GlobalTheory.Tw.Model.Phi_mul_transpose, det_one]`.

Rewrite using `[det_mul, det_mul, mul_right_comm, h1, one_mul, det_conjTranspose, det_nonsing_inv, Ring.inverse_eq_inv', _root_.GlobalTheory.JR.Unram.norm_star F, norm_inv, hd, inv_one]`.
-/
private theorem theta_integral_of_integral_of_norm_det_one (F E : Type)
    [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E]
    [_root_.GlobalTheory.JR.Unram F E] {n : ℕ} {g : Matrix (Fin n) (Fin n) E}
    (hg : ∀ i j, ‖g i j‖ ≤ 1) (hd : ‖g.det‖ = 1) :
    (∀ i j, ‖_root_.GlobalTheory.Tw.theta g i j‖ ≤ 1) ∧ ‖(_root_.GlobalTheory.Tw.theta g).det‖ = 1 := by
  haveI := _root_.GlobalTheory.JR.Unram.ultraE F (E := E)
  have hΦ : ∀ i j, ‖_root_.GlobalTheory.Tw.Phi n E i j‖ ≤ 1 := by
    intro i j
    rw [_root_.GlobalTheory.Tw.Model.Phi_apply']
    split_ifs <;> simp
  have hΦt : ∀ i j, ‖(_root_.GlobalTheory.Tw.Phi n E)ᵀ i j‖ ≤ 1 := fun i j => hΦ j i
  have hinv := _root_.GlobalTheory.TwIntegral.intg_inv hg hd
  have hH : ∀ i j, ‖(g⁻¹)ᴴ i j‖ ≤ 1 := by
    intro i j
    rw [conjTranspose_apply, _root_.GlobalTheory.JR.Unram.norm_star F]
    exact hinv j i
  unfold _root_.GlobalTheory.Tw.theta
  refine ⟨_root_.GlobalTheory.UnitDiscAlg.integ_mul (_root_.GlobalTheory.UnitDiscAlg.integ_mul hΦ hH) hΦt, ?_⟩
  have h1 : (_root_.GlobalTheory.Tw.Phi n E).det * (_root_.GlobalTheory.Tw.Phi n E)ᵀ.det = 1 := by
    rw [← det_mul, _root_.GlobalTheory.Tw.Model.Phi_mul_transpose, det_one]
  rw [det_mul, det_mul, mul_right_comm, h1, one_mul, det_conjTranspose, det_nonsing_inv,
    Ring.inverse_eq_inv', _root_.GlobalTheory.JR.Unram.norm_star F, norm_inv,
    hd, inv_one]

open Matrix in
/- English proof (translation)
Use `haveI := _root_.GlobalTheory.JR.Unram.ultraE F (E := E)`. Use `haveI := _root_.GlobalTheory.JR.Unram.lcE F (E := E)`. Use `haveI : ProperSpace E := ProperSpace.of_locallyCompactSpace E`. Take `⟨y, hy0, hy1⟩` from `NormedField.exists_norm_lt_one E`. Establish `hK : IsCompact (Metric.ball (0 : E) 1)` using `(isCompact_closedBall (0 : E) 1).of_isClosed_subset (IsUltrametricDist.isClosed_ball 0 1) Metric.ball_subset_closedBall`.

Take `⟨w, hw, hmax⟩` from `hK.exists_isMaxOn ⟨y, by simpa using hy1⟩ continuous_norm.continuousOn`. Take `⟨a, ha⟩` from `_root_.GlobalTheory.JR.Unram.unram (F := F) w`. Establish `hw1 : ‖w‖ < 1` using `by simpa using hw`. Establish `hyw : ‖y‖ ≤ ‖w‖` using `hmax (by simpa using hy1)`. Apply the tactic sequence `refine ⟨algebraMap F E a, _root_.GlobalTheory.JR.Unram.star_fix a, ?_, ?_, ?_⟩ <;> rw [norm_algebraMap', ← ha]`.

Conclude with `hy0.trans_le hyw`. Conclude with `hw1`. Introduce `z hz`. Conclude with `hmax (by simpa using hz)`.
-/
private theorem exists_star_fixed_uniformizer (F E : Type) [NontriviallyNormedField F]
    [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E]
    [_root_.GlobalTheory.JR.Unram F E] :
    ∃ ϖ : E, star ϖ = ϖ ∧ 0 < ‖ϖ‖ ∧ ‖ϖ‖ < 1 ∧ ∀ y : E, ‖y‖ < 1 → ‖y‖ ≤ ‖ϖ‖ := by
  haveI := _root_.GlobalTheory.JR.Unram.ultraE F (E := E)
  haveI := _root_.GlobalTheory.JR.Unram.lcE F (E := E)
  haveI : ProperSpace E := ProperSpace.of_locallyCompactSpace E
  obtain ⟨y, hy0, hy1⟩ := NormedField.exists_norm_lt_one E
  have hK : IsCompact (Metric.ball (0 : E) 1) :=
    (isCompact_closedBall (0 : E) 1).of_isClosed_subset (IsUltrametricDist.isClosed_ball 0 1)
      Metric.ball_subset_closedBall
  obtain ⟨w, hw, hmax⟩ := hK.exists_isMaxOn ⟨y, by simpa using hy1⟩ continuous_norm.continuousOn
  obtain ⟨a, ha⟩ := _root_.GlobalTheory.JR.Unram.unram (F := F) w
  have hw1 : ‖w‖ < 1 := by simpa using hw
  have hyw : ‖y‖ ≤ ‖w‖ := hmax (by simpa using hy1)
  refine ⟨algebraMap F E a, _root_.GlobalTheory.JR.Unram.star_fix a,
    ?_, ?_, ?_⟩ <;> rw [norm_algebraMap', ← ha]
  · exact hy0.trans_le hyw
  · exact hw1
  · intro z hz
    exact hmax (by simpa using hz)

open Matrix in
/- English proof (translation)
Establish `e1' : τ Q * τ Qi = 1` using `by rw [← hτmul, e1, hτone]`. Establish `e3' : τ X * τ Xi = 1` using `by rw [← hτmul, e3, hτone]`. Establish `e2' : τ Q * τ X = (w * τ c ^ 3 + (c * τ c) ^ 3) * (w + τ c ^ 2)`. Rewrite using `[← hτmul, e2, hτP]`. Establish `hmain : Q * τ Q = τ c * c`.

Combine the equalities or inequalities in the displayed calculation. Rewrite using `[e2, e2', hτX, hX]`. Expand and normalize the polynomial expressions, which then agree. Use `_ = τ c * c := by rw [e3, e3', mul_one, mul_one]`. Combine the equalities or inequalities in the displayed calculation.
-/
private theorem mul_inv_mul_conj_eq_one_of_norm_quotient {B : Type} [CommRing B] (τ : B → B)
    (w c Q Qi X Xi : B) (hτmul : ∀ g h, τ (g * h) = τ g * τ h) (hτone : τ 1 = 1)
    (hX : X = (w + c ^ 3) * (w * c ^ 2 + (τ c * c) ^ 2))
    (hτX : τ X = (w + τ c ^ 3) * (w * τ c ^ 2 + (c * τ c) ^ 2))
    (hτP : τ ((w * c ^ 3 + (τ c * c) ^ 3) * (w + c ^ 2)) =
      (w * τ c ^ 3 + (c * τ c) ^ 3) * (w + τ c ^ 2))
    (e1 : Q * Qi = 1) (e2 : Q * X = (w * c ^ 3 + (τ c * c) ^ 3) * (w + c ^ 2))
    (e3 : X * Xi = 1) :
    c * Qi * τ (c * Qi) = 1 := by
  have e1' : τ Q * τ Qi = 1 := by rw [← hτmul, e1, hτone]
  have e3' : τ X * τ Xi = 1 := by rw [← hτmul, e3, hτone]
  have e2' : τ Q * τ X = (w * τ c ^ 3 + (c * τ c) ^ 3) * (w + τ c ^ 2) := by
    rw [← hτmul, e2, hτP]
  have hmain : Q * τ Q = τ c * c := by
    calc Q * τ Q = Q * τ Q * (X * Xi) * (τ X * τ Xi) := by rw [e3, e3', mul_one, mul_one]
      _ = (Q * X) * (τ Q * τ X) * Xi * τ Xi := by ring
      _ = τ c * c * (X * Xi) * (τ X * τ Xi) := by
          rw [e2, e2', hτX, hX]
          ring
      _ = τ c * c := by rw [e3, e3', mul_one, mul_one]
  calc c * Qi * τ (c * Qi) = (Q * τ Q) * Qi * τ Qi := by rw [hmain, hτmul]; ring
    _ = (Q * Qi) * (τ Q * τ Qi) := by ring
    _ = 1 := by rw [e1, e1', one_mul]

open Matrix in
/- English proof (translation)
Use `set N := _root_.GlobalTheory.Tw.nrm δ`. Use `set A := Algebra.adjoin E {N}`. Establish `hmem : ∀ g, g * N = N * g → g ∈ A` using `fun g hg => _root_.GlobalTheory.Tw.CentralizerAdjoin.mem_adjoin_of_commute N g hsep hg`. Establish `hNA : N ∈ A` using `Algebra.self_mem_adjoin_singleton E N`. Establish `hcomm : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a` using `fun a ha b hb =>`.

Use `letI : CommRing A := Algebra.adjoinCommRingOfComm E (by simp)`. Use `congrArg Subtype.val (mul_comm (⟨a, ha⟩ : A) ⟨b, hb⟩)`. Establish `hinvA : ∀ g ∈ A, IsUnit g → g⁻¹ ∈ A`. Introduce `g hg hu`. Establish `hd : IsUnit g.det` using `(isUnit_iff_isUnit_det g).mp hu`.

Apply `hmem` to reduce the goal to its premises. Combine the equalities or inequalities in the displayed calculation. Establish `hτA : ∀ g ∈ A, _root_.GlobalTheory.Tw.adj δ g ∈ A ∧ _root_.GlobalTheory.Tw.adj δ (_root_.GlobalTheory.Tw.adj δ g) = g` using `_root_.GlobalTheory.Tw.CentralizerAdjoin.adj_adjoin hδ`. Set `τA : A → A` to `fun g => ⟨_root_.GlobalTheory.Tw.adj δ g.1, (hτA g.1 g.2).1⟩`. Establish `hτmul : ∀ g h : A, τA (g * h) = τA g * τA h`.

Introduce `g h`. Apply `Subtype.ext` to reduce the goal to its premises. Use `show _root_.GlobalTheory.Tw.adj δ (g.1 * h.1) = _root_.GlobalTheory.Tw.adj δ g.1 * _root_.GlobalTheory.Tw.adj δ h.1`. Rewrite using `[_root_.GlobalTheory.Tw.CentralizerAdjoin.adj_mul' hδ]`. Conclude with `hcomm _ (hτA h.1 h.2).1 _ (hτA g.1 g.2).1`.

Establish `hτ0 : _root_.GlobalTheory.Tw.adj δ 0 = 0`. Establish `h` using `_root_.GlobalTheory.Tw.CentralizerAdjoin.adj_semi δ 1 0 0`. Simplify using `using h`. Establish `hτadd : ∀ g h : A, τA (g + h) = τA g + τA h`. Introduce `g h`.

Apply `Subtype.ext` to reduce the goal to its premises. Use `show _root_.GlobalTheory.Tw.adj δ (g.1 + h.1) = _root_.GlobalTheory.Tw.adj δ g.1 + _root_.GlobalTheory.Tw.adj δ h.1`. Establish `e` using `_root_.GlobalTheory.Tw.CentralizerAdjoin.adj_semi δ 1 g.1 h.1`. Simplify using `using e`. Establish `hτsmul : ∀ (r : E) (g : A), τA (r • g) = star r • τA g`.

Introduce `r g`. Apply `Subtype.ext` to reduce the goal to its premises. Use `show _root_.GlobalTheory.Tw.adj δ (r • g.1) = star r • _root_.GlobalTheory.Tw.adj δ g.1`. Establish `e` using `_root_.GlobalTheory.Tw.CentralizerAdjoin.adj_semi δ r g.1 0`. Simplify `e` using `[hτ0]`.

Establish `hτone : τA 1 = 1` using `Subtype.ext (_root_.GlobalTheory.Tw.CentralizerAdjoin.adj_one' hδ)`. Establish `hτpow : ∀ (g : A) (k : ℕ), τA (g ^ k) = τA g ^ k`. Introduce `g k`. Proceed by induction on `k with`. Consider the case `zero => simpa using hτone`.

Consider the case `succ k ih => rw [pow_succ, hτmul, ih, pow_succ]`. Establish `hττ : ∀ g : A, τA (τA g) = g` using `fun g => Subtype.ext (hτA g.1 g.2).2`. Establish `hcA : c ∈ A` using `hmem c hcN`. Establish `hsub : ∀ g : A, IsUnit g.1 → (g.1)⁻¹ ∈ A` using `fun g hg => hinvA g.1 g.2 hg`. Set `cA : A` to `⟨c, hcA⟩`.

Set `w : A` to `algebraMap E A ϖ`. Establish `hw : (w : Matrix (Fin n) (Fin n) E) = ϖ • 1` using `Algebra.algebraMap_eq_smul_one ϖ`. Establish `hτw : τA w = w` using `by show τA (algebraMap E A ϖ) = algebraMap E A ϖ`. Rewrite using `[Algebra.algebraMap_eq_smul_one, hτsmul, hτone, hϖ]`. Set `X : A` to `(w + cA ^ 3) * (w * cA ^ 2 + (τA cA * cA) ^ 2)`.

Set `P : A` to `(w * cA ^ 3 + (τA cA * cA) ^ 3) * (w + cA ^ 2)`. Establish `hXm : X.1 = (ϖ • 1 + c ^ 3) * (ϖ • c ^ 2 + (_root_.GlobalTheory.Tw.adj δ c * c) ^ 2)` using `by show ((w : Matrix (Fin n) (Fin n) E) + c ^ 3) * ((w : Matrix (Fin n) (Fin n) E) * c ^ 2 + (_root_.GlobalTheory.Tw.adj δ c * c) ^ 2) = _`. Rewrite using `[hw, smul_mul_assoc, one_mul]`. Establish `hPm : P.1 = (ϖ • c ^ 3 + (_root_.GlobalTheory.Tw.adj δ c * c) ^ 3) * (ϖ • 1 + c ^ 2)` using `by show ((w : Matrix (Fin n) (Fin n) E) * c ^ 3 + (_root_.GlobalTheory.Tw.adj δ c * c) ^ 3) * ((w : Matrix (Fin n) (Fin n) E) + c ^ 2) = _`. Rewrite using `[hw, smul_mul_assoc, one_mul]`.

Establish `hXu : IsUnit X.1` using `hXm ▸ hP3.mul hP4`. Establish `hXd : IsUnit (X.1).det` using `(isUnit_iff_isUnit_det _).mp hXu`. Set `Xi : A` to `⟨(X.1)⁻¹, hsub X hXu⟩`. Set `QA : A` to `P * Xi`. Establish `hQm : QA.1 = (ϖ • c ^ 3 + (_root_.GlobalTheory.Tw.adj δ c * c) ^ 3) * (ϖ • 1 + c ^ 2) * ((ϖ • 1 + c ^ 3) * (ϖ • c ^ 2 + (_root_.GlobalTheory.Tw.adj δ c * c) ^ 2))⁻¹` using `by show P.1 * (X.1)⁻¹ = _`.

Rewrite using `[hPm, hXm]`. Establish `hQu : IsUnit QA.1` using `hQm ▸ hQ`. Establish `hQd : IsUnit (QA.1).det` using `(isUnit_iff_isUnit_det _).mp hQu`. Set `Qi : A` to `⟨(QA.1)⁻¹, hsub QA hQu⟩`. Establish `e1 : QA * Qi = 1` using `Subtype.ext (mul_nonsing_inv _ hQd)`.

Establish `e2 : QA * X = P` using `Subtype.ext (nonsing_inv_mul_cancel_right _ _ hXd)`. Establish `e3 : X * Xi = 1` using `Subtype.ext (mul_nonsing_inv _ hXd)`. Establish `hτX : τA X = (w + τA cA ^ 3) * (w * τA cA ^ 2 + (cA * τA cA) ^ 2)`. Simplify using `only [X, hτmul, hτadd, hτpow, hττ, hτw]`. Establish `hτP : τA P = (w * τA cA ^ 3 + (cA * τA cA) ^ 3) * (w + τA cA ^ 2)`.

Simplify using `only [P, hτmul, hτadd, hτpow, hττ, hτw]`. Use `letI : CommRing A := Algebra.adjoinCommRingOfComm E (by simp)`. Establish `htt : cA * Qi * τA (cA * Qi) = 1` using `mul_inv_mul_conj_eq_one_of_norm_quotient τA w cA QA Qi X Xi hτmul hτone rfl hτX hτP e1 e2 e3`. Rewrite using `[← hQm]`. Establish `ht : IsUnit (c * (QA.1)⁻¹)` using `hc.mul ((isUnit_nonsing_inv_iff).mpr hQu)`.

Establish `htt' : c * (QA.1)⁻¹ * _root_.GlobalTheory.Tw.adj δ (c * (QA.1)⁻¹) = 1` using `congrArg Subtype.val htt`. Rewrite `htt'` using `[_root_.GlobalTheory.Tw.Model.adj_eq hδ ht]`. Establish `hθ` using `((_root_.GlobalTheory.Tw.theta_props n E).2.1 _ ht).1`. Establish `hM : IsUnit (δ * _root_.GlobalTheory.Tw.theta (c * (QA.1)⁻¹) * δ⁻¹)` using `(hδ.mul hθ).mul ((isUnit_nonsing_inv_iff).mpr hδ)`. Establish `hMd` using `(isUnit_iff_isUnit_det _).mp hM`.

Establish `hδd` using `(isUnit_iff_isUnit_det _).mp hδ`. Establish `heq : c * (QA.1)⁻¹ = δ * _root_.GlobalTheory.Tw.theta (c * (QA.1)⁻¹) * δ⁻¹`. Combine the equalities or inequalities in the displayed calculation. Use `⟨ht, ?_⟩` and prove the remaining obligations. Use `show c * (QA.1)⁻¹ * δ = δ * _root_.GlobalTheory.Tw.theta (c * (QA.1)⁻¹)`.

Rewrite using `[heq, nonsing_inv_mul_cancel_right _ _ hδd, ← heq]`.
-/
private theorem mul_inv_quotient_mem_twistedCentralizerGL_lemma_3 {E : Type} [Field E] [StarRing E]
    {n : ℕ} (δ c : Matrix (Fin n) (Fin n) E) (ϖ : E) (hδ : IsUnit δ) (hϖ : star ϖ = ϖ)
    (hsep : (_root_.GlobalTheory.Tw.nrm δ).charpoly.Separable) (hc : IsUnit c)
    (hcN : c * _root_.GlobalTheory.Tw.nrm δ = _root_.GlobalTheory.Tw.nrm δ * c)
    (hP3 : IsUnit (ϖ • 1 + c ^ 3))
    (hP4 : IsUnit (ϖ • c ^ 2 + (_root_.GlobalTheory.Tw.adj δ c * c) ^ 2))
    (hQ : IsUnit ((ϖ • c ^ 3 + (_root_.GlobalTheory.Tw.adj δ c * c) ^ 3) * (ϖ • 1 + c ^ 2) *
      ((ϖ • 1 + c ^ 3) * (ϖ • c ^ 2 + (_root_.GlobalTheory.Tw.adj δ c * c) ^ 2))⁻¹)) :
    c * ((ϖ • c ^ 3 + (_root_.GlobalTheory.Tw.adj δ c * c) ^ 3) * (ϖ • 1 + c ^ 2) *
      ((ϖ • 1 + c ^ 3) * (ϖ • c ^ 2 + (_root_.GlobalTheory.Tw.adj δ c * c) ^ 2))⁻¹)⁻¹ ∈
      _root_.GlobalTheory.Tw.cent δ := by
  set N := _root_.GlobalTheory.Tw.nrm δ
  set A := Algebra.adjoin E {N}
  have hmem : ∀ g, g * N = N * g → g ∈ A := fun g hg =>
    _root_.GlobalTheory.Tw.CentralizerAdjoin.mem_adjoin_of_commute N g hsep hg
  have hNA : N ∈ A := Algebra.self_mem_adjoin_singleton E N
  have hcomm : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a := fun a ha b hb =>
    letI : CommRing A := Algebra.adjoinCommRingOfComm E (by simp)
    congrArg Subtype.val (mul_comm (⟨a, ha⟩ : A) ⟨b, hb⟩)
  have hinvA : ∀ g ∈ A, IsUnit g → g⁻¹ ∈ A := by
    intro g hg hu
    have hd : IsUnit g.det := (isUnit_iff_isUnit_det g).mp hu
    apply hmem
    calc g⁻¹ * N = g⁻¹ * N * (g * g⁻¹) := by rw [mul_nonsing_inv _ hd, mul_one]
      _ = g⁻¹ * (N * g) * g⁻¹ := by simp only [mul_assoc]
      _ = g⁻¹ * (g * N) * g⁻¹ := by rw [hcomm N hNA g hg]
      _ = N * g⁻¹ := by rw [← mul_assoc, nonsing_inv_mul _ hd, one_mul]
  have hτA : ∀ g ∈ A, _root_.GlobalTheory.Tw.adj δ g ∈ A ∧
      _root_.GlobalTheory.Tw.adj δ (_root_.GlobalTheory.Tw.adj δ g) = g :=
    _root_.GlobalTheory.Tw.CentralizerAdjoin.adj_adjoin hδ
  let τA : A → A := fun g => ⟨_root_.GlobalTheory.Tw.adj δ g.1, (hτA g.1 g.2).1⟩
  have hτmul : ∀ g h : A, τA (g * h) = τA g * τA h := by
    intro g h
    apply Subtype.ext
    show _root_.GlobalTheory.Tw.adj δ (g.1 * h.1) =
      _root_.GlobalTheory.Tw.adj δ g.1 * _root_.GlobalTheory.Tw.adj δ h.1
    rw [_root_.GlobalTheory.Tw.CentralizerAdjoin.adj_mul' hδ]
    exact hcomm _ (hτA h.1 h.2).1 _ (hτA g.1 g.2).1
  have hτ0 : _root_.GlobalTheory.Tw.adj δ 0 = 0 := by
    have h := _root_.GlobalTheory.Tw.CentralizerAdjoin.adj_semi δ 1 0 0
    simpa using h
  have hτadd : ∀ g h : A, τA (g + h) = τA g + τA h := by
    intro g h
    apply Subtype.ext
    show _root_.GlobalTheory.Tw.adj δ (g.1 + h.1) =
      _root_.GlobalTheory.Tw.adj δ g.1 + _root_.GlobalTheory.Tw.adj δ h.1
    have e := _root_.GlobalTheory.Tw.CentralizerAdjoin.adj_semi δ 1 g.1 h.1
    simpa using e
  have hτsmul : ∀ (r : E) (g : A), τA (r • g) = star r • τA g := by
    intro r g
    apply Subtype.ext
    show _root_.GlobalTheory.Tw.adj δ (r • g.1) = star r • _root_.GlobalTheory.Tw.adj δ g.1
    have e := _root_.GlobalTheory.Tw.CentralizerAdjoin.adj_semi δ r g.1 0
    simpa [hτ0] using e
  have hτone : τA 1 = 1 := Subtype.ext (_root_.GlobalTheory.Tw.CentralizerAdjoin.adj_one' hδ)
  have hτpow : ∀ (g : A) (k : ℕ), τA (g ^ k) = τA g ^ k := by
    intro g k
    induction k with
    | zero => simpa using hτone
    | succ k ih => rw [pow_succ, hτmul, ih, pow_succ]
  have hττ : ∀ g : A, τA (τA g) = g := fun g => Subtype.ext (hτA g.1 g.2).2
  have hcA : c ∈ A := hmem c hcN
  have hsub : ∀ g : A, IsUnit g.1 → (g.1)⁻¹ ∈ A := fun g hg => hinvA g.1 g.2 hg
  let cA : A := ⟨c, hcA⟩
  let w : A := algebraMap E A ϖ
  have hw : (w : Matrix (Fin n) (Fin n) E) = ϖ • 1 := Algebra.algebraMap_eq_smul_one ϖ
  have hτw : τA w = w := by
    show τA (algebraMap E A ϖ) = algebraMap E A ϖ
    rw [Algebra.algebraMap_eq_smul_one, hτsmul, hτone, hϖ]
  let X : A := (w + cA ^ 3) * (w * cA ^ 2 + (τA cA * cA) ^ 2)
  let P : A := (w * cA ^ 3 + (τA cA * cA) ^ 3) * (w + cA ^ 2)
  have hXm : X.1 =
      (ϖ • 1 + c ^ 3) * (ϖ • c ^ 2 + (_root_.GlobalTheory.Tw.adj δ c * c) ^ 2) := by
    show ((w : Matrix (Fin n) (Fin n) E) + c ^ 3) *
      ((w : Matrix (Fin n) (Fin n) E) * c ^ 2 + (_root_.GlobalTheory.Tw.adj δ c * c) ^ 2) = _
    rw [hw, smul_mul_assoc, one_mul]
  have hPm : P.1 =
      (ϖ • c ^ 3 + (_root_.GlobalTheory.Tw.adj δ c * c) ^ 3) * (ϖ • 1 + c ^ 2) := by
    show ((w : Matrix (Fin n) (Fin n) E) * c ^ 3 + (_root_.GlobalTheory.Tw.adj δ c * c) ^ 3) *
      ((w : Matrix (Fin n) (Fin n) E) + c ^ 2) = _
    rw [hw, smul_mul_assoc, one_mul]
  have hXu : IsUnit X.1 := hXm ▸ hP3.mul hP4
  have hXd : IsUnit (X.1).det := (isUnit_iff_isUnit_det _).mp hXu
  let Xi : A := ⟨(X.1)⁻¹, hsub X hXu⟩
  let QA : A := P * Xi
  have hQm : QA.1 =
      (ϖ • c ^ 3 + (_root_.GlobalTheory.Tw.adj δ c * c) ^ 3) * (ϖ • 1 + c ^ 2) *
      ((ϖ • 1 + c ^ 3) * (ϖ • c ^ 2 + (_root_.GlobalTheory.Tw.adj δ c * c) ^ 2))⁻¹ := by
    show P.1 * (X.1)⁻¹ = _
    rw [hPm, hXm]
  have hQu : IsUnit QA.1 := hQm ▸ hQ
  have hQd : IsUnit (QA.1).det := (isUnit_iff_isUnit_det _).mp hQu
  let Qi : A := ⟨(QA.1)⁻¹, hsub QA hQu⟩
  have e1 : QA * Qi = 1 := Subtype.ext (mul_nonsing_inv _ hQd)
  have e2 : QA * X = P := Subtype.ext (nonsing_inv_mul_cancel_right _ _ hXd)
  have e3 : X * Xi = 1 := Subtype.ext (mul_nonsing_inv _ hXd)
  have hτX : τA X = (w + τA cA ^ 3) * (w * τA cA ^ 2 + (cA * τA cA) ^ 2) := by
    simp only [X, hτmul, hτadd, hτpow, hττ, hτw]
  have hτP : τA P = (w * τA cA ^ 3 + (cA * τA cA) ^ 3) * (w + τA cA ^ 2) := by
    simp only [P, hτmul, hτadd, hτpow, hττ, hτw]
  letI : CommRing A := Algebra.adjoinCommRingOfComm E (by simp)
  have htt : cA * Qi * τA (cA * Qi) = 1 :=
    mul_inv_mul_conj_eq_one_of_norm_quotient τA w cA QA Qi X Xi hτmul hτone rfl hτX hτP
      e1 e2 e3
  rw [← hQm]
  have ht : IsUnit (c * (QA.1)⁻¹) := hc.mul ((isUnit_nonsing_inv_iff).mpr hQu)
  have htt' : c * (QA.1)⁻¹ * _root_.GlobalTheory.Tw.adj δ (c * (QA.1)⁻¹) = 1 :=
    congrArg Subtype.val htt
  rw [_root_.GlobalTheory.Tw.Model.adj_eq hδ ht] at htt'
  have hθ := ((_root_.GlobalTheory.Tw.theta_props n E).2.1 _ ht).1
  have hM : IsUnit (δ * _root_.GlobalTheory.Tw.theta (c * (QA.1)⁻¹) * δ⁻¹) :=
    (hδ.mul hθ).mul ((isUnit_nonsing_inv_iff).mpr hδ)
  have hMd := (isUnit_iff_isUnit_det _).mp hM
  have hδd := (isUnit_iff_isUnit_det _).mp hδ
  have heq : c * (QA.1)⁻¹ = δ * _root_.GlobalTheory.Tw.theta (c * (QA.1)⁻¹) * δ⁻¹ := by
    calc c * (QA.1)⁻¹ = c * (QA.1)⁻¹ * (δ * _root_.GlobalTheory.Tw.theta (c * (QA.1)⁻¹) * δ⁻¹)⁻¹ *
          (δ * _root_.GlobalTheory.Tw.theta (c * (QA.1)⁻¹) * δ⁻¹) :=
          (nonsing_inv_mul_cancel_right _ _ hMd).symm
      _ = _ := by rw [htt', one_mul]
  refine ⟨ht, ?_⟩
  show c * (QA.1)⁻¹ * δ = δ * _root_.GlobalTheory.Tw.theta (c * (QA.1)⁻¹)
  rw [heq, nonsing_inv_mul_cancel_right _ _ hδd, ← heq]

open Matrix in
/- English proof (translation)
Introduce `F E _ _ _ _ _ n δ x hδ hδd ⟨u, v, hu, hv, huv⟩ hx hx' hx'd`. Use `haveI := _root_.GlobalTheory.JR.Unram.ultraE F (E := E)`. Establish `hδu` using `_root_.GlobalTheory.TwIntegral.isUnit_of_norm_det hδd`. Establish `hδdu` using `(isUnit_iff_isUnit_det δ).mp hδu`. Take `⟨hθδ, -⟩` from `theta_integral_of_integral_of_norm_det_one F E hδ hδd`.

Establish `hN : _root_.GlobalTheory.Tw.nrm δ = δ * _root_.GlobalTheory.Tw.theta δ` using `rfl`. Establish `hNi : ∀ i j, ‖_root_.GlobalTheory.Tw.nrm δ i j‖ ≤ 1`. Rewrite using `[hN]`. Conclude with `_root_.GlobalTheory.UnitDiscAlg.integ_mul hδ hθδ`. Establish `hsep : (_root_.GlobalTheory.Tw.nrm δ).charpoly.Separable` using `⟨u, v, huv⟩`.

Take `⟨hθx', -⟩` from `theta_integral_of_integral_of_norm_det_one F E hx' hx'd`. Establish `hconj : x⁻¹ * _root_.GlobalTheory.Tw.nrm δ * x = _root_.GlobalTheory.Tw.twConj x δ * _root_.GlobalTheory.Tw.theta (_root_.GlobalTheory.Tw.twConj x δ)`. Unfold `_root_.GlobalTheory.Tw.twConj`. Rewrite using `[hN, _root_.GlobalTheory.Tw.Model.theta_mul, _root_.GlobalTheory.Tw.Model.theta_mul, _root_.GlobalTheory.Tw.Model.theta_theta hx]`. Simplify using `only [mul_assoc]`.

Rewrite using `[← mul_assoc (_root_.GlobalTheory.Tw.theta x), _root_.GlobalTheory.Tw.Model.theta_mul_theta_inv hx, one_mul]`. Establish `hxN : ∀ i j, ‖(x⁻¹ * _root_.GlobalTheory.Tw.nrm δ * x) i j‖ ≤ 1`. Rewrite using `[hconj]`. Conclude with `_root_.GlobalTheory.UnitDiscAlg.integ_mul hx' hθx'`. Take `⟨c, hc, hcN, hk, hkd⟩` from `_root_.GlobalTheory.IntConj.exists_commuting_mul_integral E n _ x hNi ⟨u, v, hu, hv, huv⟩ hx hxN`.

Establish `hcd` using `(isUnit_iff_isUnit_det c).mp hc`. Take `⟨k, rfl⟩ : ∃ k, x = c * k` from `⟨c⁻¹ * x, (mul_nonsing_inv_cancel_left c x hcd).symm⟩`. Rewrite `hk`, `hkd` using `[nonsing_inv_mul_cancel_left _ _ hcd]`. Establish `hkdu` using `(isUnit_iff_isUnit_det k).mp (_root_.GlobalTheory.TwIntegral.isUnit_of_norm_det hkd)`. Take `⟨hθk, hθkd⟩` from `theta_integral_of_integral_of_norm_det_one F E hk hkd`.

Establish `hθkdu` using `(isUnit_iff_isUnit_det _).mp (_root_.GlobalTheory.TwIntegral.isUnit_of_norm_det hθkd)`. Establish `hcA : c ∈ Algebra.adjoin E {_root_.GlobalTheory.Tw.nrm δ}` using `_root_.GlobalTheory.Tw.CentralizerAdjoin.mem_adjoin_of_commute _ c hsep hcN`. Take `⟨haA, -⟩` from `_root_.GlobalTheory.Tw.CentralizerAdjoin.adj_adjoin hδu c hcA`. Establish `hcommN : ∀ g ∈ Algebra.adjoin E {_root_.GlobalTheory.Tw.nrm δ}, g * _root_.GlobalTheory.Tw.nrm δ = _root_.GlobalTheory.Tw.nrm δ * g` using `fun g hg =>`. Use `letI : CommRing (Algebra.adjoin E {_root_.GlobalTheory.Tw.nrm δ}) := Algebra.adjoinCommRingOfComm E (by simp)`.

Use `congrArg Subtype.val (mul_comm (⟨g, hg⟩ : Algebra.adjoin E {_root_.GlobalTheory.Tw.nrm δ}) ⟨_, Algebra.self_mem_adjoin_singleton E _⟩)`. Establish `hsN` using `hcommN _ (Subalgebra.mul_mem _ haA hcA)`. Establish `hs : _root_.GlobalTheory.Tw.adj δ c * c = δ * _root_.GlobalTheory.Tw.theta k * (_root_.GlobalTheory.Tw.twConj (c * k) δ)⁻¹ * k⁻¹`. Rewrite using `[_root_.GlobalTheory.Tw.Model.adj_eq hδu hc]`. Unfold `_root_.GlobalTheory.Tw.twConj`.

Rewrite using `[_root_.GlobalTheory.Tw.Model.theta_mul]`. Establish `hck : IsUnit (c * k).det` using `by rw [det_mul]; exact hcd.mul hkdu`. Simplify using `only [Matrix.mul_inv_rev, nonsing_inv_nonsing_inv _ hδdu, nonsing_inv_nonsing_inv _ hck, nonsing_inv_nonsing_inv _ hcd, nonsing_inv_nonsing_inv _ hkdu, mul_assoc, mul_nonsing_inv_cancel_left _ _ hθkdu, mul_nonsing_inv _ hkdu, mul_one]`. Establish `hsi : ∀ i j, ‖(_root_.GlobalTheory.Tw.adj δ c * c) i j‖ ≤ 1`. Rewrite using `[hs]`.

Conclude with `_root_.GlobalTheory.UnitDiscAlg.integ_mul (_root_.GlobalTheory.UnitDiscAlg.integ_mul (_root_.GlobalTheory.UnitDiscAlg.integ_mul hδ hθk) (_root_.GlobalTheory.TwIntegral.intg_inv hx' hx'd)) (_root_.GlobalTheory.TwIntegral.intg_inv hk hkd)`. Establish `hsd : ‖(_root_.GlobalTheory.Tw.adj δ c * c).det‖ = 1`. Rewrite using `[hs]`. Simplify using `[det_mul, det_nonsing_inv, Ring.inverse_eq_inv', hδd, hθkd, hx'd, hkd]`. Take `⟨ϖ, hϖs, hϖ0, hϖ1, hϖmax⟩` from `exists_star_fixed_uniformizer F E`.

Use `haveI := _root_.GlobalTheory.JR.Unram.lcE F (E := E)`. Take `⟨-, hP3, hP4, -, hQi, hQd⟩` from `_root_.GlobalTheory.UnitDiscAlg.units_quotient E n _ c _ ϖ hNi ⟨u, v, hu, hv, huv⟩ hϖ0 hϖ1 hϖmax hc hcN hsN hsi hsd`. Establish `hQ` using `_root_.GlobalTheory.TwIntegral.isUnit_of_norm_det hQd`. Use `⟨_, mul_inv_quotient_mem_twistedCentralizerGL_lemma_3 δ c ϖ hδu hϖs hsep hc hcN hP3 hP4 hQ, _ * k, _root_.GlobalTheory.UnitDiscAlg.integ_mul hQi hk, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[det_mul, norm_mul, hQd, hkd, one_mul]`.

Rewrite using `[mul_assoc, nonsing_inv_mul_cancel_left _ _ ((isUnit_iff_isUnit_det _).mp hQ)]`.
-/
theorem _root_.GlobalTheory.TwIntegral.integral_twConj_mem_cent_mul : ∀ (F E : Type) [NontriviallyNormedField F]
    [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E]
    [_root_.GlobalTheory.JR.Unram F E] (n : ℕ) (δ x : Matrix (Fin n) (Fin n) E),
    (∀ i j, ‖δ i j‖ ≤ 1) → ‖δ.det‖ = 1 →
    (∃ u v : Polynomial E, (∀ i, ‖u.coeff i‖ ≤ 1) ∧ (∀ i, ‖v.coeff i‖ ≤ 1) ∧
      u * (_root_.GlobalTheory.Tw.nrm δ).charpoly +
        v * Polynomial.derivative (_root_.GlobalTheory.Tw.nrm δ).charpoly = 1) →
    IsUnit x → (∀ i j, ‖_root_.GlobalTheory.Tw.twConj x δ i j‖ ≤ 1) →
    ‖(_root_.GlobalTheory.Tw.twConj x δ).det‖ = 1 →
    ∃ t ∈ _root_.GlobalTheory.Tw.cent δ, ∃ k : Matrix (Fin n) (Fin n) E, (∀ i j, ‖k i j‖ ≤ 1) ∧
      ‖k.det‖ = 1 ∧ x = t * k := by
  intro F E _ _ _ _ _ n δ x hδ hδd ⟨u, v, hu, hv, huv⟩ hx hx' hx'd
  haveI := _root_.GlobalTheory.JR.Unram.ultraE F (E := E)
  have hδu := _root_.GlobalTheory.TwIntegral.isUnit_of_norm_det hδd
  have hδdu := (isUnit_iff_isUnit_det δ).mp hδu
  obtain ⟨hθδ, -⟩ := theta_integral_of_integral_of_norm_det_one F E hδ hδd
  have hN : _root_.GlobalTheory.Tw.nrm δ = δ * _root_.GlobalTheory.Tw.theta δ := rfl
  have hNi : ∀ i j, ‖_root_.GlobalTheory.Tw.nrm δ i j‖ ≤ 1 := by
    rw [hN]; exact _root_.GlobalTheory.UnitDiscAlg.integ_mul hδ hθδ
  have hsep : (_root_.GlobalTheory.Tw.nrm δ).charpoly.Separable := ⟨u, v, huv⟩
  obtain ⟨hθx', -⟩ := theta_integral_of_integral_of_norm_det_one F E hx' hx'd
  have hconj : x⁻¹ * _root_.GlobalTheory.Tw.nrm δ * x =
      _root_.GlobalTheory.Tw.twConj x δ * _root_.GlobalTheory.Tw.theta (_root_.GlobalTheory.Tw.twConj x δ) := by
    unfold _root_.GlobalTheory.Tw.twConj
    rw [hN, _root_.GlobalTheory.Tw.Model.theta_mul, _root_.GlobalTheory.Tw.Model.theta_mul,
      _root_.GlobalTheory.Tw.Model.theta_theta hx]
    simp only [mul_assoc]
    rw [← mul_assoc (_root_.GlobalTheory.Tw.theta x), _root_.GlobalTheory.Tw.Model.theta_mul_theta_inv hx, one_mul]
  have hxN : ∀ i j, ‖(x⁻¹ * _root_.GlobalTheory.Tw.nrm δ * x) i j‖ ≤ 1 := by
    rw [hconj]; exact _root_.GlobalTheory.UnitDiscAlg.integ_mul hx' hθx'
  obtain ⟨c, hc, hcN, hk, hkd⟩ :=
    _root_.GlobalTheory.IntConj.exists_commuting_mul_integral E n _ x hNi ⟨u, v, hu, hv, huv⟩ hx hxN
  have hcd := (isUnit_iff_isUnit_det c).mp hc
  obtain ⟨k, rfl⟩ : ∃ k, x = c * k := ⟨c⁻¹ * x, (mul_nonsing_inv_cancel_left c x hcd).symm⟩
  rw [nonsing_inv_mul_cancel_left _ _ hcd] at hk hkd
  have hkdu := (isUnit_iff_isUnit_det k).mp (_root_.GlobalTheory.TwIntegral.isUnit_of_norm_det hkd)
  obtain ⟨hθk, hθkd⟩ := theta_integral_of_integral_of_norm_det_one F E hk hkd
  have hθkdu := (isUnit_iff_isUnit_det _).mp (_root_.GlobalTheory.TwIntegral.isUnit_of_norm_det hθkd)
  have hcA : c ∈ Algebra.adjoin E {_root_.GlobalTheory.Tw.nrm δ} :=
    _root_.GlobalTheory.Tw.CentralizerAdjoin.mem_adjoin_of_commute _ c hsep hcN
  obtain ⟨haA, -⟩ := _root_.GlobalTheory.Tw.CentralizerAdjoin.adj_adjoin hδu c hcA
  have hcommN : ∀ g ∈ Algebra.adjoin E {_root_.GlobalTheory.Tw.nrm δ},
      g * _root_.GlobalTheory.Tw.nrm δ = _root_.GlobalTheory.Tw.nrm δ * g := fun g hg =>
    letI : CommRing (Algebra.adjoin E {_root_.GlobalTheory.Tw.nrm δ}) :=
      Algebra.adjoinCommRingOfComm E (by simp)
    congrArg Subtype.val (mul_comm (⟨g, hg⟩ : Algebra.adjoin E {_root_.GlobalTheory.Tw.nrm δ})
      ⟨_, Algebra.self_mem_adjoin_singleton E _⟩)
  have hsN := hcommN _ (Subalgebra.mul_mem _ haA hcA)
  have hs : _root_.GlobalTheory.Tw.adj δ c * c =
      δ * _root_.GlobalTheory.Tw.theta k * (_root_.GlobalTheory.Tw.twConj (c * k) δ)⁻¹ * k⁻¹ := by
    rw [_root_.GlobalTheory.Tw.Model.adj_eq hδu hc]
    unfold _root_.GlobalTheory.Tw.twConj
    rw [_root_.GlobalTheory.Tw.Model.theta_mul]
    have hck : IsUnit (c * k).det := by rw [det_mul]; exact hcd.mul hkdu
    simp only [Matrix.mul_inv_rev, nonsing_inv_nonsing_inv _ hδdu, nonsing_inv_nonsing_inv _ hck,
      nonsing_inv_nonsing_inv _ hcd, nonsing_inv_nonsing_inv _ hkdu, mul_assoc,
      mul_nonsing_inv_cancel_left _ _ hθkdu, mul_nonsing_inv _ hkdu, mul_one]
  have hsi : ∀ i j, ‖(_root_.GlobalTheory.Tw.adj δ c * c) i j‖ ≤ 1 := by
    rw [hs]
    exact _root_.GlobalTheory.UnitDiscAlg.integ_mul (_root_.GlobalTheory.UnitDiscAlg.integ_mul
      (_root_.GlobalTheory.UnitDiscAlg.integ_mul hδ hθk) (_root_.GlobalTheory.TwIntegral.intg_inv hx' hx'd))
      (_root_.GlobalTheory.TwIntegral.intg_inv hk hkd)
  have hsd : ‖(_root_.GlobalTheory.Tw.adj δ c * c).det‖ = 1 := by
    rw [hs]
    simp [det_mul, det_nonsing_inv, Ring.inverse_eq_inv', hδd, hθkd, hx'd, hkd]
  obtain ⟨ϖ, hϖs, hϖ0, hϖ1, hϖmax⟩ := exists_star_fixed_uniformizer F E
  haveI := _root_.GlobalTheory.JR.Unram.lcE F (E := E)
  obtain ⟨-, hP3, hP4, -, hQi, hQd⟩ := _root_.GlobalTheory.UnitDiscAlg.units_quotient E n _ c _ ϖ hNi
    ⟨u, v, hu, hv, huv⟩ hϖ0 hϖ1 hϖmax hc hcN hsN hsi hsd
  have hQ := _root_.GlobalTheory.TwIntegral.isUnit_of_norm_det hQd
  refine ⟨_, mul_inv_quotient_mem_twistedCentralizerGL_lemma_3 δ c ϖ hδu hϖs hsep hc hcN hP3 hP4 hQ,
    _ * k, _root_.GlobalTheory.UnitDiscAlg.integ_mul hQi hk, ?_, ?_⟩
  · rw [det_mul, norm_mul, hQd, hkd, one_mul]
  · rw [mul_assoc, nonsing_inv_mul_cancel_left _ _ ((isUnit_iff_isUnit_det _).mp hQ)]

end GlobalTheory.TwIntegral

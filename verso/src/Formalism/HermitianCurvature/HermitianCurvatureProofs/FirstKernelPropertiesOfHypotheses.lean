import Formalism.HermitianCurvature.BlockKernelPropertiesOfSteps
import Formalism.DoubleCosetMeasures.LowerUnipotentOrbits.MulInvBlockDiagApplySameBlock
import Formalism.DoubleCosetMeasures.LowerUnipotentOrbits.LowUniMulVecELast

set_option maxHeartbeats 400000

noncomputable section

open Formalism.DoubleCosetMeasures Formalism.FourierDecayAlt.A5 Matrix
open scoped ComplexConjugate

namespace Formalism.FourierDecayAlt.P

namespace A5x6

/- English proof (translation)
The claim follows from `Matrix.isUnit_det_of_right_inverse (Formalism.DoubleCosetMeasures.P.Phase.pt_mul_ptI h.1 h.2)`.
-/
theorem pt_det_isUnit {K : Type} [CommRing K] (h : Point K) : IsUnit (pt h.1 h.2).det :=
  Matrix.isUnit_det_of_right_inverse (Formalism.DoubleCosetMeasures.P.Phase.pt_mul_ptI h.1 h.2)

/- English proof (translation)
Unfold `IsPSD`. Introduce `a`. Establish `e : ∑ x ∈ F, ∑ y ∈ F, a x * conj (a y) * k x y = 0` using `Finset.sum_eq_zero fun x hx => Finset.sum_eq_zero fun y hy => by rw [h x hx y hy, mul_zero]`. Rewrite using `[e]`. Simplify using the standard rewrite rules.
-/
theorem isPSD_zero {X : Type} (F : Finset X) (k : X → X → ℂ)
    (h : ∀ x ∈ F, ∀ y ∈ F, k x y = 0) : IsPSD F k := by
  unfold IsPSD
  intro a
  have e : ∑ x ∈ F, ∑ y ∈ F, a x * conj (a y) * k x y = 0 :=
    Finset.sum_eq_zero fun x hx => Finset.sum_eq_zero fun y hy => by rw [h x hx y hy, mul_zero]
  rw [e]
  simp

/- English proof (translation)
Unfold `mulR`. Use extensionality with `z`. Simplify using `only [AddSubgroup.mem_map, AddMonoidHom.coe_mulLeft, Subring.mem_toAddSubgroup]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨y, hy, rfl⟩`.

Conclude with `R.mul_mem hd hy`. Introduce `hz`. Conclude with `⟨e * z, R.mul_mem he hz, by rw [← mul_assoc, hde, one_mul]⟩`.
-/
theorem mulR_eq {K : Type} [CommRing K] (R : Subring K) (d e : K) (hd : d ∈ R) (he : e ∈ R)
    (hde : d * e = 1) : mulR R d = R.toAddSubgroup := by
  unfold mulR
  ext z
  simp only [AddSubgroup.mem_map, AddMonoidHom.coe_mulLeft, Subring.mem_toAddSubgroup]
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact R.mul_mem hd hy
  · intro hz
    exact ⟨e * z, R.mul_mem he hz, by rw [← mul_assoc, hde, one_mul]⟩

/- English proof (translation)
Unfold `modK`. Rewrite using `[mulR_eq R d e hd he hde]`. Simplify using `[AddSubgroup.relIndex_self]`.
-/
theorem modK_eq_one {K : Type} [CommRing K] (R : Subring K) (d e : K) (hd : d ∈ R) (he : e ∈ R)
    (hde : d * e = 1) : modK R d = 1 := by
  unfold modK
  rw [mulR_eq R d e hd he hde]
  simp [AddSubgroup.relIndex_self]

/- English proof (translation)
Rewrite using `[Matrix.det_apply]`. Use `R.sum_mem fun σ _ => ?_` and prove the remaining obligations. Rewrite using `[Units.smul_def, zsmul_eq_mul]`. Conclude with `R.mul_mem (intCast_mem R _) (R.prod_mem fun i _ => hM _ _)`.
-/
theorem det_mem {K : Type} [CommRing K] (R : Subring K) {n : ℕ} (M : Matrix (Fin n) (Fin n) K)
    (hM : IsInt R M) : M.det ∈ R := by
  rw [Matrix.det_apply]
  refine R.sum_mem fun σ _ => ?_
  rw [Units.smul_def, zsmul_eq_mul]
  exact R.mul_mem (intCast_mem R _) (R.prod_mem fun i _ => hM _ _)

/- English proof (translation)
Take `⟨h1, h2⟩` from `hh`. Use `⟨det_mem R _ h1, det_mem R _ h2, ?_⟩` and prove the remaining obligations. Rewrite using `[Matrix.det_nonsing_inv, Ring.mul_inverse_cancel _ (pt_det_isUnit h)]`.
-/
theorem glr_det {K : Type} [CommRing K] (R : Subring K) (h : Point K) (hh : InGLR R h) :
    (pt h.1 h.2).det ∈ R ∧ (pt h.1 h.2)⁻¹.det ∈ R ∧ (pt h.1 h.2).det * (pt h.1 h.2)⁻¹.det = 1 := by
  obtain ⟨h1, h2⟩ := hh
  refine ⟨det_mem R _ h1, det_mem R _ h2, ?_⟩
  rw [Matrix.det_nonsing_inv, Ring.mul_inverse_cancel _ (pt_det_isUnit h)]

/- English proof (translation)
Take `⟨h1, h2, h3⟩` from `glr_det R h hh`. Unfold `cSize`. Rewrite using `[modK_eq_one R _ _ h1 h2 h3]`. Simplify using the standard rewrite rules.
-/
theorem cSize_glr {K : Type} [CommRing K] (R : Subring K) (h : Point K) (hh : InGLR R h) :
    cSize R h = 1 := by
  obtain ⟨h1, h2, h3⟩ := glr_det R h hh
  unfold cSize
  rw [modK_eq_one R _ _ h1 h2 h3]
  simp

/- English proof (translation)
Introduce `K _ _ _ R ψ hL m`. Establish `hrep : ∀ x : K ⧸ R.toAddSubgroup, ∃ u : Kˣ, ((u : K) : K ⧸ R.toAddSubgroup) = x`. Introduce `x`. Take `⟨r, hr, hu⟩` from `hL.unitRep (Quotient.out x)`. Use `⟨hu.unit, ?_⟩` and prove the remaining obligations.

Rewrite using `[IsUnit.unit_spec, QuotientAddGroup.mk_add, (QuotientAddGroup.eq_zero_iff r).mpr hr, add_zero]`. Conclude with `QuotientAddGroup.out_eq' x`. Use `choose cr hcr using hrep`. Establish `hcrsub : ∀ x : K, ((cr (x : K ⧸ R.toAddSubgroup) : Kˣ) : K) - x ∈ R`. Introduce `x`.

Establish `h1` using `QuotientAddGroup.eq.mp (hcr (x : K ⧸ R.toAddSubgroup))`. Establish `h2` using `R.toAddSubgroup.neg_mem h1`. Establish `e : -(-((cr (x : K ⧸ R.toAddSubgroup) : Kˣ) : K) + x) = ((cr (x : K ⧸ R.toAddSubgroup) : Kˣ) : K) - x` using `by ring`. Rewrite `h2` using `[e]`. Conclude with `h2`.

Set `Θ : K → Point K → Point K → ℂ` to `fun x h h' => Ns R ψ 1 h h' (cr (x : K ⧸ R.toAddSubgroup)) (cr (x : K ⧸ R.toAddSubgroup))`. Establish `hΘt : ∀ (t : Kˣ) (h h' : Point K), h.1.sum = h'.1.sum → Θ (t : K) h h' = Ns R ψ 1 h h' t t` using `fun t h h' e => hPer K R ψ hL h h' _ _ e (hcrsub t)`. Establish `hsum : ∀ h h' : Point K, h.1.sum = h'.1.sum → ∑ᶠ x : K ⧸ R.toAddSubgroup, Θ (Quotient.out x) h h' = ((cSize R h * cSize R h' : ℝ) : ℂ) * N0 R ψ h h'`. Introduce `h h' e`. Rewrite using `[← (hPars K R ψ hL h h' e cr hcr).2]`.

Apply `finsum_congr` to reduce the goal to its premises. Introduce `x`. Simplify using `only [Θ]`. Rewrite using `[QuotientAddGroup.out_eq']`. Establish `hglr : ∀ h h' : Point K, InGLR R h → ∀ y : K ⧸ R.toAddSubgroup, Ns R ψ 1 h h' (cr y) (cr y) ≠ 0 → y = 0`.

Introduce `h h' hh y h0`. Take `⟨h1, h2, h3⟩` from `glr_det R h hh`. Establish `h4` using `(hSup K R ψ 1 le_rfl h h' _ _ h0).1`. Establish `h5 : ((cr y : Kˣ) : K) ∈ R`. Use `R.mul_mem h2 h4` as an intermediate fact.

Rewrite `this` using `[← mul_assoc, mul_comm _ (pt h.1 h.2).det, h3, one_mul]`. Then use the resulting hypothesis. Rewrite using `[← hcr y]`. Conclude with `(QuotientAddGroup.eq_zero_iff _).mpr h5`. Use `⟨Θ, fun t h h' e e' => hΘt t h h' (e.trans e'.symm), fun h h' e e' => hsum h h' (e.trans e'.symm), fun F hF => ?_⟩` and prove the remaining obligations. Establish `hFF : ∀ h ∈ F, ∀ h' ∈ F, h.1.sum = h'.1.sum` using `fun h hh h' hh' => (hF h hh).trans (hF h' hh').symm`.

Use `⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `x r hr`. Establish `: ((x + r : K) : K ⧸ R.toAddSubgroup) = (x : K ⧸ R.toAddSubgroup)`. Rewrite using `[QuotientAddGroup.mk_add, (QuotientAddGroup.eq_zero_iff r).mpr hr, add_zero]`. Use function extensionality and compare the values at `h h'`.

Simplify using `only [Θ]`. Rewrite using `[this]`. Introduce `x`. Conclude with `hGram K R ψ hL m F hF (cr x)`. Take `⟨ϖ, hϖ, hϖx⟩` from `hL.unif choose M hM using fun h : Point K => hϖx (((pt_det_isUnit h).unit⁻¹ : Kˣ) : K)`.

Set `N` to `F.sup M`. Set `L : Submodule R K` to `{ carrier := {x | (ϖ : K) ^ N * x ∈ R} add_mem' := by`. Introduce `a b ha hb`. Simplify using `only [Set.mem_ofPred_eq] at ha hb ⊢`. Rewrite using `[mul_add]`.

Conclude with `R.add_mem ha hb`. Use the proof step `zero_mem' := by simp [R.zero_mem]`. Use the proof step `smul_mem' := by`. Introduce `c x hx`. Simplify using `only [Set.mem_ofPred_eq] at hx ⊢`.

Rewrite using `[Subring.smul_def, smul_eq_mul, mul_left_comm]`. Conclude with `R.mul_mem c.2 hx }`. Use `⟨L, ?_, ?_, ?_⟩` and prove the remaining obligations. Conclude with `hL.isOpen.preimage (continuous_const_mul ((ϖ : K) ^ N))`. Establish `: (L : Set K) = (fun x => ((ϖ⁻¹ : Kˣ) : K) ^ N * x) '' (R : Set K)`.

Use extensionality with `x`. Prove the components needed by the constructor for the conclusion. Introduce `hx`. Use `⟨(ϖ : K) ^ N * x, hx, ?_⟩` and prove the remaining obligations. Simplify using `only`.

Rewrite using `[← mul_assoc, ← mul_pow, Units.inv_mul, one_pow, one_mul]`. Introduce and unpack `⟨y, hy, rfl⟩ show (ϖ : K) ^ N * (((ϖ⁻¹ : Kˣ) : K) ^ N * y) ∈ R`. Rewrite using `[← mul_assoc, ← mul_pow, Units.mul_inv, one_pow, one_mul]`. Conclude with `hy`. Rewrite using `[this]`.

Conclude with `hL.isCompact.image (continuous_const_mul _)`. Introduce `x hx h hh h' _`. Assume the negation of the conclusion as `h0`. Apply `hx` to reduce the goal to its premises. Establish `h4` using `(hSup K R ψ 1 le_rfl h h' _ _ h0).1`.

Establish `hle : M h ≤ N` using `Finset.le_sup (f := M) hh`. Use `show (ϖ : K) ^ N * x ∈ R`. Establish `hpN : (ϖ : K) ^ N ∈ R` using `R.pow_mem hϖ N`. Establish `e1 : (ϖ : K) ^ N * x = (ϖ : K) ^ (N - M h) * (((ϖ : K) ^ M h * (((pt_det_isUnit h).unit⁻¹ : Kˣ) : K)) * ((pt h.1 h.2).det * ((cr (x : K ⧸ R.toAddSubgroup) : Kˣ) : K))) - (ϖ : K) ^ N * (((cr (x : K ⧸ R.toAddSubgroup) : Kˣ) : K) - x)`. Establish `e2 : (((pt_det_isUnit h).unit⁻¹ : Kˣ) : K) * (pt h.1 h.2).det = 1` using `IsUnit.val_inv_mul (pt_det_isUnit h)`.

Establish `e3 : (ϖ : K) ^ N = (ϖ : K) ^ (N - M h) * (ϖ : K) ^ M h`. Rewrite using `[← pow_add, Nat.sub_add_cancel hle]`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[e2]`. Expand and normalize the polynomial expressions, which then agree.

Use `_ = _ := by rw [e3]; ring`. Rewrite using `[e1]`. Conclude with `R.sub_mem (R.mul_mem (R.pow_mem hϖ _) (R.mul_mem (hM h) h4)) (R.mul_mem hpN (hcrsub x))`. Introduce `t`. Apply `isPSD_zero` to reduce the goal to its premises.

Introduce `h hh h' hh'`. Rewrite using `[hΘt t h h' (hFF h hh h' hh'), sub_self]`. Apply `isPSD_zero` to reduce the goal to its premises. Introduce `h hh h' hh'`. Rewrite using `[hsum h h' (hFF h hh h' hh'), pow_one, pow_one, sub_self]`.

Introduce `x h hh h' hh' hne`. Assume the negation of the conclusion as `h0`. Conclude with `hne ((hBD K R ψ hL h h' (hFF h hh h' hh')).2 1 _ h0)`. Introduce `hGL x`. Apply `isPSD_zero` to reduce the goal to its premises.

Introduce `h hh h' hh'`. Distinguish the cases in `hx : x ∈ R`. Rewrite using `[if_pos hx]`. Establish `P` using `(hPars K R ψ hL h h' (hFF h hh h' hh') cr hcr).2`. Rewrite using `[finsum_eq_single _ (0 : K ⧸ R.toAddSubgroup) (fun y hy => by`.

Assume the negation of the conclusion as `h0`. Conclude with `hy (hglr h h' (hGL h hh) y h0)),`. Use `cSize_glr R h (hGL h hh), cSize_glr R h' (hGL h' hh')] at P`. Establish `hx0 : (x : K ⧸ R.toAddSubgroup) = 0` using `(QuotientAddGroup.eq_zero_iff _).mpr hx`. Simplify using `only [Θ]`.

Rewrite using `[hx0, P]`. Simplify using the standard rewrite rules. Rewrite using `[if_neg hx, zero_sub, neg_eq_zero]`. Assume the negation of the conclusion as `h0`. Conclude with `hx ((QuotientAddGroup.eq_zero_iff _).mp (hglr h h' (hGL h hh) _ h0))`.
-/
theorem first_theta_equality_of_kernel_facts (hPer : SingleBlockPeriodic) (hGram : SingleBlockPosSemidef) (hPars : SingleBlockParseval) (hSup : NsSupport)
    (hBD : NsBlockDiag) : SingleBlockThetaProps := by
  intro K _ _ _ R ψ hL m
  classical
  have hrep : ∀ x : K ⧸ R.toAddSubgroup, ∃ u : Kˣ, ((u : K) : K ⧸ R.toAddSubgroup) = x := by
    intro x
    obtain ⟨r, hr, hu⟩ := hL.unitRep (Quotient.out x)
    refine ⟨hu.unit, ?_⟩
    rw [IsUnit.unit_spec, QuotientAddGroup.mk_add, (QuotientAddGroup.eq_zero_iff r).mpr hr,
      add_zero]
    exact QuotientAddGroup.out_eq' x
  choose cr hcr using hrep
  have hcrsub : ∀ x : K, ((cr (x : K ⧸ R.toAddSubgroup) : Kˣ) : K) - x ∈ R := by
    intro x
    have h1 := QuotientAddGroup.eq.mp (hcr (x : K ⧸ R.toAddSubgroup))
    have h2 := R.toAddSubgroup.neg_mem h1
    have e : -(-((cr (x : K ⧸ R.toAddSubgroup) : Kˣ) : K) + x) =
      ((cr (x : K ⧸ R.toAddSubgroup) : Kˣ) : K) - x := by ring
    rw [e] at h2; exact h2
  let Θ : K → Point K → Point K → ℂ := fun x h h' =>
    Ns R ψ 1 h h' (cr (x : K ⧸ R.toAddSubgroup)) (cr (x : K ⧸ R.toAddSubgroup))
  have hΘt : ∀ (t : Kˣ) (h h' : Point K), h.1.sum = h'.1.sum →
      Θ (t : K) h h' = Ns R ψ 1 h h' t t :=
    fun t h h' e => hPer K R ψ hL h h' _ _ e (hcrsub t)
  have hsum : ∀ h h' : Point K, h.1.sum = h'.1.sum →
      ∑ᶠ x : K ⧸ R.toAddSubgroup, Θ (Quotient.out x) h h' =
        ((cSize R h * cSize R h' : ℝ) : ℂ) * N0 R ψ h h' := by
    intro h h' e
    rw [← (hPars K R ψ hL h h' e cr hcr).2]
    apply finsum_congr
    intro x
    simp only [Θ]
    rw [QuotientAddGroup.out_eq']
  have hglr : ∀ h h' : Point K, InGLR R h → ∀ y : K ⧸ R.toAddSubgroup,
      Ns R ψ 1 h h' (cr y) (cr y) ≠ 0 → y = 0 := by
    intro h h' hh y h0
    obtain ⟨h1, h2, h3⟩ := glr_det R h hh
    have h4 := (hSup K R ψ 1 le_rfl h h' _ _ h0).1
    have h5 : ((cr y : Kˣ) : K) ∈ R := by
      have := R.mul_mem h2 h4
      rwa [← mul_assoc, mul_comm _ (pt h.1 h.2).det, h3, one_mul] at this
    rw [← hcr y]
    exact (QuotientAddGroup.eq_zero_iff _).mpr h5
  refine ⟨Θ, fun t h h' e e' => hΘt t h h' (e.trans e'.symm),
    fun h h' e e' => hsum h h' (e.trans e'.symm), fun F hF => ?_⟩
  have hFF : ∀ h ∈ F, ∀ h' ∈ F, h.1.sum = h'.1.sum := fun h hh h' hh' =>
    (hF h hh).trans (hF h' hh').symm
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro x r hr
    have : ((x + r : K) : K ⧸ R.toAddSubgroup) = (x : K ⧸ R.toAddSubgroup) := by
      rw [QuotientAddGroup.mk_add, (QuotientAddGroup.eq_zero_iff r).mpr hr, add_zero]
    funext h h'
    simp only [Θ]
    rw [this]
  · intro x
    exact hGram K R ψ hL m F hF (cr x)
  · obtain ⟨ϖ, hϖ, hϖx⟩ := hL.unif
    choose M hM using fun h : Point K => hϖx (((pt_det_isUnit h).unit⁻¹ : Kˣ) : K)
    let N := F.sup M
    let L : Submodule R K :=
      { carrier := {x | (ϖ : K) ^ N * x ∈ R}
        add_mem' := by
          intro a b ha hb
          simp only [Set.mem_ofPred_eq] at ha hb ⊢
          rw [mul_add]; exact R.add_mem ha hb
        zero_mem' := by simp [R.zero_mem]
        smul_mem' := by
          intro c x hx
          simp only [Set.mem_ofPred_eq] at hx ⊢
          rw [Subring.smul_def, smul_eq_mul, mul_left_comm]
          exact R.mul_mem c.2 hx }
    refine ⟨L, ?_, ?_, ?_⟩
    · exact hL.isOpen.preimage (continuous_const_mul ((ϖ : K) ^ N))
    · have : (L : Set K) = (fun x => ((ϖ⁻¹ : Kˣ) : K) ^ N * x) '' (R : Set K) := by
        ext x
        constructor
        · intro hx
          refine ⟨(ϖ : K) ^ N * x, hx, ?_⟩
          simp only
          rw [← mul_assoc, ← mul_pow, Units.inv_mul, one_pow, one_mul]
        · rintro ⟨y, hy, rfl⟩
          show (ϖ : K) ^ N * (((ϖ⁻¹ : Kˣ) : K) ^ N * y) ∈ R
          rw [← mul_assoc, ← mul_pow, Units.mul_inv, one_pow, one_mul]
          exact hy
      rw [this]
      exact hL.isCompact.image (continuous_const_mul _)
    · intro x hx h hh h' _
      by_contra h0
      apply hx
      have h4 := (hSup K R ψ 1 le_rfl h h' _ _ h0).1
      have hle : M h ≤ N := Finset.le_sup (f := M) hh
      show (ϖ : K) ^ N * x ∈ R
      have hpN : (ϖ : K) ^ N ∈ R := R.pow_mem hϖ N
      have e1 : (ϖ : K) ^ N * x = (ϖ : K) ^ (N - M h) *
          (((ϖ : K) ^ M h * (((pt_det_isUnit h).unit⁻¹ : Kˣ) : K)) *
            ((pt h.1 h.2).det * ((cr (x : K ⧸ R.toAddSubgroup) : Kˣ) : K))) -
          (ϖ : K) ^ N * (((cr (x : K ⧸ R.toAddSubgroup) : Kˣ) : K) - x) := by
        have e2 : (((pt_det_isUnit h).unit⁻¹ : Kˣ) : K) * (pt h.1 h.2).det = 1 :=
          IsUnit.val_inv_mul (pt_det_isUnit h)
        have e3 : (ϖ : K) ^ N = (ϖ : K) ^ (N - M h) * (ϖ : K) ^ M h := by
          rw [← pow_add, Nat.sub_add_cancel hle]
        calc (ϖ : K) ^ N * x = (ϖ : K) ^ N * ((((pt_det_isUnit h).unit⁻¹ : Kˣ) : K) *
              (pt h.1 h.2).det) * ((cr (x : K ⧸ R.toAddSubgroup) : Kˣ) : K) -
              (ϖ : K) ^ N * (((cr (x : K ⧸ R.toAddSubgroup) : Kˣ) : K) - x) := by
                rw [e2]; ring
          _ = _ := by rw [e3]; ring
      rw [e1]
      exact R.sub_mem (R.mul_mem (R.pow_mem hϖ _) (R.mul_mem (hM h) h4))
        (R.mul_mem hpN (hcrsub x))
  · intro t
    apply isPSD_zero
    intro h hh h' hh'
    rw [hΘt t h h' (hFF h hh h' hh'), sub_self]
  · apply isPSD_zero
    intro h hh h' hh'
    rw [hsum h h' (hFF h hh h' hh'), pow_one, pow_one, sub_self]
  · intro x h hh h' hh' hne
    by_contra h0
    exact hne ((hBD K R ψ hL h h' (hFF h hh h' hh')).2 1 _ h0)
  · intro hGL x
    apply isPSD_zero
    intro h hh h' hh'
    by_cases hx : x ∈ R
    · rw [if_pos hx]
      have P := (hPars K R ψ hL h h' (hFF h hh h' hh') cr hcr).2
      rw [finsum_eq_single _ (0 : K ⧸ R.toAddSubgroup) (fun y hy => by
        by_contra h0; exact hy (hglr h h' (hGL h hh) y h0)),
        cSize_glr R h (hGL h hh), cSize_glr R h' (hGL h' hh')] at P
      have hx0 : (x : K ⧸ R.toAddSubgroup) = 0 := (QuotientAddGroup.eq_zero_iff _).mpr hx
      simp only [Θ]
      rw [hx0, P]
      simp
    · rw [if_neg hx, zero_sub, neg_eq_zero]
      by_contra h0
      exact hx ((QuotientAddGroup.eq_zero_iff _).mp (hglr h h' (hGL h hh) _ h0))

/- English proof (translation)
Unfold `Th1Eq`. Unfold `SingleBlockThetaProps at h`. Introduce `K _ _ _ R ψ hLD m`. Take `⟨Θ, h1, h2, h3⟩` from `h K R ψ hLD m`. Take `⟨hp, -⟩` from `h3 ∅ (by simp)`.

Conclude with `⟨Θ, hp, h1, h2⟩`.
-/
theorem first_theta_eq_of_equality (h : SingleBlockThetaProps) : Th1Eq := by
  unfold Th1Eq
  unfold SingleBlockThetaProps at h
  intro K _ _ _ R ψ hLD m
  obtain ⟨Θ, h1, h2, h3⟩ := h K R ψ hLD m
  obtain ⟨hp, -⟩ := h3 ∅ (by simp)
  exact ⟨Θ, hp, h1, h2⟩

/- English proof (translation)
Unfold `A13 ThetaExists`. Unfold `SingleBlockThetaProps at h`. Introduce `K _ _ _ R ψ hLD _ m F hF`. Take `⟨Θ, -, -, h3⟩` from `h K R ψ hLD m`. Conclude with `⟨Θ, h3 F hF⟩`.
-/
theorem first_level_of_equality (h : SingleBlockThetaProps) : A13 1 := by
  unfold A13 ThetaExists
  unfold SingleBlockThetaProps at h
  intro K _ _ _ R ψ hLD _ m F hF
  obtain ⟨Θ, -, -, h3⟩ := h K R ψ hLD m
  exact ⟨Θ, h3 F hF⟩

section KRfacts

variable {K : Type} [CommRing K] (R : Subring K)

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `h`. Take `⟨r, rfl⟩` from `LinearMap.mem_range.mp h`. Conclude with `r.2`. Introduce `ha`.

Conclude with `LinearMap.mem_range.mpr ⟨⟨a, ha⟩, rfl⟩`.
-/
theorem mem_rangeR (a : K) : a ∈ LinearMap.range (Algebra.linearMap R K) ↔ a ∈ R := by
  constructor
  · intro h
    obtain ⟨r, rfl⟩ := LinearMap.mem_range.mp h
    exact r.2
  · intro ha
    exact LinearMap.mem_range.mpr ⟨⟨a, ha⟩, rfl⟩

/- English proof (translation)
Unfold `psiKR`. Use `set b := Quotient.out (Submodule.Quotient.mk a : KR R) with hb`. Establish `h1 : b - a ∈ R`. Rewrite using `[← mem_rangeR R, ← Submodule.Quotient.eq]`. Conclude with `Quotient.out_eq _`.

Combine the equalities or inequalities in the displayed calculation.
-/
theorem psiKR_mk (ψ : AddChar K ℂ) (hψ : ∀ r ∈ R, ψ r = 1) (a : K) :
    psiKR R ψ (Submodule.Quotient.mk a : KR R) = ψ a := by
  unfold psiKR
  set b := Quotient.out (Submodule.Quotient.mk a : KR R) with hb
  have h1 : b - a ∈ R := by
    rw [← mem_rangeR R, ← Submodule.Quotient.eq]
    exact Quotient.out_eq _
  calc ψ b = ψ (a + (b - a)) := by congr 1; abel
    _ = ψ a := by rw [AddChar.map_add_eq_mul, hψ _ h1, mul_one]

/- English proof (translation)
Take `⟨a, rfl⟩` from `Submodule.Quotient.mk_surjective _ x`. Take `⟨b, rfl⟩` from `Submodule.Quotient.mk_surjective _ y`. Rewrite using `[← Submodule.Quotient.mk_add, psiKR_mk R ψ hψ, psiKR_mk R ψ hψ, psiKR_mk R ψ hψ, AddChar.map_add_eq_mul]`.
-/
theorem psiKR_add (ψ : AddChar K ℂ) (hψ : ∀ r ∈ R, ψ r = 1) (x y : KR R) :
    psiKR R ψ (x + y) = psiKR R ψ x * psiKR R ψ y := by
  obtain ⟨a, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  obtain ⟨b, rfl⟩ := Submodule.Quotient.mk_surjective _ y
  rw [← Submodule.Quotient.mk_add, psiKR_mk R ψ hψ, psiKR_mk R ψ hψ, psiKR_mk R ψ hψ,
    AddChar.map_add_eq_mul]

/- English proof (translation)
Introduce `v hv`. Take `⟨w, hw⟩` from `LinearMap.mem_range.mp (Submodule.mem_comap.mp hv)`. Rewrite using `[LinearMap.mem_ker]`. Simplify using `only [lamLin, LinearMap.comp_apply, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]`. Rewrite using `[← hw]`.

Simplify using `only [LinearMap.comp_apply, LinearMap.restrictScalars_apply, Matrix.mulVecLin_apply, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hZ, Matrix.one_mulVec]`. Rewrite using `[mem_rangeR]`. Unfold `lastCoord`. Rewrite using `[LinearMap.sum_apply]`. Use `R.sum_mem fun j _ => ?_` and prove the remaining obligations.

Use `split_ifs`. Simplify using `[coeLin]`. Conclude with `(w j).2`. Simplify using the standard rewrite rules.
-/
theorem latZ_le_ker {n : ℕ} (Z : Matrix (Fin n) (Fin n) K) (hZ : IsUnit Z.det) :
    latZ R Z ≤ LinearMap.ker (lamLin R Z) := by
  intro v hv
  obtain ⟨w, hw⟩ := LinearMap.mem_range.mp (Submodule.mem_comap.mp hv)
  rw [LinearMap.mem_ker]
  simp only [lamLin, LinearMap.comp_apply, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
  rw [← hw]
  simp only [LinearMap.comp_apply, LinearMap.restrictScalars_apply, Matrix.mulVecLin_apply,
    Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hZ, Matrix.one_mulVec]
  rw [mem_rangeR]
  unfold lastCoord
  rw [LinearMap.sum_apply]
  refine R.sum_mem fun j _ => ?_
  split_ifs
  · simp [coeLin]
    exact (w j).2
  · simp

def muZ {n : ℕ} (Z : Matrix (Fin n) (Fin n) K) (hZ : IsUnit Z.det) : coker R Z →ₗ[R] KR R :=
  (latZ R Z).liftQ (lamLin R Z) (latZ_le_ker R Z hZ)

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem muZ_mk {n : ℕ} (Z : Matrix (Fin n) (Fin n) K) (hZ : IsUnit Z.det) (v : Fin n → R) :
    muZ R Z hZ (Submodule.Quotient.mk v) = lamLin R Z v := rfl

/- English proof (translation)
Rewrite using `[← muZ_mk R Z hZ (Quotient.out β)]`. Use `congr 1`. Conclude with `Quotient.out_eq β`.
-/
theorem lamLin_out {n : ℕ} (Z : Matrix (Fin n) (Fin n) K) (hZ : IsUnit Z.det) (β : coker R Z) :
    lamLin R Z (Quotient.out β) = muZ R Z hZ β := by
  rw [← muZ_mk R Z hZ (Quotient.out β)]
  congr 1
  exact Quotient.out_eq β

/- English proof (translation)
Rewrite using `[sub_eq_zero, sub_eq_zero, LinearEquiv.eq_symm_apply]`. Simplify using `only [isoZZ, Set.mem_setOf_eq]`. Use `and_congr Iff.rfl ⟨fun h => ?_, fun h v v' hv => ?_⟩` and prove the remaining obligations. Use `LinearMap.ext fun β => ?_` and prove the remaining obligations. Take `⟨v, rfl⟩` from `Submodule.Quotient.mk_surjective _ β`.

Simplify using `only [LinearMap.comp_apply, LinearEquiv.coe_coe, muZ_mk]`. Rewrite using `[← lamLin_out R Z' hZ']`. Conclude with `(h v _ (Quotient.out_eq _).symm).symm`. Rewrite using `[← muZ_mk R Z' hZ' v', ← hv, ← muZ_mk R Z hZ v, h]`. Both sides reduce to the same expression.
-/
theorem mem_isoZZ_iff {n n' : ℕ} (Z : Matrix (Fin n) (Fin n) K) (Z' : Matrix (Fin n') (Fin n') K)
    (hZ : IsUnit Z.det) (hZ' : IsUnit Z'.det) (θ : coker R Z ≃ₗ[R] coker R Z') :
    θ ∈ isoZZ R Z Z' ↔ eZ R Z - θ.symm (eZ R Z') = 0 ∧
      muZ R Z hZ - (muZ R Z' hZ').comp θ.toLinearMap = 0 := by
  rw [sub_eq_zero, sub_eq_zero, LinearEquiv.eq_symm_apply]
  simp only [isoZZ, Set.mem_setOf_eq]
  refine and_congr Iff.rfl ⟨fun h => ?_, fun h v v' hv => ?_⟩
  · refine LinearMap.ext fun β => ?_
    obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective _ β
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, muZ_mk]
    rw [← lamLin_out R Z' hZ']
    exact (h v _ (Quotient.out_eq _).symm).symm
  · rw [← muZ_mk R Z' hZ' v', ← hv, ← muZ_mk R Z hZ v, h]
    rfl

end KRfacts

/- English proof (translation)
Establish `hfin : ∀ τ : T, (Function.support fun x => if g τ = -κ x then f τ else 0).Finite`. Introduce `τ`. Apply `Set.Subsingleton.finite` to reduce the goal to its premises. Introduce `x hx y hy`. Simplify using `only [Function.mem_support, ne_eq, ite_eq_right_iff, Classical.not_imp] at hx hy`.

Apply `hκ.1` to reduce the goal to its premises. Rewrite using `[← neg_inj, ← hx.1, ← hy.1]`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Use `(Set.finite_iUnion hfin).subset ?_` and prove the remaining obligations. Introduce `x hx`.

Simplify using `only [Function.mem_support, ne_eq] at hx`. Assume the negation of the conclusion as `hcon`. Apply `hx` to reduce the goal to its premises. Apply `Finset.sum_eq_zero` to reduce the goal to its premises. Introduce `τ _`.

Assume the negation of the conclusion as `h0`. Conclude with `hcon (Set.mem_iUnion.mpr ⟨τ, h0⟩)`. Rewrite using `[finsum_sum_comm _ _ (fun τ _ => hfin τ)]`. Apply `Finset.sum_congr rfl` to reduce the goal to its premises. Introduce `τ _`.

Take `⟨x0, hx0⟩` from `hκ.2 (-g τ)`. Rewrite using `[finsum_eq_single _ x0]`. Rewrite using `[if_pos (by rw [hx0, neg_neg])]`. Introduce `x hx`. Rewrite using `[if_neg]`.

Introduce `h`. Apply `hx` to reduce the goal to its premises. Apply `hκ.1` to reduce the goal to its premises. Rewrite using `[hx0, h, neg_neg]`.
-/
theorem finsum_fiber {X Y T : Type} [AddGroup Y] [Fintype T] (κ : X → Y)
    (hκ : Function.Bijective κ) (g : T → Y) (f : T → ℂ) [∀ τ x, Decidable (g τ = -κ x)] :
    (Function.support fun x => ∑ τ : T, if g τ = -κ x then f τ else 0).Finite ∧
      ∑ᶠ x, ∑ τ : T, (if g τ = -κ x then f τ else 0) = ∑ τ : T, f τ := by
  have hfin : ∀ τ : T, (Function.support fun x => if g τ = -κ x then f τ else 0).Finite := by
    intro τ
    apply Set.Subsingleton.finite
    intro x hx y hy
    simp only [Function.mem_support, ne_eq, ite_eq_right_iff, Classical.not_imp] at hx hy
    apply hκ.1
    rw [← neg_inj, ← hx.1, ← hy.1]
  refine ⟨?_, ?_⟩
  · refine (Set.finite_iUnion hfin).subset ?_
    intro x hx
    simp only [Function.mem_support, ne_eq] at hx
    by_contra hcon
    apply hx
    apply Finset.sum_eq_zero
    intro τ _
    by_contra h0
    exact hcon (Set.mem_iUnion.mpr ⟨τ, h0⟩)
  · rw [finsum_sum_comm _ _ (fun τ _ => hfin τ)]
    apply Finset.sum_congr rfl
    intro τ _
    obtain ⟨x0, hx0⟩ := hκ.2 (-g τ)
    rw [finsum_eq_single _ x0]
    · rw [if_pos (by rw [hx0, neg_neg])]
    · intro x hx
      rw [if_neg]
      intro h
      apply hx
      apply hκ.1
      rw [hx0, h, neg_neg]

/- English proof (translation)
Establish `: Finite (coker R Z ≃ₗ[R] coker R Z')` using `Finite.of_injective (fun θ : coker R Z ≃ₗ[R] coker R Z' => (θ : coker R Z → coker R Z')) (fun x y h => LinearEquiv.ext (congrFun h))`. Set `_` to `Fintype.ofFinite (coker R Z ≃ₗ[R] coker R Z')`. Set `_` to `Fintype.ofFinite (coker R Z →ₗ[R] KR R)`. Set `_` to `Fintype.ofFinite (coker R Z)`. Set `f : (coker R Z ≃ₗ[R] coker R Z') × (coker R Z →ₗ[R] KR R) × coker R Z → ℂ` to `fun τ => psiKR R ψ (τ.2.1 (eZ R Z - τ.1.symm (eZ R Z')) + (lamLin R Z (Quotient.out τ.2.2) - lamLin R Z' (Quotient.out (τ.1 τ.2.2))))`.

Set `g : (coker R Z ≃ₗ[R] coker R Z') × (coker R Z →ₗ[R] KR R) × coker R Z → KR R` to `fun τ => τ.2.1 τ.2.2`. Establish `hform : ∀ c : K, singleBlockInner R ψ Z Z' c = ∑ τ, if g τ = -(Submodule.Quotient.mk c : KR R) then f τ else 0`. Introduce `c`. Unfold `singleBlockInner`. Rewrite using `[finsum_eq_sum_of_fintype, Fintype.sum_prod_type]`.

Apply `Finset.sum_congr rfl` to reduce the goal to its premises. Introduce `θ _`. Rewrite using `[finsum_eq_sum_of_fintype, Fintype.sum_prod_type]`. Apply `Finset.sum_congr rfl` to reduce the goal to its premises. Introduce `α _`.

Rewrite using `[finsum_eq_sum_of_fintype]`. Establish `key` using `finsum_fiber (fun x => (Submodule.Quotient.mk (κ x) : KR R)) hκ g f`. Simplify using `only [hform]`. Use `⟨key.1, ?_⟩` and prove the remaining obligations. Rewrite using `[key.2]`.

Establish `hf : ∀ τ, f τ = psiKR R ψ (τ.2.1 (eZ R Z - τ.1.symm (eZ R Z'))) * psiKR R ψ ((muZ R Z hZ - (muZ R Z' hZ').comp τ.1.toLinearMap) τ.2.2)`. Introduce `τ`. Simplify using `only [f]`. Rewrite using `[psiKR_add R ψ hψ, lamLin_out R Z hZ, lamLin_out R Z' hZ']`. Both sides reduce to the same expression.

Simplify using `only [hf]`. Rewrite using `[Fintype.sum_prod_type]`. Establish `hθ : ∀ θ : coker R Z ≃ₗ[R] coker R Z', ∑ y : (coker R Z →ₗ[R] KR R) × coker R Z, psiKR R ψ (y.1 (eZ R Z - θ.symm (eZ R Z'))) * psiKR R ψ ((muZ R Z hZ - (muZ R Z' hZ').comp θ.toLinearMap) y.2) = if θ ∈ isoZZ R Z Z' then (Nat.card (coker R Z) : ℂ) * (Nat.card (coker R Z') : ℂ) else …`. Introduce `θ`. Rewrite using `[Fintype.sum_prod_type]`.

Simplify using `only`. Rewrite using `[← Finset.sum_mul_sum, ← finsum_eq_sum_of_fintype, ← finsum_eq_sum_of_fintype]`. Distinguish the cases in `h1 : eZ R Z - θ.symm (eZ R Z') = 0`. Distinguish the cases in `h2 : muZ R Z hZ - (muZ R Z' hZ').comp θ.toLinearMap = 0`. Rewrite using `[hOD1 _ h1, hO1 _ h2, if_pos ((mem_isoZZ_iff R Z Z' hZ hZ' θ).mpr ⟨h1, h2⟩), ← Nat.card_congr θ.toEquiv]`.

Rewrite using `[hO2 _ h2, mul_zero, if_neg]`. Introduce `h`. Conclude with `h2 ((mem_isoZZ_iff R Z Z' hZ hZ' θ).mp h).2`. Rewrite using `[hOD2 _ h1, zero_mul, if_neg]`. Introduce `h`.

Conclude with `h1 ((mem_isoZZ_iff R Z Z' hZ hZ' θ).mp h).1`. Rewrite using `[Finset.sum_congr rfl (fun θ _ => hθ θ), Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul, Nat.subtype_card (Finset.univ.filter (· ∈ isoZZ R Z Z')) (by simp)]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem first_kernel_inner_sum {K : Type} [CommRing K] (R : Subring K) (ψ : AddChar K ℂ)
    (hψ : ∀ r ∈ R, ψ r = 1) {n n' : ℕ} (Z : Matrix (Fin n) (Fin n) K)
    (Z' : Matrix (Fin n') (Fin n') K) (hZ : IsUnit Z.det) (hZ' : IsUnit Z'.det)
    (hC : Finite (coker R Z)) (hC' : Finite (coker R Z')) (hD : Finite (coker R Z →ₗ[R] KR R))
    (hOD1 : ∀ x : coker R Z, x = 0 →
      ∑ᶠ α : coker R Z →ₗ[R] KR R, psiKR R ψ (α x) = (Nat.card (coker R Z) : ℂ))
    (hOD2 : ∀ x : coker R Z, x ≠ 0 → ∑ᶠ α : coker R Z →ₗ[R] KR R, psiKR R ψ (α x) = 0)
    (hO1 : ∀ μ : coker R Z →ₗ[R] KR R, μ = 0 →
      ∑ᶠ β : coker R Z, psiKR R ψ (μ β) = (Nat.card (coker R Z) : ℂ))
    (hO2 : ∀ μ : coker R Z →ₗ[R] KR R, μ ≠ 0 → ∑ᶠ β : coker R Z, psiKR R ψ (μ β) = 0)
    {X : Type} (κ : X → K)
    (hκ : Function.Bijective (fun x => (Submodule.Quotient.mk (κ x) : KR R))) :
    (Function.support fun x => singleBlockInner R ψ Z Z' (κ x)).Finite ∧
      ∑ᶠ x, singleBlockInner R ψ Z Z' (κ x) = (Nat.card (coker R Z) : ℂ) * (Nat.card (coker R Z') : ℂ) *
        (Nat.card (isoZZ R Z Z') : ℂ) := by
  classical
  have : Finite (coker R Z ≃ₗ[R] coker R Z') :=
    Finite.of_injective (fun θ : coker R Z ≃ₗ[R] coker R Z' => (θ : coker R Z → coker R Z'))
      (fun x y h => LinearEquiv.ext (congrFun h))
  let _ := Fintype.ofFinite (coker R Z ≃ₗ[R] coker R Z')
  let _ := Fintype.ofFinite (coker R Z →ₗ[R] KR R)
  let _ := Fintype.ofFinite (coker R Z)
  let f : (coker R Z ≃ₗ[R] coker R Z') × (coker R Z →ₗ[R] KR R) × coker R Z → ℂ := fun τ =>
    psiKR R ψ (τ.2.1 (eZ R Z - τ.1.symm (eZ R Z')) +
      (lamLin R Z (Quotient.out τ.2.2) - lamLin R Z' (Quotient.out (τ.1 τ.2.2))))
  let g : (coker R Z ≃ₗ[R] coker R Z') × (coker R Z →ₗ[R] KR R) × coker R Z → KR R :=
    fun τ => τ.2.1 τ.2.2
  have hform : ∀ c : K, singleBlockInner R ψ Z Z' c =
      ∑ τ, if g τ = -(Submodule.Quotient.mk c : KR R) then f τ else 0 := by
    intro c
    unfold singleBlockInner
    rw [finsum_eq_sum_of_fintype, Fintype.sum_prod_type]
    apply Finset.sum_congr rfl
    intro θ _
    rw [finsum_eq_sum_of_fintype, Fintype.sum_prod_type]
    apply Finset.sum_congr rfl
    intro α _
    rw [finsum_eq_sum_of_fintype]
  have key := finsum_fiber (fun x => (Submodule.Quotient.mk (κ x) : KR R)) hκ g f
  simp only [hform]
  refine ⟨key.1, ?_⟩
  rw [key.2]
  have hf : ∀ τ, f τ = psiKR R ψ (τ.2.1 (eZ R Z - τ.1.symm (eZ R Z'))) *
      psiKR R ψ ((muZ R Z hZ - (muZ R Z' hZ').comp τ.1.toLinearMap) τ.2.2) := by
    intro τ
    simp only [f]
    rw [psiKR_add R ψ hψ, lamLin_out R Z hZ, lamLin_out R Z' hZ']
    rfl
  simp only [hf]
  rw [Fintype.sum_prod_type]
  have hθ : ∀ θ : coker R Z ≃ₗ[R] coker R Z',
      ∑ y : (coker R Z →ₗ[R] KR R) × coker R Z,
        psiKR R ψ (y.1 (eZ R Z - θ.symm (eZ R Z'))) *
          psiKR R ψ ((muZ R Z hZ - (muZ R Z' hZ').comp θ.toLinearMap) y.2) =
      if θ ∈ isoZZ R Z Z' then (Nat.card (coker R Z) : ℂ) * (Nat.card (coker R Z') : ℂ) else 0 := by
    intro θ
    rw [Fintype.sum_prod_type]
    simp only
    rw [← Finset.sum_mul_sum, ← finsum_eq_sum_of_fintype, ← finsum_eq_sum_of_fintype]
    by_cases h1 : eZ R Z - θ.symm (eZ R Z') = 0
    · by_cases h2 : muZ R Z hZ - (muZ R Z' hZ').comp θ.toLinearMap = 0
      · rw [hOD1 _ h1, hO1 _ h2, if_pos ((mem_isoZZ_iff R Z Z' hZ hZ' θ).mpr ⟨h1, h2⟩),
          ← Nat.card_congr θ.toEquiv]
      · rw [hO2 _ h2, mul_zero, if_neg]
        intro h; exact h2 ((mem_isoZZ_iff R Z Z' hZ hZ' θ).mp h).2
    · rw [hOD2 _ h1, zero_mul, if_neg]
      intro h; exact h1 ((mem_isoZZ_iff R Z Z' hZ hZ' θ).mp h).1
  rw [Finset.sum_congr rfl (fun θ _ => hθ θ), Finset.sum_ite, Finset.sum_const_zero, add_zero,
    Finset.sum_const, nsmul_eq_mul,
    Nat.subtype_card (Finset.univ.filter (· ∈ isoZZ R Z Z')) (by simp)]
  ring

/- English proof (translation)
Unfold `orbZ`. Rewrite using `[Matrix.det_mul, Matrix.det_mul, isLowUni_det K p.1.2.1, isUpUni_det K p.2.2, one_mul, mul_one]`.
-/
theorem orbZ_det {K : Type} [CommRing K] (w : Point K)
    (p : lowW K w.1 w.2 × upUniG K w.1.sum) : (orbZ w p).det = (pt w.1 w.2).det := by
  unfold orbZ
  rw [Matrix.det_mul, Matrix.det_mul, isLowUni_det K p.1.2.1, isUpUni_det K p.2.2, one_mul,
    mul_one]

/- English proof (translation)
Unfold `SingleBlockPeriodic`. Unfold `SingleBlockFormula at hF`. Introduce `K _ _ _ R ψ hLD h h' c c' hs hc`. Rewrite using `[hF K R ψ hLD h h' c hs, hF K R ψ hLD h h' c' hs]`. Establish `e : (Submodule.Quotient.mk (c : K) : KR R) = Submodule.Quotient.mk (c' : K)`.

Rewrite using `[Submodule.Quotient.eq, mem_rangeR]`. Conclude with `hc`. Establish `e2 : ∀ {n n' : ℕ} (Z : Matrix (Fin n) (Fin n) K) (Z' : Matrix (Fin n') (Fin n') K), singleBlockInner R ψ Z Z' (c : K) = singleBlockInner R ψ Z Z' (c' : K)`. Introduce `n n' Z Z'`. Unfold `singleBlockInner`.

Rewrite using `[e]`. Simplify using `only [e2]`.
-/
theorem first_kernel_periodic_of_formula (hF : SingleBlockFormula) : SingleBlockPeriodic := by
  unfold SingleBlockPeriodic
  unfold SingleBlockFormula at hF
  intro K _ _ _ R ψ hLD h h' c c' hs hc
  rw [hF K R ψ hLD h h' c hs, hF K R ψ hLD h h' c' hs]
  have e : (Submodule.Quotient.mk (c : K) : KR R) = Submodule.Quotient.mk (c' : K) := by
    rw [Submodule.Quotient.eq, mem_rangeR]
    exact hc
  have e2 : ∀ {n n' : ℕ} (Z : Matrix (Fin n) (Fin n) K) (Z' : Matrix (Fin n') (Fin n') K),
      singleBlockInner R ψ Z Z' (c : K) = singleBlockInner R ψ Z Z' (c' : K) := by
    intro n n' Z Z'
    unfold singleBlockInner
    rw [e]
  simp only [e2]

/- English proof (translation)
Introduce `K _ _ _ R ψ hL h h' e cr hcr`. Establish `hψ : ∀ r ∈ R, ψ r = 1` using `fun r hr => by`. Simplify using `using (hL.selfDual 1).mpr R.one_mem r hr`. Establish `hκ : Function.Bijective (fun x : K ⧸ R.toAddSubgroup => (Submodule.Quotient.mk ((cr x : Kˣ) : K) : KR R))`. Prove the components needed by the constructor for the conclusion.

Introduce `x y hxy`. Establish `h1` using `(mem_rangeR R _).mp ((Submodule.Quotient.eq _).mp hxy)`. Rewrite using `[← hcr x, ← hcr y]`. Conclude with `QuotientAddGroup.eq_iff_sub_mem.mpr h1`. Introduce `y`.

Take `⟨a, rfl⟩` from `Submodule.Quotient.mk_surjective _ y`. Use `⟨(a : K ⧸ R.toAddSubgroup), ?_⟩` and prove the remaining obligations. Apply `(Submodule.Quotient.eq _).mpr` to reduce the goal to its premises. Rewrite using `[mem_rangeR]`. Conclude with `QuotientAddGroup.eq_iff_sub_mem.mp (hcr (a : K ⧸ R.toAddSubgroup))`.

Set `G : (K ⧸ R.toAddSubgroup) → Cos R h × Cos R h' → ℂ` to `fun x q => (if IsInt R (orbZ h (rep R q.1)) ∧ IsInt R (orbZ h' (rep R q.2)) then singleBlockInner R ψ (orbZ h (rep R q.1)) (orbZ h' (rep R q.2)) ((cr x : Kˣ) : K) else 0) * phase ψ (rep R q.1) * conj (phase ψ (rep R q.2))`. Establish `hG : ∀ q, (Function.support fun x => G x q).Finite ∧ ∑ᶠ x, G x q = ((cSize R h * cSize R h' : ℝ) : ℂ) * pairTerm R ψ h h' q`. Introduce `q`. Distinguish the cases in `hq : IsInt R (orbZ h (rep R q.1)) ∧ IsInt R (orbZ h' (rep R q.2))`. Establish `hZ : IsUnit (orbZ h (rep R q.1)).det` using `by rw [orbZ_det]; exact pt_det_isUnit h`.

Establish `hZ' : IsUnit (orbZ h' (rep R q.2)).det` using `by rw [orbZ_det]; exact pt_det_isUnit h'`. Take `⟨hC, hcard⟩` from `hCC K R ψ hL _ _ hq.1 hZ`. Take `⟨hC', hcard'⟩` from `hCC K R ψ hL _ _ hq.2 hZ'`. Take `⟨hD, hOD⟩` from `hCD K R ψ hL _ _ hq.1 hZ`. Establish `hO` using `hCO K R ψ hL _ _ hq.1 hZ`.

Establish `key` using `first_kernel_inner_sum R ψ hψ _ _ hZ hZ' hC hC' hD (fun x hx => by rw [hOD x, if_pos hx]) (fun x hx => by rw [hOD x, if_neg hx]; simp) (fun μ hμ => by rw [hO μ, if_pos hμ]) (fun μ hμ => by rw [hO μ, if_neg hμ]; simp) (fun x : K ⧸ R.toAddSubgroup => ((cr x : Kˣ) : K)) hκ`. Establish `hc : (Nat.card (coker R (orbZ h (rep R q.1))) : ℂ) = ((cSize R h : ℝ) : ℂ)`. Rewrite using `[cSize, ← orbZ_det h (rep R q.1), ← hcard]`. Simplify using the standard rewrite rules. Establish `hc' : (Nat.card (coker R (orbZ h' (rep R q.2))) : ℂ) = ((cSize R h' : ℝ) : ℂ)`.

Rewrite using `[cSize, ← orbZ_det h' (rep R q.2), ← hcard']`. Simplify using the standard rewrite rules. Simplify using `only [G, if_pos hq, mul_assoc]`. Prove the components needed by the constructor for the conclusion. Use `key.1.subset ?_` and prove the remaining obligations.

Introduce `x hx`. Simplify using `only [Function.mem_support, ne_eq] at hx ⊢`. Introduce `h0`. Apply `hx` to reduce the goal to its premises. Rewrite using `[h0, zero_mul]`.

Rewrite using `[← finsum_mul, key.2, hc, hc']`. Unfold `pairTerm`. Rewrite using `[if_pos hq]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.

Simplify using `only [G, if_neg hq, pairTerm]`. Simplify using the standard rewrite rules. Establish `hS` using `(hI K R ψ hL h).prod (hI K R ψ hL h')`. Establish `hNs : ∀ x, Ns R ψ 1 h h' (cr x) (cr x) = ∑ q ∈ hS.toFinset, G x q`. Introduce `x`.

Rewrite using `[hF K R ψ hL h h' (cr x) e]`. Apply `finsum_eq_sum_of_support_subset` to reduce the goal to its premises. Introduce `q hq`. Simplify using `only [Function.mem_support, ne_eq] at hq`. Rewrite using `[Set.Finite.coe_toFinset]`.

Assume the negation of the conclusion as `hcon`. Apply `hq` to reduce the goal to its premises. Rewrite using `[if_neg (fun hI' => hcon ⟨hI'.1, hI'.2⟩)]`. Simplify using the standard rewrite rules. Establish `hKp : N0 R ψ h h' = ∑ q ∈ hS.toFinset, pairTerm R ψ h h' q`.

Unfold `N0 Kp`. Apply `finsum_eq_sum_of_support_subset` to reduce the goal to its premises. Introduce `q hq`. Simplify using `only [Function.mem_support, ne_eq, pairTerm] at hq`. Rewrite using `[Set.Finite.coe_toFinset]`.

Assume the negation of the conclusion as `hcon`. Apply `hq` to reduce the goal to its premises. Rewrite using `[if_neg (fun hI' => hcon ⟨hI'.1, hI'.2⟩)]`. Simplify using the standard rewrite rules. Simplify using `only [hNs]`.

Prove the components needed by the constructor for the conclusion. Use `(Set.Finite.biUnion hS.toFinset.finite_toSet (fun q _ => (hG q).1)).subset ?_` and prove the remaining obligations. Introduce `x hx`. Simplify using `only [Function.mem_support, ne_eq] at hx`. Assume the negation of the conclusion as `hcon`.

Apply `hx` to reduce the goal to its premises. Apply `Finset.sum_eq_zero` to reduce the goal to its premises. Introduce `q hq`. Assume the negation of the conclusion as `h0`. Conclude with `hcon (Set.mem_biUnion (Finset.mem_coe.mpr hq) h0)`.

Rewrite using `[finsum_sum_comm _ _ (fun q _ => (hG q).1), hKp, Finset.mul_sum]`. Conclude with `Finset.sum_congr rfl (fun q _ => (hG q).2)`.
-/
theorem first_kernel_parseval_of_formula (hF : SingleBlockFormula) (hI : IntFinite) (hCD : CharOrthDual) (hCO : CharOrth)
    (hCC : CokerCard) : SingleBlockParseval := by
  intro K _ _ _ R ψ hL h h' e cr hcr
  classical
  have hψ : ∀ r ∈ R, ψ r = 1 := fun r hr => by
    simpa using (hL.selfDual 1).mpr R.one_mem r hr
  have hκ : Function.Bijective (fun x : K ⧸ R.toAddSubgroup =>
      (Submodule.Quotient.mk ((cr x : Kˣ) : K) : KR R)) := by
    constructor
    · intro x y hxy
      have h1 := (mem_rangeR R _).mp ((Submodule.Quotient.eq _).mp hxy)
      rw [← hcr x, ← hcr y]
      exact QuotientAddGroup.eq_iff_sub_mem.mpr h1
    · intro y
      obtain ⟨a, rfl⟩ := Submodule.Quotient.mk_surjective _ y
      refine ⟨(a : K ⧸ R.toAddSubgroup), ?_⟩
      apply (Submodule.Quotient.eq _).mpr
      rw [mem_rangeR]
      exact QuotientAddGroup.eq_iff_sub_mem.mp (hcr (a : K ⧸ R.toAddSubgroup))
  let G : (K ⧸ R.toAddSubgroup) → Cos R h × Cos R h' → ℂ := fun x q =>
    (if IsInt R (orbZ h (rep R q.1)) ∧ IsInt R (orbZ h' (rep R q.2)) then
      singleBlockInner R ψ (orbZ h (rep R q.1)) (orbZ h' (rep R q.2)) ((cr x : Kˣ) : K) else 0) *
      phase ψ (rep R q.1) * conj (phase ψ (rep R q.2))
  have hG : ∀ q, (Function.support fun x => G x q).Finite ∧
      ∑ᶠ x, G x q = ((cSize R h * cSize R h' : ℝ) : ℂ) * pairTerm R ψ h h' q := by
    intro q
    by_cases hq : IsInt R (orbZ h (rep R q.1)) ∧ IsInt R (orbZ h' (rep R q.2))
    · have hZ : IsUnit (orbZ h (rep R q.1)).det := by rw [orbZ_det]; exact pt_det_isUnit h
      have hZ' : IsUnit (orbZ h' (rep R q.2)).det := by rw [orbZ_det]; exact pt_det_isUnit h'
      obtain ⟨hC, hcard⟩ := hCC K R ψ hL _ _ hq.1 hZ
      obtain ⟨hC', hcard'⟩ := hCC K R ψ hL _ _ hq.2 hZ'
      obtain ⟨hD, hOD⟩ := hCD K R ψ hL _ _ hq.1 hZ
      have hO := hCO K R ψ hL _ _ hq.1 hZ
      have key := first_kernel_inner_sum R ψ hψ _ _ hZ hZ' hC hC' hD
        (fun x hx => by rw [hOD x, if_pos hx]) (fun x hx => by rw [hOD x, if_neg hx]; simp)
        (fun μ hμ => by rw [hO μ, if_pos hμ]) (fun μ hμ => by rw [hO μ, if_neg hμ]; simp)
        (fun x : K ⧸ R.toAddSubgroup => ((cr x : Kˣ) : K)) hκ
      have hc : (Nat.card (coker R (orbZ h (rep R q.1))) : ℂ) = ((cSize R h : ℝ) : ℂ) := by
        rw [cSize, ← orbZ_det h (rep R q.1), ← hcard]; simp
      have hc' : (Nat.card (coker R (orbZ h' (rep R q.2))) : ℂ) = ((cSize R h' : ℝ) : ℂ) := by
        rw [cSize, ← orbZ_det h' (rep R q.2), ← hcard']; simp
      simp only [G, if_pos hq, mul_assoc]
      constructor
      · refine key.1.subset ?_
        intro x hx
        simp only [Function.mem_support, ne_eq] at hx ⊢
        intro h0; apply hx; rw [h0, zero_mul]
      · rw [← finsum_mul, key.2, hc, hc']
        unfold pairTerm
        rw [if_pos hq]
        push_cast
        ring
    · simp only [G, if_neg hq, pairTerm]
      simp
  have hS := (hI K R ψ hL h).prod (hI K R ψ hL h')
  have hNs : ∀ x, Ns R ψ 1 h h' (cr x) (cr x) = ∑ q ∈ hS.toFinset, G x q := by
    intro x
    rw [hF K R ψ hL h h' (cr x) e]
    apply finsum_eq_sum_of_support_subset
    intro q hq
    simp only [Function.mem_support, ne_eq] at hq
    rw [Set.Finite.coe_toFinset]
    by_contra hcon
    apply hq
    rw [if_neg (fun hI' => hcon ⟨hI'.1, hI'.2⟩)]
    simp
  have hKp : N0 R ψ h h' = ∑ q ∈ hS.toFinset, pairTerm R ψ h h' q := by
    unfold N0 Kp
    apply finsum_eq_sum_of_support_subset
    intro q hq
    simp only [Function.mem_support, ne_eq, pairTerm] at hq
    rw [Set.Finite.coe_toFinset]
    by_contra hcon
    apply hq
    rw [if_neg (fun hI' => hcon ⟨hI'.1, hI'.2⟩)]
    simp
  simp only [hNs]
  constructor
  · refine (Set.Finite.biUnion hS.toFinset.finite_toSet (fun q _ => (hG q).1)).subset ?_
    intro x hx
    simp only [Function.mem_support, ne_eq] at hx
    by_contra hcon
    apply hx
    apply Finset.sum_eq_zero
    intro q hq
    by_contra h0
    exact hcon (Set.mem_biUnion (Finset.mem_coe.mpr hq) h0)
  · rw [finsum_sum_comm _ _ (fun q _ => (hG q).1), hKp, Finset.mul_sum]
    exact Finset.sum_congr rfl (fun q _ => (hG q).2)

/- English proof (translation)
Simplify using `[addBlock]`.
-/
theorem addBlock_sum {K : Type} [CommRing K] (h : Point K) (s : ℕ) (t : Kˣ) :
    (addBlock h s t).1.sum = h.1.sum + s := by
  simp [addBlock]

/- English proof (translation)
Introduce `K _ _ _ R ψ hL s hs h h' t t' hsz hN`. Establish `hKp : Kp R ψ (addBlock h s t) (addBlock h' s t') ≠ 0`. Introduce `h0`. Apply `hN` to reduce the goal to its premises. Simplify using `[Ns, h0]`.

Establish `e1 : (addBlock h s t).1.sum = (h.1.sum + (s - 1)) + 1` using `by rw [addBlock_sum]; omega`. Establish `e2 : (addBlock h' s t').1.sum = (h.1.sum + (s - 1)) + 1` using `by rw [addBlock_sum]; omega`. Rewrite `hKp` using `[hTF K R ψ _ _ _ e1 e2]`. Establish `desc : ∀ d, d + 1 ≤ s → intTT R ψ (h.1.sum + d) (addBlock h s t) (addBlock h' s t') = intTT R ψ h.1.sum (addBlock h s t) (addBlock h' s t')`. Introduce `d`.

Proceed by induction on `d with`. Consider the case `zero => intro _`. Both sides reduce to the same expression. Consider the case `succ d ih`. Introduce `hd`.

Rewrite using `[← ih (by omega)]`. Conclude with `hAvg K R ψ hL h h' s t t' (h.1.sum + d) hsz (by omega) (by omega)`. Rewrite `hKp` using `[desc (s - 1) (by omega)]`. Unfold `intTT at hKp`. Assume the negation of the conclusion as `hcon`.

Apply `hKp` to reduce the goal to its premises. Apply `finsum_eq_zero_of_forall_eq_zero` to reduce the goal to its premises. Introduce `q`. Use `split_ifs with hI`. Establish `: IsEmpty {φ : coker R (orbZ (addBlock h s t) (rep R q.1)) ≃ₗ[R] coker R (orbZ (addBlock h' s t') (rep R q.2)) // φ ∈ isoZZ R (orbZ (addBlock h s t) (rep R q.1)) (orbZ (addBlock h' s t') (rep R q.2)) ∧ InTT R h.1.sum (orbZ (addBlock h s t) (rep R q.1)) (orbZ (addBlock h' s t') (r …`.

Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨φ, hφ, hT⟩`. Conclude with `hcon (hEnd K R h h' s t t' hsz hs _ _ _ _ (rep R q.1).1.2.1 (rep R q.1).2.2 (rep R q.2).1.2.1 (rep R q.2).2.2 φ hφ hT)`. Simplify using `[Nat.card_of_isEmpty]`. Simplify using the standard rewrite rules.
-/
theorem second_vanishing_of_triple_form (hTF : TripleForm) (hAvg : AvgClaim) (hEnd : TTEnd) : BlockKernelSupport := by
  intro K _ _ _ R ψ hL s hs h h' t t' hsz hN
  have hKp : Kp R ψ (addBlock h s t) (addBlock h' s t') ≠ 0 := by
    intro h0; apply hN; simp [Ns, h0]
  have e1 : (addBlock h s t).1.sum = (h.1.sum + (s - 1)) + 1 := by rw [addBlock_sum]; omega
  have e2 : (addBlock h' s t').1.sum = (h.1.sum + (s - 1)) + 1 := by rw [addBlock_sum]; omega
  rw [hTF K R ψ _ _ _ e1 e2] at hKp
  have desc : ∀ d, d + 1 ≤ s → intTT R ψ (h.1.sum + d) (addBlock h s t) (addBlock h' s t') =
      intTT R ψ h.1.sum (addBlock h s t) (addBlock h' s t') := by
    intro d
    induction d with
    | zero => intro _; rfl
    | succ d ih =>
      intro hd
      rw [← ih (by omega)]
      exact hAvg K R ψ hL h h' s t t' (h.1.sum + d) hsz (by omega) (by omega)
  rw [desc (s - 1) (by omega)] at hKp
  unfold intTT at hKp
  by_contra hcon
  apply hKp
  apply finsum_eq_zero_of_forall_eq_zero
  intro q
  split_ifs with hI
  · have : IsEmpty {φ : coker R (orbZ (addBlock h s t) (rep R q.1)) ≃ₗ[R]
        coker R (orbZ (addBlock h' s t') (rep R q.2)) //
        φ ∈ isoZZ R (orbZ (addBlock h s t) (rep R q.1)) (orbZ (addBlock h' s t') (rep R q.2)) ∧
        InTT R h.1.sum (orbZ (addBlock h s t) (rep R q.1))
          (orbZ (addBlock h' s t') (rep R q.2)) φ} := by
      constructor
      rintro ⟨φ, hφ, hT⟩
      exact hcon (hEnd K R h h' s t t' hsz hs _ _ _ _ (rep R q.1).1.2.1 (rep R q.1).2.2
        (rep R q.2).1.2.1 (rep R q.2).2.2 φ hφ hT)
    simp [Nat.card_of_isEmpty]
  · simp

/- English proof (translation)
Rewrite using `[← Finset.sum_fiberwise_of_maps_to (fun x hx => Finset.mem_image_of_mem f hx) (fun x => a x * g (f x))]`. Use `Finset.sum_congr rfl fun y _ => ?_` and prove the remaining obligations. Rewrite using `[Finset.sum_mul]`. Use `Finset.sum_congr rfl fun x hx => ?_` and prove the remaining obligations. Rewrite using `[(Finset.mem_filter.mp hx).2]`.
-/
private lemma sum_mul_comp_eq_sum_image_filter {X Y : Type} [DecidableEq Y] (F : Finset X) (f : X → Y)
    (a : X → ℂ) (g : Y → ℂ) :
    ∑ x ∈ F, a x * g (f x) =
      ∑ y ∈ F.image f, (∑ x ∈ F.filter (fun x => f x = y), a x) * g y := by
  rw [← Finset.sum_fiberwise_of_maps_to (fun x hx => Finset.mem_image_of_mem f hx)
    (fun x => a x * g (f x))]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun x hx => ?_
  rw [(Finset.mem_filter.mp hx).2]

/- English proof (translation)
Unfold `IsPSD at h ⊢`. Introduce `a`. Take `⟨h1, h2⟩` from `h (fun z => ∑ u ∈ F.filter (fun u => f u = z), a u)`. Establish `e1 : ∀ z, ∑ y ∈ F, conj (a y) * k z (f y) = ∑ w ∈ F.image f, conj (∑ u ∈ F.filter (fun u => f u = w), a u) * k z w`. Introduce `z`.

Rewrite using `[sum_mul_comp_eq_sum_image_filter F f (fun y => conj (a y)) (k z)]`. Use `Finset.sum_congr rfl fun w _ => ?_` and prove the remaining obligations. Rewrite using `[map_sum]`. Establish `key : ∑ x ∈ F, ∑ y ∈ F, a x * conj (a y) * k (f x) (f y) = ∑ x ∈ F.image f, ∑ y ∈ F.image f, (∑ u ∈ F.filter (fun u => f u = x), a u) * conj (∑ u ∈ F.filter (fun u => f u = y), a u) * k x y`. Combine the equalities or inequalities in the displayed calculation.

Use `Finset.sum_congr rfl fun x _ => ?_` and prove the remaining obligations. Rewrite using `[Finset.mul_sum]`. Use `Finset.sum_congr rfl fun y _ => ?_` and prove the remaining obligations. Expand and normalize the polynomial expressions, which then agree. Use `_ = ∑ z ∈ F.image f, (∑ u ∈ F.filter (fun u => f u = z), a u) * ∑ y ∈ F, conj (a y) * k z (f y) := sum_mul_comp_eq_sum_image_filter F f a (fun z => ∑ y ∈ F, conj (a y) * k z (f y))`.

Use `_ = _ := by`. Use `Finset.sum_congr rfl fun z _ => ?_` and prove the remaining obligations. Rewrite using `[e1 z, Finset.mul_sum]`. Use `Finset.sum_congr rfl fun w _ => ?_` and prove the remaining obligations. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[key]`. Conclude with `⟨h1, h2⟩`.
-/
theorem psd_comap {X Y : Type} [DecidableEq Y] (k : Y → Y → ℂ) (f : X → Y) (F : Finset X)
    (h : IsPSD (F.image f) k) : IsPSD F (fun x y => k (f x) (f y)) := by
  unfold IsPSD at h ⊢
  intro a
  obtain ⟨h1, h2⟩ := h (fun z => ∑ u ∈ F.filter (fun u => f u = z), a u)
  have e1 : ∀ z, ∑ y ∈ F, conj (a y) * k z (f y) =
      ∑ w ∈ F.image f, conj (∑ u ∈ F.filter (fun u => f u = w), a u) * k z w := by
    intro z
    rw [sum_mul_comp_eq_sum_image_filter F f (fun y => conj (a y)) (k z)]
    refine Finset.sum_congr rfl fun w _ => ?_
    rw [map_sum]
  have key : ∑ x ∈ F, ∑ y ∈ F, a x * conj (a y) * k (f x) (f y) =
      ∑ x ∈ F.image f, ∑ y ∈ F.image f, (∑ u ∈ F.filter (fun u => f u = x), a u) *
        conj (∑ u ∈ F.filter (fun u => f u = y), a u) * k x y := by
    calc ∑ x ∈ F, ∑ y ∈ F, a x * conj (a y) * k (f x) (f y)
        = ∑ x ∈ F, a x * ∑ y ∈ F, conj (a y) * k (f x) (f y) := by
          refine Finset.sum_congr rfl fun x _ => ?_
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun y _ => ?_
          ring
      _ = ∑ z ∈ F.image f, (∑ u ∈ F.filter (fun u => f u = z), a u) *
            ∑ y ∈ F, conj (a y) * k z (f y) :=
          sum_mul_comp_eq_sum_image_filter F f a (fun z => ∑ y ∈ F, conj (a y) * k z (f y))
      _ = _ := by
          refine Finset.sum_congr rfl fun z _ => ?_
          rw [e1 z, Finset.mul_sum]
          refine Finset.sum_congr rfl fun w _ => ?_
          ring
  rw [key]
  exact ⟨h1, h2⟩

/- English proof (translation)
Unfold `IsPSD at h ⊢`. Introduce `a`. Establish `e : ∑ x ∈ F, ∑ y ∈ F, a x * conj (a y) * ((c x : ℂ) * (c y : ℂ) * k x y) = ∑ x ∈ F, ∑ y ∈ F, (a x * c x) * conj (a y * c y) * k x y`. Use `Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_` and prove the remaining obligations. Rewrite using `[map_mul, Complex.conj_ofReal]`.

Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e]`. Conclude with `h _`.
-/
private lemma isPSD_real_rescale {X : Type} (F : Finset X) (k : X → X → ℂ) (c : X → ℝ)
    (h : IsPSD F k) : IsPSD F (fun x y => (c x : ℂ) * (c y : ℂ) * k x y) := by
  unfold IsPSD at h ⊢
  intro a
  have e : ∑ x ∈ F, ∑ y ∈ F, a x * conj (a y) * ((c x : ℂ) * (c y : ℂ) * k x y) =
      ∑ x ∈ F, ∑ y ∈ F, (a x * c x) * conj (a y * c y) * k x y := by
    refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
    rw [map_mul, Complex.conj_ofReal]
    ring
  rw [e]
  exact h _

/- English proof (translation)
Unfold `BlockKernelPosSemidef`. Unfold `KpGram at hG`. Unfold `ModMul at hM`. Introduce `K _ _ _ R ψ hLD s hs m F hF`. Establish `hK` using `psd_comap (Kp R ψ) (fun x : Point K × Kˣ => addBlock x.1 s x.2) F (hG K R ψ hLD _)`.

Establish `hc` using `isPSD_real_rescale F _ (fun x : Point K × Kˣ => modK R (x.2 : K) ^ (s * (s - 1) / 2)) hK`. Establish `e : (fun x y : Point K × Kˣ => Ns R ψ s x.1 y.1 x.2 y.2) = fun x y => ((modK R (x.2 : K) ^ (s * (s - 1) / 2) : ℝ) : ℂ) * ((modK R (y.2 : K) ^ (s * (s - 1) / 2) : ℝ) : ℂ) * Kp R ψ (addBlock x.1 s x.2) (addBlock y.1 s y.2)`. Use function extensionality and compare the values at `x y`. Unfold `Ns`. Rewrite using `[(hM K R ψ hLD x.2 y.2).2, mul_pow, Complex.ofReal_mul]`.

Rewrite using `[e]`. Conclude with `hc`.
-/
theorem second_gram_of_kernel_gram (hG : KpGram) (hM : ModMul) : BlockKernelPosSemidef := by
  classical
  unfold BlockKernelPosSemidef
  unfold KpGram at hG
  unfold ModMul at hM
  intro K _ _ _ R ψ hLD s hs m F hF
  have hK := psd_comap (Kp R ψ) (fun x : Point K × Kˣ => addBlock x.1 s x.2) F
    (hG K R ψ hLD _)
  have hc := isPSD_real_rescale F _ (fun x : Point K × Kˣ => modK R (x.2 : K) ^ (s * (s - 1) / 2)) hK
  have e : (fun x y : Point K × Kˣ => Ns R ψ s x.1 y.1 x.2 y.2) = fun x y =>
      ((modK R (x.2 : K) ^ (s * (s - 1) / 2) : ℝ) : ℂ) *
        ((modK R (y.2 : K) ^ (s * (s - 1) / 2) : ℝ) : ℂ) *
        Kp R ψ (addBlock x.1 s x.2) (addBlock y.1 s y.2) := by
    funext x y
    unfold Ns
    rw [(hM K R ψ hLD x.2 y.2).2, mul_pow, Complex.ofReal_mul]
  rw [e]
  exact hc

/- English proof (translation)
Unfold `SingleBlockPosSemidef`. Unfold `BlockKernelPosSemidef at h`. Introduce `K _ _ _ R ψ hLD m F hF c`. Establish `hI` using `h K R ψ hLD 1 le_rfl m (F.image fun x => (x, c)) (by`. Introduce `x hx`.

Take `⟨y, hy, rfl⟩` from `Finset.mem_image.mp hx`. Conclude with `hF y hy)`. Conclude with `psd_comap (fun x y : Point K × Kˣ => Ns R ψ 1 x.1 y.1 x.2 y.2) (fun x => (x, c)) F hI`.
-/
theorem first_kernel_gram_of_second (h : BlockKernelPosSemidef) : SingleBlockPosSemidef := by
  classical
  unfold SingleBlockPosSemidef
  unfold BlockKernelPosSemidef at h
  intro K _ _ _ R ψ hLD m F hF c
  have hI := h K R ψ hLD 1 le_rfl m (F.image fun x => (x, c)) (by
    intro x hx
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hx
    exact hF y hy)
  exact psd_comap (fun x y : Point K × Kˣ => Ns R ψ 1 x.1 y.1 x.2 y.2) (fun x => (x, c)) F hI

end A5x6

open A5x6

/- English proof (translation)
Introduce `hG hM` and use `second_gram_of_kernel_gram hG hM`.
-/
theorem second_gram_of_gram_and_modulus : Formalism.FourierDecayAlt.A5.KpGram → Formalism.FourierDecayAlt.A5.ModMul → Formalism.FourierDecayAlt.A5.BlockKernelPosSemidef := fun hG hM => second_gram_of_kernel_gram hG hM

/- English proof (translation)
Unfold `Formalism.FourierDecayAlt.A5.BlockKernelPropertiesOfSteps Formalism.FourierDecayAlt.A5.A2`. Introduce `hG hM hTF hAvg hEnd`. Conclude with `⟨second_gram_of_kernel_gram hG hM, second_vanishing_of_triple_form hTF hAvg hEnd⟩`.
-/
theorem second_gram_vanishing_of_parts : Formalism.FourierDecayAlt.A5.BlockKernelPropertiesOfSteps := by
  unfold Formalism.FourierDecayAlt.A5.BlockKernelPropertiesOfSteps Formalism.FourierDecayAlt.A5.A2
  intro hG hM hTF hAvg hEnd
  exact ⟨second_gram_of_kernel_gram hG hM, second_vanishing_of_triple_form hTF hAvg hEnd⟩

/- English proof (translation)
Unfold `Formalism.FourierDecayAlt.A5.SingleBlockOfSteps`. Introduce `hF hI hCD hCO hCC hG`. Conclude with `⟨first_kernel_periodic_of_formula hF, first_kernel_gram_of_second hG, first_kernel_parseval_of_formula hF hI hCD hCO hCC⟩`.
-/
theorem first_kernel_properties_of_hypotheses : Formalism.FourierDecayAlt.A5.SingleBlockOfSteps := by
  unfold Formalism.FourierDecayAlt.A5.SingleBlockOfSteps
  intro hF hI hCD hCO hCC hG
  exact ⟨first_kernel_periodic_of_formula hF, first_kernel_gram_of_second hG, first_kernel_parseval_of_formula hF hI hCD hCO hCC⟩

/- English proof (translation)
Unfold `Formalism.FourierDecayAlt.A5.SingleBlockThetaOfSteps`. Introduce `hPer hGram hPars hSup hBD _`. Establish `h` using `first_theta_equality_of_kernel_facts hPer hGram hPars hSup hBD`. Conclude with `⟨first_theta_eq_of_equality h, h⟩`.
-/
theorem first_theta_properties_of_parts : Formalism.FourierDecayAlt.A5.SingleBlockThetaOfSteps := by
  unfold Formalism.FourierDecayAlt.A5.SingleBlockThetaOfSteps
  intro hPer hGram hPars hSup hBD _
  have h := first_theta_equality_of_kernel_facts hPer hGram hPars hSup hBD
  exact ⟨first_theta_eq_of_equality h, h⟩

/- English proof (translation)
Unfold `Formalism.FourierDecayAlt.A5.LemmaAAssemble Formalism.FourierDecayAlt.A5.LemmaA`. Introduce `hA2 hPars hTh hA13 hStep hN0 hSup hBD`. Use `⟨hA2, ?_, hTh, hA13, hN0, hSup, hBD⟩` and prove the remaining obligations. Introduce `s hs`. Proceed by induction on `s, hs using Nat.le_induction with`.

Consider the case `base => exact first_level_of_equality hA13`. Consider the case `succ s hs ih`. Unfold `Formalism.FourierDecayAlt.A5.A13 at ih ⊢`. Introduce `K _ _ _ R ψ hLD hU`. Unfold `Formalism.FourierDecayAlt.A5.ThetaExistsStep at hStep`.

Conclude with `hStep hA2 hPars K R ψ hLD hU s hs (ih K R ψ hLD hU)`.
-/
theorem lattice_average_lemma_from_parts : Formalism.FourierDecayAlt.A5.LemmaAAssemble := by
  unfold Formalism.FourierDecayAlt.A5.LemmaAAssemble Formalism.FourierDecayAlt.A5.LemmaA
  intro hA2 hPars hTh hA13 hStep hN0 hSup hBD
  refine ⟨hA2, ?_, hTh, hA13, hN0, hSup, hBD⟩
  intro s hs
  induction s, hs using Nat.le_induction with
  | base => exact first_level_of_equality hA13
  | succ s hs ih =>
    unfold Formalism.FourierDecayAlt.A5.A13 at ih ⊢
    intro K _ _ _ R ψ hLD hU
    unfold Formalism.FourierDecayAlt.A5.ThetaExistsStep at hStep
    exact hStep hA2 hPars K R ψ hLD hU s hs (ih K R ψ hLD hU)

end Formalism.FourierDecayAlt.P

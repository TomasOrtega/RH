import Mathlib
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.IsDiscriminantTwelfthRootOfIdealLattice
import Formalism.LocalToGlobal.GlobalTheory.GL3.CubicFields.EpsteinZeta.Jacobi
import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.PeriodLatticeAgreement

noncomputable section

namespace GlobalTheory.LatticePeriodEtaProof

open Formalism.MainNotions.TaylorLogMetric GlobalTheory.IndefiniteRowSideFullHecke.PeriodLatticeAgreement
open scoped UpperHalfPlane

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem lattice_discriminant_eq_weierstrass_discr (Λ : AddSubgroup ℂ) : discr Λ = Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.B5.discr Λ := rfl

/- English proof (translation)
Use extensionality with `w`. Rewrite using `[mem_latt, Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.B5.jac_mem_closure]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨m, n, rfl⟩`. Conclude with `⟨![n, m], by simp only [Matrix.cons_val_zero, Matrix.cons_val_one]; ring⟩`.

Introduce and unpack `⟨v, rfl⟩`. Conclude with `⟨v 1, v 0, by ring⟩`.
-/
theorem latt_eq_closure (ω₁ τ : ℂ) : latt ω₁ τ = AddSubgroup.closure {ω₁, ω₁ * τ} := by
  ext w
  rw [mem_latt, Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.B5.jac_mem_closure]
  constructor
  · rintro ⟨m, n, rfl⟩
    exact ⟨![n, m], by simp only [Matrix.cons_val_zero, Matrix.cons_val_one]; ring⟩
  · rintro ⟨v, rfl⟩
    exact ⟨v 1, v 0, by ring⟩

/- English proof (translation)
Introduce `ω₁ τ h`. Rewrite using `[lattice_discriminant_eq_weierstrass_discr, latt_eq_closure]`. Conclude with `Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.B5.jac_discr ω₁ τ h τ.2`.
-/
theorem discrEta : DiscrEta := by
  intro ω₁ τ h
  rw [lattice_discriminant_eq_weierstrass_discr, latt_eq_closure]
  exact Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.B5.jac_discr ω₁ τ h τ.2

/- English proof (translation)
Rewrite using `[Complex.sq_norm, Complex.normSq_apply]`. Simplify using `[Complex.mul_im, Complex.mul_re]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem im_conj_mul (ω τ : ℂ) (m n m' n' : ℤ) :
    ((starRingEnd ℂ) (ω * ((m : ℂ) + (n : ℂ) * τ)) * (ω * ((m' : ℂ) + (n' : ℂ) * τ))).im =
      ‖ω‖ ^ 2 * τ.im * ((m * n' - n * m' : ℤ) : ℝ) := by
  rw [Complex.sq_norm, Complex.normSq_apply]
  simp [Complex.mul_im, Complex.mul_re]
  ring

/- English proof (translation)
Introduce `ω₁ τ h`. Establish `hy : 0 < τ.im` using `τ.2`. Establish `hω : 0 < ‖ω₁‖` using `norm_pos_iff.2 h`. Establish `hc : 0 < ‖ω₁‖ ^ 2 * τ.im` using `by positivity`. Unfold `area`.

Apply `IsLeast.csInf_eq` to reduce the goal to its premises. Use `⟨⟨hc, ω₁ * ((1 : ℤ) + ((0 : ℤ) : ℂ) * (τ : ℂ)), ⟨1, 0, rfl⟩, ω₁ * (((0 : ℤ) : ℂ) + ((1 : ℤ) : ℂ) * (τ : ℂ)), ⟨0, 1, rfl⟩, ?_⟩, ?_⟩` and prove the remaining obligations. Rewrite using `[im_conj_mul]`. Evaluate the numerical expressions using `[UpperHalfPlane.coe_im, abs_of_pos hy]`. Introduce and unpack `a ⟨ha, w₁, ⟨m, n, rfl⟩, w₂, ⟨m', n', rfl⟩, rfl⟩`.

Rewrite `ha`, the goal using `[im_conj_mul]`. Simplify using `only [UpperHalfPlane.coe_im] at ha ⊢`. Rewrite using `[abs_mul, abs_of_pos hc]`. Establish `hd : (m * n' - n * m' : ℤ) ≠ 0`. Introduce and unpack `h0`.

Rewrite `ha` using `[h0]`. Simplify using `at ha`. Establish `h1 : (1 : ℝ) ≤ |((m * n' - n * m' : ℤ) : ℝ)|`. Rewrite using `[← Int.cast_abs]`. Conclude with `Int.one_le_abs hd` after adjusting the coercions.

Use the polynomial consequences of the given equalities and inequalities.
-/
theorem areaEq : AreaEq := by
  intro ω₁ τ h
  have hy : 0 < τ.im := τ.2
  have hω : 0 < ‖ω₁‖ := norm_pos_iff.2 h
  have hc : 0 < ‖ω₁‖ ^ 2 * τ.im := by positivity
  unfold area
  apply IsLeast.csInf_eq
  refine ⟨⟨hc, ω₁ * ((1 : ℤ) + ((0 : ℤ) : ℂ) * (τ : ℂ)), ⟨1, 0, rfl⟩,
    ω₁ * (((0 : ℤ) : ℂ) + ((1 : ℤ) : ℂ) * (τ : ℂ)), ⟨0, 1, rfl⟩, ?_⟩, ?_⟩
  · rw [im_conj_mul]
    norm_num [UpperHalfPlane.coe_im, abs_of_pos hy]
  · rintro a ⟨ha, w₁, ⟨m, n, rfl⟩, w₂, ⟨m', n', rfl⟩, rfl⟩
    rw [im_conj_mul] at ha ⊢
    simp only [UpperHalfPlane.coe_im] at ha ⊢
    rw [abs_mul, abs_of_pos hc]
    have hd : (m * n' - n * m' : ℤ) ≠ 0 := by
      rintro h0
      rw [h0] at ha
      simp at ha
    have h1 : (1 : ℝ) ≤ |((m * n' - n * m' : ℤ) : ℝ)| := by
      rw [← Int.cast_abs]
      exact_mod_cast Int.one_le_abs hd
    nlinarith

/- English proof (translation)
Introduce `ω₁ τ h`. Establish `hω : 0 < ‖ω₁‖` using `norm_pos_iff.2 h`. Establish `hπ : 0 < Real.pi` using `Real.pi_pos`. Unfold `period`. Rewrite using `[discrEta ω₁ τ h, areaEq ω₁ τ h]`.

Establish `e : ‖(2 * (Real.pi : ℂ) / ω₁) ^ 12 * ModularForm.eta (τ : ℂ) ^ 24‖ = ((2 * Real.pi / ‖ω₁‖) ^ 2 * ‖ModularForm.eta (τ : ℂ)‖ ^ 4) ^ 6`. Rewrite using `[norm_mul, norm_pow, norm_pow, norm_div, norm_mul, Complex.norm_real, Real.norm_of_nonneg hπ.le]`. Evaluate the numerical expressions. Expand and normalize the polynomial expressions, which then agree. Establish `hx : 0 ≤ (2 * Real.pi / ‖ω₁‖) ^ 2 * ‖ModularForm.eta (τ : ℂ)‖ ^ 4` using `by positivity`.

Rewrite using `[e, show ((1 : ℝ) / 6) = ((6 : ℕ) : ℝ)⁻¹ by norm_num, Real.pow_rpow_inv_natCast hx (by norm_num)]`. Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree.
-/
theorem periodEta : PeriodEta := by
  intro ω₁ τ h
  have hω : 0 < ‖ω₁‖ := norm_pos_iff.2 h
  have hπ : 0 < Real.pi := Real.pi_pos
  unfold period
  rw [discrEta ω₁ τ h, areaEq ω₁ τ h]
  have e : ‖(2 * (Real.pi : ℂ) / ω₁) ^ 12 * ModularForm.eta (τ : ℂ) ^ 24‖ =
      ((2 * Real.pi / ‖ω₁‖) ^ 2 * ‖ModularForm.eta (τ : ℂ)‖ ^ 4) ^ 6 := by
    rw [norm_mul, norm_pow, norm_pow, norm_div, norm_mul, Complex.norm_real,
      Real.norm_of_nonneg hπ.le]
    norm_num
    ring
  have hx : 0 ≤ (2 * Real.pi / ‖ω₁‖) ^ 2 * ‖ModularForm.eta (τ : ℂ)‖ ^ 4 := by positivity
  rw [e, show ((1 : ℝ) / 6) = ((6 : ℕ) : ℝ)⁻¹ by norm_num, Real.pow_rpow_inv_natCast hx (by norm_num)]
  field_simp
  ring

/- English proof (translation)
Introduce `ω₁ τ c h hc`. Rewrite using `[scale_latt, discrEta _ τ (mul_ne_zero hc h), discrEta ω₁ τ h]`. Rewrite using `[zpow_neg, show (12 : ℤ) = ((12 : ℕ) : ℤ) from rfl, zpow_natCast]`. Clear the denominators using the available nonvanishing facts.
-/
theorem discrScale : DiscrScale := by
  intro ω₁ τ c h hc
  rw [scale_latt, discrEta _ τ (mul_ne_zero hc h), discrEta ω₁ τ h]
  rw [zpow_neg, show (12 : ℤ) = ((12 : ℕ) : ℤ) from rfl, zpow_natCast]
  field_simp

/- English proof (translation)
Establish `h` using `L.hasSum_sumInvPow 0 hn`. Simplify using `only [sub_zero, PeriodPair.sumInvPow_zero] at h`. Establish `h1 : HasSum (((L.lattice : Set ℂ)).indicator (fun w : ℂ => 1 / w ^ n)) (L.G n)`. Rewrite using `[← hasSum_subtype_iff_indicator]`. Simplify using `only [one_div]`.

Conclude with `h`. Establish `h2 : ((L.lattice : Set ℂ)).indicator (fun w : ℂ => 1 / w ^ n) = ({w : ℂ | w ∈ L.lattice.toAddSubgroup ∧ w ≠ 0}).indicator (fun w : ℂ => 1 / w ^ n)`. Use extensionality with `w`. Distinguish the cases in `hw : w = 0`. Substitute `hw` using the available equality.

Simplify using `[Set.indicator, zero_pow (by omega : n ≠ 0)]`. Establish `e : (w ∈ (L.lattice : Set ℂ)) ↔ (w ∈ L.lattice.toAddSubgroup ∧ w ≠ 0)` using `⟨fun h => ⟨h, hw⟩, fun h => h.1⟩`. Simplify using `only [Set.indicator]`. Conclude with `if_congr e rfl rfl`. Rewrite `h1` using `[h2, ← hasSum_subtype_iff_indicator]`.

Conclude with `h1`.
-/
theorem hasSum_G (L : PeriodPair) {n : ℕ} (hn : 2 < n) :
    HasSum (fun w : {w : ℂ // w ∈ L.lattice.toAddSubgroup ∧ w ≠ 0} => 1 / (w : ℂ) ^ n) (L.G n) := by
  have h := L.hasSum_sumInvPow 0 hn
  simp only [sub_zero, PeriodPair.sumInvPow_zero] at h
  have h1 : HasSum (((L.lattice : Set ℂ)).indicator (fun w : ℂ => 1 / w ^ n)) (L.G n) := by
    rw [← hasSum_subtype_iff_indicator]
    simp only [one_div]
    exact h
  have h2 : ((L.lattice : Set ℂ)).indicator (fun w : ℂ => 1 / w ^ n) =
      ({w : ℂ | w ∈ L.lattice.toAddSubgroup ∧ w ≠ 0}).indicator (fun w : ℂ => 1 / w ^ n) := by
    ext w
    by_cases hw : w = 0
    · subst hw
      simp [Set.indicator, zero_pow (by omega : n ≠ 0)]
    · classical
      have e : (w ∈ (L.lattice : Set ℂ)) ↔ (w ∈ L.lattice.toAddSubgroup ∧ w ≠ 0) :=
        ⟨fun h => ⟨h, hw⟩, fun h => h.1⟩
      simp only [Set.indicator]
      exact if_congr e rfl rfl
  rw [h2, ← hasSum_subtype_iff_indicator] at h1
  exact h1

/- English proof (translation)
Introduce `L`. Establish `hk : ∀ k : ℕ, 2 ≤ k → (Summable (fun w : {w : ℂ // w ∈ L.lattice.toAddSubgroup ∧ w ≠ 0} => 1 / (w : ℂ) ^ (2 * k)) ∧ eisG L.lattice.toAddSubgroup k = L.G (2 * k))`. Introduce `k hk`. Establish `h` using `hasSum_G L (n := 2 * k) (by omega)`. Conclude with `⟨h.summable, h.tsum_eq⟩`.

Use `⟨hk, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[g2, PeriodPair.g₂, (hk 2 le_rfl).2]`. Rewrite using `[g3, PeriodPair.g₃, (hk 3 (by norm_num)).2]`.
-/
theorem agreePeriodPair : AgreePeriodPair := by
  intro L
  have hk : ∀ k : ℕ, 2 ≤ k →
      (Summable (fun w : {w : ℂ // w ∈ L.lattice.toAddSubgroup ∧ w ≠ 0} => 1 / (w : ℂ) ^ (2 * k)) ∧
      eisG L.lattice.toAddSubgroup k = L.G (2 * k)) := by
    intro k hk
    have h := hasSum_G L (n := 2 * k) (by omega)
    exact ⟨h.summable, h.tsum_eq⟩
  refine ⟨hk, ?_, ?_⟩
  · rw [g2, PeriodPair.g₂, (hk 2 le_rfl).2]
  · rw [g3, PeriodPair.g₃, (hk 3 (by norm_num)).2]

/- English proof (translation)
Assemble the required witnesses or components as `⟨discrEta, areaEq, periodEta, discrScale, agreePeriodPair⟩`.
-/
theorem latticePeriodEta : LatticePeriodEta :=
  ⟨discrEta, areaEq, periodEta, discrScale, agreePeriodPair⟩

end GlobalTheory.LatticePeriodEtaProof

import Formalism.SharpRestriction.CuspSpanNormBounds.FrobeniusCoefficientMemLp.LemmaJ

open MeasureTheory
open scoped ENNReal

noncomputable section

namespace Formalism.MainNotions.S.Pv.LemmaJ

open Formalism.BasicNotions Formalism.QuantumDeterminants Formalism.MainNotions.S Formalism.MainNotions.S.Bridge Formalism.MainNotions.S.ThB

def AmpUnif : Prop :=
  ∀ Cg cb Cu cT CT C0 C1 : ℝ, ∃ Ca : ℝ, 0 ≤ Ca ∧ ∃ C'₀ Cl₀ : ℝ, ∀ C' Cl : ℝ, C'₀ ≤ C' → Cl₀ ≤ Cl →
    ∀ (D : D7) (large₂ : SizeData₂ D), AmpIsBessel D large₂ C' Cl Cg cb Cu cT CT C0 0 C1 Ca

def AmpOrbU : Prop :=
  ∀ Cg cb Cu cT CT C0 : ℝ, ∃ C'₀ Cl₀ : ℝ, ∀ C' Cl : ℝ, C'₀ ≤ C' → Cl₀ ≤ Cl →
    ∀ (D : D7) (large₂ : SizeData₂ D), AmpOrb D large₂ C' Cl Cg cb Cu cT CT C0 0

def OrbEq (D : D7) {τ : D.what₂.Tau} {w w' : D.what₂.Word} {θ : ℝ} {W : LocW D.R.k D.R.rS}
    {lam' : Fin (2 * D.R.rS + D.R.k + 1) → ℝ} {A : LocS W} (hW : GoodW D τ w w' θ W) (hA : GoodS D lam' A)
    (hT : 0 < Tr D w) (hT' : 0 < Tr D w')
    (f : MatKR D.R.k D.R.rS →
      ((toBessel D τ w w' θ W lam' A hW hA hT hT').Wq →L[ℂ] (toBessel D τ w w' θ W lam' A hW hA hT hT').Wp)) : Prop :=
  ∀ γ : MatKR D.R.k D.R.rS, γ ∈ UH (Hpk D.R.k D.R.rS) → 0 < Gf D.R.k D.R.rS W.z W.z' γ →
    Formalism.FourierDecayAlt.C2.IsMonomial (Formalism.QuantumDeterminants.Zhat D.R.k D.R.rS W.z W.z' γ) →
    IsRelStab (toBessel D τ w w' θ W lam' A hW hA hT hT') γ →
    ∀ (μR νR : Measure (Mt D.R.k D.R.rS)) (ν : Measure (PairSp D.R.k D.R.rS)),
      IsHaarOn (RStab D.R.k D.R.rS γ) μR →
      IsOrbQuot (toBessel D τ w w' θ W lam' A hW hA hT hT') γ μR ν →
      IsQuotMeas W.μG (μR.map (fun x => fun i j => (γ⁻¹ * Matrix.of x * γ) i j)) νR →
      A.J νR γ = OrbInt (toBessel D τ w w' θ W lam' A hW hA hT hT') f γ ν

def BigCellEq : Prop :=
  ∀ (D : D7) (τ : D.what₂.Tau) (w w' : D.what₂.Word) (θ : ℝ) (W : LocW D.R.k D.R.rS) (hW : GoodW D τ w w' θ W)
    (lam' : Fin (2 * D.R.rS + D.R.k + 1) → ℝ) (A : LocS W) (hA : GoodS D lam' A) (hT : 0 < Tr D w) (hT' : 0 < Tr D w')
    (f : MatKR D.R.k D.R.rS →
      ((toBessel D τ w w' θ W lam' A hW hA hT hT').Wq →L[ℂ] (toBessel D τ w w' θ W lam' A hW hA hT hT').Wp)),
    OrbEq D hW hA hT hT' f →
    ∀ μsec, IsSection D.R.k D.R.rS W.z W.z' μsec →
      jNorm2 (toBessel D τ w w' θ W lam' A hW hA hT hT') f μsec = MMv D w w' A μsec

def RootCmp : Prop :=
  ∀ (D : D7) (τ : D.what₂.Tau) (w w' : D.what₂.Word) (θ : ℝ) (W : LocW D.R.k D.R.rS) (hW : GoodW D τ w w' θ W)
    (lam' : Fin (2 * D.R.rS + D.R.k + 1) → ℝ) (A : LocS W) (hA : GoodS D lam' A) (hT : 0 < Tr D w) (hT' : 0 < Tr D w')
    (γ : MatKR D.R.k D.R.rS) (p : Point ℂ (D.R.rS + 1)), RelPt D W.z W.z' γ p →
    ∀ (θ' : ℝ), 0 < θ' → ∀ νR : Measure (Mt D.R.k D.R.rS), RMeas D W γ θ' νR →
      ∃ (g₀ : MatKR D.R.k D.R.rS) (μR νR₀ : Measure (Mt D.R.k D.R.rS)) (ν : Measure (PairSp D.R.k D.R.rS)),
        IsPtRepO (toBessel D τ w w' θ W lam' A hW hA hT hT') p g₀ ∧
        0 < Gf D.R.k D.R.rS W.z W.z' g₀ ∧ Formalism.FourierDecayAlt.C2.IsMonomial (Formalism.QuantumDeterminants.Zhat D.R.k D.R.rS W.z W.z' g₀) ∧
        IsRelStab (toBessel D τ w w' θ W lam' A hW hA hT hT') g₀ ∧
        IsRootMeas (toBessel D τ w w' θ W lam' A hW hA hT hT') p g₀ μR ∧
        IsHaarOn (RStab D.R.k D.R.rS g₀) μR ∧ IsOrbQuot (toBessel D τ w w' θ W lam' A hW hA hT hT') g₀ μR ν ∧
        IsQuotMeas W.μG (μR.map (fun x => fun i j => (g₀⁻¹ * Matrix.of x * g₀) i j)) νR₀ ∧
        ENNReal.ofReal (hsNormSq (A.J νR γ)) ≤ ENNReal.ofReal (θ' ^ (-(2 : ℤ))) * ENNReal.ofReal (hsNormSq (A.J νR₀ g₀))

def AmpNZ : Prop :=
  ∀ Cg cb Cu cT CT C0 : ℝ, ∃ C'₀ Cl₀ : ℝ, ∀ C' Cl : ℝ, C'₀ ≤ C' → Cl₀ ≤ Cl → ∀ (D : D7) (large₂ : SizeData₂ D),
    Cnt.Hyp0 D large₂ C' Cl Cg cb Cu cT CT C0 →
    ∀ τ w w', HypTT D w w' → ∀ θ (W : LocW D.R.k D.R.rS), GoodW D τ w w' θ W →
    ∀ (A : LocS W), GoodS D (lamD D τ) A → 0 < Tr D w → 0 < Tr D w' →
    ∀ μsec, IsSection D.R.k D.R.rS W.z W.z' μsec → MMv D w w' A μsec ≠ 0

/- English proof (translation)
Unfold `l1dist at h`. Establish `h0 : ∑ i, |x i - y i| = 0` using `le_antisymm h (Finset.sum_nonneg fun i _ => abs_nonneg _)`. Rewrite `h0` using `[Finset.sum_eq_zero_iff_of_nonneg (fun i _ => abs_nonneg _)]`. Use function extensionality and compare the values at `i`. Use `h0 i (Finset.mem_univ i)` as an intermediate fact.

Rewrite `this` using `[abs_eq_zero, sub_eq_zero]`. Conclude with `this`.
-/
theorem l1dist_zero {N : ℕ} {x y : Fin N → ℝ} (h : l1dist x y ≤ 0) : x = y := by
  unfold l1dist at h
  have h0 : ∑ i, |x i - y i| = 0 := le_antisymm h (Finset.sum_nonneg fun i _ => abs_nonneg _)
  rw [Finset.sum_eq_zero_iff_of_nonneg (fun i _ => abs_nonneg _)] at h0
  funext i
  have := h0 i (Finset.mem_univ i)
  rw [abs_eq_zero, sub_eq_zero] at this
  exact this

/- English proof (translation)
Establish `hb0 : 0 < b` using `by linarith`. Establish `hp : 0 < b ^ (-(C1 * m ^ 2))` using `Real.rpow_pos_of_pos hb0 _`. Establish `hθ0 : 0 < θ'` using `lt_of_lt_of_le hp hθ`. Rewrite using `[one_mul, zpow_neg, zpow_two]`. Establish `hsq : b ^ (-(C1 * m ^ 2)) * b ^ (-(C1 * m ^ 2)) ≤ θ' * θ'` using `mul_le_mul hθ hθ hp.le hθ0.le`.

Establish `hinv : (θ' * θ')⁻¹ ≤ (b ^ (-(C1 * m ^ 2)) * b ^ (-(C1 * m ^ 2)))⁻¹` using `inv_anti₀ (mul_pos hp hp) hsq`. Establish `heq : (b ^ (-(C1 * m ^ 2)) * b ^ (-(C1 * m ^ 2)))⁻¹ = b ^ (2 * C1 * m ^ 2)`. Rewrite using `[← Real.rpow_add hb0, ← Real.rpow_neg hb0.le]`. Put the polynomial expressions in normal form. Establish `hmono : b ^ (2 * C1 * m ^ 2) ≤ b ^ (Ca * m ^ 2)`.

Apply `Real.rpow_le_rpow_of_exponent_le hb` to reduce the goal to its premises. Establish `: 0 ≤ m ^ 2` using `sq_nonneg m`. Use the polynomial consequences of the given equalities and inequalities. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem window_pow {b θ' C1 Ca m : ℝ} (hb : 1 ≤ b) (hθ : b ^ (-(C1 * m ^ 2)) ≤ θ') (hCa : 2 * C1 ≤ Ca) :
    θ' ^ (-(2 : ℤ)) ≤ 1 * b ^ (Ca * m ^ 2) := by
  have hb0 : 0 < b := by linarith
  have hp : 0 < b ^ (-(C1 * m ^ 2)) := Real.rpow_pos_of_pos hb0 _
  have hθ0 : 0 < θ' := lt_of_lt_of_le hp hθ
  rw [one_mul, zpow_neg, zpow_two]
  have hsq : b ^ (-(C1 * m ^ 2)) * b ^ (-(C1 * m ^ 2)) ≤ θ' * θ' := mul_le_mul hθ hθ hp.le hθ0.le
  have hinv : (θ' * θ')⁻¹ ≤ (b ^ (-(C1 * m ^ 2)) * b ^ (-(C1 * m ^ 2)))⁻¹ :=
    inv_anti₀ (mul_pos hp hp) hsq
  have heq : (b ^ (-(C1 * m ^ 2)) * b ^ (-(C1 * m ^ 2)))⁻¹ = b ^ (2 * C1 * m ^ 2) := by
    rw [← Real.rpow_add hb0, ← Real.rpow_neg hb0.le]
    ring_nf
  have hmono : b ^ (2 * C1 * m ^ 2) ≤ b ^ (Ca * m ^ 2) := by
    apply Real.rpow_le_rpow_of_exponent_le hb
    have : 0 ≤ m ^ 2 := sq_nonneg m
    nlinarith
  linarith

/- English proof (translation)
Introduce `Cg cb Cu cT CT C0 C1`. Take `⟨C'a, Cla, hAO'⟩` from `hAO Cg cb Cu cT CT C0`. Take `⟨C'n, Cln, hNZ'⟩` from `hNZ Cg cb Cu cT CT C0`. Use `⟨max 0 (2 * C1), le_max_left _ _, max C'a C'n, max (max Cla Cln) 1000, ?_⟩` and prove the remaining obligations. Introduce `C' Cl hC' hCl D large₂ hH τ w w' hTT θ hθ W hW lam' hlam A hA hT hT'`.

Establish `hCla : Cla ≤ Cl` using `le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hCl`. Establish `hCln : Cln ≤ Cl` using `le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hCl`. Establish `h1000 : (1000 : ℝ) ≤ Cl` using `le_trans (le_max_right _ _) hCl`. Establish `hC'a : C'a ≤ C'` using `le_trans (le_max_left _ _) hC'`. Establish `hC'n : C'n ≤ C'` using `le_trans (le_max_right _ _) hC'`.

Establish `hb : 1 ≤ large₂.sc.b`. Unfold `Formalism.BasicNotions.Scale.b Formalism.BasicNotions.Scale.L`. Conclude with `Real.one_le_exp (Real.rpow_nonneg (by linarith [large₂.sc.one_lt_alt]) _)`. Establish `hl : lam' = lamD D τ` using `l1dist_zero (by simpa using hlam)`. Substitute `hl` using the available equality.

Establish `hl0 : l1dist (lamD D τ) (lamD D τ) ≤ 0 * (D.R.k : ℝ) * (D.R.m : ℝ) ^ 3`. Simplify using `[l1dist]`. Take `⟨f, hf, horb⟩` from `hAO' C' Cl hC'a hCla D large₂ hH h1000 (by linarith) τ w w' hTT θ W hW (lamD D τ) hl0 A hA hT hT'`. Establish `hOE : OrbEq D hW hA hT hT' f` using `horb`. Use `⟨f, 1, one_pos, hf, ?_, ?_⟩` and prove the remaining obligations.

Introduce `μsec hsec`. Establish `hBC'` using `hBC D τ w w' θ W hW (lamD D τ) A hA hT hT' f hOE μsec hsec`. Establish `hnz` using `hNZ' C' Cl hC'n hCln D large₂ hH τ w w' hTT θ W hW A hA hT hT' μsec hsec`. Use `⟨by rw [hBC']; exact hnz, ?_⟩` and prove the remaining obligations. Rewrite using `[hBC', ENNReal.ofReal_one, one_mul]`.

Introduce `γ p hp θ' hθ' νR hνR`. Establish `hθ'0 : 0 < θ'` using `lt_of_lt_of_le (Real.rpow_pos_of_pos (by linarith) _) hθ'.1`. Take `⟨g₀, μR, νR₀, ν, hrep, hG, hmono, hrel, hroot, hhaar, hquot, hqm, hle⟩` from `hRC D τ w w' θ W hW (lamD D τ) A hA hT hT' γ p hp θ' hθ'0 νR hνR`. Establish `hJ` using `hOE g₀ ?_ hG hmono hrel μR νR₀ ν hhaar hquot hqm`. Use `le_trans hle (mul_le_mul' (ENNReal.ofReal_le_ofReal (window_pow hb hθ'.1 (le_max_right _ _))) ?_)` and prove the remaining obligations.

Rewrite using `[hJ]`. Conclude with `le_iSup_of_le g₀ (le_iSup_of_le μR (le_iSup_of_le ν (le_iSup_of_le ⟨hrep, hrel, hroot, hquot⟩ le_rfl)))`. Conclude with `hrep.1`.
-/
theorem ampUnif_of (hAO : AmpOrbU) (hBC : BigCellEq) (hRC : RootCmp) (hNZ : AmpNZ) : AmpUnif := by
  intro Cg cb Cu cT CT C0 C1
  obtain ⟨C'a, Cla, hAO'⟩ := hAO Cg cb Cu cT CT C0
  obtain ⟨C'n, Cln, hNZ'⟩ := hNZ Cg cb Cu cT CT C0
  refine ⟨max 0 (2 * C1), le_max_left _ _, max C'a C'n, max (max Cla Cln) 1000, ?_⟩
  intro C' Cl hC' hCl D large₂ hH τ w w' hTT θ hθ W hW lam' hlam A hA hT hT'
  have hCla : Cla ≤ Cl := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hCl
  have hCln : Cln ≤ Cl := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hCl
  have h1000 : (1000 : ℝ) ≤ Cl := le_trans (le_max_right _ _) hCl
  have hC'a : C'a ≤ C' := le_trans (le_max_left _ _) hC'
  have hC'n : C'n ≤ C' := le_trans (le_max_right _ _) hC'
  have hb : 1 ≤ large₂.sc.b := by
    unfold Formalism.BasicNotions.Scale.b Formalism.BasicNotions.Scale.L
    exact Real.one_le_exp (Real.rpow_nonneg (by linarith [large₂.sc.one_lt_alt]) _)
  have hl : lam' = lamD D τ := l1dist_zero (by simpa using hlam)
  subst hl
  have hl0 : l1dist (lamD D τ) (lamD D τ) ≤ 0 * (D.R.k : ℝ) * (D.R.m : ℝ) ^ 3 := by
    simp [l1dist]
  obtain ⟨f, hf, horb⟩ := hAO' C' Cl hC'a hCla D large₂ hH h1000 (by linarith) τ w w' hTT θ W hW (lamD D τ) hl0
    A hA hT hT'
  have hOE : OrbEq D hW hA hT hT' f := horb
  refine ⟨f, 1, one_pos, hf, ?_, ?_⟩
  · intro μsec hsec
    have hBC' := hBC D τ w w' θ W hW (lamD D τ) A hA hT hT' f hOE μsec hsec
    have hnz := hNZ' C' Cl hC'n hCln D large₂ hH τ w w' hTT θ W hW A hA hT hT' μsec hsec
    refine ⟨by rw [hBC']; exact hnz, ?_⟩
    rw [hBC', ENNReal.ofReal_one, one_mul]
  · intro γ p hp θ' hθ' νR hνR
    have hθ'0 : 0 < θ' := lt_of_lt_of_le (Real.rpow_pos_of_pos (by linarith) _) hθ'.1
    obtain ⟨g₀, μR, νR₀, ν, hrep, hG, hmono, hrel, hroot, hhaar, hquot, hqm, hle⟩ :=
      hRC D τ w w' θ W hW (lamD D τ) A hA hT hT' γ p hp θ' hθ'0 νR hνR
    have hJ := hOE g₀ ?_ hG hmono hrel μR νR₀ ν hhaar hquot hqm
    · refine le_trans hle (mul_le_mul' (ENNReal.ofReal_le_ofReal
        (window_pow hb hθ'.1 (le_max_right _ _))) ?_)
      rw [hJ]
      exact le_iSup_of_le g₀ (le_iSup_of_le μR (le_iSup_of_le ν
        (le_iSup_of_le ⟨hrep, hrel, hroot, hquot⟩ le_rfl)))
    · exact hrep.1

end Formalism.MainNotions.S.Pv.LemmaJ

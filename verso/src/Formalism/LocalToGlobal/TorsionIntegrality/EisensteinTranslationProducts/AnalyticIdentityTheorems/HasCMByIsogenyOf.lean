import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.EisensteinS2LimitFormula
import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.QuasiPeriodConstIsogeny

noncomputable section
open scoped BigOperators ComplexConjugate
open Formalism.L2.Th1.CM (omegaK HasCMBy)

namespace Formalism.L2.Th1.F

namespace CmBy

/- English proof (translation)
Simplify using the standard rewrite rules. Expand and normalize the polynomial expressions, which then agree.
-/
private lemma re_add_mul_omegaK (d : ℕ) (m n : ℤ) :
    ((m : ℂ) + (n : ℂ) * omegaK d).re = (m : ℝ) + (n : ℝ) / 2 := by
  simp [omegaK]
  ring

/- English proof (translation)
Simplify using the standard rewrite rules. Expand and normalize the polynomial expressions, which then agree.
-/
private lemma im_add_mul_omegaK (d : ℕ) (m n : ℤ) :
    ((m : ℂ) + (n : ℂ) * omegaK d).im = (n : ℝ) * Real.sqrt d / 2 := by
  simp [omegaK]
  ring

/- English proof (translation)
Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Take a linear combination of the given relations to obtain the conclusion.
-/
lemma normSq_omega (d : ℕ) (m n : ℤ) :
    Complex.normSq ((m : ℂ) + (n : ℂ) * omegaK d)
      = (m : ℝ) ^ 2 + (m : ℝ) * (n : ℝ) + (n : ℝ) ^ 2 * ((1 + (d : ℝ)) / 4) := by
  have hs : Real.sqrt (d : ℝ) * Real.sqrt d = d := Real.mul_self_sqrt (Nat.cast_nonneg d)
  rw [Complex.normSq_apply, re_add_mul_omegaK, im_add_mul_omegaK]
  linear_combination ((n : ℝ) ^ 2 / 4) * hs

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Rewrite the indicated hypotheses using the stated equalities.

Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Separate the alternatives or extract the components of the hypothesis. Combine the linear equalities and inequalities to obtain the conclusion.

Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. A detailed English derivation is pending.
-/
lemma ne_zero (d : ℕ) (hd : 0 < d) (m n : ℤ) (h : (m, n) ≠ (0, 0)) :
    (m : ℂ) + (n : ℂ) * omegaK d ≠ 0 := by
  intro h0
  have hre := re_add_mul_omegaK d m n
  have him := im_add_mul_omegaK d m n
  rw [h0, Complex.zero_re] at hre
  rw [h0, Complex.zero_im] at him
  have hs : 0 < Real.sqrt (d : ℝ) := Real.sqrt_pos.mpr (by exact_mod_cast hd)
  have hn : (n : ℝ) = 0 := by
    have h2 : (n : ℝ) * Real.sqrt d = 0 := by linarith
    rcases mul_eq_zero.mp h2 with h1 | h1
    · exact h1
    · linarith
  have hm : (m : ℝ) = 0 := by rw [hn] at hre; linarith
  have hn' : n = 0 := by exact_mod_cast hn
  have hm' : m = 0 := by exact_mod_cast hm
  exact h (by rw [hm', hn'])

end CmBy

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Reduce the conclusion to the remaining proof obligations. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Establish an intermediate fact.

Simplify using the standard rewrite rules. Expand and normalize the polynomial expressions, which then agree. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem has_cm_stable : HasCMByStable := by
  intro d L hL m n
  refine ⟨?_, CmBy.normSq_omega d m n⟩
  intro w hw
  have h1 : omegaK d * w ∈ L.lattice := hL w hw
  have he : ((m : ℂ) + (n : ℂ) * omegaK d) * w = m • w + n • (omegaK d * w) := by
    simp only [zsmul_eq_mul]; ring
  rw [he]
  exact L.lattice.add_mem (L.lattice.smul_mem m hw) (L.lattice.smul_mem n h1)

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Rewrite the hypotheses and the conclusion using the stated equalities. Rewrite the hypotheses and the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem hasCMByScale_of (h : Homogeneity) : HasCMByScale := by
  intro d L c hc hL w hw
  have hmem := (h L c hc).1
  rw [hmem] at hw ⊢
  rw [show c⁻¹ * (omegaK d * w) = omegaK d * (c⁻¹ * w) by ring]
  exact hL _ hw

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Substitute using the available equality. Establish an intermediate fact. Establish an intermediate fact.

Simplify using the standard rewrite rules. Move the embeddings inside the algebraic operations. Expand and normalize the polynomial expressions, which then agree. Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities.

A detailed English derivation is pending.
-/
theorem cmPairHasCMBy_of (h : CmStable) : CmPairHasCMBy := by
  intro a b c d ha hd hdisc hb
  obtain ⟨k, hk⟩ := hb
  subst hk
  have hst := h a (2 * k + 1) c d ha hd hdisc (-k) 1
  have heq : omegaK d = ((-k : ℤ) : ℂ) + ((1 : ℤ) : ℂ) * cmTheta (2 * k + 1) d := by
    simp only [omegaK, cmTheta]
    push_cast
    ring
  intro w hw
  rw [heq]
  exact hst w hw

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Supply the required witnesses or components.
-/
theorem hasCMByIsogeny_of (hs : HasCMByStable) (he : KerRepsExist) (hc : KerRepsCard)
    (hf : IsogenyFormulaInstance) (h2 : QuasiPeriodConstIsogeny) : HasCMByIsogeny := by
  intro d L hL m n hmn hd
  have hα0 := CmBy.ne_zero d hd m n hmn
  obtain ⟨hms, hnorm⟩ := hs d L hL m n
  obtain ⟨S, hS⟩ := he L _ hα0 hms
  exact ⟨S, hS, (hc L _ S hα0 hms hS).trans hnorm, hf L _ S hα0 hms hS, h2 L _ S hα0 hms hS⟩

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Simplify using the standard rewrite rules. Establish an intermediate fact. Establish an intermediate fact.

Establish an intermediate fact. Rewrite the hypotheses and the conclusion using the stated equalities.
-/
theorem jInvScale_of (h : Homogeneity) : JInvScale := by
  intro L c hc
  obtain ⟨-, -, -, -, -, -, -, -, -, hg2, hg3⟩ := h L c hc
  simp only [Formalism.L2.Th1.CM.jInv, hg2, hg3]
  have hc12 : (c ^ 12)⁻¹ ≠ 0 := inv_ne_zero (pow_ne_zero _ hc)
  have e1 : ((c ^ 4)⁻¹ * L.g₂) ^ 3 = (c ^ 12)⁻¹ * L.g₂ ^ 3 := by ring
  have e2 : ((c ^ 6)⁻¹ * L.g₃) ^ 2 = (c ^ 12)⁻¹ * L.g₃ ^ 2 := by ring
  rw [e1, e2, show (1728 : ℂ) * ((c ^ 12)⁻¹ * L.g₂ ^ 3) = (c ^ 12)⁻¹ * (1728 * L.g₂ ^ 3) by ring,
    show (c ^ 12)⁻¹ * L.g₂ ^ 3 - 27 * ((c ^ 12)⁻¹ * L.g₃ ^ 2)
      = (c ^ 12)⁻¹ * (L.g₂ ^ 3 - 27 * L.g₃ ^ 2) by ring,
    mul_div_mul_left _ _ hc12]

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem has_cm_scale : HasCMByScale := hasCMByScale_of homogeneity

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem cm_pair_has_cm : CmPairHasCMBy := cmPairHasCMBy_of cmStable

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem hasCMByIsogeny_of' (hf : IsogenyFormulaInstance) : HasCMByIsogeny :=
  hasCMByIsogeny_of has_cm_stable kerRepsExist kerRepsCard hf quasiPeriodConstIsogeny

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem j_invariant_scale : JInvScale := jInvScale_of homogeneity

end Formalism.L2.Th1.F

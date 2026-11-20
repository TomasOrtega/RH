import Mathlib
import Formalism.PeriodIntegrals.IdealLattice
import Formalism.PeriodIntegrals.AreaLat
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.IdealLatticeBasis.IdealBasisAlt
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.AreaLat

open NumberField

namespace PI.IdealLatticeWork

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Supply the required witnesses or components.
-/
theorem okBasis : OKBasis := by
  intro K _ _ h
  exact ⟨Module.finBasisOfFinrankEq ℤ (𝓞 K) (by rw [NumberField.RingOfIntegers.rank, h])⟩

/- English proof (translation)
Simplify using the standard rewrite rules. Move the embeddings inside the algebraic operations. Expand and normalize the polynomial expressions, which then agree.
-/
theorem im_comb (u v : ℂ) (p q r s : ℤ) :
    ((starRingEnd ℂ) ((p : ℂ) * u + (q : ℂ) * v) * ((r : ℂ) * u + (s : ℂ) * v)).im
      = ((p * s - q * r : ℤ) : ℝ) * ((starRingEnd ℂ) u * v).im := by
  simp only [map_add, map_mul, map_intCast, Complex.mul_im, Complex.mul_re,
    Complex.add_im, Complex.add_re, Complex.intCast_re, Complex.intCast_im, Complex.conj_re,
    Complex.conj_im]
  push_cast
  ring

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Expand and normalize the polynomial expressions, which then agree.
-/
theorem im_scale (δ x y : ℂ) :
    ((starRingEnd ℂ) (δ * x) * (δ * y)).im = ‖δ‖ ^ 2 * ((starRingEnd ℂ) x * y).im := by
  rw [Complex.sq_norm, Complex.normSq_apply]
  simp only [map_mul, Complex.mul_im, Complex.mul_re, Complex.conj_re, Complex.conj_im]
  ring

/- English proof (translation)
Simplify using the standard rewrite rules.
-/
theorem phi_comb {K : Type} [Field K] [NumberField K] (φ : K →+* ℂ) (m n : ℤ) (x y : 𝓞 K) :
    φ ((m • x + n • y : 𝓞 K) : K) = (m : ℂ) * φ (x : K) + (n : ℂ) * φ (y : K) := by
  simp [zsmul_eq_mul]

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Establish an intermediate fact. Reduce the claim to the hypotheses of an applicable result.

Rewrite the conclusion using the stated equalities. Assume the hypotheses and unpack their components. Extract witnesses or component facts from the available result. Rewrite the conclusion using the stated equalities. Establish an intermediate fact.

Simplify using the standard rewrite rules. Expand and normalize the polynomial expressions, which then agree. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses.

Separate the alternatives or extract the components of the hypothesis. Establish an intermediate fact. Assume the hypotheses and unpack their components. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.

Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Use the resulting assumption.

Establish an intermediate fact. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Expand and normalize the polynomial expressions, which then agree. Establish an intermediate fact.

Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Rewrite the indicated hypotheses using the stated equalities. Combine the linear equalities and inequalities to obtain the conclusion. Reduce the conclusion to the remaining proof obligations.

Rewrite the conclusion using the stated equalities. Express the relevant assertion in an equivalent form by its definition. Rewrite the conclusion using the stated equalities. Expand and normalize the polynomial expressions, which then agree. A detailed English derivation is pending.
-/
theorem assemble : Assemble := by
  intro hA hI hB hL K _ _ φ h2 hcx cc δ hcc hδ
  obtain ⟨b⟩ := hB K h2
  obtain ⟨c₁, hc₁, c₂, hc₂, hspan, p, q, r, s, hc1, hc2, hdet⟩ := hI K b cc hcc
  have hgen : AddSubgroup.closure {w | ∃ c ∈ cc, w = δ * φ (c : K)} =
      AddSubgroup.closure {δ * φ (c₁ : K), δ * φ (c₂ : K)} := by
    apply le_antisymm
    · rw [AddSubgroup.closure_le]
      rintro w ⟨c, hc, rfl⟩
      obtain ⟨m, n, rfl⟩ := hspan c hc
      rw [phi_comb φ m n c₁ c₂]
      have e : δ * ((m : ℂ) * φ (c₁ : K) + (n : ℂ) * φ (c₂ : K)) =
          m • (δ * φ (c₁ : K)) + n • (δ * φ (c₂ : K)) := by
        simp only [zsmul_eq_mul]
        ring
      rw [e]
      exact AddSubgroup.add_mem _
        (AddSubgroup.zsmul_mem _ (AddSubgroup.subset_closure (by simp)) m)
        (AddSubgroup.zsmul_mem _ (AddSubgroup.subset_closure (by simp)) n)
    · rw [AddSubgroup.closure_le]
      intro w hw
      rcases hw with rfl | rfl
      · exact AddSubgroup.subset_closure ⟨c₁, hc₁, rfl⟩
      · exact AddSubgroup.subset_closure ⟨c₂, hc₂, rfl⟩
  have hφc : ∀ c : 𝓞 K, ∀ x y : ℤ, c = x • b 0 + y • b 1 →
      φ (c : K) = (x : ℂ) * φ (b 0 : K) + (y : ℂ) * φ (b 1 : K) := by
    rintro c x y rfl
    exact phi_comb φ x y (b 0) (b 1)
  have him : ((starRingEnd ℂ) (δ * φ (c₁ : K)) * (δ * φ (c₂ : K))).im =
      ‖δ‖ ^ 2 * (((p * s - q * r : ℤ) : ℝ) * ((starRingEnd ℂ) (φ (b 0 : K)) * φ (b 1 : K)).im) := by
    rw [im_scale, hφc c₁ p q hc1, hφc c₂ r s hc2, im_comb]
  have hA' := hA K φ h2 hcx b
  have hd : (0 : ℝ) < Real.sqrt |(NumberField.discr K : ℝ)| / 2 := by
    have h0 : (NumberField.discr K : ℝ) ≠ 0 := by exact_mod_cast NumberField.discr_ne_zero K
    exact div_pos (Real.sqrt_pos.mpr (abs_pos.mpr h0)) two_pos
  have hn : Ideal.absNorm cc ≠ 0 := by
    rwa [Ne, Ideal.absNorm_eq_zero_iff]
  have hδ2 : (0 : ℝ) < ‖δ‖ ^ 2 := pow_pos (norm_pos_iff.mpr hδ) 2
  have habs : |((starRingEnd ℂ) (δ * φ (c₁ : K)) * (δ * φ (c₂ : K))).im| =
      ‖δ‖ ^ 2 * (Ideal.absNorm cc : ℝ) * (Real.sqrt |(NumberField.discr K : ℝ)| / 2) := by
    rw [him, abs_mul, abs_mul, hA', abs_of_pos hδ2, ← hdet, Nat.cast_natAbs, Int.cast_abs]
    ring
  have hpos : (0 : ℝ) < ‖δ‖ ^ 2 * (Ideal.absNorm cc : ℝ) * (Real.sqrt |(NumberField.discr K : ℝ)| / 2) :=
    mul_pos (mul_pos hδ2 (by exact_mod_cast Nat.pos_of_ne_zero hn)) hd
  have hne : ((starRingEnd ℂ) (δ * φ (c₁ : K)) * (δ * φ (c₂ : K))).im ≠ 0 := by
    intro h0
    rw [h0, abs_zero] at habs
    linarith
  refine ⟨⟨δ * φ (c₁ : K), δ * φ (c₂ : K), hne, hgen⟩, ?_⟩
  rw [hgen]
  change area (PI.lat2 _ _) = _
  rw [(hL _ _ hne).1, habs]
  ring

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem idealLattice_of (h1 : OKArea) (h2 : IdealBasis) : PI.IdealLattice :=
  assemble h1 h2 okBasis area_lattice_formula

end PI.IdealLatticeWork

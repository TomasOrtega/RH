import Mathlib
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ModDefs

noncomputable section
open scoped BigOperators Classical UpperHalfPlane MatrixGroups CongruenceSubgroup Manifold
open ModularForm EisensteinSeries ModularFormClass UpperHalfPlane Formalism.L2.Th1.CM

namespace ReciprocityTheory.ChartRestriction.L1

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Prove the components needed by the constructor for the conclusion. Assume the hypotheses and unpack their components. Rewrite the indicated hypotheses using the stated equalities. Supply the required witnesses or components.

Extract witnesses or component facts from the available result. Assume the hypotheses and unpack their components. Simplify using the standard rewrite rules. Establish an intermediate fact. Establish an intermediate fact.

Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Supply the required witnesses or components. Simplify using the standard rewrite rules.
-/
theorem mem_Tm {m : ℕ} (hm : 0 < m) (t : ℕ × ℕ × ℕ) :
    t ∈ Tm m ↔ t.1 * t.2.2 = m ∧ t.2.1 < t.2.2 := by
  rw [Tm, Finset.mem_image]
  constructor
  · rintro ⟨⟨a, b⟩, hx, rfl⟩
    rw [Finset.mem_sigma, Nat.mem_divisors, Finset.mem_range] at hx
    exact ⟨Nat.mul_div_cancel' hx.1.1, hx.2⟩
  · obtain ⟨a, b, e⟩ := t
    rintro ⟨h1, h2⟩
    simp only at h1 h2
    have ha : 0 < a := Nat.pos_of_ne_zero (by rintro rfl; omega)
    have he : m / a = e := by rw [← h1, Nat.mul_div_cancel_left _ ha]
    refine ⟨⟨a, b⟩, ?_, ?_⟩
    · rw [Finset.mem_sigma, Nat.mem_divisors, Finset.mem_range]
      exact ⟨⟨⟨e, h1.symm⟩, hm.ne'⟩, by rw [he]; exact h2⟩
    · simp only [he]

/- English proof (translation)
Establish an intermediate fact. Establish an intermediate fact. Apply the first step, then apply the next step to every resulting obligation. Apply the first step, then apply the next step to every resulting obligation.
-/
theorem Tm_pos {m : ℕ} (hm : 0 < m) {t : ℕ × ℕ × ℕ} (ht : t ∈ Tm m) : 0 < t.1 ∧ 0 < t.2.2 := by
  have h := ((mem_Tm hm t).mp ht).1
  have hpos : 0 < t.1 * t.2.2 := h ▸ hm
  refine ⟨Nat.pos_of_ne_zero fun h0 => ?_, Nat.pos_of_ne_zero fun h0 => ?_⟩ <;>
    rw [h0] at hpos <;> simp at hpos

/- English proof (translation)
Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities.

A detailed English derivation is pending.
-/
theorem pt_coe {a e : ℕ} (ha : 0 < a) (he : 0 < e) (b : ℕ) (τ : ℍ) :
    ((pt a b e τ : ℍ) : ℂ) = ((a : ℂ) * τ + b) / e := by
  have hz : 0 < (((a : ℂ) * τ + b) / e).im := by
    rw [Complex.div_natCast_im]
    simp only [Complex.add_im, Complex.mul_im, Complex.natCast_re, Complex.natCast_im, zero_mul, add_zero,
      UpperHalfPlane.coe_im]
    exact div_pos (mul_pos (by exact_mod_cast ha) τ.im_pos) (by exact_mod_cast he)
  unfold pt
  rw [UpperHalfPlane.ofComplex_apply_of_im_pos hz]

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem DD_ne_zero (τ : ℍ) : DD τ ≠ 0 := by
  exact ModularForm.discriminant_ne_zero τ

/- English proof (translation)
Establish an intermediate fact. A detailed English derivation is pending.
-/
theorem smul_of_form {k : ℤ} (g : ModularForm 𝒮ℒ k) (γ : SL(2, ℤ)) (τ : ℍ) :
    g (γ • τ) = denom γ τ ^ k * g τ := by
  have h := SlashInvariantForm.slash_action_eqn'' g (γ := Matrix.SpecialLinearGroup.mapGL ℝ γ)
    (MonoidHom.mem_range.mpr ⟨γ, rfl⟩) τ
  exact h

/- English proof (translation)
Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Replace the relevant objects with their definitions. Expand and normalize the polynomial expressions, which then agree. A detailed English derivation is pending.
-/
theorem isMF_AA : IsMF 12 AA := by
  refine ⟨ModularForm.mcast (by norm_num) (ModularForm.E₄.mul (ModularForm.E₄.mul ModularForm.E₄)), fun τ => ?_⟩
  show (ModularForm.E₄.mul (ModularForm.E₄.mul ModularForm.E₄)) τ = AA τ
  rw [ModularForm.coe_mul, Pi.mul_apply, ModularForm.coe_mul, Pi.mul_apply]
  unfold AA
  ring

/- English proof (translation)
Treat this case separately. Treat this case separately. A detailed English derivation is pending.
-/
theorem isMF_DD : IsMF 12 DD := by
  first
    | exact ⟨ModularFormClass.modularForm ModularForm.discriminantCuspForm, fun τ => rfl⟩
    | exact ⟨ModularFormClass.modularForm CuspForm.discriminant, fun τ => rfl⟩

/- English proof (translation)
Extract witnesses or component facts from the available result. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem IsMF.smul_eq {k : ℤ} {f : ℍ → ℂ} (h : IsMF k f) (γ : SL(2, ℤ)) (τ : ℍ) :
    f (γ • τ) = denom γ τ ^ k * f τ := by
  obtain ⟨g, hg⟩ := h
  rw [← hg, ← hg]
  exact smul_of_form g γ τ

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem AA_smul (γ : SL(2, ℤ)) (τ : ℍ) : AA (γ • τ) = denom γ τ ^ 12 * AA τ := by
  exact isMF_AA.smul_eq γ τ

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem DD_smul (γ : SL(2, ℤ)) (τ : ℍ) : DD (γ • τ) = denom γ τ ^ 12 * DD τ := by
  exact isMF_DD.smul_eq γ τ

/- English proof (translation)
Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities.
-/
theorem jT_smul (γ : SL(2, ℤ)) (τ : ℍ) : jT (γ • τ) = jT τ := by
  unfold jT
  rw [AA_smul, DD_smul, mul_div_mul_left _ _ (pow_ne_zero _ (UpperHalfPlane.denom_ne_zero _ τ))]

/- English proof (translation)
Substitute using the available equality. A detailed English derivation is pending.
-/
theorem IsMF.congr_weight {k k' : ℤ} {f : ℍ → ℂ} (h : IsMF k f) (hk : k = k') : IsMF k' f := by
  subst hk
  exact h

/- English proof (translation)
Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Supply the required witnesses or components.
-/
theorem IsMF.add {k : ℤ} {f g : ℍ → ℂ} (hf : IsMF k f) (hg : IsMF k g) : IsMF k (fun τ => f τ + g τ) := by
  obtain ⟨f', hf'⟩ := hf
  obtain ⟨g', hg'⟩ := hg
  exact ⟨f' + g', fun τ => by simp [hf', hg']⟩

/- English proof (translation)
Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Supply the required witnesses or components.
-/
theorem IsMF.sub {k : ℤ} {f g : ℍ → ℂ} (hf : IsMF k f) (hg : IsMF k g) : IsMF k (fun τ => f τ - g τ) := by
  obtain ⟨f', hf'⟩ := hf
  obtain ⟨g', hg'⟩ := hg
  exact ⟨f' - g', fun τ => by simp [hf', hg']⟩

/- English proof (translation)
Extract witnesses or component facts from the available result. Supply the required witnesses or components.
-/
theorem IsMF.const_mul {k : ℤ} {f : ℍ → ℂ} (c : ℂ) (hf : IsMF k f) : IsMF k (fun τ => c * f τ) := by
  obtain ⟨f', hf'⟩ := hf
  exact ⟨c • f', fun τ => by simp [hf']⟩

/- English proof (translation)
Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Supply the required witnesses or components.
-/
theorem IsMF.mul {k k' : ℤ} {f g : ℍ → ℂ} (hf : IsMF k f) (hg : IsMF k' g) :
    IsMF (k + k') (fun τ => f τ * g τ) := by
  obtain ⟨f', hf'⟩ := hf
  obtain ⟨g', hg'⟩ := hg
  exact ⟨f'.mul g', fun τ => by rw [ModularForm.coe_mul, Pi.mul_apply, hf', hg']⟩

/- English proof (translation)
Proceed by induction. Treat this case separately. Reduce the conclusion to the remaining proof obligations. Simplify using the standard rewrite rules. Treat this case separately.

Establish an intermediate fact. Simplify to obtain the desired conclusion from the available facts.
-/
theorem IsMF.pow {k : ℤ} {f : ℍ → ℂ} (hf : IsMF k f) (n : ℕ) : IsMF (n * k) (fun τ => f τ ^ n) := by
  induction n with
  | zero =>
    refine IsMF.congr_weight (k := 0) ⟨1, fun τ => ?_⟩ (by simp)
    simp
  | succ n ih =>
    have h := (ih.mul hf).congr_weight (show (n : ℤ) * k + k = ((n + 1 : ℕ) : ℤ) * k by push_cast; ring)
    simpa [pow_succ] using h

/- English proof (translation)
Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.
-/
theorem zetaC_pow_self {m : ℕ} (hm : 0 < m) : zetaC m ^ m = 1 := by
  unfold zetaC
  rw [← Complex.exp_nat_mul]
  have hm' : (m : ℂ) ≠ 0 := by exact_mod_cast hm.ne'
  have : (m : ℂ) * (2 * Real.pi * Complex.I / m) = 2 * Real.pi * Complex.I := by field_simp
  rw [this, Complex.exp_two_pi_mul_I]

/- English proof (translation)
Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Establish an intermediate fact. Reduce the equality to equality of the corresponding arguments.

Move the embeddings inside the algebraic operations. Clear the denominators using the available nonvanishing facts.
-/
theorem zetaC_mul {a e : ℕ} (ha : 0 < a) (he : 0 < e) : zetaC (a * e) ^ a = zetaC e := by
  unfold zetaC
  rw [← Complex.exp_nat_mul]
  have ha' : (a : ℂ) ≠ 0 := by exact_mod_cast ha.ne'
  have he' : (e : ℂ) ≠ 0 := by exact_mod_cast he.ne'
  congr 1
  push_cast
  field_simp

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem zetaC_mem (m : ℕ) : zetaC m ∈ Rm m := by
  exact Subring.subset_closure (Set.mem_singleton _)

/- English proof (translation)
Establish an intermediate fact. Use symmetry to reverse the relation. Reduce the claim to the hypotheses of an applicable result. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities.

A detailed English derivation is pending.
-/
theorem zetaC_inv_mem {m : ℕ} (hm : 0 < m) : (zetaC m)⁻¹ ∈ Rm m := by
  have h : (zetaC m)⁻¹ = zetaC m ^ (m - 1) := by
    symm
    apply eq_inv_of_mul_eq_one_left
    rw [← pow_succ, Nat.sub_add_cancel hm, zetaC_pow_self hm]
  rw [h]
  exact pow_mem (zetaC_mem m) _

/- English proof (translation)
Establish an intermediate fact. Establish an intermediate fact. A detailed English derivation is pending.
-/
theorem Rm_isIntegral {m : ℕ} (hm : 0 < m) {x : ℂ} (hx : x ∈ Rm m) : IsIntegral ℤ x := by
  have hζ : IsIntegral ℤ (zetaC m) :=
    IsIntegral.of_pow hm (by rw [zetaC_pow_self hm]; exact isIntegral_one)
  have hle : Rm m ≤ (integralClosure ℤ ℂ).toSubring :=
    Subring.closure_le.mpr (Set.singleton_subset_iff.mpr hζ)
  exact hle hx

end ReciprocityTheory.ChartRestriction.L1

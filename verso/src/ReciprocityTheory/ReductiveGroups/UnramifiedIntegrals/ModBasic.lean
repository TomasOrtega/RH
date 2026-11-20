import Mathlib
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ModDefs

noncomputable section
open scoped BigOperators Classical UpperHalfPlane MatrixGroups CongruenceSubgroup Manifold
open ModularForm EisensteinSeries ModularFormClass UpperHalfPlane Formalism.L2.Th1.CM

namespace ReciprocityTheory.ChartRestriction.L1

/- English proof (translation)
Rewrite using `[Tm, Finset.mem_image]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨⟨a, b⟩, hx, rfl⟩`. Rewrite `hx` using `[Finset.mem_sigma, Nat.mem_divisors, Finset.mem_range]`. Conclude with `⟨Nat.mul_div_cancel' hx.1.1, hx.2⟩`.

Take `⟨a, b, e⟩` from `t`. Introduce and unpack `⟨h1, h2⟩`. Simplify using `only at h1 h2`. Establish `ha : 0 < a` using `Nat.pos_of_ne_zero (by rintro rfl; omega)`. Establish `he : m / a = e` using `by rw [← h1, Nat.mul_div_cancel_left _ ha]`.

Use `⟨⟨a, b⟩, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[Finset.mem_sigma, Nat.mem_divisors, Finset.mem_range]`. Conclude with `⟨⟨⟨e, h1.symm⟩, hm.ne'⟩, by rw [he]; exact h2⟩`. Simplify using `only [he]`.
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
Establish `h` using `((mem_Tm hm t).mp ht).1`. Establish `hpos : 0 < t.1 * t.2.2` using `h ▸ hm`. Apply the tactic sequence `refine ⟨Nat.pos_of_ne_zero fun h0 => ?_, Nat.pos_of_ne_zero fun h0 => ?_⟩ <;>`. Apply the tactic sequence `rw [h0] at hpos <;> simp at hpos`.
-/
theorem Tm_pos {m : ℕ} (hm : 0 < m) {t : ℕ × ℕ × ℕ} (ht : t ∈ Tm m) : 0 < t.1 ∧ 0 < t.2.2 := by
  have h := ((mem_Tm hm t).mp ht).1
  have hpos : 0 < t.1 * t.2.2 := h ▸ hm
  refine ⟨Nat.pos_of_ne_zero fun h0 => ?_, Nat.pos_of_ne_zero fun h0 => ?_⟩ <;>
    rw [h0] at hpos <;> simp at hpos

/- English proof (translation)
Establish `hz : 0 < (((a : ℂ) * τ + b) / e).im`. Rewrite using `[Complex.div_natCast_im]`. Simplify using `only [Complex.add_im, Complex.mul_im, Complex.natCast_re, Complex.natCast_im, zero_mul, add_zero, UpperHalfPlane.coe_im]`. Conclude with `div_pos (mul_pos (by exact_mod_cast ha) τ.im_pos) (by exact_mod_cast he)`. Unfold `pt`.

Rewrite using `[UpperHalfPlane.ofComplex_apply_of_im_pos hz]`.
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
Conclude with `ModularForm.discriminant_ne_zero τ`.
-/
theorem DD_ne_zero (τ : ℍ) : DD τ ≠ 0 := by
  exact ModularForm.discriminant_ne_zero τ

/- English proof (translation)
Establish `h` using `SlashInvariantForm.slash_action_eqn'' g (γ := Matrix.SpecialLinearGroup.mapGL ℝ γ) (MonoidHom.mem_range.mpr ⟨γ, rfl⟩) τ`. Conclude with `h`.
-/
theorem smul_of_form {k : ℤ} (g : ModularForm 𝒮ℒ k) (γ : SL(2, ℤ)) (τ : ℍ) :
    g (γ • τ) = denom γ τ ^ k * g τ := by
  have h := SlashInvariantForm.slash_action_eqn'' g (γ := Matrix.SpecialLinearGroup.mapGL ℝ γ)
    (MonoidHom.mem_range.mpr ⟨γ, rfl⟩) τ
  exact h

/- English proof (translation)
Use `⟨ModularForm.mcast (by norm_num) (ModularForm.E₄.mul (ModularForm.E₄.mul ModularForm.E₄)), fun τ => ?_⟩` and prove the remaining obligations. Use `show (ModularForm.E₄.mul (ModularForm.E₄.mul ModularForm.E₄)) τ = AA τ`. Rewrite using `[ModularForm.coe_mul, Pi.mul_apply, ModularForm.coe_mul, Pi.mul_apply]`. Unfold `AA`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem isMF_AA : IsMF 12 AA := by
  refine ⟨ModularForm.mcast (by norm_num) (ModularForm.E₄.mul (ModularForm.E₄.mul ModularForm.E₄)), fun τ => ?_⟩
  show (ModularForm.E₄.mul (ModularForm.E₄.mul ModularForm.E₄)) τ = AA τ
  rw [ModularForm.coe_mul, Pi.mul_apply, ModularForm.coe_mul, Pi.mul_apply]
  unfold AA
  ring

/- English proof (translation)
Use `first`. Consider the case `exact ⟨ModularFormClass.modularForm ModularForm.discriminantCuspForm, fun τ => rfl⟩`. Consider the case `exact ⟨ModularFormClass.modularForm CuspForm.discriminant, fun τ => rfl⟩`.
-/
theorem isMF_DD : IsMF 12 DD := by
  first
    | exact ⟨ModularFormClass.modularForm ModularForm.discriminantCuspForm, fun τ => rfl⟩
    | exact ⟨ModularFormClass.modularForm CuspForm.discriminant, fun τ => rfl⟩

/- English proof (translation)
Take `⟨g, hg⟩` from `h`. Rewrite using `[← hg, ← hg]`. Conclude with `smul_of_form g γ τ`.
-/
theorem IsMF.smul_eq {k : ℤ} {f : ℍ → ℂ} (h : IsMF k f) (γ : SL(2, ℤ)) (τ : ℍ) :
    f (γ • τ) = denom γ τ ^ k * f τ := by
  obtain ⟨g, hg⟩ := h
  rw [← hg, ← hg]
  exact smul_of_form g γ τ

/- English proof (translation)
Conclude with `isMF_AA.smul_eq γ τ`.
-/
theorem AA_smul (γ : SL(2, ℤ)) (τ : ℍ) : AA (γ • τ) = denom γ τ ^ 12 * AA τ := by
  exact isMF_AA.smul_eq γ τ

/- English proof (translation)
Conclude with `isMF_DD.smul_eq γ τ`.
-/
theorem DD_smul (γ : SL(2, ℤ)) (τ : ℍ) : DD (γ • τ) = denom γ τ ^ 12 * DD τ := by
  exact isMF_DD.smul_eq γ τ

/- English proof (translation)
Unfold `jT`. Rewrite using `[AA_smul, DD_smul, mul_div_mul_left _ _ (pow_ne_zero _ (UpperHalfPlane.denom_ne_zero _ τ))]`.
-/
theorem jT_smul (γ : SL(2, ℤ)) (τ : ℍ) : jT (γ • τ) = jT τ := by
  unfold jT
  rw [AA_smul, DD_smul, mul_div_mul_left _ _ (pow_ne_zero _ (UpperHalfPlane.denom_ne_zero _ τ))]

/- English proof (translation)
Substitute `hk` using the available equality. Conclude with `h`.
-/
theorem IsMF.congr_weight {k k' : ℤ} {f : ℍ → ℂ} (h : IsMF k f) (hk : k = k') : IsMF k' f := by
  subst hk
  exact h

/- English proof (translation)
Take `⟨f', hf'⟩` from `hf`. Take `⟨g', hg'⟩` from `hg`. Conclude with `⟨f' + g', fun τ => by simp [hf', hg']⟩`.
-/
theorem IsMF.add {k : ℤ} {f g : ℍ → ℂ} (hf : IsMF k f) (hg : IsMF k g) : IsMF k (fun τ => f τ + g τ) := by
  obtain ⟨f', hf'⟩ := hf
  obtain ⟨g', hg'⟩ := hg
  exact ⟨f' + g', fun τ => by simp [hf', hg']⟩

/- English proof (translation)
Take `⟨f', hf'⟩` from `hf`. Take `⟨g', hg'⟩` from `hg`. Conclude with `⟨f' - g', fun τ => by simp [hf', hg']⟩`.
-/
theorem IsMF.sub {k : ℤ} {f g : ℍ → ℂ} (hf : IsMF k f) (hg : IsMF k g) : IsMF k (fun τ => f τ - g τ) := by
  obtain ⟨f', hf'⟩ := hf
  obtain ⟨g', hg'⟩ := hg
  exact ⟨f' - g', fun τ => by simp [hf', hg']⟩

/- English proof (translation)
Take `⟨f', hf'⟩` from `hf`. Conclude with `⟨c • f', fun τ => by simp [hf']⟩`.
-/
theorem IsMF.const_mul {k : ℤ} {f : ℍ → ℂ} (c : ℂ) (hf : IsMF k f) : IsMF k (fun τ => c * f τ) := by
  obtain ⟨f', hf'⟩ := hf
  exact ⟨c • f', fun τ => by simp [hf']⟩

/- English proof (translation)
Take `⟨f', hf'⟩` from `hf`. Take `⟨g', hg'⟩` from `hg`. Conclude with `⟨f'.mul g', fun τ => by rw [ModularForm.coe_mul, Pi.mul_apply, hf', hg']⟩`.
-/
theorem IsMF.mul {k k' : ℤ} {f g : ℍ → ℂ} (hf : IsMF k f) (hg : IsMF k' g) :
    IsMF (k + k') (fun τ => f τ * g τ) := by
  obtain ⟨f', hf'⟩ := hf
  obtain ⟨g', hg'⟩ := hg
  exact ⟨f'.mul g', fun τ => by rw [ModularForm.coe_mul, Pi.mul_apply, hf', hg']⟩

/- English proof (translation)
Proceed by induction on `n with`. Consider the case `zero`. Use `IsMF.congr_weight (k := 0) ⟨1, fun τ => ?_⟩ (by simp)` and prove the remaining obligations. Simplify using the standard rewrite rules. Consider the case `succ n ih`.

Establish `h` using `(ih.mul hf).congr_weight (show (n : ℤ) * k + k = ((n + 1 : ℕ) : ℤ) * k by push_cast; ring)`. Simplify `h` using `[pow_succ]`.
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
Unfold `zetaC`. Rewrite using `[← Complex.exp_nat_mul]`. Establish `hm' : (m : ℂ) ≠ 0` using `by exact_mod_cast hm.ne'`. Establish `: (m : ℂ) * (2 * Real.pi * Complex.I / m) = 2 * Real.pi * Complex.I` using `by field_simp`. Rewrite using `[this, Complex.exp_two_pi_mul_I]`.
-/
theorem zetaC_pow_self {m : ℕ} (hm : 0 < m) : zetaC m ^ m = 1 := by
  unfold zetaC
  rw [← Complex.exp_nat_mul]
  have hm' : (m : ℂ) ≠ 0 := by exact_mod_cast hm.ne'
  have : (m : ℂ) * (2 * Real.pi * Complex.I / m) = 2 * Real.pi * Complex.I := by field_simp
  rw [this, Complex.exp_two_pi_mul_I]

/- English proof (translation)
Unfold `zetaC`. Rewrite using `[← Complex.exp_nat_mul]`. Establish `ha' : (a : ℂ) ≠ 0` using `by exact_mod_cast ha.ne'`. Establish `he' : (e : ℂ) ≠ 0` using `by exact_mod_cast he.ne'`. Use `congr 1`.

Use `push_cast`. Clear the denominators using the available nonvanishing facts.
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
Conclude with `Subring.subset_closure (Set.mem_singleton _)`.
-/
theorem zetaC_mem (m : ℕ) : zetaC m ∈ Rm m := by
  exact Subring.subset_closure (Set.mem_singleton _)

/- English proof (translation)
Establish `h : (zetaC m)⁻¹ = zetaC m ^ (m - 1)`. Use `symm`. Apply `eq_inv_of_mul_eq_one_left` to reduce the goal to its premises. Rewrite using `[← pow_succ, Nat.sub_add_cancel hm, zetaC_pow_self hm]`. Rewrite using `[h]`.

Conclude with `pow_mem (zetaC_mem m) _`.
-/
theorem zetaC_inv_mem {m : ℕ} (hm : 0 < m) : (zetaC m)⁻¹ ∈ Rm m := by
  have h : (zetaC m)⁻¹ = zetaC m ^ (m - 1) := by
    symm
    apply eq_inv_of_mul_eq_one_left
    rw [← pow_succ, Nat.sub_add_cancel hm, zetaC_pow_self hm]
  rw [h]
  exact pow_mem (zetaC_mem m) _

/- English proof (translation)
Establish `hζ : IsIntegral ℤ (zetaC m)` using `IsIntegral.of_pow hm (by rw [zetaC_pow_self hm]; exact isIntegral_one)`. Establish `hle : Rm m ≤ (integralClosure ℤ ℂ).toSubring` using `Subring.closure_le.mpr (Set.singleton_subset_iff.mpr hζ)`. Conclude with `hle hx`.
-/
theorem Rm_isIntegral {m : ℕ} (hm : 0 < m) {x : ℂ} (hx : x ∈ Rm m) : IsIntegral ℤ x := by
  have hζ : IsIntegral ℤ (zetaC m) :=
    IsIntegral.of_pow hm (by rw [zetaC_pow_self hm]; exact isIntegral_one)
  have hle : Rm m ≤ (integralClosure ℤ ℂ).toSubring :=
    Subring.closure_le.mpr (Set.singleton_subset_iff.mpr hζ)
  exact hle hx

end ReciprocityTheory.ChartRestriction.L1

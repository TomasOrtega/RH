import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.DualRestrictSurjectiveOfIsTorsionFreeQuotient
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.IsUnitOfLagrangian
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.DifferentiableOnLeftInverse
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.HasSumPolyDerivMulProdAddMatrix

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

namespace GlobalTheory.HolTheta

open Matrix GlobalTheory.CanTh GlobalTheory.RiemannRel

variable {g : ℕ}

/- English proof (translation)
Establish `hRY : M.map Complex.re * τ.map Complex.im = 1`. Use extensionality with `j k`. Use `hN j k` as an intermediate fact. Simplify using `only [Matrix.mul_apply, Complex.im_sum, map_apply, Complex.mul_im, hM, Complex.conj_im, zero_mul, add_zero, mul_neg, Finset.sum_neg_distrib, neg_inj] at this`. Rewrite using `[← this]`.

Simplify using `[Matrix.mul_apply]`. Rewrite using `[imInv, inv_eq_left_inv hRY]`. Use extensionality with `j k`. Apply `Complex.ext` to reduce the goal to its premises. Simplify using the standard rewrite rules.

Simplify using `[hM]`.
-/
theorem pull_eq_imInv (M τ : Matrix (Fin g) (Fin g) ℂ) (hM : ∀ j k, (M j k).im = 0)
    (hN : ∀ j k, ((M * τ.map (starRingEnd ℂ)) j k).im = -(1 : Matrix (Fin g) (Fin g) ℝ) j k) :
    M = imInv τ := by
  have hRY : M.map Complex.re * τ.map Complex.im = 1 := by
    ext j k
    have := hN j k
    simp only [Matrix.mul_apply, Complex.im_sum, map_apply, Complex.mul_im, hM, Complex.conj_im, zero_mul, add_zero,
      mul_neg, Finset.sum_neg_distrib, neg_inj] at this
    rw [← this]
    simp [Matrix.mul_apply]
  rw [imInv, inv_eq_left_inv hRY]
  ext j k
  apply Complex.ext
  · simp
  · simp [hM]

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField in
open scoped CategoryTheory.Obj TensorProduct in
open Matrix in
variable {g : ℕ} in

/- English proof (translation)
Use `set F : Matrix (Fin g) (Fin g) ℂ := Matrix.of fun i j => f j i with hF`. Establish `hAe : ∀ k, A *ᵥ Pi.single k 1 = e k` using `fun k => by`. Rewrite using `[hA]`. Conclude with `_root_.GlobalTheory.RiemannRel.of_cols_mulVec e k`. Establish `hFf : ∀ k, F *ᵥ Pi.single k 1 = f k` using `fun k => _root_.GlobalTheory.RiemannRel.of_cols_mulVec f k`.

Establish `h1 : ∀ j k, ((Aᵀ * G * A.map (starRingEnd ℂ)) j k).im = 0` using `fun j k => by`. Rewrite using `[← _root_.GlobalTheory.RiemannRel.hermForm_col, hAe, hAe]`. Conclude with `hee j k`. Establish `h2 : ∀ j k, ((Aᵀ * G * F.map (starRingEnd ℂ)) j k).im = -(1 : Matrix (Fin g) (Fin g) ℝ) j k` using `fun j k => by rw [← _root_.GlobalTheory.RiemannRel.hermForm_col, hAe, hFf]; exact hef j k`. Establish `h3 : ∀ j k, ((Fᵀ * G * F.map (starRingEnd ℂ)) j k).im = 0` using `fun j k => by`.

Rewrite using `[← _root_.GlobalTheory.RiemannRel.hermForm_col, hFf, hFf]`. Conclude with `hff j k`. Establish `hdet : A.det ≠ 0` using `_root_.GlobalTheory.RiemannRel.det_ne_zero G A F hpos h1 h2`. Establish `hunit : IsUnit A.det` using `isUnit_iff_ne_zero.mpr hdet`. Establish `hAτ : A * τ = F`.

Rewrite using `[hτ, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv A hunit, Matrix.one_mul]`. Take `⟨hsymm, hpd⟩` from `_root_.GlobalTheory.RiemannRel.symm_posDef G A τ hG hdet hpos h1 (by rw [hAτ]; exact h2) (by rw [hAτ]; exact h3)`. Use `⟨hunit, hsymm, hpd, ?_⟩` and prove the remaining obligations. Use `set M := Aᵀ * G * A.map (starRingEnd ℂ) with hMdef`. Establish `hMreal : (M.map Complex.re).map Complex.ofReal = M`.

Use extensionality with `j k`. Apply `Complex.ext` to reduce the goal to its premises. Simplify using the standard rewrite rules. Simplify using `[h1 j k]`. Establish `hinv : M.map Complex.re * τ.map Complex.im = 1`.

Use extensionality with `j k`. Establish `h` using `h2 j k`. Rewrite `h` using `[← hAτ, Matrix.map_mul, ← Matrix.mul_assoc, Matrix.mul_apply, Complex.im_sum]`. Rewrite using `[Matrix.mul_apply]`. Establish `hsum : ∀ l, ((M j l) * (starRingEnd ℂ) (τ l k)).im = -((M j l).re * (τ l k).im)`.

Introduce `l`. Rewrite using `[Complex.mul_im, Complex.conj_re, Complex.conj_im, h1 j l]`. Expand and normalize the polynomial expressions, which then agree. Simplify using `only [Matrix.map_apply] at h ⊢`. Rewrite `h` using `[Finset.sum_congr rfl (fun l _ => hsum l), Finset.sum_neg_distrib]`.

Combine the linear equalities and inequalities to obtain the conclusion. Establish `hM : M = _root_.GlobalTheory.CanTh.imInv τ`. Unfold `_root_.GlobalTheory.CanTh.imInv`. Rewrite using `[Matrix.inv_eq_left_inv hinv, hMreal]`. Introduce `z w`.

Establish `hz : ∀ v : Fin g → ℂ, v = A *ᵥ (A⁻¹ *ᵥ v)` using `fun v => by`. Rewrite using `[Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv A hunit, Matrix.one_mulVec]`. Use `conv_lhs => rw [hz z, hz w]`. Rewrite using `[_root_.GlobalTheory.RiemannRel.hermForm_mulVec, ← hMdef, hM]`. Both sides reduce to the same expression.
-/
theorem _root_.GlobalTheory.HolTheta.normal_form (G : Matrix (Fin g) (Fin g) ℂ) (e f : Fin g → Fin g → ℂ) (hG : G.IsHermitian)
    (hpos : ∀ z : Fin g → ℂ, z ≠ 0 → 0 < (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm G z z).re)
    (hee : ∀ j k, (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm G (e j) (e k)).im = 0) (hff : ∀ j k, (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm G (f j) (f k)).im = 0)
    (hef : ∀ j k, (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm G (e j) (f k)).im = -(1 : Matrix (Fin g) (Fin g) ℝ) j k)
    {A τ : Matrix (Fin g) (Fin g) ℂ} (hA : A = Matrix.of fun i j => e j i)
    (hτ : τ = A⁻¹ * Matrix.of fun i j => f j i) :
    IsUnit A.det ∧ τ.IsSymm ∧ (τ.map Complex.im).PosDef ∧
      ∀ z w, _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm G z w = _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm (_root_.GlobalTheory.CanTh.imInv τ) (A⁻¹ *ᵥ z) (A⁻¹ *ᵥ w) := by
  set F : Matrix (Fin g) (Fin g) ℂ := Matrix.of fun i j => f j i with hF
  have hAe : ∀ k, A *ᵥ Pi.single k 1 = e k := fun k => by
    rw [hA]; exact _root_.GlobalTheory.RiemannRel.of_cols_mulVec e k
  have hFf : ∀ k, F *ᵥ Pi.single k 1 = f k := fun k => _root_.GlobalTheory.RiemannRel.of_cols_mulVec f k
  have h1 : ∀ j k, ((Aᵀ * G * A.map (starRingEnd ℂ)) j k).im = 0 := fun j k => by
    rw [← _root_.GlobalTheory.RiemannRel.hermForm_col, hAe, hAe]; exact hee j k
  have h2 : ∀ j k, ((Aᵀ * G * F.map (starRingEnd ℂ)) j k).im = -(1 : Matrix (Fin g) (Fin g) ℝ) j k :=
    fun j k => by rw [← _root_.GlobalTheory.RiemannRel.hermForm_col, hAe, hFf]; exact hef j k
  have h3 : ∀ j k, ((Fᵀ * G * F.map (starRingEnd ℂ)) j k).im = 0 := fun j k => by
    rw [← _root_.GlobalTheory.RiemannRel.hermForm_col, hFf, hFf]; exact hff j k
  have hdet : A.det ≠ 0 := _root_.GlobalTheory.RiemannRel.det_ne_zero G A F hpos h1 h2
  have hunit : IsUnit A.det := isUnit_iff_ne_zero.mpr hdet
  have hAτ : A * τ = F := by
    rw [hτ, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv A hunit, Matrix.one_mul]
  obtain ⟨hsymm, hpd⟩ := _root_.GlobalTheory.RiemannRel.symm_posDef G A τ hG hdet hpos h1
    (by rw [hAτ]; exact h2) (by rw [hAτ]; exact h3)
  refine ⟨hunit, hsymm, hpd, ?_⟩
  set M := Aᵀ * G * A.map (starRingEnd ℂ) with hMdef
  have hMreal : (M.map Complex.re).map Complex.ofReal = M := by
    ext j k
    apply Complex.ext
    · simp
    · simp [h1 j k]
  have hinv : M.map Complex.re * τ.map Complex.im = 1 := by
    ext j k
    have h := h2 j k
    rw [← hAτ, Matrix.map_mul, ← Matrix.mul_assoc, Matrix.mul_apply, Complex.im_sum] at h
    rw [Matrix.mul_apply]
    have hsum : ∀ l, ((M j l) * (starRingEnd ℂ) (τ l k)).im = -((M j l).re * (τ l k).im) := by
      intro l
      rw [Complex.mul_im, Complex.conj_re, Complex.conj_im, h1 j l]
      ring
    simp only [Matrix.map_apply] at h ⊢
    rw [Finset.sum_congr rfl (fun l _ => hsum l), Finset.sum_neg_distrib] at h
    linarith
  have hM : M = _root_.GlobalTheory.CanTh.imInv τ := by
    unfold _root_.GlobalTheory.CanTh.imInv
    rw [Matrix.inv_eq_left_inv hinv, hMreal]
  intro z w
  have hz : ∀ v : Fin g → ℂ, v = A *ᵥ (A⁻¹ *ᵥ v) := fun v => by
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv A hunit, Matrix.one_mulVec]
  conv_lhs => rw [hz z, hz w]
  rw [_root_.GlobalTheory.RiemannRel.hermForm_mulVec, ← hMdef, hM]
  rfl

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField in
open scoped CategoryTheory.Obj TensorProduct in
open Matrix in
variable {g : ℕ} in

/- English proof (translation)
Establish `hneg : ∀ k : ℤ, ((-1 : ℂ)) ^ k = Complex.exp (k * (Real.pi * Complex.I))`. Introduce `k`. Rewrite using `[Complex.exp_int_mul, Complex.exp_pi_mul_I]`. Unfold `_root_.GlobalTheory.CanTh.canMult`. Rewrite using `[hneg, ← Complex.exp_add, ← Complex.exp_add, Complex.exp_eq_exp_iff_exists_int]`.

Use `⟨m ⬝ᵥ n', ?_⟩` and prove the remaining obligations. Establish `h1 : (fun i => ((m + m') i : ℝ)) = (fun i => (m i : ℝ)) + fun i => (m' i : ℝ)`. Use extensionality with `i`. Simplify using the standard rewrite rules. Establish `h2 : (fun i => ((n + n') i : ℝ)) = (fun i => (n i : ℝ)) + fun i => (n' i : ℝ)`.

Use extensionality with `i`. Simplify using the standard rewrite rules. Simplify using `only [h1, h2, dotProduct_add, add_dotProduct, dotProduct_comm n m']`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem _root_.GlobalTheory.HolTheta.canMult_add (a c : Fin g → ℝ) (m n m' n' : Fin g → ℤ) :
    _root_.GlobalTheory.CanTh.canMult a c (m + m') (n + n') = _root_.GlobalTheory.CanTh.canMult a c m n * _root_.GlobalTheory.CanTh.canMult a c m' n' * (-1) ^ (n ⬝ᵥ m' - m ⬝ᵥ n') := by
  have hneg : ∀ k : ℤ, ((-1 : ℂ)) ^ k = Complex.exp (k * (Real.pi * Complex.I)) := by
    intro k; rw [Complex.exp_int_mul, Complex.exp_pi_mul_I]
  unfold _root_.GlobalTheory.CanTh.canMult
  rw [hneg, ← Complex.exp_add, ← Complex.exp_add, Complex.exp_eq_exp_iff_exists_int]
  refine ⟨m ⬝ᵥ n', ?_⟩
  have h1 : (fun i => ((m + m') i : ℝ)) = (fun i => (m i : ℝ)) + fun i => (m' i : ℝ) := by
    ext i; simp
  have h2 : (fun i => ((n + n') i : ℝ)) = (fun i => (n i : ℝ)) + fun i => (n' i : ℝ) := by
    ext i; simp
  simp only [h1, h2, dotProduct_add, add_dotProduct, dotProduct_comm n m']
  push_cast
  ring

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField in
open scoped CategoryTheory.Obj TensorProduct in
open Matrix in
variable {g : ℕ} in

/- English proof (translation)
Establish `h0 : χ 0 = ψ 0`. Establish `h1` using `hχ 0 0`. Establish `h2` using `hψ 0 0`. Simplify using `only [add_zero] at h1 h2`. Establish `e1 : χ 0 * E 0 0 = 1`.

Apply `mul_left_cancel₀ (hχ0 0)` to reduce the goal to its premises. Take the linear combination `-h1`. Establish `e2 : ψ 0 * E 0 0 = 1`. Apply `mul_left_cancel₀ (hψ0 0)` to reduce the goal to its premises. Take the linear combination `-h2`.

Take the linear combination `ψ 0 * e1 - χ 0 * e2`. Set `S : AddSubgroup La` to `{ carrier := {x | χ x = ψ x} add_mem' := by`. Introduce `x y hx hy`. Simplify using `only [Set.mem_setOf_eq] at hx hy ⊢`. Rewrite using `[hχ, hψ, hx, hy]`.

Use the proof step `zero_mem' := h0`. Use the proof step `neg_mem' := by`. Introduce `x hx`. Simplify using `only [Set.mem_setOf_eq] at hx ⊢`. Establish `h1` using `hχ x (-x)`.

Establish `h2` using `hψ x (-x)`. Rewrite `h1`, `h2` using `[add_neg_cancel]`. Establish `hne : ψ x * E x (-x) ≠ 0` using `mul_ne_zero (hψ0 x) (hE x (-x))`. Apply `mul_left_cancel₀ hne` to reduce the goal to its premises. Take the linear combination `-(E x (-x)) * χ (-x) * hx - h1 + h2 + h0 }`.

Establish `hspan : Submodule.span ℤ (Set.range bs) ≤ S.toIntSubmodule`. Rewrite using `[Submodule.span_le]`. Introduce and unpack `_ ⟨i, rfl⟩`. Conclude with `hb i`. Rewrite `hspan` using `[bs.span_eq]`.

Conclude with `hspan Submodule.mem_top`.
-/
theorem _root_.GlobalTheory.HolTheta.eq_of_cocycle {La κ : Type*} [AddCommGroup La] (bs : Module.Basis κ ℤ La) (E : La → La → ℂ)
    {χ ψ : La → ℂ} (hE : ∀ x y, E x y ≠ 0) (hχ0 : ∀ x, χ x ≠ 0) (hψ0 : ∀ x, ψ x ≠ 0)
    (hχ : ∀ x y, χ (x + y) = χ x * χ y * E x y) (hψ : ∀ x y, ψ (x + y) = ψ x * ψ y * E x y)
    (hb : ∀ i, χ (bs i) = ψ (bs i)) (x : La) : χ x = ψ x := by
  have h0 : χ 0 = ψ 0 := by
    have h1 := hχ 0 0
    have h2 := hψ 0 0
    simp only [add_zero] at h1 h2
    have e1 : χ 0 * E 0 0 = 1 := by
      apply mul_left_cancel₀ (hχ0 0)
      linear_combination -h1
    have e2 : ψ 0 * E 0 0 = 1 := by
      apply mul_left_cancel₀ (hψ0 0)
      linear_combination -h2
    linear_combination ψ 0 * e1 - χ 0 * e2
  let S : AddSubgroup La :=
    { carrier := {x | χ x = ψ x}
      add_mem' := by
        intro x y hx hy
        simp only [Set.mem_setOf_eq] at hx hy ⊢
        rw [hχ, hψ, hx, hy]
      zero_mem' := h0
      neg_mem' := by
        intro x hx
        simp only [Set.mem_setOf_eq] at hx ⊢
        have h1 := hχ x (-x)
        have h2 := hψ x (-x)
        rw [add_neg_cancel] at h1 h2
        have hne : ψ x * E x (-x) ≠ 0 := mul_ne_zero (hψ0 x) (hE x (-x))
        apply mul_left_cancel₀ hne
        linear_combination -(E x (-x)) * χ (-x) * hx - h1 + h2 + h0 }
  have hspan : Submodule.span ℤ (Set.range bs) ≤ S.toIntSubmodule := by
    rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    exact hb i
  rw [bs.span_eq] at hspan
  exact hspan Submodule.mem_top

/- English proof (translation)
Establish `key : ∀ x, ∃ t : ℝ, Complex.exp (2 * Real.pi * Complex.I * t) = χ x` using `fun x => by`. Break down `h1 x with h | h` into its components or cases. Conclude with `⟨0, by simp [h]⟩`. Use `⟨1 / 2, ?_⟩` and prove the remaining obligations. Rewrite using `[h, ← Complex.exp_pi_mul_I]`.

Use `congr 1`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Use `choose t ht using key`. Apply the tactic sequence `refine ⟨fun i => t (bs (Sum.inl i)), fun i => -t (bs (Sum.inr i)), eq_of_cocycle bs (fun x y => (-1) ^ EF x y) (fun x y => zpow_ne_zero _ (by norm_num)) (fun x => by rcases h1 x with h | h <;> simp [h]) (fun x => Complex.exp_ne_zero _) hχ (fun x y => ?_) ?_⟩`.

Establish `h` using `hbs.apply_eq_sum halt.neg x y`. Establish `e : EF x y = (fun i => bs.repr x (Sum.inr i)) ⬝ᵥ (fun i => bs.repr y (Sum.inl i)) - (fun i => bs.repr x (Sum.inl i)) ⬝ᵥ (fun i => bs.repr y (Sum.inr i))`. Simplify using `only [LinearMap.neg_apply, neg_eq_iff_eq_neg] at h`. Rewrite using `[h]`. Simplify using `[dotProduct]`.

Rewrite using `[e, ← canMult_add, map_add]`. Both sides reduce to the same expression. Introduce and unpack `(i | i)`. Rewrite using `[← ht, canMult]`. Simplify using `[dotProduct, Finsupp.single_apply]`.

Rewrite using `[← ht, canMult]`. Simplify using `[dotProduct, Finsupp.single_apply]`.
-/
theorem exists_canMult {La : Type*} [AddCommGroup La] (bs : Module.Basis (Fin g ⊕ Fin g) ℤ La)
    (EF : LinearMap.BilinForm ℤ La) (halt : EF.IsAlt) (hbs : IsSymplecticBasis (-EF) bs) {χ : La → ℂ}
    (h1 : ∀ x, χ x = 1 ∨ χ x = -1) (hχ : ∀ x y, χ (x + y) = χ x * χ y * (-1) ^ EF x y) :
    ∃ a c : Fin g → ℝ, ∀ x, χ x =
      canMult a c (fun i => bs.repr x (Sum.inl i)) (fun i => bs.repr x (Sum.inr i)) := by
  classical
  have key : ∀ x, ∃ t : ℝ, Complex.exp (2 * Real.pi * Complex.I * t) = χ x := fun x => by
    rcases h1 x with h | h
    · exact ⟨0, by simp [h]⟩
    · refine ⟨1 / 2, ?_⟩
      rw [h, ← Complex.exp_pi_mul_I]
      congr 1
      push_cast
      ring
  choose t ht using key
  refine ⟨fun i => t (bs (Sum.inl i)), fun i => -t (bs (Sum.inr i)),
    eq_of_cocycle bs (fun x y => (-1) ^ EF x y) (fun x y => zpow_ne_zero _ (by norm_num))
      (fun x => by rcases h1 x with h | h <;> simp [h]) (fun x => Complex.exp_ne_zero _) hχ (fun x y => ?_) ?_⟩
  · have h := hbs.apply_eq_sum halt.neg x y
    have e : EF x y = (fun i => bs.repr x (Sum.inr i)) ⬝ᵥ (fun i => bs.repr y (Sum.inl i)) -
        (fun i => bs.repr x (Sum.inl i)) ⬝ᵥ (fun i => bs.repr y (Sum.inr i)) := by
      simp only [LinearMap.neg_apply, neg_eq_iff_eq_neg] at h
      rw [h]
      simp [dotProduct]
    rw [e, ← canMult_add, map_add]
    rfl
  · rintro (i | i)
    · rw [← ht, canMult]
      simp [dotProduct, Finsupp.single_apply]
    · rw [← ht, canMult]
      simp [dotProduct, Finsupp.single_apply]

/- English proof (translation)
Establish `h` using `dot_imInv_eq_hermForm_add hp (fun i => (n i : ℝ)) (fun i => (m i : ℝ)) y`. Simplify using `only [Complex.ofReal_intCast] at h`. Rewrite `h` using `[← hy]`. Rewrite using `[canTh, ← _root_.mul_assoc, ← Complex.exp_add, mulVec_smul, smul_dotProduct, dotProduct_smul, h]`. Use `congr 2`.

Simplify using `only [smul_eq_mul]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem exp_mul_canTh {τ : Matrix (Fin g) (Fin g) ℂ} (hp : (τ.map Complex.im).PosDef) (a c : Fin g → ℝ)
    (m n : Fin g → ℤ) {y : Fin g → ℂ} (hy : y = (fun i => (m i : ℂ)) + τ *ᵥ fun i => (n i : ℂ)) (s : ℂ) :
    Complex.exp (-(Real.pi / 2 / s ^ 2) * hermForm (imInv τ) y y) * canTh τ a c (s⁻¹ • y) =
      Complex.exp (Real.pi / 2 / s ^ 2 * (2 * Complex.I * (y ⬝ᵥ fun i => (n i : ℂ)))) *
        thetaChar τ (fun i => (a i : ℂ)) (fun i => (c i : ℂ)) (s⁻¹ • y) := by
  have h := dot_imInv_eq_hermForm_add hp (fun i => (n i : ℝ)) (fun i => (m i : ℝ)) y
  simp only [Complex.ofReal_intCast] at h
  rw [← hy] at h
  rw [canTh, ← _root_.mul_assoc, ← Complex.exp_add, mulVec_smul, smul_dotProduct, dotProduct_smul, h]
  congr 2
  simp only [smul_eq_mul]
  ring

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField in
open scoped CategoryTheory.Obj TensorProduct in
open Matrix in
variable {g : ℕ} in
/- English proof (translation)
Set `L : Submodule ℤ (Fin g → ℂ)` to `LinearMap.range P.toIntLinearMap`. Use `haveI : DiscreteTopology L := hdisc`. Use `haveI : IsZLattice ℝ L := ⟨by simpa [L, LinearMap.coe_range] using hspan⟩`. Establish `h1` using `ZLattice.rank ℝ L`. Establish `h2` using `(LinearEquiv.ofInjective P.toIntLinearMap hinj).finrank_eq`.

Rewrite using `[h2, h1, Module.finrank_pi_fintype]`. Simplify using `[Complex.finrank_real_complex, mul_comm]`.
-/
private theorem finrank_eq_two_mul_of_discrete_spanning_embedding {La : Type} [AddCommGroup La] [Module.Free ℤ La]
    [Module.Finite ℤ La] {g : ℕ} (P : La →+ (Fin g → ℂ)) (hinj : Function.Injective P)
    (hdisc : DiscreteTopology P.range) (hspan : Submodule.span ℝ (Set.range P) = ⊤) :
    Module.finrank ℤ La = 2 * g := by
  let L : Submodule ℤ (Fin g → ℂ) := LinearMap.range P.toIntLinearMap
  haveI : DiscreteTopology L := hdisc
  haveI : IsZLattice ℝ L := ⟨by simpa [L, LinearMap.coe_range] using hspan⟩
  have h1 := ZLattice.rank ℝ L
  have h2 := (LinearEquiv.ofInjective P.toIntLinearMap hinj).finrank_eq
  rw [h2, h1, Module.finrank_pi_fintype]
  simp [Complex.finrank_real_complex, mul_comm]

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField in
open scoped CategoryTheory.Obj TensorProduct in
open Matrix in
variable {g : ℕ} in
/- English proof (translation)
Set `a : Fin g → ℝ` to `fun j => if χ (bs (Sum.inr j)) = 1 then 0 else 1 / 2`. Set `c : Fin g → ℝ` to `fun j => if χ (bs (Sum.inl j)) = 1 then 0 else 1 / 2`. Use `⟨a, c, fun x => ?_⟩` and prove the remaining obligations. Establish `hhalf : Complex.exp (2 * Real.pi * Complex.I * ((1 / 2 : ℝ) : ℂ)) = -1`. Rewrite using `[← Complex.exp_pi_mul_I]`.

Use `congr 1`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Establish `hhalf' : Complex.exp (2 * Real.pi * Complex.I * (-((1 / 2 : ℝ) : ℂ))) = -1`. Rewrite using `[mul_neg, Complex.exp_neg, hhalf]`.

Evaluate the numerical expressions. Apply the tactic sequence `refine _root_.GlobalTheory.HolTheta.eq_of_cocycle (ψ := fun x => _root_.GlobalTheory.CanTh.canMult a c (fun j => bs.repr x (Sum.inr j)) (fun j => bs.repr x (Sum.inl j))) bs (fun x y => (-1 : ℂ) ^ EF x y) (fun x y => zpow_ne_zero _ (by norm_num)) (fun x => by rcases hpm x with h | …`. Establish `hm : (fun j => bs.repr (x + y) (Sum.inr j)) = (fun j => bs.repr x (Sum.inr j)) + fun j => bs.repr y (Sum.inr j)` using `by ext j; simp`. Establish `hn : (fun j => bs.repr (x + y) (Sum.inl j)) = (fun j => bs.repr x (Sum.inl j)) + fun j => bs.repr y (Sum.inl j)` using `by ext j; simp`. Rewrite using `[hm, hn, _root_.GlobalTheory.HolTheta.canMult_add, hbs.apply_eq_sum halt]`.

Use `congr 2`. Simplify using `only [dotProduct, Finset.sum_sub_distrib]`. Break down `i with j | j` into its components or cases. Establish `hm : (fun k => bs.repr (bs (Sum.inl j)) (Sum.inr k)) = 0`. Use extensionality with `k`.

Simplify using `[Finsupp.single_apply]`. Establish `hn : (fun k => bs.repr (bs (Sum.inl j)) (Sum.inl k)) = Pi.single j 1`. Use extensionality with `k`. Simplify using `[Finsupp.single_apply, Pi.single_apply, eq_comm]`. Rewrite using `[hm, hn]`.

Establish `key : _root_.GlobalTheory.CanTh.canMult a c 0 (Pi.single j 1) = Complex.exp (2 * Real.pi * Complex.I * (-((c j : ℝ) : ℂ)))`. Unfold `_root_.GlobalTheory.CanTh.canMult`. Use `congr 1`. Simplify using `[dotProduct, Pi.single_apply]`. Rewrite using `[key]`.

Break down `hpm (bs (Sum.inl j)) with h | h` into its components or cases. Simplify using `[c, h]`. Simplify using `only [c, h, if_neg (show (-1 : ℂ) ≠ 1 by norm_num)]`. Conclude with `hhalf'.symm`. Establish `hm : (fun k => bs.repr (bs (Sum.inr j)) (Sum.inr k)) = Pi.single j 1`.

Use extensionality with `k`. Simplify using `[Finsupp.single_apply, Pi.single_apply, eq_comm]`. Establish `hn : (fun k => bs.repr (bs (Sum.inr j)) (Sum.inl k)) = 0`. Use extensionality with `k`. Simplify using `[Finsupp.single_apply]`.

Rewrite using `[hm, hn]`. Establish `key : _root_.GlobalTheory.CanTh.canMult a c (Pi.single j 1) 0 = Complex.exp (2 * Real.pi * Complex.I * ((a j : ℝ) : ℂ))`. Unfold `_root_.GlobalTheory.CanTh.canMult`. Use `congr 1`. Simplify using `[dotProduct, Pi.single_apply]`.

Rewrite using `[key]`. Break down `hpm (bs (Sum.inr j)) with h | h` into its components or cases. Simplify using `[a, h]`. Simplify using `only [a, h, if_neg (show (-1 : ℂ) ≠ 1 by norm_num)]`. Conclude with `hhalf.symm`.
-/
private theorem exists_characteristics_eq_canMult_of_semicharacter {La : Type} [AddCommGroup La] {g : ℕ}
    (EF : LinearMap.BilinForm ℤ La) (bs : Module.Basis (Fin g ⊕ Fin g) ℤ La)
    (hbs : _root_.GlobalTheory.IsSymplecticBasis EF bs) (halt : EF.IsAlt) (χ : La → ℂ)
    (hpm : ∀ x, χ x = 1 ∨ χ x = -1) (hχ : ∀ x y, χ (x + y) = χ x * χ y * (-1) ^ EF x y) :
    ∃ a c : Fin g → ℝ, ∀ x, χ x = _root_.GlobalTheory.CanTh.canMult a c
      (fun j => bs.repr x (Sum.inr j)) (fun j => bs.repr x (Sum.inl j)) := by
  classical
  let a : Fin g → ℝ := fun j => if χ (bs (Sum.inr j)) = 1 then 0 else 1 / 2
  let c : Fin g → ℝ := fun j => if χ (bs (Sum.inl j)) = 1 then 0 else 1 / 2
  refine ⟨a, c, fun x => ?_⟩
  have hhalf : Complex.exp (2 * Real.pi * Complex.I * ((1 / 2 : ℝ) : ℂ)) = -1 := by
    rw [← Complex.exp_pi_mul_I]; congr 1; push_cast; ring
  have hhalf' : Complex.exp (2 * Real.pi * Complex.I * (-((1 / 2 : ℝ) : ℂ))) = -1 := by
    rw [mul_neg, Complex.exp_neg, hhalf]; norm_num
  refine _root_.GlobalTheory.HolTheta.eq_of_cocycle (ψ := fun x => _root_.GlobalTheory.CanTh.canMult a c
      (fun j => bs.repr x (Sum.inr j)) (fun j => bs.repr x (Sum.inl j))) bs
    (fun x y => (-1 : ℂ) ^ EF x y)
    (fun x y => zpow_ne_zero _ (by norm_num))
    (fun x => by rcases hpm x with h | h <;> rw [h] <;> norm_num)
    (fun x => by unfold _root_.GlobalTheory.CanTh.canMult; exact Complex.exp_ne_zero _)
    hχ (fun x y => ?_) (fun i => ?_) x
  · have hm : (fun j => bs.repr (x + y) (Sum.inr j)) =
        (fun j => bs.repr x (Sum.inr j)) + fun j => bs.repr y (Sum.inr j) := by ext j; simp
    have hn : (fun j => bs.repr (x + y) (Sum.inl j)) =
        (fun j => bs.repr x (Sum.inl j)) + fun j => bs.repr y (Sum.inl j) := by ext j; simp
    rw [hm, hn, _root_.GlobalTheory.HolTheta.canMult_add, hbs.apply_eq_sum halt]
    congr 2
    simp only [dotProduct, Finset.sum_sub_distrib]
  · rcases i with j | j
    · have hm : (fun k => bs.repr (bs (Sum.inl j)) (Sum.inr k)) = 0 := by
        ext k; simp [Finsupp.single_apply]
      have hn : (fun k => bs.repr (bs (Sum.inl j)) (Sum.inl k)) = Pi.single j 1 := by
        ext k; simp [Finsupp.single_apply, Pi.single_apply, eq_comm]
      rw [hm, hn]
      have key : _root_.GlobalTheory.CanTh.canMult a c 0 (Pi.single j 1) =
          Complex.exp (2 * Real.pi * Complex.I * (-((c j : ℝ) : ℂ))) := by
        unfold _root_.GlobalTheory.CanTh.canMult
        congr 1
        simp [dotProduct, Pi.single_apply]
      rw [key]
      rcases hpm (bs (Sum.inl j)) with h | h
      · simp [c, h]
      · simp only [c, h, if_neg (show (-1 : ℂ) ≠ 1 by norm_num)]
        exact hhalf'.symm
    · have hm : (fun k => bs.repr (bs (Sum.inr j)) (Sum.inr k)) = Pi.single j 1 := by
        ext k; simp [Finsupp.single_apply, Pi.single_apply, eq_comm]
      have hn : (fun k => bs.repr (bs (Sum.inr j)) (Sum.inl k)) = 0 := by
        ext k; simp [Finsupp.single_apply]
      rw [hm, hn]
      have key : _root_.GlobalTheory.CanTh.canMult a c (Pi.single j 1) 0 =
          Complex.exp (2 * Real.pi * Complex.I * ((a j : ℝ) : ℂ)) := by
        unfold _root_.GlobalTheory.CanTh.canMult
        congr 1
        simp [dotProduct, Pi.single_apply]
      rw [key]
      rcases hpm (bs (Sum.inr j)) with h | h
      · simp [a, h]
      · simp only [a, h, if_neg (show (-1 : ℂ) ≠ 1 by norm_num)]
        exact hhalf.symm

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField in
open scoped CategoryTheory.Obj TensorProduct in
open Matrix in
variable {g : ℕ} in
/- English proof (translation)
The claim follows from `(LinearMap.toContinuousLinearMap (Matrix.mulVecLin M)).differentiable`.
-/
private theorem differentiable_matrix_mulVec (M : Matrix (Fin g) (Fin g) ℂ) :
    Differentiable ℂ (fun z : Fin g → ℂ => M *ᵥ z) :=
  (LinearMap.toContinuousLinearMap (Matrix.mulVecLin M)).differentiable

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField in
open scoped CategoryTheory.Obj TensorProduct in
open Matrix in
variable {g : ℕ} in

/- English proof (translation)
Introduce `La _ _ _ EF χ g m N' B P Hm hN hbij hpm hχ hB hPd hlat`. Distinguish the cases in `hne : B.Nonempty`. Use `swap`. Use `⟨fun _ _ => 0, fun b hb => (hne ⟨b, hb⟩).elim, fun x => ?_⟩` and prove the remaining obligations. Rewrite using `[Set.not_nonempty_iff_eq_empty.mp hne]`.

Conclude with `differentiableOn_empty`. Take `⟨b0, hb0⟩` from `hne`. Take `⟨hinj0, hdisc0, hspan0, hH0, -, hEF0⟩` from `hlat b0 hb0`. Establish `halt : EF.IsAlt` using `fun x => by`. Establish `h` using `hEF0 x x`.

Establish `him : (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm (Hm b0) (P b0 x) (P b0 x)).im = 0`. Establish `hs` using `_root_.GlobalTheory.SiegelNormalForm.form_conj hH0 (P b0 x) (P b0 x)`. Unfold `_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm`. Conclude with `Complex.conj_eq_iff_im.mp hs`. Rewrite `h` using `[him]`.

Conclude with `h.symm` after adjusting the coercions. Establish `hrank` using `finrank_eq_two_mul_of_discrete_spanning_embedding (P b0) hinj0 hdisc0 hspan0`. Take `⟨bs, hbs⟩` from `_root_.GlobalTheory.exists_isSymplecticBasis_of_finrank halt hbij hrank`. Take `⟨a, c, hac⟩` from `exists_characteristics_eq_canMult_of_semicharacter EF bs hbs halt χ hpm hχ`. Use `set A : (Fin m → ℂ) → Matrix (Fin g) (Fin g) ℂ := fun b => Matrix.of fun i j => P b (bs (Sum.inr j)) i with hAdef`.

Use `set F : (Fin m → ℂ) → Matrix (Fin g) (Fin g) ℂ := fun b => Matrix.of fun i j => P b (bs (Sum.inl j)) i with hFdef`. Use `set τ : (Fin m → ℂ) → Matrix (Fin g) (Fin g) ℂ := fun b => (A b)⁻¹ * F b with hτdef`. Establish `hnf : ∀ b ∈ B, IsUnit (A b).det ∧ (τ b).IsSymm ∧ ((τ b).map Complex.im).PosDef ∧ ∀ z w, _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm (Hm b) z w = _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm (_root_.GlobalTheory.CanTh.imInv (τ b)) ((A b)⁻¹ *ᵥ z) (( …`. Introduce `b hb`. Take `⟨-, -, -, hH, hpos, hEF⟩` from `hlat b hb`.

Use `_root_.GlobalTheory.HolTheta.normal_form (Hm b) (fun j => P b (bs (Sum.inr j))) (fun j => P b (bs (Sum.inl j))) hH hpos ?_ ?_ ?_ rfl rfl` and prove the remaining obligations. Introduce `j k`. Rewrite using `[hEF, hbs.right_right]`. Simplify using the standard rewrite rules. Introduce `j k`.

Rewrite using `[hEF, hbs.left_left]`. Simplify using the standard rewrite rules. Introduce `j k`. Rewrite using `[hEF, hbs.right_left halt, Matrix.one_apply]`. Apply the tactic sequence `split_ifs <;> simp`.

Establish `hsumP : ∀ b x, P b x = A b *ᵥ (fun i => (bs.repr x (Sum.inr i) : ℂ)) + F b *ᵥ (fun i => (bs.repr x (Sum.inl i) : ℂ))`. Introduce `b x`. Use `conv_lhs => rw [← bs.sum_repr x]`. Rewrite using `[map_sum, Fintype.sum_sum_type, add_comm]`. Use extensionality with `i`.

Simplify using `[Matrix.mulVec, dotProduct, A, F, Finset.sum_apply, mul_comm]`. Establish `hlat_pt : ∀ b ∈ B, ∀ x, (A b)⁻¹ *ᵥ P b x = (fun i => (bs.repr x (Sum.inr i) : ℂ)) + τ b *ᵥ (fun i => (bs.repr x (Sum.inl i) : ℂ))`. Introduce `b hb x`. Establish `hu` using `(hnf b hb).1`. Rewrite using `[hsumP, Matrix.mulVec_add, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hu, Matrix.one_mulVec, Matrix.mulVec_mulVec]`.

Use `⟨fun b z => _root_.GlobalTheory.CanTh.canTh (τ b) a c ((A b)⁻¹ *ᵥ z), ?_, ?_⟩` and prove the remaining obligations. Introduce `b hb`. Take `⟨hu, hs, hpd, hform⟩` from `hnf b hb`. Use `⟨?_, (_root_.GlobalTheory.CanTh.differentiable_canTh hpd a c).comp (differentiable_matrix_mulVec _), fun x z => ?_⟩` and prove the remaining obligations. Introduce `h`.

Apply `_root_.GlobalTheory.CanTh.canTh_ne_zero hs hpd a c` to reduce the goal to its premises. Use function extensionality and compare the values at `ζ`. Use `congrFun h (A b *ᵥ ζ)` as an intermediate fact. Simplify `this` using `[Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hu]`. Use `show _root_.GlobalTheory.CanTh.canTh (τ b) a c ((A b)⁻¹ *ᵥ (z + P b x)) = _`.

Rewrite using `[Matrix.mulVec_add, hlat_pt b hb x, _root_.GlobalTheory.CanTh.canTh_add_period hs hpd a c _ _ rfl, hac x, hform z, hform (P b x), hlat_pt b hb x]`. Introduce `x set a' : Fin g → ℝ := fun i => (bs.repr x (Sum.inl i) : ℝ) / N' with ha' set b' : Fin g → ℝ := fun i => (bs.repr x (Sum.inr i) : ℝ) / N' with hb'`. Establish `hNc : (N' : ℂ) ≠ 0` using `by exact_mod_cast hN.ne'`. Establish `hAd : ∀ i j, DifferentiableOn ℂ (fun b => A b i j) B` using `fun i j => differentiableOn_pi.1 (hPd (bs (Sum.inr j))) i`. Establish `hFd : ∀ i j, DifferentiableOn ℂ (fun b => F b i j) B` using `fun i j => differentiableOn_pi.1 (hPd (bs (Sum.inl j))) i`.

Establish `hinvd` using `_root_.GlobalTheory.RiemannRel.differentiableOn_left_inverse A (fun b => (A b)⁻¹) hAd (fun b hb => Matrix.nonsing_inv_mul _ (hnf b hb).1)`. Establish `hτd : ∀ i j, DifferentiableOn ℂ (fun b => τ b i j) B`. Introduce `i j`. Simplify using `only [hτdef, Matrix.mul_apply]`. Conclude with `DifferentiableOn.fun_sum fun l _ => (hinvd i l).mul (hFd l j)`.

Establish `hdom : ∀ b ∈ B, τ b ∈ _root_.ReciprocityTheory.PTheta.ThetaDomain (Fin g)` using `fun b hb => _root_.GlobalTheory.CanTh.mem_thetaDomain (hnf b hb).2.2.1`. Use `(DifferentiableOn.const_mul (_root_.GlobalTheory.CanTh.differentiableOn_thetaChar hτd (differentiableOn_const 0) hdom (a + a') (c + b')) (_root_.GlobalTheory.CanTh.translConst c a' b')).congr fun b hb => ?_` and prove the remaining obligations. Take `⟨hu, hs, hpd, hform⟩` from `hnf b hb`. Use `set l := (fun i => (bs.repr x (Sum.inr i) : ℂ)) + τ b *ᵥ (fun i => (bs.repr x (Sum.inl i) : ℂ)) with hldef`. Establish `hl : (A b)⁻¹ *ᵥ P b x = l` using `hlat_pt b hb x`.

Establish `e1 : (fun i => ((a' i : ℝ) : ℂ)) = (N' : ℂ)⁻¹ • fun i => (bs.repr x (Sum.inl i) : ℂ)`. Use extensionality with `i`. Simplify using `[ha', div_eq_inv_mul]`. Establish `e2 : (fun i => ((b' i : ℝ) : ℂ)) = (N' : ℂ)⁻¹ • fun i => (bs.repr x (Sum.inr i) : ℂ)`. Use extensionality with `i`.

Simplify using `[hb', div_eq_inv_mul]`. Establish `hy : (N' : ℂ)⁻¹ • l = (fun i => ((b' i : ℝ) : ℂ)) + τ b *ᵥ fun i => ((a' i : ℝ) : ℂ)`. Rewrite using `[e1, e2, Matrix.mulVec_smul, hldef, smul_add]`. Establish `ht` using `_root_.GlobalTheory.CanTh.canTh_translate hs hpd a c a' b' hy 0`. Use `set M := _root_.GlobalTheory.CanTh.imInv (τ b)`.

Establish `hzero : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm M 0 ((N' : ℂ)⁻¹ • l) = 0` using `by unfold _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm; simp`. Establish `hscal : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm M ((N' : ℂ)⁻¹ • l) ((N' : ℂ)⁻¹ • l) = ((N' : ℂ)⁻¹) ^ 2 * _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm M l l`. Unfold `_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm`. Simplify using `[smul_dotProduct, Matrix.mulVec_smul, dotProduct_smul, star_smul]`. Expand and normalize the polynomial expressions, which then agree.

Establish `htheta0 : _root_.GlobalTheory.CanTh.canTh (τ b) (a + a') (c + b') 0 = _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.thetaChar (τ b) (fun i => ((a + a') i : ℂ)) (fun i => ((c + b') i : ℂ)) 0`. Unfold `_root_.GlobalTheory.CanTh.canTh`. Simplify using the standard rewrite rules. Rewrite `ht` using `[zero_add, hzero, hscal]`. Use `show Complex.exp (-(Real.pi / 2 / (N' : ℂ) ^ 2) * _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm (Hm b) (P b x) (P b x)) * _root_.GlobalTheory.CanTh.canTh (τ b) a c ((A b)⁻¹ *ᵥ ((N' : ℂ)⁻¹ • P b x)) = _`.

Rewrite using `[Matrix.mulVec_smul, hl, hform, hl, ← htheta0, ← ht]`. Use `congr 2`. Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree.
-/
theorem _root_.GlobalTheory.HolTheta.exists_theta_holomorphic : ∀ (La : Type) [AddCommGroup La] [Module.Free ℤ La] [Module.Finite ℤ La] (EF : LinearMap.BilinForm ℤ La) (χ : La → ℂ) (g m N' : ℕ) (B : Set (Fin m → ℂ)) (P : (Fin m → ℂ) → (La →+ (Fin g → ℂ))) (Hm : (Fin m → ℂ) → Matrix (Fin g) (Fin g) ℂ), 0 < N' → Function.Bijective EF → (∀ x, χ x = 1 ∨ χ x = -1) → (∀ x y, χ (x + y) = χ x * χ y * (-1) ^ EF x y) → IsOpen B → (∀ x, DifferentiableOn ℂ (fun b => P b x) B) → (∀ b ∈ B, Function.Injective (P b) ∧ DiscreteTopology (P b).range ∧ Submodule.span ℝ (Set.range (P b)) = ⊤ ∧ (Hm b).IsHermitian ∧ (∀ z : Fin g → ℂ, z ≠ 0 → 0 < (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm (Hm b) z z).re) ∧ ∀ x y, (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm (Hm b) (P b x) (P b y)).im = EF x y) → ∃ θ : (Fin m → ℂ) → (Fin g → ℂ) → ℂ, (∀ b ∈ B, θ b ≠ 0 ∧ Differentiable ℂ (θ b) ∧ ∀ x z, θ b (z + P b x) = χ x * Complex.exp (Real.pi * _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm (Hm b) z (P b x) + Real.pi / 2 * _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm (Hm b) (P b x) (P b x)) * θ b z) ∧ ∀ x, DifferentiableOn ℂ (fun b => Complex.exp (-(Real.pi / 2 / (N' : ℂ) ^ 2) * _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm (Hm b) (P b x) (P b x)) * θ b ((N' : ℂ)⁻¹ • P b x)) B := by
  intro La _ _ _ EF χ g m N' B P Hm hN hbij hpm hχ hB hPd hlat
  classical
  by_cases hne : B.Nonempty
  swap
  · refine ⟨fun _ _ => 0, fun b hb => (hne ⟨b, hb⟩).elim, fun x => ?_⟩
    rw [Set.not_nonempty_iff_eq_empty.mp hne]
    exact differentiableOn_empty
  obtain ⟨b0, hb0⟩ := hne
  obtain ⟨hinj0, hdisc0, hspan0, hH0, -, hEF0⟩ := hlat b0 hb0
  have halt : EF.IsAlt := fun x => by
    have h := hEF0 x x
    have him : (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm (Hm b0) (P b0 x) (P b0 x)).im = 0 := by
      have hs := _root_.GlobalTheory.SiegelNormalForm.form_conj hH0 (P b0 x) (P b0 x)
      unfold _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm
      exact Complex.conj_eq_iff_im.mp hs
    rw [him] at h
    exact_mod_cast h.symm
  have hrank := finrank_eq_two_mul_of_discrete_spanning_embedding (P b0) hinj0 hdisc0 hspan0
  obtain ⟨bs, hbs⟩ := _root_.GlobalTheory.exists_isSymplecticBasis_of_finrank halt hbij hrank
  obtain ⟨a, c, hac⟩ := exists_characteristics_eq_canMult_of_semicharacter EF bs hbs halt χ hpm hχ
  set A : (Fin m → ℂ) → Matrix (Fin g) (Fin g) ℂ :=
    fun b => Matrix.of fun i j => P b (bs (Sum.inr j)) i with hAdef
  set F : (Fin m → ℂ) → Matrix (Fin g) (Fin g) ℂ :=
    fun b => Matrix.of fun i j => P b (bs (Sum.inl j)) i with hFdef
  set τ : (Fin m → ℂ) → Matrix (Fin g) (Fin g) ℂ := fun b => (A b)⁻¹ * F b with hτdef
  have hnf : ∀ b ∈ B, IsUnit (A b).det ∧ (τ b).IsSymm ∧ ((τ b).map Complex.im).PosDef ∧
      ∀ z w, _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm (Hm b) z w =
        _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm (_root_.GlobalTheory.CanTh.imInv (τ b)) ((A b)⁻¹ *ᵥ z) ((A b)⁻¹ *ᵥ w) := by
    intro b hb
    obtain ⟨-, -, -, hH, hpos, hEF⟩ := hlat b hb
    refine _root_.GlobalTheory.HolTheta.normal_form (Hm b) (fun j => P b (bs (Sum.inr j)))
      (fun j => P b (bs (Sum.inl j))) hH hpos ?_ ?_ ?_ rfl rfl
    · intro j k; rw [hEF, hbs.right_right]; simp
    · intro j k; rw [hEF, hbs.left_left]; simp
    · intro j k
      rw [hEF, hbs.right_left halt, Matrix.one_apply]
      split_ifs <;> simp
  have hsumP : ∀ b x, P b x = A b *ᵥ (fun i => (bs.repr x (Sum.inr i) : ℂ)) +
      F b *ᵥ (fun i => (bs.repr x (Sum.inl i) : ℂ)) := by
    intro b x
    conv_lhs => rw [← bs.sum_repr x]
    rw [map_sum, Fintype.sum_sum_type, add_comm]
    ext i
    simp [Matrix.mulVec, dotProduct, A, F, Finset.sum_apply, mul_comm]
  have hlat_pt : ∀ b ∈ B, ∀ x, (A b)⁻¹ *ᵥ P b x = (fun i => (bs.repr x (Sum.inr i) : ℂ)) +
      τ b *ᵥ (fun i => (bs.repr x (Sum.inl i) : ℂ)) := by
    intro b hb x
    have hu := (hnf b hb).1
    rw [hsumP, Matrix.mulVec_add, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hu,
      Matrix.one_mulVec, Matrix.mulVec_mulVec]
  refine ⟨fun b z => _root_.GlobalTheory.CanTh.canTh (τ b) a c ((A b)⁻¹ *ᵥ z), ?_, ?_⟩
  · intro b hb
    obtain ⟨hu, hs, hpd, hform⟩ := hnf b hb
    refine ⟨?_, (_root_.GlobalTheory.CanTh.differentiable_canTh hpd a c).comp
      (differentiable_matrix_mulVec _), fun x z => ?_⟩
    · intro h
      apply _root_.GlobalTheory.CanTh.canTh_ne_zero hs hpd a c
      funext ζ
      have := congrFun h (A b *ᵥ ζ)
      simpa [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hu] using this
    · show _root_.GlobalTheory.CanTh.canTh (τ b) a c ((A b)⁻¹ *ᵥ (z + P b x)) = _
      rw [Matrix.mulVec_add, hlat_pt b hb x, _root_.GlobalTheory.CanTh.canTh_add_period hs hpd a c
        _ _ rfl, hac x, hform z, hform (P b x), hlat_pt b hb x]
  · intro x
    set a' : Fin g → ℝ := fun i => (bs.repr x (Sum.inl i) : ℝ) / N' with ha'
    set b' : Fin g → ℝ := fun i => (bs.repr x (Sum.inr i) : ℝ) / N' with hb'
    have hNc : (N' : ℂ) ≠ 0 := by exact_mod_cast hN.ne'
    have hAd : ∀ i j, DifferentiableOn ℂ (fun b => A b i j) B := fun i j =>
      differentiableOn_pi.1 (hPd (bs (Sum.inr j))) i
    have hFd : ∀ i j, DifferentiableOn ℂ (fun b => F b i j) B := fun i j =>
      differentiableOn_pi.1 (hPd (bs (Sum.inl j))) i
    have hinvd := _root_.GlobalTheory.RiemannRel.differentiableOn_left_inverse A (fun b => (A b)⁻¹) hAd
      (fun b hb => Matrix.nonsing_inv_mul _ (hnf b hb).1)
    have hτd : ∀ i j, DifferentiableOn ℂ (fun b => τ b i j) B := by
      intro i j
      simp only [hτdef, Matrix.mul_apply]
      exact DifferentiableOn.fun_sum fun l _ => (hinvd i l).mul (hFd l j)
    have hdom : ∀ b ∈ B, τ b ∈ _root_.ReciprocityTheory.PTheta.ThetaDomain (Fin g) := fun b hb =>
      _root_.GlobalTheory.CanTh.mem_thetaDomain (hnf b hb).2.2.1
    refine (DifferentiableOn.const_mul (_root_.GlobalTheory.CanTh.differentiableOn_thetaChar hτd
      (differentiableOn_const 0) hdom (a + a') (c + b'))
      (_root_.GlobalTheory.CanTh.translConst c a' b')).congr fun b hb => ?_
    obtain ⟨hu, hs, hpd, hform⟩ := hnf b hb
    set l := (fun i => (bs.repr x (Sum.inr i) : ℂ)) + τ b *ᵥ (fun i => (bs.repr x (Sum.inl i) : ℂ))
      with hldef
    have hl : (A b)⁻¹ *ᵥ P b x = l := hlat_pt b hb x
    have e1 : (fun i => ((a' i : ℝ) : ℂ)) = (N' : ℂ)⁻¹ • fun i => (bs.repr x (Sum.inl i) : ℂ) := by
      ext i; simp [ha', div_eq_inv_mul]
    have e2 : (fun i => ((b' i : ℝ) : ℂ)) = (N' : ℂ)⁻¹ • fun i => (bs.repr x (Sum.inr i) : ℂ) := by
      ext i; simp [hb', div_eq_inv_mul]
    have hy : (N' : ℂ)⁻¹ • l = (fun i => ((b' i : ℝ) : ℂ)) + τ b *ᵥ fun i => ((a' i : ℝ) : ℂ) := by
      rw [e1, e2, Matrix.mulVec_smul, hldef, smul_add]
    have ht := _root_.GlobalTheory.CanTh.canTh_translate hs hpd a c a' b' hy 0
    set M := _root_.GlobalTheory.CanTh.imInv (τ b)
    have hzero : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm M 0 ((N' : ℂ)⁻¹ • l) = 0 := by unfold _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm; simp
    have hscal : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm M ((N' : ℂ)⁻¹ • l) ((N' : ℂ)⁻¹ • l) = ((N' : ℂ)⁻¹) ^ 2 * _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm M l l := by
      unfold _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm
      simp [smul_dotProduct, Matrix.mulVec_smul, dotProduct_smul, star_smul]
      ring
    have htheta0 : _root_.GlobalTheory.CanTh.canTh (τ b) (a + a') (c + b') 0 =
        _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.thetaChar (τ b) (fun i => ((a + a') i : ℂ)) (fun i => ((c + b') i : ℂ)) 0 := by
      unfold _root_.GlobalTheory.CanTh.canTh; simp
    rw [zero_add, hzero, hscal] at ht
    show Complex.exp (-(Real.pi / 2 / (N' : ℂ) ^ 2) * _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm (Hm b) (P b x) (P b x)) *
      _root_.GlobalTheory.CanTh.canTh (τ b) a c ((A b)⁻¹ *ᵥ ((N' : ℂ)⁻¹ • P b x)) = _
    rw [Matrix.mulVec_smul, hl, hform, hl, ← htheta0, ← ht]
    congr 2
    field_simp
    ring

end GlobalTheory.HolTheta

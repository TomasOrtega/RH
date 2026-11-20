import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.GCauchyStatement
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.FockTranslationLaws
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.IntegrableOnFundamentalDomainOfContinuous

namespace GlobalTheory

open Complex ReciprocityTheory.ChartRestriction.G.I2 MeasureTheory

namespace IsogenySum

open FockTranslation

variable {ι : Type} [Fintype ι]

/- English proof (translation)
Establish `hspan : ∀ v, (Hf v a).im = 0`. Introduce `v`. Establish `hv : v ∈ Submodule.span ℝ (Set.range Y.b)`. Rewrite using `[Y.b.span_eq]`. Conclude with `Submodule.mem_top`.

Proceed by induction on `hv using Submodule.span_induction with`. Consider the case `mem x hx => exact h x (Submodule.subset_span hx)`. Consider the case `zero => simp [Hf]`. Consider the case `add x y _ _ hx hy => rw [herm_add_left, Complex.add_im, hx, hy, add_zero]`. Consider the case `smul c x _ hx`.

Establish `e : Hf (c • x) a = (c : ℂ) * Hf x a`. Simplify using `only [Hf, PiLp.smul_apply, Complex.real_smul, Finset.mul_sum]`. Conclude with `Finset.sum_congr rfl fun i _ => by ring`. Rewrite using `[e, Complex.im_ofReal_mul, hx, mul_zero]`. Establish `h1` using `hspan (I • a)`.

Establish `e : Hf (I • a) a = I * Hf a a`. Simplify using `only [Hf, PiLp.smul_apply, smul_eq_mul, Finset.mul_sum]`. Conclude with `Finset.sum_congr rfl fun i _ => by ring`. Rewrite `h1` using `[e, Complex.I_mul_im, herm_self_re]`. Simplify using `using h1`.
-/
theorem eq_zero_of_im_lattice (Y : GT ι) {a : EuclideanSpace ℂ ι}
    (h : ∀ y ∈ lat Y.b, (Hf y a).im = 0) : a = 0 := by
  have hspan : ∀ v, (Hf v a).im = 0 := by
    intro v
    have hv : v ∈ Submodule.span ℝ (Set.range Y.b) := by
      rw [Y.b.span_eq]; exact Submodule.mem_top
    induction hv using Submodule.span_induction with
    | mem x hx => exact h x (Submodule.subset_span hx)
    | zero => simp [Hf]
    | add x y _ _ hx hy => rw [herm_add_left, Complex.add_im, hx, hy, add_zero]
    | smul c x _ hx =>
      have e : Hf (c • x) a = (c : ℂ) * Hf x a := by
        simp only [Hf, PiLp.smul_apply, Complex.real_smul, Finset.mul_sum]
        exact Finset.sum_congr rfl fun i _ => by ring
      rw [e, Complex.im_ofReal_mul, hx, mul_zero]
  have h1 := hspan (I • a)
  have e : Hf (I • a) a = I * Hf a a := by
    simp only [Hf, PiLp.smul_apply, smul_eq_mul, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [e, Complex.I_mul_im, herm_self_re] at h1
  simpa using h1

/- English proof (translation)
Establish `hfl : ∀ y ∈ lat Y.b, ((⌊(Hf y a).im⌋ : ℤ) : ℝ) = (Hf y a).im`. Introduce `y hy`. Take `⟨k, hk⟩` from `h y hy`. Rewrite using `[hk, Int.floor_intCast]`. Set `φ : lat Y.b →+ ℤ` to `{ toFun := fun y => ⌊(Hf (y : EuclideanSpace ℂ ι) a).im⌋ map_zero' := by simp [Hf] map_add' := by`.

Introduce `y y'`. Apply `Int.cast_injective (α := ℝ)` to reduce the goal to its premises. Use `push_cast`. Rewrite using `[hfl _ ((lat Y.b).add_mem y.2 y'.2), hfl _ y.2, hfl _ y'.2, herm_add_left, Complex.add_im] }`. Take `⟨x0, hx0, hφ⟩` from `Y.perfect φ`.

Establish `h0 : a + x0 = 0`. Apply `eq_zero_of_im_lattice Y` to reduce the goal to its premises. Introduce `y hy`. Use `hφ ⟨y, hy⟩` as an intermediate fact. Simplify using `only [φ, AddMonoidHom.coe_mk, ZeroHom.coe_mk] at this`.

Rewrite `this` using `[hfl y hy]`. Rewrite using `[herm_add_right, Complex.add_im, this, herm_im_swap x0 y]`. Expand and normalize the polynomial expressions, which then agree. Establish `: a = -x0` using `eq_neg_of_add_eq_zero_left h0`. Rewrite using `[this]`.

Conclude with `(lat Y.b).neg_mem hx0`.
-/
theorem mem_lattice_of_int (Y : GT ι) {a : EuclideanSpace ℂ ι}
    (h : ∀ y ∈ lat Y.b, ∃ k : ℤ, (Hf y a).im = k) : a ∈ lat Y.b := by
  have hfl : ∀ y ∈ lat Y.b, ((⌊(Hf y a).im⌋ : ℤ) : ℝ) = (Hf y a).im := by
    intro y hy
    obtain ⟨k, hk⟩ := h y hy
    rw [hk, Int.floor_intCast]
  let φ : lat Y.b →+ ℤ :=
    { toFun := fun y => ⌊(Hf (y : EuclideanSpace ℂ ι) a).im⌋
      map_zero' := by simp [Hf]
      map_add' := by
        intro y y'
        apply Int.cast_injective (α := ℝ)
        push_cast
        rw [hfl _ ((lat Y.b).add_mem y.2 y'.2), hfl _ y.2, hfl _ y'.2, herm_add_left,
          Complex.add_im] }
  obtain ⟨x0, hx0, hφ⟩ := Y.perfect φ
  have h0 : a + x0 = 0 := by
    apply eq_zero_of_im_lattice Y
    intro y hy
    have := hφ ⟨y, hy⟩
    simp only [φ, AddMonoidHom.coe_mk, ZeroHom.coe_mk] at this
    rw [hfl y hy] at this
    rw [herm_add_right, Complex.add_im, this, herm_im_swap x0 y]
    ring
  have : a = -x0 := eq_neg_of_add_eq_zero_left h0
  rw [this]
  exact (lat Y.b).neg_mem hx0

/- English proof (translation)
Establish `hN : ∀ i, ∃ N : ℤ, N ≠ 0 ∧ N • Y'.b i ∈ lat Y.b`. Introduce `i`. Establish `hi : Y'.b i ∈ lat Y'.b` using `Submodule.subset_span ⟨i, rfl⟩`. Use `choose r hr hr' using fun n : ℤ => hR' (n • Y'.b i) ((lat Y'.b).smul_mem n hi)`. Take `⟨n, m, hnm, e⟩` from `Finite.exists_ne_map_eq_of_infinite (fun n : ℤ => (⟨r n, hr n⟩ : R))`.

Establish `e' : r n = r m` using `congrArg Subtype.val e`. Use `⟨n - m, sub_ne_zero.2 hnm, ?_⟩` and prove the remaining obligations. Use `(lat Y.b).sub_mem (hr' n) (hr' m)` as an intermediate fact. Rewrite `this` using `[e', sub_sub_sub_cancel_right]`. Rewrite using `[sub_smul]` and apply the resulting hypothesis.

Use `choose N hN0 hN using hN`. Establish `hu : ∀ i, IsUnit (N i : ℝ)` using `fun i => (Int.cast_ne_zero.2 (hN0 i)).isUnit`. Use `⟨Y'.b.isUnitSMul hu, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[Submodule.span_le]`. Introduce and unpack `_ ⟨i, rfl⟩`.

Rewrite using `[Module.Basis.isUnitSMul_apply, Int.cast_smul_eq_zsmul]`. Conclude with `hN i`. Rewrite using `[Submodule.span_le]`. Introduce and unpack `_ ⟨i, rfl⟩`. Rewrite using `[Module.Basis.isUnitSMul_apply, Int.cast_smul_eq_zsmul]`.

Conclude with `(lat Y'.b).smul_mem _ (Submodule.subset_span ⟨i, rfl⟩)`.
-/
theorem exists_common_sublattice (Y Y' : GT ι) (R : Finset (EuclideanSpace ℂ ι))
    (hR' : ∀ y ∈ lat Y'.b, ∃ r ∈ R, y - r ∈ lat Y.b) :
    ∃ b : Module.Basis (Fin (2 * Fintype.card ι)) ℝ (EuclideanSpace ℂ ι),
      lat b ≤ lat Y.b ∧ lat b ≤ lat Y'.b := by
  have hN : ∀ i, ∃ N : ℤ, N ≠ 0 ∧ N • Y'.b i ∈ lat Y.b := by
    intro i
    have hi : Y'.b i ∈ lat Y'.b := Submodule.subset_span ⟨i, rfl⟩
    choose r hr hr' using fun n : ℤ => hR' (n • Y'.b i) ((lat Y'.b).smul_mem n hi)
    obtain ⟨n, m, hnm, e⟩ := Finite.exists_ne_map_eq_of_infinite (fun n : ℤ => (⟨r n, hr n⟩ : R))
    have e' : r n = r m := congrArg Subtype.val e
    refine ⟨n - m, sub_ne_zero.2 hnm, ?_⟩
    have := (lat Y.b).sub_mem (hr' n) (hr' m)
    rw [e', sub_sub_sub_cancel_right] at this
    rwa [sub_smul]
  choose N hN0 hN using hN
  have hu : ∀ i, IsUnit (N i : ℝ) := fun i => (Int.cast_ne_zero.2 (hN0 i)).isUnit
  refine ⟨Y'.b.isUnitSMul hu, ?_, ?_⟩
  · rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    rw [Module.Basis.isUnitSMul_apply, Int.cast_smul_eq_zsmul]
    exact hN i
  · rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    rw [Module.Basis.isUnitSMul_apply, Int.cast_smul_eq_zsmul]
    exact (lat Y'.b).smul_mem _ (Submodule.subset_span ⟨i, rfl⟩)

section

variable (U : ℕ → EuclideanSpace ℂ ι → (EuclideanSpace ℂ ι → ℂ) → EuclideanSpace ℂ ι → ℂ)
  (hU : ∀ (q : ℕ) a F v, U q a F v =
    cexp (q * Real.pi * Hf v a - q * Real.pi * Hf a a / 2) * F (v - a))
include hU

/- English proof (translation)
Establish `hk : Y.ka x * (starRingEnd ℂ) (Y.ka x) = 1`. Rewrite using `[Complex.mul_conj, Complex.normSq_eq_norm_sq, Y.ka_abs x hx]`. Simplify using the standard rewrite rules. Establish `e : ∀ z, v + x - z = (v - z) + x` using `fun z => by abel`. Simplify using `only [hU, e, hF.2 x hx, map_mul, ← Complex.exp_conj, map_add, map_sub, map_div₀, herm_conj, Complex.conj_ofReal, Nat.cast_one, one_mul, map_ofNat]`.

Establish `key : cexp (Real.pi * Hf (v + x) y - Real.pi * Hf y y / 2) * cexp (Real.pi * Hf (v - y) x + Real.pi * Hf x x / 2) * cexp (Real.pi * Hf y' (v + x) - Real.pi * Hf y' y' / 2) * cexp (Real.pi * Hf x (v - y') + Real.pi * Hf x x / 2) * cexp (-(Real.pi * Hf (v + x) (v + x))) = cexp (2 * …`. Simplify using `only [← Complex.exp_add]`. Use `congr 1`. Simplify using `only [herm_add_left, herm_add_right, herm_sub_left, herm_sub_right, Complex.sub_im]`. Rewrite using `[herm_sub_swap x y, herm_sub_swap x y']`.

Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Take the linear combination `(F (v - y) * (starRingEnd ℂ) (F (v - y'))) * key + (F (v - y) * (starRingEnd ℂ) (F (v - y')) * cexp (Real.pi * Hf (v + x) y - Real.pi * Hf y y / 2) * cexp (Real.pi * Hf (v - y) x + Real.pi * Hf x x / 2) * cexp (Real.pi * Hf y' (v + x) - Real.pi * Hf y' y' / 2) * cexp (Real.pi * H …`.
-/
theorem pairing_density_add (Y : GT ι) {F : EuclideanSpace ℂ ι → ℂ} (hF : F ∈ Y.Sec 1)
    (y y' : EuclideanSpace ℂ ι) {x : EuclideanSpace ℂ ι} (hx : x ∈ lat Y.b)
    (v : EuclideanSpace ℂ ι) :
    U 1 y F (v + x) * (starRingEnd ℂ) (U 1 y' F (v + x)) * cexp (-(Real.pi * Hf (v + x) (v + x))) =
      cexp (2 * Real.pi * I * (Hf x (y - y')).im) *
        (U 1 y F v * (starRingEnd ℂ) (U 1 y' F v) * cexp (-(Real.pi * Hf v v))) := by
  have hk : Y.ka x * (starRingEnd ℂ) (Y.ka x) = 1 := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, Y.ka_abs x hx]; simp
  have e : ∀ z, v + x - z = (v - z) + x := fun z => by abel
  simp only [hU, e, hF.2 x hx, map_mul, ← Complex.exp_conj, map_add, map_sub, map_div₀,
    herm_conj, Complex.conj_ofReal, Nat.cast_one, one_mul, map_ofNat]
  have key : cexp (Real.pi * Hf (v + x) y - Real.pi * Hf y y / 2) *
      cexp (Real.pi * Hf (v - y) x + Real.pi * Hf x x / 2) *
      cexp (Real.pi * Hf y' (v + x) - Real.pi * Hf y' y' / 2) *
      cexp (Real.pi * Hf x (v - y') + Real.pi * Hf x x / 2) *
      cexp (-(Real.pi * Hf (v + x) (v + x))) =
      cexp (2 * Real.pi * I * (Hf x (y - y')).im) *
      cexp (Real.pi * Hf v y - Real.pi * Hf y y / 2) *
      cexp (Real.pi * Hf y' v - Real.pi * Hf y' y' / 2) * cexp (-(Real.pi * Hf v v)) := by
    simp only [← Complex.exp_add]
    congr 1
    simp only [herm_add_left, herm_add_right, herm_sub_left, herm_sub_right, Complex.sub_im]
    rw [herm_sub_swap x y, herm_sub_swap x y']
    push_cast
    ring
  linear_combination (F (v - y) * (starRingEnd ℂ) (F (v - y'))) * key +
    (F (v - y) * (starRingEnd ℂ) (F (v - y')) *
      cexp (Real.pi * Hf (v + x) y - Real.pi * Hf y y / 2) *
      cexp (Real.pi * Hf (v - y) x + Real.pi * Hf x x / 2) *
      cexp (Real.pi * Hf y' (v + x) - Real.pi * Hf y' y' / 2) *
      cexp (Real.pi * Hf x (v - y') + Real.pi * Hf x x / 2) *
      cexp (-(Real.pi * Hf (v + x) (v + x)))) * hk

/- English proof (translation)
Establish `e : U 1 a F = fun v => cexp ((1 : ℕ) * Real.pi * Hf v a - (1 : ℕ) * Real.pi * Hf a a / 2) * F (v - a)`. Use function extensionality and compare the values at `fun v => hU 1 a F v`. Rewrite using `[e]`. Use `herm_differentiable a` as an intermediate fact. Use `fun_prop`.
-/
theorem translate_differentiable {F : EuclideanSpace ℂ ι → ℂ} (hF : Differentiable ℂ F)
    (a : EuclideanSpace ℂ ι) : Differentiable ℂ (U 1 a F) := by
  have e : U 1 a F = fun v =>
      cexp ((1 : ℕ) * Real.pi * Hf v a - (1 : ℕ) * Real.pi * Hf a a / 2) * F (v - a) :=
    funext fun v => hU 1 a F v
  rw [e]
  have := herm_differentiable a
  fun_prop

/- English proof (translation)
Establish `h1` using `(translate_differentiable U hU hF y).continuous`. Establish `h2` using `(translate_differentiable U hU hF y').continuous`. Simplify using `only [herm_self]`. Use `fun_prop`.
-/
theorem pairing_density_continuous {F : EuclideanSpace ℂ ι → ℂ} (hF : Differentiable ℂ F)
    (y y' : EuclideanSpace ℂ ι) : Continuous fun v =>
      U 1 y F v * (starRingEnd ℂ) (U 1 y' F v) * cexp (-(Real.pi * Hf v v)) := by
  have h1 := (translate_differentiable U hU hF y).continuous
  have h2 := (translate_differentiable U hU hF y').continuous
  simp only [herm_self]
  fun_prop

/- English proof (translation)
Choose the witnesses or unpack the hypotheses as in `⟨x, hx, hx'⟩ : ∃ x ∈ lat Y.b, cexp (2 * Real.pi * I * (Hf x (y - y')).im) ≠ 1 := by`. Assume the negation of the conclusion as `hcon`. Use `push Not at hcon`. Use `hne (mem_lattice_of_int Y fun x hx => ?_)` and prove the remaining obligations. Take `⟨k, hk⟩` from `Complex.exp_eq_one_iff.1 (hcon x hx)`.

Use `⟨k, ?_⟩` and prove the remaining obligations. Rewrite `hk` using `[mul_comm (k : ℂ)]`. Use `mul_left_cancel₀ Complex.two_pi_I_ne_zero hk` as an intermediate fact. Conclude with `this` after adjusting the coercions. Establish `h` using `setIntegral_fundamentalDomain_add_right volume b (fun v => U 1 y F v * (starRingEnd ℂ) (U 1 y' F v) * cexp (-(Real.pi * Hf v v))) (fun γ hγ v => by`.

Take `⟨k, hk⟩` from `hint γ hγ`. Simplify using `only [pairing_density_add U hU Y hF y y' (hb hγ), hk]`. Rewrite using `[mul_comm _ ((k : ℝ) : ℂ), Complex.ofReal_intCast, Complex.exp_int_mul_two_pi_mul_I, one_mul]) x`. Simplify using `only [pairing_density_add U hU Y hF y y' hx] at h`. Rewrite `h` using `[integral_const_mul]`.

Establish `h2` using `sub_eq_zero.2 h`. Rewrite `h2` using `[← sub_one_mul]`. Conclude with `(mul_eq_zero.1 h2).resolve_left (sub_ne_zero.2 hx')`.
-/
theorem integral_pairing_density_eq_zero (Y : GT ι) {F : EuclideanSpace ℂ ι → ℂ}
    (hF : F ∈ Y.Sec 1) {κ : Type} [Fintype κ] (b : Module.Basis κ ℝ (EuclideanSpace ℂ ι))
    (hb : lat b ≤ lat Y.b) (y y' : EuclideanSpace ℂ ι)
    (hint : ∀ x ∈ lat b, ∃ k : ℤ, (Hf x (y - y')).im = k) (hne : y - y' ∉ lat Y.b) :
    ∫ v in ZSpan.fundamentalDomain b,
      U 1 y F v * (starRingEnd ℂ) (U 1 y' F v) * cexp (-(Real.pi * Hf v v)) = 0 := by
  obtain ⟨x, hx, hx'⟩ : ∃ x ∈ lat Y.b, cexp (2 * Real.pi * I * (Hf x (y - y')).im) ≠ 1 := by
    by_contra hcon
    push Not at hcon
    refine hne (mem_lattice_of_int Y fun x hx => ?_)
    obtain ⟨k, hk⟩ := Complex.exp_eq_one_iff.1 (hcon x hx)
    refine ⟨k, ?_⟩
    rw [mul_comm (k : ℂ)] at hk
    have := mul_left_cancel₀ Complex.two_pi_I_ne_zero hk
    exact_mod_cast this
  have h := setIntegral_fundamentalDomain_add_right volume b
    (fun v => U 1 y F v * (starRingEnd ℂ) (U 1 y' F v) * cexp (-(Real.pi * Hf v v)))
    (fun γ hγ v => by
      obtain ⟨k, hk⟩ := hint γ hγ
      simp only [pairing_density_add U hU Y hF y y' (hb hγ), hk]
      rw [mul_comm _ ((k : ℝ) : ℂ), Complex.ofReal_intCast, Complex.exp_int_mul_two_pi_mul_I,
        one_mul]) x
  simp only [pairing_density_add U hU Y hF y y' hx] at h
  rw [integral_const_mul] at h
  have h2 := sub_eq_zero.2 h
  rw [← sub_one_mul] at h2
  exact (mul_eq_zero.1 h2).resolve_left (sub_ne_zero.2 hx')

/- English proof (translation)
Establish `h1` using `(fock_translation_laws U hU 1).1 x y F`. Establish `e : U 1 x (Y.ka y • U 1 y F) = Y.ka y • U 1 x (U 1 y F)`. Use function extensionality and compare the values at `v`. Simplify using `only [Pi.smul_apply, smul_eq_mul, hU 1 x]`. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[e, h1, hY x hx y hy, smul_smul, smul_smul]`. Use `congr 2`. Take `⟨k, hk⟩` from `Y.integral x y hx hy`. Rewrite using `[Complex.exp_eq_exp_iff_exists_int]`. Use `⟨-k, ?_⟩` and prove the remaining obligations.

Rewrite using `[hk]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem translate_translate (Y : GT ι)
    (hY : ∀ x ∈ lat Y.b, ∀ y ∈ lat Y.b,
      Y.ka (x + y) = Y.ka x * Y.ka y * cexp (Real.pi * I * (Hf x y).im))
    {x y : EuclideanSpace ℂ ι} (hx : x ∈ lat Y.b) (hy : y ∈ lat Y.b)
    (F : EuclideanSpace ℂ ι → ℂ) :
    Y.ka x • U 1 x (Y.ka y • U 1 y F) = Y.ka (x + y) • U 1 (x + y) F := by
  have h1 := (fock_translation_laws U hU 1).1 x y F
  have e : U 1 x (Y.ka y • U 1 y F) = Y.ka y • U 1 x (U 1 y F) := by
    funext v
    simp only [Pi.smul_apply, smul_eq_mul, hU 1 x]
    ring
  rw [e, h1, hY x hx y hy, smul_smul, smul_smul]
  congr 2
  obtain ⟨k, hk⟩ := Y.integral x y hx hy
  rw [Complex.exp_eq_exp_iff_exists_int]
  refine ⟨-k, ?_⟩
  rw [hk]
  push_cast
  ring

/- English proof (translation)
Take `⟨-, -, -, -, h5, h6, -⟩` from `fock_translation_laws U hU 1`. Establish `h` using `h5 γ F (v + γ)`. Rewrite `h` using `[add_sub_cancel_right]`. Unfold `GT.ptN2`. Rewrite using `[← h]`.

Use `conv_lhs => rw [← ((h6 Y F).1 hF).2 γ hγ]`. Rewrite using `[Pi.smul_apply, norm_smul, Y.ka_abs γ hγ, one_mul]`.
-/
theorem thetaSectionPointwiseNormSq_periodic (Y : GT ι) {F : EuclideanSpace ℂ ι → ℂ} (hF : F ∈ Y.Sec 1)
    {γ : EuclideanSpace ℂ ι} (hγ : γ ∈ lat Y.b) (v : EuclideanSpace ℂ ι) :
    Y.ptN2 1 F (v + γ) = Y.ptN2 1 F v := by
  obtain ⟨-, -, -, -, h5, h6, -⟩ := fock_translation_laws U hU 1
  have h := h5 γ F (v + γ)
  rw [add_sub_cancel_right] at h
  unfold GT.ptN2
  rw [← h]
  conv_lhs => rw [← ((h6 Y F).1 hF).2 γ hγ]
  rw [Pi.smul_apply, norm_smul, Y.ka_abs γ hγ, one_mul]

end

/- English proof (translation)
Unfold `GT.ptN2`. Use `fun_prop`.
-/
theorem continuous_thetaSectionPointwiseNormSq (Y : GT ι) {F : EuclideanSpace ℂ ι → ℂ} (hF : Continuous F) :
    Continuous (Y.ptN2 1 F) := by
  unfold GT.ptN2
  fun_prop

/- English proof (translation)
Rewrite using `[GT.ptN2, Complex.mul_conj, Complex.normSq_eq_norm_sq, herm_self]`. Use `push_cast`. Use `congr 2`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem thetaSectionPointwiseNormSq_eq (Y : GT ι) (F : EuclideanSpace ℂ ι → ℂ) (v : EuclideanSpace ℂ ι) :
    ((Y.ptN2 1 F v : ℝ) : ℂ) = F v * (starRingEnd ℂ) (F v) * cexp (-(Real.pi * Hf v v)) := by
  rw [GT.ptN2, Complex.mul_conj, Complex.normSq_eq_norm_sq, herm_self]
  push_cast
  congr 2
  ring

end IsogenySum

open IsogenySum FockTranslation in

/- English proof (translation)
Take `⟨-, -, -, -, h5, h6, -⟩` from `fock_translation_laws U hU 1`. Establish `hinj : ∀ y ∈ R, ∀ y' ∈ R, y - y' ∈ lat Y.b → y = y'` using `fun y hy y' hy' h => (hR' y (hR y hy)).unique ⟨hy, by simp⟩ ⟨hy', h⟩`. Establish `hdiff : Differentiable ℂ (∑ y ∈ R, Y'.ka y • U 1 y F)` using `Differentiable.sum fun y _ => (translate_differentiable U hU hF.1 y).const_smul _`. Establish `hmem : (∑ y ∈ R, Y'.ka y • U 1 y F) ∈ Y'.Sec 1`. Use `(h6 Y' _).2 ⟨hdiff, fun γ hγ => ?_⟩` and prove the remaining obligations.

Establish `e : Y'.ka γ • U 1 γ (∑ y ∈ R, Y'.ka y • U 1 y F) = ∑ y ∈ R, Y'.ka γ • U 1 γ (Y'.ka y • U 1 y F)`. Use function extensionality and compare the values at `v`. Simplify using `only [Pi.smul_apply, smul_eq_mul, hU 1 γ, Finset.sum_apply, Finset.mul_sum]`. Rewrite using `[e]`. Use `choose σ hσ hσ' using fun (y) (hy : y ∈ R) => (hR' (γ + y) ((lat Y'.b).add_mem hγ (hR y hy))).exists`.

Establish `hσinj : ∀ y (hy : y ∈ R) y' (hy' : y' ∈ R), σ y hy = σ y' hy' → y = y'`. Introduce `y hy y' hy' h`. Use `hinj y hy y' hy' ?_` and prove the remaining obligations. Use `(lat Y.b).sub_mem (hσ' y hy) (hσ' y' hy')` as an intermediate fact. Rewrite `this` using `[h, sub_sub_sub_cancel_right, add_sub_add_left_eq_sub]`. Then use the resulting hypothesis.

Use `Finset.sum_bij σ hσ hσinj ?_ ?_` and prove the remaining obligations. Introduce `z hz`. Take `⟨a, ha, h⟩` from `Finset.surj_on_of_inj_on_of_card_le σ hσ (fun a₁ a₂ h₁ h₂ h => hσinj a₁ h₁ a₂ h₂ h) le_rfl z hz`. Conclude with `⟨a, ha, h.symm⟩`. Introduce `y hy`.

Establish `hd' : γ + y - σ y hy ∈ lat Y'.b` using `(lat Y'.b).sub_mem ((lat Y'.b).add_mem hγ (hR y hy)) (hR _ (hσ y hy))`. Establish `hfix : Y'.ka (γ + y - σ y hy) • U 1 (γ + y - σ y hy) F = F`. Rewrite using `[← hag _ (hσ' y hy) hd']`. Conclude with `((h6 Y F).1 hF).2 _ (hσ' y hy)`. Rewrite using `[translate_translate U hU Y' hY' hγ (hR y hy)]`.

Use `conv_rhs => rw [← hfix]`. Rewrite using `[translate_translate U hU Y' hY' (hR _ (hσ y hy)) hd', add_sub_cancel]`. Use `⟨hmem, ?_⟩` and prove the remaining obligations. Take `⟨b, hb, hb'⟩` from `exists_common_sublattice Y Y' R fun y hy => (hR' y hy).exists`. Establish `e1` using `average_fundamentalDomain_eq_real volume Y'.b b _ (continuous_thetaSectionPointwiseNormSq Y' hdiff.continuous) (fun γ hγ v => thetaSectionPointwiseNormSq_periodic U hU Y' hmem hγ v) hb' 0`.

Establish `e2` using `fun a => average_fundamentalDomain_eq_real volume Y.b b _ (continuous_thetaSectionPointwiseNormSq Y hF.1.continuous) (fun γ hγ v => thetaSectionPointwiseNormSq_periodic U hU Y hF hγ v) hb a`. Simplify using `only [add_zero] at e1`. Establish `e3 : ∫ v in ZSpan.fundamentalDomain b, Y'.ptN2 1 (∑ y ∈ R, Y'.ka y • U 1 y F) v = ∑ y ∈ R, ∫ v in ZSpan.fundamentalDomain b, Y.ptN2 1 F (v + -y)`. Apply `Complex.ofReal_injective` to reduce the goal to its premises. Rewrite using `[← integral_complex_ofReal]`.

Establish `hpt : ∀ v, ((Y'.ptN2 1 (∑ y ∈ R, Y'.ka y • U 1 y F) v : ℝ) : ℂ) = ∑ y ∈ R, ∑ y' ∈ R, (Y'.ka y * (starRingEnd ℂ) (Y'.ka y')) * (U 1 y F v * (starRingEnd ℂ) (U 1 y' F v) * cexp (-(Real.pi * Hf v v)))`. Introduce `v`. Rewrite using `[thetaSectionPointwiseNormSq_eq]`. Simplify using `only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, map_sum, map_mul]`. Rewrite using `[Finset.sum_mul_sum]`.

Simplify using `only [Finset.sum_mul]`. Conclude with `Finset.sum_congr rfl fun y _ => Finset.sum_congr rfl fun y' _ => by ring`. Establish `hint : ∀ y y', IntegrableOn (fun v => (Y'.ka y * (starRingEnd ℂ) (Y'.ka y')) * (U 1 y F v * (starRingEnd ℂ) (U 1 y' F v) * cexp (-(Real.pi * Hf v v)))) (ZSpan.fundamentalDomain b) volume` using `fun y y' => integrableOn_fundamentalDomain_of_continuous volume b _ (continuous_const.mul (pairing_density_continuous U hU hF.1 y y'))`. Rewrite using `[integral_congr_ae (Filter.Eventually.of_forall hpt)]`. Rewrite using `[integral_finset_sum _ fun y _ => integrable_finset_sum _ fun y' _ => hint y y', Complex.ofReal_sum]`.

Use `Finset.sum_congr rfl fun y hy => ?_` and prove the remaining obligations. Rewrite using `[integral_finset_sum _ fun y' _ => hint y y', Finset.sum_eq_single_of_mem y hy]`. Establish `hk : Y'.ka y * (starRingEnd ℂ) (Y'.ka y) = 1`. Rewrite using `[Complex.mul_conj, Complex.normSq_eq_norm_sq, Y'.ka_abs y (hR y hy)]`. Simplify using the standard rewrite rules.

Rewrite using `[hk, ← integral_complex_ofReal]`. Use `integral_congr_ae (Filter.Eventually.of_forall fun v => ?_)` and prove the remaining obligations. Simplify using `only [one_mul]`. Rewrite using `[← thetaSectionPointwiseNormSq_eq Y, ← sub_eq_add_neg]`. Conclude with `congrArg _ (h5 y F v)`.

Introduce `y' hy' hne`. Rewrite using `[integral_const_mul, integral_pairing_density_eq_zero U hU Y hF b hb y y' (fun x hx => Y'.integral _ _ (hb' hx) ((lat Y'.b).sub_mem (hR y hy) (hR y' hy'))) (fun h => hne (hinj y hy y' hy' h).symm), mul_zero]`. Unfold `GT.l2`. Rewrite using `[← e1, setAverage_eq, e3, Finset.smul_sum]`. Simplify using `only [← setAverage_eq, e2]`.

Simplify using the standard rewrite rules.
-/
theorem isogeny_sum_mem_and_norm {ι : Type} [Fintype ι] (U : ℕ → EuclideanSpace ℂ ι → (EuclideanSpace ℂ ι → ℂ) → EuclideanSpace ℂ ι → ℂ)
    (hU : ∀ (q : ℕ) a F v, U q a F v = cexp (q * Real.pi * Hf v a - q * Real.pi * Hf a a / 2) * F (v - a))
    (Y Y' : GT ι) (hY : (∀ x ∈ lat Y.b, ∀ y ∈ lat Y.b, Y.ka (x + y) = Y.ka x * Y.ka y * cexp (Real.pi * I * (Hf x y).im))) (hY' : (∀ x ∈ lat Y'.b, ∀ y ∈ lat Y'.b, Y'.ka (x + y) = Y'.ka x * Y'.ka y * cexp (Real.pi * I * (Hf x y).im)))
    (hag : ∀ x ∈ lat Y.b, x ∈ lat Y'.b → Y.ka x = Y'.ka x)
    (R : Finset (EuclideanSpace ℂ ι)) (hR : ∀ y ∈ R, y ∈ lat Y'.b) (hR' : ∀ y ∈ lat Y'.b, ∃! r ∈ R, y - r ∈ lat Y.b)
    (F : EuclideanSpace ℂ ι → ℂ) (hF : F ∈ Y.Sec 1) :
    (∑ y ∈ R, Y'.ka y • U 1 y F) ∈ Y'.Sec 1 ∧ Y'.l2 1 (∑ y ∈ R, Y'.ka y • U 1 y F) = R.card * Y.l2 1 F := by
  classical
  obtain ⟨-, -, -, -, h5, h6, -⟩ := fock_translation_laws U hU 1
  have hinj : ∀ y ∈ R, ∀ y' ∈ R, y - y' ∈ lat Y.b → y = y' := fun y hy y' hy' h =>
    (hR' y (hR y hy)).unique ⟨hy, by simp⟩ ⟨hy', h⟩
  have hdiff : Differentiable ℂ (∑ y ∈ R, Y'.ka y • U 1 y F) :=
    Differentiable.sum fun y _ => (translate_differentiable U hU hF.1 y).const_smul _
  have hmem : (∑ y ∈ R, Y'.ka y • U 1 y F) ∈ Y'.Sec 1 := by
    refine (h6 Y' _).2 ⟨hdiff, fun γ hγ => ?_⟩
    have e : Y'.ka γ • U 1 γ (∑ y ∈ R, Y'.ka y • U 1 y F) =
        ∑ y ∈ R, Y'.ka γ • U 1 γ (Y'.ka y • U 1 y F) := by
      funext v
      simp only [Pi.smul_apply, smul_eq_mul, hU 1 γ, Finset.sum_apply, Finset.mul_sum]
    rw [e]
    choose σ hσ hσ' using fun (y) (hy : y ∈ R) =>
      (hR' (γ + y) ((lat Y'.b).add_mem hγ (hR y hy))).exists
    have hσinj : ∀ y (hy : y ∈ R) y' (hy' : y' ∈ R), σ y hy = σ y' hy' → y = y' := by
      intro y hy y' hy' h
      refine hinj y hy y' hy' ?_
      have := (lat Y.b).sub_mem (hσ' y hy) (hσ' y' hy')
      rwa [h, sub_sub_sub_cancel_right, add_sub_add_left_eq_sub] at this
    refine Finset.sum_bij σ hσ hσinj ?_ ?_
    · intro z hz
      obtain ⟨a, ha, h⟩ := Finset.surj_on_of_inj_on_of_card_le σ hσ
        (fun a₁ a₂ h₁ h₂ h => hσinj a₁ h₁ a₂ h₂ h) le_rfl z hz
      exact ⟨a, ha, h.symm⟩
    · intro y hy
      have hd' : γ + y - σ y hy ∈ lat Y'.b :=
        (lat Y'.b).sub_mem ((lat Y'.b).add_mem hγ (hR y hy)) (hR _ (hσ y hy))
      have hfix : Y'.ka (γ + y - σ y hy) • U 1 (γ + y - σ y hy) F = F := by
        rw [← hag _ (hσ' y hy) hd']
        exact ((h6 Y F).1 hF).2 _ (hσ' y hy)
      rw [translate_translate U hU Y' hY' hγ (hR y hy)]
      conv_rhs => rw [← hfix]
      rw [translate_translate U hU Y' hY' (hR _ (hσ y hy)) hd', add_sub_cancel]
  refine ⟨hmem, ?_⟩
  obtain ⟨b, hb, hb'⟩ := exists_common_sublattice Y Y' R fun y hy => (hR' y hy).exists
  have e1 := average_fundamentalDomain_eq_real volume Y'.b b _
    (continuous_thetaSectionPointwiseNormSq Y' hdiff.continuous) (fun γ hγ v => thetaSectionPointwiseNormSq_periodic U hU Y' hmem hγ v) hb' 0
  have e2 := fun a => average_fundamentalDomain_eq_real volume Y.b b _
    (continuous_thetaSectionPointwiseNormSq Y hF.1.continuous) (fun γ hγ v => thetaSectionPointwiseNormSq_periodic U hU Y hF hγ v) hb a
  simp only [add_zero] at e1
  have e3 : ∫ v in ZSpan.fundamentalDomain b, Y'.ptN2 1 (∑ y ∈ R, Y'.ka y • U 1 y F) v =
      ∑ y ∈ R, ∫ v in ZSpan.fundamentalDomain b, Y.ptN2 1 F (v + -y) := by
    apply Complex.ofReal_injective
    rw [← integral_complex_ofReal]
    have hpt : ∀ v, ((Y'.ptN2 1 (∑ y ∈ R, Y'.ka y • U 1 y F) v : ℝ) : ℂ) =
        ∑ y ∈ R, ∑ y' ∈ R, (Y'.ka y * (starRingEnd ℂ) (Y'.ka y')) *
          (U 1 y F v * (starRingEnd ℂ) (U 1 y' F v) * cexp (-(Real.pi * Hf v v))) := by
      intro v
      rw [thetaSectionPointwiseNormSq_eq]
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, map_sum, map_mul]
      rw [Finset.sum_mul_sum]
      simp only [Finset.sum_mul]
      exact Finset.sum_congr rfl fun y _ => Finset.sum_congr rfl fun y' _ => by ring
    have hint : ∀ y y', IntegrableOn (fun v => (Y'.ka y * (starRingEnd ℂ) (Y'.ka y')) *
          (U 1 y F v * (starRingEnd ℂ) (U 1 y' F v) * cexp (-(Real.pi * Hf v v))))
          (ZSpan.fundamentalDomain b) volume := fun y y' =>
      integrableOn_fundamentalDomain_of_continuous volume b _
        (continuous_const.mul (pairing_density_continuous U hU hF.1 y y'))
    rw [integral_congr_ae (Filter.Eventually.of_forall hpt)]
    rw [integral_finset_sum _ fun y _ => integrable_finset_sum _ fun y' _ => hint y y',
      Complex.ofReal_sum]
    refine Finset.sum_congr rfl fun y hy => ?_
    rw [integral_finset_sum _ fun y' _ => hint y y', Finset.sum_eq_single_of_mem y hy]
    · have hk : Y'.ka y * (starRingEnd ℂ) (Y'.ka y) = 1 := by
        rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, Y'.ka_abs y (hR y hy)]; simp
      rw [hk, ← integral_complex_ofReal]
      refine integral_congr_ae (Filter.Eventually.of_forall fun v => ?_)
      simp only [one_mul]
      rw [← thetaSectionPointwiseNormSq_eq Y, ← sub_eq_add_neg]
      exact congrArg _ (h5 y F v)
    · intro y' hy' hne
      rw [integral_const_mul, integral_pairing_density_eq_zero U hU Y hF b hb y y'
        (fun x hx => Y'.integral _ _ (hb' hx) ((lat Y'.b).sub_mem (hR y hy) (hR y' hy')))
        (fun h => hne (hinj y hy y' hy' h).symm), mul_zero]
  unfold GT.l2
  rw [← e1, setAverage_eq, e3, Finset.smul_sum]
  simp only [← setAverage_eq, e2]
  simp

end GlobalTheory

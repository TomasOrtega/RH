import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
import Formalism.PairingDivisors.StatementH
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.DifferentiableComb
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.GalTheta
open scoped BigOperators

noncomputable section

namespace GlobalTheory.GalTheta.Avg

/- English proof (translation)
Rewrite using `[← Equiv.sum_comp (Equiv.addLeft (x : A ⧸ S)) (fun q : A ⧸ S => f q.out)]`. Use `Finset.sum_congr rfl fun q _ => ?_` and prove the remaining obligations. Establish `h : ((x + q.out : A) : A ⧸ S) = (((x : A ⧸ S) + q).out : A)` using `by simp`. Rewrite `h` using `[QuotientAddGroup.eq]`. Use `hf (x + q.out) _ h` as an intermediate fact.

Simplify using `only [Equiv.coe_addLeft]`. Rewrite using `[← this]`. Use `congr 1`. Normalize the expressions using the abelian group laws.
-/
theorem sum_out_translate {A M : Type*} [AddCommGroup A] [AddCommMonoid M] (S : AddSubgroup A) [Fintype (A ⧸ S)]
    (f : A → M) (hf : ∀ a, ∀ s ∈ S, f (a + s) = f a) (x : A) :
    ∑ q : A ⧸ S, f (x + q.out) = ∑ q : A ⧸ S, f q.out := by
  rw [← Equiv.sum_comp (Equiv.addLeft (x : A ⧸ S)) (fun q : A ⧸ S => f q.out)]
  refine Finset.sum_congr rfl fun q _ => ?_
  have h : ((x + q.out : A) : A ⧸ S) = (((x : A ⧸ S) + q).out : A) := by simp
  rw [QuotientAddGroup.eq] at h
  have := hf (x + q.out) _ h
  simp only [Equiv.coe_addLeft]
  rw [← this]
  congr 1
  abel

variable (D : D7) (T : Tor D) {N N' : ℕ}

def W (x : VC D N N') (G : VC D N N' → ℂ) : VC D N N' → ℂ := fun z => al D T x * U D T x G z

/- English proof (translation)
Use function extensionality and compare the values at `z`. Use `U_mul D T x (al D T y) (U D T y G) z` as an intermediate fact. Unfold `W`. Rewrite using `[this, U_U, h]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem Wm_mul_Wm_comm {x y : VC D N N'}
    (h : al D T (x + y) = al D T x * al D T y *
      Complex.exp (-(Real.pi : ℂ) * Complex.I * ((Hf D T x y).im : ℂ))) (G : VC D N N' → ℂ) :
    W D T x (W D T y G) = W D T (x + y) G := by
  funext z
  have := U_mul D T x (al D T y) (U D T y G) z
  unfold W
  rw [this, U_U, h]
  ring

/- English proof (translation)
Rewrite using `[U_U, U_U, add_comm y x, Hf_im_swap D T x y, ← mul_assoc, ← Complex.exp_add]`. Use `congr 2`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem U_comm (x y : VC D N N') (G : VC D N N' → ℂ) (z : VC D N N') :
    U D T x (U D T y G) z =
      Complex.exp (-(2 * Real.pi * Complex.I) * ((Hf D T x y).im : ℂ)) * U D T y (U D T x G) z := by
  rw [U_U, U_U, add_comm y x, Hf_im_swap D T x y, ← mul_assoc, ← Complex.exp_add]
  congr 2
  push_cast
  ring

/- English proof (translation)
Use `h (z - x)` as an intermediate fact. Simplify `this` using `[U]`.
-/
theorem eq_zero_of_U {x : VC D N N'} {G : VC D N N' → ℂ} (h : ∀ z, U D T x G z = 0) (z : VC D N N') :
    G z = 0 := by
  have := h (z - x)
  simpa [U] using this

/- English proof (translation)
Take `⟨m, hm⟩` from `hx`. Unfold `qH at hm`. Establish `: √↑D.host.d / 2 * (Hf D T ((2 * n) • x) ((2 * n) • x)).re = ((2 * (2 * n * n * m) : ℤ) : ℝ)`. Rewrite using `[Hf_nsmul_left, Hf_nsmul_right, ← mul_assoc, ← Nat.cast_mul, ← Complex.ofReal_natCast, Complex.re_ofReal_mul, mul_left_comm, hm]`. Use `push_cast`.

Expand and normalize the polynomial expressions, which then agree. Unfold `al`. Rewrite using `[this, round_intCast, zpow_mul]`. Evaluate the numerical expressions.
-/
theorem al_two_mul {x : VC D N N'} (hx : ∃ m : ℤ, qH D T x = m) (n : ℕ) : al D T ((2 * n) • x) = 1 := by
  obtain ⟨m, hm⟩ := hx
  unfold qH at hm
  have : √↑D.host.d / 2 * (Hf D T ((2 * n) • x) ((2 * n) • x)).re = ((2 * (2 * n * n * m) : ℤ) : ℝ) := by
    rw [Hf_nsmul_left, Hf_nsmul_right, ← mul_assoc, ← Nat.cast_mul, ← Complex.ofReal_natCast,
      Complex.re_ofReal_mul, mul_left_comm, hm]
    push_cast
    ring
  unfold al
  rw [this, round_intCast, zpow_mul]
  norm_num

/- English proof (translation)
Rewrite using `[Hf_smul_right, Complex.conj_ofReal, Complex.im_ofReal_mul]`.
-/
theorem im_smul_right (c : ℝ) (x y : VC D N N') : (Hf D T x ((c : ℂ) • y)).im = c * (Hf D T x y).im := by
  rw [Hf_smul_right, Complex.conj_ofReal, Complex.im_ofReal_mul]

/- English proof (translation)
Rewrite using `[Hf_smul_left, Complex.im_ofReal_mul]`.
-/
theorem im_smul_left (c : ℝ) (x y : VC D N N') : (Hf D T ((c : ℂ) • x) y).im = c * (Hf D T x y).im := by
  rw [Hf_smul_left, Complex.im_ofReal_mul]

/- English proof (translation)
Rewrite using `[← im_smul_right, Complex.ofReal_natCast, Nat.cast_smul_eq_nsmul]`.
-/
theorem im_nsmul_right (c : ℕ) (x y : VC D N N') : (Hf D T x (c • y)).im = c * (Hf D T x y).im := by
  rw [← im_smul_right, Complex.ofReal_natCast, Nat.cast_smul_eq_nsmul]

/- English proof (translation)
Rewrite using `[← im_smul_left, Complex.ofReal_natCast, Nat.cast_smul_eq_nsmul]`.
-/
theorem im_nsmul_left (c : ℕ) (x y : VC D N N') : (Hf D T (c • x) y).im = c * (Hf D T x y).im := by
  rw [← im_smul_left, Complex.ofReal_natCast, Nat.cast_smul_eq_nsmul]

/- English proof (translation)
Rewrite using `[Complex.exp_eq_one_iff]`. Conclude with `⟨-m, by rw [h]; push_cast; ring⟩`.
-/
theorem exp_int (t : ℝ) (m : ℤ) (h : t = m) : Complex.exp (-(2 * Real.pi * Complex.I) * (t : ℂ)) = 1 := by
  rw [Complex.exp_eq_one_iff]
  exact ⟨-m, by rw [h]; push_cast; ring⟩

/- English proof (translation)
Rewrite `h` using `[Complex.exp_eq_one_iff]`. Take `⟨m, hm⟩` from `h`. Use `⟨-m, ?_⟩` and prove the remaining obligations. Establish `h2 : (2 * Real.pi * Complex.I : ℂ) ≠ 0` using `Complex.two_pi_I_ne_zero`. Establish `: (t : ℂ) = ((-m : ℤ) : ℝ)`.

Apply `mul_left_cancel₀ h2` to reduce the goal to its premises. Use `push_cast`. Take the linear combination `-hm`. Conclude with `this` after adjusting the coercions.
-/
theorem int_of_exp (t : ℝ) (h : Complex.exp (-(2 * Real.pi * Complex.I) * (t : ℂ)) = 1) : ∃ m : ℤ, t = m := by
  rw [Complex.exp_eq_one_iff] at h
  obtain ⟨m, hm⟩ := h
  refine ⟨-m, ?_⟩
  have h2 : (2 * Real.pi * Complex.I : ℂ) ≠ 0 := Complex.two_pi_I_ne_zero
  have : (t : ℂ) = ((-m : ℤ) : ℝ) := by
    apply mul_left_cancel₀ h2
    push_cast
    linear_combination -hm
  exact_mod_cast this

end GlobalTheory.GalTheta.Avg

namespace GlobalTheory.GalTheta

open Avg

/- English proof (translation)
Introduce `D T N N' A hfg hint hdual hq hal F hF hF0 n hn hlev`. Establish `hn2 : 0 < 2 * n` using `by omega`. Use `haveI : AddGroup.FG A := (AddGroup.fg_iff_addSubgroup_fg A).2 hfg`. Use `set S : AddSubgroup A := (nsmulAddMonoidHom (α := A) (2 * n)).range with hS`. Use `haveI : S.FiniteIndex := AddSubgroup.finiteIndex_range_nsmulAddMonoidHom_of_fg A hn2.ne'`.

Use `letI : Fintype (A ⧸ S) := Fintype.ofFinite _`. Use `set c : ℝ := ((2 * n : ℕ) : ℝ)⁻¹ with hc`. Establish `hcn : ((2 * n : ℕ) : ℝ) * c = 1` using `mul_inv_cancel₀ (by exact_mod_cast hn2.ne')`. Establish `hcs : ∀ y : VC D N N', (2 * n) • ((c : ℂ) • y) = y`. Introduce `y`.

Rewrite using `[← Nat.cast_smul_eq_nsmul ℂ, smul_smul, ← Complex.ofReal_natCast, ← Complex.ofReal_mul, hcn]`. Simplify using the standard rewrite rules. Establish `hUF : ∀ x ∈ A, U D T ((2 * n) • x) F = F`. Introduce `x hx`. Rewrite using `[mul_comm, mul_smul]`.

Conclude with `hlev _ (A.nsmul_mem hx 2)`. Establish `hfix : ∀ y ∈ A, ∀ x ∈ A, W D T ((2 * n) • x) (U D T ((c : ℂ) • y) F) = U D T ((c : ℂ) • y) F`. Introduce `y hy x hx`. Use function extensionality and compare the values at `z`. Take `⟨m, hm⟩` from `hint x hx y hy`.

Unfold `W`. Rewrite using `[al_two_mul D T (hq x hx), one_mul, U_comm, hUF x hx, exp_int _ m, one_mul]`. Rewrite using `[im_nsmul_left, im_smul_right, ← mul_assoc, hcn, one_mul, hm]`. Establish `hcls : ∀ y ∈ A, ∀ a : A, ∀ s ∈ S, W D T ((a + s : A) : VC D N N') (U D T ((c : ℂ) • y) F) = W D T a (U D T ((c : ℂ) • y) F)`. Introduce and unpack `y hy a s ⟨b, rfl⟩`.

Establish `e : ((a + nsmulAddMonoidHom (2 * n) b : A) : VC D N N') = (a : VC D N N') + (2 * n) • (b : VC D N N')`. Simplify using the standard rewrite rules. Rewrite using `[e, ← Wm_mul_Wm_comm D T (hal _ a.2 _ (A.nsmul_mem b.2 _)), hfix y hy b b.2]`. Use `set P : VC D N N' → VC D N N' → ℂ := fun y z => ∑ q : A ⧸ S, W D T (q.out : A) (U D T ((c : ℂ) • y) F) z with hP`. Establish `hTr : ∀ y ∈ A, IsTr D T A F (P y)`.

Introduce `y hy`. Use `IsTr.trans D T (IsTr.single D T F 1 ((c : ℂ) • y) (2 * n) hn2 (by rw [hcs]; exact hy)) ?_` and prove the remaining obligations. Set `e` to `Fintype.equivFin (A ⧸ S)`. Use `⟨_, fun i => al D T (((e.symm i).out : A) : VC D N N'), fun i => (((e.symm i).out : A) : VC D N N'), 1, one_pos, fun i => by simp, ?_⟩` and prove the remaining obligations. Use function extensionality and compare the values at `z`.

Simplify using `only [hP, comb, one_mul, W]`. Conclude with `(Equiv.sum_comp e.symm _).symm`. Establish `hTh : ∀ y ∈ A, P y ∈ ThSp D T A`. Introduce `y hy`. Use `⟨?_, fun x hx z => ?_⟩` and prove the remaining obligations.

Conclude with `Differentiable.fun_sum fun q _ => (differentiable_U D T _ (differentiable_U D T ((c : ℂ) • y) hF)).const_mul _`. Establish `h1` using `sum_out_translate S (fun a : A => W D T (a : VC D N N') (U D T ((c : ℂ) • y) F) z) (fun a s hs => by simp only [hcls y hy a s hs]) ⟨x, hx⟩`. Simplify using `only [hP]`. Rewrite using `[← h1, U_sum, Finset.mul_sum]`. Use `Finset.sum_congr rfl fun q _ => ?_` and prove the remaining obligations.

Conclude with `congrFun (Wm_mul_Wm_comm D T (hal x hx _ (q.out).2) _) z`. Assume the negation of the conclusion as `hcon`. Use `push Not at hcon`. Establish `hP0 : ∀ y ∈ A, P y = 0` using `fun y hy => hcon _ (hTr y hy) (hTh y hy)`. Use `set χ : A → A → ℂ := fun a y => Complex.exp (-(2 * Real.pi * Complex.I) * ((c * (Hf D T (a : VC D N N') y).im : ℝ) : ℂ)) with hχ`.

Establish `hsum : ∀ y : A, ∀ z, ∑ q : A ⧸ S, χ q.out y * W D T (q.out : A) F z = 0`. Introduce `y`. Apply `eq_zero_of_U D T (x := (c : ℂ) • (y : VC D N N'))` to reduce the goal to its premises. Introduce `z`. Establish `h0` using `congrFun (hP0 y y.2) z`.

Simplify using `only [hP, Pi.zero_apply] at h0`. Rewrite using `[U_sum, ← h0]`. Use `Finset.sum_congr rfl fun q _ => ?_` and prove the remaining obligations. Establish `h2` using `U_mul D T ((c : ℂ) • (y : VC D N N')) (al D T ((q.out : A) : VC D N N')) (U D T (q.out : A) F) z`. Rewrite using `[U_mul]`.

Unfold `W`. Rewrite using `[h2, U_comm D T ((q.out : A) : VC D N N'), im_smul_right]`. Simplify using `only [hχ]`. Expand and normalize the polynomial expressions, which then agree. Establish `hadd : ∀ a x y : A, χ a (x + y) = χ a x * χ a y`.

Introduce `a x y`. Simplify using `only [hχ]`. Rewrite using `[← Complex.exp_add, AddSubgroup.coe_add, Hf_add_right, Complex.add_im]`. Use `congr 1`. Use `push_cast`.

Expand and normalize the polynomial expressions, which then agree. Establish `hS1 : ∀ a : A, ∀ s ∈ S, χ a s = 1`. Introduce and unpack `a s ⟨b, rfl⟩`. Take `⟨m, hm⟩` from `hint a a.2 b b.2`. Establish `e : ((nsmulAddMonoidHom (2 * n) b : A) : VC D N N') = (2 * n) • (b : VC D N N')` using `by simp`.

Use `exp_int _ m ?_` and prove the remaining obligations. Rewrite using `[e, im_nsmul_right, ← mul_assoc, mul_comm c, hcn, one_mul, hm]`. Establish `hS2 : ∀ s ∈ S, ∀ a : A, χ s a = 1`. Introduce and unpack `s ⟨b, rfl⟩ a`. Take `⟨m, hm⟩` from `hint b b.2 a a.2`.

Establish `e : ((nsmulAddMonoidHom (2 * n) b : A) : VC D N N') = (2 * n) • (b : VC D N N')` using `by simp`. Use `exp_int _ m ?_` and prove the remaining obligations. Rewrite using `[e, im_nsmul_left, ← mul_assoc, mul_comm c, hcn, one_mul, hm]`. Establish `hvan : ∀ q : A ⧸ S, q ≠ 0 → ∑ r : A ⧸ S, χ q.out r.out = 0`. Introduce `q hq0`.

Assume the negation of the conclusion as `hne`. Apply `hq0` to reduce the goal to its premises. Establish `hall : ∀ y : A, χ q.out y = 1`. Introduce `y`. Establish `h1` using `sum_out_translate S (χ q.out) (fun a s hs => by rw [hadd, hS1 _ s hs, mul_one]) y`.

Simplify using `only [hadd, ← Finset.mul_sum] at h1`. Conclude with `mul_right_cancel₀ hne (by rw [h1, one_mul])`. Establish `hmem : (c : ℂ) • ((q.out : A) : VC D N N') ∈ A`. Use `hdual _ fun y hy => ?_` and prove the remaining obligations. Rewrite using `[im_smul_left]`.

Conclude with `int_of_exp _ (hall ⟨y, hy⟩)`. Rewrite using `[← QuotientAddGroup.out_eq' q, QuotientAddGroup.eq_zero_iff]`. Conclude with `⟨⟨_, hmem⟩, Subtype.ext (by simpa using hcs _)⟩`. Establish `h0S : (0 : A ⧸ S).out ∈ S`. Rewrite using `[← QuotientAddGroup.eq_zero_iff, QuotientAddGroup.out_eq']`.

Establish `hW0 : W D T ((0 : A ⧸ S).out : A) F = F`. Take `⟨b, hb⟩` from `h0S`. Use `hfix 0 A.zero_mem b b.2` as an intermediate fact. Rewrite `this` using `[smul_zero, U_zero]`. Rewrite using `[← hb]`.

Simplify using `using this`. Apply `hF0` to reduce the goal to its premises. Use function extensionality and compare the values at `z`. Establish `h3 : ∑ r : A ⧸ S, ∑ q : A ⧸ S, χ q.out r.out * W D T (q.out : A) F z = 0` using `Finset.sum_eq_zero fun r _ => hsum _ z`. Rewrite `h3` using `[Finset.sum_comm, Finset.sum_eq_single 0 (fun q _ hq0 => by rw [← Finset.sum_mul, hvan q hq0, zero_mul]) (by simp)]`.

Simplify using `only [hS2 _ h0S, hW0, one_mul, Finset.sum_const, nsmul_eq_mul, mul_eq_zero, Nat.cast_eq_zero, Finset.card_univ, Fintype.card_ne_zero, false_or] at h3`. Conclude with `h3`.
-/
theorem exists_theta_of_level : ∀ (D : D7) (T : Tor D) (N N' : ℕ) (A : AddSubgroup (VC D N N')), A.FG → (∀ x ∈ A, ∀ y ∈ A, ∃ m : ℤ, (Hf D T x y).im = m) → (∀ x, (∀ y ∈ A, ∃ m : ℤ, (Hf D T x y).im = m) → x ∈ A) → (∀ x ∈ A, ∃ m : ℤ, qH D T x = m) → (∀ x ∈ A, ∀ y ∈ A, al D T (x + y) = al D T x * al D T y * Complex.exp (-(Real.pi : ℂ) * Complex.I * ((Hf D T x y).im : ℂ))) → ∀ F : VC D N N' → ℂ, Differentiable ℂ F → F ≠ 0 → ∀ n : ℕ, 0 < n → (∀ x ∈ A, U D T (n • x) F = F) → ∃ P, IsTr D T A F P ∧ P ∈ ThSp D T A ∧ P ≠ 0 := by
  intro D T N N' A hfg hint hdual hq hal F hF hF0 n hn hlev
  have hn2 : 0 < 2 * n := by omega
  haveI : AddGroup.FG A := (AddGroup.fg_iff_addSubgroup_fg A).2 hfg
  set S : AddSubgroup A := (nsmulAddMonoidHom (α := A) (2 * n)).range with hS
  haveI : S.FiniteIndex := AddSubgroup.finiteIndex_range_nsmulAddMonoidHom_of_fg A hn2.ne'
  letI : Fintype (A ⧸ S) := Fintype.ofFinite _
  set c : ℝ := ((2 * n : ℕ) : ℝ)⁻¹ with hc
  have hcn : ((2 * n : ℕ) : ℝ) * c = 1 := mul_inv_cancel₀ (by exact_mod_cast hn2.ne')
  have hcs : ∀ y : VC D N N', (2 * n) • ((c : ℂ) • y) = y := by
    intro y
    rw [← Nat.cast_smul_eq_nsmul ℂ, smul_smul, ← Complex.ofReal_natCast, ← Complex.ofReal_mul, hcn]
    simp
  have hUF : ∀ x ∈ A, U D T ((2 * n) • x) F = F := by
    intro x hx
    rw [mul_comm, mul_smul]
    exact hlev _ (A.nsmul_mem hx 2)

  have hfix : ∀ y ∈ A, ∀ x ∈ A, W D T ((2 * n) • x) (U D T ((c : ℂ) • y) F) = U D T ((c : ℂ) • y) F := by
    intro y hy x hx
    funext z
    obtain ⟨m, hm⟩ := hint x hx y hy
    unfold W
    rw [al_two_mul D T (hq x hx), one_mul, U_comm, hUF x hx, exp_int _ m, one_mul]
    rw [im_nsmul_left, im_smul_right, ← mul_assoc, hcn, one_mul, hm]
  have hcls : ∀ y ∈ A, ∀ a : A, ∀ s ∈ S,
      W D T ((a + s : A) : VC D N N') (U D T ((c : ℂ) • y) F) = W D T a (U D T ((c : ℂ) • y) F) := by
    rintro y hy a s ⟨b, rfl⟩
    have e : ((a + nsmulAddMonoidHom (2 * n) b : A) : VC D N N') = (a : VC D N N') + (2 * n) • (b : VC D N N') := by
      simp
    rw [e, ← Wm_mul_Wm_comm D T (hal _ a.2 _ (A.nsmul_mem b.2 _)), hfix y hy b b.2]

  set P : VC D N N' → VC D N N' → ℂ :=
    fun y z => ∑ q : A ⧸ S, W D T (q.out : A) (U D T ((c : ℂ) • y) F) z with hP
  have hTr : ∀ y ∈ A, IsTr D T A F (P y) := by
    intro y hy
    refine IsTr.trans D T (IsTr.single D T F 1 ((c : ℂ) • y) (2 * n) hn2 (by rw [hcs]; exact hy)) ?_
    let e := Fintype.equivFin (A ⧸ S)
    refine ⟨_, fun i => al D T (((e.symm i).out : A) : VC D N N'), fun i => (((e.symm i).out : A) : VC D N N'), 1, one_pos,
      fun i => by simp, ?_⟩
    funext z
    simp only [hP, comb, one_mul, W]
    exact (Equiv.sum_comp e.symm _).symm
  have hTh : ∀ y ∈ A, P y ∈ ThSp D T A := by
    intro y hy
    refine ⟨?_, fun x hx z => ?_⟩
    · exact Differentiable.fun_sum fun q _ =>
        (differentiable_U D T _ (differentiable_U D T ((c : ℂ) • y) hF)).const_mul _
    · have h1 := sum_out_translate S (fun a : A => W D T (a : VC D N N') (U D T ((c : ℂ) • y) F) z)
        (fun a s hs => by simp only [hcls y hy a s hs]) ⟨x, hx⟩
      simp only [hP]
      rw [← h1, U_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun q _ => ?_
      exact congrFun (Wm_mul_Wm_comm D T (hal x hx _ (q.out).2) _) z
  by_contra hcon
  push Not at hcon
  have hP0 : ∀ y ∈ A, P y = 0 := fun y hy => hcon _ (hTr y hy) (hTh y hy)

  set χ : A → A → ℂ := fun a y =>
    Complex.exp (-(2 * Real.pi * Complex.I) * ((c * (Hf D T (a : VC D N N') y).im : ℝ) : ℂ)) with hχ
  have hsum : ∀ y : A, ∀ z, ∑ q : A ⧸ S, χ q.out y * W D T (q.out : A) F z = 0 := by
    intro y
    apply eq_zero_of_U D T (x := (c : ℂ) • (y : VC D N N'))
    intro z
    have h0 := congrFun (hP0 y y.2) z
    simp only [hP, Pi.zero_apply] at h0
    rw [U_sum, ← h0]
    refine Finset.sum_congr rfl fun q _ => ?_
    have h2 := U_mul D T ((c : ℂ) • (y : VC D N N')) (al D T ((q.out : A) : VC D N N')) (U D T (q.out : A) F) z
    rw [U_mul]
    unfold W
    rw [h2, U_comm D T ((q.out : A) : VC D N N'), im_smul_right]
    simp only [hχ]
    ring
  have hadd : ∀ a x y : A, χ a (x + y) = χ a x * χ a y := by
    intro a x y
    simp only [hχ]
    rw [← Complex.exp_add, AddSubgroup.coe_add, Hf_add_right, Complex.add_im]
    congr 1
    push_cast
    ring
  have hS1 : ∀ a : A, ∀ s ∈ S, χ a s = 1 := by
    rintro a s ⟨b, rfl⟩
    obtain ⟨m, hm⟩ := hint a a.2 b b.2
    have e : ((nsmulAddMonoidHom (2 * n) b : A) : VC D N N') = (2 * n) • (b : VC D N N') := by simp
    refine exp_int _ m ?_
    rw [e, im_nsmul_right, ← mul_assoc, mul_comm c, hcn, one_mul, hm]
  have hS2 : ∀ s ∈ S, ∀ a : A, χ s a = 1 := by
    rintro s ⟨b, rfl⟩ a
    obtain ⟨m, hm⟩ := hint b b.2 a a.2
    have e : ((nsmulAddMonoidHom (2 * n) b : A) : VC D N N') = (2 * n) • (b : VC D N N') := by simp
    refine exp_int _ m ?_
    rw [e, im_nsmul_left, ← mul_assoc, mul_comm c, hcn, one_mul, hm]
  have hvan : ∀ q : A ⧸ S, q ≠ 0 → ∑ r : A ⧸ S, χ q.out r.out = 0 := by
    intro q hq0
    by_contra hne
    apply hq0
    have hall : ∀ y : A, χ q.out y = 1 := by
      intro y
      have h1 := sum_out_translate S (χ q.out) (fun a s hs => by rw [hadd, hS1 _ s hs, mul_one]) y
      simp only [hadd, ← Finset.mul_sum] at h1
      exact mul_right_cancel₀ hne (by rw [h1, one_mul])
    have hmem : (c : ℂ) • ((q.out : A) : VC D N N') ∈ A := by
      refine hdual _ fun y hy => ?_
      rw [im_smul_left]
      exact int_of_exp _ (hall ⟨y, hy⟩)
    rw [← QuotientAddGroup.out_eq' q, QuotientAddGroup.eq_zero_iff]
    exact ⟨⟨_, hmem⟩, Subtype.ext (by simpa using hcs _)⟩
  have h0S : (0 : A ⧸ S).out ∈ S := by
    rw [← QuotientAddGroup.eq_zero_iff, QuotientAddGroup.out_eq']
  have hW0 : W D T ((0 : A ⧸ S).out : A) F = F := by
    obtain ⟨b, hb⟩ := h0S
    have := hfix 0 A.zero_mem b b.2
    rw [smul_zero, U_zero] at this
    rw [← hb]
    simpa using this
  apply hF0
  funext z
  have h3 : ∑ r : A ⧸ S, ∑ q : A ⧸ S, χ q.out r.out * W D T (q.out : A) F z = 0 :=
    Finset.sum_eq_zero fun r _ => hsum _ z
  rw [Finset.sum_comm, Finset.sum_eq_single 0 (fun q _ hq0 => by rw [← Finset.sum_mul, hvan q hq0, zero_mul])
    (by simp)] at h3
  simp only [hS2 _ h0S, hW0, one_mul, Finset.sum_const, nsmul_eq_mul, mul_eq_zero, Nat.cast_eq_zero,
    Finset.card_univ, Fintype.card_ne_zero, false_or] at h3
  exact h3

end GlobalTheory.GalTheta

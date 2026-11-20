import Mathlib

open Set ComplexConjugate

set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

noncomputable section

namespace DiscreteGroups.sglob.LConvKM

variable {M : Type*} [AddCommGroup M] [Module ℂ M]

def InvF {G : Type*} [Group G] (ρ : Representation ℂ G M) (B : M →ₗ⋆[ℂ] M →ₗ[ℂ] ℂ) : Prop :=
  (∀ x y, (starRingEnd ℂ) (B x y) = B y x) ∧ (∀ x, 0 ≤ (B x x).re) ∧ ∀ g x y, B (ρ g x) (ρ g y) = B x y

/- English proof (translation)
Use `⟨fun x y => ?_, fun x => ?_, fun g x y => ?_⟩` and prove the remaining obligations. Simplify using `only [LinearMap.smul_apply, smul_eq_mul, map_mul, Complex.conj_ofReal, hB.1 x y]`. Simplify using `only [LinearMap.smul_apply, smul_eq_mul, Complex.re_ofReal_mul]`. Conclude with `mul_nonneg hr (hB.2.1 x)`. Simplify using `only [LinearMap.smul_apply, smul_eq_mul, hB.2.2 g x y]`.
-/
lemma InvF.smul {G : Type*} [Group G] {ρ : Representation ℂ G M} {B : M →ₗ⋆[ℂ] M →ₗ[ℂ] ℂ}
    (hB : InvF ρ B) {r : ℝ} (hr : 0 ≤ r) : InvF ρ ((r : ℂ) • B) := by
  refine ⟨fun x y => ?_, fun x => ?_, fun g x y => ?_⟩
  · simp only [LinearMap.smul_apply, smul_eq_mul, map_mul, Complex.conj_ofReal, hB.1 x y]
  · simp only [LinearMap.smul_apply, smul_eq_mul, Complex.re_ofReal_mul]
    exact mul_nonneg hr (hB.2.1 x)
  · simp only [LinearMap.smul_apply, smul_eq_mul, hB.2.2 g x y]

section form

variable (B : M →ₗ⋆[ℂ] M →ₗ[ℂ] ℂ)

/- English proof (translation)
Establish `h` using `congrArg Complex.im (herm x x)`. Rewrite `h` using `[Complex.conj_im]`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
lemma im_diag (herm : ∀ x y, (starRingEnd ℂ) (B x y) = B y x) (x : M) : (B x x).im = 0 := by
  have h := congrArg Complex.im (herm x x)
  rw [Complex.conj_im] at h
  linarith

/- English proof (translation)
Establish `h : B x x = ((B x x).re : ℂ)` using `(Complex.conj_eq_iff_re.mp (herm x x)).symm`. Use `conv_lhs => rw [h]`. Rewrite using `[Complex.norm_real, Real.norm_of_nonneg (psd x)]`.
-/
lemma norm_diag (herm : ∀ x y, (starRingEnd ℂ) (B x y) = B y x) (psd : ∀ x, 0 ≤ (B x x).re) (x : M) :
    ‖B x x‖ = (B x x).re := by
  have h : B x x = ((B x x).re : ℂ) := (Complex.conj_eq_iff_re.mp (herm x x)).symm
  conv_lhs => rw [h]
  rw [Complex.norm_real, Real.norm_of_nonneg (psd x)]

/- English proof (translation)
Simplify using `only [map_add, map_sub, LinearMap.add_apply, LinearMap.sub_apply]`. Expand and normalize the polynomial expressions, which then agree.
-/
lemma diag_expand_add (x y : M) :
    B (x + y) (x + y) + B (x - y) (x - y) = B x x + B x x + (B y y + B y y) := by
  simp only [map_add, map_sub, LinearMap.add_apply, LinearMap.sub_apply]
  ring

/- English proof (translation)
Establish `h` using `congrArg Complex.re (diag_expand_add B x y)`. Simplify using `only [Complex.add_re] at h`. Combine the linear relations using `[psd (x - y)]`.
-/
lemma re_add_le (psd : ∀ x, 0 ≤ (B x x).re) (x y : M) :
    (B (x + y) (x + y)).re ≤ 2 * (B x x).re + 2 * (B y y).re := by
  have h := congrArg Complex.re (diag_expand_add B x y)
  simp only [Complex.add_re] at h
  linarith [psd (x - y)]

/- English proof (translation)
Simplify using `only [map_smulₛₗ, map_smul, LinearMap.smul_apply, smul_eq_mul, RingHom.id_apply]`. Expand and normalize the polynomial expressions, which then agree.
-/
lemma apply_smul_smul (a : ℂ) (x y : M) : B (a • x) (a • y) = (starRingEnd ℂ) a * a * B x y := by
  simp only [map_smulₛₗ, map_smul, LinearMap.smul_apply, smul_eq_mul, RingHom.id_apply]
  ring

/- English proof (translation)
Rewrite using `[apply_smul_smul, ← Complex.normSq_eq_conj_mul_self, Complex.re_ofReal_mul]`.
-/
lemma re_smul (a : ℂ) (x : M) : (B (a • x) (a • x)).re = Complex.normSq a * (B x x).re := by
  rw [apply_smul_smul, ← Complex.normSq_eq_conj_mul_self, Complex.re_ofReal_mul]

/- English proof (translation)
Simplify using `only [map_add, map_sub, map_smulₛₗ, map_smul, LinearMap.add_apply, LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul, RingHom.id_apply, Complex.conj_I]`. Take the linear combination `(2 * (B x y - B y x)) * Complex.I_sq`.
-/
lemma polar (x y : M) :
    4 * B x y = B (x + y) (x + y) - B (x - y) (x - y) - Complex.I * B (x + Complex.I • y) (x + Complex.I • y)
      + Complex.I * B (x - Complex.I • y) (x - Complex.I • y) := by
  simp only [map_add, map_sub, map_smulₛₗ, map_smul, LinearMap.add_apply, LinearMap.sub_apply,
    LinearMap.smul_apply, smul_eq_mul, RingHom.id_apply, Complex.conj_I]
  linear_combination (2 * (B x y - B y x)) * Complex.I_sq

/- English proof (translation)
Establish `h0 : ‖(4 : ℂ) * B x y‖ = 4 * ‖B x y‖` using `by rw [norm_mul]; norm_num`. Establish `h1` using `norm_add_le (B (x + y) (x + y) - B (x - y) (x - y) - Complex.I * B (x + Complex.I • y) (x + Complex.I • y)) (Complex.I * B (x - Complex.I • y) (x - Complex.I • y))`. Establish `h2` using `norm_sub_le (B (x + y) (x + y) - B (x - y) (x - y)) (Complex.I * B (x + Complex.I • y) (x + Complex.I • y))`. Establish `h3` using `norm_sub_le (B (x + y) (x + y)) (B (x - y) (x - y))`. Simplify using `only [norm_mul, Complex.norm_I, one_mul] at h1 h2`.

Rewrite `h1` using `[← polar B x y, h0]`. Simplify using `only [norm_diag B herm psd] at h1 h2 h3`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
lemma norm_le_polar (herm : ∀ x y, (starRingEnd ℂ) (B x y) = B y x) (psd : ∀ x, 0 ≤ (B x x).re)
    (x y : M) :
    4 * ‖B x y‖ ≤ (B (x + y) (x + y)).re + (B (x - y) (x - y)).re
      + (B (x + Complex.I • y) (x + Complex.I • y)).re + (B (x - Complex.I • y) (x - Complex.I • y)).re := by
  have h0 : ‖(4 : ℂ) * B x y‖ = 4 * ‖B x y‖ := by rw [norm_mul]; norm_num
  have h1 := norm_add_le (B (x + y) (x + y) - B (x - y) (x - y)
    - Complex.I * B (x + Complex.I • y) (x + Complex.I • y)) (Complex.I * B (x - Complex.I • y) (x - Complex.I • y))
  have h2 := norm_sub_le (B (x + y) (x + y) - B (x - y) (x - y))
    (Complex.I * B (x + Complex.I • y) (x + Complex.I • y))
  have h3 := norm_sub_le (B (x + y) (x + y)) (B (x - y) (x - y))
  simp only [norm_mul, Complex.norm_I, one_mul] at h1 h2
  rw [← polar B x y, h0] at h1
  simp only [norm_diag B herm psd] at h1 h2 h3
  linarith

/- English proof (translation)
Assume the negation of the conclusion as `ha`. Establish `hN : 0 < Complex.normSq (B u y)` using `Complex.normSq_pos.mpr ha`. Establish `hN' : Complex.normSq (B u y) ≠ 0` using `hN.ne'`. Establish `huu : B u u = 0` using `Complex.ext (by simpa using hu) (by simpa using im_diag B herm u)`. Establish `hyu : B y u = (starRingEnd ℂ) (B u y)` using `(herm u y).symm`.

Take `⟨t, ht⟩ : ∃ t : ℝ, 2 * t * Complex.normSq (B u y) = (B y y).re + 1` from `⟨((B y y).re + 1) / (2 * Complex.normSq (B u y)), by field_simp⟩`. Establish `ex : B (y - ((t : ℂ) * B u y) • u) (y - ((t : ℂ) * B u y) • u) = B y y - ((t : ℂ) * B u y) * B y u - (starRingEnd ℂ) ((t : ℂ) * B u y) * B u y + (starRingEnd ℂ) ((t : ℂ) * B u y) * ((t : ℂ) * B u y) * B u u`. Simplify using `only [map_sub, map_smulₛₗ, map_smul, LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul, RingHom.id_apply]`. Expand and normalize the polynomial expressions, which then agree. Establish `key : B (y - ((t : ℂ) * B u y) • u) (y - ((t : ℂ) * B u y) • u) = B y y - ((2 * t * Complex.normSq (B u y) : ℝ) : ℂ)`.

Rewrite using `[ex, hyu, huu, map_mul, Complex.conj_ofReal]`. Use `push_cast`. Rewrite using `[Complex.normSq_eq_conj_mul_self]`. Expand and normalize the polynomial expressions, which then agree. Establish `h` using `psd (y - ((t : ℂ) * B u y) • u)`.

Rewrite `h` using `[key, Complex.sub_re, Complex.ofReal_re, ht]`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
lemma apply_eq_zero_of_re (herm : ∀ x y, (starRingEnd ℂ) (B x y) = B y x) (psd : ∀ x, 0 ≤ (B x x).re)
    (u : M) (hu : (B u u).re = 0) (y : M) : B u y = 0 := by
  by_contra ha
  have hN : 0 < Complex.normSq (B u y) := Complex.normSq_pos.mpr ha
  have hN' : Complex.normSq (B u y) ≠ 0 := hN.ne'
  have huu : B u u = 0 := Complex.ext (by simpa using hu) (by simpa using im_diag B herm u)
  have hyu : B y u = (starRingEnd ℂ) (B u y) := (herm u y).symm
  obtain ⟨t, ht⟩ : ∃ t : ℝ, 2 * t * Complex.normSq (B u y) = (B y y).re + 1 :=
    ⟨((B y y).re + 1) / (2 * Complex.normSq (B u y)), by field_simp⟩
  have ex : B (y - ((t : ℂ) * B u y) • u) (y - ((t : ℂ) * B u y) • u)
      = B y y - ((t : ℂ) * B u y) * B y u - (starRingEnd ℂ) ((t : ℂ) * B u y) * B u y
        + (starRingEnd ℂ) ((t : ℂ) * B u y) * ((t : ℂ) * B u y) * B u u := by
    simp only [map_sub, map_smulₛₗ, map_smul, LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul,
      RingHom.id_apply]
    ring
  have key : B (y - ((t : ℂ) * B u y) • u) (y - ((t : ℂ) * B u y) • u)
      = B y y - ((2 * t * Complex.normSq (B u y) : ℝ) : ℂ) := by
    rw [ex, hyu, huu, map_mul, Complex.conj_ofReal]
    push_cast
    rw [Complex.normSq_eq_conj_mul_self]
    ring
  have h := psd (y - ((t : ℂ) * B u y) • u)
  rw [key, Complex.sub_re, Complex.ofReal_re, ht] at h
  linarith

/- English proof (translation)
Establish `hle : Submodule.span ℂ (Set.range xs) ≤ LinearMap.ker B`. Rewrite using `[Submodule.span_le]`. Introduce and unpack `_ ⟨i, rfl⟩`. Rewrite using `[SetLike.mem_coe, LinearMap.mem_ker]`. Use extensionality with `z`.

Rewrite using `[LinearMap.zero_apply]`. Conclude with `apply_eq_zero_of_re B herm psd (xs i) (h i) z`. Establish `hx : x ∈ LinearMap.ker B` using `hle (by rw [hsp]; exact Submodule.mem_top)`. Rewrite `hx` using `[LinearMap.mem_ker]`. Rewrite using `[hx, LinearMap.zero_apply]`.
-/
lemma eq_zero_of_re (herm : ∀ x y, (starRingEnd ℂ) (B x y) = B y x) (psd : ∀ x, 0 ≤ (B x x).re)
    (xs : ℕ → M) (hsp : Submodule.span ℂ (Set.range xs) = ⊤)
    (h : ∀ i, (B (xs i) (xs i)).re = 0) (x y : M) : B x y = 0 := by
  have hle : Submodule.span ℂ (Set.range xs) ≤ LinearMap.ker B := by
    rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    rw [SetLike.mem_coe, LinearMap.mem_ker]
    ext z
    rw [LinearMap.zero_apply]
    exact apply_eq_zero_of_re B herm psd (xs i) (h i) z
  have hx : x ∈ LinearMap.ker B := hle (by rw [hsp]; exact Submodule.mem_top)
  rw [LinearMap.mem_ker] at hx
  rw [hx, LinearMap.zero_apply]

end form

/- English proof (translation)
The claim follows from `(continuous_apply b).comp (continuous_apply a)`.
-/
lemma continuous_eval (a b : M) : Continuous fun F : M → M → ℂ => F a b :=
  (continuous_apply b).comp (continuous_apply a)

/- English proof (translation)
Simplify using `only [Pi.add_apply, Pi.smul_apply, Complex.real_smul]`.
-/
lemma comb_apply (F G : M → M → ℂ) (a b : ℝ) (x y : M) :
    (a • F + b • G) x y = (a : ℂ) * F x y + (b : ℂ) * G x y := by
  simp only [Pi.add_apply, Pi.smul_apply, Complex.real_smul]

def ev (B : M →ₗ⋆[ℂ] M →ₗ[ℂ] ℂ) : M → M → ℂ := fun x y => B x y

def sesqSet : Set (M → M → ℂ) :=
  {F | ∀ x y z, F (x + y) z = F x z + F y z} ∩ {F | ∀ (a : ℂ) x z, F (a • x) z = (starRingEnd ℂ) a * F x z} ∩
    {F | ∀ x y z, F x (y + z) = F x y + F x z} ∩ {F | ∀ (a : ℂ) x y, F x (a • y) = a * F x y}

def mkForm (F : M → M → ℂ) (h : F ∈ (sesqSet : Set (M → M → ℂ))) : M →ₗ⋆[ℂ] M →ₗ[ℂ] ℂ :=
  LinearMap.mk₂'ₛₗ (starRingEnd ℂ) (RingHom.id ℂ) F h.1.1.1 (fun a x z => h.1.1.2 a x z) h.1.2
    (fun a x y => h.2 a x y)

/- English proof (translation)
Both sides reduce to the same expression.
-/
@[simp] lemma mkForm_apply (F : M → M → ℂ) (h : F ∈ (sesqSet : Set (M → M → ℂ))) (x y : M) :
    mkForm F h x y = F x y := rfl

/- English proof (translation)
Apply the tactic sequence `refine ⟨⟨⟨fun x y z => ?_, fun a x z => ?_⟩, fun x y z => ?_⟩, fun a x y => ?_⟩ <;>`. Simplify using `[ev]`.
-/
lemma ev_mem_sesq (B : M →ₗ⋆[ℂ] M →ₗ[ℂ] ℂ) : ev B ∈ (sesqSet : Set (M → M → ℂ)) := by
  refine ⟨⟨⟨fun x y z => ?_, fun a x z => ?_⟩, fun x y z => ?_⟩, fun a x y => ?_⟩ <;>
    simp [ev]

/- English proof (translation)
Simplify using `only [sesqSet, Set.ofPred_forall]`. Use `((IsClosed.inter ?_ ?_).inter ?_).inter ?_` and prove the remaining obligations. Conclude with `isClosed_iInter fun x => isClosed_iInter fun y => isClosed_iInter fun z => isClosed_eq (continuous_eval _ _) ((continuous_eval _ _).add (continuous_eval _ _))`. Conclude with `isClosed_iInter fun a => isClosed_iInter fun x => isClosed_iInter fun z => isClosed_eq (continuous_eval _ _) (continuous_const.mul (continuous_eval _ _))`. Conclude with `isClosed_iInter fun x => isClosed_iInter fun y => isClosed_iInter fun z => isClosed_eq (continuous_eval _ _) ((continuous_eval _ _).add (continuous_eval _ _))`.

Conclude with `isClosed_iInter fun a => isClosed_iInter fun x => isClosed_iInter fun y => isClosed_eq (continuous_eval _ _) (continuous_const.mul (continuous_eval _ _))`.
-/
lemma isClosed_sesqSet : IsClosed (sesqSet : Set (M → M → ℂ)) := by
  simp only [sesqSet, Set.ofPred_forall]
  refine ((IsClosed.inter ?_ ?_).inter ?_).inter ?_
  · exact isClosed_iInter fun x => isClosed_iInter fun y => isClosed_iInter fun z =>
      isClosed_eq (continuous_eval _ _) ((continuous_eval _ _).add (continuous_eval _ _))
  · exact isClosed_iInter fun a => isClosed_iInter fun x => isClosed_iInter fun z =>
      isClosed_eq (continuous_eval _ _) (continuous_const.mul (continuous_eval _ _))
  · exact isClosed_iInter fun x => isClosed_iInter fun y => isClosed_iInter fun z =>
      isClosed_eq (continuous_eval _ _) ((continuous_eval _ _).add (continuous_eval _ _))
  · exact isClosed_iInter fun a => isClosed_iInter fun x => isClosed_iInter fun y =>
      isClosed_eq (continuous_eval _ _) (continuous_const.mul (continuous_eval _ _))

section cap

variable {G : Type*} [Group G] (ρ : Representation ℂ G M) (c : ℕ → ℝ) (xs : ℕ → M)

def Cap (F : M → M → ℂ) : Prop := ∀ n, ∑ i ∈ Finset.range n, c i * (F (xs i) (xs i)).re ≤ 1

def capSet : Set (M → M → ℂ) :=
  (sesqSet : Set (M → M → ℂ)) ∩ {F | ∀ x y, (starRingEnd ℂ) (F x y) = F y x} ∩ {F | ∀ x, 0 ≤ (F x x).re} ∩
    {F | ∀ g x y, F (ρ g x) (ρ g y) = F x y} ∩ {F | Cap c xs F}

/- English proof (translation)
Assemble the required witnesses or components as `⟨h.1.1.1.2, h.1.1.2, h.1.2⟩`.
-/
lemma invF_mkForm {F : M → M → ℂ} (h : F ∈ capSet ρ c xs) : InvF ρ (mkForm F h.1.1.1.1) :=
  ⟨h.1.1.1.2, h.1.1.2, h.1.2⟩

/- English proof (translation)
Assemble the required witnesses or components as `⟨⟨⟨⟨ev_mem_sesq B, hB.1⟩, hB.2.1⟩, hB.2.2⟩, hc⟩`.
-/
lemma ev_mem {B : M →ₗ⋆[ℂ] M →ₗ[ℂ] ℂ} (hB : InvF ρ B) (hc : Cap c xs (ev B)) : ev B ∈ capSet ρ c xs :=
  ⟨⟨⟨⟨ev_mem_sesq B, hB.1⟩, hB.2.1⟩, hB.2.2⟩, hc⟩

/- English proof (translation)
Simplify using `only [capSet, Cap, Set.ofPred_forall]`. Use `(((isClosed_sesqSet.inter ?_).inter ?_).inter ?_).inter ?_` and prove the remaining obligations. Conclude with `isClosed_iInter fun x => isClosed_iInter fun y => isClosed_eq (Complex.continuous_conj.comp (continuous_eval _ _)) (continuous_eval _ _)`. Conclude with `isClosed_iInter fun x => isClosed_le continuous_const (Complex.continuous_re.comp (continuous_eval _ _))`. Conclude with `isClosed_iInter fun g => isClosed_iInter fun x => isClosed_iInter fun y => isClosed_eq (continuous_eval _ _) (continuous_eval _ _)`.

Conclude with `isClosed_iInter fun n => isClosed_le (continuous_finsetSum _ fun i _ => continuous_const.mul (Complex.continuous_re.comp (continuous_eval _ _))) continuous_const`.
-/
lemma isClosed_capSet : IsClosed (capSet ρ c xs) := by
  simp only [capSet, Cap, Set.ofPred_forall]
  refine (((isClosed_sesqSet.inter ?_).inter ?_).inter ?_).inter ?_
  · exact isClosed_iInter fun x => isClosed_iInter fun y =>
      isClosed_eq (Complex.continuous_conj.comp (continuous_eval _ _)) (continuous_eval _ _)
  · exact isClosed_iInter fun x => isClosed_le continuous_const (Complex.continuous_re.comp (continuous_eval _ _))
  · exact isClosed_iInter fun g => isClosed_iInter fun x => isClosed_iInter fun y =>
      isClosed_eq (continuous_eval _ _) (continuous_eval _ _)
  · exact isClosed_iInter fun n => isClosed_le
      (continuous_finsetSum _ fun i _ => continuous_const.mul (Complex.continuous_re.comp (continuous_eval _ _)))
      continuous_const

/- English proof (translation)
Introduce `F hF G hG a b ha hb hab`. Take `⟨⟨⟨⟨⟨⟨⟨f1, f2⟩, f3⟩, f4⟩, fh⟩, fp⟩, fi⟩, fk⟩` from `hF`. Take `⟨⟨⟨⟨⟨⟨⟨g1, g2⟩, g3⟩, g4⟩, gh⟩, gp⟩, gi⟩, gk⟩` from `hG`. Use `⟨⟨⟨⟨⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩` and prove the remaining obligations. Introduce `x y z`.

Simplify using `only [comb_apply, f1 x y z, g1 x y z]`. Expand and normalize the polynomial expressions, which then agree. Introduce `α x z`. Simplify using `only [comb_apply, f2 α x z, g2 α x z]`. Expand and normalize the polynomial expressions, which then agree.

Introduce `x y z`. Simplify using `only [comb_apply, f3 x y z, g3 x y z]`. Expand and normalize the polynomial expressions, which then agree. Introduce `α x y`. Simplify using `only [comb_apply, f4 α x y, g4 α x y]`.

Expand and normalize the polynomial expressions, which then agree. Introduce `x y`. Simplify using `only [comb_apply, map_add, map_mul, Complex.conj_ofReal, fh x y, gh x y]`. Introduce `x`. Simplify using `only [comb_apply, Complex.add_re, Complex.re_ofReal_mul]`.

Conclude with `add_nonneg (mul_nonneg ha (fp x)) (mul_nonneg hb (gp x))`. Introduce `g x y`. Simplify using `only [comb_apply, fi g x y, gi g x y]`. Introduce `n`. Establish `e : ∑ i ∈ Finset.range n, c i * ((a • F + b • G) (xs i) (xs i)).re = a * ∑ i ∈ Finset.range n, c i * (F (xs i) (xs i)).re + b * ∑ i ∈ Finset.range n, c i * (G (xs i) (xs i)).re`.

Rewrite using `[Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Simplify using `only [comb_apply, Complex.add_re, Complex.re_ofReal_mul]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e]`.

Combine the linear relations using `[mul_le_mul_of_nonneg_left (fk n) ha, mul_le_mul_of_nonneg_left (gk n) hb]`.
-/
lemma convex_capSet : Convex ℝ (capSet ρ c xs) := by
  intro F hF G hG a b ha hb hab
  obtain ⟨⟨⟨⟨⟨⟨⟨f1, f2⟩, f3⟩, f4⟩, fh⟩, fp⟩, fi⟩, fk⟩ := hF
  obtain ⟨⟨⟨⟨⟨⟨⟨g1, g2⟩, g3⟩, g4⟩, gh⟩, gp⟩, gi⟩, gk⟩ := hG
  refine ⟨⟨⟨⟨⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩
  · intro x y z; simp only [comb_apply, f1 x y z, g1 x y z]; ring
  · intro α x z; simp only [comb_apply, f2 α x z, g2 α x z]; ring
  · intro x y z; simp only [comb_apply, f3 x y z, g3 x y z]; ring
  · intro α x y; simp only [comb_apply, f4 α x y, g4 α x y]; ring
  · intro x y; simp only [comb_apply, map_add, map_mul, Complex.conj_ofReal, fh x y, gh x y]
  · intro x
    simp only [comb_apply, Complex.add_re, Complex.re_ofReal_mul]
    exact add_nonneg (mul_nonneg ha (fp x)) (mul_nonneg hb (gp x))
  · intro g x y; simp only [comb_apply, fi g x y, gi g x y]
  · intro n
    have e : ∑ i ∈ Finset.range n, c i * ((a • F + b • G) (xs i) (xs i)).re
        = a * ∑ i ∈ Finset.range n, c i * (F (xs i) (xs i)).re
          + b * ∑ i ∈ Finset.range n, c i * (G (xs i) (xs i)).re := by
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      simp only [comb_apply, Complex.add_re, Complex.re_ofReal_mul]
      ring
    rw [e]
    linarith [mul_le_mul_of_nonneg_left (fk n) ha, mul_le_mul_of_nonneg_left (gk n) hb]

/- English proof (translation)
Establish `hx : x ∈ Submodule.span ℂ (Set.range xs)` using `by rw [hsp]; exact Submodule.mem_top`. Proceed by induction on `hx using Submodule.span_induction with`. Consider the case `mem x hx`. Take `⟨i, rfl⟩` from `hx`. Use `⟨1 / c i, fun F hF => ?_⟩` and prove the remaining obligations.

Establish `h1` using `Finset.single_le_sum (f := fun j => c j * (F (xs j) (xs j)).re) (fun j _ => mul_nonneg (hc j).le (hF.1.1.2 (xs j))) (Finset.self_mem_range_succ i)`. Establish `h2` using `hF.2 (i + 1)`. Rewrite using `[le_div_iff₀ (hc i)]`. Combine the linear relations using `[mul_comm (F (xs i) (xs i)).re (c i)]`. Consider the case `zero`.

Use `⟨0, fun F hF => ?_⟩` and prove the remaining obligations. Establish `h : mkForm F hF.1.1.1.1 0 0 = 0` using `by simp only [map_zero, LinearMap.zero_apply]`. Rewrite `h` using `[mkForm_apply]`. Rewrite using `[h, Complex.zero_re]`. Consider the case `add x y _ _ hx hy`.

Take `⟨R₁, h₁⟩` from `hx`. Take `⟨R₂, h₂⟩` from `hy`. Use `⟨2 * R₁ + 2 * R₂, fun F hF => ?_⟩` and prove the remaining obligations. Use `re_add_le (mkForm F hF.1.1.1.1) hF.1.1.2 x y` as an intermediate fact. Simplify using `only [mkForm_apply] at this`.

Combine the linear relations using `[h₁ F hF, h₂ F hF]`. Consider the case `smul a x _ hx`. Take `⟨R, h⟩` from `hx`. Use `⟨Complex.normSq a * R, fun F hF => ?_⟩` and prove the remaining obligations. Use `re_smul (mkForm F hF.1.1.1.1) a x` as an intermediate fact.

Simplify using `only [mkForm_apply] at this`. Rewrite using `[this]`. Conclude with `mul_le_mul_of_nonneg_left (h F hF) (Complex.normSq_nonneg a)`.
-/
lemma diag_bound (hsp : Submodule.span ℂ (Set.range xs) = ⊤) (hc : ∀ i, 0 < c i) (x : M) :
    ∃ R, ∀ F ∈ capSet ρ c xs, (F x x).re ≤ R := by
  have hx : x ∈ Submodule.span ℂ (Set.range xs) := by rw [hsp]; exact Submodule.mem_top
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨i, rfl⟩ := hx
    refine ⟨1 / c i, fun F hF => ?_⟩
    have h1 := Finset.single_le_sum (f := fun j => c j * (F (xs j) (xs j)).re)
      (fun j _ => mul_nonneg (hc j).le (hF.1.1.2 (xs j))) (Finset.self_mem_range_succ i)
    have h2 := hF.2 (i + 1)
    rw [le_div_iff₀ (hc i)]
    linarith [mul_comm (F (xs i) (xs i)).re (c i)]
  | zero =>
    refine ⟨0, fun F hF => ?_⟩
    have h : mkForm F hF.1.1.1.1 0 0 = 0 := by simp only [map_zero, LinearMap.zero_apply]
    rw [mkForm_apply] at h
    rw [h, Complex.zero_re]
  | add x y _ _ hx hy =>
    obtain ⟨R₁, h₁⟩ := hx
    obtain ⟨R₂, h₂⟩ := hy
    refine ⟨2 * R₁ + 2 * R₂, fun F hF => ?_⟩
    have := re_add_le (mkForm F hF.1.1.1.1) hF.1.1.2 x y
    simp only [mkForm_apply] at this
    linarith [h₁ F hF, h₂ F hF]
  | smul a x _ hx =>
    obtain ⟨R, h⟩ := hx
    refine ⟨Complex.normSq a * R, fun F hF => ?_⟩
    have := re_smul (mkForm F hF.1.1.1.1) a x
    simp only [mkForm_apply] at this
    rw [this]
    exact mul_le_mul_of_nonneg_left (h F hF) (Complex.normSq_nonneg a)

/- English proof (translation)
Take `⟨R₁, h₁⟩` from `diag_bound ρ c xs hsp hc (x + y)`. Take `⟨R₂, h₂⟩` from `diag_bound ρ c xs hsp hc (x - y)`. Take `⟨R₃, h₃⟩` from `diag_bound ρ c xs hsp hc (x + Complex.I • y)`. Take `⟨R₄, h₄⟩` from `diag_bound ρ c xs hsp hc (x - Complex.I • y)`. Use `⟨(R₁ + R₂ + R₃ + R₄) / 4, fun F hF => ?_⟩` and prove the remaining obligations.

Use `norm_le_polar (mkForm F hF.1.1.1.1) hF.1.1.1.2 hF.1.1.2 x y` as an intermediate fact. Simplify using `only [mkForm_apply] at this`. Combine the linear relations using `[h₁ F hF, h₂ F hF, h₃ F hF, h₄ F hF]`.
-/
lemma off_bound (hsp : Submodule.span ℂ (Set.range xs) = ⊤) (hc : ∀ i, 0 < c i) (x y : M) :
    ∃ R, ∀ F ∈ capSet ρ c xs, ‖F x y‖ ≤ R := by
  obtain ⟨R₁, h₁⟩ := diag_bound ρ c xs hsp hc (x + y)
  obtain ⟨R₂, h₂⟩ := diag_bound ρ c xs hsp hc (x - y)
  obtain ⟨R₃, h₃⟩ := diag_bound ρ c xs hsp hc (x + Complex.I • y)
  obtain ⟨R₄, h₄⟩ := diag_bound ρ c xs hsp hc (x - Complex.I • y)
  refine ⟨(R₁ + R₂ + R₃ + R₄) / 4, fun F hF => ?_⟩
  have := norm_le_polar (mkForm F hF.1.1.1.1) hF.1.1.1.2 hF.1.1.2 x y
  simp only [mkForm_apply] at this
  linarith [h₁ F hF, h₂ F hF, h₃ F hF, h₄ F hF]

/- English proof (translation)
Use `choose R hR using off_bound ρ c xs hsp hc`. Use `IsCompact.of_isClosed_subset (isCompact_univ_pi fun x => isCompact_univ_pi fun y => isCompact_closedBall (0 : ℂ) (R x y)) (isClosed_capSet ρ c xs) fun F hF => ?_` and prove the remaining obligations. Simplify using `only [Set.mem_univ_pi, Metric.mem_closedBall, dist_zero_right]`. Conclude with `fun x y => hR x y F hF`.
-/
lemma isCompact_capSet (hsp : Submodule.span ℂ (Set.range xs) = ⊤) (hc : ∀ i, 0 < c i) :
    IsCompact (capSet ρ c xs) := by
  choose R hR using off_bound ρ c xs hsp hc
  refine IsCompact.of_isClosed_subset
    (isCompact_univ_pi fun x => isCompact_univ_pi fun y => isCompact_closedBall (0 : ℂ) (R x y))
    (isClosed_capSet ρ c xs) fun F hF => ?_
  simp only [Set.mem_univ_pi, Metric.mem_closedBall, dist_zero_right]
  exact fun x y => hR x y F hF

/- English proof (translation)
Take `⟨hBm, hBx⟩` from `mem_extremePoints.mp hB`. Establish `hcapB : ∀ n, ∑ i ∈ Finset.range n, c i * (B (xs i) (xs i)).re ≤ 1` using `hBm.2`. Establish `hsplit : ∀ i, c i * (B (xs i) (xs i)).re = c i * (B' (xs i) (xs i)).re + c i * ((B - B') (xs i) (xs i)).re`. Introduce `i`. Rewrite using `[LinearMap.sub_apply, LinearMap.sub_apply, Complex.sub_re]`.

Expand and normalize the polynomial expressions, which then agree. Establish `h0' : ∀ i, 0 ≤ c i * (B' (xs i) (xs i)).re` using `fun i => mul_nonneg (hc i).le (h1.2.1 _)`. Establish `h0'' : ∀ i, 0 ≤ c i * ((B - B') (xs i) (xs i)).re` using `fun i => mul_nonneg (hc i).le (h2.2.1 _)`. Establish `hb' : ∀ n, ∑ i ∈ Finset.range n, c i * (B' (xs i) (xs i)).re ≤ 1` using `fun n => by`. Use `hcapB n` as an intermediate fact.

Simplify using `only [hsplit, Finset.sum_add_distrib] at this`. Combine the linear relations using `[Finset.sum_nonneg fun i (_ : i ∈ Finset.range n) => h0'' i]`. Establish `hb'' : ∀ n, ∑ i ∈ Finset.range n, c i * ((B - B') (xs i) (xs i)).re ≤ 1` using `fun n => by`. Use `hcapB n` as an intermediate fact. Simplify using `only [hsplit, Finset.sum_add_distrib] at this`.

Combine the linear relations using `[Finset.sum_nonneg fun i (_ : i ∈ Finset.range n) => h0' i]`. Establish `hs'` using `summable_of_sum_range_le h0' hb'`. Establish `hs''` using `summable_of_sum_range_le h0'' hb''`. Establish `hP : ∑' i, c i * (B' (xs i) (xs i)).re + ∑' i, c i * ((B - B') (xs i) (xs i)).re ≤ 1`. Rewrite using `[← hs'.tsum_add hs'']`.

Use `(hs'.add hs'').tsum_le_of_sum_range_le fun n => ?_` and prove the remaining obligations. Use `hcapB n` as an intermediate fact. Simplify using `only [hsplit] at this`. Conclude with `this`. Establish `hle' : ∀ n, ∑ i ∈ Finset.range n, c i * (B' (xs i) (xs i)).re ≤ ∑' i, c i * (B' (xs i) (xs i)).re` using `fun n => hs'.sum_le_tsum _ (fun i _ => h0' i)`.

Establish `hle'' : ∀ n, ∑ i ∈ Finset.range n, c i * ((B - B') (xs i) (xs i)).re ≤ ∑' i, c i * ((B - B') (xs i) (xs i)).re` using `fun n => hs''.sum_le_tsum _ (fun i _ => h0'' i)`. Establish `hi' : ∀ i, c i * (B' (xs i) (xs i)).re ≤ ∑' i, c i * (B' (xs i) (xs i)).re` using `fun i => hs'.le_tsum i (fun j _ => h0' j)`. Establish `hi'' : ∀ i, c i * ((B - B') (xs i) (xs i)).re ≤ ∑' i, c i * ((B - B') (xs i) (xs i)).re` using `fun i => hs''.le_tsum i (fun j _ => h0'' j)`. Establish `hnn' : 0 ≤ ∑' i, c i * (B' (xs i) (xs i)).re` using `tsum_nonneg h0'`. Establish `hnn'' : 0 ≤ ∑' i, c i * ((B - B') (xs i) (xs i)).re` using `tsum_nonneg h0''`.

Generalize the expression as in `∑' i, c i * (B' (xs i) (xs i)).re = p' at hP hle' hi' hnn'`. Generalize the expression as in `∑' i, c i * ((B - B') (xs i) (xs i)).re = p'' at hP hle'' hi'' hnn''`. Establish `zero_of : ∀ B₁ : M →ₗ⋆[ℂ] M →ₗ[ℂ] ℂ, InvF ρ B₁ → (∀ i, c i * (B₁ (xs i) (xs i)).re ≤ 0) → ∀ x y, B₁ x y = 0`. Introduce `B₁ hB₁ hle x y`. Use `eq_zero_of_re B₁ hB₁.1 hB₁.2.1 xs hsp (fun i => ?_) x y` and prove the remaining obligations.

Establish `h0` using `mul_nonneg (hc i).le (hB₁.2.1 (xs i))`. Use `le_antisymm (hle i) h0` as an intermediate fact. Conclude with `(mul_eq_zero.mp this).resolve_left (hc i).ne'`. Break down `hnn'.lt_or_eq with hp' | hp'` into its components or cases. Use `swap`.

Use `⟨0, fun x y => ?_⟩` and prove the remaining obligations. Rewrite using `[zero_of B' h1 (fun i => (hi' i).trans hp'.ge) x y, zero_mul]`. Break down `hnn''.lt_or_eq with hp'' | hp''` into its components or cases. Use `swap`. Use `⟨1, fun x y => ?_⟩` and prove the remaining obligations.

Use `zero_of (B - B') h2 (fun i => (hi'' i).trans hp''.ge) x y` as an intermediate fact. Rewrite `this` using `[LinearMap.sub_apply, LinearMap.sub_apply, sub_eq_zero]`. Rewrite using `[this, one_mul]`. Establish `hPpos : 0 < p' + p''` using `by linarith`. Establish `hne'` using `hp'.ne'`.

Establish `hne''` using `hp''.ne'`. Establish `hPne` using `hPpos.ne'`. Establish `hr' : (0 : ℝ) ≤ (p' + p'') / p'` using `div_nonneg hPpos.le hp'.le`. Establish `hr'' : (0 : ℝ) ≤ (p' + p'') / p''` using `div_nonneg hPpos.le hp''.le`. Establish `hF1 : ev ((((p' + p'') / p' : ℝ) : ℂ) • B') ∈ capSet ρ c xs`.

Use `ev_mem ρ c xs (h1.smul hr') fun n => ?_` and prove the remaining obligations. Use `show ∑ i ∈ Finset.range n, c i * (((((p' + p'') / p' : ℝ) : ℂ) • B') (xs i) (xs i)).re ≤ 1`. Establish `e : ∑ i ∈ Finset.range n, c i * (((((p' + p'') / p' : ℝ) : ℂ) • B') (xs i) (xs i)).re = (p' + p'') / p' * ∑ i ∈ Finset.range n, c i * (B' (xs i) (xs i)).re`. Rewrite using `[Finset.mul_sum]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations.

Simplify using `only [LinearMap.smul_apply, smul_eq_mul, Complex.re_ofReal_mul]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e]`. Combine the equalities or inequalities in the displayed calculation. Establish `hF2 : ev ((((p' + p'') / p'' : ℝ) : ℂ) • (B - B')) ∈ capSet ρ c xs`.

Use `ev_mem ρ c xs (h2.smul hr'') fun n => ?_` and prove the remaining obligations. Use `show ∑ i ∈ Finset.range n, c i * (((((p' + p'') / p'' : ℝ) : ℂ) • (B - B')) (xs i) (xs i)).re ≤ 1`. Establish `e : ∑ i ∈ Finset.range n, c i * (((((p' + p'') / p'' : ℝ) : ℂ) • (B - B')) (xs i) (xs i)).re = (p' + p'') / p'' * ∑ i ∈ Finset.range n, c i * ((B - B') (xs i) (xs i)).re`. Rewrite using `[Finset.mul_sum]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations.

Simplify using `only [LinearMap.smul_apply, smul_eq_mul, Complex.re_ofReal_mul]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e]`. Combine the equalities or inequalities in the displayed calculation. Establish `k1r : p' / (p' + p'') * ((p' + p'') / p') = 1` using `by field_simp`.

Establish `k2r : p'' / (p' + p'') * ((p' + p'') / p'') = 1` using `by field_simp`. Establish `k1 : ((p' / (p' + p'') : ℝ) : ℂ) * (((p' + p'') / p' : ℝ) : ℂ) = 1`. Rewrite using `[← Complex.ofReal_mul, k1r, Complex.ofReal_one]`. Establish `k2 : ((p'' / (p' + p'') : ℝ) : ℂ) * (((p' + p'') / p'' : ℝ) : ℂ) = 1`. Rewrite using `[← Complex.ofReal_mul, k2r, Complex.ofReal_one]`.

Establish `hseg : ev B ∈ openSegment ℝ (ev ((((p' + p'') / p' : ℝ) : ℂ) • B')) (ev ((((p' + p'') / p'' : ℝ) : ℂ) • (B - B')))`. Use `⟨p' / (p' + p''), p'' / (p' + p''), div_pos hp' hPpos, div_pos hp'' hPpos, by field_simp, ?_⟩` and prove the remaining obligations. Use function extensionality and compare the values at `x y`. Rewrite using `[comb_apply]`. Simplify using `only [ev, LinearMap.smul_apply, LinearMap.sub_apply, smul_eq_mul]`.

Take the linear combination `(B' x y) * k1 + (B x y - B' x y) * k2`. Establish `hx` using `hBx _ hF1 _ hF2 hseg`. Use `⟨((p' / (p' + p'') : ℝ) : ℂ), fun x y => ?_⟩` and prove the remaining obligations. Establish `e` using `congrFun (congrFun hx.1 x) y`. Simplify using `only [ev, LinearMap.smul_apply, smul_eq_mul] at e`.

Rewrite using `[← e]`. Take the linear combination `(-(B' x y)) * k1`.
-/
lemma ray (hsp : Submodule.span ℂ (Set.range xs) = ⊤) (hc : ∀ i, 0 < c i) (B : M →ₗ⋆[ℂ] M →ₗ[ℂ] ℂ)
    (hB : ev B ∈ (capSet ρ c xs).extremePoints ℝ) (B' : M →ₗ⋆[ℂ] M →ₗ[ℂ] ℂ)
    (h1 : InvF ρ B') (h2 : InvF ρ (B - B')) : ∃ k : ℂ, ∀ x y, B' x y = k * B x y := by
  obtain ⟨hBm, hBx⟩ := mem_extremePoints.mp hB
  have hcapB : ∀ n, ∑ i ∈ Finset.range n, c i * (B (xs i) (xs i)).re ≤ 1 := hBm.2
  have hsplit : ∀ i, c i * (B (xs i) (xs i)).re
      = c i * (B' (xs i) (xs i)).re + c i * ((B - B') (xs i) (xs i)).re := by
    intro i; rw [LinearMap.sub_apply, LinearMap.sub_apply, Complex.sub_re]; ring
  have h0' : ∀ i, 0 ≤ c i * (B' (xs i) (xs i)).re := fun i => mul_nonneg (hc i).le (h1.2.1 _)
  have h0'' : ∀ i, 0 ≤ c i * ((B - B') (xs i) (xs i)).re := fun i => mul_nonneg (hc i).le (h2.2.1 _)
  have hb' : ∀ n, ∑ i ∈ Finset.range n, c i * (B' (xs i) (xs i)).re ≤ 1 := fun n => by
    have := hcapB n
    simp only [hsplit, Finset.sum_add_distrib] at this
    linarith [Finset.sum_nonneg fun i (_ : i ∈ Finset.range n) => h0'' i]
  have hb'' : ∀ n, ∑ i ∈ Finset.range n, c i * ((B - B') (xs i) (xs i)).re ≤ 1 := fun n => by
    have := hcapB n
    simp only [hsplit, Finset.sum_add_distrib] at this
    linarith [Finset.sum_nonneg fun i (_ : i ∈ Finset.range n) => h0' i]
  have hs' := summable_of_sum_range_le h0' hb'
  have hs'' := summable_of_sum_range_le h0'' hb''
  have hP : ∑' i, c i * (B' (xs i) (xs i)).re + ∑' i, c i * ((B - B') (xs i) (xs i)).re ≤ 1 := by
    rw [← hs'.tsum_add hs'']
    refine (hs'.add hs'').tsum_le_of_sum_range_le fun n => ?_
    have := hcapB n
    simp only [hsplit] at this
    exact this
  have hle' : ∀ n, ∑ i ∈ Finset.range n, c i * (B' (xs i) (xs i)).re
      ≤ ∑' i, c i * (B' (xs i) (xs i)).re := fun n => hs'.sum_le_tsum _ (fun i _ => h0' i)
  have hle'' : ∀ n, ∑ i ∈ Finset.range n, c i * ((B - B') (xs i) (xs i)).re
      ≤ ∑' i, c i * ((B - B') (xs i) (xs i)).re := fun n => hs''.sum_le_tsum _ (fun i _ => h0'' i)
  have hi' : ∀ i, c i * (B' (xs i) (xs i)).re ≤ ∑' i, c i * (B' (xs i) (xs i)).re :=
    fun i => hs'.le_tsum i (fun j _ => h0' j)
  have hi'' : ∀ i, c i * ((B - B') (xs i) (xs i)).re ≤ ∑' i, c i * ((B - B') (xs i) (xs i)).re :=
    fun i => hs''.le_tsum i (fun j _ => h0'' j)
  have hnn' : 0 ≤ ∑' i, c i * (B' (xs i) (xs i)).re := tsum_nonneg h0'
  have hnn'' : 0 ≤ ∑' i, c i * ((B - B') (xs i) (xs i)).re := tsum_nonneg h0''
  generalize ∑' i, c i * (B' (xs i) (xs i)).re = p' at hP hle' hi' hnn'
  generalize ∑' i, c i * ((B - B') (xs i) (xs i)).re = p'' at hP hle'' hi'' hnn''
  have zero_of : ∀ B₁ : M →ₗ⋆[ℂ] M →ₗ[ℂ] ℂ, InvF ρ B₁ → (∀ i, c i * (B₁ (xs i) (xs i)).re ≤ 0) →
      ∀ x y, B₁ x y = 0 := by
    intro B₁ hB₁ hle x y
    refine eq_zero_of_re B₁ hB₁.1 hB₁.2.1 xs hsp (fun i => ?_) x y
    have h0 := mul_nonneg (hc i).le (hB₁.2.1 (xs i))
    have := le_antisymm (hle i) h0
    exact (mul_eq_zero.mp this).resolve_left (hc i).ne'
  rcases hnn'.lt_or_eq with hp' | hp'
  swap
  · refine ⟨0, fun x y => ?_⟩
    rw [zero_of B' h1 (fun i => (hi' i).trans hp'.ge) x y, zero_mul]
  rcases hnn''.lt_or_eq with hp'' | hp''
  swap
  · refine ⟨1, fun x y => ?_⟩
    have := zero_of (B - B') h2 (fun i => (hi'' i).trans hp''.ge) x y
    rw [LinearMap.sub_apply, LinearMap.sub_apply, sub_eq_zero] at this
    rw [this, one_mul]
  have hPpos : 0 < p' + p'' := by linarith
  have hne' := hp'.ne'
  have hne'' := hp''.ne'
  have hPne := hPpos.ne'
  have hr' : (0 : ℝ) ≤ (p' + p'') / p' := div_nonneg hPpos.le hp'.le
  have hr'' : (0 : ℝ) ≤ (p' + p'') / p'' := div_nonneg hPpos.le hp''.le
  have hF1 : ev ((((p' + p'') / p' : ℝ) : ℂ) • B') ∈ capSet ρ c xs := by
    refine ev_mem ρ c xs (h1.smul hr') fun n => ?_
    show ∑ i ∈ Finset.range n, c i * (((((p' + p'') / p' : ℝ) : ℂ) • B') (xs i) (xs i)).re ≤ 1
    have e : ∑ i ∈ Finset.range n, c i * (((((p' + p'') / p' : ℝ) : ℂ) • B') (xs i) (xs i)).re
        = (p' + p'') / p' * ∑ i ∈ Finset.range n, c i * (B' (xs i) (xs i)).re := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      simp only [LinearMap.smul_apply, smul_eq_mul, Complex.re_ofReal_mul]
      ring
    rw [e]
    calc (p' + p'') / p' * ∑ i ∈ Finset.range n, c i * (B' (xs i) (xs i)).re
        ≤ (p' + p'') / p' * p' := mul_le_mul_of_nonneg_left (hle' n) hr'
      _ = p' + p'' := by field_simp
      _ ≤ 1 := hP
  have hF2 : ev ((((p' + p'') / p'' : ℝ) : ℂ) • (B - B')) ∈ capSet ρ c xs := by
    refine ev_mem ρ c xs (h2.smul hr'') fun n => ?_
    show ∑ i ∈ Finset.range n, c i * (((((p' + p'') / p'' : ℝ) : ℂ) • (B - B')) (xs i) (xs i)).re ≤ 1
    have e : ∑ i ∈ Finset.range n, c i * (((((p' + p'') / p'' : ℝ) : ℂ) • (B - B')) (xs i) (xs i)).re
        = (p' + p'') / p'' * ∑ i ∈ Finset.range n, c i * ((B - B') (xs i) (xs i)).re := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      simp only [LinearMap.smul_apply, smul_eq_mul, Complex.re_ofReal_mul]
      ring
    rw [e]
    calc (p' + p'') / p'' * ∑ i ∈ Finset.range n, c i * ((B - B') (xs i) (xs i)).re
        ≤ (p' + p'') / p'' * p'' := mul_le_mul_of_nonneg_left (hle'' n) hr''
      _ = p' + p'' := by field_simp
      _ ≤ 1 := hP
  have k1r : p' / (p' + p'') * ((p' + p'') / p') = 1 := by field_simp
  have k2r : p'' / (p' + p'') * ((p' + p'') / p'') = 1 := by field_simp
  have k1 : ((p' / (p' + p'') : ℝ) : ℂ) * (((p' + p'') / p' : ℝ) : ℂ) = 1 := by
    rw [← Complex.ofReal_mul, k1r, Complex.ofReal_one]
  have k2 : ((p'' / (p' + p'') : ℝ) : ℂ) * (((p' + p'') / p'' : ℝ) : ℂ) = 1 := by
    rw [← Complex.ofReal_mul, k2r, Complex.ofReal_one]
  have hseg : ev B ∈ openSegment ℝ (ev ((((p' + p'') / p' : ℝ) : ℂ) • B'))
      (ev ((((p' + p'') / p'' : ℝ) : ℂ) • (B - B'))) := by
    refine ⟨p' / (p' + p''), p'' / (p' + p''), div_pos hp' hPpos, div_pos hp'' hPpos, by field_simp, ?_⟩
    funext x y
    rw [comb_apply]
    simp only [ev, LinearMap.smul_apply, LinearMap.sub_apply, smul_eq_mul]
    linear_combination (B' x y) * k1 + (B x y - B' x y) * k2
  have hx := hBx _ hF1 _ hF2 hseg
  refine ⟨((p' / (p' + p'') : ℝ) : ℂ), fun x y => ?_⟩
  have e := congrFun (congrFun hx.1 x) y
  simp only [ev, LinearMap.smul_apply, smul_eq_mul] at e
  rw [← e]
  linear_combination (-(B' x y)) * k1

end cap

/- English proof (translation)
Take `⟨s, hsc, hss⟩` from `hspan`. Take `⟨xs, hxs⟩` from `(hsc.insert 0).exists_eq_range (Set.insert_nonempty 0 s)`. Establish `hsp : Submodule.span ℂ (Set.range xs) = ⊤` using `by rw [← hxs, Submodule.span_insert_zero, hss]`. Take `⟨c, hc_def⟩ : ∃ c : ℕ → ℝ, c = fun i => (1 / 2 : ℝ) ^ i / (1 + (B₀ (xs i) (xs i)).re)` from `⟨_, rfl⟩`. Establish `hc : ∀ i, 0 < c i` using `fun i => by`.

Simplify using `only [hc_def]`. Conclude with `div_pos (by positivity) (by linarith [h₀.2.1 (xs i)])`. Establish `hhalf : InvF ρ (((1 / 2 : ℝ) : ℂ) • B₀)` using `h₀.smul (by norm_num)`. Establish `hmem₀ : ev (((1 / 2 : ℝ) : ℂ) • B₀) ∈ capSet ρ c xs`. Use `ev_mem ρ c xs hhalf fun n => ?_` and prove the remaining obligations.

Use `show ∑ i ∈ Finset.range n, c i * ((((1 / 2 : ℝ) : ℂ) • B₀) (xs i) (xs i)).re ≤ 1`. Establish `hterm : ∀ i, c i * ((((1 / 2 : ℝ) : ℂ) • B₀) (xs i) (xs i)).re ≤ (1 / 2) * (1 / 2 : ℝ) ^ i`. Introduce `i`. Establish `hr` using `h₀.2.1 (xs i)`. Establish `hp : (0 : ℝ) < (1 / 2) ^ i` using `by positivity`.

Simplify using `only [LinearMap.smul_apply, smul_eq_mul, Complex.re_ofReal_mul, hc_def]`. Rewrite using `[div_mul_eq_mul_div, div_le_iff₀ (by linarith)]`. Use the polynomial consequences of the given equalities and inequalities. Combine the equalities or inequalities in the displayed calculation. Choose the witnesses or unpack the hypotheses as in `⟨F, hFe, hFf⟩ : ∃ F ∈ (capSet ρ c xs).extremePoints ℝ, F f f ≠ 0 := by`.

Assume the negation of the conclusion as `hcon`. Simplify using `only [not_exists, not_and, ne_eq, not_not] at hcon`. Establish `hZ : IsClosed {F : M → M → ℂ | F f f = 0}` using `isClosed_eq (continuous_eval f f) continuous_const`. Establish `hZc : Convex ℝ {F : M → M → ℂ | F f f = 0}`. Introduce `F hF G hG a b _ _ _`.

Establish `hF' : F f f = 0` using `hF`. Establish `hG' : G f f = 0` using `hG`. Use `show (a • F + b • G) f f = 0`. Rewrite using `[comb_apply, hF', hG', mul_zero, mul_zero, add_zero]`. Establish `hsub : capSet ρ c xs ⊆ {F | F f f = 0}`.

Rewrite using `[← closure_convexHull_extremePoints (isCompact_capSet ρ c xs hsp hc) (convex_capSet ρ c xs)]`. Conclude with `closure_minimal (convexHull_min (fun F hF => hcon F hF) hZc) hZ`. Establish `h : ((1 / 2 : ℝ) : ℂ) * B₀ f f = 0` using `hsub hmem₀`. Apply `hf` to reduce the goal to its premises. Simplify using `using h`.

Establish `hFm` using `(mem_extremePoints.mp hFe).1`. Conclude with `⟨mkForm F hFm.1.1.1.1, ⟨invF_mkForm ρ c xs hFm, fun B' h1 h2 => ray ρ c xs hsp hc (mkForm F hFm.1.1.1.1) hFe B' h1 h2⟩, hFf⟩`.
-/
theorem extreme_exists_core {G : Type*} [Group G] (ρ : Representation ℂ G M)
    (hspan : ∃ s : Set M, s.Countable ∧ Submodule.span ℂ s = ⊤)
    (B₀ : M →ₗ⋆[ℂ] M →ₗ[ℂ] ℂ) (h₀ : InvF ρ B₀) (f : M) (hf : B₀ f f ≠ 0) :
    ∃ B : M →ₗ⋆[ℂ] M →ₗ[ℂ] ℂ, (InvF ρ B ∧ ∀ B' : M →ₗ⋆[ℂ] M →ₗ[ℂ] ℂ, InvF ρ B' → InvF ρ (B - B') →
      ∃ c : ℂ, ∀ x y, B' x y = c * B x y) ∧ B f f ≠ 0 := by
  obtain ⟨s, hsc, hss⟩ := hspan
  obtain ⟨xs, hxs⟩ := (hsc.insert 0).exists_eq_range (Set.insert_nonempty 0 s)
  have hsp : Submodule.span ℂ (Set.range xs) = ⊤ := by rw [← hxs, Submodule.span_insert_zero, hss]
  obtain ⟨c, hc_def⟩ : ∃ c : ℕ → ℝ, c = fun i => (1 / 2 : ℝ) ^ i / (1 + (B₀ (xs i) (xs i)).re) := ⟨_, rfl⟩
  have hc : ∀ i, 0 < c i := fun i => by
    simp only [hc_def]
    exact div_pos (by positivity) (by linarith [h₀.2.1 (xs i)])
  have hhalf : InvF ρ (((1 / 2 : ℝ) : ℂ) • B₀) := h₀.smul (by norm_num)
  have hmem₀ : ev (((1 / 2 : ℝ) : ℂ) • B₀) ∈ capSet ρ c xs := by
    refine ev_mem ρ c xs hhalf fun n => ?_
    show ∑ i ∈ Finset.range n, c i * ((((1 / 2 : ℝ) : ℂ) • B₀) (xs i) (xs i)).re ≤ 1
    have hterm : ∀ i, c i * ((((1 / 2 : ℝ) : ℂ) • B₀) (xs i) (xs i)).re ≤ (1 / 2) * (1 / 2 : ℝ) ^ i := by
      intro i
      have hr := h₀.2.1 (xs i)
      have hp : (0 : ℝ) < (1 / 2) ^ i := by positivity
      simp only [LinearMap.smul_apply, smul_eq_mul, Complex.re_ofReal_mul, hc_def]
      rw [div_mul_eq_mul_div, div_le_iff₀ (by linarith)]
      nlinarith
    calc ∑ i ∈ Finset.range n, c i * ((((1 / 2 : ℝ) : ℂ) • B₀) (xs i) (xs i)).re
        ≤ ∑ i ∈ Finset.range n, (1 / 2) * (1 / 2 : ℝ) ^ i := Finset.sum_le_sum fun i _ => hterm i
      _ = (1 / 2) * ∑ i ∈ Finset.range n, (1 / 2 : ℝ) ^ i := by rw [Finset.mul_sum]
      _ ≤ 1 := by linarith [sum_geometric_two_le n]
  obtain ⟨F, hFe, hFf⟩ : ∃ F ∈ (capSet ρ c xs).extremePoints ℝ, F f f ≠ 0 := by
    by_contra hcon
    simp only [not_exists, not_and, ne_eq, not_not] at hcon
    have hZ : IsClosed {F : M → M → ℂ | F f f = 0} := isClosed_eq (continuous_eval f f) continuous_const
    have hZc : Convex ℝ {F : M → M → ℂ | F f f = 0} := by
      intro F hF G hG a b _ _ _
      have hF' : F f f = 0 := hF
      have hG' : G f f = 0 := hG
      show (a • F + b • G) f f = 0
      rw [comb_apply, hF', hG', mul_zero, mul_zero, add_zero]
    have hsub : capSet ρ c xs ⊆ {F | F f f = 0} := by
      rw [← closure_convexHull_extremePoints (isCompact_capSet ρ c xs hsp hc) (convex_capSet ρ c xs)]
      exact closure_minimal (convexHull_min (fun F hF => hcon F hF) hZc) hZ
    have h : ((1 / 2 : ℝ) : ℂ) * B₀ f f = 0 := hsub hmem₀
    apply hf
    simpa using h
  have hFm := (mem_extremePoints.mp hFe).1
  exact ⟨mkForm F hFm.1.1.1.1, ⟨invF_mkForm ρ c xs hFm, fun B' h1 h2 => ray ρ c xs hsp hc (mkForm F hFm.1.1.1.1) hFe B' h1 h2⟩, hFf⟩

end DiscreteGroups.sglob.LConvKM

import Mathlib
import Formalism.LocalToGlobal.TorsionIntegrality.QuadraticSemicharacters.CayleyGaussianIntegrals.MatrixFormFourfoldBlock
import Formalism.LocalToGlobal.TorsionIntegrality.QuadraticSemicharacters.CayleyGaussianIntegrals.Th0CharMulOpUTh0HalfPeriodEq
import Formalism.LocalToGlobal.TorsionIntegrality.QuadraticSemicharacters.CayleyGaussianIntegrals.MatrixFormFourfoldBlockFirstBlockEmb

noncomputable section
open scoped BigOperators ComplexConjugate

namespace Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.SC

open Formalism.L2.Th1.H
open Formalism.L2.Th1.F (cmTheta thetaZeroCharacter semiChar herm)

/- English proof (translation)
Use linear arithmetic over natural numbers and integers.
-/
theorem even_im_hermitian_sub (a b c e m k : ℤ) (h1 : ¬(2 ∣ a ∧ 2 ∣ b)) (h2 : ¬(2 ∣ c ∧ 2 ∣ e))
    (h3 : ¬(2 ∣ a + c ∧ 2 ∣ b + e)) :
    (2 ∣ m ∧ 2 ∣ k) ∨ (2 ∣ m - a ∧ 2 ∣ k - b) ∨ (2 ∣ m - c ∧ 2 ∣ k - e) ∨ (2 ∣ m - (a + c) ∧ 2 ∣ k - (b + e)) := by
  omega

/- English proof (translation)
Take `⟨a', rfl⟩` from `ha`. Take `⟨b', rfl⟩` from `hb`. Establish `h1 : L.ω₁ ∈ L.lattice` using `Submodule.subset_span (Set.mem_insert _ _)`. Establish `h2 : L.ω₂ ∈ L.lattice` using `Submodule.subset_span (Set.mem_insert_of_mem _ rfl)`. Establish `e : (((2 * a' : ℤ) : ℂ) * L.ω₁ + ((2 * b' : ℤ) : ℂ) * L.ω₂) / 2 = a' • L.ω₁ + b' • L.ω₂`.

Simplify using `only [zsmul_eq_mul]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e]`. Conclude with `L.lattice.add_mem (L.lattice.smul_mem a' h1) (L.lattice.smul_mem b' h2)`.
-/
theorem half_mem (L : PeriodPair) (a b : ℤ) (ha : 2 ∣ a) (hb : 2 ∣ b) :
    ((a : ℂ) * L.ω₁ + (b : ℂ) * L.ω₂) / 2 ∈ L.lattice := by
  obtain ⟨a', rfl⟩ := ha
  obtain ⟨b', rfl⟩ := hb
  have h1 : L.ω₁ ∈ L.lattice := Submodule.subset_span (Set.mem_insert _ _)
  have h2 : L.ω₂ ∈ L.lattice := Submodule.subset_span (Set.mem_insert_of_mem _ rfl)
  have e : (((2 * a' : ℤ) : ℂ) * L.ω₁ + ((2 * b' : ℤ) : ℂ) * L.ω₂) / 2 = a' • L.ω₁ + b' • L.ω₂ := by
    simp only [zsmul_eq_mul]
    push_cast
    ring
  rw [e]
  exact L.lattice.add_mem (L.lattice.smul_mem a' h1) (L.lattice.smul_mem b' h2)

/- English proof (translation)
Establish `coord : ∀ z ∈ L.lattice, ∃ m n : ℤ, z = (m : ℂ) * L.ω₁ + (n : ℂ) * L.ω₂`. Introduce `z hz`. Take `⟨m, n, h⟩` from `Submodule.mem_span_pair.mp hz`. Conclude with `⟨m, n, by rw [← h]; simp [zsmul_eq_mul]⟩`. Take `⟨a, b, rfl⟩` from `coord x hx`.

Take `⟨c, e, rfl⟩` from `coord y hy`. Take `⟨m, k, rfl⟩` from `coord w hw`. Establish `n1 : ¬(2 ∣ a ∧ 2 ∣ b)` using `fun h => h1 (half_mem L a b h.1 h.2)`. Establish `n2 : ¬(2 ∣ c ∧ 2 ∣ e)` using `fun h => h2 (half_mem L c e h.1 h.2)`. Establish `n3 : ¬(2 ∣ a + c ∧ 2 ∣ b + e)`.

Introduce `h`. Apply `h3` to reduce the goal to its premises. Establish `eq : ((a : ℂ) * L.ω₁ + (b : ℂ) * L.ω₂ + ((c : ℂ) * L.ω₁ + (e : ℂ) * L.ω₂)) / 2 = (((a + c : ℤ) : ℂ) * L.ω₁ + ((b + e : ℤ) : ℂ) * L.ω₂) / 2`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[eq]`. Conclude with `half_mem L _ _ h.1 h.2`. Break down `even_im_hermitian_sub a b c e m k n1 n2 n3 with h | h | h | h` into its components or cases. Use `⟨((m : ℂ) * L.ω₁ + (k : ℂ) * L.ω₂) / 2, half_mem L m k h.1 h.2, Or.inl ?_⟩` and prove the remaining obligations. Expand and normalize the polynomial expressions, which then agree.

Use `⟨(((m - a : ℤ) : ℂ) * L.ω₁ + ((k - b : ℤ) : ℂ) * L.ω₂) / 2, half_mem L _ _ h.1 h.2, Or.inr (Or.inl ?_)⟩` and prove the remaining obligations. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Use `⟨(((m - c : ℤ) : ℂ) * L.ω₁ + ((k - e : ℤ) : ℂ) * L.ω₂) / 2, half_mem L _ _ h.1 h.2, Or.inr (Or.inr (Or.inl ?_))⟩` and prove the remaining obligations. Use `push_cast`.

Expand and normalize the polynomial expressions, which then agree. Use `⟨(((m - (a + c) : ℤ) : ℂ) * L.ω₁ + ((k - (b + e) : ℤ) : ℂ) * L.ω₂) / 2, half_mem L _ _ h.1 h.2, Or.inr (Or.inr (Or.inr ?_))⟩` and prove the remaining obligations. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem gen_mod_two (L : PeriodPair) (x y w : ℂ) (hx : x ∈ L.lattice) (hy : y ∈ L.lattice) (hw : w ∈ L.lattice)
    (h1 : x / 2 ∉ L.lattice) (h2 : y / 2 ∉ L.lattice) (h3 : (x + y) / 2 ∉ L.lattice) :
    ∃ v ∈ L.lattice, w = 2 * v ∨ w = x + 2 * v ∨ w = y + 2 * v ∨ w = x + y + 2 * v := by
  have coord : ∀ z ∈ L.lattice, ∃ m n : ℤ, z = (m : ℂ) * L.ω₁ + (n : ℂ) * L.ω₂ := by
    intro z hz
    obtain ⟨m, n, h⟩ := Submodule.mem_span_pair.mp hz
    exact ⟨m, n, by rw [← h]; simp [zsmul_eq_mul]⟩
  obtain ⟨a, b, rfl⟩ := coord x hx
  obtain ⟨c, e, rfl⟩ := coord y hy
  obtain ⟨m, k, rfl⟩ := coord w hw
  have n1 : ¬(2 ∣ a ∧ 2 ∣ b) := fun h => h1 (half_mem L a b h.1 h.2)
  have n2 : ¬(2 ∣ c ∧ 2 ∣ e) := fun h => h2 (half_mem L c e h.1 h.2)
  have n3 : ¬(2 ∣ a + c ∧ 2 ∣ b + e) := by
    intro h
    apply h3
    have eq : ((a : ℂ) * L.ω₁ + (b : ℂ) * L.ω₂ + ((c : ℂ) * L.ω₁ + (e : ℂ) * L.ω₂)) / 2 =
        (((a + c : ℤ) : ℂ) * L.ω₁ + ((b + e : ℤ) : ℂ) * L.ω₂) / 2 := by
      push_cast
      ring
    rw [eq]
    exact half_mem L _ _ h.1 h.2
  rcases even_im_hermitian_sub a b c e m k n1 n2 n3 with h | h | h | h
  · refine ⟨((m : ℂ) * L.ω₁ + (k : ℂ) * L.ω₂) / 2, half_mem L m k h.1 h.2, Or.inl ?_⟩
    ring
  · refine ⟨(((m - a : ℤ) : ℂ) * L.ω₁ + ((k - b : ℤ) : ℂ) * L.ω₂) / 2, half_mem L _ _ h.1 h.2,
      Or.inr (Or.inl ?_)⟩
    push_cast
    ring
  · refine ⟨(((m - c : ℤ) : ℂ) * L.ω₁ + ((k - e : ℤ) : ℂ) * L.ω₂) / 2, half_mem L _ _ h.1 h.2,
      Or.inr (Or.inr (Or.inl ?_))⟩
    push_cast
    ring
  · refine ⟨(((m - (a + c) : ℤ) : ℂ) * L.ω₁ + ((k - (b + e) : ℤ) : ℂ) * L.ω₂) / 2,
      half_mem L _ _ h.1 h.2, Or.inr (Or.inr (Or.inr ?_))⟩
    push_cast
    ring

section Main

variable (L : PeriodPair) (d : ℕ)

local notation "EE" => Formalism.L2.Th1.F.altE L

def q1 (w : ℂ) : ℝ := Real.sqrt d / 2 * (herm L w w).re

def aa (w : ℂ) : ℂ := Complex.exp ((Real.pi : ℂ) * Complex.I * ((q1 L d w : ℝ) : ℂ))

def io (w : ℂ) : Unit → ℂ := fun _ => w

/- English proof (translation)
Unfold `stdLat`. Use `first`. Consider the case `exact fun _ _ => h`. Consider the case `(rw [← SetLike.mem_coe, AddSubgroup.coe_pi]; exact Set.mem_univ_pi.mpr fun _ => h)`.
-/
theorem io_mem {w : ℂ} (h : w ∈ L.lattice) : io w ∈ stdLat L Unit := by
  unfold stdLat
  first
    | exact fun _ _ => h
    | (rw [← SetLike.mem_coe, AddSubgroup.coe_pi]; exact Set.mem_univ_pi.mpr fun _ => h)

/- English proof (translation)
Unfold `stdH`. Rewrite using `[matH_apply]`. Simplify using `only [Finset.univ_unique, Finset.sum_singleton, Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul, mul_one, io, herm]`. Expand and normalize the polynomial expressions, which then agree.
-/
private theorem stdH_unit_io_io_eq_herm (x y : ℂ) : stdH L Unit (io x) (io y) = herm L x y := by
  unfold stdH
  rw [matH_apply]
  simp only [Finset.univ_unique, Finset.sum_singleton, Matrix.smul_apply, Matrix.one_apply_eq,
    smul_eq_mul, mul_one, io, herm]
  ring

/- English proof (translation)
Unfold `qOf q1`. Rewrite using `[stdH_unit_io_io_eq_herm]`.
-/
theorem cmQuadraticForm_eq_alternatingForm (w : ℂ) : qOf (Real.sqrt d / 2) (stdH L Unit) (io w) = q1 L d w := by
  unfold qOf q1
  rw [stdH_unit_io_io_eq_herm]

/- English proof (translation)
Unfold `alphaQ aa`. Rewrite using `[cmQuadraticForm_eq_alternatingForm]`.
-/
theorem aa_eq (w : ℂ) : alphaQ (Real.sqrt d / 2) (stdH L Unit) (io w) = aa L d w := by
  unfold alphaQ aa
  rw [cmQuadraticForm_eq_alternatingForm]

/- English proof (translation)
Unfold `Formalism.L2.Th1.H.altE Formalism.L2.Th1.F.altE`. Rewrite using `[stdH_unit_io_io_eq_herm]`.
-/
theorem altE_io (x y : ℂ) : altE (stdH L Unit) (io x) (io y) = EE x y := by
  unfold Formalism.L2.Th1.H.altE Formalism.L2.Th1.F.altE
  rw [stdH_unit_io_io_eq_herm]

/- English proof (translation)
Take `⟨m, n, h⟩` from `Submodule.mem_span_pair.mp hz`. Conclude with `⟨m, n, by rw [← h]; simp [zsmul_eq_mul]⟩`.
-/
private theorem coord_lemma (z : ℂ) (hz : z ∈ L.lattice) :
    ∃ m n : ℤ, z = (m : ℂ) * L.ω₁ + (n : ℂ) * L.ω₂ := by
  obtain ⟨m, n, h⟩ := Submodule.mem_span_pair.mp hz
  exact ⟨m, n, by rw [← h]; simp [zsmul_eq_mul]⟩

/- English proof (translation)
Simplify using `only [herm]`. Rewrite using `[Complex.mul_conj, Complex.ofReal_div]`.
-/
theorem herm_self (w : ℂ) : herm L w w = ((Complex.normSq w / Formalism.L2.Th1.F.area L : ℝ) : ℂ) := by
  simp only [herm]
  rw [Complex.mul_conj, Complex.ofReal_div]

/- English proof (translation)
Take `⟨t, ht⟩ : ∃ t : ℝ, t = (L.ω₁ * conj L.ω₂).im` from `⟨_, rfl⟩`. Establish `hA : Formalism.L2.Th1.F.area L = |t|`. Unfold `Formalism.L2.Th1.F.area`. Rewrite using `[ht, show (conj L.ω₁ * L.ω₂).im = -(L.ω₁ * conj L.ω₂).im by`. Simplify using `only [Complex.mul_im, Complex.conj_re, Complex.conj_im]`.

Use the proof step `ring, abs_neg]`. Establish `hpos : 0 < |t|` using `hA ▸ Formalism.L2.Th1.F.areaPos L`. Establish `hIm : ∀ a b c e : ℤ, (((a : ℂ) * L.ω₁ + (b : ℂ) * L.ω₂) * conj ((c : ℂ) * L.ω₁ + (e : ℂ) * L.ω₂)).im = ((a : ℝ) * e - b * c) * t`. Introduce `a b c e`. Rewrite using `[ht]`.

Simplify using `only [Complex.mul_im, Complex.mul_re, Complex.add_re, Complex.add_im, Complex.conj_re, Complex.conj_im, Complex.intCast_re, Complex.intCast_im]`. Expand and normalize the polynomial expressions, which then agree. Establish `key : ∀ a b c e : ℤ, EE ((a : ℂ) * L.ω₁ + (b : ℂ) * L.ω₂) ((c : ℂ) * L.ω₁ + (e : ℂ) * L.ω₂) = ((a : ℝ) * e - b * c) * t / |t|`. Introduce `a b c e`. Simplify using `only [Formalism.L2.Th1.F.altE, herm]`.

Rewrite using `[Complex.div_ofReal_im, hIm, hA]`. Break down `lt_or_gt_of_ne (abs_pos.mp hpos) with hneg | hp` into its components or cases. Use `⟨-1, Or.inr rfl, fun a b c e => ?_⟩` and prove the remaining obligations. Rewrite using `[key, abs_of_neg hneg, mul_div_assoc, div_neg, div_self hneg.ne]`. Use `push_cast`.

Expand and normalize the polynomial expressions, which then agree. Use `⟨1, Or.inl rfl, fun a b c e => ?_⟩` and prove the remaining obligations. Rewrite using `[key, abs_of_pos hp, mul_div_assoc, div_self hp.ne']`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
private theorem exists_sign_EE_lattice_eq_det : ∃ s : ℤ, (s = 1 ∨ s = -1) ∧ ∀ a b c e : ℤ,
    EE ((a : ℂ) * L.ω₁ + (b : ℂ) * L.ω₂) ((c : ℂ) * L.ω₁ + (e : ℂ) * L.ω₂) =
      ((s * (a * e - b * c) : ℤ) : ℝ) := by
  obtain ⟨t, ht⟩ : ∃ t : ℝ, t = (L.ω₁ * conj L.ω₂).im := ⟨_, rfl⟩
  have hA : Formalism.L2.Th1.F.area L = |t| := by
    unfold Formalism.L2.Th1.F.area
    rw [ht, show (conj L.ω₁ * L.ω₂).im = -(L.ω₁ * conj L.ω₂).im by
      simp only [Complex.mul_im, Complex.conj_re, Complex.conj_im]; ring, abs_neg]
  have hpos : 0 < |t| := hA ▸ Formalism.L2.Th1.F.areaPos L
  have hIm : ∀ a b c e : ℤ, (((a : ℂ) * L.ω₁ + (b : ℂ) * L.ω₂) *
      conj ((c : ℂ) * L.ω₁ + (e : ℂ) * L.ω₂)).im = ((a : ℝ) * e - b * c) * t := by
    intro a b c e
    rw [ht]
    simp only [Complex.mul_im, Complex.mul_re, Complex.add_re, Complex.add_im, Complex.conj_re,
      Complex.conj_im, Complex.intCast_re, Complex.intCast_im]
    ring
  have key : ∀ a b c e : ℤ, EE ((a : ℂ) * L.ω₁ + (b : ℂ) * L.ω₂) ((c : ℂ) * L.ω₁ + (e : ℂ) * L.ω₂) =
      ((a : ℝ) * e - b * c) * t / |t| := by
    intro a b c e
    simp only [Formalism.L2.Th1.F.altE, herm]
    rw [Complex.div_ofReal_im, hIm, hA]
  rcases lt_or_gt_of_ne (abs_pos.mp hpos) with hneg | hp
  · refine ⟨-1, Or.inr rfl, fun a b c e => ?_⟩
    rw [key, abs_of_neg hneg, mul_div_assoc, div_neg, div_self hneg.ne]
    push_cast
    ring
  · refine ⟨1, Or.inl rfl, fun a b c e => ?_⟩
    rw [key, abs_of_pos hp, mul_div_assoc, div_self hp.ne']
    push_cast
    ring

/- English proof (translation)
Simplify using `only [Formalism.L2.Th1.F.altE, herm, map_add, mul_add, add_div, Complex.add_im]`.
-/
theorem altE_add_right (x y z : ℂ) : EE x (y + z) = EE x y + EE x z := by
  simp only [Formalism.L2.Th1.F.altE, herm, map_add, mul_add, add_div, Complex.add_im]

/- English proof (translation)
Take `⟨s, -, hs⟩` from `exists_sign_EE_lattice_eq_det L`. Take `⟨a, b, rfl⟩` from `coord_lemma L x hx`. Take `⟨c, e, rfl⟩` from `coord_lemma L y hy`. Conclude with `⟨_, hs a b c e⟩`.
-/
private theorem exists_int_EE_eq_of_mem_lattice (x : ℂ) (hx : x ∈ L.lattice) (y : ℂ) (hy : y ∈ L.lattice) :
    ∃ m : ℤ, EE x y = m := by
  obtain ⟨s, -, hs⟩ := exists_sign_EE_lattice_eq_det L
  obtain ⟨a, b, rfl⟩ := coord_lemma L x hx
  obtain ⟨c, e, rfl⟩ := coord_lemma L y hy
  exact ⟨_, hs a b c e⟩

/- English proof (translation)
Establish `h : herm L x (2 * v) = ((2 : ℝ) : ℂ) * herm L x v`. Simplify using `only [herm, map_mul, map_ofNat]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Simplify using `only [Formalism.L2.Th1.F.altE]`.

Rewrite using `[h, Complex.im_ofReal_mul]`.
-/
theorem altE_two_right (x v : ℂ) : EE x (2 * v) = 2 * EE x v := by
  have h : herm L x (2 * v) = ((2 : ℝ) : ℂ) * herm L x v := by
    simp only [herm, map_mul, map_ofNat]
    push_cast
    ring
  simp only [Formalism.L2.Th1.F.altE]
  rw [h, Complex.im_ofReal_mul]

/- English proof (translation)
Establish `h : (Real.pi : ℂ) * Complex.I * (((m : ℝ)) : ℂ) = (m : ℂ) * ((Real.pi : ℂ) * Complex.I)`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[h, Complex.exp_int_mul, Complex.exp_pi_mul_I]`.
-/
private theorem exp_pi_I_intCast_eq_neg_one_pow (m : ℤ) :
    Complex.exp ((Real.pi : ℂ) * Complex.I * (((m : ℝ)) : ℂ)) = (-1 : ℂ) ^ m := by
  have h : (Real.pi : ℂ) * Complex.I * (((m : ℝ)) : ℂ) = (m : ℂ) * ((Real.pi : ℂ) * Complex.I) := by
    push_cast
    ring
  rw [h, Complex.exp_int_mul, Complex.exp_pi_mul_I]

/- English proof (translation)
Establish `h : herm L (x / 2) y = ((1 / 2 : ℝ) : ℂ) * herm L x y`. Simplify using `only [herm]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Simplify using `only [Formalism.L2.Th1.F.altE]`.

Rewrite using `[h, Complex.im_ofReal_mul]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem altE_half_left (x y : ℂ) : EE (x / 2) y = EE x y / 2 := by
  have h : herm L (x / 2) y = ((1 / 2 : ℝ) : ℂ) * herm L x y := by
    simp only [herm]
    push_cast
    ring
  simp only [Formalism.L2.Th1.F.altE]
  rw [h, Complex.im_ofReal_mul]
  ring

/- English proof (translation)
Simplify using `only [cmTheta]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
private theorem cmTheta_one_eq :
    cmTheta 1 d = ((1 / 2 : ℝ) : ℂ) + ((Real.sqrt d / 2 : ℝ) : ℂ) * Complex.I := by
  simp only [cmTheta]
  push_cast
  ring

/- English proof (translation)
Rewrite using `[cmTheta_one_eq]`. Simplify using the standard rewrite rules.
-/
theorem theta_re : (cmTheta 1 d).re = 1 / 2 := by
  rw [cmTheta_one_eq]
  simp
/- English proof (translation)
Rewrite using `[cmTheta_one_eq]`. Simplify using the standard rewrite rules.
-/
theorem theta_im : (cmTheta 1 d).im = Real.sqrt d / 2 := by
  rw [cmTheta_one_eq]
  simp

/- English proof (translation)
Rewrite using `[Complex.normSq_apply, theta_re, theta_im]`. Establish `h` using `Real.mul_self_sqrt (Nat.cast_nonneg (α := ℝ) d)`. Take the linear combination `h / 4`.
-/
theorem theta_normSq : Complex.normSq (cmTheta 1 d) = (1 + (d : ℝ)) / 4 := by
  rw [Complex.normSq_apply, theta_re, theta_im]
  have h := Real.mul_self_sqrt (Nat.cast_nonneg (α := ℝ) d)
  linear_combination h / 4

/- English proof (translation)
Establish `h1 : herm L (cmTheta 1 d * w) w = cmTheta 1 d * herm L w w`. Simplify using `only [herm]`. Expand and normalize the polynomial expressions, which then agree. Simplify using `only [Formalism.L2.Th1.F.altE, q1]`. Rewrite using `[h1, herm_self, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, theta_im]`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem altE_theta (w : ℂ) : EE (cmTheta 1 d * w) w = q1 L d w := by
  have h1 : herm L (cmTheta 1 d * w) w = cmTheta 1 d * herm L w w := by
    simp only [herm]
    ring
  simp only [Formalism.L2.Th1.F.altE, q1]
  rw [h1, herm_self, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, theta_im]
  ring

/- English proof (translation)
Simplify using `only [q1, Formalism.L2.Th1.F.altE, herm, cmTheta_one_eq, map_add]`. Simplify using `only [Complex.div_ofReal_re, Complex.div_ofReal_im, Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.conj_re, Complex.conj_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im]`. Expand and normalize the polynomial expressions, which then agree.
-/
private theorem q1_add (x y : ℂ) :
    q1 L d (x + y) = q1 L d x + q1 L d y + 2 * EE (cmTheta 1 d * x) y - EE x y := by
  simp only [q1, Formalism.L2.Th1.F.altE, herm, cmTheta_one_eq, map_add]
  simp only [Complex.div_ofReal_re, Complex.div_ofReal_im, Complex.add_re, Complex.add_im,
    Complex.mul_re, Complex.mul_im, Complex.conj_re, Complex.conj_im, Complex.ofReal_re,
    Complex.ofReal_im, Complex.I_re, Complex.I_im]
  ring

/- English proof (translation)
Establish `h1 : herm L (cmTheta 1 d * w) (cmTheta 1 d * w) = ((Complex.normSq (cmTheta 1 d) : ℝ) : ℂ) * herm L w w`. Simplify using `only [herm, map_mul]`. Rewrite using `[← Complex.mul_conj]`. Expand and normalize the polynomial expressions, which then agree. Simplify using `only [q1]`.

Rewrite using `[h1, Complex.re_ofReal_mul, theta_normSq]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem quadratic_form_theta_scaling (w : ℂ) : q1 L d (cmTheta 1 d * w) = (1 + (d : ℝ)) / 4 * q1 L d w := by
  have h1 : herm L (cmTheta 1 d * w) (cmTheta 1 d * w) =
      ((Complex.normSq (cmTheta 1 d) : ℝ) : ℂ) * herm L w w := by
    simp only [herm, map_mul]
    rw [← Complex.mul_conj]
    ring
  simp only [q1]
  rw [h1, Complex.re_ofReal_mul, theta_normSq]
  ring

variable {L d}
variable (hst : ∀ x ∈ L.lattice, cmTheta 1 d * x ∈ L.lattice)
include hst

/- English proof (translation)
Establish `hint : ∀ x ∈ L.lattice, ∃ m : ℤ, q1 L d x = (m : ℝ)`. Introduce `x hx`. Take `⟨m, hm⟩` from `exists_int_EE_eq_of_mem_lattice L _ (hst x hx) x hx`. Conclude with `⟨m, (altE_theta L d x).symm.trans hm⟩`. Use `⟨hint, fun x hx => ?_, fun x hx y hy => ?_⟩` and prove the remaining obligations.

Take `⟨m, hm⟩` from `hint x hx`. Unfold `aa`. Rewrite using `[hm, exp_pi_I_intCast_eq_neg_one_pow]`. Break down `Int.even_or_odd m with he | ho` into its components or cases. Conclude with `Or.inl he.neg_one_zpow`.

Conclude with `Or.inr ho.neg_one_zpow`. Take `⟨m1, hm1⟩` from `exists_int_EE_eq_of_mem_lattice L _ (hst x hx) y hy`. Take `⟨m2, hm2⟩` from `exists_int_EE_eq_of_mem_lattice L x hx y hy`. Unfold `aa`. Rewrite using `[q1_add, hm1, hm2, ← Complex.exp_add, ← Complex.exp_add, Complex.exp_eq_exp_iff_exists_int]`.

Conclude with `⟨m1 - m2, by push_cast; ring⟩`.
-/
theorem semi :
    (∀ x ∈ L.lattice, ∃ m : ℤ, q1 L d x = (m : ℝ)) ∧ (∀ x ∈ L.lattice, aa L d x = 1 ∨ aa L d x = -1) ∧
    ∀ x ∈ L.lattice, ∀ y ∈ L.lattice, aa L d (x + y) = aa L d x * aa L d y *
      Complex.exp ((Real.pi : ℂ) * Complex.I * (EE x y : ℂ)) := by
  have hint : ∀ x ∈ L.lattice, ∃ m : ℤ, q1 L d x = (m : ℝ) := by
    intro x hx
    obtain ⟨m, hm⟩ := exists_int_EE_eq_of_mem_lattice L _ (hst x hx) x hx
    exact ⟨m, (altE_theta L d x).symm.trans hm⟩
  refine ⟨hint, fun x hx => ?_, fun x hx y hy => ?_⟩
  · obtain ⟨m, hm⟩ := hint x hx
    unfold aa
    rw [hm, exp_pi_I_intCast_eq_neg_one_pow]
    rcases Int.even_or_odd m with he | ho
    · exact Or.inl he.neg_one_zpow
    · exact Or.inr ho.neg_one_zpow
  · obtain ⟨m1, hm1⟩ := exists_int_EE_eq_of_mem_lattice L _ (hst x hx) y hy
    obtain ⟨m2, hm2⟩ := exists_int_EE_eq_of_mem_lattice L x hx y hy
    unfold aa
    rw [q1_add, hm1, hm2, ← Complex.exp_add, ← Complex.exp_add,
      Complex.exp_eq_exp_iff_exists_int]
    exact ⟨m1 - m2, by push_cast; ring⟩

variable {ω₀ : ℂ} (h0 : ω₀ ∈ L.lattice) (hθ : cmTheta 1 d * (ω₀ / 2) ∉ L.lattice)
  (hθ' : (1 - cmTheta 1 d) * (ω₀ / 2) ∉ L.lattice)
include h0 hθ hθ'

/- English proof (translation)
Conclude with `fun h => hθ (hst _ h)`.
-/
theorem half_notMem : ω₀ / 2 ∉ L.lattice := by
  exact fun h => hθ (hst _ h)

/- English proof (translation)
Use `⟨half_notMem hst h0 hθ hθ', ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[mul_div_assoc]`. Conclude with `hθ`. Introduce `h`. Apply `hθ'` to reduce the goal to its premises.

Establish `e : (1 - cmTheta 1 d) * (ω₀ / 2) = ω₀ - (ω₀ + cmTheta 1 d * ω₀) / 2` using `by ring`. Rewrite using `[e]`. Conclude with `L.lattice.sub_mem h0 h`.
-/
private theorem half_periods_not_mem_cm_lattice : ω₀ / 2 ∉ L.lattice ∧ cmTheta 1 d * ω₀ / 2 ∉ L.lattice ∧
    (ω₀ + cmTheta 1 d * ω₀) / 2 ∉ L.lattice := by
  refine ⟨half_notMem hst h0 hθ hθ', ?_, ?_⟩
  · rw [mul_div_assoc]
    exact hθ
  · intro h
    apply hθ'
    have e : (1 - cmTheta 1 d) * (ω₀ / 2) = ω₀ - (ω₀ + cmTheta 1 d * ω₀) / 2 := by ring
    rw [e]
    exact L.lattice.sub_mem h0 h

/- English proof (translation)
Take `⟨n1, n2, n3⟩` from `half_periods_not_mem_cm_lattice hst h0 hθ hθ'`. Conclude with `gen_mod_two L ω₀ (cmTheta 1 d * ω₀) w h0 (hst _ h0) hw n1 n2 n3`.
-/
theorem gen (w : ℂ) (hw : w ∈ L.lattice) :
    ∃ v ∈ L.lattice, w = 2 * v ∨ w = ω₀ + 2 * v ∨ w = cmTheta 1 d * ω₀ + 2 * v ∨
      w = ω₀ + cmTheta 1 d * ω₀ + 2 * v := by
  obtain ⟨n1, n2, n3⟩ := half_periods_not_mem_cm_lattice hst h0 hθ hθ'
  exact gen_mod_two L ω₀ (cmTheta 1 d * ω₀) w h0 (hst _ h0) hw n1 n2 n3

/- English proof (translation)
Take `⟨n1, n2, n3⟩` from `half_periods_not_mem_cm_lattice hst h0 hθ hθ'`. Take `⟨a, b, hab⟩` from `coord_lemma L ω₀ h0`. Take `⟨c, e, hce⟩` from `coord_lemma L _ (hst _ h0)`. Establish `p1 : ¬(2 ∣ a ∧ 2 ∣ b)` using `fun h => n1 (by rw [hab]; exact half_mem L a b h.1 h.2)`. Establish `p2 : ¬(2 ∣ c ∧ 2 ∣ e)` using `fun h => n2 (by rw [hce]; exact half_mem L c e h.1 h.2)`.

Establish `p3 : ¬(2 ∣ a + c ∧ 2 ∣ b + e)`. Introduce `h`. Apply `n3` to reduce the goal to its premises. Establish `eq : ω₀ + cmTheta 1 d * ω₀ = (((a + c : ℤ)) : ℂ) * L.ω₁ + ((b + e : ℤ) : ℂ) * L.ω₂`. Rewrite using `[hce]`.

Rewrite using `[hab]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[eq]`. Conclude with `half_mem L _ _ h.1 h.2`.

Take `⟨s, hs, hE⟩` from `exists_sign_EE_lattice_eq_det L`. Establish `hq : q1 L d ω₀ = ((s * (c * b - e * a) : ℤ) : ℝ)`. Rewrite using `[← altE_theta, hce]`. Rewrite using `[hab]`. Conclude with `hE c e a b`.

Establish `hodd : Odd (c * b - e * a)`. Rewrite using `[Int.odd_iff, Int.sub_emod, Int.mul_emod c, Int.mul_emod e]`. Apply the tactic sequence `rcases Int.emod_two_eq_zero_or_one a with ha | ha <;>`. Apply the tactic sequence `rcases Int.emod_two_eq_zero_or_one b with hb | hb <;>`. Apply the tactic sequence `rcases Int.emod_two_eq_zero_or_one c with hc | hc <;>`.

Apply the tactic sequence `rcases Int.emod_two_eq_zero_or_one e with he | he <;>`. Apply the tactic sequence `simp only [ha, hb, hc, he] <;> omega`. Use `⟨s * (c * b - e * a), ?_, hq⟩` and prove the remaining obligations. Break down `hs with rfl | rfl` into its components or cases. Simplify using `using hodd`.

Establish `h2 : Odd (e * a - c * b)`. Rewrite using `[← neg_sub]`. Conclude with `hodd.neg`. Simplify using `using h2`.
-/
theorem q_odd : ∃ Q : ℤ, Odd Q ∧ q1 L d ω₀ = (Q : ℝ) := by
  obtain ⟨n1, n2, n3⟩ := half_periods_not_mem_cm_lattice hst h0 hθ hθ'
  obtain ⟨a, b, hab⟩ := coord_lemma L ω₀ h0
  obtain ⟨c, e, hce⟩ := coord_lemma L _ (hst _ h0)
  have p1 : ¬(2 ∣ a ∧ 2 ∣ b) := fun h => n1 (by rw [hab]; exact half_mem L a b h.1 h.2)
  have p2 : ¬(2 ∣ c ∧ 2 ∣ e) := fun h => n2 (by rw [hce]; exact half_mem L c e h.1 h.2)
  have p3 : ¬(2 ∣ a + c ∧ 2 ∣ b + e) := by
    intro h
    apply n3
    have eq : ω₀ + cmTheta 1 d * ω₀ = (((a + c : ℤ)) : ℂ) * L.ω₁ + ((b + e : ℤ) : ℂ) * L.ω₂ := by
      rw [hce]
      rw [hab]
      push_cast
      ring
    rw [eq]
    exact half_mem L _ _ h.1 h.2
  obtain ⟨s, hs, hE⟩ := exists_sign_EE_lattice_eq_det L
  have hq : q1 L d ω₀ = ((s * (c * b - e * a) : ℤ) : ℝ) := by
    rw [← altE_theta, hce]
    rw [hab]
    exact hE c e a b
  have hodd : Odd (c * b - e * a) := by
    rw [Int.odd_iff, Int.sub_emod, Int.mul_emod c, Int.mul_emod e]
    rcases Int.emod_two_eq_zero_or_one a with ha | ha <;>
    rcases Int.emod_two_eq_zero_or_one b with hb | hb <;>
    rcases Int.emod_two_eq_zero_or_one c with hc | hc <;>
    rcases Int.emod_two_eq_zero_or_one e with he | he <;>
    simp only [ha, hb, hc, he] <;> omega
  refine ⟨s * (c * b - e * a), ?_, hq⟩
  rcases hs with rfl | rfl
  · simpa using hodd
  · have h2 : Odd (e * a - c * b) := by
      rw [← neg_sub]
      exact hodd.neg
    simpa using h2

/- English proof (translation)
Take `⟨hq, hpm, hadd⟩` from `semi hst`. Take `⟨Q, hodd, hQ⟩` from `q_odd hst h0 hθ hθ'`. Establish `hu : cmTheta 1 d * ω₀ ∈ L.lattice` using `hst _ h0`. Establish `radd : ∀ x ∈ L.lattice, ∀ y ∈ L.lattice, aa L d (x + y) * thetaZeroCharacter L ω₀ (x + y) = (aa L d x * thetaZeroCharacter L ω₀ x) * (aa L d y * thetaZeroCharacter L ω₀ y)`. Introduce `x hx y hy`.

Rewrite using `[hadd x hx y hy, th0Char_add L ω₀ x y hx hy]`. Take `⟨k, hk⟩` from `Formalism.L2.Th1.F.altEInt L x y hx hy`. Rewrite using `[hk, exp_pi_int]`. Apply the tactic sequence `rcases neg_one_zpow_pm k with h | h <;> rw [h] <;> ring`. Establish `rsq : ∀ x ∈ L.lattice, (aa L d x * thetaZeroCharacter L ω₀ x) * (aa L d x * thetaZeroCharacter L ω₀ x) = 1`.

Introduce `x hx`. Establish `h1` using `th0Char_sq L ω₀ x h0 hx`. Apply the tactic sequence `have h2 : aa L d x * aa L d x = 1 := by rcases hpm x hx with h | h <;> rw [h] <;> norm_num`. Combine the equalities or inequalities in the displayed calculation. Establish `rtwo : ∀ v ∈ L.lattice, aa L d (2 * v) * thetaZeroCharacter L ω₀ (2 * v) = 1`.

Introduce `v hv`. Rewrite using `[two_mul, radd v hv v hv, rsq v hv]`. Establish `r0 : aa L d ω₀ * thetaZeroCharacter L ω₀ ω₀ = 1`. Rewrite using `[aa, hQ, exp_pi_int, hodd.neg_one_zpow, thetaZeroCharacter, semiChar, if_neg (half_notMem hst h0 hθ hθ'), cayleyGaussianIntegrals_self_fact]`. Simplify using the standard rewrite rules.

Establish `ru : aa L d (cmTheta 1 d * ω₀) * thetaZeroCharacter L ω₀ (cmTheta 1 d * ω₀) = 1`. Establish `hne : cmTheta 1 d * ω₀ / 2 ∉ L.lattice` using `by rwa [mul_div_assoc]`. Take `⟨k', hk'⟩ : ∃ k' : ℤ, (d : ℤ) = 8 * k' + 7` from `⟨(d : ℤ) / 8, by omega⟩`. Establish `hq2 : q1 L d (cmTheta 1 d * ω₀) = (((2 * (k' + 1) * Q : ℤ)) : ℝ)`. Rewrite using `[quadratic_form_theta_scaling, hQ]`.

Establish `hd' : (d : ℝ) = 8 * (k' : ℝ) + 7` using `by exact_mod_cast hk'`. Rewrite using `[hd']`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[aa, hq2, exp_pi_int, thetaZeroCharacter, semiChar, if_neg hne, altE_theta, hQ, exp_pi_int, hodd.neg_one_zpow, Even.neg_one_zpow ⟨(k' + 1) * Q, by ring⟩]`.

Evaluate the numerical expressions. Establish `rall : aa L d w * thetaZeroCharacter L ω₀ w = 1`. Take `⟨v, hv, hc⟩` from `gen hst h0 hθ hθ' w hw`. Establish `h2v : 2 * v ∈ L.lattice` using `by rw [two_mul]; exact add_mem hv hv`. Break down `hc with rfl | rfl | rfl | rfl` into its components or cases.

Conclude with `rtwo v hv`. Rewrite using `[radd _ h0 _ h2v, r0, rtwo v hv, one_mul]`. Rewrite using `[radd _ hu _ h2v, ru, rtwo v hv, one_mul]`. Rewrite using `[radd _ (add_mem h0 hu) _ h2v, radd _ h0 _ hu, r0, ru, rtwo v hv]`. Evaluate the numerical expressions.

Combine the equalities or inequalities in the displayed calculation.
-/
theorem char_eq (hd : d % 8 = 7) (w : ℂ) (hw : w ∈ L.lattice) : aa L d w = thetaZeroCharacter L ω₀ w := by
  obtain ⟨hq, hpm, hadd⟩ := semi hst
  obtain ⟨Q, hodd, hQ⟩ := q_odd hst h0 hθ hθ'
  have hu : cmTheta 1 d * ω₀ ∈ L.lattice := hst _ h0
  have radd : ∀ x ∈ L.lattice, ∀ y ∈ L.lattice,
      aa L d (x + y) * thetaZeroCharacter L ω₀ (x + y) = (aa L d x * thetaZeroCharacter L ω₀ x) * (aa L d y * thetaZeroCharacter L ω₀ y) := by
    intro x hx y hy
    rw [hadd x hx y hy, th0Char_add L ω₀ x y hx hy]
    obtain ⟨k, hk⟩ := Formalism.L2.Th1.F.altEInt L x y hx hy
    rw [hk, exp_pi_int]
    rcases neg_one_zpow_pm k with h | h <;> rw [h] <;> ring
  have rsq : ∀ x ∈ L.lattice, (aa L d x * thetaZeroCharacter L ω₀ x) * (aa L d x * thetaZeroCharacter L ω₀ x) = 1 := by
    intro x hx
    have h1 := th0Char_sq L ω₀ x h0 hx
    have h2 : aa L d x * aa L d x = 1 := by rcases hpm x hx with h | h <;> rw [h] <;> norm_num
    calc _ = (aa L d x * aa L d x) * (thetaZeroCharacter L ω₀ x * thetaZeroCharacter L ω₀ x) := by ring
      _ = 1 := by rw [h1, h2, one_mul]
  have rtwo : ∀ v ∈ L.lattice, aa L d (2 * v) * thetaZeroCharacter L ω₀ (2 * v) = 1 := by
    intro v hv; rw [two_mul, radd v hv v hv, rsq v hv]
  have r0 : aa L d ω₀ * thetaZeroCharacter L ω₀ ω₀ = 1 := by
    rw [aa, hQ, exp_pi_int, hodd.neg_one_zpow, thetaZeroCharacter, semiChar, if_neg (half_notMem hst h0 hθ hθ'), cayleyGaussianIntegrals_self_fact]
    simp
  have ru : aa L d (cmTheta 1 d * ω₀) * thetaZeroCharacter L ω₀ (cmTheta 1 d * ω₀) = 1 := by
    have hne : cmTheta 1 d * ω₀ / 2 ∉ L.lattice := by rwa [mul_div_assoc]
    obtain ⟨k', hk'⟩ : ∃ k' : ℤ, (d : ℤ) = 8 * k' + 7 := ⟨(d : ℤ) / 8, by omega⟩
    have hq2 : q1 L d (cmTheta 1 d * ω₀) = (((2 * (k' + 1) * Q : ℤ)) : ℝ) := by
      rw [quadratic_form_theta_scaling, hQ]
      have hd' : (d : ℝ) = 8 * (k' : ℝ) + 7 := by exact_mod_cast hk'
      rw [hd']; push_cast; ring
    rw [aa, hq2, exp_pi_int, thetaZeroCharacter, semiChar, if_neg hne, altE_theta, hQ, exp_pi_int, hodd.neg_one_zpow,
      Even.neg_one_zpow ⟨(k' + 1) * Q, by ring⟩]
    norm_num
  have rall : aa L d w * thetaZeroCharacter L ω₀ w = 1 := by
    obtain ⟨v, hv, hc⟩ := gen hst h0 hθ hθ' w hw
    have h2v : 2 * v ∈ L.lattice := by rw [two_mul]; exact add_mem hv hv
    rcases hc with rfl | rfl | rfl | rfl
    · exact rtwo v hv
    · rw [radd _ h0 _ h2v, r0, rtwo v hv, one_mul]
    · rw [radd _ hu _ h2v, ru, rtwo v hv, one_mul]
    · rw [radd _ (add_mem h0 hu) _ h2v, radd _ h0 _ hu, r0, ru, rtwo v hv]; norm_num
  calc aa L d w = aa L d w * (thetaZeroCharacter L ω₀ w * thetaZeroCharacter L ω₀ w) := by rw [th0Char_sq L ω₀ w h0 hw, mul_one]
    _ = (aa L d w * thetaZeroCharacter L ω₀ w) * thetaZeroCharacter L ω₀ w := by ring
    _ = thetaZeroCharacter L ω₀ w := by rw [rall, one_mul]

/- English proof (translation)
Rewrite `hx` using `[mem_stdLat]`. Rewrite using `[alphaQ, qOf, stdH_apply, Complex.re_sum, Finset.mul_sum, Complex.ofReal_sum, Finset.mul_sum, Complex.exp_sum, stdChar]`. Conclude with `Finset.prod_congr rfl fun i _ => char_eq hst h0 hθ hθ' hd (x i) (hx i)`.
-/
theorem stdChar_eq (hd : d % 8 = 7) (n : Type) [Fintype n] [DecidableEq n] (x : n → ℂ) (hx : x ∈ stdLat L n) :
    alphaQ (Real.sqrt d / 2) (stdH L n) x = stdChar L ω₀ x := by
  rw [mem_stdLat] at hx
  rw [alphaQ, qOf, stdH_apply, Complex.re_sum, Finset.mul_sum, Complex.ofReal_sum, Finset.mul_sum,
    Complex.exp_sum, stdChar]
  exact Finset.prod_congr rfl fun i _ => char_eq hst h0 hθ hθ' hd (x i) (hx i)

end Main

end Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.SC

end

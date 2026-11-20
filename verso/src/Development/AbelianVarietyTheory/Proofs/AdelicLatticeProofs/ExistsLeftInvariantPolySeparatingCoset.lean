import Mathlib
import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.AdelicPair
open Matrix GlobalTheory.ClassFin
open scoped Kronecker ComplexOrder TensorProduct

namespace GlobalTheory.ClassFin.CosetSep

variable {ι : Type} [Fintype ι] [DecidableEq ι]

def vanC (S : Set (Matrix ι ι ℂ)) : Ideal (MvPolynomial (ι × ι) ℂ) where
  carrier := {f | ∀ g ∈ S, evC f g = 0}
  add_mem' := by
    intro a b ha hb g hg
    have h1 := ha g hg
    have h2 := hb g hg
    simp only [evC] at h1 h2 ⊢
    rw [map_add, h1, h2, add_zero]
  zero_mem' := by
    intro g _
    simp [evC]
  smul_mem' := by
    intro c a ha g hg
    have h1 := ha g hg
    simp only [evC] at h1 ⊢
    rw [smul_eq_mul, map_mul, h1, mul_zero]

omit [Fintype ι] [DecidableEq ι] in
/- English proof (translation)
Unfold both sides. The equivalence is reflexive.
-/
lemma mem_vanC {S : Set (Matrix ι ι ℂ)} {f : MvPolynomial (ι × ι) ℂ} :
    f ∈ vanC S ↔ ∀ g ∈ S, evC f g = 0 := Iff.rfl

omit [DecidableEq ι] in
/- English proof (translation)
Proceed by induction on `f using MvPolynomial.induction_on with`. Consider the case `C a => simp [evC, ltr]`. Consider the case `add p q hp hq`. Simplify using `only [evC] at hp hq ⊢`. Rewrite using `[map_add, map_add, map_add, hp, hq]`.

Consider the case `mul_X p ij hp`. Simplify using `only [evC] at hp ⊢`. Rewrite using `[map_mul, map_mul, map_mul, hp]`. Use `congr 1`. Simplify using `[ltr, Matrix.mul_apply]`.
-/
lemma evC_ltr (g y : Matrix ι ι ℂ) (f : MvPolynomial (ι × ι) ℂ) : evC (ltr g f) y = evC f (g * y) := by
  induction f using MvPolynomial.induction_on with
  | C a => simp [evC, ltr]
  | add p q hp hq =>
    simp only [evC] at hp hq ⊢
    rw [map_add, map_add, map_add, hp, hq]
  | mul_X p ij hp =>
    simp only [evC] at hp ⊢
    rw [map_mul, map_mul, map_mul, hp]
    congr 1
    simp [ltr, Matrix.mul_apply]

omit [DecidableEq ι] in
/- English proof (translation)
Proceed by induction on `f using MvPolynomial.induction_on with`. Consider the case `C a => exact ⟨MvPolynomial.C a, fun z => by simp [evC]⟩`. Consider the case `add p q hp hq`. Take `⟨p', hp⟩` from `hp`. Take `⟨q', hq⟩` from `hq`.

Use `⟨p' + q', fun z => ?_⟩` and prove the remaining obligations. Establish `h1` using `hp z`. Establish `h2` using `hq z`. Simplify using `only [evC] at h1 h2 ⊢`. Rewrite using `[map_add, map_add, h1, h2]`.

Consider the case `mul_X p ij hp`. Take `⟨p', hp⟩` from `hp`. Use `⟨p' * ∑ k, MvPolynomial.X (ij.1, k) * MvPolynomial.C (h k ij.2), fun z => ?_⟩` and prove the remaining obligations. Establish `h1` using `hp z`. Simplify using `only [evC] at h1 ⊢`.

Rewrite using `[map_mul, map_mul, h1]`. Use `congr 1`. Simplify using `[Matrix.mul_apply]`.
-/
lemma exists_rtr (h : Matrix ι ι ℂ) (f : MvPolynomial (ι × ι) ℂ) :
    ∃ f' : MvPolynomial (ι × ι) ℂ, ∀ z, evC f' z = evC f (z * h) := by
  induction f using MvPolynomial.induction_on with
  | C a => exact ⟨MvPolynomial.C a, fun z => by simp [evC]⟩
  | add p q hp hq =>
    obtain ⟨p', hp⟩ := hp
    obtain ⟨q', hq⟩ := hq
    refine ⟨p' + q', fun z => ?_⟩
    have h1 := hp z
    have h2 := hq z
    simp only [evC] at h1 h2 ⊢
    rw [map_add, map_add, h1, h2]
  | mul_X p ij hp =>
    obtain ⟨p', hp⟩ := hp
    refine ⟨p' * ∑ k, MvPolynomial.X (ij.1, k) * MvPolynomial.C (h k ij.2), fun z => ?_⟩
    have h1 := hp z
    simp only [evC] at h1 ⊢
    rw [map_mul, map_mul, h1]
    congr 1
    simp [Matrix.mul_apply]

omit [Fintype ι] [DecidableEq ι] in
/- English proof (translation)
Simplify using `only [evC, ev]`. Rewrite using `[MvPolynomial.eval_map, MvPolynomial.aeval_def]`.
-/
lemma evC_map (f : MvPolynomial (ι × ι) ℚ) (g : Matrix ι ι ℂ) :
    evC (MvPolynomial.map (algebraMap ℚ ℂ) f) g = ev f g := by
  simp only [evC, ev]
  rw [MvPolynomial.eval_map, MvPolynomial.aeval_def]

/- English proof (translation)
Apply `hΓ.closed` to reduce the goal to its premises. Introduce `f hf`. Rewrite using `[← evC_map]`. Apply `hz` to reduce the goal to its premises. Introduce `g hg`.

Rewrite using `[evC_map]`. Conclude with `hf g hg`.
-/
lemma mem_of_forall_vanC {Γ : Set (Matrix ι ι ℂ)} (hΓ : IsQGroup Γ) {z : Matrix ι ι ℂ}
    (hz : ∀ f ∈ vanC Γ, evC f z = 0) : z ∈ Γ := by
  apply hΓ.closed
  intro f hf
  rw [← evC_map]
  apply hz
  intro g hg
  rw [evC_map]
  exact hf g hg

/- English proof (translation)
Assume the negation of the conclusion as `hne`. Take `⟨M, hM, hle⟩` from `Ideal.exists_le_maximal _ hne`. Take `⟨x, rfl⟩` from `(MvPolynomial.isMaximal_iff_eq_vanishingIdeal_singleton).1 hM`. Use `set z : Matrix ι ι ℂ := Matrix.of fun i j => x (i, j) with hz`. Establish `key : ∀ f ∈ vanC Γ ⊔ vanC ((fun g => g * y) '' Γ), evC f z = 0`.

Introduce `f hf`. Establish `h1` using `(MvPolynomial.mem_vanishingIdeal_singleton_iff x f).1 (hle hf)`. Simplify `h1` using `[evC, hz]`. Establish `hzΓ : z ∈ Γ` using `mem_of_forall_vanC hΓ fun f hf => key f (Ideal.mem_sup_left hf)`. Establish `hyy : y * y.adjugate = 1` using `by rw [Matrix.mul_adjugate, hy, one_smul]`.

Establish `hyy' : y.adjugate * y = 1` using `by rw [Matrix.adjugate_mul, hy, one_smul]`. Establish `hwΓ : z * y.adjugate ∈ Γ`. Use `mem_of_forall_vanC hΓ fun f hf => ?_` and prove the remaining obligations. Take `⟨f', hf'⟩` from `exists_rtr y.adjugate f`. Rewrite using `[← hf']`.

Use `key f' (Ideal.mem_sup_right ?_)` and prove the remaining obligations. Introduce and unpack `_ ⟨g, hg, rfl⟩`. Rewrite using `[hf', mul_assoc, hyy, mul_one]`. Conclude with `hf g hg`. Apply `hyΓ` to reduce the goal to its premises.

Establish `h1 : (z * y.adjugate).adjugate * (z * y.adjugate) = 1`. Rewrite using `[Matrix.adjugate_mul, hΓ.det_eq _ hwΓ, one_smul]`. Establish `h2 : y = (z * y.adjugate).adjugate * z`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[h2]`.

Conclude with `hΓ.mul_mem _ (hΓ.adj_mem _ hwΓ) _ hzΓ`.
-/
lemma vanC_sup_eq_top {Γ : Set (Matrix ι ι ℂ)} (hΓ : IsQGroup Γ) {y : Matrix ι ι ℂ} (hy : y.det = 1)
    (hyΓ : y ∉ Γ) : vanC Γ ⊔ vanC ((fun g => g * y) '' Γ) = ⊤ := by
  by_contra hne
  obtain ⟨M, hM, hle⟩ := Ideal.exists_le_maximal _ hne
  obtain ⟨x, rfl⟩ := (MvPolynomial.isMaximal_iff_eq_vanishingIdeal_singleton).1 hM
  set z : Matrix ι ι ℂ := Matrix.of fun i j => x (i, j) with hz
  have key : ∀ f ∈ vanC Γ ⊔ vanC ((fun g => g * y) '' Γ), evC f z = 0 := by
    intro f hf
    have h1 := (MvPolynomial.mem_vanishingIdeal_singleton_iff x f).1 (hle hf)
    simpa [evC, hz] using h1
  have hzΓ : z ∈ Γ := mem_of_forall_vanC hΓ fun f hf => key f (Ideal.mem_sup_left hf)
  have hyy : y * y.adjugate = 1 := by rw [Matrix.mul_adjugate, hy, one_smul]
  have hyy' : y.adjugate * y = 1 := by rw [Matrix.adjugate_mul, hy, one_smul]
  have hwΓ : z * y.adjugate ∈ Γ := by
    refine mem_of_forall_vanC hΓ fun f hf => ?_
    obtain ⟨f', hf'⟩ := exists_rtr y.adjugate f
    rw [← hf']
    refine key f' (Ideal.mem_sup_right ?_)
    rintro _ ⟨g, hg, rfl⟩
    rw [hf', mul_assoc, hyy, mul_one]
    exact hf g hg
  apply hyΓ
  have h1 : (z * y.adjugate).adjugate * (z * y.adjugate) = 1 := by
    rw [Matrix.adjugate_mul, hΓ.det_eq _ hwΓ, one_smul]
  have h2 : y = (z * y.adjugate).adjugate * z := by
    calc y = (z * y.adjugate).adjugate * (z * y.adjugate) * y := by rw [h1, one_mul]
      _ = (z * y.adjugate).adjugate * (z * (y.adjugate * y)) := by simp only [mul_assoc]
      _ = _ := by rw [hyy', mul_one]
  rw [h2]
  exact hΓ.mul_mem _ (hΓ.adj_mem _ hwΓ) _ hzΓ

end GlobalTheory.ClassFin.CosetSep

namespace GlobalTheory.ClassFin

open CosetSep in

/- English proof (translation)
Introduce `ι _ _ Γ Rey hΓ hR y hy hyΓ`. Establish `htop` using `vanC_sup_eq_top hΓ hy hyΓ`. Establish `h1 : (1 : MvPolynomial (ι × ι) ℂ) ∈ vanC Γ ⊔ vanC ((fun g => g * y) '' Γ)`. Rewrite using `[htop]`. Discharge the goal by the elementary cases of `trivial`.

Take `⟨a, ha, b, hb, hab⟩` from `Submodule.mem_sup.1 h1`. Establish `hRa : Rey a ∈ vanC Γ`. Use `hR.stable ((vanC Γ).restrictScalars ℂ) ?_ a ha` and prove the remaining obligations. Introduce `g hg f hf h hh`. Rewrite using `[evC_ltr]`.

Conclude with `hf _ (hΓ.mul_mem _ hg _ hh)`. Establish `hRb : Rey b ∈ vanC ((fun g => g * y) '' Γ)`. Use `hR.stable ((vanC ((fun g => g * y) '' Γ)).restrictScalars ℂ) ?_ b hb` and prove the remaining obligations. Introduce and unpack `g hg f hf _ ⟨h, hh, rfl⟩`. Rewrite using `[evC_ltr, ← mul_assoc]`.

Conclude with `hf _ ⟨g * h, hΓ.mul_mem _ hg _ hh, rfl⟩`. Establish `hR1 : Rey 1 = 1` using `hR.fix 1 (fun g _ z => by simp [evC])`. Establish `hsum : Rey a + Rey b = 1` using `by rw [← map_add, hab, hR1]`. Use `⟨Rey a, hR.inv a, ?_⟩` and prove the remaining obligations. Establish `e1 : evC (Rey a) 1 = 0` using `hRa 1 hΓ.one_mem`.

Establish `e2 : evC (Rey b) y = 0` using `hRb y ⟨1, hΓ.one_mem, one_mul y⟩`. Establish `e3 : evC (Rey a) y = 1`. Establish `h` using `congrArg (fun f => evC f y) hsum`. Simplify using `only [evC] at h e2 ⊢`. Rewrite `h` using `[map_add, e2, add_zero, map_one]`.

Conclude with `h`. Rewrite using `[e1, e3]`. Conclude with `zero_ne_one`.
-/
theorem exists_isInv_evC_one_ne : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (Γ : Set (Matrix ι ι ℂ)) (Rey : MvPolynomial (ι × ι) ℂ →ₗ[ℂ] MvPolynomial (ι × ι) ℂ), IsQGroup Γ → IsReynolds Γ Rey → ∀ y : Matrix ι ι ℂ, y.det = 1 → y ∉ Γ → ∃ f, IsInv Γ f ∧ evC f 1 ≠ evC f y := by
  intro ι _ _ Γ Rey hΓ hR y hy hyΓ
  have htop := vanC_sup_eq_top hΓ hy hyΓ
  have h1 : (1 : MvPolynomial (ι × ι) ℂ) ∈ vanC Γ ⊔ vanC ((fun g => g * y) '' Γ) := by
    rw [htop]; trivial
  obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.1 h1
  have hRa : Rey a ∈ vanC Γ := by
    refine hR.stable ((vanC Γ).restrictScalars ℂ) ?_ a ha
    intro g hg f hf h hh
    rw [evC_ltr]
    exact hf _ (hΓ.mul_mem _ hg _ hh)
  have hRb : Rey b ∈ vanC ((fun g => g * y) '' Γ) := by
    refine hR.stable ((vanC ((fun g => g * y) '' Γ)).restrictScalars ℂ) ?_ b hb
    rintro g hg f hf _ ⟨h, hh, rfl⟩
    rw [evC_ltr, ← mul_assoc]
    exact hf _ ⟨g * h, hΓ.mul_mem _ hg _ hh, rfl⟩
  have hR1 : Rey 1 = 1 := hR.fix 1 (fun g _ z => by simp [evC])
  have hsum : Rey a + Rey b = 1 := by rw [← map_add, hab, hR1]
  refine ⟨Rey a, hR.inv a, ?_⟩
  have e1 : evC (Rey a) 1 = 0 := hRa 1 hΓ.one_mem
  have e2 : evC (Rey b) y = 0 := hRb y ⟨1, hΓ.one_mem, one_mul y⟩
  have e3 : evC (Rey a) y = 1 := by
    have h := congrArg (fun f => evC f y) hsum
    simp only [evC] at h e2 ⊢
    rw [map_add, e2, add_zero, map_one] at h
    exact h
  rw [e1, e3]
  exact zero_ne_one

end GlobalTheory.ClassFin

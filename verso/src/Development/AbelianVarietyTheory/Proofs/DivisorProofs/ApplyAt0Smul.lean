import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.FinitePrimesUnder
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.VacuumUnderAdelicPairModulusOne
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ThetaSpanRationalTranslatesVacuum

noncomputable section

open Formalism.BasicNotions Formalism.IndefR.Links IsDedekindDomain NumberField Polynomial
open scoped Pointwise nonZeroDivisors
open Formalism.L2.Host (HChar embTau)
open GlobalTheory.ChiGrid GlobalTheory.LeafRestExamples
open Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.FunObj GlobalTheory.FunObj.SqNum

namespace GlobalTheory.FunObj.NormUniq

variable {D : D7}

/- English proof (translation)
Use function extensionality and compare the values at `z`. Simplify using `only [Wd, U, Pi.smul_apply, smul_eq_mul]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem wd_smul (T : Tor D) {N N' : ℕ} (x : VC D N N') (c : ℂ) (G : VC D N N' → ℂ) :
    Wd D T x (c • G) = c • Wd D T x G := by
  funext z
  simp only [Wd, U, Pi.smul_apply, smul_eq_mul]
  ring

/- English proof (translation)
Use function extensionality and compare the values at `z`. Simplify using `only [Wd, U, Pi.add_apply]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem wd_add (T : Tor D) {N N' : ℕ} (x : VC D N N') (G G' : VC D N N' → ℂ) :
    Wd D T x (G + G') = Wd D T x G + Wd D T x G' := by
  funext z
  simp only [Wd, U, Pi.add_apply]
  ring

/- English proof (translation)
Simplify using `only [GL3Theta.applyAt0, Finset.mul_sum]`. Use `Finset.sum_congr rfl fun α _ => ?_` and prove the remaining obligations. Establish `: TaylorLogMetric.taylor D (c • G) α = c * TaylorLogMetric.taylor D G α`. Unfold `TaylorLogMetric.taylor`. Set `g : ℂ ≃L[ℂ] ℂ` to `ContinuousLinearEquiv.smulLeft (R₁ := ℂ) (M₁ := ℂ) (G := ℂˣ) (Units.mk0 c hc)`.

Establish `e : c • G = ⇑g ∘ G`. Use function extensionality and compare the values at `z`. Simplify using `[g, ContinuousLinearEquiv.smulLeft, Units.smul_def]`. Rewrite using `[e, ContinuousLinearEquiv.iteratedFDeriv_comp_left]`. Simplify using `[g, ContinuousLinearEquiv.smulLeft, Units.smul_def]`.

Expand and normalize the polynomial expressions, which then agree. Rewrite using `[this]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem applyAt0_smul {N N' : ℕ} (P : MvPolynomial (GL3Theta.Idx D N N') ℂ) {c : ℂ} (hc : c ≠ 0)
    (G : VC D N N' → ℂ) : GL3Theta.applyAt0 D P (c • G) = c * GL3Theta.applyAt0 D P G := by
  simp only [GL3Theta.applyAt0, Finset.mul_sum]
  refine Finset.sum_congr rfl fun α _ => ?_
  have : TaylorLogMetric.taylor D (c • G) α = c * TaylorLogMetric.taylor D G α := by
    unfold TaylorLogMetric.taylor
    let g : ℂ ≃L[ℂ] ℂ := ContinuousLinearEquiv.smulLeft (R₁ := ℂ) (M₁ := ℂ) (G := ℂˣ) (Units.mk0 c hc)
    have e : c • G = ⇑g ∘ G := by
      funext z; simp [g, ContinuousLinearEquiv.smulLeft, Units.smul_def]
    rw [e, ContinuousLinearEquiv.iteratedFDeriv_comp_left]
    simp [g, ContinuousLinearEquiv.smulLeft, Units.smul_def]
    ring
  rw [this]; ring

/- English proof (translation)
Assemble the required witnesses or components as `⟨differentiable_const 0, 1, one_pos, fun x _ => by funext z; simp [Wd, U]⟩`.
-/
theorem tt_zero (T : Tor D) {N N' : ℕ} : (0 : VC D N N' → ℂ) ∈ TT D T N N' :=
  ⟨differentiable_const 0, 1, one_pos, fun x _ => by funext z; simp [Wd, U]⟩

/- English proof (translation)
Take `⟨h1, m, hm, h2⟩` from `hF`. Take `⟨h1', m', hm', h2'⟩` from `hF'`. Use `⟨h1.add h1', m * m', Nat.mul_pos hm hm', fun x hx => ?_⟩` and prove the remaining obligations. Establish `e1` using `h2 (m' • x) (AddSubgroup.nsmul_mem _ hx _)`. Establish `e2` using `h2' (m • x) (AddSubgroup.nsmul_mem _ hx _)`.

Rewrite `e1`, `e2` using `[smul_smul]`. Rewrite `e2` using `[mul_comm m' m]`. Rewrite using `[wd_add, e1, e2]`.
-/
theorem tt_add {T : Tor D} {N N' : ℕ} {F F' : VC D N N' → ℂ} (hF : F ∈ TT D T N N') (hF' : F' ∈ TT D T N N') :
    F + F' ∈ TT D T N N' := by
  obtain ⟨h1, m, hm, h2⟩ := hF
  obtain ⟨h1', m', hm', h2'⟩ := hF'
  refine ⟨h1.add h1', m * m', Nat.mul_pos hm hm', fun x hx => ?_⟩
  have e1 := h2 (m' • x) (AddSubgroup.nsmul_mem _ hx _)
  have e2 := h2' (m • x) (AddSubgroup.nsmul_mem _ hx _)
  rw [smul_smul] at e1 e2
  rw [mul_comm m' m] at e2
  rw [wd_add, e1, e2]

/- English proof (translation)
Take `⟨h1, m, hm, h2⟩` from `hF`. Conclude with `⟨h1.const_smul c, m, hm, fun x hx => by rw [wd_smul, h2 x hx]⟩`.
-/
theorem tt_smul {T : Tor D} {N N' : ℕ} {F : VC D N N' → ℂ} (hF : F ∈ TT D T N N') (c : ℂ) :
    c • F ∈ TT D T N N' := by
  obtain ⟨h1, m, hm, h2⟩ := hF
  exact ⟨h1.const_smul c, m, hm, fun x hx => by rw [wd_smul, h2 x hx]⟩

/- English proof (translation)
Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty => simpa using tt_zero T`. Consider the case `insert a s ha ih`. Rewrite using `[Finset.sum_insert ha]`. Conclude with `tt_add (hF a (Finset.mem_insert_self a s)) (ih fun i hi => hF i (Finset.mem_insert_of_mem hi))`.
-/
theorem tt_sum {T : Tor D} {N N' : ℕ} {ι : Type*} (s : Finset ι) {F : ι → VC D N N' → ℂ}
    (hF : ∀ i ∈ s, F i ∈ TT D T N N') : ∑ i ∈ s, F i ∈ TT D T N N' := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using tt_zero T
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact tt_add (hF a (Finset.mem_insert_self a s)) (ih fun i hi => hF i (Finset.mem_insert_of_mem hi))

end GlobalTheory.FunObj.NormUniq

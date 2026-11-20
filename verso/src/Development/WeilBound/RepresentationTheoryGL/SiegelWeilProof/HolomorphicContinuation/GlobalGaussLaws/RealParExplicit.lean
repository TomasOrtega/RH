import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.ConvRight
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsRealParOfIsCharAF
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ArchimedeanParametersAddCharUnique

noncomputable section

open scoped Matrix NNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace PositivityTheory.Rg.Sw.Glob

set_option synthInstance.maxHeartbeats 400000 in

/- English proof (translation)
Take `⟨ψ₀, h₀, a, ha0, ha⟩` from `GlobalTheory.ThetaAllChar.exists_std hψ`. Use `set y : D.host.E := algebraMap D.host.F D.host.E a with hy_def`. Establish `hyc : IsCMField.complexConj D.host.E y = y` using `(IsCMField.complexConj_eq_self_iff D.host.E y).2 a.2`. Establish `hreal : ∀ τ, (tauE D τ y).im = 0`. Introduce `τ`.

Establish `h` using `IsCMField.complexEmbedding_complexConj D.host.E (tauE D τ) y`. Rewrite `h` using `[hyc]`. Use `congrArg Complex.im h` as an intermediate fact. Rewrite `this` using `[Complex.conj_im]`. Combine the linear equalities and inequalities to obtain the conclusion.

Use `⟨a, ha0, ?_, hreal⟩` and prove the remaining obligations. Introduce `x`. Establish `e1 : psiInf D.host.F ψ x = psiInf D.host.F ψ₀ (algebraMap D.host.F (Ainf D.host.F) a * x)`. Simplify using `only [psiInf]`. Rewrite using `[ha]`.

Use `congr 1`. Use `show (algebraMap D.host.F (Ainf D.host.F) a * x, algebraMap D.host.F (Af D.host.F) a * 0) = _`. Rewrite using `[mul_zero]`. Both sides reduce to the same expression. Rewrite using `[e1, h₀.2.2 θ hθ]`.

Use `congr 1`. Establish `e2 : ∀ ρ, θ ρ ((algebraMap D.host.F (Ainf D.host.F) a * x) ⊗ₜ[D.host.F] (1 : D.host.E)) = θ ρ (x ⊗ₜ[D.host.F] (1 : D.host.E)) * tauE D ρ y`. Introduce `ρ`. Establish `e3 : (algebraMap D.host.F (Ainf D.host.F) a * x) ⊗ₜ[D.host.F] (1 : D.host.E) = (x ⊗ₜ[D.host.F] (1 : D.host.E)) * ((1 : Ainf D.host.F) ⊗ₜ[D.host.F] y)`. Rewrite using `[Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul, ← Algebra.smul_def, ← TensorProduct.smul_tmul', ← TensorProduct.tmul_smul, Algebra.smul_def, mul_one]`.

Rewrite using `[e3, map_mul, (hθ ρ).1]`. Simplify using `only [e2]`. Establish `e5 : ∀ ρ, (((tauE D ρ (algebraMap D.host.F D.host.E a)).re : ℝ) : ℂ) = tauE D ρ y`. Introduce `ρ`. Establish `h` using `hreal ρ`.

Rewrite `h`, the goal using `[hy_def]`. Apply `Complex.ext` to reduce the goal to its premises. Simplify using the standard rewrite rules. Simplify using `[h]`. Simplify using `only [Finset.mul_sum]`.

Use `push_cast`. Use `Finset.sum_congr rfl fun ρ _ => ?_` and prove the remaining obligations. Rewrite using `[e5 ρ]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem realPar_explicit (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (hψ : IsCharAF D.host.F ψ) (θ : InfFam D)
    (hθ : IsInfFam θ) : ∃ a : D.host.F, a ≠ 0 ∧
      HasRealPar ψ θ (fun τ => -(tauE D τ (algebraMap D.host.F D.host.E a)).re) ∧
      ∀ τ, (tauE D τ (algebraMap D.host.F D.host.E a)).im = 0 := by
  obtain ⟨ψ₀, h₀, a, ha0, ha⟩ := GlobalTheory.ThetaAllChar.exists_std hψ
  set y : D.host.E := algebraMap D.host.F D.host.E a with hy_def
  have hyc : IsCMField.complexConj D.host.E y = y :=
    (IsCMField.complexConj_eq_self_iff D.host.E y).2 a.2
  have hreal : ∀ τ, (tauE D τ y).im = 0 := by
    intro τ
    have h := IsCMField.complexEmbedding_complexConj D.host.E (tauE D τ) y
    rw [hyc] at h
    have := congrArg Complex.im h
    rw [Complex.conj_im] at this
    linarith
  refine ⟨a, ha0, ?_, hreal⟩
  intro x
  have e1 : psiInf D.host.F ψ x = psiInf D.host.F ψ₀ (algebraMap D.host.F (Ainf D.host.F) a * x) := by
    simp only [psiInf]
    rw [ha]
    congr 1
    show (algebraMap D.host.F (Ainf D.host.F) a * x, algebraMap D.host.F (Af D.host.F) a * 0) = _
    rw [mul_zero]; rfl
  rw [e1, h₀.2.2 θ hθ]
  congr 1
  have e2 : ∀ ρ, θ ρ ((algebraMap D.host.F (Ainf D.host.F) a * x) ⊗ₜ[D.host.F] (1 : D.host.E)) =
      θ ρ (x ⊗ₜ[D.host.F] (1 : D.host.E)) * tauE D ρ y := by
    intro ρ
    have e3 : (algebraMap D.host.F (Ainf D.host.F) a * x) ⊗ₜ[D.host.F] (1 : D.host.E) =
        (x ⊗ₜ[D.host.F] (1 : D.host.E)) * ((1 : Ainf D.host.F) ⊗ₜ[D.host.F] y) := by
      rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul, ← Algebra.smul_def, ← TensorProduct.smul_tmul',
        ← TensorProduct.tmul_smul, Algebra.smul_def, mul_one]
    rw [e3, map_mul, (hθ ρ).1]
  simp only [e2]
  have e5 : ∀ ρ, (((tauE D ρ (algebraMap D.host.F D.host.E a)).re : ℝ) : ℂ) = tauE D ρ y := by
    intro ρ
    have h := hreal ρ
    rw [hy_def] at h ⊢
    apply Complex.ext
    · simp
    · simp [h]
  simp only [Finset.mul_sum]
  push_cast
  refine Finset.sum_congr rfl fun ρ _ => ?_
  rw [e5 ρ]
  ring

/- English proof (translation)
Introduce `D ψ θ l hψ hθ hl τ`. Take `⟨a, ha0, hl0, hre⟩` from `realPar_explicit D ψ hψ θ hθ`. Establish `e : l = _` using `GlobalTheory.StdUnn.RealPar.realPar_unique D ψ θ hθ l _ hl hl0`. Rewrite using `[e]`. Introduce `h0`.

Apply `ha0` to reduce the goal to its premises. Establish `h1 : tauE D τ (algebraMap D.host.F D.host.E a) = 0`. Apply `Complex.ext` to reduce the goal to its premises. Simplify using `using h0`. Simplify using `using hre τ`.

Establish `h2 : algebraMap D.host.F D.host.E a = 0` using `(map_eq_zero _).1 h1`. Conclude with `(map_eq_zero_iff _ (algebraMap D.host.F D.host.E).injective).1 h2`.
-/
theorem lNZ : LNZ := by
  intro D ψ θ l hψ hθ hl τ
  obtain ⟨a, ha0, hl0, hre⟩ := realPar_explicit D ψ hψ θ hθ
  have e : l = _ := GlobalTheory.StdUnn.RealPar.realPar_unique D ψ θ hθ l _ hl hl0
  rw [e]
  intro h0
  apply ha0
  have h1 : tauE D τ (algebraMap D.host.F D.host.E a) = 0 := by
    apply Complex.ext
    · simpa using h0
    · simpa using hre τ
  have h2 : algebraMap D.host.F D.host.E a = 0 := (map_eq_zero _).1 h1
  exact (map_eq_zero_iff _ (algebraMap D.host.F D.host.E).injective).1 h2

end PositivityTheory.Rg.Sw.Glob

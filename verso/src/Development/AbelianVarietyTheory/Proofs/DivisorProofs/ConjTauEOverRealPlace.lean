import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsNotRelZero
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.UnitaryConjugation
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SquareTriple
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SquareStanding

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open Classical
open scoped TensorProduct ComplexConjugate GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ alpha beta Num skewGram blk conjU)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model HasExp SplitsFully Chars)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

noncomputable section

namespace GlobalTheory.ConjTypeOverReal

/- English proof (translation)
Take `⟨g, rfl⟩` from `(factEmb D.R D.host).1.2 ψ`. Use `⟨D.eTau.symm ⟨g, ((factEmb D.R D.host).2 g).1 h⟩, ?_⟩` and prove the remaining obligations. Simplify using `[tauE]`.
-/
theorem exists_tau_of_val {D : D7} (ψ : D.host.E →+* ℂ)
    (h : ψ D.host.sqrtMinusD = Complex.I * (Real.sqrt D.host.d : ℂ)) :
    ∃ τ : D.what₂.Tau, tauE D τ = ψ := by
  obtain ⟨g, rfl⟩ := (factEmb D.R D.host).1.2 ψ
  refine ⟨D.eTau.symm ⟨g, ((factEmb D.R D.host).2 g).1 h⟩, ?_⟩
  simp [tauE]

/- English proof (translation)
Establish `h0 : (Complex.I * (Real.sqrt D.host.d : ℂ)) ^ 2 = -(D.host.d : ℂ)`. Rewrite using `[mul_pow, Complex.I_sq, ← Complex.ofReal_pow, Real.sq_sqrt (Nat.cast_nonneg _)]`. Simplify using the standard rewrite rules. Establish `h3 : D.host.φ₀ D.host.sqrtMinusD = Complex.I * (Real.sqrt D.host.d : ℂ)` using `D.host.φ₀_mem`. Apply `D.host.φ₀.injective` to reduce the goal to its premises.

Rewrite using `[map_pow, h3, h0]`. Simplify using the standard rewrite rules.
-/
theorem sqrt_sq' {D : D7} : D.host.sqrtMinusD ^ 2 = -(D.host.d : D.host.E) := by
  have h0 : (Complex.I * (Real.sqrt D.host.d : ℂ)) ^ 2 = -(D.host.d : ℂ) := by
    rw [mul_pow, Complex.I_sq, ← Complex.ofReal_pow, Real.sq_sqrt (Nat.cast_nonneg _)]
    simp
  have h3 : D.host.φ₀ D.host.sqrtMinusD = Complex.I * (Real.sqrt D.host.d : ℂ) := D.host.φ₀_mem
  apply D.host.φ₀.injective
  rw [map_pow, h3, h0]
  simp

/- English proof (translation)
Use `letI : Algebra D.host.F ℂ := w.embedding.toAlgebra`. Use `haveI : Algebra.IsAlgebraic D.host.F D.host.E := inferInstance`. Use `haveI : Module.IsTorsionFree D.host.F ℂ := by set_option synthInstance.maxHeartbeats 400000 in infer_instance`. Set `ψ : D.host.E →ₐ[D.host.F] ℂ` to `IsAlgClosed.lift`. Establish `hψ : (ψ : D.host.E →+* ℂ).comp (algebraMap D.host.F D.host.E) = w.embedding`.

Use extensionality with `x`. Simplify using `only [RingHom.comp_apply, RingHom.coe_coe, AlgHom.commutes]`. Both sides reduce to the same expression. Establish `hreal : (starRingEnd ℂ).comp w.embedding = w.embedding`. Establish `hw : w.IsReal` using `IsTotallyReal.isReal w`.

Use `(InfinitePlace.isReal_iff.1 hw)` as an intermediate fact. Conclude with `this`. Establish `h0 : (Complex.I * (Real.sqrt D.host.d : ℂ)) ^ 2 = -(D.host.d : ℂ)`. Rewrite using `[mul_pow, Complex.I_sq, ← Complex.ofReal_pow, Real.sq_sqrt (Nat.cast_nonneg _)]`. Simplify using the standard rewrite rules.

Establish `h1 : (ψ : D.host.E →+* ℂ) D.host.sqrtMinusD ^ 2 = (Complex.I * (Real.sqrt D.host.d : ℂ)) ^ 2`. Rewrite using `[← map_pow, sqrt_sq', h0]`. Simplify using the standard rewrite rules. Break down `sq_eq_sq_iff_eq_or_eq_neg.1 h1 with h2 | h2` into its components or cases. Take `⟨τ, hτ⟩` from `exists_tau_of_val (ψ : D.host.E →+* ℂ) h2`.

Use `⟨τ, ?_⟩` and prove the remaining obligations. Rewrite using `[hτ, RingHom.comp_assoc, hψ, hreal]`. Take `⟨τ, hτ⟩` from `exists_tau_of_val ((starRingEnd ℂ).comp (ψ : D.host.E →+* ℂ)) (by rw [RingHom.comp_apply, h2]; simp)`. Use `⟨τ, ?_⟩` and prove the remaining obligations. Rewrite using `[hτ, ← RingHom.comp_assoc]`.

Establish `hcc : (starRingEnd ℂ).comp (starRingEnd ℂ) = RingHom.id ℂ`. Use extensionality with `z`. Simplify using the standard rewrite rules. Rewrite using `[hcc, RingHom.id_comp, hψ]`.
-/
theorem exists_conj_tauE_over (D : D7) (w : InfinitePlace D.host.F) : ∃ τ : D.what₂.Tau,
    ((starRingEnd ℂ).comp (tauE D τ)).comp (algebraMap D.host.F D.host.E) = w.embedding := by
  letI : Algebra D.host.F ℂ := w.embedding.toAlgebra
  haveI : Algebra.IsAlgebraic D.host.F D.host.E := inferInstance
  haveI : Module.IsTorsionFree D.host.F ℂ := by
    set_option synthInstance.maxHeartbeats 400000 in infer_instance
  let ψ : D.host.E →ₐ[D.host.F] ℂ := IsAlgClosed.lift
  have hψ : (ψ : D.host.E →+* ℂ).comp (algebraMap D.host.F D.host.E) = w.embedding := by
    ext x
    simp only [RingHom.comp_apply, RingHom.coe_coe, AlgHom.commutes]
    rfl
  have hreal : (starRingEnd ℂ).comp w.embedding = w.embedding := by
    have hw : w.IsReal := IsTotallyReal.isReal w
    have := (InfinitePlace.isReal_iff.1 hw)
    exact this
  have h0 : (Complex.I * (Real.sqrt D.host.d : ℂ)) ^ 2 = -(D.host.d : ℂ) := by
    rw [mul_pow, Complex.I_sq, ← Complex.ofReal_pow, Real.sq_sqrt (Nat.cast_nonneg _)]
    simp
  have h1 : (ψ : D.host.E →+* ℂ) D.host.sqrtMinusD ^ 2 =
      (Complex.I * (Real.sqrt D.host.d : ℂ)) ^ 2 := by
    rw [← map_pow, sqrt_sq', h0]; simp
  rcases sq_eq_sq_iff_eq_or_eq_neg.1 h1 with h2 | h2
  · obtain ⟨τ, hτ⟩ := exists_tau_of_val (ψ : D.host.E →+* ℂ) h2
    refine ⟨τ, ?_⟩
    rw [hτ, RingHom.comp_assoc, hψ, hreal]
  · obtain ⟨τ, hτ⟩ := exists_tau_of_val ((starRingEnd ℂ).comp (ψ : D.host.E →+* ℂ))
      (by rw [RingHom.comp_apply, h2]; simp)
    refine ⟨τ, ?_⟩
    rw [hτ, ← RingHom.comp_assoc]
    have hcc : (starRingEnd ℂ).comp (starRingEnd ℂ) = RingHom.id ℂ := by
      ext z; simp
    rw [hcc, RingHom.id_comp, hψ]

/- English proof (translation)
Introduce `{D} w` and use `exists_conj_tauE_over D w`.
-/
theorem conj_tauE_over_realPlace : ∀ {D : D7} (w : InfinitePlace D.host.F), ∃ τ : D.what₂.Tau,
    ((starRingEnd ℂ).comp (tauE D τ)).comp (algebraMap D.host.F D.host.E) = w.embedding :=
  fun {D} w => exists_conj_tauE_over D w

end GlobalTheory.ConjTypeOverReal

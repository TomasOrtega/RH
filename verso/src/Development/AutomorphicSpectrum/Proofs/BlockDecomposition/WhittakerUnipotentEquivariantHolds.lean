import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FintypeResidue
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalFunctionalSectionNonvanishing

noncomputable section

open MeasureTheory Matrix GroundTheory.LocalField GroundTheory.Automorphic
open GroundTheory.Automorphic.Spherical GroundTheory.Automorphic.Iwasawa GroundTheory.Automorphic.GLnLocal
open scoped ValuativeRel

namespace GlobalTheory.CompanionTheory.LFUDom

/- English proof (translation)
Introduce `x hx`. Take `⟨hc, h1, h0⟩` from `h`. Establish `ht` using `isTrivialOn_addCharConductor hc h1`. Rewrite `ht` using `[h0]`. Use `ht x (mem_valBall_zero_iff.2 hx)` as an intermediate fact.

Use `show ((ψ x : Circle) : ℂ) = 1`. Rewrite using `[this, Circle.coe_one]`.
-/
theorem compChar_eq_one_of_isStd {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] {ψ : AddChar F Circle} (h : Ad3.IsStd ψ) :
    ∀ x ∈ 𝒪[F], Circle.coeHom.compAddChar ψ x = 1 := by
  intro x hx
  obtain ⟨hc, h1, h0⟩ := h
  have ht := isTrivialOn_addCharConductor hc h1
  rw [h0] at ht
  have := ht x (mem_valBall_zero_iff.2 hx)
  show ((ψ x : Circle) : ℂ) = 1
  rw [this, Circle.coe_one]

/- English proof (translation)
Use `⟨fun {i j} hij => ?_, fun i => ?_⟩` and prove the remaining obligations. Apply the tactic sequence `fin_cases i <;> fin_cases j <;> simp_all [Ad3.uni2]`. Apply the tactic sequence `fin_cases i <;> simp [Ad3.uni2]`.
-/
theorem uni2_mem_unipotent {F : Type} [Field F] (y : F) : Ad3.uni2 y ∈ unipotent F 2 := by
  refine ⟨fun {i j} hij => ?_, fun i => ?_⟩
  · fin_cases i <;> fin_cases j <;> simp_all [Ad3.uni2]
  · fin_cases i <;> simp [Ad3.uni2]

/- English proof (translation)
Simplify using `[Whittaker.superdiagSum, Fin.sum_univ_two, Ad3.uni2]`.
-/
theorem superdiagSum_uni2 {F : Type} [Field F] (y : F) :
    Whittaker.superdiagSum ((Ad3.uni2 y : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) = y := by
  simp [Whittaker.superdiagSum, Fin.sum_univ_two, Ad3.uni2]

/- English proof (translation)
Introduce `F _ _ _ _ _ _ ψ hψ ν y g`. Unfold `Ad3.LFS.s2`. Rewrite using `[sphericalWhittaker_mul_left (compChar_eq_one_of_isStd hψ) _ (uni2_mem_unipotent y) g, Whittaker.psiN, superdiagSum_uni2]`. Both sides reduce to the same expression.
-/
theorem whittaker_unipotent_left_equivariant : ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] [MeasurableSpace F] [BorelSpace F] (ψ : AddChar F Circle),
    Ad3.IsStd ψ → ∀ (ν : Fˣ →* ℂˣ) (y : F) (g : GL (Fin 2) F),
      Ad3.LFS.s2 ψ ν (Ad3.uni2 y * g) = ((ψ y : Circle) : ℂ) * Ad3.LFS.s2 ψ ν g := by
  intro F _ _ _ _ _ _ ψ hψ ν y g
  unfold Ad3.LFS.s2
  rw [sphericalWhittaker_mul_left (compChar_eq_one_of_isStd hψ) _ (uni2_mem_unipotent y) g,
    Whittaker.psiN, superdiagSum_uni2]
  rfl

end GlobalTheory.CompanionTheory.LFUDom

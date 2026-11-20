import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFinMapsOfForall
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneMemKAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FromBlocksMem
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.KFinLoc
open scoped TensorProduct Matrix

noncomputable section

namespace GlobalTheory.SchAConj

open GlobalTheory.WeilM
open scoped Classical

def conjSchwartz {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] (f : SchwartzMap V ℂ) : SchwartzMap V ℂ where
  toFun x := star (f x)
  smooth' := Complex.conjLIE.toContinuousLinearEquiv.contDiff.comp f.smooth'
  decay' := by
    intro k n
    obtain ⟨C, hC⟩ := f.decay' k n
    refine ⟨C, fun x => ?_⟩
    have h := Complex.conjLIE.norm_iteratedFDeriv_comp_left (𝕜 := ℝ) (f : V → ℂ) x n
    have e : (fun x => star (f x)) = (Complex.conjLIE : ℂ → ℂ) ∘ (f : V → ℂ) := rfl
    show ‖x‖ ^ k * ‖iteratedFDeriv ℝ n (fun x => star (f x)) x‖ ≤ C
    rw [e, h]
    exact hC x

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem conjSchwartz_apply {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] (f : SchwartzMap V ℂ) (x : V) :
    conjSchwartz f x = star (f x) := rfl

/- English proof (translation)
Introduce `F _ _ κ _ Φ hΦ`. Proceed by induction on `hΦ using Submodule.span_induction with`. Consider the case `mem Ψ hΨ`. Take `⟨f, g, hg, rfl⟩` from `hΨ`. Use `Submodule.subset_span ⟨conjSchwartz f, fun y => star (g y), ⟨hg.1.comp star, ?_⟩, ?_⟩` and prove the remaining obligations.

Conclude with `hg.2.comp_left (g := star) (star_zero ℂ)`. Use function extensionality and compare the values at `x`. Simplify using `[pureA, conjSchwartz_apply, star_mul']`. Consider the case `zero`. Use `(schA F κ).zero_mem using 1` and compare the differences between its conclusion and the goal.

Use function extensionality and compare the values at `x`. Simplify using the standard rewrite rules. Consider the case `add Ψ Ψ' _ _ h h'`. Use `(schA F κ).add_mem h h'` as an intermediate fact. Use `this using 1` and compare the differences between its conclusion and the goal.

Use function extensionality and compare the values at `x`. Simplify using `[star_add]`. Consider the case `smul c Ψ _ h`. Use `(schA F κ).smul_mem (star c) h` as an intermediate fact. Use `this using 1` and compare the differences between its conclusion and the goal.

Use function extensionality and compare the values at `x`. Simplify using `[star_mul']`.
-/
theorem star_mem_schA : ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ]
    (Φ : (κ → AF F) → ℂ), Φ ∈ schA F κ → (fun x => star (Φ x)) ∈ schA F κ := by
  intro F _ _ κ _ Φ hΦ
  induction hΦ using Submodule.span_induction with
  | mem Ψ hΨ =>
    obtain ⟨f, g, hg, rfl⟩ := hΨ
    refine Submodule.subset_span ⟨conjSchwartz f, fun y => star (g y), ⟨hg.1.comp star, ?_⟩, ?_⟩
    · exact hg.2.comp_left (g := star) (star_zero ℂ)
    · funext x
      simp [pureA, conjSchwartz_apply, star_mul']
  | zero =>
    convert (schA F κ).zero_mem using 1
    funext x; simp
  | add Ψ Ψ' _ _ h h' =>
    have := (schA F κ).add_mem h h'
    convert this using 1
    funext x; simp [star_add]
  | smul c Ψ _ h =>
    have := (schA F κ).smul_mem (star c) h
    convert this using 1
    funext x; simp [star_mul']

end GlobalTheory.SchAConj

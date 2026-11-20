import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.OneSubOfIsIrreducible
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HypothesesAbsDet
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.BernsteinUnitaryProductIrreducible
import Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.GenericUnitaryDualGLOfTwo
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.PrincipalSeriesSubquotientOfCharacters
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsSubquotientUnramPrinSeriesOfHasSupport
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ParIndJacPlacing
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NonemptyEquivMultiProdOne
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.NontrivialOfIrreducible
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.TypeTwo GlobalTheory.ThetaGL GlobalTheory.LocGL
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.TypeTwo.PowIrrProof

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

/- English proof (translation)
Take `⟨S, f, hf⟩` from `h`. Take `⟨y, hy⟩` from `exists_ne (0 : W)`. Take `⟨v, rfl⟩` from `hf y`. Use `haveI : IsSimpleOrder (Subrepresentation ρ) := hρ`. Break down `eq_bot_or_eq_top S with rfl | rfl` into its components or cases.

Conclude with `absurd (by rw [show v = 0 from Subtype.ext v.2, map_zero]) hy`. Set `F : ρ.IntertwiningMap σ` to `f.comp (topEquiv ρ).symm.toIntertwiningMap`. Establish `hs : Function.Surjective F` using `hf.comp (topEquiv ρ).symm.toLinearEquiv.surjective`. Use `⟨equivOfBijective F ⟨(injective_iff_map_eq_zero _).2 fun x hx => ?_, hs⟩⟩` and prove the remaining obligations. Use `haveI : IsSimpleOrder (Subrepresentation ρ) := hρ`.

Break down `eq_bot_or_eq_top F.ker with h | h` into its components or cases. Establish `: x ∈ F.ker` using `hx`. Rewrite `this` using `[h]`. Conclude with `this`. Establish `: v.1 ∈ F.ker` using `by rw [h]; trivial`.

Conclude with `absurd this hy`.
-/
theorem equiv_of_isSubquotient {G V W : Type} [Group G] [AddCommGroup V] [Module ℂ V] [AddCommGroup W]
    [Module ℂ W] {σ : Representation ℂ G W} {ρ : Representation ℂ G V} (h : IsSubquotient σ ρ) [Nontrivial W]
    (hρ : ρ.IsIrreducible) : Nonempty (ρ.Equiv σ) := by
  obtain ⟨S, f, hf⟩ := h
  obtain ⟨y, hy⟩ := exists_ne (0 : W)
  obtain ⟨v, rfl⟩ := hf y
  haveI : IsSimpleOrder (Subrepresentation ρ) := hρ
  rcases eq_bot_or_eq_top S with rfl | rfl
  · exact absurd (by rw [show v = 0 from Subtype.ext v.2, map_zero]) hy
  let F : ρ.IntertwiningMap σ := f.comp (topEquiv ρ).symm.toIntertwiningMap
  have hs : Function.Surjective F := hf.comp (topEquiv ρ).symm.toLinearEquiv.surjective
  refine ⟨equivOfBijective F ⟨(injective_iff_map_eq_zero _).2 fun x hx => ?_, hs⟩⟩
  haveI : IsSimpleOrder (Subrepresentation ρ) := hρ
  rcases eq_bot_or_eq_top F.ker with h | h
  · have : x ∈ F.ker := hx
    rw [h] at this
    exact this
  · have : v.1 ∈ F.ker := by rw [h]; trivial
    exact absurd this hy

/- English proof (translation)
Take `⟨S, f, hf⟩` from `h`. Use `hf.nontrivial` as an intermediate fact. Conclude with `Subtype.val_injective.nontrivial (α := S.toSubmodule)`.
-/
theorem nontrivial_of_isSubquotient {G V W : Type} [Group G] [AddCommGroup V] [Module ℂ V] [AddCommGroup W]
    [Module ℂ W] {σ : Representation ℂ G W} {ρ : Representation ℂ G V} (h : IsSubquotient σ ρ) [Nontrivial W] :
    Nontrivial V := by
  obtain ⟨S, f, hf⟩ := h
  have := hf.nontrivial
  exact Subtype.val_injective.nontrivial (α := S.toSubmodule)

end GlobalTheory.TypeTwo.PowIrrProof

namespace GlobalTheory.TypeTwo.PowIrrProof

end GlobalTheory.TypeTwo.PowIrrProof

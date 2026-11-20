import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RankPosOfLeaves
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CentreEnvelopingAlgebraCommuteRealLieSmoothing

noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.DiscSpec GlobalTheory.CompanionTheory.CTFin PositivityTheory.Rg.Rs
open PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.SpectralAccumulation
open GlobalTheory.CompanionTheory.EGlue

namespace GlobalTheory.CompanionTheory.EGlue

/- English proof (translation)
Proceed by induction on `hz using Algebra.adjoin_induction with`. Consider the case `mem x hx`. Take `⟨X, rfl⟩` from `hx`. Conclude with `fun χ hχ => ⟨hU (.lie X) χ hχ, hT (.lie X) χ hχ⟩`. Consider the case `algebraMap c`.

Introduce `χ hχ`. Simplify `U.smul_mem c hχ` using `[Module.algebraMap_end_apply]`. Consider the case `add x y _ _ hx hy`. Introduce `χ hχ`. Take `⟨x₁, x₂⟩` from `hx χ hχ`.

Take `⟨y₁, y₂⟩` from `hy χ hχ`. Conclude with `⟨by simpa using U.add_mem x₁ y₁, by simp [x₂, y₂]⟩`. Consider the case `mul x y _ _ hx hy`. Introduce `χ hχ`. Take `⟨y₁, y₂⟩` from `hy χ hχ`.

Take `⟨x₁, x₂⟩` from `hx _ y₁`. Conclude with `⟨by simpa [Module.End.mul_apply] using x₁, by simp [Module.End.mul_apply, x₂, y₂]⟩`.
-/
theorem adjoin_lie_equiv {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {N : ℕ}
    {U : Submodule ℂ (Sm E N)} (T : Sm E N →ₗ[ℂ] Sm E N) (hU : IsStable U)
    (hT : ∀ o, ∀ χ ∈ U, T (act o χ) = act o (T χ)) {z : Module.End ℂ (Sm E N)}
    (hz : z ∈ Algebra.adjoin ℂ (Set.range (lie E N))) :
    ∀ χ ∈ U, z χ ∈ U ∧ T (z χ) = z (T χ) := by
  induction hz using Algebra.adjoin_induction with
  | mem x hx =>
    obtain ⟨X, rfl⟩ := hx
    exact fun χ hχ => ⟨hU (.lie X) χ hχ, hT (.lie X) χ hχ⟩
  | algebraMap c =>
    intro χ hχ
    simpa [Module.algebraMap_end_apply] using U.smul_mem c hχ
  | add x y _ _ hx hy =>
    intro χ hχ
    obtain ⟨x₁, x₂⟩ := hx χ hχ
    obtain ⟨y₁, y₂⟩ := hy χ hχ
    exact ⟨by simpa using U.add_mem x₁ y₁, by simp [x₂, y₂]⟩
  | mul x y _ _ hx hy =>
    intro χ hχ
    obtain ⟨y₁, y₂⟩ := hy χ hχ
    obtain ⟨x₁, x₂⟩ := hx _ y₁
    exact ⟨by simpa [Module.End.mul_apply] using x₁, by simp [Module.End.mul_apply, x₂, y₂]⟩

/- English proof (translation)
Introduce `E _ _ _ N U T ψ m hU hT hψ hc τ u`. Rewrite using `[← (adjoin_lie_equiv T hU hT (GlobalTheory.CentreSmooth.cap_mem τ u) ψ hψ).2, hc τ u, map_smul]`.
-/
theorem capEquiv : CapEquiv := by
  intro E _ _ _ N U T ψ m hU hT hψ hc τ u
  rw [← (adjoin_lie_equiv T hU hT (GlobalTheory.CentreSmooth.cap_mem τ u) ψ hψ).2, hc τ u, map_smul]

end GlobalTheory.CompanionTheory.EGlue

end

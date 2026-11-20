import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.LanglandsDataDualGL
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StandardCosocleGL
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.GeometricLemmaFiltration
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IrreducibleAdmissibleGL
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.StandardFunctorsFiniteLength
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsLevelCharacterAtConjugateSplitPlace
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsSupercuspidalOfIsCuspidal
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsCuspidalOfIsSupercuspidal
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsSupercuspidalCompGeneralLinearGroupMapOfFieldE
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.LocLanglands GlobalTheory.JHMult

namespace GlobalTheory.InvTransposeCusp

/- English proof (translation)
Apply `Units.ext` to reduce the goal to its premises. Conclude with `Matrix.transpose_transpose (g : Matrix (Fin n) (Fin n) R)`.
-/
theorem invTranspose_invol {R : Type} [CommRing R] (n : ℕ) (g : GL (Fin n) R) :
    GlobalTheory.TypeTame.invTranspose n (GlobalTheory.TypeTame.invTranspose n g) = g := by
  apply Units.ext
  exact Matrix.transpose_transpose (g : Matrix (Fin n) (Fin n) R)

/- English proof (translation)
Establish `hcont` using `GlobalTheory.TypeTame.continuous_invTranspose (R := k) n`. Take `⟨hsm, hc⟩` from `hs`. Use `⟨fun v => (hsm v).preimage hcont, ?_⟩` and prove the remaining obligations. Introduce `v l hl`. Establish `hl' : l ∈ smoothPart π.dual` using `by show IsOpen {g | π.dual g l = l}`.

Establish `: {g | π.dual g l = l} = (GlobalTheory.TypeTame.invTranspose n) ⁻¹' {g | Representation.dual (π.comp (GlobalTheory.TypeTame.invTranspose n)) g l = l}`. Use extensionality with `g`. Simplify using `[Representation.dual, map_inv, invTranspose_invol]`. Rewrite using `[this]`. Conclude with `hl.preimage hcont`.

Take `⟨C, hC, hCl⟩` from `hc v l hl'`. Use `⟨(GlobalTheory.TypeTame.invTranspose n) '' C, hC.image hcont, fun g hg => ?_⟩` and prove the remaining obligations. Take `⟨z, hz, c, hcC, hgc⟩` from `hCl (GlobalTheory.TypeTame.invTranspose n g) hg`. Use `⟨GlobalTheory.TypeTame.invTranspose n z, ?_, GlobalTheory.TypeTame.invTranspose n c, ⟨c, hcC, rfl⟩, ?_⟩` and prove the remaining obligations. Rewrite using `[Subgroup.mem_center_iff]`.

Introduce `h`. Use `Subgroup.mem_center_iff.1 hz (GlobalTheory.TypeTame.invTranspose n h)` as an intermediate fact. Establish `h2` using `congrArg (GlobalTheory.TypeTame.invTranspose n) this`. Simplify `h2` using `[map_mul, invTranspose_invol]`. Rewrite using `[← map_mul, ← hgc, invTranspose_invol]`.
-/
theorem isSupercuspidal_comp_invTranspose (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (n : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ (GL (Fin n) k) V) (hs : IsSupercuspidal π) :
    IsSupercuspidal (π.comp (GlobalTheory.TypeTame.invTranspose n)) := by
  have hcont := GlobalTheory.TypeTame.continuous_invTranspose (R := k) n
  obtain ⟨hsm, hc⟩ := hs
  refine ⟨fun v => (hsm v).preimage hcont, ?_⟩
  intro v l hl
  have hl' : l ∈ smoothPart π.dual := by
    show IsOpen {g | π.dual g l = l}
    have : {g | π.dual g l = l} = (GlobalTheory.TypeTame.invTranspose n) ⁻¹'
        {g | Representation.dual (π.comp (GlobalTheory.TypeTame.invTranspose n)) g l = l} := by
      ext g
      simp [Representation.dual, map_inv, invTranspose_invol]
    rw [this]
    exact hl.preimage hcont
  obtain ⟨C, hC, hCl⟩ := hc v l hl'
  refine ⟨(GlobalTheory.TypeTame.invTranspose n) '' C, hC.image hcont, fun g hg => ?_⟩
  obtain ⟨z, hz, c, hcC, hgc⟩ := hCl (GlobalTheory.TypeTame.invTranspose n g) hg
  refine ⟨GlobalTheory.TypeTame.invTranspose n z, ?_, GlobalTheory.TypeTame.invTranspose n c, ⟨c, hcC, rfl⟩, ?_⟩
  · rw [Subgroup.mem_center_iff]
    intro h
    have := Subgroup.mem_center_iff.1 hz (GlobalTheory.TypeTame.invTranspose n h)
    have h2 := congrArg (GlobalTheory.TypeTame.invTranspose n) this
    simpa [map_mul, invTranspose_invol] using h2
  · rw [← map_mul, ← hgc, invTranspose_invol]

/- English proof (translation)
Introduce `k _ _ _ _ n V _ _ π h`. Conclude with `GlobalTheory.SuperCusp.isCuspidal_of_isSupercuspidal k n V _ (isSupercuspidal_comp_invTranspose k n V π (GlobalTheory.CuspCoef.isSupercuspidal_of_isCuspidal k n V π h))`.
-/
theorem isCuspidal_comp_invTranspose : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin n) k) V), IsCuspidal π → IsCuspidal (π.comp (GlobalTheory.TypeTame.invTranspose n)) := by
  intro k _ _ _ _ n V _ _ π h
  exact GlobalTheory.SuperCusp.isCuspidal_of_isSupercuspidal k n V _
    (isSupercuspidal_comp_invTranspose k n V π
      (GlobalTheory.CuspCoef.isSupercuspidal_of_isCuspidal k n V π h))

end GlobalTheory.InvTransposeCusp

import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsAuxiliaryVectorWittDec
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsGivenStageEqOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemMulInvIff
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin

namespace GlobalTheory.AdjSrcZero

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts}

/- English proof (translation)
Take `⟨⟨hAA, hbar⟩, -⟩` from `GlobalTheory.ChiGrid.StairConj.conj_AA_and_stA D`. Introduce `h0`. Apply `hAA` to reduce the goal to its premises. Rewrite `h0`, the goal using `[FractionalIdeal.eq_zero_iff]`. Introduce `x hx`.

Establish `h1 : star x ∈ D.host.AAbar` using `(hbar _).2 (by rwa [star_star])`. Establish `h2` using `h0 _ h1`. Simplify using `using congrArg star h2`.
-/
theorem AAbar_ne_zero (D : D7) : D.host.AAbar ≠ 0 := by
  obtain ⟨⟨hAA, hbar⟩, -⟩ := GlobalTheory.ChiGrid.StairConj.conj_AA_and_stA D
  intro h0
  apply hAA
  rw [FractionalIdeal.eq_zero_iff] at h0 ⊢
  intro x hx
  have h1 : star x ∈ D.host.AAbar := (hbar _).2 (by rwa [star_star])
  have h2 := h0 _ h1
  simpa using congrArg star h2

/- English proof (translation)
Establish `hA` using `AAbar_ne_zero D`. Simplify using `only [zero_add, pow_one, Places.stA, Places.stAbar, shiftId, mul_inv, inv_inv]`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem AAbar_mul_st (G : GridData L sc) :
    D.host.AAbar * (G.pl.stA sc ^ (0 + 1) * (G.pl.stAbar sc ^ (0 + 1))⁻¹) = D.host.AA * shiftId G := by
  have hA := AAbar_ne_zero D
  simp only [zero_add, pow_one, Places.stA, Places.stAbar, shiftId, mul_inv, inv_inv]
  calc _ = (D.host.AAbar * D.host.AAbar⁻¹) * (D.host.AA *
        (((G.pl.modul sc : Ideal (𝓞 D.host.E)) : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) *
        ((G.pl.modulBar sc : Ideal (𝓞 D.host.E)) : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E)⁻¹)) := by ring
    _ = _ := by rw [mul_inv_cancel₀ hA, one_mul]

/- English proof (translation)
Introduce `D T L sc G n Λ₀ a ha s hs`. Take `⟨⟨-, hbar⟩, -⟩` from `GlobalTheory.ChiGrid.StairConj.conj_AA_and_stA D`. Establish `key : ∀ b ∈ D.host.AA * shiftId G, ∀ y ∈ Λ₀, b • y ∈ Submodule.span (𝓞 D.host.E) {y | ∃ a' ∈ D.host.AA, ∃ s' ∈ idLat (shiftId G) Λ₀, y = a' • s'}`. Introduce `b hb y hy`. Use `FractionalIdeal.mul_induction_on (C := fun b => b • y ∈ Submodule.span (𝓞 D.host.E) {y | ∃ a' ∈ D.host.AA, ∃ s' ∈ idLat (shiftId G) Λ₀, y = a' • s'}) hb ?_ ?_` and prove the remaining obligations.

Introduce `i hi j hj`. Use `Submodule.subset_span ⟨i, hi, j • y, Submodule.subset_span ⟨j, hj, y, hy, rfl⟩, ?_⟩` and prove the remaining obligations. Rewrite using `[smul_smul]`. Introduce `x z hx hz`. Rewrite using `[add_smul]`.

Conclude with `add_mem hx hz`. Establish `hsa : star a ∈ D.host.AAbar` using `(hbar _).2 (by rwa [star_star])`. Unfold `idLat at hs`. Use `Submodule.span_induction (p := fun z _ => star a • z ∈ Submodule.span (𝓞 D.host.E) {y | ∃ a' ∈ D.host.AA, ∃ s' ∈ idLat (shiftId G) Λ₀, y = a' • s'}) ?_ ?_ ?_ ?_ hs` and prove the remaining obligations. Introduce and unpack `_ ⟨i, hi, y, hy, rfl⟩`.

Rewrite using `[smul_smul]`. Conclude with `key _ (AAbar_mul_st G ▸ FractionalIdeal.mul_mem_mul hsa hi) y hy`. Simplify using the standard rewrite rules. Introduce `x z _ _ hx hz`. Rewrite using `[smul_add]`.

Conclude with `add_mem hx hz`. Introduce `c x _ hx`. Rewrite using `[smul_comm]`. Conclude with `Submodule.smul_mem _ c hx`.
-/
theorem star_smul_mem_span : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} (G : GridData L sc) {n : ℕ}
    (Λ₀ : Submodule (𝓞 D.host.E) (Fin n → D.host.E)), ∀ a ∈ D.host.AA,
    ∀ s ∈ idLat (G.pl.stA sc ^ (0 + 1) * (G.pl.stAbar sc ^ (0 + 1))⁻¹) Λ₀,
    star a • s ∈ Submodule.span (𝓞 D.host.E) {y | ∃ a' ∈ D.host.AA, ∃ s' ∈ idLat (shiftId G) Λ₀, y = a' • s'} := by
  intro D T L sc G n Λ₀ a ha s hs
  obtain ⟨⟨-, hbar⟩, -⟩ := GlobalTheory.ChiGrid.StairConj.conj_AA_and_stA D
  have key : ∀ b ∈ D.host.AA * shiftId G, ∀ y ∈ Λ₀, b • y ∈
      Submodule.span (𝓞 D.host.E) {y | ∃ a' ∈ D.host.AA, ∃ s' ∈ idLat (shiftId G) Λ₀, y = a' • s'} := by
    intro b hb y hy
    refine FractionalIdeal.mul_induction_on (C := fun b => b • y ∈
      Submodule.span (𝓞 D.host.E) {y | ∃ a' ∈ D.host.AA, ∃ s' ∈ idLat (shiftId G) Λ₀, y = a' • s'}) hb ?_ ?_
    · intro i hi j hj
      refine Submodule.subset_span ⟨i, hi, j • y, Submodule.subset_span ⟨j, hj, y, hy, rfl⟩, ?_⟩
      rw [smul_smul]
    · intro x z hx hz
      rw [add_smul]
      exact add_mem hx hz
  have hsa : star a ∈ D.host.AAbar := (hbar _).2 (by rwa [star_star])
  unfold idLat at hs
  refine Submodule.span_induction (p := fun z _ => star a • z ∈
      Submodule.span (𝓞 D.host.E) {y | ∃ a' ∈ D.host.AA, ∃ s' ∈ idLat (shiftId G) Λ₀, y = a' • s'}) ?_ ?_ ?_ ?_ hs
  · rintro _ ⟨i, hi, y, hy, rfl⟩
    rw [smul_smul]
    exact key _ (AAbar_mul_st G ▸ FractionalIdeal.mul_mem_mul hsa hi) y hy
  · simp
  · intro x z _ _ hx hz
    rw [smul_add]
    exact add_mem hx hz
  · intro c x _ hx
    rw [smul_comm]
    exact Submodule.smul_mem _ c hx

end GlobalTheory.AdjSrcZero

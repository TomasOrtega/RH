import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagMat
import Development.AbelianVarietyTheory.Counterexamples.PlaceInjectivity.PlaceInjective
open NumberField MvPolynomial Filter Topology Formalism.BasicNotions Formalism.MainNotions Formalism.DegreeFormula GlobalTheory.FlagPoly GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.CovTest GlobalTheory.Published
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt
open Formalism.BasicNotions.DV Formalism.MainNotions.WeightThresholdDefs GlobalTheory.FlagAr GlobalTheory.ShFam.Pad GlobalTheory.VB GlobalTheory.ShFam GlobalTheory.TrueGeo Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ArLieBase
open GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.ProjVar
open GlobalTheory.FlagCls

noncomputable section

namespace GlobalTheory.FlagCls

/- English proof (translation)
Introduce `h` and use `by exact IsTotallyComplex.complexEmbedding_not_isReal (tauEmb D ρ) (ComplexEmbedding.isReal_iff.2 h.symm)`.
-/
theorem tauEmb_ne_conjugate (D : D7) (ρ : D.what₂.Tau) :
    tauEmb D ρ ≠ ComplexEmbedding.conjugate (tauEmb D ρ) := fun h => by
  exact IsTotallyComplex.complexEmbedding_not_isReal (tauEmb D ρ) (ComplexEmbedding.isReal_iff.2 h.symm)

/- English proof (translation)
Introduce `D`. Establish `hb : Function.Bijective fun ρ => InfinitePlace.mk (tauEmb D ρ)` using `GlobalTheory.VolRatioCheck.place_bijective D`. Establish `hT : ∀ ρ, embB D (ρ, true) = tauEmb D ρ` using `fun _ => rfl`. Establish `hF : ∀ ρ, embB D (ρ, false) = ComplexEmbedding.conjugate (tauEmb D ρ)` using `fun _ => rfl`. Establish `hm : ∀ a, InfinitePlace.mk (embB D a) = InfinitePlace.mk (tauEmb D a.1)`.

Introduce and unpack `⟨ρ, _ | _⟩`. Rewrite using `[hF, InfinitePlace.mk_conjugate_eq]`. Rewrite using `[hT]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨a, s⟩ ⟨b, t⟩ h`.

Establish `hab : a = b` using `hb.1 ((hm (a, s)).symm.trans ((congrArg InfinitePlace.mk h).trans (hm (b, t))))`. Substitute `hab` using the available equality. Apply the tactic sequence `cases s <;> cases t`. Both sides reduce to the same expression. Rewrite `h` using `[hF, hT]`.

Conclude with `(tauEmb_ne_conjugate D a h.symm).elim`. Rewrite `h` using `[hF, hT]`. Conclude with `(tauEmb_ne_conjugate D a h).elim`. Both sides reduce to the same expression. Introduce `φ`.

Take `⟨ρ, hρ⟩` from `hb.2 (InfinitePlace.mk φ)`. Break down `InfinitePlace.mk_eq_iff.1 hρ with h | h` into its components or cases. Conclude with `⟨(ρ, true), h⟩`. Conclude with `⟨(ρ, false), h⟩`.
-/
theorem embB_bijective : ∀ D : D7, Function.Bijective (embB D) := by
  intro D
  have hb : Function.Bijective fun ρ => InfinitePlace.mk (tauEmb D ρ) := GlobalTheory.VolRatioCheck.place_bijective D
  have hT : ∀ ρ, embB D (ρ, true) = tauEmb D ρ := fun _ => rfl
  have hF : ∀ ρ, embB D (ρ, false) = ComplexEmbedding.conjugate (tauEmb D ρ) := fun _ => rfl
  have hm : ∀ a, InfinitePlace.mk (embB D a) = InfinitePlace.mk (tauEmb D a.1) := by
    rintro ⟨ρ, _ | _⟩
    · rw [hF, InfinitePlace.mk_conjugate_eq]
    · rw [hT]
  constructor
  · rintro ⟨a, s⟩ ⟨b, t⟩ h
    have hab : a = b := hb.1 ((hm (a, s)).symm.trans ((congrArg InfinitePlace.mk h).trans (hm (b, t))))
    subst hab
    cases s <;> cases t
    · rfl
    · rw [hF, hT] at h; exact (tauEmb_ne_conjugate D a h.symm).elim
    · rw [hF, hT] at h; exact (tauEmb_ne_conjugate D a h).elim
    · rfl
  · intro φ
    obtain ⟨ρ, hρ⟩ := hb.2 (InfinitePlace.mk φ)
    rcases InfinitePlace.mk_eq_iff.1 hρ with h | h
    · exact ⟨(ρ, true), h⟩
    · exact ⟨(ρ, false), h⟩

end GlobalTheory.FlagCls

end

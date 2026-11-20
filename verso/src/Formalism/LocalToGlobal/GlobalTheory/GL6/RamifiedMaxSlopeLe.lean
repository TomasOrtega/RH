import Formalism.LocalToGlobal.GlobalTheory.GL6.Statement
import Formalism.HarderNarasimhan.ShiftInvariance

noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.LocalLatticeBases

open Formalism.BasicNotions

/- English proof (translation)
Establish `hLne : L ≠ ⊥` using `fun h => hN (le_bot_iff.1 (h ▸ hNL))`. Establish `hzl : (Formalism.HN.zl ρ N : Set E) ⊆ (Formalism.HN.zl ρ L : Set E)`. Introduce and unpack `x ⟨y, hy, rfl⟩`. Conclude with `⟨y, hNL hy, rfl⟩`. Establish `hNlat : Formalism.HN.IsLat ρ N`.

Use `⟨hL.1.mono hNL, ?_⟩` and prove the remaining obligations. Use `hL.2` as an intermediate fact. Conclude with `DiscreteTopology.of_subset (s := (Formalism.HN.zl ρ L : Set E)) inferInstance hzl`. Establish `cL` using `(Formalism.HN.slope_characterization R V E ρ L hL hLne).1 (Formalism.HN.muMax ρ L)`. Establish `cN` using `(Formalism.HN.slope_characterization R V E ρ N hNlat hN).1 (Formalism.HN.muMax ρ L)`.

Conclude with `cN.2 fun M hM => cL.1 le_rfl M (hM.trans hNL)`.
-/
theorem max_slope_mono {R V E : Type} [Ring R] [AddCommGroup V] [Module R V] [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] (ρ : V →+ E) (L N : Submodule R V)
    (hL : Formalism.HN.IsLat ρ L) (hNL : N ≤ L) (hN : N ≠ ⊥) :
    Formalism.HN.muMax ρ N ≤ Formalism.HN.muMax ρ L := by
  have hLne : L ≠ ⊥ := fun h => hN (le_bot_iff.1 (h ▸ hNL))
  have hzl : (Formalism.HN.zl ρ N : Set E) ⊆ (Formalism.HN.zl ρ L : Set E) := by
    rintro x ⟨y, hy, rfl⟩
    exact ⟨y, hNL hy, rfl⟩
  have hNlat : Formalism.HN.IsLat ρ N := by
    refine ⟨hL.1.mono hNL, ?_⟩
    have := hL.2
    exact DiscreteTopology.of_subset (s := (Formalism.HN.zl ρ L : Set E)) inferInstance hzl
  have cL := (Formalism.HN.slope_characterization R V E ρ L hL hLne).1 (Formalism.HN.muMax ρ L)
  have cN := (Formalism.HN.slope_characterization R V E ρ N hNlat hN).1 (Formalism.HN.muMax ρ L)
  exact cN.2 fun M hM => cL.1 le_rfl M (hM.trans hNL)

/- English proof (translation)
Establish `hg` using `(D.fm u).lat_good 0`. Establish `hlat` using `(Formalism.HN.place_lattice_structure D.what₂.LL ((D.fm u).lat 0).V ((D.fm u).lat 0).ι ((D.fm u).lat 0).b ((D.fm u).lat 0).X hg.1 ((D.fm u).lat 0).L hg.2.1).1`. Establish `hle : (D.fm u).ramL ≤ ((D.fm u).lat 0).L` using `inf_le_left`. Establish `h` using `max_slope_mono _ _ _ hlat hle hne`. Unfold `Formalism.BasicNotions.HLat.muMax Formalism.HN.muMaxDef`.

Use `show 2 * Formalism.HN.muMax (Formalism.HermitianLatticesTheory.realize ((D.fm u).lat 0).b ((D.fm u).lat 0).X) (D.fm u).ramL - _ + _ ≤ _`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem ramified_max_slope_le (D : D7) (u : D.what₂.Word) (hne : (D.fm u).ramL ≠ ⊥) :
    (D.fm u).ramLat.muMax ≤ ((D.fm u).lat 0).muMax := by
  have hg := (D.fm u).lat_good 0
  have hlat := (Formalism.HN.place_lattice_structure D.what₂.LL ((D.fm u).lat 0).V ((D.fm u).lat 0).ι ((D.fm u).lat 0).b
    ((D.fm u).lat 0).X hg.1 ((D.fm u).lat 0).L hg.2.1).1
  have hle : (D.fm u).ramL ≤ ((D.fm u).lat 0).L := inf_le_left
  have h := max_slope_mono _ _ _ hlat hle hne
  unfold Formalism.BasicNotions.HLat.muMax Formalism.HN.muMaxDef
  show 2 * Formalism.HN.muMax (Formalism.HermitianLatticesTheory.realize ((D.fm u).lat 0).b ((D.fm u).lat 0).X) (D.fm u).ramL - _ + _ ≤ _
  linarith

end Formalism.L2.GlobalTheoryTheory.LocalLatticeBases

end

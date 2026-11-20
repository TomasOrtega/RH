import Mathlib
import Formalism.SharpRestriction.CuspSpanNormBounds.CongruenceAtSplitFrobeniusHolds
import Formalism.SharpRestriction.GlobalSchurBounds.ThickPlacesCorollaryOfAnyTranslate
import Formalism.FlagUnipotentLattices.CardSubgroupsOfIndexLe
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ChartGen
import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.MaxMass
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MemOfPerpPerp
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MassGenusCyclicDiscriminantSplitPrime
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.StdLatIsOrthoLatticeAndMassPropertiesStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MaximalHermitianLatticeMassRatioStatement

open NumberField Matrix GlobalTheory.Mass Formalism.HermitianLatticesTheory Formalism.BasicNotions Formalism.MainNotions.S
open scoped ENNReal Classical

namespace GlobalTheory.Mass.RowPerpMass

/- English proof (translation)
Introduce `D u F0 he hz hp hs Λ hΛ`. Set `` to `D.host.cmStar`. Take `⟨⟨hPD, hrk⟩, hL⟩` from `GlobalTheory.Mass.RowPerp.main D u F0 he hz`. Take `⟨hInt, hdisc⟩` from `hL Λ hΛ`. Take `⟨hsym, hortho, hpos, -, -⟩` from `GlobalTheory.T.stdLat_isOrthoLattice_and_mass_properties D.host.E D.sp.cm.cmUnram D.R.k`.

Establish `hk : 1 ≤ D.R.k` using `by have := D.R.m_add_three_le_k; omega`. Establish `hf : fDeg D.host.E = D.R.f`. Establish `: NumberField.IsTotallyComplex D.host.E` using `D.sp.cm.cmUnram.1`. Establish `h1` using `NumberField.InfinitePlace.card_add_two_mul_card_eq_rank D.host.E`. Establish `h2` using `Formalism.HC.HostAx.finrank_cmField D.host.toHostAx`.

Establish `h3 : NumberField.InfinitePlace.nrRealPlaces D.host.E = 0` using `NumberField.IsTotallyComplex.nrRealPlaces_eq_zero D.host.E`. Establish `h4 : fDeg D.host.E = NumberField.InfinitePlace.nrRealPlaces D.host.E + NumberField.InfinitePlace.nrComplexPlaces D.host.E` using `NumberField.InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces D.host.E`. Use `show _ = 2 * D.R.ord`. Use linear arithmetic over natural numbers and integers. Establish `hmass` using `GlobalTheory.Mass.CyclicDisc.main GlobalTheory.T.maximalHermitianLattice_massRatio D.host.E (D.sp.X 0).V (D.sp.X 0).hT D.sp.cm.cmUnram (D.sp.X 0).herm hPD (by rw [hrk]; exact hk) (Fin D.R.k → D.host.E) (Cnt.stdH D.host.E D.R.k) hsym (Cnt.stdLat D.host.E D.R.k) (by rw [hrk]; exact …`.

Rewrite `hmass` using `[hrk, hf]`. Establish `hS : mass (Cnt.stdH D.host.E D.R.k) (Cnt.stdLat D.host.E D.R.k) = Cnt.massS D D.R.k` using `rfl`. Rewrite `hmass` using `[hS]`. Use `⟨hmass, ?_⟩` and prove the remaining obligations. Rewrite using `[hmass]`.

Establish `hT2 : (2 : ℝ) ≤ (Lat.Tu D u : ℝ)` using `by exact_mod_cast hp.two_le`. Establish `hgeom : (Lat.Tu D u : ℝ) ^ (D.R.k - 1) ≤ ((Lat.Tu D u : ℝ) ^ D.R.k - 1) / ((Lat.Tu D u : ℝ) - 1)`. Rewrite using `[le_div_iff₀ (by linarith)]`. Establish `e : (Lat.Tu D u : ℝ) ^ D.R.k = (Lat.Tu D u : ℝ) * (Lat.Tu D u : ℝ) ^ (D.R.k - 1)`. Rewrite using `[← pow_succ']`.

Use `congr 1`. Use linear arithmetic over natural numbers and integers. Establish `h1 : (1 : ℝ) ≤ (Lat.Tu D u : ℝ) ^ (D.R.k - 1)` using `one_le_pow₀ (by linarith)`. Rewrite using `[e]`. Use the polynomial consequences of the given equalities and inequalities.

Establish `hNT : Cnt.NT D u ^ (D.R.k - 1) = ((Lat.Tu D u : ℝ) ^ (D.R.k - 1)) ^ D.R.f` using `by show (((D.mem u).A.T : ℝ) ^ D.R.f) ^ (D.R.k - 1) = _`. Rewrite using `[← pow_mul, ← pow_mul, mul_comm]`. Both sides reduce to the same expression. Rewrite using `[hNT]`. Establish `hm : 0 ≤ Cnt.massS D D.R.k` using `hpos.le`.

Use `gcongr`.
-/
theorem main : ∀ (D : D7) (u : D.what₂.Word), letI := D.host.cmStar; ∀ F0 : FlagG (VS D) D.R.rS ((Lat.Tu D u : ℕ) : D.host.E), F0.e = D.sp.hypE → F0.z = D.zmOf u → (Lat.Tu D u).Prime → Lat.SplitsCompletely (E := D.host.E) (Lat.Tu D u) → ∀ Λ : Cnt.LatV D, IsRowLat D F0 Λ → mass (D.sp.X 0).hT (Lat.L0X D Λ (lf D F0)) = Cnt.massS D D.R.k * ((((Lat.Tu D u : ℕ) : ℝ) ^ D.R.k - 1) / (((Lat.Tu D u : ℕ) : ℝ) - 1)) ^ D.R.f ∧ Cnt.massS D D.R.k * Cnt.NT D u ^ (D.R.k - 1) ≤ mass (D.sp.X 0).hT (Lat.L0X D Λ (lf D F0)) := by
  intro D u F0 he hz hp hs Λ hΛ
  let := D.host.cmStar
  obtain ⟨⟨hPD, hrk⟩, hL⟩ := GlobalTheory.Mass.RowPerp.main D u F0 he hz
  obtain ⟨hInt, hdisc⟩ := hL Λ hΛ
  obtain ⟨hsym, hortho, hpos, -, -⟩ := GlobalTheory.T.stdLat_isOrthoLattice_and_mass_properties D.host.E D.sp.cm.cmUnram D.R.k
  have hk : 1 ≤ D.R.k := by have := D.R.m_add_three_le_k; omega

  have hf : fDeg D.host.E = D.R.f := by
    have : NumberField.IsTotallyComplex D.host.E := D.sp.cm.cmUnram.1
    have h1 := NumberField.InfinitePlace.card_add_two_mul_card_eq_rank D.host.E
    have h2 := Formalism.HC.HostAx.finrank_cmField D.host.toHostAx
    have h3 : NumberField.InfinitePlace.nrRealPlaces D.host.E = 0 :=
      NumberField.IsTotallyComplex.nrRealPlaces_eq_zero D.host.E
    have h4 : fDeg D.host.E = NumberField.InfinitePlace.nrRealPlaces D.host.E +
        NumberField.InfinitePlace.nrComplexPlaces D.host.E :=
      NumberField.InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces D.host.E
    show _ = 2 * D.R.ord
    omega
  have hmass := GlobalTheory.Mass.CyclicDisc.main GlobalTheory.T.maximalHermitianLattice_massRatio D.host.E (D.sp.X 0).V (D.sp.X 0).hT
    D.sp.cm.cmUnram (D.sp.X 0).herm hPD (by rw [hrk]; exact hk) (Fin D.R.k → D.host.E)
    (Cnt.stdH D.host.E D.R.k) hsym (Cnt.stdLat D.host.E D.R.k) (by rw [hrk]; exact hortho)
    (Lat.Tu D u) hp hs _ hInt hdisc
  rw [hrk, hf] at hmass
  have hS : mass (Cnt.stdH D.host.E D.R.k) (Cnt.stdLat D.host.E D.R.k) = Cnt.massS D D.R.k := rfl
  rw [hS] at hmass
  refine ⟨hmass, ?_⟩
  rw [hmass]

  have hT2 : (2 : ℝ) ≤ (Lat.Tu D u : ℝ) := by exact_mod_cast hp.two_le
  have hgeom : (Lat.Tu D u : ℝ) ^ (D.R.k - 1) ≤ ((Lat.Tu D u : ℝ) ^ D.R.k - 1) / ((Lat.Tu D u : ℝ) - 1) := by
    rw [le_div_iff₀ (by linarith)]
    have e : (Lat.Tu D u : ℝ) ^ D.R.k = (Lat.Tu D u : ℝ) * (Lat.Tu D u : ℝ) ^ (D.R.k - 1) := by
      rw [← pow_succ']; congr 1; omega
    have h1 : (1 : ℝ) ≤ (Lat.Tu D u : ℝ) ^ (D.R.k - 1) := one_le_pow₀ (by linarith)
    rw [e]; nlinarith
  have hNT : Cnt.NT D u ^ (D.R.k - 1) = ((Lat.Tu D u : ℝ) ^ (D.R.k - 1)) ^ D.R.f := by
    show (((D.mem u).A.T : ℝ) ^ D.R.f) ^ (D.R.k - 1) = _
    rw [← pow_mul, ← pow_mul, mul_comm]; rfl
  rw [hNT]
  have hm : 0 ≤ Cnt.massS D D.R.k := hpos.le
  gcongr

end GlobalTheory.Mass.RowPerpMass

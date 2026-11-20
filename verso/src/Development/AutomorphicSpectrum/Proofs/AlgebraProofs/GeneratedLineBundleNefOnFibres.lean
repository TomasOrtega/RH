import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterNamed
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterRes
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.BlowupProjections.BlowupProjStatement
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.MoriwakiSt
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsArith
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsPieceDegree
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsEmbeddingPieces
import GroundTheory.HeightsAndTheta.Heights.Intersections.Statements
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.StatementsPushDown
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PGenOnFibres
import GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.PGeneratedNefFX
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PNefAmpleFibre
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PSemiampleNef
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.GeoNum
set_option maxSynthPendingDepth 1

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry Filter Topology NumberField

namespace GlobalTheory.CompanionTheory.Ar.Giv

open ReciprocityTheory.ChartRestriction.G.AI.I1 GroundTheory.Heights₂.Heights.HilbertSamuel GroundTheory.Heights₂.Heights

/- English proof (translation)
Introduce `K _ ι _ Ω _ y D a m w _ _ hw hg W hW hPW hchar hdim`. Set `_ : LinearOrder K` to `LinearOrder.lift' (Fintype.equivFin K) (Fintype.equivFin K).injective`. Set `_ : ∀ k, LinearOrder (ι k)` to `fun k => LinearOrder.lift' (Fintype.equivFin (ι k)) (Fintype.equivFin (ι k)).injective`. Establish `: W.IsPrime` using `hW.1`. Use `set ℓ := charOf W with hℓdef`.

Establish `hℓ : ℓ.Prime` using `SemiampleNefAlt.charOf_prime hchar`. Establish `: Fact ℓ.Prime` using `⟨hℓ⟩`. Establish `hgen : KH.GeneratedV (ZMod ℓ) (fibreIdeal ℓ y) a` using `(GenOnFibres.proof K ι Ω y _ m w hw hg).2 ℓ hℓ`. Establish `hpW : ((ℓ : ℕ) : MRing ι) ∈ W`. Establish `h` using `GroundTheory.Heights₂.Heights.Inter.C_charOf_mem W`.

Rewrite `h` using `[map_natCast]`. Then use the resulting hypothesis. Use `set W' := W.map (NefAmpleFibreAlt.red (ι := ι) ℓ) with hW'def`. Establish `hker` using `NefAmpleFibreAlt.ker_red_le (ι := ι) ℓ hpW`. Establish `hW'proj : IsProjVarF W' 1`. Use `⟨⟨Ideal.map_isPrime_of_surjective (NefAmpleFibreAlt.red_surjective ℓ) hker, NefAmpleFibreAlt.isMultiHomogIdeal_map _ hW.2.1, fun k => ?_⟩, ?_⟩` and prove the remaining obligations.

Take `⟨i, hi⟩` from `hW.2.2 k`. Use `⟨i, fun h => hi ?_⟩` and prove the remaining obligations. Rewrite using `[← NefAmpleFibreAlt.mem_map_red_iff ℓ hpW]`. Simplify `h` using `[NefAmpleFibreAlt.red]`. Rewrite using `[NefAmpleFibreAlt.ringKrullDim_red ℓ hpW, hdim, add_comm]`.

Establish `hle : fibreIdeal ℓ y ≤ W'` using `Ideal.map_mono hPW`. Establish `hI` using `GeoNumTarget.isFieldIntersection_intNum (K := K) (ι := ι) ℓ`. Establish `hnef` using `GeneratedNefF.proof (ZMod ℓ) K ι _ (fibreIdeal ℓ y) a hI hgen W' hW'proj hle`. Establish `hgeo` using `geoNumStatement ι ℓ _ hI W 1 (fun _ => a) hW hpW hW'proj`. Rewrite using `[hgeo]`.

Use `hnef using 2` and compare the differences between its conclusion and the goal. Use function extensionality and compare the values at `j`. Use `fin_cases j`. Both sides reduce to the same expression.
-/
theorem nefOnFibres_of_generatesOn :
    ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] (y : (Σ k, ι k) → Ω) (D : ℕ)
      (a : K → ℤ) (q : ℕ) (w : Fin q → Ω), IsArithVar (mCoordIdeal y) (D + 1) → Birational y →
      (∀ j, w j ∈ chartLat y a 1) → KH.GeneratesOn y a w → NefOnFibres (mCoordIdeal y) a := by
  classical
  intro K _ ι _ Ω _ y D a m w _ _ hw hg W hW hPW hchar hdim
  let _ : LinearOrder K := LinearOrder.lift' (Fintype.equivFin K) (Fintype.equivFin K).injective
  let _ : ∀ k, LinearOrder (ι k) := fun k =>
    LinearOrder.lift' (Fintype.equivFin (ι k)) (Fintype.equivFin (ι k)).injective
  have : W.IsPrime := hW.1
  set ℓ := charOf W with hℓdef
  have hℓ : ℓ.Prime := SemiampleNefAlt.charOf_prime hchar
  have : Fact ℓ.Prime := ⟨hℓ⟩
  have hgen : KH.GeneratedV (ZMod ℓ) (fibreIdeal ℓ y) a :=
    (GenOnFibres.proof K ι Ω y _ m w hw hg).2 ℓ hℓ
  have hpW : ((ℓ : ℕ) : MRing ι) ∈ W := by
    have h := GroundTheory.Heights₂.Heights.Inter.C_charOf_mem W
    rwa [map_natCast] at h
  set W' := W.map (NefAmpleFibreAlt.red (ι := ι) ℓ) with hW'def
  have hker := NefAmpleFibreAlt.ker_red_le (ι := ι) ℓ hpW
  have hW'proj : IsProjVarF W' 1 := by
    refine ⟨⟨Ideal.map_isPrime_of_surjective (NefAmpleFibreAlt.red_surjective ℓ) hker,
      NefAmpleFibreAlt.isMultiHomogIdeal_map _ hW.2.1, fun k => ?_⟩, ?_⟩
    · obtain ⟨i, hi⟩ := hW.2.2 k
      refine ⟨i, fun h => hi ?_⟩
      rw [← NefAmpleFibreAlt.mem_map_red_iff ℓ hpW]
      simpa [NefAmpleFibreAlt.red] using h
    · rw [NefAmpleFibreAlt.ringKrullDim_red ℓ hpW, hdim, add_comm]
  have hle : fibreIdeal ℓ y ≤ W' := Ideal.map_mono hPW
  have hI := GeoNumTarget.isFieldIntersection_intNum (K := K) (ι := ι) ℓ
  have hnef := GeneratedNefF.proof (ZMod ℓ) K ι _ (fibreIdeal ℓ y) a hI hgen W' hW'proj hle
  have hgeo := geoNumStatement ι ℓ _ hI W 1 (fun _ => a) hW hpW hW'proj
  rw [hgeo]
  convert hnef using 2
  funext j
  fin_cases j
  rfl

end GlobalTheory.CompanionTheory.Ar.Giv

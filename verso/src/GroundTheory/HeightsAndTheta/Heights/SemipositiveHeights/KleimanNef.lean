import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.KleimanNefness.KleimanSt
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.GeoNum
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PNefAmpleFibre
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PSemiampleNef
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.ForSecondHalf

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
open GroundTheory.Heights₂.Heights.HilbertSamuel.NefAmpleFibreAlt

noncomputable section

namespace KleimanNef

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

/- English proof (translation)
Establish `: V.IsPrime` using `hV.1`. Use `⟨Ideal.map_isPrime_of_surjective (red_surjective p) (ker_red_le p hp), isMultiHomogIdeal_map _ hV.2.1, fun k => ?_⟩` and prove the remaining obligations. Take `⟨i, hi⟩` from `hV.2.2 k`. Use `⟨i, fun h => hi ?_⟩` and prove the remaining obligations. Establish `h' : red p (X ⟨k, i⟩ : MRing ι) ∈ V.map (red p)`.

Simplify `h` using `only [red, map_X]`. Conclude with `(mem_map_red_iff p hp _).1 h'`.
-/
theorem isMultiProjPrime_map_red (p : ℕ) {V : Ideal (MRing ι)} (hV : IsMultiProjPrime V)
    (hp : ((p : ℕ) : MRing ι) ∈ V) : IsMultiProjPrime (V.map (red p)) := by
  have : V.IsPrime := hV.1
  refine ⟨Ideal.map_isPrime_of_surjective (red_surjective p) (ker_red_le p hp),
    isMultiHomogIdeal_map _ hV.2.1, fun k => ?_⟩
  obtain ⟨i, hi⟩ := hV.2.2 k
  refine ⟨i, fun h => hi ?_⟩
  have h' : red p (X ⟨k, i⟩ : MRing ι) ∈ V.map (red p) := by
    simpa only [red, map_X] using h
  exact (mem_map_red_iff p hp _).1 h'

omit [Fintype K] [∀ k, Fintype (ι k)] in

/- English proof (translation)
Establish `hg` using `Submodule.IsPrincipal.generator_mem (W.comap (C : ℤ →+* MRing ι))`. Establish `hdvd : Submodule.IsPrincipal.generator (W.comap (C : ℤ →+* MRing ι)) ∣ ((charOf W : ℕ) : ℤ)` using `Int.dvd_natAbs.mpr dvd_rfl`. Establish `hmem : ((charOf W : ℕ) : ℤ) ∈ W.comap (C : ℤ →+* MRing ι)` using `Ideal.mem_of_dvd _ hdvd hg`. Rewrite `hmem` using `[Ideal.mem_comap, map_natCast]`. Conclude with `hmem`.
-/
theorem charOf_mem (W : Ideal (MRing ι)) : ((charOf W : ℕ) : MRing ι) ∈ W := by
  have hg := Submodule.IsPrincipal.generator_mem (W.comap (C : ℤ →+* MRing ι))
  have hdvd : Submodule.IsPrincipal.generator (W.comap (C : ℤ →+* MRing ι)) ∣
      ((charOf W : ℕ) : ℤ) := Int.dvd_natAbs.mpr dvd_rfl
  have hmem : ((charOf W : ℕ) : ℤ) ∈ W.comap (C : ℤ →+* MRing ι) :=
    Ideal.mem_of_dvd _ hdvd hg
  rw [Ideal.mem_comap, map_natCast] at hmem
  exact hmem

end KleimanNef

open KleimanNef in

/- English proof (translation)
Introduce `K _ ι _ V n a hV hchar hdim hnef`. Establish `: V.IsPrime` using `hV.1`. Use `set p := charOf V with hpdef`. Establish `: Fact p.Prime` using `⟨HilbertSamuel.SemiampleNefAlt.charOf_prime hchar⟩`. Establish `hpV : ((p : ℕ) : MRing ι) ∈ V` using `charOf_mem V`.

Set `I : IFamily (ZMod p) ι` to `fun V _ L => NumbersDVR.intNum (ZMod p) V L`. Establish `hI : IsFieldIntersection I` using `GeoNumTarget.isFieldIntersection_intNum p`. Establish `hGeo` using `GroundTheory.Heights₂.Heights.geoNumStatement ι p I hI`. Establish `hproj : IsProjVarF (V.map (red p)) n` using `⟨isMultiProjPrime_map_red p hV hpV, by rw [ringKrullDim_red p hpV, hdim]⟩`. Establish `hnefF : ∀ j, KH.NefOnF I (V.map (red p)) (a j)`.

Introduce `j W' hW' hle`. Use `set W := W'.comap (red p) with hWdef`. Establish `hmap : W.map (red p) = W'` using `Ideal.map_comap_of_surjective _ (red_surjective p) W'`. Establish `hVW : V ≤ W` using `Ideal.map_le_iff_le_comap.mp hle`. Establish `hpW : ((p : ℕ) : MRing ι) ∈ W` using `hVW hpV`.

Establish `hWm : IsMultiProjPrime W`. Take `⟨⟨hW'p, hW'h, hW'r⟩, -⟩` from `hW'`. Use `⟨Ideal.comap_isPrime _ W', isMultiHomogIdeal_comap _ hW'h, fun k => ?_⟩` and prove the remaining obligations. Take `⟨i, hi⟩` from `hW'r k`. Use `⟨i, ?_⟩` and prove the remaining obligations.

Rewrite using `[hWdef, Ideal.mem_comap, map_X]`. Conclude with `hi`. Establish `hdimW : ringKrullDim (MRing ι ⧸ W) = ((1 + Fintype.card K : ℕ) : WithBot ℕ∞)`. Rewrite using `[← ringKrullDim_red p hpW, hmap, hW'.2]`. Establish `hWp : IsProjVarF (W.map (red p)) 1`.

Rewrite using `[hmap]`. Conclude with `hW'`. Establish `h` using `hnef j W hWm hVW hdimW`. Rewrite `h` using `[hGeo W 1 _ hWm hpW hWp, hmap]`. Use `h using 2` and compare the differences between its conclusion and the goal.

Use function extensionality and compare the values at `i`. Use `fin_cases i`. Both sides reduce to the same expression. Establish `h` using `hF (ZMod p) K ι I (V.map (red p)) n a hI hproj hnefF`. Rewrite using `[hGeo V n a hV hpV hproj]`.

Conclude with `h`.
-/
theorem KleimanNef.proof (hF : KH.KleimanNefFStatement) : KH.KleimanNefIntersectionNonneg := by
  classical
  intro K _ ι _ V n a hV hchar hdim hnef
  have : V.IsPrime := hV.1
  set p := charOf V with hpdef
  have : Fact p.Prime := ⟨HilbertSamuel.SemiampleNefAlt.charOf_prime hchar⟩
  have hpV : ((p : ℕ) : MRing ι) ∈ V := charOf_mem V
  let I : IFamily (ZMod p) ι := fun V _ L => NumbersDVR.intNum (ZMod p) V L
  have hI : IsFieldIntersection I := GeoNumTarget.isFieldIntersection_intNum p
  have hGeo := GroundTheory.Heights₂.Heights.geoNumStatement ι p I hI
  have hproj : IsProjVarF (V.map (red p)) n :=
    ⟨isMultiProjPrime_map_red p hV hpV, by rw [ringKrullDim_red p hpV, hdim]⟩
  have hnefF : ∀ j, KH.NefOnF I (V.map (red p)) (a j) := by
    intro j W' hW' hle
    set W := W'.comap (red p) with hWdef
    have hmap : W.map (red p) = W' := Ideal.map_comap_of_surjective _ (red_surjective p) W'
    have hVW : V ≤ W := Ideal.map_le_iff_le_comap.mp hle
    have hpW : ((p : ℕ) : MRing ι) ∈ W := hVW hpV
    have hWm : IsMultiProjPrime W := by
      obtain ⟨⟨hW'p, hW'h, hW'r⟩, -⟩ := hW'
      refine ⟨Ideal.comap_isPrime _ W', isMultiHomogIdeal_comap _ hW'h, fun k => ?_⟩
      obtain ⟨i, hi⟩ := hW'r k
      refine ⟨i, ?_⟩
      rw [hWdef, Ideal.mem_comap, map_X]
      exact hi
    have hdimW : ringKrullDim (MRing ι ⧸ W) = ((1 + Fintype.card K : ℕ) : WithBot ℕ∞) := by
      rw [← ringKrullDim_red p hpW, hmap, hW'.2]
    have hWp : IsProjVarF (W.map (red p)) 1 := by
      rw [hmap]
      exact hW'
    have h := hnef j W hWm hVW hdimW
    rw [hGeo W 1 _ hWm hpW hWp, hmap] at h
    convert h using 2
    funext i
    fin_cases i
    rfl
  have h := hF (ZMod p) K ι I (V.map (red p)) n a hI hproj hnefF
  rw [hGeo V n a hV hpV hproj]
  exact h

end

end GroundTheory.Heights₂.Heights.ForSecondHalf

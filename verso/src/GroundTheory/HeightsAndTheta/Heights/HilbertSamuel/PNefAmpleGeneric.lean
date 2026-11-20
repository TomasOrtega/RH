import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsNefAmpleGeneric
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PNefOnGenericOfSemipos
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.ExistsLinearIndependentOfGenerates
import GroundTheory.HeightsAndTheta.Heights.Intersections.Statements
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.AssemblyBridgeFull
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PGenericFibProps
import GroundTheory.HeightsAndTheta.Heights.HeightComparison.IsMultiHomogIdealIff
import ReciprocityTheory.AnalyticForms.RegularLocalRings.IntToRat
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.KleimanNefness.AmpleSt
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.ChartRestriction.G.AI.I1

noncomputable section

namespace NefAmpleGeneric

attribute [local instance] MvPolynomial.algebraMvPolynomial

/- English proof (translation)
Take `⟨⟨hprime, hhom, hrel⟩, hdim⟩` from `hW`. Use `set φ : MRing ι →+* MRingOver ℚ ι := MvPolynomial.map (Int.castRingHom ℚ) with hφdef`. Use `set P := W.comap φ with hPdef`. Use `hprime` as an intermediate fact. Establish `hPp : P.IsPrime` using `Ideal.comap_isPrime φ W`.

Set `S : Submonoid (MRing ι)` to `(nonZeroDivisors ℤ).map (C (σ := Σ k, ι k))`. Establish `: IsLocalization S (MRingOver ℚ ι)` using `MvPolynomial.isLocalization (nonZeroDivisors ℤ) ℚ`. Establish `hφ : algebraMap (MRing ι) (MRingOver ℚ ι) = φ` using `by show MvPolynomial.map (algebraMap ℤ ℚ) = _`. Rewrite using `[RingHom.ext_int (algebraMap ℤ ℚ) (Int.castRingHom ℚ)]`. Establish `hmap : P.map φ = W`.

Establish `h` using `IsLocalization.map_under S (MRingOver ℚ ι) W`. Rewrite `h` using `[hφ]`. Then use the resulting hypothesis. Establish `hch : ∀ m : ℤ, (C m : MRing ι) ∈ P → m = 0`. Introduce `m hm`. Assume the negation of the conclusion as `h0`.

Establish `hu : IsUnit (φ (C m))`. Rewrite using `[hφdef, map_C]`. Conclude with `(isUnit_iff_ne_zero.mpr (by simpa using h0 : ((Int.castRingHom ℚ) m) ≠ 0)).map C`. Conclude with `hprime.ne_top (Ideal.eq_top_of_isUnit_mem _ hm hu)`. Establish `hWN : NumbersDVR.IsMultiProjPrime (K` using `K) W := (GroundTheory.Heights₂.Heights.Bridge.isMultiProjPrime_iff W).mpr ⟨hprime, hhom, hrel⟩`.

Establish `hPN : NumbersDVR.IsMultiProjPrime (K` using `K) P := by`. Use `⟨hPp, fun f hf b => ?_, fun k => ?_⟩` and prove the remaining obligations. Use `show φ _ ∈ W`. Rewrite using `[hφdef, ← NumbersDVR.weightedHomogeneousComponent_map]`. Conclude with `hWN.multiHomog _ hf b`.

Take `⟨i, hi⟩` from `hrel k`. Conclude with `⟨i, fun h => hi (by simpa [hPdef, hφdef] using h)⟩`. Take `⟨-, hhomP, hrelP⟩` from `(GroundTheory.Heights₂.Heights.Bridge.isMultiProjPrime_iff P).mp hPN`. Take `⟨-, -, hd⟩` from `ReciprocityTheory.AnForm.R.extQ_spec P hch`. Use `⟨⟨‹Nonempty K›, ⟨hPp, hhomP, hrelP⟩, ?_, ?_⟩, hmap⟩` and prove the remaining obligations.

Use extensionality with `m`. Simplify using `only [Ideal.mem_comap, Ideal.mem_bot]`. Conclude with `⟨hch m, fun h => by rw [h, map_zero]; exact P.zero_mem⟩`. Establish `hext : ReciprocityTheory.AnForm.R.extQ P = W` using `hmap`. Rewrite using `[← hd, hext, hdim, show d + 1 + Fintype.card K = (d + Fintype.card K) + 1 by omega, Nat.cast_succ]`.
-/
theorem isArithVar_comap_of_isProjVarF {K : Type} [Fintype K] [Nonempty K] {ι : K → Type}
    [∀ k, Fintype (ι k)] {W : Ideal (MRingOver ℚ ι)} {d : ℕ} (hW : IsProjVarF W d) :
    IsArithVar (W.comap (MvPolynomial.map (Int.castRingHom ℚ))) (d + 1) ∧
      (W.comap (MvPolynomial.map (Int.castRingHom ℚ))).map (MvPolynomial.map (Int.castRingHom ℚ)) = W := by
  classical
  obtain ⟨⟨hprime, hhom, hrel⟩, hdim⟩ := hW
  set φ : MRing ι →+* MRingOver ℚ ι := MvPolynomial.map (Int.castRingHom ℚ) with hφdef
  set P := W.comap φ with hPdef
  have := hprime
  have hPp : P.IsPrime := Ideal.comap_isPrime φ W
  let S : Submonoid (MRing ι) := (nonZeroDivisors ℤ).map (C (σ := Σ k, ι k))
  have : IsLocalization S (MRingOver ℚ ι) := MvPolynomial.isLocalization (nonZeroDivisors ℤ) ℚ
  have hφ : algebraMap (MRing ι) (MRingOver ℚ ι) = φ := by
    show MvPolynomial.map (algebraMap ℤ ℚ) = _
    rw [RingHom.ext_int (algebraMap ℤ ℚ) (Int.castRingHom ℚ)]
  have hmap : P.map φ = W := by
    have h := IsLocalization.map_under S (MRingOver ℚ ι) W
    rwa [hφ] at h
  have hch : ∀ m : ℤ, (C m : MRing ι) ∈ P → m = 0 := by
    intro m hm
    by_contra h0
    have hu : IsUnit (φ (C m)) := by
      rw [hφdef, map_C]
      exact (isUnit_iff_ne_zero.mpr (by simpa using h0 : ((Int.castRingHom ℚ) m) ≠ 0)).map C
    exact hprime.ne_top (Ideal.eq_top_of_isUnit_mem _ hm hu)
  have hWN : NumbersDVR.IsMultiProjPrime (K := K) W :=
    (GroundTheory.Heights₂.Heights.Bridge.isMultiProjPrime_iff W).mpr ⟨hprime, hhom, hrel⟩
  have hPN : NumbersDVR.IsMultiProjPrime (K := K) P := by
    refine ⟨hPp, fun f hf b => ?_, fun k => ?_⟩
    · show φ _ ∈ W
      rw [hφdef, ← NumbersDVR.weightedHomogeneousComponent_map]
      exact hWN.multiHomog _ hf b
    · obtain ⟨i, hi⟩ := hrel k
      exact ⟨i, fun h => hi (by simpa [hPdef, hφdef] using h)⟩
  obtain ⟨-, hhomP, hrelP⟩ := (GroundTheory.Heights₂.Heights.Bridge.isMultiProjPrime_iff P).mp hPN
  obtain ⟨-, -, hd⟩ := ReciprocityTheory.AnForm.R.extQ_spec P hch
  refine ⟨⟨‹Nonempty K›, ⟨hPp, hhomP, hrelP⟩, ?_, ?_⟩, hmap⟩
  · ext m
    simp only [Ideal.mem_comap, Ideal.mem_bot]
    exact ⟨hch m, fun h => by rw [h, map_zero]; exact P.zero_mem⟩
  · have hext : ReciprocityTheory.AnForm.R.extQ P = W := hmap
    rw [← hd, hext, hdim, show d + 1 + Fintype.card K = (d + Fintype.card K) + 1 by omega, Nat.cast_succ]

end NefAmpleGeneric

/- English proof (translation)
Introduce `K _ _ ι _ _ Ω _ _ y D M P0 b a hV hP0 hs hb ha`. Establish `: Nonempty K` using `hV.1`. Set `I : IFamily ℚ ι` to `fun V _ L => NumbersDVR.intNum ℚ V L`. Establish `hI : IsFieldIntersection I` using `NumbersDVR.IntNumIsFieldIntersection.full ℚ K ι`. Establish `hnef : KH.NefOnF I (KH.genIdeal y) M.a`.

Introduce `W hW hle`. Take `⟨hWar, hWmap⟩` from `NefAmpleGeneric.isArithVar_comap_of_isProjVarF hW`. Establish `hPW : mCoordIdeal y ≤ W.comap (MvPolynomial.map (Int.castRingHom ℚ))` using `Ideal.map_le_iff_le_comap.mp hle`. Establish `h0 : 0 ≤ geomDeg (W.comap (MvPolynomial.map (Int.castRingHom ℚ))) M 1` using `NefOnGenericOfSemipos.proof K ι _ P0 M hP0 hs _ hWar hPW`. Establish `hdeg` using `hDG K ι (W.comap (MvPolynomial.map (Int.castRingHom ℚ))) 1 ![M] hWar (fun j => by fin_cases j; exact hs.1)`.

Rewrite `hdeg` using `[hWmap]`. Establish `hpot : pot ![M] = fun (_ : Fin 1) z => Real.log (M.h z)`. Use function extensionality and compare the values at `j z`. Use `fin_cases j`. Both sides reduce to the same expression.

Establish `hL : (fun j => (![M] j).a) = ![M.a]`. Use function extensionality and compare the values at `j`. Use `fin_cases j`. Both sides reduce to the same expression. Rewrite `hdeg` using `[hpot, hL]`.

Establish `h1 : (0 : ℝ) ≤ (NumbersDVR.intNum ℚ W ![M.a] : ℝ)`. Rewrite using `[← hdeg]`. Conclude with `h0`. Use `show 0 ≤ NumbersDVR.intNum ℚ W ![M.a]`. Conclude with `h1` after adjusting the coercions.

Establish `h` using `hKA ℚ K ι I (KH.genIdeal y) D M.a b a hI (isProjVarF_map_of_isArithVar hV) hnef hb ha`. Rewrite `h` using `[← natCast_zsmul]`. Then use the resulting hypothesis.
-/
theorem NefAmpleGeneric.proof (hKA : KH.KAmpStatement)
    (hDG : GroundTheory.Heights₂.Heights.Inter.DegreeGeneric.Statement) : NefAmpleGeneric.Statement := by
  intro K _ _ ι _ _ Ω _ _ y D M P0 b a hV hP0 hs hb ha
  classical
  have : Nonempty K := hV.1
  let I : IFamily ℚ ι := fun V _ L => NumbersDVR.intNum ℚ V L
  have hI : IsFieldIntersection I := NumbersDVR.IntNumIsFieldIntersection.full ℚ K ι
  have hnef : KH.NefOnF I (KH.genIdeal y) M.a := by
    intro W hW hle
    obtain ⟨hWar, hWmap⟩ := NefAmpleGeneric.isArithVar_comap_of_isProjVarF hW
    have hPW : mCoordIdeal y ≤ W.comap (MvPolynomial.map (Int.castRingHom ℚ)) :=
      Ideal.map_le_iff_le_comap.mp hle
    have h0 : 0 ≤ geomDeg (W.comap (MvPolynomial.map (Int.castRingHom ℚ))) M 1 :=
      NefOnGenericOfSemipos.proof K ι _ P0 M hP0 hs _ hWar hPW
    have hdeg := hDG K ι (W.comap (MvPolynomial.map (Int.castRingHom ℚ))) 1 ![M] hWar (fun j => by fin_cases j; exact hs.1)
    rw [hWmap] at hdeg
    have hpot : pot ![M] = fun (_ : Fin 1) z => Real.log (M.h z) := by
      funext j z
      fin_cases j
      rfl
    have hL : (fun j => (![M] j).a) = ![M.a] := by
      funext j
      fin_cases j
      rfl
    rw [hpot, hL] at hdeg
    have h1 : (0 : ℝ) ≤ (NumbersDVR.intNum ℚ W ![M.a] : ℝ) := by
      rw [← hdeg]
      exact h0
    show 0 ≤ NumbersDVR.intNum ℚ W ![M.a]
    exact_mod_cast h1
  have h := hKA ℚ K ι I (KH.genIdeal y) D M.a b a hI (isProjVarF_map_of_isArithVar hV) hnef hb ha
  rwa [← natCast_zsmul] at h

end

end GroundTheory.Heights₂.Heights.HilbertSamuel

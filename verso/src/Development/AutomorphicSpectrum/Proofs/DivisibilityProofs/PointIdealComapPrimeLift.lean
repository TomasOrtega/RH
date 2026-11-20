import Mathlib
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.LocalAtPlaces
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsFlagIndependence
import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.ConstantsMonomialApproximation
import Development.WeilBound.CoreStatements.IdealCycleValues.LengthLocQuot
open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR GlobalTheory.CompanionTheory.Ar.Num GlobalTheory.CompanionTheory.Ar.Top GroundTheory.Heights₂.Heights.ModelLeaves
open ReciprocityTheory.ChartRestriction.G.Geo (HermLine IsSmoothHerm IsArithVar IsHorizontal mcPts mCoordIdeal IsIntersectionFamily IsIntersectionSystem IntersectionSystem ptsIntegral geoNum charOf recR arInt ChartBundle chartRing)

namespace GlobalTheory.CompanionTheory.Ar.Num

section ConstantsCorrespondence

variable {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω]
  {A : Type} [CommRing A] [Algebra A Ω]

/- English proof (translation)
Proceed by induction on `g using MvPolynomial.induction_on with`. Consider the case `C a => simp [pointConeMap, ReciprocityTheory.ChartRestriction.G.Geo.mConeMap]`. Consider the case `add p q hp hq => simp only [map_add, hp, hq]`. Consider the case `mul_X p i hp`. Simplify using `only [map_mul, hp, map_X]`.

Simplify using `[pointConeMap, ReciprocityTheory.ChartRestriction.G.Geo.mConeMap]`.
-/
theorem pointConeMap_map_intCast (y : (Σ k, ι k) → Ω) (g : MRing ι ℤ) :
    pointConeMap A y (MvPolynomial.map (Int.castRingHom A) g) = ReciprocityTheory.ChartRestriction.G.Geo.mConeMap y g := by
  induction g using MvPolynomial.induction_on with
  | C a => simp [pointConeMap, ReciprocityTheory.ChartRestriction.G.Geo.mConeMap]
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p i hp =>
    simp only [map_mul, hp, map_X]
    simp [pointConeMap, ReciprocityTheory.ChartRestriction.G.Geo.mConeMap]

/- English proof (translation)
Use extensionality with `g`. Rewrite using `[Ideal.mem_comap]`. Simplify using `only [pointIdeal, mCoordIdeal, RingHom.mem_ker, pointConeMap_map_intCast]`.
-/
theorem comap_pointIdeal_eq_mCoordIdeal (y : (Σ k, ι k) → Ω) :
    (pointIdeal A y).comap (MvPolynomial.map (Int.castRingHom A)) = mCoordIdeal y := by
  ext g
  rw [Ideal.mem_comap]
  simp only [pointIdeal, mCoordIdeal, RingHom.mem_ker, pointConeMap_map_intCast]

/- English proof (translation)
Establish `hs : MvPolynomial.map (Int.castRingHom A) (∏ k, X ⟨k, c k⟩ : MRing ι ℤ) = (∏ k, X ⟨k, c k⟩ : MRing ι A)`. Simplify using `[map_prod]`. Rewrite using `[hs]`. Use `set s : MRing ι A := ∏ k, X ⟨k, c k⟩ with hsdef`. Proceed by induction on `r using MvPolynomial.induction_on with`.

Consider the case `C a`. Take `⟨n, G, -, hG⟩` from `const_mul_chartMonomial_pow_form K ι Ω y A hA c a`. Use `⟨n, G, ?_⟩` and prove the remaining obligations. Rewrite using `[mul_comm]`. Conclude with `hG`.

Consider the case `add p q hp hq`. Take `⟨n, g, hg⟩` from `hp`. Take `⟨m, k, hk⟩` from `hq`. Use `⟨n + m, (∏ k, X ⟨k, c k⟩ : MRing ι ℤ) ^ m * g + (∏ k, X ⟨k, c k⟩ : MRing ι ℤ) ^ n * k, ?_⟩` and prove the remaining obligations. Establish `h` using `(pointIdeal A y).add_mem ((pointIdeal A y).mul_mem_left (s ^ m) hg) ((pointIdeal A y).mul_mem_left (s ^ n) hk)`.

Use `h using 1` and compare the differences between its conclusion and the goal. Simplify using `only [map_add, map_mul, map_pow, hs, ← hsdef]`. Expand and normalize the polynomial expressions, which then agree. Consider the case `mul_X p i hp`. Take `⟨n, g, hg⟩` from `hp`.

Use `⟨n, g * X i, ?_⟩` and prove the remaining obligations. Establish `h` using `(pointIdeal A y).mul_mem_right (X i) hg`. Use `h using 1` and compare the differences between its conclusion and the goal. Simplify using `only [map_mul, map_X]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem exists_pow_chartMonomial_mul_sub_map_mem {y : (Σ k, ι k) → Ω} (hA : HasConstants ℤ A y) (c : ∀ k, ι k)
    (r : MRing ι A) :
    ∃ (n : ℕ) (g : MRing ι ℤ),
      (MvPolynomial.map (Int.castRingHom A) (∏ k, X ⟨k, c k⟩ : MRing ι ℤ)) ^ n * r -
        MvPolynomial.map (Int.castRingHom A) g ∈ pointIdeal A y := by
  have hs : MvPolynomial.map (Int.castRingHom A) (∏ k, X ⟨k, c k⟩ : MRing ι ℤ) =
      (∏ k, X ⟨k, c k⟩ : MRing ι A) := by
    simp [map_prod]
  rw [hs]
  set s : MRing ι A := ∏ k, X ⟨k, c k⟩ with hsdef
  induction r using MvPolynomial.induction_on with
  | C a =>
    obtain ⟨n, G, -, hG⟩ := const_mul_chartMonomial_pow_form K ι Ω y A hA c a
    refine ⟨n, G, ?_⟩
    rw [mul_comm]
    exact hG
  | add p q hp hq =>
    obtain ⟨n, g, hg⟩ := hp
    obtain ⟨m, k, hk⟩ := hq
    refine ⟨n + m, (∏ k, X ⟨k, c k⟩ : MRing ι ℤ) ^ m * g + (∏ k, X ⟨k, c k⟩ : MRing ι ℤ) ^ n * k, ?_⟩
    have h := (pointIdeal A y).add_mem ((pointIdeal A y).mul_mem_left (s ^ m) hg)
      ((pointIdeal A y).mul_mem_left (s ^ n) hk)
    convert h using 1
    simp only [map_add, map_mul, map_pow, hs, ← hsdef]
    ring
  | mul_X p i hp =>
    obtain ⟨n, g, hg⟩ := hp
    refine ⟨n, g * X i, ?_⟩
    have h := (pointIdeal A y).mul_mem_right (X i) hg
    convert h using 1
    simp only [map_mul, map_X]
    ring

/- English proof (translation)
Use `choose c hc using hr`. Use `⟨c, fun h => ?_⟩` and prove the remaining obligations. Take `⟨k, -, hk⟩` from `(hW.prod_mem_iff).1 h`. Conclude with `hc k hk`.
-/
theorem exists_chart_not_mem {R : Type} [CommRing R] {W : Ideal (MRing ι R)} (hW : W.IsPrime) (hr : IsRelevant W) :
    ∃ c : ∀ k, ι k, (∏ k, X ⟨k, c k⟩ : MRing ι R) ∉ W := by
  choose c hc using hr
  refine ⟨c, fun h => ?_⟩
  obtain ⟨k, -, hk⟩ := (hW.prod_mem_iff).1 h
  exact hc k hk

/- English proof (translation)
Introduce `k`. Take `⟨i, hi⟩` from `hr k`. Conclude with `⟨i, by simpa [Ideal.mem_comap] using hi⟩`.
-/
theorem isRelevant_comap_map_intCast {W' : Ideal (MRing ι A)} (hr : IsRelevant W') :
    IsRelevant (W'.comap (MvPolynomial.map (Int.castRingHom A)) : Ideal (MRing ι ℤ)) := by
  intro k
  obtain ⟨i, hi⟩ := hr k
  exact ⟨i, by simpa [Ideal.mem_comap] using hi⟩

end ConstantsCorrespondence

/- English proof (translation)
Introduce `K _ _ ι _ Ω _ y A _ _ hA`. Establish `hcomap` using `comap_pointIdeal_eq_mCoordIdeal (A := A) y`. Use `⟨hcomap, ?_, ?_⟩` and prove the remaining obligations. Introduce `W hW hr hle`. Take `⟨c, hc⟩` from `exists_chart_not_mem hW hr`.

Establish `h` using `exists_pow_chartMonomial_mul_sub_map_mem hA c`. Take `⟨W', hW', hPW', hWc⟩` from `BaseChangeColon.Corr.exists_lift h hW (by rw [hcomap]; exact hle) hc`. Establish `hc' : MvPolynomial.map (Int.castRingHom A) (∏ k, X ⟨k, c k⟩ : MRing ι ℤ) ∉ W'`. Introduce `hm`. Apply `hc` to reduce the goal to its premises.

Rewrite using `[← hWc]`. Conclude with `hm`. Use `⟨W', ⟨hW', hPW', hWc⟩, ?_⟩` and prove the remaining obligations. Introduce and unpack `V ⟨hV, hPV, hVc⟩`. Establish `hcV : MvPolynomial.map (Int.castRingHom A) (∏ k, X ⟨k, c k⟩ : MRing ι ℤ) ∉ V`.

Introduce `hm`. Apply `hc` to reduce the goal to its premises. Rewrite using `[← hVc]`. Conclude with `hm`. Conclude with `le_antisymm (BaseChangeColon.Corr.mono h hW' hPV hPW' hc' (by rw [hVc, hWc])) (BaseChangeColon.Corr.mono h hV hPW' hPV hcV (by rw [hVc, hWc]))`.

Introduce `f W' hW' hr hPW'`. Choose the witnesses or unpack the hypotheses as in `⟨c, hc⟩ : ∃ c : ∀ k, ι k, MvPolynomial.map (Int.castRingHom A) (∏ k, X ⟨k, c k⟩ : MRing ι ℤ) ∉ W' := by`. Take `⟨c, hc⟩` from `exists_chart_not_mem hW' hr`. Conclude with `⟨c, by simpa [map_prod] using hc⟩`. Establish `h` using `exists_pow_chartMonomial_mul_sub_map_mem hA c`.

Use `set φ := MvPolynomial.map (σ := (Σ k, ι k)) (Int.castRingHom A) with hφ`. Use `set J : Ideal (MRing ι ℤ) := mCoordIdeal y ⊔ Ideal.span {f} with hJdef`. Establish `hJ : (pointIdeal A y).comap φ ≤ J` using `by rw [hcomap]; exact le_sup_left`. Establish `hJeq : pointIdeal A y ⊔ Ideal.span {φ f} = pointIdeal A y ⊔ J.map φ`. Rewrite using `[hJdef, Ideal.map_sup, Ideal.map_span, Set.image_singleton, ← sup_assoc]`.

Use `congr 1`. Use `(sup_eq_left.2 ?_).symm` and prove the remaining obligations. Rewrite using `[Ideal.map_le_iff_le_comap, hcomap]`. Establish `hmin` using `BaseChangeColon.Corr.minimal_iff h J hJ hW' hPW' hc`. Establish `hrel` using `isRelevant_comap_map_intCast hr`.

Establish `hWp : (W'.comap φ).IsPrime` using `Ideal.comap_isPrime φ W'`. Establish `hlen` using `BaseChangeColon.Corr.length_eq h J hJ W' (W'.comap φ) rfl hPW' hc`. Establish `hmin' : W' ∈ (pointIdeal A y ⊔ Ideal.span {φ f}).minimalPrimes ↔ W'.comap φ ∈ J.minimalPrimes`. Rewrite using `[hJeq]`. Conclude with `hmin`.

Establish `hlen' : Module.length (Localization.AtPrime W') (LocalizedModule W'.primeCompl (MRing ι A ⧸ (pointIdeal A y ⊔ Ideal.span {φ f}))) = Module.length (Localization.AtPrime (W'.comap φ)) (LocalizedModule (W'.comap φ).primeCompl (MRing ι ℤ ⧸ J))`. Rewrite using `[hJeq]`. Conclude with `hlen`. Unfold `divCycle`. Distinguish the cases in `hm : W'.comap φ ∈ J.minimalPrimes`.

Rewrite using `[dif_pos ⟨hmin'.2 hm, hr⟩, dif_pos ⟨hm, hrel⟩]`. Conclude with `congrArg (fun t : ℕ∞ => ((ENat.toNat t : ℕ) : ℤ)) hlen'`. Rewrite using `[dif_neg (fun hh => hm (hmin'.1 hh.1)), dif_neg (fun hh => hm hh.1)]`.
-/
theorem pl_corr : ∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] (y : (Σ k, ι k) → Ω) (A : Type) [CommRing A] [Algebra A Ω], HasConstants ℤ A y → (pointIdeal A y).comap (MvPolynomial.map (Int.castRingHom A)) = mCoordIdeal y ∧ (∀ W : Ideal (MRing ι ℤ), W.IsPrime → IsRelevant W → mCoordIdeal y ≤ W → ∃! W' : Ideal (MRing ι A), W'.IsPrime ∧ pointIdeal A y ≤ W' ∧ W'.comap (MvPolynomial.map (Int.castRingHom A)) = W) ∧ ∀ (f : MRing ι ℤ) (W' : Ideal (MRing ι A)), W'.IsPrime → IsRelevant W' → pointIdeal A y ≤ W' → divCycle (pointIdeal A y) (MvPolynomial.map (Int.castRingHom A) f) W' = divCycle (mCoordIdeal y) f (W'.comap (MvPolynomial.map (Int.castRingHom A))) := by
  intro K _ _ ι _ Ω _ y A _ _ hA
  have hcomap := comap_pointIdeal_eq_mCoordIdeal (A := A) y
  refine ⟨hcomap, ?_, ?_⟩
  · intro W hW hr hle
    obtain ⟨c, hc⟩ := exists_chart_not_mem hW hr
    have h := exists_pow_chartMonomial_mul_sub_map_mem hA c
    obtain ⟨W', hW', hPW', hWc⟩ := BaseChangeColon.Corr.exists_lift h hW (by rw [hcomap]; exact hle) hc
    have hc' : MvPolynomial.map (Int.castRingHom A) (∏ k, X ⟨k, c k⟩ : MRing ι ℤ) ∉ W' := by
      intro hm
      apply hc
      rw [← hWc]
      exact hm
    refine ⟨W', ⟨hW', hPW', hWc⟩, ?_⟩
    rintro V ⟨hV, hPV, hVc⟩
    have hcV : MvPolynomial.map (Int.castRingHom A) (∏ k, X ⟨k, c k⟩ : MRing ι ℤ) ∉ V := by
      intro hm
      apply hc
      rw [← hVc]
      exact hm
    exact le_antisymm (BaseChangeColon.Corr.mono h hW' hPV hPW' hc' (by rw [hVc, hWc]))
      (BaseChangeColon.Corr.mono h hV hPW' hPV hcV (by rw [hVc, hWc]))
  · intro f W' hW' hr hPW'
    obtain ⟨c, hc⟩ : ∃ c : ∀ k, ι k,
        MvPolynomial.map (Int.castRingHom A) (∏ k, X ⟨k, c k⟩ : MRing ι ℤ) ∉ W' := by
      obtain ⟨c, hc⟩ := exists_chart_not_mem hW' hr
      exact ⟨c, by simpa [map_prod] using hc⟩
    have h := exists_pow_chartMonomial_mul_sub_map_mem hA c
    set φ := MvPolynomial.map (σ := (Σ k, ι k)) (Int.castRingHom A) with hφ
    set J : Ideal (MRing ι ℤ) := mCoordIdeal y ⊔ Ideal.span {f} with hJdef
    have hJ : (pointIdeal A y).comap φ ≤ J := by rw [hcomap]; exact le_sup_left
    have hJeq : pointIdeal A y ⊔ Ideal.span {φ f} = pointIdeal A y ⊔ J.map φ := by
      rw [hJdef, Ideal.map_sup, Ideal.map_span, Set.image_singleton, ← sup_assoc]
      congr 1
      refine (sup_eq_left.2 ?_).symm
      rw [Ideal.map_le_iff_le_comap, hcomap]
    have hmin := BaseChangeColon.Corr.minimal_iff h J hJ hW' hPW' hc
    have hrel := isRelevant_comap_map_intCast hr
    have hWp : (W'.comap φ).IsPrime := Ideal.comap_isPrime φ W'
    have hlen := BaseChangeColon.Corr.length_eq h J hJ W' (W'.comap φ) rfl hPW' hc
    have hmin' : W' ∈ (pointIdeal A y ⊔ Ideal.span {φ f}).minimalPrimes ↔ W'.comap φ ∈ J.minimalPrimes := by
      rw [hJeq]
      exact hmin
    have hlen' : Module.length (Localization.AtPrime W')
        (LocalizedModule W'.primeCompl (MRing ι A ⧸ (pointIdeal A y ⊔ Ideal.span {φ f}))) =
        Module.length (Localization.AtPrime (W'.comap φ))
          (LocalizedModule (W'.comap φ).primeCompl (MRing ι ℤ ⧸ J)) := by
      rw [hJeq]
      exact hlen
    unfold divCycle
    by_cases hm : W'.comap φ ∈ J.minimalPrimes
    · rw [dif_pos ⟨hmin'.2 hm, hr⟩, dif_pos ⟨hm, hrel⟩]
      exact congrArg (fun t : ℕ∞ => ((ENat.toNat t : ℕ) : ℤ)) hlen'
    · rw [dif_neg (fun hh => hm (hmin'.1 hh.1)), dif_neg (fun hh => hm hh.1)]

end GlobalTheory.CompanionTheory.Ar.Num

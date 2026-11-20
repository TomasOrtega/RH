import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MultihomogeneousIdeals.ExistsUniqueStatement
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterDivSupp
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterRedF
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.IsMultiHomogIdealChain
import GroundTheory.HeightsAndTheta.Heights.Intersections.IsMultiHomogFirstCoordinate
import GroundTheory.HeightsAndTheta.Heights.Intersections.TableDegreeThreeBase
import GroundTheory.HeightsAndTheta.Heights.HeightComparison.IsMultiHomogIdealIff
import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.ContractRelevant
import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.PPFContractedDim
import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.PPFContracted
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4

namespace PointVertical

section Reduction

variable {K : Type} {ι : K → Type} (p : ℕ)

abbrev red : MRing ι →+* MRingOver (ZMod p) ι := MvPolynomial.map (Int.castRingHom (ZMod p))

/- English proof (translation)
The claim follows from `MvPolynomial.map_surjective _ (fun x => ZMod.intCast_surjective x)`.
-/
theorem red_surjective : Function.Surjective (red (ι := ι) p) :=
  MvPolynomial.map_surjective _ (fun x => ZMod.intCast_surjective x)

/- English proof (translation)
Rewrite using `[MvPolynomial.ker_map, ZMod.ker_intCastRingHom, Ideal.map_span, Set.image_singleton, Ideal.span_le, Set.singleton_subset_iff]`. Simplify using `using hp`.
-/
theorem ker_red_le {J : Ideal (MRing ι)} (hp : ((p : ℕ) : MRing ι) ∈ J) :
    RingHom.ker (red (ι := ι) p) ≤ J := by
  rw [MvPolynomial.ker_map, ZMod.ker_intCastRingHom, Ideal.map_span, Set.image_singleton, Ideal.span_le,
    Set.singleton_subset_iff]
  simpa using hp

/- English proof (translation)
Rewrite using `[← Ideal.mem_comap, Ideal.comap_map_of_surjective _ (red_surjective p), sup_eq_left.mpr]`. Rewrite using `[← RingHom.ker_eq_comap_bot]`. Conclude with `ker_red_le p hp`.
-/
theorem mem_map_red_iff {J : Ideal (MRing ι)} (hp : ((p : ℕ) : MRing ι) ∈ J) (g : MRing ι) :
    red p g ∈ J.map (red p) ↔ g ∈ J := by
  rw [← Ideal.mem_comap, Ideal.comap_map_of_surjective _ (red_surjective p), sup_eq_left.mpr]
  rw [← RingHom.ker_eq_comap_bot]
  exact ker_red_le p hp

/- English proof (translation)
Establish `e : J = RingHom.ker ((Ideal.Quotient.mk (J.map (red p))).comp (red p))`. Use extensionality with `g`. Rewrite using `[RingHom.mem_ker, RingHom.comp_apply, Ideal.Quotient.eq_zero_iff_mem, mem_map_red_iff p hp]`. Conclude with `(ringKrullDim_eq_of_ringEquiv ((Ideal.quotEquivOfEq e).trans (RingHom.quotientKerEquivOfSurjective (Ideal.Quotient.mk_surjective.comp (red_surjective p))))).symm`.
-/
theorem ringKrullDim_red {J : Ideal (MRing ι)} (hp : ((p : ℕ) : MRing ι) ∈ J) :
    ringKrullDim (MRingOver (ZMod p) ι ⧸ J.map (red p)) = ringKrullDim (MRing ι ⧸ J) := by
  have e : J = RingHom.ker ((Ideal.Quotient.mk (J.map (red p))).comp (red p)) := by
    ext g
    rw [RingHom.mem_ker, RingHom.comp_apply, Ideal.Quotient.eq_zero_iff_mem, mem_map_red_iff p hp]
  exact (ringKrullDim_eq_of_ringEquiv ((Ideal.quotEquivOfEq e).trans
    (RingHom.quotientKerEquivOfSurjective (Ideal.Quotient.mk_surjective.comp (red_surjective p))))).symm

/- English proof (translation)
Take `⟨hJp, ⟨S, hS, hJS⟩, hJr⟩` from `hJ`. Use `⟨Ideal.map_isPrime_of_surjective (red_surjective p) (ker_red_le p hp), ⟨red p '' S, ?_, by rw [hJS, Ideal.map_span]⟩, fun k => ?_⟩` and prove the remaining obligations. Introduce and unpack `_ ⟨f, hf, rfl⟩`. Take `⟨a, ha⟩` from `hS f hf`. Conclude with `⟨a, fun m hm => ha m (support_map_subset _ _ hm)⟩`.

Take `⟨i, hi⟩` from `hJr k`. Use `⟨i, fun h => hi ((mem_map_red_iff p hp _).mp ?_)⟩` and prove the remaining obligations. Rewrite using `[map_X]`. Conclude with `h`.
-/
theorem isMultiProjPrime_red [∀ k, Fintype (ι k)] {J : Ideal (MRing ι)} (hJ : IsMultiProjPrime J)
    (hp : ((p : ℕ) : MRing ι) ∈ J) : IsMultiProjPrime (J.map (red p)) := by
  obtain ⟨hJp, ⟨S, hS, hJS⟩, hJr⟩ := hJ
  refine ⟨Ideal.map_isPrime_of_surjective (red_surjective p) (ker_red_le p hp),
    ⟨red p '' S, ?_, by rw [hJS, Ideal.map_span]⟩, fun k => ?_⟩
  · rintro _ ⟨f, hf, rfl⟩
    obtain ⟨a, ha⟩ := hS f hf
    exact ⟨a, fun m hm => ha m (support_map_subset _ _ hm)⟩
  · obtain ⟨i, hi⟩ := hJr k
    refine ⟨i, fun h => hi ((mem_map_red_iff p hp _).mp ?_)⟩
    rw [map_X]
    exact h

variable {K' : Type} {ι' : K' → Type}

/- English proof (translation)
Establish `hp' : ((p : ℕ) : MRing ι) ∈ imageZ v W` using `by show rename v ((p : ℕ) : MRing ι) ∈ W`. Simplify using `using hp`. Use extensionality with `f`. Take `⟨g, rfl⟩` from `red_surjective p f`. Rewrite using `[mem_map_red_iff p hp' g]`.

Use `show rename v (red p g) ∈ W.map (red p) ↔ rename v g ∈ W`. Rewrite using `[← map_rename, mem_map_red_iff p hp]`.
-/
theorem imageVar_red [Fact p.Prime] (v : (Σ k, ι k) → (Σ k', ι' k')) {W : Ideal (MRing ι')}
    (hp : ((p : ℕ) : MRing ι') ∈ W) :
    imageVar (ZMod p) v (W.map (red p)) = (imageZ v W).map (red p) := by
  have hp' : ((p : ℕ) : MRing ι) ∈ imageZ v W := by
    show rename v ((p : ℕ) : MRing ι) ∈ W
    simpa using hp
  ext f
  obtain ⟨g, rfl⟩ := red_surjective p f
  rw [mem_map_red_iff p hp' g]
  show rename v (red p g) ∈ W.map (red p) ↔ rename v g ∈ W
  rw [← map_rename, mem_map_red_iff p hp]

/- English proof (translation)
Establish `ht'` using `(Bridge.isMultiHomog_iff t a).mpr ht`. Use `(Bridge.isMultiHomog_iff _ _).mp ?_` and prove the remaining obligations. Establish `e` using `FieldNumbers.ContractRelevant.rename_weightedHomogeneousComponent hv.2.2.1 hv.1 hv.2.1 a t`. Rewrite `e` using `[IsWeightedHomogeneous.weightedHomogeneousComponent_same ht']`. Rewrite using `[e]`.

Conclude with `weightedHomogeneousComponent_isWeightedHomogeneous _ _`.
-/
theorem isMultiHomog_rename [∀ k, Fintype (ι k)] [∀ k, Fintype (ι' k)] {κ : K → K'} {v : (Σ k, ι k) → (Σ k', ι' k')} (hv : IsBlockMap κ v)
    {t : MRing ι} {a : K → ℕ} (ht : IsMultiHomog t a) :
    IsMultiHomog (rename v t) (Function.extend κ a 0) := by
  classical
  have ht' := (Bridge.isMultiHomog_iff t a).mpr ht
  refine (Bridge.isMultiHomog_iff _ _).mp ?_
  have e := FieldNumbers.ContractRelevant.rename_weightedHomogeneousComponent hv.2.2.1 hv.1 hv.2.1 a t
  rw [IsWeightedHomogeneous.weightedHomogeneousComponent_same ht'] at e
  rw [e]
  exact weightedHomogeneousComponent_isWeightedHomogeneous _ _

/- English proof (translation)
Establish `h` using `FieldNumbers.ContractRelevant.isMultiProjPrime_comap_rename (R := ℤ) hv.2.2.1 hv.1 hv.2.1 (fun w hw => hv.2.2.2 w hw) ((Bridge.isMultiProjPrime_iff W).mpr hW)`. Conclude with `(Bridge.isMultiProjPrime_iff _).mp h`.
-/
theorem isMultiProjPrime_imageZ [∀ k, Fintype (ι k)] [∀ k, Fintype (ι' k)] {κ : K → K'} {v : (Σ k, ι k) → (Σ k', ι' k')} (hv : IsBlockMap κ v)
    {W : Ideal (MRing ι')} (hW : IsMultiProjPrime W) : IsMultiProjPrime (imageZ v W) := by
  classical
  have h := FieldNumbers.ContractRelevant.isMultiProjPrime_comap_rename (R := ℤ) hv.2.2.1 hv.1 hv.2.1
    (fun w hw => hv.2.2.2 w hw) ((Bridge.isMultiProjPrime_iff W).mpr hW)
  exact (Bridge.isMultiProjPrime_iff _).mp h

end Reduction

/- English proof (translation)
Use `hV.1` as an intermediate fact. Establish `hmh` using `(Bridge.isMultiHomogIdeal_iff V).mpr hV.2.1`. Conclude with `FieldNumbers.PFContracted.exists_ringKrullDim_eq (fun T q hq => FieldNumbers.PFContracted.killBlocks_mem_of_isMultiHomogIdeal hmh T hq) hV.2.2`.
-/
theorem exists_dim_F {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] (p : ℕ) [Fact p.Prime]
    (V : Ideal (MRingOver (ZMod p) ι)) (hV : IsMultiProjPrime V) :
    ∃ D : ℕ, Fintype.card K ≤ D ∧ ringKrullDim (MRingOver (ZMod p) ι ⧸ V) = D := by
  classical
  have := hV.1
  have hmh := (Bridge.isMultiHomogIdeal_iff V).mpr hV.2.1
  exact FieldNumbers.PFContracted.exists_ringKrullDim_eq
    (fun T q hq => FieldNumbers.PFContracted.killBlocks_mem_of_isMultiHomogIdeal hmh T hq) hV.2.2

/- English proof (translation)
Use `set p := charOf W with hpdef`. Establish `: Fact p.Prime` using `⟨hpr⟩`. Establish `hpW : ((p : ℕ) : MRing ι') ∈ W` using `ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.natCast_mem_of_charOf W`. Establish `hWp : IsProjVarF (W.map (red p)) n` using `⟨isMultiProjPrime_red p hWm hpW, by rw [ringKrullDim_red p hpW, hWd]⟩`. Establish `hImm : IsMultiProjPrime (imageZ v W)` using `isMultiProjPrime_imageZ hv hWm`.

Establish `hpI : ((p : ℕ) : MRing ι) ∈ imageZ v W` using `by show rename v ((p : ℕ) : MRing ι) ∈ W`. Simplify using `using hpW`. Establish `hVm` using `isMultiProjPrime_red p hImm hpI`. Take `⟨D, hKD, hD⟩` from `exists_dim_F p _ hVm`. Take `⟨-, ⟨hQp, -, -⟩, hQh, hQd⟩` from `hP`.

Use `hQp` as an intermediate fact. Establish `hle : imageZ v P' ≤ imageZ v W` using `Ideal.comap_mono hPW`. Establish `hpQ : ((p : ℕ) : MRing ι) ∉ imageZ v P'`. Introduce `h`. Establish `h2 : ((p : ℕ) : ℤ) ∈ (imageZ v P').comap (C : ℤ →+* MRing ι)`.

Rewrite using `[Ideal.mem_comap, map_natCast]`. Conclude with `h`. Rewrite `h2` using `[hQh, Ideal.mem_bot]`. Conclude with `hpr.ne_zero (by exact_mod_cast h2)`. Establish `hdim` using `krullDim_quot_add_one_le hle hpI hpQ`.

Rewrite `hdim` using `[← ringKrullDim_red p hpI, hD, hQd]`. Establish `hD' : D + 1 ≤ d + Fintype.card K` using `by exact_mod_cast hdim`. Establish `hVi : IsProjVarF (imageVar (ZMod p) v (W.map (red p))) (D - Fintype.card K)`. Rewrite using `[imageVar_red p v hpW]`. Use `⟨hVm, ?_⟩` and prove the remaining obligations.

Rewrite using `[hD, Nat.sub_add_cancel hKD]`. Take `⟨I, hI, -⟩` from `hR4 (ZMod p) K' ι'`. Rewrite using `[hGeo K' ι' p I hI W n _ hWm hpW hWp]`. Conclude with `hPC (ZMod p) K ι K' ι' I hI κ v _ n _ L hv hWp hVi (by omega)`.
-/
theorem geoNum_eq_zero
    (hGeo : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)], GeoNumStatement ι)
    (hR4 : ∀ (F : Type) [Field F] (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)],
      ExistsUniqueStatement F ι)
    (hPC : ∀ (F : Type) [Field F] (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)]
      (K' : Type) [Fintype K'] (ι' : K' → Type) [∀ k, Fintype (ι' k)], ProjContractStatement F ι ι')
    {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
    {K' : Type} [Fintype K'] {ι' : K' → Type} [∀ k, Fintype (ι' k)]
    {κ : K → K'} {v : (Σ k, ι k) → (Σ k', ι' k')} (hv : IsBlockMap κ v) {P' : Ideal (MRing ι')} {d n : ℕ}
    (hP : IsArithVar (imageZ v P') d) (hdn : d < n + 1) {W : Ideal (MRing ι')} (hPW : P' ≤ W)
    (hWm : IsMultiProjPrime W) (hpr : (charOf W).Prime)
    (hWd : ringKrullDim (MRing ι' ⧸ W) = ((n + Fintype.card K' : ℕ) : WithBot ℕ∞)) (L : Fin n → K → ℤ) :
    geoNum n W (fun j => pullDeg κ (L j)) = 0 := by
  set p := charOf W with hpdef
  have : Fact p.Prime := ⟨hpr⟩
  have hpW : ((p : ℕ) : MRing ι') ∈ W := ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.natCast_mem_of_charOf W
  have hWp : IsProjVarF (W.map (red p)) n := ⟨isMultiProjPrime_red p hWm hpW, by rw [ringKrullDim_red p hpW, hWd]⟩
  have hImm : IsMultiProjPrime (imageZ v W) := isMultiProjPrime_imageZ hv hWm
  have hpI : ((p : ℕ) : MRing ι) ∈ imageZ v W := by
    show rename v ((p : ℕ) : MRing ι) ∈ W
    simpa using hpW
  have hVm := isMultiProjPrime_red p hImm hpI
  obtain ⟨D, hKD, hD⟩ := exists_dim_F p _ hVm
  obtain ⟨-, ⟨hQp, -, -⟩, hQh, hQd⟩ := hP
  have := hQp
  have hle : imageZ v P' ≤ imageZ v W := Ideal.comap_mono hPW
  have hpQ : ((p : ℕ) : MRing ι) ∉ imageZ v P' := by
    intro h
    have h2 : ((p : ℕ) : ℤ) ∈ (imageZ v P').comap (C : ℤ →+* MRing ι) := by
      rw [Ideal.mem_comap, map_natCast]
      exact h
    rw [hQh, Ideal.mem_bot] at h2
    exact hpr.ne_zero (by exact_mod_cast h2)
  have hdim := krullDim_quot_add_one_le hle hpI hpQ
  rw [← ringKrullDim_red p hpI, hD, hQd] at hdim
  have hD' : D + 1 ≤ d + Fintype.card K := by exact_mod_cast hdim
  have hVi : IsProjVarF (imageVar (ZMod p) v (W.map (red p))) (D - Fintype.card K) := by
    rw [imageVar_red p v hpW]
    refine ⟨hVm, ?_⟩
    rw [hD, Nat.sub_add_cancel hKD]
  obtain ⟨I, hI, -⟩ := hR4 (ZMod p) K' ι'
  rw [hGeo K' ι' p I hI W n _ hWm hpW hWp]
  exact hPC (ZMod p) K ι K' ι' I hI κ v _ n _ L hv hWp hVi (by omega)

end PointVertical

open PointVertical in

/- English proof (translation)
Introduce `K _ ι _ K' _ ι' _ κ v P' d n L L' t a hv hP' hP hdn hL ht htQ`. Establish `hs : IsSectionOn P' (HermLine.sqMetric (ι` using `ι') (Function.extend κ a 0)) (rename v t) := ⟨Function.extend κ a 0, fun _ => rfl, isMultiHomog_rename hv ht, htQ⟩`. Unfold `vertR`. Use `finsum_mem_eq_zero_of_forall_eq_zero fun W hW => ?_` and prove the remaining obligations. Take `⟨-, hvert⟩` from `divSuppArith K' ι' P' n _ _ W hP' hs hW`.

Distinguish the cases in `hh : IsHorizontal W`. Simplify using `[hh]`. Take `⟨hWm, hpr, hWd⟩` from `hvert hh`. Establish `hPW : P' ≤ W` using `le_sup_left.trans hW.1.1.2`. Establish `e : (fun j => (L' j).a) = fun j => pullDeg κ (L j).a` using `funext fun j => (hL j).1`.

Simplify using `only [if_neg hh, e, geoNum_eq_zero hGeo hR4 hPC hv hP hdn hPW hWm hpr hWd (fun j => (L j).a)]`. Simplify using the standard rewrite rules.
-/
theorem ProjectivePointVertical.proof
    (hGeo : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)], GeoNumStatement ι)
    (hR4 : ∀ (F : Type) [Field F] (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)],
      ExistsUniqueStatement F ι)
    (hPC : ∀ (F : Type) [Field F] (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)]
      (K' : Type) [Fintype K'] (ι' : K' → Type) [∀ k, Fintype (ι' k)], ProjContractStatement F ι ι') :
    ProjectivePointVertical.Statement := by
  intro K _ ι _ K' _ ι' _ κ v P' d n L L' t a hv hP' hP hdn hL ht htQ
  classical
  have hs : IsSectionOn P' (HermLine.sqMetric (ι := ι') (Function.extend κ a 0)) (rename v t) :=
    ⟨Function.extend κ a 0, fun _ => rfl, isMultiHomog_rename hv ht, htQ⟩
  unfold vertR
  refine finsum_mem_eq_zero_of_forall_eq_zero fun W hW => ?_
  obtain ⟨-, hvert⟩ := divSuppArith K' ι' P' n _ _ W hP' hs hW
  by_cases hh : IsHorizontal W
  · simp [hh]
  · obtain ⟨hWm, hpr, hWd⟩ := hvert hh
    have hPW : P' ≤ W := le_sup_left.trans hW.1.1.2
    have e : (fun j => (L' j).a) = fun j => pullDeg κ (L j).a := funext fun j => (hL j).1
    simp only [if_neg hh, e, geoNum_eq_zero hGeo hR4 hPC hv hP hdn hPW hWm hpr hWd (fun j => (L j).a)]
    simp

end GroundTheory.Heights₂.Heights.Inter

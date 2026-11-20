import Mathlib

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum NumberField

namespace GroundTheory.Global

section Residue

variable {R : Type*} [CommRing R] [IsDedekindDomain R] {K : Type*} [Field K] [Algebra R K]
  [IsFractionRing R K] (v : HeightOneSpectrum R)

/- English proof (translation)
Rewrite using `[IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, adicCompletionIntegers.isUnit_iff_valued_eq_one, algebraMap_adicCompletionIntegers_apply, valuedAdicCompletion_eq_valuation', valuation_eq_one_iff_notMem, not_not]`.
-/
theorem algebraMap_mem_maximalIdeal_adicCompletionIntegers_iff (r : R) :
    algebraMap R (v.adicCompletionIntegers K) r ∈
        IsLocalRing.maximalIdeal (v.adicCompletionIntegers K) ↔ r ∈ v.asIdeal := by
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff,
    adicCompletionIntegers.isUnit_iff_valued_eq_one, algebraMap_adicCompletionIntegers_apply,
    valuedAdicCompletion_eq_valuation', valuation_eq_one_iff_notMem, not_not]

/- English proof (translation)
Establish `hnhds : {y : v.adicCompletion K | Valued.v (y - (x : v.adicCompletion K)) < 1} ∈ nhds (x : v.adicCompletion K)` using `Valued.mem_nhds.2 ⟨1, fun y hy ↦ by`. Simplify `hy⟩` using `[Valuation.restrict_lt_one_iff]`. Take `⟨k, hk⟩` from `(denseRange_algebraMap (K := K) v).mem_nhds hnhds`. Establish `hk' : Valued.v ((x : v.adicCompletion K) - (k : v.adicCompletion K)) < 1`. Rewrite using `[Valuation.map_sub_swap]`.

Conclude with `hk`. Establish `hk1 : v.valuation K k ≤ 1`. Rewrite using `[← valuedAdicCompletion_eq_valuation']`. Establish `: (k : v.adicCompletion K) = (x : v.adicCompletion K) - ((x : v.adicCompletion K) - (k : v.adicCompletion K))` using `by ring`. Rewrite using `[this]`.

Conclude with `(Valuation.map_sub _ _ _).trans (max_le x.2 hk'.le)`. Take `⟨r, hr⟩` from `exists_valuation_sub_lt_of_integer v hk1 1`. Use `⟨r, ?_⟩` and prove the remaining obligations. Rewrite using `[IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, adicCompletionIntegers.isUnit_iff_valued_eq_one]`. Use `ne_of_lt ?_` and prove the remaining obligations.

Establish `hr' : Valued.v (algebraMap K (v.adicCompletion K) (k - algebraMap R K r)) < 1`. Rewrite `hr` using `[Valuation.map_sub_swap]`. Use `valuedAdicCompletion_eq_valuation' (R := R) v (k - algebraMap R K r)` as an intermediate fact. Conclude with `this.trans_lt (by simpa using hr)`. Establish `: ((x - algebraMap R (v.adicCompletionIntegers K) r : v.adicCompletionIntegers K) : v.adicCompletion K) = ((x : v.adicCompletion K) - (k : v.adicCompletion K)) + algebraMap K (v.adicCompletion K) (k - algebraMap R K r)`.

Rewrite using `[map_sub]`. Simplify using `[algebraMap_adicCompletion]`. Rewrite using `[this]`. Conclude with `Valuation.map_add_lt _ hk' hr'`.
-/
theorem exists_algebraMap_sub_mem_maximalIdeal (x : v.adicCompletionIntegers K) :
    ∃ r : R, x - algebraMap R (v.adicCompletionIntegers K) r ∈
      IsLocalRing.maximalIdeal (v.adicCompletionIntegers K) := by

  have hnhds : {y : v.adicCompletion K | Valued.v (y - (x : v.adicCompletion K)) < 1} ∈
      nhds (x : v.adicCompletion K) :=
    Valued.mem_nhds.2 ⟨1, fun y hy ↦ by
      simpa [Valuation.restrict_lt_one_iff] using hy⟩
  obtain ⟨k, hk⟩ := (denseRange_algebraMap (K := K) v).mem_nhds hnhds
  have hk' : Valued.v ((x : v.adicCompletion K) - (k : v.adicCompletion K)) < 1 := by
    rw [Valuation.map_sub_swap]; exact hk

  have hk1 : v.valuation K k ≤ 1 := by
    rw [← valuedAdicCompletion_eq_valuation']
    have : (k : v.adicCompletion K) = (x : v.adicCompletion K) -
        ((x : v.adicCompletion K) - (k : v.adicCompletion K)) := by ring
    rw [this]
    exact (Valuation.map_sub _ _ _).trans (max_le x.2 hk'.le)
  obtain ⟨r, hr⟩ := exists_valuation_sub_lt_of_integer v hk1 1
  refine ⟨r, ?_⟩
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff,
    adicCompletionIntegers.isUnit_iff_valued_eq_one]
  refine ne_of_lt ?_
  have hr' : Valued.v (algebraMap K (v.adicCompletion K) (k - algebraMap R K r)) < 1 := by
    rw [Valuation.map_sub_swap] at hr
    have := valuedAdicCompletion_eq_valuation' (R := R) v (k - algebraMap R K r)
    exact this.trans_lt (by simpa using hr)
  have : ((x - algebraMap R (v.adicCompletionIntegers K) r : v.adicCompletionIntegers K) :
      v.adicCompletion K) = ((x : v.adicCompletion K) - (k : v.adicCompletion K)) +
        algebraMap K (v.adicCompletion K) (k - algebraMap R K r) := by
    rw [map_sub]
    simp [algebraMap_adicCompletion]
  rw [this]
  exact Valuation.map_add_lt _ hk' hr'

noncomputable def toResidueFieldAdicCompletionIntegers :
    R →+* IsLocalRing.ResidueField (v.adicCompletionIntegers K) :=
  (IsLocalRing.residue _).comp (algebraMap R (v.adicCompletionIntegers K))

/- English proof (translation)
Use extensionality with `r`. Rewrite using `[RingHom.mem_ker, toResidueFieldAdicCompletionIntegers, RingHom.comp_apply, IsLocalRing.residue_eq_zero_iff, algebraMap_mem_maximalIdeal_adicCompletionIntegers_iff]`.
-/
theorem ker_toResidueFieldAdicCompletionIntegers :
    RingHom.ker (toResidueFieldAdicCompletionIntegers (K := K) v) = v.asIdeal := by
  ext r
  rw [RingHom.mem_ker, toResidueFieldAdicCompletionIntegers, RingHom.comp_apply,
    IsLocalRing.residue_eq_zero_iff, algebraMap_mem_maximalIdeal_adicCompletionIntegers_iff]

/- English proof (translation)
Introduce `y`. Take `⟨x, rfl⟩` from `IsLocalRing.residue_surjective y`. Take `⟨r, hr⟩` from `exists_algebraMap_sub_mem_maximalIdeal v x`. Conclude with `⟨r, (Ideal.Quotient.eq.2 hr).symm⟩`.
-/
theorem toResidueFieldAdicCompletionIntegers_surjective :
    Function.Surjective (toResidueFieldAdicCompletionIntegers (K := K) v) := by
  intro y
  obtain ⟨x, rfl⟩ := IsLocalRing.residue_surjective y
  obtain ⟨r, hr⟩ := exists_algebraMap_sub_mem_maximalIdeal v x
  exact ⟨r, (Ideal.Quotient.eq.2 hr).symm⟩

noncomputable def residueFieldEquiv :
    (R ⧸ v.asIdeal) ≃+* IsLocalRing.ResidueField (v.adicCompletionIntegers K) :=
  (Ideal.quotEquivOfEq (ker_toResidueFieldAdicCompletionIntegers v).symm).trans
    (RingHom.quotientKerEquivOfSurjective (toResidueFieldAdicCompletionIntegers_surjective v))

@[simp]
/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem residueFieldEquiv_mk (r : R) :
    residueFieldEquiv (K := K) v (Ideal.Quotient.mk v.asIdeal r) =
      IsLocalRing.residue _ (algebraMap R (v.adicCompletionIntegers K) r) :=
  rfl

end Residue

section NumberField

variable {K : Type*} [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))

instance : Finite (IsLocalRing.ResidueField (v.adicCompletionIntegers K)) :=
  haveI := Ideal.finiteQuotientOfFreeOfNeBot v.asIdeal v.ne_bot
  Finite.of_equiv _ (residueFieldEquiv v).toEquiv

/- English proof (translation)
Rewrite using `[Ideal.absNorm_apply, Submodule.cardQuot_apply]`. Conclude with `(Nat.card_congr (residueFieldEquiv v).toEquiv).symm`.
-/
theorem natCard_residueField_adicCompletionIntegers :
    Nat.card (IsLocalRing.ResidueField (v.adicCompletionIntegers K)) =
      Ideal.absNorm v.asIdeal := by
  rw [Ideal.absNorm_apply, Submodule.cardQuot_apply]
  exact (Nat.card_congr (residueFieldEquiv v).toEquiv).symm

end NumberField

section Topology

variable {K : Type*} [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))

/- English proof (translation)
The claim follows from `Valued.isOpen_valuationSubring _`.
-/
theorem isOpen_adicCompletionIntegers :
    IsOpen (v.adicCompletionIntegers K : Set (v.adicCompletion K)) :=
  Valued.isOpen_valuationSubring _

/- English proof (translation)
The claim follows from `(Valued.isClopen_integer (v.adicCompletion K)).isClosed`.
-/
theorem isClosed_adicCompletionIntegers :
    IsClosed (v.adicCompletionIntegers K : Set (v.adicCompletion K)) :=
  (Valued.isClopen_integer (v.adicCompletion K)).isClosed

/- English proof (translation)
Establish `: CompleteSpace (Valued.integer (v.adicCompletion K))` using `(isClosed_adicCompletionIntegers v).completeSpace_coe`. Establish `: IsDiscreteValuationRing (Valued.integer (v.adicCompletion K))` using `inferInstanceAs (IsDiscreteValuationRing (v.adicCompletionIntegers K))`. Establish `: Finite (Valued.ResidueField (v.adicCompletion K))` using `inferInstanceAs (Finite (IsLocalRing.ResidueField (v.adicCompletionIntegers K)))`. Establish `h : CompactSpace (Valued.integer (v.adicCompletion K))` using `Valued.integer.compactSpace_iff_completeSpace_and_isDiscreteValuationRing_and_finite_residueField.2 ⟨inferInstance, inferInstance, inferInstance⟩`. Conclude with `isCompact_iff_compactSpace.2 h`.
-/
theorem isCompact_adicCompletionIntegers :
    IsCompact (v.adicCompletionIntegers K : Set (v.adicCompletion K)) := by
  have : CompleteSpace (Valued.integer (v.adicCompletion K)) :=
    (isClosed_adicCompletionIntegers v).completeSpace_coe
  have : IsDiscreteValuationRing (Valued.integer (v.adicCompletion K)) :=
    inferInstanceAs (IsDiscreteValuationRing (v.adicCompletionIntegers K))
  have : Finite (Valued.ResidueField (v.adicCompletion K)) :=
    inferInstanceAs (Finite (IsLocalRing.ResidueField (v.adicCompletionIntegers K)))
  have h : CompactSpace (Valued.integer (v.adicCompletion K)) :=
    Valued.integer.compactSpace_iff_completeSpace_and_isDiscreteValuationRing_and_finite_residueField.2
      ⟨inferInstance, inferInstance, inferInstance⟩
  exact isCompact_iff_compactSpace.2 h

instance : CompactSpace (v.adicCompletionIntegers K) :=
  isCompact_iff_compactSpace.1 (isCompact_adicCompletionIntegers v)

instance : LocallyCompactSpace (v.adicCompletion K) :=
  (isCompact_adicCompletionIntegers v).locallyCompactSpace_of_mem_nhds_of_addGroup
    ((isOpen_adicCompletionIntegers v).mem_nhds (v.adicCompletionIntegers K).zero_mem)

instance : CompleteSpace (v.adicCompletionIntegers K) :=
  (isClosed_adicCompletionIntegers v).completeSpace_coe

end Topology

end GroundTheory.Global

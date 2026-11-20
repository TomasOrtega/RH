import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.StatementsGrassFibreDegree
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PGrassLinesProj
import GroundTheory.HeightsAndTheta.Heights.Intersections.ConservationDegreeFormOfExistence
import GroundTheory.HeightsAndTheta.Heights.HeightComparison.GeoNum
import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.IntNumRelabel
import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.StatementsExamples
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MultihomogeneousIdeals.InhDivCycleOfSuppEmpty
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I2 MvPolynomial

noncomputable section

namespace GrassmannianFibreDegree

variable (n p : ℕ) [Fact p.Prime]

/- English proof (translation)
The claim follows from `(Bridge.GeoNum.ker_red p).symm`.
-/
theorem span_eq_ker :
    (Ideal.span {C (p : ℤ)} : Ideal (MRing (plBlocks 1 1 n))) =
      RingHom.ker (Bridge.GeoNum.red (ι := plBlocks 1 1 n) p) :=
  (Bridge.GeoNum.ker_red p).symm

/- English proof (translation)
Rewrite using `[span_eq_ker]`. Conclude with `RingHom.ker_isPrime _`.
-/
theorem isPrime : (Ideal.span {C (p : ℤ)} : Ideal (MRing (plBlocks 1 1 n))).IsPrime := by
  rw [span_eq_ker]
  exact RingHom.ker_isPrime _

/- English proof (translation)
Introduce `k`. Use `⟨plAnchor 1 n, ?_⟩` and prove the remaining obligations. Rewrite using `[span_eq_ker, RingHom.mem_ker, Bridge.GeoNum.red, map_X]`. Conclude with `X_ne_zero _`.
-/
theorem isRelevant : IsRelevant (Ideal.span {C (p : ℤ)} : Ideal (MRing (plBlocks 1 1 n))) := by
  intro k
  refine ⟨plAnchor 1 n, ?_⟩
  rw [span_eq_ker, RingHom.mem_ker, Bridge.GeoNum.red, map_X]
  exact X_ne_zero _

/- English proof (translation)
Use `isPrime n p` as an intermediate fact. Use extensionality with `W`. Simplify using `only [divSupp, bot_sup_eq, Ideal.minimalPrimes_eq_subsingleton_self, Set.mem_ofPred_eq, Set.mem_singleton_iff]`. Prove the components needed by the constructor for the conclusion. Conclude with `fun h => h.1`.

Introduce and unpack `rfl`. Conclude with `⟨rfl, isRelevant n p⟩`.
-/
theorem divSupp_eq :
    divSupp (⊥ : Ideal (MRing (plBlocks 1 1 n))) (C (p : ℤ)) = {Ideal.span {C (p : ℤ)}} := by
  have := isPrime n p
  ext W
  simp only [divSupp, bot_sup_eq, Ideal.minimalPrimes_eq_subsingleton_self, Set.mem_ofPred_eq,
    Set.mem_singleton_iff]
  constructor
  · exact fun h => h.1
  · rintro rfl
    exact ⟨rfl, isRelevant n p⟩

/- English proof (translation)
Rewrite using `[span_eq_ker, ringKrullDim_eq_of_ringEquiv (RingHom.quotientKerEquivOfSurjective (Bridge.GeoNum.red_surjective p)), MvPolynomial.ringKrullDim_of_isNoetherianRing, ringKrullDim_eq_zero_of_field, zero_add]`. Establish `hc : Nat.card ((_ : Fin 1) × PlIdx 1 n) = n + 1`. Rewrite using `[Nat.card_eq_fintype_card, Fintype.card_sigma]`. Simplify using the standard rewrite rules. Use linear arithmetic over natural numbers and integers.

Rewrite using `[hc, Fintype.card_fin]`.
-/
theorem ringKrullDim_quot :
    ringKrullDim (MRing (plBlocks 1 1 n) ⧸ (Ideal.span {C (p : ℤ)} : Ideal (MRing (plBlocks 1 1 n)))) =
      ((n + Fintype.card (Fin 1) : ℕ) : WithBot ℕ∞) := by
  rw [span_eq_ker, ringKrullDim_eq_of_ringEquiv
      (RingHom.quotientKerEquivOfSurjective (Bridge.GeoNum.red_surjective p)),
    MvPolynomial.ringKrullDim_of_isNoetherianRing, ringKrullDim_eq_zero_of_field, zero_add]
  have hc : Nat.card ((_ : Fin 1) × PlIdx 1 n) = n + 1 := by
    rw [Nat.card_eq_fintype_card, Fintype.card_sigma]
    simp
    omega
  rw [hc, Fintype.card_fin]

def coordEquiv : (Σ _ : Unit, Fin (n + 1)) ≃ (Σ _ : Fin 1, PlIdx 1 n) :=
  Equiv.ofBijective (GrassmannianLinesProjective.coordMap n)
    ⟨(GrassmannianLinesProjective.isBlockMap n).2.1, GrassmannianLinesProjective.coordMap_surjective n⟩

/- English proof (translation)
Establish `h` using `FieldNumbers.Relabel.intNum_map_rename (F := ZMod p) (Equiv.ofUnique Unit (Fin 1)) (coordEquiv n) (fun _ => Subsingleton.elim _ _) (⊥ : Ideal (NumbersDVR.MRing (FieldNumbers.ProjIdx n) (ZMod p))) (fun _ : Fin n => fun _ : Fin 1 => (1 : ℤ))`. Rewrite `h` using `[Ideal.map_bot]`. Rewrite using `[h]`. Conclude with `FieldNumbers.intNum_projectiveSpace (ZMod p) n`.
-/
theorem intNum_bot :
    NumbersDVR.intNum (ZMod p) (⊥ : Ideal (NumbersDVR.MRing (plBlocks 1 1 n) (ZMod p)))
      (fun _ : Fin n => fun _ : Fin 1 => (1 : ℤ)) = 1 := by
  have h := FieldNumbers.Relabel.intNum_map_rename (F := ZMod p) (Equiv.ofUnique Unit (Fin 1))
    (coordEquiv n) (fun _ => Subsingleton.elim _ _)
    (⊥ : Ideal (NumbersDVR.MRing (FieldNumbers.ProjIdx n) (ZMod p)))
    (fun _ : Fin n => fun _ : Fin 1 => (1 : ℤ))
  rw [Ideal.map_bot] at h
  rw [h]
  exact FieldNumbers.intNum_projectiveSpace (ZMod p) n

/- English proof (translation)
Use `isPrime n p` as an intermediate fact. Establish `hV : IsMultiProjPrime (Ideal.span {C (p : ℤ)} : Ideal (MRing (plBlocks 1 1 n)))` using `⟨isPrime n p, ⟨{C (p : ℤ)}, fun f hf => ⟨0, by`. Rewrite using `[Set.mem_singleton_iff.mp hf]`. Conclude with `Inter.Conservation.isMultiHomog_C _⟩, rfl⟩, isRelevant n p⟩`. Rewrite using `[← Bridge.intNum_map_eq_geoNum p n _ hV (Ideal.mem_span_singleton_self _) (ringKrullDim_quot n p)]`.

Establish `hb : (Ideal.span {C (p : ℤ)} : Ideal (MRing (plBlocks 1 1 n))).map (MvPolynomial.map (Int.castRingHom (ZMod p))) = ⊥` using `(Ideal.map_eq_bot_iff_le_ker _).mpr (span_eq_ker n p).le`. Rewrite using `[hb]`. Conclude with `intNum_bot n p`.
-/
theorem geoNum_span :
    geoNum n (Ideal.span {C (p : ℤ)} : Ideal (MRing (plBlocks 1 1 n)))
      (fun _ : Fin n => fun _ : Fin 1 => (1 : ℤ)) = 1 := by
  have := isPrime n p
  have hV : IsMultiProjPrime (Ideal.span {C (p : ℤ)} : Ideal (MRing (plBlocks 1 1 n))) :=
    ⟨isPrime n p, ⟨{C (p : ℤ)}, fun f hf => ⟨0, by
      rw [Set.mem_singleton_iff.mp hf]
      exact Inter.Conservation.isMultiHomog_C _⟩, rfl⟩, isRelevant n p⟩
  rw [← Bridge.intNum_map_eq_geoNum p n _ hV (Ideal.mem_span_singleton_self _) (ringKrullDim_quot n p)]
  have hb : (Ideal.span {C (p : ℤ)} : Ideal (MRing (plBlocks 1 1 n))).map
      (MvPolynomial.map (Int.castRingHom (ZMod p))) = ⊥ :=
    (Ideal.map_eq_bot_iff_le_ker _).mpr (span_eq_ker n p).le
  rw [hb]
  exact intNum_bot n p

end GrassmannianFibreDegree

open GrassmannianFibreDegree in

/- English proof (translation)
Introduce `n p hp`. Establish `: Fact p.Prime` using `⟨hp⟩`. Use `isPrime n p` as an intermediate fact. Establish `hW : (Ideal.span {C (p : ℤ)} : Ideal (MRing (plBlocks 1 1 n))) ∈ divSupp (⊥ : Ideal (MRing (plBlocks 1 1 n))) (C (p : ℤ))`. Rewrite using `[divSupp_eq]`.

Both sides reduce to the same expression. Establish `hg : geoNum n (Ideal.span {C (p : ℤ)} : Ideal (MRing (plBlocks 1 1 n))) (fun j => ((fun _ : Fin n => fsMulti (plBlocks 1 1 n)) j).a) = 1` using `geoNum_span n p`. Rewrite using `[GrassmannianLinesProjective.grassIdeal_eq_bot]`. Unfold `vertR`. Rewrite using `[divSupp_eq, finsum_mem_singleton, if_neg (Inter.Conservation.not_horizontal hp hW), Inter.Conservation.charOf_eq hp hW, bot_sup_eq, ReciprocityTheory.ChartRestriction.G.AI.I1.inh_multAt_self, hg]`.

Simplify using the standard rewrite rules.
-/
theorem GrassFibreDegree.proof : GrassFibreDegree.Statement := by
  intro n p hp
  have : Fact p.Prime := ⟨hp⟩
  have := isPrime n p
  have hW : (Ideal.span {C (p : ℤ)} : Ideal (MRing (plBlocks 1 1 n))) ∈
      divSupp (⊥ : Ideal (MRing (plBlocks 1 1 n))) (C (p : ℤ)) := by
    rw [divSupp_eq]
    rfl
  have hg : geoNum n (Ideal.span {C (p : ℤ)} : Ideal (MRing (plBlocks 1 1 n)))
      (fun j => ((fun _ : Fin n => fsMulti (plBlocks 1 1 n)) j).a) = 1 :=
    geoNum_span n p
  rw [GrassmannianLinesProjective.grassIdeal_eq_bot]
  unfold vertR
  rw [divSupp_eq, finsum_mem_singleton, if_neg (Inter.Conservation.not_horizontal hp hW),
    Inter.Conservation.charOf_eq hp hW, bot_sup_eq, ReciprocityTheory.ChartRestriction.G.AI.I1.inh_multAt_self, hg]
  simp

end

end GroundTheory.Heights₂.Heights

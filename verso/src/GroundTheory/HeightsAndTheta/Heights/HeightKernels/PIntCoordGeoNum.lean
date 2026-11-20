import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.StatementsIntCoordGeoNum
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.ChartRestriction.G.Geo MvPolynomial

noncomputable section

namespace IntegralCoordGeometricNumber

variable {T T₂ : Type} [Fintype T] [DecidableEq T] [Fintype T₂] [DecidableEq T₂]

def substR (R : Type) [CommRing R] (A : Matrix T T₂ ℤ) :
    MRingOver R (dualBlocks T₂) →ₐ[R] MRingOver R (dualBlocks T) :=
  aeval fun p => ∑ t, C ((A t p.2 : ℤ) : R) * X (⟨(), t⟩ : Σ k : Unit, dualBlocks T k)

omit [Fintype T₂] [DecidableEq T] [DecidableEq T₂] in

/- English proof (translation)
Replace the relevant objects with their definitions. Simplify using the standard rewrite rules.
-/
theorem substR_int (A : Matrix T T₂ ℤ) : substR ℤ A = intCoordSubst A := by
  unfold substR intCoordSubst
  simp

omit [DecidableEq T₂] in

/- English proof (translation)
Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. Extract witnesses or component facts from the available result. Simplify using the standard rewrite rules. Rewrite the conclusion repeatedly using the stated equalities.

Rewrite the conclusion using the stated equalities. Rewrite the conclusion repeatedly using the stated equalities. Establish an intermediate fact. Simplify using the standard rewrite rules. Rewrite the conclusion repeatedly using the stated equalities.

Simplify using the standard rewrite rules. A detailed English derivation is pending.
-/
theorem substR_substR (R : Type) [CommRing R] {A : Matrix T T₂ ℤ} {B : Matrix T₂ T ℤ}
    (hAB : A * B = 1) (f : MRingOver R (dualBlocks T)) : substR R A (substR R B f) = f := by
  have h : (substR R A).comp (substR R B) = AlgHom.id R _ := by
    refine MvPolynomial.algHom_ext fun p => ?_
    obtain ⟨⟨⟩, t⟩ := p
    simp only [AlgHom.comp_apply, AlgHom.id_apply, substR, aeval_X, map_sum, map_mul, aeval_C,
      algebraMap_eq]
    simp_rw [Finset.mul_sum, ← mul_assoc, ← C_mul]
    rw [Finset.sum_comm]
    simp_rw [← Finset.sum_mul, ← map_sum C, ← Int.cast_mul, ← Int.cast_sum]
    have h1 : ∀ x : T, ∑ s, B s t * A x s = (A * B) x t := fun x => by
      simp [Matrix.mul_apply, mul_comm]
    simp_rw [h1, hAB, Matrix.one_apply]
    simp
  exact DFunLike.congr_fun h f

omit [DecidableEq T] in

/- English proof (translation)
Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Replace the relevant objects with their definitions.

Simplify using the standard rewrite rules. Prove the components needed by the constructor for the conclusion. Fix the arbitrary inputs or assume the hypotheses. Fix the arbitrary inputs or assume the hypotheses. Split into cases according to the possible forms of the given data.

A detailed English derivation is pending.
-/
theorem isWH_iff {R : Type} [CommRing R] (f : MRingOver R (dualBlocks T)) (m : Unit → ℕ) :
    IsWeightedHomogeneous (NumbersDVR.blockWeight (dualBlocks T)) f m ↔ f.IsHomogeneous (m ()) := by
  have hw : ∀ d : (Σ k : Unit, dualBlocks T k) →₀ ℕ,
      Finsupp.weight (1 : (Σ k : Unit, dualBlocks T k) → ℕ) d = ∑ i : T, d ⟨(), i⟩ := by
    intro d
    rw [Pi.one_def, ← Finsupp.degree_eq_weight_one, Finsupp.degree_eq_sum, Fintype.sum_sigma]
    simp
  unfold IsHomogeneous IsWeightedHomogeneous
  simp only [Bridge.weight_blockWeight, hw, funext_iff]
  constructor
  · intro h d hd
    exact h hd ()
  · intro h d hd u
    cases u
    exact h hd

omit [DecidableEq T] [DecidableEq T₂] in

/- English proof (translation)
Rewrite the hypotheses and the conclusion using the stated equalities. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact.

Rewrite the indicated hypotheses using the stated equalities. Use the resulting assumption. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities.

A detailed English derivation is pending.
-/
theorem substR_isWH (R : Type) [CommRing R] (A : Matrix T T₂ ℤ) {f : MRingOver R (dualBlocks T₂)}
    {m : Unit → ℕ} (hf : IsWeightedHomogeneous (NumbersDVR.blockWeight (dualBlocks T₂)) f m) :
    IsWeightedHomogeneous (NumbersDVR.blockWeight (dualBlocks T)) (substR R A f) m := by
  rw [isWH_iff] at hf ⊢
  have hg : ∀ p : Σ k : Unit, dualBlocks T₂ k,
      (∑ t, C ((A t p.2 : ℤ) : R) * X (⟨(), t⟩ : Σ k : Unit, dualBlocks T k)).IsHomogeneous 1 := by
    intro p
    refine IsHomogeneous.sum _ _ _ fun t _ => ?_
    have := (isHomogeneous_C (Σ k : Unit, dualBlocks T k) ((A t p.2 : ℤ) : R)).mul
      (isHomogeneous_X R (⟨(), t⟩ : Σ k : Unit, dualBlocks T k))
    rwa [zero_add] at this
  have := hf.eval₂ (algebraMap R _) _ (fun r => by rw [algebraMap_eq]; exact isHomogeneous_C _ r) hg
  rw [one_mul] at this
  unfold substR
  rw [aeval_def]
  exact this

/- English proof (translation)
Reduce the claim to the hypotheses of an applicable result. Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses.

Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem comap_substR (R : Type) [CommRing R] {A : Matrix T T₂ ℤ} {B : Matrix T₂ T ℤ}
    (hAB : A * B = 1) (hBA : B * A = 1) (V : Ideal (MRingOver R (dualBlocks T))) :
    V.comap (substR R A) = V.map (substR R B) := by
  apply le_antisymm
  · intro f hf
    rw [← substR_substR R hBA f]
    exact Ideal.mem_map_of_mem _ hf
  · rw [Ideal.map_le_iff_le_comap]
    intro g hg
    rw [Ideal.mem_comap, Ideal.mem_comap, substR_substR R hAB]
    exact hg

omit [Fintype T₂] [DecidableEq T] [DecidableEq T₂] in

/- English proof (translation)
Proceed by induction. Treat this case separately. Treat this case separately. Treat this case separately. Rewrite the conclusion using the stated equalities.

Reduce the equality to equality of the corresponding arguments. Simplify using the standard rewrite rules.
-/
theorem red_substR (p : ℕ) (A : Matrix T T₂ ℤ) (f : MRingOver ℤ (dualBlocks T₂)) :
    MvPolynomial.map (Int.castRingHom (ZMod p)) (substR ℤ A f) =
      substR (ZMod p) A (MvPolynomial.map (Int.castRingHom (ZMod p)) f) := by
  induction f using MvPolynomial.induction_on with
  | C a => simp [substR]
  | add f g hf hg => rw [map_add, map_add, hf, hg, map_add, map_add]
  | mul_X f q hf =>
    rw [map_mul, map_mul, hf, map_mul, map_mul, map_X]
    congr 1
    simp [substR, map_sum]

/- English proof (translation)
Introduce a local definition for the expression. Establish an intermediate fact. Introduce a local definition for the expression. Establish an intermediate fact. Establish an intermediate fact.

Fix the arbitrary inputs or assume the hypotheses. Reduce the claim to the hypotheses of an applicable result. Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses. Rewrite the hypotheses and the conclusion using the stated equalities.

Fix the arbitrary inputs or assume the hypotheses. Rewrite the indicated hypotheses using the stated equalities. Supply the required witnesses or components. Apply function extensionality and compare values at an arbitrary argument. Replace the relevant objects with their definitions.

Establish an intermediate fact. Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities. Reduce the equality to equality of the corresponding arguments. Rewrite the conclusion using the stated equalities.

Both sides reduce to the same expression. A detailed English derivation is pending.
-/
theorem hilbFn_comap (F : Type) [Field F] {A : Matrix T T₂ ℤ} {B : Matrix T₂ T ℤ}
    (hAB : A * B = 1) (hBA : B * A = 1) (Q : Ideal (MRingOver F (dualBlocks T))) :
    NumbersDVR.hilbFn (Q.comap (substR F A)) = NumbersDVR.hilbFn Q := by
  let e : MRingOver F (dualBlocks T₂) ≃ₐ[F] MRingOver F (dualBlocks T) :=
    AlgEquiv.ofAlgHom (substR F A) (substR F B) (AlgHom.ext fun f => substR_substR F hAB f)
      (AlgHom.ext fun f => substR_substR F hBA f)
  have hQ : Q = (Q.comap (substR F A)).map (e : MRingOver F (dualBlocks T₂) →+* MRingOver F (dualBlocks T)) :=
    (Ideal.map_comap_of_surjective _ e.surjective Q).symm
  let qe := Ideal.quotientEquivAlg (Q.comap (substR F A)) Q e hQ
  have hcomp : qe.toLinearEquiv.toLinearMap ∘ₗ (Ideal.Quotient.mkₐ F (Q.comap (substR F A))).toLinearMap =
      (Ideal.Quotient.mkₐ F Q).toLinearMap ∘ₗ (substR F A).toLinearMap :=
    LinearMap.ext fun x => rfl
  have hH : ∀ m : Unit → ℕ,
      (weightedHomogeneousSubmodule F (NumbersDVR.blockWeight (dualBlocks T₂)) m).map
        (substR F A).toLinearMap =
      weightedHomogeneousSubmodule F (NumbersDVR.blockWeight (dualBlocks T)) m := by
    intro m
    apply le_antisymm
    · rw [Submodule.map_le_iff_le_comap]
      intro f hf
      rw [Submodule.mem_comap, mem_weightedHomogeneousSubmodule] at *
      exact substR_isWH F A hf
    · intro g hg
      rw [mem_weightedHomogeneousSubmodule] at hg
      exact ⟨substR F B g, (mem_weightedHomogeneousSubmodule _ _ _ _).mpr (substR_isWH F B hg),
        substR_substR F hAB g⟩
  funext m
  unfold NumbersDVR.hilbFn
  split_ifs with hm
  · have key : (NumbersDVR.gradedPiece (Q.comap (substR F A)) fun k => (m k).toNat).map
        qe.toLinearEquiv.toLinearMap = NumbersDVR.gradedPiece Q fun k => (m k).toNat := by
      unfold NumbersDVR.gradedPiece
      rw [← Submodule.map_comp, hcomp, Submodule.map_comp, hH]
    congr 1
    rw [← key]
    exact (LinearEquiv.finrank_map_eq qe.toLinearEquiv _).symm
  · rfl

end IntegralCoordGeometricNumber

open IntegralCoordGeometricNumber in

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Establish an intermediate fact.

Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. Assume the hypotheses and unpack their components.

Extract witnesses or component facts from the available result. Supply the required witnesses or components. Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result.

Assume the negation of the conclusion and derive a contradiction. Reduce the claim to the hypotheses of an applicable result. Establish an intermediate fact. Simplify using the standard rewrite rules. Rewrite the indicated hypotheses using the stated equalities. Use the resulting assumption.

Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Simplify to obtain the desired conclusion from the available facts. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.

Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact.

Rewrite the conclusion using the stated equalities. Reduce the equality to equality of the corresponding arguments. Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem IntCoordGeoNum.proof : IntCoordGeoNum.Statement := by
  intro T T₂ _ _ _ _ A B hAB hBA V n p hV hp hpV hdim a
  have : Fact p.Prime := ⟨hp⟩
  rw [← substR_int]
  have hsurj : Function.Surjective (substR ℤ A) := fun f => ⟨substR ℤ B f, substR_substR ℤ hAB f⟩
  have hV' : IsMultiProjPrime (V.comap (substR ℤ A)) := by
    have : V.IsPrime := hV.1
    refine ⟨inferInstance, ?_, ?_⟩
    · obtain ⟨S, hS, hVS⟩ := hV.2.1
      refine ⟨substR ℤ B '' S, ?_, ?_⟩
      · rintro _ ⟨f, hf, rfl⟩
        obtain ⟨b, hb⟩ := hS f hf
        exact ⟨b, (Bridge.isMultiHomog_iff _ b).mp
          (substR_isWH ℤ B ((Bridge.isMultiHomog_iff f b).mpr hb))⟩
      · rw [comap_substR ℤ hAB hBA, hVS, Ideal.map_span]
    · intro k
      obtain ⟨t, ht⟩ := hV.2.2 k
      by_contra h
      push Not at h
      apply ht
      have hmem : substR ℤ B (X ⟨k, t⟩) ∈ V.comap (substR ℤ A) := by
        simp only [substR, aeval_X]
        exact Ideal.sum_mem _ fun s _ => Ideal.mul_mem_left _ _ (h s)
      rwa [Ideal.mem_comap, substR_substR ℤ hAB] at hmem
  have hpV' : (C (p : ℤ) : MRing (dualBlocks T₂)) ∈ V.comap (substR ℤ A) := by
    rw [Ideal.mem_comap]
    simpa [substR] using hpV
  have hdim' : ringKrullDim (MRing (dualBlocks T₂) ⧸ V.comap (substR ℤ A)) =
      ((n + Fintype.card Unit : ℕ) : WithBot ℕ∞) := by
    rw [← hdim]
    exact ringKrullDim_eq_of_ringEquiv ((Ideal.quotEquivOfEq (by
        rw [← RingHom.comap_ker, Ideal.mk_ker]
        try rfl)).trans
      (RingHom.quotientKerEquivOfSurjective (f := (Ideal.Quotient.mk V).comp
        (substR ℤ A : MRing (dualBlocks T₂) →+* MRing (dualBlocks T)))
        (Ideal.Quotient.mk_surjective.comp hsurj)))
  rw [← Bridge.intNum_map_eq_geoNum p n V hV hpV hdim a,
    ← Bridge.intNum_map_eq_geoNum p n _ hV' hpV' hdim' a]
  have e1 : V.map (substR ℤ B) =
      V.map (substR ℤ B : MRingOver ℤ (dualBlocks T) →+* MRingOver ℤ (dualBlocks T₂)) := rfl
  have e2 : (V.map (MvPolynomial.map (Int.castRingHom (ZMod p)))).map (substR (ZMod p) B) =
      (V.map (MvPolynomial.map (Int.castRingHom (ZMod p)))).map
        (substR (ZMod p) B : MRingOver (ZMod p) (dualBlocks T) →+* MRingOver (ZMod p) (dualBlocks T₂)) := rfl
  have hred : (V.comap (substR ℤ A)).map (MvPolynomial.map (Int.castRingHom (ZMod p))) =
      (V.map (MvPolynomial.map (Int.castRingHom (ZMod p)))).comap (substR (ZMod p) A) := by
    rw [comap_substR ℤ hAB hBA, comap_substR (ZMod p) hAB hBA, e1, e2, Ideal.map_map, Ideal.map_map]
    congr 1
    exact RingHom.ext fun f => red_substR p B f
  unfold NumbersDVR.intNum
  rw [hred, hilbFn_comap (ZMod p) hAB hBA]

end

end GroundTheory.Heights₂.Heights

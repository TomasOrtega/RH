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
Unfold `substR intCoordSubst`. Simplify using the standard rewrite rules.
-/
theorem substR_int (A : Matrix T T₂ ℤ) : substR ℤ A = intCoordSubst A := by
  unfold substR intCoordSubst
  simp

omit [DecidableEq T₂] in

/- English proof (translation)
Establish `h : (substR R A).comp (substR R B) = AlgHom.id R _`. Use `MvPolynomial.algHom_ext fun p => ?_` and prove the remaining obligations. Take `⟨⟨⟩, t⟩` from `p`. Simplify using `only [AlgHom.comp_apply, AlgHom.id_apply, substR, aeval_X, map_sum, map_mul, aeval_C, algebraMap_eq]`. Repeatedly rewrite using `[Finset.mul_sum, ← mul_assoc, ← C_mul]`.

Rewrite using `[Finset.sum_comm]`. Repeatedly rewrite using `[← Finset.sum_mul, ← map_sum C, ← Int.cast_mul, ← Int.cast_sum]`. Establish `h1 : ∀ x : T, ∑ s, B s t * A x s = (A * B) x t` using `fun x => by`. Simplify using `[Matrix.mul_apply, mul_comm]`. Repeatedly rewrite using `[h1, hAB, Matrix.one_apply]`.

Simplify using the standard rewrite rules. Conclude with `DFunLike.congr_fun h f`.
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
Establish `hw : ∀ d : (Σ k : Unit, dualBlocks T k) →₀ ℕ, Finsupp.weight (1 : (Σ k : Unit, dualBlocks T k) → ℕ) d = ∑ i : T, d ⟨(), i⟩`. Introduce `d`. Rewrite using `[Pi.one_def, ← Finsupp.degree_eq_weight_one, Finsupp.degree_eq_sum, Fintype.sum_sigma]`. Simplify using the standard rewrite rules. Unfold `IsHomogeneous IsWeightedHomogeneous`.

Simplify using `only [Bridge.weight_blockWeight, hw, funext_iff]`. Prove the components needed by the constructor for the conclusion. Introduce `h d hd`. Conclude with `h hd ()`. Introduce `h d hd u`.

Consider the cases of `u`. Conclude with `h hd`.
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
Rewrite `hf`, the goal using `[isWH_iff]`. Establish `hg : ∀ p : Σ k : Unit, dualBlocks T₂ k, (∑ t, C ((A t p.2 : ℤ) : R) * X (⟨(), t⟩ : Σ k : Unit, dualBlocks T k)).IsHomogeneous 1`. Introduce `p`. Use `IsHomogeneous.sum _ _ _ fun t _ => ?_` and prove the remaining obligations. Use `(isHomogeneous_C (Σ k : Unit, dualBlocks T k) ((A t p.2 : ℤ) : R)).mul (isHomogeneous_X R (⟨(), t⟩ : Σ k : Unit, dualBlocks T k))` as an intermediate fact.

Rewrite `this` using `[zero_add]`. Then use the resulting hypothesis. Use `hf.eval₂ (algebraMap R _) _ (fun r => by rw [algebraMap_eq]; exact isHomogeneous_C _ r) hg` as an intermediate fact. Rewrite `this` using `[one_mul]`. Unfold `substR`. Rewrite using `[aeval_def]`.

Conclude with `this`.
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
Apply `le_antisymm` to reduce the goal to its premises. Introduce `f hf`. Rewrite using `[← substR_substR R hBA f]`. Conclude with `Ideal.mem_map_of_mem _ hf`. Rewrite using `[Ideal.map_le_iff_le_comap]`.

Introduce `g hg`. Rewrite using `[Ideal.mem_comap, Ideal.mem_comap, substR_substR R hAB]`. Conclude with `hg`.
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
Proceed by induction on `f using MvPolynomial.induction_on with`. Consider the case `C a => simp [substR]`. Consider the case `add f g hf hg => rw [map_add, map_add, hf, hg, map_add, map_add]`. Consider the case `mul_X f q hf`. Rewrite using `[map_mul, map_mul, hf, map_mul, map_mul, map_X]`.

Use `congr 1`. Simplify using `[substR, map_sum]`.
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
Set `e : MRingOver F (dualBlocks T₂) ≃ₐ[F] MRingOver F (dualBlocks T)` to `AlgEquiv.ofAlgHom (substR F A) (substR F B) (AlgHom.ext fun f => substR_substR F hAB f) (AlgHom.ext fun f => substR_substR F hBA f)`. Establish `hQ : Q = (Q.comap (substR F A)).map (e : MRingOver F (dualBlocks T₂) →+* MRingOver F (dualBlocks T))` using `(Ideal.map_comap_of_surjective _ e.surjective Q).symm`. Set `qe` to `Ideal.quotientEquivAlg (Q.comap (substR F A)) Q e hQ`. Establish `hcomp : qe.toLinearEquiv.toLinearMap ∘ₗ (Ideal.Quotient.mkₐ F (Q.comap (substR F A))).toLinearMap = (Ideal.Quotient.mkₐ F Q).toLinearMap ∘ₗ (substR F A).toLinearMap` using `LinearMap.ext fun x => rfl`. Establish `hH : ∀ m : Unit → ℕ, (weightedHomogeneousSubmodule F (NumbersDVR.blockWeight (dualBlocks T₂)) m).map (substR F A).toLinearMap = weightedHomogeneousSubmodule F (NumbersDVR.blockWeight (dualBlocks T)) m`.

Introduce `m`. Apply `le_antisymm` to reduce the goal to its premises. Rewrite using `[Submodule.map_le_iff_le_comap]`. Introduce `f hf`. Rewrite `*` using `[Submodule.mem_comap, mem_weightedHomogeneousSubmodule]`.

Conclude with `substR_isWH F A hf`. Introduce `g hg`. Rewrite `hg` using `[mem_weightedHomogeneousSubmodule]`. Conclude with `⟨substR F B g, (mem_weightedHomogeneousSubmodule _ _ _ _).mpr (substR_isWH F B hg), substR_substR F hAB g⟩`. Use function extensionality and compare the values at `m`.

Unfold `NumbersDVR.hilbFn`. Use `split_ifs with hm`. Establish `key : (NumbersDVR.gradedPiece (Q.comap (substR F A)) fun k => (m k).toNat).map qe.toLinearEquiv.toLinearMap = NumbersDVR.gradedPiece Q fun k => (m k).toNat`. Unfold `NumbersDVR.gradedPiece`. Rewrite using `[← Submodule.map_comp, hcomp, Submodule.map_comp, hH]`.

Use `congr 1`. Rewrite using `[← key]`. Conclude with `(LinearEquiv.finrank_map_eq qe.toLinearEquiv _).symm`. Both sides reduce to the same expression.
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
Introduce `T T₂ _ _ _ _ A B hAB hBA V n p hV hp hpV hdim a`. Establish `: Fact p.Prime` using `⟨hp⟩`. Rewrite using `[← substR_int]`. Establish `hsurj : Function.Surjective (substR ℤ A)` using `fun f => ⟨substR ℤ B f, substR_substR ℤ hAB f⟩`. Establish `hV' : IsMultiProjPrime (V.comap (substR ℤ A))`.

Establish `: V.IsPrime` using `hV.1`. Use `⟨inferInstance, ?_, ?_⟩` and prove the remaining obligations. Take `⟨S, hS, hVS⟩` from `hV.2.1`. Use `⟨substR ℤ B '' S, ?_, ?_⟩` and prove the remaining obligations. Introduce and unpack `_ ⟨f, hf, rfl⟩`.

Take `⟨b, hb⟩` from `hS f hf`. Conclude with `⟨b, (Bridge.isMultiHomog_iff _ b).mp (substR_isWH ℤ B ((Bridge.isMultiHomog_iff f b).mpr hb))⟩`. Rewrite using `[comap_substR ℤ hAB hBA, hVS, Ideal.map_span]`. Introduce `k`. Take `⟨t, ht⟩` from `hV.2.2 k`.

Assume the negation of the conclusion as `h`. Use `push Not at h`. Apply `ht` to reduce the goal to its premises. Establish `hmem : substR ℤ B (X ⟨k, t⟩) ∈ V.comap (substR ℤ A)`. Simplify using `only [substR, aeval_X]`.

Conclude with `Ideal.sum_mem _ fun s _ => Ideal.mul_mem_left _ _ (h s)`. Rewrite `hmem` using `[Ideal.mem_comap, substR_substR ℤ hAB]`. Then use the resulting hypothesis. Establish `hpV' : (C (p : ℤ) : MRing (dualBlocks T₂)) ∈ V.comap (substR ℤ A)`. Rewrite using `[Ideal.mem_comap]`. Simplify `hpV` using `[substR]`.

Establish `hdim' : ringKrullDim (MRing (dualBlocks T₂) ⧸ V.comap (substR ℤ A)) = ((n + Fintype.card Unit : ℕ) : WithBot ℕ∞)`. Rewrite using `[← hdim]`. Conclude with `ringKrullDim_eq_of_ringEquiv ((Ideal.quotEquivOfEq (by`. Rewrite using `[← RingHom.comap_ker, Ideal.mk_ker]`. Apply the tactic sequence `try rfl)).trans`.

Use the proof step `(RingHom.quotientKerEquivOfSurjective (f := (Ideal.Quotient.mk V).comp (substR ℤ A : MRing (dualBlocks T₂) →+* MRing (dualBlocks T))) (Ideal.Quotient.mk_surjective.comp hsurj)))`. Rewrite using `[← Bridge.intNum_map_eq_geoNum p n V hV hpV hdim a, ← Bridge.intNum_map_eq_geoNum p n _ hV' hpV' hdim' a]`. Establish `e1 : V.map (substR ℤ B) = V.map (substR ℤ B : MRingOver ℤ (dualBlocks T) →+* MRingOver ℤ (dualBlocks T₂))` using `rfl`. Establish `e2 : (V.map (MvPolynomial.map (Int.castRingHom (ZMod p)))).map (substR (ZMod p) B) = (V.map (MvPolynomial.map (Int.castRingHom (ZMod p)))).map (substR (ZMod p) B : MRingOver (ZMod p) (dualBlocks T) →+* MRingOver (ZMod p) (dualBlocks T₂))` using `rfl`. Establish `hred : (V.comap (substR ℤ A)).map (MvPolynomial.map (Int.castRingHom (ZMod p))) = (V.map (MvPolynomial.map (Int.castRingHom (ZMod p)))).comap (substR (ZMod p) A)`.

Rewrite using `[comap_substR ℤ hAB hBA, comap_substR (ZMod p) hAB hBA, e1, e2, Ideal.map_map, Ideal.map_map]`. Use `congr 1`. Conclude with `RingHom.ext fun f => red_substR p B f`. Unfold `NumbersDVR.intNum`. Rewrite using `[hred, hilbFn_comap (ZMod p) hAB hBA]`.
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

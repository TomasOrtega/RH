import Mathlib
import GroundTheory.GlobalFields.SemilocalAlgebras.NormTrace
import GroundTheory.GlobalFields.CompletionAtPlace.Integers

namespace GroundTheory.Global

open IsDedekindDomain NumberField TensorProduct Module Filter Topology
open scoped RestrictedProduct

noncomputable section

namespace AdeleBaseChange

open SemiLocal

variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

variable (K) in

def below (w : HeightOneSpectrum (𝓞 L)) : HeightOneSpectrum (𝓞 K) where
  asIdeal := w.asIdeal.under (𝓞 K)
  isPrime := Ideal.IsPrime.under (𝓞 K) w.asIdeal
  ne_bot := Ideal.under_ne_bot (𝓞 K) w.ne_bot

instance liesOver_below (w : HeightOneSpectrum (𝓞 L)) :
    w.asIdeal.LiesOver (below K w).asIdeal :=
  ⟨rfl⟩

omit [NumberField K] [NumberField L] in

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Assume the hypotheses and unpack their components. Fix the arbitrary inputs or assume the hypotheses. A detailed English derivation is pending.
-/
theorem below_eq_iff (w : HeightOneSpectrum (𝓞 L)) (v : HeightOneSpectrum (𝓞 K)) :
    below K w = v ↔ w.asIdeal.LiesOver v.asIdeal := by
  constructor
  · rintro rfl
    infer_instance
  · intro h
    exact HeightOneSpectrum.ext h.over.symm

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem tendsto_below : Tendsto (below K (L := L)) cofinite cofinite :=
  Filter.Tendsto.cofinite_of_finite_preimage_singleton fun v ↦
    ((Set.finite_range (Subtype.val : PlacesOver L v → HeightOneSpectrum (𝓞 L))).subset
      fun w hw ↦ ⟨⟨w, (below_eq_iff w v).1 hw⟩, rfl⟩).to_subtype

/- English proof (translation)
Substitute using the available equality. Both sides reduce to the same expression.
-/
theorem completionMap_congr {v v' : HeightOneSpectrum (𝓞 K)} (h : v = v')
    (w : HeightOneSpectrum (𝓞 L)) [w.asIdeal.LiesOver v.asIdeal] [w.asIdeal.LiesOver v'.asIdeal]
    (a : FiniteAdeleRing (𝓞 K) K) :
    completionMap v w (a v) = completionMap v' w (a v') := by
  subst h
  rfl

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Rewrite the hypotheses and the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem mapsTo_completionMap (v : HeightOneSpectrum (𝓞 K)) (w : HeightOneSpectrum (𝓞 L))
    [w.asIdeal.LiesOver v.asIdeal] :
    Set.MapsTo (completionMap v w) (v.adicCompletionIntegers K) (w.adicCompletionIntegers L) := by
  intro x hx
  rw [SetLike.mem_coe, HeightOneSpectrum.mem_adicCompletionIntegers] at hx ⊢
  rw [valued_completionMap]
  exact pow_le_one' hx _

variable (K L) in

def finiteAdeleMap : FiniteAdeleRing (𝓞 K) K →+* FiniteAdeleRing (𝓞 L) L :=
  RestrictedProduct.mapAlongRingHom (fun v : HeightOneSpectrum (𝓞 K) ↦ v.adicCompletion K)
    (fun w : HeightOneSpectrum (𝓞 L) ↦ w.adicCompletion L)
    (B₁ := fun v ↦ v.adicCompletionIntegers K) (B₂ := fun w ↦ w.adicCompletionIntegers L)
    (below K) tendsto_below (fun w ↦ completionMap (below K w) w)
    (hφ := .of_forall fun w ↦ mapsTo_completionMap (below K w) w)

@[simp]
/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem finiteAdeleMap_apply (x : FiniteAdeleRing (𝓞 K) K) (w : HeightOneSpectrum (𝓞 L)) :
    finiteAdeleMap K L x w = completionMap (below K w) w (x (below K w)) :=
  rfl

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem continuous_finiteAdeleMap : Continuous (finiteAdeleMap K L) :=
  RestrictedProduct.mapAlong_continuous _ _ (below K) tendsto_below _
    (.of_forall fun w ↦ mapsTo_completionMap (below K w) w) fun w ↦ continuous_completionMap (below K w) w

/- English proof (translation)
Reduce the conclusion to the remaining proof obligations. A detailed English derivation is pending.
-/
theorem finiteAdeleMap_algebraMap (k : K) :
    finiteAdeleMap K L (algebraMap K _ k) = algebraMap L _ (algebraMap K L k) := by
  refine FiniteAdeleRing.ext (K := L) fun w ↦ ?_
  exact (completionMap_algebraMap (below K w) w k).trans
    (IsScalarTower.algebraMap_apply K L (w.adicCompletion L) k)

end AdeleBaseChange

end

end GroundTheory.Global

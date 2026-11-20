import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsTypeGroupBlockLift
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ValLeOneOfMemKO
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsAdelicUnitaryTrivialOutsideSplitPlaceLocEq
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsSplitPlaceEqFixedTypePrimePlace
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.DiagUniformiserConjTransposeInvMemUpperParahoric
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SplitPlaceCompletionIsoPreservesValuation
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.CmFieldAdeleSplitPlaceSupportIntegral

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin GlobalTheory.PendOf
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.TrivOutsideGen

variable {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ}

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem coe_mul_mat (x y : GAf L n) :
    ((x * y).1 : Matrix (Fin n) (Fin n) (AL L)) =
      (x.1 : Matrix (Fin n) (Fin n) (AL L)) * (y.1 : Matrix (Fin n) (Fin n) (AL L)) := rfl

/- English proof (translation)
Rewrite using `[← Matrix.map_mul, ← coe_mul_mat, inv_mul_cancel]`. Conclude with `Matrix.map_one _ (map_zero _) (map_one _)`.
-/
theorem map_inv_mul_map (x : GAf L n) (w : HeightOneSpectrum (𝓞 (maximalRealSubfield L))) :
    ((x⁻¹).1 : Matrix (Fin n) (Fin n) (AL L)).map (compAt L w) *
      (x.1 : Matrix (Fin n) (Fin n) (AL L)).map (compAt L w) = 1 := by
  rw [← Matrix.map_mul, ← coe_mul_mat, inv_mul_cancel]
  exact Matrix.map_one _ (map_zero _) (map_one _)

/- English proof (translation)
Use `map_inv_mul_map x w` as an intermediate fact. Rewrite `this` using `[h, mul_one]`. Then use the resulting hypothesis.
-/
theorem map_inv_eq_one (x : GAf L n) (w : HeightOneSpectrum (𝓞 (maximalRealSubfield L)))
    (h : (x.1 : Matrix (Fin n) (Fin n) (AL L)).map (compAt L w) = 1) :
    ((x⁻¹).1 : Matrix (Fin n) (Fin n) (AL L)).map (compAt L w) = 1 := by
  have := map_inv_mul_map x w
  rwa [h, mul_one] at this

/- English proof (translation)
Establish `hcard : Module.finrank (maximalRealSubfield L) L = 2` using `Algebra.IsQuadraticExtension.finrank_eq_two _ _`. Set `b : Module.Basis (Fin 2) (maximalRealSubfield L) L` to `Module.finBasisOfFinrankEq _ _ hcard`. Take `⟨A, B, hAB⟩` from `GlobalTheory.tensor_exists_decomp b z`. Establish `hw : ∀ w, A w = 0 ∧ B w = 0`. Introduce `w`.

Establish `h` using `hz w`. Rewrite `h` using `[hAB]`. Apply `GlobalTheory.tensor_decomp_eq_zero b` to reduce the goal to its premises. Simplify using `[ReciprocityTheory.Aut.compAt, Algebra.TensorProduct.map_tmul] at h`. Conclude with `h`.

Establish `hA : A = 0` using `DFunLike.ext _ _ fun w => (hw w).1`. Establish `hB : B = 0` using `DFunLike.ext _ _ fun w => (hw w).2`. Rewrite using `[hAB, hA, hB]`. Simplify using the standard rewrite rules.
-/
theorem adele_eq_zero (z : AL L) (hz : ∀ w, compAt L w z = 0) : z = 0 := by
  have hcard : Module.finrank (maximalRealSubfield L) L = 2 :=
    Algebra.IsQuadraticExtension.finrank_eq_two _ _
  let b : Module.Basis (Fin 2) (maximalRealSubfield L) L := Module.finBasisOfFinrankEq _ _ hcard
  obtain ⟨A, B, hAB⟩ := GlobalTheory.tensor_exists_decomp b z
  have hw : ∀ w, A w = 0 ∧ B w = 0 := by
    intro w
    have h := hz w
    rw [hAB] at h
    apply GlobalTheory.tensor_decomp_eq_zero b
    simp [ReciprocityTheory.Aut.compAt, Algebra.TensorProduct.map_tmul] at h
    exact h
  have hA : A = 0 := DFunLike.ext _ _ fun w => (hw w).1
  have hB : B = 0 := DFunLike.ext _ _ fun w => (hw w).2
  rw [hAB, hA, hB]
  simp

/- English proof (translation)
Use `Subtype.ext (Units.ext (Matrix.ext fun i j => ?_))` and prove the remaining obligations. Rewrite using `[← sub_eq_zero]`. Apply `adele_eq_zero` to reduce the goal to its premises. Introduce `w`. Establish `h1` using `congrFun (congrFun (hy w (Set.notMem_empty w)) i) j`.

Simplify using `only [Matrix.map_apply] at h1`. Rewrite using `[map_sub, h1]`. Simplify using `only [OneMemClass.coe_one, Units.val_one, Matrix.one_apply]`. Apply the tactic sequence `split_ifs <;> simp`.
-/
theorem eq_one_of_trivOutside_empty (y : GAf L n) (hy : TrivOutside (∅ : Set _) y) : y = 1 := by
  refine Subtype.ext (Units.ext (Matrix.ext fun i j => ?_))
  rw [← sub_eq_zero]
  apply adele_eq_zero
  intro w
  have h1 := congrFun (congrFun (hy w (Set.notMem_empty w)) i) j
  simp only [Matrix.map_apply] at h1
  rw [map_sub, h1]
  simp only [OneMemClass.coe_one, Units.val_one, Matrix.one_apply]
  split_ifs <;> simp

/- English proof (translation)
Introduce `L _ _ _ n K T`. Proceed by induction on `T using Finset.induction_on with`. Consider the case `empty`. Introduce `y hy _`. Rewrite using `[eq_one_of_trivOutside_empty y (by simpa using hy)]`.

Conclude with `K.one_mem`. Consider the case `insert v T hv ih`. Introduce `y hy hloc`. Take `⟨p, hpK, hpT, hpv⟩` from `hloc v (Finset.mem_insert_self v T)`. Establish `hpinv : ∀ w, w ≠ v → ((p⁻¹).1 : Matrix (Fin n) (Fin n) (AL L)).map (compAt L w) = 1` using `fun w hw => map_inv_eq_one p w (hpT w (by simpa using hw))`.

Establish `key : y = p * (p⁻¹ * y)` using `by group`. Rewrite using `[key]`. Use `K.mul_mem hpK (ih _ ?_ ?_)` and prove the remaining obligations. Introduce `w hw`. Rewrite using `[coe_mul_mat, Matrix.map_mul]`.

Distinguish the cases in `hwv : w = v`. Substitute `hwv` using the available equality. Rewrite using `[← hpv, map_inv_mul_map]`. Establish `hwT : w ∉ ((insert v T : Finset _) : Set _)`. Simplify using `only [Finset.coe_insert, Set.mem_insert_iff, not_or]`.

Conclude with `⟨hwv, hw⟩`. Rewrite using `[hpinv w hwv, hy w hwT, mul_one]`. Introduce `w hw`. Take `⟨q, hqK, hqT, hqw⟩` from `hloc w (Finset.mem_insert_of_mem hw)`. Use `⟨q, hqK, hqT, ?_⟩` and prove the remaining obligations.

Establish `hwv : w ≠ v` using `fun h => hv (h ▸ hw)`. Rewrite using `[hqw, coe_mul_mat, Matrix.map_mul, hpinv w hwv, one_mul]`.
-/
theorem mem_of_trivOutside_of_local : ∀ {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ} (K : Subgroup (GAf L n)) (T : Finset (HeightOneSpectrum (𝓞 (maximalRealSubfield L)))) (y : GAf L n), TrivOutside (T : Set (HeightOneSpectrum (𝓞 (maximalRealSubfield L)))) y → (∀ v ∈ T, ∃ p ∈ K, TrivOutside {v} p ∧ (p.1 : Matrix (Fin n) (Fin n) (AL L)).map (compAt L v) = (y.1 : Matrix (Fin n) (Fin n) (AL L)).map (compAt L v)) → y ∈ K := by
  intro L _ _ _ n K T
  classical
  induction T using Finset.induction_on with
  | empty =>
    intro y hy _
    rw [eq_one_of_trivOutside_empty y (by simpa using hy)]
    exact K.one_mem
  | insert v T hv ih =>
    intro y hy hloc
    obtain ⟨p, hpK, hpT, hpv⟩ := hloc v (Finset.mem_insert_self v T)
    have hpinv : ∀ w, w ≠ v → ((p⁻¹).1 : Matrix (Fin n) (Fin n) (AL L)).map (compAt L w) = 1 :=
      fun w hw => map_inv_eq_one p w (hpT w (by simpa using hw))
    have key : y = p * (p⁻¹ * y) := by group
    rw [key]
    refine K.mul_mem hpK (ih _ ?_ ?_)
    · intro w hw
      rw [coe_mul_mat, Matrix.map_mul]
      by_cases hwv : w = v
      · subst hwv
        rw [← hpv, map_inv_mul_map]
      · have hwT : w ∉ ((insert v T : Finset _) : Set _) := by
          simp only [Finset.coe_insert, Set.mem_insert_iff, not_or]
          exact ⟨hwv, hw⟩
        rw [hpinv w hwv, hy w hwT, mul_one]
    · intro w hw
      obtain ⟨q, hqK, hqT, hqw⟩ := hloc w (Finset.mem_insert_of_mem hw)
      refine ⟨q, hqK, hqT, ?_⟩
      have hwv : w ≠ v := fun h => hv (h ▸ hw)
      rw [hqw, coe_mul_mat, Matrix.map_mul, hpinv w hwv, one_mul]

end GlobalTheory.TrivOutsideGen

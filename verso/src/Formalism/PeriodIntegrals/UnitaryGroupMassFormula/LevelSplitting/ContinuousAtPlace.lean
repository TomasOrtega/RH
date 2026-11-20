import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LevelSplitting.MeasDefs

noncomputable section

namespace PI.LevelKSplit.W.Cont

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub NumberField IsDedekindDomain MeasureTheory
open scoped TensorProduct

section

variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E]

/- English proof (translation)
The claim follows from `RestrictedProduct.continuous_eval (R := fun w : HeightOneSpectrum (𝓞 F) => w.adicCompletion F) (A := fun w : HeightOneSpectrum (𝓞 F) => (w.adicCompletionIntegers F : Set (w.adicCompletion F))) v`.
-/
theorem continuous_evalV (v : HeightOneSpectrum (𝓞 F)) : Continuous (evalV F v) :=
  RestrictedProduct.continuous_eval (R := fun w : HeightOneSpectrum (𝓞 F) => w.adicCompletion F)
    (A := fun w : HeightOneSpectrum (𝓞 F) => (w.adicCompletionIntegers F : Set (w.adicCompletion F))) v

def phiV (v : HeightOneSpectrum (𝓞 F)) : Af F ⊗[F] E →ₐ[F] Fv F v ⊗[F] E :=
  Algebra.TensorProduct.map (evalV F v) (AlgHom.id F E)

/- English proof (translation)
Rewrite using `[Algebra.smul_def, Algebra.smul_def, map_mul]`. Use `congr 1`.
-/
theorem phiV_smul (v : HeightOneSpectrum (𝓞 F)) (a : Af F) (x : Af F ⊗[F] E) :
    phiV (E := E) v (a • x) = evalV F v a • phiV v x := by
  rw [Algebra.smul_def, Algebra.smul_def, map_mul]
  congr 1

def phiSL (v : HeightOneSpectrum (𝓞 F)) :
    Af F ⊗[F] E →ₛₗ[(evalV F v).toRingHom] Fv F v ⊗[F] E where
  toFun := phiV v
  map_add' := map_add _
  map_smul' := fun a x => phiV_smul v a x

/- English proof (translation)
Establish `: IsModuleTopology (Af F) (Af F ⊗[F] E)` using `⟨rfl⟩`. Establish `: IsModuleTopology (Fv F v) (Fv F v ⊗[F] E)` using `⟨rfl⟩`. Establish `: ContinuousAdd (Fv F v ⊗[F] E)` using `IsModuleTopology.toContinuousAdd (Fv F v) _`. Establish `: ContinuousSMul (Fv F v) (Fv F v ⊗[F] E)` using `IsModuleTopology.toContinuousSMul (Fv F v) _`. Conclude with `IsModuleTopology.continuous_of_linearMapₛₗ (continuous_evalV v) (phiSL v)`.
-/
theorem continuous_phiV (v : HeightOneSpectrum (𝓞 F)) : Continuous (phiV (E := E) v) := by
  have : IsModuleTopology (Af F) (Af F ⊗[F] E) := ⟨rfl⟩
  have : IsModuleTopology (Fv F v) (Fv F v ⊗[F] E) := ⟨rfl⟩
  have : ContinuousAdd (Fv F v ⊗[F] E) := IsModuleTopology.toContinuousAdd (Fv F v) _
  have : ContinuousSMul (Fv F v) (Fv F v ⊗[F] E) := IsModuleTopology.toContinuousSMul (Fv F v) _
  exact IsModuleTopology.continuous_of_linearMapₛₗ (continuous_evalV v) (phiSL v)

end

/- English proof (translation)
Introduce `F E _ _ _ _ _ σ n J v`. Establish `h1 : Continuous (fun g : HA (Af F) σ J => (incAf σ J g : GL (Fin n) (Af F ⊗[F] E)))` using `continuous_subtype_val`. Establish `h2 : Continuous (fun g : HA (Af F) σ J => ((incAf σ J g : GL (Fin n) (Af F ⊗[F] E)) : Matrix (Fin n) (Fin n) (Af F ⊗[F] E)))` using `Units.continuous_val.comp h1`. Use `(h2.matrix_map (continuous_phiV (E := E) v)).congr ?_` and prove the remaining obligations. Introduce `g`.

Both sides reduce to the same expression.
-/
theorem continuous_at_place : PI.LevelKSplit.W.Meas.ContPlace := by
  intro F E _ _ _ _ _ σ n J v
  have h1 : Continuous (fun g : HA (Af F) σ J => (incAf σ J g : GL (Fin n) (Af F ⊗[F] E))) :=
    continuous_subtype_val
  have h2 : Continuous (fun g : HA (Af F) σ J =>
      ((incAf σ J g : GL (Fin n) (Af F ⊗[F] E)) : Matrix (Fin n) (Fin n) (Af F ⊗[F] E))) :=
    Units.continuous_val.comp h1
  refine (h2.matrix_map (continuous_phiV (E := E) v)).congr ?_
  intro g
  rfl

end PI.LevelKSplit.W.Cont

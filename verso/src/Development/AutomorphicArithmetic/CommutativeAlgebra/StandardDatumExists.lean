import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.GeometricFlagBases.FinModel
open UpperTheory.Gal.Int.Geo

open NumberField GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen in
/- English proof (translation)
Introduce `p _ D ha E _ _ e`. Set `φ : 𝓞 D.F →+* E` to `(e : D.F →+* E).comp (algebraMap (𝓞 D.F) D.F)`. Establish `key : D.ω ^ 2 - (D.tr : 𝓞 D.F) * D.ω + (D.nm : 𝓞 D.F) = 0`. Rewrite using `[← D.tr_eq, ← D.nm_eq]`. Expand and normalize the polynomial expressions, which then agree.

Establish `hroot : φ D.ω ^ 2 - (D.tr : E) * φ D.ω + (D.nm : E) = 0`. Simplify using `using congrArg φ key`. Establish `hsub : Subsingleton (Fin D.toG.a)`. Establish `h : D.toG.a = 1` using `ha`. Rewrite using `[h]`.

Use `infer_instance`. Conclude with `⟨{ ρ := φ D.ω ρ_root := hroot t := fun _ => φ t_ω := fun _ => rfl comax := fun i j hij => (hij (Subsingleton.elim i j)).elim }, rfl, fun _ _ => rfl⟩`.
-/
theorem UpperTheory.standard_datum_exists :
    StdEx := by
  intro p _ D ha E _ _ e
  let φ : 𝓞 D.F →+* E := (e : D.F →+* E).comp (algebraMap (𝓞 D.F) D.F)
  have key : D.ω ^ 2 - (D.tr : 𝓞 D.F) * D.ω + (D.nm : 𝓞 D.F) = 0 := by
    rw [← D.tr_eq, ← D.nm_eq]
    ring
  have hroot : φ D.ω ^ 2 - (D.tr : E) * φ D.ω + (D.nm : E) = 0 := by
    simpa using congrArg φ key
  have hsub : Subsingleton (Fin D.toG.a) := by
    have h : D.toG.a = 1 := ha
    rw [h]
    infer_instance
  exact ⟨{ ρ := φ D.ω
           ρ_root := hroot
           t := fun _ => φ
           t_ω := fun _ => rfl
           comax := fun i j hij => (hij (Subsingleton.elim i j)).elim }, rfl, fun _ _ => rfl⟩

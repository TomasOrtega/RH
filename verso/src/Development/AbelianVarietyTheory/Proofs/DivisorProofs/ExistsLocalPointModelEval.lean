import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocPt

open scoped TensorProduct
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open scoped Classical

namespace GlobalTheory.FinComm.Surj

variable {F : Type} [Field F] [NumberField F]

noncomputable def adAt (v : Pl F) (a : Fv F v) : AF F := LinearMap.inr F (Ainf F) (Af F) (singleFin v a)

/- English proof (translation)
Use `show Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v (sndA F (adAt v a)) = a`. Conclude with `evalV_singleFin_self v a`.
-/
theorem evFin_adAt_self (v : Pl F) (a : Fv F v) : evFin F v (adAt v a) = a := by
  show Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v (sndA F (adAt v a)) = a
  exact evalV_singleFin_self v a

/- English proof (translation)
Establish `h2 : u.2 * singleFin v a = 0`. Apply `af_ext` to reduce the goal to its premises. Introduce `t`. Rewrite using `[map_mul, map_zero]`. Distinguish the cases in `h : t = v`.

Substitute `h` using the available equality. Establish `: Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F t u.2 = 0` using `hu`. Rewrite using `[this, zero_mul]`. Rewrite using `[evalV_singleFin_ne h, mul_zero]`. Conclude with `Prod.ext (mul_zero _) h2`.
-/
theorem mul_adAt_eq_zero (v : Pl F) (a : Fv F v) {u : AF F} (hu : evFin F v u = 0) : u * adAt v a = 0 := by
  have h2 : u.2 * singleFin v a = 0 := by
    apply af_ext
    intro t
    rw [map_mul, map_zero]
    by_cases h : t = v
    · subst h
      have : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F t u.2 = 0 := hu
      rw [this, zero_mul]
    · rw [evalV_singleFin_ne h, mul_zero]
  exact Prod.ext (mul_zero _) h2

end GlobalTheory.FinComm.Surj

open GlobalTheory.FinComm.Surj in
/- English proof (translation)
Use `⟨M.co.e.symm (fun i => adAt v (p.1 i), fun i => adAt v (p.2 i)), ?_, ?_⟩` and prove the remaining obligations. Introduce `u hu`. Rewrite using `[← map_smul]`. Use `M.co.e.symm.map_zero using 2` and compare the differences between its conclusion and the goal. Use extensionality with `i`.

Conclude with `mul_adAt_eq_zero v _ hu`. Conclude with `mul_adAt_eq_zero v _ hu`. Rewrite using `[LinearEquiv.apply_symm_apply]`. Conclude with `Prod.ext (funext fun i => evFin_adAt_self v _) (funext fun i => evFin_adAt_self v _)`.
-/
theorem GlobalTheory.FinComm.exists_At_locPt_eq {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {σ : E →ₐ[F] E} {n d : ℕ}
    {X : Spc F E n} {W : Spc F E d} (M : Model σ X W) (v : Pl F)
    (p : (Fin n × Fin d → Fv F v) × (Fin n × Fin d → Fv F v)) :
    ∃ w : Matrix (Fin n) (Fin d) (AE F E), At (evFin F v) w ∧ GlobalTheory.FinComm.locPt v (M.co.e w) = p := by
  refine ⟨M.co.e.symm (fun i => adAt v (p.1 i), fun i => adAt v (p.2 i)), ?_, ?_⟩
  · intro u hu
    rw [← map_smul]
    convert M.co.e.symm.map_zero using 2
    ext i
    · exact mul_adAt_eq_zero v _ hu
    · exact mul_adAt_eq_zero v _ hu
  · rw [LinearEquiv.apply_symm_apply]
    exact Prod.ext (funext fun i => evFin_adAt_self v _) (funext fun i => evFin_adAt_self v _)

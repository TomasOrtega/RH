import Development.AbelianVarietyTheory.Definitions.Divisors.DivisorSupportCondition
import Development.AbelianVarietyTheory.Definitions.Divisors.SecClass
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BigEtaleModuleSheafMonoEpiIffSections
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleSheafSectionsExtAndGlue
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC
open scoped TensorProduct

namespace GlobalTheory.EtC.TensZero

variable {R : Type} [CommRing R]

/- English proof (translation)
Establish `h : 𝟙 F = 0` using `hF.eq_of_src _ _`. Establish `: Sec.map (𝟙 F) a = Sec.map (0 : F ⟶ F) a` using `by rw [h]`. Establish `h1 : Sec.map (𝟙 F) a = a` using `rfl`. Establish `h2 : Sec.map (0 : F ⟶ F) a = 0`. Simplify using `only [Sec.map]`.

Both sides reduce to the same expression. Rewrite `this` using `[h1, h2]`. Conclude with `this`.
-/
theorem sec_eq_zero_of_isZero {F : Shv R} (hF : IsZero F) {U : Scheme.{0}} (a : Sec F U) : a = 0 := by
  have h : 𝟙 F = 0 := hF.eq_of_src _ _
  have : Sec.map (𝟙 F) a = Sec.map (0 : F ⟶ F) a := by rw [h]
  have h1 : Sec.map (𝟙 F) a = a := rfl
  have h2 : Sec.map (0 : F ⟶ F) a = 0 := by
    simp only [Sec.map]
    rfl
  rw [h1, h2] at this
  exact this

/- English proof (translation)
Rewrite using `[IsZero.iff_id_eq_zero]`. Use `((GlobalTheory.EtC.mono_epi_sections R (𝟙 F)).2.2.2 0 fun U a => ?_)` and prove the remaining obligations. Rewrite using `[h U a]`. Simplify using the standard rewrite rules.
-/
theorem isZero_of_sec {F : Shv R} (h : ∀ (U : Scheme.{0}) (a : Sec F U), a = 0) : IsZero F := by
  rw [IsZero.iff_id_eq_zero]
  refine ((GlobalTheory.EtC.mono_epi_sections R (𝟙 F)).2.2.2 0 fun U a => ?_)
  rw [h U a]
  simp

/- English proof (translation)
Use `DFinsupp.ext fun p => ?_` and prove the remaining obligations. Use `show x p = 0`. Establish `hp` using `p.2`. Distinguish the cases in `h1 : p.1.1 = 0`. Establish `h2 : p.1.2 ≠ 0` using `by omega`.

Proceed by induction on `x p using TensorProduct.induction_on with`. Consider the case `zero => rfl`. Consider the case `tmul a b => rw [sec_eq_zero_of_isZero (hJ _ h2) b, TensorProduct.tmul_zero]`. Consider the case `add a b ha hb => rw [ha, hb, add_zero]`. Proceed by induction on `x p using TensorProduct.induction_on with`.

Consider the case `zero => rfl`. Consider the case `tmul a b => rw [sec_eq_zero_of_isZero (hI _ h1) a, TensorProduct.zero_tmul]`. Consider the case `add a b ha hb => rw [ha, hb, add_zero]`.
-/
theorem tens_eq_zero {I J : Cx R} (hI : ∀ s : ℤ, s ≠ 0 → IsZero (I.X s)) (hJ : ∀ t : ℤ, t ≠ 0 → IsZero (J.X t))
    (U : Scheme.{0}) (w : ℤ) (hw : w ≠ 0) (x : Tens I J U w) : x = 0 := by
  refine DFinsupp.ext fun p => ?_
  show x p = 0
  have hp := p.2
  by_cases h1 : p.1.1 = 0
  · have h2 : p.1.2 ≠ 0 := by omega
    induction x p using TensorProduct.induction_on with
    | zero => rfl
    | tmul a b => rw [sec_eq_zero_of_isZero (hJ _ h2) b, TensorProduct.tmul_zero]
    | add a b ha hb => rw [ha, hb, add_zero]
  · induction x p using TensorProduct.induction_on with
    | zero => rfl
    | tmul a b => rw [sec_eq_zero_of_isZero (hI _ h1) a, TensorProduct.zero_tmul]
    | add a b ha hb => rw [ha, hb, add_zero]

end GlobalTheory.EtC.TensZero

open GlobalTheory.EtC.TensZero in
/- English proof (translation)
Introduce `R _ I J K τ hτ hI hJ w hw`. Use `isZero_of_sec fun U y => ?_` and prove the remaining obligations. Use `(GlobalTheory.EtC.sec_ext_glue R (K.X w) U).1 y 0 ?_` and prove the remaining obligations. Take `⟨S, hS, hP⟩` from `hτ.1 U w y`. Use `⟨S, hS, fun V g hg => ?_⟩` and prove the remaining obligations.

Take `⟨x, hx⟩` from `hP V g hg`. Rewrite `hx` using `[tens_eq_zero hI hJ V w hw x, map_zero]`. Rewrite using `[← hx]`. Conclude with `(map_zero _).symm`.
-/
theorem GlobalTheory.EtC.isZero_tensor_of_deg_zero : ∀ (R : Type) [CommRing R] {I J K : Cx R} (τ : Pair I J K), τ.IsTensor →
    (∀ s : ℤ, s ≠ 0 → IsZero (I.X s)) → (∀ t : ℤ, t ≠ 0 → IsZero (J.X t)) → ∀ w : ℤ, w ≠ 0 → IsZero (K.X w) := by
  intro R _ I J K τ hτ hI hJ w hw
  refine isZero_of_sec fun U y => ?_
  refine (GlobalTheory.EtC.sec_ext_glue R (K.X w) U).1 y 0 ?_
  obtain ⟨S, hS, hP⟩ := hτ.1 U w y
  refine ⟨S, hS, fun V g hg => ?_⟩
  obtain ⟨x, hx⟩ := hP V g hg
  rw [tens_eq_zero hI hJ V w hw x, map_zero] at hx
  rw [← hx]
  exact (map_zero _).symm

import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FinPartIdemMulMemIff

noncomputable section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

namespace GlobalTheory.VacAny

variable {F : Type} [Field F] [NumberField F]

scoped instance invTwoV (v : HeightOneSpectrum (𝓞 F)) : Invertible (2 : Fv F v) :=
  invertibleOfNonzero (by
    rw [← map_ofNat (algebraMap F (Fv F v)) 2]
    exact (map_ne_zero _).2 two_ne_zero)

def psiV (ψ : AddChar (AF F) ℂ) (v : HeightOneSpectrum (𝓞 F)) : AddChar (Fv F v) ℂ :=
  ψ.compAddMonoidHom (GlobalTheory.EmbChart.atPlace v).toAddMonoidHom

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem psiV_apply (ψ : AddChar (AF F) ℂ) (v : HeightOneSpectrum (𝓞 F)) (t : Fv F v) :
    psiV ψ v t = ψ (GlobalTheory.EmbChart.atPlace v t) := rfl

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem psiV_eq_psiLoc (ψ : AddChar (AF F) ℂ) (v : HeightOneSpectrum (𝓞 F)) (t : Fv F v) :
    psiV ψ v t = GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.psiLoc ψ v t := rfl

/- English proof (translation)
Establish `h : (GlobalTheory.EmbChart.atPlace v : Fv F v → AF F) = fun t => (0, GlobalTheory.AdelicU.singleFin v t)` using `rfl`. Rewrite using `[h]`. Conclude with `continuous_const.prodMk (GlobalTheory.AdelicU.continuous_singleFin v)`.
-/
theorem continuous_atPlace (v : HeightOneSpectrum (𝓞 F)) : Continuous (GlobalTheory.EmbChart.atPlace v) := by
  have h : (GlobalTheory.EmbChart.atPlace v : Fv F v → AF F) = fun t => (0, GlobalTheory.AdelicU.singleFin v t) := rfl
  rw [h]
  exact continuous_const.prodMk (GlobalTheory.AdelicU.continuous_singleFin v)

/- English proof (translation)
The claim follows from `hψ.comp (continuous_atPlace v)`.
-/
theorem continuous_psiV {ψ : AddChar (AF F) ℂ} (hψ : Continuous ψ) (v : HeightOneSpectrum (𝓞 F)) :
    Continuous (psiV ψ v) :=
  hψ.comp (continuous_atPlace v)

section At

variable {v : HeightOneSpectrum (𝓞 F)}

local notation "ev" => GlobalTheory.AdelicU.evFin F v

/- English proof (translation)
Use `(invOf_eq_right_inv ?_).symm` and prove the remaining obligations. Establish `h : ev (2 * ⅟(2 : AF F)) = 1` using `by rw [mul_invOf_self, map_one]`. Rewrite `h` using `[map_mul, map_ofNat]`. Then use the resulting hypothesis.
-/
theorem evFin_invOf_two : ev (⅟(2 : AF F)) = ⅟(2 : Fv F v) := by
  refine (invOf_eq_right_inv ?_).symm
  have h : ev (2 * ⅟(2 : AF F)) = 1 := by rw [mul_invOf_self, map_one]
  rwa [map_mul, map_ofNat] at h

/- English proof (translation)
Introduce `u hu` and use `by rw [smul_eq_mul, mul_comm, GlobalTheory.EmbChart.atPlace_mul_right, hu, mul_zero, map_zero]`.
-/
theorem at_atPlace (t : Fv F v) : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At ev (GlobalTheory.EmbChart.atPlace v t) := fun u hu => by
  rw [smul_eq_mul, mul_comm, GlobalTheory.EmbChart.atPlace_mul_right, hu, mul_zero, map_zero]

/- English proof (translation)
Introduce `u hu` and use `by rw [smul_eq_mul, ← mul_assoc, show u * x = 0 from hx u hu, zero_mul]`.
-/
theorem at_mul_right {x : AF F} (hx : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At ev x) (y : AF F) :
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At ev (x * y) := fun u hu => by
  rw [smul_eq_mul, ← mul_assoc, show u * x = 0 from hx u hu, zero_mul]

/- English proof (translation)
Rewrite using `[mul_comm]`. Conclude with `at_mul_right hy x`.
-/
theorem at_mul_left (x : AF F) {y : AF F} (hy : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At ev y) :
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At ev (x * y) := by
  rw [mul_comm]; exact at_mul_right hy x

/- English proof (translation)
Introduce `u hu` and use `by rw [smul_add, hx u hu, hy u hu, add_zero]`.
-/
theorem at_add {x y : AF F} (hx : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At ev x) (hy : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At ev y) :
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At ev (x + y) := fun u hu => by rw [smul_add, hx u hu, hy u hu, add_zero]

/- English proof (translation)
Introduce `u _` and use `smul_zero u`.
-/
theorem at_zero : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At ev (0 : AF F) := fun u _ => smul_zero u

/- English proof (translation)
Introduce `u hu` and use `by rw [smul_neg, hx u hu, neg_zero]`.
-/
theorem at_neg {x : AF F} (hx : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At ev x) : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At ev (-x) := fun u hu => by
  rw [smul_neg, hx u hu, neg_zero]

/- English proof (translation)
Rewrite using `[sub_eq_add_neg]`. Conclude with `at_add hx (at_neg hy)`.
-/
theorem at_sub {x y : AF F} (hx : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At ev x) (hy : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At ev y) :
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At ev (x - y) := by
  rw [sub_eq_add_neg]; exact at_add hx (at_neg hy)

/- English proof (translation)
Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty => rw [Finset.sum_empty]`. Conclude with `at_zero`. Consider the case `insert a s ha ih`. Rewrite using `[Finset.sum_insert ha]`.

Conclude with `at_add (h a (Finset.mem_insert_self a s)) (ih fun i hi => h i (Finset.mem_insert_of_mem hi))`.
-/
theorem at_sum {ι : Type} (s : Finset ι) {f : ι → AF F} (h : ∀ i ∈ s, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At ev (f i)) :
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At ev (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => rw [Finset.sum_empty]; exact at_zero
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact at_add (h a (Finset.mem_insert_self a s)) (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

/- English proof (translation)
Introduce `u hu` and use `funext fun i => h i u hu`.
-/
theorem at_pi {κ : Type} {z : κ → AF F} (h : ∀ i, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At ev (z i)) :
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At ev z := fun u hu => funext fun i => h i u hu

end At

end GlobalTheory.VacAny

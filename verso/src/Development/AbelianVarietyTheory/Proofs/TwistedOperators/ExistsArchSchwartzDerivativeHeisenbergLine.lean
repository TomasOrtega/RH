import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique

open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open scoped SchwartzMap

noncomputable section

namespace GlobalTheory.HeisDeriv

variable {F : Type} [Field F] [NumberField F]

/- English proof (translation)
The claim follows from `map_add (InfiniteAdeleRing.ringEquiv_mixedSpace F) a.1 b.1`.
-/
theorem evI_add (a b : AF F) : evI F (a + b) = evI F a + evI F b :=
  map_add (InfiniteAdeleRing.ringEquiv_mixedSpace F) a.1 b.1

/- English proof (translation)
The claim follows from `map_mul (InfiniteAdeleRing.ringEquiv_mixedSpace F) a.1 b.1`.
-/
theorem evI_mul (a b : AF F) : evI F (a * b) = evI F a * evI F b :=
  map_mul (InfiniteAdeleRing.ringEquiv_mixedSpace F) a.1 b.1

/- English proof (translation)
Proceed by induction on `(Finset.univ : Finset κ) using Finset.induction_on with`. Consider the case `empty => simp only [Finset.sum_empty]`. Conclude with `map_zero (InfiniteAdeleRing.ringEquiv_mixedSpace F)`. Consider the case `insert j s hj ih => rw [Finset.sum_insert hj, Finset.sum_insert hj, evI_add, ih]`.
-/
theorem evI_sum {κ : Type} [Fintype κ] (g : κ → AF F) : evI F (∑ i, g i) = ∑ i, evI F (g i) := by
  classical
  induction (Finset.univ : Finset κ) using Finset.induction_on with
  | empty => simp only [Finset.sum_empty]; exact map_zero (InfiniteAdeleRing.ringEquiv_mixedSpace F)
  | insert j s hj ih => rw [Finset.sum_insert hj, Finset.sum_insert hj, evI_add, ih]

/- English proof (translation)
The claim follows from `(InfiniteAdeleRing.ringEquiv_mixedSpace F).apply_symm_apply _`.
-/
theorem evI_realAd (t : ℝ) : evI F (realAd F t) = algebraMap ℝ _ t :=
  (InfiniteAdeleRing.ringEquiv_mixedSpace F).apply_symm_apply _

/- English proof (translation)
Establish `h1 : a.1 = 0` using `(map_eq_zero_iff _ (InfiniteAdeleRing.ringEquiv_mixedSpace F).injective).mp ha`. Establish `h2 : (realAd F t).2 = 0` using `rfl`. Use `show ((a.1 * (realAd F t).1, a.2 * (realAd F t).2) : InfiniteAdeleRing F × FiniteAdeleRing (𝓞 F) F) = (0, 0)`. Rewrite using `[h1, h2, zero_mul, mul_zero]`.
-/
theorem mul_realAd_eq_zero {a : AF F} (ha : evI F a = 0) (t : ℝ) : a * realAd F t = 0 := by
  have h1 : a.1 = 0 := (map_eq_zero_iff _ (InfiniteAdeleRing.ringEquiv_mixedSpace F).injective).mp ha
  have h2 : (realAd F t).2 = 0 := rfl
  show ((a.1 * (realAd F t).1, a.2 * (realAd F t).2) : InfiniteAdeleRing F × FiniteAdeleRing (𝓞 F) F) = (0, 0)
  rw [h1, h2, zero_mul, mul_zero]

end GlobalTheory.HeisDeriv

namespace GlobalTheory.HeisDeriv

open scoped Classical

variable {F : Type} [Field F] [NumberField F]

variable (F) in

def trForm {κ : Type} [Fintype κ] (y : κ → AF F) : (κ → mixedEmbedding.mixedSpace F) →L[ℝ] ℝ :=
  LinearMap.toContinuousLinearMap
    ((Algebra.trace ℝ (mixedEmbedding.mixedSpace F)).comp
      (∑ i, (LinearMap.mulRight ℝ (evI F (y i))).comp (LinearMap.proj i)))

/- English proof (translation)
Simplify using `[trForm, LinearMap.sum_apply]`.
-/
theorem trForm_apply {κ : Type} [Fintype κ] (y : κ → AF F) (z : κ → mixedEmbedding.mixedSpace F) :
    trForm F y z = Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (∑ i, z i * evI F (y i)) := by
  simp [trForm, LinearMap.sum_apply]

variable (F) in

def mult {κ : Type} [Fintype κ] (y : κ → AF F) : (κ → mixedEmbedding.mixedSpace F) →L[ℝ] ℂ :=
  (-(2 * Real.pi * Complex.I)) • (Complex.ofRealCLM.comp (trForm F y))

/- English proof (translation)
Simplify using `[mult]`.
-/
theorem mult_apply {κ : Type} [Fintype κ] (y : κ → AF F) (z : κ → mixedEmbedding.mixedSpace F) :
    mult F y z = -(2 * Real.pi * Complex.I) * (trForm F y z : ℂ) := by
  simp [mult]

variable (F) in

def heisD {κ : Type} [Fintype κ] (v : κ → mixedEmbedding.mixedSpace F) (y : κ → AF F) :
    SInf F κ →ₗ[ℂ] SInf F κ :=
  (LineDeriv.lineDerivOpCLM ℂ (SInf F κ) v + SchwartzMap.smulLeftCLM ℂ (⇑(mult F y))).toLinearMap

/- English proof (translation)
Establish `h : (⇑(mult F y)).HasTemperateGrowth` using `(mult F y).hasTemperateGrowth`. Simplify using `[heisD, h, SchwartzMap.lineDerivOp_apply_eq_fderiv]`.
-/
theorem heisD_apply {κ : Type} [Fintype κ] (v : κ → mixedEmbedding.mixedSpace F) (y : κ → AF F) (f : SInf F κ)
    (z : κ → mixedEmbedding.mixedSpace F) :
    heisD F v y f z = fderiv ℝ f z v + mult F y z * f z := by
  have h : (⇑(mult F y)).HasTemperateGrowth := (mult F y).hasTemperateGrowth
  simp [heisD, h, SchwartzMap.lineDerivOp_apply_eq_fderiv]

end GlobalTheory.HeisDeriv

namespace GlobalTheory.HeisDeriv

open scoped Classical
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

variable {F : Type} [Field F] [NumberField F]

/- English proof (translation)
Use `set x₁ := (M.co.e u).1 with hx₁`. Use `set y₁ := (M.co.e u).2 with hy₁`. Use `set v : Fin n × Fin d → mixedEmbedding.mixedSpace F := fun i => evI F (x₁ i) with hv`. Use `⟨heisD F v y₁, fun f r hr x => ?_⟩` and prove the remaining obligations. Use `set z : Fin n × Fin d → mixedEmbedding.mixedSpace F := fun i => evI F (x i) with hz`.

Use `set P : ℝ := trForm F y₁ z with hP`. Use `set Q : ℝ := Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (evI F (⅟(2 : AF F) * (x₁ ⬝ᵥ y₁))) with hQ`. Establish `hline : ∀ t : ℝ, M.heisLine ψ u t (tens (evI F) f r) x = Complex.exp (-(2 * Real.pi * Complex.I) * ((t * (P + t * Q) : ℝ) : ℂ)) * (f (z + t • v) * r x)`. Introduce `t`. Establish `he : M.co.e (realAd F t • u) = realAd F t • M.co.e u` using `map_smul _ _ _`.

Simplify using `only [Model.heisLine, Darboux.rho, he, schr, tens, Prod.smul_fst, Prod.smul_snd, ← hx₁, ← hy₁]`. Establish `hAt1 : At (evI F) (realAd F t • x₁)` using `fun a ha => by`. Rewrite using `[smul_smul, mul_realAd_eq_zero ha, zero_smul]`. Rewrite using `[hr.1 x _ hAt1]`. Use `set A : AF F := x ⬝ᵥ (realAd F t • y₁) + ⅟(2 : AF F) * ((realAd F t • x₁) ⬝ᵥ (realAd F t • y₁)) with hAdef`.

Establish `hA : A = realAd F t * (x ⬝ᵥ y₁ + realAd F t * (⅟(2 : AF F) * (x₁ ⬝ᵥ y₁)))`. Simplify using `only [hAdef, dotProduct_smul, smul_dotProduct, smul_eq_mul]`. Expand and normalize the polynomial expressions, which then agree. Establish `hAt2 : At (evI F) A` using `fun a ha => by`. Rewrite using `[hA, smul_eq_mul, ← mul_assoc, mul_realAd_eq_zero ha, zero_mul]`.

Establish `hxy : evI F (x ⬝ᵥ y₁) = ∑ i, z i * evI F (y₁ i)`. Simplify using `only [dotProduct, evI_sum, evI_mul, hz]`. Establish `htr : Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (evI F A) = t * (P + t * Q)`. Rewrite using `[hA, evI_mul, evI_add, evI_mul, evI_realAd, ← Algebra.smul_def, ← Algebra.smul_def, map_smul, map_add, map_smul, hxy, hP, trForm_apply, hQ, smul_eq_mul, smul_eq_mul]`. Establish `harg : (fun i => evI F ((x + realAd F t • x₁) i)) = z + t • v`.

Use function extensionality and compare the values at `i`. Simplify using `only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, evI_add, evI_mul, evI_realAd, hz, hv]`. Rewrite using `[Algebra.smul_def]`. Rewrite using `[hψ.2.2 A hAt2, htr, harg]`. Establish `h1 : HasDerivAt (fun t : ℝ => t * (P + t * Q)) P 0`.

Use `(hasDerivAt_id (0 : ℝ)).mul ((hasDerivAt_const (0 : ℝ) P).add ((hasDerivAt_id (0 : ℝ)).mul_const Q))` as an intermediate fact. Conclude with `this.congr_deriv (by simp)`. Establish `h2` using `(h1.ofReal_comp.const_mul (-(2 * Real.pi * Complex.I))).cexp`. Establish `h3 : HasDerivAt (fun t : ℝ => z + t • v) v 0`. Simplify using `using ((hasDerivAt_id (0 : ℝ)).smul_const v).const_add z`.

Establish `h4 : HasDerivAt (fun t : ℝ => f (z + t • v)) (fderiv ℝ f z v) 0`. Use `(f.hasFDerivAt (z + (0 : ℝ) • v)).comp_hasDerivAt (0 : ℝ) h3` as an intermediate fact. Simplify `this` using `[Function.comp_def]`. Establish `h5` using `h2.mul (h4.mul_const (r x))`. Use `(h5.congr_deriv ?_).congr_of_eventuallyEq (.of_forall fun t => hline t)` and prove the remaining obligations.

Simplify using `only [tens, heisD_apply, mult_apply, ← hz, ← hP]`. Simplify using the standard rewrite rules. Expand and normalize the polynomial expressions, which then agree.
-/
theorem exists_heisLine_deriv {E : Type} [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
    {n d : ℕ} {X : Spc F E n} {W : Spc F E d} (M : Model σ X W) (ψ : AddChar (AF F) ℂ) (hψ : IsStd ψ)
    (u : Matrix (Fin n) (Fin d) (AE F E)) :
    ∃ D : SInf F (Fin n × Fin d) →ₗ[ℂ] SInf F (Fin n × Fin d), ∀ f : SInf F (Fin n × Fin d),
      ActsD (evI F) (M.heisLine ψ u) f (D f) := by
  set x₁ := (M.co.e u).1 with hx₁
  set y₁ := (M.co.e u).2 with hy₁
  set v : Fin n × Fin d → mixedEmbedding.mixedSpace F := fun i => evI F (x₁ i) with hv
  refine ⟨heisD F v y₁, fun f r hr x => ?_⟩
  set z : Fin n × Fin d → mixedEmbedding.mixedSpace F := fun i => evI F (x i) with hz
  set P : ℝ := trForm F y₁ z with hP
  set Q : ℝ := Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (evI F (⅟(2 : AF F) * (x₁ ⬝ᵥ y₁))) with hQ
  have hline : ∀ t : ℝ, M.heisLine ψ u t (tens (evI F) f r) x =
      Complex.exp (-(2 * Real.pi * Complex.I) * ((t * (P + t * Q) : ℝ) : ℂ)) * (f (z + t • v) * r x) := by
    intro t
    have he : M.co.e (realAd F t • u) = realAd F t • M.co.e u := map_smul _ _ _
    simp only [Model.heisLine, Darboux.rho, he, schr, tens, Prod.smul_fst, Prod.smul_snd, ← hx₁, ← hy₁]
    have hAt1 : At (evI F) (realAd F t • x₁) := fun a ha => by
      rw [smul_smul, mul_realAd_eq_zero ha, zero_smul]
    rw [hr.1 x _ hAt1]
    set A : AF F := x ⬝ᵥ (realAd F t • y₁) + ⅟(2 : AF F) * ((realAd F t • x₁) ⬝ᵥ (realAd F t • y₁)) with hAdef
    have hA : A = realAd F t * (x ⬝ᵥ y₁ + realAd F t * (⅟(2 : AF F) * (x₁ ⬝ᵥ y₁))) := by
      simp only [hAdef, dotProduct_smul, smul_dotProduct, smul_eq_mul]; ring
    have hAt2 : At (evI F) A := fun a ha => by
      rw [hA, smul_eq_mul, ← mul_assoc, mul_realAd_eq_zero ha, zero_mul]
    have hxy : evI F (x ⬝ᵥ y₁) = ∑ i, z i * evI F (y₁ i) := by
      simp only [dotProduct, evI_sum, evI_mul, hz]
    have htr : Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (evI F A) = t * (P + t * Q) := by
      rw [hA, evI_mul, evI_add, evI_mul, evI_realAd, ← Algebra.smul_def, ← Algebra.smul_def, map_smul, map_add,
        map_smul, hxy, hP, trForm_apply, hQ, smul_eq_mul, smul_eq_mul]
    have harg : (fun i => evI F ((x + realAd F t • x₁) i)) = z + t • v := by
      funext i
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, evI_add, evI_mul, evI_realAd, hz, hv]
      rw [Algebra.smul_def]
    rw [hψ.2.2 A hAt2, htr, harg]
  have h1 : HasDerivAt (fun t : ℝ => t * (P + t * Q)) P 0 := by
    have := (hasDerivAt_id (0 : ℝ)).mul ((hasDerivAt_const (0 : ℝ) P).add ((hasDerivAt_id (0 : ℝ)).mul_const Q))
    exact this.congr_deriv (by simp)
  have h2 := (h1.ofReal_comp.const_mul (-(2 * Real.pi * Complex.I))).cexp
  have h3 : HasDerivAt (fun t : ℝ => z + t • v) v 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const v).const_add z
  have h4 : HasDerivAt (fun t : ℝ => f (z + t • v)) (fderiv ℝ f z v) 0 := by
    have := (f.hasFDerivAt (z + (0 : ℝ) • v)).comp_hasDerivAt (0 : ℝ) h3
    simpa [Function.comp_def] using this
  have h5 := h2.mul (h4.mul_const (r x))
  refine (h5.congr_deriv ?_).congr_of_eventuallyEq (.of_forall fun t => hline t)
  simp only [tens, heisD_apply, mult_apply, ← hz, ← hP]
  simp
  ring

end GlobalTheory.HeisDeriv

open GlobalTheory.HeisDeriv in

/- English proof (translation)
Introduce `M ψ hψ u _` and use `exists_heisLine_deriv M ψ hψ u`.
-/
theorem GlobalTheory.HeisDeriv.exists_actsD_heisLine : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
    {n d : ℕ} {X : Spc F E n} {W : Spc F E d} (M : Model σ X W) (ψ : AddChar (AF F) ℂ), IsStd ψ →
    ∀ u : Matrix (Fin n) (Fin d) (AE F E), At (evI F) u →
    ∃ D : SInf F (Fin n × Fin d) →ₗ[ℂ] SInf F (Fin n × Fin d), ∀ f : SInf F (Fin n × Fin d), ActsD (evI F) (M.heisLine ψ u) f (D f) :=
  fun M ψ hψ u _ => exists_heisLine_deriv M ψ hψ u

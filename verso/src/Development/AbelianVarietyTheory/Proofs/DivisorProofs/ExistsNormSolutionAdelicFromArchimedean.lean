import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.NotIsCompactUnivFv
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.Published
open scoped TensorProduct

noncomputable section
namespace GlobalTheory
open Classical

variable (F : Type) [Field F] [NumberField F] (w : InfinitePlace F)

/- English proof (translation)
Use function extensionality and compare the values at `u`. Express the relevant statement in the definitionally equal form `(Pi.single w (a*b) : ∀ v : InfinitePlace F, v.Completion) u = (Pi.single w a : ∀ v : InfinitePlace F, v.Completion) u * (Pi.single w b : ∀ v : InfinitePlace F, v.Completion) u`. Distinguish the cases in `h : u = w`. Substitute `h` using the available equality. Simplify using `only [Pi.single_eq_same]`.

Simplify using `only [Pi.single_eq_of_ne h, mul_zero]`.
-/
theorem ainf_single_mul (a b : w.Completion) :
    (show Ainf F from Pi.single w (a * b)) = (show Ainf F from Pi.single w a) * (show Ainf F from Pi.single w b) := by
  funext u
  change (Pi.single w (a*b) : ∀ v : InfinitePlace F, v.Completion) u =
    (Pi.single w a : ∀ v : InfinitePlace F, v.Completion) u * (Pi.single w b : ∀ v : InfinitePlace F, v.Completion) u
  by_cases h : u = w
  · subst h; simp only [Pi.single_eq_same]
  · simp only [Pi.single_eq_of_ne h, mul_zero]

/- English proof (translation)
Use function extensionality and compare the values at `u`. Express the relevant statement in the definitionally equal form `(e : ∀ v : InfinitePlace F, v.Completion) u * (Pi.single w a : ∀ v : InfinitePlace F, v.Completion) u = (Pi.single w a : ∀ v : InfinitePlace F, v.Completion) u`. Distinguish the cases in `h : u = w`. Substitute `h` using the available equality. Rewrite using `[h1, one_mul]`.

Simplify using `only [Pi.single_eq_of_ne h, mul_zero]`.
-/
theorem ainf_idem_mul (e : Ainf F) (h1 : e w = 1) (h0 : ∀ u, u ≠ w → e u = 0) (a : w.Completion) :
    e * (show Ainf F from Pi.single w a) = (show Ainf F from Pi.single w a) := by
  funext u
  change (e : ∀ v : InfinitePlace F, v.Completion) u * (Pi.single w a : ∀ v : InfinitePlace F, v.Completion) u = (Pi.single w a : ∀ v : InfinitePlace F, v.Completion) u
  by_cases h : u = w
  · subst h; rw [h1, one_mul]
  · simp only [Pi.single_eq_of_ne h, mul_zero]

/- English proof (translation)
Use function extensionality and compare the values at `u`. Express the relevant statement in the definitionally equal form `(Pi.single w 1 : ∀ v : InfinitePlace F, v.Completion) u = e u`. Distinguish the cases in `h : u = w`. Substitute `h` using the available equality. Rewrite using `[h1, Pi.single_eq_same]`.

Rewrite using `[Pi.single_eq_of_ne h, h0 u h]`.
-/
theorem ainf_single_one (e : Ainf F) (h1 : e w = 1) (h0 : ∀ u, u ≠ w → e u = 0) :
    (show Ainf F from Pi.single w 1) = e := by
  funext u
  change (Pi.single w 1 : ∀ v : InfinitePlace F, v.Completion) u = e u
  by_cases h : u = w
  · subst h; rw [h1, Pi.single_eq_same]
  · rw [Pi.single_eq_of_ne h, h0 u h]

/- English proof (translation)
Use extensionality with `v`. Conclude with `congrArg _ (h v)`.
-/
theorem af_zero (y : Af F) (h : ∀ v, evalV F v y = 0) : y = 0 := by
  ext v
  exact congrArg _ (h v)

/- English proof (translation)
The claim follows from `Prod.ext h1 h2`.
-/
theorem af_ext {p q : AF F} (h1 : fstA F p = fstA F q) (h2 : sndA F p = sndA F q) : p = q :=
  Prod.ext h1 h2

def placeAtInf : w.Completion →ₗ[F] AF F :=
  (LinearMap.inl F (Ainf F) (Af F)).comp (LinearMap.single F (fun u : InfinitePlace F => u.Completion) w)

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem fstA_placeAtInf (a : w.Completion) : fstA F (placeAtInf F w a) = (show Ainf F from Pi.single w a) := rfl
/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem sndA_placeAtInf (a : w.Completion) : sndA F (placeAtInf F w a) = 0 := rfl

/- English proof (translation)
Apply `af_ext` to reduce the goal to its premises. Establish `e2 : fstA F (placeAtInf F w a * placeAtInf F w b) = fstA F (placeAtInf F w a) * fstA F (placeAtInf F w b)` using `map_mul (fstA F) _ _`. Conclude with `(fstA_placeAtInf F w (a * b)).trans ((ainf_single_mul F w a b).trans (e2.trans (congrArg₂ (· * ·) (fstA_placeAtInf F w a) (fstA_placeAtInf F w b))).symm)`. Establish `e2 : sndA F (placeAtInf F w a * placeAtInf F w b) = sndA F (placeAtInf F w a) * sndA F (placeAtInf F w b)` using `map_mul (sndA F) _ _`. Conclude with `(sndA_placeAtInf F w (a * b)).trans ((mul_zero (0 : Af F)).symm.trans (e2.trans (congrArg₂ (· * ·) (sndA_placeAtInf F w a) (sndA_placeAtInf F w b))).symm)`.
-/
theorem placeAtInf_mul (a b : w.Completion) :
    placeAtInf F w (a * b) = placeAtInf F w a * placeAtInf F w b := by
  apply af_ext
  · have e2 : fstA F (placeAtInf F w a * placeAtInf F w b) =
        fstA F (placeAtInf F w a) * fstA F (placeAtInf F w b) := map_mul (fstA F) _ _
    exact (fstA_placeAtInf F w (a * b)).trans ((ainf_single_mul F w a b).trans
      (e2.trans (congrArg₂ (· * ·) (fstA_placeAtInf F w a) (fstA_placeAtInf F w b))).symm)
  · have e2 : sndA F (placeAtInf F w a * placeAtInf F w b) =
        sndA F (placeAtInf F w a) * sndA F (placeAtInf F w b) := map_mul (sndA F) _ _
    exact (sndA_placeAtInf F w (a * b)).trans ((mul_zero (0 : Af F)).symm.trans
      (e2.trans (congrArg₂ (· * ·) (sndA_placeAtInf F w a) (sndA_placeAtInf F w b))).symm)

variable {F w}

/- English proof (translation)
Apply `af_ext` to reduce the goal to its premises. Establish `e2 : fstA F (ε * placeAtInf F w a) = fstA F ε * fstA F (placeAtInf F w a)` using `map_mul (fstA F) _ _`. Conclude with `e2.trans ((congrArg (fstA F ε * ·) (fstA_placeAtInf F w a)).trans ((ainf_idem_mul F w _ (hε.1 w (Finset.mem_singleton_self w)) (fun u hu => hε.2.1 u (by simpa using hu)) a).trans (fstA_placeAtInf F w a).symm))`. Establish `e2 : sndA F (ε * placeAtInf F w a) = sndA F ε * sndA F (placeAtInf F w a)` using `map_mul (sndA F) _ _`. Conclude with `e2.trans ((congrArg (sndA F ε * ·) (sndA_placeAtInf F w a)).trans ((mul_zero _).trans (sndA_placeAtInf F w a).symm))`.
-/
theorem idem_mul_placeAtInf {ε : AF F} (hε : IsPlacesIdem {w} ∅ ε) (a : w.Completion) :
    ε * placeAtInf F w a = placeAtInf F w a := by
  apply af_ext
  · have e2 : fstA F (ε * placeAtInf F w a) = fstA F ε * fstA F (placeAtInf F w a) := map_mul (fstA F) _ _
    exact e2.trans ((congrArg (fstA F ε * ·) (fstA_placeAtInf F w a)).trans
      ((ainf_idem_mul F w _ (hε.1 w (Finset.mem_singleton_self w))
        (fun u hu => hε.2.1 u (by simpa using hu)) a).trans (fstA_placeAtInf F w a).symm))
  · have e2 : sndA F (ε * placeAtInf F w a) = sndA F ε * sndA F (placeAtInf F w a) := map_mul (sndA F) _ _
    exact e2.trans ((congrArg (sndA F ε * ·) (sndA_placeAtInf F w a)).trans
      ((mul_zero _).trans (sndA_placeAtInf F w a).symm))

/- English proof (translation)
Apply `af_ext` to reduce the goal to its premises. Use `(fstA_placeAtInf F w 1).trans ?_` and prove the remaining obligations. Conclude with `ainf_single_one F w _ (hε.1 w (Finset.mem_singleton_self w)) (fun u hu => hε.2.1 u (by simpa using hu))`. Use `(sndA_placeAtInf F w 1).trans ?_` and prove the remaining obligations. Conclude with `(af_zero F _ (fun v => hε.2.2.2 v (Finset.notMem_empty v))).symm`.
-/
theorem placeAtInf_one {ε : AF F} (hε : IsPlacesIdem {w} ∅ ε) : placeAtInf F w 1 = ε := by
  apply af_ext
  · refine (fstA_placeAtInf F w 1).trans ?_
    exact ainf_single_one F w _ (hε.1 w (Finset.mem_singleton_self w))
      (fun u hu => hε.2.1 u (by simpa using hu))
  · refine (sndA_placeAtInf F w 1).trans ?_
    exact (af_zero F _ (fun v => hε.2.2.2 v (Finset.notMem_empty v))).symm

variable (F w) (E : Type) [Field E] [Algebra F E]

def placeAtInfE : w.Completion ⊗[F] E →ₗ[F] AF F ⊗[F] E :=
  LinearMap.rTensor E (placeAtInf F w)

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem placeAtInfE_tmul (a : w.Completion) (e : E) :
    placeAtInfE F w E (a ⊗ₜ e) = placeAtInf F w a ⊗ₜ e := rfl

/- English proof (translation)
Proceed by induction on `x using TensorProduct.induction_on with`. Consider the case `zero => rw [zero_mul, map_zero, zero_mul]`. Consider the case `add a b ha hb => rw [add_mul, map_add, map_add, ha, hb, add_mul]`. Consider the case `tmul a e`. Proceed by induction on `y using TensorProduct.induction_on with`.

Consider the case `zero => rw [mul_zero, map_zero, mul_zero]`. Consider the case `add c d hc hd => rw [mul_add, map_add, map_add, hc, hd, mul_add]`. Consider the case `tmul b f`. Unfold `placeAtInfE`. Rewrite using `[Algebra.TensorProduct.tmul_mul_tmul, LinearMap.rTensor_tmul, LinearMap.rTensor_tmul, LinearMap.rTensor_tmul, Algebra.TensorProduct.tmul_mul_tmul, placeAtInf_mul]`.
-/
theorem placeAtInfE_mul (x y : w.Completion ⊗[F] E) :
    placeAtInfE F w E (x * y) = placeAtInfE F w E x * placeAtInfE F w E y := by
  induction x using TensorProduct.induction_on with
  | zero => rw [zero_mul, map_zero, zero_mul]
  | add a b ha hb => rw [add_mul, map_add, map_add, ha, hb, add_mul]
  | tmul a e =>
    induction y using TensorProduct.induction_on with
    | zero => rw [mul_zero, map_zero, mul_zero]
    | add c d hc hd => rw [mul_add, map_add, map_add, hc, hd, mul_add]
    | tmul b f =>
      unfold placeAtInfE
      rw [Algebra.TensorProduct.tmul_mul_tmul, LinearMap.rTensor_tmul, LinearMap.rTensor_tmul,
        LinearMap.rTensor_tmul, Algebra.TensorProduct.tmul_mul_tmul, placeAtInf_mul]

/- English proof (translation)
Proceed by induction on `x using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `add x₁ x₂ h₁ h₂ => simp only [map_add, h₁, h₂]`. Consider the case `tmul a e`. Simplify using `only [sigR, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, Algebra.TensorProduct.map_tmul, AlgHom.coe_id, id_eq, placeAtInfE_tmul]`.
-/
theorem placeAtInfE_sig (σ : E →ₐ[F] E) (x : w.Completion ⊗[F] E) :
    placeAtInfE F w E (sigR w.Completion σ x) = sigR (AF F) σ (placeAtInfE F w E x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add x₁ x₂ h₁ h₂ => simp only [map_add, h₁, h₂]
  | tmul a e =>
    simp only [sigR, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, Algebra.TensorProduct.map_tmul,
      AlgHom.coe_id, id_eq, placeAtInfE_tmul]

variable {F w E}

/- English proof (translation)
Proceed by induction on `x using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `add x₁ x₂ h₁ h₂ => simp only [mul_add, map_add, h₁, h₂]`. Consider the case `tmul a e`. Rewrite using `[placeAtInfE_tmul, Algebra.TensorProduct.algebraMap_apply, Algebra.TensorProduct.tmul_mul_tmul, one_mul, Algebra.algebraMap_self, RingHom.id_apply, idem_mul_placeAtInf hε]`.
-/
theorem idem_mul_placeAtInfE {ε : AF F} (hε : IsPlacesIdem {w} ∅ ε) (x : w.Completion ⊗[F] E) :
    algebraMap (AF F) (AF F ⊗[F] E) ε * placeAtInfE F w E x = placeAtInfE F w E x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add x₁ x₂ h₁ h₂ => simp only [mul_add, map_add, h₁, h₂]
  | tmul a e =>
    rw [placeAtInfE_tmul, Algebra.TensorProduct.algebraMap_apply, Algebra.TensorProduct.tmul_mul_tmul,
      one_mul, Algebra.algebraMap_self, RingHom.id_apply, idem_mul_placeAtInf hε]

/- English proof (translation)
Simplify using `only [inclR, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, Algebra.TensorProduct.includeRight_apply, placeAtInfE_tmul, Algebra.TensorProduct.algebraMap_apply, Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_one, Algebra.algebraMap_self, RingHom.id_apply, placeAtInf_one hε]`.
-/
theorem placeAtInfE_incl {ε : AF F} (hε : IsPlacesIdem {w} ∅ ε) (c : E) :
    placeAtInfE F w E (inclR w.Completion c) = algebraMap (AF F) (AF F ⊗[F] E) ε * inclR (AF F) c := by
  simp only [inclR, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, Algebra.TensorProduct.includeRight_apply,
    placeAtInfE_tmul, Algebra.TensorProduct.algebraMap_apply, Algebra.TensorProduct.tmul_mul_tmul, one_mul,
    mul_one, Algebra.algebraMap_self, RingHom.id_apply, placeAtInf_one hε]

/- English proof (translation)
Introduce `F E _ _ _ _ σ w ε hε c ⟨t, ht⟩`. Use `⟨placeAtInfE F w E t, ?_⟩` and prove the remaining obligations. Rewrite using `[← placeAtInfE_sig, ← placeAtInfE_mul, mul_add, idem_mul_placeAtInfE hε, ← placeAtInfE_incl hε, ← map_add, ht, map_zero]`.
-/
theorem normEq_inf_place : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [Algebra F E] (σ : E →ₐ[F] E)
    (w : InfinitePlace F) (ε : AF F), IsPlacesIdem {w} ∅ ε → ∀ c : E,
    (∃ t : w.Completion ⊗[F] E, t * sigR w.Completion σ t + inclR w.Completion c = 0) →
    ∃ t : AF F ⊗[F] E, algebraMap (AF F) (AF F ⊗[F] E) ε * (t * sigR (AF F) σ t + inclR (AF F) c) = 0 := by
  intro F E _ _ _ _ σ w ε hε c ⟨t, ht⟩
  refine ⟨placeAtInfE F w E t, ?_⟩
  rw [← placeAtInfE_sig, ← placeAtInfE_mul, mul_add, idem_mul_placeAtInfE hε, ← placeAtInfE_incl hε,
    ← map_add, ht, map_zero]

end GlobalTheory

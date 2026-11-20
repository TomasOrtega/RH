import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsPotential
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.OneSubPhiOntoOfFilZero
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BhattScholzeCrystallineLattices
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.ConductorExponents
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ThetaBdRPlusSurjectiveKerUnitsEquivariant
import Development.AbelianVarietyTheory.CrystallinePeriods.RingBasics
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

noncomputable section

namespace GlobalTheory.Prism.PullGal

variable {l : ℕ} [hl : Fact l.Prime]

/- English proof (translation)
Use `WittVector.ext fun n => ?_` and prove the remaining obligations. Simplify using `[galW, mapAlgEquivW, mapEquivW, frobW, WittVector.map_coeff, frobenius_def, map_pow]`.
-/
theorem galW_frobW (g : GQ l) (x : WCb l) : galW l g (frobW l x) = frobW l (galW l g x) := by
  refine WittVector.ext fun n => ?_
  simp [galW, mapAlgEquivW, mapEquivW, frobW, WittVector.map_coeff, frobenius_def, map_pow]

/- English proof (translation)
Rewrite using `[GlobalTheory.RingBasics.θ_σA, ha, map_zero]`.
-/
theorem theta_σA_eq_zero (g : GQ l) (a : Ainf l) (ha : Per.θ l a = 0) : Per.θ l (Per.σA g a) = 0 := by
  rw [GlobalTheory.RingBasics.θ_σA, ha, map_zero]

/- English proof (translation)
Establish `h` using `GlobalTheory.MemLoc.ThetaD.θP_σ l g (algebraMap (Per.Ainf l) (Per.AinfP l) a)`. Rewrite `h` using `[GlobalTheory.RingBasics.awayMap_algebraMap₂, GlobalTheory.MemLoc.ThetaD.fontaineTheta_algebraMap₂, GlobalTheory.MemLoc.ThetaD.fontaineTheta_algebraMap₂]`. Use `h.trans ?_` and prove the remaining obligations. Rewrite using `[ha, GlobalTheory.RingBasics.σC_coe]`.
-/
theorem theta_σA_coe (g : GQ l) (a : Ainf l) (x : Om l) (ha : ((Per.θ l a : OC l) : ℂ_[l]) = (x : ℂ_[l])) :
    ((Per.θ l (Per.σA g a) : OC l) : ℂ_[l]) = ((g x : Om l) : ℂ_[l]) := by
  have h := GlobalTheory.MemLoc.ThetaD.θP_σ l g (algebraMap (Per.Ainf l) (Per.AinfP l) a)
  rw [GlobalTheory.RingBasics.awayMap_algebraMap₂, GlobalTheory.MemLoc.ThetaD.fontaineTheta_algebraMap₂, GlobalTheory.MemLoc.ThetaD.fontaineTheta_algebraMap₂] at h
  refine h.trans ?_
  rw [ha, GlobalTheory.RingBasics.σC_coe]

/- English proof (translation)
Apply `inclW_injective` to reduce the goal to its premises. Rewrite using `[← galW_inclW, ← frobW_inclW, ← frobW_inclW, ← galW_inclW, galW_frobW]`.
-/
theorem σA_frobenius (g : GQ l) (a : Ainf l) :
    Per.σA g (WittVector.frobenius a) = WittVector.frobenius (Per.σA g a) := by
  apply inclW_injective
  rw [← galW_inclW, ← frobW_inclW, ← frobW_inclW, ← galW_inclW, galW_frobW]

def homTo (K : FinExt l) (g : GQ l) (σ : ↥(OL K) →+* ↥(OL K))
    (hσ : ∀ x, (((σ x : ↥K.1) : Om l)) = g ((x : ↥K.1) : Om l)) :
    Hom (ainfObj K) ((ainfObj K).restrict σ) where
  f := Per.σA g
  f_δ := (ainfObj K).D.map_δ_of_map_φ ((ainfObj K).restrict σ).D ainf_torsionFree _ fun a =>
    σA_frobenius g a
  f_I a ha := theta_σA_eq_zero g a ha
  f_str r a h := by
    have h1 := ((isAinf_ainfObj K).mk_eq_str_iff r a).1 h
    refine ((isAinf_ainfObj K).mk_eq_str_iff (σ r) (Per.σA g a)).2 (Subtype.ext ?_)
    refine (theta_σA_coe g a _ ((congrArg Subtype.val h1).trans (coe_intToOC K r))).trans ?_
    rw [coe_intToOC, hσ]

def homFrom (K : FinExt l) (g : GQ l) (σ : ↥(OL K) →+* ↥(OL K))
    (hσ : ∀ x, (((σ x : ↥K.1) : Om l)) = g ((x : ↥K.1) : Om l)) :
    Hom ((ainfObj K).restrict σ) (ainfObj K) where
  f := Per.σA g⁻¹
  f_δ := ((ainfObj K).restrict σ).D.map_δ_of_map_φ (ainfObj K).D ainf_torsionFree _ fun a =>
    σA_frobenius g⁻¹ a
  f_I a ha := theta_σA_eq_zero g⁻¹ a ha
  f_str r a h := by
    have h1 := ((isAinf_ainfObj K).mk_eq_str_iff (σ r) a).1 h
    refine ((isAinf_ainfObj K).mk_eq_str_iff r (Per.σA g⁻¹ a)).2 (Subtype.ext ?_)
    have h2 : ((Per.θ l a : OC l) : ℂ_[l]) = ((g ((r : ↥K.1) : Om l) : Om l) : ℂ_[l]) :=
      (congrArg Subtype.val h1).trans ((coe_intToOC K (σ r)).trans (by rw [hσ]))
    refine (theta_σA_coe g⁻¹ a _ h2).trans ?_
    rw [coe_intToOC, ← AlgEquiv.mul_apply, inv_mul_cancel, AlgEquiv.one_apply]

end GlobalTheory.Prism.PullGal

namespace GlobalTheory.Prism.PullGal

variable {l : ℕ} [hl : Fact l.Prime]

section Tensor

variable {T : Type} [AddCommGroup T] [Module ℤ_[l] T]

/- English proof (translation)
Proceed by induction on `x using TensorProduct.induction_on with`. Consider the case `zero => simp only [smul_zero, map_zero]`. Consider the case `tmul w t`. Rewrite using `[smul_tmul', TensorProduct.map_tmul, TensorProduct.map_tmul, smul_tmul', smul_eq_mul, smul_eq_mul, AlgEquiv.toLinearMap_apply, AlgEquiv.toLinearMap_apply, map_mul]`. Consider the case `add x y hx hy => rw [smul_add, map_add, map_add, hx, hy, smul_add]`.
-/
theorem map_gal_smul (g : GQ l) (r : T →ₗ[ℤ_[l]] T) (c : WCb l) (x : WCb l ⊗[ℤ_[l]] T) :
    TensorProduct.map (galW l g).toLinearMap r (c • x) =
      galW l g c • TensorProduct.map (galW l g).toLinearMap r x := by
  induction x using TensorProduct.induction_on with
  | zero => simp only [smul_zero, map_zero]
  | tmul w t =>
    rw [smul_tmul', TensorProduct.map_tmul, TensorProduct.map_tmul, smul_tmul', smul_eq_mul, smul_eq_mul,
      AlgEquiv.toLinearMap_apply, AlgEquiv.toLinearMap_apply, map_mul]
  | add x y hx hy => rw [smul_add, map_add, map_add, hx, hy, smul_add]

/- English proof (translation)
Proceed by induction on `x using TensorProduct.induction_on with`. Consider the case `zero => simp only [map_zero]`. Consider the case `tmul w t`. Simplify using `only [TensorProduct.map_tmul, AlgHom.toLinearMap_apply, AlgEquiv.toLinearMap_apply, LinearMap.id_apply]`. Rewrite using `[galW_frobW]`.

Consider the case `add x y hx hy => rw [map_add, map_add, map_add, map_add, hx, hy]`.
-/
theorem map_gal_frob (g : GQ l) (r : T →ₗ[ℤ_[l]] T) (x : WCb l ⊗[ℤ_[l]] T) :
    TensorProduct.map (galW l g).toLinearMap r (TensorProduct.map (frobW l).toLinearMap LinearMap.id x) =
      TensorProduct.map (frobW l).toLinearMap LinearMap.id (TensorProduct.map (galW l g).toLinearMap r x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul w t =>
    simp only [TensorProduct.map_tmul, AlgHom.toLinearMap_apply, AlgEquiv.toLinearMap_apply, LinearMap.id_apply]
    rw [galW_frobW]
  | add x y hx hy => rw [map_add, map_add, map_add, map_add, hx, hy]

/- English proof (translation)
Proceed by induction on `x using TensorProduct.induction_on with`. Consider the case `zero => simp only [map_zero]`. Consider the case `tmul w t`. Simplify using `only [TensorProduct.map_tmul, AlgEquiv.toLinearMap_apply, LinearMap.comp_apply, map_mul, AlgEquiv.mul_apply]`. Consider the case `add x y hx hy => rw [map_add, map_add, map_add, hx, hy]`.
-/
theorem map_gal_comp (g g' : GQ l) (r r' : T →ₗ[ℤ_[l]] T) (x : WCb l ⊗[ℤ_[l]] T) :
    TensorProduct.map (galW l g).toLinearMap r (TensorProduct.map (galW l g').toLinearMap r' x) =
      TensorProduct.map (galW l (g * g')).toLinearMap (r ∘ₗ r') x := by
  induction x using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul w t =>
    simp only [TensorProduct.map_tmul, AlgEquiv.toLinearMap_apply, LinearMap.comp_apply, map_mul,
      AlgEquiv.mul_apply]
  | add x y hx hy => rw [map_add, map_add, map_add, hx, hy]

/- English proof (translation)
Rewrite using `[map_gal_comp]`. Proceed by induction on `x using TensorProduct.induction_on with`. Consider the case `zero => simp only [map_zero]`. Consider the case `tmul w t => simp`. Consider the case `add x y hx hy => rw [map_add, hx, hy]`.
-/
theorem map_gal_inv (g : GQ l) (r : T ≃ₗ[ℤ_[l]] T) (x : WCb l ⊗[ℤ_[l]] T) :
    TensorProduct.map (galW l g⁻¹).toLinearMap r.symm.toLinearMap
      (TensorProduct.map (galW l g).toLinearMap r.toLinearMap x) = x := by
  rw [map_gal_comp]
  induction x using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul w t => simp
  | add x y hx hy => rw [map_add, hx, hy]

/- English proof (translation)
Rewrite using `[map_gal_comp]`. Proceed by induction on `x using TensorProduct.induction_on with`. Consider the case `zero => simp only [map_zero]`. Consider the case `tmul w t => simp`. Consider the case `add x y hx hy => rw [map_add, hx, hy]`.
-/
theorem map_gal_inv' (g : GQ l) (r : T ≃ₗ[ℤ_[l]] T) (x : WCb l ⊗[ℤ_[l]] T) :
    TensorProduct.map (galW l g).toLinearMap r.toLinearMap
      (TensorProduct.map (galW l g⁻¹).toLinearMap r.symm.toLinearMap x) = x := by
  rw [map_gal_comp]
  induction x using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul w t => simp
  | add x y hx hy => rw [map_add, hx, hy]

end Tensor

end GlobalTheory.Prism.PullGal

namespace GlobalTheory.Prism.PullGal

variable {l : ℕ} [hl : Fact l.Prime]

/- English proof (translation)
Rewrite using `[← GlobalTheory.RingBasics.σA_mul, inv_mul_cancel, GlobalTheory.RingBasics.σA_one]`.
-/
theorem σA_inv_σA (g : GQ l) (a : Ainf l) : Per.σA g⁻¹ (Per.σA g a) = a := by
  rw [← GlobalTheory.RingBasics.σA_mul, inv_mul_cancel, GlobalTheory.RingBasics.σA_one]

/- English proof (translation)
Rewrite using `[← GlobalTheory.RingBasics.σA_mul, mul_inv_cancel, GlobalTheory.RingBasics.σA_one]`.
-/
theorem σA_σA_inv (g : GQ l) (a : Ainf l) : Per.σA g (Per.σA g⁻¹ a) = a := by
  rw [← GlobalTheory.RingBasics.σA_mul, mul_inv_cancel, GlobalTheory.RingBasics.σA_one]

/- English proof (translation)
The claim follows from `Hom.ext' (RingHom.ext fun a => σA_inv_σA g a)`.
-/
theorem homFrom_comp_homTo (K : FinExt l) (g : GQ l) (σ : ↥(OL K) →+* ↥(OL K))
    (hσ : ∀ x, (((σ x : ↥K.1) : Om l)) = g ((x : ↥K.1) : Om l)) :
    (homFrom K g σ hσ).comp (homTo K g σ hσ) = Hom.id _ :=
  Hom.ext' (RingHom.ext fun a => σA_inv_σA g a)

/- English proof (translation)
The claim follows from `Hom.ext' (RingHom.ext fun a => σA_σA_inv g a)`.
-/
theorem homTo_comp_homFrom (K : FinExt l) (g : GQ l) (σ : ↥(OL K) →+* ↥(OL K))
    (hσ : ∀ x, (((σ x : ↥K.1) : Om l)) = g ((x : ↥K.1) : Om l)) :
    (homTo K g σ hσ).comp (homFrom K g σ hσ) = Hom.id _ :=
  Hom.ext' (RingHom.ext fun a => σA_σA_inv g a)

def Tw (τ : WCb l →+* WCb l) (Q : Type) : Type := Q

instance instAddCommGroupTw (τ : WCb l →+* WCb l) (Q : Type) [AddCommGroup Q] : AddCommGroup (Tw τ Q) :=
  ‹AddCommGroup Q›

instance instModuleTw (τ : WCb l →+* WCb l) (Q : Type) [AddCommGroup Q] [Module (WCb l) Q] :
    Module (WCb l) (Tw τ Q) :=
  Module.compHom Q τ

variable {K : FinExt l} {E : FCrys l ↥(OL K)} {T : Type} [AddCommGroup T] [Module ℤ_[l] T]

def pullJ (j : E.M (ainfObj K) →ₛₗ[(inclW l).comp (ainfId K).toRingHom] (WCb l ⊗[ℤ_[l]] T)) (g : GQ l)
    (σ : ↥(OL K) →+* ↥(OL K)) (hσ : ∀ x, (((σ x : ↥K.1) : Om l)) = g ((x : ↥K.1) : Om l))
    (ρg : T ≃ₗ[ℤ_[l]] T) :
    (E.pullback σ).M (ainfObj K) →ₛₗ[(inclW l).comp (ainfId K).toRingHom] (WCb l ⊗[ℤ_[l]] T) where
  toFun y := TensorProduct.map (galW l g).toLinearMap ρg.toLinearMap (j (E.tr (homFrom K g σ hσ) y))
  map_add' y z := by
    have h1 := map_add (E.tr (homFrom K g σ hσ)) y z
    refine (congrArg (fun w => TensorProduct.map (galW l g).toLinearMap ρg.toLinearMap (j w)) h1).trans ?_
    rw [map_add, map_add]
    rfl
  map_smul' a y := by
    have h1 := LinearMap.map_smulₛₗ (E.tr (homFrom K g σ hσ)) a y
    have h2 := LinearMap.map_smulₛₗ j ((homFrom K g σ hσ).f a) (E.tr (homFrom K g σ hσ) y)
    have h3 := map_gal_smul g ρg.toLinearMap (((inclW l).comp (ainfId K).toRingHom) ((homFrom K g σ hσ).f a))
      (j (E.tr (homFrom K g σ hσ) y))
    have h4 : galW l g (((inclW l).comp (ainfId K).toRingHom) ((homFrom K g σ hσ).f a)) =
        ((inclW l).comp (ainfId K).toRingHom) a :=
      (galW_inclW g _).trans (congrArg (inclW l) (σA_σA_inv g a))
    refine (congrArg (fun w => TensorProduct.map (galW l g).toLinearMap ρg.toLinearMap (j w)) h1).trans ?_
    refine (congrArg _ h2).trans ?_
    exact h3.trans (congrArg (· • _) h4)

end GlobalTheory.Prism.PullGal

namespace GlobalTheory.Prism.PullGal

variable {l : ℕ} [hl : Fact l.Prime]
variable {K : FinExt l} {E : FCrys l ↥(OL K)} {T : Type} [AddCommGroup T] [Module ℤ_[l] T]

/- English proof (translation)
Express the relevant statement in the definitionally equal form `TensorProduct.map (galW l g).toLinearMap ρg.toLinearMap (j (E.tr (homFrom K g σ hσ) (E.tr (homTo K g σ hσ) z))) = _`. Rewrite using `[← E.tr_comp, homFrom_comp_homTo, E.tr_id]`.
-/
theorem pullJ_tr (j : E.M (ainfObj K) →ₛₗ[(inclW l).comp (ainfId K).toRingHom] (WCb l ⊗[ℤ_[l]] T))
    (g : GQ l) (σ : ↥(OL K) →+* ↥(OL K)) (hσ : ∀ x, (((σ x : ↥K.1) : Om l)) = g ((x : ↥K.1) : Om l))
    (ρg : T ≃ₗ[ℤ_[l]] T) (z : E.M (ainfObj K)) :
    pullJ j g σ hσ ρg (E.tr (homTo K g σ hσ) z) =
      TensorProduct.map (galW l g).toLinearMap ρg.toLinearMap (j z) := by
  change TensorProduct.map (galW l g).toLinearMap ρg.toLinearMap
    (j (E.tr (homFrom K g σ hσ) (E.tr (homTo K g σ hσ) z))) = _
  rw [← E.tr_comp, homFrom_comp_homTo, E.tr_id]

/- English proof (translation)
Introduce `Q _ _ v`. Set `τ : WCb l →+* WCb l` to `(galW l g : WCb l →+* WCb l)`. Set `G` to `TensorProduct.map (galW l g).toLinearMap ρg.toLinearMap`. Set `Gi` to `TensorProduct.map (galW l g⁻¹).toLinearMap ρg.symm.toLinearMap`. Set `v₁ : E.M (ainfObj K) →ₛₗ[(inclW l).comp (ainfId K).toRingHom] Tw τ Q` to `{ toFun := fun z => (v (E.tr (homTo K g σ hσ) z) : Q) map_add' := fun z z' => by`.

Establish `h1` using `map_add (E.tr (homTo K g σ hσ)) z z'`. Conclude with `(congrArg v h1).trans (map_add v _ _)`. Use the proof step `map_smul' := fun a z => by`. Establish `h1` using `LinearMap.map_smulₛₗ (E.tr (homTo K g σ hσ)) a z`. Establish `h2` using `LinearMap.map_smulₛₗ v ((homTo K g σ hσ).f a) (E.tr (homTo K g σ hσ) z)`.

Use `(congrArg v h1).trans (h2.trans ?_)` and prove the remaining obligations. Conclude with `congrArg (fun c : WCb l => c • (v (E.tr (homTo K g σ hσ) z) : Q)) (galW_inclW g a).symm }`. Take `⟨w₁, hw₁, hu₁⟩` from `hbc (Tw τ Q) v₁`. Set `w : (WCb l ⊗[ℤ_[l]] T) →ₗ[WCb l] Q` to `{ toFun := fun x => (w₁ (Gi x) : Q) map_add' := fun x y => by`. Express the relevant statement in the definitionally equal form `(w₁ (Gi (x + y)) : Q) = (w₁ (Gi x) : Q) + (w₁ (Gi y) : Q)`.

Rewrite using `[map_add, map_add]`. Use the proof step `map_smul' := fun c x => by`. Express the relevant statement in the definitionally equal form `(show Q from w₁ (Gi (c • x))) = (RingHom.id (WCb l) c) • (show Q from w₁ (Gi x))`. Rewrite using `[RingHom.id_apply, map_gal_smul, w₁.map_smul]`. Express the relevant statement in the definitionally equal form `galW l g (galW l g⁻¹ c) • (show Q from w₁ (Gi x)) = _`.

Rewrite using `[← AlgEquiv.mul_apply, ← map_mul, mul_inv_cancel, map_one, AlgEquiv.one_apply] }`. Use `⟨w, fun y => ?_, fun w' hw' => ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `(w₁ (Gi (G (j (E.tr (homFrom K g σ hσ) y)))) : Q) = v y`. Rewrite using `[map_gal_inv, hw₁]`. Conclude with `congrArg v ((E.tr_comp _ _ y).symm.trans ((congrArg (fun f => E.tr f y) (homTo_comp_homFrom K g σ hσ)).trans (E.tr_id _ y)))`.

Set `w'' : (WCb l ⊗[ℤ_[l]] T) →ₗ[WCb l] Tw τ Q` to `{ toFun := fun x => (w' (G x) : Q) map_add' := fun x y => by`. Express the relevant statement in the definitionally equal form `w' (G (x + y)) = w' (G x) + w' (G y)`. Rewrite using `[map_add, map_add]`. Use the proof step `map_smul' := fun c x => by`. Express the relevant statement in the definitionally equal form `w' (G (c • x)) = galW l g c • w' (G x)`.

Rewrite using `[map_gal_smul, w'.map_smul] }`. Establish `h1 : w'' = w₁` using `hu₁ w'' fun z => by`. Express the relevant statement in the definitionally equal form `w' (G (j z)) = v (E.tr (homTo K g σ hσ) z)`. Rewrite using `[← hw' (E.tr (homTo K g σ hσ) z), pullJ_tr]`. Use `LinearMap.ext fun x => ?_` and prove the remaining obligations.

Express the relevant statement in the definitionally equal form `w' x = (w₁ (Gi x) : Q)`. Rewrite using `[← h1]`. Express the relevant statement in the definitionally equal form `w' x = w' (G (Gi x))`. Rewrite using `[map_gal_inv']`.
-/
theorem semiBC_pullJ (j : E.M (ainfObj K) →ₛₗ[(inclW l).comp (ainfId K).toRingHom] (WCb l ⊗[ℤ_[l]] T))
    (hbc : SemiBC j) (g : GQ l) (σ : ↥(OL K) →+* ↥(OL K))
    (hσ : ∀ x, (((σ x : ↥K.1) : Om l)) = g ((x : ↥K.1) : Om l)) (ρg : T ≃ₗ[ℤ_[l]] T) :
    SemiBC (pullJ j g σ hσ ρg) := by
  intro Q _ _ v
  let τ : WCb l →+* WCb l := (galW l g : WCb l →+* WCb l)
  let G := TensorProduct.map (galW l g).toLinearMap ρg.toLinearMap
  let Gi := TensorProduct.map (galW l g⁻¹).toLinearMap ρg.symm.toLinearMap
  let v₁ : E.M (ainfObj K) →ₛₗ[(inclW l).comp (ainfId K).toRingHom] Tw τ Q :=
    { toFun := fun z => (v (E.tr (homTo K g σ hσ) z) : Q)
      map_add' := fun z z' => by
        have h1 := map_add (E.tr (homTo K g σ hσ)) z z'
        exact (congrArg v h1).trans (map_add v _ _)
      map_smul' := fun a z => by
        have h1 := LinearMap.map_smulₛₗ (E.tr (homTo K g σ hσ)) a z
        have h2 := LinearMap.map_smulₛₗ v ((homTo K g σ hσ).f a) (E.tr (homTo K g σ hσ) z)
        refine (congrArg v h1).trans (h2.trans ?_)
        exact congrArg (fun c : WCb l => c • (v (E.tr (homTo K g σ hσ) z) : Q)) (galW_inclW g a).symm }
  obtain ⟨w₁, hw₁, hu₁⟩ := hbc (Tw τ Q) v₁
  let w : (WCb l ⊗[ℤ_[l]] T) →ₗ[WCb l] Q :=
    { toFun := fun x => (w₁ (Gi x) : Q)
      map_add' := fun x y => by
        change (w₁ (Gi (x + y)) : Q) = (w₁ (Gi x) : Q) + (w₁ (Gi y) : Q)
        rw [map_add, map_add]
      map_smul' := fun c x => by
        change (show Q from w₁ (Gi (c • x))) = (RingHom.id (WCb l) c) • (show Q from w₁ (Gi x))
        rw [RingHom.id_apply, map_gal_smul, w₁.map_smul]
        change galW l g (galW l g⁻¹ c) • (show Q from w₁ (Gi x)) = _
        rw [← AlgEquiv.mul_apply, ← map_mul, mul_inv_cancel, map_one, AlgEquiv.one_apply] }
  refine ⟨w, fun y => ?_, fun w' hw' => ?_⟩
  · change (w₁ (Gi (G (j (E.tr (homFrom K g σ hσ) y)))) : Q) = v y
    rw [map_gal_inv, hw₁]
    exact congrArg v ((E.tr_comp _ _ y).symm.trans
      ((congrArg (fun f => E.tr f y) (homTo_comp_homFrom K g σ hσ)).trans (E.tr_id _ y)))
  · let w'' : (WCb l ⊗[ℤ_[l]] T) →ₗ[WCb l] Tw τ Q :=
      { toFun := fun x => (w' (G x) : Q)
        map_add' := fun x y => by
          change w' (G (x + y)) = w' (G x) + w' (G y)
          rw [map_add, map_add]
        map_smul' := fun c x => by
          change w' (G (c • x)) = galW l g c • w' (G x)
          rw [map_gal_smul, w'.map_smul] }
    have h1 : w'' = w₁ := hu₁ w'' fun z => by
      change w' (G (j z)) = v (E.tr (homTo K g σ hσ) z)
      rw [← hw' (E.tr (homTo K g σ hσ) z), pullJ_tr]
    refine LinearMap.ext fun x => ?_
    change w' x = (w₁ (Gi x) : Q)
    rw [← h1]
    change w' x = w' (G (Gi x))
    rw [map_gal_inv']

end GlobalTheory.Prism.PullGal

namespace GlobalTheory.Prism.PullGal

variable {l : ℕ} [hl : Fact l.Prime]
variable {K : FinExt l} {E : FCrys l ↥(OL K)} {T : Type} [AddCommGroup T] [Module ℤ_[l] T]
  {ρ : ↥(GK K) → (T →ₗ[ℤ_[l]] T)}

/- English proof (translation)
Establish `: IsDomain (ainfObj K).A` using `(ainfId K).toMulEquiv.isDomain`. Use `E.proj (ainfObj K)` as an intermediate fact. Take `⟨d', hd'⟩ : ∃ d' : ↥(ainfObj K).I, (d' : (ainfObj K).A) = (homFrom K g σ hσ).f (d₀ : (ainfObj K).A)` from `⟨⟨_, (homFrom K g σ hσ).f_I _ d₀.2⟩, rfl⟩`. Establish `hσd : Per.σA g (d' : (ainfObj K).A) = (d₀ : (ainfObj K).A)`. Rewrite using `[hd']`.

Conclude with `σA_σA_inv g _`. Establish `hd'0 : (d' : (ainfObj K).A) ≠ 0` using `fun h0 => hd0 (hσd.symm.trans ((congrArg (Per.σA g) h0).trans (map_zero _)))`. Take `⟨n, i, hn⟩` from `exists_isFrac (d' : (ainfObj K).A) (E.Φ (ainfObj K) d' (E.tr (homFrom K g σ hσ) x))`. Take `⟨r, hr⟩` from `E.Φ_nat (homFrom K g σ hσ) d₀ d' x m k n i h hn`. Rewrite `hr` using `[← hd']`.

Establish `heq : (d' : (ainfObj K).A) ^ i • E.tr (homFrom K g σ hσ) m = (d' : (ainfObj K).A) ^ k • n` using `sub_eq_zero.1 ((smul_eq_zero.1 hr).resolve_left (pow_ne_zero _ (mul_ne_zero hd'0 hd'0)))`. Establish `hjn` using `hj.j_φ d' hd'0 (E.tr (homFrom K g σ hσ) x) n i hn`. Establish `hc2 : ∀ i : ℕ, galW l g (inclW l ((ainfId K) (d' : (ainfObj K).A)) ^ i) = inclW l ((ainfId K) (d₀ : (ainfObj K).A)) ^ i` using `fun i => by`. Rewrite using `[map_pow]`. Conclude with `congrArg (· ^ i) ((galW_inclW g _).trans (congrArg (inclW l) hσd))`.

Establish `hc : ∀ i : ℕ, galW l g (((inclW l).comp (ainfId K).toRingHom) ((d' : (ainfObj K).A) ^ i)) = inclW l ((ainfId K) (d₀ : (ainfObj K).A)) ^ i` using `fun i => (congrArg (galW l g) (map_pow ((inclW l).comp (ainfId K).toRingHom) _ i)).trans (hc2 i)`. Establish `hsm : ∀ (a : (ainfObj K).A) (y : E.M (ainfObj K)), TensorProduct.map (galW l g).toLinearMap ρg.toLinearMap (j (a • y)) = galW l g (((inclW l).comp (ainfId K).toRingHom) a) • TensorProduct.map (galW l g).toLinearMap ρg.toLinearMap (j y)` using `fun a y => (congrArg (TensorProduct.map (galW l g).toLinearMap ρg.toLinearMap) (LinearMap.map_smulₛₗ j a y)).trans (map_gal_smul g _ _ _)`. Establish `h5` using `congrArg (TensorProduct.map (galW l g).toLinearMap ρg.toLinearMap) hjn`. Establish `h6` using `(map_gal_smul g ρg.toLinearMap _ _).symm.trans h5`. Establish `e1` using `h6.symm.trans (congrArg₂ (· • ·) (hc2 i) (map_gal_frob g ρg.toLinearMap _))`.

Establish `e2` using `((congrArg₂ (· • ·) (hc i).symm rfl).trans (hsm _ _).symm).trans ((congrArg (fun y => TensorProduct.map (galW l g).toLinearMap ρg.toLinearMap (j y)) heq).trans ((hsm _ _).trans (congrArg₂ (· • ·) (hc k) rfl)))`. Establish `hu : IsUnit (inclW l ((ainfId K) (d₀ : (ainfObj K).A)))` using `(isAinf_ainfObj K).isUnit_inclW hd`. Apply `(hu.pow i).smul_left_cancel.1` to reduce the goal to its premises. Conclude with `(smul_comm _ _ _).trans ((congrArg (_ • ·) e1.symm).trans e2.symm)`.
-/
theorem pullJ_φ {j : E.M (ainfObj K) →ₛₗ[(inclW l).comp (ainfId K).toRingHom] (WCb l ⊗[ℤ_[l]] T)}
    (hj : Realises K E (ainfObj K) (ainfId K) T ρ j) (g : GQ l) (σ : ↥(OL K) →+* ↥(OL K))
    (hσ : ∀ x, (((σ x : ↥K.1) : Om l)) = g ((x : ↥K.1) : Om l)) (ρg : T ≃ₗ[ℤ_[l]] T)
    (d₀ : ↥(ainfObj K).I) (hd : Ideal.span {(d₀ : (ainfObj K).A)} = (ainfObj K).I)
    (hd0 : (d₀ : (ainfObj K).A) ≠ 0) (x m : (E.pullback σ).M (ainfObj K)) (k : ℕ)
    (h : IsFrac (d₀ : (ainfObj K).A) ((E.pullback σ).Φ (ainfObj K) d₀ x) m k) :
    inclW l ((ainfId K) (d₀ : (ainfObj K).A)) ^ k •
        TensorProduct.map (frobW l).toLinearMap LinearMap.id (pullJ j g σ hσ ρg x) =
      pullJ j g σ hσ ρg m := by
  have : IsDomain (ainfObj K).A := (ainfId K).toMulEquiv.isDomain
  have := E.proj (ainfObj K)
  obtain ⟨d', hd'⟩ : ∃ d' : ↥(ainfObj K).I, (d' : (ainfObj K).A) = (homFrom K g σ hσ).f (d₀ : (ainfObj K).A) :=
    ⟨⟨_, (homFrom K g σ hσ).f_I _ d₀.2⟩, rfl⟩
  have hσd : Per.σA g (d' : (ainfObj K).A) = (d₀ : (ainfObj K).A) := by
    rw [hd']; exact σA_σA_inv g _
  have hd'0 : (d' : (ainfObj K).A) ≠ 0 := fun h0 => hd0 (hσd.symm.trans ((congrArg (Per.σA g) h0).trans (map_zero _)))
  obtain ⟨n, i, hn⟩ := exists_isFrac (d' : (ainfObj K).A) (E.Φ (ainfObj K) d' (E.tr (homFrom K g σ hσ) x))
  obtain ⟨r, hr⟩ := E.Φ_nat (homFrom K g σ hσ) d₀ d' x m k n i h hn
  rw [← hd'] at hr
  have heq : (d' : (ainfObj K).A) ^ i • E.tr (homFrom K g σ hσ) m = (d' : (ainfObj K).A) ^ k • n :=
    sub_eq_zero.1 ((smul_eq_zero.1 hr).resolve_left (pow_ne_zero _ (mul_ne_zero hd'0 hd'0)))
  have hjn := hj.j_φ d' hd'0 (E.tr (homFrom K g σ hσ) x) n i hn
  have hc2 : ∀ i : ℕ, galW l g (inclW l ((ainfId K) (d' : (ainfObj K).A)) ^ i) =
      inclW l ((ainfId K) (d₀ : (ainfObj K).A)) ^ i := fun i => by
    rw [map_pow]
    exact congrArg (· ^ i) ((galW_inclW g _).trans (congrArg (inclW l) hσd))
  have hc : ∀ i : ℕ, galW l g (((inclW l).comp (ainfId K).toRingHom) ((d' : (ainfObj K).A) ^ i)) =
      inclW l ((ainfId K) (d₀ : (ainfObj K).A)) ^ i := fun i =>
    (congrArg (galW l g) (map_pow ((inclW l).comp (ainfId K).toRingHom) _ i)).trans (hc2 i)
  have hsm : ∀ (a : (ainfObj K).A) (y : E.M (ainfObj K)),
      TensorProduct.map (galW l g).toLinearMap ρg.toLinearMap (j (a • y)) =
        galW l g (((inclW l).comp (ainfId K).toRingHom) a) •
          TensorProduct.map (galW l g).toLinearMap ρg.toLinearMap (j y) := fun a y =>
    (congrArg (TensorProduct.map (galW l g).toLinearMap ρg.toLinearMap) (LinearMap.map_smulₛₗ j a y)).trans
      (map_gal_smul g _ _ _)
  have h5 := congrArg (TensorProduct.map (galW l g).toLinearMap ρg.toLinearMap) hjn
  have h6 := (map_gal_smul g ρg.toLinearMap _ _).symm.trans h5
  have e1 := h6.symm.trans (congrArg₂ (· • ·) (hc2 i) (map_gal_frob g ρg.toLinearMap _))
  have e2 := ((congrArg₂ (· • ·) (hc i).symm rfl).trans (hsm _ _).symm).trans
    ((congrArg (fun y => TensorProduct.map (galW l g).toLinearMap ρg.toLinearMap (j y)) heq).trans
      ((hsm _ _).trans (congrArg₂ (· • ·) (hc k) rfl)))
  have hu : IsUnit (inclW l ((ainfId K) (d₀ : (ainfObj K).A))) := (isAinf_ainfObj K).isUnit_inclW hd
  apply (hu.pow i).smul_left_cancel.1
  exact (smul_comm _ _ _).trans ((congrArg (_ • ·) e1.symm).trans e2.symm)

end GlobalTheory.Prism.PullGal

namespace GlobalTheory.Prism.PullGal

variable {l : ℕ} [hl : Fact l.Prime]
variable {K : FinExt l} {E : FCrys l ↥(OL K)} {T : Type} [AddCommGroup T] [Module ℤ_[l] T]
  {ρ : ↥(GK K) → (T →ₗ[ℤ_[l]] T)}

/- English proof (translation)
Rewrite using `[← GlobalTheory.RingBasics.σA_mul, ← GlobalTheory.RingBasics.σA_mul]`. Use `congr 1`. Use `group`.
-/
theorem σA_conj (g h : GQ l) (a : Ainf l) : Per.σA g⁻¹ (Per.σA h a) = Per.σA (g⁻¹ * h * g) (Per.σA g⁻¹ a) := by
  rw [← GlobalTheory.RingBasics.σA_mul, ← GlobalTheory.RingBasics.σA_mul]
  congr 1
  group

/- English proof (translation)
Set `h' : ↥(GK K)` to `⟨_, hconj (h : GQ l) h.2⟩`. Establish `hc : (homFrom K g σ hσ).comp (((isAinf_ainfObj K).galHom h).restrict σ) = ((isAinf_ainfObj K).galHom h').comp (homFrom K g σ hσ)` using `Hom.ext' (RingHom.ext fun a => σA_conj g (h : GQ l) a)`. Establish `e0 : E.tr (homFrom K g σ hσ) (E.tr (((isAinf_ainfObj K).galHom h).restrict σ) x) = E.tr ((isAinf_ainfObj K).galHom h') (E.tr (homFrom K g σ hσ) x)` using `(E.tr_comp _ _ x).symm.trans ((congrArg (fun f => E.tr f x) hc).trans (E.tr_comp _ _ x))`. Establish `e1 : g * (h' : GQ l) = (h : GQ l) * g`. Express the relevant statement in the definitionally equal form `g * (g⁻¹ * (h : GQ l) * g) = _`.

Use `group`. Establish `e2 : ρg.toLinearMap ∘ₗ ρ h' = ρ h ∘ₗ ρg.toLinearMap` using `LinearMap.ext fun t => hρg h h' rfl t`. Use `(congrArg (fun y => TensorProduct.map (galW l g).toLinearMap ρg.toLinearMap (j y)) e0).trans ?_` and prove the remaining obligations. Use `(congrArg (TensorProduct.map (galW l g).toLinearMap ρg.toLinearMap) (hj.j_act h' _)).trans ?_` and prove the remaining obligations. Use `(map_gal_comp _ _ _ _ _).trans ?_` and prove the remaining obligations.

Use `Eq.trans ?_ (map_gal_comp _ _ _ _ _).symm` and prove the remaining obligations. Rewrite using `[e1, e2]`.
-/
theorem pullJ_act {j : E.M (ainfObj K) →ₛₗ[(inclW l).comp (ainfId K).toRingHom] (WCb l ⊗[ℤ_[l]] T)}
    (hj : Realises K E (ainfObj K) (ainfId K) T ρ j) (g : GQ l) (σ : ↥(OL K) →+* ↥(OL K))
    (hσ : ∀ x, (((σ x : ↥K.1) : Om l)) = g ((x : ↥K.1) : Om l)) (hconj : ∀ h ∈ GK K, g⁻¹ * h * g ∈ GK K)
    (ρg : T ≃ₗ[ℤ_[l]] T)
    (hρg : ∀ h h' : ↥(GK K), (h' : GQ l) = g⁻¹ * h * g → ∀ x, ρg (ρ h' x) = ρ h (ρg x))
    (h : ↥(GK K)) (x : (E.pullback σ).M (ainfObj K)) :
    pullJ j g σ hσ ρg ((E.pullback σ).tr ((isAinf_ainfObj K).galHom h) x) =
      TensorProduct.map (galW l (h : GQ l)).toLinearMap (ρ h) (pullJ j g σ hσ ρg x) := by
  let h' : ↥(GK K) := ⟨_, hconj (h : GQ l) h.2⟩
  have hc : (homFrom K g σ hσ).comp (((isAinf_ainfObj K).galHom h).restrict σ) =
      ((isAinf_ainfObj K).galHom h').comp (homFrom K g σ hσ) :=
    Hom.ext' (RingHom.ext fun a => σA_conj g (h : GQ l) a)
  have e0 : E.tr (homFrom K g σ hσ) (E.tr (((isAinf_ainfObj K).galHom h).restrict σ) x) =
      E.tr ((isAinf_ainfObj K).galHom h') (E.tr (homFrom K g σ hσ) x) :=
    (E.tr_comp _ _ x).symm.trans ((congrArg (fun f => E.tr f x) hc).trans (E.tr_comp _ _ x))
  have e1 : g * (h' : GQ l) = (h : GQ l) * g := by
    change g * (g⁻¹ * (h : GQ l) * g) = _
    group
  have e2 : ρg.toLinearMap ∘ₗ ρ h' = ρ h ∘ₗ ρg.toLinearMap :=
    LinearMap.ext fun t => hρg h h' rfl t
  refine (congrArg (fun y => TensorProduct.map (galW l g).toLinearMap ρg.toLinearMap (j y)) e0).trans ?_
  refine (congrArg (TensorProduct.map (galW l g).toLinearMap ρg.toLinearMap) (hj.j_act h' _)).trans ?_
  refine (map_gal_comp _ _ _ _ _).trans ?_
  refine Eq.trans ?_ (map_gal_comp _ _ _ _ _).symm
  rw [e1, e2]

end GlobalTheory.Prism.PullGal

namespace GlobalTheory.Prism.PullGal

/- English proof (translation)
Introduce `l _ K E T _ _ ρ j hj g σ hσ hconj ρg hρg`. Use `⟨homTo K g σ hσ, pullJ j g σ hσ ρg, fun _ => rfl, ?_, pullJ_tr j g σ hσ ρg⟩` and prove the remaining obligations. Take `⟨d₀, hd, hd0⟩` from `(isAinf_ainfObj K).exists_generator`. Conclude with `Realises.of_generator (isAinf_ainfObj K) (semiBC_pullJ j hj.bc g σ hσ ρg) d₀ hd (fun x m k h => pullJ_φ hj g σ hσ ρg d₀ hd hd0 x m k h) (fun h x => pullJ_act hj g σ hσ hconj ρg hρg h x)`.
-/
theorem realises_pullback : ∀ {l : ℕ} [Fact l.Prime] (K : FinExt l) (E : FCrys l ↥(OL K)) (T : Type) [AddCommGroup T] [Module ℤ_[l] T] (ρ : ↥(GK K) → (T →ₗ[ℤ_[l]] T)) (j : E.M (ainfObj K) →ₛₗ[(inclW l).comp (ainfId K).toRingHom] (WCb l ⊗[ℤ_[l]] T)), Realises K E (ainfObj K) (ainfId K) T ρ j → ∀ (g : GQ l) (σ : ↥(OL K) →+* ↥(OL K)), (∀ x, (((σ x : ↥K.1) : Om l)) = g ((x : ↥K.1) : Om l)) → (∀ h ∈ GK K, g⁻¹ * h * g ∈ GK K) → ∀ (ρg : T ≃ₗ[ℤ_[l]] T), (∀ h h' : ↥(GK K), (h' : GQ l) = g⁻¹ * h * g → ∀ x, ρg (ρ h' x) = ρ h (ρg x)) → ∃ (gH : Hom (ainfObj K) ((ainfObj K).restrict σ)) (j' : (E.pullback σ).M (ainfObj K) →ₛₗ[(inclW l).comp (ainfId K).toRingHom] (WCb l ⊗[ℤ_[l]] T)), (∀ x, gH.f x = Per.σA g x) ∧ Realises K (E.pullback σ) (ainfObj K) (ainfId K) T ρ j' ∧ ∀ z, j' (E.tr gH z) = TensorProduct.map (galW l g).toLinearMap ρg.toLinearMap (j z) := by
  intro l _ K E T _ _ ρ j hj g σ hσ hconj ρg hρg
  refine ⟨homTo K g σ hσ, pullJ j g σ hσ ρg, fun _ => rfl, ?_, pullJ_tr j g σ hσ ρg⟩
  obtain ⟨d₀, hd, hd0⟩ := (isAinf_ainfObj K).exists_generator
  exact Realises.of_generator (isAinf_ainfObj K) (semiBC_pullJ j hj.bc g σ hσ ρg) d₀ hd
    (fun x m k h => pullJ_φ hj g σ hσ ρg d₀ hd hd0 x m k h)
    (fun h x => pullJ_act hj g σ hσ hconj ρg hρg h x)

end GlobalTheory.Prism.PullGal

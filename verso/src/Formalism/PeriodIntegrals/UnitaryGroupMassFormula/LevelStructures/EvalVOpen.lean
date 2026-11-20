import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LevelStructures.FinProjOpen
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerOrbitVolume.SdUniq

noncomputable section

namespace MassDataLevelSSteps

namespace EvalVW

open scoped TensorProduct
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Measures

/- English proof (translation)
Introduce `U hU`. Rewrite using `[isOpen_iff_forall_mem_open]`. Introduce and unpack `_ ⟨x, hx, rfl⟩`. Set `t : H → G` to `fun y => s y * ((s (π x))⁻¹ * x)`. Establish `ht : Continuous t` using `hs.mul continuous_const`.

Use `⟨t ⁻¹' U, fun y hy => ⟨t y, hy, by simp [t, hπ]⟩, hU.preimage ht, ?_⟩` and prove the remaining obligations. Use `show s (π x) * ((s (π x))⁻¹ * x) ∈ U`. Rewrite using `[mul_inv_cancel_left]` and apply the resulting hypothesis.
-/
theorem isOpenMap_of_section {G H : Type} [Group G] [Group H] [TopologicalSpace G] [TopologicalSpace H]
    [ContinuousMul G] (π : G →* H) (s : H → G) (hs : Continuous s) (hπ : ∀ y, π (s y) = y) :
    IsOpenMap π := by
  intro U hU
  rw [isOpen_iff_forall_mem_open]
  rintro _ ⟨x, hx, rfl⟩

  let t : H → G := fun y => s y * ((s (π x))⁻¹ * x)
  have ht : Continuous t := hs.mul continuous_const
  refine ⟨t ⁻¹' U, fun y hy => ⟨t y, hy, by simp [t, hπ]⟩, hU.preimage ht, ?_⟩
  show s (π x) * ((s (π x))⁻¹ * x) ∈ U
  rwa [mul_inv_cancel_left]

variable {F E : Type} [Field F] [Field E] [Algebra F E]
variable {R R' : Type} [CommRing R] [Algebra F R] [CommRing R'] [Algebra F R']
variable (j : R' →ₗ[F] R)

def Jt : R' ⊗[F] E →ₗ[F] R ⊗[F] E := TensorProduct.map j LinearMap.id

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem Jt_tmul (a : R') (e : E) : Jt (E := E) j (a ⊗ₜ e) = j a ⊗ₜ e := rfl

variable {j}

/- English proof (translation)
Proceed by induction on `x using TensorProduct.induction_on with`. Consider the case `zero => rw [zero_mul, map_zero, zero_mul]`. Consider the case `tmul a e`. Proceed by induction on `y using TensorProduct.induction_on with`. Consider the case `zero => rw [mul_zero, map_zero, mul_zero]`.

Consider the case `tmul b e'`. Rewrite using `[Algebra.TensorProduct.tmul_mul_tmul, Jt_tmul, Jt_tmul, Jt_tmul, hj, Algebra.TensorProduct.tmul_mul_tmul]`. Consider the case `add y y' hy hy' => rw [mul_add, map_add, hy, hy', map_add, mul_add]`. Consider the case `add x x' hx hx' => rw [add_mul, map_add, hx, hx', map_add, add_mul]`.
-/
theorem Jt_mul (hj : ∀ x y, j (x * y) = j x * j y) (x y : R' ⊗[F] E) :
    Jt j (x * y) = Jt j x * Jt j y := by
  induction x using TensorProduct.induction_on with
  | zero => rw [zero_mul, map_zero, zero_mul]
  | tmul a e =>
    induction y using TensorProduct.induction_on with
    | zero => rw [mul_zero, map_zero, mul_zero]
    | tmul b e' =>
      rw [Algebra.TensorProduct.tmul_mul_tmul, Jt_tmul, Jt_tmul, Jt_tmul, hj, Algebra.TensorProduct.tmul_mul_tmul]
    | add y y' hy hy' => rw [mul_add, map_add, hy, hy', map_add, mul_add]
  | add x x' hx hx' => rw [add_mul, map_add, hx, hx', map_add, add_mul]

def eps (j : R' →ₗ[F] R) : R ⊗[F] E := Jt j 1

/- English proof (translation)
Rewrite using `[eps, ← Jt_mul hj, mul_one]`.
-/
theorem Jt_mul_eps (hj : ∀ x y, j (x * y) = j x * j y) (x : R' ⊗[F] E) : Jt j x * eps (E := E) j = Jt j x := by
  rw [eps, ← Jt_mul hj, mul_one]

/- English proof (translation)
Rewrite using `[eps, ← Jt_mul hj, one_mul]`.
-/
theorem eps_mul_Jt (hj : ∀ x y, j (x * y) = j x * j y) (x : R' ⊗[F] E) : eps (E := E) j * Jt j x = Jt j x := by
  rw [eps, ← Jt_mul hj, one_mul]

/- English proof (translation)
The claim follows from `Jt_mul_eps hj 1`.
-/
theorem eps_mul_eps (hj : ∀ x y, j (x * y) = j x * j y) : eps (E := E) j * eps (E := E) j = eps (E := E) j :=
  Jt_mul_eps hj 1

/- English proof (translation)
Use `show Jt j ((1 : R') ⊗ₜ e) = Jt j ((1 : R') ⊗ₜ (1 : E)) * ((1 : R) ⊗ₜ e)`. Rewrite using `[Jt_tmul, Jt_tmul, Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]`.
-/
theorem Jt_inclR (e : E) : Jt j (inclR R' e) = eps (E := E) j * inclR R e := by
  show Jt j ((1 : R') ⊗ₜ e) = Jt j ((1 : R') ⊗ₜ (1 : E)) * ((1 : R) ⊗ₜ e)
  rw [Jt_tmul, Jt_tmul, Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]

/- English proof (translation)
Proceed by induction on `x using TensorProduct.induction_on with`. Consider the case `zero => rw [map_zero, map_zero, map_zero, map_zero]`. Consider the case `tmul a e => show Algebra.TensorProduct.map (AlgHom.id F R) σ (Jt j (a ⊗ₜ e)) = Jt j (Algebra.TensorProduct.map (AlgHom.id F R') σ (a ⊗ₜ e))`. Rewrite using `[Jt_tmul, Algebra.TensorProduct.map_tmul, Algebra.TensorProduct.map_tmul, Jt_tmul]`. Both sides reduce to the same expression.

Consider the case `add x y hx hy => rw [map_add, map_add, hx, hy, map_add, map_add]`.
-/
theorem sigR_Jt (σ : E →ₐ[F] E) (x : R' ⊗[F] E) : sigR R σ (Jt j x) = Jt j (sigR R' σ x) := by
  induction x using TensorProduct.induction_on with
  | zero => rw [map_zero, map_zero, map_zero, map_zero]
  | tmul a e =>
    show Algebra.TensorProduct.map (AlgHom.id F R) σ (Jt j (a ⊗ₜ e)) =
      Jt j (Algebra.TensorProduct.map (AlgHom.id F R') σ (a ⊗ₜ e))
    rw [Jt_tmul, Algebra.TensorProduct.map_tmul, Algebra.TensorProduct.map_tmul, Jt_tmul]
    rfl
  | add x y hx hy => rw [map_add, map_add, hx, hy, map_add, map_add]

/- English proof (translation)
Proceed by induction on `x using TensorProduct.induction_on with`. Consider the case `zero => rw [map_zero, map_zero]`. Consider the case `tmul a e => show Algebra.TensorProduct.map φ (AlgHom.id F E) (Jt j (a ⊗ₜ e)) = a ⊗ₜ e`. Rewrite using `[Jt_tmul, Algebra.TensorProduct.map_tmul, hφ]`. Both sides reduce to the same expression.

Consider the case `add x y hx hy => rw [map_add, map_add, hx, hy]`.
-/
theorem tensMap_Jt (φ : R →ₐ[F] R') (hφ : ∀ x, φ (j x) = x) (x : R' ⊗[F] E) :
    tensMap (E := E) φ (Jt j x) = x := by
  induction x using TensorProduct.induction_on with
  | zero => rw [map_zero, map_zero]
  | tmul a e =>
    show Algebra.TensorProduct.map φ (AlgHom.id F E) (Jt j (a ⊗ₜ e)) = a ⊗ₜ e
    rw [Jt_tmul, Algebra.TensorProduct.map_tmul, hφ]
    rfl
  | add x y hx hy => rw [map_add, map_add, hx, hy]

section Mat

variable {n : ℕ}

def secM (j : R' →ₗ[F] R) (M : Matrix (Fin n) (Fin n) (R' ⊗[F] E)) : Matrix (Fin n) (Fin n) (R ⊗[F] E) :=
  M.map (Jt j) + (1 - eps (E := E) j) • (1 : Matrix (Fin n) (Fin n) (R ⊗[F] E))

variable (hj : ∀ x y, j (x * y) = j x * j y)
include hj

/- English proof (translation)
Use extensionality with `i k`. Simplify using `only [Matrix.map_apply, Matrix.mul_apply, map_sum, Jt_mul hj]`.
-/
theorem mapJ_mul (A B : Matrix (Fin n) (Fin n) (R' ⊗[F] E)) :
    (A * B).map (Jt j) = A.map (Jt j) * B.map (Jt j) := by
  ext i k
  simp only [Matrix.map_apply, Matrix.mul_apply, map_sum, Jt_mul hj]

/- English proof (translation)
Use extensionality with `i k`. Rewrite using `[Matrix.smul_apply, Matrix.map_apply, smul_eq_mul, eps_mul_Jt hj]`.
-/
theorem eps_smul_mapJ (A : Matrix (Fin n) (Fin n) (R' ⊗[F] E)) : eps (E := E) j • A.map (Jt j) = A.map (Jt j) := by
  ext i k
  rw [Matrix.smul_apply, Matrix.map_apply, smul_eq_mul, eps_mul_Jt hj]

/- English proof (translation)
Rewrite using `[sub_smul, one_smul, eps_smul_mapJ hj, sub_self]`.
-/
theorem c_smul_mapJ (A : Matrix (Fin n) (Fin n) (R' ⊗[F] E)) : (1 - eps (E := E) j) • A.map (Jt j) = 0 := by
  rw [sub_smul, one_smul, eps_smul_mapJ hj, sub_self]

/- English proof (translation)
Use extensionality with `i k`. Rewrite using `[Matrix.map_apply, Matrix.smul_apply, smul_eq_mul]`. Conclude with `Jt_inclR (J i k)`.
-/
theorem JR_mapJ (J : Matrix (Fin n) (Fin n) E) : (JR (F := F) R' J).map (Jt j) = eps (E := E) j • JR (F := F) R J := by
  ext i k
  rw [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul]
  exact Jt_inclR (J i k)

/- English proof (translation)
Rewrite using `[mapJ_mul hj, JR_mapJ hj, Matrix.mul_smul, ← Matrix.smul_mul, eps_smul_mapJ hj]`.
-/
theorem mapJ_mul_JR (J : Matrix (Fin n) (Fin n) E) (A : Matrix (Fin n) (Fin n) (R' ⊗[F] E)) :
    A.map (Jt j) * JR (F := F) R J = (A * JR (F := F) R' J).map (Jt j) := by
  rw [mapJ_mul hj, JR_mapJ hj, Matrix.mul_smul, ← Matrix.smul_mul, eps_smul_mapJ hj]

/- English proof (translation)
Rewrite using `[mapJ_mul hj, JR_mapJ hj, Matrix.smul_mul, ← Matrix.mul_smul, eps_smul_mapJ hj]`.
-/
theorem JR_mul_mapJ (J : Matrix (Fin n) (Fin n) E) (A : Matrix (Fin n) (Fin n) (R' ⊗[F] E)) :
    JR (F := F) R J * A.map (Jt j) = (JR (F := F) R' J * A).map (Jt j) := by
  rw [mapJ_mul hj, JR_mapJ hj, Matrix.smul_mul, ← Matrix.mul_smul, eps_smul_mapJ hj]

/- English proof (translation)
Take the linear combination `eps_mul_eps (E := E) hj`.
-/
theorem c_mul_c : (1 - eps (E := E) j) * (1 - eps (E := E) j) = 1 - eps (E := E) j := by
  linear_combination eps_mul_eps (E := E) hj

/- English proof (translation)
Simplify using `only [secM, mapJ_mul hj, add_mul, mul_add, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, Matrix.one_mul, c_smul_mapJ hj, smul_smul, c_mul_c hj, add_zero, zero_add]`.
-/
theorem secM_mul (M N : Matrix (Fin n) (Fin n) (R' ⊗[F] E)) :
    secM j (M * N) = secM j M * secM j N := by
  simp only [secM, mapJ_mul hj, add_mul, mul_add, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, Matrix.one_mul,
    c_smul_mapJ hj, smul_smul, c_mul_c hj, add_zero, zero_add]

/- English proof (translation)
Establish `h1 : (1 : Matrix (Fin n) (Fin n) (R' ⊗[F] E)).map (Jt j) = eps (E` using `E) j • 1 := by`. Use extensionality with `i k`. Rewrite using `[Matrix.map_apply, Matrix.smul_apply, Matrix.one_apply, Matrix.one_apply]`. Apply the tactic sequence `split_ifs <;> simp [eps]`. Rewrite using `[secM, h1, ← add_smul, add_sub_cancel, one_smul]`.
-/
theorem secM_one : secM j (1 : Matrix (Fin n) (Fin n) (R' ⊗[F] E)) = 1 := by
  have h1 : (1 : Matrix (Fin n) (Fin n) (R' ⊗[F] E)).map (Jt j) = eps (E := E) j • 1 := by
    ext i k
    rw [Matrix.map_apply, Matrix.smul_apply, Matrix.one_apply, Matrix.one_apply]
    split_ifs <;> simp [eps]
  rw [secM, h1, ← add_smul, add_sub_cancel, one_smul]

/- English proof (translation)
Establish `hc : sigR R σ (1 - eps (E` using `E) j) = 1 - eps (E := E) j := by`. Rewrite using `[map_sub, map_one, eps, sigR_Jt, map_one]`. Use extensionality with `i k`. Simplify using `only [Formalism.UG.cT, secM, Matrix.transpose_apply, Matrix.map_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, map_add, map_mul, hc, sigR_Jt]`. Break down `eq_or_ne i k with rfl | h` into its components or cases.

Simplify using the standard rewrite rules. Simplify using `[Matrix.one_apply_ne h, Matrix.one_apply_ne (Ne.symm h)]`.
-/
theorem cT_secM (σ : E →ₐ[F] E) (M : Matrix (Fin n) (Fin n) (R' ⊗[F] E)) :
    Formalism.UG.cT (sigR R σ) (secM j M) = secM j (Formalism.UG.cT (sigR R' σ) M) := by
  have hc : sigR R σ (1 - eps (E := E) j) = 1 - eps (E := E) j := by
    rw [map_sub, map_one, eps, sigR_Jt, map_one]
  ext i k
  simp only [Formalism.UG.cT, secM, Matrix.transpose_apply, Matrix.map_apply, Matrix.add_apply, Matrix.smul_apply,
    smul_eq_mul, map_add, map_mul, hc, sigR_Jt]
  rcases eq_or_ne i k with rfl | h
  · simp
  · simp [Matrix.one_apply_ne h, Matrix.one_apply_ne (Ne.symm h)]

/- English proof (translation)
Rewrite using `[cT_secM hj]`. Simplify using `only [secM]`. Rewrite using `[add_mul, Matrix.smul_mul, Matrix.one_mul, mapJ_mul_JR hj, add_mul, mul_add, mul_add, ← mapJ_mul hj, hM, JR_mapJ hj, Matrix.mul_smul, Matrix.mul_one, c_smul_mapJ hj, Matrix.smul_mul, JR_mul_mapJ hj, c_smul_mapJ hj, Matrix.smul_mul, Matrix.mul_smul, Matrix.mul_one, smul_smul, c_mu …`.
-/
theorem secM_unitary (σ : E →ₐ[F] E) (J : Matrix (Fin n) (Fin n) E) (M : Matrix (Fin n) (Fin n) (R' ⊗[F] E))
    (hM : Formalism.UG.cT (sigR R' σ) M * JR (F := F) R' J * M = JR (F := F) R' J) :
    Formalism.UG.cT (sigR R σ) (secM j M) * JR (F := F) R J * secM j M = JR (F := F) R J := by
  rw [cT_secM hj]
  simp only [secM]
  rw [add_mul, Matrix.smul_mul, Matrix.one_mul, mapJ_mul_JR hj, add_mul, mul_add, mul_add, ← mapJ_mul hj, hM,
    JR_mapJ hj, Matrix.mul_smul, Matrix.mul_one, c_smul_mapJ hj, Matrix.smul_mul, JR_mul_mapJ hj, c_smul_mapJ hj,
    Matrix.smul_mul, Matrix.mul_smul, Matrix.mul_one, smul_smul, c_mul_c hj, add_zero, zero_add,
    ← add_smul, add_sub_cancel, one_smul]

end Mat

section Grp

variable {n : ℕ} (σ : E →ₐ[F] E) (J : Matrix (Fin n) (Fin n) E)
variable (hj : ∀ x y, j (x * y) = j x * j y)

def secGL (g : GL (Fin n) (R' ⊗[F] E)) : GL (Fin n) (R ⊗[F] E) where
  val := secM j g
  inv := secM j (g⁻¹ : GL (Fin n) (R' ⊗[F] E))
  val_inv := by rw [← secM_mul hj, Units.mul_inv, secM_one hj]
  inv_val := by rw [← secM_mul hj, Units.inv_mul, secM_one hj]

def secHA (h : HA R' σ J) : HA R σ J :=
  (⟨secGL hj (HA.mat R' σ J h), secM_unitary hj σ J _ (show ↥(HR R' σ J) from h).2⟩ : HR R σ J)

/- English proof (translation)
Apply `Subtype.ext` to reduce the goal to its premises. Apply `Units.ext` to reduce the goal to its premises. Use `show (secM j (HA.mat R' σ J h : Matrix (Fin n) (Fin n) (R' ⊗[F] E))).map (tensMap (E := E) φ) = (HA.mat R' σ J h : Matrix (Fin n) (Fin n) (R' ⊗[F] E))`. Use extensionality with `i k`. Simplify using `[secM, eps, tensMap_Jt φ hφ]`.
-/
theorem haMap_secHA (φ : R →ₐ[F] R') (hφ : ∀ x, φ (j x) = x) (h : HA R' σ J) :
    haMap σ J φ (secHA σ J hj h) = h := by
  apply Subtype.ext
  apply Units.ext
  show (secM j (HA.mat R' σ J h : Matrix (Fin n) (Fin n) (R' ⊗[F] E))).map (tensMap (E := E) φ) =
    (HA.mat R' σ J h : Matrix (Fin n) (Fin n) (R' ⊗[F] E))
  ext i k
  simp [secM, eps, tensMap_Jt φ hφ]

/- English proof (translation)
Use `haveI : ContinuousAdd (R ⊗[F] E) := ModuleTopology.continuousAdd R _`. Conclude with `(continuous_id.matrix_map hc).add continuous_const`.
-/
theorem continuous_secM [TopologicalSpace R] [TopologicalSpace R'] (hc : Continuous (Jt (E := E) j)) :
    Continuous (secM (E := E) (n := n) j) := by
  haveI : ContinuousAdd (R ⊗[F] E) := ModuleTopology.continuousAdd R _
  exact (continuous_id.matrix_map hc).add continuous_const

/- English proof (translation)
Establish `hM : Continuous (secM (E` using `E) (n := n) j) := continuous_secM hc`. Establish `hG : Continuous (fun h : HA R' σ J => secGL hj (HA.mat R' σ J h))` using `Units.continuous_iff.2 ⟨hM.comp (Units.continuous_val.comp continuous_subtype_val), hM.comp (Units.continuous_coe_inv.comp continuous_subtype_val)⟩`. Conclude with `hG.subtype_mk _`.
-/
theorem continuous_secHA [TopologicalSpace R] [TopologicalSpace R'] (hc : Continuous (Jt (E := E) j)) :
    Continuous (secHA σ J hj) := by
  have hM : Continuous (secM (E := E) (n := n) j) := continuous_secM hc
  have hG : Continuous (fun h : HA R' σ J => secGL hj (HA.mat R' σ J h)) :=
    Units.continuous_iff.2 ⟨hM.comp (Units.continuous_val.comp continuous_subtype_val),
      hM.comp (Units.continuous_coe_inv.comp continuous_subtype_val)⟩
  exact hG.subtype_mk _

end Grp

end EvalVW

end MassDataLevelSSteps

namespace MassDataLevelSSteps

namespace EvalVSpec

open scoped TensorProduct
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Measures
open Formalism.MainNotions.S (AutInst)

variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E]

open Classical in

def singleL (v : HeightOneSpectrum (𝓞 F)) : Fv F v →ₗ[F] Af F where
  toFun := singleV F v
  map_add' x y := by
    unfold singleV
    exact RestrictedProduct.single_add _ v x y
  map_smul' c x := by
    simp only [RingHom.id_apply, Algebra.smul_def]
    unfold singleV
    exact RestrictedProduct.mul_single _ v x (algebraMap F (Af F) c)

open Classical in
/- English proof (translation)
Unfold `singleV`. Conclude with `RestrictedProduct.single_eq_same _ v x`.
-/
theorem singleV_self (v : HeightOneSpectrum (𝓞 F)) (x : Fv F v) : (singleV F v x) v = x := by
  unfold singleV
  exact RestrictedProduct.single_eq_same _ v x

open Classical in
/- English proof (translation)
Establish `h` using `RestrictedProduct.single_mul (fun w : HeightOneSpectrum (𝓞 F) => w.adicCompletionIntegers F) v x (singleV F v y)`. Establish `e : x * y = x * (singleV F v y) v` using `by rw [singleV_self]`. Conclude with `(congrArg (singleV F v) e).trans h`.
-/
theorem singleL_mul (v : HeightOneSpectrum (𝓞 F)) (x y : Fv F v) :
    singleL v (x * y) = singleL v x * singleL v y := by
  have h := RestrictedProduct.single_mul (fun w : HeightOneSpectrum (𝓞 F) => w.adicCompletionIntegers F) v x
    (singleV F v y)
  have e : x * y = x * (singleV F v y) v := by rw [singleV_self]
  exact (congrArg (singleV F v) e).trans h

/- English proof (translation)
The claim follows from `singleV_self v x`.
-/
theorem evalV_singleL (v : HeightOneSpectrum (𝓞 F)) (x : Fv F v) : evalV F v (singleL v x) = x :=
  singleV_self v x

def uHom (v : HeightOneSpectrum (𝓞 F)) : Fv F v →* Af F where
  toFun a := singleL v a + (1 - singleL v 1)
  map_one' := add_sub_cancel _ _
  map_mul' a b := by
    have hab := singleL_mul v a b
    have h1 : singleL v a * singleL v 1 = singleL v a := by rw [← singleL_mul, mul_one]
    have h2 : singleL v b * singleL v 1 = singleL v b := by rw [← singleL_mul, mul_one]
    have h3 : singleL v (1 : Fv F v) * singleL v 1 = singleL v 1 := by rw [← singleL_mul, mul_one]
    linear_combination hab + h1 + h2 - h3

/- English proof (translation)
The claim follows from `(PI.VolStabSW.SdUniqW.continuous_singleV v).add continuous_const`.
-/
theorem continuous_uHom (v : HeightOneSpectrum (𝓞 F)) : Continuous (uHom v) :=
  (PI.VolStabSW.SdUniqW.continuous_singleV v).add continuous_const

/- English proof (translation)
Use `show (singleL v a + (1 - singleL v 1)) * singleL v b = singleL v (a * b)`. Rewrite using `[add_mul, sub_mul, one_mul, ← singleL_mul, ← singleL_mul, one_mul, sub_self, add_zero]`.
-/
theorem uHom_mul_single (v : HeightOneSpectrum (𝓞 F)) (a b : Fv F v) :
    uHom v a * singleL v b = singleL v (a * b) := by
  show (singleL v a + (1 - singleL v 1)) * singleL v b = singleL v (a * b)
  rw [add_mul, sub_mul, one_mul, ← singleL_mul, ← singleL_mul, one_mul, sub_self, add_zero]

/- English proof (translation)
Proceed by induction on `z using TensorProduct.induction_on with`. Consider the case `zero => rw [smul_zero, map_zero, smul_zero]`. Consider the case `tmul b e`. Rewrite using `[TensorProduct.smul_tmul', EvalVW.Jt_tmul, EvalVW.Jt_tmul, TensorProduct.smul_tmul', smul_eq_mul, smul_eq_mul, uHom_mul_single]`. Consider the case `add x y hx hy => rw [smul_add, map_add, hx, hy, map_add, smul_add]`.
-/
theorem Jt_smul (v : HeightOneSpectrum (𝓞 F)) (a : Fv F v) (z : Fv F v ⊗[F] E) :
    EvalVW.Jt (singleL v) (a • z) = uHom v a • EvalVW.Jt (singleL v) z := by
  induction z using TensorProduct.induction_on with
  | zero => rw [smul_zero, map_zero, smul_zero]
  | tmul b e =>
    rw [TensorProduct.smul_tmul', EvalVW.Jt_tmul, EvalVW.Jt_tmul, TensorProduct.smul_tmul', smul_eq_mul, smul_eq_mul,
      uHom_mul_single]
  | add x y hx hy => rw [smul_add, map_add, hx, hy, map_add, smul_add]

/- English proof (translation)
Set `τ : TopologicalSpace (Fv F v ⊗[F] E)` to `TopologicalSpace.induced (EvalVW.Jt (E := E) (singleL v)) inferInstance`. Use `haveI : ContinuousSMul (Af F) (Af F ⊗[F] E) := ModuleTopology.continuousSMul _ _`. Use `haveI : ContinuousAdd (Af F ⊗[F] E) := ModuleTopology.continuousAdd _ _`. Establish `h1 : @ContinuousSMul (Fv F v) (Fv F v ⊗[F] E) _ _ τ`. Use `letI := τ`.

Use `⟨continuous_induced_rng.2 ?_⟩` and prove the remaining obligations. Establish `e : (EvalVW.Jt (E` using `E) (singleL v)) ∘ (fun p : Fv F v × (Fv F v ⊗[F] E) => p.1 • p.2) = fun p => uHom v p.1 • EvalVW.Jt (E := E) (singleL v) p.2 := funext fun p => Jt_smul v p.1 p.2`. Rewrite using `[e]`. Conclude with `((continuous_uHom v).comp continuous_fst).smul (continuous_induced_dom.comp continuous_snd)`. Establish `h2 : @ContinuousAdd (Fv F v ⊗[F] E) τ _`.

Use `letI := τ`. Use `⟨continuous_induced_rng.2 ?_⟩` and prove the remaining obligations. Establish `e : (EvalVW.Jt (E` using `E) (singleL v)) ∘ (fun p : (Fv F v ⊗[F] E) × (Fv F v ⊗[F] E) => p.1 + p.2) = fun p => EvalVW.Jt (E := E) (singleL v) p.1 + EvalVW.Jt (E := E) (singleL v) p.2 :=`. Use function extensionality and compare the values at `fun p => map_add _ _ _`. Rewrite using `[e]`.

Conclude with `(continuous_induced_dom.comp continuous_fst).add (continuous_induced_dom.comp continuous_snd)`. Conclude with `continuous_iff_le_induced.2 (sInf_le ⟨h1, h2⟩)`.
-/
theorem continuous_Jt_single (v : HeightOneSpectrum (𝓞 F)) :
    Continuous (EvalVW.Jt (E := E) (singleL v)) := by

  let τ : TopologicalSpace (Fv F v ⊗[F] E) := TopologicalSpace.induced (EvalVW.Jt (E := E) (singleL v)) inferInstance
  haveI : ContinuousSMul (Af F) (Af F ⊗[F] E) := ModuleTopology.continuousSMul _ _
  haveI : ContinuousAdd (Af F ⊗[F] E) := ModuleTopology.continuousAdd _ _
  have h1 : @ContinuousSMul (Fv F v) (Fv F v ⊗[F] E) _ _ τ := by
    letI := τ
    refine ⟨continuous_induced_rng.2 ?_⟩
    have e : (EvalVW.Jt (E := E) (singleL v)) ∘ (fun p : Fv F v × (Fv F v ⊗[F] E) => p.1 • p.2) =
        fun p => uHom v p.1 • EvalVW.Jt (E := E) (singleL v) p.2 := funext fun p => Jt_smul v p.1 p.2
    rw [e]
    exact ((continuous_uHom v).comp continuous_fst).smul (continuous_induced_dom.comp continuous_snd)
  have h2 : @ContinuousAdd (Fv F v ⊗[F] E) τ _ := by
    letI := τ
    refine ⟨continuous_induced_rng.2 ?_⟩
    have e : (EvalVW.Jt (E := E) (singleL v)) ∘ (fun p : (Fv F v ⊗[F] E) × (Fv F v ⊗[F] E) => p.1 + p.2) =
        fun p => EvalVW.Jt (E := E) (singleL v) p.1 + EvalVW.Jt (E := E) (singleL v) p.2 :=
      funext fun p => map_add _ _ _
    rw [e]
    exact (continuous_induced_dom.comp continuous_fst).add (continuous_induced_dom.comp continuous_snd)
  exact continuous_iff_le_induced.2 (sInf_le ⟨h1, h2⟩)

end EvalVSpec

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Measures NumberField IsDedekindDomain
open Formalism.MainNotions.S (AutInst)
open scoped TensorProduct

/- English proof (translation)
Introduce `I v`. Conclude with `EvalVW.isOpenMap_of_section _ (EvalVW.secHA I.cm.sig I.J (EvalVSpec.singleL_mul v)) (EvalVW.continuous_secHA I.cm.sig I.J _ (EvalVSpec.continuous_Jt_single v)) (EvalVW.haMap_secHA I.cm.sig I.J (EvalVSpec.singleL_mul v) (evalV I.F v) (EvalVSpec.evalV_singleL v))`.
-/
theorem evalVOpen_holds : EvalVOpen := by
  intro I v
  exact EvalVW.isOpenMap_of_section _ (EvalVW.secHA I.cm.sig I.J (EvalVSpec.singleL_mul v))
    (EvalVW.continuous_secHA I.cm.sig I.J _ (EvalVSpec.continuous_Jt_single v))
    (EvalVW.haMap_secHA I.cm.sig I.J (EvalVSpec.singleL_mul v) (evalV I.F v) (EvalVSpec.evalV_singleL v))

/- English proof (translation)
The claim follows from `haarIdxGlob_of_finProj finProjOpen_holds`.
-/
theorem haarIdxGlob_holds : HaarIdxGlob :=
  haarIdxGlob_of_finProj finProjOpen_holds

/- English proof (translation)
The claim follows from `haarIdxLoc_of_open finProjOpen_holds evalVOpen_holds`.
-/
theorem haarIdxLoc_holds : HaarIdxLoc :=
  haarIdxLoc_of_open finProjOpen_holds evalVOpen_holds

end MassDataLevelSSteps

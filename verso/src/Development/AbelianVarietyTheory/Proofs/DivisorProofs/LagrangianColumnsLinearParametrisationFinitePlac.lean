import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiagWZero
import Development.AbelianVarietyTheory.Definitions.Divisors.RankEqCardIffExistsFrameMatrixFirstColumnBlock
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeisenbergInvariantFormVanishesLagrangianTest
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels MeasureTheory GlobalTheory.LatVac GlobalTheory.InertVacLag GlobalTheory.InertLagChar
open scoped TensorProduct Matrix GlobalTheory.VacAny
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.InertLagParam

open GlobalTheory.LatVac GlobalTheory.InertVacLag GlobalTheory.InertLagUniq

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

abbrev lift (v : Pl F) : Fv F v ⊗[F] E →ₗ[F] AE F E := (liftV v).rTensor E

/- English proof (translation)
Proceed by induction on `t using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `tmul x e => simp [compFin, evFin_liftV]`. Consider the case `add x y hx hy => rw [map_add, map_add, hx, hy]`.
-/
theorem compFin_lift (v : Pl F) (t : Fv F v ⊗[F] E) : compFin F E v (lift v t) = t := by
  induction t using TensorProduct.induction_on with
  | zero => simp
  | tmul x e => simp [compFin, evFin_liftV]
  | add x y hx hy => rw [map_add, map_add, hx, hy]

/- English proof (translation)
Proceed by induction on `a using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `tmul x e`. Rewrite using `[TensorProduct.smul_tmul', smul_eq_mul, liftV_one_mul]`. Simplify using `[compFin]`.

Consider the case `add x y hx hy => rw [smul_add, hx, hy, map_add, map_add]`.
-/
theorem liftV_one_smul_eq (v : Pl F) (a : AE F E) : liftV v (1 : Fv F v) • a = lift v (compFin F E v a) := by
  induction a using TensorProduct.induction_on with
  | zero => simp
  | tmul x e =>
    rw [TensorProduct.smul_tmul', smul_eq_mul, liftV_one_mul]
    simp [compFin]
  | add x y hx hy => rw [smul_add, hx, hy, map_add, map_add]

/- English proof (translation)
Proceed by induction on `a using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `tmul x e`. Rewrite using `[TensorProduct.smul_tmul', smul_eq_mul]`. Simplify using `[compFin, TensorProduct.smul_tmul']`.

Consider the case `add x y hx hy => rw [smul_add, map_add, hx, hy, map_add, smul_add]`.
-/
theorem compFin_smul (v : Pl F) (r : AF F) (a : AE F E) : compFin F E v (r • a) = evFin F v r • compFin F E v a := by
  induction a using TensorProduct.induction_on with
  | zero => simp
  | tmul x e =>
    rw [TensorProduct.smul_tmul', smul_eq_mul]
    simp [compFin, TensorProduct.smul_tmul']
  | add x y hx hy => rw [smul_add, map_add, hx, hy, map_add, smul_add]

/- English proof (translation)
Introduce `u hu`. Use extensionality with `i k`. Simplify using `only [Matrix.smul_apply, Matrix.map_apply, Matrix.zero_apply]`. Proceed by induction on `A i k using TensorProduct.induction_on with`. Consider the case `zero => simp`.

Consider the case `tmul x e`. Simplify using `only [LinearMap.rTensor_tmul, TensorProduct.smul_tmul', smul_eq_mul]`. Rewrite using `[← smul_eq_mul, at_liftV v x u hu, TensorProduct.zero_tmul]`. Consider the case `add x y hx hy => rw [map_add, smul_add, hx, hy, add_zero]`.
-/
theorem at_map_lift {α β : Type} (v : Pl F) (A : Matrix α β (Fv F v ⊗[F] E)) : At (evFin F v) (A.map (lift v)) := by
  intro u hu
  ext i k
  simp only [Matrix.smul_apply, Matrix.map_apply, Matrix.zero_apply]
  induction A i k using TensorProduct.induction_on with
  | zero => simp
  | tmul x e =>
    simp only [LinearMap.rTensor_tmul, TensorProduct.smul_tmul', smul_eq_mul]
    rw [← smul_eq_mul, at_liftV v x u hu, TensorProduct.zero_tmul]
  | add x y hx hy => rw [map_add, smul_add, hx, hy, add_zero]

/- English proof (translation)
Use `conv_lhs => rw [← liftV_one_smul v z hz]`. Use extensionality with `i k`. Simplify using `only [Matrix.smul_apply, Matrix.map_apply, liftV_one_smul_eq]`.
-/
theorem eq_map_lift {α β : Type} (v : Pl F) (z : Matrix α β (AE F E)) (hz : At (evFin F v) z) :
    z = (z.map (compFin F E v)).map (lift v) := by
  conv_lhs => rw [← liftV_one_smul v z hz]
  ext i k
  simp only [Matrix.smul_apply, Matrix.map_apply, liftV_one_smul_eq]

/- English proof (translation)
Use extensionality with `i k`. Simplify using `[compFin_lift]`.
-/
theorem map_lift_compFin {α β : Type} (v : Pl F) (A : Matrix α β (Fv F v ⊗[F] E)) :
    (A.map (lift v)).map (compFin F E v) = A := by
  ext i k; simp [compFin_lift]

end GlobalTheory.InertLagParam
end

namespace GlobalTheory.InertLagParam
open GlobalTheory.LatVac GlobalTheory.InertVacLag GlobalTheory.InertLagUniq
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

/- English proof (translation)
Set `f : (β → R) ≃ₗ[R] (α → R)` to `LinearEquiv.ofLinear (Matrix.toLin' A) (Matrix.toLin' B) (by rw [← Matrix.toLin'_mul, h1, Matrix.toLin'_one]) (by rw [← Matrix.toLin'_mul, h2, Matrix.toLin'_one])`. Use `f.finrank_eq` as an intermediate fact. Rewrite `this` using `[Module.finrank_fintype_fun_eq_card, Module.finrank_fintype_fun_eq_card]`. Conclude with `this.symm`.
-/
theorem card_eq_of_inv {R : Type} [CommRing R] [Nontrivial R] {α β : Type} [Fintype α] [Fintype β] [DecidableEq α]
    [DecidableEq β] (A : Matrix α β R) (B : Matrix β α R) (h1 : A * B = 1) (h2 : B * A = 1) :
    Fintype.card α = Fintype.card β := by
  let f : (β → R) ≃ₗ[R] (α → R) := LinearEquiv.ofLinear (Matrix.toLin' A) (Matrix.toLin' B)
    (by rw [← Matrix.toLin'_mul, h1, Matrix.toLin'_one]) (by rw [← Matrix.toLin'_mul, h2, Matrix.toLin'_one])
  have := f.finrank_eq
  rw [Module.finrank_fintype_fun_eq_card, Module.finrank_fintype_fun_eq_card] at this
  exact this.symm

/- English proof (translation)
Establish `h1 : co.e u = liftV v (1 : Fv F v) • co.e u` using `by rw [← LinearEquiv.map_smul, liftV_one_smul v u hu]`. Establish `h2 : co.e u = 0`. Rewrite using `[h1]`. Use `Prod.ext (funext fun k => ?_) (funext fun k => ?_)` and prove the remaining obligations. Use `congrArg (fun p => p.1 k) h0` as an intermediate fact.

Simplify using `only [locCo, AddMonoidHom.coe_mk, ZeroHom.coe_mk, Prod.fst_zero, Pi.zero_apply] at this`. Simplify using `[liftV_one_mul, this]`. Use `congrArg (fun p => p.2 k) h0` as an intermediate fact. Simplify using `only [locCo, AddMonoidHom.coe_mk, ZeroHom.coe_mk, Prod.snd_zero, Pi.zero_apply] at this`. Simplify using `[liftV_one_mul, this]`.

Conclude with `co.e.map_eq_zero_iff.1 h2`.
-/
theorem eq_zero_of_locCo {W : Type} [AddCommGroup W] [Module (AF F) W] {B : W → W → AF F} {κ : Type} [Fintype κ]
    (co : Darboux B κ) (v : Pl F) (u : W) (hu : At (evFin F v) u) (h0 : locCo co v u = 0) : u = 0 := by
  have h1 : co.e u = liftV v (1 : Fv F v) • co.e u := by rw [← LinearEquiv.map_smul, liftV_one_smul v u hu]
  have h2 : co.e u = 0 := by
    rw [h1]
    refine Prod.ext (funext fun k => ?_) (funext fun k => ?_)
    · have := congrArg (fun p => p.1 k) h0
      simp only [locCo, AddMonoidHom.coe_mk, ZeroHom.coe_mk, Prod.fst_zero, Pi.zero_apply] at this
      simp [liftV_one_mul, this]
    · have := congrArg (fun p => p.2 k) h0
      simp only [locCo, AddMonoidHom.coe_mk, ZeroHom.coe_mk, Prod.snd_zero, Pi.zero_apply] at this
      simp [liftV_one_mul, this]
  exact co.e.map_eq_zero_iff.1 h2

end GlobalTheory.InertLagParam

namespace GlobalTheory.InertLagParam

def mulLeft {R : Type} [CommRing R] (n m : ℕ) (A : Matrix (Fin n) (Fin n) R) :
    Matrix (Fin n) (Fin m) R →ₗ[R] Matrix (Fin n) (Fin m) R where
  toFun x := A * x
  map_add' x y := Matrix.mul_add A x y
  map_smul' c x := Matrix.mul_smul A c x

/- English proof (translation)
Set `τ : Matrix (Fin n) (Fin m) R ≃ₗ[R] (Fin m → Fin n → R)` to `{ toFun := fun x k i => x i k invFun := fun y => Matrix.of fun i k => y k i map_add' := fun _ _ => rfl map_smul' := fun _ _ => rfl left_inv := fun _ => rfl right_inv := fun _ => rfl }`. Establish `h : (τ : _ →ₗ[R] _) ∘ₗ mulLeft n m A ∘ₗ (τ.symm : (Fin m → Fin n → R) →ₗ[R] _) = LinearMap.pi fun k : Fin m => Matrix.toLin' A ∘ₗ LinearMap.proj k`. Use `LinearMap.ext fun y => ?_` and prove the remaining obligations. Use function extensionality and compare the values at `k i`. Both sides reduce to the same expression.

Rewrite using `[← LinearMap.det_conj (mulLeft n m A) τ, h, LinearMap.det_pi]`. Simplify using `[LinearMap.det_toLin']`.
-/
theorem det_mulLeft {R : Type} [CommRing R] (n m : ℕ) (A : Matrix (Fin n) (Fin n) R) :
    LinearMap.det (mulLeft n m A) = A.det ^ m := by
  let τ : Matrix (Fin n) (Fin m) R ≃ₗ[R] (Fin m → Fin n → R) :=
    { toFun := fun x k i => x i k
      invFun := fun y => Matrix.of fun i k => y k i
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  have h : (τ : _ →ₗ[R] _) ∘ₗ mulLeft n m A ∘ₗ (τ.symm : (Fin m → Fin n → R) →ₗ[R] _) =
      LinearMap.pi fun k : Fin m => Matrix.toLin' A ∘ₗ LinearMap.proj k := by
    refine LinearMap.ext fun y => ?_
    funext k i
    rfl
  rw [← LinearMap.det_conj (mulLeft n m A) τ, h, LinearMap.det_pi]
  simp [LinearMap.det_toLin']

end GlobalTheory.InertLagParam

namespace GlobalTheory.InertLagParam
open GlobalTheory.LatVac GlobalTheory.InertVacLag GlobalTheory.InertLagUniq

/- English proof (translation)
Introduce `F E _ _ _ _ _ σ n d X W M v m C hC`. Take `⟨h0, Cx, P, hx, h1, h2⟩` from `hC`. Establish `hP1 : P.toRows₁ * C.map (compFin F E v) = 1`. Establish `h2'` using `h2`. Rewrite `h2'` using `[← Matrix.fromRows_toRows P, Matrix.fromRows_mul_fromCols, ← Matrix.fromBlocks_one, Matrix.fromBlocks_inj]`.

Conclude with `h2'.1`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Use `card_eq_of_inv _ _ h1 h2` as an intermediate fact. Simplify using `only [Fintype.card_fin, Fintype.card_sum] at this`. Use linear arithmetic over natural numbers and integers.

Set `Z` to `Matrix (Fin n) (Fin m) (Fv F v ⊗[F] E)`. Set `N` to `Module.finrank (Fv F v) Z`. Set `e : (Fin N → Fv F v) ≃ₗ[Fv F v] Z` to `(Module.finBasis (Fv F v) Z).equivFun.symm`. Set `ζ : (Fin N → Fv F v) → Matrix (Fin n) (Fin m) (AE F E)` to `fun y => (e y).map (lift v)`. Establish `hζat : ∀ y, At (evFin F v) (ζ y)` using `fun y => at_map_lift v _`.

Establish `hζc : ∀ y, (ζ y).map (compFin F E v) = e y` using `fun y => map_lift_compFin v _`. Establish `hζadd : ∀ y y', ζ (y + y') = ζ y + ζ y'` using `fun y y' => by`. Simplify using `only [ζ, map_add]`. Conclude with `Matrix.map_add _ (map_add _) _ _`. Establish `hζsmul : ∀ (a : Fv F v) y, ζ (a • y) = liftV v a • ζ y` using `fun a y => by`.

Establish `hat : At (evFin F v) (liftV v a • ζ y)` using `fun u hu => by rw [smul_comm, hζat y u hu, smul_zero]`. Rewrite using `[eq_map_lift v _ hat]`. Use `congr 1`. Use extensionality with `i k`. Apply the tactic sequence `simp [ζ, compFin_smul, evFin_liftV, compFin_lift] <;> rfl`.

Set `j : (Fin N → Fv F v) →ₗ[Fv F v] (Fin n × Fin d → Fv F v) × (Fin n × Fin d → Fv F v)` to `{ toFun := fun y => locCo M.co v (ζ y * Cᵀ) map_add' := fun y y' => by rw [hζadd, Matrix.add_mul, map_add] map_smul' := fun a y => by`. Rewrite using `[hζsmul, Matrix.smul_mul]`. Apply the tactic sequence `ext k <;> simp [locCo, evFin_liftV, -Matrix.smul_mul] }`. Use `⟨N, j, ζ, ?_, fun y => ⟨hζat y, rfl⟩, fun z hz => ?_, fun s => ?_⟩` and prove the remaining obligations. Rewrite using `[← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']`.

Introduce `y hy`. Establish `hu` using `eq_zero_of_locCo M.co v _ (at_mul v _ (hζat y) _) hy`. Establish `h3 : e y * (C.map (compFin F E v))ᵀ = 0`. Use `congrArg (fun x => Matrix.map x (compFin F E v)) hu` as an intermediate fact. Simplify using `only [Matrix.map_mul, Matrix.transpose_map, hζc, Matrix.map_zero _ (map_zero _)] at this`.

Conclude with `this`. Establish `h4 : e y = 0`. Establish `h5 : e y = e y * (P.toRows₁ * C.map (compFin F E v))ᵀ`. Rewrite using `[hP1, Matrix.transpose_one, Matrix.mul_one]`. Rewrite using `[h5, Matrix.transpose_mul, ← Matrix.mul_assoc, h3, Matrix.zero_mul]`.

Conclude with `e.map_eq_zero_iff.1 h4`. Conclude with `⟨e.symm (z.map (compFin F E v)), by simp only [ζ, LinearEquiv.apply_symm_apply]; exact (eq_map_lift v z hz).symm⟩`. Set `sv` to `s.val.map (compFin F E v)`. Set `L : Z →ₗ[Fv F v] Z` to `(mulLeft n m sv).restrictScalars (Fv F v)`. Set `f` to `e.symm.toLinearMap ∘ₗ L ∘ₗ e.toLinearMap`.

Establish `hdet : (LinearMap.toMatrix' f).det = Algebra.norm (Fv F v) (compFin F E v s.val.det) ^ m`. Rewrite using `[LinearMap.det_toMatrix']`. Establish `hf : f = e.symm.toLinearMap ∘ₗ L ∘ₗ e.symm.symm.toLinearMap` using `rfl`. Rewrite using `[hf, LinearMap.det_conj, LinearMap.det_restrictScalars, det_mulLeft, map_pow, RingHom.map_det]`. Both sides reduce to the same expression.

Establish `hs : IsUnit s.val.det` using `by simpa using (Matrix.GeneralLinearGroup.det s).isUnit`. Establish `hne : (LinearMap.toMatrix' f).det ≠ 0`. Rewrite using `[hdet]`. Conclude with `(((hs.map (compFin F E v)).map (Algebra.norm (Fv F v))).pow m).ne_zero`. Use `⟨Matrix.GeneralLinearGroup.mkOfDetNeZero _ hne, fun y => ?_, hdet⟩` and prove the remaining obligations.

Use `show ζ (LinearMap.toMatrix' f *ᵥ y) = s.val * ζ y`. Rewrite using `[LinearMap.toMatrix'_mulVec]`. Establish `hat : At (evFin F v) (s.val * ζ y)` using `fun u hu => by rw [← Matrix.mul_smul, hζat y u hu, Matrix.mul_zero]`. Rewrite using `[eq_map_lift v _ hat, Matrix.map_mul, hζc]`. Simplify using `[ζ, f, L, mulLeft, sv]`.
-/
theorem param : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (v : Pl F)
    (m : ℕ) (C : Matrix (Fin d) (Fin m) (AE F E)), IsLagrAt σ W v C →
    d = 2 * m ∧ ∃ (N : ℕ) (j : (Fin N → Fv F v) →ₗ[Fv F v] (Fin n × Fin d → Fv F v) × (Fin n × Fin d → Fv F v))
      (ζ : (Fin N → Fv F v) → Matrix (Fin n) (Fin m) (AE F E)), Function.Injective j ∧
      (∀ y, At (evFin F v) (ζ y) ∧ locCo M.co v (ζ y * Cᵀ) = j y) ∧
      (∀ z : Matrix (Fin n) (Fin m) (AE F E), At (evFin F v) z → ∃ y, ζ y = z) ∧
      ∀ s : GL (Fin n) (AE F E), ∃ T : GL (Fin N) (Fv F v), (∀ y, ζ (T.val *ᵥ y) = s.val * ζ y) ∧
        T.val.det = Algebra.norm (Fv F v) (compFin F E v s.val.det) ^ m := by
  intro F E _ _ _ _ _ σ n d X W M v m C hC
  obtain ⟨h0, Cx, P, hx, h1, h2⟩ := hC
  have hP1 : P.toRows₁ * C.map (compFin F E v) = 1 := by
    have h2' := h2
    rw [← Matrix.fromRows_toRows P, Matrix.fromRows_mul_fromCols, ← Matrix.fromBlocks_one,
      Matrix.fromBlocks_inj] at h2'
    exact h2'.1
  refine ⟨?_, ?_⟩
  · have := card_eq_of_inv _ _ h1 h2
    simp only [Fintype.card_fin, Fintype.card_sum] at this
    omega
  let Z := Matrix (Fin n) (Fin m) (Fv F v ⊗[F] E)
  let N := Module.finrank (Fv F v) Z
  let e : (Fin N → Fv F v) ≃ₗ[Fv F v] Z := (Module.finBasis (Fv F v) Z).equivFun.symm
  let ζ : (Fin N → Fv F v) → Matrix (Fin n) (Fin m) (AE F E) := fun y => (e y).map (lift v)
  have hζat : ∀ y, At (evFin F v) (ζ y) := fun y => at_map_lift v _
  have hζc : ∀ y, (ζ y).map (compFin F E v) = e y := fun y => map_lift_compFin v _
  have hζadd : ∀ y y', ζ (y + y') = ζ y + ζ y' := fun y y' => by
    simp only [ζ, map_add]
    exact Matrix.map_add _ (map_add _) _ _
  have hζsmul : ∀ (a : Fv F v) y, ζ (a • y) = liftV v a • ζ y := fun a y => by
    have hat : At (evFin F v) (liftV v a • ζ y) := fun u hu => by rw [smul_comm, hζat y u hu, smul_zero]
    rw [eq_map_lift v _ hat]
    congr 1
    ext i k
    simp [ζ, compFin_smul, evFin_liftV, compFin_lift] <;> rfl
  let j : (Fin N → Fv F v) →ₗ[Fv F v] (Fin n × Fin d → Fv F v) × (Fin n × Fin d → Fv F v) :=
    { toFun := fun y => locCo M.co v (ζ y * Cᵀ)
      map_add' := fun y y' => by rw [hζadd, Matrix.add_mul, map_add]
      map_smul' := fun a y => by
        rw [hζsmul, Matrix.smul_mul]
        ext k <;> simp [locCo, evFin_liftV, -Matrix.smul_mul] }
  refine ⟨N, j, ζ, ?_, fun y => ⟨hζat y, rfl⟩, fun z hz => ?_, fun s => ?_⟩
  · rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro y hy
    have hu := eq_zero_of_locCo M.co v _ (at_mul v _ (hζat y) _) hy
    have h3 : e y * (C.map (compFin F E v))ᵀ = 0 := by
      have := congrArg (fun x => Matrix.map x (compFin F E v)) hu
      simp only [Matrix.map_mul, Matrix.transpose_map, hζc, Matrix.map_zero _ (map_zero _)] at this
      exact this
    have h4 : e y = 0 := by
      have h5 : e y = e y * (P.toRows₁ * C.map (compFin F E v))ᵀ := by
        rw [hP1, Matrix.transpose_one, Matrix.mul_one]
      rw [h5, Matrix.transpose_mul, ← Matrix.mul_assoc, h3, Matrix.zero_mul]
    exact e.map_eq_zero_iff.1 h4
  · exact ⟨e.symm (z.map (compFin F E v)), by simp only [ζ, LinearEquiv.apply_symm_apply]; exact (eq_map_lift v z hz).symm⟩
  · let sv := s.val.map (compFin F E v)
    let L : Z →ₗ[Fv F v] Z := (mulLeft n m sv).restrictScalars (Fv F v)
    let f := e.symm.toLinearMap ∘ₗ L ∘ₗ e.toLinearMap
    have hdet : (LinearMap.toMatrix' f).det = Algebra.norm (Fv F v) (compFin F E v s.val.det) ^ m := by
      rw [LinearMap.det_toMatrix']
      have hf : f = e.symm.toLinearMap ∘ₗ L ∘ₗ e.symm.symm.toLinearMap := rfl
      rw [hf, LinearMap.det_conj, LinearMap.det_restrictScalars, det_mulLeft, map_pow, RingHom.map_det]
      rfl
    have hs : IsUnit s.val.det := by simpa using (Matrix.GeneralLinearGroup.det s).isUnit
    have hne : (LinearMap.toMatrix' f).det ≠ 0 := by
      rw [hdet]
      exact (((hs.map (compFin F E v)).map (Algebra.norm (Fv F v))).pow m).ne_zero
    refine ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero _ hne, fun y => ?_, hdet⟩
    show ζ (LinearMap.toMatrix' f *ᵥ y) = s.val * ζ y
    rw [LinearMap.toMatrix'_mulVec]
    have hat : At (evFin F v) (s.val * ζ y) := fun u hu => by rw [← Matrix.mul_smul, hζat y u hu, Matrix.mul_zero]
    rw [eq_map_lift v _ hat, Matrix.map_mul, hζc]
    simp [ζ, f, L, mulLeft, sv]

end GlobalTheory.InertLagParam

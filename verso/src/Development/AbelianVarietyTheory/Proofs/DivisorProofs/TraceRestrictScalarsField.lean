import Mathlib
import GroundTheory.Brauer.BaseChangeCSA

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.QTrace

set_option autoImplicit false in
/- English proof (translation)
Set `b` to `Module.finBasis ℚ F`. Set `d` to `Module.finBasis F W`. Rewrite using `[LinearMap.trace_eq_matrix_trace ℚ (b.smulTower d), LinearMap.trace_eq_matrix_trace F d, Matrix.trace, Matrix.trace, map_sum, Fintype.sum_prod_type, Finset.sum_comm]`. Use `Finset.sum_congr rfl fun k _ => ?_` and prove the remaining obligations. Rewrite using `[Algebra.trace_eq_matrix_trace b, Matrix.trace]`.

Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Simplify using `[LinearMap.toMatrix_apply, Module.Basis.smulTower_apply, Module.Basis.smulTower_repr, Algebra.leftMulMatrix_eq_repr_mul, mul_comm]`.
-/
private lemma trace_restrictScalars_rat {F W : Type} [Field F] [NumberField F] [AddCommGroup W]
    [Module F W] [Module ℚ W] [IsScalarTower ℚ F W] [FiniteDimensional F W] (f : W →ₗ[F] W) :
    LinearMap.trace ℚ W (f.restrictScalars ℚ) = Algebra.trace ℚ F (LinearMap.trace F W f) := by
  classical
  let b := Module.finBasis ℚ F
  let d := Module.finBasis F W
  rw [LinearMap.trace_eq_matrix_trace ℚ (b.smulTower d), LinearMap.trace_eq_matrix_trace F d,
    Matrix.trace, Matrix.trace, map_sum, Fintype.sum_prod_type, Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Algebra.trace_eq_matrix_trace b, Matrix.trace]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp [LinearMap.toMatrix_apply, Module.Basis.smulTower_apply, Module.Basis.smulTower_repr,
    Algebra.leftMulMatrix_eq_repr_mul, mul_comm]

set_option autoImplicit false in
/- English proof (translation)
Rewrite using `[LinearMap.trace_eq_matrix_trace ℂ (Matrix.stdBasis ℂ (Fin n) (Fin n))]`. Simplify using `only [Matrix.trace, LinearMap.toMatrix_apply, Matrix.diag, Fintype.sum_prod_type]`. Establish `key : ∀ i j, (Matrix.stdBasis ℂ (Fin n) (Fin n)).repr (LinearMap.mulLeft ℂ M (Matrix.stdBasis ℂ (Fin n) (Fin n) (i, j))) (i, j) = M i i`. Introduce `i j`. Rewrite using `[Matrix.stdBasis_eq_single]`.

Simplify using `[Matrix.stdBasis]`. Simplify using `only [key]`. Simplify using `[Finset.sum_const, Finset.card_univ, Finset.mul_sum]`.
-/
private lemma trace_mulLeft_matrix (n : ℕ) (M : Matrix (Fin n) (Fin n) ℂ) :
    LinearMap.trace ℂ (Matrix (Fin n) (Fin n) ℂ) (LinearMap.mulLeft ℂ M) = n * M.trace := by
  rw [LinearMap.trace_eq_matrix_trace ℂ (Matrix.stdBasis ℂ (Fin n) (Fin n))]
  simp only [Matrix.trace, LinearMap.toMatrix_apply, Matrix.diag, Fintype.sum_prod_type]
  have key : ∀ i j, (Matrix.stdBasis ℂ (Fin n) (Fin n)).repr
      (LinearMap.mulLeft ℂ M (Matrix.stdBasis ℂ (Fin n) (Fin n) (i, j))) (i, j) = M i i := by
    intro i j
    rw [Matrix.stdBasis_eq_single]
    simp [Matrix.stdBasis]
  simp only [key]
  simp [Finset.sum_const, Finset.card_univ, Finset.mul_sum]

set_option autoImplicit false in
/- English proof (translation)
Use `letI : Algebra F ℂ := σ.toAlgebra`. Establish `hn0 : n ≠ 0`. Introduce and unpack `rfl`. Establish `: 0 < Module.finrank F A` using `Module.finrank_pos`. Simplify using `[hn] at this`.

Use `haveI : NeZero n := ⟨hn0⟩`. Set `φF : A →ₐ[F] Matrix (Fin n) (Fin n) ℂ` to `{ φ with commutes' := fun x => (hφ x).trans rfl }`. Set `ι : ℂ →ₐ[ℂ] Matrix (Fin n) (Fin n) ℂ` to `Algebra.ofId ℂ _`. Set `G : TensorProduct F ℂ A →ₐ[ℂ] Matrix (Fin n) (Fin n) ℂ` to `Algebra.TensorProduct.lift ι φF (fun z a => Algebra.commute_algebraMap_left z _)`. Set `H : TensorProduct F A ℂ →ₐ[F] Matrix (Fin n) (Fin n) ℂ` to `Algebra.TensorProduct.lift φF (ι.restrictScalars F) (fun a z => (Algebra.commute_algebraMap_left z _).symm)`.

Establish `hH : Function.Injective H`. Rewrite using `[← TwoSidedIdeal.ker_eq_bot]`. Assume the negation of the conclusion as `hne`. Take `⟨b, hb, hmem⟩` from `_root_.GroundTheory.Brauer.exists_one_tmul_mem_of_ne_bot _ hne`. Rewrite `hmem` using `[TwoSidedIdeal.mem_ker]`.

Establish `: algebraMap ℂ (Matrix (Fin n) (Fin n) ℂ) b = 0`. Establish `h1 : H (1 ⊗ₜ[F] b) = φF 1 * (ι.restrictScalars F) b` using `Algebra.TensorProduct.lift_tmul _ _ _ _ _`. Rewrite `hmem` using `[h1, map_one, one_mul]`. Conclude with `hmem`. Conclude with `hb ((algebraMap ℂ (Matrix (Fin n) (Fin n) ℂ)).injective (this.trans (map_zero _).symm))`.

Establish `hGH : ∀ x, G x = H (TensorProduct.comm F ℂ A x)`. Introduce `x`. Proceed by induction on `x using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `tmul z a`.

Rewrite using `[TensorProduct.comm_tmul]`. Simplify using `only [G, H, Algebra.TensorProduct.lift_tmul, AlgHom.restrictScalars_apply, ι, Algebra.ofId_apply]`. Conclude with `Algebra.commutes z _`. Consider the case `add x y hx hy => simp [map_add, hx, hy]`. Establish `hG : Function.Injective G`.

Introduce `x y hxy`. Rewrite `hxy` using `[hGH, hGH]`. Conclude with `(TensorProduct.comm F ℂ A).injective (hH hxy)`. Establish `hdim : Module.finrank ℂ (TensorProduct F ℂ A) = Module.finrank ℂ (Matrix (Fin n) (Fin n) ℂ)`. Rewrite using `[_root_.GroundTheory.Brauer.finrank_baseChange_eq, hn, Module.finrank_matrix]`.

Simplify using `[sq]`. Use `haveI : FiniteDimensional ℂ (TensorProduct F ℂ A) := Module.finite_of_finrank_pos (by rw [hdim]; simp [Module.finrank_matrix, Nat.pos_of_ne_zero hn0])`. Set `e : TensorProduct F ℂ A ≃ₗ[ℂ] Matrix (Fin n) (Fin n) ℂ` to `LinearEquiv.ofBijective G.toLinearMap ⟨hG, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).mp hG⟩`. Establish `hconj : e.conj ((LinearMap.mulLeft F c).baseChange ℂ) = LinearMap.mulLeft ℂ (φ c)`. Use `LinearMap.ext fun y => ?_` and prove the remaining obligations.

Take `⟨x, rfl⟩` from `e.surjective y`. Rewrite using `[LinearEquiv.conj_apply, LinearMap.comp_apply, LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply]`. Use `show G _ = φ c * G x`. Proceed by induction on `x using TensorProduct.induction_on with`. Consider the case `zero => simp`.

Consider the case `tmul z a`. Rewrite using `[LinearMap.baseChange_tmul]`. Simplify using `only [G, Algebra.TensorProduct.lift_tmul, ι, Algebra.ofId_apply, LinearMap.mulLeft_apply]`. Use `show algebraMap ℂ _ z * φ (c * a) = φ c * (algebraMap ℂ _ z * φ a)`. Rewrite using `[map_mul, ← mul_assoc, ← mul_assoc, Algebra.commutes z (φ c)]`.

Consider the case `add x y hx hy => simp [map_add, hx, hy, mul_add]`. Rewrite using `[← trace_mulLeft_matrix, ← hconj, LinearMap.trace_conj', LinearMap.trace_baseChange]`. Both sides reduce to the same expression.
-/
private lemma embedding_trace_mulLeft_eq_mul_trace {F A : Type} [Field F] [Ring A] [Algebra F A]
    [FiniteDimensional F A] [Algebra.IsCentral F A] [IsSimpleRing A] (n : ℕ)
    (hn : Module.finrank F A = n ^ 2) (σ : F →+* ℂ) (φ : A →+* Matrix (Fin n) (Fin n) ℂ)
    (hφ : ∀ x : F, φ (algebraMap F A x) = Matrix.scalar (Fin n) (σ x)) (c : A) :
    σ (LinearMap.trace F A (LinearMap.mulLeft F c)) = n * (φ c).trace := by
  letI : Algebra F ℂ := σ.toAlgebra
  have hn0 : n ≠ 0 := by
    rintro rfl
    have : 0 < Module.finrank F A := Module.finrank_pos
    simp [hn] at this
  haveI : NeZero n := ⟨hn0⟩
  let φF : A →ₐ[F] Matrix (Fin n) (Fin n) ℂ :=
    { φ with commutes' := fun x => (hφ x).trans rfl }
  let ι : ℂ →ₐ[ℂ] Matrix (Fin n) (Fin n) ℂ := Algebra.ofId ℂ _
  let G : TensorProduct F ℂ A →ₐ[ℂ] Matrix (Fin n) (Fin n) ℂ :=
    Algebra.TensorProduct.lift ι φF (fun z a => Algebra.commute_algebraMap_left z _)
  let H : TensorProduct F A ℂ →ₐ[F] Matrix (Fin n) (Fin n) ℂ :=
    Algebra.TensorProduct.lift φF (ι.restrictScalars F)
      (fun a z => (Algebra.commute_algebraMap_left z _).symm)
  have hH : Function.Injective H := by
    rw [← TwoSidedIdeal.ker_eq_bot]
    by_contra hne
    obtain ⟨b, hb, hmem⟩ := _root_.GroundTheory.Brauer.exists_one_tmul_mem_of_ne_bot _ hne
    rw [TwoSidedIdeal.mem_ker] at hmem
    have : algebraMap ℂ (Matrix (Fin n) (Fin n) ℂ) b = 0 := by
      have h1 : H (1 ⊗ₜ[F] b) = φF 1 * (ι.restrictScalars F) b :=
        Algebra.TensorProduct.lift_tmul _ _ _ _ _
      rw [h1, map_one, one_mul] at hmem
      exact hmem
    exact hb ((algebraMap ℂ (Matrix (Fin n) (Fin n) ℂ)).injective (this.trans (map_zero _).symm))
  have hGH : ∀ x, G x = H (TensorProduct.comm F ℂ A x) := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul z a =>
      rw [TensorProduct.comm_tmul]
      simp only [G, H, Algebra.TensorProduct.lift_tmul, AlgHom.restrictScalars_apply, ι, Algebra.ofId_apply]
      exact Algebra.commutes z _
    | add x y hx hy => simp [map_add, hx, hy]
  have hG : Function.Injective G := by
    intro x y hxy
    rw [hGH, hGH] at hxy
    exact (TensorProduct.comm F ℂ A).injective (hH hxy)
  have hdim : Module.finrank ℂ (TensorProduct F ℂ A) = Module.finrank ℂ (Matrix (Fin n) (Fin n) ℂ) := by
    rw [_root_.GroundTheory.Brauer.finrank_baseChange_eq, hn, Module.finrank_matrix]
    simp [sq]
  haveI : FiniteDimensional ℂ (TensorProduct F ℂ A) :=
    Module.finite_of_finrank_pos (by rw [hdim]; simp [Module.finrank_matrix, Nat.pos_of_ne_zero hn0])
  let e : TensorProduct F ℂ A ≃ₗ[ℂ] Matrix (Fin n) (Fin n) ℂ :=
    LinearEquiv.ofBijective G.toLinearMap
      ⟨hG, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).mp hG⟩
  have hconj : e.conj ((LinearMap.mulLeft F c).baseChange ℂ) = LinearMap.mulLeft ℂ (φ c) := by
    refine LinearMap.ext fun y => ?_
    obtain ⟨x, rfl⟩ := e.surjective y
    rw [LinearEquiv.conj_apply, LinearMap.comp_apply, LinearMap.comp_apply, LinearEquiv.coe_coe,
      LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply]
    show G _ = φ c * G x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul z a =>
      rw [LinearMap.baseChange_tmul]
      simp only [G, Algebra.TensorProduct.lift_tmul, ι, Algebra.ofId_apply, LinearMap.mulLeft_apply]
      show algebraMap ℂ _ z * φ (c * a) = φ c * (algebraMap ℂ _ z * φ a)
      rw [map_mul, ← mul_assoc, ← mul_assoc, Algebra.commutes z (φ c)]
    | add x y hx hy => simp [map_add, hx, hy, mul_add]
  rw [← trace_mulLeft_matrix, ← hconj, LinearMap.trace_conj', LinearMap.trace_baseChange]
  rfl

set_option autoImplicit false in
/- English proof (translation)
Set `e` to `TensorProduct.piScalarRight ℚ ℚ N (Fin m)`. Establish `h : e.symm.conj (LinearMap.pi fun i => f ∘ₗ LinearMap.proj i) = TensorProduct.map f LinearMap.id`. Apply `TensorProduct.ext'` to reduce the goal to its premises. Introduce `x y`. Establish `hx : (LinearMap.pi fun i => f ∘ₗ LinearMap.proj i) (e (x ⊗ₜ y)) = e (f x ⊗ₜ y)`.

Use extensionality with `i`. Simplify using `[e, TensorProduct.piScalarRight_apply]`. Simplify using `only [LinearEquiv.conj_apply, LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_symm, hx, LinearEquiv.symm_apply_apply, TensorProduct.map_tmul, LinearMap.id_apply]`. Rewrite using `[← LinearMap.trace_conj' _ e.symm, h, LinearMap.trace_tensorProduct', LinearMap.trace_id]`. Simplify using `[mul_comm]`.
-/
private lemma trace_pi_comp_proj {N : Type} [AddCommGroup N] [Module ℚ N] [FiniteDimensional ℚ N] (m : ℕ)
    (f : N →ₗ[ℚ] N) :
    LinearMap.trace ℚ (Fin m → N) (LinearMap.pi fun i => f ∘ₗ LinearMap.proj i) =
      m * LinearMap.trace ℚ N f := by
  let e := TensorProduct.piScalarRight ℚ ℚ N (Fin m)
  have h : e.symm.conj (LinearMap.pi fun i => f ∘ₗ LinearMap.proj i) = TensorProduct.map f LinearMap.id := by
    apply TensorProduct.ext'
    intro x y
    have hx : (LinearMap.pi fun i => f ∘ₗ LinearMap.proj i) (e (x ⊗ₜ y)) = e (f x ⊗ₜ y) := by
      ext i
      simp [e, TensorProduct.piScalarRight_apply]
    simp only [LinearEquiv.conj_apply, LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_symm, hx,
      LinearEquiv.symm_apply_apply, TensorProduct.map_tmul, LinearMap.id_apply]
  rw [← LinearMap.trace_conj' _ e.symm, h, LinearMap.trace_tensorProduct', LinearMap.trace_id]
  simp [mul_comm]

set_option autoImplicit false in
/- English proof (translation)
Set `e' : M ≃ₗ[ℚ] (Fin k → S)` to `e.restrictScalars ℚ`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Rewrite using `[← LinearMap.trace_conj' _ e', ← trace_pi_comp_proj]`. Use `congr 1`. Use `LinearMap.ext fun v => funext fun x => ?_` and prove the remaining obligations.

Use `show e (c • e.symm v) x = c • v x`. Rewrite using `[map_smul, LinearEquiv.apply_symm_apply]`. Both sides reduce to the same expression. Rewrite using `[e'.finrank_eq, Module.finrank_pi_fintype]`. Simplify using the standard rewrite rules.
-/
private lemma trace_and_finrank_of_linearEquiv_pi {A M S : Type} [Ring A] [Algebra ℚ A] [AddCommGroup M]
    [Module A M] [Module ℚ M] [IsScalarTower ℚ A M] [AddCommGroup S] [Module A S] [Module ℚ S]
    [IsScalarTower ℚ A S] [FiniteDimensional ℚ S] (k : ℕ) (e : M ≃ₗ[A] (Fin k → S)) (c : A) :
    LinearMap.trace ℚ M (DistribMulAction.toLinearMap ℚ M c) =
        k * LinearMap.trace ℚ S (DistribMulAction.toLinearMap ℚ S c) ∧
      Module.finrank ℚ M = k * Module.finrank ℚ S := by
  let e' : M ≃ₗ[ℚ] (Fin k → S) := e.restrictScalars ℚ
  refine ⟨?_, ?_⟩
  · rw [← LinearMap.trace_conj' _ e', ← trace_pi_comp_proj]
    congr 1
    refine LinearMap.ext fun v => funext fun x => ?_
    show e (c • e.symm v) x = c • v x
    rw [map_smul, LinearEquiv.apply_symm_apply]
    rfl
  · rw [e'.finrank_eq, Module.finrank_pi_fintype]
    simp

set_option autoImplicit false in
/- English proof (translation)
Use `haveI : IsArtinianRing A := IsArtinianRing.of_finite ℚ A`. Use `haveI : IsSemisimpleRing A := (IsSimpleRing.isSemisimpleRing_iff_isArtinianRing (R := A)).mpr inferInstance`. Use `haveI : Module.Finite A M := Module.Finite.of_restrictScalars_finite ℚ A M`. Take `⟨S, hS⟩` from `IsSemisimpleModule.exists_simple_submodule A (A × M)`. Establish `hP : IsIsotypicOfType A (A × M) S` using `IsSimpleRing.isIsotypic A (A × M) S`.

Establish `hA : IsIsotypicOfType A A S`. Use `(LinearEquiv.isIsotypicOfType_iff (LinearEquiv.ofInjective (LinearMap.inl A A M) LinearMap.inl_injective)).mpr ?_` and prove the remaining obligations. Use `isIsotypicOfType_submodule_iff.mpr ?_` and prove the remaining obligations. Introduce `m _ _`. Conclude with `hP m`.

Establish `hM : IsIsotypicOfType A M S`. Use `(LinearEquiv.isIsotypicOfType_iff (LinearEquiv.ofInjective (LinearMap.inr A A M) LinearMap.inr_injective)).mpr ?_` and prove the remaining obligations. Use `isIsotypicOfType_submodule_iff.mpr ?_` and prove the remaining obligations. Introduce `m _ _`. Conclude with `hP m`.

Use `haveI : FiniteDimensional ℚ S := Module.Finite.of_injective ((S.subtype).restrictScalars ℚ) S.injective_subtype`. Take `⟨k, ⟨eA⟩⟩` from `hA.linearEquiv_fun`. Take `⟨m, ⟨eM⟩⟩` from `hM.linearEquiv_fun`. Take `⟨hA1, hA2⟩` from `trace_and_finrank_of_linearEquiv_pi k eA c`. Take `⟨hM1, hM2⟩` from `trace_and_finrank_of_linearEquiv_pi m eM c`.

Rewrite using `[hA1, hA2, hM1, hM2]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
private lemma trace_mul_finrank_eq_finrank_mul_trace {A M : Type} [Ring A] [Algebra ℚ A] [FiniteDimensional ℚ A]
    [IsSimpleRing A] [AddCommGroup M] [Module A M] [Module ℚ M] [IsScalarTower ℚ A M]
    [FiniteDimensional ℚ M] (c : A) :
    LinearMap.trace ℚ M (DistribMulAction.toLinearMap ℚ M c) * Module.finrank ℚ A =
      Module.finrank ℚ M * LinearMap.trace ℚ A (DistribMulAction.toLinearMap ℚ A c) := by
  haveI : IsArtinianRing A := IsArtinianRing.of_finite ℚ A
  haveI : IsSemisimpleRing A := (IsSimpleRing.isSemisimpleRing_iff_isArtinianRing (R := A)).mpr inferInstance
  haveI : Module.Finite A M := Module.Finite.of_restrictScalars_finite ℚ A M
  obtain ⟨S, hS⟩ := IsSemisimpleModule.exists_simple_submodule A (A × M)
  have hP : IsIsotypicOfType A (A × M) S := IsSimpleRing.isIsotypic A (A × M) S
  have hA : IsIsotypicOfType A A S := by
    refine (LinearEquiv.isIsotypicOfType_iff
      (LinearEquiv.ofInjective (LinearMap.inl A A M) LinearMap.inl_injective)).mpr ?_
    refine isIsotypicOfType_submodule_iff.mpr ?_
    intro m _ _
    exact hP m
  have hM : IsIsotypicOfType A M S := by
    refine (LinearEquiv.isIsotypicOfType_iff
      (LinearEquiv.ofInjective (LinearMap.inr A A M) LinearMap.inr_injective)).mpr ?_
    refine isIsotypicOfType_submodule_iff.mpr ?_
    intro m _ _
    exact hP m
  haveI : FiniteDimensional ℚ S :=
    Module.Finite.of_injective ((S.subtype).restrictScalars ℚ) S.injective_subtype
  obtain ⟨k, ⟨eA⟩⟩ := hA.linearEquiv_fun
  obtain ⟨m, ⟨eM⟩⟩ := hM.linearEquiv_fun
  obtain ⟨hA1, hA2⟩ := trace_and_finrank_of_linearEquiv_pi k eA c
  obtain ⟨hM1, hM2⟩ := trace_and_finrank_of_linearEquiv_pi m eM c
  rw [hA1, hA2, hM1, hM2]
  push_cast
  ring

set_option autoImplicit false in

/- English proof (translation)
Introduce `F A V _ _ _ _ _ _ _ _ _ _ n hn ρ ψ hψ c`. Establish `hn0 : n ≠ 0`. Introduce and unpack `rfl`. Establish `: 0 < Module.finrank F A` using `Module.finrank_pos`. Simplify using `[hn] at this`.

Use `letI : Algebra ℚ A := RingHom.toAlgebra' ((algebraMap F A).comp (algebraMap ℚ F)) (fun q x => Algebra.commutes _ x)`. Use `haveI : IsScalarTower ℚ F A := IsScalarTower.of_algebraMap_eq (fun _ => rfl)`. Use `haveI : FiniteDimensional ℚ A := Module.Finite.trans F A`. Use `letI : Module A V := Module.compHom V ρ`. Establish `hρq : ∀ q : ℚ, ρ (algebraMap ℚ A q) = algebraMap ℚ (Module.End ℚ V) q` using `fun q => congrArg (fun f : ℚ →+* Module.End ℚ V => f q) (RingHom.ext_rat (ρ.comp (algebraMap ℚ A)) (algebraMap ℚ (Module.End ℚ V)))`.

Use `haveI : IsScalarTower ℚ A V := ⟨fun q a v => by show ρ (q • a) v = q • ρ a v`. Rewrite using `[Algebra.smul_def, map_mul, Module.End.mul_apply, hρq, Module.algebraMap_end_apply]⟩`. Establish `hV : LinearMap.trace ℚ V (DistribMulAction.toLinearMap ℚ V c) = LinearMap.trace ℚ V (ρ c)` using `rfl`. Establish `hA : LinearMap.trace ℚ A (DistribMulAction.toLinearMap ℚ A c) = Algebra.trace ℚ F (LinearMap.trace F A (LinearMap.mulLeft F c))`. Rewrite using `[← trace_restrictScalars_rat]`.

Both sides reduce to the same expression. Establish `hsum : (algebraMap ℚ ℂ (Algebra.trace ℚ F (LinearMap.trace F A (LinearMap.mulLeft F c)))) = n * ∑ σ, Matrix.trace (ψ σ c)`. Rewrite using `[trace_eq_sum_embeddings ℂ, Finset.mul_sum]`. Use `(Fintype.sum_equiv (RingHom.equivRatAlgHom F ℂ).symm _ _ fun τ => ?_)` and prove the remaining obligations. Conclude with `embedding_trace_mulLeft_eq_mul_trace n hn _ (ψ _) (hψ _) c`.

Establish `hdim : Module.finrank ℚ A = Module.finrank ℚ F * n ^ 2`. Rewrite using `[← hn, Module.finrank_mul_finrank]`. Establish `key` using `trace_mul_finrank_eq_finrank_mul_trace (A := A) (M := V) c`. Rewrite `key` using `[hV, hA, hdim]`. Establish `key'` using `congrArg (fun t : ℚ => (t : ℂ)) key`.

Simplify using `only [Rat.cast_mul, Rat.cast_natCast] at key'`. Establish `hsum' : ((Algebra.trace ℚ F (LinearMap.trace F A (LinearMap.mulLeft F c)) : ℚ) : ℂ) = n * ∑ σ, Matrix.trace (ψ σ c)` using `hsum`. Rewrite `key'` using `[hsum']`. Establish `hnC : (n : ℂ) ≠ 0` using `Nat.cast_ne_zero.mpr hn0`. Apply `mul_left_cancel₀ hnC` to reduce the goal to its premises.

Move the coercions through the operations in `at key' ⊢`. Take the linear combination `key'`.
-/
theorem _root_.GlobalTheory.QTrace.q_trace : ∀ {F A V : Type} [Field F] [NumberField F] [Ring A] [Algebra F A] [FiniteDimensional F A] [Algebra.IsCentral F A]
    [IsSimpleRing A] [AddCommGroup V] [Module ℚ V] [FiniteDimensional ℚ V] (n : ℕ), Module.finrank F A = n ^ 2 →
    ∀ (ρ : A →+* Module.End ℚ V) (ψ : (F →+* ℂ) → (A →+* Matrix (Fin n) (Fin n) ℂ)),
    (∀ σ (x : F), ψ σ (algebraMap F A x) = Matrix.scalar (Fin n) (σ x)) → ∀ c : A,
    ((n * Module.finrank ℚ F : ℕ) : ℂ) * ((LinearMap.trace ℚ V (ρ c) : ℚ) : ℂ) =
      (Module.finrank ℚ V : ℂ) * ∑ σ, Matrix.trace (ψ σ c) := by
  intro F A V _ _ _ _ _ _ _ _ _ _ n hn ρ ψ hψ c
  have hn0 : n ≠ 0 := by
    rintro rfl
    have : 0 < Module.finrank F A := Module.finrank_pos
    simp [hn] at this
  letI : Algebra ℚ A := RingHom.toAlgebra' ((algebraMap F A).comp (algebraMap ℚ F))
    (fun q x => Algebra.commutes _ x)
  haveI : IsScalarTower ℚ F A := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  haveI : FiniteDimensional ℚ A := Module.Finite.trans F A
  letI : Module A V := Module.compHom V ρ
  have hρq : ∀ q : ℚ, ρ (algebraMap ℚ A q) = algebraMap ℚ (Module.End ℚ V) q := fun q =>
    congrArg (fun f : ℚ →+* Module.End ℚ V => f q)
      (RingHom.ext_rat (ρ.comp (algebraMap ℚ A)) (algebraMap ℚ (Module.End ℚ V)))
  haveI : IsScalarTower ℚ A V := ⟨fun q a v => by
    show ρ (q • a) v = q • ρ a v
    rw [Algebra.smul_def, map_mul, Module.End.mul_apply, hρq, Module.algebraMap_end_apply]⟩
  have hV : LinearMap.trace ℚ V (DistribMulAction.toLinearMap ℚ V c) = LinearMap.trace ℚ V (ρ c) := rfl
  have hA : LinearMap.trace ℚ A (DistribMulAction.toLinearMap ℚ A c) =
      Algebra.trace ℚ F (LinearMap.trace F A (LinearMap.mulLeft F c)) := by
    rw [← trace_restrictScalars_rat]
    rfl
  have hsum : (algebraMap ℚ ℂ (Algebra.trace ℚ F (LinearMap.trace F A (LinearMap.mulLeft F c)))) =
      n * ∑ σ, Matrix.trace (ψ σ c) := by
    rw [trace_eq_sum_embeddings ℂ, Finset.mul_sum]
    refine (Fintype.sum_equiv (RingHom.equivRatAlgHom F ℂ).symm _ _ fun τ => ?_)
    exact embedding_trace_mulLeft_eq_mul_trace n hn _ (ψ _) (hψ _) c
  have hdim : Module.finrank ℚ A = Module.finrank ℚ F * n ^ 2 := by
    rw [← hn, Module.finrank_mul_finrank]
  have key := trace_mul_finrank_eq_finrank_mul_trace (A := A) (M := V) c
  rw [hV, hA, hdim] at key
  have key' := congrArg (fun t : ℚ => (t : ℂ)) key
  simp only [Rat.cast_mul, Rat.cast_natCast] at key'
  have hsum' : ((Algebra.trace ℚ F (LinearMap.trace F A (LinearMap.mulLeft F c)) : ℚ) : ℂ) =
      n * ∑ σ, Matrix.trace (ψ σ c) := hsum
  rw [hsum'] at key'
  have hnC : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hn0
  apply mul_left_cancel₀ hnC
  push_cast at key' ⊢
  linear_combination key'

end GlobalTheory.QTrace

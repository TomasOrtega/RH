import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt

namespace GlobalTheory.HopfQuot

open TensorProduct

section Trace
variable {A M ι : Type*} [CommRing A] [AddCommGroup M] [Module A M] [Fintype ι]

def tr (e : ι → M) (c : ι → M →ₗ[A] A) (φ : M →ₗ[A] M) : A := ∑ i, c i (φ (e i))

/- English proof (translation)
Establish `key : ∀ φ ψ : M →ₗ[A] M, tr e c (φ ∘ₗ ψ) = ∑ i, ∑ j, c j (ψ (e i)) * c i (φ (e j))`. Introduce `φ ψ`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[LinearMap.comp_apply]`. Use `conv_lhs => rw [← h (ψ (e i))]`.

Simplify using `[map_sum]`. Rewrite using `[key, key, Finset.sum_comm]`. Simplify using `[mul_comm]`.
-/
theorem tr_comm (e : ι → M) (c : ι → M →ₗ[A] A) (h : ∀ m, ∑ i, c i m • e i = m)
    (φ ψ : M →ₗ[A] M) : tr e c (φ ∘ₗ ψ) = tr e c (ψ ∘ₗ φ) := by
  have key : ∀ φ ψ : M →ₗ[A] M, tr e c (φ ∘ₗ ψ) =
      ∑ i, ∑ j, c j (ψ (e i)) * c i (φ (e j)) := by
    intro φ ψ
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [LinearMap.comp_apply]
    conv_lhs => rw [← h (ψ (e i))]
    simp [map_sum]
  rw [key, key, Finset.sum_comm]
  simp [mul_comm]

end Trace

section Ev
variable {R Λ : Type*} [CommRing R] [AddCommGroup Λ] [Module R Λ]

noncomputable def ev (B : Type*) [CommRing B] [Algebra R B] (f : Λ →ₗ[R] R) :
    B ⊗[R] Λ →ₗ[B] B :=
  (TensorProduct.AlgebraTensorModule.rid R B B).toLinearMap ∘ₗ f.baseChange B

/- English proof (translation)
Simplify using `[ev]`.
-/
@[simp] theorem ev_tmul (B : Type*) [CommRing B] [Algebra R B] (f : Λ →ₗ[R] R) (b : B) (x : Λ) :
    ev B f (b ⊗ₜ x) = f x • b := by
  simp [ev]

end Ev

section Integral
variable {R Λ ι : Type*} [CommRing R] [CommRing Λ] [HopfAlgebra R Λ] [Fintype ι]

noncomputable def hit (f : Λ →ₗ[R] R) : Λ →ₗ[R] Λ :=
  (ev Λ f).restrictScalars R ∘ₗ Coalgebra.comul

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem hit_apply (f : Λ →ₗ[R] R) (y : Λ) : hit f y = ev Λ f (Coalgebra.comul y) := rfl

noncomputable def shear (R Λ : Type*) [CommRing R] [CommRing Λ] [HopfAlgebra R Λ] :
    Λ ⊗[R] Λ →ₐ[Λ] Λ ⊗[R] Λ :=
  Algebra.TensorProduct.lift (Algebra.ofId Λ _) (Bialgebra.comulAlgHom R Λ)
    (fun _ _ => Commute.all _ _)

/- English proof (translation)
Simplify using `[shear, Algebra.smul_def, Algebra.ofId_apply]`.
-/
theorem shear_tmul (x y : Λ) : shear R Λ (x ⊗ₜ y) = x • Coalgebra.comul (R := R) y := by
  simp [shear, Algebra.smul_def, Algebra.ofId_apply]

/- English proof (translation)
Establish `key : ∀ y : Λ, shear R Λ ((HopfAlgebra.antipode R).rTensor Λ (Coalgebra.comul y)) = 1 ⊗ₜ y`. Introduce `y`. Establish `h1 : ∀ z : Λ ⊗[R] Λ, shear R Λ ((HopfAlgebra.antipode R).rTensor Λ z) = (LinearMap.mul' R Λ ∘ₗ (HopfAlgebra.antipode R).rTensor Λ).rTensor Λ ((TensorProduct.assoc R Λ Λ Λ).symm ((Coalgebra.comul (R` using `R)).lTensor Λ z)) := by`. Introduce `z`. Proceed by induction on `z with`.

Consider the case `zero => simp`. Consider the case `add a b ha hb => simp only [map_add, ha, hb]`. Consider the case `tmul a b`. Rewrite using `[LinearMap.rTensor_tmul, shear_tmul, LinearMap.lTensor_tmul]`. Generalize the expression as in `Coalgebra.comul (R := R) b = w`.

Proceed by induction on `w with`. Consider the case `zero => simp`. Consider the case `add u v hu hv => simp only [map_add, smul_add, tmul_add, hu, hv]`. Consider the case `tmul u v => simp [TensorProduct.smul_tmul']`. Rewrite using `[h1, Coalgebra.coassoc_symm_apply, ← LinearMap.comp_apply, ← LinearMap.rTensor_comp, LinearMap.comp_assoc, HopfAlgebra.mul_antipode_rTensor_comul, LinearMap.rTensor_comp, LinearMap.comp_apply, Coalgebra.rTensor_counit_comul]`.

Simplify using the standard rewrite rules. Introduce `z`. Proceed by induction on `z with`. Consider the case `zero => exact ⟨0, map_zero _⟩`. Consider the case `add a b ha hb`.

Take `⟨a, rfl⟩` from `ha`. Take `⟨b, rfl⟩` from `hb`. Conclude with `⟨a + b, map_add _ _ _⟩`. Consider the case `tmul a b`. Use `⟨a • (HopfAlgebra.antipode R).rTensor Λ (Coalgebra.comul b), ?_⟩` and prove the remaining obligations.

Rewrite using `[map_smul, key, TensorProduct.smul_tmul']`. Simplify using the standard rewrite rules.
-/
theorem shear_surjective : Function.Surjective (shear R Λ) := by
  have key : ∀ y : Λ, shear R Λ ((HopfAlgebra.antipode R).rTensor Λ (Coalgebra.comul y))
      = 1 ⊗ₜ y := by
    intro y
    have h1 : ∀ z : Λ ⊗[R] Λ, shear R Λ ((HopfAlgebra.antipode R).rTensor Λ z) =
        (LinearMap.mul' R Λ ∘ₗ (HopfAlgebra.antipode R).rTensor Λ).rTensor Λ
          ((TensorProduct.assoc R Λ Λ Λ).symm ((Coalgebra.comul (R := R)).lTensor Λ z)) := by
      intro z
      induction z with
      | zero => simp
      | add a b ha hb => simp only [map_add, ha, hb]
      | tmul a b =>
        rw [LinearMap.rTensor_tmul, shear_tmul, LinearMap.lTensor_tmul]
        generalize Coalgebra.comul (R := R) b = w
        induction w with
        | zero => simp
        | add u v hu hv => simp only [map_add, smul_add, tmul_add, hu, hv]
        | tmul u v => simp [TensorProduct.smul_tmul']
    rw [h1, Coalgebra.coassoc_symm_apply, ← LinearMap.comp_apply, ← LinearMap.rTensor_comp,
      LinearMap.comp_assoc, HopfAlgebra.mul_antipode_rTensor_comul, LinearMap.rTensor_comp,
      LinearMap.comp_apply, Coalgebra.rTensor_counit_comul]
    simp
  intro z
  induction z with
  | zero => exact ⟨0, map_zero _⟩
  | add a b ha hb =>
    obtain ⟨a, rfl⟩ := ha
    obtain ⟨b, rfl⟩ := hb
    exact ⟨a + b, map_add _ _ _⟩
  | tmul a b =>
    refine ⟨a • (HopfAlgebra.antipode R).rTensor Λ (Coalgebra.comul b), ?_⟩
    rw [map_smul, key, TensorProduct.smul_tmul']
    simp

/- English proof (translation)
Establish `key : ∀ y : Λ, Coalgebra.comul (R` using `R) (hit f y) = (hit f).baseChange Λ (Coalgebra.comul y) := by`. Introduce `y`. Set `F : Λ ⊗[R] (Λ ⊗[R] Λ) →ₗ[R] Λ ⊗[R] Λ` to `((ev Λ f).restrictScalars R).lTensor Λ`. Establish `h1 : ∀ w : Λ ⊗[R] Λ, Coalgebra.comul (R` using `R) (ev Λ f w) = F (TensorProduct.assoc R Λ Λ Λ ((Coalgebra.comul (R := R)).rTensor Λ w)) := by`. Introduce `w`.

Proceed by induction on `w with`. Consider the case `zero => simp`. Consider the case `add a b ha hb => simp only [map_add, ha, hb]`. Consider the case `tmul a b`. Rewrite using `[ev_tmul, map_smul, LinearMap.rTensor_tmul]`.

Generalize the expression as in `Coalgebra.comul (R := R) a = w`. Proceed by induction on `w with`. Consider the case `zero => simp`. Consider the case `add u v hu hv => simp only [map_add, smul_add, add_tmul, hu, hv]`. Consider the case `tmul u v => simp [F]`.

Establish `h2 : ∀ w : Λ ⊗[R] Λ, (hit f).baseChange Λ w = F ((Coalgebra.comul (R` using `R)).lTensor Λ w) := by`. Introduce `w`. Proceed by induction on `w with`. Consider the case `zero => simp`. Consider the case `add a b ha hb => simp only [map_add, ha, hb]`.

Consider the case `tmul a b => simp [F, hit_apply]`. Rewrite using `[hit_apply, h1, h2, Coalgebra.coassoc_apply]`. Proceed by induction on `z with`. Consider the case `zero => simp`. Consider the case `add a b ha hb => simp only [map_add, ha, hb]`.

Consider the case `tmul a b`. Rewrite using `[LinearMap.baseChange_tmul, shear_tmul, shear_tmul, map_smul, key]`.
-/
theorem shear_hit (f : Λ →ₗ[R] R) (z : Λ ⊗[R] Λ) :
    shear R Λ ((hit f).baseChange Λ z) = (hit f).baseChange Λ (shear R Λ z) := by
  have key : ∀ y : Λ, Coalgebra.comul (R := R) (hit f y) =
      (hit f).baseChange Λ (Coalgebra.comul y) := by
    intro y
    let F : Λ ⊗[R] (Λ ⊗[R] Λ) →ₗ[R] Λ ⊗[R] Λ := ((ev Λ f).restrictScalars R).lTensor Λ
    have h1 : ∀ w : Λ ⊗[R] Λ, Coalgebra.comul (R := R) (ev Λ f w) =
        F (TensorProduct.assoc R Λ Λ Λ ((Coalgebra.comul (R := R)).rTensor Λ w)) := by
      intro w
      induction w with
      | zero => simp
      | add a b ha hb => simp only [map_add, ha, hb]
      | tmul a b =>
        rw [ev_tmul, map_smul, LinearMap.rTensor_tmul]
        generalize Coalgebra.comul (R := R) a = w
        induction w with
        | zero => simp
        | add u v hu hv => simp only [map_add, smul_add, add_tmul, hu, hv]
        | tmul u v => simp [F]
    have h2 : ∀ w : Λ ⊗[R] Λ, (hit f).baseChange Λ w =
        F ((Coalgebra.comul (R := R)).lTensor Λ w) := by
      intro w
      induction w with
      | zero => simp
      | add a b ha hb => simp only [map_add, ha, hb]
      | tmul a b => simp [F, hit_apply]
    rw [hit_apply, h1, h2, Coalgebra.coassoc_apply]
  induction z with
  | zero => simp
  | add a b ha hb => simp only [map_add, ha, hb]
  | tmul a b =>
    rw [LinearMap.baseChange_tmul, shear_tmul, shear_tmul, map_smul, key]

noncomputable def lam (e : ι → Λ) (c : ι → Λ →ₗ[R] R) (f : Λ →ₗ[R] R) : Λ →ₗ[R] R :=
  ∑ i, c i ∘ₗ hit f ∘ₗ LinearMap.mulRight R (e i)

/- English proof (translation)
Simplify using `[lam, tr]`.
-/
theorem lam_apply (e : ι → Λ) (c : ι → Λ →ₗ[R] R) (f : Λ →ₗ[R] R) (x : Λ) :
    lam e c f x = tr e c (hit f ∘ₗ LinearMap.mulLeft R x) := by
  simp [lam, tr]

/- English proof (translation)
Set `e' : ι → Λ ⊗[R] Λ` to `fun i => 1 ⊗ₜ e i`. Set `c' : ι → Λ ⊗[R] Λ →ₗ[Λ] Λ` to `fun i => ev Λ (c i)`. Establish `h' : ∀ m, ∑ i, c' i m • e' i = m`. Introduce `m`. Proceed by induction on `m with`.

Consider the case `zero => simp`. Consider the case `add a b ha hb => simp only [map_add, add_smul, Finset.sum_add_distrib, ha, hb]`. Consider the case `tmul a b => conv_rhs => rw [← h b, tmul_sum]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Simplify using `[c', e', TensorProduct.smul_tmul']`.

Establish `h1 : ∀ z : Λ ⊗[R] Λ, ev Λ (lam e c f) z = tr e' c' ((hit f).baseChange Λ ∘ₗ LinearMap.mulLeft Λ z)`. Introduce `z`. Proceed by induction on `z with`. Consider the case `zero => simp [tr]`. Consider the case `add a b ha hb`.

Rewrite using `[map_add, ha, hb]`. Simplify using `[tr, add_mul, Finset.sum_add_distrib]`. Consider the case `tmul a b`. Simplify using `[lam_apply, tr, c', e', Finset.sum_smul]`. Establish `hb : Function.Bijective (shear R Λ).toLinearMap` using `OrzechProperty.bijective_of_surjective_endomorphism _ shear_surjective`.

Set `σ` to `LinearEquiv.ofBijective _ hb`. Establish `h2 : (hit f).baseChange Λ ∘ₗ LinearMap.mulLeft Λ (Coalgebra.comul (R` using `R) x) = σ.toLinearMap ∘ₗ (((hit f).baseChange Λ ∘ₗ LinearMap.mulLeft Λ (1 ⊗ₜ x)) ∘ₗ σ.symm.toLinearMap) := by`. Use `LinearMap.ext fun z => ?_` and prove the remaining obligations. Take `⟨z, rfl⟩` from `σ.surjective z`. Simplify using `only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply, LinearMap.mulLeft_apply]`.

Express the relevant statement in the definitionally equal form `_ = shear R Λ _`. Rewrite using `[shear_hit, map_mul (shear R Λ), shear_tmul, one_smul]`. Both sides reduce to the same expression. Rewrite using `[h1, h2, tr_comm e' c' h', LinearMap.comp_assoc, LinearEquiv.symm_comp, LinearMap.comp_id, ← h1, ev_tmul, Algebra.algebraMap_eq_smul_one]`.
-/
theorem lam_integral [Module.Finite R Λ] (e : ι → Λ) (c : ι → Λ →ₗ[R] R)
    (h : ∀ m, ∑ i, c i m • e i = m) (f : Λ →ₗ[R] R) (x : Λ) :
    ev Λ (lam e c f) (Coalgebra.comul x) = algebraMap R Λ (lam e c f x) := by
  let e' : ι → Λ ⊗[R] Λ := fun i => 1 ⊗ₜ e i
  let c' : ι → Λ ⊗[R] Λ →ₗ[Λ] Λ := fun i => ev Λ (c i)
  have h' : ∀ m, ∑ i, c' i m • e' i = m := by
    intro m
    induction m with
    | zero => simp
    | add a b ha hb => simp only [map_add, add_smul, Finset.sum_add_distrib, ha, hb]
    | tmul a b =>
      conv_rhs => rw [← h b, tmul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      simp [c', e', TensorProduct.smul_tmul']
  have h1 : ∀ z : Λ ⊗[R] Λ, ev Λ (lam e c f) z =
      tr e' c' ((hit f).baseChange Λ ∘ₗ LinearMap.mulLeft Λ z) := by
    intro z
    induction z with
    | zero => simp [tr]
    | add a b ha hb =>
      rw [map_add, ha, hb]
      simp [tr, add_mul, Finset.sum_add_distrib]
    | tmul a b =>
      simp [lam_apply, tr, c', e', Finset.sum_smul]
  have hb : Function.Bijective (shear R Λ).toLinearMap :=
    OrzechProperty.bijective_of_surjective_endomorphism _ shear_surjective
  let σ := LinearEquiv.ofBijective _ hb
  have h2 : (hit f).baseChange Λ ∘ₗ LinearMap.mulLeft Λ (Coalgebra.comul (R := R) x) =
      σ.toLinearMap ∘ₗ (((hit f).baseChange Λ ∘ₗ LinearMap.mulLeft Λ (1 ⊗ₜ x)) ∘ₗ
        σ.symm.toLinearMap) := by
    refine LinearMap.ext fun z => ?_
    obtain ⟨z, rfl⟩ := σ.surjective z
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply,
      LinearMap.mulLeft_apply]
    change _ = shear R Λ _
    rw [shear_hit, map_mul (shear R Λ), shear_tmul, one_smul]
    rfl
  rw [h1, h2, tr_comm e' c' h', LinearMap.comp_assoc, LinearEquiv.symm_comp,
    LinearMap.comp_id, ← h1, ev_tmul, Algebra.algebraMap_eq_smul_one]

/- English proof (translation)
Establish `h1 : ∀ k, lam e c (c k) (HopfAlgebra.antipode R (e k) * x) = ∑ i, c i (HopfAlgebra.antipode R (e k) * hit (c k) (x * e i))`. Introduce `k`. Establish `: hit (c k) ∘ₗ LinearMap.mulLeft R (HopfAlgebra.antipode R (e k) * x) = (hit (c k) ∘ₗ LinearMap.mulLeft R x) ∘ₗ LinearMap.mulLeft R (HopfAlgebra.antipode R (e k))`. Use extensionality with `y`. Simplify using `[mul_left_comm, mul_assoc]`.

Rewrite using `[lam_apply, this, tr_comm e c h]`. Simplify using `[tr]`. Establish `h2 : ∀ y : Λ, ∑ k, HopfAlgebra.antipode R (e k) * hit (c k) y = algebraMap R Λ (Coalgebra.counit y)`. Introduce `y`. Rewrite using `[← HopfAlgebra.mul_antipode_lTensor_comul_apply]`.

Simplify using `only [hit_apply]`. Generalize the expression as in `Coalgebra.comul (R := R) y = w`. Proceed by induction on `w with`. Consider the case `zero => simp`. Consider the case `add u v hu hv => simp only [map_add, mul_add, Finset.sum_add_distrib, hu, hv]`.

Consider the case `tmul u v => conv_rhs => rw [← h v]`. Simplify using `[tmul_sum, map_sum, mul_comm]`. Simplify using `only [h1]`. Rewrite using `[Finset.sum_comm]`. Simplify using `only [← map_sum, h2, Bialgebra.counit_mul, Algebra.algebraMap_eq_smul_one, map_smul, smul_eq_mul, mul_assoc, ← Finset.mul_sum]`.

Establish `: ∑ i, Coalgebra.counit (R` using `R) (e i) * c i 1 = 1 := by`. Use `congrArg (Coalgebra.counit (R := R)) (h 1)` as an intermediate fact. Simplify `this` using `[map_sum, mul_comm]`. Rewrite using `[this, mul_one]`.
-/
theorem sum_lam (e : ι → Λ) (c : ι → Λ →ₗ[R] R)
    (h : ∀ m, ∑ i, c i m • e i = m) (x : Λ) :
    ∑ k, lam e c (c k) (HopfAlgebra.antipode R (e k) * x) = Coalgebra.counit (R := R) x := by
  have h1 : ∀ k, lam e c (c k) (HopfAlgebra.antipode R (e k) * x) =
      ∑ i, c i (HopfAlgebra.antipode R (e k) * hit (c k) (x * e i)) := by
    intro k
    have : hit (c k) ∘ₗ LinearMap.mulLeft R (HopfAlgebra.antipode R (e k) * x) =
        (hit (c k) ∘ₗ LinearMap.mulLeft R x) ∘ₗ
          LinearMap.mulLeft R (HopfAlgebra.antipode R (e k)) := by
      ext y
      simp [mul_left_comm, mul_assoc]
    rw [lam_apply, this, tr_comm e c h]
    simp [tr]
  have h2 : ∀ y : Λ, ∑ k, HopfAlgebra.antipode R (e k) * hit (c k) y =
      algebraMap R Λ (Coalgebra.counit y) := by
    intro y
    rw [← HopfAlgebra.mul_antipode_lTensor_comul_apply]
    simp only [hit_apply]
    generalize Coalgebra.comul (R := R) y = w
    induction w with
    | zero => simp
    | add u v hu hv => simp only [map_add, mul_add, Finset.sum_add_distrib, hu, hv]
    | tmul u v =>
      conv_rhs => rw [← h v]
      simp [tmul_sum, map_sum, mul_comm]
  simp only [h1]
  rw [Finset.sum_comm]
  simp only [← map_sum, h2, Bialgebra.counit_mul, Algebra.algebraMap_eq_smul_one, map_smul,
    smul_eq_mul, mul_assoc, ← Finset.mul_sum]
  have : ∑ i, Coalgebra.counit (R := R) (e i) * c i 1 = 1 := by
    have := congrArg (Coalgebra.counit (R := R)) (h 1)
    simpa [map_sum, mul_comm] using this
  rw [this, mul_one]

/- English proof (translation)
Take `⟨n, p, s, -, -, hps⟩` from `Module.Finite.exists_comp_eq_id_of_projective R Λ`. Set `e : Fin n → Λ` to `fun i => p (Pi.single i 1)`. Set `c : Fin n → Λ →ₗ[R] R` to `fun i => LinearMap.proj i ∘ₗ s`. Establish `h : ∀ m, ∑ i, c i m • e i = m`. Introduce `m`.

Establish `h1 : p (s m) = m` using `LinearMap.congr_fun hps m`. Use `conv_rhs => rw [← h1, pi_eq_sum_univ' (s m)]`. Simplify using `[c, e, map_sum]`. Conclude with `⟨n, fun k => lam e c (c k), fun k => HopfAlgebra.antipode R (e k), fun k x => lam_integral e c h _ x, sum_lam e c h⟩`.
-/
theorem exists_integrals (R Λ : Type*) [CommRing R] [CommRing Λ] [HopfAlgebra R Λ]
    [Module.Finite R Λ] [Module.Projective R Λ] :
    ∃ (n : ℕ) (l : Fin n → Λ →ₗ[R] R) (T : Fin n → Λ),
      (∀ k x, ev Λ (l k) (Coalgebra.comul x) = algebraMap R Λ (l k x)) ∧
      ∀ x, ∑ k, l k (T k * x) = Coalgebra.counit (R := R) x := by
  obtain ⟨n, p, s, -, -, hps⟩ := Module.Finite.exists_comp_eq_id_of_projective R Λ
  let e : Fin n → Λ := fun i => p (Pi.single i 1)
  let c : Fin n → Λ →ₗ[R] R := fun i => LinearMap.proj i ∘ₗ s
  have h : ∀ m, ∑ i, c i m • e i = m := by
    intro m
    have h1 : p (s m) = m := LinearMap.congr_fun hps m
    conv_rhs => rw [← h1, pi_eq_sum_univ' (s m)]
    simp [c, e, map_sum]
  exact ⟨n, fun k => lam e c (c k), fun k => HopfAlgebra.antipode R (e k),
    fun k x => lam_integral e c h _ x, sum_lam e c h⟩

end Integral

section Action
variable {R Λ B : Type*} [CommRing R] [CommRing Λ] [HopfAlgebra R Λ] [CommRing B] [Algebra R B]
  (ρ : B →ₐ[R] B ⊗[R] Λ)

/- English proof (translation)
Set `F : B ⊗[R] (Λ ⊗[R] Λ) →ₗ[R] B ⊗[R] Λ` to `((ev Λ l).restrictScalars R).lTensor B`. Establish `h1 : ∀ w : B ⊗[R] Λ, ρ (ev B l w) = F (TensorProduct.assoc R B Λ Λ (ρ.toLinearMap.rTensor Λ w))`. Introduce `w`. Proceed by induction on `w with`. Consider the case `zero => simp`.

Consider the case `add a b ha hb => simp only [map_add, ha, hb]`. Consider the case `tmul a b`. Rewrite using `[ev_tmul, map_smul, LinearMap.rTensor_tmul, AlgHom.toLinearMap_apply]`. Generalize the expression as in `ρ a = w`. Proceed by induction on `w with`.

Consider the case `zero => simp`. Consider the case `add u v hu hv => simp only [map_add, smul_add, add_tmul, hu, hv]`. Consider the case `tmul u v => simp [F]`. Establish `h2 : ∀ w : B ⊗[R] Λ, F ((Coalgebra.comul (R` using `R)).lTensor B w) = ev B l w ⊗ₜ 1 := by`. Introduce `w`.

Proceed by induction on `w with`. Consider the case `zero => simp`. Consider the case `add a b ha hb => simp only [map_add, add_tmul, ha, hb]`. Consider the case `tmul a b => simp [F, hl, Algebra.algebraMap_eq_smul_one, smul_tmul]`. Rewrite using `[AlgHom.mem_equalizer, h1, hassoc, h2]`.

Both sides reduce to the same expression.
-/
theorem ev_mem_equalizer
    (hassoc : ∀ b, TensorProduct.assoc R B Λ Λ (ρ.toLinearMap.rTensor Λ (ρ b)) =
      (Coalgebra.comul (R := R) (A := Λ)).lTensor B (ρ b))
    (l : Λ →ₗ[R] R) (hl : ∀ x, ev Λ l (Coalgebra.comul x) = algebraMap R Λ (l x)) (b : B) :
    ev B l (ρ b) ∈ AlgHom.equalizer ρ
      (Algebra.TensorProduct.includeLeft : B →ₐ[R] B ⊗[R] Λ) := by
  let F : B ⊗[R] (Λ ⊗[R] Λ) →ₗ[R] B ⊗[R] Λ := ((ev Λ l).restrictScalars R).lTensor B
  have h1 : ∀ w : B ⊗[R] Λ, ρ (ev B l w) =
      F (TensorProduct.assoc R B Λ Λ (ρ.toLinearMap.rTensor Λ w)) := by
    intro w
    induction w with
    | zero => simp
    | add a b ha hb => simp only [map_add, ha, hb]
    | tmul a b =>
      rw [ev_tmul, map_smul, LinearMap.rTensor_tmul, AlgHom.toLinearMap_apply]
      generalize ρ a = w
      induction w with
      | zero => simp
      | add u v hu hv => simp only [map_add, smul_add, add_tmul, hu, hv]
      | tmul u v => simp [F]
  have h2 : ∀ w : B ⊗[R] Λ, F ((Coalgebra.comul (R := R)).lTensor B w) =
      ev B l w ⊗ₜ 1 := by
    intro w
    induction w with
    | zero => simp
    | add a b ha hb => simp only [map_add, add_tmul, ha, hb]
    | tmul a b => simp [F, hl, Algebra.algebraMap_eq_smul_one, smul_tmul]
  rw [AlgHom.mem_equalizer, h1, hassoc, h2]
  rfl

/- English proof (translation)
Take `⟨n, l, T, hl, hT⟩` from `exists_integrals R Λ`. Use `choose z hz using fun k => hsurj (1 ⊗ₜ T k)`. Use `choose m x y hxy using fun k => TensorProduct.exists_sum_tmul_eq (z k)`. Use `⟨Σ k, Fin (m k), inferInstance, fun j => x j.1 j.2, fun j => ev B (l j.1) ∘ₗ LinearMap.mulLeft B (ρ (y j.1 j.2)), fun j u => ?_, fun u => ?_⟩` and prove the remaining obligations. Rewrite using `[LinearMap.comp_apply, LinearMap.mulLeft_apply, ← map_mul]`.

Conclude with `ev_mem_equalizer ρ hassoc _ (hl _) _`. Rewrite using `[Fintype.sum_sigma]`. Establish `h1 : ∀ k, ∑ i, ev B (l k) (ρ (y k i) * ρ u) * x k i = ev B (l k) (1 ⊗ₜ T k * ρ u)`. Introduce `k`. Rewrite using `[← hz, hxy, map_sum, Finset.sum_mul, map_sum]`.

Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[mul_comm, ← smul_eq_mul, ← map_smul, Algebra.TensorProduct.productMap_apply_tmul, mul_assoc, Algebra.smul_def]`. Both sides reduce to the same expression. Simplify using `only [LinearMap.comp_apply, LinearMap.mulLeft_apply, h1]`. Use `conv_rhs => rw [← hcounit u]`.

Generalize the expression as in `ρ u = w`. Proceed by induction on `w with`. Consider the case `zero => simp`. Consider the case `add u v hu hv => simp only [map_add, mul_add, Finset.sum_add_distrib, hu, hv]`. Consider the case `tmul u v => simp [← Finset.sum_smul, hT]`.
-/
theorem exists_dual_family [Module.Finite R Λ] [Module.Projective R Λ]
    (hassoc : ∀ b, TensorProduct.assoc R B Λ Λ (ρ.toLinearMap.rTensor Λ (ρ b)) =
      (Coalgebra.comul (R := R) (A := Λ)).lTensor B (ρ b))
    (hcounit : ∀ b, TensorProduct.rid R B
      ((Coalgebra.counit (R := R) (A := Λ)).lTensor B (ρ b)) = b)
    (hsurj : Function.Surjective (Algebra.TensorProduct.productMap
      (Algebra.TensorProduct.includeLeft : B →ₐ[R] B ⊗[R] Λ) ρ)) :
    ∃ (ι : Type) (_ : Fintype ι) (a : ι → B) (L : ι → B ⊗[R] Λ →ₗ[B] B),
      (∀ j u, L j (ρ u) ∈ AlgHom.equalizer ρ
        (Algebra.TensorProduct.includeLeft : B →ₐ[R] B ⊗[R] Λ)) ∧
      ∀ u, ∑ j, L j (ρ u) * a j = u := by
  obtain ⟨n, l, T, hl, hT⟩ := exists_integrals R Λ
  choose z hz using fun k => hsurj (1 ⊗ₜ T k)
  choose m x y hxy using fun k => TensorProduct.exists_sum_tmul_eq (z k)
  refine ⟨Σ k, Fin (m k), inferInstance, fun j => x j.1 j.2,
    fun j => ev B (l j.1) ∘ₗ LinearMap.mulLeft B (ρ (y j.1 j.2)), fun j u => ?_, fun u => ?_⟩
  · rw [LinearMap.comp_apply, LinearMap.mulLeft_apply, ← map_mul]
    exact ev_mem_equalizer ρ hassoc _ (hl _) _
  · rw [Fintype.sum_sigma]
    have h1 : ∀ k, ∑ i, ev B (l k) (ρ (y k i) * ρ u) * x k i = ev B (l k) (1 ⊗ₜ T k * ρ u) := by
      intro k
      rw [← hz, hxy, map_sum, Finset.sum_mul, map_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [mul_comm, ← smul_eq_mul, ← map_smul, Algebra.TensorProduct.productMap_apply_tmul,
        mul_assoc, Algebra.smul_def]
      rfl
    simp only [LinearMap.comp_apply, LinearMap.mulLeft_apply, h1]
    conv_rhs => rw [← hcounit u]
    generalize ρ u = w
    induction w with
    | zero => simp
    | add u v hu hv => simp only [map_add, mul_add, Finset.sum_add_distrib, hu, hv]
    | tmul u v => simp [← Finset.sum_smul, hT]

/- English proof (translation)
Take `⟨ι, _, a, L, hL, ha⟩` from `exists_dual_family ρ hassoc hcounit hsurj`. Use `set B₀ := AlgHom.equalizer ρ (Algebra.TensorProduct.includeLeft : B →ₐ[R] B ⊗[R] Λ) with hB₀`. Set `s : B →ₗ[B₀] (ι → B₀)` to `{ toFun := fun u j => ⟨L j (ρ u), hL j u⟩ map_add' := fun u v => by`. Use extensionality with `j`. Simplify using the standard rewrite rules.

Use the proof step `map_smul' := fun t u => by`. Use extensionality with `j`. Establish `ht : ρ t = (t : B) ⊗ₜ 1` using `t.2`. Express the relevant statement in the definitionally equal form `L j (ρ (t * u)) = t * L j (ρ u)`. Rewrite using `[map_mul, ht, ← smul_eq_mul (t : B), ← map_smul, Algebra.smul_def]`.

Use `rfl }`. Set `p : (ι → B₀) →ₗ[B₀] B` to `Fintype.linearCombination B₀ a`. Establish `hps : p ∘ₗ s = LinearMap.id`. Use `LinearMap.ext fun u => ?_` and prove the remaining obligations. Conclude with `ha u`.

Establish `hfin : Module.Finite B₀ B` using `Module.Finite.of_surjective p fun u => ⟨s u, LinearMap.congr_fun hps u⟩`. Establish `hproj : Module.Projective B₀ B` using `Module.Projective.of_split s p hps`. Use `⟨hfin, hproj, .of_comap_surjective (Algebra.IsIntegral.comap_surjective B₀ B), le_antisymm ?_ ?_⟩` and prove the remaining obligations. Use `set I := Ideal.span {z | ∃ b ∈ B₀, z = b ⊗ₜ[R] (1 : B) - (1 : B) ⊗ₜ[R] b}`. Establish `key : ∀ z : B ⊗[R] B, (∑ j, L j (Algebra.TensorProduct.productMap (Algebra.TensorProduct.includeLeft : B →ₐ[R] B ⊗[R] Λ) ρ z) ⊗ₜ[R] a j) - z ∈ I`.

Introduce `z`. Proceed by induction on `z with`. Consider the case `zero => simp`. Consider the case `add u v hu hv`. Simplify using `only [map_add, add_tmul, Finset.sum_add_distrib]`.

Rewrite using `[add_sub_add_comm]`. Conclude with `I.add_mem hu hv`. Consider the case `tmul x y`. Establish `: x ⊗ₜ[R] y = ∑ j, x ⊗ₜ[R] (L j (ρ y) * a j)` using `by rw [← tmul_sum, ha]`. Rewrite using `[Algebra.TensorProduct.productMap_apply_tmul, this, ← Finset.sum_sub_distrib]`.

Use `I.sum_mem fun j _ => ?_` and prove the remaining obligations. Establish `h1 : L j ((Algebra.TensorProduct.includeLeft : B →ₐ[R] B ⊗[R] Λ) x * ρ y) = x * L j (ρ y)`. Rewrite using `[← smul_eq_mul x, ← map_smul, Algebra.smul_def]`. Both sides reduce to the same expression. Establish `h2 : (x * L j (ρ y)) ⊗ₜ[R] a j - x ⊗ₜ[R] (L j (ρ y) * a j) = (x ⊗ₜ[R] a j) * (L j (ρ y) ⊗ₜ[R] (1 : B) - (1 : B) ⊗ₜ[R] L j (ρ y))`.

Simplify using `[mul_sub, mul_comm]`. Rewrite using `[h1, h2]`. Conclude with `I.mul_mem_left _ (Ideal.subset_span ⟨_, hL j y, rfl⟩)`. Introduce `z hz`. Use `key z` as an intermediate fact.

Rewrite `hz` using `[RingHom.mem_ker]`. Simplify using `only [hz, map_zero, zero_tmul, Finset.sum_const_zero, zero_sub] at this`. Conclude with `neg_mem_iff.1 this`. Rewrite using `[Ideal.span_le]`. Introduce and unpack `_ ⟨b, hb, rfl⟩`.

Establish `hb' : ρ b = b ⊗ₜ 1` using `hb`. Simplify using `[RingHom.mem_ker, hb']`.
-/
theorem finite_faithfullyFlat_ker [Module.Finite R Λ] [Module.Projective R Λ]
    (hassoc : ∀ b, TensorProduct.assoc R B Λ Λ (ρ.toLinearMap.rTensor Λ (ρ b)) =
      (Coalgebra.comul (R := R) (A := Λ)).lTensor B (ρ b))
    (hcounit : ∀ b, TensorProduct.rid R B
      ((Coalgebra.counit (R := R) (A := Λ)).lTensor B (ρ b)) = b)
    (hsurj : Function.Surjective (Algebra.TensorProduct.productMap
      (Algebra.TensorProduct.includeLeft : B →ₐ[R] B ⊗[R] Λ) ρ)) :
    Module.Finite (AlgHom.equalizer ρ
      (Algebra.TensorProduct.includeLeft : B →ₐ[R] B ⊗[R] Λ)) B ∧
    Module.Projective (AlgHom.equalizer ρ
      (Algebra.TensorProduct.includeLeft : B →ₐ[R] B ⊗[R] Λ)) B ∧
    Module.FaithfullyFlat (AlgHom.equalizer ρ
      (Algebra.TensorProduct.includeLeft : B →ₐ[R] B ⊗[R] Λ)) B ∧
    RingHom.ker (Algebra.TensorProduct.productMap
        (Algebra.TensorProduct.includeLeft : B →ₐ[R] B ⊗[R] Λ) ρ) =
      Ideal.span {z | ∃ b ∈ AlgHom.equalizer ρ
        (Algebra.TensorProduct.includeLeft : B →ₐ[R] B ⊗[R] Λ),
        z = b ⊗ₜ[R] (1 : B) - (1 : B) ⊗ₜ[R] b} := by
  classical
  obtain ⟨ι, _, a, L, hL, ha⟩ := exists_dual_family ρ hassoc hcounit hsurj
  set B₀ := AlgHom.equalizer ρ (Algebra.TensorProduct.includeLeft : B →ₐ[R] B ⊗[R] Λ) with hB₀
  let s : B →ₗ[B₀] (ι → B₀) :=
    { toFun := fun u j => ⟨L j (ρ u), hL j u⟩
      map_add' := fun u v => by
        ext j
        simp
      map_smul' := fun t u => by
        ext j
        have ht : ρ t = (t : B) ⊗ₜ 1 := t.2
        change L j (ρ (t * u)) = t * L j (ρ u)
        rw [map_mul, ht, ← smul_eq_mul (t : B), ← map_smul, Algebra.smul_def]
        rfl }
  let p : (ι → B₀) →ₗ[B₀] B := Fintype.linearCombination B₀ a
  have hps : p ∘ₗ s = LinearMap.id := by
    refine LinearMap.ext fun u => ?_
    exact ha u
  have hfin : Module.Finite B₀ B :=
    Module.Finite.of_surjective p fun u => ⟨s u, LinearMap.congr_fun hps u⟩
  have hproj : Module.Projective B₀ B := Module.Projective.of_split s p hps
  refine ⟨hfin, hproj,
    .of_comap_surjective (Algebra.IsIntegral.comap_surjective B₀ B), le_antisymm ?_ ?_⟩
  · set I := Ideal.span {z | ∃ b ∈ B₀, z = b ⊗ₜ[R] (1 : B) - (1 : B) ⊗ₜ[R] b}
    have key : ∀ z : B ⊗[R] B, (∑ j, L j (Algebra.TensorProduct.productMap
        (Algebra.TensorProduct.includeLeft : B →ₐ[R] B ⊗[R] Λ) ρ z) ⊗ₜ[R] a j) - z ∈ I := by
      intro z
      induction z with
      | zero => simp
      | add u v hu hv =>
        simp only [map_add, add_tmul, Finset.sum_add_distrib]
        rw [add_sub_add_comm]
        exact I.add_mem hu hv
      | tmul x y =>
        have : x ⊗ₜ[R] y = ∑ j, x ⊗ₜ[R] (L j (ρ y) * a j) := by rw [← tmul_sum, ha]
        rw [Algebra.TensorProduct.productMap_apply_tmul, this, ← Finset.sum_sub_distrib]
        refine I.sum_mem fun j _ => ?_
        have h1 : L j ((Algebra.TensorProduct.includeLeft : B →ₐ[R] B ⊗[R] Λ) x * ρ y) =
            x * L j (ρ y) := by
          rw [← smul_eq_mul x, ← map_smul, Algebra.smul_def]
          rfl
        have h2 : (x * L j (ρ y)) ⊗ₜ[R] a j - x ⊗ₜ[R] (L j (ρ y) * a j) =
            (x ⊗ₜ[R] a j) * (L j (ρ y) ⊗ₜ[R] (1 : B) - (1 : B) ⊗ₜ[R] L j (ρ y)) := by
          simp [mul_sub, mul_comm]
        rw [h1, h2]
        exact I.mul_mem_left _ (Ideal.subset_span ⟨_, hL j y, rfl⟩)
    intro z hz
    have := key z
    rw [RingHom.mem_ker] at hz
    simp only [hz, map_zero, zero_tmul, Finset.sum_const_zero, zero_sub] at this
    exact neg_mem_iff.1 this
  · rw [Ideal.span_le]
    rintro _ ⟨b, hb, rfl⟩
    have hb' : ρ b = b ⊗ₜ 1 := hb
    simp [RingHom.mem_ker, hb']

end Action

end GlobalTheory.HopfQuot

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory

/- English proof (translation)
Introduce `_ R Λ B _ _ _ _ _ _ _ ρ h1 h2 h3`. Take `⟨a, -, b, c⟩` from `GlobalTheory.HopfQuot.finite_faithfullyFlat_ker ρ h1 h2 h3`. Conclude with `⟨a, b, c⟩`.
-/
theorem GlobalTheory.HopfQuot.affine_quotient :
    (∀ (A B M : Type) [CommRing A] [IsLocalRing A] [Infinite (IsLocalRing.ResidueField A)] [CommRing B] [Algebra A B] [Finite (MaximalSpectrum B)] [AddCommGroup M] [Module B M] [Module A M] [IsScalarTower A B M] (n : ℕ) (_ : Module.Basis (Fin n) B M) (N : Submodule A M), (∀ m : MaximalSpectrum B, (IsLocalRing.maximalIdeal A).map (algebraMap A B) ≤ m.asIdeal) → Submodule.span B (N : Set M) = ⊤ → ∃ b : Module.Basis (Fin n) B M, ∀ i, b i ∈ N) → ∀ (R Λ B : Type) [CommRing R] [CommRing Λ] [HopfAlgebra R Λ] [Module.Finite R Λ] [Module.Projective R Λ] [CommRing B] [Algebra R B] (ρ : B →ₐ[R] TensorProduct R B Λ), (∀ b, TensorProduct.assoc R B Λ Λ (ρ.toLinearMap.rTensor Λ (ρ b)) = (Coalgebra.comul (R := R) (A := Λ)).lTensor B (ρ b)) → (∀ b, TensorProduct.rid R B ((Coalgebra.counit (R := R) (A := Λ)).lTensor B (ρ b)) = b) → Function.Surjective (Algebra.TensorProduct.productMap (Algebra.TensorProduct.includeLeft : B →ₐ[R] TensorProduct R B Λ) ρ) → Module.Finite (AlgHom.equalizer ρ (Algebra.TensorProduct.includeLeft : B →ₐ[R] TensorProduct R B Λ)) B ∧ Module.FaithfullyFlat (AlgHom.equalizer ρ (Algebra.TensorProduct.includeLeft : B →ₐ[R] TensorProduct R B Λ)) B ∧ RingHom.ker (Algebra.TensorProduct.productMap (Algebra.TensorProduct.includeLeft : B →ₐ[R] TensorProduct R B Λ) ρ) = Ideal.span {z | ∃ b ∈ AlgHom.equalizer ρ (Algebra.TensorProduct.includeLeft : B →ₐ[R] TensorProduct R B Λ), z = b ⊗ₜ[R] (1 : B) - (1 : B) ⊗ₜ[R] b} := by
  intro _ R Λ B _ _ _ _ _ _ _ ρ h1 h2 h3
  obtain ⟨a, -, b, c⟩ := GlobalTheory.HopfQuot.finite_faithfullyFlat_ker ρ h1 h2 h3
  exact ⟨a, b, c⟩

import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ContractionTensorModels

noncomputable section

open scoped InnerProductSpace TensorProduct

namespace GlobalTheory.ContrObj

open GlobalTheory.IndefiniteRowSideFullHecke.ContractionTensorModels

section Hilbert

variable {H₁ H₂ FF : Type}
  [NormedAddCommGroup H₁] [InnerProductSpace ℂ H₁]
  [NormedAddCommGroup H₂] [InnerProductSpace ℂ H₂]
  [NormedAddCommGroup FF] [InnerProductSpace ℂ FF]

/- English proof (translation)
Establish `h` using `hI x x y y`. Rewrite `h` using `[inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K, ← mul_pow]`. Establish `h2 : ‖Tm x y‖ ^ 2 = (‖x‖ * ‖y‖) ^ 2` using `by exact_mod_cast h`. Conclude with `(pow_left_inj₀ (norm_nonneg _) (by positivity) two_ne_zero).1 h2`.
-/
theorem norm_of_isIsoBilin {Tm : H₁ →ₗ[ℂ] H₂ →ₗ[ℂ] FF} (hI : IsIsoBilin Tm) (x : H₁) (y : H₂) :
    ‖Tm x y‖ = ‖x‖ * ‖y‖ := by
  have h := hI x x y y
  rw [inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K, ← mul_pow] at h
  have h2 : ‖Tm x y‖ ^ 2 = (‖x‖ * ‖y‖) ^ 2 := by exact_mod_cast h
  exact (pow_left_inj₀ (norm_nonneg _) (by positivity) two_ne_zero).1 h2

/- English proof (translation)
Set `ℓ : H₁ →L[ℂ] ℂ` to `((innerₛₗ ℂ φ) ∘ₗ Tm.flip y).mkContinuous (‖φ‖ * ‖y‖) fun x => by`. Use `norm_inner_le_norm (𝕜 := ℂ) φ (Tm x y)` as an intermediate fact. Rewrite `this` using `[norm_of_isIsoBilin hI]`. Simplify `this` using `[mul_assoc, mul_comm, mul_left_comm]`. Take `⟨w, hw⟩` from `(InnerProductSpace.toDual ℂ H₁).surjective ℓ`.

Use `⟨w, fun x => ?_⟩` and prove the remaining obligations. Establish `h : ⟪w, x⟫_ℂ = ⟪φ, Tm x y⟫_ℂ`. Use `congrArg (fun f : H₁ →L[ℂ] ℂ => f x) hw` as an intermediate fact. Simplify `this` using `[ℓ]`. Rewrite using `[← inner_conj_symm, h, inner_conj_symm]`.
-/
theorem exists_riesz [CompleteSpace H₁] {Tm : H₁ →ₗ[ℂ] H₂ →ₗ[ℂ] FF} (hI : IsIsoBilin Tm) (φ : FF) (y : H₂) :
    ∃ w : H₁, ∀ x, ⟪x, w⟫_ℂ = ⟪Tm x y, φ⟫_ℂ := by
  let ℓ : H₁ →L[ℂ] ℂ := ((innerₛₗ ℂ φ) ∘ₗ Tm.flip y).mkContinuous (‖φ‖ * ‖y‖) fun x => by
    have := norm_inner_le_norm (𝕜 := ℂ) φ (Tm x y)
    rw [norm_of_isIsoBilin hI] at this
    simpa [mul_assoc, mul_comm, mul_left_comm] using this
  obtain ⟨w, hw⟩ := (InnerProductSpace.toDual ℂ H₁).surjective ℓ
  refine ⟨w, fun x => ?_⟩
  have h : ⟪w, x⟫_ℂ = ⟪φ, Tm x y⟫_ℂ := by
    have := congrArg (fun f : H₁ →L[ℂ] ℂ => f x) hw
    simpa [ℓ] using this
  rw [← inner_conj_symm, h, inner_conj_symm]

/- English proof (translation)
Use `choose w hw using exists_riesz hI`. Use `⟨LinearMap.mk₂'ₛₗ (RingHom.id ℂ) (starRingEnd ℂ) w ?_ ?_ ?_ ?_, fun φ y x => hw φ y x, ?_⟩` and prove the remaining obligations. Introduce `a b y`. Conclude with `ext_inner_left ℂ fun x => by simp [hw, inner_add_right]`. Introduce `c a y`.

Conclude with `ext_inner_left ℂ fun x => by simp [hw, inner_smul_right]`. Introduce `a y z`. Conclude with `ext_inner_left ℂ fun x => by simp [hw, inner_add_right, inner_add_left]`. Introduce `c a y`. Conclude with `ext_inner_left ℂ fun x => by simp [hw, inner_smul_right, inner_smul_left, mul_comm]`.

Introduce `It hIt`. Use extensionality with `φ y`. Conclude with `ext_inner_left ℂ fun x => (hIt φ y x).trans (hw φ y x).symm`.
-/
theorem existsUnique_isContr [CompleteSpace H₁] {Tm : H₁ →ₗ[ℂ] H₂ →ₗ[ℂ] FF} (hI : IsIsoBilin Tm) :
    ∃! It : FF →ₗ[ℂ] H₂ →ₛₗ[starRingEnd ℂ] H₁, IsContr Tm It := by
  choose w hw using exists_riesz hI
  refine ⟨LinearMap.mk₂'ₛₗ (RingHom.id ℂ) (starRingEnd ℂ) w ?_ ?_ ?_ ?_, fun φ y x => hw φ y x, ?_⟩
  · intro a b y
    exact ext_inner_left ℂ fun x => by simp [hw, inner_add_right]
  · intro c a y
    exact ext_inner_left ℂ fun x => by simp [hw, inner_smul_right]
  · intro a y z
    exact ext_inner_left ℂ fun x => by simp [hw, inner_add_right, inner_add_left]
  · intro c a y
    exact ext_inner_left ℂ fun x => by simp [hw, inner_smul_right, inner_smul_left, mul_comm]
  · intro It hIt
    ext φ y
    exact ext_inner_left ℂ fun x => (hIt φ y x).trans (hw φ y x).symm

end Hilbert

/- English proof (translation)
Introduce `H₁ H₂ FF _ _ _ _ _ _ _ _ _ G₁ G₂ _ _ π₁ π₂ ρ Tm hI hE`. Conclude with `⟨existsUnique_isContr hI, fun It hC => contrProps_of hI hE hC⟩`.
-/
theorem contrHilbert : ContrHilbert := by
  intro H₁ H₂ FF _ _ _ _ _ _ _ _ _ G₁ G₂ _ _ π₁ π₂ ρ Tm hI hE
  exact ⟨existsUnique_isContr hI, fun It hC => contrProps_of hI hE hC⟩

section Tensor

open MvPolynomial

variable {ι : Type} [Fintype ι] {σ : ι → Type} {Var : Type} (e : (Σ τ, σ τ) ≃ Var)

omit [Fintype ι] in
/- English proof (translation)
The claim follows from `e.injective.comp sigma_mk_injective`.
-/
theorem emb_injective (i : ι) : Function.Injective fun s : σ i => e ⟨i, s⟩ :=
  e.injective.comp sigma_mk_injective

def res (α : Var →₀ ℕ) (i : ι) : σ i →₀ ℕ :=
  Finsupp.comapDomain (fun s : σ i => e ⟨i, s⟩) α (emb_injective e i).injOn

/- English proof (translation)
Use function extensionality and compare the values at `j`. Use extensionality with `s`. Express the relevant statement in the definitionally equal form `(∑ i, Finsupp.mapDomain (fun s : σ i => e ⟨i, s⟩) (a i)) (e ⟨j, s⟩) = a j s`. Rewrite using `[Finsupp.finset_sum_apply, Finset.sum_eq_single j]`. Conclude with `Finsupp.mapDomain_apply (emb_injective e j) _ _`.

Introduce `i _ hi`. Use `Finsupp.mapDomain_notin_range _ _ ?_` and prove the remaining obligations. Introduce and unpack `⟨t, ht⟩`. Conclude with `hi (congrArg Sigma.fst (e.injective ht))`. Simplify using the standard rewrite rules.
-/
theorem res_sum (a : ∀ i, σ i →₀ ℕ) :
    res e (∑ i, Finsupp.mapDomain (fun s : σ i => e ⟨i, s⟩) (a i)) = a := by
  classical
  funext j
  ext s
  change (∑ i, Finsupp.mapDomain (fun s : σ i => e ⟨i, s⟩) (a i)) (e ⟨j, s⟩) = a j s
  rw [Finsupp.finset_sum_apply, Finset.sum_eq_single j]
  · exact Finsupp.mapDomain_apply (emb_injective e j) _ _
  · intro i _ hi
    refine Finsupp.mapDomain_notin_range _ _ ?_
    rintro ⟨t, ht⟩
    exact hi (congrArg Sigma.fst (e.injective ht))
  · simp

variable {A B : ι → Type} [∀ i, AddCommGroup (A i)] [∀ i, Module ℂ (A i)]
  [∀ i, AddCommGroup (B i)] [∀ i, Module ℂ (B i)]

def tens (I : ∀ i, MvPolynomial (σ i) ℂ →ₗ[ℂ] A i →ₗ[ℂ] B i) :
    MvPolynomial Var ℂ →ₗ[ℂ] (⨂[ℂ] i, A i) →ₗ[ℂ] ⨂[ℂ] i, B i :=
  (basisMonomials Var ℂ).constr ℂ fun α => PiTensorProduct.map fun i => I i (monomial (res e α i) 1)

/- English proof (translation)
Set `pr : MultilinearMap ℂ (fun i : ι => MvPolynomial (σ i) ℂ) (MvPolynomial Var ℂ)` to `(MultilinearMap.mkPiAlgebra ℂ ι (MvPolynomial Var ℂ)).compLinearMap fun i => (rename (fun s : σ i => e ⟨i, s⟩) : MvPolynomial (σ i) ℂ →ₐ[ℂ] _).toLinearMap`. Establish `hpr : ∀ P, pr P = ∏ i, rename (fun s : σ i => e ⟨i, s⟩) (P i)` using `fun P => by simp [pr]`. Establish `key : (tens e I).compMultilinearMap pr = (PiTensorProduct.mapMultilinear ℂ A B).compLinearMap I`. Use `Module.Basis.ext_multilinear (fun i => basisMonomials (σ i) ℂ) fun a => ?_` and prove the remaining obligations. Simplify using `only [LinearMap.compMultilinearMap_apply, hpr, coe_basisMonomials, MultilinearMap.compLinearMap_apply, PiTensorProduct.mapMultilinear_apply, rename_monomial]`.

Rewrite using `[← monomial_sum_one]`. Use `(basisMonomials Var ℂ).constr_basis ℂ (fun α => PiTensorProduct.map fun i => I i (monomial (res e α i) 1)) (∑ i, Finsupp.mapDomain (fun s : σ i => e ⟨i, s⟩) (a i))` as an intermediate fact. Rewrite `this` using `[res_sum, coe_basisMonomials]`. Conclude with `this`. Use `congrArg (fun f => f P) key` as an intermediate fact.

Simplify `this` using `[hpr]`.
-/
theorem tens_prod (I : ∀ i, MvPolynomial (σ i) ℂ →ₗ[ℂ] A i →ₗ[ℂ] B i) (P : ∀ i, MvPolynomial (σ i) ℂ) :
    tens e I (∏ i, rename (fun s : σ i => e ⟨i, s⟩) (P i)) = PiTensorProduct.map fun i => I i (P i) := by
  classical
  let pr : MultilinearMap ℂ (fun i : ι => MvPolynomial (σ i) ℂ) (MvPolynomial Var ℂ) :=
    (MultilinearMap.mkPiAlgebra ℂ ι (MvPolynomial Var ℂ)).compLinearMap
      fun i => (rename (fun s : σ i => e ⟨i, s⟩) : MvPolynomial (σ i) ℂ →ₐ[ℂ] _).toLinearMap
  have hpr : ∀ P, pr P = ∏ i, rename (fun s : σ i => e ⟨i, s⟩) (P i) := fun P => by simp [pr]
  have key : (tens e I).compMultilinearMap pr
      = (PiTensorProduct.mapMultilinear ℂ A B).compLinearMap I := by
    refine Module.Basis.ext_multilinear (fun i => basisMonomials (σ i) ℂ) fun a => ?_
    simp only [LinearMap.compMultilinearMap_apply, hpr, coe_basisMonomials,
      MultilinearMap.compLinearMap_apply, PiTensorProduct.mapMultilinear_apply, rename_monomial]
    rw [← monomial_sum_one]
    have := (basisMonomials Var ℂ).constr_basis ℂ
      (fun α => PiTensorProduct.map fun i => I i (monomial (res e α i) 1))
      (∑ i, Finsupp.mapDomain (fun s : σ i => e ⟨i, s⟩) (a i))
    rw [res_sum, coe_basisMonomials] at this
    exact this
  have := congrArg (fun f => f P) key
  simpa [hpr] using this

/- English proof (translation)
Use `choose l hl using fun i => Module.Projective.exists_dual_eq_one ℂ (hv i)`. Introduce `h0`. Use `congrArg (PiTensorProduct.lift ((MultilinearMap.mkPiAlgebra ℂ ι ℂ).compLinearMap l)) h0` as an intermediate fact. Simplify using `[hl] at this`.
-/
theorem tprod_ne_zero (v : ∀ i, B i) (hv : ∀ i, v i ≠ 0) : PiTensorProduct.tprod ℂ v ≠ 0 := by
  classical
  choose l hl using fun i => Module.Projective.exists_dual_eq_one ℂ (hv i)
  intro h0
  have := congrArg (PiTensorProduct.lift ((MultilinearMap.mkPiAlgebra ℂ ι ℂ).compLinearMap l)) h0
  simp [hl] at this

end Tensor

/- English proof (translation)
Introduce `ι _ σ Var e A B _ _ _ _ I`. Establish `h : IsTensorIt e I (tens e I)` using `fun P v => by`. Rewrite using `[tens_prod, PiTensorProduct.map_tprod]`. Use `⟨tens e I, h, fun hI h0 => ?_⟩` and prove the remaining obligations. Establish `hex : ∀ i, ∃ P v, I i P v ≠ 0`.

Introduce `i`. Assume the negation of the conclusion as `hc`. Use `push Not at hc`. Conclude with `hI i (LinearMap.ext fun P => LinearMap.ext fun v => hc P v)`. Use `choose P v hPv using hex`.

Establish `h1` using `h P v`. Rewrite `h1` using `[h0]`. Conclude with `tprod_ne_zero _ hPv h1.symm`.
-/
theorem contrTensor : ContrTensor := by
  intro ι _ σ Var e A B _ _ _ _ I
  have h : IsTensorIt e I (tens e I) := fun P v => by
    rw [tens_prod, PiTensorProduct.map_tprod]
  refine ⟨tens e I, h, fun hI h0 => ?_⟩
  have hex : ∀ i, ∃ P v, I i P v ≠ 0 := by
    intro i
    by_contra hc
    push Not at hc
    exact hI i (LinearMap.ext fun P => LinearMap.ext fun v => hc P v)
  choose P v hPv using hex
  have h1 := h P v
  rw [h0] at h1
  exact tprod_ne_zero _ hPv h1.symm

/- English proof (translation)
Assemble the required witnesses or components as `⟨contrHilbert, contrTensor⟩`.
-/
theorem contraction : GlobalTheory.IndefiniteRowSideFullHecke.ContractionTensorModels.Contraction := ⟨contrHilbert, contrTensor⟩

end GlobalTheory.ContrObj

end

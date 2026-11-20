import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ContractionTensorModels

noncomputable section

open scoped InnerProductSpace TensorProduct

namespace GlobalTheory.Contr

open GlobalTheory.IndefiniteRowSideFullHecke.ContractionTensorModels

section Hilbert

variable {H₁ H₂ FF : Type}
  [NormedAddCommGroup H₁] [InnerProductSpace ℂ H₁] [CompleteSpace H₁]
  [NormedAddCommGroup H₂] [InnerProductSpace ℂ H₂]
  [NormedAddCommGroup FF] [InnerProductSpace ℂ FF] [CompleteSpace FF]

omit [CompleteSpace H₁] [CompleteSpace FF] in

/- English proof (translation)
Establish `h` using `hI x x y y`. Rewrite `h` using `[inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K, ← mul_pow]`. Establish `h2 : ‖Tm x y‖ ^ 2 = (‖x‖ * ‖y‖) ^ 2` using `by exact_mod_cast h`. Conclude with `(pow_left_inj₀ (norm_nonneg _) (by positivity) two_ne_zero).1 h2`.
-/
theorem norm_isoBilin {Tm : H₁ →ₗ[ℂ] H₂ →ₗ[ℂ] FF} (hI : IsIsoBilin Tm) (x : H₁) (y : H₂) :
    ‖Tm x y‖ = ‖x‖ * ‖y‖ := by
  have h := hI x x y y
  rw [inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K, ← mul_pow] at h
  have h2 : ‖Tm x y‖ ^ 2 = (‖x‖ * ‖y‖) ^ 2 := by exact_mod_cast h
  exact (pow_left_inj₀ (norm_nonneg _) (by positivity) two_ne_zero).1 h2

/- English proof (translation)
Set `L : H₂ → (H₁ →L[ℂ] FF)` to `fun y => (Tm.flip y).mkContinuous ‖y‖ fun x => by simp [norm_isoBilin hI, mul_comm]`. Set `f : FF → H₂ → H₁` to `fun φ y => ContinuousLinearMap.adjoint (L y) φ`. Establish `hf : ∀ φ y x, ⟪x, f φ y⟫_ℂ = ⟪Tm x y, φ⟫_ℂ` using `fun φ y x => by`. Simplify using `only [f, ContinuousLinearMap.adjoint_inner_right]`. Both sides reduce to the same expression.

Use `⟨LinearMap.mk₂'ₛₗ (RingHom.id ℂ) (starRingEnd ℂ) f ?_ ?_ ?_ ?_, hf⟩` and prove the remaining obligations. Introduce `a b y`. Conclude with `ext_inner_left ℂ fun x => by simp only [inner_add_right, hf]`. Introduce `c a y`. Conclude with `ext_inner_left ℂ fun x => by simp only [inner_smul_right, hf, RingHom.id_apply]`.

Introduce `a y z`. Conclude with `ext_inner_left ℂ fun x => by simp only [inner_add_right, hf, map_add, inner_add_left]`. Introduce `c a y`. Conclude with `ext_inner_left ℂ fun x => by simp only [inner_smul_right, hf, map_smul, inner_smul_left]`.
-/
theorem exists_isContr {Tm : H₁ →ₗ[ℂ] H₂ →ₗ[ℂ] FF} (hI : IsIsoBilin Tm) :
    ∃ It : FF →ₗ[ℂ] H₂ →ₛₗ[starRingEnd ℂ] H₁, IsContr Tm It := by
  let L : H₂ → (H₁ →L[ℂ] FF) := fun y =>
    (Tm.flip y).mkContinuous ‖y‖ fun x => by simp [norm_isoBilin hI, mul_comm]
  let f : FF → H₂ → H₁ := fun φ y => ContinuousLinearMap.adjoint (L y) φ
  have hf : ∀ φ y x, ⟪x, f φ y⟫_ℂ = ⟪Tm x y, φ⟫_ℂ := fun φ y x => by
    simp only [f, ContinuousLinearMap.adjoint_inner_right]
    rfl
  refine ⟨LinearMap.mk₂'ₛₗ (RingHom.id ℂ) (starRingEnd ℂ) f ?_ ?_ ?_ ?_, hf⟩
  · intro a b y
    exact ext_inner_left ℂ fun x => by simp only [inner_add_right, hf]
  · intro c a y
    exact ext_inner_left ℂ fun x => by simp only [inner_smul_right, hf, RingHom.id_apply]
  · intro a y z
    exact ext_inner_left ℂ fun x => by simp only [inner_add_right, hf, map_add, inner_add_left]
  · intro c a y
    exact ext_inner_left ℂ fun x => by simp only [inner_smul_right, hf, map_smul, inner_smul_left]

omit [CompleteSpace H₁] [CompleteSpace FF] in

/- English proof (translation)
Use extensionality with `φ y`. Conclude with `ext_inner_left ℂ fun x => by rw [h, h']`.
-/
theorem isContr_unique {Tm : H₁ →ₗ[ℂ] H₂ →ₗ[ℂ] FF} {It It' : FF →ₗ[ℂ] H₂ →ₛₗ[starRingEnd ℂ] H₁}
    (h : IsContr Tm It) (h' : IsContr Tm It') : It = It' := by
  ext φ y
  exact ext_inner_left ℂ fun x => by rw [h, h']

end Hilbert

/- English proof (translation)
Introduce `H₁ H₂ FF _ _ _ _ _ _ _ _ _ G₁ G₂ _ _ π₁ π₂ ρ Tm hI hE`. Take `⟨It, hIt⟩` from `exists_isContr hI`. Conclude with `⟨⟨It, hIt, fun It' h' => isContr_unique h' hIt⟩, fun It' h' => contrProps_of hI hE h'⟩`.
-/
theorem contrHilbert : ContrHilbert := by
  intro H₁ H₂ FF _ _ _ _ _ _ _ _ _ G₁ G₂ _ _ π₁ π₂ ρ Tm hI hE
  obtain ⟨It, hIt⟩ := exists_isContr hI
  exact ⟨⟨It, hIt, fun It' h' => isContr_unique h' hIt⟩, fun It' h' => contrProps_of hI hE h'⟩

/- English proof (translation)
Establish `: ∀ τ, ∃ f : Module.Dual ℂ (B τ), f (w τ) ≠ 0` using `fun τ => by`. Assume the negation of the conclusion as `hc`. Use `push_neg at hc`. Conclude with `hw τ ((Module.forall_dual_apply_eq_zero_iff ℂ (w τ)).1 hc)`. Use `choose f hf using this`.

Introduce `h`. Use `congrArg (PiTensorProduct.lift ((MultilinearMap.mkPiAlgebra ℂ ι ℂ).compLinearMap f)) h` as an intermediate fact. Simplify using `[Finset.prod_eq_zero_iff, hf] at this`.
-/
theorem tprod_ne_zero_of_ne {ι : Type} [Fintype ι] {B : ι → Type} [∀ τ, AddCommGroup (B τ)]
    [∀ τ, Module ℂ (B τ)] (w : ∀ τ, B τ) (hw : ∀ τ, w τ ≠ 0) : PiTensorProduct.tprod ℂ w ≠ 0 := by
  classical
  have : ∀ τ, ∃ f : Module.Dual ℂ (B τ), f (w τ) ≠ 0 := fun τ => by
    by_contra hc
    push_neg at hc
    exact hw τ ((Module.forall_dual_apply_eq_zero_iff ℂ (w τ)).1 hc)
  choose f hf using this
  intro h
  have := congrArg (PiTensorProduct.lift ((MultilinearMap.mkPiAlgebra ℂ ι ℂ).compLinearMap f)) h
  simp [Finset.prod_eq_zero_iff, hf] at this

/- English proof (translation)
Introduce `ι _ σ Var e A B _ _ _ _ Itl`. Establish `hinj : ∀ τ, Function.Injective fun s : σ τ => e ⟨τ, s⟩` using `fun τ => e.injective.comp sigma_mk_injective`. Set `r : (Var →₀ ℕ) → ∀ τ, σ τ →₀ ℕ` to `fun m τ => m.comapDomain (fun s => e ⟨τ, s⟩) (hinj τ).injOn`. Set `It : MvPolynomial Var ℂ →ₗ[ℂ] (⨂[ℂ] τ, A τ) →ₗ[ℂ] ⨂[ℂ] τ, B τ` to `(MvPolynomial.basisMonomials Var ℂ).constr ℂ fun m => PiTensorProduct.map fun τ => Itl τ (MvPolynomial.monomial (r m τ) 1)`. Establish `hr : ∀ m : ∀ τ, σ τ →₀ ℕ, r (∑ τ, (m τ).mapDomain fun s => e ⟨τ, s⟩) = m`.

Introduce `m`. Use function extensionality and compare the values at `τ`. Use extensionality with `s`. Simplify using `only [r, Finsupp.comapDomain_apply, Finsupp.finset_sum_apply]`. Rewrite using `[Finset.sum_eq_single τ]`.

Conclude with `Finsupp.mapDomain_apply (hinj τ) _ _`. Introduce `τ' _ hne`. Apply `Finsupp.mapDomain_notin_range` to reduce the goal to its premises. Introduce and unpack `⟨s', hs'⟩`. Conclude with `hne (congrArg Sigma.fst (e.injective hs'))`.

Simplify using the standard rewrite rules. Establish `key : It.compMultilinearMap ((MultilinearMap.mkPiAlgebra ℂ ι (MvPolynomial Var ℂ)).compLinearMap fun τ => (MvPolynomial.rename (fun s : σ τ => e ⟨τ, s⟩)).toLinearMap) = (PiTensorProduct.mapMultilinear ℂ A B).compLinearMap Itl`. Apply `Module.Basis.ext_multilinear fun τ => MvPolynomial.basisMonomials (σ τ) ℂ` to reduce the goal to its premises. Introduce `m`. Simplify using `only [LinearMap.compMultilinearMap_apply, MultilinearMap.compLinearMap_apply, MultilinearMap.mkPiAlgebra_apply, AlgHom.toLinearMap_apply, MvPolynomial.coe_basisMonomials, MvPolynomial.rename_monomial, PiTensorProduct.mapMultilinear_apply]`.

Rewrite using `[← MvPolynomial.monomial_sum_one]`. Use `(MvPolynomial.basisMonomials Var ℂ).constr_basis ℂ (fun m => PiTensorProduct.map fun τ => Itl τ (MvPolynomial.monomial (r m τ) 1)) (∑ τ, (m τ).mapDomain fun s => e ⟨τ, s⟩)` as an intermediate fact. Rewrite `this` using `[hr]`. Simplify `this` using `[It]`. Establish `hT : IsTensorIt e Itl It`.

Introduce `P v`. Use `congrArg (fun F => F P (PiTensorProduct.tprod ℂ v)) key` as an intermediate fact. Simplify using `using this`. Use `⟨It, hT, fun hne h0 => ?_⟩` and prove the remaining obligations. Establish `: ∀ τ, ∃ P v, Itl τ P v ≠ 0` using `fun τ => by`.

Assume the negation of the conclusion as `hc`. Use `push_neg at hc`. Conclude with `hne τ (LinearMap.ext fun P => LinearMap.ext fun v => hc P v)`. Use `choose P v hPv using this`. Apply `tprod_ne_zero_of_ne _ hPv` to reduce the goal to its premises.

Rewrite using `[← hT P v, h0]`. Both sides reduce to the same expression.
-/
theorem contrTensor : ContrTensor := by
  intro ι _ σ Var e A B _ _ _ _ Itl
  classical
  have hinj : ∀ τ, Function.Injective fun s : σ τ => e ⟨τ, s⟩ := fun τ =>
    e.injective.comp sigma_mk_injective
  let r : (Var →₀ ℕ) → ∀ τ, σ τ →₀ ℕ := fun m τ => m.comapDomain (fun s => e ⟨τ, s⟩) (hinj τ).injOn
  let It : MvPolynomial Var ℂ →ₗ[ℂ] (⨂[ℂ] τ, A τ) →ₗ[ℂ] ⨂[ℂ] τ, B τ :=
    (MvPolynomial.basisMonomials Var ℂ).constr ℂ fun m =>
      PiTensorProduct.map fun τ => Itl τ (MvPolynomial.monomial (r m τ) 1)
  have hr : ∀ m : ∀ τ, σ τ →₀ ℕ, r (∑ τ, (m τ).mapDomain fun s => e ⟨τ, s⟩) = m := by
    intro m
    funext τ
    ext s
    simp only [r, Finsupp.comapDomain_apply, Finsupp.finset_sum_apply]
    rw [Finset.sum_eq_single τ]
    · exact Finsupp.mapDomain_apply (hinj τ) _ _
    · intro τ' _ hne
      apply Finsupp.mapDomain_notin_range
      rintro ⟨s', hs'⟩
      exact hne (congrArg Sigma.fst (e.injective hs'))
    · simp
  have key : It.compMultilinearMap ((MultilinearMap.mkPiAlgebra ℂ ι (MvPolynomial Var ℂ)).compLinearMap
      fun τ => (MvPolynomial.rename (fun s : σ τ => e ⟨τ, s⟩)).toLinearMap) =
      (PiTensorProduct.mapMultilinear ℂ A B).compLinearMap Itl := by
    apply Module.Basis.ext_multilinear fun τ => MvPolynomial.basisMonomials (σ τ) ℂ
    intro m
    simp only [LinearMap.compMultilinearMap_apply, MultilinearMap.compLinearMap_apply,
      MultilinearMap.mkPiAlgebra_apply, AlgHom.toLinearMap_apply, MvPolynomial.coe_basisMonomials,
      MvPolynomial.rename_monomial, PiTensorProduct.mapMultilinear_apply]
    rw [← MvPolynomial.monomial_sum_one]
    have := (MvPolynomial.basisMonomials Var ℂ).constr_basis ℂ (fun m =>
      PiTensorProduct.map fun τ => Itl τ (MvPolynomial.monomial (r m τ) 1))
      (∑ τ, (m τ).mapDomain fun s => e ⟨τ, s⟩)
    rw [hr] at this
    simpa [It] using this
  have hT : IsTensorIt e Itl It := by
    intro P v
    have := congrArg (fun F => F P (PiTensorProduct.tprod ℂ v)) key
    simpa using this
  refine ⟨It, hT, fun hne h0 => ?_⟩
  have : ∀ τ, ∃ P v, Itl τ P v ≠ 0 := fun τ => by
    by_contra hc
    push_neg at hc
    exact hne τ (LinearMap.ext fun P => LinearMap.ext fun v => hc P v)
  choose P v hPv using this
  apply tprod_ne_zero_of_ne _ hPv
  rw [← hT P v, h0]
  rfl

/- English proof (translation)
Assemble the required witnesses or components as `⟨contrHilbert, contrTensor⟩`.
-/
theorem contraction : Contraction := ⟨contrHilbert, contrTensor⟩

/- English proof (translation)
The claim follows from `contrTensorModels_of contrTensor`.
-/
theorem contrTensorModels : ContrTensorModels := contrTensorModels_of contrTensor

end GlobalTheory.Contr

end

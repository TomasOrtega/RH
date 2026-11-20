import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CentralizerTensorForms
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.NotCompactOfIdempotent
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CyclicVectorOfSeparableCharpolyField
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CyclicVectorSemilocalOfCyclicVectorField
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CyclicVectorGeneratedAlgebraStructure

open Matrix Polynomial

namespace GlobalTheory.IntConj

section Krylov

variable {A : Type} [CommRing A] {n : Type} [Fintype n] [DecidableEq n]

/- English proof (translation)
Use extensionality with `i j`. Establish `hk : ∀ k : ℕ, x * M' ^ k = M ^ k * x` using `fun k => SemiconjBy.pow_right h k`. Combine the equalities or inequalities in the displayed calculation. Simplify using `[GlobalTheory.RegSS.krylov, Matrix.mul_apply, Matrix.mulVec, dotProduct]`. Use `_ = ((M ^ ((Fintype.equivFin n j : Fin (Fintype.card n)) : ℕ)) *ᵥ (x *ᵥ w)) i := by`.

Rewrite using `[mulVec_mulVec, hk, ← mulVec_mulVec]`. Use `_ = GlobalTheory.RegSS.krylov M (x *ᵥ w) i j := by simp [GlobalTheory.RegSS.krylov]`.
-/
theorem mul_krylov_of_semiconj {M M' x : Matrix n n A} (h : x * M' = M * x) (w : n → A) :
    x * GlobalTheory.RegSS.krylov M' w = GlobalTheory.RegSS.krylov M (x *ᵥ w) := by
  ext i j
  have hk : ∀ k : ℕ, x * M' ^ k = M ^ k * x := fun k => SemiconjBy.pow_right h k
  calc (x * GlobalTheory.RegSS.krylov M' w) i j
      = (x *ᵥ ((M' ^ ((Fintype.equivFin n j : Fin (Fintype.card n)) : ℕ)) *ᵥ w)) i := by
        simp [GlobalTheory.RegSS.krylov, Matrix.mul_apply, Matrix.mulVec, dotProduct]
    _ = ((M ^ ((Fintype.equivFin n j : Fin (Fintype.card n)) : ℕ)) *ᵥ (x *ᵥ w)) i := by
        rw [mulVec_mulVec, hk, ← mulVec_mulVec]
    _ = GlobalTheory.RegSS.krylov M (x *ᵥ w) i j := by simp [GlobalTheory.RegSS.krylov]

end Krylov

/- English proof (translation)
Rewrite using `[Valuation.mem_valuationSubring_iff, NormedField.valuation_apply, ← NNReal.coe_le_coe]`. Simplify using the standard rewrite rules.
-/
theorem mem_unitBall {E : Type} [NormedField E] [IsUltrametricDist E] (y : E) :
    y ∈ (NormedField.valuation (K := E)).valuationSubring ↔ ‖y‖ ≤ 1 := by
  rw [Valuation.mem_valuationSubring_iff, NormedField.valuation_apply, ← NNReal.coe_le_coe]
  simp

/- English proof (translation)
Take `⟨u, rfl⟩` from `ha`. Establish `h` using `congrArg (fun y : (NormedField.valuation (K := E)).valuationSubring => ‖(y : E)‖) u.mul_inv`. Simplify using `only [MulMemClass.coe_mul, norm_mul, OneMemClass.coe_one, norm_one] at h`. Establish `h1 : ‖((u : (NormedField.valuation (K` using `E)).valuationSubring) : E)‖ ≤ 1 := (mem_unitBall _).1 (u : (NormedField.valuation (K := E)).valuationSubring).2`. Establish `h2 : ‖(((u⁻¹ : _ˣ) : (NormedField.valuation (K` using `E)).valuationSubring) : E)‖ ≤ 1 := (mem_unitBall _).1 ((u⁻¹ : _ˣ) : (NormedField.valuation (K := E)).valuationSubring).2`.

Use polynomial arithmetic with `[norm_nonneg ((u : (NormedField.valuation (K := E)).valuationSubring) : E), norm_nonneg (((u⁻¹ : _ˣ) : (NormedField.valuation (K := E)).valuationSubring) : E)]`.
-/
theorem norm_eq_one_of_isUnit {E : Type} [NormedField E] [IsUltrametricDist E]
    {a : (NormedField.valuation (K := E)).valuationSubring} (ha : IsUnit a) : ‖(a : E)‖ = 1 := by
  obtain ⟨u, rfl⟩ := ha
  have h := congrArg (fun y : (NormedField.valuation (K := E)).valuationSubring => ‖(y : E)‖) u.mul_inv
  simp only [MulMemClass.coe_mul, norm_mul, OneMemClass.coe_one, norm_one] at h
  have h1 : ‖((u : (NormedField.valuation (K := E)).valuationSubring) : E)‖ ≤ 1 :=
    (mem_unitBall _).1 (u : (NormedField.valuation (K := E)).valuationSubring).2
  have h2 : ‖(((u⁻¹ : _ˣ) : (NormedField.valuation (K := E)).valuationSubring) : E)‖ ≤ 1 :=
    (mem_unitBall _).1 ((u⁻¹ : _ˣ) : (NormedField.valuation (K := E)).valuationSubring).2
  nlinarith [norm_nonneg ((u : (NormedField.valuation (K := E)).valuationSubring) : E),
    norm_nonneg (((u⁻¹ : _ˣ) : (NormedField.valuation (K := E)).valuationSubring) : E)]

end GlobalTheory.IntConj

namespace GlobalTheory.IntConj

/- English proof (translation)
Set `O` to `(NormedField.valuation (K := E)).valuationSubring`. Set `φ : O →+* E` to `O.subtype`. Establish `hφ : Function.Injective φ` using `Subtype.val_injective`. Establish `lift : ∀ M : Matrix (Fin n) (Fin n) E, (∀ i j, ‖M i j‖ ≤ 1) → ∃ M₀ : Matrix (Fin n) (Fin n) O, M₀.map φ = M` using `fun M hM => ⟨Matrix.of fun i j => ⟨M i j, (mem_unitBall _).2 (hM i j)⟩, by ext i j; rfl⟩`. Establish `liftP : ∀ p : E[X], (∀ i, ‖p.coeff i‖ ≤ 1) → ∃ p₀ : O[X], p₀.map φ = p`.

Introduce `p hp`. Establish `: p ∈ Polynomial.lifts φ` using `(lifts_iff_coeff_lifts p).2 fun k => ⟨⟨_, (mem_unitBall _).2 (hp k)⟩, rfl⟩`. Conclude with `(mem_lifts p).1 this`. Take `⟨u, v, hu, hv, huv⟩` from `hsep`. Take `⟨u₀, rfl⟩` from `liftP u hu`.

Take `⟨v₀, rfl⟩` from `liftP v hv`. Establish `sep : ∀ M₀ : Matrix (Fin n) (Fin n) O, (M₀.map φ).charpoly = N.charpoly → M₀.charpoly.Separable`. Introduce `M₀ hM`. Use `⟨u₀, v₀, ?_⟩` and prove the remaining obligations. Apply `Polynomial.map_injective φ hφ` to reduce the goal to its premises.

Rewrite using `[Polynomial.map_add, Polynomial.map_mul, Polynomial.map_mul, ← Polynomial.derivative_map, ← Matrix.charpoly_map, hM, Polynomial.map_one]`. Conclude with `huv`. Take `⟨X, rfl⟩` from `hx`. Establish `hXd : IsUnit (X : Matrix (Fin n) (Fin n) E).det` using `(Matrix.isUnit_iff_isUnit_det _).1 X.isUnit`. Establish `hcp : ((X : Matrix (Fin n) (Fin n) E)⁻¹ * N * (X : Matrix (Fin n) (Fin n) E)).charpoly = N.charpoly`.

Conclude with `Matrix.charpoly_units_conj' X N`. Take `⟨N₀, hN₀⟩` from `lift N hN`. Take `⟨N₀', hN₀'⟩` from `lift _ hN'`. Take `⟨v₁, hv₁⟩` from `GlobalTheory.RegSS.Semilocal.cyclicSemilocal_of_cyclicField GlobalTheory.RegSS.cyclicField O (Fin n) N₀ (sep N₀ (by rw [hN₀]))`. Take `⟨w₁, hw₁⟩` from `GlobalTheory.RegSS.Semilocal.cyclicSemilocal_of_cyclicField GlobalTheory.RegSS.cyclicField O (Fin n) N₀' (sep N₀' (by rw [hN₀', hcp]))`.

Establish `hK : (GlobalTheory.RegSS.krylov N₀ v₁).map φ = GlobalTheory.RegSS.krylov N (φ ∘ v₁)`. Rewrite using `[GlobalTheory.RegSS.Semilocal.krylov_map_ringHom, hN₀]`. Establish `hK' : (GlobalTheory.RegSS.krylov N₀' w₁).map φ = GlobalTheory.RegSS.krylov ((X : Matrix (Fin n) (Fin n) E)⁻¹ * N * (X : Matrix (Fin n) (Fin n) E)) (φ ∘ w₁)`. Rewrite using `[GlobalTheory.RegSS.Semilocal.krylov_map_ringHom, hN₀']`. Establish `hKu` using `GlobalTheory.RegSS.isUnit_det_map φ hv₁`.

Establish `hKu'` using `GlobalTheory.RegSS.isUnit_det_map φ hw₁`. Take `⟨-, -, hbij⟩` from `GlobalTheory.RegSS.CycAlg.cyclicAlgebra E (Fin n) N (φ ∘ v₁) (by rw [← hK]; exact hKu)`. Take `⟨l, hl⟩` from `hbij.2 ((X : Matrix (Fin n) (Fin n) E) *ᵥ (φ ∘ w₁))`. Simplify using `only at hl`. Establish `hcN : N * (l : Matrix (Fin n) (Fin n) E) = l * N` using `GlobalTheory.RegSS.commute_of_mem_genAlg rfl l.2`.

Establish `hXN : (X : Matrix (Fin n) (Fin n) E) * ((X : Matrix (Fin n) (Fin n) E)⁻¹ * N * (X : Matrix (Fin n) (Fin n) E)) = N * X`. Rewrite using `[← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hXd, Matrix.one_mul]`. Establish `key : (l : Matrix (Fin n) (Fin n) E) * (GlobalTheory.RegSS.krylov N₀ v₁).map φ = (X : Matrix (Fin n) (Fin n) E) * (GlobalTheory.RegSS.krylov N₀' w₁).map φ`. Rewrite using `[hK, hK', mul_krylov_of_semiconj hcN.symm, mul_krylov_of_semiconj hXN, hl]`. Use `set Kv := (GlobalTheory.RegSS.krylov N₀ v₁).map φ with hKv`.

Use `set Kw := (GlobalTheory.RegSS.krylov N₀' w₁).map φ with hKw`. Generalize the expression as in `(l : Matrix (Fin n) (Fin n) E) = c at key hcN`. Establish `hcu : IsUnit c`. Establish `: c = (X : Matrix (Fin n) (Fin n) E) * Kw * Kv⁻¹`. Rewrite using `[← key, Matrix.mul_nonsing_inv_cancel_right _ _ hKu]`.

Rewrite using `[this]`. Conclude with `(X.isUnit.mul ((Matrix.isUnit_iff_isUnit_det _).2 hKu')).mul ((Matrix.isUnit_iff_isUnit_det _).2 (Matrix.isUnit_nonsing_inv_det _ hKu))`. Establish `hcd : IsUnit c.det` using `(Matrix.isUnit_iff_isUnit_det _).1 hcu`. Establish `e2 : c⁻¹ * (X : Matrix (Fin n) (Fin n) E) = Kv * Kw⁻¹`. Rewrite using `[← Matrix.mul_nonsing_inv_cancel_right _ (c⁻¹ * (X : Matrix (Fin n) (Fin n) E)) hKu', Matrix.mul_assoc c⁻¹, ← key, Matrix.nonsing_inv_mul_cancel_left _ _ hcd]`.

Establish `hinv : Kw⁻¹ = ((GlobalTheory.RegSS.krylov N₀' w₁)⁻¹).map φ`. Use `Matrix.inv_eq_left_inv ?_` and prove the remaining obligations. Rewrite using `[hKw, ← RingHom.mapMatrix_apply, ← RingHom.mapMatrix_apply, ← map_mul, Matrix.nonsing_inv_mul _ hw₁, map_one]`. Establish `e3 : c⁻¹ * (X : Matrix (Fin n) (Fin n) E) = (GlobalTheory.RegSS.krylov N₀ v₁ * (GlobalTheory.RegSS.krylov N₀' w₁)⁻¹).map φ`. Rewrite using `[e2, hinv, hKv, Matrix.map_mul]`.

Use `⟨c, hcu, hcN.symm, fun i j => ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[e3]`. Conclude with `(mem_unitBall _).1 ((GlobalTheory.RegSS.krylov N₀ v₁ * (GlobalTheory.RegSS.krylov N₀' w₁)⁻¹) i j).2`. Rewrite using `[e3, ← RingHom.mapMatrix_apply, ← RingHom.map_det]`. Conclude with `norm_eq_one_of_isUnit (by`.

Rewrite using `[Matrix.det_mul]`. Conclude with `hv₁.mul (Matrix.isUnit_nonsing_inv_det _ hw₁))`.
-/
theorem exists_commuting_mul_integral (E : Type) [NontriviallyNormedField E] [IsUltrametricDist E]
    (n : ℕ) (N x : Matrix (Fin n) (Fin n) E) (hN : ∀ i j, ‖N i j‖ ≤ 1)
    (hsep : ∃ u v : Polynomial E, (∀ i, ‖u.coeff i‖ ≤ 1) ∧ (∀ i, ‖v.coeff i‖ ≤ 1) ∧
      u * N.charpoly + v * Polynomial.derivative N.charpoly = 1)
    (hx : IsUnit x) (hN' : ∀ i j, ‖(x⁻¹ * N * x) i j‖ ≤ 1) :
    ∃ c : Matrix (Fin n) (Fin n) E, IsUnit c ∧ c * N = N * c ∧ (∀ i j, ‖(c⁻¹ * x) i j‖ ≤ 1) ∧
      ‖(c⁻¹ * x).det‖ = 1 := by
  classical
  let O := (NormedField.valuation (K := E)).valuationSubring
  let φ : O →+* E := O.subtype
  have hφ : Function.Injective φ := Subtype.val_injective
  have lift : ∀ M : Matrix (Fin n) (Fin n) E, (∀ i j, ‖M i j‖ ≤ 1) →
      ∃ M₀ : Matrix (Fin n) (Fin n) O, M₀.map φ = M := fun M hM =>
    ⟨Matrix.of fun i j => ⟨M i j, (mem_unitBall _).2 (hM i j)⟩, by ext i j; rfl⟩
  have liftP : ∀ p : E[X], (∀ i, ‖p.coeff i‖ ≤ 1) → ∃ p₀ : O[X], p₀.map φ = p := by
    intro p hp
    have : p ∈ Polynomial.lifts φ :=
      (lifts_iff_coeff_lifts p).2 fun k => ⟨⟨_, (mem_unitBall _).2 (hp k)⟩, rfl⟩
    exact (mem_lifts p).1 this
  obtain ⟨u, v, hu, hv, huv⟩ := hsep
  obtain ⟨u₀, rfl⟩ := liftP u hu
  obtain ⟨v₀, rfl⟩ := liftP v hv
  have sep : ∀ M₀ : Matrix (Fin n) (Fin n) O, (M₀.map φ).charpoly = N.charpoly →
      M₀.charpoly.Separable := by
    intro M₀ hM
    refine ⟨u₀, v₀, ?_⟩
    apply Polynomial.map_injective φ hφ
    rw [Polynomial.map_add, Polynomial.map_mul, Polynomial.map_mul, ← Polynomial.derivative_map,
      ← Matrix.charpoly_map, hM, Polynomial.map_one]
    exact huv
  obtain ⟨X, rfl⟩ := hx
  have hXd : IsUnit (X : Matrix (Fin n) (Fin n) E).det :=
    (Matrix.isUnit_iff_isUnit_det _).1 X.isUnit
  have hcp : ((X : Matrix (Fin n) (Fin n) E)⁻¹ * N * (X : Matrix (Fin n) (Fin n) E)).charpoly = N.charpoly := by
    exact Matrix.charpoly_units_conj' X N
  obtain ⟨N₀, hN₀⟩ := lift N hN
  obtain ⟨N₀', hN₀'⟩ := lift _ hN'
  obtain ⟨v₁, hv₁⟩ := GlobalTheory.RegSS.Semilocal.cyclicSemilocal_of_cyclicField GlobalTheory.RegSS.cyclicField
    O (Fin n) N₀ (sep N₀ (by rw [hN₀]))
  obtain ⟨w₁, hw₁⟩ := GlobalTheory.RegSS.Semilocal.cyclicSemilocal_of_cyclicField GlobalTheory.RegSS.cyclicField
    O (Fin n) N₀' (sep N₀' (by rw [hN₀', hcp]))
  have hK : (GlobalTheory.RegSS.krylov N₀ v₁).map φ = GlobalTheory.RegSS.krylov N (φ ∘ v₁) := by
    rw [GlobalTheory.RegSS.Semilocal.krylov_map_ringHom, hN₀]
  have hK' : (GlobalTheory.RegSS.krylov N₀' w₁).map φ =
      GlobalTheory.RegSS.krylov ((X : Matrix (Fin n) (Fin n) E)⁻¹ * N * (X : Matrix (Fin n) (Fin n) E)) (φ ∘ w₁) := by
    rw [GlobalTheory.RegSS.Semilocal.krylov_map_ringHom, hN₀']
  have hKu := GlobalTheory.RegSS.isUnit_det_map φ hv₁
  have hKu' := GlobalTheory.RegSS.isUnit_det_map φ hw₁
  obtain ⟨-, -, hbij⟩ := GlobalTheory.RegSS.CycAlg.cyclicAlgebra E (Fin n) N (φ ∘ v₁) (by rw [← hK]; exact hKu)
  obtain ⟨l, hl⟩ := hbij.2 ((X : Matrix (Fin n) (Fin n) E) *ᵥ (φ ∘ w₁))
  simp only at hl
  have hcN : N * (l : Matrix (Fin n) (Fin n) E) = l * N := GlobalTheory.RegSS.commute_of_mem_genAlg rfl l.2
  have hXN : (X : Matrix (Fin n) (Fin n) E) * ((X : Matrix (Fin n) (Fin n) E)⁻¹ * N * (X : Matrix (Fin n) (Fin n) E)) = N * X := by
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hXd, Matrix.one_mul]
  have key : (l : Matrix (Fin n) (Fin n) E) * (GlobalTheory.RegSS.krylov N₀ v₁).map φ =
      (X : Matrix (Fin n) (Fin n) E) * (GlobalTheory.RegSS.krylov N₀' w₁).map φ := by
    rw [hK, hK', mul_krylov_of_semiconj hcN.symm, mul_krylov_of_semiconj hXN, hl]
  set Kv := (GlobalTheory.RegSS.krylov N₀ v₁).map φ with hKv
  set Kw := (GlobalTheory.RegSS.krylov N₀' w₁).map φ with hKw
  generalize (l : Matrix (Fin n) (Fin n) E) = c at key hcN
  have hcu : IsUnit c := by
    have : c = (X : Matrix (Fin n) (Fin n) E) * Kw * Kv⁻¹ := by
      rw [← key, Matrix.mul_nonsing_inv_cancel_right _ _ hKu]
    rw [this]
    exact (X.isUnit.mul ((Matrix.isUnit_iff_isUnit_det _).2 hKu')).mul
      ((Matrix.isUnit_iff_isUnit_det _).2 (Matrix.isUnit_nonsing_inv_det _ hKu))
  have hcd : IsUnit c.det := (Matrix.isUnit_iff_isUnit_det _).1 hcu
  have e2 : c⁻¹ * (X : Matrix (Fin n) (Fin n) E) = Kv * Kw⁻¹ := by
    rw [← Matrix.mul_nonsing_inv_cancel_right _ (c⁻¹ * (X : Matrix (Fin n) (Fin n) E)) hKu',
      Matrix.mul_assoc c⁻¹, ← key, Matrix.nonsing_inv_mul_cancel_left _ _ hcd]
  have hinv : Kw⁻¹ = ((GlobalTheory.RegSS.krylov N₀' w₁)⁻¹).map φ := by
    refine Matrix.inv_eq_left_inv ?_
    rw [hKw, ← RingHom.mapMatrix_apply, ← RingHom.mapMatrix_apply, ← map_mul,
      Matrix.nonsing_inv_mul _ hw₁, map_one]
  have e3 : c⁻¹ * (X : Matrix (Fin n) (Fin n) E) =
      (GlobalTheory.RegSS.krylov N₀ v₁ * (GlobalTheory.RegSS.krylov N₀' w₁)⁻¹).map φ := by
    rw [e2, hinv, hKv, Matrix.map_mul]
  refine ⟨c, hcu, hcN.symm, fun i j => ?_, ?_⟩
  · rw [e3]; exact (mem_unitBall _).1 ((GlobalTheory.RegSS.krylov N₀ v₁ * (GlobalTheory.RegSS.krylov N₀' w₁)⁻¹) i j).2
  · rw [e3, ← RingHom.mapMatrix_apply, ← RingHom.map_det]
    exact norm_eq_one_of_isUnit (by
      rw [Matrix.det_mul]; exact hv₁.mul (Matrix.isUnit_nonsing_inv_det _ hw₁))

end GlobalTheory.IntConj

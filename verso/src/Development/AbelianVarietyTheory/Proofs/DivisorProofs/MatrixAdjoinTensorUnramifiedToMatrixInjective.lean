import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolySubComm
open Matrix GlobalTheory.LKRes GlobalTheory.LKMid
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.PolyTensor

variable (p : ℕ) [Fact p.Prime] (K : IntermediateField ℚ_[p] (PadicAlgCl p)) (n : ℕ)
  (γ : Matrix (Fin n) (Fin n) K) (r : ℕ)

def entries : PolyAlg p K n γ →ₗ[ℚ_[p]] (Fin n × Fin n → K) where
  toFun b ij := val p K n γ b ij.1 ij.2
  map_add' a b := by funext ij; simp [map_add]
  map_smul' c b := by funext ij; simp [map_smul]

/- English proof (translation)
Introduce `a b h`. Apply `Subtype.ext` to reduce the goal to its premises. Conclude with `Matrix.ext fun i j => congrFun h (i, j)`.
-/
theorem entries_injective : Function.Injective (entries p K n γ) := by
  intro a b h
  apply Subtype.ext
  exact Matrix.ext fun i j => congrFun h (i, j)

/- English proof (translation)
Establish `e : ∀ z : (ι → K) ⊗[ℚ_[p]] Qr p r, ∀ i, TensorProduct.piRight ℚ_[p] ℚ_[p] (Qr p r) (fun _ : ι => K) (TensorProduct.comm _ _ _ z) i = TensorProduct.comm _ _ _ ((LinearMap.proj i : (ι → K) →ₗ[ℚ_[p]] K).rTensor (Qr p r) z)`. Introduce `z i`. Proceed by induction on `z using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `tmul a q => simp`.

Consider the case `add a b ha hb => simp only [map_add, Pi.add_apply, ha, hb]`. Establish `h0 : TensorProduct.piRight ℚ_[p] ℚ_[p] (Qr p r) (fun _ : ι => K) (TensorProduct.comm _ _ _ y) = 0`. Use function extensionality and compare the values at `i`. Rewrite using `[e, h i, map_zero]`. Both sides reduce to the same expression.

Conclude with `(LinearEquiv.map_eq_zero_iff _).1 ((LinearEquiv.map_eq_zero_iff _).1 h0)`.
-/
theorem eq_zero_of_proj {ι : Type} [Fintype ι] [DecidableEq ι] (y : (ι → K) ⊗[ℚ_[p]] Qr p r)
    (h : ∀ i, (LinearMap.proj i : (ι → K) →ₗ[ℚ_[p]] K).rTensor (Qr p r) y = 0) : y = 0 := by
  have e : ∀ z : (ι → K) ⊗[ℚ_[p]] Qr p r, ∀ i,
      TensorProduct.piRight ℚ_[p] ℚ_[p] (Qr p r) (fun _ : ι => K) (TensorProduct.comm _ _ _ z) i =
        TensorProduct.comm _ _ _ ((LinearMap.proj i : (ι → K) →ₗ[ℚ_[p]] K).rTensor (Qr p r) z) := by
    intro z i
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul a q => simp
    | add a b ha hb => simp only [map_add, Pi.add_apply, ha, hb]
  have h0 : TensorProduct.piRight ℚ_[p] ℚ_[p] (Qr p r) (fun _ : ι => K) (TensorProduct.comm _ _ _ y) = 0 := by
    funext i
    rw [e, h i, map_zero]
    rfl
  exact (LinearEquiv.map_eq_zero_iff _).1 ((LinearEquiv.map_eq_zero_iff _).1 h0)

/- English proof (translation)
Proceed by induction on `x using TensorProduct.induction_on with`. Consider the case `zero => rw [map_zero, map_zero]`. Both sides reduce to the same expression. Consider the case `tmul b q`. Rewrite using `[phi_tmul, Matrix.algebraMap_eq_diagonal, Matrix.mul_diagonal]`.

Simplify using `only [Matrix.map_apply, Pi.algebraMap_apply, LinearMap.rTensor_tmul, LinearMap.coe_comp, Function.comp_apply, LinearMap.coe_proj, Function.eval]`. Use `show (inclK p K r (val p K n γ b j k)) * (inclQ p K r q) = _`. Use `show ((val p K n γ b j k) ⊗ₜ[ℚ_[p]] (1 : Qr p r) : K ⊗[ℚ_[p]] Qr p r) * ((1 : K) ⊗ₜ[ℚ_[p]] q) = _`. Rewrite using `[Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]`. Both sides reduce to the same expression.

Consider the case `add a b ha hb => rw [map_add, Matrix.add_apply, ha, hb, map_add]`. Both sides reduce to the same expression.
-/
theorem phi_apply_entry (x : PolyAlg p K n γ ⊗[ℚ_[p]] Qr p r) (j k : Fin n) :
    phi p K n γ r x j k =
      (LinearMap.proj (j, k) ∘ₗ entries p K n γ).rTensor (Qr p r) x := by
  induction x using TensorProduct.induction_on with
  | zero => rw [map_zero, map_zero]; rfl
  | tmul b q =>
    rw [phi_tmul, Matrix.algebraMap_eq_diagonal, Matrix.mul_diagonal]
    simp only [Matrix.map_apply, Pi.algebraMap_apply, LinearMap.rTensor_tmul, LinearMap.coe_comp,
      Function.comp_apply, LinearMap.coe_proj, Function.eval]
    show (inclK p K r (val p K n γ b j k)) * (inclQ p K r q) = _
    show ((val p K n γ b j k) ⊗ₜ[ℚ_[p]] (1 : Qr p r) : K ⊗[ℚ_[p]] Qr p r) * ((1 : K) ⊗ₜ[ℚ_[p]] q) = _
    rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
    rfl
  | add a b ha hb => rw [map_add, Matrix.add_apply, ha, hb, map_add]; rfl

/- English proof (translation)
Rewrite using `[injective_iff_map_eq_zero]`. Introduce `x hx`. Establish `hinj : Function.Injective ((entries p K n γ).rTensor (Qr p r))` using `Module.Flat.rTensor_preserves_injective_linearMap _ (entries_injective p K n γ)`. Apply `hinj` to reduce the goal to its premises. Rewrite using `[map_zero]`.

Apply `eq_zero_of_proj` to reduce the goal to its premises. Introduce `ij`. Rewrite using `[← LinearMap.rTensor_comp_apply, ← phi_apply_entry, hx]`. Both sides reduce to the same expression.
-/
theorem phi_injective_any : Function.Injective (phi p K n γ r) := by
  rw [injective_iff_map_eq_zero]
  intro x hx
  have hinj : Function.Injective ((entries p K n γ).rTensor (Qr p r)) :=
    Module.Flat.rTensor_preserves_injective_linearMap _ (entries_injective p K n γ)
  apply hinj
  rw [map_zero]
  apply eq_zero_of_proj
  intro ij
  rw [← LinearMap.rTensor_comp_apply, ← phi_apply_entry, hx]
  rfl

/- English proof (translation)
Introduce `p _ K n r γ _` and use `phi_injective_any p K n γ r`.
-/
theorem phi_injective : ∀ (p : ℕ) [Fact p.Prime] (K : IntermediateField ℚ_[p] (PadicAlgCl p)) (n r : ℕ)
    (γ : Matrix (Fin n) (Fin n) K), 0 < r → Function.Injective (GlobalTheory.PolyTensor.phi p K n γ r) :=
  fun p _ K n r γ _ => phi_injective_any p K n γ r

end GlobalTheory.PolyTensor

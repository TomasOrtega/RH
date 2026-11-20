import Mathlib
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.RealDescent.RealLeviDescent.HighestVectorsRegularLine
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WtRInjective

noncomputable section

open Matrix Finset
open scoped InnerProductSpace ComplexConjugate

namespace GlobalTheory.CompanionTheory.RealCountG.LefDual

open PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD GlobalTheory.CompanionTheory.RealCount GlobalTheory.CompanionTheory.RealCountG

variable {n : ℕ}

/- English proof (translation)
Set `e : Module.Dual ℂ E.V ≃ₗ[ℂ] (E.V →L[ℂ] ℂ)` to `LinearMap.toContinuousLinearMap`. Establish `h : (dualT E S : (E.V →L[ℂ] ℂ) →ₗ[ℂ] (E.V →L[ℂ] ℂ)) = e.conj (Module.Dual.transpose (R` using `ℂ) (S : E.V →ₗ[ℂ] E.V)) := by`. Use extensionality with `φ x`. Simplify using `[e, dualT, LinearEquiv.conj_apply, Module.Dual.transpose_apply]`. Rewrite using `[h, LinearMap.trace_conj', LinearMap.trace_transpose']`.
-/
theorem trace_dualT (E : KMod n) (S : E.V →L[ℂ] E.V) :
    LinearMap.trace ℂ (E.V →L[ℂ] ℂ) (dualT E S : (E.V →L[ℂ] ℂ) →ₗ[ℂ] (E.V →L[ℂ] ℂ)) =
      LinearMap.trace ℂ E.V (S : E.V →ₗ[ℂ] E.V) := by
  let e : Module.Dual ℂ E.V ≃ₗ[ℂ] (E.V →L[ℂ] ℂ) := LinearMap.toContinuousLinearMap
  have h : (dualT E S : (E.V →L[ℂ] ℂ) →ₗ[ℂ] (E.V →L[ℂ] ℂ)) =
      e.conj (Module.Dual.transpose (R := ℂ) (S : E.V →ₗ[ℂ] E.V)) := by
    ext φ x
    simp [e, dualT, LinearEquiv.conj_apply, Module.Dual.transpose_apply]
  rw [h, LinearMap.trace_conj', LinearMap.trace_transpose']

/- English proof (translation)
Unfold `weylChar`. Rewrite using `[map_div₀, RingHom.map_det, RingHom.map_det]`. Apply the tactic sequence `congr 2 <;> ext i j <;> simp [map_zpow₀]`.
-/
theorem weylChar_conj_arg (lam : Fin n → ℤ) (u : Fin n → ℂ) :
    weylChar lam (fun a => conj (u a)) = conj (weylChar lam u) := by
  unfold weylChar
  rw [map_div₀, RingHom.map_det, RingHom.map_det]
  congr 2 <;> ext i j <;> simp [map_zpow₀]

/- English proof (translation)
Establish `h` using `Matrix.mem_unitaryGroup_iff'.1 k.2`. Rewrite `h` using `[hk, Matrix.star_eq_conjTranspose, Matrix.diagonal_conjTranspose, Matrix.diagonal_mul_diagonal]`. Establish `ha` using `congrFun (congrFun h a) a`. Rewrite `ha` using `[Matrix.diagonal_apply_eq, Matrix.one_apply_eq, Pi.star_apply]`. Establish `h1 : conj (z a) * z a = 1` using `ha`.

Establish `h0 : z a ≠ 0` using `fun h0 => by rw [h0, mul_zero] at h1; exact zero_ne_one h1`. Conclude with `⟨h0, eq_inv_of_mul_eq_one_left h1⟩`.
-/
theorem conj_eq_inv (k : Matrix.unitaryGroup (Fin n) ℂ) (z : Fin n → ℂ) (hk : k.1 = diagonal z) (a : Fin n) :
    z a ≠ 0 ∧ conj (z a) = (z a)⁻¹ := by
  have h := Matrix.mem_unitaryGroup_iff'.1 k.2
  rw [hk, Matrix.star_eq_conjTranspose, Matrix.diagonal_conjTranspose,
    Matrix.diagonal_mul_diagonal] at h
  have ha := congrFun (congrFun h a) a
  rw [Matrix.diagonal_apply_eq, Matrix.one_apply_eq, Pi.star_apply] at ha
  have h1 : conj (z a) * z a = 1 := ha
  have h0 : z a ≠ 0 := fun h0 => by rw [h0, mul_zero] at h1; exact zero_ne_one h1
  exact ⟨h0, eq_inv_of_mul_eq_one_left h1⟩

/- English proof (translation)
Establish `hz` using `conj_eq_inv k z hk`. Establish `hk' : (k⁻¹ : Matrix.unitaryGroup (Fin n) ℂ).1 = diagonal (fun a => (z a)⁻¹)`. Rewrite using `[← Unitary.star_eq_inv, Unitary.coe_star, hk, Matrix.star_eq_conjTranspose, Matrix.diagonal_conjTranspose]`. Use `congr 1`. Use function extensionality and compare the values at `a`.

Conclude with `(hz a).2`. Establish `hinj' : Function.Injective (fun a => (z a)⁻¹ ^ 2)` using `fun a b h => by`. Apply `hinj` to reduce the goal to its premises. Simplify `h` using `[inv_pow]`. Take `⟨-, -, h3⟩` from `hT`.

Take `⟨-, h2⟩` from `h3 k⁻¹ (fun a => (z a)⁻¹) hk' hinj'`. Use `beta_reduce at h2`. Rewrite using `[trace_dualT, h2]`. Establish `hw : (fun a => (z a)⁻¹ ^ 2) = fun a => conj (z a ^ 2)`. Use function extensionality and compare the values at `a`.

Rewrite using `[map_pow, (hz a).2]`. Use `congr 1`. Repeatedly rewrite using `[inv_div_inv]`. Conclude with `Finset.prod_comm`. Rewrite using `[hw, weylChar_conj_arg, Complex.conj_conj]`.
-/
theorem trace_dualT_inv (lam : Fin n → ℤ) (E : KMod n) (T : E.V →L[ℂ] E.V) (hT : IsLefK lam E T)
    (k : Matrix.unitaryGroup (Fin n) ℂ) (z : Fin n → ℂ) (hk : k.1 = diagonal z)
    (hinj : Function.Injective (fun a => z a ^ 2)) :
    LinearMap.trace ℂ (E.V →L[ℂ] ℂ) (dualT E (E.ρ k⁻¹ * T) : (E.V →L[ℂ] ℂ) →ₗ[ℂ] (E.V →L[ℂ] ℂ)) =
      (∏ a, ∏ b, (1 + z a / z b)) * weylChar lam (fun a => z a ^ 2) := by
  have hz := conj_eq_inv k z hk
  have hk' : (k⁻¹ : Matrix.unitaryGroup (Fin n) ℂ).1 = diagonal (fun a => (z a)⁻¹) := by
    rw [← Unitary.star_eq_inv, Unitary.coe_star, hk, Matrix.star_eq_conjTranspose,
      Matrix.diagonal_conjTranspose]
    congr 1
    funext a
    exact (hz a).2
  have hinj' : Function.Injective (fun a => (z a)⁻¹ ^ 2) := fun a b h => by
    apply hinj
    simpa [inv_pow] using h
  obtain ⟨-, -, h3⟩ := hT
  obtain ⟨-, h2⟩ := h3 k⁻¹ (fun a => (z a)⁻¹) hk' hinj'
  beta_reduce at h2
  rw [trace_dualT, h2]
  have hw : (fun a => (z a)⁻¹ ^ 2) = fun a => conj (z a ^ 2) := by
    funext a
    rw [map_pow, (hz a).2]
  congr 1
  · simp_rw [inv_div_inv]
    exact Finset.prod_comm
  · rw [hw, weylChar_conj_arg, Complex.conj_conj]

end GlobalTheory.CompanionTheory.RealCountG.LefDual

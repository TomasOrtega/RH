import Mathlib

namespace GlobalTheory.AlternatingLinearCombination

/- English proof (translation)
Rewrite using `[← sub_eq_zero, ← Module.forall_dual_apply_eq_zero_iff L]`. Introduce `φ`. Set `ψ : (Fin n → L) →ₗ[L] M` to `Fintype.linearCombination L g`. Set `F : (Fin n → L) [⋀^Fin n]→ₗ[L] L` to `(φ.compAlternatingMap f).compLinearMap ψ`. Establish `h` using `F.eq_smul_basis_det (Pi.basisFun L (Fin n))`.

Establish `h1 : F a = φ (f fun i => ∑ l : Fin n, a i l • g l)`. Simplify using `[F, ψ, Fintype.linearCombination_apply]`. Establish `h2 : F (Pi.basisFun L (Fin n)) = φ (f g)`. Establish `: (fun i => ψ (Pi.basisFun L (Fin n) i)) = g`. Use function extensionality and compare the values at `i`.

Simplify using `[ψ]`. Express the relevant statement in the definitionally equal form `φ (f fun i => ψ (Pi.basisFun L (Fin n) i)) = _`. Rewrite using `[this]`. Establish `h3 : F a = φ (f g) * Matrix.det (Matrix.of a)`. Rewrite using `[h, AlternatingMap.smul_apply, h2, Pi.basisFun_det_apply, smul_eq_mul]`.

Rewrite using `[map_sub, map_smul, ← h1, h3, smul_eq_mul, mul_comm, sub_self]`.
-/
theorem alternating_map_linear_combination {L M N : Type} [Field L] [AddCommGroup M] [Module L M]
    [AddCommGroup N] [Module L N] {n : ℕ} (f : M [⋀^Fin n]→ₗ[L] N) (g : Fin n → M)
    (a : Fin n → Fin n → L) :
    (f fun i => ∑ l : Fin n, a i l • g l) = Matrix.det (Matrix.of a) • f g := by
  classical
  rw [← sub_eq_zero, ← Module.forall_dual_apply_eq_zero_iff L]
  intro φ
  let ψ : (Fin n → L) →ₗ[L] M := Fintype.linearCombination L g
  let F : (Fin n → L) [⋀^Fin n]→ₗ[L] L := (φ.compAlternatingMap f).compLinearMap ψ
  have h := F.eq_smul_basis_det (Pi.basisFun L (Fin n))
  have h1 : F a = φ (f fun i => ∑ l : Fin n, a i l • g l) := by
    simp [F, ψ, Fintype.linearCombination_apply]
  have h2 : F (Pi.basisFun L (Fin n)) = φ (f g) := by
    have : (fun i => ψ (Pi.basisFun L (Fin n) i)) = g := by
      funext i
      simp [ψ]
    change φ (f fun i => ψ (Pi.basisFun L (Fin n) i)) = _
    rw [this]
  have h3 : F a = φ (f g) * Matrix.det (Matrix.of a) := by
    rw [h, AlternatingMap.smul_apply, h2, Pi.basisFun_det_apply, smul_eq_mul]
  rw [map_sub, map_smul, ← h1, h3, smul_eq_mul, mul_comm, sub_self]

end GlobalTheory.AlternatingLinearCombination

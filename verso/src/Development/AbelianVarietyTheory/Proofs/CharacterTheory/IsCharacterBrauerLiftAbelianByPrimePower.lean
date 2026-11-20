import Mathlib
import Development.AbelianVarietyTheory.Definitions.CommutativeAlgebra.AbByPOfComm
import Development.AbelianVarietyTheory.Definitions.CommutativeAlgebra.InvariantSubspaceMobiusInverseRecEqOfFinrankLt
import Development.AbelianVarietyTheory.Proofs.CharacterTheory.ExistsMonomialBasisAbelianByPrimePowerStatement
import Development.AbelianVarietyTheory.Proofs.CharacterTheory.TraceLiftMonomialMatrixEqSumEigenvaluesStatement
open Polynomial GlobalTheory.CuspGL GlobalTheory.BI

namespace GlobalTheory.CuspGL

/- English proof (translation)
Establish `h1` using `congrArg (fun v => b.repr v i) h`. Simplify using `only [map_smul, Module.Basis.repr_self, Finsupp.smul_apply, Finsupp.single_eq_same, smul_eq_mul, mul_one, Finsupp.single_apply] at h1`. Distinguish the cases in `hij : j = i`. Substitute `hij` using the available equality. Simplify using `using h1`.

Simplify using `[hij, hx] at h1`.
-/
theorem basis_smul_eq_smul_cancel {k V ι : Type} [Field k] [AddCommGroup V] [Module k V]
    (b : Module.Basis ι k V) {x y : k} {i j : ι} (hx : x ≠ 0) (h : x • b i = y • b j) :
    i = j ∧ x = y := by
  classical
  have h1 := congrArg (fun v => b.repr v i) h
  simp only [map_smul, Module.Basis.repr_self, Finsupp.smul_apply, Finsupp.single_eq_same,
    smul_eq_mul, mul_one, Finsupp.single_apply] at h1
  by_cases hij : j = i
  · subst hij
    simpa using h1
  · simp [hij, hx] at h1

/- English proof (translation)
Introduce `k _ _ θ hθ G _ _ hG hc n ρ`. Set `R : Representation k G (Fin n → k)` to `((Matrix.toLinAlgEquiv' : Matrix (Fin n) (Fin n) k ≃ₐ[k] _).toMonoidHom.comp (Units.coeHom _)).comp ρ`. Establish `hR : ∀ g, R g = Matrix.toLin' (ρ g : Matrix (Fin n) (Fin n) k)` using `fun g => rfl`. Take `⟨m, b, hb⟩` from `GlobalTheory.T.exists_monomial_basis_abelianByPrimePower k G (Fin n → k) R hG hc`. Use `choose s c hsc using hb`.

Establish `hc0 : ∀ g i, c g i ≠ 0`. Introduce `g i h0`. Establish `h1 : R g (b i) = 0` using `by rw [hsc, h0, zero_smul]`. Establish `h2 : R (g⁻¹ * g) (b i) = 0`. Rewrite using `[map_mul, Module.End.mul_apply, h1, map_zero]`.

Rewrite `h2` using `[inv_mul_cancel, map_one, Module.End.one_apply]`. Conclude with `b.ne_zero i h2`. Establish `hmul : ∀ g h i, s (g * h) i = s g (s h i) ∧ c (g * h) i = c g (s h i) * c h i`. Introduce `g h i`. Apply `basis_smul_eq_smul_cancel b (hc0 _ _)` to reduce the goal to its premises.

Rewrite using `[← hsc, map_mul, Module.End.mul_apply, hsc, map_smul, hsc, smul_smul, mul_comm]`. Establish `hone : ∀ i, s 1 i = i ∧ c 1 i = 1`. Introduce `i`. Apply `basis_smul_eq_smul_cancel b (hc0 _ _)` to reduce the goal to its premises. Rewrite using `[← hsc, map_one, Module.End.one_apply, one_smul]`.

Set `σ : G → Equiv.Perm (Fin m)` to `fun g => { toFun := s g invFun := s g⁻¹ left_inv := fun i => by rw [← (hmul _ _ _).1, inv_mul_cancel, (hone i).1] right_inv := fun i => by rw [← (hmul _ _ _).1, mul_inv_cancel, (hone i).1] }`. Set `L : G →* Matrix (Fin m) (Fin m) ℂ` to `{ toFun := fun g => Matrix.of fun i j => if i = σ g j then θ (c g j) else 0 map_one' := by`. Use extensionality with `i j`. Simplify using `[σ, (hone j).1, (hone j).2, Matrix.one_apply]`. Use the proof step `map_mul' := by`.

Introduce `g h`. Use extensionality with `i j`. Simplify using `[σ, Matrix.mul_apply, (hmul g h j).1, (hmul g h j).2] }`. Establish `hM : ∀ g, (Matrix.of fun i j => if i = σ g j then c g j else 0 : Matrix (Fin m) (Fin m) k) = LinearMap.toMatrix b b (R g)`. Introduce `g`.

Use extensionality with `i j`. Simplify using `[σ, LinearMap.toMatrix_apply, hsc, Finsupp.single_apply, eq_comm]`. Use `⟨m, (Matrix.toLinAlgEquiv' : Matrix (Fin m) (Fin m) ℂ ≃ₐ[ℂ] _).toMonoidHom.comp L, fun g => ?_⟩` and prove the remaining obligations. Establish `h1 : (Matrix.of fun i j => if i = σ g j then c g j else 0 : Matrix (Fin m) (Fin m) k) ^ Nat.card G = 1`. Rewrite using `[hM, LinearMap.toMatrix_pow, ← map_pow, pow_card_eq_one', map_one, LinearMap.toMatrix_one]`.

Establish `h2 : L g ^ Nat.card G = 1` using `by rw [← map_pow, pow_card_eq_one', map_one]`. Establish `h3` using `GlobalTheory.T.trace_lift_monomialMatrix_eq_sum_eigenvalues k θ hθ m (Nat.card G) (σ g) (c g) (hc0 g) hc h1 h2`. Rewrite `h3` using `[hM, LinearMap.charpoly_toMatrix, hR, Matrix.charpoly_toLin']`. Use `show _ = LinearMap.trace ℂ _ (Matrix.toLin' (L g))`. Rewrite using `[Matrix.trace_toLin'_eq]`.

Conclude with `h3.symm`.
-/
theorem isChar_brauerLift : ∀ (k : Type) [Field k] [IsAlgClosed k] (θ : k →* ℂ), (∀ x y : k, x ≠ 0 → y ≠ 0 → θ x = θ y → x = y) → ∀ (G : Type) [Group G] [Finite G], AbByP G → (Nat.card G : k) ≠ 0 → ∀ (n : ℕ) (ρ : G →* GL (Fin n) k), IsChar ℂ ℂ (fun g => ((Matrix.charpoly (ρ g : Matrix (Fin n) (Fin n) k)).roots.map θ).sum) := by
  intro k _ _ θ hθ G _ _ hG hc n ρ
  classical
  let R : Representation k G (Fin n → k) :=
    ((Matrix.toLinAlgEquiv' : Matrix (Fin n) (Fin n) k ≃ₐ[k] _).toMonoidHom.comp
      (Units.coeHom _)).comp ρ
  have hR : ∀ g, R g = Matrix.toLin' (ρ g : Matrix (Fin n) (Fin n) k) := fun g => rfl
  obtain ⟨m, b, hb⟩ := GlobalTheory.T.exists_monomial_basis_abelianByPrimePower k G (Fin n → k) R hG hc
  choose s c hsc using hb
  have hc0 : ∀ g i, c g i ≠ 0 := by
    intro g i h0
    have h1 : R g (b i) = 0 := by rw [hsc, h0, zero_smul]
    have h2 : R (g⁻¹ * g) (b i) = 0 := by
      rw [map_mul, Module.End.mul_apply, h1, map_zero]
    rw [inv_mul_cancel, map_one, Module.End.one_apply] at h2
    exact b.ne_zero i h2
  have hmul : ∀ g h i, s (g * h) i = s g (s h i) ∧ c (g * h) i = c g (s h i) * c h i := by
    intro g h i
    apply basis_smul_eq_smul_cancel b (hc0 _ _)
    rw [← hsc, map_mul, Module.End.mul_apply, hsc, map_smul, hsc, smul_smul, mul_comm]
  have hone : ∀ i, s 1 i = i ∧ c 1 i = 1 := by
    intro i
    apply basis_smul_eq_smul_cancel b (hc0 _ _)
    rw [← hsc, map_one, Module.End.one_apply, one_smul]
  let σ : G → Equiv.Perm (Fin m) := fun g =>
    { toFun := s g
      invFun := s g⁻¹
      left_inv := fun i => by rw [← (hmul _ _ _).1, inv_mul_cancel, (hone i).1]
      right_inv := fun i => by rw [← (hmul _ _ _).1, mul_inv_cancel, (hone i).1] }
  let L : G →* Matrix (Fin m) (Fin m) ℂ :=
    { toFun := fun g => Matrix.of fun i j => if i = σ g j then θ (c g j) else 0
      map_one' := by
        ext i j
        simp [σ, (hone j).1, (hone j).2, Matrix.one_apply]
      map_mul' := by
        intro g h
        ext i j
        simp [σ, Matrix.mul_apply, (hmul g h j).1, (hmul g h j).2] }
  have hM : ∀ g, (Matrix.of fun i j => if i = σ g j then c g j else 0 : Matrix (Fin m) (Fin m) k)
      = LinearMap.toMatrix b b (R g) := by
    intro g
    ext i j
    simp [σ, LinearMap.toMatrix_apply, hsc, Finsupp.single_apply, eq_comm]
  refine ⟨m, (Matrix.toLinAlgEquiv' : Matrix (Fin m) (Fin m) ℂ ≃ₐ[ℂ] _).toMonoidHom.comp L, fun g => ?_⟩
  have h1 : (Matrix.of fun i j => if i = σ g j then c g j else 0 : Matrix (Fin m) (Fin m) k)
      ^ Nat.card G = 1 := by
    rw [hM, LinearMap.toMatrix_pow, ← map_pow, pow_card_eq_one', map_one, LinearMap.toMatrix_one]
  have h2 : L g ^ Nat.card G = 1 := by rw [← map_pow, pow_card_eq_one', map_one]
  have h3 := GlobalTheory.T.trace_lift_monomialMatrix_eq_sum_eigenvalues k θ hθ m (Nat.card G) (σ g) (c g) (hc0 g) hc h1 h2
  rw [hM, LinearMap.charpoly_toMatrix, hR, Matrix.charpoly_toLin'] at h3
  show _ = LinearMap.trace ℂ _ (Matrix.toLin' (L g))
  rw [Matrix.trace_toLin'_eq]
  exact h3.symm

end GlobalTheory.CuspGL

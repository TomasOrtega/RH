import Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.DualModuleCocycles.RepRSingle
import Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.DualModuleCocycles.StarFacts
open Matrix IsLocalRing UpperTheory.V UpperTheory.V.W UpperTheory.V.Alg UpperTheory.V.Pa UpperTheory.V.Th UpperTheory.V.Th.Coc

/- English proof (translation)
Introduce `l _ F O R X _ _ _ _ _ n _ x δ ρ P τ c d z hδ hF hL hst hz`. Establish `bmul : ∀ A B : Matrix (Fin n) (Fin n) O, bar X (A * B) = bar X A * bar X B` using `fun A B => Matrix.map_mul`. Establish `bone : bar X (1 : Matrix (Fin n) (Fin n) O) = 1` using `Matrix.map_one _ (map_zero _) (map_one _)`. Establish `bsm : ∀ (e : O) (A : Matrix (Fin n) (Fin n) O), bar X (e • A) = e • bar X A`. Introduce `e A`.

Use extensionality with `i j`. Use `show algebraMap O X (e * A i j) = e • algebraMap O X (A i j)`. Rewrite using `[map_mul, Algebra.smul_def]`. Establish `rmul : ∀ g g', bar X (mat ρ (g * g')) = bar X (mat ρ g) * bar X (mat ρ g')`. Introduce `g g'`.

Rewrite using `[map_mul, bmul]`. Establish `rinv : ∀ g, bar X (mat ρ g⁻¹) * bar X (mat ρ g) = 1`. Introduce `g`. Rewrite using `[← rmul, inv_mul_cancel, map_one, bone]`. Establish `rinv' : ∀ g, bar X (mat ρ g) * bar X (mat ρ g⁻¹) = 1`.

Introduce `g`. Rewrite using `[← rmul, mul_inv_cancel, map_one, bone]`. Establish `d1 : d 1 = 0`. Establish `h` using `hL.mul 1 1`. Rewrite `h` using `[mul_one, map_one (repR x (mat ρ)), bone, mul_one, one_mul]`.

Conclude with `left_eq_add.mp h`. Establish `δ1 : δ 1 = 0`. Establish `h` using `hδ 1 1`. Rewrite `h` using `[mul_one, map_one x, one_smul]`. Conclude with `left_eq_add.mp h`.

Establish `δa : ∀ e : O, δ (algebraMap O R e) = 0`. Introduce `e`. Rewrite using `[Algebra.algebraMap_eq_smul_one, map_smul, δ1, smul_zero]`. Establish `dmul : ∀ g g', d (MonoidAlgebra.single (g * g') 1) = d (MonoidAlgebra.single g 1) * bar X (mat ρ g') + bar X (mat ρ g) * d (MonoidAlgebra.single g' 1)`. Introduce `g g'`.

Establish `h` using `hL.mul (MonoidAlgebra.single g 1) (MonoidAlgebra.single g' 1)`. Rewrite `h` using `[MonoidAlgebra.single_mul_single, mul_one, repR_single, repR_single, map_one, one_smul, one_smul]`. Conclude with `h`. Establish `hd : ∀ g, d (MonoidAlgebra.single g 1) = z g * bar X (mat ρ g)`. Introduce `g`.

Rewrite using `[hz, mul_assoc, rinv, mul_one]`. Establish `dinv : ∀ g, d (MonoidAlgebra.single g⁻¹ 1) = -(bar X (mat ρ g⁻¹) * z g)`. Introduce `g`. Establish `h` using `dmul g⁻¹ g`. Rewrite `h` using `[inv_mul_cancel, ← MonoidAlgebra.one_def, d1]`.

Establish `h2` using `congrArg (· * bar X (mat ρ g⁻¹)) h`. Simplify using `only [zero_mul, add_mul, mul_assoc, rinv', mul_one] at h2`. Rewrite using `[hz]`. Conclude with `eq_neg_of_add_eq_zero_left h2.symm`. Use `⟨d1, ?_, ?_, ?_⟩` and prove the remaining obligations.

Introduce `g g'`. Rewrite using `[hz (g * g'), dmul, _root_.mul_inv_rev, rmul, hz g, hz g', add_mul]`. Simplify using `only [mul_assoc]`. Rewrite using `[← mul_assoc (bar X (mat ρ g')), rinv', one_mul]`. Introduce `g`.

Establish `h` using `hst (MonoidAlgebra.single g 1)`. Rewrite `h` using `[(starFacts F (O := O) (R := R) (n := n)).2.2.2.2.1 g]`. Establish `hf` using `congrArg (bar X) (hF g)`. Generalize the expression as in `((F.eps O O g ^ (1 - (n : ℤ)) : Oˣ) : O) = e at h hf`. Establish `hs : (MonoidAlgebra.single (F.conj g)⁻¹ (algebraMap O R e) : MonoidAlgebra R F.G₀) = algebraMap O R e • MonoidAlgebra.single (F.conj g)⁻¹ 1`.

Rewrite using `[MonoidAlgebra.smul_single, smul_eq_mul, mul_one]`. Rewrite `h` using `[hs, hL.smul, δa, smul_zero, zero_smul, add_zero, AlgHom.commutes, dinv, hd, transpose_mul]`. Rewrite `hf` using `[bmul, bmul, bsm]`. Establish `ht : bar X (mat ρ g)ᵀ = (bar X (mat ρ g))ᵀ` using `rfl`. Rewrite `hf` using `[ht]`.

Establish `hf2 : (bar X (mat ρ g))ᵀ * bar X (P : Matrix (Fin n) (Fin n) O) = e • (bar X (P : Matrix (Fin n) (Fin n) O) * bar X (mat ρ (F.conj g)⁻¹))`. Rewrite using `[← smul_mul_assoc, ← hf, mul_assoc, rinv', mul_one]`. Establish `h3 : (bar X (mat ρ g))ᵀ * (bar X (P : Matrix (Fin n) (Fin n) O) * z (F.conj g)) = (bar X (mat ρ g))ᵀ * -((z g)ᵀ * bar X (P : Matrix (Fin n) (Fin n) O))`. Rewrite using `[mul_neg, ← mul_assoc, ← mul_assoc, ← h, hf2]`. Simplify using `[mul_assoc]`.

Establish `h4 : (bar X (mat ρ g⁻¹))ᵀ * (bar X (mat ρ g))ᵀ = 1`. Rewrite using `[← transpose_mul, rinv', transpose_one]`. Establish `h5` using `congrArg ((bar X (mat ρ g⁻¹))ᵀ * ·) h3`. Simplify using `only [← mul_assoc _ (bar X (mat ρ g))ᵀ, h4, one_mul] at h5`. Conclude with `h5`.

Introduce `g`. Rewrite using `[← hd, hL.tr]`.
-/
theorem UpperTheory.V.Th.Coc.zOf :
    ∀ {l : ℕ} [Fact l.Prime] (F : GFrame l) {O R X : Type} [CommRing O] [CommRing R] [Algebra O R] [CommRing X] [Algebra O X] {n : ℕ} [Algebra ℤ_[l] O] (x : R →ₐ[O] O) (δ : R →ₗ[O] X) (ρ : F.G₀ →* GL (Fin n) O) (P : GL (Fin n) O) (τ : MonoidAlgebra R F.G₀ → R) (c : O) (d : MonoidAlgebra R F.G₀ →+ Matrix (Fin n) (Fin n) X) (z : F.G₀ → Matrix (Fin n) (Fin n) X), IsDer x δ → F.IsForm O n ρ P → IsLift x δ (repR x (mat ρ)) τ c d → (∀ a, bar X (P : Matrix (Fin n) (Fin n) O) * d (F.star O R n a) = (d a)ᵀ * bar X (P : Matrix (Fin n) (Fin n) O)) → (∀ g, z g = d (MonoidAlgebra.single g 1) * bar X (mat ρ g⁻¹)) → d 1 = 0 ∧ (∀ g g', z (g * g') = z g + bar X (mat ρ g) * z g' * bar X (mat ρ g⁻¹)) ∧ (∀ g, bar X (P : Matrix (Fin n) (Fin n) O) * z (F.conj g) = -((z g)ᵀ * bar X (P : Matrix (Fin n) (Fin n) O))) ∧ ∀ g, (z g * bar X (mat ρ g)).trace = c • δ (τ (MonoidAlgebra.single g 1)) := by
  intro l _ F O R X _ _ _ _ _ n _ x δ ρ P τ c d z hδ hF hL hst hz
  have bmul : ∀ A B : Matrix (Fin n) (Fin n) O, bar X (A * B) = bar X A * bar X B := fun A B => Matrix.map_mul
  have bone : bar X (1 : Matrix (Fin n) (Fin n) O) = 1 := Matrix.map_one _ (map_zero _) (map_one _)
  have bsm : ∀ (e : O) (A : Matrix (Fin n) (Fin n) O), bar X (e • A) = e • bar X A := by
    intro e A
    ext i j
    show algebraMap O X (e * A i j) = e • algebraMap O X (A i j)
    rw [map_mul, Algebra.smul_def]
  have rmul : ∀ g g', bar X (mat ρ (g * g')) = bar X (mat ρ g) * bar X (mat ρ g') := by
    intro g g'
    rw [map_mul, bmul]
  have rinv : ∀ g, bar X (mat ρ g⁻¹) * bar X (mat ρ g) = 1 := by
    intro g
    rw [← rmul, inv_mul_cancel, map_one, bone]
  have rinv' : ∀ g, bar X (mat ρ g) * bar X (mat ρ g⁻¹) = 1 := by
    intro g
    rw [← rmul, mul_inv_cancel, map_one, bone]
  have d1 : d 1 = 0 := by
    have h := hL.mul 1 1
    rw [mul_one, map_one (repR x (mat ρ)), bone, mul_one, one_mul] at h
    exact left_eq_add.mp h
  have δ1 : δ 1 = 0 := by
    have h := hδ 1 1
    rw [mul_one, map_one x, one_smul] at h
    exact left_eq_add.mp h
  have δa : ∀ e : O, δ (algebraMap O R e) = 0 := by
    intro e
    rw [Algebra.algebraMap_eq_smul_one, map_smul, δ1, smul_zero]
  have dmul : ∀ g g', d (MonoidAlgebra.single (g * g') 1) =
      d (MonoidAlgebra.single g 1) * bar X (mat ρ g') + bar X (mat ρ g) * d (MonoidAlgebra.single g' 1) := by
    intro g g'
    have h := hL.mul (MonoidAlgebra.single g 1) (MonoidAlgebra.single g' 1)
    rw [MonoidAlgebra.single_mul_single, mul_one, repR_single, repR_single, map_one, one_smul, one_smul] at h
    exact h
  have hd : ∀ g, d (MonoidAlgebra.single g 1) = z g * bar X (mat ρ g) := by
    intro g
    rw [hz, mul_assoc, rinv, mul_one]
  have dinv : ∀ g, d (MonoidAlgebra.single g⁻¹ 1) = -(bar X (mat ρ g⁻¹) * z g) := by
    intro g
    have h := dmul g⁻¹ g
    rw [inv_mul_cancel, ← MonoidAlgebra.one_def, d1] at h
    have h2 := congrArg (· * bar X (mat ρ g⁻¹)) h
    simp only [zero_mul, add_mul, mul_assoc, rinv', mul_one] at h2
    rw [hz]
    exact eq_neg_of_add_eq_zero_left h2.symm
  refine ⟨d1, ?_, ?_, ?_⟩
  · intro g g'
    rw [hz (g * g'), dmul, _root_.mul_inv_rev, rmul, hz g, hz g', add_mul]
    simp only [mul_assoc]
    rw [← mul_assoc (bar X (mat ρ g')), rinv', one_mul]
  · intro g
    have h := hst (MonoidAlgebra.single g 1)
    rw [(starFacts F (O := O) (R := R) (n := n)).2.2.2.2.1 g] at h
    have hf := congrArg (bar X) (hF g)
    generalize ((F.eps O O g ^ (1 - (n : ℤ)) : Oˣ) : O) = e at h hf
    have hs : (MonoidAlgebra.single (F.conj g)⁻¹ (algebraMap O R e) : MonoidAlgebra R F.G₀) =
        algebraMap O R e • MonoidAlgebra.single (F.conj g)⁻¹ 1 := by
      rw [MonoidAlgebra.smul_single, smul_eq_mul, mul_one]
    rw [hs, hL.smul, δa, smul_zero, zero_smul, add_zero, AlgHom.commutes, dinv, hd, transpose_mul] at h
    rw [bmul, bmul, bsm] at hf
    have ht : bar X (mat ρ g)ᵀ = (bar X (mat ρ g))ᵀ := rfl
    rw [ht] at hf
    have hf2 : (bar X (mat ρ g))ᵀ * bar X (P : Matrix (Fin n) (Fin n) O) =
        e • (bar X (P : Matrix (Fin n) (Fin n) O) * bar X (mat ρ (F.conj g)⁻¹)) := by
      rw [← smul_mul_assoc, ← hf, mul_assoc, rinv', mul_one]
    have h3 : (bar X (mat ρ g))ᵀ * (bar X (P : Matrix (Fin n) (Fin n) O) * z (F.conj g)) =
        (bar X (mat ρ g))ᵀ * -((z g)ᵀ * bar X (P : Matrix (Fin n) (Fin n) O)) := by
      rw [mul_neg, ← mul_assoc, ← mul_assoc, ← h, hf2]
      simp [mul_assoc]
    have h4 : (bar X (mat ρ g⁻¹))ᵀ * (bar X (mat ρ g))ᵀ = 1 := by
      rw [← transpose_mul, rinv', transpose_one]
    have h5 := congrArg ((bar X (mat ρ g⁻¹))ᵀ * ·) h3
    simp only [← mul_assoc _ (bar X (mat ρ g))ᵀ, h4, one_mul] at h5
    exact h5
  · intro g
    rw [← hd, hL.tr]

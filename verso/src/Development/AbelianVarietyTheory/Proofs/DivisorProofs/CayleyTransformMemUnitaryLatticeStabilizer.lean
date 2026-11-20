import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFinMapsOfForall
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneMemKAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FromBlocksMem
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.KFinLoc
open scoped TensorProduct Matrix

namespace GlobalTheory.CayleyStab

/- English proof (translation)
Introduce `F E _ _ _ _ _ σ d W v Y hY hYL hskew ⟨Np, hP1, hP2, hPL⟩ ⟨Nm, hM1, hM2, hML⟩`. Use `set J := incM F W.J with hJ`. Establish `hmap : ∀ A B : Matrix (Fin d) (Fin d) (AE F E), (A * B).map (cA σ) = A.map (cA σ) * B.map (cA σ)` using `fun A B => Matrix.map_mul (f := (cA σ).toRingHom)`. Establish `hmap1 : (1 : Matrix (Fin d) (Fin d) (AE F E)).map (cA σ) = 1` using `Matrix.map_one _ (map_zero (cA σ)) (map_one (cA σ))`. Establish `hGP : (1 - Y) * Np * (1 + Y) = 1 - Y` using `by rw [Matrix.mul_assoc, hP2, Matrix.mul_one]`.

Establish `h1 : (1 - Y) * Np * ((1 + Y) * Nm) = 1`. Rewrite using `[← Matrix.mul_assoc, hGP, hM1]`. Establish `h2 : (1 + Y) * Nm * ((1 - Y) * Np) = 1`. Rewrite using `[← Matrix.mul_assoc, Matrix.mul_assoc (1 + Y), hM2, Matrix.mul_one, hP1]`. Establish `hQP : (1 - Y)ᵀ * J * (1 - Y).map (cA σ) = (1 + Y)ᵀ * J * (1 + Y).map (cA σ)`.

Rewrite using `[Matrix.map_sub _ (map_sub (cA σ)), Matrix.map_add _ (map_add (cA σ)), hmap1, Matrix.transpose_sub, Matrix.transpose_add, Matrix.transpose_one]`. Establish `e : ∀ A B : Matrix (Fin d) (Fin d) (AE F E), (1 - A) * J * (1 - B) = (1 + A) * J * (1 + B) - 2 * (A * J + J * B)`. Introduce `A B`. Use `noncomm_ring`. Rewrite using `[e, hskew, mul_zero, sub_zero]`.

Establish `hU : ((1 - Y) * Np)ᵀ * J * ((1 - Y) * Np).map (cA σ) = J`. Establish `eT : Npᵀ * (1 + Y)ᵀ = 1` using `by rw [← Matrix.transpose_mul, hP1, Matrix.transpose_one]`. Establish `eM : (1 + Y).map (cA σ) * Np.map (cA σ) = 1` using `by rw [← hmap, hP1, hmap1]`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[eT, eM, Matrix.one_mul, Matrix.mul_one]`.

Use `_ = Npᵀ * (((1 - Y) * Np * (1 + Y))ᵀ * J * ((1 - Y) * Np * (1 + Y)).map (cA σ)) * Np.map (cA σ) := by`. Rewrite using `[hmap ((1 - Y) * Np), Matrix.transpose_mul ((1 - Y) * Np)]`. Simplify using `only [Matrix.mul_assoc]`. Use `_ = Npᵀ * ((1 + Y)ᵀ * J * (1 + Y).map (cA σ)) * Np.map (cA σ) := by rw [hGP, hQP]`. Use `_ = (Npᵀ * (1 + Y)ᵀ) * J * ((1 + Y).map (cA σ) * Np.map (cA σ)) := by simp only [Matrix.mul_assoc]`.

Use `_ = J := by rw [eT, eM, Matrix.one_mul, Matrix.mul_one]`. Set `g : GL (Fin d) (AE F E)` to `⟨(1 - Y) * Np, (1 + Y) * Nm, h1, h2⟩`. Establish `hg : g ∈ UG (cA σ) (incM F W.J)` using `hU`. Set `h : UA σ W.J` to `⟨g, hg⟩`. Establish `hmat : mat h = (1 - Y) * Np` using `rfl`.

Establish `hmatinv : mat h⁻¹ = (1 + Y) * Nm` using `rfl`. Use `⟨h, ⟨?_, ?_⟩, ?_⟩` and prove the remaining obligations. Introduce `u hu`. Establish `e : mat h - 1 = -(Y * Np) - Y * Np`. Rewrite using `[hmat]`.

Combine the equalities or inequalities in the displayed calculation. Establish `hYu : u • Y = 0` using `hY u hu`. Rewrite using `[e, smul_sub, smul_neg, ← Matrix.smul_mul, hYu, Matrix.zero_mul, neg_zero, sub_zero]`. Introduce `z hz`. Use `⟨?_, ?_⟩` and prove the remaining obligations.

Rewrite using `[hmat, ← Matrix.mulVec_mulVec, Matrix.sub_mulVec, Matrix.one_mulVec]`. Conclude with `sub_mem (hPL z hz) (hYL _ (hPL z hz))`. Rewrite using `[hmatinv, ← Matrix.mulVec_mulVec, Matrix.add_mulVec, Matrix.one_mulVec]`. Conclude with `add_mem (hML z hz) (hYL _ (hML z hz))`. Rewrite using `[hmat, hGP]`.
-/
theorem cayley_mem_KAt : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (d : ℕ)
    (W : Spc F E d) (v : Pl F) (Y : Matrix (Fin d) (Fin d) (AE F E)), At (evFin F v) Y →
    (∀ z ∈ GlobalTheory.InertSph.latAt W v, Y *ᵥ z ∈ GlobalTheory.InertSph.latAt W v) →
    Yᵀ * incM F W.J + incM F W.J * Y.map (cA σ) = 0 →
    (∃ M : Matrix (Fin d) (Fin d) (AE F E), (1 + Y) * M = 1 ∧ M * (1 + Y) = 1 ∧
      ∀ z ∈ GlobalTheory.InertSph.latAt W v, M *ᵥ z ∈ GlobalTheory.InertSph.latAt W v) →
    (∃ M : Matrix (Fin d) (Fin d) (AE F E), (1 - Y) * M = 1 ∧ M * (1 - Y) = 1 ∧
      ∀ z ∈ GlobalTheory.InertSph.latAt W v, M *ᵥ z ∈ GlobalTheory.InertSph.latAt W v) →
    ∃ h ∈ GlobalTheory.InertSph.KAt σ W v, mat h * (1 + Y) = 1 - Y := by
  intro F E _ _ _ _ _ σ d W v Y hY hYL hskew ⟨Np, hP1, hP2, hPL⟩ ⟨Nm, hM1, hM2, hML⟩
  set J := incM F W.J with hJ
  have hmap : ∀ A B : Matrix (Fin d) (Fin d) (AE F E), (A * B).map (cA σ) = A.map (cA σ) * B.map (cA σ) :=
    fun A B => Matrix.map_mul (f := (cA σ).toRingHom)
  have hmap1 : (1 : Matrix (Fin d) (Fin d) (AE F E)).map (cA σ) = 1 :=
    Matrix.map_one _ (map_zero (cA σ)) (map_one (cA σ))
  have hGP : (1 - Y) * Np * (1 + Y) = 1 - Y := by rw [Matrix.mul_assoc, hP2, Matrix.mul_one]
  have h1 : (1 - Y) * Np * ((1 + Y) * Nm) = 1 := by
    rw [← Matrix.mul_assoc, hGP, hM1]
  have h2 : (1 + Y) * Nm * ((1 - Y) * Np) = 1 := by
    rw [← Matrix.mul_assoc, Matrix.mul_assoc (1 + Y), hM2, Matrix.mul_one, hP1]

  have hQP : (1 - Y)ᵀ * J * (1 - Y).map (cA σ) = (1 + Y)ᵀ * J * (1 + Y).map (cA σ) := by
    rw [Matrix.map_sub _ (map_sub (cA σ)), Matrix.map_add _ (map_add (cA σ)), hmap1, Matrix.transpose_sub, Matrix.transpose_add, Matrix.transpose_one]
    have e : ∀ A B : Matrix (Fin d) (Fin d) (AE F E), (1 - A) * J * (1 - B) = (1 + A) * J * (1 + B) - 2 * (A * J + J * B) := by
      intro A B; noncomm_ring
    rw [e, hskew, mul_zero, sub_zero]
  have hU : ((1 - Y) * Np)ᵀ * J * ((1 - Y) * Np).map (cA σ) = J := by
    have eT : Npᵀ * (1 + Y)ᵀ = 1 := by rw [← Matrix.transpose_mul, hP1, Matrix.transpose_one]
    have eM : (1 + Y).map (cA σ) * Np.map (cA σ) = 1 := by rw [← hmap, hP1, hmap1]
    calc ((1 - Y) * Np)ᵀ * J * ((1 - Y) * Np).map (cA σ)
        = (Npᵀ * (1 + Y)ᵀ) * (((1 - Y) * Np)ᵀ * J * ((1 - Y) * Np).map (cA σ)) * ((1 + Y).map (cA σ) * Np.map (cA σ)) := by
          rw [eT, eM, Matrix.one_mul, Matrix.mul_one]
      _ = Npᵀ * (((1 - Y) * Np * (1 + Y))ᵀ * J * ((1 - Y) * Np * (1 + Y)).map (cA σ)) * Np.map (cA σ) := by
          rw [hmap ((1 - Y) * Np), Matrix.transpose_mul ((1 - Y) * Np)]
          simp only [Matrix.mul_assoc]
      _ = Npᵀ * ((1 + Y)ᵀ * J * (1 + Y).map (cA σ)) * Np.map (cA σ) := by rw [hGP, hQP]
      _ = (Npᵀ * (1 + Y)ᵀ) * J * ((1 + Y).map (cA σ) * Np.map (cA σ)) := by simp only [Matrix.mul_assoc]
      _ = J := by rw [eT, eM, Matrix.one_mul, Matrix.mul_one]
  let g : GL (Fin d) (AE F E) := ⟨(1 - Y) * Np, (1 + Y) * Nm, h1, h2⟩
  have hg : g ∈ UG (cA σ) (incM F W.J) := hU
  let h : UA σ W.J := ⟨g, hg⟩
  have hmat : mat h = (1 - Y) * Np := rfl
  have hmatinv : mat h⁻¹ = (1 + Y) * Nm := rfl
  refine ⟨h, ⟨?_, ?_⟩, ?_⟩
  · intro u hu
    have e : mat h - 1 = -(Y * Np) - Y * Np := by
      rw [hmat]
      calc (1 - Y) * Np - 1 = (1 - Y) * Np - (1 + Y) * Np := by rw [hP1]
        _ = -(Y * Np) - Y * Np := by noncomm_ring
    have hYu : u • Y = 0 := hY u hu
    rw [e, smul_sub, smul_neg, ← Matrix.smul_mul, hYu, Matrix.zero_mul, neg_zero, sub_zero]
  · intro z hz
    refine ⟨?_, ?_⟩
    · rw [hmat, ← Matrix.mulVec_mulVec, Matrix.sub_mulVec, Matrix.one_mulVec]
      exact sub_mem (hPL z hz) (hYL _ (hPL z hz))
    · rw [hmatinv, ← Matrix.mulVec_mulVec, Matrix.add_mulVec, Matrix.one_mulVec]
      exact add_mem (hML z hz) (hYL _ (hML z hz))
  · rw [hmat, hGP]

end GlobalTheory.CayleyStab

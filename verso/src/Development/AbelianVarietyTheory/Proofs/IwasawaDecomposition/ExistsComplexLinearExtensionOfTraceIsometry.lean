import Mathlib
import Formalism.LocalToGlobal.KernelLattices.LateralTheory
open NumberField IsDedekindDomain Formalism.L2.Ker Matrix
open scoped BigOperators

namespace GlobalTheory

/- English proof (translation)
Introduce `K E _ _ _ cj ι _ φ emb hφ hemb hK htr γ`. Set `b : Fin 4 × ι → Fin 4 → E` to `fun w => γ.g.symm (Pi.single w 1)`. Set `B : Matrix (Fin 4 × ι) (Fin 4 × ι) ℂ` to `fun v w => emb v.2 (b w v.1)`. Establish `hB : Bᴴ * B = 1`. Use extensionality with `w' w`.

Establish `h` using `congrArg φ (γ.isom (b w) (b w'))`. Simplify using `only [b, LinearEquiv.apply_symm_apply, map_sum, map_mul, hφ, ← htr, hemb] at h`. Rewrite using `[Matrix.mul_apply, Fintype.sum_prod_type]`. Establish `h2 : ∑ a, ∑ τ, Bᴴ w' (a, τ) * B (a, τ) w = ∑ a, ∑ τ, emb τ (b w a) * starRingEnd ℂ (emb τ (b w' a))`. Use `Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun τ _ => ?_` and prove the remaining obligations.

Rewrite using `[Matrix.conjTranspose_apply, mul_comm]`. Both sides reduce to the same expression. Rewrite using `[h2, ← h, Finset.sum_eq_single w]`. Distinguish the cases in `hw : w' = w`. Substitute `hw` using the available equality.

Simplify using the standard rewrite rules. Simplify using `[Matrix.one_apply_ne hw, Pi.single_eq_of_ne (Ne.symm hw)]`. Introduce `u _ hu`. Simplify using `[Pi.single_eq_of_ne hu]`. Simplify using the standard rewrite rules.

Establish `hB' : B * Bᴴ = 1` using `mul_eq_one_comm.mp hB`. Use `⟨Matrix.toLin'OfInv hB' hB, fun x => ?_⟩` and prove the remaining obligations. Establish `hx : x = ∑ w, γ.g x w • b w`. Apply `γ.g.injective` to reduce the goal to its premises. Simplify using `only [b, map_sum, map_smul, LinearEquiv.apply_symm_apply]`.

Use extensionality with `u`. Simplify using `[Finset.sum_apply, Pi.single_apply]`. Establish `hv : (fun w : Fin 4 × ι => emb w.2 (x w.1)) = B *ᵥ (fun w => φ (algebraMap K E (γ.g x w)))`. Use extensionality with `v`. Use `congrArg (fun y => emb v.2 (y v.1)) hx` as an intermediate fact.

Simplify using `only [Finset.sum_apply, Pi.smul_apply, Algebra.smul_def, map_sum, map_mul, hK] at this`. Rewrite using `[this]`. Simplify using `[Matrix.mulVec, dotProduct, B, mul_comm, hK]`. Rewrite using `[hv]`. Express the relevant statement in the definitionally equal form `Bᴴ *ᵥ (B *ᵥ _) = _`.

Rewrite using `[Matrix.mulVec_mulVec, hB, Matrix.one_mulVec]`.
-/
theorem exists_complexLinear_extension_of_traceIsometry : ∀ (K E : Type) [Field K] [Field E] [Algebra K E] (cj : E → E) (ι : Type) [Fintype ι] (φ : E →+* ℂ) (emb : ι → E →+* ℂ), (∀ y, φ (cj y) = starRingEnd ℂ (φ y)) → (∀ τ y, emb τ (cj y) = starRingEnd ℂ (emb τ y)) → (∀ τ (x : K), emb τ (algebraMap K E x) = φ (algebraMap K E x)) → (∀ y, ∑ τ, emb τ y = φ (algebraMap K E (Algebra.trace K E y))) → ∀ γ : IsoKG K E cj ι, ∃ gC : (Fin 4 × ι → ℂ) ≃ₗ[ℂ] (Fin 4 × ι → ℂ), ∀ x : Fin 4 → E, gC (fun w => emb w.2 (x w.1)) = fun w => φ (algebraMap K E (γ.g x w)) := by
  intro K E _ _ _ cj ι _ φ emb hφ hemb hK htr γ
  classical
  let b : Fin 4 × ι → Fin 4 → E := fun w => γ.g.symm (Pi.single w 1)
  let B : Matrix (Fin 4 × ι) (Fin 4 × ι) ℂ := fun v w => emb v.2 (b w v.1)
  have hB : Bᴴ * B = 1 := by
    ext w' w
    have h := congrArg φ (γ.isom (b w) (b w'))
    simp only [b, LinearEquiv.apply_symm_apply, map_sum, map_mul, hφ, ← htr, hemb] at h
    rw [Matrix.mul_apply, Fintype.sum_prod_type]
    have h2 : ∑ a, ∑ τ, Bᴴ w' (a, τ) * B (a, τ) w
        = ∑ a, ∑ τ, emb τ (b w a) * starRingEnd ℂ (emb τ (b w' a)) := by
      refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun τ _ => ?_
      rw [Matrix.conjTranspose_apply, mul_comm]
      rfl
    rw [h2, ← h, Finset.sum_eq_single w]
    · by_cases hw : w' = w
      · subst hw; simp
      · simp [Matrix.one_apply_ne hw, Pi.single_eq_of_ne (Ne.symm hw)]
    · intro u _ hu
      simp [Pi.single_eq_of_ne hu]
    · simp
  have hB' : B * Bᴴ = 1 := mul_eq_one_comm.mp hB
  refine ⟨Matrix.toLin'OfInv hB' hB, fun x => ?_⟩
  have hx : x = ∑ w, γ.g x w • b w := by
    apply γ.g.injective
    simp only [b, map_sum, map_smul, LinearEquiv.apply_symm_apply]
    ext u
    simp [Finset.sum_apply, Pi.single_apply]
  have hv : (fun w : Fin 4 × ι => emb w.2 (x w.1))
      = B *ᵥ (fun w => φ (algebraMap K E (γ.g x w))) := by
    ext v
    have := congrArg (fun y => emb v.2 (y v.1)) hx
    simp only [Finset.sum_apply, Pi.smul_apply, Algebra.smul_def, map_sum, map_mul, hK] at this
    rw [this]
    simp [Matrix.mulVec, dotProduct, B, mul_comm, hK]
  rw [hv]
  change Bᴴ *ᵥ (B *ᵥ _) = _
  rw [Matrix.mulVec_mulVec, hB, Matrix.one_mulVec]

end GlobalTheory

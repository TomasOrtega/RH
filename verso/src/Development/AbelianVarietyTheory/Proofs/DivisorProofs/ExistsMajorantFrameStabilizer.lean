import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoreConcl
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MatHomOfGAdSymm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHaarOfIsCompact
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.EventuallyAlgebraMapMemIntegers
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsIsLatticeFrameIsMajorantFrame
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.StabiliserEqCentraliserCartan
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MajorantFrameCommutesCartan

noncomputable section

namespace GlobalTheory.MajFrameCartan

open scoped TensorProduct Matrix ComplexOrder
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.UG GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.AdelicU

/- English proof (translation)
Introduce `F E _ _ _ _ _ σ B n X r s hB hX`. Establish `hcm` using `hB.cm`. Establish `hM : ∀ w : InfinitePlace F, (X.J.map (B.emb w).1)ᴴ = X.J.map (B.emb w).1` using `fun w => by`. Use extensionality with `i j`. Simplify using `only [Matrix.conjTranspose_apply, Matrix.map_apply]`.

Rewrite using `[← hcm.2.2.2 (B.emb w).1, hX.herm]`. Establish `hC : ∀ w : InfinitePlace F, Formalism.IndefR.Datum.IsCartanInv (X.Jᵀ.map (B.emb w).1) (X.θ w)` using `fun w => by`. Rewrite using `[Matrix.transpose_map]`. Conclude with `isCartanInv_transpose (hM w) (hX.cartan w)`. Use `choose b ε h1 h2 using fun w => GlobalTheory.Doubling.exists_frame_of_isCartanInv (hC w)`.

Set `e` to `fun w : InfinitePlace F => RingEquiv.ofBijective _ (infEmb_bijective hcm (B.emb w))`. Set `c : ∀ w : InfinitePlace F, GL (Fin n) (w.Completion ⊗[F] E)` to `fun w => bc (e w).symm.toRingHom (b w)`. Establish `hc : ∀ w, (c w).1.map (infEmb (B.emb w)) = (b w).1` using `fun w => Matrix.ext fun i j => (e w).apply_symm_apply _`. Establish `hc' : ∀ w, ((c w)⁻¹).1.map (infEmb (B.emb w)) = ((b w)⁻¹).1` using `fun w => by`. Rewrite using `[show (c w)⁻¹ = bc (e w).symm.toRingHom (b w)⁻¹ from (map_inv _ _).symm]`.

Conclude with `Matrix.ext fun i j => (e w).apply_symm_apply _`. Take `⟨a, -, ha⟩` from `GlobalTheory.AdelicU.Frames.exists_GL_of_components (F := F) (E := E) (n := n) ∅ (fun _ => 1) (fun _ _ => rfl) c`. Use `⟨a, fun w => ⟨ε w, ?_⟩, fun w k => ?_⟩` and prove the remaining obligations. Rewrite using `[ha w, GlobalTheory.Doubling.frame_local_iff hcm (B.emb w) X.Jᵀ (c w).1 (ε w), hc]`. Conclude with `h1 w`.

Establish `hK : ((matHom w.Completion σ X.Jᵀ k).1.map (infEmb (B.emb w)))ᴴ * X.Jᵀ.map (B.emb w).1 * (matHom w.Completion σ X.Jᵀ k).1.map (infEmb (B.emb w)) = X.Jᵀ.map (B.emb w).1` using `(archEquiv X.Jᵀ hcm (B.emb w) k).2`. Establish `hbc : (b w).1 * ((b w)⁻¹).1 = 1` using `Units.mul_inv _`. Establish `key : ∀ x : GL (Fin n) (w.Completion ⊗[F] E), x ∈ UJ (sigR w.Completion σ) 1 ↔ (x.1.map (infEmb (B.emb w)))ᴴ * x.1.map (infEmb (B.emb w)) = 1` using `fun x => by`. Express the relevant statement in the definitionally equal form `cT _ x.1 * 1 * x.1 = 1 ↔ _`. Rewrite using `[← (Matrix.map_injective (infEmb_bijective hcm (B.emb w)).1).eq_iff]`.

Use `beta_reduce`. Rewrite using `[mul_one, Matrix.map_mul, Frames.map_cT_sigR hcm, Matrix.map_one _ (map_zero _) (map_one _)]`. Rewrite using `[mem_stabArch, ha w, key, Units.val_mul, Units.val_mul, Matrix.map_mul, Matrix.map_mul, hc, hc', GlobalTheory.Doubling.unitary_iff_commute hbc (h1 w) (GlobalTheory.Doubling.diagonal_sign_mul_self (ε w)) hK, h2 w]`.
-/
theorem exists_majorantFrame_commute_iff : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E]
    [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n : ℕ) (X : Spc F E n) (r s : ℕ), B.IsGood σ → X.IsHerm σ B r s →
    ∃ a : GL (Fin n) (AF F ⊗[F] E), IsMajorantFrame σ X.Jᵀ a ∧ ∀ (w : InfinitePlace F) (k : GArch σ X.Jᵀ w),
      k ∈ stabArch σ X.Jᵀ w (bc (compInf F E w) a) ↔
        Commute ((matHom w.Completion σ X.Jᵀ k).1.map (infEmb (B.emb w))) (X.θ w) := by
  intro F E _ _ _ _ _ σ B n X r s hB hX
  have hcm := hB.cm
  have hM : ∀ w : InfinitePlace F, (X.J.map (B.emb w).1)ᴴ = X.J.map (B.emb w).1 := fun w => by
    ext i j
    simp only [Matrix.conjTranspose_apply, Matrix.map_apply]
    rw [← hcm.2.2.2 (B.emb w).1, hX.herm]
  have hC : ∀ w : InfinitePlace F, Formalism.IndefR.Datum.IsCartanInv (X.Jᵀ.map (B.emb w).1) (X.θ w) := fun w => by
    rw [Matrix.transpose_map]
    exact isCartanInv_transpose (hM w) (hX.cartan w)
  choose b ε h1 h2 using fun w => GlobalTheory.Doubling.exists_frame_of_isCartanInv (hC w)
  let e := fun w : InfinitePlace F => RingEquiv.ofBijective _ (infEmb_bijective hcm (B.emb w))
  let c : ∀ w : InfinitePlace F, GL (Fin n) (w.Completion ⊗[F] E) := fun w => bc (e w).symm.toRingHom (b w)
  have hc : ∀ w, (c w).1.map (infEmb (B.emb w)) = (b w).1 := fun w =>
    Matrix.ext fun i j => (e w).apply_symm_apply _
  have hc' : ∀ w, ((c w)⁻¹).1.map (infEmb (B.emb w)) = ((b w)⁻¹).1 := fun w => by
    rw [show (c w)⁻¹ = bc (e w).symm.toRingHom (b w)⁻¹ from (map_inv _ _).symm]
    exact Matrix.ext fun i j => (e w).apply_symm_apply _
  obtain ⟨a, -, ha⟩ := GlobalTheory.AdelicU.Frames.exists_GL_of_components (F := F) (E := E) (n := n) ∅ (fun _ => 1)
    (fun _ _ => rfl) c
  refine ⟨a, fun w => ⟨ε w, ?_⟩, fun w k => ?_⟩
  · rw [ha w, GlobalTheory.Doubling.frame_local_iff hcm (B.emb w) X.Jᵀ (c w).1 (ε w), hc]
    exact h1 w
  · have hK : ((matHom w.Completion σ X.Jᵀ k).1.map (infEmb (B.emb w)))ᴴ * X.Jᵀ.map (B.emb w).1 *
        (matHom w.Completion σ X.Jᵀ k).1.map (infEmb (B.emb w)) = X.Jᵀ.map (B.emb w).1 :=
      (archEquiv X.Jᵀ hcm (B.emb w) k).2
    have hbc : (b w).1 * ((b w)⁻¹).1 = 1 := Units.mul_inv _
    have key : ∀ x : GL (Fin n) (w.Completion ⊗[F] E), x ∈ UJ (sigR w.Completion σ) 1 ↔
        (x.1.map (infEmb (B.emb w)))ᴴ * x.1.map (infEmb (B.emb w)) = 1 := fun x => by
      change cT _ x.1 * 1 * x.1 = 1 ↔ _
      rw [← (Matrix.map_injective (infEmb_bijective hcm (B.emb w)).1).eq_iff]
      beta_reduce
      rw [mul_one, Matrix.map_mul, Frames.map_cT_sigR hcm, Matrix.map_one _ (map_zero _) (map_one _)]
    rw [mem_stabArch, ha w, key, Units.val_mul, Units.val_mul, Matrix.map_mul, Matrix.map_mul, hc, hc',
      GlobalTheory.Doubling.unitary_iff_commute hbc (h1 w) (GlobalTheory.Doubling.diagonal_sign_mul_self (ε w)) hK, h2 w]

end GlobalTheory.MajFrameCartan

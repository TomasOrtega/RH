import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHaarOfIsCompact
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MatHomOfGAdSymm
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.EventuallyAlgebraMapMemIntegers
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsIsLatticeFrameIsMajorantFrame
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.StabiliserEqCentraliserCartan

noncomputable section

namespace GlobalTheory.MajFrameCartan

open scoped TensorProduct Matrix ComplexOrder
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.UG GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.AdelicU

/- English proof (translation)
Take `⟨h1, h2, h3⟩` from `h`. Establish `h2' : θᴴ * Mᵀ * θ = Mᵀ`. Use `congrArg Matrix.transpose h2` as an intermediate fact. Rewrite `this` using `[Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose, ← Matrix.transpose_map]`. Use `show θᵀ.map star * Mᵀ * θ = Mᵀ`.

Rewrite using `[Matrix.mul_assoc]`. Conclude with `this`. Establish `hMt : (Mᵀ)ᴴ = Mᵀ`. Use extensionality with `i j`. Use `congrFun (congrFun hM j) i` as an intermediate fact.

Simplify `this` using `[Matrix.conjTranspose_apply]`. Establish `hH : (Mᵀ * θ)ᴴ = Mᵀ * θ`. Rewrite using `[Matrix.conjTranspose_mul, hMt]`. Combine the equalities or inequalities in the displayed calculation. Use `⟨h1, h2', Matrix.posDef_iff_dotProduct_mulVec.2 ⟨hH, fun x hx => ?_⟩⟩` and prove the remaining obligations.

Establish `e : star x ⬝ᵥ ((Mᵀ * θ) *ᵥ x) = (θ *ᵥ x) ⬝ᵥ (M *ᵥ star x)`. Rewrite using `[← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, Matrix.vecMul_transpose, dotProduct_comm]`. Establish `him` using `Matrix.IsHermitian.im_star_dotProduct_mulVec_self (A := Mᵀ * θ) hH x`. Use `Complex.pos_iff.mpr ⟨?_, ?_⟩` and prove the remaining obligations. Rewrite using `[e]`.

Conclude with `h3 x hx`. Simplify using `using him.symm`.
-/
theorem isCartanInv_transpose {n : ℕ} {M θ : Matrix (Fin n) (Fin n) ℂ} (hM : Mᴴ = M) (h : IsCartan M θ) :
    Formalism.IndefR.Datum.IsCartanInv Mᵀ θ := by
  obtain ⟨h1, h2, h3⟩ := h
  have h2' : θᴴ * Mᵀ * θ = Mᵀ := by
    have := congrArg Matrix.transpose h2
    rw [Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose, ← Matrix.transpose_map] at this
    show θᵀ.map star * Mᵀ * θ = Mᵀ
    rw [Matrix.mul_assoc]
    exact this
  have hMt : (Mᵀ)ᴴ = Mᵀ := by
    ext i j
    have := congrFun (congrFun hM j) i
    simpa [Matrix.conjTranspose_apply] using this
  have hH : (Mᵀ * θ)ᴴ = Mᵀ * θ := by
    rw [Matrix.conjTranspose_mul, hMt]
    calc θᴴ * Mᵀ = θᴴ * Mᵀ * (θ * θ) := by rw [h1, Matrix.mul_one]
      _ = (θᴴ * Mᵀ * θ) * θ := by simp only [Matrix.mul_assoc]
      _ = Mᵀ * θ := by rw [h2']
  refine ⟨h1, h2', Matrix.posDef_iff_dotProduct_mulVec.2 ⟨hH, fun x hx => ?_⟩⟩
  have e : star x ⬝ᵥ ((Mᵀ * θ) *ᵥ x) = (θ *ᵥ x) ⬝ᵥ (M *ᵥ star x) := by
    rw [← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, Matrix.vecMul_transpose, dotProduct_comm]
  have him := Matrix.IsHermitian.im_star_dotProduct_mulVec_self (A := Mᵀ * θ) hH x
  refine Complex.pos_iff.mpr ⟨?_, ?_⟩
  · rw [e]; exact h3 x hx
  · simpa using him.symm

/- English proof (translation)
Introduce `F E _ _ _ _ _ σ B n X r s hB hX`. Establish `hcm` using `hB.cm`. Establish `hM : ∀ w : InfinitePlace F, (X.J.map (B.emb w).1)ᴴ = X.J.map (B.emb w).1` using `fun w => by`. Use extensionality with `i j`. Simplify using `only [Matrix.conjTranspose_apply, Matrix.map_apply]`.

Rewrite using `[← hcm.2.2.2 (B.emb w).1, hX.herm]`. Establish `hC : ∀ w : InfinitePlace F, Formalism.IndefR.Datum.IsCartanInv (X.Jᵀ.map (B.emb w).1) (X.θ w)` using `fun w => by`. Rewrite using `[Matrix.transpose_map]`. Conclude with `isCartanInv_transpose (hM w) (hX.cartan w)`. Use `choose b ε h1 h2 using fun w => GlobalTheory.Doubling.exists_frame_of_isCartanInv (hC w)`.

Set `e` to `fun w : InfinitePlace F => RingEquiv.ofBijective _ (infEmb_bijective hcm (B.emb w))`. Set `c : ∀ w : InfinitePlace F, GL (Fin n) (w.Completion ⊗[F] E)` to `fun w => bc (e w).symm.toRingHom (b w)`. Establish `hc : ∀ w, (c w).1.map (infEmb (B.emb w)) = (b w).1` using `fun w => Matrix.ext fun i j => (e w).apply_symm_apply _`. Establish `hc' : ∀ w, ((c w)⁻¹).1.map (infEmb (B.emb w)) = ((b w)⁻¹).1` using `fun w => by`. Rewrite using `[show (c w)⁻¹ = bc (e w).symm.toRingHom (b w)⁻¹ from (map_inv _ _).symm]`.

Conclude with `Matrix.ext fun i j => (e w).apply_symm_apply _`. Take `⟨a, -, ha⟩` from `GlobalTheory.AdelicU.Frames.exists_GL_of_components (F := F) (E := E) (n := n) ∅ (fun _ => 1) (fun _ _ => rfl) c`. Use `⟨a, fun w => ⟨ε w, ?_⟩, fun w k hk => ?_⟩` and prove the remaining obligations. Rewrite using `[ha w, GlobalTheory.Doubling.frame_local_iff hcm (B.emb w) X.Jᵀ (c w).1 (ε w), hc]`. Conclude with `h1 w`.

Establish `hK : ((matHom w.Completion σ X.Jᵀ k).1.map (infEmb (B.emb w)))ᴴ * X.Jᵀ.map (B.emb w).1 * (matHom w.Completion σ X.Jᵀ k).1.map (infEmb (B.emb w)) = X.Jᵀ.map (B.emb w).1` using `(archEquiv X.Jᵀ hcm (B.emb w) k).2`. Establish `hbc : (b w).1 * ((b w)⁻¹).1 = 1` using `Units.mul_inv _`. Establish `key : ∀ x : GL (Fin n) (w.Completion ⊗[F] E), x ∈ UJ (sigR w.Completion σ) 1 → (x.1.map (infEmb (B.emb w)))ᴴ * x.1.map (infEmb (B.emb w)) = 1` using `fun x hx => by`. Establish `hx' : cT (sigR w.Completion σ) x.1 * 1 * x.1 = 1` using `hx`. Use `congrArg (fun y => y.map (infEmb (B.emb w))) hx'` as an intermediate fact.

Simplify `this` using `only [mul_one, Matrix.map_mul, Frames.map_cT_sigR hcm, Matrix.map_one _ (map_zero _) (map_one _)]`. Rewrite `hk` using `[mem_stabArch, ha w]`. Establish `hu` using `key _ hk`. Rewrite `hu` using `[Units.val_mul, Units.val_mul, Matrix.map_mul, Matrix.map_mul, hc, hc']`. Use `(GlobalTheory.Doubling.unitary_iff_commute hbc (h1 w) (GlobalTheory.Doubling.diagonal_sign_mul_self (ε w)) hK).1 hu` as an intermediate fact.

Rewrite `this` using `[h2 w]`. Then use the resulting hypothesis.
-/
theorem exists_majorantFrame_commute : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (B : Base F E) (n : ℕ) (X : Spc F E n) (r s : ℕ), B.IsGood σ → X.IsHerm σ B r s →
    ∃ a : GL (Fin n) (AF F ⊗[F] E), IsMajorantFrame σ X.Jᵀ a ∧ ∀ (w : InfinitePlace F) (k : GArch σ X.Jᵀ w),
      k ∈ stabArch σ X.Jᵀ w (bc (compInf F E w) a) →
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
  refine ⟨a, fun w => ⟨ε w, ?_⟩, fun w k hk => ?_⟩
  · rw [ha w, GlobalTheory.Doubling.frame_local_iff hcm (B.emb w) X.Jᵀ (c w).1 (ε w), hc]
    exact h1 w
  · have hK : ((matHom w.Completion σ X.Jᵀ k).1.map (infEmb (B.emb w)))ᴴ * X.Jᵀ.map (B.emb w).1 *
        (matHom w.Completion σ X.Jᵀ k).1.map (infEmb (B.emb w)) = X.Jᵀ.map (B.emb w).1 :=
      (archEquiv X.Jᵀ hcm (B.emb w) k).2
    have hbc : (b w).1 * ((b w)⁻¹).1 = 1 := Units.mul_inv _
    have key : ∀ x : GL (Fin n) (w.Completion ⊗[F] E), x ∈ UJ (sigR w.Completion σ) 1 →
        (x.1.map (infEmb (B.emb w)))ᴴ * x.1.map (infEmb (B.emb w)) = 1 := fun x hx => by
      have hx' : cT (sigR w.Completion σ) x.1 * 1 * x.1 = 1 := hx
      have := congrArg (fun y => y.map (infEmb (B.emb w))) hx'
      simpa only [mul_one, Matrix.map_mul, Frames.map_cT_sigR hcm, Matrix.map_one _ (map_zero _) (map_one _)]
        using this
    rw [mem_stabArch, ha w] at hk
    have hu := key _ hk
    rw [Units.val_mul, Units.val_mul, Matrix.map_mul, Matrix.map_mul, hc, hc'] at hu
    have := (GlobalTheory.Doubling.unitary_iff_commute hbc (h1 w) (GlobalTheory.Doubling.diagonal_sign_mul_self (ε w)) hK).1 hu
    rwa [h2 w] at this

end GlobalTheory.MajFrameCartan

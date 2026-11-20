import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.CmStarOfIsCMUnram
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ImportsRest
import Development.AbelianVarietyTheory.Proofs.HermitianTraceForms.ExistsOrthogonalBasisDotProductApplyEq

open NumberField Formalism.BasicNotions

namespace GlobalTheory.SA.AmbSig

open Matrix Module

/- English proof (translation)
Set `f : (Fin d → ℂ) →ₗ[ℂ] (Fin q → ℂ)` to `LinearMap.funLeft ℂ ℂ (Sum.inr : Fin q → Fin p ⊕ Fin q) ∘ₗ Matrix.mulVecLin N`. Establish `hf : Function.Injective f`. Use `(injective_iff_map_eq_zero f).2 fun c hc => ?_` and prove the remaining obligations. Use `set w := N *ᵥ c with hw`. Establish `hr : ∀ i, w (Sum.inr i) = 0` using `fun i => congrFun hc i`.

Establish `hform : star w ⬝ᵥ (Formalism.UG.Jpq p q *ᵥ w) = star c ⬝ᵥ (diagonal δ *ᵥ c)`. Rewrite using `[← hN, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]`. Use `conv_rhs => rw [Matrix.dotProduct_mulVec, ← Matrix.star_mulVec]`. Establish `hleft : (star w ⬝ᵥ (Formalism.UG.Jpq p q *ᵥ w)).re = ∑ i, Complex.normSq (w (Sum.inl i))`. Unfold `Formalism.UG.Jpq`.

Rewrite using `[Matrix.fromBlocks_mulVec]`. Simplify using `[dotProduct, Fintype.sum_sum_type, hr, Complex.mul_re, Complex.normSq_apply]`. Establish `hright : (star c ⬝ᵥ (diagonal δ *ᵥ c)).re = ∑ j, (δ j).re * Complex.normSq (c j)`. Simplify using `only [dotProduct, Matrix.mulVec_diagonal, Complex.re_sum, Pi.star_apply]`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations.

Simplify using `only [Complex.star_def, Complex.mul_re, Complex.mul_im, Complex.conj_re, Complex.conj_im, Complex.normSq_apply]`. Expand and normalize the polynomial expressions, which then agree. Establish `hnn : ∀ i, 0 ≤ Complex.normSq (w (Sum.inl i))` using `fun i => Complex.normSq_nonneg _`. Establish `hsum : ∑ i, Complex.normSq (w (Sum.inl i)) ≤ 0`. Rewrite using `[← hleft, hform, hright]`.

Conclude with `Finset.sum_nonpos fun j _ => mul_nonpos_of_nonpos_of_nonneg (hδ j) (Complex.normSq_nonneg _)`. Establish `hl : ∀ i, w (Sum.inl i) = 0` using `fun i => Complex.normSq_eq_zero.1 (le_antisymm ((Finset.single_le_sum (fun j _ => hnn j) (Finset.mem_univ i)).trans hsum) (hnn i))`. Apply `hinj` to reduce the goal to its premises. Use function extensionality and compare the values at `x`. Consider the cases of `x with`.

Consider the case `inl i => exact hl i`. Consider the case `inr i => exact hr i`. Simplify using `using LinearMap.finrank_le_finrank_of_injective hf`.
-/
theorem card_le_of_diag {p q d : ℕ} (N : Matrix (Fin p ⊕ Fin q) (Fin d) ℂ) (δ : Fin d → ℂ)
    (hδ : ∀ j, (δ j).re ≤ 0) (hN : Nᴴ * Formalism.UG.Jpq p q * N = diagonal δ)
    (hinj : ∀ c, N *ᵥ c = 0 → c = 0) : d ≤ q := by
  classical

  let f : (Fin d → ℂ) →ₗ[ℂ] (Fin q → ℂ) :=
    LinearMap.funLeft ℂ ℂ (Sum.inr : Fin q → Fin p ⊕ Fin q) ∘ₗ Matrix.mulVecLin N
  have hf : Function.Injective f := by
    refine (injective_iff_map_eq_zero f).2 fun c hc => ?_
    set w := N *ᵥ c with hw
    have hr : ∀ i, w (Sum.inr i) = 0 := fun i => congrFun hc i

    have hform : star w ⬝ᵥ (Formalism.UG.Jpq p q *ᵥ w) = star c ⬝ᵥ (diagonal δ *ᵥ c) := by
      rw [← hN, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
      conv_rhs => rw [Matrix.dotProduct_mulVec, ← Matrix.star_mulVec]
    have hleft : (star w ⬝ᵥ (Formalism.UG.Jpq p q *ᵥ w)).re = ∑ i, Complex.normSq (w (Sum.inl i)) := by
      unfold Formalism.UG.Jpq
      rw [Matrix.fromBlocks_mulVec]
      simp [dotProduct, Fintype.sum_sum_type, hr, Complex.mul_re, Complex.normSq_apply]
    have hright : (star c ⬝ᵥ (diagonal δ *ᵥ c)).re = ∑ j, (δ j).re * Complex.normSq (c j) := by
      simp only [dotProduct, Matrix.mulVec_diagonal, Complex.re_sum, Pi.star_apply]
      refine Finset.sum_congr rfl fun j _ => ?_
      simp only [Complex.star_def, Complex.mul_re, Complex.mul_im, Complex.conj_re,
        Complex.conj_im, Complex.normSq_apply]
      ring
    have hnn : ∀ i, 0 ≤ Complex.normSq (w (Sum.inl i)) := fun i => Complex.normSq_nonneg _
    have hsum : ∑ i, Complex.normSq (w (Sum.inl i)) ≤ 0 := by
      rw [← hleft, hform, hright]
      exact Finset.sum_nonpos fun j _ =>
        mul_nonpos_of_nonpos_of_nonneg (hδ j) (Complex.normSq_nonneg _)
    have hl : ∀ i, w (Sum.inl i) = 0 := fun i =>
      Complex.normSq_eq_zero.1 (le_antisymm
        ((Finset.single_le_sum (fun j _ => hnn j) (Finset.mem_univ i)).trans hsum) (hnn i))
    apply hinj
    funext x
    cases x with
    | inl i => exact hl i
    | inr i => exact hr i
  simpa using LinearMap.finrank_le_finrank_of_injective hf

/- English proof (translation)
Use `conv_lhs => rw [← S.frame.sum_repr x, ← S.frame.sum_repr y]`. Simplify using `only [map_sum, LinearMap.sum_apply, LinearMap.map_smulₛₗ, LinearMap.smul_apply, map_smul, smul_eq_mul, starRingEnd_apply, Finset.mul_sum, Finset.sum_mul]`. Simplify using `only [HSpace.gram]`. Conclude with `Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring`.
-/
theorem hT_eq_sum {E : Type} [Field E] [NumberField E] [StarRing E] (S : HSpace E) (x y : S.V) :
    S.hT x y = ∑ b, (∑ a, star (S.frame.repr x a) * S.gram a b) * S.frame.repr y b := by
  conv_lhs => rw [← S.frame.sum_repr x, ← S.frame.sum_repr y]
  simp only [map_sum, LinearMap.sum_apply, LinearMap.map_smulₛₗ, LinearMap.smul_apply, map_smul,
    smul_eq_mul, starRingEnd_apply, Finset.mul_sum, Finset.sum_mul]
  simp only [HSpace.gram]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

/- English proof (translation)
Introduce `E _ _ _ S k r hcm hok hsig`. Establish `hfac : ∀ τ : E →+* ℂ, S.rank = k + r + (r + 1) ∧ ∃ A : Matrix (Fin (k + r) ⊕ Fin (r + 1)) (Fin S.rank) ℂ, Aᴴ * Formalism.UG.Jpq (k + r) (r + 1) * A = S.gram.map τ ∧ ∃ B : Matrix (Fin S.rank) (Fin (k + r) ⊕ Fin (r + 1)) ℂ, B * A = 1`. Introduce `τ`. Establish `h` using `hok τ`. Rewrite `h` using `[hsig τ]`.

Take `⟨h1, ⟨A, hA⟩, h3⟩` from `GlobalTheory.Mem.SignatureFactor.exists_factor S.rank (k + r) (r + 1) _ h`. Take `⟨B, -, hBA⟩` from `h3 A hA`. Conclude with `⟨h1.symm, A, hA, B, hBA⟩`. Take `⟨τ₀⟩ : Nonempty (E →+* ℂ)` from `inferInstance`. Use `⟨hcm, ?_, ?_⟩` and prove the remaining obligations.

Rewrite using `[S.rank_eq, (hfac τ₀).1]`. Expand and normalize the polynomial expressions, which then agree. Introduce `τ U hU classical`. Take `⟨-, A, hA, B, hBA⟩` from `hfac τ`. Set `F : U →ₗ[E] U →ₛₗ[starRingEnd E] E` to `S.hT.flip.domRestrict₁₂ U U`.

Establish `hF : ∀ x y, starRingEnd E (F x y) = F y x` using `fun x y => S.herm.eq (y : S.V) (x : S.V)`. Take `⟨u, hu⟩` from `GlobalTheory.HermDiag.exists_orthogonal_basis_fin (E := E) (c := starRingEnd E) two_ne_zero (Module.finrank E U) F hF rfl`. Set `v : Fin (Module.finrank E U) → Fin S.rank → E` to `fun j => S.frame.repr (u j : S.V)`. Establish `hv : LinearIndependent E v`. Establish `hker : LinearMap.ker (S.frame.equivFun.toLinearMap ∘ₗ U.subtype) = ⊥` using `LinearMap.ker_eq_bot.2 (S.frame.equivFun.injective.comp Subtype.val_injective)`.

Conclude with `u.linearIndependent.map' _ hker`. Use `letI : Algebra E ℂ := τ.toAlgebra`. Use `haveI : FaithfulSMul E ℂ := (faithfulSMul_iff_algebraMap_injective E ℂ).2 τ.injective`. Establish `hvC : LinearIndependent ℂ (fun j => algebraMap E ℂ ∘ v j)` using `linearIndependent_algebraMap_comp_iff.2 hv`. Set `C : Matrix (Fin S.rank) (Fin (Module.finrank E U)) ℂ` to `Matrix.of fun a j => τ (v j a)`.

Use `card_le_of_diag (A * C) (fun j => τ (S.hT (u j : S.V) (u j : S.V))) (fun j => hU _ (u j).2) ?_ ?_` and prove the remaining obligations. Establish `hsplit : (A * C)ᴴ * Formalism.UG.Jpq (k + r) (r + 1) * (A * C) = Cᴴ * (Aᴴ * Formalism.UG.Jpq (k + r) (r + 1) * A) * C`. Simplify using `only [Matrix.conjTranspose_mul, Matrix.mul_assoc]`. Rewrite using `[hsplit, hA]`. Use extensionality with `i j`.

Establish `hij : τ (S.hT (u i : S.V) (u j : S.V)) = (Cᴴ * S.gram.map τ * C) i j`. Rewrite using `[hT_eq_sum, map_sum, Matrix.mul_apply]`. Use `Finset.sum_congr rfl fun b _ => ?_` and prove the remaining obligations. Rewrite using `[map_mul, map_sum, Matrix.mul_apply]`. Use `congr 1`.

Use `Finset.sum_congr rfl fun a _ => ?_` and prove the remaining obligations. Simplify using `[C, v, hcm τ]`. Rewrite using `[← hij, Matrix.diagonal_apply]`. Use `split_ifs with h`. Rewrite using `[h]`.

Establish `h0 : F (u j) (u i) = 0` using `hu j i (Ne.symm h)`. Simplify using `only [F, LinearMap.domRestrict₁₂_apply, LinearMap.flip_apply] at h0`. Rewrite using `[h0, map_zero]`. Introduce `c hc`. Establish `hCc : C *ᵥ c = 0`.

Rewrite `hc` using `[← Matrix.mulVec_mulVec]`. Rewrite using `[← Matrix.one_mulVec (C *ᵥ c), ← hBA, ← Matrix.mulVec_mulVec, hc, Matrix.mulVec_zero]`. Establish `hlin` using `Fintype.linearIndependent_iff.1 hvC c (by`. Rewrite using `[← hCc]`. Use function extensionality and compare the values at `a`.

Simplify using `[Matrix.mulVec, dotProduct, Finset.sum_apply, C, mul_comm, RingHom.algebraMap_toAlgebra])`. Use function extensionality and compare the values at `j`. Conclude with `hlin j`.
-/
theorem amb_of_sig : ∀ (E : Type) [Field E] [NumberField E] [StarRing E] (S : HSpace E) (k r : ℕ),
    GlobalTheory.SA.CMStar E → S.SigOK → (∀ τ : E →+* ℂ, S.sig τ = (k + r, r + 1)) → GlobalTheory.SA.Amb S k r := by
  intro E _ _ _ S k r hcm hok hsig

  have hfac : ∀ τ : E →+* ℂ, S.rank = k + r + (r + 1) ∧
      ∃ A : Matrix (Fin (k + r) ⊕ Fin (r + 1)) (Fin S.rank) ℂ,
        Aᴴ * Formalism.UG.Jpq (k + r) (r + 1) * A = S.gram.map τ ∧
        ∃ B : Matrix (Fin S.rank) (Fin (k + r) ⊕ Fin (r + 1)) ℂ, B * A = 1 := by
    intro τ
    have h := hok τ
    rw [hsig τ] at h
    obtain ⟨h1, ⟨A, hA⟩, h3⟩ :=
      GlobalTheory.Mem.SignatureFactor.exists_factor S.rank (k + r) (r + 1) _ h
    obtain ⟨B, -, hBA⟩ := h3 A hA
    exact ⟨h1.symm, A, hA, B, hBA⟩
  obtain ⟨τ₀⟩ : Nonempty (E →+* ℂ) := inferInstance
  refine ⟨hcm, ?_, ?_⟩
  · rw [S.rank_eq, (hfac τ₀).1]
    ring
  · intro τ U hU
    classical
    obtain ⟨-, A, hA, B, hBA⟩ := hfac τ

    let F : U →ₗ[E] U →ₛₗ[starRingEnd E] E := S.hT.flip.domRestrict₁₂ U U
    have hF : ∀ x y, starRingEnd E (F x y) = F y x := fun x y => S.herm.eq (y : S.V) (x : S.V)
    obtain ⟨u, hu⟩ := GlobalTheory.HermDiag.exists_orthogonal_basis_fin (E := E) (c := starRingEnd E)
      two_ne_zero (Module.finrank E U) F hF rfl

    let v : Fin (Module.finrank E U) → Fin S.rank → E := fun j => S.frame.repr (u j : S.V)
    have hv : LinearIndependent E v := by
      have hker : LinearMap.ker (S.frame.equivFun.toLinearMap ∘ₗ U.subtype) = ⊥ :=
        LinearMap.ker_eq_bot.2 (S.frame.equivFun.injective.comp Subtype.val_injective)
      exact u.linearIndependent.map' _ hker
    letI : Algebra E ℂ := τ.toAlgebra
    haveI : FaithfulSMul E ℂ := (faithfulSMul_iff_algebraMap_injective E ℂ).2 τ.injective
    have hvC : LinearIndependent ℂ (fun j => algebraMap E ℂ ∘ v j) :=
      linearIndependent_algebraMap_comp_iff.2 hv
    let C : Matrix (Fin S.rank) (Fin (Module.finrank E U)) ℂ := Matrix.of fun a j => τ (v j a)
    refine card_le_of_diag (A * C) (fun j => τ (S.hT (u j : S.V) (u j : S.V)))
      (fun j => hU _ (u j).2) ?_ ?_
    · have hsplit : (A * C)ᴴ * Formalism.UG.Jpq (k + r) (r + 1) * (A * C) =
          Cᴴ * (Aᴴ * Formalism.UG.Jpq (k + r) (r + 1) * A) * C := by
        simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
      rw [hsplit, hA]
      ext i j
      have hij : τ (S.hT (u i : S.V) (u j : S.V)) = (Cᴴ * S.gram.map τ * C) i j := by
        rw [hT_eq_sum, map_sum, Matrix.mul_apply]
        refine Finset.sum_congr rfl fun b _ => ?_
        rw [map_mul, map_sum, Matrix.mul_apply]
        congr 1
        refine Finset.sum_congr rfl fun a _ => ?_
        simp [C, v, hcm τ]
      rw [← hij, Matrix.diagonal_apply]
      split_ifs with h
      · rw [h]
      · have h0 : F (u j) (u i) = 0 := hu j i (Ne.symm h)
        simp only [F, LinearMap.domRestrict₁₂_apply, LinearMap.flip_apply] at h0
        rw [h0, map_zero]
    · intro c hc
      have hCc : C *ᵥ c = 0 := by
        rw [← Matrix.mulVec_mulVec] at hc
        rw [← Matrix.one_mulVec (C *ᵥ c), ← hBA, ← Matrix.mulVec_mulVec, hc, Matrix.mulVec_zero]
      have hlin := Fintype.linearIndependent_iff.1 hvC c (by
        rw [← hCc]
        funext a
        simp [Matrix.mulVec, dotProduct, Finset.sum_apply, C, mul_comm, RingHom.algebraMap_toAlgebra])
      funext j
      exact hlin j

end GlobalTheory.SA.AmbSig

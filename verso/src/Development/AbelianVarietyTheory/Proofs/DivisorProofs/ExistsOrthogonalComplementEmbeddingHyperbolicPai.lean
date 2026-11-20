import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.AdelicU

namespace GlobalTheory

/- English proof (translation)
Introduce `F E _ _ _ _ _ σ n n₁ J x y hn hJ hxx hyy hxy`. Use `set a : Fin n → E := J *ᵥ fun i => σ (x i) with ha_def`. Use `set b : Fin n → E := J *ᵥ fun i => σ (y i) with hb_def`. Establish `hfa : ∀ z, form σ J z x = z ⬝ᵥ a` using `fun z => rfl`. Establish `hfb : ∀ z, form σ J z y = z ⬝ᵥ b` using `fun z => rfl`.

Establish `hxa : x ⬝ᵥ a = 0` using `hxx`. Establish `hxb : x ⬝ᵥ b = 1` using `hxy`. Establish `ha : a ≠ 0`. Introduce `h0`. Establish `hv : x ᵥ* J = 0`.

Use function extensionality and compare the values at `j`. Apply `σ.toRingHom.injective` to reduce the goal to its premises. Establish `h1` using `congrFun h0 j`. Simplify using `only [ha_def, Matrix.mulVec, dotProduct, Pi.zero_apply] at h1`. Simplify using `only [Matrix.vecMul, dotProduct, Pi.zero_apply, map_zero, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, map_sum, map_mul]`.

Rewrite using `[← h1]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[hJ j i, mul_comm]`. Apply `one_ne_zero (α := E)` to reduce the goal to its premises. Rewrite using `[← hxb, hb_def, Matrix.dotProduct_mulVec, hv, zero_dotProduct]`.

Choose the witnesses or unpack the hypotheses as in `⟨i, hi⟩ : ∃ i, a i ≠ 0 := by`. Assume the negation of the conclusion as `h`. Use `push_neg at h`. Conclude with `ha (funext h)`. Use `set w : Fin n → E := (a i)⁻¹ • (Pi.single i 1 - (b i) • x) with hw`.

Establish `hwa : w ⬝ᵥ a = 1`. Rewrite using `[hw, smul_dotProduct, sub_dotProduct, smul_dotProduct, hxa, single_dotProduct]`. Simplify using `[hi]`. Establish `hwb : w ⬝ᵥ b = 0`. Rewrite using `[hw, smul_dotProduct, sub_dotProduct, smul_dotProduct, hxb, single_dotProduct]`.

Simplify using the standard rewrite rules. Set `M : Matrix (Fin 2) (Fin n) E` to `Matrix.of ![a, b]`. Establish `hM : ∀ z, M *ᵥ z = ![z ⬝ᵥ a, z ⬝ᵥ b]`. Apply the tactic sequence `intro z; funext k; fin_cases k <;> simp [M, Matrix.mulVec, dotProduct_comm]`. Establish `hsurj : LinearMap.range (Matrix.mulVecLin M) = ⊤`.

Rewrite using `[LinearMap.range_eq_top]`. Introduce `v`. Use `⟨v 0 • w + v 1 • x, ?_⟩` and prove the remaining obligations. Rewrite using `[Matrix.mulVecLin_apply, hM]`. Apply the tactic sequence `funext k; fin_cases k <;> simp [add_dotProduct, smul_dotProduct, hwa, hwb, hxa, hxb]`.

Establish `hrank : Module.finrank E (LinearMap.ker (Matrix.mulVecLin M)) = n₁`. Establish `h` using `LinearMap.finrank_range_add_finrank_ker (Matrix.mulVecLin M)`. Rewrite `h` using `[hsurj, finrank_top, Module.finrank_fin_fun, Module.finrank_fin_fun]`. Use linear arithmetic over natural numbers and integers. Use `set K := LinearMap.ker (Matrix.mulVecLin M) with hK`.

Establish `hmemK : ∀ z, z ∈ K ↔ z ⬝ᵥ a = 0 ∧ z ⬝ᵥ b = 0`. Introduce `z`. Rewrite using `[hK, LinearMap.mem_ker, Matrix.mulVecLin_apply, hM]`. Prove the components needed by the constructor for the conclusion. Introduce `h; exact ⟨by simpa using congrFun h 0, by simpa using congrFun h 1⟩`.

Apply the tactic sequence `rintro ⟨h1, h2⟩; funext k; fin_cases k <;> simp [h1, h2]`. Set `bK : Module.Basis (Fin n₁) E K` to `Module.finBasisOfFinrankEq E K hrank`. Set `f : (Fin n₁ → E) →ₗ[E] (Fin n → E)` to `K.subtype ∘ₗ bK.equivFun.symm.toLinearMap`. Establish `hfinj : LinearMap.ker f = ⊥`. Rewrite using `[LinearMap.ker_eq_bot]`.

Conclude with `Subtype.val_injective.comp bK.equivFun.symm.injective`. Take `⟨g, hg⟩` from `LinearMap.exists_leftInverse_of_injective f hfinj`. Use `⟨LinearMap.toMatrix' f, LinearMap.toMatrix' g, ?_, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[← LinearMap.toMatrix'_comp, hg, LinearMap.toMatrix'_id]`. Introduce `u`.

Rewrite using `[LinearMap.toMatrix'_mulVec, hfa, hfb]`. Conclude with `(hmemK _).1 (bK.equivFun.symm u).2`. Introduce `z h1 h2`. Establish `hz : z ∈ K` using `(hmemK z).2 ⟨h1, h2⟩`. Use `⟨bK.equivFun ⟨z, hz⟩, ?_⟩` and prove the remaining obligations.

Rewrite using `[LinearMap.toMatrix'_mulVec]`. Simplify using `[f]`.
-/
theorem exists_orthCompl_hypPair : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (n n₁ : ℕ) (J : Matrix (Fin n) (Fin n) E) (x y : Fin n → E),
    n = n₁ + 2 → (∀ i j, σ (J j i) = J i j) → form σ J x x = 0 → form σ J y y = 0 → form σ J x y = 1 →
    ∃ (ι : Matrix (Fin n) (Fin n₁) E) (P : Matrix (Fin n₁) (Fin n) E), P * ι = 1 ∧
      (∀ u, form σ J (ι *ᵥ u) x = 0 ∧ form σ J (ι *ᵥ u) y = 0) ∧
      ∀ z, form σ J z x = 0 → form σ J z y = 0 → ∃ u, z = ι *ᵥ u := by
  intro F E _ _ _ _ _ σ n n₁ J x y hn hJ hxx hyy hxy
  classical
  set a : Fin n → E := J *ᵥ fun i => σ (x i) with ha_def
  set b : Fin n → E := J *ᵥ fun i => σ (y i) with hb_def
  have hfa : ∀ z, form σ J z x = z ⬝ᵥ a := fun z => rfl
  have hfb : ∀ z, form σ J z y = z ⬝ᵥ b := fun z => rfl
  have hxa : x ⬝ᵥ a = 0 := hxx
  have hxb : x ⬝ᵥ b = 1 := hxy
  have ha : a ≠ 0 := by
    intro h0
    have hv : x ᵥ* J = 0 := by
      funext j
      apply σ.toRingHom.injective
      have h1 := congrFun h0 j
      simp only [ha_def, Matrix.mulVec, dotProduct, Pi.zero_apply] at h1
      simp only [Matrix.vecMul, dotProduct, Pi.zero_apply, map_zero, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, map_sum, map_mul]
      rw [← h1]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [hJ j i, mul_comm]
    apply one_ne_zero (α := E)
    rw [← hxb, hb_def, Matrix.dotProduct_mulVec, hv, zero_dotProduct]
  obtain ⟨i, hi⟩ : ∃ i, a i ≠ 0 := by
    by_contra h; push_neg at h; exact ha (funext h)
  set w : Fin n → E := (a i)⁻¹ • (Pi.single i 1 - (b i) • x) with hw
  have hwa : w ⬝ᵥ a = 1 := by
    rw [hw, smul_dotProduct, sub_dotProduct, smul_dotProduct, hxa, single_dotProduct]
    simp [hi]
  have hwb : w ⬝ᵥ b = 0 := by
    rw [hw, smul_dotProduct, sub_dotProduct, smul_dotProduct, hxb, single_dotProduct]
    simp
  let M : Matrix (Fin 2) (Fin n) E := Matrix.of ![a, b]
  have hM : ∀ z, M *ᵥ z = ![z ⬝ᵥ a, z ⬝ᵥ b] := by
    intro z; funext k; fin_cases k <;> simp [M, Matrix.mulVec, dotProduct_comm]
  have hsurj : LinearMap.range (Matrix.mulVecLin M) = ⊤ := by
    rw [LinearMap.range_eq_top]
    intro v
    refine ⟨v 0 • w + v 1 • x, ?_⟩
    rw [Matrix.mulVecLin_apply, hM]
    funext k; fin_cases k <;> simp [add_dotProduct, smul_dotProduct, hwa, hwb, hxa, hxb]
  have hrank : Module.finrank E (LinearMap.ker (Matrix.mulVecLin M)) = n₁ := by
    have h := LinearMap.finrank_range_add_finrank_ker (Matrix.mulVecLin M)
    rw [hsurj, finrank_top, Module.finrank_fin_fun, Module.finrank_fin_fun] at h
    omega
  set K := LinearMap.ker (Matrix.mulVecLin M) with hK
  have hmemK : ∀ z, z ∈ K ↔ z ⬝ᵥ a = 0 ∧ z ⬝ᵥ b = 0 := by
    intro z
    rw [hK, LinearMap.mem_ker, Matrix.mulVecLin_apply, hM]
    constructor
    · intro h; exact ⟨by simpa using congrFun h 0, by simpa using congrFun h 1⟩
    · rintro ⟨h1, h2⟩; funext k; fin_cases k <;> simp [h1, h2]
  let bK : Module.Basis (Fin n₁) E K := Module.finBasisOfFinrankEq E K hrank
  let f : (Fin n₁ → E) →ₗ[E] (Fin n → E) := K.subtype ∘ₗ bK.equivFun.symm.toLinearMap
  have hfinj : LinearMap.ker f = ⊥ := by
    rw [LinearMap.ker_eq_bot]
    exact Subtype.val_injective.comp bK.equivFun.symm.injective
  obtain ⟨g, hg⟩ := LinearMap.exists_leftInverse_of_injective f hfinj
  refine ⟨LinearMap.toMatrix' f, LinearMap.toMatrix' g, ?_, ?_, ?_⟩
  · rw [← LinearMap.toMatrix'_comp, hg, LinearMap.toMatrix'_id]
  · intro u
    rw [LinearMap.toMatrix'_mulVec, hfa, hfb]
    exact (hmemK _).1 (bK.equivFun.symm u).2
  · intro z h1 h2
    have hz : z ∈ K := (hmemK z).2 ⟨h1, h2⟩
    refine ⟨bK.equivFun ⟨z, hz⟩, ?_⟩
    rw [LinearMap.toMatrix'_mulVec]
    simp [f]

end GlobalTheory

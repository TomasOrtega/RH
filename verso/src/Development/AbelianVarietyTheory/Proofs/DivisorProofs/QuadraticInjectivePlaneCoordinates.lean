import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MulTransposeInjective

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.MixedLagr
open GlobalTheory.Doubling (absE)

noncomputable section

namespace GlobalTheory.MixedLagr

/- English proof (translation)
Introduce `F E _ _ _ _ _ σ n d d₁ X W W₁ M M₁ H' hE hd hxy hιy hι f hf hfe K hK hK0`. Use `haveI : Module.Finite F E := Module.finite_of_finrank_pos (by omega)`. Set `Φ : (Fin n → E) × K →ₗ[F] Matrix (Fin n) (Fin d) E` to `{ toFun := fun p => Matrix.vecMulVec p.1 H'.x + (p.2 : Matrix (Fin n) (Fin d₁) E) * H'.ιᵀ map_add' := fun p q => by`. Simplify using `only [Prod.fst_add, Prod.snd_add, Submodule.coe_add, Matrix.add_vecMulVec, Matrix.add_mul]`. Normalize the expressions using the abelian group laws.

Use the proof step `map_smul' := fun c p => by`. Use extensionality with `i j`. Simplify using `[Matrix.vecMulVec_apply, Matrix.mul_apply, Finset.smul_sum, smul_mul_assoc, smul_add] }`. Establish `hΦ : ∀ p, Φ p = Matrix.vecMulVec p.1 H'.x + (p.2 : Matrix (Fin n) (Fin d₁) E) * H'.ιᵀ` using `fun _ => rfl`. Establish `h1 : incM F (1 : Matrix (Fin n) (Fin n) E) = 1`.

Use extensionality with `i j`. Distinguish the cases in `h : i = j`. Substitute `h` using the available equality. Simplify using `[incM]`. Simplify using `[incM, Matrix.one_apply, h]`.

Establish `hmem : ∀ p, f (Φ p) ∈ lagr M M₁ H'`. Introduce `p`. Rewrite using `[mem_lagr, hfe, LinearEquiv.symm_apply_apply]`. Use `⟨Matrix.vecMulVec (incV F p.1) (incV F H'.x), ⟨incV F p.1, rfl⟩, incM F (p.2 : Matrix (Fin n) (Fin d₁) E), hK0 _ p.2.2, ?_⟩` and prove the remaining obligations. Rewrite using `[h1, Matrix.one_mul, hΦ]`.

Use extensionality with `i j`. Simplify using `[incM, incV, Matrix.vecMulVec_apply, Matrix.mul_apply, map_sum, map_mul]`. Establish `hform : ∀ (a : E) (u v : Fin d → E), form σ W.J (a • u + v) H'.y = a * form σ W.J u H'.y + form σ W.J v H'.y`. Introduce `a u v`. Simplify using `[form, add_dotProduct, smul_dotProduct]`.

Establish `hinj : Function.Injective Φ`. Rewrite using `[← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']`. Introduce `p hp`. Rewrite `hp` using `[hΦ]`. Establish `hrow : ∀ i, (p.1 i) • H'.x + H'.ι *ᵥ ((p.2 : Matrix (Fin n) (Fin d₁) E) i) = 0`.

Introduce `i`. Use function extensionality and compare the values at `j`. Use `congrFun (congrFun hp i) j` as an intermediate fact. Simplify using `only [Matrix.add_apply, Matrix.vecMulVec_apply, Matrix.mul_apply, Matrix.transpose_apply, Matrix.zero_apply] at this`. Simplify using `only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Matrix.mulVec, dotProduct, Pi.zero_apply]`.

Rewrite using `[← this]`. Use `congr 1`. Conclude with `Finset.sum_congr rfl fun k _ => mul_comm _ _`. Establish `hy : p.1 = 0`. Use function extensionality and compare the values at `i`.

Establish `: form σ W.J ((p.1 i) • H'.x + H'.ι *ᵥ ((p.2 : Matrix (Fin n) (Fin d₁) E) i)) H'.y = form σ W.J 0 H'.y`. Rewrite using `[hrow i]`. Rewrite `this` using `[hform, hxy, hιy]`. Simplify `this` using `[form]`. Establish `hz : (p.2 : Matrix (Fin n) (Fin d₁) E) = 0`.

Apply `hι` to reduce the goal to its premises. Simplify using `only`. Rewrite using `[Matrix.zero_mul, ← hp, hy, Matrix.zero_vecMulVec, zero_add]`. Conclude with `Prod.ext hy (Subtype.ext hz)`. Set `g` to `(f ∘ₗ Φ).codRestrict (lagr M M₁ H') hmem`.

Establish `hg : Function.Injective g`. Introduce `p q h`. Apply `hinj` to reduce the goal to its premises. Apply `hf` to reduce the goal to its premises. Simplify `congrArg Subtype.val h` using `[g]`.

Establish `hle` using `LinearMap.finrank_le_finrank_of_injective hg`. Establish `hdom : Module.finrank F ((Fin n → E) × K) = n * d`. Rewrite using `[Module.finrank_prod, Module.finrank_pi_fintype, hK]`. Simplify using `[hE, hd]`. Expand and normalize the polynomial expressions, which then agree.

Use linear arithmetic over natural numbers and integers.
-/
theorem le_finrank_lagr : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (n d d₁ : ℕ) (X : Spc F E n) (W : Spc F E d) (W₁ : Spc F E d₁) (M : Model σ X W) (M₁ : Model σ X W₁) (H' : Plane E d d₁),
    Module.finrank F E = 2 → d = d₁ + 2 → form σ W.J H'.x H'.y = 1 → (∀ u, form σ W.J (H'.ι *ᵥ u) H'.y = 0) →
    (Function.Injective fun z : Matrix (Fin n) (Fin d₁) E => z * H'.ιᵀ) →
    ∀ f : Matrix (Fin n) (Fin d) E →ₗ[F] (Fin n × Fin d → F) × (Fin n × Fin d → F),
      Function.Injective f → (∀ x, hat (f x) = M.co.e (incM F x)) →
    ∀ K : Submodule F (Matrix (Fin n) (Fin d₁) E), Module.finrank F K = n * d₁ → (∀ z ∈ K, (M₁.co.e (incM F z)).1 = 0) →
      n * d ≤ Module.finrank F (lagr M M₁ H') := by
  intro F E _ _ _ _ _ σ n d d₁ X W W₁ M M₁ H' hE hd hxy hιy hι f hf hfe K hK hK0
  haveI : Module.Finite F E := Module.finite_of_finrank_pos (by omega)

  let Φ : (Fin n → E) × K →ₗ[F] Matrix (Fin n) (Fin d) E :=
    { toFun := fun p => Matrix.vecMulVec p.1 H'.x + (p.2 : Matrix (Fin n) (Fin d₁) E) * H'.ιᵀ
      map_add' := fun p q => by
        simp only [Prod.fst_add, Prod.snd_add, Submodule.coe_add, Matrix.add_vecMulVec, Matrix.add_mul]; abel
      map_smul' := fun c p => by
        ext i j
        simp [Matrix.vecMulVec_apply, Matrix.mul_apply, Finset.smul_sum, smul_mul_assoc, smul_add] }
  have hΦ : ∀ p, Φ p = Matrix.vecMulVec p.1 H'.x + (p.2 : Matrix (Fin n) (Fin d₁) E) * H'.ιᵀ := fun _ => rfl
  have h1 : incM F (1 : Matrix (Fin n) (Fin n) E) = 1 := by
    ext i j
    by_cases h : i = j
    · subst h; simp [incM]
    · simp [incM, Matrix.one_apply, h]
  have hmem : ∀ p, f (Φ p) ∈ lagr M M₁ H' := by
    intro p
    rw [mem_lagr, hfe, LinearEquiv.symm_apply_apply]
    refine ⟨Matrix.vecMulVec (incV F p.1) (incV F H'.x), ⟨incV F p.1, rfl⟩, incM F (p.2 : Matrix (Fin n) (Fin d₁) E),
      hK0 _ p.2.2, ?_⟩
    rw [h1, Matrix.one_mul, hΦ]
    ext i j
    simp [incM, incV, Matrix.vecMulVec_apply, Matrix.mul_apply, map_sum, map_mul]
  have hform : ∀ (a : E) (u v : Fin d → E), form σ W.J (a • u + v) H'.y = a * form σ W.J u H'.y + form σ W.J v H'.y := by
    intro a u v
    simp [form, add_dotProduct, smul_dotProduct]
  have hinj : Function.Injective Φ := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro p hp
    rw [hΦ] at hp
    have hrow : ∀ i, (p.1 i) • H'.x + H'.ι *ᵥ ((p.2 : Matrix (Fin n) (Fin d₁) E) i) = 0 := by
      intro i
      funext j
      have := congrFun (congrFun hp i) j
      simp only [Matrix.add_apply, Matrix.vecMulVec_apply, Matrix.mul_apply, Matrix.transpose_apply,
        Matrix.zero_apply] at this
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Matrix.mulVec, dotProduct, Pi.zero_apply]
      rw [← this]
      congr 1
      exact Finset.sum_congr rfl fun k _ => mul_comm _ _
    have hy : p.1 = 0 := by
      funext i
      have : form σ W.J ((p.1 i) • H'.x + H'.ι *ᵥ ((p.2 : Matrix (Fin n) (Fin d₁) E) i)) H'.y = form σ W.J 0 H'.y := by
        rw [hrow i]
      rw [hform, hxy, hιy] at this
      simpa [form] using this
    have hz : (p.2 : Matrix (Fin n) (Fin d₁) E) = 0 := by
      apply hι
      simp only
      rw [Matrix.zero_mul, ← hp, hy, Matrix.zero_vecMulVec, zero_add]
    exact Prod.ext hy (Subtype.ext hz)
  let g := (f ∘ₗ Φ).codRestrict (lagr M M₁ H') hmem
  have hg : Function.Injective g := by
    intro p q h
    apply hinj; apply hf
    simpa [g] using congrArg Subtype.val h
  have hle := LinearMap.finrank_le_finrank_of_injective hg
  have hdom : Module.finrank F ((Fin n → E) × K) = n * d := by
    rw [Module.finrank_prod, Module.finrank_pi_fintype, hK]
    simp [hE, hd]
    ring
  omega

end GlobalTheory.MixedLagr

end

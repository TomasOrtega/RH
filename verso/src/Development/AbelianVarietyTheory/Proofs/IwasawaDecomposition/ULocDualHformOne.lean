import Mathlib
import Formalism.LocalToGlobal.HermitianForms.DefsGH
import Formalism.LocalToGlobal.Columns.RecLevelLocT
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.Col Formalism.UG Formalism.L2.Forms Matrix
open scoped TensorProduct

noncomputable section

namespace GlobalTheory

/- English proof (translation)
Take `⟨r, rfl⟩` from `ha`. Conclude with `⟨⟨σ r, (RingOfIntegers.isIntegral_coe r).map σ.toIntAlgHom⟩, rfl⟩`.
-/
theorem uLocDual_intOE_map {E : Type} [Field E] [NumberField E] (σ : E →+* E) {a : E}
    (ha : a ∈ intOE E) : σ a ∈ intOE E := by
  obtain ⟨r, rfl⟩ := ha
  exact ⟨⟨σ r, (RingOfIntegers.isIntegral_coe r).map σ.toIntAlgHom⟩, rfl⟩

/- English proof (translation)
Unfold `Formalism.UG.hform`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[Finset.sum_eq_single i]`. Rewrite using `[Matrix.one_apply_eq, mul_one]`. Introduce `j _ hj`.

Rewrite using `[Matrix.one_apply_ne (Ne.symm hj), mul_zero, zero_mul]`. Introduce `h`. Conclude with `absurd (Finset.mem_univ _) h`.
-/
theorem uLocDual_hform_one {E : Type} [Field E] {n : ℕ} (σ : E →+* E) (x y : Fin n → E) :
    Formalism.UG.hform σ (1 : Matrix (Fin n) (Fin n) E) x y = ∑ i, σ (x i) * y i := by
  unfold Formalism.UG.hform
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_eq_single i]
  · rw [Matrix.one_apply_eq, mul_one]
  · intro j _ hj; rw [Matrix.one_apply_ne (Ne.symm hj), mul_zero, zero_mul]
  · intro h; exact absurd (Finset.mem_univ _) h

/- English proof (translation)
Introduce `F E _ _ _ _ _ σ _ n _ p q hp hq`. Establish `e : dualSet (σ : E →+* E) (1 : Matrix (Fin n) (Fin n) E) (rll_dLat n ((p : E)⁻¹)) = (rll_dLat n (q : E) : Set (Fin n → E))`. Use extensionality with `y`. Rewrite using `[SetLike.mem_coe, rll_mem_dLat]`. Use `show (∀ x ∈ rll_dLat n ((p : E)⁻¹), Formalism.UG.hform (σ : E →+* E) 1 x y ∈ (algebraMap (𝓞 E) E).range) ↔ _`.

Simplify using `only [uLocDual_hform_one]`. Prove the components needed by the constructor for the conclusion. Introduce `hy`. Use `⟨fun i hi => ?_, ?_⟩` and prove the remaining obligations. Use `hy (Pi.single i 1) ⟨fun j _ => by` as an intermediate fact.

Distinguish the cases in `hj : j = i`. Substitute `hj` using the available equality. Rewrite using `[Pi.single_eq_same]`. Conclude with `one_mem _`. Rewrite using `[Pi.single_eq_of_ne hj]; exact zero_mem _, by`.

Rewrite using `[Pi.single_eq_of_ne (Ne.symm hi), mul_zero]`. Conclude with `zero_mem _⟩`. Rewrite `this` using `[Finset.sum_eq_single i]`. Rewrite `this` using `[Pi.single_eq_same, map_one, one_mul]`. Then use the resulting hypothesis. Introduce `j _ hj`.

Rewrite using `[Pi.single_eq_of_ne hj, map_zero, zero_mul]`. Introduce `h`. Conclude with `absurd (Finset.mem_univ _) h`. Use `hy (Pi.single (lastIdx n) (p : E)) ⟨fun j hj => by` as an intermediate fact. Rewrite using `[Pi.single_eq_of_ne hj]; exact zero_mem _, by`.

Rewrite using `[Pi.single_eq_same, inv_mul_cancel₀ hp]`. Conclude with `one_mem _⟩`. Rewrite `this` using `[Finset.sum_eq_single (lastIdx n)]`. Rewrite using `[Pi.single_eq_same] at this show (q : E) * y (lastIdx n) ∈ intOE E`. Rewrite using `[hq]`.

Conclude with `this`. Introduce `j _ hj`. Rewrite using `[Pi.single_eq_of_ne hj, map_zero, zero_mul]`. Introduce `h`. Conclude with `absurd (Finset.mem_univ _) h`.

Introduce and unpack `⟨h1, h2⟩ x ⟨hx1, hx2⟩`. Use `sum_mem fun i _ => ?_` and prove the remaining obligations. Distinguish the cases in `hi : i = lastIdx n`. Substitute `hi` using the available equality. Establish `hl : x (lastIdx n) = (p : E) * ((p : E)⁻¹ * x (lastIdx n))`.

Rewrite using `[mul_inv_cancel_left₀ hp]`. Rewrite using `[hl, map_mul, mul_comm ((σ : E →+* E) (p : E)), mul_assoc]`. Use `mul_mem (uLocDual_intOE_map _ hx2) ?_` and prove the remaining obligations. Establish `: (σ : E →+* E) (p : E) = (q : E)` using `by rw [hq]; rfl`. Rewrite using `[this]`.

Conclude with `h2`. Conclude with `mul_mem (uLocDual_intOE_map _ (hx1 i hi)) (h1 i hi)`. Rewrite using `[e, Submodule.span_eq]`.
-/
theorem uLocDual_eq : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (_ : ∀ x, σ (σ x) = x) (n : ℕ) [NeZero n] (p q : 𝓞 E) (_ : (p : E) ≠ 0) (_ : (q : E) = σ (p : E)),
    Submodule.span (𝓞 E) (dualSet (σ : E →+* E) (1 : Matrix (Fin n) (Fin n) E) (rll_dLat n ((p : E)⁻¹))) = rll_dLat n (q : E) := by
  intro F E _ _ _ _ _ σ _ n _ p q hp hq
  have e : dualSet (σ : E →+* E) (1 : Matrix (Fin n) (Fin n) E) (rll_dLat n ((p : E)⁻¹)) =
      (rll_dLat n (q : E) : Set (Fin n → E)) := by
    ext y
    rw [SetLike.mem_coe, rll_mem_dLat]
    show (∀ x ∈ rll_dLat n ((p : E)⁻¹), Formalism.UG.hform (σ : E →+* E) 1 x y ∈ (algebraMap (𝓞 E) E).range) ↔ _
    simp only [uLocDual_hform_one]
    constructor
    · intro hy
      refine ⟨fun i hi => ?_, ?_⟩
      · have := hy (Pi.single i 1) ⟨fun j _ => by
          by_cases hj : j = i
          · subst hj; rw [Pi.single_eq_same]; exact one_mem _
          · rw [Pi.single_eq_of_ne hj]; exact zero_mem _, by
          rw [Pi.single_eq_of_ne (Ne.symm hi), mul_zero]; exact zero_mem _⟩
        rw [Finset.sum_eq_single i] at this
        · rwa [Pi.single_eq_same, map_one, one_mul] at this
        · intro j _ hj; rw [Pi.single_eq_of_ne hj, map_zero, zero_mul]
        · intro h; exact absurd (Finset.mem_univ _) h
      · have := hy (Pi.single (lastIdx n) (p : E)) ⟨fun j hj => by
          rw [Pi.single_eq_of_ne hj]; exact zero_mem _, by
          rw [Pi.single_eq_same, inv_mul_cancel₀ hp]; exact one_mem _⟩
        rw [Finset.sum_eq_single (lastIdx n)] at this
        · rw [Pi.single_eq_same] at this
          show (q : E) * y (lastIdx n) ∈ intOE E
          rw [hq]; exact this
        · intro j _ hj; rw [Pi.single_eq_of_ne hj, map_zero, zero_mul]
        · intro h; exact absurd (Finset.mem_univ _) h
    · rintro ⟨h1, h2⟩ x ⟨hx1, hx2⟩
      refine sum_mem fun i _ => ?_
      by_cases hi : i = lastIdx n
      · subst hi
        have hl : x (lastIdx n) = (p : E) * ((p : E)⁻¹ * x (lastIdx n)) := by
          rw [mul_inv_cancel_left₀ hp]
        rw [hl, map_mul, mul_comm ((σ : E →+* E) (p : E)), mul_assoc]
        refine mul_mem (uLocDual_intOE_map _ hx2) ?_
        have : (σ : E →+* E) (p : E) = (q : E) := by rw [hq]; rfl
        rw [this]; exact h2
      · exact mul_mem (uLocDual_intOE_map _ (hx1 i hi)) (h1 i hi)
  rw [e, Submodule.span_eq]

end GlobalTheory

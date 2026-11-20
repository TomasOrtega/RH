import Formalism.WachLatticeTwists.CoprimeLiftBounds.Statement
import Formalism.CharacterColumnKernels.IdempotentNormalForms.ColKerChiOne

open Finset

noncomputable section

namespace Formalism.RepresentationBoundsCohomology.BR

open Formalism.NG Formalism.NG.ColumnGeneratorDecomposition Formalism.NG.ColKerChi

/- English proof (translation)
Introduce `A T' G _ _ _ _ M _ _ r χ E e₁ δ ι _ D j Kc k0 φ l`. Establish `hR : ∀ z ∈ colRelJ r χ E e₁ δ D j Kc k0, φ (Submodule.Quotient.mk z) = 0` using `fun z hz => by`. Rewrite using `[(Submodule.Quotient.mk_eq_zero _).mpr hz, map_zero]`. Establish `hsing : ∀ (x : A) (v : A × (Fin (j l) → A) × A), x • Pi.single (M` using `fun l => A × (Fin (j l) → A) × A) l v = Pi.single l (x • v) := by`. Introduce `x v`.

Use function extensionality and compare the values at `k`. Distinguish the cases in `h : k = l`. Substitute `h` using the available equality. Simplify using the standard rewrite rules. Simplify using `[Pi.single_eq_of_ne h]`.

Establish `hsing2 : ∀ (x : A) (a : Fin (j l)) (t : A), x • (Pi.single a t : Fin (j l) → A) = Pi.single a (x * t)`. Introduce `x a t`. Use function extensionality and compare the values at `k`. Distinguish the cases in `h : k = a`. Substitute `h` using the available equality.

Simplify using the standard rewrite rules. Simplify using `[Pi.single_eq_of_ne h]`. Establish `hgen : ∀ (x c : A) (s : Fin (j l) → A) (c₀ : A), x • (colGenJ (0 : Ymod r χ E) l c s c₀ : ColFreeJ A r χ E ι j) = colGenJ 0 l (x * c) (x • s) (x * c₀)`. Introduce `x c s c₀`. Use `show (x • (0 : Ymod r χ E), x • Pi.single (M := fun l => A × (Fin (j l) → A) × A) l (c, s, c₀)) = ((0 : Ymod r χ E), Pi.single (M := fun l => A × (Fin (j l) → A) × A) l (x * c, x • s, x * c₀))`.

Rewrite using `[smul_zero, hsing]`. Both sides reduce to the same expression. Use `⟨?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[← map_smul] show φ (E • Submodule.Quotient.mk ((colGenJ (0 : Ymod r χ E) l 1 0 0 : ColFreeJ A r χ E ι j))) = 0`. Rewrite using `[← Submodule.Quotient.mk_smul, hgen, mul_one, smul_zero, mul_zero]`.

Conclude with `hR _ (Submodule.subset_span (Or.inl (Or.inl (Or.inl ⟨l, rfl⟩))))`. Introduce `a`. Establish `hz` using `hR (colGenJ (0 : Ymod r χ E) l 0 (Pi.single a (1 - e₁)) 0) (Submodule.subset_span (Or.inl (Or.inl (Or.inr ⟨l, a, rfl⟩))))`. Establish `e : (colGenJ (0 : Ymod r χ E) l 0 (Pi.single a (1 - e₁)) 0 : ColFreeJ A r χ E ι j) = (1 - e₁) • colGenJ (0 : Ymod r χ E) l 0 (Pi.single a 1) 0`. Rewrite using `[hgen, mul_zero, hsing2, mul_one]`.

Rewrite `hz` using `[e, Submodule.Quotient.mk_smul, map_smul, sub_smul, one_smul, sub_eq_zero]`. Conclude with `hz.symm`. Establish `hz` using `hR (colGenJ (0 : Ymod r χ E) l 0 0 (algebraMap T' A δ - E)) (Submodule.subset_span (Or.inl (Or.inr ⟨l, rfl⟩)))`. Establish `e : (colGenJ (0 : Ymod r χ E) l 0 0 (algebraMap T' A δ - E) : ColFreeJ A r χ E ι j) = (algebraMap T' A δ - E) • (colGenJ (0 : Ymod r χ E) l 0 0 1 : ColFreeJ A r χ E ι j)`. Rewrite using `[hgen, mul_zero, smul_zero, mul_one]`.

Rewrite `hz` using `[e, Submodule.Quotient.mk_smul, map_smul, sub_smul, sub_eq_zero]`. Conclude with `hz`. Introduce `g hg`. Establish `hz` using `hR (colGenJ (⟨ycoc r χ E g, Submodule.subset_span ⟨g, rfl⟩⟩ : Ymod r χ E) l ((((χ g)⁻¹ : T'ˣ) : T') • r g - 1) (fun a => -(algebraMap T' A δ * Kc l a g)) (-(algebraMap T' A δ * k0 l g))) (Submodule.subset_span (Or.inr ⟨l, g, hg, rfl⟩))`. Establish `key : (colGenJ (⟨ycoc r χ E g, Submodule.subset_span ⟨g, rfl⟩⟩ : Ymod r χ E) l ((((χ g)⁻¹ : T'ˣ) : T') • r g - 1) (fun a => -(algebraMap T' A δ * Kc l a g)) (-(algebraMap T' A δ * k0 l g)) : ColFreeJ A r χ E ι j) = ((⟨ycoc r χ E g, Submodule.subset_span ⟨g, rfl⟩⟩ : Ymod r χ E), 0 …`.

Simplify using `only [hgen, hsing2, mul_one, mul_zero, smul_zero]`. Use `Prod.ext ?_ ?_` and prove the remaining obligations. Simplify using `[colGenJ, Prod.fst_sum]`. Use function extensionality and compare the values at `k`. Distinguish the cases in `hk : k = l`.

Substitute `hk` using the available equality. Simplify using `[colGenJ, Prod.snd_sum, Finset.sum_apply, funext_iff, Pi.single_apply]`. Use `Prod.ext ?_ (Prod.ext ?_ ?_)` and prove the remaining obligations. Simplify using `[Prod.fst_sum]`. Use function extensionality and compare the values at `a`.

Simplify using `[Prod.snd_sum, Prod.fst_sum, Finset.sum_apply, Pi.single_apply]`. Simplify using `[Prod.snd_sum]`. Simplify using `[colGenJ, Prod.snd_sum, Finset.sum_apply, Pi.single_eq_of_ne hk]`. Rewrite `hz` using `[key]`. Simplify using `only [← Submodule.mkQ_apply, map_add, map_smul, map_sum] at hz`.

Establish `hz' : φ (yGen r χ E e₁ δ D j Kc k0 g) + ((uElt r χ g - 1) • φ (nuGen r χ E e₁ δ D j Kc k0 l) + (∑ a, (-(algebraMap T' A δ * Kc l a g)) • φ (sigGen r χ E e₁ δ D j Kc k0 l a) + (-(algebraMap T' A δ * k0 l g)) • φ (sigmaZeroColumnGenerator r χ E e₁ δ D j Kc k0 l))) = 0` using `hz`. Simplify using `only [sub_smul, one_smul, neg_smul, mul_smul, Finset.sum_neg_distrib, ← Finset.smul_sum] at hz'`. Rewrite using `[smul_add, ← sub_eq_zero, ← hz']`. Normalize the expressions using the abelian group laws.
-/
theorem rel : StatRel := by
  intro A T' G _ _ _ _ M _ _ r χ E e₁ δ ι _ D j Kc k0 φ l
  have hR : ∀ z ∈ colRelJ r χ E e₁ δ D j Kc k0, φ (Submodule.Quotient.mk z) = 0 := fun z hz => by
    rw [(Submodule.Quotient.mk_eq_zero _).mpr hz, map_zero]
  have hsing : ∀ (x : A) (v : A × (Fin (j l) → A) × A),
      x • Pi.single (M := fun l => A × (Fin (j l) → A) × A) l v = Pi.single l (x • v) := by
    intro x v
    funext k
    by_cases h : k = l
    · subst h
      simp
    · simp [Pi.single_eq_of_ne h]
  have hsing2 : ∀ (x : A) (a : Fin (j l)) (t : A),
      x • (Pi.single a t : Fin (j l) → A) = Pi.single a (x * t) := by
    intro x a t
    funext k
    by_cases h : k = a
    · subst h
      simp
    · simp [Pi.single_eq_of_ne h]
  have hgen : ∀ (x c : A) (s : Fin (j l) → A) (c₀ : A),
      x • (colGenJ (0 : Ymod r χ E) l c s c₀ : ColFreeJ A r χ E ι j) =
        colGenJ 0 l (x * c) (x • s) (x * c₀) := by
    intro x c s c₀
    show (x • (0 : Ymod r χ E), x • Pi.single (M := fun l => A × (Fin (j l) → A) × A) l (c, s, c₀)) =
      ((0 : Ymod r χ E), Pi.single (M := fun l => A × (Fin (j l) → A) × A) l (x * c, x • s, x * c₀))
    rw [smul_zero, hsing]
    rfl
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← map_smul]
    show φ (E • Submodule.Quotient.mk ((colGenJ (0 : Ymod r χ E) l 1 0 0 : ColFreeJ A r χ E ι j))) = 0
    rw [← Submodule.Quotient.mk_smul, hgen, mul_one, smul_zero, mul_zero]
    exact hR _ (Submodule.subset_span (Or.inl (Or.inl (Or.inl ⟨l, rfl⟩))))
  · intro a
    have hz := hR (colGenJ (0 : Ymod r χ E) l 0 (Pi.single a (1 - e₁)) 0)
      (Submodule.subset_span (Or.inl (Or.inl (Or.inr ⟨l, a, rfl⟩))))
    have e : (colGenJ (0 : Ymod r χ E) l 0 (Pi.single a (1 - e₁)) 0 : ColFreeJ A r χ E ι j) =
        (1 - e₁) • colGenJ (0 : Ymod r χ E) l 0 (Pi.single a 1) 0 := by
      rw [hgen, mul_zero, hsing2, mul_one]
    rw [e, Submodule.Quotient.mk_smul, map_smul, sub_smul, one_smul, sub_eq_zero] at hz
    exact hz.symm
  · have hz := hR (colGenJ (0 : Ymod r χ E) l 0 0 (algebraMap T' A δ - E))
      (Submodule.subset_span (Or.inl (Or.inr ⟨l, rfl⟩)))
    have e : (colGenJ (0 : Ymod r χ E) l 0 0 (algebraMap T' A δ - E) : ColFreeJ A r χ E ι j) =
        (algebraMap T' A δ - E) • (colGenJ (0 : Ymod r χ E) l 0 0 1 : ColFreeJ A r χ E ι j) := by
      rw [hgen, mul_zero, smul_zero, mul_one]
    rw [e, Submodule.Quotient.mk_smul, map_smul, sub_smul, sub_eq_zero] at hz
    exact hz
  · intro g hg
    have hz := hR (colGenJ (⟨ycoc r χ E g, Submodule.subset_span ⟨g, rfl⟩⟩ : Ymod r χ E) l
        ((((χ g)⁻¹ : T'ˣ) : T') • r g - 1) (fun a => -(algebraMap T' A δ * Kc l a g))
        (-(algebraMap T' A δ * k0 l g)))
      (Submodule.subset_span (Or.inr ⟨l, g, hg, rfl⟩))
    have key : (colGenJ (⟨ycoc r χ E g, Submodule.subset_span ⟨g, rfl⟩⟩ : Ymod r χ E) l
        ((((χ g)⁻¹ : T'ˣ) : T') • r g - 1) (fun a => -(algebraMap T' A δ * Kc l a g))
        (-(algebraMap T' A δ * k0 l g)) : ColFreeJ A r χ E ι j) =
        ((⟨ycoc r χ E g, Submodule.subset_span ⟨g, rfl⟩⟩ : Ymod r χ E), 0) +
          (((((χ g)⁻¹ : T'ˣ) : T') • r g - 1) • (colGenJ (0 : Ymod r χ E) l 1 0 0 : ColFreeJ A r χ E ι j) +
          (∑ a, (-(algebraMap T' A δ * Kc l a g)) • colGenJ (0 : Ymod r χ E) l 0 (Pi.single a 1) 0 +
          (-(algebraMap T' A δ * k0 l g)) • (colGenJ (0 : Ymod r χ E) l 0 0 1 : ColFreeJ A r χ E ι j))) := by
      simp only [hgen, hsing2, mul_one, mul_zero, smul_zero]
      refine Prod.ext ?_ ?_
      · simp [colGenJ, Prod.fst_sum]
      · funext k
        by_cases hk : k = l
        · subst hk
          simp [colGenJ, Prod.snd_sum, Finset.sum_apply, funext_iff, Pi.single_apply]
          refine Prod.ext ?_ (Prod.ext ?_ ?_)
          · simp [Prod.fst_sum]
          · funext a
            simp [Prod.snd_sum, Prod.fst_sum, Finset.sum_apply, Pi.single_apply]
          · simp [Prod.snd_sum]
        · simp [colGenJ, Prod.snd_sum, Finset.sum_apply, Pi.single_eq_of_ne hk]
    rw [key] at hz
    simp only [← Submodule.mkQ_apply, map_add, map_smul, map_sum] at hz
    have hz' : φ (yGen r χ E e₁ δ D j Kc k0 g) + ((uElt r χ g - 1) • φ (nuGen r χ E e₁ δ D j Kc k0 l) +
        (∑ a, (-(algebraMap T' A δ * Kc l a g)) • φ (sigGen r χ E e₁ δ D j Kc k0 l a) +
        (-(algebraMap T' A δ * k0 l g)) • φ (sigmaZeroColumnGenerator r χ E e₁ δ D j Kc k0 l))) = 0 := hz
    simp only [sub_smul, one_smul, neg_smul, mul_smul, Finset.sum_neg_distrib,
      ← Finset.smul_sum] at hz'
    rw [smul_add, ← sub_eq_zero, ← hz']
    abel

end Formalism.RepresentationBoundsCohomology.BR

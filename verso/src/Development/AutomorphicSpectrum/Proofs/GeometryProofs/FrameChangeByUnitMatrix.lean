import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.CoordTieCompEquiv

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.FlagBun

open AlgebraicGeometry CategoryTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.FlagBun

/- English proof (translation)
Set `P' : Matrix (Fin r) (Fin r) R` to `fun a b => ⟨P a b, hP a b⟩`. Establish `hPP : P = (R.subtype).mapMatrix P'`. Use extensionality with `a b`. Both sides reduce to the same expression. Rewrite using `[hPP, ← RingHom.map_adjugate]`.

Conclude with `(P'.adjugate i j).2`.
-/
theorem adjugate_entry_mem {Ω : Type} [Field Ω] (R : Subring Ω) {r : ℕ}
    (P : Matrix (Fin r) (Fin r) Ω) (hP : ∀ a b, P a b ∈ R) (i j : Fin r) :
    P.adjugate i j ∈ R := by
  let P' : Matrix (Fin r) (Fin r) R := fun a b => ⟨P a b, hP a b⟩
  have hPP : P = (R.subtype).mapMatrix P' := by
    ext a b
    rfl
  rw [hPP, ← RingHom.map_adjugate]
  exact (P'.adjugate i j).2

/- English proof (translation)
Rewrite `hβ`, the goal using `[Fintype.linearIndependent_iff]`. Introduce `g hg`. Establish `h1 : ∀ a, ∑ k, P a k * g k = 0`. Apply `hβ` to reduce the goal to its premises. Use `Eq.trans ?_ hg` and prove the remaining obligations.

Simplify using `only [Finset.smul_sum, Finset.sum_smul, smul_smul]`. Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun k _ => ?_` and prove the remaining obligations. Rewrite using `[mul_comm]`. Establish `h2 : Matrix.mulVec P g = 0`.

Use function extensionality and compare the values at `a`. Conclude with `h1 a`. Establish `h3` using `Matrix.eq_zero_of_mulVec_eq_zero hd h2`. Introduce `i`. Rewrite using `[h3]`.

Both sides reduce to the same expression.
-/
theorem linearIndependent_matrix_comb {Ω : Type} [Field Ω] {E : Type} [AddCommGroup E] [Module Ω E] {r : ℕ}
    {β : Fin r → E} (hβ : LinearIndependent Ω β) (P : Matrix (Fin r) (Fin r) Ω) (hd : P.det ≠ 0) :
    LinearIndependent Ω (fun k => ∑ a, P a k • β a) := by
  rw [Fintype.linearIndependent_iff] at hβ ⊢
  intro g hg
  have h1 : ∀ a, ∑ k, P a k * g k = 0 := by
    apply hβ
    refine Eq.trans ?_ hg
    simp only [Finset.smul_sum, Finset.sum_smul, smul_smul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun k _ => ?_
    rw [mul_comm]
  have h2 : Matrix.mulVec P g = 0 := by
    funext a
    exact h1 a
  have h3 := Matrix.eq_zero_of_mulVec_eq_zero hd h2
  intro i
  rw [h3]
  rfl

/- English proof (translation)
Apply `le_antisymm` to reduce the goal to its premises. Rewrite using `[Submodule.span_le, Set.range_subset_iff]`. Introduce `k`. Use `show ∑ a, P a k • β a ∈ Submodule.span R (Set.range β)`. Use `sum_mem fun a _ => ?_` and prove the remaining obligations.

Conclude with `Submodule.smul_mem _ (⟨P a k, hP a k⟩ : R) (Submodule.subset_span ⟨a, rfl⟩)`. Rewrite using `[Submodule.span_le, Set.range_subset_iff]`. Introduce `b`. Use `show β b ∈ Submodule.span R (Set.range fun k => ∑ a, P a k • β a)`. Establish `hm : ∀ a, ∑ k, P a k * P.adjugate k b = (P * P.adjugate) a b` using `fun a => (Matrix.mul_apply).symm`.

Establish `hdet : ∑ k, P.adjugate k b • ∑ a, P a k • β a = P.det • β b`. Combine the equalities or inequalities in the displayed calculation. Simplify using `only [Finset.smul_sum, smul_smul, Finset.sum_smul]`. Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun k _ => ?_` and prove the remaining obligations.

Rewrite using `[mul_comm]`. Use `_ = ∑ a, (P * P.adjugate) a b • β a := by`. Simplify using `only [hm]`. Use `_ = P.det • β b := by`. Rewrite using `[Matrix.mul_adjugate]`.

Simplify using `[Matrix.one_apply]`. Establish `key : β b = ∑ k, (P.det⁻¹ * P.adjugate k b) • ∑ a, P a k • β a`. Simplify using `only [← smul_smul, ← Finset.smul_sum]`. Rewrite using `[hdet, smul_smul, inv_mul_cancel₀ hd, one_smul]`. Rewrite using `[key]`.

Use `sum_mem fun k _ => ?_` and prove the remaining obligations. Conclude with `Submodule.smul_mem _ (⟨P.det⁻¹ * P.adjugate k b, R.mul_mem hdi (adjugate_entry_mem R P hP k b)⟩ : R) (Submodule.subset_span ⟨k, rfl⟩)`.
-/
theorem span_matrix_comb {Ω : Type} [Field Ω] {E : Type} [AddCommGroup E] [Module Ω E] (R : Subring Ω) {r : ℕ}
    (β : Fin r → E) (P : Matrix (Fin r) (Fin r) Ω) (hP : ∀ a b, P a b ∈ R) (hd : P.det ≠ 0)
    (hdi : P.det⁻¹ ∈ R) :
    Submodule.span R (Set.range fun k => ∑ a, P a k • β a) = Submodule.span R (Set.range β) := by
  apply le_antisymm
  · rw [Submodule.span_le, Set.range_subset_iff]
    intro k
    show ∑ a, P a k • β a ∈ Submodule.span R (Set.range β)
    refine sum_mem fun a _ => ?_
    exact Submodule.smul_mem _ (⟨P a k, hP a k⟩ : R) (Submodule.subset_span ⟨a, rfl⟩)
  · rw [Submodule.span_le, Set.range_subset_iff]
    intro b
    show β b ∈ Submodule.span R (Set.range fun k => ∑ a, P a k • β a)
    have hm : ∀ a, ∑ k, P a k * P.adjugate k b = (P * P.adjugate) a b := fun a =>
      (Matrix.mul_apply).symm
    have hdet : ∑ k, P.adjugate k b • ∑ a, P a k • β a = P.det • β b := by
      calc ∑ k, P.adjugate k b • ∑ a, P a k • β a
          = ∑ a, (∑ k, P a k * P.adjugate k b) • β a := by
            simp only [Finset.smul_sum, smul_smul, Finset.sum_smul]
            rw [Finset.sum_comm]
            refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun k _ => ?_
            rw [mul_comm]
        _ = ∑ a, (P * P.adjugate) a b • β a := by
            simp only [hm]
        _ = P.det • β b := by
            rw [Matrix.mul_adjugate]
            simp [Matrix.one_apply]
    have key : β b = ∑ k, (P.det⁻¹ * P.adjugate k b) • ∑ a, P a k • β a := by
      simp only [← smul_smul, ← Finset.smul_sum]
      rw [hdet, smul_smul, inv_mul_cancel₀ hd, one_smul]
    rw [key]
    refine sum_mem fun k _ => ?_
    exact Submodule.smul_mem _
      (⟨P.det⁻¹ * P.adjugate k b, R.mul_mem hdi (adjugate_entry_mem R P hP k b)⟩ : R)
      (Submodule.subset_span ⟨k, rfl⟩)

/- English proof (translation)
Introduce `X Ω _ ξ E _ _ L r β q P h1 h2 h3`. Take `⟨hli, hspan⟩` from `h1`. Take `⟨hne, -, hinv⟩` from `h3`. Use `show LinearIndependent Ω (fun k => ∑ a, P a k • β a) ∧ L q = Submodule.span (regAt ξ q) (Set.range fun k => ∑ a, P a k • β a)`. Use `⟨linearIndependent_matrix_comb hli P hne, ?_⟩` and prove the remaining obligations.

Rewrite using `[hspan]`. Conclude with `(span_matrix_comb (regAt ξ q) β P h2 hne hinv).symm`.
-/
theorem isFrameAt_matrix_comb : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (E : Type)
    [AddCommGroup E] [Module Ω E] (L : Lat ξ E) (r : ℕ) (β : Fin r → E) (q : Cpt ξ)
    (P : Matrix (Fin r) (Fin r) Ω), L.IsFrameAt β q → (∀ a b, P a b ∈ regAt ξ q) → unitAt ξ q P.det →
    L.IsFrameAt (fun k => ∑ a, P a k • β a) q := by
  intro X Ω _ ξ E _ _ L r β q P h1 h2 h3
  obtain ⟨hli, hspan⟩ := h1
  obtain ⟨hne, -, hinv⟩ := h3
  show LinearIndependent Ω (fun k => ∑ a, P a k • β a) ∧
    L q = Submodule.span (regAt ξ q) (Set.range fun k => ∑ a, P a k • β a)
  refine ⟨linearIndependent_matrix_comb hli P hne, ?_⟩
  rw [hspan]
  exact (span_matrix_comb (regAt ξ q) β P h2 hne hinv).symm

end GlobalTheory.CompanionTheory.Ar.FlagBun

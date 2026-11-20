import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.GlobalTheta.HermitianHassePrincipleHolds
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsZeroCoordNeZero
import Development.AbelianVarietyTheory.Proofs.HermitianTraceForms.PosIndexMapEqCardOfCongrDiagonal
import Development.AbelianVarietyTheory.Proofs.HermitianTraceForms.ExistsOrthogonalBasisDotProductApplyEq

open Matrix NumberField
open scoped ComplexConjugate

namespace PositivityTheory.Rg.Sw.Glob.WLt

open ReciprocityTheory.ChartRestriction.G

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

/- English proof (translation)
The claim follows from `IsCMField.complexConj_apply_apply E t`.
-/
theorem cc_cc (t : E) : FD.cc (FD.cc t) = t := IsCMField.complexConj_apply_apply E t

/- English proof (translation)
The claim follows from `IsCMField.complexEmbedding_complexConj E τ t`.
-/
theorem emb_cc (τ : E →+* ℂ) (t : E) : τ (FD.cc t) = conj (τ t) := IsCMField.complexEmbedding_complexConj E τ t

/- English proof (translation)
Assume the negation of the conclusion as `hne`. Use `push Not at hne`. Apply `IsCMField.complexConj_ne_one E` to reduce the goal to its premises. Use extensionality with `t`. Assume the negation of the conclusion as `ht`.

Establish `h1 : t - FD.cc t ≠ 0` using `sub_ne_zero.mpr (Ne.symm ht)`. Apply `hne _ h1` to reduce the goal to its premises. Use `show IsCMField.complexConj E (t - FD.cc t) = -(t - FD.cc t)`. Rewrite using `[map_sub]`. Express the relevant statement in the definitionally equal form `FD.cc t - FD.cc (FD.cc t) = _`.

Rewrite using `[cc_cc]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem exists_skew : ∃ θ : E, θ ≠ 0 ∧ FD.cc θ = -θ := by
  by_contra hne
  push Not at hne
  apply IsCMField.complexConj_ne_one E
  ext t
  by_contra ht
  have h1 : t - FD.cc t ≠ 0 := sub_ne_zero.mpr (Ne.symm ht)
  apply hne _ h1
  show IsCMField.complexConj E (t - FD.cc t) = -(t - FD.cc t)
  rw [map_sub]
  change FD.cc t - FD.cc (FD.cc t) = _
  rw [cc_cc]
  ring

/- English proof (translation)
Establish `h` using `emb_cc τ t`. Rewrite `h` using `[ht]`. Apply `Complex.ext` to reduce the goal to its premises. Simplify using the standard rewrite rules. Use `congrArg Complex.im h` as an intermediate fact.

Simplify using `only [Complex.conj_im] at this`. Simplify using `only [Complex.ofReal_im]`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem emb_real (τ : E →+* ℂ) {t : E} (ht : FD.cc t = t) : τ t = ((τ t).re : ℂ) := by
  have h := emb_cc τ t
  rw [ht] at h
  apply Complex.ext
  · simp
  · have := congrArg Complex.im h
    simp only [Complex.conj_im] at this
    simp only [Complex.ofReal_im]
    linarith

/- English proof (translation)
Take `⟨θ, hθ0, hθ⟩` from `exists_skew (E := E)`. Establish `hF : ∀ t : E, IsCMField.complexConj E t = t ↔ ∃ s : maximalRealSubfield E, algebraMap (maximalRealSubfield E) E s = t` using `fun t => (IsCMField.complexConj_eq_self_iff E t).trans ⟨fun h => ⟨⟨t, h⟩, rfl⟩, by rintro ⟨s, rfl⟩; exact s.2⟩`. Establish `hne : ∀ (τ : E →+* ℂ) (i : Fin (r + 1)), (τ (g i)).re ≠ 0`. Introduce `τ i h`. Establish `h1` using `emb_real τ (hg i)`.

Rewrite `h1` using `[h, Complex.ofReal_zero]`. Conclude with `hg0 i ((map_eq_zero τ).1 h1)`. Take `⟨z, hz⟩` from `GlobalTheory.HermGlobal.exists_represent (σ := IsCMField.complexConj E) (IsCMField.complexConj_apply_apply E) hF hθ0 hθ hr (g := fun i => g i.succ) (fun i => hg _) (fun i => hg0 _) (b := -g 0) (by show IsCMField.complexConj E (-g 0) = -g 0; rw [map_neg]; exact congrArg Neg.neg (h …`. Introduce `τ _`. Take `⟨⟨i, hi⟩, ⟨j, hj⟩⟩` from `hs τ`.

Establish `hb : (τ (-g 0)).re = -(τ (g 0)).re` using `by simp`. Break down `lt_or_gt_of_ne (hne τ 0) with h0 | h0` into its components or cases. Establish `hi0 : i ≠ 0` using `by rintro rfl; linarith`. Take `⟨i', rfl⟩` from `Fin.exists_succ_eq.mpr hi0`. Apply the tactic sequence `exact ⟨i', by simp only [hb]; constructor <;> intro _ <;> linarith⟩`.

Establish `hj0 : j ≠ 0` using `by rintro rfl; linarith`. Take `⟨j', rfl⟩` from `Fin.exists_succ_eq.mpr hj0`. Apply the tactic sequence `exact ⟨j', by simp only [hb]; constructor <;> intro h <;> linarith⟩)`. Use `⟨Fin.cons 1 z, fun h => one_ne_zero (congrFun h 0), ?_⟩` and prove the remaining obligations. Establish `key : (Fin.cons 1 z : Fin (r + 1) → E) ⬝ᵥ diagonal g *ᵥ (FD.cc ∘ Fin.cons 1 z) = g 0 + z ⬝ᵥ diagonal (fun i => g i.succ) *ᵥ (FD.cc ∘ z)`.

Simplify using `only [dotProduct, mulVec_diagonal, Fin.sum_univ_succ, Function.comp_apply, Fin.cons_zero, Fin.cons_succ]`. Establish `: FD.cc (1 : E) = 1` using `map_one (IsCMField.complexConj E)`. Rewrite using `[this]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[key]`.

Establish `hz' : z ⬝ᵥ diagonal (fun i => g i.succ) *ᵥ (FD.cc ∘ z) = -g 0` using `hz`. Rewrite using `[hz']`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem iso_diag {r : ℕ} (g : Fin (r + 1) → E) (hr : 2 ≤ r) (hg : ∀ i, FD.cc (g i) = g i) (hg0 : ∀ i, g i ≠ 0)
    (hs : ∀ τ : E →+* ℂ, (∃ i, 0 < (τ (g i)).re) ∧ (∃ j, (τ (g j)).re < 0)) :
    ∃ z : Fin (r + 1) → E, z ≠ 0 ∧ z ⬝ᵥ diagonal g *ᵥ (FD.cc ∘ z) = 0 := by
  obtain ⟨θ, hθ0, hθ⟩ := exists_skew (E := E)
  have hF : ∀ t : E, IsCMField.complexConj E t = t ↔ ∃ s : maximalRealSubfield E, algebraMap (maximalRealSubfield E) E s = t :=
    fun t => (IsCMField.complexConj_eq_self_iff E t).trans ⟨fun h => ⟨⟨t, h⟩, rfl⟩, by rintro ⟨s, rfl⟩; exact s.2⟩
  have hne : ∀ (τ : E →+* ℂ) (i : Fin (r + 1)), (τ (g i)).re ≠ 0 := by
    intro τ i h
    have h1 := emb_real τ (hg i)
    rw [h, Complex.ofReal_zero] at h1
    exact hg0 i ((map_eq_zero τ).1 h1)
  obtain ⟨z, hz⟩ := GlobalTheory.HermGlobal.exists_represent (σ := IsCMField.complexConj E) (IsCMField.complexConj_apply_apply E) hF
    hθ0 hθ hr (g := fun i => g i.succ) (fun i => hg _) (fun i => hg0 _) (b := -g 0)
    (by show IsCMField.complexConj E (-g 0) = -g 0; rw [map_neg]; exact congrArg Neg.neg (hg 0))
    (neg_ne_zero.mpr (hg0 0)) (by
      intro τ _
      obtain ⟨⟨i, hi⟩, ⟨j, hj⟩⟩ := hs τ
      have hb : (τ (-g 0)).re = -(τ (g 0)).re := by simp
      rcases lt_or_gt_of_ne (hne τ 0) with h0 | h0
      ·
        have hi0 : i ≠ 0 := by rintro rfl; linarith
        obtain ⟨i', rfl⟩ := Fin.exists_succ_eq.mpr hi0
        exact ⟨i', by simp only [hb]; constructor <;> intro _ <;> linarith⟩
      · have hj0 : j ≠ 0 := by rintro rfl; linarith
        obtain ⟨j', rfl⟩ := Fin.exists_succ_eq.mpr hj0
        exact ⟨j', by simp only [hb]; constructor <;> intro h <;> linarith⟩)
  refine ⟨Fin.cons 1 z, fun h => one_ne_zero (congrFun h 0), ?_⟩
  have key : (Fin.cons 1 z : Fin (r + 1) → E) ⬝ᵥ diagonal g *ᵥ (FD.cc ∘ Fin.cons 1 z) =
      g 0 + z ⬝ᵥ diagonal (fun i => g i.succ) *ᵥ (FD.cc ∘ z) := by
    simp only [dotProduct, mulVec_diagonal, Fin.sum_univ_succ, Function.comp_apply, Fin.cons_zero, Fin.cons_succ]
    have : FD.cc (1 : E) = 1 := map_one (IsCMField.complexConj E)
    rw [this]
    ring
  rw [key]
  have hz' : z ⬝ᵥ diagonal (fun i => g i.succ) *ᵥ (FD.cc ∘ z) = -g 0 := hz
  rw [hz']
  ring

end PositivityTheory.Rg.Sw.Glob.WLt

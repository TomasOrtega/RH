import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsDominantOfSection
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LinearFormAntisymmOfDoublePointSymmMultilinearStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InterPolyEqZeroOfIsHomogeneousNeDimStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIntersectionFormPicardDoubleSpaceStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntersectionNumberPullbackDimSuccDivisorsEqZeroStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NumConsEqMulOfEffectiveDivisorSuppSectionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DoubleSpaceSectionIntersectionNumberEqBaseStatement

open CategoryTheory AlgebraicGeometry TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZH GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.FlagPush
open Classical

namespace GlobalTheory.FlagPush.Dbl

/- English proof (translation)
Introduce `F _ Y W hW κ a b hab gr D₁ D₂ Θ ⟨h₁, h₂, hx, hsum, hΘ, hE, hS⟩`. Take `⟨T, hTs, hT⟩` from `GlobalTheory.T.exists_intersectionForm_picard_doubleSpace F Y W hW`. Take `⟨μ, hμ, hc⟩` from `GlobalTheory.T.num_cons_eq_mul_of_effective_divisor_supp_section F Y W hW Θ hE hS`. Set `N : AddSubgroup (CartierDiv W.Z)` to `(toPic (X := W.Z)).ker`. Set `π : CartierDiv W.Z →+ CartierDiv W.Z ⧸ N` to `QuotientAddGroup.mk' N`.

Set `φ : (CartierDiv W.Z ⧸ N) →+ Pic W.Z` to `QuotientAddGroup.kerLift toPic`. Establish `hφ : Function.Injective φ` using `QuotientAddGroup.kerLift_injective _`. Establish `hπ (D : CartierDiv W.Z) : φ (π D) = toPic D` using `rfl`. Set `T' : MultilinearMap ℤ (fun _ : Fin (Y.dim + 1) => CartierDiv W.Z ⧸ N) ℤ` to `T.compLinearMap fun _ => φ.toIntLinearMap`. Establish `hT' (y : Fin (Y.dim + 1) → CartierDiv W.Z) : T' (fun i => π (y i)) = W.num y` using `hT y`.

Use `GlobalTheory.T.linearForm_antisymm_of_doublePoint_symmMultilinear κ a b hab (CartierDiv W.Z ⧸ N) Y.dim T' (fun σ y => hTs σ fun i => φ (y i)) (fun x => π (D₁ x)) (fun x => π (D₂ x)) (Y.interPoly gr) μ hμ (fun x ha hb => hφ (hx x ha hb)) (hφ ?_) (fun s => ?_) (fun s => ?_) (fun k …` and prove the remaining obligations. Simplify `hsum` using `only [map_add, hπ]`. Conclude with `(hT' (fun i => D₁ (s i))).trans (GlobalTheory.T.intersectionNumber_pullback_dimSuccDivisors_eq_zero F Y W hW W.p₁ _ (fun i => gr (s i)) fun i => h₁ (s i))`. Conclude with `(hT' (fun i => D₂ (s i))).trans (GlobalTheory.T.intersectionNumber_pullback_dimSuccDivisors_eq_zero F Y W hW W.p₂ _ (fun i => gr (s i)) fun i => h₂ (s i))`. Establish `hΘ' : π (D₂ b) - π (D₁ a) = π Θ` using `hφ (by simp only [map_sub, hπ, hΘ])`.

Establish `e : (Fin.cons (π (D₂ b) - π (D₁ a)) (Sum.elim (fun x => π (D₁ x)) (fun x => π (D₂ x)) ∘ s) : Fin (Y.dim + 1) → CartierDiv W.Z ⧸ N) = fun i => π ((Fin.cons Θ (Sum.elim D₁ D₂ ∘ s) : Fin (Y.dim + 1) → CartierDiv W.Z) i)`. Use function extensionality and compare the values at `i`. Use `Fin.cases ?_ (fun j => ?_) i` and prove the remaining obligations. Simplify using `only [Fin.cons_zero, hΘ']`. Simplify using `only [Fin.cons_succ, Function.comp_apply]`.

Apply the tactic sequence `cases s j <;> rfl`. Establish `r` using `GlobalTheory.T.doubleSpace_section_intersectionNumber_eq_base F Y W (Sum.elim D₁ D₂ ∘ s) (gr ∘ fun i => Sum.elim id id (s i)) fun i => by`. Simplify using `only [Function.comp_apply]`. Consider the cases of `s i with`. Consider the case `inl x => exact Or.inl (h₁ x)`.

Consider the case `inr x => exact Or.inr (h₂ x)`. Rewrite using `[e, hT', hc, r, Var.interPoly_prod]`. Use `push_cast`. Both sides reduce to the same expression.
-/
theorem interPoly_rename_swap : ∀ (F : Type) [Field F] (Y : Var F) (W : Dbl Y), W.Small → ∀ (κ : Type) (a b : κ), a ≠ b → ∀ (gr : κ → Y.Dv) (D₁ D₂ : κ → CartierDiv W.Z) (Θ : CartierDiv W.Z), (∀ x, IsPull W.p₁ (D₁ x) (gr x)) ∧ (∀ x, IsPull W.p₂ (D₂ x) (gr x)) ∧ (∀ x, x ≠ a → x ≠ b → toPic (D₁ x) = toPic (D₂ x)) ∧ toPic (D₁ a) + toPic (D₁ b) = toPic (D₂ a) + toPic (D₂ b) ∧ toPic Θ = toPic (D₂ b) - toPic (D₁ a) ∧ Θ.Eff ∧ (Θ.supp : Set W.Z) = Set.range W.δ → ∀ Q : MvPolynomial κ ℝ, Y.interPoly gr (rename (Equiv.swap a b) Q) = - Y.interPoly gr Q := by
  intro F _ Y W hW κ a b hab gr D₁ D₂ Θ ⟨h₁, h₂, hx, hsum, hΘ, hE, hS⟩
  obtain ⟨T, hTs, hT⟩ := GlobalTheory.T.exists_intersectionForm_picard_doubleSpace F Y W hW
  obtain ⟨μ, hμ, hc⟩ := GlobalTheory.T.num_cons_eq_mul_of_effective_divisor_supp_section F Y W hW Θ hE hS
  let N : AddSubgroup (CartierDiv W.Z) := (toPic (X := W.Z)).ker
  let π : CartierDiv W.Z →+ CartierDiv W.Z ⧸ N := QuotientAddGroup.mk' N
  let φ : (CartierDiv W.Z ⧸ N) →+ Pic W.Z := QuotientAddGroup.kerLift toPic
  have hφ : Function.Injective φ := QuotientAddGroup.kerLift_injective _
  have hπ (D : CartierDiv W.Z) : φ (π D) = toPic D := rfl
  let T' : MultilinearMap ℤ (fun _ : Fin (Y.dim + 1) => CartierDiv W.Z ⧸ N) ℤ :=
    T.compLinearMap fun _ => φ.toIntLinearMap
  have hT' (y : Fin (Y.dim + 1) → CartierDiv W.Z) : T' (fun i => π (y i)) = W.num y := hT y
  refine GlobalTheory.T.linearForm_antisymm_of_doublePoint_symmMultilinear κ a b hab (CartierDiv W.Z ⧸ N) Y.dim T' (fun σ y => hTs σ fun i => φ (y i))
    (fun x => π (D₁ x)) (fun x => π (D₂ x))
    (Y.interPoly gr) μ hμ (fun x ha hb => hφ (hx x ha hb)) (hφ ?_) (fun s => ?_) (fun s => ?_)
    (fun k P hP hk => GlobalTheory.T.interPoly_eq_zero_of_isHomogeneous_ne_dim F Y κ gr k P hP hk) (fun s => ?_)
  · simpa only [map_add, hπ] using hsum
  · exact (hT' (fun i => D₁ (s i))).trans
      (GlobalTheory.T.intersectionNumber_pullback_dimSuccDivisors_eq_zero F Y W hW W.p₁ _ (fun i => gr (s i)) fun i => h₁ (s i))
  · exact (hT' (fun i => D₂ (s i))).trans
      (GlobalTheory.T.intersectionNumber_pullback_dimSuccDivisors_eq_zero F Y W hW W.p₂ _ (fun i => gr (s i)) fun i => h₂ (s i))
  · have hΘ' : π (D₂ b) - π (D₁ a) = π Θ := hφ (by simp only [map_sub, hπ, hΘ])
    have e : (Fin.cons (π (D₂ b) - π (D₁ a))
        (Sum.elim (fun x => π (D₁ x)) (fun x => π (D₂ x)) ∘ s) : Fin (Y.dim + 1) → CartierDiv W.Z ⧸ N) =
        fun i => π ((Fin.cons Θ (Sum.elim D₁ D₂ ∘ s) : Fin (Y.dim + 1) → CartierDiv W.Z) i) := by
      funext i
      refine Fin.cases ?_ (fun j => ?_) i
      · simp only [Fin.cons_zero, hΘ']
      · simp only [Fin.cons_succ, Function.comp_apply]
        cases s j <;> rfl
    have r := GlobalTheory.T.doubleSpace_section_intersectionNumber_eq_base F Y W (Sum.elim D₁ D₂ ∘ s) (gr ∘ fun i => Sum.elim id id (s i)) fun i => by
      simp only [Function.comp_apply]
      cases s i with
      | inl x => exact Or.inl (h₁ x)
      | inr x => exact Or.inr (h₂ x)
    rw [e, hT', hc, r, Var.interPoly_prod]
    push_cast
    rfl

end GlobalTheory.FlagPush.Dbl

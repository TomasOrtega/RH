import Mathlib
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.QuotientVanishing.NonEllFlag

noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.Tf.Loc
open PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.D4

namespace GlobalTheory.CompanionTheory.ChiGamGlobal

/- English proof (translation)
Establish `h : t⁻¹ * δ * θ t = δ` using `ht`. Combine the equalities or inequalities in the displayed calculation. Simplify using `only [twConj, map_mul, _root_.mul_inv_rev, mul_assoc]`. Use `_ = twConj θ x δ := by rw [h]; rfl`.
-/
theorem twConj_cent_mul {G : Type} [Group G] (θ : Monoid.End G) {t δ : G} (x : G) (ht : twConj θ t δ = δ) :
    twConj θ (t * x) δ = twConj θ x δ := by
  have h : t⁻¹ * δ * θ t = δ := ht
  calc twConj θ (t * x) δ = x⁻¹ * (t⁻¹ * δ * θ t) * θ x := by
        simp only [twConj, map_mul, _root_.mul_inv_rev, mul_assoc]
    _ = twConj θ x δ := by rw [h]; rfl

/- English proof (translation)
Establish `h : ∀ A : Matrix (Fin n) (Fin n) (Ad E), 0 ≤ logSizeM A` using `fun A => add_nonneg (Finset.sum_nonneg fun _ _ => Real.posLog_nonneg) (finsum_nonneg fun _ => Real.posLog_nonneg)`. Conclude with `add_nonneg (h _) (h _)`.
-/
theorem logSize_nonneg {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {n : ℕ} (g : GA E n) :
    0 ≤ logSize g := by
  have h : ∀ A : Matrix (Fin n) (Fin n) (Ad E), 0 ≤ logSizeM A := fun A =>
    add_nonneg (Finset.sum_nonneg fun _ _ => Real.posLog_nonneg)
      (finsum_nonneg fun _ => Real.posLog_nonneg)
  exact add_nonneg (h _) (h _)

/- English proof (translation)
Introduce `E _ _ _ n`. Take `⟨C₁, h₁⟩` from `hI E n`. Take `⟨C₂, h₂⟩` from `hP E n`. Use `⟨max C₁ C₂, fun d m Wof a hiso huniq h0 hmeet hle hreg hdeg τ x hτ t ht => ?_⟩` and prove the remaining obligations. Establish `hs : 0 ≤ 1 + logSize (twConj (thetaA E n) x (ratGL E n d))`.

Use `logSize_nonneg (twConj (thetaA E n) x (ratGL E n d))` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion. Establish `b₁` using `(mul_le_mul_of_nonneg_right (le_max_left C₁ C₂) hs).trans hτ`. Establish `b₂` using `(mul_le_mul_of_nonneg_right (le_max_right C₁ C₂) hs).trans hτ`. Establish `hconj : twConj (thetaA E n) (t * x) (ratGL E n d) = twConj (thetaA E n) x (ratGL E n d)` using `twConj_cent_mul _ x ht`.

Establish `hind` using `(hC m).1 _ (a t) (h₂ d m Wof hiso huniq h0 hmeet hle hreg τ x b₂)`. Establish `hiff : t * x ∈ cutSet E n τ ↔ ∀ e, sdot e (a t) ≤ prof n τ (Module.finrank E (Wof e)) - deg x (Wof e)`. Rewrite using `[h₁ τ (t * x) d (by rw [hconj]; exact b₁)]`. Prove the components needed by the constructor for the conclusion. Introduce `h e`.

Use `h (Wof e) (hiso e).1 (hiso e).2` as an intermediate fact. Rewrite `this` using `[hdeg t ht x e]`. Combine the linear equalities and inequalities to obtain the conclusion. Introduce `h W hW₁ hW₂`. Take `⟨e, rfl, _⟩` from `huniq W ⟨hW₁, hW₂⟩`.

Use `h e` as an intermediate fact. Rewrite using `[hdeg t ht x e]`. Combine the linear equalities and inequalities to obtain the conclusion. Rewrite using `[hind]`. Distinguish the cases in `hx : t * x ∈ cutSet E n τ`.

Establish `ha : a t ∈ {b : Fin m → ℝ | ∀ e, sdot e b ≤ prof n τ (Module.finrank E (Wof e)) - deg x (Wof e)}` using `hiff.1 hx`. Rewrite using `[Set.indicator_of_mem ha, chiT, Set.indicator_of_mem hx]`. Simplify using the standard rewrite rules. Establish `ha : a t ∉ {b : Fin m → ℝ | ∀ e, sdot e b ≤ prof n τ (Module.finrank E (Wof e)) - deg x (Wof e)}` using `fun h => hx (hiff.2 h)`. Rewrite using `[Set.indicator_of_notMem ha, chiT, Set.indicator_of_notMem hx]`.

Simplify using the standard rewrite rules.
-/
theorem chiGam_of (hI : OnlyIsotropic) (hP : PosY) (hC : ChainSum) : ChiGam := by
  classical
  intro E _ _ _ n
  obtain ⟨C₁, h₁⟩ := hI E n
  obtain ⟨C₂, h₂⟩ := hP E n
  refine ⟨max C₁ C₂, fun d m Wof a hiso huniq h0 hmeet hle hreg hdeg τ x hτ t ht => ?_⟩
  have hs : 0 ≤ 1 + logSize (twConj (thetaA E n) x (ratGL E n d)) := by
    have := logSize_nonneg (twConj (thetaA E n) x (ratGL E n d))
    linarith
  have b₁ := (mul_le_mul_of_nonneg_right (le_max_left C₁ C₂) hs).trans hτ
  have b₂ := (mul_le_mul_of_nonneg_right (le_max_right C₁ C₂) hs).trans hτ
  have hconj : twConj (thetaA E n) (t * x) (ratGL E n d) = twConj (thetaA E n) x (ratGL E n d) :=
    twConj_cent_mul _ x ht
  have hind := (hC m).1 _ (a t) (h₂ d m Wof hiso huniq h0 hmeet hle hreg τ x b₂)
  have hiff : t * x ∈ cutSet E n τ ↔
      ∀ e, sdot e (a t) ≤ prof n τ (Module.finrank E (Wof e)) - deg x (Wof e) := by
    rw [h₁ τ (t * x) d (by rw [hconj]; exact b₁)]
    constructor
    · intro h e
      have := h (Wof e) (hiso e).1 (hiso e).2
      rw [hdeg t ht x e] at this
      linarith
    · intro h W hW₁ hW₂
      obtain ⟨e, rfl, _⟩ := huniq W ⟨hW₁, hW₂⟩
      have := h e
      rw [hdeg t ht x e]
      linarith
  rw [hind]
  by_cases hx : t * x ∈ cutSet E n τ
  · have ha : a t ∈ {b : Fin m → ℝ | ∀ e, sdot e b ≤ prof n τ (Module.finrank E (Wof e)) - deg x (Wof e)} :=
      hiff.1 hx
    rw [Set.indicator_of_mem ha, chiT, Set.indicator_of_mem hx]
    simp
  · have ha : a t ∉ {b : Fin m → ℝ | ∀ e, sdot e b ≤ prof n τ (Module.finrank E (Wof e)) - deg x (Wof e)} :=
      fun h => hx (hiff.2 h)
    rw [Set.indicator_of_notMem ha, chiT, Set.indicator_of_notMem hx]
    simp

end GlobalTheory.CompanionTheory.ChiGamGlobal

end

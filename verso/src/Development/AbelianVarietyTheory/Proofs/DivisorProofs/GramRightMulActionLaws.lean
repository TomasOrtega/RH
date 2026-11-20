import Mathlib
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.ChainOfKernelsUnique
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsIsoIffBijectiveOverAlgClosed
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped NumberField CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

/- English proof (translation)
Introduce `S A K i hi hfin het d hd hcard`. Establish `h : (toUnit K).left = K.hom` using `by simpa using Over.w (toUnit K)`. Establish `hrank : ∀ s : S, K.hom.finrank s = d`. Introduce `s`. Take `⟨k, _, _, t, ht⟩` from `GlobalTheory.FinEt.exists_algClosed_point S s`.

Take `⟨z, rfl⟩ : s ∈ Set.range t` from `by rw [ht]; rfl`. Take `⟨-, hc⟩` from `GlobalTheory.FinEt.card_points_eq_finrank K.hom t z`. Rewrite using `[← hc, ← hcard k t]`. Use `Nat.card_congr (Equiv.ofBijective (fun x => ⟨Over.homMk x.1 x.2 ≫ i, ⟨Over.homMk x.1 x.2, rfl⟩⟩) ⟨?_, ?_⟩)` and prove the remaining obligations. Introduce and unpack `⟨a, ha⟩ ⟨b, hb⟩ hab`.

Use `(cancel_mono i).1 (congrArg Subtype.val hab)` as an intermediate fact. Conclude with `Subtype.ext (congrArg CommaMorphism.left this)`. Introduce and unpack `⟨y, y', hy'⟩`. Use `⟨⟨y'.left, Over.w y'⟩, Subtype.ext ?_⟩` and prove the remaining obligations. Simplify using `only`.

Rewrite using `[← hy']`. Use `congr 1`. Establish `hflat : Flat K.hom` using `inferInstance`. Use `⟨?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[h]`.

Conclude with `hfin`. Rewrite using `[h]`. Conclude with `hflat`. Rewrite using `[h]`. Conclude with `(Scheme.Hom.one_le_finrank_iff_surjective K.hom).1 fun s => (hrank s).symm ▸ hd`.

Introduce `y`. Rewrite using `[h]`. Conclude with `hrank y`.
-/
theorem GlobalTheory.FinEtRank.isIsogDeg_of_card :
  ∀ {S : Scheme.{0}} (A K : Over S) (i : K ⟶ A), Mono i → IsFinite K.hom → Etale K.hom → ∀ (d : ℕ), 1 ≤ d → (∀ (k : Type) [Field k] [IsAlgClosed k] (t : Sp k ⟶ S), Nat.card {y : Over.mk t ⟶ A // GlobalTheory.IwLevel.InSub i y} = d) → GlobalTheory.IwLevel.IsIsogDeg (toUnit K) d := by
  intro S A K i hi hfin het d hd hcard
  have h : (toUnit K).left = K.hom := by simpa using Over.w (toUnit K)
  have hrank : ∀ s : S, K.hom.finrank s = d := by
    intro s
    obtain ⟨k, _, _, t, ht⟩ := GlobalTheory.FinEt.exists_algClosed_point S s
    obtain ⟨z, rfl⟩ : s ∈ Set.range t := by rw [ht]; rfl
    obtain ⟨-, hc⟩ := GlobalTheory.FinEt.card_points_eq_finrank K.hom t z
    rw [← hc, ← hcard k t]
    refine Nat.card_congr (Equiv.ofBijective (fun x => ⟨Over.homMk x.1 x.2 ≫ i, ⟨Over.homMk x.1 x.2, rfl⟩⟩) ⟨?_, ?_⟩)
    · rintro ⟨a, ha⟩ ⟨b, hb⟩ hab
      have := (cancel_mono i).1 (congrArg Subtype.val hab)
      exact Subtype.ext (congrArg CommaMorphism.left this)
    · rintro ⟨y, y', hy'⟩
      refine ⟨⟨y'.left, Over.w y'⟩, Subtype.ext ?_⟩
      simp only
      rw [← hy']
      congr 1
  have hflat : Flat K.hom := inferInstance
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [h]; exact hfin
  · rw [h]; exact hflat
  · rw [h]; exact (Scheme.Hom.one_le_finrank_iff_surjective K.hom).1 fun s => (hrank s).symm ▸ hd
  · intro y; rw [h]; exact hrank y

import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MumfordSectionsMultiplierThickeningsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSectionNonvanishingClosedFibreOfThreeLeStatement
import Development.AbelianVarietyTheory.Definitions.Divisors.FormalEnd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SecRatioEqRefl
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordConstruction
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.MumSec

def zeroSec {X : Scheme.{0}} (L : LB X) : LB.Sec L where
  f := fun _ => 0
  compat := fun _ _ => by simp

/- English proof (translation)
Both sides reduce to the same expression.
-/
@[simp] lemma zeroSec_f {X : Scheme.{0}} (L : LB X) (i : L.ι) : (zeroSec L).f i = 0 := rfl

/- English proof (translation)
Introduce `R _ _ _ hB D A G _ _ hG U a a' h h' hE b hb`. Take `⟨N, hN, hP⟩` from `GlobalTheory.T.mumfordSections_multiplier_thickenings R hB D A G hG U a a' h h' hE b hb`. Set `S : ∀ k : ℕ, H0 U.LG.L k → H0 U.LG.L (N * k)` to `fun k => if hk : 3 ≤ k then (hP k hk).choose else fun _ => zeroSec _`. Use `⟨N, hN, S, ?_, ?_⟩` and prove the remaining obligations. Introduce `k e s₁ s₂ i i'`.

Distinguish the cases in `hk : 3 ≤ k`. Take `⟨c, hc, -⟩` from `(hP k hk).choose_spec`. Establish `e1` using `hc e s₁ i i'`. Establish `e2` using `hc e s₂ i i'`. Establish `hS : S k = (hP k hk).choose` using `dif_pos hk`.

Rewrite using `[hS, e1, e2]`. Expand and normalize the polynomial expressions, which then agree. Establish `hS : S k = fun _ => zeroSec _` using `dif_neg hk`. Rewrite using `[hS]`. Simplify using `only [zeroSec]`.

Use `erw [map_zero, map_zero]`. Simplify using `only [map_zero, mul_zero]`. Introduce `k hk`. Take `⟨c, hc, y, ⟨i', hi'⟩, hy⟩` from `(hP k hk).choose_spec`. Take `⟨s₀, i, hs⟩` from `GlobalTheory.T.exists_section_nonvanishing_closedFibre_of_three_le R hB D A G hG U k hk ((b 0).left.base y)`.

Establish `hu : y ∈ (thickObj R (maximalIdeal R) 0 G).left.basicOpen ((((b 0).left ≫ (fstG (maximalIdeal R) 0 G).left).app (secChart U.LG.L i)).hom (s₀.f i))`. Establish `h1 : y ∈ (b 0).left ⁻¹ᵁ (thickObj R (maximalIdeal R) 0 G).left.basicOpen (((fstG (maximalIdeal R) 0 G).left.app (secChart U.LG.L i)).hom (s₀.f i))` using `hs`. Rewrite `h1` using `[Scheme.preimage_basicOpen]`. Conclude with `h1`. Establish `hyW : y ∈ ((b 0).left ≫ (fstG (maximalIdeal R) 0 G).left) ⁻¹ᵁ secChart U.LG.L i ⊓ (fstG (maximalIdeal R) 0 G).left ⁻¹ᵁ secChart U.LG.L i'` using `⟨Scheme.basicOpen_le _ _ hu, hi'⟩`.

Establish `hS : S k = (hP k hk).choose` using `dif_pos hk`. Use `⟨s₀, y, i, i', hu, ?_⟩` and prove the remaining obligations. Rewrite using `[hS]`. Establish `key` using `hc 0 s₀ i i'`. Establish `hprod : y ∈ (thickObj R (maximalIdeal R) 0 G).left.basicOpen (c 0 i i' * ((thickObj R (maximalIdeal R) 0 G).left.presheaf.map (homOfLE (inf_le_left : ((b 0).left ≫ (fstG (maximalIdeal R) 0 G).left) ⁻¹ᵁ secChart U.LG.L i ⊓ (fstG (maximalIdeal R) 0 G).left ⁻¹ᵁ secChart U.LG.L i' ≤ …`.

Rewrite using `[Scheme.basicOpen_mul, Scheme.basicOpen_res]`. Conclude with `⟨hy i i' hyW, hyW, hu⟩`. Rewrite `hprod` using `[← key, Scheme.basicOpen_res]`. Conclude with `hprod.2`.
-/
theorem main : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ U : Unif (maximalIdeal R) D A G, ∀ (a a' : D.toPre.P.A ⟶ D.toPre.P.A) (h h' : D.toPre.X →+ D.toPre.X), EndData D.toPre a a' h h' → ∀ b, FormalEnd U.toUnifPre a h' b → ∃ N : ℕ, 1 ≤ N ∧ ∃ S : ∀ k : ℕ, H0 U.LG.L k → H0 U.LG.L (N * k), (∀ (k e : ℕ) (s₁ s₂ : H0 U.LG.L k), SecRatioEq U.LG.L ((b e).left ≫ (fstG (maximalIdeal R) e G).left) (fstG (maximalIdeal R) e G).left s₁ s₂ (S k s₁) (S k s₂)) ∧ (∀ k : ℕ, 3 ≤ k → ∃ s₀ : H0 U.LG.L k, SecCoNonzero U.LG.L ((b 0).left ≫ (fstG (maximalIdeal R) 0 G).left) (fstG (maximalIdeal R) 0 G).left s₀ (S k s₀)) := by
  intro R _ _ _ hB D A G _ _ hG U a a' h h' hE b hb
  obtain ⟨N, hN, hP⟩ := GlobalTheory.T.mumfordSections_multiplier_thickenings R hB D A G hG U a a' h h' hE b hb
  classical
  let S : ∀ k : ℕ, H0 U.LG.L k → H0 U.LG.L (N * k) := fun k =>
    if hk : 3 ≤ k then (hP k hk).choose else fun _ => zeroSec _
  refine ⟨N, hN, S, ?_, ?_⟩
  · intro k e s₁ s₂ i i'
    by_cases hk : 3 ≤ k
    · obtain ⟨c, hc, -⟩ := (hP k hk).choose_spec
      have e1 := hc e s₁ i i'
      have e2 := hc e s₂ i i'
      have hS : S k = (hP k hk).choose := dif_pos hk
      rw [hS, e1, e2]
      ring
    · have hS : S k = fun _ => zeroSec _ := dif_neg hk
      rw [hS]
      dsimp only [zeroSec]
      erw [map_zero, map_zero]
      simp only [map_zero, mul_zero]
  · intro k hk
    obtain ⟨c, hc, y, ⟨i', hi'⟩, hy⟩ := (hP k hk).choose_spec
    obtain ⟨s₀, i, hs⟩ := GlobalTheory.T.exists_section_nonvanishing_closedFibre_of_three_le R hB D A G hG U k hk ((b 0).left.base y)
    have hu : y ∈ (thickObj R (maximalIdeal R) 0 G).left.basicOpen
        ((((b 0).left ≫ (fstG (maximalIdeal R) 0 G).left).app (secChart U.LG.L i)).hom (s₀.f i)) := by
      have h1 : y ∈ (b 0).left ⁻¹ᵁ (thickObj R (maximalIdeal R) 0 G).left.basicOpen
          (((fstG (maximalIdeal R) 0 G).left.app (secChart U.LG.L i)).hom (s₀.f i)) := hs
      rw [Scheme.preimage_basicOpen] at h1
      exact h1
    have hyW : y ∈ ((b 0).left ≫ (fstG (maximalIdeal R) 0 G).left) ⁻¹ᵁ secChart U.LG.L i ⊓
        (fstG (maximalIdeal R) 0 G).left ⁻¹ᵁ secChart U.LG.L i' :=
      ⟨Scheme.basicOpen_le _ _ hu, hi'⟩
    have hS : S k = (hP k hk).choose := dif_pos hk
    refine ⟨s₀, y, i, i', hu, ?_⟩
    rw [hS]
    have key := hc 0 s₀ i i'
    have hprod : y ∈ (thickObj R (maximalIdeal R) 0 G).left.basicOpen (c 0 i i' *
        ((thickObj R (maximalIdeal R) 0 G).left.presheaf.map (homOfLE (inf_le_left :
          ((b 0).left ≫ (fstG (maximalIdeal R) 0 G).left) ⁻¹ᵁ secChart U.LG.L i ⊓
            (fstG (maximalIdeal R) 0 G).left ⁻¹ᵁ secChart U.LG.L i' ≤
            ((b 0).left ≫ (fstG (maximalIdeal R) 0 G).left) ⁻¹ᵁ secChart U.LG.L i)).op).hom
          ((((b 0).left ≫ (fstG (maximalIdeal R) 0 G).left).app (secChart U.LG.L i)).hom (s₀.f i))) := by
      rw [Scheme.basicOpen_mul, Scheme.basicOpen_res]
      exact ⟨hy i i' hyW, hyW, hu⟩
    rw [← key, Scheme.basicOpen_res] at hprod
    exact hprod.2

end GlobalTheory.MumSec

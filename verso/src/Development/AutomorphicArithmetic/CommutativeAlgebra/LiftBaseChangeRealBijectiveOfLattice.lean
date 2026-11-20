import Mathlib
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.ComplexUniformizationSigOne
import Development.AutomorphicArithmetic.RealSpanData.RealData

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField Matrix
open IsDedekindDomain
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct Classical ComplexOrder
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.DiscreteGroups.LocalClassField
open GlobalTheory GlobalTheory.AV GlobalTheory.AV.AbVar GlobalTheory.PDivGroup GlobalTheory.Dieu GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKGeo GlobalTheory.LKCx GlobalTheory.PELU
attribute [local instance] Over.cartesianMonoidalCategory
open UpperTheory.ComplexUniformization

/- English proof (translation)
Introduce `g V La _ _ _ _ _ j hj hspan P hP hdisc hPspan Pq hPq`. Establish `hsurj : Function.Surjective (LinearMap.liftBaseChange ℝ Pq)`. Rewrite using `[← LinearMap.range_eq_top, eq_top_iff, ← hPspan, Submodule.span_le]`. Introduce and unpack `_ ⟨z, rfl⟩`. Conclude with `⟨(1 : ℝ) ⊗ₜ j z, by simp [LinearMap.liftBaseChange_tmul, hPq]⟩`.

Set `L : Submodule ℤ (Fin g → ℂ)` to `P.range.toIntSubmodule`. Use `haveI : DiscreteTopology L := hdisc`. Use `haveI : IsZLattice ℝ L := ⟨by simpa [L] using hPspan⟩`. Establish `hrank : Module.finrank ℤ La = Module.finrank ℝ (Fin g → ℂ)`. Rewrite using `[← ZLattice.rank ℝ L]`.

Conclude with `LinearEquiv.finrank_eq (LinearEquiv.ofInjective P.toIntLinearMap hP)`. Set `b` to `Module.Free.chooseBasis ℤ La`. Establish `hsub : ∀ z, j z ∈ Submodule.span ℚ (Set.range (j ∘ b))`. Introduce `z`. Establish `htop : ((Submodule.span ℚ (Set.range (j ∘ b))).restrictScalars ℤ).comap j.toIntLinearMap = ⊤`.

Rewrite using `[eq_top_iff, ← b.span_eq, Submodule.span_le]`. Introduce and unpack `_ ⟨i, rfl⟩`. Conclude with `Submodule.subset_span ⟨i, rfl⟩`. Establish `: z ∈ ((Submodule.span ℚ (Set.range (j ∘ b))).restrictScalars ℤ).comap j.toIntLinearMap`. Rewrite using `[htop]`.

Discharge the goal by the elementary cases of `trivial`. Conclude with `this`. Establish `hVspan : Submodule.span ℚ (Set.range (j ∘ b)) = ⊤`. Rewrite using `[eq_top_iff, ← hspan, Submodule.span_le]`. Introduce and unpack `_ ⟨z, rfl⟩`.

Conclude with `hsub z`. Use `haveI : Module.Finite ℚ V := ⟨⟨Finset.univ.image (j ∘ b), by`. Rewrite using `[Finset.coe_image, Finset.coe_univ, Set.image_univ]`. Conclude with `hVspan⟩⟩`. Establish `hV : Module.finrank ℚ V ≤ Module.finrank ℤ La`.

Rewrite using `[Module.finrank_eq_card_chooseBasisIndex ℤ La, ← finrank_top, ← hVspan]`. Conclude with `finrank_range_le_card (b := j ∘ b)`. Establish `hdim : Module.finrank ℝ (ℝ ⊗[ℚ] V) = Module.finrank ℝ (Fin g → ℂ)`. Use `le_antisymm ?_ ?_` and prove the remaining obligations. Rewrite using `[Module.finrank_baseChange]`.

Use linear arithmetic over natural numbers and integers. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[LinearMap.range_eq_top.mpr hsurj]`. Use `_ ≤ _ := LinearMap.finrank_range_le _`. Conclude with `⟨(LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).mpr hsurj, hsurj⟩`.
-/
theorem UpperTheory.liftBaseChange_real_bijective_of_lattice :
    ∀ (g : ℕ) (V La : Type) [AddCommGroup V] [Module ℚ V] [AddCommGroup La] [Module.Finite ℤ La] [Module.Free ℤ La] (j : La →+ V), Function.Injective j → Submodule.span ℚ (Set.range j) = ⊤ → ∀ P : La →+ (Fin g → ℂ), Function.Injective P → DiscreteTopology P.range → Submodule.span ℝ (Set.range P) = ⊤ → ∀ Pq : V →ₗ[ℚ] (Fin g → ℂ), (∀ z, Pq (j z) = P z) → Function.Bijective (LinearMap.liftBaseChange ℝ Pq) := by
  intro g V La _ _ _ _ _ j hj hspan P hP hdisc hPspan Pq hPq
  classical
  have hsurj : Function.Surjective (LinearMap.liftBaseChange ℝ Pq) := by
    rw [← LinearMap.range_eq_top, eq_top_iff, ← hPspan, Submodule.span_le]
    rintro _ ⟨z, rfl⟩
    exact ⟨(1 : ℝ) ⊗ₜ j z, by simp [LinearMap.liftBaseChange_tmul, hPq]⟩
  let L : Submodule ℤ (Fin g → ℂ) := P.range.toIntSubmodule
  haveI : DiscreteTopology L := hdisc
  haveI : IsZLattice ℝ L := ⟨by simpa [L] using hPspan⟩
  have hrank : Module.finrank ℤ La = Module.finrank ℝ (Fin g → ℂ) := by
    rw [← ZLattice.rank ℝ L]
    exact LinearEquiv.finrank_eq (LinearEquiv.ofInjective P.toIntLinearMap hP)
  let b := Module.Free.chooseBasis ℤ La
  have hsub : ∀ z, j z ∈ Submodule.span ℚ (Set.range (j ∘ b)) := by
    intro z
    have htop : ((Submodule.span ℚ (Set.range (j ∘ b))).restrictScalars ℤ).comap j.toIntLinearMap = ⊤ := by
      rw [eq_top_iff, ← b.span_eq, Submodule.span_le]
      rintro _ ⟨i, rfl⟩
      exact Submodule.subset_span ⟨i, rfl⟩
    have : z ∈ ((Submodule.span ℚ (Set.range (j ∘ b))).restrictScalars ℤ).comap j.toIntLinearMap := by
      rw [htop]; trivial
    exact this
  have hVspan : Submodule.span ℚ (Set.range (j ∘ b)) = ⊤ := by
    rw [eq_top_iff, ← hspan, Submodule.span_le]
    rintro _ ⟨z, rfl⟩
    exact hsub z
  haveI : Module.Finite ℚ V := ⟨⟨Finset.univ.image (j ∘ b), by
    rw [Finset.coe_image, Finset.coe_univ, Set.image_univ]; exact hVspan⟩⟩
  have hV : Module.finrank ℚ V ≤ Module.finrank ℤ La := by
    rw [Module.finrank_eq_card_chooseBasisIndex ℤ La, ← finrank_top, ← hVspan]
    exact finrank_range_le_card (b := j ∘ b)
  have hdim : Module.finrank ℝ (ℝ ⊗[ℚ] V) = Module.finrank ℝ (Fin g → ℂ) := by
    refine le_antisymm ?_ ?_
    · rw [Module.finrank_baseChange]; omega
    · calc Module.finrank ℝ (Fin g → ℂ)
          = Module.finrank ℝ (⊤ : Submodule ℝ (Fin g → ℂ)) := (finrank_top ℝ _).symm
        _ = Module.finrank ℝ (LinearMap.range (LinearMap.liftBaseChange ℝ Pq)) := by
          rw [LinearMap.range_eq_top.mpr hsurj]
        _ ≤ _ := LinearMap.finrank_range_le _
  exact ⟨(LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).mpr hsurj, hsurj⟩

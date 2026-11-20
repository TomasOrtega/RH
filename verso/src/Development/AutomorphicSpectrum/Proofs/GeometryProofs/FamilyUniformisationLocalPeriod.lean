import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.BdryChart
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsFlatAnIffIsConstMul
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.LevelSectionsExactKernelLocusOpen
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.ClopenCondOnto
import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.BlowupProjections.BlowupProjStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat Filter Topology Metric

namespace GlobalTheory.CompanionTheory.Ar.Flat

/- English proof (translation)
Introduce `E _ _ _ H D l Xo σ g ty FU m B y hB hpre hne hs hy`. Set `S : Fin FU.n → Set (Fin m → ℂ)` to `fun i => {b₀ | ∃ (B' : Set (Fin m → ℂ)) (P : (Fin m → ℂ) → ((FU.Di i).La →+ (Fin g → ℂ))), IsOpen B' ∧ b₀ ∈ B' ∧ B' ⊆ B ∧ IsHolPeriods (FU.Di i) ty B' P ∧ ∀ b ∈ B', FU.u i (P b) = y b}`. Establish `hopen : ∀ i, IsOpen (S i)`. Introduce `i`. Use `isOpen_iff_forall_mem_open.2 ?_` and prove the remaining obligations.

Introduce and unpack `b₀ ⟨B', P, hB', hb₀, hsub, hP, hu⟩`. Conclude with `⟨B', fun b hb => ⟨B', P, hB', hb, hsub, hP, hu⟩, hB', hb₀⟩`. Establish `hcover : ∀ b ∈ B, ∃ i, b ∈ S i`. Introduce `b hb`. Take `⟨B', i, P, hB', hb', hsub, hP, hu⟩` from `FU.lift m B y hB hs hy b hb`.

Conclude with `⟨i, B', P, hB', hb', hsub, hP, hu⟩`. Establish `hdisj : ∀ i j b, b ∈ S i → b ∈ S j → i = j`. Introduce and unpack `i j b ⟨B₁, P₁, -, hb₁, -, hP₁, hu₁⟩ ⟨B₂, P₂, -, hb₂, -, hP₂, hu₂⟩`. Conclude with `FU.disj i j (P₁ b) (P₂ b) (hP₁.1 b hb₁) (hP₂.1 b hb₂) ((hu₁ b hb₁).trans (hu₂ b hb₂).symm)`. Take `⟨b₁, hb₁⟩` from `hne`.

Take `⟨i, hi⟩` from `hcover b₁ hb₁`. Establish `hsub : B ⊆ S i`. Use `IsPreconnected.subset_left_of_subset_union (v := ⋃ j ∈ {j | j ≠ i}, S j) (hopen i) (isOpen_biUnion fun j _ => hopen j) ?_ ?_ ⟨b₁, hb₁, hi⟩ hpre` and prove the remaining obligations. Use `Set.disjoint_left.2 fun b hbi hbT => ?_` and prove the remaining obligations. Take `⟨j, hj, hbj⟩` from `Set.mem_iUnion₂.1 hbT`.

Conclude with `hj (hdisj i j b hbi hbj).symm`. Introduce `b hb`. Take `⟨j, hj⟩` from `hcover b hb`. Distinguish the cases in `hji : j = i`. Conclude with `Or.inl (hji ▸ hj)`.

Conclude with `Or.inr (Set.mem_iUnion₂.2 ⟨j, hji, hj⟩)`. Conclude with `⟨i, fun b₀ hb₀ => hsub hb₀⟩`.
-/
theorem exists_index_of_isPreconnected : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (σ : KA l →+* ℂ) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (FU : FamilyUnif Xo σ ty) (m : ℕ) (B : Set (Fin m → ℂ)) (y : (Fin m → ℂ) → (Sp ℂ ⟶ Xo.X)), IsOpen B → IsPreconnected B → B.Nonempty → (∀ b ∈ B, y b ≫ Xo.s = spMap σ) → IsHolTo B y → ∃ i : Fin FU.n, ∀ b₀ ∈ B, ∃ (B' : Set (Fin m → ℂ)) (P : (Fin m → ℂ) → ((FU.Di i).La →+ (Fin g → ℂ))), IsOpen B' ∧ b₀ ∈ B' ∧ B' ⊆ B ∧ IsHolPeriods (FU.Di i) ty B' P ∧ ∀ b ∈ B', FU.u i (P b) = y b := by
  intro E _ _ _ H D l Xo σ g ty FU m B y hB hpre hne hs hy
  let S : Fin FU.n → Set (Fin m → ℂ) := fun i => {b₀ | ∃ (B' : Set (Fin m → ℂ))
    (P : (Fin m → ℂ) → ((FU.Di i).La →+ (Fin g → ℂ))), IsOpen B' ∧ b₀ ∈ B' ∧ B' ⊆ B ∧
      IsHolPeriods (FU.Di i) ty B' P ∧ ∀ b ∈ B', FU.u i (P b) = y b}
  have hopen : ∀ i, IsOpen (S i) := by
    intro i
    refine isOpen_iff_forall_mem_open.2 ?_
    rintro b₀ ⟨B', P, hB', hb₀, hsub, hP, hu⟩
    exact ⟨B', fun b hb => ⟨B', P, hB', hb, hsub, hP, hu⟩, hB', hb₀⟩
  have hcover : ∀ b ∈ B, ∃ i, b ∈ S i := by
    intro b hb
    obtain ⟨B', i, P, hB', hb', hsub, hP, hu⟩ := FU.lift m B y hB hs hy b hb
    exact ⟨i, B', P, hB', hb', hsub, hP, hu⟩
  have hdisj : ∀ i j b, b ∈ S i → b ∈ S j → i = j := by
    rintro i j b ⟨B₁, P₁, -, hb₁, -, hP₁, hu₁⟩ ⟨B₂, P₂, -, hb₂, -, hP₂, hu₂⟩
    exact FU.disj i j (P₁ b) (P₂ b) (hP₁.1 b hb₁) (hP₂.1 b hb₂) ((hu₁ b hb₁).trans (hu₂ b hb₂).symm)
  obtain ⟨b₁, hb₁⟩ := hne
  obtain ⟨i, hi⟩ := hcover b₁ hb₁
  have hsub : B ⊆ S i := by
    refine IsPreconnected.subset_left_of_subset_union (v := ⋃ j ∈ {j | j ≠ i}, S j) (hopen i)
      (isOpen_biUnion fun j _ => hopen j) ?_ ?_ ⟨b₁, hb₁, hi⟩ hpre
    · refine Set.disjoint_left.2 fun b hbi hbT => ?_
      obtain ⟨j, hj, hbj⟩ := Set.mem_iUnion₂.1 hbT
      exact hj (hdisj i j b hbi hbj).symm
    · intro b hb
      obtain ⟨j, hj⟩ := hcover b hb
      by_cases hji : j = i
      · exact Or.inl (hji ▸ hj)
      · exact Or.inr (Set.mem_iUnion₂.2 ⟨j, hji, hj⟩)
  exact ⟨i, fun b₀ hb₀ => hsub hb₀⟩

end GlobalTheory.CompanionTheory.Ar.Flat

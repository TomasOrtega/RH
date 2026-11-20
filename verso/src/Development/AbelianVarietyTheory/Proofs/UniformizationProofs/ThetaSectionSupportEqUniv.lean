import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.IsNsmul
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.QkToAkU
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.FamMod
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PhiGenPf
import Development.AbelianVarietyTheory.Definitions.Uniformization.PsiScal
import Development.AbelianVarietyTheory.Definitions.Uniformization.ExistsUniqueSamePt
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsUniquePullB
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsPrimeHomZmodOfNeTop
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.LineBundleSectionsTorusTorsionWeightSpacesStatement
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ThetaExpansionSupportNotInPrimeIndexSubgroupStatement
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExpFOneDimStatement
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.PullbackSectionFamilyNeZeroIff
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ThetaSupportPairIffDegreeTwoSumDiffStatement
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU
namespace GlobalTheory.UU

/- English proof (translation)
Introduce `h1 h2 V _ _ _ hV D A G _ _ U θ f hθ`. Establish `hrel` using `GlobalTheory.T.thetaSupport_pair_iff_degreeTwo_sum_diff h1 h2 V hV D A G U θ f hθ`. Establish `hodd` using `GlobalTheory.T.thetaExpansion_support_not_in_primeIndex_subgroup h1 h2 V hV D A G U θ f hθ`. Establish `hw` using `GlobalTheory.T.lineBundleSections_torusTorsion_weightSpaces h1 h2 V hV D A G U`. Establish `hpull` using `GlobalTheory.UU.PullSec.pullEx V hV D A G U (Kbar V) (𝟙_ _) (toUnit _) 1`.

Take `⟨th, hth, -⟩` from `hpull.1 θ`. Take `⟨s₀, hs₀, -⟩` from `hpull.2 f`. Establish `hone` using `(GlobalTheory.T.expF_of_theta_degree_one h1 h2 V hV D A G U θ f hθ th s₀ hth hs₀).2.2`. Establish `hne : ({α | ∃ j, (f α).f j ≠ 0} : Set D.X).Nonempty`. Take `⟨mu, t, s, hts, j, hj⟩` from `(hw 1 le_rfl).2.1 0`.

Take `⟨c, hc⟩` from `hone t s hts`. Use `⟨0 + 1 • mu, (_root_.GlobalTheory.pullB_ne_zero_iff V D (Kbar V) 1 f s₀ hs₀ _).1 ⟨j, fun h0 => hj ?_⟩⟩` and prove the remaining obligations. Rewrite using `[hc, h0, mul_zero]`. Take `⟨hS, Λ, hΛ, hc⟩` from `GlobalTheory.support_subgroup_odd_index D.X {α | ∃ j, (f α).f j ≠ 0} {α | U.Supp (Kbar V) 2 α} hne hrel (fun x => by`. Take `⟨mu, hmu⟩` from `(hw 2 (by norm_num)).2.1 x`.

Conclude with `⟨mu, by rw [← two_nsmul]; exact hmu⟩)`. Establish `htop : Λ = ⊤`. Break down `hc with h | ⟨l, hl, -, g, hg, hgΛ⟩` into its components or cases. Conclude with `h`. Use `absurd (hodd l hl g fun α hα => hgΛ α ?_) hg` and prove the remaining obligations.

Establish `: α ∈ (Λ : Set D.X)` using `by rw [hΛ]; exact hα`. Conclude with `this`. Establish `hall : ∀ α, α ∈ ({α | ∃ j, (f α).f j ≠ 0} : Set D.X)` using `fun α => by`. Rewrite using `[← hΛ, htop]`. Discharge the goal by the elementary cases of `trivial`.

Use `⟨hall, fun α => ?_⟩` and prove the remaining obligations. Establish `: α ∈ ({α | U.Supp (Kbar V) 2 α} : Set D.X)` using `by rw [hS]; exact hall α`. Conclude with `this`.
-/
theorem theta_support_eq_univ : Laws → Laws2 → (AllPre fun {V} _ _ _ {D} {A} {G} _ _ U => ∀ θ f, U.Theta θ f → (∀ α, ∃ j, (f α).f j ≠ 0) ∧ ∀ α, U.Supp (Kbar V) 2 α) := by
  intro h1 h2 V _ _ _ hV D A G _ _ U θ f hθ
  have hrel := GlobalTheory.T.thetaSupport_pair_iff_degreeTwo_sum_diff h1 h2 V hV D A G U θ f hθ
  have hodd := GlobalTheory.T.thetaExpansion_support_not_in_primeIndex_subgroup h1 h2 V hV D A G U θ f hθ
  have hw := GlobalTheory.T.lineBundleSections_torusTorsion_weightSpaces h1 h2 V hV D A G U
  have hpull := GlobalTheory.UU.PullSec.pullEx V hV D A G U (Kbar V) (𝟙_ _) (toUnit _) 1
  obtain ⟨th, hth, -⟩ := hpull.1 θ
  obtain ⟨s₀, hs₀, -⟩ := hpull.2 f
  have hone := (GlobalTheory.T.expF_of_theta_degree_one h1 h2 V hV D A G U θ f hθ th s₀ hth hs₀).2.2
  have hne : ({α | ∃ j, (f α).f j ≠ 0} : Set D.X).Nonempty := by
    obtain ⟨mu, t, s, hts, j, hj⟩ := (hw 1 le_rfl).2.1 0
    obtain ⟨c, hc⟩ := hone t s hts
    refine ⟨0 + 1 • mu, (_root_.GlobalTheory.pullB_ne_zero_iff V D (Kbar V) 1 f s₀ hs₀ _).1 ⟨j, fun h0 => hj ?_⟩⟩
    rw [hc, h0, mul_zero]
  obtain ⟨hS, Λ, hΛ, hc⟩ := GlobalTheory.support_subgroup_odd_index D.X {α | ∃ j, (f α).f j ≠ 0}
    {α | U.Supp (Kbar V) 2 α} hne hrel (fun x => by
      obtain ⟨mu, hmu⟩ := (hw 2 (by norm_num)).2.1 x
      exact ⟨mu, by rw [← two_nsmul]; exact hmu⟩)
  have htop : Λ = ⊤ := by
    rcases hc with h | ⟨l, hl, -, g, hg, hgΛ⟩
    · exact h
    · refine absurd (hodd l hl g fun α hα => hgΛ α ?_) hg
      have : α ∈ (Λ : Set D.X) := by rw [hΛ]; exact hα
      exact this
  have hall : ∀ α, α ∈ ({α | ∃ j, (f α).f j ≠ 0} : Set D.X) := fun α => by
    rw [← hΛ, htop]; trivial
  refine ⟨hall, fun α => ?_⟩
  have : α ∈ ({α | U.Supp (Kbar V) 2 α} : Set D.X) := by rw [hS]; exact hall α
  exact this

end GlobalTheory.UU

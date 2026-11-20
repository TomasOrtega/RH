import Mathlib
import Formalism.PeriodIntegrals.FoldMult

open MeasureTheory
open scoped ENNReal NNReal

namespace PI.FoldMult.UnitaryGroupMassFormula

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G]

def cnt (Γ : Subgroup G) (Ω : Set G) (x y : G) : Set Γ := {γ : Γ | x⁻¹ * ((γ : G) * y) ∈ Ω}

/- English proof (translation)
Use `set K : Set G := (fun p : G × G => x * p.1 * (x * p.2)⁻¹) '' (Ω ×ˢ Ω) with hKdef`. Establish `hK : IsCompact K` using `(hΩ.prod hΩ).image (by fun_prop)`. Establish `hS : ((Subtype.val : Γ → G) ⁻¹' K).Finite` using `((Subgroup.isClosed_of_discrete (H := Γ)).isClosedEmbedding_subtypeVal.isCompact_preimage hK).finite_of_discrete`. Use `⟨((Subtype.val : Γ → G) ⁻¹' K).encard, hS.encard_lt_top, fun y => ?_⟩` and prove the remaining obligations. Break down `(cnt Γ Ω x y).eq_empty_or_nonempty with h | ⟨γ₀, hγ₀⟩` into its components or cases.

Rewrite using `[h, Set.encard_empty]`. Conclude with `zero_le`. Use `le_trans (Set.encard_le_encard (t := (fun δ : Γ => δ * γ₀) '' ((Subtype.val : Γ → G) ⁻¹' K)) ?_) (Set.encard_image_le _ _)` and prove the remaining obligations. Introduce `γ hγ`. Use `⟨γ * γ₀⁻¹, ?_, by simp⟩` and prove the remaining obligations.

Use `⟨(x⁻¹ * ((γ : G) * y), x⁻¹ * ((γ₀ : G) * y)), ⟨hγ, hγ₀⟩, ?_⟩` and prove the remaining obligations. Simplify using `only [Subgroup.coe_mul, Subgroup.coe_inv]`. Use `group`.
-/
theorem cnt_encard_le (Γ : Subgroup G) [DiscreteTopology Γ] (Ω : Set G) (hΩ : IsCompact Ω)
    (x : G) : ∃ N : ℕ∞, N < ⊤ ∧ ∀ y, (cnt Γ Ω x y).encard ≤ N := by
  set K : Set G := (fun p : G × G => x * p.1 * (x * p.2)⁻¹) '' (Ω ×ˢ Ω) with hKdef
  have hK : IsCompact K := (hΩ.prod hΩ).image (by fun_prop)
  have hS : ((Subtype.val : Γ → G) ⁻¹' K).Finite :=
    ((Subgroup.isClosed_of_discrete (H := Γ)).isClosedEmbedding_subtypeVal.isCompact_preimage hK).finite_of_discrete
  refine ⟨((Subtype.val : Γ → G) ⁻¹' K).encard, hS.encard_lt_top, fun y => ?_⟩
  rcases (cnt Γ Ω x y).eq_empty_or_nonempty with h | ⟨γ₀, hγ₀⟩
  · rw [h, Set.encard_empty]
    exact zero_le
  · refine le_trans (Set.encard_le_encard (t := (fun δ : Γ => δ * γ₀) '' ((Subtype.val : Γ → G) ⁻¹' K)) ?_)
      (Set.encard_image_le _ _)
    intro γ hγ
    refine ⟨γ * γ₀⁻¹, ?_, by simp⟩
    refine ⟨(x⁻¹ * ((γ : G) * y), x⁻¹ * ((γ₀ : G) * y)), ⟨hγ, hγ₀⟩, ?_⟩
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    group

/- English proof (translation)
Unfold `Formalism.L2.SG.FoldBound.mult`. Use `le_iSup_of_le x ?_` and prove the remaining obligations. Establish `h : (1 : ℕ∞) ≤ ({γ : Γ | x⁻¹ * ((γ : G) * x) ∈ Ω} : Set Γ).encard` using `Set.one_le_encard_iff_nonempty.2 ⟨1, by simpa using h1⟩`. Conclude with `h` after adjusting the coercions.
-/
theorem one_le_mult (Γ : Subgroup G) (Ω : Set G) (h1 : (1 : G) ∈ Ω) (x : G) :
    1 ≤ Formalism.L2.SG.FoldBound.mult Γ Ω x := by
  unfold Formalism.L2.SG.FoldBound.mult
  refine le_iSup_of_le x ?_
  have h : (1 : ℕ∞) ≤ ({γ : Γ | x⁻¹ * ((γ : G) * x) ∈ Ω} : Set Γ).encard :=
    Set.one_le_encard_iff_nonempty.2 ⟨1, by simpa using h1⟩
  exact_mod_cast h

/- English proof (translation)
Take `⟨N, hN, hle⟩` from `cnt_encard_le Γ Ω hΩ x`. Conclude with `lt_of_le_of_lt (b := (N : ℝ≥0∞)) (iSup_le fun y => ENat.toENNReal_le.2 (hle y)) (ENat.toENNReal_lt_top.2 hN)`.
-/
theorem mult_lt_top (Γ : Subgroup G) [DiscreteTopology Γ] (Ω : Set G) (hΩ : IsCompact Ω)
    (x : G) : Formalism.L2.SG.FoldBound.mult Γ Ω x < ⊤ := by
  obtain ⟨N, hN, hle⟩ := cnt_encard_le Γ Ω hΩ x
  exact lt_of_le_of_lt (b := (N : ℝ≥0∞)) (iSup_le fun y => ENat.toENNReal_le.2 (hle y))
    (ENat.toENNReal_lt_top.2 hN)

/- English proof (translation)
Unfold `Formalism.L2.SG.FoldBound.mult`. Use `iSup_congr fun y => ?_` and prove the remaining obligations. Establish `hs : ({δ : Γ | (γ * x)⁻¹ * ((δ : G) * y) ∈ Ω} : Set Γ) = (fun ε : Γ => (⟨γ, hγ⟩ : Γ) * ε) '' {ε : Γ | x⁻¹ * ((ε : G) * y) ∈ Ω}`. Use extensionality with `δ`. Simplify using `only [Set.mem_ofPred_eq, Set.mem_image]`.

Prove the components needed by the constructor for the conclusion. Introduce `hδ`. Use `⟨(⟨γ, hγ⟩ : Γ)⁻¹ * δ, ?_, by simp⟩` and prove the remaining obligations. Simplify `hδ` using `[mul_assoc]`. Introduce and unpack `⟨ε, hε, rfl⟩`.

Simplify `hε` using `[mul_assoc]`. Rewrite using `[hs, Set.InjOn.encard_image (mul_right_injective _).injOn]`.
-/
theorem mult_mul_left (Γ : Subgroup G) (Ω : Set G) (γ : G) (hγ : γ ∈ Γ) (x : G) :
    Formalism.L2.SG.FoldBound.mult Γ Ω (γ * x) = Formalism.L2.SG.FoldBound.mult Γ Ω x := by
  unfold Formalism.L2.SG.FoldBound.mult
  refine iSup_congr fun y => ?_
  have hs : ({δ : Γ | (γ * x)⁻¹ * ((δ : G) * y) ∈ Ω} : Set Γ) =
      (fun ε : Γ => (⟨γ, hγ⟩ : Γ) * ε) '' {ε : Γ | x⁻¹ * ((ε : G) * y) ∈ Ω} := by
    ext δ
    simp only [Set.mem_ofPred_eq, Set.mem_image]
    constructor
    · intro hδ
      refine ⟨(⟨γ, hγ⟩ : Γ)⁻¹ * δ, ?_, by simp⟩
      simpa [mul_assoc] using hδ
    · rintro ⟨ε, hε, rfl⟩
      simpa [mul_assoc] using hε
  rw [hs, Set.InjOn.encard_image (mul_right_injective _).injOn]

def hitSet (Γ : Subgroup G) (Ω : Set G) (A : Finset Γ) : Set G :=
  {x | ∃ y : G, ∀ a ∈ A, x⁻¹ * ((a : G) * y) ∈ Ω}

/- English proof (translation)
Break down `A.eq_empty_or_nonempty with rfl | ⟨a₀, ha₀⟩` into its components or cases. Use `isClosed_univ` and compare the differences between its conclusion and the goal. Use extensionality with `x`. Simplify using `[hitSet]`. Establish `hΩc : IsClosed Ω` using `hΩ.isClosed`.

Establish `: CompactSpace Ω` using `isCompact_iff_compactSpace.1 hΩ`. Establish `hC : IsClosed {p : G × Ω | ∀ a ∈ A, p.1⁻¹ * ((a : G) * ((a₀ : G)⁻¹ * (p.1 * (p.2 : G)))) ∈ Ω}`. Establish `hI : {p : G × Ω | ∀ a ∈ A, p.1⁻¹ * ((a : G) * ((a₀ : G)⁻¹ * (p.1 * (p.2 : G)))) ∈ Ω} = ⋂ a ∈ A, (fun p : G × Ω => p.1⁻¹ * ((a : G) * ((a₀ : G)⁻¹ * (p.1 * (p.2 : G))))) ⁻¹' Ω`. Use extensionality with `p`. Simplify using the standard rewrite rules.

Rewrite using `[hI]`. Conclude with `isClosed_biInter fun a _ => hΩc.preimage (by fun_prop)`. Establish `hEq : hitSet Γ Ω A = Prod.fst '' {p : G × Ω | ∀ a ∈ A, p.1⁻¹ * ((a : G) * ((a₀ : G)⁻¹ * (p.1 * (p.2 : G)))) ∈ Ω}`. Use extensionality with `x`. Prove the components needed by the constructor for the conclusion.

Introduce and unpack `⟨y, hy⟩`. Use `⟨(x, ⟨x⁻¹ * ((a₀ : G) * y), hy a₀ ha₀⟩), fun a ha => ?_, rfl⟩` and prove the remaining obligations. Simplify `hy a ha` using `[mul_assoc]`. Introduce and unpack `⟨p, hp, rfl⟩`. Conclude with `⟨(a₀ : G)⁻¹ * (p.1 * (p.2 : G)), hp⟩`.

Rewrite using `[hEq]`. Conclude with `isClosedMap_fst_of_compactSpace _ hC`.
-/
theorem isClosed_hitSet (Γ : Subgroup G) (Ω : Set G) (hΩ : IsCompact Ω) (A : Finset Γ) :
    IsClosed (hitSet Γ Ω A) := by
  rcases A.eq_empty_or_nonempty with rfl | ⟨a₀, ha₀⟩
  · convert isClosed_univ
    ext x
    simp [hitSet]
  · have hΩc : IsClosed Ω := hΩ.isClosed
    have : CompactSpace Ω := isCompact_iff_compactSpace.1 hΩ
    have hC : IsClosed {p : G × Ω | ∀ a ∈ A, p.1⁻¹ * ((a : G) * ((a₀ : G)⁻¹ * (p.1 * (p.2 : G)))) ∈ Ω} := by
      have hI : {p : G × Ω | ∀ a ∈ A, p.1⁻¹ * ((a : G) * ((a₀ : G)⁻¹ * (p.1 * (p.2 : G)))) ∈ Ω} =
          ⋂ a ∈ A, (fun p : G × Ω => p.1⁻¹ * ((a : G) * ((a₀ : G)⁻¹ * (p.1 * (p.2 : G))))) ⁻¹' Ω := by
        ext p
        simp
      rw [hI]
      exact isClosed_biInter fun a _ => hΩc.preimage (by fun_prop)
    have hEq : hitSet Γ Ω A =
        Prod.fst '' {p : G × Ω | ∀ a ∈ A, p.1⁻¹ * ((a : G) * ((a₀ : G)⁻¹ * (p.1 * (p.2 : G)))) ∈ Ω} := by
      ext x
      constructor
      · rintro ⟨y, hy⟩
        refine ⟨(x, ⟨x⁻¹ * ((a₀ : G) * y), hy a₀ ha₀⟩), fun a ha => ?_, rfl⟩
        simpa [mul_assoc] using hy a ha
      · rintro ⟨p, hp, rfl⟩
        exact ⟨(a₀ : G)⁻¹ * (p.1 * (p.2 : G)), hp⟩
    rw [hEq]
    exact isClosedMap_fst_of_compactSpace _ hC

/- English proof (translation)
Take `⟨N, hN, hle⟩` from `cnt_encard_le Γ Ω hΩ x`. Unfold `Formalism.L2.SG.FoldBound.mult`. Apply `le_antisymm` to reduce the goal to its premises. Use `iSup_le fun y => ?_` and prove the remaining obligations. Establish `hfin : (cnt Γ Ω x y).Finite` using `Set.encard_lt_top_iff.1 ((hle y).trans_lt hN)`.

Use `le_iSup_of_le hfin.toFinset ?_` and prove the remaining obligations. Establish `hx : x ∈ hitSet Γ Ω hfin.toFinset` using `⟨y, fun a ha => hfin.mem_toFinset.1 ha⟩`. Rewrite using `[Set.indicator_of_mem hx]`. Express the relevant statement in the definitionally equal form `((cnt Γ Ω x y).encard : ℝ≥0∞) ≤ (hfin.toFinset.card : ℝ≥0∞)`. Conclude with `le_of_eq (by rw [hfin.encard_eq_coe_toFinset_card, ENat.toENNReal_coe])`.

Use `iSup_le fun B => ?_` and prove the remaining obligations. Distinguish the cases in `hx : x ∈ hitSet Γ Ω B`. Take `⟨y, hy⟩` from `hx`. Rewrite using `[Set.indicator_of_mem (show x ∈ hitSet Γ Ω B from ⟨y, hy⟩)]`. Use `le_iSup_of_le y ?_` and prove the remaining obligations.

Establish `hsub : (B : Set Γ) ⊆ cnt Γ Ω x y` using `fun a ha => hy a ha`. Establish `hc` using `Set.encard_le_encard hsub`. Rewrite `hc` using `[Set.encard_coe_eq_coe_finsetCard]`. Use `show (B.card : ℝ≥0∞) ≤ _`. Rewrite using `[← ENat.toENNReal_coe]`.

Conclude with `ENat.toENNReal_le.2 hc`. Rewrite using `[Set.indicator_of_notMem hx]`. Conclude with `zero_le`.
-/
theorem mult_eq_iSup (Γ : Subgroup G) [DiscreteTopology Γ] (Ω : Set G) (hΩ : IsCompact Ω)
    (x : G) : Formalism.L2.SG.FoldBound.mult Γ Ω x =
      ⨆ A : Finset Γ, (hitSet Γ Ω A).indicator (fun _ => (A.card : ℝ≥0∞)) x := by
  obtain ⟨N, hN, hle⟩ := cnt_encard_le Γ Ω hΩ x
  unfold Formalism.L2.SG.FoldBound.mult
  apply le_antisymm
  · refine iSup_le fun y => ?_
    have hfin : (cnt Γ Ω x y).Finite := Set.encard_lt_top_iff.1 ((hle y).trans_lt hN)
    refine le_iSup_of_le hfin.toFinset ?_
    have hx : x ∈ hitSet Γ Ω hfin.toFinset := ⟨y, fun a ha => hfin.mem_toFinset.1 ha⟩
    rw [Set.indicator_of_mem hx]
    change ((cnt Γ Ω x y).encard : ℝ≥0∞) ≤ (hfin.toFinset.card : ℝ≥0∞)
    exact le_of_eq (by rw [hfin.encard_eq_coe_toFinset_card, ENat.toENNReal_coe])
  · refine iSup_le fun B => ?_
    by_cases hx : x ∈ hitSet Γ Ω B
    · obtain ⟨y, hy⟩ := hx
      rw [Set.indicator_of_mem (show x ∈ hitSet Γ Ω B from ⟨y, hy⟩)]
      refine le_iSup_of_le y ?_
      have hsub : (B : Set Γ) ⊆ cnt Γ Ω x y := fun a ha => hy a ha
      have hc := Set.encard_le_encard hsub
      rw [Set.encard_coe_eq_coe_finsetCard] at hc
      show (B.card : ℝ≥0∞) ≤ _
      rw [← ENat.toENNReal_coe]
      exact ENat.toENNReal_le.2 hc
    · rw [Set.indicator_of_notMem hx]
      exact zero_le

/- English proof (translation)
Establish `: Countable Γ` using `TopologicalSpace.separableSpace_iff_countable.1 inferInstance`. Establish `hm : Formalism.L2.SG.FoldBound.mult Γ Ω = fun x => ⨆ A : Finset Γ, (hitSet Γ Ω A).indicator (fun _ => (A.card : ℝ≥0∞)) x`. Use function extensionality and compare the values at `(mult_eq_iSup Γ Ω hΩ)`. Rewrite using `[hm]`. Conclude with `Measurable.iSup fun A => measurable_const.indicator (isClosed_hitSet Γ Ω hΩ A).measurableSet`.
-/
theorem measurable_mult [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
    (Γ : Subgroup G) [DiscreteTopology Γ] (Ω : Set G) (hΩ : IsCompact Ω) :
    Measurable (Formalism.L2.SG.FoldBound.mult Γ Ω) := by
  have : Countable Γ := TopologicalSpace.separableSpace_iff_countable.1 inferInstance
  have hm : Formalism.L2.SG.FoldBound.mult Γ Ω =
      fun x => ⨆ A : Finset Γ, (hitSet Γ Ω A).indicator (fun _ => (A.card : ℝ≥0∞)) x :=
    funext (mult_eq_iSup Γ Ω hΩ)
  rw [hm]
  exact Measurable.iSup fun A => measurable_const.indicator (isClosed_hitSet Γ Ω hΩ A).measurableSet

end PI.FoldMult.UnitaryGroupMassFormula

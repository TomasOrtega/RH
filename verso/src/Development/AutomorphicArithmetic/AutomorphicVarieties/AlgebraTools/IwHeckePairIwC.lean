import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.HeckePairTop
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.IwMemIwC
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ValuationDetOfMemKO
open ValuativeRel Matrix GlobalTheory.SmGL GlobalTheory.SplitWeil UpperTheory.V.Hi UpperTheory.V.AlgebraTools

/- English proof (translation)
Use `haveI : DiscreteTopology (G ⧸ K') := QuotientGroup.discreteTopology hK'`. Establish `hc : Continuous fun g : G => ((g * x : G) : G ⧸ K')` using `QuotientGroup.continuous_mk.comp (continuous_id.mul continuous_const)`. Use `((hL.image hc).finite_of_discrete).subset ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨g, rfl⟩`. Conclude with `⟨g, hK g.2, rfl⟩`.
-/
private theorem finOrb_of_compact {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    {K K' L : Subgroup G} (hL : IsCompact (L : Set G)) (hK : K ≤ L) (hK' : IsOpen (K' : Set G)) (x : G) :
    FinOrb K K' x := by
  haveI : DiscreteTopology (G ⧸ K') := QuotientGroup.discreteTopology hK'
  have hc : Continuous fun g : G => ((g * x : G) : G ⧸ K') :=
    QuotientGroup.continuous_mk.comp (continuous_id.mul continuous_const)
  refine ((hL.image hc).finite_of_discrete).subset ?_
  rintro _ ⟨g, rfl⟩
  exact ⟨g, hK g.2, rfl⟩

/- English proof (translation)
Use `sup_le (sup_le GlobalTheory.StepData.KOne_le_KO inf_le_right) ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨t, ht, rfl⟩`. Use `iwahori_le_KO k (Fin n) (diagT_mem_iwahori fun i => ?_)` and prove the remaining obligations. Take `⟨u, -, hu⟩` from `ht i trivial`. Rewrite using `[← hu]`.

Conclude with `(Valuation.integer.integers (valuation k)).one_of_isUnit (Units.isUnit u)`.
-/
private theorem iwC_le_KO (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (n : ℕ) (C : Subgroup 𝓀[k]ˣ) : iwC k n C ≤ KO k (Fin n) := by
  refine sup_le (sup_le GlobalTheory.StepData.KOne_le_KO inf_le_right) ?_
  rintro _ ⟨t, ht, rfl⟩
  refine iwahori_le_KO k (Fin n) (diagT_mem_iwahori fun i => ?_)
  obtain ⟨u, -, hu⟩ := ht i trivial
  rw [← hu]
  exact (Valuation.integer.integers (valuation k)).one_of_isUnit (Units.isUnit u)

/- English proof (translation)
Introduce `k _ _ _ _ n C`. Establish `hc : IsCompact (KO k (Fin n) : Set (GL (Fin n) k))` using `GlobalTheory.SplitFlip.isCompact_KO`. Establish `ho : IsOpen (iwC k n C : Set (GL (Fin n) k))` using `Subgroup.isOpen_mono (H₁ := KOne k (Fin n)) (le_sup_left.trans le_sup_left) GlobalTheory.StepData.isOpen_KOne`. Conclude with `⟨fun x => finOrb_of_compact hc (iwC_le_KO k n C) ho x, fun x => finOrb_of_compact hc le_rfl GlobalTheory.SplitFlip.isOpen_KO x, fun C' => ⟨finOrb_of_compact hc (iwC_le_KO k n C') ho 1, finOrb_of_compact hc le_rfl ho 1⟩⟩`.
-/
theorem UpperTheory.V.AlgebraTools.heckePairIwC :
    ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ) (C : Subgroup 𝓀[k]ˣ), HeckePair (iwC k n C) ∧ HeckePair (KO k (Fin n)) ∧ ∀ (C' : Subgroup 𝓀[k]ˣ), FinOrb (iwC k n C') (iwC k n C) 1 ∧ FinOrb (KO k (Fin n)) (iwC k n C) 1 := by
  intro k _ _ _ _ n C
  have hc : IsCompact (KO k (Fin n) : Set (GL (Fin n) k)) := GlobalTheory.SplitFlip.isCompact_KO
  have ho : IsOpen (iwC k n C : Set (GL (Fin n) k)) :=
    Subgroup.isOpen_mono (H₁ := KOne k (Fin n)) (le_sup_left.trans le_sup_left) GlobalTheory.StepData.isOpen_KOne
  exact ⟨fun x => finOrb_of_compact hc (iwC_le_KO k n C) ho x,
    fun x => finOrb_of_compact hc le_rfl GlobalTheory.SplitFlip.isOpen_KO x,
    fun C' => ⟨finOrb_of_compact hc (iwC_le_KO k n C') ho 1, finOrb_of_compact hc le_rfl ho 1⟩⟩

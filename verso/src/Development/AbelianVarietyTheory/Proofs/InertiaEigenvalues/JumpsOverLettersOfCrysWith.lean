import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Saturated
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.LettersFreeOfRank
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.PointRingCommRing
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.WachModuleUniqueness
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.JumpIffMultNeZero

noncomputable section

open GlobalTheory.WachUse GlobalTheory.AdmLoc Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.IndefiniteRowSideFullHecke.PointRingCommRing

namespace GlobalTheory.WachUse.HeightsProof

section Generic

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL]
    [CommRing O] [Algebra O LL] [TopologicalSpace LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    (W : LocWach PD LL O v n)

/- English proof (translation)
Apply function extensionality and compare values at an arbitrary argument. Express the relevant assertion in an equivalent form by its definition. Consider separately whether the proposition holds or fails. Substitute using the available equality. Simplify using the standard rewrite rules.

Establish an intermediate fact. Simplify using the standard rewrite rules.
-/
theorem letφ_letE (i : ZMod n) : letφ W.φ₀ (letE (i - 1) : LetA O n) = letE i := by
  funext j
  change W.φ₀ ((letE (i - 1) : LetA O n) (j - 1)) = (letE i : LetA O n) j
  by_cases hj : j = i
  · subst hj
    simp [letE]
  · have hj' : j - 1 ≠ i - 1 := fun h => hj (sub_left_injective h)
    simp [letE, hj, hj']

/- English proof (translation)
Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Use the resulting assumption.
-/
theorem φD_letE (T : LocLat G Qp LL O) (i : ZMod n) (x : W.DD T) :
    W.φD T ((letE (i - 1) : LetA O n) • x) = (letE i : LetA O n) • W.φD T x := by
  have := W.φD_smul T (algebraMap (LetA O n) W.EE (letE (i - 1))) x
  rwa [algebraMap_smul, W.φE_ext, algebraMap_smul, letφ_letE] at this

/- English proof (translation)
Assume the hypotheses and unpack their components. A detailed English derivation is pending.
-/
theorem Nl_le (T : LocLat G Qp LL O) (i : ZMod n) : W.Nl T i ≤ W.N T := by
  rintro _ ⟨x, hx, rfl⟩
  exact (W.N T).smul_mem _ hx

/- English proof (translation)
Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem of_heightBounds (T : LocLat G Qp LL O) (M h : ZMod n → ℕ) (hb : HeightBounds W T M h) (i : ZMod n) :
    (∀ x ∈ W.N T, W.Q ^ M i • (letE i : LetA O n) • W.φD T x ∈ W.N T) ∧
      ∀ y ∈ W.N T, W.Q ^ h i • (letE i : LetA O n) • y ∈ W.φpull T := by
  refine ⟨fun x hx => Nl_le W T i ((hb i).1 _ ?_), fun y hy => ?_⟩
  · rw [← φD_letE]
    exact Submodule.subset_span ⟨_, ⟨x, hx, rfl⟩, rfl⟩
  · exact Submodule.span_mono (Set.image_mono (Nl_le W T (i - 1))) ((hb i).2 _ ⟨y, hy, rfl⟩)

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. A detailed English derivation is pending.
-/
theorem jumpsOverLetters_of_crysWith (T : LocLat G Qp LL O) [FiniteDimensional LL ↥(DdR PD T.ρ)]
    (U : ZMod n → Multiset ℤ) (M h : ZMod n → ℕ) (hU : CrysWith PD W.emb T.ρ U)
    (hb : ∀ i, ∀ u ∈ U i, -(M i : ℤ) ≤ u ∧ u ≤ h i) : JumpsOverLetters W T M h := by
  intro i τ hτ a ha
  have h1 := (GlobalTheory.Per.JumpMult.jump_iff_of_finite PD T.ρ τ a).2.2.1 ha
  rw [hU.2 i τ hτ a] at h1
  exact hb i a (Multiset.count_ne_zero.1 (by exact_mod_cast h1))

end Generic

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. A detailed English derivation is pending.
-/
theorem heights_of_finite {l : ℕ} [Fact l.Prime] {P : LocPrime l} {AI : LocAinf l P} {H : LocHW l P}
    {E : LocFon l P AI H} {C : LocCmpT l P AI H E} (hJ : HeightsFromJumps l P AI H E C)
    (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL)
    (hfin : ∀ T : LocLat ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL), FiniteDimensional ↥LL.1 ↥(DdR (P.PD K) T.ρ)) :
    Heights (H.W K s LL h) := by
  intro T U M hh hU hb
  haveI := hfin T
  exact of_heightBounds _ T M hh
    (hJ K s LL h T hU.1 M hh (jumpsOverLetters_of_crysWith _ T U M hh hU hb)).1

/- English proof (translation)
Assume the hypotheses and unpack their components. A detailed English derivation is pending.
-/
theorem heights_of_caseA : ∀ {l : ℕ} [Fact l.Prime] {P : LocPrime l} (AI : LocAinf l P) (H : LocHW l P) (E : LocFon l P AI H) (C : LocCmpT l P AI H E), Nonempty (LocTied l P AI) → GlobalTheory.IndefiniteRowSideFullHecke.PointRingCommRing.HeightsFromJumps l P AI H E C → ∀ (K LL : FinExt l) (h : CaseA K LL), Heights (H.W K 1 LL h.2.2) := by
  rintro l _ P AI H E C ⟨Ti⟩ hJ K LL h
  exact heights_of_finite hJ K 1 LL h.2.2 fun T => (GlobalTheory.Per.TiedDdR.ddR_finrank_le l P AI Ti K LL T.V T.ρ).1

end GlobalTheory.WachUse.HeightsProof

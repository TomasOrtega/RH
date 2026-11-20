import Mathlib
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.ImportsTerTer
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.ImportsBisRest
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.ImportsTerMore
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.ImportsTerExtra
set_option maxSynthPendingDepth 1

noncomputable section

set_option linter.unusedSectionVars false

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial
open ReciprocityTheory.ChartRestriction.G.Geo (ChartBundle chartRing)
open IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg joinCoord restrictChart pullDeg liftVar ptIdx ptCoord chartMon
  IsGradedFrame IsUnitOn FlagPair IsPull fnField IsVertDiv mcIdeal)

namespace JoinPointFlagModel

section Charts

variable {Ω : Type*} [Field Ω] {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

def extChart (t : ∀ k, ι k) : ∀ k : K ⊕ Unit, Sum.elim ι ptIdx k
  | .inl k => t k
  | .inr _ => (0 : Fin 1)

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem restrictChart_extChart (t : ∀ k, ι k) : restrictChart (extChart t) = t :=
  rfl

/- English proof (translation)
Simplify using the standard rewrite rules. Simplify using the standard rewrite rules.
-/
theorem mseg_join (y : (Σ k, ι k) → Ω) (s : ∀ k : K ⊕ Unit, Sum.elim ι ptIdx k) :
    mseg (joinCoord y (ptCoord (Ω := Ω))) s = mseg y (restrictChart s) := by
  simp only [mseg, Fintype.prod_sum_type]
  simp [joinCoord, ptCoord, restrictChart]

/- English proof (translation)
Simplify using the standard rewrite rules. Simplify using the standard rewrite rules.
-/
theorem chartMon_join (y : (Σ k, ι k) → Ω) (s : ∀ k : K ⊕ Unit, Sum.elim ι ptIdx k) (a : K → ℤ) :
    chartMon (joinCoord y (ptCoord (Ω := Ω))) s (pullDeg a) = chartMon y (restrictChart s) a := by
  simp only [chartMon, Fintype.prod_sum_type]
  simp [joinCoord, ptCoord, restrictChart, pullDeg]

variable (O : Type*) [CommRing O] [Algebra O Ω]

/- English proof (translation)
Replace the relevant objects with their definitions. Reduce the equality to equality of the corresponding arguments. By extensionality, compare the relevant components. Simplify using the standard rewrite rules. Prove the components needed by the constructor for the conclusion.

Assume the hypotheses and unpack their components. Supply the required witnesses or components. Assume the hypotheses and unpack their components. Supply the required witnesses or components.
-/
theorem chartRing_join (y : (Σ k, ι k) → Ω) (s : ∀ k : K ⊕ Unit, Sum.elim ι ptIdx k) :
    chartRing O (mseg (joinCoord y (ptCoord (Ω := Ω)))) s = chartRing O (mseg y) (restrictChart s) := by
  unfold chartRing
  congr 1
  ext a
  simp only [Set.mem_range, mseg_join]
  constructor
  · rintro ⟨t, rfl⟩
    exact ⟨restrictChart t, rfl⟩
  · rintro ⟨t, rfl⟩
    exact ⟨extChart t, rfl⟩

/- English proof (translation)
Rewrite the conclusion using the stated equalities.
-/
theorem mem_chartRing_join (y : (Σ k, ι k) → Ω) (s : ∀ k : K ⊕ Unit, Sum.elim ι ptIdx k) (a : Ω) :
    a ∈ chartRing O (mseg (joinCoord y (ptCoord (Ω := Ω)))) s ↔
      a ∈ chartRing O (mseg y) (restrictChart s) := by
  rw [chartRing_join]

end Charts

section Bundles

variable (O : Type*) [CommRing O] {Ω : Type*} [Field Ω] [Algebra O Ω]
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
variable {N : ℕ} {E : Type*} [AddCommGroup E] [Module Ω E]

def pullBundle (y : (Σ k, ι k) → Ω) (B : ChartBundle O (mseg y) N E) :
    ChartBundle O (mseg (joinCoord y (ptCoord (Ω := Ω)))) N E where
  lat s := B.lat (restrictChart s)
  stable s a ha e he := B.stable _ a ((mem_chartRing_join O y s a).mp ha) e he
  frame s hs := by
    rw [chartRing_join]
    exact B.frame _ (by rwa [mseg_join] at hs)
  overlap s t hs ht e he := by
    rw [mseg_join, mseg_join]
    rw [mseg_join] at hs ht
    exact B.overlap _ _ hs ht e he

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem pullBundle_lat (y : (Σ k, ι k) → Ω) (B : ChartBundle O (mseg y) N E)
    (s : ∀ k : K ⊕ Unit, Sum.elim ι ptIdx k) : (pullBundle O y B).lat s = B.lat (restrictChart s) :=
  rfl

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities. Reduce the claim to the hypotheses of an applicable result. Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities.

Assume the hypotheses and unpack their components. A detailed English derivation is pending.
-/
theorem isPull_pullBundle (y : (Σ k, ι k) → Ω) (B : ChartBundle O (mseg y) N E) :
    IsPull O y (ptCoord (Ω := Ω)) B (pullBundle O y B) := by
  intro s _
  rw [pullBundle_lat]
  apply le_antisymm
  · intro v hv
    exact AddSubgroup.subset_closure ⟨1, one_mem _, v, hv, (one_smul _ _).symm⟩
  · rw [AddSubgroup.closure_le]
    rintro _ ⟨a, ha, e, he, rfl⟩
    exact B.stable _ a ((mem_chartRing_join O y s a).mp ha) e he

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Rewrite the indicated hypotheses using the stated equalities. Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. Extract witnesses or component facts from the available result.

Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations.

Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem isGradedFrame_pull (y : (Σ k, ι k) → Ω) {B : ChartBundle O (mseg y) N E}
    {Vs : Fin (N + 1) → Submodule Ω E} {m : Fin N → K → ℤ} {gen : Fin N → E}
    (h : IsGradedFrame O y B Vs m gen) :
    IsGradedFrame O (joinCoord y (ptCoord (Ω := Ω))) (pullBundle O y B) Vs
      (fun i => pullDeg (m i)) gen := by
  intro s hs
  rw [mseg_join] at hs
  obtain ⟨k, f, c, hf, hc, hsum, hl⟩ := h _ hs
  refine ⟨k, f, c, fun l => (mem_chartRing_join O y s _).mpr (hf l),
    fun l => (mem_chartRing_join O y s _).mpr (hc l), hsum, fun l => ?_⟩
  obtain ⟨b, hli, hspan, hiff, hw⟩ := hl l
  refine ⟨b, hli, hspan, fun e => ?_, fun i => ?_⟩
  · rw [pullBundle_lat]
    simp only [mem_chartRing_join]
    exact hiff e
  · obtain ⟨w, ⟨hw0, ⟨n₁, hn₁⟩, ⟨n₂, hn₂⟩⟩, hmem⟩ := hw i
    refine ⟨w, ⟨hw0, ⟨n₁, (mem_chartRing_join O y s _).mpr hn₁⟩,
      ⟨n₂, (mem_chartRing_join O y s _).mpr hn₂⟩⟩, ?_⟩
    rw [chartMon_join]
    exact hmem

end Bundles

section Forms

variable {O : Type*} [CommRing O] {Ω : Type*} [Field Ω] [Algebra O Ω]
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression.
-/
theorem aeval_join (y : (Σ k, ι k) → Ω) (f : ReciprocityTheory.ChartRestriction.G.Geo.MRingOver O ι) :
    aeval (joinCoord y (ptCoord (Ω := Ω))) (rename (liftVar ptIdx) f) = aeval y f := by
  rw [aeval_rename]
  rfl

/- English proof (translation)
Apply function extensionality and compare values at an arbitrary argument. Apply the first step, then apply the next step to every resulting obligation.
-/
theorem pullDeg_sub (a b : K → ℤ) :
    pullDeg (K' := Unit) a - pullDeg (K' := Unit) b = pullDeg (K' := Unit) (a - b) := by
  funext k
  cases k <;> simp [pullDeg]

end Forms

section Pairs

variable (O : Type*) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {Ω : Type*} [Field Ω]
  [Algebra O Ω]
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
variable {N : ℕ} {E : Type*} [AddCommGroup E] [Module Ω E]

def pullFlagPair (y : (Σ k, ι k) → Ω) {B B' : ChartBundle O (mseg y) N E} (F : FlagPair O y B B')
    (hvert : ∀ i, IsVertDiv O (mcIdeal O (joinCoord y (ptCoord (Ω := Ω))))
      (pullDeg (K' := Unit) (F.deg i - F.deg' i)) (rename (liftVar ptIdx) (F.f i))
      (rename (liftVar ptIdx) (F.g i))) :
    FlagPair O (joinCoord y (ptCoord (Ω := Ω))) (pullBundle O y B) (pullBundle O y B') where
  Vs := F.Vs
  mono := F.mono
  dim := F.dim
  top := F.top
  deg i := pullDeg (F.deg i)
  gen := F.gen
  gen_mem := F.gen_mem
  frame := isGradedFrame_pull O y F.frame
  deg' i := pullDeg (F.deg' i)
  gen' := F.gen'
  gen'_mem := F.gen'_mem
  frame' := isGradedFrame_pull O y F.frame'
  f i := rename (liftVar ptIdx) (F.f i)
  g i := rename (liftVar ptIdx) (F.g i)
  rel i := by
    simp only [aeval_join]
    exact F.rel i
  vert i := by
    simp only [pullDeg_sub]
    exact hvert i

/- English proof (translation)
Replace the relevant objects with their definitions. Reduce the claim to the hypotheses of an applicable result. Rewrite the conclusion using the stated equalities. Assume the hypotheses and unpack their components. Establish an intermediate fact.

Simplify using the standard rewrite rules. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Reduce the claim to the hypotheses of an applicable result. Assume the hypotheses and unpack their components.

Prove the first alternative. Prove the second alternative. A detailed English derivation is pending.
-/
theorem fnField_join (y : (Σ k, ι k) → Ω) :
    fnField O (joinCoord y (ptCoord (Ω := Ω))) = fnField O y := by
  unfold fnField
  apply le_antisymm
  · rw [Subfield.closure_le]
    rintro a (ha | ⟨⟨k | u, i, j⟩, rfl⟩)
    · exact Subfield.subset_closure (Or.inl ha)
    · exact Subfield.subset_closure (Or.inr ⟨⟨k, i, j⟩, rfl⟩)
    · have h1 : joinCoord y (ptCoord (Ω := Ω)) ⟨Sum.inr u, i⟩ /
          joinCoord y (ptCoord (Ω := Ω)) ⟨Sum.inr u, j⟩ = 1 := by
        simp [joinCoord, ptCoord]
      simp only at h1 ⊢
      rw [h1]
      exact one_mem _
  · apply Subfield.closure_mono
    rintro a (ha | ⟨⟨k, i, j⟩, rfl⟩)
    · exact Or.inl ha
    · exact Or.inr ⟨⟨Sum.inl k, i, j⟩, rfl⟩

end Pairs

end JoinPointFlagModel

open JoinPointFlagModel in

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities.

Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem JoinPointFlagModel.proof (hIff : FlagPairCharacterisation.Statement.{0, 0, 0})
    (hModel : JoinPointModel.Statement) (hVert : JoinPointVerticalDivisor.Statement) :
    JoinPointFlagModel.Statement := by
  intro O _ _ _ ϖ hϖ Ω _ _ K _ _ ι _ y d hW N E _ _ B B' _ w w' x x' f g hF
  obtain ⟨F, -, -, hdeg, hdeg', hf, hg⟩ :=
    ((hIff O Ω K ι y N E B B' ϖ hϖ hW.multiProj).1 w w' x x' f g).1 hF
  refine ⟨pullBundle O y B, pullBundle O y B',
    pullFlagPair O y F fun i => hVert O Ω K ι y _ _ _ (F.vert i),
    hModel O Ω K ι y d hW, fnField_join O y, isPull_pullBundle O y B, isPull_pullBundle O y B',
    ?_, ?_, ?_, ?_⟩
  · show (fun i => pullDeg (F.deg i)) = _
    rw [hdeg]
  · show (fun i => pullDeg (F.deg' i)) = _
    rw [hdeg']
  · show (fun i => rename (liftVar ptIdx) (F.f i)) = _
    rw [hf]
  · show (fun i => rename (liftVar ptIdx) (F.g i)) = _
    rw [hg]

end GroundTheory.Heights₂.Heights.NumbersDVR

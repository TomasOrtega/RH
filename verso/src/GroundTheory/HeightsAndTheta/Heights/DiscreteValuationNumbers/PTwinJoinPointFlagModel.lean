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
Simplify using `only [mseg, Fintype.prod_sum_type]`. Simplify using `[joinCoord, ptCoord, restrictChart]`.
-/
theorem mseg_join (y : (Σ k, ι k) → Ω) (s : ∀ k : K ⊕ Unit, Sum.elim ι ptIdx k) :
    mseg (joinCoord y (ptCoord (Ω := Ω))) s = mseg y (restrictChart s) := by
  simp only [mseg, Fintype.prod_sum_type]
  simp [joinCoord, ptCoord, restrictChart]

/- English proof (translation)
Simplify using `only [chartMon, Fintype.prod_sum_type]`. Simplify using `[joinCoord, ptCoord, restrictChart, pullDeg]`.
-/
theorem chartMon_join (y : (Σ k, ι k) → Ω) (s : ∀ k : K ⊕ Unit, Sum.elim ι ptIdx k) (a : K → ℤ) :
    chartMon (joinCoord y (ptCoord (Ω := Ω))) s (pullDeg a) = chartMon y (restrictChart s) a := by
  simp only [chartMon, Fintype.prod_sum_type]
  simp [joinCoord, ptCoord, restrictChart, pullDeg]

variable (O : Type*) [CommRing O] [Algebra O Ω]

/- English proof (translation)
Unfold `chartRing`. Use `congr 1`. Use extensionality with `a`. Simplify using `only [Set.mem_range, mseg_join]`. Prove the components needed by the constructor for the conclusion.

Introduce and unpack `⟨t, rfl⟩`. Conclude with `⟨restrictChart t, rfl⟩`. Introduce and unpack `⟨t, rfl⟩`. Conclude with `⟨extChart t, rfl⟩`.
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
Rewrite using `[chartRing_join]`.
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
Introduce `s _`. Rewrite using `[pullBundle_lat]`. Apply `le_antisymm` to reduce the goal to its premises. Introduce `v hv`. Conclude with `AddSubgroup.subset_closure ⟨1, one_mem _, v, hv, (one_smul _ _).symm⟩`.

Rewrite using `[AddSubgroup.closure_le]`. Introduce and unpack `_ ⟨a, ha, e, he, rfl⟩`. Conclude with `B.stable _ a ((mem_chartRing_join O y s a).mp ha) e he`.
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
Introduce `s hs`. Rewrite `hs` using `[mseg_join]`. Take `⟨k, f, c, hf, hc, hsum, hl⟩` from `h _ hs`. Use `⟨k, f, c, fun l => (mem_chartRing_join O y s _).mpr (hf l), fun l => (mem_chartRing_join O y s _).mpr (hc l), hsum, fun l => ?_⟩` and prove the remaining obligations. Take `⟨b, hli, hspan, hiff, hw⟩` from `hl l`.

Use `⟨b, hli, hspan, fun e => ?_, fun i => ?_⟩` and prove the remaining obligations. Rewrite using `[pullBundle_lat]`. Simplify using `only [mem_chartRing_join]`. Conclude with `hiff e`. Take `⟨w, ⟨hw0, ⟨n₁, hn₁⟩, ⟨n₂, hn₂⟩⟩, hmem⟩` from `hw i`.

Use `⟨w, ⟨hw0, ⟨n₁, (mem_chartRing_join O y s _).mpr hn₁⟩, ⟨n₂, (mem_chartRing_join O y s _).mpr hn₂⟩⟩, ?_⟩` and prove the remaining obligations. Rewrite using `[chartMon_join]`. Conclude with `hmem`.
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
Rewrite using `[aeval_rename]`. Both sides reduce to the same expression.
-/
theorem aeval_join (y : (Σ k, ι k) → Ω) (f : ReciprocityTheory.ChartRestriction.G.Geo.MRingOver O ι) :
    aeval (joinCoord y (ptCoord (Ω := Ω))) (rename (liftVar ptIdx) f) = aeval y f := by
  rw [aeval_rename]
  rfl

/- English proof (translation)
Use function extensionality and compare the values at `k`. Apply the tactic sequence `cases k <;> simp [pullDeg]`.
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
Unfold `fnField`. Apply `le_antisymm` to reduce the goal to its premises. Rewrite using `[Subfield.closure_le]`. Introduce and unpack `a (ha | ⟨⟨k | u, i, j⟩, rfl⟩)`. Conclude with `Subfield.subset_closure (Or.inl ha)`.

Conclude with `Subfield.subset_closure (Or.inr ⟨⟨k, i, j⟩, rfl⟩)`. Establish `h1 : joinCoord y (ptCoord (Ω` using `Ω)) ⟨Sum.inr u, i⟩ / joinCoord y (ptCoord (Ω := Ω)) ⟨Sum.inr u, j⟩ = 1 := by`. Simplify using `[joinCoord, ptCoord]`. Simplify using `only at h1 ⊢`. Rewrite using `[h1]`.

Conclude with `one_mem _`. Apply `Subfield.closure_mono` to reduce the goal to its premises. Introduce and unpack `a (ha | ⟨⟨k, i, j⟩, rfl⟩)`. Conclude with `Or.inl ha`. Conclude with `Or.inr ⟨⟨Sum.inl k, i, j⟩, rfl⟩`.
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
Introduce `O _ _ _ ϖ hϖ Ω _ _ K _ _ ι _ y d hW N E _ _ B B' _ w w' x x' f g hF`. Take `⟨F, -, -, hdeg, hdeg', hf, hg⟩` from `((hIff O Ω K ι y N E B B' ϖ hϖ hW.multiProj).1 w w' x x' f g).1 hF`. Use `⟨pullBundle O y B, pullBundle O y B', pullFlagPair O y F fun i => hVert O Ω K ι y _ _ _ (F.vert i), hModel O Ω K ι y d hW, fnField_join O y, isPull_pullBundle O y B, isPull_pullBundle O y B', ?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Use `show (fun i => pullDeg (F.deg i)) = _`. Rewrite using `[hdeg]`.

Use `show (fun i => pullDeg (F.deg' i)) = _`. Rewrite using `[hdeg']`. Use `show (fun i => rename (liftVar ptIdx) (F.f i)) = _`. Rewrite using `[hf]`. Use `show (fun i => rename (liftVar ptIdx) (F.g i)) = _`.

Rewrite using `[hg]`.
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

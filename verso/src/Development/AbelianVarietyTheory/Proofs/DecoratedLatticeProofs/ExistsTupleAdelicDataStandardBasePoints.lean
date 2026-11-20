import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.SplitPart
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.NotIsCompactUnivFv
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.LevChiEqOne
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.XiEqXiOffMul
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsTupleChainAdelicDataStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsMemberStepCharts
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsAdelicReadingLastStepTrivialOffLevelStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsPointOfDecoratedLatticeUniqueStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.UG
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.Core.Rk GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.KJInf Formalism.L2.Ker
open GlobalTheory.SeeSaw GlobalTheory.Unf

namespace GlobalTheory.AdForm

set_option maxHeartbeats 1000000 in

/- English proof (translation)
Introduce `B X I hI hP l Z u a`. Take `⟨Ch, hF, A, hA, hU, hk⟩` from `GlobalTheory.T.exists_tupleChain_adelicData I hI hP l Z u a`. Take `⟨A₁, hA₁, hk₁, hm₁⟩` from `GlobalTheory.T.exists_adelicReading_lastStep_trivial_off_level I hI hP l Z u a Ch A hA hU`. Establish `hkb : ∀ i, i ≤ B.R.m → ∀ β β', A₁.kb i β = A₁.kb i β'`. Introduce `i hi β β'`.

Break down `Nat.lt_or_eq_of_le hi with h | rfl` into its components or cases. Rewrite using `[hk₁ i h, hk₁ i h, hk i h, hk i h]`. Take `⟨hu⟩` from `hU`. Rewrite using `[hu.uniq β, hu.uniq β']`. Set `A₂ : TwDat I l Z u a Ch` to `{ A₁ with kA := fun i β => A₁.kA i (Classical.choice ⟨β⟩) xr := fun i β => A₁.xr i (Classical.choice ⟨β⟩) }`.

Establish `hA₂ : A₂.Is`. Use `{ hA₁ with kA := fun i hi β => ?_ }` and prove the remaining obligations. Take `⟨h1, h2, h3⟩` from `hA₁.kA i hi (Classical.choice ⟨β⟩)`. Use `⟨h1, ?_, h3⟩` and prove the remaining obligations. Rewrite using `[h2, hkb i hi]`.

Establish `hd : Disjoint (B.primes X).vGs (I.Q a)` using `(LevTwist.levOk_twists B X I hI).2.1.mono_right (I.Q_subset_SQ a)`. Use `⟨Ch, hF, A₂, hA₂, hU, ?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `i ⟨b⟩`. Establish `: NeZero (B.R.N i)` using `⟨(B.R.N_pos i).ne'⟩`. Take `⟨p, -⟩` from `exists_ptAt (R := B.R) I.sel (I.tup a) (I.cst a) (u := u) (j := i) (Formalism.L2.Col.DecoF.base _ _ _ _ _)`.

Conclude with `⟨A₂.chOf i ((I.stp u a i).cl b p)⟩`. Introduce `i hi β β'`. Use `⟨?_, rfl, rfl⟩` and prove the remaining obligations. Establish `e1` using `(hA₁.base i hi β).1`. Establish `e2` using `(hA₁.base i hi β').1`.

Rewrite `e1` using `[hkb i hi β β']`. Conclude with `GlobalTheory.T.isPointOfDecoratedLattice_unique _ _ _ _ (IsPtOf.of_extTo (I.Q_subset_SQ a) hd e1) (IsPtOf.of_extTo (I.Q_subset_SQ a) hd e2)`. Introduce `i hi β`. Conclude with `(hk₁ i hi β).trans (hk i hi β)`. Introduce `i hi β v hv hq`.

Use `⟨?_, fun i hi β => (hk₁ i hi β).trans (hk i hi β)⟩` and prove the remaining obligations. Break down `hq with h | h` into its components or cases. Use `show Formalism.UG.bc _ (A₁.kb i β) = 1`. Rewrite using `[hk₁ i h, hk i h]`. Conclude with `(MemChart.kStd_spec l.pr u _).2.1 v hv`.

Break down `Nat.lt_or_eq_of_le hi with h' | rfl` into its components or cases. Use `show Formalism.UG.bc _ (A₁.kb i β) = 1`. Rewrite using `[hk₁ i h', hk i h']`. Conclude with `(MemChart.kStd_spec l.pr u _).2.1 v hv`. Conclude with `hm₁ β v hv h`.
-/
theorem exists_twDat_baseStd : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (u : B.Word) (a : I.ι), ∃ (Ch : ℕ → Type) (_ : ∀ i, Fintype (Ch i)) (A : TwDat I l Z u a Ch), A.Is ∧ Nonempty (Unique (Ch B.R.m)) ∧ (∀ i, Nonempty (Idx I.sel (I.tup a) (I.idx a) i) → Nonempty (Ch i)) ∧ GlobalTheory.QTw.BaseCommon A ∧ (∀ i, i < B.R.m → ∀ β, A.kb i β = TC.kStd X u (B.R.N i)) ∧ ∀ i, i ≤ B.R.m → ∀ β (v : HeightOneSpectrum (𝓞 B.host.F)), ((B.T u : ℕ) : 𝓞 B.host.F) ∉ v.asIdeal → (i < B.R.m ∨ ¬ I.UnderQ a v) → Formalism.UG.bc (Formalism.UG.prV (E := B.host.E) v) (A.kb i β) = 1 ∧ ∀ i, i < B.R.m → ∀ β, A.kb i β = TC.kStd X u (B.R.N i) := by
  intro B X I hI hP l Z u a
  obtain ⟨Ch, hF, A, hA, hU, hk⟩ := GlobalTheory.T.exists_tupleChain_adelicData I hI hP l Z u a
  obtain ⟨A₁, hA₁, hk₁, hm₁⟩ := GlobalTheory.T.exists_adelicReading_lastStep_trivial_off_level I hI hP l Z u a Ch A hA hU
  have hkb : ∀ i, i ≤ B.R.m → ∀ β β', A₁.kb i β = A₁.kb i β' := by
    intro i hi β β'
    rcases Nat.lt_or_eq_of_le hi with h | rfl
    · rw [hk₁ i h, hk₁ i h, hk i h, hk i h]
    · obtain ⟨hu⟩ := hU
      rw [hu.uniq β, hu.uniq β']
  let A₂ : TwDat I l Z u a Ch := { A₁ with
    kA := fun i β => A₁.kA i (Classical.choice ⟨β⟩)
    xr := fun i β => A₁.xr i (Classical.choice ⟨β⟩) }
  have hA₂ : A₂.Is := by
    refine { hA₁ with kA := fun i hi β => ?_ }
    obtain ⟨h1, h2, h3⟩ := hA₁.kA i hi (Classical.choice ⟨β⟩)
    refine ⟨h1, ?_, h3⟩
    rw [h2, hkb i hi]
  have hd : Disjoint (B.primes X).vGs (I.Q a) := (LevTwist.levOk_twists B X I hI).2.1.mono_right (I.Q_subset_SQ a)
  refine ⟨Ch, hF, A₂, hA₂, hU, ?_, ?_, ?_, ?_⟩
  · intro i ⟨b⟩
    have : NeZero (B.R.N i) := ⟨(B.R.N_pos i).ne'⟩
    obtain ⟨p, -⟩ := exists_ptAt (R := B.R) I.sel (I.tup a) (I.cst a) (u := u) (j := i) (Formalism.L2.Col.DecoF.base _ _ _ _ _)
    exact ⟨A₂.chOf i ((I.stp u a i).cl b p)⟩
  · intro i hi β β'
    refine ⟨?_, rfl, rfl⟩
    have e1 := (hA₁.base i hi β).1
    have e2 := (hA₁.base i hi β').1
    rw [hkb i hi β β'] at e1
    exact GlobalTheory.T.isPointOfDecoratedLattice_unique _ _ _ _ (IsPtOf.of_extTo (I.Q_subset_SQ a) hd e1) (IsPtOf.of_extTo (I.Q_subset_SQ a) hd e2)
  · intro i hi β
    exact (hk₁ i hi β).trans (hk i hi β)
  · intro i hi β v hv hq
    refine ⟨?_, fun i hi β => (hk₁ i hi β).trans (hk i hi β)⟩
    rcases hq with h | h
    · show Formalism.UG.bc _ (A₁.kb i β) = 1
      rw [hk₁ i h, hk i h]
      exact (MemChart.kStd_spec l.pr u _).2.1 v hv
    · rcases Nat.lt_or_eq_of_le hi with h' | rfl
      · show Formalism.UG.bc _ (A₁.kb i β) = 1
        rw [hk₁ i h', hk i h']
        exact (MemChart.kStd_spec l.pr u _).2.1 v hv
      · exact hm₁ β v hv h

end GlobalTheory.AdForm

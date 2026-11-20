import Development.AbelianVarietyTheory.Definitions.Foundations.T2SpaceAdeleRing
import Development.AbelianVarietyTheory.Definitions.Foundations.NotIsSplitOfIsInertAt
import Development.AbelianVarietyTheory.Definitions.Foundations.GLintEqKOAndPrincEqKOne
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.GaussianBinomialClosedForm
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.TrivialParameterBound
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PairwiseDisjointCell
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.PRep
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt Hecke ordL)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
open GlobalTheory.LGrp (bcParam)
open GlobalTheory.LFun (toCompl locMat locChar IsSplitChart IsInertChart IsFrameAt KGL IsSatVecGL IsSatVecU eulerFac UnrAt LvTw dv Fam)

namespace GlobalTheory.LFun

/- English proof (translation)
Use `set e : Fin n ⊕ Fin n ≃ Fin (n + n) := finSumFinEquiv`. Establish `hl0 : ∀ {X : Type} [AddCommGroup X] (x y : Fin n → X), pairVec e (x + y) 0 = pairVec e x 0 + pairVec e y 0`. Apply the tactic sequence `intro X _ x y; funext j; obtain ⟨i | i, rfl⟩ := e.surjective j <;> simp`. Establish `hr0 : ∀ {X : Type} [AddCommGroup X] (x y : Fin n → X), pairVec e 0 (x + y) = pairVec e 0 x + pairVec e 0 y`. Apply the tactic sequence `intro X _ x y; funext j; obtain ⟨i | i, rfl⟩ := e.surjective j <;> simp`.

Establish `hls : ∀ (c : Formalism.UG.Ov E w) (x : Fin n → w.adicCompletion E), pairVec e (c • x) 0 = c • pairVec e x 0`. Apply the tactic sequence `intro c x; funext j; obtain ⟨i | i, rfl⟩ := e.surjective j <;> simp`. Establish `hrs : ∀ (c : Formalism.UG.Ov E w) (x : Fin n → w.adicCompletion E), pairVec e 0 (c • x) = c • pairVec e 0 x`. Apply the tactic sequence `intro c x; funext j; obtain ⟨i | i, rfl⟩ := e.surjective j <;> simp`. Establish `hz : pairVec e (0 : Fin n → w.adicCompletion E) 0 = 0`.

Apply the tactic sequence `funext j; obtain ⟨i | i, rfl⟩ := e.surjective j <;> simp`. Establish `hsplit : ∀ (x y : Fin n → w.adicCompletion E), pairVec e x y = pairVec e x 0 + pairVec e 0 y`. Apply the tactic sequence `intro x y; funext j; obtain ⟨i | i, rfl⟩ := e.surjective j <;> simp`. Use `set φ : (Fin n → E) → (Fin n → w.adicCompletion E) := fun x i => algebraMap E (w.adicCompletion E) (x i)`. Apply `le_antisymm` to reduce the goal to its premises.

Use `Submodule.span_le.2 ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨x, hx, rfl⟩`. Rewrite `hx`, the goal using `[SetLike.mem_coe, mem_sumLat]`. Conclude with `⟨Submodule.subset_span ⟨_, hx.1, rfl⟩, Submodule.subset_span ⟨_, hx.2, rfl⟩⟩`. Introduce `z hz'`.

Rewrite `hz'` using `[← pairVec_eta e z, pairVec_mem_sumLat]`. Rewrite using `[← pairVec_eta e z, hsplit]`. Use `Submodule.add_mem _ ?_ ?_` and prove the remaining obligations. Take `⟨u, hu⟩ : ∃ u, u = fun i => z (e (.inl i))` from `⟨_, rfl⟩`. Establish `hu'` using `hz'.1`.

Rewrite `hu'`, the goal using `[← hu]`. Use `clear hu`. Proceed by induction on `hu' using Submodule.span_induction with`. Consider the case `mem x hx`. Take `⟨y, hy, rfl⟩` from `hx`.

Use `Submodule.subset_span ⟨pairVec e y 0, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[SetLike.mem_coe, pairVec_mem_sumLat]`. Conclude with `⟨hy, L.zero_mem⟩`. Apply the tactic sequence `funext j; obtain ⟨i | i, rfl⟩ := e.surjective j <;> simp`. Consider the case `zero => rw [hz]`.

Conclude with `Submodule.zero_mem _`. Consider the case `add x y _ _ hx hy => rw [hl0]`. Conclude with `Submodule.add_mem _ hx hy`. Consider the case `smul c x _ hx => rw [hls]`. Conclude with `Submodule.smul_mem _ c hx`.

Take `⟨u, hu⟩ : ∃ u, u = fun i => z (e (.inr i))` from `⟨_, rfl⟩`. Establish `hu'` using `hz'.2`. Rewrite `hu'`, the goal using `[← hu]`. Use `clear hu`. Proceed by induction on `hu' using Submodule.span_induction with`.

Consider the case `mem x hx`. Take `⟨y, hy, rfl⟩` from `hx`. Use `Submodule.subset_span ⟨pairVec e 0 y, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[SetLike.mem_coe, pairVec_mem_sumLat]`. Conclude with `⟨L.zero_mem, hy⟩`.

Apply the tactic sequence `funext j; obtain ⟨i | i, rfl⟩ := e.surjective j <;> simp`. Consider the case `zero => rw [hz]`. Conclude with `Submodule.zero_mem _`. Consider the case `add x y _ _ hx hy => rw [hr0]`. Conclude with `Submodule.add_mem _ hx hy`.

Consider the case `smul c x _ hx => rw [hrs]`. Conclude with `Submodule.smul_mem _ c hx`.
-/
theorem latAt_sumLat_self {E : Type} [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E)) {n : ℕ}
    (L : Submodule (𝓞 E) (Fin n → E)) :
    latAt w (sumLat finSumFinEquiv L L) = sumLat finSumFinEquiv (latAt w L) (latAt w L) := by
  set e : Fin n ⊕ Fin n ≃ Fin (n + n) := finSumFinEquiv
  have hl0 : ∀ {X : Type} [AddCommGroup X] (x y : Fin n → X),
      pairVec e (x + y) 0 = pairVec e x 0 + pairVec e y 0 := by
    intro X _ x y; funext j; obtain ⟨i | i, rfl⟩ := e.surjective j <;> simp
  have hr0 : ∀ {X : Type} [AddCommGroup X] (x y : Fin n → X),
      pairVec e 0 (x + y) = pairVec e 0 x + pairVec e 0 y := by
    intro X _ x y; funext j; obtain ⟨i | i, rfl⟩ := e.surjective j <;> simp
  have hls : ∀ (c : Formalism.UG.Ov E w) (x : Fin n → w.adicCompletion E), pairVec e (c • x) 0 = c • pairVec e x 0 := by
    intro c x; funext j; obtain ⟨i | i, rfl⟩ := e.surjective j <;> simp
  have hrs : ∀ (c : Formalism.UG.Ov E w) (x : Fin n → w.adicCompletion E), pairVec e 0 (c • x) = c • pairVec e 0 x := by
    intro c x; funext j; obtain ⟨i | i, rfl⟩ := e.surjective j <;> simp
  have hz : pairVec e (0 : Fin n → w.adicCompletion E) 0 = 0 := by
    funext j; obtain ⟨i | i, rfl⟩ := e.surjective j <;> simp
  have hsplit : ∀ (x y : Fin n → w.adicCompletion E), pairVec e x y = pairVec e x 0 + pairVec e 0 y := by
    intro x y; funext j; obtain ⟨i | i, rfl⟩ := e.surjective j <;> simp
  set φ : (Fin n → E) → (Fin n → w.adicCompletion E) := fun x i => algebraMap E (w.adicCompletion E) (x i)
  apply le_antisymm
  · refine Submodule.span_le.2 ?_
    rintro _ ⟨x, hx, rfl⟩
    rw [SetLike.mem_coe, mem_sumLat] at hx ⊢
    exact ⟨Submodule.subset_span ⟨_, hx.1, rfl⟩, Submodule.subset_span ⟨_, hx.2, rfl⟩⟩
  · intro z hz'
    rw [← pairVec_eta e z, pairVec_mem_sumLat] at hz'
    rw [← pairVec_eta e z, hsplit]
    refine Submodule.add_mem _ ?_ ?_
    · obtain ⟨u, hu⟩ : ∃ u, u = fun i => z (e (.inl i)) := ⟨_, rfl⟩
      have hu' := hz'.1
      rw [← hu] at hu' ⊢
      clear hu
      induction hu' using Submodule.span_induction with
      | mem x hx =>
        obtain ⟨y, hy, rfl⟩ := hx
        refine Submodule.subset_span ⟨pairVec e y 0, ?_, ?_⟩
        · rw [SetLike.mem_coe, pairVec_mem_sumLat]; exact ⟨hy, L.zero_mem⟩
        · funext j; obtain ⟨i | i, rfl⟩ := e.surjective j <;> simp
      | zero => rw [hz]; exact Submodule.zero_mem _
      | add x y _ _ hx hy => rw [hl0]; exact Submodule.add_mem _ hx hy
      | smul c x _ hx => rw [hls]; exact Submodule.smul_mem _ c hx
    · obtain ⟨u, hu⟩ : ∃ u, u = fun i => z (e (.inr i)) := ⟨_, rfl⟩
      have hu' := hz'.2
      rw [← hu] at hu' ⊢
      clear hu
      induction hu' using Submodule.span_induction with
      | mem x hx =>
        obtain ⟨y, hy, rfl⟩ := hx
        refine Submodule.subset_span ⟨pairVec e 0 y, ?_, ?_⟩
        · rw [SetLike.mem_coe, pairVec_mem_sumLat]; exact ⟨L.zero_mem, hy⟩
        · funext j; obtain ⟨i | i, rfl⟩ := e.surjective j <;> simp
      | zero => rw [hz]; exact Submodule.zero_mem _
      | add x y _ _ hx hy => rw [hr0]; exact Submodule.add_mem _ hx hy
      | smul c x _ hx => rw [hrs]; exact Submodule.smul_mem _ c hx

/- English proof (translation)
Introduce `E _ _ w n L a ha y`. Use `set e : Fin n ⊕ Fin n ≃ Fin (n + n) := finSumFinEquiv`. Rewrite using `[latAt_sumLat_self, ← pairVec_eta e y, val_blkGL, blkMat_mulVec, pairVec_mem_sumLat, ← ha, ← ha]`. Prove the components needed by the constructor for the conclusion. Introduce `h; exact ⟨fun i => by simpa using h (e (.inl i)), fun i => by simpa using h (e (.inr i))⟩`.

Apply the tactic sequence `rintro ⟨h1, h2⟩ j; obtain ⟨i | i, rfl⟩ := e.surjective j <;> simp [h1, h2]`.
-/
theorem isFrameAt_sumLat_blkGL : ∀ (E : Type) [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E)) (n : ℕ) (L : Submodule (𝓞 E) (Fin n → E)) (a : GL (Fin n) (w.adicCompletion E)), IsFrameAt w L a → IsFrameAt w (sumLat finSumFinEquiv L L) (blkGL finSumFinEquiv (a, a)) := by
  intro E _ _ w n L a ha y
  set e : Fin n ⊕ Fin n ≃ Fin (n + n) := finSumFinEquiv
  rw [latAt_sumLat_self, ← pairVec_eta e y, val_blkGL, blkMat_mulVec, pairVec_mem_sumLat,
    ← ha, ← ha]
  constructor
  · intro h; exact ⟨fun i => by simpa using h (e (.inl i)), fun i => by simpa using h (e (.inr i))⟩
  · rintro ⟨h1, h2⟩ j; obtain ⟨i | i, rfl⟩ := e.surjective j <;> simp [h1, h2]

end GlobalTheory.LFun

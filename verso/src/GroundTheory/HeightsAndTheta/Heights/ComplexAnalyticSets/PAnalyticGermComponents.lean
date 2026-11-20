import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StAnalyticGermComponents
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StAnalyticGermsNoetherian
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open Topology Filter

namespace AnalyticGermComponents

variable {σ : Type} [Fintype σ]

def vanishingIdeal (X : Set (σ → ℂ)) (w : σ → ℂ) : Ideal (holGerms w) where
  carrier := {φ | ∃ f : (σ → ℂ) → ℂ, (f : Germ (𝓝 w) ℂ) = (φ : Germ (𝓝 w) ℂ) ∧ ∀ᶠ z in 𝓝 w, z ∈ X → f z = 0}
  add_mem' := by
    rintro a b ⟨f, hf, hf0⟩ ⟨g, hg, hg0⟩
    refine ⟨f + g, ?_, ?_⟩
    · show ((f + g : (σ → ℂ) → ℂ) : Germ (𝓝 w) ℂ) = (a : Germ (𝓝 w) ℂ) + (b : Germ (𝓝 w) ℂ)
      rw [← hf, ← hg]
      rfl
    · filter_upwards [hf0, hg0] with z h1 h2 hz
      simp [h1 hz, h2 hz]
  zero_mem' := ⟨0, rfl, Eventually.of_forall fun _ _ => rfl⟩
  smul_mem' := by
    rintro c a ⟨f, hf, hf0⟩
    obtain ⟨h, -, hh⟩ := c.2
    refine ⟨h * f, ?_, ?_⟩
    · show ((h * f : (σ → ℂ) → ℂ) : Germ (𝓝 w) ℂ) = (c : Germ (𝓝 w) ℂ) * (a : Germ (𝓝 w) ℂ)
      rw [← hh, ← hf]
      rfl
    · filter_upwards [hf0] with z h1 hz
      simp [h1 hz]

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨g, hg, hg0⟩`. Establish `he : g =ᶠ[𝓝 w] f` using `Germ.coe_eq.1 hg`. Use `filter_upwards [hg0, he] with z h1 h2 hz`. Rewrite using `[← h2]`.

Conclude with `h1 hz`. Introduce `h`. Conclude with `⟨f, rfl, h⟩`.
-/
theorem mem_vanishingIdeal_iff {X : Set (σ → ℂ)} {w : σ → ℂ} {f : (σ → ℂ) → ℂ} (hf : AnalyticAt ℂ f w) :
    (⟨(f : Germ (𝓝 w) ℂ), f, hf, rfl⟩ : holGerms w) ∈ vanishingIdeal X w ↔ ∀ᶠ z in 𝓝 w, z ∈ X → f z = 0 := by
  constructor
  · rintro ⟨g, hg, hg0⟩
    have he : g =ᶠ[𝓝 w] f := Germ.coe_eq.1 hg
    filter_upwards [hg0, he] with z h1 h2 hz
    rw [← h2]
    exact h1 hz
  · intro h
    exact ⟨f, rfl, h⟩

/- English proof (translation)
Introduce and unpack `φ ⟨f, hf, hf0⟩`. Use `⟨f, hf, ?_⟩` and prove the remaining obligations. Use `filter_upwards [hf0] with z h hz`. Conclude with `h (hXX' hz)`.
-/
theorem vanishingIdeal_anti {X X' : Set (σ → ℂ)} {w : σ → ℂ} (hXX' : X' ⊆ X) :
    vanishingIdeal X w ≤ vanishingIdeal X' w := by
  rintro φ ⟨f, hf, hf0⟩
  refine ⟨f, hf, ?_⟩
  filter_upwards [hf0] with z h hz
  exact h (hXX' hz)

/- English proof (translation)
Take `⟨N, k, F, hN, hwN, hF, hXN⟩` from `hX`. Use `⟨N ∩ {z | AnalyticAt ℂ f z}, k + 1, Fin.cons f F, hN.inter (isOpen_analyticAt ℂ f), ⟨hwN, hf⟩, ?_, ?_⟩` and prove the remaining obligations. Introduce `i`. Use `Fin.cases ?_ (fun j => ?_) i` and prove the remaining obligations. Introduce `z hz`.

Simplify using `using hz.2`. Introduce `z hz`. Simplify using `using hF j z hz.1`. Use extensionality with `z`. Establish `e` using `Set.ext_iff.1 hXN z`.

Simplify using `only [Set.mem_inter_iff, Set.mem_ofPred_eq] at e ⊢`. Simplify using `only [Fin.forall_fin_succ, Fin.cons_zero, Fin.cons_succ]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨⟨hzX, hfz⟩, hzN, hza⟩`. Conclude with `⟨⟨hzN, hza⟩, hfz, (e.1 ⟨hzX, hzN⟩).2⟩`.

Introduce and unpack `⟨⟨hzN, hza⟩, hfz, hFz⟩`. Conclude with `⟨⟨(e.2 ⟨hzN, hFz⟩).1, hfz⟩, hzN, hza⟩`.
-/
theorem isAnalyticNear_inter_zero {X : Set (σ → ℂ)} {w : σ → ℂ} {f : (σ → ℂ) → ℂ}
    (hX : IsAnalyticNear X w) (hf : AnalyticAt ℂ f w) : IsAnalyticNear (X ∩ {z | f z = 0}) w := by
  obtain ⟨N, k, F, hN, hwN, hF, hXN⟩ := hX
  refine ⟨N ∩ {z | AnalyticAt ℂ f z}, k + 1, Fin.cons f F, hN.inter (isOpen_analyticAt ℂ f), ⟨hwN, hf⟩, ?_, ?_⟩
  · intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · intro z hz
      simpa using hz.2
    · intro z hz
      simpa using hF j z hz.1
  · ext z
    have e := Set.ext_iff.1 hXN z
    simp only [Set.mem_inter_iff, Set.mem_ofPred_eq] at e ⊢
    simp only [Fin.forall_fin_succ, Fin.cons_zero, Fin.cons_succ]
    constructor
    · rintro ⟨⟨hzX, hfz⟩, hzN, hza⟩
      exact ⟨⟨hzN, hza⟩, hfz, (e.1 ⟨hzX, hzN⟩).2⟩
    · rintro ⟨⟨hzN, hza⟩, hfz, hFz⟩
      exact ⟨⟨(e.2 ⟨hzN, hFz⟩).1, hfz⟩, hzN, hza⟩

/- English proof (translation)
Assume the negation of the conclusion as `h0`. Apply `hng` to reduce the goal to its premises. Establish `hev : ∀ᶠ z in 𝓝 w, f z ≠ 0` using `hf.continuousAt.eventually_ne h0`. Use `filter_upwards [hfg, hev] with z h1 h2 hz`. Conclude with `(mul_eq_zero.1 (h1 hz)).resolve_left h2`.
-/
theorem apply_eq_zero_of_not {X : Set (σ → ℂ)} {w : σ → ℂ} {f g : (σ → ℂ) → ℂ} (hf : AnalyticAt ℂ f w)
    (hfg : ∀ᶠ z in 𝓝 w, z ∈ X → f z * g z = 0) (hng : ¬ ∀ᶠ z in 𝓝 w, z ∈ X → g z = 0) : f w = 0 := by
  by_contra h0
  apply hng
  have hev : ∀ᶠ z in 𝓝 w, f z ≠ 0 := hf.continuousAt.eventually_ne h0
  filter_upwards [hfg, hev] with z h1 h2 hz
  exact (mul_eq_zero.1 (h1 hz)).resolve_left h2

/- English proof (translation)
Use `lt_of_le_of_ne (vanishingIdeal_anti Set.inter_subset_left) fun heq => hnf ?_` and prove the remaining obligations. Establish `hm : (⟨(f : Germ (𝓝 w) ℂ), f, hf, rfl⟩ : holGerms w) ∈ vanishingIdeal (X ∩ {z | f z = 0}) w` using `(mem_vanishingIdeal_iff hf).2 (Eventually.of_forall fun z hz => hz.2)`. Rewrite `hm` using `[← heq]`. Conclude with `(mem_vanishingIdeal_iff hf).1 hm`.
-/
theorem vanishingIdeal_lt {X : Set (σ → ℂ)} {w : σ → ℂ} {f : (σ → ℂ) → ℂ} (hf : AnalyticAt ℂ f w)
    (hnf : ¬ ∀ᶠ z in 𝓝 w, z ∈ X → f z = 0) :
    vanishingIdeal X w < vanishingIdeal (X ∩ {z | f z = 0}) w := by
  refine lt_of_le_of_ne (vanishingIdeal_anti Set.inter_subset_left) fun heq => hnf ?_
  have hm : (⟨(f : Germ (𝓝 w) ℂ), f, hf, rfl⟩ : holGerms w) ∈ vanishingIdeal (X ∩ {z | f z = 0}) w :=
    (mem_vanishingIdeal_iff hf).2 (Eventually.of_forall fun z hz => hz.2)
  rw [← heq] at hm
  exact (mem_vanishingIdeal_iff hf).1 hm

/- English proof (translation)
It suffices to establish `H : ∀ J : Ideal (holGerms w), ∀ X : Set (σ → ℂ), vanishingIdeal X w = J → IsAnalyticNear X w → w ∈ X → ∃ s : Finset (Set (σ → ℂ)), (∀ Y ∈ s, IsAnalyticNear Y w ∧ GermIrreducibleAt Y w) ∧ ∃ W ∈ 𝓝 w, X ∩ W = (⋃ Y ∈ s, Y) ∩ W from H _ X rfl hX hw`. Introduce `J`. Proceed by induction on `J using WellFoundedGT.induction with`. Consider the case `_ J ih`. Introduce `X hJ hX hw`.

Distinguish the cases in `hirr : GermIrreducibleAt X w`. Use `⟨{X}, ?_, Set.univ, Filter.univ_mem, ?_⟩` and prove the remaining obligations. Introduce `Y hY`. Rewrite `hY` using `[Finset.mem_singleton]`. Conclude with `hY ▸ ⟨hX, hirr⟩`.

Simplify using the standard rewrite rules. Choose the witnesses or unpack the hypotheses as in `⟨f, g, hf, hg, hfg, hnf, hng⟩ : ∃ f g : (σ → ℂ) → ℂ, AnalyticAt ℂ f w ∧ AnalyticAt ℂ g w ∧ (∀ᶠ z in 𝓝 w, z ∈ X → f z * g z = 0) ∧ ¬ (∀ᶠ z in 𝓝 w, z ∈ X → f z = 0) ∧ ¬ (∀ᶠ z in 𝓝 w, z ∈ X → g z = 0) := by`. Assume the negation of the conclusion as `hcon`. Use `hirr ⟨hw, fun f g hf hg hfg => ?_⟩` and prove the remaining obligations. Assume the negation of the conclusion as `h`.

Rewrite `h` using `[not_or]`. Conclude with `hcon ⟨f, g, hf, hg, hfg, h.1, h.2⟩`. Establish `hgf : ∀ᶠ z in 𝓝 w, z ∈ X → g z * f z = 0` using `by filter_upwards [hfg] with z h hz`. Rewrite using `[mul_comm]`. Conclude with `h hz`.

Establish `hfw : f w = 0` using `apply_eq_zero_of_not hf hfg hng`. Establish `hgw : g w = 0` using `apply_eq_zero_of_not hg hgf hnf`. Take `⟨s₁, hs₁, W₁, hW₁, hX₁⟩` from `ih _ (hJ ▸ vanishingIdeal_lt hf hnf) _ rfl (isAnalyticNear_inter_zero hX hf) ⟨hw, hfw⟩`. Take `⟨s₂, hs₂, W₂, hW₂, hX₂⟩` from `ih _ (hJ ▸ vanishingIdeal_lt hg hng) _ rfl (isAnalyticNear_inter_zero hX hg) ⟨hw, hgw⟩`. Use `⟨s₁ ∪ s₂, ?_, W₁ ∩ W₂ ∩ {z | z ∈ X → f z * g z = 0}, inter_mem (inter_mem hW₁ hW₂) hfg, ?_⟩` and prove the remaining obligations.

Introduce `Y hY`. Break down `Finset.mem_union.1 hY with h | h` into its components or cases. Conclude with `hs₁ Y h`. Conclude with `hs₂ Y h`. Use extensionality with `z`.

Establish `e₁` using `Set.ext_iff.1 hX₁ z`. Establish `e₂` using `Set.ext_iff.1 hX₂ z`. Simplify using `only [Set.mem_inter_iff, Set.mem_ofPred_eq, Set.mem_iUnion, exists_prop] at e₁ e₂`. Simplify using `only [Set.mem_inter_iff, Set.mem_ofPred_eq, Set.mem_iUnion, exists_prop, Finset.mem_union]`. Prove the components needed by the constructor for the conclusion.

Introduce and unpack `⟨hzX, ⟨hz₁, hz₂⟩, hz0⟩`. Use `⟨?_, ⟨hz₁, hz₂⟩, hz0⟩` and prove the remaining obligations. Break down `mul_eq_zero.1 (hz0 hzX) with h | h` into its components or cases. Take `⟨Y, hY, hzY⟩` from `(e₁.1 ⟨⟨hzX, h⟩, hz₁⟩).1`. Conclude with `⟨Y, Or.inl hY, hzY⟩`.

Take `⟨Y, hY, hzY⟩` from `(e₂.1 ⟨⟨hzX, h⟩, hz₂⟩).1`. Conclude with `⟨Y, Or.inr hY, hzY⟩`. Introduce and unpack `⟨⟨Y, hY, hzY⟩, ⟨hz₁, hz₂⟩, hz0⟩`. Use `⟨?_, ⟨hz₁, hz₂⟩, hz0⟩` and prove the remaining obligations. Break down `hY with hY | hY` into its components or cases.

Conclude with `(e₁.2 ⟨⟨Y, hY, hzY⟩, hz₁⟩).1.1`. Conclude with `(e₂.2 ⟨⟨Y, hY, hzY⟩, hz₂⟩).1.1`.
-/
theorem exists_finset {w : σ → ℂ} (hN : IsNoetherianRing (holGerms w)) (X : Set (σ → ℂ))
    (hX : IsAnalyticNear X w) (hw : w ∈ X) :
    ∃ s : Finset (Set (σ → ℂ)), (∀ Y ∈ s, IsAnalyticNear Y w ∧ GermIrreducibleAt Y w) ∧
      ∃ W ∈ 𝓝 w, X ∩ W = (⋃ Y ∈ s, Y) ∩ W := by
  classical
  suffices H : ∀ J : Ideal (holGerms w), ∀ X : Set (σ → ℂ), vanishingIdeal X w = J → IsAnalyticNear X w →
      w ∈ X → ∃ s : Finset (Set (σ → ℂ)), (∀ Y ∈ s, IsAnalyticNear Y w ∧ GermIrreducibleAt Y w) ∧
        ∃ W ∈ 𝓝 w, X ∩ W = (⋃ Y ∈ s, Y) ∩ W from H _ X rfl hX hw
  intro J
  induction J using WellFoundedGT.induction with
  | _ J ih =>
  intro X hJ hX hw
  by_cases hirr : GermIrreducibleAt X w
  · refine ⟨{X}, ?_, Set.univ, Filter.univ_mem, ?_⟩
    · intro Y hY
      rw [Finset.mem_singleton] at hY
      exact hY ▸ ⟨hX, hirr⟩
    · simp
  obtain ⟨f, g, hf, hg, hfg, hnf, hng⟩ : ∃ f g : (σ → ℂ) → ℂ, AnalyticAt ℂ f w ∧ AnalyticAt ℂ g w ∧
      (∀ᶠ z in 𝓝 w, z ∈ X → f z * g z = 0) ∧ ¬ (∀ᶠ z in 𝓝 w, z ∈ X → f z = 0) ∧
      ¬ (∀ᶠ z in 𝓝 w, z ∈ X → g z = 0) := by
    by_contra hcon
    refine hirr ⟨hw, fun f g hf hg hfg => ?_⟩
    by_contra h
    rw [not_or] at h
    exact hcon ⟨f, g, hf, hg, hfg, h.1, h.2⟩
  have hgf : ∀ᶠ z in 𝓝 w, z ∈ X → g z * f z = 0 := by
    filter_upwards [hfg] with z h hz
    rw [mul_comm]
    exact h hz
  have hfw : f w = 0 := apply_eq_zero_of_not hf hfg hng
  have hgw : g w = 0 := apply_eq_zero_of_not hg hgf hnf
  obtain ⟨s₁, hs₁, W₁, hW₁, hX₁⟩ := ih _ (hJ ▸ vanishingIdeal_lt hf hnf) _ rfl
    (isAnalyticNear_inter_zero hX hf) ⟨hw, hfw⟩
  obtain ⟨s₂, hs₂, W₂, hW₂, hX₂⟩ := ih _ (hJ ▸ vanishingIdeal_lt hg hng) _ rfl
    (isAnalyticNear_inter_zero hX hg) ⟨hw, hgw⟩
  refine ⟨s₁ ∪ s₂, ?_, W₁ ∩ W₂ ∩ {z | z ∈ X → f z * g z = 0}, inter_mem (inter_mem hW₁ hW₂) hfg, ?_⟩
  · intro Y hY
    rcases Finset.mem_union.1 hY with h | h
    · exact hs₁ Y h
    · exact hs₂ Y h
  ext z
  have e₁ := Set.ext_iff.1 hX₁ z
  have e₂ := Set.ext_iff.1 hX₂ z
  simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, Set.mem_iUnion, exists_prop] at e₁ e₂
  simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, Set.mem_iUnion, exists_prop, Finset.mem_union]
  constructor
  · rintro ⟨hzX, ⟨hz₁, hz₂⟩, hz0⟩
    refine ⟨?_, ⟨hz₁, hz₂⟩, hz0⟩
    rcases mul_eq_zero.1 (hz0 hzX) with h | h
    · obtain ⟨Y, hY, hzY⟩ := (e₁.1 ⟨⟨hzX, h⟩, hz₁⟩).1
      exact ⟨Y, Or.inl hY, hzY⟩
    · obtain ⟨Y, hY, hzY⟩ := (e₂.1 ⟨⟨hzX, h⟩, hz₂⟩).1
      exact ⟨Y, Or.inr hY, hzY⟩
  · rintro ⟨⟨Y, hY, hzY⟩, ⟨hz₁, hz₂⟩, hz0⟩
    refine ⟨?_, ⟨hz₁, hz₂⟩, hz0⟩
    rcases hY with hY | hY
    · exact (e₁.2 ⟨⟨Y, hY, hzY⟩, hz₁⟩).1.1
    · exact (e₂.2 ⟨⟨Y, hY, hzY⟩, hz₂⟩).1.1

/- English proof (translation)
Introduce `σ _ X w hX hw`. Take `⟨s, hs, W, hW, hXW⟩` from `exists_finset (hN σ w) X hX hw`. Use `⟨s.card, fun i => (s.equivFin.symm i : Set (σ → ℂ)), fun i => hs _ (s.equivFin.symm i).2, W, hW, ?_⟩` and prove the remaining obligations. Rewrite using `[hXW]`. Use `congr 1`.

Use extensionality with `z`. Simplify using `only [Set.mem_iUnion, exists_prop]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨Y, hY, hz⟩`. Conclude with `⟨s.equivFin ⟨Y, hY⟩, by simpa using hz⟩`.

Introduce and unpack `⟨i, hz⟩`. Conclude with `⟨_, (s.equivFin.symm i).2, hz⟩`.
-/
theorem proof (hN : AnalyticGermsNoetherian.Statement) : AnalyticGermComponents.Statement := by
  intro σ _ X w hX hw
  obtain ⟨s, hs, W, hW, hXW⟩ := exists_finset (hN σ w) X hX hw
  refine ⟨s.card, fun i => (s.equivFin.symm i : Set (σ → ℂ)), fun i => hs _ (s.equivFin.symm i).2, W, hW, ?_⟩
  rw [hXW]
  congr 1
  ext z
  simp only [Set.mem_iUnion, exists_prop]
  constructor
  · rintro ⟨Y, hY, hz⟩
    exact ⟨s.equivFin ⟨Y, hY⟩, by simpa using hz⟩
  · rintro ⟨i, hz⟩
    exact ⟨_, (s.equivFin.symm i).2, hz⟩

end AnalyticGermComponents

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

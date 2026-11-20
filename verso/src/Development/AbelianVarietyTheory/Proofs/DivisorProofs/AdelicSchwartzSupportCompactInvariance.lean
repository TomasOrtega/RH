import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.MatchingOfParts
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqOfComponentTensorAdelicFunctionEq
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilRepresentationPreservesSchwartz
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open Matrix

noncomputable section

namespace GlobalTheory.FinLocSchA

open GlobalTheory.WeilM

/- English proof (translation)
Set `K : AddSubgroup X` to `{ carrier := {k | ∀ z, g (z + k) = g z} zero_mem' := by intro z; simp add_mem' := by`. Introduce `a b ha hb z`. Rewrite using `[← add_assoc, hb, ha]`. Use the proof step `neg_mem' := by`. Introduce `a ha z`.

Use `ha (z + -a)` as an intermediate fact. Simplify using `using this.symm }`. Use `⟨K, ?_, fun z k hk => hk z⟩` and prove the remaining obligations. Establish `h1 : ∀ᶠ k in nhds (0 : X), ∀ z ∈ tsupport g, g (z + k) = g z`. Apply `IsCompact.eventually_forall_of_forall_eventually hg.2` to reduce the goal to its premises.

Introduce `z _`. Establish `a1 : IsLocallyConstant (fun p : X × X => g (p.2 + p.1))` using `hg.1.comp_continuous (by fun_prop)`. Establish `a2 : IsLocallyConstant (fun p : X × X => g p.2)` using `hg.1.comp_continuous (by fun_prop)`. Use `filter_upwards [a1.eventually_eq (0, z), a2.eventually_eq (0, z)] with p hp1 hp2`. Simplify using `only [hp1, hp2, add_zero]`.

Establish `h2 : ∀ᶠ k in nhds (0 : X), ∀ z ∈ tsupport g, g (z + -k) = g z`. Establish `: Filter.Tendsto (fun k : X => -k) (nhds 0) (nhds 0)`. Simplify using `using (continuous_neg (G := X)).tendsto 0`. Conclude with `this.eventually h1`. Apply `AddSubgroup.isOpen_of_mem_nhds K (g := 0)` to reduce the goal to its premises.

Use `filter_upwards [h1, h2] with k hk1 hk2`. Introduce `z`. Distinguish the cases in `hz : z ∈ tsupport g`. Conclude with `hk1 z hz`. Distinguish the cases in `hz' : z + k ∈ tsupport g`.

Simplify using `using (hk2 _ hz').symm`. Rewrite using `[image_eq_zero_of_notMem_tsupport hz, image_eq_zero_of_notMem_tsupport hz']`.
-/
theorem exists_open_addStab {X : Type} [AddGroup X] [TopologicalSpace X] [IsTopologicalAddGroup X]
    {g : X → ℂ} (hg : g ∈ SB X) :
    ∃ K : AddSubgroup X, IsOpen (K : Set X) ∧ ∀ z, ∀ k ∈ K, g (z + k) = g z := by
  let K : AddSubgroup X :=
    { carrier := {k | ∀ z, g (z + k) = g z}
      zero_mem' := by intro z; simp
      add_mem' := by
        intro a b ha hb z
        rw [← add_assoc, hb, ha]
      neg_mem' := by
        intro a ha z
        have := ha (z + -a)
        simpa using this.symm }
  refine ⟨K, ?_, fun z k hk => hk z⟩
  have h1 : ∀ᶠ k in nhds (0 : X), ∀ z ∈ tsupport g, g (z + k) = g z := by
    apply IsCompact.eventually_forall_of_forall_eventually hg.2
    intro z _
    have a1 : IsLocallyConstant (fun p : X × X => g (p.2 + p.1)) :=
      hg.1.comp_continuous (by fun_prop)
    have a2 : IsLocallyConstant (fun p : X × X => g p.2) :=
      hg.1.comp_continuous (by fun_prop)
    filter_upwards [a1.eventually_eq (0, z), a2.eventually_eq (0, z)] with p hp1 hp2
    simp only [hp1, hp2, add_zero]
  have h2 : ∀ᶠ k in nhds (0 : X), ∀ z ∈ tsupport g, g (z + -k) = g z := by
    have : Filter.Tendsto (fun k : X => -k) (nhds 0) (nhds 0) := by
      simpa using (continuous_neg (G := X)).tendsto 0
    exact this.eventually h1
  apply AddSubgroup.isOpen_of_mem_nhds K (g := 0)
  filter_upwards [h1, h2] with k hk1 hk2
  intro z
  by_cases hz : z ∈ tsupport g
  · exact hk1 z hz
  · by_cases hz' : z + k ∈ tsupport g
    · simpa using (hk2 _ hz').symm
    · rw [image_eq_zero_of_notMem_tsupport hz, image_eq_zero_of_notMem_tsupport hz']

/- English proof (translation)
Introduce `F _ _ κ _ Φ hΦ`. Proceed by induction on `hΦ using Submodule.span_induction with`. Consider the case `mem Φ h`. Take `⟨f, g, hg, rfl⟩` from `h`. Take `⟨K, hKo, hK⟩` from `exists_open_addStab hg`.

Use `⟨tsupport g, K, hg.2, hKo, K.zero_mem, ?_, ?_⟩` and prove the remaining obligations. Introduce `x hx`. Assume the negation of the conclusion as `hc`. Apply `hx` to reduce the goal to its premises. Simplify using `only [pureA]`.

Rewrite using `[image_eq_zero_of_notMem_tsupport hc, mul_zero]`. Introduce `x x' h1 h2`. Simplify using `only [pureA, ← h1]`. Use `congr 1`. Establish `e2 : (fun i => (x' i).2) = (fun i => (x i).2) + (fun i => (x' i).2 - (x i).2)`.

Use extensionality with `i`. Simplify using the standard rewrite rules. Rewrite using `[e2]`. Conclude with `hK _ _ h2`. Consider the case `zero`.

Use `⟨∅, Set.univ, isCompact_empty, isOpen_univ, trivial, ?_, ?_⟩` and prove the remaining obligations. Introduce `x hx`. Conclude with `absurd rfl hx`. Introduce `x x' _ _`. Both sides reduce to the same expression.

Consider the case `add Φ Ψ _ _ ihΦ ihΨ`. Take `⟨C₁, K₁, hC₁, hK₁, h0₁, hs₁, hi₁⟩` from `ihΦ`. Take `⟨C₂, K₂, hC₂, hK₂, h0₂, hs₂, hi₂⟩` from `ihΨ`. Use `⟨C₁ ∪ C₂, K₁ ∩ K₂, hC₁.union hC₂, hK₁.inter hK₂, ⟨h0₁, h0₂⟩, ?_, ?_⟩` and prove the remaining obligations. Introduce `x hx`.

Distinguish the cases in `h : Φ x = 0`. Use `right`. Apply `hs₂ x` to reduce the goal to its premises. Introduce `h'`. Apply `hx` to reduce the goal to its premises.

Simplify using `[h, h']`. Use `left`. Conclude with `hs₁ x h`. Introduce `x x' h1 h2`. Simplify using `only [Pi.add_apply, hi₁ x x' h1 h2.1, hi₂ x x' h1 h2.2]`.

Consider the case `smul a Φ _ ih`. Take `⟨C, K, hC, hK, h0, hs, hi⟩` from `ih`. Use `⟨C, K, hC, hK, h0, ?_, ?_⟩` and prove the remaining obligations. Introduce `x hx`. Apply `hs x` to reduce the goal to its premises.

Introduce `h`. Apply `hx` to reduce the goal to its premises. Simplify using `[h]`. Introduce `x x' h1 h2`. Simplify using `only [Pi.smul_apply, hi x x' h1 h2]`.
-/
theorem compact_support_locally_constant_fin : ∀ {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ], ∀ Φ ∈ GlobalTheory.WeilM.schA F κ,
    ∃ (C K : Set (κ → Af F)), IsCompact C ∧ IsOpen K ∧ (0 : κ → Af F) ∈ K ∧
      (∀ x : κ → AF F, Φ x ≠ 0 → (fun i => (x i).2) ∈ C) ∧
      ∀ x x' : κ → AF F, (∀ i, (x i).1 = (x' i).1) → (fun i => (x' i).2 - (x i).2) ∈ K → Φ x' = Φ x := by
  intro F _ _ κ _ Φ hΦ
  induction hΦ using Submodule.span_induction with
  | mem Φ h =>
    obtain ⟨f, g, hg, rfl⟩ := h
    obtain ⟨K, hKo, hK⟩ := exists_open_addStab hg
    refine ⟨tsupport g, K, hg.2, hKo, K.zero_mem, ?_, ?_⟩
    · intro x hx
      by_contra hc
      apply hx
      simp only [pureA]
      rw [image_eq_zero_of_notMem_tsupport hc, mul_zero]
    · intro x x' h1 h2
      simp only [pureA, ← h1]
      congr 1
      have e2 : (fun i => (x' i).2) = (fun i => (x i).2) + (fun i => (x' i).2 - (x i).2) := by
        ext i; simp
      rw [e2]
      exact hK _ _ h2
  | zero =>
    refine ⟨∅, Set.univ, isCompact_empty, isOpen_univ, trivial, ?_, ?_⟩
    · intro x hx; exact absurd rfl hx
    · intro x x' _ _; rfl
  | add Φ Ψ _ _ ihΦ ihΨ =>
    obtain ⟨C₁, K₁, hC₁, hK₁, h0₁, hs₁, hi₁⟩ := ihΦ
    obtain ⟨C₂, K₂, hC₂, hK₂, h0₂, hs₂, hi₂⟩ := ihΨ
    refine ⟨C₁ ∪ C₂, K₁ ∩ K₂, hC₁.union hC₂, hK₁.inter hK₂, ⟨h0₁, h0₂⟩, ?_, ?_⟩
    · intro x hx
      by_cases h : Φ x = 0
      · right; apply hs₂ x; intro h'; apply hx; simp [h, h']
      · left; exact hs₁ x h
    · intro x x' h1 h2
      simp only [Pi.add_apply, hi₁ x x' h1 h2.1, hi₂ x x' h1 h2.2]
  | smul a Φ _ ih =>
    obtain ⟨C, K, hC, hK, h0, hs, hi⟩ := ih
    refine ⟨C, K, hC, hK, h0, ?_, ?_⟩
    · intro x hx
      apply hs x
      intro h; apply hx; simp [h]
    · intro x x' h1 h2
      simp only [Pi.smul_apply, hi x x' h1 h2]

end GlobalTheory.FinLocSchA

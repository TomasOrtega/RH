import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.DiscreteSeriesCoefficientsCuspidal
import PositivityTheory.AutomorphicForms.PublishedInputs.NonzeroTypes.ProductIrreducible2
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.TypesNZeroGDefs
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.LitAut

set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open ValuativeRel Matrix
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL
namespace UpperTheory.TNZ.ProductIrreducible₂
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
/- English proof (translation)
Introduce `s`. Proceed by induction on `s with`. Consider the case `zero`. Use `intros`. Conclude with `GlobalTheory.SmGL.MultiIrr.isIrreducible_multiProd_zero _ _`.

Consider the case `succ s ih`. Introduce `N d hd X _ _ σ hs hi η hη μ hμ hcs`. Establish `e : N = d 0 + ∑ i : Fin s, d i.succ` using `hd.symm.trans (Fin.sum_univ_succ _)`. Substitute `e` using the available equality. Take `⟨E⟩` from `GlobalTheory.SmGL.MultiIrr.nonempty_prod₂_equiv_multiProd_succ d hd σ`.

Establish `hτi : (multiProd (stdBlocks (fun i : Fin s => d i.succ) rfl) fun i => σ i.succ).IsIrreducible` using `ih _ (fun i => d i.succ) rfl (fun i => X i.succ) (fun i => σ i.succ) (fun i => hs _) (fun i => hi _) (fun i => η i.succ) (fun b c hbc => hη _ _ fun h => hbc (Fin.succ_injective _ h)) (fun i => μ i.succ) (fun i => hμ _) (fun i => hcs _)`. Establish `hτs : IsSmooth (multiProd (stdBlocks (fun i : Fin s => d i.succ) rfl) fun i => σ i.succ)` using `isSmooth_parInd _ _`. Take `⟨h', x, hx, hxc⟩` from `GlobalTheory.LocGL.SupportRing.hasSupport_multiProd hL.zel (d := fun i : Fin s => d i.succ) rfl (fun i => σ i.succ) (fun i => hs _) (fun i => hi _) (fun i => hasSupport_of_isCuspSupport (hcs i.succ)) hτi`. Establish `hP` using `hL.disj k (d 0) (∑ i : Fin s, d i.succ) (d 0) h' { V := X 0, π := σ 0, smooth := hs 0, irr := hi 0 } { V := _, π := multiProd (stdBlocks (fun i : Fin s => d i.succ) rfl) fun i => σ i.succ, smooth := hτs, irr := hτi } (fun _ => 1) (fun b => (x b).1) (fun a => GlobalTheory.SplitRea …`. Conclude with `GlobalTheory.Parabolic.isIrreducible_of_equiv E hP`.

Introduce `a b hab j _ hφ`. Establish `hxb : x b ∈ ∑ i : Fin s, Finset.univ.val.map fun a => IrrGL.of (detRep (Fin 1) (μ i.succ a)) ((hcs i.succ).2.1 a).2.2.1 ((hcs i.succ).2.1 a).2.1`. Rewrite using `[← hx]`. Conclude with `Multiset.mem_map_of_mem x (Finset.mem_univ_val b)`. Take `⟨c, -, hc⟩` from `Multiset.mem_sum.1 hxb`.

Take `⟨j', -, hj'⟩` from `Multiset.mem_map.1 hc`. Take `⟨u, hu, hne⟩` from `hη 0 c.succ (Fin.succ_ne_zero c).symm`. Apply `hne` to reduce the goal to its premises. Rewrite using `[← (hμ 0 a).2 u hu, ← (hμ c.succ j').2 u hu]`. Conclude with `eq_on_units (x b) hab (μ 0 a) (μ c.succ j') (hμ 0 a).1 _ _ hj' j hφ u hu`.
-/
theorem isIrreducible_multiProd_stdBlocks_of_ne_on_units (hL : _root_.GlobalTheory.Mem.LiteralAutomorphy.LitLocAlt) :
    ∀ (s N : ℕ) (d : Fin s → ℕ) (hd : ∑ b, d b = N) (X : Fin s → Type) [∀ b, AddCommGroup (X b)]
      [∀ b, Module ℂ (X b)] (σ : ∀ b, Representation ℂ (GL (Fin (d b)) k) (X b)),
      (∀ b, IsSmooth (σ b)) → (∀ b, (σ b).IsIrreducible) → ∀ η : Fin s → kˣ →* ℂˣ,
      (∀ b c, b ≠ c → ∃ u : kˣ, valuation k (u : k) = 1 ∧ η b u ≠ η c u) →
      ∀ μ : ∀ b, Fin (d b) → kˣ →* ℂˣ,
      (∀ b j, IsSmoothChar (μ b j) ∧ ∀ u : kˣ, valuation k (u : k) = 1 → μ b j u = η b u) →
      (∀ b, IsCuspSupport (σ b) (fun _ => 1) (fun j => detRep (Fin 1) (μ b j))) →
        (multiProd (stdBlocks d hd) σ).IsIrreducible := by
  intro s
  induction s with
  | zero =>
    intros
    exact GlobalTheory.SmGL.MultiIrr.isIrreducible_multiProd_zero _ _
  | succ s ih =>
    intro N d hd X _ _ σ hs hi η hη μ hμ hcs
    have e : N = d 0 + ∑ i : Fin s, d i.succ := hd.symm.trans (Fin.sum_univ_succ _)
    subst e
    obtain ⟨E⟩ := GlobalTheory.SmGL.MultiIrr.nonempty_prod₂_equiv_multiProd_succ d hd σ
    have hτi : (multiProd (stdBlocks (fun i : Fin s => d i.succ) rfl) fun i => σ i.succ).IsIrreducible :=
      ih _ (fun i => d i.succ) rfl (fun i => X i.succ) (fun i => σ i.succ) (fun i => hs _) (fun i => hi _)
        (fun i => η i.succ) (fun b c hbc => hη _ _ fun h => hbc (Fin.succ_injective _ h))
        (fun i => μ i.succ) (fun i => hμ _) (fun i => hcs _)
    have hτs : IsSmooth (multiProd (stdBlocks (fun i : Fin s => d i.succ) rfl) fun i => σ i.succ) :=
      isSmooth_parInd _ _
    obtain ⟨h', x, hx, hxc⟩ := GlobalTheory.LocGL.SupportRing.hasSupport_multiProd hL.zel (d := fun i : Fin s => d i.succ) rfl
      (fun i => σ i.succ) (fun i => hs _) (fun i => hi _) (fun i => hasSupport_of_isCuspSupport (hcs i.succ)) hτi
    have hP := hL.disj k (d 0) (∑ i : Fin s, d i.succ) (d 0) h'
      { V := X 0, π := σ 0, smooth := hs 0, irr := hi 0 }
      { V := _, π := multiProd (stdBlocks (fun i : Fin s => d i.succ) rfl) fun i => σ i.succ, smooth := hτs,
        irr := hτi }
      (fun _ => 1) (fun b => (x b).1) (fun a => GlobalTheory.SplitRead.Irr.ofDet 1 (μ 0 a) (hμ 0 a).1)
      (fun b => GlobalTheory.SplitRead.Irr.ofIrrRep (x b).2.rep) (hcs 0) hxc ?_
    · exact GlobalTheory.Parabolic.isIrreducible_of_equiv E hP
    · intro a b hab j _ hφ
      have hxb : x b ∈ ∑ i : Fin s, Finset.univ.val.map fun a =>
          IrrGL.of (detRep (Fin 1) (μ i.succ a)) ((hcs i.succ).2.1 a).2.2.1 ((hcs i.succ).2.1 a).2.1 := by
        rw [← hx]
        exact Multiset.mem_map_of_mem x (Finset.mem_univ_val b)
      obtain ⟨c, -, hc⟩ := Multiset.mem_sum.1 hxb
      obtain ⟨j', -, hj'⟩ := Multiset.mem_map.1 hc
      obtain ⟨u, hu, hne⟩ := hη 0 c.succ (Fin.succ_ne_zero c).symm
      apply hne
      rw [← (hμ 0 a).2 u hu, ← (hμ c.succ j').2 u hu]
      exact eq_on_units (x b) hab (μ 0 a) (μ c.succ j') (hμ 0 a).1 _ _ hj' j hφ u hu
end UpperTheory.TNZ.ProductIrreducible₂
namespace UpperTheory.TNZ
/- English proof (translation)
Unfold `_root_.UpperTheory.TNZ.Step_prodIrr_alt`. Introduce `hC hL k _ _ _ _ s N d hd X _ _ σ hs hi η hη hdv hne`. Establish `H` using `fun b => hC hL k (d b) (X b) (σ b) (hs b) (hi b) (η b) (hη b) (hdv b)`. Use `choose μ hμ hcs using H`. Conclude with `_root_.UpperTheory.TNZ.ProductIrreducible₂.isIrreducible_multiProd_stdBlocks_of_ne_on_units hL s N d hd X σ hs hi η hne μ hμ hcs`.
-/
theorem step_prodIrr_alt : _root_.UpperTheory.TNZ.Step_prodIrr_alt := by
  unfold _root_.UpperTheory.TNZ.Step_prodIrr_alt
  intro hC hL k _ _ _ _ s N d hd X _ _ σ hs hi η hη hdv hne
  have H := fun b => hC hL k (d b) (X b) (σ b) (hs b) (hi b) (η b) (hη b) (hdv b)
  choose μ hμ hcs using H
  exact _root_.UpperTheory.TNZ.ProductIrreducible₂.isIrreducible_multiProd_stdBlocks_of_ne_on_units hL s N d hd X σ hs hi η hne μ hμ hcs
end UpperTheory.TNZ
end
end

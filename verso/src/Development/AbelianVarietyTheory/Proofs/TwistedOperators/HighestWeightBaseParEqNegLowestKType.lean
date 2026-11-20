import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MeasurePreservingMulRight
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.StepUnfold
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsDefiniteOfAllPlus
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.PairwiseFlatMapBand
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsHCTypeWConj
import Development.AbelianVarietyTheory.Definitions.Foundations.StrictInterlaceIffDescEnum
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open GlobalTheory.ChiGrid GlobalTheory.RowReal GlobalTheory.IndefiniteRowSideFullHecke.MinorOrderedEntries
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.RowReal.BaseWeights

/- English proof (translation)
Take `⟨a, ha, rfl⟩` from `List.mem_map.1 h`. Conclude with `Finset.mem_image.2 ⟨a, Finset.mem_range.2 (List.mem_range.1 ha), rfl⟩`.
-/
theorem mem_tparBlock {c x : ℚ} {n : ℕ} (h : x ∈ GlobalTheory.IndefiniteRowSideFullHecke.MinorOrderedEntries.block c n) : x ∈ TPar.block c n := by
  obtain ⟨a, ha, rfl⟩ := List.mem_map.1 h
  exact Finset.mem_image.2 ⟨a, Finset.mem_range.2 (List.mem_range.1 ha), rfl⟩

/- English proof (translation)
Establish `h1 : ∀ l : List (Fin (S.k - 1)), (l.map fun i => (P.v i : ℚ)).Sublist (l.flatMap fun i => [(P.v i : ℚ), P.u i])`. Introduce `l`. Proceed by induction on `l with`. Consider the case `nil => simp`. Consider the case `cons a l ih`.

Simplify using `only [List.map_cons, List.flatMap_cons, List.cons_append, List.nil_append]`. Conclude with `(ih.cons _).cons₂ _`. Unfold `Entries.basePar Entries.orderList`. Conclude with `List.Sublist.append ((h1 _).trans (List.sublist_append_right _ _)) (List.Sublist.refl _)`.
-/
theorem basePar_sublist {S : Sizes} (P : Entries S) : P.basePar.Sublist P.orderList := by
  have h1 : ∀ l : List (Fin (S.k - 1)),
      (l.map fun i => (P.v i : ℚ)).Sublist (l.flatMap fun i => [(P.v i : ℚ), P.u i]) := by
    intro l
    induction l with
    | nil => simp
    | cons a l ih =>
      simp only [List.map_cons, List.flatMap_cons, List.cons_append, List.nil_append]
      exact (ih.cons _).cons₂ _
  unfold Entries.basePar Entries.orderList
  exact List.Sublist.append ((h1 _).trans (List.sublist_append_right _ _)) (List.Sublist.refl _)

/- English proof (translation)
Establish `hodd : ¬ Odd D.R.m` using `Nat.not_odd_iff_even.2 D.R.m_even`. Take `⟨hv, hb, he⟩` from `GlobalTheory.SignedHC.GridData.ofHCParam_spec (D.hc τ) (sLen D) (gap D C) (cen D C τ)`. Introduce `x hx`. Simplify using `only [Entries.basePar, List.mem_append, List.mem_map, List.mem_flatMap, List.mem_cons, List.mem_finRange, true_and] at hx`. Unfold `TPar.Dpar`.

Break down `hx with ⟨i, rfl⟩ | ⟨j, h | h⟩` into its components or cases. Use `⟨true, Finset.mem_image.2 ⟨((Ptw D).v τ i, true), ?_, ?_⟩⟩` and prove the remaining obligations. Conclude with `Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_image_of_mem _ (Finset.mem_univ i)))`. Simplify using `only [hodd, if_false, add_zero]`. Conclude with `Prod.ext (hv i) rfl`.

Use `⟨decide ((j : ℕ) ≤ D.R.m ∨ Even ((j : ℕ) - D.R.m)), Finset.mem_image.2 ⟨(-(Ptw D).b τ j, decide ((j : ℕ) ≤ D.R.m ∨ Even ((j : ℕ) - D.R.m))), ?_, ?_⟩⟩` and prove the remaining obligations. Conclude with `Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_image_of_mem _ (Finset.mem_univ j)))`. Simplify using `only [hodd, if_false, add_zero]`. Use `Prod.ext ?_ rfl` and prove the remaining obligations. Rewrite using `[h]`.

Use `show -(D.hc τ).b j = _`. Rewrite using `[hb j]`. Both sides reduce to the same expression. Use `⟨true, Finset.mem_image.2 ⟨(x, true), ?_, ?_⟩⟩` and prove the remaining obligations. Use `Finset.mem_union_right _ (Finset.mem_biUnion.2 ⟨j, Finset.mem_filter.2 ⟨Finset.mem_univ _, j.2⟩, ?_⟩)` and prove the remaining obligations.

Use `Finset.mem_image.2 ⟨x, ?_, rfl⟩` and prove the remaining obligations. Establish `hx'` using `mem_tparBlock h`. Establish `: (-(Ptw D).e τ j) = -(((rowEntries D C τ).e j : ℤ) : ℚ)` using `by show -(D.hc τ).e j = _`. Rewrite using `[he j]`. Both sides reduce to the same expression.

Rewrite using `[this]`. Conclude with `hx'`. Simplify using `only [hodd, if_false, add_zero]`.
-/
theorem base_mem_Dpar (D : D7) (C : ℝ) (τ : D.what₂.Tau) :
    ∀ x ∈ (rowEntries D C τ).basePar, ∃ s, (x, s) ∈ (Ptw D).Dpar D.R.m τ := by
  have hodd : ¬ Odd D.R.m := Nat.not_odd_iff_even.2 D.R.m_even
  obtain ⟨hv, hb, he⟩ := GlobalTheory.SignedHC.GridData.ofHCParam_spec (D.hc τ) (sLen D) (gap D C) (cen D C τ)
  intro x hx
  simp only [Entries.basePar, List.mem_append, List.mem_map, List.mem_flatMap, List.mem_cons, List.mem_finRange,
    true_and] at hx
  unfold TPar.Dpar
  rcases hx with ⟨i, rfl⟩ | ⟨j, h | h⟩
  · refine ⟨true, Finset.mem_image.2 ⟨((Ptw D).v τ i, true), ?_, ?_⟩⟩
    · exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_image_of_mem _ (Finset.mem_univ i)))
    · simp only [hodd, if_false, add_zero]
      exact Prod.ext (hv i) rfl
  · refine ⟨decide ((j : ℕ) ≤ D.R.m ∨ Even ((j : ℕ) - D.R.m)), Finset.mem_image.2 ⟨(-(Ptw D).b τ j, decide ((j : ℕ) ≤ D.R.m ∨ Even ((j : ℕ) - D.R.m))), ?_, ?_⟩⟩
    · exact Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_image_of_mem _ (Finset.mem_univ j)))
    · simp only [hodd, if_false, add_zero]
      refine Prod.ext ?_ rfl
      rw [h]
      show -(D.hc τ).b j = _
      rw [hb j]; rfl
  · refine ⟨true, Finset.mem_image.2 ⟨(x, true), ?_, ?_⟩⟩
    · refine Finset.mem_union_right _ (Finset.mem_biUnion.2 ⟨j, Finset.mem_filter.2 ⟨Finset.mem_univ _, j.2⟩, ?_⟩)
      refine Finset.mem_image.2 ⟨x, ?_, rfl⟩
      have hx' := mem_tparBlock h
      have : (-(Ptw D).e τ j) = -(((rowEntries D C τ).e j : ℤ) : ℚ) := by
        show -(D.hc τ).e j = _
        rw [he j]; rfl
      rw [this]
      exact hx'
    · simp only [hodd, if_false, add_zero]

end GlobalTheory.RowReal.BaseWeights

namespace GlobalTheory.RowReal

open GlobalTheory.RowReal.BaseWeights

/- English proof (translation)
Introduce `D C M τ i`. Establish `hlen : (rowEntries D C τ).basePar.length = D.sp.X'.rank`. Rewrite using `[length_base, D.sp.X'_rank]`. Simplify using `[Sizes.nC, rowSizes, Ranks.rankX', Ranks.r]`. Establish `hε : M.ε τ = Formalism.MainNotions.S.allPos _` using `funext fun a => GlobalTheory.DefiniteMult.allPlus_parB _ (Nat.sub_le _ _) M τ a`.

Take `⟨hanti, q, hq, hS⟩` from `M.enum τ`. Establish `hqa : StrictAnti q` using `fun a b h => by`. Use `hanti h` as an intermediate fact. Rewrite `this` using `[hq, hq]`. Conclude with `this` after adjusting the coercions.

Establish `hinj : Function.Injective fun a => -q a` using `fun a b h => hqa.injective (neg_injective h)`. Establish `hE : (Finset.univ.image fun a => -q a).card = D.sp.X'.rank`. Rewrite using `[Finset.card_image_of_injective _ hinj]`. Simplify using the standard rewrite rules. Establish `hpw` using `(rowEntries_good D C τ).order.sublist (basePar_sublist (rowEntries D C τ))`.

Set `f : Fin D.sp.X'.rank → ℚ` to `fun j => (rowEntries D C τ).basePar[(j : ℕ)]'(by rw [hlen]; exact j.2)`. Establish `hf : StrictAnti f` using `fun a b hab => List.pairwise_iff_getElem.1 hpw _ _ _ _ hab`. Establish `hfm : ∀ j, f j ∈ Finset.univ.image fun a => -q a`. Introduce `j`. Take `⟨s, hs⟩` from `base_mem_Dpar D C τ _ (List.getElem_mem (by rw [hlen]; exact j.2))`.

Establish `h2 : (-(f j), s) ∈ Formalism.IndefR.Mult.parB (Ptw D) D.R.m τ` using `Finset.mem_image.2 ⟨_, hs, rfl⟩`. Rewrite `h2` using `[hS]`. Take `⟨a, -, ha⟩` from `Finset.mem_image.1 h2`. Use `Finset.mem_image.2 ⟨a, Finset.mem_univ _, ?_⟩` and prove the remaining obligations. Establish `h3` using `congrArg Prod.fst ha`.

Simplify using `only at h3`. Rewrite using `[h3, neg_neg]`. Set `g : Fin D.sp.X'.rank → ℚ` to `fun j => -q j.rev`. Establish `hg : StrictAnti g` using `fun a b hab => by`. Simplify using `only [g, neg_lt_neg_iff]`.

Conclude with `hqa (Fin.rev_lt_rev.2 hab)`. Establish `hgm : ∀ j, g j ∈ Finset.univ.image fun a => -q a` using `fun j => Finset.mem_image.2 ⟨j.rev, Finset.mem_univ _, rfl⟩`. Establish `hfg : f = g` using `(GlobalTheory.SignedHC.descEnum_unique hE hf hfm).symm.trans (GlobalTheory.SignedHC.descEnum_unique hE hg hgm)`. Establish `hi : (i : ℕ) < (rowEntries D C τ).basePar.length` using `by rw [hlen]; exact i.2`. Establish `key : (rowEntries D C τ).basePar[(i : ℕ)] = -q i.rev` using `congrFun hfg i`.

Establish `h1` using `hw_base _ i hi`. Establish `hl : (((rowEntries D C τ).basePar.length : ℕ) : ℚ) = (D.sp.X'.rank : ℚ)` using `by rw [hlen]`. Rewrite `h1` using `[hl, key]`. Rewrite using `[hε, GlobalTheory.ConjTypeW.lowK_allPos, hq]`. Establish `h4 : (hw (rowEntries D C τ).basePar i : ℝ) = (((hw (rowEntries D C τ).basePar i : ℤ) : ℚ) : ℝ)` using `by push_cast; rfl`.

Rewrite using `[h4, h1, Fin.val_rev]`. Establish `h5 : (i : ℕ) + 1 ≤ D.sp.X'.rank` using `i.2`. Rewrite using `[Nat.cast_sub h5]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem hw_basePar_eq_neg_lowK : ∀ (D : D7) (C : ℝ)
    (M : Formalism.IndefR.Mult.DSModel D.sp.X' (Formalism.IndefR.Mult.parB (Ptw D) D.R.m)) (τ : D.what₂.Tau)
    (i : Fin D.sp.X'.rank),
    (hw (rowEntries D C τ).basePar i : ℝ) = -(Formalism.QuantumDeterminants.lowK (M.ε τ) (M.lam τ)) (Fin.rev i) := by
  intro D C M τ i
  have hlen : (rowEntries D C τ).basePar.length = D.sp.X'.rank := by
    rw [length_base, D.sp.X'_rank]
    simp [Sizes.nC, rowSizes, Ranks.rankX', Ranks.r]
  have hε : M.ε τ = Formalism.MainNotions.S.allPos _ := funext fun a => GlobalTheory.DefiniteMult.allPlus_parB _ (Nat.sub_le _ _) M τ a
  obtain ⟨hanti, q, hq, hS⟩ := M.enum τ
  have hqa : StrictAnti q := fun a b h => by
    have := hanti h
    rw [hq, hq] at this
    exact_mod_cast this
  have hinj : Function.Injective fun a => -q a := fun a b h => hqa.injective (neg_injective h)
  have hE : (Finset.univ.image fun a => -q a).card = D.sp.X'.rank := by
    rw [Finset.card_image_of_injective _ hinj]; simp
  have hpw := (rowEntries_good D C τ).order.sublist (basePar_sublist (rowEntries D C τ))
  let f : Fin D.sp.X'.rank → ℚ := fun j => (rowEntries D C τ).basePar[(j : ℕ)]'(by rw [hlen]; exact j.2)
  have hf : StrictAnti f := fun a b hab => List.pairwise_iff_getElem.1 hpw _ _ _ _ hab
  have hfm : ∀ j, f j ∈ Finset.univ.image fun a => -q a := by
    intro j
    obtain ⟨s, hs⟩ := base_mem_Dpar D C τ _ (List.getElem_mem (by rw [hlen]; exact j.2))
    have h2 : (-(f j), s) ∈ Formalism.IndefR.Mult.parB (Ptw D) D.R.m τ := Finset.mem_image.2 ⟨_, hs, rfl⟩
    rw [hS] at h2
    obtain ⟨a, -, ha⟩ := Finset.mem_image.1 h2
    refine Finset.mem_image.2 ⟨a, Finset.mem_univ _, ?_⟩
    have h3 := congrArg Prod.fst ha
    simp only at h3
    rw [h3, neg_neg]
  let g : Fin D.sp.X'.rank → ℚ := fun j => -q j.rev
  have hg : StrictAnti g := fun a b hab => by
    simp only [g, neg_lt_neg_iff]
    exact hqa (Fin.rev_lt_rev.2 hab)
  have hgm : ∀ j, g j ∈ Finset.univ.image fun a => -q a := fun j => Finset.mem_image.2 ⟨j.rev, Finset.mem_univ _, rfl⟩
  have hfg : f = g := (GlobalTheory.SignedHC.descEnum_unique hE hf hfm).symm.trans (GlobalTheory.SignedHC.descEnum_unique hE hg hgm)
  have hi : (i : ℕ) < (rowEntries D C τ).basePar.length := by rw [hlen]; exact i.2
  have key : (rowEntries D C τ).basePar[(i : ℕ)] = -q i.rev := congrFun hfg i
  have h1 := hw_base _ i hi
  have hl : (((rowEntries D C τ).basePar.length : ℕ) : ℚ) = (D.sp.X'.rank : ℚ) := by rw [hlen]
  rw [hl, key] at h1
  rw [hε, GlobalTheory.ConjTypeW.lowK_allPos, hq]
  have h4 : (hw (rowEntries D C τ).basePar i : ℝ) = (((hw (rowEntries D C τ).basePar i : ℤ) : ℚ) : ℝ) := by push_cast; rfl
  rw [h4, h1, Fin.val_rev]
  have h5 : (i : ℕ) + 1 ≤ D.sp.X'.rank := i.2
  rw [Nat.cast_sub h5]
  push_cast
  ring

end GlobalTheory.RowReal

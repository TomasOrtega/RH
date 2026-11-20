import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.FrameBoundSpaces.FrameBound
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.LeviMatchingWords.SplitPlaceGeneratorPowers
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.SeenTr
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.WordFrameBounds.WordIdAt
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.AdelicHeckeBlocks.Imports
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.AdelicHeckeBlocks.DoubleSumFinprodFactor
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.AdelicHeckeBlocks.PFinConv
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.LeviMatchingWords.GeneratorPowSplitPlacesOfIdempotent
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.HermitianConvolution.LpowMulPf
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MatchingTransferOf

noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory Filter
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open PositivityTheory.Rg.BcB.E PositivityTheory.RgBcC PositivityTheory.Rg.BcB.CG PositivityTheory.Rg.BcB.G8
open PositivityTheory.RgTw (Mat G)
open PositivityTheory.Rg.BcB.SpectralAccumulation (Hf)
open scoped Classical

set_option synthInstance.maxHeartbeats 200000

open PositivityTheory.Rg.BcB.F.Eig PositivityTheory.Rg.BcN.F2

namespace PositivityTheory.Rg.BcB.F.B3

attribute [local instance] borelG borelF borelA GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

set_option linter.unusedSectionVars false

namespace PLocMatch

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {a b : ℕ}

/- English proof (translation)
Use `⟨fun x y => ?_, FinConv.isTestFunction_mulConvolution hL.2 hL'.2⟩` and prove the remaining obligations. Set `z₀ : ∀ w : P, κ w` to `fun w => Classical.choice (hne w)`. Establish `hT : ∀ z : (∀ w : P, κ w), IsTestP (fun w => mconv (L.ent P x z w) (L'.ent P z y w))` using `fun z => FinConv.isTestFunction_mulConvolution (hL.1 x z) (hL'.1 z y)`. Use `Fm.isTestFunction_linearCombination (J := ∀ w : P, κ w) _ hT _ (fun w => ?_) (Fm.cof_off P (hT z₀) fun w hw => ?_)` and prove the remaining obligations. Distinguish the cases in `hw : w ∈ P`.

Use `⟨κ w, inferInstance, fun i => Function.update z₀ ⟨w, hw⟩ i, fun _ => 1, ?_⟩` and prove the remaining obligations. Simplify using `[LM.ent, LM.mul, hw]`. Use `⟨Unit, inferInstance, fun _ => z₀, fun _ => 1, ?_⟩` and prove the remaining obligations. Simplify using `[LM.ent, LM.mul, hw]`. Simplify using `[LM.ent, LM.mul, hw]`.
-/
theorem ok_mul {κ : Pl E → Type} [∀ w, Fintype (κ w)] (P : Finset (Pl E)) (hne : ∀ w, Nonempty (κ w))
    {L L' : LM κ a b} (hL : L.Ok P) (hL' : L'.Ok P) : (L.mul L').Ok P := by
  refine ⟨fun x y => ?_, FinConv.isTestFunction_mulConvolution hL.2 hL'.2⟩
  let z₀ : ∀ w : P, κ w := fun w => Classical.choice (hne w)
  have hT : ∀ z : (∀ w : P, κ w), IsTestP (fun w => mconv (L.ent P x z w) (L'.ent P z y w)) :=
    fun z => FinConv.isTestFunction_mulConvolution (hL.1 x z) (hL'.1 z y)
  refine Fm.isTestFunction_linearCombination (J := ∀ w : P, κ w) _ hT _ (fun w => ?_) (Fm.cof_off P (hT z₀) fun w hw => ?_)
  · by_cases hw : w ∈ P
    · refine ⟨κ w, inferInstance, fun i => Function.update z₀ ⟨w, hw⟩ i, fun _ => 1, ?_⟩
      simp [LM.ent, LM.mul, hw]
    · refine ⟨Unit, inferInstance, fun _ => z₀, fun _ => 1, ?_⟩
      simp [LM.ent, LM.mul, hw]
  · simp [LM.ent, LM.mul, hw]

/- English proof (translation)
The claim follows from `| [], _ => h₀ | L :: l, hl => ok_mul P hne (hl L List.mem_cons_self) (ok_foldr P hne h₀ l fun L' h' => hl L' (List.mem_cons_of_mem _ h'))`.
-/
theorem ok_foldr {κ : Pl E → Type} [∀ w, Fintype (κ w)] (P : Finset (Pl E)) (hne : ∀ w, Nonempty (κ w))
    {L₀ : LM κ a b} (h₀ : L₀.Ok P) : ∀ l : List (LM κ a b), (∀ L ∈ l, L.Ok P) → (l.foldr LM.mul L₀).Ok P
  | [], _ => h₀
  | L :: l, hl => ok_mul P hne (hl L List.mem_cons_self)
      (ok_foldr P hne h₀ l fun L' h' => hl L' (List.mem_cons_of_mem _ h'))

/- English proof (translation)
Set `z₀ : ∀ w : P, κ w` to `fun w => Classical.choice (hne w)`. Use `Fm.isTestFunction_linearCombination (J := (∀ w : P, κ w) × (∀ w : P, κ w)) (fun p => L.ent P p.1 p.2) (fun p => hL.1 p.1 p.2) _ (fun w => ?_) (Fm.cof_off P (hL.1 z₀ z₀) fun w hw => ?_)` and prove the remaining obligations. Distinguish the cases in `hw : w ∈ P`. Use `⟨κ w × κ w, inferInstance, fun i => (Function.update z₀ ⟨w, hw⟩ i.1, Function.update z₀ ⟨w, hw⟩ i.2), fun i => N w i.2 i.1, ?_⟩` and prove the remaining obligations. Simplify using `[LM.tr, LM.ent, hw, Fintype.sum_prod_type]`.

Use `⟨Unit, inferInstance, fun _ => (z₀, z₀), fun _ => 1, ?_⟩` and prove the remaining obligations. Simplify using `[LM.tr, LM.ent, hw]`. Simplify using `[LM.tr, LM.ent, hw]`.
-/
theorem isTestFunction_translate {κ : Pl E → Type} [∀ w, Fintype (κ w)] (P : Finset (Pl E)) (hne : ∀ w, Nonempty (κ w))
    {L : LM κ a b} (hL : L.Ok P) (N : ∀ w, κ w → κ w → ℂ) : IsTestP (L.tr P N) := by
  let z₀ : ∀ w : P, κ w := fun w => Classical.choice (hne w)
  refine Fm.isTestFunction_linearCombination (J := (∀ w : P, κ w) × (∀ w : P, κ w)) (fun p => L.ent P p.1 p.2) (fun p => hL.1 p.1 p.2) _
    (fun w => ?_) (Fm.cof_off P (hL.1 z₀ z₀) fun w hw => ?_)
  · by_cases hw : w ∈ P
    · refine ⟨κ w × κ w, inferInstance, fun i => (Function.update z₀ ⟨w, hw⟩ i.1, Function.update z₀ ⟨w, hw⟩ i.2),
        fun i => N w i.2 i.1, ?_⟩
      simp [LM.tr, LM.ent, hw, Fintype.sum_prod_type]
    · refine ⟨Unit, inferInstance, fun _ => (z₀, z₀), fun _ => 1, ?_⟩
      simp [LM.tr, LM.ent, hw]
  · simp [LM.tr, LM.ent, hw]

/- English proof (translation)
Use function extensionality and compare the values at `y`. Simplify using `only [seen, if_pos hs]`. Both sides reduce to the same expression.
-/
theorem seen_split {φ₁ φ₂ : ∀ w : Pl E, LF a b w} {w : Pl E} (hs : IsSplitAt w) :
    seen φ₁ φ₂ w = mconv (φ₁ w) (φ₂ w) := by
  funext y; simp only [seen, if_pos hs]; rfl

/- English proof (translation)
Use function extensionality and compare the values at `y`. Simplify using `only [seen, if_neg hs]`.
-/
theorem seen_inert {φ₁ φ₂ : ∀ w : Pl E, LF a b w} {w : Pl E} (hs : ¬ IsSplitAt w) : seen φ₁ φ₂ w = φ₁ w := by
  funext y; simp only [seen, if_neg hs]

/- English proof (translation)
Establish `hm` using `FinConv.isTestFunction_mulConvolution h₁ h₂`. Apply the tactic sequence `refine Fm.isTestFunction_linearCombination (J := Bool) (fun j => if j then (fun w => mconv (φ₁ w) (φ₂ w)) else φ₁) (fun j => by cases j <;> simpa) _ (fun w => ⟨Unit, inferInstance, fun _ => decide (IsSplitAt w), fun _ => 1, ?_⟩) ?_`. Distinguish the cases in `hs : IsSplitAt w`. Simplify using `[hs, seen_split hs]`. Simplify using `[hs, seen_inert hs]`.

Use `filter_upwards [Fm.cof_of_test h₁, Fm.cof_of_test hm] with w e1 e2`. Distinguish the cases in `hs : IsSplitAt w`. Rewrite using `[seen_split hs]`. Conclude with `e2`. Rewrite using `[seen_inert hs]`.

Conclude with `e1`.
-/
theorem testP_seen {φ₁ φ₂ : ∀ w : Pl E, LF a b w} (h₁ : IsTestP φ₁) (h₂ : IsTestP φ₂) : IsTestP (seen φ₁ φ₂) := by
  have hm := FinConv.isTestFunction_mulConvolution h₁ h₂
  refine Fm.isTestFunction_linearCombination (J := Bool) (fun j => if j then (fun w => mconv (φ₁ w) (φ₂ w)) else φ₁)
    (fun j => by cases j <;> simpa) _ (fun w => ⟨Unit, inferInstance, fun _ => decide (IsSplitAt w), fun _ => 1, ?_⟩) ?_
  · by_cases hs : IsSplitAt w
    · simp [hs, seen_split hs]
    · simp [hs, seen_inert hs]
  · filter_upwards [Fm.cof_of_test h₁, Fm.cof_of_test hm] with w e1 e2
    by_cases hs : IsSplitAt w
    · rw [seen_split hs]; exact e2
    · rw [seen_inert hs]; exact e1

/- English proof (translation)
Use `⟨HasCompactSupport.finset_sum fun i _ => (hf i).1.mul_left (f := fun _ => c i), fun k hk x => ?_⟩` and prove the remaining obligations. Simplify using `only [Finset.sum_apply, Pi.smul_apply]`. Conclude with `⟨Finset.sum_congr rfl fun i _ => by rw [((hf i).2 k hk x).1], Finset.sum_congr rfl fun i _ => by rw [((hf i).2 k hk x).2]⟩`.
-/
theorem hk_fsum {G ι : Type} [Group G] [TopologicalSpace G] (K : Subgroup G) (s : Finset ι) (c : ι → ℂ)
    (f : ι → G → ℂ) (hf : ∀ i, IsHecke K (f i)) : IsHecke K (∑ i ∈ s, c i • f i) := by
  refine ⟨HasCompactSupport.finset_sum fun i _ => (hf i).1.mul_left (f := fun _ => c i), fun k hk x => ?_⟩
  simp only [Finset.sum_apply, Pi.smul_apply]
  exact ⟨Finset.sum_congr rfl fun i _ => by rw [((hf i).2 k hk x).1],
    Finset.sum_congr rfl fun i _ => by rw [((hf i).2 k hk x).2]⟩

/- English proof (translation)
Establish `hK : IsCompact (KL n w : Set (UL n w))`. Rewrite using `[KL, Subgroup.coe_subgroupOf]`. Conclude with `(GlobalTheory.CompanionTheory.LevelU.isClosed_UL n w).isClosedEmbedding_subtypeVal.isCompact_preimage (GlobalTheory.LFun.SatCompare.isOpen_isCompact_KGL w n).2`. Establish `hC : IsClosed (K' : Set (UL n w))` using `K'.isClosed_of_isOpen hO`. Establish `hK'c : IsCompact (K' : Set (UL n w))` using `hK.of_isClosed_subset hC hKK`.

Use `⟨HasCompactSupport.intro' hK'c hC fun x hx => Set.indicator_of_notMem hx _, fun k hk x => ⟨?_, ?_⟩⟩` and prove the remaining obligations. Simplify using `only [U.lone, Set.indicator_apply, SetLike.mem_coe, K'.mul_mem_cancel_left hk]`. Simplify using `only [U.lone, Set.indicator_apply, SetLike.mem_coe, K'.mul_mem_cancel_right hk]`.
-/
theorem lone_hecke {n : ℕ} {w : Pl E} {K' : Subgroup (UL n w)} (hO : IsOpen (K' : Set (UL n w))) (hKK : K' ≤ KL n w) :
    IsHecke K' (U.lone K') := by
  have hK : IsCompact (KL n w : Set (UL n w)) := by
    rw [KL, Subgroup.coe_subgroupOf]
    exact (GlobalTheory.CompanionTheory.LevelU.isClosed_UL n w).isClosedEmbedding_subtypeVal.isCompact_preimage
      (GlobalTheory.LFun.SatCompare.isOpen_isCompact_KGL w n).2
  have hC : IsClosed (K' : Set (UL n w)) := K'.isClosed_of_isOpen hO
  have hK'c : IsCompact (K' : Set (UL n w)) := hK.of_isClosed_subset hC hKK
  refine ⟨HasCompactSupport.intro' hK'c hC fun x hx => Set.indicator_of_notMem hx _, fun k hk x => ⟨?_, ?_⟩⟩
  · simp only [U.lone, Set.indicator_apply, SetLike.mem_coe, K'.mul_mem_cancel_left hk]
  · simp only [U.lone, Set.indicator_apply, SetLike.mem_coe, K'.mul_mem_cancel_right hk]

/- English proof (translation)
Proceed by induction on `k with`. Consider the case `zero => exact lone_hecke hO hKK`. Consider the case `succ j ih`. Use `PositivityTheory.Rg.BcB.F.FinConv.cv_hecke (KL n w) K' K' g (U.lpow K' g j) hg ih` as an intermediate fact. Rewrite `this` using `[inf_idem]`.

Conclude with `this`.
-/
theorem lpow_hecke {n : ℕ} {w : Pl E} {K' : Subgroup (UL n w)} (hO : IsOpen (K' : Set (UL n w))) (hKK : K' ≤ KL n w)
    {g : UL n w → ℂ} (hg : IsHecke K' g) (k : ℕ) : IsHecke K' (U.lpow K' g k) := by
  induction k with
  | zero => exact lone_hecke hO hKK
  | succ j ih =>
    have := PositivityTheory.Rg.BcB.F.FinConv.cv_hecke (KL n w) K' K' g (U.lpow K' g j) hg ih
    rw [inf_idem] at this
    exact this

/- English proof (translation)
Distinguish the cases in `hT : w ∈ d.T`. Establish `hs` using `(hM.T w hT).1`. Establish `e1 : d.KU w = iwU n w (d.b w)` using `by simp only [LocData.KU, if_pos hT]`. Establish `e2 : d.g₀ w = ∑ x ∈ (d.c w).support, ((d.c w) x * (((iwU n w (d.b w)).relIndex (KL n w) : ℕ) : ℂ)) • fU n w (d.b w) (d.ϖ w) (PositivityTheory.Rg.Bc.ArchbcB.B.lOf x)`. Use function extensionality and compare the values at `y`.

Simplify using `only [LocData.g₀, if_pos hT, Finsupp.sum, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]`. Rewrite using `[e1, e2]`. Conclude with `hk_fsum _ _ _ _ fun x => GlobalTheory.CompanionTheory.MatchPow.fU_hecke hs _ _ _ (GlobalTheory.LocFinU.continuous_cj w)`. Distinguish the cases in `hS : w ∈ d.S₀`. Establish `e1 : d.KU w = (d.K' w).subgroupOf (UL n w)` using `by simp only [LocData.KU, if_neg hT, if_pos hS]`.

Establish `e2 : d.g₀ w = fun y => d.e w y.1` using `by simp only [LocData.g₀, if_neg hT, if_pos hS]`. Establish `hk` using `(hd.K' w hS).2.2.2.2.2`. Rewrite using `[e1, e2]`. Use `⟨hk.2.2.1.comp_isClosedEmbedding (GlobalTheory.CompanionTheory.LevelU.isClosed_UL n w).isClosedEmbedding_subtypeVal, fun k hk' x => ⟨?_, ?_⟩⟩` and prove the remaining obligations. Use `hk.2.2.2 k.1 (Subgroup.mem_subgroupOf.1 hk') 1 (Subgroup.one_mem _) x.1` as an intermediate fact.

Simplify using `using this`. Use `hk.2.2.2 1 (Subgroup.one_mem _) k.1 (Subgroup.mem_subgroupOf.1 hk') x.1` as an intermediate fact. Simplify using `using this`. Establish `e2 : d.g₀ w = U.lone (d.KU w)` using `by simp only [LocData.g₀, if_neg hT, if_neg hS]`. Rewrite using `[e2]`.

Conclude with `lone_hecke hO hKK`.
-/
theorem initial_generator_isHecke {n : ℕ} (d : LocData E n) (hd : d.Ok) (hM : MLM.MOk d) {w : Pl E}
    (hO : IsOpen (d.KU w : Set (UL n w))) (hKK : d.KU w ≤ KL n w) (hw : w ∈ d.B) : IsHecke (d.KU w) (d.g₀ w) := by
  by_cases hT : w ∈ d.T
  · have hs := (hM.T w hT).1
    have e1 : d.KU w = iwU n w (d.b w) := by simp only [LocData.KU, if_pos hT]
    have e2 : d.g₀ w = ∑ x ∈ (d.c w).support,
        ((d.c w) x * (((iwU n w (d.b w)).relIndex (KL n w) : ℕ) : ℂ)) • fU n w (d.b w) (d.ϖ w) (PositivityTheory.Rg.Bc.ArchbcB.B.lOf x) := by
      funext y
      simp only [LocData.g₀, if_pos hT, Finsupp.sum, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    rw [e1, e2]
    exact hk_fsum _ _ _ _ fun x => GlobalTheory.CompanionTheory.MatchPow.fU_hecke hs _ _ _ (GlobalTheory.LocFinU.continuous_cj w)
  by_cases hS : w ∈ d.S₀
  · have e1 : d.KU w = (d.K' w).subgroupOf (UL n w) := by simp only [LocData.KU, if_neg hT, if_pos hS]
    have e2 : d.g₀ w = fun y => d.e w y.1 := by simp only [LocData.g₀, if_neg hT, if_pos hS]
    have hk := (hd.K' w hS).2.2.2.2.2
    rw [e1, e2]
    refine ⟨hk.2.2.1.comp_isClosedEmbedding (GlobalTheory.CompanionTheory.LevelU.isClosed_UL n w).isClosedEmbedding_subtypeVal,
      fun k hk' x => ⟨?_, ?_⟩⟩
    · have := hk.2.2.2 k.1 (Subgroup.mem_subgroupOf.1 hk') 1 (Subgroup.one_mem _) x.1
      simpa using this
    · have := hk.2.2.2 1 (Subgroup.one_mem _) k.1 (Subgroup.mem_subgroupOf.1 hk') x.1
      simpa using this
  · have e2 : d.g₀ w = U.lone (d.KU w) := by simp only [LocData.g₀, if_neg hT, if_neg hS]
    rw [e2]; exact lone_hecke hO hKK

end PLocMatch

open PLocMatch in
/- English proof (translation)
Introduce `E _ _ _ hE n d hd hM S hS hLev hTne hμ hGood ls m k hm hk hcnt lU hlU`. Take `⟨N, hN⟩ : ∃ N, m * k = N + 1` from `⟨m * k - 1, by have := Nat.mul_pos hm hk; omega⟩`. Establish `hO : ∀ w, IsOpen (d.KU w : Set (UL n w))` using `fun w => (hLev.2.1.1 w).1`. Establish `hKK : ∀ w, d.KU w ≤ KL n w` using `fun w => (hLev.2.1.1 w).2.1`. Establish `hg0 : ∀ w ∈ d.B, IsHecke (d.KU w) (d.g₀ w)` using `fun w hw => initial_generator_isHecke d hd hM (hO w) (hKK w) hw`.

Establish `hfamB : ∀ w ∈ d.B, U.fam d.B d.KU (d.gU m) k lU w = d.gU (N + 1) w`. Introduce `w hw`. Simplify using `only [U.fam, if_pos hw, LocData.gU]`. Rewrite using `[FBL.lpowMul E n w (d.KU w) (d.g₀ w) (hO w) (hKK w) (hg0 w hw) m k, hN]`. Establish `hBS : ∀ w ∈ d.B, w ∈ S` using `fun w hw => hLev.1 hw`.

Establish `hTB : ∀ w ∈ d.T, w ∈ d.B` using `fun w hw => by simp [LocData.B, hw]`. Establish `hPB : ∀ w, w ∉ d.B → w ∉ d.P` using `fun w hw hP => hw (by`. Simplify using `only [LocData.P, Finset.mem_union] at hP`. Simplify using `only [LocData.B, Finset.mem_union]`. Use the proof step `tauto)`.

Take `⟨w₀, hw₀⟩` from `hTne`. Use `⟨fun w hw => lpow_hecke (hO w) (hKK w) (hg0 w hw) m, ⟨w₀, hBS _ (hTB _ hw₀), fun y hy => ?_⟩, fun a ha => ?_⟩` and prove the remaining obligations. Rewrite `hy` using `[hfamB w₀ (hTB _ hw₀)]`. Conclude with `MLM.sepPowT E hE n d hd hM N w₀ hw₀ y hy`. Take `⟨hlet, hBtr, hoff, hnil⟩` from `h E n d hd a ha ls N (hcnt.trans hN)`.

Establish `hloc` using `BlockFiniteConvolution.locOk₀ E n d hd a ha`. Establish `hne : ∀ w, Nonempty (d.kap w)` using `hloc.1`. Establish `hpe : prodL d ls a = (d.fixL a :: ls.map (locL d a ha)).foldr LM.mul (d.eL a)`. Simplify using `only [prodL, dif_pos ha]`. Establish `hall : ∀ L ∈ (d.fixL a :: ls.map (locL d a ha)), L.Ok d.P ∧ d.IsLetter a ha L`.

Introduce `L hL`. Break down `List.mem_cons.1 hL with rfl | hL` into its components or cases. Conclude with `⟨hloc.2.2.1, Or.inr (Or.inr (Or.inr rfl))⟩`. Take `⟨p, -, rfl⟩` from `List.mem_map.1 hL`. Conclude with `⟨(hlet p).1, (hlet p).2.2⟩`.

Establish `hok : (prodL d ls a).Ok d.P`. Rewrite using `[hpe]`. Conclude with `ok_foldr d.P hne (hloc.2.2.2 _ (Or.inl rfl)) _ fun L hL => (hall L hL).1`. Establish `htr : IsTestP ((prodL d ls a).tr d.P d.one)` using `isTestFunction_translate d.P hne hok d.one`. Establish `hseenB : ∀ w ∈ d.B, seen ((prodL d ls a).tr d.P d.one) (prodL d ls a).t w = (prodL d ls a).tr d.P d.one w`.

Introduce `w hw`. Use `(BlockFiniteConvolution.seenTr₀ E n d hd a ha _ d.one (fun L hL => (hall L hL).2) w hw).2 fun hT => (hM.T w hT).1` as an intermediate fact. Rewrite `this` using `[← hpe]`. Conclude with `this`. Use `⟨⟨htr, hok.2, testP_seen htr hok.2, fun w hwS => ?_⟩, ⟨w₀, hBS _ (hTB _ hw₀), (hM.T w₀ hw₀).1, ?_⟩⟩` and prove the remaining obligations.

Distinguish the cases in `hwB : w ∈ d.B`. Rewrite using `[hfamB w hwB, hseenB w hwB, hBtr w hwB]`. Establish `hb` using `h1 E hE n d hd hM a ha N w hwB`. Distinguish the cases in `hmu : w ∈ d.S₀ ∨ (w ∈ d.Bad ∧ IsSplitAt w)`. Establish `e : MLM.muAt d w = d.μ w` using `by simp only [MLM.muAt, if_pos hmu]`.

Rewrite `hb` using `[e]`. Then use the resulting hypothesis. Establish `hns : ¬ IsSplitAt w`. Introduce `hs`. Simplify using `only [LocData.B, Finset.mem_union] at hwB`. Break down `hwB with (hT | hS0) | hBad` into its components or cases.

Conclude with `(hM.T w hT).1 hs`. Conclude with `hmu (Or.inl hS0)`. Conclude with `hmu (Or.inr ⟨hBad, hs⟩)`. Conclude with `(MLM.muInert E n a (n - a) w hns _ _ _ _).1 hb`. Establish `hf : U.fam d.B d.KU (d.gU m) k lU w = MLM.wordUS d w (atPlace d w ls)`.

Simplify using `only [U.fam, if_neg hwB]`. Conclude with `hlU w hwB`. Establish `e1 : (prodL d ls a).tr d.P d.one w = (MLM.wordLS d a ha w (atPlace d w ls)).tr d.P d.one w`. Simplify using `only [LM.tr, if_neg (hPB w hwB)]`. Conclude with `(hoff w hwB).1`.

Rewrite using `[hf]`. Distinguish the cases in `hs : IsSplitAt w`. Rewrite using `[seen_split hs, e1, (hoff w hwB).2]`. Conclude with `h2 E hE n d hd a ha w (hGood w hwS hwB hs) (hμ w) _`. Rewrite using `[seen_inert hs, e1, hnil w fun hG => hs hG.1]`.

Use `h3 E hE n d hd a ha w hwB fun hs' => absurd hs' hs` as an intermediate fact. Rewrite `this` using `[if_neg hs]`. Conclude with `(MLM.muInert E n a (n - a) w hs _ _ _ _).1 this`. Rewrite using `[hBtr w₀ (hTB _ hw₀)]`. Conclude with `MLM.regPowT E hE n d hd hM a ha N w₀ hw₀`.
-/
theorem locMatch (h : LocWord) (h1 : MLM.MatchLMB2) (h2 : MLM.MatchLMWordS) (h3 : MLM.MatchLMUnit) : LocMatch := by
  intro E _ _ _ hE n d hd hM S hS hLev hTne hμ hGood ls m k hm hk hcnt lU hlU
  obtain ⟨N, hN⟩ : ∃ N, m * k = N + 1 := ⟨m * k - 1, by have := Nat.mul_pos hm hk; omega⟩
  have hO : ∀ w, IsOpen (d.KU w : Set (UL n w)) := fun w => (hLev.2.1.1 w).1
  have hKK : ∀ w, d.KU w ≤ KL n w := fun w => (hLev.2.1.1 w).2.1
  have hg0 : ∀ w ∈ d.B, IsHecke (d.KU w) (d.g₀ w) := fun w hw => initial_generator_isHecke d hd hM (hO w) (hKK w) hw
  have hfamB : ∀ w ∈ d.B, U.fam d.B d.KU (d.gU m) k lU w = d.gU (N + 1) w := by
    intro w hw
    simp only [U.fam, if_pos hw, LocData.gU]
    rw [FBL.lpowMul E n w (d.KU w) (d.g₀ w) (hO w) (hKK w) (hg0 w hw) m k, hN]
  have hBS : ∀ w ∈ d.B, w ∈ S := fun w hw => hLev.1 hw
  have hTB : ∀ w ∈ d.T, w ∈ d.B := fun w hw => by simp [LocData.B, hw]
  have hPB : ∀ w, w ∉ d.B → w ∉ d.P := fun w hw hP => hw (by
    simp only [LocData.P, Finset.mem_union] at hP; simp only [LocData.B, Finset.mem_union]; tauto)
  obtain ⟨w₀, hw₀⟩ := hTne
  refine ⟨fun w hw => lpow_hecke (hO w) (hKK w) (hg0 w hw) m, ⟨w₀, hBS _ (hTB _ hw₀), fun y hy => ?_⟩, fun a ha => ?_⟩
  · rw [hfamB w₀ (hTB _ hw₀)] at hy
    exact MLM.sepPowT E hE n d hd hM N w₀ hw₀ y hy
  obtain ⟨hlet, hBtr, hoff, hnil⟩ := h E n d hd a ha ls N (hcnt.trans hN)
  have hloc := BlockFiniteConvolution.locOk₀ E n d hd a ha
  have hne : ∀ w, Nonempty (d.kap w) := hloc.1
  have hpe : prodL d ls a = (d.fixL a :: ls.map (locL d a ha)).foldr LM.mul (d.eL a) := by
    simp only [prodL, dif_pos ha]
  have hall : ∀ L ∈ (d.fixL a :: ls.map (locL d a ha)), L.Ok d.P ∧ d.IsLetter a ha L := by
    intro L hL
    rcases List.mem_cons.1 hL with rfl | hL
    · exact ⟨hloc.2.2.1, Or.inr (Or.inr (Or.inr rfl))⟩
    · obtain ⟨p, -, rfl⟩ := List.mem_map.1 hL
      exact ⟨(hlet p).1, (hlet p).2.2⟩
  have hok : (prodL d ls a).Ok d.P := by
    rw [hpe]; exact ok_foldr d.P hne (hloc.2.2.2 _ (Or.inl rfl)) _ fun L hL => (hall L hL).1
  have htr : IsTestP ((prodL d ls a).tr d.P d.one) := isTestFunction_translate d.P hne hok d.one
  have hseenB : ∀ w ∈ d.B, seen ((prodL d ls a).tr d.P d.one) (prodL d ls a).t w = (prodL d ls a).tr d.P d.one w := by
    intro w hw
    have := (BlockFiniteConvolution.seenTr₀ E n d hd a ha _ d.one (fun L hL => (hall L hL).2) w hw).2 fun hT => (hM.T w hT).1
    rw [← hpe] at this; exact this
  refine ⟨⟨htr, hok.2, testP_seen htr hok.2, fun w hwS => ?_⟩,
    ⟨w₀, hBS _ (hTB _ hw₀), (hM.T w₀ hw₀).1, ?_⟩⟩
  · by_cases hwB : w ∈ d.B
    · rw [hfamB w hwB, hseenB w hwB, hBtr w hwB]
      have hb := h1 E hE n d hd hM a ha N w hwB
      by_cases hmu : w ∈ d.S₀ ∨ (w ∈ d.Bad ∧ IsSplitAt w)
      · have e : MLM.muAt d w = d.μ w := by simp only [MLM.muAt, if_pos hmu]
        rwa [e] at hb
      · have hns : ¬ IsSplitAt w := by
          intro hs
          simp only [LocData.B, Finset.mem_union] at hwB
          rcases hwB with (hT | hS0) | hBad
          · exact (hM.T w hT).1 hs
          · exact hmu (Or.inl hS0)
          · exact hmu (Or.inr ⟨hBad, hs⟩)
        exact (MLM.muInert E n a (n - a) w hns _ _ _ _).1 hb
    · have hf : U.fam d.B d.KU (d.gU m) k lU w = MLM.wordUS d w (atPlace d w ls) := by
        simp only [U.fam, if_neg hwB]; exact hlU w hwB
      have e1 : (prodL d ls a).tr d.P d.one w = (MLM.wordLS d a ha w (atPlace d w ls)).tr d.P d.one w := by
        simp only [LM.tr, if_neg (hPB w hwB)]; exact (hoff w hwB).1
      rw [hf]
      by_cases hs : IsSplitAt w
      · rw [seen_split hs, e1, (hoff w hwB).2]
        exact h2 E hE n d hd a ha w (hGood w hwS hwB hs) (hμ w) _
      · rw [seen_inert hs, e1, hnil w fun hG => hs hG.1]
        have := h3 E hE n d hd a ha w hwB fun hs' => absurd hs' hs
        rw [if_neg hs] at this
        exact (MLM.muInert E n a (n - a) w hs _ _ _ _).1 this
  · rw [hBtr w₀ (hTB _ hw₀)]
    exact MLM.regPowT E hE n d hd hM a ha N w₀ hw₀

end PositivityTheory.Rg.BcB.F.B3

end

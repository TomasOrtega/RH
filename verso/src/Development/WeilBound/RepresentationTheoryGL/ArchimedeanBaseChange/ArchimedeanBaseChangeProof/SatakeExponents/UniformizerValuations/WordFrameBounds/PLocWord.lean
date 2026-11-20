import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.WordFrameBounds.WordIdAt
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.AdelicHeckeBlocks.Imports
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.AdelicHeckeBlocks.DoubleSumFinprodFactor

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

namespace PLocWord

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ} (d : LocData E n)

def HG (a : ℕ) (L : LM d.kap a (n - a)) : Prop :=
  (∀ w ∈ d.P, ∀ x y, IsHecke (d.lev a w) (L.m w x y)) ∧ (∀ w ∉ d.P, IsHecke (d.lev a w) (L.s w)) ∧
    ∀ w, IsHecke (d.lev₂ a w) (L.t w)

/- English proof (translation)
Distinguish the cases in `hP : w ∈ d.P`. Conclude with `LocComm.lev_ok d hd ha hP`. Establish `hT : w ∉ d.T` using `fun h => hP (Finset.mem_union_left _ h)`. Distinguish the cases in `hSB : w ∈ d.S₀ ∪ d.Bad`. Rewrite using `[PSeen.lev_eq d hd hSB]`.

Conclude with `PSeen.L_ok d hd ha hSB`. Simplify using `only [LocData.lev, if_neg hT, if_neg hSB]`. Conclude with `⟨LocComm.isOpen_levelSubgroup' _ _ _, le_rfl⟩`.
-/
theorem levOk (hd : d.Ok) {a : ℕ} (ha : a ≤ n) (w : Pl E) :
    IsOpen (d.lev a w : Set (GLw a w × GLw (n - a) w)) ∧ d.lev a w ≤ K2 a (n - a) w := by
  by_cases hP : w ∈ d.P
  · exact LocComm.lev_ok d hd ha hP
  · have hT : w ∉ d.T := fun h => hP (Finset.mem_union_left _ h)
    by_cases hSB : w ∈ d.S₀ ∪ d.Bad
    · rw [PSeen.lev_eq d hd hSB]
      exact PSeen.L_ok d hd ha hSB
    · simp only [LocData.lev, if_neg hT, if_neg hSB]
      exact ⟨LocComm.isOpen_levelSubgroup' _ _ _, le_rfl⟩

def idA (hd : d.Ok) {a : ℕ} (ha : a ≤ n) (w : Pl E) := idemAlg E a (n - a) w _ (levOk d hd ha w).1 (levOk d hd ha w).2

def idB (hd : d.Ok) {a : ℕ} (ha : a ≤ n) (w : Pl E) :=
  idemAlg E a (n - a) w _ (PSeen.lev₂_ok d hd ha w).1 (PSeen.lev₂_ok d hd ha w).2

/- English proof (translation)
Unfold `LocData.diag`. Use `split_ifs`. Conclude with `hf`. Conclude with `LocComm.isHecke_zero _`.
-/
theorem diagH {a : ℕ} {w : Pl E} {K : Subgroup (GLw a w × GLw (n - a) w)} {f : LF a (n - a) w} (hf : IsHecke K f)
    (x y : d.kap w) : IsHecke K (d.diag (fun _ => f) x y) := by
  unfold LocData.diag
  split_ifs
  · exact hf
  · exact LocComm.isHecke_zero _

/- English proof (translation)
Assemble the required witnesses or components as `⟨fun w _ x y => diagH d (idA d hd ha w).1 x y, fun w _ => (idA d hd ha w).1, fun w => (idB d hd ha w).1⟩`.
-/
theorem hgEL (hd : d.Ok) {a : ℕ} (ha : a ≤ n) : HG d a (d.eL a) :=
  ⟨fun w _ x y => diagH d (idA d hd ha w).1 x y, fun w _ => (idA d hd ha w).1, fun w => (idB d hd ha w).1⟩

/- English proof (translation)
Use `⟨fun w hw x y => ?_, fun w hw => ?_, fun w => ?_⟩` and prove the remaining obligations. Use `show IsHecke _ (∑ z, mconv (L.m w x z) (L'.m w z y))`. Conclude with `PSeen.isHecke_fsum _ Finset.univ (fun z => mconv (L.m w x z) (L'.m w z y)) fun z _ => PSeen.mconv_hecke _ (h.1 w hw x z) (h'.1 w hw z y)`. Conclude with `PSeen.mconv_hecke _ (h.2.1 w hw) (h'.2.1 w hw)`. Conclude with `PSeen.mconv_hecke _ (h.2.2 w) (h'.2.2 w)`.
-/
theorem hg_mul {a : ℕ} {L L' : LM d.kap a (n - a)} (h : HG d a L) (h' : HG d a L') : HG d a (L.mul L') := by
  refine ⟨fun w hw x y => ?_, fun w hw => ?_, fun w => ?_⟩
  · show IsHecke _ (∑ z, mconv (L.m w x z) (L'.m w z y))
    exact PSeen.isHecke_fsum _ Finset.univ (fun z => mconv (L.m w x z) (L'.m w z y))
      fun z _ => PSeen.mconv_hecke _ (h.1 w hw x z) (h'.1 w hw z y)
  · exact PSeen.mconv_hecke _ (h.2.1 w hw) (h'.2.1 w hw)
  · exact PSeen.mconv_hecke _ (h.2.2 w) (h'.2.2 w)

/- English proof (translation)
Assemble the required witnesses or components as `⟨fun w hw x y => ((idA d hd ha w).2.2 _ (h.1 w hw y x)).2.2, fun w hw => ((idA d hd ha w).2.2 _ (h.2.1 w hw)).2.2, fun w => ((idB d hd ha w).2.2 _ (h.2.2 w)).2.2⟩`.
-/
theorem hg_adj (hd : d.Ok) {a : ℕ} (ha : a ≤ n) {L : LM d.kap a (n - a)} (h : HG d a L) : HG d a L.adj :=
  ⟨fun w hw x y => ((idA d hd ha w).2.2 _ (h.1 w hw y x)).2.2, fun w hw => ((idA d hd ha w).2.2 _ (h.2.1 w hw)).2.2,
    fun w => ((idB d hd ha w).2.2 _ (h.2.2 w)).2.2⟩

/- English proof (translation)
Assemble the required witnesses or components as `⟨fun w hw x y => LocComm.hecke_beta d (PositivityTheory.Rg.BcN.F2.LocOpPf.locOp3 E) hd ha hw x y, fun w _ => (idA d hd ha w).1, fun w => (idB d hd ha w).1⟩`.
-/
theorem hgBeta (hd : d.Ok) {a : ℕ} (ha : a ≤ n) : HG d a (d.betaL a ha) :=
  ⟨fun w hw x y => LocComm.hecke_beta d (PositivityTheory.Rg.BcN.F2.LocOpPf.locOp3 E) hd ha hw x y, fun w _ => (idA d hd ha w).1,
    fun w => (idB d hd ha w).1⟩

/- English proof (translation)
Use `⟨fun w hw x y => ?_, fun w _ => ?_, fun w => ?_⟩` and prove the remaining obligations. Rewrite using `[LocComm.gen_m d hL]`. Conclude with `(hgEL d hd ha).1 w hw x y`. Break down `LocComm.generator_first_levi_position d hL w with h | ⟨hg, k, h⟩` into its components or cases. Rewrite using `[h]`.

Conclude with `(idA d hd ha w).1`. Rewrite using `[h, LocComm.lev_good d hg]`. Conclude with `LocComm.hecke_hc d hd ha hg k`. Break down `LocComm.generator_second_levi_position d hL w with h | ⟨hg, k, h⟩` into its components or cases. Rewrite using `[h]`.

Conclude with `(idB d hd ha w).1`. Rewrite using `[h, LocComm.lev₂_good d hg]`. Conclude with `LocComm.hecke_hc d hd ha hg k`.
-/
theorem hgGen (hd : d.Ok) {a : ℕ} (ha : a ≤ n) {L : LM d.kap a (n - a)} (hL : d.IsGen a ha L) : HG d a L := by
  refine ⟨fun w hw x y => ?_, fun w _ => ?_, fun w => ?_⟩
  · rw [LocComm.gen_m d hL]
    exact (hgEL d hd ha).1 w hw x y
  · rcases LocComm.generator_first_levi_position d hL w with h | ⟨hg, k, h⟩
    · rw [h]; exact (idA d hd ha w).1
    · rw [h, LocComm.lev_good d hg]; exact LocComm.hecke_hc d hd ha hg k
  · rcases LocComm.generator_second_levi_position d hL w with h | ⟨hg, k, h⟩
    · rw [h]; exact (idB d hd ha w).1
    · rw [h, LocComm.lev₂_good d hg]; exact LocComm.hecke_hc d hd ha hg k

/- English proof (translation)
Use `⟨⟨fun w hw => ?_, fun w hw => ?_, ?_⟩, ⟨fun w hw => ?_, fun w hw => ?_, ?_⟩⟩` and prove the remaining obligations. Use function extensionality and compare the values at `x y show ∑ z, mconv (d.diag (fun _ => idem (d.lev a w)) x z) (X.m w z y) = X.m w x y`. Rewrite using `[LocComm.sum_diag_left]`. Conclude with `((idA d hd ha w).2.2 _ (h.1 w hw x y)).1`. Conclude with `((idA d hd ha w).2.2 _ (h.2.1 w hw)).1`.

Use function extensionality and compare the values at `w`. Conclude with `((idB d hd ha w).2.2 _ (h.2.2 w)).1`. Use function extensionality and compare the values at `x y show ∑ z, mconv (X.m w x z) (d.diag (fun _ => idem (d.lev a w)) z y) = X.m w x y`. Rewrite using `[LocComm.sum_diag_right]`. Conclude with `((idA d hd ha w).2.2 _ (h.1 w hw x y)).2.1`.

Conclude with `((idA d hd ha w).2.2 _ (h.2.1 w hw)).2.1`. Use function extensionality and compare the values at `w`. Conclude with `((idB d hd ha w).2.2 _ (h.2.2 w)).2.1`.
-/
theorem unit_eqv (hd : d.Ok) {a : ℕ} (ha : a ≤ n) {X : LM d.kap a (n - a)} (h : HG d a X) :
    ((d.eL a).mul X).Eqv d.P X ∧ (X.mul (d.eL a)).Eqv d.P X := by
  refine ⟨⟨fun w hw => ?_, fun w hw => ?_, ?_⟩, ⟨fun w hw => ?_, fun w hw => ?_, ?_⟩⟩
  · funext x y
    show ∑ z, mconv (d.diag (fun _ => idem (d.lev a w)) x z) (X.m w z y) = X.m w x y
    rw [LocComm.sum_diag_left]
    exact ((idA d hd ha w).2.2 _ (h.1 w hw x y)).1
  · exact ((idA d hd ha w).2.2 _ (h.2.1 w hw)).1
  · funext w
    exact ((idB d hd ha w).2.2 _ (h.2.2 w)).1
  · funext x y
    show ∑ z, mconv (X.m w x z) (d.diag (fun _ => idem (d.lev a w)) z y) = X.m w x y
    rw [LocComm.sum_diag_right]
    exact ((idA d hd ha w).2.2 _ (h.1 w hw x y)).2.1
  · exact ((idA d hd ha w).2.2 _ (h.2.1 w hw)).2.1
  · funext w
    exact ((idB d hd ha w).2.2 _ (h.2.2 w)).2.1

/- English proof (translation)
Use `⟨fun x y => ?_, Fm.isTestFunction_star h.2⟩` and prove the remaining obligations. Rewrite using `[Fm.adj_ent]`. Conclude with `Fm.isTestFunction_star (h.1 y x)`.
-/
theorem ok_adj {a : ℕ} {L : LM d.kap a (n - a)} (h : L.Ok d.P) : L.adj.Ok d.P := by
  refine ⟨fun x y => ?_, Fm.isTestFunction_star h.2⟩
  rw [Fm.adj_ent]
  exact Fm.isTestFunction_star (h.1 y x)

/- English proof (translation)
Break down `p with u | u | ⟨⟨w', hg⟩, k, intersection_update_fsHerm_neg_one, st⟩` into its components or cases. Conclude with `Or.inl rfl`. Conclude with `Or.inr (Or.inl (Or.inl rfl))`. Establish `hG : d.IsGen a ha (d.hL a ha w' k intersection_update_fsHerm_neg_one)` using `Or.inr ⟨w', k, intersection_update_fsHerm_neg_one, hg, rfl⟩`. Consider the cases of `st`.

Conclude with `Or.inr (Or.inl (by simpa [locL] using hG))`. Conclude with `Or.inr (Or.inr ⟨_, hG, by simp [locL]⟩)`.
-/
theorem kinds {a : ℕ} (ha : a ≤ n) (p : LL d) : locL d a ha p = d.betaL a ha ∨ d.IsGen a ha (locL d a ha p) ∨
    ∃ L, d.IsGen a ha L ∧ locL d a ha p = L.adj := by
  rcases p with u | u | ⟨⟨w', hg⟩, k, intersection_update_fsHerm_neg_one, st⟩
  · exact Or.inl rfl
  · exact Or.inr (Or.inl (Or.inl rfl))
  · have hG : d.IsGen a ha (d.hL a ha w' k intersection_update_fsHerm_neg_one) := Or.inr ⟨w', k, intersection_update_fsHerm_neg_one, hg, rfl⟩
    cases st
    · exact Or.inr (Or.inl (by simpa [locL] using hG))
    · exact Or.inr (Or.inr ⟨_, hG, by simp [locL]⟩)

/- English proof (translation)
Break down `kinds d ha p with h | h | ⟨L, hL, h⟩` into its components or cases. Rewrite using `[h]`. Conclude with `hgBeta d hd ha`. Conclude with `hgGen d hd ha h`. Rewrite using `[h]`.

Conclude with `hg_adj d hd ha (hgGen d hd ha hL)`.
-/
theorem hgL (hd : d.Ok) {a : ℕ} (ha : a ≤ n) (p : LL d) : HG d a (locL d a ha p) := by
  rcases kinds d ha p with h | h | ⟨L, hL, h⟩
  · rw [h]; exact hgBeta d hd ha
  · exact hgGen d hd ha h
  · rw [h]; exact hg_adj d hd ha (hgGen d hd ha hL)

/- English proof (translation)
The claim follows from `| [] => hgEL d hd ha | p :: ls => hg_mul d (hgL d hd ha p) (hg_foldr hd ha ls)`.
-/
theorem hg_foldr (hd : d.Ok) {a : ℕ} (ha : a ≤ n) : ∀ ls : List (LL d), HG d a ((ls.map (locL d a ha)).foldr LM.mul (d.eL a))
  | [] => hgEL d hd ha
  | p :: ls => hg_mul d (hgL d hd ha p) (hg_foldr hd ha ls)

def AtW {a : ℕ} (w : Pl E) (L L' : LM d.kap a (n - a)) : Prop :=
  (w ∈ d.P → L.m w = L'.m w) ∧ (w ∉ d.P → L.s w = L'.s w)

/- English proof (translation)
Assemble the required witnesses or components as `⟨fun _ => rfl, fun _ => rfl⟩`.
-/
theorem atW_refl {a : ℕ} (w : Pl E) (L : LM d.kap a (n - a)) : AtW d w L L := ⟨fun _ => rfl, fun _ => rfl⟩

/- English proof (translation)
Assemble the required witnesses or components as `⟨fun hw => (h.1 hw).trans (h'.1 hw), fun hw => (h.2 hw).trans (h'.2 hw)⟩`.
-/
theorem atW_trans {a : ℕ} {w : Pl E} {L₁ L₂ L₃ : LM d.kap a (n - a)} (h : AtW d w L₁ L₂) (h' : AtW d w L₂ L₃) :
    AtW d w L₁ L₃ := ⟨fun hw => (h.1 hw).trans (h'.1 hw), fun hw => (h.2 hw).trans (h'.2 hw)⟩

/- English proof (translation)
Assemble the required witnesses or components as `⟨fun hw => h.1 w hw, fun hw => h.2.1 w hw⟩`.
-/
theorem atW_of_eqv {a : ℕ} {w : Pl E} {L L' : LM d.kap a (n - a)} (h : L.Eqv d.P L') : AtW d w L L' :=
  ⟨fun hw => h.1 w hw, fun hw => h.2.1 w hw⟩

/- English proof (translation)
Use `⟨fun hw => ?_, fun hw => ?_⟩` and prove the remaining obligations. Use `show (fun x y => ∑ z, mconv (A.m w x z) (B.m w z y)) = fun x y => ∑ z, mconv (A'.m w x z) (B'.m w z y)`. Rewrite using `[h.1 hw, h'.1 hw]`. Use `show mconv (A.s w) (B.s w) = mconv (A'.s w) (B'.s w)`. Rewrite using `[h.2 hw, h'.2 hw]`.
-/
theorem atW_mul {a : ℕ} {w : Pl E} {A A' B B' : LM d.kap a (n - a)} (h : AtW d w A A') (h' : AtW d w B B') :
    AtW d w (A.mul B) (A'.mul B') := by
  refine ⟨fun hw => ?_, fun hw => ?_⟩
  · show (fun x y => ∑ z, mconv (A.m w x z) (B.m w z y)) = fun x y => ∑ z, mconv (A'.m w x z) (B'.m w z y)
    rw [h.1 hw, h'.1 hw]
  · show mconv (A.s w) (B.s w) = mconv (A'.s w) (B'.s w)
    rw [h.2 hw, h'.2 hw]

/- English proof (translation)
Unfold `LM.tr`. Use `split_ifs with hw`. Rewrite using `[h.1 hw]`. Conclude with `h.2 hw`.
-/
theorem atW_tr {a : ℕ} {w : Pl E} {L L' : LM d.kap a (n - a)} (h : AtW d w L L') (N : ∀ w, d.kap w → d.kap w → ℂ) :
    L.tr d.P N w = L'.tr d.P N w := by
  unfold LM.tr
  split_ifs with hw
  · rw [h.1 hw]
  · exact h.2 hw

/- English proof (translation)
Establish `hs : L.s w = idem (d.lev a w)`. Break down `LocComm.generator_first_levi_position d hL w with h | ⟨h, -⟩` into its components or cases. Conclude with `h`. Conclude with `absurd h (PSeen.notGood d hw)`. Use `⟨⟨fun _ => by rw [LocComm.gen_m d hL], fun _ => hs⟩, ⟨fun _ => by rw [LocComm.adj_m d hL], fun _ => ?_⟩⟩` and prove the remaining obligations.

Use `show lfStar (L.s w) = idem (d.lev a w)`. Rewrite using `[hs, LocComm.lfStar_idem]`.
-/
theorem genAtW {a : ℕ} {ha : a ≤ n} {w : Pl E} (hw : w ∈ d.B) {L : LM d.kap a (n - a)} (hL : d.IsGen a ha L) :
    AtW d w L (d.eL a) ∧ AtW d w L.adj (d.eL a) := by
  have hs : L.s w = idem (d.lev a w) := by
    rcases LocComm.generator_first_levi_position d hL w with h | ⟨h, -⟩
    · exact h
    · exact absurd h (PSeen.notGood d hw)
  refine ⟨⟨fun _ => by rw [LocComm.gen_m d hL], fun _ => hs⟩, ⟨fun _ => by rw [LocComm.adj_m d hL], fun _ => ?_⟩⟩
  show lfStar (L.s w) = idem (d.lev a w)
  rw [hs, LocComm.lfStar_idem]

def cw (a : ℕ) (ha : a ≤ n) : ℕ → LM d.kap a (n - a)
  | 0 => d.eL a
  | j + 1 => MLM.pw (d.betaL a ha) j

/- English proof (translation)
The claim follows from `| 0 => atW_of_eqv d (unit_eqv d hd ha (hgBeta d hd ha)).2 | _ + 1 => atW_refl d w _`.
-/
theorem beta_cw (hd : d.Ok) {a : ℕ} (ha : a ≤ n) (w : Pl E) :
    ∀ c, AtW d w ((d.betaL a ha).mul (cw d a ha c)) (cw d a ha (c + 1))
  | 0 => atW_of_eqv d (unit_eqv d hd ha (hgBeta d hd ha)).2
  | _ + 1 => atW_refl d w _

/- English proof (translation)
The claim follows from `| [] => by rw [List.countP_nil] exact atW_refl d w _ | p :: ls => by have ih := prodW hd ha hw ls have hX := hg_foldr d hd ha ls have nb : ∀ L : LM d.kap a (n - a), AtW d w L (d.eL a) → AtW d w (L.mul ((ls.map (locL d a ha)).foldr LM.mul (d.eL a))) (cw d a ha (ls.countP Sum.isLef …`.
-/
theorem prodW (hd : d.Ok) {a : ℕ} (ha : a ≤ n) {w : Pl E} (hw : w ∈ d.B) : ∀ ls : List (LL d),
    AtW d w ((ls.map (locL d a ha)).foldr LM.mul (d.eL a)) (cw d a ha (ls.countP Sum.isLeft))
  | [] => by
    rw [List.countP_nil]
    exact atW_refl d w _
  | p :: ls => by
    have ih := prodW hd ha hw ls
    have hX := hg_foldr d hd ha ls
    have nb : ∀ L : LM d.kap a (n - a), AtW d w L (d.eL a) →
        AtW d w (L.mul ((ls.map (locL d a ha)).foldr LM.mul (d.eL a))) (cw d a ha (ls.countP Sum.isLeft)) :=
      fun L hL => atW_trans d (atW_trans d (atW_mul d hL (atW_refl d w _)) (atW_of_eqv d (unit_eqv d hd ha hX).1)) ih
    rcases p with u | u | ⟨⟨w', hg⟩, k, intersection_update_fsHerm_neg_one, st⟩
    · have hc : (Sum.inl u :: ls : List (LL d)).countP Sum.isLeft = ls.countP Sum.isLeft + 1 := by
        simp [List.countP_cons]
      rw [hc]
      exact atW_trans d (atW_mul d (atW_refl d w (d.betaL a ha)) ih) (beta_cw d hd ha w _)
    · have hc : (Sum.inr (Sum.inl u) :: ls : List (LL d)).countP Sum.isLeft = ls.countP Sum.isLeft := by
        simp [List.countP_cons]
      rw [hc]
      exact nb _ (atW_refl d w _)
    · have hc : (Sum.inr (Sum.inr ⟨⟨w', hg⟩, k, intersection_update_fsHerm_neg_one, st⟩) :: ls : List (LL d)).countP Sum.isLeft =
          ls.countP Sum.isLeft := by
        simp [List.countP_cons]
      rw [hc]
      have hG : d.IsGen a ha (d.hL a ha w' k intersection_update_fsHerm_neg_one) := Or.inr ⟨w', k, intersection_update_fsHerm_neg_one, hg, rfl⟩
      cases st
      · exact nb _ (genAtW d hw hG).1
      · exact nb _ (genAtW d hw hG).2

/- English proof (translation)
Use `⟨?_, ?_⟩` and prove the remaining obligations. Use `show mconv (l.s w) (X.s w) = X.s w`. Rewrite using `[hs]`. Conclude with `((idA d hd ha w).2.2 _ (hX.2.1 w hP)).1`. Use `show mconv (l.t w) (X.t w) = X.t w`.

Rewrite using `[ht]`. Conclude with `((idB d hd ha w).2.2 _ (hX.2.2 w)).1`.
-/
theorem offStep (hd : d.Ok) {a : ℕ} (ha : a ≤ n) {w : Pl E} (hP : w ∉ d.P) {l X : LM d.kap a (n - a)} (hX : HG d a X)
    (hs : l.s w = idem (d.lev a w)) (ht : l.t w = idem (d.lev₂ a w)) :
    (l.mul X).s w = X.s w ∧ (l.mul X).t w = X.t w := by
  refine ⟨?_, ?_⟩
  · show mconv (l.s w) (X.s w) = X.s w
    rw [hs]
    exact ((idA d hd ha w).2.2 _ (hX.2.1 w hP)).1
  · show mconv (l.t w) (X.t w) = X.t w
    rw [ht]
    exact ((idB d hd ha w).2.2 _ (hX.2.2 w)).1

/- English proof (translation)
Apply the tactic sequence `cases intersection_update_fsHerm_neg_one <;> simp [LocData.hL, Function.update_of_ne hne, LocData.eL]`.
-/
theorem hL_off {a : ℕ} (ha : a ≤ n) {w w' : Pl E} (hne : w ≠ w') (k : ℕ) (intersection_update_fsHerm_neg_one : Bool) :
    (d.hL a ha w' k intersection_update_fsHerm_neg_one).s w = idem (d.lev a w) ∧ (d.hL a ha w' k intersection_update_fsHerm_neg_one).t w = idem (d.lev₂ a w) := by
  cases intersection_update_fsHerm_neg_one <;> simp [LocData.hL, Function.update_of_ne hne, LocData.eL]

/- English proof (translation)
The claim follows from `| [] => ⟨rfl, rfl⟩ | p :: ls => by obtain ⟨ih1, ih2⟩ := offB hd ha hP ls have hX := hg_foldr d hd ha ls have fin : ∀ l : LM d.kap a (n - a), l.s w = idem (d.lev a w) → l.t w = idem (d.lev₂ a w) → (l.mul ((ls.map (locL d a ha)).foldr LM.mul (d.eL a))).s w = (MLM.wordLS d a ha w (a …`.
-/
theorem offB (hd : d.Ok) {a : ℕ} (ha : a ≤ n) {w : Pl E} (hP : w ∉ d.P) : ∀ ls : List (LL d),
    ((ls.map (locL d a ha)).foldr LM.mul (d.eL a)).s w = (MLM.wordLS d a ha w (atPlace d w ls)).s w ∧
    ((ls.map (locL d a ha)).foldr LM.mul (d.eL a)).t w = (MLM.wordLS d a ha w (atPlace d w ls)).t w
  | [] => ⟨rfl, rfl⟩
  | p :: ls => by
    obtain ⟨ih1, ih2⟩ := offB hd ha hP ls
    have hX := hg_foldr d hd ha ls
    have fin : ∀ l : LM d.kap a (n - a), l.s w = idem (d.lev a w) → l.t w = idem (d.lev₂ a w) →
        (l.mul ((ls.map (locL d a ha)).foldr LM.mul (d.eL a))).s w = (MLM.wordLS d a ha w (atPlace d w ls)).s w ∧
        (l.mul ((ls.map (locL d a ha)).foldr LM.mul (d.eL a))).t w = (MLM.wordLS d a ha w (atPlace d w ls)).t w := by
      intro l hs ht
      obtain ⟨e1, e2⟩ := offStep d hd ha hP hX hs ht
      exact ⟨e1.trans ih1, e2.trans ih2⟩
    rcases p with u | u | ⟨⟨w', hg⟩, k, intersection_update_fsHerm_neg_one, st⟩
    · have e : atPlace d w (Sum.inl u :: ls) = atPlace d w ls := by simp [atPlace]
      rw [e]
      exact fin _ rfl rfl
    · have e : atPlace d w (Sum.inr (Sum.inl u) :: ls) = atPlace d w ls := by simp [atPlace]
      rw [e]
      exact fin _ rfl rfl
    · by_cases hw : w' = w
      · subst hw
        have e : atPlace d w' (Sum.inr (Sum.inr ⟨⟨w', hg⟩, k, intersection_update_fsHerm_neg_one, st⟩) :: ls) = (k, intersection_update_fsHerm_neg_one, st) :: atPlace d w' ls := by
          simp [atPlace]
        rw [e]
        refine ⟨?_, ?_⟩
        · show mconv ((locL d a ha (Sum.inr (Sum.inr ⟨⟨w', hg⟩, k, intersection_update_fsHerm_neg_one, st⟩))).s w')
              (((ls.map (locL d a ha)).foldr LM.mul (d.eL a)).s w') =
            mconv ((if st then (d.hL a ha w' k intersection_update_fsHerm_neg_one).adj else d.hL a ha w' k intersection_update_fsHerm_neg_one).s w')
              ((MLM.wordLS d a ha w' (atPlace d w' ls)).s w')
          rw [ih1]
          rfl
        · show mconv ((locL d a ha (Sum.inr (Sum.inr ⟨⟨w', hg⟩, k, intersection_update_fsHerm_neg_one, st⟩))).t w')
              (((ls.map (locL d a ha)).foldr LM.mul (d.eL a)).t w') =
            mconv ((if st then (d.hL a ha w' k intersection_update_fsHerm_neg_one).adj else d.hL a ha w' k intersection_update_fsHerm_neg_one).t w')
              ((MLM.wordLS d a ha w' (atPlace d w' ls)).t w')
          rw [ih2]
          rfl
      · have e : atPlace d w (Sum.inr (Sum.inr ⟨⟨w', hg⟩, k, intersection_update_fsHerm_neg_one, st⟩) :: ls) = atPlace d w ls := by
          simp [atPlace, hw]
        rw [e]
        obtain ⟨hs, ht⟩ := hL_off d ha (Ne.symm hw) k intersection_update_fsHerm_neg_one
        cases st
        · exact fin _ hs ht
        · refine fin _ ?_ ?_
          · show lfStar ((d.hL a ha w' k intersection_update_fsHerm_neg_one).s w) = _
            rw [hs, LocComm.lfStar_idem]
          · show lfStar ((d.hL a ha w' k intersection_update_fsHerm_neg_one).t w) = _
            rw [ht, LocComm.lfStar_idem]

/- English proof (translation)
The claim follows from `| [] => rfl | p :: ls => by have ih := atPlace_nil hw ls rcases p with u | u | ⟨⟨w', hg⟩, x⟩ · simpa [atPlace] using ih · simpa [atPlace] using ih · have hne : w' ≠ w := fun e => hw (e ▸ hg) simpa [atPlace, hne] using ih`.
-/
theorem atPlace_nil {w : Pl E} (hw : ¬ d.Good w) : ∀ ls : List (LL d), atPlace d w ls = []
  | [] => rfl
  | p :: ls => by
    have ih := atPlace_nil hw ls
    rcases p with u | u | ⟨⟨w', hg⟩, x⟩
    · simpa [atPlace] using ih
    · simpa [atPlace] using ih
    · have hne : w' ≠ w := fun e => hw (e ▸ hg)
      simpa [atPlace, hne] using ih

end PLocWord

open PLocWord in
/- English proof (translation)
Introduce `E _ _ _ n d hd a ha ls N hN`. Establish `hP : ∀ w, w ∉ d.B → w ∉ d.P` using `fun w hw h => hw (by`. Simplify using `only [LocData.B, LocData.P, Finset.mem_union] at h ⊢`. Use the proof step `tauto)`. Establish `hprod : prodL d ls a = (d.fixL a).mul ((ls.map (locL d a ha)).foldr LM.mul (d.eL a))`.

Rewrite using `[prodL, dif_pos ha]`. Both sides reduce to the same expression. Use `⟨fun p => ⟨?_, (unit_eqv d hd ha (hgL d hd ha p)).1, ?_⟩, fun w hw => ?_, fun w hw => ?_, fun w hw => atPlace_nil d hw ls⟩` and prove the remaining obligations. Establish `hOk` using `BlockFiniteConvolution.locOk₀ E n d hd a ha`. Break down `kinds d ha p with h | h | ⟨L, hL, h⟩` into its components or cases.

Rewrite using `[h]`. Conclude with `hOk.2.1`. Conclude with `hOk.2.2.2 _ h`. Rewrite using `[h]`. Conclude with `ok_adj d (hOk.2.2.2 _ hL)`.

Break down `kinds d ha p with h | h | ⟨L, hL, h⟩` into its components or cases. Conclude with `Or.inr (Or.inr (Or.inl h))`. Conclude with `Or.inl h`. Conclude with `Or.inr (Or.inl ⟨L, hL, h⟩)`. Rewrite using `[hprod]`.

Establish `h1` using `atW_mul d (atW_refl d w (d.fixL a)) (prodW d hd ha hw ls)`. Rewrite `h1` using `[hN]`. Conclude with `atW_tr d h1 d.one`. Establish `hwP` using `hP w hw`. Establish `hBad : w ∉ d.Bad` using `fun h => hw (by simp [LocData.B, h])`.

Take `⟨e1, e2⟩` from `offB d hd ha hwP ls`. Establish `hs : (d.fixL a).s w = idem (d.lev a w)` using `by simp [LocData.fixL, hBad]`. Take `⟨f1, f2⟩` from `offStep d hd ha hwP (hg_foldr d hd ha ls) hs rfl`. Rewrite using `[hprod]`. Conclude with `⟨f1.trans e1, f2.trans e2⟩`.
-/
theorem locWord : LocWord := by
  intro E _ _ _ n d hd a ha ls N hN
  have hP : ∀ w, w ∉ d.B → w ∉ d.P := fun w hw h => hw (by
    simp only [LocData.B, LocData.P, Finset.mem_union] at h ⊢
    tauto)
  have hprod : prodL d ls a = (d.fixL a).mul ((ls.map (locL d a ha)).foldr LM.mul (d.eL a)) := by
    rw [prodL, dif_pos ha]
    rfl
  refine ⟨fun p => ⟨?_, (unit_eqv d hd ha (hgL d hd ha p)).1, ?_⟩, fun w hw => ?_, fun w hw => ?_,
    fun w hw => atPlace_nil d hw ls⟩
  · have hOk := BlockFiniteConvolution.locOk₀ E n d hd a ha
    rcases kinds d ha p with h | h | ⟨L, hL, h⟩
    · rw [h]; exact hOk.2.1
    · exact hOk.2.2.2 _ h
    · rw [h]; exact ok_adj d (hOk.2.2.2 _ hL)
  · rcases kinds d ha p with h | h | ⟨L, hL, h⟩
    · exact Or.inr (Or.inr (Or.inl h))
    · exact Or.inl h
    · exact Or.inr (Or.inl ⟨L, hL, h⟩)
  · rw [hprod]
    have h1 := atW_mul d (atW_refl d w (d.fixL a)) (prodW d hd ha hw ls)
    rw [hN] at h1
    exact atW_tr d h1 d.one
  · have hwP := hP w hw
    have hBad : w ∉ d.Bad := fun h => hw (by simp [LocData.B, h])
    obtain ⟨e1, e2⟩ := offB d hd ha hwP ls
    have hs : (d.fixL a).s w = idem (d.lev a w) := by simp [LocData.fixL, hBad]
    obtain ⟨f1, f2⟩ := offStep d hd ha hwP (hg_foldr d hd ha ls) hs rfl
    rw [hprod]
    exact ⟨f1.trans e1, f2.trans e2⟩

end PositivityTheory.Rg.BcB.F.B3

end

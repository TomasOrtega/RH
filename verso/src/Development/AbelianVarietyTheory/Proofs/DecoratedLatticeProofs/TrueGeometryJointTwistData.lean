import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ColNone
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MemSupportedSubgroupOfSuppAtSplitPlaceMem
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.UnitaryFiniteAdelicGroupSplitFinitePlaceSet
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.AdForm GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Fam GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SplitWeil
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
attribute [local instance] GlobalTheory.Fam.GeoAll.fld GlobalTheory.Fam.GeoAll.val GlobalTheory.Fam.GeoAll.top GlobalTheory.Fam.GeoAll.loc

namespace GlobalTheory.QPl.EpsSupp

/- English proof (translation)
Introduce `n`. Proceed by induction on `n with`. Consider the case `zero`. Introduce `f g hg`. Simplify using `only [List.ofFn_zero, conv, List.foldr_nil] at hg`.

Use `Finsupp.support_single_subset hg` as an intermediate fact. Rewrite `this` using `[Finset.mem_singleton]`. Conclude with `⟨Fin.elim0, fun i => i.elim0, by simp [this]⟩`. Consider the case `succ n ih`. Introduce `f g hg`.

Rewrite `hg` using `[List.ofFn_succ]`. Simplify using `only [conv, List.foldr_cons] at hg`. Establish `h1` using `Finsupp.support_sum hg`. Rewrite `h1` using `[Finset.mem_biUnion]`. Take `⟨g₀, hg₀, h2⟩` from `h1`.

Establish `h3` using `Finsupp.support_sum h2`. Rewrite `h3` using `[Finset.mem_biUnion]`. Take `⟨g', hg', h4⟩` from `h3`. Establish `h5` using `Finsupp.support_single_subset h4`. Rewrite `h5` using `[Finset.mem_singleton]`.

Take `⟨x, hx, hxe⟩` from `ih (fun k => f k.succ) g' hg'`. Use `⟨Fin.cons g₀ x, fun i => Fin.cases hg₀ (fun k => hx k) i, ?_⟩` and prove the remaining obligations. Rewrite using `[List.ofFn_succ, List.prod_cons, h5, hxe]`. Simplify using the standard rewrite rules.
-/
theorem exists_prod_of_mem_support_conv {G : Type} [Monoid G] : ∀ (n : ℕ) (f : Fin n → (G →₀ ℂ)) (g : G),
    g ∈ (conv (List.ofFn f)).support → ∃ x : Fin n → G, (∀ i, x i ∈ (f i).support) ∧ g = (List.ofFn x).prod := by
  classical
  intro n
  induction n with
  | zero =>
    intro f g hg
    simp only [List.ofFn_zero, conv, List.foldr_nil] at hg
    have := Finsupp.support_single_subset hg
    rw [Finset.mem_singleton] at this
    exact ⟨Fin.elim0, fun i => i.elim0, by simp [this]⟩
  | succ n ih =>
    intro f g hg
    rw [List.ofFn_succ] at hg
    simp only [conv, List.foldr_cons] at hg
    have h1 := Finsupp.support_sum hg
    rw [Finset.mem_biUnion] at h1
    obtain ⟨g₀, hg₀, h2⟩ := h1
    have h3 := Finsupp.support_sum h2
    rw [Finset.mem_biUnion] at h3
    obtain ⟨g', hg', h4⟩ := h3
    have h5 := Finsupp.support_single_subset h4
    rw [Finset.mem_singleton] at h5
    obtain ⟨x, hx, hxe⟩ := ih (fun k => f k.succ) g' hg'
    refine ⟨Fin.cons g₀ x, fun i => Fin.cases hg₀ (fun k => hx k) i, ?_⟩
    rw [List.ofFn_succ, List.prod_cons, h5, hxe]
    simp

/- English proof (translation)
Introduce `g hg`. Simplify using `only [QFam.pinTup] at hg ⊢`. Use `split_ifs at hg with hc`. Establish `hg'` using `Finsupp.support_smul hg`. Take `⟨x, hx, rfl⟩` from `exists_prod_of_mem_support_conv _ _ g hg'`.

Apply `Subgroup.list_prod_mem` to reduce the goal to its premises. Introduce `y hy`. Take `⟨i, rfl⟩` from `List.mem_ofFn.1 hy`. Establish `hP : (F.Q i).q.v ∈ Finset.univ.image fun i => (F.Q i).q.v` using `Finset.mem_image_of_mem _ (Finset.mem_univ i)`. Break down `hc with ⟨ρ, hρ⟩ | hj` into its components or cases.

Take `⟨e, -, he⟩` from `(F.Q i).εL_at j ρ hρ (2 * ρ) (by have := (F.Q i).hs; omega) (F.eqv j α i)`. Establish `hxi` using `hx i`. Rewrite `hxi` using `[he]`. Take `⟨a, -, hax⟩` from `Finset.mem_image.1 (Finsupp.mapDomain_support hxi)`. Rewrite using `[← hax]`.

Conclude with `GlobalTheory.SuppGrp.mem_grpAt_of_suppAt D _ (F.Q i).q _ _ ((F.Q i).gl_loc _ _ _ a).1 _ hP`. Substitute `hj` using the available equality. Establish `hxi` using `hx i`. Rewrite `hxi` using `[h0]`. Establish `h1` using `Finsupp.support_single_subset hxi`.

Rewrite `h1` using `[Finset.mem_singleton]`. Rewrite using `[h1]`. Conclude with `one_mem _`. Simplify using `at hg`.
-/
theorem eps_mem_grpAt {D : D7} {c : Comm D} {v : VCom c} {t : Tup c} (F : QFam v t) (sc cT : ℕ → ℂ)
    (h0 : ∀ i β, (F.Q i).εL 0 β = Finsupp.single 1 1) (j : ℕ) (α : t.Ch j) :
    ∀ g ∈ ((F.pinTup sc cT).ε j α).support, g ∈ GlobalTheory.FinPl.grpAt (c.V j) (· ∈ (F.pinTup sc cT).Q) := by
  classical
  intro g hg
  dsimp only [QFam.pinTup] at hg ⊢
  split_ifs at hg with hc
  · have hg' := Finsupp.support_smul hg
    obtain ⟨x, hx, rfl⟩ := exists_prod_of_mem_support_conv _ _ g hg'
    apply Subgroup.list_prod_mem
    intro y hy
    obtain ⟨i, rfl⟩ := List.mem_ofFn.1 hy
    have hP : (F.Q i).q.v ∈ Finset.univ.image fun i => (F.Q i).q.v := Finset.mem_image_of_mem _ (Finset.mem_univ i)
    rcases hc with ⟨ρ, hρ⟩ | hj
    · obtain ⟨e, -, he⟩ := (F.Q i).εL_at j ρ hρ (2 * ρ) (by have := (F.Q i).hs; omega) (F.eqv j α i)
      have hxi := hx i
      rw [he] at hxi
      obtain ⟨a, -, hax⟩ := Finset.mem_image.1 (Finsupp.mapDomain_support hxi)
      rw [← hax]
      exact GlobalTheory.SuppGrp.mem_grpAt_of_suppAt D _ (F.Q i).q _ _ ((F.Q i).gl_loc _ _ _ a).1 _ hP
    · subst hj
      have hxi := hx i
      rw [h0] at hxi
      have h1 := Finsupp.support_single_subset hxi
      rw [Finset.mem_singleton] at h1
      rw [h1]
      exact one_mem _
  · simp at hg

end GlobalTheory.QPl.EpsSupp

open GlobalTheory.QPl.EpsSupp in

/- English proof (translation)
Introduce `B X I l Z L hT Gi Gl Kc Yd cX ex W _ u a ha _ J _ row col hCh sc cT t j α g hg`. Establish `h1` using `eps_mem_grpAt (famOf a J row col hCh t) sc cT (fun i β => ((J t).E i).εL_zero β) j α g hg`. Use `⟨h1, mul_mem (GlobalTheory.FinPl.SetCut.grpAt_le_GfC _ _ h1) ?_⟩` and prove the remaining obligations. Rewrite using `[← (ha.tie row col).1.b j]`. Conclude with `ha.vis.b j`.
-/
theorem GlobalTheory.Fam.famOf_eps_mem : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (I.rec7 l Z)} {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX} (W : RealPack ex), AllTrue W → ∀ (u : B.Word) (a : GeoAll W u), a.Is → a.True → ∀ (J : ∀ t, QJ a t), (∀ t, (J t).Reads) → ∀ (row : ∀ t, RowCh (pk W) (lvP W) u a.g t)
    (col : ∀ t : W.P.T, ColCh (D := I.rec7 l Z) u ((I.rec7 l Z).chTw u (W.P.I.tup t))) (hCh : ∀ t, (col t).Ch = (J t).Ch) (sc cT : ℕ → ℂ) t, ∀ j α, ∀ g ∈ (((famOf a J row col hCh t).pinTup sc cT).ε j α).support,
    g ∈ GlobalTheory.FinPl.grpAt (Yc (I.rec7 l Z) j) (· ∈ ((famOf a J row col hCh t).pinTup sc cT).Q) ∧ g * a.g.b j ∈ GfC (Yc (I.rec7 l Z) j) := by
  intro B X I l Z L hT Gi Gl Kc Yd cX ex W _ u a ha _ J _ row col hCh sc cT t j α g hg
  have h1 := eps_mem_grpAt (famOf a J row col hCh t) sc cT (fun i β => ((J t).E i).εL_zero β) j α g hg
  refine ⟨h1, mul_mem (GlobalTheory.FinPl.SetCut.grpAt_le_GfC _ _ h1) ?_⟩
  rw [← (ha.tie row col).1.b j]
  exact ha.vis.b j

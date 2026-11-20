import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LocK
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPlaceLocalGroupClosedEmbeddingIntegralStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.UnitaryFiniteAdelicGroupSplitFinitePlaceSetStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.QPl ValuativeRel
open GlobalTheory.PosOne (toOne Covers TriPos)
open GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage (app HasTensorVal fl opEFJ IsQuotIntFJ RFJ)
open GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum (IsCO)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.QSuppTwo

/- English proof (translation)
Introduce `n`. Proceed by induction on `n with`. Consider the case `zero => intro f i`. Conclude with `i.elim0`. Consider the case `succ n ih`.

Introduce `f i`. Use `Fin.cases ?_ (fun k => ?_) i` and prove the remaining obligations. Introduce `hf0 hc0`. Establish `hP : (List.ofFn fun k : Fin n => f k.succ).prod ∈ H`. Apply `Subgroup.list_prod_mem` to reduce the goal to its premises.

Introduce `x hx`. Take `⟨k, rfl⟩` from `List.mem_ofFn.1 hx`. Conclude with `hf0 _ (Fin.succ_ne_zero k)`. Rewrite using `[List.ofFn_succ, List.prod_cons, hc0 _ hP, mul_assoc, mul_inv_cancel, mul_one]`. Conclude with `hP`.

Introduce `hfk hck`. Rewrite using `[List.ofFn_succ, List.prod_cons, mul_assoc]`. Conclude with `mul_mem (hfk 0 (Fin.succ_ne_zero k).symm) (ih (fun k => f k.succ) k (fun k' hk' => hfk _ (fun e => hk' (Fin.succ_injective _ e))) hck)`.
-/
theorem prod_mul_inv_mem {G : Type} [Group G] (H : Subgroup G) : ∀ (n : ℕ) (f : Fin n → G) (i : Fin n),
    (∀ i', i' ≠ i → f i' ∈ H) → (∀ y ∈ H, f i * y = y * f i) → (List.ofFn f).prod * (f i)⁻¹ ∈ H := by
  intro n
  induction n with
  | zero => intro f i; exact i.elim0
  | succ n ih =>
    intro f i
    refine Fin.cases ?_ (fun k => ?_) i
    · intro hf0 hc0
      have hP : (List.ofFn fun k : Fin n => f k.succ).prod ∈ H := by
        apply Subgroup.list_prod_mem
        intro x hx
        obtain ⟨k, rfl⟩ := List.mem_ofFn.1 hx
        exact hf0 _ (Fin.succ_ne_zero k)
      rw [List.ofFn_succ, List.prod_cons, hc0 _ hP, mul_assoc, mul_inv_cancel, mul_one]
      exact hP
    · intro hfk hck
      rw [List.ofFn_succ, List.prod_cons, mul_assoc]
      exact mul_mem (hfk 0 (Fin.succ_ne_zero k).symm)
        (ih (fun k => f k.succ) k (fun k' hk' => hfk _ (fun e => hk' (Fin.succ_injective _ e))) hck)

/- English proof (translation)
Introduce `n`. Proceed by induction on `n with`. Consider the case `zero`. Introduce `f g hg`. Simplify using `only [List.ofFn_zero, conv, List.foldr_nil] at hg`.

Use `Finsupp.support_single_subset hg` as an intermediate fact. Rewrite `this` using `[Finset.mem_singleton]`. Conclude with `⟨Fin.elim0, fun i => i.elim0, by simp [this]⟩`. Consider the case `succ n ih`. Introduce `f g hg`.

Rewrite `hg` using `[List.ofFn_succ]`. Simplify using `only [conv, List.foldr_cons] at hg`. Establish `h1` using `Finsupp.support_sum hg`. Rewrite `h1` using `[Finset.mem_biUnion]`. Take `⟨g₀, hg₀, h2⟩` from `h1`.

Establish `h3` using `Finsupp.support_sum h2`. Rewrite `h3` using `[Finset.mem_biUnion]`. Take `⟨g', hg', h4⟩` from `h3`. Establish `h5` using `Finsupp.support_single_subset h4`. Rewrite `h5` using `[Finset.mem_singleton]`.

Take `⟨x, hx, hxe⟩` from `ih (fun k => f k.succ) g' hg'`. Use `⟨Fin.cons g₀ x, fun i => Fin.cases hg₀ (fun k => hx k) i, ?_⟩` and prove the remaining obligations. Rewrite using `[List.ofFn_succ, List.prod_cons, h5, hxe]`. Simplify using the standard rewrite rules.
-/
theorem mem_support_conv {G : Type} [Monoid G] : ∀ (n : ℕ) (f : Fin n → (G →₀ ℂ)) (g : G),
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

end GlobalTheory.QSuppTwo

open GlobalTheory.QSuppTwo in
/- English proof (translation)
Introduce `D c v t w F hF j σ h`. Establish `hd : ∀ i, j + (2 * σ + 2) = (F.Q i).s` using `fun i => by have := (F.Q i).hs; omega`. Use `choose e he using fun i (α' : (F.Q i).Ch j) => (F.Q i).εL_at j (σ + 1) h (2 * σ + 2) (hd i) α'`. Use `⟨fun i => Finset.univ.biUnion fun α' => (e i α').support, ?_⟩` and prove the remaining obligations. Introduce `α g hg`.

Rewrite `hg` using `[hF.ε j (σ + 1) h α]`. Establish `hg'` using `Finsupp.support_smul hg`. Take `⟨x, hx, rfl⟩` from `mem_support_conv _ _ g hg'`. Establish `hpt : ∀ i, ∃ a ∈ (e i (F.eqv j α i)).support, (F.Q i).gl j (2 * σ + 2 + 1) (by have` using `(F.Q i).hs; omega) a = x i := by`. Introduce `i`.

Use `hx i` as an intermediate fact. Rewrite `this` using `[(he i (F.eqv j α i)).2]`. Use `Finsupp.mapDomain_support this` as an intermediate fact. Rewrite `this` using `[Finset.mem_image]`. Conclude with `this`.

Use `choose a ha hax using hpt`. Use `⟨a, fun i => ⟨Finset.mem_biUnion.2 ⟨F.eqv j α i, Finset.mem_univ _, ha i⟩, ?_⟩⟩` and prove the remaining obligations. Establish `I` using `fun i => GlobalTheory.T.splitPlace_local_group_closedEmbedding_integral D (F.Q i).k (F.Q i).q (c.V j) _ ((F.Q i).FY j (2 * σ + 2 + 1) (by have := (F.Q i).hs; omega)) ((F.Q i).gl j (2 * σ + 2 + 1) (by have := (F.Q i).hs; omega)) ((F.Q i).gl_loc j _ _)`. Rewrite using `[hax i]`. Apply `prod_mul_inv_mem _ _ x i` to reduce the goal to its premises.

Introduce `i' hi'`. Rewrite using `[← hax i']`. Establish `hr : (F.Q i').gl j (2 * σ + 2 + 1) (by have` using `(F.Q i').hs; omega) (a i') ∈ GlobalTheory.FinPl.grpAt (c.V j) (· = (F.Q i').q.v) := by`. Rewrite using `[← (I i').2.1]`. Conclude with `⟨_, rfl⟩`.

Conclude with `(GlobalTheory.T.unitaryFiniteAdelicGroup_split_finitePlaceSet D (c.V j) ∅).2.2.2.2.2.2.1 _ _ (fun p hp hn => hi' (hF.inj (hp.symm.trans hn))) hr`. Introduce `y hy`. Rewrite using `[← hax i]`. Conclude with `(I i).2.2.2.1 (a i) y hy`.
-/
theorem GlobalTheory.QSuppTwo.main : ∀ (D : D7) (c : Comm D) (v : VCom c) (t : Tup c) (w : VTup t) (F : QFam v t), F.Pins w → ∀ j σ (h : j + 2 * (σ + 1) + 2 = D.R.m), ∃ A : ∀ i, Finset (GL ((F.Q i).X j ⊕ Fin (2 * σ + 2 + 1)) (F.Q i).k), ∀ α, ∀ g ∈ (w.ε j α).support, ∃ a : ∀ i, GL ((F.Q i).X j ⊕ Fin (2 * σ + 2 + 1)) (F.Q i).k, ∀ i, a i ∈ A i ∧ g * ((F.Q i).gl j (2 * σ + 2 + 1) (by have := (F.Q i).hs; omega) (a i))⁻¹ ∈ GlobalTheory.FinPl.grpOff (c.V j) (· = (F.Q i).q.v) := by
  classical
  intro D c v t w F hF j σ h
  have hd : ∀ i, j + (2 * σ + 2) = (F.Q i).s := fun i => by have := (F.Q i).hs; omega
  choose e he using fun i (α' : (F.Q i).Ch j) => (F.Q i).εL_at j (σ + 1) h (2 * σ + 2) (hd i) α'
  refine ⟨fun i => Finset.univ.biUnion fun α' => (e i α').support, ?_⟩
  intro α g hg
  rw [hF.ε j (σ + 1) h α] at hg
  have hg' := Finsupp.support_smul hg
  obtain ⟨x, hx, rfl⟩ := mem_support_conv _ _ g hg'
  have hpt : ∀ i, ∃ a ∈ (e i (F.eqv j α i)).support,
      (F.Q i).gl j (2 * σ + 2 + 1) (by have := (F.Q i).hs; omega) a = x i := by
    intro i
    have := hx i
    rw [(he i (F.eqv j α i)).2] at this
    have := Finsupp.mapDomain_support this
    rw [Finset.mem_image] at this
    exact this
  choose a ha hax using hpt
  refine ⟨a, fun i => ⟨Finset.mem_biUnion.2 ⟨F.eqv j α i, Finset.mem_univ _, ha i⟩, ?_⟩⟩
  have I := fun i => GlobalTheory.T.splitPlace_local_group_closedEmbedding_integral D (F.Q i).k (F.Q i).q (c.V j) _ ((F.Q i).FY j (2 * σ + 2 + 1) (by have := (F.Q i).hs; omega))
    ((F.Q i).gl j (2 * σ + 2 + 1) (by have := (F.Q i).hs; omega)) ((F.Q i).gl_loc j _ _)
  rw [hax i]
  apply prod_mul_inv_mem _ _ x i
  · intro i' hi'
    rw [← hax i']
    have hr : (F.Q i').gl j (2 * σ + 2 + 1) (by have := (F.Q i').hs; omega) (a i') ∈ GlobalTheory.FinPl.grpAt (c.V j) (· = (F.Q i').q.v) := by
      rw [← (I i').2.1]; exact ⟨_, rfl⟩
    exact (GlobalTheory.T.unitaryFiniteAdelicGroup_split_finitePlaceSet D (c.V j) ∅).2.2.2.2.2.2.1 _ _ (fun p hp hn => hi' (hF.inj (hp.symm.trans hn))) hr
  · intro y hy
    rw [← hax i]
    exact (I i).2.2.2.1 (a i) y hy

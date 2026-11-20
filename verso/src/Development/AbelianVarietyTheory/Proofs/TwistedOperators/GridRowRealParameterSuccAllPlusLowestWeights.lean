import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.NodeYPredEqChainVertexAtRowZeroLast
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LastStepParametersPartitionExtendedByZeros
import Development.AbelianVarietyTheory.Definitions.Divisors.LeastSplitAuxiliaryPrimeThetaChainSpec
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.S Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum GlobalTheory.Chain GlobalTheory.CompactHowe Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.ColParam

open GlobalTheory.Grid Finset

section GridFacts

variable (D : D7) (τ : D.what₂.Tau)

local notation "Γ" => grid D τ

/- English proof (translation)
Take `⟨l, rfl⟩ : ∃ l', l = l' + 1` from `⟨l - 1, by omega⟩`. Conclude with `GlobalTheory.SignedHC.GridData.extend_cast 1 (D.hc τ).e_int ⟨l, by omega⟩`.
-/
theorem e_eq {l : ℕ} (h1 : 1 ≤ l) (h2 : l ≤ D.R.m) : (((Γ).e l : ℤ) : ℚ) = (D.hc τ).e ⟨l - 1, by omega⟩ := by
  obtain ⟨l, rfl⟩ : ∃ l', l = l' + 1 := ⟨l - 1, by omega⟩
  exact GlobalTheory.SignedHC.GridData.extend_cast 1 (D.hc τ).e_int ⟨l, by omega⟩

/- English proof (translation)
Take `⟨l, rfl⟩ : ∃ l', l = l' + 1` from `⟨l - 1, by omega⟩`. Conclude with `GlobalTheory.SignedHC.GridData.extend_cast 1 (D.hc τ).b_int ⟨l, by omega⟩`.
-/
theorem b_eq {l : ℕ} (h1 : 1 ≤ l) (h2 : l ≤ D.R.m) : (((Γ).b l : ℤ) : ℚ) = (D.hc τ).b ⟨l - 1, by omega⟩ := by
  obtain ⟨l, rfl⟩ : ∃ l', l = l' + 1 := ⟨l - 1, by omega⟩
  exact GlobalTheory.SignedHC.GridData.extend_cast 1 (D.hc τ).b_int ⟨l, by omega⟩

/- English proof (translation)
Take `⟨i, rfl⟩ : ∃ i', i = i' + 2` from `⟨i - 2, by omega⟩`. Conclude with `GlobalTheory.SignedHC.GridData.extend_cast 2 (D.hc τ).v_int ⟨i, by omega⟩`.
-/
theorem v_eq {i : ℕ} (h1 : 2 ≤ i) (h2 : i ≤ D.R.k) : (((Γ).v i : ℤ) : ℚ) = (D.hc τ).v ⟨i - 2, by omega⟩ := by
  obtain ⟨i, rfl⟩ : ∃ i', i = i' + 2 := ⟨i - 2, by omega⟩
  exact GlobalTheory.SignedHC.GridData.extend_cast 2 (D.hc τ).v_int ⟨i, by omega⟩

/- English proof (translation)
Rewrite using `[e_eq D τ h1 h2, b_eq D τ h1 h2]`. Conclude with `(D.hc τ).gap_be _`.
-/
theorem be {l : ℕ} (h1 : 1 ≤ l) (h2 : l ≤ D.R.m) : ((D.R.t : ℚ) + 3) / 2 ≤ ((Γ).e l : ℚ) - (Γ).b l := by
  rw [e_eq D τ h1 h2, b_eq D τ h1 h2]
  exact (D.hc τ).gap_be _

/- English proof (translation)
Rewrite using `[e_eq D τ h1 (by omega), b_eq D τ (by omega) h2]`. Take `⟨l, rfl⟩ : ∃ l', l = l' + 1` from `⟨l - 1, by omega⟩`. Conclude with `(D.hc τ).gap_eb ⟨l, by omega⟩ (by simpa using (by omega : l + 1 < D.R.m))`.
-/
theorem eb {l : ℕ} (h1 : 1 ≤ l) (h2 : l + 1 ≤ D.R.m) : ((D.R.t : ℚ) + 3) / 2 ≤ ((Γ).b (l + 1) : ℚ) - (Γ).e l := by
  rw [e_eq D τ h1 (by omega), b_eq D τ (by omega) h2]
  obtain ⟨l, rfl⟩ : ∃ l', l = l' + 1 := ⟨l - 1, by omega⟩
  exact (D.hc τ).gap_eb ⟨l, by omega⟩ (by simpa using (by omega : l + 1 < D.R.m))

/- English proof (translation)
Proceed by induction on `l', h using Nat.le_induction with`. Consider the case `base`. Combine the linear relations using `[be D τ (l := l + 1) (by omega) h2, eb D τ h1 h2]`. Consider the case `succ n hn ih`. Use `ih (by omega)` as an intermediate fact.

Establish `e1` using `be D τ (l := n + 1) (by omega) h2`. Establish `e2` using `eb D τ (l := n) (by omega) h2`. Establish `: (0 : ℚ) ≤ D.R.t` using `by positivity`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem e_lt {l l' : ℕ} (h1 : 1 ≤ l) (h : l < l') (h2 : l' ≤ D.R.m) : (D.R.t : ℚ) + 3 + (Γ).e l ≤ (Γ).e l' := by
  induction l', h using Nat.le_induction with
  | base =>
    linarith [be D τ (l := l + 1) (by omega) h2, eb D τ h1 h2]
  | succ n hn ih =>
    have := ih (by omega)
    have e1 := be D τ (l := n + 1) (by omega) h2
    have e2 := eb D τ (l := n) (by omega) h2
    have : (0 : ℚ) ≤ D.R.t := by positivity
    linarith

/- English proof (translation)
Establish `hm : 1 ≤ D.R.m` using `by have := D.R.two_le_m; omega`. Establish `hk : 2 ≤ D.R.k` using `by have := D.R.m_add_three_le_k; omega`. Establish `base : -((Γ).b 1 : ℚ) < (Γ).v D.R.k`. Rewrite using `[v_eq D τ hk le_rfl, b_eq D τ le_rfl hm]`. Establish `e1` using `(D.hc τ).u_last_gt (by omega) (by omega)`.

Establish `e2` using `(D.hc τ).v_gt_u ⟨D.R.k - 2, by omega⟩`. Establish `e3 : (⟨D.R.k - 2 + 1, by omega⟩ : Fin D.R.k) = ⟨D.R.k - 1, by omega⟩` using `Fin.ext (by simp only; omega)`. Simplify using `only [e3] at e2`. Conclude with `e1.trans e2`. Establish `base' : -((Γ).b 1) < (Γ).v D.R.k` using `by exact_mod_cast base`.

Establish `step : (Γ).v D.R.k ≤ (Γ).v i`. Break down `h2.eq_or_lt with rfl | h` into its components or cases. Conclude with `le_rfl`. Conclude with `((Γ).v_anti i D.R.k h1 h le_rfl).le`. Establish `: -((Γ).b 1) + 1 ≤ (Γ).v i` using `by omega`.

Conclude with `this` after adjusting the coercions.
-/
theorem cloud_ge {i : ℕ} (h1 : 2 ≤ i) (h2 : i ≤ D.R.k) : -((Γ).b 1 : ℚ) + 1 ≤ (Γ).v i := by
  have hm : 1 ≤ D.R.m := by have := D.R.two_le_m; omega
  have hk : 2 ≤ D.R.k := by have := D.R.m_add_three_le_k; omega
  have base : -((Γ).b 1 : ℚ) < (Γ).v D.R.k := by
    rw [v_eq D τ hk le_rfl, b_eq D τ le_rfl hm]
    have e1 := (D.hc τ).u_last_gt (by omega) (by omega)
    have e2 := (D.hc τ).v_gt_u ⟨D.R.k - 2, by omega⟩
    have e3 : (⟨D.R.k - 2 + 1, by omega⟩ : Fin D.R.k) = ⟨D.R.k - 1, by omega⟩ := Fin.ext (by simp only; omega)
    simp only [e3] at e2
    exact e1.trans e2
  have base' : -((Γ).b 1) < (Γ).v D.R.k := by exact_mod_cast base
  have step : (Γ).v D.R.k ≤ (Γ).v i := by
    rcases h2.eq_or_lt with rfl | h
    · exact le_rfl
    · exact ((Γ).v_anti i D.R.k h1 h le_rfl).le
  have : -((Γ).b 1) + 1 ≤ (Γ).v i := by omega
  exact_mod_cast this

/- English proof (translation)
Break down `h.eq_or_lt with rfl | h` into its components or cases. Conclude with `le_rfl`. Establish `: (0 : ℚ) ≤ (Γ).ga` using `by positivity`. Combine the linear relations using `[GlobalTheory.ChiGrid.a_add_le (G := Γ) h]`.
-/
theorem a_le {i j : ℕ} (h : i ≤ j) : (Γ).a j ≤ (Γ).a i := by
  rcases h.eq_or_lt with rfl | h
  · exact le_rfl
  · have : (0 : ℚ) ≤ (Γ).ga := by positivity
    linarith [GlobalTheory.ChiGrid.a_add_le (G := Γ) h]

/- English proof (translation)
Use `abs_le.1 (GlobalTheory.SignedHC.abs_sub_le_of_mem_block h)` as an intermediate fact. Establish `e : (((Γ).t + 1 : ℕ) : ℚ) = D.R.t + 1` using `by push_cast; rfl`. Rewrite `this` using `[e]`. Apply the tactic sequence `constructor <;> linarith [this.1, this.2]`.
-/
theorem blockMPlus_bd {l : ℕ} {x : ℚ} (h : x ∈ (Γ).blockMPlus l) :
    -((Γ).e l : ℚ) - (D.R.t : ℚ) / 2 ≤ x ∧ x ≤ -((Γ).e l : ℚ) + (D.R.t : ℚ) / 2 := by
  have := abs_le.1 (GlobalTheory.SignedHC.abs_sub_le_of_mem_block h)
  have e : (((Γ).t + 1 : ℕ) : ℚ) = D.R.t + 1 := by push_cast; rfl
  rw [e] at this
  constructor <;> linarith [this.1, this.2]

/- English proof (translation)
Use `(isLeast_gap D).1.2.1` as an intermediate fact. Use `show sLen D < gap D`. Use linear arithmetic over natural numbers and integers.
-/
theorem s_lt_gap : (Γ).s < (Γ).ga := by
  have := (isLeast_gap D).1.2.1
  show sLen D < gap D
  omega

/- English proof (translation)
The claim follows from `GlobalTheory.ChiGrid.odd_sLen D`.
-/
theorem gridDataAtRealPlace_s_odd : Odd (Γ).s := GlobalTheory.ChiGrid.odd_sLen D

/- English proof (translation)
Establish `hm : 1 ≤ D.R.m` using `by omega`. Establish `hk : 2 ≤ D.R.k` using `by have := D.R.m_add_three_le_k; omega`. Establish `ht : (0 : ℚ) ≤ D.R.t` using `by positivity`. Establish `hg : (0 : ℚ) ≤ (Γ).ga` using `by positivity`. Take `⟨y1, y2⟩` from `blockMPlus_bd D τ hy`.

Establish `hbe` using `be D τ (l := 1) le_rfl hm`. Establish `he1 : ((Γ).e 1 : ℚ) ≤ (Γ).e (j + 1)`. Break down `Nat.eq_zero_or_pos j with rfl | h` into its components or cases. Conclude with `le_rfl`. Combine the linear relations using `[e_lt D τ (l := 1) (l' := j + 1) le_rfl (by omega) hj]`.

Establish `hlow : y < -((Γ).b 1 : ℚ)` using `by linarith`. Establish `hc2` using `cloud_ge D τ (i := 2) le_rfl hk`. Establish `ham : (Γ).a (Γ).m = (Γ).v 2 + (Γ).ga + 1 / 2` using `(Γ).a_m`. Break down `GlobalTheory.SignedHC.GridData.mem_weightX.1 hx with h | h | ⟨i, h1, h2, h⟩ | ⟨l, h1, h2, h⟩` into its components or cases. Take `⟨i, hi, rfl⟩` from `GlobalTheory.SignedHC.GridData.mem_tops.1 h`.

Combine the linear relations using `[a_le D τ hi]`. Take `⟨i, h1, h2, rfl⟩` from `GlobalTheory.SignedHC.GridData.mem_cloudHalf.1 h`. Use `cloud_ge D τ h1 h2` as an intermediate fact. Simplify using `only [GlobalTheory.SignedHC.GridData.vHalf]`. Combine the linear equalities and inequalities to obtain the conclusion.

Use `(GlobalTheory.ChiGrid.blockC'_between (grid_nearMid D τ) (gridDataAtRealPlace_s_odd D τ).pos (s_lt_gap D τ) h1 h2 h).1` as an intermediate fact. Combine the linear relations using `[a_le D τ h2]`. Use `e_lt D τ h1 (by omega : l < j + 1) hj` as an intermediate fact. Use `(blockMPlus_bd D τ h).1` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem weightX_above {j : ℕ} (hj : j + 1 ≤ D.R.m) {x y : ℚ} (hx : x ∈ (Γ).weightX j)
    (hy : y ∈ (Γ).blockMPlus (j + 1)) : y < x := by
  have hm : 1 ≤ D.R.m := by omega
  have hk : 2 ≤ D.R.k := by have := D.R.m_add_three_le_k; omega
  have ht : (0 : ℚ) ≤ D.R.t := by positivity
  have hg : (0 : ℚ) ≤ (Γ).ga := by positivity
  obtain ⟨y1, y2⟩ := blockMPlus_bd D τ hy
  have hbe := be D τ (l := 1) le_rfl hm
  have he1 : ((Γ).e 1 : ℚ) ≤ (Γ).e (j + 1) := by
    rcases Nat.eq_zero_or_pos j with rfl | h
    · exact le_rfl
    · linarith [e_lt D τ (l := 1) (l' := j + 1) le_rfl (by omega) hj]
  have hlow : y < -((Γ).b 1 : ℚ) := by linarith
  have hc2 := cloud_ge D τ (i := 2) le_rfl hk
  have ham : (Γ).a (Γ).m = (Γ).v 2 + (Γ).ga + 1 / 2 := (Γ).a_m
  rcases GlobalTheory.SignedHC.GridData.mem_weightX.1 hx with h | h | ⟨i, h1, h2, h⟩ | ⟨l, h1, h2, h⟩
  · obtain ⟨i, hi, rfl⟩ := GlobalTheory.SignedHC.GridData.mem_tops.1 h
    linarith [a_le D τ hi]
  · obtain ⟨i, h1, h2, rfl⟩ := GlobalTheory.SignedHC.GridData.mem_cloudHalf.1 h
    have := cloud_ge D τ h1 h2
    simp only [GlobalTheory.SignedHC.GridData.vHalf]
    linarith
  · have := (GlobalTheory.ChiGrid.blockC'_between (grid_nearMid D τ) (gridDataAtRealPlace_s_odd D τ).pos (s_lt_gap D τ) h1 h2 h).1
    linarith [a_le D τ h2]
  · have := e_lt D τ h1 (by omega : l < j + 1) hj
    have := (blockMPlus_bd D τ h).1
    linarith

/- English proof (translation)
Proceed by induction on `j with`. Consider the case `zero => exact GlobalTheory.ChiGrid.inCoset_weightX_zero (gridDataAtRealPlace_s_odd D τ)`. Consider the case `succ j ih`. Rewrite using `[(Γ).weightX_succ]`. Introduce `x hx`.

Break down `mem_union.1 hx with h | h` into its components or cases. Conclude with `ih x h`. Take `⟨a, -, rfl⟩` from `GlobalTheory.SignedHC.mem_block.1 h`. Take `⟨u, hu⟩` from `D.R.t_odd`. Establish `e : ((Γ).t : ℚ) = 2 * u + 1`.

Establish `: ((Γ).t : ℚ) = D.R.t` using `rfl`. Rewrite using `[this, hu]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Use `⟨-(Γ).e (j + 1) + u - a, ?_⟩` and prove the remaining obligations.

Use `push_cast`. Rewrite using `[e]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem inCoset_weightX (j : ℕ) : GlobalTheory.SignedHC.InCoset (1 / 2) ((Γ).weightX j) := by
  induction j with
  | zero => exact GlobalTheory.ChiGrid.inCoset_weightX_zero (gridDataAtRealPlace_s_odd D τ)
  | succ j ih =>
    rw [(Γ).weightX_succ]
    intro x hx
    rcases mem_union.1 hx with h | h
    · exact ih x h
    · obtain ⟨a, -, rfl⟩ := GlobalTheory.SignedHC.mem_block.1 h
      obtain ⟨u, hu⟩ := D.R.t_odd
      have e : ((Γ).t : ℚ) = 2 * u + 1 := by
        have : ((Γ).t : ℚ) = D.R.t := rfl
        rw [this, hu]; push_cast; ring
      refine ⟨-(Γ).e (j + 1) + u - a, ?_⟩
      push_cast
      rw [e]
      ring

/- English proof (translation)
Proceed by induction on `j with`. Consider the case `zero`. Rewrite using `[GlobalTheory.ChiGrid.card_weightX_zero (grid_nearMid D τ) (gridDataAtRealPlace_s_odd D τ).pos (s_lt_gap D τ)]`. Simplify using `[GlobalTheory.ChiGrid.rankX]`. Both sides reduce to the same expression.

Consider the case `succ j ih`. Rewrite using `[(Γ).weightX_succ, card_union_of_disjoint (disjoint_left.2 fun x hx hy => (weightX_above D τ hj hx hy).ne rfl), ih (by omega)]`. Establish `: ((Γ).blockMPlus (j + 1)).card = D.R.t + 1` using `GlobalTheory.SignedHC.card_block _ _`. Rewrite using `[this]`. Simplify using `only [GlobalTheory.ChiGrid.rankX]`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem card_weightX {j : ℕ} (hj : j ≤ D.R.m) : ((Γ).weightX j).card = GlobalTheory.ChiGrid.rankX D j := by
  induction j with
  | zero =>
    rw [GlobalTheory.ChiGrid.card_weightX_zero (grid_nearMid D τ) (gridDataAtRealPlace_s_odd D τ).pos (s_lt_gap D τ)]
    simp [GlobalTheory.ChiGrid.rankX]; rfl
  | succ j ih =>
    rw [(Γ).weightX_succ, card_union_of_disjoint
      (disjoint_left.2 fun x hx hy => (weightX_above D τ hj hx hy).ne rfl), ih (by omega)]
    have : ((Γ).blockMPlus (j + 1)).card = D.R.t + 1 := GlobalTheory.SignedHC.card_block _ _
    rw [this]
    simp only [GlobalTheory.ChiGrid.rankX]
    ring

end GridFacts

/- English proof (translation)
Take `⟨hl, q, hq, hS⟩` from `h`. Establish `hmem : ∀ a, q a ∈ E ∧ ε a = true` using `fun a => by`. Establish `: (q a, ε a) ∈ GlobalTheory.SignedHC.plus E` using `by rw [hS]; exact mem_image_of_mem _ (mem_univ a)`. Conclude with `GlobalTheory.SignedHC.mem_plus.1 this`. Establish `hinj : Function.Injective fun a => (q a, ε a)`.

Introduce `a b hab`. Establish `h1 : q a = q b` using `congrArg Prod.fst hab`. Apply `hl.injective` to reduce the goal to its premises. Rewrite using `[hq, hq, h1]`. Use `⟨funext fun a => by rw [(hmem a).2]; rfl, ?_, ?_⟩` and prove the remaining obligations.

Establish `h1 : (GlobalTheory.SignedHC.plus E).card = E.card` using `card_image_of_injective _ (fun x y h => congrArg Prod.fst h)`. Rewrite using `[← h1, hS, card_image_of_injective _ hinj, card_univ, Fintype.card_fin]`. Introduce `x`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨a, rfl⟩`.

Conclude with `⟨q a, (hmem a).1, hq a⟩`. Introduce and unpack `⟨y, hy, rfl⟩`. Establish `: (y, true) ∈ GlobalTheory.SignedHC.plus E` using `GlobalTheory.SignedHC.mem_plus.2 ⟨hy, rfl⟩`. Rewrite `this` using `[hS]`. Take `⟨a, -, ha⟩` from `mem_image.1 this`.

Conclude with `⟨a, by rw [hq]; congr 1; exact congrArg Prod.fst ha⟩`.
-/
theorem enum_plus {n : ℕ} {E : Finset ℚ} {lam : Fin n → ℝ} {ε : Fin n → Bool}
    (h : Formalism.L2.Theta.IsEnum (GlobalTheory.SignedHC.plus E) lam ε) :
    ε = Formalism.MainNotions.S.allPos n ∧ E.card = n ∧ ∀ x : ℝ, x ∈ Set.range lam ↔ ∃ y ∈ E, x = (y : ℝ) := by
  obtain ⟨hl, q, hq, hS⟩ := h
  have hmem : ∀ a, q a ∈ E ∧ ε a = true := fun a => by
    have : (q a, ε a) ∈ GlobalTheory.SignedHC.plus E := by rw [hS]; exact mem_image_of_mem _ (mem_univ a)
    exact GlobalTheory.SignedHC.mem_plus.1 this
  have hinj : Function.Injective fun a => (q a, ε a) := by
    intro a b hab
    have h1 : q a = q b := congrArg Prod.fst hab
    apply hl.injective
    rw [hq, hq, h1]
  refine ⟨funext fun a => by rw [(hmem a).2]; rfl, ?_, ?_⟩
  · have h1 : (GlobalTheory.SignedHC.plus E).card = E.card :=
      card_image_of_injective _ (fun x y h => congrArg Prod.fst h)
    rw [← h1, hS, card_image_of_injective _ hinj, card_univ, Fintype.card_fin]
  · intro x
    constructor
    · rintro ⟨a, rfl⟩; exact ⟨q a, (hmem a).1, hq a⟩
    · rintro ⟨y, hy, rfl⟩
      have : (y, true) ∈ GlobalTheory.SignedHC.plus E := GlobalTheory.SignedHC.mem_plus.2 ⟨hy, rfl⟩
      rw [hS] at this
      obtain ⟨a, -, ha⟩ := mem_image.1 this
      exact ⟨a, by rw [hq]; congr 1; exact congrArg Prod.fst ha⟩

/- English proof (translation)
Set `L : Fin (n + T) → ℝ` to `fun b => if h : (b : ℕ) < n then lam ⟨b, h⟩ else c - (((b : ℕ) - n : ℕ) : ℝ)`. Establish `hL : StrictAnti L`. Introduce `a b hab`. Establish `hab' : (a : ℕ) < b` using `hab`. Simplify using `only [L]`.

Use `split_ifs with h1 h2 h2`. Conclude with `hl (Fin.mk_lt_mk.2 hab')`. Use linear arithmetic over natural numbers and integers. Use `hb ⟨a, h2⟩` as an intermediate fact. Establish `: (0 : ℝ) ≤ (((b : ℕ) - n : ℕ) : ℝ)` using `Nat.cast_nonneg _`.

Combine the linear equalities and inequalities to obtain the conclusion. Establish `: (((a : ℕ) - n : ℕ) : ℝ) < (((b : ℕ) - n : ℕ) : ℝ)` using `by exact_mod_cast (by omega : (a : ℕ) - n < b - n)`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `key : lam' = L`. Rewrite using `[← StrictAnti.range_inj h' hL]`.

Use extensionality with `x`. Rewrite using `[hr]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `(⟨a, rfl⟩ | ⟨d, hd, rfl⟩)`. Use `⟨⟨a, by omega⟩, ?_⟩` and prove the remaining obligations.

Simplify using `[L]`. Use `⟨⟨n + d, by omega⟩, ?_⟩` and prove the remaining obligations. Simplify using `[L]`. Introduce and unpack `⟨b, rfl⟩`. Distinguish the cases in `hb' : (b : ℕ) < n`.

Conclude with `.inl ⟨⟨b, hb'⟩, by simp [L, hb']⟩`. Conclude with `.inr ⟨(b : ℕ) - n, by omega, by simp [L, hb']⟩`. Rewrite using `[key]`.
-/
theorem shape_below {n T : ℕ} (c : ℝ) (lam : Fin n → ℝ) (hl : StrictAnti lam) (hb : ∀ a, c < lam a)
    (lam' : Fin (n + T) → ℝ) (h' : StrictAnti lam')
    (hr : ∀ x : ℝ, x ∈ Set.range lam' ↔ x ∈ Set.range lam ∨ ∃ d : ℕ, d < T ∧ x = c - d) (b : Fin (n + T)) :
    lam' b = if h : (b : ℕ) < n then lam ⟨b, h⟩ else c - (((b : ℕ) - n : ℕ) : ℝ) := by
  let L : Fin (n + T) → ℝ := fun b => if h : (b : ℕ) < n then lam ⟨b, h⟩ else c - (((b : ℕ) - n : ℕ) : ℝ)
  have hL : StrictAnti L := by
    intro a b hab
    have hab' : (a : ℕ) < b := hab
    simp only [L]
    split_ifs with h1 h2 h2
    · exact hl (Fin.mk_lt_mk.2 hab')
    · omega
    · have := hb ⟨a, h2⟩
      have : (0 : ℝ) ≤ (((b : ℕ) - n : ℕ) : ℝ) := Nat.cast_nonneg _
      linarith
    · have : (((a : ℕ) - n : ℕ) : ℝ) < (((b : ℕ) - n : ℕ) : ℝ) := by exact_mod_cast (by omega : (a : ℕ) - n < b - n)
      linarith
  have key : lam' = L := by
    rw [← StrictAnti.range_inj h' hL]
    ext x
    rw [hr]
    constructor
    · rintro (⟨a, rfl⟩ | ⟨d, hd, rfl⟩)
      · refine ⟨⟨a, by omega⟩, ?_⟩
        simp [L]
      · refine ⟨⟨n + d, by omega⟩, ?_⟩
        simp [L]
    · rintro ⟨b, rfl⟩
      by_cases hb' : (b : ℕ) < n
      · exact .inl ⟨⟨b, hb'⟩, by simp [L, hb']⟩
      · exact .inr ⟨(b : ℕ) - n, by omega, by simp [L, hb']⟩
  rw [key]

/- English proof (translation)
Introduce `D j hj τ n N lam ε lam' ε' hE hE'`. Establish `hj' : j + 1 ≤ D.R.m` using `hj`. Take `⟨s, hs⟩` from `D.R.t_odd`. Establish `htR : (D.R.t : ℝ) = 2 * s + 1` using `by rw [hs]; push_cast; ring`. Establish `htQ : (D.R.t : ℚ) = 2 * s + 1` using `by rw [hs]; push_cast; ring`.

Use `set e : ℤ := (grid D τ).e (j + 1) with he_def`. Establish `hce : (e : ℚ) = (D.hc τ).e ⟨j, hj⟩`. Use `e_eq D τ (l := j + 1) (by omega) hj'` as an intermediate fact. Simplify using `only [Nat.add_sub_cancel] at this`. Conclude with `this`.

Establish `hB : (grid D τ).blockMPlus (j + 1) = TPar.block (-(e : ℚ)) (D.R.t + 1)` using `rfl`. Establish `hX : parXp D j τ = GlobalTheory.SignedHC.plus ((grid D τ).weightX j)` using `rfl`. Establish `hX' : parXp D (j + 1) τ = GlobalTheory.SignedHC.plus ((grid D τ).weightX j ∪ TPar.block (-(e : ℚ)) (D.R.t + 1))` using `by show GlobalTheory.SignedHC.plus ((grid D τ).weightX (j + 1)) = _`. Rewrite using `[(grid D τ).weightX_succ, hB]`. Rewrite `hE` using `[hX]`.

Rewrite `hE'` using `[hX']`. Take `⟨hε, hcard, hr⟩` from `enum_plus hE`. Take `⟨hε', hcard', hr'⟩` from `enum_plus hE'`. Establish `htop : -(e : ℚ) + (D.R.t : ℚ) / 2 ∈ (grid D τ).blockMPlus (j + 1)`. Rewrite using `[hB]; exact GlobalTheory.SignedHC.mem_block.2 ⟨0, by omega, by push_cast; ring⟩`.

Establish `habove : ∀ x ∈ (grid D τ).weightX j, -(e : ℚ) + (D.R.t : ℚ) / 2 + 1 ≤ x`. Introduce `x hx`. Establish `hlt` using `weightX_above D τ hj' hx htop`. Take `⟨z, hz⟩` from `inCoset_weightX D τ j x hx`. Rewrite `hlt`, the goal using `[hz, htQ]`.

Establish `: ((-e + s : ℤ) : ℚ) < z` using `by push_cast; linarith`. Establish `h2 : -e + s < z` using `by exact_mod_cast this`. Establish `h3 : ((-e + s + 1 : ℤ) : ℚ) ≤ z` using `by exact_mod_cast Int.add_one_le_iff.2 h2`. Move the coercions through the operations in `at h3`. Combine the linear equalities and inequalities to obtain the conclusion.

Establish `hdisj : Disjoint ((grid D τ).weightX j) (TPar.block (-(e : ℚ)) (D.R.t + 1))` using `disjoint_left.2 fun x hx hy => (weightX_above D τ hj' hx (by rw [hB]; exact hy)).ne rfl`. Establish `hN : N = n + (D.R.t + 1)`. Rewrite using `[← hcard', card_union_of_disjoint hdisj, hcard, GlobalTheory.SignedHC.card_block]`. Establish `hne : Even n`. Rewrite using `[← hcard, card_weightX D τ (by omega)]; exact GlobalTheory.ChiGrid.even_rankX D j`.

Substitute `hN` using the available equality. Use `⟨hε, hε', ?_⟩` and prove the remaining obligations. Take `⟨p, hp⟩` from `hne`. Establish `hpR : (n : ℝ) = 2 * p` using `by rw [hp]; push_cast; ring`. Establish `hpQ : (n : ℚ) = 2 * p` using `by rw [hp]; push_cast; ring`.

Establish `hz0 : ∀ a, ∃ z : ℤ, lam a = (z : ℝ) + 1 / 2` using `fun a => by`. Take `⟨y, hy, hya⟩` from `(hr (lam a)).1 ⟨a, rfl⟩`. Take `⟨z, hz⟩` from `inCoset_weightX D τ j y hy`. Conclude with `⟨z, by rw [hya, hz]; push_cast; ring⟩`. Use `choose z hz using hz0`.

Establish `hzb : ∀ a, -e + s + 1 ≤ z a` using `fun a => by`. Take `⟨y, hy, hya⟩` from `(hr (lam a)).1 ⟨a, rfl⟩`. Establish `h1` using `habove y hy`. Establish `h3 : ((-(e : ℚ) + (D.R.t : ℚ) / 2 + 1 : ℚ) : ℝ) ≤ (y : ℝ)` using `by exact_mod_cast h1`. Move the coercions through the operations in `at h3`.

Rewrite `h3` using `[htR, ← hya, hz]`. Establish `h4 : ((-e + s + 1 : ℤ) : ℝ) ≤ z a` using `by push_cast; linarith`. Conclude with `h4` after adjusting the coercions. Establish `hzanti : StrictAnti z` using `fun a b hab => by`. Use `hE.1 hab` as an intermediate fact.

Rewrite `this` using `[hz, hz]`. Establish `: (z b : ℝ) < z a` using `by linarith`. Conclude with `this` after adjusting the coercions. Use `set c : ℝ := -(e : ℝ) + s + 1 / 2 with hc`. Establish `hshape` using `shape_below c lam hE.1 (fun a => by`.

Use `hzb a` as an intermediate fact. Establish `h : ((-e + s + 1 : ℤ) : ℝ) ≤ z a` using `by exact_mod_cast this`. Move the coercions through the operations in `at h`. Rewrite using `[hz, hc]; linarith) lam' hE'.1 (fun x => by`. Rewrite using `[hr' x, hr x]`.

Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨y, hy, rfl⟩`. Break down `mem_union.1 hy with hy | hy` into its components or cases. Conclude with `.inl ⟨y, hy, rfl⟩`. Take `⟨d, hd, rfl⟩` from `GlobalTheory.SignedHC.mem_block.1 hy`.

Use `.inr ⟨d, hd, ?_⟩` and prove the remaining obligations. Use `push_cast`. Rewrite using `[htR, hc]`. Expand and normalize the polynomial expressions, which then agree. Introduce and unpack `(⟨y, hy, rfl⟩ | ⟨d, hd, rfl⟩)`.

Conclude with `⟨y, mem_union_left _ hy, rfl⟩`. Use `⟨-(e : ℚ) + (((D.R.t + 1 : ℕ) : ℚ) - 1) / 2 - d, mem_union_right _ (GlobalTheory.SignedHC.mem_block.2 ⟨d, hd, rfl⟩), ?_⟩` and prove the remaining obligations. Use `push_cast`. Rewrite using `[htR, hc]`. Use the proof step `ring)`.

Set `ν : Fin (n + (D.R.t + 1)) → ℕ` to `fun b => if h : (b : ℕ) < n then (z ⟨b, h⟩ + (b : ℕ) + e - n - s).toNat else 0`. Establish `hmono : ∀ a b : Fin n, a ≤ b → z b + (b : ℕ) ≤ z a + (a : ℕ)` using `fun a b hab => by`. Use `GlobalTheory.LastStepParam.sub_mono' (z := fun a => -z a) (fun x y hxy => by simpa using hzanti hxy) hab` as an intermediate fact. Apply the tactic sequence `try simp only at this`. Use linear arithmetic over natural numbers and integers.

Establish `hpos : ∀ a : Fin n, 0 ≤ z a + (a : ℕ) + e - n - s` using `fun a => by`. Establish `ha` using `a.2`. Establish `h1` using `hmono a ⟨n - 1, by omega⟩ (Fin.mk_le_mk.2 (by omega) : (⟨a, a.2⟩ : Fin n) ≤ ⟨n - 1, by omega⟩)`. Establish `h2` using `hzb ⟨n - 1, by omega⟩`. Apply the tactic sequence `try simp only at h1`.

Use linear arithmetic over natural numbers and integers. Establish `hν : ∀ (b : Fin (n + (D.R.t + 1))) (h : (b : ℕ) < n), (ν b : ℝ) = z ⟨b, h⟩ + ((b : ℕ) : ℝ) + e - n - s`. Introduce `b h`. Establish `: ((ν b : ℕ) : ℤ) = z ⟨b, h⟩ + (b : ℕ) + e - n - s`. Simplify using `only [ν, dif_pos h]`.

Conclude with `Int.toNat_of_nonneg (hpos ⟨b, h⟩)`. Establish `: ((ν b : ℕ) : ℝ) = ((z ⟨b, h⟩ + (b : ℕ) + e - n - s : ℤ) : ℝ)` using `by exact_mod_cast this`. Rewrite using `[this]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.

Use `⟨-e + p, e - p - s - 1, ?_, ?_, by omega, ν, ?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[← hce]`. Use `push_cast`. Rewrite using `[hpQ]`. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[← hce]`. Use `push_cast`. Rewrite using `[hpQ, htQ]`. Expand and normalize the polynomial expressions, which then agree. Introduce `c d hcd`.

Establish `hcd' : (c : ℕ) ≤ d` using `hcd`. Simplify using `only [ν]`. Use `split_ifs with h1 h2 h2`. Apply the tactic sequence `all_goals first`. Consider the case `exact Nat.zero_le _`.

Consider the case `exact le_rfl`. Consider the case `omega`. Consider the case `(apply Int.toNat_le_toNat`. Use `hmono ⟨c, by omega⟩ ⟨d, by omega⟩ (Fin.mk_le_mk.2 hcd')` as an intermediate fact. Apply the tactic sequence `try simp only at this`.

Use the proof step `omega)`. Introduce `b hb`. Simplify using `only [ν]`. Rewrite using `[dif_neg (by omega)]`. Introduce `a`.

Establish `e1` using `hν (Fin.castLE (by omega) a) a.2`. Rewrite using `[GlobalTheory.LastStepParam.lowK_allPos, e1, hz a]`. Simplify using `only [Fin.val_castLE, Fin.eta]`. Use `push_cast`. Combine the linear relations using `[hpR]`.

Introduce `b`. Rewrite using `[GlobalTheory.LastStepParam.lowK_allPos, hshape b]`. Distinguish the cases in `hb : (b : ℕ) < n`. Rewrite using `[dif_pos hb, hz, hν b hb]`. Use `push_cast`.

Combine the linear relations using `[hpR, htR]`. Establish `h0 : ν b = 0` using `by simp only [ν]; rw [dif_neg hb]`. Rewrite using `[dif_neg hb, h0, Nat.cast_sub (by omega)]`. Use `push_cast`. Combine the linear relations using `[hpR, htR]`.
-/
theorem colPar : ∀ (D : D7) (j : ℕ) (hj : j < D.R.m) (τ : D.what₂.Tau) (n N : ℕ) (lam : Fin n → ℝ) (ε : Fin n → Bool) (lam' : Fin N → ℝ) (ε' : Fin N → Bool), Formalism.L2.Theta.IsEnum (GlobalTheory.Grid.parXp D j τ) lam ε → Formalism.L2.Theta.IsEnum (GlobalTheory.Grid.parXp D (j + 1) τ) lam' ε' → ε = Formalism.MainNotions.S.allPos n ∧ ε' = Formalism.MainNotions.S.allPos N ∧ ∃ x₁ x₃ : ℤ, (x₁ : ℚ) = -(D.hc τ).e ⟨j, hj⟩ + (n : ℚ) / 2 ∧ (x₃ : ℚ) = -((N : ℚ) / 2 + -(D.hc τ).e ⟨j, hj⟩) ∧ ∃ (hn : n ≤ N) (ν : Fin N → ℕ), Antitone ν ∧ (∀ b : Fin N, n ≤ (b : ℕ) → ν b = 0) ∧ (∀ a, Formalism.QuantumDeterminants.lowK (Formalism.MainNotions.S.allPos n) lam a = -(x₃ : ℝ) + ν (Fin.castLE hn a)) ∧ ∀ b, Formalism.QuantumDeterminants.lowK (Formalism.MainNotions.S.allPos N) lam' b = (x₁ : ℝ) + ν b := by
  intro D j hj τ n N lam ε lam' ε' hE hE'
  have hj' : j + 1 ≤ D.R.m := hj
  obtain ⟨s, hs⟩ := D.R.t_odd
  have htR : (D.R.t : ℝ) = 2 * s + 1 := by rw [hs]; push_cast; ring
  have htQ : (D.R.t : ℚ) = 2 * s + 1 := by rw [hs]; push_cast; ring
  set e : ℤ := (grid D τ).e (j + 1) with he_def
  have hce : (e : ℚ) = (D.hc τ).e ⟨j, hj⟩ := by
    have := e_eq D τ (l := j + 1) (by omega) hj'
    simp only [Nat.add_sub_cancel] at this
    exact this
  have hB : (grid D τ).blockMPlus (j + 1) = TPar.block (-(e : ℚ)) (D.R.t + 1) := rfl
  have hX : parXp D j τ = GlobalTheory.SignedHC.plus ((grid D τ).weightX j) := rfl
  have hX' : parXp D (j + 1) τ =
      GlobalTheory.SignedHC.plus ((grid D τ).weightX j ∪ TPar.block (-(e : ℚ)) (D.R.t + 1)) := by
    show GlobalTheory.SignedHC.plus ((grid D τ).weightX (j + 1)) = _
    rw [(grid D τ).weightX_succ, hB]
  rw [hX] at hE
  rw [hX'] at hE'
  obtain ⟨hε, hcard, hr⟩ := enum_plus hE
  obtain ⟨hε', hcard', hr'⟩ := enum_plus hE'
  have htop : -(e : ℚ) + (D.R.t : ℚ) / 2 ∈ (grid D τ).blockMPlus (j + 1) := by
    rw [hB]; exact GlobalTheory.SignedHC.mem_block.2 ⟨0, by omega, by push_cast; ring⟩
  have habove : ∀ x ∈ (grid D τ).weightX j, -(e : ℚ) + (D.R.t : ℚ) / 2 + 1 ≤ x := by
    intro x hx
    have hlt := weightX_above D τ hj' hx htop
    obtain ⟨z, hz⟩ := inCoset_weightX D τ j x hx
    rw [hz, htQ] at hlt ⊢
    have : ((-e + s : ℤ) : ℚ) < z := by push_cast; linarith
    have h2 : -e + s < z := by exact_mod_cast this
    have h3 : ((-e + s + 1 : ℤ) : ℚ) ≤ z := by exact_mod_cast Int.add_one_le_iff.2 h2
    push_cast at h3
    linarith
  have hdisj : Disjoint ((grid D τ).weightX j) (TPar.block (-(e : ℚ)) (D.R.t + 1)) :=
    disjoint_left.2 fun x hx hy => (weightX_above D τ hj' hx (by rw [hB]; exact hy)).ne rfl
  have hN : N = n + (D.R.t + 1) := by
    rw [← hcard', card_union_of_disjoint hdisj, hcard, GlobalTheory.SignedHC.card_block]
  have hne : Even n := by
    rw [← hcard, card_weightX D τ (by omega)]; exact GlobalTheory.ChiGrid.even_rankX D j
  subst hN
  refine ⟨hε, hε', ?_⟩
  obtain ⟨p, hp⟩ := hne
  have hpR : (n : ℝ) = 2 * p := by rw [hp]; push_cast; ring
  have hpQ : (n : ℚ) = 2 * p := by rw [hp]; push_cast; ring
  have hz0 : ∀ a, ∃ z : ℤ, lam a = (z : ℝ) + 1 / 2 := fun a => by
    obtain ⟨y, hy, hya⟩ := (hr (lam a)).1 ⟨a, rfl⟩
    obtain ⟨z, hz⟩ := inCoset_weightX D τ j y hy
    exact ⟨z, by rw [hya, hz]; push_cast; ring⟩
  choose z hz using hz0
  have hzb : ∀ a, -e + s + 1 ≤ z a := fun a => by
    obtain ⟨y, hy, hya⟩ := (hr (lam a)).1 ⟨a, rfl⟩
    have h1 := habove y hy
    have h3 : ((-(e : ℚ) + (D.R.t : ℚ) / 2 + 1 : ℚ) : ℝ) ≤ (y : ℝ) := by exact_mod_cast h1
    push_cast at h3
    rw [htR, ← hya, hz] at h3
    have h4 : ((-e + s + 1 : ℤ) : ℝ) ≤ z a := by push_cast; linarith
    exact_mod_cast h4
  have hzanti : StrictAnti z := fun a b hab => by
    have := hE.1 hab
    rw [hz, hz] at this
    have : (z b : ℝ) < z a := by linarith
    exact_mod_cast this
  set c : ℝ := -(e : ℝ) + s + 1 / 2 with hc
  have hshape := shape_below c lam hE.1 (fun a => by
      have := hzb a
      have h : ((-e + s + 1 : ℤ) : ℝ) ≤ z a := by exact_mod_cast this
      push_cast at h
      rw [hz, hc]; linarith) lam' hE'.1 (fun x => by
      rw [hr' x, hr x]
      constructor
      · rintro ⟨y, hy, rfl⟩
        rcases mem_union.1 hy with hy | hy
        · exact .inl ⟨y, hy, rfl⟩
        · obtain ⟨d, hd, rfl⟩ := GlobalTheory.SignedHC.mem_block.1 hy
          refine .inr ⟨d, hd, ?_⟩
          push_cast
          rw [htR, hc]; ring
      · rintro (⟨y, hy, rfl⟩ | ⟨d, hd, rfl⟩)
        · exact ⟨y, mem_union_left _ hy, rfl⟩
        · refine ⟨-(e : ℚ) + (((D.R.t + 1 : ℕ) : ℚ) - 1) / 2 - d,
            mem_union_right _ (GlobalTheory.SignedHC.mem_block.2 ⟨d, hd, rfl⟩), ?_⟩
          push_cast
          rw [htR, hc]; ring)
  let ν : Fin (n + (D.R.t + 1)) → ℕ := fun b =>
    if h : (b : ℕ) < n then (z ⟨b, h⟩ + (b : ℕ) + e - n - s).toNat else 0
  have hmono : ∀ a b : Fin n, a ≤ b → z b + (b : ℕ) ≤ z a + (a : ℕ) := fun a b hab => by
    have := GlobalTheory.LastStepParam.sub_mono' (z := fun a => -z a) (fun x y hxy => by simpa using hzanti hxy) hab
    try simp only at this
    omega
  have hpos : ∀ a : Fin n, 0 ≤ z a + (a : ℕ) + e - n - s := fun a => by
    have ha := a.2
    have h1 := hmono a ⟨n - 1, by omega⟩ (Fin.mk_le_mk.2 (by omega) : (⟨a, a.2⟩ : Fin n) ≤ ⟨n - 1, by omega⟩)
    have h2 := hzb ⟨n - 1, by omega⟩
    try simp only at h1
    omega
  have hν : ∀ (b : Fin (n + (D.R.t + 1))) (h : (b : ℕ) < n), (ν b : ℝ) = z ⟨b, h⟩ + ((b : ℕ) : ℝ) + e - n - s := by
    intro b h
    have : ((ν b : ℕ) : ℤ) = z ⟨b, h⟩ + (b : ℕ) + e - n - s := by
      simp only [ν, dif_pos h]
      exact Int.toNat_of_nonneg (hpos ⟨b, h⟩)
    have : ((ν b : ℕ) : ℝ) = ((z ⟨b, h⟩ + (b : ℕ) + e - n - s : ℤ) : ℝ) := by exact_mod_cast this
    rw [this]; push_cast; ring
  refine ⟨-e + p, e - p - s - 1, ?_, ?_, by omega, ν, ?_, ?_, ?_, ?_⟩
  · rw [← hce]; push_cast; rw [hpQ]; ring
  · rw [← hce]; push_cast; rw [hpQ, htQ]; ring
  · intro c d hcd
    have hcd' : (c : ℕ) ≤ d := hcd
    simp only [ν]
    split_ifs with h1 h2 h2
    all_goals first
      | exact Nat.zero_le _
      | exact le_rfl
      | omega
      | (apply Int.toNat_le_toNat
         have := hmono ⟨c, by omega⟩ ⟨d, by omega⟩ (Fin.mk_le_mk.2 hcd')
         try simp only at this
         omega)
  · intro b hb
    simp only [ν]
    rw [dif_neg (by omega)]
  · intro a
    have e1 := hν (Fin.castLE (by omega) a) a.2
    rw [GlobalTheory.LastStepParam.lowK_allPos, e1, hz a]
    simp only [Fin.val_castLE, Fin.eta]
    push_cast
    linarith [hpR]
  · intro b
    rw [GlobalTheory.LastStepParam.lowK_allPos, hshape b]
    by_cases hb : (b : ℕ) < n
    · rw [dif_pos hb, hz, hν b hb]
      push_cast
      linarith [hpR, htR]
    · have h0 : ν b = 0 := by simp only [ν]; rw [dif_neg hb]
      rw [dif_neg hb, h0, Nat.cast_sub (by omega)]
      push_cast
      linarith [hpR, htR]

end GlobalTheory.ColParam

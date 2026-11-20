import Formalism.SharpRestriction.GrowthBounds.StandardPolynomials.KGShift
import Formalism.SharpRestriction.GrowthBounds.FrobeniusPaths.AntitoneOfAppend

noncomputable section

open MvPolynomial Finset Formalism.MainNotions.G Formalism.MainNotions.CovariantDegrees Formalism.MainNotions.LemmaBAlt Formalism.MainNotions.LemmaBAlt.B2

namespace Formalism.MainNotions.ColumnSystems.Pf.Col

variable {N K : ℕ}

def kaS (ka : Fin (N + 1) → Fin K → ℤ) : Fin (N + 1 + 1) → Fin K → ℤ := Fin.cons 0 ka

def muP (nu : ℕ → ℤ) (ka : Fin (N + 1) → Fin K → ℤ) : Fin (N + 1 + 1) → Fin (1 + K) → ℤ :=
  joinPT (fun t _ => nu t.val) (kaS ka)

structure PH (vecc : Fin N → Bool) (B : Fin N → ℕ) (ka : Fin (N + 1) → Fin K → ℤ) (nu : ℕ → ℤ) : Prop where
  ka0 : ka 0 = 0
  kadom : ∀ i, Dominant (ka i)
  kastep : ∀ i : Fin N, if vecc i then HStrip (ka i.castSucc) (ka i.succ) (B i) else HStrip (ka i.succ) (ka i.castSucc) (B i)
  nu0 : nu 0 = 0
  numono : ∀ t, nu t ≤ nu (t + 1)
  nucov : ∀ i : Fin N, vecc i = false → nu (i.val + 2) = nu (i.val + 1)
  C : ∀ i : Fin N, vecc i = true → ∀ b, ka i.succ b ≤ nu (i.val + 1)
  hK : N < K

/- English proof (translation)
Simplify using `only [colH, Finset.card_filter]`. Rewrite using `[Fin.sum_univ_add]`. Simplify using `[muP, joinPT]`.
-/
theorem colH_muP (nu : ℕ → ℤ) (ka : Fin (N + 1) → Fin K → ℤ) (t : Fin (N + 1 + 1)) (c : ℤ) :
    colH (muP nu ka t) c = (if c ≤ nu t.val then 1 else 0) + colH (kaS ka t) c := by
  simp only [colH, Finset.card_filter]
  rw [Fin.sum_univ_add]
  simp [muP, joinPT]

/- English proof (translation)
Unfold `colH`. Apply the tactic sequence `split_ifs with hc <;> simp [hc]`.
-/
theorem colH_zero (c : ℤ) : colH (0 : Fin K → ℤ) c = if c ≤ 0 then K else 0 := by
  unfold colH
  split_ifs with hc <;> simp [hc]

/- English proof (translation)
Rewrite using `[colH_muP, Fin.val_zero]`. Use `congr 1`. Simplify using `only [kaS, Fin.cons_zero]`. Conclude with `colH_zero c`.
-/
theorem H0 (nu : ℕ → ℤ) (ka : Fin (N + 1) → Fin K → ℤ) (c : ℤ) :
    colH (muP nu ka 0) c = (if c ≤ nu 0 then 1 else 0) + (if c ≤ 0 then K else 0) := by
  rw [colH_muP, Fin.val_zero]
  congr 1
  simp only [kaS, Fin.cons_zero]
  exact colH_zero c

/- English proof (translation)
Rewrite using `[colH_muP]`. Both sides reduce to the same expression.
-/
theorem HS (nu : ℕ → ℤ) (ka : Fin (N + 1) → Fin K → ℤ) (i : Fin (N + 1)) (c : ℤ) :
    colH (muP nu ka i.succ) c = (if c ≤ nu (i.val + 1) then 1 else 0) + colH (ka i) c := by
  rw [colH_muP]; rfl

variable {vecc : Fin N → Bool} {B : Fin N → ℕ} {ka : Fin (N + 1) → Fin K → ℤ} {nu : ℕ → ℤ}

/- English proof (translation)
Introduce `t`. Proceed by induction on `t with`. Consider the case `zero => exact h.nu0.ge`. Consider the case `succ t ih => exact ih.trans (h.numono t)`.
-/
theorem PH.nonneg (h : PH vecc B ka nu) : ∀ t, 0 ≤ nu t := by
  intro t
  induction t with
  | zero => exact h.nu0.ge
  | succ t ih => exact ih.trans (h.numono t)

/- English proof (translation)
Introduce `i`. Proceed by induction on `i using Fin.induction with`. Consider the case `zero`. Introduce `b`. Simplify `h.nonneg 1` using `[h.ka0]`.

Consider the case `succ j ih`. Introduce `b`. Establish `hs` using `h.kastep j`. Distinguish the cases in `hv : vecc j = true`. Establish `h1 : ka j.succ b ≤ nu (j.val + 1)` using `h.C j hv b`.

Establish `h2 : nu (j.val + 1) ≤ nu (j.val + 1 + 1)` using `h.numono _`. Conclude with `h1.trans h2`. Rewrite `hs` using `[if_neg hv]`. Establish `h1 : ka j.succ b ≤ ka j.castSucc b` using `hs.1 b`. Establish `h2 : ka j.castSucc b ≤ nu (j.val + 1)` using `ih b`.

Establish `h3 : nu (j.val + 1) ≤ nu (j.val + 1 + 1)` using `h.numono _`. Conclude with `h1.trans (h2.trans h3)`.
-/
theorem PH.ka_le (h : PH vecc B ka nu) : ∀ (i : Fin (N + 1)) (b : Fin K), ka i b ≤ nu (i.val + 1) := by
  intro i
  induction i using Fin.induction with
  | zero =>
    intro b
    simpa [h.ka0] using h.nonneg 1
  | succ j ih =>
    intro b
    have hs := h.kastep j
    by_cases hv : vecc j = true
    · have h1 : ka j.succ b ≤ nu (j.val + 1) := h.C j hv b
      have h2 : nu (j.val + 1) ≤ nu (j.val + 1 + 1) := h.numono _
      exact h1.trans h2
    · rw [if_neg hv] at hs
      have h1 : ka j.succ b ≤ ka j.castSucc b := hs.1 b
      have h2 : ka j.castSucc b ≤ nu (j.val + 1) := ih b
      have h3 : nu (j.val + 1) ≤ nu (j.val + 1 + 1) := h.numono _
      exact h1.trans (h2.trans h3)

/- English proof (translation)
Unfold `colH at h`. Take `⟨b, hb⟩` from `Finset.card_pos.1 h`. Conclude with `⟨b, (Finset.mem_filter.1 hb).2⟩`.
-/
theorem pos_of_colH {n : ℕ} {mu : Fin n → ℤ} {c : ℤ} (h : 1 ≤ colH mu c) : ∃ b, c ≤ mu b := by
  unfold colH at h
  obtain ⟨b, hb⟩ := Finset.card_pos.1 h
  exact ⟨b, (Finset.mem_filter.1 hb).2⟩

/- English proof (translation)
Take `⟨b, hb⟩` from `pos_of_colH hc`. Conclude with `hb.trans (h.ka_le i b)`.
-/
theorem PH.pos_le (h : PH vecc B ka nu) (i : Fin (N + 1)) {c : ℤ} (hc : 1 ≤ colH (ka i) c) : c ≤ nu (i.val + 1) := by
  obtain ⟨b, hb⟩ := pos_of_colH hc
  exact hb.trans (h.ka_le i b)

/- English proof (translation)
Take `⟨h1, h2, -⟩` from `hs`. Unfold `colH`. Prove the components needed by the constructor for the conclusion. Conclude with `Finset.card_le_card fun x hx => by`. Simplify using `only [Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢`.

Conclude with `hx.trans (h1 x)`. Establish `hsplit : (Finset.univ.filter fun x : Fin n => c ≤ b x) ⊆ (Finset.univ.filter fun x : Fin n => x.val = 0) ∪ (Finset.univ.filter fun x : Fin n => 0 < x.val ∧ c ≤ b x)`. Introduce `x hx`. Simplify using `only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢`. Distinguish the cases in `hx0 : x.val = 0`.

Conclude with `Or.inl hx0`. Conclude with `Or.inr ⟨Nat.pos_of_ne_zero hx0, hx⟩`. Establish `hz : (Finset.univ.filter fun x : Fin n => x.val = 0).card ≤ 1`. Rewrite using `[Finset.card_le_one]`. Introduce `x hx y hy`.

Simplify using `only [Finset.mem_filter, Finset.mem_univ, true_and] at hx hy`. Conclude with `Fin.ext (hx.trans hy.symm)`. Establish `hinj : (Finset.univ.filter fun x : Fin n => 0 < x.val ∧ c ≤ b x).card ≤ (Finset.univ.filter fun x : Fin n => c ≤ a x).card`. Use `Finset.card_le_card_of_injOn (fun x => ⟨x.val - 1, lt_of_le_of_lt (Nat.sub_le _ _) x.isLt⟩) ?_ ?_` and prove the remaining obligations. Introduce `x hx`.

Simplify using `only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢`. Establish `hlt : x.val - 1 + 1 < n` using `by have := x.isLt; omega`. Establish `hb` using `h2 ⟨x.val - 1, lt_of_le_of_lt (Nat.sub_le _ _) x.isLt⟩ hlt`. Establish `e : (⟨x.val - 1 + 1, hlt⟩ : Fin n) = x` using `Fin.ext (by simp only; omega)`. Rewrite `hb` using `[e]`.

Conclude with `hx.2.trans hb`. Introduce `x hx y hy hxy`. Simplify using `only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hx hy`. Use `congrArg Fin.val hxy` as an intermediate fact. Simplify using `only at this`.

Conclude with `Fin.ext (by omega)`. Combine the equalities or inequalities in the displayed calculation.
-/
private theorem colH_le_le_add_one_of_HStrip {n : ℕ} {a b : Fin n → ℤ} {m : ℕ} (hs : HStrip a b m) (c : ℤ) :
    colH a c ≤ colH b c ∧ colH b c ≤ colH a c + 1 := by
  obtain ⟨h1, h2, -⟩ := hs
  unfold colH
  constructor
  · exact Finset.card_le_card fun x hx => by
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
      exact hx.trans (h1 x)
  · have hsplit : (Finset.univ.filter fun x : Fin n => c ≤ b x) ⊆
        (Finset.univ.filter fun x : Fin n => x.val = 0) ∪
          (Finset.univ.filter fun x : Fin n => 0 < x.val ∧ c ≤ b x) := by
      intro x hx
      simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
      by_cases hx0 : x.val = 0
      · exact Or.inl hx0
      · exact Or.inr ⟨Nat.pos_of_ne_zero hx0, hx⟩
    have hz : (Finset.univ.filter fun x : Fin n => x.val = 0).card ≤ 1 := by
      rw [Finset.card_le_one]
      intro x hx y hy
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx hy
      exact Fin.ext (hx.trans hy.symm)
    have hinj : (Finset.univ.filter fun x : Fin n => 0 < x.val ∧ c ≤ b x).card ≤
        (Finset.univ.filter fun x : Fin n => c ≤ a x).card := by
      refine Finset.card_le_card_of_injOn
        (fun x => ⟨x.val - 1, lt_of_le_of_lt (Nat.sub_le _ _) x.isLt⟩) ?_ ?_
      · intro x hx
        simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
        have hlt : x.val - 1 + 1 < n := by have := x.isLt; omega
        have hb := h2 ⟨x.val - 1, lt_of_le_of_lt (Nat.sub_le _ _) x.isLt⟩ hlt
        have e : (⟨x.val - 1 + 1, hlt⟩ : Fin n) = x := Fin.ext (by simp only; omega)
        rw [e] at hb
        exact hx.2.trans hb
      · intro x hx y hy hxy
        simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hx hy
        have := congrArg Fin.val hxy
        simp only at this
        exact Fin.ext (by omega)
    calc _ ≤ _ := Finset.card_le_card hsplit
      _ ≤ _ := Finset.card_union_le _ _
      _ ≤ _ := by omega

/- English proof (translation)
Establish `hs` using `h.kastep i`. Rewrite `hs` using `[if_pos hv]`. Take `⟨s1, s2⟩` from `colH_le_le_add_one_of_HStrip hs c`. Use `⟨s1, s2, fun hlt => ?_⟩` and prove the remaining obligations. Take `⟨b, hb⟩` from `pos_of_colH (c := c) (mu := ka i.succ) (by omega)`.

Conclude with `hb.trans (h.C i hv b)`.
-/
theorem PH.stepV (h : PH vecc B ka nu) (i : Fin N) (hv : vecc i = true) (c : ℤ) :
    colH (ka i.castSucc) c ≤ colH (ka i.succ) c ∧ colH (ka i.succ) c ≤ colH (ka i.castSucc) c + 1 ∧
      (colH (ka i.castSucc) c < colH (ka i.succ) c → c ≤ nu (i.val + 1)) := by
  have hs := h.kastep i
  rw [if_pos hv] at hs
  obtain ⟨s1, s2⟩ := colH_le_le_add_one_of_HStrip hs c
  refine ⟨s1, s2, fun hlt => ?_⟩
  obtain ⟨b, hb⟩ := pos_of_colH (c := c) (mu := ka i.succ) (by omega)
  exact hb.trans (h.C i hv b)

/- English proof (translation)
Establish `hs` using `h.kastep i`. Rewrite `hs` using `[if_neg (by simp [hv])]`. Conclude with `colH_le_le_add_one_of_HStrip hs c`.
-/
theorem PH.stepC (h : PH vecc B ka nu) (i : Fin N) (hv : vecc i = false) (c : ℤ) :
    colH (ka i.succ) c ≤ colH (ka i.castSucc) c ∧ colH (ka i.castSucc) c ≤ colH (ka i.succ) c + 1 := by
  have hs := h.kastep i
  rw [if_neg (by simp [hv])] at hs
  exact colH_le_le_add_one_of_HStrip hs c

/- English proof (translation)
Introduce `i`. Proceed by induction on `i using Fin.induction with`. Consider the case `zero => rw [h.ka0, colH_zero, if_pos hc]`. Simplify using the standard rewrite rules. Consider the case `succ i ih`.

Simplify using `only [Fin.val_succ, Fin.val_castSucc] at ih ⊢`. Distinguish the cases in `hv : vecc i = true`. Use `(h.stepV i hv c).1` as an intermediate fact. Use linear arithmetic over natural numbers and integers. Use `(h.stepC i (by simpa using hv) c).2; omega` as an intermediate fact.
-/
theorem PH.dualLow (h : PH vecc B ka nu) {c : ℤ} (hc : c ≤ 0) : ∀ i : Fin (N + 1), K ≤ colH (ka i) c + i.val := by
  intro i
  induction i using Fin.induction with
  | zero => rw [h.ka0, colH_zero, if_pos hc]; simp
  | succ i ih =>
    simp only [Fin.val_succ, Fin.val_castSucc] at ih ⊢
    by_cases hv : vecc i = true
    · have := (h.stepV i hv c).1; omega
    · have := (h.stepC i (by simpa using hv) c).2; omega

/- English proof (translation)
Establish `h1` using `h.dualLow hc i`. Establish `h2` using `i.isLt`. Establish `h3` using `h.hK`. Use linear arithmetic over natural numbers and integers.
-/
theorem PH.dual1 (h : PH vecc B ka nu) {c : ℤ} (hc : c ≤ 0) (i : Fin (N + 1)) : 1 ≤ colH (ka i) c := by
  have h1 := h.dualLow hc i
  have h2 := i.isLt
  have h3 := h.hK
  omega

/- English proof (translation)
Use `⟨?_, ?_⟩` and prove the remaining obligations. Rewrite using `[← Fin.succ_castSucc]`. Conclude with `HS nu ka i.castSucc c`. Conclude with `HS nu ka i.succ c`.
-/
theorem PH.heights (_h : PH vecc B ka nu) (i : Fin N) (c : ℤ) :
    colH (muP nu ka i.succ.castSucc) c = (if c ≤ nu (i.val + 1) then 1 else 0) + colH (ka i.castSucc) c ∧
    colH (muP nu ka i.succ.succ) c = (if c ≤ nu (i.val + 2) then 1 else 0) + colH (ka i.succ) c := by
  refine ⟨?_, ?_⟩
  · rw [← Fin.succ_castSucc]
    exact HS nu ka i.castSucc c
  · exact HS nu ka i.succ c

/- English proof (translation)
Use `⟨?_, ?_⟩` and prove the remaining obligations. Establish `e` using `H0 nu ka c`. Rewrite `e` using `[h.nu0]`. Simplify using `using e`. Apply the tactic sequence `rw [HS, h.ka0, colH_zero] try simp`.
-/
theorem PH.heights0 (h : PH vecc B ka nu) (c : ℤ) :
    colH (muP nu ka (0 : Fin (N + 1)).castSucc) c = (if c ≤ 0 then 1 else 0) + (if c ≤ 0 then K else 0) ∧
    colH (muP nu ka (0 : Fin (N + 1)).succ) c = (if c ≤ nu 1 then 1 else 0) + (if c ≤ 0 then K else 0) := by
  refine ⟨?_, ?_⟩
  · have e := H0 nu ka c
    rw [h.nu0] at e
    simpa using e
  · rw [HS, h.ka0, colH_zero]
    try simp

/- English proof (translation)
Unfold `IsCostly`. Take `⟨h1, h2⟩` from `h.heights0 c`. Rewrite using `[h1, h2]`. Use `h.nonneg 1` as an intermediate fact. Use `h.hK` as an intermediate fact.

Apply the tactic sequence `split_ifs <;> omega`.
-/
theorem PH.not_costly_zero (h : PH vecc B ka nu) (c : ℤ) : ¬ IsCostly (muP nu ka) c 0 := by
  unfold IsCostly
  obtain ⟨h1, h2⟩ := h.heights0 c
  rw [h1, h2]
  have := h.nonneg 1
  have := h.hK
  split_ifs <;> omega

/- English proof (translation)
Take `⟨e1, e2⟩` from `h.heights i c`. Establish `hm : nu (i.val + 1) ≤ nu (i.val + 2)` using `h.numono _`. Establish `p1 : 1 ≤ colH (ka i.castSucc) c → c ≤ nu (i.val + 1)` using `fun hc => h.pos_le i.castSucc hc`. Unfold `IsCostly`. Rewrite using `[e1, e2]`.

Consider the cases of `hv : vecc i`. Establish `hc` using `h.nucov i hv`. Use `h.stepC i hv c` as an intermediate fact. Rewrite using `[hc]`. Distinguish the cases in `hx : 1 ≤ colH (ka i.castSucc) c`.

Apply the tactic sequence `have := p1 hx split_ifs <;> omega`. Apply the tactic sequence `split_ifs <;> omega`. Take `⟨s1, s2, s3⟩` from `h.stepV i hv c`. Distinguish the cases in `hlt : colH (ka i.castSucc) c < colH (ka i.succ) c`. Apply the tactic sequence `have := s3 hlt split_ifs <;> omega`.

Distinguish the cases in `hx : 1 ≤ colH (ka i.castSucc) c`. Apply the tactic sequence `have := p1 hx split_ifs <;> omega`. Apply the tactic sequence `split_ifs <;> omega`.
-/
theorem PH.costly_succ (h : PH vecc B ka nu) (i : Fin N) (c : ℤ) :
    IsCostly (muP nu ka) c i.succ ↔ colH (ka i.castSucc) c < colH (ka i.succ) c := by
  obtain ⟨e1, e2⟩ := h.heights i c
  have hm : nu (i.val + 1) ≤ nu (i.val + 2) := h.numono _
  have p1 : 1 ≤ colH (ka i.castSucc) c → c ≤ nu (i.val + 1) := fun hc => h.pos_le i.castSucc hc
  unfold IsCostly
  rw [e1, e2]
  cases hv : vecc i
  · have hc := h.nucov i hv
    have := h.stepC i hv c
    rw [hc]
    by_cases hx : 1 ≤ colH (ka i.castSucc) c
    · have := p1 hx
      split_ifs <;> omega
    · split_ifs <;> omega
  · obtain ⟨s1, s2, s3⟩ := h.stepV i hv c
    by_cases hlt : colH (ka i.castSucc) c < colH (ka i.succ) c
    · have := s3 hlt
      split_ifs <;> omega
    · by_cases hx : 1 ≤ colH (ka i.castSucc) c
      · have := p1 hx
        split_ifs <;> omega
      · split_ifs <;> omega

/- English proof (translation)
Unfold `oc`. Rewrite using `[Fin.sum_univ_succ, if_neg (h.not_costly_zero c), zero_add]`. Conclude with `Finset.sum_congr rfl fun i _ => if_congr (h.costly_succ i c) rfl rfl`.
-/
theorem PH.oc_eq (h : PH vecc B ka nu) (om : Fin (N + 1) → ℕ) (c : ℤ) :
    oc om (muP nu ka) c = ∑ i : Fin N, if colH (ka i.castSucc) c < colH (ka i.succ) c then om i.succ else 0 := by
  classical
  unfold oc
  rw [Fin.sum_univ_succ, if_neg (h.not_costly_zero c), zero_add]
  exact Finset.sum_congr rfl fun i _ => if_congr (h.costly_succ i c) rfl rfl

/- English proof (translation)
Establish `hv : Antitone (kaS ka t)`. Proceed by induction on `t using Fin.cases with`. Consider the case `zero`. Simplify using `only [kaS, Fin.cons_zero]`. Conclude with `fun _ _ _ => le_rfl`.

Consider the case `succ i`. Simplify using `only [kaS, Fin.cons_succ]`. Conclude with `h.kadom i`. Establish `hb : ∀ b, kaS ka t b ≤ nu t.val`. Proceed by induction on `t using Fin.cases with`.

Consider the case `zero`. Introduce `b`. Simplify using `[kaS, h.nu0]`. Consider the case `succ i`. Introduce `b`.

Simplify using `only [kaS, Fin.cons_succ, Fin.val_succ]`. Conclude with `h.ka_le i b`. Unfold `Dominant`. Introduce `a b hab`. Proceed by induction on `a using Fin.addCases with`.

Consider the case `left i`. Proceed by induction on `b using Fin.addCases with`. Consider the case `left j => simp [muP, joinPT]`. Consider the case `right j`. Simplify using `only [muP, joinPT, Fin.append_left, Fin.append_right]`.

Conclude with `hb j`. Consider the case `right i`. Proceed by induction on `b using Fin.addCases with`. Consider the case `left j`. It suffices to derive a contradiction.

Rewrite `hab` using `[Fin.le_def]`. Simplify using `only [Fin.coe_natAdd, Fin.coe_castAdd] at hab`. Use `j.isLt` as an intermediate fact. Use linear arithmetic over natural numbers and integers. Consider the case `right j`.

Simplify using `only [muP, joinPT, Fin.append_right]`. Apply `hv` to reduce the goal to its premises. Rewrite `hab`, the goal using `[Fin.le_def]`. Simplify using `only [Fin.coe_natAdd] at hab`. Use linear arithmetic over natural numbers and integers.
-/
theorem PH.dom (h : PH vecc B ka nu) (t : Fin (N + 1 + 1)) : Dominant (muP nu ka t) := by
  have hv : Antitone (kaS ka t) := by
    induction t using Fin.cases with
    | zero =>
      simp only [kaS, Fin.cons_zero]
      exact fun _ _ _ => le_rfl
    | succ i =>
      simp only [kaS, Fin.cons_succ]
      exact h.kadom i
  have hb : ∀ b, kaS ka t b ≤ nu t.val := by
    induction t using Fin.cases with
    | zero =>
      intro b
      simp [kaS, h.nu0]
    | succ i =>
      intro b
      simp only [kaS, Fin.cons_succ, Fin.val_succ]
      exact h.ka_le i b
  unfold Dominant
  intro a b hab
  induction a using Fin.addCases with
  | left i =>
    induction b using Fin.addCases with
    | left j => simp [muP, joinPT]
    | right j =>
      simp only [muP, joinPT, Fin.append_left, Fin.append_right]
      exact hb j
  | right i =>
    induction b using Fin.addCases with
    | left j =>
      exfalso
      rw [Fin.le_def] at hab
      simp only [Fin.coe_natAdd, Fin.coe_castAdd] at hab
      have := j.isLt
      omega
    | right j =>
      simp only [muP, joinPT, Fin.append_right]
      apply hv
      rw [Fin.le_def] at hab ⊢
      simp only [Fin.coe_natAdd] at hab
      omega

/- English proof (translation)
Proceed by induction on `i using Fin.cases with`. Consider the case `zero`. Take `⟨e1, e2⟩` from `h.heights0 c`. Use `h.nonneg 1` as an intermediate fact. Rewrite using `[e1, e2, hv0]`.

Use `⟨fun hlt => ⟨rfl, ?_⟩, fun hlt => ?_⟩` and prove the remaining obligations. Apply the tactic sequence `split_ifs at hlt ⊢ <;> omega`. Apply the tactic sequence `exfalso split_ifs at hlt <;> omega`. Consider the case `succ k`. Take `⟨e1, e2⟩` from `h.heights k c`.

Establish `hm : nu (k.val + 1) ≤ nu (k.val + 2)` using `h.numono _`. Establish `p1 : 1 ≤ colH (ka k.castSucc) c → c ≤ nu (k.val + 1)` using `fun hc => h.pos_le k.castSucc hc`. Rewrite using `[e1, e2, hvs]`. Consider the cases of `hv : vecc k`. Establish `hc` using `h.nucov k hv`.

Use `h.stepC k hv c` as an intermediate fact. Rewrite using `[hc]`. Use `⟨fun hlt => ?_, fun hlt => ⟨rfl, ?_⟩⟩` and prove the remaining obligations. Apply the tactic sequence `exfalso split_ifs at hlt <;> omega`. Apply the tactic sequence `split_ifs at hlt ⊢ <;> omega`.

Take `⟨s1, s2, s3⟩` from `h.stepV k hv c`. Use `⟨fun hlt => ⟨rfl, ?_⟩, fun hlt => ?_⟩` and prove the remaining obligations. Distinguish the cases in `hx : colH (ka k.castSucc) c < colH (ka k.succ) c`. Apply the tactic sequence `have := s3 hx split_ifs at hlt ⊢ <;> omega`. Apply the tactic sequence `split_ifs at hlt ⊢ <;> omega`.

Apply the tactic sequence `exfalso split_ifs at hlt <;> omega`.
-/
private theorem colH_muP_succ_ne_castSucc_iff_vec (h : PH vecc B ka nu) (LL : LiftLetters (Fin (N + 1))) (hv0 : LL.vec 0 = true)
    (hvs : ∀ i : Fin N, LL.vec i.succ = vecc i) (c : ℤ) (i : Fin (N + 1)) :
    (colH (muP nu ka i.castSucc) c < colH (muP nu ka i.succ) c →
      LL.vec i = true ∧ colH (muP nu ka i.succ) c = colH (muP nu ka i.castSucc) c + 1) ∧
    (colH (muP nu ka i.succ) c < colH (muP nu ka i.castSucc) c →
      LL.vec i = false ∧ colH (muP nu ka i.castSucc) c = colH (muP nu ka i.succ) c + 1) := by
  induction i using Fin.cases with
  | zero =>
    obtain ⟨e1, e2⟩ := h.heights0 c
    have := h.nonneg 1
    rw [e1, e2, hv0]
    refine ⟨fun hlt => ⟨rfl, ?_⟩, fun hlt => ?_⟩
    · split_ifs at hlt ⊢ <;> omega
    · exfalso
      split_ifs at hlt <;> omega
  | succ k =>
    obtain ⟨e1, e2⟩ := h.heights k c
    have hm : nu (k.val + 1) ≤ nu (k.val + 2) := h.numono _
    have p1 : 1 ≤ colH (ka k.castSucc) c → c ≤ nu (k.val + 1) := fun hc => h.pos_le k.castSucc hc
    rw [e1, e2, hvs]
    cases hv : vecc k
    · have hc := h.nucov k hv
      have := h.stepC k hv c
      rw [hc]
      refine ⟨fun hlt => ?_, fun hlt => ⟨rfl, ?_⟩⟩
      · exfalso
        split_ifs at hlt <;> omega
      · split_ifs at hlt ⊢ <;> omega
    · obtain ⟨s1, s2, s3⟩ := h.stepV k hv c
      refine ⟨fun hlt => ⟨rfl, ?_⟩, fun hlt => ?_⟩
      · by_cases hx : colH (ka k.castSucc) c < colH (ka k.succ) c
        · have := s3 hx
          split_ifs at hlt ⊢ <;> omega
        · split_ifs at hlt ⊢ <;> omega
      · exfalso
        split_ifs at hlt <;> omega

/- English proof (translation)
Proceed by induction on `t using Fin.cases with`. Consider the case `zero`. Rewrite using `[H0, h.nu0]`. Use `h.hK` as an intermediate fact. Apply the tactic sequence `split_ifs <;> omega`.

Consider the case `succ i`. Rewrite using `[HS]`. Establish `h1` using `h.nonneg (i.val + 1)`. Establish `h2` using `h.dual1 (c := c) (by omega) i`. Apply the tactic sequence `split_ifs <;> omega`.
-/
private theorem one_lt_colH_muP_of_PH_of_lt_one (h : PH vecc B ka nu) {c : ℤ} (hc : ¬ 1 ≤ c) (t : Fin (N + 1 + 1)) :
    1 < colH (muP nu ka t) c := by
  induction t using Fin.cases with
  | zero =>
    rw [H0, h.nu0]
    have := h.hK
    split_ifs <;> omega
  | succ i =>
    rw [HS]
    have h1 := h.nonneg (i.val + 1)
    have h2 := h.dual1 (c := c) (by omega) i
    split_ifs <;> omega

/- English proof (translation)
Use `⟨fun j hj hlt => (colH_muP_succ_ne_castSucc_iff_vec h LL hv0 hvs c ⟨j, hj⟩).1 hlt, fun j hj hlt => (colH_muP_succ_ne_castSucc_iff_vec h LL hv0 hvs c ⟨j, hj⟩).2 hlt, fun hc => ?_, fun hc j hj => one_lt_colH_muP_of_PH_of_lt_one h hc ⟨j, by omega⟩⟩` and prove the remaining obligations. Establish `e` using `H0 nu ka c`. Rewrite `e` using `[h.nu0]`. Establish `e0 : (⟨0, by omega⟩ : Fin (N + 1 + 1)) = 0` using `Fin.ext (by simp)`. Rewrite using `[e0, e]`.

Apply the tactic sequence `split_ifs <;> omega`.
-/
theorem PH.colOK (h : PH vecc B ka nu) (LL : LiftLetters (Fin (N + 1))) (hv0 : LL.vec 0 = true)
    (hvs : ∀ i : Fin N, LL.vec i.succ = vecc i) (c : ℤ) : ColOK LL (muP nu ka) c := by
  refine ⟨fun j hj hlt => (colH_muP_succ_ne_castSucc_iff_vec h LL hv0 hvs c ⟨j, hj⟩).1 hlt,
    fun j hj hlt => (colH_muP_succ_ne_castSucc_iff_vec h LL hv0 hvs c ⟨j, hj⟩).2 hlt, fun hc => ?_,
    fun hc j hj => one_lt_colH_muP_of_PH_of_lt_one h hc ⟨j, by omega⟩⟩
  have e := H0 nu ka c
  rw [h.nu0] at e
  have e0 : (⟨0, by omega⟩ : Fin (N + 1 + 1)) = 0 := Fin.ext (by simp)
  rw [e0, e]
  split_ifs <;> omega

/- English proof (translation)
Introduce `i i' hii' _ hc`. Apply `hpos i i' hii'` to reduce the goal to its premises. Proceed by induction on `i' using Fin.cases with`. Consider the case `zero => exact absurd hc (h.not_costly_zero c)`. Consider the case `succ k`.

Rewrite using `[hvs]`. Rewrite `hc` using `[h.costly_succ]`. Consider the cases of `hv : vecc k`. Use `(h.stepC k hv c).1` as an intermediate fact. It suffices to derive a contradiction.

Use linear arithmetic over natural numbers and integers. Both sides reduce to the same expression.
-/
theorem PH.posc (h : PH vecc B ka nu) (LL : LiftLetters (Fin (N + 1))) (hvs : ∀ i : Fin N, LL.vec i.succ = vecc i)
    (hpos : ∀ i i' : Fin (N + 1), i < i' → LL.vec i' = true → LL.pos i < LL.pos i') (c : ℤ) :
    ∀ i i' : Fin (N + 1), i < i' → IsUsed (muP nu ka) c i → IsCostly (muP nu ka) c i' → LL.pos i < LL.pos i' := by
  intro i i' hii' _ hc
  apply hpos i i' hii'
  induction i' using Fin.cases with
  | zero => exact absurd hc (h.not_costly_zero c)
  | succ k =>
    rw [hvs]
    rw [h.costly_succ] at hc
    cases hv : vecc k
    · have := (h.stepC k hv c).1
      exfalso
      omega
    · rfl

end Formalism.MainNotions.ColumnSystems.Pf.Col

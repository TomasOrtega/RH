import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TensorRepresentations.InhabCAR
import Mathlib.LinearAlgebra.ExteriorAlgebra.Basis

noncomputable section

open Finset

namespace ReciprocityTheory.ChartRestriction.DS

variable {n : ℕ}

def modeWt (ε : Fin n → Bool) (x : Fin n × Fin n) : Fin n → ℝ :=
  if ε x.1 = true ∧ ε x.2 = false then root x.1 x.2 else 0

def fockBasis (n : ℕ) : Module.Basis (Finset (Fin (n * n))) ℂ (Fock n) :=
  ((Pi.basisFun ℂ (Fin n × Fin n)).reindex finProdFinEquiv).ExteriorAlgebra

def fockWt (ε : Fin n → Bool) (s : Finset (Fin (n * n))) : Fin n → ℝ :=
  ∑ k ∈ s, modeWt ε (finProdFinEquiv.symm k)

section Comm

variable {W : Type*} [AddCommGroup W] [Module ℂ W]

/- English proof (translation)
Establish `e1 : cp a y * cp i x = -(cp i x * cp a y)` using `eq_neg_of_add_eq_zero_left (hC a y i x).1`. Establish `e3 : cm b y * cp i x = (if b = i ∧ y = x then 1 else 0) - cp i x * cm b y` using `eq_sub_of_add_eq (hC b y i x).2.2`. Rewrite using `[mul_assoc, e3, mul_sub, ← mul_assoc (cp a y) (cp i x), e1]`. Apply the tactic sequence `split_ifs <;> simp [mul_assoc, add_comm]`.
-/
private theorem car_mul_mul_commute_add_ite {cp cm : Fin n → Fin n → Module.End ℂ W} (hC : IsCAR cp cm)
    (a b y i x : Fin n) :
    cp a y * cm b y * cp i x =
      cp i x * (cp a y * cm b y) + (if b = i ∧ y = x then cp a y else 0) := by
  have e1 : cp a y * cp i x = -(cp i x * cp a y) := eq_neg_of_add_eq_zero_left (hC a y i x).1
  have e3 : cm b y * cp i x = (if b = i ∧ y = x then 1 else 0) - cp i x * cm b y :=
    eq_sub_of_add_eq (hC b y i x).2.2
  rw [mul_assoc, e3, mul_sub, ← mul_assoc (cp a y) (cp i x), e1]
  split_ifs <;> simp [mul_assoc, add_comm]

/- English proof (translation)
Unfold `sgE`. Distinguish the cases in `hc : ε c = true`. Rewrite using `[if_pos ⟨hc, hc⟩, Finset.sum_mul, Finset.mul_sum]`. Repeatedly rewrite using `[car_mul_mul_commute_add_ite hC]`. Rewrite using `[Finset.sum_add_distrib]`.

Use `congr 1`. Distinguish the cases in `hci : c = i`. Substitute `hci` using the available equality. Simplify using `only [true_and]`. Rewrite using `[Finset.sum_ite_eq']`.

Distinguish the cases in `hx : ε x = false`. Establish `hxc : x ≠ c` using `fun h => by rw [h, hc] at hx; exact Bool.noConfusion hx`. Simplify using `[minusIdx, hx, hc, modeWt, root, Pi.single_apply, hxc]`. Simplify using `[minusIdx, hx, modeWt]`. Simplify using `only [hci, false_and, if_false, Finset.sum_const_zero]`.

Distinguish the cases in `hx : ε i = true ∧ ε x = false`. Establish `hxc : x ≠ c` using `fun h => by rw [h, hc] at hx; exact Bool.noConfusion hx.2`. Simplify using `[modeWt, hx, root, Pi.single_apply, Ne.symm hci, hxc]`. Simplify using `[modeWt, hx]`. Establish `hc' : ε c = false` using `by simpa using hc`.

Rewrite using `[if_neg (fun h => hc h.1), if_pos ⟨hc', hc'⟩, neg_mul, mul_neg, Finset.sum_mul, Finset.mul_sum]`. Repeatedly rewrite using `[car_mul_mul_commute_add_ite hC]`. Rewrite using `[Finset.sum_add_distrib, neg_add]`. Use `congr 1`. Distinguish the cases in `hcx : c = x`.

Substitute `hcx` using the available equality. Simplify using `only [eq_self_iff_true, and_true]`. Rewrite using `[Finset.sum_ite_eq']`. Distinguish the cases in `hi : ε i = true`. Establish `hic : i ≠ c` using `fun h => by rw [h, hc'] at hi; exact Bool.noConfusion hi`.

Simplify using `[plusIdx, hi, hc', modeWt, root, Pi.single_apply, hic]`. Simplify using `[plusIdx, hi, modeWt]`. Simplify using `only [hcx, and_false, if_false, neg_zero, Finset.sum_const_zero]`. Distinguish the cases in `hx : ε i = true ∧ ε x = false`. Establish `hic : i ≠ c` using `fun h => by rw [h, hc'] at hx; exact Bool.noConfusion hx.1`.

Simplify using `[modeWt, hx, root, Pi.single_apply, hic, Ne.symm hcx]`. Simplify using `[modeWt, hx]`.
-/
theorem sg_cp_comm {cp cm : Fin n → Fin n → Module.End ℂ W} (hC : IsCAR cp cm) (ε : Fin n → Bool)
    (c i x : Fin n) :
    sgE ε cp cm c c * cp i x = cp i x * sgE ε cp cm c c + ((modeWt ε (i, x) c : ℝ) : ℂ) • cp i x := by
  unfold sgE
  by_cases hc : ε c = true
  · rw [if_pos ⟨hc, hc⟩, Finset.sum_mul, Finset.mul_sum]
    simp_rw [car_mul_mul_commute_add_ite hC]
    rw [Finset.sum_add_distrib]
    congr 1
    by_cases hci : c = i
    · subst hci
      simp only [true_and]
      rw [Finset.sum_ite_eq']
      by_cases hx : ε x = false
      · have hxc : x ≠ c := fun h => by rw [h, hc] at hx; exact Bool.noConfusion hx
        simp [minusIdx, hx, hc, modeWt, root, Pi.single_apply, hxc]
      · simp [minusIdx, hx, modeWt]
    · simp only [hci, false_and, if_false, Finset.sum_const_zero]
      by_cases hx : ε i = true ∧ ε x = false
      · have hxc : x ≠ c := fun h => by rw [h, hc] at hx; exact Bool.noConfusion hx.2
        simp [modeWt, hx, root, Pi.single_apply, Ne.symm hci, hxc]
      · simp [modeWt, hx]
  · have hc' : ε c = false := by simpa using hc
    rw [if_neg (fun h => hc h.1), if_pos ⟨hc', hc'⟩, neg_mul, mul_neg, Finset.sum_mul, Finset.mul_sum]
    simp_rw [car_mul_mul_commute_add_ite hC]
    rw [Finset.sum_add_distrib, neg_add]
    congr 1
    by_cases hcx : c = x
    · subst hcx
      simp only [eq_self_iff_true, and_true]
      rw [Finset.sum_ite_eq']
      by_cases hi : ε i = true
      · have hic : i ≠ c := fun h => by rw [h, hc'] at hi; exact Bool.noConfusion hi
        simp [plusIdx, hi, hc', modeWt, root, Pi.single_apply, hic]
      · simp [plusIdx, hi, modeWt]
    · simp only [hcx, and_false, if_false, neg_zero, Finset.sum_const_zero]
      by_cases hx : ε i = true ∧ ε x = false
      · have hic : i ≠ c := fun h => by rw [h, hc'] at hx; exact Bool.noConfusion hx.1
        simp [modeWt, hx, root, Pi.single_apply, hic, Ne.symm hcx]
      · simp [modeWt, hx]

end Comm

/- English proof (translation)
Unfold `sgE`. Apply the tactic sequence `split_ifs <;> simp [cmFock, LinearMap.sum_apply, Module.End.mul_apply, CliffordAlgebra.contractLeft_one]`.
-/
theorem sgE_one (ε : Fin n → Bool) (c : Fin n) : sgE ε cpFock cmFock c c (1 : Fock n) = 0 := by
  unfold sgE
  split_ifs <;> simp [cmFock, LinearMap.sum_apply, Module.End.mul_apply, CliffordAlgebra.contractLeft_one]

/- English proof (translation)
Proceed by induction on `l with`. Consider the case `nil => simp [sgE_one]`. Consider the case `cons x l ih`. Take `⟨i, y⟩` from `x`. Establish `h` using `LinearMap.congr_fun (sg_cp_comm isCAR_fock ε c i y) ((l.map fun x => ExteriorAlgebra.ι ℂ (Pi.single x (1 : ℂ))).prod)`.

Simplify using `only [Module.End.mul_apply, LinearMap.add_apply, LinearMap.smul_apply, ih, map_smul] at h`. Simplify using `only [List.map_cons, List.prod_cons, List.sum_cons]`. Rewrite using `[show ExteriorAlgebra.ι ℂ (Pi.single (i, y) (1 : ℂ)) * (l.map fun x => ExteriorAlgebra.ι ℂ (Pi.single x (1 : ℂ))).prod = cpFock i y ((l.map fun x => ExteriorAlgebra.ι ℂ (Pi.single x (1 : ℂ))).prod) from rfl, h, ← add_smul]`. Use `congr 1`. Use `push_cast`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem sg_prod_list (ε : Fin n → Bool) (c : Fin n) (l : List (Fin n × Fin n)) :
    sgE ε cpFock cmFock c c (l.map fun x => ExteriorAlgebra.ι ℂ (Pi.single x (1 : ℂ))).prod =
      (((l.map fun x => modeWt ε x c).sum : ℝ) : ℂ) •
        (l.map fun x => ExteriorAlgebra.ι ℂ (Pi.single x (1 : ℂ))).prod := by
  induction l with
  | nil => simp [sgE_one]
  | cons x l ih =>
    obtain ⟨i, y⟩ := x
    have h := LinearMap.congr_fun (sg_cp_comm isCAR_fock ε c i y)
      ((l.map fun x => ExteriorAlgebra.ι ℂ (Pi.single x (1 : ℂ))).prod)
    simp only [Module.End.mul_apply, LinearMap.add_apply, LinearMap.smul_apply, ih, map_smul] at h
    simp only [List.map_cons, List.prod_cons, List.sum_cons]
    rw [show ExteriorAlgebra.ι ℂ (Pi.single (i, y) (1 : ℂ)) *
        (l.map fun x => ExteriorAlgebra.ι ℂ (Pi.single x (1 : ℂ))).prod =
        cpFock i y ((l.map fun x => ExteriorAlgebra.ι ℂ (Pi.single x (1 : ℂ))).prod) from rfl, h,
      ← add_smul]
    congr 1
    push_cast
    ring

/- English proof (translation)
Establish `hl : (List.ofFn fun i => ExteriorAlgebra.ι ℂ (Pi.single (v i) (1 : ℂ))) = (List.ofFn v).map fun x => ExteriorAlgebra.ι ℂ (Pi.single x (1 : ℂ))`. Rewrite using `[List.map_ofFn]`. Both sides reduce to the same expression. Rewrite using `[ExteriorAlgebra.ιMulti_apply, hl, sg_prod_list, List.map_ofFn, List.sum_ofFn]`. Both sides reduce to the same expression.
-/
theorem sg_ιMulti (ε : Fin n → Bool) (c : Fin n) {k : ℕ} (v : Fin k → Fin n × Fin n) :
    sgE ε cpFock cmFock c c (ExteriorAlgebra.ιMulti ℂ k (fun i => Pi.single (v i) (1 : ℂ))) =
      ((∑ i, modeWt ε (v i) c : ℝ) : ℂ) • ExteriorAlgebra.ιMulti ℂ k (fun i => Pi.single (v i) (1 : ℂ)) := by
  have hl : (List.ofFn fun i => ExteriorAlgebra.ι ℂ (Pi.single (v i) (1 : ℂ))) =
      (List.ofFn v).map fun x => ExteriorAlgebra.ι ℂ (Pi.single x (1 : ℂ)) := by
    rw [List.map_ofFn]
    rfl
  rw [ExteriorAlgebra.ιMulti_apply, hl, sg_prod_list, List.map_ofFn, List.sum_ofFn]
  rfl

/- English proof (translation)
Rewrite using `[← Finset.sum_coe_sort s f]`. Conclude with `Fintype.sum_equiv (s.orderIsoOfFin rfl).toEquiv _ _ (fun i => by simp)`.
-/
private theorem sum_orderEmbOfFin_eq_sum (s : Finset (Fin (n * n))) (f : Fin (n * n) → ℝ) :
    ∑ i : Fin s.card, f (s.orderEmbOfFin rfl i) = ∑ k ∈ s, f k := by
  rw [← Finset.sum_coe_sort s f]
  exact Fintype.sum_equiv (s.orderIsoOfFin rfl).toEquiv _ _ (fun i => by simp)

/- English proof (translation)
Establish `hb : fockBasis n s = ExteriorAlgebra.ιMulti ℂ s.card (fun i => Pi.single (finProdFinEquiv.symm (s.orderEmbOfFin rfl i)) (1 : ℂ))`. Simplify using `[fockBasis, Module.Basis.ExteriorAlgebra, ExteriorAlgebra.ιMulti_family, Set.powersetCard.ofFinEmbEquiv_symm_apply]`. Use `congr 1`. Use function extensionality and compare the values at `i`. Simplify using the standard rewrite rules.

Both sides reduce to the same expression. Rewrite using `[hb, sg_ιMulti]`. Use `congr 2`. Rewrite using `[fockWt, Finset.sum_apply]`. Conclude with `sum_orderEmbOfFin_eq_sum s (fun k => modeWt ε (finProdFinEquiv.symm k) c)`.
-/
theorem fockBasis_wt (ε : Fin n → Bool) (s : Finset (Fin (n * n))) (c : Fin n) :
    sgE ε cpFock cmFock c c (fockBasis n s) = ((fockWt ε s c : ℝ) : ℂ) • fockBasis n s := by
  have hb : fockBasis n s = ExteriorAlgebra.ιMulti ℂ s.card
      (fun i => Pi.single (finProdFinEquiv.symm (s.orderEmbOfFin rfl i)) (1 : ℂ)) := by
    simp [fockBasis, Module.Basis.ExteriorAlgebra, ExteriorAlgebra.ιMulti_family,
      Set.powersetCard.ofFinEmbEquiv_symm_apply]
    congr 1
    funext i
    simp
    rfl
  rw [hb, sg_ιMulti]
  congr 2
  rw [fockWt, Finset.sum_apply]
  exact sum_orderEmbOfFin_eq_sum s (fun k => modeWt ε (finProdFinEquiv.symm k) c)

/- English proof (translation)
Establish `e1 : ∀ (p : Fin n → Prop) [DecidablePred p], (((univ.filter p).card : ℕ) : ℝ) = ∑ b, if p b then (1 : ℝ) else 0`. Introduce `p _`. Rewrite using `[Finset.card_filter]`. Use `push_cast`. Both sides reduce to the same expression.

Simplify using `only [Pi.sub_apply, rhoHol, rhoN, qOf, pOf]`. Rewrite using `[e1, e1, e1, e1]`. Consider the cases of `hc : ε c`. Simplify using `only [Bool.false_eq_true, if_false, Finset.sum_div, ← Finset.sum_sub_distrib, ← Finset.sum_neg_distrib]`. Use `Finset.sum_congr rfl fun b _ => ?_` and prove the remaining obligations.

Break down `lt_trichotomy b c with h | h | h` into its components or cases. Apply the tactic sequence `cases hb : ε b <;> simp [hb, hc, h, lt_asymm h, h.ne, h.ne'] <;> norm_num`. Substitute `h` using the available equality. Simplify using `[hc]`. Apply the tactic sequence `cases hb : ε b <;> simp [hb, hc, h, lt_asymm h, h.ne, h.ne'] <;> norm_num`.

Simplify using `only [if_true, Finset.sum_div, ← Finset.sum_sub_distrib, ← Finset.sum_neg_distrib]`. Use `Finset.sum_congr rfl fun b _ => ?_` and prove the remaining obligations. Break down `lt_trichotomy b c with h | h | h` into its components or cases. Apply the tactic sequence `cases hb : ε b <;> simp [hb, hc, h, lt_asymm h, h.ne, h.ne'] <;> norm_num`. Substitute `h` using the available equality.

Simplify using `[hc]`. Apply the tactic sequence `cases hb : ε b <;> simp [hb, hc, h, lt_asymm h, h.ne, h.ne'] <;> norm_num`.
-/
theorem cfa_rho_coord (ε : Fin n → Bool) (c : Fin n) :
    (rhoHol ε - rhoN ε) c = ∑ b, ((if ε c = true ∧ ε b = false ∧ b < c then (1 : ℝ) else 0) -
      (if ε b = true ∧ ε c = false ∧ c < b then (1 : ℝ) else 0)) := by
  have e1 : ∀ (p : Fin n → Prop) [DecidablePred p],
      (((univ.filter p).card : ℕ) : ℝ) = ∑ b, if p b then (1 : ℝ) else 0 := by
    intro p _
    rw [Finset.card_filter]
    push_cast
    rfl
  simp only [Pi.sub_apply, rhoHol, rhoN, qOf, pOf]
  rw [e1, e1, e1, e1]
  cases hc : ε c
  · simp only [Bool.false_eq_true, if_false, Finset.sum_div, ← Finset.sum_sub_distrib,
      ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun b _ => ?_
    rcases lt_trichotomy b c with h | h | h
    · cases hb : ε b <;> simp [hb, hc, h, lt_asymm h, h.ne, h.ne'] <;> norm_num
    · subst h; simp [hc]
    · cases hb : ε b <;> simp [hb, hc, h, lt_asymm h, h.ne, h.ne'] <;> norm_num
  · simp only [if_true, Finset.sum_div, ← Finset.sum_sub_distrib, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun b _ => ?_
    rcases lt_trichotomy b c with h | h | h
    · cases hb : ε b <;> simp [hb, hc, h, lt_asymm h, h.ne, h.ne'] <;> norm_num
    · subst h; simp [hc]
    · cases hb : ε b <;> simp [hb, hc, h, lt_asymm h, h.ne, h.ne'] <;> norm_num

def cfaM (ε : Fin n → Bool) (lam : Fin n → ℝ) (x : Fin n × Fin n) : ℝ :=
  (if ε x.1 = true ∧ ε x.2 = false ∧ x.2 < x.1 then lam x.1 else 0) -
    (if ε x.1 = true ∧ ε x.2 = false ∧ x.2 < x.1 then lam x.2 else 0)

/- English proof (translation)
Establish `h1 : dot (rhoHol ε - rhoN ε) lam = ∑ x : Fin n × Fin n, cfaM ε lam x`. Simplify using `only [dot, cfa_rho_coord, cfaM, Fintype.sum_prod_type, Finset.sum_mul, sub_mul, Finset.sum_sub_distrib, ite_mul, one_mul, zero_mul]`. Use `congr 1`. Conclude with `Finset.sum_comm`. Establish `hroot : ∀ x : Fin n × Fin n, dot (modeWt ε x) lam = if ε x.1 = true ∧ ε x.2 = false then lam x.1 - lam x.2 else 0`.

Introduce `x`. Unfold `modeWt`. Use `split_ifs`. Simplify using `[dot, root, sub_mul, Finset.sum_sub_distrib, Pi.single_apply]`. Simplify using `[dot]`.

Establish `h2 : ∀ x, cfaM ε lam x ≤ 0 ∧ cfaM ε lam x ≤ dot (modeWt ε x) lam`. Introduce `x`. Rewrite using `[hroot]`. Unfold `cfaM`. Distinguish the cases in `hx : ε x.1 = true ∧ ε x.2 = false`.

Distinguish the cases in `hlt : x.2 < x.1`. Use `hlam hlt` as an intermediate fact. Establish `hp : ε x.1 = true ∧ ε x.2 = false ∧ x.2 < x.1` using `⟨hx.1, hx.2, hlt⟩`. Rewrite using `[if_pos hp, if_pos hp, if_pos hx]`. Apply the tactic sequence `constructor <;> linarith`.

Use `hlam.antitone (not_lt.1 hlt)` as an intermediate fact. Establish `hn : ¬ (ε x.1 = true ∧ ε x.2 = false ∧ x.2 < x.1)` using `fun h => hlt h.2.2`. Rewrite using `[if_neg hn, if_neg hn, if_pos hx, sub_self]`. Apply the tactic sequence `constructor <;> linarith`. Establish `: ¬ (ε x.1 = true ∧ ε x.2 = false ∧ x.2 < x.1)` using `fun h => hx ⟨h.1, h.2.1⟩`.

Simplify using `[hx, this]`. Establish `h3 : dot (fockWt ε s) lam = ∑ k ∈ s, dot (modeWt ε (finProdFinEquiv.symm k)) lam`. Simplify using `only [dot, fockWt, Finset.sum_apply, Finset.sum_mul]`. Conclude with `Finset.sum_comm`. Rewrite using `[h1, h3, ← Equiv.sum_comp finProdFinEquiv.symm (cfaM ε lam)]`.

Combine the equalities or inequalities in the displayed calculation. Rewrite using `[← Finset.sum_sdiff (Finset.subset_univ s)]`. Use `Finset.sum_nonpos (s := univ \ s) fun k _ => (h2 (finProdFinEquiv.symm k)).1` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion. Use `_ ≤ _ := Finset.sum_le_sum fun k _ => (h2 _).2`.
-/
theorem fockWt_dot_ge (ε : Fin n → Bool) {lam : Fin n → ℝ} (hlam : StrictAnti lam)
    (s : Finset (Fin (n * n))) : dot (rhoHol ε - rhoN ε) lam ≤ dot (fockWt ε s) lam := by
  have h1 : dot (rhoHol ε - rhoN ε) lam = ∑ x : Fin n × Fin n, cfaM ε lam x := by
    simp only [dot, cfa_rho_coord, cfaM, Fintype.sum_prod_type, Finset.sum_mul, sub_mul,
      Finset.sum_sub_distrib, ite_mul, one_mul, zero_mul]
    congr 1
    exact Finset.sum_comm
  have hroot : ∀ x : Fin n × Fin n, dot (modeWt ε x) lam =
      if ε x.1 = true ∧ ε x.2 = false then lam x.1 - lam x.2 else 0 := by
    intro x
    unfold modeWt
    split_ifs
    · simp [dot, root, sub_mul, Finset.sum_sub_distrib, Pi.single_apply]
    · simp [dot]
  have h2 : ∀ x, cfaM ε lam x ≤ 0 ∧ cfaM ε lam x ≤ dot (modeWt ε x) lam := by
    intro x
    rw [hroot]
    unfold cfaM
    by_cases hx : ε x.1 = true ∧ ε x.2 = false
    · by_cases hlt : x.2 < x.1
      · have := hlam hlt
        have hp : ε x.1 = true ∧ ε x.2 = false ∧ x.2 < x.1 := ⟨hx.1, hx.2, hlt⟩
        rw [if_pos hp, if_pos hp, if_pos hx]
        constructor <;> linarith
      · have := hlam.antitone (not_lt.1 hlt)
        have hn : ¬ (ε x.1 = true ∧ ε x.2 = false ∧ x.2 < x.1) := fun h => hlt h.2.2
        rw [if_neg hn, if_neg hn, if_pos hx, sub_self]
        constructor <;> linarith
    · have : ¬ (ε x.1 = true ∧ ε x.2 = false ∧ x.2 < x.1) := fun h => hx ⟨h.1, h.2.1⟩
      simp [hx, this]
  have h3 : dot (fockWt ε s) lam = ∑ k ∈ s, dot (modeWt ε (finProdFinEquiv.symm k)) lam := by
    simp only [dot, fockWt, Finset.sum_apply, Finset.sum_mul]
    exact Finset.sum_comm
  rw [h1, h3, ← Equiv.sum_comp finProdFinEquiv.symm (cfaM ε lam)]
  calc ∑ k, cfaM ε lam (finProdFinEquiv.symm k)
      ≤ ∑ k ∈ s, cfaM ε lam (finProdFinEquiv.symm k) := by
        rw [← Finset.sum_sdiff (Finset.subset_univ s)]
        have := Finset.sum_nonpos (s := univ \ s) fun k _ => (h2 (finProdFinEquiv.symm k)).1
        linarith
    _ ≤ _ := Finset.sum_le_sum fun k _ => (h2 _).2

end ReciprocityTheory.ChartRestriction.DS

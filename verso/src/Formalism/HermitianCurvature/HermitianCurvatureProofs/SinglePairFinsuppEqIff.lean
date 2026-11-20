import Formalism.HermitianCurvature.HermitianCurvatureProofs.CapRWordsOfParts
import Formalism.HermitianCurvature.HermitianCurvatureProofs.ActualAdjointnessFromHermitian
import Formalism.HermitianCurvature.HermitianCurvatureProofs.RegularisedPairingViaPhase

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt NumberField Matrix
open scoped ContDiff

namespace Formalism.FourierDecayAlt.P.CutMP.SmoothTransferRegularity

noncomputable section

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

namespace CapWP

/- English proof (translation)
Proceed by induction on `l with`. Consider the case `nil => simp`. Consider the case `cons a l ih => simp [List.flatMap_cons, List.sum_append, ih]`.
-/
theorem sum_flatMap' {α β M : Type*} [AddCommMonoid M] (l : List α) (f : α → List β) (φ : β → M) :
    ((l.flatMap f).map φ).sum = (l.map fun a => ((f a).map φ).sum).sum := by
  induction l with
  | nil => simp
  | cons a l ih => simp [List.flatMap_cons, List.sum_append, ih]

/- English proof (translation)
Proceed by induction on `l with`. Consider the case `nil => simp`. Consider the case `cons a l ih => by_cases h : p a <;> simp [h, ih]`.
-/
theorem sum_filter' {α M : Type*} [AddCommMonoid M] (l : List α) (p : α → Bool) (φ : α → M) :
    ((l.filter p).map φ).sum = (l.map fun a => if p a then φ a else 0).sum := by
  induction l with
  | nil => simp
  | cons a l ih => by_cases h : p a <;> simp [h, ih]

/- English proof (translation)
Proceed by induction on `l with`. Consider the case `nil => simp`. Consider the case `cons a l ih => simp [Finset.sum_add_distrib, ih]`.
-/
theorem finset_sum_list {ι α M : Type*} [AddCommMonoid M] (s : Finset ι) (l : List α) (F : ι → α → M) :
    ∑ i ∈ s, (l.map (F i)).sum = (l.map fun a => ∑ i ∈ s, F i a).sum := by
  induction l with
  | nil => simp
  | cons a l ih => simp [Finset.sum_add_distrib, ih]

/- English proof (translation)
Conclude with `Finset.sum_map_toList s F`.
-/
theorem sum_toList_map {ι M : Type*} [AddCommMonoid M] (s : Finset ι) (F : ι → M) :
    (s.toList.map F).sum = ∑ i ∈ s, F i := by
  exact Finset.sum_map_toList s F

/- English proof (translation)
Proceed by induction on `l with`. Consider the case `nil => simp`. Consider the case `cons a l ih => simp [MvPolynomial.coeff_add, ih]`.
-/
theorem coeff_listSum {σ' : Type*} {α : Type*} (m : σ' →₀ ℕ) (l : List α) (F : α → MvPolynomial σ' ℂ) :
    MvPolynomial.coeff m ((l.map F).sum) = (l.map fun a => MvPolynomial.coeff m (F a)).sum := by
  induction l with
  | nil => simp
  | cons a l ih => simp [MvPolynomial.coeff_add, ih]

/- English proof (translation)
Proceed by induction on `l with`. Consider the case `nil => simp`. Consider the case `cons a l ih => simp [ih]`.
-/
theorem eval_listSum {σ' : Type*} {α : Type*} (x : σ' → ℂ) (l : List α) (F : α → MvPolynomial σ' ℂ) :
    MvPolynomial.eval x ((l.map F).sum) = (l.map fun a => MvPolynomial.eval x (F a)).sum := by
  induction l with
  | nil => simp
  | cons a l ih => simp [ih]

/- English proof (translation)
Break down `h.lt_or_eq with h | h` into its components or cases. Rewrite using `[Polynomial.coeff_eq_zero_of_natDegree_lt h, Polynomial.coeff_eq_zero_of_natDegree_lt (by rwa [Polynomial.natDegree_taylor])]`. Substitute `h` using the available equality. Use `Polynomial.leadingCoeff_taylor c p` as an intermediate fact. Rewrite `this` using `[Polynomial.leadingCoeff, Polynomial.leadingCoeff, Polynomial.natDegree_taylor]`.

Conclude with `this`.
-/
theorem taylor_coeff_top (p : Polynomial ℂ) (c : ℂ) (d : ℕ) (h : p.natDegree ≤ d) :
    (Polynomial.taylor c p).coeff d = p.coeff d := by
  rcases h.lt_or_eq with h | h
  · rw [Polynomial.coeff_eq_zero_of_natDegree_lt h,
      Polynomial.coeff_eq_zero_of_natDegree_lt (by rwa [Polynomial.natDegree_taylor])]
  · subst h
    have := Polynomial.leadingCoeff_taylor c p
    rw [Polynomial.leadingCoeff, Polynomial.leadingCoeff, Polynomial.natDegree_taylor] at this
    exact this

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `h`. Establish `h0` using `DFunLike.congr_fun h 0`. Establish `h1` using `DFunLike.congr_fun h 1`. Simplify using `at h0 h1`.

Conclude with `⟨h0, h1⟩`. Introduce and unpack `⟨rfl, rfl⟩`. Both sides reduce to the same expression.
-/
theorem single_pair_finsupp_eq_iff (d l a b : ℕ) :
    (Finsupp.single (0 : Fin 2) d + Finsupp.single (1 : Fin 2) l =
      Finsupp.single (0 : Fin 2) a + Finsupp.single (1 : Fin 2) b) ↔ d = a ∧ l = b := by
  constructor
  · intro h
    have h0 := DFunLike.congr_fun h 0
    have h1 := DFunLike.congr_fun h 1
    simp at h0 h1
    exact ⟨h0, h1⟩
  · rintro ⟨rfl, rfl⟩; rfl

variable {k r : ℕ}

def Lw {t N : ℕ} (G : Equiv.Perm (Fin t) → List (GenW k r)) (Ys : Fin (N + 1) → ℝ) (lam : Fin (N + 1) → ℂ)
    (c : ℂ) (j : ℕ) : List (ℂ × List (B.Mat k r)) :=
  (Finset.univ : Finset (Equiv.Perm (Fin t))).toList.flatMap fun σ =>
    ((fexp (G σ)).filter fun tm => decide (tm.2.length ≤ j)).map fun tm =>
      (((Equiv.Perm.sign σ : ℤ) : ℂ) * ∑ i, lam i * tm.1.eval ((Ys i : ℂ) + c), tm.2)

section core

variable {t N : ℕ} (G : Equiv.Perm (Fin t) → List (GenW k r)) (Ys : Fin (N + 1) → ℝ) (lam : Fin (N + 1) → ℂ)
  (c : ℂ) (j : ℕ)

/- English proof (translation)
Establish `hd` using `(hD k r (G σ) (hdeg σ) tm htm).1`. Rewrite `hd` using `[hlen σ]`. Use `⟨hd, ?_⟩` and prove the remaining obligations. Rewrite using `[← hYs (Polynomial.taylor c tm.1) (by rw [Polynomial.natDegree_taylor]; omega)]`. Simplify using `only [Polynomial.taylor_eval]`.
-/
theorem coef_interp (hD : FExpDeg) (hlen : ∀ σ, (G σ).length = t) (hdeg : ∀ σ, ∀ gn ∈ G σ, gn.1.natDegree ≤ 1)
    (htN : t ≤ N) (hYs : ∀ q : Polynomial ℂ, q.natDegree ≤ N → ∑ i, lam i * q.eval (Ys i : ℂ) = q.coeff (t - j))
    (σ : Equiv.Perm (Fin t)) (tm : Polynomial ℂ × List (B.Mat k r)) (htm : tm ∈ fexp (G σ)) :
    tm.1.natDegree + tm.2.length ≤ t ∧
      ∑ i, lam i * tm.1.eval ((Ys i : ℂ) + c) = (Polynomial.taylor c tm.1).coeff (t - j) := by
  have hd := (hD k r (G σ) (hdeg σ) tm htm).1
  rw [hlen σ] at hd
  refine ⟨hd, ?_⟩
  rw [← hYs (Polynomial.taylor c tm.1) (by rw [Polynomial.natDegree_taylor]; omega)]
  simp only [Polynomial.taylor_eval]

/- English proof (translation)
Unfold `Lw`. Rewrite using `[sum_flatMap', sum_toList_map]`. Repeatedly rewrite using `[Finset.smul_sum]`. Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_congr rfl fun σ _ => ?_` and prove the remaining obligations.

Rewrite using `[List.map_map, sum_filter']`. Repeatedly rewrite using `[List.smul_sum, List.map_map]`. Rewrite using `[finset_sum_list]`. Use `congr 1`. Use `List.map_congr_left fun tm htm => ?_` and prove the remaining obligations.

Take `⟨hd, hc⟩` from `coef_interp G Ys lam c j hD hlen hdeg htN hYs σ tm htm`. Simplify using `only [Function.comp_apply, smul_smul]`. Rewrite using `[← Finset.sum_smul]`. Establish `e : ∑ i, lam i * (((Equiv.Perm.sign σ : ℤ) : ℂ) * tm.1.eval ((Ys i : ℂ) + c)) = ((Equiv.Perm.sign σ : ℤ) : ℂ) * ∑ i, lam i * tm.1.eval ((Ys i : ℂ) + c)`. Rewrite using `[Finset.mul_sum]`.

Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e]`. Distinguish the cases in `hl : tm.2.length ≤ j`. Simplify using `[hl]`.

Simplify using `only [hl, decide_false, Bool.false_eq_true, if_false]`. Rewrite using `[hc, Polynomial.coeff_eq_zero_of_natDegree_lt (by rw [Polynomial.natDegree_taylor]; omega)]`. Simplify using the standard rewrite rules.
-/
theorem core_eval (hD : FExpDeg) (hlen : ∀ σ, (G σ).length = t)
    (hdeg : ∀ σ, ∀ gn ∈ G σ, gn.1.natDegree ≤ 1) (htN : t ≤ N)
    (hYs : ∀ q : Polynomial ℂ, q.natDegree ≤ N → ∑ i, lam i * q.eval (Ys i : ℂ) = q.coeff (t - j))
    {E : Type*} [AddCommGroup E] [Module ℂ E] (W : List (B.Mat k r) → E) :
    ∑ i, lam i • ∑ σ : Equiv.Perm (Fin t), ((Equiv.Perm.sign σ : ℤ) : ℂ) •
        ((fexp (G σ)).map fun tm => tm.1.eval ((Ys i : ℂ) + c) • W tm.2).sum =
      ((Lw G Ys lam c j).map fun tm => tm.1 • W tm.2).sum := by
  unfold Lw
  rw [sum_flatMap', sum_toList_map]
  simp_rw [Finset.smul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [List.map_map, sum_filter']
  simp_rw [List.smul_sum, List.map_map]
  rw [finset_sum_list]
  congr 1
  refine List.map_congr_left fun tm htm => ?_
  obtain ⟨hd, hc⟩ := coef_interp G Ys lam c j hD hlen hdeg htN hYs σ tm htm
  simp only [Function.comp_apply, smul_smul]
  rw [← Finset.sum_smul]
  have e : ∑ i, lam i * (((Equiv.Perm.sign σ : ℤ) : ℂ) * tm.1.eval ((Ys i : ℂ) + c)) =
      ((Equiv.Perm.sign σ : ℤ) : ℂ) * ∑ i, lam i * tm.1.eval ((Ys i : ℂ) + c) := by
    rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun i _ => ?_; ring
  rw [e]
  by_cases hl : tm.2.length ≤ j
  · simp [hl]
  · simp only [hl, decide_false, Bool.false_eq_true, if_false]
    rw [hc, Polynomial.coeff_eq_zero_of_natDegree_lt (by rw [Polynomial.natDegree_taylor]; omega)]
    simp

def termP (tm : Polynomial ℂ × List (B.Mat k r)) (τ : B.Mat k r → ℂ) (t : ℕ) : MvPolynomial (Fin 2) ℂ :=
  ∑ d ∈ Finset.range (t + 1), MvPolynomial.monomial
    (Finsupp.single (0 : Fin 2) d + Finsupp.single (1 : Fin 2) tm.2.length) (tm.1.coeff d * (tm.2.map τ).prod)

/- English proof (translation)
Unfold `termP`. Rewrite using `[MvPolynomial.coeff_sum]`. Repeatedly rewrite using `[MvPolynomial.coeff_monomial, single_pair_finsupp_eq_iff]`. Distinguish the cases in `hl : tm.2.length = j`. Substitute `hl` using the available equality.

Simplify using `only [and_true]`. Rewrite using `[Finset.sum_ite_eq']`. Simplify using `[show t - tm.2.length < t + 1 by omega]`. Simplify using `[hl]`.
-/
theorem coeff_termPolynomial (tm : Polynomial ℂ × List (B.Mat k r)) (τ : B.Mat k r → ℂ) (hj : j ≤ t) :
    MvPolynomial.coeff (Finsupp.single (0 : Fin 2) (t - j) + Finsupp.single (1 : Fin 2) j) (termP tm τ t) =
      if tm.2.length = j then tm.1.coeff (t - j) * (tm.2.map τ).prod else 0 := by
  unfold termP
  rw [MvPolynomial.coeff_sum]
  simp_rw [MvPolynomial.coeff_monomial, single_pair_finsupp_eq_iff]
  by_cases hl : tm.2.length = j
  · subst hl
    simp only [and_true]
    rw [Finset.sum_ite_eq']
    simp [show t - tm.2.length < t + 1 by omega]
  · simp [hl]

/- English proof (translation)
Unfold `termP`. Rewrite using `[map_sum, Polynomial.eval_eq_sum_range' (show tm.1.natDegree < t + 1 by omega), Finset.sum_mul, Finset.sum_mul]`. Use `Finset.sum_congr rfl fun d _ => ?_` and prove the remaining obligations. Rewrite using `[MvPolynomial.eval_monomial, Finsupp.prod_add_index' (by simp) (by intros; rw [pow_add]), Finsupp.prod_single_index (by simp), Finsupp.prod_single_index (by simp)]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem eval_termPolynomial (tm : Polynomial ℂ × List (B.Mat k r)) (τ : B.Mat k r → ℂ) (ht : tm.1.natDegree ≤ t)
    (x : Fin 2 → ℂ) :
    MvPolynomial.eval x (termP tm τ t) = tm.1.eval (x 0) * x 1 ^ tm.2.length * (tm.2.map τ).prod := by
  unfold termP
  rw [map_sum, Polynomial.eval_eq_sum_range' (show tm.1.natDegree < t + 1 by omega), Finset.sum_mul, Finset.sum_mul]
  refine Finset.sum_congr rfl fun d _ => ?_
  rw [MvPolynomial.eval_monomial, Finsupp.prod_add_index' (by simp) (by intros; rw [pow_add]),
    Finsupp.prod_single_index (by simp), Finsupp.prod_single_index (by simp)]
  ring

/- English proof (translation)
Use `set P : MvPolynomial (Fin 2) ℂ := ∑ σ : Equiv.Perm (Fin t), ((Equiv.Perm.sign σ : ℤ) : MvPolynomial (Fin 2) ℂ) * ((fexp (G σ)).map fun tm => termP tm τ t).sum with hP`. Use `set D : MvPolynomial (Fin 2) ℂ := ∑ σ : Equiv.Perm (Fin t), ((Equiv.Perm.sign σ : ℤ) : MvPolynomial (Fin 2) ℂ) * ∏ i : Fin t, ((if σ i = i then MvPolynomial.X 0 - MvPolynomial.C ((i : ℕ) : ℂ) else 0) + MvPolynomial.X 1 * MvPolynomial.C (M (σ i) i)) with hDdef`. Establish `hPD : P = D`. Apply `MvPolynomial.funext` to reduce the goal to its premises. Introduce `x`.

Rewrite using `[hP, hDdef, map_sum, map_sum]`. Use `Finset.sum_congr rfl fun σ _ => ?_` and prove the remaining obligations. Rewrite using `[map_mul, map_mul, eval_listSum]`. Use `congr 1`. Establish `e1 : ((fexp (G σ)).map fun tm => MvPolynomial.eval x (termP tm τ t)) = (fexp (G σ)).map fun tm => tm.1.eval (x 0) * x 1 ^ tm.2.length * (tm.2.map τ).prod`.

Use `List.map_congr_left fun tm htm => ?_` and prove the remaining obligations. Establish `hd` using `(hD k r (G σ) (hdeg σ) tm htm).1`. Rewrite `hd` using `[hlen σ]`. Conclude with `eval_termPolynomial tm τ (by omega) x`. Rewrite using `[e1, hS k r (G σ) τ (x 0) (x 1), hsym, map_prod]`.

Use `Finset.prod_congr rfl fun i _ => ?_` and prove the remaining obligations. Apply the tactic sequence `by_cases h : σ i = i <;> simp [h]`. Establish `hcoef` using `hDet t M j hj`. Rewrite `hcoef` using `[← hDdef, ← hPD, hP, MvPolynomial.coeff_sum]`. Rewrite using `[← hcoef]`.

Unfold `Lw`. Rewrite using `[sum_flatMap', sum_toList_map]`. Use `Finset.sum_congr rfl fun σ _ => ?_` and prove the remaining obligations. Rewrite using `[← map_intCast (MvPolynomial.C : ℂ →+* MvPolynomial (Fin 2) ℂ), MvPolynomial.coeff_C_mul, coeff_listSum, List.map_map, sum_filter', ← List.sum_map_mul_left]`. Use `congr 1`.

Use `List.map_congr_left fun tm htm => ?_` and prove the remaining obligations. Take `⟨hd, hc⟩` from `coef_interp G Ys lam c j hD hlen hdeg htN hYs σ tm htm`. Simplify using `only [Function.comp_apply]`. Rewrite using `[coeff_termPolynomial j tm τ hj]`. Distinguish the cases in `hl : tm.2.length = j`.

Substitute `hl` using the available equality. Rewrite using `[hc, taylor_coeff_top _ _ _ (by omega)]`. Apply the tactic sequence `split_ifs <;> (try simp_all) <;> ring`. Apply the tactic sequence `by_cases hl' : tm.2.length ≤ j <;> simp [hl, hl']`.
-/
theorem core_symb (hD : FExpDeg) (hS : FExpSymb) (hDet : DetShiftCoeff) (hlen : ∀ σ, (G σ).length = t)
    (hdeg : ∀ σ, ∀ gn ∈ G σ, gn.1.natDegree ≤ 1) (hj : j ≤ t) (htN : t ≤ N)
    (hYs : ∀ q : Polynomial ℂ, q.natDegree ≤ N → ∑ i, lam i * q.eval (Ys i : ℂ) = q.coeff (t - j))
    (τ : B.Mat k r → ℂ) (M : Matrix (Fin t) (Fin t) ℂ)
    (hsym : ∀ (σ : Equiv.Perm (Fin t)) (u s : ℂ),
      ((G σ).map fun gn => gn.1.eval u + s * (gn.2.map fun dX => dX.1 * τ dX.2).sum).prod =
        ∏ i : Fin t, ((if σ i = i then u - ((i : ℕ) : ℂ) else 0) + s * M (σ i) i)) :
    ((Lw G Ys lam c j).map fun tm => if tm.2.length = j then tm.1 * (tm.2.map τ).prod else 0).sum =
      (-1) ^ j * M.charpoly.coeff (t - j) := by
  set P : MvPolynomial (Fin 2) ℂ := ∑ σ : Equiv.Perm (Fin t),
    ((Equiv.Perm.sign σ : ℤ) : MvPolynomial (Fin 2) ℂ) * ((fexp (G σ)).map fun tm => termP tm τ t).sum with hP
  set D : MvPolynomial (Fin 2) ℂ := ∑ σ : Equiv.Perm (Fin t), ((Equiv.Perm.sign σ : ℤ) : MvPolynomial (Fin 2) ℂ) *
      ∏ i : Fin t, ((if σ i = i then MvPolynomial.X 0 - MvPolynomial.C ((i : ℕ) : ℂ) else 0) +
        MvPolynomial.X 1 * MvPolynomial.C (M (σ i) i)) with hDdef
  have hPD : P = D := by
    apply MvPolynomial.funext
    intro x
    rw [hP, hDdef, map_sum, map_sum]
    refine Finset.sum_congr rfl fun σ _ => ?_
    rw [map_mul, map_mul, eval_listSum]
    congr 1
    have e1 : ((fexp (G σ)).map fun tm => MvPolynomial.eval x (termP tm τ t)) =
        (fexp (G σ)).map fun tm => tm.1.eval (x 0) * x 1 ^ tm.2.length * (tm.2.map τ).prod := by
      refine List.map_congr_left fun tm htm => ?_
      have hd := (hD k r (G σ) (hdeg σ) tm htm).1
      rw [hlen σ] at hd
      exact eval_termPolynomial tm τ (by omega) x
    rw [e1, hS k r (G σ) τ (x 0) (x 1), hsym, map_prod]
    refine Finset.prod_congr rfl fun i _ => ?_
    by_cases h : σ i = i <;> simp [h]
  have hcoef := hDet t M j hj
  rw [← hDdef, ← hPD, hP, MvPolynomial.coeff_sum] at hcoef
  rw [← hcoef]
  unfold Lw
  rw [sum_flatMap', sum_toList_map]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [← map_intCast (MvPolynomial.C : ℂ →+* MvPolynomial (Fin 2) ℂ), MvPolynomial.coeff_C_mul, coeff_listSum,
    List.map_map, sum_filter', ← List.sum_map_mul_left]
  congr 1
  refine List.map_congr_left fun tm htm => ?_
  obtain ⟨hd, hc⟩ := coef_interp G Ys lam c j hD hlen hdeg htN hYs σ tm htm
  simp only [Function.comp_apply]
  rw [coeff_termPolynomial j tm τ hj]
  by_cases hl : tm.2.length = j
  · subst hl
    rw [hc, taylor_coeff_top _ _ _ (by omega)]
    split_ifs <;> (try simp_all) <;> ring
  · by_cases hl' : tm.2.length ≤ j <;> simp [hl, hl']

end core

section gens

variable {t : ℕ}

/- English proof (translation)
Unfold `capGen`. Use `split_ifs`. Conclude with `(Polynomial.natDegree_X_sub_C _).le`. Simplify using the standard rewrite rules.
-/
theorem capGen_deg (Zg : Fin t → Fin t → B.Mat k r) (σ : Equiv.Perm (Fin t)) (i : Fin t) :
    (capGen Zg σ i).1.natDegree ≤ 1 := by
  unfold capGen
  split_ifs
  · exact (Polynomial.natDegree_X_sub_C _).le
  · simp

/- English proof (translation)
Simplify using `[capGens]`.
-/
theorem capGens_len (Zg : Fin t → Fin t → B.Mat k r) (σ : Equiv.Perm (Fin t)) : (capGens Zg σ).length = t := by
  simp [capGens]

/- English proof (translation)
Introduce `gn hgn`. Take `⟨i, rfl⟩` from `List.mem_ofFn.1 hgn`. Conclude with `capGen_deg Zg σ i`.
-/
theorem capGens_deg (Zg : Fin t → Fin t → B.Mat k r) (σ : Equiv.Perm (Fin t)) :
    ∀ gn ∈ capGens Zg σ, gn.1.natDegree ≤ 1 := by
  intro gn hgn
  obtain ⟨i, rfl⟩ := List.mem_ofFn.1 hgn
  exact capGen_deg Zg σ i

/- English proof (translation)
Introduce `gn hgn dX hdX`. Take `⟨i, rfl⟩` from `List.mem_ofFn.1 hgn`. Simplify using `only [capGen, List.mem_cons, List.not_mem_nil, or_false] at hdX`. Break down `hdX with rfl | rfl` into its components or cases. Unfold `B.inLie`.

Conclude with `Formalism.FourierDecayAlt.P.Qx2.hpart1_lie _`. Unfold `B.inLie`. Conclude with `Formalism.FourierDecayAlt.P.Qx2.hpart2_lie _`.
-/
theorem capGens_lie (Zg : Fin t → Fin t → B.Mat k r) (σ : Equiv.Perm (Fin t)) :
    ∀ gn ∈ capGens Zg σ, ∀ dX ∈ gn.2, B.inLie k r dX.2 := by
  intro gn hgn dX hdX
  obtain ⟨i, rfl⟩ := List.mem_ofFn.1 hgn
  simp only [capGen, List.mem_cons, List.not_mem_nil, or_false] at hdX
  rcases hdX with rfl | rfl
  · unfold B.inLie; exact Formalism.FourierDecayAlt.P.Qx2.hpart1_lie _
  · unfold B.inLie; exact Formalism.FourierDecayAlt.P.Qx2.hpart2_lie _

/- English proof (translation)
Rewrite using `[capGens, List.map_ofFn, List.prod_ofFn]`. Use `Finset.prod_congr rfl fun i _ => ?_` and prove the remaining obligations. Simplify using `only [Function.comp_apply, capGen]`. Use `congr 1`. Apply the tactic sequence `split_ifs <;> simp`.

Use `congr 1`. Simplify using `only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero, one_mul]`. Use `conv_rhs => rw [← Formalism.FourierDecayAlt.P.Qx5.hpart_sum (Zg (σ i) i)]`. Rewrite using `[Matrix.mul_add, Matrix.trace_add, Matrix.mul_smul, Matrix.trace_smul, smul_eq_mul]`.
-/
theorem capGens_symb (Zg : Fin t → Fin t → B.Mat k r) (Ξ : B.Mat k r) (σ : Equiv.Perm (Fin t)) (u s : ℂ) :
    ((capGens Zg σ).map fun gn => gn.1.eval u + s * (gn.2.map fun dX => dX.1 * Matrix.trace (Ξ * dX.2)).sum).prod =
      ∏ i : Fin t, ((if σ i = i then u - ((i : ℕ) : ℂ) else 0) + s * Matrix.trace (Ξ * Zg (σ i) i)) := by
  rw [capGens, List.map_ofFn, List.prod_ofFn]
  refine Finset.prod_congr rfl fun i _ => ?_
  simp only [Function.comp_apply, capGen]
  congr 1
  · split_ifs <;> simp
  · congr 1
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero, one_mul]
    conv_rhs => rw [← Formalism.FourierDecayAlt.P.Qx5.hpart_sum (Zg (σ i) i)]
    rw [Matrix.mul_add, Matrix.trace_add, Matrix.mul_smul, Matrix.trace_smul, smul_eq_mul]

/- English proof (translation)
Rewrite using `[List.map_reverse, List.prod_reverse]`. Conclude with `capGens_symb Zg Ξ σ u s`.
-/
theorem capGensRev_symb (Zg : Fin t → Fin t → B.Mat k r) (Ξ : B.Mat k r) (σ : Equiv.Perm (Fin t)) (u s : ℂ) :
    ((capGens Zg σ).reverse.map fun gn =>
        gn.1.eval u + s * (gn.2.map fun dX => dX.1 * Matrix.trace (Ξ * dX.2)).sum).prod =
      ∏ i : Fin t, ((if σ i = i then u - ((i : ℕ) : ℂ) else 0) + s * Matrix.trace (Ξ * Zg (σ i) i)) := by
  rw [List.map_reverse, List.prod_reverse]
  exact capGens_symb Zg Ξ σ u s

end gens

/- English proof (translation)
Simplify using `[Q.mdim]`.
-/
theorem mdim0 (k r : ℕ) : Q.mdim k r 0 = 2 * r + k + 1 := by simp [Q.mdim]

/- English proof (translation)
Establish `e : ((fun a b => Matrix.trace (Ξ * zgCV k r a b)) : Matrix (Fin (Q.mdim k r 0)) (Fin (Q.mdim k r 0)) ℂ) = (Matrix.reindex (finCongr (mdim0 k r)).symm (finCongr (mdim0 k r)).symm Ξ)ᵀ`. Use extensionality with `a b`. Simplify using `only [zgCV, Matrix.trace_mul_single, Matrix.transpose_apply, Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.symm_symm, MulOpposite.op_one, one_smul]`. Use `congr 1`. Rewrite using `[e, Matrix.charpoly_transpose, Matrix.charpoly_reindex]`.
-/
theorem cv_charpoly (Ξ : B.Mat k r) :
    Matrix.charpoly (n := Fin (Q.mdim k r 0)) (fun a b => Matrix.trace (Ξ * zgCV k r a b)) =
      Ξ.charpoly := by
  have e : ((fun a b => Matrix.trace (Ξ * zgCV k r a b)) : Matrix (Fin (Q.mdim k r 0)) (Fin (Q.mdim k r 0)) ℂ) =
      (Matrix.reindex (finCongr (mdim0 k r)).symm (finCongr (mdim0 k r)).symm Ξ)ᵀ := by
    ext a b
    simp only [zgCV, Matrix.trace_mul_single, Matrix.transpose_apply, Matrix.reindex_apply, Matrix.submatrix_apply,
      Equiv.symm_symm, MulOpposite.op_one, one_smul]
    congr 1
  rw [e, Matrix.charpoly_transpose, Matrix.charpoly_reindex]

/- English proof (translation)
Introduce `tm htm`. Take `⟨σ, -, htm⟩` from `List.mem_flatMap.1 htm`. Take `⟨tm', htm', rfl⟩` from `List.mem_map.1 htm`. Take `⟨htm', hl⟩` from `List.mem_filter.1 htm'`. Use `⟨of_decide_eq_true hl, fun X hX => ?_⟩` and prove the remaining obligations.

Take `⟨gn, hgn, d, hdX⟩` from `(hD k r (G σ) (hdeg σ) tm' htm').2 X hX`. Conclude with `hlie σ gn hgn (d, X) hdX`.
-/
theorem mem_Lw {t N : ℕ} {G : Equiv.Perm (Fin t) → List (GenW k r)} {Ys : Fin (N + 1) → ℝ}
    {lam : Fin (N + 1) → ℂ} {c : ℂ} {j : ℕ} (hD : FExpDeg) (hdeg : ∀ σ, ∀ gn ∈ G σ, gn.1.natDegree ≤ 1)
    (hlie : ∀ σ, ∀ gn ∈ G σ, ∀ dX ∈ gn.2, B.inLie k r dX.2) :
    ∀ tm ∈ Lw G Ys lam c j, tm.2.length ≤ j ∧ ∀ X ∈ tm.2, B.inLie k r X := by
  intro tm htm
  obtain ⟨σ, -, htm⟩ := List.mem_flatMap.1 htm
  obtain ⟨tm', htm', rfl⟩ := List.mem_map.1 htm
  obtain ⟨htm', hl⟩ := List.mem_filter.1 htm'
  refine ⟨of_decide_eq_true hl, fun X hX => ?_⟩
  obtain ⟨gn, hgn, d, hdX⟩ := (hD k r (G σ) (hdeg σ) tm' htm').2 X hX
  exact hlie σ gn hgn (d, X) hdX

end CapWP

open CapWP in

/- English proof (translation)
Introduce `_ hR hCV hD hS hDet hI k r j hj1 hjn`. Establish `hmd` using `mdim0 k r`. Take `⟨Ys, lam, hYs⟩` from `hI (2 * r + k + 1) (Q.mdim k r 0 - j) (by omega)`. Use `⟨Ys, lam, Lw (fun σ => capGens (zgCV k r) σ) Ys lam ((((Q.mdim k r 0 : ℕ) : ℂ) - 1) / 2) j, (-1) ^ j, pow_ne_zero _ (by norm_num), mem_Lw hD (fun σ => capGens_deg _ σ) (fun σ => capGens_lie _ σ), ?_, ?_⟩` and prove the remaining obligations. Introduce `E _ _ UU f hf g hgU hgG`.

Establish `hCk : ∀ σ : Equiv.Perm (Fin (Q.mdim k r 0)), B.CkOn ((capGens (zgCV k r) σ).length : ℕ∞) UU f` using `fun σ => by`. Rewrite using `[capGens_len, hmd]`. Conclude with `hf`. Establish `e : ∀ i, Q.CV k r (Ys i : ℂ) f g = ∑ σ : Equiv.Perm (Fin (Q.mdim k r 0)), ((Equiv.Perm.sign σ : ℤ) : ℂ) • ((fexp (capGens (zgCV k r) σ)).map fun tm => tm.1.eval ((Ys i : ℂ) + (((Q.mdim k r 0 : ℕ) : ℂ) - 1) / 2) • B.Rw tm.2 f g).sum`. Introduce `i`.

Rewrite using `[hCV k r E (Ys i : ℂ) f g]`. Use `Finset.sum_congr rfl fun σ _ => ?_` and prove the remaining obligations. Use `congr 1`. Conclude with `hR k r E (capGens (zgCV k r) σ) (Q.uC k r 0 (Ys i : ℂ)) UU f (capGens_lie _ σ) (hCk σ) g hgU hgG`. Repeatedly rewrite using `[e]`.

Conclude with `core_eval (fun σ => capGens (zgCV k r) σ) Ys lam _ j hD (fun σ => capGens_len _ σ) (fun σ => capGens_deg _ σ) (by omega) hYs (fun w => B.Rw w f g)`. Introduce `Ξ _`. Rewrite using `[core_symb (fun σ => capGens (zgCV k r) σ) Ys lam _ j hD hS hDet (fun σ => capGens_len _ σ) (fun σ => capGens_deg _ σ) (by omega) (by omega) hYs (fun X => Matrix.trace (Ξ * X)) (fun a b => Matrix.trace (Ξ * zgCV k r a b)) (fun σ u s => capGens_symb _ Ξ σ u s), cv_charpoly, hmd]`.
-/
theorem capelli_words_holds : CapWordsOfParts := by
  intro _ hR hCV hD hS hDet hI k r j hj1 hjn
  have hmd := mdim0 k r
  obtain ⟨Ys, lam, hYs⟩ := hI (2 * r + k + 1) (Q.mdim k r 0 - j) (by omega)
  refine ⟨Ys, lam, Lw (fun σ => capGens (zgCV k r) σ) Ys lam ((((Q.mdim k r 0 : ℕ) : ℂ) - 1) / 2) j, (-1) ^ j,
    pow_ne_zero _ (by norm_num), mem_Lw hD (fun σ => capGens_deg _ σ) (fun σ => capGens_lie _ σ), ?_, ?_⟩
  · intro E _ _ UU f hf g hgU hgG
    have hCk : ∀ σ : Equiv.Perm (Fin (Q.mdim k r 0)),
        B.CkOn ((capGens (zgCV k r) σ).length : ℕ∞) UU f := fun σ => by
      rw [capGens_len, hmd]; exact hf
    have e : ∀ i, Q.CV k r (Ys i : ℂ) f g = ∑ σ : Equiv.Perm (Fin (Q.mdim k r 0)), ((Equiv.Perm.sign σ : ℤ) : ℂ) •
        ((fexp (capGens (zgCV k r) σ)).map fun tm =>
          tm.1.eval ((Ys i : ℂ) + (((Q.mdim k r 0 : ℕ) : ℂ) - 1) / 2) • B.Rw tm.2 f g).sum := by
      intro i
      rw [hCV k r E (Ys i : ℂ) f g]
      refine Finset.sum_congr rfl fun σ _ => ?_
      congr 1
      exact hR k r E (capGens (zgCV k r) σ) (Q.uC k r 0 (Ys i : ℂ)) UU f (capGens_lie _ σ) (hCk σ) g hgU hgG
    simp_rw [e]
    exact core_eval (fun σ => capGens (zgCV k r) σ) Ys lam _ j hD (fun σ => capGens_len _ σ)
      (fun σ => capGens_deg _ σ) (by omega) hYs (fun w => B.Rw w f g)
  · intro Ξ _
    rw [core_symb (fun σ => capGens (zgCV k r) σ) Ys lam _ j hD hS hDet (fun σ => capGens_len _ σ)
      (fun σ => capGens_deg _ σ) (by omega) (by omega) hYs (fun X => Matrix.trace (Ξ * X))
      (fun a b => Matrix.trace (Ξ * zgCV k r a b)) (fun σ u s => capGens_symb _ Ξ σ u s), cv_charpoly, hmd]

open CapWP in

/- English proof (translation)
Introduce `_ hR hCR hD hS hDet hI k r z' Bs _ j hj1 hjk`. Take `⟨Ys, lam, hYs⟩` from `hI k (k - j) (by omega)`. Use `⟨fun i => (Ys i : ℂ), lam, Lw (fun σ => capGens (zgB Bs) σ) Ys lam 0 j, (-1) ^ j, pow_ne_zero _ (by norm_num), mem_Lw hD (fun σ => capGens_deg _ σ) (fun σ => capGens_lie _ σ), ?_, ?_⟩` and prove the remaining obligations. Introduce `E _ _ UU f hf g hgU hgG`. Establish `hCk : ∀ σ : Equiv.Perm (Fin k), B.CkOn ((capGens (zgB Bs) σ).length : ℕ∞) UU f` using `fun σ => by`.

Rewrite using `[capGens_len]`. Conclude with `Formalism.FourierDecayAlt.P.B5.ckOn_mono (by exact_mod_cast (show k ≤ 2 * r + k + 1 by omega)) hf`. Establish `e : ∀ i, Q.capR k r Bs (Ys i : ℂ) f g = ∑ σ : Equiv.Perm (Fin k), ((Equiv.Perm.sign σ : ℤ) : ℂ) • ((fexp (capGens (zgB Bs) σ)).map fun tm => tm.1.eval ((Ys i : ℂ) + 0) • B.Rw tm.2 f g).sum`. Introduce `i`. Rewrite using `[hCR k r E Bs (Ys i : ℂ) f g]`.

Use `Finset.sum_congr rfl fun σ _ => ?_` and prove the remaining obligations. Use `congr 1`. Simplify using `only [add_zero]`. Conclude with `hR k r E (capGens (zgB Bs) σ) (Ys i : ℂ) UU f (capGens_lie _ σ) (hCk σ) g hgU hgG`. Repeatedly rewrite using `[e]`.

Conclude with `core_eval (fun σ => capGens (zgB Bs) σ) Ys lam 0 j hD (fun σ => capGens_len _ σ) (fun σ => capGens_deg _ σ) le_rfl hYs (fun w => B.Rw w f g)`. Introduce `Ξ _`. Conclude with `core_symb (fun σ => capGens (zgB Bs) σ) Ys lam 0 j hD hS hDet (fun σ => capGens_len _ σ) (fun σ => capGens_deg _ σ) (by omega) le_rfl hYs (fun X => Matrix.trace (Ξ * X)) (fun a b => Matrix.trace (Ξ * zgB Bs a b)) (fun σ u s => capGens_symb _ Ξ σ u s)`.
-/
theorem right_capelli_words_holds : CapRWordsOfParts := by
  intro _ hR hCR hD hS hDet hI k r z' Bs _ j hj1 hjk
  obtain ⟨Ys, lam, hYs⟩ := hI k (k - j) (by omega)
  refine ⟨fun i => (Ys i : ℂ), lam, Lw (fun σ => capGens (zgB Bs) σ) Ys lam 0 j, (-1) ^ j,
    pow_ne_zero _ (by norm_num), mem_Lw hD (fun σ => capGens_deg _ σ) (fun σ => capGens_lie _ σ), ?_, ?_⟩
  · intro E _ _ UU f hf g hgU hgG
    have hCk : ∀ σ : Equiv.Perm (Fin k), B.CkOn ((capGens (zgB Bs) σ).length : ℕ∞) UU f := fun σ => by
      rw [capGens_len]
      exact Formalism.FourierDecayAlt.P.B5.ckOn_mono (by exact_mod_cast (show k ≤ 2 * r + k + 1 by omega)) hf
    have e : ∀ i, Q.capR k r Bs (Ys i : ℂ) f g = ∑ σ : Equiv.Perm (Fin k), ((Equiv.Perm.sign σ : ℤ) : ℂ) •
        ((fexp (capGens (zgB Bs) σ)).map fun tm => tm.1.eval ((Ys i : ℂ) + 0) • B.Rw tm.2 f g).sum := by
      intro i
      rw [hCR k r E Bs (Ys i : ℂ) f g]
      refine Finset.sum_congr rfl fun σ _ => ?_
      congr 1
      simp only [add_zero]
      exact hR k r E (capGens (zgB Bs) σ) (Ys i : ℂ) UU f (capGens_lie _ σ) (hCk σ) g hgU hgG
    simp_rw [e]
    exact core_eval (fun σ => capGens (zgB Bs) σ) Ys lam 0 j hD (fun σ => capGens_len _ σ)
      (fun σ => capGens_deg _ σ) le_rfl hYs (fun w => B.Rw w f g)
  · intro Ξ _
    exact core_symb (fun σ => capGens (zgB Bs) σ) Ys lam 0 j hD hS hDet (fun σ => capGens_len _ σ)
      (fun σ => capGens_deg _ σ) (by omega) le_rfl hYs (fun X => Matrix.trace (Ξ * X))
      (fun a b => Matrix.trace (Ξ * zgB Bs a b)) (fun σ u s => capGens_symb _ Ξ σ u s)

open CapWP in

/- English proof (translation)
Introduce `_ hL hCL hD hS hDet hI k r z Bs _ j hj1 hjk`. Take `⟨Ys, lam, hYs⟩` from `hI k (k - j) (by omega)`. Establish `hlen : ∀ σ : Equiv.Perm (Fin k), (capGens (zgB Bs) σ).reverse.length = k` using `fun σ => by`. Rewrite using `[List.length_reverse, capGens_len]`. Establish `hdeg : ∀ σ : Equiv.Perm (Fin k), ∀ gn ∈ (capGens (zgB Bs) σ).reverse, gn.1.natDegree ≤ 1` using `fun σ gn hgn => capGens_deg _ σ gn (List.mem_reverse.1 hgn)`.

Establish `hlie : ∀ σ : Equiv.Perm (Fin k), ∀ gn ∈ (capGens (zgB Bs) σ).reverse, ∀ dX ∈ gn.2, B.inLie k r dX.2` using `fun σ gn hgn => capGens_lie _ σ gn (List.mem_reverse.1 hgn)`. Use `⟨fun i => (Ys i : ℂ), lam, Lw (fun σ => (capGens (zgB Bs) σ).reverse) Ys lam 0 j, (-1) ^ j, pow_ne_zero _ (by norm_num), mem_Lw hD hdeg hlie, ?_, ?_⟩` and prove the remaining obligations. Introduce `E _ _ UU f hf g hgU hgG`. Establish `hCk : ∀ σ : Equiv.Perm (Fin k), B.CkOn ((capGens (zgB Bs) σ).reverse.length : ℕ∞) UU f` using `fun σ => by`. Rewrite using `[hlen]`.

Conclude with `Formalism.FourierDecayAlt.P.B5.ckOn_mono (by exact_mod_cast (show k ≤ 2 * r + k + 1 by omega)) hf`. Establish `e : ∀ i, Q.capLft k r Bs (Ys i : ℂ) f g = ∑ σ : Equiv.Perm (Fin k), ((Equiv.Perm.sign σ : ℤ) : ℂ) • ((fexp (capGens (zgB Bs) σ).reverse).map fun tm => tm.1.eval ((Ys i : ℂ) + 0) • tm.2.foldr Q.LdV f g).sum`. Introduce `i`. Rewrite using `[hCL k r E Bs (Ys i : ℂ) f g]`. Use `Finset.sum_congr rfl fun σ _ => ?_` and prove the remaining obligations.

Use `congr 1`. Simplify using `only [add_zero]`. Conclude with `hL k r E (capGens (zgB Bs) σ).reverse (Ys i : ℂ) UU f (hlie σ) (hCk σ) g hgU hgG`. Repeatedly rewrite using `[e]`. Conclude with `core_eval (fun σ => (capGens (zgB Bs) σ).reverse) Ys lam 0 j hD hlen hdeg le_rfl hYs (fun w => w.foldr Q.LdV f g)`.

Introduce `Ξ _`. Conclude with `core_symb (fun σ => (capGens (zgB Bs) σ).reverse) Ys lam 0 j hD hS hDet hlen hdeg (by omega) le_rfl hYs (fun X => Matrix.trace (Ξ * X)) (fun a b => Matrix.trace (Ξ * zgB Bs a b)) (fun σ u s => capGensRev_symb _ Ξ σ u s)`.
-/
theorem left_capelli_words_holds : CapLWordsOfParts := by
  intro _ hL hCL hD hS hDet hI k r z Bs _ j hj1 hjk
  obtain ⟨Ys, lam, hYs⟩ := hI k (k - j) (by omega)
  have hlen : ∀ σ : Equiv.Perm (Fin k), (capGens (zgB Bs) σ).reverse.length = k := fun σ => by
    rw [List.length_reverse, capGens_len]
  have hdeg : ∀ σ : Equiv.Perm (Fin k), ∀ gn ∈ (capGens (zgB Bs) σ).reverse, gn.1.natDegree ≤ 1 :=
    fun σ gn hgn => capGens_deg _ σ gn (List.mem_reverse.1 hgn)
  have hlie : ∀ σ : Equiv.Perm (Fin k), ∀ gn ∈ (capGens (zgB Bs) σ).reverse, ∀ dX ∈ gn.2, B.inLie k r dX.2 :=
    fun σ gn hgn => capGens_lie _ σ gn (List.mem_reverse.1 hgn)
  refine ⟨fun i => (Ys i : ℂ), lam, Lw (fun σ => (capGens (zgB Bs) σ).reverse) Ys lam 0 j, (-1) ^ j,
    pow_ne_zero _ (by norm_num), mem_Lw hD hdeg hlie, ?_, ?_⟩
  · intro E _ _ UU f hf g hgU hgG
    have hCk : ∀ σ : Equiv.Perm (Fin k), B.CkOn ((capGens (zgB Bs) σ).reverse.length : ℕ∞) UU f := fun σ => by
      rw [hlen]
      exact Formalism.FourierDecayAlt.P.B5.ckOn_mono (by exact_mod_cast (show k ≤ 2 * r + k + 1 by omega)) hf
    have e : ∀ i, Q.capLft k r Bs (Ys i : ℂ) f g = ∑ σ : Equiv.Perm (Fin k), ((Equiv.Perm.sign σ : ℤ) : ℂ) •
        ((fexp (capGens (zgB Bs) σ).reverse).map fun tm =>
          tm.1.eval ((Ys i : ℂ) + 0) • tm.2.foldr Q.LdV f g).sum := by
      intro i
      rw [hCL k r E Bs (Ys i : ℂ) f g]
      refine Finset.sum_congr rfl fun σ _ => ?_
      congr 1
      simp only [add_zero]
      exact hL k r E (capGens (zgB Bs) σ).reverse (Ys i : ℂ) UU f (hlie σ) (hCk σ) g hgU hgG
    simp_rw [e]
    exact core_eval (fun σ => (capGens (zgB Bs) σ).reverse) Ys lam 0 j hD hlen hdeg le_rfl hYs
      (fun w => w.foldr Q.LdV f g)
  · intro Ξ _
    exact core_symb (fun σ => (capGens (zgB Bs) σ).reverse) Ys lam 0 j hD hS hDet hlen hdeg (by omega) le_rfl hYs
      (fun X => Matrix.trace (Ξ * X)) (fun a b => Matrix.trace (Ξ * zgB Bs a b))
      (fun σ u s => capGensRev_symb _ Ξ σ u s)

end

end Formalism.FourierDecayAlt.P.CutMP.SmoothTransferRegularity

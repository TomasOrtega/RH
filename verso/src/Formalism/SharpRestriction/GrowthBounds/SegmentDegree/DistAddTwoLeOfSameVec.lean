import Formalism.SharpRestriction.GrowthBounds.SegmentDegree.FourHundredSixteenLeA
import Formalism.SharpRestriction.GrowthBounds.SegmentDegree.TypicalPathOrdersSmall

noncomputable section

namespace Formalism.MainNotions.SelectionLemmas.Pf.TE

open Formalism.MainNotions.G Formalism.MainNotions.SelectionLemmas Formalism.MainNotions.G.Joints.StandardMonomialSpace Formalism.MainNotions.SelectionLemmas.Pf.T

section Asm

variable {p n' r K : ℕ} [NeZero n'] [NeZero r] [NeZero K] {X : Dat n' r}

omit [NeZero r] in
/- English proof (translation)
Use extensionality with `x`. Prove the components needed by the constructor for the conclusion. Introduce `hx`. Simplify using `only [Finset.mem_image, Finset.mem_univ, true_and]`. Use `⟨((F.letters j).orderIsoOfFin rfl).symm ⟨x, hx⟩, ?_⟩` and prove the remaining obligations.

Simplify using `[segE]`. Introduce `hx`. Simplify using `only [Finset.mem_image, Finset.mem_univ, true_and] at hx`. Take `⟨i, rfl⟩` from `hx`. Conclude with `((F.letters j).orderIsoOfFin rfl i).2`.
-/
theorem letters_eq_image (F : Frames n' r) (j : ℤ) : F.letters j = Finset.univ.image (segE F j) := by
  ext x
  constructor
  · intro hx
    simp only [Finset.mem_image, Finset.mem_univ, true_and]
    refine ⟨((F.letters j).orderIsoOfFin rfl).symm ⟨x, hx⟩, ?_⟩
    simp [segE]
  · intro hx
    simp only [Finset.mem_image, Finset.mem_univ, true_and] at hx
    obtain ⟨i, rfl⟩ := hx
    exact ((F.letters j).orderIsoOfFin rfl i).2

/- English proof (translation)
Establish `hx'` using `(Finset.mem_filter.mp hx).1`. Rewrite `hx'` using `[Finset.mem_Icc]`. Use `show (((F.fr j (r - 1) - x).toNat : ℕ) : ℤ) = F.fr j (r - 1) - x`. Conclude with `Int.toNat_of_nonneg (by omega)`.
-/
theorem dist_cast {F : Frames n' r} {j x : ℤ} (hx : x ∈ F.letters j) : (F.dist j x : ℤ) = F.fr j (r - 1) - x := by
  have hx' := (Finset.mem_filter.mp hx).1
  rw [Finset.mem_Icc] at hx'
  show (((F.fr j (r - 1) - x).toNat : ℕ) : ℤ) = F.fr j (r - 1) - x
  exact Int.toNat_of_nonneg (by omega)

/- English proof (translation)
Establish `hm : segE F j i < segE F j i'`. Unfold `segE`. Conclude with `((F.letters j).orderIsoOfFin rfl).strictMono h` after adjusting the coercions. Establish `hmem : ∀ k : Fin (segN F j), segE F j k ∈ F.letters j` using `fun k => by`. Unfold `segE`.

Conclude with `((F.letters j).orderIsoOfFin rfl k).2`. Establish `h1` using `dist_cast (hmem i)`. Establish `h2` using `dist_cast (hmem i')`. Use linear arithmetic over natural numbers and integers.
-/
theorem dist_lt {F : Frames n' r} {j : ℤ} {i i' : Fin (segN F j)} (h : i < i') :
    F.dist j (segE F j i') + 1 ≤ F.dist j (segE F j i) := by
  have hm : segE F j i < segE F j i' := by
    unfold segE
    exact_mod_cast ((F.letters j).orderIsoOfFin rfl).strictMono h
  have hmem : ∀ k : Fin (segN F j), segE F j k ∈ F.letters j := fun k => by
    unfold segE
    exact ((F.letters j).orderIsoOfFin rfl k).2
  have h1 := dist_cast (hmem i)
  have h2 := dist_cast (hmem i')
  omega

/- English proof (translation)
Establish `hm : segE F j i < segE F j i'`. Unfold `segE`. Conclude with `((F.letters j).orderIsoOfFin rfl).strictMono h` after adjusting the coercions. Establish `hmem : ∀ k : Fin (segN F j), segE F j k ∈ F.letters j` using `fun k => by`. Unfold `segE`.

Conclude with `((F.letters j).orderIsoOfFin rfl k).2`. Establish `h1` using `dist_cast (hmem i)`. Establish `h2` using `dist_cast (hmem i')`. Establish `hv' : decide (Even (segE F j i)) = decide (Even (segE F j i'))` using `hv`. Rewrite `hv'` using `[decide_eq_decide]`.

Establish `h3 : segE F j i + 1 ≠ segE F j i'`. Introduce `he`. Rewrite `hv'` using `[← he, Int.even_add_one]`. The claim follows by propositional logic. Use linear arithmetic over natural numbers and integers.
-/
theorem dist_add_two_le_of_same_vec {F : Frames n' r} {j : ℤ} {i i' : Fin (segN F j)} (h : i < i')
    (hv : (segLL F j).vec i = (segLL F j).vec i') : F.dist j (segE F j i') + 2 ≤ F.dist j (segE F j i) := by
  have hm : segE F j i < segE F j i' := by
    unfold segE
    exact_mod_cast ((F.letters j).orderIsoOfFin rfl).strictMono h
  have hmem : ∀ k : Fin (segN F j), segE F j k ∈ F.letters j := fun k => by
    unfold segE
    exact ((F.letters j).orderIsoOfFin rfl k).2
  have h1 := dist_cast (hmem i)
  have h2 := dist_cast (hmem i')
  have hv' : decide (Even (segE F j i)) = decide (Even (segE F j i')) := hv
  rw [decide_eq_decide] at hv'
  have h3 : segE F j i + 1 ≠ segE F j i' := by
    intro he
    rw [← he, Int.even_add_one] at hv'
    tauto
  omega

/- English proof (translation)
Unfold `Dat.beS beA`. Rewrite using `[← Finset.sum_filter, letters_eq_image, Finset.filter_image, Finset.sum_image]`. Apply `Finset.sum_congr _ (fun _ _ => rfl)` to reduce the goal to its premises. Use extensionality with `i`. Simplify using `[dict_early hV]`.

Introduce `a _ b _ hab`. Unfold `segE at hab`. Conclude with `((X.F.letters j).orderIsoOfFin rfl).injective (Subtype.ext hab)`.
-/
theorem beS_eq (hV : X.F.Valid X.L₁ X.N₁) (j : ℤ) (b' : ℤ → ℕ) :
    X.beS p K j b' = beA (segN X.F j - r) (fun i => X.Bdeg p K j b' (segE X.F j i)) := by
  unfold Dat.beS beA
  rw [← Finset.sum_filter, letters_eq_image, Finset.filter_image, Finset.sum_image]
  · apply Finset.sum_congr _ (fun _ _ => rfl)
    ext i
    simp [dict_early hV]
  · intro a _ b _ hab
    unfold segE at hab
    exact ((X.F.letters j).orderIsoOfFin rfl).injective (Subtype.ext hab)

omit [NeZero n'] [NeZero r] [NeZero K] in
/- English proof (translation)
Rewrite using `[Fin.prod_univ_eq_prod_range (fun i => if i < r then h i else 1) N, Fin.prod_univ_eq_prod_range h r, Finset.prod_ite, Finset.prod_const_one, mul_one]`. Use `congr 1`. Use extensionality with `i`. Simplify using `only [Finset.mem_filter, Finset.mem_range]`. Use linear arithmetic over natural numbers and integers.
-/
theorem prod_fin_lt (N r : ℕ) (hr : r ≤ N) (h : ℕ → ℝ) :
    ∏ i : Fin N, (if i.val < r then h i.val else 1) = ∏ i : Fin r, h i.val := by
  rw [Fin.prod_univ_eq_prod_range (fun i => if i < r then h i else 1) N,
    Fin.prod_univ_eq_prod_range h r, Finset.prod_ite, Finset.prod_const_one, mul_one]
  congr 1
  ext i
  simp only [Finset.mem_filter, Finset.mem_range]
  omega

/- English proof (translation)
Establish `ha` using `four_hundred_sixteen_le_a hX`. Establish `hab` using `a_big hX`. Establish `hL` using `log_a_ge hX`. Establish `hNs : (N : ℝ) ≤ X.Ns` using `by exact_mod_cast hN`. Establish `hN0 : (0 : ℝ) ≤ N` using `Nat.cast_nonneg N`.

Establish `hapos : 0 < X.a` using `by linarith`. Establish `h1 : 1 + 2 * X.a * (N : ℝ) ≤ X.a ^ 2`. Use polynomial arithmetic with `[mul_le_mul_of_nonneg_left hNs hapos.le, mul_le_mul_of_nonneg_left hab hapos.le, mul_le_mul ha ha (by norm_num) hapos.le]`. Establish `hpos1 : 0 < 1 + 2 * X.a * (N : ℝ)`. Use `mul_nonneg hapos.le hN0` as an intermediate fact.

Combine the linear equalities and inequalities to obtain the conclusion. Establish `hl0 : ell0 N X.a ≤ 2 * Real.log X.a`. Unfold `ell0`. Establish `e : Real.log (X.a ^ 2) = 2 * Real.log X.a`. Rewrite using `[Real.log_pow]`.

Evaluate the numerical expressions. Rewrite using `[← e]`. Conclude with `Real.log_le_log hpos1 h1`. Establish `hl0nn : 0 ≤ ell0 N X.a`. Unfold `ell0`.

Apply `Real.log_nonneg` to reduce the goal to its premises. Use `mul_nonneg hapos.le hN0` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hS : 0 ≤ (X.Ns : ℝ) ^ 2 * Real.log X.a` using `mul_nonneg (sq_nonneg _) (by linarith)`. Establish `hmin : 1088 * ((X.Ns : ℝ) ^ 2 * Real.log X.a) ≤ min X.La ((r + K : ℕ) : ℝ)`.

Apply `le_min` to reduce the goal to its premises. Use `show 1088 * ((X.Ns : ℝ) ^ 2 * Real.log X.a) ≤ X.CLa * (X.Ns : ℝ) ^ 2 * Real.log X.a`. Use polynomial arithmetic with `[mul_le_mul_of_nonneg_right hLa hS]`. Use polynomial arithmetic with `[mul_le_mul_of_nonneg_right hk hS, hX.P1]`. Establish `hN2 : (N : ℝ) ^ 2 ≤ (X.Ns : ℝ) ^ 2` using `by gcongr`.

Establish `hexp : 11 * (N : ℝ) ^ 2 * ell0 N X.a - min X.La ((r + K : ℕ) : ℝ) / 32 ≤ -((X.Ns : ℝ) ^ 2 * Real.log X.a)`. Use polynomial arithmetic with `[mul_le_mul hN2 hl0 hl0nn (sq_nonneg _)]`. Establish `e2 : Real.log (X.a ^ (X.Ns ^ 2)) = (X.Ns : ℝ) ^ 2 * Real.log X.a`. Rewrite using `[Real.log_pow]`. Use `push_cast`.

Expand and normalize the polynomial expressions, which then agree. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[Real.exp_neg, one_div, ← e2, Real.exp_log (pow_pos hapos _)]`.
-/
theorem final_num (hX : X.Hyp p K) (hLa : 1088 ≤ X.CLa) (hk : 1088 ≤ X.Ck) (N : ℕ) (hN : N ≤ X.Ns) :
    Real.exp (11 * (N : ℝ) ^ 2 * ell0 N X.a - min X.La ((r + K : ℕ) : ℝ) / 32) ≤ 1 / X.a ^ (X.Ns ^ 2) := by
  have ha := four_hundred_sixteen_le_a hX
  have hab := a_big hX
  have hL := log_a_ge hX
  have hNs : (N : ℝ) ≤ X.Ns := by exact_mod_cast hN
  have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  have hapos : 0 < X.a := by linarith
  have h1 : 1 + 2 * X.a * (N : ℝ) ≤ X.a ^ 2 := by
    nlinarith [mul_le_mul_of_nonneg_left hNs hapos.le, mul_le_mul_of_nonneg_left hab hapos.le,
      mul_le_mul ha ha (by norm_num) hapos.le]
  have hpos1 : 0 < 1 + 2 * X.a * (N : ℝ) := by
    have := mul_nonneg hapos.le hN0
    linarith
  have hl0 : ell0 N X.a ≤ 2 * Real.log X.a := by
    unfold ell0
    have e : Real.log (X.a ^ 2) = 2 * Real.log X.a := by
      rw [Real.log_pow]
      norm_num
    rw [← e]
    exact Real.log_le_log hpos1 h1
  have hl0nn : 0 ≤ ell0 N X.a := by
    unfold ell0
    apply Real.log_nonneg
    have := mul_nonneg hapos.le hN0
    linarith
  have hS : 0 ≤ (X.Ns : ℝ) ^ 2 * Real.log X.a := mul_nonneg (sq_nonneg _) (by linarith)
  have hmin : 1088 * ((X.Ns : ℝ) ^ 2 * Real.log X.a) ≤ min X.La ((r + K : ℕ) : ℝ) := by
    apply le_min
    · show 1088 * ((X.Ns : ℝ) ^ 2 * Real.log X.a) ≤ X.CLa * (X.Ns : ℝ) ^ 2 * Real.log X.a
      nlinarith [mul_le_mul_of_nonneg_right hLa hS]
    · nlinarith [mul_le_mul_of_nonneg_right hk hS, hX.P1]
  have hN2 : (N : ℝ) ^ 2 ≤ (X.Ns : ℝ) ^ 2 := by gcongr
  have hexp : 11 * (N : ℝ) ^ 2 * ell0 N X.a - min X.La ((r + K : ℕ) : ℝ) / 32 ≤
      -((X.Ns : ℝ) ^ 2 * Real.log X.a) := by
    nlinarith [mul_le_mul hN2 hl0 hl0nn (sq_nonneg _)]
  have e2 : Real.log (X.a ^ (X.Ns ^ 2)) = (X.Ns : ℝ) ^ 2 * Real.log X.a := by
    rw [Real.log_pow]
    push_cast
    ring
  calc Real.exp (11 * (N : ℝ) ^ 2 * ell0 N X.a - min X.La ((r + K : ℕ) : ℝ) / 32)
      ≤ Real.exp (-((X.Ns : ℝ) ^ 2 * Real.log X.a)) := Real.exp_le_exp.mpr hexp
    _ = 1 / X.a ^ (X.Ns ^ 2) := by
      rw [Real.exp_neg, one_div, ← e2, Real.exp_log (pow_pos hapos _)]

/- English proof (translation)
Introduce `p n' r K _ _ _ X hX hLa hk j b hA`. Establish `hV` using `hX.valid`. Take `⟨h41a, -⟩` from `h41 p n' r K X hX hLa hk`. Take `⟨od, hod⟩` from `exists_od hV j`. Establish `hNr` using `r_le_segN hV j`.

Establish `h2r` using `two_r_le hV j`. Establish `hNNs : segN X.F j ≤ X.Ns` using `hX.card j`. Establish `Bs` using `basics hX`. Establish `hN6 : (6 : ℝ) ≤ X.Ns` using `by exact_mod_cast six_le_Ns hX`. Establish `ha` using `a_big hX`.

Establish `ha416` using `four_hundred_sixteen_le_a hX`. Establish `hlog` using `log_a_ge hX`. Establish `hkb` using `k_big hX hk`. Establish `hp0 : (0 : ℝ) < p` using `by linarith [Bs.p1]`. Establish `ha0 : (0 : ℝ) < X.a` using `by linarith`.

Establish `hk5` using `Bs.k5`. Establish `hkdef : Dat.k (r` using `r) K = ((r + K : ℕ) : ℝ) := rfl`. Establish `hPpos : ∀ x : ℤ, (0 : ℝ) < (p : ℝ) ^ (X.F.dist j x + X.Rj p K j)` using `fun x => by positivity`. Establish `hP1 : ∀ x : ℤ, (1 : ℝ) ≤ (p : ℝ) ^ (X.F.dist j x + X.Rj p K j)` using `fun x => one_le_pow₀ Bs.p1.le`. Establish `Bb : ∀ i : Fin (segN X.F j), i.val < segN X.F j - r → (X.a' p K (posOf n' (segE X.F j i)) : ℝ) / (p : ℝ) ^ (X.F.dist j (segE X.F j i) + X.Rj p K j) - 2 * Dat.k (r` using `r) K * (X.Ns : ℝ) ≤ (X.Bdeg p K j (X.restr j b) (segE X.F j i) : ℝ) ∧ (X.Bdeg p K j (X.restr j b) (segE X.F j i) : ℝ) ≤ (X.a' p K (posOf n' (segE X.F j i)) : ℝ) / (p : ℝ) ^ (X.F.dist j (segE X.F j i) + X.Rj p K j) := fun i hi => Bdeg_bounds hX hk h41a j b hA _ (segE_mem X.F j i) …`.

Establish `cb` using `fun i : Fin (segN X.F j) => c_bounds hX h41a j _ (segE_mem X.F j i)`. Establish `Bup : ∀ i : Fin (segN X.F j), i.val < segN X.F j - r → (X.Bdeg p K j (X.restr j b) (segE X.F j i) : ℝ) ≤ 2 * X.a / (p : ℝ) ^ (X.F.dist j (segE X.F j i) + X.Rj p K j)` using `fun i hi => le_trans (Bb i hi).2 (div_le_div_of_nonneg_right (cb i).2.2 (hPpos _).le)`. Establish `hkN : Dat.k (r` using `r) K * 6 ≤ Dat.k (r := r) K * (X.Ns : ℝ) := mul_le_mul_of_nonneg_left hN6 (by linarith)`. Establish `hk2 : Dat.k (r` using `r) K * (X.Ns : ℝ) * 5 ≤ Dat.k (r := r) K ^ 2 * (X.Ns : ℝ) := by`. Establish `: 0 ≤ Dat.k (r` using `r) K * (X.Ns : ℝ) := by positivity`.

Use the polynomial consequences of the given equalities and inequalities. Establish `cge : ∀ i : Fin (segN X.F j), 36 * (Dat.k (r` using `r) K * (X.Ns : ℝ)) ≤ (X.a' p K (posOf n' (segE X.F j i)) : ℝ) / (p : ℝ) ^ (X.F.dist j (segE X.F j i) + X.Rj p K j) := by`. Introduce `i`. Rewrite using `[le_div_iff₀ (hPpos _)]`. Use `le_trans ?_ (cb i).1` and prove the remaining obligations.

Use `mul_le_mul_of_nonneg_right ?_ (hPpos _).le` and prove the remaining obligations. Establish `h1 : 0 ≤ Dat.k (r` using `r) K ^ 2 * (X.Ns : ℝ) := by positivity`. Use polynomial arithmetic with `[Bs.Y1]`. Establish `H : HypT (segN X.F j) (segN X.F j - r) r K (segLL X.F j) (fun i => X.Bdeg p K j (X.restr j b) (segE X.F j i)) od (fun i => X.a / (p : ℝ) ^ (X.F.dist j (segE X.F j i) + X.Rj p K j)) X.a X.La p`. Use `{ hN := by omega r1 := by have := hX.r2; omega a3 := by linarith p13 := hX.p13 H1 := ?_ H2 := ?_ vec_true_of_early := fun i hi => (comb_vec X.F j i).2 (comb_W_even X.F j hV _ (segE_mem X.F j i) ((dict_w hV i).2 hi)) vec_true_of_late := fun i hi => (comb_vec X.F j i).2 (dict_lateV …` and prove the remaining obligations.

Introduce `i hi`. Establish `h1` using `Bb i hi`. Establish `h2` using `cge i`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Use `show ((r + K : ℕ) : ℝ) ≤ (X.Bdeg p K j (X.restr j b) (segE X.F j i) : ℝ)`.

Rewrite using `[← hkdef]`. Use the polynomial consequences of the given equalities and inequalities. Use `show (X.Bdeg p K j (X.restr j b) (segE X.F j i) : ℝ) ≤ 2 * X.a`. Use `le_trans h1.2 (le_trans (div_le_self (Nat.cast_nonneg _) (hP1 _)) (cb i).2.2)` and prove the remaining obligations. Introduce `i i' hii hi' hv show (p : ℝ) ^ 2 / 5 * (X.Bdeg p K j (X.restr j b) (segE X.F j i) : ℝ) ≤ (X.Bdeg p K j (X.restr j b) (segE X.F j i') : ℝ)`.

Establish `hi : i.val < segN X.F j - r` using `lt_trans hii hi'`. Establish `hd` using `dist_add_two_le_of_same_vec hii hv`. Establish `hPP : (p : ℝ) ^ (X.F.dist j (segE X.F j i') + X.Rj p K j) * (p : ℝ) ^ 2 ≤ (p : ℝ) ^ (X.F.dist j (segE X.F j i) + X.Rj p K j)`. Rewrite using `[← pow_add]`. Conclude with `pow_le_pow_right₀ Bs.p1.le (by omega)`.

Use `set P' := (p : ℝ) ^ (X.F.dist j (segE X.F j i') + X.Rj p K j) with hP'`. Establish `hP'0 : 0 < P'` using `hPpos _`. Establish `h1 : (X.Bdeg p K j (X.restr j b) (segE X.F j i) : ℝ) ≤ 2 * X.a / (P' * (p : ℝ) ^ 2)` using `le_trans (Bup i hi) (div_le_div_of_nonneg_left (by linarith) (by positivity) hPP)`. Establish `h2 : (p : ℝ) ^ 2 / 5 * (2 * X.a / (P' * (p : ℝ) ^ 2)) = 2 / 5 * (X.a / P')`. Clear the denominators using the available nonvanishing facts.

Establish `h3 : (p : ℝ) ^ 2 / 5 * (X.Bdeg p K j (X.restr j b) (segE X.F j i) : ℝ) ≤ 2 / 5 * (X.a / P')`. Rewrite using `[← h2]; exact mul_le_mul_of_nonneg_left h1 (by positivity)`. Establish `h4` using `(Bb i' hi').1`. Establish `h5` using `cge i'`. Establish `h6 : 9 / 10 * (X.a / P') ≤ (X.a' p K (posOf n' (segE X.F j i')) : ℝ) / P'`.

Rewrite using `[← mul_div_assoc]`. Conclude with `div_le_div_of_nonneg_right (cb i').2.1 hP'0.le`. Establish `h7 : 0 < X.a / P'` using `div_pos ha0 hP'0`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hr3 : (r : ℝ) ≤ X.Ns`.

Establish `: r ≤ X.Ns` using `by omega`. Conclude with `this` after adjusting the coercions. Establish `hNR : ((segN X.F j : ℕ) : ℝ) ≤ X.Ns` using `by exact_mod_cast hNNs`. Establish `hsq : (X.Ns : ℝ) ≤ (X.Ns : ℝ) ^ 2` using `by nlinarith`. Move the coercions through the operations in `at hkb ⊢`.

Combine the linear equalities and inequalities to obtain the conclusion. Establish `hNR : ((segN X.F j : ℕ) : ℝ) ≤ X.Ns` using `by exact_mod_cast hNNs`. Combine the linear equalities and inequalities to obtain the conclusion. Introduce `i l _ hli hl show (X.Bdeg p K j (X.restr j b) (segE X.F j l) : ℝ) ≤ 4 * (X.a / (p : ℝ) ^ (X.F.dist j (segE X.F j i) + X.Rj p K j)) / (p : ℝ)`. Establish `hd` using `dist_lt hli`.

Establish `hPP : (p : ℝ) ^ (X.F.dist j (segE X.F j i) + X.Rj p K j) * (p : ℝ) ≤ (p : ℝ) ^ (X.F.dist j (segE X.F j l) + X.Rj p K j)`. Rewrite using `[← pow_succ]`. Conclude with `pow_le_pow_right₀ Bs.p1.le (by omega)`. Use `set P' := (p : ℝ) ^ (X.F.dist j (segE X.F j i) + X.Rj p K j) with hP'`. Establish `hP'0 : 0 < P'` using `hPpos _`.

Establish `h1 : (X.Bdeg p K j (X.restr j b) (segE X.F j l) : ℝ) ≤ 2 * X.a / (P' * (p : ℝ))` using `le_trans (Bup l hl) (div_le_div_of_nonneg_left (by linarith) (by positivity) hPP)`. Establish `h2 : 4 * (X.a / P') / (p : ℝ) = 2 * (2 * X.a / (P' * (p : ℝ)))` using `by field_simp; ring`. Rewrite using `[h2]`. Establish `h3 : 0 ≤ 2 * X.a / (P' * (p : ℝ))` using `by positivity`. Combine the linear equalities and inequalities to obtain the conclusion.

Unfold `Dat.La`. Establish `: (0 : ℝ) < X.CLa` using `by linarith`. Establish `h6 : (0 : ℝ) < X.Ns` using `by linarith`. Establish `: (0 : ℝ) < Real.log X.a` using `by linarith`. Check the signs of the components of the expression.

Use `⟨segN X.F j - r, od, H, ?_, ?_, ?_, final_num hX hLa hk _ hNNs⟩` and prove the remaining obligations. Introduce `μ dd`. Prove the components needed by the constructor for the conclusion. Introduce `h`. Use `⟨h.path, fun i hi => h.degs i ((dict_early hV i).2 hi), fun i m hi hm => ?_⟩` and prove the remaining obligations.

Establish `hlt : i.val - (segN X.F j - r) < r` using `by have := i.2; omega`. Use `h.head i ⟨i.val - (segN X.F j - r), hlt⟩ ((dict_tau hV i ⟨i.val - (segN X.F j - r), hlt⟩).2 (by simp only; omega)) m hm` as an intermediate fact. Rewrite using `[this, beS_eq hV]`. Introduce `h`. Use `⟨h.path, fun i hi => h.degs i ((dict_early hV i).1 hi), fun i i' hi m hm => ?_⟩` and prove the remaining obligations.

Establish `hidx` using `(dict_tau hV i i').1 hi`. Use `h.head i m (by omega) (by omega)` as an intermediate fact. Rewrite using `[this, beS_eq hV]`. Introduce `μ hG i hnW`. Establish `hi : r ≤ i.val` using `by rw [dict_w hV] at hnW; omega`.

Take `⟨g1, g2, g3⟩` from `hG i hi`. Establish `hodn` using `oldest_lt_n0 H i hi`. Establish `hoe` using `(hod i hi).1`. Establish `hXi : Xi r K (fun i => X.a / (p : ℝ) ^ (X.F.dist j (segE X.F j i) + X.Rj p K j)) X.La p i = X.La * X.a / ((p : ℝ) * Dat.k (r` using `r) K * (p : ℝ) ^ (X.F.dist j (segE X.F j i) + X.Rj p K j)) := by`. Unfold `Xi`.

Rewrite using `[hkdef]`. Use `(hPpos (segE X.F j i)).ne'` as an intermediate fact. Establish `hk0 : ((r + K : ℕ) : ℝ) ≠ 0` using `by rw [← hkdef]; linarith`. Clear the denominators using the available nonvanishing facts. Use `⟨le_trans ?_ g1, ?_, ?_⟩` and prove the remaining obligations.

Unfold `Dat.thc`. Rewrite using `[← hoe]`. Use `mul_le_mul_of_nonneg_left ?_ (by norm_num)` and prove the remaining obligations. Use `show _ ≤ ((X.Bdeg p K j (X.restr j b) (segE X.F j (od i)) : ℕ) : ℝ)`. Unfold `Dat.Bdeg`.

Distinguish the cases in `hW : X.F.IsW j (segE X.F j (od i))`. Rewrite using `[if_pos hW, if_pos hW]`. Use `Int.self_le_toNat (X.Bw p K j (segE X.F j (od i)) - (X.m0 K : ℤ))` as an intermediate fact. Conclude with `this` after adjusting the coercions. Rewrite using `[if_neg hW, if_neg hW]`.

Introduce `hE`. Use `le_trans (g2 ((comb_vec X.F j i).2 hE)) ?_` and prove the remaining obligations. Unfold `Dat.oc`. Rewrite using `[if_pos hE, hXi, ← hoe]`. Establish `h1` using `Bup (od i) hodn`.

Establish `h2 : (p : ℝ) ^ (-((X.F.dist j (segE X.F j (od i)) : ℤ) + (X.Rj p K j : ℤ))) = 1 / (p : ℝ) ^ (X.F.dist j (segE X.F j (od i)) + X.Rj p K j)`. Rewrite using `[zpow_neg, ← Nat.cast_add, zpow_natCast, one_div]`. Rewrite using `[h2]`. Establish `h3 : 4 * X.a * (1 / (p : ℝ) ^ (X.F.dist j (segE X.F j (od i)) + X.Rj p K j)) = 2 * (2 * X.a / (p : ℝ) ^ (X.F.dist j (segE X.F j (od i)) + X.Rj p K j))` using `by ring`. Rewrite using `[h3]`.

Establish `h1' : ((X.Bdeg p K j (X.restr j b) (segE X.F j (od i)) : ℕ) : ℝ) ≤ 2 * X.a / (p : ℝ) ^ (X.F.dist j (segE X.F j (od i)) + X.Rj p K j)` using `h1`. Combine the linear equalities and inequalities to obtain the conclusion. Introduce `hE`. Establish `hv : (segLL X.F j).vec i = false`. Consider the cases of `hvv : (segLL X.F j).vec i with`.

Consider the case `true => exact absurd ((comb_vec X.F j i).1 hvv) hE`. Consider the case `false => rfl`. Use `le_trans (g3 hv) ?_` and prove the remaining obligations. Unfold `Dat.oc`. Rewrite using `[if_neg hE, hXi, add_zero]`.

Unfold `rkA`. Use `push_cast`. Establish `hpt : ∀ i : Fin (segN X.F j), ((if i.val < segN X.F j - r then (Nat.choose (X.Bdeg p K j (X.restr j b) (segE X.F j i) + (r + K) - 1) (r + K - 1) : ℕ) else 1 : ℕ) : ℝ) = (if r ≤ i.val ∧ i.val < segN X.F j - r then ((Nat.choose (b (segE X.F j i) + (r + K) - 1) (r + K - 1) : ℕ) : ℝ) …`. Introduce `i`. Distinguish the cases in `h1 : i.val < r`.

Establish `hW` using `(dict_w hV i).2 h1`. Rewrite using `[if_pos (by omega), if_neg (by omega), if_pos h1, one_mul]`. Unfold `Dat.Bdeg`. Rewrite using `[if_pos hW, dict_wE hV i h1]`. Distinguish the cases in `h2 : i.val < segN X.F j - r`.

Establish `hW : ¬ X.F.IsW j (segE X.F j i)` using `fun h => h1 ((dict_w hV i).1 h)`. Establish `hlate : segE X.F j i ∈ X.toLate j`. Unfold `Dat.toLate`. Rewrite using `[Finset.mem_filter]`. Conclude with `⟨segE_mem X.F j i, hW⟩`.

Rewrite using `[if_pos h2, if_pos ⟨by omega, h2⟩, if_neg h1, mul_one]`. Unfold `Dat.Bdeg Dat.restr`. Rewrite using `[if_neg hW, if_pos hlate]`. Rewrite using `[if_neg h2, if_neg (by omega), if_neg h1]; simp`. Establish `hL : (∏ i : Fin (segN X.F j), ((if i.val < segN X.F j - r then (Nat.choose (X.Bdeg p K j (X.restr j b) (segE X.F j i) + (r + K) - 1) (r + K - 1) : ℕ) else 1 : ℕ) : ℝ)) = (∏ x ∈ X.F.LLset j, ((Nat.choose (b x + (r + K) - 1) (r + K - 1) : ℕ) : ℝ)) * (∏ i : Fin r, ((Nat.choose ((X.B …`.

Rewrite using `[Finset.prod_congr rfl fun i _ => hpt i, Finset.prod_mul_distrib, prod_fin_lt (segN X.F j) r hNr (fun m => ((Nat.choose ((X.Bw p K j (X.F.fr (j - 1) m) - (X.m0 K : ℤ)).toNat + (r + K) - 1) (r + K - 1) : ℕ) : ℝ))]`. Use `congr 1`. Rewrite using `[LLset_eq_image hV, Finset.prod_image (fun a _ b _ h => (segE_strictMono X.F j).injective h), Finset.prod_filter]`. Conclude with `hL` after adjusting the coercions.
-/
theorem letter_dictionary_bounds (h41 : TopCountLowerBounds 1088) : LetterDictionaryBounds 1088 := by
  classical
  intro p n' r K _ _ _ X hX hLa hk j b hA
  have hV := hX.valid
  obtain ⟨h41a, -⟩ := h41 p n' r K X hX hLa hk
  obtain ⟨od, hod⟩ := exists_od hV j
  have hNr := r_le_segN hV j
  have h2r := two_r_le hV j
  have hNNs : segN X.F j ≤ X.Ns := hX.card j
  have Bs := basics hX
  have hN6 : (6 : ℝ) ≤ X.Ns := by exact_mod_cast six_le_Ns hX
  have ha := a_big hX
  have ha416 := four_hundred_sixteen_le_a hX
  have hlog := log_a_ge hX
  have hkb := k_big hX hk
  have hp0 : (0 : ℝ) < p := by linarith [Bs.p1]
  have ha0 : (0 : ℝ) < X.a := by linarith
  have hk5 := Bs.k5
  have hkdef : Dat.k (r := r) K = ((r + K : ℕ) : ℝ) := rfl
  have hPpos : ∀ x : ℤ, (0 : ℝ) < (p : ℝ) ^ (X.F.dist j x + X.Rj p K j) := fun x => by positivity
  have hP1 : ∀ x : ℤ, (1 : ℝ) ≤ (p : ℝ) ^ (X.F.dist j x + X.Rj p K j) := fun x => one_le_pow₀ Bs.p1.le
  have Bb : ∀ i : Fin (segN X.F j), i.val < segN X.F j - r →
      (X.a' p K (posOf n' (segE X.F j i)) : ℝ) / (p : ℝ) ^ (X.F.dist j (segE X.F j i) + X.Rj p K j) -
          2 * Dat.k (r := r) K * (X.Ns : ℝ) ≤ (X.Bdeg p K j (X.restr j b) (segE X.F j i) : ℝ) ∧
        (X.Bdeg p K j (X.restr j b) (segE X.F j i) : ℝ) ≤
          (X.a' p K (posOf n' (segE X.F j i)) : ℝ) / (p : ℝ) ^ (X.F.dist j (segE X.F j i) + X.Rj p K j) :=
    fun i hi => Bdeg_bounds hX hk h41a j b hA _ (segE_mem X.F j i) ((dict_early hV i).2 hi)
  have cb := fun i : Fin (segN X.F j) => c_bounds hX h41a j _ (segE_mem X.F j i)

  have Bup : ∀ i : Fin (segN X.F j), i.val < segN X.F j - r →
      (X.Bdeg p K j (X.restr j b) (segE X.F j i) : ℝ) ≤
        2 * X.a / (p : ℝ) ^ (X.F.dist j (segE X.F j i) + X.Rj p K j) := fun i hi =>
    le_trans (Bb i hi).2 (div_le_div_of_nonneg_right (cb i).2.2 (hPpos _).le)
  have hkN : Dat.k (r := r) K * 6 ≤ Dat.k (r := r) K * (X.Ns : ℝ) := mul_le_mul_of_nonneg_left hN6 (by linarith)
  have hk2 : Dat.k (r := r) K * (X.Ns : ℝ) * 5 ≤ Dat.k (r := r) K ^ 2 * (X.Ns : ℝ) := by
    have : 0 ≤ Dat.k (r := r) K * (X.Ns : ℝ) := by positivity
    nlinarith

  have cge : ∀ i : Fin (segN X.F j), 36 * (Dat.k (r := r) K * (X.Ns : ℝ)) ≤
      (X.a' p K (posOf n' (segE X.F j i)) : ℝ) / (p : ℝ) ^ (X.F.dist j (segE X.F j i) + X.Rj p K j) := by
    intro i
    rw [le_div_iff₀ (hPpos _)]
    refine le_trans ?_ (cb i).1
    refine mul_le_mul_of_nonneg_right ?_ (hPpos _).le
    have h1 : 0 ≤ Dat.k (r := r) K ^ 2 * (X.Ns : ℝ) := by positivity
    nlinarith [Bs.Y1]
  have H : HypT (segN X.F j) (segN X.F j - r) r K (segLL X.F j)
      (fun i => X.Bdeg p K j (X.restr j b) (segE X.F j i)) od
      (fun i => X.a / (p : ℝ) ^ (X.F.dist j (segE X.F j i) + X.Rj p K j)) X.a X.La p := by
    refine
      { hN := by omega
        r1 := by have := hX.r2; omega
        a3 := by linarith
        p13 := hX.p13
        H1 := ?_
        H2 := ?_
        vec_true_of_early := fun i hi => (comb_vec X.F j i).2 (comb_W_even X.F j hV _ (segE_mem X.F j i) ((dict_w hV i).2 hi))
        vec_true_of_late := fun i hi => (comb_vec X.F j i).2 (dict_lateV hV i hi)
        two_r_le_n0 := h2r
        N_add_r_le_K := by have := hX.NsK; omega
        H4 := ?_
        N_le_a := ?_
        od_lt := fun i hi => (hod i hi).2.1
        od_vec := fun i hi => (hod i hi).2.2.1
        od_card := fun i hi => (hod i hi).2.2.2
        bb_pos := fun i _ => div_pos ha0 (hPpos _)
        bb_le := ?_
        La_pos := ?_ }
    · intro i hi
      have h1 := Bb i hi
      have h2 := cge i
      refine ⟨?_, ?_⟩
      · show ((r + K : ℕ) : ℝ) ≤ (X.Bdeg p K j (X.restr j b) (segE X.F j i) : ℝ)
        rw [← hkdef]
        nlinarith
      · show (X.Bdeg p K j (X.restr j b) (segE X.F j i) : ℝ) ≤ 2 * X.a
        refine le_trans h1.2 (le_trans (div_le_self (Nat.cast_nonneg _) (hP1 _)) (cb i).2.2)
    · intro i i' hii hi' hv
      show (p : ℝ) ^ 2 / 5 * (X.Bdeg p K j (X.restr j b) (segE X.F j i) : ℝ) ≤
        (X.Bdeg p K j (X.restr j b) (segE X.F j i') : ℝ)
      have hi : i.val < segN X.F j - r := lt_trans hii hi'
      have hd := dist_add_two_le_of_same_vec hii hv
      have hPP : (p : ℝ) ^ (X.F.dist j (segE X.F j i') + X.Rj p K j) * (p : ℝ) ^ 2 ≤
          (p : ℝ) ^ (X.F.dist j (segE X.F j i) + X.Rj p K j) := by
        rw [← pow_add]
        exact pow_le_pow_right₀ Bs.p1.le (by omega)
      set P' := (p : ℝ) ^ (X.F.dist j (segE X.F j i') + X.Rj p K j) with hP'
      have hP'0 : 0 < P' := hPpos _
      have h1 : (X.Bdeg p K j (X.restr j b) (segE X.F j i) : ℝ) ≤ 2 * X.a / (P' * (p : ℝ) ^ 2) :=
        le_trans (Bup i hi) (div_le_div_of_nonneg_left (by linarith) (by positivity) hPP)
      have h2 : (p : ℝ) ^ 2 / 5 * (2 * X.a / (P' * (p : ℝ) ^ 2)) = 2 / 5 * (X.a / P') := by
        field_simp
      have h3 : (p : ℝ) ^ 2 / 5 * (X.Bdeg p K j (X.restr j b) (segE X.F j i) : ℝ) ≤ 2 / 5 * (X.a / P') := by
        rw [← h2]; exact mul_le_mul_of_nonneg_left h1 (by positivity)
      have h4 := (Bb i' hi').1
      have h5 := cge i'
      have h6 : 9 / 10 * (X.a / P') ≤ (X.a' p K (posOf n' (segE X.F j i')) : ℝ) / P' := by
        rw [← mul_div_assoc]
        exact div_le_div_of_nonneg_right (cb i').2.1 hP'0.le
      have h7 : 0 < X.a / P' := div_pos ha0 hP'0
      linarith
    · have hr3 : (r : ℝ) ≤ X.Ns := by
        have : r ≤ X.Ns := by omega
        exact_mod_cast this
      have hNR : ((segN X.F j : ℕ) : ℝ) ≤ X.Ns := by exact_mod_cast hNNs
      have hsq : (X.Ns : ℝ) ≤ (X.Ns : ℝ) ^ 2 := by nlinarith
      push_cast at hkb ⊢
      linarith
    · have hNR : ((segN X.F j : ℕ) : ℝ) ≤ X.Ns := by exact_mod_cast hNNs
      linarith
    · intro i l _ hli hl
      show (X.Bdeg p K j (X.restr j b) (segE X.F j l) : ℝ) ≤
        4 * (X.a / (p : ℝ) ^ (X.F.dist j (segE X.F j i) + X.Rj p K j)) / (p : ℝ)
      have hd := dist_lt hli
      have hPP : (p : ℝ) ^ (X.F.dist j (segE X.F j i) + X.Rj p K j) * (p : ℝ) ≤
          (p : ℝ) ^ (X.F.dist j (segE X.F j l) + X.Rj p K j) := by
        rw [← pow_succ]
        exact pow_le_pow_right₀ Bs.p1.le (by omega)
      set P' := (p : ℝ) ^ (X.F.dist j (segE X.F j i) + X.Rj p K j) with hP'
      have hP'0 : 0 < P' := hPpos _
      have h1 : (X.Bdeg p K j (X.restr j b) (segE X.F j l) : ℝ) ≤ 2 * X.a / (P' * (p : ℝ)) :=
        le_trans (Bup l hl) (div_le_div_of_nonneg_left (by linarith) (by positivity) hPP)
      have h2 : 4 * (X.a / P') / (p : ℝ) = 2 * (2 * X.a / (P' * (p : ℝ))) := by field_simp; ring
      rw [h2]
      have h3 : 0 ≤ 2 * X.a / (P' * (p : ℝ)) := by positivity
      linarith
    · unfold Dat.La
      have : (0 : ℝ) < X.CLa := by linarith
      have h6 : (0 : ℝ) < X.Ns := by linarith
      have : (0 : ℝ) < Real.log X.a := by linarith
      positivity
  refine ⟨segN X.F j - r, od, H, ?_, ?_, ?_, final_num hX hLa hk _ hNNs⟩
  · intro μ dd
    constructor
    · intro h
      refine ⟨h.path, fun i hi => h.degs i ((dict_early hV i).2 hi), fun i m hi hm => ?_⟩
      have hlt : i.val - (segN X.F j - r) < r := by have := i.2; omega
      have := h.head i ⟨i.val - (segN X.F j - r), hlt⟩
        ((dict_tau hV i ⟨i.val - (segN X.F j - r), hlt⟩).2 (by simp only; omega)) m hm
      rw [this, beS_eq hV]
    · intro h
      refine ⟨h.path, fun i hi => h.degs i ((dict_early hV i).1 hi), fun i i' hi m hm => ?_⟩
      have hidx := (dict_tau hV i i').1 hi
      have := h.head i m (by omega) (by omega)
      rw [this, beS_eq hV]
  · intro μ hG i hnW
    have hi : r ≤ i.val := by rw [dict_w hV] at hnW; omega
    obtain ⟨g1, g2, g3⟩ := hG i hi
    have hodn := oldest_lt_n0 H i hi
    have hoe := (hod i hi).1
    have hXi : Xi r K (fun i => X.a / (p : ℝ) ^ (X.F.dist j (segE X.F j i) + X.Rj p K j)) X.La p i =
        X.La * X.a / ((p : ℝ) * Dat.k (r := r) K * (p : ℝ) ^ (X.F.dist j (segE X.F j i) + X.Rj p K j)) := by
      unfold Xi
      rw [hkdef]
      have := (hPpos (segE X.F j i)).ne'
      have hk0 : ((r + K : ℕ) : ℝ) ≠ 0 := by rw [← hkdef]; linarith
      field_simp
    refine ⟨le_trans ?_ g1, ?_, ?_⟩
    · unfold Dat.thc
      rw [← hoe]
      refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
      show _ ≤ ((X.Bdeg p K j (X.restr j b) (segE X.F j (od i)) : ℕ) : ℝ)
      unfold Dat.Bdeg
      by_cases hW : X.F.IsW j (segE X.F j (od i))
      · rw [if_pos hW, if_pos hW]
        have := Int.self_le_toNat (X.Bw p K j (segE X.F j (od i)) - (X.m0 K : ℤ))
        exact_mod_cast this
      · rw [if_neg hW, if_neg hW]
    · intro hE
      refine le_trans (g2 ((comb_vec X.F j i).2 hE)) ?_
      unfold Dat.oc
      rw [if_pos hE, hXi, ← hoe]
      have h1 := Bup (od i) hodn
      have h2 : (p : ℝ) ^ (-((X.F.dist j (segE X.F j (od i)) : ℤ) + (X.Rj p K j : ℤ))) =
          1 / (p : ℝ) ^ (X.F.dist j (segE X.F j (od i)) + X.Rj p K j) := by
        rw [zpow_neg, ← Nat.cast_add, zpow_natCast, one_div]
      rw [h2]
      have h3 : 4 * X.a * (1 / (p : ℝ) ^ (X.F.dist j (segE X.F j (od i)) + X.Rj p K j)) =
          2 * (2 * X.a / (p : ℝ) ^ (X.F.dist j (segE X.F j (od i)) + X.Rj p K j)) := by ring
      rw [h3]
      have h1' : ((X.Bdeg p K j (X.restr j b) (segE X.F j (od i)) : ℕ) : ℝ) ≤
          2 * X.a / (p : ℝ) ^ (X.F.dist j (segE X.F j (od i)) + X.Rj p K j) := h1
      linarith
    · intro hE
      have hv : (segLL X.F j).vec i = false := by
        cases hvv : (segLL X.F j).vec i with
        | true => exact absurd ((comb_vec X.F j i).1 hvv) hE
        | false => rfl
      refine le_trans (g3 hv) ?_
      unfold Dat.oc
      rw [if_neg hE, hXi, add_zero]
  · unfold rkA
    push_cast
    have hpt : ∀ i : Fin (segN X.F j),
        ((if i.val < segN X.F j - r then
          (Nat.choose (X.Bdeg p K j (X.restr j b) (segE X.F j i) + (r + K) - 1) (r + K - 1) : ℕ) else 1 : ℕ) : ℝ) =
        (if r ≤ i.val ∧ i.val < segN X.F j - r then
          ((Nat.choose (b (segE X.F j i) + (r + K) - 1) (r + K - 1) : ℕ) : ℝ) else 1) *
        (if i.val < r then ((Nat.choose ((X.Bw p K j (X.F.fr (j - 1) i.val) - (X.m0 K : ℤ)).toNat + (r + K) - 1)
          (r + K - 1) : ℕ) : ℝ) else 1) := by
      intro i
      by_cases h1 : i.val < r
      · have hW := (dict_w hV i).2 h1
        rw [if_pos (by omega), if_neg (by omega), if_pos h1, one_mul]
        unfold Dat.Bdeg
        rw [if_pos hW, dict_wE hV i h1]
      · by_cases h2 : i.val < segN X.F j - r
        · have hW : ¬ X.F.IsW j (segE X.F j i) := fun h => h1 ((dict_w hV i).1 h)
          have hlate : segE X.F j i ∈ X.toLate j := by
            unfold Dat.toLate; rw [Finset.mem_filter]; exact ⟨segE_mem X.F j i, hW⟩
          rw [if_pos h2, if_pos ⟨by omega, h2⟩, if_neg h1, mul_one]
          unfold Dat.Bdeg Dat.restr
          rw [if_neg hW, if_pos hlate]
        · rw [if_neg h2, if_neg (by omega), if_neg h1]; simp
    have hL : (∏ i : Fin (segN X.F j), ((if i.val < segN X.F j - r then
          (Nat.choose (X.Bdeg p K j (X.restr j b) (segE X.F j i) + (r + K) - 1) (r + K - 1) : ℕ) else 1 : ℕ) : ℝ)) =
        (∏ x ∈ X.F.LLset j, ((Nat.choose (b x + (r + K) - 1) (r + K - 1) : ℕ) : ℝ)) *
        (∏ i : Fin r, ((Nat.choose ((X.Bw p K j (X.F.fr (j - 1) i.val) - (X.m0 K : ℤ)).toNat + (r + K) - 1)
          (r + K - 1) : ℕ) : ℝ)) := by
      rw [Finset.prod_congr rfl fun i _ => hpt i, Finset.prod_mul_distrib,
        prod_fin_lt (segN X.F j) r hNr (fun m => ((Nat.choose ((X.Bw p K j (X.F.fr (j - 1) m) - (X.m0 K : ℤ)).toNat +
          (r + K) - 1) (r + K - 1) : ℕ) : ℝ))]
      congr 1
      rw [LLset_eq_image hV, Finset.prod_image (fun a _ b _ h => (segE_strictMono X.F j).injective h),
        Finset.prod_filter]
    exact_mod_cast hL

end Asm

end Formalism.MainNotions.SelectionLemmas.Pf.TE

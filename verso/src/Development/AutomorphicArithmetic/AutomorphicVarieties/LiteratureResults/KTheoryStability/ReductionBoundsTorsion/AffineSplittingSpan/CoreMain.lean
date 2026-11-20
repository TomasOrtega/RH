import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.AffineSplittingSpan.CoreRec

noncomputable section

namespace PositivityTheory.KB.SplitAffineSpectral.NormTraceLemmas

variable {P Q : Type} [Group P] [Group Q]

/- English proof (translation)
Establish `h1` using `congrFun (congrFun h x) ![1, z 0]`. Simplify using `[dv, dc, Fin.sum_univ_two] at h1`. Establish `e1 : (fun _ : Fin 1 => z 0) = z`. Use function extensionality and compare the values at `j`. Rewrite using `[Subsingleton.elim j 0]`.

Establish `e2 : (fun j : Fin 1 => (![1, z 0] : Fin 2 → P) (Fin.succAbove 1 j)) = fun _ => 1`. Use function extensionality and compare the values at `j`. Rewrite using `[Subsingleton.elim j 0]`. Both sides reduce to the same expression. Rewrite `h1` using `[e1, e2]`.

Combine the linear equalities and inequalities to obtain the conclusion.
-/
private theorem bi_apply_eq_apply_const_one_of_dv_eq_zero {a : ℕ} (F : Bi P Q a 1) (h : dv F = 0) (x : Fin a → Q) (z : Fin 1 → P) :
    F x z = F x (fun _ => 1) := by
  have h1 := congrFun (congrFun h x) ![1, z 0]
  simp [dv, dc, Fin.sum_univ_two] at h1
  have e1 : (fun _ : Fin 1 => z 0) = z := by
    funext j
    rw [Subsingleton.elim j 0]
  have e2 : (fun j : Fin 1 => (![1, z 0] : Fin 2 → P) (Fin.succAbove 1 j)) = fun _ => 1 := by
    funext j
    rw [Subsingleton.elim j 0]
    rfl
  rw [e1, e2] at h1
  linarith

/- English proof (translation)
Establish `hc` using `bi_apply_eq_apply_const_one_of_dv_eq_zero F hv`. Unfold `PInv at hF`. Establish `hdc : dc (fun x => F x (fun _ => 1)) = 0`. Use function extensionality and compare the values at `x`. Conclude with `congrFun (congrFun hh x) (fun _ => 1)`.

Use `⟨fun x => F x (fun _ => 1), ?_, ?_⟩` and prove the remaining obligations. Unfold `QC`. Use `⟨?_, hdc⟩` and prove the remaining obligations. Introduce `g x`. Use `show F (fun i => g * x i) (fun _ => 1) = F x (fun _ => 1)`.

Establish `h1` using `hF (s g) x (fun _ => 1)`. Simplify using `only [hs, mul_one] at h1`. Rewrite using `[← h1]`. Conclude with `(hc _ _).symm`. Rewrite using `[hB P Q pr N _ hdc, smul_smul, ← mul_pow]`.

Simplify using `only [neg_one_mul, neg_neg, one_pow, one_smul]`. Use function extensionality and compare the values at `x z`. Conclude with `hc x z`.
-/
private theorem exists_quasiCocycle_eq_dh_zz_of_pInv_dv_dh_zero (hB : SplitB) (pr : P →* Q) (s : Q →* P) (hs : ∀ g, pr (s g) = g) {N : ℕ}
    (F : Bi P Q (N + 2) 1) (hF : PInv pr F) (hv : dv F = 0) (hh : dh F = 0) :
    ∃ b : (Fin (N + 2) → Q) → ℝ, QC b ∧ F = ((-1 : ℝ) ^ (N + 1)) • dh (zz pr b (N + 1) 1) := by
  have hc := bi_apply_eq_apply_const_one_of_dv_eq_zero F hv
  unfold PInv at hF
  have hdc : dc (fun x => F x (fun _ => 1)) = 0 := by
    funext x
    exact congrFun (congrFun hh x) (fun _ => 1)
  refine ⟨fun x => F x (fun _ => 1), ?_, ?_⟩
  · unfold QC
    refine ⟨?_, hdc⟩
    intro g x
    show F (fun i => g * x i) (fun _ => 1) = F x (fun _ => 1)
    have h1 := hF (s g) x (fun _ => 1)
    simp only [hs, mul_one] at h1
    rw [← h1]
    exact (hc _ _).symm
  · rw [hB P Q pr N _ hdc, smul_smul, ← mul_pow]
    simp only [neg_one_mul, neg_neg, one_pow, one_smul]
    funext x z
    exact hc x z

/- English proof (translation)
Introduce `q`. Proceed by induction on `q with`. Consider the case `zero`. Introduce `hq p x hx hv hh`. Take `⟨w, e, hw, hwv, he, rfl⟩` from `hE P Q pr s hs u hu m hm p 0 hq x hx hv hh`.

Establish `hyv : dv (dh e) = 0`. Rewrite using `[← dh_dv]`. Rewrite `hh` using `[dh_add, dh_dh]`. Simplify using `using hh`. Take `⟨b, hb, hyb⟩` from `exists_quasiCocycle_eq_dh_zz_of_pInv_dv_dh_zero hB pr s hs (dh e) (PInv.dh pr he) hyv (dh_dh e)`.

Establish `hb' : QC b` using `hb`. Unfold `QC at hb`. Establish `h2 : dh (zz pr b (p + 1) (0 + 2)) = (-1 : ℝ) ^ (p + 1) • dv (zz pr b (p + 1 + 1) 1)` using `hS P Q pr p 0 b hb.2`. Establish `hr : (-1 : ℝ) * (-1) ^ (p + 1) = (-1) ^ (p + 1 + 1)` using `by ring`. Unfold `GoodS`.

Use `⟨p + 0 + 2, rfl, (-1 : ℝ) • b, hb'.smul _, w, e - (-1 : ℝ) ^ (p + 1 + 1) • zz pr b (p + 1 + 1) 1, hw, hwv, ?_, ?_, ?_⟩` and prove the remaining obligations. Conclude with `PInv.sub pr he (PInv.smul pr _ (hZ P Q pr _ _ _ b (by omega) hb.1))`. Rewrite using `[dh_sub, dh_smul, ← hyb, sub_self]`. Rewrite using `[zz_smul, dh_smul, h2, smul_smul, hr, dv_sub, dv_smul]`. Normalize the expressions using the abelian group laws.

Consider the case `succ q ih`. Introduce `hq p x hx hv hh`. Take `⟨w, e, hw, hwv, he, rfl⟩` from `hE P Q pr s hs u hu m hm p (q + 1) hq x hx hv hh`. Establish `hyv : dv (dh e) = 0`. Rewrite using `[← dh_dv]`.

Rewrite `hh` using `[dh_add, dh_dh]`. Simplify using `using hh`. Establish `hg` using `ih (by omega) (p + 1) (dh e) (PInv.dh pr he) hyv (dh_dh e)`. Unfold `GoodS at hg`. Take `⟨n, hn, b, hb, w', e', hw', hwv', he', hhe', hy⟩` from `hg`.

Take `rfl : n = p + (q + 1) + 2` from `by omega`. Take `⟨f, hf, hef⟩` from `row_exact pr e' he' hhe'`. Establish `hb' : QC b` using `hb`. Unfold `QC at hb`. Establish `h2 : dh (zz pr b (p + 1) (q + 1 + 2)) = (-1 : ℝ) ^ (p + 1) • dv (zz pr b (p + 1 + 1) (q + 2))` using `hS P Q pr p (q + 1) b hb.2`.

Unfold `GoodS`. Use `⟨p + (q + 1) + 2, rfl, (-1 : ℝ) ^ (p + 1) • b, hb'.smul _, w, e - zz pr b (p + 1 + 1) (q + 2) - w' - dv f, hw, hwv, ?_, ?_, ?_⟩` and prove the remaining obligations. Conclude with `PInv.sub pr (PInv.sub pr (PInv.sub pr he (hZ P Q pr _ _ _ b (by omega) hb.1)) hw') (PInv.dv pr hf)`. Rewrite using `[dh_sub, dh_sub, dh_sub, hy, dh_dv f, ← hef]`. Normalize the expressions using the abelian group laws.

Rewrite using `[zz_smul, dh_smul, h2, smul_smul, ← mul_pow, dv_sub, dv_sub, dv_sub, hwv', dv_dv]`. Simplify using `only [neg_one_mul, neg_neg, one_pow, one_smul]`. Normalize the expressions using the abelian group laws.
-/
theorem claimS (hB : SplitB) (hS : SplitS) (hZ : ZInv) (hE : E2VanishingOtherColumns) (pr : P →* Q) (s : Q →* P)
    (hs : ∀ g, pr (s g) = g) (u : Q) (hu : ∀ g, g * u = u * g) (m : ℕ) (hm : ColPoly pr s u m) :
    ∀ q : ℕ, q + 1 ≤ m → ∀ (p : ℕ) (x : Bi P Q (p + 2) (q + 2)), PInv pr x → dv x = 0 → dh x = 0 →
      GoodS pr x := by
  intro q
  induction q with
  | zero =>
    intro hq p x hx hv hh
    obtain ⟨w, e, hw, hwv, he, rfl⟩ := hE P Q pr s hs u hu m hm p 0 hq x hx hv hh
    have hyv : dv (dh e) = 0 := by
      rw [← dh_dv]
      rw [dh_add, dh_dh] at hh
      simpa using hh
    obtain ⟨b, hb, hyb⟩ := exists_quasiCocycle_eq_dh_zz_of_pInv_dv_dh_zero hB pr s hs (dh e) (PInv.dh pr he) hyv (dh_dh e)
    have hb' : QC b := hb
    unfold QC at hb
    have h2 : dh (zz pr b (p + 1) (0 + 2)) = (-1 : ℝ) ^ (p + 1) • dv (zz pr b (p + 1 + 1) 1) :=
      hS P Q pr p 0 b hb.2
    have hr : (-1 : ℝ) * (-1) ^ (p + 1) = (-1) ^ (p + 1 + 1) := by ring
    unfold GoodS
    refine ⟨p + 0 + 2, rfl, (-1 : ℝ) • b, hb'.smul _, w, e - (-1 : ℝ) ^ (p + 1 + 1) • zz pr b (p + 1 + 1) 1,
      hw, hwv, ?_, ?_, ?_⟩
    · exact PInv.sub pr he (PInv.smul pr _ (hZ P Q pr _ _ _ b (by omega) hb.1))
    · rw [dh_sub, dh_smul, ← hyb, sub_self]
    · rw [zz_smul, dh_smul, h2, smul_smul, hr, dv_sub, dv_smul]
      abel
  | succ q ih =>
    intro hq p x hx hv hh
    obtain ⟨w, e, hw, hwv, he, rfl⟩ := hE P Q pr s hs u hu m hm p (q + 1) hq x hx hv hh
    have hyv : dv (dh e) = 0 := by
      rw [← dh_dv]
      rw [dh_add, dh_dh] at hh
      simpa using hh
    have hg := ih (by omega) (p + 1) (dh e) (PInv.dh pr he) hyv (dh_dh e)
    unfold GoodS at hg
    obtain ⟨n, hn, b, hb, w', e', hw', hwv', he', hhe', hy⟩ := hg
    obtain rfl : n = p + (q + 1) + 2 := by omega
    obtain ⟨f, hf, hef⟩ := row_exact pr e' he' hhe'
    have hb' : QC b := hb
    unfold QC at hb
    have h2 : dh (zz pr b (p + 1) (q + 1 + 2)) = (-1 : ℝ) ^ (p + 1) • dv (zz pr b (p + 1 + 1) (q + 2)) :=
      hS P Q pr p (q + 1) b hb.2
    unfold GoodS
    refine ⟨p + (q + 1) + 2, rfl, (-1 : ℝ) ^ (p + 1) • b, hb'.smul _, w,
      e - zz pr b (p + 1 + 1) (q + 2) - w' - dv f, hw, hwv, ?_, ?_, ?_⟩
    · exact PInv.sub pr (PInv.sub pr (PInv.sub pr he (hZ P Q pr _ _ _ b (by omega) hb.1)) hw')
        (PInv.dv pr hf)
    · rw [dh_sub, dh_sub, dh_sub, hy, dh_dv f, ← hef]
      abel
    · rw [zz_smul, dh_smul, h2, smul_smul, ← mul_pow, dv_sub, dv_sub, dv_sub, hwv', dv_dv]
      simp only [neg_one_mul, neg_neg, one_pow, one_smul]
      abel

/- English proof (translation)
Take `⟨e, he, rfl⟩` from `hEz P Q pr s hs u hu m hm q hq x hx hv hh`. Establish `hyv : dv (dh e) = 0`. Rewrite using `[← dh_dv]`. Conclude with `hh`. Unfold `GoodT`.

Consider the cases of `q with`. Consider the case `zero`. Take `⟨b, hb, hyb⟩` from `exists_quasiCocycle_eq_dh_zz_of_pInv_dv_dh_zero hB pr s hs (dh e) (PInv.dh pr he) hyv (dh_dh e)`. Establish `hb' : QC b` using `hb`. Unfold `QC at hb`.

Establish `h2 : Wtop pr b = dv (zz pr b (0 + 1) 1)` using `hA P Q pr 0 b hb.2`. Use `⟨(-1 : ℝ) ^ (0 + 1) • b, hb'.smul _, e - (-1 : ℝ) ^ (0 + 1) • zz pr b (0 + 1) 1, ?_, ?_, ?_⟩` and prove the remaining obligations. Conclude with `PInv.sub pr he (PInv.smul pr _ (hZ P Q pr _ _ _ b (by omega) hb.1))`. Rewrite using `[dh_sub, dh_smul, ← hyb, sub_self]`. Rewrite using `[Wtop_smul, h2, dv_sub, dv_smul]`.

Normalize the expressions using the abelian group laws. Consider the case `succ q`. Establish `hg` using `claimS hB hS hZ hEs pr s hs u hu m hm q (by omega) 0 (dh e) (PInv.dh pr he) hyv (dh_dh e)`. Unfold `GoodS at hg`. Take `⟨n, hn, b, hb, w', e', hw', hwv', he', hhe', hy⟩` from `hg`.

Take `rfl : n = q + 1 + 1` from `by omega`. Take `⟨f, hf, hef⟩` from `row_exact pr e' he' hhe'`. Establish `hb' : QC b` using `hb`. Unfold `QC at hb`. Establish `h2 : Wtop pr b = dv (zz pr b (0 + 1) (q + 2))` using `hA P Q pr (q + 1) b hb.2`.

Use `⟨b, hb', e - zz pr b (0 + 1) (q + 2) - w' - dv f, ?_, ?_, ?_⟩` and prove the remaining obligations. Conclude with `PInv.sub pr (PInv.sub pr (PInv.sub pr he (hZ P Q pr _ _ _ b (by omega) hb.1)) hw') (PInv.dv pr hf)`. Rewrite using `[dh_sub, dh_sub, dh_sub, hy, dh_dv f, ← hef]`. Normalize the expressions using the abelian group laws. Rewrite using `[h2, dv_sub, dv_sub, dv_sub, hwv', dv_dv]`.

Normalize the expressions using the abelian group laws.
-/
theorem claimT (hB : SplitB) (hA : SplitA) (hS : SplitS) (hZ : ZInv) (hEz : E2VanishingFirstColumn) (hEs : E2VanishingOtherColumns)
    (pr : P →* Q) (s : Q →* P) (hs : ∀ g, pr (s g) = g) (u : Q) (hu : ∀ g, g * u = u * g) (m : ℕ)
    (hm : ColPoly pr s u m) (q : ℕ) (hq : q + 1 ≤ m) (x : Bi P Q 1 (q + 2)) (hx : PInv pr x)
    (hv : dv x = 0) (hh : dh x = 0) : GoodT pr x := by
  obtain ⟨e, he, rfl⟩ := hEz P Q pr s hs u hu m hm q hq x hx hv hh
  have hyv : dv (dh e) = 0 := by
    rw [← dh_dv]
    exact hh
  unfold GoodT
  cases q with
  | zero =>
    obtain ⟨b, hb, hyb⟩ := exists_quasiCocycle_eq_dh_zz_of_pInv_dv_dh_zero hB pr s hs (dh e) (PInv.dh pr he) hyv (dh_dh e)
    have hb' : QC b := hb
    unfold QC at hb
    have h2 : Wtop pr b = dv (zz pr b (0 + 1) 1) := hA P Q pr 0 b hb.2
    refine ⟨(-1 : ℝ) ^ (0 + 1) • b, hb'.smul _, e - (-1 : ℝ) ^ (0 + 1) • zz pr b (0 + 1) 1, ?_, ?_, ?_⟩
    · exact PInv.sub pr he (PInv.smul pr _ (hZ P Q pr _ _ _ b (by omega) hb.1))
    · rw [dh_sub, dh_smul, ← hyb, sub_self]
    · rw [Wtop_smul, h2, dv_sub, dv_smul]
      abel
  | succ q =>
    have hg := claimS hB hS hZ hEs pr s hs u hu m hm q (by omega) 0 (dh e) (PInv.dh pr he) hyv (dh_dh e)
    unfold GoodS at hg
    obtain ⟨n, hn, b, hb, w', e', hw', hwv', he', hhe', hy⟩ := hg
    obtain rfl : n = q + 1 + 1 := by omega
    obtain ⟨f, hf, hef⟩ := row_exact pr e' he' hhe'
    have hb' : QC b := hb
    unfold QC at hb
    have h2 : Wtop pr b = dv (zz pr b (0 + 1) (q + 2)) := hA P Q pr (q + 1) b hb.2
    refine ⟨b, hb', e - zz pr b (0 + 1) (q + 2) - w' - dv f, ?_, ?_, ?_⟩
    · exact PInv.sub pr (PInv.sub pr (PInv.sub pr he (hZ P Q pr _ _ _ b (by omega) hb.1)) hw')
        (PInv.dv pr hf)
    · rw [dh_sub, dh_sub, dh_sub, hy, dh_dv f, ← hef]
      abel
    · rw [h2, dv_sub, dv_sub, dv_sub, hwv', dv_dv]
      abel

/- English proof (translation)
Establish `h1` using `congrFun (congrFun h ![1, x 0]) y`. Simplify using `[dh, dc, Fin.sum_univ_two] at h1`. Establish `e1 : (fun _ : Fin 1 => x 0) = x`. Use function extensionality and compare the values at `j`. Rewrite using `[Subsingleton.elim j 0]`.

Establish `e2 : (fun j : Fin 1 => (![1, x 0] : Fin 2 → Q) (Fin.succAbove 1 j)) = fun _ => 1`. Use function extensionality and compare the values at `j`. Rewrite using `[Subsingleton.elim j 0]`. Both sides reduce to the same expression. Rewrite `h1` using `[e1, e2]`.

Combine the linear equalities and inequalities to obtain the conclusion.
-/
private theorem bi_fin_one_apply_eq_apply_one_of_dh_eq_zero {k : ℕ} (F : Bi P Q 1 k) (h : dh F = 0) (x : Fin 1 → Q) (y : Fin k → P) :
    F x y = F (fun _ => 1) y := by
  have h1 := congrFun (congrFun h ![1, x 0]) y
  simp [dh, dc, Fin.sum_univ_two] at h1
  have e1 : (fun _ : Fin 1 => x 0) = x := by
    funext j
    rw [Subsingleton.elim j 0]
  have e2 : (fun j : Fin 1 => (![1, x 0] : Fin 2 → Q) (Fin.succAbove 1 j)) = fun _ => 1 := by
    funext j
    rw [Subsingleton.elim j 0]
    rfl
  rw [e1, e2] at h1
  linarith

/- English proof (translation)
Unfold `Core`. Introduce `P Q _ _ pr s hs u hu m hm j hj c hc hdc hvan`. Unfold `InvS at hc`. Establish `hP : PInv pr (fun (_ : Fin 1 → Q) (y : Fin (j + 2) → P) => c y : Bi P Q 1 (j + 2))`. Unfold `PInv`.

Introduce `g a y`. Conclude with `hc g (Set.mem_univ g) y`. Establish `hV : dv (fun (_ : Fin 1 → Q) (y : Fin (j + 2) → P) => c y : Bi P Q 1 (j + 2)) = 0`. Use function extensionality and compare the values at `a y`. Conclude with `congrFun hdc y`.

Establish `hH : dh (fun (_ : Fin 1 → Q) (y : Fin (j + 2) → P) => c y : Bi P Q 1 (j + 2)) = 0`. Use function extensionality and compare the values at `a y`. Simplify using `[dh, dc, Fin.sum_univ_two]`. Establish `hT` using `claimT hB hA hS hZ hEz hEs pr s hs u hu m hm j hj _ hP hV hH`. Unfold `GoodT at hT`.

Take `⟨b, hb, e, he, hhe, hxe⟩` from `hT`. Unfold `PInv at he`. Use `set e' : (Fin (j + 1) → P) → ℝ := fun z => e (fun _ => 1) z with he'`. Establish `hinv : ∀ (g : P) (y : Fin (j + 1) → P), e' (fun i => g * y i) = e' y`. Introduce `g y`.

Conclude with `(bi_fin_one_apply_eq_apply_one_of_dh_eq_zero e hhe _ _).symm.trans (he g (fun _ => 1) y)`. Establish `hpt : ∀ y, c y = b (fun i => pr (y i)) + dc e' y` using `fun y => congrFun (congrFun hxe (fun _ => 1)) y`. Establish `hbv : ∀ y : Fin (j + 2) → Q, b y = - dc (fun z => e' (fun i => s (z i))) y`. Introduce `y`. Establish `h` using `hpt (fun i => s (y i))`.

Rewrite `h` using `[hvan y]`. Simplify using `only [hs] at h`. Establish `h3 : dc (fun z => e' (fun i => s (z i))) y = dc e' (fun i => s (y i))` using `rfl`. Combine the linear equalities and inequalities to obtain the conclusion. Use `⟨e' - fun z => e' (fun i => s (pr (z i))), ?_, ?_⟩` and prove the remaining obligations.

Unfold `InvS`. Introduce `g _ y`. Simplify using `only [Pi.sub_apply, map_mul]`. Rewrite using `[hinv g y]`. Use `congr 1`.

Conclude with `hinv (s (pr g)) (fun i => s (pr (y i)))`. Use function extensionality and compare the values at `y`. Rewrite using `[dc_sub, Pi.sub_apply, hpt y, hbv (fun i => pr (y i))]`. Establish `h3 : dc (fun z => e' (fun i => s (z i))) (fun i => pr (y i)) = dc (fun z => e' (fun i => s (pr (z i)))) y` using `rfl`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem core_of (hA : SplitA) (hS : SplitS) (hB : SplitB) (hZ : ZInv) (hEz : E2VanishingFirstColumn) (hEs : E2VanishingOtherColumns) : Core := by
  unfold Core
  intro P Q _ _ pr s hs u hu m hm j hj c hc hdc hvan
  unfold InvS at hc
  have hP : PInv pr (fun (_ : Fin 1 → Q) (y : Fin (j + 2) → P) => c y : Bi P Q 1 (j + 2)) := by
    unfold PInv
    intro g a y
    exact hc g (Set.mem_univ g) y
  have hV : dv (fun (_ : Fin 1 → Q) (y : Fin (j + 2) → P) => c y : Bi P Q 1 (j + 2)) = 0 := by
    funext a y
    exact congrFun hdc y
  have hH : dh (fun (_ : Fin 1 → Q) (y : Fin (j + 2) → P) => c y : Bi P Q 1 (j + 2)) = 0 := by
    funext a y
    simp [dh, dc, Fin.sum_univ_two]
  have hT := claimT hB hA hS hZ hEz hEs pr s hs u hu m hm j hj _ hP hV hH
  unfold GoodT at hT
  obtain ⟨b, hb, e, he, hhe, hxe⟩ := hT
  unfold PInv at he
  set e' : (Fin (j + 1) → P) → ℝ := fun z => e (fun _ => 1) z with he'
  have hinv : ∀ (g : P) (y : Fin (j + 1) → P), e' (fun i => g * y i) = e' y := by
    intro g y
    exact (bi_fin_one_apply_eq_apply_one_of_dh_eq_zero e hhe _ _).symm.trans (he g (fun _ => 1) y)
  have hpt : ∀ y, c y = b (fun i => pr (y i)) + dc e' y := fun y => congrFun (congrFun hxe (fun _ => 1)) y
  have hbv : ∀ y : Fin (j + 2) → Q, b y = - dc (fun z => e' (fun i => s (z i))) y := by
    intro y
    have h := hpt (fun i => s (y i))
    rw [hvan y] at h
    simp only [hs] at h
    have h3 : dc (fun z => e' (fun i => s (z i))) y = dc e' (fun i => s (y i)) := rfl
    linarith
  refine ⟨e' - fun z => e' (fun i => s (pr (z i))), ?_, ?_⟩
  · unfold InvS
    intro g _ y
    simp only [Pi.sub_apply, map_mul]
    rw [hinv g y]
    congr 1
    exact hinv (s (pr g)) (fun i => s (pr (y i)))
  · funext y
    rw [dc_sub, Pi.sub_apply, hpt y, hbv (fun i => pr (y i))]
    have h3 : dc (fun z => e' (fun i => s (z i))) (fun i => pr (y i))
        = dc (fun z => e' (fun i => s (pr (z i)))) y := rfl
    linarith

end PositivityTheory.KB.SplitAffineSpectral.NormTraceLemmas

end

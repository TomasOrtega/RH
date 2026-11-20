import Formalism.ThetaLogCoordinates.PartnerMeanCoordinates.TheoremMXB

namespace Formalism.InvariantFactorPaths.MC

open Formalism.GM Formalism.GM.TM Formalism.GM.M Formalism.InvariantFactorPaths.OddLevelGainBounds.TB MvPolynomial Finset

/- English proof (translation)
Introduce `p _ N r _ _ LL T Xb E κ κ4 lgv e1 Yl n₀ dd ρ hp2 hr hρ hadm hE hYd hS hdeg hsz hrX hL hκ32 he1 hκ4 hHyp`. Establish `hp1 : (1 : ℝ) < p` using `by exact_mod_cast (Fact.out : p.Prime).one_lt`. Establish `hlg : 0 ≤ lgv`. Establish `: (0 : ℝ) ≤ (Nat.log p Xb : ℝ)` using `Nat.cast_nonneg _`. Combine the linear equalities and inequalities to obtain the conclusion.

Establish `hκ : ((N + 2) * r ^ 2 : ℝ) * lgv ≤ κ`. Establish `: 0 ≤ ((N + 2) * r ^ 2 : ℝ) * lgv` using `by positivity`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hκ0 : 0 ≤ κ` using `le_trans (by positivity) hκ`. Use `choose nb fb ord hli hsp hord hfil using fun (i : Fin T.t) (L0 : Letters (T.pos i + 1)) (w : Fin r → ℤ) => hAd p (T.pos i) r L0 T.J (T.thrUpTo i) ρ w`.

Use `choose Uc Vc dgc hUc using fun (k : ℕ) (A : Matrix (Fin k) (Fin k) ℚ_[p]) => smith_qp hSmith A`. Establish `hfwex : ∀ (i : Fin T.t) (L0 : Letters (T.pos i + 1)) (w : Fin r → ℤ), ∃ g, g ∈ MMw p L0 T.J (T.thrUpTo i) ρ w ∧ (MMw p L0 T.J (T.thrUpTo i) ρ w ≠ ⊥ → g ≠ 0)`. Introduce `i L0 w`. Distinguish the cases in `h : MMw p L0 T.J (T.thrUpTo i) ρ w = ⊥`. Conclude with `⟨0, Submodule.zero_mem _, fun h' => absurd h h'⟩`.

Take `⟨g, hg, hg0⟩` from `Submodule.exists_mem_ne_zero_of_ne_bot h`. Conclude with `⟨g, hg, fun _ => hg0⟩`. Use `choose fw hfw using hfwex`. Establish `hnb : ∀ i L0 w, nb i L0 w = Module.finrank ℚ_[p] (MMw p L0 T.J (T.thrUpTo i) ρ w)` using `fun i L0 w => (finrank_of_lattice_basis _ (fb i L0 w) (hli i L0 w) (hsp i L0 w)).symm`. Set `MatF : ∀ (i : Fin T.t) (L0 : Letters (T.pos i + 1)) (w : Fin r → ℤ) (y : ℕ), Matrix (Fin (nb i L0 w)) (Fin (nb i L0 w)) ℚ_[p]` to `fun i L0 w y => Matrix.of fun x x' => (p : ℚ_[p]) ^ (⌈κ⌉₊) * tieGam p L0 ρ (T.z i) y (fb i L0 w x) (fb i L0 w x')`.

Set `cntF : ∀ (i : Fin T.t) (L0 : Letters (T.pos i + 1)) (w : Fin r → ℤ) (y : ℕ), ℕ` to `fun i L0 w y => (univ.filter (fun b => ‖dgc _ (MatF i L0 w y) b‖ < (p : ℝ) ^ (-E))).card`. Set `Bx : ∀ i : Fin T.t, Letters (T.pos i + 1) → Finset (Fin r → ℤ)` to `fun i L0 => Fintype.piFinset fun _ => Icc (-(L0.total : ℤ)) L0.total`. Establish `hcntle : ∀ i L0 w y, cntF i L0 w y ≤ nb i L0 w` using `fun i L0 w y => (Finset.card_filter_le _ _).trans (by rw [Finset.card_univ, Fintype.card_fin])`. Establish `hbot : ∀ i L0 w, w ∉ Bx i L0 → MMw p L0 T.J (T.thrUpTo i) ρ w = ⊥` using `fun i L0 w hw => by`. Assume the negation of the conclusion as `h`.

Conclude with `hw (mmw_ne_bot_box L0 T.J (T.thrUpTo i) ρ w h)`. Establish `hnb0 : ∀ i L0 w, w ∉ Bx i L0 → nb i L0 w = 0` using `fun i L0 w hw => by`. Rewrite using `[hnb, hbot i L0 w hw, finrank_bot]`. Establish `hcnt0 : ∀ i L0 w y, w ∉ Bx i L0 → cntF i L0 w y = 0` using `fun i L0 w y hw => Nat.eq_zero_of_le_zero ((hcntle i L0 w y).trans (hnb0 i L0 w hw).le)`. Set `sI : Fin T.t → Finset ℕ` to `fun i => (range (Yl i)).image (fun j => n₀ i + dd i * j)`.

Set `top : Fin T.t → ℕ` to `fun i => n₀ i + dd i * (Yl i - 1)`. Establish `hsI : ∀ i y, y ∈ sI i → n₀ i ≤ y ∧ y ≤ top i`. Introduce `i y hy`. Simplify using `only [sI, mem_image, mem_range] at hy`. Take `⟨j, hj, rfl⟩` from `hy`.

Use `⟨Nat.le_add_right _ _, Nat.add_le_add_left (Nat.mul_le_mul_left _ (by omega)) _⟩` and prove the remaining obligations. Establish `hgrid : ∀ n ∈ Fintype.piFinset sI, ∀ i, n₀ i ≤ n i ∧ n i ≤ top i` using `fun n hn i => hsI i (n i) (Fintype.mem_piFinset.mp hn i)`. Establish `hinj : ∀ i, Set.InjOn (fun j => n₀ i + dd i * j) (range (Yl i) : Set ℕ)`. Introduce `i x _ y _ hxy`. Use `(hYd i).2.1` as an intermediate fact.

Simplify using `only at hxy`. Conclude with `Nat.eq_of_mul_eq_mul_left this (by omega)`. Establish `hcard : ∀ i, (sI i).card = Yl i` using `fun i => by`. Simplify using `only [sI]`. Rewrite using `[Finset.card_image_of_injOn (hinj i), Finset.card_range]`.

Set `BB : Fin T.t → (Fin T.t → ℕ) → ℝ` to `fun i n => ∑ w ∈ Bx i ((LL.setTies T n).takeD (T.pos i + 1)), (cntF i ((LL.setTies T n).takeD (T.pos i + 1)) w (n i) : ℝ) * (Module.finrank ℚ_[p] (T.YYsp p LL i ρ n (fw i ((LL.setTies T n).takeD (T.pos i + 1)) w)) : ℝ)`. Use `grid_average sI (fun n => (bad p (fun F G => fockN p (LL.setTies T n) (T.phis p (LL.setTies T n) F) G) (YZ p (r := r) (LL.setTies T n) T.J T.thr) ⌊(T.t : ℝ) * (E + κ) + κ⌋ : ℝ)) BB (fun i n => (Module.finrank ℚ_[p] (Y p (r := r) (LL.setTies T (Function.update n i (top i))) T.J T. …` and prove the remaining obligations. Introduce `n hn`. Establish `hnt : ∀ i, n i ≤ top i` using `fun i => (hgrid n hn i).2`. Establish `hSn : ∀ i, T.S (LL.setTies T n) i ≤ n i` using `fun i => (S_mono LL T n top hnt i).trans ((hS i).trans (hgrid n hn i).1)`.

Establish `hdegn : ∀ x, (LL.setTies T n).deg x ≤ Xb` using `fun x => (setTies_deg_mono LL T n top hnt x).trans (hdeg x)`. Take `⟨hP, hW, hL4⟩` from `hHyp n hn`. Establish `key` using `hPW p N r LL T Xb E κ lgv e1 n ρ hp2 hr hρ hadm hE hSn hdegn hL hκ he1 hP hW (fun i w => nb i ((LL.setTies T n).takeD (T.pos i + 1)) w) (fun i w => fb i ((LL.setTies T n).takeD (T.pos i + 1)) w) (fun i w => Uc _ (MatF i ((LL.setTies T n).takeD (T.pos i + 1)) w (n i))) (fun i w => …`. Use `key.trans (le_of_eq (Finset.sum_congr rfl fun i _ => ?_))` and prove the remaining obligations. Apply `finsum_eq_sum_of_support_subset` to reduce the goal to its premises.

Introduce `w hw`. Assume the negation of the conclusion as `hwn`. Apply `hw` to reduce the goal to its premises. Establish `h0` using `hcnt0 i ((LL.setTies T n).takeD (T.pos i + 1)) w (n i) hwn`. Simplify using `only [cntF] at h0`.

Simplify using `only [h0, Nat.cast_zero, zero_mul]`. Introduce `i n hn`. Establish `hnt : ∀ i, n i ≤ top i` using `fun i => (hgrid n hn i).2`. Take `⟨hlt, hvW, _⟩` from `hadm.2.1 i`. Take `⟨_, _, hL4⟩` from `hHyp n hn`.

Establish `hLW : ∀ y, (LL.setTies T (Function.update n i y)).takeD (T.pos i + 1) = (LL.setTies T n).takeD (T.pos i + 1)` using `fun y => takeD_setTies_update LL T n i y`. Establish `hL0S : ((LL.setTies T n).takeD (T.pos i + 1)).total ≤ T.S (LL.setTies T top) i`. Rewrite using `[takeD_total_eq (LL.setTies T n) T i hlt]`. Conclude with `S_mono LL T n top hnt i`. Establish `hL0tot : ((LL.setTies T n).takeD (T.pos i + 1)).total ≤ n₀ i` using `hL0S.trans (hS i)`.

Establish `hvec : ((LL.setTies T n).takeD (T.pos i + 1)).vec (Fin.last (T.pos i)) = true`. Simplify using `only [Letters.takeD, Fin.val_last]`. Rewrite using `[dif_pos (by omega)]`. Conclude with `hvW`. Establish `h2S : 2 * ((LL.setTies T n).takeD (T.pos i + 1)).total ≤ Xb`.

Conclude with `(Nat.mul_le_mul_left 2 hL0S).trans (hsz i).1`. Establish `hzo : T.z i + ((LL.setTies T n).takeD (T.pos i + 1)).deg (Fin.last (T.pos i)) ≤ Xb`. Establish `h1` using `(hsz i).2.2 (by omega)`. Establish `h2 : ((LL.setTies T n).takeD (T.pos i + 1)).deg (Fin.last (T.pos i)) = (LL.setTies T n).deg ⟨T.pos i, by omega⟩`. Simplify using `only [Letters.takeD, Fin.val_last]`.

Rewrite using `[dif_pos (by omega)]`. Establish `h3` using `setTies_deg_mono LL T n top hnt ⟨T.pos i, by omega⟩`. Rewrite using `[h2]`. Conclude with `(Nat.add_le_add_left h3 _).trans h1`. Establish `hκi : ((((T.pos i : ℕ) : ℝ) + 4) * r + 6 : ℝ) * lgv ≤ κ`.

Use `le_trans ?_ hκ32` and prove the remaining obligations. Establish `hP4 : ((T.pos i : ℕ) : ℝ) + 4 ≤ (N : ℝ) + 2`. Establish `: T.pos i + 4 ≤ N + 2` using `by omega`. Conclude with `this` after adjusting the coercions. Establish `hP0 : (0 : ℝ) ≤ ((T.pos i : ℕ) : ℝ)` using `Nat.cast_nonneg _`.

Establish `hr' : (2 : ℝ) ≤ r` using `by exact_mod_cast hr`. Establish `hN4 : (4 : ℝ) ≤ (N : ℝ) + 2` using `by linarith`. Establish `g1 : 2 * (((N : ℝ) + 2) * r) ≤ ((N : ℝ) + 2) * (r : ℝ) ^ 2`. Use `mul_nonneg (mul_nonneg (by linarith : (0 : ℝ) ≤ (N : ℝ) + 2) (by linarith : (0 : ℝ) ≤ (r : ℝ))) (sub_nonneg.mpr hr')` as an intermediate fact. Use the polynomial consequences of the given equalities and inequalities.

Establish `g2 : (8 : ℝ) ≤ ((N : ℝ) + 2) * r`. Use `mul_le_mul hN4 hr' (by norm_num) (by linarith)` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion. Establish `g3 : (((T.pos i : ℕ) : ℝ) + 4) * r ≤ ((N : ℝ) + 2) * r` using `mul_le_mul_of_nonneg_right hP4 (by linarith)`. Establish `g4 : (((T.pos i : ℕ) : ℝ) + 4) * r + 6 ≤ 3 / 2 * (((N : ℝ) + 2) * (r : ℝ) ^ 2)` using `by linarith`.

Combine the equalities or inequalities in the displayed calculation. Use `set L0 := (LL.setTies T n).takeD (T.pos i + 1) with hL0`. Establish `qe1 : ∀ y, BB i (Function.update n i y) = ∑ w ∈ Bx i L0, (cntF i L0 w y : ℝ) * (Module.finrank ℚ_[p] (T.YYsp p LL i ρ (Function.update n i y) (fw i L0 w)) : ℝ)`. Introduce `y`. Simplify using `only [BB]`.

Rewrite using `[hLW y, Function.update_self]`. Simplify using `only [qe1]`. Establish `hmono : ∀ y ∈ sI i, ∀ w, (cntF i L0 w y : ℝ) * (Module.finrank ℚ_[p] (T.YYsp p LL i ρ (Function.update n i y) (fw i L0 w)) : ℝ) ≤ (cntF i L0 w y : ℝ) * (Module.finrank ℚ_[p] (T.YYsp p LL i ρ (Function.update n i (top i)) (fw i L0 w)) : ℝ)`. Introduce `y hy w`. Distinguish the cases in `hM : MMw p L0 T.J (T.thrUpTo i) ρ w = ⊥`.

Establish `: cntF i L0 w y = 0` using `Nat.eq_zero_of_le_zero ((hcntle i L0 w y).trans (by rw [hnb, hM, finrank_bot]))`. Simplify using `[this]`. Apply `mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)` to reduce the goal to its premises. Establish `hm` using `hMono p N r LL T hadm ρ hρ hr i (Function.update n i y) w (fw i L0 w) (by rw [hLW y]; exact (hfw i L0 w).1) ((hfw i L0 w).2 hM) (by rw [hLW y, Function.update_self]; exact hL0tot.trans (hsI i y hy).1) (top i) (by rw [Function.update_self]; exact (hsI i y hy).2)`. Rewrite `hm` using `[Function.update_idem]`.

Conclude with `hm` after adjusting the coercions. Establish `hmean : ∀ w ∈ Bx i L0, (∑ y ∈ sI i, (cntF i L0 w y : ℝ)) ≤ (Yl i : ℝ) * ((nb i L0 w : ℝ) * (2 * (T.S (LL.setTies T top) i : ℝ) / Yl i + (2 * κ + 2 * (T.S (LL.setTies T top) i : ℝ) * lgv / Yl i) / E))`. Introduce `w _`. Establish `hm` using `hMG p (T.pos i) r L0 T.J (T.thrUpTo i) ρ (T.z i) w (nb i L0 w) (fb i L0 w) (ord i L0 w) (n₀ i) (dd i) (Yl i) Xb E κ κ4 lgv (fun j => Uc _ (MatF i L0 w (n₀ i + dd i * j))) (fun j => Vc _ (MatF i L0 w (n₀ i + dd i * j))) (fun j => dgc _ (MatF i L0 w (n₀ i + dd i * j))) hρ hr hvec ( …`. Establish `hY0 : (0 : ℝ) < Yl i` using `by exact_mod_cast (hYd i).1`.

Rewrite `hm` using `[div_le_iff₀ hY0]`. Establish `hsum : (∑ y ∈ sI i, (cntF i L0 w y : ℝ)) = ∑ j ∈ range (Yl i), ((univ.filter (fun b => ‖dgc _ (MatF i L0 w (n₀ i + dd i * j)) b‖ < (p : ℝ) ^ (-E))).card : ℝ)`. Simplify using `only [sI]`. Rewrite using `[Finset.sum_image (hinj i)]`. Rewrite using `[hsum]`.

Use `hm.trans ?_` and prove the remaining obligations. Rewrite using `[mul_comm]`. Apply `mul_le_mul_of_nonneg_left _ hY0.le` to reduce the goal to its premises. Apply `mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)` to reduce the goal to its premises. Establish `hE0 : (0 : ℝ) < E` using `by linarith`.

Establish `hL : ((L0.total : ℕ) : ℝ) ≤ (T.S (LL.setTies T top) i : ℝ)` using `by exact_mod_cast hL0S`. Establish `hC : κ + 3 * lgv + κ4 ≤ 2 * κ` using `by linarith`. Use `gcongr`. Establish `hcount : (∑ w ∈ Bx i L0, (nb i L0 w : ℝ) * (Module.finrank ℚ_[p] (T.YYsp p LL i ρ (Function.update n i (top i)) (fw i L0 w)) : ℝ)) = (Module.finrank ℚ_[p] (Y p (r` using `r) (LL.setTies T (Function.update n i (top i))) T.J T.thr) : ℝ) := by`. Establish `hc` using `hCount p N r LL T hadm ρ hρ hr i (Function.update n i (top i)) (by rw [hLW, Function.update_self]; exact hL0tot.trans (Nat.le_add_right _ _)) (fun w => fw i L0 w) (fun w => by rw [hLW]; exact hfw i L0 w)`.

Rewrite `hc` using `[hLW]`. Rewrite using `[finsum_eq_sum_of_support_subset _ (s := Bx i L0) (fun w hw => by`. Assume the negation of the conclusion as `hwn`. Apply `hw` to reduce the goal to its premises. Use `beta_reduce`.

Rewrite `hc` using `[← hnb, hnb0 i L0 w hwn, zero_mul])]`. Rewrite using `[← hc]`. Use `push_cast`. Apply `Finset.sum_congr rfl` to reduce the goal to its premises. Introduce `w _`.

Rewrite using `[hnb]`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[Finset.sum_comm]`. Simplify using `only [Finset.sum_mul]`. Use `_ ≤ ∑ w ∈ Bx i L0, ((Yl i : ℝ) * ((nb i L0 w : ℝ) * (2 * (T.S (LL.setTies T top) i : ℝ) / Yl i + (2 * κ + 2 * (T.S (LL.setTies T top) i : ℝ) * lgv / Yl i) / E))) * (Module.finrank ℚ_[p] (T.YYsp p LL i ρ (Function.update n i (top i)) (fw i L0 w)) : ℝ) := Finset.sum_le_sum fun w hw …`.

Use `_ = (sI i).card * ((2 * (T.S (LL.setTies T top) i : ℝ) / Yl i + (2 * κ + 2 * (T.S (LL.setTies T top) i : ℝ) * lgv / Yl i) / E) * ∑ w ∈ Bx i L0, (nb i L0 w : ℝ) * (Module.finrank ℚ_[p] (T.YYsp p LL i ρ (Function.update n i (top i)) (fw i L0 w)) : ℝ)) := by`. Rewrite using `[hcard, Finset.mul_sum, Finset.mul_sum]`. Apply `Finset.sum_congr rfl` to reduce the goal to its premises. Introduce `w _`. Expand and normalize the polynomial expressions, which then agree.

Use `_ = _ := by rw [hcount]`.
-/
theorem theoremMXB_of_point (hMG : MeanGamX) (hMono : WeightSpaceDimMonotone) (hCount : MonoCount) (hSmith : SmithZp)
    (hAd : AdaptedBasisExists) (hPW : PointMX) : TheoremMXB := by
  intro p _ N r _ _ LL T Xb E κ κ4 lgv e1 Yl n₀ dd ρ hp2 hr hρ hadm hE hYd hS hdeg hsz hrX hL hκ32 he1 hκ4 hHyp
  classical
  have hp1 : (1 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).one_lt
  have hlg : 0 ≤ lgv := by
    have : (0 : ℝ) ≤ (Nat.log p Xb : ℝ) := Nat.cast_nonneg _
    linarith
  have hκ : ((N + 2) * r ^ 2 : ℝ) * lgv ≤ κ := by
    have : 0 ≤ ((N + 2) * r ^ 2 : ℝ) * lgv := by positivity
    linarith
  have hκ0 : 0 ≤ κ := le_trans (by positivity) hκ

  choose nb fb ord hli hsp hord hfil using fun (i : Fin T.t) (L0 : Letters (T.pos i + 1)) (w : Fin r → ℤ) =>
    hAd p (T.pos i) r L0 T.J (T.thrUpTo i) ρ w
  choose Uc Vc dgc hUc using fun (k : ℕ) (A : Matrix (Fin k) (Fin k) ℚ_[p]) => smith_qp hSmith A
  have hfwex : ∀ (i : Fin T.t) (L0 : Letters (T.pos i + 1)) (w : Fin r → ℤ), ∃ g,
      g ∈ MMw p L0 T.J (T.thrUpTo i) ρ w ∧ (MMw p L0 T.J (T.thrUpTo i) ρ w ≠ ⊥ → g ≠ 0) := by
    intro i L0 w
    by_cases h : MMw p L0 T.J (T.thrUpTo i) ρ w = ⊥
    · exact ⟨0, Submodule.zero_mem _, fun h' => absurd h h'⟩
    · obtain ⟨g, hg, hg0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot h
      exact ⟨g, hg, fun _ => hg0⟩
  choose fw hfw using hfwex
  have hnb : ∀ i L0 w, nb i L0 w = Module.finrank ℚ_[p] (MMw p L0 T.J (T.thrUpTo i) ρ w) := fun i L0 w =>
    (finrank_of_lattice_basis _ (fb i L0 w) (hli i L0 w) (hsp i L0 w)).symm
  let MatF : ∀ (i : Fin T.t) (L0 : Letters (T.pos i + 1)) (w : Fin r → ℤ) (y : ℕ),
      Matrix (Fin (nb i L0 w)) (Fin (nb i L0 w)) ℚ_[p] := fun i L0 w y =>
    Matrix.of fun x x' => (p : ℚ_[p]) ^ (⌈κ⌉₊) * tieGam p L0 ρ (T.z i) y (fb i L0 w x) (fb i L0 w x')
  let cntF : ∀ (i : Fin T.t) (L0 : Letters (T.pos i + 1)) (w : Fin r → ℤ) (y : ℕ), ℕ := fun i L0 w y =>
    (univ.filter (fun b => ‖dgc _ (MatF i L0 w y) b‖ < (p : ℝ) ^ (-E))).card
  let Bx : ∀ i : Fin T.t, Letters (T.pos i + 1) → Finset (Fin r → ℤ) := fun i L0 =>
    Fintype.piFinset fun _ => Icc (-(L0.total : ℤ)) L0.total
  have hcntle : ∀ i L0 w y, cntF i L0 w y ≤ nb i L0 w := fun i L0 w y =>
    (Finset.card_filter_le _ _).trans (by rw [Finset.card_univ, Fintype.card_fin])
  have hbot : ∀ i L0 w, w ∉ Bx i L0 → MMw p L0 T.J (T.thrUpTo i) ρ w = ⊥ := fun i L0 w hw => by
    by_contra h; exact hw (mmw_ne_bot_box L0 T.J (T.thrUpTo i) ρ w h)
  have hnb0 : ∀ i L0 w, w ∉ Bx i L0 → nb i L0 w = 0 := fun i L0 w hw => by
    rw [hnb, hbot i L0 w hw, finrank_bot]
  have hcnt0 : ∀ i L0 w y, w ∉ Bx i L0 → cntF i L0 w y = 0 := fun i L0 w y hw =>
    Nat.eq_zero_of_le_zero ((hcntle i L0 w y).trans (hnb0 i L0 w hw).le)
  let sI : Fin T.t → Finset ℕ := fun i => (range (Yl i)).image (fun j => n₀ i + dd i * j)
  let top : Fin T.t → ℕ := fun i => n₀ i + dd i * (Yl i - 1)
  have hsI : ∀ i y, y ∈ sI i → n₀ i ≤ y ∧ y ≤ top i := by
    intro i y hy
    simp only [sI, mem_image, mem_range] at hy
    obtain ⟨j, hj, rfl⟩ := hy
    refine ⟨Nat.le_add_right _ _, Nat.add_le_add_left (Nat.mul_le_mul_left _ (by omega)) _⟩
  have hgrid : ∀ n ∈ Fintype.piFinset sI, ∀ i, n₀ i ≤ n i ∧ n i ≤ top i := fun n hn i =>
    hsI i (n i) (Fintype.mem_piFinset.mp hn i)
  have hinj : ∀ i, Set.InjOn (fun j => n₀ i + dd i * j) (range (Yl i) : Set ℕ) := by
    intro i x _ y _ hxy
    have := (hYd i).2.1
    simp only at hxy
    exact Nat.eq_of_mul_eq_mul_left this (by omega)
  have hcard : ∀ i, (sI i).card = Yl i := fun i => by
    simp only [sI]; rw [Finset.card_image_of_injOn (hinj i), Finset.card_range]
  let BB : Fin T.t → (Fin T.t → ℕ) → ℝ := fun i n =>
    ∑ w ∈ Bx i ((LL.setTies T n).takeD (T.pos i + 1)),
      (cntF i ((LL.setTies T n).takeD (T.pos i + 1)) w (n i) : ℝ) *
        (Module.finrank ℚ_[p] (T.YYsp p LL i ρ n (fw i ((LL.setTies T n).takeD (T.pos i + 1)) w)) : ℝ)
  refine grid_average sI (fun n => (bad p (fun F G => fockN p (LL.setTies T n) (T.phis p (LL.setTies T n) F) G)
      (YZ p (r := r) (LL.setTies T n) T.J T.thr) ⌊(T.t : ℝ) * (E + κ) + κ⌋ : ℝ)) BB
    (fun i n => (Module.finrank ℚ_[p] (Y p (r := r) (LL.setTies T (Function.update n i (top i))) T.J T.thr) : ℝ))
    (fun i => 2 * (T.S (LL.setTies T top) i : ℝ) / Yl i +
      (2 * κ + 2 * (T.S (LL.setTies T top) i : ℝ) * lgv / Yl i) / E)
    (fun i => by rw [hcard]; exact (hYd i).1) ?_ ?_
  · intro n hn
    have hnt : ∀ i, n i ≤ top i := fun i => (hgrid n hn i).2
    have hSn : ∀ i, T.S (LL.setTies T n) i ≤ n i := fun i =>
      (S_mono LL T n top hnt i).trans ((hS i).trans (hgrid n hn i).1)
    have hdegn : ∀ x, (LL.setTies T n).deg x ≤ Xb := fun x =>
      (setTies_deg_mono LL T n top hnt x).trans (hdeg x)
    obtain ⟨hP, hW, hL4⟩ := hHyp n hn
    have key := hPW p N r LL T Xb E κ lgv e1 n ρ hp2 hr hρ hadm hE hSn hdegn hL hκ he1 hP hW
      (fun i w => nb i ((LL.setTies T n).takeD (T.pos i + 1)) w)
      (fun i w => fb i ((LL.setTies T n).takeD (T.pos i + 1)) w)
      (fun i w => Uc _ (MatF i ((LL.setTies T n).takeD (T.pos i + 1)) w (n i)))
      (fun i w => Vc _ (MatF i ((LL.setTies T n).takeD (T.pos i + 1)) w (n i)))
      (fun i w => dgc _ (MatF i ((LL.setTies T n).takeD (T.pos i + 1)) w (n i)))
      (fun i w => fw i ((LL.setTies T n).takeD (T.pos i + 1)) w)
      (fun i w => ⟨hli _ _ _, hsp _ _ _⟩) (fun i w => hUc _ _) (fun i w => hfw _ _ _)
    refine key.trans (le_of_eq (Finset.sum_congr rfl fun i _ => ?_))
    apply finsum_eq_sum_of_support_subset
    intro w hw
    by_contra hwn
    apply hw
    have h0 := hcnt0 i ((LL.setTies T n).takeD (T.pos i + 1)) w (n i) hwn
    simp only [cntF] at h0
    simp only [h0, Nat.cast_zero, zero_mul]
  · intro i n hn
    have hnt : ∀ i, n i ≤ top i := fun i => (hgrid n hn i).2
    obtain ⟨hlt, hvW, _⟩ := hadm.2.1 i
    obtain ⟨_, _, hL4⟩ := hHyp n hn
    have hLW : ∀ y, (LL.setTies T (Function.update n i y)).takeD (T.pos i + 1) =
        (LL.setTies T n).takeD (T.pos i + 1) := fun y => takeD_setTies_update LL T n i y
    have hL0S : ((LL.setTies T n).takeD (T.pos i + 1)).total ≤ T.S (LL.setTies T top) i := by
      rw [takeD_total_eq (LL.setTies T n) T i hlt]; exact S_mono LL T n top hnt i
    have hL0tot : ((LL.setTies T n).takeD (T.pos i + 1)).total ≤ n₀ i := hL0S.trans (hS i)
    have hvec : ((LL.setTies T n).takeD (T.pos i + 1)).vec (Fin.last (T.pos i)) = true := by
      simp only [Letters.takeD, Fin.val_last]
      rw [dif_pos (by omega)]
      exact hvW
    have h2S : 2 * ((LL.setTies T n).takeD (T.pos i + 1)).total ≤ Xb := by
      exact (Nat.mul_le_mul_left 2 hL0S).trans (hsz i).1
    have hzo : T.z i + ((LL.setTies T n).takeD (T.pos i + 1)).deg (Fin.last (T.pos i)) ≤ Xb := by
      have h1 := (hsz i).2.2 (by omega)
      have h2 : ((LL.setTies T n).takeD (T.pos i + 1)).deg (Fin.last (T.pos i)) =
          (LL.setTies T n).deg ⟨T.pos i, by omega⟩ := by
        simp only [Letters.takeD, Fin.val_last]
        rw [dif_pos (by omega)]
      have h3 := setTies_deg_mono LL T n top hnt ⟨T.pos i, by omega⟩
      rw [h2]
      exact (Nat.add_le_add_left h3 _).trans h1
    have hκi : ((((T.pos i : ℕ) : ℝ) + 4) * r + 6 : ℝ) * lgv ≤ κ := by
      refine le_trans ?_ hκ32
      have hP4 : ((T.pos i : ℕ) : ℝ) + 4 ≤ (N : ℝ) + 2 := by
        have : T.pos i + 4 ≤ N + 2 := by omega
        exact_mod_cast this
      have hP0 : (0 : ℝ) ≤ ((T.pos i : ℕ) : ℝ) := Nat.cast_nonneg _
      have hr' : (2 : ℝ) ≤ r := by exact_mod_cast hr
      have hN4 : (4 : ℝ) ≤ (N : ℝ) + 2 := by linarith
      have g1 : 2 * (((N : ℝ) + 2) * r) ≤ ((N : ℝ) + 2) * (r : ℝ) ^ 2 := by
        have := mul_nonneg (mul_nonneg (by linarith : (0 : ℝ) ≤ (N : ℝ) + 2) (by linarith : (0 : ℝ) ≤ (r : ℝ)))
          (sub_nonneg.mpr hr')
        nlinarith
      have g2 : (8 : ℝ) ≤ ((N : ℝ) + 2) * r := by
        have := mul_le_mul hN4 hr' (by norm_num) (by linarith)
        linarith
      have g3 : (((T.pos i : ℕ) : ℝ) + 4) * r ≤ ((N : ℝ) + 2) * r := mul_le_mul_of_nonneg_right hP4 (by linarith)
      have g4 : (((T.pos i : ℕ) : ℝ) + 4) * r + 6 ≤ 3 / 2 * (((N : ℝ) + 2) * (r : ℝ) ^ 2) := by linarith
      calc ((((T.pos i : ℕ) : ℝ) + 4) * r + 6 : ℝ) * lgv
          ≤ (3 / 2 * (((N : ℝ) + 2) * (r : ℝ) ^ 2)) * lgv := mul_le_mul_of_nonneg_right g4 hlg
        _ = 3 / 2 * (((N : ℝ) + 2) * (r : ℝ) ^ 2 * lgv) := by ring
    set L0 := (LL.setTies T n).takeD (T.pos i + 1) with hL0
    have qe1 : ∀ y, BB i (Function.update n i y) = ∑ w ∈ Bx i L0, (cntF i L0 w y : ℝ) *
        (Module.finrank ℚ_[p] (T.YYsp p LL i ρ (Function.update n i y) (fw i L0 w)) : ℝ) := by
      intro y
      simp only [BB]
      rw [hLW y, Function.update_self]
    simp only [qe1]

    have hmono : ∀ y ∈ sI i, ∀ w, (cntF i L0 w y : ℝ) *
        (Module.finrank ℚ_[p] (T.YYsp p LL i ρ (Function.update n i y) (fw i L0 w)) : ℝ) ≤
        (cntF i L0 w y : ℝ) *
        (Module.finrank ℚ_[p] (T.YYsp p LL i ρ (Function.update n i (top i)) (fw i L0 w)) : ℝ) := by
      intro y hy w
      by_cases hM : MMw p L0 T.J (T.thrUpTo i) ρ w = ⊥
      · have : cntF i L0 w y = 0 := Nat.eq_zero_of_le_zero
          ((hcntle i L0 w y).trans (by rw [hnb, hM, finrank_bot]))
        simp [this]
      · apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
        have hm := hMono p N r LL T hadm ρ hρ hr i (Function.update n i y) w (fw i L0 w)
          (by rw [hLW y]; exact (hfw i L0 w).1) ((hfw i L0 w).2 hM)
          (by rw [hLW y, Function.update_self]; exact hL0tot.trans (hsI i y hy).1) (top i)
          (by rw [Function.update_self]; exact (hsI i y hy).2)
        rw [Function.update_idem] at hm
        exact_mod_cast hm

    have hmean : ∀ w ∈ Bx i L0, (∑ y ∈ sI i, (cntF i L0 w y : ℝ)) ≤
        (Yl i : ℝ) * ((nb i L0 w : ℝ) * (2 * (T.S (LL.setTies T top) i : ℝ) / Yl i +
          (2 * κ + 2 * (T.S (LL.setTies T top) i : ℝ) * lgv / Yl i) / E)) := by
      intro w _
      have hm := hMG p (T.pos i) r L0 T.J (T.thrUpTo i) ρ (T.z i) w (nb i L0 w) (fb i L0 w) (ord i L0 w)
        (n₀ i) (dd i) (Yl i) Xb E κ κ4 lgv (fun j => Uc _ (MatF i L0 w (n₀ i + dd i * j)))
        (fun j => Vc _ (MatF i L0 w (n₀ i + dd i * j))) (fun j => dgc _ (MatF i L0 w (n₀ i + dd i * j)))
        hρ hr hvec (hli _ _ _) (hsp _ _ _) (hord _ _ _) (hfil _ _ _) hE (hYd i).1 (hYd i).2.1 (hYd i).2.2
        hL0tot h2S hzo (hsz i).2.1 hrX hL hκi (hL4 i) (fun j _ => hUc _ _)
      have hY0 : (0 : ℝ) < Yl i := by exact_mod_cast (hYd i).1
      rw [div_le_iff₀ hY0] at hm
      have hsum : (∑ y ∈ sI i, (cntF i L0 w y : ℝ)) =
          ∑ j ∈ range (Yl i), ((univ.filter (fun b =>
            ‖dgc _ (MatF i L0 w (n₀ i + dd i * j)) b‖ < (p : ℝ) ^ (-E))).card : ℝ) := by
        simp only [sI]
        rw [Finset.sum_image (hinj i)]
      rw [hsum]
      refine hm.trans ?_
      rw [mul_comm]
      apply mul_le_mul_of_nonneg_left _ hY0.le
      apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
      have hE0 : (0 : ℝ) < E := by linarith
      have hL : ((L0.total : ℕ) : ℝ) ≤ (T.S (LL.setTies T top) i : ℝ) := by exact_mod_cast hL0S
      have hC : κ + 3 * lgv + κ4 ≤ 2 * κ := by linarith
      gcongr

    have hcount : (∑ w ∈ Bx i L0, (nb i L0 w : ℝ) *
        (Module.finrank ℚ_[p] (T.YYsp p LL i ρ (Function.update n i (top i)) (fw i L0 w)) : ℝ)) =
        (Module.finrank ℚ_[p] (Y p (r := r) (LL.setTies T (Function.update n i (top i))) T.J T.thr) : ℝ) := by
      have hc := hCount p N r LL T hadm ρ hρ hr i (Function.update n i (top i))
        (by rw [hLW, Function.update_self]; exact hL0tot.trans (Nat.le_add_right _ _)) (fun w => fw i L0 w)
        (fun w => by rw [hLW]; exact hfw i L0 w)
      rw [hLW] at hc
      rw [finsum_eq_sum_of_support_subset _ (s := Bx i L0) (fun w hw => by
        by_contra hwn
        apply hw
        beta_reduce
        rw [← hnb, hnb0 i L0 w hwn, zero_mul])] at hc
      rw [← hc]
      push_cast
      apply Finset.sum_congr rfl
      intro w _
      rw [hnb]
    calc ∑ y ∈ sI i, ∑ w ∈ Bx i L0, (cntF i L0 w y : ℝ) *
            (Module.finrank ℚ_[p] (T.YYsp p LL i ρ (Function.update n i y) (fw i L0 w)) : ℝ)
        ≤ ∑ y ∈ sI i, ∑ w ∈ Bx i L0, (cntF i L0 w y : ℝ) *
            (Module.finrank ℚ_[p] (T.YYsp p LL i ρ (Function.update n i (top i)) (fw i L0 w)) : ℝ) :=
          Finset.sum_le_sum fun y hy => Finset.sum_le_sum fun w _ => hmono y hy w
      _ = ∑ w ∈ Bx i L0, (∑ y ∈ sI i, (cntF i L0 w y : ℝ)) *
            (Module.finrank ℚ_[p] (T.YYsp p LL i ρ (Function.update n i (top i)) (fw i L0 w)) : ℝ) := by
          rw [Finset.sum_comm]
          simp only [Finset.sum_mul]
      _ ≤ ∑ w ∈ Bx i L0, ((Yl i : ℝ) * ((nb i L0 w : ℝ) * (2 * (T.S (LL.setTies T top) i : ℝ) / Yl i +
          (2 * κ + 2 * (T.S (LL.setTies T top) i : ℝ) * lgv / Yl i) / E))) *
            (Module.finrank ℚ_[p] (T.YYsp p LL i ρ (Function.update n i (top i)) (fw i L0 w)) : ℝ) :=
          Finset.sum_le_sum fun w hw => mul_le_mul_of_nonneg_right (hmean w hw) (Nat.cast_nonneg _)
      _ = (sI i).card * ((2 * (T.S (LL.setTies T top) i : ℝ) / Yl i +
          (2 * κ + 2 * (T.S (LL.setTies T top) i : ℝ) * lgv / Yl i) / E) *
            ∑ w ∈ Bx i L0, (nb i L0 w : ℝ) *
              (Module.finrank ℚ_[p] (T.YYsp p LL i ρ (Function.update n i (top i)) (fw i L0 w)) : ℝ)) := by
          rw [hcard, Finset.mul_sum, Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro w _
          ring
      _ = _ := by rw [hcount]

end Formalism.InvariantFactorPaths.MC

import Formalism.LocalToGlobal.TorsionIntegrality.GaussSumParity.BiextensionHypothesesOfLevelOne
import Formalism.LocalToGlobal.TorsionIntegrality.GaussSumParity.StatementK

noncomputable section
open scoped BigOperators

namespace Formalism.L2.Th1.D

open Formalism.InvariantFactorPaths.G7 (UnrOK)

namespace TraceDualSums

/- English proof (translation)
Consider the cases of `d with`. Consider the case `zero => exact absurd rfl (NeZero.ne 0)`. Consider the case `succ n`. Rewrite using `[Finset.sum_range]`. Both sides reduce to the same expression.
-/
lemma sum_zmod {M : Type} [AddCommMonoid M] (d : ℕ) [NeZero d] (F : ℕ → M) :
    (∑ s : ZMod d, F s.val) = ∑ i ∈ Finset.range d, F i := by
  cases d with
  | zero => exact absurd rfl (NeZero.ne 0)
  | succ n =>
    rw [Finset.sum_range]
    rfl

/- English proof (translation)
Proceed by induction on `m with`. Consider the case `zero => simp`. Consider the case `succ m ih`. Rewrite using `[show 2 * (m + 1) = 2 * m + 1 + 1 by ring, Finset.sum_range_succ, Finset.sum_range_succ, ih, Finset.sum_range_succ]`. Establish `h1 : (2 * m) % 2 = 0` using `by omega`.

Establish `h2 : ¬ (2 * m + 1) % 2 = 0` using `by omega`. Rewrite using `[if_pos h1, if_neg h2, add_zero]`.
-/
lemma sum_range_even {M : Type} [AddCommMonoid M] (m : ℕ) (g : ℕ → M) :
    (∑ i ∈ Finset.range (2 * m), if i % 2 = 0 then g i else 0) =
      ∑ k ∈ Finset.range m, g (2 * k) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [show 2 * (m + 1) = 2 * m + 1 + 1 by ring, Finset.sum_range_succ, Finset.sum_range_succ, ih,
      Finset.sum_range_succ]
    have h1 : (2 * m) % 2 = 0 := by omega
    have h2 : ¬ (2 * m + 1) % 2 = 0 := by omega
    rw [if_pos h1, if_neg h2, add_zero]

/- English proof (translation)
Rewrite using `[Matrix.det_apply]`. Use `IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one ?_` and prove the remaining obligations. Introduce `p _`. Rewrite using `[Units.smul_def, zsmul_eq_mul, norm_mul, norm_prod]`. Conclude with `mul_le_one₀ (IsUltrametricDist.norm_intCast_le_one K _) (Finset.prod_nonneg fun _ _ => norm_nonneg _) (Finset.prod_le_one (fun _ _ => norm_nonneg _) fun i _ => h _ _)`.
-/
lemma norm_det_le {K : Type} [NormedField K] [IsUltrametricDist K] {n : Type} [Fintype n]
    [DecidableEq n] (M : Matrix n n K) (h : ∀ i j, ‖M i j‖ ≤ 1) : ‖M.det‖ ≤ 1 := by
  rw [Matrix.det_apply]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one ?_
  intro p _
  rw [Units.smul_def, zsmul_eq_mul, norm_mul, norm_prod]
  exact mul_le_one₀ (IsUltrametricDist.norm_intCast_le_one K _)
    (Finset.prod_nonneg fun _ _ => norm_nonneg _)
    (Finset.prod_le_one (fun _ _ => norm_nonneg _) fun i _ => h _ _)

/- English proof (translation)
Establish `h1 : (V.map τ) * (P.map τ) = 1`. Rewrite using `[← Matrix.map_mul, hVP]`. Conclude with `Matrix.map_one τ (map_zero τ) (map_one τ)`. Establish `h2 : V.map τ = V.submatrix (Equiv.addRight (1 : Fin m)) id`. Use extensionality with `k r`.

Conclude with `hV k r`. Establish `h3 : (V.submatrix (Equiv.addRight (1 : Fin m)) id) * (P.submatrix id (Equiv.addRight (1 : Fin m))) = 1`. Rewrite using `[← Matrix.submatrix_mul _ _ _ _ _ Function.bijective_id, hVP, Matrix.submatrix_one_equiv]`. Establish `h4 : P.map τ = P.submatrix id (Equiv.addRight (1 : Fin m))`. Rewrite using `[← Matrix.inv_eq_right_inv h1, h2, Matrix.inv_eq_right_inv h3]`.

Introduce `r k`. Conclude with `congrFun (congrFun h4 r) k`.
-/
lemma inv_shift {K : Type} [Field K] {m : ℕ} [NeZero m] (τ : K →+* K)
    (V P : Matrix (Fin m) (Fin m) K) (hVP : V * P = 1)
    (hV : ∀ k r, τ (V k r) = V (k + 1) r) : ∀ r k, τ (P r k) = P r (k + 1) := by
  have h1 : (V.map τ) * (P.map τ) = 1 := by
    rw [← Matrix.map_mul, hVP]
    exact Matrix.map_one τ (map_zero τ) (map_one τ)
  have h2 : V.map τ = V.submatrix (Equiv.addRight (1 : Fin m)) id := by
    ext k r
    exact hV k r
  have h3 : (V.submatrix (Equiv.addRight (1 : Fin m)) id) *
      (P.submatrix id (Equiv.addRight (1 : Fin m))) = 1 := by
    rw [← Matrix.submatrix_mul _ _ _ _ _ Function.bijective_id, hVP, Matrix.submatrix_one_equiv]
  have h4 : P.map τ = P.submatrix id (Equiv.addRight (1 : Fin m)) := by
    rw [← Matrix.inv_eq_right_inv h1, h2, Matrix.inv_eq_right_inv h3]
  intro r k
  exact congrFun (congrFun h4 r) k

end TraceDualSums

open TraceDualSums Fin.NatCast in
/- English proof (translation)
Introduce `K _ _ _ l d _ σ hU hd ζ hζ`. Take `⟨m, rfl⟩` from `hd`. Establish `hd0 : m + m ≠ 0` using `NeZero.ne (m + m)`. Establish `hm0 : m ≠ 0` using `by omega`. Establish `hdm : (m + m) / 2 = m` using `by omega`.

Rewrite using `[hdm]`. Establish `: NeZero m` using `⟨hm0⟩`. Establish `hp : l.Prime` using `hU.1`. Establish `hl3 : 2 < l` using `hU.2.1`. Establish `hlt : ‖(l : K)‖ < 1`.

Rewrite using `[hU.2.2.1]`. Conclude with `inv_lt_one_of_one_lt₀ (by exact_mod_cast hp.one_lt)`. Establish `hpos : 1 ≤ l ^ (m + m)` using `Nat.one_le_pow _ _ hp.pos`. Establish `hnd : ¬ l ∣ l ^ (m + m) - 1`. Introduce `h`.

Establish `h1 : l ∣ l ^ (m + m)` using `dvd_pow_self l hd0`. Establish `h2 : l ∣ 1`. Use `(Nat.dvd_sub h1 h)` as an intermediate fact. Rewrite `this` using `[Nat.sub_sub_self hpos]`. Then use the resulting hypothesis. Conclude with `hp.one_lt.ne' (Nat.dvd_one.1 h2)`.

Establish `hN : ‖((l ^ (m + m) - 1 : ℕ) : K)‖ = 1` using `Formalism.DworkPowerSeriesWeights.norm_natCast_eq_one_of_not_dvd hp hlt hnd`. Establish `hN0 : l ^ (m + m) - 1 ≠ 0`. Introduce `h`. Rewrite `hnd` using `[h]`. Conclude with `hnd (dvd_zero l)`.

Establish `nζ : ‖ζ‖ = 1` using `FormalExponential.norm_eq_one_of_pow hN0 hζ.pow_eq_one`. Establish `hσζ : σ ζ = ζ ^ l` using `teichSigma K l (m + m) σ hU (by omega) ζ hζ.pow_eq_one`. Establish `hit : ∀ j, σ^[j] ζ = ζ ^ (l ^ j)` using `B4.iterate_of_pow hσζ`. Establish `hper : σ^[m + m] ζ = ζ`. Rewrite using `[hit, show l ^ (m + m) = (l ^ (m + m) - 1) + 1 by omega, pow_succ, hζ.pow_eq_one, one_mul]`.

Set `τ : K →+* K` to `σ.comp σ`. Establish `hτ : ∀ (k : ℕ) (a : K), τ^[k] a = σ^[2 * k] a`. Introduce `k a`. Rewrite using `[Function.iterate_mul]`. Both sides reduce to the same expression.

Establish `hper' : Function.IsPeriodicPt τ m ζ` using `by show τ^[m] ζ = ζ`. Rewrite using `[hτ, two_mul]`. Conclude with `hper`. Set `x : Fin m → K` to `fun k => σ^[2 * k.val] ζ`. Establish `hxn : ∀ j : ℕ, x (j : Fin m) = τ^[j] ζ`.

Introduce `j`. Use `show σ^[2 * ((j : Fin m) : ℕ)] ζ = _`. Rewrite using `[Fin.val_natCast, ← hτ, hper'.iterate_mod_apply]`. Establish `hxs : ∀ k, τ (x k) = x (k + 1)`. Introduce `k`.

Establish `h : k + 1 = ((k.val + 1 : ℕ) : Fin m)`. Rewrite using `[Nat.cast_succ, Fin.cast_val_eq_self]`. Rewrite using `[h, hxn, Function.iterate_succ_apply', ← hxn, Fin.cast_val_eq_self]`. Set `V : Matrix (Fin m) (Fin m) K` to `Matrix.vandermonde x`. Establish `hVa : ∀ k r, V k r = x k ^ (r : ℕ)` using `fun k r => Matrix.vandermonde_apply x k r`.

Establish `hVs : ∀ k r, τ (V k r) = V (k + 1) r`. Introduce `k r`. Rewrite using `[hVa, hVa, map_pow, hxs]`. Establish `hxpow : ∀ k, x k = ζ ^ (l ^ (2 * k.val))` using `fun k => hit _`. Establish `hxN : ∀ k, x k ^ (l ^ (m + m) - 1) = 1`.

Introduce `k`. Rewrite using `[hxpow, ← pow_mul, mul_comm, pow_mul, hζ.pow_eq_one, one_pow]`. Establish `nx : ∀ k, ‖x k‖ = 1` using `fun k => FormalExponential.norm_eq_one_of_pow hN0 (hxN k)`. Establish `hsmall : ∀ k : Fin m, l ^ (2 * k.val) < l ^ (m + m) - 1`. Introduce `k`.

Establish `hk` using `k.2`. Establish `h1 : l ^ (2 * k.val) ≤ l ^ (m + m - 1)` using `Nat.pow_le_pow_right hp.pos (by omega)`. Establish `h2 : l ^ (m + m) = l ^ (m + m - 1) * l`. Rewrite using `[← pow_succ]`. Use `congr 1`.

Use linear arithmetic over natural numbers and integers. Establish `h3 : 1 ≤ l ^ (m + m - 1)` using `Nat.one_le_pow _ _ hp.pos`. Establish `h4 : l ^ (m + m - 1) * 3 ≤ l ^ (m + m - 1) * l` using `Nat.mul_le_mul_left _ hl3`. Use linear arithmetic over natural numbers and integers. Establish `hinj : Function.Injective x`.

Introduce `i j hij`. Rewrite `hij` using `[hxpow, hxpow]`. Establish `h1` using `hζ.pow_inj (hsmall i) (hsmall j) hij`. Establish `h2` using `Nat.pow_right_injective hp.two_le h1`. Conclude with `Fin.ext (by omega)`.

Establish `hdiff : ∀ i j, i ≠ j → ‖x j - x i‖ = 1`. Introduce `i j hij`. Use `le_antisymm ?_ ?_` and prove the remaining obligations. Rewrite using `[sub_eq_add_neg]`. Use `(IsUltrametricDist.norm_add_le_max _ _).trans ?_` and prove the remaining obligations.

Rewrite using `[norm_neg, nx, nx, max_self]`. Assume the negation of the conclusion as `hlt'`. Conclude with `hij (hinj (FormalExponential.root_eq_of_norm_lt hN (hxN j) (hxN i) (not_le.1 hlt'))).symm`. Establish `hdet : ‖V.det‖ = 1`. Rewrite using `[Matrix.det_vandermonde, norm_prod]`.

Use `Finset.prod_eq_one fun i _ => ?_` and prove the remaining obligations. Rewrite using `[norm_prod]`. Conclude with `Finset.prod_eq_one fun j hj => hdiff i j (ne_of_lt (Finset.mem_Ioi.1 hj))`. Establish `hdet0 : V.det ≠ 0`. Introduce `h`.

Rewrite `hdet` using `[h, norm_zero]`. Conclude with `zero_ne_one hdet`. Set `P : Matrix (Fin m) (Fin m) K` to `V⁻¹`. Establish `hVP : V * P = 1` using `Matrix.mul_nonsing_inv V (isUnit_iff_ne_zero.2 hdet0)`. Establish `hPV : P * V = 1` using `Matrix.nonsing_inv_mul V (isUnit_iff_ne_zero.2 hdet0)`.

Establish `hVint : ∀ k r, ‖V k r‖ ≤ 1`. Introduce `k r`. Rewrite using `[hVa, norm_pow, nx, one_pow]`. Establish `hPint : ∀ r k, ‖P r k‖ ≤ 1`. Introduce `r k`.

Use `show ‖(V⁻¹) r k‖ ≤ 1`. Rewrite using `[Matrix.inv_def, Matrix.smul_apply, smul_eq_mul, Ring.inverse_eq_inv', norm_mul, norm_inv, hdet, inv_one, one_mul, Matrix.adjugate_apply]`. Use `norm_det_le _ fun i j => ?_` and prove the remaining obligations. Rewrite using `[Matrix.updateRow_apply]`. Use `split_ifs`.

Apply the tactic sequence `rw [Pi.single_apply] split_ifs <;> simp`. Conclude with `hVint i j`. Establish `hPs` using `inv_shift τ V P hVP hVs`. Establish `hPn : ∀ (r : Fin m) (j : ℕ), τ^[j] (P r 0) = P r (j : Fin m)`. Introduce `r j`.

Proceed by induction on `j with`. Consider the case `zero => simp`. Consider the case `succ j ih => rw [Function.iterate_succ_apply', ih, hPs, Nat.cast_succ]`. Use `⟨fun r => ζ ^ (r : ℕ), fun r => P r 0, ⟨fun r => ⟨by rw [norm_pow, nζ, one_pow], hPint r 0⟩, fun r => ⟨?_, ?_⟩⟩, ⟨?_, ?_⟩⟩` and prove the remaining obligations. Use `show σ^[m + m] (ζ ^ (r : ℕ)) = ζ ^ (r : ℕ)`.

Rewrite using `[iterate_map_pow, hper]`. Use `show σ^[m + m] (P r 0) = P r 0`. Rewrite using `[← two_mul, ← hτ, hPn, Fin.natCast_self]`. Rewrite using `[Fintype.card_fin, two_mul]`. Introduce `r r' show (∑ s : ZMod (m + m), if s.val % 2 = 0 then σ^[s.val] (ζ ^ (r : ℕ) * P r' 0) else 0) = _`.

Rewrite using `[sum_zmod (m + m) (fun i => if i % 2 = 0 then σ^[i] (ζ ^ (r : ℕ) * P r' 0) else 0), ← two_mul, sum_range_even m (fun i => σ^[i] (ζ ^ (r : ℕ) * P r' 0)), Finset.sum_range]`. Establish `hterm : ∀ k : Fin m, σ^[2 * (k : ℕ)] (ζ ^ (r : ℕ) * P r' 0) = P r' k * V k r`. Introduce `k`. Rewrite using `[iterate_map_mul, iterate_map_pow, ← hτ k.val (P r' 0), hPn, Fin.cast_val_eq_self, hVa, mul_comm]`. Rewrite using `[Finset.sum_congr rfl fun k _ => hterm k, ← Matrix.mul_apply, hPV, Matrix.one_apply]`.

Simplify using `only [eq_comm]`.
-/
theorem trace_dual_exists : TrDualExists := by
  intro K _ _ _ l d _ σ hU hd ζ hζ
  obtain ⟨m, rfl⟩ := hd
  have hd0 : m + m ≠ 0 := NeZero.ne (m + m)
  have hm0 : m ≠ 0 := by omega
  have hdm : (m + m) / 2 = m := by omega
  rw [hdm]
  have : NeZero m := ⟨hm0⟩
  have hp : l.Prime := hU.1
  have hl3 : 2 < l := hU.2.1
  have hlt : ‖(l : K)‖ < 1 := by
    rw [hU.2.2.1]
    exact inv_lt_one_of_one_lt₀ (by exact_mod_cast hp.one_lt)
  have hpos : 1 ≤ l ^ (m + m) := Nat.one_le_pow _ _ hp.pos
  have hnd : ¬ l ∣ l ^ (m + m) - 1 := by
    intro h
    have h1 : l ∣ l ^ (m + m) := dvd_pow_self l hd0
    have h2 : l ∣ 1 := by
      have := (Nat.dvd_sub h1 h)
      rwa [Nat.sub_sub_self hpos] at this
    exact hp.one_lt.ne' (Nat.dvd_one.1 h2)
  have hN : ‖((l ^ (m + m) - 1 : ℕ) : K)‖ = 1 :=
    Formalism.DworkPowerSeriesWeights.norm_natCast_eq_one_of_not_dvd hp hlt hnd
  have hN0 : l ^ (m + m) - 1 ≠ 0 := by
    intro h
    rw [h] at hnd
    exact hnd (dvd_zero l)
  have nζ : ‖ζ‖ = 1 := FormalExponential.norm_eq_one_of_pow hN0 hζ.pow_eq_one
  have hσζ : σ ζ = ζ ^ l := teichSigma K l (m + m) σ hU (by omega) ζ hζ.pow_eq_one
  have hit : ∀ j, σ^[j] ζ = ζ ^ (l ^ j) := B4.iterate_of_pow hσζ
  have hper : σ^[m + m] ζ = ζ := by
    rw [hit, show l ^ (m + m) = (l ^ (m + m) - 1) + 1 by omega, pow_succ, hζ.pow_eq_one, one_mul]
  let τ : K →+* K := σ.comp σ
  have hτ : ∀ (k : ℕ) (a : K), τ^[k] a = σ^[2 * k] a := by
    intro k a
    rw [Function.iterate_mul]
    rfl
  have hper' : Function.IsPeriodicPt τ m ζ := by
    show τ^[m] ζ = ζ
    rw [hτ, two_mul]
    exact hper
  let x : Fin m → K := fun k => σ^[2 * k.val] ζ
  have hxn : ∀ j : ℕ, x (j : Fin m) = τ^[j] ζ := by
    intro j
    show σ^[2 * ((j : Fin m) : ℕ)] ζ = _
    rw [Fin.val_natCast, ← hτ, hper'.iterate_mod_apply]
  have hxs : ∀ k, τ (x k) = x (k + 1) := by
    intro k
    have h : k + 1 = ((k.val + 1 : ℕ) : Fin m) := by
      rw [Nat.cast_succ, Fin.cast_val_eq_self]
    rw [h, hxn, Function.iterate_succ_apply', ← hxn, Fin.cast_val_eq_self]
  let V : Matrix (Fin m) (Fin m) K := Matrix.vandermonde x
  have hVa : ∀ k r, V k r = x k ^ (r : ℕ) := fun k r => Matrix.vandermonde_apply x k r
  have hVs : ∀ k r, τ (V k r) = V (k + 1) r := by
    intro k r
    rw [hVa, hVa, map_pow, hxs]
  have hxpow : ∀ k, x k = ζ ^ (l ^ (2 * k.val)) := fun k => hit _
  have hxN : ∀ k, x k ^ (l ^ (m + m) - 1) = 1 := by
    intro k
    rw [hxpow, ← pow_mul, mul_comm, pow_mul, hζ.pow_eq_one, one_pow]
  have nx : ∀ k, ‖x k‖ = 1 := fun k => FormalExponential.norm_eq_one_of_pow hN0 (hxN k)
  have hsmall : ∀ k : Fin m, l ^ (2 * k.val) < l ^ (m + m) - 1 := by
    intro k
    have hk := k.2
    have h1 : l ^ (2 * k.val) ≤ l ^ (m + m - 1) := Nat.pow_le_pow_right hp.pos (by omega)
    have h2 : l ^ (m + m) = l ^ (m + m - 1) * l := by
      rw [← pow_succ]
      congr 1
      omega
    have h3 : 1 ≤ l ^ (m + m - 1) := Nat.one_le_pow _ _ hp.pos
    have h4 : l ^ (m + m - 1) * 3 ≤ l ^ (m + m - 1) * l := Nat.mul_le_mul_left _ hl3
    omega
  have hinj : Function.Injective x := by
    intro i j hij
    rw [hxpow, hxpow] at hij
    have h1 := hζ.pow_inj (hsmall i) (hsmall j) hij
    have h2 := Nat.pow_right_injective hp.two_le h1
    exact Fin.ext (by omega)
  have hdiff : ∀ i j, i ≠ j → ‖x j - x i‖ = 1 := by
    intro i j hij
    refine le_antisymm ?_ ?_
    · rw [sub_eq_add_neg]
      refine (IsUltrametricDist.norm_add_le_max _ _).trans ?_
      rw [norm_neg, nx, nx, max_self]
    · by_contra hlt'
      exact hij (hinj (FormalExponential.root_eq_of_norm_lt hN (hxN j) (hxN i) (not_le.1 hlt'))).symm
  have hdet : ‖V.det‖ = 1 := by
    rw [Matrix.det_vandermonde, norm_prod]
    refine Finset.prod_eq_one fun i _ => ?_
    rw [norm_prod]
    exact Finset.prod_eq_one fun j hj => hdiff i j (ne_of_lt (Finset.mem_Ioi.1 hj))
  have hdet0 : V.det ≠ 0 := by
    intro h
    rw [h, norm_zero] at hdet
    exact zero_ne_one hdet
  let P : Matrix (Fin m) (Fin m) K := V⁻¹
  have hVP : V * P = 1 := Matrix.mul_nonsing_inv V (isUnit_iff_ne_zero.2 hdet0)
  have hPV : P * V = 1 := Matrix.nonsing_inv_mul V (isUnit_iff_ne_zero.2 hdet0)
  have hVint : ∀ k r, ‖V k r‖ ≤ 1 := by
    intro k r
    rw [hVa, norm_pow, nx, one_pow]
  have hPint : ∀ r k, ‖P r k‖ ≤ 1 := by
    intro r k
    show ‖(V⁻¹) r k‖ ≤ 1
    rw [Matrix.inv_def, Matrix.smul_apply, smul_eq_mul, Ring.inverse_eq_inv', norm_mul, norm_inv,
      hdet, inv_one, one_mul, Matrix.adjugate_apply]
    refine norm_det_le _ fun i j => ?_
    rw [Matrix.updateRow_apply]
    split_ifs
    · rw [Pi.single_apply]
      split_ifs <;> simp
    · exact hVint i j
  have hPs := inv_shift τ V P hVP hVs
  have hPn : ∀ (r : Fin m) (j : ℕ), τ^[j] (P r 0) = P r (j : Fin m) := by
    intro r j
    induction j with
    | zero => simp
    | succ j ih => rw [Function.iterate_succ_apply', ih, hPs, Nat.cast_succ]
  refine ⟨fun r => ζ ^ (r : ℕ), fun r => P r 0,
    ⟨fun r => ⟨by rw [norm_pow, nζ, one_pow], hPint r 0⟩, fun r => ⟨?_, ?_⟩⟩, ⟨?_, ?_⟩⟩
  · show σ^[m + m] (ζ ^ (r : ℕ)) = ζ ^ (r : ℕ)
    rw [iterate_map_pow, hper]
  · show σ^[m + m] (P r 0) = P r 0
    rw [← two_mul, ← hτ, hPn, Fin.natCast_self]
  · rw [Fintype.card_fin, two_mul]
  · intro r r'
    show (∑ s : ZMod (m + m), if s.val % 2 = 0 then σ^[s.val] (ζ ^ (r : ℕ) * P r' 0) else 0) = _
    rw [sum_zmod (m + m) (fun i => if i % 2 = 0 then σ^[i] (ζ ^ (r : ℕ) * P r' 0) else 0),
      ← two_mul, sum_range_even m (fun i => σ^[i] (ζ ^ (r : ℕ) * P r' 0)), Finset.sum_range]
    have hterm : ∀ k : Fin m, σ^[2 * (k : ℕ)] (ζ ^ (r : ℕ) * P r' 0) = P r' k * V k r := by
      intro k
      rw [iterate_map_mul, iterate_map_pow, ← hτ k.val (P r' 0), hPn, Fin.cast_val_eq_self, hVa,
        mul_comm]
    rw [Finset.sum_congr rfl fun k _ => hterm k, ← Matrix.mul_apply, hPV, Matrix.one_apply]
    simp only [eq_comm]

end Formalism.L2.Th1.D

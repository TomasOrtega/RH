import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutGCoreGTCCurvPolyCut

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Polynomial

namespace Formalism.FourierDecayAlt.P.CutMP.Gauge.GC.CurvScal

noncomputable section

/- English proof (translation)
The claim follows from `monic_prod_of_monic _ _ (fun i _ => monic_X_add_C (f i))`.
-/
theorem pl_monic (s : Finset ℕ) (f : ℕ → ℂ) : (∏ i ∈ s, (X + C (f i))).Monic :=
  monic_prod_of_monic _ _ (fun i _ => monic_X_add_C (f i))

/- English proof (translation)
Rewrite using `[natDegree_prod_of_monic _ _ (fun i _ => monic_X_add_C (f i))]`. Simplify using `[natDegree_X_add_C]`.
-/
theorem pl_natDegree (s : Finset ℕ) (f : ℕ → ℂ) : (∏ i ∈ s, (X + C (f i))).natDegree = s.card := by
  rw [natDegree_prod_of_monic _ _ (fun i _ => monic_X_add_C (f i))]
  simp [natDegree_X_add_C]

/- English proof (translation)
Establish `h` using `(pl_monic s f).coeff_natDegree`. Rewrite `h` using `[pl_natDegree]`. Then use the resulting hypothesis.
-/
theorem pl_top (s : Finset ℕ) (f : ℕ → ℂ) : (∏ i ∈ s, (X + C (f i))).coeff s.card = 1 := by
  have h := (pl_monic s f).coeff_natDegree
  rwa [pl_natDegree] at h

/- English proof (translation)
Establish `h` using `nextCoeff_of_natDegree_pos (p := ∏ i ∈ s, (X + C (f i))) (by rw [pl_natDegree]; exact hs)`. Rewrite `h` using `[pl_natDegree]`. Rewrite using `[← h, Monic.nextCoeff_prod _ _ (fun i _ => monic_X_add_C (f i))]`. Simplify using `[nextCoeff_X_add_C]`.
-/
theorem pl_next (s : Finset ℕ) (f : ℕ → ℂ) (hs : 0 < s.card) :
    (∏ i ∈ s, (X + C (f i))).coeff (s.card - 1) = ∑ i ∈ s, f i := by
  have h := nextCoeff_of_natDegree_pos (p := ∏ i ∈ s, (X + C (f i))) (by rw [pl_natDegree]; exact hs)
  rw [pl_natDegree] at h
  rw [← h, Monic.nextCoeff_prod _ _ (fun i _ => monic_X_add_C (f i))]
  simp [nextCoeff_X_add_C]

/- English proof (translation)
The claim follows from `coeff_eq_zero_of_natDegree_lt (by rw [pl_natDegree]; exact hj)`.
-/
theorem pl_high (s : Finset ℕ) (f : ℕ → ℂ) {j : ℕ} (hj : s.card < j) : (∏ i ∈ s, (X + C (f i))).coeff j = 0 :=
  coeff_eq_zero_of_natDegree_lt (by rw [pl_natDegree]; exact hj)

/- English proof (translation)
Rewrite using `[eval_eq_sum_range' h, Finset.sum_range_succ, Finset.sum_range_succ]`. Establish `: ∀ i, p.coeff i * u ^ i = u ^ i * p.coeff i` using `fun i => mul_comm _ _`. Simplify using `only [this]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem top2 (p : ℂ[X]) (N : ℕ) (h : p.natDegree < N + 2) (u : ℂ) :
    p.eval u = u ^ (N + 1) * p.coeff (N + 1) + u ^ N * p.coeff N + ∑ i ∈ Finset.range N, u ^ i * p.coeff i := by
  rw [eval_eq_sum_range' h, Finset.sum_range_succ, Finset.sum_range_succ]
  have : ∀ i, p.coeff i * u ^ i = u ^ i * p.coeff i := fun i => mul_comm _ _
  simp only [this]
  ring

/- English proof (translation)
Simplify using the standard rewrite rules.
-/
theorem card_Icc_one (n : ℕ) : (Finset.Icc 1 n).card = n := by simp

/- English proof (translation)
Establish `h1 : P.k - 1 = m + 1` using `by omega`. Establish `h2 : P.k - 2 = m` using `by omega`. Set `f : ℕ → ℂ` to `fun i => ((M.rho P ρ i : ℝ) : ℂ)`. Use `⟨fun i => (∏ i ∈ Finset.Icc 1 (m + 1), (X + C (f i))).coeff i, fun u => ?_⟩` and prove the remaining obligations. Establish `hx : M.xC P ρ u = (∏ i ∈ Finset.Icc 1 (m + 1), (X + C (f i))).eval u`.

Rewrite using `[eval_prod]`. Unfold `M.xC`. Rewrite using `[h1]`. Simplify using `[f]`. Rewrite using `[hx, top2 _ m (by rw [pl_natDegree, card_Icc_one]; omega) u, h1, h2]`.

Establish `ht` using `pl_top (Finset.Icc 1 (m + 1)) f`. Establish `hn` using `pl_next (Finset.Icc 1 (m + 1)) f (by rw [card_Icc_one]; omega)`. Rewrite `ht`, `hn` using `[card_Icc_one]`. Rewrite `hn` using `[Nat.add_sub_cancel]`. Rewrite using `[ht, hn]`.

Establish `ha : (absTy P ρ : ℂ) = ∑ i ∈ Finset.Icc 1 (m + 1), f i`. Simplify using `only [absTy, h1, f]`. Use `push_cast`. Both sides reduce to the same expression. Rewrite using `[ha]`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem xC_leading_terms_alt (P : M.Par) (m : ℕ) (hm : P.k = m + 2) (ρ : M.Ty P) :
    ∃ c : ℕ → ℂ, ∀ u : ℂ, M.xC P ρ u = u ^ (P.k - 1) + (absTy P ρ : ℂ) * u ^ (P.k - 2) +
        ∑ i ∈ Finset.range (P.k - 2), u ^ i * c i := by
  have h1 : P.k - 1 = m + 1 := by omega
  have h2 : P.k - 2 = m := by omega
  let f : ℕ → ℂ := fun i => ((M.rho P ρ i : ℝ) : ℂ)
  refine ⟨fun i => (∏ i ∈ Finset.Icc 1 (m + 1), (X + C (f i))).coeff i, fun u => ?_⟩
  have hx : M.xC P ρ u = (∏ i ∈ Finset.Icc 1 (m + 1), (X + C (f i))).eval u := by
    rw [eval_prod]; unfold M.xC; rw [h1]; simp [f]
  rw [hx, top2 _ m (by rw [pl_natDegree, card_Icc_one]; omega) u, h1, h2]
  have ht := pl_top (Finset.Icc 1 (m + 1)) f
  have hn := pl_next (Finset.Icc 1 (m + 1)) f (by rw [card_Icc_one]; omega)
  rw [card_Icc_one] at ht hn
  rw [Nat.add_sub_cancel] at hn
  rw [ht, hn]
  have ha : (absTy P ρ : ℂ) = ∑ i ∈ Finset.Icc 1 (m + 1), f i := by
    simp only [absTy, h1, f]; push_cast; rfl
  rw [ha]; ring

/- English proof (translation)
Establish `h1 : P.k - 1 = m + 1` using `by omega`. Set `f : ℕ → ℂ` to `fun i => ((M.rho P ρ i : ℝ) : ℂ)`. Set `s` to `Finset.Icc 1 (m + 1) \ ex`. Establish `hs : s.card < m + 1`. Take `⟨l, hl, hlI⟩` from `hex`.

Rewrite `hlI` using `[h1]`. Establish `hss : s ⊂ Finset.Icc 1 (m + 1)` using `(Finset.ssubset_iff_of_subset Finset.sdiff_subset).2 ⟨l, hlI, by simp [s, hl]⟩`. Use `Finset.card_lt_card hss` as an intermediate fact. Rewrite `this` using `[card_Icc_one]`. Then use the resulting hypothesis. Use `⟨fun i => (∏ i ∈ s, (X + C (f i))).coeff i, fun u => ?_⟩` and prove the remaining obligations.

Establish `hx : M.xEx P ex ρ u = (∏ i ∈ s, (X + C (f i))).eval u`. Rewrite using `[eval_prod]`. Unfold `M.xEx`. Rewrite using `[h1]`. Simplify using `[f, s]`.

Rewrite using `[hx, eval_eq_sum_range' (by rw [pl_natDegree]; omega) u, h1]`. Conclude with `Finset.sum_congr rfl fun i _ => mul_comm _ _`.
-/
theorem part_ex (P : M.Par) (m : ℕ) (hm : P.k = m + 2) (ρ : M.Ty P) (ex : Finset ℕ)
    (hex : ∃ l ∈ ex, l ∈ Finset.Icc 1 (P.k - 1)) :
    ∃ c : ℕ → ℂ, ∀ u : ℂ, M.xEx P ex ρ u = ∑ i ∈ Finset.range (P.k - 1), u ^ i * c i := by
  have h1 : P.k - 1 = m + 1 := by omega
  let f : ℕ → ℂ := fun i => ((M.rho P ρ i : ℝ) : ℂ)
  let s := Finset.Icc 1 (m + 1) \ ex
  have hs : s.card < m + 1 := by
    obtain ⟨l, hl, hlI⟩ := hex
    rw [h1] at hlI
    have hss : s ⊂ Finset.Icc 1 (m + 1) :=
      (Finset.ssubset_iff_of_subset Finset.sdiff_subset).2 ⟨l, hlI, by simp [s, hl]⟩
    have := Finset.card_lt_card hss
    rwa [card_Icc_one] at this
  refine ⟨fun i => (∏ i ∈ s, (X + C (f i))).coeff i, fun u => ?_⟩
  have hx : M.xEx P ex ρ u = (∏ i ∈ s, (X + C (f i))).eval u := by
    rw [eval_prod]; unfold M.xEx; rw [h1]; simp [f, s]
  rw [hx, eval_eq_sum_range' (by rw [pl_natDegree]; omega) u, h1]
  exact Finset.sum_congr rfl fun i _ => mul_comm _ _

/- English proof (translation)
Establish `h1 : P.k - 1 = m + 1` using `by omega`. Set `fx : ℕ → ℂ` to `fun i => ((M.rho P ρ i : ℝ) : ℂ) + 1`. Set `xp` to `∏ i ∈ Finset.Icc 1 (m + 1), (X + C (fx i))`. Establish `hxp : M.coordinatePolynomial P ρ = xp` using `by unfold M.coordinatePolynomial; rw [h1]`. Establish `xmon : xp.Monic` using `pl_monic _ _`.

Establish `xdeg : xp.natDegree = m + 1` using `by rw [pl_natDegree, card_Icc_one]`. Establish `xtop : xp.coeff (m + 1) = 1`. Use `pl_top (Finset.Icc 1 (m + 1)) fx` as an intermediate fact. Rewrite `this` using `[card_Icc_one]`. Then use the resulting hypothesis. Establish `xnext : xp.coeff m = ∑ i ∈ Finset.Icc 1 (m + 1), fx i`.

Use `pl_next (Finset.Icc 1 (m + 1)) fx (by rw [card_Icc_one]; omega)` as an intermediate fact. Rewrite `this` using `[card_Icc_one, Nat.add_sub_cancel]`. Then use the resulting hypothesis. Establish `xhigh : xp.coeff (m + 2) = 0` using `pl_high _ _ (by rw [card_Icc_one]; omega)`. Set `fa : ℕ → ℂ` to `fun i => 1 / 2 + (P.u i : ℂ)`. Set `fb : ℕ → ℂ` to `fun i => 1 / 2 + (P.u' i : ℂ)`.

Set `pa` to `∏ i ∈ Finset.Icc 1 (m + 2), (X + C (fa i))`. Set `pb` to `∏ i ∈ Finset.Icc 1 (m + 2), (X + C (fb i))`. Establish `hT : (-((P.T : ℂ) * (P.T' : ℂ))) = -(P.TT : ℂ)` using `by simp [M.Par.TT]`. Establish `hq : M.qP P = C (-(P.TT : ℂ)) * (pa * pb)`. Unfold `M.qP`.

Rewrite using `[hm, Finset.prod_mul_distrib, hT]`. Establish `abmon : (pa * pb).Monic` using `(pl_monic _ _).mul (pl_monic _ _)`. Establish `abdeg : (pa * pb).natDegree = 2 * m + 4`. Rewrite using `[(pl_monic _ _).natDegree_mul (pl_monic _ _), pl_natDegree, pl_natDegree, card_Icc_one]`. Expand and normalize the polynomial expressions, which then agree.

Establish `abtop : (pa * pb).coeff (2 * m + 4) = 1` using `by rw [← abdeg]; exact abmon.coeff_natDegree`. Establish `abnext : (pa * pb).coeff (2 * m + 3) = ∑ i ∈ Finset.Icc 1 (m + 2), fa i + ∑ i ∈ Finset.Icc 1 (m + 2), fb i`. Establish `h` using `nextCoeff_of_natDegree_pos (p := pa * pb) (by rw [abdeg]; omega)`. Rewrite `h` using `[abdeg, show 2 * m + 4 - 1 = 2 * m + 3 by omega]`. Rewrite using `[← h, (pl_monic _ _).nextCoeff_mul (pl_monic _ _), Monic.nextCoeff_prod _ _ (fun i _ => monic_X_add_C (fa i)), Monic.nextCoeff_prod _ _ (fun i _ => monic_X_add_C (fb i))]`.

Simplify using `only [nextCoeff_X_add_C]`. Set `NS : ℂ[X]` to `∑ l ∈ Finset.Icc 1 (m + 1), C ((M.Nrm P l ρ : ℝ) : ℂ) * ((∏ j ∈ (Finset.Icc 1 (m + 1)).erase l, (X + C ((M.rho P ρ j : ℝ) : ℂ))) * ∏ j ∈ (Finset.Icc 1 (m + 1)).erase l, (X + C (((M.rho P ρ j : ℝ) : ℂ) + 1)))`. Establish `hw : M.wNum P ρ = M.qP P + NS` using `by unfold M.wNum; rw [h1]`. Establish `nsdeg : NS.natDegree ≤ 2 * m + 2`. Apply `natDegree_sum_le_of_forall_le` to reduce the goal to its premises.

Introduce `l hl`. Use `(natDegree_C_mul_le _ _).trans (natDegree_mul_le.trans ?_)` and prove the remaining obligations. Establish `hc : ((Finset.Icc 1 (m + 1)).erase l).card = m`. Rewrite using `[Finset.card_erase_of_mem hl, card_Icc_one]`. Use linear arithmetic over natural numbers and integers.

Establish `e1` using `pl_natDegree ((Finset.Icc 1 (m + 1)).erase l) (fun j => ((M.rho P ρ j : ℝ) : ℂ))`. Establish `e2` using `pl_natDegree ((Finset.Icc 1 (m + 1)).erase l) (fun j => ((M.rho P ρ j : ℝ) : ℂ) + 1)`. Rewrite using `[e1, e2, hc]`. Use linear arithmetic over natural numbers and integers. Set `c0 : ℂ` to `(P.TT : ℂ) * ((absTy P ρ : ℂ) - 1 - sumU P)`.

Set `Q0 : ℂ[X]` to `C (-(P.TT : ℂ)) * X ^ (m + 3) + C c0 * X ^ (m + 2)`. Set `G : ℂ[X]` to `M.wNum P ρ - xp * Q0`. Establish `e_xQ : xp * Q0 = C (-(P.TT : ℂ)) * (xp * X ^ (m + 3)) + C c0 * (xp * X ^ (m + 2))`. Simplify using `only [Q0]`. Expand and normalize the polynomial expressions, which then agree.

Establish `c4a : (xp * X ^ (m + 3)).coeff (2 * m + 4) = 1`. Rewrite using `[show 2 * m + 4 = (m + 1) + (m + 3) by ring, coeff_mul_X_pow, xtop]`. Establish `c4b : (xp * X ^ (m + 2)).coeff (2 * m + 4) = 0`. Rewrite using `[show 2 * m + 4 = (m + 2) + (m + 2) by ring, coeff_mul_X_pow, xhigh]`. Establish `c3a : (xp * X ^ (m + 3)).coeff (2 * m + 3) = xp.coeff m`.

Rewrite using `[show 2 * m + 3 = m + (m + 3) by ring, coeff_mul_X_pow]`. Establish `c3b : (xp * X ^ (m + 2)).coeff (2 * m + 3) = 1`. Rewrite using `[show 2 * m + 3 = (m + 1) + (m + 2) by ring, coeff_mul_X_pow, xtop]`. Establish `Q0deg : (xp * Q0).natDegree ≤ 2 * m + 4`. Use `natDegree_mul_le.trans ?_` and prove the remaining obligations.

Rewrite using `[xdeg]`. Establish `: Q0.natDegree ≤ m + 3` using `(natDegree_add_le _ _).trans (max_le (natDegree_C_mul_X_pow_le _ _) ((natDegree_C_mul_X_pow_le _ _).trans (by omega)))`. Use linear arithmetic over natural numbers and integers. Establish `qdeg : (M.qP P).natDegree ≤ 2 * m + 4`. Rewrite using `[hq]`.

Conclude with `(natDegree_C_mul_le _ _).trans abdeg.le`. Establish `hA : (absTy P ρ : ℂ) = ∑ i ∈ Finset.Icc 1 (m + 1), ((M.rho P ρ i : ℝ) : ℂ)`. Simplify using `only [absTy, h1]`. Use `push_cast`. Both sides reduce to the same expression.

Establish `hS : sumU P = ∑ i ∈ Finset.Icc 1 (m + 2), (P.u i : ℂ) + ∑ i ∈ Finset.Icc 1 (m + 2), (P.u' i : ℂ)`. Simplify using `only [sumU, hm, Finset.sum_add_distrib]`. Establish `Gdeg : G.natDegree ≤ 2 * m + 2`. Rewrite using `[natDegree_le_iff_coeff_eq_zero]`. Introduce `N hN`.

Simplify using `only [G, hw, coeff_sub, coeff_add]`. Rewrite using `[coeff_eq_zero_of_natDegree_lt (p := NS) (by omega), add_zero]`. Break down `(show N = 2 * m + 3 ∨ N = 2 * m + 4 ∨ 2 * m + 4 < N by omega) with h | h | h` into its components or cases. Substitute `h` using the available equality. Rewrite using `[e_xQ, coeff_add, coeff_C_mul, coeff_C_mul, c3a, c3b, xnext, hq, coeff_C_mul, abnext]`.

Simplify using `only [fa, fb, fx, c0, hA, hS, Finset.sum_add_distrib, Finset.sum_const, card_Icc_one, nsmul_eq_mul]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Substitute `h` using the available equality. Rewrite using `[e_xQ, coeff_add, coeff_C_mul, coeff_C_mul, c4a, c4b, hq, coeff_C_mul, abtop]`.

Expand and normalize the polynomial expressions, which then agree. Rewrite using `[coeff_eq_zero_of_natDegree_lt (by omega : (M.qP P).natDegree < N), coeff_eq_zero_of_natDegree_lt (by omega : (xp * Q0).natDegree < N)]; ring`. Establish `hG` using `modByMonic_add_div G xp`. Establish `hdiv : M.wNum P ρ /ₘ xp = Q0 + G /ₘ xp`. Use `(div_modByMonic_unique (Q0 + G /ₘ xp) (G %ₘ xp) xmon ⟨?_, degree_modByMonic_lt _ xmon⟩).1` and prove the remaining obligations.

Combine the equalities or inequalities in the displayed calculation. Establish `Gq : (G /ₘ xp).natDegree < m + 2` using `by rw [natDegree_divByMonic _ xmon, xdeg]; omega`. Use `⟨fun i => (G /ₘ xp).coeff i, fun u => ?_⟩` and prove the remaining obligations. Unfold `M.wC`. Rewrite using `[hxp, hdiv, eval_add, eval_eq_sum_range' Gq u, hm]`.

Simplify using `only [Q0, c0, eval_add, eval_mul, eval_C, eval_pow, eval_X]`. Establish `: ∀ i, (G /ₘ xp).coeff i * u ^ i = u ^ i * (G /ₘ xp).coeff i` using `fun i => mul_comm _ _`. Simplify using `only [this]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem part_w (P : M.Par) (m : ℕ) (hm : P.k = m + 2) (ρ : M.Ty P) :
    ∃ c : ℕ → ℂ, ∀ u : ℂ, M.wC P ρ u = u ^ (P.k + 1) * (-(P.TT : ℂ)) +
        u ^ P.k * ((P.TT : ℂ) * ((absTy P ρ : ℂ) - 1 - sumU P)) + ∑ i ∈ Finset.range P.k, u ^ i * c i := by
  have h1 : P.k - 1 = m + 1 := by omega
  let fx : ℕ → ℂ := fun i => ((M.rho P ρ i : ℝ) : ℂ) + 1
  let xp := ∏ i ∈ Finset.Icc 1 (m + 1), (X + C (fx i))
  have hxp : M.coordinatePolynomial P ρ = xp := by unfold M.coordinatePolynomial; rw [h1]
  have xmon : xp.Monic := pl_monic _ _
  have xdeg : xp.natDegree = m + 1 := by rw [pl_natDegree, card_Icc_one]
  have xtop : xp.coeff (m + 1) = 1 := by
    have := pl_top (Finset.Icc 1 (m + 1)) fx; rwa [card_Icc_one] at this
  have xnext : xp.coeff m = ∑ i ∈ Finset.Icc 1 (m + 1), fx i := by
    have := pl_next (Finset.Icc 1 (m + 1)) fx (by rw [card_Icc_one]; omega)
    rwa [card_Icc_one, Nat.add_sub_cancel] at this
  have xhigh : xp.coeff (m + 2) = 0 := pl_high _ _ (by rw [card_Icc_one]; omega)
  let fa : ℕ → ℂ := fun i => 1 / 2 + (P.u i : ℂ)
  let fb : ℕ → ℂ := fun i => 1 / 2 + (P.u' i : ℂ)
  let pa := ∏ i ∈ Finset.Icc 1 (m + 2), (X + C (fa i))
  let pb := ∏ i ∈ Finset.Icc 1 (m + 2), (X + C (fb i))
  have hT : (-((P.T : ℂ) * (P.T' : ℂ))) = -(P.TT : ℂ) := by simp [M.Par.TT]
  have hq : M.qP P = C (-(P.TT : ℂ)) * (pa * pb) := by
    unfold M.qP; rw [hm, Finset.prod_mul_distrib, hT]
  have abmon : (pa * pb).Monic := (pl_monic _ _).mul (pl_monic _ _)
  have abdeg : (pa * pb).natDegree = 2 * m + 4 := by
    rw [(pl_monic _ _).natDegree_mul (pl_monic _ _), pl_natDegree, pl_natDegree, card_Icc_one]; ring
  have abtop : (pa * pb).coeff (2 * m + 4) = 1 := by rw [← abdeg]; exact abmon.coeff_natDegree
  have abnext : (pa * pb).coeff (2 * m + 3) =
      ∑ i ∈ Finset.Icc 1 (m + 2), fa i + ∑ i ∈ Finset.Icc 1 (m + 2), fb i := by
    have h := nextCoeff_of_natDegree_pos (p := pa * pb) (by rw [abdeg]; omega)
    rw [abdeg, show 2 * m + 4 - 1 = 2 * m + 3 by omega] at h
    rw [← h, (pl_monic _ _).nextCoeff_mul (pl_monic _ _),
      Monic.nextCoeff_prod _ _ (fun i _ => monic_X_add_C (fa i)),
      Monic.nextCoeff_prod _ _ (fun i _ => monic_X_add_C (fb i))]
    simp only [nextCoeff_X_add_C]
  let NS : ℂ[X] := ∑ l ∈ Finset.Icc 1 (m + 1), C ((M.Nrm P l ρ : ℝ) : ℂ) *
    ((∏ j ∈ (Finset.Icc 1 (m + 1)).erase l, (X + C ((M.rho P ρ j : ℝ) : ℂ))) *
      ∏ j ∈ (Finset.Icc 1 (m + 1)).erase l, (X + C (((M.rho P ρ j : ℝ) : ℂ) + 1)))
  have hw : M.wNum P ρ = M.qP P + NS := by unfold M.wNum; rw [h1]
  have nsdeg : NS.natDegree ≤ 2 * m + 2 := by
    apply natDegree_sum_le_of_forall_le
    intro l hl
    refine (natDegree_C_mul_le _ _).trans (natDegree_mul_le.trans ?_)
    have hc : ((Finset.Icc 1 (m + 1)).erase l).card = m := by
      rw [Finset.card_erase_of_mem hl, card_Icc_one]; omega
    have e1 := pl_natDegree ((Finset.Icc 1 (m + 1)).erase l) (fun j => ((M.rho P ρ j : ℝ) : ℂ))
    have e2 := pl_natDegree ((Finset.Icc 1 (m + 1)).erase l) (fun j => ((M.rho P ρ j : ℝ) : ℂ) + 1)
    rw [e1, e2, hc]; omega
  let c0 : ℂ := (P.TT : ℂ) * ((absTy P ρ : ℂ) - 1 - sumU P)
  let Q0 : ℂ[X] := C (-(P.TT : ℂ)) * X ^ (m + 3) + C c0 * X ^ (m + 2)
  let G : ℂ[X] := M.wNum P ρ - xp * Q0
  have e_xQ : xp * Q0 = C (-(P.TT : ℂ)) * (xp * X ^ (m + 3)) + C c0 * (xp * X ^ (m + 2)) := by
    simp only [Q0]; ring
  have c4a : (xp * X ^ (m + 3)).coeff (2 * m + 4) = 1 := by
    rw [show 2 * m + 4 = (m + 1) + (m + 3) by ring, coeff_mul_X_pow, xtop]
  have c4b : (xp * X ^ (m + 2)).coeff (2 * m + 4) = 0 := by
    rw [show 2 * m + 4 = (m + 2) + (m + 2) by ring, coeff_mul_X_pow, xhigh]
  have c3a : (xp * X ^ (m + 3)).coeff (2 * m + 3) = xp.coeff m := by
    rw [show 2 * m + 3 = m + (m + 3) by ring, coeff_mul_X_pow]
  have c3b : (xp * X ^ (m + 2)).coeff (2 * m + 3) = 1 := by
    rw [show 2 * m + 3 = (m + 1) + (m + 2) by ring, coeff_mul_X_pow, xtop]
  have Q0deg : (xp * Q0).natDegree ≤ 2 * m + 4 := by
    refine natDegree_mul_le.trans ?_
    rw [xdeg]
    have : Q0.natDegree ≤ m + 3 := (natDegree_add_le _ _).trans
      (max_le (natDegree_C_mul_X_pow_le _ _) ((natDegree_C_mul_X_pow_le _ _).trans (by omega)))
    omega
  have qdeg : (M.qP P).natDegree ≤ 2 * m + 4 := by
    rw [hq]; exact (natDegree_C_mul_le _ _).trans abdeg.le
  have hA : (absTy P ρ : ℂ) = ∑ i ∈ Finset.Icc 1 (m + 1), ((M.rho P ρ i : ℝ) : ℂ) := by
    simp only [absTy, h1]; push_cast; rfl
  have hS : sumU P = ∑ i ∈ Finset.Icc 1 (m + 2), (P.u i : ℂ) + ∑ i ∈ Finset.Icc 1 (m + 2), (P.u' i : ℂ) := by
    simp only [sumU, hm, Finset.sum_add_distrib]
  have Gdeg : G.natDegree ≤ 2 * m + 2 := by
    rw [natDegree_le_iff_coeff_eq_zero]
    intro N hN
    simp only [G, hw, coeff_sub, coeff_add]
    rw [coeff_eq_zero_of_natDegree_lt (p := NS) (by omega), add_zero]
    rcases (show N = 2 * m + 3 ∨ N = 2 * m + 4 ∨ 2 * m + 4 < N by omega) with h | h | h
    · subst h
      rw [e_xQ, coeff_add, coeff_C_mul, coeff_C_mul, c3a, c3b, xnext, hq, coeff_C_mul, abnext]
      simp only [fa, fb, fx, c0, hA, hS, Finset.sum_add_distrib, Finset.sum_const, card_Icc_one, nsmul_eq_mul]
      push_cast
      ring
    · subst h
      rw [e_xQ, coeff_add, coeff_C_mul, coeff_C_mul, c4a, c4b, hq, coeff_C_mul, abtop]; ring
    · rw [coeff_eq_zero_of_natDegree_lt (by omega : (M.qP P).natDegree < N),
        coeff_eq_zero_of_natDegree_lt (by omega : (xp * Q0).natDegree < N)]; ring
  have hG := modByMonic_add_div G xp
  have hdiv : M.wNum P ρ /ₘ xp = Q0 + G /ₘ xp := by
    refine (div_modByMonic_unique (Q0 + G /ₘ xp) (G %ₘ xp) xmon ⟨?_, degree_modByMonic_lt _ xmon⟩).1
    calc G %ₘ xp + xp * (Q0 + G /ₘ xp) = xp * Q0 + (G %ₘ xp + xp * (G /ₘ xp)) := by ring
      _ = xp * Q0 + G := by rw [hG]
      _ = M.wNum P ρ := by simp only [G]; ring
  have Gq : (G /ₘ xp).natDegree < m + 2 := by rw [natDegree_divByMonic _ xmon, xdeg]; omega
  refine ⟨fun i => (G /ₘ xp).coeff i, fun u => ?_⟩
  unfold M.wC
  rw [hxp, hdiv, eval_add, eval_eq_sum_range' Gq u, hm]
  simp only [Q0, c0, eval_add, eval_mul, eval_C, eval_pow, eval_X]
  have : ∀ i, (G /ₘ xp).coeff i * u ^ i = u ^ i * (G /ₘ xp).coeff i := fun i => mul_comm _ _
  simp only [this]
  ring

end

end Formalism.FourierDecayAlt.P.CutMP.Gauge.GC.CurvScal

namespace Formalism.FourierDecayAlt.P.CutMP.Gauge.GC

/- English proof (translation)
Introduce `P hk ρ`. Take `⟨m, hm⟩ : ∃ m, P.k = m + 2` from `⟨P.k - 2, by omega⟩`. Conclude with `⟨CurvScal.part_w P m hm ρ, CurvScal.xC_leading_terms_alt P m hm ρ, fun ex hex => CurvScal.part_ex P m hm ρ ex hex⟩`.
-/
theorem curvature_scalar_holds : GTCCurvScal := by
  intro P hk ρ
  obtain ⟨m, hm⟩ : ∃ m, P.k = m + 2 := ⟨P.k - 2, by omega⟩
  exact ⟨CurvScal.part_w P m hm ρ, CurvScal.xC_leading_terms_alt P m hm ρ, fun ex hex => CurvScal.part_ex P m hm ρ ex hex⟩

end Formalism.FourierDecayAlt.P.CutMP.Gauge.GC

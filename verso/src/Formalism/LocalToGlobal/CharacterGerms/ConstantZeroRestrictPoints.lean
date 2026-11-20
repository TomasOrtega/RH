import Formalism.LocalToGlobal.CharacterGerms.PderivDoubleMultiplicationJacobian
import Formalism.LocalToGlobal.CharacterGerms.FirstVanishingAt

set_option autoImplicit false

noncomputable section

open scoped BigOperators
open Classical

namespace Formalism.L2.FormalSeriesBounds.FunEq

open Formalism.L2.FormalSeriesBounds Formalism.L2.FormalSeriesBounds.PartialDerivEval ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ MvPowerSeries

variable {C : Type} [Field C] [CharZero C] {dd : ℕ}

def up (m : ℕ) : Fin m × Fin dd → Fin (m + 1) × Fin dd := fun p => (p.1.succ, p.2)

/- English proof (translation)
Introduce `a b h`. Simplify using `only [up, Prod.mk.injEq, Fin.succ_inj] at h`. Conclude with `Prod.ext h.1 h.2`.
-/
theorem up_inj (m : ℕ) : Function.Injective (up (dd := dd) m) := by
  intro a b h
  simp only [up, Prod.mk.injEq, Fin.succ_inj] at h
  exact Prod.ext h.1 h.2

def rz (m : ℕ) : Fin (m + 1) → Pt C m dd := Fin.cons 0 (fun k => pt C dd k)

/- English proof (translation)
Introduce `k i`. Use `Fin.cases ?_ (fun k => ?_) k` and prove the remaining obligations. Use `show MvPowerSeries.constantCoeff (0 : MvPowerSeries (Fin m × Fin dd) C) = 0`. Simplify using the standard rewrite rules. Conclude with `MvPowerSeries.constantCoeff_X (R := C) (k, i)`.
-/
theorem constant_zero_restrict_points (m : ℕ) : Z0 (rz (C := C) (dd := dd) m) := by
  intro k i
  refine Fin.cases ?_ (fun k => ?_) k
  · show MvPowerSeries.constantCoeff (0 : MvPowerSeries (Fin m × Fin dd) C) = 0
    simp
  · exact MvPowerSeries.constantCoeff_X (R := C) (k, i)

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem rz_zero (m : ℕ) (i : Fin dd) : rz (C := C) (dd := dd) m 0 i = 0 := rfl

/- English proof (translation)
Introduce and unpack `⟨p, hp⟩`. Conclude with `Fin.succ_ne_zero _ (congrArg Prod.fst hp)`.
-/
theorem up_ne_zero (m : ℕ) (i : Fin dd) : ((0 : Fin (m + 1)), i) ∉ Set.range (up (dd := dd) m) := by
  rintro ⟨p, hp⟩
  exact Fin.succ_ne_zero _ (congrArg Prod.fst hp)

/- English proof (translation)
Unfold `ev`. Rewrite using `[coeff_subst (hasSubst_ev (constant_zero_restrict_points m)), finsum_eq_single _ (ν.mapDomain (up m))]`. Rewrite using `[Finsupp.prod_mapDomain_index_inj (up_inj m)]`. Establish `e : (ν.prod fun t e => (fun p : Fin (m + 1) × Fin dd => rz (C` using `C) (dd := dd) m p.1 p.2) (up m t) ^ e) = monomial ν (1 : C) := by`. Establish `h1` using `monomial_eq (R := C) ν (fun _ => (1 : C))`.

Simplify using `only [one_pow, Finsupp.prod, Finset.prod_const_one, one_smul] at h1`. Rewrite using `[Finsupp.prod, h1]`. Both sides reduce to the same expression. Rewrite using `[e, coeff_monomial, if_pos rfl, smul_eq_mul, mul_one]`. Introduce `d hd`.

Distinguish the cases in `hx : ∃ j, d ((0 : Fin (m + 1)), j) ≠ 0`. Take `⟨j, hj⟩` from `hx`. Rewrite using `[Finsupp.prod, Finset.prod_eq_zero (i := ((0 : Fin (m + 1)), j)) (Finsupp.mem_support_iff.2 hj) (by show (rz (C := C) (dd := dd) m 0 j) ^ _ = 0; rw [rz_zero]; exact zero_pow hj), map_zero, smul_zero]`. Use `push_neg at hx`. Establish `hsub : ↑d.support ⊆ Set.range (up (dd` using `dd) m) := by`.

Introduce `s hs`. Take `⟨s1, s2⟩` from `s`. Establish `hs1 : s1 ≠ 0`. Introduce and unpack `rfl`. Conclude with `(Finsupp.mem_support_iff.1 hs) (hx s2)`.

Conclude with `⟨(s1.pred hs1, s2), by simp [up, Fin.succ_pred]⟩`. Use `set e := Finsupp.comapDomain (up m) d ((up_inj m).injOn) with he`. Establish `hde : e.mapDomain (up m) = d` using `Finsupp.mapDomain_comapDomain _ (up_inj m) d hsub`. Establish `hne : e ≠ ν`. Introduce `h`.

Apply `hd` to reduce the goal to its premises. Rewrite using `[← hde, h]`. Rewrite using `[← hde, Finsupp.prod_mapDomain_index_inj (up_inj m)]`. Establish `e2 : (e.prod fun t k => (fun p : Fin (m + 1) × Fin dd => rz (C` using `C) (dd := dd) m p.1 p.2) (up m t) ^ k) = monomial e (1 : C) := by`. Establish `h1` using `monomial_eq (R := C) e (fun _ => (1 : C))`.

Simplify using `only [one_pow, Finsupp.prod, Finset.prod_const_one, one_smul] at h1`. Rewrite using `[Finsupp.prod, h1]`. Both sides reduce to the same expression. Rewrite using `[e2, coeff_monomial, if_neg (Ne.symm hne), smul_zero]`.
-/
theorem coeff_rz (m : ℕ) (f : PS C (m + 1) dd) (ν : Fin m × Fin dd →₀ ℕ) :
    coeff ν (ev (rz m) f) = coeff (ν.mapDomain (up m)) f := by
  unfold ev
  rw [coeff_subst (hasSubst_ev (constant_zero_restrict_points m)), finsum_eq_single _ (ν.mapDomain (up m))]
  · rw [Finsupp.prod_mapDomain_index_inj (up_inj m)]
    have e : (ν.prod fun t e => (fun p : Fin (m + 1) × Fin dd => rz (C := C) (dd := dd) m p.1 p.2) (up m t) ^ e) =
        monomial ν (1 : C) := by
      have h1 := monomial_eq (R := C) ν (fun _ => (1 : C))
      simp only [one_pow, Finsupp.prod, Finset.prod_const_one, one_smul] at h1
      rw [Finsupp.prod, h1]
      rfl
    rw [e, coeff_monomial, if_pos rfl, smul_eq_mul, mul_one]
  · intro d hd
    by_cases hx : ∃ j, d ((0 : Fin (m + 1)), j) ≠ 0
    · obtain ⟨j, hj⟩ := hx
      rw [Finsupp.prod, Finset.prod_eq_zero (i := ((0 : Fin (m + 1)), j)) (Finsupp.mem_support_iff.2 hj)
        (by show (rz (C := C) (dd := dd) m 0 j) ^ _ = 0; rw [rz_zero]; exact zero_pow hj),
        map_zero, smul_zero]
    · push_neg at hx
      have hsub : ↑d.support ⊆ Set.range (up (dd := dd) m) := by
        intro s hs
        obtain ⟨s1, s2⟩ := s
        have hs1 : s1 ≠ 0 := by
          rintro rfl
          exact (Finsupp.mem_support_iff.1 hs) (hx s2)
        exact ⟨(s1.pred hs1, s2), by simp [up, Fin.succ_pred]⟩
      set e := Finsupp.comapDomain (up m) d ((up_inj m).injOn) with he
      have hde : e.mapDomain (up m) = d := Finsupp.mapDomain_comapDomain _ (up_inj m) d hsub
      have hne : e ≠ ν := by
        intro h; apply hd; rw [← hde, h]
      rw [← hde, Finsupp.prod_mapDomain_index_inj (up_inj m)]
      have e2 : (e.prod fun t k => (fun p : Fin (m + 1) × Fin dd => rz (C := C) (dd := dd) m p.1 p.2) (up m t) ^ k) =
          monomial e (1 : C) := by
        have h1 := monomial_eq (R := C) e (fun _ => (1 : C))
        simp only [one_pow, Finsupp.prod, Finset.prod_const_one, one_smul] at h1
        rw [Finsupp.prod, h1]
        rfl
      rw [e2, coeff_monomial, if_neg (Ne.symm hne), smul_zero]

/- English proof (translation)
Proceed by induction on `L generalizing f with`. Consider the case `zero => simp`. Consider the case `succ L ih`. Establish `h1 : n + (L + 1) • Finsupp.single q 1 = n + L • Finsupp.single q 1 + Finsupp.single q 1`. Rewrite using `[add_smul, one_smul, add_assoc]`.

Rewrite using `[Function.iterate_succ_apply, ih, coeff_pderiv, Finset.prod_range_succ, h1]`. Simplify using `only [Finsupp.coe_add, Finsupp.coe_smul, Pi.add_apply, Pi.smul_apply, Finsupp.single_eq_same, smul_eq_mul, mul_one, Nat.cast_add, Nat.cast_one]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem coeff_iter_pderiv {σ : Type} (q : σ) (L : ℕ) (f : MvPowerSeries σ C) (n : σ →₀ ℕ) :
    coeff n ((pderiv C q)^[L] f) =
      coeff (n + L • Finsupp.single q 1) f * ∏ r ∈ Finset.range L, ((n q : C) + r + 1) := by
  induction L generalizing f with
  | zero => simp
  | succ L ih =>
    have h1 : n + (L + 1) • Finsupp.single q 1 = n + L • Finsupp.single q 1 + Finsupp.single q 1 := by
      rw [add_smul, one_smul, add_assoc]
    rw [Function.iterate_succ_apply, ih, coeff_pderiv, Finset.prod_range_succ, h1]
    simp only [Finsupp.coe_add, Finsupp.coe_smul, Pi.add_apply, Pi.smul_apply, Finsupp.single_eq_same,
      smul_eq_mul, mul_one, Nat.cast_add, Nat.cast_one]
    ring

/- English proof (translation)
Rewrite using `[coeff_rz, coeff_iter_pderiv, Finsupp.mapDomain_notin_range _ _ (up_ne_zero m i)]`. Simplify using `only [Nat.cast_zero, zero_add]`. Rewrite using `[← Finset.prod_range_add_one_eq_factorial, Nat.cast_prod, Finsupp.smul_single_one, add_comm (Finsupp.mapDomain (up m) ν)]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem coeff_rz_iter (m : ℕ) (i : Fin dd) (L : ℕ) (f : PS C (m + 1) dd) (ν : Fin m × Fin dd →₀ ℕ) :
    coeff ν (ev (rz m) ((pderiv C ((0 : Fin (m + 1)), i))^[L] f)) =
      (L.factorial : C) * coeff (Finsupp.single ((0 : Fin (m + 1)), i) L + ν.mapDomain (up m)) f := by
  rw [coeff_rz, coeff_iter_pderiv, Finsupp.mapDomain_notin_range _ _ (up_ne_zero m i)]
  simp only [Nat.cast_zero, zero_add]
  rw [← Finset.prod_range_add_one_eq_factorial, Nat.cast_prod, Finsupp.smul_single_one,
    add_comm (Finsupp.mapDomain (up m) ν)]
  push_cast
  ring

end Formalism.L2.FormalSeriesBounds.FunEq

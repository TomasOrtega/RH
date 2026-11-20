import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CosetVecEq
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemPrincipalCongruenceLevelSubgroupIffIntegralCo
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryCongruentOneDetSubOneMemIdealMulConj
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemBlockCongruenceLevelSubgroupIffStabilizerEntr
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIdealMatrixApproxCongruentOneTranslate
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RationalPointsIntegralPointsMembership
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsHalfIdem
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.CmFiniteAdeleIntegralSeparatedCompleteStatement
open scoped Pointwise
open Formalism.BasicNotions Formalism.IndefR.Links IsDedekindDomain NumberField
open Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.LeafRestExamples GlobalTheory.FunObj.SqNum GlobalTheory.NormSum GlobalTheory.FunObj.StdDatum
open GlobalTheory.Mem.Col2.SplitChar (finIdl)

namespace GlobalTheory.PowIdem

/- English proof (translation)
Use `haveI := Fintype.ofFinite M`. Take `⟨a, b, hab, h⟩` from `Fintype.exists_ne_map_eq_of_card_lt (fun i : Fin (Nat.card M + 1) => y ^ (i : ℕ)) (by simp [Nat.card_eq_fintype_card])`. Establish `ha` using `a.isLt`. Establish `hb` using `b.isLt`. Break down `lt_or_gt_of_ne (Fin.val_injective.ne hab) with hlt | hlt` into its components or cases.

Use `⟨a, b - a, by omega, by omega, ?_⟩` and prove the remaining obligations. Rewrite using `[Nat.add_sub_cancel' hlt.le]`. Conclude with `h.symm`. Use `⟨b, a - b, by omega, by omega, ?_⟩` and prove the remaining obligations. Rewrite using `[Nat.add_sub_cancel' hlt.le]`.

Conclude with `h`.
-/
theorem exists_period {M : Type*} [Monoid M] [Finite M] (y : M) :
    ∃ i p : ℕ, 0 < p ∧ i + p ≤ Nat.card M ∧ y ^ (i + p) = y ^ i := by
  classical
  haveI := Fintype.ofFinite M
  obtain ⟨a, b, hab, h⟩ := Fintype.exists_ne_map_eq_of_card_lt
    (fun i : Fin (Nat.card M + 1) => y ^ (i : ℕ)) (by simp [Nat.card_eq_fintype_card])
  have ha := a.isLt
  have hb := b.isLt
  rcases lt_or_gt_of_ne (Fin.val_injective.ne hab) with hlt | hlt
  · refine ⟨a, b - a, by omega, by omega, ?_⟩
    rw [Nat.add_sub_cancel' hlt.le]; exact h.symm
  · refine ⟨b, a - b, by omega, by omega, ?_⟩
    rw [Nat.add_sub_cancel' hlt.le]; exact h

/- English proof (translation)
Take `⟨i, p, hp, hip, h⟩` from `exists_period y`. Establish `step : ∀ t, i ≤ t → y ^ (t + p) = y ^ t`. Introduce `t ht`. Take `⟨s, rfl⟩` from `Nat.exists_eq_add_of_le ht`. Rewrite using `[show i + s + p = s + (i + p) by ring, pow_add, h, ← pow_add, add_comm s i]`.

Establish `iter : ∀ q t, i ≤ t → y ^ (t + q * p) = y ^ t`. Introduce `q`. Proceed by induction on `q with`. Consider the case `zero => intro t _`. Simplify using the standard rewrite rules.

Consider the case `succ q ih`. Introduce `t ht`. Rewrite using `[show t + (q + 1) * p = (t + q * p) + p by ring, step _ (by omega), ih t ht]`. Take `⟨c, hc⟩` from `Nat.dvd_factorial hp (by omega : p ≤ n)`. Rewrite using `[hc, show j * (p * c) = (j * c) * p by ring]`.

Conclude with `iter _ _ (by omega)`.
-/
theorem pow_add_mul_factorial {M : Type*} [Monoid M] [Finite M] (y : M) (n : ℕ)
    (hn : Nat.card M ≤ n) (k j : ℕ) (hk : n ≤ k) : y ^ (k + j * n.factorial) = y ^ k := by
  obtain ⟨i, p, hp, hip, h⟩ := exists_period y
  have step : ∀ t, i ≤ t → y ^ (t + p) = y ^ t := by
    intro t ht
    obtain ⟨s, rfl⟩ := Nat.exists_eq_add_of_le ht
    rw [show i + s + p = s + (i + p) by ring, pow_add, h, ← pow_add, add_comm s i]
  have iter : ∀ q t, i ≤ t → y ^ (t + q * p) = y ^ t := by
    intro q
    induction q with
    | zero => intro t _; simp
    | succ q ih =>
      intro t ht
      rw [show t + (q + 1) * p = (t + q * p) + p by ring, step _ (by omega), ih t ht]
  obtain ⟨c, hc⟩ := Nat.dvd_factorial hp (by omega : p ≤ n)
  rw [hc, show j * (p * c) = (j * c) * p by ring]
  exact iter _ _ (by omega)

/- English proof (translation)
Set `ι : 𝓞 D.host.E →+* OhE D` to `((inc D).comp (algebraMap (𝓞 D.host.E) D.host.E)).codRestrict _ fun x => GlobalTheory.CongApprox.inc_mem_OhE D x`. Use `haveI : Finite (𝓞 D.host.E ⧸ Ideal.span {(N : 𝓞 D.host.E)}) := Ideal.finiteQuotientOfFreeOfNeBot _ (by simpa using hN.ne')`. Use `Finite.of_surjective (Ideal.quotientMap (I := Ideal.span {(N : 𝓞 D.host.E)}) (Ideal.span {(N : OhE D)}) ι ?_) ?_` and prove the remaining obligations. Rewrite using `[Ideal.span_le, Set.singleton_subset_iff]`. Express the relevant statement in the definitionally equal form `ι N ∈ Ideal.span {(N : OhE D)}`.

Rewrite using `[map_natCast]`. Conclude with `Ideal.mem_span_singleton_self _`. Introduce `z`. Take `⟨z, rfl⟩` from `Ideal.Quotient.mk_surjective z`. Take `⟨x, w, hw, h⟩` from `GlobalTheory.CongApprox.exists_int_approx D N hN z z.2`.

Use `⟨Ideal.Quotient.mk _ x, ?_⟩` and prove the remaining obligations. Rewrite using `[Ideal.quotientMap_mk, eq_comm, Ideal.Quotient.eq, Ideal.mem_span_singleton]`. Use `⟨⟨w, hw⟩, Subtype.ext ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `(z : AE D) - inc D (x : D.host.E) = ((N : OhE D) : AE D) * w`. Rewrite using `[h, add_sub_cancel_left]`.

Simplify using the standard rewrite rules.
-/
theorem finite_quot (D : D7) (N : ℕ) (hN : 0 < N) :
    Finite (OhE D ⧸ Ideal.span {(N : OhE D)}) := by
  let ι : 𝓞 D.host.E →+* OhE D :=
    ((inc D).comp (algebraMap (𝓞 D.host.E) D.host.E)).codRestrict _
      fun x => GlobalTheory.CongApprox.inc_mem_OhE D x
  haveI : Finite (𝓞 D.host.E ⧸ Ideal.span {(N : 𝓞 D.host.E)}) :=
    Ideal.finiteQuotientOfFreeOfNeBot _ (by simpa using hN.ne')
  refine Finite.of_surjective (Ideal.quotientMap (I := Ideal.span {(N : 𝓞 D.host.E)})
    (Ideal.span {(N : OhE D)}) ι ?_) ?_
  · rw [Ideal.span_le, Set.singleton_subset_iff]
    change ι N ∈ Ideal.span {(N : OhE D)}
    rw [map_natCast]
    exact Ideal.mem_span_singleton_self _
  · intro z
    obtain ⟨z, rfl⟩ := Ideal.Quotient.mk_surjective z
    obtain ⟨x, w, hw, h⟩ := GlobalTheory.CongApprox.exists_int_approx D N hN z z.2
    refine ⟨Ideal.Quotient.mk _ x, ?_⟩
    rw [Ideal.quotientMap_mk, eq_comm, Ideal.Quotient.eq, Ideal.mem_span_singleton]
    refine ⟨⟨w, hw⟩, Subtype.ext ?_⟩
    change (z : AE D) - inc D (x : D.host.E) = ((N : OhE D) : AE D) * w
    rw [h, add_sub_cancel_left]
    simp

/- English proof (translation)
Rewrite `h` using `[Ideal.Quotient.eq, Ideal.mem_span_singleton]`. Take `⟨c, hc⟩` from `h`. Use `⟨c, c.2, ?_⟩` and prove the remaining obligations. Use `congrArg Subtype.val hc` as an intermediate fact. Move the coercions through the operations in `at this`.

Take the linear combination `this`.
-/
theorem exists_of_mk_eq (D : D7) (N : ℕ) (a b : OhE D)
    (h : Ideal.Quotient.mk (Ideal.span {(N : OhE D)}) a = Ideal.Quotient.mk _ b) :
    ∃ w ∈ OhE D, (a : AE D) = b + (N : AE D) * w := by
  rw [Ideal.Quotient.eq, Ideal.mem_span_singleton] at h
  obtain ⟨c, hc⟩ := h
  refine ⟨c, c.2, ?_⟩
  have := congrArg Subtype.val hc
  push_cast at this
  linear_combination this

/- English proof (translation)
Rewrite using `[Ideal.Quotient.eq, Ideal.mem_span_singleton]`. Use `⟨⟨w, hw⟩, Subtype.ext ?_⟩` and prove the remaining obligations. Use `push_cast`. Take the linear combination `h`.
-/
theorem mk_eq_of_exists (D : D7) (N : ℕ) (a b : OhE D) (w : AE D) (hw : w ∈ OhE D)
    (h : (a : AE D) = b + (N : AE D) * w) :
    Ideal.Quotient.mk (Ideal.span {(N : OhE D)}) a = Ideal.Quotient.mk _ b := by
  rw [Ideal.Quotient.eq, Ideal.mem_span_singleton]
  refine ⟨⟨w, hw⟩, Subtype.ext ?_⟩
  push_cast
  linear_combination h

/- English proof (translation)
Proceed by induction on `k with`. Consider the case `zero => simp`. Consider the case `succ k ih`. Establish `e : y ^ (k + 1) - 1 = y * (y ^ k - 1) + (y - 1)` using `by ring`. Rewrite using `[e]`.

Conclude with `add_mem (GlobalTheory.CongApprox.mul_mem_hatId D 𝔪 y hy _ ih) hy1`.
-/
theorem pow_sub_one_mem (D : D7) (𝔪 : Ideal (𝓞 D.host.E)) (y : AE D) (hy : y ∈ OhE D)
    (hy1 : y - 1 ∈ hatId D 𝔪) (k : ℕ) : y ^ k - 1 ∈ hatId D 𝔪 := by
  induction k with
  | zero => simp
  | succ k ih =>
    have e : y ^ (k + 1) - 1 = y * (y ^ k - 1) + (y - 1) := by ring
    rw [e]
    exact add_mem (GlobalTheory.CongApprox.mul_mem_hatId D 𝔪 y hy _ ih) hy1

set_option maxHeartbeats 1600000 in

/- English proof (translation)
Introduce `D 𝔪 h𝔪 y hy hy1`. Take `⟨hsep, hcpl⟩` from `GlobalTheory.T.cmFiniteAdele_integral_separated_complete D`. Set `R : ℕ → ℕ` to `fun N => ∑ n ∈ Finset.range (N + 1), Nat.card (OhE D ⧸ Ideal.span {(n : OhE D)})`. Establish `hR : ∀ N : ℕ, Nat.card (OhE D ⧸ Ideal.span {(N : OhE D)}) ≤ R N` using `fun N => Finset.single_le_sum (f := fun n : ℕ => Nat.card (OhE D ⧸ Ideal.span {((n : ℕ) : OhE D)})) (fun _ _ => Nat.zero_le _) (Finset.self_mem_range_succ N)`. Establish `hRmono : ∀ N M, N ≤ M → R N ≤ R M` using `fun N M h => Finset.sum_le_sum_of_subset (by intro a ha; simp only [Finset.mem_range] at ha ⊢; omega)`.

Set `ys : OhE D` to `⟨y, hy⟩`. Set `e : ℕ → ℕ` to `fun N => 2 * (R N).factorial - 1`. Establish `key : ∀ N : ℕ, 0 < N → ∀ k j, R N ≤ k → (Ideal.Quotient.mk (Ideal.span {(N : OhE D)}) ys) ^ (k + j * (R N).factorial) = (Ideal.Quotient.mk (Ideal.span {(N : OhE D)}) ys) ^ k`. Introduce `N hN k j hk`. Use `haveI := finite_quot D N hN`.

Conclude with `pow_add_mul_factorial _ _ (hR N) k j hk`. Establish `he : ∀ N : ℕ, R N ≤ e N`. Introduce `N`. Use `Nat.self_le_factorial (R N)` as an intermediate fact. Use `Nat.factorial_pos (R N)` as an intermediate fact.

Simplify using `only [e]`. Use linear arithmetic over natural numbers and integers. Establish `he1 : ∀ N : ℕ, e N + 1 = 2 * (R N).factorial`. Introduce `N`. Use `Nat.factorial_pos (R N)` as an intermediate fact.

Simplify using `only [e]`. Use linear arithmetic over natural numbers and integers. Establish `hediv : ∀ N M : ℕ, R N ≤ R M → ∃ j : ℕ, e M = e N + j * (R N).factorial`. Introduce `N M hle`. Take `⟨c, hc⟩` from `Nat.factorial_dvd_factorial hle`.

Establish `hF` using `Nat.factorial_pos (R N)`. Establish `hc0 : 0 < c`. Break down `Nat.eq_zero_or_pos c with h0 | h0` into its components or cases. Use `Nat.factorial_pos (R M)` as an intermediate fact. Rewrite `this` using `[hc, h0, mul_zero]`.

Use linear arithmetic over natural numbers and integers. Conclude with `h0`. Take `⟨c', rfl⟩` from `Nat.exists_eq_add_of_le' hc0`. Use `⟨2 * c', ?_⟩` and prove the remaining obligations. Simplify using `only [e]`.

Rewrite using `[hc]`. Establish `h1 : (R N).factorial * (c' + 1) = (R N).factorial * c' + (R N).factorial` using `by ring`. Establish `h2 : 2 * c' * (R N).factorial = 2 * ((R N).factorial * c')` using `by ring`. Rewrite using `[h1, h2]`. Use linear arithmetic over natural numbers and integers.

Use `clear_value e R`. Set `x : ℕ → AE D` to `fun N => ((ys ^ e N : OhE D) : AE D)`. Establish `hx : ∀ N : ℕ, x N ∈ OhE D` using `fun N => (ys ^ e N).2`. Establish `hcong : ∀ N m : ℕ, 0 < N → 0 < m → ∃ w ∈ OhE D, x (N * m) = x N + (N : AE D) * w`. Introduce `N m hN hm`.

Apply `exists_of_mk_eq` to reduce the goal to its premises. Take `⟨j, hj⟩` from `hediv N (N * m) (hRmono _ _ (Nat.le_mul_of_pos_right N hm))`. Rewrite using `[map_pow, map_pow, hj, key N hN _ _ (he N)]`. Take `⟨g, hg, hgN⟩` from `hcpl x hx hcong`. Set `gs : OhE D` to `⟨g, hg⟩`.

Establish `hmk : ∀ N : ℕ, 0 < N → Ideal.Quotient.mk (Ideal.span {(N : OhE D)}) gs = (Ideal.Quotient.mk (Ideal.span {(N : OhE D)}) ys) ^ e N`. Introduce `N hN`. Take `⟨w, hw, h⟩` from `hgN N hN`. Rewrite using `[← map_pow]`. Conclude with `mk_eq_of_exists D N gs (ys ^ e N) w hw h`.

Establish `hyg : ∀ N : ℕ, 0 < N → Ideal.Quotient.mk (Ideal.span {(N : OhE D)}) (ys * gs) = (Ideal.Quotient.mk (Ideal.span {(N : OhE D)}) ys) ^ (2 * (R N).factorial)`. Introduce `N hN`. Rewrite using `[map_mul, hmk N hN, ← he1]`. Conclude with `(pow_succ' _ _).symm`. Use `⟨g, hg, ?_, ?_⟩` and prove the remaining obligations.

Establish `h0 : y * g * (y * g) - y * g = 0`. Apply `hsep` to reduce the goal to its premises. Introduce `N hN`. Establish `hq : Ideal.Quotient.mk (Ideal.span {(N : OhE D)}) (ys * gs * (ys * gs)) = Ideal.Quotient.mk (Ideal.span {(N : OhE D)}) (ys * gs)`. Establish `hk : R N ≤ 2 * (R N).factorial` using `(he N).trans ((Nat.le_succ _).trans (he1 N).le)`.

Combine the equalities or inequalities in the displayed calculation. Rewrite using `[hyg N hN]`. Use `_ = (Ideal.Quotient.mk (Ideal.span {(N : OhE D)}) ys) ^ (2 * (R N).factorial + 2 * (R N).factorial) := (pow_add _ _ _).symm`. Use `_ = (Ideal.Quotient.mk (Ideal.span {(N : OhE D)}) ys) ^ (2 * (R N).factorial) := key N hN _ 2 hk`. Use `_ = Ideal.Quotient.mk (Ideal.span {(N : OhE D)}) (ys * gs) := (hyg N hN).symm`.

Take `⟨w, hw, h⟩` from `exists_of_mk_eq D N _ _ hq`. Use `⟨w, hw, ?_⟩` and prove the remaining obligations. Establish `h' : y * g * (y * g) = y * g + (N : AE D) * w` using `h`. Rewrite using `[h']`. Expand and normalize the polynomial expressions, which then agree.

Conclude with `sub_eq_zero.1 h0`. Establish `hN0 : 0 < Ideal.absNorm 𝔪`. Break down `Nat.eq_zero_or_pos (Ideal.absNorm 𝔪) with h0 | h0` into its components or cases. Conclude with `absurd (Ideal.absNorm_eq_zero_iff.1 h0) h𝔪`. Conclude with `h0`.

Take `⟨w, hw, h⟩` from `exists_of_mk_eq D (Ideal.absNorm 𝔪) (ys * gs) (ys ^ (2 * (R (Ideal.absNorm 𝔪)).factorial)) (by rw [map_pow]; exact hyg _ hN0)`. Establish `h' : y * g = y ^ (2 * (R (Ideal.absNorm 𝔪)).factorial) + (Ideal.absNorm 𝔪 : AE D) * w`. Conclude with `h`. Establish `hmem : (Ideal.absNorm 𝔪 : AE D) * w ∈ hatId D 𝔪`. Use `AddSubgroup.subset_closure ⟨(Ideal.absNorm 𝔪 : 𝓞 D.host.E), Ideal.absNorm_mem 𝔪, w, hw, ?_⟩` and prove the remaining obligations.

Use `congr 1`. Rewrite using `[h', show y ^ (2 * (R (Ideal.absNorm 𝔪)).factorial) + (Ideal.absNorm 𝔪 : AE D) * w - 1 = (y ^ (2 * (R (Ideal.absNorm 𝔪)).factorial) - 1) + (Ideal.absNorm 𝔪 : AE D) * w by ring]`. Conclude with `add_mem (pow_sub_one_mem D 𝔪 y hy hy1 _) hmem`.
-/
theorem exists_idem : ∀ (D : D7) (𝔪 : Ideal (𝓞 D.host.E)), 𝔪 ≠ ⊥ → ∀ y ∈ OhE D, y - 1 ∈ hatId D 𝔪 → ∃ g ∈ OhE D, y * g * (y * g) = y * g ∧ y * g - 1 ∈ hatId D 𝔪 := by
  intro D 𝔪 h𝔪 y hy hy1
  obtain ⟨hsep, hcpl⟩ := GlobalTheory.T.cmFiniteAdele_integral_separated_complete D
  let R : ℕ → ℕ := fun N =>
    ∑ n ∈ Finset.range (N + 1), Nat.card (OhE D ⧸ Ideal.span {(n : OhE D)})
  have hR : ∀ N : ℕ, Nat.card (OhE D ⧸ Ideal.span {(N : OhE D)}) ≤ R N := fun N =>
    Finset.single_le_sum (f := fun n : ℕ => Nat.card (OhE D ⧸ Ideal.span {((n : ℕ) : OhE D)}))
      (fun _ _ => Nat.zero_le _) (Finset.self_mem_range_succ N)
  have hRmono : ∀ N M, N ≤ M → R N ≤ R M := fun N M h =>
    Finset.sum_le_sum_of_subset (by intro a ha; simp only [Finset.mem_range] at ha ⊢; omega)
  let ys : OhE D := ⟨y, hy⟩
  let e : ℕ → ℕ := fun N => 2 * (R N).factorial - 1
  have key : ∀ N : ℕ, 0 < N → ∀ k j, R N ≤ k →
      (Ideal.Quotient.mk (Ideal.span {(N : OhE D)}) ys) ^ (k + j * (R N).factorial) =
        (Ideal.Quotient.mk (Ideal.span {(N : OhE D)}) ys) ^ k := by
    intro N hN k j hk
    haveI := finite_quot D N hN
    exact pow_add_mul_factorial _ _ (hR N) k j hk
  have he : ∀ N : ℕ, R N ≤ e N := by
    intro N
    have := Nat.self_le_factorial (R N)
    have := Nat.factorial_pos (R N)
    simp only [e]
    omega
  have he1 : ∀ N : ℕ, e N + 1 = 2 * (R N).factorial := by
    intro N
    have := Nat.factorial_pos (R N)
    simp only [e]
    omega
  have hediv : ∀ N M : ℕ, R N ≤ R M → ∃ j : ℕ, e M = e N + j * (R N).factorial := by
    intro N M hle
    obtain ⟨c, hc⟩ := Nat.factorial_dvd_factorial hle
    have hF := Nat.factorial_pos (R N)
    have hc0 : 0 < c := by
      rcases Nat.eq_zero_or_pos c with h0 | h0
      · have := Nat.factorial_pos (R M); rw [hc, h0, mul_zero] at this; omega
      · exact h0
    obtain ⟨c', rfl⟩ := Nat.exists_eq_add_of_le' hc0
    refine ⟨2 * c', ?_⟩
    simp only [e]
    rw [hc]
    have h1 : (R N).factorial * (c' + 1) = (R N).factorial * c' + (R N).factorial := by ring
    have h2 : 2 * c' * (R N).factorial = 2 * ((R N).factorial * c') := by ring
    rw [h1, h2]
    omega
  clear_value e R
  let x : ℕ → AE D := fun N => ((ys ^ e N : OhE D) : AE D)
  have hx : ∀ N : ℕ, x N ∈ OhE D := fun N => (ys ^ e N).2
  have hcong : ∀ N m : ℕ, 0 < N → 0 < m → ∃ w ∈ OhE D, x (N * m) = x N + (N : AE D) * w := by
    intro N m hN hm
    apply exists_of_mk_eq
    obtain ⟨j, hj⟩ := hediv N (N * m) (hRmono _ _ (Nat.le_mul_of_pos_right N hm))
    rw [map_pow, map_pow, hj, key N hN _ _ (he N)]
  obtain ⟨g, hg, hgN⟩ := hcpl x hx hcong
  let gs : OhE D := ⟨g, hg⟩
  have hmk : ∀ N : ℕ, 0 < N → Ideal.Quotient.mk (Ideal.span {(N : OhE D)}) gs =
      (Ideal.Quotient.mk (Ideal.span {(N : OhE D)}) ys) ^ e N := by
    intro N hN
    obtain ⟨w, hw, h⟩ := hgN N hN
    rw [← map_pow]
    exact mk_eq_of_exists D N gs (ys ^ e N) w hw h
  have hyg : ∀ N : ℕ, 0 < N → Ideal.Quotient.mk (Ideal.span {(N : OhE D)}) (ys * gs) =
      (Ideal.Quotient.mk (Ideal.span {(N : OhE D)}) ys) ^ (2 * (R N).factorial) := by
    intro N hN
    rw [map_mul, hmk N hN, ← he1]
    exact (pow_succ' _ _).symm
  refine ⟨g, hg, ?_, ?_⟩
  · have h0 : y * g * (y * g) - y * g = 0 := by
      apply hsep
      intro N hN
      have hq : Ideal.Quotient.mk (Ideal.span {(N : OhE D)}) (ys * gs * (ys * gs)) =
          Ideal.Quotient.mk (Ideal.span {(N : OhE D)}) (ys * gs) := by
        have hk : R N ≤ 2 * (R N).factorial := (he N).trans ((Nat.le_succ _).trans (he1 N).le)
        calc Ideal.Quotient.mk (Ideal.span {(N : OhE D)}) (ys * gs * (ys * gs))
            = Ideal.Quotient.mk (Ideal.span {(N : OhE D)}) (ys * gs) *
                Ideal.Quotient.mk (Ideal.span {(N : OhE D)}) (ys * gs) := map_mul _ _ _
          _ = (Ideal.Quotient.mk (Ideal.span {(N : OhE D)}) ys) ^ (2 * (R N).factorial) *
                (Ideal.Quotient.mk (Ideal.span {(N : OhE D)}) ys) ^ (2 * (R N).factorial) := by
              rw [hyg N hN]
          _ = (Ideal.Quotient.mk (Ideal.span {(N : OhE D)}) ys) ^
                (2 * (R N).factorial + 2 * (R N).factorial) := (pow_add _ _ _).symm
          _ = (Ideal.Quotient.mk (Ideal.span {(N : OhE D)}) ys) ^ (2 * (R N).factorial) :=
              key N hN _ 2 hk
          _ = Ideal.Quotient.mk (Ideal.span {(N : OhE D)}) (ys * gs) := (hyg N hN).symm
      obtain ⟨w, hw, h⟩ := exists_of_mk_eq D N _ _ hq
      refine ⟨w, hw, ?_⟩
      have h' : y * g * (y * g) = y * g + (N : AE D) * w := h
      rw [h']; ring
    exact sub_eq_zero.1 h0
  · have hN0 : 0 < Ideal.absNorm 𝔪 := by
      rcases Nat.eq_zero_or_pos (Ideal.absNorm 𝔪) with h0 | h0
      · exact absurd (Ideal.absNorm_eq_zero_iff.1 h0) h𝔪
      · exact h0
    obtain ⟨w, hw, h⟩ := exists_of_mk_eq D (Ideal.absNorm 𝔪) (ys * gs) (ys ^ (2 * (R (Ideal.absNorm 𝔪)).factorial))
      (by rw [map_pow]; exact hyg _ hN0)
    have h' : y * g = y ^ (2 * (R (Ideal.absNorm 𝔪)).factorial) + (Ideal.absNorm 𝔪 : AE D) * w := by
      exact h
    have hmem : (Ideal.absNorm 𝔪 : AE D) * w ∈ hatId D 𝔪 := by
      refine AddSubgroup.subset_closure ⟨(Ideal.absNorm 𝔪 : 𝓞 D.host.E), Ideal.absNorm_mem 𝔪, w, hw, ?_⟩
      congr 1
    rw [h', show y ^ (2 * (R (Ideal.absNorm 𝔪)).factorial) + (Ideal.absNorm 𝔪 : AE D) * w - 1 =
      (y ^ (2 * (R (Ideal.absNorm 𝔪)).factorial) - 1) + (Ideal.absNorm 𝔪 : AE D) * w by ring]
    exact add_mem (pow_sub_one_mem D 𝔪 y hy hy1 _) hmem

end GlobalTheory.PowIdem

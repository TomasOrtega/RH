import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HasLenOfLatLen

noncomputable section

open Formalism.UG Matrix GlobalTheory.SatakeWeyl

namespace GlobalTheory.InertZeta

variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {σ : L →+* L} {ϖ : L} {q N : ℕ}

omit [Valued L (WithZero (Multiplicative ℤ))] in
/- English proof (translation)
The claim follows from `((Matrix.isUnit_iff_isUnit_det _).mp (g : GL (Fin n) L).isUnit).ne_zero`.
-/
theorem det_mat_ne_zero {n : ℕ} (g : GU σ n) : (mat g).det ≠ 0 := ((Matrix.isUnit_iff_isUnit_det _).mp (g : GL (Fin n) L).isUnit).ne_zero

/- English proof (translation)
Establish `hv : Valued.v ϖ = WithZero.exp (-1 : ℤ)` using `hU.2.2.2.1`. Establish `hq : 1 ≤ q` using `le_trans (by norm_num) hU.2.2.2.2.2.1`. Take `⟨U, V, C, hfr, hdet⟩` from `hF L ϖ N hv (mat g₀) (det_mat_ne_zero g₀)`. Establish `hPt` using `hP L ϖ σ q N hU a g₀ m hm U V C (len (mat g₀)) hfr hdet`. Establish `hcard : ∀ j : ℕ, Nat.card {c : RadQuot σ N // len (mat (m * (c.out : radQ σ N).1)) ≤ a.natAbs + len (mat g₀) + j} = q ^ (2 * len (mat g₀) + (2 * N + 2) * a.toNat) * q ^ (2 * N * (j / 2) + j)`.

Introduce `j`. Establish `hiff : ∀ c : RadQuot σ N, len (mat (m * (c.out : radQ σ N).1)) ≤ a.natAbs + len (mat g₀) + j ↔ Small ϖ (a.toNat + j / 2) (2 * a.toNat + j) C (C * V * mat g₀) (c.out : radQ σ N).1` using `fun c => (hPt _ (c.out : radQ σ N).2).2 j`. Rewrite using `[Nat.card_congr (Equiv.subtypeEquivRight hiff)]`. Rewrite using `[hC L ϖ σ q N hU C (C * V * mat g₀) (len (mat g₀)) (a.toNat + j / 2) (2 * a.toNat + j) hfr.2.2.1 hdet (fun r hr => hS L ϖ σ q N hU g₀ U V C hfr _ _ r (by omega) hr) ?_]`. Rewrite using `[← pow_add]`.

Use `congr 1`. Generalize the expression as in `j / 2 = t`. Expand and normalize the polynomial expressions, which then agree. Introduce `u hu k hk hkK hsm`. Establish `hlen : len (mat (m * (u * k))) = len (mat (m * u))`.

Establish `h` using `len_mat_mul (KU σ (N + 2)).one_mem hkK (m * u)`. Rewrite `h` using `[one_mul, mul_assoc]`. Then use the resulting hypothesis. Use `((hPt _ (mul_mem hu hk)).2 j).mp ?_` and prove the remaining obligations. Rewrite using `[hlen]`. Conclude with `((hPt u hu).2 j).mpr hsm`.

Establish `key` using `hG (RadQuot σ N) (fun c => len (mat (m * (c.out : radQ σ N).1))) (a.natAbs + len (mat g₀)) (q ^ (2 * len (mat g₀) + (2 * N + 2) * a.toNat)) q N X (Nat.one_le_pow _ _ hq) hq (fun c => (hPt _ (c.out : radQ σ N).2).1) hcard hX`. Move the coercions through the operations in `at key`. Conclude with `key`.
-/
theorem constTerm (hF : FracExists) (hP : Pointwise) (hC : Count) (hS : SmallCorner) (hG : GenFun)
    (hU : IsUnramInv ϖ σ q) {a : ℤ} {g₀ : GU σ N} {m : GU σ (N + 2)} (hm : IsLeviElt ϖ a g₀ m) (X : ℂ)
    (hX : ‖(q : ℂ) ^ (N + 1) * X‖ < 1) :
    HasSum (fun c : RadQuot σ N => X ^ len (mat (m * (c.out : radQ σ N).1)))
      ((q : ℂ) ^ (2 * len (mat g₀) + (2 * N + 2) * a.toNat) * X ^ (a.natAbs + len (mat g₀)) * jFac q N X) := by
  have hv : Valued.v ϖ = WithZero.exp (-1 : ℤ) := hU.2.2.2.1
  have hq : 1 ≤ q := le_trans (by norm_num) hU.2.2.2.2.2.1
  obtain ⟨U, V, C, hfr, hdet⟩ := hF L ϖ N hv (mat g₀) (det_mat_ne_zero g₀)
  have hPt := hP L ϖ σ q N hU a g₀ m hm U V C (len (mat g₀)) hfr hdet
  have hcard : ∀ j : ℕ, Nat.card {c : RadQuot σ N //
      len (mat (m * (c.out : radQ σ N).1)) ≤ a.natAbs + len (mat g₀) + j} =
      q ^ (2 * len (mat g₀) + (2 * N + 2) * a.toNat) * q ^ (2 * N * (j / 2) + j) := by
    intro j
    have hiff : ∀ c : RadQuot σ N, len (mat (m * (c.out : radQ σ N).1)) ≤ a.natAbs + len (mat g₀) + j ↔
        Small ϖ (a.toNat + j / 2) (2 * a.toNat + j) C (C * V * mat g₀) (c.out : radQ σ N).1 :=
      fun c => (hPt _ (c.out : radQ σ N).2).2 j
    rw [Nat.card_congr (Equiv.subtypeEquivRight hiff)]
    rw [hC L ϖ σ q N hU C (C * V * mat g₀) (len (mat g₀)) (a.toNat + j / 2) (2 * a.toNat + j) hfr.2.2.1 hdet
      (fun r hr => hS L ϖ σ q N hU g₀ U V C hfr _ _ r (by omega) hr) ?_]
    · rw [← pow_add]; congr 1; generalize j / 2 = t; ring
    · intro u hu k hk hkK hsm
      have hlen : len (mat (m * (u * k))) = len (mat (m * u)) := by
        have h := len_mat_mul (KU σ (N + 2)).one_mem hkK (m * u)
        rwa [one_mul, mul_assoc] at h
      refine ((hPt _ (mul_mem hu hk)).2 j).mp ?_
      rw [hlen]
      exact ((hPt u hu).2 j).mpr hsm
  have key := hG (RadQuot σ N) (fun c => len (mat (m * (c.out : radQ σ N).1))) (a.natAbs + len (mat g₀))
    (q ^ (2 * len (mat g₀) + (2 * N + 2) * a.toNat)) q N X (Nat.one_le_pow _ _ hq) hq
    (fun c => (hPt _ (c.out : radQ σ N).2).1) hcard hX
  push_cast at key
  exact key

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨⟨a, y⟩, c⟩ ⟨⟨a', y'⟩, c'⟩ h`. Establish `h'` using `QuotientGroup.eq.mp h`. Take `⟨rfl, hy⟩` from `hI L ϖ σ q N hU a a' y.out y'.out (m a y) (m a' y') (hm a y) (hm a' y') _ (c.out : radQ σ N).2 _ (c'.out : radQ σ N).2 h'`. Establish `hyy : y = y'`.

Rewrite using `[← QuotientGroup.out_eq' y, ← QuotientGroup.out_eq' y']`. Conclude with `QuotientGroup.eq.mpr hy`. Substitute `hyy` using the available equality. Establish `hc : c = c'`. Rewrite using `[← QuotientGroup.out_eq' c, ← QuotientGroup.out_eq' c']`.

Apply `QuotientGroup.eq.mpr` to reduce the goal to its premises. Rewrite using `[Subgroup.mem_subgroupOf]`. Simplify `h'` using `[mul_assoc]`. Rewrite using `[hc]`. Introduce `z`.

Take `⟨g, rfl⟩` from `QuotientGroup.mk_surjective z`. Take `⟨a, y, hay⟩` from `hS L ϖ σ q N hU g`. Take `⟨u, hu, k, hk, rfl⟩` from `hay (m a y) (hm a y)`. Use `⟨((a, y), (QuotientGroup.mk ⟨u, hu⟩ : RadQuot σ N)), ?_⟩` and prove the remaining obligations. Simplify using `only`.

Apply `QuotientGroup.eq.mpr` to reduce the goal to its premises. Establish `h1` using `QuotientGroup.eq.mp (QuotientGroup.out_eq' (QuotientGroup.mk ⟨u, hu⟩ : RadQuot σ N))`. Rewrite `h1` using `[Subgroup.mem_subgroupOf]`. Establish `e : (m a y * ((QuotientGroup.mk ⟨u, hu⟩ : RadQuot σ N).out : radQ σ N).1)⁻¹ * (m a y * u * k) = (((QuotientGroup.mk ⟨u, hu⟩ : RadQuot σ N).out)⁻¹ * ⟨u, hu⟩ : radQ σ N).1 * k`. Simplify using `[mul_assoc]`.

Rewrite using `[e]`. Conclude with `mul_mem h1 hk`.
-/
theorem bijective_cells (hS : CosetSurj) (hI : CosetInj) (hU : IsUnramInv ϖ σ q)
    (m : ℤ → GU σ N ⧸ KU σ N → GU σ (N + 2)) (hm : ∀ a y, IsLeviElt ϖ a y.out (m a y)) :
    Function.Bijective fun p : (ℤ × (GU σ N ⧸ KU σ N)) × RadQuot σ N =>
      (QuotientGroup.mk (m p.1.1 p.1.2 * (p.2.out : radQ σ N).1) : GU σ (N + 2) ⧸ KU σ (N + 2)) := by
  constructor
  · rintro ⟨⟨a, y⟩, c⟩ ⟨⟨a', y'⟩, c'⟩ h
    have h' := QuotientGroup.eq.mp h
    obtain ⟨rfl, hy⟩ := hI L ϖ σ q N hU a a' y.out y'.out (m a y) (m a' y') (hm a y) (hm a' y')
      _ (c.out : radQ σ N).2 _ (c'.out : radQ σ N).2 h'
    have hyy : y = y' := by
      rw [← QuotientGroup.out_eq' y, ← QuotientGroup.out_eq' y']
      exact QuotientGroup.eq.mpr hy
    subst hyy
    have hc : c = c' := by
      rw [← QuotientGroup.out_eq' c, ← QuotientGroup.out_eq' c']
      apply QuotientGroup.eq.mpr
      rw [Subgroup.mem_subgroupOf]
      simpa [mul_assoc] using h'
    rw [hc]
  · intro z
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective z
    obtain ⟨a, y, hay⟩ := hS L ϖ σ q N hU g
    obtain ⟨u, hu, k, hk, rfl⟩ := hay (m a y) (hm a y)
    refine ⟨((a, y), (QuotientGroup.mk ⟨u, hu⟩ : RadQuot σ N)), ?_⟩
    dsimp only
    apply QuotientGroup.eq.mpr
    have h1 := QuotientGroup.eq.mp (QuotientGroup.out_eq' (QuotientGroup.mk ⟨u, hu⟩ : RadQuot σ N))
    rw [Subgroup.mem_subgroupOf] at h1
    have e : (m a y * ((QuotientGroup.mk ⟨u, hu⟩ : RadQuot σ N).out : radQ σ N).1)⁻¹ * (m a y * u * k) =
        (((QuotientGroup.mk ⟨u, hu⟩ : RadQuot σ N).out)⁻¹ * ⟨u, hu⟩ : radQ σ N).1 * k := by
      simp [mul_assoc]
    rw [e]
    exact mul_mem h1 hk

/- English proof (translation)
Establish `hp : ∏ j ∈ Finset.range (N + 2), (1 - (-(q : ℂ)) ^ j * X) = (1 - X) * (1 + q * X) * ∏ j ∈ Finset.range N, (1 - (-(q : ℂ)) ^ j * ((q : ℂ) ^ 2 * X))`. Rewrite using `[Finset.prod_range_succ', Finset.prod_range_succ']`. Establish `h : ∀ j ∈ Finset.range N, (1 - (-(q : ℂ)) ^ (j + 1 + 1) * X) = (1 - (-(q : ℂ)) ^ j * ((q : ℂ) ^ 2 * X))`. Introduce `j _`. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[Finset.prod_congr rfl h]`. Expand and normalize the polynomial expressions, which then agree. Establish `ho : Odd (N + 2) ↔ Odd N` using `by rw [Nat.odd_add]; simp`. Unfold `zVal`. Rewrite using `[hp, Fin.prod_univ_succ, if_congr ho rfl rfl]`.

Simplify using `only [Fin.tail]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem zVal_succ (q N : ℕ) (X y : ℂ) {r : ℕ} (α : Fin (r + 1) → ℂ) :
    zVal q (N + 2) X y α = (1 - X) * (1 + q * X) * ((1 - y * α 0)⁻¹ * (1 - y / α 0)⁻¹) *
      zVal q N ((q : ℂ) ^ 2 * X) y (Fin.tail α) := by
  have hp : ∏ j ∈ Finset.range (N + 2), (1 - (-(q : ℂ)) ^ j * X) =
      (1 - X) * (1 + q * X) * ∏ j ∈ Finset.range N, (1 - (-(q : ℂ)) ^ j * ((q : ℂ) ^ 2 * X)) := by
    rw [Finset.prod_range_succ', Finset.prod_range_succ']
    have h : ∀ j ∈ Finset.range N,
        (1 - (-(q : ℂ)) ^ (j + 1 + 1) * X) = (1 - (-(q : ℂ)) ^ j * ((q : ℂ) ^ 2 * X)) := by
      intro j _; ring
    rw [Finset.prod_congr rfl h]; ring
  have ho : Odd (N + 2) ↔ Odd N := by rw [Nat.odd_add]; simp
  unfold zVal
  rw [hp, Fin.prod_univ_succ, if_congr ho rfl rfl]
  simp only [Fin.tail]
  ring

/- English proof (translation)
Establish `hK : ∀ g : GU σ n, g ∈ KU σ n` using `fun g => hR L ϖ σ q n hU hn g`. Establish `h1 : (fun x : GU σ n ⧸ KU σ n => F x.out) = fun _ => 1` using `funext fun x => hF _ (hK _)`. Rewrite using `[h1]`. Use `hasSum_single (f := fun _ : GU σ n ⧸ KU σ n => (1 : ℂ)) (QuotientGroup.mk 1) fun b hb => ?_` and prove the remaining obligations. It suffices to derive a contradiction.

Apply `hb` to reduce the goal to its premises. Take `⟨a, rfl⟩` from `QuotientGroup.mk_surjective b`. Conclude with `QuotientGroup.eq.mpr (hK _)`.
-/
theorem hasSum_small (hR : SmallRank) (hU : IsUnramInv ϖ σ q) {n : ℕ} (hn : n ≤ 1) (F : GU σ n → ℂ)
    (hF : ∀ k ∈ KU σ n, F k = 1) : HasSum (fun x : GU σ n ⧸ KU σ n => F x.out) 1 := by
  have hK : ∀ g : GU σ n, g ∈ KU σ n := fun g => hR L ϖ σ q n hU hn g
  have h1 : (fun x : GU σ n ⧸ KU σ n => F x.out) = fun _ => 1 := funext fun x => hF _ (hK _)
  rw [h1]
  refine hasSum_single (f := fun _ : GU σ n ⧸ KU σ n => (1 : ℂ)) (QuotientGroup.mk 1) fun b hb => ?_
  exfalso; apply hb
  obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective b
  exact QuotientGroup.eq.mpr (hK _)

/- English proof (translation)
Apply `HasLen.len_eq` to reduce the goal to its premises. Apply `hasLen_of_isInt` to reduce the goal to its premises. Introduce `i j`. Rewrite `hk` using `[KU, Subgroup.mem_subgroupOf]`. Unfold `intPts at hk`.

Take `⟨A, hA⟩` from `(Subgroup.mem_inf.mp hk).2`. Use `show (((k : GU σ n) : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) i j ∈ intL L`. Rewrite using `[← hA]`. Conclude with `((A : Matrix (Fin n) (Fin n) (intL L)) i j).2`.
-/
theorem len_of_mem {n : ℕ} {k : GU σ n} (hk : k ∈ KU σ n) : len (mat k) = 0 := by
  apply HasLen.len_eq
  apply hasLen_of_isInt
  intro i j
  rw [KU, Subgroup.mem_subgroupOf] at hk
  unfold intPts at hk
  obtain ⟨A, hA⟩ := (Subgroup.mem_inf.mp hk).2
  show (((k : GU σ n) : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) i j ∈ intL L
  rw [← hA]
  exact ((A : Matrix (Fin n) (Fin n) (intL L)) i j).2

/- English proof (translation)
Establish `h : Valued.v (1 : L) ≠ 0` using `by simp`. Establish `hu : WithZero.unzero h = 1`. Apply `WithZero.coe_injective` to reduce the goal to its premises. Rewrite using `[WithZero.coe_unzero, map_one, WithZero.coe_one]`. Unfold `ordL`.

Rewrite using `[dif_neg h, hu]`. Simplify using the standard rewrite rules.
-/
private lemma ordL_one_twisted_operators : ordL (1 : L) = 0 := by
  have h : Valued.v (1 : L) ≠ 0 := by simp
  have hu : WithZero.unzero h = 1 := by
    apply WithZero.coe_injective
    rw [WithZero.coe_unzero, map_one, WithZero.coe_one]
  unfold ordL
  rw [dif_neg h, hu]
  simp

/- English proof (translation)
Unfold `chiDeltaU`. Use `Finset.prod_eq_one fun i _ => ?_` and prove the remaining obligations. Use `split_ifs`. Simplify using `[ordL_one_twisted_operators]`. Both sides reduce to the same expression.
-/
private lemma chiDeltaU_one' {n m : ℕ} (α : Fin m → ℂ) : chiDeltaU (σ := σ) (n := n) q α 1 = 1 := by
  unfold chiDeltaU
  refine Finset.prod_eq_one fun i _ => ?_
  split_ifs
  · simp [ordL_one_twisted_operators]
  · rfl

/- English proof (translation)
Introduce `i j h`. Simplify using `[Matrix.one_apply_ne h.ne']`.
-/
private lemma isBorelU_one' {n : ℕ} : IsBorelU (1 : GU σ n) := by
  intro i j h
  simp [Matrix.one_apply_ne h.ne']

/- English proof (translation)
Establish `h` using `hφ 1 g k isBorelU_one' hk`. Rewrite `h` using `[one_mul, chiDeltaU_one', one_mul]`. Then use the resulting hypothesis.
-/
private lemma isSphericalU_apply_mul_of_mem_KU {n m : ℕ} {α : Fin m → ℂ} {φ : GU σ n → ℂ} (hφ : IsSphericalU q α φ) (g k : GU σ n)
    (hk : k ∈ KU σ n) : φ (g * k) = φ g := by
  have h := hφ 1 g k isBorelU_one' hk
  rwa [one_mul, chiDeltaU_one', one_mul] at h

/- English proof (translation)
Use `⟨g⁻¹ * (QuotientGroup.mk g : GU σ n ⧸ KU σ n).out, ?_, (mul_inv_cancel_left _ _).symm⟩` and prove the remaining obligations. Establish `h` using `QuotientGroup.eq.mp (QuotientGroup.out_eq' (QuotientGroup.mk g : GU σ n ⧸ KU σ n))`. Simplify `inv_mem h` using `[_root_.mul_inv_rev]`.
-/
private lemma exists_mem_KU_out_mk_eq_mul {n : ℕ} (g : GU σ n) :
    ∃ k ∈ KU σ n, (QuotientGroup.mk g : GU σ n ⧸ KU σ n).out = g * k := by
  refine ⟨g⁻¹ * (QuotientGroup.mk g : GU σ n ⧸ KU σ n).out, ?_, (mul_inv_cancel_left _ _).symm⟩
  have h := QuotientGroup.eq.mp (QuotientGroup.out_eq' (QuotientGroup.mk g : GU σ n ⧸ KU σ n))
  simpa [_root_.mul_inv_rev] using inv_mem h

/- English proof (translation)
Establish `hq2 : 2 ≤ q` using `hU.2.2.2.2.2.1`. Establish `hq0 : (q : ℂ) ≠ 0` using `by exact_mod_cast (show q ≠ 0 by omega)`. Proceed by induction on `r with`. Consider the case `zero`. Introduce `n hn0 hn1 α X y φ _ hyX hy _ hφ h1`.

Establish `hn : n ≤ 1` using `by omega`. Establish `hK : ∀ g : GU σ n, g ∈ KU σ n` using `fun g => hR L ϖ σ q n hU hn g`. Establish `hφk : ∀ g : GU σ n, φ g = 1`. Introduce `g`. Establish `h` using `isSphericalU_apply_mul_of_mem_KU hφ 1 g (hK g)`.

Rewrite `h` using `[one_mul, h1]`. Then use the resulting hypothesis. Establish `hsum` using `hasSum_small hR hU hn (fun g => X ^ len (mat g) * φ g) (fun k hk => by rw [len_of_mem hk, hφk, pow_zero, one_mul])`. Use `hsum using 1` and compare the differences between its conclusion and the goal. Use `interval_cases n`. Simplify using `[zVal]`.

Establish `hyx : y = X`. Apply `mul_right_cancel₀ hq0` to reduce the goal to its premises. Rewrite using `[hyX]`. Expand and normalize the polynomial expressions, which then agree. Substitute `hyx` using the available equality.

Establish `hy1 : (1 : ℂ) - y ≠ 0`. Introduce `h`. Establish `h' : y = 1` using `by linear_combination -h`. Rewrite `hy` using `[h']`. Simplify using `at hy`.

Simplify using `[zVal, hy1]`. Consider the case `succ r ih`. Introduce `n hn0 hn1 α X y φ hα hyX hy hαy hφ h1`. Take `⟨N, rfl⟩ : ∃ N, n = N + 2` from `⟨n - 2, by omega⟩`. Take `⟨φ₀, hφ₀, hφ₀1, -⟩` from `Formalism.UG.Final.SphericalExistsU L ϖ σ q N r hU (by omega) (by omega) (Fin.tail α) (fun i => hα _)`.

Establish `hZ` using `ih N (by omega) (by omega) (Fin.tail α) ((q : ℂ) ^ 2 * X) y φ₀ (fun i => hα _) (by rw [hyX]; ring) hy (fun i => hαy _) hφ₀ hφ₀1`. Establish `hy' : y = (q : ℂ) ^ (N + 1) * X`. Apply `mul_right_cancel₀ hq0` to reduce the goal to its premises. Rewrite using `[hyX]`. Expand and normalize the polynomial expressions, which then agree.

Use `choose m hm using fun (a : ℤ) (b : GU σ N ⧸ KU σ N) => hL L ϖ σ q N hU a b.out`. Establish `hstep` using `hSt (GU σ N ⧸ KU σ N) (RadQuot σ N) q N (fun a b c => len (mat (m a b * (c.out : radQ σ N).1))) (fun b => len (mat b.out)) (fun b => φ₀ b.out) (α 0) X y (zVal q N ((q : ℂ) ^ 2 * X) y (Fin.tail α)) (by omega) (hα 0) hy' hy (hαy 0).1 (hαy 0).2 (fun X' hX' a b => constTerm hF hP hC …`. Rewrite using `[zVal_succ, ← (Equiv.ofBijective _ (bijective_cells hSu hI hU m hm)).hasSum_iff]`. Use `hstep using 1` and compare the differences between its conclusion and the goal. Use function extensionality and compare the values at `p`.

Take `⟨⟨a, b⟩, c⟩` from `p`. Simplify using `only [Function.comp_apply, Equiv.ofBijective_apply]`. Take `⟨k, hk, hout⟩` from `exists_mem_KU_out_mk_eq_mul (m a b * (c.out : radQ σ N).1)`. Establish `hlen` using `len_mat_mul (KU σ (N + 2)).one_mem hk (m a b * (c.out : radQ σ N).1)`. Rewrite `hlen` using `[one_mul]`.

Rewrite using `[hout, isSphericalU_apply_mul_of_mem_KU hφ _ _ hk, hlen, hT L ϖ σ q N r hU (by omega) α φ φ₀ hα hφ h1 hφ₀ hφ₀1 a b.out (m a b) (hm a b) _ (c.out : radQ σ N).2]`.
-/
theorem hasSum_spherical [CompleteSpace L] (hF : FracExists) (hP : Pointwise) (hC : Count) (hS : SmallCorner)
    (hG : GenFun) (hSu : CosetSurj) (hI : CosetInj) (hL : LeviExists) (hT : SphTrans) (hR : SmallRank) (hSt : Step)
    (hU : IsUnramInv ϖ σ q) (r : ℕ) : ∀ (n : ℕ), 2 * r ≤ n → n ≤ 2 * r + 1 → ∀ (α : Fin r → ℂ) (X y : ℂ)
      (φ : GU σ n → ℂ), (∀ i, α i ≠ 0) → y * q = X * (q : ℂ) ^ n → ‖y‖ < 1 →
      (∀ i, ‖y‖ * ‖α i‖ < 1 ∧ ‖y‖ * ‖α i‖⁻¹ < 1) → IsSphericalU q α φ → φ 1 = 1 →
      HasSum (fun x : GU σ n ⧸ KU σ n => X ^ len (mat x.out) * φ x.out) (zVal q n X y α) := by
  have hq2 : 2 ≤ q := hU.2.2.2.2.2.1
  have hq0 : (q : ℂ) ≠ 0 := by exact_mod_cast (show q ≠ 0 by omega)
  induction r with
  | zero =>
    intro n hn0 hn1 α X y φ _ hyX hy _ hφ h1
    have hn : n ≤ 1 := by omega
    have hK : ∀ g : GU σ n, g ∈ KU σ n := fun g => hR L ϖ σ q n hU hn g
    have hφk : ∀ g : GU σ n, φ g = 1 := by
      intro g
      have h := isSphericalU_apply_mul_of_mem_KU hφ 1 g (hK g)
      rwa [one_mul, h1] at h
    have hsum := hasSum_small hR hU hn (fun g => X ^ len (mat g) * φ g)
      (fun k hk => by rw [len_of_mem hk, hφk, pow_zero, one_mul])
    convert hsum using 1
    interval_cases n
    · simp [zVal]
    · have hyx : y = X := by
        apply mul_right_cancel₀ hq0
        rw [hyX]; ring
      subst hyx
      have hy1 : (1 : ℂ) - y ≠ 0 := by
        intro h
        have h' : y = 1 := by linear_combination -h
        rw [h'] at hy; simp at hy
      simp [zVal, hy1]
  | succ r ih =>
    intro n hn0 hn1 α X y φ hα hyX hy hαy hφ h1
    obtain ⟨N, rfl⟩ : ∃ N, n = N + 2 := ⟨n - 2, by omega⟩
    obtain ⟨φ₀, hφ₀, hφ₀1, -⟩ := Formalism.UG.Final.SphericalExistsU L ϖ σ q N r hU (by omega) (by omega)
      (Fin.tail α) (fun i => hα _)
    have hZ := ih N (by omega) (by omega) (Fin.tail α) ((q : ℂ) ^ 2 * X) y φ₀ (fun i => hα _)
      (by rw [hyX]; ring) hy (fun i => hαy _) hφ₀ hφ₀1
    have hy' : y = (q : ℂ) ^ (N + 1) * X := by
      apply mul_right_cancel₀ hq0
      rw [hyX]; ring
    choose m hm using fun (a : ℤ) (b : GU σ N ⧸ KU σ N) => hL L ϖ σ q N hU a b.out
    have hstep := hSt (GU σ N ⧸ KU σ N) (RadQuot σ N) q N
      (fun a b c => len (mat (m a b * (c.out : radQ σ N).1))) (fun b => len (mat b.out)) (fun b => φ₀ b.out)
      (α 0) X y (zVal q N ((q : ℂ) ^ 2 * X) y (Fin.tail α))
      (by omega) (hα 0) hy' hy (hαy 0).1 (hαy 0).2
      (fun X' hX' a b => constTerm hF hP hC hS hG hU (hm a b) X' hX') hZ
    rw [zVal_succ, ← (Equiv.ofBijective _ (bijective_cells hSu hI hU m hm)).hasSum_iff]
    convert hstep using 1
    funext p
    obtain ⟨⟨a, b⟩, c⟩ := p
    simp only [Function.comp_apply, Equiv.ofBijective_apply]
    obtain ⟨k, hk, hout⟩ := exists_mem_KU_out_mk_eq_mul (m a b * (c.out : radQ σ N).1)
    have hlen := len_mat_mul (KU σ (N + 2)).one_mem hk (m a b * (c.out : radQ σ N).1)
    rw [one_mul] at hlen
    rw [hout, isSphericalU_apply_mul_of_mem_KU hφ _ _ hk, hlen,
      hT L ϖ σ q N r hU (by omega) α φ φ₀ hα hφ h1 hφ₀ hφ₀1 a b.out (m a b) (hm a b) _ (c.out : radQ σ N).2]

end GlobalTheory.InertZeta

end

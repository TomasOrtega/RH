import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ChSumSubCMul
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.NormSubOnePowThreeLe

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 GlobalTheory.KZ PowerSeries GlobalTheory.KZ.Cmp

namespace GlobalTheory.KZ.Cmp

/- English proof (translation)
Introduce `l _ m z ψ hz`. Establish `hp : l.Prime` using `Fact.out`. Use `haveI : NeZero (l ^ m) := ⟨pow_ne_zero _ hp.ne_zero⟩`. Take `⟨k, hk⟩ : ∃ k, k = m / 2` from `⟨_, rfl⟩`. Take `⟨s, hs⟩ : ∃ s, s = m - k` from `⟨_, rfl⟩`.

Rewrite using `[← hk]`. Establish `hsm : s ≤ m` using `by omega`. Establish `hmss : m ≤ s + s` using `by omega`. Establish `hmsk : m = s + k` using `by omega`. Use `haveI : NeZero (l ^ s) := ⟨pow_ne_zero _ hp.ne_zero⟩`.

Set `π : ZMod (l ^ m) →+* ZMod (l ^ s)` to `ZMod.castHom (pow_dvd_pow l hsm) (ZMod (l ^ s))`. Establish `hsurj : Function.Surjective π` using `ZMod.castHom_surjective (pow_dvd_pow l hsm)`. Set `q : ZMod (l ^ m)` to `((l ^ s : ℕ) : ZMod (l ^ m))`. Establish `hqq : q * q = 0`. Simplify using `only [q, ← Nat.cast_mul, ← pow_add, ZMod.natCast_eq_zero_iff]`.

Conclude with `pow_dvd_pow l hmss`. Establish `hπq : π q = 0`. Simplify using `only [q]`. Rewrite using `[map_natCast, ZMod.natCast_self]`. Establish `hfib : ∀ x x0 : ZMod (l ^ m), π x = π x0 → ∃ y, x = x0 + q * y`.

Introduce `x x0 h`. Establish `h0 : π (x - x0) = 0` using `by rw [map_sub, h, sub_self]`. Establish `hd : ((x - x0).val : ZMod (l ^ m)) = x - x0` using `ZMod.natCast_zmod_val _`. Rewrite `h0` using `[← hd, map_natCast, ZMod.natCast_eq_zero_iff]`. Take `⟨j, hj⟩` from `h0`.

Use `⟨(j : ZMod (l ^ m)), ?_⟩` and prove the remaining obligations. Rewrite using `[← sub_eq_iff_eq_add', ← hd, hj, Nat.cast_mul]`. Set `e : ZMod (l ^ m) → Qbar l` to `fun x => z ^ x.val`. Establish `he : ∀ a b, e (a + b) = e a * e b`. Introduce `a b`.

Simplify using `only [e, ZMod.val_add, ← pow_add]`. Conclude with `(pow_eq_pow_mod _ hz).symm`. Set `g : ZMod (l ^ m) → Qbar l` to `fun x => ψ x * e x`. Establish `hzn : ‖z‖ = 1`. Establish `h1` using `congrArg norm hz`.

Rewrite `h1` using `[norm_pow, norm_one]`. Conclude with `(pow_eq_one_iff_of_nonneg (norm_nonneg _) (pow_ne_zero _ hp.ne_zero)).1 h1`. Establish `hg1 : ∀ x, ‖g x‖ ≤ 1`. Introduce `x`. Simplify using `only [g, e, norm_mul, norm_pow, hzn, one_pow, mul_one]`.

Conclude with `DirichletCharacter.norm_le_one ψ x`. Establish `hsum : gSum m z ψ = ∑ x, g x`. Unfold `gSum`. Use `symm`. Rewrite using `[← Finset.sum_filter_of_ne (p := IsUnit) (fun x _ hx => by`.

Assume the negation of the conclusion as `h; exact hx (by simp [g, MulChar.map_nonunit ψ h]))]`. Apply the tactic sequence `refine Finset.sum_bij' (fun x hx => (Finset.mem_filter.1 hx).2.unit) (fun b _ => (b : ZMod (l ^ m))) ?_ ?_ ?_ ?_ ?_ <;> simp [g, e]`. Establish `hmove : ∀ x x0 y : ZMod (l ^ m), π x = π x0 → x * q * y = x0 * q * y`. Introduce `x x0 y h`. Take `⟨y', rfl⟩` from `hfib x x0 h`.

Take the linear combination `(y' * y) * hqq`. Establish `h1 : ∀ y : ZMod (l ^ m), (1 - q * y) * (1 + q * y) = 1` using `fun y => by`. Take the linear combination `(-(y * y)) * hqq`. Establish `hinv : ∀ x0 y : ZMod (l ^ m), ∑ x ∈ Finset.univ.filter (fun x => π x = π x0), g x = ψ (1 + q * y) * e (x0 * q * y) * ∑ x ∈ Finset.univ.filter (fun x => π x = π x0), g x`. Introduce `x0 y`.

Rewrite using `[Finset.mul_sum]`. Combine the equalities or inequalities in the displayed calculation. Use `Finset.sum_nbij' (fun x => x * (1 - q * y)) (fun x => x * (1 + q * y)) ?_ ?_ ?_ ?_ ?_` and prove the remaining obligations. Introduce `a ha`. Simplify using `only [Finset.mem_filter, Finset.mem_univ, true_and, map_mul, map_sub, map_one, hπq, zero_mul, sub_zero, mul_one] at ha ⊢`.

Conclude with `ha`. Introduce `a ha`. Simplify using `only [Finset.mem_filter, Finset.mem_univ, true_and, map_mul, map_add, map_one, hπq, zero_mul, add_zero, mul_one] at ha ⊢`. Conclude with `ha`. Introduce `a _`.

Simplify using `only [mul_assoc, h1, mul_one]`. Introduce `a _`. Simplify using `only [mul_assoc, mul_comm (1 + q * y), h1, mul_one]`. Introduce `a _`. Simplify using `only [mul_assoc, h1, mul_one]`.

Use `_ = _ := Finset.sum_congr rfl fun x hx => by`. Establish `hx' : π x = π x0` using `(Finset.mem_filter.1 hx).2`. Use `show ψ (x * (1 + q * y)) * e (x * (1 + q * y)) = ψ (1 + q * y) * e (x0 * q * y) * (ψ x * e x)`. Rewrite using `[map_mul, show x * (1 + q * y) = x + x * q * y by ring, he, hmove x x0 y hx']`. Expand and normalize the polynomial expressions, which then agree.

Establish `H : ∀ u w y' : ZMod (l ^ m), IsUnit u → w = u + q * y' → (∀ y, ψ (1 + q * y) * e (u * q * y) = 1) → g w = g u`. Introduce `u w y' hu hw hχu`. Take `⟨U, rfl⟩` from `hu`. Establish `hUU : (U : ZMod (l ^ m)) * ((U⁻¹ : (ZMod (l ^ m))ˣ) : ZMod (l ^ m)) = 1` using `Units.mul_inv U`. Establish `hw' : w = (U : ZMod (l ^ m)) + U * q * (((U⁻¹ : (ZMod (l ^ m))ˣ) : ZMod (l ^ m)) * y')`.

Rewrite using `[hw]`. Take the linear combination `(-(q * y')) * hUU`. Establish `hw'' : w = (U : ZMod (l ^ m)) * (1 + q * (((U⁻¹ : (ZMod (l ^ m))ˣ) : ZMod (l ^ m)) * y'))`. Rewrite using `[hw']`. Expand and normalize the polynomial expressions, which then agree.

Use `hχu (((U⁻¹ : (ZMod (l ^ m))ˣ) : ZMod (l ^ m)) * y')` as an intermediate fact. Use `show ψ w * e w = ψ U * e U`. Rewrite using `[hw'', map_mul, ← hw'', hw', he]`. Take the linear combination `(ψ U * e U) * this`. Establish `hcard0 : ∀ x0, (Finset.univ.filter (fun x => π x = π x0)).card = (Finset.univ.filter (fun x => π x = 0)).card`.

Introduce `x0`. Use `Finset.card_nbij' (fun x => x - x0) (fun x => x + x0) ?_ ?_ ?_ ?_` and prove the remaining obligations. Introduce `a ha`. Simplify using `only [Finset.coe_filter, Finset.mem_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at ha ⊢`. Rewrite using `[map_sub, ha, sub_self]`.

Introduce `a ha`. Simplify using `only [Finset.coe_filter, Finset.mem_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at ha ⊢`. Rewrite using `[map_add, ha, zero_add]`. Introduce `a _`. Simplify using the standard rewrite rules.

Introduce `a _`. Simplify using the standard rewrite rules. Establish `htot : l ^ m = l ^ s * (Finset.univ.filter (fun x => π x = 0)).card`. Use `Finset.card_eq_sum_card_fiberwise (s := Finset.univ) (t := Finset.univ) (f := π) (fun x _ => Finset.mem_univ _)` as an intermediate fact. Rewrite `this` using `[Finset.card_univ, ZMod.card]`.

Use `this.trans ?_` and prove the remaining obligations. Rewrite using `[Finset.sum_congr rfl (g := fun _ => (Finset.univ.filter (fun x => π x = 0)).card) (fun c _ => by`. Take `⟨x0, rfl⟩` from `hsurj c`. Conclude with `hcard0 x0), Finset.sum_const, Finset.card_univ, ZMod.card, smul_eq_mul]`. Establish `hcardk : (Finset.univ.filter (fun x => π x = 0)).card = l ^ k`.

Establish `h2 : l ^ s * (Finset.univ.filter (fun x => π x = 0)).card = l ^ s * l ^ k`. Rewrite using `[← htot, ← pow_add, ← hmsk]`. Conclude with `Nat.eq_of_mul_eq_mul_left (pow_pos hp.pos s) h2`. Rewrite using `[hsum, ← Finset.sum_fiberwise Finset.univ π g]`. Use `IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (norm_nonneg _) fun c _ => ?_` and prove the remaining obligations.

Take `⟨x0, rfl⟩` from `hsurj c`. Distinguish the cases in `hχ : ∀ y, ψ (1 + q * y) * e (x0 * q * y) = 1`. Establish `hall : ∀ x ∈ Finset.univ.filter (fun x => π x = π x0), g x = g x0`. Introduce `x hx`. Establish `hx' : π x = π x0` using `(Finset.mem_filter.1 hx).2`.

Take `⟨y', hy'⟩` from `hfib x x0 hx'`. Distinguish the cases in `hu0 : IsUnit x0`. Conclude with `H x0 x y' hu0 hy' hχ`. Distinguish the cases in `hu : IsUnit x`. Use `(H x x0 (-y') hu (by rw [hy']; ring) fun y => ?_).symm` and prove the remaining obligations.

Rewrite using `[hmove x x0 y hx']`. Conclude with `hχ y`. Use `show ψ x * e x = ψ x0 * e x0`. Rewrite using `[MulChar.map_nonunit ψ hu, MulChar.map_nonunit ψ hu0, zero_mul, zero_mul]`. Rewrite using `[Finset.sum_congr rfl hall, Finset.sum_const, nsmul_eq_mul, norm_mul, hcard0, hcardk]`.

Use `push_cast`. Combine the equalities or inequalities in the displayed calculation. Use `push_neg at hχ`. Take `⟨y, hy⟩` from `hχ`. Establish `hI` using `hinv x0 y`.

Establish `h0 : ∑ x ∈ Finset.univ.filter (fun x => π x = π x0), g x = 0`. Establish `hm : (1 - ψ (1 + q * y) * e (x0 * q * y)) * ∑ x ∈ Finset.univ.filter (fun x => π x = π x0), g x = 0`. Rewrite using `[sub_mul, one_mul, ← hI, sub_self]`. Conclude with `(mul_eq_zero.1 hm).resolve_left (sub_ne_zero.2 (Ne.symm hy))`. Rewrite using `[h0, norm_zero]`.

Check the signs of the components of the expression.
-/
theorem norm_gSum_le : ∀ (l : ℕ) [Fact l.Prime] (m : ℕ) (z : Qbar l) (ψ : DirichletCharacter (Qbar l) (l ^ m)),
    z ^ (l ^ m) = 1 → ‖gSum m z ψ‖ ≤ ‖(l : Qbar l) ^ (m / 2)‖ := by
  intro l _ m z ψ hz
  have hp : l.Prime := Fact.out
  haveI : NeZero (l ^ m) := ⟨pow_ne_zero _ hp.ne_zero⟩
  obtain ⟨k, hk⟩ : ∃ k, k = m / 2 := ⟨_, rfl⟩
  obtain ⟨s, hs⟩ : ∃ s, s = m - k := ⟨_, rfl⟩
  rw [← hk]
  have hsm : s ≤ m := by omega
  have hmss : m ≤ s + s := by omega
  have hmsk : m = s + k := by omega
  haveI : NeZero (l ^ s) := ⟨pow_ne_zero _ hp.ne_zero⟩
  let π : ZMod (l ^ m) →+* ZMod (l ^ s) := ZMod.castHom (pow_dvd_pow l hsm) (ZMod (l ^ s))
  have hsurj : Function.Surjective π := ZMod.castHom_surjective (pow_dvd_pow l hsm)
  let q : ZMod (l ^ m) := ((l ^ s : ℕ) : ZMod (l ^ m))
  have hqq : q * q = 0 := by
    simp only [q, ← Nat.cast_mul, ← pow_add, ZMod.natCast_eq_zero_iff]
    exact pow_dvd_pow l hmss
  have hπq : π q = 0 := by
    simp only [q]
    rw [map_natCast, ZMod.natCast_self]
  have hfib : ∀ x x0 : ZMod (l ^ m), π x = π x0 → ∃ y, x = x0 + q * y := by
    intro x x0 h
    have h0 : π (x - x0) = 0 := by rw [map_sub, h, sub_self]
    have hd : ((x - x0).val : ZMod (l ^ m)) = x - x0 := ZMod.natCast_zmod_val _
    rw [← hd, map_natCast, ZMod.natCast_eq_zero_iff] at h0
    obtain ⟨j, hj⟩ := h0
    refine ⟨(j : ZMod (l ^ m)), ?_⟩
    rw [← sub_eq_iff_eq_add', ← hd, hj, Nat.cast_mul]
  let e : ZMod (l ^ m) → Qbar l := fun x => z ^ x.val
  have he : ∀ a b, e (a + b) = e a * e b := by
    intro a b
    simp only [e, ZMod.val_add, ← pow_add]
    exact (pow_eq_pow_mod _ hz).symm
  let g : ZMod (l ^ m) → Qbar l := fun x => ψ x * e x
  have hzn : ‖z‖ = 1 := by
    have h1 := congrArg norm hz
    rw [norm_pow, norm_one] at h1
    exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) (pow_ne_zero _ hp.ne_zero)).1 h1
  have hg1 : ∀ x, ‖g x‖ ≤ 1 := by
    intro x
    simp only [g, e, norm_mul, norm_pow, hzn, one_pow, mul_one]
    exact DirichletCharacter.norm_le_one ψ x
  have hsum : gSum m z ψ = ∑ x, g x := by
    unfold gSum
    symm
    rw [← Finset.sum_filter_of_ne (p := IsUnit) (fun x _ hx => by
      by_contra h; exact hx (by simp [g, MulChar.map_nonunit ψ h]))]
    refine Finset.sum_bij' (fun x hx => (Finset.mem_filter.1 hx).2.unit) (fun b _ => (b : ZMod (l ^ m)))
      ?_ ?_ ?_ ?_ ?_ <;> simp [g, e]
  have hmove : ∀ x x0 y : ZMod (l ^ m), π x = π x0 → x * q * y = x0 * q * y := by
    intro x x0 y h
    obtain ⟨y', rfl⟩ := hfib x x0 h
    linear_combination (y' * y) * hqq
  have h1 : ∀ y : ZMod (l ^ m), (1 - q * y) * (1 + q * y) = 1 := fun y => by
    linear_combination (-(y * y)) * hqq
  have hinv : ∀ x0 y : ZMod (l ^ m), ∑ x ∈ Finset.univ.filter (fun x => π x = π x0), g x =
      ψ (1 + q * y) * e (x0 * q * y) * ∑ x ∈ Finset.univ.filter (fun x => π x = π x0), g x := by
    intro x0 y
    rw [Finset.mul_sum]
    calc ∑ x ∈ Finset.univ.filter (fun x => π x = π x0), g x
        = ∑ x ∈ Finset.univ.filter (fun x => π x = π x0), g (x * (1 + q * y)) := by
          refine Finset.sum_nbij' (fun x => x * (1 - q * y)) (fun x => x * (1 + q * y)) ?_ ?_ ?_ ?_ ?_
          · intro a ha
            simp only [Finset.mem_filter, Finset.mem_univ, true_and, map_mul, map_sub, map_one, hπq,
              zero_mul, sub_zero, mul_one] at ha ⊢
            exact ha
          · intro a ha
            simp only [Finset.mem_filter, Finset.mem_univ, true_and, map_mul, map_add, map_one, hπq,
              zero_mul, add_zero, mul_one] at ha ⊢
            exact ha
          · intro a _
            simp only [mul_assoc, h1, mul_one]
          · intro a _
            simp only [mul_assoc, mul_comm (1 + q * y), h1, mul_one]
          · intro a _
            simp only [mul_assoc, h1, mul_one]
      _ = _ := Finset.sum_congr rfl fun x hx => by
          have hx' : π x = π x0 := (Finset.mem_filter.1 hx).2
          show ψ (x * (1 + q * y)) * e (x * (1 + q * y)) = ψ (1 + q * y) * e (x0 * q * y) * (ψ x * e x)
          rw [map_mul, show x * (1 + q * y) = x + x * q * y by ring, he, hmove x x0 y hx']
          ring
  have H : ∀ u w y' : ZMod (l ^ m), IsUnit u → w = u + q * y' →
      (∀ y, ψ (1 + q * y) * e (u * q * y) = 1) → g w = g u := by
    intro u w y' hu hw hχu
    obtain ⟨U, rfl⟩ := hu
    have hUU : (U : ZMod (l ^ m)) * ((U⁻¹ : (ZMod (l ^ m))ˣ) : ZMod (l ^ m)) = 1 := Units.mul_inv U
    have hw' : w = (U : ZMod (l ^ m)) + U * q * (((U⁻¹ : (ZMod (l ^ m))ˣ) : ZMod (l ^ m)) * y') := by
      rw [hw]; linear_combination (-(q * y')) * hUU
    have hw'' : w = (U : ZMod (l ^ m)) * (1 + q * (((U⁻¹ : (ZMod (l ^ m))ˣ) : ZMod (l ^ m)) * y')) := by
      rw [hw']; ring
    have := hχu (((U⁻¹ : (ZMod (l ^ m))ˣ) : ZMod (l ^ m)) * y')
    show ψ w * e w = ψ U * e U
    rw [hw'', map_mul, ← hw'', hw', he]
    linear_combination (ψ U * e U) * this
  have hcard0 : ∀ x0, (Finset.univ.filter (fun x => π x = π x0)).card =
      (Finset.univ.filter (fun x => π x = 0)).card := by
    intro x0
    refine Finset.card_nbij' (fun x => x - x0) (fun x => x + x0) ?_ ?_ ?_ ?_
    · intro a ha
      simp only [Finset.coe_filter, Finset.mem_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at ha ⊢
      rw [map_sub, ha, sub_self]
    · intro a ha
      simp only [Finset.coe_filter, Finset.mem_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at ha ⊢
      rw [map_add, ha, zero_add]
    · intro a _; simp
    · intro a _; simp
  have htot : l ^ m = l ^ s * (Finset.univ.filter (fun x => π x = 0)).card := by
    have := Finset.card_eq_sum_card_fiberwise (s := Finset.univ) (t := Finset.univ) (f := π)
      (fun x _ => Finset.mem_univ _)
    rw [Finset.card_univ, ZMod.card] at this
    refine this.trans ?_
    rw [Finset.sum_congr rfl (g := fun _ => (Finset.univ.filter (fun x => π x = 0)).card) (fun c _ => by
      obtain ⟨x0, rfl⟩ := hsurj c
      exact hcard0 x0), Finset.sum_const, Finset.card_univ, ZMod.card, smul_eq_mul]
  have hcardk : (Finset.univ.filter (fun x => π x = 0)).card = l ^ k := by
    have h2 : l ^ s * (Finset.univ.filter (fun x => π x = 0)).card = l ^ s * l ^ k := by
      rw [← htot, ← pow_add, ← hmsk]
    exact Nat.eq_of_mul_eq_mul_left (pow_pos hp.pos s) h2
  rw [hsum, ← Finset.sum_fiberwise Finset.univ π g]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (norm_nonneg _) fun c _ => ?_
  obtain ⟨x0, rfl⟩ := hsurj c
  by_cases hχ : ∀ y, ψ (1 + q * y) * e (x0 * q * y) = 1
  · have hall : ∀ x ∈ Finset.univ.filter (fun x => π x = π x0), g x = g x0 := by
      intro x hx
      have hx' : π x = π x0 := (Finset.mem_filter.1 hx).2
      obtain ⟨y', hy'⟩ := hfib x x0 hx'
      by_cases hu0 : IsUnit x0
      · exact H x0 x y' hu0 hy' hχ
      by_cases hu : IsUnit x
      · refine (H x x0 (-y') hu (by rw [hy']; ring) fun y => ?_).symm
        rw [hmove x x0 y hx']
        exact hχ y
      · show ψ x * e x = ψ x0 * e x0
        rw [MulChar.map_nonunit ψ hu, MulChar.map_nonunit ψ hu0, zero_mul, zero_mul]
    rw [Finset.sum_congr rfl hall, Finset.sum_const, nsmul_eq_mul, norm_mul, hcard0, hcardk]
    push_cast
    calc ‖(l : Qbar l) ^ k‖ * ‖g x0‖ ≤ ‖(l : Qbar l) ^ k‖ * 1 :=
          mul_le_mul_of_nonneg_left (hg1 x0) (norm_nonneg _)
      _ = _ := mul_one _
  · push_neg at hχ
    obtain ⟨y, hy⟩ := hχ
    have hI := hinv x0 y
    have h0 : ∑ x ∈ Finset.univ.filter (fun x => π x = π x0), g x = 0 := by
      have hm : (1 - ψ (1 + q * y) * e (x0 * q * y)) * ∑ x ∈ Finset.univ.filter (fun x => π x = π x0), g x = 0 := by
        rw [sub_mul, one_mul, ← hI, sub_self]
      exact (mul_eq_zero.1 hm).resolve_left (sub_ne_zero.2 (Ne.symm hy))
    rw [h0, norm_zero]
    positivity

end GlobalTheory.KZ.Cmp

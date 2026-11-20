import Mathlib
import Formalism.DirichletDensity.Statement

open Filter Topology Finset Formalism.Q3

noncomputable section

namespace Formalism.HF.P

/- English proof (translation)
Rewrite using `[← jacobiSym.legendreSym.to_jacobiSym, legendreSym.eq_zero_iff, Int.cast_natCast, ZMod.natCast_eq_zero_iff]`.
-/
theorem hda_jac_zero_iff (p : ℕ) [Fact p.Prime] (m : ℕ) :
    jacobiSym (m : ℤ) p = 0 ↔ p ∣ m := by
  rw [← jacobiSym.legendreSym.to_jacobiSym, legendreSym.eq_zero_iff, Int.cast_natCast,
    ZMod.natCast_eq_zero_iff]

/- English proof (translation)
Rewrite using `[← jacobiSym.legendreSym.to_jacobiSym]`. Unfold `legendreSym`. Rewrite using `[Int.cast_natCast]`.
-/
theorem hda_jac_qc (p : ℕ) [Fact p.Prime] (m : ℕ) :
    jacobiSym (m : ℤ) p = quadraticChar (ZMod p) (m : ZMod p) := by
  rw [← jacobiSym.legendreSym.to_jacobiSym]
  unfold legendreSym
  rw [Int.cast_natCast]

/- English proof (translation)
Establish `hF : ringChar (ZMod p) ≠ 2` using `by rw [ZMod.ringChar_zmod_n]; exact hp`. Establish `key : ∀ y : ZMod p, quadraticChar (ZMod p) y = 0 ∨ quadraticChar (ZMod p) y = 1 ∨ quadraticChar (ZMod p) y = -1`. Introduce `y`. Distinguish the cases in `hy : y = 0`. Use `left`.

Rewrite using `[hy]`. Conclude with `MulChar.map_zero _`. Use `right`. Conclude with `quadraticChar_dichotomy hy`. Establish `hsum : ((univ.filter (fun y : ZMod p => quadraticChar (ZMod p) y = 1)).card : ℤ) - (univ.filter (fun y : ZMod p => quadraticChar (ZMod p) y = -1)).card = 0`.

Establish `h0` using `quadraticChar_sum_zero hF`. Establish `: ∀ y : ZMod p, quadraticChar (ZMod p) y = (if quadraticChar (ZMod p) y = 1 then 1 else 0) - (if quadraticChar (ZMod p) y = -1 then 1 else 0)`. Apply the tactic sequence `intro y; rcases key y with h | h | h <;> simp [h]`. Rewrite `h0` using `[Finset.sum_congr rfl (fun y _ => this y), Finset.sum_sub_distrib]`. Rewrite using `[Finset.card_filter, Finset.card_filter]`.

Use `push_cast`. Conclude with `h0`. Establish `htot : (univ.filter (fun y : ZMod p => quadraticChar (ZMod p) y = 1)).card + (univ.filter (fun y : ZMod p => quadraticChar (ZMod p) y = -1)).card = p - 1`. Establish `: ∀ y : ZMod p, ((if quadraticChar (ZMod p) y = 1 then 1 else 0) + (if quadraticChar (ZMod p) y = -1 then 1 else 0) : ℕ) = (if y ≠ 0 then 1 else 0 : ℕ)`. Introduce `y`.

Distinguish the cases in `hy : y = 0`. Simplify using `[hy]`. Apply the tactic sequence `rcases quadraticChar_dichotomy hy with h | h <;> simp [h, hy]`. Rewrite using `[Finset.card_filter, Finset.card_filter, ← Finset.sum_add_distrib, Finset.sum_congr rfl (fun y _ => this y), ← Finset.card_filter, Finset.filter_ne', Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, ZMod.card]`. Apply the tactic sequence `rcases he with rfl | rfl <;> omega`.
-/
theorem hda_card_qc (p : ℕ) [Fact p.Prime] (hp : p ≠ 2) (e : ℤ) (he : e = 1 ∨ e = -1) :
    2 * (univ.filter (fun y : ZMod p => quadraticChar (ZMod p) y = e)).card = p - 1 := by
  classical
  have hF : ringChar (ZMod p) ≠ 2 := by rw [ZMod.ringChar_zmod_n]; exact hp
  have key : ∀ y : ZMod p, quadraticChar (ZMod p) y = 0 ∨ quadraticChar (ZMod p) y = 1 ∨
      quadraticChar (ZMod p) y = -1 := by
    intro y
    by_cases hy : y = 0
    · left; rw [hy]; exact MulChar.map_zero _
    · right; exact quadraticChar_dichotomy hy
  have hsum : ((univ.filter (fun y : ZMod p => quadraticChar (ZMod p) y = 1)).card : ℤ) -
      (univ.filter (fun y : ZMod p => quadraticChar (ZMod p) y = -1)).card = 0 := by
    have h0 := quadraticChar_sum_zero hF
    have : ∀ y : ZMod p, quadraticChar (ZMod p) y =
        (if quadraticChar (ZMod p) y = 1 then 1 else 0) -
          (if quadraticChar (ZMod p) y = -1 then 1 else 0) := by
      intro y; rcases key y with h | h | h <;> simp [h]
    rw [Finset.sum_congr rfl (fun y _ => this y), Finset.sum_sub_distrib] at h0
    rw [Finset.card_filter, Finset.card_filter]; push_cast; exact h0
  have htot : (univ.filter (fun y : ZMod p => quadraticChar (ZMod p) y = 1)).card +
      (univ.filter (fun y : ZMod p => quadraticChar (ZMod p) y = -1)).card = p - 1 := by
    have : ∀ y : ZMod p, ((if quadraticChar (ZMod p) y = 1 then 1 else 0) +
        (if quadraticChar (ZMod p) y = -1 then 1 else 0) : ℕ) = (if y ≠ 0 then 1 else 0 : ℕ) := by
      intro y
      by_cases hy : y = 0
      · simp [hy]
      · rcases quadraticChar_dichotomy hy with h | h <;> simp [h, hy]
    rw [Finset.card_filter, Finset.card_filter, ← Finset.sum_add_distrib,
      Finset.sum_congr rfl (fun y _ => this y), ← Finset.card_filter, Finset.filter_ne',
      Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, ZMod.card]
  rcases he with rfl | rfl <;> omega

/- English proof (translation)
Take `⟨hp, hinj⟩` from `hq`. Establish `hF : ∀ i, Fact (q i).Prime` using `fun i => ⟨(hp i).1⟩`. Establish `hne2 : ∀ i, q i ≠ 2` using `fun i h => by have := (hp i).2; omega`. Establish `hcop : ∀ i j, i ≠ j → Nat.Coprime (q i) (q j)` using `fun i j h => (Nat.coprime_primes (hp i).1 (hp j).1).mpr (hinj.ne h)`. Use `set N := q 0 * q 1 * q 2 with hN`.

Establish `hNpos : 0 < N` using `Nat.mul_pos (Nat.mul_pos (hp 0).1.pos (hp 1).1.pos) (hp 2).1.pos`. Establish `: NeZero N` using `⟨hNpos.ne'⟩`. Use `set e : Fin 3 → ℤ := fun i => ((g i : ℤˣ) : ℤ) with he_def`. Establish `he : ∀ i, e i = 1 ∨ e i = -1` using `fun i => by`. Apply the tactic sequence `rcases Int.units_eq_one_or (g i) with h | h <;> simp [he_def, h]`.

Establish `hd0 : q 0 ∣ N` using `Dvd.intro (q 1 * q 2) (by rw [hN]; ring)`. Establish `hd1 : q 1 ∣ N` using `Dvd.intro (q 0 * q 2) (by rw [hN]; ring)`. Establish `hd2 : q 2 ∣ N` using `Dvd.intro (q 0 * q 1) (by rw [hN]; ring)`. Establish `hdvd : ∀ i, q i ∣ N`. Introduce `i`.

Use `fin_cases i`. Use `exacts [hd0, hd1, hd2]`. Set `A : Finset (ZMod N)` to `univ.filter (fun a => ∀ i, jacobiSym (a.val : ℤ) (q i) = e i)`. Establish `hval : ∀ (n : ℕ) i, jacobiSym (((n : ZMod N)).val : ℤ) (q i) = jacobiSym (n : ℤ) (q i)`. Introduce `n i`.

Apply `jacobiSym.mod_left'` to reduce the goal to its premises. Rewrite using `[ZMod.val_natCast, Int.natCast_mod, Int.emod_emod_of_dvd _ (Int.natCast_dvd_natCast.mpr (hdvd i))]`. Establish `hmem : ∀ n : ℕ, ((∀ i, n ≠ q i) ∧ ∀ i, chiQ (q i) n = e i) ↔ (n : ZMod N) ∈ A`. Introduce `n`. Simplify using `only [A, Finset.mem_filter, Finset.mem_univ, true_and, hval, chiQ]`.

Prove the components needed by the constructor for the conclusion. Conclude with `fun h => h.2`. Introduce `h`. Use `⟨fun i hni => ?_, h⟩` and prove the remaining obligations. Establish `h0 : jacobiSym (n : ℤ) (q i) = 0` using `(hda_jac_zero_iff (q i) n).mpr (by rw [hni])`.

Rewrite `h0` using `[h i]`. Apply the tactic sequence `rcases he i with h1 | h1 <;> omega`. Establish `hunit : ∀ a ∈ A, IsUnit a`. Introduce `a ha`. Simplify using `only [A, Finset.mem_filter, Finset.mem_univ, true_and] at ha`.

Rewrite using `[← ZMod.natCast_zmod_val a, ZMod.isUnit_iff_coprime]`. Establish `hc : ∀ i, Nat.Coprime a.val (q i)`. Introduce `i`. Rewrite using `[Nat.coprime_comm, Nat.Prime.coprime_iff_not_dvd (hp i).1]`. Introduce `hd`.

Establish `h0` using `(hda_jac_zero_iff (q i) a.val).mpr hd`. Rewrite `h0` using `[ha i]`. Apply the tactic sequence `rcases he i with h1 | h1 <;> omega`. Conclude with `Nat.Coprime.mul_right (Nat.Coprime.mul_right (hc 0) (hc 1)) (hc 2)`. Set `F : ZMod N → ZMod (q 0) × ZMod (q 1) × ZMod (q 2)` to `fun a => ((a.val : ZMod (q 0)), (a.val : ZMod (q 1)), (a.val : ZMod (q 2)))`.

Establish `hFinj : Function.Injective F`. Introduce `a b hab`. Simplify using `only [F, Prod.mk.injEq, ZMod.natCast_eq_natCast_iff] at hab`. Take `⟨h0, h1, h2⟩` from `hab`. Establish `h01 : a.val ≡ b.val [MOD q 0 * q 1]` using `(Nat.modEq_and_modEq_iff_modEq_mul (hcop 0 1 (by decide))).mp ⟨h0, h1⟩`.

Establish `h012 : a.val ≡ b.val [MOD N]` using `(Nat.modEq_and_modEq_iff_modEq_mul (Nat.Coprime.mul_left (hcop 0 2 (by decide)) (hcop 1 2 (by decide)))).mp ⟨h01, h2⟩`. Apply `ZMod.val_injective N` to reduce the goal to its premises. Unfold `Nat.ModEq at h012`. Rewrite `h012` using `[Nat.mod_eq_of_lt (ZMod.val_lt a), Nat.mod_eq_of_lt (ZMod.val_lt b)]`. Then use the resulting hypothesis. Establish `hFbij : Function.Bijective F`.

Rewrite using `[Fintype.bijective_iff_injective_and_card]`. Use `⟨hFinj, ?_⟩` and prove the remaining obligations. Simplify using `only [ZMod.card, Fintype.card_prod, hN, mul_assoc]`. Set `B : ∀ i, Finset (ZMod (q i))` to `fun i => univ.filter (fun y => quadraticChar (ZMod (q i)) y = e i)`. Establish `hcardA : A.card = (B 0).card * (B 1).card * (B 2).card`.

Establish `hmap : A.map ⟨F, hFinj⟩ = B 0 ×ˢ (B 1 ×ˢ B 2)`. Use extensionality with `⟨y0, y1, y2⟩`. Simplify using `only [Finset.mem_map, Finset.mem_product, A, B, Finset.mem_filter, Finset.mem_univ, true_and, Function.Embedding.coeFn_mk]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨a, ha, hFa⟩`.

Simplify using `only [F, Prod.mk.injEq] at hFa`. Take `⟨r0, r1, r2⟩` from `hFa`. Use `⟨?_, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[← r0, ← hda_jac_qc]`. Conclude with `ha 0`.

Rewrite using `[← r1, ← hda_jac_qc]`. Conclude with `ha 1`. Rewrite using `[← r2, ← hda_jac_qc]`. Conclude with `ha 2`. Introduce and unpack `⟨h0, h1, h2⟩`.

Take `⟨a, ha⟩` from `hFbij.2 (y0, y1, y2)`. Use `⟨a, ?_, ha⟩` and prove the remaining obligations. Simplify using `only [F, Prod.mk.injEq] at ha`. Take `⟨r0, r1, r2⟩` from `ha`. Introduce `i`.

Use `fin_cases i`. Use `show jacobiSym (a.val : ℤ) (q 0) = e 0`. Rewrite using `[hda_jac_qc, r0]`. Conclude with `h0`. Use `show jacobiSym (a.val : ℤ) (q 1) = e 1`.

Rewrite using `[hda_jac_qc, r1]`. Conclude with `h1`. Use `show jacobiSym (a.val : ℤ) (q 2) = e 2`. Rewrite using `[hda_jac_qc, r2]`. Conclude with `h2`.

Rewrite using `[← Finset.card_map ⟨F, hFinj⟩, hmap, Finset.card_product, Finset.card_product, mul_assoc]`. Establish `hB : ∀ i, 2 * (B i).card = q i - 1` using `fun i => hda_card_qc (q i) (hne2 i) (e i) (he i)`. Establish `htot : N.totient = (q 0 - 1) * (q 1 - 1) * (q 2 - 1)`. Rewrite using `[hN, Nat.totient_mul (Nat.Coprime.mul_left (hcop 0 2 (by decide)) (hcop 1 2 (by decide))), Nat.totient_mul (hcop 0 1 (by decide)), Nat.totient_prime (hp 0).1, Nat.totient_prime (hp 1).1, Nat.totient_prime (hp 2).1]`. Establish `h8 : 8 * A.card = N.totient`.

Rewrite using `[hcardA, htot, ← hB 0, ← hB 1, ← hB 2]`. Expand and normalize the polynomial expressions, which then agree. Establish `hphi : (0 : ℝ) < N.totient` using `Nat.cast_pos.mpr (Nat.totient_pos.mpr hNpos)`. Establish `hsumconst : ∑ a ∈ A, (1 / (N.totient : ℝ)) = 1 / 8`. Rewrite using `[Finset.sum_const, nsmul_eq_mul]`.

Establish `h8r : (8 : ℝ) * A.card = N.totient` using `by exact_mod_cast h8`. Establish `hA0 : (A.card : ℝ) ≠ 0` using `by intro h0; rw [h0] at h8r; linarith`. Rewrite using `[← h8r]`. Clear the denominators using the available nonvanishing facts. Establish `hS : ∀ a ∈ A, LogDensity {p : ℕ | (p : ZMod N) = a} (1 / (N.totient : ℝ))` using `fun a ha => hAP N a (hunit a ha)`.

Establish `hind : ∀ (f : ℕ → ℝ) (n : ℕ), {p : ℕ | p.Prime ∧ p ∈ {p : ℕ | (∀ i, p ≠ q i) ∧ ∀ i, chiQ (q i) p = e i}}.indicator f n = ∑ a ∈ A, {p : ℕ | p.Prime ∧ p ∈ {p : ℕ | (p : ZMod N) = a}}.indicator f n`. Introduce `f n`. Distinguish the cases in `hn : n.Prime`. Distinguish the cases in `hT : (∀ i, n ≠ q i) ∧ ∀ i, chiQ (q i) n = e i`. Establish `ha : (n : ZMod N) ∈ A` using `(hmem n).1 hT`.

Rewrite using `[Set.indicator_of_mem (show n ∈ {p : ℕ | p.Prime ∧ p ∈ {p : ℕ | (∀ i, p ≠ q i) ∧ ∀ i, chiQ (q i) p = e i}} from ⟨hn, hT⟩), Finset.sum_eq_single_of_mem (n : ZMod N) ha]`. Rewrite using `[Set.indicator_of_mem (show n ∈ {p : ℕ | p.Prime ∧ p ∈ {p : ℕ | (p : ZMod N) = (n : ZMod N)}} from ⟨hn, rfl⟩)]`. Introduce `b _ hb`. Conclude with `Set.indicator_of_notMem (fun h => hb h.2.symm) _`. Rewrite using `[Set.indicator_of_notMem (fun h => hT h.2), Finset.sum_eq_zero]`.

Introduce `b hb`. Apply `Set.indicator_of_notMem` to reduce the goal to its premises. Introduce and unpack `⟨_, h⟩`. Establish `h' : (n : ZMod N) = b` using `h`. Conclude with `hT ((hmem n).2 (h' ▸ hb))`.

Rewrite using `[Set.indicator_of_notMem (fun h => hn h.1), Finset.sum_eq_zero]`. Introduce `b _`. Conclude with `Set.indicator_of_notMem (fun h => hn h.1) _`. Establish `hsumm : ∀ᶠ x in 𝓝[>] (1 : ℝ), ∀ a ∈ A, Summable ({p : ℕ | p.Prime ∧ p ∈ {p : ℕ | (p : ZMod N) = a}}.indicator (fun m : ℕ => Real.log m / (m : ℝ) ^ x))`. Rewrite using `[Filter.eventually_all_finset]`.

Introduce `a ha`. Establish `hpos : (0 : ℝ) < 1 / (N.totient : ℝ)` using `by positivity`. Use `filter_upwards [(hS a ha).eventually (lt_mem_nhds hpos)] with x hx`. Assume the negation of the conclusion as `hns`. Rewrite `hx` using `[tsum_eq_zero_of_not_summable hns, mul_zero]`.

Conclude with `lt_irrefl _ hx`. Establish `heq : (fun x : ℝ => ∑ a ∈ A, (x - 1) * (∑' n : ℕ, {p : ℕ | p.Prime ∧ p ∈ {p : ℕ | (p : ZMod N) = a}}.indicator (fun m : ℕ => Real.log m / (m : ℝ) ^ x) n)) =ᶠ[𝓝[>] (1 : ℝ)] (fun x : ℝ => (x - 1) * (∑' n : ℕ, {p : ℕ | p.Prime ∧ p ∈ {p : ℕ | (∀ i, p ≠ q i) ∧ ∀ i, chiQ (q i) p = e i} …` using `by filter_upwards [hsumm] with x hx`. Rewrite using `[← Finset.mul_sum, ← Summable.tsum_finsetSum hx]`. Use `congr 1`. Conclude with `tsum_congr (fun n => (hind _ n).symm)`.

Establish `hlim` using `tendsto_finsetSum A (fun a ha => hS a ha)`. Rewrite `hlim` using `[hsumconst]`. Conclude with `hlim.congr' heq`.
-/
theorem hda_log (hAP : APLogDensity) (q : Fin 3 → ℕ) (hq : Hyp3 q) (g : Gal3) :
    LogDensity {p : ℕ | (∀ i, p ≠ q i) ∧ ∀ i, chiQ (q i) p = ((g i : ℤˣ) : ℤ)} (1 / 8) := by
  classical
  obtain ⟨hp, hinj⟩ := hq
  have hF : ∀ i, Fact (q i).Prime := fun i => ⟨(hp i).1⟩
  have hne2 : ∀ i, q i ≠ 2 := fun i h => by have := (hp i).2; omega
  have hcop : ∀ i j, i ≠ j → Nat.Coprime (q i) (q j) := fun i j h =>
    (Nat.coprime_primes (hp i).1 (hp j).1).mpr (hinj.ne h)
  set N := q 0 * q 1 * q 2 with hN
  have hNpos : 0 < N := Nat.mul_pos (Nat.mul_pos (hp 0).1.pos (hp 1).1.pos) (hp 2).1.pos
  have : NeZero N := ⟨hNpos.ne'⟩
  set e : Fin 3 → ℤ := fun i => ((g i : ℤˣ) : ℤ) with he_def
  have he : ∀ i, e i = 1 ∨ e i = -1 := fun i => by
    rcases Int.units_eq_one_or (g i) with h | h <;> simp [he_def, h]
  have hd0 : q 0 ∣ N := Dvd.intro (q 1 * q 2) (by rw [hN]; ring)
  have hd1 : q 1 ∣ N := Dvd.intro (q 0 * q 2) (by rw [hN]; ring)
  have hd2 : q 2 ∣ N := Dvd.intro (q 0 * q 1) (by rw [hN]; ring)
  have hdvd : ∀ i, q i ∣ N := by
    intro i; fin_cases i
    exacts [hd0, hd1, hd2]

  let A : Finset (ZMod N) := univ.filter (fun a => ∀ i, jacobiSym (a.val : ℤ) (q i) = e i)
  have hval : ∀ (n : ℕ) i, jacobiSym (((n : ZMod N)).val : ℤ) (q i) = jacobiSym (n : ℤ) (q i) := by
    intro n i
    apply jacobiSym.mod_left'
    rw [ZMod.val_natCast, Int.natCast_mod, Int.emod_emod_of_dvd _ (Int.natCast_dvd_natCast.mpr (hdvd i))]
  have hmem : ∀ n : ℕ, ((∀ i, n ≠ q i) ∧ ∀ i, chiQ (q i) n = e i) ↔ (n : ZMod N) ∈ A := by
    intro n
    simp only [A, Finset.mem_filter, Finset.mem_univ, true_and, hval, chiQ]
    constructor
    · exact fun h => h.2
    · intro h
      refine ⟨fun i hni => ?_, h⟩
      have h0 : jacobiSym (n : ℤ) (q i) = 0 := (hda_jac_zero_iff (q i) n).mpr (by rw [hni])
      rw [h i] at h0
      rcases he i with h1 | h1 <;> omega
  have hunit : ∀ a ∈ A, IsUnit a := by
    intro a ha
    simp only [A, Finset.mem_filter, Finset.mem_univ, true_and] at ha
    rw [← ZMod.natCast_zmod_val a, ZMod.isUnit_iff_coprime]
    have hc : ∀ i, Nat.Coprime a.val (q i) := by
      intro i
      rw [Nat.coprime_comm, Nat.Prime.coprime_iff_not_dvd (hp i).1]
      intro hd
      have h0 := (hda_jac_zero_iff (q i) a.val).mpr hd
      rw [ha i] at h0
      rcases he i with h1 | h1 <;> omega
    exact Nat.Coprime.mul_right (Nat.Coprime.mul_right (hc 0) (hc 1)) (hc 2)

  let F : ZMod N → ZMod (q 0) × ZMod (q 1) × ZMod (q 2) := fun a =>
    ((a.val : ZMod (q 0)), (a.val : ZMod (q 1)), (a.val : ZMod (q 2)))
  have hFinj : Function.Injective F := by
    intro a b hab
    simp only [F, Prod.mk.injEq, ZMod.natCast_eq_natCast_iff] at hab
    obtain ⟨h0, h1, h2⟩ := hab
    have h01 : a.val ≡ b.val [MOD q 0 * q 1] :=
      (Nat.modEq_and_modEq_iff_modEq_mul (hcop 0 1 (by decide))).mp ⟨h0, h1⟩
    have h012 : a.val ≡ b.val [MOD N] :=
      (Nat.modEq_and_modEq_iff_modEq_mul
        (Nat.Coprime.mul_left (hcop 0 2 (by decide)) (hcop 1 2 (by decide)))).mp ⟨h01, h2⟩
    apply ZMod.val_injective N
    unfold Nat.ModEq at h012
    rwa [Nat.mod_eq_of_lt (ZMod.val_lt a), Nat.mod_eq_of_lt (ZMod.val_lt b)] at h012
  have hFbij : Function.Bijective F := by
    rw [Fintype.bijective_iff_injective_and_card]
    refine ⟨hFinj, ?_⟩
    simp only [ZMod.card, Fintype.card_prod, hN, mul_assoc]
  let B : ∀ i, Finset (ZMod (q i)) := fun i => univ.filter (fun y => quadraticChar (ZMod (q i)) y = e i)
  have hcardA : A.card = (B 0).card * (B 1).card * (B 2).card := by
    have hmap : A.map ⟨F, hFinj⟩ = B 0 ×ˢ (B 1 ×ˢ B 2) := by
      ext ⟨y0, y1, y2⟩
      simp only [Finset.mem_map, Finset.mem_product, A, B, Finset.mem_filter, Finset.mem_univ,
        true_and, Function.Embedding.coeFn_mk]
      constructor
      · rintro ⟨a, ha, hFa⟩
        simp only [F, Prod.mk.injEq] at hFa
        obtain ⟨r0, r1, r2⟩ := hFa
        refine ⟨?_, ?_, ?_⟩
        · rw [← r0, ← hda_jac_qc]; exact ha 0
        · rw [← r1, ← hda_jac_qc]; exact ha 1
        · rw [← r2, ← hda_jac_qc]; exact ha 2
      · rintro ⟨h0, h1, h2⟩
        obtain ⟨a, ha⟩ := hFbij.2 (y0, y1, y2)
        refine ⟨a, ?_, ha⟩
        simp only [F, Prod.mk.injEq] at ha
        obtain ⟨r0, r1, r2⟩ := ha
        intro i; fin_cases i
        · show jacobiSym (a.val : ℤ) (q 0) = e 0
          rw [hda_jac_qc, r0]; exact h0
        · show jacobiSym (a.val : ℤ) (q 1) = e 1
          rw [hda_jac_qc, r1]; exact h1
        · show jacobiSym (a.val : ℤ) (q 2) = e 2
          rw [hda_jac_qc, r2]; exact h2
    rw [← Finset.card_map ⟨F, hFinj⟩, hmap, Finset.card_product, Finset.card_product, mul_assoc]
  have hB : ∀ i, 2 * (B i).card = q i - 1 := fun i => hda_card_qc (q i) (hne2 i) (e i) (he i)
  have htot : N.totient = (q 0 - 1) * (q 1 - 1) * (q 2 - 1) := by
    rw [hN, Nat.totient_mul (Nat.Coprime.mul_left (hcop 0 2 (by decide)) (hcop 1 2 (by decide))),
      Nat.totient_mul (hcop 0 1 (by decide)), Nat.totient_prime (hp 0).1,
      Nat.totient_prime (hp 1).1, Nat.totient_prime (hp 2).1]
  have h8 : 8 * A.card = N.totient := by
    rw [hcardA, htot, ← hB 0, ← hB 1, ← hB 2]; ring
  have hphi : (0 : ℝ) < N.totient := Nat.cast_pos.mpr (Nat.totient_pos.mpr hNpos)
  have hsumconst : ∑ a ∈ A, (1 / (N.totient : ℝ)) = 1 / 8 := by
    rw [Finset.sum_const, nsmul_eq_mul]
    have h8r : (8 : ℝ) * A.card = N.totient := by exact_mod_cast h8
    have hA0 : (A.card : ℝ) ≠ 0 := by intro h0; rw [h0] at h8r; linarith
    rw [← h8r]; field_simp

  have hS : ∀ a ∈ A, LogDensity {p : ℕ | (p : ZMod N) = a} (1 / (N.totient : ℝ)) :=
    fun a ha => hAP N a (hunit a ha)
  have hind : ∀ (f : ℕ → ℝ) (n : ℕ),
      {p : ℕ | p.Prime ∧ p ∈ {p : ℕ | (∀ i, p ≠ q i) ∧ ∀ i, chiQ (q i) p = e i}}.indicator f n =
        ∑ a ∈ A, {p : ℕ | p.Prime ∧ p ∈ {p : ℕ | (p : ZMod N) = a}}.indicator f n := by
    intro f n
    by_cases hn : n.Prime
    · by_cases hT : (∀ i, n ≠ q i) ∧ ∀ i, chiQ (q i) n = e i
      · have ha : (n : ZMod N) ∈ A := (hmem n).1 hT
        rw [Set.indicator_of_mem (show n ∈ {p : ℕ | p.Prime ∧ p ∈ {p : ℕ | (∀ i, p ≠ q i) ∧
          ∀ i, chiQ (q i) p = e i}} from ⟨hn, hT⟩), Finset.sum_eq_single_of_mem (n : ZMod N) ha]
        · rw [Set.indicator_of_mem (show n ∈ {p : ℕ | p.Prime ∧ p ∈ {p : ℕ | (p : ZMod N) = (n : ZMod N)}}
            from ⟨hn, rfl⟩)]
        · intro b _ hb
          exact Set.indicator_of_notMem (fun h => hb h.2.symm) _
      · rw [Set.indicator_of_notMem (fun h => hT h.2), Finset.sum_eq_zero]
        intro b hb
        apply Set.indicator_of_notMem
        rintro ⟨_, h⟩
        have h' : (n : ZMod N) = b := h
        exact hT ((hmem n).2 (h' ▸ hb))
    · rw [Set.indicator_of_notMem (fun h => hn h.1), Finset.sum_eq_zero]
      intro b _
      exact Set.indicator_of_notMem (fun h => hn h.1) _
  have hsumm : ∀ᶠ x in 𝓝[>] (1 : ℝ), ∀ a ∈ A,
      Summable ({p : ℕ | p.Prime ∧ p ∈ {p : ℕ | (p : ZMod N) = a}}.indicator
        (fun m : ℕ => Real.log m / (m : ℝ) ^ x)) := by
    rw [Filter.eventually_all_finset]
    intro a ha
    have hpos : (0 : ℝ) < 1 / (N.totient : ℝ) := by positivity
    filter_upwards [(hS a ha).eventually (lt_mem_nhds hpos)] with x hx
    by_contra hns
    rw [tsum_eq_zero_of_not_summable hns, mul_zero] at hx
    exact lt_irrefl _ hx
  have heq : (fun x : ℝ => ∑ a ∈ A, (x - 1) * (∑' n : ℕ,
      {p : ℕ | p.Prime ∧ p ∈ {p : ℕ | (p : ZMod N) = a}}.indicator
        (fun m : ℕ => Real.log m / (m : ℝ) ^ x) n)) =ᶠ[𝓝[>] (1 : ℝ)]
      (fun x : ℝ => (x - 1) * (∑' n : ℕ,
        {p : ℕ | p.Prime ∧ p ∈ {p : ℕ | (∀ i, p ≠ q i) ∧ ∀ i, chiQ (q i) p = e i}}.indicator
          (fun m : ℕ => Real.log m / (m : ℝ) ^ x) n)) := by
    filter_upwards [hsumm] with x hx
    rw [← Finset.mul_sum, ← Summable.tsum_finsetSum hx]
    congr 1
    exact tsum_congr (fun n => (hind _ n).symm)
  have hlim := tendsto_finsetSum A (fun a ha => hS a ha)
  rw [hsumconst] at hlim
  exact hlim.congr' heq

end Formalism.HF.P

namespace Formalism.HF

/- English proof (translation)
Introduce `q hq g`. Establish `h` using `Formalism.HF.P.hda_log hAP q hq g`. Conclude with `⟨h, hLD _ _ h⟩`.
-/
theorem hostDensityArith_of (hAP : Formalism.HF.APLogDensity) (hLD : Formalism.HF.LogToDir) :
    Formalism.HF.HostDensityArith := by
  intro q hq g
  have h := Formalism.HF.P.hda_log hAP q hq g
  exact ⟨h, hLD _ _ h⟩

end Formalism.HF

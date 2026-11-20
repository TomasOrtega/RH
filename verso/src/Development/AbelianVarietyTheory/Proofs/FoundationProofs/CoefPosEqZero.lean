import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PrimitiveCharDoubleSumPrimePowEvalStatement

open GlobalTheory.KummerEisensteinGalois Finset
open scoped Classical

namespace GlobalTheory.KummerEisensteinGalois.UnitPiece

variable {K : Type} [Field K] [CharZero K]

omit [CharZero K] in

/- English proof (translation)
Rewrite using `[Int.divisorsAntidiag_natCast, sum_disjUnion, sum_map, sum_map, ← sum_add_distrib]`. Conclude with `Nat.sum_divisorsAntidiagonal' (fun a b : ℕ => G a b + G (-(a : ℤ)) (-(b : ℤ)))`.
-/
theorem sum_antidiag (n : ℕ) (G : ℤ → ℤ → K) :
    ∑ q ∈ (n : ℤ).divisorsAntidiag, G q.1 q.2 =
      ∑ d ∈ n.divisors, (G ((n / d : ℕ) : ℤ) d + G (-((n / d : ℕ) : ℤ)) (-(d : ℤ))) := by
  rw [Int.divisorsAntidiag_natCast, sum_disjUnion, sum_map, sum_map, ← sum_add_distrib]
  exact Nat.sum_divisorsAntidiagonal' (fun a b : ℕ => G a b + G (-(a : ℤ)) (-(b : ℤ)))

/- English proof (translation)
Rewrite using `[sum_antidiag n (fun A d => if A ≡ a₁ [ZMOD M] then (d.sign : K) * ((A : K) / M) ^ (j - 1) * ζ ^ (a₂ * d) else 0)]`. Unfold `coefPos`. Use `sum_congr rfl fun d hd => ?_` and prove the remaining obligations. Establish `hd0 : (0 : ℤ) < d` using `by exact_mod_cast Nat.pos_of_mem_divisors hd`. Rewrite using `[Int.sign_neg, Int.sign_eq_one_of_pos hd0, sub_eq_add_neg]`.

Use `congr 1`. Apply the tactic sequence `split_ifs <;> simp [-Nat.cast_div_charZero, -Int.natCast_div, -Int.natCast_ediv]`. Apply the tactic sequence `split_ifs <;> simp [neg_div, -Nat.cast_div_charZero, -Int.natCast_div, -Int.natCast_ediv]`.
-/
theorem coefPos_eq (j M : ℕ) (ζ : K) (a₁ a₂ : ℤ) (n : ℕ) :
    coefPos j M ζ a₁ a₂ n = ∑ q ∈ (n : ℤ).divisorsAntidiag,
      if q.1 ≡ a₁ [ZMOD M] then (q.2.sign : K) * ((q.1 : K) / M) ^ (j - 1) * ζ ^ (a₂ * q.2) else 0 := by
  rw [sum_antidiag n (fun A d => if A ≡ a₁ [ZMOD M] then (d.sign : K) * ((A : K) / M) ^ (j - 1) * ζ ^ (a₂ * d) else 0)]
  unfold coefPos
  refine sum_congr rfl fun d hd => ?_
  have hd0 : (0 : ℤ) < d := by exact_mod_cast Nat.pos_of_mem_divisors hd
  rw [Int.sign_neg, Int.sign_eq_one_of_pos hd0, sub_eq_add_neg]
  congr 1
  · split_ifs <;> simp [-Nat.cast_div_charZero, -Int.natCast_div, -Int.natCast_ediv]
  · split_ifs <;> simp [neg_div, -Nat.cast_div_charZero, -Int.natCast_div, -Int.natCast_ediv]

/- English proof (translation)
Rewrite using `[sum_antidiag n (fun A d => if ¬ (p : ℤ) ∣ A ∧ ¬ (p : ℤ) ∣ d then (d.sign : K) * (ψ (A : ZMod (p ^ m)) * (A : K) ^ (k - 2) * (ζ ^ (p ^ m)) ^ (x * t * d)) else 0)]`. Unfold `ffPos`. Use `sum_congr rfl fun d hd => ?_` and prove the remaining obligations. Establish `hd0 : (0 : ℤ) < d` using `by exact_mod_cast Nat.pos_of_mem_divisors hd`. Rewrite using `[Int.sign_neg, Int.sign_eq_one_of_pos hd0]`.

Simplify using `only [dvd_neg, Int.natCast_dvd_natCast, Int.cast_neg, Int.cast_natCast, Int.cast_one, mul_neg]`. Apply the tactic sequence `by_cases h1 : p ∣ d <;> by_cases h2 : p ∣ n / d <;> simp [h1, h2, sub_eq_add_neg]`.
-/
theorem ffPos_eq (N p m k : ℕ) (ψ : DirichletCharacter K (p ^ m)) (x t : ℤ) (ζ : K) (n : ℕ) :
    ffPos N p m k ψ x t ζ false n = ∑ q ∈ (n : ℤ).divisorsAntidiag,
      if ¬ (p : ℤ) ∣ q.1 ∧ ¬ (p : ℤ) ∣ q.2 then
        (q.2.sign : K) * (ψ (q.1 : ZMod (p ^ m)) * (q.1 : K) ^ (k - 2) * (ζ ^ (p ^ m)) ^ (x * t * q.2)) else 0 := by
  rw [sum_antidiag n (fun A d => if ¬ (p : ℤ) ∣ A ∧ ¬ (p : ℤ) ∣ d then
        (d.sign : K) * (ψ (A : ZMod (p ^ m)) * (A : K) ^ (k - 2) * (ζ ^ (p ^ m)) ^ (x * t * d)) else 0)]
  unfold ffPos
  refine sum_congr rfl fun d hd => ?_
  have hd0 : (0 : ℤ) < d := by exact_mod_cast Nat.pos_of_mem_divisors hd
  rw [Int.sign_neg, Int.sign_eq_one_of_pos hd0]
  simp only [dvd_neg, Int.natCast_dvd_natCast, Int.cast_neg, Int.cast_natCast, Int.cast_one, mul_neg]
  by_cases h1 : p ∣ d <;> by_cases h2 : p ∣ n / d <;> simp [h1, h2, sub_eq_add_neg]

/- English proof (translation)
Rewrite using `[sum_antidiag n (fun A d => if ¬ (p : ℤ) ∣ A ∧ ¬ (p : ℤ) ∣ d then (d.sign : K) * (ψ⁻¹ (d : ZMod (p ^ m)) * (ζ ^ (p ^ m)) ^ (t * d)) else 0)]`. Unfold `eePos`. Use `sum_congr rfl fun d hd => ?_` and prove the remaining obligations. Establish `hd0 : (0 : ℤ) < d` using `by exact_mod_cast Nat.pos_of_mem_divisors hd`. Rewrite using `[Int.sign_neg, Int.sign_eq_one_of_pos hd0]`.

Simplify using `only [dvd_neg, Int.natCast_dvd_natCast, Int.cast_neg, Int.cast_natCast, Int.cast_one, mul_neg]`. Apply the tactic sequence `by_cases h1 : p ∣ d <;> by_cases h2 : p ∣ n / d <;> simp [h1, h2, sub_eq_add_neg]`.
-/
theorem eePos_eq (N p m : ℕ) (ψ : DirichletCharacter K (p ^ m)) (t : ℤ) (ζ : K) (n : ℕ) :
    eePos N p m ψ t ζ false n = ∑ q ∈ (n : ℤ).divisorsAntidiag,
      if ¬ (p : ℤ) ∣ q.1 ∧ ¬ (p : ℤ) ∣ q.2 then
        (q.2.sign : K) * (ψ⁻¹ (q.2 : ZMod (p ^ m)) * (ζ ^ (p ^ m)) ^ (t * q.2)) else 0 := by
  rw [sum_antidiag n (fun A d => if ¬ (p : ℤ) ∣ A ∧ ¬ (p : ℤ) ∣ d then
        (d.sign : K) * (ψ⁻¹ (d : ZMod (p ^ m)) * (ζ ^ (p ^ m)) ^ (t * d)) else 0)]
  unfold eePos
  refine sum_congr rfl fun d hd => ?_
  have hd0 : (0 : ℤ) < d := by exact_mod_cast Nat.pos_of_mem_divisors hd
  rw [Int.sign_neg, Int.sign_eq_one_of_pos hd0]
  simp only [dvd_neg, Int.natCast_dvd_natCast, Int.cast_neg, Int.cast_natCast, Int.cast_one, mul_neg]
  by_cases h1 : p ∣ d <;> by_cases h2 : p ∣ n / d <;> simp [h1, h2, sub_eq_add_neg]

def primeTo (p m : ℕ) [NeZero p] : Finset (ZMod (p ^ m)) := univ.filter fun c => ¬ p ∣ c.val

omit [CharZero K] in

/- English proof (translation)
Establish `e : ∑ u ∈ primeTo p m, ∑ a : ZMod (p ^ m), ∑ v ∈ primeTo p m, ∑ b : ZMod (p ^ m), ψ (u * b - a * v) * H u a v b = ∑ w ∈ primeTo p m ×ˢ ((univ : Finset (ZMod (p ^ m))) ×ˢ (primeTo p m ×ˢ (univ : Finset (ZMod (p ^ m))))), ψ (w.1 * w.2.2.2 - w.2.1 * w.2.2.1) * H w.1 w.2.1 w.2.2.1 w. …`. Simplify using `only [sum_product]`. Rewrite using `[e]`. Use `sum_of_injOn (fun γ : GL (Fin 2) (ZMod (p ^ m)) => ((γ : Matrix (Fin 2) (Fin 2) (ZMod (p ^ m))) 0 0, (γ : Matrix (Fin 2) (Fin 2) (ZMod (p ^ m))) 0 1, (γ : Matrix (Fin 2) (Fin 2) (ZMod (p ^ m))) 1 0, (γ : Matrix (Fin 2) (Fin 2) (ZMod (p ^ m))) 1 1)) ?_ ?_ ?_ ?_` and prove the remaining obligations. Introduce `γ _ δ _ h`.

Simplify using `only [Prod.mk.injEq] at h`. Use extensionality with `i j`. Apply the tactic sequence `fin_cases i <;> fin_cases j <;> simp [h]`. Introduce `γ hγ`. Simplify `hγ` using `[unitSet, primeTo]`.

Introduce and unpack `⟨u, a, v, b⟩ hw hn`. Distinguish the cases in `hu : IsUnit (u * b - a * v)`. It suffices to derive a contradiction. Apply `hn` to reduce the goal to its premises. Use `⟨Matrix.GeneralLinearGroup.mk'' !![u, a; v, b] (by simpa [Matrix.det_fin_two] using hu), ?_, ?_⟩` and prove the remaining obligations.

Simplify `hw` using `[unitSet, primeTo]`. Simplify using the standard rewrite rules. Simplify using `only`. Rewrite using `[MulChar.map_nonunit _ hu, zero_mul]`. Introduce `γ _`.

Simplify using `only [ZMod.natCast_zmod_val, Matrix.det_fin_two]`.
-/
theorem sum_unitSet (p m : ℕ) [NeZero p] (ψ : DirichletCharacter K (p ^ m))
    (H : ZMod (p ^ m) → ZMod (p ^ m) → ZMod (p ^ m) → ZMod (p ^ m) → K) :
    ∑ γ ∈ unitSet p m, ψ (((γ : Matrix (Fin 2) (Fin 2) (ZMod (p ^ m))).det.val : ℕ) : ZMod (p ^ m)) *
      H ((γ : Matrix (Fin 2) (Fin 2) (ZMod (p ^ m))) 0 0) ((γ : Matrix (Fin 2) (Fin 2) (ZMod (p ^ m))) 0 1)
        ((γ : Matrix (Fin 2) (Fin 2) (ZMod (p ^ m))) 1 0) ((γ : Matrix (Fin 2) (Fin 2) (ZMod (p ^ m))) 1 1) =
    ∑ u ∈ primeTo p m, ∑ a : ZMod (p ^ m), ∑ v ∈ primeTo p m, ∑ b : ZMod (p ^ m),
      ψ (u * b - a * v) * H u a v b := by
  have e : ∑ u ∈ primeTo p m, ∑ a : ZMod (p ^ m), ∑ v ∈ primeTo p m, ∑ b : ZMod (p ^ m),
      ψ (u * b - a * v) * H u a v b =
      ∑ w ∈ primeTo p m ×ˢ ((univ : Finset (ZMod (p ^ m))) ×ˢ (primeTo p m ×ˢ (univ : Finset (ZMod (p ^ m))))),
        ψ (w.1 * w.2.2.2 - w.2.1 * w.2.2.1) * H w.1 w.2.1 w.2.2.1 w.2.2.2 := by
    simp only [sum_product]
  rw [e]
  refine sum_of_injOn (fun γ : GL (Fin 2) (ZMod (p ^ m)) =>
    ((γ : Matrix (Fin 2) (Fin 2) (ZMod (p ^ m))) 0 0, (γ : Matrix (Fin 2) (Fin 2) (ZMod (p ^ m))) 0 1,
     (γ : Matrix (Fin 2) (Fin 2) (ZMod (p ^ m))) 1 0, (γ : Matrix (Fin 2) (Fin 2) (ZMod (p ^ m))) 1 1)) ?_ ?_ ?_ ?_
  · intro γ _ δ _ h
    simp only [Prod.mk.injEq] at h
    ext i j
    fin_cases i <;> fin_cases j <;> simp [h]
  · intro γ hγ
    simpa [unitSet, primeTo] using hγ
  · rintro ⟨u, a, v, b⟩ hw hn
    by_cases hu : IsUnit (u * b - a * v)
    · exfalso
      apply hn
      refine ⟨Matrix.GeneralLinearGroup.mk'' !![u, a; v, b] (by simpa [Matrix.det_fin_two] using hu), ?_, ?_⟩
      · simpa [unitSet, primeTo] using hw
      · simp
    · simp only
      rw [MulChar.map_nonunit _ hu, zero_mul]
  · intro γ _
    simp only [ZMod.natCast_zmod_val, Matrix.det_fin_two]

/- English proof (translation)
Rewrite using `[← Int.natCast_dvd_natCast, ZMod.val_intCast]`. Establish `h : (p : ℤ) ∣ ((p ^ m : ℕ) : ℤ)` using `by push_cast; exact dvd_pow_self _ (by omega)`. Rewrite using `[Int.emod_def]`. Conclude with `dvd_sub_left (h.mul_right _)`.
-/
theorem dvd_val_iff (p m : ℕ) [NeZero p] (hm : 1 ≤ m) (z : ℤ) :
    p ∣ (z : ZMod (p ^ m)).val ↔ (p : ℤ) ∣ z := by
  rw [← Int.natCast_dvd_natCast, ZMod.val_intCast]
  have h : (p : ℤ) ∣ ((p ^ m : ℕ) : ℤ) := by push_cast; exact dvd_pow_self _ (by omega)
  rw [Int.emod_def]
  exact dvd_sub_left (h.mul_right _)

/- English proof (translation)
Establish `hN' : (N : ℤ) ≠ 0` using `by exact_mod_cast hN.ne'`. Establish `hNK : (N : K) ≠ 0` using `by exact_mod_cast hN.ne'`. Establish `e : ∀ u : ZMod (p ^ m), ∑ a : ZMod (p ^ m), Φ u a * coefPos j (N * p ^ m) ζ (N * u.val) (s a) (N * n) = ∑ q ∈ ((N * n : ℕ) : ℤ).divisorsAntidiag, if q.1 ≡ N * u.val [ZMOD (N * p ^ m : ℕ)] then (q.2.sign : K) * ((q.1 : K) / (N * p ^ m : ℕ)) ^ (j - 1) * ∑ a : ZMod (p ^ m), Φ u a * …`. Introduce `u`. Repeatedly rewrite using `[coefPos_eq, mul_sum]`.

Rewrite using `[sum_comm]`. Use `sum_congr rfl fun q _ => ?_` and prove the remaining obligations. Use `split_ifs`. Conclude with `sum_congr rfl fun a _ => by ring`. Simplify using the standard rewrite rules.

Rewrite using `[sum_congr rfl fun u _ => e u, ← sum_product', ← sum_filter, ← sum_filter]`. Use `symm`. Use `sum_bij (fun q _ => ((q.1 : ZMod (p ^ m)), ((N : ℤ) * q.1, q.2))) ?_ ?_ ?_ ?_` and prove the remaining obligations. Introduce `q hq`. Take `⟨hq, hp⟩` from `mem_filter.mp hq`.

Take `⟨h1, h2⟩` from `Int.mem_divisorsAntidiag.mp hq`. Use `mem_filter.mpr ⟨mem_product.mpr ⟨?_, Int.mem_divisorsAntidiag.mpr ⟨?_, ?_⟩⟩, ?_⟩` and prove the remaining obligations. Simplify `hp` using `[primeTo, dvd_val_iff p m hm]`. Use `push_cast`. Rewrite using `[← h1]`.

Expand and normalize the polynomial expressions, which then agree. Use `push_cast`. Conclude with `mul_ne_zero hN' h2`. Simplify using `only [ZMod.val_intCast]`. Rewrite using `[Nat.cast_mul]`.

Conclude with `(Int.mod_modEq _ _).symm.mul_left'`. Introduce `q _ q' _ h`. Simplify using `only [Prod.mk.injEq] at h`. Conclude with `Prod.ext (mul_left_cancel₀ hN' h.2.1) h.2.2`. Introduce and unpack `⟨u, A, d⟩ hw`.

Take `⟨hw, hA⟩` from `mem_filter.mp hw`. Take `⟨hu, hq⟩` from `mem_product.mp hw`. Take `⟨h1, h2⟩` from `Int.mem_divisorsAntidiag.mp hq`. Simplify using `only at h1 hA hu`. Take `⟨c, hc⟩` from `hA.dvd`.

Establish `hA' : A = N * (u.val - (p ^ m : ℕ) * c)` using `by push_cast at hc ⊢; linear_combination -hc`. Establish `hcast : (((u.val : ℤ) - (p ^ m : ℕ) * c : ℤ) : ZMod (p ^ m)) = u`. Rewrite using `[Int.cast_sub, Int.cast_mul, Int.cast_natCast, Int.cast_natCast, ZMod.natCast_self, ZMod.natCast_zmod_val]`. Expand and normalize the polynomial expressions, which then agree. Use `⟨((u.val : ℤ) - (p ^ m : ℕ) * c, d), mem_filter.mpr ⟨Int.mem_divisorsAntidiag.mpr ⟨?_, ?_⟩, ?_⟩, ?_⟩` and prove the remaining obligations.

Apply `mul_left_cancel₀ hN'` to reduce the goal to its premises. Rewrite using `[← mul_assoc, ← hA', h1]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Introduce `h`.

Apply `h2` to reduce the goal to its premises. Use `push_cast`. Rewrite using `[h, mul_zero]`. Rewrite using `[← dvd_val_iff p m hm, hcast]`. Conclude with `(mem_filter.mp hu).2`.

Simplify using `only [hcast, ← hA']`. Introduce `q _`. Simplify using `only`. Use `congr 3`. Use `push_cast`.

Clear the denominators using the available nonvanishing facts.
-/
theorem row_sum (p m N j : ℕ) [NeZero p] (hm : 1 ≤ m) (hN : 0 < N) (ζ : K) (s : ZMod (p ^ m) → ℤ)
    (Φ : ZMod (p ^ m) → ZMod (p ^ m) → K) (n : ℕ) :
    ∑ u ∈ primeTo p m, ∑ a : ZMod (p ^ m), Φ u a * coefPos j (N * p ^ m) ζ (N * u.val) (s a) (N * n) =
    ∑ q ∈ (n : ℤ).divisorsAntidiag, if ¬ (p : ℤ) ∣ q.1 then
      (q.2.sign : K) * ((q.1 : K) / (p : K) ^ m) ^ (j - 1) *
        ∑ a : ZMod (p ^ m), Φ (q.1 : ZMod (p ^ m)) a * ζ ^ (s a * q.2) else 0 := by
  have hN' : (N : ℤ) ≠ 0 := by exact_mod_cast hN.ne'
  have hNK : (N : K) ≠ 0 := by exact_mod_cast hN.ne'
  have e : ∀ u : ZMod (p ^ m),
      ∑ a : ZMod (p ^ m), Φ u a * coefPos j (N * p ^ m) ζ (N * u.val) (s a) (N * n) =
      ∑ q ∈ ((N * n : ℕ) : ℤ).divisorsAntidiag, if q.1 ≡ N * u.val [ZMOD (N * p ^ m : ℕ)] then
        (q.2.sign : K) * ((q.1 : K) / (N * p ^ m : ℕ)) ^ (j - 1) *
          ∑ a : ZMod (p ^ m), Φ u a * ζ ^ (s a * q.2) else 0 := by
    intro u
    simp_rw [coefPos_eq, mul_sum]
    rw [sum_comm]
    refine sum_congr rfl fun q _ => ?_
    split_ifs
    · exact sum_congr rfl fun a _ => by ring
    · simp
  rw [sum_congr rfl fun u _ => e u, ← sum_product', ← sum_filter, ← sum_filter]
  symm
  refine sum_bij (fun q _ => ((q.1 : ZMod (p ^ m)), ((N : ℤ) * q.1, q.2))) ?_ ?_ ?_ ?_
  · intro q hq
    obtain ⟨hq, hp⟩ := mem_filter.mp hq
    obtain ⟨h1, h2⟩ := Int.mem_divisorsAntidiag.mp hq
    refine mem_filter.mpr ⟨mem_product.mpr ⟨?_, Int.mem_divisorsAntidiag.mpr ⟨?_, ?_⟩⟩, ?_⟩
    · simpa [primeTo, dvd_val_iff p m hm] using hp
    · push_cast; rw [← h1]; ring
    · push_cast; exact mul_ne_zero hN' h2
    · simp only [ZMod.val_intCast]
      rw [Nat.cast_mul]
      exact (Int.mod_modEq _ _).symm.mul_left'
  · intro q _ q' _ h
    simp only [Prod.mk.injEq] at h
    exact Prod.ext (mul_left_cancel₀ hN' h.2.1) h.2.2
  · rintro ⟨u, A, d⟩ hw
    obtain ⟨hw, hA⟩ := mem_filter.mp hw
    obtain ⟨hu, hq⟩ := mem_product.mp hw
    obtain ⟨h1, h2⟩ := Int.mem_divisorsAntidiag.mp hq
    simp only at h1 hA hu
    obtain ⟨c, hc⟩ := hA.dvd
    have hA' : A = N * (u.val - (p ^ m : ℕ) * c) := by push_cast at hc ⊢; linear_combination -hc
    have hcast : (((u.val : ℤ) - (p ^ m : ℕ) * c : ℤ) : ZMod (p ^ m)) = u := by
      rw [Int.cast_sub, Int.cast_mul, Int.cast_natCast, Int.cast_natCast, ZMod.natCast_self, ZMod.natCast_zmod_val]; ring
    refine ⟨((u.val : ℤ) - (p ^ m : ℕ) * c, d), mem_filter.mpr ⟨Int.mem_divisorsAntidiag.mpr ⟨?_, ?_⟩, ?_⟩, ?_⟩
    · apply mul_left_cancel₀ hN'
      rw [← mul_assoc, ← hA', h1]; push_cast; ring
    · intro h; apply h2; push_cast; rw [h, mul_zero]
    · rw [← dvd_val_iff p m hm, hcast]
      exact (mem_filter.mp hu).2
    · simp only [hcast, ← hA']
  · intro q _
    simp only
    congr 3
    push_cast
    field_simp

/- English proof (translation)
Establish `hp : p.Prime` using `Fact.out`. Establish `hpZ : Prime (p : ℤ)` using `Nat.prime_iff_prime_int.mp hp`. Establish `hpos : 0 < N * p ^ m` using `Nat.mul_pos hN (pow_pos hp.pos m)`. Establish `hζ0 : ζ ≠ 0` using `hζ.ne_zero hpos.ne'`. Establish `hζN : IsPrimitiveRoot (ζ ^ N) (p ^ m)` using `hζ.pow hpos rfl`.

Establish `hpm : (p : ℤ) ∣ (p : ℤ) ^ m` using `dvd_pow_self _ (by omega)`. Establish `hunit : ∀ z : ℤ, IsUnit (z : ZMod (p ^ m)) ↔ ¬ (p : ℤ) ∣ z`. Introduce `z`. Rewrite using `[← dvd_val_iff p m hm, ← ZMod.natCast_zmod_val (z : ZMod (p ^ m)), ZMod.isUnit_iff_coprime, Nat.coprime_pow_right_iff (by omega), Nat.coprime_comm, hp.coprime_iff_not_dvd, ZMod.natCast_zmod_val]`. Establish `hdvd : ∀ z : ℤ, (p : ℤ) ^ m ∣ z ↔ (z : ZMod (p ^ m)) = 0`.

Introduce `z`. Rewrite using `[ZMod.intCast_zmod_eq_zero_iff_dvd]`. Use `push_cast`. Both sides reduce to the same expression. Take `⟨c1, c2⟩` from `GlobalTheory.T.primitiveChar_doubleSum_primePow_eval p m K ψ (ζ ^ N) hm hψ hζN n₁ n₂ d d' (fun h => h₁ h.1)`.

Establish `e : ∑ a : ZMod (p ^ m), (∑ b : ZMod (p ^ m), ψ ((n₁ : ZMod (p ^ m)) * b - a * (n₂ : ZMod (p ^ m))) * ζ ^ (((N : ℤ) * b.val + (p : ℤ) ^ m * y₂) * d')) * ζ ^ (((N : ℤ) * a.val + (p : ℤ) ^ m * y₁) * d) = (∑ a : ZMod (p ^ m), ∑ b : ZMod (p ^ m), ψ ((n₁ : ZMod (p ^ m)) * b - (n₂ : ZMo …`. Simplify using `only [sum_mul]`. Use `sum_congr rfl fun a _ => sum_congr rfl fun b _ => ?_` and prove the remaining obligations. Rewrite using `[mul_comm a, mul_assoc, mul_assoc, ← zpow_natCast ζ N, ← zpow_natCast ζ (p ^ m), ← zpow_mul, ← zpow_mul, ← zpow_mul, ← zpow_add₀ hζ0, ← zpow_add₀ hζ0, ← zpow_add₀ hζ0]`. Use `congr 2`.

Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e]`. Take `⟨w, hw⟩` from `(hunit n₁).mpr h₁`. Use `split_ifs with hc`.

Take `⟨hs, -, hd'⟩` from `hc`. Take `⟨v, hv⟩` from `(hunit d').mpr hd'`. Rewrite `hs` using `[hdvd]`. Move the coercions through the operations in `at hs`. Rewrite `hs` using `[← hw, ← hv]`.

Establish `hww : ((w⁻¹ : (ZMod (p ^ m))ˣ) : ZMod (p ^ m)) * w = 1` using `w.inv_mul`. Rewrite using `[c1 (v * w⁻¹) ?_ ?_]`. Establish `: ψ⁻¹ ((v * w⁻¹ : (ZMod (p ^ m))ˣ) : ZMod (p ^ m)) = ψ (n₁ : ZMod (p ^ m)) * ψ⁻¹ (d' : ZMod (p ^ m))`. Rewrite using `[Units.val_mul, map_mul, ← hw, ← hv, mul_comm]`. Use `congr 1`.

Rewrite using `[MulChar.inv_apply, Ring.inverse_unit, inv_inv]`. Rewrite using `[this]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[Units.val_mul]`. Take the linear combination `((w⁻¹ : (ZMod (p ^ m))ˣ) : ZMod (p ^ m)) * hs - (d : ZMod (p ^ m)) * hww`.

Rewrite using `[Units.val_mul, ← hw, ← hv]`. Take the linear combination `(-(v : ZMod (p ^ m))) * hww`. Rewrite using `[c2, zero_mul]`. Introduce and unpack `⟨u, hd, hd'⟩`. Apply `hc` to reduce the goal to its premises.

Use `⟨?_, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[hdvd]`. Use `push_cast`. Rewrite using `[hd, hd']`. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[← hunit, hd]`. Conclude with `u.isUnit.mul ((hunit n₂).mpr h₂).neg`. Rewrite using `[← hunit, hd']`. Conclude with `u.isUnit.mul ((hunit n₁).mpr h₁)`.
-/
theorem col_sum (p m N : ℕ) [Fact p.Prime] (hm : 1 ≤ m) (hN : 0 < N) (ψ : DirichletCharacter K (p ^ m))
    (hψ : ψ.IsPrimitive) (ζ : K) (hζ : IsPrimitiveRoot ζ (N * p ^ m)) (y₁ y₂ n₁ n₂ d d' : ℤ)
    (h₁ : ¬ (p : ℤ) ∣ n₁) (h₂ : ¬ (p : ℤ) ∣ n₂) :
    ∑ a : ZMod (p ^ m), (∑ b : ZMod (p ^ m), ψ ((n₁ : ZMod (p ^ m)) * b - a * (n₂ : ZMod (p ^ m))) *
        ζ ^ (((N : ℤ) * b.val + (p : ℤ) ^ m * y₂) * d')) * ζ ^ (((N : ℤ) * a.val + (p : ℤ) ^ m * y₁) * d) =
      if (p : ℤ) ^ m ∣ n₁ * d + n₂ * d' ∧ ¬ (p : ℤ) ∣ d ∧ ¬ (p : ℤ) ∣ d' then
        (p : K) ^ m * gaussS p m ψ (ζ ^ N) * (ψ (n₁ : ZMod (p ^ m)) * (ζ ^ (p ^ m)) ^ (y₁ * d)) *
          (ψ⁻¹ (d' : ZMod (p ^ m)) * (ζ ^ (p ^ m)) ^ (y₂ * d')) else 0 := by
  have hp : p.Prime := Fact.out
  have hpZ : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
  have hpos : 0 < N * p ^ m := Nat.mul_pos hN (pow_pos hp.pos m)
  have hζ0 : ζ ≠ 0 := hζ.ne_zero hpos.ne'
  have hζN : IsPrimitiveRoot (ζ ^ N) (p ^ m) := hζ.pow hpos rfl
  have hpm : (p : ℤ) ∣ (p : ℤ) ^ m := dvd_pow_self _ (by omega)
  have hunit : ∀ z : ℤ, IsUnit (z : ZMod (p ^ m)) ↔ ¬ (p : ℤ) ∣ z := by
    intro z
    rw [← dvd_val_iff p m hm, ← ZMod.natCast_zmod_val (z : ZMod (p ^ m)), ZMod.isUnit_iff_coprime,
      Nat.coprime_pow_right_iff (by omega), Nat.coprime_comm, hp.coprime_iff_not_dvd, ZMod.natCast_zmod_val]
  have hdvd : ∀ z : ℤ, (p : ℤ) ^ m ∣ z ↔ (z : ZMod (p ^ m)) = 0 := by
    intro z; rw [ZMod.intCast_zmod_eq_zero_iff_dvd]; push_cast; rfl
  obtain ⟨c1, c2⟩ := GlobalTheory.T.primitiveChar_doubleSum_primePow_eval p m K ψ (ζ ^ N) hm hψ hζN n₁ n₂ d d' (fun h => h₁ h.1)
  have e : ∑ a : ZMod (p ^ m), (∑ b : ZMod (p ^ m), ψ ((n₁ : ZMod (p ^ m)) * b - a * (n₂ : ZMod (p ^ m))) *
        ζ ^ (((N : ℤ) * b.val + (p : ℤ) ^ m * y₂) * d')) * ζ ^ (((N : ℤ) * a.val + (p : ℤ) ^ m * y₁) * d) =
      (∑ a : ZMod (p ^ m), ∑ b : ZMod (p ^ m), ψ ((n₁ : ZMod (p ^ m)) * b - (n₂ : ZMod (p ^ m)) * a) *
        (ζ ^ N) ^ ((a.val : ℤ) * d + (b.val : ℤ) * d')) *
        ((ζ ^ (p ^ m)) ^ (y₁ * d) * (ζ ^ (p ^ m)) ^ (y₂ * d')) := by
    simp only [sum_mul]
    refine sum_congr rfl fun a _ => sum_congr rfl fun b _ => ?_
    rw [mul_comm a, mul_assoc, mul_assoc, ← zpow_natCast ζ N, ← zpow_natCast ζ (p ^ m), ← zpow_mul, ← zpow_mul,
      ← zpow_mul, ← zpow_add₀ hζ0, ← zpow_add₀ hζ0, ← zpow_add₀ hζ0]
    congr 2
    push_cast; ring
  rw [e]
  obtain ⟨w, hw⟩ := (hunit n₁).mpr h₁
  split_ifs with hc
  · obtain ⟨hs, -, hd'⟩ := hc
    obtain ⟨v, hv⟩ := (hunit d').mpr hd'
    rw [hdvd] at hs
    push_cast at hs
    rw [← hw, ← hv] at hs
    have hww : ((w⁻¹ : (ZMod (p ^ m))ˣ) : ZMod (p ^ m)) * w = 1 := w.inv_mul
    rw [c1 (v * w⁻¹) ?_ ?_]
    · have : ψ⁻¹ ((v * w⁻¹ : (ZMod (p ^ m))ˣ) : ZMod (p ^ m)) = ψ (n₁ : ZMod (p ^ m)) * ψ⁻¹ (d' : ZMod (p ^ m)) := by
        rw [Units.val_mul, map_mul, ← hw, ← hv, mul_comm]
        congr 1
        rw [MulChar.inv_apply, Ring.inverse_unit, inv_inv]
      rw [this]; ring
    · rw [Units.val_mul]
      linear_combination ((w⁻¹ : (ZMod (p ^ m))ˣ) : ZMod (p ^ m)) * hs - (d : ZMod (p ^ m)) * hww
    · rw [Units.val_mul, ← hw, ← hv]
      linear_combination (-(v : ZMod (p ^ m))) * hww
  · rw [c2, zero_mul]
    rintro ⟨u, hd, hd'⟩
    apply hc
    refine ⟨?_, ?_, ?_⟩
    · rw [hdvd]; push_cast; rw [hd, hd']; ring
    · rw [← hunit, hd]; exact u.isUnit.mul ((hunit n₂).mpr h₂).neg
    · rw [← hunit, hd']; exact u.isUnit.mul ((hunit n₁).mpr h₁)

/- English proof (translation)
Establish `e1 : ∀ u a : ZMod (p ^ m), ∑ v ∈ primeTo p m, ∑ b : ZMod (p ^ m), ψ (u * b - a * v) * (coefPos (k - 1) (N * p ^ m) ζ (N * u.val) (N * a.val + (p : ℤ) ^ m * (x * t)) (N * i) * coefPos 1 (N * p ^ m) ζ (N * v.val) (N * b.val + (p : ℤ) ^ m * t) (N * j)) = (∑ q ∈ (j : ℤ).divisorsAntid …`. Introduce `u a`. Use `row_sum p m N 1 hm hN ζ (fun b => (N : ℤ) * b.val + (p : ℤ) ^ m * t) (fun v b => ψ (u * b - a * v)) j` as an intermediate fact. Simplify using `only [Nat.sub_self, pow_zero, mul_one] at this`. Rewrite using `[← this]`.

Simplify using `only [sum_mul]`. Conclude with `sum_congr rfl fun v _ => sum_congr rfl fun b _ => by ring`. Simplify using `only [e1]`. Rewrite using `[row_sum p m N (k - 1) hm hN ζ (fun a => (N : ℤ) * a.val + (p : ℤ) ^ m * (x * t)) (fun u a => ∑ q ∈ (j : ℤ).divisorsAntidiag, if ¬ (p : ℤ) ∣ q.1 then (q.2.sign : K) * ∑ b : ZMod (p ^ m), ψ (u * b - a * (q.1 : ZMod (p ^ m))) * ζ ^ (((N : ℤ) * b.val + (p : ℤ) ^ m * t) * q.2) else 0 …`. Establish `e2 : ∀ (c : Prop) [Decidable c] (C : K) (A B : ℤ × ℤ → K), (if c then C * ((∑ q ∈ (i : ℤ).divisorsAntidiag, A q) * ∑ q ∈ (j : ℤ).divisorsAntidiag, B q) else 0) = ∑ q ∈ (i : ℤ).divisorsAntidiag, ∑ q' ∈ (j : ℤ).divisorsAntidiag, if c then C * (A q * B q') else 0`.

Introduce `c _ C A B`. Use `split_ifs`. Rewrite using `[sum_mul_sum]`. Simplify using `only [mul_sum]`. Simplify using the standard rewrite rules.

Rewrite using `[ffPos_eq, eePos_eq, e2]`. Use `sum_congr rfl fun q hq => ?_` and prove the remaining obligations. Distinguish the cases in `h₁ : (p : ℤ) ∣ q.1`. Simplify using `[h₁]`. Rewrite using `[if_pos h₁]`.

Simplify using `only [sum_mul (j : ℤ).divisorsAntidiag]`. Rewrite using `[sum_comm, mul_sum]`. Use `sum_congr rfl fun q' hq' => ?_` and prove the remaining obligations. Distinguish the cases in `h₂ : (p : ℤ) ∣ q'.1`. Simplify using `[h₂]`.

Simplify using `only [if_pos h₂, mul_assoc (q'.2.sign : K)]`. Rewrite using `[← mul_sum, col_sum p m N hm hN ψ hψ ζ hζ (x * t) t q.1 q'.1 q.2 q'.2 h₁ h₂, (Int.mem_divisorsAntidiag.mp hq).1, (Int.mem_divisorsAntidiag.mp hq').1]`. Establish `hc : (p : ℤ) ^ m ∣ (i : ℤ) + j ↔ p ^ m ∣ i + j` using `by norm_cast`. Simplify using `only [hc]`. Rewrite using `[show k - 1 - 1 = k - 2 from rfl, div_pow, div_eq_mul_inv]`.

Apply the tactic sequence `by_cases a1 : p ^ m ∣ i + j <;> by_cases a2 : (p : ℤ) ∣ q.2 <;> by_cases a3 : (p : ℤ) ∣ q'.2 <;>`. Simplify using `only [a1, a2, a3, h₁, h₂, not_true, not_false_iff, and_true, and_false, and_self, if_true, if_false, mul_zero, zero_mul, false_and]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem entry_sum (p m N k : ℕ) [Fact p.Prime] (hm : 1 ≤ m) (hN : 0 < N) (ψ : DirichletCharacter K (p ^ m))
    (hψ : ψ.IsPrimitive) (ζ : K) (hζ : IsPrimitiveRoot ζ (N * p ^ m)) (x t : ℤ) (i j : ℕ) :
    ∑ u ∈ primeTo p m, ∑ a : ZMod (p ^ m), ∑ v ∈ primeTo p m, ∑ b : ZMod (p ^ m), ψ (u * b - a * v) *
      (coefPos (k - 1) (N * p ^ m) ζ (N * u.val) (N * a.val + (p : ℤ) ^ m * (x * t)) (N * i) *
        coefPos 1 (N * p ^ m) ζ (N * v.val) (N * b.val + (p : ℤ) ^ m * t) (N * j)) =
    if p ^ m ∣ i + j then (p : K) ^ m * gaussS p m ψ (ζ ^ N) * (((p : K) ^ m) ^ (k - 2))⁻¹ *
      (ffPos N p m k ψ x t ζ false i * eePos N p m ψ t ζ false j) else 0 := by
  have e1 : ∀ u a : ZMod (p ^ m), ∑ v ∈ primeTo p m, ∑ b : ZMod (p ^ m), ψ (u * b - a * v) *
      (coefPos (k - 1) (N * p ^ m) ζ (N * u.val) (N * a.val + (p : ℤ) ^ m * (x * t)) (N * i) *
        coefPos 1 (N * p ^ m) ζ (N * v.val) (N * b.val + (p : ℤ) ^ m * t) (N * j)) =
      (∑ q ∈ (j : ℤ).divisorsAntidiag, if ¬ (p : ℤ) ∣ q.1 then (q.2.sign : K) *
        ∑ b : ZMod (p ^ m), ψ (u * b - a * (q.1 : ZMod (p ^ m))) *
          ζ ^ (((N : ℤ) * b.val + (p : ℤ) ^ m * t) * q.2) else 0) *
      coefPos (k - 1) (N * p ^ m) ζ (N * u.val) (N * a.val + (p : ℤ) ^ m * (x * t)) (N * i) := by
    intro u a
    have := row_sum p m N 1 hm hN ζ (fun b => (N : ℤ) * b.val + (p : ℤ) ^ m * t) (fun v b => ψ (u * b - a * v)) j
    simp only [Nat.sub_self, pow_zero, mul_one] at this
    rw [← this]
    simp only [sum_mul]
    exact sum_congr rfl fun v _ => sum_congr rfl fun b _ => by ring
  simp only [e1]
  rw [row_sum p m N (k - 1) hm hN ζ (fun a => (N : ℤ) * a.val + (p : ℤ) ^ m * (x * t))
    (fun u a => ∑ q ∈ (j : ℤ).divisorsAntidiag, if ¬ (p : ℤ) ∣ q.1 then (q.2.sign : K) *
        ∑ b : ZMod (p ^ m), ψ (u * b - a * (q.1 : ZMod (p ^ m))) *
          ζ ^ (((N : ℤ) * b.val + (p : ℤ) ^ m * t) * q.2) else 0) i]
  have e2 : ∀ (c : Prop) [Decidable c] (C : K) (A B : ℤ × ℤ → K),
      (if c then C * ((∑ q ∈ (i : ℤ).divisorsAntidiag, A q) * ∑ q ∈ (j : ℤ).divisorsAntidiag, B q) else 0) =
      ∑ q ∈ (i : ℤ).divisorsAntidiag, ∑ q' ∈ (j : ℤ).divisorsAntidiag, if c then C * (A q * B q') else 0 := by
    intro c _ C A B
    split_ifs
    · rw [sum_mul_sum]; simp only [mul_sum]
    · simp
  rw [ffPos_eq, eePos_eq, e2]
  refine sum_congr rfl fun q hq => ?_
  by_cases h₁ : (p : ℤ) ∣ q.1
  · simp [h₁]
  rw [if_pos h₁]
  simp only [sum_mul (j : ℤ).divisorsAntidiag]
  rw [sum_comm, mul_sum]
  refine sum_congr rfl fun q' hq' => ?_
  by_cases h₂ : (p : ℤ) ∣ q'.1
  · simp [h₂]
  simp only [if_pos h₂, mul_assoc (q'.2.sign : K)]
  rw [← mul_sum, col_sum p m N hm hN ψ hψ ζ hζ (x * t) t q.1 q'.1 q.2 q'.2 h₁ h₂,
    (Int.mem_divisorsAntidiag.mp hq).1, (Int.mem_divisorsAntidiag.mp hq').1]
  have hc : (p : ℤ) ^ m ∣ (i : ℤ) + j ↔ p ^ m ∣ i + j := by norm_cast
  simp only [hc]
  rw [show k - 1 - 1 = k - 2 from rfl, div_pow, div_eq_mul_inv]
  by_cases a1 : p ^ m ∣ i + j <;> by_cases a2 : (p : ℤ) ∣ q.2 <;> by_cases a3 : (p : ℤ) ∣ q'.2 <;>
    simp only [a1, a2, a3, h₁, h₂, not_true, not_false_iff, and_true, and_false, and_self, if_true, if_false,
      mul_zero, zero_mul, false_and]
  ring

omit [CharZero K] in

/- English proof (translation)
Establish `hp : p.Prime` using `Fact.out`. Establish `hne : ψ ≠ 1`. Introduce `h`. Rewrite `hψ` using `[DirichletCharacter.isPrimitive_def, h, DirichletCharacter.conductor_one]`. Conclude with `(Nat.one_lt_pow (by omega) hp.one_lt).ne hψ`.

Take `⟨w, rfl⟩` from `hu`. Rewrite using `[← MulChar.sum_eq_zero_of_ne_one hne]`. Conclude with `Equiv.sum_comp ((Units.mulLeft w).trans (Equiv.addRight c)) ψ`.
-/
theorem sum_affine (p m : ℕ) [Fact p.Prime] (hm : 1 ≤ m) (ψ : DirichletCharacter K (p ^ m))
    (hψ : ψ.IsPrimitive) (u c : ZMod (p ^ m)) (hu : IsUnit u) : ∑ b : ZMod (p ^ m), ψ (u * b + c) = 0 := by
  have hp : p.Prime := Fact.out
  have hne : ψ ≠ 1 := by
    intro h
    rw [DirichletCharacter.isPrimitive_def, h, DirichletCharacter.conductor_one] at hψ
    exact (Nat.one_lt_pow (by omega) hp.one_lt).ne hψ
  obtain ⟨w, rfl⟩ := hu
  rw [← MulChar.sum_eq_zero_of_ne_one hne]
  exact Equiv.sum_comp ((Units.mulLeft w).trans (Equiv.addRight c)) ψ

/- English proof (translation)
Establish `hp : p.Prime` using `Fact.out`. Rewrite using `[← ZMod.natCast_zmod_val u, ZMod.isUnit_iff_coprime]`. Conclude with `((hp.coprime_iff_not_dvd.mpr (mem_filter.mp hu).2).symm).pow_right m`.
-/
theorem isUnit_of_mem (p m : ℕ) [Fact p.Prime] {u : ZMod (p ^ m)} (hu : u ∈ primeTo p m) : IsUnit u := by
  have hp : p.Prime := Fact.out
  rw [← ZMod.natCast_zmod_val u, ZMod.isUnit_iff_coprime]
  exact ((hp.coprime_iff_not_dvd.mpr (mem_filter.mp hu).2).symm).pow_right m

omit [CharZero K] in

/- English proof (translation)
Use `sum_eq_zero fun u _ => ?_` and prove the remaining obligations. Rewrite using `[sum_comm]`. Use `sum_eq_zero fun v hv => ?_` and prove the remaining obligations. Rewrite using `[sum_comm]`. Use `sum_eq_zero fun b _ => ?_` and prove the remaining obligations.

Rewrite using `[← sum_mul, ← zero_mul (f u * g v b), ← sum_affine p m hm ψ hψ (-v) (u * b) (isUnit_of_mem p m hv).neg]`. Use `congr 1`. Conclude with `sum_congr rfl fun a _ => by congr 1; ring`.
-/
theorem sum_zero_left (p m : ℕ) [Fact p.Prime] (hm : 1 ≤ m) (ψ : DirichletCharacter K (p ^ m))
    (hψ : ψ.IsPrimitive) (f : ZMod (p ^ m) → K) (g : ZMod (p ^ m) → ZMod (p ^ m) → K) :
    ∑ u ∈ primeTo p m, ∑ a : ZMod (p ^ m), ∑ v ∈ primeTo p m, ∑ b : ZMod (p ^ m),
      ψ (u * b - a * v) * (f u * g v b) = 0 := by
  refine sum_eq_zero fun u _ => ?_
  rw [sum_comm]
  refine sum_eq_zero fun v hv => ?_
  rw [sum_comm]
  refine sum_eq_zero fun b _ => ?_
  rw [← sum_mul, ← zero_mul (f u * g v b), ← sum_affine p m hm ψ hψ (-v) (u * b) (isUnit_of_mem p m hv).neg]
  congr 1
  exact sum_congr rfl fun a _ => by congr 1; ring

omit [CharZero K] in

/- English proof (translation)
Use `sum_eq_zero fun u hu => sum_eq_zero fun a _ => sum_eq_zero fun v _ => ?_` and prove the remaining obligations. Rewrite using `[← sum_mul, ← zero_mul (f u a * g v), ← sum_affine p m hm ψ hψ u (-(a * v)) (isUnit_of_mem p m hu)]`. Simplify using `only [sub_eq_add_neg]`.
-/
theorem sum_zero_right (p m : ℕ) [Fact p.Prime] (hm : 1 ≤ m) (ψ : DirichletCharacter K (p ^ m))
    (hψ : ψ.IsPrimitive) (f : ZMod (p ^ m) → ZMod (p ^ m) → K) (g : ZMod (p ^ m) → K) :
    ∑ u ∈ primeTo p m, ∑ a : ZMod (p ^ m), ∑ v ∈ primeTo p m, ∑ b : ZMod (p ^ m),
      ψ (u * b - a * v) * (f u a * g v) = 0 := by
  refine sum_eq_zero fun u hu => sum_eq_zero fun a _ => sum_eq_zero fun v _ => ?_
  rw [← sum_mul, ← zero_mul (f u a * g v), ← sum_affine p m hm ψ hψ u (-(a * v)) (isUnit_of_mem p m hu)]
  simp only [sub_eq_add_neg]

/- English proof (translation)
Distinguish the cases in `hi : i = 0`. Substitute `hi` using the available equality. Establish `hk1 : k - 1 ≠ 1` using `by omega`. Simplify using `only [eisF, const0, if_true, if_neg hk1]`. Rewrite using `[sum_zero_left p m hm ψ hψ]`.

Simplify using `[coefPos]`. Distinguish the cases in `hj : j = 0`. Substitute `hj` using the available equality. Establish `e : ∀ v ∈ primeTo p m, ∀ z : ℤ, eisF 1 (N * p ^ m) ζ (N * v.val) z 0 = ((1 / 2 - frc (N * p ^ m) (N * v.val) : ℚ) : K)`. Introduce `v hv z`.

Establish `: ¬ ((N * p ^ m : ℕ) : ℤ) ∣ N * v.val`. Introduce `h`. Establish `h' : N * p ^ m ∣ N * v.val` using `by exact_mod_cast h`. Conclude with `(mem_filter.mp hv).2 ((dvd_pow_self p (by omega)).trans (Nat.dvd_of_mul_dvd_mul_left hN h'))`. Simplify using `only [eisF, const0, if_true, if_neg this]`.

Rewrite using `[sum_congr rfl fun u _ => sum_congr rfl fun a _ => sum_congr rfl fun v hv => sum_congr rfl fun b _ => by`. Rewrite using `[e v hv], sum_zero_right p m hm ψ hψ]`. Simplify using `[coefPos]`. Simplify using `only [eisF, if_neg hi, if_neg hj]`.
-/
theorem drop_const (p m N k : ℕ) [Fact p.Prime] (hm : 1 ≤ m) (hN : 0 < N) (hk : 3 ≤ k)
    (ψ : DirichletCharacter K (p ^ m)) (hψ : ψ.IsPrimitive) (ζ : K) (y₁ y₂ : ℤ) (i j : ℕ) :
    ∑ u ∈ primeTo p m, ∑ a : ZMod (p ^ m), ∑ v ∈ primeTo p m, ∑ b : ZMod (p ^ m), ψ (u * b - a * v) *
      (eisF (k - 1) (N * p ^ m) ζ (N * u.val) (N * a.val + (p : ℤ) ^ m * y₁) i *
        eisF 1 (N * p ^ m) ζ (N * v.val) (N * b.val + (p : ℤ) ^ m * y₂) j) =
    ∑ u ∈ primeTo p m, ∑ a : ZMod (p ^ m), ∑ v ∈ primeTo p m, ∑ b : ZMod (p ^ m), ψ (u * b - a * v) *
      (coefPos (k - 1) (N * p ^ m) ζ (N * u.val) (N * a.val + (p : ℤ) ^ m * y₁) i *
        coefPos 1 (N * p ^ m) ζ (N * v.val) (N * b.val + (p : ℤ) ^ m * y₂) j) := by
  by_cases hi : i = 0
  · subst hi
    have hk1 : k - 1 ≠ 1 := by omega
    simp only [eisF, const0, if_true, if_neg hk1]
    rw [sum_zero_left p m hm ψ hψ]
    simp [coefPos]
  by_cases hj : j = 0
  · subst hj
    have e : ∀ v ∈ primeTo p m, ∀ z : ℤ, eisF 1 (N * p ^ m) ζ (N * v.val) z 0 =
        ((1 / 2 - frc (N * p ^ m) (N * v.val) : ℚ) : K) := by
      intro v hv z
      have : ¬ ((N * p ^ m : ℕ) : ℤ) ∣ N * v.val := by
        intro h
        have h' : N * p ^ m ∣ N * v.val := by exact_mod_cast h
        exact (mem_filter.mp hv).2 ((dvd_pow_self p (by omega)).trans (Nat.dvd_of_mul_dvd_mul_left hN h'))
      simp only [eisF, const0, if_true, if_neg this]
    rw [sum_congr rfl fun u _ => sum_congr rfl fun a _ => sum_congr rfl fun v hv => sum_congr rfl fun b _ => by
      rw [e v hv], sum_zero_right p m hm ψ hψ]
    simp [coefPos]
  simp only [eisF, if_neg hi, if_neg hj]

end GlobalTheory.KummerEisensteinGalois.UnitPiece

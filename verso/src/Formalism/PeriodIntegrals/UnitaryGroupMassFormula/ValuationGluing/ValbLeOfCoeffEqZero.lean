import Mathlib
import Formalism.PeriodIntegrals.ArtSch

namespace PI.ArtSch.Glue

open scoped NNReal

noncomputable section

variable {l : ℕ} [hl : Fact l.Prime]

/- English proof (translation)
The claim follows from `| 0 => by simp | k + 1 => by rw [pow_succ', pow_mul, ← add_assoc, PreTilt.coeff_pow_p, coeff_add_pow x n k]`.
-/
theorem coeff_add_pow (x : OCb l) (n : ℕ) : ∀ k : ℕ,
    PreTilt.coeff (n + k) x ^ (l ^ k) = PreTilt.coeff n x
  | 0 => by simp
  | k + 1 => by
    rw [pow_succ', pow_mul, ← add_assoc, PreTilt.coeff_pow_p, coeff_add_pow x n k]

/- English proof (translation)
Establish `hv` using `PadicComplexInt.integers l`. Establish `hnu : ¬ IsUnit ((l : ℕ) : OC l)` using `Fact.out`. Establish `h1` using `hv.map_le_one ((l : ℕ) : OC l)`. Establish `h2 : (PadicComplex.valued l).v (algebraMap (OC l) (PadicComplex l) ((l : ℕ) : OC l)) ≠ 1` using `fun h => hnu (hv.isUnit_iff_valuation_eq_one.mpr h)`. Rewrite `h1`, `h2` using `[map_natCast]`.

Conclude with `lt_of_le_of_ne h1 h2`.
-/
theorem v_l_lt_one : (PadicComplex.valued l).v ((l : ℕ) : PadicComplex l) < 1 := by
  have hv := PadicComplexInt.integers l
  have hnu : ¬ IsUnit ((l : ℕ) : OC l) := Fact.out
  have h1 := hv.map_le_one ((l : ℕ) : OC l)
  have h2 : (PadicComplex.valued l).v (algebraMap (OC l) (PadicComplex l) ((l : ℕ) : OC l)) ≠ 1 :=
    fun h => hnu (hv.isUnit_iff_valuation_eq_one.mpr h)
  rw [map_natCast] at h1 h2
  exact lt_of_le_of_ne h1 h2

/- English proof (translation)
Distinguish the cases in `h0 : r = 0`. Rewrite using `[h0, map_zero]`. Conclude with `zero_le`. Establish `hex : ∃ m, PreTilt.coeff m r ≠ 0`. Assume the negation of the conclusion as `hall`.

Use `push_neg at hall`. Conclude with `h0 (Perfection.ext fun m => (hall m).trans (map_zero _).symm)`. Take `⟨N, hM⟩ : ∃ N, PreTilt.coeff (N + n) r ≠ 0` from `⟨_, PreTilt.coeff_nat_find_add_ne_zero (h := hex) n⟩`. Establish `hk : PreTilt.coeff (N + n) r ^ (l ^ N) = 0`. Establish `h1` using `coeff_add_pow r n (N)`.

Rewrite `h1` using `[hr, Nat.add_comm]`. Conclude with `h1`. Use `show PreTilt.valAux (PadicComplex l) (PadicComplex.valued l).v (OC l) l r ≤ _`. Rewrite using `[PreTilt.valAux_eq (PadicComplexInt.integers l) hM]`. Take `⟨y, hy⟩` from `Ideal.Quotient.mk_surjective (PreTilt.coeff (N + n) r)`.

Rewrite using `[← hy, ModP.preVal_mk (PadicComplexInt.integers l) (by rw [hy]; exact hM)]`. Establish `hdiv : ((l : ℕ) : OC l) ∣ y ^ (l ^ N)`. Rewrite using `[← Ideal.mem_span_singleton, ← Ideal.Quotient.eq_zero_iff_mem, map_pow, hy]`. Conclude with `hk`. Establish `hle` using `(PadicComplexInt.integers l).le_of_dvd hdiv`.

Rewrite `hle` using `[map_pow, map_pow, map_natCast]`. Rewrite using `[pow_add, pow_mul]`. Conclude with `pow_le_pow_left₀ zero_le hle _`.
-/
theorem valb_le_of_coeff_eq_zero (r : OCb l) (n : ℕ) (hr : PreTilt.coeff n r = 0) :
    valb l r ≤ (PadicComplex.valued l).v ((l : ℕ) : PadicComplex l) ^ (l ^ n) := by
  by_cases h0 : r = 0
  · rw [h0, map_zero]; exact zero_le
  have hex : ∃ m, PreTilt.coeff m r ≠ 0 := by
    by_contra hall
    push_neg at hall
    exact h0 (Perfection.ext fun m => (hall m).trans (map_zero _).symm)
  obtain ⟨N, hM⟩ : ∃ N, PreTilt.coeff (N + n) r ≠ 0 :=
    ⟨_, PreTilt.coeff_nat_find_add_ne_zero (h := hex) n⟩
  have hk : PreTilt.coeff (N + n) r ^ (l ^ N) = 0 := by
    have h1 := coeff_add_pow r n (N)
    rw [hr, Nat.add_comm] at h1
    exact h1
  show PreTilt.valAux (PadicComplex l) (PadicComplex.valued l).v (OC l) l r ≤ _
  rw [PreTilt.valAux_eq (PadicComplexInt.integers l) hM]
  obtain ⟨y, hy⟩ := Ideal.Quotient.mk_surjective (PreTilt.coeff (N + n) r)
  rw [← hy, ModP.preVal_mk (PadicComplexInt.integers l) (by rw [hy]; exact hM)]
  have hdiv : ((l : ℕ) : OC l) ∣ y ^ (l ^ N) := by
    rw [← Ideal.mem_span_singleton, ← Ideal.Quotient.eq_zero_iff_mem, map_pow, hy]
    exact hk
  have hle := (PadicComplexInt.integers l).le_of_dvd hdiv
  rw [map_pow, map_pow, map_natCast] at hle
  rw [pow_add, pow_mul]
  exact pow_le_pow_left₀ zero_le hle _

/- English proof (translation)
Establish `hq` using `v_l_lt_one (l := l)`. Take `⟨n, hn⟩` from `exists_pow_lt_of_lt_one ht hq`. Conclude with `⟨n, lt_of_le_of_lt (pow_le_pow_of_le_one zero_le hq.le (Nat.lt_pow_self (Fact.out : l.Prime).one_lt).le) hn⟩`.
-/
theorem exists_small (t : ℝ≥0) (ht : 0 < t) :
    ∃ n : ℕ, (PadicComplex.valued l).v ((l : ℕ) : PadicComplex l) ^ (l ^ n) < t := by
  have hq := v_l_lt_one (l := l)
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one ht hq
  exact ⟨n, lt_of_le_of_lt (pow_le_pow_of_le_one zero_le hq.le
    (Nat.lt_pow_self (Fact.out : l.Prime).one_lt).le) hn⟩

/- English proof (translation)
Introduce `b`. Take `⟨z, hz⟩` from `hR l 0 b`. Conclude with `⟨z, by rw [frobenius_def]; linear_combination hz⟩`.
-/
theorem frob_surj (hR : RootModP) : Function.Surjective (frobenius (ModP (OC l) l) l) := by
  intro b
  obtain ⟨z, hz⟩ := hR l 0 b
  exact ⟨z, by rw [frobenius_def]; linear_combination hz⟩

/- English proof (translation)
Introduce `hR hD hS l _ a`. Take `⟨⟨x, s⟩, rfl⟩` from `IsLocalization.mk'_surjective (nonZeroDivisors (OCb l)) a`. Establish `hs0 : (s : OCb l) ≠ 0` using `nonZeroDivisors.coe_ne_zero s`. Establish `hl1 : 1 ≤ l` using `(Fact.out : l.Prime).one_lt.le`. Take `⟨c, hc⟩ : ∃ c : OCb l, c = (s : OCb l) ^ (l - 1)` from `⟨_, rfl⟩`.

Take `⟨b, hb⟩ : ∃ b : OCb l, b = x * (s : OCb l) ^ (l - 1)` from `⟨_, rfl⟩`. Establish `hvs : 0 < valb l ((s : OCb l) ^ l)`. Rewrite using `[pos_iff_ne_zero, Ne, PreTilt.map_eq_zero]`. Conclude with `pow_ne_zero _ hs0`. Take `⟨n, hn⟩` from `exists_small (l := l) (valb l ((s : OCb l) ^ l)) hvs`.

Take `⟨z0, hz0⟩` from `hR l (PreTilt.coeff n c) (PreTilt.coeff n b)`. Take `⟨z, hz'⟩ : ∃ z : OCb l, PreTilt.coeff n z = z0` from `Perfection.coeff_surjective (frob_surj (l := l) hR) n z0`. Take `⟨rr, hrr⟩ : ∃ rr : OCb l, rr = z ^ l - c * z - b` from `⟨_, rfl⟩`. Establish `hcr : PreTilt.coeff n rr = 0`. Rewrite using `[hrr, map_sub, map_sub, map_mul, map_pow, hz']`.

Conclude with `hz0`. Establish `hvr : valb l rr < valb l ((s : OCb l) ^ l)` using `lt_of_le_of_lt (valb_le_of_coeff_eq_zero rr n hcr) hn`. Take `⟨e, he⟩` from `hD l rr ((s : OCb l) ^ l) hvr.le`. Establish `hve : valb l e < 1`. Assume the negation of the conclusion as `hge`.

Use `push_neg at hge`. Establish `h3 : valb l ((s : OCb l) ^ l) ≤ valb l rr`. Rewrite using `[he, map_mul]`. Conclude with `le_mul_of_one_le_right zero_le hge`. Conclude with `absurd hvr (not_lt.mpr h3)`.

Take `⟨w, hw⟩` from `hS l (-e) (by rwa [Valuation.map_neg])`. Take `⟨Z, hZ⟩ : ∃ Z : OCb l, Z = z + (s : OCb l) * w` from `⟨_, rfl⟩`. Establish `hfrob : Z ^ l = z ^ l + (s : OCb l) ^ l * w ^ l`. Rewrite using `[hZ, add_pow_char, mul_pow]`. Establish `hcs : c * (s : OCb l) = (s : OCb l) ^ l`.

Rewrite using `[hc, ← pow_succ, Nat.sub_add_cancel hl1]`. Establish `he1 : z ^ l - c * z - b = (s : OCb l) ^ l * e` using `by rw [← hrr]; exact he`. Establish `key : Z ^ l - c * Z - b = 0`. Take the linear combination `hfrob + he1 + (s : OCb l) ^ l * hw - w * hcs - c * hZ`. Use `⟨IsLocalization.mk' (Cb l) Z s, ?_⟩` and prove the remaining obligations.

Simplify using `only [IsFractionRing.mk'_eq_div]`. Establish `hS0 : algebraMap (OCb l) (Cb l) (s : OCb l) ≠ 0` using `IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors s.2`. Establish `hmap` using `congrArg (algebraMap (OCb l) (Cb l)) key`. Rewrite `hmap` using `[map_sub, map_sub, map_mul, map_pow, map_zero, hc, hb, map_mul, map_pow]`. Establish `hT0 : algebraMap (OCb l) (Cb l) (s : OCb l) ^ (l - 1) ≠ 0` using `pow_ne_zero _ hS0`.

Establish `hSl : algebraMap (OCb l) (Cb l) (s : OCb l) ^ l = algebraMap (OCb l) (Cb l) (s : OCb l) ^ (l - 1) * algebraMap (OCb l) (Cb l) (s : OCb l)`. Rewrite using `[← pow_succ, Nat.sub_add_cancel hl1]`. Rewrite using `[div_pow, hSl, show algebraMap (OCb l) (Cb l) Z ^ l = algebraMap (OCb l) (Cb l) (s : OCb l) ^ (l - 1) * algebraMap (OCb l) (Cb l) Z + algebraMap (OCb l) (Cb l) x * algebraMap (OCb l) (Cb l) (s : OCb l) ^ (l - 1) by`. Take the linear combination `hmap]`. Clear the denominators using the available nonvanishing facts.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem tiltGlue : TiltGlue := by
  intro hR hD hS l _ a
  obtain ⟨⟨x, s⟩, rfl⟩ := IsLocalization.mk'_surjective (nonZeroDivisors (OCb l)) a
  have hs0 : (s : OCb l) ≠ 0 := nonZeroDivisors.coe_ne_zero s
  have hl1 : 1 ≤ l := (Fact.out : l.Prime).one_lt.le
  obtain ⟨c, hc⟩ : ∃ c : OCb l, c = (s : OCb l) ^ (l - 1) := ⟨_, rfl⟩
  obtain ⟨b, hb⟩ : ∃ b : OCb l, b = x * (s : OCb l) ^ (l - 1) := ⟨_, rfl⟩
  have hvs : 0 < valb l ((s : OCb l) ^ l) := by
    rw [pos_iff_ne_zero, Ne, PreTilt.map_eq_zero]
    exact pow_ne_zero _ hs0
  obtain ⟨n, hn⟩ := exists_small (l := l) (valb l ((s : OCb l) ^ l)) hvs
  obtain ⟨z0, hz0⟩ := hR l (PreTilt.coeff n c) (PreTilt.coeff n b)
  obtain ⟨z, hz'⟩ : ∃ z : OCb l, PreTilt.coeff n z = z0 :=
    Perfection.coeff_surjective (frob_surj (l := l) hR) n z0
  obtain ⟨rr, hrr⟩ : ∃ rr : OCb l, rr = z ^ l - c * z - b := ⟨_, rfl⟩
  have hcr : PreTilt.coeff n rr = 0 := by
    rw [hrr, map_sub, map_sub, map_mul, map_pow, hz']
    exact hz0
  have hvr : valb l rr < valb l ((s : OCb l) ^ l) :=
    lt_of_le_of_lt (valb_le_of_coeff_eq_zero rr n hcr) hn
  obtain ⟨e, he⟩ := hD l rr ((s : OCb l) ^ l) hvr.le
  have hve : valb l e < 1 := by
    by_contra hge
    push_neg at hge
    have h3 : valb l ((s : OCb l) ^ l) ≤ valb l rr := by
      rw [he, map_mul]
      exact le_mul_of_one_le_right zero_le hge
    exact absurd hvr (not_lt.mpr h3)
  obtain ⟨w, hw⟩ := hS l (-e) (by rwa [Valuation.map_neg])
  obtain ⟨Z, hZ⟩ : ∃ Z : OCb l, Z = z + (s : OCb l) * w := ⟨_, rfl⟩
  have hfrob : Z ^ l = z ^ l + (s : OCb l) ^ l * w ^ l := by
    rw [hZ, add_pow_char, mul_pow]
  have hcs : c * (s : OCb l) = (s : OCb l) ^ l := by
    rw [hc, ← pow_succ, Nat.sub_add_cancel hl1]
  have he1 : z ^ l - c * z - b = (s : OCb l) ^ l * e := by rw [← hrr]; exact he
  have key : Z ^ l - c * Z - b = 0 := by
    linear_combination hfrob + he1 + (s : OCb l) ^ l * hw - w * hcs - c * hZ
  refine ⟨IsLocalization.mk' (Cb l) Z s, ?_⟩
  simp only [IsFractionRing.mk'_eq_div]
  have hS0 : algebraMap (OCb l) (Cb l) (s : OCb l) ≠ 0 :=
    IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors s.2
  have hmap := congrArg (algebraMap (OCb l) (Cb l)) key
  rw [map_sub, map_sub, map_mul, map_pow, map_zero, hc, hb, map_mul, map_pow] at hmap
  have hT0 : algebraMap (OCb l) (Cb l) (s : OCb l) ^ (l - 1) ≠ 0 := pow_ne_zero _ hS0
  have hSl : algebraMap (OCb l) (Cb l) (s : OCb l) ^ l =
      algebraMap (OCb l) (Cb l) (s : OCb l) ^ (l - 1) * algebraMap (OCb l) (Cb l) (s : OCb l) := by
    rw [← pow_succ, Nat.sub_add_cancel hl1]
  rw [div_pow, hSl, show algebraMap (OCb l) (Cb l) Z ^ l =
      algebraMap (OCb l) (Cb l) (s : OCb l) ^ (l - 1) * algebraMap (OCb l) (Cb l) Z +
        algebraMap (OCb l) (Cb l) x * algebraMap (OCb l) (Cb l) (s : OCb l) ^ (l - 1) by
      linear_combination hmap]
  field_simp
  ring

end

end PI.ArtSch.Glue

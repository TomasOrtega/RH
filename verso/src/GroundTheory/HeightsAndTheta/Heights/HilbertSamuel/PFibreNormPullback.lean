import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsFibreNormPullback
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsFibreNormRoots
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterBridgeB
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry MvPolynomial

noncomputable section

namespace FibreNormPullback

/- English proof (translation)
Use `charZero_of_inj_zero fun m hm => ?_` and prove the remaining obligations. Establish `hmem : (m : ℤ) ∈ (mCoordIdeal y).comap (C : ℤ →+* MRing ι)` using `by show mConeMap y (C (m : ℤ)) = 0`. Simplify using `only [mConeMap, eq_intCast, Int.cast_natCast]`. Rewrite using `[map_natCast, ← map_natCast (MvPolynomial.C : Ω →+* MvPolynomial K Ω), hm, map_zero]`. Rewrite `hmem` using `[hV.2.2.1, Ideal.mem_bot]`.

Conclude with `hmem` after adjusting the coercions.
-/
theorem charZero_of_isArithVar {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω]
    {y : (Σ k, ι k) → Ω} {d : ℕ} (hV : IsArithVar (mCoordIdeal y) d) : CharZero Ω := by
  refine charZero_of_inj_zero fun m hm => ?_
  have hmem : (m : ℤ) ∈ (mCoordIdeal y).comap (C : ℤ →+* MRing ι) := by
    show mConeMap y (C (m : ℤ)) = 0
    simp only [mConeMap, eq_intCast, Int.cast_natCast]
    rw [map_natCast, ← map_natCast (MvPolynomial.C : Ω →+* MvPolynomial K Ω), hm, map_zero]
  rw [hV.2.2.1, Ideal.mem_bot] at hmem
  exact_mod_cast hmem

/- English proof (translation)
Introduce `{d} hd` and use `h (by rw [coeff_map, eq_intCast, ne_eq, Int.cast_eq_zero]; exact hd)`.
-/
theorem isHomogeneous_of_map {σ : Type} {F : MvPolynomial σ ℤ} {m : ℕ}
    (h : (map (Int.castRingHom ℚ) F).IsHomogeneous m) : F.IsHomogeneous m := fun {d} hd =>
  h (by rw [coeff_map, eq_intCast, ne_eq, Int.cast_eq_zero]; exact hd)

/- English proof (translation)
Proceed by induction on `m using Multiset.induction_on with`. Consider the case `empty => simp`. Consider the case `cons a m ih`. Rewrite using `[Multiset.prod_cons, norm_mul, Multiset.card_cons, pow_succ']`. Conclude with `mul_le_mul (h a (Multiset.mem_cons_self a m)) (ih fun x hx => h x (Multiset.mem_cons_of_mem hx)) (norm_nonneg _) hB`.
-/
theorem norm_prod_le_pow {B : ℝ} (hB : 0 ≤ B) (m : Multiset ℂ) (h : ∀ x ∈ m, ‖x‖ ≤ B) :
    ‖m.prod‖ ≤ B ^ Multiset.card m := by
  induction m using Multiset.induction_on with
  | empty => simp
  | cons a m ih =>
    rw [Multiset.prod_cons, norm_mul, Multiset.card_cons, pow_succ']
    exact mul_le_mul (h a (Multiset.mem_cons_self a m)) (ih fun x hx => h x (Multiset.mem_cons_of_mem hx))
      (norm_nonneg _) hB

/- English proof (translation)
Use `set p : Polynomial ℂ := ∑ i ∈ Finset.range (n + 1), Polynomial.C (a i) * Polynomial.X ^ (n - i) with hp`. Establish `hcoeff : ∀ k, p.coeff k = ∑ i ∈ Finset.range (n + 1), if k = n - i then a i else 0`. Introduce `k`. Rewrite using `[hp, Polynomial.finsetSum_coeff]`. Simplify using `only [Polynomial.coeff_C_mul_X_pow]`.

Establish `hdeg : p.natDegree ≤ n` using `Polynomial.natDegree_sum_le_of_forall_le _ _ fun i _ => (Polynomial.natDegree_C_mul_X_pow_le _ _).trans (Nat.sub_le n i)`. Establish `hlead : p.coeff n = 1`. Rewrite using `[hcoeff, Finset.sum_eq_single 0]`. Simplify using `[ha]`. Introduce `i hi hi0`.

Rewrite `hi` using `[Finset.mem_range]`. Rewrite using `[if_neg]`. Use linear arithmetic over natural numbers and integers. Introduce `h`. Conclude with `absurd (Finset.mem_range.mpr (Nat.succ_pos n)) h`.

Establish `hmon : p.Monic` using `Polynomial.monic_of_degree_le n (Polynomial.degree_le_of_natDegree_le hdeg) hlead`. Establish `hnat : p.natDegree = n` using `Polynomial.natDegree_eq_of_le_of_coeff_ne_zero hdeg (by rw [hlead]; exact one_ne_zero)`. Establish `hzero : p.coeff 0 = a n`. Rewrite using `[hcoeff, Finset.sum_eq_single n]`. Simplify using the standard rewrite rules.

Introduce `i hi hin`. Rewrite `hi` using `[Finset.mem_range]`. Rewrite using `[if_neg]`. Use linear arithmetic over natural numbers and integers. Introduce `h`.

Conclude with `absurd (Finset.mem_range.mpr (Nat.lt_succ_self n)) h`. Establish `hsplit : p.Splits` using `IsAlgClosed.splits p`. Establish `hcard : Multiset.card p.roots = n` using `by rw [Polynomial.splits_iff_card_roots.mp hsplit, hnat]`. Establish `hprod` using `hsplit.coeff_zero_eq_prod_roots_of_monic hmon`. Rewrite `hprod` using `[hzero, hnat]`.

Rewrite using `[hprod, norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul, ← hcard]`. Use `norm_prod_le_pow hB _ fun w hw => hroot w ?_` and prove the remaining obligations. Establish `hw'` using `(Polynomial.mem_roots hmon.ne_zero).mp hw`. Rewrite `hw'` using `[Polynomial.IsRoot.def, hp, Polynomial.eval_finsetSum]`. Simplify using `using hw'`.
-/
theorem norm_last_le {n : ℕ} (a : ℕ → ℂ) (ha : a 0 = 1) {B : ℝ} (hB : 0 ≤ B)
    (hroot : ∀ w : ℂ, ∑ i ∈ Finset.range (n + 1), a i * w ^ (n - i) = 0 → ‖w‖ ≤ B) :
    ‖a n‖ ≤ B ^ n := by
  classical
  set p : Polynomial ℂ := ∑ i ∈ Finset.range (n + 1), Polynomial.C (a i) * Polynomial.X ^ (n - i) with hp
  have hcoeff : ∀ k, p.coeff k = ∑ i ∈ Finset.range (n + 1), if k = n - i then a i else 0 := by
    intro k
    rw [hp, Polynomial.finsetSum_coeff]
    simp only [Polynomial.coeff_C_mul_X_pow]
  have hdeg : p.natDegree ≤ n :=
    Polynomial.natDegree_sum_le_of_forall_le _ _ fun i _ =>
      (Polynomial.natDegree_C_mul_X_pow_le _ _).trans (Nat.sub_le n i)
  have hlead : p.coeff n = 1 := by
    rw [hcoeff, Finset.sum_eq_single 0]
    · simp [ha]
    · intro i hi hi0
      rw [Finset.mem_range] at hi
      rw [if_neg]
      omega
    · intro h; exact absurd (Finset.mem_range.mpr (Nat.succ_pos n)) h
  have hmon : p.Monic := Polynomial.monic_of_degree_le n (Polynomial.degree_le_of_natDegree_le hdeg) hlead
  have hnat : p.natDegree = n :=
    Polynomial.natDegree_eq_of_le_of_coeff_ne_zero hdeg (by rw [hlead]; exact one_ne_zero)
  have hzero : p.coeff 0 = a n := by
    rw [hcoeff, Finset.sum_eq_single n]
    · simp
    · intro i hi hin
      rw [Finset.mem_range] at hi
      rw [if_neg]
      omega
    · intro h; exact absurd (Finset.mem_range.mpr (Nat.lt_succ_self n)) h
  have hsplit : p.Splits := IsAlgClosed.splits p
  have hcard : Multiset.card p.roots = n := by rw [Polynomial.splits_iff_card_roots.mp hsplit, hnat]
  have hprod := hsplit.coeff_zero_eq_prod_roots_of_monic hmon
  rw [hzero, hnat] at hprod
  rw [hprod, norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul, ← hcard]
  refine norm_prod_le_pow hB _ fun w hw => hroot w ?_
  have hw' := (Polynomial.mem_roots hmon.ne_zero).mp hw
  rw [Polynomial.IsRoot.def, hp, Polynomial.eval_finsetSum] at hw'
  simpa using hw'

/- English proof (translation)
Introduce `K _ ι _ Ω _ y D e L q hV hBir he hL hL0`. Establish `: CharZero Ω` using `charZero_of_isArithVar hV`. Take `⟨hfin, hA'⟩` from `hA K ι Ω y D e L q hV hBir he hL hL0`. Take `⟨M₀, hM₀, hI'⟩` from `hI K ι Ω y D e L q hV hBir he hL hL0`. Establish `hR'` using `hR K ι Ω y D e L q hV hBir he hL hL0`.

Establish `hP : IsMultiHomogIdeal (mCoordIdeal y)` using `hV.2.1.2.1`. Use `set n := Module.finrank (pullField y L) Ω`. Establish `hn1 : 1 ≤ n` using `Module.finrank_pos`. Use `⟨n, M₀, hn1, by exact_mod_cast hM₀, fun τ s hs hs0 => ?_⟩` and prove the remaining obligations. Take `⟨c, hc, hcn⟩` from `hA' τ s hs`.

Take `⟨F, hF⟩` from `hI' τ s hs c hc`. Establish `hRc` using `hR' τ s hs c hc`. Take `⟨_, hc0, hch, -⟩` from `hc`. Establish `hM₀q : ((M₀ : ℚ) ^ τ) ≠ 0` using `pow_ne_zero _ (by exact_mod_cast (show M₀ ≠ 0 by omega))`. Use `⟨F, ?_, ?_, fun ζ hζ S hS M hM hrep => ?_⟩` and prove the remaining obligations.

Introduce and unpack `rfl`. Rewrite `hF` using `[map_zero, eq_comm, smul_eq_zero]`. Conclude with `hF.elim hM₀q (hcn hs0)`. Apply `isHomogeneous_of_map` to reduce the goal to its premises. Rewrite using `[hF, smul_eq_C_mul, show n * q * τ = 0 + n * (q * τ) by ring]`.

Conclude with `(isHomogeneous_C _ _).mul (hch n le_rfl)`. Establish `hmapF : eval ζ (map (Int.castRingHom ℂ) F) = (M₀ : ℂ) ^ τ * eval ζ (map (algebraMap ℚ ℂ) (c n))`. Establish `h1 : map (Int.castRingHom ℂ) F = map (algebraMap ℚ ℂ) (map (Int.castRingHom ℚ) F)`. Rewrite using `[map_map]`. Use `congr 1`.

Rewrite using `[h1, hF, smul_eq_C_mul, map_mul, map_C, eval_mul, eval_C]`. Simplify using the standard rewrite rules. Use `set B := M * ‖ζ‖ ^ (q * τ) with hBdef`. Establish `hB0 : 0 ≤ B` using `mul_nonneg hM (pow_nonneg (norm_nonneg _) _)`. Establish `hroot : ∀ w : ℂ, ∑ i ∈ Finset.range (n + 1), eval ζ (map (algebraMap ℚ ℂ) (c i)) * w ^ (n - i) = 0 → ‖w‖ ≤ B`.

Introduce `w hw`. Take `⟨z, hz, t, ht0, hLz, hval⟩` from `hRc ζ hζ w hw`. Take `⟨z', hz'S, r, hr0, rfl⟩` from `hS z hz ⟨t, hLz⟩`. Establish `hz'm : z' ∈ mcPts (mCoordIdeal y)`. Establish `h1` using `mcPts_smul hP (fun k => (r k)⁻¹) (fun k => inv_ne_zero (hr0 k)) hz`.

Use `h1 using 1` and compare the differences between its conclusion and the goal. Use function extensionality and compare the values at `p`. Simplify using `[hr0 p.1]`. Take `⟨dg, dh, g, h, hg, hh, hd, hgh, hz'0, hle⟩` from `hrep z' hz'S hz'm`. Establish `hgz` using `eval_smul_homog g dg hg r z'`.

Establish `hhz` using `eval_smul_homog h dh hh r z'`. Establish `hhz0 : eval (fun p => r p.1 * z' p) (map (Int.castRingHom ℂ) h) ≠ 0`. Rewrite using `[hhz]`. Conclude with `mul_ne_zero (Finset.prod_ne_zero_iff.mpr fun k _ => pow_ne_zero _ (hr0 k)) hz'0`. Establish `hv` using `hval dg dh g h hg hh hd hgh hhz0`.

Establish `hRg : (∏ k, r k ^ dg k) = (∏ k, r k ^ dh k) * (∏ k, r k ^ e k) ^ (q * τ)`. Rewrite using `[← Finset.prod_pow, ← Finset.prod_mul_distrib]`. Use `Finset.prod_congr rfl fun k _ => ?_` and prove the remaining obligations. Rewrite using `[hd k, ← pow_mul, ← pow_add]`. Expand and normalize the polynomial expressions, which then agree.

Establish `hnormL : ‖∏ k, r k ^ e k‖ * ‖fun j => eval z' (map (Int.castRingHom ℂ) (L j))‖ = ‖t‖ * ‖ζ‖`. Establish `h1 : (∏ k, r k ^ e k) • (fun j => eval z' (map (Int.castRingHom ℂ) (L j))) = t • ζ`. Use function extensionality and compare the values at `j`. Simplify using `only [Pi.smul_apply, smul_eq_mul]`. Rewrite using `[← eval_smul_homog (L j) e (hL j) r z', hLz j]`.

Rewrite using `[← norm_smul, h1, norm_smul]`. Establish `hpos : 0 < ‖t‖ ^ (q * τ) * ‖eval (fun p => r p.1 * z' p) (map (Int.castRingHom ℂ) h)‖` using `mul_pos (pow_pos (norm_pos_iff.mpr ht0) _) (norm_pos_iff.mpr hhz0)`. Use `le_of_mul_le_mul_right ?_ hpos` and prove the remaining obligations. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[hv, norm_mul, norm_mul, norm_pow]`.

Expand and normalize the polynomial expressions, which then agree. Use `_ = ‖∏ k, r k ^ dg k‖ * ‖eval z' (map (Int.castRingHom ℂ) g)‖ := by rw [hgz, norm_mul]`. Use `_ ≤ ‖∏ k, r k ^ dg k‖ * (M * ‖fun j => eval z' (map (Int.castRingHom ℂ) (L j))‖ ^ (q * τ) * ‖eval z' (map (Int.castRingHom ℂ) h)‖) := mul_le_mul_of_nonneg_left hle (norm_nonneg _)`. Use `_ = M * (‖∏ k, r k ^ e k‖ * ‖fun j => eval z' (map (Int.castRingHom ℂ) (L j))‖) ^ (q * τ) * (‖∏ k, r k ^ dh k‖ * ‖eval z' (map (Int.castRingHom ℂ) h)‖) := by`. Rewrite using `[hRg, norm_mul, norm_pow]`.

Expand and normalize the polynomial expressions, which then agree. Use `_ = B * (‖t‖ ^ (q * τ) * ‖eval (fun p => r p.1 * z' p) (map (Int.castRingHom ℂ) h)‖) := by`. Rewrite using `[hnormL, hhz, norm_mul, hBdef]`. Expand and normalize the polynomial expressions, which then agree. Establish `key` using `norm_last_le (fun i => eval ζ (map (algebraMap ℚ ℂ) (c i))) (by simp [hc0]) hB0 hroot`.

Rewrite using `[hmapF, norm_mul, norm_pow, Complex.norm_natCast]`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[hBdef, mul_pow, ← pow_mul, show q * τ * n = n * q * τ by ring]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem proof (hA : FibreNormCharpoly.Statement) (hI : FibreNormIntegral.Statement)
    (hR : FibreNormRoots.Statement) : FibreNormPullback.Statement := by
  intro K _ ι _ Ω _ y D e L q hV hBir he hL hL0
  classical
  have : CharZero Ω := charZero_of_isArithVar hV
  obtain ⟨hfin, hA'⟩ := hA K ι Ω y D e L q hV hBir he hL hL0
  obtain ⟨M₀, hM₀, hI'⟩ := hI K ι Ω y D e L q hV hBir he hL hL0
  have hR' := hR K ι Ω y D e L q hV hBir he hL hL0
  have hP : IsMultiHomogIdeal (mCoordIdeal y) := hV.2.1.2.1
  set n := Module.finrank (pullField y L) Ω
  have hn1 : 1 ≤ n := Module.finrank_pos
  refine ⟨n, M₀, hn1, by exact_mod_cast hM₀, fun τ s hs hs0 => ?_⟩
  obtain ⟨c, hc, hcn⟩ := hA' τ s hs
  obtain ⟨F, hF⟩ := hI' τ s hs c hc
  have hRc := hR' τ s hs c hc
  obtain ⟨_, hc0, hch, -⟩ := hc
  have hM₀q : ((M₀ : ℚ) ^ τ) ≠ 0 := pow_ne_zero _ (by exact_mod_cast (show M₀ ≠ 0 by omega))
  refine ⟨F, ?_, ?_, fun ζ hζ S hS M hM hrep => ?_⟩
  · rintro rfl
    rw [map_zero, eq_comm, smul_eq_zero] at hF
    exact hF.elim hM₀q (hcn hs0)
  · apply isHomogeneous_of_map
    rw [hF, smul_eq_C_mul, show n * q * τ = 0 + n * (q * τ) by ring]
    exact (isHomogeneous_C _ _).mul (hch n le_rfl)

  have hmapF : eval ζ (map (Int.castRingHom ℂ) F) = (M₀ : ℂ) ^ τ * eval ζ (map (algebraMap ℚ ℂ) (c n)) := by
    have h1 : map (Int.castRingHom ℂ) F = map (algebraMap ℚ ℂ) (map (Int.castRingHom ℚ) F) := by
      rw [map_map]
      congr 1
    rw [h1, hF, smul_eq_C_mul, map_mul, map_C, eval_mul, eval_C]
    simp
  set B := M * ‖ζ‖ ^ (q * τ) with hBdef
  have hB0 : 0 ≤ B := mul_nonneg hM (pow_nonneg (norm_nonneg _) _)
  have hroot : ∀ w : ℂ, ∑ i ∈ Finset.range (n + 1), eval ζ (map (algebraMap ℚ ℂ) (c i)) * w ^ (n - i) = 0 →
      ‖w‖ ≤ B := by
    intro w hw
    obtain ⟨z, hz, t, ht0, hLz, hval⟩ := hRc ζ hζ w hw
    obtain ⟨z', hz'S, r, hr0, rfl⟩ := hS z hz ⟨t, hLz⟩
    have hz'm : z' ∈ mcPts (mCoordIdeal y) := by
      have h1 := mcPts_smul hP (fun k => (r k)⁻¹) (fun k => inv_ne_zero (hr0 k)) hz
      convert h1 using 1
      funext p
      simp [hr0 p.1]
    obtain ⟨dg, dh, g, h, hg, hh, hd, hgh, hz'0, hle⟩ := hrep z' hz'S hz'm
    have hgz := eval_smul_homog g dg hg r z'
    have hhz := eval_smul_homog h dh hh r z'
    have hhz0 : eval (fun p => r p.1 * z' p) (map (Int.castRingHom ℂ) h) ≠ 0 := by
      rw [hhz]
      exact mul_ne_zero (Finset.prod_ne_zero_iff.mpr fun k _ => pow_ne_zero _ (hr0 k)) hz'0
    have hv := hval dg dh g h hg hh hd hgh hhz0
    have hRg : (∏ k, r k ^ dg k) = (∏ k, r k ^ dh k) * (∏ k, r k ^ e k) ^ (q * τ) := by
      rw [← Finset.prod_pow, ← Finset.prod_mul_distrib]
      refine Finset.prod_congr rfl fun k _ => ?_
      rw [hd k, ← pow_mul, ← pow_add]
      ring
    have hnormL : ‖∏ k, r k ^ e k‖ * ‖fun j => eval z' (map (Int.castRingHom ℂ) (L j))‖ = ‖t‖ * ‖ζ‖ := by
      have h1 : (∏ k, r k ^ e k) • (fun j => eval z' (map (Int.castRingHom ℂ) (L j))) = t • ζ := by
        funext j
        simp only [Pi.smul_apply, smul_eq_mul]
        rw [← eval_smul_homog (L j) e (hL j) r z', hLz j]
      rw [← norm_smul, h1, norm_smul]
    have hpos : 0 < ‖t‖ ^ (q * τ) * ‖eval (fun p => r p.1 * z' p) (map (Int.castRingHom ℂ) h)‖ :=
      mul_pos (pow_pos (norm_pos_iff.mpr ht0) _) (norm_pos_iff.mpr hhz0)
    refine le_of_mul_le_mul_right ?_ hpos
    calc ‖w‖ * (‖t‖ ^ (q * τ) * ‖eval (fun p => r p.1 * z' p) (map (Int.castRingHom ℂ) h)‖)
        = ‖eval (fun p => r p.1 * z' p) (map (Int.castRingHom ℂ) g)‖ := by
          rw [hv, norm_mul, norm_mul, norm_pow]; ring
      _ = ‖∏ k, r k ^ dg k‖ * ‖eval z' (map (Int.castRingHom ℂ) g)‖ := by rw [hgz, norm_mul]
      _ ≤ ‖∏ k, r k ^ dg k‖ * (M * ‖fun j => eval z' (map (Int.castRingHom ℂ) (L j))‖ ^ (q * τ) *
            ‖eval z' (map (Int.castRingHom ℂ) h)‖) := mul_le_mul_of_nonneg_left hle (norm_nonneg _)
      _ = M * (‖∏ k, r k ^ e k‖ * ‖fun j => eval z' (map (Int.castRingHom ℂ) (L j))‖) ^ (q * τ) *
            (‖∏ k, r k ^ dh k‖ * ‖eval z' (map (Int.castRingHom ℂ) h)‖) := by
          rw [hRg, norm_mul, norm_pow]; ring
      _ = B * (‖t‖ ^ (q * τ) * ‖eval (fun p => r p.1 * z' p) (map (Int.castRingHom ℂ) h)‖) := by
          rw [hnormL, hhz, norm_mul, hBdef]; ring
  have key := norm_last_le (fun i => eval ζ (map (algebraMap ℚ ℂ) (c i))) (by simp [hc0]) hB0 hroot
  rw [hmapF, norm_mul, norm_pow, Complex.norm_natCast]
  calc (M₀ : ℝ) ^ τ * ‖eval ζ (map (algebraMap ℚ ℂ) (c n))‖ ≤ (M₀ : ℝ) ^ τ * B ^ n :=
        mul_le_mul_of_nonneg_left key (pow_nonneg (Nat.cast_nonneg _) _)
    _ = (M₀ : ℝ) ^ τ * ‖ζ‖ ^ (n * q * τ) * M ^ n := by
        rw [hBdef, mul_pow, ← pow_mul, show q * τ * n = n * q * τ by ring]
        ring

end FibreNormPullback

end

end GroundTheory.Heights₂.Heights.HilbertSamuel

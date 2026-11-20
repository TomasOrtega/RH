import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.ApplyEqOfMemAdjoin
import Development.AbelianVarietyTheory.Definitions.Foundations.IsTopWTopWOfExists

open GlobalTheory.K5 GlobalTheory.Glue

noncomputable section

namespace GlobalTheory.Glue.DPsi

variable {p : ℕ} [Fact p.Prime]

/- English proof (translation)
Use extensionality with `r`. Simplify using `[thL, mul_add]`.
-/
theorem thL_add (a b : Lau p) : thL (a + b) = thL a + thL b := by
  ext r
  simp [thL, mul_add]

/- English proof (translation)
Use extensionality with `r`. Simplify using `[thL]`.
-/
theorem thL_zero : thL (0 : Lau p) = 0 := by
  ext r
  simp [thL]

def sh (N : ℕ) (i : ℤ) (w : ℤ → ℤ_[p]) (b : Lau p) : Lau p where
  coeff r := if (N : ℤ) ∣ r then w r * b.coeff (r + i) else 0
  isPWO_support' := by
    refine (b.isPWO_support.image_of_monotone (f := fun r : ℤ => r - i) (fun x y h => by simpa using h)).mono ?_
    intro r hr
    refine ⟨r + i, ?_, by simp⟩
    intro h
    apply hr
    simp [h]

def dn (N : ℕ) (hN : 0 < N) (B : Lau p) : Lau p where
  coeff j := B.coeff ((N : ℤ) * j)
  isPWO_support' := by
    have hm : StrictMono (fun j : ℤ => (N : ℤ) * j) := fun x y h =>
      mul_lt_mul_of_pos_left h (by exact_mod_cast hN)
    have hwf := B.isPWO_support
    rw [Set.IsPWO, Set.partiallyWellOrderedOn_iff_exists_lt] at hwf ⊢
    intro g hg
    obtain ⟨m, n, hmn, h⟩ := hwf (fun k => (N : ℤ) * g k) hg
    exact ⟨m, n, hmn, hm.le_iff_le.1 h⟩

/- English proof (translation)
Rewrite using `[← nsmul_eq_mul, ← Nat.cast_smul_eq_nsmul ℤ_[p], HahnSeries.coeff_smul, smul_eq_mul]`.
-/
theorem coeff_natCast_mul (n : ℕ) (X : Lau p) (s : ℤ) : ((n : Lau p) * X).coeff s = (n : ℤ_[p]) * X.coeff s := by
  rw [← nsmul_eq_mul, ← Nat.cast_smul_eq_nsmul ℤ_[p], HahnSeries.coeff_smul, smul_eq_mul]

/- English proof (translation)
Use extensionality with `s`. Establish `hN' : (0 : ℤ) < N` using `by exact_mod_cast hN`. Rewrite using `[HahnSeries.coeff_sum, Finset.sum_eq_single (s % N).toNat]`. Establish `h0 : (((s % N).toNat : ℕ) : ℤ) = s % N` using `Int.toNat_of_nonneg (Int.emod_nonneg _ hN'.ne')`. Establish `h1 : (N : ℤ) ∣ s - s % N` using `Int.dvd_self_sub_emod`.

Rewrite using `[HahnSeries.coeff_single_mul, h0]`. Simplify using `[sh, h1]`. Introduce `i hi hne`. Establish `h1 : ¬ (N : ℤ) ∣ s - i`. Introduce `h`.

Establish `h2 : (i : ℤ) % N = s % N` using `(Int.modEq_iff_dvd).2 h`. Rewrite `h2` using `[Int.emod_eq_of_lt (by positivity) (by exact_mod_cast Finset.mem_range.1 hi)]`. Apply `hne` to reduce the goal to its premises. Rewrite using `[← h2]`. Simplify using the standard rewrite rules.

Rewrite using `[HahnSeries.coeff_single_mul]`. Simplify using `[sh, h1]`. Introduce `h`. It suffices to derive a contradiction. Apply `h` to reduce the goal to its premises.

Rewrite using `[Finset.mem_range]`. Use `Int.emod_lt_of_pos s hN'` as an intermediate fact. Use `Int.emod_nonneg s hN'.ne'` as an intermediate fact. Use linear arithmetic over natural numbers and integers.
-/
theorem decomp (N : ℕ) (hN : 0 < N) (b : Lau p) :
    b = ∑ i ∈ Finset.range N, HahnSeries.single (i : ℤ) (1 : ℤ_[p]) * sh N i (fun _ => 1) b := by
  ext s
  have hN' : (0 : ℤ) < N := by exact_mod_cast hN
  rw [HahnSeries.coeff_sum, Finset.sum_eq_single (s % N).toNat]
  · have h0 : (((s % N).toNat : ℕ) : ℤ) = s % N := Int.toNat_of_nonneg (Int.emod_nonneg _ hN'.ne')
    have h1 : (N : ℤ) ∣ s - s % N := Int.dvd_self_sub_emod
    rw [HahnSeries.coeff_single_mul, h0]
    simp [sh, h1]
  · intro i hi hne
    have h1 : ¬ (N : ℤ) ∣ s - i := by
      intro h
      have h2 : (i : ℤ) % N = s % N := (Int.modEq_iff_dvd).2 h
      rw [Int.emod_eq_of_lt (by positivity) (by exact_mod_cast Finset.mem_range.1 hi)] at h2
      apply hne
      rw [← h2]
      simp
    rw [HahnSeries.coeff_single_mul]
    simp [sh, h1]
  · intro h
    exfalso
    apply h
    rw [Finset.mem_range]
    have := Int.emod_lt_of_pos s hN'
    have := Int.emod_nonneg s hN'.ne'
    omega

/- English proof (translation)
Use extensionality with `s`. Rewrite using `[HahnSeries.coeff_add, coeff_natCast_mul, coeff_natCast_mul]`. Express the relevant statement in the definitionally equal form `(s : ℤ_[p]) * _ = _`. Simplify using `only [HahnSeries.coeff_single_mul, sh, one_mul]`. Use `split_ifs with h`.

Establish `h1 : (s : ℤ_[p]) = i + N * (((s - i) / N : ℤ) : ℤ_[p])`. Establish `h2 : s = i + N * ((s - i) / N)` using `by rw [Int.mul_ediv_cancel' h]; ring`. Conclude with `congrArg (Int.cast : ℤ → ℤ_[p]) h2` after adjusting the coercions. Rewrite using `[← mul_assoc, ← add_mul, ← h1]`. Simplify using the standard rewrite rules.
-/
theorem thL_part (N i : ℕ) (b : Lau p) :
    thL (HahnSeries.single (i : ℤ) (1 : ℤ_[p]) * sh N i (fun _ => 1) b) =
      (i : Lau p) * (HahnSeries.single (i : ℤ) (1 : ℤ_[p]) * sh N i (fun _ => 1) b) +
      (N : Lau p) * (HahnSeries.single (i : ℤ) (1 : ℤ_[p]) * sh N i (fun r => ((r / N : ℤ) : ℤ_[p])) b) := by
  ext s
  rw [HahnSeries.coeff_add, coeff_natCast_mul, coeff_natCast_mul]
  change (s : ℤ_[p]) * _ = _
  simp only [HahnSeries.coeff_single_mul, sh, one_mul]
  split_ifs with h
  · have h1 : (s : ℤ_[p]) = i + N * (((s - i) / N : ℤ) : ℤ_[p]) := by
      have h2 : s = i + N * ((s - i) / N) := by rw [Int.mul_ediv_cancel' h]; ring
      exact_mod_cast congrArg (Int.cast : ℤ → ℤ_[p]) h2
    rw [← mul_assoc, ← add_mul, ← h1]
  · simp

/- English proof (translation)
Rewrite using `[Derivation.leibniz, hβ, smul_zero, zero_add, add_smul, mul_comm (N : R), mul_smul γ, hN, smul_zero, add_zero, Derivation.leibniz_pow, ← Nat.cast_smul_eq_nsmul R, smul_smul, smul_smul, smul_smul, ← sub_smul]`. Break down `Nat.eq_zero_or_pos i with rfl | hi` into its components or cases. Simplify using the standard rewrite rules. Establish `h : q * β * i * q ^ (i - 1) - i * (q ^ i * β) = 0` using `by conv_lhs => rw [← mul_pow_sub_one hi.ne' q]`. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[h, zero_smul]`.
-/
theorem part_eq_zero {A R M : Type*} [CommRing A] [CommRing R] [Algebra A R] [AddCommGroup M] [Module R M] [Module A M]
    (D : Derivation A R M) (q β γ : R) (i N : ℕ) (hβ : D β = 0) (hN : (N : R) • D q = 0) :
    q • D (q ^ i * β) - ((i : R) * (q ^ i * β) + (N : R) * γ) • D q = 0 := by
  rw [Derivation.leibniz, hβ, smul_zero, zero_add, add_smul, mul_comm (N : R), mul_smul γ, hN, smul_zero, add_zero,
    Derivation.leibniz_pow, ← Nat.cast_smul_eq_nsmul R, smul_smul, smul_smul, smul_smul, ← sub_smul]
  rcases Nat.eq_zero_or_pos i with rfl | hi
  · simp
  · have h : q * β * i * q ^ (i - 1) - i * (q ^ i * β) = 0 := by
      conv_lhs => rw [← mul_pow_sub_one hi.ne' q]
      ring
    rw [h, zero_smul]

/- English proof (translation)
Introduce `p hp Ω _ _ T L ψ hψ b x y qL hx hy hq`. Establish `hqi : IsIntegral (O0 p) (T.qq L)` using `IsIntegral.of_pow (pow_pos hp.out.pos L) (by rw [Basic.qq_pow]; exact isIntegral_algebraMap)`. Establish `hmem : ∀ z, ψ z ∈ integralClosure (O0 p) Ω` using `fun z => by`. Establish `h1 : ψ z ∈ ψ.range` using `⟨z, rfl⟩`. Rewrite `h1` using `[hψ.rng]`.

Conclude with `adjoin_le_integralClosure hqi h1`. Take `⟨Ψ, hΨ⟩ : ∃ Ψ : Lau p →+* integralClosure (O0 p) Ω, ∀ c, (Ψ c : Ω) = ψ (algebraMap (Lau p) (O0 p) c)` from `⟨(ψ.codRestrict (integralClosure (O0 p) Ω) hmem).comp (algebraMap (Lau p) (O0 p)), fun _ => rfl⟩`. Establish `hx' : x = Ψ b` using `Subtype.ext (hx.trans (hΨ _).symm)`. Establish `hy' : y = Ψ (thL b)` using `Subtype.ext (hy.trans (hΨ _).symm)`. Rewrite using `[hx', hy']`.

Generalize the expression as in `KaehlerDifferential.D (O0 p) (integralClosure (O0 p) Ω) = D`. Establish `hN : 0 < p ^ L` using `pow_pos hp.out.pos L`. Establish `hqN : qL ^ p ^ L = algebraMap (O0 p) (integralClosure (O0 p) Ω) (qO p)` using `Subtype.ext (by rw [SubmonoidClass.coe_pow, hq, Basic.qq_pow]; rfl)`. Establish `hND : ((p ^ L : ℕ) : integralClosure (O0 p) Ω) • D qL = 0`. Establish `h1 : D (qL ^ p ^ L) = 0` using `by rw [hqN]; exact D.map_algebraMap _`.

Rewrite `h1` using `[Derivation.leibniz_pow]`. Establish `h2 : qL • ((p ^ L) • qL ^ (p ^ L - 1) • D qL) = 0` using `by rw [h1, smul_zero]`. Rewrite `h2` using `[← Nat.cast_smul_eq_nsmul (integralClosure (O0 p) Ω), smul_smul, smul_smul, mul_right_comm, mul_pow_sub_one hN.ne', hqN, mul_smul]`. Establish `hu : IsUnit (algebraMap (O0 p) (integralClosure (O0 p) Ω) (qO p))` using `(Basic.isUnit_qO p).map _`. Conclude with `hu.smul_left_cancel.1 (h2.trans (smul_zero _).symm)`.

Establish `hmono : ∀ i : ℕ, Ψ (HahnSeries.single (i : ℤ) (1 : ℤ_[p])) = qL ^ i`. Introduce `i`. Establish `h1 : (HahnSeries.single (i : ℤ) (1 : ℤ_[p]) : Lau p) = (HahnSeries.single (1 : ℤ) (1 : ℤ_[p])) ^ i`. Rewrite using `[HahnSeries.single_pow]`. Simplify using the standard rewrite rules.

Establish `h2 : Ψ (HahnSeries.single (1 : ℤ) (1 : ℤ_[p])) = qL` using `Subtype.ext (by rw [hΨ, hq]; exact hψ.par)`. Rewrite using `[h1, map_pow, h2]`. Establish `hsub : ∀ (i : ℤ), D (Ψ (sh (p ^ L) i (fun _ => 1) b)) = 0`. Introduce `i`. Establish `h1 : Ψ (sh (p ^ L) i (fun _ => 1) b) = algebraMap (O0 p) (integralClosure (O0 p) Ω) (algebraMap (Lau p) (O0 p) (dn (p ^ L) hN (sh (p ^ L) i (fun _ => 1) b)))`.

Apply `Subtype.ext` to reduce the goal to its premises. Rewrite using `[hΨ]`. Use `hψ.sub _ _ (fun j => ?_) (fun r hr => ?_)` and prove the remaining obligations. Simplify using `[dn]`. Establish `h2 : ¬ ((p ^ L : ℕ) : ℤ) ∣ r` using `by simpa using hr`.

Conclude with `if_neg h2`. Rewrite using `[h1]`. Conclude with `D.map_algebraMap _`. Set `E : Lau p →+ KaehlerDifferential (O0 p) (integralClosure (O0 p) Ω)` to `{ toFun := fun c => qL • D (Ψ c) - Ψ (thL c) • D qL map_zero' := by simp [thL_zero] map_add' := by`. Introduce `a c`.

Simplify using `only [thL_add, map_add, add_smul, smul_add]`. Use `abel }`. Establish `hpart : ∀ i ∈ Finset.range (p ^ L), E (HahnSeries.single (i : ℤ) (1 : ℤ_[p]) * sh (p ^ L) i (fun _ => 1) b) = 0`. Introduce `i _`. Express the relevant statement in the definitionally equal form `qL • D (Ψ _) - Ψ (thL _) • D qL = 0`.

Rewrite using `[thL_part, map_add Ψ, map_mul Ψ (i : Lau p), map_mul Ψ ((p ^ L : ℕ) : Lau p), map_mul Ψ, map_natCast Ψ, map_natCast Ψ, hmono]`. Conclude with `part_eq_zero D qL _ _ i (p ^ L) (hsub i) hND`. Establish `hE : E b = 0`. Rewrite using `[decomp (p ^ L) hN b, map_sum]`. Conclude with `Finset.sum_eq_zero hpart`.

Conclude with `sub_eq_zero.1 hE`.
-/
theorem smul_D_psi : ∀ (p : ℕ) [Fact p.Prime] (Ω : Type) [Field Ω] [Algebra (O0 p) Ω] (T : Tower p Ω) (L : ℕ) (ψ : O0 p →+* Ω), IsReb T L ψ → ∀ (b : Lau p) (x y qL : integralClosure (O0 p) Ω), (x : Ω) = ψ (algebraMap (Lau p) (O0 p) b) → (y : Ω) = ψ (algebraMap (Lau p) (O0 p) (thL b)) → (qL : Ω) = T.qq L → qL • KaehlerDifferential.D (O0 p) (integralClosure (O0 p) Ω) x = y • KaehlerDifferential.D (O0 p) (integralClosure (O0 p) Ω) qL := by
  intro p hp Ω _ _ T L ψ hψ b x y qL hx hy hq
  have hqi : IsIntegral (O0 p) (T.qq L) :=
    IsIntegral.of_pow (pow_pos hp.out.pos L) (by rw [Basic.qq_pow]; exact isIntegral_algebraMap)
  have hmem : ∀ z, ψ z ∈ integralClosure (O0 p) Ω := fun z => by
    have h1 : ψ z ∈ ψ.range := ⟨z, rfl⟩
    rw [hψ.rng] at h1
    exact adjoin_le_integralClosure hqi h1
  obtain ⟨Ψ, hΨ⟩ : ∃ Ψ : Lau p →+* integralClosure (O0 p) Ω, ∀ c, (Ψ c : Ω) = ψ (algebraMap (Lau p) (O0 p) c) :=
    ⟨(ψ.codRestrict (integralClosure (O0 p) Ω) hmem).comp (algebraMap (Lau p) (O0 p)), fun _ => rfl⟩
  have hx' : x = Ψ b := Subtype.ext (hx.trans (hΨ _).symm)
  have hy' : y = Ψ (thL b) := Subtype.ext (hy.trans (hΨ _).symm)
  rw [hx', hy']
  generalize KaehlerDifferential.D (O0 p) (integralClosure (O0 p) Ω) = D
  have hN : 0 < p ^ L := pow_pos hp.out.pos L
  have hqN : qL ^ p ^ L = algebraMap (O0 p) (integralClosure (O0 p) Ω) (qO p) :=
    Subtype.ext (by rw [SubmonoidClass.coe_pow, hq, Basic.qq_pow]; rfl)
  have hND : ((p ^ L : ℕ) : integralClosure (O0 p) Ω) • D qL = 0 := by
    have h1 : D (qL ^ p ^ L) = 0 := by rw [hqN]; exact D.map_algebraMap _
    rw [Derivation.leibniz_pow] at h1
    have h2 : qL • ((p ^ L) • qL ^ (p ^ L - 1) • D qL) = 0 := by rw [h1, smul_zero]
    rw [← Nat.cast_smul_eq_nsmul (integralClosure (O0 p) Ω), smul_smul, smul_smul, mul_right_comm,
      mul_pow_sub_one hN.ne', hqN, mul_smul] at h2
    have hu : IsUnit (algebraMap (O0 p) (integralClosure (O0 p) Ω) (qO p)) := (Basic.isUnit_qO p).map _
    exact hu.smul_left_cancel.1 (h2.trans (smul_zero _).symm)
  have hmono : ∀ i : ℕ, Ψ (HahnSeries.single (i : ℤ) (1 : ℤ_[p])) = qL ^ i := by
    intro i
    have h1 : (HahnSeries.single (i : ℤ) (1 : ℤ_[p]) : Lau p) = (HahnSeries.single (1 : ℤ) (1 : ℤ_[p])) ^ i := by
      rw [HahnSeries.single_pow]; simp
    have h2 : Ψ (HahnSeries.single (1 : ℤ) (1 : ℤ_[p])) = qL :=
      Subtype.ext (by rw [hΨ, hq]; exact hψ.par)
    rw [h1, map_pow, h2]
  have hsub : ∀ (i : ℤ), D (Ψ (sh (p ^ L) i (fun _ => 1) b)) = 0 := by
    intro i
    have h1 : Ψ (sh (p ^ L) i (fun _ => 1) b) = algebraMap (O0 p) (integralClosure (O0 p) Ω)
        (algebraMap (Lau p) (O0 p) (dn (p ^ L) hN (sh (p ^ L) i (fun _ => 1) b))) := by
      apply Subtype.ext
      rw [hΨ]
      refine hψ.sub _ _ (fun j => ?_) (fun r hr => ?_)
      · simp [dn]
      · have h2 : ¬ ((p ^ L : ℕ) : ℤ) ∣ r := by simpa using hr
        exact if_neg h2
    rw [h1]
    exact D.map_algebraMap _
  let E : Lau p →+ KaehlerDifferential (O0 p) (integralClosure (O0 p) Ω) :=
    { toFun := fun c => qL • D (Ψ c) - Ψ (thL c) • D qL
      map_zero' := by simp [thL_zero]
      map_add' := by
        intro a c
        simp only [thL_add, map_add, add_smul, smul_add]
        abel }
  have hpart : ∀ i ∈ Finset.range (p ^ L),
      E (HahnSeries.single (i : ℤ) (1 : ℤ_[p]) * sh (p ^ L) i (fun _ => 1) b) = 0 := by
    intro i _
    change qL • D (Ψ _) - Ψ (thL _) • D qL = 0
    rw [thL_part, map_add Ψ, map_mul Ψ (i : Lau p), map_mul Ψ ((p ^ L : ℕ) : Lau p), map_mul Ψ, map_natCast Ψ, map_natCast Ψ, hmono]
    exact part_eq_zero D qL _ _ i (p ^ L) (hsub i) hND
  have hE : E b = 0 := by
    rw [decomp (p ^ L) hN b, map_sum]
    exact Finset.sum_eq_zero hpart
  exact sub_eq_zero.1 hE

end GlobalTheory.Glue.DPsi

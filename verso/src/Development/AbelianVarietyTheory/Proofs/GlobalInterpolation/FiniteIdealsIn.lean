import Mathlib
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.LamIdealOfNotPrimePow
open Complex ArithmeticFunction MeasureTheory Filter Topology NumberField GlobalTheory.Hk GlobalTheory.Mem
open scoped Classical

namespace GlobalTheory.Hk.RayConv

variable {K : Type} [Field K] [NumberField K]

/- English proof (translation)
Establish `h1 : P.IsPrime` using `Ideal.isPrime_of_prime hP`. Unfold `lamIdeal`. Rewrite using `[if_pos ⟨P, k + 1, h1, hP.ne_zero, by omega, rfl⟩, Ideal.radical_pow _ (by omega), h1.radical]`.
-/
theorem lamIdeal_pow {P : Ideal (𝓞 K)} (hP : Prime P) (k : ℕ) :
    lamIdeal (P ^ (k + 1)) = Real.log (Ideal.absNorm P) := by
  have h1 : P.IsPrime := Ideal.isPrime_of_prime hP
  unfold lamIdeal
  rw [if_pos ⟨P, k + 1, h1, hP.ne_zero, by omega, rfl⟩, Ideal.radical_pow _ (by omega), h1.radical]

/- English proof (translation)
Use `(Ideal.finite_setOf_absNorm_le (S := 𝓞 K) (Ideal.absNorm I)).subset fun J hJ => ?_` and prove the remaining obligations. Conclude with `Nat.le_of_dvd (Nat.pos_of_ne_zero fun h => hI (Ideal.absNorm_eq_zero_iff.1 h)) (map_dvd _ hJ)`.
-/
theorem finite_dvd {I : Ideal (𝓞 K)} (hI : I ≠ 0) : {J : Ideal (𝓞 K) | J ∣ I}.Finite := by
  refine (Ideal.finite_setOf_absNorm_le (S := 𝓞 K) (Ideal.absNorm I)).subset fun J hJ => ?_
  exact Nat.le_of_dvd (Nat.pos_of_ne_zero fun h => hI (Ideal.absNorm_eq_zero_iff.1 h)) (map_dvd _ hJ)

/- English proof (translation)
Proceed by induction on `I using UniqueFactorizationMonoid.induction_on_prime with`. Consider the case `h₁ => intro h`. Conclude with `(h rfl).elim`. Consider the case `h₂ I hu`. Introduce `_ T hT`.

Establish `h1 : I = 1` using `isUnit_iff_eq_one.1 hu`. Substitute `h1` using the available equality. Rewrite using `[map_one, Nat.cast_one, Real.log_one]`. Use `Finset.sum_eq_zero fun J hJ => ?_` and prove the remaining obligations. Unfold `lamIdeal`.

Rewrite using `[if_neg]`. Introduce and unpack `⟨P, k, hP, hP0, hk, rfl⟩`. Use `isUnit_of_dvd_one ((hT _).1 hJ)` as an intermediate fact. Rewrite `this` using `[isUnit_pow_iff (by omega), Ideal.isUnit_iff]`. Conclude with `hP.ne_top this`.

Consider the case `h₃ I P hI hP ih`. Introduce `_ T hT`. Use `set S := (finite_dvd hI).toFinset with hS`. Establish `hSm : ∀ J, J ∈ S ↔ J ∣ I` using `fun J => by simp [hS]`. Establish `hsub : S ⊆ T` using `fun J hJ => (hT J).2 (((hSm J).1 hJ).mul_left P)`.

Establish `hfin : FiniteMultiplicity P I` using `FiniteMultiplicity.of_prime_left hP hI`. Establish `hN : ∀ J : Ideal (𝓞 K), J ≠ 0 → ((Ideal.absNorm J : ℕ) : ℝ) ≠ 0` using `fun J hJ => Nat.cast_ne_zero.2 fun h => hJ (Ideal.absNorm_eq_zero_iff.1 h)`. Rewrite using `[← Finset.sum_sdiff hsub, ih hI S hSm, map_mul, Nat.cast_mul, Real.log_mul (hN _ hP.ne_zero) (hN _ hI)]`. Use `congr 1`. Rewrite using `[Finset.sum_eq_single_of_mem (P ^ (multiplicity P I + 1)), lamIdeal_pow hP]`.

Rewrite using `[Finset.mem_sdiff, hT, hSm]`. Use `⟨?_, hfin.not_pow_dvd_of_multiplicity_lt (Nat.lt_succ_self _)⟩` and prove the remaining obligations. Rewrite using `[pow_succ']`. Conclude with `mul_dvd_mul_left _ (pow_multiplicity_dvd _ _)`. Introduce `J hJ hne`.

Rewrite `hJ` using `[Finset.mem_sdiff, hT, hSm]`. Unfold `lamIdeal`. Rewrite using `[if_neg]`. Introduce and unpack `⟨Q, k, hQ, hQ0, hk, rfl⟩`. Establish `hQp : Prime Q` using `Ideal.prime_of_isPrime hQ0 hQ`.

Distinguish the cases in `hQP : Q = P`. Substitute `hQP` using the available equality. Take `⟨j, rfl⟩ : ∃ j, k = j + 1` from `⟨k - 1, by omega⟩`. Establish `h1 : Q ^ j ∣ I`. Use `hJ.1` as an intermediate fact.

Rewrite `this` using `[pow_succ']`. Conclude with `(mul_dvd_mul_iff_left hP.ne_zero).1 this`. Establish `h2 : j ≤ multiplicity Q I` using `hfin.le_multiplicity_of_pow_dvd h1`. Establish `h3 : ¬ j + 1 ≤ multiplicity Q I` using `fun h => hJ.2 (pow_dvd_of_le_multiplicity h)`. Conclude with `hne (by rw [show j = multiplicity Q I by omega])`.

Use `hJ.2 (hQp.pow_dvd_of_dvd_mul_left k ?_ hJ.1)` and prove the remaining obligations. Introduce `hd`. Conclude with `hQP (associated_iff_eq.1 ((hQp.dvd_prime_iff_associated hP).1 hd))`.
-/
theorem sum_lamIdeal (I : Ideal (𝓞 K)) : I ≠ 0 → ∀ T : Finset (Ideal (𝓞 K)), (∀ J, J ∈ T ↔ J ∣ I) →
    ∑ J ∈ T, lamIdeal J = Real.log (Ideal.absNorm I) := by
  induction I using UniqueFactorizationMonoid.induction_on_prime with
  | h₁ => intro h; exact (h rfl).elim
  | h₂ I hu =>
    intro _ T hT
    have h1 : I = 1 := isUnit_iff_eq_one.1 hu
    subst h1
    rw [map_one, Nat.cast_one, Real.log_one]
    refine Finset.sum_eq_zero fun J hJ => ?_
    unfold lamIdeal
    rw [if_neg]
    rintro ⟨P, k, hP, hP0, hk, rfl⟩
    have := isUnit_of_dvd_one ((hT _).1 hJ)
    rw [isUnit_pow_iff (by omega), Ideal.isUnit_iff] at this
    exact hP.ne_top this
  | h₃ I P hI hP ih =>
    intro _ T hT
    set S := (finite_dvd hI).toFinset with hS
    have hSm : ∀ J, J ∈ S ↔ J ∣ I := fun J => by simp [hS]
    have hsub : S ⊆ T := fun J hJ => (hT J).2 (((hSm J).1 hJ).mul_left P)
    have hfin : FiniteMultiplicity P I := FiniteMultiplicity.of_prime_left hP hI
    have hN : ∀ J : Ideal (𝓞 K), J ≠ 0 → ((Ideal.absNorm J : ℕ) : ℝ) ≠ 0 := fun J hJ =>
      Nat.cast_ne_zero.2 fun h => hJ (Ideal.absNorm_eq_zero_iff.1 h)
    rw [← Finset.sum_sdiff hsub, ih hI S hSm, map_mul, Nat.cast_mul, Real.log_mul (hN _ hP.ne_zero) (hN _ hI)]
    congr 1
    rw [Finset.sum_eq_single_of_mem (P ^ (multiplicity P I + 1)), lamIdeal_pow hP]
    · rw [Finset.mem_sdiff, hT, hSm]
      refine ⟨?_, hfin.not_pow_dvd_of_multiplicity_lt (Nat.lt_succ_self _)⟩
      rw [pow_succ']
      exact mul_dvd_mul_left _ (pow_multiplicity_dvd _ _)
    · intro J hJ hne
      rw [Finset.mem_sdiff, hT, hSm] at hJ
      unfold lamIdeal
      rw [if_neg]
      rintro ⟨Q, k, hQ, hQ0, hk, rfl⟩
      have hQp : Prime Q := Ideal.prime_of_isPrime hQ0 hQ
      by_cases hQP : Q = P
      · subst hQP
        obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
        have h1 : Q ^ j ∣ I := by
          have := hJ.1
          rw [pow_succ'] at this
          exact (mul_dvd_mul_iff_left hP.ne_zero).1 this
        have h2 : j ≤ multiplicity Q I := hfin.le_multiplicity_of_pow_dvd h1
        have h3 : ¬ j + 1 ≤ multiplicity Q I := fun h => hJ.2 (pow_dvd_of_le_multiplicity h)
        exact hne (by rw [show j = multiplicity Q I by omega])
      · refine hJ.2 (hQp.pow_dvd_of_dvd_mul_left k ?_ hJ.1)
        intro hd
        exact hQP (associated_iff_eq.1 ((hQp.dvd_prime_iff_associated hP).1 hd))

variable {M : ℕ} (D : RayData K M)

/- English proof (translation)
The claim follows from `(Ideal.finite_setOf_absNorm_eq (S := 𝓞 K) n).subset fun _ h => h.2.2.1`.
-/
theorem finite_idealsIn (g : D.G) (n : ℕ) : (idealsIn D g n).Finite :=
  (Ideal.finite_setOf_absNorm_eq (S := 𝓞 K) n).subset fun _ h => h.2.2.1

end GlobalTheory.Hk.RayConv

namespace GlobalTheory.Hk

open RayConv in

/- English proof (translation)
Introduce `K _ _ M _ D g n`. Set `F : D.G → ℕ → Finset (Ideal (𝓞 K))` to `fun g n => (finite_idealsIn D g n).toFinset`. Establish `hF : ∀ g n I, I ∈ F g n ↔ I ≠ ⊥ ∧ IsCoprime I (Ideal.span {(M : 𝓞 K)}) ∧ Ideal.absNorm I = n ∧ D.cls I = g` using `fun g n I => by simp [F, idealsIn]`. Establish `ha : ∀ g n, aRay D g n = (F g n).card` using `fun g n => by`. Unfold `aRay`.

Rewrite using `[Set.ncard_eq_toFinset_card _ (finite_idealsIn D g n)]`. Establish `hl : ∀ g n, lamRay D g n = ∑ I ∈ F g n, lamIdeal I` using `fun g n => by`. Unfold `lamRay`. Rewrite using `[finsum_mem_eq_finite_toFinset_sum _ (finite_idealsIn D g n)]`. Set `T : Ideal (𝓞 K) → Finset (Ideal (𝓞 K))` to `fun I => if h : I = 0 then ∅ else (finite_dvd h).toFinset`.

Establish `hT : ∀ I, I ≠ 0 → ∀ J, J ∈ T I ↔ J ∣ I` using `fun I hI J => by`. Simplify using `only [T]`. Rewrite using `[dif_neg hI]`. Simplify using the standard rewrite rules. Establish `L : aRay D g n * Real.log n = ∑ I ∈ F g n, ∑ J ∈ T I, lamIdeal J`.

Rewrite using `[ha, ← nsmul_eq_mul, ← Finset.sum_const]`. Use `Finset.sum_congr rfl fun I hI => ?_` and prove the remaining obligations. Use `(hF _ _ _).1 hI` as an intermediate fact. Rewrite using `[sum_lamIdeal I this.1 _ (hT I this.1), this.2.2.1]`. Establish `R : ∀ h (p : ℕ × ℕ), lamRay D h p.1 * aRay D (g / h) p.2 = ∑ q ∈ F h p.1 ×ˢ F (g / h) p.2, lamIdeal q.1` using `fun h p => by`.

Rewrite using `[hl, ha, Finset.sum_product, Finset.sum_mul]`. Use `Finset.sum_congr rfl fun I _ => ?_` and prove the remaining obligations. Simplify using `[mul_comm]`. Simplify using `only [R]`. Rewrite using `[L, Finset.sum_sigma', Finset.sum_sigma', Finset.sum_sigma']`.

Use `symm`. Use `Finset.sum_bij (fun x _ => ⟨x.2.1 * x.2.2, x.2.1⟩) ?_ ?_ ?_ ?_` and prove the remaining obligations. Introduce and unpack `⟨⟨h, p⟩, I, J⟩ hx`. Simplify using `only [Finset.mem_sigma, Finset.mem_product, hF, Nat.mem_divisorsAntidiagonal] at hx ⊢`. Take `⟨⟨-, hp, -⟩, ⟨a1, a2, a3, a4⟩, b1, b2, b3, b4⟩` from `hx`.

Use `⟨⟨mul_ne_zero a1 b1, a2.mul_left b2, by rw [map_mul, a3, b3, hp], ?_⟩, (hT _ (mul_ne_zero a1 b1) _).2 (dvd_mul_right _ _)⟩` and prove the remaining obligations. Rewrite using `[D.cls_mul I J a2 b2 a1 b1, a4, b4, mul_div_cancel]`. Introduce and unpack `⟨⟨h, p, p'⟩, I, J⟩ hx ⟨⟨h', q, q'⟩, I', J'⟩ hy hxy`. Simplify using `only [Finset.mem_sigma, Finset.mem_product, hF, Nat.mem_divisorsAntidiagonal] at hx hy`. Take `⟨⟨-, hp, -⟩, ⟨a1, a2, a3, a4⟩, b1, b2, b3, b4⟩` from `hx`.

Take `⟨⟨-, hq, -⟩, ⟨c1, c2, c3, c4⟩, d1, d2, d3, d4⟩` from `hy`. Simplify using `only [Sigma.mk.injEq, heq_eq_eq] at hxy`. Take `⟨e1, rfl⟩` from `hxy`. Take `rfl : J = J'` from `mul_left_cancel₀ a1 e1`. Substitute `a3 b3 a4 c3 d3 c4` using the available equality.

Both sides reduce to the same expression. Introduce and unpack `⟨I, J⟩ hx`. Simplify using `only [Finset.mem_sigma, hF] at hx`. Take `⟨⟨a1, a2, a3, a4⟩, hJ⟩` from `hx`. Take `⟨J', rfl⟩` from `(hT _ a1 _).1 hJ`.

Establish `j1 : J ≠ ⊥` using `left_ne_zero_of_mul a1`. Establish `j2 : J' ≠ ⊥` using `right_ne_zero_of_mul a1`. Use `⟨⟨⟨D.cls J, Ideal.absNorm J, Ideal.absNorm J'⟩, J, J'⟩, ?_, rfl⟩` and prove the remaining obligations. Simplify using `only [Finset.mem_sigma, Finset.mem_product, hF, Nat.mem_divisorsAntidiagonal, Finset.mem_univ, true_and, and_true]`. Use `⟨⟨by rw [← map_mul, a3], ?_⟩, ⟨j1, a2.of_mul_left_left⟩, j2, a2.of_mul_left_right, ?_⟩` and prove the remaining obligations.

Rewrite using `[← a3]`. Conclude with `fun h => a1 (Ideal.absNorm_eq_zero_iff.1 h)`. Rewrite using `[← a4, D.cls_mul J J' a2.of_mul_left_left a2.of_mul_left_right j1 j2, mul_div_cancel_left]`. Introduce `x _`. Both sides reduce to the same expression.
-/
theorem aRay_mul_log : ∀ (K : Type) [Field K] [NumberField K] (M : ℕ), 2 ≤ M → ∀ (D : RayData K M) (g : D.G) (n : ℕ), aRay D g n * Real.log n = ∑ h : D.G, ∑ p ∈ n.divisorsAntidiagonal, lamRay D h p.1 * aRay D (g / h) p.2 := by
  intro K _ _ M _ D g n
  let F : D.G → ℕ → Finset (Ideal (𝓞 K)) := fun g n => (finite_idealsIn D g n).toFinset
  have hF : ∀ g n I, I ∈ F g n ↔ I ≠ ⊥ ∧ IsCoprime I (Ideal.span {(M : 𝓞 K)}) ∧ Ideal.absNorm I = n ∧ D.cls I = g :=
    fun g n I => by simp [F, idealsIn]
  have ha : ∀ g n, aRay D g n = (F g n).card := fun g n => by
    unfold aRay; rw [Set.ncard_eq_toFinset_card _ (finite_idealsIn D g n)]
  have hl : ∀ g n, lamRay D g n = ∑ I ∈ F g n, lamIdeal I := fun g n => by
    unfold lamRay; rw [finsum_mem_eq_finite_toFinset_sum _ (finite_idealsIn D g n)]
  let T : Ideal (𝓞 K) → Finset (Ideal (𝓞 K)) := fun I => if h : I = 0 then ∅ else (finite_dvd h).toFinset
  have hT : ∀ I, I ≠ 0 → ∀ J, J ∈ T I ↔ J ∣ I := fun I hI J => by
    simp only [T]; rw [dif_neg hI]; simp
  have L : aRay D g n * Real.log n = ∑ I ∈ F g n, ∑ J ∈ T I, lamIdeal J := by
    rw [ha, ← nsmul_eq_mul, ← Finset.sum_const]
    refine Finset.sum_congr rfl fun I hI => ?_
    have := (hF _ _ _).1 hI
    rw [sum_lamIdeal I this.1 _ (hT I this.1), this.2.2.1]
  have R : ∀ h (p : ℕ × ℕ), lamRay D h p.1 * aRay D (g / h) p.2 =
      ∑ q ∈ F h p.1 ×ˢ F (g / h) p.2, lamIdeal q.1 := fun h p => by
    rw [hl, ha, Finset.sum_product, Finset.sum_mul]
    refine Finset.sum_congr rfl fun I _ => ?_
    simp [mul_comm]
  simp only [R]
  rw [L, Finset.sum_sigma', Finset.sum_sigma', Finset.sum_sigma']
  symm
  refine Finset.sum_bij (fun x _ => ⟨x.2.1 * x.2.2, x.2.1⟩) ?_ ?_ ?_ ?_
  · rintro ⟨⟨h, p⟩, I, J⟩ hx
    simp only [Finset.mem_sigma, Finset.mem_product, hF, Nat.mem_divisorsAntidiagonal] at hx ⊢
    obtain ⟨⟨-, hp, -⟩, ⟨a1, a2, a3, a4⟩, b1, b2, b3, b4⟩ := hx
    refine ⟨⟨mul_ne_zero a1 b1, a2.mul_left b2, by rw [map_mul, a3, b3, hp], ?_⟩,
      (hT _ (mul_ne_zero a1 b1) _).2 (dvd_mul_right _ _)⟩
    rw [D.cls_mul I J a2 b2 a1 b1, a4, b4, mul_div_cancel]
  · rintro ⟨⟨h, p, p'⟩, I, J⟩ hx ⟨⟨h', q, q'⟩, I', J'⟩ hy hxy
    simp only [Finset.mem_sigma, Finset.mem_product, hF, Nat.mem_divisorsAntidiagonal] at hx hy
    obtain ⟨⟨-, hp, -⟩, ⟨a1, a2, a3, a4⟩, b1, b2, b3, b4⟩ := hx
    obtain ⟨⟨-, hq, -⟩, ⟨c1, c2, c3, c4⟩, d1, d2, d3, d4⟩ := hy
    simp only [Sigma.mk.injEq, heq_eq_eq] at hxy
    obtain ⟨e1, rfl⟩ := hxy
    obtain rfl : J = J' := mul_left_cancel₀ a1 e1
    subst a3 b3 a4 c3 d3 c4
    rfl
  · rintro ⟨I, J⟩ hx
    simp only [Finset.mem_sigma, hF] at hx
    obtain ⟨⟨a1, a2, a3, a4⟩, hJ⟩ := hx
    obtain ⟨J', rfl⟩ := (hT _ a1 _).1 hJ
    have j1 : J ≠ ⊥ := left_ne_zero_of_mul a1
    have j2 : J' ≠ ⊥ := right_ne_zero_of_mul a1
    refine ⟨⟨⟨D.cls J, Ideal.absNorm J, Ideal.absNorm J'⟩, J, J'⟩, ?_, rfl⟩
    simp only [Finset.mem_sigma, Finset.mem_product, hF, Nat.mem_divisorsAntidiagonal, Finset.mem_univ, true_and, and_true]
    refine ⟨⟨by rw [← map_mul, a3], ?_⟩, ⟨j1, a2.of_mul_left_left⟩, j2, a2.of_mul_left_right, ?_⟩
    · rw [← a3]; exact fun h => a1 (Ideal.absNorm_eq_zero_iff.1 h)
    · rw [← a4, D.cls_mul J J' a2.of_mul_left_left a2.of_mul_left_right j1 j2, mul_div_cancel_left]
  · intro x _; rfl

end GlobalTheory.Hk

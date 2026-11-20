import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.OneAddXMulDerivativeBin
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DvdSubOfDvdSubX

noncomputable section

open PowerSeries GlobalTheory.CycFr

namespace GlobalTheory.CycFr.Red

def lvlPoly (l : ℕ) (R : Type) [CommRing R] (k : ℕ) : Polynomial R :=
  ∑ i ∈ Finset.range l, ((1 + Polynomial.X : Polynomial R) ^ l ^ k) ^ i

variable {l : ℕ} {R S : Type} [CommRing R] [CommRing S]

/- English proof (translation)
Use `map_sum (Polynomial.coeToPowerSeries.ringHom (R := R)) (fun i => ((1 + Polynomial.X : Polynomial R) ^ l ^ k) ^ i) (Finset.range l)` as an intermediate fact. Rewrite `this` using `[Polynomial.coeToPowerSeries.ringHom_apply]`. Rewrite using `[lvlPoly, this, lvl]`. Simplify using the standard rewrite rules.
-/
theorem lvlPoly_coe (k : ℕ) : ((lvlPoly l R k : Polynomial R) : R⟦X⟧) = lvl l R k := by
  have := map_sum (Polynomial.coeToPowerSeries.ringHom (R := R))
    (fun i => ((1 + Polynomial.X : Polynomial R) ^ l ^ k) ^ i) (Finset.range l)
  rw [Polynomial.coeToPowerSeries.ringHom_apply] at this
  rw [lvlPoly, this, lvl]
  simp

/- English proof (translation)
Simplify using `[lvlPoly, Polynomial.map_sum]`.
-/
theorem lvlPoly_map (j : R →+* S) (k : ℕ) : (lvlPoly l R k).map j = lvlPoly l S k := by
  simp [lvlPoly, Polynomial.map_sum]

/- English proof (translation)
Rewrite using `[lvlPoly, geom_sum_mul, ← pow_mul, pow_succ]`.
-/
theorem lvlPoly_mul (k : ℕ) :
    lvlPoly l R k * ((1 + Polynomial.X) ^ l ^ k - 1) = (1 + Polynomial.X) ^ l ^ (k + 1) - 1 := by
  rw [lvlPoly, geom_sum_mul, ← pow_mul, pow_succ]

/- English proof (translation)
Establish `h : lvlPoly l R k = (Polynomial.cyclotomic (l ^ (k + 1)) R).comp (Polynomial.X + Polynomial.C 1)`. Rewrite using `[Polynomial.cyclotomic_prime_pow_eq_geom_sum hl.out, lvlPoly]`. Simplify using `[Polynomial.sum_comp, add_comm]`. Rewrite using `[h]`. Conclude with `(Polynomial.cyclotomic.monic _ _).comp_X_add_C _`.
-/
theorem lvlPoly_monic [Nontrivial R] [hl : Fact l.Prime] (k : ℕ) : (lvlPoly l R k).Monic := by
  have h : lvlPoly l R k =
      (Polynomial.cyclotomic (l ^ (k + 1)) R).comp (Polynomial.X + Polynomial.C 1) := by
    rw [Polynomial.cyclotomic_prime_pow_eq_geom_sum hl.out, lvlPoly]
    simp [Polynomial.sum_comp, add_comm]
  rw [h]
  exact (Polynomial.cyclotomic.monic _ _).comp_X_add_C _

/- English proof (translation)
Establish `h` using `lvlPoly_mul (l := l) (R := F) k`. Rewrite `h` using `[add_pow_char_pow, add_pow_char_pow, one_pow, one_pow, add_sub_cancel_left, add_sub_cancel_left]`. Establish `hle : l ^ k ≤ l ^ (k + 1)` using `Nat.pow_le_pow_right hl.out.pos (Nat.le_succ k)`. Apply `mul_right_cancel₀ (pow_ne_zero (l ^ k) Polynomial.X_ne_zero)` to reduce the goal to its premises. Rewrite using `[h, ← pow_add, Nat.sub_add_cancel hle]`.
-/
theorem lvlPoly_charP {F : Type} [Field F] [hl : Fact l.Prime] [CharP F l] (k : ℕ) :
    lvlPoly l F k = Polynomial.X ^ (l ^ (k + 1) - l ^ k) := by
  have h := lvlPoly_mul (l := l) (R := F) k
  rw [add_pow_char_pow, add_pow_char_pow, one_pow, one_pow, add_sub_cancel_left,
    add_sub_cancel_left] at h
  have hle : l ^ k ≤ l ^ (k + 1) := Nat.pow_le_pow_right hl.out.pos (Nat.le_succ k)
  apply mul_right_cancel₀ (pow_ne_zero (l ^ k) Polynomial.X_ne_zero)
  rw [h, ← pow_add, Nat.sub_add_cancel hle]

/- English proof (translation)
Use `⟨⟨fun {n} hn => ?_⟩, lvlPoly_monic k⟩` and prove the remaining obligations. Establish `h0 : (l : IsLocalRing.ResidueField R) = 0`. Rewrite using `[← map_natCast (IsLocalRing.residue R), IsLocalRing.residue_eq_zero_iff]`. Conclude with `h`. Use `haveI : CharP (IsLocalRing.ResidueField R) l := (CharP.charP_iff_prime_eq_zero hl.out).2 h0`.

Establish `h1` using `lvlPoly_map (l := l) (IsLocalRing.residue R) k`. Rewrite `h1` using `[lvlPoly_charP]`. Establish `h2 : (lvlPoly l R k).natDegree = l ^ (k + 1) - l ^ k`. Rewrite using `[← (lvlPoly_monic (l := l) (R := R) k).natDegree_map (IsLocalRing.residue R), h1, Polynomial.natDegree_X_pow]`. Establish `h3` using `congrArg (fun p => Polynomial.coeff p n) h1`.

Rewrite `hn` using `[h2]`. Simplify using `only [Polynomial.coeff_map, Polynomial.coeff_X_pow, hn.ne, if_false] at h3`. Conclude with `(IsLocalRing.residue_eq_zero_iff _).1 h3`.
-/
theorem lvlPoly_distinguished [hl : Fact l.Prime] [IsLocalRing R] (h : ¬ IsUnit (l : R)) (k : ℕ) :
    (lvlPoly l R k).IsDistinguishedAt (IsLocalRing.maximalIdeal R) := by
  refine ⟨⟨fun {n} hn => ?_⟩, lvlPoly_monic k⟩
  have h0 : (l : IsLocalRing.ResidueField R) = 0 := by
    rw [← map_natCast (IsLocalRing.residue R), IsLocalRing.residue_eq_zero_iff]; exact h
  haveI : CharP (IsLocalRing.ResidueField R) l := (CharP.charP_iff_prime_eq_zero hl.out).2 h0
  have h1 := lvlPoly_map (l := l) (IsLocalRing.residue R) k
  rw [lvlPoly_charP] at h1
  have h2 : (lvlPoly l R k).natDegree = l ^ (k + 1) - l ^ k := by
    rw [← (lvlPoly_monic (l := l) (R := R) k).natDegree_map (IsLocalRing.residue R), h1,
      Polynomial.natDegree_X_pow]
  have h3 := congrArg (fun p => Polynomial.coeff p n) h1
  rw [h2] at hn
  simp only [Polynomial.coeff_map, Polynomial.coeff_X_pow, hn.ne, if_false] at h3
  exact (IsLocalRing.residue_eq_zero_iff _).1 h3

/- English proof (translation)
Establish `hN : 0 < l ^ (k + 1)` using `pow_pos hl.out.pos _`. Establish `hs : ((1 + Polynomial.X : Polynomial K) ^ l ^ (k + 1) - 1).Separable`. Take `⟨M, hM⟩ : ∃ M, l ^ (k + 1) = M + 1` from `⟨_, (Nat.succ_pred_eq_of_pos hN).symm⟩`. Rewrite using `[hM, Polynomial.separable_def']`. Establish `hc : ((M : K) + 1) ≠ 0` using `by exact_mod_cast Nat.succ_ne_zero M`.

Use `⟨-1, Polynomial.C ((M : K) + 1)⁻¹ * (1 + Polynomial.X), ?_⟩` and prove the remaining obligations. Establish `e : Polynomial.C ((M : K) + 1)⁻¹ * Polynomial.C ((M : K) + 1) = 1`. Rewrite using `[← map_mul, inv_mul_cancel₀ hc, map_one]`. Simplify using `only [Polynomial.derivative_sub, Polynomial.derivative_one, Polynomial.derivative_pow_succ, Polynomial.derivative_add, Polynomial.derivative_X, zero_add, mul_one, sub_zero]`. Take the linear combination `((1 + Polynomial.X : Polynomial K) ^ (M + 1)) * e`.

Rewrite `hs` using `[← lvlPoly_mul]`. Conclude with `hs.of_mul_left`.
-/
theorem lvlPoly_separable {K : Type} [Field K] [CharZero K] [hl : Fact l.Prime] (k : ℕ) :
    (lvlPoly l K k).Separable := by
  have hN : 0 < l ^ (k + 1) := pow_pos hl.out.pos _
  have hs : ((1 + Polynomial.X : Polynomial K) ^ l ^ (k + 1) - 1).Separable := by
    obtain ⟨M, hM⟩ : ∃ M, l ^ (k + 1) = M + 1 := ⟨_, (Nat.succ_pred_eq_of_pos hN).symm⟩
    rw [hM, Polynomial.separable_def']
    have hc : ((M : K) + 1) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero M
    refine ⟨-1, Polynomial.C ((M : K) + 1)⁻¹ * (1 + Polynomial.X), ?_⟩
    have e : Polynomial.C ((M : K) + 1)⁻¹ * Polynomial.C ((M : K) + 1) = 1 := by
      rw [← map_mul, inv_mul_cancel₀ hc, map_one]
    simp only [Polynomial.derivative_sub, Polynomial.derivative_one, Polynomial.derivative_pow_succ,
      Polynomial.derivative_add, Polynomial.derivative_X, zero_add, mul_one, sub_zero]
    linear_combination ((1 + Polynomial.X : Polynomial K) ^ (M + 1)) * e
  rw [← lvlPoly_mul] at hs
  exact hs.of_mul_left

/- English proof (translation)
Rewrite `ha`, the goal using `[← lvlPoly_coe]`. Establish `H` using `lvlPoly_distinguished h k`. Take `⟨r, -, hr⟩` from `GlobalTheory.NB.LT.exists_poly_mod H a`. Establish `h1 : ((lvlPoly l O k : Polynomial O) : O⟦X⟧) ∣ ((r ^ 2 : Polynomial O) : O⟦X⟧)`. Rewrite using `[Polynomial.coe_pow, show (r : O⟦X⟧) ^ 2 = a ^ 2 - (a - r) * (a + r) by ring]`.

Conclude with `ha.sub (hr.mul_right _)`. Establish `h2` using `GlobalTheory.NB.LT.poly_dvd_of_dvd H h1`. Set `K` to `FractionRing O`. Use `haveI : CharZero K := algebraRat.charZero K`. Establish `h3` using `Polynomial.map_dvd (algebraMap O K) h2`.

Rewrite `h3` using `[Polynomial.map_pow, lvlPoly_map]`. Establish `h4` using `(lvlPoly_separable (l := l) (K := K) k).squarefree.dvd_pow_iff_dvd two_ne_zero |>.1 h3`. Rewrite `h4` using `[← lvlPoly_map (algebraMap O K), Polynomial.map_dvd_map _ (IsFractionRing.injective O K) H.monic]`. Take `⟨s, hs⟩` from `h4`. Establish `h5 : ((lvlPoly l O k : Polynomial O) : O⟦X⟧) ∣ (r : O⟦X⟧)` using `⟨s, by rw [hs, Polynomial.coe_mul]⟩`.

Simplify using `using hr.add h5`.
-/
theorem lvl_dvd_of_dvd_sq {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] [IsAdicComplete (IsLocalRing.maximalIdeal O) O] [CharZero O]
    (h : ¬ IsUnit (l : O)) (k : ℕ) (a : O⟦X⟧) (ha : lvl l O k ∣ a ^ 2) : lvl l O k ∣ a := by
  rw [← lvlPoly_coe] at ha ⊢
  have H := lvlPoly_distinguished h k
  obtain ⟨r, -, hr⟩ := GlobalTheory.NB.LT.exists_poly_mod H a
  have h1 : ((lvlPoly l O k : Polynomial O) : O⟦X⟧) ∣ ((r ^ 2 : Polynomial O) : O⟦X⟧) := by
    rw [Polynomial.coe_pow,
      show (r : O⟦X⟧) ^ 2 = a ^ 2 - (a - r) * (a + r) by ring]
    exact ha.sub (hr.mul_right _)
  have h2 := GlobalTheory.NB.LT.poly_dvd_of_dvd H h1
  let K := FractionRing O
  haveI : CharZero K := algebraRat.charZero K
  have h3 := Polynomial.map_dvd (algebraMap O K) h2
  rw [Polynomial.map_pow, lvlPoly_map] at h3
  have h4 := (lvlPoly_separable (l := l) (K := K) k).squarefree.dvd_pow_iff_dvd two_ne_zero |>.1 h3
  rw [← lvlPoly_map (algebraMap O K),
    Polynomial.map_dvd_map _ (IsFractionRing.injective O K) H.monic] at h4
  obtain ⟨s, hs⟩ := h4
  have h5 : ((lvlPoly l O k : Polynomial O) : O⟦X⟧) ∣ (r : O⟦X⟧) :=
    ⟨s, by rw [hs, Polynomial.coe_mul]⟩
  simpa using hr.add h5

end GlobalTheory.CycFr.Red

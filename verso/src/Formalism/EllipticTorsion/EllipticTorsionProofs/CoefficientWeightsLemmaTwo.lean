import Mathlib
import Formalism.EllipticTorsion.EllipticTorsionWeights
import Formalism.EllipticTorsion.EllipticTorsionProofs.CompExp
import Formalism.FormalGroupLog.LogDeterminesLaw

open PowerSeries

namespace Formalism.ELL.Lemma2Aux

variable {K : Type*} [NormedField K] [IsUltrametricDist K]

/- English proof (translation)
Establish `hcop : Nat.Coprime p m` using `(Nat.Prime.coprime_iff_not_dvd hp).2 hm`. Establish `h` using `Nat.gcd_eq_gcd_ab p m`. Rewrite `h` using `[hcop]`. Establish `hK : (1 : K) = (p : K) * (Nat.gcdA p m : K) + (m : K) * (Nat.gcdB p m : K)`. Use `congrArg (Int.cast : ℤ → K) h` as an intermediate fact.

Move the coercions through the operations in `at this`. Conclude with `this`. Use `le_antisymm (IsUltrametricDist.norm_natCast_le_one K m) ?_` and prove the remaining obligations. Assume the negation of the conclusion as `hlt`. Use `push_neg at hlt`.

Establish `hmax` using `IsUltrametricDist.norm_add_le_max ((p : K) * (Nat.gcdA p m : K)) ((m : K) * (Nat.gcdB p m : K))`. Rewrite `hmax` using `[← hK, norm_one, norm_mul, norm_mul]`. Establish `ha` using `IsUltrametricDist.norm_intCast_le_one K (Nat.gcdA p m)`. Establish `hb` using `IsUltrametricDist.norm_intCast_le_one K (Nat.gcdB p m)`. Establish `h1 : ‖(p : K)‖ * ‖((Nat.gcdA p m : ℤ) : K)‖ < 1` using `lt_of_le_of_lt (mul_le_of_le_one_right (norm_nonneg _) ha) hpl`.

Establish `h2 : ‖(m : K)‖ * ‖((Nat.gcdB p m : ℤ) : K)‖ < 1` using `lt_of_le_of_lt (mul_le_of_le_one_right (norm_nonneg _) hb) hlt`. Conclude with `absurd hmax (not_le.2 (max_lt h1 h2))`.
-/
theorem norm_nat_eq_one {p : ℕ} (hp : p.Prime) (hpl : ‖(p : K)‖ < 1) (m : ℕ) (hm : ¬ p ∣ m) :
    ‖(m : K)‖ = 1 := by
  have hcop : Nat.Coprime p m := (Nat.Prime.coprime_iff_not_dvd hp).2 hm
  have h := Nat.gcd_eq_gcd_ab p m
  rw [hcop] at h
  have hK : (1 : K) = (p : K) * (Nat.gcdA p m : K) + (m : K) * (Nat.gcdB p m : K) := by
    have := congrArg (Int.cast : ℤ → K) h
    push_cast at this
    exact this
  refine le_antisymm (IsUltrametricDist.norm_natCast_le_one K m) ?_
  by_contra hlt
  push_neg at hlt
  have hmax := IsUltrametricDist.norm_add_le_max ((p : K) * (Nat.gcdA p m : K)) ((m : K) * (Nat.gcdB p m : K))
  rw [← hK, norm_one, norm_mul, norm_mul] at hmax
  have ha := IsUltrametricDist.norm_intCast_le_one K (Nat.gcdA p m)
  have hb := IsUltrametricDist.norm_intCast_le_one K (Nat.gcdB p m)
  have h1 : ‖(p : K)‖ * ‖((Nat.gcdA p m : ℤ) : K)‖ < 1 :=
    lt_of_le_of_lt (mul_le_of_le_one_right (norm_nonneg _) ha) hpl
  have h2 : ‖(m : K)‖ * ‖((Nat.gcdB p m : ℤ) : K)‖ < 1 :=
    lt_of_le_of_lt (mul_le_of_le_one_right (norm_nonneg _) hb) hlt
  exact absurd hmax (not_le.2 (max_lt h1 h2))

/- English proof (translation)
Establish `: Fact p.Prime` using `⟨hp⟩`. Proceed by induction on `k with`. Consider the case `zero => simp [Nat.ModEq.refl]`. Consider the case `succ k ih`. Establish `h` using `Choose.choose_mul_mul_modEq_choose_nat (p := p) (a := p ^ k * m) (b := p ^ k)`.

Rewrite using `[pow_succ', mul_assoc]`. Conclude with `h.trans ih`.
-/
theorem choose_pow_mul_modEq {p : ℕ} (hp : p.Prime) (k m : ℕ) :
    (p ^ k * m).choose (p ^ k) ≡ m [MOD p] := by
  have : Fact p.Prime := ⟨hp⟩
  induction k with
  | zero => simp [Nat.ModEq.refl]
  | succ k ih =>
    have h := Choose.choose_mul_mul_modEq_choose_nat (p := p) (a := p ^ k * m) (b := p ^ k)
    rw [pow_succ', mul_assoc]
    exact h.trans ih

/- English proof (translation)
Rewrite using `[Nat.factorization_choose_prime_pow hp (Nat.pow_le_pow_right hp.pos (by omega)) (pow_ne_zero _ hp.ne_zero)]`. Rewrite using `[hp.factorization_pow]`. Simplify using the standard rewrite rules. Use linear arithmetic over natural numbers and integers.
-/
theorem fact_choose_prime_pow {p : ℕ} (hp : p.Prime) (k : ℕ) (hk : 1 ≤ k) :
    ((p ^ k).choose (p ^ (k - 1))).factorization p = 1 := by
  rw [Nat.factorization_choose_prime_pow hp (Nat.pow_le_pow_right hp.pos (by omega))
    (pow_ne_zero _ hp.ne_zero)]
  rw [hp.factorization_pow]
  simp
  omega

/- English proof (translation)
Rewrite using `[add_pow, map_sum]`. Establish `hterm : ∀ m ∈ Finset.range (d + 1), MvPowerSeries.coeff (Finsupp.single (0 : Fin 2) i + Finsupp.single 1 j) ((MvPowerSeries.X 0 : MvPowerSeries (Fin 2) R) ^ m * MvPowerSeries.X 1 ^ (d - m) * (d.choose m : MvPowerSeries (Fin 2) R)) = if m = i ∧ d - m = j then (d.choose m : R) else …`. Introduce `m _`. Rewrite using `[MvPowerSeries.X_pow_eq, MvPowerSeries.X_pow_eq, MvPowerSeries.monomial_mul_monomial, ← map_natCast (MvPowerSeries.C (σ := Fin 2) (R := R)), mul_comm, MvPowerSeries.coeff_C_mul, MvPowerSeries.coeff_monomial]`. Establish `: (Finsupp.single (0 : Fin 2) i + Finsupp.single 1 j = Finsupp.single 0 m + Finsupp.single 1 (d - m)) ↔ (m = i ∧ d - m = j)`.

Prove the components needed by the constructor for the conclusion. Introduce `h`. Establish `h0` using `congrArg (· 0) h`. Establish `h1` using `congrArg (· 1) h`. Simplify using `at h0 h1`.

Use linear arithmetic over natural numbers and integers. Introduce and unpack `⟨rfl, rfl⟩`. Both sides reduce to the same expression. Distinguish the cases in `hc : m = i ∧ d - m = j`. Rewrite using `[if_pos (this.2 hc), if_pos hc]`.

Simplify using the standard rewrite rules. Rewrite using `[if_neg (fun h => hc (this.1 h)), if_neg hc, mul_zero]`. Rewrite using `[Finset.sum_congr rfl hterm]`. Distinguish the cases in `hij : i + j = d`. Rewrite using `[if_pos hij, Finset.sum_eq_single i]`.

Rewrite using `[if_pos ⟨rfl, by omega⟩]`. Introduce `b _ hb`. Rewrite using `[if_neg (fun h => hb h.1)]`. Introduce `h`. Simplify using `at h`.

Use linear arithmetic over natural numbers and integers. Rewrite using `[if_neg hij]`. Use `Finset.sum_eq_zero fun m hm => ?_` and prove the remaining obligations. Simplify using `at hm`. Rewrite using `[if_neg (by omega)]`.
-/
theorem coeff_X0_add_X1_pow {R : Type*} [CommRing R] (d i j : ℕ) :
    MvPowerSeries.coeff (Finsupp.single (0 : Fin 2) i + Finsupp.single 1 j)
      ((MvPowerSeries.X 0 + MvPowerSeries.X 1 : MvPowerSeries (Fin 2) R) ^ d) =
      if i + j = d then (d.choose i : R) else 0 := by
  rw [add_pow, map_sum]
  have hterm : ∀ m ∈ Finset.range (d + 1),
      MvPowerSeries.coeff (Finsupp.single (0 : Fin 2) i + Finsupp.single 1 j)
        ((MvPowerSeries.X 0 : MvPowerSeries (Fin 2) R) ^ m * MvPowerSeries.X 1 ^ (d - m) *
          (d.choose m : MvPowerSeries (Fin 2) R)) =
      if m = i ∧ d - m = j then (d.choose m : R) else 0 := by
    intro m _
    rw [MvPowerSeries.X_pow_eq, MvPowerSeries.X_pow_eq, MvPowerSeries.monomial_mul_monomial,
      ← map_natCast (MvPowerSeries.C (σ := Fin 2) (R := R)), mul_comm, MvPowerSeries.coeff_C_mul,
      MvPowerSeries.coeff_monomial]
    have : (Finsupp.single (0 : Fin 2) i + Finsupp.single 1 j =
        Finsupp.single 0 m + Finsupp.single 1 (d - m)) ↔ (m = i ∧ d - m = j) := by
      constructor
      · intro h
        have h0 := congrArg (· 0) h
        have h1 := congrArg (· 1) h
        simp at h0 h1
        omega
      · rintro ⟨rfl, rfl⟩; rfl
    by_cases hc : m = i ∧ d - m = j
    · rw [if_pos (this.2 hc), if_pos hc]; simp
    · rw [if_neg (fun h => hc (this.1 h)), if_neg hc, mul_zero]
  rw [Finset.sum_congr rfl hterm]
  by_cases hij : i + j = d
  · rw [if_pos hij, Finset.sum_eq_single i]
    · rw [if_pos ⟨rfl, by omega⟩]
    · intro b _ hb; rw [if_neg (fun h => hb h.1)]
    · intro h; simp at h; omega
  · rw [if_neg hij]
    refine Finset.sum_eq_zero fun m hm => ?_
    simp at hm
    rw [if_neg (by omega)]

open Formalism.G

/- English proof (translation)
Use `set b := fun i : Fin 2 => E.subst (MvPowerSeries.X i : MvPowerSeries (Fin 2) K) with hbdef`. Establish `hbi : ∀ i, MvPowerSeries.constantCoeff (b i) = 0` using `fun i => PowerSeries.constantCoeff_subst_eq_zero (by simp) E hE0`. Establish `hb : MvPowerSeries.HasSubst b` using `MvPowerSeries.hasSubst_of_constantCoeff_zero hbi`. Establish `hE : PowerSeries.HasSubst E` using `PowerSeries.HasSubst.of_constantCoeff_zero' hE0`. Establish `hS : MvPowerSeries.constantCoeff (MvPowerSeries.X 0 + MvPowerSeries.X 1 : MvPowerSeries (Fin 2) K) = 0` using `by simp`.

Establish `hlb : ∀ i, l.subst (b i) = MvPowerSeries.X i`. Introduce `i`. Simplify using `only [hbdef]`. Rewrite using `[← PowerSeries.subst_comp_subst_apply hE (PowerSeries.HasSubst.X i), hlE, PowerSeries.subst_X (PowerSeries.HasSubst.X i)]`. Establish `hsF : MvPowerSeries.constantCoeff (MvPowerSeries.subst b Fs) = 0`.

Rewrite using `[LogP.constantCoeff_subst_of_zero Fs hbi, hFc]`. Establish `h1 : l.subst (MvPowerSeries.subst b Fs) = MvPowerSeries.X 0 + MvPowerSeries.X 1`. Rewrite using `[← LogP.psubst_subst l hFc hb, hlF, MvPowerSeries.subst_add hb, atX, atY, LogP.psubst_subst l (by simp) hb, LogP.psubst_subst l (by simp) hb, MvPowerSeries.subst_X hb, MvPowerSeries.subst_X hb, hlb, hlb]`. Establish `key : MvPowerSeries.subst b Fs = E.subst (MvPowerSeries.X 0 + MvPowerSeries.X 1 : MvPowerSeries (Fin 2) K)`. Combine the equalities or inequalities in the displayed calculation.

Rewrite using `[MvPowerSeries.subst_sub hb, MvPowerSeries.subst_sub hb, LogP.psubst_subst g hFc hb, key, atX, atY, LogP.psubst_subst g (by simp) hb, LogP.psubst_subst g (by simp) hb, MvPowerSeries.subst_X hb, MvPowerSeries.subst_X hb, PowerSeries.subst_comp_subst_apply hE (PowerSeries.HasSubst. …`.
-/
theorem add_identity (Fs : MvPowerSeries (Fin 2) K) (hFc : MvPowerSeries.constantCoeff Fs = 0)
    (l E g : PowerSeries K) (hl0 : constantCoeff l = 0) (hlF : l.subst Fs = atX l + atY l)
    (hE0 : constantCoeff E = 0) (hEl : E.subst l = X) (hlE : l.subst E = X) :
    MvPowerSeries.subst (fun i : Fin 2 => E.subst (MvPowerSeries.X i : MvPowerSeries (Fin 2) K))
        (g.subst Fs - atX g - atY g) =
      PowerSeries.subst (MvPowerSeries.X 0 + MvPowerSeries.X 1 : MvPowerSeries (Fin 2) K) (PowerSeries.subst E g)
        - PowerSeries.subst (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) K) (PowerSeries.subst E g)
        - PowerSeries.subst (MvPowerSeries.X 1 : MvPowerSeries (Fin 2) K) (PowerSeries.subst E g) := by
  set b := fun i : Fin 2 => E.subst (MvPowerSeries.X i : MvPowerSeries (Fin 2) K) with hbdef
  have hbi : ∀ i, MvPowerSeries.constantCoeff (b i) = 0 := fun i =>
    PowerSeries.constantCoeff_subst_eq_zero (by simp) E hE0
  have hb : MvPowerSeries.HasSubst b := MvPowerSeries.hasSubst_of_constantCoeff_zero hbi
  have hE : PowerSeries.HasSubst E := PowerSeries.HasSubst.of_constantCoeff_zero' hE0
  have hS : MvPowerSeries.constantCoeff (MvPowerSeries.X 0 + MvPowerSeries.X 1 : MvPowerSeries (Fin 2) K) = 0 := by simp
  have hlb : ∀ i, l.subst (b i) = MvPowerSeries.X i := by
    intro i
    simp only [hbdef]
    rw [← PowerSeries.subst_comp_subst_apply hE (PowerSeries.HasSubst.X i), hlE,
      PowerSeries.subst_X (PowerSeries.HasSubst.X i)]
  have hsF : MvPowerSeries.constantCoeff (MvPowerSeries.subst b Fs) = 0 := by
    rw [LogP.constantCoeff_subst_of_zero Fs hbi, hFc]
  have h1 : l.subst (MvPowerSeries.subst b Fs) = MvPowerSeries.X 0 + MvPowerSeries.X 1 := by
    rw [← LogP.psubst_subst l hFc hb, hlF, MvPowerSeries.subst_add hb, atX, atY,
      LogP.psubst_subst l (by simp) hb, LogP.psubst_subst l (by simp) hb,
      MvPowerSeries.subst_X hb, MvPowerSeries.subst_X hb, hlb, hlb]
  have key : MvPowerSeries.subst b Fs = E.subst (MvPowerSeries.X 0 + MvPowerSeries.X 1 : MvPowerSeries (Fin 2) K) := by
    calc MvPowerSeries.subst b Fs
        = PowerSeries.subst (MvPowerSeries.subst b Fs) (X : PowerSeries K) :=
          (PowerSeries.subst_X (PowerSeries.HasSubst.of_constantCoeff_zero hsF)).symm
      _ = PowerSeries.subst (MvPowerSeries.subst b Fs) (PowerSeries.subst l E : PowerSeries K) := by rw [hEl]
      _ = PowerSeries.subst (PowerSeries.subst (MvPowerSeries.subst b Fs) l) E :=
          PowerSeries.subst_comp_subst_apply (PowerSeries.HasSubst.of_constantCoeff_zero' hl0)
            (PowerSeries.HasSubst.of_constantCoeff_zero hsF) E
      _ = _ := by rw [h1]
  rw [MvPowerSeries.subst_sub hb, MvPowerSeries.subst_sub hb, LogP.psubst_subst g hFc hb, key, atX, atY,
    LogP.psubst_subst g (by simp) hb, LogP.psubst_subst g (by simp) hb,
    MvPowerSeries.subst_X hb, MvPowerSeries.subst_X hb,
    PowerSeries.subst_comp_subst_apply hE (PowerSeries.HasSubst.of_constantCoeff_zero hS),
    PowerSeries.subst_comp_subst_apply hE (PowerSeries.HasSubst.X 0),
    PowerSeries.subst_comp_subst_apply hE (PowerSeries.HasSubst.X 1)]

/- English proof (translation)
Establish `hh : IsHom F FormalGroup.𝔾ₐ (l.subst (ζ • X : PowerSeries K))` using `Formalism.G.homComp K F F FormalGroup.𝔾ₐ _ _ hhom ((Formalism.G.logIffHomGa K F l).1 hl).1`. Use `set h : PowerSeries K := l.subst (ζ • X : PowerSeries K) with hdef`. Establish `hFs : PowerSeries.HasSubst F.toPowerSeries` using `PowerSeries.HasSubst.of_constantCoeff_zero F.zero_constantCoeff`. Establish `hfun : PowerSeries.subst F.toPowerSeries h = atX h + atY h`. Establish `hv` using `LogP.hs2 (σ := Fin 2) (u := atX h) (v := atY h) (PowerSeries.constantCoeff_subst_eq_zero (by simp) h hh.1) (PowerSeries.constantCoeff_subst_eq_zero (by simp) h hh.1)`.

Rewrite using `[hh.2, FormalGroup.𝔾ₐ_toPowerSeries, MvPowerSeries.subst_add hv, MvPowerSeries.subst_X hv, MvPowerSeries.subst_X hv]`. Both sides reduce to the same expression. Establish `hc1 : coeff 1 h = ζ`. Rewrite using `[hdef, ← PowerSeries.rescale_eq_subst, PowerSeries.coeff_rescale, hl.2.1]`. Simplify using the standard rewrite rules.

Establish `hlog : IsLog F (ζ⁻¹ • h)`. Use `⟨?_, ?_, ?_⟩` and prove the remaining obligations. Simplify using `[hh.1]`. Rewrite using `[LinearMap.map_smul_of_tower, hc1, smul_eq_mul, inv_mul_cancel₀ hζ0]`. Simplify using `only [Formalism.G.atX, Formalism.G.atY] at hfun ⊢`.

Rewrite using `[PowerSeries.subst_smul hFs, hfun, PowerSeries.subst_smul (PowerSeries.HasSubst.X 0), PowerSeries.subst_smul (PowerSeries.HasSubst.X 1), smul_add]`. Use `LogP.log_unique F hlog hl` as an intermediate fact. Rewrite using `[← this, smul_inv_smul₀ hζ0]`.
-/
theorem log_rescale [CharZero K] (F : FormalGroup K) (l : PowerSeries K) (ζ : K) (hζ0 : ζ ≠ 0)
    (hl : IsLog F l) (hhom : IsHom F F (ζ • X)) : (l.subst (ζ • X : PowerSeries K) : PowerSeries K) = ζ • l := by
  have hh : IsHom F FormalGroup.𝔾ₐ (l.subst (ζ • X : PowerSeries K)) :=
    Formalism.G.homComp K F F FormalGroup.𝔾ₐ _ _ hhom ((Formalism.G.logIffHomGa K F l).1 hl).1
  set h : PowerSeries K := l.subst (ζ • X : PowerSeries K) with hdef
  have hFs : PowerSeries.HasSubst F.toPowerSeries :=
    PowerSeries.HasSubst.of_constantCoeff_zero F.zero_constantCoeff
  have hfun : PowerSeries.subst F.toPowerSeries h = atX h + atY h := by
    have hv := LogP.hs2 (σ := Fin 2) (u := atX h) (v := atY h)
      (PowerSeries.constantCoeff_subst_eq_zero (by simp) h hh.1)
      (PowerSeries.constantCoeff_subst_eq_zero (by simp) h hh.1)
    rw [hh.2, FormalGroup.𝔾ₐ_toPowerSeries, MvPowerSeries.subst_add hv, MvPowerSeries.subst_X hv,
      MvPowerSeries.subst_X hv]
    rfl
  have hc1 : coeff 1 h = ζ := by
    rw [hdef, ← PowerSeries.rescale_eq_subst, PowerSeries.coeff_rescale, hl.2.1]; simp
  have hlog : IsLog F (ζ⁻¹ • h) := by
    refine ⟨?_, ?_, ?_⟩
    · simp [hh.1]
    · rw [LinearMap.map_smul_of_tower, hc1, smul_eq_mul, inv_mul_cancel₀ hζ0]
    · simp only [Formalism.G.atX, Formalism.G.atY] at hfun ⊢
      rw [PowerSeries.subst_smul hFs, hfun, PowerSeries.subst_smul (PowerSeries.HasSubst.X 0),
        PowerSeries.subst_smul (PowerSeries.HasSubst.X 1), smul_add]
  have := LogP.log_unique F hlog hl
  rw [← this, smul_inv_smul₀ hζ0]

/- English proof (translation)
Establish `hE : PowerSeries.HasSubst E` using `PowerSeries.HasSubst.of_constantCoeff_zero' hE0`. Establish `ha : PowerSeries.HasSubst (ζ • X : PowerSeries K)` using `PowerSeries.HasSubst.smul_X' ζ`. Establish `hzE : (PowerSeries.subst E (ζ • X : PowerSeries K) : PowerSeries K) = ζ • E`. Rewrite using `[PowerSeries.subst_smul hE, PowerSeries.subst_X hE]`. Establish `hzE0 : constantCoeff (ζ • E) = 0` using `by simp [hE0]`.

Establish `hzEs : PowerSeries.HasSubst (ζ • E)` using `PowerSeries.HasSubst.of_constantCoeff_zero' hzE0`. Establish `h1 : (PowerSeries.subst (ζ • E) l : PowerSeries K) = ζ • X`. Rewrite using `[← hzE, ← PowerSeries.subst_comp_subst_apply ha hE, hlz, PowerSeries.subst_smul hE, hlE]`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem exp_rescale (l E : PowerSeries K) (ζ : K) (hE0 : constantCoeff E = 0) (hl0 : constantCoeff l = 0)
    (hEl : E.subst l = X) (hlE : l.subst E = X) (hlz : (l.subst (ζ • X : PowerSeries K) : PowerSeries K) = ζ • l) :
    (E.subst (ζ • X : PowerSeries K) : PowerSeries K) = ζ • E := by
  have hE : PowerSeries.HasSubst E := PowerSeries.HasSubst.of_constantCoeff_zero' hE0
  have ha : PowerSeries.HasSubst (ζ • X : PowerSeries K) := PowerSeries.HasSubst.smul_X' ζ
  have hzE : (PowerSeries.subst E (ζ • X : PowerSeries K) : PowerSeries K) = ζ • E := by
    rw [PowerSeries.subst_smul hE, PowerSeries.subst_X hE]
  have hzE0 : constantCoeff (ζ • E) = 0 := by simp [hE0]
  have hzEs : PowerSeries.HasSubst (ζ • E) := PowerSeries.HasSubst.of_constantCoeff_zero' hzE0
  have h1 : (PowerSeries.subst (ζ • E) l : PowerSeries K) = ζ • X := by
    rw [← hzE, ← PowerSeries.subst_comp_subst_apply ha hE, hlz, PowerSeries.subst_smul hE, hlE]
  calc (E.subst (ζ • X : PowerSeries K) : PowerSeries K) = PowerSeries.subst (PowerSeries.subst (ζ • E) l : PowerSeries K) E := by rw [h1]
    _ = PowerSeries.subst (ζ • E) (PowerSeries.subst l E : PowerSeries K) :=
        (PowerSeries.subst_comp_subst_apply (PowerSeries.HasSubst.of_constantCoeff_zero' hl0) hzEs E).symm
    _ = ζ • E := by rw [hEl, PowerSeries.subst_X hzEs]

universe u

/- English proof (translation)
Introduce `K _ _ _ p hp hp0 hp1 F l E g ζ hl hE0 hEl hlE hEb hζ hζu hhom hg0 hH hh _hg1 n`. Use `set D : ℝ := (p : ℝ) ^ 2 - 1 with hD`. Establish `hp2 : (2 : ℝ) ≤ p` using `by exact_mod_cast hp.two_le`. Establish `hDpos : 0 < D` using `by rw [hD]; nlinarith`. Use `set c : ℝ := ‖(p : K)‖ ^ (1 / D) with hcdef`.

Establish `hc : 0 < c` using `Real.rpow_pos_of_pos hp0 _`. Establish `hc1 : c ≤ 1` using `Real.rpow_le_one (norm_nonneg _) hp1.le (by positivity)`. Establish `cz : ∀ k : ℤ, c ^ k = ‖(p : K)‖ ^ ((k : ℝ) / D)`. Introduce `k`. Rewrite using `[hcdef, ← Real.rpow_intCast, ← Real.rpow_mul (norm_nonneg _)]`.

Use `congr 1`. Expand and normalize the polynomial expressions, which then agree. Establish `hEb' : ∀ n : ℕ, 1 ≤ n → ‖coeff n E‖ ≤ c ^ (1 - (n : ℤ))`. Introduce `m hm`. Rewrite using `[cz]`.

Use `hEb m hm using 2` and compare the differences between its conclusion and the goal. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Use `set G : PowerSeries K := PowerSeries.subst E g with hGdef`. Establish `hE' : PowerSeries.HasSubst E` using `PowerSeries.HasSubst.of_constantCoeff_zero' hE0`.

Establish `hbin : ∀ i j : ℕ, 1 ≤ i → 1 ≤ j → ‖(((i + j).choose i : ℕ) : K)‖ * ‖coeff (i + j) G‖ ≤ c ^ (-((i + j : ℕ) : ℤ))`. Introduce `i j hi hj`. Establish `hS : MvPowerSeries.constantCoeff (MvPowerSeries.X 0 + MvPowerSeries.X 1 : MvPowerSeries (Fin 2) K) = 0` using `by simp`. Establish `hw` using `hCE K (Fin 2) c hc hc1 E hE0 hEb' _ hH (Finsupp.single 0 i + Finsupp.single 1 j)`. Rewrite `hw` using `[add_identity (FK F).toPowerSeries (FK F).zero_constantCoeff l E g hl.1 hl.2.2 hE0 hEl hlE]`.

Establish `e1 : MvPowerSeries.coeff (Finsupp.single 0 i + Finsupp.single 1 j) (PowerSeries.subst (MvPowerSeries.X 0 + MvPowerSeries.X 1 : MvPowerSeries (Fin 2) K) G) = (((i + j).choose i : ℕ) : K) * coeff (i + j) G`. Rewrite using `[PowerSeries.coeff_subst (PowerSeries.HasSubst.of_constantCoeff_zero hS), finsum_eq_single _ (i + j)]`. Rewrite using `[coeff_X0_add_X1_pow, if_pos rfl, smul_eq_mul, mul_comm]`. Introduce `d hd`. Rewrite using `[coeff_X0_add_X1_pow, if_neg (Ne.symm hd), smul_zero]`.

Establish `e2 : MvPowerSeries.coeff (Finsupp.single 0 i + Finsupp.single 1 j) (PowerSeries.subst (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) K) G) = 0`. Rewrite using `[PowerSeries.coeff_subst_single, if_neg]`. Introduce `h`. Use `congrArg (· 1) h` as an intermediate fact. Simplify using `at this`.

Use linear arithmetic over natural numbers and integers. Establish `e3 : MvPowerSeries.coeff (Finsupp.single 0 i + Finsupp.single 1 j) (PowerSeries.subst (MvPowerSeries.X 1 : MvPowerSeries (Fin 2) K) G) = 0`. Rewrite using `[PowerSeries.coeff_subst_single, if_neg]`. Introduce `h`. Use `congrArg (· 0) h` as an intermediate fact.

Simplify using `at this`. Use linear arithmetic over natural numbers and integers. Establish `edeg : (Finsupp.single (0 : Fin 2) i + Finsupp.single 1 j).degree = i + j`. Rewrite using `[map_add, Finsupp.degree_single, Finsupp.degree_single]`. Rewrite `hw` using `[map_sub, map_sub, e1, e2, e3, sub_zero, sub_zero, norm_mul, edeg]`.

Conclude with `hw` after adjusting the coercions. Establish `hpq : p < p ^ 2`. Rewrite using `[sq]`. Conclude with `Nat.lt_mul_self_iff.2 hp.two_le`. Establish `hq0 : p ^ 2 - 1 ≠ 0` using `Nat.sub_ne_zero_of_lt (one_lt_pow' hp.one_lt (by norm_num))`.

Establish `hζ0 : ζ ≠ 0`. Introduce and unpack `rfl`. Rewrite `hζ` using `[zero_pow hq0]`. Conclude with `zero_ne_one hζ`. Establish `hnz : ‖ζ‖ = 1`.

Establish `h1 : ‖ζ‖ ^ (p ^ 2 - 1) = 1` using `by rw [← norm_pow, hζ, norm_one]`. Conclude with `(pow_eq_one_iff_of_nonneg (norm_nonneg _) hq0).1 h1`. Establish `hζbound : ∀ m : ℕ, ‖(ζ ^ m - ζ ^ p) * coeff m G‖ ≤ c ^ (-(m : ℤ))`. Introduce `m`. Establish `hlz` using `log_rescale (FK F) l ζ hζ0 hl hhom`.

Establish `hEz` using `exp_rescale l E ζ hE0 hl.1 hEl hlE hlz`. Establish `ha : PowerSeries.HasSubst (ζ • X : PowerSeries K)` using `PowerSeries.HasSubst.smul_X' ζ`. Use `set h' : PowerSeries K := PowerSeries.subst (ζ • X : PowerSeries K) g - ζ ^ p • g with hh'`. Establish `hid : (PowerSeries.subst E h' : PowerSeries K) = PowerSeries.rescale ζ G - ζ ^ p • G`. Rewrite using `[hh', PowerSeries.subst_sub hE', PowerSeries.subst_smul hE', PowerSeries.subst_comp_subst_apply ha hE', PowerSeries.subst_smul hE', PowerSeries.subst_X hE', PowerSeries.rescale_eq_subst, hGdef, PowerSeries.subst_comp_subst_apply hE' ha, hEz]`.

Establish `hint : IntegralMv (ι` using `Unit) h' := by`. Introduce `d`. Establish `hd : d = Finsupp.single () (d ())`. Use `Finsupp.ext fun x => ?_` and prove the remaining obligations. Consider the cases of `x`.

Simplify using the standard rewrite rules. Rewrite using `[hd]`. Conclude with `hh (d ())`. Establish `hw` using `hCE K Unit c hc hc1 E hE0 hEb' h' hint (Finsupp.single () m)`. Establish `hsub : (fun i : Unit => E.subst (MvPowerSeries.X i : MvPowerSeries Unit K)) = fun _ => E`.

Use function extensionality and compare the values at `i`. Consider the cases of `i`. Conclude with `PowerSeries.X_subst E`. Rewrite `hw` using `[hsub, ← PowerSeries.subst_def, hid, Finsupp.degree_single]`. Establish `hcm : MvPowerSeries.coeff (Finsupp.single () m) (PowerSeries.rescale ζ G - ζ ^ p • G) = (ζ ^ m - ζ ^ p) * coeff m G`.

Express the relevant statement in the definitionally equal form `coeff m (PowerSeries.rescale ζ G - ζ ^ p • G) = _`. Rewrite using `[map_sub, PowerSeries.coeff_rescale, LinearMap.map_smul_of_tower, smul_eq_mul, sub_mul]`. Rewrite `hw` using `[hcm]`. Conclude with `hw`. Establish `strong : ∀ x : K, ‖x‖ ≤ c ^ (-(n : ℤ)) → ‖x‖ ≤ ‖(p : K)‖ ^ (-(n : ℝ) / D)`.

Introduce `x hx`. Rewrite `hx` using `[cz]`. Move the coercions through the operations in `at hx`. Conclude with `hx`. Establish `weak : ∀ x : K, ‖(p : K)‖ * ‖x‖ ≤ c ^ (-(n : ℤ)) → ‖x‖ ≤ ‖(p : K)‖ ^ (-1 - (n : ℝ) / D)`.

Introduce `x hx`. Rewrite `hx` using `[cz]`. Move the coercions through the operations in `at hx`. Rewrite using `[show (-1 - (n : ℝ) / D) = -1 + (-(n : ℝ) / D) by ring, Real.rpow_add hp0, Real.rpow_neg_one, le_inv_mul_iff₀ hp0]`. Conclude with `hx`.

Break down `Nat.eq_zero_or_pos n with rfl | hn` into its components or cases. Use `left`. Establish `h0 : coeff 0 G = 0`. Rewrite using `[PowerSeries.coeff_zero_eq_constantCoeff_apply, hGdef]`. Conclude with `PowerSeries.constantCoeff_subst_eq_zero hE0 g hg0`.

Rewrite using `[h0, norm_zero]`. Check the signs of the components of the expression. Take `⟨k, m, hnm, hm⟩ : ∃ k m, p ^ k * m = n ∧ ¬ p ∣ m` from `⟨_, _, Nat.ordProj_mul_ordCompl_eq_self n p, Nat.not_dvd_ordCompl hp hn.ne'⟩`. Establish `hm0 : m ≠ 0`. Introduce and unpack `rfl`.

Rewrite `hnm` using `[mul_zero]`. Use linear arithmetic over natural numbers and integers. Establish `hpk : 1 ≤ p ^ k` using `Nat.one_le_pow _ _ hp.pos`. Distinguish the cases in `hm1 : m = 1`. Rewrite `hnm` using `[hm1, mul_one]`.

Substitute `hnm` using the available equality. Break down `Nat.even_or_odd k with hke | hko` into its components or cases. Use `left`. Apply `strong` to reduce the goal to its premises. Establish `hb` using `hζbound (p ^ k)`.

Establish `hunit : ‖ζ ^ (p ^ k) - ζ ^ p‖ = 1`. Break down `Nat.eq_zero_or_pos k with rfl | hkpos` into its components or cases. Establish `hndvd : ¬ (p ^ 2 - 1) ∣ (p - 1)`. Introduce `h`. Establish `h3` using `Nat.le_of_dvd (by have := hp.two_le; omega) h`.

Establish `h4` using `hpq`. Establish `h5` using `hp.two_le`. Generalize the expression as in `p ^ 2 = q at h3 h4`. Use linear arithmetic over natural numbers and integers. Rewrite using `[pow_zero, pow_one, show ζ ^ p = ζ * ζ ^ (p - 1) by`.

Rewrite using `[← pow_succ', Nat.sub_add_cancel hp.one_le]]`. Rewrite using `[show ζ - ζ * ζ ^ (p - 1) = -(ζ * (ζ ^ (p - 1) - 1)) by ring, norm_neg, norm_mul, hnz, hζu _ hndvd, one_mul]`. Take `⟨t, ht⟩` from `hke`. Establish `hle : p ≤ p ^ k` using `Nat.le_self_pow (by omega) p`. Establish `hd1 : (p ^ 2 - 1) ∣ p ^ k - 1`.

Use `Nat.sub_dvd_pow_sub_pow (p ^ 2) 1 t` as an intermediate fact. Rewrite `this` using `[one_pow, ← pow_mul]`. Rewrite `this` using `[show 2 * t = k by omega]`. Then use the resulting hypothesis. Establish `hndvd : ¬ (p ^ 2 - 1) ∣ (p ^ k - p)`. Introduce `h`.

Establish `h2` using `Nat.dvd_sub hd1 h`. Establish `hpk'` using `hpk`. Establish `hle'` using `hle`. Rewrite using `[show p ^ k - 1 - (p ^ k - p) = p - 1 by`. Generalize the expression as in `p ^ k = r at hpk' hle' ⊢`.

Use the proof step `omega] at h2`. Establish `h3` using `Nat.le_of_dvd (by have := hp.two_le; omega) h2`. Establish `h4` using `hpq`. Establish `h5` using `hp.two_le`. Generalize the expression as in `p ^ 2 = q at h3 h4`.

Use linear arithmetic over natural numbers and integers. Rewrite using `[show ζ ^ (p ^ k) = ζ ^ p * ζ ^ (p ^ k - p) by`. Rewrite using `[← pow_add, Nat.add_sub_cancel' hle]]`. Rewrite using `[show ζ ^ p * ζ ^ (p ^ k - p) - ζ ^ p = ζ ^ p * (ζ ^ (p ^ k - p) - 1) by ring, norm_mul, norm_pow, hnz, one_pow, hζu _ hndvd, one_mul]`. Rewrite `hb` using `[norm_mul, hunit, one_mul]`.

Conclude with `hb`. Use `right`. Use `⟨k, hko, rfl, weak _ ?_⟩` and prove the remaining obligations. Establish `hk1 : 1 ≤ k` using `hko.pos`. Establish `hlt : p ^ (k - 1) < p ^ k` using `Nat.pow_lt_pow_right hp.one_lt (by omega)`.

Establish `hN0 : (p ^ k).choose (p ^ (k - 1)) ≠ 0` using `(Nat.choose_pos hlt.le).ne'`. Establish `hf` using `fact_choose_prime_pow hp k hk1`. Establish `hNd : (p ^ k).choose (p ^ (k - 1)) = p * ((p ^ k).choose (p ^ (k - 1)) / p)`. Use `Nat.ordProj_mul_ordCompl_eq_self ((p ^ k).choose (p ^ (k - 1))) p` as an intermediate fact. Rewrite `this` using `[hf, pow_one]`.

Conclude with `this.symm`. Establish `hNp : ¬ p ∣ (p ^ k).choose (p ^ (k - 1)) / p`. Use `Nat.not_dvd_ordCompl hp hN0` as an intermediate fact. Rewrite `this` using `[hf, pow_one]`. Then use the resulting hypothesis. Establish `hb` using `hbin (p ^ (k - 1)) (p ^ k - p ^ (k - 1)) (Nat.one_le_pow _ _ hp.pos) (Nat.sub_pos_of_lt hlt)`.

Establish `hs : p ^ (k - 1) + (p ^ k - p ^ (k - 1)) = p ^ k` using `Nat.add_sub_cancel' hlt.le`. Rewrite `hb` using `[hs, hNd, Nat.cast_mul, norm_mul, norm_nat_eq_one hp hp1 _ hNp, mul_one]`. Conclude with `hb`. Use `left`. Apply `strong` to reduce the goal to its premises.

Establish `hm2 : 2 ≤ m` using `by omega`. Establish `hj : 1 ≤ p ^ k * (m - 1)` using `Nat.one_le_iff_ne_zero.2 (Nat.mul_ne_zero (pow_ne_zero _ hp.ne_zero) (by omega))`. Establish `hb` using `hbin (p ^ k) (p ^ k * (m - 1)) hpk hj`. Establish `hs : p ^ k + p ^ k * (m - 1) = n`. Rewrite using `[← hnm]`.

Use `conv_rhs => rw [show m = 1 + (m - 1) by omega]`. Expand and normalize the polynomial expressions, which then agree. Establish `hch : ¬ p ∣ n.choose (p ^ k)`. Rewrite using `[← hnm]`. Introduce `hd`.

Establish `h` using `choose_pow_mul_modEq hp k m`. Unfold `Nat.ModEq at h`. Rewrite `hd` using `[Nat.dvd_iff_mod_eq_zero]`. Conclude with `hm (Nat.dvd_of_mod_eq_zero (by omega))`. Rewrite `hb` using `[hs, norm_nat_eq_one hp hp1 _ hch, one_mul]`.

Conclude with `hb`.
-/
theorem main (hCE : Formalism.ELL.CompExpWeight.{u}) : Formalism.ELL.EllipticTorsionWeights.{u} := by
  intro K _ _ _ p hp hp0 hp1 F l E g ζ hl hE0 hEl hlE hEb hζ hζu hhom hg0 hH hh _hg1 n
  set D : ℝ := (p : ℝ) ^ 2 - 1 with hD
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  have hDpos : 0 < D := by rw [hD]; nlinarith
  set c : ℝ := ‖(p : K)‖ ^ (1 / D) with hcdef
  have hc : 0 < c := Real.rpow_pos_of_pos hp0 _
  have hc1 : c ≤ 1 := Real.rpow_le_one (norm_nonneg _) hp1.le (by positivity)
  have cz : ∀ k : ℤ, c ^ k = ‖(p : K)‖ ^ ((k : ℝ) / D) := by
    intro k
    rw [hcdef, ← Real.rpow_intCast, ← Real.rpow_mul (norm_nonneg _)]
    congr 1
    ring
  have hEb' : ∀ n : ℕ, 1 ≤ n → ‖coeff n E‖ ≤ c ^ (1 - (n : ℤ)) := by
    intro m hm
    rw [cz]
    convert hEb m hm using 2
    push_cast
    ring
  set G : PowerSeries K := PowerSeries.subst E g with hGdef
  have hE' : PowerSeries.HasSubst E := PowerSeries.HasSubst.of_constantCoeff_zero' hE0

  have hbin : ∀ i j : ℕ, 1 ≤ i → 1 ≤ j →
      ‖(((i + j).choose i : ℕ) : K)‖ * ‖coeff (i + j) G‖ ≤ c ^ (-((i + j : ℕ) : ℤ)) := by
    intro i j hi hj
    have hS : MvPowerSeries.constantCoeff
        (MvPowerSeries.X 0 + MvPowerSeries.X 1 : MvPowerSeries (Fin 2) K) = 0 := by simp
    have hw := hCE K (Fin 2) c hc hc1 E hE0 hEb' _ hH (Finsupp.single 0 i + Finsupp.single 1 j)
    rw [add_identity (FK F).toPowerSeries (FK F).zero_constantCoeff l E g hl.1 hl.2.2 hE0 hEl hlE]
      at hw
    have e1 : MvPowerSeries.coeff (Finsupp.single 0 i + Finsupp.single 1 j)
        (PowerSeries.subst (MvPowerSeries.X 0 + MvPowerSeries.X 1 : MvPowerSeries (Fin 2) K) G) =
        (((i + j).choose i : ℕ) : K) * coeff (i + j) G := by
      rw [PowerSeries.coeff_subst (PowerSeries.HasSubst.of_constantCoeff_zero hS),
        finsum_eq_single _ (i + j)]
      · rw [coeff_X0_add_X1_pow, if_pos rfl, smul_eq_mul, mul_comm]
      · intro d hd
        rw [coeff_X0_add_X1_pow, if_neg (Ne.symm hd), smul_zero]
    have e2 : MvPowerSeries.coeff (Finsupp.single 0 i + Finsupp.single 1 j)
        (PowerSeries.subst (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) K) G) = 0 := by
      rw [PowerSeries.coeff_subst_single, if_neg]
      intro h
      have := congrArg (· 1) h
      simp at this
      omega
    have e3 : MvPowerSeries.coeff (Finsupp.single 0 i + Finsupp.single 1 j)
        (PowerSeries.subst (MvPowerSeries.X 1 : MvPowerSeries (Fin 2) K) G) = 0 := by
      rw [PowerSeries.coeff_subst_single, if_neg]
      intro h
      have := congrArg (· 0) h
      simp at this
      omega
    have edeg : (Finsupp.single (0 : Fin 2) i + Finsupp.single 1 j).degree = i + j := by
      rw [map_add, Finsupp.degree_single, Finsupp.degree_single]
    rw [map_sub, map_sub, e1, e2, e3, sub_zero, sub_zero, norm_mul, edeg] at hw
    exact_mod_cast hw

  have hpq : p < p ^ 2 := by
    rw [sq]; exact Nat.lt_mul_self_iff.2 hp.two_le
  have hq0 : p ^ 2 - 1 ≠ 0 := Nat.sub_ne_zero_of_lt (one_lt_pow' hp.one_lt (by norm_num))
  have hζ0 : ζ ≠ 0 := by
    rintro rfl
    rw [zero_pow hq0] at hζ
    exact zero_ne_one hζ
  have hnz : ‖ζ‖ = 1 := by
    have h1 : ‖ζ‖ ^ (p ^ 2 - 1) = 1 := by rw [← norm_pow, hζ, norm_one]
    exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) hq0).1 h1
  have hζbound : ∀ m : ℕ, ‖(ζ ^ m - ζ ^ p) * coeff m G‖ ≤ c ^ (-(m : ℤ)) := by
    intro m
    have hlz := log_rescale (FK F) l ζ hζ0 hl hhom
    have hEz := exp_rescale l E ζ hE0 hl.1 hEl hlE hlz
    have ha : PowerSeries.HasSubst (ζ • X : PowerSeries K) := PowerSeries.HasSubst.smul_X' ζ
    set h' : PowerSeries K := PowerSeries.subst (ζ • X : PowerSeries K) g - ζ ^ p • g with hh'
    have hid : (PowerSeries.subst E h' : PowerSeries K) = PowerSeries.rescale ζ G - ζ ^ p • G := by
      rw [hh', PowerSeries.subst_sub hE', PowerSeries.subst_smul hE',
        PowerSeries.subst_comp_subst_apply ha hE', PowerSeries.subst_smul hE', PowerSeries.subst_X hE',
        PowerSeries.rescale_eq_subst, hGdef, PowerSeries.subst_comp_subst_apply hE' ha, hEz]
    have hint : IntegralMv (ι := Unit) h' := by
      intro d
      have hd : d = Finsupp.single () (d ()) := by
        refine Finsupp.ext fun x => ?_
        cases x
        simp
      rw [hd]
      exact hh (d ())
    have hw := hCE K Unit c hc hc1 E hE0 hEb' h' hint (Finsupp.single () m)
    have hsub : (fun i : Unit => E.subst (MvPowerSeries.X i : MvPowerSeries Unit K)) = fun _ => E := by
      funext i
      cases i
      exact PowerSeries.X_subst E
    rw [hsub, ← PowerSeries.subst_def, hid, Finsupp.degree_single] at hw
    have hcm : MvPowerSeries.coeff (Finsupp.single () m) (PowerSeries.rescale ζ G - ζ ^ p • G) =
        (ζ ^ m - ζ ^ p) * coeff m G := by
      change coeff m (PowerSeries.rescale ζ G - ζ ^ p • G) = _
      rw [map_sub, PowerSeries.coeff_rescale, LinearMap.map_smul_of_tower, smul_eq_mul, sub_mul]
    rw [hcm] at hw
    exact hw
  have strong : ∀ x : K, ‖x‖ ≤ c ^ (-(n : ℤ)) → ‖x‖ ≤ ‖(p : K)‖ ^ (-(n : ℝ) / D) := by
    intro x hx
    rw [cz] at hx
    push_cast at hx
    exact hx
  have weak : ∀ x : K, ‖(p : K)‖ * ‖x‖ ≤ c ^ (-(n : ℤ)) →
      ‖x‖ ≤ ‖(p : K)‖ ^ (-1 - (n : ℝ) / D) := by
    intro x hx
    rw [cz] at hx
    push_cast at hx
    rw [show (-1 - (n : ℝ) / D) = -1 + (-(n : ℝ) / D) by ring, Real.rpow_add hp0, Real.rpow_neg_one,
      le_inv_mul_iff₀ hp0]
    exact hx
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · left
    have h0 : coeff 0 G = 0 := by
      rw [PowerSeries.coeff_zero_eq_constantCoeff_apply, hGdef]
      exact PowerSeries.constantCoeff_subst_eq_zero hE0 g hg0
    rw [h0, norm_zero]
    positivity
  obtain ⟨k, m, hnm, hm⟩ : ∃ k m, p ^ k * m = n ∧ ¬ p ∣ m :=
    ⟨_, _, Nat.ordProj_mul_ordCompl_eq_self n p, Nat.not_dvd_ordCompl hp hn.ne'⟩
  have hm0 : m ≠ 0 := by
    rintro rfl
    rw [mul_zero] at hnm
    omega
  have hpk : 1 ≤ p ^ k := Nat.one_le_pow _ _ hp.pos
  by_cases hm1 : m = 1
  · rw [hm1, mul_one] at hnm
    subst hnm
    rcases Nat.even_or_odd k with hke | hko
    · left
      apply strong
      have hb := hζbound (p ^ k)
      have hunit : ‖ζ ^ (p ^ k) - ζ ^ p‖ = 1 := by
        rcases Nat.eq_zero_or_pos k with rfl | hkpos
        · have hndvd : ¬ (p ^ 2 - 1) ∣ (p - 1) := by
            intro h
            have h3 := Nat.le_of_dvd (by have := hp.two_le; omega) h
            have h4 := hpq
            have h5 := hp.two_le
            generalize p ^ 2 = q at h3 h4
            omega
          rw [pow_zero, pow_one, show ζ ^ p = ζ * ζ ^ (p - 1) by
            rw [← pow_succ', Nat.sub_add_cancel hp.one_le]]
          rw [show ζ - ζ * ζ ^ (p - 1) = -(ζ * (ζ ^ (p - 1) - 1)) by ring, norm_neg, norm_mul, hnz,
            hζu _ hndvd, one_mul]
        · obtain ⟨t, ht⟩ := hke
          have hle : p ≤ p ^ k := Nat.le_self_pow (by omega) p
          have hd1 : (p ^ 2 - 1) ∣ p ^ k - 1 := by
            have := Nat.sub_dvd_pow_sub_pow (p ^ 2) 1 t
            rw [one_pow, ← pow_mul] at this
            rwa [show 2 * t = k by omega] at this
          have hndvd : ¬ (p ^ 2 - 1) ∣ (p ^ k - p) := by
            intro h
            have h2 := Nat.dvd_sub hd1 h
            have hpk' := hpk
            have hle' := hle
            rw [show p ^ k - 1 - (p ^ k - p) = p - 1 by
              generalize p ^ k = r at hpk' hle' ⊢; omega] at h2
            have h3 := Nat.le_of_dvd (by have := hp.two_le; omega) h2
            have h4 := hpq
            have h5 := hp.two_le
            generalize p ^ 2 = q at h3 h4
            omega
          rw [show ζ ^ (p ^ k) = ζ ^ p * ζ ^ (p ^ k - p) by
            rw [← pow_add, Nat.add_sub_cancel' hle]]
          rw [show ζ ^ p * ζ ^ (p ^ k - p) - ζ ^ p = ζ ^ p * (ζ ^ (p ^ k - p) - 1) by ring,
            norm_mul, norm_pow, hnz, one_pow, hζu _ hndvd, one_mul]
      rw [norm_mul, hunit, one_mul] at hb
      exact hb
    · right
      refine ⟨k, hko, rfl, weak _ ?_⟩
      have hk1 : 1 ≤ k := hko.pos
      have hlt : p ^ (k - 1) < p ^ k := Nat.pow_lt_pow_right hp.one_lt (by omega)
      have hN0 : (p ^ k).choose (p ^ (k - 1)) ≠ 0 := (Nat.choose_pos hlt.le).ne'
      have hf := fact_choose_prime_pow hp k hk1
      have hNd : (p ^ k).choose (p ^ (k - 1)) = p * ((p ^ k).choose (p ^ (k - 1)) / p) := by
        have := Nat.ordProj_mul_ordCompl_eq_self ((p ^ k).choose (p ^ (k - 1))) p
        rw [hf, pow_one] at this
        exact this.symm
      have hNp : ¬ p ∣ (p ^ k).choose (p ^ (k - 1)) / p := by
        have := Nat.not_dvd_ordCompl hp hN0
        rwa [hf, pow_one] at this
      have hb := hbin (p ^ (k - 1)) (p ^ k - p ^ (k - 1)) (Nat.one_le_pow _ _ hp.pos) (Nat.sub_pos_of_lt hlt)
      have hs : p ^ (k - 1) + (p ^ k - p ^ (k - 1)) = p ^ k := Nat.add_sub_cancel' hlt.le
      rw [hs, hNd, Nat.cast_mul, norm_mul, norm_nat_eq_one hp hp1 _ hNp, mul_one] at hb
      exact hb
  · left
    apply strong
    have hm2 : 2 ≤ m := by omega
    have hj : 1 ≤ p ^ k * (m - 1) := Nat.one_le_iff_ne_zero.2 (Nat.mul_ne_zero (pow_ne_zero _ hp.ne_zero) (by omega))
    have hb := hbin (p ^ k) (p ^ k * (m - 1)) hpk hj
    have hs : p ^ k + p ^ k * (m - 1) = n := by
      rw [← hnm]
      conv_rhs => rw [show m = 1 + (m - 1) by omega]
      ring
    have hch : ¬ p ∣ n.choose (p ^ k) := by
      rw [← hnm]
      intro hd
      have h := choose_pow_mul_modEq hp k m
      unfold Nat.ModEq at h
      rw [Nat.dvd_iff_mod_eq_zero] at hd
      exact hm (Nat.dvd_of_mod_eq_zero (by omega))
    rw [hs, norm_nat_eq_one hp hp1 _ hch, one_mul] at hb
    exact hb

end Formalism.ELL.Lemma2Aux

namespace Formalism.ELL

universe u

/- English proof (translation)
The claim follows from `Lemma2Aux.main comp_exp_coeff_weight`.
-/
theorem coefficient_weights_lemma_two : EllipticTorsionWeights.{u} := Lemma2Aux.main comp_exp_coeff_weight

end Formalism.ELL

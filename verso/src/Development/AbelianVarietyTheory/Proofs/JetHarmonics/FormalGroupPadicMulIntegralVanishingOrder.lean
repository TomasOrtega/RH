import Mathlib
import Development.AbelianVarietyTheory.Definitions.Jets.CmLatticeCommutatorPairingPowEqOneOfGoodLift
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.CpSeriesCoeffNormBoundedRingLaws
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.FormalGroupNatMulSeriesProperties
open PowerSeries GlobalTheory.MomOne
open scoped ComplexConjugate BigOperators Topology

namespace GlobalTheory.MomOne.FormalMul

section General
variable {K : Type*} [CommRing K]

/- English proof (translation)
The claim follows from `HasSubst.of_constantCoeff_zero' hf`.
-/
theorem hs {f : K⟦X⟧} (hf : constantCoeff f = 0) : HasSubst f := HasSubst.of_constantCoeff_zero' hf

/- English proof (translation)
The claim follows from `PowerSeries.constantCoeff_subst_eq_zero (τ := Unit) hg f hf`.
-/
theorem cc_subst {f g : K⟦X⟧} (hf : constantCoeff f = 0) (hg : constantCoeff g = 0) :
    constantCoeff (f.subst g : K⟦X⟧) = 0 :=
  PowerSeries.constantCoeff_subst_eq_zero (τ := Unit) hg f hf

/- English proof (translation)
The claim follows from `PowerSeries.subst_C r`.
-/
theorem subst_C' (g : K⟦X⟧) (r : K) : ((C r : K⟦X⟧).subst g : K⟦X⟧) = C r := PowerSeries.subst_C r

/- English proof (translation)
Establish `hfh : constantCoeff (f + h) = 0` using `by rw [map_add, hf, hh0, add_zero]`. Use `set M := 2 * N with hM`. Take `⟨V, P, hU⟩ : ∃ (V : K⟦X⟧) (P : Polynomial K), U = X ^ (M + 1) * V + (P : K⟦X⟧)` from `⟨_, _, eq_X_pow_mul_shift_add_trunc (M + 1) U⟩`. Establish `hD : d⁄dX K U = X ^ M * (((M + 1 : ℕ) : K⟦X⟧) * V + X * d⁄dX K V) + ((Polynomial.derivative P : Polynomial K) : K⟦X⟧)`. Rewrite using `[hU, map_add, derivative_coe, Derivation.leibniz, Derivation.leibniz_pow, derivative_X]`.

Simplify using `only [smul_eq_mul, nsmul_eq_mul, Nat.add_sub_cancel]`. Expand and normalize the polynomial expressions, which then agree. Take `⟨k, hk⟩` from `(P.map (algebraMap K K⟦X⟧)).binomExpansion f h`. Rewrite `hk` using `[Polynomial.derivative_map, Polynomial.eval_map_algebraMap, Polynomial.eval_map_algebraMap, Polynomial.eval_map_algebraMap]`. Rewrite using `[hD]`.

Rewrite using `[hU, subst_add (hs hfh), subst_add (hs hf), subst_add (hs hf), subst_mul (hs hfh), subst_mul (hs hf), subst_mul (hs hf), subst_pow (hs hfh), subst_pow (hs hf), subst_pow (hs hf), subst_X (hs hfh), subst_X (hs hf), subst_coe (hs hfh), subst_coe (hs hf), subst_coe (hs hf)]`. Establish `d1 : (X : K⟦X⟧) ^ M ∣ f ^ M` using `pow_dvd_pow_of_dvd (X_dvd_iff.2 hf) _`. Establish `d2 : (X : K⟦X⟧) ^ M ∣ (f + h) ^ M` using `pow_dvd_pow_of_dvd (X_dvd_iff.2 hfh) _`. Establish `d3 : (X : K⟦X⟧) ^ M ∣ h ^ 2`. Rewrite using `[hM, mul_comm, pow_mul]`.

Conclude with `pow_dvd_pow_of_dvd hh _`. Establish `key : ∀ a b c p0 p1 p2 : K⟦X⟧, p0 = p1 + p2 * h + k * h ^ 2 → (X : K⟦X⟧) ^ M ∣ (f + h) ^ (M + 1) * a + p0 - (f ^ (M + 1) * b + p1) - (f ^ M * c + p2) * h`. Introduce `a b c p0 p1 p2 e`. Establish `: (f + h) ^ (M + 1) * a + p0 - (f ^ (M + 1) * b + p1) - (f ^ M * c + p2) * h = (f + h) ^ M * ((f + h) * a) - f ^ M * (f * b + c * h) + h ^ 2 * k`. Rewrite using `[e]`.

Expand and normalize the polynomial expressions, which then agree. Rewrite using `[this]`. Conclude with `dvd_add (dvd_sub (d2.mul_right _) (d1.mul_right _)) (d3.mul_right _)`. Conclude with `key _ _ _ _ _ _ hk`.
-/
theorem taylor_dvd (U f h : K⟦X⟧) (N : ℕ) (hf : constantCoeff f = 0) (hh0 : constantCoeff h = 0)
    (hh : X ^ N ∣ h) :
    (X : K⟦X⟧) ^ (2 * N) ∣ (U.subst (f + h) : K⟦X⟧) - U.subst f - (d⁄dX K U).subst f * h := by
  have hfh : constantCoeff (f + h) = 0 := by rw [map_add, hf, hh0, add_zero]
  set M := 2 * N with hM
  obtain ⟨V, P, hU⟩ : ∃ (V : K⟦X⟧) (P : Polynomial K), U = X ^ (M + 1) * V + (P : K⟦X⟧) :=
    ⟨_, _, eq_X_pow_mul_shift_add_trunc (M + 1) U⟩
  have hD : d⁄dX K U = X ^ M * (((M + 1 : ℕ) : K⟦X⟧) * V + X * d⁄dX K V) +
      ((Polynomial.derivative P : Polynomial K) : K⟦X⟧) := by
    rw [hU, map_add, derivative_coe, Derivation.leibniz, Derivation.leibniz_pow, derivative_X]
    simp only [smul_eq_mul, nsmul_eq_mul, Nat.add_sub_cancel]
    ring
  obtain ⟨k, hk⟩ := (P.map (algebraMap K K⟦X⟧)).binomExpansion f h
  rw [Polynomial.derivative_map, Polynomial.eval_map_algebraMap, Polynomial.eval_map_algebraMap,
    Polynomial.eval_map_algebraMap] at hk
  rw [hD]
  rw [hU, subst_add (hs hfh), subst_add (hs hf), subst_add (hs hf), subst_mul (hs hfh), subst_mul (hs hf),
    subst_mul (hs hf), subst_pow (hs hfh), subst_pow (hs hf), subst_pow (hs hf), subst_X (hs hfh), subst_X (hs hf),
    subst_coe (hs hfh), subst_coe (hs hf), subst_coe (hs hf)]
  have d1 : (X : K⟦X⟧) ^ M ∣ f ^ M := pow_dvd_pow_of_dvd (X_dvd_iff.2 hf) _
  have d2 : (X : K⟦X⟧) ^ M ∣ (f + h) ^ M := pow_dvd_pow_of_dvd (X_dvd_iff.2 hfh) _
  have d3 : (X : K⟦X⟧) ^ M ∣ h ^ 2 := by
    rw [hM, mul_comm, pow_mul]; exact pow_dvd_pow_of_dvd hh _
  have key : ∀ a b c p0 p1 p2 : K⟦X⟧, p0 = p1 + p2 * h + k * h ^ 2 →
      (X : K⟦X⟧) ^ M ∣ (f + h) ^ (M + 1) * a + p0 - (f ^ (M + 1) * b + p1) - (f ^ M * c + p2) * h := by
    intro a b c p0 p1 p2 e
    have : (f + h) ^ (M + 1) * a + p0 - (f ^ (M + 1) * b + p1) - (f ^ M * c + p2) * h
        = (f + h) ^ M * ((f + h) * a) - f ^ M * (f * b + c * h) + h ^ 2 * k := by
      rw [e]; ring
    rw [this]
    exact dvd_add (dvd_sub (d2.mul_right _) (d1.mul_right _)) (d3.mul_right _)
  exact key _ _ _ _ _ _ hk

/- English proof (translation)
Establish `hb` using `GlobalTheory.ConvSer.nMul_hasSubst_pair hf hg`. Establish `hX : ∀ i : Fin 2, MvPowerSeries.constantCoeff (MvPowerSeries.X i : MvPowerSeries (Fin 2) K) = 0` using `by simp`. Establish `comp : ∀ a : MvPowerSeries (Fin 2) K, MvPowerSeries.constantCoeff a = 0 → MvPowerSeries.subst (![f, g] : Fin 2 → MvPowerSeries Unit K) (PowerSeries.subst a U) = PowerSeries.subst (MvPowerSeries.subst (![f, g] : Fin 2 → MvPowerSeries Unit K) a) U`. Introduce `a ha`. Rewrite using `[PowerSeries.subst, MvPowerSeries.subst_comp_subst_apply (HasSubst.of_constantCoeff_zero ha).const hb]`.

Both sides reduce to the same expression. Establish `ha : MvPowerSeries.HasSubst (![PowerSeries.subst (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) K) U, PowerSeries.subst (MvPowerSeries.X 1 : MvPowerSeries (Fin 2) K) U] : Fin 2 → MvPowerSeries (Fin 2) K)`. Use `MvPowerSeries.hasSubst_of_constantCoeff_zero fun s => ?_` and prove the remaining obligations. Use `fin_cases s`. Conclude with `PowerSeries.constantCoeff_subst_eq_zero (hX 0) U hU`.

Conclude with `PowerSeries.constantCoeff_subst_eq_zero (hX 1) U hU`. Use `congrArg (MvPowerSeries.subst (R := K) (![f, g] : Fin 2 → MvPowerSeries Unit K)) hG` as an intermediate fact. Rewrite `this` using `[MvPowerSeries.subst_comp_subst_apply ha hb, comp _ (by simp), MvPowerSeries.subst_add hb, MvPowerSeries.subst_X hb, MvPowerSeries.subst_X hb]`. Use `Eq.trans ?_ this` and prove the remaining obligations. Use `congr! 2 with s`.

Use `fin_cases s`. Simplify using `only [Fin.zero_eta, Matrix.cons_val_zero]`. Rewrite using `[comp _ (hX 0), MvPowerSeries.subst_X hb]`. Both sides reduce to the same expression. Simplify using `only [Fin.mk_one, Matrix.cons_val_one, Matrix.cons_val_fin_one]`.

Rewrite using `[comp _ (hX 1), MvPowerSeries.subst_X hb]`. Both sides reduce to the same expression.
-/
theorem add_law (G : MvPowerSeries (Fin 2) K) (U : K⟦X⟧) (hU : constantCoeff U = 0)
    (hG : MvPowerSeries.subst (![PowerSeries.subst (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) K) U,
      PowerSeries.subst (MvPowerSeries.X 1 : MvPowerSeries (Fin 2) K) U] : Fin 2 → MvPowerSeries (Fin 2) K) G
      = PowerSeries.subst (MvPowerSeries.X 0 + MvPowerSeries.X 1 : MvPowerSeries (Fin 2) K) U)
    (f g : K⟦X⟧) (hf : constantCoeff f = 0) (hg : constantCoeff g = 0) :
    (MvPowerSeries.subst (![U.subst f, U.subst g] : Fin 2 → MvPowerSeries Unit K) G : K⟦X⟧) = U.subst (f + g) := by
  have hb := GlobalTheory.ConvSer.nMul_hasSubst_pair hf hg
  have hX : ∀ i : Fin 2, MvPowerSeries.constantCoeff (MvPowerSeries.X i : MvPowerSeries (Fin 2) K) = 0 := by simp
  have comp : ∀ a : MvPowerSeries (Fin 2) K, MvPowerSeries.constantCoeff a = 0 →
      MvPowerSeries.subst (![f, g] : Fin 2 → MvPowerSeries Unit K) (PowerSeries.subst a U)
        = PowerSeries.subst (MvPowerSeries.subst (![f, g] : Fin 2 → MvPowerSeries Unit K) a) U := by
    intro a ha
    rw [PowerSeries.subst, MvPowerSeries.subst_comp_subst_apply (HasSubst.of_constantCoeff_zero ha).const hb]
    rfl
  have ha : MvPowerSeries.HasSubst (![PowerSeries.subst (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) K) U,
      PowerSeries.subst (MvPowerSeries.X 1 : MvPowerSeries (Fin 2) K) U] : Fin 2 → MvPowerSeries (Fin 2) K) := by
    refine MvPowerSeries.hasSubst_of_constantCoeff_zero fun s => ?_
    fin_cases s
    · exact PowerSeries.constantCoeff_subst_eq_zero (hX 0) U hU
    · exact PowerSeries.constantCoeff_subst_eq_zero (hX 1) U hU
  have := congrArg (MvPowerSeries.subst (R := K) (![f, g] : Fin 2 → MvPowerSeries Unit K)) hG
  rw [MvPowerSeries.subst_comp_subst_apply ha hb, comp _ (by simp), MvPowerSeries.subst_add hb,
    MvPowerSeries.subst_X hb, MvPowerSeries.subst_X hb] at this
  refine Eq.trans ?_ this
  congr! 2 with s
  fin_cases s
  · simp only [Fin.zero_eta, Matrix.cons_val_zero]
    rw [comp _ (hX 0), MvPowerSeries.subst_X hb]; rfl
  · simp only [Fin.mk_one, Matrix.cons_val_one, Matrix.cons_val_fin_one]
    rw [comp _ (hX 1), MvPowerSeries.subst_X hb]; rfl

/- English proof (translation)
Rewrite using `[← derivative_subst (hs hℓ), h, derivative_X]`.
-/
theorem deriv_mul_eq_one {U ℓ : K⟦X⟧} (hℓ : constantCoeff ℓ = 0) (h : U.subst ℓ = (X : K⟦X⟧)) :
    ((d⁄dX K U).subst ℓ : K⟦X⟧) * d⁄dX K ℓ = 1 := by
  rw [← derivative_subst (hs hℓ), h, derivative_X]

/- English proof (translation)
Establish `h1` using `congrArg constantCoeff (deriv_mul_eq_one hℓ h)`. Rewrite `h1` using `[map_mul, map_one, ← coeff_zero_eq_constantCoeff_apply (d⁄dX K ℓ), coeff_derivative]`. Simplify using `only [zero_add, Nat.cast_zero, mul_one] at h1`. Establish `: Invertible (coeff 1 ℓ)` using `⟨_, h1, by rw [mul_comm]; exact h1⟩`. Establish `h2` using `subst_substInv_right ℓ hℓ`.

Establish `hV : HasSubst ℓ.substInv` using `hs (by simp)`. Establish `: U = ℓ.substInv`. Use `subst_comp_subst_apply (hs hℓ) hV U` as an intermediate fact. Rewrite `this` using `[h, h2, subst_X hV]`. Rewrite using `[this, ← PowerSeries.map_algebraMap_eq_subst_X]`.

Simplify using the standard rewrite rules. Rewrite using `[this, h2]`.
-/
theorem subst_inv {U ℓ : K⟦X⟧} (hℓ : constantCoeff ℓ = 0) (h : U.subst ℓ = (X : K⟦X⟧)) :
    ℓ.subst U = (X : K⟦X⟧) := by
  have h1 := congrArg constantCoeff (deriv_mul_eq_one hℓ h)
  rw [map_mul, map_one, ← coeff_zero_eq_constantCoeff_apply (d⁄dX K ℓ), coeff_derivative] at h1
  simp only [zero_add, Nat.cast_zero, mul_one] at h1
  have : Invertible (coeff 1 ℓ) := ⟨_, h1, by rw [mul_comm]; exact h1⟩
  have h2 := subst_substInv_right ℓ hℓ
  have hV : HasSubst ℓ.substInv := hs (by simp)
  have : U = ℓ.substInv := by
    have := subst_comp_subst_apply (hs hℓ) hV U
    rw [h, h2, subst_X hV] at this
    rw [this, ← PowerSeries.map_algebraMap_eq_subst_X]; simp
  rw [this, h2]

/- English proof (translation)
Rewrite using `[coeff_subst' (hs (by simp [hℓ])), finsum_eq_sum_of_support_subset (s := Finset.range (n + 1))]`. Use `Finset.sum_congr rfl fun d _ => ?_` and prove the remaining obligations. Rewrite using `[mul_pow, ← map_pow, coeff_C_mul, smul_eq_mul]`. Introduce `d hd`. Assume the negation of the conclusion as `hn`.

Apply `hd` to reduce the goal to its premises. Simplify using `only [Finset.coe_range, Set.mem_Iio, not_lt] at hn`. Establish `: coeff n (ℓ ^ d) = 0` using `X_pow_dvd_iff.1 (pow_dvd_pow_of_dvd (X_dvd_iff.2 hℓ) d) n (by omega)`. Use `show _ • _ = _`. Rewrite using `[mul_pow, ← map_pow, coeff_C_mul, this, mul_zero, smul_zero]`.
-/
theorem coeff_subst_C_mul (U ℓ : K⟦X⟧) (hℓ : constantCoeff ℓ = 0) (n : ℕ) (a : K) :
    coeff n (U.subst (C a * ℓ) : K⟦X⟧) = ∑ d ∈ Finset.range (n + 1), coeff d U * (a ^ d * coeff n (ℓ ^ d)) := by
  rw [coeff_subst' (hs (by simp [hℓ])), finsum_eq_sum_of_support_subset (s := Finset.range (n + 1))]
  · refine Finset.sum_congr rfl fun d _ => ?_
    rw [mul_pow, ← map_pow, coeff_C_mul, smul_eq_mul]
  · intro d hd
    by_contra hn
    apply hd
    simp only [Finset.coe_range, Set.mem_Iio, not_lt] at hn
    have : coeff n (ℓ ^ d) = 0 := X_pow_dvd_iff.1 (pow_dvd_pow_of_dvd (X_dvd_iff.2 hℓ) d) n (by omega)
    show _ • _ = _
    rw [mul_pow, ← map_pow, coeff_C_mul, this, mul_zero, smul_zero]

end General

section Padic
variable {q : ℕ} [Fact q.Prime]

/- English proof (translation)
Rewrite using `[PadicComplexInt, Valuation.mem_valuationSubring_iff, PadicComplex.norm_eq_norm, Valuation.norm_def, PadicComplex.RankOne.hom_eq_embedding, Valuation.embedding_restrict]`. Conclude with `Iff.rfl` after adjusting the coercions.
-/
theorem mem_int_iff (x : ℂ_[q]) : x ∈ 𝓞_ℂ_[q] ↔ ‖x‖ ≤ 1 := by
  rw [PadicComplexInt, Valuation.mem_valuationSubring_iff, PadicComplex.norm_eq_norm, Valuation.norm_def,
    PadicComplex.RankOne.hom_eq_embedding, Valuation.embedding_restrict]
  exact_mod_cast Iff.rfl

/- English proof (translation)
Introduce `n`. Rewrite using `[coeff_map]`. Conclude with `(mem_int_iff _).1 (coeff n f).2`.
-/
theorem bd_map (f : 𝓞_ℂ_[q]⟦X⟧) : Bd 1 (PowerSeries.map (algebraMap 𝓞_ℂ_[q] ℂ_[q]) f) := by
  intro n
  rw [coeff_map]
  exact (mem_int_iff _).1 (coeff n f).2

/- English proof (translation)
Rewrite using `[zc, norm_algebraMap']`. Both sides reduce to the same expression.
-/
theorem norm_zc (a : ℤ_[q]) : ‖zc a‖ = ‖a‖ := by
  rw [zc, norm_algebraMap']; rfl

/- English proof (translation)
Simplify using `[zc]`.
-/
theorem zc_natCast (n : ℕ) : zc (n : ℤ_[q]) = (n : ℂ_[q]) := by simp [zc]

/- English proof (translation)
Simplify using `[zc]`.
-/
theorem zc_mul (a b : ℤ_[q]) : zc (a * b) = zc a * zc b := by simp [zc]

/- English proof (translation)
The claim follows from `(continuous_algebraMap ℚ_[q] ℂ_[q]).comp continuous_subtype_val`.
-/
theorem continuous_zc : Continuous (zc : ℤ_[q] → ℂ_[q]) :=
  (continuous_algebraMap ℚ_[q] ℂ_[q]).comp continuous_subtype_val

def Van (m : ℕ) (f : ℂ_[q]⟦X⟧) : Prop := ∀ n < m, ‖coeff n f‖ < 1

/- English proof (translation)
The claim follows from `(IsUltrametricDist.norm_add_le_max x y).trans_lt (max_lt hx hy)`.
-/
theorem norm_add_lt {x y : ℂ_[q]} (hx : ‖x‖ < 1) (hy : ‖y‖ < 1) : ‖x + y‖ < 1 :=
  (IsUltrametricDist.norm_add_le_max x y).trans_lt (max_lt hx hy)

/- English proof (translation)
Rewrite using `[norm_mul]`. Conclude with `mul_lt_one_of_nonneg_of_lt_one_left (norm_nonneg _) hx hy`.
-/
theorem norm_mul_lt_left {x y : ℂ_[q]} (hx : ‖x‖ < 1) (hy : ‖y‖ ≤ 1) : ‖x * y‖ < 1 := by
  rw [norm_mul]
  exact mul_lt_one_of_nonneg_of_lt_one_left (norm_nonneg _) hx hy

/- English proof (translation)
Introduce `n hn`. Rewrite using `[coeff_mul]`. Use `Finset.sum_induction _ (fun x => ‖x‖ < 1) (fun _ _ => norm_add_lt) (by simp) ?_` and prove the remaining obligations. Introduce `p hp`. Establish `hp' : p.1 + p.2 = n` using `Finset.HasAntidiagonal.mem_antidiagonal.1 hp`.

Distinguish the cases in `h : p.1 < a`. Conclude with `norm_mul_lt_left (ha _ h) (hg _)`. Rewrite using `[mul_comm]`. Conclude with `norm_mul_lt_left (hb _ (by omega)) (hf _)`.
-/
theorem van_mul {f g : ℂ_[q]⟦X⟧} {a b : ℕ} (hf : Bd 1 f) (hg : Bd 1 g) (ha : Van a f) (hb : Van b g) :
    Van (a + b) (f * g) := by
  intro n hn
  rw [coeff_mul]
  refine Finset.sum_induction _ (fun x => ‖x‖ < 1) (fun _ _ => norm_add_lt) (by simp) ?_
  intro p hp
  have hp' : p.1 + p.2 = n := Finset.HasAntidiagonal.mem_antidiagonal.1 hp
  by_cases h : p.1 < a
  · exact norm_mul_lt_left (ha _ h) (hg _)
  · rw [mul_comm]
    exact norm_mul_lt_left (hb _ (by omega)) (hf _)

/- English proof (translation)
Proceed by induction on `d with`. Consider the case `zero`. Introduce `n`. Rewrite using `[pow_zero, coeff_one]`. Apply the tactic sequence `split_ifs <;> simp`.

Consider the case `succ d ih`. Use `((sup_norm_laws q).1 _ _ _ _ ih hg).2` as an intermediate fact. Rewrite `this` using `[one_mul, ← pow_succ]`. Then use the resulting hypothesis.
-/
theorem bd_pow {g : ℂ_[q]⟦X⟧} (hg : Bd 1 g) (d : ℕ) : Bd 1 (g ^ d) := by
  induction d with
  | zero =>
    intro n
    rw [pow_zero, coeff_one]
    split_ifs <;> simp
  | succ d ih =>
    have := ((sup_norm_laws q).1 _ _ _ _ ih hg).2
    rwa [one_mul, ← pow_succ] at this

/- English proof (translation)
Proceed by induction on `d with`. Consider the case `zero => intro n hn`. Use linear arithmetic over natural numbers and integers. Consider the case `succ d ih`. Rewrite using `[add_mul, one_mul, pow_succ]`.

Conclude with `van_mul (bd_pow hg d) hg ih hr`.
-/
theorem van_pow {g : ℂ_[q]⟦X⟧} {r : ℕ} (hg : Bd 1 g) (hr : Van r g) (d : ℕ) : Van (d * r) (g ^ d) := by
  induction d with
  | zero => intro n hn; omega
  | succ d ih =>
    rw [add_mul, one_mul, pow_succ]
    exact van_mul (bd_pow hg d) hg ih hr

/- English proof (translation)
Introduce `n hn`. Rewrite using `[coeff_subst' (hs h0)]`. Use `finsum_induction (fun x => ‖x‖ < 1) (by simp) (fun _ _ => norm_add_lt) fun d => ?_` and prove the remaining obligations. Rewrite using `[smul_eq_mul]`. Distinguish the cases in `h : d < m`.

Conclude with `norm_mul_lt_left (hm _ h) (bd_pow hg d n)`. Rewrite using `[mul_comm]`. Conclude with `norm_mul_lt_left (van_pow hg hr d n (hn.trans_le (Nat.mul_le_mul_right r (by omega)))) (hf d)`.
-/
theorem van_subst {f g : ℂ_[q]⟦X⟧} {m r : ℕ} (hf : Bd 1 f) (hg : Bd 1 g) (h0 : constantCoeff g = 0)
    (hm : Van m f) (hr : Van r g) : Van (m * r) (f.subst g) := by
  intro n hn
  rw [coeff_subst' (hs h0)]
  refine finsum_induction (fun x => ‖x‖ < 1) (by simp) (fun _ _ => norm_add_lt) fun d => ?_
  rw [smul_eq_mul]
  by_cases h : d < m
  · exact norm_mul_lt_left (hm _ h) (bd_pow hg d n)
  · rw [mul_comm]
    exact norm_mul_lt_left (van_pow hg hr d n (hn.trans_le (Nat.mul_le_mul_right r (by omega)))) (hf d)

/- English proof (translation)
Use `symm`. Use `(MvPowerSeries.map_subst (GlobalTheory.ConvSer.nMul_hasSubst_pair hf hg) _).trans ?_` and prove the remaining obligations. Use `congr! 2 with s`. Apply the tactic sequence `fin_cases s <;> rfl`.
-/
theorem map_law (F : FormalGroup 𝓞_ℂ_[q]) (f g : 𝓞_ℂ_[q]⟦X⟧) (hf : constantCoeff f = 0) (hg : constantCoeff g = 0) :
    (MvPowerSeries.subst (![PowerSeries.map (algebraMap 𝓞_ℂ_[q] ℂ_[q]) f, PowerSeries.map (algebraMap 𝓞_ℂ_[q] ℂ_[q]) g] :
      Fin 2 → MvPowerSeries Unit ℂ_[q]) (MvPowerSeries.map (algebraMap 𝓞_ℂ_[q] ℂ_[q]) F.toPowerSeries) : ℂ_[q]⟦X⟧)
    = PowerSeries.map (algebraMap 𝓞_ℂ_[q] ℂ_[q])
      (MvPowerSeries.subst (![f, g] : Fin 2 → MvPowerSeries Unit 𝓞_ℂ_[q]) F.toPowerSeries) := by
  symm
  refine (MvPowerSeries.map_subst (GlobalTheory.ConvSer.nMul_hasSubst_pair hf hg) _).trans ?_
  congr! 2 with s
  fin_cases s <;> rfl

end Padic

/- English proof (translation)
Introduce `q hq F U ℓ hU hℓ hUℓ hG`. Establish `law` using `add_law _ U hU hG`. Establish `hinv` using `subst_inv hℓ hUℓ`. Establish `hc : ∀ a : ℂ_[q], constantCoeff (C a * ℓ) = 0` using `fun a => by simp [hℓ]`. Establish `hB0 : ∀ a : ℂ_[q], constantCoeff (U.subst (C a * ℓ) : ℂ_[q]⟦X⟧) = 0` using `fun a => cc_subst hU (hc a)`.

Establish `hℓB : ∀ a : ℂ_[q], (ℓ.subst (U.subst (C a * ℓ) : ℂ_[q]⟦X⟧) : ℂ_[q]⟦X⟧) = C a * ℓ` using `fun a => by`. Rewrite using `[← subst_comp_subst_apply (hs hU) (hs (hc a)), hinv, subst_X (hs (hc a))]`. Establish `hcomp : ∀ a b : ℂ_[q], (PowerSeries.subst (U.subst (C b * ℓ) : ℂ_[q]⟦X⟧) (U.subst (C a * ℓ) : ℂ_[q]⟦X⟧) : ℂ_[q]⟦X⟧) = U.subst (C (a * b) * ℓ)` using `fun a b => by`. Rewrite using `[subst_comp_subst_apply (hs (hc a)) (hs (hB0 b)), subst_mul (hs (hB0 b)), subst_C', hℓB, map_mul, mul_assoc]`. Establish `hnat : ∀ n : ℕ, (U.subst (C (n : ℂ_[q]) * ℓ) : ℂ_[q]⟦X⟧) = PowerSeries.map (algebraMap 𝓞_ℂ_[q] ℂ_[q]) (GlobalTheory.ConvSer.nMul F n)`.

Introduce `n`. Proceed by induction on `n with`. Consider the case `zero`. Use extensionality with `m`. Rewrite using `[coeff_subst_C_mul U ℓ hℓ, GlobalTheory.ConvSer.nMul_zero, map_zero, map_zero]`.

Use `Finset.sum_eq_zero fun d _ => ?_` and prove the remaining obligations. Break down `d with _ | d` into its components or cases. Simplify using `[hU]`. Simplify using the standard rewrite rules. Consider the case `succ n ih`.

Rewrite using `[GlobalTheory.ConvSer.nMul_succ, ← map_law F _ _ (GlobalTheory.ConvSer.nMul_constantCoeff F n) constantCoeff_X, ← ih, map_X]`. Use `law _ _ (hc n) hℓ` as an intermediate fact. Rewrite `this` using `[hUℓ]`. Rewrite using `[this]`. Use `congr 1`.

Use `push_cast`. Rewrite using `[map_add, map_one]`. Expand and normalize the polynomial expressions, which then agree. Establish `hint : ∀ a : ℤ_[q], Bd 1 (U.subst (C (zc a) * ℓ))`. Introduce `a m`.

Use `PadicInt.denseRange_natCast.induction_on (p := fun a => ‖coeff m (U.subst (C (zc a) * ℓ) : ℂ_[q]⟦X⟧)‖ ≤ 1) a ?_ fun n => ?_` and prove the remaining obligations. Simplify using `only [coeff_subst_C_mul U ℓ hℓ]`. Use `continuous_zc (q := q)` as an intermediate fact. Conclude with `isClosed_le (by fun_prop) continuous_const`. Rewrite using `[zc_natCast, hnat]`.

Conclude with `bd_map _ m`. Establish `hBq : Bd 1 (U.subst (C (q : ℂ_[q]) * ℓ))`. Use `hint q` as an intermediate fact. Rewrite `this` using `[zc_natCast]`. Then use the resulting hypothesis. Establish `hone` using `deriv_mul_eq_one hℓ hUℓ`.

Use `set W : ℂ_[q]⟦X⟧ := C (coeff 1 ℓ) * (d⁄dX ℂ_[q] U).subst ℓ with hW`. Establish `hW0 : constantCoeff W = 1`. Establish `h1` using `congrArg constantCoeff hone`. Rewrite `h1` using `[map_mul, map_one, ← coeff_zero_eq_constantCoeff_apply (d⁄dX _ ℓ), coeff_derivative]`. Simplify using `only [zero_add, Nat.cast_zero, mul_one] at h1`.

Rewrite using `[hW, map_mul, constantCoeff_C, mul_comm, h1]`. Establish `hWint : Bd 1 W`. Introduce `m`. Use `set N := m + 2 with hN`. Establish `hXN : constantCoeff (X ^ N : ℂ_[q]⟦X⟧) = 0` using `by simp [hN]`.

Use `set h : ℂ_[q]⟦X⟧ := ℓ.subst (X ^ N : ℂ_[q]⟦X⟧) with hh`. Establish `hh0 : constantCoeff h = 0` using `cc_subst hℓ hXN`. Establish `hUh : (U.subst h : ℂ_[q]⟦X⟧) = X ^ N`. Rewrite using `[hh, ← subst_comp_subst_apply (hs hℓ) (hs hXN), hUℓ, subst_X (hs hXN)]`. Choose the witnesses or unpack the hypotheses as in `⟨V, hV⟩ : ∃ V : ℂ_[q]⟦X⟧, ℓ = C (coeff 1 ℓ) * X + X ^ 2 * V := by`.

Establish `: (X : ℂ_[q]⟦X⟧) ^ 2 ∣ ℓ - C (coeff 1 ℓ) * X`. Rewrite using `[X_pow_dvd_iff]`. Introduce `j hj`. Use `interval_cases j`. Simplify using `[hℓ]`.

Simplify using the standard rewrite rules. Take `⟨V, hV⟩` from `this`. Conclude with `⟨V, by rw [← hV]; ring⟩`. Establish `hh' : h = C (coeff 1 ℓ) * X ^ N + X ^ (2 * N) * V.subst (X ^ N : ℂ_[q]⟦X⟧)`. Rewrite using `[hh]`.

Use `conv_lhs => rw [hV]`. Rewrite using `[subst_add (hs hXN), subst_mul (hs hXN), subst_mul (hs hXN), subst_pow (hs hXN), subst_C', subst_X (hs hXN), ← pow_mul, mul_comm N 2]`. Establish `hd : (X : ℂ_[q]⟦X⟧) ^ N ∣ h`. Rewrite using `[hh']`. Conclude with `dvd_add (dvd_mul_left _ _) ((pow_dvd_pow _ (by omega)).mul_right _)`.

Take `⟨T, hT⟩` from `taylor_dvd U ℓ h N hℓ hh0 hd`. Establish `hl` using `law _ _ hℓ hh0`. Establish `hb` using `map_law F X (X ^ N) constantCoeff_X (by simp [hN])`. Rewrite `hb` using `[map_pow, map_X]`. Rewrite `hl` using `[hUℓ, hUh, hb]`.

Establish `hbd : Bd 1 (U.subst (ℓ + h))` using `hl ▸ bd_map _`. Establish `e : (U.subst (ℓ + h) : ℂ_[q]⟦X⟧) = X + X ^ N * W + X ^ (2 * N) * (T + (d⁄dX ℂ_[q] U).subst ℓ * V.subst (X ^ N : ℂ_[q]⟦X⟧))`. Rewrite `hT` using `[hUℓ]`. Rewrite using `[hW]`. Take the linear combination `hT + ((d⁄dX ℂ_[q] U).subst ℓ : ℂ_[q]⟦X⟧) * hh'`.

Use `hbd (m + N)` as an intermediate fact. Rewrite `this` using `[e, map_add, map_add, coeff_X_pow_mul, coeff_X, if_neg (by omega), coeff_X_pow_mul', if_neg (by omega)]`. Simplify using `using this`. Establish `hq1 : ‖(q : ℂ_[q])‖ < 1`. Rewrite using `[← zc_natCast, norm_zc, PadicInt.norm_p]`.

Conclude with `inv_lt_one_of_one_lt₀ (by exact_mod_cast hq.out.one_lt)`. Establish `hder : Bd ‖(q : ℂ_[q])‖ (d⁄dX ℂ_[q] (U.subst (C (q : ℂ_[q]) * ℓ)))`. Use `(sup_norm_laws q).2.2.2.2.2 _ W 0 _ hWint (by rw [hW0, norm_one]) ?_` and prove the remaining obligations. Establish `e : X ^ 0 * W * d⁄dX ℂ_[q] (U.subst (C (q : ℂ_[q]) * ℓ)) = C (q : ℂ_[q]) * W.subst (U.subst (C (q : ℂ_[q]) * ℓ) : ℂ_[q]⟦X⟧)`. Rewrite using `[derivative_subst (hs (hc q)), hW, subst_mul (hs (hB0 q)), subst_C', subst_comp_subst_apply (hs hℓ) (hs (hB0 q)), hℓB, Derivation.leibniz, derivative_C]`.

Simplify using `only [smul_eq_mul]`. Take the linear combination `(C (coeff 1 ℓ) * C (q : ℂ_[q]) * ((d⁄dX ℂ_[q] U).subst (C (q : ℂ_[q]) * ℓ) : ℂ_[q]⟦X⟧)) * hone`. Rewrite using `[e]`. Introduce `n`. Rewrite using `[coeff_C_mul, norm_mul]`.

Conclude with `mul_le_of_le_one_right (norm_nonneg _) ((sup_norm_laws q).2.1 W _ 1 hWint hBq (hB0 q) n)`. Establish `h2 : ∀ k, ¬ q ∣ k → ‖coeff k (U.subst (C (q : ℂ_[q]) * ℓ) : ℂ_[q]⟦X⟧)‖ < 1`. Introduce `k hk`. Break down `k with _ | k` into its components or cases. Conclude with `absurd (dvd_zero q) hk`.

Use `hder k` as an intermediate fact. Rewrite `this` using `[coeff_derivative, norm_mul]`. Establish `hk1 : ‖((k : ℂ_[q]) + 1)‖ = 1`. Rewrite using `[← Nat.cast_succ, ← zc_natCast, norm_zc, PadicInt.norm_natCast_eq_one_iff]`. Conclude with `(Nat.Prime.coprime_iff_not_dvd hq.out).2 hk`.

Rewrite `this` using `[hk1, mul_one]`. Conclude with `this.trans_lt hq1`. Use `⟨hint, h2, fun hqq k a ha => ?_⟩` and prove the remaining obligations. Establish `hv : Van (2 * q) (U.subst (C (q : ℂ_[q]) * ℓ))`. Introduce `n hn`.

Distinguish the cases in `hd : q ∣ n`. Take `⟨c, rfl⟩` from `hd`. Establish `hc2 : c < 2`. Assume the negation of the conclusion as `h`. Establish `: q * 2 ≤ q * c` using `Nat.mul_le_mul_left q (by omega)`.

Use linear arithmetic over natural numbers and integers. Use `interval_cases c`. Rewrite using `[mul_zero, coeff_zero_eq_constantCoeff_apply, hB0]`. Simplify using the standard rewrite rules. Rewrite using `[mul_one]` and apply the resulting hypothesis.

Conclude with `h2 n hd`. Take `⟨v, rfl⟩` from `Ideal.mem_span_singleton'.1 ((PadicInt.norm_le_pow_iff_mem_span_pow a k).1 ha)`. Use `clear ha`. Use `show Van _ _`. Proceed by induction on `k with`.

Consider the case `zero`. Introduce `n hn`. Take `rfl : n = 0` from `by simpa using hn`. Rewrite using `[coeff_zero_eq_constantCoeff_apply, hB0]`. Simplify using the standard rewrite rules.

Consider the case `succ k ih`. Use `van_subst hBq (hint _) (hB0 _) hv ih` as an intermediate fact. Rewrite `this` using `[hcomp, ← zc_natCast, ← zc_mul, ← pow_succ']`. Use `this using 5` and compare the differences between its conclusion and the goal. Expand and normalize the polynomial expressions, which then agree.
-/
theorem padic_multiplications : ∀ (q : ℕ) [Fact q.Prime] (F : FormalGroup 𝓞_ℂ_[q]) (U ℓ : ℂ_[q]⟦X⟧), constantCoeff U = 0 → constantCoeff ℓ = 0 → U.subst ℓ = X → MvPowerSeries.subst (![PowerSeries.subst (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) ℂ_[q]) U, PowerSeries.subst (MvPowerSeries.X 1 : MvPowerSeries (Fin 2) ℂ_[q]) U] : Fin 2 → MvPowerSeries (Fin 2) ℂ_[q]) (MvPowerSeries.map (algebraMap 𝓞_ℂ_[q] ℂ_[q]) F.toPowerSeries) = PowerSeries.subst (MvPowerSeries.X 0 + MvPowerSeries.X 1 : MvPowerSeries (Fin 2) ℂ_[q]) U → (∀ a : ℤ_[q], Bd 1 (U.subst (C (zc a) * ℓ))) ∧ (∀ k, ¬ q ∣ k → ‖coeff k (U.subst (C (q : ℂ_[q]) * ℓ))‖ < 1) ∧ (‖coeff q (U.subst (C (q : ℂ_[q]) * ℓ))‖ < 1 → ∀ (k : ℕ) (a : ℤ_[q]), ‖a‖ ≤ (q : ℝ) ^ (-(k : ℤ)) → ∀ n < (2 * q) ^ k, ‖coeff n (U.subst (C (zc a) * ℓ))‖ < 1) := by
  intro q hq F U ℓ hU hℓ hUℓ hG
  have law := add_law _ U hU hG
  have hinv := subst_inv hℓ hUℓ
  have hc : ∀ a : ℂ_[q], constantCoeff (C a * ℓ) = 0 := fun a => by simp [hℓ]
  have hB0 : ∀ a : ℂ_[q], constantCoeff (U.subst (C a * ℓ) : ℂ_[q]⟦X⟧) = 0 := fun a => cc_subst hU (hc a)
  have hℓB : ∀ a : ℂ_[q], (ℓ.subst (U.subst (C a * ℓ) : ℂ_[q]⟦X⟧) : ℂ_[q]⟦X⟧) = C a * ℓ := fun a => by
    rw [← subst_comp_subst_apply (hs hU) (hs (hc a)), hinv, subst_X (hs (hc a))]
  have hcomp : ∀ a b : ℂ_[q], (PowerSeries.subst (U.subst (C b * ℓ) : ℂ_[q]⟦X⟧) (U.subst (C a * ℓ) : ℂ_[q]⟦X⟧) : ℂ_[q]⟦X⟧)
      = U.subst (C (a * b) * ℓ) := fun a b => by
    rw [subst_comp_subst_apply (hs (hc a)) (hs (hB0 b)), subst_mul (hs (hB0 b)), subst_C', hℓB, map_mul, mul_assoc]

  have hnat : ∀ n : ℕ, (U.subst (C (n : ℂ_[q]) * ℓ) : ℂ_[q]⟦X⟧)
      = PowerSeries.map (algebraMap 𝓞_ℂ_[q] ℂ_[q]) (GlobalTheory.ConvSer.nMul F n) := by
    intro n
    induction n with
    | zero =>
      ext m
      rw [coeff_subst_C_mul U ℓ hℓ, GlobalTheory.ConvSer.nMul_zero, map_zero, map_zero]
      refine Finset.sum_eq_zero fun d _ => ?_
      rcases d with _ | d
      · simp [hU]
      · simp
    | succ n ih =>
      rw [GlobalTheory.ConvSer.nMul_succ, ← map_law F _ _ (GlobalTheory.ConvSer.nMul_constantCoeff F n) constantCoeff_X, ← ih, map_X]
      have := law _ _ (hc n) hℓ
      rw [hUℓ] at this
      rw [this]
      congr 1
      push_cast
      rw [map_add, map_one]
      ring
  have hint : ∀ a : ℤ_[q], Bd 1 (U.subst (C (zc a) * ℓ)) := by
    intro a m
    refine PadicInt.denseRange_natCast.induction_on (p := fun a => ‖coeff m (U.subst (C (zc a) * ℓ) : ℂ_[q]⟦X⟧)‖ ≤ 1)
      a ?_ fun n => ?_
    · simp only [coeff_subst_C_mul U ℓ hℓ]
      have := continuous_zc (q := q)
      exact isClosed_le (by fun_prop) continuous_const
    · rw [zc_natCast, hnat]
      exact bd_map _ m
  have hBq : Bd 1 (U.subst (C (q : ℂ_[q]) * ℓ)) := by
    have := hint q
    rwa [zc_natCast] at this

  have hone := deriv_mul_eq_one hℓ hUℓ
  set W : ℂ_[q]⟦X⟧ := C (coeff 1 ℓ) * (d⁄dX ℂ_[q] U).subst ℓ with hW
  have hW0 : constantCoeff W = 1 := by
    have h1 := congrArg constantCoeff hone
    rw [map_mul, map_one, ← coeff_zero_eq_constantCoeff_apply (d⁄dX _ ℓ), coeff_derivative] at h1
    simp only [zero_add, Nat.cast_zero, mul_one] at h1
    rw [hW, map_mul, constantCoeff_C, mul_comm, h1]
  have hWint : Bd 1 W := by
    intro m
    set N := m + 2 with hN
    have hXN : constantCoeff (X ^ N : ℂ_[q]⟦X⟧) = 0 := by simp [hN]
    set h : ℂ_[q]⟦X⟧ := ℓ.subst (X ^ N : ℂ_[q]⟦X⟧) with hh
    have hh0 : constantCoeff h = 0 := cc_subst hℓ hXN
    have hUh : (U.subst h : ℂ_[q]⟦X⟧) = X ^ N := by
      rw [hh, ← subst_comp_subst_apply (hs hℓ) (hs hXN), hUℓ, subst_X (hs hXN)]
    obtain ⟨V, hV⟩ : ∃ V : ℂ_[q]⟦X⟧, ℓ = C (coeff 1 ℓ) * X + X ^ 2 * V := by
      have : (X : ℂ_[q]⟦X⟧) ^ 2 ∣ ℓ - C (coeff 1 ℓ) * X := by
        rw [X_pow_dvd_iff]
        intro j hj
        interval_cases j
        · simp [hℓ]
        · simp
      obtain ⟨V, hV⟩ := this
      exact ⟨V, by rw [← hV]; ring⟩
    have hh' : h = C (coeff 1 ℓ) * X ^ N + X ^ (2 * N) * V.subst (X ^ N : ℂ_[q]⟦X⟧) := by
      rw [hh]
      conv_lhs => rw [hV]
      rw [subst_add (hs hXN), subst_mul (hs hXN), subst_mul (hs hXN), subst_pow (hs hXN), subst_C', subst_X (hs hXN),
        ← pow_mul, mul_comm N 2]
    have hd : (X : ℂ_[q]⟦X⟧) ^ N ∣ h := by
      rw [hh']
      exact dvd_add (dvd_mul_left _ _) ((pow_dvd_pow _ (by omega)).mul_right _)
    obtain ⟨T, hT⟩ := taylor_dvd U ℓ h N hℓ hh0 hd
    have hl := law _ _ hℓ hh0
    have hb := map_law F X (X ^ N) constantCoeff_X (by simp [hN])
    rw [map_pow, map_X] at hb
    rw [hUℓ, hUh, hb] at hl
    have hbd : Bd 1 (U.subst (ℓ + h)) := hl ▸ bd_map _
    have e : (U.subst (ℓ + h) : ℂ_[q]⟦X⟧) = X + X ^ N * W +
        X ^ (2 * N) * (T + (d⁄dX ℂ_[q] U).subst ℓ * V.subst (X ^ N : ℂ_[q]⟦X⟧)) := by
      rw [hUℓ] at hT
      rw [hW]
      linear_combination hT + ((d⁄dX ℂ_[q] U).subst ℓ : ℂ_[q]⟦X⟧) * hh'
    have := hbd (m + N)
    rw [e, map_add, map_add, coeff_X_pow_mul, coeff_X, if_neg (by omega), coeff_X_pow_mul', if_neg (by omega)] at this
    simpa using this
  have hq1 : ‖(q : ℂ_[q])‖ < 1 := by
    rw [← zc_natCast, norm_zc, PadicInt.norm_p]
    exact inv_lt_one_of_one_lt₀ (by exact_mod_cast hq.out.one_lt)
  have hder : Bd ‖(q : ℂ_[q])‖ (d⁄dX ℂ_[q] (U.subst (C (q : ℂ_[q]) * ℓ))) := by
    refine (sup_norm_laws q).2.2.2.2.2 _ W 0 _ hWint (by rw [hW0, norm_one]) ?_
    have e : X ^ 0 * W * d⁄dX ℂ_[q] (U.subst (C (q : ℂ_[q]) * ℓ))
        = C (q : ℂ_[q]) * W.subst (U.subst (C (q : ℂ_[q]) * ℓ) : ℂ_[q]⟦X⟧) := by
      rw [derivative_subst (hs (hc q)), hW, subst_mul (hs (hB0 q)), subst_C',
        subst_comp_subst_apply (hs hℓ) (hs (hB0 q)), hℓB, Derivation.leibniz, derivative_C]
      simp only [smul_eq_mul]
      linear_combination (C (coeff 1 ℓ) * C (q : ℂ_[q]) *
        ((d⁄dX ℂ_[q] U).subst (C (q : ℂ_[q]) * ℓ) : ℂ_[q]⟦X⟧)) * hone
    rw [e]
    intro n
    rw [coeff_C_mul, norm_mul]
    exact mul_le_of_le_one_right (norm_nonneg _) ((sup_norm_laws q).2.1 W _ 1 hWint hBq (hB0 q) n)
  have h2 : ∀ k, ¬ q ∣ k → ‖coeff k (U.subst (C (q : ℂ_[q]) * ℓ) : ℂ_[q]⟦X⟧)‖ < 1 := by
    intro k hk
    rcases k with _ | k
    · exact absurd (dvd_zero q) hk
    have := hder k
    rw [coeff_derivative, norm_mul] at this
    have hk1 : ‖((k : ℂ_[q]) + 1)‖ = 1 := by
      rw [← Nat.cast_succ, ← zc_natCast, norm_zc, PadicInt.norm_natCast_eq_one_iff]
      exact (Nat.Prime.coprime_iff_not_dvd hq.out).2 hk
    rw [hk1, mul_one] at this
    exact this.trans_lt hq1
  refine ⟨hint, h2, fun hqq k a ha => ?_⟩
  have hv : Van (2 * q) (U.subst (C (q : ℂ_[q]) * ℓ)) := by
    intro n hn
    by_cases hd : q ∣ n
    · obtain ⟨c, rfl⟩ := hd
      have hc2 : c < 2 := by
        by_contra h
        have : q * 2 ≤ q * c := Nat.mul_le_mul_left q (by omega)
        omega
      interval_cases c
      · rw [mul_zero, coeff_zero_eq_constantCoeff_apply, hB0]; simp
      · rwa [mul_one]
    · exact h2 n hd
  obtain ⟨v, rfl⟩ := Ideal.mem_span_singleton'.1 ((PadicInt.norm_le_pow_iff_mem_span_pow a k).1 ha)
  clear ha
  show Van _ _
  induction k with
  | zero =>
    intro n hn
    obtain rfl : n = 0 := by simpa using hn
    rw [coeff_zero_eq_constantCoeff_apply, hB0]; simp
  | succ k ih =>
    have := van_subst hBq (hint _) (hB0 _) hv ih
    rw [hcomp, ← zc_natCast, ← zc_mul, ← pow_succ'] at this
    convert this using 5
    ring

end GlobalTheory.MomOne.FormalMul

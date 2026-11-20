import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.ExistsRootOfIsAlgClosed
import Development.AbelianVarietyTheory.Definitions.Foundations.EeProd
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsLogDerivQExpansionModPrimePowUnique
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsLogDerivQExpansionModPrimePowCalculus
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsPrimitiveExpansionQuotientLevelOneStatement
open GlobalTheory.KZ GlobalTheory.CyclotomicQExpansion GlobalTheory.Glue
open scoped MatrixGroups

namespace GlobalTheory.Glue.DlPow

open scoped MatrixGroups in

/- English proof (translation)
Use `⟨fun c => ?_⟩` and prove the remaining obligations. Take `⟨D, hD, hint⟩` from `X.bdd (algebraMap Ω X.K c)`. Take `⟨k, hk⟩` from `hint 0`. Establish `hc : (algebraMap Ω (HahnSeries ℚ Ω) c).coeff 0 = c`. Rewrite using `[HahnSeries.algebraMap_apply']`.

Simplify using the standard rewrite rules. Rewrite `hk` using `[AlgHom.commutes, hc]`. Establish `h1 : IsAlgebraic ℚ ((D : Ω) ^ k * c)` using `(hk.tower_top (A := ℚ)).isAlgebraic`. Establish `hD' : ((D : ℚ) ^ k) ≠ 0` using `pow_ne_zero _ (by exact_mod_cast hD.ne')`. Establish `hc' : c = algebraMap ℚ Ω (((D : ℚ) ^ k)⁻¹) * ((D : Ω) ^ k * c)`.

Rewrite using `[← mul_assoc, ← map_natCast (algebraMap ℚ Ω), ← map_pow, ← map_mul, inv_mul_cancel₀ hD', map_one, one_mul]`. Rewrite using `[hc']`. Conclude with `(isAlgebraic_algebraMap _).mul h1`.
-/
theorem _root_.GlobalTheory.Glue.DlPow.isAlgebraic_of_tower {Ω : Type} [Field Ω] [Algebra ℚ Ω]
    {ε : Ω →+* ℂ} (X : _root_.GlobalTheory.KZ.Tower Ω ε) :
    Algebra.IsAlgebraic ℚ Ω := by
  refine ⟨fun c => ?_⟩
  obtain ⟨D, hD, hint⟩ := X.bdd (algebraMap Ω X.K c)
  obtain ⟨k, hk⟩ := hint 0
  have hc : (algebraMap Ω (HahnSeries ℚ Ω) c).coeff 0 = c := by
    rw [HahnSeries.algebraMap_apply']
    simp
  rw [AlgHom.commutes, hc] at hk
  have h1 : IsAlgebraic ℚ ((D : Ω) ^ k * c) := (hk.tower_top (A := ℚ)).isAlgebraic
  have hD' : ((D : ℚ) ^ k) ≠ 0 := pow_ne_zero _ (by exact_mod_cast hD.ne')
  have hc' : c = algebraMap ℚ Ω (((D : ℚ) ^ k)⁻¹) * ((D : Ω) ^ k * c) := by
    rw [← mul_assoc, ← map_natCast (algebraMap ℚ Ω), ← map_pow, ← map_mul, inv_mul_cancel₀ hD',
      map_one, one_mul]
  rw [hc']
  exact (isAlgebraic_algebraMap _).mul h1

open scoped MatrixGroups in
/- English proof (translation)
Proceed by induction on `k with`. Consider the case `zero => rwa [zero_add, pow_one]`. Consider the case `succ k ih`. Rewrite using `[pow_succ]`. Conclude with `_root_.GlobalTheory.Glue.Prim.mul A _ _ ih hP`.
-/
private lemma prim_pow_succ {Ω : Type} [Field Ω] {A : ValuationSubring Ω}
    {P : HahnSeries ℚ Ω} (hP : _root_.GlobalTheory.Glue.Prim A P) (k : ℕ) :
    _root_.GlobalTheory.Glue.Prim A (P ^ (k + 1)) := by
  induction k with
  | zero => rwa [zero_add, pow_one]
  | succ k ih =>
    rw [pow_succ]
    exact _root_.GlobalTheory.Glue.Prim.mul A _ _ ih hP

open scoped MatrixGroups in
/- English proof (translation)
Proceed by induction on `k with`. Consider the case `zero => simp`. Consider the case `succ k ih`. Rewrite using `[pow_succ, (_root_.GlobalTheory.Glue.theta_leibniz_add_const s _ _).1, ih]`. Use `push_cast`.

Simplify using `only [map_add, map_natCast, map_one]`. Expand and normalize the polynomial expressions, which then agree.
-/
private lemma theta_pow_succ {Ω : Type} [Field Ω] [Algebra ℚ Ω] (s : ℚ)
    (P : HahnSeries ℚ Ω) (k : ℕ) :
    _root_.GlobalTheory.Glue.theta s (P ^ (k + 1)) =
      HahnSeries.C ((k + 1 : ℕ) : Ω) * P ^ k * _root_.GlobalTheory.Glue.theta s P := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, (_root_.GlobalTheory.Glue.theta_leibniz_add_const s _ _).1, ih]
    push_cast
    simp only [map_add, map_natCast, map_one]
    ring

open scoped MatrixGroups in
/- English proof (translation)
Use `show algebraMap ℚ Ω (1 * r) * P.coeff r ∈ A`. Distinguish the cases in `h : P.coeff r = 0`. Rewrite using `[h, mul_zero]`. Conclude with `zero_mem A`. Use `mul_mem ?_ (hP r)` and prove the remaining obligations.

Rewrite using `[one_mul, ← Rat.coe_int_num_of_den_eq_one (hden r h), map_intCast]`. Conclude with `intCast_mem A _`.
-/
private lemma theta_one_coeff_mem_of_integral_den_one {Ω : Type} [Field Ω] [Algebra ℚ Ω]
    (A : ValuationSubring Ω) {P : HahnSeries ℚ Ω} (hP : ∀ r, P.coeff r ∈ A)
    (hden : ∀ r, P.coeff r ≠ 0 → r.den = 1) (r : ℚ) :
    (_root_.GlobalTheory.Glue.theta 1 P).coeff r ∈ A := by
  show algebraMap ℚ Ω (1 * r) * P.coeff r ∈ A
  by_cases h : P.coeff r = 0
  · rw [h, mul_zero]
    exact zero_mem A
  · refine mul_mem ?_ (hP r)
    rw [one_mul, ← Rat.coe_int_num_of_den_eq_one (hden r h), map_intCast]
    exact intCast_mem A _

open scoped MatrixGroups in
/- English proof (translation)
Rewrite using `[HahnSeries.coeff_mul]`. Conclude with `sum_mem fun ij _ => mul_mem (hx _) (hy _)`.
-/
private lemma hahnSeries_coeff_mul_mem_valuationSubring {Ω : Type} [Field Ω] (A : ValuationSubring Ω)
    {x y : HahnSeries ℚ Ω} (hx : ∀ r, x.coeff r ∈ A) (hy : ∀ r, y.coeff r ∈ A) (r : ℚ) :
    (x * y).coeff r ∈ A := by
  rw [HahnSeries.coeff_mul]
  exact sum_mem fun ij _ => mul_mem (hx _) (hy _)

open scoped MatrixGroups in
/- English proof (translation)
Proceed by induction on `k generalizing r with`. Consider the case `zero`. Rewrite using `[pow_zero, HahnSeries.coeff_one]`. Use `split_ifs`. Conclude with `one_mem A`.

Conclude with `zero_mem A`. Consider the case `succ k ih`. Rewrite using `[pow_succ]`. Conclude with `hahnSeries_coeff_mul_mem_valuationSubring A ih hx r`.
-/
private lemma hahnSeries_coeff_pow_mem_valuationSubring {Ω : Type} [Field Ω] (A : ValuationSubring Ω)
    {x : HahnSeries ℚ Ω} (hx : ∀ r, x.coeff r ∈ A) (k : ℕ) (r : ℚ) : (x ^ k).coeff r ∈ A := by
  induction k generalizing r with
  | zero =>
    rw [pow_zero, HahnSeries.coeff_one]
    split_ifs
    · exact one_mem A
    · exact zero_mem A
  | succ k ih =>
    rw [pow_succ]
    exact hahnSeries_coeff_mul_mem_valuationSubring A ih hx r

open scoped MatrixGroups in

/- English proof (translation)
Introduce `Ω _ _ _ ε X A l _ hl n f u hf hu hT φ φ' hφ hφ' r`. Establish `hj : ∃ g : ℂ → ℂ, DifferentiableOn ℂ g _root_.GlobalTheory.KZ.Hs ∧ X.an X.jK = ↑g`. Take `⟨g, h1, h2⟩` from `X.j_hol`. Conclude with `⟨g, h2, h1⟩`. Establish `hden : ∀ x : X.K, X.sl (_root_.GlobalTheory.KZ.ofSL ModularGroup.T) x = x → ∀ s, (X.exp x).coeff s ≠ 0 → s.den = 1`.

Introduce `x hx s hs`. Establish `hmem : x ∈ _root_.GlobalTheory.Glue.KT X 1`. Rewrite using `[_root_.GlobalTheory.Glue.KT.mem_def, pow_one]`. Conclude with `hx`. Simplify using `using (_root_.GlobalTheory.Glue.KTExp.mem_KT_iff ε X 1 one_pos x).1 hmem s hs`.

Establish `hu0 : _root_.GlobalTheory.Glue.IsDl X A l n 1 (u ^ (l ^ n)) 0`. Take `⟨a, b, κ, S, hκ, hab, hPa, hPb, hb, -⟩` from `_root_.GlobalTheory.exists_prim_frac_level_one ε X hj l A hl u hu`. Establish `hbT` using `hb ModularGroup.T`. Establish `haT : X.sl (_root_.GlobalTheory.KZ.ofSL ModularGroup.T) a = a`. Establish `h1` using `congrArg (X.sl (_root_.GlobalTheory.KZ.ofSL ModularGroup.T)) hab`.

Rewrite `h1` using `[map_mul, map_mul, hT, hbT, AlgEquiv.commutes, hab]`. Conclude with `(mul_left_cancel₀ ((map_ne_zero _).2 hκ) h1).symm`. Take `⟨k, hk⟩ : ∃ k, l ^ n = k + 1` from `⟨l ^ n - 1, (Nat.succ_pred_eq_of_pos (pow_pos (Fact.out : l.Prime).pos n)).symm⟩`. Establish `hl' : (l : Ω) ^ n = ((k + 1 : ℕ) : Ω)` using `by rw [← Nat.cast_pow, hk]`. Establish `hPaA` using `hPa.1`.

Establish `hPbA` using `hPb.1`. Unfold `_root_.GlobalTheory.Glue.IsDl`. Use `⟨fun s => by simpa using zero_mem A, a ^ (l ^ n), b ^ (l ^ n), κ ^ (l ^ n), pow_ne_zero _ hκ, by rw [map_pow, ← mul_pow, ← mul_pow, hab], ?_, ?_, fun s => ?_⟩` and prove the remaining obligations. Rewrite using `[map_pow, hk]`. Conclude with `prim_pow_succ hPa k`.

Rewrite using `[map_pow, hk]`. Conclude with `prim_pow_succ hPb k`. Rewrite using `[map_pow, map_pow, hk, theta_pow_succ, theta_pow_succ] set P := X.exp a set Q := X.exp b set W := P ^ k * Q ^ k * (_root_.GlobalTheory.Glue.theta 1 P * Q - P * _root_.GlobalTheory.Glue.theta 1 Q)`. Establish `hW : W.coeff s ∈ A`. Establish `hθP` using `theta_one_coeff_mem_of_integral_den_one A hPaA (hden a haT)`.

Establish `hθQ` using `theta_one_coeff_mem_of_integral_den_one A hPbA (hden b hbT)`. Use `hahnSeries_coeff_mul_mem_valuationSubring A (hahnSeries_coeff_mul_mem_valuationSubring A (hahnSeries_coeff_pow_mem_valuationSubring A hPaA k) (hahnSeries_coeff_pow_mem_valuationSubring A hPbA k)) (fun t => ?_) s` and prove the remaining obligations. Rewrite using `[HahnSeries.coeff_sub]`. Conclude with `sub_mem (hahnSeries_coeff_mul_mem_valuationSubring A hθP hPbA t) (hahnSeries_coeff_mul_mem_valuationSubring A hPaA hθQ t)`. Establish `hexp : HahnSeries.C ((k + 1 : ℕ) : Ω) * P ^ k * _root_.GlobalTheory.Glue.theta 1 P * Q ^ (k + 1) - P ^ (k + 1) * (HahnSeries.C ((k + 1 : ℕ) : Ω) * Q ^ k * _root_.GlobalTheory.Glue.theta 1 Q) = HahnSeries.C ((k + 1 : ℕ) : Ω) * W`.

Simplify using `only [W]`. Expand and normalize the polynomial expressions, which then agree. Unfold `_root_.GlobalTheory.Glue.CgA`. Use `⟨-W.coeff s, neg_mem hW, ?_⟩` and prove the remaining obligations. Rewrite using `[hexp, HahnSeries.C_mul_eq_smul, HahnSeries.coeff_smul, zero_mul, zero_mul, HahnSeries.coeff_zero, hl', smul_eq_mul]`.

Expand and normalize the polynomial expressions, which then agree. Establish `h` using `(_root_.GlobalTheory.Glue.isDl_calc ε X hj l A hl n 1 f (u ^ (l ^ n)) φ 0).1 hφ hu0`. Simplify using `using _root_.GlobalTheory.Glue.isDl_unique ε X hj l A hl n 1 _ _ _ h hφ' r`.
-/
theorem _root_.GlobalTheory.Glue.DlPow.isDl_mul_lpow_cong : ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω]
    [IsAlgClosure ℚ Ω] {ε : Ω →+* ℂ} (X : _root_.GlobalTheory.KZ.Tower Ω ε)
    (A : ValuationSubring Ω) (l : ℕ) [Fact l.Prime], (l : Ω) ∈ A.nonunits →
    ∀ (n : ℕ) (f u : X.K), f ≠ 0 → u ≠ 0 →
      X.sl (_root_.GlobalTheory.KZ.ofSL ModularGroup.T) u = u →
      ∀ φ φ' : HahnSeries ℚ Ω, _root_.GlobalTheory.Glue.IsDl X A l n 1 f φ →
        _root_.GlobalTheory.Glue.IsDl X A l n 1 (f * u ^ (l ^ n)) φ' →
          ∀ r, _root_.GlobalTheory.Glue.CgA A l n (φ.coeff r) (φ'.coeff r) := by
  intro Ω _ _ _ ε X A l _ hl n f u hf hu hT φ φ' hφ hφ' r
  have hj : ∃ g : ℂ → ℂ, DifferentiableOn ℂ g _root_.GlobalTheory.KZ.Hs ∧
      X.an X.jK = ↑g := by
    obtain ⟨g, h1, h2⟩ := X.j_hol
    exact ⟨g, h2, h1⟩
  have hden : ∀ x : X.K,
      X.sl (_root_.GlobalTheory.KZ.ofSL ModularGroup.T) x = x →
        ∀ s, (X.exp x).coeff s ≠ 0 → s.den = 1 := by
    intro x hx s hs
    have hmem : x ∈ _root_.GlobalTheory.Glue.KT X 1 := by
      rw [_root_.GlobalTheory.Glue.KT.mem_def, pow_one]
      exact hx
    simpa using (_root_.GlobalTheory.Glue.KTExp.mem_KT_iff ε X 1 one_pos x).1 hmem s hs
  have hu0 : _root_.GlobalTheory.Glue.IsDl X A l n 1 (u ^ (l ^ n)) 0 := by
    obtain ⟨a, b, κ, S, hκ, hab, hPa, hPb, hb, -⟩ :=
      _root_.GlobalTheory.exists_prim_frac_level_one ε X hj l A hl u hu
    have hbT := hb ModularGroup.T
    have haT : X.sl (_root_.GlobalTheory.KZ.ofSL ModularGroup.T) a = a := by
      have h1 := congrArg (X.sl (_root_.GlobalTheory.KZ.ofSL ModularGroup.T)) hab
      rw [map_mul, map_mul, hT, hbT, AlgEquiv.commutes, hab] at h1
      exact (mul_left_cancel₀ ((map_ne_zero _).2 hκ) h1).symm
    obtain ⟨k, hk⟩ : ∃ k, l ^ n = k + 1 :=
      ⟨l ^ n - 1, (Nat.succ_pred_eq_of_pos (pow_pos (Fact.out : l.Prime).pos n)).symm⟩
    have hl' : (l : Ω) ^ n = ((k + 1 : ℕ) : Ω) := by rw [← Nat.cast_pow, hk]
    have hPaA := hPa.1
    have hPbA := hPb.1
    unfold _root_.GlobalTheory.Glue.IsDl
    refine ⟨fun s => by simpa using zero_mem A, a ^ (l ^ n), b ^ (l ^ n), κ ^ (l ^ n),
      pow_ne_zero _ hκ, by rw [map_pow, ← mul_pow, ← mul_pow, hab], ?_, ?_, fun s => ?_⟩
    · rw [map_pow, hk]
      exact prim_pow_succ hPa k
    · rw [map_pow, hk]
      exact prim_pow_succ hPb k
    · rw [map_pow, map_pow, hk, theta_pow_succ, theta_pow_succ]
      set P := X.exp a
      set Q := X.exp b
      set W := P ^ k * Q ^ k *
        (_root_.GlobalTheory.Glue.theta 1 P * Q - P * _root_.GlobalTheory.Glue.theta 1 Q)
      have hW : W.coeff s ∈ A := by
        have hθP := theta_one_coeff_mem_of_integral_den_one A hPaA (hden a haT)
        have hθQ := theta_one_coeff_mem_of_integral_den_one A hPbA (hden b hbT)
        refine hahnSeries_coeff_mul_mem_valuationSubring A
          (hahnSeries_coeff_mul_mem_valuationSubring A (hahnSeries_coeff_pow_mem_valuationSubring A hPaA k)
            (hahnSeries_coeff_pow_mem_valuationSubring A hPbA k)) (fun t => ?_) s
        rw [HahnSeries.coeff_sub]
        exact sub_mem (hahnSeries_coeff_mul_mem_valuationSubring A hθP hPbA t)
          (hahnSeries_coeff_mul_mem_valuationSubring A hPaA hθQ t)
      have hexp : HahnSeries.C ((k + 1 : ℕ) : Ω) * P ^ k * _root_.GlobalTheory.Glue.theta 1 P *
          Q ^ (k + 1) -
          P ^ (k + 1) * (HahnSeries.C ((k + 1 : ℕ) : Ω) * Q ^ k * _root_.GlobalTheory.Glue.theta 1 Q) =
          HahnSeries.C ((k + 1 : ℕ) : Ω) * W := by
        simp only [W]
        ring
      unfold _root_.GlobalTheory.Glue.CgA
      refine ⟨-W.coeff s, neg_mem hW, ?_⟩
      rw [hexp, HahnSeries.C_mul_eq_smul, HahnSeries.coeff_smul, zero_mul, zero_mul,
        HahnSeries.coeff_zero, hl', smul_eq_mul]
      ring
  have h := (_root_.GlobalTheory.Glue.isDl_calc ε X hj l A hl n 1 f (u ^ (l ^ n)) φ 0).1
    hφ hu0
  simpa using _root_.GlobalTheory.Glue.isDl_unique ε X hj l A hl n 1 _ _ _ h hφ' r

end GlobalTheory.Glue.DlPow

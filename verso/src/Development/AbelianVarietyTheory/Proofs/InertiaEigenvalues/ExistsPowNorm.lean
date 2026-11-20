import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsCrisP
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AcrisToBdRPlusInjective
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsGaussNormExtensionAcrisStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AcrisNormOfNonzeroStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AcrisGaussNormEventuallyMonomialStatement
import Development.AbelianVarietyTheory.CrystallinePeriods.RingIface

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.MemLoc
open scoped Formalism.Per

namespace GlobalTheory.MemLoc.GaussCore

/- English proof (translation)
Assume the negation of the conclusion as `hlt`. Use `push_neg at hlt`. Establish `ha : 0 < N a` using `lt_of_le_of_lt (h01 b).1 hlt`. Establish `hb1 : N b < 1` using `lt_of_lt_of_le hlt (h01 a).2`. Establish `h0 : N 0 = 0`.

Use `hmul 0 b` as an intermediate fact. Rewrite `this` using `[zero_mul]`. Establish `h2` using `(h01 0).1`. Use the polynomial consequences of the given equalities and inequalities. Establish `hpow : ∀ (x : A) (n : ℕ), N (x ^ n) = N x ^ n`.

Introduce `x n`. Proceed by induction on `n with`. Consider the case `zero => simpa using hA`. Consider the case `succ n ih => rw [pow_succ, hmul, ih, pow_succ]`. Establish `hsum : ∀ (s : Finset ℕ) (f : ℕ → A) (M : ℝ), 0 < M → (∀ i ∈ s, N (f i) < M) → N (∑ i ∈ s, f i) < M`.

Introduce `s f M hM`. Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty => intro _`. Simplify `hM` using `[h0]`. Consider the case `insert i s hi ih`.

Introduce `hs`. Rewrite using `[Finset.sum_insert hi]`. Conclude with `lt_of_le_of_lt (hadd _ _) (max_lt (hs i (Finset.mem_insert_self _ _)) (ih fun j hj => hs j (Finset.mem_insert_of_mem hj)))`. Establish `key` using `hsum (Finset.range d) (fun i => c i * a ^ i * b ^ (d - i)) (N a ^ d) (pow_pos ha d) (by`. Introduce `i hi`.

Establish `hi'` using `Finset.mem_range.1 hi`. Rewrite using `[hmul, hmul, hpow, hpow]`. Establish `e : N a ^ d = N a ^ i * N a ^ (d - i)`. Rewrite using `[← pow_add]`. Use `congr 1`.

Use linear arithmetic over natural numbers and integers. Establish `h1 : N b ^ (d - i) < N a ^ (d - i)` using `pow_lt_pow_left₀ hlt (h01 b).1 (by omega)`. Establish `h2 : 0 < N a ^ i` using `pow_pos ha i`. Establish `h3 : 0 ≤ N b ^ (d - i)` using `pow_nonneg (h01 b).1 _`. Combine the equalities or inequalities in the displayed calculation.

Rewrite `key` using `[eq_neg_of_add_eq_zero_right h, hneg, hpow]`. Conclude with `lt_irrefl _ key`.
-/
theorem le_of_homog {A : Type} [CommRing A] (N : A → ℝ) (h01 : ∀ x, 0 ≤ N x ∧ N x ≤ 1)
    (hadd : ∀ x y, N (x + y) ≤ max (N x) (N y)) (hneg : ∀ x, N (-x) = N x)
    (hmul : ∀ x y, N (x * y) = N x * N y) (a b : A) (d : ℕ) (c : ℕ → A)
    (h : a ^ d + ∑ i ∈ Finset.range d, c i * a ^ i * b ^ (d - i) = 0) (hA : N 1 = 1) :
    N a ≤ N b := by
  by_contra hlt
  push_neg at hlt
  have ha : 0 < N a := lt_of_le_of_lt (h01 b).1 hlt
  have hb1 : N b < 1 := lt_of_lt_of_le hlt (h01 a).2
  have h0 : N 0 = 0 := by
    have := hmul 0 b
    rw [zero_mul] at this
    have h2 := (h01 0).1
    nlinarith
  have hpow : ∀ (x : A) (n : ℕ), N (x ^ n) = N x ^ n := by
    intro x n
    induction n with
    | zero => simpa using hA
    | succ n ih => rw [pow_succ, hmul, ih, pow_succ]
  have hsum : ∀ (s : Finset ℕ) (f : ℕ → A) (M : ℝ), 0 < M → (∀ i ∈ s, N (f i) < M) →
      N (∑ i ∈ s, f i) < M := by
    intro s f M hM
    induction s using Finset.induction_on with
    | empty => intro _; simpa [h0] using hM
    | insert i s hi ih =>
      intro hs
      rw [Finset.sum_insert hi]
      exact lt_of_le_of_lt (hadd _ _) (max_lt (hs i (Finset.mem_insert_self _ _))
        (ih fun j hj => hs j (Finset.mem_insert_of_mem hj)))
  have key := hsum (Finset.range d) (fun i => c i * a ^ i * b ^ (d - i)) (N a ^ d) (pow_pos ha d) (by
    intro i hi
    have hi' := Finset.mem_range.1 hi
    rw [hmul, hmul, hpow, hpow]
    have e : N a ^ d = N a ^ i * N a ^ (d - i) := by
      rw [← pow_add]; congr 1; omega
    have h1 : N b ^ (d - i) < N a ^ (d - i) := pow_lt_pow_left₀ hlt (h01 b).1 (by omega)
    have h2 : 0 < N a ^ i := pow_pos ha i
    have h3 : 0 ≤ N b ^ (d - i) := pow_nonneg (h01 b).1 _
    calc N (c i) * N a ^ i * N b ^ (d - i) ≤ 1 * N a ^ i * N b ^ (d - i) := by
          gcongr; exact (h01 _).2
      _ < N a ^ d := by rw [one_mul, e]; gcongr)
  rw [eq_neg_of_add_eq_zero_right h, hneg, hpow] at key
  exact lt_irrefl _ key

variable {l : ℕ} [Fact l.Prime]

/- English proof (translation)
Establish `hx : IsIntegral ℚ_[l] x` using `Algebra.IsIntegral.isIntegral x`. Rewrite `h` using `[← PadicAlgCl.spectralNorm_eq, spectralNorm, spectralValue_le_one_iff (minpoly.monic hx)]`. Establish `hl : minpoly ℚ_[l] x ∈ Polynomial.lifts (algebraMap ℤ_[l] ℚ_[l])`. Rewrite using `[Polynomial.lifts_iff_coeff_lifts]`. Conclude with `fun n => ⟨⟨_, h n⟩, rfl⟩`.

Take `⟨q, hq, -, hqm⟩` from `Polynomial.lifts_and_degree_eq_and_monic hl (minpoly.monic hx)`. Use `⟨q, hqm, ?_⟩` and prove the remaining obligations. Rewrite using `[← Polynomial.eval₂_map, hq, ← Polynomial.aeval_def, minpoly.aeval]`.
-/
theorem exists_monic (x : Om l) (h : ‖x‖ ≤ 1) : ∃ q : Polynomial ℤ_[l], q.Monic ∧
    Polynomial.eval₂ ((algebraMap ℚ_[l] (Om l)).comp (algebraMap ℤ_[l] ℚ_[l])) x q = 0 := by
  have hx : IsIntegral ℚ_[l] x := Algebra.IsIntegral.isIntegral x
  rw [← PadicAlgCl.spectralNorm_eq, spectralNorm, spectralValue_le_one_iff (minpoly.monic hx)] at h
  have hl : minpoly ℚ_[l] x ∈ Polynomial.lifts (algebraMap ℤ_[l] ℚ_[l]) := by
    rw [Polynomial.lifts_iff_coeff_lifts]
    exact fun n => ⟨⟨_, h n⟩, rfl⟩
  obtain ⟨q, hq, -, hqm⟩ := Polynomial.lifts_and_degree_eq_and_monic hl (minpoly.monic hx)
  refine ⟨q, hqm, ?_⟩
  rw [← Polynomial.eval₂_map, hq, ← Polynomial.aeval_def, minpoly.aeval]

/- English proof (translation)
Establish `hi : IsIntegral ℚ_[l] x` using `Algebra.IsIntegral.isIntegral x`. Establish `h0 : (minpoly ℚ_[l] x).coeff 0 ≠ 0` using `minpoly.coeff_zero_ne_zero hi hx`. Establish `hd` using `minpoly.natDegree_pos hi`. Use `⟨(minpoly ℚ_[l] x).natDegree, -((minpoly ℚ_[l] x).coeff 0).valuation, hd, ?_⟩` and prove the remaining obligations. Rewrite using `[← PadicAlgCl.spectralNorm_eq, spectralNorm.spectralNorm_eq_norm_coeff_zero_rpow, ← Padic.norm_eq_zpow_neg_valuation h0, one_div]`.

Conclude with `Real.rpow_inv_natCast_pow (norm_nonneg _) hd.ne'`.
-/
theorem exists_pow_norm (x : Om l) (hx : x ≠ 0) :
    ∃ (t : ℕ) (s : ℤ), 0 < t ∧ ‖x‖ ^ t = (l : ℝ) ^ s := by
  have hi : IsIntegral ℚ_[l] x := Algebra.IsIntegral.isIntegral x
  have h0 : (minpoly ℚ_[l] x).coeff 0 ≠ 0 := minpoly.coeff_zero_ne_zero hi hx
  have hd := minpoly.natDegree_pos hi
  refine ⟨(minpoly ℚ_[l] x).natDegree, -((minpoly ℚ_[l] x).coeff 0).valuation, hd, ?_⟩
  rw [← PadicAlgCl.spectralNorm_eq, spectralNorm.spectralNorm_eq_norm_coeff_zero_rpow,
    ← Padic.norm_eq_zpow_neg_valuation h0, one_div]
  exact Real.rpow_inv_natCast_pow (norm_nonneg _) hd.ne'

/- English proof (translation)
Rewrite using `[GlobalTheory.RingIface.tower, C.j_cris.on0]`. Simplify using `[aDp]`.
-/
theorem j_alg (C : Core l) (a : Per.Ainf l) :
    C.j (algebraMap (Per.Ainf l) (Per.Acris l) a) = aDp l a := by
  rw [GlobalTheory.RingIface.tower, C.j_cris.on0]
  simp [aDp]

set_option allowUnsafeReducibility true
attribute [local irreducible] Per.Acris Per.Bcris

/- English proof (translation)
Take `⟨q, hq, h0⟩` from `exists_monic y hy`. Use `⟨q.natDegree, fun i => algebraMap (Per.Ainf l) (Per.Acris l) (Per.zA l (q.coeff i)), ?_⟩` and prove the remaining obligations. Apply `crisP_injective l C.j C.j_cris` to reduce the goal to its premises. Rewrite `h0` using `[hq.as_sum, Polynomial.eval₂_add, Polynomial.eval₂_X_pow, Polynomial.eval₂_finset_sum]`. Establish `h1` using `congrArg (fun z => C.o z * C.j b ^ q.natDegree) h0`.

Simplify using `only [map_add, map_pow, map_sum, map_zero, zero_mul, add_mul, Finset.sum_mul, Polynomial.eval₂_mul, Polynomial.eval₂_C, Polynomial.eval₂_X_pow, map_mul] at h1`. Simplify using `only [map_add, map_pow, map_sum, map_zero, map_mul, h, j_alg]`. Rewrite using `[← h1, mul_pow]`. Use `congr 1`. Use `Finset.sum_congr rfl fun i hi => ?_` and prove the remaining obligations.

Establish `hi'` using `Finset.mem_range.1 hi`. Rewrite using `[← C.o_sec.z]`. Establish `e : C.j b ^ q.natDegree = C.j b ^ i * C.j b ^ (q.natDegree - i)`. Rewrite using `[← pow_add]`. Use `congr 1`.

Use linear arithmetic over natural numbers and integers. Rewrite using `[e, mul_pow]`. Simplify using `only [RingHom.comp_apply, PadicInt.algebraMap_apply]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem homog_eq (C : Core l) (a b : Per.Acris l) (y : Om l) (hy : ‖y‖ ≤ 1)
    (h : C.j a = C.o y * C.j b) : ∃ (d : ℕ) (c : ℕ → Per.Acris l),
      a ^ d + ∑ i ∈ Finset.range d, c i * a ^ i * b ^ (d - i) = 0 := by
  obtain ⟨q, hq, h0⟩ := exists_monic y hy
  refine ⟨q.natDegree, fun i => algebraMap (Per.Ainf l) (Per.Acris l) (Per.zA l (q.coeff i)), ?_⟩
  apply crisP_injective l C.j C.j_cris
  rw [hq.as_sum, Polynomial.eval₂_add, Polynomial.eval₂_X_pow, Polynomial.eval₂_finset_sum] at h0
  have h1 := congrArg (fun z => C.o z * C.j b ^ q.natDegree) h0
  simp only [map_add, map_pow, map_sum, map_zero, zero_mul, add_mul, Finset.sum_mul,
    Polynomial.eval₂_mul, Polynomial.eval₂_C, Polynomial.eval₂_X_pow, map_mul] at h1
  simp only [map_add, map_pow, map_sum, map_zero, map_mul, h, j_alg]
  rw [← h1, mul_pow]
  congr 1
  refine Finset.sum_congr rfl fun i hi => ?_
  have hi' := Finset.mem_range.1 hi
  rw [← C.o_sec.z]
  have e : C.j b ^ q.natDegree = C.j b ^ i * C.j b ^ (q.natDegree - i) := by
    rw [← pow_add]; congr 1; omega
  rw [e, mul_pow]
  simp only [RingHom.comp_apply, PadicInt.algebraMap_apply]
  ring

/- English proof (translation)
Rewrite using `[← WittVector.fontaineTheta_teichmuller, WittVector.teichmuller_zero, map_zero]`.
-/
theorem untilt_zero : (0 : Per.Fl l).untilt = 0 := by
  rw [← WittVector.fontaineTheta_teichmuller, WittVector.teichmuller_zero, map_zero]

/- English proof (translation)
Establish `hl : (0 : ℝ) < l` using `by exact_mod_cast (Fact.out : l.Prime).pos`. Establish `hf : ∀ n : ℕ, ‖(((((l : ℕ) : Per.Ainf l).coeff n).untilt : Per.OC l) : ℂ_[l])‖ ^ ((1 : ℝ) / (l : ℝ) ^ n) * r ^ n = if n = 1 then r else 0`. Introduce `n`. Rewrite using `[WittVector.coeff_p]`. Use `split_ifs with h`.

Simplify using `[h]`. Rewrite using `[untilt_zero]`. Establish `: ((1 : ℝ) / (l : ℝ) ^ n) ≠ 0` using `by positivity`. Simplify using `only [ZeroMemClass.coe_zero, norm_zero, Real.zero_rpow this, zero_mul]`. Simplify using `only [hf]`.

Apply the tactic sequence `have hb : ∀ n : ℕ, (if n = 1 then r else 0) ≤ r := fun n => by split_ifs <;> simp [hr]`. Use `le_antisymm (ciSup_le hb) ?_` and prove the remaining obligations. Use `le_ciSup (f := fun n : ℕ => if n = 1 then r else 0) ⟨r, by rintro _ ⟨n, rfl⟩; exact hb n⟩ 1` as an intermediate fact. Simplify using `using this`.
-/
theorem gauss_l (r : ℝ) (hr : 0 ≤ r) :
    (⨆ n : ℕ, ‖(((((l : ℕ) : Per.Ainf l).coeff n).untilt : Per.OC l) : ℂ_[l])‖ ^
      ((1 : ℝ) / (l : ℝ) ^ n) * r ^ n) = r := by
  have hl : (0 : ℝ) < l := by exact_mod_cast (Fact.out : l.Prime).pos
  have hf : ∀ n : ℕ, ‖(((((l : ℕ) : Per.Ainf l).coeff n).untilt : Per.OC l) : ℂ_[l])‖ ^
      ((1 : ℝ) / (l : ℝ) ^ n) * r ^ n = if n = 1 then r else 0 := by
    intro n
    rw [WittVector.coeff_p]
    split_ifs with h
    · simp [h]
    · rw [untilt_zero]
      have : ((1 : ℝ) / (l : ℝ) ^ n) ≠ 0 := by positivity
      simp only [ZeroMemClass.coe_zero, norm_zero, Real.zero_rpow this, zero_mul]
  simp only [hf]
  have hb : ∀ n : ℕ, (if n = 1 then r else 0) ≤ r := fun n => by split_ifs <;> simp [hr]
  refine le_antisymm (ciSup_le hb) ?_
  have := le_ciSup (f := fun n : ℕ => if n = 1 then r else 0) ⟨r, by rintro _ ⟨n, rfl⟩; exact hb n⟩ 1
  simpa using this

/- English proof (translation)
Take `⟨r, h1, h2⟩` from `exists_between huv`. Take `⟨s, h3, h4⟩` from `exists_between h2`. Establish `hr : 0 < r` using `hu.trans h1`. Establish `hs : 0 < s` using `hr.trans h3`. Establish `e1` using `h r h1 h2`.

Establish `e2` using `h s (h1.trans h3) h4`. Establish `hq : 1 < s / r` using `(one_lt_div hr).2 h3`. Establish `hc' : c' ≠ 0`. Introduce and unpack `rfl`. Establish `: 0 < c * r ^ k` using `mul_pos hc (zpow_pos hr _)`.

Rewrite `this` using `[e1, zero_mul]`. Conclude with `lt_irrefl _ this`. Apply `zpow_right_injective₀ (one_pos.trans hq) hq.ne'` to reduce the goal to its premises. Establish `a1 : r ^ k ≠ 0` using `(zpow_pos hr _).ne'`. Establish `a2 : r ^ k' ≠ 0` using `(zpow_pos hr _).ne'`.

Use `show (s / r) ^ k = (s / r) ^ k'`. Rewrite using `[div_zpow, div_zpow, ← mul_div_mul_left _ _ hc.ne', e1, e2, mul_div_mul_left _ _ hc']`.
-/
theorem exp_eq {u v c c' : ℝ} {k k' : ℤ} (hu : 0 < u) (huv : u < v) (hc : 0 < c)
    (h : ∀ r, u < r → r < v → c * r ^ k = c' * r ^ k') : k = k' := by
  obtain ⟨r, h1, h2⟩ := exists_between huv
  obtain ⟨s, h3, h4⟩ := exists_between h2
  have hr : 0 < r := hu.trans h1
  have hs : 0 < s := hr.trans h3
  have e1 := h r h1 h2
  have e2 := h s (h1.trans h3) h4
  have hq : 1 < s / r := (one_lt_div hr).2 h3
  have hc' : c' ≠ 0 := by
    rintro rfl
    have : 0 < c * r ^ k := mul_pos hc (zpow_pos hr _)
    rw [e1, zero_mul] at this
    exact lt_irrefl _ this
  apply zpow_right_injective₀ (one_pos.trans hq) hq.ne'
  have a1 : r ^ k ≠ 0 := (zpow_pos hr _).ne'
  have a2 : r ^ k' ≠ 0 := (zpow_pos hr _).ne'
  show (s / r) ^ k = (s / r) ^ k'
  rw [div_zpow, div_zpow, ← mul_div_mul_left _ _ hc.ne', e1, e2, mul_div_mul_left _ _ hc']

/- English proof (translation)
Introduce `l _ C a b x hb hx h`. Establish `hl1 : (1 : ℝ) < l` using `by exact_mod_cast (Fact.out : l.Prime).one_lt`. Establish `hl : (0 : ℝ) < l` using `one_pos.trans hl1`. Establish `hli : (0 : ℝ) < (l : ℝ)⁻¹` using `inv_pos.2 hl`. Establish `hex : ∀ r : ℝ, ∃ N : Per.Acris l → ℝ, (l : ℝ)⁻¹ ≤ r → r < 1 → (∀ x, 0 ≤ N x ∧ N x ≤ 1) ∧ (∀ x y, N (x + y) ≤ max (N x) (N y)) ∧ (∀ x, N (-x) = N x) ∧ (∀ x y, N (x * y) = N x * N y) ∧ ∀ a : Per.Ainf l, N (algebraMap (Per.Ainf l) (Per.Acris l) a) = ⨆ n : ℕ, ‖(((a.coeff n).untilt : …`.

Introduce `r`. Distinguish the cases in `h1 : (l : ℝ)⁻¹ ≤ r ∧ r < 1`. Take `⟨N, hN⟩` from `GlobalTheory.T.exists_gauss_norm_extension_acris l r h1.1 h1.2`. Conclude with `⟨N, fun _ _ => hN⟩`. Conclude with `⟨fun _ => 0, fun h2 h3 => absurd ⟨h2, h3⟩ h1⟩`.

Use `choose N hN using hex`. Establish `ha : a ≠ 0`. Introduce and unpack `rfl`. Apply `hb` to reduce the goal to its premises. Apply `crisP_injective l C.j C.j_cris` to reduce the goal to its premises.

Use `congrArg (fun z => C.o x⁻¹ * z) h` as an intermediate fact. Simplify using `only [map_zero, mul_zero, ← mul_assoc, ← map_mul, inv_mul_cancel₀ hx, map_one, one_mul] at this`. Rewrite using `[← this, map_zero]`. Take `⟨r₁, c, k, hr₁, hr₁', hc, hNa⟩` from `GlobalTheory.T.acris_gauss_norm_eventually_monomial l N hN a (GlobalTheory.T.acris_norm_of_nonzero l N hN a ha)`. Take `⟨r₂, c', k', hr₂, hr₂', hc', hNb⟩` from `GlobalTheory.T.acris_gauss_norm_eventually_monomial l N hN b (GlobalTheory.T.acris_norm_of_nonzero l N hN b hb)`.

Take `⟨t, s, ht, hts⟩` from `exists_pow_norm x hx`. Take `⟨m, n, rfl⟩ : ∃ m n : ℕ, s = (m : ℤ) - n` from `⟨s.toNat, (-s).toNat, by omega⟩`. Establish `hl0 : ((l : ℕ) : Om l) ≠ 0` using `by exact_mod_cast (Fact.out : l.Prime).ne_zero`. Establish `hnl : ‖((l : ℕ) : Om l)‖ = (l : ℝ)⁻¹`. Rewrite using `[← map_natCast (algebraMap ℚ_[l] (Om l)), norm_algebraMap', Padic.norm_p]`.

Use `set y : Om l := x ^ t * (l : Om l) ^ m / (l : Om l) ^ n with hy`. Establish `hy1 : ‖y‖ = 1`. Rewrite using `[hy, norm_div, norm_mul, norm_pow, norm_pow, norm_pow, hts, hnl, zpow_sub₀ hl.ne']`. Simplify using `only [zpow_natCast, inv_pow]`. Clear the denominators using the available nonvanishing facts.

Establish `hy0 : y ≠ 0`. Introduce `h0`. Rewrite `hy1` using `[h0, norm_zero]`. Conclude with `zero_ne_one hy1`. Establish `e1 : C.j (a ^ t * (l : Per.Acris l) ^ m) = C.o y * C.j (b ^ t * (l : Per.Acris l) ^ n)`.

Establish `e : y * (l : Om l) ^ n = x ^ t * (l : Om l) ^ m` using `div_mul_cancel₀ _ (pow_ne_zero _ hl0)`. Establish `e'` using `congrArg C.o e`. Simplify using `only [map_mul, map_pow, map_natCast] at e' ⊢`. Rewrite using `[h, mul_pow]`. Take the linear combination `(-(C.j b) ^ t) * e'`.

Establish `e2 : C.j (b ^ t * (l : Per.Acris l) ^ n) = C.o y⁻¹ * C.j (a ^ t * (l : Per.Acris l) ^ m)`. Rewrite using `[e1, ← mul_assoc, ← map_mul, inv_mul_cancel₀ hy0, map_one, one_mul]`. Take `⟨d1, c1, q1⟩` from `homog_eq C _ _ y hy1.le e1`. Take `⟨d2, c2, q2⟩` from `homog_eq C _ _ y⁻¹ (by rw [norm_inv, hy1, inv_one]) e2`. Establish `hk : k * t + m = k' * t + n`.

Use `exp_eq (c := c ^ t) (c' := c' ^ t) hli (lt_min hr₁ hr₂) (pow_pos hc t) fun r h1 h2 => ?_` and prove the remaining obligations. Establish `hr : 0 < r` using `hli.trans h1`. Establish `h3 : r < r₁` using `h2.trans_le (min_le_left _ _)`. Establish `h4 : r < r₂` using `h2.trans_le (min_le_right _ _)`. Take `⟨n01, nadd, nneg, nmul, nalg⟩` from `hN r h1.le (h3.trans hr₁')`.

Establish `hNl : N r (l : Per.Acris l) = r`. Rewrite using `[← map_natCast (algebraMap (Per.Ainf l) (Per.Acris l)), nalg, gauss_l r hr.le]`. Establish `hN1 : N r 1 = 1`. Use `nmul (l : Per.Acris l) 1` as an intermediate fact. Rewrite `this` using `[mul_one, hNl]`.

Conclude with `(mul_eq_left₀ hr.ne').1 this.symm`. Establish `hpow : ∀ (x : Per.Acris l) (n : ℕ), N r (x ^ n) = N r x ^ n`. Introduce `x n`. Proceed by induction on `n with`. Consider the case `zero => simpa using hN1`.

Consider the case `succ n ih => rw [pow_succ, nmul, ih, pow_succ]`. Establish `e` using `le_antisymm (le_of_homog (N r) n01 nadd nneg nmul _ _ d1 c1 q1 hN1) (le_of_homog (N r) n01 nadd nneg nmul _ _ d2 c2 q2 hN1)`. Rewrite `e` using `[nmul, nmul, hpow, hpow, hpow, hpow, hNl, hNa r h1 h3, hNb r h1 h4]`. Rewrite using `[zpow_add₀ hr.ne', zpow_add₀ hr.ne', zpow_mul, zpow_mul]`. Simplify using `only [zpow_natCast]`.

Rewrite using `[← mul_assoc, ← mul_assoc, ← mul_pow, ← mul_pow, e]`. Use `⟨k' - k, ?_⟩` and prove the remaining obligations. Apply `(pow_left_inj₀ (norm_nonneg _) (zpow_pos hl _).le ht.ne').1` to reduce the goal to its premises. Rewrite using `[hts, ← zpow_natCast, ← zpow_mul]`. Use `congr 1`.

Take the linear combination `hk`.
-/
theorem norm_eq_zpow : ∀ (l : ℕ) [Fact l.Prime] (C : Core l) (a b : Per.Acris l) (x : Om l),
    b ≠ 0 → x ≠ 0 → C.j a = C.o x * C.j b → ∃ k : ℤ, ‖x‖ = (l : ℝ) ^ k := by
  intro l _ C a b x hb hx h
  have hl1 : (1 : ℝ) < l := by exact_mod_cast (Fact.out : l.Prime).one_lt
  have hl : (0 : ℝ) < l := one_pos.trans hl1
  have hli : (0 : ℝ) < (l : ℝ)⁻¹ := inv_pos.2 hl
  have hex : ∀ r : ℝ, ∃ N : Per.Acris l → ℝ, (l : ℝ)⁻¹ ≤ r → r < 1 → (∀ x, 0 ≤ N x ∧ N x ≤ 1) ∧ (∀ x y, N (x + y) ≤ max (N x) (N y)) ∧ (∀ x, N (-x) = N x) ∧ (∀ x y, N (x * y) = N x * N y) ∧ ∀ a : Per.Ainf l, N (algebraMap (Per.Ainf l) (Per.Acris l) a) = ⨆ n : ℕ, ‖(((a.coeff n).untilt : Per.OC l) : ℂ_[l])‖ ^ ((1 : ℝ) / (l : ℝ) ^ n) * r ^ n := by
    intro r
    by_cases h1 : (l : ℝ)⁻¹ ≤ r ∧ r < 1
    · obtain ⟨N, hN⟩ := GlobalTheory.T.exists_gauss_norm_extension_acris l r h1.1 h1.2
      exact ⟨N, fun _ _ => hN⟩
    · exact ⟨fun _ => 0, fun h2 h3 => absurd ⟨h2, h3⟩ h1⟩
  choose N hN using hex
  have ha : a ≠ 0 := by
    rintro rfl
    apply hb
    apply crisP_injective l C.j C.j_cris
    have := congrArg (fun z => C.o x⁻¹ * z) h
    simp only [map_zero, mul_zero, ← mul_assoc, ← map_mul, inv_mul_cancel₀ hx, map_one,
      one_mul] at this
    rw [← this, map_zero]
  obtain ⟨r₁, c, k, hr₁, hr₁', hc, hNa⟩ := GlobalTheory.T.acris_gauss_norm_eventually_monomial l N hN a (GlobalTheory.T.acris_norm_of_nonzero l N hN a ha)
  obtain ⟨r₂, c', k', hr₂, hr₂', hc', hNb⟩ := GlobalTheory.T.acris_gauss_norm_eventually_monomial l N hN b (GlobalTheory.T.acris_norm_of_nonzero l N hN b hb)
  obtain ⟨t, s, ht, hts⟩ := exists_pow_norm x hx
  obtain ⟨m, n, rfl⟩ : ∃ m n : ℕ, s = (m : ℤ) - n := ⟨s.toNat, (-s).toNat, by omega⟩
  have hl0 : ((l : ℕ) : Om l) ≠ 0 := by exact_mod_cast (Fact.out : l.Prime).ne_zero
  have hnl : ‖((l : ℕ) : Om l)‖ = (l : ℝ)⁻¹ := by
    rw [← map_natCast (algebraMap ℚ_[l] (Om l)), norm_algebraMap', Padic.norm_p]
  set y : Om l := x ^ t * (l : Om l) ^ m / (l : Om l) ^ n with hy
  have hy1 : ‖y‖ = 1 := by
    rw [hy, norm_div, norm_mul, norm_pow, norm_pow, norm_pow, hts, hnl, zpow_sub₀ hl.ne']
    simp only [zpow_natCast, inv_pow]
    field_simp
  have hy0 : y ≠ 0 := by
    intro h0; rw [h0, norm_zero] at hy1; exact zero_ne_one hy1
  have e1 : C.j (a ^ t * (l : Per.Acris l) ^ m) = C.o y * C.j (b ^ t * (l : Per.Acris l) ^ n) := by
    have e : y * (l : Om l) ^ n = x ^ t * (l : Om l) ^ m := div_mul_cancel₀ _ (pow_ne_zero _ hl0)
    have e' := congrArg C.o e
    simp only [map_mul, map_pow, map_natCast] at e' ⊢
    rw [h, mul_pow]
    linear_combination (-(C.j b) ^ t) * e'
  have e2 : C.j (b ^ t * (l : Per.Acris l) ^ n) = C.o y⁻¹ * C.j (a ^ t * (l : Per.Acris l) ^ m) := by
    rw [e1, ← mul_assoc, ← map_mul, inv_mul_cancel₀ hy0, map_one, one_mul]
  obtain ⟨d1, c1, q1⟩ := homog_eq C _ _ y hy1.le e1
  obtain ⟨d2, c2, q2⟩ := homog_eq C _ _ y⁻¹ (by rw [norm_inv, hy1, inv_one]) e2
  have hk : k * t + m = k' * t + n := by
    refine exp_eq (c := c ^ t) (c' := c' ^ t) hli (lt_min hr₁ hr₂) (pow_pos hc t) fun r h1 h2 => ?_
    have hr : 0 < r := hli.trans h1
    have h3 : r < r₁ := h2.trans_le (min_le_left _ _)
    have h4 : r < r₂ := h2.trans_le (min_le_right _ _)
    obtain ⟨n01, nadd, nneg, nmul, nalg⟩ := hN r h1.le (h3.trans hr₁')
    have hNl : N r (l : Per.Acris l) = r := by
      rw [← map_natCast (algebraMap (Per.Ainf l) (Per.Acris l)), nalg, gauss_l r hr.le]
    have hN1 : N r 1 = 1 := by
      have := nmul (l : Per.Acris l) 1
      rw [mul_one, hNl] at this
      exact (mul_eq_left₀ hr.ne').1 this.symm
    have hpow : ∀ (x : Per.Acris l) (n : ℕ), N r (x ^ n) = N r x ^ n := by
      intro x n
      induction n with
      | zero => simpa using hN1
      | succ n ih => rw [pow_succ, nmul, ih, pow_succ]
    have e := le_antisymm (le_of_homog (N r) n01 nadd nneg nmul _ _ d1 c1 q1 hN1)
      (le_of_homog (N r) n01 nadd nneg nmul _ _ d2 c2 q2 hN1)
    rw [nmul, nmul, hpow, hpow, hpow, hpow, hNl, hNa r h1 h3, hNb r h1 h4] at e
    rw [zpow_add₀ hr.ne', zpow_add₀ hr.ne', zpow_mul, zpow_mul]
    simp only [zpow_natCast]
    rw [← mul_assoc, ← mul_assoc, ← mul_pow, ← mul_pow, e]
  refine ⟨k' - k, ?_⟩
  apply (pow_left_inj₀ (norm_nonneg _) (zpow_pos hl _).le ht.ne').1
  rw [hts, ← zpow_natCast, ← zpow_mul]
  congr 1
  linear_combination hk

end GlobalTheory.MemLoc.GaussCore

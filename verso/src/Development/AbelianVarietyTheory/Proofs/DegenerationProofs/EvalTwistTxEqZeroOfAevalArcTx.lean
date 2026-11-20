import Mathlib
import Development.AbelianVarietyTheory.Definitions.Degenerations.NotAllMatchRankZero
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.TwistTermsStatement

open ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Ex
open scoped BigOperators

namespace GlobalTheory.BddArc

section
variable {C : Type} [NontriviallyNormedField C] [CompleteSpace C]

def AbsSumAt (u : C) (f : PowerSeries C) (c : C) : Prop :=
  (Summable fun n => ‖PowerSeries.coeff n f * u ^ n‖) ∧ ∑' n, PowerSeries.coeff n f * u ^ n = c

omit [CompleteSpace C] in
/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Use `summable_of_ne_finset_zero (s := {0}) fun n hn => ?_` and prove the remaining obligations. Simplify using `[PowerSeries.coeff_C, Finset.notMem_singleton.1 hn]`. Rewrite using `[tsum_eq_single 0 fun n hn => by simp [PowerSeries.coeff_C, hn]]`. Simplify using the standard rewrite rules.
-/
theorem AbsSumAt.const (u a : C) : AbsSumAt u (PowerSeries.C a) a := by
  constructor
  · refine summable_of_ne_finset_zero (s := {0}) fun n hn => ?_
    simp [PowerSeries.coeff_C, Finset.notMem_singleton.1 hn]
  · rw [tsum_eq_single 0 fun n hn => by simp [PowerSeries.coeff_C, hn]]
    simp

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Use `(hf.1.add hg.1).of_nonneg_of_le (fun _ => norm_nonneg _) fun n => ?_` and prove the remaining obligations. Rewrite using `[map_add, add_mul]`. Conclude with `norm_add_le _ _`. Rewrite using `[← hf.2, ← hg.2, ← hf.1.of_norm.tsum_add hg.1.of_norm]`.

Simplify using `only [map_add, add_mul]`.
-/
theorem AbsSumAt.add {u : C} {f g : PowerSeries C} {a b : C} (hf : AbsSumAt u f a) (hg : AbsSumAt u g b) :
    AbsSumAt u (f + g) (a + b) := by
  constructor
  · refine (hf.1.add hg.1).of_nonneg_of_le (fun _ => norm_nonneg _) fun n => ?_
    rw [map_add, add_mul]
    exact norm_add_le _ _
  · rw [← hf.2, ← hg.2, ← hf.1.of_norm.tsum_add hg.1.of_norm]
    simp only [map_add, add_mul]

/- English proof (translation)
Establish `e : ∀ n, PowerSeries.coeff n (f * g) * u ^ n = ∑ kl ∈ Finset.HasAntidiagonal.antidiagonal n, (PowerSeries.coeff kl.1 f * u ^ kl.1) * (PowerSeries.coeff kl.2 g * u ^ kl.2)` using `fun n => by`. Rewrite using `[PowerSeries.coeff_mul, Finset.sum_mul]`. Use `Finset.sum_congr rfl fun kl h => ?_` and prove the remaining obligations. Rewrite using `[← Finset.HasAntidiagonal.mem_antidiagonal.1 h, pow_add]`. Expand and normalize the polynomial expressions, which then agree.

Prove the components needed by the constructor for the conclusion. Simplify using `only [e]`. Conclude with `summable_norm_sum_mul_antidiagonal_of_summable_norm (f := fun n => PowerSeries.coeff n f * u ^ n) (g := fun n => PowerSeries.coeff n g * u ^ n) hf.1 hg.1`. Rewrite using `[← hf.2, ← hg.2, tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_summable_norm hf.1 hg.1]`. Simplify using `only [e]`.
-/
theorem AbsSumAt.mul {u : C} {f g : PowerSeries C} {a b : C} (hf : AbsSumAt u f a) (hg : AbsSumAt u g b) :
    AbsSumAt u (f * g) (a * b) := by
  have e : ∀ n, PowerSeries.coeff n (f * g) * u ^ n = ∑ kl ∈ Finset.HasAntidiagonal.antidiagonal n,
      (PowerSeries.coeff kl.1 f * u ^ kl.1) * (PowerSeries.coeff kl.2 g * u ^ kl.2) := fun n => by
    rw [PowerSeries.coeff_mul, Finset.sum_mul]
    refine Finset.sum_congr rfl fun kl h => ?_
    rw [← Finset.HasAntidiagonal.mem_antidiagonal.1 h, pow_add]
    ring
  constructor
  · simp only [e]
    exact summable_norm_sum_mul_antidiagonal_of_summable_norm (f := fun n => PowerSeries.coeff n f * u ^ n)
      (g := fun n => PowerSeries.coeff n g * u ^ n) hf.1 hg.1
  · rw [← hf.2, ← hg.2, tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_summable_norm hf.1 hg.1]
    simp only [e]

open scoped BigOperators in
variable {C : Type} [NontriviallyNormedField C] [CompleteSpace C] in
/- English proof (translation)
Establish `h : (fun n => PowerSeries.coeff n (algebraMap C (PowerSeries C) a) * u ^ n) = fun n => if n = 0 then a else 0`. Use function extensionality and compare the values at `n`. Apply the tactic sequence `rcases n with _ | n <;> simp [PowerSeries.coeff_C]`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Use `summable_of_ne_finset_zero (s := {0}) fun n hn => ?_` and prove the remaining obligations.

Rewrite using `[congrFun h n, if_neg (by simpa using hn), norm_zero]`. Rewrite using `[h]`. Simplify using the standard rewrite rules.
-/
private theorem absSumAt_algebraMap (u a : C) :
    _root_.GlobalTheory.BddArc.AbsSumAt u (algebraMap C (PowerSeries C) a) a := by
  have h : (fun n => PowerSeries.coeff n (algebraMap C (PowerSeries C) a) * u ^ n) =
      fun n => if n = 0 then a else 0 := by
    funext n
    rcases n with _ | n <;> simp [PowerSeries.coeff_C]
  refine ⟨?_, ?_⟩
  · refine summable_of_ne_finset_zero (s := {0}) fun n hn => ?_
    rw [congrFun h n, if_neg (by simpa using hn), norm_zero]
  · rw [h]
    simp

open scoped BigOperators in
variable {C : Type} [NontriviallyNormedField C] [CompleteSpace C] in
/- English proof (translation)
Establish `h : ∀ n, PowerSeries.coeff n (f + g) * u ^ n = PowerSeries.coeff n f * u ^ n + PowerSeries.coeff n g * u ^ n` using `fun n => by`. Rewrite using `[map_add, add_mul]`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Use `Summable.of_nonneg_of_le (fun n => norm_nonneg _) (fun n => ?_) (Summable.add hf.1 hg.1)` and prove the remaining obligations. Rewrite using `[h]`.

Conclude with `norm_add_le _ _`. Repeatedly rewrite using `[h]`. Rewrite using `[(hf.1.of_norm).tsum_add hg.1.of_norm, hf.2, hg.2]`.
-/
private theorem absSumAt_add {u : C} {f g : PowerSeries C} {a b : C}
    (hf : _root_.GlobalTheory.BddArc.AbsSumAt u f a) (hg : _root_.GlobalTheory.BddArc.AbsSumAt u g b) :
    _root_.GlobalTheory.BddArc.AbsSumAt u (f + g) (a + b) := by
  have h : ∀ n, PowerSeries.coeff n (f + g) * u ^ n =
      PowerSeries.coeff n f * u ^ n + PowerSeries.coeff n g * u ^ n := fun n => by
    rw [map_add, add_mul]
  refine ⟨?_, ?_⟩
  · refine Summable.of_nonneg_of_le (fun n => norm_nonneg _) (fun n => ?_) (Summable.add hf.1 hg.1)
    rw [h]
    exact norm_add_le _ _
  · simp_rw [h]
    rw [(hf.1.of_norm).tsum_add hg.1.of_norm, hf.2, hg.2]

open scoped BigOperators in
variable {C : Type} [NontriviallyNormedField C] [CompleteSpace C] in
/- English proof (translation)
Establish `h : ∀ n, PowerSeries.coeff n (f * g) * u ^ n = ∑ kl ∈ Finset.HasAntidiagonal.antidiagonal n, (PowerSeries.coeff kl.1 f * u ^ kl.1) * (PowerSeries.coeff kl.2 g * u ^ kl.2)` using `fun n => by`. Rewrite using `[PowerSeries.coeff_mul, Finset.sum_mul]`. Use `Finset.sum_congr rfl fun kl hkl => ?_` and prove the remaining obligations. Rewrite using `[← Finset.HasAntidiagonal.mem_antidiagonal.1 hkl, pow_add]`. Expand and normalize the polynomial expressions, which then agree.

Use `⟨?_, ?_⟩` and prove the remaining obligations. Conclude with `(summable_norm_sum_mul_antidiagonal_of_summable_norm hf.1 hg.1).congr fun n => by rw [h]`. Rewrite using `[tsum_congr h, ← tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_summable_norm hf.1 hg.1, hf.2, hg.2]`.
-/
private theorem absSumAt_mul {u : C} {f g : PowerSeries C} {a b : C}
    (hf : _root_.GlobalTheory.BddArc.AbsSumAt u f a) (hg : _root_.GlobalTheory.BddArc.AbsSumAt u g b) :
    _root_.GlobalTheory.BddArc.AbsSumAt u (f * g) (a * b) := by
  have h : ∀ n, PowerSeries.coeff n (f * g) * u ^ n =
      ∑ kl ∈ Finset.HasAntidiagonal.antidiagonal n,
        (PowerSeries.coeff kl.1 f * u ^ kl.1) * (PowerSeries.coeff kl.2 g * u ^ kl.2) := fun n => by
    rw [PowerSeries.coeff_mul, Finset.sum_mul]
    refine Finset.sum_congr rfl fun kl hkl => ?_
    rw [← Finset.HasAntidiagonal.mem_antidiagonal.1 hkl, pow_add]
    ring
  refine ⟨?_, ?_⟩
  · exact (summable_norm_sum_mul_antidiagonal_of_summable_norm hf.1 hg.1).congr fun n => by rw [h]
  · rw [tsum_congr h, ← tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_summable_norm hf.1 hg.1, hf.2, hg.2]

open scoped BigOperators in
variable {C : Type} [NontriviallyNormedField C] [CompleteSpace C] in
/- English proof (translation)
Proceed by induction on `F using MvPolynomial.induction_on with`. Consider the case `C c`. Rewrite using `[MvPolynomial.aeval_C, MvPolynomial.eval_C]`. Conclude with `absSumAt_algebraMap u c`. Consider the case `add p q hp hq`.

Rewrite using `[map_add, map_add]`. Conclude with `absSumAt_add hp hq`. Consider the case `mul_X p i hp`. Rewrite using `[map_mul, map_mul, MvPolynomial.aeval_X, MvPolynomial.eval_X]`. Conclude with `absSumAt_mul hp (h i)`.
-/
theorem _root_.GlobalTheory.BddArc.AbsSumAt.aeval {u : C} {ι : Type} {f : ι → PowerSeries C} {a : ι → C}
    (h : ∀ i, _root_.GlobalTheory.BddArc.AbsSumAt u (f i) (a i))
    (F : MvPolynomial ι C) :
    _root_.GlobalTheory.BddArc.AbsSumAt u (MvPolynomial.aeval f F) (MvPolynomial.eval a F) := by
  induction F using MvPolynomial.induction_on with
  | C c =>
    rw [MvPolynomial.aeval_C, MvPolynomial.eval_C]
    exact absSumAt_algebraMap u c
  | add p q hp hq =>
    rw [map_add, map_add]
    exact absSumAt_add hp hq
  | mul_X p i hp =>
    rw [map_mul, map_mul, MvPolynomial.aeval_X, MvPolynomial.eval_X]
    exact absSumAt_mul hp (h i)

end

end GlobalTheory.BddArc

open scoped BigOperators in
/- English proof (translation)
Use `set b := Module.Free.chooseBasis ℤ X with hb`. Set `M : Matrix (Module.Free.ChooseBasisIndex ℤ X) (Module.Free.ChooseBasisIndex ℤ X) ℚ` to `Matrix.of fun i j => (B (b i) (b j) : ℚ)`. Set `Bq` to `Matrix.toBilin' M`. Set `φ : X → Module.Free.ChooseBasisIndex ℤ X → ℚ` to `fun y i => (b.repr y i : ℚ)`. Establish `hφ : ∀ y z, ((B y z : ℤ) : ℚ) = Bq (φ y) (φ z)`.

Introduce `y z`. Rewrite using `[Matrix.toBilin'_apply]`. Use `conv_lhs => rw [← b.sum_repr y, ← b.sum_repr z]`. Simplify using `only [map_sum, LinearMap.sum_apply, map_smul, LinearMap.smul_apply, smul_eq_mul, Int.cast_sum, Int.cast_mul, Finset.mul_sum, M, φ, Matrix.of_apply]`. Rewrite using `[Finset.sum_comm]`.

Use `Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Expand and normalize the polynomial expressions, which then agree. Establish `hBsymm : LinearMap.IsSymm Bq`. Use `LinearMap.isSymm_iff_eq_flip.2 (LinearMap.ext₂ fun x y => ?_)` and prove the remaining obligations. Rewrite using `[LinearMap.flip_apply, Matrix.toBilin'_apply, Matrix.toBilin'_apply, Finset.sum_comm]`.

Use `Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Simplify using `only [M, Matrix.of_apply, hsymm (b i) (b j)]`. Expand and normalize the polynomial expressions, which then agree. Establish `hqpos : ∀ v, v ≠ 0 → 0 < Bq v v`. Introduce `v hv`.

Take `⟨d, hd⟩` from `IsLocalization.exist_integer_multiples (nonZeroDivisors ℤ) Finset.univ v`. Use `choose n hn using fun i => hd i (Finset.mem_univ i)`. Establish `hd0 : ((d : ℤ) : ℚ) ≠ 0` using `by exact_mod_cast nonZeroDivisors.coe_ne_zero d`. Use `set y : X := b.equivFun.symm n`. Establish `hy : φ y = ((d : ℤ) : ℚ) • v`.

Use function extensionality and compare the values at `i`. Use `hn i` as an intermediate fact. Simplify using `only [algebraMap_int_eq, eq_intCast, zsmul_eq_mul] at this`. Establish `hr : b.repr y i = n i` using `by rw [← b.equivFun_apply, LinearEquiv.apply_symm_apply]`. Simplify using `only [φ, Pi.smul_apply, smul_eq_mul, hr]`.

Conclude with `this`. Establish `hy0 : y ≠ 0`. Introduce `h`. Apply `hv` to reduce the goal to its premises. Establish `h2 : ((d : ℤ) : ℚ) • v = 0` using `by rw [← hy, h]; funext i; simp [φ]`.

Conclude with `(smul_eq_zero.1 h2).resolve_left hd0`. Establish `h1` using `hpos y hy0`. Establish `h2 : (0 : ℚ) < Bq (φ y) (φ y)` using `by rw [← hφ]; exact_mod_cast h1`. Rewrite `h2` using `[hy]`. Simplify using `only [map_smul, LinearMap.smul_apply, smul_eq_mul] at h2`.

Establish `h3 : 0 < ((d : ℤ) : ℚ) * ((d : ℤ) : ℚ)` using `mul_self_pos.2 hd0`. Use the polynomial consequences of the given equalities and inequalities. Use `haveI : Invertible (2 : ℚ) := invertibleOfNonzero two_ne_zero`. Take `⟨w, hw⟩` from `LinearMap.BilinForm.exists_orthogonal_basis hBsymm`. Establish `hexp : ∀ v, Bq v v = ∑ k, (w.repr v k) ^ 2 * Bq (w k) (w k)`.

Introduce `v`. Use `conv_lhs => rw [← w.sum_repr v]`. Simplify using `only [map_sum, LinearMap.sum_apply, map_smul, LinearMap.smul_apply, smul_eq_mul]`. Use `Finset.sum_congr rfl fun k _ => ?_` and prove the remaining obligations. Rewrite using `[Finset.sum_eq_single k]`.

Expand and normalize the polynomial expressions, which then agree. Introduce `l _ hlk`. Rewrite using `[hw hlk]`. Expand and normalize the polynomial expressions, which then agree. Introduce `h`.

Conclude with `absurd (Finset.mem_univ k) h`. Establish `hdpos : ∀ k, 0 < Bq (w k) (w k)` using `fun k => hqpos _ (w.ne_zero k)`. Use `set A : ℚ := ∑ k, max 1 ((L : ℚ) / Bq (w k) (w k)) with hAdef`. Use `set T : ℚ := ∑ i, A * ∑ k, |w k i| with hTdef`. Establish `hA : 0 ≤ A` using `Finset.sum_nonneg fun k _ => le_trans zero_le_one (le_max_left _ _)`.

Establish `hcoord : ∀ v, Bq v v ≤ L → ∀ i, |v i| ≤ T`. Introduce `v hv i`. Establish `hc : ∀ k, |w.repr v k| ≤ A`. Introduce `k`. Establish `h1 : (w.repr v k) ^ 2 * Bq (w k) (w k) ≤ L`.

Rewrite `hv` using `[hexp]`. Use `le_trans ?_ hv` and prove the remaining obligations. Conclude with `Finset.single_le_sum (f := fun k => (w.repr v k) ^ 2 * Bq (w k) (w k)) (fun k _ => mul_nonneg (sq_nonneg _) (hdpos k).le) (Finset.mem_univ k)`. Establish `h2 : |w.repr v k| ≤ max 1 ((L : ℚ) / Bq (w k) (w k))`. Break down `le_or_gt (|w.repr v k|) 1 with h | h` into its components or cases.

Conclude with `h.trans (le_max_left _ _)`. Use `le_trans ?_ (le_max_right _ _)` and prove the remaining obligations. Rewrite using `[le_div_iff₀ (hdpos k)]`. Establish `h3 : |w.repr v k| ≤ (w.repr v k) ^ 2` using `by rw [← sq_abs]; nlinarith`. Use polynomial arithmetic with `[hdpos k]`.

Use `h2.trans ?_` and prove the remaining obligations. Conclude with `Finset.single_le_sum (f := fun k => max 1 ((L : ℚ) / Bq (w k) (w k))) (fun k _ => le_trans zero_le_one (le_max_left _ _)) (Finset.mem_univ k)`. Establish `hvi : v i = ∑ k, w.repr v k * w k i` using `by conv_lhs => rw [← w.sum_repr v]`. Simplify using `[Finset.sum_apply]`. Combine the equalities or inequalities in the displayed calculation.

Rewrite using `[abs_mul]`. Conclude with `mul_le_mul_of_nonneg_right (hc k) (abs_nonneg _)`. Use `_ = A * ∑ k, |w k i| := (Finset.mul_sum _ _ _).symm`. Use `_ ≤ T := Finset.single_le_sum (f := fun i => A * ∑ k, |w k i|) (fun i _ => mul_nonneg hA (Finset.sum_nonneg fun k _ => abs_nonneg _)) (Finset.mem_univ i)`. Set `ψ : X → Module.Free.ChooseBasisIndex ℤ X → ℤ` to `fun y i => b.repr y i`.

Establish `hψ : Function.Injective ψ`. Introduce `y z h`. Apply `b.repr.injective` to reduce the goal to its premises. Use extensionality with `i`. Conclude with `congrFun h i`.

Use `((Set.finite_Icc (fun _ => -⌈T⌉) (fun _ => ⌈T⌉)).preimage hψ.injOn).subset ?_` and prove the remaining obligations. Introduce `y hy`. Establish `hy' : Bq (φ y) (φ y) ≤ L` using `by rw [← hφ]; exact_mod_cast hy`. Establish `h` using `hcoord _ hy'`. Use `⟨fun i => ?_, fun i => ?_⟩` and prove the remaining obligations.

Establish `h4` using `(abs_le.1 ((h i).trans (Int.le_ceil T))).1 show -⌈T⌉ ≤ b.repr y i`. Simplify using `only [φ] at h4`. Conclude with `h4` after adjusting the coercions. Establish `h4` using `(abs_le.1 ((h i).trans (Int.le_ceil T))).2 show b.repr y i ≤ ⌈T⌉`. Simplify using `only [φ] at h4`.

Conclude with `h4` after adjusting the coercions.
-/
private theorem finite_setOf_bilin_self_le_of_posDef {X : Type} [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X]
    (B : LinearMap.BilinForm ℤ X) (hsymm : ∀ y z, B y z = B z y) (hpos : ∀ y, y ≠ 0 → 0 < B y y) (L : ℤ) :
    {y | B y y ≤ L}.Finite := by
  classical
  set b := Module.Free.chooseBasis ℤ X with hb
  let M : Matrix (Module.Free.ChooseBasisIndex ℤ X) (Module.Free.ChooseBasisIndex ℤ X) ℚ :=
    Matrix.of fun i j => (B (b i) (b j) : ℚ)
  let Bq := Matrix.toBilin' M
  let φ : X → Module.Free.ChooseBasisIndex ℤ X → ℚ := fun y i => (b.repr y i : ℚ)
  have hφ : ∀ y z, ((B y z : ℤ) : ℚ) = Bq (φ y) (φ z) := by
    intro y z
    rw [Matrix.toBilin'_apply]
    conv_lhs => rw [← b.sum_repr y, ← b.sum_repr z]
    simp only [map_sum, LinearMap.sum_apply, map_smul, LinearMap.smul_apply, smul_eq_mul, Int.cast_sum,
      Int.cast_mul, Finset.mul_sum, M, φ, Matrix.of_apply]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    ring
  have hBsymm : LinearMap.IsSymm Bq := by
    refine LinearMap.isSymm_iff_eq_flip.2 (LinearMap.ext₂ fun x y => ?_)
    rw [LinearMap.flip_apply, Matrix.toBilin'_apply, Matrix.toBilin'_apply, Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    simp only [M, Matrix.of_apply, hsymm (b i) (b j)]
    ring
  have hqpos : ∀ v, v ≠ 0 → 0 < Bq v v := by
    intro v hv
    obtain ⟨d, hd⟩ := IsLocalization.exist_integer_multiples (nonZeroDivisors ℤ) Finset.univ v
    choose n hn using fun i => hd i (Finset.mem_univ i)
    have hd0 : ((d : ℤ) : ℚ) ≠ 0 := by exact_mod_cast nonZeroDivisors.coe_ne_zero d
    set y : X := b.equivFun.symm n
    have hy : φ y = ((d : ℤ) : ℚ) • v := by
      funext i
      have := hn i
      simp only [algebraMap_int_eq, eq_intCast, zsmul_eq_mul] at this
      have hr : b.repr y i = n i := by rw [← b.equivFun_apply, LinearEquiv.apply_symm_apply]
      simp only [φ, Pi.smul_apply, smul_eq_mul, hr]
      exact this
    have hy0 : y ≠ 0 := by
      intro h
      apply hv
      have h2 : ((d : ℤ) : ℚ) • v = 0 := by rw [← hy, h]; funext i; simp [φ]
      exact (smul_eq_zero.1 h2).resolve_left hd0
    have h1 := hpos y hy0
    have h2 : (0 : ℚ) < Bq (φ y) (φ y) := by rw [← hφ]; exact_mod_cast h1
    rw [hy] at h2
    simp only [map_smul, LinearMap.smul_apply, smul_eq_mul] at h2
    have h3 : 0 < ((d : ℤ) : ℚ) * ((d : ℤ) : ℚ) := mul_self_pos.2 hd0
    nlinarith
  haveI : Invertible (2 : ℚ) := invertibleOfNonzero two_ne_zero
  obtain ⟨w, hw⟩ := LinearMap.BilinForm.exists_orthogonal_basis hBsymm
  have hexp : ∀ v, Bq v v = ∑ k, (w.repr v k) ^ 2 * Bq (w k) (w k) := by
    intro v
    conv_lhs => rw [← w.sum_repr v]
    simp only [map_sum, LinearMap.sum_apply, map_smul, LinearMap.smul_apply, smul_eq_mul]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Finset.sum_eq_single k]
    · ring
    · intro l _ hlk
      rw [hw hlk]
      ring
    · intro h
      exact absurd (Finset.mem_univ k) h
  have hdpos : ∀ k, 0 < Bq (w k) (w k) := fun k => hqpos _ (w.ne_zero k)
  set A : ℚ := ∑ k, max 1 ((L : ℚ) / Bq (w k) (w k)) with hAdef
  set T : ℚ := ∑ i, A * ∑ k, |w k i| with hTdef
  have hA : 0 ≤ A := Finset.sum_nonneg fun k _ => le_trans zero_le_one (le_max_left _ _)
  have hcoord : ∀ v, Bq v v ≤ L → ∀ i, |v i| ≤ T := by
    intro v hv i
    have hc : ∀ k, |w.repr v k| ≤ A := by
      intro k
      have h1 : (w.repr v k) ^ 2 * Bq (w k) (w k) ≤ L := by
        rw [hexp] at hv
        refine le_trans ?_ hv
        exact Finset.single_le_sum (f := fun k => (w.repr v k) ^ 2 * Bq (w k) (w k))
          (fun k _ => mul_nonneg (sq_nonneg _) (hdpos k).le) (Finset.mem_univ k)
      have h2 : |w.repr v k| ≤ max 1 ((L : ℚ) / Bq (w k) (w k)) := by
        rcases le_or_gt (|w.repr v k|) 1 with h | h
        · exact h.trans (le_max_left _ _)
        · refine le_trans ?_ (le_max_right _ _)
          rw [le_div_iff₀ (hdpos k)]
          have h3 : |w.repr v k| ≤ (w.repr v k) ^ 2 := by rw [← sq_abs]; nlinarith
          nlinarith [hdpos k]
      refine h2.trans ?_
      exact Finset.single_le_sum (f := fun k => max 1 ((L : ℚ) / Bq (w k) (w k)))
        (fun k _ => le_trans zero_le_one (le_max_left _ _)) (Finset.mem_univ k)
    have hvi : v i = ∑ k, w.repr v k * w k i := by
      conv_lhs => rw [← w.sum_repr v]
      simp [Finset.sum_apply]
    calc |v i| ≤ ∑ k, |w.repr v k * w k i| := by rw [hvi]; exact Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ k, A * |w k i| := Finset.sum_le_sum fun k _ => by
          rw [abs_mul]; exact mul_le_mul_of_nonneg_right (hc k) (abs_nonneg _)
      _ = A * ∑ k, |w k i| := (Finset.mul_sum _ _ _).symm
      _ ≤ T := Finset.single_le_sum (f := fun i => A * ∑ k, |w k i|)
          (fun i _ => mul_nonneg hA (Finset.sum_nonneg fun k _ => abs_nonneg _)) (Finset.mem_univ i)
  let ψ : X → Module.Free.ChooseBasisIndex ℤ X → ℤ := fun y i => b.repr y i
  have hψ : Function.Injective ψ := by
    intro y z h
    apply b.repr.injective
    ext i
    exact congrFun h i
  refine ((Set.finite_Icc (fun _ => -⌈T⌉) (fun _ => ⌈T⌉)).preimage hψ.injOn).subset ?_
  intro y hy
  have hy' : Bq (φ y) (φ y) ≤ L := by rw [← hφ]; exact_mod_cast hy
  have h := hcoord _ hy'
  refine ⟨fun i => ?_, fun i => ?_⟩
  · have h4 := (abs_le.1 ((h i).trans (Int.le_ceil T))).1
    show -⌈T⌉ ≤ b.repr y i
    simp only [φ] at h4
    exact_mod_cast h4
  · have h4 := (abs_le.1 ((h i).trans (Int.le_ceil T))).2
    show b.repr y i ≤ ⌈T⌉
    simp only [φ] at h4
    exact_mod_cast h4

open scoped BigOperators in
/- English proof (translation)
Introduce `x y h`. Establish `h' : m • x = m • y` using `add_left_cancel h`. Apply `(Module.Free.chooseBasis ℤ X).repr.injective` to reduce the goal to its premises. Use extensionality with `i`. Use `congrArg (fun z => (Module.Free.chooseBasis ℤ X).repr z i) h'` as an intermediate fact.

Simplify using `only [map_nsmul, Finsupp.smul_apply, nsmul_eq_mul] at this`. Conclude with `mul_left_cancel₀ (by exact_mod_cast hm) this`.
-/
private theorem injective_add_nsmul_of_ne_zero {X : Type} [AddCommGroup X] [Module.Free ℤ X] (a : X) {m : ℕ}
    (hm : m ≠ 0) : Function.Injective (fun χ : X => a + m • χ) := by
  intro x y h
  have h' : m • x = m • y := add_left_cancel h
  apply (Module.Free.chooseBasis ℤ X).repr.injective
  ext i
  have := congrArg (fun z => (Module.Free.chooseBasis ℤ X).repr z i) h'
  simp only [map_nsmul, Finsupp.smul_apply, nsmul_eq_mul] at this
  exact mul_left_cancel₀ (by exact_mod_cast hm) this

open scoped BigOperators in
/- English proof (translation)
Establish `h` using `Finset.tsum_subtype' hS.toFinset g`. Rewrite `h` using `[hS.coe_toFinset]`. Rewrite using `[finsum_mem_eq_finite_toFinset_sum _ hS, h]`.
-/
private theorem tsum_subtype_eq_finsum_mem_of_finite {X M : Type} [AddCommMonoid M] [TopologicalSpace M]
    [T2Space M] (S : Set X) (hS : S.Finite) (g : X → M) : ∑' b : S, g b = ∑ᶠ x ∈ S, g x := by
  have h := Finset.tsum_subtype' hS.toFinset g
  rw [hS.coe_toFinset] at h
  rw [finsum_mem_eq_finite_toFinset_sum _ hS, h]

open scoped BigOperators in
/- English proof (translation)
Use `set a : N.X := Multiplicative.toAdd (p : Multiplicative N.X × N.Gt).1 with ha`. Use `set q : N.X → ℤ := fun χ => β.be (a + m • χ) (a + m • χ) / (2 * (m : ℤ) ^ 2) with hq`. Establish `hm0 : m ≠ 0` using `hodd.pos.ne'`. Establish `hden : (0 : ℤ) < 2 * (m : ℤ) ^ 2` using `by positivity`. Establish `hq0 : ∀ χ, 0 ≤ q χ`.

Introduce `χ`. Use `Int.ediv_nonneg ?_ hden.le` and prove the remaining obligations. Distinguish the cases in `h : a + m • χ = 0`. Rewrite using `[h]`. Simplify using the standard rewrite rules.

Conclude with `(β.pos _ h).le`. Establish `hfin : ∀ K : ℤ, {χ | q χ ≤ K}.Finite`. Introduce `K`. Use `((finite_setOf_bilin_self_le_of_posDef β.be β.symm β.pos ((K + 1) * (2 * (m : ℤ) ^ 2))).preimage (injective_add_nsmul_of_ne_zero a hm0).injOn).subset ?_` and prove the remaining obligations. Introduce `χ hχ`.

Simplify using `only [Set.mem_setOf_eq, Set.mem_preimage] at hχ ⊢`. Establish `h1` using `Int.lt_mul_ediv_self_add (x := β.be (a + m • χ) (a + m • χ)) hden`. Establish `h2 : 2 * (m : ℤ) ^ 2 * (β.be (a + m • χ) (a + m • χ) / (2 * (m : ℤ) ^ 2)) ≤ 2 * (m : ℤ) ^ 2 * K` using `mul_le_mul_of_nonneg_left hχ hden.le`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hfinS : ∀ n : ℕ, {χ | q χ = n}.Finite` using `fun n => (hfin n).subset fun χ hχ => le_of_eq hχ`.

Use `set Q : N.X → ℕ := fun χ => (q χ).toNat with hQdef`. Establish `hQ : ∀ χ, ((Q χ : ℕ) : ℤ) = q χ` using `fun χ => Int.toNat_of_nonneg (hq0 χ)`. Establish `hpow : ∀ χ, ((u ^ q χ : Cˣ) : C) = (u : C) ^ Q χ`. Introduce `χ`. Use `conv_lhs => rw [← hQ χ]`.

Rewrite using `[zpow_natCast, Units.val_pow_eq_pow_val]`. Use `set f : N.X → C := fun χ => (u : C) ^ Q χ * N.txT m p χ with hf`. Establish `htw : (N.twist β u).tx m (N.twQ β u hm p) = ∑' χ, f χ`. Unfold `_root_.GlobalTheory.Ex.NumD.tx`. Use `tsum_congr fun χ => ?_` and prove the remaining obligations.

Rewrite using `[N.twist_txT β u m hm hodd p χ]`. Conclude with `congrArg (· * N.txT m p χ) (hpow χ)`. Establish `hcoeff' : ∀ n : ℕ, PowerSeries.coeff n (N.arcTx β.be m p) = ∑ᶠ χ ∈ {χ | q χ = n}, N.txT m p χ`. Introduce `n`. Unfold `_root_.GlobalTheory.Ex.NumD.arcTx`.

Rewrite using `[PowerSeries.coeff_mk]`. Both sides reduce to the same expression. Establish `hcn : ∀ n : ℕ, ‖PowerSeries.coeff n (N.arcTx β.be m p)‖ ≤ 1`. Introduce `n`. Rewrite using `[hcoeff', finsum_mem_eq_finite_toFinset_sum _ (hfinS n)]`.

Conclude with `IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one fun χ _ => hbd χ`. Establish `hnorm : ∀ χ, ‖f χ‖ ≤ ‖(u : C)‖ ^ Q χ` using `fun χ => by`. Rewrite using `[hf, norm_mul, norm_pow]`. Conclude with `mul_le_of_le_one_right (by positivity) (hbd χ)`. Establish `hQtend : Filter.Tendsto Q Filter.cofinite Filter.atTop`.

Use `Filter.tendsto_atTop.2 fun K => Filter.eventually_cofinite.2 ?_` and prove the remaining obligations. Use `(hfin K).subset fun χ hχ => ?_` and prove the remaining obligations. Simplify using `only [Set.mem_setOf_eq, not_le] at hχ ⊢`. Use `hQ χ` as an intermediate fact. Use linear arithmetic over natural numbers and integers.

Establish `hsum : Summable f`. Use `NonarchimedeanAddGroup.summable_of_tendsto_cofinite_zero ?_` and prove the remaining obligations. Rewrite using `[tendsto_zero_iff_norm_tendsto_zero]`. Conclude with `squeeze_zero (fun χ => norm_nonneg _) hnorm ((tendsto_pow_atTop_nhds_zero_of_lt_one (norm_nonneg _) hu).comp hQtend)`. Establish `hcoeff : ∀ n : ℕ, ∑' b : ↑(Q ⁻¹' {n}), f b = PowerSeries.coeff n (N.arcTx β.be m p) * (u : C) ^ n`.

Introduce `n`. Establish `hset : Q ⁻¹' {n} = {χ | q χ = n}`. Use extensionality with `χ`. Simplify using `only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_setOf_eq]`. Use `hQ χ` as an intermediate fact.

Use linear arithmetic over natural numbers and integers. Establish `hterm : ∀ b : ↑(Q ⁻¹' {n}), f b = (u : C) ^ n * N.txT m p b`. Introduce `b`. Establish `hb : Q b = n` using `b.2`. Rewrite using `[hf]`.

Simplify using `only [hb]`. Rewrite using `[tsum_congr hterm, tsum_mul_left, hset, tsum_subtype_eq_finsum_mem_of_finite _ (hfinS n), hcoeff', mul_comm]`. Establish `hfib` using `hsum.hasSum.tsum_fiberwise Q`. Rewrite `hfib` using `[show (fun n => ∑' b : ↑(Q ⁻¹' {n}), f b) = fun n => PowerSeries.coeff n (N.arcTx β.be m p) * (u : C) ^ n from funext hcoeff]`. Use `⟨?_, ?_⟩` and prove the remaining obligations.

Use `Summable.of_nonneg_of_le (fun n => norm_nonneg _) (fun n => ?_) (summable_geometric_of_lt_one (norm_nonneg _) hu)` and prove the remaining obligations. Rewrite using `[norm_mul, norm_pow]`. Conclude with `mul_le_of_le_one_left (by positivity) (hcn n)`. Rewrite using `[htw]`. Conclude with `hfib.tsum_eq`.
-/
private theorem absSumAt_arcTx_twist_tx {C : Type} [NontriviallyNormedField C]
    [IsUltrametricDist C] [CompleteSpace C] (N : _root_.GlobalTheory.Ex.NumD C) {k : ℕ}
    (β : N.Form k) (m : ℕ) (hm : m ^ 2 ∣ k) (hodd : Odd m)
    (p : N.QT (m ^ 2))
    (hbd : ∀ χ, ‖N.txT m p χ‖ ≤ 1) (u : Cˣ) (hu : ‖(u : C)‖ < 1) :
    _root_.GlobalTheory.BddArc.AbsSumAt (u : C)
      (N.arcTx β.be m p)
      ((N.twist β u).tx m (N.twQ β u hm p)) := by
  classical
  set a : N.X := Multiplicative.toAdd (p : Multiplicative N.X × N.Gt).1 with ha
  set q : N.X → ℤ := fun χ =>
    β.be (a + m • χ) (a + m • χ) / (2 * (m : ℤ) ^ 2) with hq
  have hm0 : m ≠ 0 := hodd.pos.ne'
  have hden : (0 : ℤ) < 2 * (m : ℤ) ^ 2 := by positivity
  have hq0 : ∀ χ, 0 ≤ q χ := by
    intro χ
    refine Int.ediv_nonneg ?_ hden.le
    by_cases h : a + m • χ = 0
    · rw [h]; simp
    · exact (β.pos _ h).le
  have hfin : ∀ K : ℤ, {χ | q χ ≤ K}.Finite := by
    intro K
    refine ((finite_setOf_bilin_self_le_of_posDef β.be β.symm β.pos
      ((K + 1) * (2 * (m : ℤ) ^ 2))).preimage (injective_add_nsmul_of_ne_zero a hm0).injOn).subset ?_
    intro χ hχ
    simp only [Set.mem_setOf_eq, Set.mem_preimage] at hχ ⊢
    have h1 := Int.lt_mul_ediv_self_add
      (x := β.be (a + m • χ) (a + m • χ)) hden
    have h2 : 2 * (m : ℤ) ^ 2 * (β.be (a + m • χ) (a + m • χ) / (2 * (m : ℤ) ^ 2))
        ≤ 2 * (m : ℤ) ^ 2 * K := mul_le_mul_of_nonneg_left hχ hden.le
    linarith
  have hfinS : ∀ n : ℕ, {χ | q χ = n}.Finite := fun n =>
    (hfin n).subset fun χ hχ => le_of_eq hχ
  set Q : N.X → ℕ := fun χ => (q χ).toNat with hQdef
  have hQ : ∀ χ, ((Q χ : ℕ) : ℤ) = q χ := fun χ => Int.toNat_of_nonneg (hq0 χ)
  have hpow : ∀ χ, ((u ^ q χ : Cˣ) : C) = (u : C) ^ Q χ := by
    intro χ
    conv_lhs => rw [← hQ χ]
    rw [zpow_natCast, Units.val_pow_eq_pow_val]
  set f : N.X → C := fun χ => (u : C) ^ Q χ * N.txT m p χ with hf
  have htw : (N.twist β u).tx m (N.twQ β u hm p)
      = ∑' χ, f χ := by
    unfold _root_.GlobalTheory.Ex.NumD.tx
    refine tsum_congr fun χ => ?_
    rw [N.twist_txT β u m hm hodd p χ]
    exact congrArg (· * N.txT m p χ) (hpow χ)
  have hcoeff' : ∀ n : ℕ, PowerSeries.coeff n (N.arcTx β.be m p)
      = ∑ᶠ χ ∈ {χ | q χ = n}, N.txT m p χ := by
    intro n
    unfold _root_.GlobalTheory.Ex.NumD.arcTx
    rw [PowerSeries.coeff_mk]
    rfl
  have hcn : ∀ n : ℕ,
      ‖PowerSeries.coeff n (N.arcTx β.be m p)‖ ≤ 1 := by
    intro n
    rw [hcoeff', finsum_mem_eq_finite_toFinset_sum _ (hfinS n)]
    exact IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one fun χ _ => hbd χ
  have hnorm : ∀ χ, ‖f χ‖ ≤ ‖(u : C)‖ ^ Q χ := fun χ => by
    rw [hf, norm_mul, norm_pow]
    exact mul_le_of_le_one_right (by positivity) (hbd χ)
  have hQtend : Filter.Tendsto Q Filter.cofinite Filter.atTop := by
    refine Filter.tendsto_atTop.2 fun K => Filter.eventually_cofinite.2 ?_
    refine (hfin K).subset fun χ hχ => ?_
    simp only [Set.mem_setOf_eq, not_le] at hχ ⊢
    have := hQ χ
    omega
  have hsum : Summable f := by
    refine NonarchimedeanAddGroup.summable_of_tendsto_cofinite_zero ?_
    rw [tendsto_zero_iff_norm_tendsto_zero]
    exact squeeze_zero (fun χ => norm_nonneg _) hnorm
      ((tendsto_pow_atTop_nhds_zero_of_lt_one (norm_nonneg _) hu).comp hQtend)
  have hcoeff : ∀ n : ℕ, ∑' b : ↑(Q ⁻¹' {n}), f b =
      PowerSeries.coeff n (N.arcTx β.be m p) * (u : C) ^ n := by
    intro n
    have hset : Q ⁻¹' {n} = {χ | q χ = n} := by
      ext χ
      simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_setOf_eq]
      have := hQ χ
      omega
    have hterm : ∀ b : ↑(Q ⁻¹' {n}), f b = (u : C) ^ n * N.txT m p b := by
      intro b
      have hb : Q b = n := b.2
      rw [hf]
      simp only [hb]
    rw [tsum_congr hterm, tsum_mul_left, hset,
      tsum_subtype_eq_finsum_mem_of_finite _ (hfinS n), hcoeff', mul_comm]
  have hfib := hsum.hasSum.tsum_fiberwise Q
  rw [show (fun n => ∑' b : ↑(Q ⁻¹' {n}), f b) = fun n =>
      PowerSeries.coeff n (N.arcTx β.be m p) * (u : C) ^ n
      from funext hcoeff] at hfib
  refine ⟨?_, ?_⟩
  · refine Summable.of_nonneg_of_le (fun n => norm_nonneg _) (fun n => ?_)
      (summable_geometric_of_lt_one (norm_nonneg _) hu)
    rw [norm_mul, norm_pow]
    exact mul_le_of_le_one_left (by positivity) (hcn n)
  · rw [htw]
    exact hfib.tsum_eq

open scoped BigOperators in

/- English proof (translation)
Introduce `C _ _ _ N k β m hm hodd ι p hbd F hF u hu`. Establish `h` using `_root_.GlobalTheory.BddArc.AbsSumAt.aeval (u := (u : C)) (fun i => absSumAt_arcTx_twist_tx N β m hm hodd (p i) (hbd i) u hu) F`. Rewrite `h` using `[hF]`. Rewrite using `[← h.2]`. Simplify using the standard rewrite rules.
-/
theorem _root_.GlobalTheory.eval_twist_tx_eq_zero_of_aeval_arcTx : ∀ (C : Type) [NontriviallyNormedField C]
    [IsUltrametricDist C] [CompleteSpace C] (N : _root_.GlobalTheory.Ex.NumD C) (k : ℕ)
    (β : N.Form k) (m : ℕ) (hm : m ^ 2 ∣ k), Odd m →
    ∀ (ι : Type) (p : ι → N.QT (m ^ 2)),
    (∀ i χ, ‖N.txT m (p i) χ‖ ≤ 1) → ∀ (F : MvPolynomial ι C),
    MvPolynomial.aeval (fun i => N.arcTx β.be m (p i)) F = 0 →
    ∀ u : Cˣ, ‖(u : C)‖ < 1 →
    MvPolynomial.eval (fun i => (N.twist β u).tx m
      (N.twQ β u hm (p i))) F = 0 := by
  intro C _ _ _ N k β m hm hodd ι p hbd F hF u hu
  have h := _root_.GlobalTheory.BddArc.AbsSumAt.aeval (u := (u : C))
    (fun i => absSumAt_arcTx_twist_tx N β m hm hodd (p i) (hbd i) u hu) F
  rw [hF] at h
  rw [← h.2]
  simp

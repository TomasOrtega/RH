import PositivityTheory.AutomorphicForms.PublishedInputs.HilbertEisenstein.IdeleModuleInfIdDetLe
import GroundTheory.GlobalFields.Adele.IntegersLattice

noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V.Af UpperTheory.V.Base
open scoped Matrix nonZeroDivisors
open MeasureTheory GroundTheory.Global GroundTheory.Global.IdeleGroup UpperTheory.V.Sd UpperTheory.V.Published

namespace UpperTheory.HilbertEisensteinWeightOne.eisensteinGrowth

variable {F : Type} [Field F] [NumberField F] [IsTotallyReal F]

def sig (v : InfinitePlace F) (x : F) : ℝ := UpperTheory.V.TR.pInf F (algebraMap F (Ad F) x) v

/- English proof (translation)
Establish `h` using `(InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal (IsTotallyReal.isReal v)).norm_map_of_map_zero (map_zero _) (x.1 v)`. Rewrite `h` using `[Real.norm_eq_abs]`. Conclude with `h`.
-/
theorem abs_pInf (x : Ad F) (v : InfinitePlace F) : |UpperTheory.V.TR.pInf F x v| = ‖x.1 v‖ := by
  have h := (InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal
    (IsTotallyReal.isReal v)).norm_map_of_map_zero (map_zero _) (x.1 v)
  rw [Real.norm_eq_abs] at h
  exact h

/- English proof (translation)
Rewrite using `[sig, abs_pInf]`. Conclude with `GroundTheory.Global.norm_algebraMap_apply F x v`.
-/
theorem abs_sig (v : InfinitePlace F) (x : F) : |sig v x| = v x := by
  rw [sig, abs_pInf]
  exact GroundTheory.Global.norm_algebraMap_apply F x v

/- English proof (translation)
Establish `hprod : ∀ y : F, ∏ v, |sig v y| = |((Algebra.norm ℚ y : ℚ) : ℝ)|`. Introduce `y`. Repeatedly rewrite using `[abs_sig]`. Rewrite using `[← Rat.cast_abs, ← InfinitePlace.prod_eq_abs_norm]`. Use `Finset.prod_congr rfl fun w _ => ?_` and prove the remaining obligations.

Rewrite using `[(IsTotallyReal.isReal w).mult_eq_one, pow_one]`. Take `⟨r, hr⟩` from `hx`. Establish `hDF : (D : F) ≠ 0` using `(map_ne_zero_iff _ (IsFractionRing.injective (𝓞 F) F)).mpr hD`. Establish `hr0 : r ≠ 0`. Introduce and unpack `rfl`.

Establish `: (D : F) * x = 0` using `by rw [hr]; simp`. Conclude with `mul_ne_zero hDF hx0 this`. Rewrite using `[hprod, ← abs_mul, ← Rat.cast_mul, ← map_mul, hr]`. Conclude with `GroundTheory.Global.one_le_abs_norm_of_ne_zero hr0`.
-/
theorem one_le_norm_mul_prod {D : 𝓞 F} (hD : D ≠ 0) {x : F} (hx0 : x ≠ 0) (hx : ∃ r : 𝓞 F, (D : F) * x = r) :
    1 ≤ |((Algebra.norm ℚ (D : F) : ℚ) : ℝ)| * ∏ v, |sig v x| := by
  have hprod : ∀ y : F, ∏ v, |sig v y| = |((Algebra.norm ℚ y : ℚ) : ℝ)| := by
    intro y
    simp_rw [abs_sig]
    rw [← Rat.cast_abs, ← InfinitePlace.prod_eq_abs_norm]
    refine Finset.prod_congr rfl fun w _ => ?_
    rw [(IsTotallyReal.isReal w).mult_eq_one, pow_one]
  obtain ⟨r, hr⟩ := hx
  have hDF : (D : F) ≠ 0 := (map_ne_zero_iff _ (IsFractionRing.injective (𝓞 F) F)).mpr hD
  have hr0 : r ≠ 0 := by
    rintro rfl
    have : (D : F) * x = 0 := by rw [hr]; simp
    exact mul_ne_zero hDF hx0 this
  rw [hprod, ← abs_mul, ← Rat.cast_mul, ← map_mul, hr]
  exact GroundTheory.Global.one_le_abs_norm_of_ne_zero hr0

omit [IsTotallyReal F] in
/- English proof (translation)
Use `⟨Real.exp 1 * (Nat.factorial (1 + k + m) : ℝ), by positivity, fun p q => ?_⟩` and prove the remaining obligations. Use `set s := p ^ 2 + q ^ 2 with hs`. Establish `hs0 : 0 ≤ s` using `by positivity`. Establish `hnorm : ‖((p : ℂ) + Complex.I * (q : ℂ)) * Complex.exp (-(Real.pi : ℂ) * ((p : ℂ) ^ 2 + (q : ℂ) ^ 2))‖ = Real.sqrt s * Real.exp (-Real.pi * s)`. Rewrite using `[norm_mul]`.

Use `congr 1`. Rewrite using `[mul_comm Complex.I, Complex.norm_add_mul_I]`. Establish `: -(Real.pi : ℂ) * ((p : ℂ) ^ 2 + (q : ℂ) ^ 2) = ((-Real.pi * s : ℝ) : ℂ)`. Rewrite using `[hs]`. Use `push_cast`.

Expand and normalize the polynomial expressions, which then agree. Rewrite using `[this, Complex.norm_exp_ofReal]`. Use `set ρ := max |p| |q| with hρ`. Establish `hρ0 : 0 ≤ ρ` using `le_max_of_le_left (abs_nonneg p)`. Establish `hρs : ρ ^ 2 ≤ s`.

Break down `max_choice |p| |q| with h | h` into its components or cases. Rewrite using `[hρ, h, sq_abs]`. Use polynomial arithmetic with `[sq_nonneg q]`. Rewrite using `[hρ, h, sq_abs]`. Use polynomial arithmetic with `[sq_nonneg p]`.

Establish `hsq : Real.sqrt s ≤ 1 + s` using `by nlinarith [Real.sq_sqrt hs0, Real.sqrt_nonneg s]`. Establish `hρ1 : ρ ≤ 1 + s`. Establish `h` using `Real.sqrt_le_sqrt hρs`. Rewrite `h` using `[Real.sqrt_sq hρ0]`. Combine the linear equalities and inequalities to obtain the conclusion.

Establish `hρ2 : 1 + ρ ^ 2 ≤ 1 + s` using `by linarith`. Establish `hexp : Real.exp (-Real.pi * s) ≤ Real.exp (-s)` using `Real.exp_le_exp.2 (by nlinarith [Real.pi_gt_three])`. Establish `hfact` using `Real.pow_div_factorial_le_exp (1 + s) (by linarith) (1 + k + m)`. Establish `hN : (0 : ℝ) < Nat.factorial (1 + k + m)` using `by positivity`. Rewrite `hfact` using `[div_le_iff₀ hN]`.

Rewrite using `[hnorm]`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[Real.exp_add]`. Expand and normalize the polynomial expressions, which then agree. Use `_ = Real.exp 1 * Nat.factorial (1 + k + m) := by`.

Rewrite using `[← Real.exp_add, add_neg_cancel, Real.exp_zero, mul_one]`.
-/
theorem arch_factor_bound (k m : ℕ) : ∃ C : ℝ, 0 < C ∧ ∀ p q : ℝ,
    ‖((p : ℂ) + Complex.I * (q : ℂ)) * Complex.exp (-(Real.pi : ℂ) * ((p : ℂ) ^ 2 + (q : ℂ) ^ 2))‖ *
      (max |p| |q|) ^ k * (1 + (max |p| |q|) ^ 2) ^ m ≤ C := by
  refine ⟨Real.exp 1 * (Nat.factorial (1 + k + m) : ℝ), by positivity, fun p q => ?_⟩
  set s := p ^ 2 + q ^ 2 with hs
  have hs0 : 0 ≤ s := by positivity
  have hnorm : ‖((p : ℂ) + Complex.I * (q : ℂ)) *
      Complex.exp (-(Real.pi : ℂ) * ((p : ℂ) ^ 2 + (q : ℂ) ^ 2))‖ =
      Real.sqrt s * Real.exp (-Real.pi * s) := by
    rw [norm_mul]
    congr 1
    · rw [mul_comm Complex.I, Complex.norm_add_mul_I]
    · have : -(Real.pi : ℂ) * ((p : ℂ) ^ 2 + (q : ℂ) ^ 2) = ((-Real.pi * s : ℝ) : ℂ) := by
        rw [hs]; push_cast; ring
      rw [this, Complex.norm_exp_ofReal]
  set ρ := max |p| |q| with hρ
  have hρ0 : 0 ≤ ρ := le_max_of_le_left (abs_nonneg p)
  have hρs : ρ ^ 2 ≤ s := by
    rcases max_choice |p| |q| with h | h
    · rw [hρ, h, sq_abs]; nlinarith [sq_nonneg q]
    · rw [hρ, h, sq_abs]; nlinarith [sq_nonneg p]
  have hsq : Real.sqrt s ≤ 1 + s := by nlinarith [Real.sq_sqrt hs0, Real.sqrt_nonneg s]
  have hρ1 : ρ ≤ 1 + s := by
    have h := Real.sqrt_le_sqrt hρs
    rw [Real.sqrt_sq hρ0] at h
    linarith
  have hρ2 : 1 + ρ ^ 2 ≤ 1 + s := by linarith
  have hexp : Real.exp (-Real.pi * s) ≤ Real.exp (-s) :=
    Real.exp_le_exp.2 (by nlinarith [Real.pi_gt_three])
  have hfact := Real.pow_div_factorial_le_exp (1 + s) (by linarith) (1 + k + m)
  have hN : (0 : ℝ) < Nat.factorial (1 + k + m) := by positivity
  rw [div_le_iff₀ hN] at hfact
  rw [hnorm]
  calc Real.sqrt s * Real.exp (-Real.pi * s) * ρ ^ k * (1 + ρ ^ 2) ^ m
      ≤ (1 + s) * Real.exp (-s) * (1 + s) ^ k * (1 + s) ^ m := by
        gcongr
    _ = (1 + s) ^ (1 + k + m) * Real.exp (-s) := by ring
    _ ≤ Real.exp (1 + s) * Nat.factorial (1 + k + m) * Real.exp (-s) := by gcongr
    _ = Real.exp 1 * Nat.factorial (1 + k + m) * (Real.exp s * Real.exp (-s)) := by
        rw [Real.exp_add]; ring
    _ = Real.exp 1 * Nat.factorial (1 + k + m) := by
        rw [← Real.exp_add, add_neg_cancel, Real.exp_zero, mul_one]

omit [IsTotallyReal F] in
/- English proof (translation)
Take `⟨C, hC0, hC⟩` from `arch_factor_bound k m`. Use `⟨C ^ Fintype.card (InfinitePlace F), by positivity, fun x y => ?_⟩` and prove the remaining obligations. Rewrite using `[arch, norm_prod, ← Finset.prod_mul_distrib, ← Finset.card_univ, ← Finset.prod_const]`. Use `Finset.prod_le_prod (fun v _ => by positivity) fun v _ => ?_` and prove the remaining obligations. Rewrite using `[← mul_assoc]`.

Conclude with `hC (x v) (y v)`.
-/
theorem arch_bound (k m : ℕ) : ∃ C : ℝ, 0 < C ∧ ∀ x y : UpperTheory.V.TR.Rinf F,
    ‖arch x y‖ * ∏ v, ((max |x v| |y v|) ^ k * (1 + (max |x v| |y v|) ^ 2) ^ m) ≤ C := by
  obtain ⟨C, hC0, hC⟩ := arch_factor_bound k m
  refine ⟨C ^ Fintype.card (InfinitePlace F), by positivity, fun x y => ?_⟩
  rw [arch, norm_prod, ← Finset.prod_mul_distrib, ← Finset.card_univ, ← Finset.prod_const]
  refine Finset.prod_le_prod (fun v _ => by positivity) fun v _ => ?_
  rw [← mul_assoc]
  exact hC (x v) (y v)

open Classical in
/- English proof (translation)
Establish `hDF : (D : F) ≠ 0` using `(map_ne_zero_iff _ (IsFractionRing.injective (𝓞 F) F)).mpr hD`. Use `set J : (FractionalIdeal (𝓞 F)⁰ F)ˣ := Units.mk0 (FractionalIdeal.spanSingleton (𝓞 F)⁰ (D : F)⁻¹) ((FractionalIdeal.spanSingleton_ne_zero_iff).mpr (inv_ne_zero hDF)) with hJ`. Establish `hmem : ∀ x : F, x ∈ (J : FractionalIdeal (𝓞 F)⁰ F) ↔ ∃ r : 𝓞 F, (D : F) * x = r`. Introduce `x`. Rewrite using `[hJ, Units.val_mk0, FractionalIdeal.mem_spanSingleton]`.

Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨r, rfl⟩`. Use `⟨r, ?_⟩` and prove the remaining obligations. Rewrite using `[Algebra.smul_def, mul_comm, mul_assoc, inv_mul_cancel₀ hDF, mul_one]`. Introduce and unpack `⟨r, hr⟩`.

Use `⟨r, ?_⟩` and prove the remaining obligations. Establish `hr' : algebraMap (𝓞 F) F r = (D : F) * x` using `hr.symm`. Rewrite using `[Algebra.smul_def, hr', mul_comm, ← mul_assoc, inv_mul_cancel₀ hDF, one_mul]`. Use `set n := Module.finrank ℤ (mixedEmbedding.idealLattice F J)`. Use `⟨n + 1, ?_⟩` and prove the remaining obligations.

Establish `hh` using `(GroundTheory.Global.summable_inv_one_add_norm_pow_idealLattice J).mul_left ((2 : ℝ) ^ (n + 1))`. Establish `hs` using `GroundTheory.Global.summable_ite_mem_of_summable_idealLattice J (h := fun e => (2 : ℝ) ^ (n + 1) * ((1 + ‖e‖) ^ (n + 1))⁻¹) hh`. Use `hs.of_nonneg_of_le (fun x => ?_) (fun x => ?_)` and prove the remaining obligations. Use `split_ifs`. Establish `: 0 ≤ ∏ v, (1 + sig v x ^ 2)` using `Finset.prod_nonneg fun v _ => by positivity`.

Check the signs of the components of the expression. Conclude with `le_rfl`. Distinguish the cases in `hx : ∃ r : 𝓞 F, (D : F) * x = r`. Rewrite using `[if_pos hx, if_pos ((hmem x).2 hx)] set P := ∏ v, (1 + sig v x ^ 2) with hP`. Establish `hP1 : ∀ v, 1 + sig v x ^ 2 ≤ P`.

Introduce `v`. Rewrite using `[hP, ← Finset.mul_prod_erase Finset.univ (fun v => 1 + sig v x ^ 2) (Finset.mem_univ v)]`. Establish `h1 : (1 : ℝ) ≤ ∏ w ∈ Finset.univ.erase v, (1 + sig w x ^ 2)`. Use `Finset.prod_le_prod (s := Finset.univ.erase v) (f := fun _ => (1 : ℝ)) (g := fun w => 1 + sig w x ^ 2) (fun _ _ => zero_le_one) (fun w _ => by nlinarith [sq_nonneg (sig w x)])` as an intermediate fact. Simplify using `using this`.

Use polynomial arithmetic with `[sq_nonneg (sig v x)]`. Establish `hPpos : 1 ≤ P`. Take `⟨v⟩` from `(inferInstance : Nonempty (InfinitePlace F))`. Use polynomial arithmetic with `[hP1 v, sq_nonneg (sig v x)]`. Establish `he : ‖mixedEmbedding F x‖ ≤ P`.

Rewrite using `[mixedEmbedding.norm_eq_sup'_normAtPlace]`. Use `Finset.sup'_le _ _ fun v _ => ?_` and prove the remaining obligations. Rewrite using `[mixedEmbedding.normAtPlace_apply, ← abs_sig]`. Use polynomial arithmetic with `[hP1 v, abs_nonneg (sig v x), sq_abs (sig v x)]`. Establish `h1 : (1 + ‖mixedEmbedding F x‖) ^ (n + 1) ≤ 2 ^ (n + 1) * P ^ (n + 1)`.

Rewrite using `[← mul_pow]`. Conclude with `pow_le_pow_left₀ (by positivity) (by linarith) _`. Establish `hpos : 0 < (1 + ‖mixedEmbedding F x‖) ^ (n + 1)` using `by positivity`. Establish `hPn : 0 < P ^ (n + 1)` using `by positivity`. Use `show (P ^ (n + 1))⁻¹ ≤ 2 ^ (n + 1) * ((1 + ‖mixedEmbedding F x‖) ^ (n + 1))⁻¹`.

Rewrite using `[inv_le_iff_one_le_mul₀ hPn]`. Rewrite using `[← div_eq_mul_inv, div_mul_eq_mul_div, le_div_iff₀ hpos, one_mul]`. Combine the linear equalities and inequalities to obtain the conclusion. Rewrite using `[if_neg hx, if_neg (fun h => hx ((hmem x).1 h))]`.
-/
theorem summable_beta (D : 𝓞 F) (hD : D ≠ 0) : ∃ m : ℕ, Summable (fun x : F =>
    if ∃ r : 𝓞 F, (D : F) * x = r then ((∏ v, (1 + sig v x ^ 2)) ^ m)⁻¹ else 0) := by
  have hDF : (D : F) ≠ 0 := (map_ne_zero_iff _ (IsFractionRing.injective (𝓞 F) F)).mpr hD
  set J : (FractionalIdeal (𝓞 F)⁰ F)ˣ := Units.mk0 (FractionalIdeal.spanSingleton (𝓞 F)⁰ (D : F)⁻¹)
    ((FractionalIdeal.spanSingleton_ne_zero_iff).mpr (inv_ne_zero hDF)) with hJ
  have hmem : ∀ x : F, x ∈ (J : FractionalIdeal (𝓞 F)⁰ F) ↔ ∃ r : 𝓞 F, (D : F) * x = r := by
    intro x
    rw [hJ, Units.val_mk0, FractionalIdeal.mem_spanSingleton]
    constructor
    · rintro ⟨r, rfl⟩
      refine ⟨r, ?_⟩
      rw [Algebra.smul_def, mul_comm, mul_assoc, inv_mul_cancel₀ hDF, mul_one]
    · rintro ⟨r, hr⟩
      refine ⟨r, ?_⟩
      have hr' : algebraMap (𝓞 F) F r = (D : F) * x := hr.symm
      rw [Algebra.smul_def, hr', mul_comm, ← mul_assoc, inv_mul_cancel₀ hDF, one_mul]
  set n := Module.finrank ℤ (mixedEmbedding.idealLattice F J)
  refine ⟨n + 1, ?_⟩
  have hh := (GroundTheory.Global.summable_inv_one_add_norm_pow_idealLattice J).mul_left ((2 : ℝ) ^ (n + 1))
  have hs := GroundTheory.Global.summable_ite_mem_of_summable_idealLattice J
    (h := fun e => (2 : ℝ) ^ (n + 1) * ((1 + ‖e‖) ^ (n + 1))⁻¹) hh
  refine hs.of_nonneg_of_le (fun x => ?_) (fun x => ?_)
  · split_ifs
    · have : 0 ≤ ∏ v, (1 + sig v x ^ 2) := Finset.prod_nonneg fun v _ => by positivity
      positivity
    · exact le_rfl
  · by_cases hx : ∃ r : 𝓞 F, (D : F) * x = r
    · rw [if_pos hx, if_pos ((hmem x).2 hx)]
      set P := ∏ v, (1 + sig v x ^ 2) with hP
      have hP1 : ∀ v, 1 + sig v x ^ 2 ≤ P := by
        intro v
        rw [hP, ← Finset.mul_prod_erase Finset.univ (fun v => 1 + sig v x ^ 2) (Finset.mem_univ v)]
        have h1 : (1 : ℝ) ≤ ∏ w ∈ Finset.univ.erase v, (1 + sig w x ^ 2) := by
          have := Finset.prod_le_prod (s := Finset.univ.erase v) (f := fun _ => (1 : ℝ))
            (g := fun w => 1 + sig w x ^ 2) (fun _ _ => zero_le_one) (fun w _ => by nlinarith [sq_nonneg (sig w x)])
          simpa using this
        nlinarith [sq_nonneg (sig v x)]
      have hPpos : 1 ≤ P := by
        obtain ⟨v⟩ := (inferInstance : Nonempty (InfinitePlace F))
        nlinarith [hP1 v, sq_nonneg (sig v x)]
      have he : ‖mixedEmbedding F x‖ ≤ P := by
        rw [mixedEmbedding.norm_eq_sup'_normAtPlace]
        refine Finset.sup'_le _ _ fun v _ => ?_
        rw [mixedEmbedding.normAtPlace_apply, ← abs_sig]
        nlinarith [hP1 v, abs_nonneg (sig v x), sq_abs (sig v x)]
      have h1 : (1 + ‖mixedEmbedding F x‖) ^ (n + 1) ≤ 2 ^ (n + 1) * P ^ (n + 1) := by
        rw [← mul_pow]
        exact pow_le_pow_left₀ (by positivity) (by linarith) _
      have hpos : 0 < (1 + ‖mixedEmbedding F x‖) ^ (n + 1) := by positivity
      have hPn : 0 < P ^ (n + 1) := by positivity
      show (P ^ (n + 1))⁻¹ ≤ 2 ^ (n + 1) * ((1 + ‖mixedEmbedding F x‖) ^ (n + 1))⁻¹
      rw [inv_le_iff_one_le_mul₀ hPn]
      rw [← div_eq_mul_inv, div_mul_eq_mul_div, le_div_iff₀ hpos, one_mul]
      linarith
    · rw [if_neg hx, if_neg (fun h => hx ((hmem x).1 h))]

omit [IsTotallyReal F] in

/- English proof (translation)
Use `set f : Ideles F → ℝ := fun a => ∑ v, (‖((a : Ideles F) : Ad F).1 v‖ + ‖((a⁻¹ : Ideles F) : Ad F).1 v‖)`. Establish `h1 : Continuous (fun a : Ideles F => ((a : Ideles F) : Ad F))` using `Units.continuous_val`. Establish `h2 : Continuous (fun a : Ideles F => ((a⁻¹ : Ideles F) : Ad F))` using `Units.continuous_coe_inv`. Establish `h3 : ∀ v : InfinitePlace F, Continuous (fun x : Ad F => x.1 v)` using `fun v => (continuous_apply v).comp continuous_fst`. Establish `hf : Continuous f`.

Use `continuous_finsetSum _ fun v _ => ?_` and prove the remaining obligations. Conclude with `(continuous_norm.comp ((h3 v).comp h1)).add (continuous_norm.comp ((h3 v).comp h2))`. Take `⟨C, hC⟩` from `hK.exists_bound_of_continuousOn hf.continuousOn`. Use `⟨max C 1, le_max_right _ _, fun a ha v => ?_⟩` and prove the remaining obligations. Establish `h1` using `hC a ha`.

Rewrite `h1` using `[Real.norm_eq_abs]`. Establish `hle : ‖((a : Ideles F) : Ad F).1 v‖ + ‖((a⁻¹ : Ideles F) : Ad F).1 v‖ ≤ f a` using `Finset.single_le_sum (f := fun v => ‖((a : Ideles F) : Ad F).1 v‖ + ‖((a⁻¹ : Ideles F) : Ad F).1 v‖) (fun v _ => by positivity) (Finset.mem_univ v)`. Establish `h2` using `le_abs_self (f a)`. Apply the tactic sequence `constructor <;> nlinarith [norm_nonneg (((a : Ideles F) : Ad F).1 v), norm_nonneg (((a⁻¹ : Ideles F) : Ad F).1 v), le_max_left C 1]`.
-/
theorem exists_bound_inf {K : Set (Ideles F)} (hK : IsCompact K) : ∃ B : ℝ, 1 ≤ B ∧ ∀ a ∈ K, ∀ v,
    ‖((a : Ideles F) : Ad F).1 v‖ ≤ B ∧ ‖((a⁻¹ : Ideles F) : Ad F).1 v‖ ≤ B := by
  set f : Ideles F → ℝ := fun a => ∑ v, (‖((a : Ideles F) : Ad F).1 v‖ + ‖((a⁻¹ : Ideles F) : Ad F).1 v‖)
  have h1 : Continuous (fun a : Ideles F => ((a : Ideles F) : Ad F)) := Units.continuous_val
  have h2 : Continuous (fun a : Ideles F => ((a⁻¹ : Ideles F) : Ad F)) := Units.continuous_coe_inv
  have h3 : ∀ v : InfinitePlace F, Continuous (fun x : Ad F => x.1 v) := fun v =>
    (continuous_apply v).comp continuous_fst
  have hf : Continuous f := by
    refine continuous_finsetSum _ fun v _ => ?_
    exact (continuous_norm.comp ((h3 v).comp h1)).add (continuous_norm.comp ((h3 v).comp h2))
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hf.continuousOn
  refine ⟨max C 1, le_max_right _ _, fun a ha v => ?_⟩
  have h1 := hC a ha
  rw [Real.norm_eq_abs] at h1
  have hle : ‖((a : Ideles F) : Ad F).1 v‖ + ‖((a⁻¹ : Ideles F) : Ad F).1 v‖ ≤ f a :=
    Finset.single_le_sum (f := fun v => ‖((a : Ideles F) : Ad F).1 v‖ + ‖((a⁻¹ : Ideles F) : Ad F).1 v‖)
      (fun v _ => by positivity) (Finset.mem_univ v)
  have h2 := le_abs_self (f a)
  constructor <;> nlinarith [norm_nonneg (((a : Ideles F) : Ad F).1 v), norm_nonneg (((a⁻¹ : Ideles F) : Ad F).1 v),
    le_max_left C 1]

open Classical in
/- English proof (translation)
The claim follows from `|UpperTheory.V.TR.pInf F ((moduleSection (w0 F) t : Ideles F) : Ad F) v| = if v = w0 F then (t : ℝ) else 1 := by rw [abs_pInf, norm_moduleSection_apply] split_ifs with h · have h1 := norm_posRealElem_pow (w0 F) t.2.le rwa [InfinitePlace.mult, if_pos (IsTotallyReal.isReal _), pow_ …`.
-/
theorem abs_pInf_moduleSection (t : {r : ℝ // 0 < r}) (v : InfinitePlace F) :
    |UpperTheory.V.TR.pInf F ((moduleSection (w0 F) t : Ideles F) : Ad F) v| = if v = w0 F then (t : ℝ) else 1 := by
  rw [abs_pInf, norm_moduleSection_apply]
  split_ifs with h
  · have h1 := norm_posRealElem_pow (w0 F) t.2.le
    rwa [InfinitePlace.mult, if_pos (IsTotallyReal.isReal _), pow_one] at h1
  · rfl

end UpperTheory.HilbertEisensteinWeightOne.eisensteinGrowth

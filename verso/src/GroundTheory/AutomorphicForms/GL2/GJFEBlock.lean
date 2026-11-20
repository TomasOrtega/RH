import Mathlib
import GroundTheory.AutomorphicForms.GL2.GJFEDefs
import GroundTheory.AutomorphicForms.GL2.GJFEBlockPoint

noncomputable section

namespace GroundTheory.Automorphic

namespace GodementJacquet

open GLnLocal MeasureTheory Polynomial GJMatrix
open scoped NNReal

variable {F : Type*} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [MeasurableSpace F] [BorelSpace F]
  {m : ℕ} [NeZero m] [MeasurableSpace (GL (Fin m) F)] [BorelSpace (GL (Fin m) F)]
  {H : Type*} [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [LocallyCompactSpace H]
  [T2Space H] [TotallyDisconnectedSpace H]
  {W : Type*} [AddCommGroup W] [Module ℂ W] {σ : Representation ℂ (GL (Fin m) F × H) W}

/- English proof (translation)
Introduce `h`. Take `⟨r, hr⟩` from `RatFunc.denom_div_dvd P Q`. Apply `hQ` to reduce the goal to its premises. Rewrite using `[hr, eval_mul, h, zero_mul]`.
-/
theorem denom_eval_ne_zero_of_div {P Q : ℂ[X]} {x : ℂ} (hQ : Q.eval x ≠ 0) :
    (algebraMap ℂ[X] (RatFunc ℂ) P / algebraMap ℂ[X] (RatFunc ℂ) Q).denom.eval x ≠ 0 := by
  intro h
  obtain ⟨r, hr⟩ := RatFunc.denom_div_dvd P Q
  apply hQ
  rw [hr, eval_mul, h, zero_mul]

def reflPoly (κ : ℂ) (d : ℕ) (P : ℂ[X]) : ℂ[X] :=
  ∑ i ∈ Finset.range (d + 1), C (P.coeff i * κ ^ i) * X ^ (d - i)

/- English proof (translation)
Rewrite using `[reflPoly, eval_finsetSum, eval_eq_sum_range' (Nat.lt_succ_of_le hd), Finset.mul_sum]`. Use `Finset.sum_congr rfl fun i hi => ?_` and prove the remaining obligations. Establish `hid : i ≤ d` using `Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)`. Rewrite using `[eval_mul, eval_C, eval_pow, eval_X, div_pow, mul_div_assoc', pow_sub₀ x hx hid]`. Clear the denominators using the available nonvanishing facts.
-/
theorem eval_reflPoly (κ : ℂ) {d : ℕ} {P : ℂ[X]} (hd : P.natDegree ≤ d) {x : ℂ} (hx : x ≠ 0) :
    (reflPoly κ d P).eval x = x ^ d * P.eval (κ / x) := by
  rw [reflPoly, eval_finsetSum, eval_eq_sum_range' (Nat.lt_succ_of_le hd), Finset.mul_sum]
  refine Finset.sum_congr rfl fun i hi => ?_
  have hid : i ≤ d := Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)
  rw [eval_mul, eval_C, eval_pow, eval_X, div_pow, mul_div_assoc', pow_sub₀ x hx hid]
  field_simp

/- English proof (translation)
Use `set d := max P.natDegree Q.natDegree`. Use `⟨reflPoly κ d P, reflPoly κ d Q, fun x hx hQ => ?_⟩` and prove the remaining obligations. Establish `hQ' : (reflPoly κ d Q).eval x ≠ 0`. Rewrite using `[eval_reflPoly κ (le_max_right _ _) hx]`. Conclude with `mul_ne_zero (pow_ne_zero _ hx) hQ`.

Use `⟨hQ', ?_⟩` and prove the remaining obligations. Rewrite using `[eval_reflPoly κ (le_max_left _ _) hx, eval_reflPoly κ (le_max_right _ _) hx, mul_div_mul_left _ _ (pow_ne_zero _ hx)]`.
-/
theorem exists_poly_eval_inv (κ : ℂ) (P Q : ℂ[X]) :
    ∃ P' Q' : ℂ[X], ∀ x : ℂ, x ≠ 0 → Q.eval (κ / x) ≠ 0 →
      Q'.eval x ≠ 0 ∧ P'.eval x / Q'.eval x = P.eval (κ / x) / Q.eval (κ / x) := by
  set d := max P.natDegree Q.natDegree
  refine ⟨reflPoly κ d P, reflPoly κ d Q, fun x hx hQ => ?_⟩
  have hQ' : (reflPoly κ d Q).eval x ≠ 0 := by
    rw [eval_reflPoly κ (le_max_right _ _) hx]
    exact mul_ne_zero (pow_ne_zero _ hx) hQ
  refine ⟨hQ', ?_⟩
  rw [eval_reflPoly κ (le_max_left _ _) hx, eval_reflPoly κ (le_max_right _ _) hx,
    mul_div_mul_left _ _ (pow_ne_zero _ hx)]

/- English proof (translation)
Rewrite using `[sub_eq_add_neg, qs_add, div_eq_mul_inv]`. Use `congr 1`. Rewrite using `[qs, qs, neg_neg, Complex.cpow_neg, inv_inv]`.
-/
theorem qs_natCast_sub (s : ℂ) : qs F ((m : ℂ) - s) = qs F (m : ℂ) / qs F s := by
  rw [sub_eq_add_neg, qs_add, div_eq_mul_inv]
  congr 1
  rw [qs, qs, neg_neg, Complex.cpow_neg, inv_inv]

/- English proof (translation)
Establish `hq0 : (0 : ℝ) ≤ LocalField.residueCard F` using `Nat.cast_nonneg _`. Rewrite using `[norm_mul, norm_pow, norm_qs, ← Real.rpow_natCast, ← Real.rpow_mul hq0]`. Put the polynomial expressions in normal form.
-/
theorem norm_mul_qs_pow (α : ℂ) (s : ℂ) :
    ‖α * qs F s ^ m‖ = ‖α‖ * (LocalField.residueCard F : ℝ) ^ (-(m * s.re)) := by
  have hq0 : (0 : ℝ) ≤ LocalField.residueCard F := Nat.cast_nonneg _
  rw [norm_mul, norm_pow, norm_qs, ← Real.rpow_natCast, ← Real.rpow_mul hq0]
  ring_nf

/- English proof (translation)
Establish `hq : (1 : ℝ) < LocalField.residueCard F` using `by exact_mod_cast LocalField.one_lt_residueCard`. Establish `hm : (0 : ℝ) < m` using `by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne m)`. Rewrite using `[norm_mul_qs_pow, ← Real.rpow_logb (by linarith) hq.ne' (norm_pos_iff.2 hα0), ← Real.rpow_add (by linarith)]`. Use `Real.rpow_lt_one_of_one_lt_of_neg hq ?_` and prove the remaining obligations. Rewrite `hs` using `[div_lt_iff₀ hm]`.

Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem norm_mul_qs_pow_lt_one {α : ℂ} (hα0 : α ≠ 0) {s : ℂ}
    (hs : Real.logb (LocalField.residueCard F) ‖α‖ / m < s.re) :
    ‖α * qs F s ^ m‖ < 1 := by
  have hq : (1 : ℝ) < LocalField.residueCard F := by exact_mod_cast LocalField.one_lt_residueCard
  have hm : (0 : ℝ) < m := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne m)
  rw [norm_mul_qs_pow, ← Real.rpow_logb (by linarith) hq.ne' (norm_pos_iff.2 hα0),
    ← Real.rpow_add (by linarith)]
  refine Real.rpow_lt_one_of_one_lt_of_neg hq ?_
  rw [div_lt_iff₀ hm] at hs
  linarith

/- English proof (translation)
Establish `hq : (1 : ℝ) < LocalField.residueCard F` using `by exact_mod_cast LocalField.one_lt_residueCard`. Establish `hm : (0 : ℝ) < m` using `by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne m)`. Rewrite using `[norm_mul_qs_pow, ← Real.rpow_logb (by linarith) hq.ne' (norm_pos_iff.2 hα0), ← Real.rpow_add (by linarith), ← Real.rpow_natCast, ← Real.rpow_intCast, ← Real.rpow_mul (by linarith)]`. Use `Real.rpow_lt_rpow_of_exponent_lt hq ?_` and prove the remaining obligations. Establish `: s.re * m < Real.logb (LocalField.residueCard F) ‖α‖ + m * m`.

Use `(lt_div_iff₀ hm).1 (show s.re - m < Real.logb (LocalField.residueCard F) ‖α‖ / m by linarith)` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion. Use `push_cast`. Use the polynomial consequences of the given equalities and inequalities.
-/
theorem lt_norm_mul_qs_pow {α : ℂ} (hα0 : α ≠ 0) {s : ℂ}
    (hs : s.re < Real.logb (LocalField.residueCard F) ‖α‖ / m + m) :
    ((LocalField.residueCard F : ℝ) ^ m) ^ (-(m : ℤ)) < ‖α * qs F s ^ m‖ := by
  have hq : (1 : ℝ) < LocalField.residueCard F := by exact_mod_cast LocalField.one_lt_residueCard
  have hm : (0 : ℝ) < m := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne m)
  rw [norm_mul_qs_pow, ← Real.rpow_logb (by linarith) hq.ne' (norm_pos_iff.2 hα0),
    ← Real.rpow_add (by linarith), ← Real.rpow_natCast, ← Real.rpow_intCast,
    ← Real.rpow_mul (by linarith)]
  refine Real.rpow_lt_rpow_of_exponent_lt hq ?_
  have : s.re * m < Real.logb (LocalField.residueCard F) ‖α‖ + m * m := by
    have := (lt_div_iff₀ hm).1 (show s.re - m < Real.logb (LocalField.residueCard F) ‖α‖ / m by
      linarith)
    linarith
  push_cast
  nlinarith

/- English proof (translation)
Establish `hst : (stabilizerOf σ v : Set (GL (Fin m) F × H)) ∈ nhds (1, 1)` using `(hσ v).mem_nhds (one_mem _)`. Take `⟨u, hu, t, ht, hut⟩` from `mem_nhds_prod_iff.1 hst`. Take `⟨r₁, -, hr₁⟩` from `(hasBasis_nhds_one F m).mem_iff.1 hu`. Take `⟨K'', hK''c, hK''t⟩` from `exists_openSubgroup_isCompact_subset ht`. Use `⟨max r₀ r₁, le_max_left _ _, K''.toSubgroup ⊓ K₀', inf_le_right, ?_, ?_, ?_⟩` and prove the remaining obligations.

Conclude with `hK₀'c.of_isClosed_subset (K''.isClosed.inter (Subgroup.isClosed_of_isOpen _ hK₀'o)) Set.inter_subset_right`. Conclude with `K''.isOpen.inter hK₀'o`. Use `mem_fixedVectors.2 fun k hk => ?_` and prove the remaining obligations. Take `⟨hk1, hk2⟩` from `Subgroup.mem_prod.1 hk`. Establish `hk1' : k.1 ∈ u` using `hr₁ (congruenceSubgroup_antitone F m (le_max_right r₀ r₁) hk1)`.

Establish `hk2' : k.2 ∈ t` using `hK''t (Subgroup.mem_inf.1 hk2).1`. Conclude with `mem_stabilizerOf.1 (hut ⟨hk1', hk2'⟩)`.
-/
theorem exists_fixed_prod (hσ : IsSmooth σ) (v : W) (r₀ : ℕ) (K₀' : Subgroup H)
    (hK₀'c : IsCompact (K₀' : Set H)) (hK₀'o : IsOpen (K₀' : Set H)) :
    ∃ r ≥ r₀, ∃ K' : Subgroup H, K' ≤ K₀' ∧ IsCompact (K' : Set H) ∧ IsOpen (K' : Set H) ∧
      v ∈ fixedVectors σ ((congruenceSubgroup F m r).prod K') := by
  have hst : (stabilizerOf σ v : Set (GL (Fin m) F × H)) ∈ nhds (1, 1) :=
    (hσ v).mem_nhds (one_mem _)
  obtain ⟨u, hu, t, ht, hut⟩ := mem_nhds_prod_iff.1 hst
  obtain ⟨r₁, -, hr₁⟩ := (hasBasis_nhds_one F m).mem_iff.1 hu
  obtain ⟨K'', hK''c, hK''t⟩ := exists_openSubgroup_isCompact_subset ht
  refine ⟨max r₀ r₁, le_max_left _ _, K''.toSubgroup ⊓ K₀', inf_le_right, ?_, ?_, ?_⟩
  · exact hK₀'c.of_isClosed_subset (K''.isClosed.inter (Subgroup.isClosed_of_isOpen _ hK₀'o))
      Set.inter_subset_right
  · exact K''.isOpen.inter hK₀'o
  · refine mem_fixedVectors.2 fun k hk => ?_
    obtain ⟨hk1, hk2⟩ := Subgroup.mem_prod.1 hk
    have hk1' : k.1 ∈ u := hr₁ (congruenceSubgroup_antitone F m (le_max_right r₀ r₁) hk1)
    have hk2' : k.2 ∈ t := hK''t (Subgroup.mem_inf.1 hk2).1
    exact mem_stabilizerOf.1 (hut ⟨hk1', hk2'⟩)

/- English proof (translation)
Take `⟨K₀, hK₀c, -⟩` from `exists_openSubgroup_isCompact_subset (G := H) (U := Set.univ) Filter.univ_mem`. Take `⟨r, -, K', -, hc, ho, hv⟩` from `exists_fixed_prod hσ v 0 K₀.toSubgroup hK₀c K₀.isOpen`. Conclude with `⟨r, K', hc, ho, hv⟩`.
-/
theorem exists_fixed_prod₀ (hσ : IsSmooth σ) (v : W) :
    ∃ r : ℕ, ∃ K' : Subgroup H, IsCompact (K' : Set H) ∧ IsOpen (K' : Set H) ∧
      v ∈ fixedVectors σ ((congruenceSubgroup F m r).prod K') := by
  obtain ⟨K₀, hK₀c, -⟩ := exists_openSubgroup_isCompact_subset (G := H) (U := Set.univ)
    Filter.univ_mem
  obtain ⟨r, -, K', -, hc, ho, hv⟩ := exists_fixed_prod hσ v 0 K₀.toSubgroup hK₀c K₀.isOpen
  exact ⟨r, K', hc, ho, hv⟩

/- English proof (translation)
Establish `hdet : ∀ g ∈ congruenceSubgroup F m r, detPow g s = 1` using `fun g hg => detPow_of_mem_integralGL (congruenceSubgroup_le F m r hg) s`. Establish `hfix : ∀ g ∈ congruenceSubgroup F m r, σ (g, 1) v = v` using `fun g hg => mem_fixedVectors.1 hv _ (Subgroup.mem_prod.2 ⟨hg, K'.one_mem⟩)`. Simplify using `only [blockA, mul_assoc]`. Rewrite using `[integral_indGL_mul μ (isOpen_congruenceSubgroup F m r).measurableSet (x₀ := 1) (fun g hg => by rw [hdet g hg, hdet 1 (one_mem _), hfix g hg, hfix 1 (one_mem _)]), hdet 1 (one_mem _), one_mul, hfix 1 (one_mem _)]`.
-/
theorem blockA_indGL (μ : Measure (GL (Fin m) F)) {r : ℕ} {K' : Subgroup H} {v : W}
    (hv : v ∈ fixedVectors σ ((congruenceSubgroup F m r).prod K')) (ℓ : Module.Dual ℂ W) (s : ℂ) :
    blockA μ σ (indGL (congruenceSubgroup F m r : Set (GL (Fin m) F))) v ℓ s =
      μ.real (congruenceSubgroup F m r : Set (GL (Fin m) F)) * ℓ v := by
  have hdet : ∀ g ∈ congruenceSubgroup F m r, detPow g s = 1 := fun g hg =>
    detPow_of_mem_integralGL (congruenceSubgroup_le F m r hg) s
  have hfix : ∀ g ∈ congruenceSubgroup F m r, σ (g, 1) v = v := fun g hg =>
    mem_fixedVectors.1 hv _ (Subgroup.mem_prod.2 ⟨hg, K'.one_mem⟩)
  simp only [blockA, mul_assoc]
  rw [integral_indGL_mul μ (isOpen_congruenceSubgroup F m r).measurableSet (x₀ := 1)
    (fun g hg => by rw [hdet g hg, hdet 1 (one_mem _), hfix g hg, hfix 1 (one_mem _)]),
    hdet 1 (one_mem _), one_mul, hfix 1 (one_mem _)]

/- English proof (translation)
Take `⟨r, hr, K', hK'le, hK'c, hK'o, hv⟩` from `exists_fixed_prod hσ.1 v r₀ K₀' hK₀'c hK₀'o`. Take `⟨c, hc⟩` from `exists_blockB_eq_smul hσ hα0 hα hsupp μ hψ hψ1 hs hs' (isCompact_congruenceSubgroup F m r) (isOpen_congruenceSubgroup F m r) (congruenceSubgroup_le F m r) hK'c hK'o`. Establish `hv₀' : v₀ ∈ fixedVectors σ ((congruenceSubgroup F m r).prod K')`. Use `mem_fixedVectors.2 fun k hk => mem_fixedVectors.1 hv₀ k ?_` and prove the remaining obligations. Take `⟨h1, h2⟩` from `Subgroup.mem_prod.1 hk`.

Conclude with `Subgroup.mem_prod.2 ⟨congruenceSubgroup_antitone F m hr h1, hK'le h2⟩`. Establish `he₀` using `isSchwartzBruhat_indGL (isCompact_congruenceSubgroup F m r₀) (isOpen_congruenceSubgroup F m r₀)`. Establish `h1` using `hc Φ hΦ v hv ℓ hℓ`. Establish `h2` using `hc _ he₀ v₀ hv₀' ℓ₀ hℓ₀`. Establish `hμK : ((μ.real (congruenceSubgroup F m r : Set (GL (Fin m) F)) : ℝ) : ℂ) ≠ 0`.

Establish `: μ.real (congruenceSubgroup F m r : Set (GL (Fin m) F)) ≠ 0`. Rewrite using `[measureReal_ne_zero_iff ((isCompact_congruenceSubgroup F m r).measure_lt_top.ne)]`. Conclude with `((isOpen_congruenceSubgroup F m r).measure_pos μ ⟨1, one_mem _⟩).ne'`. Conclude with `this` after adjusting the coercions. Apply `mul_left_cancel₀ hμK` to reduce the goal to its premises.

Take the linear combination `(blockA μ σ (indGL (congruenceSubgroup F m r₀ : Set (GL (Fin m) F))) v₀ ℓ₀ s) * h1 - (blockA μ σ Φ v ℓ s) * h2`.
-/
theorem blockB_mul_blockA_eq (hσ : IsAdmissible σ) [σ.IsIrreducible] {α : ℂ} (hα0 : α ≠ 0)
    (hα : ∀ v, σ (centralUnif F m, 1) v = α • v)
    (hsupp : ∀ v : W, ∀ ℓ ∈ smoothVectors (Representation.dual σ),
      ∃ C : Set (GL (Fin m) F), IsCompact C ∧
        ∀ g, ℓ (σ (g, 1) v) ≠ 0 → ∃ j : ℤ, centralUnif F m ^ j * g ∈ C)
    (μ : Measure (GL (Fin m) F)) [μ.IsHaarMeasure] {ψ : AddChar F Circle} (hψ : Continuous ψ)
    (hψ1 : ψ ≠ 1) {s : ℂ} (hs : ‖α * qs F s ^ m‖ < 1)
    (hs' : ((LocalField.residueCard F : ℝ) ^ m) ^ (-(m : ℤ)) < ‖α * qs F s ^ m‖)
    {r₀ : ℕ} {K₀' : Subgroup H} (hK₀'c : IsCompact (K₀' : Set H)) (hK₀'o : IsOpen (K₀' : Set H))
    {v₀ : W} (hv₀ : v₀ ∈ fixedVectors σ ((congruenceSubgroup F m r₀).prod K₀'))
    {ℓ₀ : Module.Dual ℂ W} (hℓ₀ : ℓ₀ ∈ smoothVectors (Representation.dual σ))
    {Φ : Matrix (Fin m) (Fin m) F → ℂ} (hΦ : IsSchwartzBruhat Φ) (v : W) {ℓ : Module.Dual ℂ W}
    (hℓ : ℓ ∈ smoothVectors (Representation.dual σ)) :
    blockB μ σ (localMatrixFourier ψ Φ) v ℓ s *
        blockA μ σ (indGL (congruenceSubgroup F m r₀ : Set (GL (Fin m) F))) v₀ ℓ₀ s =
      blockB μ σ (localMatrixFourier ψ (indGL (congruenceSubgroup F m r₀ : Set (GL (Fin m) F))))
          v₀ ℓ₀ s * blockA μ σ Φ v ℓ s := by
  obtain ⟨r, hr, K', hK'le, hK'c, hK'o, hv⟩ := exists_fixed_prod hσ.1 v r₀ K₀' hK₀'c hK₀'o
  obtain ⟨c, hc⟩ := exists_blockB_eq_smul hσ hα0 hα hsupp μ hψ hψ1 hs hs'
    (isCompact_congruenceSubgroup F m r) (isOpen_congruenceSubgroup F m r)
    (congruenceSubgroup_le F m r) hK'c hK'o
  have hv₀' : v₀ ∈ fixedVectors σ ((congruenceSubgroup F m r).prod K') := by
    refine mem_fixedVectors.2 fun k hk => mem_fixedVectors.1 hv₀ k ?_
    obtain ⟨h1, h2⟩ := Subgroup.mem_prod.1 hk
    exact Subgroup.mem_prod.2 ⟨congruenceSubgroup_antitone F m hr h1, hK'le h2⟩
  have he₀ := isSchwartzBruhat_indGL (isCompact_congruenceSubgroup F m r₀)
    (isOpen_congruenceSubgroup F m r₀)
  have h1 := hc Φ hΦ v hv ℓ hℓ
  have h2 := hc _ he₀ v₀ hv₀' ℓ₀ hℓ₀
  have hμK : ((μ.real (congruenceSubgroup F m r : Set (GL (Fin m) F)) : ℝ) : ℂ) ≠ 0 := by
    have : μ.real (congruenceSubgroup F m r : Set (GL (Fin m) F)) ≠ 0 := by
      rw [measureReal_ne_zero_iff ((isCompact_congruenceSubgroup F m r).measure_lt_top.ne)]
      exact ((isOpen_congruenceSubgroup F m r).measure_pos μ ⟨1, one_mem _⟩).ne'
    exact_mod_cast this
  apply mul_left_cancel₀ hμK
  linear_combination (blockA μ σ (indGL (congruenceSubgroup F m r₀ : Set (GL (Fin m) F))) v₀ ℓ₀ s) *
    h1 - (blockA μ σ Φ v ℓ s) * h2

/- English proof (translation)
Take `⟨v₀, hv₀ne⟩` from `exists_ne_zero_of_isIrreducible (ρ := σ)`. Establish `hα0 : α ≠ 0`. Introduce `h0`. Apply `hv₀ne` to reduce the goal to its premises. Establish `h1` using `hα v₀`.

Rewrite `h1` using `[h0, zero_smul]`. Establish `h2` using `congrArg (σ ((centralUnif F m, (1 : H))⁻¹)) h1`. Rewrite `h2` using `[← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply, map_zero]`. Then use the resulting hypothesis. Take `⟨r₀, K₀', hK₀'c, hK₀'o, hv₀⟩` from `exists_fixed_prod₀ hσ.1 v₀`. Use `set 𝕂₀ := (congruenceSubgroup F m r₀).prod K₀'`.

Establish `h𝕂₀c : IsCompact (𝕂₀ : Set (GL (Fin m) F × H))`. Rewrite using `[Subgroup.coe_prod]`. Conclude with `(isCompact_congruenceSubgroup F m r₀).prod hK₀'c`. Establish `h𝕂₀o : IsOpen (𝕂₀ : Set (GL (Fin m) F × H))`. Rewrite using `[Subgroup.coe_prod]`.

Conclude with `(isOpen_congruenceSubgroup F m r₀).prod hK₀'o`. Choose the witnesses or unpack the hypotheses as in `⟨φ, hφ⟩ : ∃ φ : Module.Dual ℂ (fixedVectors σ 𝕂₀), φ ⟨v₀, hv₀⟩ ≠ 0 := by`. Assume the negation of the conclusion as `h`. Use `push Not at h`. Conclude with `hv₀ne (congrArg Subtype.val ((Module.forall_dual_apply_eq_zero_iff ℂ _).1 h))`.

Use `set ef := fixedContragredientEquiv hσ.1 h𝕂₀c h𝕂₀o with hef`. Use `set ℓ₀ : Module.Dual ℂ W := (((ef.symm φ : fixedVectors (contragredient σ) 𝕂₀) : smoothVectors (Representation.dual σ)) : Module.Dual ℂ W) with hℓ₀def`. Establish `hℓ₀ : ℓ₀ ∈ smoothVectors (Representation.dual σ)` using `((ef.symm φ : fixedVectors (contragredient σ) 𝕂₀) : smoothVectors (Representation.dual σ)).2`. Establish `hℓ₀v₀ : ℓ₀ v₀ ≠ 0`. Establish `h` using `congrArg (fun f : Module.Dual ℂ (fixedVectors σ 𝕂₀) => f ⟨v₀, hv₀⟩) (ef.apply_symm_apply φ)`.

Rewrite `h` using `[hef, fixedContragredientEquiv_apply, restrictFixed_apply]`. Rewrite using `[hℓ₀def, hef, h]`. Conclude with `hφ`. Use `set K₀ : Set (GL (Fin m) F) := (congruenceSubgroup F m r₀ : Set (GL (Fin m) F))`. Establish `he₀ : IsSchwartzBruhat (indGL K₀)` using `isSchwartzBruhat_indGL (isCompact_congruenceSubgroup F m r₀) (isOpen_congruenceSubgroup F m r₀)`.

Use `set A₀ : ℂ := (μ.real K₀ : ℂ) * ℓ₀ v₀ with hA₀def`. Establish `hA₀ : A₀ ≠ 0`. Use `mul_ne_zero ?_ hℓ₀v₀` and prove the remaining obligations. Establish `: μ.real K₀ ≠ 0`. Rewrite using `[measureReal_ne_zero_iff ((isCompact_congruenceSubgroup F m r₀).measure_lt_top.ne)]`.

Conclude with `((isOpen_congruenceSubgroup F m r₀).measure_pos μ ⟨1, one_mem _⟩).ne'`. Conclude with `this` after adjusting the coercions. Establish `hA₀s : ∀ s, blockA μ σ (indGL K₀) v₀ ℓ₀ s = A₀` using `fun s => blockA_indGL μ hv₀ ℓ₀ s`. Use `set a : ℝ := Real.logb (LocalField.residueCard F) ‖α‖ / m with ha`. Establish `hm : (0 : ℝ) < m` using `by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne m)`.

Establish `hdual : ∀ {v : W} {ℓ : Module.Dual ℂ W}, ℓ ∈ smoothVectors (Representation.dual σ) → ∀ {Φ : Matrix (Fin m) (Fin m) F → ℂ}, IsSchwartzBruhat Φ → ∃ P' Q' : ℂ[X], ∀ s : ℂ, ((LocalField.residueCard F : ℝ) ^ m) ^ (-(m : ℤ)) < ‖α * qs F s ^ m‖ → Q'.eval (qs F s) ≠ 0 ∧ blockB μ σ (local …`. Introduce `v ℓ hℓ Φ hΦ`. Take `⟨P, N, hP⟩` from `(isCentralCoeff_coeff hσ.1 hα0 hα hsupp v hℓ).inv.exists_eq_div_zeta μ (hΦ.localMatrixFourier hψ hψ1)`. Take `⟨P', Q', hPQ⟩` from `exists_poly_eval_inv (qs F (m : ℂ)) P (X ^ N * (1 - C α⁻¹ * X ^ m))`. Use `⟨P', Q', fun s hs' => ?_⟩` and prove the remaining obligations.

Establish `hlt` using `norm_inv_mul_qs_sub_lt_one hα0 hs'`. Establish `hy : qs F ((m : ℂ) - s) = qs F (m : ℂ) / qs F s` using `qs_natCast_sub s`. Establish `hQ : (X ^ N * (1 - C α⁻¹ * X ^ m) : ℂ[X]).eval (qs F (m : ℂ) / qs F s) ≠ 0`. Rewrite using `[← hy]`. Simplify using `only [eval_mul, eval_pow, eval_X, eval_sub, eval_one, eval_C]`.

Use `mul_ne_zero (pow_ne_zero _ (qs_ne_zero _)) fun h => ?_` and prove the remaining obligations. Establish `: α⁻¹ * qs F ((m : ℂ) - s) ^ m = 1` using `by linear_combination -h`. Rewrite `hlt` using `[this, norm_one]`. Conclude with `lt_irrefl _ hlt`. Take `⟨hQ', heq⟩` from `hPQ (qs F s) (qs_ne_zero s) hQ`.

Use `⟨hQ', ?_⟩` and prove the remaining obligations. Rewrite using `[heq, ← hy]`. Use `hP ((m : ℂ) - s) hlt` as an intermediate fact. Simplify using `only [eval_mul, eval_pow, eval_X, eval_sub, eval_one, eval_C]`. Conclude with `this`.

Take `⟨Pr, Qr, hPQr⟩` from `hdual hℓ₀ he₀`. Use `set γ : RatFunc ℂ := algebraMap ℂ[X] (RatFunc ℂ) (C A₀⁻¹ * Pr) / algebraMap ℂ[X] (RatFunc ℂ) Qr`. Use `⟨γ, max a (-(a + m)), fun Φ hΦ v ℓ hℓ => ⟨fun s hs => ?_, fun s hs => ?_, ?_⟩⟩` and prove the remaining obligations. Conclude with `integrable_blockA hσ.1 hα0 hα hsupp μ hΦ v hℓ (norm_mul_qs_pow_lt_one hα0 (lt_of_le_of_lt (le_max_left _ _) hs))`. Conclude with `integrable_blockB hσ.1 hα0 hα hsupp μ (hΦ.localMatrixFourier hψ hψ1) v hℓ (lt_norm_mul_qs_pow hα0 (by have := le_max_right a (-(a + m)); linarith))`.

Take `⟨PA, NA, hPA⟩` from `(isCentralCoeff_coeff hσ.1 hα0 hα hsupp v hℓ).exists_eq_div_zeta μ hΦ`. Use `set QA : ℂ[X] := X ^ NA * (1 - C α * X ^ m)`. Use `set RA : RatFunc ℂ := algebraMap ℂ[X] (RatFunc ℂ) PA / algebraMap ℂ[X] (RatFunc ℂ) QA`. Establish `hAeval : ∀ s : ℂ, ‖α * qs F s ^ m‖ < 1 → QA.eval (qs F s) ≠ 0 ∧ blockA μ σ Φ v ℓ s = RA.eval (RingHom.id ℂ) (qs F s)`. Introduce `s hs`.

Establish `hQ : QA.eval (qs F s) ≠ 0`. Simplify using `only [QA, eval_mul, eval_pow, eval_X, eval_sub, eval_one, eval_C]`. Use `mul_ne_zero (pow_ne_zero _ (qs_ne_zero _)) fun h => ?_` and prove the remaining obligations. Establish `: α * qs F s ^ m = 1` using `by linear_combination -h`. Rewrite `hs` using `[this, norm_one]`.

Conclude with `lt_irrefl _ hs`. Use `⟨hQ, ?_⟩` and prove the remaining obligations. Rewrite using `[eval_div_algebraMap _ _ hQ, blockA, hPA s hs]`. Simplify using `only [QA, eval_mul, eval_pow, eval_X, eval_sub, eval_one, eval_C]`. Take `⟨PB, QB, hPQB⟩` from `hdual hℓ hΦ`.

Use `set RB : RatFunc ℂ := algebraMap ℂ[X] (RatFunc ℂ) PB / algebraMap ℂ[X] (RatFunc ℂ) QB`. Establish `hBeval : ∀ s : ℂ, ((LocalField.residueCard F : ℝ) ^ m) ^ (-(m : ℤ)) < ‖α * qs F s ^ m‖ → blockB μ σ (localMatrixFourier ψ Φ) v ℓ s = RB.eval (RingHom.id ℂ) (qs F s)`. Introduce `s hs'`. Take `⟨hQ, heq⟩` from `hPQB s hs'`. Rewrite using `[heq, eval_div_algebraMap _ _ hQ]`.

Establish `hid : RB = γ * RA` using `by set t : ℕ → ℝ := fun k => a + m / (k + 2)`. Establish `ht : ∀ k, a < t k ∧ t k < a + m` using `fun k => by`. Establish `hk : (0 : ℝ) < (k : ℝ) + 2` using `by positivity`. Use `⟨by simp only [t]; have := div_pos hm hk; linarith, ?_⟩` and prove the remaining obligations. Simplify using `only [t]`.

Establish `: m / ((k : ℝ) + 2) < m`. Rewrite using `[div_lt_iff₀ hk]`. Use the polynomial consequences of the given equalities and inequalities. Combine the linear equalities and inequalities to obtain the conclusion. Use `eq_of_eval_eq_of_infinite (S := Set.range fun k : ℕ => qs F ((t k : ℝ) : ℂ)) ?_ ?_` and prove the remaining obligations.

Use `Set.infinite_range_of_injective fun k l hkl => ?_` and prove the remaining obligations. Establish `hn` using `congrArg norm hkl`. Simplify using `only [norm_qs, Complex.ofReal_re] at hn`. Establish `hq : (1 : ℝ) < LocalField.residueCard F`. Conclude with `LocalField.one_lt_residueCard` after adjusting the coercions.

Establish `htt : t k = t l`. Establish `hl` using `congrArg (Real.logb (LocalField.residueCard F)) hn`. Rewrite `hl` using `[Real.logb_rpow (by linarith) hq.ne', Real.logb_rpow (by linarith) hq.ne']`. Combine the linear equalities and inequalities to obtain the conclusion. Simplify using `only [t, add_right_inj] at htt`.

Establish `hk : (0 : ℝ) < (k : ℝ) + 2` using `by positivity`. Establish `hl : (0 : ℝ) < (l : ℝ) + 2` using `by positivity`. Rewrite `htt` using `[div_eq_div_iff hk.ne' hl.ne']`. Establish `: (k : ℝ) = l` using `by nlinarith`. Conclude with `this` after adjusting the coercions.

Introduce and unpack `x ⟨k, rfl⟩ set s : ℂ := ((t k : ℝ) : ℂ)`. Establish `hsre : s.re = t k` using `Complex.ofReal_re _`. Establish `hs : ‖α * qs F s ^ m‖ < 1` using `norm_mul_qs_pow_lt_one hα0 (by rw [hsre]; exact (ht k).1)`. Establish `hs'` using `lt_norm_mul_qs_pow hα0 (s := s) (by rw [hsre]; exact (ht k).2)`. Take `⟨hQA, hA⟩` from `hAeval s hs`.

Take `⟨hQr, hr⟩` from `hPQr s hs'`. Establish `hcross` using `blockB_mul_blockA_eq hσ hα0 hα hsupp μ hψ hψ1 hs hs' hK₀'c hK₀'o hv₀ hℓ₀ hΦ v hℓ`. Rewrite `hcross` using `[hA₀s]`. Rewrite using `[← hBeval s hs', RatFunc.eval_mul (hx := denom_eval_ne_zero_of_div hQr) (hy := denom_eval_ne_zero_of_div hQA), eval_div_algebraMap _ _ hQr, ← hA]`. Simplify using `only [eval_mul, eval_C]`.

Rewrite using `[mul_div_assoc, ← hr]`. Clear the denominators using the available nonvanishing facts. Take the linear combination `hcross`. Use `⟨RA, max a (-(a + m)), fun s hs => ?_, fun s hs => ?_⟩` and prove the remaining obligations. Conclude with `(hAeval s (norm_mul_qs_pow_lt_one hα0 (lt_of_le_of_lt (le_max_left _ _) hs))).2`.

Rewrite using `[← hid]`. Conclude with `hBeval s (lt_norm_mul_qs_pow hα0 (by have := le_max_right a (-(a + m)); linarith))`.
-/
theorem exists_blockFE (μ : Measure (GL (Fin m) F)) [μ.IsHaarMeasure] (hσ : IsAdmissible σ)
    [σ.IsIrreducible] {ψ : AddChar F Circle} (hψ : Continuous ψ) (hψ1 : ψ ≠ 1) {α : ℂ}
    (hα : ∀ v, σ (centralUnif F m, 1) v = α • v)
    (hsupp : ∀ v : W, ∀ ℓ ∈ smoothVectors (Representation.dual σ),
      ∃ C : Set (GL (Fin m) F), IsCompact C ∧
        ∀ g, ℓ (σ (g, 1) v) ≠ 0 → ∃ j : ℤ, centralUnif F m ^ j * g ∈ C) :
    ∃ γ : RatFunc ℂ, ∃ s₁ : ℝ, ∀ Φ : Matrix (Fin m) (Fin m) F → ℂ, IsSchwartzBruhat Φ → ∀ v : W,
      ∀ ℓ ∈ smoothVectors (Representation.dual σ),
        (∀ s : ℂ, s₁ < s.re → Integrable (fun g : GL (Fin m) F =>
          Φ (g : Matrix (Fin m) (Fin m) F) * detPow g s * ℓ (σ (g, 1) v)) μ) ∧
        (∀ s : ℂ, s.re < -s₁ → Integrable (fun g : GL (Fin m) F =>
          GJMatrix.localMatrixFourier ψ Φ (g : Matrix (Fin m) (Fin m) F) * detPow g (m - s) *
            ℓ (σ (g⁻¹, 1) v)) μ) ∧
        RatFE F γ (blockA μ σ Φ v ℓ) (blockB μ σ (GJMatrix.localMatrixFourier ψ Φ) v ℓ) := by
  classical

  obtain ⟨v₀, hv₀ne⟩ := exists_ne_zero_of_isIrreducible (ρ := σ)
  have hα0 : α ≠ 0 := by
    intro h0
    apply hv₀ne
    have h1 := hα v₀
    rw [h0, zero_smul] at h1
    have h2 := congrArg (σ ((centralUnif F m, (1 : H))⁻¹)) h1
    rwa [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply,
      map_zero] at h2

  obtain ⟨r₀, K₀', hK₀'c, hK₀'o, hv₀⟩ := exists_fixed_prod₀ hσ.1 v₀
  set 𝕂₀ := (congruenceSubgroup F m r₀).prod K₀'
  have h𝕂₀c : IsCompact (𝕂₀ : Set (GL (Fin m) F × H)) := by
    rw [Subgroup.coe_prod]; exact (isCompact_congruenceSubgroup F m r₀).prod hK₀'c
  have h𝕂₀o : IsOpen (𝕂₀ : Set (GL (Fin m) F × H)) := by
    rw [Subgroup.coe_prod]; exact (isOpen_congruenceSubgroup F m r₀).prod hK₀'o
  obtain ⟨φ, hφ⟩ : ∃ φ : Module.Dual ℂ (fixedVectors σ 𝕂₀), φ ⟨v₀, hv₀⟩ ≠ 0 := by
    by_contra h
    push Not at h
    exact hv₀ne (congrArg Subtype.val ((Module.forall_dual_apply_eq_zero_iff ℂ _).1 h))
  set ef := fixedContragredientEquiv hσ.1 h𝕂₀c h𝕂₀o with hef
  set ℓ₀ : Module.Dual ℂ W := (((ef.symm φ : fixedVectors (contragredient σ) 𝕂₀) :
    smoothVectors (Representation.dual σ)) : Module.Dual ℂ W) with hℓ₀def
  have hℓ₀ : ℓ₀ ∈ smoothVectors (Representation.dual σ) :=
    ((ef.symm φ : fixedVectors (contragredient σ) 𝕂₀) : smoothVectors (Representation.dual σ)).2
  have hℓ₀v₀ : ℓ₀ v₀ ≠ 0 := by
    have h := congrArg (fun f : Module.Dual ℂ (fixedVectors σ 𝕂₀) => f ⟨v₀, hv₀⟩)
      (ef.apply_symm_apply φ)
    rw [hef, fixedContragredientEquiv_apply, restrictFixed_apply] at h
    rw [hℓ₀def, hef, h]
    exact hφ
  set K₀ : Set (GL (Fin m) F) := (congruenceSubgroup F m r₀ : Set (GL (Fin m) F))
  have he₀ : IsSchwartzBruhat (indGL K₀) := isSchwartzBruhat_indGL
    (isCompact_congruenceSubgroup F m r₀) (isOpen_congruenceSubgroup F m r₀)
  set A₀ : ℂ := (μ.real K₀ : ℂ) * ℓ₀ v₀ with hA₀def
  have hA₀ : A₀ ≠ 0 := by
    refine mul_ne_zero ?_ hℓ₀v₀
    have : μ.real K₀ ≠ 0 := by
      rw [measureReal_ne_zero_iff ((isCompact_congruenceSubgroup F m r₀).measure_lt_top.ne)]
      exact ((isOpen_congruenceSubgroup F m r₀).measure_pos μ ⟨1, one_mem _⟩).ne'
    exact_mod_cast this
  have hA₀s : ∀ s, blockA μ σ (indGL K₀) v₀ ℓ₀ s = A₀ := fun s => blockA_indGL μ hv₀ ℓ₀ s

  set a : ℝ := Real.logb (LocalField.residueCard F) ‖α‖ / m with ha
  have hm : (0 : ℝ) < m := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne m)

  have hdual : ∀ {v : W} {ℓ : Module.Dual ℂ W}, ℓ ∈ smoothVectors (Representation.dual σ) →
      ∀ {Φ : Matrix (Fin m) (Fin m) F → ℂ}, IsSchwartzBruhat Φ →
      ∃ P' Q' : ℂ[X], ∀ s : ℂ,
        ((LocalField.residueCard F : ℝ) ^ m) ^ (-(m : ℤ)) < ‖α * qs F s ^ m‖ →
          Q'.eval (qs F s) ≠ 0 ∧
            blockB μ σ (localMatrixFourier ψ Φ) v ℓ s = P'.eval (qs F s) / Q'.eval (qs F s) := by
    intro v ℓ hℓ Φ hΦ
    obtain ⟨P, N, hP⟩ := (isCentralCoeff_coeff hσ.1 hα0 hα hsupp v hℓ).inv.exists_eq_div_zeta μ
      (hΦ.localMatrixFourier hψ hψ1)
    obtain ⟨P', Q', hPQ⟩ := exists_poly_eval_inv (qs F (m : ℂ)) P (X ^ N * (1 - C α⁻¹ * X ^ m))
    refine ⟨P', Q', fun s hs' => ?_⟩
    have hlt := norm_inv_mul_qs_sub_lt_one hα0 hs'
    have hy : qs F ((m : ℂ) - s) = qs F (m : ℂ) / qs F s := qs_natCast_sub s
    have hQ : (X ^ N * (1 - C α⁻¹ * X ^ m) : ℂ[X]).eval (qs F (m : ℂ) / qs F s) ≠ 0 := by
      rw [← hy]
      simp only [eval_mul, eval_pow, eval_X, eval_sub, eval_one, eval_C]
      refine mul_ne_zero (pow_ne_zero _ (qs_ne_zero _)) fun h => ?_
      have : α⁻¹ * qs F ((m : ℂ) - s) ^ m = 1 := by linear_combination -h
      rw [this, norm_one] at hlt
      exact lt_irrefl _ hlt
    obtain ⟨hQ', heq⟩ := hPQ (qs F s) (qs_ne_zero s) hQ
    refine ⟨hQ', ?_⟩
    rw [heq, ← hy]
    have := hP ((m : ℂ) - s) hlt
    simp only [eval_mul, eval_pow, eval_X, eval_sub, eval_one, eval_C]
    exact this
  obtain ⟨Pr, Qr, hPQr⟩ := hdual hℓ₀ he₀
  set γ : RatFunc ℂ := algebraMap ℂ[X] (RatFunc ℂ) (C A₀⁻¹ * Pr) / algebraMap ℂ[X] (RatFunc ℂ) Qr
  refine ⟨γ, max a (-(a + m)), fun Φ hΦ v ℓ hℓ => ⟨fun s hs => ?_, fun s hs => ?_, ?_⟩⟩
  · exact integrable_blockA hσ.1 hα0 hα hsupp μ hΦ v hℓ
      (norm_mul_qs_pow_lt_one hα0 (lt_of_le_of_lt (le_max_left _ _) hs))
  · exact integrable_blockB hσ.1 hα0 hα hsupp μ (hΦ.localMatrixFourier hψ hψ1) v hℓ
      (lt_norm_mul_qs_pow hα0 (by have := le_max_right a (-(a + m)); linarith))
  ·
    obtain ⟨PA, NA, hPA⟩ := (isCentralCoeff_coeff hσ.1 hα0 hα hsupp v hℓ).exists_eq_div_zeta μ hΦ
    set QA : ℂ[X] := X ^ NA * (1 - C α * X ^ m)
    set RA : RatFunc ℂ := algebraMap ℂ[X] (RatFunc ℂ) PA / algebraMap ℂ[X] (RatFunc ℂ) QA
    have hAeval : ∀ s : ℂ, ‖α * qs F s ^ m‖ < 1 →
        QA.eval (qs F s) ≠ 0 ∧ blockA μ σ Φ v ℓ s = RA.eval (RingHom.id ℂ) (qs F s) := by
      intro s hs
      have hQ : QA.eval (qs F s) ≠ 0 := by
        simp only [QA, eval_mul, eval_pow, eval_X, eval_sub, eval_one, eval_C]
        refine mul_ne_zero (pow_ne_zero _ (qs_ne_zero _)) fun h => ?_
        have : α * qs F s ^ m = 1 := by linear_combination -h
        rw [this, norm_one] at hs
        exact lt_irrefl _ hs
      refine ⟨hQ, ?_⟩
      rw [eval_div_algebraMap _ _ hQ, blockA, hPA s hs]
      simp only [QA, eval_mul, eval_pow, eval_X, eval_sub, eval_one, eval_C]
    obtain ⟨PB, QB, hPQB⟩ := hdual hℓ hΦ
    set RB : RatFunc ℂ := algebraMap ℂ[X] (RatFunc ℂ) PB / algebraMap ℂ[X] (RatFunc ℂ) QB
    have hBeval : ∀ s : ℂ, ((LocalField.residueCard F : ℝ) ^ m) ^ (-(m : ℤ)) < ‖α * qs F s ^ m‖ →
        blockB μ σ (localMatrixFourier ψ Φ) v ℓ s = RB.eval (RingHom.id ℂ) (qs F s) := by
      intro s hs'
      obtain ⟨hQ, heq⟩ := hPQB s hs'
      rw [heq, eval_div_algebraMap _ _ hQ]

    have hid : RB = γ * RA := by
      set t : ℕ → ℝ := fun k => a + m / (k + 2)
      have ht : ∀ k, a < t k ∧ t k < a + m := fun k => by
        have hk : (0 : ℝ) < (k : ℝ) + 2 := by positivity
        refine ⟨by simp only [t]; have := div_pos hm hk; linarith, ?_⟩
        simp only [t]
        have : m / ((k : ℝ) + 2) < m := by
          rw [div_lt_iff₀ hk]; nlinarith
        linarith
      refine eq_of_eval_eq_of_infinite (S := Set.range fun k : ℕ => qs F ((t k : ℝ) : ℂ)) ?_ ?_
      · refine Set.infinite_range_of_injective fun k l hkl => ?_
        have hn := congrArg norm hkl
        simp only [norm_qs, Complex.ofReal_re] at hn
        have hq : (1 : ℝ) < LocalField.residueCard F := by
          exact_mod_cast LocalField.one_lt_residueCard
        have htt : t k = t l := by
          have hl := congrArg (Real.logb (LocalField.residueCard F)) hn
          rw [Real.logb_rpow (by linarith) hq.ne', Real.logb_rpow (by linarith) hq.ne'] at hl
          linarith
        simp only [t, add_right_inj] at htt
        have hk : (0 : ℝ) < (k : ℝ) + 2 := by positivity
        have hl : (0 : ℝ) < (l : ℝ) + 2 := by positivity
        rw [div_eq_div_iff hk.ne' hl.ne'] at htt
        have : (k : ℝ) = l := by nlinarith
        exact_mod_cast this
      · rintro x ⟨k, rfl⟩
        set s : ℂ := ((t k : ℝ) : ℂ)
        have hsre : s.re = t k := Complex.ofReal_re _
        have hs : ‖α * qs F s ^ m‖ < 1 := norm_mul_qs_pow_lt_one hα0 (by rw [hsre]; exact (ht k).1)
        have hs' := lt_norm_mul_qs_pow hα0 (s := s) (by rw [hsre]; exact (ht k).2)
        obtain ⟨hQA, hA⟩ := hAeval s hs
        obtain ⟨hQr, hr⟩ := hPQr s hs'
        have hcross := blockB_mul_blockA_eq hσ hα0 hα hsupp μ hψ hψ1 hs hs' hK₀'c hK₀'o hv₀ hℓ₀ hΦ v
          hℓ
        rw [hA₀s] at hcross
        rw [← hBeval s hs', RatFunc.eval_mul (hx := denom_eval_ne_zero_of_div hQr)
          (hy := denom_eval_ne_zero_of_div hQA), eval_div_algebraMap _ _ hQr, ← hA]
        simp only [eval_mul, eval_C]
        rw [mul_div_assoc, ← hr]
        field_simp
        linear_combination hcross
    refine ⟨RA, max a (-(a + m)), fun s hs => ?_, fun s hs => ?_⟩
    · exact (hAeval s (norm_mul_qs_pow_lt_one hα0 (lt_of_le_of_lt (le_max_left _ _) hs))).2
    · rw [← hid]
      exact hBeval s (lt_norm_mul_qs_pow hα0 (by have := le_max_right a (-(a + m)); linarith))

end GodementJacquet

end GroundTheory.Automorphic

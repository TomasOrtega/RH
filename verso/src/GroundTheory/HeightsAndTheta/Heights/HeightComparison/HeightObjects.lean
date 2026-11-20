import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HeightsOfSets.FiniteSupportHeight
import GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.Objects
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ArithmeticHilbertSamuelLowerBound
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.RationalSections.IsRatSectionOn
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G
open scoped ContDiff

noncomputable section

variable {ι : Type} {n : ι → ℕ}

abbrev blockIdx (n : ι → ℕ) : ι → Type := fun k ↦ Fin (n k + 1)

def flatCone {F : Type*} (z : Cone n F) : Coord n → F := fun p ↦ z p.1 p.2

def unflatCone {F : Type*} (w : Coord n → F) : Cone n F := fun k i ↦ w ⟨k, i⟩

/- English proof (translation)
Both sides reduce to the same expression.
-/
@[simp] theorem unflatCone_flatCone {F : Type*} (z : Cone n F) : unflatCone (flatCone z) = z := rfl

/- English proof (translation)
Both sides reduce to the same expression.
-/
@[simp] theorem flatCone_unflatCone {F : Type*} (w : Coord n → F) : flatCone (unflatCone w) = w := rfl

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem blockNonzero_unflatCone_iff {F : Type*} [Zero F] (w : Coord n → F) :
    BlockNonzero (unflatCone w) ↔ ∀ k, ∃ i, w ⟨k, i⟩ ≠ 0 :=
  forall_congr' fun _ ↦ Function.ne_iff

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression.
-/
theorem eval_map_flatCone {F : Type*} [CommRing F] (z : Cone n F) (f : MvPolynomial (Coord n) ℤ) :
    eval (flatCone z) (map (Int.castRingHom F) f) = evalCone z f := by
  rw [eval_map]
  rfl

variable [Fintype ι] [DecidableEq ι]

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities.
-/
theorem ArithVariety.mem_mcPts_iff (P : ArithVariety n) (w : Coord n → ℂ) :
    w ∈ Geo.mcPts P.ideal ↔ unflatCone w ∈ P.points ℂ := by
  rw [ArithVariety.points, Set.mem_setOf_eq, blockNonzero_unflatCone_iff, Geo.mcPts,
    Set.mem_setOf_eq]
  refine and_congr Iff.rfl (forall₂_congr fun f _ ↦ ?_)
  rw [← eval_map_flatCone, flatCone_unflatCone]

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Fix the arbitrary inputs or assume the hypotheses. Reduce the conclusion to the remaining proof obligations. Simplify using the standard rewrite rules.

Simplify using the standard rewrite rules.
-/
theorem weight_coordDeg_apply (d : Coord n →₀ ℕ) (k : ι) :
    Finsupp.weight (coordDeg n) d k = ∑ i, d ⟨k, i⟩ := by
  classical
  rw [Finsupp.weight_apply, Finsupp.sum_fintype _ _ (by intros; exact zero_smul _ _), Finset.sum_apply,
    Fintype.sum_sigma, Finset.sum_eq_single k]
  · simp [coordDeg]
  · intro j _ hj
    refine Finset.sum_eq_zero fun i _ ↦ ?_
    simp [coordDeg, Pi.single_apply, Ne.symm hj]
  · simp

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Fix the arbitrary inputs or assume the hypotheses. Apply function extensionality and compare values at an arbitrary argument. Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses.

Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem geoMultiHomog_iff (f : MvPolynomial (Coord n) ℤ) (a : ι → ℕ) :
    Geo.IsMultiHomog (ι := blockIdx n) f a ↔ IsWeightedHomogeneous (coordDeg n) f a := by
  constructor
  · intro h d hd
    funext k
    rw [weight_coordDeg_apply]
    exact h d (mem_support_iff.mpr hd) k
  · intro h m hm k
    rw [← weight_coordDeg_apply, h (mem_support_iff.mp hm)]

/- English proof (translation)
Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. A detailed English derivation is pending.
-/
theorem ArithVariety.isMultiProjPrime (P : ArithVariety n) :
    Geo.IsMultiProjPrime (ι := blockIdx n) P.ideal := by
  classical
  refine ⟨P.isPrime, ⟨{f | f ∈ P.ideal ∧ ∃ a, Geo.IsMultiHomog (ι := blockIdx n) f a},
    fun f hf ↦ hf.2, le_antisymm (fun f hf ↦ ?_) (Ideal.span_le.mpr fun f hf ↦ hf.1)⟩, P.relevant⟩
  rw [← sum_weightedHomogeneousComponent (w := coordDeg n) f,
    finsum_eq_sum _ (weightedHomogeneousComponent_finsupp f)]
  refine Ideal.sum_mem _ fun m _ ↦ Ideal.subset_span ⟨P.homogeneous f hf m, m, ?_⟩
  exact (geoMultiHomog_iff _ m).mpr (weightedHomogeneousComponent_isWeightedHomogeneous m f)

/- English proof (translation)
By extensionality, compare the relevant components. Rewrite the conclusion using the stated equalities. Supply the required witnesses or components.
-/
theorem ArithVariety.isHorizontal (P : ArithVariety n) :
    Geo.IsHorizontal (ι := blockIdx n) P.ideal := by
  ext a
  rw [Ideal.mem_comap, Ideal.mem_bot]
  exact ⟨P.horizontal a, fun h ↦ by rw [h, map_zero]; exact P.ideal.zero_mem⟩

namespace HermLine

open Classical in

def toGeo (A : HermLine n) : Geo.HermLine (blockIdx n) where
  a := A.deg
  h w := if BlockNonzero (unflatCone w) then A.metric (unflatCone w) else 0
  pos w hw := by
    have hw' : BlockNonzero (unflatCone w) := (blockNonzero_unflatCone_iff w).mpr hw
    rw [if_pos hw']
    exact A.metric_pos _ hw'
  smul c w hc := by
    have e : unflatCone (fun p : Coord n ↦ c p.1 * w p) = fun k i ↦ c k * unflatCone w k i := rfl
    by_cases hw : BlockNonzero (unflatCone w)
    · have hcw : BlockNonzero (unflatCone (fun p : Coord n ↦ c p.1 * w p)) := by
        intro k hk
        apply hw k
        funext i
        have := congrFun hk i
        rw [e] at this
        exact (mul_eq_zero.mp this).resolve_left (hc k)
      rw [if_pos hw, if_pos hcw, e, A.metric_smul c _ hc hw]
    · have hcw : ¬ BlockNonzero (unflatCone (fun p : Coord n ↦ c p.1 * w p)) := by
        intro h
        apply hw
        intro k hk
        apply h k
        funext i
        rw [e]
        simp [congrFun hk i]
      rw [if_neg hw, if_neg hcw, mul_zero]

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem toGeo_a (A : HermLine n) : A.toGeo.a = A.deg := rfl

/- English proof (translation)
Simplify using the standard rewrite rules.
-/
theorem toGeo_h_of_blockNonzero (A : HermLine n) {w : Coord n → ℂ}
    (hw : BlockNonzero (unflatCone w)) : A.toGeo.h w = A.metric (unflatCone w) := by
  simp only [toGeo, if_pos hw]

/- English proof (translation)
Establish an intermediate fact. Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. A detailed English derivation is pending.
-/
theorem isSmoothHerm_toGeo (A : HermLine n) : Geo.IsSmoothHerm A.toGeo := by
  have hu : ContDiff ℝ ∞ (fun w : Coord n → ℂ ↦ unflatCone w) :=
    contDiff_pi.2 fun k ↦ contDiff_pi.2 fun i ↦ contDiff_apply ℝ ℂ (⟨k, i⟩ : Coord n)
  have hm : ContDiffOn ℝ ∞ (fun w : Coord n → ℂ ↦ A.metric (unflatCone w))
      {w | ∀ k, ∃ i, w ⟨k, i⟩ ≠ 0} :=
    A.metric_smooth.comp hu.contDiffOn fun w hw ↦ (blockNonzero_unflatCone_iff w).mpr hw
  refine hm.congr fun w hw ↦ ?_
  exact A.toGeo_h_of_blockNonzero ((blockNonzero_unflatCone_iff w).mpr hw)

/- English proof (translation)
Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Simplify using the standard rewrite rules. Substitute using the available equality. Both sides reduce to the same expression.
-/
theorem geo_ext {K : Type*} [Fintype K] {κ : K → Type*} [∀ k, Fintype (κ k)]
    {A B : Geo.HermLine κ} (ha : A.a = B.a) (hh : A.h = B.h) : A = B := by
  obtain ⟨a, h, _, _⟩ := A
  obtain ⟨b, h', _, _⟩ := B
  simp only at ha hh
  subst ha hh
  rfl

/- English proof (translation)
Reduce the conclusion to the remaining proof obligations. Apply function extensionality and compare values at an arbitrary argument. Simplify using the standard rewrite rules. Apply the first step, then apply the next step to every resulting obligation.
-/
theorem toGeo_mul (A B : HermLine n) : (A.mul B).toGeo = A.toGeo.tensor B.toGeo := by
  refine geo_ext rfl ?_
  funext w
  simp only [toGeo, mul, Geo.HermLine.tensor]
  split_ifs <;> simp

end HermLine

namespace IntegralSection

variable {P : ArithVariety n} {a : ι → ℤ}

end IntegralSection

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.

Reduce the equality to equality of the corresponding arguments. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.

Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Rewrite the conclusion repeatedly using the stated equalities. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities.

Reduce the conclusion to the remaining proof obligations. A detailed English derivation is pending.
-/
theorem aeval_div_chart_mem {Ω : Type*} [Field Ω] (y : Coord n → Ω) (c : (k : ι) → Fin (n k + 1))
    (hc : ∀ k, y ⟨k, c k⟩ ≠ 0) (e : MvPolynomial (Coord n) ℤ) (δ : ι → ℕ)
    (he : IsWeightedHomogeneous (coordDeg n) e δ) :
    aeval y e * ∏ k, (y ⟨k, c k⟩ ^ δ k)⁻¹ ∈ Geo.chartRingZ (ι := blockIdx n) y c := by
  classical
  rw [aeval_def, eval₂_eq, Finset.sum_mul]
  refine Subalgebra.sum_mem _ fun m hm ↦ ?_
  have hmδ : ∀ k, ∑ i, m ⟨k, i⟩ = δ k := (geoMultiHomog_iff e δ).mpr he m hm
  have key : (algebraMap ℤ Ω (coeff m e) * ∏ p ∈ m.support, y p ^ m p) * ∏ k, (y ⟨k, c k⟩ ^ δ k)⁻¹ =
      algebraMap ℤ Ω (coeff m e) * ∏ p, (y p / y ⟨p.1, c p.1⟩) ^ m p := by
    rw [mul_assoc]
    congr 1
    rw [Finset.prod_subset (Finset.subset_univ m.support) (fun p _ hp ↦ by
      rw [Finsupp.notMem_support_iff.mp hp, pow_zero])]
    have hden : ∏ p : Coord n, y ⟨p.1, c p.1⟩ ^ m p = ∏ k, y ⟨k, c k⟩ ^ δ k := by
      rw [Fintype.prod_sigma]
      refine Finset.prod_congr rfl fun k _ ↦ ?_
      rw [← hmδ k, ← Finset.prod_pow_eq_pow_sum]
    simp_rw [div_pow]
    rw [Finset.prod_div_distrib, hden, div_eq_mul_inv, Finset.prod_inv_distrib]
  rw [key]
  refine Subalgebra.mul_mem _ (Subalgebra.algebraMap_mem _ _) (Subalgebra.prod_mem _ fun p _ ↦ ?_)
  exact Subalgebra.pow_mem _ (Algebra.subset_adjoin (Set.mem_range_self p)) _

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Extract witnesses or component facts from the available result. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities.

Establish an intermediate fact. Simplify using the standard rewrite rules. Rewrite the indicated hypotheses using the stated equalities. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.

Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Reduce the equality to equality of the corresponding arguments. Move the embeddings inside the algebraic operations.

Expand and normalize the polynomial expressions, which then agree. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem IntegralSection.value_mem_chartLat {P : ArithVariety n} {a : ι → ℤ}
    (s : IntegralSection P a) {Ω : Type*} [Field Ω] (y : Coord n → Ω)
    (hy : ∀ f ∈ P.ideal, aeval y f = 0) (hG : aeval y s.den ≠ 0) :
    aeval y s.num / aeval y s.den ∈ Geo.chartLat (ι := blockIdx n) y a 1 := by
  intro c hc
  have hX : ∀ k, (X ⟨k, c k⟩ : MvPolynomial (Coord n) ℤ) ∉ P.ideal := fun k hk ↦
    hc k (by simpa using hy _ hk)
  obtain ⟨d, e, ⟨δ, he, hδ⟩, hmem⟩ := s.regular c hX
  have hrel := hy _ hmem
  rw [map_sub, map_mul, map_mul, sub_eq_zero] at hrel
  have hmon : aeval y (chartMonomial c d) = ∏ k, y ⟨k, c k⟩ ^ d k := by
    simp [chartMonomial, map_prod]
  rw [hmon] at hrel
  have hpow : ∏ k, y ⟨k, c k⟩ ^ (-(((1 : ℕ) : ℤ) * a k)) =
      (∏ k, y ⟨k, c k⟩ ^ d k) * ∏ k, (y ⟨k, c k⟩ ^ δ k)⁻¹ := by
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun k _ ↦ ?_
    have h0 := hc k
    rw [← zpow_natCast, ← zpow_natCast, ← zpow_neg, ← zpow_add₀ h0, hδ k]
    congr 1
    push_cast
    ring
  have hval : aeval y s.num / aeval y s.den * ∏ k, y ⟨k, c k⟩ ^ (-(((1 : ℕ) : ℤ) * a k)) =
      aeval y e * ∏ k, (y ⟨k, c k⟩ ^ δ k)⁻¹ := by
    rw [hpow, ← mul_assoc, div_mul_eq_mul_div, ← hrel, mul_comm (aeval y s.den), mul_div_assoc,
      div_self hG, mul_one]
  rw [hval]
  exact aeval_div_chart_mem y c hc e δ he

def orbitIdeal (x : Cone n (AlgebraicClosure ℚ)) : Ideal (MvPolynomial (Coord n) ℤ) :=
  Geo.mCoordIdeal (ι := blockIdx n) (flatCone x)

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Rewrite the indicated hypotheses using the stated equalities. Rewrite the indicated hypotheses using the stated equalities. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities.

A detailed English derivation is pending.
-/
theorem chartMonomial_notMem_orbitIdeal (x : Cone n (AlgebraicClosure ℚ))
    (c : (k : ι) → Fin (n k + 1)) (hc : ∀ k, x k (c k) ≠ 0) (d : ι → ℕ) :
    chartMonomial c d ∉ orbitIdeal x := by
  intro h
  rw [orbitIdeal, Geo.mCoordIdeal, RingHom.mem_ker] at h
  rw [chartMonomial, map_prod] at h
  refine (Finset.prod_ne_zero_iff.mpr fun k _ ↦ ?_) h
  rw [map_pow, Geo.mConeMap, aeval_X]
  exact pow_ne_zero _ (mul_ne_zero (C_ne_zero.mpr (hc k)) (X_ne_zero _))

/- English proof (translation)
Supply the required witnesses or components.
-/
theorem isSectionOn_chartMonomial (A : HermLine n) (x : Cone n (AlgebraicClosure ℚ))
    (c : (k : ι) → Fin (n k + 1)) (hc : ∀ k, x k (c k) ≠ 0) (d : ι → ℕ)
    (hd : ∀ k, A.deg k = d k) :
    Geo.IsSectionOn (orbitIdeal x) A.toGeo (chartMonomial c d) :=
  ⟨d, hd, (geoMultiHomog_iff _ d).mpr (isWeightedHomogeneous_chartMonomial c d),
    chartMonomial_notMem_orbitIdeal x c hc d⟩

/- English proof (translation)
Supply the required witnesses or components.
-/
theorem exists_chart {F : Type*} [Zero F] {x : Cone n F} (hx : BlockNonzero x) :
    ∃ c : (k : ι) → Fin (n k + 1), ∀ k, x k (c k) ≠ 0 :=
  ⟨fun k ↦ (Function.ne_iff.mp (hx k)).choose, fun k ↦ (Function.ne_iff.mp (hx k)).choose_spec⟩

def samplePoint : Cone (fun _ : Unit ↦ 1) (AlgebraicClosure ℚ) := fun _ ↦ ![1, 2]

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Simplify using the standard rewrite rules.
-/
theorem samplePoint_blockNonzero : BlockNonzero samplePoint := by
  intro _ h
  have := congrFun h 0
  simp [samplePoint] at this

/- English proof (translation)
A detailed English derivation is pending.
-/
example : Geo.IsSectionOn (orbitIdeal samplePoint) (HermLine.standard _).toGeo
    (chartMonomial (fun _ ↦ 0) 1) :=
  isSectionOn_chartMonomial _ _ _ (fun _ ↦ by simp [samplePoint]) 1 (fun _ ↦ rfl)

/- English proof (translation)
Supply the required witnesses or components.
-/
example : Geo.IsMultiProjPrime (ι := blockIdx (fun _ : Unit ↦ 1)) (ArithVariety.whole _).ideal ∧
    Geo.IsSmoothHerm (HermLine.standard (fun _ : Unit ↦ 1)).toGeo :=
  ⟨ArithVariety.isMultiProjPrime _, HermLine.isSmoothHerm_toGeo _⟩

end

end GroundTheory.Heights₂.Heights

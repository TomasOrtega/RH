import Mathlib
import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.StatementsMChart
import GroundTheory.ArithmeticGeometry.AbelianVarieties.JacobianSmoothness.RingKrullDimLeRingKrullDimQuotientAddOne
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.FieldNumbers

open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR

noncomputable section

universe u

namespace MChartTrdeg

variable {F : Type u} [Field F] {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type}

/- English proof (translation)
Establish `h` using `IsWeightedHomogeneous.prod (R := F) (w := blockWeight ι) Finset.univ (fun k => (X ⟨k, u k⟩ : MRing ι F) ^ b k) (fun k => b k • blockWeight ι ⟨k, u k⟩) (fun k _ => (isWeightedHomogeneous_X F _ _).pow (b k))`. Establish `hb : ∑ k, b k • blockWeight ι ⟨k, u k⟩ = b`. Use function extensionality and compare the values at `j`. Simplify using `[blockWeight, Finset.sum_apply, Pi.single_apply]`. Unfold `IsMultiHomog chartMonomial`.

Rewrite `h` using `[hb]`. Then use the resulting hypothesis.
-/
theorem chartMonomial_isMultiHomog (u : ∀ k, ι k) (b : K → ℕ) :
    IsMultiHomog (chartMonomial (F := F) u b) b := by
  have h := IsWeightedHomogeneous.prod (R := F) (w := blockWeight ι) Finset.univ
    (fun k => (X ⟨k, u k⟩ : MRing ι F) ^ b k) (fun k => b k • blockWeight ι ⟨k, u k⟩)
    (fun k _ => (isWeightedHomogeneous_X F _ _).pow (b k))
  have hb : ∑ k, b k • blockWeight ι ⟨k, u k⟩ = b := by
    funext j
    simp [blockWeight, Finset.sum_apply, Pi.single_apply]
  unfold IsMultiHomog chartMonomial
  rwa [hb] at h

variable (P : Ideal (MRing ι F)) [P.IsPrime]

omit [Fintype K] [DecidableEq K] [P.IsPrime] in

/- English proof (translation)
Rewrite using `[IsFractionRing.to_map_eq_zero_iff, Ideal.Quotient.eq_zero_iff_mem]`.
-/
theorem map_eq_zero_iff (f : MRing ι F) :
    algebraMap (MRing ι F ⧸ P) (FractionRing (MRing ι F ⧸ P)) (Ideal.Quotient.mk P f) = 0 ↔ f ∈ P := by
  rw [IsFractionRing.to_map_eq_zero_iff, Ideal.Quotient.eq_zero_iff_mem]

omit [DecidableEq K] [P.IsPrime] in

/- English proof (translation)
Simplify using `[chartMonomial, map_prod, map_pow]`.
-/
theorem map_chartMonomial (u : ∀ k, ι k) (b : K → ℕ) :
    algebraMap (MRing ι F ⧸ P) (FractionRing (MRing ι F ⧸ P)) (Ideal.Quotient.mk P (chartMonomial u b)) =
      ∏ k, algebraMap (MRing ι F ⧸ P) (FractionRing (MRing ι F ⧸ P))
        (Ideal.Quotient.mk P (X ⟨k, u k⟩)) ^ b k := by
  simp [chartMonomial, map_prod, map_pow]

omit [DecidableEq K] in

/- English proof (translation)
Rewrite using `[map_chartMonomial]`. Conclude with `Finset.prod_ne_zero_iff.2 fun k _ => pow_ne_zero _ fun h => hu k ((map_eq_zero_iff P _).1 h)`.
-/
theorem map_chartMonomial_ne_zero (u : ∀ k, ι k) (hu : ∀ k, (X ⟨k, u k⟩ : MRing ι F) ∉ P)
    (b : K → ℕ) :
    algebraMap (MRing ι F ⧸ P) (FractionRing (MRing ι F ⧸ P))
      (Ideal.Quotient.mk P (chartMonomial u b)) ≠ 0 := by
  rw [map_chartMonomial]
  exact Finset.prod_ne_zero_iff.2 fun k _ => pow_ne_zero _ fun h => hu k ((map_eq_zero_iff P _).1 h)

/- English proof (translation)
Use `set L := FractionRing (MRing ι F ⧸ P)`. Use `set φ : MRing ι F →+* L := (algebraMap (MRing ι F ⧸ P) L).comp (Ideal.Quotient.mk P) with hφ`. Establish `hφapp : ∀ f, φ f = algebraMap (MRing ι F ⧸ P) L (Ideal.Quotient.mk P f)` using `fun _ => rfl`. Rewrite using `[algebraicIndependent_iff]`. Introduce `p hp`.

Establish `hq : ∀ m, ∃ q, chartMap P u q = ((p.coeff m : (chartMap P u).range) : L)` using `fun m => (p.coeff m).2`. Use `choose q hq using hq`. Use `choose b h hhom heq using fun m => hH F K ι u (q m)`. Establish `hval : ∀ m, φ (h m) = ((p.coeff m : (chartMap P u).range) : L) * φ (chartMonomial u (b m))`. Introduce `m`.

Use `heq m P hu` as an intermediate fact. Rewrite `this` using `[hq m, eq_div_iff (map_chartMonomial_ne_zero P u hu _)]`. Rewrite using `[hφapp, hφapp]`. Conclude with `this.symm`. Use `set s := p.support`.

Use `set N : K → ℕ := ∑ m ∈ s, b m`. Establish `hbN : ∀ m ∈ s, ∀ k, b m k ≤ N k` using `fun m hm => Finset.single_le_sum (f := b) (fun _ _ _ => Nat.zero_le _) hm`. Use `set c : (K →₀ ℕ) → K → ℕ := fun m => N - b m + ⇑m`. Establish `hbc : ∀ m ∈ s, b m + c m = N + ⇑m`. Introduce `m hm`.

Use function extensionality and compare the values at `k`. Use `hbN m hm k` as an intermediate fact. Simplify using `only [c, Pi.add_apply, Pi.sub_apply]`. Use linear arithmetic over natural numbers and integers. Use `set G := ∑ m ∈ s, h m * chartMonomial u (c m)`.

Establish `hG : G ∈ P`. Rewrite using `[← map_eq_zero_iff, ← hφapp]`. Establish `hp'` using `hp`. Rewrite `hp'` using `[aeval_def, eval₂_eq']`. Combine the equalities or inequalities in the displayed calculation.

Simplify using `only [G, map_sum, map_mul, hval]`. Use `Finset.sum_congr rfl fun m hm => ?_` and prove the remaining obligations. Rewrite using `[hφapp (chartMonomial u (b m)), hφapp (chartMonomial u (c m)), hφapp (chartMonomial u N), map_chartMonomial, map_chartMonomial, map_chartMonomial]`. Establish `e : ∀ x : K → L, (∏ k, x k ^ b m k) * (∏ k, x k ^ c m k) = (∏ k, x k ^ N k) * ∏ k, x k ^ m k`. Introduce `x`.

Rewrite using `[← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]`. Use `Finset.prod_congr rfl fun k _ => ?_` and prove the remaining obligations. Rewrite using `[← pow_add, ← pow_add]`. Conclude with `congrArg (x k ^ ·) (congrFun (hbc m hm) k)`. Rewrite using `[mul_assoc, e, mul_left_comm]`.

Both sides reduce to the same expression. Use `_ = 0 := by rw [← Finset.mul_sum, hp', mul_zero]`. Establish `hhomt : ∀ m ∈ s, IsMultiHomog (h m * chartMonomial u (c m)) (N + ⇑m)`. Introduce `m hm`. Unfold `IsMultiHomog`.

Rewrite using `[← hbc m hm]`. Conclude with `IsWeightedHomogeneous.mul (hhom m) (chartMonomial_isMultiHomog u (c m))`. Establish `hcomp : ∀ m ∈ s, weightedHomogeneousComponent (blockWeight ι) (N + ⇑m) G = h m * chartMonomial u (c m)`. Introduce `m hm`. Simplify using `only [G, map_sum]`.

Rewrite using `[Finset.sum_eq_single m]`. Conclude with `IsWeightedHomogeneous.weightedHomogeneousComponent_same (hhomt m hm)`. Introduce `m' hm' hne`. Conclude with `IsWeightedHomogeneous.weightedHomogeneousComponent_ne (N + ⇑m) (hhomt m' hm') fun e => hne (DFunLike.coe_injective (add_left_cancel e)).symm`. Introduce `hms`.

Conclude with `absurd hm hms`. Establish `hzero : ∀ m ∈ s, p.coeff m = 0`. Introduce `m hm`. Establish `hmem : h m * chartMonomial u (c m) ∈ P` using `hcomp m hm ▸ hP G hG (N + ⇑m)`. Establish `hcm : chartMonomial u (c m) ∉ P` using `fun h' => map_chartMonomial_ne_zero P u hu (c m) ((map_eq_zero_iff P _).2 h')`.

Establish `hh : h m ∈ P` using `(Ideal.IsPrime.mem_or_mem ‹_› hmem).resolve_right hcm`. Establish `h2` using `hval m`. Rewrite `h2` using `[hφapp, (map_eq_zero_iff P _).2 hh, eq_comm, mul_eq_zero]`. Break down `h2 with h2 | h2` into its components or cases. Conclude with `Subtype.ext h2`.

Conclude with `absurd h2 (map_chartMonomial_ne_zero P u hu (b m))`. Use extensionality with `m`. Assume the negation of the conclusion as `hne`. Conclude with `hne (by simpa using hzero m (mem_support_iff.2 (by simpa using hne)))`.
-/
theorem algebraicIndependent (hH : MChartHomog.Statement.{u}) (hP : IsMultiHomogIdeal P)
    (u : ∀ k, ι k) (hu : ∀ k, (X ⟨k, u k⟩ : MRing ι F) ∉ P) :
    AlgebraicIndependent (chartMap P u).range (fun k => algebraMap (MRing ι F ⧸ P)
      (FractionRing (MRing ι F ⧸ P)) (Ideal.Quotient.mk P (X ⟨k, u k⟩))) := by
  classical
  set L := FractionRing (MRing ι F ⧸ P)
  set φ : MRing ι F →+* L := (algebraMap (MRing ι F ⧸ P) L).comp (Ideal.Quotient.mk P) with hφ
  have hφapp : ∀ f, φ f = algebraMap (MRing ι F ⧸ P) L (Ideal.Quotient.mk P f) := fun _ => rfl
  rw [algebraicIndependent_iff]
  intro p hp

  have hq : ∀ m, ∃ q, chartMap P u q = ((p.coeff m : (chartMap P u).range) : L) := fun m => (p.coeff m).2
  choose q hq using hq
  choose b h hhom heq using fun m => hH F K ι u (q m)
  have hval : ∀ m, φ (h m) = ((p.coeff m : (chartMap P u).range) : L) * φ (chartMonomial u (b m)) := by
    intro m
    have := heq m P hu
    rw [hq m, eq_div_iff (map_chartMonomial_ne_zero P u hu _)] at this
    rw [hφapp, hφapp]
    exact this.symm
  set s := p.support
  set N : K → ℕ := ∑ m ∈ s, b m
  have hbN : ∀ m ∈ s, ∀ k, b m k ≤ N k := fun m hm =>
    Finset.single_le_sum (f := b) (fun _ _ _ => Nat.zero_le _) hm
  set c : (K →₀ ℕ) → K → ℕ := fun m => N - b m + ⇑m
  have hbc : ∀ m ∈ s, b m + c m = N + ⇑m := by
    intro m hm
    funext k
    have := hbN m hm k
    simp only [c, Pi.add_apply, Pi.sub_apply]
    omega

  set G := ∑ m ∈ s, h m * chartMonomial u (c m)
  have hG : G ∈ P := by
    rw [← map_eq_zero_iff, ← hφapp]
    have hp' := hp
    rw [aeval_def, eval₂_eq'] at hp'
    calc φ G = ∑ m ∈ s, φ (chartMonomial u N) * (algebraMap (chartMap P u).range L (p.coeff m) *
          ∏ k, algebraMap (MRing ι F ⧸ P) L (Ideal.Quotient.mk P (X ⟨k, u k⟩)) ^ m k) := by
          simp only [G, map_sum, map_mul, hval]
          refine Finset.sum_congr rfl fun m hm => ?_
          rw [hφapp (chartMonomial u (b m)), hφapp (chartMonomial u (c m)), hφapp (chartMonomial u N),
            map_chartMonomial, map_chartMonomial, map_chartMonomial]
          have e : ∀ x : K → L, (∏ k, x k ^ b m k) * (∏ k, x k ^ c m k) =
              (∏ k, x k ^ N k) * ∏ k, x k ^ m k := by
            intro x
            rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
            refine Finset.prod_congr rfl fun k _ => ?_
            rw [← pow_add, ← pow_add]
            exact congrArg (x k ^ ·) (congrFun (hbc m hm) k)
          rw [mul_assoc, e, mul_left_comm]
          rfl
      _ = 0 := by rw [← Finset.mul_sum, hp', mul_zero]

  have hhomt : ∀ m ∈ s, IsMultiHomog (h m * chartMonomial u (c m)) (N + ⇑m) := by
    intro m hm
    unfold IsMultiHomog
    rw [← hbc m hm]
    exact IsWeightedHomogeneous.mul (hhom m) (chartMonomial_isMultiHomog u (c m))
  have hcomp : ∀ m ∈ s,
      weightedHomogeneousComponent (blockWeight ι) (N + ⇑m) G = h m * chartMonomial u (c m) := by
    intro m hm
    simp only [G, map_sum]
    rw [Finset.sum_eq_single m]
    · exact IsWeightedHomogeneous.weightedHomogeneousComponent_same (hhomt m hm)
    · intro m' hm' hne
      exact IsWeightedHomogeneous.weightedHomogeneousComponent_ne (N + ⇑m) (hhomt m' hm')
        fun e => hne (DFunLike.coe_injective (add_left_cancel e)).symm
    · intro hms
      exact absurd hm hms

  have hzero : ∀ m ∈ s, p.coeff m = 0 := by
    intro m hm
    have hmem : h m * chartMonomial u (c m) ∈ P := hcomp m hm ▸ hP G hG (N + ⇑m)
    have hcm : chartMonomial u (c m) ∉ P := fun h' =>
      map_chartMonomial_ne_zero P u hu (c m) ((map_eq_zero_iff P _).2 h')
    have hh : h m ∈ P := (Ideal.IsPrime.mem_or_mem ‹_› hmem).resolve_right hcm
    have h2 := hval m
    rw [hφapp, (map_eq_zero_iff P _).2 hh, eq_comm, mul_eq_zero] at h2
    rcases h2 with h2 | h2
    · exact Subtype.ext h2
    · exact absurd h2 (map_chartMonomial_ne_zero P u hu (b m))
  ext m
  by_contra hne
  exact hne (by simpa using hzero m (mem_support_iff.2 (by simpa using hne)))

omit [Fintype K] [DecidableEq K] in

/- English proof (translation)
Use `set R := MRing ι F ⧸ P`. Use `set L := FractionRing R`. Use `set A₀ := (chartMap P u).range`. Use `set S' := Algebra.adjoin A₀ (Set.range fun k => algebraMap R L (Ideal.Quotient.mk P (X ⟨k, u k⟩)))`. Establish `hξS : ∀ v, algebraMap R L (Ideal.Quotient.mk P (X v)) ∈ S'`.

Introduce `v`. Establish `hr : chartMap P u (X v) ∈ A₀` using `AlgHom.mem_range_self _ _`. Establish `hne : algebraMap R L (Ideal.Quotient.mk P (X ⟨v.1, u v.1⟩)) ≠ 0` using `fun h => hu v.1 ((map_eq_zero_iff P _).1 h)`. Establish `e : algebraMap R L (Ideal.Quotient.mk P (X v)) = chartMap P u (X v) * algebraMap R L (Ideal.Quotient.mk P (X ⟨v.1, u v.1⟩))`. Simplify using `only [chartMap, aeval_X]`.

Conclude with `(div_mul_cancel₀ _ hne).symm`. Rewrite using `[e]`. Conclude with `S'.mul_mem (S'.algebraMap_mem (⟨_, hr⟩ : A₀)) (Algebra.subset_adjoin ⟨v.1, rfl⟩)`. Establish `hRS : ∀ r : R, algebraMap R L r ∈ S'`. Introduce `r`.

Take `⟨f, rfl⟩` from `Ideal.Quotient.mk_surjective r`. Proceed by induction on `f using MvPolynomial.induction_on with`. Consider the case `C c`. Rewrite using `[show (Ideal.Quotient.mk P (C c) : R) = algebraMap F R c from rfl, ← IsScalarTower.algebraMap_apply, IsScalarTower.algebraMap_apply F A₀ L]`. Conclude with `S'.algebraMap_mem _`.

Consider the case `add f g hf hg => rw [map_add, map_add]`. Conclude with `S'.add_mem hf hg`. Consider the case `mul_X f i hf => rw [map_mul, map_mul]`. Conclude with `S'.mul_mem hf (hξS i)`. Set `_ : CommRing S'` to `Subalgebra.toCommRing S'`.

Use `⟨fun x => ?_⟩` and prove the remaining obligations. Take `⟨a, d, hd, rfl⟩` from `IsFractionRing.div_surjective (A := R) x`. Establish `hd0 : algebraMap R L d ≠ 0` using `IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hd`. Use `⟨Polynomial.C (⟨_, hRS d⟩ : S') * Polynomial.X - Polynomial.C (⟨_, hRS a⟩ : S'), fun h => hd0 ?_, ?_⟩` and prove the remaining obligations. Use `congrArg (Polynomial.coeff · 1) h` as an intermediate fact.

Simplify using `only [Polynomial.coeff_sub, Polynomial.coeff_C_mul_X, Polynomial.coeff_C, ↓reduceIte, one_ne_zero, Polynomial.coeff_zero] at this`. Establish `h'` using `congrArg Subtype.val this`. Simplify using `only [Subalgebra.coe_zero, sub_zero] at h'`. Conclude with `h'`. Simplify using `only [map_sub, map_mul, Polynomial.aeval_C, Polynomial.aeval_X] show algebraMap R L d * (algebraMap R L a / algebraMap R L d) - algebraMap R L a = 0`.

Rewrite using `[mul_comm, div_mul_cancel₀ _ hd0, sub_self]`.
-/
theorem isAlgebraic_adjoin (u : ∀ k, ι k) (hu : ∀ k, (X ⟨k, u k⟩ : MRing ι F) ∉ P) :
    Algebra.IsAlgebraic (Algebra.adjoin (chartMap P u).range (Set.range fun k =>
      algebraMap (MRing ι F ⧸ P) (FractionRing (MRing ι F ⧸ P)) (Ideal.Quotient.mk P (X ⟨k, u k⟩))))
      (FractionRing (MRing ι F ⧸ P)) := by
  set R := MRing ι F ⧸ P
  set L := FractionRing R
  set A₀ := (chartMap P u).range
  set S' := Algebra.adjoin A₀ (Set.range fun k => algebraMap R L (Ideal.Quotient.mk P (X ⟨k, u k⟩)))
  have hξS : ∀ v, algebraMap R L (Ideal.Quotient.mk P (X v)) ∈ S' := by
    intro v
    have hr : chartMap P u (X v) ∈ A₀ := AlgHom.mem_range_self _ _
    have hne : algebraMap R L (Ideal.Quotient.mk P (X ⟨v.1, u v.1⟩)) ≠ 0 :=
      fun h => hu v.1 ((map_eq_zero_iff P _).1 h)
    have e : algebraMap R L (Ideal.Quotient.mk P (X v)) =
        chartMap P u (X v) * algebraMap R L (Ideal.Quotient.mk P (X ⟨v.1, u v.1⟩)) := by
      simp only [chartMap, aeval_X]
      exact (div_mul_cancel₀ _ hne).symm
    rw [e]
    exact S'.mul_mem (S'.algebraMap_mem (⟨_, hr⟩ : A₀)) (Algebra.subset_adjoin ⟨v.1, rfl⟩)
  have hRS : ∀ r : R, algebraMap R L r ∈ S' := by
    intro r
    obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective r
    induction f using MvPolynomial.induction_on with
    | C c =>
      rw [show (Ideal.Quotient.mk P (C c) : R) = algebraMap F R c from rfl,
        ← IsScalarTower.algebraMap_apply, IsScalarTower.algebraMap_apply F A₀ L]
      exact S'.algebraMap_mem _
    | add f g hf hg => rw [map_add, map_add]; exact S'.add_mem hf hg
    | mul_X f i hf => rw [map_mul, map_mul]; exact S'.mul_mem hf (hξS i)
  let _ : CommRing S' := Subalgebra.toCommRing S'
  refine ⟨fun x => ?_⟩
  obtain ⟨a, d, hd, rfl⟩ := IsFractionRing.div_surjective (A := R) x
  have hd0 : algebraMap R L d ≠ 0 := IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hd
  refine ⟨Polynomial.C (⟨_, hRS d⟩ : S') * Polynomial.X - Polynomial.C (⟨_, hRS a⟩ : S'),
    fun h => hd0 ?_, ?_⟩
  · have := congrArg (Polynomial.coeff · 1) h
    simp only [Polynomial.coeff_sub, Polynomial.coeff_C_mul_X, Polynomial.coeff_C, ↓reduceIte,
      one_ne_zero, Polynomial.coeff_zero] at this
    have h' := congrArg Subtype.val this
    simp only [Subalgebra.coe_zero, sub_zero] at h'
    exact h'
  · simp only [map_sub, map_mul, Polynomial.aeval_C, Polynomial.aeval_X]
    show algebraMap R L d * (algebraMap R L a / algebraMap R L d) - algebraMap R L a = 0
    rw [mul_comm, div_mul_cancel₀ _ hd0, sub_self]

end MChartTrdeg

/- English proof (translation)
Introduce `F _ K _ _ ι _ P _ hP u hu`. Use `set R := MRing ι F ⧸ P`. Use `set L := FractionRing R`. Use `set A₀ := (chartMap P u).range`. Establish `hb : IsTranscendenceBasis A₀ (fun k => algebraMap R L (Ideal.Quotient.mk P (X ⟨k, u k⟩)))` using `(MChartTrdeg.algebraicIndependent P hH hP u hu).isTranscendenceBasis_iff_isAlgebraic.mpr (MChartTrdeg.isAlgebraic_adjoin P u hu)`.

Establish `h1 : Algebra.trdeg A₀ L = Fintype.card K`. Simplify using `using hb.lift_cardinalMk_eq_trdeg.symm`. Establish `: FaithfulSMul A₀ L` using `(faithfulSMul_iff_algebraMap_injective _ _).2 Subtype.val_injective`. Establish `: FaithfulSMul F A₀` using `(faithfulSMul_iff_algebraMap_injective _ _).2 (algebraMap F A₀).injective`. Rewrite using `[show Algebra.trdeg F (MRing ι F ⧸ chartIdeal P u) = Algebra.trdeg F A₀ from (Ideal.quotientKerEquivRange (chartMap P u)).trdeg_eq, ← h1, trdeg_add_eq F A₀ (A := L), GroundTheory.Arith.Abelian.Jacobian.trdeg_eq_of_isFractionRing (k := F) (A := R) L]`.
-/
theorem MChartTrdeg.proof (hH : MChartHomog.Statement.{u}) : MChartTrdeg.Statement.{u} := by
  intro F _ K _ _ ι _ P _ hP u hu
  set R := MRing ι F ⧸ P
  set L := FractionRing R
  set A₀ := (chartMap P u).range
  have hb : IsTranscendenceBasis A₀ (fun k => algebraMap R L (Ideal.Quotient.mk P (X ⟨k, u k⟩))) :=
    (MChartTrdeg.algebraicIndependent P hH hP u hu).isTranscendenceBasis_iff_isAlgebraic.mpr
      (MChartTrdeg.isAlgebraic_adjoin P u hu)
  have h1 : Algebra.trdeg A₀ L = Fintype.card K := by
    simpa using hb.lift_cardinalMk_eq_trdeg.symm
  have : FaithfulSMul A₀ L :=
    (faithfulSMul_iff_algebraMap_injective _ _).2 Subtype.val_injective
  have : FaithfulSMul F A₀ :=
    (faithfulSMul_iff_algebraMap_injective _ _).2 (algebraMap F A₀).injective
  rw [show Algebra.trdeg F (MRing ι F ⧸ chartIdeal P u) = Algebra.trdeg F A₀ from
      (Ideal.quotientKerEquivRange (chartMap P u)).trdeg_eq, ← h1, trdeg_add_eq F A₀ (A := L),
    GroundTheory.Arith.Abelian.Jacobian.trdeg_eq_of_isFractionRing (k := F) (A := R) L]

end

end GroundTheory.Heights₂.Heights.FieldNumbers

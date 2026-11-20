import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.DlogRatioVolumeFormNeZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ComplementaryModuleEqTopFormsOfFiniteCoverStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.VolumeChartChangeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KahlerFormsOverSubalgebraStandardOpenIffPowSmulStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteCoverRingLocalizationChart
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteCoverChartSmoothNormal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemStandardOpenCoordinateRingIffLocalizationCharStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StandardAffineOpenRingPolynomialEquivStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StandardOpenCoordinateRingIsFractionRingIsNoetheStatement

set_option autoImplicit false

open GlobalTheory.PD GlobalTheory.CechDR KaehlerDifferential

namespace GlobalTheory.ComplStd

/- English proof (translation)
Simplify using `only [omA, Submodule.mem_iInf, Submodule.mem_comap, LinearMap.mulLeft_apply, Subalgebra.mem_toSubmodule]`. Use `⟨fun h => h i hi, fun h i' _ => ?_⟩` and prove the remaining obligations. Establish `hg : x i' / x i ∈ rA k x I` using `Algebra.subset_adjoin ⟨i, hi, i', rfl⟩`. Establish `e : (∏ j, x i' / x j) = (x i' / x i) ^ (d + 1) * ∏ j, x i / x j`. Rewrite using `[show (x i' / x i) ^ (d + 1) = ∏ _j : Fin (d + 1), x i' / x i by`.

Rewrite using `[Finset.prod_const, Finset.card_univ, Fintype.card_fin], ← Finset.prod_mul_distrib]`. Conclude with `Finset.prod_congr rfl fun j _ => (div_mul_div_cancel₀ (hx i)).symm`. Rewrite using `[e, mul_assoc]`. Conclude with `Subalgebra.mul_mem _ (Subalgebra.pow_mem _ hg _) h`.
-/
theorem mem_omA_iff {k F : Type} [Field k] [Field F] [Algebra k F] {d : ℕ} {x : Fin (d + 1) → F}
    (hx : ∀ i, x i ≠ 0) {I : Finset (Fin (d + 1))} {i : Fin (d + 1)} (hi : i ∈ I) (f : F) :
    f ∈ omA k x I ↔ (∏ j, x i / x j) * f ∈ rA k x I := by
  simp only [omA, Submodule.mem_iInf, Submodule.mem_comap, LinearMap.mulLeft_apply, Subalgebra.mem_toSubmodule]
  refine ⟨fun h => h i hi, fun h i' _ => ?_⟩
  have hg : x i' / x i ∈ rA k x I := Algebra.subset_adjoin ⟨i, hi, i', rfl⟩
  have e : (∏ j, x i' / x j) = (x i' / x i) ^ (d + 1) * ∏ j, x i / x j := by
    rw [show (x i' / x i) ^ (d + 1) = ∏ _j : Fin (d + 1), x i' / x i by
      rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin], ← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl fun j _ => (div_mul_div_cancel₀ (hx i)).symm
  rw [e, mul_assoc]
  exact Subalgebra.mul_mem _ (Subalgebra.pow_mem _ hg _) h

/- English proof (translation)
Rewrite using `[← Algebra.smul_def, LinearMap.map_smul, smul_eq_mul]`.
-/
theorem trace_algebraMap_mul {F K : Type} [Field F] [Field K] [Algebra F K] (c : F) (w : K) :
    Algebra.trace F K (algebraMap F K c * w) = c * Algebra.trace F K w := by
  rw [← Algebra.smul_def, LinearMap.map_smul, smul_eq_mul]

/- English proof (translation)
Use `haveI := hc.fin`. Establish `hx` using `hc.pd.ne`. Take `⟨e, he⟩` from `GlobalTheory.T.standardAffineOpen_ring_polynomialEquiv k F d x hc.pd i`. Use `set u : Fin d → F := fun j => x (i.succAbove j) / x i with hu_def`. Establish `hu : AlgebraicIndependent k u`.

Rewrite using `[algebraicIndependent_iff_injective_aeval]`. Establish `: MvPolynomial.aeval u = (rA k x {i}).val.comp e.toAlgHom` using `MvPolynomial.algHom_ext fun j => by simp [he, u]`. Rewrite using `[this]`. Conclude with `Subtype.val_injective.comp e.injective`. Establish `hA : rA k x {i} = Algebra.adjoin k (Set.range u)`.

Apply `le_antisymm` to reduce the goal to its premises. Apply `Algebra.adjoin_le` to reduce the goal to its premises. Introduce and unpack `y ⟨i', hi', j, rfl⟩`. Rewrite `hi'` using `[Finset.mem_singleton]`. Substitute `hi'` using the available equality.

Distinguish the cases in `hj : j = i'`. Substitute `hj` using the available equality. Rewrite using `[div_self (hx _)]`. Conclude with `one_mem _`. Take `⟨j', rfl⟩` from `Fin.exists_succAbove_eq hj`.

Conclude with `Algebra.subset_adjoin ⟨j', rfl⟩`. Apply `Algebra.adjoin_le` to reduce the goal to its premises. Introduce and unpack `y ⟨j, rfl⟩`. Conclude with `Algebra.subset_adjoin ⟨i, Finset.mem_singleton_self _, _, rfl⟩`. Use `haveI : IsFractionRing (rA k x {i}) F := (GlobalTheory.T.standardOpenCoordinateRing_isFractionRing_isNoetherianRing k F d x hc.pd {i} (Finset.singleton_nonempty _)).1`.

Take `⟨ε, hε⟩` from `GlobalTheory.T.exists_sign_iMulti_D_chart_change k F K d x hc i`. Use `set P : F := ∏ j, x i / x j with hP`. Use `set C : F := ∏ j, x j / x i with hC`. Establish `hPC : algebraMap F K P * algebraMap F K C = 1`. Rewrite using `[← map_mul, hP, hC, ← Finset.prod_mul_distrib]`.

Rewrite using `[Finset.prod_eq_one fun j _ => by rw [div_mul_div_cancel₀ (hx j), div_self (hx i)], map_one]`. Establish `hPne : algebraMap F K P ≠ 0` using `left_ne_zero_of_mul_eq_one hPC`. Set `τ' : DR k K →ₗ[K] K` to `(((ε : ℤ) : K) * algebraMap F K P) • τ`. Establish `hτ' : τ' (ExteriorAlgebra.ιMulti K d fun j => D k K (algebraMap F K (u j))) = 1`. Simplify using `only [u]`.

Rewrite using `[hε]`. Rewrite using `[LinearMap.smul_apply, Units.smul_def, map_zsmul, map_smul, hτ.1]`. Simplify using `only [smul_eq_mul, zsmul_eq_mul, mul_one]`. Establish `hε2 : ((ε : ℤ) : K) * ((ε : ℤ) : K) = 1`. Rewrite using `[← Int.cast_mul, ← Units.val_mul, Int.units_mul_self, Units.val_one, Int.cast_one]`.

Take the linear combination `(algebraMap F K P * algebraMap F K C) * hε2 + hPC`. Establish `key` using `GlobalTheory.T.complementaryModule_eq_topForms_of_finiteCover k F K d u hu (rA k x {i}) hA (rB k K x {i}) rfl (hc.smooth i) τ' hτ' (algebraMap F K P * z)`. Establish `lhs : (∀ b ∈ rB k K x {i}, Algebra.trace F K (z * b) ∈ omA k x {i}) ↔ ∀ b : rB k K x {i}, Algebra.trace F K (algebraMap F K P * z * b) ∈ rA k x {i}`. Simplify using `only [Subtype.forall, mem_omA_iff hx (Finset.mem_singleton_self i), mul_assoc, trace_algebraMap_mul]`. Conclude with `Iff.rfl`.

Establish `rhs : (∃ y ∈ omB k K (rB k K x {i}) d, τ' y = algebraMap F K P * z) ↔ ∃ y ∈ omB k K (rB k K x {i}) d, τ y = z`. Establish `h1 : ∀ y, τ' y = algebraMap F K P * z ↔ ((ε : ℤ) : K) * τ y = z`. Introduce `y`. Simplify using `only [τ', LinearMap.smul_apply, smul_eq_mul]`. Rewrite using `[show ((ε : ℤ) : K) * algebraMap F K P * τ y = algebraMap F K P * (((ε : ℤ) : K) * τ y) by ring, mul_right_inj' hPne]`.

Simplify using `only [h1]`. Break down `Int.units_eq_one_or ε with rfl | rfl` into its components or cases. Simplify using the standard rewrite rules. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨y, hy, h⟩; exact ⟨-y, neg_mem hy, by rw [map_neg]; simpa using h⟩`.

Introduce and unpack `⟨y, hy, h⟩; exact ⟨-y, neg_mem hy, by rw [map_neg]; simp [h]⟩`. Conclude with `lhs.trans (key.trans rhs)`.
-/
theorem single (k : Type) [Field k] [CharZero k] (F K : Type) [Field F] [Field K] [Algebra k F] [Algebra k K]
    [Algebra F K] [IsScalarTower k F K] (d : ℕ) (x : Fin (d + 1) → F) (hc : IsFinCover k K x)
    (τ : DR k K →ₗ[K] K) (hτ : IsTop k K x τ) (i : Fin (d + 1)) (z : K) :
    (∀ b ∈ rB k K x {i}, Algebra.trace F K (z * b) ∈ omA k x {i}) ↔ ∃ y ∈ omB k K (rB k K x {i}) d, τ y = z := by
  haveI := hc.fin
  have hx := hc.pd.ne
  obtain ⟨e, he⟩ := GlobalTheory.T.standardAffineOpen_ring_polynomialEquiv k F d x hc.pd i
  set u : Fin d → F := fun j => x (i.succAbove j) / x i with hu_def
  have hu : AlgebraicIndependent k u := by
    rw [algebraicIndependent_iff_injective_aeval]
    have : MvPolynomial.aeval u = (rA k x {i}).val.comp e.toAlgHom :=
      MvPolynomial.algHom_ext fun j => by simp [he, u]
    rw [this]
    exact Subtype.val_injective.comp e.injective
  have hA : rA k x {i} = Algebra.adjoin k (Set.range u) := by
    apply le_antisymm
    · apply Algebra.adjoin_le
      rintro y ⟨i', hi', j, rfl⟩
      rw [Finset.mem_singleton] at hi'
      subst hi'
      by_cases hj : j = i'
      · subst hj; rw [div_self (hx _)]; exact one_mem _
      · obtain ⟨j', rfl⟩ := Fin.exists_succAbove_eq hj
        exact Algebra.subset_adjoin ⟨j', rfl⟩
    · apply Algebra.adjoin_le
      rintro y ⟨j, rfl⟩
      exact Algebra.subset_adjoin ⟨i, Finset.mem_singleton_self _, _, rfl⟩
  haveI : IsFractionRing (rA k x {i}) F := (GlobalTheory.T.standardOpenCoordinateRing_isFractionRing_isNoetherianRing k F d x hc.pd {i} (Finset.singleton_nonempty _)).1
  obtain ⟨ε, hε⟩ := GlobalTheory.T.exists_sign_iMulti_D_chart_change k F K d x hc i
  set P : F := ∏ j, x i / x j with hP
  set C : F := ∏ j, x j / x i with hC
  have hPC : algebraMap F K P * algebraMap F K C = 1 := by
    rw [← map_mul, hP, hC, ← Finset.prod_mul_distrib]
    rw [Finset.prod_eq_one fun j _ => by rw [div_mul_div_cancel₀ (hx j), div_self (hx i)], map_one]
  have hPne : algebraMap F K P ≠ 0 := left_ne_zero_of_mul_eq_one hPC
  let τ' : DR k K →ₗ[K] K := (((ε : ℤ) : K) * algebraMap F K P) • τ
  have hτ' : τ' (ExteriorAlgebra.ιMulti K d fun j => D k K (algebraMap F K (u j))) = 1 := by
    simp only [u]
    rw [hε]
    rw [LinearMap.smul_apply, Units.smul_def, map_zsmul, map_smul, hτ.1]
    simp only [smul_eq_mul, zsmul_eq_mul, mul_one]
    have hε2 : ((ε : ℤ) : K) * ((ε : ℤ) : K) = 1 := by
      rw [← Int.cast_mul, ← Units.val_mul, Int.units_mul_self, Units.val_one, Int.cast_one]
    linear_combination (algebraMap F K P * algebraMap F K C) * hε2 + hPC
  have key := GlobalTheory.T.complementaryModule_eq_topForms_of_finiteCover k F K d u hu (rA k x {i}) hA (rB k K x {i}) rfl (hc.smooth i) τ' hτ'
    (algebraMap F K P * z)
  have lhs : (∀ b ∈ rB k K x {i}, Algebra.trace F K (z * b) ∈ omA k x {i}) ↔
      ∀ b : rB k K x {i}, Algebra.trace F K (algebraMap F K P * z * b) ∈ rA k x {i} := by
    simp only [Subtype.forall, mem_omA_iff hx (Finset.mem_singleton_self i), mul_assoc, trace_algebraMap_mul]
    exact Iff.rfl
  have rhs : (∃ y ∈ omB k K (rB k K x {i}) d, τ' y = algebraMap F K P * z) ↔
      ∃ y ∈ omB k K (rB k K x {i}) d, τ y = z := by
    have h1 : ∀ y, τ' y = algebraMap F K P * z ↔ ((ε : ℤ) : K) * τ y = z := by
      intro y
      simp only [τ', LinearMap.smul_apply, smul_eq_mul]
      rw [show ((ε : ℤ) : K) * algebraMap F K P * τ y = algebraMap F K P * (((ε : ℤ) : K) * τ y) by ring,
        mul_right_inj' hPne]
    simp only [h1]
    rcases Int.units_eq_one_or ε with rfl | rfl
    · simp
    · constructor
      · rintro ⟨y, hy, h⟩; exact ⟨-y, neg_mem hy, by rw [map_neg]; simpa using h⟩
      · rintro ⟨y, hy, h⟩; exact ⟨-y, neg_mem hy, by rw [map_neg]; simp [h]⟩
  exact lhs.trans (key.trans rhs)

/- English proof (translation)
Establish `hx` using `hc.pd.ne`. Use `set s : F := ∏ j ∈ I, x j / x i with hs`. Use `set P : F := ∏ j, x i / x j with hP`. Establish `hs1 : s ∈ rA k x {i}` using `Subalgebra.prod_mem _ fun j _ => Algebra.subset_adjoin ⟨i, Finset.mem_singleton_self _, j, rfl⟩`. Establish `hle : rB k K x {i} ≤ rB k K x I` using `(GlobalTheory.T.finite_cover_ring_localization_chart k F K d x hc {i} i (Finset.mem_singleton_self _)).1 I (Finset.singleton_subset_iff.2 hi)`.

Use `haveI : Module.Finite (rA k x {i}) (integralClosure (rA k x {i}) K) := (GlobalTheory.T.finite_cover_chart_smooth_normal k F K d x hc {i} (Finset.singleton_nonempty _)).1`. Take `⟨S, hS⟩` from `Module.Finite.fg_top (R := rA k x {i}) (M := integralClosure (rA k x {i}) K)`. Establish `hg : ∀ g : integralClosure (rA k x {i}) K, ∃ N : ℕ, P * Algebra.trace F K (z * g) * s ^ N ∈ rA k x {i}`. Introduce `g`. Establish `hgI : (g : K) ∈ rB k K x I` using `hle g.2`.

Conclude with `(GlobalTheory.T.mem_standardOpenCoordinateRing_iff_localization_chart k F d x hc.pd I i hi _).1 ((mem_omA_iff hx hi _).1 (h _ hgI))`. Use `choose Nf hNf using hg`. Use `⟨∑ g ∈ S, Nf g, fun b hb => ?_⟩` and prove the remaining obligations. Rewrite using `[mem_omA_iff hx (Finset.mem_singleton_self i)]`. Establish `hb' : (⟨b, hb⟩ : integralClosure (rA k x {i}) K) ∈ Submodule.span (rA k x {i}) (S : Set _)`.

Rewrite using `[hS]`. Discharge the goal by the elementary cases of `trivial`. Establish `key : ∀ w : integralClosure (rA k x {i}) K, w ∈ Submodule.span (rA k x {i}) (S : Set _) → P * Algebra.trace F K (z * algebraMap F K s ^ (∑ g ∈ S, Nf g) * w) ∈ rA k x {i}`. Introduce `w hw`. Proceed by induction on `hw using Submodule.span_induction with`.

Consider the case `mem g hg`. Take `⟨m, hm⟩` from `Nat.exists_eq_add_of_le (Finset.single_le_sum (fun _ _ => Nat.zero_le _) hg)`. Establish `e : P * Algebra.trace F K (z * algebraMap F K s ^ (∑ g ∈ S, Nf g) * g) = s ^ m * (P * Algebra.trace F K (z * g) * s ^ Nf g)`. Rewrite using `[hm, mul_comm z, ← map_pow, mul_assoc, trace_algebraMap_mul]`. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[e]`. Conclude with `Subalgebra.mul_mem _ (Subalgebra.pow_mem _ hs1 _) (hNf g)`. Consider the case `zero => simp`. Consider the case `add a c _ _ ha hc`. Establish `e : ((a + c : integralClosure (rA k x {i}) K) : K) = a + c` using `rfl`.

Rewrite using `[e, mul_add, map_add, mul_add]`. Conclude with `add_mem ha hc`. Consider the case `smul r a _ ha`. Establish `e : ((r • a : integralClosure (rA k x {i}) K) : K) = algebraMap F K (r : F) * a`. Rewrite using `[SetLike.val_smul, Algebra.smul_def]`.

Both sides reduce to the same expression. Establish `e2 : P * Algebra.trace F K (z * algebraMap F K s ^ (∑ g ∈ S, Nf g) * (algebraMap F K (r : F) * a)) = (r : F) * (P * Algebra.trace F K (z * algebraMap F K s ^ (∑ g ∈ S, Nf g) * a))`. Rewrite using `[show z * algebraMap F K s ^ (∑ g ∈ S, Nf g) * (algebraMap F K (r : F) * a) = algebraMap F K (r : F) * (z * algebraMap F K s ^ (∑ g ∈ S, Nf g) * a) by ring, trace_algebraMap_mul]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e, e2]`.

Conclude with `Subalgebra.mul_mem _ r.2 ha`. Conclude with `key _ hb'`.
-/
theorem unif (k : Type) [Field k] [CharZero k] (F K : Type) [Field F] [Field K] [Algebra k F] [Algebra k K]
    [Algebra F K] [IsScalarTower k F K] (d : ℕ) (x : Fin (d + 1) → F) (hc : IsFinCover k K x)
    (I : Finset (Fin (d + 1))) (i : Fin (d + 1)) (hi : i ∈ I) (z : K)
    (h : ∀ b ∈ rB k K x I, Algebra.trace F K (z * b) ∈ omA k x I) :
    ∃ N : ℕ, ∀ b ∈ rB k K x {i},
      Algebra.trace F K (z * algebraMap F K (∏ j ∈ I, x j / x i) ^ N * b) ∈ omA k x {i} := by
  have hx := hc.pd.ne
  set s : F := ∏ j ∈ I, x j / x i with hs
  set P : F := ∏ j, x i / x j with hP
  have hs1 : s ∈ rA k x {i} :=
    Subalgebra.prod_mem _ fun j _ => Algebra.subset_adjoin ⟨i, Finset.mem_singleton_self _, j, rfl⟩
  have hle : rB k K x {i} ≤ rB k K x I :=
    (GlobalTheory.T.finite_cover_ring_localization_chart k F K d x hc {i} i (Finset.mem_singleton_self _)).1 I (Finset.singleton_subset_iff.2 hi)
  haveI : Module.Finite (rA k x {i}) (integralClosure (rA k x {i}) K) :=
    (GlobalTheory.T.finite_cover_chart_smooth_normal k F K d x hc {i} (Finset.singleton_nonempty _)).1
  obtain ⟨S, hS⟩ := Module.Finite.fg_top (R := rA k x {i}) (M := integralClosure (rA k x {i}) K)
  have hg : ∀ g : integralClosure (rA k x {i}) K, ∃ N : ℕ,
      P * Algebra.trace F K (z * g) * s ^ N ∈ rA k x {i} := by
    intro g
    have hgI : (g : K) ∈ rB k K x I := hle g.2
    exact (GlobalTheory.T.mem_standardOpenCoordinateRing_iff_localization_chart k F d x hc.pd I i hi _).1 ((mem_omA_iff hx hi _).1 (h _ hgI))
  choose Nf hNf using hg
  refine ⟨∑ g ∈ S, Nf g, fun b hb => ?_⟩
  rw [mem_omA_iff hx (Finset.mem_singleton_self i)]
  have hb' : (⟨b, hb⟩ : integralClosure (rA k x {i}) K) ∈ Submodule.span (rA k x {i}) (S : Set _) := by
    rw [hS]; trivial
  have key : ∀ w : integralClosure (rA k x {i}) K, w ∈ Submodule.span (rA k x {i}) (S : Set _) →
      P * Algebra.trace F K (z * algebraMap F K s ^ (∑ g ∈ S, Nf g) * w) ∈ rA k x {i} := by
    intro w hw
    induction hw using Submodule.span_induction with
    | mem g hg =>
      obtain ⟨m, hm⟩ := Nat.exists_eq_add_of_le (Finset.single_le_sum (fun _ _ => Nat.zero_le _) hg)
      have e : P * Algebra.trace F K (z * algebraMap F K s ^ (∑ g ∈ S, Nf g) * g) =
          s ^ m * (P * Algebra.trace F K (z * g) * s ^ Nf g) := by
        rw [hm, mul_comm z, ← map_pow, mul_assoc, trace_algebraMap_mul]; ring
      rw [e]
      exact Subalgebra.mul_mem _ (Subalgebra.pow_mem _ hs1 _) (hNf g)
    | zero => simp
    | add a c _ _ ha hc =>
      have e : ((a + c : integralClosure (rA k x {i}) K) : K) = a + c := rfl
      rw [e, mul_add, map_add, mul_add]
      exact add_mem ha hc
    | smul r a _ ha =>
      have e : ((r • a : integralClosure (rA k x {i}) K) : K) = algebraMap F K (r : F) * a := by
        rw [SetLike.val_smul, Algebra.smul_def]; rfl
      have e2 : P * Algebra.trace F K (z * algebraMap F K s ^ (∑ g ∈ S, Nf g) * (algebraMap F K (r : F) * a)) =
          (r : F) * (P * Algebra.trace F K (z * algebraMap F K s ^ (∑ g ∈ S, Nf g) * a)) := by
        rw [show z * algebraMap F K s ^ (∑ g ∈ S, Nf g) * (algebraMap F K (r : F) * a) =
          algebraMap F K (r : F) * (z * algebraMap F K s ^ (∑ g ∈ S, Nf g) * a) by ring, trace_algebraMap_mul]
        ring
      rw [e, e2]
      exact Subalgebra.mul_mem _ r.2 ha
  exact key _ hb'

/- English proof (translation)
Introduce `k _ _ F K _ _ _ _ _ _ d x hc τ hτ I hI z`. Take `⟨i, hi⟩` from `hI`. Establish `hx` using `hc.pd.ne`. Use `set s : F := ∏ j ∈ I, x j / x i with hs`. Establish `hsne : algebraMap F K s ≠ 0` using `(map_ne_zero _).2 (Finset.prod_ne_zero_iff.2 fun j _ => div_ne_zero (hx j) (hx i))`.

Prove the components needed by the constructor for the conclusion. Introduce `h`. Take `⟨N, hN⟩` from `unif k F K d x hc I i hi z h`. Take `⟨y', hy', hτy'⟩` from `(single k F K d x hc τ hτ i _).1 hN`. Use `⟨(algebraMap F K s ^ N)⁻¹ • y', (GlobalTheory.T.kahlerFormsOverSubalgebra_standardOpen_iff_pow_smul k F K d x hc I i hi d _).2 ⟨N, ?_⟩, ?_⟩` and prove the remaining obligations.

Rewrite using `[smul_smul, mul_inv_cancel₀ (pow_ne_zero _ hsne), one_smul]`. Conclude with `hy'`. Rewrite using `[map_smul, hτy', smul_eq_mul]`. Clear the denominators using the available nonvanishing facts. Conclude with `mul_comm _ _`.

Introduce and unpack `⟨y, hy, rfl⟩`. Take `⟨N, hN⟩` from `(GlobalTheory.T.kahlerFormsOverSubalgebra_standardOpen_iff_pow_smul k F K d x hc I i hi d y).1 hy`. Establish `h1` using `(single k F K d x hc τ hτ i _).2 ⟨_, hN, rfl⟩`. Introduce `b hb`. Take `⟨M, hM⟩` from `((GlobalTheory.T.finite_cover_ring_localization_chart k F K d x hc I i hi).2 b).1 hb`.

Establish `h2` using `(mem_omA_iff hx (Finset.mem_singleton_self i) _).1 (h1 _ hM)`. Rewrite using `[mem_omA_iff hx hi, GlobalTheory.T.mem_standardOpenCoordinateRing_iff_localization_chart k F d x hc.pd I i hi]`. Use `⟨N + M, ?_⟩` and prove the remaining obligations. Use `h2 using 1` and compare the differences between its conclusion and the goal. Rewrite using `[map_smul, smul_eq_mul, show algebraMap F K s ^ N * τ y * (b * algebraMap F K s ^ M) = algebraMap F K (s ^ (N + M)) * (τ y * b) by rw [map_pow, pow_add]; ring, trace_algebraMap_mul]`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem complementary_iff : ∀ (k : Type) [Field k] [CharZero k] (F K : Type) [Field F] [Field K] [Algebra k F] [Algebra k K] [Algebra F K] [IsScalarTower k F K] (d : ℕ) (x : Fin (d + 1) → F), IsFinCover k K x → ∀ (τ : DR k K →ₗ[K] K), IsTop k K x τ → ∀ I : Finset (Fin (d + 1)), I.Nonempty → ∀ z : K, (∀ b ∈ rB k K x I, Algebra.trace F K (z * b) ∈ omA k x I) ↔ ∃ y ∈ omB k K (rB k K x I) d, τ y = z := by
  intro k _ _ F K _ _ _ _ _ _ d x hc τ hτ I hI z
  obtain ⟨i, hi⟩ := hI
  have hx := hc.pd.ne
  set s : F := ∏ j ∈ I, x j / x i with hs
  have hsne : algebraMap F K s ≠ 0 :=
    (map_ne_zero _).2 (Finset.prod_ne_zero_iff.2 fun j _ => div_ne_zero (hx j) (hx i))
  constructor
  · intro h
    obtain ⟨N, hN⟩ := unif k F K d x hc I i hi z h
    obtain ⟨y', hy', hτy'⟩ := (single k F K d x hc τ hτ i _).1 hN
    refine ⟨(algebraMap F K s ^ N)⁻¹ • y', (GlobalTheory.T.kahlerFormsOverSubalgebra_standardOpen_iff_pow_smul k F K d x hc I i hi d _).2 ⟨N, ?_⟩, ?_⟩
    · rw [smul_smul, mul_inv_cancel₀ (pow_ne_zero _ hsne), one_smul]; exact hy'
    · rw [map_smul, hτy', smul_eq_mul]; field_simp; exact mul_comm _ _
  · rintro ⟨y, hy, rfl⟩
    obtain ⟨N, hN⟩ := (GlobalTheory.T.kahlerFormsOverSubalgebra_standardOpen_iff_pow_smul k F K d x hc I i hi d y).1 hy
    have h1 := (single k F K d x hc τ hτ i _).2 ⟨_, hN, rfl⟩
    intro b hb
    obtain ⟨M, hM⟩ := ((GlobalTheory.T.finite_cover_ring_localization_chart k F K d x hc I i hi).2 b).1 hb
    have h2 := (mem_omA_iff hx (Finset.mem_singleton_self i) _).1 (h1 _ hM)
    rw [mem_omA_iff hx hi, GlobalTheory.T.mem_standardOpenCoordinateRing_iff_localization_chart k F d x hc.pd I i hi]
    refine ⟨N + M, ?_⟩
    convert h2 using 1
    rw [map_smul, smul_eq_mul, show algebraMap F K s ^ N * τ y * (b * algebraMap F K s ^ M) =
      algebraMap F K (s ^ (N + M)) * (τ y * b) by rw [map_pow, pow_add]; ring, trace_algebraMap_mul]
    ring

end GlobalTheory.ComplStd

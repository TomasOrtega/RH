import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.DlogRatioVolumeFormNeZero

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.PD.Model

open GlobalTheory.PD

variable (k : Type) [Field k] (d : ℕ)

abbrev Fd : Type := FractionRing (MvPolynomial (Fin d) k)

def xs : Fin (d + 1) → Fd k d := Fin.cons 1 fun j => algebraMap (MvPolynomial (Fin d) k) _ (MvPolynomial.X j)

/- English proof (translation)
Use `Fin.cases ?_ (fun j => ?_) i` and prove the remaining obligations. Simplify using `[xs]`. Simplify using `only [xs, Fin.cons_succ, ne_eq]`. Rewrite using `[map_eq_zero_iff _ (IsFractionRing.injective (MvPolynomial (Fin d) k) (Fd k d))]`. Conclude with `MvPolynomial.X_ne_zero j`.
-/
theorem xs_ne (i : Fin (d + 1)) : xs k d i ≠ 0 := by
  refine Fin.cases ?_ (fun j => ?_) i
  · simp [xs]
  · simp only [xs, Fin.cons_succ, ne_eq]
    rw [map_eq_zero_iff _ (IsFractionRing.injective (MvPolynomial (Fin d) k) (Fd k d))]
    exact MvPolynomial.X_ne_zero j

/- English proof (translation)
The claim follows from `xs_ne k d indep := by have h : (fun j : Fin d => xs k d j.succ / xs k d 0) = (IsScalarTower.toAlgHom k (MvPolynomial (Fin d) k) (Fd k d)) ∘ MvPolynomial.X := by funext j simp [xs] rw [h] exact (MvPolynomial.algebraicIndependent_X (Fin d) k).map' (IsFractionRing.injective _ _) gen …`.
-/
theorem isPd_xs : IsPd k (xs k d) where
  ne := xs_ne k d
  indep := by

    have h : (fun j : Fin d => xs k d j.succ / xs k d 0) =
        (IsScalarTower.toAlgHom k (MvPolynomial (Fin d) k) (Fd k d)) ∘ MvPolynomial.X := by
      funext j
      simp [xs]
    rw [h]
    exact (MvPolynomial.algebraicIndependent_X (Fin d) k).map' (IsFractionRing.injective _ _)
  gen := by
    rw [eq_top_iff]
    intro z _

    have key : ∀ p : MvPolynomial (Fin d) k, algebraMap _ (Fd k d) p ∈
        IntermediateField.adjoin k (Set.range fun j : Fin d => xs k d j.succ / xs k d 0) := by
      intro p
      induction p using MvPolynomial.induction_on with
      | C a =>
        have e : algebraMap (MvPolynomial (Fin d) k) (Fd k d) (MvPolynomial.C a) = algebraMap k (Fd k d) a := by
          rw [IsScalarTower.algebraMap_apply k (MvPolynomial (Fin d) k) (Fd k d), MvPolynomial.algebraMap_eq]
        rw [e]
        exact IntermediateField.algebraMap_mem _ a
      | add p q hp hq =>
        rw [map_add]
        exact add_mem hp hq
      | mul_X p n hp =>
        rw [map_mul]
        refine mul_mem hp (IntermediateField.subset_adjoin _ _ ⟨n, ?_⟩)
        simp [xs]
    obtain ⟨a, b, _, rfl⟩ := IsFractionRing.div_surjective (A := MvPolynomial (Fin d) k) z
    exact div_mem (key a) (key b)

section Bundle

variable (k : Type) [Field k] {F : Type} [Field F] [Algebra k F] {d : ℕ} (x : Fin (d + 1) → F)

/- English proof (translation)
Break down `m with n | n` into its components or cases. Rewrite using `[Int.ofNat_eq_natCast, zpow_natCast]`. Conclude with `pow_mem ha n`. Rewrite using `[zpow_negSucc, ← inv_pow]`. Conclude with `pow_mem ha' _`.
-/
theorem zpow_mem_of_inv {S : Subalgebra k F} {a : F} (ha : a ∈ S) (ha' : a⁻¹ ∈ S) (m : ℤ) : a ^ m ∈ S := by
  rcases m with n | n
  · rw [Int.ofNat_eq_natCast, zpow_natCast]
    exact pow_mem ha n
  · rw [zpow_negSucc, ← inv_pow]
    exact pow_mem ha' _

/- English proof (translation)
Unfold `rA`. Conclude with `Algebra.subset_adjoin ⟨i, hi, j, rfl⟩`.
-/
theorem ratio_mem {I : Finset (Fin (d + 1))} {i : Fin (d + 1)} (hi : i ∈ I) (j : Fin (d + 1)) : x j / x i ∈ rA k x I := by
  unfold rA
  exact Algebra.subset_adjoin ⟨i, hi, j, rfl⟩

/- English proof (translation)
Unfold `rA`. Conclude with `Algebra.adjoin_mono fun y ⟨i, hi, j, hj⟩ => ⟨i, h hi, j, hj⟩`.
-/
theorem rA_mono {I J : Finset (Fin (d + 1))} (h : I ⊆ J) : rA k x I ≤ rA k x J := by
  unfold rA
  exact Algebra.adjoin_mono fun y ⟨i, hi, j, hj⟩ => ⟨i, h hi, j, hj⟩

/- English proof (translation)
Simplify using `only [tw, Submodule.mem_iInf, Submodule.mem_comap, LinearMap.mulLeft_apply, Subalgebra.mem_toSubmodule]`. Use `⟨fun h => h i hi, fun h i' hi' => ?_⟩` and prove the remaining obligations. Establish `key : x i / x i' * (x 0 / x i) = x 0 / x i'`. Rewrite using `[div_mul_div_comm, mul_comm (x i) (x 0), mul_div_mul_right _ _ (hx i)]`. Establish `e : (x 0 / x i') ^ m * f = (x i / x i') ^ m * ((x 0 / x i) ^ m * f)`.

Rewrite using `[← mul_assoc, ← mul_zpow, key]`. Rewrite using `[e]`. Use `mul_mem (zpow_mem_of_inv k (ratio_mem k x hi' i) ?_ m) h` and prove the remaining obligations. Rewrite using `[inv_div]`. Conclude with `ratio_mem k x hi i'`.
-/
theorem mem_tw_iff (hx : ∀ i, x i ≠ 0) (m : ℤ) {I : Finset (Fin (d + 1))} {i : Fin (d + 1)} (hi : i ∈ I) (f : F) :
    f ∈ tw k x m I ↔ (x 0 / x i) ^ m * f ∈ rA k x I := by
  simp only [tw, Submodule.mem_iInf, Submodule.mem_comap, LinearMap.mulLeft_apply, Subalgebra.mem_toSubmodule]
  refine ⟨fun h => h i hi, fun h i' hi' => ?_⟩

  have key : x i / x i' * (x 0 / x i) = x 0 / x i' := by
    rw [div_mul_div_comm, mul_comm (x i) (x 0), mul_div_mul_right _ _ (hx i)]
  have e : (x 0 / x i') ^ m * f = (x i / x i') ^ m * ((x 0 / x i) ^ m * f) := by
    rw [← mul_assoc, ← mul_zpow, key]
  rw [e]
  refine mul_mem (zpow_mem_of_inv k (ratio_mem k x hi' i) ?_ m) h
  rw [inv_div]
  exact ratio_mem k x hi i'

/- English proof (translation)
Establish `h1 : (x 0 / x i) ^ m * (x i / x 0) ^ m = 1`. Rewrite using `[← mul_zpow, div_mul_div_comm, mul_comm (x 0) (x i), div_self (mul_ne_zero (hx i) (hx 0)), one_zpow]`. Use extensionality with `f`. Rewrite using `[mem_tw_iff k x hx m hi, Submodule.restrictScalars_mem, Submodule.mem_span_singleton]`. Prove the components needed by the constructor for the conclusion.

Introduce `h`. Use `⟨⟨_, h⟩, ?_⟩` and prove the remaining obligations. Rewrite using `[Subalgebra.smul_def, smul_eq_mul]`. Express the relevant statement in the definitionally equal form `(x 0 / x i) ^ m * f * (x i / x 0) ^ m = f`. Rewrite using `[mul_right_comm, h1, one_mul]`.

Introduce and unpack `⟨r, rfl⟩`. Rewrite using `[Subalgebra.smul_def, smul_eq_mul, mul_left_comm, h1, mul_one]`. Conclude with `r.2`.
-/
theorem tw_eq_span (hx : ∀ i, x i ≠ 0) (m : ℤ) {I : Finset (Fin (d + 1))} {i : Fin (d + 1)} (hi : i ∈ I) :
    tw k x m I = (Submodule.span (rA k x I) {(x i / x 0) ^ m}).restrictScalars k := by
  have h1 : (x 0 / x i) ^ m * (x i / x 0) ^ m = 1 := by
    rw [← mul_zpow, div_mul_div_comm, mul_comm (x 0) (x i), div_self (mul_ne_zero (hx i) (hx 0)), one_zpow]
  ext f
  rw [mem_tw_iff k x hx m hi, Submodule.restrictScalars_mem, Submodule.mem_span_singleton]
  constructor
  · intro h
    refine ⟨⟨_, h⟩, ?_⟩
    rw [Subalgebra.smul_def, smul_eq_mul]
    change (x 0 / x i) ^ m * f * (x i / x 0) ^ m = f
    rw [mul_right_comm, h1, one_mul]
  · rintro ⟨r, rfl⟩
    rw [Subalgebra.smul_def, smul_eq_mul, mul_left_comm, h1, mul_one]
    exact r.2

/- English proof (translation)
Use `⟨{(x i / x 0) ^ m}, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[Finset.coe_singleton]`. Conclude with `tw_eq_span k x hx m (Finset.mem_singleton_self i)`. Rewrite using `[Finset.coe_singleton]`. Conclude with `Ideal.span_singleton_eq_top.2 (isUnit_iff_ne_zero.2 (zpow_ne_zero _ (div_ne_zero (hx i) (hx 0))))`.

Use `proj i := by`. Establish `hg : (x i / x 0) ^ m ≠ 0` using `zpow_ne_zero _ (div_ne_zero (hx i) (hx 0))`. Establish `e : Submodule.span (rA k x {i}) (tw k x m {i} : Set F) = Submodule.span (rA k x {i}) {(x i / x 0) ^ m}`. Rewrite using `[tw_eq_span k x hx m (Finset.mem_singleton_self i), Submodule.coe_restrictScalars, Submodule.span_eq]`. Rewrite using `[e]`.

Establish `hli : LinearIndependent (rA k x {i}) (fun _ : Unit => (x i / x 0) ^ m)`. Rewrite using `[linearIndependent_unique_iff]`. Conclude with `hg`. Establish `hr : Set.range (fun _ : Unit => (x i / x 0) ^ m) = {(x i / x 0) ^ m}` using `Set.range_const`. Rewrite using `[← hr]`.

Use `Module.Free.of_basis (Module.Basis.span hli)` as an intermediate fact. Use `infer_instance`. Use `loc I i hi := by`. Rewrite using `[tw_eq_span k x hx m hi, tw_eq_span k x hx m (Finset.mem_singleton_self i), Submodule.restrictScalars_inj]`. Apply `le_antisymm` to reduce the goal to its premises.

Rewrite using `[Submodule.span_le]`. Introduce and unpack `_ rfl`. Conclude with `Submodule.subset_span (Submodule.mem_span_singleton_self _)`. Rewrite using `[Submodule.span_le]`. Introduce `y hy`.

Rewrite `hy` using `[SetLike.mem_coe, Submodule.restrictScalars_mem, Submodule.mem_span_singleton]`. Take `⟨r, rfl⟩` from `hy`. Rewrite using `[SetLike.mem_coe, Submodule.mem_span_singleton]`. Conclude with `⟨⟨r, rA_mono k x (Finset.singleton_subset_iff.2 hi) r.2⟩, rfl⟩`.
-/
theorem isBundle_tw (hx : ∀ i, x i ≠ 0) (m : ℤ) : IsBundle k x (tw k x m) where
  fg i := by
    refine ⟨{(x i / x 0) ^ m}, ?_, ?_⟩
    · rw [Finset.coe_singleton]
      exact tw_eq_span k x hx m (Finset.mem_singleton_self i)
    · rw [Finset.coe_singleton]
      exact Ideal.span_singleton_eq_top.2 (isUnit_iff_ne_zero.2 (zpow_ne_zero _ (div_ne_zero (hx i) (hx 0))))
  proj i := by

    have hg : (x i / x 0) ^ m ≠ 0 := zpow_ne_zero _ (div_ne_zero (hx i) (hx 0))
    have e : Submodule.span (rA k x {i}) (tw k x m {i} : Set F) =
        Submodule.span (rA k x {i}) {(x i / x 0) ^ m} := by
      rw [tw_eq_span k x hx m (Finset.mem_singleton_self i), Submodule.coe_restrictScalars, Submodule.span_eq]
    rw [e]
    have hli : LinearIndependent (rA k x {i}) (fun _ : Unit => (x i / x 0) ^ m) := by
      rw [linearIndependent_unique_iff]
      exact hg
    have hr : Set.range (fun _ : Unit => (x i / x 0) ^ m) = {(x i / x 0) ^ m} := Set.range_const
    rw [← hr]
    have := Module.Free.of_basis (Module.Basis.span hli)
    infer_instance
  loc I i hi := by
    rw [tw_eq_span k x hx m hi, tw_eq_span k x hx m (Finset.mem_singleton_self i), Submodule.restrictScalars_inj]
    apply le_antisymm
    · rw [Submodule.span_le]
      rintro _ rfl
      exact Submodule.subset_span (Submodule.mem_span_singleton_self _)
    · rw [Submodule.span_le]
      intro y hy
      rw [SetLike.mem_coe, Submodule.restrictScalars_mem, Submodule.mem_span_singleton] at hy
      obtain ⟨r, rfl⟩ := hy
      rw [SetLike.mem_coe, Submodule.mem_span_singleton]
      exact ⟨⟨r, rA_mono k x (Finset.singleton_subset_iff.2 hi) r.2⟩, rfl⟩

end Bundle

section Cover

variable (k : Type) [Field k] {F : Type} [Field F] [Algebra k F] {d : ℕ} (x : Fin (d + 1) → F)

def yc (i : Fin (d + 1)) : Fin d → F := fun j => x (i.succAbove j) / x i

/- English proof (translation)
Use `IsFractionRing.of_field (Algebra.adjoin k S) F fun z => ?_` and prove the remaining obligations. Establish `hz : z ∈ IntermediateField.adjoin k S` using `h ▸ IntermediateField.mem_top`. Take `⟨r, hr, s, hs, rfl⟩` from `IntermediateField.mem_adjoin_iff_div.1 hz`. Conclude with `⟨⟨r, hr⟩, ⟨s, hs⟩, rfl⟩`.
-/
theorem isFrac_of_adjoin_eq_top (S : Set F) (h : IntermediateField.adjoin k S = ⊤) :
    IsFractionRing (Algebra.adjoin k S) F := by
  refine IsFractionRing.of_field (Algebra.adjoin k S) F fun z => ?_
  have hz : z ∈ IntermediateField.adjoin k S := h ▸ IntermediateField.mem_top
  obtain ⟨r, hr, s, hs, rfl⟩ := IntermediateField.mem_adjoin_iff_div.1 hz
  exact ⟨⟨r, hr⟩, ⟨s, hs⟩, rfl⟩

/- English proof (translation)
Break down `eq_or_ne a i with rfl | h` into its components or cases. Rewrite using `[div_self (hx a)]`. Conclude with `IntermediateField.one_mem _`. Take `⟨j, rfl⟩` from `Fin.exists_succAbove_eq h`. Conclude with `IntermediateField.subset_adjoin _ _ ⟨j, rfl⟩`.
-/
theorem ratio_mem_field (hx : ∀ i, x i ≠ 0) (i a : Fin (d + 1)) :
    x a / x i ∈ IntermediateField.adjoin k (Set.range (yc x i)) := by
  rcases eq_or_ne a i with rfl | h
  · rw [div_self (hx a)]
    exact IntermediateField.one_mem _
  · obtain ⟨j, rfl⟩ := Fin.exists_succAbove_eq h
    exact IntermediateField.subset_adjoin _ _ ⟨j, rfl⟩

/- English proof (translation)
Rewrite using `[eq_top_iff, ← hP.gen, IntermediateField.adjoin_le_iff]`. Introduce and unpack `_ ⟨j, rfl⟩`. Use `show x j.succ / x 0 ∈ IntermediateField.adjoin k (Set.range (yc x i))`. Establish `e : x j.succ / x 0 = (x j.succ / x i) / (x 0 / x i)`. Rewrite using `[div_div_div_cancel_right₀ (hP.ne i)]`.

Rewrite using `[e]`. Conclude with `div_mem (ratio_mem_field k x hP.ne i _) (ratio_mem_field k x hP.ne i _)`.
-/
theorem adjoin_yc_eq_top (hP : IsPd k x) (i : Fin (d + 1)) :
    IntermediateField.adjoin k (Set.range (yc x i)) = ⊤ := by
  rw [eq_top_iff, ← hP.gen, IntermediateField.adjoin_le_iff]
  rintro _ ⟨j, rfl⟩
  show x j.succ / x 0 ∈ IntermediateField.adjoin k (Set.range (yc x i))

  have e : x j.succ / x 0 = (x j.succ / x i) / (x 0 / x i) := by
    rw [div_div_div_cancel_right₀ (hP.ne i)]
  rw [e]
  exact div_mem (ratio_mem_field k x hP.ne i _) (ratio_mem_field k x hP.ne i _)

/- English proof (translation)
Conclude with `hP.indep.cardinalMk_le_trdeg`.
-/
theorem trdeg_eq (hP : IsPd k x) : Cardinal.mk (Fin d) ≤ Algebra.trdeg k F := by
  exact hP.indep.cardinalMk_le_trdeg

/- English proof (translation)
Establish `: IsFractionRing (Algebra.adjoin k (Set.range (yc x i))) F` using `isFrac_of_adjoin_eq_top k _ (adjoin_yc_eq_top k x hP i)`. Establish `: Algebra.IsAlgebraic (Algebra.adjoin k (Set.range (yc x i))) F` using `IsLocalization.isAlgebraic F (nonZeroDivisors (Algebra.adjoin k (Set.range (yc x i))))`. Conclude with `(Algebra.IsAlgebraic.isTranscendenceBasis_of_le_trdeg_of_finite k (yc x i) (trdeg_eq k x hP)).1`.
-/
theorem indep_yc (hP : IsPd k x) (i : Fin (d + 1)) : AlgebraicIndependent k (yc x i) := by

  have : IsFractionRing (Algebra.adjoin k (Set.range (yc x i))) F :=
    isFrac_of_adjoin_eq_top k _ (adjoin_yc_eq_top k x hP i)
  have : Algebra.IsAlgebraic (Algebra.adjoin k (Set.range (yc x i))) F :=
    IsLocalization.isAlgebraic F (nonZeroDivisors (Algebra.adjoin k (Set.range (yc x i))))
  exact (Algebra.IsAlgebraic.isTranscendenceBasis_of_le_trdeg_of_finite k (yc x i) (trdeg_eq k x hP)).1

/- English proof (translation)
Unfold `rA`. Apply `le_antisymm` to reduce the goal to its premises. Rewrite using `[Algebra.adjoin_le_iff]`. Introduce and unpack `_ ⟨i', hi', j, rfl⟩`. Rewrite `hi'` using `[Finset.mem_singleton]`.

Substitute `hi'` using the available equality. Break down `eq_or_ne j i' with rfl | h` into its components or cases. Rewrite using `[div_self (hx j)]`. Conclude with `Subalgebra.one_mem _`. Take `⟨l, rfl⟩` from `Fin.exists_succAbove_eq h`.

Conclude with `Algebra.subset_adjoin ⟨l, rfl⟩`. Rewrite using `[Algebra.adjoin_le_iff]`. Introduce and unpack `_ ⟨j, rfl⟩`. Conclude with `Algebra.subset_adjoin ⟨i, Finset.mem_singleton_self i, i.succAbove j, rfl⟩`.
-/
theorem rA_single_eq (hx : ∀ i, x i ≠ 0) (i : Fin (d + 1)) :
    rA k x {i} = Algebra.adjoin k (Set.range (yc x i)) := by
  unfold rA
  apply le_antisymm
  · rw [Algebra.adjoin_le_iff]
    rintro _ ⟨i', hi', j, rfl⟩
    rw [Finset.mem_singleton] at hi'
    subst hi'
    rcases eq_or_ne j i' with rfl | h
    · rw [div_self (hx j)]
      exact Subalgebra.one_mem _
    · obtain ⟨l, rfl⟩ := Fin.exists_succAbove_eq h
      exact Algebra.subset_adjoin ⟨l, rfl⟩
  · rw [Algebra.adjoin_le_iff]
    rintro _ ⟨j, rfl⟩
    exact Algebra.subset_adjoin ⟨i, Finset.mem_singleton_self i, i.succAbove j, rfl⟩

def chartEquiv (hP : IsPd k x) (i : Fin (d + 1)) : MvPolynomial (Fin d) k ≃ₐ[k] rA k x {i} :=
  (indep_yc k x hP i).aevalEquiv.trans (Subalgebra.equivOfEq _ _ (rA_single_eq k x hP.ne i).symm)

/- English proof (translation)
Rewrite using `[rA_single_eq k x hP.ne i]`. Conclude with `isFrac_of_adjoin_eq_top k _ (adjoin_yc_eq_top k x hP i)`.
-/
theorem isFrac_rA (hP : IsPd k x) (i : Fin (d + 1)) : IsFractionRing (rA k x {i}) F := by
  rw [rA_single_eq k x hP.ne i]
  exact isFrac_of_adjoin_eq_top k _ (adjoin_yc_eq_top k x hP i)

/- English proof (translation)
Establish `: IsFractionRing (rA k x {i}) F` using `isFrac_rA k x hP i`. Establish `: IsIntegrallyClosed (rA k x {i})` using `IsIntegrallyClosed.of_equiv (chartEquiv k x hP i).toRingEquiv`. Use extensionality with `z`. Simplify using `only [rB, Subalgebra.mem_restrictScalars, IsIntegrallyClosed.integralClosure_eq_bot, Algebra.mem_bot]`. Prove the components needed by the constructor for the conclusion.

Introduce and unpack `⟨r, rfl⟩`. Conclude with `r.2`. Introduce `hz`. Conclude with `⟨⟨z, hz⟩, rfl⟩`.
-/
theorem rB_self_eq (hP : IsPd k x) (i : Fin (d + 1)) : rB k F x {i} = rA k x {i} := by

  have : IsFractionRing (rA k x {i}) F := isFrac_rA k x hP i
  have : IsIntegrallyClosed (rA k x {i}) := IsIntegrallyClosed.of_equiv (chartEquiv k x hP i).toRingEquiv
  ext z
  simp only [rB, Subalgebra.mem_restrictScalars, IsIntegrallyClosed.integralClosure_eq_bot, Algebra.mem_bot]
  constructor
  · rintro ⟨r, rfl⟩
    exact r.2
  · intro hz
    exact ⟨⟨z, hz⟩, rfl⟩

/- English proof (translation)
Establish `: Algebra.Smooth k (MvPolynomial (Fin d) k)` using `⟨inferInstance, inferInstance⟩`. Conclude with `Algebra.Smooth.of_equiv (chartEquiv k x hP i)`.
-/
theorem smooth_chart (hP : IsPd k x) (i : Fin (d + 1)) : Algebra.Smooth k (rA k x {i}) := by
  have : Algebra.Smooth k (MvPolynomial (Fin d) k) := ⟨inferInstance, inferInstance⟩
  exact Algebra.Smooth.of_equiv (chartEquiv k x hP i)

/- English proof (translation)
The claim follows from `hP fin := inferInstance smooth i := by rw [rB_self_eq k x hP i] exact smooth_chart k x hP i sep := inferInstance`.
-/
theorem isFinCover_self (hP : IsPd k x) : IsFinCover k F x where
  pd := hP
  fin := inferInstance
  smooth i := by
    rw [rB_self_eq k x hP i]
    exact smooth_chart k x hP i
  sep := inferInstance

end Cover

/- English proof (translation)
Assemble the required witnesses or components as `⟨isPd_xs k d, isFinCover_self k (xs k d) (isPd_xs k d), fun m => isBundle_tw k (xs k d) (xs_ne k d) m⟩`.
-/
theorem model (k : Type) [Field k] (d : ℕ) :
    IsPd k (xs k d) ∧ IsFinCover k (Fd k d) (xs k d) ∧ ∀ m : ℤ, IsBundle k (xs k d) (tw k (xs k d) m) :=
  ⟨isPd_xs k d, isFinCover_self k (xs k d) (isPd_xs k d), fun m => isBundle_tw k (xs k d) (xs_ne k d) m⟩

section Extra

/- English proof (translation)
Use `{ pd := ?_, fin := inferInstance, smooth := fun i => ?_, sep := inferInstance }` and prove the remaining obligations. Conclude with `{ ne := fun _ => one_ne_zero indep := algebraicIndependent_empty_type gen := by`. Rewrite using `[eq_top_iff]`. Introduce `z _`. Conclude with `IntermediateField.algebraMap_mem _ z }`.

Establish `htop : rB ℝ ℂ (fun _ : Fin 1 => (1 : ℝ)) {i} = ⊤`. Rewrite using `[eq_top_iff]`. Introduce `z _`. Rewrite using `[rB, Subalgebra.mem_restrictScalars, mem_integralClosure_iff]`. Conclude with `(Algebra.IsIntegral.isIntegral (R := ℝ) z).tower_top`.

Rewrite using `[htop]`. Establish `: Algebra.FormallyEtale ℝ ℂ` using `Algebra.FormallyEtale.of_isSeparable ℝ ℂ`. Establish `: Algebra.FinitePresentation ℝ ℂ` using `Algebra.FinitePresentation.of_finiteType.1 inferInstance`. Establish `: Algebra.Smooth ℝ ℂ` using `⟨inferInstance, inferInstance⟩`. Conclude with `Algebra.Smooth.of_equiv Subalgebra.topEquiv.symm`.
-/
theorem isFinCover_complex : IsFinCover ℝ ℂ (F := ℝ) (d := 0) (fun _ => (1 : ℝ)) := by
  refine { pd := ?_, fin := inferInstance, smooth := fun i => ?_, sep := inferInstance }
  · exact
      { ne := fun _ => one_ne_zero
        indep := algebraicIndependent_empty_type
        gen := by
          rw [eq_top_iff]
          intro z _
          exact IntermediateField.algebraMap_mem _ z }
  ·
    have htop : rB ℝ ℂ (fun _ : Fin 1 => (1 : ℝ)) {i} = ⊤ := by
      rw [eq_top_iff]
      intro z _
      rw [rB, Subalgebra.mem_restrictScalars, mem_integralClosure_iff]
      exact (Algebra.IsIntegral.isIntegral (R := ℝ) z).tower_top
    rw [htop]
    have : Algebra.FormallyEtale ℝ ℂ := Algebra.FormallyEtale.of_isSeparable ℝ ℂ
    have : Algebra.FinitePresentation ℝ ℂ := Algebra.FinitePresentation.of_finiteType.1 inferInstance
    have : Algebra.Smooth ℝ ℂ := ⟨inferInstance, inferInstance⟩
    exact Algebra.Smooth.of_equiv Subalgebra.topEquiv.symm

/- English proof (translation)
Establish `hprod : ∀ a : F, ∏ j, a / x j = a ^ (d + 1) / ∏ j, x j`. Introduce `a`. Rewrite using `[Finset.prod_div_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]`. Simplify using `only [omA, tw, Submodule.mem_iInf, Submodule.mem_comap, LinearMap.mulLeft_apply, Subalgebra.mem_toSubmodule]`. Use `forall₂_congr fun i _ => ?_` and prove the remaining obligations.

Establish `e : (x 0 / x i) ^ (-((d : ℤ) + 1)) * ((∏ j, x 0 / x j) * f) = (∏ j, x i / x j) * f`. Rewrite using `[hprod, hprod, show (-((d : ℤ) + 1)) = -((d + 1 : ℕ) : ℤ) by omega, zpow_neg, zpow_natCast, ← inv_pow, inv_div, ← mul_assoc]`. Use `congr 1`. Rewrite using `[div_pow, div_mul_div_comm, mul_comm (x 0 ^ (d + 1)) (∏ j, x j), mul_div_mul_right _ _ (pow_ne_zero _ (hx 0))]`. Rewrite using `[e]`.
-/
theorem mem_omA_iff_tw {k F : Type} [Field k] [Field F] [Algebra k F] {d : ℕ} (x : Fin (d + 1) → F)
    (hx : ∀ i, x i ≠ 0) (I : Finset (Fin (d + 1))) (f : F) :
    f ∈ omA k x I ↔ (∏ j, x 0 / x j) * f ∈ tw k x (-((d : ℤ) + 1)) I := by
  have hprod : ∀ a : F, ∏ j, a / x j = a ^ (d + 1) / ∏ j, x j := by
    intro a
    rw [Finset.prod_div_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  simp only [omA, tw, Submodule.mem_iInf, Submodule.mem_comap, LinearMap.mulLeft_apply, Subalgebra.mem_toSubmodule]
  refine forall₂_congr fun i _ => ?_

  have e : (x 0 / x i) ^ (-((d : ℤ) + 1)) * ((∏ j, x 0 / x j) * f) = (∏ j, x i / x j) * f := by
    rw [hprod, hprod, show (-((d : ℤ) + 1)) = -((d + 1 : ℕ) : ℤ) by omega, zpow_neg, zpow_natCast, ← inv_pow,
      inv_div, ← mul_assoc]
    congr 1
    rw [div_pow, div_mul_div_comm, mul_comm (x 0 ^ (d + 1)) (∏ j, x j), mul_div_mul_right _ _ (pow_ne_zero _ (hx 0))]
  rw [e]

/- English proof (translation)
Simplify using `[formPair, cup, map_sum]`.
-/
theorem formPair_eq_cup {k K : Type} [Field k] [Field K] [Algebra k K] {ι : Type} [LinearOrder ι] [Fintype ι]
    (t : GlobalTheory.CechDR.DR k K →ₗ[k] k) (a b : Finset ι → GlobalTheory.CechDR.DR k K) :
    formPair k t a b = t (cup (sg k K) a b Finset.univ) := by
  simp [formPair, cup, map_sum]

end Extra

end GlobalTheory.PD.Model

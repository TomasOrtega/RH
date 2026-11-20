import Mathlib
import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.Statements
import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.PGradedFinite
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.FieldNumbers

open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR

noncomputable section

universe u

section Point

variable {F : Type u} [Field F] {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type}
  [∀ k, Fintype (ι k)]

def blockMonomial (i : ∀ k, ι k) (m : K → ℕ) : MRing ι F :=
  ∏ k, X ⟨k, i k⟩ ^ m k

omit [∀ k, Fintype (ι k)] in

/- English proof (translation)
Establish `h` using `IsWeightedHomogeneous.prod (R := F) (w := blockWeight ι) Finset.univ (fun k => (X ⟨k, i k⟩ : MRing ι F) ^ m k) (fun k => m k • blockWeight ι ⟨k, i k⟩) (fun k _ => (isWeightedHomogeneous_X F (blockWeight ι) ⟨k, i k⟩).pow (m k))`. Establish `hm : (∑ k, m k • blockWeight ι ⟨k, i k⟩) = m`. Use function extensionality and compare the values at `k'`. Simplify using `[blockWeight, Finset.sum_apply, Pi.single_apply]`. Rewrite `h` using `[hm]`.

Conclude with `h`.
-/
theorem blockMonomial_isMultiHomog (i : ∀ k, ι k) (m : K → ℕ) :
    IsMultiHomog (blockMonomial (F := F) i m) m := by
  have h := IsWeightedHomogeneous.prod (R := F) (w := blockWeight ι) Finset.univ
    (fun k => (X ⟨k, i k⟩ : MRing ι F) ^ m k) (fun k => m k • blockWeight ι ⟨k, i k⟩)
    (fun k _ => (isWeightedHomogeneous_X F (blockWeight ι) ⟨k, i k⟩).pow (m k))
  have hm : (∑ k, m k • blockWeight ι ⟨k, i k⟩) = m := by
    funext k'
    simp [blockWeight, Finset.sum_apply, Pi.single_apply]
  rw [hm] at h
  exact h

omit [DecidableEq K] [∀ k, Fintype (ι k)] in

/- English proof (translation)
Simplify using `[blockMonomial, pow_add, Finset.prod_mul_distrib]`.
-/
theorem blockMonomial_add (i : ∀ k, ι k) (m n : K → ℕ) :
    blockMonomial (F := F) i (m + n) = blockMonomial i m * blockMonomial i n := by
  simp [blockMonomial, pow_add, Finset.prod_mul_distrib]

omit [DecidableEq K] [∀ k, Fintype (ι k)] in

/- English proof (translation)
Unfold `blockMonomial`. Rewrite using `[map_prod, Finset.prod_ne_zero_iff]`. Introduce `k _`. Rewrite using `[map_pow]`. Use `pow_ne_zero _ ?_` and prove the remaining obligations.

Rewrite using `[Ne, Ideal.Quotient.eq_zero_iff_mem]`. Conclude with `hi k`.
-/
theorem blockMonomial_mk_ne_zero (P : Ideal (MRing ι F)) [P.IsPrime] (i : ∀ k, ι k)
    (hi : ∀ k, (X ⟨k, i k⟩ : MRing ι F) ∉ P) (m : K → ℕ) :
    Ideal.Quotient.mk P (blockMonomial i m) ≠ 0 := by
  unfold blockMonomial
  rw [map_prod, Finset.prod_ne_zero_iff]
  intro k _
  rw [map_pow]
  refine pow_ne_zero _ ?_
  rw [Ne, Ideal.Quotient.eq_zero_iff_mem]
  exact hi k

end Point

/- English proof (translation)
Introduce `F _ K _ _ ι _ P hP hrel`. Use `hP.isPrime` as an intermediate fact. Establish `hev : ∀ᶠ m in Filter.atTop, hilbFn P m = intNum F P (n` using `0) ![] := by`. Establish `h0 : relDim P = ((0 : ℕ) : WithBot (WithTop ℤ))` using `by rw [hrel]; rfl`. Use `filter_upwards [(h1 F K ι P hP.multiHomog hP.relevant 0 h0).1 ![]] with m hm`.

Simplify `hm` using `[mixedDiff]`. Use `set c := intNum F P (n := 0) ![] with hc`. Take `⟨M0, hM0⟩` from `Filter.eventually_atTop.mp hev`. Use `choose i hi using hP.relevant`. Use `set A := MRing ι F ⧸ P`.

Use `set L := FractionRing A`. Set `xm : (K → ℕ) → L` to `fun m => algebraMap A L (Ideal.Quotient.mk P (blockMonomial i m))`. Establish `hxm : ∀ m, xm m ≠ 0` using `fun m => by`. Simplify using `only [xm, ne_eq, FaithfulSMul.algebraMap_eq_zero_iff]`. Conclude with `blockMonomial_mk_ne_zero P i hi m`.

Establish `hxm_add : ∀ m n, xm (m + n) = xm m * xm n` using `fun m n => by`. Simplify using `only [xm, blockMonomial_add, map_mul]`. Set `φ : (K → ℕ) → A →ₗ[F] L` to `fun m => (LinearMap.mulRight F (xm m)⁻¹).comp (IsScalarTower.toAlgHom F A L).toLinearMap`. Establish `hφ : ∀ m a, φ m a = algebraMap A L a / xm m` using `fun m a => by`. Simplify using `[φ, div_eq_mul_inv]`.

Establish `hφinj : ∀ m, Function.Injective (φ m)` using `fun m a b hab => by`. Rewrite `hab` using `[hφ, hφ, div_left_inj' (hxm m)]`. Conclude with `IsFractionRing.injective A L hab`. Set `U : (K → ℕ) → Submodule F L` to `fun m => (gradedPiece P m).map (φ m)`. Establish `memU : ∀ m y, y ∈ U m ↔ ∃ f : MRing ι F, IsMultiHomog f m ∧ y = algebraMap A L (Ideal.Quotient.mk P f) / xm m` using `fun m y => by`.

Simplify using `only [U, gradedPiece, Submodule.mem_map, hφ]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨a, ⟨f, hf, rfl⟩, rfl⟩`. Conclude with `⟨f, (mem_weightedHomogeneousSubmodule _ _ _ _).mp hf, rfl⟩`. Introduce and unpack `⟨f, hf, rfl⟩`.

Conclude with `⟨_, ⟨f, (mem_weightedHomogeneousSubmodule _ _ _ _).mpr hf, rfl⟩, rfl⟩`. Establish `hfinU : ∀ m, FiniteDimensional F (U m)` using `fun m => by`. Use `((GradedFinite.proof.{u}) F K ι P m).1` as an intermediate fact. Conclude with `LinearEquiv.finiteDimensional (Submodule.equivMapOfInjective _ (hφinj m) _)`. Establish `hrankU : ∀ m, Module.finrank F (U m) = Module.finrank F (gradedPiece P m)` using `fun m => (LinearEquiv.finrank_eq (Submodule.equivMapOfInjective _ (hφinj m) _)).symm`.

Establish `hmono : ∀ m n, m ≤ n → U m ≤ U n` using `fun m n hmn y hy => by`. Take `⟨f, hf, rfl⟩` from `(memU m y).mp hy`. Use `(memU n _).mpr ⟨f * blockMonomial i (n - m), ?_, ?_⟩` and prove the remaining obligations. Use `hf.mul (blockMonomial_isMultiHomog (F := F) i (n - m))` as an intermediate fact. Rewrite `this` using `[add_tsub_cancel_of_le hmn]`. Then use the resulting hypothesis.

Establish `hn : xm n = xm m * xm (n - m)` using `by rw [← hxm_add, add_tsub_cancel_of_le hmn]`. Rewrite using `[hn, map_mul, map_mul]`. Conclude with `(mul_div_mul_right _ _ (hxm (n - m))).symm`. Establish `hmul : ∀ m n y z, y ∈ U m → z ∈ U n → y * z ∈ U (m + n)` using `fun m n y z hy hz => by`. Take `⟨f, hf, rfl⟩` from `(memU m y).mp hy`.

Take `⟨g, hg, rfl⟩` from `(memU n z).mp hz`. Use `(memU _ _).mpr ⟨f * g, hf.mul hg, ?_⟩` and prove the remaining obligations. Rewrite using `[hxm_add, map_mul, map_mul]`. Conclude with `div_mul_div_comm _ _ _ _`. Set `N : K → ℕ` to `fun k => (M0 k).toNat`.

Establish `hrankc : ∀ n, N ≤ n → (Module.finrank F (U n) : ℤ) = c` using `fun n hn => by`. Rewrite using `[hrankU, ← ((GradedFinite.proof.{u}) F K ι P n).2]`. Use `hM0 _ fun k => ?_` and prove the remaining obligations. Conclude with `(Int.self_le_toNat (M0 k)).trans (by exact_mod_cast hn k)`. Establish `hstab : ∀ m, U m ≤ U N` using `fun m => by`.

Establish `hN : U N = U (m ⊔ N)`. Use `hfinU (m ⊔ N)` as an intermediate fact. Use `Submodule.eq_of_le_of_finrank_eq (hmono _ _ le_sup_right) ?_` and prove the remaining obligations. Establish `h1` using `hrankc N le_rfl`. Establish `h2` using `hrankc (m ⊔ N) le_sup_right`.

Conclude with `h1.trans h2.symm` after adjusting the coercions. Rewrite using `[hN]`. Conclude with `hmono _ _ le_sup_left`. Establish `hone : (1 : L) ∈ U N`. Use `hstab 0 ((memU 0 1).mpr ⟨1, isWeightedHomogeneous_one F _, ?_⟩)` and prove the remaining obligations.

Establish `: xm 0 = 1` using `by simp [xm, blockMonomial]`. Rewrite using `[this, map_one, map_one, div_one]`. Set `S : Subalgebra F L` to `(U N).toSubalgebra hone fun y z hy hz => hstab _ (hmul _ _ _ _ hy hz)`. Establish `: FiniteDimensional F S` using `hfinU N`. Set `E : IntermediateField F L` to `S.toIntermediateField fun y hy => S.inv_mem_of_algebraic (x := ⟨y, hy⟩) ((IsIntegral.of_finite F (⟨y, hy⟩ : S)).map S.val).isAlgebraic`.

Establish `hEq : homFracDegZero P = E`. Apply `le_antisymm` to reduce the goal to its premises. Use `IntermediateField.adjoin_le_iff.mpr ?_` and prove the remaining obligations. Introduce and unpack `x ⟨b, f, g, hf, hg, hgP, rfl⟩`. Establish `hfU : algebraMap A L (Ideal.Quotient.mk P f) / xm b ∈ E` using `hstab b ((memU b _).mpr ⟨f, hf, rfl⟩)`.

Establish `hgU : algebraMap A L (Ideal.Quotient.mk P g) / xm b ∈ E` using `hstab b ((memU b _).mpr ⟨g, hg, rfl⟩)`. Establish `hg0 : algebraMap A L (Ideal.Quotient.mk P g) ≠ 0`. Rewrite using `[Ne, FaithfulSMul.algebraMap_eq_zero_iff, Ideal.Quotient.eq_zero_iff_mem]`. Conclude with `hgP`. Establish `heq : algebraMap A L (Ideal.Quotient.mk P f) / algebraMap A L (Ideal.Quotient.mk P g) = algebraMap A L (Ideal.Quotient.mk P f) / xm b * (algebraMap A L (Ideal.Quotient.mk P g) / xm b)⁻¹`.

Rewrite using `[inv_div, div_mul_div_comm, mul_comm (xm b), mul_div_mul_right _ _ (hxm b)]`. Rewrite using `[SetLike.mem_coe, heq]`. Conclude with `E.mul_mem hfU (E.inv_mem hgU)`. Introduce `y hy`. Take `⟨f, hf, rfl⟩` from `(memU N y).mp hy`.

Conclude with `IntermediateField.subset_adjoin _ _ ⟨N, f, blockMonomial i N, hf, blockMonomial_isMultiHomog i N, fun h => blockMonomial_mk_ne_zero P i hi N (Ideal.Quotient.eq_zero_iff_mem.mpr h), rfl⟩`. Establish `hES : Subalgebra.toSubmodule E.toSubalgebra = U N` using `rfl`. Set `e : E ≃ₗ[F] U N` to `LinearEquiv.ofEq _ _ hES`. Rewrite using `[hEq]`. Use `⟨LinearEquiv.finiteDimensional e.symm, ?_⟩` and prove the remaining obligations.

Rewrite using `[e.finrank_eq]`. Conclude with `(hrankc N le_rfl).symm`.
-/
theorem IntNumBase.proof (h1 : MixedDiffConst.Statement.{u}) : IntNumBase.Statement.{u} := by
  intro F _ K _ _ ι _ P hP hrel
  have := hP.isPrime

  have hev : ∀ᶠ m in Filter.atTop, hilbFn P m = intNum F P (n := 0) ![] := by
    have h0 : relDim P = ((0 : ℕ) : WithBot (WithTop ℤ)) := by rw [hrel]; rfl
    filter_upwards [(h1 F K ι P hP.multiHomog hP.relevant 0 h0).1 ![]] with m hm
    simpa [mixedDiff] using hm
  set c := intNum F P (n := 0) ![] with hc
  obtain ⟨M0, hM0⟩ := Filter.eventually_atTop.mp hev
  choose i hi using hP.relevant
  set A := MRing ι F ⧸ P
  set L := FractionRing A
  let xm : (K → ℕ) → L := fun m => algebraMap A L (Ideal.Quotient.mk P (blockMonomial i m))
  have hxm : ∀ m, xm m ≠ 0 := fun m => by
    simp only [xm, ne_eq, FaithfulSMul.algebraMap_eq_zero_iff]
    exact blockMonomial_mk_ne_zero P i hi m
  have hxm_add : ∀ m n, xm (m + n) = xm m * xm n := fun m n => by
    simp only [xm, blockMonomial_add, map_mul]

  let φ : (K → ℕ) → A →ₗ[F] L := fun m =>
    (LinearMap.mulRight F (xm m)⁻¹).comp (IsScalarTower.toAlgHom F A L).toLinearMap
  have hφ : ∀ m a, φ m a = algebraMap A L a / xm m := fun m a => by
    simp [φ, div_eq_mul_inv]
  have hφinj : ∀ m, Function.Injective (φ m) := fun m a b hab => by
    rw [hφ, hφ, div_left_inj' (hxm m)] at hab
    exact IsFractionRing.injective A L hab
  let U : (K → ℕ) → Submodule F L := fun m => (gradedPiece P m).map (φ m)
  have memU : ∀ m y, y ∈ U m ↔ ∃ f : MRing ι F, IsMultiHomog f m ∧
      y = algebraMap A L (Ideal.Quotient.mk P f) / xm m := fun m y => by
    simp only [U, gradedPiece, Submodule.mem_map, hφ]
    constructor
    · rintro ⟨a, ⟨f, hf, rfl⟩, rfl⟩
      exact ⟨f, (mem_weightedHomogeneousSubmodule _ _ _ _).mp hf, rfl⟩
    · rintro ⟨f, hf, rfl⟩
      exact ⟨_, ⟨f, (mem_weightedHomogeneousSubmodule _ _ _ _).mpr hf, rfl⟩, rfl⟩
  have hfinU : ∀ m, FiniteDimensional F (U m) := fun m => by
    have := ((GradedFinite.proof.{u}) F K ι P m).1
    exact LinearEquiv.finiteDimensional (Submodule.equivMapOfInjective _ (hφinj m) _)
  have hrankU : ∀ m, Module.finrank F (U m) = Module.finrank F (gradedPiece P m) := fun m =>
    (LinearEquiv.finrank_eq (Submodule.equivMapOfInjective _ (hφinj m) _)).symm
  have hmono : ∀ m n, m ≤ n → U m ≤ U n := fun m n hmn y hy => by
    obtain ⟨f, hf, rfl⟩ := (memU m y).mp hy
    refine (memU n _).mpr ⟨f * blockMonomial i (n - m), ?_, ?_⟩
    · have := hf.mul (blockMonomial_isMultiHomog (F := F) i (n - m))
      rwa [add_tsub_cancel_of_le hmn] at this
    · have hn : xm n = xm m * xm (n - m) := by rw [← hxm_add, add_tsub_cancel_of_le hmn]
      rw [hn, map_mul, map_mul]
      exact (mul_div_mul_right _ _ (hxm (n - m))).symm
  have hmul : ∀ m n y z, y ∈ U m → z ∈ U n → y * z ∈ U (m + n) := fun m n y z hy hz => by
    obtain ⟨f, hf, rfl⟩ := (memU m y).mp hy
    obtain ⟨g, hg, rfl⟩ := (memU n z).mp hz
    refine (memU _ _).mpr ⟨f * g, hf.mul hg, ?_⟩
    rw [hxm_add, map_mul, map_mul]
    exact div_mul_div_comm _ _ _ _

  let N : K → ℕ := fun k => (M0 k).toNat
  have hrankc : ∀ n, N ≤ n → (Module.finrank F (U n) : ℤ) = c := fun n hn => by
    rw [hrankU, ← ((GradedFinite.proof.{u}) F K ι P n).2]
    refine hM0 _ fun k => ?_
    exact (Int.self_le_toNat (M0 k)).trans (by exact_mod_cast hn k)
  have hstab : ∀ m, U m ≤ U N := fun m => by
    have hN : U N = U (m ⊔ N) := by
      have := hfinU (m ⊔ N)
      refine Submodule.eq_of_le_of_finrank_eq (hmono _ _ le_sup_right) ?_
      have h1 := hrankc N le_rfl
      have h2 := hrankc (m ⊔ N) le_sup_right
      exact_mod_cast h1.trans h2.symm
    rw [hN]
    exact hmono _ _ le_sup_left

  have hone : (1 : L) ∈ U N := by
    refine hstab 0 ((memU 0 1).mpr ⟨1, isWeightedHomogeneous_one F _, ?_⟩)
    have : xm 0 = 1 := by simp [xm, blockMonomial]
    rw [this, map_one, map_one, div_one]
  let S : Subalgebra F L := (U N).toSubalgebra hone fun y z hy hz => hstab _ (hmul _ _ _ _ hy hz)
  have : FiniteDimensional F S := hfinU N
  let E : IntermediateField F L := S.toIntermediateField fun y hy =>
    S.inv_mem_of_algebraic (x := ⟨y, hy⟩) ((IsIntegral.of_finite F (⟨y, hy⟩ : S)).map S.val).isAlgebraic
  have hEq : homFracDegZero P = E := by
    apply le_antisymm
    · refine IntermediateField.adjoin_le_iff.mpr ?_
      rintro x ⟨b, f, g, hf, hg, hgP, rfl⟩
      have hfU : algebraMap A L (Ideal.Quotient.mk P f) / xm b ∈ E :=
        hstab b ((memU b _).mpr ⟨f, hf, rfl⟩)
      have hgU : algebraMap A L (Ideal.Quotient.mk P g) / xm b ∈ E :=
        hstab b ((memU b _).mpr ⟨g, hg, rfl⟩)
      have hg0 : algebraMap A L (Ideal.Quotient.mk P g) ≠ 0 := by
        rw [Ne, FaithfulSMul.algebraMap_eq_zero_iff, Ideal.Quotient.eq_zero_iff_mem]
        exact hgP
      have heq : algebraMap A L (Ideal.Quotient.mk P f) / algebraMap A L (Ideal.Quotient.mk P g) =
          algebraMap A L (Ideal.Quotient.mk P f) / xm b *
            (algebraMap A L (Ideal.Quotient.mk P g) / xm b)⁻¹ := by
        rw [inv_div, div_mul_div_comm, mul_comm (xm b), mul_div_mul_right _ _ (hxm b)]
      rw [SetLike.mem_coe, heq]
      exact E.mul_mem hfU (E.inv_mem hgU)
    · intro y hy
      obtain ⟨f, hf, rfl⟩ := (memU N y).mp hy
      exact IntermediateField.subset_adjoin _ _
        ⟨N, f, blockMonomial i N, hf, blockMonomial_isMultiHomog i N,
          fun h => blockMonomial_mk_ne_zero P i hi N (Ideal.Quotient.eq_zero_iff_mem.mpr h), rfl⟩
  have hES : Subalgebra.toSubmodule E.toSubalgebra = U N := rfl
  let e : E ≃ₗ[F] U N := LinearEquiv.ofEq _ _ hES
  rw [hEq]
  refine ⟨LinearEquiv.finiteDimensional e.symm, ?_⟩
  rw [e.finrank_eq]
  exact (hrankc N le_rfl).symm

end

end GroundTheory.Heights₂.Heights.FieldNumbers

import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MixedFieldContraction.ContractMixedFieldStatement
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.PFibreMultiHomog
import GroundTheory.HeightsAndTheta.Heights.Intersections.PEvalKerKrullDim
import GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.PIntDomainDim
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PCoordConeArithVar
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.ChangeOfModel
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.ForSecondHalf

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4

namespace FibreDimB

/- English proof (translation)
Establish `: FaithfulSMul B L` using `(faithfulSMul_iff_algebraMap_injective _ _).2 (IsFractionRing.injective B L)`. Establish `: FaithfulSMul ℤ B` using `(faithfulSMul_iff_algebraMap_injective _ _).2 hB`. Establish `: Algebra.IsAlgebraic B L` using `IsLocalization.isAlgebraic L (nonZeroDivisors B)`. Rewrite using `[← trdeg_add_eq ℤ B (A := L), trdeg_eq_zero (R := B) (A := L), add_zero]`.
-/
theorem trdeg_eq_of_isFractionRing (B : Type) [CommRing B] [IsDomain B] (L : Type) [Field L] [Algebra B L]
    [IsFractionRing B L] (hB : Function.Injective (algebraMap ℤ B)) :
    Algebra.trdeg ℤ L = Algebra.trdeg ℤ B := by
  have : FaithfulSMul B L :=
    (faithfulSMul_iff_algebraMap_injective _ _).2 (IsFractionRing.injective B L)
  have : FaithfulSMul ℤ B := (faithfulSMul_iff_algebraMap_injective _ _).2 hB
  have : Algebra.IsAlgebraic B L := IsLocalization.isAlgebraic L (nonZeroDivisors B)
  rw [← trdeg_add_eq ℤ B (A := L), trdeg_eq_zero (R := B) (A := L), add_zero]

/- English proof (translation)
Substitute `hker` using the available equality. Use `set φ := Ideal.kerLiftAlg (aeval y : MvPolynomial σ ℤ →ₐ[ℤ] L) with hφdef`. Establish `: (RingHom.ker (aeval y : MvPolynomial σ ℤ →ₐ[ℤ] L)).IsPrime` using `RingHom.ker_isPrime _`. Set `_ : Algebra (MvPolynomial σ ℤ ⧸ RingHom.ker (aeval y : MvPolynomial σ ℤ →ₐ[ℤ] L)) L` to `φ.toRingHom.toAlgebra`. Establish `hφ : Function.Injective φ` using `Ideal.kerLiftAlg_injective _`.

Establish `: FaithfulSMul (MvPolynomial σ ℤ ⧸ RingHom.ker (aeval y : MvPolynomial σ ℤ →ₐ[ℤ] L)) L` using `(faithfulSMul_iff_algebraMap_injective _ _).2 hφ`. Establish `: IsFractionRing (MvPolynomial σ ℤ ⧸ RingHom.ker (aeval y : MvPolynomial σ ℤ →ₐ[ℤ] L)) L` using `IsFractionRing.of_field _ L fun z => by`. Take `⟨f, g, rfl⟩` from `hgen z`. Conclude with `⟨Ideal.Quotient.mk _ f, Ideal.Quotient.mk _ g, (congrArg₂ (· / ·) (Ideal.kerLiftAlg_mk (aeval y : MvPolynomial σ ℤ →ₐ[ℤ] L) f) (Ideal.kerLiftAlg_mk (aeval y : MvPolynomial σ ℤ →ₐ[ℤ] L) g)).symm⟩`. Use `trdeg_eq_of_isFractionRing _ L fun a b h => hZ ?_` and prove the remaining obligations.

Simplify `congrArg φ h` using `only [eq_intCast, map_intCast]`.
-/
theorem trdeg_eq_of_gen {σ L : Type} [Field L] (y : σ → L) (P : Ideal (MvPolynomial σ ℤ))
    (hker : RingHom.ker (aeval y : MvPolynomial σ ℤ →ₐ[ℤ] L) = P)
    (hZ : Function.Injective (algebraMap ℤ L))
    (hgen : ∀ z : L, ∃ f g : MvPolynomial σ ℤ, z = aeval y f / aeval y g) :
    Algebra.trdeg ℤ L = Algebra.trdeg ℤ (MvPolynomial σ ℤ ⧸ P) := by
  subst hker
  set φ := Ideal.kerLiftAlg (aeval y : MvPolynomial σ ℤ →ₐ[ℤ] L) with hφdef
  have : (RingHom.ker (aeval y : MvPolynomial σ ℤ →ₐ[ℤ] L)).IsPrime := RingHom.ker_isPrime _
  let _ : Algebra (MvPolynomial σ ℤ ⧸ RingHom.ker (aeval y : MvPolynomial σ ℤ →ₐ[ℤ] L)) L :=
    φ.toRingHom.toAlgebra
  have hφ : Function.Injective φ := Ideal.kerLiftAlg_injective _
  have : FaithfulSMul (MvPolynomial σ ℤ ⧸ RingHom.ker (aeval y : MvPolynomial σ ℤ →ₐ[ℤ] L)) L :=
    (faithfulSMul_iff_algebraMap_injective _ _).2 hφ
  have : IsFractionRing (MvPolynomial σ ℤ ⧸ RingHom.ker (aeval y : MvPolynomial σ ℤ →ₐ[ℤ] L)) L :=
    IsFractionRing.of_field _ L fun z => by
      obtain ⟨f, g, rfl⟩ := hgen z
      exact ⟨Ideal.Quotient.mk _ f, Ideal.Quotient.mk _ g, (congrArg₂ (· / ·) (Ideal.kerLiftAlg_mk (aeval y : MvPolynomial σ ℤ →ₐ[ℤ] L) f)
        (Ideal.kerLiftAlg_mk (aeval y : MvPolynomial σ ℤ →ₐ[ℤ] L) g)).symm⟩
  refine trdeg_eq_of_isFractionRing _ L fun a b h => hZ ?_
  simpa only [eq_intCast, map_intCast] using congrArg φ h

/- English proof (translation)
Take `⟨_, ⟨hprime, -, -⟩, hhor, hdim⟩` from `hP`. Use `hprime` as an intermediate fact. Establish `hA` using `IntDomainDim.proof (MRing ι ⧸ P) (CoordinateConeArithVar.algebraMap_injective P hhor)`. Rewrite `hA` using `[hdim]`. Establish `h' : ((n + Fintype.card K : ℕ) : ℕ∞) = (Algebra.trdeg ℤ (MRing ι ⧸ P)).toENat + 1`.

Conclude with `hA` after adjusting the coercions. Choose the witnesses or unpack the hypotheses as in `⟨t, ht⟩ : ∃ t : ℕ, (Algebra.trdeg ℤ (MRing ι ⧸ P)).toENat = t := by`. Use `ENat.ne_top_iff_exists.mp (fun htop => ?_) |>.imp fun _ h => h.symm` and prove the remaining obligations. Rewrite `h'` using `[htop]`. Simplify using `at h'`.

Use `⟨t, Cardinal.toENat_eq_natCast.mp ht, ?_⟩` and prove the remaining obligations. Rewrite `h'` using `[ht]`. Conclude with `h'.symm` after adjusting the coercions.
-/
theorem trdeg_of_isArithVar {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {P : Ideal (MRing ι)}
    {n : ℕ} (hP : IsArithVar P n) :
    ∃ t : ℕ, Algebra.trdeg ℤ (MRing ι ⧸ P) = t ∧ t + 1 = n + Fintype.card K := by
  obtain ⟨_, ⟨hprime, -, -⟩, hhor, hdim⟩ := hP
  have := hprime
  have hA := IntDomainDim.proof (MRing ι ⧸ P) (CoordinateConeArithVar.algebraMap_injective P hhor)
  rw [hdim] at hA
  have h' : ((n + Fintype.card K : ℕ) : ℕ∞) = (Algebra.trdeg ℤ (MRing ι ⧸ P)).toENat + 1 := by
    exact_mod_cast hA
  obtain ⟨t, ht⟩ : ∃ t : ℕ, (Algebra.trdeg ℤ (MRing ι ⧸ P)).toENat = t := by
    refine ENat.ne_top_iff_exists.mp (fun htop => ?_) |>.imp fun _ h => h.symm
    rw [htop] at h'
    simp at h'
  refine ⟨t, Cardinal.toENat_eq_natCast.mp ht, ?_⟩
  rw [ht] at h'
  exact_mod_cast h'.symm

/- English proof (translation)
Proceed by induction on `f using MvPolynomial.induction_on with`. Consider the case `C a => simp [intCast_mem]`. Consider the case `add f g hf hg => simpa using add_mem hf hg`. Consider the case `mul_X f i hf => simpa using mul_mem hf (Subfield.subset_closure ⟨i, rfl⟩)`.
-/
theorem aeval_mem_closure {σ L : Type} [Field L] (y : σ → L) (f : MvPolynomial σ ℤ) :
    aeval y f ∈ Subfield.closure (Set.range y) := by
  induction f using MvPolynomial.induction_on with
  | C a => simp [intCast_mem]
  | add f g hf hg => simpa using add_mem hf hg
  | mul_X f i hf => simpa using mul_mem hf (Subfield.subset_closure ⟨i, rfl⟩)

end FibreDimB

open FibreDimB in

/- English proof (translation)
Introduce `K _ ι _ K' _ ι' _ κ v P' d r G hv hP' hP`. Use `⟨⟨RingHom.ker_isPrime _, Targets.FibreMultiHomog.proof K ι K' ι' κ v P' G hv hP'.2.1.2.1, fun k => ?_⟩, ?_⟩` and prove the remaining obligations. Take `⟨i, hi⟩` from `hP'.2.1.2.2 k.1`. Use `⟨i, fun h => hi ?_⟩` and prove the remaining obligations. Rewrite `h` using `[fibreIdeal, RingHom.mem_ker, aeval_X]`.

Rewrite using `[← G.genericFibre_ker_target, RingHom.mem_ker, aeval_X]`. Conclude with `h`. Establish `hZ' : Function.Injective (algebraMap ℤ G.Φ')`. Rewrite using `[injective_iff_map_eq_zero]`. Introduce `a ha`.

Establish `hm : a ∈ P'.comap (C : ℤ →+* MRing ι')`. Rewrite using `[Ideal.mem_comap, ← G.genericFibre_ker_target, RingHom.mem_ker, aeval_C, ha]`. Rewrite `hm` using `[show P'.comap (C : ℤ →+* MRing ι') = ⊥ from hP'.2.2.1]`. Conclude with `(Submodule.mem_bot ℤ).mp hm`. Establish `hZ : Function.Injective (algebraMap ℤ G.Φ)` using `fun a b h => hZ' (by simpa only [eq_intCast, map_intCast] using congrArg (algebraMap G.Φ G.Φ') h)`.

Use `set E := IntermediateField.adjoin G.Φ (Set.range fun q : (Σ k : FibreBlock κ, ι' k.1) => G.x' ⟨q.1.1, q.2⟩) with hEdef`. Establish `hmem : ∀ q, G.x' q ∈ E`. Introduce `q`. Distinguish the cases in `hq : q.1 ∈ Set.range κ`. Take `⟨q0, rfl⟩` from `hv.2.2.2 q hq`.

Rewrite using `[G.compat]`. Conclude with `E.algebraMap_mem _`. Conclude with `IntermediateField.subset_adjoin _ _ ⟨⟨⟨q.1, hq⟩, q.2⟩, rfl⟩`. Set `y' : (Σ k', ι' k') → E` to `fun q => ⟨G.x' q, hmem q⟩`. Establish `hval : ∀ f : MRing ι', ((aeval y' f : E) : G.Φ') = aeval G.x' f`.

Introduce `f`. Proceed by induction on `f using MvPolynomial.induction_on with`. Consider the case `C a => simp`. Consider the case `add f g hf hg => simp only [map_add, IntermediateField.coe_add, hf, hg]`. Consider the case `mul_X f i hf => simp only [map_mul, IntermediateField.coe_mul, hf, aeval_X, y']`.

Establish `hkerE : RingHom.ker (aeval y' : MRing ι' →ₐ[ℤ] E) = P'`. Use extensionality with `f`. Establish `h2 : f ∈ P' ↔ aeval G.x' f = 0` using `by rw [← RingHom.mem_ker, G.genericFibre_ker_target]`. Rewrite using `[RingHom.mem_ker, h2, ← hval]`. Conclude with `⟨fun h => by rw [h]; rfl, fun h => Subtype.ext h⟩`.

Establish `hZE : Function.Injective (algebraMap ℤ E)` using `fun a b h => hZ' (by simpa using congrArg (fun z : E => (z : G.Φ')) h)`. Establish `hkey : ∀ f : MRing ι, algebraMap G.Φ G.Φ' (aeval G.x f) = aeval G.x' (rename v f)`. Introduce `f`. Proceed by induction on `f using MvPolynomial.induction_on with`. Consider the case `C a => simp`.

Consider the case `add f g hf hg => simp only [map_add, hf, hg]`. Consider the case `mul_X f i hf => simp only [map_mul, hf, aeval_X, rename_X, G.compat]`. Establish `hle : E.toSubfield ≤ Subfield.closure (Set.range G.x')`. Rewrite using `[hEdef, IntermediateField.adjoin_toSubfield]`. Use `Subfield.closure_le.2 (Set.union_subset ?_ ?_)` and prove the remaining obligations.

Introduce and unpack `_ ⟨c, rfl⟩`. Take `⟨f, g, -, rfl⟩` from `G.gen c`. Rewrite using `[map_div₀, hkey, hkey]`. Conclude with `div_mem (aeval_mem_closure _ _) (aeval_mem_closure _ _)`. Introduce and unpack `_ ⟨q, rfl⟩`.

Conclude with `Subfield.subset_closure ⟨_, rfl⟩`. Establish `hgenE : ∀ z : E, ∃ f g : MRing ι', z = aeval y' f / aeval y' g`. Introduce `z`. Take `⟨a, ha, b, hb, hab⟩` from `(Subfield.mem_closure_iff).1 (hle z.2)`. Establish `hsub : Subring.closure (Set.range G.x') ≤ (aeval G.x' : MRing ι' →ₐ[ℤ] G.Φ').range.toSubring` using `Subring.closure_le.2 (by rintro _ ⟨q, rfl⟩; exact ⟨X q, aeval_X _ _⟩)`.

Take `⟨f, hf⟩` from `hsub ha`. Take `⟨g, hg⟩` from `hsub hb`. Use `⟨f, g, Subtype.ext ?_⟩` and prove the remaining obligations. Rewrite using `[IntermediateField.coe_div, hval, hval]`. Simplify using `only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe] at hf hg`.

Rewrite using `[hf, hg, hab]`. Establish `tΦ : Algebra.trdeg ℤ G.Φ = Algebra.trdeg ℤ (MRing ι ⧸ imageZ v P')` using `trdeg_eq_of_gen G.x _ G.ker_x hZ fun z => by`. Take `⟨f, g, -, h⟩` from `G.gen z`. Conclude with `⟨f, g, h⟩`. Establish `tE : Algebra.trdeg ℤ E = Algebra.trdeg ℤ (MRing ι' ⧸ P')` using `trdeg_eq_of_gen y' _ hkerE hZE hgenE`.

Take `⟨a, ha, ha1⟩` from `trdeg_of_isArithVar hP`. Take `⟨b, hb, hb1⟩` from `trdeg_of_isArithVar hP'`. Establish `: FaithfulSMul ℤ G.Φ` using `(faithfulSMul_iff_algebraMap_injective _ _).2 hZ`. Establish `: FaithfulSMul G.Φ E` using `(faithfulSMul_iff_algebraMap_injective _ _).2 (algebraMap G.Φ E).injective`. Establish `hadd` using `trdeg_add_eq ℤ G.Φ (A := E)`.

Rewrite `hadd` using `[tΦ, ha, tE, hb]`. Establish `hc : Fintype.card (FibreBlock κ) + Fintype.card K = Fintype.card K'`. Simplify using `only [← Nat.card_eq_fintype_card]`. Establish `h1` using `Set.ncard_add_ncard_compl (Set.range κ)`. Rewrite `h1` using `[Set.ncard_range_of_injective hv.1, add_comm]`.

Conclude with `h1`. Establish `hlt : Algebra.trdeg G.Φ E < Cardinal.aleph0` using `lt_of_le_of_lt (le_add_self.trans_eq hadd) (Cardinal.natCast_lt_aleph0)`. Take `⟨m, hm⟩` from `Cardinal.lt_aleph0.1 hlt`. Rewrite `hadd` using `[hm]`. Establish `hm' : a + m = b` using `by exact_mod_cast hadd`.

Establish `hmr : m = r + Fintype.card (FibreBlock κ)` using `by omega`. Rewrite using `[fibreIdeal, Inter.EvalKerKrullDim.proof (FibreBlock κ) (fibreIdx ι' κ) G.Φ G.Φ']`. Rewrite using `[show IntermediateField.adjoin G.Φ (Set.range fun q : (Σ k : FibreBlock κ, ι' k.1) => G.x' ⟨q.1.1, q.2⟩) = E from hEdef.symm, hm, hmr]`. Simplify using the standard rewrite rules.
-/
theorem FibreDimB.full : FibreDimStatement := by
  intro K _ ι _ K' _ ι' _ κ v P' d r G hv hP' hP
  refine ⟨⟨RingHom.ker_isPrime _,
    Targets.FibreMultiHomog.proof K ι K' ι' κ v P' G hv hP'.2.1.2.1, fun k => ?_⟩, ?_⟩
  · obtain ⟨i, hi⟩ := hP'.2.1.2.2 k.1
    refine ⟨i, fun h => hi ?_⟩
    rw [fibreIdeal, RingHom.mem_ker, aeval_X] at h
    rw [← G.genericFibre_ker_target, RingHom.mem_ker, aeval_X]
    exact h

  have hZ' : Function.Injective (algebraMap ℤ G.Φ') := by
    rw [injective_iff_map_eq_zero]
    intro a ha
    have hm : a ∈ P'.comap (C : ℤ →+* MRing ι') := by
      rw [Ideal.mem_comap, ← G.genericFibre_ker_target, RingHom.mem_ker, aeval_C, ha]
    rw [show P'.comap (C : ℤ →+* MRing ι') = ⊥ from hP'.2.2.1] at hm
    exact (Submodule.mem_bot ℤ).mp hm
  have hZ : Function.Injective (algebraMap ℤ G.Φ) := fun a b h =>
    hZ' (by simpa only [eq_intCast, map_intCast] using congrArg (algebraMap G.Φ G.Φ') h)

  set E := IntermediateField.adjoin G.Φ
    (Set.range fun q : (Σ k : FibreBlock κ, ι' k.1) => G.x' ⟨q.1.1, q.2⟩) with hEdef
  have hmem : ∀ q, G.x' q ∈ E := by
    intro q
    by_cases hq : q.1 ∈ Set.range κ
    · obtain ⟨q0, rfl⟩ := hv.2.2.2 q hq
      rw [G.compat]
      exact E.algebraMap_mem _
    · exact IntermediateField.subset_adjoin _ _ ⟨⟨⟨q.1, hq⟩, q.2⟩, rfl⟩
  let y' : (Σ k', ι' k') → E := fun q => ⟨G.x' q, hmem q⟩
  have hval : ∀ f : MRing ι', ((aeval y' f : E) : G.Φ') = aeval G.x' f := by
    intro f
    induction f using MvPolynomial.induction_on with
    | C a => simp
    | add f g hf hg => simp only [map_add, IntermediateField.coe_add, hf, hg]
    | mul_X f i hf => simp only [map_mul, IntermediateField.coe_mul, hf, aeval_X, y']
  have hkerE : RingHom.ker (aeval y' : MRing ι' →ₐ[ℤ] E) = P' := by
    ext f
    have h2 : f ∈ P' ↔ aeval G.x' f = 0 := by rw [← RingHom.mem_ker, G.genericFibre_ker_target]
    rw [RingHom.mem_ker, h2, ← hval]
    exact ⟨fun h => by rw [h]; rfl, fun h => Subtype.ext h⟩
  have hZE : Function.Injective (algebraMap ℤ E) := fun a b h =>
    hZ' (by simpa using congrArg (fun z : E => (z : G.Φ')) h)

  have hkey : ∀ f : MRing ι, algebraMap G.Φ G.Φ' (aeval G.x f) = aeval G.x' (rename v f) := by
    intro f
    induction f using MvPolynomial.induction_on with
    | C a => simp
    | add f g hf hg => simp only [map_add, hf, hg]
    | mul_X f i hf => simp only [map_mul, hf, aeval_X, rename_X, G.compat]
  have hle : E.toSubfield ≤ Subfield.closure (Set.range G.x') := by
    rw [hEdef, IntermediateField.adjoin_toSubfield]
    refine Subfield.closure_le.2 (Set.union_subset ?_ ?_)
    · rintro _ ⟨c, rfl⟩
      obtain ⟨f, g, -, rfl⟩ := G.gen c
      rw [map_div₀, hkey, hkey]
      exact div_mem (aeval_mem_closure _ _) (aeval_mem_closure _ _)
    · rintro _ ⟨q, rfl⟩
      exact Subfield.subset_closure ⟨_, rfl⟩
  have hgenE : ∀ z : E, ∃ f g : MRing ι', z = aeval y' f / aeval y' g := by
    intro z
    obtain ⟨a, ha, b, hb, hab⟩ := (Subfield.mem_closure_iff).1 (hle z.2)
    have hsub : Subring.closure (Set.range G.x') ≤ (aeval G.x' : MRing ι' →ₐ[ℤ] G.Φ').range.toSubring :=
      Subring.closure_le.2 (by rintro _ ⟨q, rfl⟩; exact ⟨X q, aeval_X _ _⟩)
    obtain ⟨f, hf⟩ := hsub ha
    obtain ⟨g, hg⟩ := hsub hb
    refine ⟨f, g, Subtype.ext ?_⟩
    rw [IntermediateField.coe_div, hval, hval]
    simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe] at hf hg
    rw [hf, hg, hab]

  have tΦ : Algebra.trdeg ℤ G.Φ = Algebra.trdeg ℤ (MRing ι ⧸ imageZ v P') :=
    trdeg_eq_of_gen G.x _ G.ker_x hZ fun z => by
      obtain ⟨f, g, -, h⟩ := G.gen z
      exact ⟨f, g, h⟩
  have tE : Algebra.trdeg ℤ E = Algebra.trdeg ℤ (MRing ι' ⧸ P') :=
    trdeg_eq_of_gen y' _ hkerE hZE hgenE
  obtain ⟨a, ha, ha1⟩ := trdeg_of_isArithVar hP
  obtain ⟨b, hb, hb1⟩ := trdeg_of_isArithVar hP'
  have : FaithfulSMul ℤ G.Φ := (faithfulSMul_iff_algebraMap_injective _ _).2 hZ
  have : FaithfulSMul G.Φ E := (faithfulSMul_iff_algebraMap_injective _ _).2 (algebraMap G.Φ E).injective
  have hadd := trdeg_add_eq ℤ G.Φ (A := E)
  rw [tΦ, ha, tE, hb] at hadd
  have hc : Fintype.card (FibreBlock κ) + Fintype.card K = Fintype.card K' := by
    simp only [← Nat.card_eq_fintype_card]
    have h1 := Set.ncard_add_ncard_compl (Set.range κ)
    rw [Set.ncard_range_of_injective hv.1, add_comm] at h1
    exact h1
  have hlt : Algebra.trdeg G.Φ E < Cardinal.aleph0 :=
    lt_of_le_of_lt (le_add_self.trans_eq hadd) (Cardinal.natCast_lt_aleph0)
  obtain ⟨m, hm⟩ := Cardinal.lt_aleph0.1 hlt
  rw [hm] at hadd
  have hm' : a + m = b := by exact_mod_cast hadd
  have hmr : m = r + Fintype.card (FibreBlock κ) := by omega
  rw [fibreIdeal, Inter.EvalKerKrullDim.proof (FibreBlock κ) (fibreIdx ι' κ) G.Φ G.Φ']
  rw [show IntermediateField.adjoin G.Φ
      (Set.range fun q : (Σ k : FibreBlock κ, ι' k.1) => G.x' ⟨q.1.1, q.2⟩) = E from hEdef.symm, hm, hmr]
  simp

section Inhabitants

end Inhabitants

end GroundTheory.Heights₂.Heights.ForSecondHalf

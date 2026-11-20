import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.WeilThetaConvergence
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsSmoothModerateOfIsAutFunSm
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LintegralSiegelConeInvModulusLtTopWeilStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsCompactAdele
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSiegelDomainReduction
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.IntegralFiniteAdeleCompactClosedMultiples
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.SiegelFormula
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open NumberField IsDedekindDomain Matrix

namespace GlobalTheory.CompanionTheory.AdelicDenom

/- English proof (translation)
Establish `h` using `RestrictedProduct.isOpen_forall_mem (ι := HeightOneSpectrum (𝓞 F)) (R := fun v => v.adicCompletion F) (A := fun v => (v.adicCompletionIntegers F : Set (v.adicCompletion F))) (fun v => Valued.isOpen_valuationSubring _)`. Conclude with `h`.
-/
theorem isOpen_integral (F : Type) [Field F] [NumberField F] :
    IsOpen {a : Af F | ∀ v, a v ∈ HeightOneSpectrum.adicCompletionIntegers F v} := by
  have h := RestrictedProduct.isOpen_forall_mem (ι := HeightOneSpectrum (𝓞 F))
    (R := fun v => v.adicCompletion F)
    (A := fun v => (v.adicCompletionIntegers F : Set (v.adicCompletion F)))
    (fun v => Valued.isOpen_valuationSubring _)
  exact h

/- English proof (translation)
The claim follows from `GlobalTheory.IntegralFinAdele.natCast_apply F M v ▸ HeightOneSpectrum.coe_mem_adicCompletionIntegers v (M : 𝓞 F)`.
-/
theorem natCast_integral (F : Type) [Field F] [NumberField F] (M : ℕ)
    (v : HeightOneSpectrum (𝓞 F)) :
    (M : Af F) v ∈ HeightOneSpectrum.adicCompletionIntegers F v :=
  GlobalTheory.IntegralFinAdele.natCast_apply F M v ▸
    HeightOneSpectrum.coe_mem_adicCompletionIntegers v (M : 𝓞 F)

/- English proof (translation)
Set `U : {M : ℕ // 0 < M} → Set (Af F)` to `fun M => (fun a => (M.1 : Af F) * a) ⁻¹' {a : Af F | ∀ v, a v ∈ HeightOneSpectrum.adicCompletionIntegers F v}`. Establish `hU : ∀ M, IsOpen (U M)` using `fun M => (isOpen_integral F).preimage (continuous_const_mul _)`. Establish `hcov : K ⊆ ⋃ M, U M` using `fun a _ => by`. Take `⟨M, hM, h⟩` from `GlobalTheory.IntegralFinAdele.exists_nat_mul_integral F a`. Conclude with `Set.mem_iUnion.2 ⟨⟨M, hM⟩, h⟩`.

Take `⟨t, ht⟩` from `hK.elim_finite_subcover U hU hcov`. Use `⟨∏ m ∈ t, m.1, Finset.prod_pos fun m _ => m.2, fun a ha v => ?_⟩` and prove the remaining obligations. Take `⟨m, hm, ham⟩` from `Set.mem_iUnion₂.1 (ht ha)`. Take `⟨c, hc⟩ : m.1 ∣ ∏ m ∈ t, m.1` from `Finset.dvd_prod_of_mem (fun m => m.1) hm`. Establish `h : ((∏ m ∈ t, m.1 : ℕ) : Af F) * a = (c : Af F) * ((m.1 : Af F) * a)`.

Rewrite using `[hc, Nat.cast_mul]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[h, GlobalTheory.IntegralFinAdele.mul_apply']`. Conclude with `mul_mem (natCast_integral F c v) (ham v)`.
-/
theorem exists_common_denominator (F : Type) [Field F] [NumberField F] (K : Set (Af F))
    (hK : IsCompact K) :
    ∃ M : ℕ, 0 < M ∧ ∀ a ∈ K, ∀ v,
      ((M : Af F) * a) v ∈ HeightOneSpectrum.adicCompletionIntegers F v := by
  let U : {M : ℕ // 0 < M} → Set (Af F) := fun M =>
    (fun a => (M.1 : Af F) * a) ⁻¹'
      {a : Af F | ∀ v, a v ∈ HeightOneSpectrum.adicCompletionIntegers F v}
  have hU : ∀ M, IsOpen (U M) := fun M =>
    (isOpen_integral F).preimage (continuous_const_mul _)
  have hcov : K ⊆ ⋃ M, U M := fun a _ => by
    obtain ⟨M, hM, h⟩ := GlobalTheory.IntegralFinAdele.exists_nat_mul_integral F a
    exact Set.mem_iUnion.2 ⟨⟨M, hM⟩, h⟩
  obtain ⟨t, ht⟩ := hK.elim_finite_subcover U hU hcov
  refine ⟨∏ m ∈ t, m.1, Finset.prod_pos fun m _ => m.2, fun a ha v => ?_⟩
  obtain ⟨m, hm, ham⟩ := Set.mem_iUnion₂.1 (ht ha)
  obtain ⟨c, hc⟩ : m.1 ∣ ∏ m ∈ t, m.1 := Finset.dvd_prod_of_mem (fun m => m.1) hm
  have h : ((∏ m ∈ t, m.1 : ℕ) : Af F) * a = (c : Af F) * ((m.1 : Af F) * a) := by
    rw [hc, Nat.cast_mul]; ring
  rw [h, GlobalTheory.IntegralFinAdele.mul_apply']
  exact mul_mem (natCast_integral F c v) (ham v)

/- English proof (translation)
Introduce `F E _ _ _ _ _ C hC`. Establish `: IsModuleTopology (Af F) (Af F ⊗[F] E)` using `⟨rfl⟩`. Set `ε` to `Module.finBasis F E`. Set `b` to `Algebra.TensorProduct.basis (Af F) ε`. Establish `hcont : ∀ k, Continuous (b.coord k)` using `fun k => IsModuleTopology.continuous_of_linearMap (b.coord k)`.

Establish `hK : IsCompact (⋃ k, (b.coord k) '' C)` using `isCompact_iUnion fun k => hC.image (hcont k)`. Take `⟨M, hM, hMK⟩` from `exists_common_denominator F _ hK`. Establish `: Algebra.IsAlgebraic ℤ E` using `(IsFractionRing.comap_isAlgebraic_iff (A := ℤ) (K := ℚ) (C := E)).2 inferInstance`. Establish `hm : ∀ k, ∃ m : ℕ, 0 < m ∧ IsIntegral ℤ ((m : E) * ε k)` using `fun k => by`. Take `⟨m, y, hm, hmy⟩` from `IsAlgebraic.exists_nsmul_eq (𝓞 E) (Algebra.IsAlgebraic.isAlgebraic (R := ℤ) (ε k))`.

Use `⟨m, Nat.pos_of_ne_zero hm, ?_⟩` and prove the remaining obligations. Rewrite using `[← nsmul_eq_mul, hmy]`. Conclude with `RingOfIntegers.isIntegral_coe y`. Use `choose m hm0 hmi using hm`. Use `⟨M * ∏ k, m k, Nat.mul_pos hM (Finset.prod_pos fun k _ => hm0 k), fun x hx => ?_⟩` and prove the remaining obligations.

Establish `hcoord : ∀ k, IsIntegral ℤ ((M : F) * ε.repr x k)` using `fun k => by`. Establish `hmem : b.coord k ((1 : Af F) ⊗ₜ[F] x) ∈ ⋃ k, (b.coord k) '' C` using `Set.mem_iUnion.2 ⟨k, Set.mem_image_of_mem _ hx⟩`. Establish `hrepr : b.coord k ((1 : Af F) ⊗ₜ[F] x) = algebraMap F (Af F) (ε.repr x k)`. Simplify using `[b, Module.Basis.coord_apply, Algebra.TensorProduct.basis_repr_tmul]`. Establish `h` using `hMK _ hmem`.

Rewrite `h` using `[hrepr, ← map_natCast (algebraMap F (Af F)) M, ← map_mul]`. Take `⟨y, hy⟩` from `(GlobalTheory.IntegralFinAdele.integral_finiteAdele_properties F).2.2.2.1 _ h`. Rewrite using `[hy]`. Conclude with `RingOfIntegers.isIntegral_coe y`. Establish `hP : ∀ k, IsIntegral ℤ (((∏ j, m j : ℕ) : E) * ε k)` using `fun k => by`.

Take `⟨c, hc⟩ : m k ∣ ∏ j, m j` from `Finset.dvd_prod_of_mem m (Finset.mem_univ k)`. Establish `: ((∏ j, m j : ℕ) : E) * ε k = (c : E) * ((m k : E) * ε k)`. Rewrite using `[hc, Nat.cast_mul]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[this]`.

Conclude with `(isIntegral_natCast c : IsIntegral ℤ (c : E)).mul (hmi k)`. Establish `hdx : ((M * ∏ k, m k : ℕ) : E) * x = ∑ k, algebraMap F E ((M : F) * ε.repr x k) * (((∏ j, m j : ℕ) : E) * ε k)` using `by conv_lhs => rw [← ε.sum_repr x]`. Rewrite using `[Finset.mul_sum]`. Use `Finset.sum_congr rfl fun k _ => ?_` and prove the remaining obligations. Rewrite using `[Algebra.smul_def, map_mul, map_natCast, Nat.cast_mul]`.

Expand and normalize the polynomial expressions, which then agree. Establish `hint : IsIntegral ℤ (((M * ∏ k, m k : ℕ) : E) * x)`. Rewrite using `[hdx]`. Conclude with `IsIntegral.sum _ fun k _ => (hcoord k).algebraMap.mul (hP k)`. Take `⟨y, hy⟩` from `(IsIntegralClosure.isIntegral_iff (A := 𝓞 E)).1 hint`.

Conclude with `⟨y, hy.symm⟩`.
-/
theorem exists_denominator_of_isCompact : ∀ (F E : Type) [Field F] [NumberField F] [Field E]
    [NumberField E] [Algebra F E] (C : Set (Af F ⊗[F] E)), IsCompact C →
    ∃ d : ℕ, 0 < d ∧ ∀ x : E, (1 : Af F) ⊗ₜ[F] x ∈ C → ∃ y : 𝓞 E, (d : E) * x = y := by
  intro F E _ _ _ _ _ C hC
  have : IsModuleTopology (Af F) (Af F ⊗[F] E) := ⟨rfl⟩
  let ε := Module.finBasis F E
  let b := Algebra.TensorProduct.basis (Af F) ε
  have hcont : ∀ k, Continuous (b.coord k) := fun k =>
    IsModuleTopology.continuous_of_linearMap (b.coord k)
  have hK : IsCompact (⋃ k, (b.coord k) '' C) :=
    isCompact_iUnion fun k => hC.image (hcont k)
  obtain ⟨M, hM, hMK⟩ := exists_common_denominator F _ hK

  have : Algebra.IsAlgebraic ℤ E :=
    (IsFractionRing.comap_isAlgebraic_iff (A := ℤ) (K := ℚ) (C := E)).2 inferInstance
  have hm : ∀ k, ∃ m : ℕ, 0 < m ∧ IsIntegral ℤ ((m : E) * ε k) := fun k => by
    obtain ⟨m, y, hm, hmy⟩ := IsAlgebraic.exists_nsmul_eq (𝓞 E)
      (Algebra.IsAlgebraic.isAlgebraic (R := ℤ) (ε k))
    refine ⟨m, Nat.pos_of_ne_zero hm, ?_⟩
    rw [← nsmul_eq_mul, hmy]
    exact RingOfIntegers.isIntegral_coe y
  choose m hm0 hmi using hm
  refine ⟨M * ∏ k, m k, Nat.mul_pos hM (Finset.prod_pos fun k _ => hm0 k), fun x hx => ?_⟩

  have hcoord : ∀ k, IsIntegral ℤ ((M : F) * ε.repr x k) := fun k => by
    have hmem : b.coord k ((1 : Af F) ⊗ₜ[F] x) ∈ ⋃ k, (b.coord k) '' C :=
      Set.mem_iUnion.2 ⟨k, Set.mem_image_of_mem _ hx⟩
    have hrepr : b.coord k ((1 : Af F) ⊗ₜ[F] x) = algebraMap F (Af F) (ε.repr x k) := by
      simp [b, Module.Basis.coord_apply, Algebra.TensorProduct.basis_repr_tmul]
    have h := hMK _ hmem
    rw [hrepr, ← map_natCast (algebraMap F (Af F)) M, ← map_mul] at h
    obtain ⟨y, hy⟩ := (GlobalTheory.IntegralFinAdele.integral_finiteAdele_properties F).2.2.2.1 _ h
    rw [hy]
    exact RingOfIntegers.isIntegral_coe y

  have hP : ∀ k, IsIntegral ℤ (((∏ j, m j : ℕ) : E) * ε k) := fun k => by
    obtain ⟨c, hc⟩ : m k ∣ ∏ j, m j := Finset.dvd_prod_of_mem m (Finset.mem_univ k)
    have : ((∏ j, m j : ℕ) : E) * ε k = (c : E) * ((m k : E) * ε k) := by
      rw [hc, Nat.cast_mul]; ring
    rw [this]
    exact (isIntegral_natCast c : IsIntegral ℤ (c : E)).mul (hmi k)
  have hdx : ((M * ∏ k, m k : ℕ) : E) * x =
      ∑ k, algebraMap F E ((M : F) * ε.repr x k) * (((∏ j, m j : ℕ) : E) * ε k) := by
    conv_lhs => rw [← ε.sum_repr x]
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Algebra.smul_def, map_mul, map_natCast, Nat.cast_mul]
    ring
  have hint : IsIntegral ℤ (((M * ∏ k, m k : ℕ) : E) * x) := by
    rw [hdx]
    exact IsIntegral.sum _ fun k _ => (hcoord k).algebraMap.mul (hP k)
  obtain ⟨y, hy⟩ := (IsIntegralClosure.isIntegral_iff (A := 𝓞 E)).1 hint
  exact ⟨y, hy.symm⟩

end GlobalTheory.CompanionTheory.AdelicDenom

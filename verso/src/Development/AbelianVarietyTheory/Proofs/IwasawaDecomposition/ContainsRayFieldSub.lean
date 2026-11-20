import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FixedCoefficientFieldInComplex
import Development.AbelianVarietyTheory.Definitions.HeightFunctions.JointQ
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CmQuadraticFormEqAlternatingForm
import Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsImagQuadraticHost
import Development.AbelianVarietyTheory.Proofs.HeightProofs.PrincipalRayPrimesSplitCompletelyWeberValuesStatement
import Development.AbelianVarietyTheory.Proofs.HeightProofs.CompleteSplittingCompositumDegreeOnePrimeStatement
import Development.AbelianVarietyTheory.Proofs.HeightProofs.LeOfFiniteSplitNotSplitBauer
import Development.AbelianVarietyTheory.Proofs.HeightProofs.WeberInvariantTorsionValuesSubsetOfContainsRayFi
import Development.AbelianVarietyTheory.Proofs.HeightProofs.ContainsRayFieldOfRay
import Development.AbelianVarietyTheory.Proofs.HeightProofs.ContainsRayFieldComp

set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.Host GlobalTheory.NT GlobalTheory.Mem GlobalTheory.Mem.Fld GlobalTheory.FieldSize
open scoped IntermediateField

namespace GlobalTheory.FieldSize.WeberRay

/- English proof (translation)
Take `⟨hm, hNF, hray⟩` from `δ.isRay`. Use `letI := algOf P.host.φ₀ δ.ray hm`. Take `⟨hab, hun, -, hart⟩` from `hray`. Use `haveI : IsGalois P.host.E δ.ray := hab.toIsGalois`. Establish `hC : GlobalTheory.IndefiniteRowSideFullHecke.RayFieldTheta.ContainsRayField (algebraMap P.host.E δ.ray) (modulus P)` using `GlobalTheory.FieldSize.RayNorm.containsRayField_of_ray (modulus P) hun (fun I hI hc => (hart I hI hc).1)`.

Set `e : P.host.E ≃ₐ[ℚ] P.host.φ₀.toRatAlgHom.fieldRange` to `AlgEquiv.ofInjectiveField P.host.φ₀.toRatAlgHom`. Set `φKE : K →+* P.host.E` to `((e.symm : P.host.φ₀.toRatAlgHom.fieldRange ≃+* P.host.E) : P.host.φ₀.toRatAlgHom.fieldRange →+* P.host.E).comp (IntermediateField.inclusion hKE).toRingHom`. Establish `hcomp : (algebraMap P.host.E δ.ray).comp φKE = (IntermediateField.inclusion hKR).toRingHom`. Use `RingHom.ext fun x => Subtype.ext ?_` and prove the remaining obligations. Use `congrArg Subtype.val (e.apply_symm_apply (IntermediateField.inclusion hKE x))` as an intermediate fact.

Conclude with `this`. Rewrite using `[← hcomp]`. Conclude with `GlobalTheory.RayDescent.containsRayField_comp K P.host.E δ.ray φKE _ _ hC`.
-/
theorem containsRayField_sub (P : Pre) (δ : FieldDat P) (K : IntermediateField ℚ ℂ) [NumberField K]
    (hKE : K ≤ P.host.φ₀.toRatAlgHom.fieldRange) (hKR : K ≤ δ.ray) :
    GlobalTheory.IndefiniteRowSideFullHecke.RayFieldTheta.ContainsRayField (IntermediateField.inclusion hKR).toRingHom (modulus P) := by
  obtain ⟨hm, hNF, hray⟩ := δ.isRay
  letI := algOf P.host.φ₀ δ.ray hm
  obtain ⟨hab, hun, -, hart⟩ := hray
  haveI : IsGalois P.host.E δ.ray := hab.toIsGalois
  have hC : GlobalTheory.IndefiniteRowSideFullHecke.RayFieldTheta.ContainsRayField (algebraMap P.host.E δ.ray) (modulus P) :=
    GlobalTheory.FieldSize.RayNorm.containsRayField_of_ray (modulus P) hun (fun I hI hc => (hart I hI hc).1)
  let e : P.host.E ≃ₐ[ℚ] P.host.φ₀.toRatAlgHom.fieldRange := AlgEquiv.ofInjectiveField P.host.φ₀.toRatAlgHom
  let φKE : K →+* P.host.E :=
    ((e.symm : P.host.φ₀.toRatAlgHom.fieldRange ≃+* P.host.E) : P.host.φ₀.toRatAlgHom.fieldRange →+* P.host.E).comp
      (IntermediateField.inclusion hKE).toRingHom
  have hcomp : (algebraMap P.host.E δ.ray).comp φKE = (IntermediateField.inclusion hKR).toRingHom := by
    refine RingHom.ext fun x => Subtype.ext ?_
    have := congrArg Subtype.val (e.apply_symm_apply (IntermediateField.inclusion hKE x))
    exact this
  rw [← hcomp]
  exact GlobalTheory.RayDescent.containsRayField_comp K P.host.E δ.ray φKE _ _ hC

/- English proof (translation)
Introduce `P δ L hL n _ hn hdvd`. Take `⟨K, hKN, hKT, h2, -, hd, hKE, hlat, -⟩` from `GlobalTheory.FieldSize.exists_hostK P.R P.host`. Establish `hP : ∀ z, z ∈ L.lattice ↔ ∃ a : 𝓞 K, ((a : K) : ℂ) = z` using `fun z => (hL z).trans (hlat z)`. Establish `hKR : K ≤ δ.ray` using `fun z hz => by`. Take `⟨x, rfl⟩` from `hKE hz`.

Conclude with `δ.isRay.emb_mem x`. Establish `hCK` using `containsRayField_sub P δ K hKE hKR`. Take `⟨inst, S, hS⟩` from `GlobalTheory.T.principalRayPrimes_splitCompletely_weberValues K h2 hd L hP n hn`. Use `haveI := GlobalTheory.FieldSize.WeberIn.numberField_adjoin K δ.ray (weberSet L n)`. Establish `hm0 : ((modulus P : ℕ) : 𝓞 δ.ray) ≠ 0`.

Conclude with `modulus_ne_zero P` after adjusting the coercions. Use `haveI : NumberField (⊥ : IntermediateField δ.ray ℂ) := NumberField.of_module_finite δ.ray _`. Establish `hle : IntermediateField.adjoin δ.ray (weberSet L n) ≤ ⊥`. Use `GlobalTheory.Bauer.le_of_finite_split_not_split δ.ray ℂ ⊥ (IntermediateField.adjoin δ.ray (weberSet L n)) ?_` and prove the remaining obligations. Use `((WeberIn.finite_mem hm0).union (WeberIn.finite_norm_mem S)).subset ?_` and prove the remaining obligations.

Introduce and unpack `𝔓 ⟨hp, -, hnot⟩`. Assume the negation of the conclusion as `hc`. Simplify using `only [Set.mem_union, Set.mem_setOf_eq, not_or] at hc`. Take `⟨f, α, hN, hα, h1⟩` from `hCK 𝔓 hc.1`. Establish `h1' : (n : 𝓞 K) ∣ α - 1` using `(Nat.cast_dvd_cast hdvd).trans h1`.

Establish `hf : f = 1`. Establish `hp'` using `hp`. Rewrite `hp'` using `[hN]`. Conclude with `hp'.eq_one_of_pow`. Substitute `hf` using the available equality.

Rewrite `hN`, `hα` using `[pow_one]`. Establish `hne : 𝔓.asIdeal.comap (RingOfIntegers.mapRingHom (IntermediateField.inclusion hKR).toRingHom) ≠ ⊥`. Introduce `h0`. Rewrite `hN` using `[h0, Ideal.absNorm_bot]`. Conclude with `hp.ne_zero hN`.

Use `haveI := 𝔓.isPrime`. Set `𝔭 : HeightOneSpectrum (𝓞 K)` to `⟨𝔓.asIdeal.comap (RingOfIntegers.mapRingHom (IntermediateField.inclusion hKR).toRingHom), Ideal.comap_isPrime _ _, hne⟩`. Apply `hnot` to reduce the goal to its premises. Use `GlobalTheory.T.completeSplitting_compositum_degreeOnePrime K δ.ray hKR (weberSet L n) 𝔭 𝔓 rfl hN ?_` and prove the remaining obligations. Establish `h𝔭 : 𝔭.asIdeal = Ideal.span {α}` using `hα`.

Rewrite using `[h𝔭]`. Conclude with `hS α _ hp hc.2 (by rw [← hα, ← hN]) (Ideal.mem_span_singleton.2 h1')`. Introduce `x hx`. Establish `hx'` using `hle (IntermediateField.subset_adjoin δ.ray _ hx)`. Take `⟨y, rfl⟩` from `IntermediateField.mem_bot.1 hx'`.

Conclude with `y.2`.
-/
theorem weberSet_subset_ray : ∀ (P : Pre) (δ : FieldDat P) (L : PeriodPair), (∀ z, z ∈ L.lattice ↔ ∃ s : ℤ × ℤ, z = s.1 + s.2 * ((1 + P.host.φ₀ P.host.sqrtMinusD) / 2)) → ∀ n : ℕ, Odd n → 3 ≤ n → n ∣ modulus P → weberSet L n ⊆ δ.ray := by
  intro P δ L hL n _ hn hdvd
  obtain ⟨K, hKN, hKT, h2, -, hd, hKE, hlat, -⟩ := GlobalTheory.FieldSize.exists_hostK P.R P.host
  have hP : ∀ z, z ∈ L.lattice ↔ ∃ a : 𝓞 K, ((a : K) : ℂ) = z := fun z => (hL z).trans (hlat z)
  have hKR : K ≤ δ.ray := fun z hz => by
    obtain ⟨x, rfl⟩ := hKE hz
    exact δ.isRay.emb_mem x
  have hCK := containsRayField_sub P δ K hKE hKR
  obtain ⟨inst, S, hS⟩ := GlobalTheory.T.principalRayPrimes_splitCompletely_weberValues K h2 hd L hP n hn
  haveI := GlobalTheory.FieldSize.WeberIn.numberField_adjoin K δ.ray (weberSet L n)
  have hm0 : ((modulus P : ℕ) : 𝓞 δ.ray) ≠ 0 := by
    exact_mod_cast modulus_ne_zero P
  haveI : NumberField (⊥ : IntermediateField δ.ray ℂ) := NumberField.of_module_finite δ.ray _
  have hle : IntermediateField.adjoin δ.ray (weberSet L n) ≤ ⊥ := by
    refine GlobalTheory.Bauer.le_of_finite_split_not_split δ.ray ℂ ⊥ (IntermediateField.adjoin δ.ray (weberSet L n)) ?_
    refine ((WeberIn.finite_mem hm0).union (WeberIn.finite_norm_mem S)).subset ?_
    rintro 𝔓 ⟨hp, -, hnot⟩
    by_contra hc
    simp only [Set.mem_union, Set.mem_setOf_eq, not_or] at hc
    obtain ⟨f, α, hN, hα, h1⟩ := hCK 𝔓 hc.1
    have h1' : (n : 𝓞 K) ∣ α - 1 := (Nat.cast_dvd_cast hdvd).trans h1
    have hf : f = 1 := by
      have hp' := hp
      rw [hN] at hp'
      exact hp'.eq_one_of_pow
    subst hf
    rw [pow_one] at hN hα
    have hne : 𝔓.asIdeal.comap (RingOfIntegers.mapRingHom (IntermediateField.inclusion hKR).toRingHom) ≠ ⊥ := by
      intro h0
      rw [h0, Ideal.absNorm_bot] at hN
      exact hp.ne_zero hN
    haveI := 𝔓.isPrime
    let 𝔭 : HeightOneSpectrum (𝓞 K) :=
      ⟨𝔓.asIdeal.comap (RingOfIntegers.mapRingHom (IntermediateField.inclusion hKR).toRingHom),
        Ideal.comap_isPrime _ _, hne⟩
    apply hnot
    refine GlobalTheory.T.completeSplitting_compositum_degreeOnePrime K δ.ray hKR (weberSet L n) 𝔭 𝔓 rfl hN ?_
    have h𝔭 : 𝔭.asIdeal = Ideal.span {α} := hα
    rw [h𝔭]
    exact hS α _ hp hc.2 (by rw [← hα, ← hN]) (Ideal.mem_span_singleton.2 h1')
  intro x hx
  have hx' := hle (IntermediateField.subset_adjoin δ.ray _ hx)
  obtain ⟨y, rfl⟩ := IntermediateField.mem_bot.1 hx'
  exact y.2

end GlobalTheory.FieldSize.WeberRay

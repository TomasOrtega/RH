import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.BijectiveAlgebraMapIntegralClosureOfBirational
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.MemPadicAlgClValuationSubringIffNormLeOne

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
local notation "OO" p:max => (Valuation.valuationSubring (Valued.v : Valuation (PadicAlgCl p) NNReal))
local notation "cPt" p:max => (IsLocalRing.closedPoint (OO p) : Sp (OO p))
local notation "gPt" p:max => spMap (ValuationSubring.subtype (OO p))

namespace GlobalTheory

/- English proof (translation)
Use `haveI := RingHom.ker_isPrime φ`. Take `⟨Q, -, hQ, hQP⟩` from `Ideal.exists_ideal_over_prime_of_isIntegral (S := B) (RingHom.ker φ) ⊥ (by`. Rewrite using `[Ideal.comap_bot_of_injective _ (FaithfulSMul.algebraMap_injective R B)]`. Conclude with `bot_le)`. Use `haveI : Q.LiesOver (RingHom.ker φ) := ⟨hQP.symm⟩`.

Use `letI : Algebra (R ⧸ RingHom.ker φ) Ω := (RingHom.kerLift φ).toAlgebra`. Use `haveI : FaithfulSMul (R ⧸ RingHom.ker φ) Ω := (faithfulSMul_iff_algebraMap_injective _ _).mpr (RingHom.kerLift_injective φ)`. Use `haveI : Module.IsTorsionFree (R ⧸ RingHom.ker φ) Ω := FaithfulSMul.to_isTorsionFree _ _`. Use `haveI : Module.IsTorsionFree (R ⧸ RingHom.ker φ) (B ⧸ Q) := FaithfulSMul.to_isTorsionFree _ _`. Use `haveI : Algebra.IsIntegral (R ⧸ RingHom.ker φ) (B ⧸ Q) := Algebra.IsIntegral.tower_top (R := R)`.

Use `haveI : Algebra.IsAlgebraic (R ⧸ RingHom.ker φ) (B ⧸ Q) := Algebra.IsIntegral.isAlgebraic`. Set `σ : (B ⧸ Q) →ₐ[R ⧸ RingHom.ker φ] Ω` to `IsAlgClosed.lift`. Use `⟨σ.toRingHom.comp (Ideal.Quotient.mk Q), RingHom.ext fun r => ?_⟩` and prove the remaining obligations. Conclude with `(σ.commutes (Ideal.Quotient.mk _ r)).trans (RingHom.kerLift_mk φ r)`.
-/
theorem exists_ringHom_extend_of_isIntegral_of_injective {R B Ω : Type*} [CommRing R] [CommRing B]
    [Algebra R B] [Algebra.IsIntegral R B] [FaithfulSMul R B] [Field Ω] [IsAlgClosed Ω]
    (φ : R →+* Ω) : ∃ ψ : B →+* Ω, ψ.comp (algebraMap R B) = φ := by
  haveI := RingHom.ker_isPrime φ
  obtain ⟨Q, -, hQ, hQP⟩ := Ideal.exists_ideal_over_prime_of_isIntegral (S := B)
    (RingHom.ker φ) ⊥ (by
      rw [Ideal.comap_bot_of_injective _ (FaithfulSMul.algebraMap_injective R B)]
      exact bot_le)
  haveI : Q.LiesOver (RingHom.ker φ) := ⟨hQP.symm⟩
  letI : Algebra (R ⧸ RingHom.ker φ) Ω := (RingHom.kerLift φ).toAlgebra
  haveI : FaithfulSMul (R ⧸ RingHom.ker φ) Ω :=
    (faithfulSMul_iff_algebraMap_injective _ _).mpr (RingHom.kerLift_injective φ)
  haveI : Module.IsTorsionFree (R ⧸ RingHom.ker φ) Ω := FaithfulSMul.to_isTorsionFree _ _
  haveI : Module.IsTorsionFree (R ⧸ RingHom.ker φ) (B ⧸ Q) := FaithfulSMul.to_isTorsionFree _ _
  haveI : Algebra.IsIntegral (R ⧸ RingHom.ker φ) (B ⧸ Q) :=
    Algebra.IsIntegral.tower_top (R := R)
  haveI : Algebra.IsAlgebraic (R ⧸ RingHom.ker φ) (B ⧸ Q) := Algebra.IsIntegral.isAlgebraic
  let σ : (B ⧸ Q) →ₐ[R ⧸ RingHom.ker φ] Ω := IsAlgClosed.lift
  refine ⟨σ.toRingHom.comp (Ideal.Quotient.mk Q), RingHom.ext fun r => ?_⟩
  exact (σ.commutes (Ideal.Quotient.mk _ r)).trans (RingHom.kerLift_mk φ r)

/- English proof (translation)
Set `K` to `FractionRing R`. Set `L` to `AlgebraicClosure K`. Establish `hRL : Function.Injective (algebraMap R L)`. Rewrite using `[IsScalarTower.algebraMap_eq R K L]`. Conclude with `(algebraMap K L).injective.comp (IsFractionRing.injective R K)`.

Use `haveI : FaithfulSMul R L := (faithfulSMul_iff_algebraMap_injective _ _).mpr hRL`. Use `haveI : Module.IsTorsionFree R L := FaithfulSMul.to_isTorsionFree _ _`. Establish `hex : ∀ Q : Ideal A, Q.IsPrime → Q.comap (algebraMap R A) = ⊥ → ∃ σ : A →ₐ[R] L, RingHom.ker σ = Q`. Introduce `Q hQ hQ0`. Establish `hinj : Function.Injective (algebraMap R (A ⧸ Q))`.

Rewrite using `[injective_iff_map_eq_zero]`. Introduce `r hr`. Establish `: r ∈ Q.comap (algebraMap R A)`. Rewrite using `[Ideal.mem_comap, ← Ideal.Quotient.eq_zero_iff_mem]`. Conclude with `hr`.

Rewrite `this` using `[hQ0, Ideal.mem_bot]`. Then use the resulting hypothesis. Use `haveI : FaithfulSMul R (A ⧸ Q) := (faithfulSMul_iff_algebraMap_injective _ _).mpr hinj`. Use `haveI : Module.IsTorsionFree R (A ⧸ Q) := FaithfulSMul.to_isTorsionFree R _`. Set `σ₀ : (A ⧸ Q) →ₐ[R] L` to `IsAlgClosed.lift`. Establish `h₀ : Function.Injective σ₀`.

Rewrite using `[injective_iff_map_eq_zero]`. Introduce `a ha`. Assume the negation of the conclusion as `h`. Take `⟨r, hr, c, hc⟩` from `(Algebra.IsIntegral.isIntegral (R := R) a).isAlgebraic.exists_nonzero_dvd (mem_nonZeroDivisors_of_ne_zero h)`. Apply `hr` to reduce the goal to its premises.

Apply `hRL` to reduce the goal to its premises. Rewrite using `[map_zero, ← σ₀.commutes, hc, map_mul, ha, zero_mul]`. Use `⟨σ₀.comp (Ideal.Quotient.mkₐ R Q), ?_⟩` and prove the remaining obligations. Use extensionality with `a`. Rewrite using `[RingHom.mem_ker, ← Ideal.Quotient.eq_zero_iff_mem]`.

Conclude with `map_eq_zero_iff σ₀ h₀`. Take `⟨M, hM⟩` from `Ideal.exists_maximal A`. Take `⟨Q₀, hQ₀, -, hQ₀0⟩` from `hgen M hM.isPrime`. Take `⟨σ, -⟩` from `hex Q₀ hQ₀ hQ₀0`. Establish `hσ : Function.Injective σ`.

Rewrite using `[injective_iff_map_eq_zero]`. Introduce `a ha`. Apply `IsNilpotent.eq_zero` to reduce the goal to its premises. Rewrite using `[← mem_nilradical, nilradical_eq_sInf, Submodule.mem_sInf]`. Introduce `P hP`.

Take `⟨Q, hQ, hQP, hQ0⟩` from `hgen P hP`. Take `⟨τ, hτ⟩` from `hex Q hQ hQ0`. Apply `hQP` to reduce the goal to its premises. Rewrite using `[← hτ, huniq τ σ]`. Conclude with `ha`.

Prove the components needed by the constructor for the conclusion. Introduce `r s h`. Apply `hRL` to reduce the goal to its premises. Rewrite using `[← σ.commutes, ← σ.commutes, h]`. Introduce `a`.

Take `⟨k, hk⟩` from `(InfiniteGalois.mem_range_algebraMap_iff_fixed (k := K) (σ a)).2 fun g => DFunLike.congr_fun (huniq ((g.toAlgHom.restrictScalars R).comp σ) σ) a`. Establish `hint : IsIntegral R k`. Rewrite using `[← isIntegral_algebraMap_iff (algebraMap K L).injective, hk]`. Conclude with `(Algebra.IsIntegral.isIntegral (R := R) a).map σ`. Take `⟨r, hr⟩` from `IsIntegrallyClosed.isIntegral_iff.mp hint`.

Use `⟨r, hσ ?_⟩` and prove the remaining obligations. Rewrite using `[σ.commutes, ← hk, ← hr, ← IsScalarTower.algebraMap_apply]`.
-/
theorem bijective_algebraMap_of_subsingleton_algHom {R A : Type*} [CommRing R] [IsDomain R]
    [IsIntegrallyClosed R] [CharZero R] [CommRing A] [IsReduced A] [Nontrivial A] [Algebra R A]
    [Algebra.IsIntegral R A]
    (hgen : ∀ P : Ideal A, P.IsPrime → ∃ Q : Ideal A, Q.IsPrime ∧ Q ≤ P ∧
      Q.comap (algebraMap R A) = ⊥)
    (huniq : ∀ σ τ : A →ₐ[R] AlgebraicClosure (FractionRing R), σ = τ) :
    Function.Bijective (algebraMap R A) := by
  let K := FractionRing R
  let L := AlgebraicClosure K
  have hRL : Function.Injective (algebraMap R L) := by
    rw [IsScalarTower.algebraMap_eq R K L]
    exact (algebraMap K L).injective.comp (IsFractionRing.injective R K)
  haveI : FaithfulSMul R L := (faithfulSMul_iff_algebraMap_injective _ _).mpr hRL
  haveI : Module.IsTorsionFree R L := FaithfulSMul.to_isTorsionFree _ _
  have hex : ∀ Q : Ideal A, Q.IsPrime → Q.comap (algebraMap R A) = ⊥ →
      ∃ σ : A →ₐ[R] L, RingHom.ker σ = Q := by
    intro Q hQ hQ0
    have hinj : Function.Injective (algebraMap R (A ⧸ Q)) := by
      rw [injective_iff_map_eq_zero]
      intro r hr
      have : r ∈ Q.comap (algebraMap R A) := by
        rw [Ideal.mem_comap, ← Ideal.Quotient.eq_zero_iff_mem]
        exact hr
      rwa [hQ0, Ideal.mem_bot] at this
    haveI : FaithfulSMul R (A ⧸ Q) := (faithfulSMul_iff_algebraMap_injective _ _).mpr hinj
    haveI : Module.IsTorsionFree R (A ⧸ Q) := FaithfulSMul.to_isTorsionFree R _
    let σ₀ : (A ⧸ Q) →ₐ[R] L := IsAlgClosed.lift
    have h₀ : Function.Injective σ₀ := by
      rw [injective_iff_map_eq_zero]
      intro a ha
      by_contra h
      obtain ⟨r, hr, c, hc⟩ := (Algebra.IsIntegral.isIntegral (R := R) a).isAlgebraic.exists_nonzero_dvd
        (mem_nonZeroDivisors_of_ne_zero h)
      apply hr
      apply hRL
      rw [map_zero, ← σ₀.commutes, hc, map_mul, ha, zero_mul]
    refine ⟨σ₀.comp (Ideal.Quotient.mkₐ R Q), ?_⟩
    ext a
    rw [RingHom.mem_ker, ← Ideal.Quotient.eq_zero_iff_mem]
    exact map_eq_zero_iff σ₀ h₀
  obtain ⟨M, hM⟩ := Ideal.exists_maximal A
  obtain ⟨Q₀, hQ₀, -, hQ₀0⟩ := hgen M hM.isPrime
  obtain ⟨σ, -⟩ := hex Q₀ hQ₀ hQ₀0
  have hσ : Function.Injective σ := by
    rw [injective_iff_map_eq_zero]
    intro a ha
    apply IsNilpotent.eq_zero
    rw [← mem_nilradical, nilradical_eq_sInf, Submodule.mem_sInf]
    intro P hP
    obtain ⟨Q, hQ, hQP, hQ0⟩ := hgen P hP
    obtain ⟨τ, hτ⟩ := hex Q hQ hQ0
    apply hQP
    rw [← hτ, huniq τ σ]
    exact ha
  constructor
  · intro r s h
    apply hRL
    rw [← σ.commutes, ← σ.commutes, h]
  · intro a
    obtain ⟨k, hk⟩ := (InfiniteGalois.mem_range_algebraMap_iff_fixed (k := K) (σ a)).2 fun g =>
      DFunLike.congr_fun (huniq ((g.toAlgHom.restrictScalars R).comp σ) σ) a
    have hint : IsIntegral R k := by
      rw [← isIntegral_algebraMap_iff (algebraMap K L).injective, hk]
      exact (Algebra.IsIntegral.isIntegral (R := R) a).map σ
    obtain ⟨r, hr⟩ := IsIntegrallyClosed.isIntegral_iff.mp hint
    refine ⟨r, hσ ?_⟩
    rw [σ.commutes, ← hk, ← hr, ← IsScalarTower.algebraMap_apply]

/- English proof (translation)
Set `K` to `FractionRing R`. Set `L` to `AlgebraicClosure K`. Establish `hRL : Function.Injective (algebraMap R L)`. Rewrite using `[IsScalarTower.algebraMap_eq R K L]`. Conclude with `(algebraMap K L).injective.comp (IsFractionRing.injective R K)`.

Set `B` to `integralClosure R L`. Use `haveI : FaithfulSMul R B := (faithfulSMul_iff_algebraMap_injective _ _).mpr fun r s h => hRL congr(($h).1)`. Set `c (ρ : A →ₐ[R] L) : A →ₐ[R] B` to `ρ.codRestrict B fun a => (Algebra.IsIntegral.isIntegral (R := R) a).map ρ`. Take `⟨a, ha⟩` from `DFunLike.ne_iff.mp hne`. Establish `hb : c σ a - c τ a ≠ 0` using `fun h => ha congr(($(sub_eq_zero.mp h)).1)`.

Take `⟨r, hr, d, hd⟩` from `(Algebra.IsIntegral.isIntegral (R := R) (c σ a - c τ a)).isAlgebraic.exists_nonzero_dvd (mem_nonZeroDivisors_of_ne_zero hb)`. Use `⟨r, hr, fun Ω _ _ O φ hφ => ?_⟩` and prove the remaining obligations. Take `⟨χ, hχ⟩` from `exists_ringHom_extend_of_isIntegral_of_injective (B := B) (O.subtype.comp φ)`. Establish `hχ' (s : R) : χ (algebraMap R B s) = φ s` using `DFunLike.congr_fun hχ s`. Establish `hmem (b : B) : χ b ∈ O`.

Establish `h₁ : IsIntegral O (χ b)` using `(Algebra.IsIntegral.isIntegral (R := R) b).map_of_comp_eq φ χ hχ.symm`. Take `⟨o, ho⟩` from `IsIntegrallyClosed.isIntegral_iff.mp h₁`. Conclude with `ho ▸ o.2`. Set `χ' : B →+* O` to `χ.codRestrict O hmem`. Establish `hcomp (ρ : A →ₐ[R] L) : (χ'.comp (c ρ).toRingHom).comp (algebraMap R A) = φ`.

Use `RingHom.ext fun s => Subtype.ext ?_` and prove the remaining obligations. Conclude with `(congrArg χ ((c ρ).commutes s)).trans (hχ' s)`. Use `⟨_, _, hcomp σ, hcomp τ, fun h => hφ (Subtype.ext ?_)⟩` and prove the remaining obligations. Establish `h₂ : χ (c σ a) = χ (c τ a)` using `congr((($h) a).1)`. Rewrite using `[← hχ', hd, map_mul, map_sub, h₂, sub_self, zero_mul]`.

Both sides reduce to the same expression.
-/
theorem exists_ne_zero_forall_exists_two_lifts {R A : Type*} [CommRing R] [IsDomain R]
    [CommRing A] [Algebra R A] [Algebra.IsIntegral R A]
    (σ τ : A →ₐ[R] AlgebraicClosure (FractionRing R)) (hne : σ ≠ τ) :
    ∃ r : R, r ≠ 0 ∧ ∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] (O : ValuationSubring Ω)
      (φ : R →+* O), φ r ≠ 0 → ∃ ψ ψ' : A →+* O, ψ.comp (algebraMap R A) = φ ∧
        ψ'.comp (algebraMap R A) = φ ∧ ψ ≠ ψ' := by
  let K := FractionRing R
  let L := AlgebraicClosure K
  have hRL : Function.Injective (algebraMap R L) := by
    rw [IsScalarTower.algebraMap_eq R K L]
    exact (algebraMap K L).injective.comp (IsFractionRing.injective R K)
  let B := integralClosure R L
  haveI : FaithfulSMul R B := (faithfulSMul_iff_algebraMap_injective _ _).mpr
    fun r s h => hRL congr(($h).1)
  let c (ρ : A →ₐ[R] L) : A →ₐ[R] B :=
    ρ.codRestrict B fun a => (Algebra.IsIntegral.isIntegral (R := R) a).map ρ
  obtain ⟨a, ha⟩ := DFunLike.ne_iff.mp hne
  have hb : c σ a - c τ a ≠ 0 := fun h => ha congr(($(sub_eq_zero.mp h)).1)
  obtain ⟨r, hr, d, hd⟩ :=
    (Algebra.IsIntegral.isIntegral (R := R) (c σ a - c τ a)).isAlgebraic.exists_nonzero_dvd
      (mem_nonZeroDivisors_of_ne_zero hb)
  refine ⟨r, hr, fun Ω _ _ O φ hφ => ?_⟩
  obtain ⟨χ, hχ⟩ := exists_ringHom_extend_of_isIntegral_of_injective (B := B) (O.subtype.comp φ)
  have hχ' (s : R) : χ (algebraMap R B s) = φ s := DFunLike.congr_fun hχ s
  have hmem (b : B) : χ b ∈ O := by
    have h₁ : IsIntegral O (χ b) :=
      (Algebra.IsIntegral.isIntegral (R := R) b).map_of_comp_eq φ χ hχ.symm
    obtain ⟨o, ho⟩ := IsIntegrallyClosed.isIntegral_iff.mp h₁
    exact ho ▸ o.2
  let χ' : B →+* O := χ.codRestrict O hmem
  have hcomp (ρ : A →ₐ[R] L) : (χ'.comp (c ρ).toRingHom).comp (algebraMap R A) = φ := by
    refine RingHom.ext fun s => Subtype.ext ?_
    exact (congrArg χ ((c ρ).commutes s)).trans (hχ' s)
  refine ⟨_, _, hcomp σ, hcomp τ, fun h => hφ (Subtype.ext ?_)⟩
  have h₂ : χ (c σ a) = χ (c τ a) := congr((($h) a).1)
  rw [← hχ', hd, map_mul, map_sub, h₂, sub_self, zero_mul]
  rfl

/- English proof (translation)
Assemble the required witnesses or components as `⟨_, (genericPoints.ofComponent ⟨_, irreducibleComponent_mem_irreducibleComponents w⟩).2, (genericPoints.isGenericPoint_ofComponent ⟨_, irreducibleComponent_mem_irreducibleComponents w⟩).specializes mem_irreducibleComponent⟩`.
-/
theorem exists_mem_genericPoints_specializes {T : Type*} [TopologicalSpace T] [QuasiSober T]
    (w : T) : ∃ w₀ ∈ genericPoints T, w₀ ⤳ w :=
  ⟨_, (genericPoints.ofComponent ⟨_, irreducibleComponent_mem_irreducibleComponents w⟩).2,
    (genericPoints.isGenericPoint_ofComponent
      ⟨_, irreducibleComponent_mem_irreducibleComponents w⟩).specializes mem_irreducibleComponent⟩

/- English proof (translation)
Establish `hr : Set.range y ⊆ Set.range hV.fromSpec`. Rewrite using `[hV.range_fromSpec]`. Introduce and unpack `_ ⟨x, rfl⟩`. Establish `: y ⁻¹ᵁ V = ⊤` using `(IsLocalRing.closed_point_mem_iff).mp hz`. Conclude with `(this.ge (Set.mem_univ x) : x ∈ y ⁻¹ᵁ V)`.

Use `⟨Spec.preimage (IsOpenImmersion.lift hV.fromSpec y hr), ?_⟩` and prove the remaining obligations. Rewrite using `[Spec.map_preimage, IsOpenImmersion.lift_fac]`.
-/
theorem exists_factor_of_isLocalRing_of_mem_affineOpen {R : CommRingCat.{0}} [IsLocalRing R]
    {X : Scheme.{0}} (y : Spec R ⟶ X) {V : X.Opens} (hV : IsAffineOpen V)
    (hz : y (IsLocalRing.closedPoint R) ∈ V) :
    ∃ φ : Γ(X, V) ⟶ R, Spec.map φ ≫ hV.fromSpec = y := by
  have hr : Set.range y ⊆ Set.range hV.fromSpec := by
    rw [hV.range_fromSpec]
    rintro _ ⟨x, rfl⟩
    have : y ⁻¹ᵁ V = ⊤ := (IsLocalRing.closed_point_mem_iff).mp hz
    exact (this.ge (Set.mem_univ x) : x ∈ y ⁻¹ᵁ V)
  refine ⟨Spec.preimage (IsOpenImmersion.lift hV.fromSpec y hr), ?_⟩
  rw [Spec.map_preimage, IsOpenImmersion.lift_fac]

/- English proof (translation)
Introduce `X _ π _ _ hN W _ hW f _ hgen x U hx hU huniq`. Establish `hN' : ∀ y : X, IsIntegrallyClosed (X.presheaf.stalk y)` using `fun y => (hN y).2`. Take `⟨V, hV, hxV, -⟩` from `exists_isAffineOpen_mem_and_subset (U := ⊤) (x := x) trivial`. Use `haveI hVne : Nonempty V := ⟨⟨x, hxV⟩⟩`. Establish `hV' : IsAffineOpen (f ⁻¹ᵁ V)` using `hV.preimage f`.

Establish `hηV : genericPoint X ∈ V` using `((genericPoint_spec X).mem_open_set_iff V.isOpen).mpr ⟨x, trivial, hxV⟩`. Establish `hgenV : ∀ w ∈ genericPoints W, w ∈ f ⁻¹ᵁ V` using `fun w hw => by`. Express the relevant statement in the definitionally equal form `f w ∈ V`. Rewrite using `[hgen w hw]`. Conclude with `hηV`.

Take `⟨w₁, hw₁, -⟩` from `exists_mem_genericPoints_specializes hW.some`. Use `haveI : Nonempty (f ⁻¹ᵁ V) := ⟨⟨w₁, hgenV w₁ hw₁⟩⟩`. Use `letI := (f.app V).hom.toAlgebra`. Use `haveI : Module.Finite Γ(X, V) Γ(W, f ⁻¹ᵁ V) := f.finite_app V hV`. Use `haveI := isIntegrallyClosed_sections_of_stalks hN' hV`.

Establish `hsq : Spec.map (f.app V) ≫ hV.fromSpec = hV'.fromSpec ≫ f`. Rewrite using `[Scheme.Hom.app_eq_appLE]`. Conclude with `IsAffineOpen.SpecMap_appLE_fromSpec f hV hV' le_rfl`. Establish `hpt : ∀ r : Γ(X, V), r ≠ 0 → ∃ (p : ℕ) (_ : Fact p.Prime) (φ : Γ(X, V) ⟶ CommRingCat.of (OO p)), φ.hom r ≠ 0 ∧ (Spec.map φ ≫ hV.fromSpec) (cPt p) = x ∧ Set.range (gPt p ≫ Spec.map φ ≫ hV.fromSpec) ⊆ U`. Introduce `r hr`.

Establish `hb : (X.basicOpen r : Set X).Nonempty`. Rewrite using `[Set.nonempty_iff_ne_empty]`. Introduce `h`. Conclude with `hr ((basicOpen_eq_bot_iff r).mp (TopologicalSpace.Opens.ext h))`. Take `⟨p, hp, y, hy, hyU⟩` from `padicAlgCl_integral_points.1 X π x hx (U ⊓ X.basicOpen r) (nonempty_preirreducible_inter U.isOpen (X.basicOpen r).isOpen hU hb)`.

Take `⟨φ, rfl⟩` from `exists_factor_of_isLocalRing_of_mem_affineOpen (R := CommRingCat.of (OO p)) y hV (hy.symm ▸ hxV)`. Use `⟨p, hp, φ, fun h0 => ?_, hy, fun z hz => (hyU hz).1⟩` and prove the remaining obligations. Set `t : Sp (PadicAlgCl p)` to `IsLocalRing.closedPoint (PadicAlgCl p)`. Establish `h₁` using `(hyU ⟨t, rfl⟩).2`. Rewrite `h₁` using `[Scheme.Hom.comp_apply, Scheme.Hom.comp_apply, SetLike.mem_coe, ← Scheme.Hom.mem_preimage, hV.fromSpec_preimage_basicOpen]`.

Apply `h₁` to reduce the goal to its premises. Express the relevant statement in the definitionally equal form `φ.hom r ∈ ((gPt p) t).asIdeal`. Rewrite using `[h0]`. Conclude with `zero_mem _`. Use `haveI : CharZero Γ(X, V) := by`.

Take `⟨p, _, φ, -⟩` from `hpt 1 one_ne_zero`. Conclude with `φ.hom.charZero`. Establish `hbij : Function.Bijective (algebraMap Γ(X, V) Γ(W, f ⁻¹ᵁ V))`. Use `bijective_algebraMap_of_subsingleton_algHom (fun P hP => ?_) fun σ τ => ?_` and prove the remaining obligations. Set `P' : Spec Γ(W, f ⁻¹ᵁ V)` to `⟨P, hP⟩`.

Take `⟨w, hw, hwP⟩` from `exists_mem_genericPoints_specializes (hV'.fromSpec P')`. Take `⟨Q, rfl⟩ : w ∈ Set.range hV'.fromSpec` from `hV'.range_fromSpec.ge (hgenV w hw)`. Use `⟨Q.asIdeal, Q.isPrime, (PrimeSpectrum.le_iff_specializes Q P').mpr (hV'.fromSpec.isOpenEmbedding.isInducing.specializes_iff.mp hwP), ?_⟩` and prove the remaining obligations. Establish `h₁ : hV.fromSpec (Spec.map (f.app V) Q) = genericPoint X`. Rewrite using `[← Scheme.Hom.comp_apply, hsq, Scheme.Hom.comp_apply]`.

Conclude with `hgen _ hw`. Establish `h₂ : hV.fromSpec (Spec.map (f.app V) Q) ⤳ hV.fromSpec (⊥ : PrimeSpectrum Γ(X, V))` using `h₁ ▸ genericPoint_specializes _`. Conclude with `le_bot_iff.mp ((PrimeSpectrum.le_iff_specializes _ _).mpr (hV.fromSpec.isOpenEmbedding.isInducing.specializes_iff.mp h₂))`. Assume the negation of the conclusion as `hne`. Take `⟨r, hr, H⟩` from `exists_ne_zero_forall_exists_two_lifts σ τ hne`.

Take `⟨p, _, φ, hφ, hc, hg⟩` from `hpt r hr`. Take `⟨ψ, ψ', hψ, hψ', hne'⟩` from `H (PadicAlgCl p) (OO p) φ.hom hφ`. Establish `key : ∀ ρ : Γ(W, f ⁻¹ᵁ V) →+* OO p, ρ.comp (algebraMap Γ(X, V) Γ(W, f ⁻¹ᵁ V)) = φ.hom → (Spec.map (CommRingCat.ofHom ρ) ≫ hV'.fromSpec) ≫ f = Spec.map φ ≫ hV.fromSpec`. Introduce `ρ hρ`. Rewrite using `[Category.assoc, ← hsq, ← Spec.map_comp_assoc]`.

Use `congr 2`. Conclude with `CommRingCat.hom_ext hρ`. Establish `h` using `huniq p (Spec.map (CommRingCat.ofHom ψ) ≫ hV'.fromSpec) (Spec.map (CommRingCat.ofHom ψ') ≫ hV'.fromSpec) ((key ψ hψ).trans (key ψ' hψ').symm) (key ψ hψ ▸ hc) (key ψ hψ ▸ hg)`. Conclude with `hne' congr(($(Spec.map_injective ((cancel_mono hV'.fromSpec).mp h))).hom)`. Use `haveI : IsIso (f ∣_ V) := (isIso_morphismRestrict_iff_isIso_app f hV).mpr ((ConcreteCategory.isIso_iff_bijective _).mpr hbij)`.

Establish `hsub : ∀ w ∈ genericPoints W, w = w₁`. Introduce `w hw`. Establish `hinj : Function.Injective (f ∣_ V)` using `(f ∣_ V).isOpenEmbedding.injective`. Use `congrArg Subtype.val (hinj (a₁ := ⟨w, hgenV w hw⟩) (a₂ := ⟨w₁, hgenV w₁ hw₁⟩) ?_)` and prove the remaining obligations. Apply `Subtype.ext` to reduce the goal to its premises.

Conclude with `(morphismRestrict_base_coe f V _).trans (((hgen w hw).trans (hgen w₁ hw₁).symm).trans (morphismRestrict_base_coe f V ⟨w₁, hgenV w₁ hw₁⟩).symm)`. Use `haveI : IrreducibleSpace W := by`. Rewrite using `[irreducibleSpace_def]`. Establish `h : closure ({w₁} : Set W) = ⊤`. Use `Set.eq_univ_of_forall fun w => ?_` and prove the remaining obligations.

Take `⟨w₀, hw₀, h₀⟩` from `exists_mem_genericPoints_specializes w`. Conclude with `specializes_iff_mem_closure.mp (hsub w₀ hw₀ ▸ h₀)`. Conclude with `h ▸ isIrreducible_singleton.closure`. Use `haveI : IsIntegral W := isIntegral_of_irreducibleSpace_of_isReduced W`. Conclude with `isIso_of_isFinite_of_birational f hN' V hVne`.
-/
theorem isIso_of_isFinite_of_unique_lift_of_classical_points :
    ∀ (X : Scheme.{0}) [IsIntegral X] (π : X ⟶ Sp ℤ) [Flat π] [LocallyOfFiniteType π],
      IsNormalScheme X → ∀ (W : Scheme.{0}) [IsReduced W] [Nonempty W] (f : W ⟶ X) [IsFinite f],
        (∀ w ∈ genericPoints W, f w = genericPoint X) → ∀ (x : X) (U : X.Opens),
          IsClosed ({x} : Set X) → (U : Set X).Nonempty →
            (∀ (p : ℕ) [Fact p.Prime] (a a' : Sp (OO p) ⟶ W), a ≫ f = a' ≫ f →
              (a ≫ f) (cPt p) = x → Set.range (gPt p ≫ a ≫ f) ⊆ U → a = a') → IsIso f := by
  intro X _ π _ _ hN W _ hW f _ hgen x U hx hU huniq
  have hN' : ∀ y : X, IsIntegrallyClosed (X.presheaf.stalk y) := fun y => (hN y).2
  obtain ⟨V, hV, hxV, -⟩ := exists_isAffineOpen_mem_and_subset (U := ⊤) (x := x) trivial
  haveI hVne : Nonempty V := ⟨⟨x, hxV⟩⟩
  have hV' : IsAffineOpen (f ⁻¹ᵁ V) := hV.preimage f
  have hηV : genericPoint X ∈ V :=
    ((genericPoint_spec X).mem_open_set_iff V.isOpen).mpr ⟨x, trivial, hxV⟩
  have hgenV : ∀ w ∈ genericPoints W, w ∈ f ⁻¹ᵁ V := fun w hw => by
    change f w ∈ V
    rw [hgen w hw]
    exact hηV
  obtain ⟨w₁, hw₁, -⟩ := exists_mem_genericPoints_specializes hW.some
  haveI : Nonempty (f ⁻¹ᵁ V) := ⟨⟨w₁, hgenV w₁ hw₁⟩⟩
  letI := (f.app V).hom.toAlgebra
  haveI : Module.Finite Γ(X, V) Γ(W, f ⁻¹ᵁ V) := f.finite_app V hV
  haveI := isIntegrallyClosed_sections_of_stalks hN' hV
  have hsq : Spec.map (f.app V) ≫ hV.fromSpec = hV'.fromSpec ≫ f := by
    rw [Scheme.Hom.app_eq_appLE]
    exact IsAffineOpen.SpecMap_appLE_fromSpec f hV hV' le_rfl

  have hpt : ∀ r : Γ(X, V), r ≠ 0 → ∃ (p : ℕ) (_ : Fact p.Prime)
      (φ : Γ(X, V) ⟶ CommRingCat.of (OO p)), φ.hom r ≠ 0 ∧
        (Spec.map φ ≫ hV.fromSpec) (cPt p) = x ∧
          Set.range (gPt p ≫ Spec.map φ ≫ hV.fromSpec) ⊆ U := by
    intro r hr
    have hb : (X.basicOpen r : Set X).Nonempty := by
      rw [Set.nonempty_iff_ne_empty]
      intro h
      exact hr ((basicOpen_eq_bot_iff r).mp (TopologicalSpace.Opens.ext h))
    obtain ⟨p, hp, y, hy, hyU⟩ := padicAlgCl_integral_points.1 X π x hx (U ⊓ X.basicOpen r)
      (nonempty_preirreducible_inter U.isOpen (X.basicOpen r).isOpen hU hb)
    obtain ⟨φ, rfl⟩ := exists_factor_of_isLocalRing_of_mem_affineOpen
      (R := CommRingCat.of (OO p)) y hV (hy.symm ▸ hxV)
    refine ⟨p, hp, φ, fun h0 => ?_, hy, fun z hz => (hyU hz).1⟩
    let t : Sp (PadicAlgCl p) := IsLocalRing.closedPoint (PadicAlgCl p)
    have h₁ := (hyU ⟨t, rfl⟩).2
    rw [Scheme.Hom.comp_apply, Scheme.Hom.comp_apply, SetLike.mem_coe, ← Scheme.Hom.mem_preimage,
      hV.fromSpec_preimage_basicOpen] at h₁
    apply h₁
    change φ.hom r ∈ ((gPt p) t).asIdeal
    rw [h0]
    exact zero_mem _
  haveI : CharZero Γ(X, V) := by
    obtain ⟨p, _, φ, -⟩ := hpt 1 one_ne_zero
    exact φ.hom.charZero
  have hbij : Function.Bijective (algebraMap Γ(X, V) Γ(W, f ⁻¹ᵁ V)) := by
    refine bijective_algebraMap_of_subsingleton_algHom (fun P hP => ?_) fun σ τ => ?_
    · let P' : Spec Γ(W, f ⁻¹ᵁ V) := ⟨P, hP⟩
      obtain ⟨w, hw, hwP⟩ := exists_mem_genericPoints_specializes (hV'.fromSpec P')
      obtain ⟨Q, rfl⟩ : w ∈ Set.range hV'.fromSpec := hV'.range_fromSpec.ge (hgenV w hw)
      refine ⟨Q.asIdeal, Q.isPrime, (PrimeSpectrum.le_iff_specializes Q P').mpr
        (hV'.fromSpec.isOpenEmbedding.isInducing.specializes_iff.mp hwP), ?_⟩
      have h₁ : hV.fromSpec (Spec.map (f.app V) Q) = genericPoint X := by
        rw [← Scheme.Hom.comp_apply, hsq, Scheme.Hom.comp_apply]
        exact hgen _ hw
      have h₂ : hV.fromSpec (Spec.map (f.app V) Q) ⤳
          hV.fromSpec (⊥ : PrimeSpectrum Γ(X, V)) := h₁ ▸ genericPoint_specializes _
      exact le_bot_iff.mp ((PrimeSpectrum.le_iff_specializes _ _).mpr
        (hV.fromSpec.isOpenEmbedding.isInducing.specializes_iff.mp h₂))
    · by_contra hne
      obtain ⟨r, hr, H⟩ := exists_ne_zero_forall_exists_two_lifts σ τ hne
      obtain ⟨p, _, φ, hφ, hc, hg⟩ := hpt r hr
      obtain ⟨ψ, ψ', hψ, hψ', hne'⟩ := H (PadicAlgCl p) (OO p) φ.hom hφ
      have key : ∀ ρ : Γ(W, f ⁻¹ᵁ V) →+* OO p, ρ.comp (algebraMap Γ(X, V) Γ(W, f ⁻¹ᵁ V)) = φ.hom →
          (Spec.map (CommRingCat.ofHom ρ) ≫ hV'.fromSpec) ≫ f = Spec.map φ ≫ hV.fromSpec := by
        intro ρ hρ
        rw [Category.assoc, ← hsq, ← Spec.map_comp_assoc]
        congr 2
        exact CommRingCat.hom_ext hρ
      have h := huniq p (Spec.map (CommRingCat.ofHom ψ) ≫ hV'.fromSpec)
        (Spec.map (CommRingCat.ofHom ψ') ≫ hV'.fromSpec) ((key ψ hψ).trans (key ψ' hψ').symm)
        (key ψ hψ ▸ hc) (key ψ hψ ▸ hg)
      exact hne' congr(($(Spec.map_injective ((cancel_mono hV'.fromSpec).mp h))).hom)
  haveI : IsIso (f ∣_ V) := (isIso_morphismRestrict_iff_isIso_app f hV).mpr
    ((ConcreteCategory.isIso_iff_bijective _).mpr hbij)
  have hsub : ∀ w ∈ genericPoints W, w = w₁ := by
    intro w hw
    have hinj : Function.Injective (f ∣_ V) := (f ∣_ V).isOpenEmbedding.injective
    refine congrArg Subtype.val (hinj (a₁ := ⟨w, hgenV w hw⟩) (a₂ := ⟨w₁, hgenV w₁ hw₁⟩) ?_)
    apply Subtype.ext
    exact (morphismRestrict_base_coe f V _).trans (((hgen w hw).trans (hgen w₁ hw₁).symm).trans
      (morphismRestrict_base_coe f V ⟨w₁, hgenV w₁ hw₁⟩).symm)
  haveI : IrreducibleSpace W := by
    rw [irreducibleSpace_def]
    have h : closure ({w₁} : Set W) = ⊤ := by
      refine Set.eq_univ_of_forall fun w => ?_
      obtain ⟨w₀, hw₀, h₀⟩ := exists_mem_genericPoints_specializes w
      exact specializes_iff_mem_closure.mp (hsub w₀ hw₀ ▸ h₀)
    exact h ▸ isIrreducible_singleton.closure
  haveI : IsIntegral W := isIntegral_of_irreducibleSpace_of_isReduced W
  exact isIso_of_isFinite_of_birational f hN' V hVne

end GlobalTheory

import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.DivisorSupportCondition
import Development.AbelianVarietyTheory.Definitions.Divisors.SecClass
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsCompletionPointClosedPointMemOfSmooth
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsIsDiscreteValuationRingOfMaximalIdealEqSpa

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC
open scoped TensorProduct

namespace GlobalTheory

open Polynomial in

/- English proof (translation)
Set `k` to `q.ResidueField`. Set `L` to `IntermediateField.adjoin k (Set.range b)`. Establish `: FiniteDimensional k L` using `IntermediateField.finiteDimensional_adjoin fun x _ => Algebra.IsIntegral.isIntegral x`. Take `⟨θ, hθ⟩` from `Field.exists_primitive_element k L`. Establish `hi : IsIntegral k θ` using `Algebra.IsIntegral.isIntegral θ`.

Establish `hr : ∀ i, ∃ r : k[X], aeval θ r = (⟨b i, IntermediateField.subset_adjoin _ _ ⟨i, rfl⟩⟩ : L)`. Introduce `i`. Establish `h₁ : (⟨b i, IntermediateField.subset_adjoin _ _ ⟨i, rfl⟩⟩ : L) ∈ Algebra.adjoin k {θ}`. Rewrite using `[← IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic hi.isAlgebraic, hθ]`. Discharge the goal by the elementary cases of `trivial`.

Rewrite `h₁` using `[Algebra.adjoin_singleton_eq_range_aeval]`. Take `⟨g, hg⟩` from `h₁`. Conclude with `⟨g, hg⟩`. Use `choose r hr using hr`. Use `Fintype.ofFinite ι` as an intermediate fact.

Set `T : Finset k` to `(minpoly k θ).coeffs ∪ Finset.univ.biUnion fun i => (r i).coeffs`. Take `⟨⟨d, hd⟩, hdT⟩` from `IsLocalization.exist_integer_multiples_of_finset (nonZeroDivisors (A ⧸ q)) T`. Take `⟨s, rfl⟩` from `Ideal.Quotient.mk_surjective d`. Establish `hs : algebraMap A k s ≠ 0`. Rewrite using `[IsScalarTower.algebraMap_apply A (A ⧸ q) k]`.

Conclude with `(IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hd)`. Set `As` to `Localization.Away s`. Set `ρ : As →+* k` to `IsLocalization.Away.lift s (Ne.isUnit hs)`. Establish `hρ : ∀ a : A, ρ (algebraMap A As a) = algebraMap A k a` using `IsLocalization.Away.lift_eq s _`. Use `letI : Algebra As k := ρ.toAlgebra`.

Use `letI : Algebra As K := ((algebraMap k K).comp ρ).toAlgebra`. Establish `: IsScalarTower As k K` using `.of_algebraMap_eq' rfl`. Establish `: IsScalarTower A As K` using `.of_algebraMap_eq fun a => by`. Express the relevant statement in the definitionally equal form `algebraMap A K a = algebraMap k K (ρ (algebraMap A As a))`. Rewrite using `[hρ, ← IsScalarTower.algebraMap_apply]`.

Establish `hT : ∀ c ∈ T, c ∈ Set.range ρ`. Introduce `c hc`. Take `⟨a, ha⟩` from `hdT c hc`. Take `⟨a, rfl⟩` from `Ideal.Quotient.mk_surjective a`. Use `⟨IsLocalization.mk' As a (⟨s, 1, by simp⟩ : Submonoid.powers s), ?_⟩` and prove the remaining obligations.

Establish `e1 : ρ (IsLocalization.mk' As a (⟨s, 1, by simp⟩ : Submonoid.powers s)) * algebraMap A k s = algebraMap A k a`. Rewrite using `[← hρ, ← hρ, ← map_mul, IsLocalization.mk'_spec]`. Establish `e2 : c * algebraMap A k s = algebraMap A k a`. Rewrite using `[IsScalarTower.algebraMap_apply A (A ⧸ q) k s, IsScalarTower.algebraMap_apply A (A ⧸ q) k a]`. Use `erw [ha]`.

Rewrite using `[Algebra.smul_def, mul_comm]`. Both sides reduce to the same expression. Conclude with `mul_right_cancel₀ hs (e1.trans e2.symm)`. Establish `hlift : ∀ g : k[X], (∀ c ∈ g.coeffs, c ∈ Set.range ρ) → ∃ g' : As[X], g'.map ρ = g`. Introduce `g hg`.

Rewrite using `[← Polynomial.mem_lifts, Polynomial.lifts_iff_coeff_lifts]`. Introduce `n`. Distinguish the cases in `h : g.coeff n = 0`. Conclude with `⟨0, by simp [h]⟩`. Conclude with `hg _ (Polynomial.coeff_mem_coeffs h)`.

Take `⟨μ, hμ, -, hμm⟩` from `lifts_and_natDegree_eq_and_monic (f := algebraMap As k) (p := minpoly k θ) (Polynomial.mem_lifts _ |>.mpr (hlift _ fun c hc => hT c (Finset.mem_union_left _ hc))) (minpoly.monic hi)`. Set `P : StandardEtalePair As` to `⟨μ, hμm, derivative μ, 1, 0, 1, by simp⟩`. Establish `key : ∀ g : As[X], aeval (θ : K) g = (aeval θ (g.map (algebraMap As k)) : L)` using `fun g => by`. Rewrite using `[← aeval_map_algebraMap k]`. Conclude with `aeval_algHom_apply L.val θ _`.

Establish `hP : P.HasMap (θ : K)`. Use `⟨by rw [key, hμ, minpoly.aeval]; rfl, Ne.isUnit ?_⟩` and prove the remaining obligations. Rewrite using `[key, ← derivative_map, hμ]`. Conclude with `fun h => (Algebra.IsSeparable.isSeparable k θ).aeval_derivative_ne_zero (minpoly.aeval k θ) (Subtype.ext h)`. Set `ε₀ : P.Ring →ₐ[As] K` to `P.lift _ hP`.

Use `letI : Algebra A P.Ring := ((algebraMap As P.Ring).comp (algebraMap A As)).toAlgebra`. Establish `: IsScalarTower A As P.Ring` using `.of_algebraMap_eq' rfl`. Use `⟨P.Ring, inferInstance, inferInstance, Algebra.Etale.comp A As P.Ring, ε₀.restrictScalars A, fun i => ?_⟩` and prove the remaining obligations. Take `⟨g, hg⟩` from `hlift (r i) fun c hc => hT c (Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ _, hc⟩))`. Use `⟨aeval P.X g, ?_⟩` and prove the remaining obligations.

Express the relevant statement in the definitionally equal form `ε₀ (aeval P.X g) = b i`. Rewrite using `[← aeval_algHom_apply, StandardEtalePair.lift_X, key]`. Express the relevant statement in the definitionally equal form `((aeval θ (g.map ρ) : L) : K) = b i`. Rewrite using `[hg, hr i]`.
-/
theorem exists_etale_subset_range_of_isPrime {A : Type} [CommRing A] (q : Ideal A) [q.IsPrime]
    {K : Type} [Field K] [Algebra A K] [Algebra q.ResidueField K]
    [IsScalarTower A q.ResidueField K] [Algebra.IsSeparable q.ResidueField K]
    {ι : Type} [Finite ι] (b : ι → K) :
    ∃ (E : Type) (_ : CommRing E) (_ : Algebra A E) (_ : Algebra.Etale A E) (ε : E →ₐ[A] K),
      ∀ i, b i ∈ Set.range ε := by
  classical
  let k := q.ResidueField
  let L := IntermediateField.adjoin k (Set.range b)
  have : FiniteDimensional k L :=
    IntermediateField.finiteDimensional_adjoin fun x _ => Algebra.IsIntegral.isIntegral x
  obtain ⟨θ, hθ⟩ := Field.exists_primitive_element k L
  have hi : IsIntegral k θ := Algebra.IsIntegral.isIntegral θ
  have hr : ∀ i, ∃ r : k[X], aeval θ r = (⟨b i, IntermediateField.subset_adjoin _ _ ⟨i, rfl⟩⟩ : L) := by
    intro i
    have h₁ : (⟨b i, IntermediateField.subset_adjoin _ _ ⟨i, rfl⟩⟩ : L) ∈ Algebra.adjoin k {θ} := by
      rw [← IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic hi.isAlgebraic, hθ]
      trivial
    rw [Algebra.adjoin_singleton_eq_range_aeval] at h₁
    obtain ⟨g, hg⟩ := h₁
    exact ⟨g, hg⟩
  choose r hr using hr
  have := Fintype.ofFinite ι
  let T : Finset k := (minpoly k θ).coeffs ∪ Finset.univ.biUnion fun i => (r i).coeffs
  obtain ⟨⟨d, hd⟩, hdT⟩ := IsLocalization.exist_integer_multiples_of_finset (nonZeroDivisors (A ⧸ q)) T
  obtain ⟨s, rfl⟩ := Ideal.Quotient.mk_surjective d
  have hs : algebraMap A k s ≠ 0 := by
    rw [IsScalarTower.algebraMap_apply A (A ⧸ q) k]
    exact (IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hd)
  let As := Localization.Away s
  let ρ : As →+* k := IsLocalization.Away.lift s (Ne.isUnit hs)
  have hρ : ∀ a : A, ρ (algebraMap A As a) = algebraMap A k a := IsLocalization.Away.lift_eq s _
  letI : Algebra As k := ρ.toAlgebra
  letI : Algebra As K := ((algebraMap k K).comp ρ).toAlgebra
  have : IsScalarTower As k K := .of_algebraMap_eq' rfl
  have : IsScalarTower A As K := .of_algebraMap_eq fun a => by
    change algebraMap A K a = algebraMap k K (ρ (algebraMap A As a))
    rw [hρ, ← IsScalarTower.algebraMap_apply]
  have hT : ∀ c ∈ T, c ∈ Set.range ρ := by
    intro c hc
    obtain ⟨a, ha⟩ := hdT c hc
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
    refine ⟨IsLocalization.mk' As a (⟨s, 1, by simp⟩ : Submonoid.powers s), ?_⟩
    have e1 : ρ (IsLocalization.mk' As a (⟨s, 1, by simp⟩ : Submonoid.powers s)) * algebraMap A k s =
        algebraMap A k a := by
      rw [← hρ, ← hρ, ← map_mul, IsLocalization.mk'_spec]
    have e2 : c * algebraMap A k s = algebraMap A k a := by
      rw [IsScalarTower.algebraMap_apply A (A ⧸ q) k s, IsScalarTower.algebraMap_apply A (A ⧸ q) k a]
      erw [ha]
      rw [Algebra.smul_def, mul_comm]
      rfl
    exact mul_right_cancel₀ hs (e1.trans e2.symm)
  have hlift : ∀ g : k[X], (∀ c ∈ g.coeffs, c ∈ Set.range ρ) → ∃ g' : As[X], g'.map ρ = g := by
    intro g hg
    rw [← Polynomial.mem_lifts, Polynomial.lifts_iff_coeff_lifts]
    intro n
    by_cases h : g.coeff n = 0
    · exact ⟨0, by simp [h]⟩
    · exact hg _ (Polynomial.coeff_mem_coeffs h)
  obtain ⟨μ, hμ, -, hμm⟩ := lifts_and_natDegree_eq_and_monic (f := algebraMap As k)
    (p := minpoly k θ) (Polynomial.mem_lifts _ |>.mpr
      (hlift _ fun c hc => hT c (Finset.mem_union_left _ hc))) (minpoly.monic hi)
  let P : StandardEtalePair As := ⟨μ, hμm, derivative μ, 1, 0, 1, by simp⟩
  have key : ∀ g : As[X], aeval (θ : K) g = (aeval θ (g.map (algebraMap As k)) : L) := fun g => by
    rw [← aeval_map_algebraMap k]
    exact aeval_algHom_apply L.val θ _
  have hP : P.HasMap (θ : K) := by
    refine ⟨by rw [key, hμ, minpoly.aeval]; rfl, Ne.isUnit ?_⟩
    rw [key, ← derivative_map, hμ]
    exact fun h => (Algebra.IsSeparable.isSeparable k θ).aeval_derivative_ne_zero
      (minpoly.aeval k θ) (Subtype.ext h)
  let ε₀ : P.Ring →ₐ[As] K := P.lift _ hP
  letI : Algebra A P.Ring := ((algebraMap As P.Ring).comp (algebraMap A As)).toAlgebra
  have : IsScalarTower A As P.Ring := .of_algebraMap_eq' rfl
  refine ⟨P.Ring, inferInstance, inferInstance, Algebra.Etale.comp A As P.Ring,
    ε₀.restrictScalars A, fun i => ?_⟩
  obtain ⟨g, hg⟩ := hlift (r i) fun c hc =>
    hT c (Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ _, hc⟩))
  refine ⟨aeval P.X g, ?_⟩
  change ε₀ (aeval P.X g) = b i
  rw [← aeval_algHom_apply, StandardEtalePair.lift_X, key]
  change ((aeval θ (g.map ρ) : L) : K) = b i
  rw [hg, hr i]

/- English proof (translation)
Use `set q := p.comap (algebraMap A C) with hq`. Set `K` to `SeparableClosure q.ResidueField`. Use `letI : Algebra A K := ((algebraMap q.ResidueField K).comp (algebraMap A q.ResidueField)).toAlgebra`. Establish `: IsScalarTower A q.ResidueField K` using `.of_algebraMap_eq' rfl`. Establish `hker : RingHom.ker (algebraMap A K) = q`.

Rewrite using `[IsScalarTower.algebraMap_eq A q.ResidueField K, ← RingHom.comap_ker, (RingHom.injective_iff_ker_eq_bot _).mp (algebraMap q.ResidueField K).injective]`. Conclude with `Ideal.ker_algebraMap_residueField q`. Take `⟨φ⟩` from `nonempty_algHom_of_smooth_of_isSepClosed (R := A) (K := K) p hker.symm`. Establish `: (RingHom.ker φ).IsPrime` using `RingHom.ker_isPrime _`. Take `⟨f, hf, n, _, _, _⟩` from `Algebra.IsSmoothAt.exists_isStandardEtale_mvPolynomial (R := A) (p := RingHom.ker φ)`.

Set `S` to `Localization.Away f`. Set `P` to `MvPolynomial (Fin n) A`. Set `φ' : S →ₐ[A] K` to `IsLocalization.Away.liftAlgHom f (Ne.isUnit hf)`. Take `⟨E, _, _, _, ε, hε⟩` from `exists_etale_subset_range_of_isPrime q fun i : Fin n => φ' (algebraMap P S (MvPolynomial.X i))`. Use `choose c hc using hε`.

Set `χ : P →ₐ[A] K` to `φ'.comp (IsScalarTower.toAlgHom A _ _)`. Establish `hχ : ε.comp (MvPolynomial.aeval c) = χ`. Use `MvPolynomial.algHom_ext fun i => ?_` and prove the remaining obligations. Conclude with `(congrArg ε (MvPolynomial.aeval_X (R := A) c i)).trans (hc i)`. Use `letI := (MvPolynomial.aeval (R := A) c).toAlgebra`.

Establish `: IsScalarTower A P E` using `.of_algebraMap_eq fun r => ((MvPolynomial.aeval (R := A) c).commutes r).symm`. Use `letI := χ.toAlgebra`. Use `letI := ε.toAlgebra`. Establish `: IsScalarTower A E K` using `.of_algebraMap_eq fun r => (ε.commutes r).symm`. Establish `: IsScalarTower P E K` using `.of_algebraMap_eq fun r => congr($hχ r).symm`.

Set `φ'' : S →ₐ[P] K` to `⟨φ', fun r => rfl⟩`. Set `W` to `E ⊗[P] S`. Set `ε' : W →ₐ[E] K` to `Algebra.TensorProduct.lift (Algebra.ofId E K) φ'' fun _ _ => .all _ _`. Establish `hcomm : ∀ r : A, (1 : E) ⊗ₜ[P] algebraMap A S r = algebraMap A W r` using `fun r => by`. Express the relevant statement in the definitionally equal form `(1 : E) ⊗ₜ[P] algebraMap A S r = (algebraMap A E r) ⊗ₜ[P] (1 : S)`.

Rewrite using `[IsScalarTower.algebraMap_apply A P S, IsScalarTower.algebraMap_apply A P E]`. Conclude with `(Algebra.TensorProduct.tmul_one_eq_one_tmul _).symm`. Use `⟨W, inferInstance, inferInstance, Algebra.Etale.comp A E W, ⟨(Algebra.TensorProduct.includeRight (R := P) (A := E) (B := S)).toRingHom.comp (algebraMap C S), fun r => ?_⟩, RingHom.ker ε', RingHom.ker_isPrime _, ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `(1 : E) ⊗ₜ[P] algebraMap C S (algebraMap A C r) = algebraMap A W r`. Rewrite using `[← IsScalarTower.algebraMap_apply]`.

Conclude with `hcomm r`. Use extensionality with `r`. Rewrite using `[Ideal.mem_comap, RingHom.mem_ker, show ε' (algebraMap A W r) = algebraMap A K r from (ε'.restrictScalars A).commutes r, ← RingHom.mem_ker, hker]`.
-/
theorem exists_etale_prime_of_smooth {A C : Type} [CommRing A] [CommRing C] [Algebra A C]
    [Algebra.Smooth A C] (p : Ideal C) [p.IsPrime] :
    ∃ (W : Type) (_ : CommRing W) (_ : Algebra A W) (_ : Algebra.Etale A W) (_ : C →ₐ[A] W)
      (P : Ideal W), P.IsPrime ∧ P.comap (algebraMap A W) = p.comap (algebraMap A C) := by
  set q := p.comap (algebraMap A C) with hq
  let K := SeparableClosure q.ResidueField
  letI : Algebra A K := ((algebraMap q.ResidueField K).comp (algebraMap A q.ResidueField)).toAlgebra
  have : IsScalarTower A q.ResidueField K := .of_algebraMap_eq' rfl
  have hker : RingHom.ker (algebraMap A K) = q := by
    rw [IsScalarTower.algebraMap_eq A q.ResidueField K, ← RingHom.comap_ker,
      (RingHom.injective_iff_ker_eq_bot _).mp (algebraMap q.ResidueField K).injective]
    exact Ideal.ker_algebraMap_residueField q
  obtain ⟨φ⟩ := nonempty_algHom_of_smooth_of_isSepClosed (R := A) (K := K) p hker.symm
  have : (RingHom.ker φ).IsPrime := RingHom.ker_isPrime _
  obtain ⟨f, hf, n, _, _, _⟩ := Algebra.IsSmoothAt.exists_isStandardEtale_mvPolynomial (R := A)
    (p := RingHom.ker φ)
  let S := Localization.Away f
  let P := MvPolynomial (Fin n) A
  let φ' : S →ₐ[A] K := IsLocalization.Away.liftAlgHom f (Ne.isUnit hf)
  obtain ⟨E, _, _, _, ε, hε⟩ := exists_etale_subset_range_of_isPrime q
    fun i : Fin n => φ' (algebraMap P S (MvPolynomial.X i))
  choose c hc using hε
  let χ : P →ₐ[A] K := φ'.comp (IsScalarTower.toAlgHom A _ _)
  have hχ : ε.comp (MvPolynomial.aeval c) = χ := by
    refine MvPolynomial.algHom_ext fun i => ?_
    exact (congrArg ε (MvPolynomial.aeval_X (R := A) c i)).trans (hc i)
  letI := (MvPolynomial.aeval (R := A) c).toAlgebra
  have : IsScalarTower A P E := .of_algebraMap_eq fun r => ((MvPolynomial.aeval (R := A) c).commutes r).symm
  letI := χ.toAlgebra
  letI := ε.toAlgebra
  have : IsScalarTower A E K := .of_algebraMap_eq fun r => (ε.commutes r).symm
  have : IsScalarTower P E K := .of_algebraMap_eq fun r => congr($hχ r).symm
  let φ'' : S →ₐ[P] K := ⟨φ', fun r => rfl⟩
  let W := E ⊗[P] S
  let ε' : W →ₐ[E] K := Algebra.TensorProduct.lift (Algebra.ofId E K) φ'' fun _ _ => .all _ _
  have hcomm : ∀ r : A, (1 : E) ⊗ₜ[P] algebraMap A S r = algebraMap A W r := fun r => by
    change (1 : E) ⊗ₜ[P] algebraMap A S r = (algebraMap A E r) ⊗ₜ[P] (1 : S)
    rw [IsScalarTower.algebraMap_apply A P S, IsScalarTower.algebraMap_apply A P E]
    exact (Algebra.TensorProduct.tmul_one_eq_one_tmul _).symm
  refine ⟨W, inferInstance, inferInstance, Algebra.Etale.comp A E W,
    ⟨(Algebra.TensorProduct.includeRight (R := P) (A := E) (B := S)).toRingHom.comp
      (algebraMap C S), fun r => ?_⟩, RingHom.ker ε', RingHom.ker_isPrime _, ?_⟩
  · change (1 : E) ⊗ₜ[P] algebraMap C S (algebraMap A C r) = algebraMap A W r
    rw [← IsScalarTower.algebraMap_apply]
    exact hcomm r
  · ext r
    rw [Ideal.mem_comap, RingHom.mem_ker,
      show ε' (algebraMap A W r) = algebraMap A K r from (ε'.restrictScalars A).commutes r,
      ← RingHom.mem_ker, hker]

/- English proof (translation)
Introduce `Y X f _ x hx`. Take `⟨y, rfl⟩` from `hx`. Take `⟨U, V, hU, hV, hVU, -, hyV⟩` from `exists_isAffineOpen_pair f y (O := ⊤) trivial`. Take `⟨p, rfl⟩ : y ∈ Set.range hV.fromSpec` from `by rwa [hV.range_fromSpec]`. Use `f.smooth_appLE hU hV hVU` as an intermediate fact.

Use `p.isPrime` as an intermediate fact. Use `algebraize [(f.appLE U V hVU).hom]`. Take `⟨W, _, _, _, ψ, P, hP, hPq⟩` from `exists_etale_prime_of_smooth (A := Γ(X, U)) (C := Γ(Y, V)) p.asIdeal`. Establish `hs : (Spec.map (CommRingCat.ofHom ψ.toRingHom) ≫ hV.fromSpec) ≫ f = Spec.map (CommRingCat.ofHom (algebraMap Γ(X, U) W)) ≫ hU.fromSpec`. Rewrite using `[Category.assoc, ← hU.SpecMap_appLE_fromSpec f hV hVU, ← Spec.map_comp_assoc]`.

Use `congr 2`. Use extensionality with `a`. Conclude with `ψ.commutes a`. Establish `: Etale (Spec.map (CommRingCat.ofHom (algebraMap Γ(X, U) W)))` using `HasRingHomProperty.Spec_iff.mpr (RingHom.etale_algebraMap.mpr ‹_›)`. Use `⟨Spec (.of W), Spec.map (CommRingCat.ofHom ψ.toRingHom) ≫ hV.fromSpec, ?_, ⟨⟨P, hP⟩, ?_⟩⟩` and prove the remaining obligations.

Rewrite using `[hs] infer_instance`. Establish `e : Spec.map (CommRingCat.ofHom (algebraMap Γ(X, U) W)) ⟨P, hP⟩ = Spec.map (f.appLE U V hVU) p` using `PrimeSpectrum.ext hPq`. Rewrite using `[hs]`. Conclude with `(congrArg hU.fromSpec e).trans congr($(hU.SpecMap_appLE_fromSpec f hV hVU) p)`.
-/
theorem exists_etale_quasiSection_of_smooth : ∀ {Y X : Scheme.{0}} (f : Y ⟶ X) [Smooth f] (x : X),
    x ∈ Set.range f → ∃ (V : Scheme.{0}) (s : V ⟶ Y), Etale (s ≫ f) ∧ x ∈ Set.range (s ≫ f) := by
  intro Y X f _ x hx
  obtain ⟨y, rfl⟩ := hx
  obtain ⟨U, V, hU, hV, hVU, -, hyV⟩ := exists_isAffineOpen_pair f y (O := ⊤) trivial
  obtain ⟨p, rfl⟩ : y ∈ Set.range hV.fromSpec := by rwa [hV.range_fromSpec]
  have := f.smooth_appLE hU hV hVU
  have := p.isPrime
  algebraize [(f.appLE U V hVU).hom]
  obtain ⟨W, _, _, _, ψ, P, hP, hPq⟩ :=
    exists_etale_prime_of_smooth (A := Γ(X, U)) (C := Γ(Y, V)) p.asIdeal
  have hs : (Spec.map (CommRingCat.ofHom ψ.toRingHom) ≫ hV.fromSpec) ≫ f =
      Spec.map (CommRingCat.ofHom (algebraMap Γ(X, U) W)) ≫ hU.fromSpec := by
    rw [Category.assoc, ← hU.SpecMap_appLE_fromSpec f hV hVU, ← Spec.map_comp_assoc]
    congr 2
    ext a
    exact ψ.commutes a
  have : Etale (Spec.map (CommRingCat.ofHom (algebraMap Γ(X, U) W))) :=
    HasRingHomProperty.Spec_iff.mpr (RingHom.etale_algebraMap.mpr ‹_›)
  refine ⟨Spec (.of W), Spec.map (CommRingCat.ofHom ψ.toRingHom) ≫ hV.fromSpec, ?_, ⟨⟨P, hP⟩, ?_⟩⟩
  · rw [hs]
    infer_instance
  have e : Spec.map (CommRingCat.ofHom (algebraMap Γ(X, U) W)) ⟨P, hP⟩ =
      Spec.map (f.appLE U V hVU) p := PrimeSpectrum.ext hPq
  rw [hs]
  exact (congrArg hU.fromSpec e).trans congr($(hU.SpecMap_appLE_fromSpec f hV hVU) p)

end GlobalTheory

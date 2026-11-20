import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.QuasiCompact
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsOpenConnectedComponentOfIsLocallyNoetherian
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.EtaleFinitePiece

open Polynomial in

/- English proof (translation)
Set `p : Ideal R` to `RingHom.ker (algebraMap R L)`. Use `haveI : p.IsPrime := RingHom.ker_isPrime _`. Set `K` to `p.ResidueField`. Use `letI : Algebra K L := (Ideal.ResidueField.lift p (algebraMap R L) le_rfl (by`. Introduce `r hr`.

Conclude with `(IsUnit.mem_submonoid_iff _).2 (isUnit_iff_ne_zero.2 (by simpa [p] using hr)))).toAlgebra`. Use `haveI : IsScalarTower R K L := IsScalarTower.of_algebraMap_eq fun r => (Ideal.ResidueField.lift_algebraMap _ _ _ _ r).symm`. Use `haveI : Algebra.QuasiFinite K L := .of_restrictScalars R K L`. Use `haveI : Module.Finite K L := .of_quasiFinite`. Set `Ks` to `separableClosure K L`.

Take `⟨θ, hθ⟩` from `Field.exists_primitive_element K Ks`. Establish `hint : IsIntegral K θ` using `.of_finite K θ`. Establish `hfrac : ∀ k : K, ∃ a c : R, algebraMap R K c ≠ 0 ∧ k * algebraMap R K c = algebraMap R K a`. Introduce `k`. Take `⟨a, c, hc, rfl⟩` from `IsFractionRing.div_surjective (A := R ⧸ p) k`.

Take `⟨a, rfl⟩` from `Ideal.Quotient.mk_surjective a`. Take `⟨c, rfl⟩` from `Ideal.Quotient.mk_surjective c`. Establish `hc' : algebraMap (R ⧸ p) K (Ideal.Quotient.mk p c) ≠ 0` using `IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hc`. Conclude with `⟨a, c, hc', div_mul_cancel₀ _ hc'⟩`. Take `⟨c, hc, hcf⟩ : ∃ c : R, algebraMap R K c ≠ 0 ∧ ∀ i, (minpoly K θ).coeff i * algebraMap R K c ∈ (algebraMap R K).range` from `by choose a c hc hac using hfrac`.

Use `⟨∏ i ∈ (minpoly K θ).support, c ((minpoly K θ).coeff i), ?_, fun i => ?_⟩` and prove the remaining obligations. Rewrite using `[map_prod]`. Conclude with `Finset.prod_ne_zero_iff.2 fun i _ => hc _`. Distinguish the cases in `hi : i ∈ (minpoly K θ).support`. Rewrite using `[← Finset.mul_prod_erase _ _ hi, map_mul, ← _root_.mul_assoc, hac, ← map_mul]`.

Conclude with `⟨_, rfl⟩`. Rewrite using `[notMem_support_iff.1 hi, zero_mul]`. Conclude with `zero_mem _`. Use `set c' := algebraMap R K c with hc'`. Establish `hmin : minpoly K (c' • θ) = (minpoly K θ).scaleRoots c'` using `IsIntegrallyClosed.minpoly_smul hc hint`.

Establish `hint' : IsIntegral K (c' • θ)` using `.of_finite K _`. Establish `hl : minpoly K (c' • θ) ∈ lifts (algebraMap R K)`. Rewrite using `[lifts_iff_coeff_lifts]`. Introduce `n`. Break down `lt_trichotomy n (minpoly K θ).natDegree with h | h | h` into its components or cases.

Rewrite using `[hmin, coeff_scaleRoots]`. Take `⟨m, hm⟩ : ∃ m, (minpoly K θ).natDegree - n = m + 1` from `⟨_, (Nat.succ_pred_eq_of_pos (by omega)).symm⟩`. Take `⟨u, hu⟩` from `hcf n`. Use `⟨u * c ^ m, ?_⟩` and prove the remaining obligations. Rewrite using `[hm, map_mul, hu, map_pow, pow_succ]`.

Expand and normalize the polynomial expressions, which then agree. Rewrite using `[hmin, coeff_scaleRoots, h, Nat.sub_self, pow_zero, _root_.mul_one, (minpoly.monic hint).coeff_natDegree]`. Conclude with `⟨1, map_one _⟩`. Rewrite using `[hmin, coeff_scaleRoots, coeff_eq_zero_of_natDegree_lt h, zero_mul]`. Conclude with `⟨0, map_zero _⟩`.

Take `⟨F, hF, -, hFm⟩` from `lifts_and_natDegree_eq_and_monic hl (minpoly.monic hint')`. Set `P : StandardEtalePair R` to `⟨F, hFm, derivative F, ⟨1, 0, 1, by simp⟩⟩`. Establish `hsep : (minpoly K (c' • θ)).Separable` using `Algebra.IsSeparable.isSeparable K _`. Establish `hP : P.HasMap (c' • θ)`. Prove the components needed by the constructor for the conclusion.

Express the relevant statement in the definitionally equal form `aeval _ F = 0`. Rewrite using `[← aeval_map_algebraMap K, hF, minpoly.aeval]`. Express the relevant statement in the definitionally equal form `IsUnit (aeval _ (derivative F))`. Rewrite using `[← aeval_map_algebraMap K, ← derivative_map, hF]`. Conclude with `(hsep.aeval_derivative_ne_zero (minpoly.aeval _ _)).isUnit`.

Use `⟨P.Ring, inferInstance, inferInstance, inferInstance, (Ks.val.restrictScalars R).comp (P.lift _ hP), fun Ω _ a₁ a₂ h => ?_⟩` and prove the remaining obligations. Establish `hR : ∀ r : R, a₁ (algebraMap R L r) = a₂ (algebraMap R L r)` using `fun r => by`. Use `congr($h (algebraMap R P.Ring r))` as an intermediate fact. Simplify using `only [AlgHom.toRingHom_eq_coe, RingHom.coe_comp, RingHom.coe_coe, Function.comp_apply, AlgHom.commutes] at this`. Conclude with `this`.

Establish `hK : ∀ k : K, a₁ (algebraMap K L k) = a₂ (algebraMap K L k)` using `fun k => by`. Take `⟨a, d, hd, e⟩` from `hfrac k`. Establish `h2 : a₂ (algebraMap K L (algebraMap R K d)) ≠ 0` using `by simpa using hd`. Apply `mul_right_cancel₀ h2` to reduce the goal to its premises. Rewrite using `[← map_mul, ← map_mul, e, ← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply, ← hR, ← hR, IsScalarTower.algebraMap_apply R K L, ← map_mul, ← map_mul, e, ← IsScalarTower.algebraMap_apply]`.

Establish `hX : a₁ ((c' • θ : Ks) : L) = a₂ ((c' • θ : Ks) : L)`. Simplify using `using congr($h P.X)`. Establish `hθ' : a₁ (θ : L) = a₂ (θ : L)`. Establish `h2 : a₂ (algebraMap K L c') ≠ 0` using `by simpa using hc`. Apply `mul_left_cancel₀ h2` to reduce the goal to its premises.

Rewrite using `[← map_mul, ← hK, ← map_mul]`. Simplify `hX` using `[Algebra.smul_def]`. Establish `hKs : a₁.comp (algebraMap Ks L) = a₂.comp (algebraMap Ks L)`. Use extensionality with `z`. Establish `hz : z ∈ IntermediateField.adjoin K {θ}` using `hθ ▸ IntermediateField.mem_top`.

Proceed by induction on `hz using IntermediateField.adjoin_induction with`. Consider the case `mem x hx => obtain rfl := hx`. Conclude with `hθ'`. Consider the case `algebraMap k => exact hK k`. Consider the case `add x y _ _ hx hy => rw [map_add, map_add, hx, hy]`.

Consider the case `inv x _ hx => rw [map_inv₀, map_inv₀, hx]`. Consider the case `mul x y _ _ hx hy => rw [map_mul, map_mul, hx, hy]`. Conclude with `IsPurelyInseparable.injective_comp_algebraMap Ks L Ω hKs`.
-/
theorem exists_etale_algebra (R L : Type) [CommRing R] [Field L] [Algebra R L] [Algebra.QuasiFinite R L] :
    ∃ (R₁ : Type) (_ : CommRing R₁) (_ : Algebra R R₁) (_ : Algebra.Etale R R₁) (ψ : R₁ →ₐ[R] L),
      ∀ (Ω : Type) [Field Ω] (a₁ a₂ : L →+* Ω),
        a₁.comp ψ.toRingHom = a₂.comp ψ.toRingHom → a₁ = a₂ := by
  let p : Ideal R := RingHom.ker (algebraMap R L)
  haveI : p.IsPrime := RingHom.ker_isPrime _
  let K := p.ResidueField
  letI : Algebra K L := (Ideal.ResidueField.lift p (algebraMap R L) le_rfl (by
    intro r hr
    exact (IsUnit.mem_submonoid_iff _).2 (isUnit_iff_ne_zero.2 (by simpa [p] using hr)))).toAlgebra
  haveI : IsScalarTower R K L := IsScalarTower.of_algebraMap_eq fun r =>
    (Ideal.ResidueField.lift_algebraMap _ _ _ _ r).symm
  haveI : Algebra.QuasiFinite K L := .of_restrictScalars R K L
  haveI : Module.Finite K L := .of_quasiFinite
  let Ks := separableClosure K L
  obtain ⟨θ, hθ⟩ := Field.exists_primitive_element K Ks
  have hint : IsIntegral K θ := .of_finite K θ
  have hfrac : ∀ k : K, ∃ a c : R, algebraMap R K c ≠ 0 ∧ k * algebraMap R K c = algebraMap R K a := by
    intro k
    obtain ⟨a, c, hc, rfl⟩ := IsFractionRing.div_surjective (A := R ⧸ p) k
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
    obtain ⟨c, rfl⟩ := Ideal.Quotient.mk_surjective c
    have hc' : algebraMap (R ⧸ p) K (Ideal.Quotient.mk p c) ≠ 0 :=
      IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hc
    exact ⟨a, c, hc', div_mul_cancel₀ _ hc'⟩
  obtain ⟨c, hc, hcf⟩ : ∃ c : R, algebraMap R K c ≠ 0 ∧ ∀ i,
      (minpoly K θ).coeff i * algebraMap R K c ∈ (algebraMap R K).range := by
    choose a c hc hac using hfrac
    refine ⟨∏ i ∈ (minpoly K θ).support, c ((minpoly K θ).coeff i), ?_, fun i => ?_⟩
    · rw [map_prod]; exact Finset.prod_ne_zero_iff.2 fun i _ => hc _
    · by_cases hi : i ∈ (minpoly K θ).support
      · rw [← Finset.mul_prod_erase _ _ hi, map_mul, ← _root_.mul_assoc, hac, ← map_mul]
        exact ⟨_, rfl⟩
      · rw [notMem_support_iff.1 hi, zero_mul]; exact zero_mem _
  set c' := algebraMap R K c with hc'
  have hmin : minpoly K (c' • θ) = (minpoly K θ).scaleRoots c' :=
    IsIntegrallyClosed.minpoly_smul hc hint
  have hint' : IsIntegral K (c' • θ) := .of_finite K _
  have hl : minpoly K (c' • θ) ∈ lifts (algebraMap R K) := by
    rw [lifts_iff_coeff_lifts]
    intro n
    rcases lt_trichotomy n (minpoly K θ).natDegree with h | h | h
    · rw [hmin, coeff_scaleRoots]
      obtain ⟨m, hm⟩ : ∃ m, (minpoly K θ).natDegree - n = m + 1 := ⟨_, (Nat.succ_pred_eq_of_pos (by omega)).symm⟩
      obtain ⟨u, hu⟩ := hcf n
      refine ⟨u * c ^ m, ?_⟩
      rw [hm, map_mul, hu, map_pow, pow_succ]; ring
    · rw [hmin, coeff_scaleRoots, h, Nat.sub_self, pow_zero, _root_.mul_one, (minpoly.monic hint).coeff_natDegree]
      exact ⟨1, map_one _⟩
    · rw [hmin, coeff_scaleRoots, coeff_eq_zero_of_natDegree_lt h, zero_mul]
      exact ⟨0, map_zero _⟩
  obtain ⟨F, hF, -, hFm⟩ := lifts_and_natDegree_eq_and_monic hl (minpoly.monic hint')
  let P : StandardEtalePair R := ⟨F, hFm, derivative F, ⟨1, 0, 1, by simp⟩⟩
  have hsep : (minpoly K (c' • θ)).Separable := Algebra.IsSeparable.isSeparable K _
  have hP : P.HasMap (c' • θ) := by
    constructor
    · change aeval _ F = 0
      rw [← aeval_map_algebraMap K, hF, minpoly.aeval]
    · change IsUnit (aeval _ (derivative F))
      rw [← aeval_map_algebraMap K, ← derivative_map, hF]
      exact (hsep.aeval_derivative_ne_zero (minpoly.aeval _ _)).isUnit
  refine ⟨P.Ring, inferInstance, inferInstance, inferInstance,
    (Ks.val.restrictScalars R).comp (P.lift _ hP), fun Ω _ a₁ a₂ h => ?_⟩
  have hR : ∀ r : R, a₁ (algebraMap R L r) = a₂ (algebraMap R L r) := fun r => by
    have := congr($h (algebraMap R P.Ring r))
    simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_comp, RingHom.coe_coe, Function.comp_apply, AlgHom.commutes] at this
    exact this
  have hK : ∀ k : K, a₁ (algebraMap K L k) = a₂ (algebraMap K L k) := fun k => by
    obtain ⟨a, d, hd, e⟩ := hfrac k
    have h2 : a₂ (algebraMap K L (algebraMap R K d)) ≠ 0 := by simpa using hd
    apply mul_right_cancel₀ h2
    rw [← map_mul, ← map_mul, e, ← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply, ← hR, ← hR,
      IsScalarTower.algebraMap_apply R K L, ← map_mul, ← map_mul, e, ← IsScalarTower.algebraMap_apply]
  have hX : a₁ ((c' • θ : Ks) : L) = a₂ ((c' • θ : Ks) : L) := by
    simpa using congr($h P.X)
  have hθ' : a₁ (θ : L) = a₂ (θ : L) := by
    have h2 : a₂ (algebraMap K L c') ≠ 0 := by simpa using hc
    apply mul_left_cancel₀ h2
    rw [← map_mul, ← hK, ← map_mul]
    simpa [Algebra.smul_def] using hX
  have hKs : a₁.comp (algebraMap Ks L) = a₂.comp (algebraMap Ks L) := by
    ext z
    have hz : z ∈ IntermediateField.adjoin K {θ} := hθ ▸ IntermediateField.mem_top
    induction hz using IntermediateField.adjoin_induction with
    | mem x hx => obtain rfl := hx; exact hθ'
    | algebraMap k => exact hK k
    | add x y _ _ hx hy => rw [map_add, map_add, hx, hy]
    | inv x _ hx => rw [map_inv₀, map_inv₀, hx]
    | mul x y _ _ hx hy => rw [map_mul, map_mul, hx, hy]
  exact IsPurelyInseparable.injective_comp_algebraMap Ks L Ω hKs

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
open TensorProduct in

/- English proof (translation)
Take `⟨_, ⟨U, hU, rfl⟩, hxU, -⟩` from `S.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ (f x)) isOpen_univ`. Take `⟨_, ⟨V, hV, rfl⟩, hxV, hUV : V ≤ f ⁻¹ᵁ U⟩` from `X.isBasis_affineOpens.exists_subset_of_mem_open hxU (f ⁻¹ᵁ U).2`. Establish `: (f.appLE U V hUV).hom.FiniteType` using `f.finiteType_appLE hU hV hUV`. Use `algebraize [(f.appLE U V hUV).hom]`. Establish `: (hV.primeIdealOf ⟨x, hxV⟩).asIdeal.LiesOver (hU.primeIdealOf ⟨f x, hxU⟩).asIdeal`.

It suffices to establish `hU.primeIdealOf ⟨f x, hxU⟩ = Spec.map (f.appLE U V hUV) (hV.primeIdealOf ⟨x, hxV⟩) from ⟨congr(($this).1)⟩`. Apply `hU.isoSpec.inv.homeomorph.injective` to reduce the goal to its premises. Apply `Subtype.ext` to reduce the goal to its premises. Simplify using `only [IsAffineOpen.primeIdealOf, Scheme.Hom.homeomorph_apply, ← Scheme.Hom.comp_apply, ← Scheme.Opens.ι_apply, IsAffineOpen.isoSpec_hom]`. Simplify using the standard rewrite rules.

Establish `: Algebra.QuasiFiniteAt Γ(S, U) (hV.primeIdealOf ⟨x, hxV⟩).asIdeal` using `hx.quasiFiniteAt hV hU hUV hxV`. Take `⟨R, _, _, _, P, _, _, e, _, P', _, hP'P, hP', heP', -, _, huniq⟩` from `Algebra.exists_etale_isIdempotentElem_forall_liesOver_eq (hU.primeIdealOf ⟨f x, hxU⟩).asIdeal (hV.primeIdealOf ⟨x, hxV⟩).asIdeal`. Establish `hfin : (algebraMap R (Localization.Away e)).Finite` using `RingHom.finite_algebraMap.mpr ‹_›`. Set `φ : Γ(S, U) ⟶ .of R` to `CommRingCat.ofHom <| algebraMap Γ(S, U) R`. Establish `hφ : φ.hom.Etale` using `RingHom.etale_algebraMap.mpr ‹_›`.

Establish `: Etale (Spec.map φ)` using `HasRingHomProperty.Spec_iff.mpr hφ`. Apply the tactic sequence `let e₁ : Spec (.of (R ⊗[Γ(S, U)] Γ(X, V))) ≅ pullback (Spec.map (f.appLE U V hUV)) (Spec.map φ) := (pullbackSpecIso _ _ _).symm ≪≫ pullbackSymmetry _ _`. Establish `he₁ : e₁.hom ≫ pullback.fst _ _ = Spec.map (CommRingCat.ofHom Algebra.TensorProduct.includeRight.toRingHom)` using `by dsimp [e₁, RingHom.algebraMap_toAlgebra]`. Rewrite using `[Category.assoc, pullbackSymmetry_hom_comp_fst]`. Conclude with `pullbackSpecIso_inv_snd ..`.

Set `g : Spec (.of (R ⊗[Γ(S, U)] Γ(X, V))) ⟶ pullback f (Spec.map φ ≫ hU.fromSpec)` to `e₁.hom ≫ pullback.map _ _ _ _ hV.fromSpec (𝟙 _) hU.fromSpec (IsAffineOpen.SpecMap_appLE_fromSpec ..) (by simp)`. Set `l : Spec (.of (Localization.Away e)) ⟶ Spec (.of (R ⊗[Γ(S, U)] Γ(X, V)))` to `Spec.map (CommRingCat.ofHom <| algebraMap _ _)`. Establish `hl : Set.range l = ((PrimeSpectrum.basicOpen e : TopologicalSpace.Opens (PrimeSpectrum _)) : Set (PrimeSpectrum _))` using `PrimeSpectrum.localization_away_comap_range _ _`. Establish `hg : g ≫ pullback.snd f _ = Spec.map (CommRingCat.ofHom (algebraMap R _))`. Establish `H : (pullbackSpecIso _ R _).inv ≫ pullback.fst _ (Spec.map (f.appLE U V hUV)) = _` using `pullbackSpecIso_inv_fst ..`.

Simplify using `[g, e₁, RingHom.algebraMap_toAlgebra, φ, H]`. Both sides reduce to the same expression. Take `⟨z, hz⟩ : (⟨P', ‹_›⟩ : PrimeSpectrum _) ∈ Set.range l` from `by rw [hl]; exact heP'`. Use `⟨Spec (.of R), Spec.map φ ≫ hU.fromSpec, _, l ≫ g, z, inferInstance, inferInstance, ?_, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[Category.assoc, hg, ← Spec.map_comp, IsFinite.SpecMap_iff]`.

Conclude with `hfin`. Rewrite using `[Category.assoc, Scheme.Hom.comp_apply, hz] trans hV.fromSpec ⟨P'.comap Algebra.TensorProduct.includeRight.toRingHom, inferInstance⟩`. Simplify using `[-Scheme.Hom.comp_base, g, reassoc_of% he₁]`. Both sides reduce to the same expression. Use `convert! hV.fromSpec_primeIdealOf ⟨x, hxV⟩`.

Introduce `w hw`. Rewrite `hw` using `[Category.assoc, hg, Scheme.Hom.comp_apply, Scheme.Hom.comp_apply, hz]`. Apply `l.isOpenEmbedding.injective` to reduce the goal to its premises. Rewrite using `[hz]`. Establish `h1 : l w ∈ ((PrimeSpectrum.basicOpen e : TopologicalSpace.Opens (PrimeSpectrum _)) : Set (PrimeSpectrum _))` using `hl ▸ Set.mem_range_self w`.

Use `PrimeSpectrum.ext (huniq _ inferInstance ⟨?_⟩ h1)` and prove the remaining obligations. Conclude with `hP'P.over.trans congr(($hw).1).symm`.
-/
theorem exists_finite_piece {X S : Scheme.{0}} (f : X ⟶ S) [LocallyOfFiniteType f]
    {x : X} (hx : f.QuasiFiniteAt x) :
    ∃ (T : Scheme.{0}) (g : T ⟶ S) (Z : Scheme.{0}) (io : Z ⟶ pullback f g) (z : Z), Etale g ∧
      IsOpenImmersion io ∧ IsFinite (io ≫ pullback.snd f g) ∧ (io ≫ pullback.fst f g) z = x ∧
      ∀ w, (io ≫ pullback.snd f g) w = (io ≫ pullback.snd f g) z → w = z := by
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, -⟩ := S.isBasis_affineOpens.exists_subset_of_mem_open
    (Set.mem_univ (f x)) isOpen_univ
  obtain ⟨_, ⟨V, hV, rfl⟩, hxV, hUV : V ≤ f ⁻¹ᵁ U⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open hxU (f ⁻¹ᵁ U).2
  have : (f.appLE U V hUV).hom.FiniteType := f.finiteType_appLE hU hV hUV
  algebraize [(f.appLE U V hUV).hom]
  have : (hV.primeIdealOf ⟨x, hxV⟩).asIdeal.LiesOver (hU.primeIdealOf ⟨f x, hxU⟩).asIdeal := by
    suffices hU.primeIdealOf ⟨f x, hxU⟩ = Spec.map (f.appLE U V hUV) (hV.primeIdealOf ⟨x, hxV⟩) from
      ⟨congr(($this).1)⟩
    apply hU.isoSpec.inv.homeomorph.injective
    apply Subtype.ext
    simp only [IsAffineOpen.primeIdealOf, Scheme.Hom.homeomorph_apply,
      ← Scheme.Hom.comp_apply, ← Scheme.Opens.ι_apply, IsAffineOpen.isoSpec_hom]
    simp
  have : Algebra.QuasiFiniteAt Γ(S, U) (hV.primeIdealOf ⟨x, hxV⟩).asIdeal :=
    hx.quasiFiniteAt hV hU hUV hxV
  obtain ⟨R, _, _, _, P, _, _, e, _, P', _, hP'P, hP', heP', -, _, huniq⟩ :=
    Algebra.exists_etale_isIdempotentElem_forall_liesOver_eq
    (hU.primeIdealOf ⟨f x, hxU⟩).asIdeal (hV.primeIdealOf ⟨x, hxV⟩).asIdeal
  have hfin : (algebraMap R (Localization.Away e)).Finite := RingHom.finite_algebraMap.mpr ‹_›
  let φ : Γ(S, U) ⟶ .of R := CommRingCat.ofHom <| algebraMap Γ(S, U) R
  have hφ : φ.hom.Etale := RingHom.etale_algebraMap.mpr ‹_›
  have : Etale (Spec.map φ) := HasRingHomProperty.Spec_iff.mpr hφ
  let e₁ : Spec (.of (R ⊗[Γ(S, U)] Γ(X, V))) ≅ pullback (Spec.map (f.appLE U V hUV)) (Spec.map φ) :=
    (pullbackSpecIso _ _ _).symm ≪≫ pullbackSymmetry _ _
  have he₁ : e₁.hom ≫ pullback.fst _ _ =
      Spec.map (CommRingCat.ofHom Algebra.TensorProduct.includeRight.toRingHom) := by
    dsimp [e₁, RingHom.algebraMap_toAlgebra]
    rw [Category.assoc, pullbackSymmetry_hom_comp_fst]
    exact pullbackSpecIso_inv_snd ..
  let g : Spec (.of (R ⊗[Γ(S, U)] Γ(X, V))) ⟶ pullback f (Spec.map φ ≫ hU.fromSpec) :=
    e₁.hom ≫ pullback.map _ _ _ _ hV.fromSpec (𝟙 _) hU.fromSpec
      (IsAffineOpen.SpecMap_appLE_fromSpec ..) (by simp)
  let l : Spec (.of (Localization.Away e)) ⟶ Spec (.of (R ⊗[Γ(S, U)] Γ(X, V))) :=
    Spec.map (CommRingCat.ofHom <| algebraMap _ _)
  have hl : Set.range l = ((PrimeSpectrum.basicOpen e : TopologicalSpace.Opens (PrimeSpectrum _)) : Set (PrimeSpectrum _)) := PrimeSpectrum.localization_away_comap_range _ _
  have hg : g ≫ pullback.snd f _ = Spec.map (CommRingCat.ofHom (algebraMap R _)) := by
    have H : (pullbackSpecIso _ R _).inv ≫ pullback.fst _ (Spec.map (f.appLE U V hUV)) = _ :=
      pullbackSpecIso_inv_fst ..
    simp [g, e₁, RingHom.algebraMap_toAlgebra, φ, H]
    rfl
  obtain ⟨z, hz⟩ : (⟨P', ‹_›⟩ : PrimeSpectrum _) ∈ Set.range l := by rw [hl]; exact heP'
  refine ⟨Spec (.of R), Spec.map φ ≫ hU.fromSpec, _, l ≫ g, z, inferInstance, inferInstance, ?_, ?_, ?_⟩
  · rw [Category.assoc, hg, ← Spec.map_comp, IsFinite.SpecMap_iff]
    exact hfin
  · rw [Category.assoc, Scheme.Hom.comp_apply, hz]
    trans hV.fromSpec ⟨P'.comap Algebra.TensorProduct.includeRight.toRingHom, inferInstance⟩
    · simp [-Scheme.Hom.comp_base, g, reassoc_of% he₁]; rfl
    convert! hV.fromSpec_primeIdealOf ⟨x, hxV⟩
  · intro w hw
    rw [Category.assoc, hg, Scheme.Hom.comp_apply, Scheme.Hom.comp_apply, hz] at hw
    apply l.isOpenEmbedding.injective
    rw [hz]
    have h1 : l w ∈ ((PrimeSpectrum.basicOpen e : TopologicalSpace.Opens (PrimeSpectrum _)) : Set (PrimeSpectrum _)) := hl ▸ Set.mem_range_self w
    refine PrimeSpectrum.ext (huniq _ inferInstance ⟨?_⟩ h1)
    exact hP'P.over.trans congr(($hw).1).symm

/- English proof (translation)
Establish `: IsClosedImmersion (pullback.snd j w)` using `.of_isPreimmersion _ (isClosed_discrete _)`. Establish `: Surjective (pullback.snd j w)` using `⟨fun s => by`. Take `⟨a, ha⟩` from `h s`. Take `⟨z, -, hz⟩` from `Scheme.Pullback.exists_preimage_pullback _ _ ha`. Conclude with `⟨z, hz⟩⟩`.

Use `isIso_of_isClosedImmersion_of_surjective (pullback.snd j w)` as an intermediate fact. Conclude with `⟨inv (pullback.snd j w) ≫ pullback.fst j w, by simp [pullback.condition]⟩`.
-/
theorem exists_factor_of_isPreimmersion {A X : Scheme.{0}} (j : A ⟶ X) [IsPreimmersion j]
    {Ω : Type} [Field Ω] (w : Spec (.of Ω) ⟶ X) (h : ∀ s, w s ∈ Set.range j) :
    ∃ c : Spec (.of Ω) ⟶ A, c ≫ j = w := by
  have : IsClosedImmersion (pullback.snd j w) := .of_isPreimmersion _ (isClosed_discrete _)
  have : Surjective (pullback.snd j w) := ⟨fun s => by
    obtain ⟨a, ha⟩ := h s
    obtain ⟨z, -, hz⟩ := Scheme.Pullback.exists_preimage_pullback _ _ ha
    exact ⟨z, hz⟩⟩
  have := isIso_of_isClosedImmersion_of_surjective (pullback.snd j w)
  exact ⟨inv (pullback.snd j w) ≫ pullback.fst j w, by simp [pullback.condition]⟩

/- English proof (translation)
Take `⟨a, ha⟩` from `h`. Take `⟨z, -, -⟩` from `Scheme.Pullback.exists_preimage_pullback _ _ ha`. Establish `: JacobsonSpace ↥(pullback b t)` using `LocallyOfFiniteType.jacobsonSpace (pullback.snd b t)`. Take `⟨x, -, hx⟩` from `nonempty_inter_closedPoints (Z := (Set.univ : Set ↥(pullback b t))) ⟨z, trivial⟩ isOpen_univ.isLocallyClosed`. Establish `hx' : IsClosed {x}` using `hx`.

Conclude with `⟨pointOfClosedPoint (pullback.snd b t) x hx' ≫ pullback.fst b t, by rw [Category.assoc, pullback.condition, pointOfClosedPoint_comp_assoc]⟩`.
-/
theorem exists_lift_of_isAlgClosed {Z T : Scheme.{0}} (b : Z ⟶ T) [LocallyOfFiniteType b]
    {Ω : Type} [Field Ω] [IsAlgClosed Ω] (t : Spec (.of Ω) ⟶ T) (s) (h : t s ∈ Set.range b) :
    ∃ w : Spec (.of Ω) ⟶ Z, w ≫ b = t := by
  obtain ⟨a, ha⟩ := h
  obtain ⟨z, -, -⟩ := Scheme.Pullback.exists_preimage_pullback _ _ ha
  have : JacobsonSpace ↥(pullback b t) := LocallyOfFiniteType.jacobsonSpace (pullback.snd b t)
  obtain ⟨x, -, hx⟩ := nonempty_inter_closedPoints (Z := (Set.univ : Set ↥(pullback b t))) ⟨z, trivial⟩
    isOpen_univ.isLocallyClosed
  have hx' : IsClosed {x} := hx
  exact ⟨pointOfClosedPoint (pullback.snd b t) x hx' ≫ pullback.fst b t, by rw [Category.assoc, pullback.condition, pointOfClosedPoint_comp_assoc]⟩

/- English proof (translation)
Take `⟨_, ⟨V, hV, rfl⟩, hyV, -⟩` from `Y.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ (y (closedPoint L))) isOpen_univ`. Take `⟨R, io, _, hio⟩ : ∃ (R : CommRingCat.{0}) (io : Spec R ⟶ Y) (_ : IsOpenImmersion io), y (closedPoint L) ∈ Set.range io` from `⟨_, hV.fromSpec, hV.isOpenImmersion_fromSpec, by rwa [hV.range_fromSpec]⟩`. Take `⟨c, rfl⟩` from `exists_factor_of_isPreimmersion io y fun s => by`. Rewrite using `[Subsingleton.elim s (closedPoint L)]` and apply the resulting hypothesis. Take `⟨φ, rfl⟩` from `Spec.map_surjective c`.

Establish `hq : LocallyQuasiFinite (Spec.map φ)` using `.of_comp _ io`. Rewrite `hq` using `[HasRingHomProperty.Spec_iff (P := @LocallyQuasiFinite)]`. Use `algebraize [φ.hom]`. Take `⟨R₁, _, _, _, ψ, hψ⟩` from `exists_etale_algebra R L`. Establish `: Etale (Spec.map (CommRingCat.ofHom (algebraMap R R₁)))` using `HasRingHomProperty.Spec_iff.mpr (RingHom.etale_algebraMap.mpr ‹_›)`.

Use `⟨Spec (.of R₁), Spec.map (CommRingCat.ofHom (algebraMap R R₁)) ≫ io, Spec.map (CommRingCat.ofHom ψ.toRingHom), inferInstance, ?_, fun Ω _ c₁ c₂ h => ?_⟩` and prove the remaining obligations. Rewrite using `[← Spec.map_comp_assoc]`. Use `congr 2`. Use extensionality with `r`. Conclude with `ψ.commutes r`.

Take `⟨a₁, rfl⟩` from `Spec.map_surjective c₁`. Take `⟨a₂, rfl⟩` from `Spec.map_surjective c₂`. Rewrite `h` using `[← Spec.map_comp, ← Spec.map_comp, Spec.map_inj]`. Use `congr 1`. Conclude with `CommRingCat.hom_ext (hψ Ω _ _ congr(($h).hom))`.
-/
theorem exists_etale_point {Y : Scheme.{0}} {L : Type} [Field L] (y : Spec (.of L) ⟶ Y)
    [LocallyQuasiFinite y] :
    ∃ (T : Scheme.{0}) (h : T ⟶ Y) (s : Spec (.of L) ⟶ T), Etale h ∧ s ≫ h = y ∧
      ∀ (Ω : Type) [Field Ω] (c₁ c₂ : Spec (.of Ω) ⟶ Spec (.of L)), c₁ ≫ s = c₂ ≫ s → c₁ = c₂ := by
  obtain ⟨_, ⟨V, hV, rfl⟩, hyV, -⟩ := Y.isBasis_affineOpens.exists_subset_of_mem_open
    (Set.mem_univ (y (closedPoint L))) isOpen_univ
  obtain ⟨R, io, _, hio⟩ : ∃ (R : CommRingCat.{0}) (io : Spec R ⟶ Y) (_ : IsOpenImmersion io),
      y (closedPoint L) ∈ Set.range io := ⟨_, hV.fromSpec, hV.isOpenImmersion_fromSpec, by rwa [hV.range_fromSpec]⟩
  obtain ⟨c, rfl⟩ := exists_factor_of_isPreimmersion io y fun s => by
    rwa [Subsingleton.elim s (closedPoint L)]
  obtain ⟨φ, rfl⟩ := Spec.map_surjective c
  have hq : LocallyQuasiFinite (Spec.map φ) := .of_comp _ io
  rw [HasRingHomProperty.Spec_iff (P := @LocallyQuasiFinite)] at hq
  algebraize [φ.hom]
  obtain ⟨R₁, _, _, _, ψ, hψ⟩ := exists_etale_algebra R L
  have : Etale (Spec.map (CommRingCat.ofHom (algebraMap R R₁))) :=
    HasRingHomProperty.Spec_iff.mpr (RingHom.etale_algebraMap.mpr ‹_›)
  refine ⟨Spec (.of R₁), Spec.map (CommRingCat.ofHom (algebraMap R R₁)) ≫ io,
    Spec.map (CommRingCat.ofHom ψ.toRingHom), inferInstance, ?_, fun Ω _ c₁ c₂ h => ?_⟩
  · rw [← Spec.map_comp_assoc]
    congr 2
    ext r
    exact ψ.commutes r
  · obtain ⟨a₁, rfl⟩ := Spec.map_surjective c₁
    obtain ⟨a₂, rfl⟩ := Spec.map_surjective c₂
    rw [← Spec.map_comp, ← Spec.map_comp, Spec.map_inj] at h
    congr 1
    exact CommRingCat.hom_ext (hψ Ω _ _ congr(($h).hom))

/- English proof (translation)
Rewrite using `[Scheme.Hom.quasiFiniteAt_iff_isOpen_singleton_asFiber, ← (φ.fiberHomeo (φ z)).isOpen_image]`. Simplify using `only [Set.image_singleton, Scheme.Hom.asFiber, Homeomorph.apply_symm_apply]`. Rewrite using `[isOpen_induced_iff]`. Use `⟨O, O.isOpen, ?_⟩` and prove the remaining obligations. Use extensionality with `⟨w, hw⟩`.

Simplify using `only [Set.mem_preimage, Set.mem_singleton_iff]`. Prove the components needed by the constructor for the conclusion. Introduce `h`. Conclude with `Subtype.ext (hO w h hw)`. Introduce `h`.

Establish `: w = z` using `congrArg Subtype.val h`. Conclude with `this ▸ hzO`.
-/
theorem quasiFiniteAt_of_isolated {H X : Scheme.{0}} (φ : H ⟶ X) [LocallyOfFiniteType φ]
    (z : H) (O : H.Opens) (hzO : z ∈ O) (hO : ∀ w ∈ O, φ w = φ z → w = z) : φ.QuasiFiniteAt z := by
  rw [Scheme.Hom.quasiFiniteAt_iff_isOpen_singleton_asFiber, ← (φ.fiberHomeo (φ z)).isOpen_image]
  simp only [Set.image_singleton, Scheme.Hom.asFiber, Homeomorph.apply_symm_apply]
  rw [isOpen_induced_iff]
  refine ⟨O, O.isOpen, ?_⟩
  ext ⟨w, hw⟩
  simp only [Set.mem_preimage, Set.mem_singleton_iff]
  constructor
  · intro h
    exact Subtype.ext (hO w h hw)
  · intro h
    have : w = z := congrArg Subtype.val h
    exact this ▸ hzO

set_option backward.isDefEq.respectTransparency false in

/- English proof (translation)
Introduce `U Y τ _ _ _ x ⟨O, hxO, hO⟩`. Establish `hx : τ.QuasiFiniteAt x` using `quasiFiniteAt_of_isolated τ x O hxO hO`. Set `Q : U.Opens` to `τ.quasiFiniteLocus`. Establish `hxQ : x ∈ Q` using `hx`. Establish `hQ : LocallyQuasiFinite (Q.ι ≫ τ)`.

Rewrite using `[← Scheme.Hom.quasiFiniteLocus_eq_top_iff, Scheme.Hom.quasiFiniteLocus_comp]`. Conclude with `top_le_iff.mp fun u _ => by show Q.ι u ∈ Q`. Simplify using `using u.2`. Establish `hfx : ∀ a : Spec (.of (U.residueField x)), U.fromSpecResidueField x a = x` using `fun a => Scheme.fromSpecResidueField_apply x a`. Set `y₀ : Spec (.of (U.residueField x)) ⟶ Y` to `U.fromSpecResidueField x ≫ τ`.

Establish `: LocallyQuasiFinite y₀`. Rewrite `hx` using `[Scheme.Hom.quasiFiniteAt_iff]`. Simplify using `only [y₀, Scheme.fromSpecResidueField]`. Rewrite using `[Category.assoc]`. Use `infer_instance`.

Take `⟨T₁, h₁, s, _, hs, hsep⟩` from `exists_etale_point y₀`. Set `j : Spec (.of (U.residueField x)) ⟶ pullback τ h₁` to `pullback.lift (U.fromSpecResidueField x) s (by rw [hs])`. Establish `hjf : j ≫ pullback.fst τ h₁ = U.fromSpecResidueField x` using `pullback.lift_fst ..`. Establish `hjs : j ≫ pullback.snd τ h₁ = s` using `pullback.lift_snd ..`. Use `haveI : IsPreimmersion (j ≫ pullback.fst τ h₁) := by rw [hjf]; infer_instance`.

Use `haveI : IsPreimmersion j := AmpUniq.isPreimmersion_of_comp j (pullback.fst τ h₁)`. Set `x₁` to `j (closedPoint _)`. Set `σ : Spec (.of (U.residueField x)) ⟶ Q` to `IsOpenImmersion.lift Q.ι (U.fromSpecResidueField x) (by`. Introduce and unpack `_ ⟨a, rfl⟩`. Conclude with `⟨⟨x, hxQ⟩, (hfx a).symm⟩)`.

Set `j' : Spec (.of (U.residueField x)) ⟶ pullback (Q.ι ≫ τ) h₁` to `pullback.lift σ s (by rw [← Category.assoc, IsOpenImmersion.lift_fac, hs])`. Set `m` to `pullback.map (Q.ι ≫ τ) h₁ τ h₁ Q.ι (𝟙 _) (𝟙 _) (by simp) (by simp)`. Establish `hjm : j' ≫ m = j`. Apply `pullback.hom_ext` to reduce the goal to its premises. Simplify using `[m, j', j, σ]`.

Simplify using `[m, j', j]`. Establish `hqf : (pullback.snd τ h₁).QuasiFiniteAt x₁`. Establish `hms : m ≫ pullback.snd τ h₁ = pullback.snd (Q.ι ≫ τ) h₁` using `by simp [m]`. Establish `: x₁ = m (j' (closedPoint _))`. Simplify using `only [x₁, ← hjm, Scheme.Hom.comp_apply]`.

Rewrite using `[this, ← Scheme.Hom.quasiFiniteAt_comp_iff_of_isOpenImmersion, hms]`. Conclude with `Scheme.Hom.quasiFiniteAt _ _`. Take `⟨T₂, g₂, Z, io, z, _, _, hfin, hz, huniq⟩` from `exists_finite_piece (pullback.snd τ h₁) hqf`. Set `b` to `io ≫ pullback.snd (pullback.snd τ h₁) g₂`. Establish `hbg : ∀ {V : Scheme.{0}} (u : V ⟶ Z), u ≫ io ≫ pullback.fst _ _ ≫ pullback.snd τ h₁ = u ≫ b ≫ g₂`.

Introduce `V u`. Simplify using `[b, pullback.condition]`. Establish `G : ∀ (Ω : Type) [Field Ω] (u₁ u₂ : Spec (.of Ω) ⟶ Z), u₁ ≫ b = u₂ ≫ b → (∀ a, u₁ a = z) → (∀ a, u₂ a = z) → u₁ = u₂`. Introduce `Ω _ u₁ u₂ hb h₁' h₂'`. Establish `hr : ∀ u : Spec (.of Ω) ⟶ Z, (∀ a, u a = z) → ∃ c : Spec (.of Ω) ⟶ Spec (.of (U.residueField x)), c ≫ j = u ≫ io ≫ pullback.fst _ _` using `fun u hu => exists_factor_of_isPreimmersion j _ fun a => ⟨closedPoint _, by`.

Simplify using `only [Scheme.Hom.comp_apply, hu]`. Conclude with `hz.symm⟩`. Take `⟨c₁, hc₁⟩` from `hr u₁ h₁'`. Take `⟨c₂, hc₂⟩` from `hr u₂ h₂'`. Establish `hcs : ∀ (c : Spec (.of Ω) ⟶ Spec (.of (U.residueField x))) (u : Spec (.of Ω) ⟶ Z), c ≫ j = u ≫ io ≫ pullback.fst _ _ → c ≫ s = u ≫ b ≫ g₂`.

Introduce `c u hcu`. Rewrite using `[← hjs, ← Category.assoc, hcu, Category.assoc, Category.assoc, hbg]`. Establish `hc : c₁ = c₂` using `hsep Ω c₁ c₂ (by rw [hcs c₁ u₁ hc₁, hcs c₂ u₂ hc₂, reassoc_of% hb])`. Rewrite using `[← cancel_mono io]`. Apply `pullback.hom_ext` to reduce the goal to its premises.

Rewrite using `[Category.assoc, Category.assoc, ← hc₁, ← hc₂, hc]`. Simplify `hb` using `[b]`. Use `haveI : IsLocallyNoetherian T₂ := LocallyOfFiniteType.isLocallyNoetherian (g₂ ≫ h₁)`. Set `C : T₂.Opens` to `⟨connectedComponent (b z), GlobalTheory.isOpen_connectedComponent_of_isLocallyNoetherian T₂ inferInstance (b z)⟩`. Establish `hzC : b z ∈ C` using `mem_connectedComponent`.

Set `h : C.toScheme ⟶ Y` to `C.ι ≫ g₂ ≫ h₁`. Set `Z' : Z.Opens` to `b ⁻¹ᵁ C`. Set `b' : Z'.toScheme ⟶ C.toScheme` to `b ∣_ C`. Establish `hb' : b' ≫ C.ι = Z'.ι ≫ b` using `morphismRestrict_ι b C`. Set `io' : Z'.toScheme ⟶ pullback τ h` to `pullback.lift (Z'.ι ≫ io ≫ pullback.fst _ _ ≫ pullback.fst τ h₁) b' (by`.

Simplify using `only [h, Category.assoc, pullback.condition]`. Rewrite using `[reassoc_of% hb']`. Simplify using `using congr($(hbg Z'.ι) ≫ h₁))`. Establish `hio'f : io' ≫ pullback.fst τ h = Z'.ι ≫ io ≫ pullback.fst _ _ ≫ pullback.fst τ h₁` using `pullback.lift_fst ..`. Establish `hio's : io' ≫ pullback.snd τ h = b'` using `pullback.lift_snd ..`.

Set `mC` to `pullback.map τ h τ (g₂ ≫ h₁) (𝟙 _) C.ι (𝟙 _) (by simp) (by simp [h])`. Establish `hmC : io' ≫ mC = Z'.ι ≫ io ≫ (pullbackLeftPullbackSndIso τ h₁ g₂).hom`. Apply `pullback.hom_ext` to reduce the goal to its premises. Simplify using `[mC, hio'f]`. Simplify using `only [mC, Category.assoc, pullback.lift_snd, pullbackLeftPullbackSndIso_hom_snd]`.

Rewrite using `[← Category.assoc, hio's, hb']`. Use `haveI : IsOpenImmersion (io' ≫ mC) := by rw [hmC]; infer_instance`. Use `haveI : IsOpenImmersion io' := IsOpenImmersion.of_comp io' mC`. Set `z' : Z'` to `⟨z, hzC⟩`. Use `haveI : IsFinite b := hfin`.

Establish `hb'inj : ∀ w : Z', b' w = b' z' → w = z'`. Introduce `w hw`. Apply `Subtype.ext` to reduce the goal to its premises. Apply `huniq` to reduce the goal to its premises. Use `congr(C.ι $hw)` as an intermediate fact.

Rewrite `this` using `[← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, hb', Scheme.Hom.comp_apply, Scheme.Hom.comp_apply]`. Simplify using `only [Scheme.Hom.comp_apply, Scheme.Opens.ι_apply] at this ⊢`. Conclude with `this`. Establish `he : io'.opensRange.ι = io'.isoOpensRange.inv ≫ io'`. Rewrite using `[Iso.eq_inv_comp, Scheme.Hom.isoOpensRange_hom_ι]`.

Use `⟨C.toScheme, h, io'.opensRange, io' z', inferInstance, ?_, ⟨z', rfl⟩, ?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Conclude with `isPreconnected_iff_preconnectedSpace.mp isPreconnected_connectedComponent`. Rewrite using `[← Scheme.Hom.comp_apply, hio'f]`. Simplify using `only [Scheme.Hom.comp_apply]`. Express the relevant statement in the definitionally equal form `pullback.fst τ h₁ ((io ≫ pullback.fst _ _) z) = x`.

Rewrite using `[hz, ← Scheme.Hom.comp_apply, hjf]`. Conclude with `hfx _`. Rewrite using `[he, Category.assoc, hio's, MorphismProperty.cancel_left_of_respectsIso @IsFinite] infer_instance`. Introduce and unpack `_ ⟨w, rfl⟩ hw`. Rewrite `hw` using `[← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, hio's]`.

Rewrite using `[hb'inj w hw]`. Introduce `Ω _ _ t ht`. Establish `hpt : pullback.snd τ h (io' z') = b' z'` using `by rw [← Scheme.Hom.comp_apply, hio's]`. Establish `htz : ∀ a, t a = b' z'` using `fun a => by`. Rewrite using `[← hpt]`.

Establish `: t a ∈ Set.range t` using `Set.mem_range_self a`. Rewrite `this` using `[ht]`. Then use the resulting hypothesis. Establish `hpts : ∀ u : Spec (.of Ω) ⟶ Z', u ≫ b' = t → ∀ a, (u ≫ Z'.ι) a = z` using `fun u hu a => by`. Establish `: b' (u a) = b' z'` using `by rw [← Scheme.Hom.comp_apply, hu, htz]`. Rewrite using `[Scheme.Hom.comp_apply, hb'inj _ this]`.

Simplify using `[z']`. Take `⟨w₀, hw₀⟩` from `exists_lift_of_isAlgClosed b' t (closedPoint Ω) ⟨z', (htz _).symm⟩`. Use `⟨w₀ ≫ io'.isoOpensRange.hom, ?_, fun w hw => ?_⟩` and prove the remaining obligations. Rewrite using `[he]`. Simplify using `[hio's, hw₀]`.

Establish `hv : w ≫ io'.isoOpensRange.inv ≫ b' = t`. Rewrite using `[← hw, ← hio's, he]`. Simplify using `only [Category.assoc]`. Establish `key : (w ≫ io'.isoOpensRange.inv) ≫ Z'.ι = w₀ ≫ Z'.ι` using `G Ω _ _ (by simp only [Category.assoc]; rw [← hb', reassoc_of% hv, reassoc_of% hw₀]) (hpts _ (by rw [Category.assoc]; exact hv)) (hpts _ hw₀)`. Establish `hv' : w ≫ io'.isoOpensRange.inv = w₀` using `by rw [← cancel_mono Z'.ι]; exact key`.

Rewrite using `[← hv']`. Simplify using the standard rewrite rules.
-/
theorem main : ∀ (U Y : Scheme.{0}) (τ : U ⟶ Y), IsLocallyNoetherian Y → LocallyOfFiniteType τ → IsSeparated τ →
    ∀ x : U, (∃ O : U.Opens, x ∈ O ∧ ∀ u ∈ O, τ u = τ x → u = x) →
    ∃ (T : Scheme.{0}) (h : T ⟶ Y) (W : (pullback τ h).Opens) (p : ↥(pullback τ h)),
      Etale h ∧ PreconnectedSpace T ∧ p ∈ W ∧ pullback.fst τ h p = x ∧ IsFinite (W.ι ≫ pullback.snd τ h) ∧
      (∀ w ∈ W, pullback.snd τ h w = pullback.snd τ h p → w = p) ∧
      ∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] (t : Sp Ω ⟶ T), Set.range t = {pullback.snd τ h p} →
        ∃! w : Sp Ω ⟶ W.toScheme, w ≫ W.ι ≫ pullback.snd τ h = t := by
  intro U Y τ _ _ _ x ⟨O, hxO, hO⟩
  have hx : τ.QuasiFiniteAt x := quasiFiniteAt_of_isolated τ x O hxO hO

  let Q : U.Opens := τ.quasiFiniteLocus
  have hxQ : x ∈ Q := hx
  have hQ : LocallyQuasiFinite (Q.ι ≫ τ) := by
    rw [← Scheme.Hom.quasiFiniteLocus_eq_top_iff, Scheme.Hom.quasiFiniteLocus_comp]
    exact top_le_iff.mp fun u _ => by
      show Q.ι u ∈ Q
      simpa using u.2
  have hfx : ∀ a : Spec (.of (U.residueField x)), U.fromSpecResidueField x a = x :=
    fun a => Scheme.fromSpecResidueField_apply x a

  let y₀ : Spec (.of (U.residueField x)) ⟶ Y := U.fromSpecResidueField x ≫ τ
  have : LocallyQuasiFinite y₀ := by
    rw [Scheme.Hom.quasiFiniteAt_iff] at hx
    dsimp only [y₀, Scheme.fromSpecResidueField]
    rw [Category.assoc]
    infer_instance
  obtain ⟨T₁, h₁, s, _, hs, hsep⟩ := exists_etale_point y₀
  let j : Spec (.of (U.residueField x)) ⟶ pullback τ h₁ :=
    pullback.lift (U.fromSpecResidueField x) s (by rw [hs])
  have hjf : j ≫ pullback.fst τ h₁ = U.fromSpecResidueField x := pullback.lift_fst ..
  have hjs : j ≫ pullback.snd τ h₁ = s := pullback.lift_snd ..
  haveI : IsPreimmersion (j ≫ pullback.fst τ h₁) := by rw [hjf]; infer_instance
  haveI : IsPreimmersion j := AmpUniq.isPreimmersion_of_comp j (pullback.fst τ h₁)
  let x₁ := j (closedPoint _)

  let σ : Spec (.of (U.residueField x)) ⟶ Q :=
    IsOpenImmersion.lift Q.ι (U.fromSpecResidueField x) (by
      rintro _ ⟨a, rfl⟩
      exact ⟨⟨x, hxQ⟩, (hfx a).symm⟩)
  let j' : Spec (.of (U.residueField x)) ⟶ pullback (Q.ι ≫ τ) h₁ :=
    pullback.lift σ s (by rw [← Category.assoc, IsOpenImmersion.lift_fac, hs])
  let m := pullback.map (Q.ι ≫ τ) h₁ τ h₁ Q.ι (𝟙 _) (𝟙 _) (by simp) (by simp)
  have hjm : j' ≫ m = j := by
    apply pullback.hom_ext
    · simp [m, j', j, σ]
    · simp [m, j', j]
  have hqf : (pullback.snd τ h₁).QuasiFiniteAt x₁ := by
    have hms : m ≫ pullback.snd τ h₁ = pullback.snd (Q.ι ≫ τ) h₁ := by simp [m]
    have : x₁ = m (j' (closedPoint _)) := by
      simp only [x₁, ← hjm, Scheme.Hom.comp_apply]
    rw [this, ← Scheme.Hom.quasiFiniteAt_comp_iff_of_isOpenImmersion, hms]
    exact Scheme.Hom.quasiFiniteAt _ _

  obtain ⟨T₂, g₂, Z, io, z, _, _, hfin, hz, huniq⟩ := exists_finite_piece (pullback.snd τ h₁) hqf
  let b := io ≫ pullback.snd (pullback.snd τ h₁) g₂
  have hbg : ∀ {V : Scheme.{0}} (u : V ⟶ Z), u ≫ io ≫ pullback.fst _ _ ≫ pullback.snd τ h₁ = u ≫ b ≫ g₂ := by
    intro V u; simp [b, pullback.condition]

  have G : ∀ (Ω : Type) [Field Ω] (u₁ u₂ : Spec (.of Ω) ⟶ Z), u₁ ≫ b = u₂ ≫ b →
      (∀ a, u₁ a = z) → (∀ a, u₂ a = z) → u₁ = u₂ := by
    intro Ω _ u₁ u₂ hb h₁' h₂'
    have hr : ∀ u : Spec (.of Ω) ⟶ Z, (∀ a, u a = z) →
        ∃ c : Spec (.of Ω) ⟶ Spec (.of (U.residueField x)), c ≫ j = u ≫ io ≫ pullback.fst _ _ :=
      fun u hu => exists_factor_of_isPreimmersion j _ fun a => ⟨closedPoint _, by
        simp only [Scheme.Hom.comp_apply, hu]
        exact hz.symm⟩
    obtain ⟨c₁, hc₁⟩ := hr u₁ h₁'
    obtain ⟨c₂, hc₂⟩ := hr u₂ h₂'
    have hcs : ∀ (c : Spec (.of Ω) ⟶ Spec (.of (U.residueField x))) (u : Spec (.of Ω) ⟶ Z),
        c ≫ j = u ≫ io ≫ pullback.fst _ _ → c ≫ s = u ≫ b ≫ g₂ := by
      intro c u hcu
      rw [← hjs, ← Category.assoc, hcu, Category.assoc, Category.assoc, hbg]
    have hc : c₁ = c₂ := hsep Ω c₁ c₂ (by rw [hcs c₁ u₁ hc₁, hcs c₂ u₂ hc₂, reassoc_of% hb])
    rw [← cancel_mono io]
    apply pullback.hom_ext
    · rw [Category.assoc, Category.assoc, ← hc₁, ← hc₂, hc]
    · simpa [b] using hb

  haveI : IsLocallyNoetherian T₂ := LocallyOfFiniteType.isLocallyNoetherian (g₂ ≫ h₁)
  let C : T₂.Opens := ⟨connectedComponent (b z),
    GlobalTheory.isOpen_connectedComponent_of_isLocallyNoetherian T₂ inferInstance (b z)⟩
  have hzC : b z ∈ C := mem_connectedComponent
  let h : C.toScheme ⟶ Y := C.ι ≫ g₂ ≫ h₁
  let Z' : Z.Opens := b ⁻¹ᵁ C
  let b' : Z'.toScheme ⟶ C.toScheme := b ∣_ C
  have hb' : b' ≫ C.ι = Z'.ι ≫ b := morphismRestrict_ι b C
  let io' : Z'.toScheme ⟶ pullback τ h :=
    pullback.lift (Z'.ι ≫ io ≫ pullback.fst _ _ ≫ pullback.fst τ h₁) b' (by
      simp only [h, Category.assoc, pullback.condition]
      rw [reassoc_of% hb']
      simpa using congr($(hbg Z'.ι) ≫ h₁))
  have hio'f : io' ≫ pullback.fst τ h = Z'.ι ≫ io ≫ pullback.fst _ _ ≫ pullback.fst τ h₁ := pullback.lift_fst ..
  have hio's : io' ≫ pullback.snd τ h = b' := pullback.lift_snd ..
  let mC := pullback.map τ h τ (g₂ ≫ h₁) (𝟙 _) C.ι (𝟙 _) (by simp) (by simp [h])
  have hmC : io' ≫ mC = Z'.ι ≫ io ≫ (pullbackLeftPullbackSndIso τ h₁ g₂).hom := by
    apply pullback.hom_ext
    · simp [mC, hio'f]
    · simp only [mC, Category.assoc, pullback.lift_snd, pullbackLeftPullbackSndIso_hom_snd]
      rw [← Category.assoc, hio's, hb']
  haveI : IsOpenImmersion (io' ≫ mC) := by rw [hmC]; infer_instance
  haveI : IsOpenImmersion io' := IsOpenImmersion.of_comp io' mC
  let z' : Z' := ⟨z, hzC⟩
  haveI : IsFinite b := hfin
  have hb'inj : ∀ w : Z', b' w = b' z' → w = z' := by
    intro w hw
    apply Subtype.ext
    apply huniq
    have := congr(C.ι $hw)
    rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, hb', Scheme.Hom.comp_apply,
      Scheme.Hom.comp_apply] at this
    simp only [Scheme.Hom.comp_apply, Scheme.Opens.ι_apply] at this ⊢
    exact this
  have he : io'.opensRange.ι = io'.isoOpensRange.inv ≫ io' := by
    rw [Iso.eq_inv_comp, Scheme.Hom.isoOpensRange_hom_ι]
  refine ⟨C.toScheme, h, io'.opensRange, io' z', inferInstance, ?_, ⟨z', rfl⟩, ?_, ?_, ?_, ?_⟩
  · exact isPreconnected_iff_preconnectedSpace.mp isPreconnected_connectedComponent
  · rw [← Scheme.Hom.comp_apply, hio'f]
    simp only [Scheme.Hom.comp_apply]
    change pullback.fst τ h₁ ((io ≫ pullback.fst _ _) z) = x
    rw [hz, ← Scheme.Hom.comp_apply, hjf]
    exact hfx _
  · rw [he, Category.assoc, hio's, MorphismProperty.cancel_left_of_respectsIso @IsFinite]
    infer_instance
  · rintro _ ⟨w, rfl⟩ hw
    rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, hio's] at hw
    rw [hb'inj w hw]
  · intro Ω _ _ t ht
    have hpt : pullback.snd τ h (io' z') = b' z' := by rw [← Scheme.Hom.comp_apply, hio's]
    have htz : ∀ a, t a = b' z' := fun a => by
      rw [← hpt]
      have : t a ∈ Set.range t := Set.mem_range_self a
      rwa [ht] at this
    have hpts : ∀ u : Spec (.of Ω) ⟶ Z', u ≫ b' = t → ∀ a, (u ≫ Z'.ι) a = z := fun u hu a => by
      have : b' (u a) = b' z' := by rw [← Scheme.Hom.comp_apply, hu, htz]
      rw [Scheme.Hom.comp_apply, hb'inj _ this]
      simp [z']
    obtain ⟨w₀, hw₀⟩ := exists_lift_of_isAlgClosed b' t (closedPoint Ω) ⟨z', (htz _).symm⟩
    refine ⟨w₀ ≫ io'.isoOpensRange.hom, ?_, fun w hw => ?_⟩
    · rw [he]
      simp [hio's, hw₀]
    · have hv : w ≫ io'.isoOpensRange.inv ≫ b' = t := by
        rw [← hw, ← hio's, he]
        simp only [Category.assoc]
      have key : (w ≫ io'.isoOpensRange.inv) ≫ Z'.ι = w₀ ≫ Z'.ι :=
        G Ω _ _ (by simp only [Category.assoc]; rw [← hb', reassoc_of% hv, reassoc_of% hw₀])
          (hpts _ (by rw [Category.assoc]; exact hv)) (hpts _ hw₀)
      have hv' : w ≫ io'.isoOpensRange.inv = w₀ := by rw [← cancel_mono Z'.ι]; exact key
      rw [← hv']
      simp

end GlobalTheory.EtaleFinitePiece

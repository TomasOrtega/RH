import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.LayerLe
import Mathlib.RingTheory.Unramified.LocalRing

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.Base UpperTheory.Top UpperTheory.V.HV

/- English proof (translation)
Take `⟨s, hs⟩ : (Subalgebra.toSubmodule A).FG` from `Module.Finite.iff_fg.1 hA`. Set `K : IntermediateField ℚ_[l] (PadicAlgCl l)` to `IntermediateField.adjoin ℚ_[l] (s : Set (PadicAlgCl l))`. Use `haveI : FiniteDimensional ℚ_[l] K := IntermediateField.finiteDimensional_adjoin fun x _ => Algebra.IsIntegral.isIntegral x`. Take `⟨h1, h2, -⟩` from `UpperTheory.V.abelian₂.dvr_intClosure l K`. Set `f : K →ₐ[ℤ_[l]] PadicAlgCl l` to `K.val.restrictScalars ℤ_[l]`.

Establish `hf : Function.Injective f` using `Subtype.val_injective`. Set `e` to `(integralClosure ℤ_[l] K).equivMapOfInjective f hf`. Use `⟨⟨(integralClosure ℤ_[l] K).map f, IsDiscreteValuationRing.RingEquivClass.isDiscreteValuationRing e, Module.Finite.equiv e.toLinearEquiv⟩, ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `Subalgebra.toSubmodule A ≤ Subalgebra.toSubmodule ((integralClosure ℤ_[l] K).map f)`. Rewrite using `[← hs, Submodule.span_le]`.

Introduce `x hx`. Establish `hxA : x ∈ A`. Express the relevant statement in the definitionally equal form `x ∈ Subalgebra.toSubmodule A`. Rewrite using `[← hs]`. Conclude with `Submodule.subset_span hx`.

Establish `hi : IsIntegral ℤ_[l] x` using `(Algebra.IsIntegral.isIntegral (R := ℤ_[l]) (⟨x, hxA⟩ : A)).map A.val`. Conclude with `⟨⟨x, IntermediateField.subset_adjoin _ _ hx⟩, (isIntegral_algHom_iff f hf).1 hi, rfl⟩`.
-/
private theorem exists_coef_ge (l : ℕ) [Fact l.Prime] (A : Subalgebra ℤ_[l] (PadicAlgCl l)) [hA : Module.Finite ℤ_[l] A] :
    ∃ c : Coef l, A ≤ c.O := by
  obtain ⟨s, hs⟩ : (Subalgebra.toSubmodule A).FG := Module.Finite.iff_fg.1 hA
  let K : IntermediateField ℚ_[l] (PadicAlgCl l) := IntermediateField.adjoin ℚ_[l] (s : Set (PadicAlgCl l))
  haveI : FiniteDimensional ℚ_[l] K :=
    IntermediateField.finiteDimensional_adjoin fun x _ => Algebra.IsIntegral.isIntegral x
  obtain ⟨h1, h2, -⟩ := UpperTheory.V.abelian₂.dvr_intClosure l K
  let f : K →ₐ[ℤ_[l]] PadicAlgCl l := K.val.restrictScalars ℤ_[l]
  have hf : Function.Injective f := Subtype.val_injective
  let e := (integralClosure ℤ_[l] K).equivMapOfInjective f hf
  refine ⟨⟨(integralClosure ℤ_[l] K).map f, IsDiscreteValuationRing.RingEquivClass.isDiscreteValuationRing e,
    Module.Finite.equiv e.toLinearEquiv⟩, ?_⟩
  change Subalgebra.toSubmodule A ≤ Subalgebra.toSubmodule ((integralClosure ℤ_[l] K).map f)
  rw [← hs, Submodule.span_le]
  intro x hx
  have hxA : x ∈ A := by
    change x ∈ Subalgebra.toSubmodule A
    rw [← hs]
    exact Submodule.subset_span hx
  have hi : IsIntegral ℤ_[l] x := (Algebra.IsIntegral.isIntegral (R := ℤ_[l]) (⟨x, hxA⟩ : A)).map A.val
  exact ⟨⟨x, IntermediateField.subset_adjoin _ _ hx⟩, (isIntegral_algHom_iff f hf).1 hi, rfl⟩

/- English proof (translation)
Set `z : Algebra.adjoin R {ζ}` to `⟨ζ, Algebra.self_mem_adjoin_singleton R ζ⟩`. Establish `hz : z ^ n = 1` using `Subtype.ext hζ`. Set `D` to `KaehlerDifferential.D R (Algebra.adjoin R {ζ})`. Establish `hDz : D z = 0`. Establish `h` using `D.leibniz_pow z n`.

Rewrite `h` using `[hz, Derivation.map_one_eq_zero, ← Nat.cast_smul_eq_nsmul R]`. Conclude with `((IsUnit.of_pow_eq_one hz hn0).pow _).smul_eq_zero.1 (hn.smul_eq_zero.1 h.symm)`. Establish `hD : ∀ x (hx : x ∈ Algebra.adjoin R {ζ}), D ⟨x, hx⟩ = 0`. Introduce `x hx`. Proceed by induction on `hx using Algebra.adjoin_induction with`.

Consider the case `mem x hx => obtain rfl := hx`. Conclude with `hDz`. Consider the case `algebraMap r => exact D.map_algebraMap r`. Consider the case `add x y hx hy h1 h2`. Use `D.map_add ⟨x, hx⟩ ⟨y, hy⟩` as an intermediate fact.

Rewrite `this` using `[h1, h2, add_zero]`. Conclude with `this`. Consider the case `mul x y hx hy h1 h2`. Use `D.leibniz ⟨x, hx⟩ ⟨y, hy⟩` as an intermediate fact. Rewrite `this` using `[h1, h2, smul_zero, smul_zero, add_zero]`.

Conclude with `this`. Use `⟨⟨fun a b => ?_⟩⟩` and prove the remaining obligations. Establish `h` using `KaehlerDifferential.span_range_derivation R (Algebra.adjoin R {ζ})`. Establish `h0 : (⊤ : Submodule (Algebra.adjoin R {ζ}) Ω[Algebra.adjoin R {ζ}⁄R]) ≤ ⊥`. Rewrite using `[← h, Submodule.span_le]`.

Introduce and unpack `_ ⟨x, rfl⟩`. Conclude with `hD x.1 x.2`. Rewrite using `[(Submodule.mem_bot _).1 (h0 (Submodule.mem_top (x := a))), (Submodule.mem_bot _).1 (h0 (Submodule.mem_top (x := b)))]`.
-/
private theorem unram_adjoin {R S : Type} [CommRing R] [CommRing S] [Algebra R S] {n : ℕ} (hn0 : n ≠ 0) (hn : IsUnit (n : R))
    {ζ : S} (hζ : ζ ^ n = 1) : Algebra.FormallyUnramified R (Algebra.adjoin R {ζ}) := by
  let z : Algebra.adjoin R {ζ} := ⟨ζ, Algebra.self_mem_adjoin_singleton R ζ⟩
  have hz : z ^ n = 1 := Subtype.ext hζ
  let D := KaehlerDifferential.D R (Algebra.adjoin R {ζ})
  have hDz : D z = 0 := by
    have h := D.leibniz_pow z n
    rw [hz, Derivation.map_one_eq_zero, ← Nat.cast_smul_eq_nsmul R] at h
    exact ((IsUnit.of_pow_eq_one hz hn0).pow _).smul_eq_zero.1 (hn.smul_eq_zero.1 h.symm)
  have hD : ∀ x (hx : x ∈ Algebra.adjoin R {ζ}), D ⟨x, hx⟩ = 0 := by
    intro x hx
    induction hx using Algebra.adjoin_induction with
    | mem x hx => obtain rfl := hx; exact hDz
    | algebraMap r => exact D.map_algebraMap r
    | add x y hx hy h1 h2 =>
      have := D.map_add ⟨x, hx⟩ ⟨y, hy⟩
      rw [h1, h2, add_zero] at this
      exact this
    | mul x y hx hy h1 h2 =>
      have := D.leibniz ⟨x, hx⟩ ⟨y, hy⟩
      rw [h1, h2, smul_zero, smul_zero, add_zero] at this
      exact this
  refine ⟨⟨fun a b => ?_⟩⟩
  have h := KaehlerDifferential.span_range_derivation R (Algebra.adjoin R {ζ})
  have h0 : (⊤ : Submodule (Algebra.adjoin R {ζ}) Ω[Algebra.adjoin R {ζ}⁄R]) ≤ ⊥ := by
    rw [← h, Submodule.span_le]
    rintro _ ⟨x, rfl⟩
    exact hD x.1 x.2
  rw [(Submodule.mem_bot _).1 (h0 (Submodule.mem_top (x := a))), (Submodule.mem_bot _).1 (h0 (Submodule.mem_top (x := b)))]

/- English proof (translation)
Unfold `eO`. Rewrite using `[hm, Module.length_eq_one_iff]`. Conclude with `isSimpleModule_iff_quot_maximal.2 ⟨_, IsLocalRing.maximalIdeal.isMaximal _, ⟨LinearEquiv.refl _ _⟩⟩`.
-/
private theorem eO_eq_one (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O] [IsLocalRing O]
    (hm : Ideal.span {(l : O)} = IsLocalRing.maximalIdeal O) : eO l O = 1 := by
  unfold eO
  rw [hm, Module.length_eq_one_iff]
  exact isSimpleModule_iff_quot_maximal.2 ⟨_, IsLocalRing.maximalIdeal.isMaximal _, ⟨LinearEquiv.refl _ _⟩⟩

/- English proof (translation)
Take `⟨ζ, hζ⟩` from `HasEnoughRootsOfUnity.exists_primitiveRoot (PadicAlgCl l) n`. Establish `hζi : IsIntegral ℤ_[l] ζ` using `(hζ.isIntegral (NeZero.pos n)).tower_top`. Establish `hu : IsUnit (n : ℤ_[l])`. Rewrite using `[PadicInt.isUnit_iff]`. Conclude with `PadicInt.norm_natCast_eq_one_iff.2 ((Nat.Prime.coprime_iff_not_dvd hl.out).2 hn)`.

Set `A : Subalgebra ℤ_[l] (PadicAlgCl l)` to `Algebra.adjoin ℤ_[l] {ζ}`. Use `haveI hfin : Module.Finite ℤ_[l] A := Module.Finite.iff_fg.2 hζi.fg_adjoin_singleton`. Use `haveI : Algebra.FormallyUnramified ℤ_[l] A := unram_adjoin (NeZero.ne n) hu hζ.pow_eq_one`. Take `⟨c, hc⟩` from `exists_coef_ge l A`. Set `f : A →ₐ[ℤ_[l]] c.O` to `Subalgebra.inclusion hc`.

Establish `hf : Function.Injective f` using `Subalgebra.inclusion_injective hc`. Use `haveI hloc : IsLocalRing A := by`. Use `letI : Algebra A c.O := f.toAlgebra`. Use `haveI : IsScalarTower ℤ_[l] A c.O := IsScalarTower.of_algebraMap_eq fun x => (f.commutes x).symm`. Use `haveI : Algebra.IsIntegral A c.O := Algebra.IsIntegral.tower_top ℤ_[l]`.

Use `haveI : FaithfulSMul A c.O := (faithfulSMul_iff_algebraMap_injective _ _).2 hf`. Use `haveI : IsLocalHom (algebraMap A c.O) := inferInstance`. Conclude with `(algebraMap A c.O).domain_isLocalRing`. Establish `hinj : Function.Injective (algebraMap ℤ_[l] A)`. Introduce `a b hab`.

Establish `h` using `congrArg (fun x : A => (x : PadicAlgCl l)) hab`. Simplify using `only [Subalgebra.coe_algebraMap, IsScalarTower.algebraMap_apply ℤ_[l] ℚ_[l] (PadicAlgCl l)] at h`. Conclude with `IsFractionRing.injective ℤ_[l] ℚ_[l] ((algebraMap ℚ_[l] (PadicAlgCl l)).injective h)`. Use `haveI : FaithfulSMul ℤ_[l] A := (faithfulSMul_iff_algebraMap_injective _ _).2 hinj`. Use `haveI : IsLocalHom (algebraMap ℤ_[l] A) := inferInstance`.

Establish `hm : Ideal.span {(l : A)} = IsLocalRing.maximalIdeal A`. Rewrite using `[← Algebra.FormallyUnramified.map_maximalIdeal (R := ℤ_[l]), PadicInt.maximalIdeal_eq_span_p, Ideal.map_span, Set.image_singleton, map_natCast]`. Establish `hnf : ¬ IsField A` using `fun hf => IsDiscreteValuationRing.not_isField ℤ_[l] ((Algebra.IsIntegral.isField_iff_isField hinj).2 hf)`. Use `haveI : IsNoetherianRing A := IsNoetherianRing.of_finite ℤ_[l] A`. Establish `hp : (IsLocalRing.maximalIdeal A).IsPrincipal` using `hm ▸ inferInstance`.

Establish `hd : IsDiscreteValuationRing A` using `((IsDiscreteValuationRing.TFAE _ hnf).out 0 4).mpr hp`. Use `⟨⟨A, hd, hfin⟩, ?_, ?_⟩` and prove the remaining obligations. Conclude with `eO_eq_one l A hm`. Use `⟨⟨⟨ζ, Algebra.self_mem_adjoin_singleton _ ζ⟩, ?_⟩, rootsOfUnity.isCyclic _ _⟩` and prove the remaining obligations. Conclude with `IsPrimitiveRoot.of_map_of_injective (f := A.val) hζ Subtype.val_injective`.
-/
private theorem exists_unram (l : ℕ) [hl : Fact l.Prime] (n : ℕ) [NeZero n] (hn : ¬ l ∣ n) :
    ∃ c : Coef l, eO l c.O = 1 ∧ HasEnoughRootsOfUnity c.O n := by
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot (PadicAlgCl l) n
  have hζi : IsIntegral ℤ_[l] ζ := (hζ.isIntegral (NeZero.pos n)).tower_top
  have hu : IsUnit (n : ℤ_[l]) := by
    rw [PadicInt.isUnit_iff]
    exact PadicInt.norm_natCast_eq_one_iff.2 ((Nat.Prime.coprime_iff_not_dvd hl.out).2 hn)
  let A : Subalgebra ℤ_[l] (PadicAlgCl l) := Algebra.adjoin ℤ_[l] {ζ}
  haveI hfin : Module.Finite ℤ_[l] A := Module.Finite.iff_fg.2 hζi.fg_adjoin_singleton
  haveI : Algebra.FormallyUnramified ℤ_[l] A := unram_adjoin (NeZero.ne n) hu hζ.pow_eq_one
  obtain ⟨c, hc⟩ := exists_coef_ge l A
  let f : A →ₐ[ℤ_[l]] c.O := Subalgebra.inclusion hc
  have hf : Function.Injective f := Subalgebra.inclusion_injective hc
  haveI hloc : IsLocalRing A := by
    letI : Algebra A c.O := f.toAlgebra
    haveI : IsScalarTower ℤ_[l] A c.O := IsScalarTower.of_algebraMap_eq fun x => (f.commutes x).symm
    haveI : Algebra.IsIntegral A c.O := Algebra.IsIntegral.tower_top ℤ_[l]
    haveI : FaithfulSMul A c.O := (faithfulSMul_iff_algebraMap_injective _ _).2 hf
    haveI : IsLocalHom (algebraMap A c.O) := inferInstance
    exact (algebraMap A c.O).domain_isLocalRing
  have hinj : Function.Injective (algebraMap ℤ_[l] A) := by
    intro a b hab
    have h := congrArg (fun x : A => (x : PadicAlgCl l)) hab
    simp only [Subalgebra.coe_algebraMap, IsScalarTower.algebraMap_apply ℤ_[l] ℚ_[l] (PadicAlgCl l)] at h
    exact IsFractionRing.injective ℤ_[l] ℚ_[l] ((algebraMap ℚ_[l] (PadicAlgCl l)).injective h)
  haveI : FaithfulSMul ℤ_[l] A := (faithfulSMul_iff_algebraMap_injective _ _).2 hinj
  haveI : IsLocalHom (algebraMap ℤ_[l] A) := inferInstance
  have hm : Ideal.span {(l : A)} = IsLocalRing.maximalIdeal A := by
    rw [← Algebra.FormallyUnramified.map_maximalIdeal (R := ℤ_[l]), PadicInt.maximalIdeal_eq_span_p,
      Ideal.map_span, Set.image_singleton, map_natCast]
  have hnf : ¬ IsField A := fun hf =>
    IsDiscreteValuationRing.not_isField ℤ_[l] ((Algebra.IsIntegral.isField_iff_isField hinj).2 hf)
  haveI : IsNoetherianRing A := IsNoetherianRing.of_finite ℤ_[l] A
  have hp : (IsLocalRing.maximalIdeal A).IsPrincipal := hm ▸ inferInstance
  have hd : IsDiscreteValuationRing A := ((IsDiscreteValuationRing.TFAE _ hnf).out 0 4).mpr hp
  refine ⟨⟨A, hd, hfin⟩, ?_, ?_⟩
  · exact eO_eq_one l A hm
  · refine ⟨⟨⟨ζ, Algebra.self_mem_adjoin_singleton _ ζ⟩, ?_⟩, rootsOfUnity.isCyclic _ _⟩
    exact IsPrimitiveRoot.of_map_of_injective (f := A.val) hζ Subtype.val_injective

/- English proof (translation)
Introduce `l _`. Use `⟨fun c c' => ?_, fun n _ hn => exists_unram l n hn, fun c x hx => ?_, fun c x hx ⟨a, b, hb, hab⟩ => ?_⟩` and prove the remaining obligations. Use `haveI := Subalgebra.finite_sup c.O c'.O`. Take `⟨d, hd⟩` from `exists_coef_ge l (c.O ⊔ c'.O)`. Conclude with `⟨d, le_sup_left.trans hd, le_sup_right.trans hd⟩`.

Use `haveI : Module.Finite ℤ_[l] (Algebra.adjoin ℤ_[l] {x}) := Module.Finite.iff_fg.2 hx.fg_adjoin_singleton haveI := Subalgebra.finite_sup c.O (Algebra.adjoin ℤ_[l] {x})`. Take `⟨d, hd⟩` from `exists_coef_ge l (c.O ⊔ Algebra.adjoin ℤ_[l] {x})`. Conclude with `⟨d, le_sup_left.trans hd, (le_sup_right.trans hd) (Algebra.self_mem_adjoin_singleton _ x)⟩`. Set `g : FractionRing c.O →ₐ[c.O] PadicAlgCl l` to `IsFractionRing.liftAlgHom (g := Algebra.ofId c.O (PadicAlgCl l)) Subtype.val_injective`. Establish `hg : g (algebraMap c.O _ a / algebraMap c.O _ b) = x`.

Rewrite using `[map_div₀, g.commutes, g.commutes]`. Conclude with `(div_eq_iff hb).2 hab.symm`. Establish `hi : IsIntegral c.O (algebraMap c.O (FractionRing c.O) a / algebraMap c.O _ b)`. Rewrite using `[← isIntegral_algHom_iff g g.injective, hg]`. Conclude with `hx.tower_top`.

Take `⟨y, hy⟩` from `IsIntegrallyClosed.algebraMap_eq_of_integral hi`. Rewrite using `[← hg, ← hy, g.commutes]`. Conclude with `y.2`.
-/
theorem UpperTheory.V.HV.coefSup :
    ∀ (l : ℕ) [Fact l.Prime], (∀ c c' : Coef l, ∃ c'' : Coef l, c.O ≤ c''.O ∧ c'.O ≤ c''.O) ∧
      (∀ (n : ℕ) [NeZero n], ¬ l ∣ n → ∃ c : Coef l, eO l c.O = 1 ∧ HasEnoughRootsOfUnity c.O n) ∧
      (∀ (c : Coef l) (x : PadicAlgCl l), IsIntegral ℤ_[l] x → ∃ c' : Coef l, c.O ≤ c'.O ∧ x ∈ c'.O) ∧
      ∀ (c : Coef l) (x : PadicAlgCl l), IsIntegral ℤ_[l] x → (∃ a b : c.O, (b : PadicAlgCl l) ≠ 0 ∧ x * b = a) → x ∈ c.O := by
  intro l _
  refine ⟨fun c c' => ?_, fun n _ hn => exists_unram l n hn, fun c x hx => ?_, fun c x hx ⟨a, b, hb, hab⟩ => ?_⟩
  · haveI := Subalgebra.finite_sup c.O c'.O
    obtain ⟨d, hd⟩ := exists_coef_ge l (c.O ⊔ c'.O)
    exact ⟨d, le_sup_left.trans hd, le_sup_right.trans hd⟩
  · haveI : Module.Finite ℤ_[l] (Algebra.adjoin ℤ_[l] {x}) := Module.Finite.iff_fg.2 hx.fg_adjoin_singleton
    haveI := Subalgebra.finite_sup c.O (Algebra.adjoin ℤ_[l] {x})
    obtain ⟨d, hd⟩ := exists_coef_ge l (c.O ⊔ Algebra.adjoin ℤ_[l] {x})
    exact ⟨d, le_sup_left.trans hd, (le_sup_right.trans hd) (Algebra.self_mem_adjoin_singleton _ x)⟩
  · let g : FractionRing c.O →ₐ[c.O] PadicAlgCl l :=
      IsFractionRing.liftAlgHom (g := Algebra.ofId c.O (PadicAlgCl l)) Subtype.val_injective
    have hg : g (algebraMap c.O _ a / algebraMap c.O _ b) = x := by
      rw [map_div₀, g.commutes, g.commutes]
      exact (div_eq_iff hb).2 hab.symm
    have hi : IsIntegral c.O (algebraMap c.O (FractionRing c.O) a / algebraMap c.O _ b) := by
      rw [← isIntegral_algHom_iff g g.injective, hg]
      exact hx.tower_top
    obtain ⟨y, hy⟩ := IsIntegrallyClosed.algebraMap_eq_of_integral hi
    rw [← hg, ← hy, g.commutes]
    exact y.2

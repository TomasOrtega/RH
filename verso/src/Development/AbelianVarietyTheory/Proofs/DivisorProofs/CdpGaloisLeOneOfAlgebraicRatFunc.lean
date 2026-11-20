import Mathlib
import GroundTheory.ProfiniteCohomology.GaloisCohomology.Kummer
import GroundTheory.ProfiniteCohomology.GaloisCohomology.Brauer
import GroundTheory.ProfiniteCohomology.RestrictedRamification.DimensionSylow
import GroundTheory.ProfiniteCohomology.LocalClassFormationAlt
import GroundTheory.ProfiniteCohomology.LocalClassFormation.FiniteVanishing.KummerOpen
import GroundTheory.ProfiniteCohomology.LocalClassFormation.FiniteVanishing.Vanishing
import GroundTheory.ProfiniteCohomology.LocalClassFormation.OrderScalars
import GroundTheory.ProfiniteCohomology.LocalEulerCharacteristic.Scalars
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.COneH2UnitsSubsingleton
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TsenAlgebraicExtensionRatFunc
set_option maxSynthPendingDepth 1

open CategoryTheory IntermediateField GroundTheory.ProfCoh

namespace GlobalTheory.TsenCD

/- English proof (translation)
It suffices to establish `h : ∀ x : cohomology (galUnits.{0} E Ω) 2, x = 0 from ⟨fun x y => (h x).trans (h y).symm⟩`. Introduce `x`. Take `⟨F, z, rfl⟩` from `exists_unitsInflation_eq 2 x`. Establish `hC` using `GlobalTheory.tsen_algebraic_extension_ratFunc k E`. Establish `h1 : Subsingleton (groupCohomology (Rep.ofAlgebraAutOnUnits E F.toIntermediateField) 2)` using `GlobalTheory.c_one_h2_units_subsingleton E F.toIntermediateField hC`.

Establish `h2 : Subsingleton (groupCohomology (galUnitsZ E F.toIntermediateField) 2)` using `h1`. Establish `h3 : Subsingleton (groupCohomology (galUnits.{0} E F.toIntermediateField) 2)` using `(h2GalUnitsAddEquiv E F.toIntermediateField).injective.subsingleton`. Rewrite using `[Subsingleton.elim z 0, map_zero]`.
-/
theorem subsingleton_brauer (k E Ω : Type) [Field k] [IsAlgClosed k] [Field E] [Algebra (RatFunc k) E]
    [Algebra.IsAlgebraic (RatFunc k) E] [Field Ω] [Algebra E Ω] [IsGalois E Ω] :
    Subsingleton (cohomology (galUnits.{0} E Ω) 2) := by
  suffices h : ∀ x : cohomology (galUnits.{0} E Ω) 2, x = 0 from ⟨fun x y => (h x).trans (h y).symm⟩
  intro x
  obtain ⟨F, z, rfl⟩ := exists_unitsInflation_eq 2 x
  have hC := GlobalTheory.tsen_algebraic_extension_ratFunc k E
  have h1 : Subsingleton (groupCohomology (Rep.ofAlgebraAutOnUnits E F.toIntermediateField) 2) :=
    GlobalTheory.c_one_h2_units_subsingleton E F.toIntermediateField hC
  have h2 : Subsingleton (groupCohomology (galUnitsZ E F.toIntermediateField) 2) := h1
  have h3 : Subsingleton (groupCohomology (galUnits.{0} E F.toIntermediateField) 2) :=
    (h2GalUnitsAddEquiv E F.toIntermediateField).injective.subsingleton
  rw [Subsingleton.elim z 0, map_zero]

/- English proof (translation)
Take `⟨e⟩` from `nonempty_zmod_addEquiv_rootsOfUnity K Ω hp hpK`. Establish `h` using `cdp_le_of_forall_openSubgroup hp (galRootsOfUnity.{0} K Ω p) e 1 (fun U => by`. Set `E` to `fixedField (U : Subgroup (Ω ≃ₐ[K] Ω))`. Use `letI : Algebra (RatFunc k) E := ((algebraMap K E).comp (algebraMap (RatFunc k) K)).toAlgebra`. Use `haveI : IsScalarTower (RatFunc k) K E := IsScalarTower.of_algebraMap_eq' rfl`.

Use `haveI : Algebra.IsAlgebraic K E := inferInstance`. Use `haveI : Algebra.IsAlgebraic (RatFunc k) E := Algebra.IsAlgebraic.trans (RatFunc k) K E`. Use `haveI : IsGalois E Ω := IsGalois.tower_top_of_isGalois K E Ω`. Establish `hB : Subsingleton (cohomology (Rep.res (U : Subgroup (Ω ≃ₐ[K] Ω)).subtype (galUnits.{0} K Ω)) 2)`. Use `subsingleton_brauer k E Ω` as an intermediate fact.

Conclude with `(openCohomologyIso U 2).toLinearEquiv.toEquiv.subsingleton`. Establish `h1 : Subsingleton (cohomology (Rep.res (U : Subgroup (Ω ≃ₐ[K] Ω)).subtype (galUnits.{0} K Ω)) 1)` using `ModuleCat.subsingleton_of_isZero (isZero_H1_open K Ω U)`. Establish `hS` using `kummerSequenceRes_shortExact (Ksep := Ω) p (U : Subgroup (Ω ≃ₐ[K] Ω)) hpK`. Use `haveI : Subsingleton (cohomology (kummerSequenceRes (K := K) (Ksep := Ω) p (U : Subgroup (Ω ≃ₐ[K] Ω))).X₂ (1 + 1)) := hB`. Conclude with `(cohomologyMap_f_injective_of_subsingleton hS 1 h1).subsingleton)`.

Conclude with `h` after adjusting the coercions.
-/
theorem cdp_le_one_of_ne_char (k K Ω : Type) [Field k] [IsAlgClosed k] [Field K]
    [Algebra (RatFunc k) K] [Algebra.IsAlgebraic (RatFunc k) K] [Field Ω] [Algebra K Ω]
    [IsSepClosure K Ω] (p : ℕ) (hp : p.Prime) (hpK : (p : K) ≠ 0) :
    cdp p (Ω ≃ₐ[K] Ω) ≤ 1 := by
  obtain ⟨e⟩ := nonempty_zmod_addEquiv_rootsOfUnity K Ω hp hpK
  have h := cdp_le_of_forall_openSubgroup hp (galRootsOfUnity.{0} K Ω p) e 1 (fun U => by
    let E := fixedField (U : Subgroup (Ω ≃ₐ[K] Ω))
    letI : Algebra (RatFunc k) E := ((algebraMap K E).comp (algebraMap (RatFunc k) K)).toAlgebra
    haveI : IsScalarTower (RatFunc k) K E := IsScalarTower.of_algebraMap_eq' rfl
    haveI : Algebra.IsAlgebraic K E := inferInstance
    haveI : Algebra.IsAlgebraic (RatFunc k) E := Algebra.IsAlgebraic.trans (RatFunc k) K E
    haveI : IsGalois E Ω := IsGalois.tower_top_of_isGalois K E Ω
    have hB : Subsingleton (cohomology (Rep.res (U : Subgroup (Ω ≃ₐ[K] Ω)).subtype
        (galUnits.{0} K Ω)) 2) := by
      have := subsingleton_brauer k E Ω
      exact (openCohomologyIso U 2).toLinearEquiv.toEquiv.subsingleton
    have h1 : Subsingleton (cohomology (Rep.res (U : Subgroup (Ω ≃ₐ[K] Ω)).subtype
        (galUnits.{0} K Ω)) 1) := ModuleCat.subsingleton_of_isZero (isZero_H1_open K Ω U)
    have hS := kummerSequenceRes_shortExact (Ksep := Ω) p (U : Subgroup (Ω ≃ₐ[K] Ω)) hpK
    haveI : Subsingleton (cohomology (kummerSequenceRes (K := K) (Ksep := Ω) p
        (U : Subgroup (Ω ≃ₐ[K] Ω))).X₂ (1 + 1)) := hB
    exact (cohomologyMap_f_injective_of_subsingleton hS 1 h1).subsingleton)
  exact_mod_cast h

section ArtinSchreier

attribute [local instance 2000] Rep.hV2

open Polynomial

/- English proof (translation)
Assume the negation of the conclusion as `hne`. Use `push_neg at hne`. Use `set f := ZMod.castHom (dvd_refl p) Ω`. Use `set P : Polynomial Ω := X ^ p - X`. Establish `hP : P ≠ 0` using `FiniteField.X_pow_card_sub_X_ne_zero Ω hp.out.one_lt`.

Establish `hroot : ∀ z : Ω, z ^ p - z = 0 → z ∈ P.roots.toFinset` using `fun z hz => by`. Rewrite using `[Multiset.mem_toFinset, mem_roots hP]`. Simplify using `[P, hz]`. Establish `hT : insert y (Finset.univ.image f) ⊆ P.roots.toFinset`. Introduce `z hz`.

Break down `Finset.mem_insert.1 hz with rfl | hz` into its components or cases. Conclude with `hroot _ hy`. Take `⟨a, -, rfl⟩` from `Finset.mem_image.1 hz`. Apply `hroot` to reduce the goal to its premises. Rewrite using `[← map_pow, ZMod.pow_card, sub_self]`.

Establish `hy' : y ∉ Finset.univ.image f` using `fun h => by`. Take `⟨a, -, ha⟩` from `Finset.mem_image.1 h`. Conclude with `hne a ha`. Establish `hcard : (insert y (Finset.univ.image f)).card = p + 1`. Rewrite using `[Finset.card_insert_of_notMem hy', Finset.card_image_of_injective _ f.injective, Finset.card_univ, ZMod.card]`.

Establish `h1` using `Finset.card_le_card hT`. Establish `h2 : P.roots.toFinset.card ≤ p` using `(Multiset.toFinset_card_le _).trans ((card_roots' P).trans (FiniteField.X_pow_card_sub_X_natDegree_eq Ω hp.out.one_lt).le)`. Use linear arithmetic over natural numbers and integers.
-/
theorem exists_zmod_cast_eq_of_pow_sub_self {p : ℕ} [hp : Fact p.Prime] {Ω : Type} [Field Ω] [CharP Ω p]
    (y : Ω) (hy : y ^ p - y = 0) : ∃ a : ZMod p, ZMod.castHom (dvd_refl p) Ω a = y := by
  classical
  by_contra hne
  push_neg at hne
  set f := ZMod.castHom (dvd_refl p) Ω
  set P : Polynomial Ω := X ^ p - X
  have hP : P ≠ 0 := FiniteField.X_pow_card_sub_X_ne_zero Ω hp.out.one_lt
  have hroot : ∀ z : Ω, z ^ p - z = 0 → z ∈ P.roots.toFinset := fun z hz => by
    rw [Multiset.mem_toFinset, mem_roots hP]
    simp [P, hz]
  have hT : insert y (Finset.univ.image f) ⊆ P.roots.toFinset := by
    intro z hz
    rcases Finset.mem_insert.1 hz with rfl | hz
    · exact hroot _ hy
    · obtain ⟨a, -, rfl⟩ := Finset.mem_image.1 hz
      apply hroot
      rw [← map_pow, ZMod.pow_card, sub_self]
  have hy' : y ∉ Finset.univ.image f := fun h => by
    obtain ⟨a, -, ha⟩ := Finset.mem_image.1 h
    exact hne a ha
  have hcard : (insert y (Finset.univ.image f)).card = p + 1 := by
    rw [Finset.card_insert_of_notMem hy', Finset.card_image_of_injective _ f.injective,
      Finset.card_univ, ZMod.card]
  have h1 := Finset.card_le_card hT
  have h2 : P.roots.toFinset.card ≤ p :=
    (Multiset.toFinset_card_le _).trans ((card_roots' P).trans
      (FiniteField.X_pow_card_sub_X_natDegree_eq Ω hp.out.one_lt).le)
  omega

/- English proof (translation)
Establish `hd : derivative (X ^ p - X - C a : Polynomial Ω) = -1`. Simplify using `[derivative_X_pow, CharP.cast_eq_zero]`. Establish `hsep : (X ^ p - X - C a : Polynomial Ω).Separable`. Rewrite using `[separable_def, hd]`. Conclude with `isCoprime_one_right.neg_right`.

Establish `hdeg : (X ^ p - X - C a : Polynomial Ω).degree ≠ 0` using `fun h => by`. Establish `h'` using `congrArg derivative (eq_C_of_degree_eq_zero h)`. Rewrite `h'` using `[hd, derivative_C]`. Conclude with `one_ne_zero (neg_eq_zero.1 h')`. Take `⟨x, hx⟩` from `IsSepClosed.exists_root _ hdeg hsep`.

Use `⟨x, ?_⟩` and prove the remaining obligations. Use `hx.eq_zero` as an intermediate fact. Simplify using `only [eval_sub, eval_pow, eval_X, eval_C] at this`. Conclude with `sub_eq_zero.1 this`.
-/
theorem exists_pow_sub_self_eq {p : ℕ} [hp : Fact p.Prime] {Ω : Type} [Field Ω] [CharP Ω p]
    [IsSepClosed Ω] (a : Ω) : ∃ x : Ω, x ^ p - x = a := by
  have hd : derivative (X ^ p - X - C a : Polynomial Ω) = -1 := by
    simp [derivative_X_pow, CharP.cast_eq_zero]
  have hsep : (X ^ p - X - C a : Polynomial Ω).Separable := by
    rw [separable_def, hd]
    exact isCoprime_one_right.neg_right
  have hdeg : (X ^ p - X - C a : Polynomial Ω).degree ≠ 0 := fun h => by
    have h' := congrArg derivative (eq_C_of_degree_eq_zero h)
    rw [hd, derivative_C] at h'
    exact one_ne_zero (neg_eq_zero.1 h')
  obtain ⟨x, hx⟩ := IsSepClosed.exists_root _ hdeg hsep
  refine ⟨x, ?_⟩
  have := hx.eq_zero
  simp only [eval_sub, eval_pow, eval_X, eval_C] at this
  exact sub_eq_zero.1 this

end ArtinSchreier

section Sequence

attribute [local instance 2000] Rep.hV2

variable (E Ω : Type) [Field E] [Field Ω] [Algebra E Ω] [IsGalois E Ω] (p : ℕ) [Fact p.Prime] [CharP Ω p]

noncomputable def primeFieldToGalAdd :
    Rep.trivial (ULift.{0} ℤ) (Ω ≃ₐ[E] Ω) (ULift.{0} (ZMod p)) ⟶ galAddInt.{0} E Ω :=
  Rep.ofHom ⟨uliftIntLinearMap ((ZMod.castHom (dvd_refl p) Ω).toAddMonoidHom.comp
      (AddEquiv.ulift : ULift.{0} (ZMod p) ≃+ ZMod p).toAddMonoidHom), fun σ =>
    LinearMap.ext fun x => by
      change ZMod.castHom (dvd_refl p) Ω x.down = σ (ZMod.castHom (dvd_refl p) Ω x.down)
      exact (congrArg (fun φ : ZMod p →+* Ω => φ x.down)
        (RingHom.ext_zmod ((σ : Ω →+* Ω).comp (ZMod.castHom (dvd_refl p) Ω))
          (ZMod.castHom (dvd_refl p) Ω))).symm⟩

noncomputable def artinSchreierMap : galAddInt.{0} E Ω ⟶ galAddInt.{0} E Ω :=
  Rep.ofHom ⟨uliftIntLinearMap ((frobenius Ω p).toAddMonoidHom - AddMonoidHom.id Ω), fun σ =>
    LinearMap.ext fun x => by
      change σ x ^ p - σ x = σ (x ^ p - x)
      rw [map_sub, map_pow]⟩

noncomputable def artinSchreierSequence : ShortComplex (Rep (ULift.{0} ℤ) (Ω ≃ₐ[E] Ω)) :=
  ShortComplex.mk (primeFieldToGalAdd E Ω p) (artinSchreierMap E Ω p) (by
    ext x
    change (ZMod.castHom (dvd_refl p) Ω x.down) ^ p - ZMod.castHom (dvd_refl p) Ω x.down = 0
    rw [← map_pow, ZMod.pow_card, sub_self])

/- English proof (translation)
The claim follows from `shortComplex_exact_of_forall_exists _ fun y hy => by obtain ⟨a, ha⟩ := exists_zmod_cast_eq_of_pow_sub_self (p := p) (Ω := Ω) y hy exact ⟨ULift.up a, ha⟩ mono_f := (Rep.mono_iff_injective _).2 fun x y h => ULift.ext _ _ ((ZMod.castHom (dvd_refl p) Ω).injective h) epi_g := (Rep.epi …`.
-/
theorem artinSchreierSequence_shortExact [IsSepClosed Ω] :
    (artinSchreierSequence E Ω p).ShortExact where
  exact := shortComplex_exact_of_forall_exists _ fun y hy => by
    obtain ⟨a, ha⟩ := exists_zmod_cast_eq_of_pow_sub_self (p := p) (Ω := Ω) y hy
    exact ⟨ULift.up a, ha⟩
  mono_f := (Rep.mono_iff_injective _).2 fun x y h =>
    ULift.ext _ _ ((ZMod.castHom (dvd_refl p) Ω).injective h)
  epi_g := (Rep.epi_iff_surjective _).2 fun a => by
    obtain ⟨x, hx⟩ := exists_pow_sub_self_eq (p := p) (Ω := Ω) a
    exact ⟨x, hx⟩

instance isDiscreteRep_artinSchreierSequence_X₁ :
    IsDiscreteRep (artinSchreierSequence E Ω p).X₁ :=
  inferInstanceAs (IsDiscreteRep (Rep.trivial (ULift.{0} ℤ) (Ω ≃ₐ[E] Ω) (ULift.{0} (ZMod p))))

instance isDiscreteRep_artinSchreierSequence_X₂ :
    IsDiscreteRep (artinSchreierSequence E Ω p).X₂ :=
  inferInstanceAs (IsDiscreteRep (galAddInt.{0} E Ω))

instance isDiscreteRep_artinSchreierSequence_X₃ :
    IsDiscreteRep (artinSchreierSequence E Ω p).X₃ :=
  inferInstanceAs (IsDiscreteRep (galAddInt.{0} E Ω))

omit [Fact p.Prime] [CharP Ω p] in

/- English proof (translation)
Use `subsingleton_cohomology_galAdd (K := E) (L := Ω) hn` as an intermediate fact. Conclude with `(cohomologyAddEquivOfEquiv (A := galAddInt.{0} E Ω) (A' := galAdd E Ω) (AddEquiv.refl Ω) (fun _ _ => rfl) n).injective.subsingleton`.
-/
theorem subsingleton_cohomology_galAddInt {n : ℕ} (hn : n ≠ 0) :
    Subsingleton (cohomology (galAddInt.{0} E Ω) n) := by
  have := subsingleton_cohomology_galAdd (K := E) (L := Ω) hn
  exact (cohomologyAddEquivOfEquiv (A := galAddInt.{0} E Ω) (A' := galAdd E Ω) (AddEquiv.refl Ω)
    (fun _ _ => rfl) n).injective.subsingleton

/- English proof (translation)
Establish `hS` using `artinSchreierSequence_shortExact E Ω p`. Establish `h1 : Subsingleton (cohomology (artinSchreierSequence E Ω p).X₃ 1)` using `subsingleton_cohomology_galAddInt E Ω one_ne_zero`. Use `haveI : Subsingleton (cohomology (artinSchreierSequence E Ω p).X₂ (1 + 1)) := subsingleton_cohomology_galAddInt E Ω (n := 2) two_ne_zero`. Conclude with `(cohomologyMap_f_injective_of_subsingleton hS 1 h1).subsingleton`.
-/
theorem subsingleton_cohomology_two_trivial_zmod [IsSepClosed Ω] :
    Subsingleton (cohomology (Rep.trivial (ULift.{0} ℤ) (Ω ≃ₐ[E] Ω) (ULift.{0} (ZMod p))) 2) := by
  have hS := artinSchreierSequence_shortExact E Ω p
  have h1 : Subsingleton (cohomology (artinSchreierSequence E Ω p).X₃ 1) :=
    subsingleton_cohomology_galAddInt E Ω one_ne_zero
  haveI : Subsingleton (cohomology (artinSchreierSequence E Ω p).X₂ (1 + 1)) :=
    subsingleton_cohomology_galAddInt E Ω (n := 2) two_ne_zero
  exact (cohomologyMap_f_injective_of_subsingleton hS 1 h1).subsingleton

end Sequence

/- English proof (translation)
Use `haveI : Fact p.Prime := ⟨hp⟩`. Use `haveI : CharP K p := (CharP.charP_iff_prime_eq_zero hp).2 hpK`. Use `haveI : CharP Ω p := charP_of_injective_algebraMap (algebraMap K Ω).injective p`. Use `haveI : IsSepClosed Ω := IsSepClosure.sep_closed K`. Establish `h` using `cdp_le_of_forall_openSubgroup hp (Rep.trivial (ULift.{0} ℤ) (Ω ≃ₐ[K] Ω) (ULift.{0} (ZMod p))) AddEquiv.ulift.symm 1 (fun U => by`.

Set `E` to `fixedField (U : Subgroup (Ω ≃ₐ[K] Ω))`. Use `haveI : IsGalois E Ω := IsGalois.tower_top_of_isGalois K E Ω`. Establish `h2` using `subsingleton_cohomology_two_trivial_zmod E Ω p`. Use `haveI : IsDiscreteRep (Rep.res (U : Subgroup (Ω ≃ₐ[K] Ω)).subtype (Rep.trivial (ULift.{0} ℤ) (Ω ≃ₐ[K] Ω) (ULift.{0} (ZMod p)))) := isDiscreteRep_res_subtype _ _`. Set `f : Rep.res (galFixedFieldEquivOpen U).toMonoidHom (Rep.res (U : Subgroup (Ω ≃ₐ[K] Ω)).subtype (Rep.trivial (ULift.{0} ℤ) (Ω ≃ₐ[K] Ω) (ULift.{0} (ZMod p)))) ⟶ Rep.trivial (ULift.{0} ℤ) (Ω ≃ₐ[E] Ω) (ULift.{0} (ZMod p))` to `Rep.ofHom ⟨LinearMap.id, fun σ => LinearMap.ext fun x => rfl⟩`.

Use `haveI := isIso_cohomologyMapAlong_of_mulEquiv (galFixedFieldEquivOpen U) (continuous_galFixedFieldEquivOpen U) (continuous_galFixedFieldEquivOpen_symm U) f Function.bijective_id 2`. Conclude with `(asIso (cohomologyMapAlong (galFixedFieldEquivOpen U).toMonoidHom (continuous_galFixedFieldEquivOpen U) f 2)).toLinearEquiv.toEquiv.subsingleton)`. Conclude with `h` after adjusting the coercions.
-/
theorem cdp_le_one_of_char_eq (K Ω : Type) [Field K] [Field Ω] [Algebra K Ω] [IsSepClosure K Ω]
    (p : ℕ) (hp : p.Prime) (hpK : (p : K) = 0) : cdp p (Ω ≃ₐ[K] Ω) ≤ 1 := by
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : CharP K p := (CharP.charP_iff_prime_eq_zero hp).2 hpK
  haveI : CharP Ω p := charP_of_injective_algebraMap (algebraMap K Ω).injective p
  haveI : IsSepClosed Ω := IsSepClosure.sep_closed K
  have h := cdp_le_of_forall_openSubgroup hp
    (Rep.trivial (ULift.{0} ℤ) (Ω ≃ₐ[K] Ω) (ULift.{0} (ZMod p))) AddEquiv.ulift.symm 1 (fun U => by
      let E := fixedField (U : Subgroup (Ω ≃ₐ[K] Ω))
      haveI : IsGalois E Ω := IsGalois.tower_top_of_isGalois K E Ω
      have h2 := subsingleton_cohomology_two_trivial_zmod E Ω p
      haveI : IsDiscreteRep (Rep.res (U : Subgroup (Ω ≃ₐ[K] Ω)).subtype
          (Rep.trivial (ULift.{0} ℤ) (Ω ≃ₐ[K] Ω) (ULift.{0} (ZMod p)))) :=
        isDiscreteRep_res_subtype _ _
      let f : Rep.res (galFixedFieldEquivOpen U).toMonoidHom
          (Rep.res (U : Subgroup (Ω ≃ₐ[K] Ω)).subtype
            (Rep.trivial (ULift.{0} ℤ) (Ω ≃ₐ[K] Ω) (ULift.{0} (ZMod p)))) ⟶
          Rep.trivial (ULift.{0} ℤ) (Ω ≃ₐ[E] Ω) (ULift.{0} (ZMod p)) :=
        Rep.ofHom ⟨LinearMap.id, fun σ => LinearMap.ext fun x => rfl⟩
      haveI := isIso_cohomologyMapAlong_of_mulEquiv (galFixedFieldEquivOpen U)
        (continuous_galFixedFieldEquivOpen U) (continuous_galFixedFieldEquivOpen_symm U) f
        Function.bijective_id 2
      exact (asIso (cohomologyMapAlong (galFixedFieldEquivOpen U).toMonoidHom
        (continuous_galFixedFieldEquivOpen U) f 2)).toLinearEquiv.toEquiv.subsingleton)
  exact_mod_cast h

/- English proof (translation)
Introduce `k K Ω _ _ _ _ _ _ _ _ p hp`. Distinguish the cases in `hpK : (p : K) = 0`. Conclude with `cdp_le_one_of_char_eq K Ω p hp hpK`. Conclude with `cdp_le_one_of_ne_char k K Ω p hp hpK`.
-/
theorem cdp_galois_le_one_of_algebraic_ratFunc : ∀ (k K Ω : Type) [Field k] [IsAlgClosed k] [Field K]
    [Algebra (RatFunc k) K] [Algebra.IsAlgebraic (RatFunc k) K] [Field Ω] [Algebra K Ω]
    [IsSepClosure K Ω] (p : ℕ), p.Prime → GroundTheory.ProfCoh.cdp p (Ω ≃ₐ[K] Ω) ≤ 1 := by
  intro k K Ω _ _ _ _ _ _ _ _ p hp
  by_cases hpK : (p : K) = 0
  · exact cdp_le_one_of_char_eq K Ω p hp hpK
  · exact cdp_le_one_of_ne_char k K Ω p hp hpK

end GlobalTheory.TsenCD

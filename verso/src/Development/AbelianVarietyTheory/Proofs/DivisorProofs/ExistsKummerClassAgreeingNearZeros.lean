import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.DivisorSupportCondition
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsExcisionNbhdSelf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CupChernKummerPullbackNaturalityStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChernClassKummerClassAdditiveStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsKummerClassOnFinerEtaleNbhdCurveStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitLocalizationEtaleNbhdEqUnitMulPowStatement
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace GlobalTheory.EtC.KummerStep

noncomputable abbrev gU (A : Type) [CommRing A] : Aˣ →* (Γ(Spec (CommRingCat.of A), ⊤))ˣ :=
  Units.map (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom.toMonoidHom

/- English proof (translation)
Simplify using `only [spMap, CommRingCat.ofHom_comp, Spec.map_comp, Functor.map_comp]`.
-/
theorem spMap_comp' {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap (g.comp f) = spMap g ≫ spMap f := by
  simp only [spMap, CommRingCat.ofHom_comp, Spec.map_comp, Functor.map_comp]

/- English proof (translation)
Simplify using `using hq.map φ`.
-/
theorem isUnit_natCast_of {k R : Type} [Field k] [CommRing R] (φ : k →+* R) {q : ℕ} (hq : IsUnit (q : k)) :
    IsUnit (q : R) := by
  simpa using hq.map φ

/- English proof (translation)
Establish `hq' : IsUnit (q : Γ(Spec (CommRingCat.of A), ⊤))`. Simplify using `using hq.map (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom`. Rewrite using `[(GlobalTheory.T.cup_chern_kummer_pullback_naturality q).2.2.2 (Spec.map (CommRingCat.ofHom φ)) (gU A u) hq']`. Use `congr 1`. Use `ext`.

Establish `h` using `Scheme.ΓSpecIso_naturality (CommRingCat.ofHom φ)`. Establish `h2 : (Spec.map (CommRingCat.ofHom φ)).appTop = (Scheme.ΓSpecIso (CommRingCat.of A)).hom ≫ CommRingCat.ofHom φ ≫ (Scheme.ΓSpecIso (CommRingCat.of B)).inv`. Rewrite using `[← Category.assoc, ← h]`. Simplify using the standard rewrite rules. Simplify using `only [gU, Units.coe_map, MonoidHom.coe_coe]`.

Rewrite using `[h2]`. Simplify using `only [CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply, CommRingCat.hom_ofHom]`. Simplify using the standard rewrite rules.
-/
theorem kum_spMap (q : ℕ) [NeZero q] {A B : Type} [CommRing A] [CommRing B] (φ : A →+* B) (hq : IsUnit (q : A))
    (u : Aˣ) : pull _ (spMap φ) _ _ (kum q (gU A u)) = kum q (gU B (Units.map φ.toMonoidHom u)) := by
  have hq' : IsUnit (q : Γ(Spec (CommRingCat.of A), ⊤)) := by
    simpa using hq.map (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom
  rw [(GlobalTheory.T.cup_chern_kummer_pullback_naturality q).2.2.2 (Spec.map (CommRingCat.ofHom φ)) (gU A u) hq']
  congr 1
  ext
  have h := Scheme.ΓSpecIso_naturality (CommRingCat.ofHom φ)
  have h2 : (Spec.map (CommRingCat.ofHom φ)).appTop = (Scheme.ΓSpecIso (CommRingCat.of A)).hom ≫ CommRingCat.ofHom φ ≫
      (Scheme.ΓSpecIso (CommRingCat.of B)).inv := by
    rw [← Category.assoc, ← h]; simp
  simp only [gU, Units.coe_map, MonoidHom.coe_coe]
  rw [h2]
  simp only [CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply, CommRingCat.hom_ofHom]
  simp

/- English proof (translation)
Establish `hq' : IsUnit (q : Γ(Spec (CommRingCat.of A), ⊤))`. Simplify using `using hq.map (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom`. Rewrite using `[map_mul, map_pow, ((GlobalTheory.T.chernClass_kummerClass_additive q).2 (gU A u) _ hq').1, ((GlobalTheory.T.chernClass_kummerClass_additive q).2 (gU A v) (gU A v) hq').2, add_zero]`.
-/
theorem kum_pow_eq (q : ℕ) [NeZero q] {A : Type} [CommRing A] (hq : IsUnit (q : A)) (u v : Aˣ) :
    kum q (gU A (u * v ^ q)) = kum q (gU A u) := by
  have hq' : IsUnit (q : Γ(Spec (CommRingCat.of A), ⊤)) := by
    simpa using hq.map (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom
  rw [map_mul, map_pow, ((GlobalTheory.T.chernClass_kummerClass_additive q).2 (gU A u) _ hq').1, ((GlobalTheory.T.chernClass_kummerClass_additive q).2 (gU A v) (gU A v) hq').2, add_zero]

/- English proof (translation)
Use `kum_pow_eq q hq 1 v` as an intermediate fact. Rewrite `this` using `[one_mul]`. Rewrite using `[this, map_one]`. Establish `hq' : IsUnit (q : Γ(Spec (CommRingCat.of A), ⊤))`. Simplify using `using hq.map (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom`.

Establish `h` using `((GlobalTheory.T.chernClass_kummerClass_additive q).2 (1 : (Γ(Spec (CommRingCat.of A), ⊤))ˣ) 1 hq').1`. Rewrite `h` using `[one_mul]`. Simplify using `using h`.
-/
theorem kum_pow (q : ℕ) [NeZero q] {A : Type} [CommRing A] (hq : IsUnit (q : A)) (v : Aˣ) :
    kum q (gU A (v ^ q)) = 0 := by
  have := kum_pow_eq q hq 1 v
  rw [one_mul] at this
  rw [this, map_one]
  have hq' : IsUnit (q : Γ(Spec (CommRingCat.of A), ⊤)) := by
    simpa using hq.map (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom
  have h := ((GlobalTheory.T.chernClass_kummerClass_additive q).2 (1 : (Γ(Spec (CommRingCat.of A), ⊤))ˣ) 1 hq').1
  rw [one_mul] at h
  simpa using h

/- English proof (translation)
Introduce `q _ k B _ _ _ _ _ _ hq f hf A' _ _ hA' w`. Take `⟨A₂, _, _, _, _, hA₂, c, hc⟩` from `L1 q k B hq f hf A' hA' w`. Use `set c₀ : (Localization.Away (algebraMap B A₂ f))ˣ := Units.map (Scheme.ΓSpecIso (CommRingCat.of (Localization.Away (algebraMap B A₂ f)))).hom.hom.toMonoidHom c with hc₀`. Establish `hcc : gU _ c₀ = c` using `by ext; simp [c₀, gU]`. Take `⟨g, hfg, u, ⟨A₃, _, _, _, _, hA₃, hg, v, hv⟩, C, _, _, hC, v', hv'⟩` from `L2 q k B hq f hf A₂ hA₂ c₀`.

Use `letI : Algebra A' A₃ := ((algebraMap A₂ A₃).comp (algebraMap A' A₂)).toAlgebra`. Use `haveI : IsScalarTower B A' A₃ := IsScalarTower.of_algebraMap_eq (fun b => by show algebraMap B A₃ b = algebraMap A₂ A₃ (algebraMap A' A₂ (algebraMap B A' b))`. Rewrite using `[← IsScalarTower.algebraMap_apply B A' A₂, ← IsScalarTower.algebraMap_apply B A₂ A₃])`. Establish `hkB : ∀ (R : Type) [CommRing R] [Algebra B R], IsUnit (q : R)` using `fun R _ _ => isUnit_natCast_of ((algebraMap B R).comp (algebraMap k B)) hq`. Use `⟨g, hfg, A₃, C, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, hA₃, hg, hC, kum q (gU _ u), ?_, ?_⟩` and prove the remaining obligations.

Rewrite using `[kum_spMap q _ (hkB _)]`. Establish `: Units.map (Localization.awayMap (algebraMap B C) (f * g)).toMonoidHom u = v' ^ q` using `by ext; simpa using hv'`. Rewrite using `[this]`. Conclude with `kum_pow q (hkB _) v'`. Introduce `φ ψ hφ hψ`.

Establish `hu₁ : IsUnit (((algebraMap A₂ (Localization.Away (algebraMap B A₂ f))).comp (algebraMap A' A₂)) (algebraMap B A' f))`. Rewrite using `[RingHom.comp_apply, ← IsScalarTower.algebraMap_apply B A' A₂]`. Conclude with `IsLocalization.Away.algebraMap_isUnit _`. Establish `hu₂ : IsUnit (((algebraMap A₃ (Localization.Away (algebraMap B A₃ f))).comp (algebraMap A₂ A₃)) (algebraMap B A₂ f))`. Rewrite using `[RingHom.comp_apply, ← IsScalarTower.algebraMap_apply B A₂ A₃]`.

Conclude with `IsLocalization.Away.algebraMap_isUnit _`. Use `set φ₁ : Localization.Away (algebraMap B A' f) →+* Localization.Away (algebraMap B A₂ f) := IsLocalization.Away.lift (algebraMap B A' f) hu₁`. Use `set φ₂ : Localization.Away (algebraMap B A₂ f) →+* Localization.Away (algebraMap B A₃ f) := IsLocalization.Away.lift (algebraMap B A₂ f) hu₂`. Establish `hφ₁ : φ₁.comp (algebraMap A' _) = (algebraMap A₂ _).comp (algebraMap A' A₂)` using `IsLocalization.Away.lift_comp (S := Localization.Away (algebraMap B A' f)) (algebraMap B A' f) hu₁`. Establish `hφ₂ : φ₂.comp (algebraMap A₂ _) = (algebraMap A₃ _).comp (algebraMap A₂ A₃)` using `IsLocalization.Away.lift_comp (S := Localization.Away (algebraMap B A₂ f)) (algebraMap B A₂ f) hu₂`.

Establish `hφe : φ = φ₂.comp φ₁`. Use `IsLocalization.ringHom_ext (Submonoid.powers (algebraMap B A' f)) ?_` and prove the remaining obligations. Rewrite using `[hφ, RingHom.comp_assoc, hφ₁, ← RingHom.comp_assoc, hφ₂, RingHom.comp_assoc]`. Both sides reduce to the same expression. Establish `key` using `hv φ₂ ψ hφ₂ hψ`.

Establish `hkey : Units.map φ₂.toMonoidHom c₀ = Units.map ψ.toMonoidHom u * v ^ q` using `by ext; simpa using key`. Rewrite using `[hφe, spMap_comp', pull_comp, hc φ₁ hφ₁, ← hcc, kum_spMap q φ₂ (hkB _), hkey, kum_pow_eq q (hkB _), kum_spMap q ψ (hkB _)]`.
-/
theorem of_steps (L1 : ∀ (q : ℕ) [NeZero q] (k B : Type) [Field k] [IsAlgClosed k] [CommRing B] [IsDedekindDomain B] [Algebra k B] [Algebra.FiniteType k B], IsUnit (q : k) → ∀ f : B, f ≠ 0 → ∀ (A' : Type) [CommRing A'] [Algebra B A'], IsExcisionNbhd B A' f → ∀ w : Ht q (sp (Localization.Away (algebraMap B A' f))) 1 1, ∃ (A₂ : Type) (_ : CommRing A₂) (_ : Algebra B A₂) (_ : Algebra A' A₂) (_ : IsScalarTower B A' A₂), IsExcisionNbhd B A₂ f ∧ ∃ c : (Γ(Spec (CommRingCat.of (Localization.Away (algebraMap B A₂ f))), ⊤))ˣ, ∀ φ : Localization.Away (algebraMap B A' f) →+* Localization.Away (algebraMap B A₂ f), φ.comp (algebraMap A' _) = (algebraMap A₂ _).comp (algebraMap A' A₂) → pull _ (spMap φ) _ _ w = kum q c) (L2 : ∀ (q : ℕ) (k B : Type) [Field k] [IsAlgClosed k] [CommRing B] [IsDedekindDomain B] [Algebra k B] [Algebra.FiniteType k B], IsUnit (q : k) → ∀ f : B, f ≠ 0 → ∀ (A₂ : Type) [CommRing A₂] [Algebra B A₂], IsExcisionNbhd B A₂ f → ∀ c : (Localization.Away (algebraMap B A₂ f))ˣ, ∃ g : B, IsCoprime f g ∧ ∃ u : (Localization.Away (f * g))ˣ, (∃ (A₃ : Type) (_ : CommRing A₃) (_ : Algebra B A₃) (_ : Algebra A₂ A₃) (_ : IsScalarTower B A₂ A₃), IsExcisionNbhd B A₃ f ∧ IsUnit (algebraMap B A₃ g) ∧ ∃ v : (Localization.Away (algebraMap B A₃ f))ˣ, ∀ (φ : Localization.Away (algebraMap B A₂ f) →+* Localization.Away (algebraMap B A₃ f)) (ψ : Localization.Away (f * g) →+* Localization.Away (algebraMap B A₃ f)), φ.comp (algebraMap A₂ _) = (algebraMap A₃ _).comp (algebraMap A₂ A₃) → ψ.comp (algebraMap B _) = (algebraMap A₃ _).comp (algebraMap B A₃) → φ (c : Localization.Away (algebraMap B A₂ f)) = ψ (u : Localization.Away (f * g)) * (v : Localization.Away (algebraMap B A₃ f)) ^ q) ∧ ∃ (C : Type) (_ : CommRing C) (_ : Algebra B C), IsExcisionNbhd B C g ∧ ∃ v' : (Localization.Away (algebraMap B C (f * g)))ˣ, Localization.awayMap (algebraMap B C) (f * g) (u : Localization.Away (f * g)) = (v' : Localization.Away (algebraMap B C (f * g))) ^ q) : ∀ (q : ℕ) [NeZero q] (k B : Type) [Field k] [IsAlgClosed k] [CommRing B] [IsDedekindDomain B] [Algebra k B] [Algebra.FiniteType k B], IsUnit (q : k) → ∀ f : B, f ≠ 0 → ∀ (A' : Type) [CommRing A'] [Algebra B A'], IsExcisionNbhd B A' f → ∀ w : Ht q (sp (Localization.Away (algebraMap B A' f))) 1 1, ∃ g : B, IsCoprime f g ∧ ∃ (A₂ C : Type) (_ : CommRing A₂) (_ : CommRing C) (_ : Algebra B A₂) (_ : Algebra A' A₂) (_ : IsScalarTower B A' A₂) (_ : Algebra B C), IsExcisionNbhd B A₂ f ∧ IsUnit (algebraMap B A₂ g) ∧ IsExcisionNbhd B C g ∧ ∃ a : Ht q (sp (Localization.Away (f * g))) 1 1, pull _ (spMap (Localization.awayMap (algebraMap B C) (f * g))) _ _ a = 0 ∧ ∀ (φ : Localization.Away (algebraMap B A' f) →+* Localization.Away (algebraMap B A₂ f)) (ψ : Localization.Away (f * g) →+* Localization.Away (algebraMap B A₂ f)), φ.comp (algebraMap A' _) = (algebraMap A₂ _).comp (algebraMap A' A₂) → ψ.comp (algebraMap B _) = (algebraMap A₂ _).comp (algebraMap B A₂) → pull _ (spMap φ) _ _ w = pull _ (spMap ψ) _ _ a := by
  intro q _ k B _ _ _ _ _ _ hq f hf A' _ _ hA' w
  obtain ⟨A₂, _, _, _, _, hA₂, c, hc⟩ := L1 q k B hq f hf A' hA' w
  set c₀ : (Localization.Away (algebraMap B A₂ f))ˣ :=
    Units.map (Scheme.ΓSpecIso (CommRingCat.of (Localization.Away (algebraMap B A₂ f)))).hom.hom.toMonoidHom c with hc₀
  have hcc : gU _ c₀ = c := by
    ext; simp [c₀, gU]
  obtain ⟨g, hfg, u, ⟨A₃, _, _, _, _, hA₃, hg, v, hv⟩, C, _, _, hC, v', hv'⟩ := L2 q k B hq f hf A₂ hA₂ c₀
  letI : Algebra A' A₃ := ((algebraMap A₂ A₃).comp (algebraMap A' A₂)).toAlgebra
  haveI : IsScalarTower B A' A₃ := IsScalarTower.of_algebraMap_eq (fun b => by
    show algebraMap B A₃ b = algebraMap A₂ A₃ (algebraMap A' A₂ (algebraMap B A' b))
    rw [← IsScalarTower.algebraMap_apply B A' A₂, ← IsScalarTower.algebraMap_apply B A₂ A₃])
  have hkB : ∀ (R : Type) [CommRing R] [Algebra B R], IsUnit (q : R) := fun R _ _ =>
    isUnit_natCast_of ((algebraMap B R).comp (algebraMap k B)) hq
  refine ⟨g, hfg, A₃, C, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    hA₃, hg, hC, kum q (gU _ u), ?_, ?_⟩
  · rw [kum_spMap q _ (hkB _)]
    have : Units.map (Localization.awayMap (algebraMap B C) (f * g)).toMonoidHom u = v' ^ q := by
      ext; simpa using hv'
    rw [this]
    exact kum_pow q (hkB _) v'
  · intro φ ψ hφ hψ
    have hu₁ : IsUnit (((algebraMap A₂ (Localization.Away (algebraMap B A₂ f))).comp (algebraMap A' A₂))
        (algebraMap B A' f)) := by
      rw [RingHom.comp_apply, ← IsScalarTower.algebraMap_apply B A' A₂]
      exact IsLocalization.Away.algebraMap_isUnit _
    have hu₂ : IsUnit (((algebraMap A₃ (Localization.Away (algebraMap B A₃ f))).comp (algebraMap A₂ A₃))
        (algebraMap B A₂ f)) := by
      rw [RingHom.comp_apply, ← IsScalarTower.algebraMap_apply B A₂ A₃]
      exact IsLocalization.Away.algebraMap_isUnit _
    set φ₁ : Localization.Away (algebraMap B A' f) →+* Localization.Away (algebraMap B A₂ f) :=
      IsLocalization.Away.lift (algebraMap B A' f) hu₁
    set φ₂ : Localization.Away (algebraMap B A₂ f) →+* Localization.Away (algebraMap B A₃ f) :=
      IsLocalization.Away.lift (algebraMap B A₂ f) hu₂
    have hφ₁ : φ₁.comp (algebraMap A' _) = (algebraMap A₂ _).comp (algebraMap A' A₂) :=
      IsLocalization.Away.lift_comp (S := Localization.Away (algebraMap B A' f)) (algebraMap B A' f) hu₁
    have hφ₂ : φ₂.comp (algebraMap A₂ _) = (algebraMap A₃ _).comp (algebraMap A₂ A₃) :=
      IsLocalization.Away.lift_comp (S := Localization.Away (algebraMap B A₂ f)) (algebraMap B A₂ f) hu₂
    have hφe : φ = φ₂.comp φ₁ := by
      refine IsLocalization.ringHom_ext (Submonoid.powers (algebraMap B A' f)) ?_
      rw [hφ, RingHom.comp_assoc, hφ₁, ← RingHom.comp_assoc, hφ₂, RingHom.comp_assoc]
      rfl
    have key := hv φ₂ ψ hφ₂ hψ
    have hkey : Units.map φ₂.toMonoidHom c₀ = Units.map ψ.toMonoidHom u * v ^ q := by
      ext; simpa using key
    rw [hφe, spMap_comp', pull_comp, hc φ₁ hφ₁, ← hcc, kum_spMap q φ₂ (hkB _), hkey, kum_pow_eq q (hkB _),
      kum_spMap q ψ (hkB _)]

/- English proof (translation)
The claim follows from `of_steps GlobalTheory.T.exists_kummerClass_on_finer_etaleNbhd_curve GlobalTheory.T.unit_localization_etaleNbhd_eq_unit_mul_pow`.
-/
theorem exists_class_agreeing_near_zeros : ∀ (q : ℕ) [NeZero q] (k B : Type) [Field k] [IsAlgClosed k] [CommRing B] [IsDedekindDomain B] [Algebra k B] [Algebra.FiniteType k B], IsUnit (q : k) → ∀ f : B, f ≠ 0 → ∀ (A' : Type) [CommRing A'] [Algebra B A'], IsExcisionNbhd B A' f → ∀ w : Ht q (sp (Localization.Away (algebraMap B A' f))) 1 1, ∃ g : B, IsCoprime f g ∧ ∃ (A₂ C : Type) (_ : CommRing A₂) (_ : CommRing C) (_ : Algebra B A₂) (_ : Algebra A' A₂) (_ : IsScalarTower B A' A₂) (_ : Algebra B C), IsExcisionNbhd B A₂ f ∧ IsUnit (algebraMap B A₂ g) ∧ IsExcisionNbhd B C g ∧ ∃ a : Ht q (sp (Localization.Away (f * g))) 1 1, pull _ (spMap (Localization.awayMap (algebraMap B C) (f * g))) _ _ a = 0 ∧ ∀ (φ : Localization.Away (algebraMap B A' f) →+* Localization.Away (algebraMap B A₂ f)) (ψ : Localization.Away (f * g) →+* Localization.Away (algebraMap B A₂ f)), φ.comp (algebraMap A' _) = (algebraMap A₂ _).comp (algebraMap A' A₂) → ψ.comp (algebraMap B _) = (algebraMap A₂ _).comp (algebraMap B A₂) → pull _ (spMap φ) _ _ w = pull _ (spMap ψ) _ _ a :=
  of_steps GlobalTheory.T.exists_kummerClass_on_finer_etaleNbhd_curve GlobalTheory.T.unit_localization_etaleNbhd_eq_unit_mul_pow

end GlobalTheory.EtC.KummerStep

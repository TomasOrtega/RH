import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MuValInjective
import Development.AbelianVarietyTheory.Definitions.Divisors.SecClass
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleLocallyIffAffineEtalePointCoverStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleSheafOfRingFunctorSectionsLocallyBijectiveStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleLocalPropertyCalculusRulesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrimitiveRootPowUnitSubProdPropertiesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleLocalPrimitiveRootAndRootsOfUnityStatement
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC GlobalTheory.EtC.MuTw

noncomputable section
namespace GlobalTheory.EtC.MuTw.Inj

variable (q : ℕ) [NeZero q]

/- English proof (translation)
Rewrite using `[Scheme.Hom.comp_appTop]`. Both sides reduce to the same expression.
-/
theorem comp_appTop_apply' {X Y Z : Scheme.{0}} (g : X ⟶ Y) (h : Y ⟶ Z) (a : Γ(Z, ⊤)) :
    (g ≫ h).appTop.hom a = g.appTop.hom (h.appTop.hom a) := by
  rw [Scheme.Hom.comp_appTop]; rfl

/- English proof (translation)
Assume the negation of the conclusion as `hC`. Establish `hne : ¬ C.val ≡ 0 [MOD q]`. Introduce `hm`. Apply `hC` to reduce the goal to its premises. Rewrite using `[← ZMod.val_eq_zero]`.

Unfold `Nat.ModEq at hm`. Rewrite `hm` using `[Nat.mod_eq_of_lt (ZMod.val_lt C), Nat.zero_mod]`. Then use the resulting hypothesis. Establish `hu` using `(GlobalTheory.T.primitiveRoot_pow_unit_sub_prod_properties q A).2.2.1 ζ C.val 0 hne`. Rewrite `hu` using `[h, pow_zero, sub_self]`. Conclude with `not_isUnit_zero hu`.
-/
theorem eq_zero_of_pow_eq_one {A : Type} [CommRing A] [Nontrivial A] (ζ : Prim q A) (C : ZMod q)
    (h : ζ.1 ^ C.val = 1) : C = 0 := by
  by_contra hC
  have hne : ¬ C.val ≡ 0 [MOD q] := by
    intro hm
    apply hC
    rw [← ZMod.val_eq_zero]
    unfold Nat.ModEq at hm
    rwa [Nat.mod_eq_of_lt (ZMod.val_lt C), Nat.zero_mod] at hm
  have hu := (GlobalTheory.T.primitiveRoot_pow_unit_sub_prod_properties q A).2.2.1 ζ C.val 0 hne
  rw [h, pow_zero, sub_self] at hu
  exact not_isUnit_zero hu

/- English proof (translation)
Rewrite using `[Submodule.mkQ_apply, Submodule.mkQ_apply, Submodule.Quotient.eq]`. Establish `hmem : Finsupp.single ξ 1 - Finsupp.single ζ (ULift.up ((a ^ (1 : ℤ) : (ZMod q)ˣ) : ZMod q)) ∈ twRel q 1 A` using `Submodule.subset_span ⟨ζ, ξ, a, h, rfl⟩`. Use `(twRel q 1 A).smul_mem c hmem` as an intermediate fact. Use `this using 1` and compare the differences between its conclusion and the goal. Rewrite using `[smul_sub, Finsupp.smul_single, Finsupp.smul_single, smul_eq_mul, smul_eq_mul, mul_one, zpow_one]`.
-/
theorem mk_single_eq {A : Type} [CommRing A] (ζ ξ : Prim q A) (a : (ZMod q)ˣ)
    (h : ξ.1 = ζ.1 ^ (a : ZMod q).val) (c : ULift.{1} (ZMod q)) :
    (twRel q 1 A).mkQ (Finsupp.single ξ c) = (twRel q 1 A).mkQ (Finsupp.single ζ (c * ULift.up (a : ZMod q))) := by
  rw [Submodule.mkQ_apply, Submodule.mkQ_apply, Submodule.Quotient.eq]
  have hmem : Finsupp.single ξ 1 - Finsupp.single ζ (ULift.up ((a ^ (1 : ℤ) : (ZMod q)ˣ) : ZMod q)) ∈ twRel q 1 A :=
    Submodule.subset_span ⟨ζ, ξ, a, h, rfl⟩
  have := (twRel q 1 A).smul_mem c hmem
  convert this using 1
  rw [smul_sub, Finsupp.smul_single, Finsupp.smul_single, smul_eq_mul, smul_eq_mul, mul_one, zpow_one]

/- English proof (translation)
Use `choose! a ha using h`. Use `⟨∑ ξ ∈ f.support, f ξ * ULift.up (a ξ : ZMod q), ?_⟩` and prove the remaining obligations. Use `conv_lhs => rw [← Finsupp.sum_single f]`. Rewrite using `[Finsupp.sum, map_sum, Finsupp.single_finsetSum, map_sum]`. Conclude with `Finset.sum_congr rfl fun ξ hξ => mk_single_eq q ζ ξ (a ξ) (ha ξ hξ) (f ξ)`.
-/
theorem mk_eq_single {A : Type} [CommRing A] (ζ : Prim q A) (f : Prim q A →₀ ULift.{1} (ZMod q))
    (h : ∀ ξ ∈ f.support, ∃ a : (ZMod q)ˣ, ξ.1 = ζ.1 ^ (a : ZMod q).val) :
    ∃ C : ULift.{1} (ZMod q), (twRel q 1 A).mkQ f = (twRel q 1 A).mkQ (Finsupp.single ζ C) := by
  classical
  choose! a ha using h
  refine ⟨∑ ξ ∈ f.support, f ξ * ULift.up (a ξ : ZMod q), ?_⟩
  conv_lhs => rw [← Finsupp.sum_single f]
  rw [Finsupp.sum, map_sum, Finsupp.single_finsetSum, map_sum]
  exact Finset.sum_congr rfl fun ξ hξ => mk_single_eq q ζ ξ (a ξ) (ha ξ hξ) (f ξ)

end GlobalTheory.EtC.MuTw.Inj

namespace GlobalTheory.EtC.MuTw.Inj
variable (q : ℕ) [NeZero q]

/- English proof (translation)
Take `⟨f, rfl⟩` from `Submodule.mkQ_surjective (twRel q 1 Γ(V, ⊤)) m`. Distinguish the cases in `hf : f = 0`. Use `⟨V, 𝟙 V, inferInstance, inferInstance, ⟨v, rfl⟩, ?_⟩` and prove the remaining obligations. Establish `h0 : ((twRel q 1 Γ(V, ⊤)).mkQ f : (twF q 1).obj Γ(V, ⊤)) = 0` using `by rw [hf, map_zero]`. Rewrite using `[h0]`.

Conclude with `map_zero _`. Take `⟨ζ₀, hζ₀⟩` from `Finsupp.support_nonempty_iff.2 hf`. Set `P : f.support → ∀ W : Scheme.{0}, (W ⟶ V) → Prop` to `fun ξ W k => ∃ a : (ZMod q)ˣ, k.appTop.hom ξ.1.1 = k.appTop.hom ζ₀.1 ^ (a : ZMod q).val`. Establish `hL : Loc V fun W k => ∀ ξ, P ξ W k` using `(GlobalTheory.T.etaleLocal_property_calculus_rules).2.2.2.2.2.1 V f.support P fun ξ => (GlobalTheory.T.etaleLocal_primitiveRoot_and_roots_of_unity q V).2.1 ζ₀ ξ.1`. Establish `hst : ∀ (W W' : Scheme.{0}) (g : W ⟶ V) (k : W' ⟶ W), (∀ ξ, P ξ W g) → ∀ ξ, P ξ W' (k ≫ g)`.

Introduce `W W' g k h ξ`. Take `⟨a, ha⟩` from `h ξ`. Use `⟨a, ?_⟩` and prove the remaining obligations. Rewrite using `[comp_appTop_apply', comp_appTop_apply', ha, map_pow]`. Take `⟨W, k, hWa, hk, ⟨w, hw⟩, hP⟩` from `((GlobalTheory.T.etaleLocally_iff_affine_etale_point_cover V _ hst).1 hL) v`.

Use `⟨W, k, hWa, hk, ⟨w, hw⟩, ?_⟩` and prove the remaining obligations. Use `haveI : Nonempty (⊤ : W.Opens) := ⟨⟨w, trivial⟩⟩`. Use `haveI : Nontrivial Γ(W, ⊤) := Scheme.component_nontrivial W ⊤`. Set `φ` to `k.appTop.hom`. Set `ζ₁ : Prim q Γ(W, ⊤)` to `Prim.map φ ζ₀`.

Establish `hmap : ((twF q 1).map k.appTop).hom ((twRel q 1 Γ(V, ⊤)).mkQ f) = (twRel q 1 Γ(W, ⊤)).mkQ (Finsupp.mapDomain (Prim.map φ) f)` using `rfl`. Take `⟨C, hC⟩` from `mk_eq_single q ζ₁ (Finsupp.mapDomain (Prim.map φ) f) (by`. Introduce `ξ' hξ'`. Take `⟨ξ, hξ, rfl⟩` from `Finset.mem_image.1 (Finsupp.mapDomain_support hξ')`. Take `⟨a, ha⟩` from `hP ⟨ξ, hξ⟩`.

Conclude with `⟨a, ha⟩)`. Rewrite using `[hmap, hC]`. Establish `he : ((eta q).app Γ(W, ⊤)).hom ((twF q 1).map k.appTop |>.hom ((twRel q 1 Γ(V, ⊤)).mkQ f)) = 0`. Use `congrArg (fun g => g.hom ((twRel q 1 Γ(V, ⊤)).mkQ f)) ((eta q).naturality k.appTop)` as an intermediate fact. Rewrite `this` using `[ModuleCat.hom_comp, ModuleCat.hom_comp]`.

Use `this.trans ?_` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `((muF q).map k.appTop).hom (((eta q).app Γ(V, ⊤)).hom ((twRel q 1 Γ(V, ⊤)).mkQ f)) = 0`. Rewrite using `[hm, map_zero]`. Rewrite `he` using `[hmap, hC, Submodule.mkQ_apply, eta_mk]`. Establish `h1 : ζ₁.1 ^ C.down.val = 1`.

Use `congrArg (fun y : ULift.{1} (Additive (rootsOfUnity q Γ(W, ⊤))) => (((Additive.toMul y.down : rootsOfUnity q Γ(W, ⊤)) : Γ(W, ⊤)ˣ) : Γ(W, ⊤))) he` as an intermediate fact. Simplify using `only [smul_eq, toMul_nsmul, toMul_ofMul] at this`. Rewrite `this` using `[root_pow_coe]`. Conclude with `this.trans rfl`. Establish `hC0 : C = 0` using `ULift.ext _ _ (eq_zero_of_pow_eq_one q ζ₁ C.down h1)`.

Rewrite using `[hC0, Finsupp.single_zero, map_zero]`. Both sides reduce to the same expression.
-/
theorem local_zero (V : Scheme.{0}) [IsAffine V] (m : (twF q 1).obj Γ(V, ⊤))
    (hm : ((eta q).app Γ(V, ⊤)).hom m = 0) (v : V) :
    ∃ (W : Scheme.{0}) (k : W ⟶ V), IsAffine W ∧ Etale k ∧ v ∈ Set.range k ∧ ((twF q 1).map k.appTop).hom m = 0 := by
  classical
  obtain ⟨f, rfl⟩ := Submodule.mkQ_surjective (twRel q 1 Γ(V, ⊤)) m
  by_cases hf : f = 0
  · refine ⟨V, 𝟙 V, inferInstance, inferInstance, ⟨v, rfl⟩, ?_⟩
    have h0 : ((twRel q 1 Γ(V, ⊤)).mkQ f : (twF q 1).obj Γ(V, ⊤)) = 0 := by rw [hf, map_zero]
    rw [h0]
    exact map_zero _
  obtain ⟨ζ₀, hζ₀⟩ := Finsupp.support_nonempty_iff.2 hf
  let P : f.support → ∀ W : Scheme.{0}, (W ⟶ V) → Prop := fun ξ W k =>
    ∃ a : (ZMod q)ˣ, k.appTop.hom ξ.1.1 = k.appTop.hom ζ₀.1 ^ (a : ZMod q).val
  have hL : Loc V fun W k => ∀ ξ, P ξ W k :=
    (GlobalTheory.T.etaleLocal_property_calculus_rules).2.2.2.2.2.1 V f.support P fun ξ => (GlobalTheory.T.etaleLocal_primitiveRoot_and_roots_of_unity q V).2.1 ζ₀ ξ.1
  have hst : ∀ (W W' : Scheme.{0}) (g : W ⟶ V) (k : W' ⟶ W), (∀ ξ, P ξ W g) → ∀ ξ, P ξ W' (k ≫ g) := by
    intro W W' g k h ξ
    obtain ⟨a, ha⟩ := h ξ
    refine ⟨a, ?_⟩
    rw [comp_appTop_apply', comp_appTop_apply', ha, map_pow]
  obtain ⟨W, k, hWa, hk, ⟨w, hw⟩, hP⟩ := ((GlobalTheory.T.etaleLocally_iff_affine_etale_point_cover V _ hst).1 hL) v
  refine ⟨W, k, hWa, hk, ⟨w, hw⟩, ?_⟩
  haveI : Nonempty (⊤ : W.Opens) := ⟨⟨w, trivial⟩⟩
  haveI : Nontrivial Γ(W, ⊤) := Scheme.component_nontrivial W ⊤
  let φ := k.appTop.hom
  let ζ₁ : Prim q Γ(W, ⊤) := Prim.map φ ζ₀
  have hmap : ((twF q 1).map k.appTop).hom ((twRel q 1 Γ(V, ⊤)).mkQ f) =
      (twRel q 1 Γ(W, ⊤)).mkQ (Finsupp.mapDomain (Prim.map φ) f) := rfl
  obtain ⟨C, hC⟩ := mk_eq_single q ζ₁ (Finsupp.mapDomain (Prim.map φ) f) (by
    intro ξ' hξ'
    obtain ⟨ξ, hξ, rfl⟩ := Finset.mem_image.1 (Finsupp.mapDomain_support hξ')
    obtain ⟨a, ha⟩ := hP ⟨ξ, hξ⟩
    exact ⟨a, ha⟩)
  rw [hmap, hC]
  have he : ((eta q).app Γ(W, ⊤)).hom ((twF q 1).map k.appTop |>.hom ((twRel q 1 Γ(V, ⊤)).mkQ f)) = 0 := by
    have := congrArg (fun g => g.hom ((twRel q 1 Γ(V, ⊤)).mkQ f)) ((eta q).naturality k.appTop)
    rw [ModuleCat.hom_comp, ModuleCat.hom_comp] at this
    refine this.trans ?_
    change ((muF q).map k.appTop).hom (((eta q).app Γ(V, ⊤)).hom ((twRel q 1 Γ(V, ⊤)).mkQ f)) = 0
    rw [hm, map_zero]
  rw [hmap, hC, Submodule.mkQ_apply, eta_mk] at he
  have h1 : ζ₁.1 ^ C.down.val = 1 := by
    have := congrArg (fun y : ULift.{1} (Additive (rootsOfUnity q Γ(W, ⊤))) =>
      (((Additive.toMul y.down : rootsOfUnity q Γ(W, ⊤)) : Γ(W, ⊤)ˣ) : Γ(W, ⊤))) he
    simp only [smul_eq, toMul_nsmul, toMul_ofMul] at this
    rw [root_pow_coe] at this
    exact this.trans rfl
  have hC0 : C = 0 := ULift.ext _ _ (eq_zero_of_pow_eq_one q ζ₁ C.down h1)
  rw [hC0, Finsupp.single_zero, map_zero]
  rfl

end GlobalTheory.EtC.MuTw.Inj

namespace GlobalTheory.EtC.MuTw.Inj

/- English proof (translation)
Express the relevant statement in the definitionally equal form `((tw q 1).obj.map (k ≫ g).op).hom x = ((tw q 1).obj.map k.op).hom (((tw q 1).obj.map g.op).hom x)`. Rewrite using `[op_comp, Functor.map_comp, ModuleCat.hom_comp, LinearMap.comp_apply]`.
-/
theorem res_comp {q : ℕ} {V W U : Scheme.{0}} (g : V ⟶ U) (k : W ⟶ V) (x : Sec (tw q 1) U) :
    Sec.res (k ≫ g) x = Sec.res k (Sec.res g x) := by
  change ((tw q 1).obj.map (k ≫ g).op).hom x = ((tw q 1).obj.map k.op).hom (((tw q 1).obj.map g.op).hom x)
  rw [op_comp, Functor.map_comp, ModuleCat.hom_comp, LinearMap.comp_apply]

/- English proof (translation)
Introduce `q _ U _`. Use `(injective_iff_map_eq_zero ((etaS q).hom.app (op U)).hom).2 fun x hx => ?_` and prove the remaining obligations. Establish `hst : ∀ (V W : Scheme.{0}) (g : V ⟶ U) (k : W ⟶ V), Sec.res g x = 0 → Sec.res (k ≫ g) x = 0`. Introduce `V W g k h`. Rewrite using `[res_comp, h]`.

Conclude with `map_zero _`. Establish `hloc : Loc U fun W g => Sec.res g x = 0`. Rewrite using `[GlobalTheory.T.etaleLocally_iff_affine_etale_point_cover U _ hst]`. Introduce `u`. Take `⟨V, j, v, m, hVa, hj, hjv, hm⟩` from `(GlobalTheory.T.etaleSheafOfRingFunctor_sections_locally_bijective (ZMod q) (twF q 1) U).1 x u`.

Establish `hem : ((eta q).app Γ(V, ⊤)).hom m = 0`. Establish `hm' : (ofRings.sec (twF q 1) V m : Sec (tw q 1) V) = Sec.res (F` using `tw q 1) j x := hm`. Rewrite using `[← etaS_sec, hm', etaS_res]`. Express the relevant statement in the definitionally equal form `Sec.res j (((etaS q).hom.app (op U)).hom x) = 0`. Rewrite using `[hx]`.

Conclude with `map_zero _`. Take `⟨W, k, hWa, hk, ⟨w, hw⟩, hmW⟩` from `local_zero q V m hem v`. Use `⟨W, k ≫ j, hWa, inferInstance, ⟨w, ?_⟩, ?_⟩` and prove the remaining obligations. Rewrite using `[Scheme.Hom.comp_apply, hw, hjv]`. Establish `hm' : Sec.res (F` using `tw q 1) j x = (ofRings.sec (twF q 1) V m : Sec (tw q 1) V) := hm.symm`.

Rewrite using `[res_comp, hm']`. Use `((GlobalTheory.T.etaleSheafOfRingFunctor_sections_locally_bijective (ZMod q) (twF q 1) V).2.2 W k m).trans ?_` and prove the remaining obligations. Rewrite using `[hmW]`. Conclude with `map_zero _`. Take `⟨S, hS, hSP⟩` from `hloc`.

Establish `hF` using `(tw q 1).property`. Rewrite `hF` using `[Presheaf.isSheaf_iff_isSheaf_forget _ _ (forget (ModuleCat.{1} (ULift.{1} (ZMod q)))), isSheaf_iff_isSheaf_of_type]`. Use `(hF S hS).isSeparatedFor.ext fun V g hg => ?_` and prove the remaining obligations. Establish `h1` using `hSP V g hg`. Express the relevant statement in the definitionally equal form `Sec.res g x = Sec.res g 0`.

Rewrite using `[h1]`. Conclude with `(map_zero _).symm`.
-/
theorem etaS_injective : ∀ (q : ℕ) [NeZero q] (U : Scheme.{0}), IsUnit (q : Γ(U, ⊤)) →
    Function.Injective ((etaS q).hom.app (op U)).hom := by
  intro q _ U _
  refine (injective_iff_map_eq_zero ((etaS q).hom.app (op U)).hom).2 fun x hx => ?_
  have hst : ∀ (V W : Scheme.{0}) (g : V ⟶ U) (k : W ⟶ V), Sec.res g x = 0 → Sec.res (k ≫ g) x = 0 := by
    intro V W g k h
    rw [res_comp, h]
    exact map_zero _
  have hloc : Loc U fun W g => Sec.res g x = 0 := by
    rw [GlobalTheory.T.etaleLocally_iff_affine_etale_point_cover U _ hst]
    intro u
    obtain ⟨V, j, v, m, hVa, hj, hjv, hm⟩ := (GlobalTheory.T.etaleSheafOfRingFunctor_sections_locally_bijective (ZMod q) (twF q 1) U).1 x u
    have hem : ((eta q).app Γ(V, ⊤)).hom m = 0 := by
      have hm' : (ofRings.sec (twF q 1) V m : Sec (tw q 1) V) = Sec.res (F := tw q 1) j x := hm
      rw [← etaS_sec, hm', etaS_res]
      change Sec.res j (((etaS q).hom.app (op U)).hom x) = 0
      rw [hx]
      exact map_zero _
    obtain ⟨W, k, hWa, hk, ⟨w, hw⟩, hmW⟩ := local_zero q V m hem v
    refine ⟨W, k ≫ j, hWa, inferInstance, ⟨w, ?_⟩, ?_⟩
    · rw [Scheme.Hom.comp_apply, hw, hjv]
    · have hm' : Sec.res (F := tw q 1) j x = (ofRings.sec (twF q 1) V m : Sec (tw q 1) V) := hm.symm
      rw [res_comp, hm']
      refine ((GlobalTheory.T.etaleSheafOfRingFunctor_sections_locally_bijective (ZMod q) (twF q 1) V).2.2 W k m).trans ?_
      rw [hmW]
      exact map_zero _
  obtain ⟨S, hS, hSP⟩ := hloc
  have hF := (tw q 1).property
  rw [Presheaf.isSheaf_iff_isSheaf_forget _ _ (forget (ModuleCat.{1} (ULift.{1} (ZMod q)))),
    isSheaf_iff_isSheaf_of_type] at hF
  refine (hF S hS).isSeparatedFor.ext fun V g hg => ?_
  have h1 := hSP V g hg
  change Sec.res g x = Sec.res g 0
  rw [h1]
  exact (map_zero _).symm

end GlobalTheory.EtC.MuTw.Inj

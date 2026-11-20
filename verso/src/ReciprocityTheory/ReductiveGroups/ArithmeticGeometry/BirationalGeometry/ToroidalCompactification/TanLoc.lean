import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsUnivRingBc
import Lemmata.MiscLemmasQ.Imports

set_option autoImplicit false

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.Chart

section TanLoc

variable {S : Type} [CommRing S] {B : Type} [CommRing B] [Algebra S B]

def dualMapS {A A' : Type} [CommRing A] [Algebra S A] [CommRing A'] [Algebra S A'] (ι : A →ₐ[S] A') :
    DualNumber A →ₐ[S] DualNumber A' := Bl.ThirdBlockLemmaB.goal1 ι

/- English proof (translation)
Simplify using `[dualMapS, Bl.ThirdBlockLemmaB.goal1, TrivSqZeroExt.lift_def]`.
-/
theorem dualMapS_fst {A A' : Type} [CommRing A] [Algebra S A] [CommRing A'] [Algebra S A'] (ι : A →ₐ[S] A')
    (x : DualNumber A) : (dualMapS ι x).fst = ι x.fst := by simp [dualMapS, Bl.ThirdBlockLemmaB.goal1, TrivSqZeroExt.lift_def]

/- English proof (translation)
Simplify using `[dualMapS, Bl.ThirdBlockLemmaB.goal1, TrivSqZeroExt.lift_def]`.
-/
theorem dualMapS_snd {A A' : Type} [CommRing A] [Algebra S A] [CommRing A'] [Algebra S A'] (ι : A →ₐ[S] A')
    (x : DualNumber A) : (dualMapS ι x).snd = ι x.snd := by simp [dualMapS, Bl.ThirdBlockLemmaB.goal1, TrivSqZeroExt.lift_def]

def scaleS {A : Type} [CommRing A] [Algebra S A] (c : A) : DualNumber A →ₐ[S] DualNumber A :=
  (scaleD c).restrictScalars S

/- English proof (translation)
Simplify using `[scaleS, scaleD]`.
-/
theorem scaleS_fst {A : Type} [CommRing A] [Algebra S A] (c : A) (x : DualNumber A) : (scaleS (S := S) c x).fst = x.fst := by
  simp [scaleS, scaleD]

/- English proof (translation)
Simplify using `[scaleS, scaleD]`.
-/
theorem scaleS_snd {A : Type} [CommRing A] [Algebra S A] (c : A) (x : DualNumber A) :
    (scaleS (S := S) c x).snd = c * x.snd := by
  simp [scaleS, scaleD]

variable {A : Type} [CommRing A] [Algebra S A] (e : B →ₐ[S] A)

def IsTanAt (h : B →ₐ[S] DualNumber A) : Prop := ∀ b, (h b).fst = e b

section Lin

variable [Module B A] [IsScalarTower S B A] (hsm : ∀ (b : B) (a : A), b • a = e b * a)

include hsm in

def derOf (h : B →ₐ[S] DualNumber A) (hh : IsTanAt e h) : Derivation S B A where
  toFun b := (h b).snd
  map_add' a b := by simp
  map_smul' r b := by simp
  map_one_eq_zero' := by simp
  leibniz' a b := by
    show (h (a * b)).snd = a • (h b).snd + b • (h a).snd
    rw [map_mul, TrivSqZeroExt.snd_mul, hsm, hsm, hh, hh]
    simp only [smul_eq_mul, MulOpposite.smul_eq_mul_unop, MulOpposite.unop_op]
    ring

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem derOf_apply (h : B →ₐ[S] DualNumber A) (hh : IsTanAt e h) (b : B) : derOf e hsm h hh b = (h b).snd := rfl

include hsm in

def ofLin (g : Ω[B⁄S] →ₗ[B] A) : B →ₐ[S] DualNumber A where
  toFun b := TrivSqZeroExt.inl (e b) + TrivSqZeroExt.inr (g (KaehlerDifferential.D S B b))
  map_one' := by ext <;> simp
  map_mul' a b := by
    ext
    · simp
    · simp only [map_mul, Derivation.leibniz, map_add, map_smul, hsm, TrivSqZeroExt.snd_add, TrivSqZeroExt.snd_inl,
        TrivSqZeroExt.snd_inr, TrivSqZeroExt.snd_mul, TrivSqZeroExt.fst_add, TrivSqZeroExt.fst_inl,
        TrivSqZeroExt.fst_inr, smul_eq_mul, MulOpposite.smul_eq_mul_unop, MulOpposite.unop_op]
      ring
  map_zero' := by ext <;> simp
  map_add' a b := by ext <;> simp
  commutes' r := by ext <;> simp [TrivSqZeroExt.algebraMap_eq_inl']

/- English proof (translation)
Simplify using `[ofLin]`.
-/
theorem ofLin_fst (g : Ω[B⁄S] →ₗ[B] A) (b : B) : (ofLin e hsm g b).fst = e b := by simp [ofLin]

/- English proof (translation)
Simplify using `[ofLin]`.
-/
theorem ofLin_snd (g : Ω[B⁄S] →ₗ[B] A) (b : B) : (ofLin e hsm g b).snd = g (KaehlerDifferential.D S B b) := by
  simp [ofLin]

end Lin

variable {A' : Type} [CommRing A'] [Algebra S A'] [Algebra A A'] [IsScalarTower S A A'] (M : Submonoid S)
  [IsLocalization (Algebra.algebraMapSubmonoid A M) A']

/- English proof (translation)
Use `⟨fun x => ?_, fun y => ?_, fun {x₁ x₂} hx => ?_⟩` and prove the remaining obligations. Take `⟨_, ⟨m, hm, rfl⟩⟩` from `x`. Establish `hu : IsUnit (algebraMap A A' (e (algebraMap S B m)))`. Rewrite using `[AlgHom.commutes]`. Conclude with `IsLocalization.map_units A' (⟨algebraMap S A m, Algebra.mem_algebraMapSubmonoid_of_mem (⟨m, hm⟩ : M)⟩ : Algebra.algebraMapSubmonoid A M)`.

Rewrite using `[Module.End.isUnit_iff]`. Take `⟨u, hu⟩` from `hu`. Prove the components needed by the constructor for the conclusion. Introduce `a₁ a₂ h`. Simplify using `only [Module.algebraMap_end_apply, hsm'] at h`.

Rewrite `h` using `[← hu]`. Conclude with `u.isUnit.mul_left_cancel h`. Introduce `a`. Use `⟨((u⁻¹ : A'ˣ) : A') * a, ?_⟩` and prove the remaining obligations. Simplify using `only [Module.algebraMap_end_apply, hsm', ← hu, ← mul_assoc, Units.mul_inv, one_mul]`.

Take `⟨⟨a, ⟨_, ⟨m, hm, rfl⟩⟩⟩, h⟩` from `IsLocalization.surj (Algebra.algebraMapSubmonoid A M) y`. Use `⟨⟨a, ⟨algebraMap S B m, Algebra.mem_algebraMapSubmonoid_of_mem (⟨m, hm⟩ : M)⟩⟩, ?_⟩` and prove the remaining obligations. Use `show algebraMap S B m • y = f a`. Rewrite using `[hsm', hf, AlgHom.commutes, ← h, mul_comm]`. Rewrite `hx` using `[hf, hf]`.

Take `⟨⟨_, ⟨m, hm, rfl⟩⟩, h⟩` from `IsLocalization.exists_of_eq (M := Algebra.algebraMapSubmonoid A M) hx`. Use `⟨⟨algebraMap S B m, Algebra.mem_algebraMapSubmonoid_of_mem (⟨m, hm⟩ : M)⟩, ?_⟩` and prove the remaining obligations. Use `show algebraMap S B m • x₁ = algebraMap S B m • x₂`. Rewrite using `[hsm, hsm, AlgHom.commutes]`. Conclude with `h`.
-/
theorem isLocalizedModule_tan [Module B A] [Module B A'] (hsm : ∀ (b : B) (a : A), b • a = e b * a)
    (hsm' : ∀ (b : B) (a : A'), b • a = algebraMap A A' (e b) * a) (f : A →ₗ[B] A') (hf : ∀ a, f a = algebraMap A A' a) :
    IsLocalizedModule (Algebra.algebraMapSubmonoid B M) f := by
  refine ⟨fun x => ?_, fun y => ?_, fun {x₁ x₂} hx => ?_⟩
  · obtain ⟨_, ⟨m, hm, rfl⟩⟩ := x
    have hu : IsUnit (algebraMap A A' (e (algebraMap S B m))) := by
      rw [AlgHom.commutes]
      exact IsLocalization.map_units A' (⟨algebraMap S A m, Algebra.mem_algebraMapSubmonoid_of_mem (⟨m, hm⟩ : M)⟩ :
        Algebra.algebraMapSubmonoid A M)
    rw [Module.End.isUnit_iff]
    obtain ⟨u, hu⟩ := hu
    constructor
    · intro a₁ a₂ h
      simp only [Module.algebraMap_end_apply, hsm'] at h
      rw [← hu] at h
      exact u.isUnit.mul_left_cancel h
    · intro a
      refine ⟨((u⁻¹ : A'ˣ) : A') * a, ?_⟩
      simp only [Module.algebraMap_end_apply, hsm', ← hu, ← mul_assoc, Units.mul_inv, one_mul]
  · obtain ⟨⟨a, ⟨_, ⟨m, hm, rfl⟩⟩⟩, h⟩ := IsLocalization.surj (Algebra.algebraMapSubmonoid A M) y
    refine ⟨⟨a, ⟨algebraMap S B m, Algebra.mem_algebraMapSubmonoid_of_mem (⟨m, hm⟩ : M)⟩⟩, ?_⟩
    show algebraMap S B m • y = f a
    rw [hsm', hf, AlgHom.commutes, ← h, mul_comm]
  · rw [hf, hf] at hx
    obtain ⟨⟨_, ⟨m, hm, rfl⟩⟩, h⟩ := IsLocalization.exists_of_eq (M := Algebra.algebraMapSubmonoid A M) hx
    refine ⟨⟨algebraMap S B m, Algebra.mem_algebraMapSubmonoid_of_mem (⟨m, hm⟩ : M)⟩, ?_⟩
    show algebraMap S B m • x₁ = algebraMap S B m • x₂
    rw [hsm, hsm, AlgHom.commutes]
    exact h

end TanLoc

section Main

variable {S : Type} [CommRing S] {B : Type} [CommRing B] [Algebra S B] [Algebra.FinitePresentation S B]
  {A : Type} [CommRing A] [Algebra S A] (e : B →ₐ[S] A)
  {A' : Type} [CommRing A'] [Algebra S A'] [Algebra A A'] [IsScalarTower S A A'] (M : Submonoid S)
  [IsLocalization (Algebra.algebraMapSubmonoid A M) A']

/- English proof (translation)
Set `ι` to `IsScalarTower.toAlgHom S A A'`. Set `iA : Module B A` to `Module.compHom A e.toRingHom`. Set `iA' : Module B A'` to `Module.compHom A' (ι.comp e).toRingHom`. Establish `hsm : ∀ (b : B) (a : A), b • a = e b * a` using `fun _ _ => rfl`. Establish `hsm' : ∀ (b : B) (a : A'), b • a = algebraMap A A' (e b) * a` using `fun _ _ => rfl`.

Establish `: IsScalarTower S B A` using `⟨fun r b a => by show e (r • b) * a = r • (e b * a)`. Rewrite using `[map_smul, smul_mul_assoc]⟩`. Establish `: IsScalarTower S B A'` using `⟨fun r b a => by show ι (e (r • b)) * a = r • (ι (e b) * a)`. Rewrite using `[map_smul, map_smul, smul_mul_assoc]⟩`. Set `f : A →ₗ[B] A'` to `{ toFun := algebraMap A A' map_add' := map_add _ map_smul' := fun b a => by show algebraMap A A' (e b * a) = algebraMap A A' (e b) * algebraMap A A' a`.

Rewrite using `[map_mul] }`. Use `isLocalizedModule_tan e M hsm hsm' f (fun _ => rfl)` as an intermediate fact. Establish `hsm'' : ∀ (b : B) (a : A'), b • a = (ι.comp e) b * a` using `fun _ _ => rfl`. Set `g'` to `(derOf (ι.comp e) hsm'' h' hh').liftKaehlerDifferential`. Take `⟨g, ⟨_, ⟨m, hm, rfl⟩⟩, hg⟩` from `Module.FinitePresentation.exists_lift_of_isLocalizedModule (Algebra.algebraMapSubmonoid B M) f g'`.

Use `⟨m, hm, ofLin e hsm g, fun b => ofLin_fst e hsm g b, ?_⟩` and prove the remaining obligations. Use extensionality with `b`. Rewrite using `[AlgHom.comp_apply, AlgHom.comp_apply, dualMapS_fst, scaleS_fst, ofLin_fst, hh']`. Both sides reduce to the same expression. Rewrite using `[AlgHom.comp_apply, AlgHom.comp_apply, dualMapS_snd, scaleS_snd, ofLin_snd]`.

Use `LinearMap.congr_fun hg (KaehlerDifferential.D S B b)` as an intermediate fact. Simplify using `only [LinearMap.comp_apply, LinearMap.smul_apply] at this`. Use `this.trans ?_` and prove the remaining obligations. Use `show (algebraMap S B m) • g' (KaehlerDifferential.D S B b) = _`. Rewrite using `[hsm', Derivation.liftKaehlerDifferential_comp_D, derOf_apply, AlgHom.commutes, ← IsScalarTower.algebraMap_apply]`.
-/
theorem tan_lift (h' : B →ₐ[S] DualNumber A') (hh' : IsTanAt ((IsScalarTower.toAlgHom S A A').comp e) h') :
    ∃ m ∈ M, ∃ h : B →ₐ[S] DualNumber A, IsTanAt e h ∧
      (dualMapS (IsScalarTower.toAlgHom S A A')).comp h = (scaleS (algebraMap S A' m)).comp h' := by
  let ι := IsScalarTower.toAlgHom S A A'
  let iA : Module B A := Module.compHom A e.toRingHom
  let iA' : Module B A' := Module.compHom A' (ι.comp e).toRingHom
  have hsm : ∀ (b : B) (a : A), b • a = e b * a := fun _ _ => rfl
  have hsm' : ∀ (b : B) (a : A'), b • a = algebraMap A A' (e b) * a := fun _ _ => rfl
  have : IsScalarTower S B A := ⟨fun r b a => by
    show e (r • b) * a = r • (e b * a)
    rw [map_smul, smul_mul_assoc]⟩
  have : IsScalarTower S B A' := ⟨fun r b a => by
    show ι (e (r • b)) * a = r • (ι (e b) * a)
    rw [map_smul, map_smul, smul_mul_assoc]⟩
  let f : A →ₗ[B] A' :=
    { toFun := algebraMap A A'
      map_add' := map_add _
      map_smul' := fun b a => by
        show algebraMap A A' (e b * a) = algebraMap A A' (e b) * algebraMap A A' a
        rw [map_mul] }
  have := isLocalizedModule_tan e M hsm hsm' f (fun _ => rfl)
  have hsm'' : ∀ (b : B) (a : A'), b • a = (ι.comp e) b * a := fun _ _ => rfl
  let g' := (derOf (ι.comp e) hsm'' h' hh').liftKaehlerDifferential
  obtain ⟨g, ⟨_, ⟨m, hm, rfl⟩⟩, hg⟩ :=
    Module.FinitePresentation.exists_lift_of_isLocalizedModule (Algebra.algebraMapSubmonoid B M) f g'
  refine ⟨m, hm, ofLin e hsm g, fun b => ofLin_fst e hsm g b, ?_⟩
  ext b
  · rw [AlgHom.comp_apply, AlgHom.comp_apply, dualMapS_fst, scaleS_fst, ofLin_fst, hh']
    rfl
  · rw [AlgHom.comp_apply, AlgHom.comp_apply, dualMapS_snd, scaleS_snd, ofLin_snd]
    have := LinearMap.congr_fun hg (KaehlerDifferential.D S B b)
    simp only [LinearMap.comp_apply, LinearMap.smul_apply] at this
    refine this.trans ?_
    show (algebraMap S B m) • g' (KaehlerDifferential.D S B b) = _
    rw [hsm', Derivation.liftKaehlerDifferential_comp_D, derOf_apply, AlgHom.commutes, ← IsScalarTower.algebraMap_apply]

/- English proof (translation)
Set `ι` to `IsScalarTower.toAlgHom S A A'`. Set `iA : Module B A` to `Module.compHom A e.toRingHom`. Set `iA' : Module B A'` to `Module.compHom A' (ι.comp e).toRingHom`. Establish `hsm : ∀ (b : B) (a : A), b • a = e b * a` using `fun _ _ => rfl`. Establish `hsm' : ∀ (b : B) (a : A'), b • a = algebraMap A A' (e b) * a` using `fun _ _ => rfl`.

Establish `: IsScalarTower S B A` using `⟨fun r b a => by show e (r • b) * a = r • (e b * a)`. Rewrite using `[map_smul, smul_mul_assoc]⟩`. Set `f : A →ₗ[B] A'` to `{ toFun := algebraMap A A' map_add' := map_add _ map_smul' := fun b a => by show algebraMap A A' (e b * a) = algebraMap A A' (e b) * algebraMap A A' a`. Rewrite using `[map_mul] }`. Use `isLocalizedModule_tan e M hsm hsm' f (fun _ => rfl)` as an intermediate fact.

Set `g₁` to `(derOf e hsm h₁ t₁).liftKaehlerDifferential`. Set `g₂` to `(derOf e hsm h₂ t₂).liftKaehlerDifferential`. Establish `hfg : f.comp g₁ = f.comp g₂`. Apply `Derivation.liftKaehlerDifferential_unique` to reduce the goal to its premises. Use extensionality with `b`.

Use `show f (g₁ (KaehlerDifferential.D S B b)) = f (g₂ (KaehlerDifferential.D S B b))`. Simplify using `only [g₁, g₂, Derivation.liftKaehlerDifferential_comp_D, derOf_apply]`. Use `congrArg TrivSqZeroExt.snd (AlgHom.congr_fun heq b)` as an intermediate fact. Simplify using `only [AlgHom.comp_apply, dualMapS_snd] at this`. Conclude with `this`.

Take `⟨⟨_, ⟨m, hm, rfl⟩⟩, hc⟩` from `Module.Finite.exists_smul_of_comp_eq_of_isLocalizedModule (Algebra.algebraMapSubmonoid B M) f g₁ g₂ hfg`. Use `⟨m, hm, ?_⟩` and prove the remaining obligations. Use extensionality with `b`. Rewrite using `[AlgHom.comp_apply, AlgHom.comp_apply, scaleS_fst, scaleS_fst, t₁, t₂]`. Rewrite using `[AlgHom.comp_apply, AlgHom.comp_apply, scaleS_snd, scaleS_snd]`.

Use `LinearMap.congr_fun hc (KaehlerDifferential.D S B b)` as an intermediate fact. Simplify using `only [LinearMap.smul_apply, g₁, g₂, Derivation.liftKaehlerDifferential_comp_D, derOf_apply] at this`. Express the relevant statement in the definitionally equal form `algebraMap S B m • (h₁ b).snd = algebraMap S B m • (h₂ b).snd at this`. Rewrite `this` using `[hsm, hsm, AlgHom.commutes]`. Then use the resulting hypothesis.
-/
theorem tan_uniq (h₁ h₂ : B →ₐ[S] DualNumber A) (t₁ : IsTanAt e h₁) (t₂ : IsTanAt e h₂)
    (heq : (dualMapS (IsScalarTower.toAlgHom S A A')).comp h₁ = (dualMapS (IsScalarTower.toAlgHom S A A')).comp h₂) :
    ∃ m ∈ M, (scaleS (algebraMap S A m)).comp h₁ = (scaleS (algebraMap S A m)).comp h₂ := by
  let ι := IsScalarTower.toAlgHom S A A'
  let iA : Module B A := Module.compHom A e.toRingHom
  let iA' : Module B A' := Module.compHom A' (ι.comp e).toRingHom
  have hsm : ∀ (b : B) (a : A), b • a = e b * a := fun _ _ => rfl
  have hsm' : ∀ (b : B) (a : A'), b • a = algebraMap A A' (e b) * a := fun _ _ => rfl
  have : IsScalarTower S B A := ⟨fun r b a => by
    show e (r • b) * a = r • (e b * a)
    rw [map_smul, smul_mul_assoc]⟩
  let f : A →ₗ[B] A' :=
    { toFun := algebraMap A A'
      map_add' := map_add _
      map_smul' := fun b a => by
        show algebraMap A A' (e b * a) = algebraMap A A' (e b) * algebraMap A A' a
        rw [map_mul] }
  have := isLocalizedModule_tan e M hsm hsm' f (fun _ => rfl)
  let g₁ := (derOf e hsm h₁ t₁).liftKaehlerDifferential
  let g₂ := (derOf e hsm h₂ t₂).liftKaehlerDifferential
  have hfg : f.comp g₁ = f.comp g₂ := by
    apply Derivation.liftKaehlerDifferential_unique
    ext b
    show f (g₁ (KaehlerDifferential.D S B b)) = f (g₂ (KaehlerDifferential.D S B b))
    simp only [g₁, g₂, Derivation.liftKaehlerDifferential_comp_D, derOf_apply]
    have := congrArg TrivSqZeroExt.snd (AlgHom.congr_fun heq b)
    simp only [AlgHom.comp_apply, dualMapS_snd] at this
    exact this
  obtain ⟨⟨_, ⟨m, hm, rfl⟩⟩, hc⟩ :=
    Module.Finite.exists_smul_of_comp_eq_of_isLocalizedModule (Algebra.algebraMapSubmonoid B M) f g₁ g₂ hfg
  refine ⟨m, hm, ?_⟩
  ext b
  · rw [AlgHom.comp_apply, AlgHom.comp_apply, scaleS_fst, scaleS_fst, t₁, t₂]
  · rw [AlgHom.comp_apply, AlgHom.comp_apply, scaleS_snd, scaleS_snd]
    have := LinearMap.congr_fun hc (KaehlerDifferential.D S B b)
    simp only [LinearMap.smul_apply, g₁, g₂, Derivation.liftKaehlerDifferential_comp_D, derOf_apply] at this
    change algebraMap S B m • (h₁ b).snd = algebraMap S B m • (h₂ b).snd at this
    rwa [hsm, hsm, AlgHom.commutes] at this

end Main

end ReciprocityTheory.ChartRestriction.G.Chart

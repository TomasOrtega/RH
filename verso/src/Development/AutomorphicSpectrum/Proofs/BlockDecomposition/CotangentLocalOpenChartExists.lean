import Mathlib
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.HodgeWedgeFields.H1CommutesBaseChange

open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge

namespace GlobalTheory.CompanionTheory.CotLoc

/- English proof (translation)
Simplify using `only [spMap, CommRingCat.ofHom_comp, Spec.map_comp]`.
-/
theorem spMap_comp' {a b c : Type} [CommRing a] [CommRing b] [CommRing c] (f : a →+* b) (g : b →+* c) :
    spMap (g.comp f) = spMap g ≫ spMap f := by
  simp only [spMap, CommRingCat.ofHom_comp, Spec.map_comp]

/- English proof (translation)
Use `congrArg CommRingCat.Hom.hom (Spec.map_injective h)` as an intermediate fact. Simplify using `using this`.
-/
theorem spMap_injective {a b : Type} [CommRing a] [CommRing b] {f g : a →+* b}
    (h : spMap f = spMap g) : f = g := by
  have := congrArg CommRingCat.Hom.hom (Spec.map_injective h)
  simpa using this

/- English proof (translation)
Establish `hsurj : ∀ p : Sp Q, ∃ p' : Sp R', spMap q p' = p`. Introduce `p`. Establish `: (p : PrimeSpectrum Q) ∈ Set.range (PrimeSpectrum.comap q)`. Rewrite using `[range_comap_of_surjective _ q hq]`. Introduce `x hx`.

Take `⟨n, hn⟩` from `hnil x hx`. Conclude with `p.2.mem_of_pow_mem n (hn ▸ zero_mem _)`. Take `⟨p', hp'⟩` from `this`. Conclude with `⟨p', hp'⟩`. Establish `hr : Set.range y ⊆ Set.range j`.

Introduce and unpack `_ ⟨p, rfl⟩`. Take `⟨p', rfl⟩` from `hsurj p`. Establish `h1 : y (spMap q p') = (spMap q ≫ y) p'` using `by simp`. Rewrite using `[h1, hy]`. Conclude with `⟨spMap ε p', by simp⟩`.

Use `⟨(Spec.preimage (IsOpenImmersion.lift j y hr)).hom, ?_⟩` and prove the remaining obligations. Establish `: spMap (Spec.preimage (IsOpenImmersion.lift j y hr)).hom = IsOpenImmersion.lift j y hr`. Simplify using `[spMap]`. Rewrite using `[this, IsOpenImmersion.lift_fac]`.
-/
theorem landing {X : Scheme.{0}} {A Q R' : Type} [CommRing A] [CommRing Q] [CommRing R']
    (j : Sp A ⟶ X) [IsOpenImmersion j] (ε : A →+* R') (q : Q →+* R')
    (hq : Function.Surjective q) (hnil : ∀ x, q x = 0 → IsNilpotent x)
    (y : Sp Q ⟶ X) (hy : spMap q ≫ y = spMap ε ≫ j) :
    ∃ ψ : A →+* Q, y = spMap ψ ≫ j := by
  have hsurj : ∀ p : Sp Q, ∃ p' : Sp R', spMap q p' = p := by
    intro p
    have : (p : PrimeSpectrum Q) ∈ Set.range (PrimeSpectrum.comap q) := by
      rw [range_comap_of_surjective _ q hq]
      intro x hx
      obtain ⟨n, hn⟩ := hnil x hx
      exact p.2.mem_of_pow_mem n (hn ▸ zero_mem _)
    obtain ⟨p', hp'⟩ := this
    exact ⟨p', hp'⟩
  have hr : Set.range y ⊆ Set.range j := by
    rintro _ ⟨p, rfl⟩
    obtain ⟨p', rfl⟩ := hsurj p
    have h1 : y (spMap q p') = (spMap q ≫ y) p' := by simp
    rw [h1, hy]
    exact ⟨spMap ε p', by simp⟩
  refine ⟨(Spec.preimage (IsOpenImmersion.lift j y hr)).hom, ?_⟩
  have : spMap (Spec.preimage (IsOpenImmersion.lift j y hr)).hom = IsOpenImmersion.lift j y hr := by
    simp [spMap]
  rw [this, IsOpenImmersion.lift_fac]

section Rel

variable {R : Type} [CommRing R] {X : Scheme.{0}} {s : X ⟶ Sp R} {e : Sp R ⟶ X}
  {W : Type} [AddCommGroup W] [Module R W] [Module Rᵐᵒᵖ W] [IsCentralScalar R W]
  {y₀ : Sp (TrivSqZeroExt R W) ⟶ X}
  {R' : Type} [CommRing R'] [Algebra R R'] {A C : Type} [CommRing A] [CommRing C] [Algebra C A]
  [Algebra A R'] {j : Sp A ⟶ X} {k : Sp C ⟶ Sp R}

/- English proof (translation)
Combine the equalities or inequalities in the displayed calculation. Rewrite using `[Category.assoc, hes, Category.comp_id]`. Use `_ = spMap (algebraMap A R') ≫ j ≫ s := by rw [← hje, Category.assoc]`. Use `_ = _ := by rw [hjs, spMap_comp', Category.assoc]`.
-/
theorem base_eq (hes : e ≫ s = 𝟙 _) (hjs : j ≫ s = spMap (algebraMap C A) ≫ k)
    (hje : spMap (algebraMap A R') ≫ j = spMap (algebraMap R R') ≫ e) :
    spMap (algebraMap R R') = spMap ((algebraMap A R').comp (algebraMap C A)) ≫ k := by
  calc spMap (algebraMap R R') = (spMap (algebraMap R R') ≫ e) ≫ s := by
        rw [Category.assoc, hes, Category.comp_id]
    _ = spMap (algebraMap A R') ≫ j ≫ s := by rw [← hje, Category.assoc]
    _ = _ := by rw [hjs, spMap_comp', Category.assoc]

variable {M : Type} [AddCommGroup M] [Module R' M] [Module R'ᵐᵒᵖ M] [IsCentralScalar R' M]
  [Module R M] [IsScalarTower R R' M]

def Good (ψ : A →+* TrivSqZeroExt R' M) : Prop :=
  (TrivSqZeroExt.fstHom R' R' M).toRingHom.comp ψ = algebraMap A R' ∧
    ψ.comp (algebraMap C A) =
      (TrivSqZeroExt.inlHom R' M).comp ((algebraMap A R').comp (algebraMap C A))

/- English proof (translation)
Apply the tactic sequence `ext x <;> simp [tsz]`.
-/
theorem fst_tsz (u : W →ₗ[R] M) :
    (TrivSqZeroExt.fstHom R' R' M).toRingHom.comp (tsz u) =
      (algebraMap R R').comp (TrivSqZeroExt.fstHom R R W).toRingHom := by
  ext x <;> simp [tsz]

/- English proof (translation)
Apply the tactic sequence `ext x <;> simp [tsz]`.
-/
theorem tsz_inl (u : W →ₗ[R] M) :
    (tsz u).comp (TrivSqZeroExt.inlHom R W) =
      (TrivSqZeroExt.inlHom R' M).comp (algebraMap R R') := by
  ext x <;> simp [tsz]

/- English proof (translation)
Use `hcot.2.2 R' M (spMap ψ ≫ j) ?_ ?_` and prove the remaining obligations. Rewrite using `[Category.assoc, hjs, ← Category.assoc, ← spMap_comp', hψ.2, spMap_comp', Category.assoc, ← base_eq hes hjs hje, ← spMap_comp']`. Rewrite using `[← Category.assoc, ← spMap_comp', hψ.1, hje]`.
-/
theorem exists_unique_of_good (hcot : IsCot s e W y₀) (hes : e ≫ s = 𝟙 _)
    (hjs : j ≫ s = spMap (algebraMap C A) ≫ k)
    (hje : spMap (algebraMap A R') ≫ j = spMap (algebraMap R R') ≫ e)
    (ψ : A →+* TrivSqZeroExt R' M) (hψ : Good (C := C) ψ) :
    ∃! u : W →ₗ[R] M, spMap ψ ≫ j = spMap (tsz u) ≫ y₀ := by
  refine hcot.2.2 R' M (spMap ψ ≫ j) ?_ ?_
  · rw [Category.assoc, hjs, ← Category.assoc, ← spMap_comp', hψ.2, spMap_comp', Category.assoc,
      ← base_eq hes hjs hje, ← spMap_comp']
  · rw [← Category.assoc, ← spMap_comp', hψ.1, hje]

/- English proof (translation)
Establish `hy : spMap (TrivSqZeroExt.fstHom R' R' M).toRingHom ≫ spMap (tsz u) ≫ y₀ = spMap (algebraMap A R') ≫ j`. Rewrite using `[← Category.assoc, ← spMap_comp', fst_tsz, spMap_comp', Category.assoc, hcot.2.1, hje]`. Take `⟨ψ, hψ⟩` from `landing j (algebraMap A R') (TrivSqZeroExt.fstHom R' R' M).toRingHom (fun x => ⟨TrivSqZeroExt.inl x, by simp⟩) (fun x hx => ⟨2, by`. Establish `hx' : x.fst = 0` using `hx`. Apply the tactic sequence `ext <;> simp [pow_two, hx']⟩) _ hy`.

Use `⟨ψ, ⟨?_, ?_⟩, hψ.symm⟩` and prove the remaining obligations. Apply `spMap_injective` to reduce the goal to its premises. Rewrite using `[← cancel_mono j, spMap_comp', Category.assoc, ← hψ, hy]`. Apply `spMap_injective` to reduce the goal to its premises. Rewrite using `[← cancel_mono k, spMap_comp', Category.assoc, ← hjs, ← Category.assoc (spMap ψ), ← hψ, Category.assoc, hcot.1, ← spMap_comp', tsz_inl, spMap_comp' (algebraMap R R'), base_eq hes hjs hje, spMap_comp' ((algebraMap A R').comp (algebraMap C A)), Category.assoc]`.
-/
theorem exists_good (hcot : IsCot s e W y₀) (hes : e ≫ s = 𝟙 _)
    [IsOpenImmersion j] [Mono k]
    (hjs : j ≫ s = spMap (algebraMap C A) ≫ k)
    (hje : spMap (algebraMap A R') ≫ j = spMap (algebraMap R R') ≫ e)
    (u : W →ₗ[R] M) :
    ∃ ψ : A →+* TrivSqZeroExt R' M, Good (C := C) ψ ∧ spMap ψ ≫ j = spMap (tsz u) ≫ y₀ := by
  have hy : spMap (TrivSqZeroExt.fstHom R' R' M).toRingHom ≫ spMap (tsz u) ≫ y₀ =
      spMap (algebraMap A R') ≫ j := by
    rw [← Category.assoc, ← spMap_comp', fst_tsz, spMap_comp', Category.assoc, hcot.2.1, hje]
  obtain ⟨ψ, hψ⟩ := landing j (algebraMap A R') (TrivSqZeroExt.fstHom R' R' M).toRingHom
    (fun x => ⟨TrivSqZeroExt.inl x, by simp⟩)
    (fun x hx => ⟨2, by
      have hx' : x.fst = 0 := hx
      ext <;> simp [pow_two, hx']⟩) _ hy
  refine ⟨ψ, ⟨?_, ?_⟩, hψ.symm⟩
  · apply spMap_injective
    rw [← cancel_mono j, spMap_comp', Category.assoc, ← hψ, hy]
  · apply spMap_injective
    rw [← cancel_mono k, spMap_comp', Category.assoc, ← hjs, ← Category.assoc (spMap ψ), ← hψ,
      Category.assoc, hcot.1, ← spMap_comp', tsz_inl, spMap_comp' (algebraMap R R'), base_eq hes hjs hje,
      spMap_comp' ((algebraMap A R').comp (algebraMap C A)), Category.assoc]

variable {N : Type} [AddCommGroup N] [Module R' N] [Module R'ᵐᵒᵖ N] [IsCentralScalar R' N]
  [Module R N] [IsScalarTower R R' N]

/- English proof (translation)
Apply the tactic sequence `ext x <;> simp [tsz]`.
-/
theorem tsz_comp (u : W →ₗ[R] M) (v : M →ₗ[R'] N) :
    (tsz (R := R') (B := R') v).comp (tsz u) = tsz ((v.restrictScalars R).comp u) := by
  ext x <;> simp [tsz]

/- English proof (translation)
Rewrite using `[spMap_comp', Category.assoc, h, ← tsz_comp, spMap_comp', Category.assoc]`.
-/
theorem rel_comp {ψ : A →+* TrivSqZeroExt R' M} {u : W →ₗ[R] M} (v : M →ₗ[R'] N)
    (h : spMap ψ ≫ j = spMap (tsz u) ≫ y₀) :
    spMap ((tsz (R := R') (B := R') v).comp ψ) ≫ j =
      spMap (tsz ((v.restrictScalars R).comp u)) ≫ y₀ := by
  rw [spMap_comp', Category.assoc, h, ← tsz_comp, spMap_comp', Category.assoc]

/- English proof (translation)
Apply the tactic sequence `ext x <;> simp [tsz]`.
-/
theorem tsz_id_comp (ψ : A →+* TrivSqZeroExt R' M) :
    (tsz (R := R') (B := R') (LinearMap.id : M →ₗ[R'] M)).comp ψ = ψ := by
  ext x <;> simp [tsz]

/- English proof (translation)
Take `⟨ψ₀, g₀, r₀⟩` from `exists_good (M := N) hcot hes hjs hje iW`. Take `⟨u₁, r₁, -⟩` from `exists_unique_of_good (M := M) hcot hes hjs hje ψ₁ h₁`. Take `⟨u', hu'⟩` from `extW u₁`. Take `⟨v, hv⟩` from `extM ψ₀ g₀`. Establish `ha : (v.restrictScalars R).comp u₁ = iW` using `(exists_unique_of_good (M := N) hcot hes hjs hje ψ₀ g₀).unique (by rw [← hv]; exact rel_comp v r₁) r₀`.

Establish `hb : (tsz (R` using `R') (B := R') u').comp ψ₀ = ψ₁ := by`. Apply `spMap_injective` to reduce the goal to its premises. Rewrite using `[← cancel_mono j, rel_comp u' r₀, hu', r₁]`. Establish `h1 : v.comp u' = LinearMap.id`. Apply `uniqW` to reduce the goal to its premises.

Use extensionality with `w`. Use `congrArg (fun f => f w) ha` as an intermediate fact. Establish `h2` using `congrArg (fun f => f w) hu'`. Simplify using `only [LinearMap.comp_apply, LinearMap.restrictScalars_apply] at this h2 ⊢`. Rewrite using `[h2, this]`.

Both sides reduce to the same expression. Establish `h2 : u'.comp v = LinearMap.id`. Apply `uniqM` to reduce the goal to its premises. Rewrite using `[tsz_id_comp]`. Use `tsz_comp (R := R') (R' := R') v u'` as an intermediate fact.

Rewrite `this` using `[LinearMap.restrictScalars_self]`. Rewrite using `[← this, RingHom.comp_assoc, hv, hb]`. Conclude with `⟨LinearEquiv.ofLinear u' v h2 h1⟩`.
-/
theorem equiv_of_universal (hcot : IsCot s e W y₀) (hes : e ≫ s = 𝟙 _)
    [IsOpenImmersion j] [Mono k]
    (hjs : j ≫ s = spMap (algebraMap C A) ≫ k)
    (hje : spMap (algebraMap A R') ≫ j = spMap (algebraMap R R') ≫ e)
    (iW : W →ₗ[R] N) (ψ₁ : A →+* TrivSqZeroExt R' M) (h₁ : Good (C := C) ψ₁)
    (extW : ∀ u : W →ₗ[R] M, ∃ u' : N →ₗ[R'] M, (u'.restrictScalars R).comp iW = u)
    (extM : ∀ ψ : A →+* TrivSqZeroExt R' N, Good (C := C) ψ →
      ∃ v : M →ₗ[R'] N, (tsz (R := R') (B := R') v).comp ψ₁ = ψ)
    (uniqW : ∀ f g : N →ₗ[R'] N, (f.restrictScalars R).comp iW = (g.restrictScalars R).comp iW → f = g)
    (uniqM : ∀ f g : M →ₗ[R'] M, (tsz (R := R') (B := R') f).comp ψ₁ =
      (tsz (R := R') (B := R') g).comp ψ₁ → f = g) :
    Nonempty (N ≃ₗ[R'] M) := by
  obtain ⟨ψ₀, g₀, r₀⟩ := exists_good (M := N) hcot hes hjs hje iW
  obtain ⟨u₁, r₁, -⟩ := exists_unique_of_good (M := M) hcot hes hjs hje ψ₁ h₁
  obtain ⟨u', hu'⟩ := extW u₁
  obtain ⟨v, hv⟩ := extM ψ₀ g₀
  have ha : (v.restrictScalars R).comp u₁ = iW :=
    (exists_unique_of_good (M := N) hcot hes hjs hje ψ₀ g₀).unique
      (by rw [← hv]; exact rel_comp v r₁) r₀
  have hb : (tsz (R := R') (B := R') u').comp ψ₀ = ψ₁ := by
    apply spMap_injective
    rw [← cancel_mono j, rel_comp u' r₀, hu', r₁]
  have h1 : v.comp u' = LinearMap.id := by
    apply uniqW
    ext w
    have := congrArg (fun f => f w) ha
    have h2 := congrArg (fun f => f w) hu'
    simp only [LinearMap.comp_apply, LinearMap.restrictScalars_apply] at this h2 ⊢
    rw [h2, this]
    rfl
  have h2 : u'.comp v = LinearMap.id := by
    apply uniqM
    rw [tsz_id_comp]
    have := tsz_comp (R := R') (R' := R') v u'
    rw [LinearMap.restrictScalars_self] at this
    rw [← this, RingHom.comp_assoc, hv, hb]
  exact ⟨LinearEquiv.ofLinear u' v h2 h1⟩

def phiOf (d : A →+ M)
    (hm : ∀ a b, d (a * b) = algebraMap A R' a • d b + algebraMap A R' b • d a) :
    A →+* TrivSqZeroExt R' M where
  toFun a := TrivSqZeroExt.inl (algebraMap A R' a) + TrivSqZeroExt.inr (d a)
  map_one' := by
    have h1 : d 1 = 0 := by simpa using hm 1 1
    ext <;> simp [h1]
  map_zero' := by ext <;> simp
  map_add' a b := by ext <;> simp
  map_mul' a b := by ext <;> simp [hm, add_comm]

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Use extensionality with `a`. Simplify using `[phiOf]`. Apply the tactic sequence `ext c <;> simp [phiOf, hc]`.
-/
theorem phiOf_good (d : A →+ M)
    (hm : ∀ a b, d (a * b) = algebraMap A R' a • d b + algebraMap A R' b • d a)
    (hc : ∀ c : C, d (algebraMap C A c) = 0) : Good (C := C) (phiOf d hm) := by
  constructor
  · ext a; simp [phiOf]
  · ext c <;> simp [phiOf, hc]

/- English proof (translation)
Use `letI : Module A M := Module.compHom M (algebraMap A R')`. Use `haveI : IsScalarTower A R' M := IsScalarTower.of_algebraMap_smul fun _ _ => rfl`. Use `letI : Module C M := Module.compHom M ((algebraMap A R').comp (algebraMap C A))`. Use `haveI : IsScalarTower C A M := IsScalarTower.of_algebraMap_smul fun _ _ => rfl`. Establish `hfst : ∀ a, (ψ a).fst = algebraMap A R' a` using `fun a => congrArg (fun f => f a) hψ.1`.

Establish `hC : ∀ c, ψ (algebraMap C A c) = TrivSqZeroExt.inl (algebraMap A R' (algebraMap C A c))` using `fun c => congrArg (fun f => f c) hψ.2`. Set `l : A →ₗ[C] M` to `{ toFun := fun a => (ψ a).snd map_add' := fun a b => by simp map_smul' := fun c a => by`. Rewrite using `[Algebra.smul_def, map_mul, hC]`. Simplify using `}`. Set `d : Derivation C A M` to `Derivation.mk' l (fun a b => by show (ψ (a * b)).snd = a • (ψ b).snd + b • (ψ a).snd`.

Rewrite using `[map_mul, TrivSqZeroExt.snd_mul, hfst, hfst, op_smul_eq_smul]`. Use the proof step `rfl)`. Use `⟨d.liftKaehlerDifferential.liftBaseChange R', fun a => ?_⟩` and prove the remaining obligations. Rewrite using `[LinearMap.liftBaseChange_tmul, one_smul, Derivation.liftKaehlerDifferential_comp_D]`. Both sides reduce to the same expression.
-/
theorem exists_lift (ψ : A →+* TrivSqZeroExt R' M) (hψ : Good (C := C) ψ) :
    ∃ v : (R' ⊗[A] KaehlerDifferential C A) →ₗ[R'] M,
      ∀ a, v (1 ⊗ₜ KaehlerDifferential.D C A a) = (ψ a).snd := by
  letI : Module A M := Module.compHom M (algebraMap A R')
  haveI : IsScalarTower A R' M := IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  letI : Module C M := Module.compHom M ((algebraMap A R').comp (algebraMap C A))
  haveI : IsScalarTower C A M := IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  have hfst : ∀ a, (ψ a).fst = algebraMap A R' a := fun a => congrArg (fun f => f a) hψ.1
  have hC : ∀ c, ψ (algebraMap C A c) =
      TrivSqZeroExt.inl (algebraMap A R' (algebraMap C A c)) := fun c => congrArg (fun f => f c) hψ.2
  let l : A →ₗ[C] M :=
    { toFun := fun a => (ψ a).snd
      map_add' := fun a b => by simp
      map_smul' := fun c a => by
        rw [Algebra.smul_def, map_mul, hC]
        simp }
  let d : Derivation C A M := Derivation.mk' l (fun a b => by
    show (ψ (a * b)).snd = a • (ψ b).snd + b • (ψ a).snd
    rw [map_mul, TrivSqZeroExt.snd_mul, hfst, hfst, op_smul_eq_smul]
    rfl)
  refine ⟨d.liftKaehlerDifferential.liftBaseChange R', fun a => ?_⟩
  rw [LinearMap.liftBaseChange_tmul, one_smul, Derivation.liftKaehlerDifferential_comp_D]
  rfl

end Rel

section Final

@[reducible] def opAct (B M : Type) [CommRing B] [AddCommGroup M] [Module B M] : Module Bᵐᵒᵖ M :=
  Module.compHom M ((RingHom.id B).fromOpposite (fun x y => mul_comm x y))

/- English proof (translation)
The claim follows from `letI := opAct B M ⟨fun _ _ => rfl⟩`.
-/
theorem opAct_central (B M : Type) [CommRing B] [AddCommGroup M] [Module B M] :
    letI := opAct B M
    IsCentralScalar B M :=
  letI := opAct B M
  ⟨fun _ _ => rfl⟩

/- English proof (translation)
The claim follows from `letI := Module.compHom P (algebraMap R R') IsScalarTower.of_algebraMap_smul fun _ _ => rfl`.
-/
theorem compHom_tower (R R' P : Type) [CommRing R] [CommRing R'] [Algebra R R'] [AddCommGroup P]
    [Module R' P] :
    letI := Module.compHom P (algebraMap R R')
    IsScalarTower R R' P :=
  letI := Module.compHom P (algebraMap R R')
  IsScalarTower.of_algebraMap_smul fun _ _ => rfl

/- English proof (translation)
Use `LinearMap.ext fun x => ?_` and prove the remaining obligations. Proceed by induction on `x using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `tmul r w`. Establish `: r ⊗ₜ[R] w = r • ((1 : R') ⊗ₜ[R] w)` using `by simp [TensorProduct.smul_tmul']`.

Rewrite using `[this, map_smul, map_smul, h]`. Consider the case `add x y hx hy => simp [hx, hy]`.
-/
theorem tensor_ext {R R' W N : Type} [CommRing R] [CommRing R'] [Algebra R R'] [AddCommGroup W]
    [Module R W] [AddCommGroup N] [Module R' N] {f g : (R' ⊗[R] W) →ₗ[R'] N}
    (h : ∀ w, f (1 ⊗ₜ w) = g (1 ⊗ₜ w)) : f = g := by
  refine LinearMap.ext fun x => ?_
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul r w =>
    have : r ⊗ₜ[R] w = r • ((1 : R') ⊗ₜ[R] w) := by simp [TensorProduct.smul_tmul']
    rw [this, map_smul, map_smul, h]
  | add x y hx hy => simp [hx, hy]

/- English proof (translation)
Rewrite using `[TensorProduct.tmul_smul, Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul', TensorProduct.smul_tmul', smul_eq_mul, _root_.mul_one]`.
-/
theorem one_tmul_smul {R' A P : Type} [CommRing R'] [CommRing A] [Algebra A R'] [AddCommGroup P]
    [Module A P] (a : A) (x : P) :
    (1 : R') ⊗ₜ[A] (a • x) = algebraMap A R' a • ((1 : R') ⊗ₜ[A] x) := by
  rw [TensorProduct.tmul_smul, Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul',
    TensorProduct.smul_tmul', smul_eq_mul, _root_.mul_one]

/- English proof (translation)
Establish `key : ∀ x ∈ Submodule.span A (Set.range (KaehlerDifferential.D C A)), f (1 ⊗ₜ x) = g (1 ⊗ₜ x)`. Introduce `x hx`. Proceed by induction on `hx using Submodule.span_induction with`. Consider the case `mem x hx => obtain ⟨a, rfl⟩ := hx`. Conclude with `h a`.

Consider the case `zero => simp`. Consider the case `add x y _ _ hx hy => simp [TensorProduct.tmul_add, hx, hy]`. Consider the case `smul a x _ hx`. Rewrite using `[one_tmul_smul, map_smul, map_smul, hx]`. Use `tensor_ext fun x => key x ?_` and prove the remaining obligations.

Rewrite using `[KaehlerDifferential.span_range_derivation]`. Discharge the goal by the elementary cases of `trivial`.
-/
theorem kaehler_ext {R' A C N : Type} [CommRing R'] [CommRing A] [CommRing C] [Algebra C A]
    [Algebra A R'] [AddCommGroup N] [Module R' N]
    {f g : (R' ⊗[A] KaehlerDifferential C A) →ₗ[R'] N}
    (h : ∀ a, f (1 ⊗ₜ KaehlerDifferential.D C A a) = g (1 ⊗ₜ KaehlerDifferential.D C A a)) :
    f = g := by
  have key : ∀ x ∈ Submodule.span A (Set.range (KaehlerDifferential.D C A)),
      f (1 ⊗ₜ x) = g (1 ⊗ₜ x) := by
    intro x hx
    induction hx using Submodule.span_induction with
    | mem x hx => obtain ⟨a, rfl⟩ := hx; exact h a
    | zero => simp
    | add x y _ _ hx hy => simp [TensorProduct.tmul_add, hx, hy]
    | smul a x _ hx =>
      rw [one_tmul_smul, map_smul, map_smul, hx]
  refine tensor_ext fun x => key x ?_
  rw [KaehlerDifferential.span_range_derivation]
  trivial

/- English proof (translation)
Use `letI := opAct R' (R' ⊗[R] W)`. Use `haveI := opAct_central R' (R' ⊗[R] W)`. Use `letI := opAct R' P`. Use `haveI := opAct_central R' P`. Use `letI : Module R P := Module.compHom _ (algebraMap R R')`.

Use `haveI : IsScalarTower R R' P := compHom_tower R R' P`. Set `d : A →+ P` to `{ toFun := fun a => eP ((1 : R') ⊗ₜ[A] KaehlerDifferential.D C A a) map_zero' := by simp map_add' := fun a b => by simp [TensorProduct.tmul_add] }`. Establish `hd : ∀ a, d a = eP ((1 : R') ⊗ₜ[A] KaehlerDifferential.D C A a)` using `fun _ => rfl`. Establish `hm : ∀ a b, d (a * b) = algebraMap A R' a • d b + algebraMap A R' b • d a`. Introduce `a b`.

Simplify using `only [hd, Derivation.leibniz, TensorProduct.tmul_add, one_tmul_smul, map_add, map_smul]`. Establish `hc : ∀ c : C, d (algebraMap C A c) = 0`. Introduce `c`. Simplify using `[hd]`. Use `equiv_of_universal hcot hes hjs hje (TensorProduct.mk R R' W 1) (phiOf d hm) (phiOf_good d hm hc) ?_ ?_ ?_ ?_` and prove the remaining obligations.

Introduce `u`. Use `⟨u.liftBaseChange R', ?_⟩` and prove the remaining obligations. Use extensionality with `w`. Simplify using the standard rewrite rules. Introduce `ψ hψ`.

Take `⟨v, hv⟩` from `exists_lift ψ hψ`. Use `⟨v ∘ₗ eP.symm.toLinearMap, RingHom.ext fun a => TrivSqZeroExt.ext ?_ ?_⟩` and prove the remaining obligations. Use `congrArg (fun f => f a) hψ.1` as an intermediate fact. Simplify `this.symm` using `[tsz, phiOf]`. Use `hv a` as an intermediate fact.

Simplify `this` using `[tsz, phiOf, hd]`. Introduce `f g h`. Conclude with `tensor_ext fun w => congrArg (fun f => f w) h`. Introduce `f g h`. Establish `key : f ∘ₗ eP.toLinearMap = g ∘ₗ eP.toLinearMap`.

Use `kaehler_ext fun a => ?_` and prove the remaining obligations. Use `congrArg (fun F => (F a).snd) h` as an intermediate fact. Simplify `this` using `[tsz, phiOf, hd]`. Use `LinearMap.ext fun x => ?_` and prove the remaining obligations. Use `congrArg (fun F => F (eP.symm x)) key` as an intermediate fact.

Simplify using `using this`.
-/
theorem equiv_general {R : Type} [CommRing R] {X : Scheme.{0}} {s : X ⟶ Sp R} {e : Sp R ⟶ X}
    (hes : e ≫ s = 𝟙 _) {W : Type} [AddCommGroup W] [Module R W] [Module Rᵐᵒᵖ W]
    [IsCentralScalar R W] {y₀ : Sp (TrivSqZeroExt R W) ⟶ X} (hcot : IsCot s e W y₀)
    {R' : Type} [CommRing R'] [Algebra R R'] {A C : Type} [CommRing A] [CommRing C] [Algebra C A]
    [Algebra A R'] {j : Sp A ⟶ X} {k : Sp C ⟶ Sp R} [IsOpenImmersion j] [Mono k]
    (hjs : j ≫ s = spMap (algebraMap C A) ≫ k)
    (hje : spMap (algebraMap A R') ≫ j = spMap (algebraMap R R') ≫ e)
    {P : Type} [AddCommGroup P] [Module R' P] (eP : (R' ⊗[A] KaehlerDifferential C A) ≃ₗ[R'] P) :
    Nonempty ((R' ⊗[R] W) ≃ₗ[R'] P) := by
  letI := opAct R' (R' ⊗[R] W)
  haveI := opAct_central R' (R' ⊗[R] W)
  letI := opAct R' P
  haveI := opAct_central R' P
  letI : Module R P := Module.compHom _ (algebraMap R R')
  haveI : IsScalarTower R R' P := compHom_tower R R' P
  let d : A →+ P :=
    { toFun := fun a => eP ((1 : R') ⊗ₜ[A] KaehlerDifferential.D C A a)
      map_zero' := by simp
      map_add' := fun a b => by simp [TensorProduct.tmul_add] }
  have hd : ∀ a, d a = eP ((1 : R') ⊗ₜ[A] KaehlerDifferential.D C A a) := fun _ => rfl
  have hm : ∀ a b, d (a * b) = algebraMap A R' a • d b + algebraMap A R' b • d a := by
    intro a b
    simp only [hd, Derivation.leibniz, TensorProduct.tmul_add, one_tmul_smul, map_add, map_smul]
  have hc : ∀ c : C, d (algebraMap C A c) = 0 := by
    intro c
    simp [hd]
  refine equiv_of_universal hcot hes hjs hje (TensorProduct.mk R R' W 1) (phiOf d hm)
    (phiOf_good d hm hc) ?_ ?_ ?_ ?_
  · intro u
    refine ⟨u.liftBaseChange R', ?_⟩
    ext w
    simp
  · intro ψ hψ
    obtain ⟨v, hv⟩ := exists_lift ψ hψ
    refine ⟨v ∘ₗ eP.symm.toLinearMap, RingHom.ext fun a => TrivSqZeroExt.ext ?_ ?_⟩
    · have := congrArg (fun f => f a) hψ.1
      simpa [tsz, phiOf] using this.symm
    · have := hv a
      simpa [tsz, phiOf, hd] using this
  · intro f g h
    exact tensor_ext fun w => congrArg (fun f => f w) h
  · intro f g h
    have key : f ∘ₗ eP.toLinearMap = g ∘ₗ eP.toLinearMap := by
      refine kaehler_ext fun a => ?_
      have := congrArg (fun F => (F a).snd) h
      simpa [tsz, phiOf, hd] using this
    refine LinearMap.ext fun x => ?_
    have := congrArg (fun F => F (eP.symm x)) key
    simpa using this

end Final

/- English proof (translation)
Introduce `R _ X s e hes W _ _ _ _ y₀ hcot r A C _ _ _ _ j k _ _ hjs hje`. Conclude with `equiv_general hes hcot hjs hje (LinearEquiv.refl _ _)`.
-/
theorem cotangent_away : ∀ (R : Type) [CommRing R] (X : Scheme.{0}) (s : X ⟶ Sp R) (e : Sp R ⟶ X), e ≫ s = 𝟙 _ → ∀ (W : Type) [AddCommGroup W] [Module R W] [Module Rᵐᵒᵖ W] [IsCentralScalar R W] (y₀ : Sp (TrivSqZeroExt R W) ⟶ X), IsCot s e W y₀ → ∀ (r : R) (A C : Type) [CommRing A] [CommRing C] [Algebra C A] [Algebra A (Localization.Away r)] (j : Sp A ⟶ X) (k : Sp C ⟶ Sp R) [IsOpenImmersion j] [Mono k], j ≫ s = spMap (algebraMap C A) ≫ k → spMap (algebraMap A (Localization.Away r)) ≫ j = spMap (algebraMap R (Localization.Away r)) ≫ e → Nonempty ((Localization.Away r ⊗[R] W) ≃ₗ[Localization.Away r] (Localization.Away r ⊗[A] KaehlerDifferential C A)) := by
  intro R _ X s e hes W _ _ _ _ y₀ hcot r A C _ _ _ _ j k _ _ hjs hje
  exact equiv_general hes hcot hjs hje (LinearEquiv.refl _ _)

end GlobalTheory.CompanionTheory.CotLoc

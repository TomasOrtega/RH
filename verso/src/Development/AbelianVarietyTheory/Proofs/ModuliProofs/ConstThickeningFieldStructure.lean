import Mathlib
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsInvDer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaUnifAV
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct ContDiff
open GlobalTheory.KS

noncomputable section

namespace GlobalTheory.ConstThickening

/- English proof (translation)
Set `_ : Algebra K A` to `c.toAlgebra`. Set `_ : Algebra A A'` to `p.hom.toAlgebra`. Set `_ : Algebra (DualNumber K) A'` to `s.toAlgebra`. Set `_ : Algebra K A'` to `(s.comp (algebraMap K (DualNumber K))).toAlgebra`. Establish `: IsScalarTower K (DualNumber K) A'` using `.of_algebraMap_eq fun _ => rfl`.

Establish `: IsScalarTower K A A'` using `.of_algebraMap_eq fun r => (congrArg (fun q => q.hom r) H.w).symm`. Establish `h : Algebra.IsPushout K A (DualNumber K) A'` using `CommRingCat.isPushout_iff_isPushout.mp H`. Set `b : Module.Basis (Fin 2) K (DualNumber K)` to `Module.Basis.finTwoProd K`. Establish `b0 : b 0 = 1` using `Module.Basis.finTwoProd_zero K`. Establish `b1 : b 1 = DualNumber.eps` using `Module.Basis.finTwoProd_one K`.

Set `B` to `h.out.basis b`. Establish `B0 : B 0 = 1`. Rewrite using `[h.out.basis_apply, b0]`. Conclude with `map_one s`. Establish `B1 : B 1 = s DualNumber.eps`.

Rewrite using `[h.out.basis_apply, b1]`. Both sides reduce to the same expression. Establish `key : ∀ x y : A, p.hom x + s DualNumber.eps * p.hom y = B.equivFun.symm ![x, y]` using `fun x y => by`. Rewrite using `[Module.Basis.equivFun_symm_apply, Fin.sum_univ_two, B0, B1, Algebra.smul_def, Algebra.smul_def, _root_.mul_one, _root_.mul_comm (s _)]`. Both sides reduce to the same expression.

Use `⟨(B.equivFun F 0, B.equivFun F 1), ?_, fun ab hab => ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `F = _`. Rewrite using `[key, LinearEquiv.eq_symm_apply]`. Apply the tactic sequence `ext i; fin_cases i <;> rfl`. Use `replace hab : F = _ := hab`.

Rewrite `hab` using `[key, LinearEquiv.eq_symm_apply]`. Rewrite using `[hab]`. Both sides reduce to the same expression.
-/
theorem existsUnique_of_isPushout {K : Type} [Field K] {A A' : CommRingCat.{0}} (c : K →+* A) (p : A ⟶ A')
    (s : DualNumber K →+* A')
    (H : IsPushout (CommRingCat.ofHom c) (CommRingCat.ofHom (algebraMap K (DualNumber K))) p (CommRingCat.ofHom s))
    (F : A') : ∃! ab : A × A, F = p.hom ab.1 + s DualNumber.eps * p.hom ab.2 := by
  let _ : Algebra K A := c.toAlgebra
  let _ : Algebra A A' := p.hom.toAlgebra
  let _ : Algebra (DualNumber K) A' := s.toAlgebra
  let _ : Algebra K A' := (s.comp (algebraMap K (DualNumber K))).toAlgebra
  have : IsScalarTower K (DualNumber K) A' := .of_algebraMap_eq fun _ => rfl
  have : IsScalarTower K A A' := .of_algebraMap_eq fun r => (congrArg (fun q => q.hom r) H.w).symm
  have h : Algebra.IsPushout K A (DualNumber K) A' := CommRingCat.isPushout_iff_isPushout.mp H
  let b : Module.Basis (Fin 2) K (DualNumber K) := Module.Basis.finTwoProd K
  have b0 : b 0 = 1 := Module.Basis.finTwoProd_zero K
  have b1 : b 1 = DualNumber.eps := Module.Basis.finTwoProd_one K
  let B := h.out.basis b
  have B0 : B 0 = 1 := by
    rw [h.out.basis_apply, b0]; exact map_one s
  have B1 : B 1 = s DualNumber.eps := by
    rw [h.out.basis_apply, b1]; rfl
  have key : ∀ x y : A, p.hom x + s DualNumber.eps * p.hom y = B.equivFun.symm ![x, y] := fun x y => by
    rw [Module.Basis.equivFun_symm_apply, Fin.sum_univ_two, B0, B1, Algebra.smul_def, Algebra.smul_def, _root_.mul_one,
      _root_.mul_comm (s _)]
    rfl
  refine ⟨(B.equivFun F 0, B.equivFun F 1), ?_, fun ab hab => ?_⟩
  · change F = _
    rw [key, LinearEquiv.eq_symm_apply]
    ext i; fin_cases i <;> rfl
  · replace hab : F = _ := hab
    rw [key, LinearEquiv.eq_symm_apply] at hab
    rw [hab]; rfl

variable {K : Type} [Field K] {Y Y' : Scheme.{0}} {q : Y ⟶ Sp K} {π : Y' ⟶ Sp (DualNumber K)} {ρ : Y' ⟶ Y}

def constHom {R : Type} [CommRing R] {X : Scheme.{0}} (f : X ⟶ Sp R) (U : X.Opens) : R →+* Γ(X, U) :=
  (f.appLE ⊤ U (fun _ _ => trivial)).hom.comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom

/- English proof (translation)
Conclude with `congrArg (fun g => g.hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom a)) (f.appLE_map (U := ⊤) (fun _ _ => trivial) (homOfLE h).op)`.
-/
theorem res_constFn {R : Type} [CommRing R] {X : Scheme.{0}} (f : X ⟶ Sp R) {U V : X.Opens} (h : V ≤ U) (a : R) :
    (X.presheaf.map (homOfLE h).op).hom (constFn f U a) = constFn f V a := by
  exact congrArg (fun g => g.hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom a))
    (f.appLE_map (U := ⊤) (fun _ _ => trivial) (homOfLE h).op)

/- English proof (translation)
Rewrite using `[← CommRingCat.comp_apply, ← CommRingCat.comp_apply, Scheme.Hom.naturality]`. Both sides reduce to the same expression.
-/
theorem res_app {X X' : Scheme.{0}} (f : X' ⟶ X) {U V : X.Opens} (h : V ≤ U) (h' : f ⁻¹ᵁ V ≤ f ⁻¹ᵁ U) (a : Γ(X, U)) :
    (X'.presheaf.map (homOfLE h').op).hom ((f.app U).hom a) = (f.app V).hom ((X.presheaf.map (homOfLE h).op).hom a) := by
  rw [← CommRingCat.comp_apply, ← CommRingCat.comp_apply, Scheme.Hom.naturality]
  rfl

/- English proof (translation)
Rewrite using `[← CommRingCat.comp_apply, ← Functor.map_comp]`. Both sides reduce to the same expression.
-/
theorem res_res {X : Scheme.{0}} {U V W : X.Opens} (h : V ≤ U) (h' : W ≤ V) (a : Γ(X, U)) :
    (X.presheaf.map (homOfLE h').op).hom ((X.presheaf.map (homOfLE h).op).hom a) =
      (X.presheaf.map (homOfLE (h'.trans h)).op).hom a := by
  rw [← CommRingCat.comp_apply, ← Functor.map_comp]
  rfl

/- English proof (translation)
Use `existsUnique_of_isPushout (constHom q U) (ρ.app U) (constHom π (ρ ⁻¹ᵁ U)) ?_ F` and prove the remaining obligations. Establish `po` using `(isIso_pushoutSection_iff H (US := ⊤) (UT := ⊤) (UX := U) (UY := ρ ⁻¹ᵁ U) le_top le_top (by simp)).mp (isIso_pushoutSection_of_isAffineOpen H _ _ _ (isAffineOpen_top _) (isAffineOpen_top _) hU)`. Use `po.of_iso (Scheme.ΓSpecIso (.of K)) (Iso.refl _) (Scheme.ΓSpecIso (.of (DualNumber K))) (Iso.refl _) ?_ ?_ ?_ ?_` and prove the remaining obligations. Use extensionality with `x`. Simplify using `[constHom]`.

Rewrite using `[← Scheme.ΓSpecIso_naturality, Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE]`. Both sides reduce to the same expression. Simplify using `[Scheme.Hom.app_eq_appLE]`. Use extensionality with `x`. Simplify using `[constHom]`.
-/
theorem existsUnique_affine (H : IsPullback ρ π q (spMap (algebraMap K (DualNumber K)))) {U : Y.Opens}
    (hU : IsAffineOpen U) (F : Γ(Y', ρ ⁻¹ᵁ U)) : ∃! ab : Γ(Y, U) × Γ(Y, U),
      F = (ρ.app U).hom ab.1 + constFn π _ DualNumber.eps * (ρ.app U).hom ab.2 := by
  refine existsUnique_of_isPushout (constHom q U) (ρ.app U) (constHom π (ρ ⁻¹ᵁ U)) ?_ F
  have po := (isIso_pushoutSection_iff H (US := ⊤) (UT := ⊤) (UX := U) (UY := ρ ⁻¹ᵁ U) le_top
    le_top (by simp)).mp (isIso_pushoutSection_of_isAffineOpen H _ _ _ (isAffineOpen_top _)
      (isAffineOpen_top _) hU)
  refine po.of_iso (Scheme.ΓSpecIso (.of K)) (Iso.refl _) (Scheme.ΓSpecIso (.of (DualNumber K))) (Iso.refl _)
    ?_ ?_ ?_ ?_
  · ext x; simp [constHom]
  · rw [← Scheme.ΓSpecIso_naturality, Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE]
    rfl
  · simp [Scheme.Hom.app_eq_appLE]
  · ext x; simp [constHom]

/- English proof (translation)
Rewrite using `[map_add, map_mul, res_app ρ h, res_app ρ h, res_constFn]`.
-/
theorem res_comb {U V : Y.Opens} (h : V ≤ U) (h' : ρ ⁻¹ᵁ V ≤ ρ ⁻¹ᵁ U) (a b : Γ(Y, U)) :
    (Y'.presheaf.map (homOfLE h').op).hom ((ρ.app U).hom a + constFn π _ DualNumber.eps * (ρ.app U).hom b) =
      (ρ.app V).hom ((Y.presheaf.map (homOfLE h).op).hom a) +
        constFn π _ DualNumber.eps * (ρ.app V).hom ((Y.presheaf.map (homOfLE h).op).hom b) := by
  rw [map_add, map_mul, res_app ρ h, res_app ρ h, res_constFn]

/- English proof (translation)
Introduce `x hx` and use `by obtain ⟨_, ⟨U, hU, rfl⟩, hxU, hUO⟩ := Y.isBasis_affineOpens.exists_subset_of_mem_open hx O.isOpen exact TopologicalSpace.Opens.mem_iSup.2 ⟨⟨U, hU, hUO⟩, hxU⟩`.
-/
theorem le_iSup_affine (O : Y.Opens) : O ≤ ⨆ U : {U : Y.Opens // IsAffineOpen U ∧ U ≤ O}, U.1 := fun x hx => by
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, hUO⟩ := Y.isBasis_affineOpens.exists_subset_of_mem_open hx O.isOpen
  exact TopologicalSpace.Opens.mem_iSup.2 ⟨⟨U, hU, hUO⟩, hxU⟩

/- English proof (translation)
Establish `loc : ∀ U : {U : Y.Opens // IsAffineOpen U ∧ U ≤ O}, ((Y.presheaf.map (homOfLE U.2.2).op).hom a, (Y.presheaf.map (homOfLE U.2.2).op).hom b) = ((Y.presheaf.map (homOfLE U.2.2).op).hom a', (Y.presheaf.map (homOfLE U.2.2).op).hom b')` using `fun U => by`. Establish `h' : ρ ⁻¹ᵁ U.1 ≤ ρ ⁻¹ᵁ O` using `fun x hx => U.2.2 hx`. Establish `e` using `congrArg (Y'.presheaf.map (homOfLE h').op).hom h`. Rewrite `e` using `[res_comb U.2.2, res_comb U.2.2]`. Conclude with `(existsUnique_affine H U.2.1 _).unique rfl e`.

Conclude with `⟨Y.sheaf.eq_of_locally_eq' _ O (fun U => homOfLE U.2.2) (le_iSup_affine O) a a' fun U => congrArg Prod.fst (loc U), Y.sheaf.eq_of_locally_eq' _ O (fun U => homOfLE U.2.2) (le_iSup_affine O) b b' fun U => congrArg Prod.snd (loc U)⟩`.
-/
theorem unique_comb (H : IsPullback ρ π q (spMap (algebraMap K (DualNumber K)))) {O : Y.Opens} {a b a' b' : Γ(Y, O)}
    (h : (ρ.app O).hom a + constFn π _ DualNumber.eps * (ρ.app O).hom b =
      (ρ.app O).hom a' + constFn π _ DualNumber.eps * (ρ.app O).hom b') : a = a' ∧ b = b' := by
  have loc : ∀ U : {U : Y.Opens // IsAffineOpen U ∧ U ≤ O},
      ((Y.presheaf.map (homOfLE U.2.2).op).hom a, (Y.presheaf.map (homOfLE U.2.2).op).hom b) =
      ((Y.presheaf.map (homOfLE U.2.2).op).hom a', (Y.presheaf.map (homOfLE U.2.2).op).hom b') := fun U => by
    have h' : ρ ⁻¹ᵁ U.1 ≤ ρ ⁻¹ᵁ O := fun x hx => U.2.2 hx
    have e := congrArg (Y'.presheaf.map (homOfLE h').op).hom h
    rw [res_comb U.2.2, res_comb U.2.2] at e
    exact (existsUnique_affine H U.2.1 _).unique rfl e
  exact ⟨Y.sheaf.eq_of_locally_eq' _ O (fun U => homOfLE U.2.2) (le_iSup_affine O) a a'
      fun U => congrArg Prod.fst (loc U),
    Y.sheaf.eq_of_locally_eq' _ O (fun U => homOfLE U.2.2) (le_iSup_affine O) b b'
      fun U => congrArg Prod.snd (loc U)⟩

/- English proof (translation)
Establish `hle : ∀ U : {U : Y.Opens // IsAffineOpen U ∧ U ≤ O}, ρ ⁻¹ᵁ U.1 ≤ ρ ⁻¹ᵁ O` using `fun U x hx => U.2.2 hx`. Use `choose ab hab using fun U : {U : Y.Opens // IsAffineOpen U ∧ U ≤ O} => (existsUnique_affine H U.2.1 ((Y'.presheaf.map (homOfLE (hle U)).op).hom F)).exists`. Establish `comp : ∀ U V : {U : Y.Opens // IsAffineOpen U ∧ U ≤ O}, (Y.presheaf.map (homOfLE (inf_le_left : U.1 ⊓ V.1 ≤ U.1)).op).hom (ab U).1 = (Y.presheaf.map (homOfLE (inf_le_right : U.1 ⊓ V.1 ≤ V.1)).op).hom (ab V).1 ∧ (Y.presheaf.map (homOfLE (inf_le_left : U.1 ⊓ V.1 ≤ U.1)).op).hom (ab …` using `fun U V => by`. Apply `unique_comb H` to reduce the goal to its premises. Rewrite using `[← res_comb inf_le_left (fun x hx => hx.1), ← res_comb inf_le_right (fun x hx => hx.2), ← hab, ← hab]`.

Conclude with `(res_res _ _ F).trans (res_res _ _ F).symm`. Take `⟨a, ha, -⟩` from `Y.sheaf.existsUnique_gluing' _ O (fun U => homOfLE U.2.2) (le_iSup_affine O) (fun U => (ab U).1) (fun U V => (comp U V).1)`. Take `⟨b, hb, -⟩` from `Y.sheaf.existsUnique_gluing' _ O (fun U => homOfLE U.2.2) (le_iSup_affine O) (fun U => (ab U).2) (fun U V => (comp U V).2)`. Establish `hF : F = (ρ.app O).hom a + constFn π _ DualNumber.eps * (ρ.app O).hom b`. Use `Y'.sheaf.eq_of_locally_eq' (fun U : {U : Y.Opens // IsAffineOpen U ∧ U ≤ O} => ρ ⁻¹ᵁ U.1) _ (fun U => homOfLE (hle U)) (fun x hx => ?_) _ _ fun U => ?_` and prove the remaining obligations.

Take `⟨U, hU⟩` from `TopologicalSpace.Opens.mem_iSup.1 (le_iSup_affine O hx)`. Conclude with `TopologicalSpace.Opens.mem_iSup.2 ⟨U, hU⟩`. Use `(hab U).trans (Eq.trans ?_ (res_comb U.2.2 (hle U) a b).symm)` and prove the remaining obligations. Rewrite using `[← ha U, ← hb U]`. Both sides reduce to the same expression.

Use `⟨(a, b), hF, fun c hc => ?_⟩` and prove the remaining obligations. Use `unique_comb H (hc.symm.trans hF)` as an intermediate fact. Conclude with `Prod.ext this.1 this.2`.
-/
theorem existsUnique_comb (H : IsPullback ρ π q (spMap (algebraMap K (DualNumber K)))) (O : Y.Opens)
    (F : Γ(Y', ρ ⁻¹ᵁ O)) : ∃! ab : Γ(Y, O) × Γ(Y, O),
      F = (ρ.app O).hom ab.1 + constFn π _ DualNumber.eps * (ρ.app O).hom ab.2 := by
  have hle : ∀ U : {U : Y.Opens // IsAffineOpen U ∧ U ≤ O}, ρ ⁻¹ᵁ U.1 ≤ ρ ⁻¹ᵁ O := fun U x hx => U.2.2 hx
  choose ab hab using fun U : {U : Y.Opens // IsAffineOpen U ∧ U ≤ O} =>
    (existsUnique_affine H U.2.1 ((Y'.presheaf.map (homOfLE (hle U)).op).hom F)).exists
  have comp : ∀ U V : {U : Y.Opens // IsAffineOpen U ∧ U ≤ O},
      (Y.presheaf.map (homOfLE (inf_le_left : U.1 ⊓ V.1 ≤ U.1)).op).hom (ab U).1 =
        (Y.presheaf.map (homOfLE (inf_le_right : U.1 ⊓ V.1 ≤ V.1)).op).hom (ab V).1 ∧
      (Y.presheaf.map (homOfLE (inf_le_left : U.1 ⊓ V.1 ≤ U.1)).op).hom (ab U).2 =
        (Y.presheaf.map (homOfLE (inf_le_right : U.1 ⊓ V.1 ≤ V.1)).op).hom (ab V).2 := fun U V => by
    apply unique_comb H
    rw [← res_comb inf_le_left (fun x hx => hx.1), ← res_comb inf_le_right (fun x hx => hx.2), ← hab, ← hab]
    exact (res_res _ _ F).trans (res_res _ _ F).symm
  obtain ⟨a, ha, -⟩ := Y.sheaf.existsUnique_gluing' _ O (fun U => homOfLE U.2.2) (le_iSup_affine O)
    (fun U => (ab U).1) (fun U V => (comp U V).1)
  obtain ⟨b, hb, -⟩ := Y.sheaf.existsUnique_gluing' _ O (fun U => homOfLE U.2.2) (le_iSup_affine O)
    (fun U => (ab U).2) (fun U V => (comp U V).2)
  have hF : F = (ρ.app O).hom a + constFn π _ DualNumber.eps * (ρ.app O).hom b := by
    refine Y'.sheaf.eq_of_locally_eq' (fun U : {U : Y.Opens // IsAffineOpen U ∧ U ≤ O} => ρ ⁻¹ᵁ U.1) _
      (fun U => homOfLE (hle U)) (fun x hx => ?_) _ _ fun U => ?_
    · obtain ⟨U, hU⟩ := TopologicalSpace.Opens.mem_iSup.1 (le_iSup_affine O hx)
      exact TopologicalSpace.Opens.mem_iSup.2 ⟨U, hU⟩
    · refine (hab U).trans (Eq.trans ?_ (res_comb U.2.2 (hle U) a b).symm)
      rw [← ha U, ← hb U]
      rfl
  refine ⟨(a, b), hF, fun c hc => ?_⟩
  have := unique_comb H (hc.symm.trans hF)
  exact Prod.ext this.1 this.2

/- English proof (translation)
Establish `hs : Function.Surjective (TrivSqZeroExt.fstHom K K K).toRingHom` using `fun x => ⟨TrivSqZeroExt.inl x, rfl⟩`. Use `⟨fun P => ?_⟩` and prove the remaining obligations. Establish `: P ∈ Set.range (PrimeSpectrum.comap (TrivSqZeroExt.fstHom K K K).toRingHom)`. Rewrite using `[range_comap_of_surjective _ _ hs]`. Introduce `x hx`.

Use `(P : PrimeSpectrum (DualNumber K)).2.mem_of_pow_mem 2 ?_` and prove the remaining obligations. Establish `hx' : x.fst = 0` using `hx`. Apply the tactic sequence `have : x ^ 2 = 0 := by ext <;> simp [sq, hx']`. Rewrite using `[this]`. Conclude with `zero_mem _`.

Conclude with `this`.
-/
theorem surjective_spMap_fst : Surjective (spMap (TrivSqZeroExt.fstHom K K K).toRingHom) := by
  have hs : Function.Surjective (TrivSqZeroExt.fstHom K K K).toRingHom := fun x => ⟨TrivSqZeroExt.inl x, rfl⟩
  refine ⟨fun P => ?_⟩
  have : P ∈ Set.range (PrimeSpectrum.comap (TrivSqZeroExt.fstHom K K K).toRingHom) := by
    rw [range_comap_of_surjective _ _ hs]
    intro x hx
    refine (P : PrimeSpectrum (DualNumber K)).2.mem_of_pow_mem 2 ?_
    have hx' : x.fst = 0 := hx
    have : x ^ 2 = 0 := by ext <;> simp [sq, hx']
    rw [this]; exact zero_mem _
  exact this

/- English proof (translation)
Introduce `K _ Y Y' q π ρ j H hj hq`. Establish `e : spMap (TrivSqZeroExt.fstHom K K K).toRingHom ≫ spMap (algebraMap K (DualNumber K)) = 𝟙 _`. Rewrite using `[← Spec.map_comp, ← Spec.map_id]`. Use `congr 1`. Establish `hp : IsPullback j q π (spMap (TrivSqZeroExt.fstHom K K K).toRingHom)`.

Use `IsPullback.of_right ?_ hq H` and prove the remaining obligations. Rewrite using `[hj, e]`. Conclude with `IsPullback.id_horiz q`. Use `⟨fun O => ?_, hp, existsUnique_comb H⟩` and prove the remaining obligations. Establish `hs : Surjective j` using `MorphismProperty.of_isPullback (P := @Surjective) hp.flip surjective_spMap_fst`.

Use extensionality with `x`. Take `⟨y, rfl⟩` from `hs.surj x`. Express the relevant statement in the definitionally equal form `j (ρ (j y)) ∈ O ↔ j y ∈ O`. Rewrite using `[← Scheme.Hom.comp_apply j ρ, hj]`. Both sides reduce to the same expression.
-/
theorem structure_dualNumber : ∀ (K : Type) [Field K] (Y Y' : Scheme.{0}) (q : Y ⟶ Sp K) (π : Y' ⟶ Sp (DualNumber K)) (ρ : Y' ⟶ Y) (j : Y ⟶ Y'), IsPullback ρ π q (spMap (algebraMap K (DualNumber K))) → j ≫ ρ = 𝟙 Y → j ≫ π = q ≫ (spMap (TrivSqZeroExt.fstHom K K K).toRingHom) → (∀ O : Y'.Opens, ρ ⁻¹ᵁ (j ⁻¹ᵁ O) = O) ∧ IsPullback j q π (spMap (TrivSqZeroExt.fstHom K K K).toRingHom) ∧ ∀ (O : Y.Opens) (F : Γ(Y', ρ ⁻¹ᵁ O)), ∃! ab : Γ(Y, O) × Γ(Y, O), F = (ρ.app O).hom ab.1 + constFn π _ DualNumber.eps * (ρ.app O).hom ab.2 := by
  intro K _ Y Y' q π ρ j H hj hq
  have e : spMap (TrivSqZeroExt.fstHom K K K).toRingHom ≫ spMap (algebraMap K (DualNumber K)) = 𝟙 _ := by
    rw [← Spec.map_comp, ← Spec.map_id]
    congr 1
  have hp : IsPullback j q π (spMap (TrivSqZeroExt.fstHom K K K).toRingHom) := by
    refine IsPullback.of_right ?_ hq H
    rw [hj, e]
    exact IsPullback.id_horiz q
  refine ⟨fun O => ?_, hp, existsUnique_comb H⟩
  have hs : Surjective j := MorphismProperty.of_isPullback (P := @Surjective) hp.flip surjective_spMap_fst
  ext x
  obtain ⟨y, rfl⟩ := hs.surj x
  change j (ρ (j y)) ∈ O ↔ j y ∈ O
  rw [← Scheme.Hom.comp_apply j ρ, hj]
  rfl

end GlobalTheory.ConstThickening
end

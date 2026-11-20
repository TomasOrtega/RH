import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GapGeSubKapBase
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnitOfCocycleRightActionCharZeroStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FromSpecResidueFieldCompAutEqOfFixesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsInvariantLocalEquationCartierFiniteQuotienStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFunctionFieldMapEqOfGroupInvariantStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RationalFunctionUnitAtPointOfFibreQuotientStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCartierDivisorGroupQuotientDescentStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CechPicardPullbackCartierDivisorBundleEqStatement

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.HSApp GlobalTheory.Cartier
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW secZ ptF LiesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR levDet secRing move)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.OrbitSep

namespace GlobalTheory.QuotDescent

/- English proof (translation)
Establish `e : Spec.map (CommRingCat.ofHom (functionFieldMap (a ≫ b))) ≫ genericFieldPoint Z = Spec.map (CommRingCat.ofHom ((functionFieldMap a).comp (functionFieldMap b))) ≫ genericFieldPoint Z`. Rewrite using `[specMap_functionFieldMap, CommRingCat.ofHom_comp, Spec.map_comp, Category.assoc, specMap_functionFieldMap, ← Category.assoc, ← Category.assoc, specMap_functionFieldMap]`. Use `haveI : Mono (genericFieldPoint Z) := inferInstanceAs (Mono (Z.fromSpecStalk _))`. Use `Spec.map_injective ((cancel_mono _).mp e)` as an intermediate fact. Conclude with `congrArg CommRingCat.Hom.hom this`.
-/
theorem functionFieldMap_comp {X Y Z : Scheme.{0}} [IsIntegral X] [IsIntegral Y] [IsIntegral Z]
    (a : X ⟶ Y) (b : Y ⟶ Z) [IsDominant a] [IsDominant b] [IsDominant (a ≫ b)] :
    functionFieldMap (a ≫ b) = (functionFieldMap a).comp (functionFieldMap b) := by
  have e : Spec.map (CommRingCat.ofHom (functionFieldMap (a ≫ b))) ≫ genericFieldPoint Z =
      Spec.map (CommRingCat.ofHom ((functionFieldMap a).comp (functionFieldMap b))) ≫
        genericFieldPoint Z := by
    rw [specMap_functionFieldMap, CommRingCat.ofHom_comp, Spec.map_comp, Category.assoc,
      specMap_functionFieldMap, ← Category.assoc, ← Category.assoc, specMap_functionFieldMap]
  haveI : Mono (genericFieldPoint Z) := inferInstanceAs (Mono (Z.fromSpecStalk _))
  have := Spec.map_injective ((cancel_mono _).mp e)
  exact congrArg CommRingCat.Hom.hom this

/- English proof (translation)
Introduce `X _ Γ _ ρ γ δ u`. Use `haveI : IsIso (ρ γ).hom := Iso.isIso_hom (ρ γ)`. Use `haveI : IsIso (ρ δ).hom := Iso.isIso_hom (ρ δ)`. Use `haveI : IsIso (ρ (γ * δ)).hom := Iso.isIso_hom (ρ (γ * δ))`. Establish `hc : (ρ (γ * δ)).hom = (ρ δ).hom ≫ (ρ γ).hom`.

Rewrite using `[map_mul, Aut.Aut_mul_def]`. Both sides reduce to the same expression. Apply `Units.ext` to reduce the goal to its premises. Express the relevant statement in the definitionally equal form `functionFieldMap (ρ (γ * δ)).hom (u : X.functionField) = functionFieldMap (ρ δ).hom (functionFieldMap (ρ γ).hom (u : X.functionField))`. Establish `key : ∀ (f : X ⟶ X) (_ : IsDominant f), f = (ρ δ).hom ≫ (ρ γ).hom → functionFieldMap f (u : X.functionField) = functionFieldMap (ρ δ).hom (functionFieldMap (ρ γ).hom (u : X.functionField))`.

Introduce and unpack `f _ rfl`. Rewrite using `[functionFieldMap_comp]`. Both sides reduce to the same expression. Conclude with `key _ inferInstance hc`.
-/
theorem fnAct_mul : ∀ (X : Scheme.{0}) [IsIntegral X] (Γ : Type) [Group Γ] (ρ : Γ →* Aut X) (γ δ : Γ)
    (u : X.functionFieldˣ), fnAct ρ (γ * δ) u = fnAct ρ δ (fnAct ρ γ u) := by
  intro X _ Γ _ ρ γ δ u
  haveI : IsIso (ρ γ).hom := Iso.isIso_hom (ρ γ)
  haveI : IsIso (ρ δ).hom := Iso.isIso_hom (ρ δ)
  haveI : IsIso (ρ (γ * δ)).hom := Iso.isIso_hom (ρ (γ * δ))
  have hc : (ρ (γ * δ)).hom = (ρ δ).hom ≫ (ρ γ).hom := by
    rw [map_mul, Aut.Aut_mul_def]; rfl
  apply Units.ext
  change functionFieldMap (ρ (γ * δ)).hom (u : X.functionField) =
    functionFieldMap (ρ δ).hom (functionFieldMap (ρ γ).hom (u : X.functionField))
  have key : ∀ (f : X ⟶ X) (_ : IsDominant f), f = (ρ δ).hom ≫ (ρ γ).hom →
      functionFieldMap f (u : X.functionField) =
        functionFieldMap (ρ δ).hom (functionFieldMap (ρ γ).hom (u : X.functionField)) := by
    rintro f _ rfl
    rw [functionFieldMap_comp]
    rfl
  exact key _ inferInstance hc

/- English proof (translation)
Introduce `F _ _ X W _ q sW Γ _ _ ρ L hL _ hq hR`. Take `⟨D, c, hcls, hcoc, heq, hin⟩` from `hR`. Use `haveI : IsIntegral W := hq.isIntegral`. Use `haveI : Surjective q := hq.surjective`. Use `haveI : CharZero X.functionField := charZero_of_injective_ringHom (toFunctionField (q ≫ sW)).injective`.

Set `σ : Γ → X.functionField →+* X.functionField` to `fun γ => haveI : IsIso (ρ γ).hom := Iso.isIso_hom (ρ γ)`. Use `functionFieldMap (ρ γ).hom`. Establish `hσu : ∀ γ (u : X.functionFieldˣ), ((fnAct ρ γ u : X.functionFieldˣ) : X.functionField) = σ γ u` using `fun _ _ => rfl`. Establish `hσ : ∀ γ δ a, σ (γ * δ) a = σ δ (σ γ a)`. Introduce `γ δ a`.

Distinguish the cases in `ha : a = 0`. Simplify using `[ha]`. Use `congrArg Units.val (fnAct_mul X Γ ρ γ δ (Units.mk0 a ha))` as an intermediate fact. Rewrite `this` using `[hσu, hσu, hσu]`. Then use the resulting hypothesis. Establish `hcoc' : ∀ γ δ, (c (γ * δ) : X.functionField) = σ δ (c γ) * c δ` using `fun γ δ => by`.

Rewrite using `[hcoc, Units.val_mul, hσu]`. Establish `htriv : ∀ γ, (∀ a, σ γ a = a) → c γ = 1`. Introduce `γ hγ`. Establish `hη : (ρ γ).hom (genericPoint X) = genericPoint X` using `by haveI : IsIso (ρ γ).hom := Iso.isIso_hom (ρ γ)`. Establish `h1` using `(genericPoint_spec X).image (ρ γ).hom.continuous`.

Establish `hs : Function.Surjective (ρ γ).hom.base` using `(ρ γ).hom.surjective`. Simplify using `only [Set.top_eq_univ, Set.image_univ, hs.range_eq, closure_univ] at h1`. Conclude with `h1.eq (genericPoint_spec X)`. Establish `hfix` using `GlobalTheory.T.fromSpecResidueField_comp_aut_eq_of_fixes X Γ ρ γ _ hη (fun u _ => by rw [hσu, hγ, sub_self]; exact zeroAt_zero _)`. Establish `h0` using `hin γ _ 1 hfix (D.isEqn_genericPoint 1)`.

Establish `h1 : ((fnAct ρ γ 1 * (c γ)⁻¹ * 1⁻¹ : X.functionFieldˣ) : X.functionField) - 1 = 0`. Assume the negation of the conclusion as `hne`. Conclude with `(zeroAt_iff.1 h0).2 (unitAt_genericPoint hne)`. Rewrite `h1` using `[map_one, one_mul, inv_one, mul_one, sub_eq_zero, ← Units.val_one, Units.val_inj, inv_eq_one]`. Conclude with `h1`.

Take `⟨f, hf⟩` from `GlobalTheory.T.hilbert90_finite_rightAction_charZero_field _ Γ σ hσ c hcoc' htriv`. Establish `hfu : ∀ γ, fnAct ρ γ f = c γ * f` using `fun γ => Units.ext (by rw [hσu, Units.val_mul]; exact hf γ)`. Use `set D' := D - CartierDiv.principal f with hD'`. Establish `hD : D' + CartierDiv.principal f = D` using `sub_add_cancel _ _`. Establish `hinv' : ∀ γ x g, D'.IsEqn ((ρ γ).hom x) g → D'.IsEqn x (fnAct ρ γ g)`.

Introduce `γ x g h`. Establish `h1` using `heq γ x (g * f) (by rw [← hD]; exact h.add (CartierDiv.isEqn_principal f _))`. Establish `h2` using `h1.sub (CartierDiv.isEqn_principal f x)`. Establish `e : fnAct ρ γ g = fnAct ρ γ (g * f) * (c γ)⁻¹ / f`. Rewrite using `[map_mul, hfu]`.

Simplify using `[div_eq_mul_inv, mul_comm, mul_assoc, mul_left_comm]`. Rewrite using `[e]`. Conclude with `h2`. Establish `hin' : ∀ γ x g, X.fromSpecResidueField x ≫ (ρ γ).hom = X.fromSpecResidueField x → D'.IsEqn x g → ZeroAt x (((fnAct ρ γ g * g⁻¹ : X.functionFieldˣ) : X.functionField) - 1)`. Introduce `γ x g hx h`.

Establish `h1` using `hin γ x (g * f) hx (by rw [← hD]; exact h.add (CartierDiv.isEqn_principal f x))`. Establish `e : fnAct ρ γ g * g⁻¹ = fnAct ρ γ (g * f) * (c γ)⁻¹ * (g * f)⁻¹`. Rewrite using `[map_mul, hfu]`. Simplify using `[mul_inv_rev, mul_comm, mul_assoc, mul_left_comm]`. Rewrite using `[e]`.

Conclude with `h1`. Establish `hloc` using `GlobalTheory.T.exists_invariant_localEquation_cartier_finiteQuotient F X W (q ≫ sW) Γ ρ q hq D' hinv' hin'`. Establish `key : ∀ y : W, ∃ b : W.functionFieldˣ, ∀ x, q x = y → D'.IsEqn x (Units.map (functionFieldMap q).toMonoidHom b)`. Introduce `y`. Take `⟨x, rfl⟩` from `q.surjective y`.

Take `⟨g, hg, hgx⟩` from `hloc x`. Take `⟨b, hb⟩` from `GlobalTheory.T.exists_functionFieldMap_eq_of_groupInvariant X W Γ ρ q hq g hg`. Use `⟨b, fun x' hx' => ?_⟩` and prove the remaining obligations. Take `⟨γ, rfl⟩` from `(hq.apply_eq_iff x x').1 hx'.symm`. Rewrite using `[hb]`.

Establish `hp : (ρ γ⁻¹).hom ((ρ γ).hom x) = x`. Rewrite using `[map_inv]`. Conclude with `Scheme.inv_hom_apply _ _`. Use `hinv' γ⁻¹ ((ρ γ).hom x) g (by rw [hp]; exact hgx)` as an intermediate fact. Rewrite `this` using `[hg]`. Then use the resulting hypothesis.

Take `⟨E, hE⟩` from `GlobalTheory.T.exists_cartierDivisor_group_quotient_descent X W Γ ρ q hq D' key`. Use `⟨toLB E, isLB_toLB E, ?_⟩` and prove the remaining obligations. Rewrite using `[GlobalTheory.T.cechPicardPullback_cartierDivisorBundle_eq X W q D' E hE]`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem descent : ∀ (F : Type) [Field F] [NumberField F] (X W : Scheme.{0}) [IsIntegral X] (q : X ⟶ W) (sW : W ⟶ Sp F) (Γ : Type) [Group Γ] [Finite Γ] (ρ : Γ →* Aut X) (L : LB X) (hL : L.IsLB), IsProjOver (q ≫ sW) → IsAffineQuotient ρ q → RatLin ρ L hL → ∃ (N : LB W) (hN : N.IsLB), CechPic.pull q (cls N hN) = cls L hL := by
  intro F _ _ X W _ q sW Γ _ _ ρ L hL _ hq hR
  obtain ⟨D, c, hcls, hcoc, heq, hin⟩ := hR
  haveI : IsIntegral W := hq.isIntegral
  haveI : Surjective q := hq.surjective
  haveI : CharZero X.functionField :=
    charZero_of_injective_ringHom (toFunctionField (q ≫ sW)).injective
  let σ : Γ → X.functionField →+* X.functionField := fun γ =>
    haveI : IsIso (ρ γ).hom := Iso.isIso_hom (ρ γ); functionFieldMap (ρ γ).hom
  have hσu : ∀ γ (u : X.functionFieldˣ), ((fnAct ρ γ u : X.functionFieldˣ) : X.functionField) = σ γ u :=
    fun _ _ => rfl
  have hσ : ∀ γ δ a, σ (γ * δ) a = σ δ (σ γ a) := by
    intro γ δ a
    by_cases ha : a = 0
    · simp [ha]
    · have := congrArg Units.val (fnAct_mul X Γ ρ γ δ (Units.mk0 a ha))
      rwa [hσu, hσu, hσu] at this
  have hcoc' : ∀ γ δ, (c (γ * δ) : X.functionField) = σ δ (c γ) * c δ := fun γ δ => by
    rw [hcoc, Units.val_mul, hσu]
  have htriv : ∀ γ, (∀ a, σ γ a = a) → c γ = 1 := by
    intro γ hγ
    have hη : (ρ γ).hom (genericPoint X) = genericPoint X := by
      haveI : IsIso (ρ γ).hom := Iso.isIso_hom (ρ γ)
      have h1 := (genericPoint_spec X).image (ρ γ).hom.continuous
      have hs : Function.Surjective (ρ γ).hom.base := (ρ γ).hom.surjective
      simp only [Set.top_eq_univ, Set.image_univ, hs.range_eq, closure_univ] at h1
      exact h1.eq (genericPoint_spec X)
    have hfix := GlobalTheory.T.fromSpecResidueField_comp_aut_eq_of_fixes X Γ ρ γ _ hη (fun u _ => by rw [hσu, hγ, sub_self]; exact zeroAt_zero _)
    have h0 := hin γ _ 1 hfix (D.isEqn_genericPoint 1)
    have h1 : ((fnAct ρ γ 1 * (c γ)⁻¹ * 1⁻¹ : X.functionFieldˣ) : X.functionField) - 1 = 0 := by
      by_contra hne
      exact (zeroAt_iff.1 h0).2 (unitAt_genericPoint hne)
    rw [map_one, one_mul, inv_one, mul_one, sub_eq_zero, ← Units.val_one, Units.val_inj, inv_eq_one] at h1
    exact h1
  obtain ⟨f, hf⟩ := GlobalTheory.T.hilbert90_finite_rightAction_charZero_field _ Γ σ hσ c hcoc' htriv
  have hfu : ∀ γ, fnAct ρ γ f = c γ * f := fun γ => Units.ext (by rw [hσu, Units.val_mul]; exact hf γ)
  set D' := D - CartierDiv.principal f with hD'
  have hD : D' + CartierDiv.principal f = D := sub_add_cancel _ _
  have hinv' : ∀ γ x g, D'.IsEqn ((ρ γ).hom x) g → D'.IsEqn x (fnAct ρ γ g) := by
    intro γ x g h
    have h1 := heq γ x (g * f) (by rw [← hD]; exact h.add (CartierDiv.isEqn_principal f _))
    have h2 := h1.sub (CartierDiv.isEqn_principal f x)
    have e : fnAct ρ γ g = fnAct ρ γ (g * f) * (c γ)⁻¹ / f := by
      rw [map_mul, hfu]; simp [div_eq_mul_inv, mul_comm, mul_assoc, mul_left_comm]
    rw [e]; exact h2
  have hin' : ∀ γ x g, X.fromSpecResidueField x ≫ (ρ γ).hom = X.fromSpecResidueField x → D'.IsEqn x g →
      ZeroAt x (((fnAct ρ γ g * g⁻¹ : X.functionFieldˣ) : X.functionField) - 1) := by
    intro γ x g hx h
    have h1 := hin γ x (g * f) hx (by rw [← hD]; exact h.add (CartierDiv.isEqn_principal f x))
    have e : fnAct ρ γ g * g⁻¹ = fnAct ρ γ (g * f) * (c γ)⁻¹ * (g * f)⁻¹ := by
      rw [map_mul, hfu]; simp [mul_inv_rev, mul_comm, mul_assoc, mul_left_comm]
    rw [e]; exact h1
  have hloc := GlobalTheory.T.exists_invariant_localEquation_cartier_finiteQuotient F X W (q ≫ sW) Γ ρ q hq D' hinv' hin'
  have key : ∀ y : W, ∃ b : W.functionFieldˣ, ∀ x, q x = y →
      D'.IsEqn x (Units.map (functionFieldMap q).toMonoidHom b) := by
    intro y
    obtain ⟨x, rfl⟩ := q.surjective y
    obtain ⟨g, hg, hgx⟩ := hloc x
    obtain ⟨b, hb⟩ := GlobalTheory.T.exists_functionFieldMap_eq_of_groupInvariant X W Γ ρ q hq g hg
    refine ⟨b, fun x' hx' => ?_⟩
    obtain ⟨γ, rfl⟩ := (hq.apply_eq_iff x x').1 hx'.symm
    rw [hb]
    have hp : (ρ γ⁻¹).hom ((ρ γ).hom x) = x := by
      rw [map_inv]
      exact Scheme.inv_hom_apply _ _
    have := hinv' γ⁻¹ ((ρ γ).hom x) g (by rw [hp]; exact hgx)
    rwa [hg] at this
  obtain ⟨E, hE⟩ := GlobalTheory.T.exists_cartierDivisor_group_quotient_descent X W Γ ρ q hq D' key
  refine ⟨toLB E, isLB_toLB E, ?_⟩
  rw [GlobalTheory.T.cechPicardPullback_cartierDivisorBundle_eq X W q D' E hE]
  calc cls (toLB D') (isLB_toLB D') = toPic D' := (toPic_apply D').symm
    _ = toPic D := by rw [hD', map_sub, toPic_principal, sub_zero]
    _ = cls L hL := hcls

end GlobalTheory.QuotDescent

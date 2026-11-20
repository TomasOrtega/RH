import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GapGeSubKapBase
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FromSpecResidueFieldCompAutEqOfFixes
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCartierSectionGeneratesAtVanishesAtFinsetStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAffineFunctionWeightedTranslatesUnitAtStatement
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

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.InvEqn

variable {X : Scheme.{0}} [IsIntegral X]

/- English proof (translation)
Take `⟨a, rfl⟩` from `h`. Conclude with `⟨φ.stalkMap x a, (GlobalTheory.functionFieldMap_algebraMap φ x a).symm⟩`.
-/
theorem regAt_map (φ : X ⟶ X) [IsDominant φ] {x : X} {f : X.functionField} (h : RegAt (φ x) f) :
    RegAt x (GlobalTheory.functionFieldMap φ f) := by
  obtain ⟨a, rfl⟩ := h
  exact ⟨φ.stalkMap x a, (GlobalTheory.functionFieldMap_algebraMap φ x a).symm⟩

/- English proof (translation)
Take `⟨a, ha, rfl⟩` from `h`. Conclude with `⟨φ.stalkMap x a, map_nonunit (φ.stalkMap x).hom a ha, (GlobalTheory.functionFieldMap_algebraMap φ x a).symm⟩`.
-/
theorem zeroAt_map (φ : X ⟶ X) [IsDominant φ] {x : X} {f : X.functionField} (h : ZeroAt (φ x) f) :
    ZeroAt x (GlobalTheory.functionFieldMap φ f) := by
  obtain ⟨a, ha, rfl⟩ := h
  exact ⟨φ.stalkMap x a, map_nonunit (φ.stalkMap x).hom a ha,
    (GlobalTheory.functionFieldMap_algebraMap φ x a).symm⟩

/- English proof (translation)
Use `(genericPoint_spec X).image φ.continuous` as an intermediate fact. Rewrite `this` using `[Set.image_univ, φ.denseRange.closure_range]`. Conclude with `this.eq (genericPoint_spec X)`.
-/
theorem map_genericPoint (φ : X ⟶ X) [IsDominant φ] : φ (genericPoint X) = genericPoint X := by
  have := (genericPoint_spec X).image φ.continuous
  rw [Set.image_univ, φ.denseRange.closure_range] at this
  exact this.eq (genericPoint_spec X)

/- English proof (translation)
Establish `hz : (φ ≫ ψ) (genericPoint X) = genericPoint X` using `map_genericPoint _`. Establish `hr : RegAt (ψ (φ (genericPoint X))) f`. Rewrite using `[show ψ (φ (genericPoint X)) = (φ ≫ ψ) (genericPoint X) from rfl, hz]`. Conclude with `regAt_genericPoint f`. Take `⟨a, rfl⟩` from `hr`.

Rewrite using `[GlobalTheory.functionFieldMap_algebraMap ψ, GlobalTheory.functionFieldMap_algebraMap φ]`. Use `GlobalTheory.functionFieldMap_algebraMap (φ ≫ ψ) (genericPoint X) a` as an intermediate fact. Use `this.trans ?_` and prove the remaining obligations. Rewrite using `[Scheme.Hom.stalkMap_comp]`. Both sides reduce to the same expression.
-/
theorem functionFieldMap_comp (φ ψ : X ⟶ X) [IsDominant φ] [IsDominant ψ] [IsDominant (φ ≫ ψ)]
    (f : X.functionField) :
    GlobalTheory.functionFieldMap (φ ≫ ψ) f = GlobalTheory.functionFieldMap φ (GlobalTheory.functionFieldMap ψ f) := by
  have hz : (φ ≫ ψ) (genericPoint X) = genericPoint X := map_genericPoint _
  have hr : RegAt (ψ (φ (genericPoint X))) f := by
    rw [show ψ (φ (genericPoint X)) = (φ ≫ ψ) (genericPoint X) from rfl, hz]
    exact regAt_genericPoint f
  obtain ⟨a, rfl⟩ := hr
  rw [GlobalTheory.functionFieldMap_algebraMap ψ, GlobalTheory.functionFieldMap_algebraMap φ]
  have := GlobalTheory.functionFieldMap_algebraMap (φ ≫ ψ) (genericPoint X) a
  refine this.trans ?_
  rw [Scheme.Hom.stalkMap_comp]
  rfl

/- English proof (translation)
Take `⟨a, ha, rfl⟩` from `h`. Take `⟨b, hb, rfl⟩` from `h'`. Use `⟨a + b, ?_, map_add _ a b⟩` and prove the remaining obligations. Assume the negation of the conclusion as `hu`. Establish `h1 : a + b ∈ IsLocalRing.maximalIdeal _` using `hu`.

Conclude with `((IsLocalRing.mem_maximalIdeal _).1 (by simpa using sub_mem h1 hb)) ha`.
-/
theorem UnitAt.add_zeroAt {x : X} {f f' : X.functionField} (h : UnitAt x f) (h' : ZeroAt x f') :
    UnitAt x (f + f') := by
  obtain ⟨a, ha, rfl⟩ := h
  obtain ⟨b, hb, rfl⟩ := h'
  refine ⟨a + b, ?_, map_add _ a b⟩
  by_contra hu
  have h1 : a + b ∈ IsLocalRing.maximalIdeal _ := hu
  exact ((IsLocalRing.mem_maximalIdeal _).1 (by simpa using sub_mem h1 hb)) ha

variable {Γ : Type} [Group Γ]

def sig (ρ : Γ →* Aut X) (γ : Γ) : X.functionField →+* X.functionField :=
  haveI : IsIso (ρ γ).hom := Iso.isIso_hom (ρ γ)
  GlobalTheory.functionFieldMap (ρ γ).hom

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem fnAct_val (ρ : Γ →* Aut X) (γ : Γ) (g : X.functionFieldˣ) :
    ((fnAct ρ γ g : X.functionFieldˣ) : X.functionField) = sig ρ γ g := rfl

/- English proof (translation)
The claim follows from `haveI : IsIso (ρ γ).hom := Iso.isIso_hom (ρ γ) regAt_map _ h`.
-/
theorem regAt_sig (ρ : Γ →* Aut X) (γ : Γ) {x : X} {f : X.functionField}
    (h : RegAt ((ρ γ).hom x) f) : RegAt x (sig ρ γ f) :=
  haveI : IsIso (ρ γ).hom := Iso.isIso_hom (ρ γ)
  regAt_map _ h

/- English proof (translation)
The claim follows from `haveI : IsIso (ρ γ).hom := Iso.isIso_hom (ρ γ) zeroAt_map _ h`.
-/
theorem zeroAt_sig (ρ : Γ →* Aut X) (γ : Γ) {x : X} {f : X.functionField}
    (h : ZeroAt ((ρ γ).hom x) f) : ZeroAt x (sig ρ γ f) :=
  haveI : IsIso (ρ γ).hom := Iso.isIso_hom (ρ γ)
  zeroAt_map _ h

/- English proof (translation)
Use `haveI : IsIso (ρ γ).hom := Iso.isIso_hom (ρ γ)`. Use `haveI : IsIso (ρ δ).hom := Iso.isIso_hom (ρ δ)`. Use `haveI : IsIso (ρ (δ * γ)).hom := Iso.isIso_hom (ρ (δ * γ))`. Establish `e : (ρ (δ * γ)).hom = (ρ γ).hom ≫ (ρ δ).hom` using `by rw [map_mul]; rfl`. Establish `key : ∀ (φ : X ⟶ X) (h : φ = (ρ γ).hom ≫ (ρ δ).hom) [IsDominant φ], GlobalTheory.functionFieldMap φ f = GlobalTheory.functionFieldMap (ρ γ).hom (GlobalTheory.functionFieldMap (ρ δ).hom f)`.

Introduce `φ h _`. Substitute `h` using the available equality. Conclude with `functionFieldMap_comp _ _ f`. Conclude with `(key _ e).symm`.
-/
theorem sig_sig (ρ : Γ →* Aut X) (γ δ : Γ) (f : X.functionField) :
    sig ρ γ (sig ρ δ f) = sig ρ (δ * γ) f := by
  haveI : IsIso (ρ γ).hom := Iso.isIso_hom (ρ γ)
  haveI : IsIso (ρ δ).hom := Iso.isIso_hom (ρ δ)
  haveI : IsIso (ρ (δ * γ)).hom := Iso.isIso_hom (ρ (δ * γ))
  have e : (ρ (δ * γ)).hom = (ρ γ).hom ≫ (ρ δ).hom := by rw [map_mul]; rfl
  have key : ∀ (φ : X ⟶ X) (h : φ = (ρ γ).hom ≫ (ρ δ).hom) [IsDominant φ],
      GlobalTheory.functionFieldMap φ f = GlobalTheory.functionFieldMap (ρ γ).hom (GlobalTheory.functionFieldMap (ρ δ).hom f) := by
    intro φ h _
    subst h
    exact functionFieldMap_comp _ _ f
  exact (key _ e).symm

/- English proof (translation)
Use `sig_sig ρ 1 1 f` as an intermediate fact. Rewrite `this` using `[mul_one]`. Conclude with `(sig ρ 1).injective this`.
-/
theorem sig_one (ρ : Γ →* Aut X) (f : X.functionField) : sig ρ 1 f = f := by
  have := sig_sig ρ 1 1 f
  rw [mul_one] at this
  exact (sig ρ 1).injective this

/- English proof (translation)
Use `set a : ℕ → X := fun k => (ρ (γ ^ k)).hom x with ha`. Establish `hs : ∀ k, a (k + 1) = (ρ γ).hom (a k)` using `fun k => by`. Simplify using `only [ha, pow_succ', map_mul]`. Both sides reduce to the same expression. Establish `h0 : a 0 = x` using `by simp only [ha, pow_zero, map_one]; rfl`.

Establish `h1 : a 1 ⤳ a 0`. Rewrite using `[h0, hs, h0, specializes_iff_mem_closure]`. Conclude with `h`. Establish `hstep : ∀ k, a (k + 1) ⤳ a k` using `fun k => by`. Proceed by induction on `k with`.

Consider the case `zero => exact h1`. Consider the case `succ k ih`. Establish `e` using `ih.map (ρ γ).hom.continuous`. Rewrite `e` using `[← hs, ← hs]`. Conclude with `e`.

Establish `hge : ∀ k, a (k + 1) ⤳ a 1` using `fun k => by`. Proceed by induction on `k with`. Consider the case `zero => exact specializes_rfl`. Consider the case `succ k ih => exact (hstep (k + 1)).trans ih`. Establish `hn : 0 < orderOf γ` using `orderOf_pos γ`.

Establish `hx : a (orderOf γ) = x` using `by simp only [ha, pow_orderOf_eq_one, map_one]; rfl`. Take `⟨m, hm⟩ : ∃ m, orderOf γ = m + 1` from `⟨orderOf γ - 1, by omega⟩`. Establish `e1 : x ⤳ a 1` using `by rw [← hx, hm]; exact hge m`. Establish `e2 : a 1 ⤳ x` using `h0 ▸ h1`. Establish `: a 1 = x` using `(e2.antisymm e1).eq`.

Combine the equalities or inequalities in the displayed calculation.
-/
theorem eq_of_mem_closure [Finite Γ] (ρ : Γ →* Aut X) (γ : Γ) (x : X)
    (h : x ∈ closure ({(ρ γ).hom x} : Set X)) : (ρ γ).hom x = x := by
  set a : ℕ → X := fun k => (ρ (γ ^ k)).hom x with ha
  have hs : ∀ k, a (k + 1) = (ρ γ).hom (a k) := fun k => by
    simp only [ha, pow_succ', map_mul]; rfl
  have h0 : a 0 = x := by simp only [ha, pow_zero, map_one]; rfl
  have h1 : a 1 ⤳ a 0 := by
    rw [h0, hs, h0, specializes_iff_mem_closure]; exact h
  have hstep : ∀ k, a (k + 1) ⤳ a k := fun k => by
    induction k with
    | zero => exact h1
    | succ k ih =>
      have e := ih.map (ρ γ).hom.continuous
      rw [← hs, ← hs] at e
      exact e
  have hge : ∀ k, a (k + 1) ⤳ a 1 := fun k => by
    induction k with
    | zero => exact specializes_rfl
    | succ k ih => exact (hstep (k + 1)).trans ih
  have hn : 0 < orderOf γ := orderOf_pos γ
  have hx : a (orderOf γ) = x := by simp only [ha, pow_orderOf_eq_one, map_one]; rfl
  obtain ⟨m, hm⟩ : ∃ m, orderOf γ = m + 1 := ⟨orderOf γ - 1, by omega⟩
  have e1 : x ⤳ a 1 := by rw [← hx, hm]; exact hge m
  have e2 : a 1 ⤳ x := h0 ▸ h1
  have : a 1 = x := (e2.antisymm e1).eq
  calc (ρ γ).hom x = a 1 := by rw [hs 0, h0]
    _ = x := this

/- English proof (translation)
Introduce `F _ _ X W _ s Γ _ _ ρ q hq D hinv hin x`. Use `haveI := Fintype.ofFinite Γ`. Take `⟨_, ⟨V, hV, rfl⟩, hxV, -⟩` from `W.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ (q x)) isOpen_univ`. Use `hq.isAffineHom` as an intermediate fact. Establish `hU : IsAffineOpen (q ⁻¹ᵁ V)` using `hV.preimage q`.

Establish `hxU : x ∈ q ⁻¹ᵁ V` using `hxV`. Establish `horb (γ : Γ) : (ρ γ).hom x ∈ q ⁻¹ᵁ V`. Establish `e : q ((ρ γ).hom x) = q x` using `congr($(hq.comp_eq γ) x)`. Use `show q _ ∈ V`. Rewrite using `[e]`.

Conclude with `hxV`. Set `T : Finset X` to `Finset.univ.image fun γ : Γ => (ρ γ).hom x`. Establish `hT (y : X) : y ∈ T ↔ ∃ γ, (ρ γ).hom x = y` using `by simp [T]`. Take `⟨e₀, he₀, hv⟩` from `GlobalTheory.T.exists_cartierSection_generatesAt_vanishesAt_finset X (q ⁻¹ᵁ V) hU D x hxU T (fun y hy => by obtain ⟨γ, rfl⟩ := (hT y).1 hy; exact horb γ) (fun y hy hne hc => by`. Take `⟨γ, rfl⟩` from `(hT y).1 hy`.

Conclude with `hne (eq_of_mem_closure ρ γ x hc))`. Establish `he0 : e₀ ≠ 0` using `he₀.ne_zero`. Use `set g : X.functionFieldˣ := (Units.mk0 e₀ he0)⁻¹ with hgdef`. Establish `hgv : (g : X.functionField) = e₀⁻¹` using `by simp [hgdef]`. Establish `hg : D.IsEqn x g` using `CartierDiv.isEqn_iff_generatesAt_inv.2 (by rw [hgv, inv_inv]; exact he₀)`.

Establish `hgs (γ : Γ) (hγ : (ρ γ).hom x = x) : D.IsEqn x (fnAct ρ γ g)` using `hinv γ x g (by rw [hγ]; exact hg)`. Set `ι` to `{γ : Γ // (ρ γ).hom x = x}`. Set `σ : ι → X.functionField →+* X.functionField` to `fun i => sig ρ i.1`. Set `u : ι → X.functionField` to `fun i => (g : X.functionField) / sig ρ i.1 g`. Establish `hu (i : ι) : UnitAt x (u i)`.

Use `(hg.iff_unitAt.1 (hgs i.1 i.2)).inv` as an intermediate fact. Rewrite `this` using `[fnAct_val, inv_div]`. Conclude with `this`. Establish `hnat (n : ℕ) (hn : n ≠ 0) : UnitAt x (n : X.functionField)`. Set `φF` to `(Scheme.ΓSpecIso (CommRingCat.of F)).inv ≫ s.appTop ≫ X.presheaf.germ ⊤ x trivial`.

Use `⟨(n : X.presheaf.stalk x), ?_, map_natCast _ n⟩` and prove the remaining obligations. Rewrite using `[← map_natCast φF.hom n]`. Conclude with `(IsUnit.mk0 (n : F) (Nat.cast_ne_zero.2 hn)).map _`. Take `⟨a, ha⟩` from `GlobalTheory.T.exists_affineFunction_weighted_translates_unitAt X (q ⁻¹ᵁ V) hU x hxU ι σ u (fun i f hf => regAt_sig ρ i.1 (by rw [i.2]; exact hf)) (fun i f hf => zeroAt_sig ρ i.1 (by rw [i.2]; exact hf)) (fun i => (hu i).regAt) (fun i hi => by`. Establish `hfr` using `fromSpecResidueField_comp_eq_of_fixes X Γ ρ i.1 x i.2 (fun v hv => by rw [fnAct_val]; exact hi v hv)`.

Establish `h1` using `hin i.1 x g hfr hg`. Rewrite `h1` using `[Units.val_mul, fnAct_val, Units.val_inv_eq_inv_val g]`. Establish `hs0 : sig ρ i.1 g ≠ 0` using `by rw [← fnAct_val]; exact Units.ne_zero _`. Establish `hg0 : (g : X.functionField) ≠ 0` using `Units.ne_zero _`. Establish `e : u i - 1 = (sig ρ i.1 g * (g : X.functionField)⁻¹ - 1) * ((-1) * u i)`.

Simplify using `only [u]`. Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e]`. Conclude with `h1.mul (RegAt.mul (⟨-1, by rw [map_neg, map_one]⟩ : RegAt x (-1)) (hu i).regAt))`.

Use `hnat`. Use the proof step `⟨⟨1, by rw [map_one]; rfl⟩, fun f _ => by`. Simplify using `only [σ, sig_one, sub_self]`. Conclude with `zeroAt_zero x⟩`. Use `set af := fnOf (q ⁻¹ᵁ V) (gen_mem hxU) a with haf`.

Use `set h : X.functionField := ∑ γ : Γ, sig ρ γ (af * e₀) with hh`. Establish `hinvh (δ : Γ) : sig ρ δ h = h`. Rewrite using `[hh, map_sum]`. Simplify using `only [sig_sig]`. Conclude with `Equiv.sum_comp (Equiv.mulRight δ) (fun γ => sig ρ γ (af * e₀))`.

Establish `hsplit : h * g = ∑ i : ι, σ i af * u i + ∑ γ ∈ Finset.univ.filter (fun γ : Γ => ¬ (ρ γ).hom x = x), sig ρ γ (af * e₀) * g`. Rewrite using `[hh, Finset.sum_mul, ← Finset.sum_filter_add_sum_filter_not Finset.univ (fun γ : Γ => (ρ γ).hom x = x)]`. Use `congr 1`. Rewrite using `[Finset.sum_subtype (p := fun γ : Γ => (ρ γ).hom x = x) _ (fun γ => by simp)]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations.

Establish `hs0 : sig ρ i.1 g ≠ 0` using `by rw [← fnAct_val]; exact Units.ne_zero _`. Simplify using `only [σ, u, map_mul, hgv, map_inv₀]`. Rewrite using `[← hgv]`. Clear the denominators using the available nonvanishing facts. Establish `hrest : ZeroAt x (∑ γ ∈ Finset.univ.filter (fun γ : Γ => ¬ (ρ γ).hom x = x), sig ρ γ (af * e₀) * g)`.

Use `Finset.sum_induction _ (ZeroAt x) (fun _ _ h h' => h.add h') (zeroAt_zero x) fun γ hγ => ?_` and prove the remaining obligations. Establish `hne : (ρ γ).hom x ≠ x` using `(Finset.mem_filter.1 hγ).2`. Take `⟨g', hg', hz⟩` from `hv _ ((hT _).2 ⟨γ, rfl⟩) hne`. Establish `hz' : ZeroAt ((ρ γ).hom x) (af * e₀ * g')`. Establish `e : af * e₀ * g' = e₀ * g' * af` using `by ring`.

Rewrite using `[e]`. Conclude with `hz.mul (regAt_fnOf (horb γ) _ a)`. Establish `h2` using `zeroAt_sig ρ γ hz'`. Establish `h3 : UnitAt x ((g : X.functionField) / fnAct ρ γ g')` using `(hinv γ x g' hg').iff_unitAt.1 hg`. Rewrite `h3` using `[fnAct_val]`.

Establish `hs0 : sig ρ γ g' ≠ 0` using `by rw [← fnAct_val]; exact Units.ne_zero _`. Establish `e : sig ρ γ (af * e₀) * g = sig ρ γ (af * e₀ * g') * ((g : X.functionField) / sig ρ γ g')`. Rewrite using `[map_mul (sig ρ γ) (af * e₀)]`. Clear the denominators using the available nonvanishing facts. Rewrite using `[e]`.

Conclude with `h2.mul h3.regAt`. Establish `hunit : UnitAt x (h * g)`. Rewrite using `[hsplit]`. Conclude with `UnitAt.add_zeroAt ha hrest`. Establish `hh0 : h ≠ 0` using `fun e => by`.

Use `hunit.ne_zero` as an intermediate fact. Rewrite `this` using `[e, zero_mul]`. Conclude with `this rfl`. Use `⟨(Units.mk0 h hh0)⁻¹, fun δ => ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[map_inv]`.

Use `congr 1`. Use `ext`. Rewrite using `[fnAct_val, Units.val_mk0, hinvh]`. Rewrite using `[CartierDiv.isEqn_iff_generatesAt_inv, Units.val_inv_eq_inv_val, inv_inv, Units.val_mk0]`. Conclude with `hg.generatesAt_iff.2 hunit`.
-/
theorem exists_invariant_isEqn : ∀ (F : Type) [Field F] [CharZero F] (X W : Scheme.{0}) [IsIntegral X] (s : X ⟶ Sp F)
    (Γ : Type) [Group Γ] [Finite Γ] (ρ : Γ →* Aut X) (q : X ⟶ W), IsAffineQuotient ρ q → ∀ (D : CartierDiv X),
    (∀ γ x g, D.IsEqn ((ρ γ).hom x) g → D.IsEqn x (fnAct ρ γ g)) →
    (∀ γ x g, X.fromSpecResidueField x ≫ (ρ γ).hom = X.fromSpecResidueField x → D.IsEqn x g →
      ZeroAt x (((fnAct ρ γ g * g⁻¹ : X.functionFieldˣ) : X.functionField) - 1)) →
    ∀ x : X, ∃ g : X.functionFieldˣ, (∀ γ, fnAct ρ γ g = g) ∧ D.IsEqn x g := by
  intro F _ _ X W _ s Γ _ _ ρ q hq D hinv hin x
  classical
  haveI := Fintype.ofFinite Γ
  obtain ⟨_, ⟨V, hV, rfl⟩, hxV, -⟩ :=
    W.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ (q x)) isOpen_univ
  have := hq.isAffineHom
  have hU : IsAffineOpen (q ⁻¹ᵁ V) := hV.preimage q
  have hxU : x ∈ q ⁻¹ᵁ V := hxV
  have horb (γ : Γ) : (ρ γ).hom x ∈ q ⁻¹ᵁ V := by
    have e : q ((ρ γ).hom x) = q x := congr($(hq.comp_eq γ) x)
    show q _ ∈ V
    rw [e]; exact hxV
  let T : Finset X := Finset.univ.image fun γ : Γ => (ρ γ).hom x
  have hT (y : X) : y ∈ T ↔ ∃ γ, (ρ γ).hom x = y := by simp [T]
  obtain ⟨e₀, he₀, hv⟩ := GlobalTheory.T.exists_cartierSection_generatesAt_vanishesAt_finset X (q ⁻¹ᵁ V) hU D x hxU T
    (fun y hy => by obtain ⟨γ, rfl⟩ := (hT y).1 hy; exact horb γ)
    (fun y hy hne hc => by
      obtain ⟨γ, rfl⟩ := (hT y).1 hy
      exact hne (eq_of_mem_closure ρ γ x hc))
  have he0 : e₀ ≠ 0 := he₀.ne_zero
  set g : X.functionFieldˣ := (Units.mk0 e₀ he0)⁻¹ with hgdef
  have hgv : (g : X.functionField) = e₀⁻¹ := by simp [hgdef]
  have hg : D.IsEqn x g := CartierDiv.isEqn_iff_generatesAt_inv.2 (by rw [hgv, inv_inv]; exact he₀)

  have hgs (γ : Γ) (hγ : (ρ γ).hom x = x) : D.IsEqn x (fnAct ρ γ g) :=
    hinv γ x g (by rw [hγ]; exact hg)
  let ι := {γ : Γ // (ρ γ).hom x = x}
  let σ : ι → X.functionField →+* X.functionField := fun i => sig ρ i.1
  let u : ι → X.functionField := fun i => (g : X.functionField) / sig ρ i.1 g
  have hu (i : ι) : UnitAt x (u i) := by
    have := (hg.iff_unitAt.1 (hgs i.1 i.2)).inv
    rw [fnAct_val, inv_div] at this
    exact this
  have hnat (n : ℕ) (hn : n ≠ 0) : UnitAt x (n : X.functionField) := by
    let φF := (Scheme.ΓSpecIso (CommRingCat.of F)).inv ≫ s.appTop ≫ X.presheaf.germ ⊤ x trivial
    refine ⟨(n : X.presheaf.stalk x), ?_, map_natCast _ n⟩
    rw [← map_natCast φF.hom n]
    exact (IsUnit.mk0 (n : F) (Nat.cast_ne_zero.2 hn)).map _
  obtain ⟨a, ha⟩ := GlobalTheory.T.exists_affineFunction_weighted_translates_unitAt X (q ⁻¹ᵁ V) hU x hxU ι σ u
    (fun i f hf => regAt_sig ρ i.1 (by rw [i.2]; exact hf))
    (fun i f hf => zeroAt_sig ρ i.1 (by rw [i.2]; exact hf))
    (fun i => (hu i).regAt)
    (fun i hi => by
      have hfr := fromSpecResidueField_comp_eq_of_fixes X Γ ρ i.1 x i.2
        (fun v hv => by rw [fnAct_val]; exact hi v hv)
      have h1 := hin i.1 x g hfr hg
      rw [Units.val_mul, fnAct_val, Units.val_inv_eq_inv_val g] at h1
      have hs0 : sig ρ i.1 g ≠ 0 := by rw [← fnAct_val]; exact Units.ne_zero _
      have hg0 : (g : X.functionField) ≠ 0 := Units.ne_zero _
      have e : u i - 1 = (sig ρ i.1 g * (g : X.functionField)⁻¹ - 1) * ((-1) * u i) := by
        simp only [u]; field_simp; ring
      rw [e]
      exact h1.mul (RegAt.mul (⟨-1, by rw [map_neg, map_one]⟩ : RegAt x (-1)) (hu i).regAt))
    hnat
    ⟨⟨1, by rw [map_one]; rfl⟩, fun f _ => by
      simp only [σ, sig_one, sub_self]; exact zeroAt_zero x⟩
  set af := fnOf (q ⁻¹ᵁ V) (gen_mem hxU) a with haf
  set h : X.functionField := ∑ γ : Γ, sig ρ γ (af * e₀) with hh

  have hinvh (δ : Γ) : sig ρ δ h = h := by
    rw [hh, map_sum]
    simp only [sig_sig]
    exact Equiv.sum_comp (Equiv.mulRight δ) (fun γ => sig ρ γ (af * e₀))

  have hsplit : h * g = ∑ i : ι, σ i af * u i +
      ∑ γ ∈ Finset.univ.filter (fun γ : Γ => ¬ (ρ γ).hom x = x), sig ρ γ (af * e₀) * g := by
    rw [hh, Finset.sum_mul, ← Finset.sum_filter_add_sum_filter_not Finset.univ
      (fun γ : Γ => (ρ γ).hom x = x)]
    congr 1
    rw [Finset.sum_subtype (p := fun γ : Γ => (ρ γ).hom x = x) _ (fun γ => by simp)]
    refine Finset.sum_congr rfl fun i _ => ?_
    have hs0 : sig ρ i.1 g ≠ 0 := by rw [← fnAct_val]; exact Units.ne_zero _
    simp only [σ, u, map_mul, hgv, map_inv₀]
    rw [← hgv]
    field_simp
  have hrest : ZeroAt x (∑ γ ∈ Finset.univ.filter (fun γ : Γ => ¬ (ρ γ).hom x = x),
      sig ρ γ (af * e₀) * g) := by
    refine Finset.sum_induction _ (ZeroAt x) (fun _ _ h h' => h.add h') (zeroAt_zero x)
      fun γ hγ => ?_
    have hne : (ρ γ).hom x ≠ x := (Finset.mem_filter.1 hγ).2
    obtain ⟨g', hg', hz⟩ := hv _ ((hT _).2 ⟨γ, rfl⟩) hne
    have hz' : ZeroAt ((ρ γ).hom x) (af * e₀ * g') := by
      have e : af * e₀ * g' = e₀ * g' * af := by ring
      rw [e]
      exact hz.mul (regAt_fnOf (horb γ) _ a)
    have h2 := zeroAt_sig ρ γ hz'
    have h3 : UnitAt x ((g : X.functionField) / fnAct ρ γ g') :=
      (hinv γ x g' hg').iff_unitAt.1 hg
    rw [fnAct_val] at h3
    have hs0 : sig ρ γ g' ≠ 0 := by rw [← fnAct_val]; exact Units.ne_zero _
    have e : sig ρ γ (af * e₀) * g = sig ρ γ (af * e₀ * g') * ((g : X.functionField) / sig ρ γ g') := by
      rw [map_mul (sig ρ γ) (af * e₀)]; field_simp
    rw [e]
    exact h2.mul h3.regAt
  have hunit : UnitAt x (h * g) := by
    rw [hsplit]; exact UnitAt.add_zeroAt ha hrest
  have hh0 : h ≠ 0 := fun e => by
    have := hunit.ne_zero; rw [e, zero_mul] at this; exact this rfl
  refine ⟨(Units.mk0 h hh0)⁻¹, fun δ => ?_, ?_⟩
  · rw [map_inv]
    congr 1
    ext
    rw [fnAct_val, Units.val_mk0, hinvh]
  · rw [CartierDiv.isEqn_iff_generatesAt_inv, Units.val_inv_eq_inv_val, inv_inv, Units.val_mk0]
    exact hg.generatesAt_iff.2 hunit

end GlobalTheory.InvEqn

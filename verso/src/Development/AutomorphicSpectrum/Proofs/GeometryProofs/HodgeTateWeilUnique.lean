import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.GenWeil
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.GlueApplyOfNotInFibre
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsHTFormOver
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.TorsionEmbeddingGeometricPointsStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.SectionEqZeroOfValuesStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsUniqueTangentDualNumberStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsExcisionNbhdAway
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LatticeRegularAtLocalPoint
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsStalkFractionOfGeneric

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.HtUniq

open GlobalTheory.CompanionTheory.Ar.LieTangent GlobalTheory.CompanionTheory.Ar.RootHt.LieFun

/- English proof (translation)
Unfold `secVal`. Establish `e` using `Scheme.Hom.map_appLE x h₁ (homOfLE hle).op`. Establish `e2` using `congrArg (fun g => g.hom f) e`. Simplify using `only [CommRingCat.hom_comp, RingHom.comp_apply] at e2`. Rewrite using `[e2]`.
-/
theorem secVal_res {B : Type} [CommRing B] {Z : Scheme.{0}} (x : Spec (CommRingCat.of B) ⟶ Z) {W W₁ : Z.Opens}
    (hle : W₁ ≤ W) (h : ⊤ ≤ x ⁻¹ᵁ W) (h₁ : ⊤ ≤ x ⁻¹ᵁ W₁) (f : Γ(Z, W)) :
    secVal x W₁ h₁ (Z.presheaf.map (homOfLE hle).op f) = secVal x W h f := by
  unfold secVal
  have e := Scheme.Hom.map_appLE x h₁ (homOfLE hle).op
  have e2 := congrArg (fun g => g.hom f) e
  simp only [CommRingCat.hom_comp, RingHom.comp_apply] at e2
  rw [e2]

/- English proof (translation)
Unfold `secVal`. Establish `e` using `Scheme.Hom.appLE_comp_appLE y i W (i ⁻¹ᵁ W) ⊤ le_rfl h`. Establish `e2` using `congrArg (fun g => g.hom f) e`. Simplify using `only [CommRingCat.hom_comp, RingHom.comp_apply] at e2`. Rewrite using `[e2]`.
-/
theorem secVal_comp {B : Type} [CommRing B] {Y Z : Scheme.{0}} (y : Spec (CommRingCat.of B) ⟶ Y) (i : Y ⟶ Z)
    (W : Z.Opens) (h : ⊤ ≤ y ⁻¹ᵁ (i ⁻¹ᵁ W)) (h' : ⊤ ≤ (y ≫ i) ⁻¹ᵁ W) (f : Γ(Z, W)) :
    secVal y (i ⁻¹ᵁ W) h ((i.appLE W (i ⁻¹ᵁ W) le_rfl).hom f) = secVal (y ≫ i) W h' f := by
  unfold secVal
  have e := Scheme.Hom.appLE_comp_appLE y i W (i ⁻¹ᵁ W) ⊤ le_rfl h
  have e2 := congrArg (fun g => g.hom f) e
  simp only [CommRingCat.hom_comp, RingHom.comp_apply] at e2
  rw [e2]

/- English proof (translation)
Unfold `secVal`. Establish `e` using `Scheme.Hom.appLE_comp_appLE (Spec.map (CommRingCat.ofHom φ)) x W ⊤ ⊤ h le_top`. Establish `e3 : Scheme.Hom.appLE (Spec.map (CommRingCat.ofHom φ)) ⊤ ⊤ le_top = Scheme.Hom.appTop (Spec.map (CommRingCat.ofHom φ))`. Simplify using `[Scheme.Hom.appLE]`. Rewrite `e` using `[e3]`.

Establish `n1` using `Scheme.ΓSpecIso_naturality (CommRingCat.ofHom φ)`. Establish `e2` using `congrArg (fun g => g.hom f) e`. Simplify using `only [CommRingCat.hom_comp, RingHom.comp_apply] at e2`. Establish `n2` using `congrArg (fun g => g.hom ((Scheme.Hom.appLE x W ⊤ h).hom f)) n1`. Simplify using `only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at n2`.

Rewrite using `[← e2, n2]`.
-/
theorem secVal_base {B B' : Type} [CommRing B] [CommRing B'] (φ : B →+* B') {Z : Scheme.{0}}
    (x : Spec (CommRingCat.of B) ⟶ Z) (W : Z.Opens) (h : ⊤ ≤ x ⁻¹ᵁ W)
    (h' : ⊤ ≤ (Spec.map (CommRingCat.ofHom φ) ≫ x) ⁻¹ᵁ W) (f : Γ(Z, W)) :
    secVal (Spec.map (CommRingCat.ofHom φ) ≫ x) W h' f = φ (secVal x W h f) := by
  unfold secVal
  have e := Scheme.Hom.appLE_comp_appLE (Spec.map (CommRingCat.ofHom φ)) x W ⊤ ⊤ h le_top
  have e3 : Scheme.Hom.appLE (Spec.map (CommRingCat.ofHom φ)) ⊤ ⊤ le_top =
      Scheme.Hom.appTop (Spec.map (CommRingCat.ofHom φ)) := by
    simp [Scheme.Hom.appLE]
  rw [e3] at e
  have n1 := Scheme.ΓSpecIso_naturality (CommRingCat.ofHom φ)
  have e2 := congrArg (fun g => g.hom f) e
  simp only [CommRingCat.hom_comp, RingHom.comp_apply] at e2
  have n2 := congrArg (fun g => g.hom ((Scheme.Hom.appLE x W ⊤ h).hom f)) n1
  simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at n2
  rw [← e2, n2]

/- English proof (translation)
Simplify using `[secVal]`.
-/
theorem secVal_sub {B : Type} [CommRing B] {Z : Scheme.{0}} (x : Spec (CommRingCat.of B) ⟶ Z) (W : Z.Opens)
    (h : ⊤ ≤ x ⁻¹ᵁ W) (f g : Γ(Z, W)) : secVal x W h (f - g) = secVal x W h f - secVal x W h g := by
  simp [secVal]

/- English proof (translation)
Substitute `e` using the available equality. Both sides reduce to the same expression.
-/
theorem secVal_congr {B : Type} [CommRing B] {Z : Scheme.{0}} {x y : Spec (CommRingCat.of B) ⟶ Z} (e : x = y)
    (W : Z.Opens) (h : ⊤ ≤ x ⁻¹ᵁ W) (h' : ⊤ ≤ y ⁻¹ᵁ W) (f : Γ(Z, W)) : secVal x W h f = secVal y W h' f := by
  subst e
  rfl

/- English proof (translation)
Introduce `z _`. Take `⟨z'⟩ : Nonempty (PrimeSpectrum B)` from `inferInstance`. Establish `e : z = Spec.map (CommRingCat.ofHom φ) z'` using `Subsingleton.elim (α := PrimeSpectrum k) _ _`. Rewrite using `[e]`. Conclude with `@h z' trivial`.
-/
theorem le_of_field {k B : Type} [Field k] [CommRing B] [Nontrivial B] (φ : k →+* B) {Z : Scheme.{0}}
    (x : Spec (CommRingCat.of k) ⟶ Z) {W : Z.Opens} (h : ⊤ ≤ (Spec.map (CommRingCat.ofHom φ) ≫ x) ⁻¹ᵁ W) :
    ⊤ ≤ x ⁻¹ᵁ W := by
  intro z _
  obtain ⟨z'⟩ : Nonempty (PrimeSpectrum B) := inferInstance
  have e : z = Spec.map (CommRingCat.ofHom φ) z' := Subsingleton.elim (α := PrimeSpectrum k) _ _
  rw [e]
  exact @h z' trivial

/- English proof (translation)
Introduce `p`. Use `⟨PrimeSpectrum.comap (algebraMap R (DualNumber R)) p, ?_⟩` and prove the remaining obligations. Apply `PrimeSpectrum.ext` to reduce the goal to its premises. Use extensionality with `a`. Express the relevant statement in the definitionally equal form `(algebraMap R (DualNumber R)) a.fst ∈ p.asIdeal ↔ a ∈ p.asIdeal`.

Establish `hsq : ∀ b : R, (TrivSqZeroExt.inr b : DualNumber R) ∈ p.asIdeal` using `fun b => p.2.mem_of_pow_mem 2 (by`. Rewrite using `[pow_two, TrivSqZeroExt.inr_mul_inr]`. Conclude with `p.asIdeal.zero_mem)`. Establish `ha : a = algebraMap R (DualNumber R) a.fst + TrivSqZeroExt.inr a.snd`. Rewrite using `[TrivSqZeroExt.algebraMap_eq_inl, TrivSqZeroExt.inl_fst_add_inr_snd_eq]`.

Prove the components needed by the constructor for the conclusion. Introduce `h`. Rewrite using `[ha]`. Conclude with `p.asIdeal.add_mem h (hsq _)`. Introduce `h`.

Establish `: algebraMap R (DualNumber R) a.fst = a - TrivSqZeroExt.inr a.snd` using `by nth_rw 2 [ha]; ring`. Rewrite using `[this]`. Conclude with `p.asIdeal.sub_mem h (hsq _)`.
-/
theorem spec_fst_surj (R : Type) [CommRing R] :
    Function.Surjective (Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom R R R).toRingHom)) := by
  intro p
  refine ⟨PrimeSpectrum.comap (algebraMap R (DualNumber R)) p, ?_⟩
  apply PrimeSpectrum.ext
  ext a
  change (algebraMap R (DualNumber R)) a.fst ∈ p.asIdeal ↔ a ∈ p.asIdeal
  have hsq : ∀ b : R, (TrivSqZeroExt.inr b : DualNumber R) ∈ p.asIdeal := fun b =>
    p.2.mem_of_pow_mem 2 (by
      rw [pow_two, TrivSqZeroExt.inr_mul_inr]
      exact p.asIdeal.zero_mem)
  have ha : a = algebraMap R (DualNumber R) a.fst + TrivSqZeroExt.inr a.snd := by
    rw [TrivSqZeroExt.algebraMap_eq_inl, TrivSqZeroExt.inl_fst_add_inr_snd_eq]
  constructor
  · intro h
    rw [ha]
    exact p.asIdeal.add_mem h (hsq _)
  · intro h
    have : algebraMap R (DualNumber R) a.fst = a - TrivSqZeroExt.inr a.snd := by
      nth_rw 2 [ha]; ring
    rw [this]
    exact p.asIdeal.sub_mem h (hsq _)

section
variable {X : Scheme.{0}} {Ω : Type} [Field Ω] {G : Over X} [GrpObj G] {ξ : Spec (CommRingCat.of Ω) ⟶ X}

/- English proof (translation)
Rewrite using `[Hom.one_def, Over.comp_left]`. Use `congr 1`.
-/
theorem one_left {T : Scheme.{0}} (x : T ⟶ X) : (1 : Over.mk x ⟶ G).left = x ≫ (η[G]).left := by
  rw [Hom.one_def, Over.comp_left]
  congr 1

/- English proof (translation)
Introduce `z _`. Take `⟨p, rfl⟩` from `spec_fst_surj (X.presheaf.stalk q) z`. Express the relevant statement in the definitionally equal form `v.left _ ∈ W`. Establish `e : (Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom (X.presheaf.stalk q) (X.presheaf.stalk q) (X.presheaf.stalk q)).toRingHom) ≫ v.left) p = (X.fromSpecStalk q ≫ (η[G]).left) p`. Rewrite using `[hv, one_left]`.

Both sides reduce to the same expression. Establish `e' : v.left ((Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom (X.presheaf.stalk q) (X.presheaf.stalk q) (X.presheaf.stalk q)).toRingHom)) p) = (η[G]).left (X.fromSpecStalk q p)` using `by simpa using e`. Rewrite using `[e']`. Establish `hs : X.fromSpecStalk q p ⤳ q`. Establish `: X.fromSpecStalk q p ∈ Set.range (X.fromSpecStalk q)` using `⟨p, rfl⟩`.

Rewrite `this` using `[Scheme.range_fromSpecStalk]`. Then use the resulting hypothesis. Conclude with `(hs.map (η[G]).left.continuous).mem_open W.isOpen hW`.
-/
theorem tan_le {q : X} (v : epsAt (R := X.presheaf.stalk q) (X.fromSpecStalk q) ⟶ G)
    (hv : IsTanAt G _ v) {W : G.left.Opens} (hW : (η[G]).left q ∈ W) : ⊤ ≤ v.left ⁻¹ᵁ W := by
  intro z _
  obtain ⟨p, rfl⟩ := spec_fst_surj (X.presheaf.stalk q) z
  change v.left _ ∈ W
  have e : (Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom (X.presheaf.stalk q) (X.presheaf.stalk q)
      (X.presheaf.stalk q)).toRingHom) ≫ v.left) p = (X.fromSpecStalk q ≫ (η[G]).left) p := by
    rw [hv, one_left]
    rfl
  have e' : v.left ((Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom (X.presheaf.stalk q) (X.presheaf.stalk q)
      (X.presheaf.stalk q)).toRingHom)) p) = (η[G]).left (X.fromSpecStalk q p) := by simpa using e
  rw [e']
  have hs : X.fromSpecStalk q p ⤳ q := by
    have : X.fromSpecStalk q p ∈ Set.range (X.fromSpecStalk q) := ⟨p, rfl⟩
    rwa [Scheme.range_fromSpecStalk] at this
  exact (hs.map (η[G]).left.continuous).mem_open W.isOpen hW

/- English proof (translation)
Set `j : Ω →+* AlgebraicClosure Ω` to `algebraMap _ _`. Set `dl : Over.mk (spMap j ≫ ξ) ⟶ Over.mk ξ` to `Over.homMk (spMap j) rfl`. Establish `hgk : (dl ≫ g) ^ n = 1` using `by rw [← MonObj.comp_pow, hg, MonObj.comp_one]`. Establish `hW` using `(GW.weil y g hy hg (AlgebraicClosure Ω) j (dl ≫ y) (dl ≫ g) (Units.map j.toMonoidHom (e y g)) rfl rfl).2 rfl`. Establish `h' : ⊤ ≤ (dl ≫ g).left ⁻¹ᵁ W` using `fun z _ => @h (spMap j z) trivial`.

Establish `e1` using `hw _ j (dl ≫ y) (dl ≫ g) _ h' rfl hgk hW`. Establish `e2` using `secVal_base j g.left W h h' f`. Apply `j.injective` to reduce the goal to its premises. Conclude with `e2.symm.trans e1`.
-/
theorem val_eq {L : LB G.left} {n : ℕ} {e : (Over.mk ξ ⟶ G) → (Over.mk ξ ⟶ G) → Ωˣ} (GW : GenWeil G L ξ n e)
    {y g : Over.mk ξ ⟶ G} (hy : y ^ n = 1) (hg : g ^ n = 1) {W : G.left.Opens} {f : Γ(G.left, W)}
    (hw : ∀ (k : Type) [Field k] [IsAlgClosed k] (i : Ω →+* k) (xk g : Over.mk (spMap i ≫ ξ) ⟶ G) (c : kˣ)
      (h : ⊤ ≤ g.left ⁻¹ᵁ W), xk.left = spMap i ≫ y.left → g ^ n = 1 →
        Out.WeilIs G L n xk g (unitOn c) → secVal (B := k) g.left W h f = c)
    (h : ⊤ ≤ g.left ⁻¹ᵁ W) : secVal g.left W h f = (e y g : Ω) := by
  let j : Ω →+* AlgebraicClosure Ω := algebraMap _ _
  let dl : Over.mk (spMap j ≫ ξ) ⟶ Over.mk ξ := Over.homMk (spMap j) rfl
  have hgk : (dl ≫ g) ^ n = 1 := by rw [← MonObj.comp_pow, hg, MonObj.comp_one]
  have hW := (GW.weil y g hy hg (AlgebraicClosure Ω) j (dl ≫ y) (dl ≫ g) (Units.map j.toMonoidHom (e y g)) rfl rfl).2 rfl
  have h' : ⊤ ≤ (dl ≫ g).left ⁻¹ᵁ W := fun z _ => @h (spMap j z) trivial
  have e1 := hw _ j (dl ≫ y) (dl ≫ g) _ h' rfl hgk hW
  have e2 := secVal_base j g.left W h h' f
  apply j.injective
  exact e2.symm.trans e1
end

section
variable {X : Scheme.{0}} [IsLocallyNoetherian X] {Ω : Type} [Field Ω] [CharZero Ω] {ξ : Spec (CommRingCat.of Ω) ⟶ X}

/- English proof (translation)
Use `letI : Algebra (X.presheaf.stalk q.1) Ω := (genMap ξ q).toAlgebra`. Use `haveI : IsDomain (X.presheaf.stalk q.1) := (hξ.inj q).isDomain _`. Use `haveI : FaithfulSMul (X.presheaf.stalk q.1) Ω := (faithfulSMul_iff_algebraMap_injective _ _).2 (hξ.inj q)`. Use `haveI : IsFractionRing (X.presheaf.stalk q.1) Ω := IsFractionRing.of_field _ _ fun z => by`. Take `⟨b, c, hc, e⟩` from `GlobalTheory.CompanionTheory.Ar.exists_frac_genMap ξ hξ q z`.

Conclude with `⟨b, c, eq_div_of_mul_eq hc e⟩`. Conclude with `⟨(FractionRing.algEquiv _ Ω).toRingEquiv, fun r => (FractionRing.algEquiv _ Ω).commutes r⟩`.
-/
theorem exists_frac (hξ : IsCptGen ξ) (q : Cpt ξ) :
    ∃ κ : FractionRing (X.presheaf.stalk q.1) ≃+* Ω, ∀ r, κ (algebraMap _ _ r) = genMap ξ q r := by
  letI : Algebra (X.presheaf.stalk q.1) Ω := (genMap ξ q).toAlgebra
  haveI : IsDomain (X.presheaf.stalk q.1) := (hξ.inj q).isDomain _
  haveI : FaithfulSMul (X.presheaf.stalk q.1) Ω := (faithfulSMul_iff_algebraMap_injective _ _).2 (hξ.inj q)
  haveI : IsFractionRing (X.presheaf.stalk q.1) Ω := IsFractionRing.of_field _ _ fun z => by
    obtain ⟨b, c, hc, e⟩ := GlobalTheory.CompanionTheory.Ar.exists_frac_genMap ξ hξ q z
    exact ⟨b, c, eq_div_of_mul_eq hc e⟩
  exact ⟨(FractionRing.algEquiv _ Ω).toRingEquiv, fun r => (FractionRing.algEquiv _ Ω).commutes r⟩

/- English proof (translation)
Use `ext_of_injective i.injective ?_ h` and prove the remaining obligations. Establish `e` using `congrArg (fun m => m (IsLocalRing.closedPoint k)) h`. Establish `c : (Spec.map (CommRingCat.ofHom i)) (IsLocalRing.closedPoint k) = IsLocalRing.closedPoint Ω` using `Subsingleton.elim (α := PrimeSpectrum Ω) _ _`. Simplify `e` using `[c]`.
-/
theorem spec_cancel {k : Type} [Field k] (i : Ω →+* k) {Y : Scheme.{0}} {a b : Spec (CommRingCat.of Ω) ⟶ Y}
    (h : Spec.map (CommRingCat.ofHom i) ≫ a = Spec.map (CommRingCat.ofHom i) ≫ b) : a = b := by
  refine ext_of_injective i.injective ?_ h
  have e := congrArg (fun m => m (IsLocalRing.closedPoint k)) h
  have c : (Spec.map (CommRingCat.ofHom i)) (IsLocalRing.closedPoint k) = IsLocalRing.closedPoint Ω :=
    Subsingleton.elim (α := PrimeSpectrum Ω) _ _
  simpa [c] using e

/- English proof (translation)
Use `haveI : IsCommMonObj G := hG.comm`. Use `haveI : CharZero (X.presheaf.stalk q.1) := (RingHom.charZero_iff (hξ.inj q)).2 inferInstance`. Set `b : Spec (CommRingCat.of (FractionRing (X.presheaf.stalk q.1))) ⟶ Spec (CommRingCat.of Ω)` to `spMap (κ.symm : Ω →+* FractionRing (X.presheaf.stalk q.1))`. Establish `hcomp : (κ.symm : Ω →+* FractionRing (X.presheaf.stalk q.1)).comp (genMap ξ q) = algebraMap _ _`. Use extensionality with `r`.

Simplify using `[← hκ r]`. Establish `hb : b ≫ ξ = (BT.genPt (X.presheaf.stalk q.1)).hom ≫ X.fromSpecStalk q.1`. Establish `h0` using `spec_genMap ξ q`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[spec_comp, hcomp]`.

Set `β : Over.mk ((BT.genPt (X.presheaf.stalk q.1)).hom ≫ X.fromSpecStalk q.1) ⟶ Over.mk ξ` to `Over.homMk b hb`. Set `T : Subgroup (Over.mk ξ ⟶ G)` to `(powMonoidHom n : (Over.mk ξ ⟶ G) →* (Over.mk ξ ⟶ G)).ker`. Establish `hTm : ∀ t : T, (t : Over.mk ξ ⟶ G) ^ n = 1` using `fun t => t.2`. Use `haveI : Finite T := by haveI := GW.finite`. Conclude with `Finite.of_injective (fun t : T => (⟨t.1, hTm t⟩ : {x : Over.mk ξ ⟶ G // x ^ n = 1})) (fun a c h => Subtype.ext (congrArg Subtype.val h))`.

Set `τ : T →* (Over.mk ((BT.genPt (X.presheaf.stalk q.1)).hom ≫ X.fromSpecStalk q.1) ⟶ G)` to `{ toFun := fun t => β ≫ t.1 map_one' := MonObj.comp_one _ map_mul' := fun a c => MonObj.comp_mul _ _ _ }`. Establish `hinv : spMap (κ : FractionRing (X.presheaf.stalk q.1) →+* Ω) ≫ b = 𝟙 _` using `by show Spec.map _ ≫ Spec.map _ = _`. Rewrite using `[spec_comp]`. Establish `: (κ : FractionRing (X.presheaf.stalk q.1) →+* Ω).comp (κ.symm : Ω →+* FractionRing (X.presheaf.stalk q.1)) = RingHom.id _` using `by ext; simp`. Rewrite using `[this, CommRingCat.ofHom_id, Spec.map_id]`.

Establish `τinj : Function.Injective τ`. Introduce `a c h`. Apply `Subtype.ext` to reduce the goal to its premises. Apply `Over.OverMorphism.ext` to reduce the goal to its premises. Establish `h1 : b ≫ (a.1).left = b ≫ (c.1).left` using `congrArg (fun m => m.left) h`.

Combine the equalities or inequalities in the displayed calculation. Rewrite using `[hinv]`. Conclude with `(Category.id_comp _).symm`. Use `_ = (spMap (κ : FractionRing (X.presheaf.stalk q.1) →+* Ω) ≫ b) ≫ (c.1).left := by`. Rewrite using `[Category.assoc, h1, Category.assoc]`.

Use `_ = (c.1).left := by rw [hinv]; exact Category.id_comp _`. Establish `τtors : ∀ t, τ t ^ n = 1` using `fun t => by show (β ≫ t.1) ^ n = 1`. Rewrite using `[← MonObj.comp_pow, hTm t, MonObj.comp_one]`. Establish `geo : ∀ (Ω' : Type) [Field Ω'] [IsAlgClosed Ω'] (a : FractionRing (X.presheaf.stalk q.1) →+* Ω') (g : Over.mk (Spec.map (CommRingCat.ofHom a) ≫ (BT.genPt (X.presheaf.stalk q.1)).hom ≫ X.fromSpecStalk q.1) ⟶ G), g ^ n = 1 → ∃ t, g.left = Spec.map (CommRingCat.ofHom a) ≫ (τ t).left`. Introduce `Ω' _ _ a g hg`.

Set `i : Ω →+* Ω'` to `a.comp (κ.symm : Ω →+* FractionRing (X.presheaf.stalk q.1))`. Establish `hi : spMap i ≫ ξ = Spec.map (CommRingCat.ofHom a) ≫ (BT.genPt (X.presheaf.stalk q.1)).hom ≫ X.fromSpecStalk q.1`. Rewrite using `[← hb, ← Category.assoc]`. Use `congr 1`. Conclude with `(spec_comp _ _).symm`.

Set `c : Over.mk (spMap i ≫ ξ) ⟶ Over.mk (Spec.map (CommRingCat.ofHom a) ≫ (BT.genPt (X.presheaf.stalk q.1)).hom ≫ X.fromSpecStalk q.1)` to `Over.homMk (𝟙 _) (by simpa using hi.symm)`. Establish `hg' : (c ≫ g) ^ n = 1` using `by rw [← MonObj.comp_pow, hg, MonObj.comp_one]`. Take `⟨x₀, hx₀⟩` from `hT Ω' i (c ≫ g) hg'`. Establish `hxl : g.left = spMap i ≫ x₀.left` using `by simpa [c] using hx₀`. Set `dl : Over.mk (spMap i ≫ ξ) ⟶ Over.mk ξ` to `Over.homMk (spMap i) rfl`.

Establish `hdl : dl ≫ x₀ = c ≫ g`. Apply `Over.OverMorphism.ext` to reduce the goal to its premises. Conclude with `hx₀.symm`. Establish `hx1 : x₀ ^ n = 1`. Apply `Over.OverMorphism.ext` to reduce the goal to its premises.

Apply `spec_cancel i` to reduce the goal to its premises. Establish `: dl ≫ x₀ ^ n = dl ≫ 1` using `by rw [MonObj.comp_pow, hdl, hg', MonObj.comp_one]`. Conclude with `congrArg (fun m => m.left) this`. Use `⟨⟨x₀, hx1⟩, ?_⟩` and prove the remaining obligations. Rewrite using `[hxl]`.

Use `show _ = Spec.map (CommRingCat.ofHom a) ≫ b ≫ x₀.left`. Rewrite using `[← Category.assoc]`. Use `congr 1`. Conclude with `(spec_comp _ _).symm`. Take `⟨Γ₀, i, h1, h2⟩` from `GlobalTheory.T.torsion_embedding_geometric_points (X.presheaf.stalk q.1) T X G hG (X.fromSpecStalk q.1) n hn τ τinj τtors geo`.

Conclude with `⟨T, inferInstance, inferInstance, Γ₀, i, h1, fun t => ⟨t.1, hTm t, h2 t⟩⟩`.
-/
theorem exists_gamma (hξ : IsCptGen ξ) {G : Over X} [GrpObj G] (hG : IsSemiAbelian G) {L : LB G.left} {n : ℕ}
    (hn : 1 ≤ n) (hT : FullTorsion G ξ n) {e : (Over.mk ξ ⟶ G) → (Over.mk ξ ⟶ G) → Ωˣ} (GW : GenWeil G L ξ n e)
    (q : Cpt ξ) [IsDomain (X.presheaf.stalk q.1)] (κ : FractionRing (X.presheaf.stalk q.1) ≃+* Ω)
    (hκ : ∀ r, κ (algebraMap _ _ r) = genMap ξ q r) :
    ∃ (T : Type) (_ : CommGroup T) (_ : Finite T) (Γ₀ : BT.QFGroup (X.presheaf.stalk q.1) T) (i : Γ₀.G.left ⟶ G.left),
      Γ₀.IsTorsionAlong G (X.fromSpecStalk q.1) n i ∧
      ∀ t, ∃ g : Over.mk ξ ⟶ G, g ^ n = 1 ∧
        (Γ₀.pt t).left ≫ i = spMap (κ.symm : Ω →+* FractionRing (X.presheaf.stalk q.1)) ≫ g.left := by
  haveI : IsCommMonObj G := hG.comm
  haveI : CharZero (X.presheaf.stalk q.1) := (RingHom.charZero_iff (hξ.inj q)).2 inferInstance
  let b : Spec (CommRingCat.of (FractionRing (X.presheaf.stalk q.1))) ⟶ Spec (CommRingCat.of Ω) :=
    spMap (κ.symm : Ω →+* FractionRing (X.presheaf.stalk q.1))
  have hcomp : (κ.symm : Ω →+* FractionRing (X.presheaf.stalk q.1)).comp (genMap ξ q) = algebraMap _ _ := by
    ext r
    simp [← hκ r]
  have hb : b ≫ ξ = (BT.genPt (X.presheaf.stalk q.1)).hom ≫ X.fromSpecStalk q.1 := by
    have h0 := spec_genMap ξ q
    calc b ≫ ξ = b ≫ (Spec.map (CommRingCat.ofHom (genMap ξ q)) ≫ X.fromSpecStalk q.1) := by rw [h0]
      _ = (b ≫ Spec.map (CommRingCat.ofHom (genMap ξ q))) ≫ X.fromSpecStalk q.1 := (Category.assoc _ _ _).symm
      _ = _ := by
        show (Spec.map _ ≫ Spec.map _) ≫ _ = Spec.map _ ≫ _
        rw [spec_comp, hcomp]
  let β : Over.mk ((BT.genPt (X.presheaf.stalk q.1)).hom ≫ X.fromSpecStalk q.1) ⟶ Over.mk ξ := Over.homMk b hb
  let T : Subgroup (Over.mk ξ ⟶ G) := (powMonoidHom n : (Over.mk ξ ⟶ G) →* (Over.mk ξ ⟶ G)).ker
  have hTm : ∀ t : T, (t : Over.mk ξ ⟶ G) ^ n = 1 := fun t => t.2
  haveI : Finite T := by
    haveI := GW.finite
    exact Finite.of_injective (fun t : T => (⟨t.1, hTm t⟩ : {x : Over.mk ξ ⟶ G // x ^ n = 1}))
      (fun a c h => Subtype.ext (congrArg Subtype.val h))
  let τ : T →* (Over.mk ((BT.genPt (X.presheaf.stalk q.1)).hom ≫ X.fromSpecStalk q.1) ⟶ G) :=
    { toFun := fun t => β ≫ t.1
      map_one' := MonObj.comp_one _
      map_mul' := fun a c => MonObj.comp_mul _ _ _ }
  have hinv : spMap (κ : FractionRing (X.presheaf.stalk q.1) →+* Ω) ≫ b = 𝟙 _ := by
    show Spec.map _ ≫ Spec.map _ = _
    rw [spec_comp]
    have : (κ : FractionRing (X.presheaf.stalk q.1) →+* Ω).comp
      (κ.symm : Ω →+* FractionRing (X.presheaf.stalk q.1)) = RingHom.id _ := by ext; simp
    rw [this, CommRingCat.ofHom_id, Spec.map_id]
  have τinj : Function.Injective τ := by
    intro a c h
    apply Subtype.ext
    apply Over.OverMorphism.ext
    have h1 : b ≫ (a.1).left = b ≫ (c.1).left := congrArg (fun m => m.left) h
    calc (a.1).left = (spMap (κ : FractionRing (X.presheaf.stalk q.1) →+* Ω) ≫ b) ≫ (a.1).left := by
          rw [hinv]; exact (Category.id_comp _).symm
      _ = (spMap (κ : FractionRing (X.presheaf.stalk q.1) →+* Ω) ≫ b) ≫ (c.1).left := by
          rw [Category.assoc, h1, Category.assoc]
      _ = (c.1).left := by rw [hinv]; exact Category.id_comp _
  have τtors : ∀ t, τ t ^ n = 1 := fun t => by
    show (β ≫ t.1) ^ n = 1
    rw [← MonObj.comp_pow, hTm t, MonObj.comp_one]
  have geo : ∀ (Ω' : Type) [Field Ω'] [IsAlgClosed Ω'] (a : FractionRing (X.presheaf.stalk q.1) →+* Ω')
      (g : Over.mk (Spec.map (CommRingCat.ofHom a) ≫ (BT.genPt (X.presheaf.stalk q.1)).hom ≫ X.fromSpecStalk q.1) ⟶ G),
      g ^ n = 1 → ∃ t, g.left = Spec.map (CommRingCat.ofHom a) ≫ (τ t).left := by
    intro Ω' _ _ a g hg
    let i : Ω →+* Ω' := a.comp (κ.symm : Ω →+* FractionRing (X.presheaf.stalk q.1))
    have hi : spMap i ≫ ξ = Spec.map (CommRingCat.ofHom a) ≫ (BT.genPt (X.presheaf.stalk q.1)).hom ≫ X.fromSpecStalk q.1 := by
      rw [← hb, ← Category.assoc]
      congr 1
      exact (spec_comp _ _).symm
    let c : Over.mk (spMap i ≫ ξ) ⟶ Over.mk (Spec.map (CommRingCat.ofHom a) ≫ (BT.genPt (X.presheaf.stalk q.1)).hom ≫ X.fromSpecStalk q.1) :=
      Over.homMk (𝟙 _) (by simpa using hi.symm)
    have hg' : (c ≫ g) ^ n = 1 := by rw [← MonObj.comp_pow, hg, MonObj.comp_one]
    obtain ⟨x₀, hx₀⟩ := hT Ω' i (c ≫ g) hg'
    have hxl : g.left = spMap i ≫ x₀.left := by simpa [c] using hx₀
    let dl : Over.mk (spMap i ≫ ξ) ⟶ Over.mk ξ := Over.homMk (spMap i) rfl
    have hdl : dl ≫ x₀ = c ≫ g := by
      apply Over.OverMorphism.ext
      exact hx₀.symm
    have hx1 : x₀ ^ n = 1 := by
      apply Over.OverMorphism.ext
      apply spec_cancel i
      have : dl ≫ x₀ ^ n = dl ≫ 1 := by rw [MonObj.comp_pow, hdl, hg', MonObj.comp_one]
      exact congrArg (fun m => m.left) this
    refine ⟨⟨x₀, hx1⟩, ?_⟩
    rw [hxl]
    show _ = Spec.map (CommRingCat.ofHom a) ≫ b ≫ x₀.left
    rw [← Category.assoc]
    congr 1
    exact (spec_comp _ _).symm
  obtain ⟨Γ₀, i, h1, h2⟩ := GlobalTheory.T.torsion_embedding_geometric_points (X.presheaf.stalk q.1) T X G hG (X.fromSpecStalk q.1) n hn τ τinj τtors geo
  exact ⟨T, inferInstance, inferInstance, Γ₀, i, h1, fun t => ⟨t.1, hTm t, h2 t⟩⟩
end

section
variable {X : Scheme.{0}} [IsLocallyNoetherian X] {Ω : Type} [Field Ω] [CharZero Ω] {ξ : Spec (CommRingCat.of Ω) ⟶ X}

/- English proof (translation)
Use `haveI : IsCommMonObj G := hG.comm`. Use `haveI : IsDomain (X.presheaf.stalk q.1) := (hξ.inj q).isDomain _`. Take `⟨κ, hκ⟩` from `exists_frac hξ q`. Take `⟨T, _, _, Γ₀, i, hΓ, hpt⟩` from `exists_gamma hξ hG hn hT GW q κ hκ`. Set `V : G.left.Opens` to `W ⊓ W'`.

Set `f₁ : Γ(G.left, V)` to `G.left.presheaf.map (homOfLE (inf_le_left : V ≤ W)).op f`. Set `f₂ : Γ(G.left, V)` to `G.left.presheaf.map (homOfLE (inf_le_right : V ≤ W')).op f'`. Set `s : Γ(Γ₀.G.left, i ⁻¹ᵁ V)` to `(i.appLE V (i ⁻¹ᵁ V) le_rfl).hom (f₁ - f₂)`. Establish `hs : s = 0`. Use `GlobalTheory.T.section_eq_zero_of_values (X.presheaf.stalk q.1) T Γ₀ (i ⁻¹ᵁ V) s fun t ht => ?_` and prove the remaining obligations.

Take `⟨g, hg, hgt⟩` from `hpt t`. Establish `hz : ⊤ ≤ ((Γ₀.pt t).left ≫ i) ⁻¹ᵁ V` using `ht`. Establish `e1 : BT.valAt (Γ₀.pt t).left (i ⁻¹ᵁ V) ht s = secVal ((Γ₀.pt t).left ≫ i) V hz (f₁ - f₂)` using `secVal_comp _ i V ht hz _`. Rewrite using `[e1, secVal_sub]`. Establish `hzW : ⊤ ≤ ((Γ₀.pt t).left ≫ i) ⁻¹ᵁ W` using `fun z _ => (@hz z trivial).1`.

Establish `hzW' : ⊤ ≤ ((Γ₀.pt t).left ≫ i) ⁻¹ᵁ W'` using `fun z _ => (@hz z trivial).2`. Establish `hyW : ⊤ ≤ (spMap (κ.symm : Ω →+* FractionRing (X.presheaf.stalk q.1)) ≫ g.left) ⁻¹ᵁ W` using `hgt ▸ hzW`. Establish `hyW' : ⊤ ≤ (spMap (κ.symm : Ω →+* FractionRing (X.presheaf.stalk q.1)) ≫ g.left) ⁻¹ᵁ W'` using `hgt ▸ hzW'`. Establish `h₀` using `le_of_field _ g.left hyW`. Establish `h₀'` using `le_of_field _ g.left hyW'`.

Rewrite using `[secVal_res _ inf_le_left hzW hz f, secVal_res _ inf_le_right hzW' hz f', secVal_congr hgt W hzW hyW f, secVal_congr hgt W' hzW' hyW' f', secVal_base _ g.left W h₀ hyW f, secVal_base _ g.left W' h₀' hyW' f', hval g h₀ h₀' hg, sub_self]`. Take `⟨e₁, he₁⟩` from `(stalkLie hξ M q).onto v hv.1`. Take `⟨vb, ⟨-, hvb⟩, -⟩` from `GlobalTheory.T.existsUnique_tangent_dual_number (X.presheaf.stalk q.1) T Γ₀ X G (X.fromSpecStalk q.1) n i hΓ (Stalk M q) (stalkLie hξ M q) e₁`. Rewrite `hvb` using `[he₁]`. Establish `hV : ⊤ ≤ v.left ⁻¹ᵁ V` using `fun z _ => ⟨@h z trivial, @h' z trivial⟩`.

Establish `h2 : ⊤ ≤ (Spec.map (CommRingCat.ofHom (dualMap (Ideal.Quotient.mk (Ideal.span {((n : ℕ) : X.presheaf.stalk q.1)})))) ≫ v.left) ⁻¹ᵁ V` using `fun z _ => @hV _ trivial`. Establish `h3 : ⊤ ≤ (vb ≫ i) ⁻¹ᵁ V` using `hvb ▸ h2`. Establish `hP : ⊤ ≤ vb ⁻¹ᵁ (i ⁻¹ᵁ V)` using `h3`. Establish `e1` using `secVal_comp vb i V hP h3 (f₁ - f₂)`. Express the relevant statement in the definitionally equal form `secVal vb (i ⁻¹ᵁ V) hP s = _ at e1`.

Rewrite `e1` using `[hs, secVal_congr hvb V h3 h2, secVal_base _ v.left V hV h2, secVal_sub, secVal_res _ inf_le_left h hV f, secVal_res _ inf_le_right h' hV f']`. Establish `e2` using `congrArg TrivSqZeroExt.snd e1`. Establish `h0 : secVal vb (i ⁻¹ᵁ V) hP 0 = 0` using `by simp [secVal]`. Rewrite `e2` using `[h0, dualMap_snd, TrivSqZeroExt.snd_zero, TrivSqZeroExt.snd_sub]`. Establish `e3` using `Ideal.Quotient.eq_zero_iff_mem.1 e2.symm`.

Take `⟨r₀, hr₀⟩` from `Ideal.mem_span_singleton.1 e3`. Conclude with `⟨r₀, hr₀⟩`.
-/
theorem tangent_congr (hξ : IsCptGen ξ) {G : Over X} [GrpObj G] (hG : IsSemiAbelian G) {L : LB G.left} {n : ℕ}
    (hn : 1 ≤ n) (hT : FullTorsion G ξ n) {e : (Over.mk ξ ⟶ G) → (Over.mk ξ ⟶ G) → Ωˣ} (GW : GenWeil G L ξ n e)
    {E : Type} [AddCommGroup E] [Module Ω E] (M : LieModel G ξ E) (q : Cpt ξ)
    {W W' : G.left.Opens} (f : Γ(G.left, W)) (f' : Γ(G.left, W'))
    (hval : ∀ (g : Over.mk ξ ⟶ G) (h : ⊤ ≤ g.left ⁻¹ᵁ W) (h' : ⊤ ≤ g.left ⁻¹ᵁ W'), g ^ n = 1 →
      secVal g.left W h f = secVal g.left W' h' f')
    {e₀ : E} {v : epsAt (R := X.presheaf.stalk q.1) (X.fromSpecStalk q.1) ⟶ G} (hv : M.Extends q e₀ v)
    (h : ⊤ ≤ v.left ⁻¹ᵁ W) (h' : ⊤ ≤ v.left ⁻¹ᵁ W') :
    ∃ r₀ : X.presheaf.stalk q.1, (secVal (B := DualNumber (X.presheaf.stalk q.1)) v.left W h f).snd -
      (secVal (B := DualNumber (X.presheaf.stalk q.1)) v.left W' h' f').snd = n * r₀ := by
  haveI : IsCommMonObj G := hG.comm
  haveI : IsDomain (X.presheaf.stalk q.1) := (hξ.inj q).isDomain _
  obtain ⟨κ, hκ⟩ := exists_frac hξ q
  obtain ⟨T, _, _, Γ₀, i, hΓ, hpt⟩ := exists_gamma hξ hG hn hT GW q κ hκ
  let V : G.left.Opens := W ⊓ W'
  let f₁ : Γ(G.left, V) := G.left.presheaf.map (homOfLE (inf_le_left : V ≤ W)).op f
  let f₂ : Γ(G.left, V) := G.left.presheaf.map (homOfLE (inf_le_right : V ≤ W')).op f'
  let s : Γ(Γ₀.G.left, i ⁻¹ᵁ V) := (i.appLE V (i ⁻¹ᵁ V) le_rfl).hom (f₁ - f₂)
  have hs : s = 0 := by
    refine GlobalTheory.T.section_eq_zero_of_values (X.presheaf.stalk q.1) T Γ₀ (i ⁻¹ᵁ V) s fun t ht => ?_
    obtain ⟨g, hg, hgt⟩ := hpt t
    have hz : ⊤ ≤ ((Γ₀.pt t).left ≫ i) ⁻¹ᵁ V := ht
    have e1 : BT.valAt (Γ₀.pt t).left (i ⁻¹ᵁ V) ht s = secVal ((Γ₀.pt t).left ≫ i) V hz (f₁ - f₂) :=
      secVal_comp _ i V ht hz _
    rw [e1, secVal_sub]
    have hzW : ⊤ ≤ ((Γ₀.pt t).left ≫ i) ⁻¹ᵁ W := fun z _ => (@hz z trivial).1
    have hzW' : ⊤ ≤ ((Γ₀.pt t).left ≫ i) ⁻¹ᵁ W' := fun z _ => (@hz z trivial).2
    have hyW : ⊤ ≤ (spMap (κ.symm : Ω →+* FractionRing (X.presheaf.stalk q.1)) ≫ g.left) ⁻¹ᵁ W := hgt ▸ hzW
    have hyW' : ⊤ ≤ (spMap (κ.symm : Ω →+* FractionRing (X.presheaf.stalk q.1)) ≫ g.left) ⁻¹ᵁ W' := hgt ▸ hzW'
    have h₀ := le_of_field _ g.left hyW
    have h₀' := le_of_field _ g.left hyW'
    rw [secVal_res _ inf_le_left hzW hz f, secVal_res _ inf_le_right hzW' hz f',
      secVal_congr hgt W hzW hyW f, secVal_congr hgt W' hzW' hyW' f',
      secVal_base _ g.left W h₀ hyW f, secVal_base _ g.left W' h₀' hyW' f', hval g h₀ h₀' hg, sub_self]
  obtain ⟨e₁, he₁⟩ := (stalkLie hξ M q).onto v hv.1
  obtain ⟨vb, ⟨-, hvb⟩, -⟩ := GlobalTheory.T.existsUnique_tangent_dual_number (X.presheaf.stalk q.1) T Γ₀ X G (X.fromSpecStalk q.1) n i hΓ
    (Stalk M q) (stalkLie hξ M q) e₁
  rw [he₁] at hvb
  have hV : ⊤ ≤ v.left ⁻¹ᵁ V := fun z _ => ⟨@h z trivial, @h' z trivial⟩
  have h2 : ⊤ ≤ (Spec.map (CommRingCat.ofHom (dualMap (Ideal.Quotient.mk
      (Ideal.span {((n : ℕ) : X.presheaf.stalk q.1)})))) ≫ v.left) ⁻¹ᵁ V := fun z _ => @hV _ trivial
  have h3 : ⊤ ≤ (vb ≫ i) ⁻¹ᵁ V := hvb ▸ h2
  have hP : ⊤ ≤ vb ⁻¹ᵁ (i ⁻¹ᵁ V) := h3
  have e1 := secVal_comp vb i V hP h3 (f₁ - f₂)
  change secVal vb (i ⁻¹ᵁ V) hP s = _ at e1
  rw [hs, secVal_congr hvb V h3 h2, secVal_base _ v.left V hV h2, secVal_sub, secVal_res _ inf_le_left h hV f,
    secVal_res _ inf_le_right h' hV f'] at e1
  have e2 := congrArg TrivSqZeroExt.snd e1
  have h0 : secVal vb (i ⁻¹ᵁ V) hP 0 = 0 := by simp [secVal]
  rw [h0, dualMap_snd, TrivSqZeroExt.snd_zero, TrivSqZeroExt.snd_sub] at e2
  have e3 := Ideal.Quotient.eq_zero_iff_mem.1 e2.symm
  obtain ⟨r₀, hr₀⟩ := Ideal.mem_span_singleton.1 e3
  exact ⟨r₀, hr₀⟩
end

/- English proof (translation)
Introduce `X _ Ω _ _ ξ hξ _ G _ hG L n hn hT e GW E _ _ M y q w w' hy hw`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨-, W', f', hW', hv', hd'⟩`. Take `⟨-, W, f, hW, hv, hd⟩` from `hw`. Establish `hn0 : (n : Ω) ≠ 0` using `Nat.cast_ne_zero.2 (by omega)`.

Establish `key : ∀ e₀ v, M.Extends q e₀ v → ∃ c ∈ regAt ξ q, w' e₀ - w e₀ = n * c`. Introduce `e₀ v hv₀`. Establish `h` using `tan_le v hv₀.1 hW`. Establish `h'` using `tan_le v hv₀.1 hW'`. Take `⟨r, hr, er⟩` from `hd e₀ v hv₀ h`.

Take `⟨r', hr', er'⟩` from `hd' e₀ v hv₀ h'`. Take `⟨r₀, e₁⟩` from `tangent_congr hξ hG hn hT GW M q f f' (fun g h₁ h₂ hg => by rw [val_eq GW hy hg hv h₁, val_eq GW hy hg hv' h₂]) hv₀ h h'`. Establish `e₂` using `congrArg (genMap ξ q) e₁`. Simplify using `only [map_sub, map_mul, map_natCast] at e₂`. Use `⟨r' - r - genMap ξ q r₀, sub_mem (sub_mem hr' hr) ⟨r₀, rfl⟩, ?_⟩` and prove the remaining obligations.

Rewrite using `[er, er']`. Take the linear combination `-e₂`. Use `⟨(n : Ω)⁻¹ • (w' - w), ?_, ?_⟩` and prove the remaining obligations. Introduce `e₀ he₀`. Take `⟨v, hv₀⟩` from `(M.mem_lat_iff q e₀).1 he₀`.

Take `⟨c, hc, ec⟩` from `key e₀ v hv₀`. Establish `: ((n : Ω)⁻¹ • (w' - w)) e₀ = c`. Simplify using `only [LinearMap.smul_apply, LinearMap.sub_apply, ec, smul_eq_mul]`. Clear the denominators using the available nonvanishing facts. Rewrite using `[this]`.

Conclude with `hc`. Use extensionality with `x`. Simplify using `only [LinearMap.add_apply, LinearMap.smul_apply, LinearMap.sub_apply, nsmul_eq_mul, smul_eq_mul]`. Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree.

Introduce and unpack `⟨u, hu, rfl⟩`. Take `⟨hwm, W, f, hW, hv, hd⟩` from `hw`. Use `⟨(M.omLat q).add_mem hwm (nsmul_mem hu n), W, f, hW, hv, fun e₀ v hv₀ h => ?_⟩` and prove the remaining obligations. Take `⟨r, hr, er⟩` from `hd e₀ v hv₀ h`. Establish `hue : u e₀ ∈ regAt ξ q` using `hu e₀ ((M.mem_lat_iff q e₀).2 ⟨v, hv₀⟩)`.

Use `⟨r + u e₀, add_mem hr hue, ?_⟩` and prove the remaining obligations. Simplify using `only [LinearMap.add_apply, LinearMap.smul_apply, er, nsmul_eq_mul]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem isHTAt_iff : ∀ (X : Scheme.{0}) [IsLocallyNoetherian X] (Ω : Type) [Field Ω] [CharZero Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X), IsCptGen ξ → Flat.NormalCpt ξ → ∀ (G : Over X) [GrpObj G], IsSemiAbelian G → ∀ (L : LB G.left) (n : ℕ), 1 ≤ n → FullTorsion G ξ n → ∀ e, GenWeil G L ξ n e → ∀ (E : Type) [AddCommGroup E] [Module Ω E] (M : LieModel G ξ E) (y : Over.mk ξ ⟶ G) (q : Cpt ξ) (w w' : Module.Dual Ω E), y ^ n = 1 → M.IsHTAt L n y q w → (M.IsHTAt L n y q w' ↔ ∃ u ∈ M.omLat q, w' = w + n • u) := by
  intro X _ Ω _ _ ξ hξ _ G _ hG L n hn hT e GW E _ _ M y q w w' hy hw
  constructor
  · rintro ⟨-, W', f', hW', hv', hd'⟩
    obtain ⟨-, W, f, hW, hv, hd⟩ := hw
    have hn0 : (n : Ω) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
    have key : ∀ e₀ v, M.Extends q e₀ v → ∃ c ∈ regAt ξ q, w' e₀ - w e₀ = n * c := by
      intro e₀ v hv₀
      have h := tan_le v hv₀.1 hW
      have h' := tan_le v hv₀.1 hW'
      obtain ⟨r, hr, er⟩ := hd e₀ v hv₀ h
      obtain ⟨r', hr', er'⟩ := hd' e₀ v hv₀ h'
      obtain ⟨r₀, e₁⟩ := tangent_congr hξ hG hn hT GW M q f f'
        (fun g h₁ h₂ hg => by rw [val_eq GW hy hg hv h₁, val_eq GW hy hg hv' h₂]) hv₀ h h'
      have e₂ := congrArg (genMap ξ q) e₁
      simp only [map_sub, map_mul, map_natCast] at e₂
      refine ⟨r' - r - genMap ξ q r₀, sub_mem (sub_mem hr' hr) ⟨r₀, rfl⟩, ?_⟩
      rw [er, er']
      linear_combination -e₂
    refine ⟨(n : Ω)⁻¹ • (w' - w), ?_, ?_⟩
    · intro e₀ he₀
      obtain ⟨v, hv₀⟩ := (M.mem_lat_iff q e₀).1 he₀
      obtain ⟨c, hc, ec⟩ := key e₀ v hv₀
      have : ((n : Ω)⁻¹ • (w' - w)) e₀ = c := by
        simp only [LinearMap.smul_apply, LinearMap.sub_apply, ec, smul_eq_mul]
        field_simp
      rw [this]
      exact hc
    · ext x
      simp only [LinearMap.add_apply, LinearMap.smul_apply, LinearMap.sub_apply, nsmul_eq_mul, smul_eq_mul]
      field_simp
      ring
  · rintro ⟨u, hu, rfl⟩
    obtain ⟨hwm, W, f, hW, hv, hd⟩ := hw
    refine ⟨(M.omLat q).add_mem hwm (nsmul_mem hu n), W, f, hW, hv, fun e₀ v hv₀ h => ?_⟩
    obtain ⟨r, hr, er⟩ := hd e₀ v hv₀ h
    have hue : u e₀ ∈ regAt ξ q := hu e₀ ((M.mem_lat_iff q e₀).2 ⟨v, hv₀⟩)
    refine ⟨r + u e₀, add_mem hr hue, ?_⟩
    simp only [LinearMap.add_apply, LinearMap.smul_apply, er, nsmul_eq_mul]
    ring

end GlobalTheory.CompanionTheory.Ar.HtUniq

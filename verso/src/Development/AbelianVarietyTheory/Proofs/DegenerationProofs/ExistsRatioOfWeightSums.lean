import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import Development.AbelianVarietyTheory.Definitions.Degenerations.OfDerivationFnOn
import Development.AbelianVarietyTheory.Definitions.Degenerations.PlOrdSomeOfAssociated
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.SemistableFin
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsSplitTorusPointsMulEquiv
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.GeometricallyIntegralIffGeometricallyConnectedOf
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.IsUnitEv
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsWeightedRelationOfMinimalSupportStatement
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsFractionEvalSectionAffineNearPointStatement
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsGenericFunctionFieldPointStatement
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.SplitTorusWeightTestGenericPointRationalPointsStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS

noncomputable section
namespace GlobalTheory.SS.WtRat

section
variable {k : Type} [Field k] {X : Type} [AddCommGroup X] {R : Type} [CommRing R] {s : Sp R ⟶ Sp k}

def chr (t : Over.mk s ⟶ splitTorus (Sp k) X) (χ : X) : R :=
  ev (R := R) t.left ⊤ le_top (charUnit (Sp k) X χ).val

/- English proof (translation)
Rewrite using `[splitTorusPointsEquiv_val]`. Conclude with `ev_top (R := R) t.left le_top _`.
-/
theorem chr_eq (t : Over.mk s ⟶ splitTorus (Sp k) X) (χ : X) :
    chr t χ = (Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom
      (splitTorusPointsEquiv (Sp k) X (Over.mk s) t (Multiplicative.ofAdd χ)).val := by
  rw [splitTorusPointsEquiv_val]
  exact ev_top (R := R) t.left le_top _

/- English proof (translation)
Rewrite using `[chr_eq, chr_eq, chr_eq, map_mul, MonoidHom.mul_apply, Units.val_mul]`. Conclude with `map_mul _ _ _`.
-/
theorem chr_mul (t t' : Over.mk s ⟶ splitTorus (Sp k) X) (χ : X) :
    chr (t * t') χ = chr t χ * chr t' χ := by
  rw [chr_eq, chr_eq, chr_eq, map_mul, MonoidHom.mul_apply, Units.val_mul]
  exact map_mul _ _ _

/- English proof (translation)
Rewrite using `[chr_eq, map_one, MonoidHom.one_apply, Units.val_one]`. Conclude with `map_one _`.
-/
theorem chr_one (χ : X) : chr (1 : Over.mk s ⟶ splitTorus (Sp k) X) χ = 1 := by
  rw [chr_eq, map_one, MonoidHom.one_apply, Units.val_one]
  exact map_one _

/- English proof (translation)
Rewrite using `[chr_eq, chr_eq, chr_eq, ofAdd_add, map_mul, Units.val_mul]`. Conclude with `map_mul _ _ _`.
-/
theorem chr_add (t : Over.mk s ⟶ splitTorus (Sp k) X) (χ χ' : X) :
    chr t (χ + χ') = chr t χ * chr t χ' := by
  rw [chr_eq, chr_eq, chr_eq, ofAdd_add, map_mul, Units.val_mul]
  exact map_mul _ _ _

/- English proof (translation)
Rewrite using `[chr_eq, ofAdd_zero, map_one, Units.val_one]`. Conclude with `map_one _`.
-/
theorem chr_zero (t : Over.mk s ⟶ splitTorus (Sp k) X) : chr t 0 = 1 := by
  rw [chr_eq, ofAdd_zero, map_one, Units.val_one]
  exact map_one _

/- English proof (translation)
Use `(splitTorusPointsEquiv (Sp k) X _).injective (MonoidHom.ext fun χ => Units.ext ?_)` and prove the remaining obligations. Use `(ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of R)).hom).1 ?_` and prove the remaining obligations. Conclude with `(chr_eq t χ.toAdd).symm.trans ((h _).trans (chr_eq t' χ.toAdd))`.
-/
theorem chr_ext {t t' : Over.mk s ⟶ splitTorus (Sp k) X} (h : ∀ χ, chr t χ = chr t' χ) : t = t' := by
  refine (splitTorusPointsEquiv (Sp k) X _).injective (MonoidHom.ext fun χ => Units.ext ?_)
  refine (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of R)).hom).1 ?_
  exact (chr_eq t χ.toAdd).symm.trans ((h _).trans (chr_eq t' χ.toAdd))

/- English proof (translation)
The claim follows from `ev_spMap e t.left ⊤ le_top le_top _`.
-/
theorem chr_comp {R' : Type} [CommRing R'] {s' : Sp R' ⟶ Sp k} (e : R →+* R') (he : spMap e ≫ s = s')
    (t : Over.mk s ⟶ splitTorus (Sp k) X) (χ : X) :
    chr ((Over.homMk (spMap e) he : Over.mk s' ⟶ Over.mk s) ≫ t) χ = e (chr t χ) :=
  ev_spMap e t.left ⊤ le_top le_top _

/- English proof (translation)
Use `⟨(splitTorusPointsEquiv (Sp k) X (Over.mk s)).symm (MonoidHom.toHomUnits ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom.toMonoidHom.comp u)), fun χ => ?_⟩` and prove the remaining obligations. Rewrite using `[chr_eq, MulEquiv.apply_symm_apply]`. Conclude with `congrArg (fun q => CommRingCat.Hom.hom q (u (Multiplicative.ofAdd χ))) (Scheme.ΓSpecIso (CommRingCat.of R)).inv_hom_id`.
-/
theorem exists_chr (s : Sp R ⟶ Sp k) (u : Multiplicative X →* R) :
    ∃ t : Over.mk s ⟶ splitTorus (Sp k) X, ∀ χ, chr t χ = u (Multiplicative.ofAdd χ) := by
  refine ⟨(splitTorusPointsEquiv (Sp k) X (Over.mk s)).symm
    (MonoidHom.toHomUnits ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom.toMonoidHom.comp u)), fun χ => ?_⟩
  rw [chr_eq, MulEquiv.apply_symm_apply]
  exact congrArg (fun q => CommRingCat.Hom.hom q (u (Multiplicative.ofAdd χ)))
    (Scheme.ΓSpecIso (CommRingCat.of R)).inv_hom_id
end

/- English proof (translation)
Set `R` to `AddMonoidAlgebra F X`. Set `sR : Sp R ⟶ Sp k` to `spMap (algebraMap F R) ≫ s`. Set `π : Over.mk sR ⟶ Over.mk s` to `Over.homMk (spMap (algebraMap F R)) rfl`. Take `⟨tR, htR⟩` from `exists_chr (X := X) sR (AddMonoidAlgebra.of F X)`. Set `a : Over.mk sR ⟶ G` to `(tR ≫ i) * (π ≫ g)`.

Set `cH (t : Over.mk s ⟶ splitTorus (Sp k) X) : Multiplicative X →* F` to `{ toFun := fun χ => chr t χ.toAdd, map_one' := chr_zero t, map_mul' := fun x y => chr_add t _ _ }`. Set `e (t : Over.mk s ⟶ splitTorus (Sp k) X) : R →+* F` to `(AddMonoidAlgebra.lift F F X (cH t)).toRingHom`. Establish `hid (t) : spMap (e t) ≫ spMap (algebraMap F R) = 𝟙 _`. Rewrite using `[← Spec.map_comp, ← Spec.map_id]`. Use `congr 1`.

Use extensionality with `x`. Conclude with `(AddMonoidAlgebra.lift F F X (cH t)).commutes x`. Establish `he (t) : spMap (e t) ≫ sR = s`. Rewrite using `[← Category.assoc, hid, Category.id_comp]`. Establish `ha (t) : (Over.homMk (spMap (e t)) (he t) : Over.mk s ⟶ Over.mk sR) ≫ a = (t ≫ i) * g`.

Establish `h1 : (Over.homMk (spMap (e t)) (he t) : Over.mk s ⟶ Over.mk sR) ≫ tR = t`. Use `chr_ext fun χ => ?_` and prove the remaining obligations. Rewrite using `[chr_comp, htR]`. Conclude with `AddMonoidAlgebra.lift_of (cH t) (Multiplicative.ofAdd χ)`. Establish `h2 : (Over.homMk (spMap (e t)) (he t) : Over.mk s ⟶ Over.mk sR) ≫ π = 𝟙 _` using `Over.OverMorphism.ext (hid t)`.

Rewrite using `[MonObj.comp_mul, ← Category.assoc, h1, ← Category.assoc, h2, Category.id_comp]`. Establish `ha' (t) : spMap (e t) ≫ a.left = ((t ≫ i) * g).left` using `congrArg CommaMorphism.left (ha t)`. Establish `hx : spMap (e 1) (IsLocalRing.closedPoint F) ∈ a.left ⁻¹ᵁ U`. Use `h₁ (show IsLocalRing.closedPoint F ∈ (⊤ : (Sp F).Opens) from trivial)` as an intermediate fact. Rewrite `this` using `[← ha']`.

Conclude with `this`. Take `⟨α, β, hβ, hαβ⟩` from `GlobalTheory.T.exists_fraction_evalSection_affine_near_point R (a.left ⁻¹ᵁ U) ((a.left.appLE U _ le_rfl).hom f) _ hx`. Establish `hsum (t) (w : R) (S : Finset X) (hS : w.coeff.support ⊆ S) : e t w = ∑ χ ∈ S, chr t χ * w.coeff χ` using `by show AddMonoidAlgebra.lift F F X (cH t) w = _`. Rewrite using `[AddMonoidAlgebra.lift_apply, Finsupp.sum_of_support_subset _ hS _ (by simp)]`. Conclude with `Finset.sum_congr rfl fun χ _ => mul_comm _ _`.

Use `⟨α.coeff.support ∪ β.coeff.support, β.coeff, α.coeff, ?_, fun t h => ?_⟩` and prove the remaining obligations. Establish `h2` using `hsum 1 β _ (Finset.subset_union_right (s₁ := α.coeff.support))`. Simplify using `only [chr_one, _root_.one_mul] at h2`. Rewrite using `[← h2]`. Introduce `h0`.

Use `hβ ?_` and prove the remaining obligations. Use `show e 1 β ∈ IsLocalRing.maximalIdeal F`. Rewrite using `[h0]`. Conclude with `zero_mem _`. Rewrite using `[← hsum t β _ Finset.subset_union_right, ← hsum t α _ Finset.subset_union_left]`.

Establish `h' : ⊤ ≤ (spMap (e t) ≫ a.left) ⁻¹ᵁ U` using `by rw [ha']; exact h`. Use `Eq.trans ?_ (hαβ F (e t) h')` and prove the remaining obligations. Use `congr 1`. Conclude with `(ev_congr (ha' t).symm U h h' f).trans (ev_appLE (spMap (e t)) a.left U _ le_rfl h' h' f).symm`.
-/
theorem exists_rel {k : Type} [Field k] {G : Over (Sp k)} [GrpObj G] {X : Type} [AddCommGroup X]
    (i : splitTorus (Sp k) X ⟶ G) {F : Type} [Field F] {s : Sp F ⟶ Sp k} (g : Over.mk s ⟶ G)
    (U : G.left.Opens) (f : Γ(G.left, U)) (h₁ : ⊤ ≤ (((1 : Over.mk s ⟶ splitTorus (Sp k) X) ≫ i) * g).left ⁻¹ᵁ U) :
    ∃ (S : Finset X) (p q : X → F), ∑ χ ∈ S, p χ ≠ 0 ∧
      ∀ (t : Over.mk s ⟶ splitTorus (Sp k) X) (h : ⊤ ≤ ((t ≫ i) * g).left ⁻¹ᵁ U),
        ev (R := F) ((t ≫ i) * g).left U h f * ∑ χ ∈ S, chr t χ * p χ = ∑ χ ∈ S, chr t χ * q χ := by
  classical
  let R := AddMonoidAlgebra F X
  let sR : Sp R ⟶ Sp k := spMap (algebraMap F R) ≫ s
  let π : Over.mk sR ⟶ Over.mk s := Over.homMk (spMap (algebraMap F R)) rfl
  obtain ⟨tR, htR⟩ := exists_chr (X := X) sR (AddMonoidAlgebra.of F X)
  let a : Over.mk sR ⟶ G := (tR ≫ i) * (π ≫ g)
  let cH (t : Over.mk s ⟶ splitTorus (Sp k) X) : Multiplicative X →* F :=
    { toFun := fun χ => chr t χ.toAdd, map_one' := chr_zero t, map_mul' := fun x y => chr_add t _ _ }
  let e (t : Over.mk s ⟶ splitTorus (Sp k) X) : R →+* F := (AddMonoidAlgebra.lift F F X (cH t)).toRingHom
  have hid (t) : spMap (e t) ≫ spMap (algebraMap F R) = 𝟙 _ := by
    rw [← Spec.map_comp, ← Spec.map_id]
    congr 1
    ext x
    exact (AddMonoidAlgebra.lift F F X (cH t)).commutes x
  have he (t) : spMap (e t) ≫ sR = s := by
    rw [← Category.assoc, hid, Category.id_comp]
  have ha (t) : (Over.homMk (spMap (e t)) (he t) : Over.mk s ⟶ Over.mk sR) ≫ a = (t ≫ i) * g := by
    have h1 : (Over.homMk (spMap (e t)) (he t) : Over.mk s ⟶ Over.mk sR) ≫ tR = t := by
      refine chr_ext fun χ => ?_
      rw [chr_comp, htR]
      exact AddMonoidAlgebra.lift_of (cH t) (Multiplicative.ofAdd χ)
    have h2 : (Over.homMk (spMap (e t)) (he t) : Over.mk s ⟶ Over.mk sR) ≫ π = 𝟙 _ :=
      Over.OverMorphism.ext (hid t)
    rw [MonObj.comp_mul, ← Category.assoc, h1, ← Category.assoc, h2, Category.id_comp]
  have ha' (t) : spMap (e t) ≫ a.left = ((t ≫ i) * g).left := congrArg CommaMorphism.left (ha t)
  have hx : spMap (e 1) (IsLocalRing.closedPoint F) ∈ a.left ⁻¹ᵁ U := by
    have := h₁ (show IsLocalRing.closedPoint F ∈ (⊤ : (Sp F).Opens) from trivial)
    rw [← ha'] at this
    exact this
  obtain ⟨α, β, hβ, hαβ⟩ := GlobalTheory.T.exists_fraction_evalSection_affine_near_point R (a.left ⁻¹ᵁ U) ((a.left.appLE U _ le_rfl).hom f) _ hx
  have hsum (t) (w : R) (S : Finset X) (hS : w.coeff.support ⊆ S) : e t w = ∑ χ ∈ S, chr t χ * w.coeff χ := by
    show AddMonoidAlgebra.lift F F X (cH t) w = _
    rw [AddMonoidAlgebra.lift_apply, Finsupp.sum_of_support_subset _ hS _ (by simp)]
    exact Finset.sum_congr rfl fun χ _ => mul_comm _ _
  refine ⟨α.coeff.support ∪ β.coeff.support, β.coeff, α.coeff, ?_, fun t h => ?_⟩
  · have h2 := hsum 1 β _ (Finset.subset_union_right (s₁ := α.coeff.support))
    simp only [chr_one, _root_.one_mul] at h2
    rw [← h2]
    intro h0
    refine hβ ?_
    show e 1 β ∈ IsLocalRing.maximalIdeal F
    rw [h0]; exact zero_mem _
  · rw [← hsum t β _ Finset.subset_union_right, ← hsum t α _ Finset.subset_union_left]
    have h' : ⊤ ≤ (spMap (e t) ≫ a.left) ⁻¹ᵁ U := by rw [ha']; exact h
    refine Eq.trans ?_ (hαβ F (e t) h')
    congr 1
    exact (ev_congr (ha' t).symm U h h' f).trans (ev_appLE (spMap (e t)) a.left U _ le_rfl h' h' f).symm

/- English proof (translation)
Introduce `k _ _ G _ hG X _ _ _ i hi U f hU`. Take `⟨hc, hs, -, -, hgc⟩` from `hG`. Establish `: IsIntegral G.left` using `isIntegral_of_smooth_of_geometricallyConnected G.hom`. Take `⟨F, _, g₀, hg, hinj, hσ, hsec⟩` from `GlobalTheory.T.exists_generic_functionField_point G.left`. Set `s : Sp F ⟶ Sp k` to `g₀ ≫ G.hom`.

Set `g : Over.mk s ⟶ G` to `Over.homMk g₀ rfl`. Set `pt (t : 𝟙_ (Over (Sp k)) ⟶ splitTorus (Sp k) X) : Over.mk s ⟶ splitTorus (Sp k) X` to `toUnit _ ≫ t`. Establish `pt_mul (t t') : pt (t * t') = pt t * pt t'` using `MonObj.comp_mul _ _ _`. Establish `pt_one : pt 1 = 1` using `MonObj.comp_one _`. Establish `hτ (t) : g₀ ≫ (transl (t ≫ i)).hom.left = ((pt t ≫ i) * g).left`.

Establish `: g ≫ (transl (t ≫ i)).hom = (pt t ≫ i) * g` using `by show g ≫ ((toUnit G ≫ t ≫ i) * 𝟙 G) = _`. Rewrite using `[MonObj.comp_mul, Category.comp_id, ← Category.assoc, comp_toUnit, ← Category.assoc]`. Conclude with `congrArg CommaMorphism.left this`. Use `choose σ hσ' using fun t : 𝟙_ (Over (Sp k)) ⟶ splitTorus (Sp k) X => hσ ((Over.forget _).mapIso (transl (t ≫ i)))`. Use `replace hσ' (t) : spMap (σ t) ≫ g₀ = ((pt t ≫ i) * g).left := (hσ' t).trans (hτ t)`.

Establish `hσs (t) : spMap (σ t) ≫ s = s` using `by show spMap (σ t) ≫ g₀ ≫ G.hom = s`. Rewrite using `[← Category.assoc, hσ']`. Conclude with `Over.w _`. Establish `hσpt (t t') : (Over.homMk (spMap (σ t)) (hσs t) : Over.mk s ⟶ Over.mk s) ≫ pt t' = pt t'` using `by show _ ≫ toUnit _ ≫ t' = _`. Rewrite using `[← Category.assoc, comp_toUnit]`.

Establish `hσg (t t') : spMap (σ t) ≫ ((pt t' ≫ i) * g).left = ((pt (t' * t) ≫ i) * g).left`. Establish `h1 : (Over.homMk (spMap (σ t)) (hσs t) : Over.mk s ⟶ Over.mk s) ≫ g = (pt t ≫ i) * g` using `Over.OverMorphism.ext (hσ' t)`. Establish `: (Over.homMk (spMap (σ t)) (hσs t) : Over.mk s ⟶ Over.mk s) ≫ ((pt t' ≫ i) * g) = (pt (t' * t) ≫ i) * g`. Rewrite using `[MonObj.comp_mul, ← Category.assoc, hσpt, h1, pt_mul, MonObj.mul_comp, _root_.mul_assoc]`. Conclude with `congrArg CommaMorphism.left this`.

Establish `hgt (t) (V : G.left.Opens) (hV : (V : Set G.left).Nonempty) : ⊤ ≤ ((pt t ≫ i) * g).left ⁻¹ᵁ V`. Rewrite using `[← hτ]`. Take `⟨x, hx⟩` from `hV`. Take `⟨y, rfl⟩` from `((Over.forget _).mapIso (transl (t ≫ i))).hom.surjective x`. Conclude with `hg ((transl (t ≫ i)).hom.left ⁻¹ᵁ V) ⟨y, hx⟩`.

Establish `hone : ((pt 1 ≫ i) * g).left = g₀`. Rewrite using `[pt_one, MonObj.one_comp, _root_.one_mul]`. Both sides reduce to the same expression. Take `⟨S, p, q, hp, hrel⟩` from `exists_rel i g U f (pt_one ▸ hgt 1 U hU)`. Take `⟨χ₀, p', q', hp', hφ, hw⟩` from `GlobalTheory.T.exists_weighted_relation_of_minimal_support F _ X (fun t χ => chr (pt t) χ) σ (fun t => ev (R := F) ((pt t ≫ i) * g).left U (hgt t U hU) f) S p q (fun t t' χ => by rw [pt_mul, chr_mul]) (fun χ => by rw [pt_one, chr_one]) (fun t t' χ => by rw [← chr_comp (σ t) (hσs …`.

Set `ε` to `S.equivFin.symm`. Establish `hε (r : X → F) : ∑ j, r (ε j) = ∑ χ ∈ S, r χ`. Rewrite using `[← Finset.sum_coe_sort S r]`. Conclude with `Equiv.sum_comp ε fun x : S => r x`. Take `⟨U', hU', u, hle, hu⟩` from `hsec U hU (Option (Fin S.card ⊕ Fin S.card)) (fun o => o.elim (∑ χ ∈ S, p' χ) (Sum.elim (fun j => q' (ε j)) fun j => p' (ε j)))`.

Establish `hwt (v : Γ(G.left, U')) (χ : X) (r : F) (hv : ev g₀ U' (hg U' hU') v = r) (hr : ∀ t, σ t r * chr (pt t) χ₀ = chr (pt t) χ * r) : Wt i U' v (χ - χ₀)`. Use `GlobalTheory.T.splitTorusWeight_test_genericPoint_rationalPoints k G hs X i F s g hg U' v _ fun t h₁ h₂ => ?_` and prove the remaining obligations. Establish `h3 : ev (R` using `F) ((pt t ≫ i) * g).left U' h₁ v = σ t r := (ev_congr (hσ' t).symm U' h₁ (hσ' t ▸ h₁) v).trans ((ev_spMap (σ t) g₀ U' (hg U' hU') _ v).trans (congrArg (σ t) hv))`. Establish `h4 : chr (pt t) χ₀ * chr (pt t) (-χ₀) = 1` using `by rw [← chr_add, add_neg_cancel, chr_zero]`. Use `h3.trans (Eq.trans ?_ (congrArg (chr (pt t) (χ - χ₀) * ·) hv.symm))` and prove the remaining obligations.

Rewrite using `[sub_eq_add_neg, chr_add]`. Take the linear combination `chr (pt t) (-χ₀) * hr t - σ t r * h4`. Establish `hun (o) : u o = 0 ∨ IsUnit (u o)`. Use `(eq_or_ne _ 0).imp (fun h => hinj U' hU' ?_) (hu o).2` and prove the remaining obligations. Rewrite using `[(hu o).1, h, map_zero]`.

Establish `hb : ev g₀ U' (hg U' hU') (∑ j, u (some (Sum.inr j))) = ∑ χ ∈ S, p' χ`. Rewrite using `[map_sum, ← hε]`. Conclude with `Finset.sum_congr rfl fun j _ => (hu _).1`. Use `⟨U', hle, S.card, fun j => u (some (Sum.inl j)), fun j => u (some (Sum.inr j)), fun j => ε j - χ₀, hU', fun j => ⟨hwt _ _ _ (hu _).1 fun t => (hw t _ (ε j).2).2, hwt _ _ _ (hu _).1 fun t => (hw t _ (ε j).2).1, hun _, hun _⟩, ?_, hinj U' hU' ?_⟩` and prove the remaining obligations. Rewrite using `[hinj U' hU' (hb.trans (hu none).1.symm)]`.

Conclude with `(hu none).2 hp'`. Rewrite using `[map_mul, hb, ev_res g₀ hle _ (hg U hU), ← ev_congr hone U (hgt 1 U hU), hφ, map_sum, ← hε]`. Conclude with `Finset.sum_congr rfl fun j _ => (hu (some (Sum.inl j))).1.symm`.
-/
theorem exists_ratio_of_weight_sums : ∀ (k : Type) [Field k] [IsAlgClosed k] (G : Over (Sp k)) [GrpObj G], SmConn G → ∀ (X : Type) [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] (i : splitTorus (Sp k) X ⟶ G), IsMonHom i → ∀ (U : G.left.Opens) (f : Γ(G.left, U)), (U : Set G.left).Nonempty → ∃ (U' : G.left.Opens) (h : U' ≤ U) (n : ℕ) (a b : Fin n → Γ(G.left, U')) (χ : Fin n → X), (U' : Set G.left).Nonempty ∧ (∀ j, Wt i U' (a j) (χ j) ∧ Wt i U' (b j) (χ j) ∧ (a j = 0 ∨ IsUnit (a j)) ∧ (b j = 0 ∨ IsUnit (b j))) ∧ IsUnit (∑ j, b j) ∧ (G.left.presheaf.map (homOfLE h).op).hom f * ∑ j, b j = ∑ j, a j := by
  intro k _ _ G _ hG X _ _ _ i hi U f hU
  obtain ⟨hc, hs, -, -, hgc⟩ := hG
  have : IsIntegral G.left := isIntegral_of_smooth_of_geometricallyConnected G.hom
  obtain ⟨F, _, g₀, hg, hinj, hσ, hsec⟩ := GlobalTheory.T.exists_generic_functionField_point G.left
  let s : Sp F ⟶ Sp k := g₀ ≫ G.hom
  let g : Over.mk s ⟶ G := Over.homMk g₀ rfl
  let pt (t : 𝟙_ (Over (Sp k)) ⟶ splitTorus (Sp k) X) : Over.mk s ⟶ splitTorus (Sp k) X := toUnit _ ≫ t
  have pt_mul (t t') : pt (t * t') = pt t * pt t' := MonObj.comp_mul _ _ _
  have pt_one : pt 1 = 1 := MonObj.comp_one _
  have hτ (t) : g₀ ≫ (transl (t ≫ i)).hom.left = ((pt t ≫ i) * g).left := by
    have : g ≫ (transl (t ≫ i)).hom = (pt t ≫ i) * g := by
      show g ≫ ((toUnit G ≫ t ≫ i) * 𝟙 G) = _
      rw [MonObj.comp_mul, Category.comp_id, ← Category.assoc, comp_toUnit, ← Category.assoc]
    exact congrArg CommaMorphism.left this
  choose σ hσ' using fun t : 𝟙_ (Over (Sp k)) ⟶ splitTorus (Sp k) X =>
    hσ ((Over.forget _).mapIso (transl (t ≫ i)))
  replace hσ' (t) : spMap (σ t) ≫ g₀ = ((pt t ≫ i) * g).left := (hσ' t).trans (hτ t)
  have hσs (t) : spMap (σ t) ≫ s = s := by
    show spMap (σ t) ≫ g₀ ≫ G.hom = s
    rw [← Category.assoc, hσ']
    exact Over.w _
  have hσpt (t t') : (Over.homMk (spMap (σ t)) (hσs t) : Over.mk s ⟶ Over.mk s) ≫ pt t' = pt t' := by
    show _ ≫ toUnit _ ≫ t' = _
    rw [← Category.assoc, comp_toUnit]
  have hσg (t t') : spMap (σ t) ≫ ((pt t' ≫ i) * g).left = ((pt (t' * t) ≫ i) * g).left := by
    have h1 : (Over.homMk (spMap (σ t)) (hσs t) : Over.mk s ⟶ Over.mk s) ≫ g = (pt t ≫ i) * g :=
      Over.OverMorphism.ext (hσ' t)
    have : (Over.homMk (spMap (σ t)) (hσs t) : Over.mk s ⟶ Over.mk s) ≫ ((pt t' ≫ i) * g) =
        (pt (t' * t) ≫ i) * g := by
      rw [MonObj.comp_mul, ← Category.assoc, hσpt, h1, pt_mul, MonObj.mul_comp, _root_.mul_assoc]
    exact congrArg CommaMorphism.left this
  have hgt (t) (V : G.left.Opens) (hV : (V : Set G.left).Nonempty) : ⊤ ≤ ((pt t ≫ i) * g).left ⁻¹ᵁ V := by
    rw [← hτ]
    obtain ⟨x, hx⟩ := hV
    obtain ⟨y, rfl⟩ := ((Over.forget _).mapIso (transl (t ≫ i))).hom.surjective x
    exact hg ((transl (t ≫ i)).hom.left ⁻¹ᵁ V) ⟨y, hx⟩
  have hone : ((pt 1 ≫ i) * g).left = g₀ := by
    rw [pt_one, MonObj.one_comp, _root_.one_mul]; rfl
  obtain ⟨S, p, q, hp, hrel⟩ := exists_rel i g U f (pt_one ▸ hgt 1 U hU)
  obtain ⟨χ₀, p', q', hp', hφ, hw⟩ := GlobalTheory.T.exists_weighted_relation_of_minimal_support F _ X (fun t χ => chr (pt t) χ) σ
    (fun t => ev (R := F) ((pt t ≫ i) * g).left U (hgt t U hU) f) S p q
    (fun t t' χ => by rw [pt_mul, chr_mul]) (fun χ => by rw [pt_one, chr_one])
    (fun t t' χ => by rw [← chr_comp (σ t) (hσs t), hσpt])
    (fun t t' => (ev_spMap (σ t) _ U _ (hσg t t' ▸ hgt (t' * t) U hU) f).symm.trans
      (ev_congr (hσg t t') U _ _ f))
    (fun t => hrel (pt t) _) hp
  let ε := S.equivFin.symm
  have hε (r : X → F) : ∑ j, r (ε j) = ∑ χ ∈ S, r χ := by
    rw [← Finset.sum_coe_sort S r]
    exact Equiv.sum_comp ε fun x : S => r x
  obtain ⟨U', hU', u, hle, hu⟩ := hsec U hU (Option (Fin S.card ⊕ Fin S.card))
    (fun o => o.elim (∑ χ ∈ S, p' χ) (Sum.elim (fun j => q' (ε j)) fun j => p' (ε j)))
  have hwt (v : Γ(G.left, U')) (χ : X) (r : F) (hv : ev g₀ U' (hg U' hU') v = r)
      (hr : ∀ t, σ t r * chr (pt t) χ₀ = chr (pt t) χ * r) : Wt i U' v (χ - χ₀) := by
    refine GlobalTheory.T.splitTorusWeight_test_genericPoint_rationalPoints k G hs X i F s g hg U' v _ fun t h₁ h₂ => ?_
    have h3 : ev (R := F) ((pt t ≫ i) * g).left U' h₁ v = σ t r :=
      (ev_congr (hσ' t).symm U' h₁ (hσ' t ▸ h₁) v).trans
        ((ev_spMap (σ t) g₀ U' (hg U' hU') _ v).trans (congrArg (σ t) hv))
    have h4 : chr (pt t) χ₀ * chr (pt t) (-χ₀) = 1 := by rw [← chr_add, add_neg_cancel, chr_zero]
    refine h3.trans (Eq.trans ?_ (congrArg (chr (pt t) (χ - χ₀) * ·) hv.symm))
    rw [sub_eq_add_neg, chr_add]
    linear_combination chr (pt t) (-χ₀) * hr t - σ t r * h4
  have hun (o) : u o = 0 ∨ IsUnit (u o) := by
    refine (eq_or_ne _ 0).imp (fun h => hinj U' hU' ?_) (hu o).2
    rw [(hu o).1, h, map_zero]
  have hb : ev g₀ U' (hg U' hU') (∑ j, u (some (Sum.inr j))) = ∑ χ ∈ S, p' χ := by
    rw [map_sum, ← hε]
    exact Finset.sum_congr rfl fun j _ => (hu _).1
  refine ⟨U', hle, S.card, fun j => u (some (Sum.inl j)), fun j => u (some (Sum.inr j)), fun j => ε j - χ₀, hU',
    fun j => ⟨hwt _ _ _ (hu _).1 fun t => (hw t _ (ε j).2).2, hwt _ _ _ (hu _).1 fun t => (hw t _ (ε j).2).1,
      hun _, hun _⟩, ?_, hinj U' hU' ?_⟩
  · rw [hinj U' hU' (hb.trans (hu none).1.symm)]
    exact (hu none).2 hp'
  · rw [map_mul, hb, ev_res g₀ hle _ (hg U hU), ← ev_congr hone U (hgt 1 U hU), hφ, map_sum, ← hε]
    exact Finset.sum_congr rfl fun j _ => (hu (some (Sum.inl j))).1.symm

end GlobalTheory.SS.WtRat
end

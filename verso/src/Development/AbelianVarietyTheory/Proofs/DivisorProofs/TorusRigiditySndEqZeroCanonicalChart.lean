import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HasRigidCoords
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CanonicalFamilyPeriodsInCoordinatesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsRigidOfBase
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAbelianSchemeOfGrpPullbackStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianPartIdentificationsAgreeConstantTangentStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FromBaseIdentityAlongMorphismStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsConstantUnitPulledBackBundleAutomorphismStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart GlobalTheory.UCanon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.TorRigid

open GlobalTheory.RigChart GlobalTheory.ToricData

/- English proof (translation)
Apply `Additive.ofMul.injective` to reduce the goal to its premises. Simplify using `only [ofMul_mul, ofMul_inv]`. Normalize the expressions using the abelian group laws.
-/
theorem commGroup_fourfold_cancellation {G : Type*} [CommGroup G] (a1 a2 a3 a4 b1 b2 b3 b4 U V : G) :
    a1 * a2⁻¹ * a3⁻¹ * a4 * V = ((b1⁻¹ * (U * a1)) * (b2⁻¹ * (U * a2))⁻¹ * (b3⁻¹ * (U * a3))⁻¹ * (b4⁻¹ * (U * a4))) *
      (b1 * b2⁻¹ * b3⁻¹ * b4 * V) := by
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv]
  abel

/- English proof (translation)
Introduce `R _ _ Q τ₀ W₀ _ ιb hFB k _ ρ hρ B' iG π₁ π₂ w c' hA y z zz J hJ`. Take `⟨h₁, h₂, h₃, h₄, h₅⟩` from `hA`. Take `⟨B₀, iB₀, M₀, c₀, τ₁, β, wF, hB₀, hM₀, hβ, hwF, hc₀, hτ₁, hpt⟩` from `GlobalTheory.T.fromBase_identity_along_morphism Q τ₀ ιb hFB`. Establish `hπ : π₁ ≫ β = π₂ ≫ β` using `GlobalTheory.T.abelianPart_identifications_agree_constant_tangent Q ιb B₀ β hβ k ρ hρ B' π₁ π₂ h₁ h₂ h₃`. Establish `hB'ab : IsAbelianScheme B'` using `GlobalTheory.T.isAbelianScheme_of_grpPullback' π₁ h₁ Q.P.isAb`.

Take `⟨u, hu⟩` from `GlobalTheory.T.exists_constant_unit_pulledBack_bundle_automorphism (DualNumber k) B' hB'ab Q.P.L M₀ β wF π₁ π₂ w Q.P.isLB hM₀ hwF h₄ hπ`. Take `⟨J₀, hJ₀⟩` from `GlobalTheory.UU.exists_good_pt hM₀ zz`. Establish `e1` using `hpt _ (spMap ρ) y z zz J J₀ hJ hJ₀`. Establish `e2` using `hpt _ (spMap (GlobalTheory.RigChart.constHom ρ)) y z zz J J₀ hJ hJ₀`. Establish `hιb : spMap ρ ≫ spMap ιb = spMap (GlobalTheory.RigChart.constHom ρ) ≫ spMap ιb`.

Establish `h' : (GlobalTheory.RigChart.constHom ρ).comp ιb = GlobalTheory.RigChart.constHom (ρ.comp ιb)`. Conclude with `RingHom.ext fun x => rfl`. Express the relevant statement in the definitionally equal form `Spec.map _ ≫ Spec.map _ = Spec.map _ ≫ Spec.map _`. Rewrite using `[← Spec.map_comp, ← Spec.map_comp]`. Use `congr 1`.

Rewrite using `[← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp]`. Conclude with `congrArg CommRingCat.ofHom (hρ.trans h'.symm)`. Rewrite `e1` using `[hιb]`. Establish `q1 : ∀ x, spMap ρ ≫ cpt Q x = c' x ≫ π₁` using `fun x => ((h₅ x).2.1).symm`. Establish `q2 : ∀ x, spMap (GlobalTheory.RigChart.constHom ρ) ≫ cpt Q x = c' x ≫ π₂` using `fun x => ((h₅ x).2.2).symm`.

Establish `q1' : ∀ x, spMap ρ ≫ cpt Q x ≫ β = c' x ≫ π₁ ≫ β` using `fun x => by`. Rewrite using `[← Category.assoc, q1, Category.assoc]`. Establish `q2' : ∀ x, spMap (GlobalTheory.RigChart.constHom ρ) ≫ cpt Q x ≫ β = c' x ≫ π₂ ≫ β` using `fun x => by`. Rewrite using `[← Category.assoc, q2, Category.assoc]`. Rewrite `e1` using `[q1', q1', q1', q1', q1, q1, q1, q1]`.

Rewrite `e2` using `[q2', q2', q2', q2', q2, q2, q2, q2]`. Establish `hW : ∀ x, gm (c' x) zz _ (w.s (fun _ => J (c' x ≫ π₂), fun _ => J (c' x ≫ π₁))) = (gm (c' x ≫ π₂) zz _ (wF.s (fun _ => J₀ (c' x ≫ π₂ ≫ β), J (c' x ≫ π₂))))⁻¹ * (gm (𝟙 _) zz ⊤ (unitOn u) * gm (c' x ≫ π₁) zz _ (wF.s (fun _ => J₀ (c' x ≫ π₁ ≫ β), J (c' x ≫ π₁))))` using `fun x => eq_inv_mul_of_mul_eq (hu (c' x) (h₅ x).1 zz J J₀ hJ hJ₀)`. Unfold `GlobalTheory.TautRigid.lamC`. Rewrite using `[e1, e2, hW, hW, hW, hW]`. Conclude with `commGroup_fourfold_cancellation _ _ _ _ _ _ _ _ _ _`.
-/
theorem val_const_of_fromBase : ∀ {R : Type} [CommRing R] [IsDomain R] (Q : DegPre R) (τ₀ : Gens Q) {W₀ : Type} [CommRing W₀] (ιb : W₀ →+* R), FromBase Q τ₀ ιb → ∀ (k : Type) [Field k] (ρ : R →+* DualNumber k), ρ.comp ιb = GlobalTheory.RigChart.constHom (ρ.comp ιb) → ∀ (B' : Over (Sp (DualNumber k))) (_ : GrpObj B') (π₁ π₂ : B'.left ⟶ Q.P.A.left) (w : LB.Iso (Q.P.L.pull π₁) (Q.P.L.pull π₂)) (c' : Q.X → (Sp (DualNumber k) ⟶ B'.left)), GlobalTheory.TautRigid.AbConst Q ρ B' π₁ π₂ w c' → ∀ (y z : Q.X) (zz : Sp (DualNumber k)) (J : (Sp (DualNumber k) ⟶ Q.P.A.left) → Q.P.L.ι), Good Q.P.L zz J → val (τ₀ y z) (spMap ρ) zz J = GlobalTheory.TautRigid.lamC Q w c' y z zz J * val (τ₀ y z) (spMap (GlobalTheory.RigChart.constHom ρ)) zz J := by
  intro R _ _ Q τ₀ W₀ _ ιb hFB k _ ρ hρ B' iG π₁ π₂ w c' hA y z zz J hJ
  obtain ⟨h₁, h₂, h₃, h₄, h₅⟩ := hA
  obtain ⟨B₀, iB₀, M₀, c₀, τ₁, β, wF, hB₀, hM₀, hβ, hwF, hc₀, hτ₁, hpt⟩ := GlobalTheory.T.fromBase_identity_along_morphism Q τ₀ ιb hFB
  have hπ : π₁ ≫ β = π₂ ≫ β := GlobalTheory.T.abelianPart_identifications_agree_constant_tangent Q ιb B₀ β hβ k ρ hρ B' π₁ π₂ h₁ h₂ h₃
  have hB'ab : IsAbelianScheme B' := GlobalTheory.T.isAbelianScheme_of_grpPullback' π₁ h₁ Q.P.isAb
  obtain ⟨u, hu⟩ := GlobalTheory.T.exists_constant_unit_pulledBack_bundle_automorphism (DualNumber k) B' hB'ab Q.P.L M₀ β wF π₁ π₂ w Q.P.isLB hM₀ hwF h₄ hπ
  obtain ⟨J₀, hJ₀⟩ := GlobalTheory.UU.exists_good_pt hM₀ zz
  have e1 := hpt _ (spMap ρ) y z zz J J₀ hJ hJ₀
  have e2 := hpt _ (spMap (GlobalTheory.RigChart.constHom ρ)) y z zz J J₀ hJ hJ₀
  have hιb : spMap ρ ≫ spMap ιb = spMap (GlobalTheory.RigChart.constHom ρ) ≫ spMap ιb := by
    have h' : (GlobalTheory.RigChart.constHom ρ).comp ιb = GlobalTheory.RigChart.constHom (ρ.comp ιb) := by
      exact RingHom.ext fun x => rfl
    change Spec.map _ ≫ Spec.map _ = Spec.map _ ≫ Spec.map _
    rw [← Spec.map_comp, ← Spec.map_comp]
    congr 1
    rw [← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp]
    exact congrArg CommRingCat.ofHom (hρ.trans h'.symm)
  rw [hιb] at e1
  have q1 : ∀ x, spMap ρ ≫ cpt Q x = c' x ≫ π₁ := fun x => ((h₅ x).2.1).symm
  have q2 : ∀ x, spMap (GlobalTheory.RigChart.constHom ρ) ≫ cpt Q x = c' x ≫ π₂ := fun x => ((h₅ x).2.2).symm
  have q1' : ∀ x, spMap ρ ≫ cpt Q x ≫ β = c' x ≫ π₁ ≫ β := fun x => by
    rw [← Category.assoc, q1, Category.assoc]
  have q2' : ∀ x, spMap (GlobalTheory.RigChart.constHom ρ) ≫ cpt Q x ≫ β = c' x ≫ π₂ ≫ β := fun x => by
    rw [← Category.assoc, q2, Category.assoc]
  rw [q1', q1', q1', q1', q1, q1, q1, q1] at e1
  rw [q2', q2', q2', q2', q2, q2, q2, q2] at e2
  have hW : ∀ x, gm (c' x) zz _ (w.s (fun _ => J (c' x ≫ π₂), fun _ => J (c' x ≫ π₁))) =
      (gm (c' x ≫ π₂) zz _ (wF.s (fun _ => J₀ (c' x ≫ π₂ ≫ β), J (c' x ≫ π₂))))⁻¹ *
        (gm (𝟙 _) zz ⊤ (unitOn u) * gm (c' x ≫ π₁) zz _ (wF.s (fun _ => J₀ (c' x ≫ π₁ ≫ β), J (c' x ≫ π₁)))) :=
    fun x => eq_inv_mul_of_mul_eq (hu (c' x) (h₅ x).1 zz J J₀ hJ hJ₀)
  unfold GlobalTheory.TautRigid.lamC
  rw [e1, e2, hW, hW, hW, hW]
  exact commGroup_fourfold_cancellation _ _ _ _ _ _ _ _ _ _

/- English proof (translation)
Introduce `E _ _ _ H Dw l Xo c φ R _ _ _ hB C Cn k _ ρ a hC hconst j`. Take `⟨ε', τ₀, hε', hFB, hτ⟩` from `GlobalTheory.T.canonicalFamily_periods_in_coordinates Xo c φ R hB C Cn`. Take `⟨B', iG, π₁, π₂, w, c', h₁, h₂, h₃, h₄, h₅, h₆⟩` from `hC`. Establish `hA : GlobalTheory.TautRigid.AbConst C.P.D.toPre ρ B' π₁ π₂ w c'` using `⟨h₁, h₂, h₃, h₄, h₅⟩`. Establish `hB1` using `val_const_of_fromBase C.P.D.toPre τ₀ (Cn.ψ.comp MvPolynomial.C) hFB k ρ hconst B' iG π₁ π₂ w c' hA`.

Use `haveI : CharZero k := by`. Set `f : c.F →+* k` to `(TrivSqZeroExt.fstHom k k k).toRingHom.comp (ρ.comp C.b)`. Conclude with `(f.charZero_iff f.injective).1 inferInstance`. Use `set M : ℕ := l.M' with hMdef`. Establish `hM : 0 < M` using `level_pos l`.

Set `Q` to `C.P.D.toPre`. Set `u : Fin Cn.N → Rˣ` to `fun j => (Cn.tor j).unit`. Establish `hu : ∀ j, (u j : R) = Cn.ψ (MvPolynomial.X (.inr j))` using `fun j => IsUnit.unit_spec _`. Set `δ : Fin C.m → LinearMap.BilinForm ℤ Q.X` to `C.δ`. Set `ε : Fin Cn.N → LinearMap.BilinForm ℤ Q.X` to `fun j => (ε' (.inr j) : LinearMap.BilinForm ℤ Q.X)`.

Establish `hδ : ∀ i, (ε' (.inl i) : LinearMap.BilinForm ℤ Q.X) = C.δ i` using `fun i => by`. Rewrite using `[hε', Cn.cone i]`. Establish `hli : LinearIndependent ℤ (Sum.elim δ ε)`. Establish `h0 : LinearIndependent ℤ (fun κ => (ε' κ : LinearMap.BilinForm ℤ Q.X))` using `ε'.linearIndependent.map' (Submodule.subtype _) (Submodule.ker_subtype _)`. Establish `hEq : Sum.elim δ ε = fun κ => (ε' κ : LinearMap.BilinForm ℤ Q.X)`.

Use function extensionality and compare the values at `κ`. Break down `κ with i | i` into its components or cases. Conclude with `(hδ i).symm`. Both sides reduce to the same expression. Rewrite using `[hEq]`.

Conclude with `h0`. Establish `key : ∀ y z, ∑ j, ((M : ℤ) * ε j y z) • Multiplicative.toAdd (GlobalTheory.TautRigid.dlog k (Units.map ρ.toMonoidHom (u j))) = ∑ i, a i * ((((M : ℤ) • δ i) y z : ℤ) : k)`. Introduce `y z`. Use `set v : Rˣ := ∏ j, u j ^ ((M : ℤ) * ε j y z) with hvdef`. Set `f : Rˣ →* (FractionRing R)ˣ` to `Units.map (algebraMap R (FractionRing R)).toMonoidHom`.

Take `⟨hg, kk, hk, hv⟩` from `hτ y z`. Establish `hU' : GlobalTheory.RigChart.IsUnitTau Q C.s (fun i => (M : ℤ) • C.δ i) y z (GlobalTheory.UU.scaleGen (unitOn v) (τ₀ y z))`. Use `⟨GlobalTheory.UU.scaleGen_isGen _ hg, kk * (f v)⁻¹, ?_, fun zz J hJ => ?_⟩` and prove the remaining obligations. Establish `hfv : ((f v : (FractionRing R)ˣ) : FractionRing R) = ∏ j, algebraMap R (FractionRing R) (u j : R) ^ ((M : ℤ) * ε j y z)`. Simplify using `only [f, v, map_prod, map_zpow, Units.coe_prod, Units.val_zpow_eq_zpow_val, Units.coe_map, MonoidHom.coe_coe, RingHom.toMonoidHom_eq_coe]`.

Establish `hne : ((f v : (FractionRing R)ˣ) : FractionRing R) ≠ 0` using `(f v).ne_zero`. Rewrite using `[Units.val_mul, hk, Units.val_inv_eq_inv_val, Fin.prod_univ_add]`. Simplify using `only [finSumFinEquiv_symm_apply_castAdd, finSumFinEquiv_symm_apply_natAdd, LinearMap.smul_apply, smul_eq_mul, Cn.bd, hδ, ← hu]`. Rewrite using `[← hfv, mul_inv_cancel_right₀ hne]`. Establish `e : gm (toUnit (TK R)).left zz ⊤ (unitOn v) = gm (𝟙 (TK R).left) zz ⊤ (unitOn (f v))`.

Rewrite using `[GlobalTheory.UU.gm_top]`. Conclude with `congrArg _ (pullTop_unitOn (algebraMap R (FractionRing R)) _)`. Rewrite using `[hv zz J hJ, GlobalTheory.UU.val_scaleGen _ _ _ hJ, e, ← _root_.mul_assoc, ← map_mul, ← unitOn_mul, inv_mul_cancel_right]`. Use `set s : k := ∑ i, a i * ((((M : ℤ) • δ i) y z : ℤ) : k) with hs`. Establish `hE : ∀ zz : Sp (DualNumber k), gm (𝟙 _) zz ⊤ (unitOn (Units.map ρ.toMonoidHom v)) = gm (𝟙 _) zz ⊤ (unitOn (GlobalTheory.TautRigid.onePlus s * Units.map (GlobalTheory.RigChart.constHom ρ).toMonoidHom v))`.

Introduce `zz`. Take `⟨J, hJ⟩` from `GlobalTheory.UU.exists_good_pt C.P.D.toPre.P.isLB zz`. Establish `hp` using `h₆ y z _ hU' (GlobalTheory.TautRigid.onePlus s) rfl zz J hJ`. Establish `hb` using `hB1 y z zz J hJ`. Establish `e₁ : gm (spMap ρ) zz ⊤ (unitOn v) = gm (𝟙 _) zz ⊤ (unitOn (Units.map ρ.toMonoidHom v))`.

Rewrite using `[GlobalTheory.UU.gm_top]`. Conclude with `congrArg _ (pullTop_unitOn ρ v)`. Establish `e₂ : gm (spMap (GlobalTheory.RigChart.constHom ρ)) zz ⊤ (unitOn v) = gm (𝟙 _) zz ⊤ (unitOn (Units.map (GlobalTheory.RigChart.constHom ρ).toMonoidHom v))`. Rewrite using `[GlobalTheory.UU.gm_top]`. Conclude with `congrArg _ (pullTop_unitOn (GlobalTheory.RigChart.constHom ρ) v)`.

Rewrite `hp` using `[GlobalTheory.UU.val_scaleGen _ _ _ hJ, GlobalTheory.UU.val_scaleGen _ _ _ hJ, e₁, e₂, hb]`. Express the relevant statement in the definitionally equal form `_ = GlobalTheory.TautRigid.lamC Q w c' y z zz J * _ * _ at hp`. Rewrite using `[unitOn_mul, map_mul]`. Conclude with `mul_right_cancel (hp.trans ((congrArg (· * _) (_root_.mul_comm _ _)).trans (mul_mul_mul_comm _ _ _ _)))`. Establish `hv2` using `unitOn_inj.1 (unit_ext fun x _ => hE x)`.

Establish `h3` using `congrArg (fun x => Multiplicative.toAdd (GlobalTheory.TautRigid.dlog k x)) hv2`. Rewrite `h3` using `[map_mul, toAdd_mul, GlobalTheory.TautRigid.dlog_onePlus]`. Establish `hc0 : Multiplicative.toAdd (GlobalTheory.TautRigid.dlog k (Units.map (GlobalTheory.RigChart.constHom ρ).toMonoidHom v)) = 0`. Establish `hs0 : ∀ r : R, (GlobalTheory.RigChart.constHom ρ r).snd = 0` using `fun r => by`. Simplify using `only [GlobalTheory.RigChart.constHom, RingHom.comp_apply]`.

Rewrite using `[TrivSqZeroExt.algebraMap_eq_inl, TrivSqZeroExt.snd_inl]`. Rewrite using `[GlobalTheory.TautRigid.dlog_apply, Units.coe_map]`. Use `erw [hs0, zero_div]`. Rewrite `h3` using `[hc0, add_zero]`. Rewrite using `[← h3, hvdef, map_prod, map_prod, toAdd_prod]`.

Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Rewrite using `[map_zpow, map_zpow, toAdd_zpow]`. Use `set L : Fin Cn.N → k := fun j => Multiplicative.toAdd (GlobalTheory.TautRigid.dlog k (Units.map ρ.toMonoidHom (u j))) with hL`. Set `F : Fin C.m ⊕ Fin Cn.N → Q.X × Q.X → ℤ` to `fun κ p => Sum.elim δ ε κ p.1 p.2`. Establish `hF : LinearIndependent ℤ F`.

Set `e : LinearMap.BilinForm ℤ Q.X →ₗ[ℤ] (Q.X × Q.X → ℤ)` to `{ toFun := fun β p => β p.1 p.2 map_add' := fun β β' => by funext p; rfl map_smul' := fun n β => by funext p; rfl }`. Establish `he : LinearMap.ker e = ⊥` using `LinearMap.ker_eq_bot.mpr fun β β' h => LinearMap.ext fun y => LinearMap.ext fun z => congrFun h (y, z)`. Establish `hEq : F = e ∘ Sum.elim δ ε`. Use function extensionality and compare the values at `κ p`. Apply the tactic sequence `rcases κ with i | j <;> rfl`.

Rewrite using `[hEq]`. Conclude with `hli.map' e he`. Establish `hz` using `GlobalTheory.PolFan.eq_zero_of_linearIndependent_int hF k (Sum.elim (fun i => a i * (M : k)) (fun j => -(L j * (M : k)))) fun p => by`. Rewrite using `[Fintype.sum_sum_type]`. Establish `hk` using `key p.1 p.2`.

Simplify using `only [zsmul_eq_mul, Int.cast_mul, Int.cast_natCast, LinearMap.smul_apply, smul_eq_mul] at hk`. Simplify using `only [Sum.elim_inl, Sum.elim_inr, F]`. Establish `e1 : ∑ i, a i * (M : k) * ((δ i p.1 p.2 : ℤ) : k) = ∑ i, a i * ((M : k) * ((δ i p.1 p.2 : ℤ) : k))` using `Finset.sum_congr rfl fun i _ => by ring`. Establish `e2 : ∑ j, -(L j * (M : k)) * ((ε j p.1 p.2 : ℤ) : k) = -∑ j, (M : k) * ((ε j p.1 p.2 : ℤ) : k) * L j`. Rewrite using `[← Finset.sum_neg_distrib]`.

Conclude with `Finset.sum_congr rfl fun j _ => by ring`. Rewrite using `[e1, e2, ← hk]`. Expand and normalize the polynomial expressions, which then agree. Establish `h1` using `congrFun hz (Sum.inr j)`. Simplify using `only [Sum.elim_inr, Pi.zero_apply, neg_eq_zero, mul_eq_zero, Nat.cast_eq_zero] at h1`.

Establish `hLj : Multiplicative.toAdd (GlobalTheory.TautRigid.dlog k (Units.map ρ.toMonoidHom (u j))) = 0` using `h1.resolve_right hM.ne'`. Rewrite `hLj` using `[GlobalTheory.TautRigid.dlog_apply, Units.coe_map]`. Use `(div_eq_zero_iff.1 hLj).resolve_right (by` as an intermediate fact. Use `GlobalTheory.TautRigid.fst_ne_zero (Units.map ρ.toMonoidHom (u j))` as an intermediate fact. Rewrite using `[Units.coe_map] at this)` and apply the resulting hypothesis.

Rewrite using `[← hu]`. Conclude with `this`.
-/
theorem snd_eq_zero_of_isConstAlong : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Geo.Tor.Level H} (Xo : Moduli Dw l) (c : Coeff l) (φ : InvFun (𝓞 E)), ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], GlobalTheory.Mum.Base R → ∀ (C : MonoFam Xo c φ R) (Cn : Canon C), ∀ (k : Type) [Field k] (ρ : R →+* DualNumber k) (a : Fin C.m → k), GlobalTheory.RigChart.IsConstAlong C.P.D.toPre C.s (fun i => (l.M' : ℤ) • C.δ i) ρ a → ρ.comp (Cn.ψ.comp MvPolynomial.C) = GlobalTheory.RigChart.constHom (ρ.comp (Cn.ψ.comp MvPolynomial.C)) → ∀ j, (ρ (Cn.ψ (MvPolynomial.X (.inr j)))).snd = 0 := by
  classical
  intro E _ _ _ H Dw l Xo c φ R _ _ _ hB C Cn k _ ρ a hC hconst j
  obtain ⟨ε', τ₀, hε', hFB, hτ⟩ := GlobalTheory.T.canonicalFamily_periods_in_coordinates Xo c φ R hB C Cn
  obtain ⟨B', iG, π₁, π₂, w, c', h₁, h₂, h₃, h₄, h₅, h₆⟩ := hC
  have hA : GlobalTheory.TautRigid.AbConst C.P.D.toPre ρ B' π₁ π₂ w c' := ⟨h₁, h₂, h₃, h₄, h₅⟩
  have hB1 := val_const_of_fromBase C.P.D.toPre τ₀ (Cn.ψ.comp MvPolynomial.C) hFB k ρ hconst B' iG π₁ π₂ w c' hA
  haveI : CharZero k := by
    let f : c.F →+* k := (TrivSqZeroExt.fstHom k k k).toRingHom.comp (ρ.comp C.b)
    exact (f.charZero_iff f.injective).1 inferInstance
  set M : ℕ := l.M' with hMdef
  have hM : 0 < M := level_pos l
  let Q := C.P.D.toPre
  let u : Fin Cn.N → Rˣ := fun j => (Cn.tor j).unit
  have hu : ∀ j, (u j : R) = Cn.ψ (MvPolynomial.X (.inr j)) := fun j => IsUnit.unit_spec _
  let δ : Fin C.m → LinearMap.BilinForm ℤ Q.X := C.δ
  let ε : Fin Cn.N → LinearMap.BilinForm ℤ Q.X := fun j => (ε' (.inr j) : LinearMap.BilinForm ℤ Q.X)
  have hδ : ∀ i, (ε' (.inl i) : LinearMap.BilinForm ℤ Q.X) = C.δ i := fun i => by
    rw [hε', Cn.cone i]
  have hli : LinearIndependent ℤ (Sum.elim δ ε) := by
    have h0 : LinearIndependent ℤ (fun κ => (ε' κ : LinearMap.BilinForm ℤ Q.X)) :=
      ε'.linearIndependent.map' (Submodule.subtype _) (Submodule.ker_subtype _)
    have hEq : Sum.elim δ ε = fun κ => (ε' κ : LinearMap.BilinForm ℤ Q.X) := by
      funext κ; rcases κ with i | i
      · exact (hδ i).symm
      · rfl
    rw [hEq]; exact h0
  have key : ∀ y z, ∑ j, ((M : ℤ) * ε j y z) • Multiplicative.toAdd (GlobalTheory.TautRigid.dlog k (Units.map ρ.toMonoidHom (u j))) =
      ∑ i, a i * ((((M : ℤ) • δ i) y z : ℤ) : k) := by
    intro y z
    set v : Rˣ := ∏ j, u j ^ ((M : ℤ) * ε j y z) with hvdef
    let f : Rˣ →* (FractionRing R)ˣ := Units.map (algebraMap R (FractionRing R)).toMonoidHom
    obtain ⟨hg, kk, hk, hv⟩ := hτ y z
    have hU' : GlobalTheory.RigChart.IsUnitTau Q C.s (fun i => (M : ℤ) • C.δ i) y z (GlobalTheory.UU.scaleGen (unitOn v) (τ₀ y z)) := by
      refine ⟨GlobalTheory.UU.scaleGen_isGen _ hg, kk * (f v)⁻¹, ?_, fun zz J hJ => ?_⟩
      · have hfv : ((f v : (FractionRing R)ˣ) : FractionRing R) =
            ∏ j, algebraMap R (FractionRing R) (u j : R) ^ ((M : ℤ) * ε j y z) := by
          simp only [f, v, map_prod, map_zpow, Units.coe_prod, Units.val_zpow_eq_zpow_val, Units.coe_map,
            MonoidHom.coe_coe, RingHom.toMonoidHom_eq_coe]
        have hne : ((f v : (FractionRing R)ˣ) : FractionRing R) ≠ 0 := (f v).ne_zero
        rw [Units.val_mul, hk, Units.val_inv_eq_inv_val, Fin.prod_univ_add]
        simp only [finSumFinEquiv_symm_apply_castAdd, finSumFinEquiv_symm_apply_natAdd, LinearMap.smul_apply, smul_eq_mul,
          Cn.bd, hδ, ← hu]
        rw [← hfv, mul_inv_cancel_right₀ hne]
      · have e : gm (toUnit (TK R)).left zz ⊤ (unitOn v) = gm (𝟙 (TK R).left) zz ⊤ (unitOn (f v)) := by
          rw [GlobalTheory.UU.gm_top]
          exact congrArg _ (pullTop_unitOn (algebraMap R (FractionRing R)) _)
        rw [hv zz J hJ, GlobalTheory.UU.val_scaleGen _ _ _ hJ, e, ← _root_.mul_assoc, ← map_mul, ← unitOn_mul,
          inv_mul_cancel_right]
    set s : k := ∑ i, a i * ((((M : ℤ) • δ i) y z : ℤ) : k) with hs
    have hE : ∀ zz : Sp (DualNumber k), gm (𝟙 _) zz ⊤ (unitOn (Units.map ρ.toMonoidHom v)) =
        gm (𝟙 _) zz ⊤ (unitOn (GlobalTheory.TautRigid.onePlus s * Units.map (GlobalTheory.RigChart.constHom ρ).toMonoidHom v)) := by
      intro zz
      obtain ⟨J, hJ⟩ := GlobalTheory.UU.exists_good_pt C.P.D.toPre.P.isLB zz
      have hp := h₆ y z _ hU' (GlobalTheory.TautRigid.onePlus s) rfl zz J hJ
      have hb := hB1 y z zz J hJ
      have e₁ : gm (spMap ρ) zz ⊤ (unitOn v) = gm (𝟙 _) zz ⊤ (unitOn (Units.map ρ.toMonoidHom v)) := by
        rw [GlobalTheory.UU.gm_top]; exact congrArg _ (pullTop_unitOn ρ v)
      have e₂ : gm (spMap (GlobalTheory.RigChart.constHom ρ)) zz ⊤ (unitOn v) =
          gm (𝟙 _) zz ⊤ (unitOn (Units.map (GlobalTheory.RigChart.constHom ρ).toMonoidHom v)) := by
        rw [GlobalTheory.UU.gm_top]; exact congrArg _ (pullTop_unitOn (GlobalTheory.RigChart.constHom ρ) v)
      rw [GlobalTheory.UU.val_scaleGen _ _ _ hJ, GlobalTheory.UU.val_scaleGen _ _ _ hJ, e₁, e₂, hb] at hp
      change _ = GlobalTheory.TautRigid.lamC Q w c' y z zz J * _ * _ at hp
      rw [unitOn_mul, map_mul]
      exact mul_right_cancel (hp.trans ((congrArg (· * _) (_root_.mul_comm _ _)).trans (mul_mul_mul_comm _ _ _ _)))
    have hv2 := unitOn_inj.1 (unit_ext fun x _ => hE x)
    have h3 := congrArg (fun x => Multiplicative.toAdd (GlobalTheory.TautRigid.dlog k x)) hv2
    rw [map_mul, toAdd_mul, GlobalTheory.TautRigid.dlog_onePlus] at h3
    have hc0 : Multiplicative.toAdd (GlobalTheory.TautRigid.dlog k (Units.map (GlobalTheory.RigChart.constHom ρ).toMonoidHom v)) = 0 := by
      have hs0 : ∀ r : R, (GlobalTheory.RigChart.constHom ρ r).snd = 0 := fun r => by
        simp only [GlobalTheory.RigChart.constHom, RingHom.comp_apply]
        rw [TrivSqZeroExt.algebraMap_eq_inl, TrivSqZeroExt.snd_inl]
      rw [GlobalTheory.TautRigid.dlog_apply, Units.coe_map]
      erw [hs0, zero_div]
    rw [hc0, add_zero] at h3
    rw [← h3, hvdef, map_prod, map_prod, toAdd_prod]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_zpow, map_zpow, toAdd_zpow]
  set L : Fin Cn.N → k := fun j => Multiplicative.toAdd (GlobalTheory.TautRigid.dlog k (Units.map ρ.toMonoidHom (u j))) with hL
  let F : Fin C.m ⊕ Fin Cn.N → Q.X × Q.X → ℤ := fun κ p => Sum.elim δ ε κ p.1 p.2
  have hF : LinearIndependent ℤ F := by
    let e : LinearMap.BilinForm ℤ Q.X →ₗ[ℤ] (Q.X × Q.X → ℤ) :=
      { toFun := fun β p => β p.1 p.2
        map_add' := fun β β' => by funext p; rfl
        map_smul' := fun n β => by funext p; rfl }
    have he : LinearMap.ker e = ⊥ := LinearMap.ker_eq_bot.mpr fun β β' h =>
      LinearMap.ext fun y => LinearMap.ext fun z => congrFun h (y, z)
    have hEq : F = e ∘ Sum.elim δ ε := by
      funext κ p
      rcases κ with i | j <;> rfl
    rw [hEq]
    exact hli.map' e he
  have hz := GlobalTheory.PolFan.eq_zero_of_linearIndependent_int hF k
    (Sum.elim (fun i => a i * (M : k)) (fun j => -(L j * (M : k)))) fun p => by
      rw [Fintype.sum_sum_type]
      have hk := key p.1 p.2
      simp only [zsmul_eq_mul, Int.cast_mul, Int.cast_natCast, LinearMap.smul_apply, smul_eq_mul] at hk
      simp only [Sum.elim_inl, Sum.elim_inr, F]
      have e1 : ∑ i, a i * (M : k) * ((δ i p.1 p.2 : ℤ) : k) = ∑ i, a i * ((M : k) * ((δ i p.1 p.2 : ℤ) : k)) :=
        Finset.sum_congr rfl fun i _ => by ring
      have e2 : ∑ j, -(L j * (M : k)) * ((ε j p.1 p.2 : ℤ) : k) =
          -∑ j, (M : k) * ((ε j p.1 p.2 : ℤ) : k) * L j := by
        rw [← Finset.sum_neg_distrib]
        exact Finset.sum_congr rfl fun j _ => by ring
      rw [e1, e2, ← hk]
      ring
  have h1 := congrFun hz (Sum.inr j)
  simp only [Sum.elim_inr, Pi.zero_apply, neg_eq_zero, mul_eq_zero, Nat.cast_eq_zero] at h1
  have hLj : Multiplicative.toAdd (GlobalTheory.TautRigid.dlog k (Units.map ρ.toMonoidHom (u j))) = 0 := h1.resolve_right hM.ne'
  rw [GlobalTheory.TautRigid.dlog_apply, Units.coe_map] at hLj
  have := (div_eq_zero_iff.1 hLj).resolve_right (by
    have := GlobalTheory.TautRigid.fst_ne_zero (Units.map ρ.toMonoidHom (u j))
    rwa [Units.coe_map] at this)
  rw [← hu]
  exact this

end GlobalTheory.TorRigid

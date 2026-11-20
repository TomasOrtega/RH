import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AffinePairRestrictionInjectiveFirstCohomology
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsAbelianSchemeOfIsGrpPullback
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import Development.WeilBound.CoreStatements.AbelianHeightsDuality.AbelianHodgeDeRham.AbelianDeRhamPage

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TensorProduct Opposite KaehlerDifferential
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR
open scoped CategoryTheory.Obj

attribute [local instance] Over.cartesianMonoidalCategory

namespace FubiniStudyChowHeightFormula₂.Hdr

/- English proof (translation)
Take `⟨⟨⟨h1, h2⟩, h3⟩, h4, h5⟩` from `hF`. Take `⟨σ, hσ⟩` from `Module.projective_lifting_property F.mkQ LinearMap.id F.mkQ_surjective`. Establish `hex : Function.Exact F.subtype F.mkQ` using `LinearMap.exact_subtype_mkQ F`. Set `e : M ≃ₗ[R] F × (M ⧸ F)` to `(hex.splitSurjectiveEquiv F.injective_subtype ⟨σ, hσ⟩).1`. Establish `k` using `hM.2 p`.

Rewrite `k` using `[Module.rankAtStalk_eq_of_equiv e, Module.rankAtStalk_prod, Pi.add_apply, h3]`. Use linear arithmetic over natural numbers and integers.
-/
theorem rank_quot {R M : Type} [CommRing R] [AddCommGroup M] [Module R M] (F : Submodule R M) {m n : ℕ}
    (hM : IsVBRank R M (m + n)) (hF : IsSubbundle F m) (p : PrimeSpectrum R) :
    Module.rankAtStalk (M ⧸ F) p = n := by
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4, h5⟩ := hF
  obtain ⟨σ, hσ⟩ := Module.projective_lifting_property F.mkQ LinearMap.id F.mkQ_surjective
  have hex : Function.Exact F.subtype F.mkQ := LinearMap.exact_subtype_mkQ F
  let e : M ≃ₗ[R] F × (M ⧸ F) := (hex.splitSurjectiveEquiv F.injective_subtype ⟨σ, hσ⟩).1
  have k := hM.2 p
  rw [Module.rankAtStalk_eq_of_equiv e, Module.rankAtStalk_prod, Pi.add_apply, h3] at k
  omega

variable {R R' : Type} [CommRing R] [CommRing R'] {X X' : Scheme.{0}}

/- English proof (translation)
Unfold `IsPull1 at e`. Rewrite `e` using `[pullHyp1_ofForm, pullHyp1_ofForm, ← sub_eq_zero, ← map_sub, ofForm_eq_zero]`. Take `⟨g, hg, hD⟩` from `e`. Take `⟨G, hG, hGp⟩` from `exists_cob_of_pair φ s' 0 (fun p ↦ g (op p)) fun p q hqp ↦ (sub_eq_zero.2 (hg (homOfLE hqp).op)).symm`. Establish `hc : ∀ ⦃T T' : AffOp X'⦄ (a : T ⟶ T'), G T' = mp (OAff s') a (G T)` using `fun T T' a ↦ sub_eq_zero.1 (congrFun (congrFun (congrFun hG T) T') a)`.

Set `η : ClosedForm s'` to `⟨⟨fun T ↦ D R' _ (G T), fun T T' a ↦ by`. Express the relevant statement in the definitionally equal form `D R' _ (G T') = p1 _ a (D R' _ (G T))`. Rewrite using `[p1_D, hc a]⟩, by rw [hcl]; trivial⟩`. Establish `h0 : η = 0` using `hinj ((ofForm_eq_zero.2 ⟨G, hc, fun _ ↦ rfl⟩).trans (map_zero _).symm)`. Establish `h1 : ∀ T, D R' _ (G T) = 0` using `fun T ↦ congrArg (fun z : ClosedForm s' ↦ z.1.1 T) h0`.

Establish `h2 : ∀ p : Pair φ, G (op p.1.1) = g (op p)` using `fun p ↦ (hc (homOfLE (le_refl p.1.1)).op).trans ((hGp p.1.1 p le_rfl).trans (sub_zero _))`. Use `Subtype.ext (funext fun p ↦ sub_eq_zero.1 ?_)` and prove the remaining obligations. Use `(hD p).symm.trans ?_` and prove the remaining obligations. Establish `h3` using `h1 (op p.unop.1.1)`. Rewrite `h3` using `[h2]`.

Conclude with `h3`.
-/
theorem isPullForm_of_isPull1 {s : X ⟶ Sp R} {s' : X' ⟶ Sp R'} {σ : R →+* R'} {φ : X' ⟶ X}
    (h : φ ≫ s = s' ≫ spMap σ) (hcl : ClosedForm s' = ⊤) (hinj : Function.Injective (clForm s'))
    (ω : ClosedForm s) (ω' : ClosedForm s') (e : IsPull1 h (clForm s ω) (clForm s' ω')) :
    IsPullForm h ω.1 ω'.1 := by
  unfold IsPull1 at e
  rw [pullHyp1_ofForm, pullHyp1_ofForm, ← sub_eq_zero, ← map_sub, ofForm_eq_zero] at e
  obtain ⟨g, hg, hD⟩ := e
  obtain ⟨G, hG, hGp⟩ := exists_cob_of_pair φ s' 0 (fun p ↦ g (op p)) fun p q hqp ↦
    (sub_eq_zero.2 (hg (homOfLE hqp).op)).symm
  have hc : ∀ ⦃T T' : AffOp X'⦄ (a : T ⟶ T'), G T' = mp (OAff s') a (G T) := fun T T' a ↦
    sub_eq_zero.1 (congrFun (congrFun (congrFun hG T) T') a)
  let η : ClosedForm s' := ⟨⟨fun T ↦ D R' _ (G T), fun T T' a ↦ by
    change D R' _ (G T') = p1 _ a (D R' _ (G T))
    rw [p1_D, hc a]⟩, by rw [hcl]; trivial⟩
  have h0 : η = 0 := hinj ((ofForm_eq_zero.2 ⟨G, hc, fun _ ↦ rfl⟩).trans (map_zero _).symm)
  have h1 : ∀ T, D R' _ (G T) = 0 := fun T ↦ congrArg (fun z : ClosedForm s' ↦ z.1.1 T) h0
  have h2 : ∀ p : Pair φ, G (op p.1.1) = g (op p) := fun p ↦
    (hc (homOfLE (le_refl p.1.1)).op).trans ((hGp p.1.1 p le_rfl).trans (sub_zero _))
  refine Subtype.ext (funext fun p ↦ sub_eq_zero.1 ?_)
  refine (hD p).symm.trans ?_
  have h3 := h1 (op p.unop.1.1)
  rw [h2] at h3
  exact h3

def formEquiv (s : X ⟶ Sp R) (hcl : ClosedForm s = ⊤) (hinj : Function.Injective (clForm s)) :
    GlobForm s ≃ₗ[R] Hodge1 s :=
  (LinearEquiv.ofTop _ hcl).symm.trans (LinearEquiv.ofInjective (clForm s) hinj)

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem formEquiv_apply (s : X ⟶ Sp R) (hcl : ClosedForm s = ⊤) (hinj : Function.Injective (clForm s))
    (ω : GlobForm s) : (formEquiv s hcl hinj ω).1 = clForm s ⟨ω, hcl ▸ trivial⟩ := rfl

/- English proof (translation)
Set `e : Over.mk s' ≅ (Over.pullback f).obj A` to `Over.isoMk h.isoPullback h.isoPullback_hom_snd`. Set `I : GrpObj (Over.mk s')` to `GrpObj.ofIso e.symm`. Establish `: IsMonHom e.symm.hom` using `CategoryTheory.isMonHom_ofIso e.symm`. Establish `: IsMonHom e.hom` using `inferInstanceAs (IsMonHom e.symm.inv)`. Conclude with `⟨I, GlobalTheory.PolPull.isAbelianScheme_of_isGrpPullback hA ((isGrpPullback_of_iso e).comp (isGrpPullback_pullback A f))⟩`.
-/
theorem exists_abelian {S S' : Scheme.{0}} (A : Over S) [GrpObj A] (hA : IsAbelianScheme A) {s' : X' ⟶ S'}
    {φ : X' ⟶ A.left} {f : S' ⟶ S} (h : IsPullback φ s' A.hom f) :
    ∃ _ : GrpObj (Over.mk s'), IsAbelianScheme (Over.mk s') := by
  let e : Over.mk s' ≅ (Over.pullback f).obj A := Over.isoMk h.isoPullback h.isoPullback_hom_snd
  let I : GrpObj (Over.mk s') := GrpObj.ofIso e.symm
  have : IsMonHom e.symm.hom := CategoryTheory.isMonHom_ofIso e.symm
  have : IsMonHom e.hom := inferInstanceAs (IsMonHom e.symm.inv)
  exact ⟨I, GlobalTheory.PolPull.isAbelianScheme_of_isGrpPullback hA
    ((isGrpPullback_of_iso e).comp (isGrpPullback_pullback A f))⟩

/- English proof (translation)
Introduce `R _ A _ g hA hg`. Take `⟨hw, h1, ⟨hcl, hinj, hF⟩, ⟨hex, hsurj⟩, hbc⟩` from `H R A g hA hg`. Set `i` to `formEquiv A.hom hcl hinj`. Establish `hk : Hodge1 A.hom = LinearMap.ker (toHO1 A.hom)`. Rewrite using `[hex.linearMap_ker_eq, Submodule.range_subtype]`.

Set `q : (HH1 A.hom ⧸ Hodge1 A.hom) ≃ₗ[R] HO1 A.hom` to `(Submodule.quotEquivOfEq _ _ hk).trans ((toHO1 A.hom).quotKerEquivOfSurjective hsurj)`. Establish `hr` using `rank_quot (Hodge1 A.hom) (m := g) (n := g) (two_mul g ▸ h1) hF`. Take `⟨⟨⟨f1, f2⟩, f3⟩, f4, f5⟩` from `hF`. Use `⟨⟨h1.1.1, h1.1.2, h1.2⟩, hw, ⟨Module.Finite.equiv i.symm, Module.Projective.of_equiv i.symm, fun p ↦ by rw [Module.rankAtStalk_eq_of_equiv i, f3]⟩, ⟨Module.Finite.equiv q, Module.Projective.of_equiv q, fun p ↦ by rw [← Module.rankAtStalk_eq_of_equiv q, hr]⟩, ⟨hcl, hinj, hsurj⟩, f …` and prove the remaining obligations. Take `⟨b1, ⟨e, he⟩, b3⟩` from `hbc R' X' s' φ h`.

Use `⟨b1, ?_, b3⟩` and prove the remaining obligations. Take `⟨_, hA'⟩` from `exists_abelian A hA h`. Establish `hg' : SmoothOfRelativeDimension g (Over.mk s').hom` using `(smoothOfRelativeDimension_isStableUnderBaseChange (n := g)).of_isPullback h hg`. Take `⟨-, -, ⟨hcl', hinj', -⟩, -⟩` from `H R' (Over.mk s') g hA' hg'`. Set `i'` to `formEquiv s' hcl' hinj'`.

Use `⟨(LinearEquiv.baseChange R R' _ _ i).trans (e.trans i'.symm), fun c ↦ ?_⟩` and prove the remaining obligations. Use `isPullForm_of_isPull1 h.w hcl' hinj' ⟨c, hcl ▸ trivial⟩ ⟨_, hcl' ▸ trivial⟩ ?_` and prove the remaining obligations. Rewrite using `[← formEquiv_apply s' hcl' hinj', ← formEquiv_apply A.hom hcl hinj]`. Establish `k : formEquiv s' hcl' hinj' (((LinearEquiv.baseChange R R' _ _ i).trans (e.trans i'.symm)) (1 ⊗ₜ c)) = e (1 ⊗ₜ i c)` using `i'.apply_symm_apply _`. Rewrite using `[k]`.

Conclude with `he (i c)`.
-/
theorem abelianHodgeDeRham_of_page (H : AbelianDeRhamPage) : GlobalTheory.Published.AbelianHodgeDeRham := by
  intro R _ A _ g hA hg
  obtain ⟨hw, h1, ⟨hcl, hinj, hF⟩, ⟨hex, hsurj⟩, hbc⟩ := H R A g hA hg
  let i := formEquiv A.hom hcl hinj
  have hk : Hodge1 A.hom = LinearMap.ker (toHO1 A.hom) := by
    rw [hex.linearMap_ker_eq, Submodule.range_subtype]
  let q : (HH1 A.hom ⧸ Hodge1 A.hom) ≃ₗ[R] HO1 A.hom :=
    (Submodule.quotEquivOfEq _ _ hk).trans ((toHO1 A.hom).quotKerEquivOfSurjective hsurj)
  have hr := rank_quot (Hodge1 A.hom) (m := g) (n := g) (two_mul g ▸ h1) hF
  obtain ⟨⟨⟨f1, f2⟩, f3⟩, f4, f5⟩ := hF
  refine ⟨⟨h1.1.1, h1.1.2, h1.2⟩, hw,
    ⟨Module.Finite.equiv i.symm, Module.Projective.of_equiv i.symm,
      fun p ↦ by rw [Module.rankAtStalk_eq_of_equiv i, f3]⟩,
    ⟨Module.Finite.equiv q, Module.Projective.of_equiv q,
      fun p ↦ by rw [← Module.rankAtStalk_eq_of_equiv q, hr]⟩,
    ⟨hcl, hinj, hsurj⟩, fun R' _ _ X' s' φ h ↦ ?_⟩
  obtain ⟨b1, ⟨e, he⟩, b3⟩ := hbc R' X' s' φ h
  refine ⟨b1, ?_, b3⟩
  obtain ⟨_, hA'⟩ := exists_abelian A hA h
  have hg' : SmoothOfRelativeDimension g (Over.mk s').hom :=
    (smoothOfRelativeDimension_isStableUnderBaseChange (n := g)).of_isPullback h hg
  obtain ⟨-, -, ⟨hcl', hinj', -⟩, -⟩ := H R' (Over.mk s') g hA' hg'
  let i' := formEquiv s' hcl' hinj'
  refine ⟨(LinearEquiv.baseChange R R' _ _ i).trans (e.trans i'.symm), fun c ↦ ?_⟩
  refine isPullForm_of_isPull1 h.w hcl' hinj' ⟨c, hcl ▸ trivial⟩ ⟨_, hcl' ▸ trivial⟩ ?_
  rw [← formEquiv_apply s' hcl' hinj', ← formEquiv_apply A.hom hcl hinj]
  have k : formEquiv s' hcl' hinj' (((LinearEquiv.baseChange R R' _ _ i).trans (e.trans i'.symm)) (1 ⊗ₜ c)) =
      e (1 ⊗ₜ i c) := i'.apply_symm_apply _
  rw [k]
  exact he (i c)

end FubiniStudyChowHeightFormula₂.Hdr

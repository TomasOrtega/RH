import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.GlobalHeightBoundIffAtGoodPrimes
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDividedDifference
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CkUniqueCharacterizationStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CapDegreeSymmetricStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CapDegreeFinitePullbackStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GenericIsoNormalModelStatement

open CategoryTheory Limits AlgebraicGeometry IsLocalRing MvPolynomial
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.DV Formalism.DegreeFormula Formalism.MainNotions.LatticeTransfer Formalism.MainNotions.WeightThresholdDefs
open GlobalTheory GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.Vert GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.Mean4O GlobalTheory.MixedLocalChains

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CkChain

variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]

open GlobalTheory.Vert.Model

/- English proof (translation)
Use `Iso.ext ?_` and prove the remaining obligations. Simplify using `[GenIso.pull]`.
-/
theorem pull_trans {Z Z₁ : Model O} {E E' E'' : Z.X.Modules} {f : Z₁.X ⟶ Z.X}
    (hf : f ≫ Z.str = Z₁.str) (φ : Z.GenIso E E') (φ' : Z.GenIso E' E'') :
    GenIso.pull hf (φ ≪≫ φ') = GenIso.pull hf φ ≪≫ GenIso.pull hf φ' := by
  refine Iso.ext ?_
  simp [GenIso.pull]

/- English proof (translation)
Establish `h : Z.genRes.map (fl.π i) = cokernel.π (Z.genRes.map (fl.step i)) ≫ (PreservesCokernel.iso Z.genRes (fl.step i)).inv`. Rewrite using `[PreservesCokernel.iso_inv, π_comp_cokernelComparison]`. Both sides reduce to the same expression. Rewrite using `[h]`. Conclude with `@epi_comp _ _ _ _ _ _ inferInstance _ (@IsIso.epi_of_iso _ _ _ _ _ (Iso.isIso_inv _))`.
-/
theorem epi_genRes_π {Z : Model O} {E : Z.X.Modules} {N : ℕ} (fl : Flag E N) (i : Fin N) :
    Epi (Z.genRes.map (fl.π i)) := by
  have h : Z.genRes.map (fl.π i) = cokernel.π (Z.genRes.map (fl.step i)) ≫
      (PreservesCokernel.iso Z.genRes (fl.step i)).inv := by
    rw [PreservesCokernel.iso_inv, π_comp_cokernelComparison]; rfl
  rw [h]
  exact @epi_comp _ _ _ _ _ _ inferInstance _ (@IsIso.epi_of_iso _ _ _ _ _ (Iso.isIso_inv _))

section Chain

variable {Z : Model O} {E E' E'' : Z.X.Modules} {N : ℕ} {φ : Z.GenIso E E'} {φ' : Z.GenIso E' E''}
  (P : FlagPair φ N) (fl'' : Flag E'' N) (gen₂ : ∀ i, Z.GenIso (P.fl'.F i) (fl''.F i))
  (h₂ : ∀ i, (gen₂ i).hom ≫ Z.genRes.map (fl''.ι i) = Z.genRes.map (P.fl'.ι i) ≫ φ'.hom)

def second : FlagPair φ' N := ⟨P.fl', fl'', gen₂, h₂⟩

def third (φ'' : Z.GenIso E E'') (h : φ''.hom = φ.hom ≫ φ'.hom) : FlagPair φ'' N :=
  ⟨P.fl, fl'', fun i => P.gen i ≪≫ gen₂ i, fun i => by
    rw [Iso.trans_hom, Category.assoc, h₂, ← Category.assoc, P.gen_ι, Category.assoc, h]⟩

/- English proof (translation)
Use `haveI := epi_genRes_π P.fl i`. Use `Iso.ext ((cancel_epi (Z.genRes.map (P.fl.π i))).1 ?_)` and prove the remaining obligations. Conclude with `((third P fl'' gen₂ h₂ φ'' h).π_grIso_hom i).trans ((Category.assoc _ _ _).trans ((congrArg ((P.gen i.succ).hom ≫ ·) ((second P fl'' gen₂ h₂).π_grIso_hom i).symm).trans (((Category.assoc _ _ _).symm.trans (congrArg (· ≫ ((second P fl'' gen₂ h₂).grIso i).hom) (P.π_grIso_hom i).sym …`.
-/
theorem grIso_third (φ'' : Z.GenIso E E'') (h : φ''.hom = φ.hom ≫ φ'.hom) (i : Fin N) :
    (third P fl'' gen₂ h₂ φ'' h).grIso i = P.grIso i ≪≫ (second P fl'' gen₂ h₂).grIso i := by
  haveI := epi_genRes_π P.fl i
  refine Iso.ext ((cancel_epi (Z.genRes.map (P.fl.π i))).1 ?_)
  exact ((third P fl'' gen₂ h₂ φ'' h).π_grIso_hom i).trans ((Category.assoc _ _ _).trans
    ((congrArg ((P.gen i.succ).hom ≫ ·) ((second P fl'' gen₂ h₂).π_grIso_hom i).symm).trans
      (((Category.assoc _ _ _).symm.trans (congrArg (· ≫ ((second P fl'' gen₂ h₂).grIso i).hom)
        (P.π_grIso_hom i).symm)).trans (Category.assoc _ _ _))))

variable (p : ℕ) [Fact p.Prime] [CharZero O] [CharP (ResidueField O) p]

/- English proof (translation)
Express the relevant statement in the definitionally equal form `toQ ((third P fl'' gen₂ h₂ φ'' h).div i).cls = toQ (P.div i).cls + toQ ((second P fl'' gen₂ h₂).div i).cls`. Rewrite using `[← map_add]`. Use `congrArg toQ ?_` and prove the remaining obligations. Use `show (((third P fl'' gen₂ h₂ φ'' h).grIso i).div _ _).cls = _`. Rewrite using `[grIso_third]`.

Conclude with `GenIso.cls_div_trans _ _ _ _ _`.
-/
theorem dv_third (φ'' : Z.GenIso E E'') (h : φ''.hom = φ.hom ≫ φ'.hom) (i : Fin N) :
    ((third P fl'' gen₂ h₂ φ'' h).toFPair p).Dv i =
      (P.toFPair p).Dv i + ((second P fl'' gen₂ h₂).toFPair p).Dv i := by
  change toQ ((third P fl'' gen₂ h₂ φ'' h).div i).cls =
    toQ (P.div i).cls + toQ ((second P fl'' gen₂ h₂).div i).cls
  rw [← map_add]
  refine congrArg toQ ?_
  show (((third P fl'' gen₂ h₂ φ'' h).grIso i).div _ _).cls = _
  rw [grIso_third]
  exact GenIso.cls_div_trans _ _ _ _ _

end Chain

/- English proof (translation)
Introduce `O _ _ _ p _ _ _ B hB E E' E'' φ φ' r k hE hE' hE''`. Establish `hadd : ∀ (E E' E'' : B.X.Modules) (φ : B.GenIso E E') (φ' : B.GenIso E' E''), GlobalTheory.VB.IsVB E r → GlobalTheory.VB.IsVB E' r → GlobalTheory.VB.IsVB E'' r → ckP p (φ ≪≫ φ') r k = ckP p φ r k + ckP p φ' r k`. Introduce `E E' E'' φ φ' hE hE' hE''`. Take `⟨B', f, hB', hf, P, ⟨fl₂, fl'', gen₂, h₂⟩, hP⟩` from `GlobalTheory.T.generic_iso_normal_model O p B hB E E' E'' φ φ' r hE hE' hE''`. Simplify using `only at hP`.

Substitute `hP` using the available equality. Establish `hc : (GenIso.pull f.comp_str (φ ≪≫ φ')).hom = (GenIso.pull f.comp_str φ).hom ≫ (GenIso.pull f.comp_str φ').hom` using `congrArg Iso.hom (pull_trans f.comp_str φ φ')`. Establish `hn` using `(GlobalTheory.T.cap_degree_finite_pullback O p B hB B' f hf).1`. Use `LinearMap.ext fun Q => mul_left_cancel₀ hn.ne' ?_` and prove the remaining obligations. Establish `c1 : ck (P.toFPair p) k (picSymPull f.f Q) = f.fibreDeg 1 * ckP p φ r k Q` using `(GlobalTheory.T.ck_unique_characterization O p B hB E E' φ r k hE hE').1 ⟨B', f, P⟩ hB' hf Q`.

Establish `c2 : ck ((second P fl'' gen₂ h₂).toFPair p) k (picSymPull f.f Q) = f.fibreDeg 1 * ckP p φ' r k Q` using `(GlobalTheory.T.ck_unique_characterization O p B hB E' E'' φ' r k hE' hE'').1 ⟨B', f, second P fl'' gen₂ h₂⟩ hB' hf Q`. Establish `c3 : ck ((third P fl'' gen₂ h₂ _ hc).toFPair p) k (picSymPull f.f Q) = f.fibreDeg 1 * ckP p (φ ≪≫ φ') r k Q` using `(GlobalTheory.T.ck_unique_characterization O p B hB E E'' (φ ≪≫ φ') r k hE hE'').1 ⟨B', f, third P fl'' gen₂ h₂ _ hc⟩ hB' hf Q`. Rewrite using `[LinearMap.add_apply, mul_add, ← c1, ← c2, ← c3]`. Conclude with `GlobalTheory.RootChernRules.ck_add (Z := B'.toITh p) (GlobalTheory.T.cap_degree_symmetric O p B' hB') (P.toFPair p) ((second P fl'' gen₂ h₂).toFPair p) ((third P fl'' gen₂ h₂ _ hc).toFPair p) rfl rfl rfl (dv_third P fl'' gen₂ h₂ p _ hc) k (picSymPull f.f Q)`. Establish `hrefl : ckP p (Iso.refl (B.genRes.obj E)) r k = 0`.

Establish `h` using `hadd E E E (Iso.refl _) (Iso.refl _) hE hE hE`. Rewrite `h` using `[Iso.refl_trans]`. Simplify using `using h`. Use `⟨hadd E E' E'' φ φ' hE hE' hE'', ?_⟩` and prove the remaining obligations. Establish `h` using `hadd E E' E φ φ.symm hE hE' hE`.

Rewrite `h` using `[Iso.self_symm_id, hrefl]`. Conclude with `eq_neg_of_add_eq_zero_right h.symm`.
-/
theorem ckP_trans : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (p : ℕ) [Fact p.Prime] [CharZero O] [CharP (ResidueField O) p] (B : GlobalTheory.Vert.Model O), GlobalTheory.IsNormalScheme B.X → ∀ (E E' E'' : B.X.Modules) (φ : B.GenIso E E') (φ' : B.GenIso E' E'') (r k : ℕ), GlobalTheory.VB.IsVB E r → GlobalTheory.VB.IsVB E' r → GlobalTheory.VB.IsVB E'' r → ckP p (φ ≪≫ φ') r k = ckP p φ r k + ckP p φ' r k ∧ ckP p φ.symm r k = -ckP p φ r k := by
  intro O _ _ _ p _ _ _ B hB E E' E'' φ φ' r k hE hE' hE''
  have hadd : ∀ (E E' E'' : B.X.Modules) (φ : B.GenIso E E') (φ' : B.GenIso E' E''),
      GlobalTheory.VB.IsVB E r → GlobalTheory.VB.IsVB E' r → GlobalTheory.VB.IsVB E'' r →
      ckP p (φ ≪≫ φ') r k = ckP p φ r k + ckP p φ' r k := by
    intro E E' E'' φ φ' hE hE' hE''
    obtain ⟨B', f, hB', hf, P, ⟨fl₂, fl'', gen₂, h₂⟩, hP⟩ :=
      GlobalTheory.T.generic_iso_normal_model O p B hB E E' E'' φ φ' r hE hE' hE''
    dsimp only at hP
    subst hP
    have hc : (GenIso.pull f.comp_str (φ ≪≫ φ')).hom =
        (GenIso.pull f.comp_str φ).hom ≫ (GenIso.pull f.comp_str φ').hom :=
      congrArg Iso.hom (pull_trans f.comp_str φ φ')
    have hn := (GlobalTheory.T.cap_degree_finite_pullback O p B hB B' f hf).1
    refine LinearMap.ext fun Q => mul_left_cancel₀ hn.ne' ?_
    have c1 : ck (P.toFPair p) k (picSymPull f.f Q) = f.fibreDeg 1 * ckP p φ r k Q :=
      (GlobalTheory.T.ck_unique_characterization O p B hB E E' φ r k hE hE').1 ⟨B', f, P⟩ hB' hf Q
    have c2 : ck ((second P fl'' gen₂ h₂).toFPair p) k (picSymPull f.f Q) =
        f.fibreDeg 1 * ckP p φ' r k Q :=
      (GlobalTheory.T.ck_unique_characterization O p B hB E' E'' φ' r k hE' hE'').1 ⟨B', f, second P fl'' gen₂ h₂⟩ hB' hf Q
    have c3 : ck ((third P fl'' gen₂ h₂ _ hc).toFPair p) k (picSymPull f.f Q) =
        f.fibreDeg 1 * ckP p (φ ≪≫ φ') r k Q :=
      (GlobalTheory.T.ck_unique_characterization O p B hB E E'' (φ ≪≫ φ') r k hE hE'').1 ⟨B', f, third P fl'' gen₂ h₂ _ hc⟩ hB' hf Q
    rw [LinearMap.add_apply, mul_add, ← c1, ← c2, ← c3]
    exact GlobalTheory.RootChernRules.ck_add (Z := B'.toITh p) (GlobalTheory.T.cap_degree_symmetric O p B' hB') (P.toFPair p)
      ((second P fl'' gen₂ h₂).toFPair p) ((third P fl'' gen₂ h₂ _ hc).toFPair p) rfl rfl rfl
      (dv_third P fl'' gen₂ h₂ p _ hc) k (picSymPull f.f Q)
  have hrefl : ckP p (Iso.refl (B.genRes.obj E)) r k = 0 := by
    have h := hadd E E E (Iso.refl _) (Iso.refl _) hE hE hE
    rw [Iso.refl_trans] at h
    simpa using h
  refine ⟨hadd E E' E'' φ φ' hE hE' hE'', ?_⟩
  have h := hadd E E' E φ φ.symm hE hE' hE
  rw [Iso.self_symm_id, hrefl] at h
  exact eq_neg_of_add_eq_zero_right h.symm

end GlobalTheory.CkChain

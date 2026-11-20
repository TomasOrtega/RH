import Mathlib
import Development.AbelianVarietyTheory.Definitions.PlaceAdaptation.AdaptStd
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.FrameTieHolds
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.GermDPf
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.GermDVal
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.GermFunPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.SectionScalarValuation

set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.PtTie
open ReciprocityTheory.ChartRestriction.G.TB (dAct dLin)
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.PlaceInt

namespace GlobalTheory.RegularGerm

/- English proof (translation)
Unfold `psJet jetCoef`. Rewrite using `[Ideal.Quotient.lift_mk, RingHom.comp_apply]`. Use `congr 1`. Unfold `psTrunc`. Simplify using `[map_sum, MvPolynomial.map_monomial, MvPowerSeries.coeff_map]`.
-/
theorem psJet_map {R R' : Type} [CommRing R] [CommRing R'] (f : R →+* R') {κ : Type} [Fintype κ] [DecidableEq κ]
    (m : ℕ) (g : MvPowerSeries κ R) : psJet m (MvPowerSeries.map f g) = jetCoef f κ m (psJet m g) := by
  unfold psJet jetCoef
  rw [Ideal.Quotient.lift_mk, RingHom.comp_apply]
  congr 1
  unfold psTrunc
  simp [map_sum, MvPolynomial.map_monomial, MvPowerSeries.coeff_map]

/- English proof (translation)
Establish `h : psTrunc m (c • f) = MvPolynomial.C c * psTrunc m f`. Simplify using `only [psTrunc, Finset.mul_sum, MvPolynomial.C_mul_monomial, map_smul, smul_eq_mul]`. Rewrite using `[psJet, h]`. Both sides reduce to the same expression.
-/
theorem psJet_smul {F κ : Type} [CommRing F] [Fintype κ] [DecidableEq κ] (m : ℕ) (c : F) (f : MvPowerSeries κ F) :
    psJet m (c • f) = algebraMap F (Jet F κ m) c * psJet m f := by
  have h : psTrunc m (c • f) = MvPolynomial.C c * psTrunc m f := by
    simp only [psTrunc, Finset.mul_sum, MvPolynomial.C_mul_monomial, map_smul, smul_eq_mul]
  rw [psJet, h]
  rfl

/- English proof (translation)
Use `(gs_pull r (spMap f) z ⊤ trivial (toΓ A a)).symm.trans ?_` and prove the remaining obligations. Conclude with `congrArg (gs r z ⊤) (congrArg (fun φ => φ.hom a) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom f))).symm`.
-/
theorem gs_spMap_toΓ {A B : Type} [CommRing A] [CommRing B] (f : A →+* B) {Z : Scheme.{0}} (r : Z ⟶ Sp B) (z : Z)
    (a : A) : gs (r ≫ spMap f) z ⊤ (toΓ A a) = gs r z ⊤ (toΓ B (f a)) := by
  refine (gs_pull r (spMap f) z ⊤ trivial (toΓ A a)).symm.trans ?_
  exact congrArg (gs r z ⊤)
    (congrArg (fun φ => φ.hom a) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom f))).symm

/- English proof (translation)
Substitute `h₁ h₂` using the available equality. Establish `hs : s = v * e.val ^ k`. Use `(Units.mul_right_inj (u₂ ^ k)).1 ?_` and prove the remaining obligations. Rewrite using `[Units.val_pow_eq_pow_val, ← hb, hv, Units.val_pow_eq_pow_val, Units.val_mul]`. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[ha, hs, Units.val_pow_eq_pow_val, Units.val_mul]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem tie_alg {R : Type} [CommRing R] {a b s v : R} {u₁ u₂ e e₁ e₂ : Rˣ} {k : ℕ} (ha : a = u₁.val ^ k * s)
    (hb : b = u₂.val ^ k * s) (hv : b = v * (e₂ ^ k).val) (h₁ : e₁ = u₁ * e) (h₂ : e₂ = u₂ * e) :
    a = v * (e₁ ^ k).val := by
  subst h₁ h₂
  have hs : s = v * e.val ^ k := by
    refine (Units.mul_right_inj (u₂ ^ k)).1 ?_
    rw [Units.val_pow_eq_pow_val, ← hb, hv, Units.val_pow_eq_pow_val, Units.val_mul]
    ring
  rw [ha, hs, Units.val_pow_eq_pow_val, Units.val_mul]
  ring

section Values
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {X : Scheme.{0}} {t : SAB H X}

abbrev sv (t : SAB H X) {k : ℤ} {T : Over X} (s : LB.Sec (LPow t.G t.PP.L k T)) {Z : Scheme.{0}} (r : Z ⟶ (T ⊗ t.G).left)
    (z : Z) (J : (Z ⟶ t.G.left) → t.PP.L.ι) : Z.presheaf.stalk z :=
  sval (L := t.PP.L) (φ := fun _ : Fin 1 => (snd T t.G).left) (ε := fun _ => k) s r z J

/- English proof (translation)
Rewrite using `[← Over.comp_left, ptSecT, lift_snd]`.
-/
theorem ptSecT_snd {T : Over X} (a : T ⟶ t.G) : (ptSecT t.G a).left ≫ (snd T t.G).left = a.left := by
  rw [← Over.comp_left, ptSecT, lift_snd]

/- English proof (translation)
Establish `hz` using `hJ.mem (fun _ : Fin 1 => a.left) r`. Use `(sval_of (φ := fun _ : Fin 1 => (snd T t.G).left) (ε := fun _ => n) s _ z J (fun _ => J (r ≫ a.left)) (fun _ => by rw [Category.assoc, ptSecT_snd])).trans ?_` and prove the remaining obligations. Conclude with `((gs_res r z _ hz _).trans (gs_pull r (ptSecT t.G a).left z _ (val_le t.G t.PP.L a _ hz) _)).symm.trans ((congrArg (gs r z _) (h _)).trans ((gs_mul r z _ hz _ _).trans (congrArg₂ (· * ·) (gs_res r z le_top hz c) (gs_unit r z _ hz _))))`.
-/
theorem sv_of_isValueAt {n : ℤ} {T : Over X} {s : LB.Sec (LPow t.G t.PP.L n T)} {a : T ⟶ t.G}
    {τ : LB.Gen (LB.LinComb t.PP.L (Y := T.left) (K := Fin 1) (fun _ => a.left) (fun _ => n))} {c : Γ(T.left, ⊤)}
    (h : IsValueAt t.G t.PP.L n s a τ c) {Z : Scheme.{0}} (r : Z ⟶ T.left) (z : Z) {J}
    (hJ : Good t.PP.L z J) : sv t s (r ≫ (ptSecT t.G a).left) z J = gs r z ⊤ c * (val τ r z J).val := by
  have hz := hJ.mem (fun _ : Fin 1 => a.left) r
  refine (sval_of (φ := fun _ : Fin 1 => (snd T t.G).left) (ε := fun _ => n) s _ z J (fun _ => J (r ≫ a.left))
    (fun _ => by rw [Category.assoc, ptSecT_snd])).trans ?_
  exact ((gs_res r z _ hz _).trans (gs_pull r (ptSecT t.G a).left z _ (val_le t.G t.PP.L a _ hz) _)).symm.trans
    ((congrArg (gs r z _) (h _)).trans ((gs_mul r z _ hz _ _).trans
      (congrArg₂ (· * ·) (gs_res r z le_top hz c) (gs_unit r z _ hz _))))

/- English proof (translation)
Introduce `j` and use `fn_ext fun y hy => by obtain ⟨J, hJ, e⟩ := exists_good t.PP.L t.PP.isLB y (fun _ : Fin 1 => a.left) j (fun a b _ => congrArg j (Subsingleton.elim a b)) (fun k => Set.mem_iInter.1 hy k) have q := h y J hJ rw [val_of τ _ y J j (fun k => by rw [Category.id_comp]; exact e k)] at q ha …`.
-/
theorem isValueAt_of_sv {n : ℤ} {T : Over X} {s : LB.Sec (LPow t.G t.PP.L n T)} {a : T ⟶ t.G}
    {τ : LB.Gen (LB.LinComb t.PP.L (Y := T.left) (K := Fin 1) (fun _ => a.left) (fun _ => n))} {c : Γ(T.left, ⊤)}
    (h : ∀ (z : T.left) J, Good t.PP.L z J →
      sv t s (𝟙 _ ≫ (ptSecT t.G a).left) z J = gs (𝟙 _) z ⊤ c * (val τ (𝟙 _) z J).val) :
    IsValueAt t.G t.PP.L n s a τ c := fun j => fn_ext fun y hy => by
  obtain ⟨J, hJ, e⟩ := exists_good t.PP.L t.PP.isLB y (fun _ : Fin 1 => a.left) j
    (fun a b _ => congrArg j (Subsingleton.elim a b)) (fun k => Set.mem_iInter.1 hy k)
  have q := h y J hJ
  rw [val_of τ _ y J j (fun k => by rw [Category.id_comp]; exact e k)] at q
  have q' := (sval_of (φ := fun _ : Fin 1 => (snd T t.G).left) (ε := fun _ => n) s (𝟙 _ ≫ (ptSecT t.G a).left) y J j
    (fun k => by rw [Category.id_comp, ptSecT_snd]; exact e k)).symm.trans q
  exact ((gs_res _ y _ hy _).trans (gs_pull _ (ptSecT t.G a).left y _ (val_le t.G t.PP.L a _ hy) _)).trans
    (q'.trans ((gs_mul _ y _ hy _ _).trans
      (congrArg₂ (· * ·) (gs_res _ y le_top hy c) (gs_unit _ y _ hy _))).symm)

/- English proof (translation)
The claim follows from `(GermD.pullSec_stalk t.G t.PP.L n hs r z _ (hJ.mem (fun _ : Fin 1 => (snd T' t.G).left) r)).trans (sval_of (φ := fun _ : Fin 1 => (snd T t.G).left) (ε := fun _ => n) s _ z J _ (fun _ => by rw [Category.assoc, ← Over.comp_left, hh])).symm`.
-/
theorem sv_pullSec {n : ℤ} {T T' : Over X} {h : T' ⊗ t.G ⟶ T ⊗ t.G} {hh : h ≫ snd T t.G = snd T' t.G}
    {s : LB.Sec (LPow t.G t.PP.L n T)} {s' : LB.Sec (LPow t.G t.PP.L n T')} (hs : IsPullSec t.G t.PP.L n h hh s s')
    {Z : Scheme.{0}} (r : Z ⟶ (T' ⊗ t.G).left) (z : Z) {J} (hJ : Good t.PP.L z J) :
    sv t s' r z J = sv t s (r ≫ h.left) z J :=
  (GermD.pullSec_stalk t.G t.PP.L n hs r z _ (hJ.mem (fun _ : Fin 1 => (snd T' t.G).left) r)).trans
    (sval_of (φ := fun _ : Fin 1 => (snd T t.G).left) (ε := fun _ => n) s _ z J _
      (fun _ => by rw [Category.assoc, ← Over.comp_left, hh])).symm

/- English proof (translation)
Establish `hm` using `hJ.mem (fun _ : Fin 1 => (snd T t.G).left) r`. Conclude with `(congrArg (gs r z _) (h _)).trans ((gs_mul r z _ hm _ _).trans (congrArg₂ (· * ·) ((gs_res r z le_top hm _).trans (gs_pull r (fst T t.G).left z ⊤ trivial c)) rfl))`.
-/
theorem sv_scale {n : ℤ} {T : Over X} {s s' : LB.Sec (LPow t.G t.PP.L n T)} {c : Γ(T.left, ⊤)}
    (h : ∀ j, s'.f j = liftFun t.G _ c * s.f j) {Z : Scheme.{0}} (r : Z ⟶ (T ⊗ t.G).left) (z : Z) {J}
    (hJ : Good t.PP.L z J) : sv t s' r z J = gs (r ≫ (fst T t.G).left) z ⊤ c * sv t s r z J := by
  have hm := hJ.mem (fun _ : Fin 1 => (snd T t.G).left) r
  exact (congrArg (gs r z _) (h _)).trans ((gs_mul r z _ hm _ _).trans (congrArg₂ (· * ·)
    ((gs_res r z le_top hm _).trans (gs_pull r (fst T t.G).left z ⊤ trivial c)) rfl))

variable {S : Type} [CommRing S] {x0 : Sp S ⟶ X} {d : ℕ}

def jetPt {m : ℕ} (a : jOG x0 d m 1 ⟶ t.G) : (jOG x0 d m 1).left ⟶ (Over.mk x0 ⊗ t.G).left :=
  (ptSecT t.G a).left ≫ (jBaseG x0 d m 1 ▷ t.G).left

/- English proof (translation)
Rewrite using `[jetPt, ← Over.comp_left, ← Over.comp_left, ptSecT, lift_whiskerRight, lift_snd]`.
-/
theorem jetPt_snd {m : ℕ} (a : jOG x0 d m 1 ⟶ t.G) : jetPt a ≫ (snd (Over.mk x0) t.G).left = a.left := by
  rw [jetPt, ← Over.comp_left, ← Over.comp_left, ptSecT, lift_whiskerRight, lift_snd]

/- English proof (translation)
Rewrite using `[jetPt, ← Over.comp_left, ← Over.comp_left, ptSecT, lift_whiskerRight, lift_fst, Category.id_comp]`. Both sides reduce to the same expression.
-/
theorem jetPt_fst {m : ℕ} (a : jOG x0 d m 1 ⟶ t.G) :
    jetPt a ≫ (fst (Over.mk x0) t.G).left = spMap (algebraMap S (Jet S (Fin 1 × Fin d) m)) := by
  rw [jetPt, ← Over.comp_left, ← Over.comp_left, ptSecT, lift_whiskerRight, lift_fst, Category.id_comp]; rfl

variable {x : ∀ m, jOG x0 d m 1 ⟶ t.G} {act : 𝓞 E → Fin d → MvPowerSeries (Fin 1 × Fin d) S}
  {e : ∀ m, FrTyG t x0 d x m} {wP : PrimTyG t} {k : ℕ} {s : LB.Sec (LPow t.G t.PP.L k (Over.mk x0))}
  {f : MvPowerSeries (Fin 1 × Fin d) S}

/- English proof (translation)
Take `⟨s₁, τ, hp, hτ, hv⟩` from `h m`. Establish `q₁` using `sv_of_isValueAt hv r z hJ`. Establish `q₂` using `(val_corr hJ hτ r).trans (GermD.val_genPowG t _ _ _ k r z J)`. Establish `q₃` using `sv_pullSec hp (r ≫ (ptSecT t.G (x m)).left) z hJ`. Rewrite `q₃` using `[Category.assoc]`.

Rewrite using `[← q₂]`. Conclude with `q₃.symm.trans q₁`.
-/
theorem sv_of_isGerm (h : IsGermG t x0 d x act e wP k s f) (m : ℕ) {Z : Scheme.{0}} (r : Z ⟶ (jOG x0 d m 1).left) (z : Z)
    {J} (hJ : Good t.PP.L z J) :
    sv t s (r ≫ jetPt (x m)) z J =
      gs r z ⊤ (toΓ _ (psJet m f)) * (val (eLG t x0 d x act e wP m) r z J ^ k).val := by
  obtain ⟨s₁, τ, hp, hτ, hv⟩ := h m
  have q₁ := sv_of_isValueAt hv r z hJ
  have q₂ := (val_corr hJ hτ r).trans (GermD.val_genPowG t _ _ _ k r z J)
  have q₃ := sv_pullSec hp (r ≫ (ptSecT t.G (x m)).left) z hJ
  rw [Category.assoc] at q₃
  rw [← q₂]
  exact q₃.symm.trans q₁

/- English proof (translation)
Introduce `m`. Establish `heL : (eLG t x0 d x act e wP m).IsGen` using `DVR.mulGen_isGen t.PP.L _ _ _ _ _ _ (DVR.pullGen_isGen t.PP.L _ _ _ hP _) (DVR.pullGen_isGen t.PP.L _ _ _ (hg m) _)`. Take `⟨τ, -, hτ⟩ : ∃ τ : LB.Gen (LB.LinComb t.PP.L (Y` from `(jOG x0 d m 1).left) (K := Fin 1) (fun _ => (x m).left) fun _ => (k : ℤ)), τ.IsGen ∧ ∀ (Z : Scheme.{0}) (r : Z ⟶ (jOG x0 d m 1).left) (z : Z) (J : (Z ⟶ t.G.left) → t.PP.L.ι), Good t.PP.L z J → val τ r z J = val (genPowG t _ _ (eLG t x0 d x act e wP m) k) r z J := by`. Use `exists_gen t.PP.isLB ?_ _ (GermD.genPowG_isGen t _ _ _ heL k)` and prove the remaining obligations. Introduce `U _ hU`.

Simplify using `only [Fintype.prod_sum_type, Sum.elim_inl, Sum.elim_inr, Fin.prod_univ_one, Category.comp_id, _root_.mul_one, GermD.formEq_eL hc m]`. Rewrite using `[_root_.mul_assoc, ← Finset.prod_mul_distrib]`. Simplify using `only [← zpow_add, _root_.mul_neg, neg_add_cancel, zpow_zero, Finset.prod_const_one, _root_.mul_one]`. Take `⟨s₁, hp⟩` from `GermD.exists_pullSec t.G t.PP.L (k : ℤ) (jBaseG x0 d m 1 ▷ t.G) (whiskerRight_snd _ _) s`. Use `⟨s₁, τ, hp, corr_of_val t.PP.isLB fun y J hJ => hτ _ _ y J hJ, isValueAt_of_sv fun z J hJ => ?_⟩` and prove the remaining obligations.

Establish `q₃` using `(hτ _ (𝟙 _) z J hJ).trans (GermD.val_genPowG t _ _ _ k (𝟙 _) z J)`. Use `(sv_pullSec hp _ z hJ).trans ?_` and prove the remaining obligations. Rewrite using `[Category.assoc, q₃]`. Conclude with `h m z J hJ`.
-/
theorem isGerm_of_sv {F : Fin d → MvPowerSeries (Fin 2 × Fin d) S} {κ : Type} [Fintype κ]
    {tg : κ → (Sp (DualNumber S) ⟶ t.G.left)} {uvec : κ → Fin d → S} (hc : IsChartG t x0 d F act tg uvec x)
    (hP : wP.IsGen) (hg : ∀ m, (e m).IsGen)
    (h : ∀ (m : ℕ) (z : (jOG x0 d m 1).left) J, Good t.PP.L z J → sv t s (𝟙 _ ≫ jetPt (x m)) z J =
      gs (𝟙 _) z ⊤ (toΓ _ (psJet m f)) * (val (eLG t x0 d x act e wP m) (𝟙 _) z J ^ k).val) :
    IsGermG t x0 d x act e wP k s f := by
  intro m
  have heL : (eLG t x0 d x act e wP m).IsGen :=
    DVR.mulGen_isGen t.PP.L _ _ _ _ _ _ (DVR.pullGen_isGen t.PP.L _ _ _ hP _) (DVR.pullGen_isGen t.PP.L _ _ _ (hg m) _)
  obtain ⟨τ, -, hτ⟩ : ∃ τ : LB.Gen (LB.LinComb t.PP.L (Y := (jOG x0 d m 1).left) (K := Fin 1) (fun _ => (x m).left)
      fun _ => (k : ℤ)), τ.IsGen ∧ ∀ (Z : Scheme.{0}) (r : Z ⟶ (jOG x0 d m 1).left) (z : Z)
        (J : (Z ⟶ t.G.left) → t.PP.L.ι), Good t.PP.L z J →
          val τ r z J = val (genPowG t _ _ (eLG t x0 d x act e wP m) k) r z J := by
    refine exists_gen t.PP.isLB ?_ _ (GermD.genPowG_isGen t _ _ _ heL k)
    intro U _ hU
    simp only [Fintype.prod_sum_type, Sum.elim_inl, Sum.elim_inr, Fin.prod_univ_one, Category.comp_id, _root_.mul_one,
      GermD.formEq_eL hc m]
    rw [_root_.mul_assoc, ← Finset.prod_mul_distrib]
    simp only [← zpow_add, _root_.mul_neg, neg_add_cancel, zpow_zero, Finset.prod_const_one, _root_.mul_one]
  obtain ⟨s₁, hp⟩ := GermD.exists_pullSec t.G t.PP.L (k : ℤ) (jBaseG x0 d m 1 ▷ t.G) (whiskerRight_snd _ _) s
  refine ⟨s₁, τ, hp, corr_of_val t.PP.isLB fun y J hJ => hτ _ _ y J hJ, isValueAt_of_sv fun z J hJ => ?_⟩
  have q₃ := (hτ _ (𝟙 _) z J hJ).trans (GermD.val_genPowG t _ _ _ k (𝟙 _) z J)
  refine (sv_pullSec hp _ z hJ).trans ?_
  rw [Category.assoc, q₃]
  exact h m z J hJ

/- English proof (translation)
Use `isGerm_of_sv hc hP hg fun m z J hJ => ?_` and prove the remaining obligations. Use `(sv_scale hs _ z hJ).trans ?_` and prove the remaining obligations. Rewrite using `[sv_of_isGerm h m (𝟙 _) z hJ, Category.assoc, jetPt_fst, psJet_smul, map_mul, ← _root_.mul_assoc]`. Use `congrArg₂ (· * ·) ?_ rfl` and prove the remaining obligations. Conclude with `(congrArg₂ (· * ·) (gs_spMap_toΓ _ _ z a) rfl).trans (gs_mul _ z ⊤ trivial _ _).symm`.
-/
theorem isGerm_smul {F : Fin d → MvPowerSeries (Fin 2 × Fin d) S} {κ : Type} [Fintype κ]
    {tg : κ → (Sp (DualNumber S) ⟶ t.G.left)} {uvec : κ → Fin d → S} (hc : IsChartG t x0 d F act tg uvec x)
    (hP : wP.IsGen) (hg : ∀ m, (e m).IsGen) {s' : LB.Sec (LPow t.G t.PP.L k (Over.mk x0))} {a : S}
    (hs : ∀ j, s'.f j = liftFun t.G _ (T := Over.mk x0) (toΓ S a) * s.f j) (h : IsGermG t x0 d x act e wP k s f) :
    IsGermG t x0 d x act e wP k s' (a • f) := by
  refine isGerm_of_sv hc hP hg fun m z J hJ => ?_
  refine (sv_scale hs _ z hJ).trans ?_
  rw [sv_of_isGerm h m (𝟙 _) z hJ, Category.assoc, jetPt_fst, psJet_smul, map_mul, ← _root_.mul_assoc]
  refine congrArg₂ (· * ·) ?_ rfl
  exact (congrArg₂ (· * ·) (gs_spMap_toΓ _ _ z a) rfl).trans (gs_mul _ z ⊤ trivial _ _).symm

end Values

/- English proof (translation)
Take `⟨σ', hσ'⟩` from `exists_sec t.PP.isLB (φ := fun _ : Fin 1 => (snd T t.G).left ≫ 𝟙 t.G.left) (ε := fun _ => n) (φ' := fun _ : Fin 1 => (snd T t.G).left) (ε' := fun _ => n) (fun U _ f => by simp) (ReciprocityTheory.ChartRestriction.G.DVR.pullSec t.PP.L (fun _ => 𝟙 t.G.left) (fun _ => n) σ (snd T t. …`. Conclude with `⟨σ', fun Z r z J hJ => (hσ' Z r z J hJ).trans (DVR.SectionScalarValuation.sval_pullSec _ _ σ _ r z hJ)⟩`.
-/
theorem exists_sec_id {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {X : Scheme.{0}} (t : SAB H X) (n : ℤ)
    (σ : LB.Sec (LB.LinComb t.PP.L (K := Fin 1) (fun _ => 𝟙 t.G.left) (fun _ => n))) (T : Over X) :
    ∃ σ' : LB.Sec (LPow t.G t.PP.L n T), ∀ (Z : Scheme.{0}) (r : Z ⟶ (T ⊗ t.G).left) (z : Z) (J),
      Good t.PP.L z J → sv t σ' r z J = sval σ (r ≫ (snd T t.G).left) z J := by
  obtain ⟨σ', hσ'⟩ := exists_sec t.PP.isLB
    (φ := fun _ : Fin 1 => (snd T t.G).left ≫ 𝟙 t.G.left)
    (ε := fun _ => n) (φ' := fun _ : Fin 1 => (snd T t.G).left)
    (ε' := fun _ => n) (fun U _ f => by simp)
    (ReciprocityTheory.ChartRestriction.G.DVR.pullSec t.PP.L (fun _ => 𝟙 t.G.left) (fun _ => n) σ (snd T t.G).left)
  exact ⟨σ', fun Z r z J hJ => (hσ' Z r z J hJ).trans (DVR.SectionScalarValuation.sval_pullSec _ _ σ _ r z hJ)⟩

section Chart
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l} [StarRing (𝓞 E)] {T : CDVR} {io : c.F →+* T.Fr} {y : IntFr Xo c T io}

/- English proof (translation)
Introduce `f g h` and use `by ext n refine IsFractionRing.injective T.V T.Fr ?_ rw [← MvPowerSeries.coeff_map, ← MvPowerSeries.coeff_map, h]`.
-/
theorem map_injective {κ : Type} :
    Function.Injective (MvPowerSeries.map (σ := κ) (algebraMap T.V T.Fr)) := fun f g h => by
  ext n
  refine IsFractionRing.injective T.V T.Fr ?_
  rw [← MvPowerSeries.coeff_map, ← MvPowerSeries.coeff_map, h]

/- English proof (translation)
Use `letI := io.toAlgebra`. Conclude with `map_injective (isGermFun_holds E H Dw l Xo c T.Fr y.1 _ _ _ _ _ k F _ _ h h')`.
-/
theorem germIs_unique (C : IntegralChartA3 Xo c T io y) (k : ℕ) (F : SecN Xo (xOf y) k) (f f' : PS T.V 1 (chD C.ch))
    (h : GermIs C k F f) (h' : GermIs C k F f') : f = f' := by
  letI := io.toAlgebra
  exact map_injective (isGermFun_holds E H Dw l Xo c T.Fr y.1 _ _ _ _ _ k F _ _ h h')

/- English proof (translation)
Use `letI := io.toAlgebra`. Establish `e : MvPowerSeries.map (algebraMap T.V T.Fr) (r • f) = algebraMap T.V T.Fr r • MvPowerSeries.map (algebraMap T.V T.Fr) f`. Use extensionality with `n`. Rewrite using `[MvPowerSeries.coeff_map, MvPowerSeries.coeff_smul, MvPowerSeries.coeff_smul, MvPowerSeries.coeff_map, map_mul]`. Establish `q` using `isGerm_smul ((isChart_iff y.1 _ _ _ _ _).1 C.ch.chart) C.ch.prim.1 C.ch.frame.gen hs ((isGerm_iff y.1 _ _ _ _ _ _ _ _).1 h)`.

Rewrite `q` using `[← e]`. Conclude with `(isGerm_iff y.1 _ _ _ _ _ _ _ _).2 q`.
-/
theorem germIs_smul (C : IntegralChartA3 Xo c T io y) (k : ℕ) (F F' : SecN Xo (xOf y) k) (r : T.V) (f : PS T.V 1 (chD C.ch))
    (hs : ∀ j, F'.f j = liftFun Xo.univ.t.G _ (T := ptO Xo (xOf y)) (toΓ T.Fr (algebraMap T.V T.Fr r)) * F.f j)
    (h : GermIs C k F f) : GermIs C k F' (r • f) := by
  letI := io.toAlgebra
  have e : MvPowerSeries.map (algebraMap T.V T.Fr) (r • f) =
      algebraMap T.V T.Fr r • MvPowerSeries.map (algebraMap T.V T.Fr) f := by
    ext n
    rw [MvPowerSeries.coeff_map, MvPowerSeries.coeff_smul, MvPowerSeries.coeff_smul, MvPowerSeries.coeff_map, map_mul]
  have q := isGerm_smul ((isChart_iff y.1 _ _ _ _ _).1 C.ch.chart) C.ch.prim.1 C.ch.frame.gen hs
    ((isGerm_iff y.1 _ _ _ _ _ _ _ _).1 h)
  rw [← e] at q
  exact (isGerm_iff y.1 _ _ _ _ _ _ _ _).2 q

set_option maxHeartbeats 1600000 in

/- English proof (translation)
Use `letI := io.toAlgebra`. Take `⟨σ, σt, hT1, hT2⟩` from `hF`. Take `⟨x', hx1, hx2, eL', heL'⟩` from `hFT T io y C`. Take `⟨σ', hσ'⟩` from `exists_sec_id C.I.G (k : ℤ) σ (Over.mk (𝟙 (Sp T.V)))`. Take `⟨fV, hfV⟩` from `germSt_holds E H (Sp T.V) C.I.G T.V (𝟙 _) (chD C.ch) C.FT C.actT (Fin (chD C.ch)) C.tgT (fun j => Pi.single j (1 : T.V)) C.xT C.ph1T C.ph2T C.syT C.adT C.eT C.wPT C.chartT C.frameT C.primT hC k σ'`.

Use `⟨fV, (isGerm_iff y.1 _ _ _ _ _ _ _ _).2 (isGerm_of_sv ((isChart_iff y.1 _ _ _ _ _).1 C.ch.chart) C.ch.prim.1 C.ch.frame.gen fun m z J hJ => ?_)⟩` and prove the remaining obligations. Take `⟨J', hJ', -⟩` from `exists_good C.I.t'.PP.L C.I.t'.PP.isLB z (K := PEmpty) PEmpty.elim PEmpty.elim (fun a => a.elim) (fun a => a.elim)`. Take `⟨J'', hJ'', -⟩` from `exists_good C.I.G.PP.L C.I.G.PP.isLB z (K := PEmpty) PEmpty.elim PEmpty.elim (fun a => a.elim) (fun a => a.elim)`. Set `ρ : Sp (Jet T.Fr (Fin 1 × Fin (chD C.ch)) m) ⟶ Sp (Jet T.V (Fin 1 × Fin (chD C.ch)) m)` to `spMap (jetCoef (algebraMap T.V T.Fr) (Fin 1 × Fin (chD C.ch)) m)`. Set `i : Sp (Jet T.Fr (Fin 1 × Fin (chD C.ch)) m) ⟶ Sp (Jet T.Fr (Fin 1 × Fin (chD C.ch)) m)` to `𝟙 _`.

Take `⟨f₁, f₂⟩` from `heL' m _ i z J J' J'' hJ hJ' hJ''`. Establish `a₁` using `hT1 _ (i ≫ (x' m).left) (i ≫ jetPt (C.ch.x m)) ((Category.assoc _ _ _).trans ((congrArg (i ≫ ·) ((jetPt_snd (C.ch.x m)).trans (hx1 m).symm)).trans (Category.assoc _ _ _).symm)) ((Category.assoc _ _ _).trans ((congrArg (i ≫ ·) ((jetPt_fst (C.ch.x m)).trans ((Over.w (x' m)).trans ( …`. Establish `a₂` using `hT2 _ (i ≫ (x' m).left) z J'' J' hJ'' hJ'`. Establish `a₃` using `sv_of_isGerm hfV m (i ≫ ρ) z hJ''`. Establish `a₄` using `hσ' _ ((i ≫ ρ) ≫ jetPt (C.xT m)) z J'' hJ''`.

Establish `b : ((i ≫ ρ) ≫ jetPt (C.xT m)) ≫ (snd (Over.mk (𝟙 (Sp T.V))) C.I.G.G).left = (i ≫ (x' m).left) ≫ C.I.m2.φ` using `(Category.assoc _ _ _).trans ((congrArg ((i ≫ ρ) ≫ ·) (jetPt_snd (C.xT m))).trans ((Category.assoc _ _ _).trans ((congrArg (i ≫ ·) (hx2 m).symm).trans (Category.assoc _ _ _).symm)))`. Establish `a₅` using `(congrArg (fun q => sval σ q z J'') b).symm.trans (a₄.symm.trans a₃)`. Use `(tie_alg a₁ a₂ a₅ f₁ f₂).trans (congrArg₂ (· * ·) ?_ rfl)` and prove the remaining obligations. Rewrite using `[psJet_map]`. Conclude with `gs_spMap_toΓ _ i z _`.
-/
theorem exists_germIs (hFT : ReciprocityTheory.ChartRestriction.G.PullbackSections.FrameTieSt Xo c) (C : IntegralChartA3 Xo c T io y)
    (hC : FrTrunc C.I.G (𝟙 (Sp T.V)) (chD C.ch) C.xT C.eT) (k : ℕ) (F : SecN Xo (xOf y) k) (hF : Regular C k F) :
    ∃ f, GermIs C k F f := by
  letI := io.toAlgebra
  obtain ⟨σ, σt, hT1, hT2⟩ := hF
  obtain ⟨x', hx1, hx2, eL', heL'⟩ := hFT T io y C
  obtain ⟨σ', hσ'⟩ := exists_sec_id C.I.G (k : ℤ) σ (Over.mk (𝟙 (Sp T.V)))
  obtain ⟨fV, hfV⟩ := germSt_holds E H (Sp T.V) C.I.G T.V (𝟙 _) (chD C.ch) C.FT C.actT
    (Fin (chD C.ch)) C.tgT (fun j => Pi.single j (1 : T.V)) C.xT C.ph1T C.ph2T C.syT C.adT C.eT C.wPT
    C.chartT C.frameT C.primT hC k σ'
  refine ⟨fV, (isGerm_iff y.1 _ _ _ _ _ _ _ _).2
    (isGerm_of_sv ((isChart_iff y.1 _ _ _ _ _).1 C.ch.chart) C.ch.prim.1 C.ch.frame.gen fun m z J hJ => ?_)⟩
  obtain ⟨J', hJ', -⟩ := exists_good C.I.t'.PP.L C.I.t'.PP.isLB z (K := PEmpty) PEmpty.elim PEmpty.elim
    (fun a => a.elim) (fun a => a.elim)
  obtain ⟨J'', hJ'', -⟩ := exists_good C.I.G.PP.L C.I.G.PP.isLB z (K := PEmpty) PEmpty.elim PEmpty.elim
    (fun a => a.elim) (fun a => a.elim)
  let ρ : Sp (Jet T.Fr (Fin 1 × Fin (chD C.ch)) m) ⟶ Sp (Jet T.V (Fin 1 × Fin (chD C.ch)) m) :=
    spMap (jetCoef (algebraMap T.V T.Fr) (Fin 1 × Fin (chD C.ch)) m)
  let i : Sp (Jet T.Fr (Fin 1 × Fin (chD C.ch)) m) ⟶ Sp (Jet T.Fr (Fin 1 × Fin (chD C.ch)) m) := 𝟙 _
  obtain ⟨f₁, f₂⟩ := heL' m _ i z J J' J'' hJ hJ' hJ''
  have a₁ := hT1 _ (i ≫ (x' m).left) (i ≫ jetPt (C.ch.x m))
    ((Category.assoc _ _ _).trans ((congrArg (i ≫ ·) ((jetPt_snd (C.ch.x m)).trans (hx1 m).symm)).trans
      (Category.assoc _ _ _).symm))
    ((Category.assoc _ _ _).trans ((congrArg (i ≫ ·) ((jetPt_fst (C.ch.x m)).trans
      ((Over.w (x' m)).trans (Category.comp_id _)).symm)).trans (Category.assoc _ _ _).symm)) z J J' hJ hJ'
  have a₂ := hT2 _ (i ≫ (x' m).left) z J'' J' hJ'' hJ'
  have a₃ := sv_of_isGerm hfV m (i ≫ ρ) z hJ''
  have a₄ := hσ' _ ((i ≫ ρ) ≫ jetPt (C.xT m)) z J'' hJ''
  have b : ((i ≫ ρ) ≫ jetPt (C.xT m)) ≫ (snd (Over.mk (𝟙 (Sp T.V))) C.I.G.G).left =
      (i ≫ (x' m).left) ≫ C.I.m2.φ :=
    (Category.assoc _ _ _).trans ((congrArg ((i ≫ ρ) ≫ ·) (jetPt_snd (C.xT m))).trans ((Category.assoc _ _ _).trans
      ((congrArg (i ≫ ·) (hx2 m).symm).trans (Category.assoc _ _ _).symm)))
  have a₅ := (congrArg (fun q => sval σ q z J'') b).symm.trans (a₄.symm.trans a₃)
  refine (tie_alg a₁ a₂ a₅ f₁ f₂).trans (congrArg₂ (· * ·) ?_ rfl)
  rw [psJet_map]
  exact gs_spMap_toΓ _ i z _

end Chart

/- English proof (translation)
Introduce `E _ _ _ H Dw l Xo c _ hstar T io y C hC k F`. Conclude with `⟨exists_germIs (GlobalTheory.PlaceInt.frameTie_holds E H Dw l Xo c hstar) C hC k F, germIs_unique C k F, germIs_smul C k F⟩`.
-/
theorem regular_germ : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) [StarRing (𝓞 E)], (∀ a : 𝓞 E, star a = H.bar a) → ∀ (T : CDVR) (io : c.F →+* T.Fr) (y : IntFr Xo c T io) (C : IntegralChartA3 Xo c T io y), FrTrunc C.I.G (𝟙 (Sp T.V)) (chD C.ch) C.xT C.eT → ∀ (k : ℕ) (F : SecN Xo (xOf y) k), (Regular C k F → ∃ f, GermIs C k F f) ∧ (∀ f f', GermIs C k F f → GermIs C k F f' → f = f') ∧ ∀ (F' : SecN Xo (xOf y) k) (r : T.V) (f : PS T.V 1 (chD C.ch)), (∀ j, F'.f j = liftFun Xo.univ.t.G _ (T := ptO Xo (xOf y)) (toΓ T.Fr (algebraMap T.V T.Fr r)) * F.f j) → GermIs C k F f → GermIs C k F' (r • f) := by
  intro E _ _ _ H Dw l Xo c _ hstar T io y C hC k F
  exact ⟨exists_germIs (GlobalTheory.PlaceInt.frameTie_holds E H Dw l Xo c hstar) C hC k F, germIs_unique C k F, germIs_smul C k F⟩

end GlobalTheory.RegularGerm

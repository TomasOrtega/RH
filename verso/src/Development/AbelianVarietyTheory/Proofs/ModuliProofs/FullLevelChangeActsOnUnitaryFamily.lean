import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RigidSys
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Splits
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GtBaseChangeSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaUnifAV
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.TopAmpExists
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.ArcFamSt
import Development.AbelianVarietyTheory.Definitions.Degenerations.HomExtSt
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.FiniteHomogeneousInf
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.ImmersedBy
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.UTorsSt
import Development.AbelianVarietyTheory.PublishedTheorems.SemistableReduction₂.SemistableReductionSt
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.LevelMapFibreSimplyTransitive
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsReducedIsNormalSchemeIsLocallyNoetherianOfSmoo
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.CmModelCoefficientSubringDedekindCompatibleEmbed
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ObjDescendLowerLevel
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.MinimalAndDimLe
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.FullObjOfObj
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsMulEquivOfIsGrpPullback
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ObjMapIdCompCancel

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models GlobalTheory.ZM

namespace GlobalTheory.FamAut

open GlobalTheory.LevelFibre

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H}

def GeomAt (D : Datum H) (N : ℕ) {S : Scheme.{0}} (t : SAB H S) (lev : D.La → (𝟙_ (Over S) ⟶ t.G)) {k : Type} [Field k]
    (x : Sp k ⟶ S) (ρ ζ : k) : Prop :=
  DetCond D t.act x ρ ∧
    ∃ I : TateIso D k (Over.mk x ⟶ t.G) (fun a g => g ≫ t.act.act a)
        (fun m g g' c => Out.WeilIs t.G t.PP.L m g g' (unitOn c)),
      (I.ζ N : k) = ζ ∧ ∀ a, toUnit _ ≫ lev a = I.ev N a

/- English proof (translation)
Take `⟨e, he⟩` from `exists_ptEquiv m.cart x _ rfl`. Establish `hl : ∀ a, e (toUnit _ ≫ lv a) = toUnit _ ≫ lev a` using `fun a => by`. Apply `Over.OverMorphism.ext` to reduce the goal to its premises. Rewrite using `[he, unit_left, unit_left, Category.assoc, Category.assoc]`. Conclude with `congrArg _ (h a)`.

Use `and_congr (detCond_iff_of_sabMap E H D S S' t t' f ⟨m⟩ k x ρ) ⟨?_, ?_⟩` and prove the remaining obligations. Introduce and unpack `⟨I, hz, hI⟩`. Take `⟨J, h₁, h₂⟩` from `exists_tate_push m x _ rfl e he I`. Conclude with `⟨J, h₁ ▸ hz, fun a => by rw [h₂, ← hI, hl]⟩`. Introduce and unpack `⟨I, hz, hI⟩`.

Use `⟨tateTransport I e.symm (fun c p => e.injective ?_) (fun n p q c h => ?_), hz, fun a => ?_⟩` and prove the remaining obligations. Take `⟨p, rfl⟩` from `e.surjective p`. Apply `Over.OverMorphism.ext` to reduce the goal to its premises. Rewrite using `[e.apply_symm_apply, e.symm_apply_apply, he, Over.comp_left, Over.comp_left, he, Category.assoc, Category.assoc]`. Conclude with `congrArg _ (m.act c).symm`.

Take `⟨p, rfl⟩` from `e.surjective p`. Take `⟨q, rfl⟩` from `e.surjective q`. Rewrite using `[e.symm_apply_apply, e.symm_apply_apply]`. Take `⟨w, hw, -⟩` from `(isPullCubical_iff m.cm t.cub t'.cub).1 m.lin`. Conclude with `(weilIs_grpPullback_of_comm _ _ _ _ f m.φ _ _ t.PP.isLB t'.PP.isLB m.cart ⟨w, (isGen_iff w).2 hw⟩ (Over.mk x) n p q (e p) (e q) _ (he p) (he q)).2 h`.

Conclude with `e.injective ((hl a).trans ((hI a).trans (e.apply_symm_apply _).symm))`.
-/
theorem geomAt_iff {N : ℕ} {S S' : Scheme.{0}} {t : SAB H S} {t' : SAB H S'} {f : S' ⟶ S} (m : SABMap t' t f)
    {lev : D.La → (𝟙_ (Over S) ⟶ t.G)} {lv : D.La → (𝟙_ (Over S') ⟶ t'.G)}
    (h : ∀ a, (lv a).left ≫ m.φ = f ≫ (lev a).left) {k : Type} [Field k] (x : Sp k ⟶ S') (ρ ζ : k) :
    GeomAt D N t' lv x ρ ζ ↔ GeomAt D N t lev (x ≫ f) ρ ζ := by
  obtain ⟨e, he⟩ := exists_ptEquiv m.cart x _ rfl
  have hl : ∀ a, e (toUnit _ ≫ lv a) = toUnit _ ≫ lev a := fun a => by
    apply Over.OverMorphism.ext
    rw [he, unit_left, unit_left, Category.assoc, Category.assoc]
    exact congrArg _ (h a)
  refine and_congr (detCond_iff_of_sabMap E H D S S' t t' f ⟨m⟩ k x ρ) ⟨?_, ?_⟩
  · rintro ⟨I, hz, hI⟩
    obtain ⟨J, h₁, h₂⟩ := exists_tate_push m x _ rfl e he I
    exact ⟨J, h₁ ▸ hz, fun a => by rw [h₂, ← hI, hl]⟩
  · rintro ⟨I, hz, hI⟩
    refine ⟨tateTransport I e.symm (fun c p => e.injective ?_) (fun n p q c h => ?_), hz, fun a => ?_⟩
    · obtain ⟨p, rfl⟩ := e.surjective p
      apply Over.OverMorphism.ext
      rw [e.apply_symm_apply, e.symm_apply_apply, he, Over.comp_left, Over.comp_left, he, Category.assoc,
        Category.assoc]
      exact congrArg _ (m.act c).symm
    · obtain ⟨p, rfl⟩ := e.surjective p
      obtain ⟨q, rfl⟩ := e.surjective q
      rw [e.symm_apply_apply, e.symm_apply_apply]
      obtain ⟨w, hw, -⟩ := (isPullCubical_iff m.cm t.cub t'.cub).1 m.lin
      exact (weilIs_grpPullback_of_comm _ _ _ _ f m.φ _ _ t.PP.isLB t'.PP.isLB m.cart ⟨w, (isGen_iff w).2 hw⟩
        (Over.mk x) n p q (e p) (e q) _ (he p) (he q)).2 h
    · exact e.injective ((hl a).trans ((hI a).trans (e.apply_symm_apply _).symm))

/- English proof (translation)
Take `⟨b, hb⟩` from `h`. Rewrite using `[sub_eq_iff_eq_add.1 hb, hP, hk, _root_.one_mul]`.
-/
theorem eq_of_sub {L Q : Type} [AddCommGroup L] [Group Q] {N : ℕ} {P : L → Q} (hP : ∀ a c, P (a + c) = P a * P c)
    (hk : ∀ a, P (N • a) = 1) {a c : L} (h : ∃ b, a - c = N • b) : P a = P c := by
  obtain ⟨b, hb⟩ := h
  rw [sub_eq_iff_eq_add.1 hb, hP, hk, _root_.one_mul]

/- English proof (translation)
Establish `o : FullObj D (sM ≫ spMap σ.toRingHom) tM (fun x => lev (g x))`. Use `⟨F.obj.proper, F.obj.ample, F.obj.ktriv, fun x y => ?_, fun x => ?_, fun k _ _ _ x β hx => ?_⟩` and prove the remaining obligations. Rewrite using `[← F.obj.add]`. Conclude with `eq_of_sub F.obj.add F.obj.ker (hg x y)`. Take `⟨b, hb⟩` from `hg' x`.

Rewrite using `[hb, F.obj.ker]`. Take `⟨y, rfl⟩` from `hl k x`. Establish `h₁ : GeomAt D N tM lev ((y ≫ r) ≫ a) _ _` using `F.obj.geom k _ β (by`. Rewrite using `[← hx]`. Simplify using `only [Category.assoc, hr])`.

Conclude with `(geomAt_iff (lev := fun x => lev (g x)) (lv := fun x => lv (g x)) ν₀ (fun x => h₀ (g x)) y _ _).1 ((geomAt_iff ν hν y _ _).2 ((geomAt_iff ν₀ h₀ _ _ _).2 h₁))`. Use `F.flat` as an intermediate fact. Establish `: IsIso (spMap σ.toRingHom)` using `inferInstanceAs (IsIso (Spec.map σ.toCommRingCatIso.hom))`. Take `⟨ρ, ⟨h₁, ν', h₂⟩, -⟩` from `F.rep MM _ tM _ F.red inferInstance inferInstance o`. Conclude with `⟨ρ, ν', h₁, h₂⟩`.
-/
theorem exists_endo {n N : ℕ} {MM X : Scheme.{0}} [IsLocallyNoetherian MM] {sM : MM ⟶ Sp (RZ H n N)} {tM : SAB H MM}
    {lev : D.La → (𝟙_ (Over MM) ⟶ tM.G)} (F : FamCore D sM tM lev) {tX : SAB H X}
    {lv : D.La → (𝟙_ (Over X) ⟶ tX.G)} {a : X ⟶ MM} (ν₀ : SABMap tX tM a)
    (h₀ : ∀ x, (lv x).left ≫ ν₀.φ = a ≫ (lev x).left)
    (hl : ∀ (k : Type) [Field k] [IsAlgClosed k] [CharZero k] (x : Sp k ⟶ MM), ∃ y, y ≫ a = x)
    {r : X ⟶ X} (ν : SABMap tX tX r) {g : D.La → D.La} (hg : ∀ x y, ∃ b, g (x + y) - (g x + g y) = N • b)
    (hg' : ∀ x, ∃ b, g (N • x) = N • b) (hν : ∀ x, (lv (g x)).left ≫ ν.φ = r ≫ (lv x).left)
    (σ : RZ H n N ≃+* RZ H n N) (hr : r ≫ a ≫ sM = a ≫ sM ≫ spMap σ.toRingHom) :
    ∃ (ρ : MM ⟶ MM) (ν' : SABMap tM tM ρ), ρ ≫ sM = sM ≫ spMap σ.toRingHom ∧
      ∀ x, (lev (g x)).left ≫ ν'.φ = ρ ≫ (lev x).left := by
  have o : FullObj D (sM ≫ spMap σ.toRingHom) tM (fun x => lev (g x)) := by
    refine ⟨F.obj.proper, F.obj.ample, F.obj.ktriv, fun x y => ?_, fun x => ?_, fun k _ _ _ x β hx => ?_⟩
    · rw [← F.obj.add]; exact eq_of_sub F.obj.add F.obj.ker (hg x y)
    · obtain ⟨b, hb⟩ := hg' x
      rw [hb, F.obj.ker]
    · obtain ⟨y, rfl⟩ := hl k x
      have h₁ : GeomAt D N tM lev ((y ≫ r) ≫ a) _ _ := F.obj.geom k _ β (by
        rw [← hx]; simp only [Category.assoc, hr])
      exact (geomAt_iff (lev := fun x => lev (g x)) (lv := fun x => lv (g x)) ν₀ (fun x => h₀ (g x)) y _ _).1
        ((geomAt_iff ν hν y _ _).2 ((geomAt_iff ν₀ h₀ _ _ _).2 h₁))
  have := F.flat
  have : IsIso (spMap σ.toRingHom) := inferInstanceAs (IsIso (Spec.map σ.toCommRingCatIso.hom))
  obtain ⟨ρ, ⟨h₁, ν', h₂⟩, -⟩ := F.rep MM _ tM _ F.red inferInstance inferInstance o
  exact ⟨ρ, ν', h₁, h₂⟩

/- English proof (translation)
Take `⟨m, hm⟩` from `sabComp pullCubComp E H _ _ _ _ _ _ _ _ ν' ν`. Use `(F.rep MM sM tM lev F.red inferInstance F.flat F.obj).unique ⟨by rw [Category.assoc, hs], m, fun x => ?_⟩ ⟨Category.id_comp _, ObjComp.sabMapId tM, fun x => (Category.comp_id _).trans (Category.id_comp _).symm⟩` and prove the remaining obligations. Rewrite using `[hm]`. Use `conv_lhs => rw [← eq_of_sub F.obj.add F.obj.ker (hg x)]`. Conclude with `ObjComp.sec_comp (h' x) (h (g' x))`.
-/
theorem eq_id {n N : ℕ} {MM : Scheme.{0}} [IsLocallyNoetherian MM] {sM : MM ⟶ Sp (RZ H n N)} {tM : SAB H MM}
    {lev : D.La → (𝟙_ (Over MM) ⟶ tM.G)} (F : FamCore D sM tM lev) {ρ ρ' : MM ⟶ MM} (ν : SABMap tM tM ρ)
    (ν' : SABMap tM tM ρ') {g g' : D.La → D.La} (h : ∀ x, (lev (g x)).left ≫ ν.φ = ρ ≫ (lev x).left)
    (h' : ∀ x, (lev (g' x)).left ≫ ν'.φ = ρ' ≫ (lev x).left) (hg : ∀ x, ∃ b, g (g' x) - x = N • b)
    (hs : ρ ≫ ρ' ≫ sM = sM) : ρ ≫ ρ' = 𝟙 MM := by
  obtain ⟨m, hm⟩ := sabComp pullCubComp E H _ _ _ _ _ _ _ _ ν' ν
  refine (F.rep MM sM tM lev F.red inferInstance F.flat F.obj).unique ⟨by rw [Category.assoc, hs], m, fun x => ?_⟩
    ⟨Category.id_comp _, ObjComp.sabMapId tM, fun x => (Category.comp_id _).trans (Category.id_comp _).symm⟩
  rw [hm]
  conv_lhs => rw [← eq_of_sub F.obj.add F.obj.ker (hg x)]
  exact ObjComp.sec_comp (h' x) (h (g' x))

/- English proof (translation)
Establish `hs : ∀ x, ∃ y, J.ev N y = I.ev N x` using `fun x => (J.onto N hN _).1 ((I.onto N hN _).2 ⟨x, rfl⟩)`. Use `choose g' hg' using hs`. Establish `hJ : ∀ {x y}, J.ev N x = J.ev N y → ∃ b, x - y = N • b` using `fun hxy => (J.ker N hN _).1 (sub_eq_one _ (J.add N) hxy)`. Use `⟨g', fun x y => hJ ?_, fun x => (J.ker N hN _).1 ?_, fun x => (I.ker N hN _).1 (sub_eq_one _ (I.add N) ?_), fun x => hJ ?_⟩` and prove the remaining obligations. Rewrite using `[J.add, hg', hg', hg', I.add]`.

Rewrite using `[hg']`. Conclude with `(I.ker N hN _).2 ⟨x, rfl⟩`. Rewrite using `[h, hg']`. Rewrite using `[hg', h]`.
-/
theorem exists_inv_mod {k : Type} [Field k] {Q : Type} [Group Q] {act : 𝓞 E → Q → Q} {e : ℕ → Q → Q → kˣ → Prop}
    (I J : TateIso D k Q act e) {N : ℕ} (hN : 0 < N) (g : D.La →+ D.La) (h : ∀ x, I.ev N (g x) = J.ev N x) :
    ∃ g' : D.La → D.La, (∀ x y, ∃ b, g' (x + y) - (g' x + g' y) = N • b) ∧ (∀ x, ∃ b, g' (N • x) = N • b) ∧
      (∀ x, ∃ b, g (g' x) - x = N • b) ∧ ∀ x, ∃ b, g' (g x) - x = N • b := by
  have hs : ∀ x, ∃ y, J.ev N y = I.ev N x := fun x => (J.onto N hN _).1 ((I.onto N hN _).2 ⟨x, rfl⟩)
  choose g' hg' using hs
  have hJ : ∀ {x y}, J.ev N x = J.ev N y → ∃ b, x - y = N • b := fun hxy =>
    (J.ker N hN _).1 (sub_eq_one _ (J.add N) hxy)
  refine ⟨g', fun x y => hJ ?_, fun x => (J.ker N hN _).1 ?_,
    fun x => (I.ker N hN _).1 (sub_eq_one _ (I.add N) ?_), fun x => hJ ?_⟩
  · rw [J.add, hg', hg', hg', I.add]
  · rw [hg']; exact (I.ker N hN _).2 ⟨x, rfl⟩
  · rw [h, hg']
  · rw [hg', h]

/- English proof (translation)
Establish `key : RZ H n l.A ≤ ((RZ H n l.A).comap ((KA l).val.toRingHom.comp σ)).map (KA l).val.toRingHom`. Establish `h2 : ((2 : KA l) : ℂ) = 2` using `map_ofNat (KA l).val 2`. Establish `hw : (((1 + (baseKA l).ρ) / 2 : KA l) : ℂ) = (1 + H.rt0) / 2` using `by simp [baseKA, h2]`. Use `Subring.closure_le.2 ?_` and prove the remaining obligations. Introduce and unpack `x (rfl | rfl | rfl)`.

Use `⟨(1 + (baseKA l).ρ) / 2, ?_, hw⟩` and prove the remaining obligations. Establish `: σ ((1 + (baseKA l).ρ) / 2) = (1 + (baseKA l).ρ) / 2`. Rewrite using `[map_div₀, map_add, map_one, hσ, map_ofNat]`. Express the relevant statement in the definitionally equal form `((σ _ : KA l) : ℂ) ∈ RZ H n l.A`. Rewrite using `[this]`.

Conclude with `Subring.subset_closure (Or.inl hw)`. Use `⟨(n : KA l)⁻¹, ?_, by simp⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `((σ _ : KA l) : ℂ) ∈ RZ H n l.A`. Rewrite using `[map_inv₀, map_natCast]`. Conclude with `Subring.subset_closure (Or.inr (Or.inl (by simp)))`.

Use `⟨(baseKA l).ζ, ?_, rfl⟩` and prove the remaining obligations. Establish `: NeZero l.A` using `⟨l.A_pos.ne'⟩`. Take `⟨i, -, hi⟩` from `(baseKA l).ζ_prim.eq_pow_of_pow_eq_one (ξ := σ (baseKA l).ζ) (by rw [← map_pow, (baseKA l).ζ_prim.pow_eq_one, map_one])`. Express the relevant statement in the definitionally equal form `((σ _ : KA l) : ℂ) ∈ RZ H n l.A`. Rewrite using `[← hi]`.

Conclude with `pow_mem (x := zeta l.A) (Subring.subset_closure (Or.inr (Or.inr rfl))) i`. Establish `hm : ∀ x : RZ H n l.A, ((KA l).val.toRingHom.comp (σ.comp β)) x ∈ RZ H n l.A` using `fun x => by`. Take `⟨y, hy, e⟩` from `key x.2`. Establish `: y = β x` using `Subtype.ext (e.trans (hβ x).symm)`. Substitute `this` using the available equality.

Conclude with `hy`. Conclude with `⟨((KA l).val.toRingHom.comp (σ.comp β)).codRestrict _ hm, RingHom.ext fun x => Subtype.ext (hβ _)⟩`.
-/
theorem exists_restrict (l : Level H) (n : ℕ) (β : RZ H n l.A →+* KA l)
    (hβ : IsInc (RZ H n l.A).subtype (KA l).val.toRingHom β) (σ : KA l →+* KA l)
    (hσ : σ (baseKA l).ρ = (baseKA l).ρ) : ∃ τ : RZ H n l.A →+* RZ H n l.A, β.comp τ = σ.comp β := by
  have key : RZ H n l.A ≤ ((RZ H n l.A).comap ((KA l).val.toRingHom.comp σ)).map (KA l).val.toRingHom := by
    have h2 : ((2 : KA l) : ℂ) = 2 := map_ofNat (KA l).val 2
    have hw : (((1 + (baseKA l).ρ) / 2 : KA l) : ℂ) = (1 + H.rt0) / 2 := by simp [baseKA, h2]
    refine Subring.closure_le.2 ?_
    rintro x (rfl | rfl | rfl)
    · refine ⟨(1 + (baseKA l).ρ) / 2, ?_, hw⟩
      have : σ ((1 + (baseKA l).ρ) / 2) = (1 + (baseKA l).ρ) / 2 := by
        rw [map_div₀, map_add, map_one, hσ, map_ofNat]
      change ((σ _ : KA l) : ℂ) ∈ RZ H n l.A
      rw [this]
      exact Subring.subset_closure (Or.inl hw)
    · refine ⟨(n : KA l)⁻¹, ?_, by simp⟩
      change ((σ _ : KA l) : ℂ) ∈ RZ H n l.A
      rw [map_inv₀, map_natCast]
      exact Subring.subset_closure (Or.inr (Or.inl (by simp)))
    · refine ⟨(baseKA l).ζ, ?_, rfl⟩
      have : NeZero l.A := ⟨l.A_pos.ne'⟩
      obtain ⟨i, -, hi⟩ := (baseKA l).ζ_prim.eq_pow_of_pow_eq_one (ξ := σ (baseKA l).ζ)
        (by rw [← map_pow, (baseKA l).ζ_prim.pow_eq_one, map_one])
      change ((σ _ : KA l) : ℂ) ∈ RZ H n l.A
      rw [← hi]
      exact pow_mem (x := zeta l.A) (Subring.subset_closure (Or.inr (Or.inr rfl))) i
  have hm : ∀ x : RZ H n l.A, ((KA l).val.toRingHom.comp (σ.comp β)) x ∈ RZ H n l.A := fun x => by
    obtain ⟨y, hy, e⟩ := key x.2
    have : y = β x := Subtype.ext (e.trans (hβ x).symm)
    subst this
    exact hy
  exact ⟨((KA l).val.toRingHom.comp (σ.comp β)).codRestrict _ hm, RingHom.ext fun x => Subtype.ext (hβ _)⟩

/- English proof (translation)
Use `letI := β.toAlgebra`. Use `hd.2.2` as an intermediate fact. Use `BaseRing.finiteDimensional_KA l` as an intermediate fact. Establish `hinj : Function.Injective δ`. Rewrite using `[injective_iff_map_eq_zero]`.

Introduce `z hz`. Assume the negation of the conclusion as `h0`. Establish `ha : IsAlgebraic ℤ z`. Establish `h₁ : IsAlgebraic ℤ (β z)` using `(IsFractionRing.isAlgebraic_iff ℤ ℚ (KA l)).2 (Algebra.IsAlgebraic.isAlgebraic _)`. Conclude with `(isAlgebraic_algHom_iff β.toIntAlgHom (IsFractionRing.injective (RZ H n l.A) (KA l))).1 h₁`.

Use `Ideal.comap_ne_bot_of_algebraic_mem (I := RingHom.ker δ) h0 hz ha ?_` and prove the remaining obligations. Use `(Submodule.eq_bot_iff _).2 fun m hm => ?_` and prove the remaining obligations. Simplify using `using hm`. Conclude with `⟨IsFractionRing.lift hinj, RingHom.ext fun x => IsFractionRing.lift_algebraMap hinj x⟩`.
-/
theorem exists_extend (l : Level H) (n : ℕ) (β : RZ H n l.A →+* KA l)
    (hβ : IsInc (RZ H n l.A).subtype (KA l).val.toRingHom β) (hd : IsDedFrac β) {k : Type} [Field k] [CharZero k]
    (δ : RZ H n l.A →+* k) : ∃ gam : KA l →+* k, gam.comp β = δ := by
  letI := β.toAlgebra
  have := hd.2.2
  have := BaseRing.finiteDimensional_KA l
  have hinj : Function.Injective δ := by
    rw [injective_iff_map_eq_zero]
    intro z hz
    by_contra h0
    have ha : IsAlgebraic ℤ z := by
      have h₁ : IsAlgebraic ℤ (β z) :=
        (IsFractionRing.isAlgebraic_iff ℤ ℚ (KA l)).2 (Algebra.IsAlgebraic.isAlgebraic _)
      exact (isAlgebraic_algHom_iff β.toIntAlgHom (IsFractionRing.injective (RZ H n l.A) (KA l))).1 h₁
    refine Ideal.comap_ne_bot_of_algebraic_mem (I := RingHom.ker δ) h0 hz ha ?_
    refine (Submodule.eq_bot_iff _).2 fun m hm => ?_
    simpa using hm
  exact ⟨IsFractionRing.lift hinj, RingHom.ext fun x => IsFractionRing.lift_algebraMap hinj x⟩

end GlobalTheory.FamAut

open GlobalTheory.FamAut GlobalTheory.LevelFibre in

/- English proof (translation)
Introduce and unpack `- - E _ _ _ H D n N MM sM tM lev l Xo β a ν₀ h r ν g σ - rfl hn - ⟨j, -, hj⟩ hβ F hsurj h₀ hσ hr hν`. Break down `isEmpty_or_nonempty Xo.X with hX | ⟨⟨p⟩⟩` into its components or cases. Conclude with `⟨Iso.refl _, ObjComp.sabMapId tM, RingEquiv.refl _, (isInitialOfIsEmpty (X := Xo.X)).hom_ext _ _, (Category.id_comp _).trans (by rw [show spMap (RingEquiv.refl (RZ H n l.A)).toRingHom = 𝟙 _ from Spec.map_id _, Category.comp_id]), rfl⟩`. Establish `hd` using `(BaseRing.isDedFrac_RZ E H l n j hn.pos hj.dvd).2.2 β hβ`. Establish `hinj : Function.Injective β` using `fun x y e => Subtype.ext ((hβ x).symm.trans ((congrArg Subtype.val e).trans (hβ y)))`.

Use `BaseRing.isDedekindDomain_RZ l hn.pos hj.dvd` as an intermediate fact. Use `FullLevel.lft_of_qproj F.qproj` as an intermediate fact. Establish `: IsLocallyNoetherian MM` using `LocallyOfFiniteType.isLocallyNoetherian sM`. Establish `hsm` using `Xo.smooth`. Establish `hsm' : Smooth Xo.s` using `SmoothOfRelativeDimension.smooth D.dim _`.

Take `⟨hred, -, hnoe⟩` from `isReduced_isNormalScheme_isLocallyNoetherian_of_smooth_over_field _ _ Xo.s hsm'`. Take `⟨τ, hτ⟩` from `exists_restrict l n β hβ σ.toRingHom hσ`. Take `⟨τ', hτ'⟩` from `exists_restrict l n β hβ σ.symm.toRingHom (σ.symm_apply_eq.2 hσ.symm)`. Establish `hτx : ∀ x, β (τ x) = σ (β x)` using `fun x => RingHom.congr_fun hτ x`. Establish `hτx' : ∀ x, β (τ' x) = σ.symm (β x)` using `fun x => RingHom.congr_fun hτ' x`.

Set `σ₀ : RZ H n l.A ≃+* RZ H n l.A` to `RingEquiv.ofRingHom τ τ' (RingHom.ext fun x => hinj (by simp [hτx, hτx'])) (RingHom.ext fun x => hinj (by simp [hτx, hτx']))`. Establish `hσ₀ : β.comp σ₀.toRingHom = σ.toRingHom.comp β` using `hτ`. Establish `hra : r.hom ≫ a ≫ sM = a ≫ sM ≫ spMap σ₀.toRingHom`. Rewrite using `[← Category.assoc a, h, reassoc_of% hr, Category.assoc, ← spMap_comp, ← spMap_comp, hσ₀]`. Establish `hss : spMap σ₀.toRingHom ≫ spMap σ₀.symm.toRingHom = 𝟙 _`.

Rewrite using `[← spMap_comp, RingEquiv.toRingHom_comp_symm_toRingHom, spMap_id']`. Establish `hss' : spMap σ₀.symm.toRingHom ≫ spMap σ₀.toRingHom = 𝟙 _`. Rewrite using `[← spMap_comp, RingEquiv.symm_toRingHom_comp_toRingHom, spMap_id']`. Establish `hra' : r.inv ≫ a ≫ sM = a ≫ sM ≫ spMap σ₀.symm.toRingHom`. Rewrite using `[Iso.inv_comp_eq, reassoc_of% hra, hss, Category.comp_id]`.

Establish `hl : ∀ (k : Type) [Field k] [IsAlgClosed k] [CharZero k] (x : Sp k ⟶ MM), ∃ y, y ≫ a = x`. Introduce `k _ _ _ x`. Take `⟨δ, hδ⟩` from `exists_spMap (x ≫ sM)`. Take `⟨gam, rfl⟩` from `exists_extend l n β hβ hd δ`. Establish `: LocallyOfFiniteType (pullback.lift a _ h ≫ pullback.snd _ _)`.

Rewrite using `[pullback.lift_snd]`. Use `infer_instance`. Use `locallyOfFiniteType_of_comp (pullback.lift a _ h) (pullback.snd _ _)` as an intermediate fact. Take `⟨y, hy⟩` from `ObjDesc.exists_geomPt_lift (pullback.lift a _ h) k (pullback.lift x (spMap gam) (hδ.trans (spMap_comp _ _)))`. Use `⟨y, ?_⟩` and prove the remaining obligations.

Use `hy =≫ pullback.fst _ _` as an intermediate fact. Rewrite `this` using `[Category.assoc, pullback.lift_fst, pullback.lift_fst]`. Then use the resulting hypothesis. Establish `o₁` using `fullObj_of_obj Xo.s Xo.univ β hβ`. Establish `o₂ : FullObj D (r.hom ≫ a ≫ sM) Xo.univ.t (fun x => Xo.univ.etaA (g x))`. Use `⟨o₁.proper, o₁.ample, o₁.ktriv, fun x y => by rw [map_add, o₁.add], fun x => by rw [map_nsmul, o₁.ker], fun k _ _ _ x δ hx => ?_⟩` and prove the remaining obligations.

Conclude with `(geomAt_iff ν hν x _ _).2 (o₁.geom k _ δ (by rw [← hx, ← h, Category.assoc]))`. Set `k` to `AlgebraicClosure (Xo.X.residueField p)`. Set `y : Sp k ⟶ Xo.X` to `spMap (algebraMap (Xo.X.residueField p) k) ≫ Xo.X.fromSpecResidueField p`. Take `⟨gam, -⟩` from `exists_spMap (y ≫ Xo.s)`. Establish `: CharZero k` using `(RingHom.charZero_iff gam.injective).1 inferInstance`.

Take `⟨δ₁, e₁⟩` from `exists_spMap (y ≫ Xo.s ≫ spMap β)`. Take `⟨δ₂, e₂⟩` from `exists_spMap (y ≫ r.hom ≫ a ≫ sM)`. Take `⟨-, I, -, hI⟩` from `o₁.geom k y δ₁ e₁`. Take `⟨-, J, -, hJ⟩` from `o₂.geom k y δ₂ e₂`. Take `⟨g', ga, gk, gr, gl⟩` from `exists_inv_mod I J l.A_pos g.toAddMonoidHom fun x => (hI _).symm.trans (hJ x)`.

Take `⟨i, hi⟩` from `sab_cast r.inv_hom_id.symm (ObjComp.sabMapId Xo.univ.t)`. Take `⟨mu, hmu⟩` from `sabCancel pullCubCancel E H _ _ _ _ _ _ r.hom r.inv ν i`. Establish `hmu' : mu.φ ≫ ν.φ = 𝟙 _` using `hmu.symm.trans hi`. Establish `hmul : ∀ x, (Xo.univ.etaA (g' x)).left ≫ mu.φ = r.inv ≫ (Xo.univ.etaA x).left` using `fun x => by`. Use `ObjComp.sec_cancel ν.cart.1 mu.cart.1.w (Over.w _) (Over.w _) (((congrArg (fun q => q.left ≫ ν.φ) (eq_of_sub o₁.add o₁.ker (gr x))).symm.trans (hν (g' x)))) ?_` and prove the remaining obligations.

Rewrite using `[r.inv_hom_id]`. Conclude with `(congrArg _ hmu').trans ((Category.comp_id _).trans (Category.id_comp _).symm)`. Take `⟨ρ, ν₁, hρ, hν₁⟩` from `exists_endo F ν₀ h₀ hl ν (g := g) (fun x y => ⟨0, by simp⟩) (fun x => ⟨g x, map_nsmul _ _ _⟩) hν σ₀ hra`. Take `⟨ρ', ν₂, hρ', hν₂⟩` from `exists_endo F ν₀ h₀ hl mu ga gk hmul σ₀.symm hra'`. Use `⟨⟨ρ, ρ', eq_id F ν₁ ν₂ hν₁ hν₂ gr ?_, eq_id F ν₂ ν₁ hν₂ hν₁ gl ?_⟩, ν₁, σ₀, ?_, hρ, hinj ?_⟩` and prove the remaining obligations.

Rewrite using `[hρ', reassoc_of% hρ, hss, Category.comp_id]`. Rewrite using `[hρ, reassoc_of% hρ', hss', Category.comp_id]`. Establish `hf : Flat (spMap β)`. Use `letI := β.toAlgebra`. Use `hd.2.2` as an intermediate fact.

Conclude with `Flat.SpecMap_iff.2 (RingHom.flat_algebraMap_iff.2 (IsLocalization.flat (KA l) (nonZeroDivisors (RZ H n l.A))))`. Establish `hfl : Flat (r.hom ≫ a ≫ sM)` using `by rw [h]; infer_instance`. Take `⟨m₁, hm₁⟩` from `sabComp pullCubComp E H _ _ _ _ _ _ _ _ ν₁ ν₀`. Take `⟨m₂, hm₂⟩` from `sabComp pullCubComp E H _ _ _ _ _ _ _ _ ν₀ ν`. Use `(F.rep _ _ _ _ hred hnoe hfl o₂).unique ⟨?_, m₁, fun x => ?_⟩ ⟨Category.assoc _ _ _, m₂, fun x => ?_⟩` and prove the remaining obligations.

Rewrite using `[hra, Category.assoc, hρ]`. Rewrite using `[hm₁]`. Conclude with `ObjComp.sec_comp (hν₁ x) (h₀ (g x))`. Rewrite using `[hm₂]`. Conclude with `ObjComp.sec_comp (h₀ x) (hν x)`.

Establish `hρt : β (RZ.rt H n l.A) = (baseKA l).ρ` using `Subtype.ext ((hβ _).trans (RZ.rt_coe _ _))`. Conclude with `(hτx _).trans (by rw [hρt, hσ])`.
-/
theorem GlobalTheory.famCore_exists_aut : Out.Laws → Out.Laws2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (n N : ℕ) (MM : Scheme.{0}) (sM : MM ⟶ Sp (RZ H n N)) (tM : SAB H MM) (lev : D.La → (𝟙_ (Over MM) ⟶ tM.G)) (l : Level H) (Xo : Moduli D l) (β : RZ H n N →+* KA l) (a : Xo.X ⟶ MM) (ν₀ : SABMap Xo.univ.t tM a) (h : a ≫ sM = Xo.s ≫ spMap β) (r : Xo.X ≅ Xo.X) (ν : SABMap Xo.univ.t Xo.univ.t r.hom) (g : D.La →ₗ[𝓞 E] D.La) (σ : KA l ≃+* KA l), 1 ≤ D.p + D.q → l.A = N → n.Prime → Odd n → (∃ j, 1 ≤ j ∧ N = n ^ j) → IsInc (RZ H n N).subtype (KA l).val.toRingHom β → FamCore D sM tM lev → Surjective (pullback.lift a _ h) → (∀ x, (Xo.univ.etaA x).left ≫ ν₀.φ = a ≫ (lev x).left) → σ (baseKA l).ρ = (baseKA l).ρ → r.hom ≫ Xo.s = Xo.s ≫ spMap σ.toRingHom → (∀ x, (Xo.univ.etaA (g x)).left ≫ ν.φ = r.hom ≫ (Xo.univ.etaA x).left) → ∃ (ρ : MM ≅ MM) (_ : SABMap tM tM ρ.hom) (σ₀ : RZ H n N ≃+* RZ H n N), a ≫ ρ.hom = r.hom ≫ a ∧ ρ.hom ≫ sM = sM ≫ spMap σ₀.toRingHom ∧ σ₀ (RZ.rt H n N) = RZ.rt H n N := by
  rintro - - E _ _ _ H D n N MM sM tM lev l Xo β a ν₀ h r ν g σ - rfl hn - ⟨j, -, hj⟩ hβ F hsurj h₀ hσ hr hν
  rcases isEmpty_or_nonempty Xo.X with hX | ⟨⟨p⟩⟩
  · exact ⟨Iso.refl _, ObjComp.sabMapId tM, RingEquiv.refl _, (isInitialOfIsEmpty (X := Xo.X)).hom_ext _ _,
      (Category.id_comp _).trans (by rw [show spMap (RingEquiv.refl (RZ H n l.A)).toRingHom = 𝟙 _ from Spec.map_id _,
        Category.comp_id]), rfl⟩
  have hd := (BaseRing.isDedFrac_RZ E H l n j hn.pos hj.dvd).2.2 β hβ
  have hinj : Function.Injective β := fun x y e => Subtype.ext ((hβ x).symm.trans ((congrArg Subtype.val e).trans (hβ y)))
  have := BaseRing.isDedekindDomain_RZ l hn.pos hj.dvd
  have := FullLevel.lft_of_qproj F.qproj
  have : IsLocallyNoetherian MM := LocallyOfFiniteType.isLocallyNoetherian sM
  have hsm := Xo.smooth
  have hsm' : Smooth Xo.s := SmoothOfRelativeDimension.smooth D.dim _
  obtain ⟨hred, -, hnoe⟩ := isReduced_isNormalScheme_isLocallyNoetherian_of_smooth_over_field _ _ Xo.s hsm'

  obtain ⟨τ, hτ⟩ := exists_restrict l n β hβ σ.toRingHom hσ
  obtain ⟨τ', hτ'⟩ := exists_restrict l n β hβ σ.symm.toRingHom (σ.symm_apply_eq.2 hσ.symm)
  have hτx : ∀ x, β (τ x) = σ (β x) := fun x => RingHom.congr_fun hτ x
  have hτx' : ∀ x, β (τ' x) = σ.symm (β x) := fun x => RingHom.congr_fun hτ' x
  let σ₀ : RZ H n l.A ≃+* RZ H n l.A := RingEquiv.ofRingHom τ τ'
    (RingHom.ext fun x => hinj (by simp [hτx, hτx'])) (RingHom.ext fun x => hinj (by simp [hτx, hτx']))
  have hσ₀ : β.comp σ₀.toRingHom = σ.toRingHom.comp β := hτ
  have hra : r.hom ≫ a ≫ sM = a ≫ sM ≫ spMap σ₀.toRingHom := by
    rw [← Category.assoc a, h, reassoc_of% hr, Category.assoc, ← spMap_comp, ← spMap_comp, hσ₀]
  have hss : spMap σ₀.toRingHom ≫ spMap σ₀.symm.toRingHom = 𝟙 _ := by
    rw [← spMap_comp, RingEquiv.toRingHom_comp_symm_toRingHom, spMap_id']
  have hss' : spMap σ₀.symm.toRingHom ≫ spMap σ₀.toRingHom = 𝟙 _ := by
    rw [← spMap_comp, RingEquiv.symm_toRingHom_comp_toRingHom, spMap_id']
  have hra' : r.inv ≫ a ≫ sM = a ≫ sM ≫ spMap σ₀.symm.toRingHom := by
    rw [Iso.inv_comp_eq, reassoc_of% hra, hss, Category.comp_id]

  have hl : ∀ (k : Type) [Field k] [IsAlgClosed k] [CharZero k] (x : Sp k ⟶ MM), ∃ y, y ≫ a = x := by
    intro k _ _ _ x
    obtain ⟨δ, hδ⟩ := exists_spMap (x ≫ sM)
    obtain ⟨gam, rfl⟩ := exists_extend l n β hβ hd δ
    have : LocallyOfFiniteType (pullback.lift a _ h ≫ pullback.snd _ _) := by
      rw [pullback.lift_snd]; infer_instance
    have := locallyOfFiniteType_of_comp (pullback.lift a _ h) (pullback.snd _ _)
    obtain ⟨y, hy⟩ := ObjDesc.exists_geomPt_lift (pullback.lift a _ h) k
      (pullback.lift x (spMap gam) (hδ.trans (spMap_comp _ _)))
    refine ⟨y, ?_⟩
    have := hy =≫ pullback.fst _ _
    rwa [Category.assoc, pullback.lift_fst, pullback.lift_fst] at this

  have o₁ := fullObj_of_obj Xo.s Xo.univ β hβ
  have o₂ : FullObj D (r.hom ≫ a ≫ sM) Xo.univ.t (fun x => Xo.univ.etaA (g x)) := by
    refine ⟨o₁.proper, o₁.ample, o₁.ktriv, fun x y => by rw [map_add, o₁.add], fun x => by rw [map_nsmul, o₁.ker],
      fun k _ _ _ x δ hx => ?_⟩
    exact (geomAt_iff ν hν x _ _).2 (o₁.geom k _ δ (by rw [← hx, ← h, Category.assoc]))

  let k := AlgebraicClosure (Xo.X.residueField p)
  let y : Sp k ⟶ Xo.X := spMap (algebraMap (Xo.X.residueField p) k) ≫ Xo.X.fromSpecResidueField p
  obtain ⟨gam, -⟩ := exists_spMap (y ≫ Xo.s)
  have : CharZero k := (RingHom.charZero_iff gam.injective).1 inferInstance
  obtain ⟨δ₁, e₁⟩ := exists_spMap (y ≫ Xo.s ≫ spMap β)
  obtain ⟨δ₂, e₂⟩ := exists_spMap (y ≫ r.hom ≫ a ≫ sM)
  obtain ⟨-, I, -, hI⟩ := o₁.geom k y δ₁ e₁
  obtain ⟨-, J, -, hJ⟩ := o₂.geom k y δ₂ e₂
  obtain ⟨g', ga, gk, gr, gl⟩ := exists_inv_mod I J l.A_pos g.toAddMonoidHom fun x => (hI _).symm.trans (hJ x)
  obtain ⟨i, hi⟩ := sab_cast r.inv_hom_id.symm (ObjComp.sabMapId Xo.univ.t)
  obtain ⟨mu, hmu⟩ := sabCancel pullCubCancel E H _ _ _ _ _ _ r.hom r.inv ν i
  have hmu' : mu.φ ≫ ν.φ = 𝟙 _ := hmu.symm.trans hi
  have hmul : ∀ x, (Xo.univ.etaA (g' x)).left ≫ mu.φ = r.inv ≫ (Xo.univ.etaA x).left := fun x => by
    refine ObjComp.sec_cancel ν.cart.1 mu.cart.1.w (Over.w _) (Over.w _)
      (((congrArg (fun q => q.left ≫ ν.φ) (eq_of_sub o₁.add o₁.ker (gr x))).symm.trans (hν (g' x)))) ?_
    rw [r.inv_hom_id]
    exact (congrArg _ hmu').trans ((Category.comp_id _).trans (Category.id_comp _).symm)
  obtain ⟨ρ, ν₁, hρ, hν₁⟩ := exists_endo F ν₀ h₀ hl ν (g := g) (fun x y => ⟨0, by simp⟩)
    (fun x => ⟨g x, map_nsmul _ _ _⟩) hν σ₀ hra
  obtain ⟨ρ', ν₂, hρ', hν₂⟩ := exists_endo F ν₀ h₀ hl mu ga gk hmul σ₀.symm hra'
  refine ⟨⟨ρ, ρ', eq_id F ν₁ ν₂ hν₁ hν₂ gr ?_, eq_id F ν₂ ν₁ hν₂ hν₁ gl ?_⟩, ν₁, σ₀, ?_, hρ, hinj ?_⟩
  · rw [hρ', reassoc_of% hρ, hss, Category.comp_id]
  · rw [hρ, reassoc_of% hρ', hss', Category.comp_id]
  · have hf : Flat (spMap β) := by
      letI := β.toAlgebra
      have := hd.2.2
      exact Flat.SpecMap_iff.2 (RingHom.flat_algebraMap_iff.2 (IsLocalization.flat (KA l) (nonZeroDivisors (RZ H n l.A))))
    have hfl : Flat (r.hom ≫ a ≫ sM) := by rw [h]; infer_instance
    obtain ⟨m₁, hm₁⟩ := sabComp pullCubComp E H _ _ _ _ _ _ _ _ ν₁ ν₀
    obtain ⟨m₂, hm₂⟩ := sabComp pullCubComp E H _ _ _ _ _ _ _ _ ν₀ ν
    refine (F.rep _ _ _ _ hred hnoe hfl o₂).unique ⟨?_, m₁, fun x => ?_⟩ ⟨Category.assoc _ _ _, m₂, fun x => ?_⟩
    · rw [hra, Category.assoc, hρ]
    · rw [hm₁]; exact ObjComp.sec_comp (hν₁ x) (h₀ (g x))
    · rw [hm₂]; exact ObjComp.sec_comp (h₀ x) (hν x)
  · have hρt : β (RZ.rt H n l.A) = (baseKA l).ρ := Subtype.ext ((hβ _).trans (RZ.rt_coe _ _))
    exact (hτx _).trans (by rw [hρt, hσ])

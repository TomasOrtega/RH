import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.DivisorSupportCondition
import Development.AbelianVarietyTheory.Definitions.Divisors.SecClass
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEtaleCocycleFirstChernClassTateTwist
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleSheafComplexQuasiIsoIffSections
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChosenInjectiveResolutionEtaleSheafPropertiesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChosenInjectiveResolutionEtaleSheafSectionsExactStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TateTwistSectionsLocallyGeneratedStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleLocalPropertyCalculusRulesStatement

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace GlobalTheory.EtC.SuppRes

open ClsSpec

variable {R : Type} [CommRing R]

/- English proof (translation)
The claim follows from `GlobalTheory.T.etaleLocal_property_calculus_rules.1 U P h`.
-/
theorem loc_all {U : Scheme.{0}} {P : ∀ V : Scheme.{0}, (V ⟶ U) → Prop} (h : ∀ V g, P V g) : Loc U P :=
  GlobalTheory.T.etaleLocal_property_calculus_rules.1 U P h

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex in
variable {R : Type} [CommRing R] in
/- English proof (translation)
Use extensionality with `U a`. Conclude with `h U.unop a`.
-/
private theorem shv_hom_ext_of_sec_map_eq {S : Type} [CommRing S] {F G : _root_.GlobalTheory.EtC.Shv S}
    (φ ψ : F ⟶ G)
    (h : ∀ U (a : _root_.GlobalTheory.EtC.Sec F U),
      _root_.GlobalTheory.EtC.Sec.map φ a = _root_.GlobalTheory.EtC.Sec.map ψ a) : φ = ψ := by
  ext U a
  exact h U.unop a

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex in
variable {R : Type} [CommRing R] in
/- English proof (translation)
Simplify using `[_root_.GlobalTheory.EtC.Sec.map]`.
-/
private theorem sec_map_zero_apply {S : Type} [CommRing S] {F G : _root_.GlobalTheory.EtC.Shv S}
    {U : Scheme} (a : _root_.GlobalTheory.EtC.Sec F U) :
    _root_.GlobalTheory.EtC.Sec.map (0 : F ⟶ G) a = 0 := by
  simp [_root_.GlobalTheory.EtC.Sec.map]

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex in
variable {R : Type} [CommRing R] in
/- English proof (translation)
Assemble the required witnesses or components as `⟨⊤, GrothendieckTopology.top_mem _ _, fun V g _ => h V g⟩`.
-/
private theorem etLoc_of_forall {U : Scheme} {P : (V : Scheme) → (V ⟶ U) → Prop}
    (h : ∀ V g, P V g) : _root_.GlobalTheory.EtC.Loc U P :=
  ⟨⊤, GrothendieckTopology.top_mem _ _, fun V g _ => h V g⟩

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex in
variable {R : Type} [CommRing R] in

/- English proof (translation)
Introduce `q _ i D ι hinj himg`. Use `haveI hmono : ∀ n, Mono (ι.f n) := fun n => (_root_.GlobalTheory.EtC.mono_epi_sections (ZMod q) (ι.f n)).1.2 (fun U => hinj n U)`. Take `⟨-, -, hIge, -, hterm, hAmono, hAd, -⟩` from `_root_.GlobalTheory.EtC.ResBasic.res_basic (ZMod q) (_root_.GlobalTheory.EtC.tw q i)`. Use `haveI := hIge`. Use `haveI := hAmono`.

Establish `hA : _root_.GlobalTheory.EtC.resι (ZMod q) (_root_.GlobalTheory.EtC.tw q i) ≫ cokernel.π (ι.f 0) = 0`. Apply `shv_hom_ext_of_sec_map_eq` to reduce the goal to its premises. Introduce `U y`. Rewrite using `[sec_map_zero_apply, ← _root_.GlobalTheory.EtC.ClsSpec.map_comp]`. Take `⟨b, hb⟩` from `(himg 0 U (_root_.GlobalTheory.EtC.Sec.map (_root_.GlobalTheory.EtC.resι (ZMod q) (_root_.GlobalTheory.EtC.tw q i)) y)).2 (by`.

Use `_root_.GlobalTheory.EtC.ClsSpec.loc_mono ((_root_.GlobalTheory.EtC.twist_sections q i).1 U y) ?_` and prove the remaining obligations. Introduce and unpack `V g (h | ⟨ζ, c, -⟩)`. Use `right`. Rewrite using `[_root_.GlobalTheory.EtC.ClsSpec.res_map, h, _root_.GlobalTheory.EtC.ClsSpec.smap_zero]`. Conclude with `Or.inl ζ.2.1)`.

Rewrite using `[← hb, _root_.GlobalTheory.EtC.ClsSpec.map_comp, cokernel.condition, sec_map_zero_apply]`. Establish `hA' : Abelian.monoLift (ι.f 0) _ hA ≫ ι.f 0 = _root_.GlobalTheory.EtC.resι (ZMod q) (_root_.GlobalTheory.EtC.tw q i)` using `Abelian.monoLift_comp _ _ _`. Establish `hd : Abelian.monoLift (ι.f 0) _ hA ≫ D.d 0 1 = 0`. Rewrite using `[← cancel_mono (ι.f 1), zero_comp, Category.assoc, ← ι.comm, ← Category.assoc, hA', hAd]`. Set `ε : _root_.GlobalTheory.EtC.sgl (_root_.GlobalTheory.EtC.tw q i) ⟶ D` to `HomologicalComplex.mkHomFromSingle (Abelian.monoLift (ι.f 0) _ hA) (by`.

Introduce `k hk`. Establish `hk1 : k = 1` using `by simpa using hk.symm`. Substitute `hk1` using the available equality. Conclude with `hd)`. Establish `hε0 : ε.f 0 = (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 (_root_.GlobalTheory.EtC.tw q i)).hom ≫ Abelian.monoLift (ι.f 0) _ hA` using `HomologicalComplex.mkHomFromSingle_f _ _`.

Establish `haug : (_root_.GlobalTheory.EtC.resAug (_root_.GlobalTheory.EtC.tw q i)).f 0 = (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 (_root_.GlobalTheory.EtC.tw q i)).hom ≫ _root_.GlobalTheory.EtC.resι (ZMod q) (_root_.GlobalTheory.EtC.tw q i)`. Rewrite using `[← hterm]`. Unfold `_root_.GlobalTheory.EtC.sglι`. Use `erw [Iso.hom_inv_id_assoc]`. Establish `hει : ε.f 0 ≫ ι.f 0 = (_root_.GlobalTheory.EtC.resAug (_root_.GlobalTheory.EtC.tw q i)).f 0`.

Rewrite using `[haug]`. Use `erw [hε0, Category.assoc, hA']`. Apply the tactic sequence `all_goals rfl`. Establish `hterm' : _root_.GlobalTheory.EtC.sglι (_root_.GlobalTheory.EtC.tw q i) ≫ ε.f 0 ≫ ι.f 0 = _root_.GlobalTheory.EtC.resι (ZMod q) (_root_.GlobalTheory.EtC.tw q i)`. Rewrite using `[hει, hterm]`.

Use `⟨fun U ζ => _root_.GlobalTheory.EtC.Sec.map (ε.f 0) (_root_.GlobalTheory.EtC.Sec.map (_root_.GlobalTheory.EtC.sglι (_root_.GlobalTheory.EtC.tw q i)) (_root_.GlobalTheory.EtC.twGen i ζ)), ?_, ?_⟩` and prove the remaining obligations. Unfold `_root_.GlobalTheory.EtC.IsTwRes`. Use `⟨?_, ε, ?_, fun U ζ => rfl⟩` and prove the remaining obligations. Rewrite using `[CochainComplex.isStrictlyGE_iff]`. Introduce `n hn`.

Conclude with `@IsZero.of_mono _ _ _ _ _ (ι.f n) (hmono n) (CochainComplex.isZero_of_isStrictlyGE _ 0 n hn)`. Use `⟨fun n => ?_⟩` and prove the remaining obligations. Break down `lt_trichotomy n 0 with hn | rfl | hn` into its components or cases. Rewrite using `[quasiIsoAt_iff_exactAt ε n (HomologicalComplex.exactAt_single_obj _ _ _ _ hn.ne)]`. Conclude with `ShortComplex.exact_of_isZero_X₂ _ (@IsZero.of_mono _ _ _ _ _ (ι.f n) (hmono n) (CochainComplex.isZero_of_isStrictlyGE _ 0 n hn))`.

Rewrite using `[quasiIsoAt_iff' ε (-1) 0 1 (by simp) (by simp), ShortComplex.quasiIso_iff_of_zeros _ ?_ ?_ ?_]`. Prove the components needed by the constructor for the conclusion. Rewrite using `[_root_.GlobalTheory.EtC.exactIff]`. Introduce `U b hb`. Establish `hcyc : _root_.GlobalTheory.EtC.Sec.map ((_root_.GlobalTheory.EtC.res (ZMod q) (_root_.GlobalTheory.EtC.tw q i)).d 0 1) (_root_.GlobalTheory.EtC.Sec.map (ι.f 0) b) = 0` using `by erw [_root_.GlobalTheory.EtC.ClsSpec.map_comp, ι.comm, ← _root_.GlobalTheory.EtC.ClsSpec.map_comp, hb]`.

Conclude with `_root_.GlobalTheory.EtC.ClsSpec.smap_zero _`. Take `⟨y, hy⟩` from `((_root_.GlobalTheory.EtC.resSec (ZMod q) (_root_.GlobalTheory.EtC.tw q i) U).1 _).1 hcyc`. Establish `hb' : _root_.GlobalTheory.EtC.Sec.map (ε.f 0) (_root_.GlobalTheory.EtC.Sec.map (_root_.GlobalTheory.EtC.sglι (_root_.GlobalTheory.EtC.tw q i)) y) = b`. Apply `hinj 0 U` to reduce the goal to its premises. Simplify using `only [_root_.GlobalTheory.EtC.ClsSpec.map_comp, Category.assoc, hterm', hy]`.

Conclude with `etLoc_of_forall fun V g => ⟨_root_.GlobalTheory.EtC.Sec.res g (_root_.GlobalTheory.EtC.Sec.map (_root_.GlobalTheory.EtC.sglι (_root_.GlobalTheory.EtC.tw q i)) y), (_root_.GlobalTheory.EtC.ClsSpec.res_map (ε.f 0) g _).symm.trans (congrArg (_root_.GlobalTheory.EtC.Sec.res g) hb')⟩`. Establish `hcomp : Mono ((HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 (_root_.GlobalTheory.EtC.tw q i)).hom ≫ _root_.GlobalTheory.EtC.resι (ZMod q) (_root_.GlobalTheory.EtC.tw q i))` using `@mono_comp _ _ _ _ _ _ (@IsIso.mono_of_iso _ _ _ _ _ (Iso.isIso_hom _)) _ hAmono`. Rewrite `hcomp` using `[← haug, ← hει]`. Conclude with `@mono_of_mono _ _ _ _ _ (ε.f 0) (ι.f 0) hcomp`. Conclude with `(HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℤ) 0 (_root_.GlobalTheory.EtC.tw q i) (-1) (by norm_num)).eq_of_src _ _`.

Conclude with `(HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℤ) 0 (_root_.GlobalTheory.EtC.tw q i) 1 (by norm_num)).eq_of_tgt _ _`. Conclude with `(@IsZero.of_mono _ _ _ _ _ (ι.f (-1)) (hmono (-1)) (CochainComplex.isZero_of_isStrictlyGE _ 0 (-1) (by simp))).eq_of_src _ _`. Rewrite using `[quasiIsoAt_iff_exactAt ε n (HomologicalComplex.exactAt_single_obj _ _ _ _ hn.ne'), D.exactAt_iff' (n - 1) n (n + 1) (by simp) (by simp), _root_.GlobalTheory.EtC.exactIff]`. Introduce `U b hb`. Establish `hcyc : _root_.GlobalTheory.EtC.Sec.map ((_root_.GlobalTheory.EtC.res (ZMod q) (_root_.GlobalTheory.EtC.tw q i)).d n (n + 1)) (_root_.GlobalTheory.EtC.Sec.map (ι.f n) b) = 0` using `by erw [_root_.GlobalTheory.EtC.ClsSpec.map_comp, ι.comm, ← _root_.GlobalTheory.EtC.ClsSpec.map_comp, hb]`.

Conclude with `_root_.GlobalTheory.EtC.ClsSpec.smap_zero _`. Establish `hex` using `(_root_.GlobalTheory.EtC.resSec (ZMod q) (_root_.GlobalTheory.EtC.tw q i) U).2.2.1 (n - 1) n (n + 1) hn (by ring) _ rfl hcyc`. Establish `hsupp` using `(himg n U (_root_.GlobalTheory.EtC.Sec.map (ι.f n) b)).1 ⟨b, rfl⟩`. Use `_root_.GlobalTheory.EtC.ClsSpec.loc_mono (_root_.GlobalTheory.EtC.ClsSpec.loc_and hex hsupp) ?_` and prove the remaining obligations. Introduce and unpack `V g ⟨⟨y, hy⟩, hq | hz⟩`.

Take `⟨y', rfl⟩` from `(himg (n - 1) V y).2 (etLoc_of_forall fun W h => Or.inl (_root_.GlobalTheory.EtC.ClsSpec.unit_res h hq))`. Use `⟨y', hinj n V ?_⟩` and prove the remaining obligations. Conclude with `(_root_.GlobalTheory.EtC.ClsSpec.map_comp (D.d (n - 1) n) (ι.f n) y').trans ((congrArg (fun φ => _root_.GlobalTheory.EtC.Sec.map φ y') (ι.comm (n - 1) n).symm).trans ((_root_.GlobalTheory.EtC.ClsSpec.map_comp (ι.f (n - 1)) ((_root_.GlobalTheory.EtC.res (ZMod q) (_root_.GlobalTheo …`. Use `⟨0, ?_⟩ erw [_root_.GlobalTheory.EtC.ClsSpec.smap_zero]` and prove the remaining obligations. Apply `hinj n V` to reduce the goal to its premises.

Conclude with `(_root_.GlobalTheory.EtC.ClsSpec.smap_zero _).trans (hz.symm.trans (_root_.GlobalTheory.EtC.ClsSpec.res_map _ g b))`. Introduce `U ζ`. Simplify using `only [_root_.GlobalTheory.EtC.ClsSpec.map_comp, Category.assoc, hterm']`. Both sides reduce to the same expression.
-/
theorem _root_.GlobalTheory.EtC.SuppRes.supp_res : ∀ (q : ℕ) [NeZero q] (i : ℤ)
    (D : _root_.GlobalTheory.EtC.Cx (ZMod q))
    (ι : D ⟶ _root_.GlobalTheory.EtC.res _ (_root_.GlobalTheory.EtC.tw q i)),
    (∀ n U, Function.Injective (_root_.GlobalTheory.EtC.Sec.map (ι.f n) (U := U))) →
    (∀ n U (a : _root_.GlobalTheory.EtC.Sec ((_root_.GlobalTheory.EtC.res _ (_root_.GlobalTheory.EtC.tw q i)).X n) U),
      (∃ b, _root_.GlobalTheory.EtC.Sec.map (ι.f n) b = a) ↔
      _root_.GlobalTheory.EtC.Loc U fun V g =>
        IsUnit (q : Γ(V, ⊤)) ∨ _root_.GlobalTheory.EtC.Sec.res g a = 0) →
    ∃ e : ∀ U : Scheme.{0}, _root_.GlobalTheory.EtC.Prim q Γ(U, ⊤) → _root_.GlobalTheory.EtC.Sec (D.X 0) U,
      _root_.GlobalTheory.EtC.IsTwRes q i D e ∧
      ∀ U ζ, _root_.GlobalTheory.EtC.Sec.map (ι.f 0) (e U ζ) = _root_.GlobalTheory.EtC.resGen i ζ := by
  intro q _ i D ι hinj himg
  haveI hmono : ∀ n, Mono (ι.f n) := fun n =>
    (_root_.GlobalTheory.EtC.mono_epi_sections (ZMod q) (ι.f n)).1.2 (fun U => hinj n U)
  obtain ⟨-, -, hIge, -, hterm, hAmono, hAd, -⟩ :=
    _root_.GlobalTheory.EtC.ResBasic.res_basic (ZMod q) (_root_.GlobalTheory.EtC.tw q i)
  haveI := hIge
  haveI := hAmono
  have hA : _root_.GlobalTheory.EtC.resι (ZMod q) (_root_.GlobalTheory.EtC.tw q i) ≫
      cokernel.π (ι.f 0) = 0 := by
    apply shv_hom_ext_of_sec_map_eq
    intro U y
    rw [sec_map_zero_apply, ← _root_.GlobalTheory.EtC.ClsSpec.map_comp]
    obtain ⟨b, hb⟩ := (himg 0 U (_root_.GlobalTheory.EtC.Sec.map
      (_root_.GlobalTheory.EtC.resι (ZMod q) (_root_.GlobalTheory.EtC.tw q i)) y)).2 (by
        refine _root_.GlobalTheory.EtC.ClsSpec.loc_mono
          ((_root_.GlobalTheory.EtC.twist_sections q i).1 U y) ?_
        rintro V g (h | ⟨ζ, c, -⟩)
        · right
          rw [_root_.GlobalTheory.EtC.ClsSpec.res_map, h,
            _root_.GlobalTheory.EtC.ClsSpec.smap_zero]
        · exact Or.inl ζ.2.1)
    rw [← hb, _root_.GlobalTheory.EtC.ClsSpec.map_comp, cokernel.condition, sec_map_zero_apply]
  have hA' : Abelian.monoLift (ι.f 0) _ hA ≫ ι.f 0 =
      _root_.GlobalTheory.EtC.resι (ZMod q) (_root_.GlobalTheory.EtC.tw q i) :=
    Abelian.monoLift_comp _ _ _
  have hd : Abelian.monoLift (ι.f 0) _ hA ≫ D.d 0 1 = 0 := by
    rw [← cancel_mono (ι.f 1), zero_comp, Category.assoc, ← ι.comm, ← Category.assoc, hA', hAd]
  let ε : _root_.GlobalTheory.EtC.sgl (_root_.GlobalTheory.EtC.tw q i) ⟶ D :=
    HomologicalComplex.mkHomFromSingle (Abelian.monoLift (ι.f 0) _ hA) (by
        intro k hk
        have hk1 : k = 1 := by simpa using hk.symm
        subst hk1
        exact hd)
  have hε0 : ε.f 0 = (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0
      (_root_.GlobalTheory.EtC.tw q i)).hom ≫ Abelian.monoLift (ι.f 0) _ hA :=
    HomologicalComplex.mkHomFromSingle_f _ _
  have haug : (_root_.GlobalTheory.EtC.resAug (_root_.GlobalTheory.EtC.tw q i)).f 0 =
      (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 (_root_.GlobalTheory.EtC.tw q i)).hom ≫
        _root_.GlobalTheory.EtC.resι (ZMod q) (_root_.GlobalTheory.EtC.tw q i) := by
    rw [← hterm]
    unfold _root_.GlobalTheory.EtC.sglι
    erw [Iso.hom_inv_id_assoc]
  have hει : ε.f 0 ≫ ι.f 0 = (_root_.GlobalTheory.EtC.resAug (_root_.GlobalTheory.EtC.tw q i)).f 0 := by
    rw [haug]
    erw [hε0, Category.assoc, hA']
    all_goals rfl
  have hterm' : _root_.GlobalTheory.EtC.sglι (_root_.GlobalTheory.EtC.tw q i) ≫ ε.f 0 ≫ ι.f 0 =
      _root_.GlobalTheory.EtC.resι (ZMod q) (_root_.GlobalTheory.EtC.tw q i) := by
    rw [hει, hterm]
  refine ⟨fun U ζ => _root_.GlobalTheory.EtC.Sec.map (ε.f 0) (_root_.GlobalTheory.EtC.Sec.map
    (_root_.GlobalTheory.EtC.sglι (_root_.GlobalTheory.EtC.tw q i)) (_root_.GlobalTheory.EtC.twGen i ζ)), ?_, ?_⟩
  · unfold _root_.GlobalTheory.EtC.IsTwRes
    refine ⟨?_, ε, ?_, fun U ζ => rfl⟩
    · rw [CochainComplex.isStrictlyGE_iff]
      intro n hn
      exact @IsZero.of_mono _ _ _ _ _ (ι.f n) (hmono n) (CochainComplex.isZero_of_isStrictlyGE _ 0 n hn)
    · refine ⟨fun n => ?_⟩
      rcases lt_trichotomy n 0 with hn | rfl | hn
      · rw [quasiIsoAt_iff_exactAt ε n (HomologicalComplex.exactAt_single_obj _ _ _ _ hn.ne)]
        exact ShortComplex.exact_of_isZero_X₂ _
          (@IsZero.of_mono _ _ _ _ _ (ι.f n) (hmono n) (CochainComplex.isZero_of_isStrictlyGE _ 0 n hn))
      · rw [quasiIsoAt_iff' ε (-1) 0 1 (by simp) (by simp),
          ShortComplex.quasiIso_iff_of_zeros _ ?_ ?_ ?_]
        · constructor
          · rw [_root_.GlobalTheory.EtC.exactIff]
            intro U b hb
            have hcyc : _root_.GlobalTheory.EtC.Sec.map
                ((_root_.GlobalTheory.EtC.res (ZMod q) (_root_.GlobalTheory.EtC.tw q i)).d 0 1)
                (_root_.GlobalTheory.EtC.Sec.map (ι.f 0) b) = 0 := by
              erw [_root_.GlobalTheory.EtC.ClsSpec.map_comp, ι.comm,
                ← _root_.GlobalTheory.EtC.ClsSpec.map_comp, hb]
              exact _root_.GlobalTheory.EtC.ClsSpec.smap_zero _
            obtain ⟨y, hy⟩ := ((_root_.GlobalTheory.EtC.resSec (ZMod q)
              (_root_.GlobalTheory.EtC.tw q i) U).1 _).1 hcyc
            have hb' : _root_.GlobalTheory.EtC.Sec.map (ε.f 0) (_root_.GlobalTheory.EtC.Sec.map
                (_root_.GlobalTheory.EtC.sglι (_root_.GlobalTheory.EtC.tw q i)) y) = b := by
              apply hinj 0 U
              simp only [_root_.GlobalTheory.EtC.ClsSpec.map_comp, Category.assoc, hterm', hy]
            exact etLoc_of_forall fun V g =>
              ⟨_root_.GlobalTheory.EtC.Sec.res g (_root_.GlobalTheory.EtC.Sec.map
                (_root_.GlobalTheory.EtC.sglι (_root_.GlobalTheory.EtC.tw q i)) y),
                (_root_.GlobalTheory.EtC.ClsSpec.res_map (ε.f 0) g _).symm.trans
                  (congrArg (_root_.GlobalTheory.EtC.Sec.res g) hb')⟩
          · have hcomp : Mono ((HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0
                (_root_.GlobalTheory.EtC.tw q i)).hom ≫
                _root_.GlobalTheory.EtC.resι (ZMod q) (_root_.GlobalTheory.EtC.tw q i)) :=
              @mono_comp _ _ _ _ _ _ (@IsIso.mono_of_iso _ _ _ _ _ (Iso.isIso_hom _)) _ hAmono
            rw [← haug, ← hει] at hcomp
            exact @mono_of_mono _ _ _ _ _ (ε.f 0) (ι.f 0) hcomp
        · exact (HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℤ) 0 (_root_.GlobalTheory.EtC.tw q i)
            (-1) (by norm_num)).eq_of_src _ _
        · exact (HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℤ) 0 (_root_.GlobalTheory.EtC.tw q i)
            1 (by norm_num)).eq_of_tgt _ _
        · exact (@IsZero.of_mono _ _ _ _ _ (ι.f (-1)) (hmono (-1))
            (CochainComplex.isZero_of_isStrictlyGE _ 0 (-1) (by simp))).eq_of_src _ _
      · rw [quasiIsoAt_iff_exactAt ε n (HomologicalComplex.exactAt_single_obj _ _ _ _ hn.ne'),
          D.exactAt_iff' (n - 1) n (n + 1) (by simp) (by simp),
          _root_.GlobalTheory.EtC.exactIff]
        intro U b hb
        have hcyc : _root_.GlobalTheory.EtC.Sec.map
            ((_root_.GlobalTheory.EtC.res (ZMod q) (_root_.GlobalTheory.EtC.tw q i)).d n (n + 1))
            (_root_.GlobalTheory.EtC.Sec.map (ι.f n) b) = 0 := by
          erw [_root_.GlobalTheory.EtC.ClsSpec.map_comp, ι.comm,
            ← _root_.GlobalTheory.EtC.ClsSpec.map_comp, hb]
          exact _root_.GlobalTheory.EtC.ClsSpec.smap_zero _
        have hex := (_root_.GlobalTheory.EtC.resSec (ZMod q)
          (_root_.GlobalTheory.EtC.tw q i) U).2.2.1 (n - 1) n (n + 1) hn (by ring) _ rfl hcyc
        have hsupp := (himg n U (_root_.GlobalTheory.EtC.Sec.map (ι.f n) b)).1 ⟨b, rfl⟩
        refine _root_.GlobalTheory.EtC.ClsSpec.loc_mono (_root_.GlobalTheory.EtC.ClsSpec.loc_and hex hsupp) ?_
        rintro V g ⟨⟨y, hy⟩, hq | hz⟩
        · obtain ⟨y', rfl⟩ := (himg (n - 1) V y).2
            (etLoc_of_forall fun W h => Or.inl (_root_.GlobalTheory.EtC.ClsSpec.unit_res h hq))
          refine ⟨y', hinj n V ?_⟩
          exact (_root_.GlobalTheory.EtC.ClsSpec.map_comp (D.d (n - 1) n) (ι.f n) y').trans
            ((congrArg (fun φ => _root_.GlobalTheory.EtC.Sec.map φ y') (ι.comm (n - 1) n).symm).trans
              ((_root_.GlobalTheory.EtC.ClsSpec.map_comp (ι.f (n - 1))
                ((_root_.GlobalTheory.EtC.res (ZMod q) (_root_.GlobalTheory.EtC.tw q i)).d (n - 1) n)
                  y').symm.trans
                (hy.trans (_root_.GlobalTheory.EtC.ClsSpec.res_map (ι.f n) g b))))
        · refine ⟨0, ?_⟩
          erw [_root_.GlobalTheory.EtC.ClsSpec.smap_zero]
          apply hinj n V
          exact (_root_.GlobalTheory.EtC.ClsSpec.smap_zero _).trans
            (hz.symm.trans (_root_.GlobalTheory.EtC.ClsSpec.res_map _ g b))
  · intro U ζ
    simp only [_root_.GlobalTheory.EtC.ClsSpec.map_comp, Category.assoc, hterm']
    rfl

end GlobalTheory.EtC.SuppRes

end

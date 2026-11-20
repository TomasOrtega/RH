import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.NonUnitAt
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsSectionOfIsIsoRestrict
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteOpenImmersionPSpace
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsCartierOnNormalizedBlowup
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteTypeCycAway

noncomputable section

open AlgebraicGeometry CategoryTheory Limits IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.ZH GlobalTheory.Poinc
open GlobalTheory.SiegelTor

namespace GlobalTheory.NormBlowupInt

/- English proof (translation)
Use `⟨fun U hU => ?_⟩` and prove the remaining obligations. Use `letI := (f.app U).hom.toAlgebra`. Use `letI : Algebra o Γ(Y, U) := ((Scheme.ΓSpecIso o).inv ≫ g.appLE ⊤ U le_top).hom.toAlgebra`. Use `haveI : Algebra.FiniteType o Γ(Y, U) := (g.finiteType_appLE (isAffineOpen_top _) hU le_top).comp (.of_surjective _ (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso o).inv).2)`. Use `haveI : Algebra.FiniteType ℤ Γ(Y, U) := .trans (S := o) inferInstance inferInstance`.

Use `haveI : IsNoetherianRing Γ(Y, U) := Algebra.FiniteType.isNoetherianRing ℤ _`. Set `D : Set X` to `genericPoints X`. Establish `hD : Dense D` using `dense_iff_closure_eq.mpr genericPoints.closure`. Set `ι` to `↥(D ∩ (f ⁻¹ᵁ U : X.Opens))`. Use `haveI : Finite ι := (GlobalTheory.finite_genericPoints_inter _ (f.isCompact_preimage hU.isCompact)).to_subtype`.

Use `letI (x : ι) : Algebra Γ(Y, U) (X.residueField x.1) := (f.app U ≫ X.evaluation (f ⁻¹ᵁ U) x.1 x.2.2).hom.toAlgebra`. Use `haveI (x : ι) : Algebra.EssFiniteType Γ(Y, U) (X.residueField x.1) := by`. Express the relevant statement in the definitionally equal form `(f.app U ≫ X.evaluation (f ⁻¹ᵁ U) x.1 x.2.2).hom.EssFiniteType`. Rewrite using `[← Scheme.evaluation_naturality f (V := U) x.1 x.2.2]`. Conclude with `.comp (.comp (essFiniteType_germ hU (f x.1) x.2.2) (RingHom.FiniteType.of_surjective _ (Y.residue_surjective _)).essFiniteType) (hess _ x.2.1)`.

Use `haveI (x : ι) := GlobalTheory.ZMain.finite_integralClosure_field Γ(Y, U) (X.residueField x.1)`. Use `haveI : Module.Finite Γ(Y, U) (integralClosure Γ(Y, U) Γ(X, f ⁻¹ᵁ U)) := by`. Use `finite_integralClosure_of_family (L := fun x : ι => X.residueField x.1) (fun x => { (X.evaluation (f ⁻¹ᵁ U) x.1 x.2.2).hom with commutes' := fun _ => rfl }) fun b hb => ?_` and prove the remaining obligations. Rewrite using `[← basicOpen_eq_bot_iff, eq_bot_iff]`. Introduce `y hy`.

Take `⟨x, hx, hxD⟩` from `hD.inter_open_nonempty _ (X.basicOpen b).isOpen ⟨y, hy⟩`. Conclude with `((X.evaluation_eq_zero_iff_notMem_basicOpen x (X.basicOpen_le b hx) b).mp (hb ⟨x, hxD, X.basicOpen_le b hx⟩) hx).elim`. Rewrite using `[f.fromNormalization_app hU]`. Conclude with `RingHom.Finite.comp (.of_surjective _ (ConcreteCategory.bijective_of_isIso (f.normalizationObjIso hU).inv).2) (RingHom.finite_algebraMap.mpr this)`.
-/
theorem isFinite_fromNormalization_int_of_isReduced {X Y : Scheme.{0}} {o : CommRingCat.{0}}
    [Algebra.FiniteType ℤ o] (f : X ⟶ Y) [QuasiCompact f] [QuasiSeparated f] (g : Y ⟶ Spec o)
    [LocallyOfFiniteType g] [IsReduced X] [IsLocallyNoetherian X]
    (hess : ∀ x ∈ genericPoints X, (f.residueFieldMap x).hom.EssFiniteType) :
    IsFinite f.fromNormalization := by
  refine ⟨fun U hU => ?_⟩
  letI := (f.app U).hom.toAlgebra
  letI : Algebra o Γ(Y, U) := ((Scheme.ΓSpecIso o).inv ≫ g.appLE ⊤ U le_top).hom.toAlgebra
  haveI : Algebra.FiniteType o Γ(Y, U) :=
    (g.finiteType_appLE (isAffineOpen_top _) hU le_top).comp
      (.of_surjective _ (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso o).inv).2)
  haveI : Algebra.FiniteType ℤ Γ(Y, U) := .trans (S := o) inferInstance inferInstance
  haveI : IsNoetherianRing Γ(Y, U) := Algebra.FiniteType.isNoetherianRing ℤ _
  let D : Set X := genericPoints X
  have hD : Dense D := dense_iff_closure_eq.mpr genericPoints.closure
  let ι := ↥(D ∩ (f ⁻¹ᵁ U : X.Opens))
  haveI : Finite ι := (GlobalTheory.finite_genericPoints_inter _ (f.isCompact_preimage hU.isCompact)).to_subtype
  letI (x : ι) : Algebra Γ(Y, U) (X.residueField x.1) :=
    (f.app U ≫ X.evaluation (f ⁻¹ᵁ U) x.1 x.2.2).hom.toAlgebra
  haveI (x : ι) : Algebra.EssFiniteType Γ(Y, U) (X.residueField x.1) := by
    change (f.app U ≫ X.evaluation (f ⁻¹ᵁ U) x.1 x.2.2).hom.EssFiniteType
    rw [← Scheme.evaluation_naturality f (V := U) x.1 x.2.2]
    exact .comp (.comp (essFiniteType_germ hU (f x.1) x.2.2)
      (RingHom.FiniteType.of_surjective _ (Y.residue_surjective _)).essFiniteType) (hess _ x.2.1)
  haveI (x : ι) := GlobalTheory.ZMain.finite_integralClosure_field Γ(Y, U) (X.residueField x.1)
  haveI : Module.Finite Γ(Y, U) (integralClosure Γ(Y, U) Γ(X, f ⁻¹ᵁ U)) := by
    refine finite_integralClosure_of_family (L := fun x : ι => X.residueField x.1)
      (fun x => { (X.evaluation (f ⁻¹ᵁ U) x.1 x.2.2).hom with commutes' := fun _ => rfl })
      fun b hb => ?_
    rw [← basicOpen_eq_bot_iff, eq_bot_iff]
    intro y hy
    obtain ⟨x, hx, hxD⟩ := hD.inter_open_nonempty _ (X.basicOpen b).isOpen ⟨y, hy⟩
    exact ((X.evaluation_eq_zero_iff_notMem_basicOpen x (X.basicOpen_le b hx) b).mp
      (hb ⟨x, hxD, X.basicOpen_le b hx⟩) hx).elim
  rw [f.fromNormalization_app hU]
  exact RingHom.Finite.comp
    (.of_surjective _ (ConcreteCategory.bijective_of_isIso (f.normalizationObjIso hU).inv).2)
    (RingHom.finite_algebraMap.mpr this)

/- English proof (translation)
Take `⟨D, hD⟩` from `EffCartierData.exists_idealSheaf_eq hb.1`. Establish `hD' : Dense (((J.comap b).support : Set X')ᶜ)`. Rewrite using `[← hD, ← D.coe_nonzeroLocus_canonical]`. Conclude with `D.dense_nonzeroLocus_canonical`. Set `Uc : Z.Opens` to `J.support.compl`.

Use `haveI : IsIso (b ∣_ Uc) := hiso Uc fun x hx => hx`. Use `haveI hoi : IsOpenImmersion ((b ⁻¹ᵁ Uc).ι ≫ b) := by`. Rewrite using `[← morphismRestrict_ι]`. Use `infer_instance`. Rewrite using `[dense_iff_inter_open]`.

Introduce `O hO hne`. Take `⟨y, hyO, hy⟩` from `hD'.inter_open_nonempty O hO hne`. Establish `hyU : y ∈ b ⁻¹ᵁ Uc`. Express the relevant statement in the definitionally equal form `b y ∉ J.support`. Introduce `h`.

Conclude with `hy ((GlobalTheory.ProjBlowup.mem_support_comap J b y).2 h)`. Set `O' : (b ⁻¹ᵁ Uc).toScheme.Opens` to `(b ⁻¹ᵁ Uc).ι ⁻¹ᵁ ⟨O, hO⟩`. Establish `hopen : IsOpen (((b ⁻¹ᵁ Uc).ι ≫ b) '' (O' : Set (b ⁻¹ᵁ Uc).toScheme))` using `((b ⁻¹ᵁ Uc).ι ≫ b).isOpenEmbedding.isOpenMap _ O'.isOpen`. Take `⟨w, ⟨t, htO, rfl⟩, hwW⟩` from `hWd.inter_open_nonempty _ hopen ⟨_, ⟨⟨y, hyU⟩, hyO, rfl⟩⟩`. Use `⟨(b ⁻¹ᵁ Uc).ι t, htO, ?_⟩` and prove the remaining obligations.

Express the relevant statement in the definitionally equal form `b ((b ⁻¹ᵁ Uc).ι t) ∈ W`. Rewrite using `[← Scheme.Hom.comp_apply]` and apply the resulting hypothesis.
-/
theorem dense_preimage_of_blowup {Z X' : Scheme.{0}} (J : Z.IdealSheafData) (b : X' ⟶ Z)
    (hb : FinalTheorems.Blowup b J) (hiso : ∀ V : Z.Opens, (∀ x ∈ V, x ∉ J.support) → IsIso (b ∣_ V))
    (W : Z.Opens) (hWd : Dense (W : Set Z)) : Dense ((b ⁻¹ᵁ W : X'.Opens) : Set X') := by
  obtain ⟨D, hD⟩ := EffCartierData.exists_idealSheaf_eq hb.1
  have hD' : Dense (((J.comap b).support : Set X')ᶜ) := by
    rw [← hD, ← D.coe_nonzeroLocus_canonical]
    exact D.dense_nonzeroLocus_canonical
  let Uc : Z.Opens := J.support.compl
  haveI : IsIso (b ∣_ Uc) := hiso Uc fun x hx => hx
  haveI hoi : IsOpenImmersion ((b ⁻¹ᵁ Uc).ι ≫ b) := by
    rw [← morphismRestrict_ι]; infer_instance
  rw [dense_iff_inter_open]
  intro O hO hne
  obtain ⟨y, hyO, hy⟩ := hD'.inter_open_nonempty O hO hne
  have hyU : y ∈ b ⁻¹ᵁ Uc := by
    change b y ∉ J.support
    intro h
    exact hy ((GlobalTheory.ProjBlowup.mem_support_comap J b y).2 h)
  let O' : (b ⁻¹ᵁ Uc).toScheme.Opens := (b ⁻¹ᵁ Uc).ι ⁻¹ᵁ ⟨O, hO⟩
  have hopen : IsOpen (((b ⁻¹ᵁ Uc).ι ≫ b) '' (O' : Set (b ⁻¹ᵁ Uc).toScheme)) :=
    ((b ⁻¹ᵁ Uc).ι ≫ b).isOpenEmbedding.isOpenMap _ O'.isOpen
  obtain ⟨w, ⟨t, htO, rfl⟩, hwW⟩ := hWd.inter_open_nonempty _ hopen ⟨_, ⟨⟨y, hyU⟩, hyO, rfl⟩⟩
  refine ⟨(b ⁻¹ᵁ Uc).ι t, htO, ?_⟩
  change b ((b ⁻¹ᵁ Uc).ι t) ∈ W
  rwa [← Scheme.Hom.comp_apply]

end GlobalTheory.NormBlowupInt

namespace GlobalTheory.NormBlowupInt

/- English proof (translation)
Introduce `n Z z hz hZ J W hWd hWJ`. Use `haveI : Algebra.FiniteType ℤ (cycAway n) := finiteType_cycAway n`. Use `haveI : Algebra.FiniteType ℤ (CommRingCat.of (cycAway n)) := ‹Algebra.FiniteType ℤ (cycAway n)›`. Use `haveI : IsNoetherianRing (cycAway n) := Algebra.FiniteType.isNoetherianRing ℤ _`. Take `⟨X', b, hb, hbs, hiso⟩` from `GlobalTheory.ProjBlowup.exists_blowup z hz J`.

Use `haveI : LocallyOfFiniteType (b ≫ z) := by`. Take `⟨m, i, hi, e⟩` from `hbs`. Use `isProper_str (cycAway n) m` as an intermediate fact. Rewrite using `[← e]`. Use `infer_instance`.

Use `haveI : IsLocallyNoetherian X' := LocallyOfFiniteType.isLocallyNoetherian (b ≫ z)`. Set `V : X'.Opens` to `b ⁻¹ᵁ W`. Use `haveI hbW : IsIso (b ∣_ W) := hiso W fun x hx hJ => hWJ x hJ hx`. Use `haveI hoi : IsOpenImmersion (V.ι ≫ b) := by`. Rewrite using `[← morphismRestrict_ι]`.

Use `infer_instance`. Use `haveI : GlobalTheory.IsNormalScheme Z := .of_pred hZ`. Use `haveI hN : GlobalTheory.IsNormalScheme V.toScheme := .of_isOpenImmersion (V.ι ≫ b)`. Use `haveI : IsReduced V.toScheme := by`. Conclude with `inferInstance`.

Use `haveI hfin : IsFinite V.ι.fromNormalization := isFinite_fromNormalization_int_of_isReduced (o := CommRingCat.of (cycAway n)) V.ι (b ≫ z) fun x _ => (LocallyOfFiniteType.stalkMap V.ι x).residueFieldMap`. Set `ν` to `V.ι.fromNormalization`. Establish `hS : ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme V.ι.normalization` using `IsNormalScheme.pred _`. Establish `hν : IsIso (ν ∣_ V)`. Establish `H` using `isPullback_toNormalization_of_mono (𝟙 _) V.ι V.ι (Category.id_comp _).symm`.

Establish `e` using `IsPullback.isoIsPullback_hom_fst _ _ (isPullback_morphismRestrict V.ι.fromNormalization V) H.flip`. Rewrite using `[← e]`. Use `infer_instance`. Establish `hd : Dense ((ν ⁻¹ᵁ V : V.ι.normalization.Opens) : Set V.ι.normalization)`. Use `V.ι.toNormalization.denseRange.mono ?_` and prove the remaining obligations.

Introduce and unpack `_ ⟨x, rfl⟩`. Express the relevant statement in the definitionally equal form `V.ι.fromNormalization (V.ι.toNormalization x) ∈ V`. Rewrite using `[← Scheme.Hom.comp_apply, Scheme.Hom.toNormalization_fromNormalization]`. Conclude with `x.2`. Establish `hVd : Dense (V : Set X')` using `dense_preimage_of_blowup J b hb hiso W hWd`.

Take `⟨D, hD⟩` from `EffCartierData.exists_idealSheaf_eq hb.1`. Establish `hK : D.KeepsRegular ν`. Use `D.keepsRegular_of_dense ν (fun y => (hS y).1) (hd.mono fun t ht => ?_)` and prove the remaining obligations. Use `show ν t ∉ D.idealSheaf.support`. Rewrite using `[hD, GlobalTheory.ProjBlowup.mem_support_comap]`.

Conclude with `fun h => hWJ _ h ht`. Use `⟨V.ι.normalization, ν ≫ b, D.pull ν hK, ⟨inferInstance, X', b, ν, V, hb, rfl, hfin, hVd, hd, hν⟩, ?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[Category.assoc]`. Conclude with `isProjOver_comp_of_isFinite ν hbs`. Rewrite using `[EffCartierData.idealSheaf_pull, hD, Scheme.IdealSheafData.comap_comp]`.

Rewrite using `[morphismRestrict_comp]`. Conclude with `IsIso.comp_isIso' hν hbW`. Use `hd using 1` and compare the differences between its conclusion and the goal. Use extensionality with `t`. Simplify using `[V]`.
-/
theorem exists_normBl : ∀ (n : ℕ) (Z : Scheme.{0}) (z : Z ⟶ Sp (cycAway n)), IsProjOver z →
    ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme Z → ∀ (J : Z.IdealSheafData) (W : Z.Opens),
    Dense (W : Set Z) → (∀ x ∈ J.support, x ∉ W) → ∃ (S : Scheme.{0}) (π : S ⟶ Z)
    (BD : EffCartierData S), IsNormBl π J ∧ IsProjOver (π ≫ z) ∧ BD.idealSheaf = J.comap π ∧
    IsIso (π ∣_ W) ∧ Dense (π ⁻¹' W : Set S) := by
  intro n Z z hz hZ J W hWd hWJ
  haveI : Algebra.FiniteType ℤ (cycAway n) := finiteType_cycAway n
  haveI : Algebra.FiniteType ℤ (CommRingCat.of (cycAway n)) := ‹Algebra.FiniteType ℤ (cycAway n)›
  haveI : IsNoetherianRing (cycAway n) := Algebra.FiniteType.isNoetherianRing ℤ _
  obtain ⟨X', b, hb, hbs, hiso⟩ := GlobalTheory.ProjBlowup.exists_blowup z hz J
  haveI : LocallyOfFiniteType (b ≫ z) := by
    obtain ⟨m, i, hi, e⟩ := hbs
    have := isProper_str (cycAway n) m
    rw [← e]; infer_instance
  haveI : IsLocallyNoetherian X' := LocallyOfFiniteType.isLocallyNoetherian (b ≫ z)
  let V : X'.Opens := b ⁻¹ᵁ W
  haveI hbW : IsIso (b ∣_ W) := hiso W fun x hx hJ => hWJ x hJ hx
  haveI hoi : IsOpenImmersion (V.ι ≫ b) := by
    rw [← morphismRestrict_ι]; infer_instance
  haveI : GlobalTheory.IsNormalScheme Z := .of_pred hZ
  haveI hN : GlobalTheory.IsNormalScheme V.toScheme := .of_isOpenImmersion (V.ι ≫ b)
  haveI : IsReduced V.toScheme := by
    exact inferInstance
  haveI hfin : IsFinite V.ι.fromNormalization :=
    isFinite_fromNormalization_int_of_isReduced (o := CommRingCat.of (cycAway n)) V.ι (b ≫ z)
      fun x _ => (LocallyOfFiniteType.stalkMap V.ι x).residueFieldMap
  let ν := V.ι.fromNormalization
  have hS : ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme V.ι.normalization := IsNormalScheme.pred _
  have hν : IsIso (ν ∣_ V) := by
    have H := isPullback_toNormalization_of_mono (𝟙 _) V.ι V.ι (Category.id_comp _).symm
    have e := IsPullback.isoIsPullback_hom_fst _ _ (isPullback_morphismRestrict V.ι.fromNormalization V) H.flip
    rw [← e]
    infer_instance
  have hd : Dense ((ν ⁻¹ᵁ V : V.ι.normalization.Opens) : Set V.ι.normalization) := by
    refine V.ι.toNormalization.denseRange.mono ?_
    rintro _ ⟨x, rfl⟩
    change V.ι.fromNormalization (V.ι.toNormalization x) ∈ V
    rw [← Scheme.Hom.comp_apply, Scheme.Hom.toNormalization_fromNormalization]
    exact x.2
  have hVd : Dense (V : Set X') := dense_preimage_of_blowup J b hb hiso W hWd
  obtain ⟨D, hD⟩ := EffCartierData.exists_idealSheaf_eq hb.1
  have hK : D.KeepsRegular ν := by
    refine D.keepsRegular_of_dense ν (fun y => (hS y).1) (hd.mono fun t ht => ?_)
    show ν t ∉ D.idealSheaf.support
    rw [hD, GlobalTheory.ProjBlowup.mem_support_comap]
    exact fun h => hWJ _ h ht
  refine ⟨V.ι.normalization, ν ≫ b, D.pull ν hK,
    ⟨inferInstance, X', b, ν, V, hb, rfl, hfin, hVd, hd, hν⟩, ?_, ?_, ?_, ?_⟩
  · rw [Category.assoc]; exact isProjOver_comp_of_isFinite ν hbs
  · rw [EffCartierData.idealSheaf_pull, hD, Scheme.IdealSheafData.comap_comp]
  · rw [morphismRestrict_comp]; exact IsIso.comp_isIso' hν hbW
  · convert hd using 1
    ext t
    simp [V]

end GlobalTheory.NormBlowupInt

import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CompEqOneOfTransl
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ConstGen
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.TheoremOfCubeTwoProjectiveFactors
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.AbelianSchemeLawsUnconditional
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KTrivialOfGeometricFibres
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SurjRestrictSnd
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.TorsionFramePowEqIntegralGenerator
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGeneratorTorsionBundleAbelianSchemeSqZeroStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsionLineBundleTrivialBasicOpenOfTrivialFibreStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalTrivialityOfNoetherianDescentStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT
open scoped CategoryTheory.Obj
open GlobalTheory.CechPic GlobalTheory.AbDual

noncomputable section

namespace GlobalTheory.RigTorsTriv

/- English proof (translation)
Introduce `S A _ _ hA M hM hrig k hk hpow hfib`. Establish `key : ∀ {Y : Scheme.{0}} (f : Y ⟶ A.left), (∃ t : (M.pull f).Gen, t.IsGen) ↔ pull f (cls M hM) = 0` using `fun f => (cls_eq_zero_iff (pull_isLB hM f)).symm.trans (by rw [cls_pull hM f])`. Establish `hsurj : ∀ V : S.Opens, Function.Surjective (A.hom ∣_ V).appTop.hom` using `fun V => by`. Establish `hG : Out.GlobalFnsSt` using `GlobalTheory.abelianSchemeLaws_all.1.globalFns`. Establish `h1` using `hG _ _ (Out.TLinPf.isAb_pullback V.ι A hA)`.

Set `e` to `IsPullback.isoIsPullback _ _ (isPullback_morphismRestrict A.hom V) (IsPullback.of_hasPullback A.hom V.ι).flip`. Establish `he : e.hom ≫ pullback.snd A.hom V.ι = A.hom ∣_ V` using `IsPullback.isoIsPullback_hom_fst _ _ _ _`. Establish `hi : Function.Surjective e.hom.appTop.hom`. Establish `: IsIso (e.hom.app ⊤)` using `inferInstance`. Conclude with `(ConcreteCategory.bijective_of_isIso (e.hom.app ⊤)).2`.

Rewrite using `[← he, Scheme.Hom.comp_appTop, CommRingCat.hom_comp]`. Conclude with `hi.comp h1.2`. Establish `hc0 : pull (1 : 𝟙_ (Over S) ⟶ A).left (cls M hM) = 0` using `(key _).1 hrig`. Establish `hkM : k • cls M hM = 0`. Establish `h` using `(cls_eq_zero_iff (LB.isLB_linComb hM _ _)).2 hpow`.

Rewrite `h` using `[cls_linComb hM]`. Simplify `h` using `[pull_id]`. Use `GlobalTheory.CubeGlue.triv_of_locally_triv hM A.hom (1 : 𝟙_ (Over S) ⟶ A).left (by simpa using Over.w (1 : 𝟙_ (Over S) ⟶ A)) hsurj hrig ?_` and prove the remaining obligations. Introduce `s`. Take `⟨R, j, hj, ⟨p, hp⟩, -⟩` from `Scheme.exists_affine_mem_range_and_range_subset (x := s) (U := ⊤) trivial`.

Set `j' : Sp R ⟶ S` to `j`. Use `haveI : IsOpenImmersion j' := hj`. Set `A'` to `(Over.pullback j').obj A`. Establish `hA' : IsAbelianScheme A'` using `Out.TLinPf.isAb_pullback j' A hA`. Set `φ` to `pullback.fst A.hom j'`.

Establish `hM' : (M.pull φ).IsLB` using `pull_isLB hM φ`. Establish `key' : ∀ {Y : Scheme.{0}} (f : Y ⟶ A'.left), (∃ t : ((M.pull φ).pull f).Gen, t.IsGen) ↔ pull (f ≫ φ) (cls M hM) = 0` using `fun f => (cls_eq_zero_iff (pull_isLB hM' f)).symm.trans (by rw [cls_pull hM' f, cls_pull hM φ, pull_comp])`. Establish `hone : (1 : 𝟙_ (Over (Sp R)) ⟶ A').left ≫ φ = j' ≫ (1 : 𝟙_ (Over S) ⟶ A).left`. Establish `h` using `GlobalTheory.TorsFrameInt.one_comm (isGrpPullback_pullback A j')`. Rewrite using `[Hom.one_def, Hom.one_def]`.

Simplify using `using h`. Establish `hrig'` using `(key' _).2 (by rw [hone, pull_comp, hc0, map_zero])`. Establish `hk' : IsUnit (k : R)`. Establish `h` using `hk.map ((Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom.comp j'.appTop.hom)`. Simplify using `using h`.

Establish `hpow' : ∃ t : (GlobalTheory.UPel.HT.Hecke.lbPow (M.pull φ) k).Gen, t.IsGen`. Use `(cls_eq_zero_iff (LB.isLB_linComb hM' _ _)).1 ?_` and prove the remaining obligations. Rewrite using `[cls_linComb hM']`. Simplify using `[pull_id, cls_pull hM φ, ← map_nsmul, hkM]`. Set `P : PrimeSpectrum R` to `p`.

Use `haveI : P.asIdeal.IsPrime := P.isPrime`. Set `F` to `AlgebraicClosure P.asIdeal.ResidueField`. Set `ψ : R →+* F` to `(algebraMap P.asIdeal.ResidueField F).comp (algebraMap R P.asIdeal.ResidueField)`. Establish `hfib' : ∃ t : ((M.pull φ).pull (pullback.fst A'.hom (spMap ψ))).Gen, t.IsGen`. Rewrite using `[key']`.

Establish `h0` using `(key _).1 (hfib F (spMap ψ ≫ j'))`. Establish `e : pullback.fst A'.hom (spMap ψ) ≫ φ = pullback.lift (pullback.fst A'.hom (spMap ψ) ≫ φ) (pullback.snd A'.hom (spMap ψ)) (by`. Establish `hc : pullback.fst A'.hom (spMap ψ) ≫ A'.hom = pullback.snd A'.hom (spMap ψ) ≫ spMap ψ` using `pullback.condition`. Rewrite using `[Category.assoc, pullback.condition, ← Category.assoc]`. Conclude with `(congrArg (· ≫ j') hc).trans (Category.assoc _ _ _))`.

Use the proof step `≫ pullback.fst A.hom (spMap ψ ≫ j') := (pullback.lift_fst _ _ _).symm`. Rewrite using `[e, pull_comp, h0, map_zero]`. Take `⟨r, hr, ht⟩` from `GlobalTheory.T.localTriviality_of_noetherian_descent (GlobalTheory.T.torsionLineBundle_trivial_basicOpen_of_trivial_fibre GlobalTheory.T.exists_generator_torsion_bundle_abelianScheme_sqZero) R A' hA' (M.pull φ) hM' hrig' k hk' hpow' F ψ hfib'`. Establish `hrp : P ∈ PrimeSpectrum.basicOpen r`. Introduce `hm`.

Apply `hr` to reduce the goal to its premises. Use `show algebraMap _ F (algebraMap R P.asIdeal.ResidueField r) = 0`. Rewrite using `[(Ideal.algebraMap_residueField_eq_zero).2 hm, map_zero]`. Use `⟨j' ''ᵁ PrimeSpectrum.basicOpen r, ⟨p, hrp, hp⟩, ?_⟩` and prove the remaining obligations. Use `(key _).2 ?_` and prove the remaining obligations.

Set `D : (Sp R).Opens` to `PrimeSpectrum.basicOpen r`. Set `W` to `A.hom ⁻¹ᵁ (j' ''ᵁ D)`. Establish `h1 : Set.range (W.ι ≫ A.hom) ⊆ Set.range j'`. Introduce and unpack `_ ⟨y, rfl⟩`. Take `⟨q, -, hq⟩` from `y.2`.

Conclude with `⟨q, hq⟩`. Set `m : W.toScheme ⟶ A'.left` to `pullback.lift W.ι (IsOpenImmersion.lift j' (W.ι ≫ A.hom) h1) (IsOpenImmersion.lift_fac _ _ _).symm`. Establish `h2 : Set.range m ⊆ Set.range (A'.hom ⁻¹ᵁ D).ι`. Introduce and unpack `_ ⟨y, rfl⟩`. Rewrite using `[Scheme.Opens.range_ι]`.

Establish `e : m ≫ A'.hom = IsOpenImmersion.lift j' (W.ι ≫ A.hom) h1` using `pullback.lift_snd _ _ _`. Use `show (m ≫ A'.hom) y ∈ D`. Rewrite using `[e]`. Take `⟨q, hqD, hq⟩` from `y.2`. Establish `: IsOpenImmersion.lift j' (W.ι ≫ A.hom) h1 y = q` using `j'.isOpenEmbedding.injective (by`.

Rewrite using `[← Scheme.Hom.comp_apply, IsOpenImmersion.lift_fac]`. Conclude with `hq.symm)`. Rewrite using `[this]`. Conclude with `hqD`. Establish `hfac : W.ι = IsOpenImmersion.lift (A'.hom ⁻¹ᵁ D).ι m h2 ≫ (A'.hom ⁻¹ᵁ D).ι ≫ φ`.

Rewrite using `[← Category.assoc, IsOpenImmersion.lift_fac]`. Conclude with `(pullback.lift_fst _ _ _).symm`. Rewrite using `[hfac, pull_comp, (key' _).1 ht, map_zero]`.
-/
theorem triv_of_geometricFibres : ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A] [IsCommMonObj A], IsAbelianScheme A → ∀ (M : LB A.left), M.IsLB → (∃ t : (M.pull (1 : 𝟙_ (Over S) ⟶ A).left).Gen, t.IsGen) → ∀ k : ℕ, IsUnit ((k : Γ(S, ⊤))) → (∃ t : (GlobalTheory.UPel.HT.Hecke.lbPow M k).Gen, t.IsGen) → (∀ (K : Type) [Field K] [IsAlgClosed K] (y : Sp K ⟶ S), ∃ t : (M.pull (pullback.fst A.hom y)).Gen, t.IsGen) → ∃ t : M.Gen, t.IsGen := by
  intro S A _ _ hA M hM hrig k hk hpow hfib
  have key : ∀ {Y : Scheme.{0}} (f : Y ⟶ A.left), (∃ t : (M.pull f).Gen, t.IsGen) ↔ pull f (cls M hM) = 0 :=
    fun f => (cls_eq_zero_iff (pull_isLB hM f)).symm.trans (by rw [cls_pull hM f])
  have hsurj : ∀ V : S.Opens, Function.Surjective (A.hom ∣_ V).appTop.hom := fun V => by
    have hG : Out.GlobalFnsSt := GlobalTheory.abelianSchemeLaws_all.1.globalFns
    have h1 := hG _ _ (Out.TLinPf.isAb_pullback V.ι A hA)
    let e := IsPullback.isoIsPullback _ _ (isPullback_morphismRestrict A.hom V)
      (IsPullback.of_hasPullback A.hom V.ι).flip
    have he : e.hom ≫ pullback.snd A.hom V.ι = A.hom ∣_ V := IsPullback.isoIsPullback_hom_fst _ _ _ _
    have hi : Function.Surjective e.hom.appTop.hom := by
      have : IsIso (e.hom.app ⊤) := inferInstance
      exact (ConcreteCategory.bijective_of_isIso (e.hom.app ⊤)).2
    rw [← he, Scheme.Hom.comp_appTop, CommRingCat.hom_comp]
    exact hi.comp h1.2
  have hc0 : pull (1 : 𝟙_ (Over S) ⟶ A).left (cls M hM) = 0 := (key _).1 hrig
  have hkM : k • cls M hM = 0 := by
    have h := (cls_eq_zero_iff (LB.isLB_linComb hM _ _)).2 hpow
    rw [cls_linComb hM] at h
    simpa [pull_id] using h
  refine GlobalTheory.CubeGlue.triv_of_locally_triv hM A.hom (1 : 𝟙_ (Over S) ⟶ A).left
    (by simpa using Over.w (1 : 𝟙_ (Over S) ⟶ A)) hsurj hrig ?_
  intro s
  obtain ⟨R, j, hj, ⟨p, hp⟩, -⟩ := Scheme.exists_affine_mem_range_and_range_subset (x := s) (U := ⊤) trivial
  let j' : Sp R ⟶ S := j
  haveI : IsOpenImmersion j' := hj
  let A' := (Over.pullback j').obj A
  have hA' : IsAbelianScheme A' := Out.TLinPf.isAb_pullback j' A hA
  let φ := pullback.fst A.hom j'
  have hM' : (M.pull φ).IsLB := pull_isLB hM φ
  have key' : ∀ {Y : Scheme.{0}} (f : Y ⟶ A'.left),
      (∃ t : ((M.pull φ).pull f).Gen, t.IsGen) ↔ pull (f ≫ φ) (cls M hM) = 0 := fun f =>
    (cls_eq_zero_iff (pull_isLB hM' f)).symm.trans (by rw [cls_pull hM' f, cls_pull hM φ, pull_comp])
  have hone : (1 : 𝟙_ (Over (Sp R)) ⟶ A').left ≫ φ = j' ≫ (1 : 𝟙_ (Over S) ⟶ A).left := by
    have h := GlobalTheory.TorsFrameInt.one_comm (isGrpPullback_pullback A j')
    rw [Hom.one_def, Hom.one_def]
    simpa using h
  have hrig' := (key' _).2 (by rw [hone, pull_comp, hc0, map_zero])
  have hk' : IsUnit (k : R) := by
    have h := hk.map ((Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom.comp j'.appTop.hom)
    simpa using h
  have hpow' : ∃ t : (GlobalTheory.UPel.HT.Hecke.lbPow (M.pull φ) k).Gen, t.IsGen := by
    refine (cls_eq_zero_iff (LB.isLB_linComb hM' _ _)).1 ?_
    rw [cls_linComb hM']
    simp [pull_id, cls_pull hM φ, ← map_nsmul, hkM]
  let P : PrimeSpectrum R := p
  haveI : P.asIdeal.IsPrime := P.isPrime
  let F := AlgebraicClosure P.asIdeal.ResidueField
  let ψ : R →+* F := (algebraMap P.asIdeal.ResidueField F).comp (algebraMap R P.asIdeal.ResidueField)
  have hfib' : ∃ t : ((M.pull φ).pull (pullback.fst A'.hom (spMap ψ))).Gen, t.IsGen := by
    rw [key']
    have h0 := (key _).1 (hfib F (spMap ψ ≫ j'))
    have e : pullback.fst A'.hom (spMap ψ) ≫ φ =
        pullback.lift (pullback.fst A'.hom (spMap ψ) ≫ φ) (pullback.snd A'.hom (spMap ψ))
          (by
            have hc : pullback.fst A'.hom (spMap ψ) ≫ A'.hom = pullback.snd A'.hom (spMap ψ) ≫ spMap ψ :=
              pullback.condition
            rw [Category.assoc, pullback.condition, ← Category.assoc]
            exact (congrArg (· ≫ j') hc).trans (Category.assoc _ _ _))
          ≫ pullback.fst A.hom (spMap ψ ≫ j') := (pullback.lift_fst _ _ _).symm
    rw [e, pull_comp, h0, map_zero]
  obtain ⟨r, hr, ht⟩ := GlobalTheory.T.localTriviality_of_noetherian_descent (GlobalTheory.T.torsionLineBundle_trivial_basicOpen_of_trivial_fibre GlobalTheory.T.exists_generator_torsion_bundle_abelianScheme_sqZero) R A' hA' (M.pull φ) hM' hrig' k hk' hpow' F ψ hfib'
  have hrp : P ∈ PrimeSpectrum.basicOpen r := by
    intro hm
    apply hr
    show algebraMap _ F (algebraMap R P.asIdeal.ResidueField r) = 0
    rw [(Ideal.algebraMap_residueField_eq_zero).2 hm, map_zero]
  refine ⟨j' ''ᵁ PrimeSpectrum.basicOpen r, ⟨p, hrp, hp⟩, ?_⟩
  refine (key _).2 ?_
  let D : (Sp R).Opens := PrimeSpectrum.basicOpen r
  let W := A.hom ⁻¹ᵁ (j' ''ᵁ D)
  have h1 : Set.range (W.ι ≫ A.hom) ⊆ Set.range j' := by
    rintro _ ⟨y, rfl⟩
    obtain ⟨q, -, hq⟩ := y.2
    exact ⟨q, hq⟩
  let m : W.toScheme ⟶ A'.left :=
    pullback.lift W.ι (IsOpenImmersion.lift j' (W.ι ≫ A.hom) h1) (IsOpenImmersion.lift_fac _ _ _).symm
  have h2 : Set.range m ⊆ Set.range (A'.hom ⁻¹ᵁ D).ι := by
    rintro _ ⟨y, rfl⟩
    rw [Scheme.Opens.range_ι]
    have e : m ≫ A'.hom = IsOpenImmersion.lift j' (W.ι ≫ A.hom) h1 := pullback.lift_snd _ _ _
    show (m ≫ A'.hom) y ∈ D
    rw [e]
    obtain ⟨q, hqD, hq⟩ := y.2
    have : IsOpenImmersion.lift j' (W.ι ≫ A.hom) h1 y = q := j'.isOpenEmbedding.injective (by
      rw [← Scheme.Hom.comp_apply, IsOpenImmersion.lift_fac]; exact hq.symm)
    rw [this]; exact hqD
  have hfac : W.ι = IsOpenImmersion.lift (A'.hom ⁻¹ᵁ D).ι m h2 ≫ (A'.hom ⁻¹ᵁ D).ι ≫ φ := by
    rw [← Category.assoc, IsOpenImmersion.lift_fac]; exact (pullback.lift_fst _ _ _).symm
  rw [hfac, pull_comp, (key' _).1 ht, map_zero]

end GlobalTheory.RigTorsTriv

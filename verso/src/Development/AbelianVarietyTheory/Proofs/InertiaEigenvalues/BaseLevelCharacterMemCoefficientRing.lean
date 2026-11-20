import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnivChar
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LevelCharacterApplyEqLevelFunctionSwap
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ToUnitsCompToCircle
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TwistingCharValuesMemCoeffFieldRange
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ThetaTranslateRangeGap
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie GlobalTheory.TwInputs GlobalTheory.TwSys GlobalTheory.TwAll GlobalTheory.SupLaw GlobalTheory.LiftLeaf
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ HkIdx V0 Fm0 FullRk SgJ BasisOf)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1600000
noncomputable section

namespace GlobalTheory.LamVal

/- English proof (translation)
Establish `hi : IsIntegral A a` using `⟨Polynomial.X ^ n - Polynomial.C 1, Polynomial.monic_X_pow_sub_C 1 hn, by simp [h]⟩`. Conclude with `IsIntegrallyClosed.isIntegral_iff.1 hi`.
-/
theorem exists_of_pow {A : Type} [CommRing A] [IsDomain A] [IsIntegrallyClosed A] {a : FractionRing A} {n : ℕ}
    (hn : n ≠ 0) (h : a ^ n = 1) : ∃ y : A, algebraMap A (FractionRing A) y = a := by
  have hi : IsIntegral A a := ⟨Polynomial.X ^ n - Polynomial.C 1, Polynomial.monic_X_pow_sub_C 1 hn, by simp [h]⟩
  exact IsIntegrallyClosed.isIntegral_iff.1 hi

variable {D : D7}

/- English proof (translation)
Take `⟨y, rfl⟩` from `exists_of_pow hn h`. Conclude with `⟨algebraMap _ _ y, hρ.ek_e i b 0 y⟩`.
-/
theorem e_mem_of_pow {ρ : Setup D.ntw} (hρ : ρ.Good) (i : D.ntw.Tw) (b : Bool) {a : FractionRing (D.ntw.O i)} {n : ℕ}
    (hn : n ≠ 0) (h : a ^ n = 1) : ρ.e i b a ∈ (ρ.eOk i b 0).range := by
  obtain ⟨y, rfl⟩ := exists_of_pow hn h
  exact ⟨algebraMap _ _ y, hρ.ek_e i b 0 y⟩

/- English proof (translation)
Take `⟨σ, hσ⟩` from `ρ.rc.exists_sym z`. Establish `hopen : IsOpen ((Formalism.MainNotions.BlochKatoReduction.Gen.psiAt b (D.ntw.delta i)).ker : Set (G D.host.E D.nd.Om))`. Establish `e : (Formalism.MainNotions.BlochKatoReduction.Gen.psiAt b (D.ntw.delta i)).ker = (D.ntw.delta i).ker`. Use extensionality with `g`. Apply the tactic sequence `cases b <;> simp [Formalism.MainNotions.BlochKatoReduction.Gen.psiAt, MonoidHom.mem_ker]`.

Rewrite using `[e]`. Conclude with `D.ntw.delta_open i`. Establish `: Finite (G D.host.E D.nd.Om ⧸ (Formalism.MainNotions.BlochKatoReduction.Gen.psiAt b (D.ntw.delta i)).ker)` using `Subgroup.quotient_finite_of_isOpen _ hopen`. Establish `hfi : (Formalism.MainNotions.BlochKatoReduction.Gen.psiAt b (D.ntw.delta i)).ker.FiniteIndex` using `Subgroup.finiteIndex_of_finite_quotient`. Establish `hn : (Formalism.MainNotions.BlochKatoReduction.Gen.psiAt b (D.ntw.delta i)).ker.index ≠ 0` using `Subgroup.FiniteIndex.index_ne_zero`.

Establish `hpow : Formalism.MainNotions.BlochKatoReduction.Gen.psiAt b (D.ntw.delta i) σ ^ (Formalism.MainNotions.BlochKatoReduction.Gen.psiAt b (D.ntw.delta i)).ker.index = 1`. Rewrite using `[← map_pow]`. Conclude with `MonoidHom.mem_ker.1 (Subgroup.pow_index_mem _ σ)`. Use `⟨algebraMap (D.ntw.O i) (D.ntw.Ok i 0) (algebraMap (D.ntw.O0 i) (D.ntw.O i) ((Formalism.MainNotions.BlochKatoReduction.Gen.psiAt b (D.ntw.delta i) σ : (D.ntw.O0 i)ˣ) : D.ntw.O0 i)), ?_⟩` and prove the remaining obligations. Rewrite using `[hρ.ek_e, hρ.delta i j b]`.

Conclude with `(charOf_eq ρ.rc ((ρ.eO i b).comp (algebraMap (D.ntw.O0 i) (D.ntw.O i))) hopen hσ hn hpow).symm`.
-/
theorem de_mem {ρ : Setup D.ntw} (hρ : ρ.Good) (i : D.ntw.Tw) (j : Fin D.R.m) (b : Bool) (z : (AE D)ˣ) :
    (((ρ.B i j b).de.chi z : Circle) : ℂ) ∈ (ρ.eOk i b 0).range := by
  obtain ⟨σ, hσ⟩ := ρ.rc.exists_sym z
  have hopen : IsOpen ((Formalism.MainNotions.BlochKatoReduction.Gen.psiAt b (D.ntw.delta i)).ker : Set (G D.host.E D.nd.Om)) := by
    have e : (Formalism.MainNotions.BlochKatoReduction.Gen.psiAt b (D.ntw.delta i)).ker = (D.ntw.delta i).ker := by
      ext g
      cases b <;> simp [Formalism.MainNotions.BlochKatoReduction.Gen.psiAt, MonoidHom.mem_ker]
    rw [e]
    exact D.ntw.delta_open i
  have : Finite (G D.host.E D.nd.Om ⧸ (Formalism.MainNotions.BlochKatoReduction.Gen.psiAt b (D.ntw.delta i)).ker) :=
    Subgroup.quotient_finite_of_isOpen _ hopen
  have hfi : (Formalism.MainNotions.BlochKatoReduction.Gen.psiAt b (D.ntw.delta i)).ker.FiniteIndex := Subgroup.finiteIndex_of_finite_quotient
  have hn : (Formalism.MainNotions.BlochKatoReduction.Gen.psiAt b (D.ntw.delta i)).ker.index ≠ 0 := Subgroup.FiniteIndex.index_ne_zero
  have hpow : Formalism.MainNotions.BlochKatoReduction.Gen.psiAt b (D.ntw.delta i) σ ^ (Formalism.MainNotions.BlochKatoReduction.Gen.psiAt b (D.ntw.delta i)).ker.index = 1 := by
    rw [← map_pow]
    exact MonoidHom.mem_ker.1 (Subgroup.pow_index_mem _ σ)
  refine ⟨algebraMap (D.ntw.O i) (D.ntw.Ok i 0)
    (algebraMap (D.ntw.O0 i) (D.ntw.O i) ((Formalism.MainNotions.BlochKatoReduction.Gen.psiAt b (D.ntw.delta i) σ : (D.ntw.O0 i)ˣ) : D.ntw.O0 i)), ?_⟩
  rw [hρ.ek_e, hρ.delta i j b]
  exact (charOf_eq ρ.rc ((ρ.eO i b).comp (algebraMap (D.ntw.O0 i) (D.ntw.O i))) hopen hσ hn hpow).symm

end GlobalTheory.LamVal

namespace GlobalTheory.LamVal

variable {D : D7} {X : RealSide D} {E : IntegralHeckeForms.XD D}

/- English proof (translation)
Unfold `ext1`. Use `split_ifs with h`. Use `set g' := (Y.Z.ρ.eG i j b).symm g with hg'`. Establish `hg : Y.Z.ρ.eG i j b g' = g` using `MulEquiv.apply_symm_apply _ _`. Establish `h' : Y.Z.ρ.eG i j b g' ∈ (Y.Z.ρ.B i j b).G.P.H` using `by rw [hg]; exact h`.

Establish `hu : g' ∈ D.nexp.U` using `((Y.Z.tie i j b).U_eq g').1 h'`. Establish `e1` using `(Y.Z.tie i j b).psiU_eq ⟨g', hu⟩ h'`. Establish `e2 : (Y.Z.ρ.B i j b).G.P.chi ⟨g, h⟩ = (Y.Z.ρ.B i j b).G.P.chi ⟨Y.Z.ρ.eG i j b g', h'⟩`. Use `congr 1`. Conclude with `Subtype.ext hg.symm`.

Rewrite using `[e2, e1]`. Establish `hfin : ((Y.Z.ρ.B i j b).G.P.chi ⟨Y.Z.ρ.eG i j b g', h'⟩) ^ Nat.card (Y.Z.ρ.B i j b).G.P.H = 1`. Rewrite using `[← map_pow, pow_card_eq_one', map_one]`. Use `e_mem_of_pow Y.Z.good i b (n := Nat.card (Y.Z.ρ.B i j b).G.P.H) Nat.card_pos.ne' ?_` and prove the remaining obligations. Apply `(Y.Z.ρ.e i b).injective` to reduce the goal to its premises.

Rewrite using `[map_pow, ← e1, ← Units.val_pow_eq_pow_val, hfin, Units.val_one, map_one]`. Conclude with `one_mem _`.
-/
theorem typeCharacterExtension_mem_range_coefficientRing (Y : SerSide X E) (i : D.ntw.Tw) (j : Fin D.R.m) (b : Bool)
    (g : G0 (Y.Z.ρ.B i j b).G.Pg (Wc D j).rank) :
    ((ext1 (Y.Z.ρ.B i j b).G.P.H (⇑(Y.Z.ρ.B i j b).G.P.chi) g : ℂˣ) : ℂ) ∈ (Y.Z.ρ.eOk i b 0).range := by
  unfold ext1
  split_ifs with h
  · set g' := (Y.Z.ρ.eG i j b).symm g with hg'
    have hg : Y.Z.ρ.eG i j b g' = g := MulEquiv.apply_symm_apply _ _
    have h' : Y.Z.ρ.eG i j b g' ∈ (Y.Z.ρ.B i j b).G.P.H := by rw [hg]; exact h
    have hu : g' ∈ D.nexp.U := ((Y.Z.tie i j b).U_eq g').1 h'
    have e1 := (Y.Z.tie i j b).psiU_eq ⟨g', hu⟩ h'
    have e2 : (Y.Z.ρ.B i j b).G.P.chi ⟨g, h⟩ = (Y.Z.ρ.B i j b).G.P.chi ⟨Y.Z.ρ.eG i j b g', h'⟩ := by
      congr 1
      exact Subtype.ext hg.symm
    rw [e2, e1]
    have hfin : ((Y.Z.ρ.B i j b).G.P.chi ⟨Y.Z.ρ.eG i j b g', h'⟩) ^ Nat.card (Y.Z.ρ.B i j b).G.P.H = 1 := by
      rw [← map_pow, pow_card_eq_one', map_one]
    refine e_mem_of_pow Y.Z.good i b (n := Nat.card (Y.Z.ρ.B i j b).G.P.H) Nat.card_pos.ne' ?_
    apply (Y.Z.ρ.e i b).injective
    rw [map_pow, ← e1, ← Units.val_pow_eq_pow_val, hfin, Units.val_one, map_one]
  · exact one_mem _

/- English proof (translation)
Establish `hB` using `Y.Z.good.base i j b`. Take `⟨P, hPg, -, hsp⟩` from `hB.places.split`. Take `⟨x, hx⟩` from `GlobalTheory.ConjTwist.exists_isLocUnit (hsp.isIdemAt (hPg hPP)) w`. Establish `e1 : (Y.Z.ρ.B i j b).G.mu PP w = (Y.Z.ρ.B i j b).mu x` using `(hx.eq (hB.tame PP hPP)).symm`. Use `show (((Y.Z.ρ.B i j b).G.mu PP w : Circle) : ℂ) ∈ _`.

Rewrite using `[e1, Base.mu, MonoidHom.mul_apply, Circle.coe_mul]`. Conclude with `mul_mem (hμ PP hPP w x hx) (de_mem Y.Z.good i j b x)`.
-/
theorem mu_mem (Y : SerSide X E) (i : D.ntw.Tw) (j : Fin D.R.m) (b : Bool)
    (hμ : ∀ PP ∈ (Y.Z.ρ.B i j b).G.Pg, ∀ (u : (kP PP)ˣ) (x : (AE D)ˣ), GlobalTheory.ConjTwist.IsLocUnit PP u x →
      (((Y.Z.ρ.B i j b).mu0 x : Circle) : ℂ) ∈ (Y.Z.ρ.eOk i b 0).range)
    {PP : Pl D.host.E} (hPP : PP ∈ (Y.Z.ρ.B i j b).G.Pg) (w : (kP PP)ˣ) :
    (((Y.Z.ρ.B i j b).G.muC PP w : ℂˣ) : ℂ) ∈ (Y.Z.ρ.eOk i b 0).range := by
  have hB := Y.Z.good.base i j b
  obtain ⟨P, hPg, -, hsp⟩ := hB.places.split
  obtain ⟨x, hx⟩ := GlobalTheory.ConjTwist.exists_isLocUnit (hsp.isIdemAt (hPg hPP)) w
  have e1 : (Y.Z.ρ.B i j b).G.mu PP w = (Y.Z.ρ.B i j b).mu x := (hx.eq (hB.tame PP hPP)).symm
  show (((Y.Z.ρ.B i j b).G.mu PP w : Circle) : ℂ) ∈ _
  rw [e1, Base.mu, MonoidHom.mul_apply, Circle.coe_mul]
  exact mul_mem (hμ PP hPP w x hx) (de_mem Y.Z.good i j b x)

/- English proof (translation)
Establish `hψ : (Y.Z.ρ.tw i b 0 ∅ 1).locC PP = 1`. Simplify using `[Twist.locC, Setup.tw, twistOf, half_empty]`. Rewrite using `[hψ, mul_one]`. Unfold `Twist.locC`. Use `split_ifs with hq`.

Establish `hB` using `Y.Z.good.base i j b`. Take `⟨P, -, hQ, hsp⟩` from `hB.places.split`. Take `⟨x, hx⟩` from `GlobalTheory.ConjTwist.exists_isLocUnit (hsp.isIdemAt (hQ hq)) w`. Use `show (((Y.Z.ρ.B i j b).de.res PP w : Circle) : ℂ) ∈ _`. Rewrite using `[← hx.eq (hB.de.res PP hq)]`.

Conclude with `de_mem Y.Z.good i j b x`. Simplify using the standard rewrite rules.
-/
theorem loc_mem (Y : SerSide X E) (i : D.ntw.Tw) (j : Fin D.R.m) (b : Bool) (PP : Pl D.host.E) (w : (kP PP)ˣ) :
    ((((Y.Z.ρ.B i j b).de.locC PP * (Y.Z.ρ.tw i b 0 ∅ 1).locC PP) w : ℂˣ) : ℂ) ∈ (Y.Z.ρ.eOk i b 0).range := by
  have hψ : (Y.Z.ρ.tw i b 0 ∅ 1).locC PP = 1 := by
    simp [Twist.locC, Setup.tw, twistOf, half_empty]
  rw [hψ, mul_one]
  unfold Twist.locC
  split_ifs with hq
  · have hB := Y.Z.good.base i j b
    obtain ⟨P, -, hQ, hsp⟩ := hB.places.split
    obtain ⟨x, hx⟩ := GlobalTheory.ConjTwist.exists_isLocUnit (hsp.isIdemAt (hQ hq)) w
    show (((Y.Z.ρ.B i j b).de.res PP w : Circle) : ℂ) ∈ _
    rw [← hx.eq (hB.de.res PP hq)]
    exact de_mem Y.Z.good i j b x
  · simp

end GlobalTheory.LamVal

namespace GlobalTheory.LamVal

/- English proof (translation)
Introduce `D X E Y i j b hμ k`. Rewrite using `[GlobalTheory.MtLatConj.levelCharacter_apply_eq_levelFunction_swap]`. Simplify using `only [levFn, Base.levS, Units.val_mul, Units.coe_prod]`. Conclude with `mul_mem (mul_mem (typeCharacterExtension_mem_range_coefficientRing Y i j b _) (prod_mem fun PP hPP => prod_mem fun _ _ => mu_mem Y i j b hμ hPP _)) (prod_mem fun PP _ => loc_mem Y i j b PP _)`.
-/
theorem levLam_mem : ∀ (D : D7) (X : RealSide D) (E : IntegralHeckeForms.XD D) (Y : SerSide X E) (i : D.ntw.Tw) (j : Fin D.R.m) (b : Bool),
    (∀ PP ∈ (Y.Z.ρ.B i j b).G.Pg, ∀ (u : (kP PP)ˣ) (x : (AE D)ˣ), GlobalTheory.ConjTwist.IsLocUnit PP u x →
      (((Y.Z.ρ.B i j b).mu0 x : Circle) : ℂ) ∈ (Y.Z.ρ.eOk i b 0).range) →
    ∀ (k : (Y.Z.ρ.B i j b).levJ (Y.Z.ρ.tw i b 0 ∅ 1)),
      (((Y.Z.ρ.B i j b).levLam (Y.Z.ρ.tw i b 0 ∅ 1) k : ℂˣ) : ℂ) ∈ (Y.Z.ρ.eOk i b 0).range := by
  intro D X E Y i j b hμ k
  rw [GlobalTheory.MtLatConj.levelCharacter_apply_eq_levelFunction_swap]
  simp only [levFn, Base.levS, Units.val_mul, Units.coe_prod]
  exact mul_mem (mul_mem (typeCharacterExtension_mem_range_coefficientRing Y i j b _) (prod_mem fun PP hPP => prod_mem fun _ _ => mu_mem Y i j b hμ hPP _))
    (prod_mem fun PP _ => loc_mem Y i j b PP _)

variable {D : D7} {X : RealSide D} {E : IntegralHeckeForms.XD D}

/- English proof (translation)
Take `⟨σ, hσ⟩` from `ρ.rc.exists_sym z`. Establish `hopen : IsOpen ((Formalism.MainNotions.BlochKatoReduction.Gen.psiAt b (D.ntw.delta i)).ker : Set (G D.host.E D.nd.Om))`. Establish `e : (Formalism.MainNotions.BlochKatoReduction.Gen.psiAt b (D.ntw.delta i)).ker = (D.ntw.delta i).ker`. Use extensionality with `g`. Apply the tactic sequence `cases b <;> simp [Formalism.MainNotions.BlochKatoReduction.Gen.psiAt, MonoidHom.mem_ker]`.

Rewrite using `[e]`. Conclude with `D.ntw.delta_open i`. Establish `: Finite (G D.host.E D.nd.Om ⧸ (Formalism.MainNotions.BlochKatoReduction.Gen.psiAt b (D.ntw.delta i)).ker)` using `Subgroup.quotient_finite_of_isOpen _ hopen`. Establish `hfi : (Formalism.MainNotions.BlochKatoReduction.Gen.psiAt b (D.ntw.delta i)).ker.FiniteIndex` using `Subgroup.finiteIndex_of_finite_quotient`. Establish `hn : (Formalism.MainNotions.BlochKatoReduction.Gen.psiAt b (D.ntw.delta i)).ker.index ≠ 0` using `Subgroup.FiniteIndex.index_ne_zero`.

Establish `hpow : Formalism.MainNotions.BlochKatoReduction.Gen.psiAt b (D.ntw.delta i) σ ^ (Formalism.MainNotions.BlochKatoReduction.Gen.psiAt b (D.ntw.delta i)).ker.index = 1`. Rewrite using `[← map_pow]`. Conclude with `MonoidHom.mem_ker.1 (Subgroup.pow_index_mem _ σ)`. Use `⟨algebraMap (D.ntw.O i) _ (algebraMap (D.ntw.O0 i) (D.ntw.O i) ((Formalism.MainNotions.BlochKatoReduction.Gen.psiAt b (D.ntw.delta i) σ : (D.ntw.O0 i)ˣ) : D.ntw.O0 i)), ?_⟩` and prove the remaining obligations. Rewrite using `[hρ.delta i j b]`.

Conclude with `(charOf_eq ρ.rc ((ρ.eO i b).comp (algebraMap (D.ntw.O0 i) (D.ntw.O i))) hopen hσ hn hpow).symm`.
-/
theorem de_frac {ρ : Setup D.ntw} (hρ : ρ.Good) (i : D.ntw.Tw) (j : Fin D.R.m) (b : Bool) (z : (AE D)ˣ) :
    ∃ d, ρ.e i b d = (((ρ.B i j b).de.chi z : Circle) : ℂ) := by
  obtain ⟨σ, hσ⟩ := ρ.rc.exists_sym z
  have hopen : IsOpen ((Formalism.MainNotions.BlochKatoReduction.Gen.psiAt b (D.ntw.delta i)).ker : Set (G D.host.E D.nd.Om)) := by
    have e : (Formalism.MainNotions.BlochKatoReduction.Gen.psiAt b (D.ntw.delta i)).ker = (D.ntw.delta i).ker := by
      ext g
      cases b <;> simp [Formalism.MainNotions.BlochKatoReduction.Gen.psiAt, MonoidHom.mem_ker]
    rw [e]
    exact D.ntw.delta_open i
  have : Finite (G D.host.E D.nd.Om ⧸ (Formalism.MainNotions.BlochKatoReduction.Gen.psiAt b (D.ntw.delta i)).ker) :=
    Subgroup.quotient_finite_of_isOpen _ hopen
  have hfi : (Formalism.MainNotions.BlochKatoReduction.Gen.psiAt b (D.ntw.delta i)).ker.FiniteIndex := Subgroup.finiteIndex_of_finite_quotient
  have hn : (Formalism.MainNotions.BlochKatoReduction.Gen.psiAt b (D.ntw.delta i)).ker.index ≠ 0 := Subgroup.FiniteIndex.index_ne_zero
  have hpow : Formalism.MainNotions.BlochKatoReduction.Gen.psiAt b (D.ntw.delta i) σ ^ (Formalism.MainNotions.BlochKatoReduction.Gen.psiAt b (D.ntw.delta i)).ker.index = 1 := by
    rw [← map_pow]
    exact MonoidHom.mem_ker.1 (Subgroup.pow_index_mem _ σ)
  refine ⟨algebraMap (D.ntw.O i) _
    (algebraMap (D.ntw.O0 i) (D.ntw.O i) ((Formalism.MainNotions.BlochKatoReduction.Gen.psiAt b (D.ntw.delta i) σ : (D.ntw.O0 i)ˣ) : D.ntw.O0 i)), ?_⟩
  rw [hρ.delta i j b]
  exact (charOf_eq ρ.rc ((ρ.eO i b).comp (algebraMap (D.ntw.O0 i) (D.ntw.O i))) hopen hσ hn hpow).symm

/- English proof (translation)
Take `⟨y, hy⟩` from `X.valKs j x hx`. Use `⟨sideEmb D.ntw i b (Y.S.kKs ((Y.YS.fi j).eK.symm y)), ?_⟩` and prove the remaining obligations. Rewrite using `[Y.Z.good.e_LL0, Y.Z.pin.mu0 i j b]`. Use `Eq.trans ?_ hy.symm` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `D.what₂.embLL ((Y.S.kKs ((Y.YS.fi j).eK.symm y) : D.LL0) : D.what₂.LL) = _`.

Rewrite using `[Y.S.kKs_spec, ← (Y.YS.fi j).eK_LL, RingEquiv.apply_symm_apply]`.
-/
theorem baseCharacter_finiteIdeles_mem_range_fractionRing (Y : SerSide X E) (i : D.ntw.Tw) (j : Fin D.R.m) (b : Bool) (x : (AE D)ˣ) (hx : infPart D (x : AE D) = 1) :
    ∃ a, Y.Z.ρ.e i b a = (((Y.Z.ρ.B i j b).mu0 x : Circle) : ℂ) := by
  obtain ⟨y, hy⟩ := X.valKs j x hx
  refine ⟨sideEmb D.ntw i b (Y.S.kKs ((Y.YS.fi j).eK.symm y)), ?_⟩
  rw [Y.Z.good.e_LL0, Y.Z.pin.mu0 i j b]
  refine Eq.trans ?_ hy.symm
  change D.what₂.embLL ((Y.S.kKs ((Y.YS.fi j).eK.symm y) : D.LL0) : D.what₂.LL) = _
  rw [Y.S.kKs_spec, ← (Y.YS.fi j).eK_LL, RingEquiv.apply_symm_apply]

/- English proof (translation)
Establish `hB` using `Y.Z.good.base i j b`. Take `⟨P, hPg, -, hsp⟩` from `hB.places.split`. Take `⟨x, hx⟩` from `GlobalTheory.ConjTwist.exists_isLocUnit (hsp.isIdemAt (hPg hPP)) w`. Establish `e1 : (Y.Z.ρ.B i j b).G.mu PP w = (Y.Z.ρ.B i j b).mu x` using `(hx.eq (hB.tame PP hPP)).symm`. Use `show (((Y.Z.ρ.B i j b).G.mu PP w : Circle) : ℂ) ∈ _`.

Take `⟨a, ha⟩` from `baseCharacter_finiteIdeles_mem_range_fractionRing Y i j b x hx.inf`. Take `⟨d, hd⟩` from `de_frac Y.Z.good i j b x`. Establish `e2 : (((Y.Z.ρ.B i j b).G.mu PP w : Circle) : ℂ) = Y.Z.ρ.e i b (a * d)`. Rewrite using `[e1, Base.mu, MonoidHom.mul_apply, Circle.coe_mul, map_mul, ha, hd]`. Use `haveI : Finite (kP PP)ˣ := inferInstance`.

Establish `hfin : ((Y.Z.ρ.B i j b).G.mu PP w) ^ Nat.card (kP PP)ˣ = 1`. Rewrite using `[← map_pow, pow_card_eq_one', map_one]`. Rewrite using `[e2]`. Use `e_mem_of_pow Y.Z.good i b (n := Nat.card (kP PP)ˣ) Nat.card_pos.ne' ?_` and prove the remaining obligations. Apply `(Y.Z.ρ.e i b).injective` to reduce the goal to its premises.

Rewrite using `[map_pow, ← e2, ← Circle.coe_pow, hfin, Circle.coe_one, map_one]`.
-/
theorem muC_mem (Y : SerSide X E) (i : D.ntw.Tw) (j : Fin D.R.m) (b : Bool)
    {PP : Pl D.host.E} (hPP : PP ∈ (Y.Z.ρ.B i j b).G.Pg) (w : (kP PP)ˣ) :
    (((Y.Z.ρ.B i j b).G.muC PP w : ℂˣ) : ℂ) ∈ (Y.Z.ρ.eOk i b 0).range := by
  have hB := Y.Z.good.base i j b
  obtain ⟨P, hPg, -, hsp⟩ := hB.places.split
  obtain ⟨x, hx⟩ := GlobalTheory.ConjTwist.exists_isLocUnit (hsp.isIdemAt (hPg hPP)) w
  have e1 : (Y.Z.ρ.B i j b).G.mu PP w = (Y.Z.ρ.B i j b).mu x := (hx.eq (hB.tame PP hPP)).symm
  show (((Y.Z.ρ.B i j b).G.mu PP w : Circle) : ℂ) ∈ _
  obtain ⟨a, ha⟩ := baseCharacter_finiteIdeles_mem_range_fractionRing Y i j b x hx.inf
  obtain ⟨d, hd⟩ := de_frac Y.Z.good i j b x
  have e2 : (((Y.Z.ρ.B i j b).G.mu PP w : Circle) : ℂ) = Y.Z.ρ.e i b (a * d) := by
    rw [e1, Base.mu, MonoidHom.mul_apply, Circle.coe_mul, map_mul, ha, hd]
  haveI : Finite (kP PP)ˣ := inferInstance
  have hfin : ((Y.Z.ρ.B i j b).G.mu PP w) ^ Nat.card (kP PP)ˣ = 1 := by
    rw [← map_pow, pow_card_eq_one', map_one]
  rw [e2]
  refine e_mem_of_pow Y.Z.good i b (n := Nat.card (kP PP)ˣ) Nat.card_pos.ne' ?_
  apply (Y.Z.ρ.e i b).injective
  rw [map_pow, ← e2, ← Circle.coe_pow, hfin, Circle.coe_one, map_one]

/- English proof (translation)
Introduce `D X E Y i j b k`. Rewrite using `[GlobalTheory.MtLatConj.levelCharacter_apply_eq_levelFunction_swap]`. Simplify using `only [levFn, Base.levS, Units.val_mul, Units.coe_prod]`. Conclude with `mul_mem (mul_mem (typeCharacterExtension_mem_range_coefficientRing Y i j b _) (prod_mem fun PP hPP => prod_mem fun _ _ => muC_mem Y i j b hPP _)) (prod_mem fun PP _ => loc_mem Y i j b PP _)`.
-/
theorem levLam_mem_coef : ∀ (D : D7) (X : RealSide D) (E : IntegralHeckeForms.XD D) (Y : SerSide X E) (i : D.ntw.Tw) (j : Fin D.R.m) (b : Bool)
    (k : (Y.Z.ρ.B i j b).levJ (Y.Z.ρ.tw i b 0 ∅ 1)),
    (((Y.Z.ρ.B i j b).levLam (Y.Z.ρ.tw i b 0 ∅ 1) k : ℂˣ) : ℂ) ∈ (Y.Z.ρ.eOk i b 0).range := by
  intro D X E Y i j b k
  rw [GlobalTheory.MtLatConj.levelCharacter_apply_eq_levelFunction_swap]
  simp only [levFn, Base.levS, Units.val_mul, Units.coe_prod]
  exact mul_mem (mul_mem (typeCharacterExtension_mem_range_coefficientRing Y i j b _) (prod_mem fun PP hPP => prod_mem fun _ _ => muC_mem Y i j b hPP _))
    (prod_mem fun PP _ => loc_mem Y i j b PP _)

end GlobalTheory.LamVal

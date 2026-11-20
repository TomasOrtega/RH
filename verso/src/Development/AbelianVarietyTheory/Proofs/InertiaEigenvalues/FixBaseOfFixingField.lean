import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FockOfApply
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FixesUntwistedTupleDataOfFixesSmallFieldStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RingAutFixingSmallFieldFixesDeltaValuesStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.FWT IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie GlobalTheory.TwInputs GlobalTheory.ConjTwist GlobalTheory.ChoiceRead
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ)
open Formalism.L2.Host (embLL0)
open Formalism.IndefR.RecTie (Used0)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000
open GlobalTheory.PlaceRead
open GlobalTheory.HeightCounting.Up (PrN)

namespace GlobalTheory.PlaceFix

/- English proof (translation)
Use `set ψ := Formalism.MainNotions.BlochKatoReduction.Gen.psiAt b (D.ntw.delta i) with hψ`. Establish `hopen : IsOpen (ψ.ker : Set (Formalism.ConjugateSelfDual.G D.host.E D.nd.Om))`. Establish `: ψ.ker = (D.ntw.delta i).ker`. Use extensionality with `σ`. Apply the tactic sequence `cases b <;> simp [hψ, Formalism.MainNotions.BlochKatoReduction.Gen.psiAt, MonoidHom.mem_ker]`.

Rewrite using `[this]`. Conclude with `D.ntw.delta_open i`. Use `haveI : ψ.ker.FiniteIndex := @Subgroup.finiteIndex_of_finite_quotient _ _ _ (Subgroup.quotient_finite_of_isOpen _ hopen)`. Establish `hpow : ∀ σ, ψ σ ^ ψ.ker.index = 1` using `fun σ => by`. Rewrite using `[← map_pow]`.

Conclude with `ψ.ker.pow_index_mem σ`. Take `⟨σ, hσ⟩` from `ρ.rc.exists_sym x`. Use `⟨σ, ?_⟩` and prove the remaining obligations. Rewrite using `[hρ.delta i j b]`. Conclude with `charOf_eq _ _ hopen hσ Subgroup.FiniteIndex.index_ne_zero (hpow σ)`.
-/
theorem de_chi_eq {D : D7} {ρ : Setup D.ntw} (hρ : ρ.Good) (i : D.ntw.Tw) (j : Fin D.R.m) (b : Bool) (x : (AE D)ˣ) :
    ∃ σ, (((ρ.B i j b).de.chi x : Circle) : ℂ) = ρ.eO i b (algebraMap (D.ntw.O0 i) (D.ntw.O i)
        ((Formalism.MainNotions.BlochKatoReduction.Gen.psiAt b (D.ntw.delta i) σ : (D.ntw.O0 i)ˣ) : D.ntw.O0 i)) := by
  set ψ := Formalism.MainNotions.BlochKatoReduction.Gen.psiAt b (D.ntw.delta i) with hψ
  have hopen : IsOpen (ψ.ker : Set (Formalism.ConjugateSelfDual.G D.host.E D.nd.Om)) := by
    have : ψ.ker = (D.ntw.delta i).ker := by
      ext σ
      cases b <;> simp [hψ, Formalism.MainNotions.BlochKatoReduction.Gen.psiAt, MonoidHom.mem_ker]
    rw [this]; exact D.ntw.delta_open i
  haveI : ψ.ker.FiniteIndex := @Subgroup.finiteIndex_of_finite_quotient _ _ _ (Subgroup.quotient_finite_of_isOpen _ hopen)
  have hpow : ∀ σ, ψ σ ^ ψ.ker.index = 1 := fun σ => by
    rw [← map_pow]; exact ψ.ker.pow_index_mem σ
  obtain ⟨σ, hσ⟩ := ρ.rc.exists_sym x
  refine ⟨σ, ?_⟩
  rw [hρ.delta i j b]
  exact charOf_eq _ _ hopen hσ Subgroup.FiniteIndex.index_ne_zero (hpow σ)

/- English proof (translation)
Introduce `hP D X X0 Y S YS Z c w j H τ hτ`. Establish `hC` using `X.char`. Establish `hτ' : ∀ z ∈ (embLL0 D).fieldRange, τ z = z`. Introduce and unpack `_ ⟨y, rfl⟩`. Conclude with `hτ y`.

Establish `hTie : TieIn X.core X.R.toRealDat X.geo.κ X.geo.v₀` using `⟨X.geo.fw.laws, X.geo.fw.alg_eq, X.geo.fw.kap, X.geo.fw.hv₀, X.geo.fw.chiR, X.geo.fw.x0⟩`. Establish `hFB : FixBase X.core X.R.toRealDat j τ` using `GlobalTheory.T.fixes_untwistedTupleData_of_fixes_smallField _ _ _ _ _ _ hP.rayF X.core X.R X.cG S YS X.F.lv2 X.geo.κ X.geo.v₀ X.geo.fw.laws ⟨hC.lev, hC.grp, hC.fam, hC.models, hC.chain, hC.thP⟩ ⟨X.geo.fw⟩ hTie H.field.galois H.field.vals H.field.ray H.field.roots j τ hτ'`. Use `⟨hFB, ?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `y`. Take `⟨σ, hσ⟩` from `de_chi_eq Z.good (c.twI w) j (c.sd w) y`.

Express the relevant statement in the definitionally equal form `τ (((Z.ρ.B _ j _).de.chi y : Circle) : ℂ) = _`. Rewrite using `[hσ]`. Use `GlobalTheory.T.ringAut_fixing_smallField_fixes_delta_values Z.ρ Z.good _ j _ (X.R.C.delAt (D.ntw.l (c.twI w))) (Z.pin.delta _ j _) ?_ τ hτ σ` and prove the remaining obligations. Unfold `Formalism.L2.Host.CharFrame.delAt`. Use `split_ifs`.

Use `exacts [H.field.vals.del', H.field.vals.del]`. Introduce and unpack `⟨q, hq⟩`. Take `⟨y, rfl⟩` from `(Z.ρ.eG (c.twI w) j (c.sd w)).surjective q`. Take `⟨g, rfl⟩` from `(X.R.eG.trans X.cG).surjective y`. Establish `hU : X.cG (X.R.eG g) ∈ D.nexp.U` using `((Z.tie (c.twI w) j (c.sd w)).U_eq _).1 hq`.

Establish `hg : g ∈ X.F.P0` using `(H.U_eq g).1 hU`. Establish `e1` using `(Z.tie (c.twI w) j (c.sd w)).psiU_eq ⟨_, hU⟩ hq`. Establish `e2` using `H.psi_eq (c.twI w) (c.sd w) ⟨g, hg⟩ hU`. Take `⟨y, hy⟩` from `H.pins.keep.levKs.1 ⟨g, hg⟩`. Establish `e3` using `e1.trans e2`.

Express the relevant statement in the definitionally equal form `τ ((((Z.ρ.B _ j _).G.P.chi ⟨_, hq⟩ : ℂˣ) : ℂ)) = _`. Establish `e4 : D.what₂.embLL (X.F.ψ0 ⟨g, hg⟩ : D.what₂.LLˣ) = embLL0 D (S.kKs ((YS.fi j).eK.symm y))`. Express the relevant statement in the definitionally equal form `_ = D.what₂.embLL ((S.kKs ((YS.fi j).eK.symm y) : ↥D.LL0) : D.what₂.LL)`. Rewrite using `[S.kKs_spec, ← (YS.fi j).eK_LL, RingEquiv.apply_symm_apply]`. Conclude with `congrArg _ hy.symm`.

Rewrite `e3` using `[e4]`. Use `(congrArg τ e3).trans (Eq.trans ?_ e3.symm)` and prove the remaining obligations. Rewrite using `[map_inv₀, hτ]`. Conclude with `(GlobalTheory.BigOn.Exp.TwConj.baseOf_of_realPin hC.lev Z.good Z.pin _ j _).fix_mu hC.lev (Z.good.base _ j _) hFB.chi`.
-/
theorem fix_at_place : PrN → ∀ (D : D7) (X : RealSide D) (X0 : BaseLevelRowSide D) (Y : GlobalTheory.Mem.R3.Read (A3 := X.A3) X.R.toRealDat X.F.lv2 X0) (S : NX.RatDat D.ntw) (YS : NX.NExpRealS X.R X.cG S) (Z : ExportTie YS X.geo.v₀) (c : NChoice D) (w : D.what₂.places.Pl) (j : Fin D.R.m) (H : AtPlace Y Z c w j),
  ∀ τ : ℂ ≃+* ℂ, (∀ a, τ (embLL0 D a) = embLL0 D a) → FixBase X.core X.R.toRealDat j τ ∧ FixDat (baseOf Z c w j) τ := by
  intro hP D X X0 Y S YS Z c w j H τ hτ
  have hC := X.char
  have hτ' : ∀ z ∈ (embLL0 D).fieldRange, τ z = z := by
    rintro _ ⟨y, rfl⟩
    exact hτ y
  have hTie : TieIn X.core X.R.toRealDat X.geo.κ X.geo.v₀ :=
    ⟨X.geo.fw.laws, X.geo.fw.alg_eq, X.geo.fw.kap, X.geo.fw.hv₀, X.geo.fw.chiR, X.geo.fw.x0⟩
  have hFB : FixBase X.core X.R.toRealDat j τ :=
    GlobalTheory.T.fixes_untwistedTupleData_of_fixes_smallField _ _ _ _ _ _ hP.rayF X.core X.R X.cG S YS X.F.lv2 X.geo.κ X.geo.v₀ X.geo.fw.laws
      ⟨hC.lev, hC.grp, hC.fam, hC.models, hC.chain, hC.thP⟩ ⟨X.geo.fw⟩ hTie H.field.galois
      H.field.vals H.field.ray H.field.roots j τ hτ'
  refine ⟨hFB, ?_, ?_, ?_⟩
  · intro y
    obtain ⟨σ, hσ⟩ := de_chi_eq Z.good (c.twI w) j (c.sd w) y
    change τ (((Z.ρ.B _ j _).de.chi y : Circle) : ℂ) = _
    rw [hσ]
    refine GlobalTheory.T.ringAut_fixing_smallField_fixes_delta_values Z.ρ Z.good _ j _ (X.R.C.delAt (D.ntw.l (c.twI w))) (Z.pin.delta _ j _) ?_ τ hτ σ
    unfold Formalism.L2.Host.CharFrame.delAt
    split_ifs
    exacts [H.field.vals.del', H.field.vals.del]
  · rintro ⟨q, hq⟩
    obtain ⟨y, rfl⟩ := (Z.ρ.eG (c.twI w) j (c.sd w)).surjective q
    obtain ⟨g, rfl⟩ := (X.R.eG.trans X.cG).surjective y
    have hU : X.cG (X.R.eG g) ∈ D.nexp.U := ((Z.tie (c.twI w) j (c.sd w)).U_eq _).1 hq
    have hg : g ∈ X.F.P0 := (H.U_eq g).1 hU
    have e1 := (Z.tie (c.twI w) j (c.sd w)).psiU_eq ⟨_, hU⟩ hq
    have e2 := H.psi_eq (c.twI w) (c.sd w) ⟨g, hg⟩ hU
    obtain ⟨y, hy⟩ := H.pins.keep.levKs.1 ⟨g, hg⟩
    have e3 := e1.trans e2
    change τ ((((Z.ρ.B _ j _).G.P.chi ⟨_, hq⟩ : ℂˣ) : ℂ)) = _
    have e4 : D.what₂.embLL (X.F.ψ0 ⟨g, hg⟩ : D.what₂.LLˣ) = embLL0 D (S.kKs ((YS.fi j).eK.symm y)) := by
      change _ = D.what₂.embLL ((S.kKs ((YS.fi j).eK.symm y) : ↥D.LL0) : D.what₂.LL)
      rw [S.kKs_spec, ← (YS.fi j).eK_LL, RingEquiv.apply_symm_apply]
      exact congrArg _ hy.symm
    rw [e4] at e3
    refine (congrArg τ e3).trans (Eq.trans ?_ e3.symm)
    rw [map_inv₀, hτ]
  · exact (GlobalTheory.BigOn.Exp.TwConj.baseOf_of_realPin hC.lev Z.good Z.pin _ j _).fix_mu hC.lev (Z.good.base _ j _) hFB.chi

end GlobalTheory.PlaceFix

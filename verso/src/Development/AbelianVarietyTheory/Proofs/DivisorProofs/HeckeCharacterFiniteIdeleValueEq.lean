import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsApprox
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsOfBalanced
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StandardLatticeDoubleCosetClassesStabilisers
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsAdeleEquivFin
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsFiniteAdeleBaseChangeEquiv
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsBaseChangeFiniteAdeleRingEquiv
import Development.AbelianVarietyTheory.Definitions.Foundations.NotIsSplitOfIsInertAt

open NumberField IsDedekindDomain
open scoped Classical Pointwise
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links
open Formalism.MainNotions.TaylorLogMetric (VC embT tor0 lamOf Th La Iop Qbar lamC)
open Formalism.MainNotions.StandardLatticesGL3 (TT stdL pt oddE0 Wd La0 Crv inc OhE IntU)
open GlobalTheory.NormSum (Pair intG)
open GlobalTheory.FunObj.SqNum (hatId CongOne skewLat unitBlock cosetVec)
open GlobalTheory.NormExact (Reads Setup IsFinIdl HasFinPart finPt)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (InId IsUnitDet unitChar stdFst)

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.StdRead

noncomputable section

open scoped TensorProduct

namespace GlobalTheory.FinIdlRead

open GlobalTheory.Mem.Col2.SplitChar

/- English proof (translation)
Set `f : Formalism.MainNotions.StandardLatticesGL3.AE D →+* Formalism.MainNotions.StandardLatticesGL3.AE D` to `(adEquiv D).symm.toRingHom.comp (GlobalTheory.BotFormula.toFinE D).toRingHom`. Establish `hf : ∀ z, adEquiv D (f z) = GlobalTheory.BotFormula.toFinE D z` using `fun z => (adEquiv D).apply_symm_apply _`. Establish `hι : ∀ (x : D.host.E) (a : FiniteAdeleRing (𝓞 ℚ) ℚ), (GlobalTheory.BotFormula.toFinE D).toRingHom (x ⊗ₜ[ℚ] a) = algebraMap D.host.E _ x * GlobalTheory.AdeleBaseChange.adMap ℚ D.host.E a` using `GlobalTheory.BotClassDict.toFinE_tmul`. Establish `hinc : ∀ a : D.host.E, f (inc D a) = inc D a` using `fun a => by`. Apply `(adEquiv D).injective` to reduce the goal to its premises.

Rewrite using `[hf, adEquiv_inc]`. Establish `h1 : GlobalTheory.BotFormula.toFinE D (inc D a) = algebraMap D.host.E _ a * GlobalTheory.AdeleBaseChange.adMap ℚ D.host.E 1` using `GlobalTheory.BotClassDict.toFinE_tmul a 1`. Rewrite using `[h1, map_one, mul_one]`. Establish `hint : ∀ r ∈ OhE D, f r ∈ OhE D` using `fun r hr => by`. Rewrite using `[mem_OhE_iff, hf]`.

Conclude with `GlobalTheory.AdeleBaseChange.map_mem_int (F := ℚ) (E := D.host.E) hι hr`. Establish `h0 : f y - y = 0`. Use `GlobalTheory.AdeleBaseChange.eq_zero_of_divisible (F := ℚ) (E := D.host.E) (f y - y) fun N hN => ?_` and prove the remaining obligations. Take `⟨a, r, hr, e⟩` from `exists_approx y hN`. Use `⟨f r - r, sub_mem (hint r hr) hr, ?_⟩` and prove the remaining obligations.

Rewrite using `[nsmul_eq_mul]`. Express the relevant statement in the definitionally equal form `f y - y = (N : Formalism.MainNotions.StandardLatticesGL3.AE D) * (f r - r)`. Rewrite using `[e, map_add, map_mul, map_natCast, hinc]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[← hf, sub_eq_zero.1 h0]`.
-/
theorem toFinE_eq_adEquiv (D : D7) (y : Formalism.MainNotions.StandardLatticesGL3.AE D) : GlobalTheory.BotFormula.toFinE D y = adEquiv D y := by
  let f : Formalism.MainNotions.StandardLatticesGL3.AE D →+* Formalism.MainNotions.StandardLatticesGL3.AE D := (adEquiv D).symm.toRingHom.comp (GlobalTheory.BotFormula.toFinE D).toRingHom
  have hf : ∀ z, adEquiv D (f z) = GlobalTheory.BotFormula.toFinE D z := fun z => (adEquiv D).apply_symm_apply _
  have hι : ∀ (x : D.host.E) (a : FiniteAdeleRing (𝓞 ℚ) ℚ), (GlobalTheory.BotFormula.toFinE D).toRingHom (x ⊗ₜ[ℚ] a) =
      algebraMap D.host.E _ x * GlobalTheory.AdeleBaseChange.adMap ℚ D.host.E a := GlobalTheory.BotClassDict.toFinE_tmul
  have hinc : ∀ a : D.host.E, f (inc D a) = inc D a := fun a => by
    apply (adEquiv D).injective
    rw [hf, adEquiv_inc]
    have h1 : GlobalTheory.BotFormula.toFinE D (inc D a) = algebraMap D.host.E _ a * GlobalTheory.AdeleBaseChange.adMap ℚ D.host.E 1 :=
      GlobalTheory.BotClassDict.toFinE_tmul a 1
    rw [h1, map_one, mul_one]
  have hint : ∀ r ∈ OhE D, f r ∈ OhE D := fun r hr => by
    rw [mem_OhE_iff, hf]
    exact GlobalTheory.AdeleBaseChange.map_mem_int (F := ℚ) (E := D.host.E) hι hr
  have h0 : f y - y = 0 := by
    refine GlobalTheory.AdeleBaseChange.eq_zero_of_divisible (F := ℚ) (E := D.host.E) (f y - y) fun N hN => ?_
    obtain ⟨a, r, hr, e⟩ := exists_approx y hN
    refine ⟨f r - r, sub_mem (hint r hr) hr, ?_⟩
    rw [nsmul_eq_mul]
    change f y - y = (N : Formalism.MainNotions.StandardLatticesGL3.AE D) * (f r - r)
    rw [e, map_add, map_mul, map_natCast, hinc]
    ring
  rw [← hf, sub_eq_zero.1 h0]

/- English proof (translation)
Use `show GlobalTheory.LFun.toFinAd D.host.F D.host.E ((1 : Af D.host.F) ⊗ₜ[D.host.F] x) = _`. Rewrite using `[GlobalTheory.LFun.toFinAd_tmul, map_one, one_mul]`.
-/
theorem finAdEquiv_one_tmul (D : D7) (x : D.host.E) :
    GlobalTheory.LFun.finAdEquiv D.host.F D.host.E ((1 : Af D.host.F) ⊗ₜ[D.host.F] x) =
      algebraMap D.host.E (FiniteAdeleRing (𝓞 D.host.E) D.host.E) x := by
  show GlobalTheory.LFun.toFinAd D.host.F D.host.E ((1 : Af D.host.F) ⊗ₜ[D.host.F] x) = _
  rw [GlobalTheory.LFun.toFinAd_tmul, map_one, one_mul]

/- English proof (translation)
Set `c` to `(Algebra.TensorProduct.comm D.host.F (Af D.host.F) D.host.E).toRingEquiv`. Set `ι : Formalism.L2.DIV.AfE D.host.F D.host.E →+* FiniteAdeleRing (𝓞 D.host.E) D.host.E` to `(GlobalTheory.LFun.finAdEquiv D.host.F D.host.E).toRingHom.comp c.symm.toRingHom`. Establish `hι : ∀ x a, ι (x ⊗ₜ[D.host.F] a) = algebraMap D.host.E _ x * GlobalTheory.AdeleBaseChange.adMap D.host.F D.host.E a` using `fun x a => (GlobalTheory.LFun.toFinAd_tmul a x).trans (mul_comm _ _)`. Establish `e : ι (Algebra.TensorProduct.comm D.host.F (Af D.host.F) D.host.E y) = GlobalTheory.LFun.finAdEquiv D.host.F D.host.E y`. Express the relevant statement in the definitionally equal form `GlobalTheory.LFun.finAdEquiv D.host.F D.host.E (c.symm (c y)) = _`.

Rewrite using `[c.symm_apply_apply]`. Rewrite using `[GlobalTheory.HostAdeleIso.mem_intAE_iff_comm]`. Prove the components needed by the constructor for the conclusion. Introduce `hy`. Use `GlobalTheory.AdeleBaseChange.map_mem_int hι hy` as an intermediate fact.

Rewrite `this` using `[e]`. Conclude with `this`. Introduce `hy`. Use `GlobalTheory.AdeleBaseChange.mem_int_of_map hι ?_` and prove the remaining obligations. Rewrite using `[e]`.

Conclude with `hy`.
-/
theorem mem_intAE_iff_finAdEquiv (D : D7) (y : Af D.host.F ⊗[D.host.F] D.host.E) :
    y ∈ intAE D ↔ ∀ P : HeightOneSpectrum (𝓞 D.host.E), Valued.v (GlobalTheory.LFun.finAdEquiv D.host.F D.host.E y P) ≤ 1 := by
  let c := (Algebra.TensorProduct.comm D.host.F (Af D.host.F) D.host.E).toRingEquiv
  let ι : Formalism.L2.DIV.AfE D.host.F D.host.E →+* FiniteAdeleRing (𝓞 D.host.E) D.host.E :=
    (GlobalTheory.LFun.finAdEquiv D.host.F D.host.E).toRingHom.comp c.symm.toRingHom
  have hι : ∀ x a, ι (x ⊗ₜ[D.host.F] a) = algebraMap D.host.E _ x * GlobalTheory.AdeleBaseChange.adMap D.host.F D.host.E a :=
    fun x a => (GlobalTheory.LFun.toFinAd_tmul a x).trans (mul_comm _ _)
  have e : ι (Algebra.TensorProduct.comm D.host.F (Af D.host.F) D.host.E y) = GlobalTheory.LFun.finAdEquiv D.host.F D.host.E y := by
    change GlobalTheory.LFun.finAdEquiv D.host.F D.host.E (c.symm (c y)) = _
    rw [c.symm_apply_apply]
  rw [GlobalTheory.HostAdeleIso.mem_intAE_iff_comm]
  constructor
  · intro hy
    have := GlobalTheory.AdeleBaseChange.map_mem_int hι hy
    rw [e] at this
    exact this
  · intro hy
    refine GlobalTheory.AdeleBaseChange.mem_int_of_map hι ?_
    rw [e]
    exact hy

/- English proof (translation)
Introduce `D ν χ h x y hxy`. Take `⟨Φ, -, hΦ', h1, h2, h3⟩` from `GlobalTheory.DetRootRead.exists_adele_equiv_fin D (GlobalTheory.LFun.finAdEquiv D.host.F D.host.E) (finAdEquiv_one_tmul D) (mem_intAE_iff_finAdEquiv D)`. Rewrite using `[GlobalTheory.DetRootRead.read_of_equiv D ν χ h Φ hΦ' h1 h2 x]`. Take `⟨s, hs, -⟩` from `GlobalTheory.AdSplit.exists_adele_equiv D.host.F D.host.E`. Establish `split : ∀ z w : AE D, infPart D z = infPart D w → finPart D z = finPart D w → z = w` using `fun z w hi hf => s.injective (Prod.ext ((hs z).1.trans (hi.trans (hs w).1.symm)) ((hs z).2.trans (hf.trans (hs w).2.symm)))`.

Establish `hfst : (Φ (x : AE D)).1 = 1`. Set `w : AE D` to `Φ.symm (1, (Φ (x : AE D)).2)`. Establish `hw : Φ w = (1, (Φ (x : AE D)).2)` using `Φ.apply_symm_apply _`. Establish `hwi : infPart D w = 1` using `(h3 w).1 (by rw [hw])`. Establish `hwf : finPart D w = finPart D (x : AE D)`.

Apply `(GlobalTheory.LFun.finAdEquiv D.host.F D.host.E).injective` to reduce the goal to its premises. Rewrite using `[← (h3 w).2, ← (h3 (x : AE D)).2, hw]`. Establish `: w = (x : AE D)` using `split _ _ (hwi.trans hxy.1.symm) hwf`. Rewrite using `[← this, hw]`. Establish `he : Units.map Φ.toRingHom.toMonoidHom x = GlobalTheory.Mem.Col2.SplitChar.finIdl D y`.

Use `Units.ext (Prod.ext ?_ ?_)` and prove the remaining obligations. Conclude with `hfst`. Express the relevant statement in the definitionally equal form `(Φ (x : AE D)).2 = adEquiv D (y : Formalism.MainNotions.StandardLatticesGL3.AE D)`. Rewrite using `[(h3 _).2, hxy.2, toFinE_eq_adEquiv]`. Rewrite using `[he]`.
-/
theorem chr_finIdl : ∀ {D : D7} (ν : (AE D)ˣ →* Circle) (χ : Formalism.L2.Host.HChar D.host.E), ChrEq ν χ → ∀ x y, IsFinIdl x y →
    ((ν x : Circle) : ℂ) = ((χ.1 (GlobalTheory.Mem.Col2.SplitChar.finIdl D y) : ℂˣ) : ℂ) := by
  intro D ν χ h x y hxy
  obtain ⟨Φ, -, hΦ', h1, h2, h3⟩ := GlobalTheory.DetRootRead.exists_adele_equiv_fin D (GlobalTheory.LFun.finAdEquiv D.host.F D.host.E)
    (finAdEquiv_one_tmul D) (mem_intAE_iff_finAdEquiv D)
  rw [GlobalTheory.DetRootRead.read_of_equiv D ν χ h Φ hΦ' h1 h2 x]
  obtain ⟨s, hs, -⟩ := GlobalTheory.AdSplit.exists_adele_equiv D.host.F D.host.E
  have split : ∀ z w : AE D, infPart D z = infPart D w → finPart D z = finPart D w → z = w := fun z w hi hf =>
    s.injective (Prod.ext ((hs z).1.trans (hi.trans (hs w).1.symm)) ((hs z).2.trans (hf.trans (hs w).2.symm)))
  have hfst : (Φ (x : AE D)).1 = 1 := by
    let w : AE D := Φ.symm (1, (Φ (x : AE D)).2)
    have hw : Φ w = (1, (Φ (x : AE D)).2) := Φ.apply_symm_apply _
    have hwi : infPart D w = 1 := (h3 w).1 (by rw [hw])
    have hwf : finPart D w = finPart D (x : AE D) := by
      apply (GlobalTheory.LFun.finAdEquiv D.host.F D.host.E).injective
      rw [← (h3 w).2, ← (h3 (x : AE D)).2, hw]
    have : w = (x : AE D) := split _ _ (hwi.trans hxy.1.symm) hwf
    rw [← this, hw]
  have he : Units.map Φ.toRingHom.toMonoidHom x = GlobalTheory.Mem.Col2.SplitChar.finIdl D y := by
    refine Units.ext (Prod.ext ?_ ?_)
    · exact hfst
    · change (Φ (x : AE D)).2 = adEquiv D (y : Formalism.MainNotions.StandardLatticesGL3.AE D)
      rw [(h3 _).2, hxy.2, toFinE_eq_adEquiv]
  rw [he]

end GlobalTheory.FinIdlRead

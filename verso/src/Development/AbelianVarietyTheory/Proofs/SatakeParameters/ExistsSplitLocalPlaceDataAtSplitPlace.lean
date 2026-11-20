import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ThetaMod
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ExistsUniqueVec
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ExistsUnitarySupportedAtPlaceOfMulEqIdem
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ContinuousSingleAt
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SplitPlaceCompletionRealSubfieldRingEquiv
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ThetaVacuumHeckeIdentitySplitPlace
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CompIncAAlgebraMap
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CompletionExistence.LeOneIffOfMulEqOne
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SplitExEveryDatum

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.SplitLocPlace

open GlobalTheory.FinPl GlobalTheory.FinPl.SplitPoint GlobalTheory.IdemModTwo GlobalTheory.SplitChart GlobalTheory.LocMod.SplitCompl Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open scoped TensorProduct

/- English proof (translation)
Introduce `h`. Establish `hm : ∀ x : 𝓞 D.host.E, x ∈ (Formalism.DivisionValues.conjPl s.w).asIdeal ↔ IsCMField.ringOfIntegersComplexConj D.host.E x ∈ s.w.asIdeal`. Introduce `x`. Use `show x ∈ Ideal.map (Formalism.DivisionValues.cO D.host.E) s.w.asIdeal ↔ _`. Establish `e0 : (Formalism.DivisionValues.cO D.host.E).symm x = IsCMField.ringOfIntegersComplexConj D.host.E x` using `RingOfIntegers.ext rfl`.

Rewrite using `[Ideal.mem_map_of_equiv]`. Use `⟨fun ⟨y, hy, hxy⟩ => ?_, fun hx => ⟨_, hx, ?_⟩⟩` and prove the remaining obligations. Rewrite using `[← e0, ← hxy, RingEquiv.symm_apply_apply]`. Conclude with `hy`. Rewrite using `[← e0, RingEquiv.apply_symm_apply]`.

Establish `hw : (GlobalTheory.SplitConjPlace.conjSP s).w = s.w`. Use `HeightOneSpectrum.ext (Ideal.ext fun x => ?_)` and prove the remaining obligations. Rewrite using `[GlobalTheory.SplitConjPlace.mem_conj_w, ← hm, h]`. Establish `hv : ∀ x : D.host.E, Valued.v ((s.i.comp (IsCMField.complexConj D.host.E).toAlgHom).toRingHom x) = s.w.valuation D.host.E x`. Introduce `x`.

Establish `h1` using `PI.CompAtExist.muV_eq (GlobalTheory.SplitConjPlace.conjSP s) x`. Rewrite `h1` using `[hw]`. Conclude with `h1`. Take `⟨φ, hφc, hφ, -⟩` from `GlobalTheory.DenseCompl.exists_extension s.w s.v _ hv`. Take `⟨c, hc, -, hci⟩` from `GlobalTheory.SplitCompl.exists_ringEquiv D.host.E s`.

Establish `hg : ∀ y, φ (c y) = y`. Introduce `y`. Use `(HeightOneSpectrum.denseRange_algebraMap (maximalRealSubfield D.host.E) s.v).induction_on (p := fun y => φ (c y) = y) y (isClosed_eq (hφc.comp hc) continuous_id) fun a => ?_` and prove the remaining obligations. Establish `e1` using `s.i.commutes a`. Rewrite using `[← e1, hci, hφ]`.

Simplify using `only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, AlgHom.coe_comp, Function.comp_apply, AlgEquiv.coe_algHom]`. Rewrite using `[AlgEquiv.commutes]`. Apply `IsCMField.complexConj_ne_one D.host.E` to reduce the goal to its premises. Use `AlgEquiv.ext fun x => s.i.toRingHom.injective ?_` and prove the remaining obligations. Establish `h2` using `hg (s.i x)`.

Rewrite `h2` using `[hci, hφ]`. Conclude with `h2`.
-/
theorem conjPl_ne {D : D7} (s : SplitPlace D.host.E) : Formalism.DivisionValues.conjPl s.w ≠ s.w := by
  intro h
  have hm : ∀ x : 𝓞 D.host.E, x ∈ (Formalism.DivisionValues.conjPl s.w).asIdeal ↔
      IsCMField.ringOfIntegersComplexConj D.host.E x ∈ s.w.asIdeal := by
    intro x
    show x ∈ Ideal.map (Formalism.DivisionValues.cO D.host.E) s.w.asIdeal ↔ _
    have e0 : (Formalism.DivisionValues.cO D.host.E).symm x = IsCMField.ringOfIntegersComplexConj D.host.E x := RingOfIntegers.ext rfl
    rw [Ideal.mem_map_of_equiv]
    refine ⟨fun ⟨y, hy, hxy⟩ => ?_, fun hx => ⟨_, hx, ?_⟩⟩
    · rw [← e0, ← hxy, RingEquiv.symm_apply_apply]; exact hy
    · rw [← e0, RingEquiv.apply_symm_apply]
  have hw : (GlobalTheory.SplitConjPlace.conjSP s).w = s.w := by
    refine HeightOneSpectrum.ext (Ideal.ext fun x => ?_)
    rw [GlobalTheory.SplitConjPlace.mem_conj_w, ← hm, h]
  have hv : ∀ x : D.host.E, Valued.v ((s.i.comp (IsCMField.complexConj D.host.E).toAlgHom).toRingHom x) =
      s.w.valuation D.host.E x := by
    intro x
    have h1 := PI.CompAtExist.muV_eq (GlobalTheory.SplitConjPlace.conjSP s) x
    rw [hw] at h1
    exact h1
  obtain ⟨φ, hφc, hφ, -⟩ := GlobalTheory.DenseCompl.exists_extension s.w s.v _ hv
  obtain ⟨c, hc, -, hci⟩ := GlobalTheory.SplitCompl.exists_ringEquiv D.host.E s
  have hg : ∀ y, φ (c y) = y := by
    intro y
    refine (HeightOneSpectrum.denseRange_algebraMap (maximalRealSubfield D.host.E) s.v).induction_on
      (p := fun y => φ (c y) = y) y (isClosed_eq (hφc.comp hc) continuous_id) fun a => ?_
    have e1 := s.i.commutes a
    rw [← e1, hci, hφ]
    simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, AlgHom.coe_comp, Function.comp_apply, AlgEquiv.coe_algHom]
    rw [AlgEquiv.commutes]
  apply IsCMField.complexConj_ne_one D.host.E
  refine AlgEquiv.ext fun x => s.i.toRingHom.injective ?_
  have h2 := hg (s.i x)
  rw [hci, hφ] at h2
  exact h2

/- English proof (translation)
Substitute `h` using the available equality. Establish `hvw : v1 = w`. Use `HeightOneSpectrum.ext (Ideal.ext fun a => ?_)` and prove the remaining obligations. Rewrite using `[← HeightOneSpectrum.valuation_lt_one_iff_mem (K := F1), ← HeightOneSpectrum.valuation_lt_one_iff_mem (K := F1), hv]`. Substitute `hvw` using the available equality.

Conclude with `⟨RingHom.id _, continuous_id, fun a => rfl, fun z => ⟨z, rfl, rfl⟩⟩`.
-/
theorem exists_transport {E : Type} [Field E] [NumberField E] {F1 F2 : Subfield E} (h : F1 = F2)
    (v1 : HeightOneSpectrum (𝓞 F1)) (w : HeightOneSpectrum (𝓞 F2))
    (hv : ∀ a : F1, v1.valuation F1 a = w.valuation F2 ⟨a, h.le a.2⟩) :
    ∃ κ : v1.adicCompletion F1 →+* w.adicCompletion F2, Continuous κ ∧
      (∀ a : F1, κ (algebraMap F1 _ a) = algebraMap F2 (w.adicCompletion F2) ⟨a, h.le a.2⟩) ∧
      ∀ z : FiniteAdeleRing (𝓞 F1) F1, ∃ z' : FiniteAdeleRing (𝓞 F2) F2,
        Formalism.IndefR.principalLevelFrame.tensCastR h (z ⊗ₜ[F1] (1 : E)) = (1 : E) ⊗ₜ[F2] z' ∧ κ (z v1) = z' w := by
  subst h
  have hvw : v1 = w := by
    refine HeightOneSpectrum.ext (Ideal.ext fun a => ?_)
    rw [← HeightOneSpectrum.valuation_lt_one_iff_mem (K := F1), ← HeightOneSpectrum.valuation_lt_one_iff_mem (K := F1),
      hv]
  subst hvw
  exact ⟨RingHom.id _, continuous_id, fun a => rfl, fun z => ⟨z, rfl, rfl⟩⟩

/- English proof (translation)
Substitute `h` using the available equality. Both sides reduce to the same expression.
-/
theorem tensCastR_one_tmul {E : Type} [Field E] [NumberField E] {F1 F2 : Subfield E} (h : F1 = F2) (x : E) :
    Formalism.IndefR.principalLevelFrame.tensCastR h ((1 : FiniteAdeleRing (𝓞 F1) F1) ⊗ₜ[F1] x) = x ⊗ₜ[F2] (1 : FiniteAdeleRing (𝓞 F2) F2) := by
  subst h
  rfl

set_option maxHeartbeats 1000000 in

/- English proof (translation)
Introduce `D s hF`. Take `⟨e, he⟩` from `GlobalTheory.Hk3.SplitMatch.exists_isIdemAt (conjPl_ne s)`. Take `⟨-, -, v, ε, hε, hs⟩` from `he.1`. Establish `hsa : SplitAt D v e` using `splitAt_of he.1 hε hs`. Establish `hP` using `splitPrime_emb hsa s.w he`.

Establish `hf : ∀ x : D.host.E, Valued.v ((emb hsa).toRingHom x) = s.w.valuation D.host.E x`. Introduce `x`. Rewrite using `[← hP]`. Conclude with `GlobalTheory.AdelicU.valued_apply_eq_valuation (emb hsa) x`. Take `⟨φ, hφc, hφ, -⟩` from `GlobalTheory.DenseCompl.exists_extension s.w v _ hf`.

Set `g : D.host.F →+* s.w.adicCompletion D.host.E` to `(algebraMap D.host.E (s.w.adicCompletion D.host.E)).comp (algebraMap D.host.F D.host.E)`. Establish `hg : ∀ a, Valued.v (g a) = v.valuation D.host.F a`. Introduce `a`. Simplify using `only [g, RingHom.comp_apply]`. Rewrite using `[GlobalTheory.Idele.valued_algebraMap, ← hf, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, AlgHom.commutes, GlobalTheory.Idele.valued_algebraMap]`.

Take `⟨ψ, hψc, hψ, -⟩` from `GlobalTheory.DenseCompl.exists_extension v s.w g hg`. Establish `hcomp : ∀ y, φ (ψ y) = y`. Introduce `y`. Use `(HeightOneSpectrum.denseRange_algebraMap D.host.F v).induction_on (p := fun y => φ (ψ y) = y) y (isClosed_eq (hφc.comp hψc) continuous_id) fun a => ?_` and prove the remaining obligations. Rewrite using `[hψ]`.

Simplify using `only [g, RingHom.comp_apply]`. Rewrite using `[hφ]`. Conclude with `(emb hsa).commutes a`. Set `e0` to `RingEquiv.ofBijective φ ⟨φ.injective, fun y => ⟨ψ y, hcomp y⟩⟩`. Establish `he0 : ∀ y, e0.symm y = ψ y` using `fun y => e0.injective (by rw [e0.apply_symm_apply]; exact (hcomp y).symm)`.

Establish `hΦc : Continuous e0.symm` using `hψc.congr fun y => (he0 y).symm`. Establish `hΦc' : Continuous e0` using `hφc`. Establish `hΦ : ∀ x : D.host.E, e0.symm (emb hsa x) = algebraMap D.host.E (s.w.adicCompletion D.host.E) x`. Introduce `x`. Establish `h1` using `e0.symm_apply_apply (algebraMap D.host.E (s.w.adicCompletion D.host.E) x)`.

Conclude with `(congrArg e0.symm (hφ x)).symm.trans h1`. Take `⟨c, hc, -, hci⟩` from `GlobalTheory.SplitCompl.exists_ringEquiv D.host.E s`. Establish `hvv : ∀ a : D.host.F, v.valuation D.host.F a = s.v.valuation (maximalRealSubfield D.host.E) ⟨a, hF.le a.2⟩`. Introduce `a`. Establish `h1` using `hf (algebraMap D.host.F D.host.E a)`.

Establish `h2` using `PI.CompAtExist.muV_eq s (algebraMap (maximalRealSubfield D.host.E) D.host.E ⟨a, hF.le a.2⟩)`. Rewrite using `[← GlobalTheory.Idele.valued_algebraMap, ← GlobalTheory.Idele.valued_algebraMap, ← (emb hsa).commutes, ← s.i.commutes]`. Conclude with `h1.trans h2.symm`. Take `⟨κ, hκc, hκa, hκz⟩` from `exists_transport hF v s.v hvv`. Establish `hΦκ : ∀ y, e0.symm y = c (κ y)`.

Introduce `y`. Use `(HeightOneSpectrum.denseRange_algebraMap D.host.F v).induction_on (p := fun y => e0.symm y = c (κ y)) y (isClosed_eq hΦc (hc.comp hκc)) fun a => ?_` and prove the remaining obligations. Establish `h1 : algebraMap D.host.F (v.adicCompletion D.host.F) a = emb hsa (algebraMap D.host.F D.host.E a)` using `((emb hsa).commutes a).symm`. Establish `h2 : algebraMap (maximalRealSubfield D.host.E) (s.v.adicCompletion (maximalRealSubfield D.host.E)) ⟨a, hF.le a.2⟩ = s.i (algebraMap (maximalRealSubfield D.host.E) D.host.E ⟨a, hF.le a.2⟩)` using `(s.i.commutes _).symm`. Rewrite using `[hκa]`.

Rewrite using `[h2]`. Rewrite using `[hci]`. Rewrite using `[h1]`. Rewrite using `[hΦ]`. Set `p : GlobalTheory.LocMod.Place D (s.w.adicCompletion D.host.E)` to `{ e := e split := he.1 π := e0.symm.toRingHom.comp (comp hsa) ι := (sec D v e).comp e0.toRingHom.toAddMonoidHom π_ι := fun x => by show e0.symm (comp hsa (sec D v e (e0 x))) = x`.

Rewrite using `[comp_sec, RingEquiv.symm_apply_apply]`. Use `ι_π := fun a => by show sec D v e (e0 (e0.symm (comp hsa a))) = e * a`. Rewrite using `[RingEquiv.apply_symm_apply, sec_comp]`. Use `cont_π := hΦc.comp (continuous_comp hsa)`. Use `cont_ι := continuous_sec.comp hΦc' }`.

Use `⟨p, c, ⟨he.1.1, ⟨v, ε, hε, Or.inl ⟨he.1.2.1, hs⟩⟩, he.2⟩, hc, hci, fun a => ?_⟩` and prove the remaining obligations. Use `show e0.symm (comp hsa a) = _`. Proceed by induction on `a using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `tmul y x`.

Establish `hyx : y ⊗ₜ[D.host.F] x = algebraMap (AF D.host.F) (AE D) y * incA D x` using `by show _ = (y ⊗ₜ[D.host.F] (1 : D.host.E)) * ((1 : AF D.host.F) ⊗ₜ[D.host.F] x)`. Rewrite using `[Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]`. Rewrite using `[hyx, map_mul, map_mul, map_mul, map_mul, map_mul, map_mul]`. Use `congr 1`. Rewrite using `[comp_algebraMap, hΦκ]`.

Take `⟨z', hz1, hz2⟩` from `hκz y.2`. Establish `e1 : Formalism.L2.Theta.finPart D (algebraMap (AF D.host.F) (AE D) y) = y.2 ⊗ₜ[D.host.F] (1 : D.host.E)` using `rfl`. Rewrite using `[e1]`. Use `show _ = c (s.proj (Formalism.IndefR.principalLevelFrame.tensCastR hF (y.2 ⊗ₜ[D.host.F] (1 : D.host.E))))`. Rewrite using `[hz1]`.

Use `show c (κ (y.2 v)) = c (s.i 1 * z' s.v)`. Rewrite using `[map_one, one_mul, hz2]`. Use `show e0.symm (emb hsa x) = _`. Rewrite using `[hΦ]`. Establish `e1 : Formalism.L2.Theta.finPart D (incA D x) = (1 : Af D.host.F) ⊗ₜ[D.host.F] x` using `rfl`.

Rewrite using `[e1]`. Use `show _ = c (s.proj (Formalism.IndefR.principalLevelFrame.tensCastR hF ((1 : Af D.host.F) ⊗ₜ[D.host.F] x)))`. Rewrite using `[tensCastR_one_tmul]`. Use `show _ = c (s.i x * ReciprocityTheory.Aut.evalAt D.host.E s.v 1)`. Rewrite using `[map_one, mul_one, hci]`.

Consider the case `add a b ha hb => simp only [map_add, ha, hb]`.
-/
theorem exists_place : ∀ (D : D7) (s : SplitPlace D.host.E) (hF : D.host.F = maximalRealSubfield D.host.E),
    ∃ (p : GlobalTheory.LocMod.Place D (s.w.adicCompletion D.host.E))
      (c : s.v.adicCompletion (maximalRealSubfield D.host.E) ≃+* s.w.adicCompletion D.host.E),
      Formalism.L2.JoinChr.IsPlIdem D p.e s.w ∧ Continuous c ∧
      (∀ x : D.host.E, c (s.i x) = algebraMap D.host.E (s.w.adicCompletion D.host.E) x) ∧
      ∀ a : Formalism.L2.Theta.AE D, p.π a = c (s.proj (GlobalTheory.NJoin.tensCast hF (Formalism.L2.Theta.finPart D a))) := by
  intro D s hF
  obtain ⟨e, he⟩ := GlobalTheory.Hk3.SplitMatch.exists_isIdemAt (conjPl_ne s)
  obtain ⟨-, -, v, ε, hε, hs⟩ := he.1
  have hsa : SplitAt D v e := splitAt_of he.1 hε hs
  have hP := splitPrime_emb hsa s.w he
  have hf : ∀ x : D.host.E, Valued.v ((emb hsa).toRingHom x) = s.w.valuation D.host.E x := by
    intro x
    rw [← hP]
    exact GlobalTheory.AdelicU.valued_apply_eq_valuation (emb hsa) x
  obtain ⟨φ, hφc, hφ, -⟩ := GlobalTheory.DenseCompl.exists_extension s.w v _ hf
  let g : D.host.F →+* s.w.adicCompletion D.host.E :=
    (algebraMap D.host.E (s.w.adicCompletion D.host.E)).comp (algebraMap D.host.F D.host.E)
  have hg : ∀ a, Valued.v (g a) = v.valuation D.host.F a := by
    intro a
    simp only [g, RingHom.comp_apply]
    rw [GlobalTheory.Idele.valued_algebraMap, ← hf, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, AlgHom.commutes,
      GlobalTheory.Idele.valued_algebraMap]
  obtain ⟨ψ, hψc, hψ, -⟩ := GlobalTheory.DenseCompl.exists_extension v s.w g hg
  have hcomp : ∀ y, φ (ψ y) = y := by
    intro y
    refine (HeightOneSpectrum.denseRange_algebraMap D.host.F v).induction_on
      (p := fun y => φ (ψ y) = y) y (isClosed_eq (hφc.comp hψc) continuous_id) fun a => ?_
    rw [hψ]
    simp only [g, RingHom.comp_apply]
    rw [hφ]
    exact (emb hsa).commutes a
  let e0 := RingEquiv.ofBijective φ ⟨φ.injective, fun y => ⟨ψ y, hcomp y⟩⟩
  have he0 : ∀ y, e0.symm y = ψ y := fun y => e0.injective (by rw [e0.apply_symm_apply]; exact (hcomp y).symm)
  have hΦc : Continuous e0.symm := hψc.congr fun y => (he0 y).symm
  have hΦc' : Continuous e0 := hφc
  have hΦ : ∀ x : D.host.E, e0.symm (emb hsa x) = algebraMap D.host.E (s.w.adicCompletion D.host.E) x := by
    intro x
    have h1 := e0.symm_apply_apply (algebraMap D.host.E (s.w.adicCompletion D.host.E) x)
    exact (congrArg e0.symm (hφ x)).symm.trans h1
  obtain ⟨c, hc, -, hci⟩ := GlobalTheory.SplitCompl.exists_ringEquiv D.host.E s
  have hvv : ∀ a : D.host.F, v.valuation D.host.F a =
      s.v.valuation (maximalRealSubfield D.host.E) ⟨a, hF.le a.2⟩ := by
    intro a
    have h1 := hf (algebraMap D.host.F D.host.E a)
    have h2 := PI.CompAtExist.muV_eq s (algebraMap (maximalRealSubfield D.host.E) D.host.E ⟨a, hF.le a.2⟩)
    rw [← GlobalTheory.Idele.valued_algebraMap, ← GlobalTheory.Idele.valued_algebraMap, ← (emb hsa).commutes, ← s.i.commutes]
    exact h1.trans h2.symm
  obtain ⟨κ, hκc, hκa, hκz⟩ := exists_transport hF v s.v hvv
  have hΦκ : ∀ y, e0.symm y = c (κ y) := by
    intro y
    refine (HeightOneSpectrum.denseRange_algebraMap D.host.F v).induction_on
      (p := fun y => e0.symm y = c (κ y)) y (isClosed_eq hΦc (hc.comp hκc)) fun a => ?_
    have h1 : algebraMap D.host.F (v.adicCompletion D.host.F) a = emb hsa (algebraMap D.host.F D.host.E a) :=
      ((emb hsa).commutes a).symm
    have h2 : algebraMap (maximalRealSubfield D.host.E) (s.v.adicCompletion (maximalRealSubfield D.host.E))
        ⟨a, hF.le a.2⟩ = s.i (algebraMap (maximalRealSubfield D.host.E) D.host.E ⟨a, hF.le a.2⟩) :=
      (s.i.commutes _).symm
    rw [hκa]
    rw [h2]
    rw [hci]
    rw [h1]
    rw [hΦ]
  let p : GlobalTheory.LocMod.Place D (s.w.adicCompletion D.host.E) :=
    { e := e
      split := he.1
      π := e0.symm.toRingHom.comp (comp hsa)
      ι := (sec D v e).comp e0.toRingHom.toAddMonoidHom
      π_ι := fun x => by
        show e0.symm (comp hsa (sec D v e (e0 x))) = x
        rw [comp_sec, RingEquiv.symm_apply_apply]
      ι_π := fun a => by
        show sec D v e (e0 (e0.symm (comp hsa a))) = e * a
        rw [RingEquiv.apply_symm_apply, sec_comp]
      cont_π := hΦc.comp (continuous_comp hsa)
      cont_ι := continuous_sec.comp hΦc' }
  refine ⟨p, c, ⟨he.1.1, ⟨v, ε, hε, Or.inl ⟨he.1.2.1, hs⟩⟩, he.2⟩, hc, hci, fun a => ?_⟩
  show e0.symm (comp hsa a) = _
  induction a using TensorProduct.induction_on with
  | zero => simp
  | tmul y x =>
    have hyx : y ⊗ₜ[D.host.F] x = algebraMap (AF D.host.F) (AE D) y * incA D x := by
      show _ = (y ⊗ₜ[D.host.F] (1 : D.host.E)) * ((1 : AF D.host.F) ⊗ₜ[D.host.F] x)
      rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
    rw [hyx, map_mul, map_mul, map_mul, map_mul, map_mul, map_mul]
    congr 1
    · rw [comp_algebraMap, hΦκ]
      obtain ⟨z', hz1, hz2⟩ := hκz y.2
      have e1 : Formalism.L2.Theta.finPart D (algebraMap (AF D.host.F) (AE D) y) = y.2 ⊗ₜ[D.host.F] (1 : D.host.E) := rfl
      rw [e1]
      show _ = c (s.proj (Formalism.IndefR.principalLevelFrame.tensCastR hF (y.2 ⊗ₜ[D.host.F] (1 : D.host.E))))
      rw [hz1]
      show c (κ (y.2 v)) = c (s.i 1 * z' s.v)
      rw [map_one, one_mul, hz2]
    · show e0.symm (emb hsa x) = _
      rw [hΦ]
      have e1 : Formalism.L2.Theta.finPart D (incA D x) = (1 : Af D.host.F) ⊗ₜ[D.host.F] x := rfl
      rw [e1]
      show _ = c (s.proj (Formalism.IndefR.principalLevelFrame.tensCastR hF ((1 : Af D.host.F) ⊗ₜ[D.host.F] x)))
      rw [tensCastR_one_tmul]
      show _ = c (s.i x * ReciprocityTheory.Aut.evalAt D.host.E s.v 1)
      rw [map_one, mul_one, hci]
  | add a b ha hb => simp only [map_add, ha, hb]

end GlobalTheory.SplitLocPlace

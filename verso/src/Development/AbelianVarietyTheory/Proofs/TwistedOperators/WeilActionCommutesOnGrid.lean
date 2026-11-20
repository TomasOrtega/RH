import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RangeSndRel
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CuspAlongSmoothRows
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.ThetaIntegralsAgree
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CommutesWithOfIsSquareConstOfTriple
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.LevelPlusSubgroup
import Development.AbelianVarietyTheory.Definitions.Divisors.LeastSplitAuxiliaryPrimeThetaChainSpec
import Development.AutomorphicArithmetic.CyclotomicBounds.RamifiedDiscriminants.FunKit

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

namespace GlobalTheory.SquareComm

open GlobalTheory.RowClaim

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Reduce the claim to the hypotheses of an applicable result. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules.

A detailed English derivation is pending.
-/
theorem natCast_not_mem_of_coprime {K : Type} [Field K] [NumberField K] (w : HeightOneSpectrum (𝓞 K)) {n p : ℕ}
    (hc : Nat.Coprime n p) (hp : (p : 𝓞 K) ∈ w.asIdeal) : (n : 𝓞 K) ∉ w.asIdeal := by
  intro hn
  obtain ⟨a, b, hab⟩ := (Nat.isCoprime_iff_coprime.2 hc).map (Int.castRingHom (𝓞 K))
  apply w.isPrime.ne_top
  rw [Ideal.eq_top_iff_one, ← hab]
  simp only [eq_intCast, Int.cast_natCast]
  exact w.asIdeal.add_mem (w.asIdeal.mul_mem_left _ hn) (w.asIdeal.mul_mem_left _ hp)

/- English proof (translation)
Rewrite the indicated hypotheses using the stated equalities. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Use the resulting assumption.
-/
theorem natCast_mem_w {D : D7} {T : Type} {L : LevCh D T} (P : Places L) {v : HeightOneSpectrum (𝓞 D.host.F)}
    (hv : v ∈ P.S0) {n : ℕ} (hn : (n : 𝓞 D.host.F) ∈ v.asIdeal) : (n : 𝓞 D.host.E) ∈ (P.w v).asIdeal := by
  rw [← P.under_w hv] at hn
  have h : (n : 𝓞 D.host.F) ∈ Ideal.comap (algebraMap (𝓞 D.host.F) (𝓞 D.host.E)) (P.w v).asIdeal := hn
  rwa [Ideal.mem_comap, map_natCast] at h

end GlobalTheory.SquareComm

namespace GlobalTheory.SquareComm

open GlobalTheory.RowClaim

/- English proof (translation)
Reduce the conclusion to the remaining proof obligations. Extract witnesses or component facts from the available result. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact.

Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Extract witnesses or component facts from the available result. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.

Simplify using the standard rewrite rules. Reduce the conclusion to the remaining proof obligations. Separate the alternatives or extract the components of the hypothesis. Extract witnesses or component facts from the available result. Separate the alternatives or extract the components of the hypothesis.

Separate the alternatives or extract the components of the hypothesis. Establish an intermediate fact. Establish an intermediate fact. Simplify using the standard rewrite rules. The claim follows by propositional logic.

A detailed English derivation is pending.
-/
theorem squareStanding_of_setting {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type}
    {A : FamIn D.what₂.LL Γ Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {large₂ : SizeData₂ D}
    {R : RealDat D A Ks} {F : Face D A} (s : HidaSetting large₂ R F) (h11 : 11 ≤ D.host.splitBound) {sc : Consts}
    (G : GridData R.toLevCh sc) (t : T) : SquareStanding G t := by
  classical
  refine ⟨h11, fun w hw => ?_⟩
  obtain ⟨⟨Pm, -, -⟩, -⟩ := s.size
  have hq := D.host.hyp.1
  have hd := D.host.hyp.2.1
  have cop : ∀ p ∈ D.host.levelPrimes, p.Prime →
      Nat.Coprime (D.host.QS * D.host.q * D.host.d * Ideal.absNorm D.host.ccK) p := by
    intro p hpl hp
    exact Nat.Coprime.mul (UpperTheory.Ram.Fun.coprime_condN_of_splitK D.host hp (Pm.level_split p hpl)).symm
      (D.host.ccK_coprime p (by simp [hpl]))
  have cop0 : Nat.Coprime (D.host.QS * D.host.q * D.host.d * Ideal.absNorm D.host.ccK) (q0 D) := by
    obtain ⟨hp0, hm, hn⟩ := leastSplitAuxiliaryPrimeThetaChain_spec D
    have c1 : Nat.Coprime (Formalism.MainNotions.rPrAv D * LevelStarExponents.condE D) (q0 D) := by
      rw [Nat.Coprime, Nat.gcd_rec, hm]
      simp
    refine Nat.Coprime.mul (Nat.Coprime.coprime_dvd_left ⟨Formalism.MainNotions.rPrAv D, by unfold LevelStarExponents.condE; ring⟩ c1) ?_
    exact ((Nat.Prime.coprime_iff_not_dvd hp0).2 hn).symm
  rcases Finset.mem_union.1 hw with hw | hw
  · obtain ⟨v, hv, rfl⟩ := Finset.mem_image.1 hw
    rcases G.pl.mem_S0_of_sum_eq.1 hv with rfl | hv1
    · exact natCast_not_mem_of_coprime _ cop0 (natCast_mem_w G.pl hv G.pl.basePlace_over_qZero)
    · rcases (S1_mem_OmF D).1 hv1 with h | h | h | h
      · exact natCast_not_mem_of_coprime _ (cop _ (D.host.g_level 0) (D.host.g_prime 0)) (natCast_mem_w G.pl hv h)
      · exact natCast_not_mem_of_coprime _ (cop _ (D.host.g_level 1) (D.host.g_prime 1)) (natCast_mem_w G.pl hv h)
      · exact natCast_not_mem_of_coprime _ (cop _ D.host.pde_level.1 D.host.pde_prime) (natCast_mem_w G.pl hv h)
      · exact natCast_not_mem_of_coprime _ (cop _ D.host.pde_level.2 D.host.pde'_prime) (natCast_mem_w G.pl hv h)
  · have h1 := (s.core.lev.Q_off t w hw).1
    have h2 := s.guard.2 t w hw
    simp only [Nat.cast_mul, w.isPrime.mul_mem_iff_mem_or_mem, not_or] at h1 h2 ⊢
    tauto

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Reduce the conclusion to the remaining proof obligations. A detailed English derivation is pending.
-/
theorem commutesWith_all : GlobalTheory.FunPr.Hypotheses₂ → GlobalTheory.SquareSt.WeilConvergence → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ThetaIntegralsAgree →
    GlobalTheory.RowClaim.Big fun {D} _ _ _ _ {T} _ _ _ _ _ _ ch =>
      ∀ (t : T) (i j : Fin D.R.m), CommutesWith ch.W ch.S.B ch.rm t i j (ch.c i j t) := by
  intro hPr hWC hK
  refine ⟨0, fun ε CF _ => ⟨0, fun D large₂ _ _ Γ _ _ Pl0 T A Ks _ _ _ R F s ch hch _ t i j => ?_⟩⟩
  exact commutesWith_of_isSquareConst hWC hK hPr.cuspDecayBound s.core.lev
    (squareStanding_of_setting s s.size.2.1.eleven_le ch.G t) (hch.const i j t)

end GlobalTheory.SquareComm

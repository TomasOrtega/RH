import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.LocModelKSN
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.LocFacts
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.NcValDiffProd
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.LeadingMinorIntegrality
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ProductFormulaHaar.HaarAlg
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ProductFormulaHaar.NormSt

noncomputable section

open NumberField IsDedekindDomain Formalism.MainNotions.S Formalism.MainNotions.S.LocalSplitGroups Formalism.FourierDecayAlt Formalism.L2.SG.DataInst
open Classical ValuativeRel
open scoped nonZeroDivisors

namespace Formalism.L2.SG.Pf.LMK

variable {D : Formalism.BasicNotions.D7}

/- English proof (translation)
Use `(D.s.atP p).borel` as an intermediate fact. Use `(D.s.atP p).free` as an intermediate fact. Establish `: Module.Finite (D.s.atP p).Fp (D.s.atP p).Ep` using `Module.finite_of_finrank_pos (by rw [(D.s.atP p).rank]; norm_num)`. Use `(D.s.atP p).top` as an intermediate fact. Establish `hOK` using `(Z.agree p).1`.

Use `hOK.haar.haar` as an intermediate fact. Establish `hu : IsUnit (algebraMap (D.s.atP p).Fp (D.s.atP p).Ep z)` using `(isUnit_iff_ne_zero.2 hz).map _`. Establish `h1` using `Formalism.MainNotions.LocalModelPeriodLattices.modK_of_OK (Z.M p) hOK hu.unit`. Rewrite `h1` using `[IsUnit.unit_spec]`. Rewrite using `[← h1]`.

Unfold `Loc.Model.modK`. Rewrite using `[PI.ProdFormulaE.HaarAlgP.haarScaling (D.s.atP p).Fp (D.s.atP p).Ep (Z.M p).mu _ hu _, hOK.haar.volR, mul_one, Algebra.norm_algebraMap, (D.s.atP p).rank, ENNReal.toReal_ofReal (PI.ProdFormulaE.HaarBox.modF_nonneg' _), pow_two, PI.ProdFormulaE.modF_mul]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem modK_alg (Z : Formalism.L2.SG.TermLoc.LocDat D) (p : PlF D) [IsNonarchimedeanLocalField (D.s.atP p).Fp]
    {z : (D.s.atP p).Fp} (hz : z ≠ 0) :
    A5.modK (Z.M p).R (algebraMap (D.s.atP p).Fp (D.s.atP p).Ep z) = PI.ProdFormulaE.modF (D.s.atP p).Fp z ^ 2 := by
  have := (D.s.atP p).borel
  have := (D.s.atP p).free
  have : Module.Finite (D.s.atP p).Fp (D.s.atP p).Ep :=
    Module.finite_of_finrank_pos (by rw [(D.s.atP p).rank]; norm_num)
  have := (D.s.atP p).top
  have hOK := (Z.agree p).1
  have := hOK.haar.haar
  have hu : IsUnit (algebraMap (D.s.atP p).Fp (D.s.atP p).Ep z) := (isUnit_iff_ne_zero.2 hz).map _
  have h1 := Formalism.MainNotions.LocalModelPeriodLattices.modK_of_OK (Z.M p) hOK hu.unit
  rw [IsUnit.unit_spec] at h1
  rw [← h1]
  unfold Loc.Model.modK
  rw [PI.ProdFormulaE.HaarAlgP.haarScaling (D.s.atP p).Fp (D.s.atP p).Ep (Z.M p).mu _ hu _, hOK.haar.volR, mul_one,
    Algebra.norm_algebraMap, (D.s.atP p).rank, ENNReal.toReal_ofReal (PI.ProdFormulaE.HaarBox.modF_nonneg' _), pow_two,
    PI.ProdFormulaE.modF_mul]
  ring

/- English proof (translation)
Use `set A := D.s.atP p with hAdef`. Establish `hδ : Z.δ p ≠ 0` using `(Z.agree p).2.1`. Establish `hx0ne : x0 ≠ 0`. Introduce and unpack `rfl`. Rewrite `hv` using `[map_zero]`.

Conclude with `WithZero.exp_ne_zero hv.symm`. Establish `hι0 : A.ιF (x0 : D.host.F) ≠ 0`. Rewrite using `[Ne, map_eq_zero_iff _ A.ιF.injective]`. Conclude with `hx0ne` after adjusting the coercions. Establish `hvx0 : p.valuation D.host.F (x0 : D.host.F) = WithZero.exp (-(Formalism.L2.SG.Pf.NcVal.mDiff D.host.F p : ℤ))`.

Rewrite using `[HeightOneSpectrum.valuation_of_algebraMap]`. Conclude with `hv`. Use `set J : FractionalIdeal (𝓞 D.host.F)⁰ D.host.F := FractionalIdeal.dual ℤ ℚ (1 : FractionalIdeal (𝓞 D.host.F)⁰ D.host.F) with hJ`. Establish `hJ0 : J ≠ 0` using `FractionalIdeal.dual_ne_zero ℤ ℚ one_ne_zero`. Establish `hdd : ((differentIdeal ℤ (𝓞 D.host.F) : Ideal (𝓞 D.host.F)) : FractionalIdeal (𝓞 D.host.F)⁰ D.host.F) = J⁻¹` using `coeIdeal_differentIdeal ℤ ℚ D.host.F (𝓞 D.host.F)`.

Establish `hmemJ : ∀ y : D.host.F, y ∈ J ↔ ∀ a : 𝓞 D.host.F, ∃ n : ℤ, Algebra.trace ℚ D.host.F (y * a) = n`. Introduce `y`. Rewrite using `[hJ, FractionalIdeal.mem_dual (one_ne_zero : (1 : FractionalIdeal (𝓞 D.host.F)⁰ D.host.F) ≠ 0)]`. Prove the components needed by the constructor for the conclusion. Introduce `h a`.

Take `⟨n, hn⟩` from `h (algebraMap _ _ a) ((FractionalIdeal.mem_one_iff _).2 ⟨a, rfl⟩)`. Conclude with `⟨n, by rw [Algebra.traceForm_apply] at hn; rw [← hn]; rfl⟩`. Introduce `h b hb`. Take `⟨a, rfl⟩` from `(FractionalIdeal.mem_one_iff _).1 hb`. Take `⟨n, hn⟩` from `h a`.

Conclude with `⟨n, by rw [Algebra.traceForm_apply, hn]; rfl⟩`. Establish `hx0J : (x0 : D.host.F) ∈ J⁻¹`. Rewrite using `[← hdd]`. Conclude with `(FractionalIdeal.mem_coeIdeal _).2 ⟨x0, hx0, rfl⟩`. Establish `hmulO : ∀ y ∈ J, ∀ b ∈ J⁻¹, p.valuation D.host.F (y * b) ≤ 1`.

Introduce `y hy b hb`. Establish `h1 : y * b ∈ J * J⁻¹` using `FractionalIdeal.mul_mem_mul hy hb`. Rewrite `h1` using `[mul_inv_cancel₀ hJ0]`. Take `⟨o, ho⟩` from `(FractionalIdeal.mem_one_iff _).1 h1`. Rewrite using `[← ho]`.

Conclude with `p.valuation_le_one o`. Take `⟨t, htr, hne, hu1, hu2⟩` from `PI.CntNotIntW.locDiff_of PI.CntNotIntW.trace_dual_lattice (PI.CntNotIntW.dualApprox_of PI.CntNotIntW.small_powers_bound PI.CntNotIntW.tensorLiftSurjective) PI.CntNotIntW.small_powers_bound D Z.δ Z.M Z.agree p`. Establish `htJ : t ∈ J` using `(hmemJ t).2 htr`. Establish `ht0 : A.ιF t ≠ 0` using `right_ne_zero_of_mul hne`. Establish `htx0 : A.ιF (t * (x0 : D.host.F)) ∈ 𝒪[A.Fp]`.

Rewrite using `[Formalism.MainNotions.BridgeLemma.mem_OF_iff]`. Conclude with `hmulO t htJ _ hx0J`. Choose the witnesses or unpack the hypotheses as in `⟨y, hy, a, ha, hya⟩ : ∃ y ∈ J, ∃ b ∈ J⁻¹, ¬ valuation A.Fp (A.ιF (y * b)) < 1 := by`. Assume the negation of the conclusion as `hcon`. Use `push Not at hcon`.

Establish `h1 : (1 : D.host.F) ∈ J * J⁻¹`. Rewrite using `[mul_inv_cancel₀ hJ0]`. Conclude with `FractionalIdeal.one_mem_one _`. Establish `h2 : valuation A.Fp (A.ιF 1) < 1`. Use `FractionalIdeal.mul_induction_on h1 (fun y hy b hb => hcon y hy b hb) ?_` and prove the remaining obligations.

Introduce `u v hu hv`. Rewrite using `[map_add]`. Conclude with `lt_of_le_of_lt (Valuation.map_add _ _ _) (max_lt hu hv)`. Rewrite `h2` using `[map_one, map_one]`. Conclude with `lt_irrefl _ h2`.

Establish `hyδ : A.ιF y * Z.δ p ∈ 𝒪[A.Fp]`. Use `A.lf` as an intermediate fact. Use `A.ellPrime` as an intermediate fact. Establish `hz` using `Formalism.L2.SG.Pf.dualLoc_holds D.host.F p A.Fp A.qlCont A.qlFin A.ιF A.dense A.val y ((hmemJ y).1 hy)`. Conclude with `Formalism.L2.SG.Pf.LocFacts.lf_dual_le p Z _ hz`.

Establish `ha0 : valuation A.Fp (A.ιF a) ≤ valuation A.Fp (A.ιF (x0 : D.host.F))`. Rewrite using `[Formalism.MainNotions.BridgeLemma.val_iff, hvx0]`. Rewrite `ha` using `[← hdd]`. Take `⟨a', ha', rfl⟩` from `(FractionalIdeal.mem_coeIdeal _).1 ha`. Rewrite using `[HeightOneSpectrum.valuation_of_algebraMap]`.

Conclude with `Formalism.L2.SG.Pf.NcVal.intValuation_le_of_mem_different p ha'`. Establish `hyx0 : 1 ≤ valuation A.Fp (A.ιF (y * (x0 : D.host.F)))`. Establish `h1 : 1 ≤ valuation A.Fp (A.ιF (y * a))` using `not_lt.1 hya`. Rewrite `h1`, the goal using `[map_mul, map_mul]`. Conclude with `le_trans h1 (mul_le_mul' le_rfl ha0)`.

Establish `hyx0ne : A.ιF (y * (x0 : D.host.F)) ≠ 0`. Introduce `h0`. Rewrite `hyx0` using `[h0, map_zero]`. Conclude with `absurd hyx0 (not_le.2 zero_lt_one)`. Use `⟨hι0, ?_, ?_⟩` and prove the remaining obligations.

Establish `e : Z.δ p * (A.ιF (x0 : D.host.F))⁻¹ = (A.ιF y * Z.δ p) * (A.ιF (y * (x0 : D.host.F)))⁻¹`. Rewrite using `[map_mul]`. Establish `hy0 : A.ιF y ≠ 0` using `by intro h0; rw [map_mul, h0, zero_mul] at hyx0ne; exact hyx0ne rfl`. Clear the denominators using the available nonvanishing facts. Rewrite using `[e]`.

Use `mul_mem hyδ ?_` and prove the remaining obligations. Rewrite using `[Valuation.mem_integer_iff, map_inv₀]`. Conclude with `inv_le_one_of_one_le₀ hyx0`. Establish `e : (Z.δ p * (A.ιF (x0 : D.host.F))⁻¹)⁻¹ = A.ιF (t * (x0 : D.host.F)) * (Z.δ p * A.ιF t)⁻¹`. Rewrite using `[map_mul]`.

Clear the denominators using the available nonvanishing facts. Rewrite using `[e]`. Conclude with `mul_mem htx0 hu2`.
-/
theorem delta_unit (Z : Formalism.L2.SG.TermLoc.LocDat D) (p : PlF D) (x0 : 𝓞 D.host.F)
    (hx0 : x0 ∈ differentIdeal ℤ (𝓞 D.host.F))
    (hv : p.intValuation x0 = WithZero.exp (-(Formalism.L2.SG.Pf.NcVal.mDiff D.host.F p : ℤ))) :
    (D.s.atP p).ιF (x0 : D.host.F) ≠ 0 ∧
      Z.δ p * ((D.s.atP p).ιF (x0 : D.host.F))⁻¹ ∈ 𝒪[(D.s.atP p).Fp] ∧
      (Z.δ p * ((D.s.atP p).ιF (x0 : D.host.F))⁻¹)⁻¹ ∈ 𝒪[(D.s.atP p).Fp] := by
  set A := D.s.atP p with hAdef
  have hδ : Z.δ p ≠ 0 := (Z.agree p).2.1
  have hx0ne : x0 ≠ 0 := by
    rintro rfl
    rw [map_zero] at hv
    exact WithZero.exp_ne_zero hv.symm
  have hι0 : A.ιF (x0 : D.host.F) ≠ 0 := by
    rw [Ne, map_eq_zero_iff _ A.ιF.injective]
    exact_mod_cast hx0ne
  have hvx0 : p.valuation D.host.F (x0 : D.host.F) = WithZero.exp (-(Formalism.L2.SG.Pf.NcVal.mDiff D.host.F p : ℤ)) := by
    rw [HeightOneSpectrum.valuation_of_algebraMap]; exact hv

  set J : FractionalIdeal (𝓞 D.host.F)⁰ D.host.F := FractionalIdeal.dual ℤ ℚ (1 : FractionalIdeal (𝓞 D.host.F)⁰ D.host.F)
    with hJ
  have hJ0 : J ≠ 0 := FractionalIdeal.dual_ne_zero ℤ ℚ one_ne_zero
  have hdd : ((differentIdeal ℤ (𝓞 D.host.F) : Ideal (𝓞 D.host.F)) : FractionalIdeal (𝓞 D.host.F)⁰ D.host.F) = J⁻¹ :=
    coeIdeal_differentIdeal ℤ ℚ D.host.F (𝓞 D.host.F)
  have hmemJ : ∀ y : D.host.F, y ∈ J ↔ ∀ a : 𝓞 D.host.F, ∃ n : ℤ, Algebra.trace ℚ D.host.F (y * a) = n := by
    intro y
    rw [hJ, FractionalIdeal.mem_dual (one_ne_zero : (1 : FractionalIdeal (𝓞 D.host.F)⁰ D.host.F) ≠ 0)]
    constructor
    · intro h a
      obtain ⟨n, hn⟩ := h (algebraMap _ _ a) ((FractionalIdeal.mem_one_iff _).2 ⟨a, rfl⟩)
      exact ⟨n, by rw [Algebra.traceForm_apply] at hn; rw [← hn]; rfl⟩
    · intro h b hb
      obtain ⟨a, rfl⟩ := (FractionalIdeal.mem_one_iff _).1 hb
      obtain ⟨n, hn⟩ := h a
      exact ⟨n, by rw [Algebra.traceForm_apply, hn]; rfl⟩
  have hx0J : (x0 : D.host.F) ∈ J⁻¹ := by
    rw [← hdd]; exact (FractionalIdeal.mem_coeIdeal _).2 ⟨x0, hx0, rfl⟩
  have hmulO : ∀ y ∈ J, ∀ b ∈ J⁻¹, p.valuation D.host.F (y * b) ≤ 1 := by
    intro y hy b hb
    have h1 : y * b ∈ J * J⁻¹ := FractionalIdeal.mul_mem_mul hy hb
    rw [mul_inv_cancel₀ hJ0] at h1
    obtain ⟨o, ho⟩ := (FractionalIdeal.mem_one_iff _).1 h1
    rw [← ho]
    exact p.valuation_le_one o

  obtain ⟨t, htr, hne, hu1, hu2⟩ := PI.CntNotIntW.locDiff_of PI.CntNotIntW.trace_dual_lattice
    (PI.CntNotIntW.dualApprox_of PI.CntNotIntW.small_powers_bound PI.CntNotIntW.tensorLiftSurjective)
    PI.CntNotIntW.small_powers_bound D Z.δ Z.M Z.agree p
  have htJ : t ∈ J := (hmemJ t).2 htr
  have ht0 : A.ιF t ≠ 0 := right_ne_zero_of_mul hne
  have htx0 : A.ιF (t * (x0 : D.host.F)) ∈ 𝒪[A.Fp] := by
    rw [Formalism.MainNotions.BridgeLemma.mem_OF_iff]
    exact hmulO t htJ _ hx0J

  obtain ⟨y, hy, a, ha, hya⟩ : ∃ y ∈ J, ∃ b ∈ J⁻¹, ¬ valuation A.Fp (A.ιF (y * b)) < 1 := by
    by_contra hcon
    push Not at hcon
    have h1 : (1 : D.host.F) ∈ J * J⁻¹ := by
      rw [mul_inv_cancel₀ hJ0]; exact FractionalIdeal.one_mem_one _
    have h2 : valuation A.Fp (A.ιF 1) < 1 := by
      refine FractionalIdeal.mul_induction_on h1 (fun y hy b hb => hcon y hy b hb) ?_
      intro u v hu hv
      rw [map_add]
      exact lt_of_le_of_lt (Valuation.map_add _ _ _) (max_lt hu hv)
    rw [map_one, map_one] at h2
    exact lt_irrefl _ h2

  have hyδ : A.ιF y * Z.δ p ∈ 𝒪[A.Fp] := by
    have := A.lf
    have := A.ellPrime
    have hz := Formalism.L2.SG.Pf.dualLoc_holds D.host.F p A.Fp A.qlCont A.qlFin A.ιF A.dense A.val y ((hmemJ y).1 hy)
    exact Formalism.L2.SG.Pf.LocFacts.lf_dual_le p Z _ hz

  have ha0 : valuation A.Fp (A.ιF a) ≤ valuation A.Fp (A.ιF (x0 : D.host.F)) := by
    rw [Formalism.MainNotions.BridgeLemma.val_iff, hvx0]
    rw [← hdd] at ha
    obtain ⟨a', ha', rfl⟩ := (FractionalIdeal.mem_coeIdeal _).1 ha
    rw [HeightOneSpectrum.valuation_of_algebraMap]
    exact Formalism.L2.SG.Pf.NcVal.intValuation_le_of_mem_different p ha'
  have hyx0 : 1 ≤ valuation A.Fp (A.ιF (y * (x0 : D.host.F))) := by
    have h1 : 1 ≤ valuation A.Fp (A.ιF (y * a)) := not_lt.1 hya
    rw [map_mul, map_mul] at h1 ⊢
    exact le_trans h1 (mul_le_mul' le_rfl ha0)
  have hyx0ne : A.ιF (y * (x0 : D.host.F)) ≠ 0 := by
    intro h0; rw [h0, map_zero] at hyx0; exact absurd hyx0 (not_le.2 zero_lt_one)
  refine ⟨hι0, ?_, ?_⟩
  · have e : Z.δ p * (A.ιF (x0 : D.host.F))⁻¹ = (A.ιF y * Z.δ p) * (A.ιF (y * (x0 : D.host.F)))⁻¹ := by
      rw [map_mul]
      have hy0 : A.ιF y ≠ 0 := by intro h0; rw [map_mul, h0, zero_mul] at hyx0ne; exact hyx0ne rfl
      field_simp
    rw [e]
    refine mul_mem hyδ ?_
    rw [Valuation.mem_integer_iff, map_inv₀]
    exact inv_le_one_of_one_le₀ hyx0
  · have e : (Z.δ p * (A.ιF (x0 : D.host.F))⁻¹)⁻¹ = A.ιF (t * (x0 : D.host.F)) * (Z.δ p * A.ιF t)⁻¹ := by
      rw [map_mul]
      field_simp
    rw [e]
    exact mul_mem htx0 hu2

/- English proof (translation)
Use `(D.s.atP p).lf` as an intermediate fact. Use `Formalism.MainNotions.LocalModelPeriodLattices.top_of_OK (Z.M p) (Z.agree p).1` as an intermediate fact. Establish `hd` using `Formalism.MainNotions.LocalModelPeriodLattices.datum_of_OK (Z.M p) (Z.agree p).1`. Take `⟨x0, hx0, hv⟩` from `Formalism.L2.SG.Pf.NcVal.exists_mem_different_intValuation_eq (F := D.host.F) p`. Take `⟨hι0, hu1, hu2⟩` from `delta_unit Z p x0 hx0 hv`.

Use `set u := Z.δ p * ((D.s.atP p).ιF (x0 : D.host.F))⁻¹ with hudef`. Establish `hu0 : u ≠ 0` using `mul_ne_zero (Z.agree p).2.1 (inv_ne_zero hι0)`. Establish `hmu : A5.modK (Z.M p).R (algebraMap (D.s.atP p).Fp (D.s.atP p).Ep u) = 1` using `Formalism.FourierDecayAlt.P.OrbitalIntegralReduction.modK_unitR (alg_mem_R (M := Z.M) p hu1) (alg_mem_R (M := Z.M) p hu2) (by rw [← map_mul, mul_inv_cancel₀ hu0, map_one])`. Establish `e : Z.δ p = u * (D.s.atP p).ιF (x0 : D.host.F)` using `by rw [hudef, mul_assoc, inv_mul_cancel₀ hι0, mul_one]`. Establish `hx0ne : x0 ≠ 0`.

Introduce and unpack `rfl`. Rewrite `hv` using `[map_zero]`. Conclude with `WithZero.exp_ne_zero hv.symm`. Rewrite using `[e, map_mul, Formalism.FourierDecayAlt.P.A5x5.modK_mul' hd ((isUnit_iff_ne_zero.2 hu0).map _) ((isUnit_iff_ne_zero.2 hι0).map _), hmu, one_mul, modK_alg Z p hι0, PI.ProdFormulaE.modF_localization_eq_adicAbv]`. Establish `h3` using `NumberField.HeightOneSpectrum.embedding_mul_absNorm D.host.F p hx0ne`.

Rewrite `h3` using `[NumberField.FinitePlace.norm_embedding]`. Establish `hcount : (Associates.mk p.asIdeal).count (Associates.mk (Ideal.span {x0})).factors = Formalism.L2.SG.Pf.NcVal.mDiff D.host.F p`. Rewrite `hv` using `[HeightOneSpectrum.intValuation_if_neg p hx0ne]`. Use `WithZero.exp_injective hv` as an intermediate fact. Use linear arithmetic over natural numbers and integers.

Establish `hmp : p.maxPowDividing (Ideal.span {x0}) = p.maxPowDividing (differentIdeal ℤ (𝓞 D.host.F))`. Unfold `HeightOneSpectrum.maxPowDividing`. Rewrite using `[hcount]`. Rewrite `h3` using `[hmp]`. Establish `hN : ((Ideal.absNorm (p.maxPowDividing (differentIdeal ℤ (𝓞 D.host.F))) : ℕ) : ℝ) ≠ 0`.

Introduce `h0`. Rewrite `h3` using `[h0, mul_zero]`. Conclude with `zero_ne_one h3`. Establish `h4 : (NumberField.HeightOneSpectrum.adicAbv D.host.F p) (x0 : D.host.F) = ((Ideal.absNorm (p.maxPowDividing (differentIdeal ℤ (𝓞 D.host.F))) : ℕ) : ℝ)⁻¹` using `eq_inv_of_mul_eq_one_left h3`. Rewrite `h4`, the goal using `[show ((x0 : D.host.F)) = algebraMap (𝓞 D.host.F) D.host.F x0 from rfl]`.

Rewrite using `[h4]`.
-/
theorem modK_delta (Z : Formalism.L2.SG.TermLoc.LocDat D) (p : PlF D) :
    A5.modK (Z.M p).R (algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (Z.δ p)) =
      (((Ideal.absNorm (p.maxPowDividing (differentIdeal ℤ (𝓞 D.host.F))) : ℕ) : ℝ)⁻¹) ^ 2 := by
  have := (D.s.atP p).lf
  have := Formalism.MainNotions.LocalModelPeriodLattices.top_of_OK (Z.M p) (Z.agree p).1
  have hd := Formalism.MainNotions.LocalModelPeriodLattices.datum_of_OK (Z.M p) (Z.agree p).1
  obtain ⟨x0, hx0, hv⟩ := Formalism.L2.SG.Pf.NcVal.exists_mem_different_intValuation_eq (F := D.host.F) p
  obtain ⟨hι0, hu1, hu2⟩ := delta_unit Z p x0 hx0 hv
  set u := Z.δ p * ((D.s.atP p).ιF (x0 : D.host.F))⁻¹ with hudef
  have hu0 : u ≠ 0 := mul_ne_zero (Z.agree p).2.1 (inv_ne_zero hι0)
  have hmu : A5.modK (Z.M p).R (algebraMap (D.s.atP p).Fp (D.s.atP p).Ep u) = 1 :=
    Formalism.FourierDecayAlt.P.OrbitalIntegralReduction.modK_unitR (alg_mem_R (M := Z.M) p hu1) (alg_mem_R (M := Z.M) p hu2)
      (by rw [← map_mul, mul_inv_cancel₀ hu0, map_one])
  have e : Z.δ p = u * (D.s.atP p).ιF (x0 : D.host.F) := by rw [hudef, mul_assoc, inv_mul_cancel₀ hι0, mul_one]
  have hx0ne : x0 ≠ 0 := by
    rintro rfl
    rw [map_zero] at hv
    exact WithZero.exp_ne_zero hv.symm
  rw [e, map_mul, Formalism.FourierDecayAlt.P.A5x5.modK_mul' hd ((isUnit_iff_ne_zero.2 hu0).map _) ((isUnit_iff_ne_zero.2 hι0).map _),
    hmu, one_mul, modK_alg Z p hι0, PI.ProdFormulaE.modF_localization_eq_adicAbv]

  have h3 := NumberField.HeightOneSpectrum.embedding_mul_absNorm D.host.F p hx0ne
  rw [NumberField.FinitePlace.norm_embedding] at h3
  have hcount : (Associates.mk p.asIdeal).count (Associates.mk (Ideal.span {x0})).factors =
      Formalism.L2.SG.Pf.NcVal.mDiff D.host.F p := by
    rw [HeightOneSpectrum.intValuation_if_neg p hx0ne] at hv
    have := WithZero.exp_injective hv
    omega
  have hmp : p.maxPowDividing (Ideal.span {x0}) = p.maxPowDividing (differentIdeal ℤ (𝓞 D.host.F)) := by
    unfold HeightOneSpectrum.maxPowDividing
    rw [hcount]
  rw [hmp] at h3
  have hN : ((Ideal.absNorm (p.maxPowDividing (differentIdeal ℤ (𝓞 D.host.F))) : ℕ) : ℝ) ≠ 0 := by
    intro h0; rw [h0, mul_zero] at h3; exact zero_ne_one h3
  have h4 : (NumberField.HeightOneSpectrum.adicAbv D.host.F p) (x0 : D.host.F) =
      ((Ideal.absNorm (p.maxPowDividing (differentIdeal ℤ (𝓞 D.host.F))) : ℕ) : ℝ)⁻¹ :=
    eq_inv_of_mul_eq_one_left h3
  rw [show ((x0 : D.host.F)) = algebraMap (𝓞 D.host.F) D.host.F x0 from rfl] at h4 ⊢
  rw [h4]

/- English proof (translation)
Set `φ : Ideal (𝓞 D.host.F) →* ℝ` to `(powMonoidHom 2).comp (invMonoidHom.comp ((Nat.castRingHom ℝ).toMonoidHom.comp (Ideal.absNorm : Ideal (𝓞 D.host.F) →*₀ ℕ).toMonoidHom))`. Establish `hφ : ∀ J, φ J = (((Ideal.absNorm J : ℕ) : ℝ)⁻¹) ^ 2` using `fun J => rfl`. Establish `hfin` using `Ideal.finite_mulSupport hI`. Establish `hsub : (Function.mulSupport fun p : PlF D => φ (p.maxPowDividing I)) ⊆ Function.mulSupport fun p : PlF D => p.maxPowDividing I` using `Function.mulSupport_comp_subset (map_one φ) _`. Use `⟨?_, ?_⟩` and prove the remaining obligations.

Simplify `hfin.subset hsub` using `only [hφ]`. Establish `h1` using `(MonoidHom.map_finprod φ hfin).symm`. Simplify using `only [hφ] at h1`. Rewrite using `[h1, Ideal.finprod_heightOneSpectrum_factorization hI]`.
-/
theorem prod_maxPow (I : Ideal (𝓞 D.host.F)) (hI : I ≠ 0) :
    (Function.mulSupport fun p : PlF D =>
      (((Ideal.absNorm (p.maxPowDividing I) : ℕ) : ℝ)⁻¹) ^ 2).Finite ∧
    ∏ᶠ p : PlF D, (((Ideal.absNorm (p.maxPowDividing I) : ℕ) : ℝ)⁻¹) ^ 2 = (((Ideal.absNorm I : ℕ) : ℝ)⁻¹) ^ 2 := by
  let φ : Ideal (𝓞 D.host.F) →* ℝ := (powMonoidHom 2).comp (invMonoidHom.comp
    ((Nat.castRingHom ℝ).toMonoidHom.comp (Ideal.absNorm : Ideal (𝓞 D.host.F) →*₀ ℕ).toMonoidHom))
  have hφ : ∀ J, φ J = (((Ideal.absNorm J : ℕ) : ℝ)⁻¹) ^ 2 := fun J => rfl
  have hfin := Ideal.finite_mulSupport hI
  have hsub : (Function.mulSupport fun p : PlF D => φ (p.maxPowDividing I)) ⊆
      Function.mulSupport fun p : PlF D => p.maxPowDividing I :=
    Function.mulSupport_comp_subset (map_one φ) _
  refine ⟨?_, ?_⟩
  · simpa only [hφ] using hfin.subset hsub
  · have h1 := (MonoidHom.map_finprod φ hfin).symm
    simp only [hφ] at h1
    rw [h1, Ideal.finprod_heightOneSpectrum_factorization hI]

/- English proof (translation)
Introduce `δ M hA`. Set `Z : Formalism.L2.SG.TermLoc.LocDat D` to `⟨δ, M, hA⟩`. Establish `hI : differentIdeal ℤ (𝓞 D.host.F) ≠ 0` using `differentIdeal_ne_bot`. Establish `hfun : (fun p => A5.modK (M p).R (algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (δ p))) = fun p : PlF D => (((Ideal.absNorm (p.maxPowDividing (differentIdeal ℤ (𝓞 D.host.F))) : ℕ) : ℝ)⁻¹) ^ 2`. Use function extensionality and compare the values at `fun p => modK_delta Z p`.

Take `⟨hfin, hval⟩` from `prod_maxPow (D := D) _ hI`. Rewrite using `[hfun]`. Use `⟨hfin, ?_⟩` and prove the remaining obligations. Rewrite using `[hval, absNorm_differentIdeal D.host.F (𝓞 D.host.F)]`. Establish `hf : Module.finrank ℚ D.host.E = 2 * D.R.f`.

Use `Formalism.MainNotions.LocalModelPeriodLattices.cmE D` as an intermediate fact. Rewrite using `[(Formalism.FourierDecayAlt.P.degreeFacts_statement D.host.E).1, Formalism.MainNotions.LocalModelPeriodLattices.deg_eq]`. Establish `hrd : D.host.rdE ^ (2 * D.R.f) = |(NumberField.discr D.host.E : ℝ)|`. Unfold `Formalism.BasicNotions.Host.rdE`. Rewrite using `[← hf, one_div]`.

Conclude with `Real.rpow_inv_natCast_pow (abs_nonneg _) Module.finrank_pos.ne'`. Rewrite using `[hrd, Formalism.L2.SG.NGCut.LeadingMinorIntegrality.discr_sq, Nat.cast_natAbs, Int.cast_abs]`. Use `push_cast`. Rewrite using `[abs_pow, inv_pow]`.
-/
theorem deltaProd_holds (D : Formalism.BasicNotions.D7) : DeltaProd D := by
  intro δ M hA
  let Z : Formalism.L2.SG.TermLoc.LocDat D := ⟨δ, M, hA⟩
  have hI : differentIdeal ℤ (𝓞 D.host.F) ≠ 0 := differentIdeal_ne_bot
  have hfun : (fun p => A5.modK (M p).R (algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (δ p))) =
      fun p : PlF D => (((Ideal.absNorm (p.maxPowDividing (differentIdeal ℤ (𝓞 D.host.F))) : ℕ) : ℝ)⁻¹) ^ 2 :=
    funext fun p => modK_delta Z p
  obtain ⟨hfin, hval⟩ := prod_maxPow (D := D) _ hI
  rw [hfun]
  refine ⟨hfin, ?_⟩
  rw [hval, absNorm_differentIdeal D.host.F (𝓞 D.host.F)]
  have hf : Module.finrank ℚ D.host.E = 2 * D.R.f := by
    have := Formalism.MainNotions.LocalModelPeriodLattices.cmE D
    rw [(Formalism.FourierDecayAlt.P.degreeFacts_statement D.host.E).1, Formalism.MainNotions.LocalModelPeriodLattices.deg_eq]
  have hrd : D.host.rdE ^ (2 * D.R.f) = |(NumberField.discr D.host.E : ℝ)| := by
    unfold Formalism.BasicNotions.Host.rdE
    rw [← hf, one_div]
    exact Real.rpow_inv_natCast_pow (abs_nonneg _) Module.finrank_pos.ne'
  rw [hrd, Formalism.L2.SG.NGCut.LeadingMinorIntegrality.discr_sq, Nat.cast_natAbs, Int.cast_abs]
  push_cast
  rw [abs_pow, inv_pow]

end Formalism.L2.SG.Pf.LMK

namespace Formalism.L2.SG.Pf

/- English proof (translation)
The claim follows from `localModelS_of_delta (LMK.deltaProd_holds D)`.
-/
theorem localModelS_holds (D : Formalism.BasicNotions.D7) : Formalism.L2.SG.DataCut.LocalModelS D := localModelS_of_delta (LMK.deltaProd_holds D)

/- English proof (translation)
The claim follows from `Formalism.L2.SG.DataCut.localModelAt_of_KS (localModelK_holds D) (localModelS_holds D)`.
-/
theorem localModelAt_holds (D : Formalism.BasicNotions.D7) : Formalism.L2.SG.DataInst.LocalModelAt D :=
  Formalism.L2.SG.DataCut.localModelAt_of_KS (localModelK_holds D) (localModelS_holds D)

end Formalism.L2.SG.Pf

import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormPeriodSq
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemLsB
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StandardLatticeDoubleCosetClassesStabilisers
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteWeilRepEqLatticeIntertwinerMulCharacter
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticePointSignEqThetaLawSemicharacter
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StdCharFiniteAdeleRationalEqExpTrace

open NumberField MeasureTheory IsDedekindDomain
open scoped Classical
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum
open Formalism.MainNotions.TaylorLogMetric (VC embT tor0 Hf lamOf area Th U)
open Formalism.MainNotions.StandardLatticesGL3 (WeilO HeckeU TT stdL pt oddE0)
open GlobalTheory.NormExact
open GlobalTheory.BotFormula (IsFinPt)
open GlobalTheory.BotClassDict (finQ)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.SplitPhase

open scoped TensorProduct

/- English proof (translation)
Introduce `D`. Establish `hsq` using `D.host.sqd_sq`. Set `b : 𝓞 D.host.E` to `⟨(1 + D.host.sqrtMinusD) / 2, GlobalTheory.NormSum.isIntegral_half_one_add D.host.d D.host.hyp.2.2.2.1 _ hsq⟩`. Establish `hbv : (b : D.host.E) = (1 + D.host.sqrtMinusD) / 2` using `rfl`. Establish `h2s : star (2 : D.host.E) = 2`.

Use `star_natCast (R := D.host.E) 2` as an intermediate fact. Conclude with `this` after adjusting the coercions. Establish `hbs : star (b : D.host.E) = 1 - (b : D.host.E)`. Rewrite using `[hbv, star_div₀, star_add, star_one, h2s, GlobalTheory.FockCompare.RealChart.star_sqrtMinusD]`. Expand and normalize the polynomial expressions, which then agree.

Use `⟨b, ?_, ?_⟩` and prove the remaining obligations. Apply `NumberField.RingOfIntegers.ext show (b : D.host.E) + ((GlobalTheory.FinWeil.sgO D b : 𝓞 D.host.E) : D.host.E) = 1` to reduce the goal to its premises. Establish `hc : ((GlobalTheory.FinWeil.sgO D b : 𝓞 D.host.E) : D.host.E) = star (b : D.host.E)`. Establish `e1 : ((GlobalTheory.FinWeil.sgO D b : 𝓞 D.host.E) : D.host.E) = D.host.conj (b : D.host.E)` using `rfl`. Rewrite using `[e1]`.

Conclude with `(Formalism.BasicNotions.bridge_star_holds D.R D.host _).symm`. Rewrite using `[hc, hbs]`. Expand and normalize the polynomial expressions, which then agree. Introduce `ψ θ S T cc δ r hset z`. Establish `hr : r ≠ 0` using `GlobalTheory.NormExact.IsScale.ne_zero hset.crv.1.1 hset.scale`.

Use `set X : Matrix (Fin T.rank) (Fin S.rank) D.host.E := Matrix.of fun i j => -(r⁻¹ * z i j) with hX`. Establish `hfin : finPt (S` using `S) (T := T) rfl rfl r z = GlobalTheory.LatVac.finTens 1 X := by`. Use function extensionality and compare the values at `i j`. Both sides reduce to the same expression. Establish `hmap : GlobalTheory.FinWeilO.intA D b • GlobalTheory.LatVac.finTens 1 X = GlobalTheory.LatVac.finTens 1 (Matrix.of fun i j => (b : D.host.E) * X i j)`.

Use function extensionality and compare the values at `i j`. Use `show ((1 : AF D.host.F) ⊗ₜ[D.host.F] (b : D.host.E)) * (pairA D.host.F 0 1 ⊗ₜ[D.host.F] (X i j)) = pairA D.host.F 0 1 ⊗ₜ[D.host.F] ((b : D.host.E) * X i j)`. Rewrite using `[Algebra.TensorProduct.tmul_mul_tmul, one_mul]`. Use `set n : D.host.E := ∑ c, ∑ a, star (X c a) * X c a with hn`. Establish `hns : star n = n`.

Rewrite using `[hn, star_sum]`. Use `Finset.sum_congr rfl fun a _ => ?_` and prove the remaining obligations. Rewrite using `[star_sum]`. Use `Finset.sum_congr rfl fun c _ => ?_` and prove the remaining obligations. Rewrite using `[star_mul', star_star, mul_comm]`.

Establish `hR : GlobalTheory.LatVac.hRat S T X X = n`. Rewrite using `[GlobalTheory.LatVac.hRat, hset.gS, hset.gT, inv_one]`. Simplify using `only [Matrix.one_apply, ite_mul, one_mul, zero_mul, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true]`. Establish `e : ∀ x, (∑ x_1, ∑ x_2, if x = x_1 then star (X x_2 x_1) * X x_2 x else 0) = ∑ x_2, star (X x_2 x) * X x_2 x` using `fun x => by`. Rewrite using `[Finset.sum_comm]`.

Simplify using `only [Finset.sum_ite_eq, Finset.mem_univ, if_true]`. Rewrite using `[Finset.sum_congr rfl fun x _ => e x, Finset.sum_comm]`. Establish `hs : symplOH S T (GlobalTheory.FinWeilO.intA D b • finPt (S` using `S) (T := T) rfl rfl r z) (finPt (S := S) (T := T) rfl rfl r z) = pairA D.host.F 0 (algebraMap D.host.F (Af D.host.F) (1 / 2 * Algebra.trace D.host.F D.host.E (D.host.xi0 * ((b : D.host.E) * n)))) := by`. Rewrite using `[hfin, hmap, symplOH, GlobalTheory.LatVac.symplO_finTens, GlobalTheory.ThetaSignLat.hRat_smul_left, hR]`. Use `Prod.ext (mul_zero _) ?_` and prove the remaining obligations.

Use `show algebraMap D.host.F (Af D.host.F) (1 / 2) * (1 * 1 * _) = _`. Rewrite using `[one_mul, one_mul, ← RingHom.map_mul]`. Both sides reduce to the same expression. Establish `hq` using `GlobalTheory.ThetaSignLat.trace_val n (b : D.host.E) hns hbv`. Use `set q : D.host.F := 1 / 2 * Algebra.trace D.host.F D.host.E (D.host.xi0 * ((b : D.host.E) * n)) with hqdef`.

Establish `hneg : -(pairA D.host.F 0 (algebraMap D.host.F (Af D.host.F) q)) = pairA D.host.F 0 (algebraMap D.host.F (Af D.host.F) (-q))`. Use `Prod.ext ?_ ?_` and prove the remaining obligations. Use `show -(0 : Ainf D.host.F) = 0`. Conclude with `neg_zero`. Use `show -(algebraMap D.host.F (Af D.host.F) q) = _`.

Rewrite using `[map_neg]`. Both sides reduce to the same expression. Rewrite using `[hs, hneg, GlobalTheory.PsiFinRat.psi_pairA_zero_algebraMap ψ hset.std]`. Take `⟨c, hc⟩ : ∃ c : ℂ, c = ∑ τ, tauE D τ n` from `⟨_, rfl⟩`. Take `⟨hxi, hN1, hd1⟩` from `ReciprocityTheory.ChartRestriction.G.PullbackSections.PfModelDataX.xiR_facts D`.

Establish `hNR : (Ideal.absNorm D.host.ccK : ℝ) ≠ 0` using `by linarith`. Establish `hNC : (Ideal.absNorm D.host.ccK : ℂ) ≠ 0` using `by exact_mod_cast hNR`. Establish `hdR : Real.sqrt D.host.d ≠ 0` using `by linarith`. Establish `hsumq : ∑ τ, tauE D τ ((-q : D.host.F) : D.host.E) = c / (2 * (Ideal.absNorm D.host.ccK : ℂ))`. Establish `e : ∀ τ, tauE D τ ((-q : D.host.F) : D.host.E) = tauE D τ n / (2 * (Ideal.absNorm D.host.ccK : ℂ))` using `fun τ => by`.

Rewrite using `[show ((-q : D.host.F) : D.host.E) = -((q : D.host.F) : D.host.E) from rfl, hq, neg_div, neg_neg, map_div₀, map_mul, map_natCast, map_ofNat]`. Rewrite using `[Finset.sum_congr rfl fun τ _ => e τ, ← Finset.sum_div, hc]`. Establish `hcre : ((c.re : ℝ) : ℂ) = c`. Establish `: starRingEnd ℂ c = c`. Rewrite using `[hc, map_sum]`.

Use `Finset.sum_congr rfl fun τ _ => ?_` and prove the remaining obligations. Rewrite using `[← GlobalTheory.FockCompare.tauE_star, hns]`. Conclude with `Complex.conj_eq_iff_re.1 this`. Use `set Z : VC D S.rank T.rank := fun τ i j => -(embT D τ (X i j)) with hZ`. Establish `hpt : pt D (tor0 D cc δ) δ z = fun τ i j => δ * embT D τ r * Z τ i j`.

Use function extensionality and compare the values at `τ i j`. Establish `ez : z i j = r * -(X i j)`. Rewrite using `[hX, Matrix.of_apply]`. Clear the denominators using the available nonvanishing facts. Use `show δ * embT D τ (z i j) = δ * embT D τ r * -(embT D τ (X i j))`.

Rewrite using `[ez, map_mul, map_neg]`. Expand and normalize the polynomial expressions, which then agree. Establish `hsum : ∑ τ, ∑ i, ∑ j, Z τ i j * starRingEnd ℂ (Z τ i j) = c`. Rewrite using `[hc]`. Use `Finset.sum_congr rfl fun τ _ => ?_` and prove the remaining obligations.

Rewrite using `[hn, map_sum]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[map_sum]`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Rewrite using `[map_mul, GlobalTheory.FockCompare.tauE_star, hZ]`.

Use `show -(tauE D τ (X i j)) * starRingEnd ℂ (-(tauE D τ (X i j))) = _`. Rewrite using `[map_neg]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[Formalism.MainNotions.StandardLatticesGL3.wdPh, Formalism.MainNotions.TaylorLogMetric.qH, hpt, GlobalTheory.NormExact.Hf_scale hset.crv hset.scale, hsum, Formalism.MainNotions.StandardLatticesGL3.ee, hsumq]`. Establish `hre : Real.sqrt D.host.d / 2 * (2 * ((Formalism.L2.Pj.xiR D : ℝ) : ℂ) * c).re / 2 = c.re / (2 * Ideal.absNorm D.host.ccK)`.

Rewrite using `[show (2 * ((Formalism.L2.Pj.xiR D : ℝ) : ℂ) * c) = ((2 * Formalism.L2.Pj.xiR D : ℝ) : ℂ) * c by push_cast; ring, Complex.re_ofReal_mul, hxi]`. Clear the denominators using the available nonvanishing facts. Rewrite using `[hre]`. Use `congr 1`. Use `push_cast`.

Rewrite using `[hcre]`.
-/
theorem phase_eq : ∀ D : D7, ∃ w : 𝓞 D.host.E, w + GlobalTheory.FinWeil.sgO D w = 1 ∧
  ∀ (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (r : D.host.E),
  Setup ψ θ S T cc δ r → ∀ z : Matrix (Fin T.rank) (Fin S.rank) D.host.E,
  ψ (-symplOH S T (GlobalTheory.FinWeilO.intA D w • finPt (S := S) (T := T) rfl rfl r z) (finPt (S := S) (T := T) rfl rfl r z)) =
    Formalism.MainNotions.StandardLatticesGL3.wdPh D (tor0 D cc δ) (pt D (tor0 D cc δ) δ z) := by
  intro D
  have hsq := D.host.sqd_sq
  let b : 𝓞 D.host.E := ⟨(1 + D.host.sqrtMinusD) / 2,
    GlobalTheory.NormSum.isIntegral_half_one_add D.host.d D.host.hyp.2.2.2.1 _ hsq⟩
  have hbv : (b : D.host.E) = (1 + D.host.sqrtMinusD) / 2 := rfl
  have h2s : star (2 : D.host.E) = 2 := by
    have := star_natCast (R := D.host.E) 2
    exact_mod_cast this
  have hbs : star (b : D.host.E) = 1 - (b : D.host.E) := by
    rw [hbv, star_div₀, star_add, star_one, h2s, GlobalTheory.FockCompare.RealChart.star_sqrtMinusD]
    ring
  refine ⟨b, ?_, ?_⟩
  · apply NumberField.RingOfIntegers.ext
    show (b : D.host.E) + ((GlobalTheory.FinWeil.sgO D b : 𝓞 D.host.E) : D.host.E) = 1
    have hc : ((GlobalTheory.FinWeil.sgO D b : 𝓞 D.host.E) : D.host.E) = star (b : D.host.E) := by
      have e1 : ((GlobalTheory.FinWeil.sgO D b : 𝓞 D.host.E) : D.host.E) = D.host.conj (b : D.host.E) := rfl
      rw [e1]
      exact (Formalism.BasicNotions.bridge_star_holds D.R D.host _).symm
    rw [hc, hbs]; ring
  · intro ψ θ S T cc δ r hset z
    have hr : r ≠ 0 := GlobalTheory.NormExact.IsScale.ne_zero hset.crv.1.1 hset.scale
    set X : Matrix (Fin T.rank) (Fin S.rank) D.host.E := Matrix.of fun i j => -(r⁻¹ * z i j) with hX
    have hfin : finPt (S := S) (T := T) rfl rfl r z = GlobalTheory.LatVac.finTens 1 X := by
      funext i j; rfl
    have hmap : GlobalTheory.FinWeilO.intA D b • GlobalTheory.LatVac.finTens 1 X =
        GlobalTheory.LatVac.finTens 1 (Matrix.of fun i j => (b : D.host.E) * X i j) := by
      funext i j
      show ((1 : AF D.host.F) ⊗ₜ[D.host.F] (b : D.host.E)) * (pairA D.host.F 0 1 ⊗ₜ[D.host.F] (X i j)) =
        pairA D.host.F 0 1 ⊗ₜ[D.host.F] ((b : D.host.E) * X i j)
      rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul]
    set n : D.host.E := ∑ c, ∑ a, star (X c a) * X c a with hn
    have hns : star n = n := by
      rw [hn, star_sum]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [star_sum]
      refine Finset.sum_congr rfl fun c _ => ?_
      rw [star_mul', star_star, mul_comm]
    have hR : GlobalTheory.LatVac.hRat S T X X = n := by
      rw [GlobalTheory.LatVac.hRat, hset.gS, hset.gT, inv_one]
      simp only [Matrix.one_apply, ite_mul, one_mul, zero_mul, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq,
        Finset.sum_ite_eq', Finset.mem_univ, if_true]
      have e : ∀ x, (∑ x_1, ∑ x_2, if x = x_1 then star (X x_2 x_1) * X x_2 x else 0) =
          ∑ x_2, star (X x_2 x) * X x_2 x := fun x => by
        rw [Finset.sum_comm]
        simp only [Finset.sum_ite_eq, Finset.mem_univ, if_true]
      rw [Finset.sum_congr rfl fun x _ => e x, Finset.sum_comm]
    have hs : symplOH S T (GlobalTheory.FinWeilO.intA D b • finPt (S := S) (T := T) rfl rfl r z)
        (finPt (S := S) (T := T) rfl rfl r z) = pairA D.host.F 0
        (algebraMap D.host.F (Af D.host.F) (1 / 2 * Algebra.trace D.host.F D.host.E (D.host.xi0 * ((b : D.host.E) * n)))) := by
      rw [hfin, hmap, symplOH, GlobalTheory.LatVac.symplO_finTens, GlobalTheory.ThetaSignLat.hRat_smul_left, hR]
      refine Prod.ext (mul_zero _) ?_
      show algebraMap D.host.F (Af D.host.F) (1 / 2) * (1 * 1 * _) = _
      rw [one_mul, one_mul, ← RingHom.map_mul]
      rfl
    have hq := GlobalTheory.ThetaSignLat.trace_val n (b : D.host.E) hns hbv
    set q : D.host.F := 1 / 2 * Algebra.trace D.host.F D.host.E (D.host.xi0 * ((b : D.host.E) * n)) with hqdef
    have hneg : -(pairA D.host.F 0 (algebraMap D.host.F (Af D.host.F) q)) =
        pairA D.host.F 0 (algebraMap D.host.F (Af D.host.F) (-q)) := by
      refine Prod.ext ?_ ?_
      · show -(0 : Ainf D.host.F) = 0
        exact neg_zero
      · show -(algebraMap D.host.F (Af D.host.F) q) = _
        rw [map_neg]
        rfl
    rw [hs, hneg, GlobalTheory.PsiFinRat.psi_pairA_zero_algebraMap ψ hset.std]
    obtain ⟨c, hc⟩ : ∃ c : ℂ, c = ∑ τ, tauE D τ n := ⟨_, rfl⟩
    obtain ⟨hxi, hN1, hd1⟩ := ReciprocityTheory.ChartRestriction.G.PullbackSections.PfModelDataX.xiR_facts D
    have hNR : (Ideal.absNorm D.host.ccK : ℝ) ≠ 0 := by linarith
    have hNC : (Ideal.absNorm D.host.ccK : ℂ) ≠ 0 := by exact_mod_cast hNR
    have hdR : Real.sqrt D.host.d ≠ 0 := by linarith
    have hsumq : ∑ τ, tauE D τ ((-q : D.host.F) : D.host.E) = c / (2 * (Ideal.absNorm D.host.ccK : ℂ)) := by
      have e : ∀ τ, tauE D τ ((-q : D.host.F) : D.host.E) = tauE D τ n / (2 * (Ideal.absNorm D.host.ccK : ℂ)) :=
        fun τ => by
          rw [show ((-q : D.host.F) : D.host.E) = -((q : D.host.F) : D.host.E) from rfl, hq, neg_div, neg_neg,
            map_div₀, map_mul, map_natCast, map_ofNat]
      rw [Finset.sum_congr rfl fun τ _ => e τ, ← Finset.sum_div, hc]
    have hcre : ((c.re : ℝ) : ℂ) = c := by
      have : starRingEnd ℂ c = c := by
        rw [hc, map_sum]
        refine Finset.sum_congr rfl fun τ _ => ?_
        rw [← GlobalTheory.FockCompare.tauE_star, hns]
      exact Complex.conj_eq_iff_re.1 this
    set Z : VC D S.rank T.rank := fun τ i j => -(embT D τ (X i j)) with hZ
    have hpt : pt D (tor0 D cc δ) δ z = fun τ i j => δ * embT D τ r * Z τ i j := by
      funext τ i j
      have ez : z i j = r * -(X i j) := by
        rw [hX, Matrix.of_apply]
        field_simp
      show δ * embT D τ (z i j) = δ * embT D τ r * -(embT D τ (X i j))
      rw [ez, map_mul, map_neg]
      ring
    have hsum : ∑ τ, ∑ i, ∑ j, Z τ i j * starRingEnd ℂ (Z τ i j) = c := by
      rw [hc]
      refine Finset.sum_congr rfl fun τ _ => ?_
      rw [hn, map_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [map_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [map_mul, GlobalTheory.FockCompare.tauE_star, hZ]
      show -(tauE D τ (X i j)) * starRingEnd ℂ (-(tauE D τ (X i j))) = _
      rw [map_neg]
      ring
    rw [Formalism.MainNotions.StandardLatticesGL3.wdPh, Formalism.MainNotions.TaylorLogMetric.qH, hpt, GlobalTheory.NormExact.Hf_scale hset.crv hset.scale, hsum, Formalism.MainNotions.StandardLatticesGL3.ee,
      hsumq]
    have hre : Real.sqrt D.host.d / 2 * (2 * ((Formalism.L2.Pj.xiR D : ℝ) : ℂ) * c).re / 2 =
        c.re / (2 * Ideal.absNorm D.host.ccK) := by
      rw [show (2 * ((Formalism.L2.Pj.xiR D : ℝ) : ℂ) * c) = ((2 * Formalism.L2.Pj.xiR D : ℝ) : ℂ) * c by push_cast; ring,
        Complex.re_ofReal_mul, hxi]
      field_simp
    rw [hre]
    congr 1
    push_cast
    rw [hcre]
end GlobalTheory.SplitPhase

import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ActFromBlocks
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.PoissonSummationAdelicTuples
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsArchimedeanExponentsAdeleCharacter
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsAdelesHaarMeasureCovolumeOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsStdCharNegOneOfStandardTraceAdelicAddChar
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicRapidDecayOfMemAdelicSchwartzSpace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExtendByZeroMemSchA
open scoped Matrix GlobalTheory.VacAny
open NumberField IsDedekindDomain MeasureTheory Filter Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RatWeilOp

noncomputable section

namespace GlobalTheory.PoissonReindex

open GlobalTheory.SWQ

variable {F : Type} [Field F] [NumberField F]

def reidx {κ ι : Type} (e : κ ≃ ι) : (ι → AF F) ≃ₜ+ (κ → AF F) where
  toFun u i := u (e i)
  invFun x j := x (e.symm j)
  left_inv u := by funext j; simp
  right_inv x := by funext i; simp
  map_add' u v := rfl
  continuous_toFun := continuous_pi fun i => continuous_apply _
  continuous_invFun := continuous_pi fun j => continuous_apply _

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem reidx_apply {κ ι : Type} (e : κ ≃ ι) (u : ι → AF F) (i : κ) : reidx (F := F) e u i = u (e i) := rfl

/- English proof (translation)
Simplify using `only [dotProduct, reidx_apply]`. Conclude with `e.sum_comp (fun j => u j * y j)`.
-/
theorem dot_reidx {κ ι : Type} [Fintype κ] [Fintype ι] (e : κ ≃ ι) (u y : ι → AF F) :
    reidx e u ⬝ᵥ reidx e y = u ⬝ᵥ y := by
  simp only [dotProduct, reidx_apply]
  exact e.sum_comp (fun j => u j * y j)

/- English proof (translation)
Simplify using `only [Bd, dotProduct]`. Use `Finset.sum_congr rfl fun l _ => ?_` and prove the remaining obligations. Rewrite using `[show (2 : F) * (1 / 2) = 1 by norm_num, map_one, one_mul]`.
-/
theorem Bd_half {N : ℕ} (s u : Fin N → AF F) : Bd (AF F) (fun _ : Fin N => (1 / 2 : F)) s u = s ⬝ᵥ u := by
  simp only [Bd, dotProduct]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [show (2 : F) * (1 / 2) = 1 by norm_num, map_one, one_mul]

/- English proof (translation)
Establish `h` using `GlobalTheory.RestrSchA.mem_schA_comp_extend F e.symm e.symm.injective Φ hΦ`. Use `h using 2 with u` and compare the differences between its conclusion and the goal. Use `congr 1`. Use function extensionality and compare the values at `i`. Rewrite using `[reidx_apply]`.

Use `conv_rhs => rw [← e.symm_apply_apply i]`. Conclude with `(e.symm.injective.extend_apply u 0 (e i)).symm`.
-/
theorem mem_schA_reidx {κ ι : Type} [Fintype κ] [Fintype ι] (e : κ ≃ ι) {Φ : (κ → AF F) → ℂ}
    (hΦ : Φ ∈ schA F κ) : (fun u => Φ (reidx e u)) ∈ schA F ι := by
  have h := GlobalTheory.RestrSchA.mem_schA_comp_extend F e.symm e.symm.injective Φ hΦ
  convert h using 2 with u
  congr 1
  funext i
  rw [reidx_apply]
  conv_rhs => rw [← e.symm_apply_apply i]
  exact (e.symm.injective.extend_apply u 0 (e i)).symm

end GlobalTheory.PoissonReindex

open GlobalTheory.SWQ GlobalTheory.PoissonReindex in

/- English proof (translation)
Introduce `F _ _ hF ψ hψ κ _ inst hB μ hμ`. Use `haveI : BorelSpace (AF F) := ⟨rfl⟩`. Use `haveI : SecondCountableTopology (AF F) := GlobalTheory.AdelicUnitaryTop.secondCountable_adele F`. Establish `hinst : inst = MeasurableSpace.pi`. Rewrite using `[hB.measurable_eq]`.

Conclude with `(Pi.borelSpace (ι := κ) (X := fun _ => AF F)).measurable_eq.symm`. Substitute `hinst` using the available equality. Use `set N := Fintype.card κ`. Set `e : κ ≃ Fin N` to `Fintype.equivFin κ`. Establish `hC1` using `GlobalTheory.StdCharFromIsStd.isCharAF hψ`.

Take `⟨lam, hlam⟩` from `GlobalTheory.SWQ.exists_isLam F hF ψ hC1`. Take `⟨ν, hν⟩` from `GlobalTheory.SWQ.exists_adeles_haarMeasure_covolume_one F`. Set `a : Fin N → F` to `fun _ => 1 / 2`. Establish `hC : Ctx ψ lam ν a` using `⟨hF, hC1, hlam, hν, fun _ => by norm_num [a]⟩`. Take `⟨hHaar, -⟩` from `GlobalTheory.SWQ.rat_lattice_fundamentalDomain F N ν hν`.

Use `haveI := hHaar`. Set `T : (Fin N → AF F) ≃ₜ+ (κ → AF F)` to `reidx e`. Set `Tm : (Fin N → AF F) ≃ᵐ (κ → AF F)` to `T.toHomeomorph.toMeasurableEquiv`. Establish `hTm : ∀ u, Tm u = T u` using `fun _ => rfl`. Use `haveI hm : (Measure.map Tm (muV N ν)).IsAddHaarMeasure := T.isAddHaarMeasure_map (muV N ν)`.

Establish `hr` using `Measure.isAddLeftInvariant_eq_smul μ (Measure.map Tm (muV N ν))`. Use `set r := μ.addHaarScalarFactor (Measure.map Tm (muV N ν))`. Establish `hr0 : (r : ℂ) ≠ 0`. Introduce `h`. Establish `h' : r = 0` using `by exact_mod_cast h`.

Rewrite `hr` using `[h', zero_smul]`. Conclude with `(NeZero.ne μ) hr`. Use `⟨(r : ℂ), hr0, fun Φ hΦ hFΦ => ?_⟩` and prove the remaining obligations. Use `set G : (κ → AF F) → ℂ := fun y => ∫ x, Φ x * ψ (x ⬝ᵥ y) ∂μ with hG`. Use `set Φ' : (Fin N → AF F) → ℂ := fun u => Φ (T u) with hΦ'`.

Establish `key : ∀ y', G (T y') = (r : ℂ) * Fo ψ ν a Φ' y'`. Introduce `y'`. Simplify using `only [hG]`. Rewrite using `[hr, integral_smul_nnreal_measure, integral_map_equiv]`. Simplify using `only [Fo, hΦ', hTm, a, Bd_half, T, dot_reidx]`.

Rewrite using `[NNReal.smul_def, Complex.real_smul]`. Establish `hΦ's : Φ' ∈ schA F (Fin N)` using `mem_schA_reidx e hΦ`. Establish `hD : Decay Φ'` using `GlobalTheory.SchwartzDecay.decay_of_mem_schA F N Φ' hΦ's`. Establish `hGs : (fun u => G (T u)) ∈ schA F (Fin N)` using `mem_schA_reidx e hFΦ`. Establish `hFeq : Fo ψ ν a Φ' = (r : ℂ)⁻¹ • fun u => G (T u)`.

Use function extensionality and compare the values at `u`. Simplify using `only [Pi.smul_apply, smul_eq_mul, key u]`. Rewrite using `[← mul_assoc, inv_mul_cancel₀ hr0, one_mul]`. Establish `hFD : Decay (Fo ψ ν a Φ')`. Rewrite using `[hFeq]`.

Conclude with `GlobalTheory.SchwartzDecay.decay_smul _ (GlobalTheory.SchwartzDecay.decay_of_mem_schA F N _ hGs)`. Establish `hP` using `GlobalTheory.SWQ.poisson_summation F N ψ lam ν a hC Φ' hD hFD`. Set `E2 : (Fin N → F) ≃ (κ → F)` to `{ toFun := fun ξ i => ξ (e i), invFun := fun η j => η (e.symm j), left_inv := fun ξ => by funext j; simp, right_inv := fun η => by funext i; simp }`. Establish `hth : ∀ H : (κ → AF F) → ℂ, thetaSum F H = th (fun u => H (T u))`. Introduce `H`.

Simplify using `only [thetaSum, th]`. Conclude with `((E2.tsum_eq (fun η => H (fun i => algebraMap F (AF F) (η i))))).symm`. Rewrite using `[hth G, hth Φ]`. Simplify using `only [th] at hP ⊢`. Simplify using `only [key, tsum_mul_left]`.

Rewrite using `[hP]`.
-/
theorem GlobalTheory.PoissonReindex.poisson_any : ∀ (F : Type) [Field F] [NumberField F], IsTotallyReal F → ∀ (ψ : AddChar (AF F) ℂ), IsStd ψ → ∀ (κ : Type) [Fintype κ]
    [MeasurableSpace (κ → AF F)] [BorelSpace (κ → AF F)] (μ : Measure (κ → AF F)) [μ.IsAddHaarMeasure],
    ∃ c : ℂ, c ≠ 0 ∧ ∀ Φ ∈ schA F κ, (fun y : κ → AF F => ∫ x, Φ x * ψ (x ⬝ᵥ y) ∂μ) ∈ schA F κ →
      thetaSum F (fun y : κ → AF F => ∫ x, Φ x * ψ (x ⬝ᵥ y) ∂μ) = c * thetaSum F Φ := by
  intro F _ _ hF ψ hψ κ _ inst hB μ hμ
  haveI : BorelSpace (AF F) := ⟨rfl⟩
  haveI : SecondCountableTopology (AF F) := GlobalTheory.AdelicUnitaryTop.secondCountable_adele F
  have hinst : inst = MeasurableSpace.pi := by
    rw [hB.measurable_eq]
    exact (Pi.borelSpace (ι := κ) (X := fun _ => AF F)).measurable_eq.symm
  subst hinst
  set N := Fintype.card κ
  let e : κ ≃ Fin N := Fintype.equivFin κ
  have hC1 := GlobalTheory.StdCharFromIsStd.isCharAF hψ
  obtain ⟨lam, hlam⟩ := GlobalTheory.SWQ.exists_isLam F hF ψ hC1
  obtain ⟨ν, hν⟩ := GlobalTheory.SWQ.exists_adeles_haarMeasure_covolume_one F
  let a : Fin N → F := fun _ => 1 / 2
  have hC : Ctx ψ lam ν a := ⟨hF, hC1, hlam, hν, fun _ => by norm_num [a]⟩
  obtain ⟨hHaar, -⟩ := GlobalTheory.SWQ.rat_lattice_fundamentalDomain F N ν hν
  haveI := hHaar
  let T : (Fin N → AF F) ≃ₜ+ (κ → AF F) := reidx e
  let Tm : (Fin N → AF F) ≃ᵐ (κ → AF F) := T.toHomeomorph.toMeasurableEquiv
  have hTm : ∀ u, Tm u = T u := fun _ => rfl
  haveI hm : (Measure.map Tm (muV N ν)).IsAddHaarMeasure := T.isAddHaarMeasure_map (muV N ν)
  have hr := Measure.isAddLeftInvariant_eq_smul μ (Measure.map Tm (muV N ν))
  set r := μ.addHaarScalarFactor (Measure.map Tm (muV N ν))
  have hr0 : (r : ℂ) ≠ 0 := by
    intro h
    have h' : r = 0 := by exact_mod_cast h
    rw [h', zero_smul] at hr
    exact (NeZero.ne μ) hr
  refine ⟨(r : ℂ), hr0, fun Φ hΦ hFΦ => ?_⟩
  set G : (κ → AF F) → ℂ := fun y => ∫ x, Φ x * ψ (x ⬝ᵥ y) ∂μ with hG
  set Φ' : (Fin N → AF F) → ℂ := fun u => Φ (T u) with hΦ'
  have key : ∀ y', G (T y') = (r : ℂ) * Fo ψ ν a Φ' y' := by
    intro y'
    simp only [hG]
    rw [hr, integral_smul_nnreal_measure, integral_map_equiv]
    simp only [Fo, hΦ', hTm, a, Bd_half, T, dot_reidx]
    rw [NNReal.smul_def, Complex.real_smul]
  have hΦ's : Φ' ∈ schA F (Fin N) := mem_schA_reidx e hΦ
  have hD : Decay Φ' := GlobalTheory.SchwartzDecay.decay_of_mem_schA F N Φ' hΦ's
  have hGs : (fun u => G (T u)) ∈ schA F (Fin N) := mem_schA_reidx e hFΦ
  have hFeq : Fo ψ ν a Φ' = (r : ℂ)⁻¹ • fun u => G (T u) := by
    funext u
    simp only [Pi.smul_apply, smul_eq_mul, key u]
    rw [← mul_assoc, inv_mul_cancel₀ hr0, one_mul]
  have hFD : Decay (Fo ψ ν a Φ') := by
    rw [hFeq]
    exact GlobalTheory.SchwartzDecay.decay_smul _ (GlobalTheory.SchwartzDecay.decay_of_mem_schA F N _ hGs)
  have hP := GlobalTheory.SWQ.poisson_summation F N ψ lam ν a hC Φ' hD hFD
  let E2 : (Fin N → F) ≃ (κ → F) :=
    { toFun := fun ξ i => ξ (e i), invFun := fun η j => η (e.symm j),
      left_inv := fun ξ => by funext j; simp, right_inv := fun η => by funext i; simp }
  have hth : ∀ H : (κ → AF F) → ℂ, thetaSum F H = th (fun u => H (T u)) := by
    intro H
    simp only [thetaSum, th]
    exact ((E2.tsum_eq (fun η => H (fun i => algebraMap F (AF F) (η i))))).symm
  rw [hth G, hth Φ]
  simp only [th] at hP ⊢
  simp only [key, tsum_mul_left]
  rw [hP]

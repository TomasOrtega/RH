import Mathlib
import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.ConvolutionSmoothL2
import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.DiscreteSpectrumKFiniteDecomposition
import Formalism.HarderNarasimhan.ShiftInvariance
import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.EigenfunctionFiniteCoefficients
import Formalism.RealPlaceAnalysis.FinalF
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.DiscreteSeriesCoefficientIntegrableMajorant
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.TruncatedLeastLatticeSizeLipschitzProperties
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExtAeEqContRep
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.RightConvolutionOperatorAeEqIntegralAdelic
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.RowsAutIdemElementary
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FiniteAdelicUnitaryCongruenceTopology
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.AdelicUnitaryHaarBiInvariant

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec GlobalTheory.DSId
open scoped InnerProductSpace ComplexOrder ContDiff

namespace GlobalTheory.ReproducingFixed

/- English proof (translation)
Unfold `rkR`. Use `set A := univ.filter fun a => ε a = true`. Use `set A' := univ.filter fun a => ε a = false`. Establish `h1` using `Finset.card_union_add_card_inter A A'`. Establish `h2 : A ∩ A' = ∅`.

Use extensionality with `a`. Simplify using `[A, A']`. Establish `h3` using `Finset.card_le_univ (A ∪ A')`. Rewrite `h1` using `[h2, Finset.card_empty]`. Rewrite `h3` using `[Fintype.card_fin]`.

Use linear arithmetic over natural numbers and integers.
-/
theorem two_mul_rank_le {n : ℕ} (ε : Fin n → Bool) : 2 * rkR ε ≤ n := by
  unfold rkR
  set A := univ.filter fun a => ε a = true
  set A' := univ.filter fun a => ε a = false
  have h1 := Finset.card_union_add_card_inter A A'
  have h2 : A ∩ A' = ∅ := by
    ext a
    simp [A, A']
  have h3 := Finset.card_le_univ (A ∪ A')
  rw [h2, Finset.card_empty] at h1
  rw [Fintype.card_fin] at h3
  omega

/- English proof (translation)
Distinguish the cases in `hq : rkR (B.I.ε v) = 0`. Conclude with `Or.inl hq`. Use `right`. Establish `h2` using `two_mul_rank_le (B.I.ε v)`. Establish `hq1 : (1 : ℝ) ≤ (rkR (B.I.ε v) : ℝ)` using `by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hq`.

Establish `h2r : 2 * (rkR (B.I.ε v) : ℝ) ≤ B.I.n` using `by exact_mod_cast h2`. Establish `hnr : (1 : ℝ) ≤ B.I.n` using `by exact_mod_cast hn`. Establish `hsq : 0 < Real.sqrt (rkR (B.I.ε v))` using `Real.sqrt_pos.mpr (by linarith)`. Establish `hbv` using `hb v`. Unfold `HBig at hbv`.

Establish `key : s + 4 * B.I.n * rkR (B.I.ε v) ≤ 4 * (B.I.n : ℝ) ^ 2` using `by nlinarith`. Establish `hle : 8 * Real.sqrt (rkR (B.I.ε v)) * (s + 4 * B.I.n * rkR (B.I.ε v)) ≤ 32 * (B.I.n : ℝ) ^ 2 * Real.sqrt (rkR (B.I.ε v))` using `by nlinarith`. Establish `hpos : 0 < (B.I.n : ℝ) ^ 2 * Real.sqrt (rkR (B.I.ε v))` using `by positivity`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem weight_condition (B : RowsAut) (h s : ℝ) (hn : 1 ≤ B.I.n) (hb : HBig B 40 h)
    (hs : s ≤ 2 * (B.I.n : ℝ) ^ 2) (v : InfinitePlace B.I.F) :
    rkR (B.I.ε v) = 0 ∨ 8 * Real.sqrt (rkR (B.I.ε v)) * (s + 4 * B.I.n * rkR (B.I.ε v)) < h := by
  by_cases hq : rkR (B.I.ε v) = 0
  · exact Or.inl hq
  right
  have h2 := two_mul_rank_le (B.I.ε v)
  have hq1 : (1 : ℝ) ≤ (rkR (B.I.ε v) : ℝ) := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hq
  have h2r : 2 * (rkR (B.I.ε v) : ℝ) ≤ B.I.n := by exact_mod_cast h2
  have hnr : (1 : ℝ) ≤ B.I.n := by exact_mod_cast hn
  have hsq : 0 < Real.sqrt (rkR (B.I.ε v)) := Real.sqrt_pos.mpr (by linarith)
  have hbv := hb v
  unfold HBig at hbv
  have key : s + 4 * B.I.n * rkR (B.I.ε v) ≤ 4 * (B.I.n : ℝ) ^ 2 := by nlinarith
  have hle : 8 * Real.sqrt (rkR (B.I.ε v)) * (s + 4 * B.I.n * rkR (B.I.ε v)) ≤
      32 * (B.I.n : ℝ) ^ 2 * Real.sqrt (rkR (B.I.ε v)) := by nlinarith
  have hpos : 0 < (B.I.n : ℝ) ^ 2 * Real.sqrt (rkR (B.I.ε v)) := by positivity
  linarith

/- English proof (translation)
Establish `ha` using `GlobalTheory.TauLipschitz.trunc_pos I hn x`. Establish `hb` using `GlobalTheory.TauLipschitz.trunc_pos I hn (x * g)`. Establish `hl` using `GlobalTheory.TauLipschitz.log_trunc_le I hn x g hg`. Establish `hf : (0 : ℝ) < I.f`. Establish `: 0 < I.f`.

Unfold `AutInst.f`. Conclude with `Module.finrank_pos`. Conclude with `this` after adjusting the coercions. Use `set D := dSum I g.1`. Establish `h1 : tau1 I x * Real.exp (-(D / I.f)) ≤ tau1 I (x * g)`.

Use `Real.exp_le_exp.mpr hl` as an intermediate fact. Rewrite `this` using `[Real.exp_log hb, Real.exp_sub, Real.exp_log ha]`. Rewrite using `[Real.exp_neg, ← div_eq_mul_inv]`. Conclude with `this`. Establish `h2 : (tau1 I (x * g))⁻¹ ≤ (tau1 I x)⁻¹ * Real.exp (D / I.f)`.

Establish `hpos : 0 < tau1 I x * Real.exp (-(D / I.f))` using `mul_pos ha (Real.exp_pos _)`. Combine the equalities or inequalities in the displayed calculation. Establish `h3` using `pow_le_pow_left₀ (inv_nonneg.mpr hb.le) h2 (2 * I.n ^ 2 * I.f)`. Establish `h4 : ((2 * I.n ^ 2 * I.f : ℕ) : ℝ) * (D / I.f) = 2 * (I.n : ℝ) ^ 2 * D`. Use `push_cast`.

Clear the denominators using the available nonvanishing facts. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[mul_pow, ← Real.exp_nat_mul, h4]`.
-/
theorem inv_tau_pow_le (I : AutInst) (hn : 1 ≤ I.n) (x g : I.GA) (hg : g.2 ∈ I.Kset) :
    (tau1 I (x * g))⁻¹ ^ (2 * I.n ^ 2 * I.f) ≤
      (tau1 I x)⁻¹ ^ (2 * I.n ^ 2 * I.f) * Real.exp (2 * (I.n : ℝ) ^ 2 * dSum I g.1) := by
  have ha := GlobalTheory.TauLipschitz.trunc_pos I hn x
  have hb := GlobalTheory.TauLipschitz.trunc_pos I hn (x * g)
  have hl := GlobalTheory.TauLipschitz.log_trunc_le I hn x g hg
  have hf : (0 : ℝ) < I.f := by
    have : 0 < I.f := by
      unfold AutInst.f
      exact Module.finrank_pos
    exact_mod_cast this
  set D := dSum I g.1
  have h1 : tau1 I x * Real.exp (-(D / I.f)) ≤ tau1 I (x * g) := by
    have := Real.exp_le_exp.mpr hl
    rw [Real.exp_log hb, Real.exp_sub, Real.exp_log ha] at this
    rw [Real.exp_neg, ← div_eq_mul_inv]
    exact this
  have h2 : (tau1 I (x * g))⁻¹ ≤ (tau1 I x)⁻¹ * Real.exp (D / I.f) := by
    have hpos : 0 < tau1 I x * Real.exp (-(D / I.f)) := mul_pos ha (Real.exp_pos _)
    calc (tau1 I (x * g))⁻¹ ≤ (tau1 I x * Real.exp (-(D / I.f)))⁻¹ := inv_anti₀ hpos h1
      _ = (tau1 I x)⁻¹ * Real.exp (D / I.f) := by rw [mul_inv, Real.exp_neg, inv_inv]
  have h3 := pow_le_pow_left₀ (inv_nonneg.mpr hb.le) h2 (2 * I.n ^ 2 * I.f)
  have h4 : ((2 * I.n ^ 2 * I.f : ℕ) : ℝ) * (D / I.f) = 2 * (I.n : ℝ) ^ 2 * D := by
    push_cast
    field_simp
  calc _ ≤ _ := h3
    _ = (tau1 I x)⁻¹ ^ (2 * I.n ^ 2 * I.f) * Real.exp (2 * (I.n : ℝ) ^ 2 * D) := by
      rw [mul_pow, ← Real.exp_nat_mul, h4]

/- English proof (translation)
Introduce `B d h hd hn hl hb T hT y f C hy hf hC`. Establish `hcr` using `hf`. Unfold `IsContRep at hf`. Take `⟨hfc, hfinv, -⟩` from `hf`. Take `⟨hphc, hphle, hphint⟩` from `GlobalTheory.Dec.PhMajProof.phMaj B d h hd hl`.

Establish `hwc` using `fun v => weight_condition B h (2 * (B.I.n : ℝ) ^ 2) hn hb le_rfl v`. Establish `hint1 : Integrable (fun g => majPh B d h g * Real.exp (2 * (B.I.n : ℝ) ^ 2 * dSum B.I g)) (muInf B.I)` using `hphint (2 * (B.I.n : ℝ) ^ 2) (by positivity) hwc`. Take `⟨hτpos, hτc, -, -⟩` from `GlobalTheory.TauLipschitz.tauLip B.I hn`. Establish `hadm` using `B.e_adm`. Unfold `AutInst.IsAdmIdem at hadm`.

Take `⟨-, -, -, -, he_supp, -, -⟩` from `hadm`. Establish `hre` using `B.Re_spec`. Unfold `AutInst.IsRConvF at hre`. Establish `hmu : B.I.muA B.μf = (muInf B.I).prod B.μf` using `rfl`. Establish `hmaj0 : ∀ g, 0 ≤ majPh B d h g` using `fun g => (norm_nonneg _).trans (hphle g)`.

Take `⟨Φ, hΦdef⟩ : ∃ Φ : B.I.GA → ℝ, Φ = fun g => max C 0 * (majPh B d h g.1 * Real.exp (2 * (B.I.n : ℝ) ^ 2 * dSum B.I g.1) * ‖B.e g.2‖)` from `⟨_, rfl⟩`. Establish `hΦg : ∀ g, Φ g = max C 0 * (majPh B d h g.1 * Real.exp (2 * (B.I.n : ℝ) ^ 2 * dSum B.I g.1) * ‖B.e g.2‖)` using `fun g => by rw [hΦdef]`. Establish `hΦ0 : ∀ g, 0 ≤ Φ g` using `fun g => by`. Rewrite using `[hΦg]`. Conclude with `mul_nonneg (le_max_right _ _) (mul_nonneg (mul_nonneg (hmaj0 _) (Real.exp_pos _).le) (norm_nonneg _))`.

Establish `hΦint : Integrable Φ (B.I.muA B.μf)`. Rewrite using `[hΦdef, hmu]`. Establish `hre1 : Integrable B.e B.μf` using `hre.1`. Conclude with `(hint1.mul_prod hre1.norm).const_mul _`. Establish `hW0 : ∀ x, 0 ≤ (tau1 B.I x)⁻¹ ^ (2 * B.I.n ^ 2 * B.I.f)` using `fun x => pow_nonneg (inv_nonneg.mpr (hτpos x).le) _`.

Establish `hbound : ∀ x g, ‖phe B d g * f (x * g)‖ ≤ (tau1 B.I x)⁻¹ ^ (2 * B.I.n ^ 2 * B.I.f) * Φ g`. Introduce `x g`. Rewrite using `[show phe B d g = ph B d g.1 * B.e g.2 from rfl]`. Distinguish the cases in `he : B.e g.2 = 0`. Rewrite using `[he, mul_zero, zero_mul, norm_zero]`.

Conclude with `mul_nonneg (hW0 x) (hΦ0 g)`. Establish `h2` using `inv_tau_pow_le B.I hn x g (he_supp g.2 he)`. Establish `h3 : ‖f (x * g)‖ ≤ max C 0 * ((tau1 B.I x)⁻¹ ^ (2 * B.I.n ^ 2 * B.I.f) * Real.exp (2 * (B.I.n : ℝ) ^ 2 * dSum B.I g.1))` using `(hC (x * g)).trans ((mul_le_mul_of_nonneg_right (le_max_left C 0) (hW0 _)).trans (mul_le_mul_of_nonneg_left h2 (le_max_right C 0)))`. Rewrite using `[norm_mul, norm_mul, hΦg]`. Combine the equalities or inequalities in the displayed calculation.

Take `⟨hext1, hext2, -, -⟩` from `GlobalTheory.ExtContRep.ext_ae_eq_contRep B y f hcr`. Establish `hrc` using `(GlobalTheory.ConvKernel.rconv_eq_integral B (phe B d) T hT y).2`. Rewrite `hrc` using `[hy]`. Establish `hshift : ∀ x : B.I.GA, ∀ᵐ g ∂(B.I.muA B.μf), B.I.ext y (x * g) = f (x * g)`. Introduce `x`.

Establish `hmap` using `(GlobalTheory.AdelicUnimod.adelic_unimodular B.I B.μf).1 x`. Distinguish the cases in `hm : AEMeasurable (fun g => x * g) (B.I.muA B.μf)`. Rewrite `hext1` using `[← hmap]`. Conclude with `ae_of_ae_map hm hext1`. Rewrite `hmap` using `[Measure.map_of_not_aemeasurable hm]`.

Rewrite using `[← hmap]`. Simplify using the standard rewrite rules. Establish `hyF : (y : B.I.GA → ℂ) =ᵐ[(B.I.muA B.μf).restrict B.fund] fun x => ∫ g, phe B d g * f (x * g) ∂(B.I.muA B.μf)`. Use `hrc.trans (Filter.Eventually.of_forall fun x => ?_)` and prove the remaining obligations. Conclude with `integral_congr_ae ((hshift x).mono fun g hg => by simp only [hg])`.

Use `haveI : SecondCountableTopology B.I.Gf := (GlobalTheory.CongTop.adelic_topology B.I).2.2.1`. Use `haveI : FirstCountableTopology B.I.Ginf := inferInstance`. Establish `hFc : Continuous fun x => ∫ g, phe B d g * f (x * g) ∂(B.I.muA B.μf)`. Rewrite using `[continuous_iff_continuousAt]`. Introduce `x0`.

Establish `hcw : Continuous fun x => (tau1 B.I x)⁻¹ ^ (2 * B.I.n ^ 2 * B.I.f)` using `(hτc.inv₀ fun x => (hτpos x).ne').pow _`. Establish `hev : ∀ᶠ x in nhds x0, (tau1 B.I x)⁻¹ ^ (2 * B.I.n ^ 2 * B.I.f) < (tau1 B.I x0)⁻¹ ^ (2 * B.I.n ^ 2 * B.I.f) + 1` using `hcw.continuousAt.eventually_lt continuousAt_const (lt_add_one _)`. Use `continuousAt_of_dominated (bound := fun g => ((tau1 B.I x0)⁻¹ ^ (2 * B.I.n ^ 2 * B.I.f) + 1) * Φ g) ?_ ?_ (hΦint.const_mul _) ?_` and prove the remaining obligations. Conclude with `Filter.Eventually.of_forall fun x => hT.1.aestronglyMeasurable.mul (hfc.comp (continuous_const.mul continuous_id)).aestronglyMeasurable`. Use `filter_upwards [hev] with x hx`.

Conclude with `Filter.Eventually.of_forall fun g => (hbound x g).trans (mul_le_mul_of_nonneg_right hx.le (hΦ0 g))`. Conclude with `Filter.Eventually.of_forall fun g => (continuous_const.mul (hfc.comp (continuous_id.mul continuous_const))).continuousAt`. Establish `hcrF : IsContRep B y fun x => ∫ g, phe B d g * f (x * g) ∂(B.I.muA B.μf)`. Unfold `IsContRep`. Use `⟨hFc, fun γ hγ x => ?_, hyF⟩` and prove the remaining obligations.

Simplify using `only [mul_assoc, hfinv γ hγ]`. Establish `hFeq` using `hext2 _ hcrF`. Conclude with `⟨⟨Φ, hΦint, hbound⟩, fun x => (congrFun hFeq x).symm⟩`.
-/
theorem reproducing_fixed : ∀ (B : RowsAut) (d : InfinitePlace B.I.F → ℝ) (h : ℝ), IsDSData B d → 1 ≤ B.I.n → LocDec B h → HBig B 40 h → ∀ T, B.I.IsRConv B.μf B.fund B.R (phe B d) T → ∀ (y : B.I.L2 B.μf B.fund) (f : B.I.GA → ℂ) (C : ℝ), T y = y → IsContRep B y f → (∀ x, ‖f x‖ ≤ C * (tau1 B.I x)⁻¹ ^ (2 * B.I.n ^ 2 * B.I.f)) → (∃ Φ : B.I.GA → ℝ, Integrable Φ (B.I.muA B.μf) ∧ ∀ x g, ‖phe B d g * f (x * g)‖ ≤ (tau1 B.I x)⁻¹ ^ (2 * B.I.n ^ 2 * B.I.f) * Φ g) ∧ ∀ x, f x = ∫ g, phe B d g * f (x * g) ∂(B.I.muA B.μf) := by
  intro B d h hd hn hl hb T hT y f C hy hf hC
  have hcr := hf
  unfold IsContRep at hf
  obtain ⟨hfc, hfinv, -⟩ := hf
  obtain ⟨hphc, hphle, hphint⟩ := GlobalTheory.Dec.PhMajProof.phMaj B d h hd hl
  have hwc := fun v => weight_condition B h (2 * (B.I.n : ℝ) ^ 2) hn hb le_rfl v
  have hint1 : Integrable (fun g => majPh B d h g * Real.exp (2 * (B.I.n : ℝ) ^ 2 * dSum B.I g)) (muInf B.I) :=
    hphint (2 * (B.I.n : ℝ) ^ 2) (by positivity) hwc
  obtain ⟨hτpos, hτc, -, -⟩ := GlobalTheory.TauLipschitz.tauLip B.I hn
  have hadm := B.e_adm
  unfold AutInst.IsAdmIdem at hadm
  obtain ⟨-, -, -, -, he_supp, -, -⟩ := hadm
  have hre := B.Re_spec
  unfold AutInst.IsRConvF at hre
  have hmu : B.I.muA B.μf = (muInf B.I).prod B.μf := rfl
  have hmaj0 : ∀ g, 0 ≤ majPh B d h g := fun g => (norm_nonneg _).trans (hphle g)
  obtain ⟨Φ, hΦdef⟩ : ∃ Φ : B.I.GA → ℝ, Φ = fun g => max C 0 *
      (majPh B d h g.1 * Real.exp (2 * (B.I.n : ℝ) ^ 2 * dSum B.I g.1) * ‖B.e g.2‖) := ⟨_, rfl⟩
  have hΦg : ∀ g, Φ g = max C 0 *
      (majPh B d h g.1 * Real.exp (2 * (B.I.n : ℝ) ^ 2 * dSum B.I g.1) * ‖B.e g.2‖) := fun g => by rw [hΦdef]
  have hΦ0 : ∀ g, 0 ≤ Φ g := fun g => by
    rw [hΦg]
    exact mul_nonneg (le_max_right _ _)
      (mul_nonneg (mul_nonneg (hmaj0 _) (Real.exp_pos _).le) (norm_nonneg _))
  have hΦint : Integrable Φ (B.I.muA B.μf) := by
    rw [hΦdef, hmu]
    have hre1 : Integrable B.e B.μf := hre.1
    exact (hint1.mul_prod hre1.norm).const_mul _
  have hW0 : ∀ x, 0 ≤ (tau1 B.I x)⁻¹ ^ (2 * B.I.n ^ 2 * B.I.f) := fun x => pow_nonneg (inv_nonneg.mpr (hτpos x).le) _
  have hbound : ∀ x g, ‖phe B d g * f (x * g)‖ ≤ (tau1 B.I x)⁻¹ ^ (2 * B.I.n ^ 2 * B.I.f) * Φ g := by
    intro x g
    rw [show phe B d g = ph B d g.1 * B.e g.2 from rfl]
    by_cases he : B.e g.2 = 0
    · rw [he, mul_zero, zero_mul, norm_zero]
      exact mul_nonneg (hW0 x) (hΦ0 g)
    · have h2 := inv_tau_pow_le B.I hn x g (he_supp g.2 he)
      have h3 : ‖f (x * g)‖ ≤ max C 0 * ((tau1 B.I x)⁻¹ ^ (2 * B.I.n ^ 2 * B.I.f) *
          Real.exp (2 * (B.I.n : ℝ) ^ 2 * dSum B.I g.1)) :=
        (hC (x * g)).trans ((mul_le_mul_of_nonneg_right (le_max_left C 0) (hW0 _)).trans
          (mul_le_mul_of_nonneg_left h2 (le_max_right C 0)))
      rw [norm_mul, norm_mul, hΦg]
      calc ‖ph B d g.1‖ * ‖B.e g.2‖ * ‖f (x * g)‖
          ≤ majPh B d h g.1 * ‖B.e g.2‖ * (max C 0 * ((tau1 B.I x)⁻¹ ^ (2 * B.I.n ^ 2 * B.I.f) *
              Real.exp (2 * (B.I.n : ℝ) ^ 2 * dSum B.I g.1))) :=
            mul_le_mul (mul_le_mul_of_nonneg_right (hphle g.1) (norm_nonneg _)) h3 (norm_nonneg _)
              (mul_nonneg (hmaj0 _) (norm_nonneg _))
        _ = _ := by ring
  obtain ⟨hext1, hext2, -, -⟩ := GlobalTheory.ExtContRep.ext_ae_eq_contRep B y f hcr
  have hrc := (GlobalTheory.ConvKernel.rconv_eq_integral B (phe B d) T hT y).2
  rw [hy] at hrc
  have hshift : ∀ x : B.I.GA, ∀ᵐ g ∂(B.I.muA B.μf), B.I.ext y (x * g) = f (x * g) := by
    intro x
    have hmap := (GlobalTheory.AdelicUnimod.adelic_unimodular B.I B.μf).1 x
    by_cases hm : AEMeasurable (fun g => x * g) (B.I.muA B.μf)
    · rw [← hmap] at hext1
      exact ae_of_ae_map hm hext1
    · rw [Measure.map_of_not_aemeasurable hm] at hmap
      rw [← hmap]
      simp
  have hyF : (y : B.I.GA → ℂ) =ᵐ[(B.I.muA B.μf).restrict B.fund]
      fun x => ∫ g, phe B d g * f (x * g) ∂(B.I.muA B.μf) := by
    refine hrc.trans (Filter.Eventually.of_forall fun x => ?_)
    exact integral_congr_ae ((hshift x).mono fun g hg => by simp only [hg])
  haveI : SecondCountableTopology B.I.Gf := (GlobalTheory.CongTop.adelic_topology B.I).2.2.1
  haveI : FirstCountableTopology B.I.Ginf := inferInstance
  have hFc : Continuous fun x => ∫ g, phe B d g * f (x * g) ∂(B.I.muA B.μf) := by
    rw [continuous_iff_continuousAt]
    intro x0
    have hcw : Continuous fun x => (tau1 B.I x)⁻¹ ^ (2 * B.I.n ^ 2 * B.I.f) :=
      (hτc.inv₀ fun x => (hτpos x).ne').pow _
    have hev : ∀ᶠ x in nhds x0, (tau1 B.I x)⁻¹ ^ (2 * B.I.n ^ 2 * B.I.f) < (tau1 B.I x0)⁻¹ ^ (2 * B.I.n ^ 2 * B.I.f) + 1 :=
      hcw.continuousAt.eventually_lt continuousAt_const (lt_add_one _)
    refine continuousAt_of_dominated (bound := fun g => ((tau1 B.I x0)⁻¹ ^ (2 * B.I.n ^ 2 * B.I.f) + 1) * Φ g)
      ?_ ?_ (hΦint.const_mul _) ?_
    · exact Filter.Eventually.of_forall fun x =>
        hT.1.aestronglyMeasurable.mul (hfc.comp (continuous_const.mul continuous_id)).aestronglyMeasurable
    · filter_upwards [hev] with x hx
      exact Filter.Eventually.of_forall fun g =>
        (hbound x g).trans (mul_le_mul_of_nonneg_right hx.le (hΦ0 g))
    · exact Filter.Eventually.of_forall fun g =>
        (continuous_const.mul (hfc.comp (continuous_id.mul continuous_const))).continuousAt
  have hcrF : IsContRep B y fun x => ∫ g, phe B d g * f (x * g) ∂(B.I.muA B.μf) := by
    unfold IsContRep
    refine ⟨hFc, fun γ hγ x => ?_, hyF⟩
    simp only [mul_assoc, hfinv γ hγ]
  have hFeq := hext2 _ hcrF
  exact ⟨⟨Φ, hΦint, hbound⟩, fun x => (congrFun hFeq x).symm⟩

end GlobalTheory.ReproducingFixed

import Mathlib
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.LatIntZero
import Formalism.LocalToGlobal.KernelLattices.LateralTheory
import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.IsAdmissibleFlagPairOfUnitriangularLeftAutomorph
import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.QuasiPeriodConstUnique
import Formalism.LocalToGlobal.GlobalTheory.GL3.PStdChar
import Formalism.LocalToGlobal.GlobalTheory.GL3.PStdOK
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.CpSeriesBoundedThetaLevelValueOneStatement
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.CmBaseFieldIntegersAndCurveIdealFactsStatement
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.LatticeJetsAreBoundedMomentsPullbackStatement
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.LatticeJetsAreBoundedMomentsOfSpanImagQuadraticStatement
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.JetsAreBoundedMeasureMomentsOfChartCoeffBoundStatement

open NumberField Formalism.BasicNotions Classical Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.L2.Ker GlobalTheory.MomN

noncomputable section

namespace GlobalTheory.MomN

open GlobalTheory.MomOne
open scoped ComplexConjugate

/- English proof (translation)
Introduce `D cc δ B hcc _ q _ hq2 hjac hcop ι δ₀ θ Ω hPer`. Take `⟨hdp, hd16, hOK, -, hlat⟩` from `GlobalTheory.T.cmBaseField_integers_and_curveIdeal_facts D`. Take `⟨hTh, -, -, -, -, -, M, hMι, hMOK, hMch⟩` from `hPer`. Establish `hcc0 : cc ≠ ⊥` using `hcc.1`. Take `⟨hA, hmem⟩` from `hlat cc δ hcc0`.

Establish `hmem1` using `(hlat ⊤ 1 top_ne_bot).2`. Establish `hqp : q.Prime` using `Fact.out`. Establish `hN0 : Ideal.absNorm cc ≠ 0`. Rewrite using `[Ne, Ideal.absNorm_eq_zero_iff]`. Conclude with `hcc0`.

Establish `hNc : ((Ideal.absNorm cc : ℕ) : ℂ) ≠ 0` using `by exact_mod_cast hN0`. Establish `hsd : 0 < Real.sqrt D.host.d` using `Real.sqrt_pos.2 (by exact_mod_cast hdp.pos)`. Establish `hAF : Formalism.L2.Th1.F.area B.L = Complex.normSq δ * (Ideal.absNorm cc : ℝ) * Real.sqrt D.host.d / 2`. Rewrite using `[← hA]`. Conclude with `B.areaOK.symm`.

Establish `hApos : 0 < Formalism.L2.Th1.F.area B.L` using `Formalism.L2.Th1.F.PeriodAreaSignLemmas.area_pos B.L`. Establish `hδ0 : δ ≠ 0`. Introduce and unpack `rfl`. Rewrite `hApos` using `[hAF]`. Simplify using `at hApos`.

Establish `hmemL : ∀ x, x ∈ B.L.lattice ↔ x ∈ lamOf D cc δ` using `Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.SO.mem_iff B`. Take `⟨hGd0, hG00, -, hzero, hlaw⟩` from `Formalism.L2.Th1.F.th0Basic B.L B.ω₀ B.omega_mem (Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.SO.half B)`. Use `set N : ℕ := Ideal.absNorm cc with hN`. Use `set G : ℂ → ℂ := fun z => B.th0 (δ * N * z) with hG`. Establish `hGd : Differentiable ℂ G`.

Establish `: Differentiable ℂ fun z : ℂ => δ * N * z` using `by fun_prop`. Conclude with `hGd0.comp this`. Establish `hG0 : G 0 = 1` using `by simp only [hG, mul_zero]; exact hG00`. Establish `hsplit : Split D.host.d q` using `Or.inr ⟨hq2, hjac⟩`. Establish `hzer : ∀ z, G z = 0 → PrimeTo D.host.d q z`.

Introduce `z hz`. Establish `h1 : δ * N * z + B.ω₀ / 2 ∈ B.L.lattice` using `(hzero _).1 hz`. Establish `h2 : δ * ((2 * N : ℕ) * z) ∈ B.L.lattice`. Establish `e : δ * ((2 * N : ℕ) * z) = (δ * N * z + B.ω₀ / 2) + (δ * N * z + B.ω₀ / 2) - B.ω₀` using `by push_cast; ring`. Rewrite using `[e]`.

Conclude with `B.L.lattice.sub_mem (B.L.lattice.add_mem h1 h1) B.omega_mem`. Take `⟨y, -, hy⟩` from `(hmem _).1 ((hmemL _).1 h2)`. Use `⟨2 * N, Nat.mul_pos two_pos (Nat.pos_of_ne_zero hN0), Nat.Coprime.mul ?_ hcop, ?_⟩` and prove the remaining obligations. Conclude with `(Nat.coprime_primes Nat.prime_two hqp).2 (Ne.symm hq2)`. Conclude with `(hOK _).2 ⟨y, mul_left_cancel₀ hδ0 hy⟩`.

Establish `hkey : ∀ z w : ℂ, Formalism.L2.Th1.F.herm B.L (δ * N * z) (δ * N * w) = N * h1 D.host.d z w`. Introduce `z w`. Establish `hc : δ * conj δ = (Complex.normSq δ : ℂ)` using `Complex.mul_conj δ`. Establish `hδn : (Complex.normSq δ : ℂ) ≠ 0` using `by exact_mod_cast (Complex.normSq_pos.2 hδ0).ne'`. Establish `hsc : ((Real.sqrt D.host.d : ℝ) : ℂ) ≠ 0` using `by exact_mod_cast hsd.ne'`.

Establish `hA0 : ((Complex.normSq δ * (N : ℝ) * Real.sqrt D.host.d / 2 : ℝ) : ℂ) ≠ 0`. Establish `: 0 < Complex.normSq δ * (N : ℝ) * Real.sqrt D.host.d / 2`. Use `Complex.normSq_pos.2 hδ0` as an intermediate fact. Establish `: (0 : ℝ) < N` using `by exact_mod_cast Nat.pos_of_ne_zero hN0`. Check the signs of the components of the expression.

Conclude with `this.ne'` after adjusting the coercions. Establish `hs2 : (2 / ((Real.sqrt D.host.d : ℝ) : ℂ)) * ((Real.sqrt D.host.d : ℝ) : ℂ) = 2`. Clear the denominators using the available nonvanishing facts. Rewrite using `[Formalism.L2.Th1.F.herm, hAF, h1, div_eq_iff hA0]`. Simplify using `only [map_mul, Complex.conj_natCast]`.

Use `push_cast`. Take the linear combination `((N : ℂ) ^ 2 * z * conj w) * hc - ((N : ℂ) ^ 2 * z * conj w * (Complex.normSq δ : ℂ) / 2) * hs2`. Establish `hlaw' : ∀ x, InOK D.host.d x → ∀ z, G (z + x) * (Complex.exp ((Real.pi : ℂ) * Complex.I * ((Complex.normSq x : ℝ) : ℂ)) * Complex.exp (-(Real.pi : ℂ) * h1 D.host.d z x - (Real.pi : ℂ) / 2 * h1 D.host.d x x)) ^ N = G z`. Introduce `x hx z`. Take `⟨o, ho⟩` from `(hOK x).1 hx`.

Establish `hω : δ * N * x ∈ B.L.lattice`. Use `(hmemL _).2 ((hmem _).2 ⟨(N : 𝓞 D.host.K) * o, cc.mul_mem_right _ (Ideal.absNorm_mem cc), ?_⟩)` and prove the remaining obligations. Rewrite using `[ho]`. Use `push_cast`. Rewrite using `[map_mul, map_natCast]`.

Expand and normalize the polynomial expressions, which then agree. Establish `hl` using `hlaw _ hω (δ * N * z)`. Rewrite `hl` using `[← Formalism.L2.Th1.F.thetaZeroCharacter]`. Rewrite `hl` using `[← Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.SC.char_eq (Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.SO.hst B) B.omega_mem (Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.SO.hθ B) (Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.SO.hθ' B) (b …`. Establish `ha` using `(Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.SC.semi (Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.SO.hst B)).2.1 _ hω`.

Establish `hq1 : Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.SC.q1 B.L D.host.d (δ * N * x) = N * Complex.normSq x`. Rewrite using `[Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.SC.q1, hkey, h1, Complex.mul_conj]`. Establish `: ((N : ℂ) * (((2 / Real.sqrt D.host.d : ℝ) : ℂ) * ((Complex.normSq x : ℝ) : ℂ))).re = N * (2 / Real.sqrt D.host.d) * Complex.normSq x`. Rewrite using `[← Complex.ofReal_natCast, ← Complex.ofReal_mul, ← Complex.ofReal_mul, Complex.ofReal_re]`. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[this]`. Clear the denominators using the available nonvanishing facts. Establish `hapow : Complex.exp ((Real.pi : ℂ) * Complex.I * ((Complex.normSq x : ℝ) : ℂ)) ^ N = Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.SC.aa B.L D.host.d (δ * N * x)`. Rewrite using `[Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.SC.aa, hq1, ← Complex.exp_nat_mul]`. Use `congr 1`.

Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Establish `e1 : G (z + x) = B.th0 (δ * N * z + δ * N * x)`. Simplify using `only [hG]`. Use `congr 1`.

Expand and normalize the polynomial expressions, which then agree. Establish `e2 : G z = B.th0 (δ * N * z)` using `rfl`. Rewrite using `[e1, e2, Base.th0, hl, mul_pow, hapow, ← Complex.exp_nat_mul]`. Use `set a := Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.SC.aa B.L D.host.d (δ * N * x)`. Apply the tactic sequence `have haa : a * a = 1 := by rcases ha with h | h <;> rw [h] <;> norm_num`.

Establish `hE : Complex.exp ((Real.pi : ℂ) * (N * h1 D.host.d z x) + (Real.pi : ℂ) * (N * h1 D.host.d x x) / 2) * Complex.exp (N * (-(Real.pi : ℂ) * h1 D.host.d z x - (Real.pi : ℂ) / 2 * h1 D.host.d x x)) = 1`. Rewrite using `[← Complex.exp_add, ← Complex.exp_zero]`. Use `congr 1`. Expand and normalize the polynomial expressions, which then agree. Take the linear combination `(Complex.exp ((Real.pi : ℂ) * (N * h1 D.host.d z x) + (Real.pi : ℂ) * (N * h1 D.host.d x x) / 2) * Complex.exp (N * (-(Real.pi : ℂ) * h1 D.host.d z x - (Real.pi : ℂ) / 2 * h1 D.host.d x x)) * Formalism.L2.Th1.F.th0 B.L (B.ω₀ / 2) (δ * N * z)) * haa + (Formalism.L2.Th1.F.th0 B.L ( …`.

Establish `hbd : Bd 1 (hat ι (PowerSeries.C (Ω / ι δ₀) * logS) G)`. Use `GlobalTheory.T.cpSeries_bounded_theta_level_value_one D.host.d q M (Ω / ι δ₀) θ G N hdp hd16 hsplit hq2 hMOK hMch hTh hGd hG0 hlaw' hzer` as an intermediate fact. Rewrite `this` using `[hMι]`. Then use the resulting hypothesis. Establish `hmom` using `GlobalTheory.T.jetsAreBoundedMeasureMoments_of_chart_coeff_bound q ι (Ω / ι δ₀) G hGd hbd`. Establish `hspan : LatInt ι (Ω / ι δ₀) (lamOf D ⊤ 1) G`.

Use `GlobalTheory.T.latticeJetsAreBoundedMoments_of_span_imagQuadratic q ι ℂ D.host.d (Ω / ι δ₀) (lamOf D ⊤ 1) Unit (fun _ => (1 : ℂ)) G hdp hd16 hsplit ?_ ?_` and prove the remaining obligations. Introduce `x hx`. Take `⟨y, -, hy⟩` from `(hmem1 x).1 hx`. Use `⟨1, Nat.coprime_one_left _, fun _ => x, fun _ => (hOK x).2 ⟨y, by rw [hy, one_mul]⟩, ?_⟩` and prove the remaining obligations. Simplify using the standard rewrite rules.

Use `hmom using 2` and compare the differences between its conclusion and the goal. Simplify using the standard rewrite rules. Establish `hδN : δ * (N : ℂ) ≠ 0` using `mul_ne_zero hδ0 hNc`. Establish `hpull` using `GlobalTheory.T.latticeJetsAreBoundedMoments_pullback q ι ℂ ℂ (Ω / ι δ₀) (lamOf D ⊤ 1) (lamOf D cc δ) ((δ * N)⁻¹ • ContinuousLinearMap.id ℂ ℂ) G hGd.contDiff ?_ hspan`. Use `hpull using 1` and compare the differences between its conclusion and the goal.

Use function extensionality and compare the values at `z`. Simplify using `only [hG, ContinuousLinearMap.smul_apply, ContinuousLinearMap.id_apply, smul_eq_mul]`. Use `congr 1`. Clear the denominators using the available nonvanishing facts. Introduce `x hx`.

Take `⟨y, -, hy⟩` from `(hmem x).1 hx`. Use `⟨N, hcop, (hmem1 _).2 ⟨y, trivial, ?_⟩⟩` and prove the remaining obligations. Simplify using `only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.id_apply, smul_eq_mul, nsmul_eq_mul, hy]`. Clear the denominators using the available nonvanishing facts.
-/
theorem latInt_th0_of_split_prime : ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (B : Base D cc δ), IsCurveIdeal D cc → IsDiscriminantTwelfthRootOfIdealLattice D cc δ → ∀ (q : ℕ) [Fact q.Prime], q ≠ 2 → jacobiSym (-(D.host.d : ℤ)) q = 1 → Nat.Coprime (Ideal.absNorm cc) q → ∀ (ι : ℂ ≃+* ℂ_[q]) (δ₀ : ℂ) (θ : ℂ → ℂ) (Ω : ℂ_[q]), Per D.host.d ι δ₀ θ Ω → LatInt ι (Ω / ι δ₀) (lamOf D cc δ) B.th0 := by
  intro D cc δ B hcc _ q _ hq2 hjac hcop ι δ₀ θ Ω hPer
  obtain ⟨hdp, hd16, hOK, -, hlat⟩ := GlobalTheory.T.cmBaseField_integers_and_curveIdeal_facts D
  obtain ⟨hTh, -, -, -, -, -, M, hMι, hMOK, hMch⟩ := hPer
  have hcc0 : cc ≠ ⊥ := hcc.1
  obtain ⟨hA, hmem⟩ := hlat cc δ hcc0
  have hmem1 := (hlat ⊤ 1 top_ne_bot).2
  have hqp : q.Prime := Fact.out
  have hN0 : Ideal.absNorm cc ≠ 0 := by
    rw [Ne, Ideal.absNorm_eq_zero_iff]; exact hcc0
  have hNc : ((Ideal.absNorm cc : ℕ) : ℂ) ≠ 0 := by exact_mod_cast hN0
  have hsd : 0 < Real.sqrt D.host.d := Real.sqrt_pos.2 (by exact_mod_cast hdp.pos)
  have hAF : Formalism.L2.Th1.F.area B.L = Complex.normSq δ * (Ideal.absNorm cc : ℝ) * Real.sqrt D.host.d / 2 := by
    rw [← hA]; exact B.areaOK.symm
  have hApos : 0 < Formalism.L2.Th1.F.area B.L := Formalism.L2.Th1.F.PeriodAreaSignLemmas.area_pos B.L
  have hδ0 : δ ≠ 0 := by
    rintro rfl
    rw [hAF] at hApos
    simp at hApos
  have hmemL : ∀ x, x ∈ B.L.lattice ↔ x ∈ lamOf D cc δ := Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.SO.mem_iff B
  obtain ⟨hGd0, hG00, -, hzero, hlaw⟩ :=
    Formalism.L2.Th1.F.th0Basic B.L B.ω₀ B.omega_mem (Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.SO.half B)
  set N : ℕ := Ideal.absNorm cc with hN
  set G : ℂ → ℂ := fun z => B.th0 (δ * N * z) with hG
  have hGd : Differentiable ℂ G := by
    have : Differentiable ℂ fun z : ℂ => δ * N * z := by fun_prop
    exact hGd0.comp this
  have hG0 : G 0 = 1 := by simp only [hG, mul_zero]; exact hG00
  have hsplit : Split D.host.d q := Or.inr ⟨hq2, hjac⟩

  have hzer : ∀ z, G z = 0 → PrimeTo D.host.d q z := by
    intro z hz
    have h1 : δ * N * z + B.ω₀ / 2 ∈ B.L.lattice := (hzero _).1 hz
    have h2 : δ * ((2 * N : ℕ) * z) ∈ B.L.lattice := by
      have e : δ * ((2 * N : ℕ) * z) = (δ * N * z + B.ω₀ / 2) + (δ * N * z + B.ω₀ / 2) - B.ω₀ := by
        push_cast; ring
      rw [e]
      exact B.L.lattice.sub_mem (B.L.lattice.add_mem h1 h1) B.omega_mem
    obtain ⟨y, -, hy⟩ := (hmem _).1 ((hmemL _).1 h2)
    refine ⟨2 * N, Nat.mul_pos two_pos (Nat.pos_of_ne_zero hN0), Nat.Coprime.mul ?_ hcop, ?_⟩
    · exact (Nat.coprime_primes Nat.prime_two hqp).2 (Ne.symm hq2)
    · exact (hOK _).2 ⟨y, mul_left_cancel₀ hδ0 hy⟩

  have hkey : ∀ z w : ℂ, Formalism.L2.Th1.F.herm B.L (δ * N * z) (δ * N * w) = N * h1 D.host.d z w := by
    intro z w
    have hc : δ * conj δ = (Complex.normSq δ : ℂ) := Complex.mul_conj δ
    have hδn : (Complex.normSq δ : ℂ) ≠ 0 := by exact_mod_cast (Complex.normSq_pos.2 hδ0).ne'
    have hsc : ((Real.sqrt D.host.d : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hsd.ne'
    have hA0 : ((Complex.normSq δ * (N : ℝ) * Real.sqrt D.host.d / 2 : ℝ) : ℂ) ≠ 0 := by
      have : 0 < Complex.normSq δ * (N : ℝ) * Real.sqrt D.host.d / 2 := by
        have := Complex.normSq_pos.2 hδ0
        have : (0 : ℝ) < N := by exact_mod_cast Nat.pos_of_ne_zero hN0
        positivity
      exact_mod_cast this.ne'
    have hs2 : (2 / ((Real.sqrt D.host.d : ℝ) : ℂ)) * ((Real.sqrt D.host.d : ℝ) : ℂ) = 2 := by
      field_simp
    rw [Formalism.L2.Th1.F.herm, hAF, h1, div_eq_iff hA0]
    simp only [map_mul, Complex.conj_natCast]
    push_cast
    linear_combination ((N : ℂ) ^ 2 * z * conj w) * hc - ((N : ℂ) ^ 2 * z * conj w * (Complex.normSq δ : ℂ) / 2) * hs2
  have hlaw' : ∀ x, InOK D.host.d x → ∀ z, G (z + x) * (Complex.exp ((Real.pi : ℂ) * Complex.I * ((Complex.normSq x : ℝ) : ℂ)) * Complex.exp (-(Real.pi : ℂ) * h1 D.host.d z x - (Real.pi : ℂ) / 2 * h1 D.host.d x x)) ^ N = G z := by
    intro x hx z
    obtain ⟨o, ho⟩ := (hOK x).1 hx
    have hω : δ * N * x ∈ B.L.lattice := by
      refine (hmemL _).2 ((hmem _).2 ⟨(N : 𝓞 D.host.K) * o, cc.mul_mem_right _ (Ideal.absNorm_mem cc), ?_⟩)
      rw [ho]; push_cast; rw [map_mul, map_natCast]; ring
    have hl := hlaw _ hω (δ * N * z)
    rw [← Formalism.L2.Th1.F.thetaZeroCharacter] at hl
    rw [← Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.SC.char_eq (Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.SO.hst B) B.omega_mem (Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.SO.hθ B)
      (Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.SO.hθ' B) (by omega) _ hω, hkey, hkey] at hl
    have ha := (Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.SC.semi (Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.SO.hst B)).2.1 _ hω
    have hq1 : Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.SC.q1 B.L D.host.d (δ * N * x) = N * Complex.normSq x := by
      rw [Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.SC.q1, hkey, h1, Complex.mul_conj]
      have : ((N : ℂ) * (((2 / Real.sqrt D.host.d : ℝ) : ℂ) * ((Complex.normSq x : ℝ) : ℂ))).re
          = N * (2 / Real.sqrt D.host.d) * Complex.normSq x := by
        rw [← Complex.ofReal_natCast, ← Complex.ofReal_mul, ← Complex.ofReal_mul, Complex.ofReal_re]; ring
      rw [this]; field_simp
    have hapow : Complex.exp ((Real.pi : ℂ) * Complex.I * ((Complex.normSq x : ℝ) : ℂ)) ^ N
        = Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.SC.aa B.L D.host.d (δ * N * x) := by
      rw [Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.SC.aa, hq1, ← Complex.exp_nat_mul]
      congr 1; push_cast; ring
    have e1 : G (z + x) = B.th0 (δ * N * z + δ * N * x) := by
      simp only [hG]; congr 1; ring
    have e2 : G z = B.th0 (δ * N * z) := rfl
    rw [e1, e2, Base.th0, hl, mul_pow, hapow, ← Complex.exp_nat_mul]
    set a := Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.SC.aa B.L D.host.d (δ * N * x)
    have haa : a * a = 1 := by rcases ha with h | h <;> rw [h] <;> norm_num
    have hE : Complex.exp ((Real.pi : ℂ) * (N * h1 D.host.d z x) + (Real.pi : ℂ) * (N * h1 D.host.d x x) / 2)
        * Complex.exp (N * (-(Real.pi : ℂ) * h1 D.host.d z x - (Real.pi : ℂ) / 2 * h1 D.host.d x x)) = 1 := by
      rw [← Complex.exp_add, ← Complex.exp_zero]; congr 1; ring
    linear_combination (Complex.exp ((Real.pi : ℂ) * (N * h1 D.host.d z x) + (Real.pi : ℂ) * (N * h1 D.host.d x x) / 2)
        * Complex.exp (N * (-(Real.pi : ℂ) * h1 D.host.d z x - (Real.pi : ℂ) / 2 * h1 D.host.d x x))
        * Formalism.L2.Th1.F.th0 B.L (B.ω₀ / 2) (δ * N * z)) * haa
      + (Formalism.L2.Th1.F.th0 B.L (B.ω₀ / 2) (δ * N * z)) * hE

  have hbd : Bd 1 (hat ι (PowerSeries.C (Ω / ι δ₀) * logS) G) := by
    have := GlobalTheory.T.cpSeries_bounded_theta_level_value_one D.host.d q M (Ω / ι δ₀) θ G N hdp hd16 hsplit hq2 hMOK hMch hTh hGd hG0 hlaw' hzer
    rwa [hMι] at this
  have hmom := GlobalTheory.T.jetsAreBoundedMeasureMoments_of_chart_coeff_bound q ι (Ω / ι δ₀) G hGd hbd
  have hspan : LatInt ι (Ω / ι δ₀) (lamOf D ⊤ 1) G := by
    refine GlobalTheory.T.latticeJetsAreBoundedMoments_of_span_imagQuadratic q ι ℂ D.host.d (Ω / ι δ₀) (lamOf D ⊤ 1) Unit (fun _ => (1 : ℂ)) G hdp hd16 hsplit ?_ ?_
    · intro x hx
      obtain ⟨y, -, hy⟩ := (hmem1 x).1 hx
      refine ⟨1, Nat.coprime_one_left _, fun _ => x, fun _ => (hOK x).2 ⟨y, by rw [hy, one_mul]⟩, ?_⟩
      simp
    · convert hmom using 2
      simp
  have hδN : δ * (N : ℂ) ≠ 0 := mul_ne_zero hδ0 hNc
  have hpull := GlobalTheory.T.latticeJetsAreBoundedMoments_pullback q ι ℂ ℂ (Ω / ι δ₀) (lamOf D ⊤ 1) (lamOf D cc δ)
    ((δ * N)⁻¹ • ContinuousLinearMap.id ℂ ℂ) G hGd.contDiff ?_ hspan
  · convert hpull using 1
    funext z
    simp only [hG, ContinuousLinearMap.smul_apply, ContinuousLinearMap.id_apply, smul_eq_mul]
    congr 1
    field_simp
  · intro x hx
    obtain ⟨y, -, hy⟩ := (hmem x).1 hx
    refine ⟨N, hcop, (hmem1 _).2 ⟨y, trivial, ?_⟩⟩
    simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.id_apply, smul_eq_mul, nsmul_eq_mul, hy]
    field_simp

end GlobalTheory.MomN

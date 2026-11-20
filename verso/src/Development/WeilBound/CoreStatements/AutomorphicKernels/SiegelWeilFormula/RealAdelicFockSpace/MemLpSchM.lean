import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.RealAdelicFockSpace.JnArcFin
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.FockSpaces.IntSch
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.FockSpaces.LocAddOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicSchwartzMemL2
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchroedingerPreservesAdelicSchwartz

noncomputable section

open scoped TensorProduct NNReal Matrix SchwartzMap Classical InnerProductSpace
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl PositivityTheory.Rg.Sw

namespace PositivityTheory.SiegelWeilFormula.KFP

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

/- English proof (translation)
Substitute `hm` using the available equality. Conclude with `GlobalTheory.WeilM.schA_memLp_two F κ μ hμ φ hφ`.
-/
theorem memLpSchA {κ : Type} [Fintype κ] (m : MeasurableSpace (κ → AF F)) (hm : m = borel _)
    (μ : @Measure (κ → AF F) m) (hμ : @Measure.IsAddHaarMeasure _ _ _ m μ) {φ : (κ → AF F) → ℂ}
    (hφ : φ ∈ schA F κ) : MemLp φ 2 μ := by
  subst hm
  exact GlobalTheory.WeilM.schA_memLp_two F κ μ hμ φ hφ

/- English proof (translation)
Take `⟨i1, i2, i3, i4⟩` from `(PositivityTheory.ThKCT.ideleTop F E).1`. Use `haveI : BorelSpace (AE F E) := ⟨rfl⟩`. Use `haveI : BorelSpace (Mx F E d.m d.n) := inferInstanceAs (BorelSpace (Fin d.m → Fin d.n → AE F E))`. Use `haveI : IsTopologicalAddGroup (Mx F E d.m d.n) := inferInstanceAs (IsTopologicalAddGroup (Fin d.m → Fin d.n → AE F E))`. Use `haveI := GlobalTheory.AdelicUnitaryTop.locallyCompact_adele F`.

Use `haveI := GlobalTheory.AdelicUnitaryTop.secondCountable_adele F`. Use `haveI : BorelSpace (AF F) := ⟨rfl⟩`. Use `haveI : BorelSpace (Fin d.m × Fin d.n × Fin 2 → AF F) := Pi.borelSpace`. Set `e : (Fin d.m × Fin d.n × Fin 2 → AF F) ≃ᵐ Mx F E d.m d.n` to `(KFock.cmbE d).toHomeomorph.toMeasurableEquiv`. Use `haveI : (Measure.map e.symm ν).IsAddHaarMeasure := ContinuousAddEquiv.isAddHaarMeasure_map ν (KFock.cmbE d).symm`.

Establish `h1 : MemLp (f ∘ e) 2 (Measure.map e.symm ν)`. Establish `hf' : f ∘ d.cmb ∈ schA F (Fin d.m × Fin d.n × Fin 2)` using `Submodule.mem_comap.mp hf`. Conclude with `memLpSchA _ BorelSpace.measurable_eq _ inferInstance hf'`. Establish `h2` using `(e.memLp_map_measure_iff).2 h1`. Rewrite `h2` using `[MeasurableEquiv.map_map_symm]`. Then use the resulting hypothesis.
-/
theorem memLp_schM (d : SD σ) (ν : Measure (Mx F E d.m d.n)) (hν : ν.IsAddHaarMeasure) {f : Mx F E d.m d.n → ℂ}
    (hf : f ∈ d.schM) : MemLp f 2 ν := by
  obtain ⟨i1, i2, i3, i4⟩ := (PositivityTheory.ThKCT.ideleTop F E).1
  haveI : BorelSpace (AE F E) := ⟨rfl⟩
  haveI : BorelSpace (Mx F E d.m d.n) := inferInstanceAs (BorelSpace (Fin d.m → Fin d.n → AE F E))
  haveI : IsTopologicalAddGroup (Mx F E d.m d.n) := inferInstanceAs (IsTopologicalAddGroup (Fin d.m → Fin d.n → AE F E))
  haveI := GlobalTheory.AdelicUnitaryTop.locallyCompact_adele F
  haveI := GlobalTheory.AdelicUnitaryTop.secondCountable_adele F
  haveI : BorelSpace (AF F) := ⟨rfl⟩
  haveI : BorelSpace (Fin d.m × Fin d.n × Fin 2 → AF F) := Pi.borelSpace
  let e : (Fin d.m × Fin d.n × Fin 2 → AF F) ≃ᵐ Mx F E d.m d.n := (KFock.cmbE d).toHomeomorph.toMeasurableEquiv
  haveI : (Measure.map e.symm ν).IsAddHaarMeasure := ContinuousAddEquiv.isAddHaarMeasure_map ν (KFock.cmbE d).symm
  have h1 : MemLp (f ∘ e) 2 (Measure.map e.symm ν) := by
    have hf' : f ∘ d.cmb ∈ schA F (Fin d.m × Fin d.n × Fin 2) := Submodule.mem_comap.mp hf
    exact memLpSchA _ BorelSpace.measurable_eq _ inferInstance hf'
  have h2 := (e.memLp_map_measure_iff).2 h1
  rwa [MeasurableEquiv.map_map_symm] at h2

variable {d : SD σ}

def TL (d : SD σ) : d.Fn →ₗ[ℂ] (Mx F E d.m d.n → ℂ) where
  toFun := d.T
  map_add' := KFock.T_add d
  map_smul' a Φ := KFock.T_smul d a Φ

/- English proof (translation)
Use function extensionality and compare the values at `x`. Simplify using `only [Darboux.rho, schr, Pi.smul_apply, smul_eq_mul]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem rho_smul (w : Matrix (Fin d.m) (Fin d.n ⊕ Fin d.n) (AE F E)) (c : ℂ) (φ : d.Fn) :
    d.dd.rho d.B.ψ w (c • φ) = c • d.dd.rho d.B.ψ w φ := by
  funext x
  simp only [Darboux.rho, schr, Pi.smul_apply, smul_eq_mul]
  ring

/- English proof (translation)
Establish `hψ : IsStd d.B.ψ` using `d.ok.good.std`. Establish `hS` using `d.ok.dbl.weil.2.1.toIsSplitting`. Establish `hrho : ∀ w, ∀ φ ∈ d.sch, d.dd.rho d.B.ψ w φ ∈ d.sch` using `fun w φ hφ => GlobalTheory.SchrKeepsSchA.schr_mem_schA F d.B.ψ hψ d.κ _ φ hφ`. Establish `hpow : ∀ i : ℕ, d.om (k ^ i) Ω = χ ^ i • Ω`. Introduce `i`.

Proceed by induction on `i with`. Consider the case `zero => simp`. Consider the case `succ i ih`. Rewrite using `[pow_succ, map_mul, Module.End.mul_apply, hk, map_smul, ih, smul_smul, pow_succ, mul_comm]`. Establish `hact : ∀ i : ℕ, actB (cA σ) (k ^ i) (actB (cA σ) (k⁻¹ ^ i) v) = v`.

Introduce `i`. Establish `e1 : k ^ i * k⁻¹ ^ i = 1` using `by rw [inv_pow, mul_inv_cancel]`. Simplify using `only [actB]`. Rewrite using `[Matrix.mul_assoc, ← Matrix.transpose_mul, ← Units.val_mul, ← Subgroup.coe_mul, e1]`. Simplify using the standard rewrite rules.

Use `set Ψ := d.dd.rho d.B.ψ v Ω with hΨdef`. Establish `hΨ : Ψ ∈ d.sch` using `hrho v Ω hΩ`. Establish `hterm : ∀ i : ℕ, (star χ)⁻¹ ^ i * B ν Φ (d.dd.rho d.B.ψ (actB (cA σ) (k⁻¹ ^ i) v) Ω) = B ν (d.om (k ^ i) Φ) Ψ`. Introduce `i`. Establish `h1` using `hU F E σ d ν hν (k ^ i) Φ hΦ (d.dd.rho d.B.ψ (actB (cA σ) (k⁻¹ ^ i) v) Ω) (hrho (actB (cA σ) (k⁻¹ ^ i) v) Ω hΩ)`.

Establish `h2 : d.om (k ^ i) (d.dd.rho d.B.ψ (actB (cA σ) (k⁻¹ ^ i) v) Ω) = χ ^ i • Ψ`. Rewrite using `[hS.impl _ _ Ω hΩ, hact, hpow, rho_smul]`. Rewrite `h1` using `[h2, KFock.T_smul]`. Unfold `B`. Rewrite using `[← h1]`.

Establish `e3 : ∀ X, d.T (d.om (k ^ i) Φ) X * star ((χ ^ i • d.T Ψ) X) = star χ ^ i * (d.T (d.om (k ^ i) Φ) X * star (d.T Ψ X))`. Introduce `X`. Rewrite using `[Pi.smul_apply, smul_eq_mul, star_mul', star_pow]`. Expand and normalize the polynomial expressions, which then agree. Repeatedly rewrite using `[e3]`.

Rewrite using `[integral_const_mul, ← mul_assoc, ← mul_pow, inv_mul_cancel₀ (star_ne_zero.2 hχ), one_pow, one_mul]`. Establish `hint : ∀ i : ℕ, Integrable (fun X => d.T (d.om (k ^ i) Φ) X * star (d.T Ψ X)) ν`. Introduce `i`. Establish `hA` using `memLp_schM d ν hν ((hT.1 F E σ d).1 (d.om (k ^ i) Φ) (hS.pres (k ^ i) Φ hΦ))`. Establish `hB` using `(memLp_schM d ν hν ((hT.1 F E σ d).1 Ψ hΨ)).star`.

Conclude with `hA.integrable_mul hB`. Combine the equalities or inequalities in the displayed calculation. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[mul_assoc, hterm]`. Use `_ = ∫ X, ∑ i ∈ Finset.range (q.natDegree + 1), q.coeff i * (d.T (d.om (k ^ i) Φ) X * star (d.T Ψ X)) ∂ν := by`.

Unfold `B`. Rewrite using `[integral_finsetSum _ fun i _ => (hint i).const_mul _]`. Repeatedly rewrite using `[integral_const_mul]`. Use `_ = ∫ X, TL d (∑ i ∈ Finset.range (q.natDegree + 1), q.coeff i • d.om (k ^ i) Φ) X * star (d.T Ψ X) ∂ν := by`. Use `congr 1`.

Use function extensionality and compare the values at `X`. Rewrite using `[map_sum, Finset.sum_apply, Finset.sum_mul]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[map_smul, Pi.smul_apply, smul_eq_mul, mul_assoc]`. Both sides reduce to the same expression.

Use `_ = 0 := by`. Rewrite using `[hq, map_zero]`. Simplify using the standard rewrite rules.
-/
theorem B_rel' (hT : TAll) (hU : TUnit) {ν : Measure (Mx F E d.m d.n)} (hν : ν.IsAddHaarMeasure) {k : d.G} {χ : ℂ}
    (hχ : χ ≠ 0) {Ω : d.Fn} (hΩ : Ω ∈ d.sch) (hk : d.om k Ω = χ • Ω) {Φ : d.Fn} (hΦ : Φ ∈ d.sch) (q : Polynomial ℂ)
    (hq : ∑ i ∈ Finset.range (q.natDegree + 1), q.coeff i • d.om (k ^ i) Φ = 0)
    (v : Matrix (Fin d.m) (Fin d.n ⊕ Fin d.n) (AE F E)) :
    ∑ i ∈ Finset.range (q.natDegree + 1),
      q.coeff i * (star χ)⁻¹ ^ i * B ν Φ (d.dd.rho d.B.ψ (actB (cA σ) (k⁻¹ ^ i) v) Ω) = 0 := by
  have hψ : IsStd d.B.ψ := d.ok.good.std
  have hS := d.ok.dbl.weil.2.1.toIsSplitting
  have hrho : ∀ w, ∀ φ ∈ d.sch, d.dd.rho d.B.ψ w φ ∈ d.sch := fun w φ hφ =>
    GlobalTheory.SchrKeepsSchA.schr_mem_schA F d.B.ψ hψ d.κ _ φ hφ
  have hpow : ∀ i : ℕ, d.om (k ^ i) Ω = χ ^ i • Ω := by
    intro i
    induction i with
    | zero => simp
    | succ i ih =>
      rw [pow_succ, map_mul, Module.End.mul_apply, hk, map_smul, ih, smul_smul, pow_succ, mul_comm]
  have hact : ∀ i : ℕ, actB (cA σ) (k ^ i) (actB (cA σ) (k⁻¹ ^ i) v) = v := by
    intro i
    have e1 : k ^ i * k⁻¹ ^ i = 1 := by rw [inv_pow, mul_inv_cancel]
    simp only [actB]
    rw [Matrix.mul_assoc, ← Matrix.transpose_mul, ← Units.val_mul, ← Subgroup.coe_mul, e1]
    simp
  set Ψ := d.dd.rho d.B.ψ v Ω with hΨdef
  have hΨ : Ψ ∈ d.sch := hrho v Ω hΩ
  have hterm : ∀ i : ℕ, (star χ)⁻¹ ^ i * B ν Φ (d.dd.rho d.B.ψ (actB (cA σ) (k⁻¹ ^ i) v) Ω) =
      B ν (d.om (k ^ i) Φ) Ψ := by
    intro i
    have h1 := hU F E σ d ν hν (k ^ i) Φ hΦ (d.dd.rho d.B.ψ (actB (cA σ) (k⁻¹ ^ i) v) Ω)
      (hrho (actB (cA σ) (k⁻¹ ^ i) v) Ω hΩ)
    have h2 : d.om (k ^ i) (d.dd.rho d.B.ψ (actB (cA σ) (k⁻¹ ^ i) v) Ω) = χ ^ i • Ψ := by
      rw [hS.impl _ _ Ω hΩ, hact, hpow, rho_smul]
    rw [h2, KFock.T_smul] at h1
    unfold B
    rw [← h1]
    have e3 : ∀ X, d.T (d.om (k ^ i) Φ) X * star ((χ ^ i • d.T Ψ) X) =
        star χ ^ i * (d.T (d.om (k ^ i) Φ) X * star (d.T Ψ X)) := by
      intro X
      rw [Pi.smul_apply, smul_eq_mul, star_mul', star_pow]
      ring
    simp_rw [e3]
    rw [integral_const_mul, ← mul_assoc, ← mul_pow, inv_mul_cancel₀ (star_ne_zero.2 hχ), one_pow, one_mul]
  have hint : ∀ i : ℕ, Integrable (fun X => d.T (d.om (k ^ i) Φ) X * star (d.T Ψ X)) ν := by
    intro i
    have hA := memLp_schM d ν hν ((hT.1 F E σ d).1 (d.om (k ^ i) Φ) (hS.pres (k ^ i) Φ hΦ))
    have hB := (memLp_schM d ν hν ((hT.1 F E σ d).1 Ψ hΨ)).star
    exact hA.integrable_mul hB
  calc ∑ i ∈ Finset.range (q.natDegree + 1),
        q.coeff i * (star χ)⁻¹ ^ i * B ν Φ (d.dd.rho d.B.ψ (actB (cA σ) (k⁻¹ ^ i) v) Ω)
      = ∑ i ∈ Finset.range (q.natDegree + 1), q.coeff i * B ν (d.om (k ^ i) Φ) Ψ := by
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [mul_assoc, hterm]
    _ = ∫ X, ∑ i ∈ Finset.range (q.natDegree + 1), q.coeff i * (d.T (d.om (k ^ i) Φ) X * star (d.T Ψ X)) ∂ν := by
        unfold B
        rw [integral_finsetSum _ fun i _ => (hint i).const_mul _]
        simp_rw [integral_const_mul]
    _ = ∫ X, TL d (∑ i ∈ Finset.range (q.natDegree + 1), q.coeff i • d.om (k ^ i) Φ) X * star (d.T Ψ X) ∂ν := by
        congr 1
        funext X
        rw [map_sum, Finset.sum_apply, Finset.sum_mul]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [map_smul, Pi.smul_apply, smul_eq_mul, mul_assoc]
        rfl
    _ = 0 := by
        rw [hq, map_zero]
        simp

end PositivityTheory.SiegelWeilFormula.KFP

end

import Mathlib
import Development.WeilBound.CoreStatements.AutomorphicKernels.UnitarySchrodingerModel.DictKAOfParts
import Development.WeilBound.CoreStatements.AutomorphicKernels.UnitarySchrodingerModel.CoefDataExists
import Development.WeilBound.CoreStatements.PublishedTheorems.SiegelWeilSchrodinger.SiegelWeilUnitarySchrodingerLit
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IwasawaDecompositionUnitary
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SiegelParabolicUnnMatrixBlockUpperTriangular
import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.EisensteinMaximalParabolic
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LeftInvSubtypeSum
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SummableOfTsumEnormLtTop
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TemperateMultiplierPreservesSchwartz
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SchwartzFunctionSchwartzBruhat
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.GaussianIsSchwartzFunction
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsRealParOfIsCharAF
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ArchimedeanParametersAddCharUnique
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.PureFiniteAdelicTestFunctionContinuousCompact
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ThetaConvergenceOfSiegelSet
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.SiegelSetUnitary
noncomputable section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)

namespace GlobalTheory.CompanionTheory.IfrAdd

open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS

variable {D : D7} {n : ℕ}

set_option synthInstance.maxHeartbeats 400000 in

/- English proof (translation)
Take `⟨ψ₀, h₀, a, ha0, ha⟩` from `GlobalTheory.ThetaAllChar.exists_std hψ`. Use `set y : D.host.E := algebraMap D.host.F D.host.E a with hy_def`. Establish `hyc : NumberField.IsCMField.complexConj D.host.E y = y` using `(NumberField.IsCMField.complexConj_eq_self_iff D.host.E y).2 a.2`. Establish `hreal : ∀ τ, (tauE D τ y).im = 0`. Introduce `τ`.

Establish `h` using `NumberField.IsCMField.complexEmbedding_complexConj D.host.E (tauE D τ) y`. Rewrite `h` using `[hyc]`. Use `congrArg Complex.im h` as an intermediate fact. Rewrite `this` using `[Complex.conj_im]`. Combine the linear equalities and inequalities to obtain the conclusion.

Establish `hl' : HasRealPar ψ θ (fun τ => -(tauE D τ y).re)`. Introduce `x`. Establish `e1 : psiInf D.host.F ψ x = psiInf D.host.F ψ₀ (algebraMap D.host.F (Ainf D.host.F) a * x)`. Simplify using `only [psiInf]`. Rewrite using `[ha]`.

Use `congr 1`. Use `show (algebraMap D.host.F (Ainf D.host.F) a * x, algebraMap D.host.F (Af D.host.F) a * 0) = _`. Rewrite using `[mul_zero]`. Both sides reduce to the same expression. Rewrite using `[e1, h₀.2.2 θ hθ]`.

Use `congr 1`. Establish `e2 : ∀ ρ, θ ρ ((algebraMap D.host.F (Ainf D.host.F) a * x) ⊗ₜ[D.host.F] (1 : D.host.E)) = θ ρ (x ⊗ₜ[D.host.F] (1 : D.host.E)) * tauE D ρ y`. Introduce `ρ`. Establish `e3 : (algebraMap D.host.F (Ainf D.host.F) a * x) ⊗ₜ[D.host.F] (1 : D.host.E) = (x ⊗ₜ[D.host.F] (1 : D.host.E)) * ((1 : Ainf D.host.F) ⊗ₜ[D.host.F] y)`. Rewrite using `[Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul, ← Algebra.smul_def, ← TensorProduct.smul_tmul', ← TensorProduct.tmul_smul, Algebra.smul_def, mul_one]`.

Rewrite using `[e3, map_mul, (hθ ρ).1]`. Simplify using `only [e2]`. Establish `e4 : ∀ ρ, (((-(tauE D ρ y).re : ℝ)) : ℂ) = -tauE D ρ y`. Introduce `ρ`. Apply the tactic sequence `apply Complex.ext <;> simp [hreal ρ]`.

Simplify using `only [e4, Finset.mul_sum]`. Use `push_cast`. Use `Finset.sum_congr rfl fun ρ _ => ?_` and prove the remaining obligations. Expand and normalize the polynomial expressions, which then agree. Establish `hy0 : y ≠ 0`.

Rewrite using `[hy_def]`. Introduce `h`. Conclude with `ha0 ((map_eq_zero_iff _ (algebraMap D.host.F D.host.E).injective).1 h)`. Establish `e` using `congrFun (GlobalTheory.StdUnn.RealPar.realPar_unique D ψ θ hθ l _ hl hl') τ`. Rewrite using `[e]`.

Introduce `h0`. Establish `h1 : (tauE D τ y).re = 0` using `by simpa using h0`. Conclude with `(map_ne_zero (tauE D τ)).2 hy0 (Complex.ext h1 (hreal τ))`.
-/
theorem realPar_ne_zero {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsCharAF D.host.F ψ) {θ : InfFam D} (hθ : IsInfFam θ)
    {l : D.what₂.Tau → ℝ} (hl : HasRealPar ψ θ l) (τ : D.what₂.Tau) : l τ ≠ 0 := by
  obtain ⟨ψ₀, h₀, a, ha0, ha⟩ := GlobalTheory.ThetaAllChar.exists_std hψ
  set y : D.host.E := algebraMap D.host.F D.host.E a with hy_def
  have hyc : NumberField.IsCMField.complexConj D.host.E y = y :=
    (NumberField.IsCMField.complexConj_eq_self_iff D.host.E y).2 a.2
  have hreal : ∀ τ, (tauE D τ y).im = 0 := by
    intro τ
    have h := NumberField.IsCMField.complexEmbedding_complexConj D.host.E (tauE D τ) y
    rw [hyc] at h
    have := congrArg Complex.im h
    rw [Complex.conj_im] at this
    linarith
  have hl' : HasRealPar ψ θ (fun τ => -(tauE D τ y).re) := by
    intro x
    have e1 : psiInf D.host.F ψ x = psiInf D.host.F ψ₀ (algebraMap D.host.F (Ainf D.host.F) a * x) := by
      simp only [psiInf]
      rw [ha]
      congr 1
      show (algebraMap D.host.F (Ainf D.host.F) a * x, algebraMap D.host.F (Af D.host.F) a * 0) = _
      rw [mul_zero]; rfl
    rw [e1, h₀.2.2 θ hθ]
    congr 1
    have e2 : ∀ ρ, θ ρ ((algebraMap D.host.F (Ainf D.host.F) a * x) ⊗ₜ[D.host.F] (1 : D.host.E)) =
        θ ρ (x ⊗ₜ[D.host.F] (1 : D.host.E)) * tauE D ρ y := by
      intro ρ
      have e3 : (algebraMap D.host.F (Ainf D.host.F) a * x) ⊗ₜ[D.host.F] (1 : D.host.E) =
          (x ⊗ₜ[D.host.F] (1 : D.host.E)) * ((1 : Ainf D.host.F) ⊗ₜ[D.host.F] y) := by
        rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul, ← Algebra.smul_def, ← TensorProduct.smul_tmul',
          ← TensorProduct.tmul_smul, Algebra.smul_def, mul_one]
      rw [e3, map_mul, (hθ ρ).1]
    simp only [e2]
    have e4 : ∀ ρ, (((-(tauE D ρ y).re : ℝ)) : ℂ) = -tauE D ρ y := by
      intro ρ
      apply Complex.ext <;> simp [hreal ρ]
    simp only [e4, Finset.mul_sum]
    push_cast
    refine Finset.sum_congr rfl fun ρ _ => ?_
    ring
  have hy0 : y ≠ 0 := by
    rw [hy_def]
    intro h
    exact ha0 ((map_eq_zero_iff _ (algebraMap D.host.F D.host.E).injective).1 h)
  have e := congrFun (GlobalTheory.StdUnn.RealPar.realPar_unique D ψ θ hθ l _ hl hl') τ
  rw [e]
  intro h0
  have h1 : (tauE D τ y).re = 0 := by simpa using h0
  exact (map_ne_zero (tauE D τ)).2 hy0 (Complex.ext h1 (hreal τ))

/- English proof (translation)
Proceed by induction on `p using MvPolynomial.induction_on with`. Consider the case `C a`. Simplify `Function.HasTemperateGrowth.const a` using `[evalPoly]`. Consider the case `add p q hp hq`. Establish `e : (fun z : D.what₂.Tau → Fin m → Fin n → ℂ => evalPoly (p + q) (fun τ => Matrix.of (z τ))) = (fun z => evalPoly p (fun τ => Matrix.of (z τ))) + (fun z => evalPoly q (fun τ => Matrix.of (z τ)))`.

Use function extensionality and compare the values at `z`. Simplify using `[evalPoly]`. Rewrite using `[e]`. Conclude with `hp.add hq`. Consider the case `mul_X p k hp`.

Establish `hk : Function.HasTemperateGrowth (fun z : D.what₂.Tau → Fin m → Fin n → ℂ => if k.2.2.2 then conj (z k.1 k.2.1 k.2.2.1) else z k.1 k.2.1 k.2.2.1)`. Set `L : (D.what₂.Tau → Fin m → Fin n → ℂ) →L[ℝ] ℂ` to `(ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin n => ℂ) k.2.2.1).comp ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin m => Fin n → ℂ) k.2.1).comp (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : D.what₂.Tau => Fin m → Fin n → ℂ) k.1))`. Distinguish the cases in `h : k.2.2.2 = true`. Simplify using `only [h, if_true]`. Conclude with `(Complex.conjCLE.toContinuousLinearMap.comp L).hasTemperateGrowth`.

Simplify using `only [h]`. Conclude with `L.hasTemperateGrowth`. Establish `e : (fun z : D.what₂.Tau → Fin m → Fin n → ℂ => evalPoly (p * MvPolynomial.X k) (fun τ => Matrix.of (z τ))) = (fun z => evalPoly p (fun τ => Matrix.of (z τ))) * (fun z => if k.2.2.2 then conj (z k.1 k.2.1 k.2.2.1) else z k.1 k.2.1 k.2.2.1)`. Use function extensionality and compare the values at `z`. Simplify using `[evalPoly]`.

Rewrite using `[e]`. Conclude with `hp.mul hk`.
-/
theorem hasTemperateGrowth_evalPoly {m : ℕ} (p : MvPolynomial (D.what₂.Tau × Fin m × Fin n × Bool) ℂ) :
    Function.HasTemperateGrowth (fun z : D.what₂.Tau → Fin m → Fin n → ℂ => evalPoly p (fun τ => Matrix.of (z τ))) := by
  induction p using MvPolynomial.induction_on with
  | C a =>
    simpa [evalPoly] using Function.HasTemperateGrowth.const a
  | add p q hp hq =>
    have e : (fun z : D.what₂.Tau → Fin m → Fin n → ℂ => evalPoly (p + q) (fun τ => Matrix.of (z τ))) =
        (fun z => evalPoly p (fun τ => Matrix.of (z τ))) + (fun z => evalPoly q (fun τ => Matrix.of (z τ))) := by
      funext z
      simp [evalPoly]
    rw [e]
    exact hp.add hq
  | mul_X p k hp =>
    have hk : Function.HasTemperateGrowth (fun z : D.what₂.Tau → Fin m → Fin n → ℂ =>
        if k.2.2.2 then conj (z k.1 k.2.1 k.2.2.1) else z k.1 k.2.1 k.2.2.1) := by
      let L : (D.what₂.Tau → Fin m → Fin n → ℂ) →L[ℝ] ℂ :=
        (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin n => ℂ) k.2.2.1).comp
          ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin m => Fin n → ℂ) k.2.1).comp
            (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : D.what₂.Tau => Fin m → Fin n → ℂ) k.1))
      by_cases h : k.2.2.2 = true
      · simp only [h, if_true]
        exact (Complex.conjCLE.toContinuousLinearMap.comp L).hasTemperateGrowth
      · simp only [h]
        exact L.hasTemperateGrowth
    have e : (fun z : D.what₂.Tau → Fin m → Fin n → ℂ => evalPoly (p * MvPolynomial.X k) (fun τ => Matrix.of (z τ))) =
        (fun z => evalPoly p (fun τ => Matrix.of (z τ))) * (fun z =>
          if k.2.2.2 then conj (z k.1 k.2.1 k.2.2.1) else z k.1 k.2.1 k.2.2.1) := by
      funext z
      simp [evalPoly]
    rw [e]
    exact hp.mul hk

section Pure

open NumberField IsDedekindDomain PI.VolStabS.PositiveNearLattice PI.VolStabS.AdmissibleCompactSupport GlobalTheory.GaugeEx Set GlobalTheory.PureFinite

variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] [FiniteDimensional F E]
  {d : ℕ} (b : Module.Basis (Fin d) F E) {n M : ℕ}

/- English proof (translation)
Rewrite using `[IsLocallyConstant.iff_eventually_eq]`. Introduce `X`. Establish `hS` using `Filter.eventually_cofinite.1 (hae.and (eventually_mem_latV b X))`. Set `O : Set (Af F)` to `{x | ∀ v, x v ∈ v.adicCompletionIntegers F}`. Establish `hOo : IsOpen O` using `RestrictedProduct.isOpen_forall_mem (R := fun v : HeightOneSpectrum (𝓞 F) => v.adicCompletion F) (A := fun v => (v.adicCompletionIntegers F : Set (v.adicCompletion F))) (fun v => Valued.isOpen_valuationSubring _)`.

Set `U : Set (Fin n → Fin M → Af F ⊗[F] E)` to `{Y | ∀ a i k, crd b (Af F) ((Y - X) a i) k ∈ O}`. Establish `hUo : IsOpen U`. Establish `e : U = ⋂ a, ⋂ i, ⋂ k, (fun Y : Fin n → Fin M → Af F ⊗[F] E => crd b (Af F) ((Y - X) a i) k) ⁻¹' O`. Use extensionality with `Y`. Simplify using `[U]`.

Rewrite using `[e]`. Conclude with `isOpen_iInter_of_finite fun a => isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun k => hOo.preimage ((continuous_crd b (Af F) k).comp ((continuous_apply i).comp ((continuous_apply a).comp (continuous_id.sub continuous_const))))`. Establish `hXU : X ∈ U`. Introduce `a i k v`. Simplify using `only [sub_self, crd, Pi.zero_apply, map_zero, Finsupp.zero_apply]`.

Conclude with `zero_mem (v.adicCompletionIntegers F)`. Establish `hev : (fun Y : Fin n → Fin M → Af F ⊗[F] E => ∏ᶠ v, Φv v (projV v Y)) =ᶠ[nhds X] fun Y => ∏ v ∈ hS.toFinset, Φv v (projV v Y)` using `by filter_upwards [hUo.mem_nhds hXU] with Y hY`. Apply `finprod_eq_prod_of_mulSupport_subset` to reduce the goal to its premises. Introduce `v hv`. Rewrite using `[Set.Finite.coe_toFinset]`.

Introduce `h`. Apply `hv` to reduce the goal to its premises. Establish `hYX : projV v (Y - X) ∈ latV b v`. Introduce `a i k`. Use `crd_projV b (Y - X) v a i k` as an intermediate fact.

Simplify using `only [crd] at this`. Rewrite using `[this]`. Conclude with `hY a i k v`. Establish `hmem : projV v Y ∈ latV b v`. Establish `e : projV v Y = projV v (Y - X) + projV v X`.

Rewrite using `[← projV_add]`. Simplify using the standard rewrite rules. Rewrite using `[e]`. Conclude with `latV_add b v hYX h.2`. Use `show Φv v (projV v Y) = 1`.

Rewrite using `[h.1, Set.indicator_of_mem hmem]`. Both sides reduce to the same expression. Establish `hlc : ∀ s : Finset (HeightOneSpectrum (𝓞 F)), IsLocallyConstant (fun Y : Fin n → Fin M → Af F ⊗[F] E => ∏ v ∈ s, Φv v (projV v Y))`. Introduce `s`. Proceed by induction on `s using Finset.induction_on with`.

Consider the case `empty`. Simplify using `only [Finset.prod_empty]`. Conclude with `IsLocallyConstant.const 1`. Consider the case `insert v s hv ih`. Simplify using `only [Finset.prod_insert hv]`.

Conclude with `((hSB v).1.comp_continuous (continuous_projV_fin b v)).mul ih`. Establish `h2` using `(IsLocallyConstant.iff_eventually_eq _).1 (hlc hS.toFinset) X`. Use `filter_upwards [hev, h2] with Y h3 h4`. Rewrite using `[h3, h4]`. Conclude with `hev.self_of_nhds.symm`.
-/
theorem isLocallyConstant_finprod (Φv : ∀ v : HeightOneSpectrum (𝓞 F), (Fin n → Fin M → Fv F v ⊗[F] E) → ℂ)
    (hSB : ∀ v, IsSB (Φv v)) (hae : ∀ᶠ v in Filter.cofinite, Φv v = (latV b v).indicator 1) :
    IsLocallyConstant (fun X : Fin n → Fin M → Af F ⊗[F] E => ∏ᶠ v, Φv v (projV v X)) := by
  classical
  rw [IsLocallyConstant.iff_eventually_eq]
  intro X
  have hS := Filter.eventually_cofinite.1 (hae.and (eventually_mem_latV b X))
  let O : Set (Af F) := {x | ∀ v, x v ∈ v.adicCompletionIntegers F}
  have hOo : IsOpen O :=
    RestrictedProduct.isOpen_forall_mem (R := fun v : HeightOneSpectrum (𝓞 F) => v.adicCompletion F)
      (A := fun v => (v.adicCompletionIntegers F : Set (v.adicCompletion F)))
      (fun v => Valued.isOpen_valuationSubring _)
  let U : Set (Fin n → Fin M → Af F ⊗[F] E) := {Y | ∀ a i k, crd b (Af F) ((Y - X) a i) k ∈ O}
  have hUo : IsOpen U := by
    have e : U = ⋂ a, ⋂ i, ⋂ k, (fun Y : Fin n → Fin M → Af F ⊗[F] E =>
        crd b (Af F) ((Y - X) a i) k) ⁻¹' O := by
      ext Y; simp [U]
    rw [e]
    exact isOpen_iInter_of_finite fun a => isOpen_iInter_of_finite fun i =>
      isOpen_iInter_of_finite fun k => hOo.preimage ((continuous_crd b (Af F) k).comp
        ((continuous_apply i).comp ((continuous_apply a).comp (continuous_id.sub continuous_const))))
  have hXU : X ∈ U := by
    intro a i k v
    simp only [sub_self, crd, Pi.zero_apply, map_zero, Finsupp.zero_apply]
    exact zero_mem (v.adicCompletionIntegers F)
  have hev : (fun Y : Fin n → Fin M → Af F ⊗[F] E => ∏ᶠ v, Φv v (projV v Y)) =ᶠ[nhds X]
      fun Y => ∏ v ∈ hS.toFinset, Φv v (projV v Y) := by
    filter_upwards [hUo.mem_nhds hXU] with Y hY
    apply finprod_eq_prod_of_mulSupport_subset
    intro v hv
    rw [Set.Finite.coe_toFinset]
    intro h
    apply hv
    have hYX : projV v (Y - X) ∈ latV b v := by
      intro a i k
      have := crd_projV b (Y - X) v a i k
      simp only [crd] at this
      rw [this]
      exact hY a i k v
    have hmem : projV v Y ∈ latV b v := by
      have e : projV v Y = projV v (Y - X) + projV v X := by
        rw [← projV_add]; simp
      rw [e]
      exact latV_add b v hYX h.2
    show Φv v (projV v Y) = 1
    rw [h.1, Set.indicator_of_mem hmem]
    rfl
  have hlc : ∀ s : Finset (HeightOneSpectrum (𝓞 F)),
      IsLocallyConstant (fun Y : Fin n → Fin M → Af F ⊗[F] E => ∏ v ∈ s, Φv v (projV v Y)) := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
      simp only [Finset.prod_empty]
      exact IsLocallyConstant.const 1
    | insert v s hv ih =>
      simp only [Finset.prod_insert hv]
      exact ((hSB v).1.comp_continuous (continuous_projV_fin b v)).mul ih
  have h2 := (IsLocallyConstant.iff_eventually_eq _).1 (hlc hS.toFinset) X
  filter_upwards [hev, h2] with Y h3 h4
  rw [h3, h4]
  exact hev.self_of_nhds.symm

end Pure

/- English proof (translation)
Use `haveI : FiniteDimensional F E := Module.Finite.of_basis b`. Establish `hc` using `(GlobalTheory.isPureFin_continuous_hasCompactSupport F E d M n b Φf Φv h).2`. Take `⟨hSB, hae, hprod⟩` from `h`. Establish `e : Φf = fun X => ∏ᶠ v, Φv v (projV v X)` using `funext hprod`. Use `⟨?_, hc⟩` and prove the remaining obligations.

Rewrite using `[e]`. Conclude with `isLocallyConstant_finprod b Φv hSB hae`.
-/
theorem mem_SB_of_isPureFin {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {d M n : ℕ}
    (b : Module.Basis (Fin d) F E) {Φf : (Fin n → Fin M → Af F ⊗[F] E) → ℂ}
    {Φv : ∀ v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F), (Fin n → Fin M → Fv F v ⊗[F] E) → ℂ}
    (h : IsPureFin b Φf Φv) : Φf ∈ GlobalTheory.WeilM.SB (Fin n → Fin M → Af F ⊗[F] E) := by
  haveI : FiniteDimensional F E := Module.Finite.of_basis b
  have hc := (GlobalTheory.isPureFin_continuous_hasCompactSupport F E d M n b Φf Φv h).2
  obtain ⟨hSB, hae, hprod⟩ := h
  have e : Φf = fun X => ∏ᶠ v, Φv v (projV v X) := funext hprod
  refine ⟨?_, hc⟩
  rw [e]
  exact isLocallyConstant_finprod b Φv hSB hae

/- English proof (translation)
Take `⟨e, c, g, d, bs, gv, hp, rfl⟩` from `hφ`. Establish `hg : g ∈ GlobalTheory.WeilM.SB (Fin V.rank → Fin n → Af D.host.F ⊗[D.host.F] D.host.E)`. Establish `h1` using `mem_SB_of_isPureFin bs (Φf := fun X => g fun i j => X j i) (Φv := gv) hp`. Establish `h2` using `GlobalTheory.CompanionTheory.SiegelND.SchGlue.isSB_swap (D := D) h1`. Conclude with `⟨h2.1, h2.2⟩`.

Take `⟨f, hf⟩` from `GlobalTheory.GaussSchwartz.exists_schwartz_gauss D n V l hl s hs`. Establish `hmem : (fun x : Mx D V.rank n => f (fun τ i j => compAt θ τ x i j) * g (fun i j => finPart D (x i j))) ∈ schwartzA θ V.rank n` using `Submodule.subset_span ⟨f, g, hg, rfl⟩`. Establish `h3` using `GlobalTheory.CompanionTheory.WSum.mul_mem_schwartzA D θ V.rank n _ (hasTemperateGrowth_evalPoly (MvPolynomial.monomial e c)) _ hmem`. Use `h3 using 1` and compare the differences between its conclusion and the goal. Use function extensionality and compare the values at `x`.

Rewrite using `[hf, mul_assoc]`. Both sides reduce to the same expression.
-/
theorem mem_schwartzA_of_isMonoFock {θ : InfFam D} (hθ : IsInfFam θ) {V : HSp D} {l : D.what₂.Tau → ℝ} (hl : ∀ τ, l τ ≠ 0)
    {s : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ} (hs : ∀ τ, IsCartanInv (gramAt D V τ) (s τ))
    {φ : Mx D V.rank n → ℂ} (hφ : IsMonoFock θ V l s φ) : φ ∈ schwartzA θ V.rank n := by
  obtain ⟨e, c, g, d, bs, gv, hp, rfl⟩ := hφ
  have hg : g ∈ GlobalTheory.WeilM.SB (Fin V.rank → Fin n → Af D.host.F ⊗[D.host.F] D.host.E) := by
    have h1 := mem_SB_of_isPureFin bs (Φf := fun X => g fun i j => X j i) (Φv := gv) hp
    have h2 := GlobalTheory.CompanionTheory.SiegelND.SchGlue.isSB_swap (D := D) h1
    exact ⟨h2.1, h2.2⟩
  obtain ⟨f, hf⟩ := GlobalTheory.GaussSchwartz.exists_schwartz_gauss D n V l hl s hs
  have hmem : (fun x : Mx D V.rank n => f (fun τ i j => compAt θ τ x i j) * g (fun i j => finPart D (x i j))) ∈
      schwartzA θ V.rank n := Submodule.subset_span ⟨f, g, hg, rfl⟩
  have h3 := GlobalTheory.CompanionTheory.WSum.mul_mem_schwartzA D θ V.rank n _ (hasTemperateGrowth_evalPoly (MvPolynomial.monomial e c)) _ hmem
  convert h3 using 1
  funext x
  rw [hf, mul_assoc]
  rfl

section Abstract

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [SecondCountableTopology G]
  [MeasurableSpace G] [BorelSpace G] {Γ : Subgroup G} [DiscreteTopology Γ] {μ : Measure G} [μ.IsMulLeftInvariant]
  {X : Type*} [Countable X]

end Abstract

end GlobalTheory.CompanionTheory.IfrAdd

end

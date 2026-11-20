import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsSplitting
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TensorRepApply
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnramifiedValuationParitySignCharacterKernelNormStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NonemptyMeasAndReps
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsLocallyConstantTestRepresentationTensorProductStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FourBProdIteratedStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AbsKMulOfEtaleSplittingStatement

open GlobalTheory.JR Matrix MeasureTheory Filter Topology

noncomputable section

namespace GlobalTheory.JR.WeilProd

def transRep {G H X Y : Type} (ρ : G → H) (e : X ≃ Y) (W : H → (Y → ℂ) → Y → ℂ) : G → (X → ℂ) → X → ℂ :=
  fun g f x => W (ρ g) (f ∘ e.symm) (e x)

/- English proof (translation)
Assemble the required witnesses or components as `⟨hf.1.comp_continuous e.continuous, hf.2.comp_homeomorph e⟩`.
-/
theorem isTest_comp_homeomorph {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y] (e : X ≃ₜ Y) {f : Y → ℂ}
    (hf : IsTest f) : IsTest (f ∘ e) :=
  ⟨hf.1.comp_continuous e.continuous, hf.2.comp_homeomorph e⟩

/- English proof (translation)
Take `⟨h1, h2, h3, h4⟩` from `hW`. Establish `ht : ∀ f, IsTest f → IsTest (f ∘ e.symm)` using `fun f hf => isTest_comp_homeomorph e.symm hf`. Use `⟨fun g f hf => isTest_comp_homeomorph e (h1 _ _ (ht f hf)), fun f hf => ?_, fun g h f hf => ?_, fun g c f f' hf hf' => ?_⟩` and prove the remaining obligations. Use function extensionality and compare the values at `x`. Simplify using `[transRep, map_one, h2 _ (ht f hf)]`.

Use function extensionality and compare the values at `x show W (ρ (g * h)) (f ∘ e.symm) (e x) = W (ρ g) ((fun x => W (ρ h) (f ∘ e.symm) (e x)) ∘ e.symm) (e x)`. Rewrite using `[map_mul, h3 _ _ _ (ht f hf)]`. Use `congr 1`. Use function extensionality and compare the values at `y`. Simplify using the standard rewrite rules.

Use function extensionality and compare the values at `x`. Establish `: (c • f + f') ∘ e.toEquiv.symm = c • (f ∘ e.symm) + f' ∘ e.symm` using `rfl`. Simplify using `only [transRep, this, h4 _ c _ _ (ht f hf) (ht f' hf')]`. Both sides reduce to the same expression.
-/
theorem isTestRep_transRep {G H X Y : Type} [Group G] [Group H] [TopologicalSpace X] [TopologicalSpace Y]
    (ρ : G →* H) (e : X ≃ₜ Y) (W : H → (Y → ℂ) → Y → ℂ) (hW : IsTestRep W) :
    IsTestRep (transRep ρ e.toEquiv W) := by
  obtain ⟨h1, h2, h3, h4⟩ := hW
  have ht : ∀ f, IsTest f → IsTest (f ∘ e.symm) := fun f hf => isTest_comp_homeomorph e.symm hf
  refine ⟨fun g f hf => isTest_comp_homeomorph e (h1 _ _ (ht f hf)), fun f hf => ?_, fun g h f hf => ?_,
    fun g c f f' hf hf' => ?_⟩
  · funext x
    simp [transRep, map_one, h2 _ (ht f hf)]
  · funext x
    show W (ρ (g * h)) (f ∘ e.symm) (e x) = W (ρ g) ((fun x => W (ρ h) (f ∘ e.symm) (e x)) ∘ e.symm) (e x)
    rw [map_mul, h3 _ _ _ (ht f hf)]
    congr 1
    funext y; simp
  · funext x
    have : (c • f + f') ∘ e.toEquiv.symm = c • (f ∘ e.symm) + f' ∘ e.symm := rfl
    simp only [transRep, this, h4 _ c _ _ (ht f hf) (ht f' hf')]
    rfl

/- English proof (translation)
Rewrite using `[Algebra.norm_apply, Algebra.norm_apply, Algebra.norm_apply, ← LinearMap.det_prodMap]`. Use `congr 1`.
-/
theorem norm_prod_apply {R S T : Type} [Field R] [CommRing S] [CommRing T] [Algebra R S] [Algebra R T]
    [Module.Finite R S] [Module.Finite R T] (p : S × T) :
    Algebra.norm R p = Algebra.norm R p.1 * Algebra.norm R p.2 := by
  rw [Algebra.norm_apply, Algebra.norm_apply, Algebra.norm_apply, ← LinearMap.det_prodMap]
  congr 1

variable {F E : Type} [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E]

/- English proof (translation)
Rewrite using `[← Algebra.trace_eq_of_algEquiv eK, Algebra.trace_prod_apply]`.
-/
theorem trace_split (A A₁ A₂ : Et F E) (eK : A.K ≃ₐ[F] A₁.K × A₂.K) (k : A.K) :
    Algebra.trace F A.K k = Algebra.trace F A₁.K (eK k).1 + Algebra.trace F A₂.K (eK k).2 := by
  rw [← Algebra.trace_eq_of_algEquiv eK, Algebra.trace_prod_apply]

/- English proof (translation)
Rewrite using `[← Algebra.norm_eq_of_algEquiv eK, norm_prod_apply]`.
-/
theorem norm_split (A A₁ A₂ : Et F E) (eK : A.K ≃ₐ[F] A₁.K × A₂.K) (k : A.K) :
    Algebra.norm F k = Algebra.norm F (eK k).1 * Algebra.norm F (eK k).2 := by
  rw [← Algebra.norm_eq_of_algEquiv eK, norm_prod_apply]

/- English proof (translation)
Take `⟨-, i₁, n₁, t₁, -⟩` from `Et.quadratic_structure F E A₁`. Take `⟨-, i₂, n₂, t₂, -⟩` from `Et.quadratic_structure F E A₂`. Take `⟨-, -, n, t, -⟩` from `Et.quadratic_structure F E A`. Take `⟨hK, -, hst⟩` from `hS`. Establish `e1` using `hK (A.NL y)`.

Rewrite `e1` using `[n, map_mul, hst]`. Establish `e2` using `hK (Algebra.trace A.K A.L y)`. Rewrite `e2` using `[t, map_add, hst]`. Use `⟨Prod.ext (i₁ ?_) (i₂ ?_), Prod.ext (i₁ ?_) (i₂ ?_)⟩` and prove the remaining obligations. Rewrite using `[n₁]`.

Simplify using `using (congrArg Prod.fst e1).symm`. Rewrite using `[n₂]`. Simplify using `using (congrArg Prod.snd e1).symm`. Rewrite using `[t₁]`. Simplify using `using (congrArg Prod.fst e2).symm`.

Rewrite using `[t₂]`. Simplify using `using (congrArg Prod.snd e2).symm`.
-/
theorem splitL [Unram F E] (A A₁ A₂ : Et F E) (eK : A.K ≃ₐ[F] A₁.K × A₂.K) (eL : A.L ≃ₐ[F] A₁.L × A₂.L)
    (hS : IsSplitting A A₁ A₂ eK eL) (y : A.L) :
    eK (A.NL y) = (A₁.NL (eL y).1, A₂.NL (eL y).2) ∧
      eK (Algebra.trace A.K A.L y) = (Algebra.trace A₁.K A₁.L (eL y).1, Algebra.trace A₂.K A₂.L (eL y).2) := by
  obtain ⟨-, i₁, n₁, t₁, -⟩ := Et.quadratic_structure F E A₁
  obtain ⟨-, i₂, n₂, t₂, -⟩ := Et.quadratic_structure F E A₂
  obtain ⟨-, -, n, t, -⟩ := Et.quadratic_structure F E A
  obtain ⟨hK, -, hst⟩ := hS
  have e1 := hK (A.NL y)
  rw [n, map_mul, hst] at e1
  have e2 := hK (Algebra.trace A.K A.L y)
  rw [t, map_add, hst] at e2
  refine ⟨Prod.ext (i₁ ?_) (i₂ ?_), Prod.ext (i₁ ?_) (i₂ ?_)⟩
  · rw [n₁]; simpa using (congrArg Prod.fst e1).symm
  · rw [n₂]; simpa using (congrArg Prod.snd e1).symm
  · rw [t₁]; simpa using (congrArg Prod.fst e2).symm
  · rw [t₂]; simpa using (congrArg Prod.snd e2).symm

/- English proof (translation)
Establish `h` using `(splitL A A₁ A₂ eK eL hS (star y' * y)).2`. Rewrite `h` using `[map_mul eL, hS.2.2]`. Simplify using `only [Et.kerL, Et.psiK]`. Rewrite using `[trace_split A A₁ A₂ eK, AddChar.map_add_eq_mul, map_mul, h]`. Both sides reduce to the same expression.
-/
theorem kerL_split [Unram F E] (A A₁ A₂ : Et F E) (eK : A.K ≃ₐ[F] A₁.K × A₂.K) (eL : A.L ≃ₐ[F] A₁.L × A₂.L)
    (hS : IsSplitting A A₁ A₂ eK eL) (ψ : AddChar F ℂ) (x : A.K) (y' y : A.L) :
    A.kerL ψ x y' y = A₁.kerL ψ (eK x).1 (eL y').1 (eL y).1 * A₂.kerL ψ (eK x).2 (eL y').2 (eL y).2 := by
  have h := (splitL A A₁ A₂ eK eL hS (star y' * y)).2
  rw [map_mul eL, hS.2.2] at h
  simp only [Et.kerL, Et.psiK]
  rw [trace_split A A₁ A₂ eK, AddChar.map_add_eq_mul, map_mul, h]
  rfl

/- English proof (translation)
Simplify using `only [Et.psiK]`. Rewrite using `[trace_split A A₁ A₂ eK, AddChar.map_add_eq_mul, map_mul, map_mul, (splitL A A₁ A₂ eK eL hS y).1]`. Both sides reduce to the same expression.
-/
theorem psiK_split [Unram F E] (A A₁ A₂ : Et F E) (eK : A.K ≃ₐ[F] A₁.K × A₂.K) (eL : A.L ≃ₐ[F] A₁.L × A₂.L)
    (hS : IsSplitting A A₁ A₂ eK eL) (ψ : AddChar F ℂ) (z x : A.K) (y : A.L) :
    A.psiK ψ (z * x * A.NL y) = A₁.psiK ψ ((eK z).1 * (eK x).1 * A₁.NL (eL y).1) *
      A₂.psiK ψ ((eK z).2 * (eK x).2 * A₂.NL (eL y).2) := by
  simp only [Et.psiK]
  rw [trace_split A A₁ A₂ eK, AddChar.map_add_eq_mul, map_mul, map_mul, (splitL A A₁ A₂ eK eL hS y).1]
  rfl

/- English proof (translation)
Establish `hu : IsUnit (eK (s : A.K))` using `s.isUnit.map eK`. Establish `h₁ : Algebra.norm F (eK s).1 ≠ 0` using `((Prod.isUnit_iff.1 hu).1.map (Algebra.norm F)).ne_zero`. Establish `h₂ : Algebra.norm F (eK s).2 ≠ 0` using `((Prod.isUnit_iff.1 hu).2.map (Algebra.norm F)).ne_zero`. Simplify using `only [Et.etaK]`. Rewrite using `[norm_split A A₁ A₂ eK, (GlobalTheory.T.unramifiedValuationParitySign_character_kernel_norms F E).1 _ _ h₁ h₂]`.
-/
theorem etaK_split [Unram F E] (A A₁ A₂ : Et F E) (eK : A.K ≃ₐ[F] A₁.K × A₂.K) (s : A.Kˣ) :
    A.etaK s = A₁.etaK (eK s).1 * A₂.etaK (eK s).2 := by
  have hu : IsUnit (eK (s : A.K)) := s.isUnit.map eK
  have h₁ : Algebra.norm F (eK s).1 ≠ 0 := ((Prod.isUnit_iff.1 hu).1.map (Algebra.norm F)).ne_zero
  have h₂ : Algebra.norm F (eK s).2 ≠ 0 := ((Prod.isUnit_iff.1 hu).2.map (Algebra.norm F)).ne_zero
  simp only [Et.etaK]
  rw [norm_split A A₁ A₂ eK, (GlobalTheory.T.unramifiedValuationParitySign_character_kernel_norms F E).1 _ _ h₁ h₂]

/- English proof (translation)
Rewrite using `[Algebra.smul_def, map_mul, hS.1, Algebra.smul_def, Algebra.smul_def]`. Both sides reduce to the same expression.
-/
theorem smul_split (A A₁ A₂ : Et F E) (eK : A.K ≃ₐ[F] A₁.K × A₂.K) (eL : A.L ≃ₐ[F] A₁.L × A₂.L)
    (hS : IsSplitting A A₁ A₂ eK eL) (k : A.K) (y : A.L) :
    eL (k • y) = ((eK k).1 • (eL y).1, (eK k).2 • (eL y).2) := by
  rw [Algebra.smul_def, map_mul, hS.1, Algebra.smul_def, Algebra.smul_def]
  rfl

/- English proof (translation)
Use `U.ultraF` as an intermediate fact. Use `U.lcF` as an intermediate fact. Use `EtMeas.finite_L A` as an intermediate fact. Establish `: IsTopologicalRing A.L` using `IsModuleTopology.isTopologicalRing F A.L`. Set `T : A.L →ₗ[F] F` to `(Algebra.trace F A.K).comp ((LinearMap.mul F A.K x).comp ((Algebra.trace A.K A.L).restrictScalars F))`.

Establish `hT : Continuous T` using `IsModuleTopology.continuous_of_linearMap T`. Establish `hs : Continuous (star : A.L → A.L)` using `IsModuleTopology.continuous_of_linearMap (EtMeas.starF A)`. Conclude with `(DualLattice.stdChar_continuous hψ).comp (hT.comp ((hs.comp continuous_fst).mul continuous_snd))`.
-/
theorem continuous_kerL [U : Unram F E] (A : Et F E) (ψ : AddChar F ℂ) (hψ : IsStdChar ψ) (x : A.K) :
    Continuous (fun p : A.L × A.L => A.kerL ψ x p.1 p.2) := by
  have := U.ultraF; have := U.lcF; have := EtMeas.finite_L A
  have : IsTopologicalRing A.L := IsModuleTopology.isTopologicalRing F A.L
  let T : A.L →ₗ[F] F :=
    (Algebra.trace F A.K).comp ((LinearMap.mul F A.K x).comp ((Algebra.trace A.K A.L).restrictScalars F))
  have hT : Continuous T := IsModuleTopology.continuous_of_linearMap T
  have hs : Continuous (star : A.L → A.L) := IsModuleTopology.continuous_of_linearMap (EtMeas.starF A)
  exact (DualLattice.stdChar_continuous hψ).comp (hT.comp ((hs.comp continuous_fst).mul continuous_snd))

/- English proof (translation)
The claim follows from `GlobalTheory.T.isLocallyConstantTestRepresentation_tensorProduct`.
-/
theorem tensor_isTestRep : ∀ {G H X Y : Type} [Group G] [Group H] [TopologicalSpace X] [TopologicalSpace Y]
    (W₁ : G → (X → ℂ) → X → ℂ) (W₂ : H → (Y → ℂ) → Y → ℂ), IsTestRep W₁ → IsTestRep W₂ →
    IsTestRep (tensorRep W₁ W₂) ∧ ∀ f : X × Y → ℂ, IsTest f →
      (∀ u, IsTest (fun v => f (u, v))) ∧ ∀ h y, IsTest (fun u => W₂ h (fun v => f (u, v)) y) := GlobalTheory.T.isLocallyConstantTestRepresentation_tensorProduct

/- English proof (translation)
The claim follows from `GlobalTheory.T.fourB_prod_iterated_alt`.
-/
theorem fourB_split : ∀ {V V₁ V₂ : Type} [AddCommGroup V] [TopologicalSpace V] [IsTopologicalAddGroup V] [T2Space V]
    [LocallyCompactSpace V] [SecondCountableTopology V] [MeasurableSpace V] [BorelSpace V]
    [AddCommGroup V₁] [TopologicalSpace V₁] [IsTopologicalAddGroup V₁] [T2Space V₁]
    [LocallyCompactSpace V₁] [SecondCountableTopology V₁] [MeasurableSpace V₁] [BorelSpace V₁]
    [AddCommGroup V₂] [TopologicalSpace V₂] [IsTopologicalAddGroup V₂] [T2Space V₂]
    [LocallyCompactSpace V₂] [SecondCountableTopology V₂] [MeasurableSpace V₂] [BorelSpace V₂]
    (e : V ≃+ V₁ × V₂), Continuous e → Continuous e.symm →
    ∀ (B : V → V → ℂ) (B₁ : V₁ → V₁ → ℂ) (B₂ : V₂ → V₂ → ℂ),
    Continuous (fun p : V₁ × V₁ => B₁ p.1 p.2) → Continuous (fun p : V₂ × V₂ => B₂ p.1 p.2) →
    (∀ y' y, B y' y = B₁ (e y').1 (e y).1 * B₂ (e y').2 (e y).2) →
    ∀ (μ : Measure V) (μ₁ : Measure V₁) (μ₂ : Measure V₂), μ.IsAddHaarMeasure → μ₁.IsAddHaarMeasure →
    μ₂.IsAddHaarMeasure → ∃ c : ℂ, c ≠ 0 ∧ ∀ φ : V → ℂ, IsTest φ → ∀ y,
      fourB μ B φ y = c * ∫ u, (∫ v, φ (e.symm (u, v)) * B₂ v (e y).2 ∂μ₂) * B₁ u (e y).1 ∂μ₁ := GlobalTheory.T.fourB_prod_iterated_alt

/- English proof (translation)
The claim follows from `GlobalTheory.T.absK_mul_of_etale_splitting`.
-/
theorem absK_split : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E]
    [StarRing E] [Unram F E] (A A₁ A₂ : Et F E) (eK : A.K ≃ₐ[F] A₁.K × A₂.K) (t : A.K),
    A.absK t = A₁.absK (eK t).1 * A₂.absK (eK t).2 := GlobalTheory.T.absK_mul_of_etale_splitting

/- English proof (translation)
Use extensionality with `i j`. Rewrite using `[SpecialLinearGroup.map_apply_coe]`. Apply the tactic sequence `fin_cases i <;> fin_cases j <;> simp [nS]`.
-/
theorem map_nS {R S : Type} [CommRing R] [CommRing S] (f : R →+* S) (z : R) :
    SpecialLinearGroup.map f (nS z) = nS (f z) := by
  ext i j
  rw [SpecialLinearGroup.map_apply_coe]
  fin_cases i <;> fin_cases j <;> simp [nS]

/- English proof (translation)
Use extensionality with `i j`. Rewrite using `[SpecialLinearGroup.map_apply_coe]`. Apply the tactic sequence `fin_cases i <;> fin_cases j <;> simp [mS]`.
-/
theorem map_mS {R S : Type} [CommRing R] [CommRing S] (f : R →+* S) (s : Rˣ) :
    SpecialLinearGroup.map f (mS s) = mS (Units.map (f : R →* S) s) := by
  ext i j
  rw [SpecialLinearGroup.map_apply_coe]
  fin_cases i <;> fin_cases j <;> simp [mS]

/- English proof (translation)
Use extensionality with `i j`. Rewrite using `[SpecialLinearGroup.map_apply_coe]`. Apply the tactic sequence `fin_cases i <;> fin_cases j <;> simp [wS]`.
-/
theorem map_wS {R S : Type} [CommRing R] [CommRing S] (f : R →+* S) :
    SpecialLinearGroup.map f (wS R) = wS S := by
  ext i j
  rw [SpecialLinearGroup.map_apply_coe]
  fin_cases i <;> fin_cases j <;> simp [wS]

section rel
variable [Unram F E] (A A₁ A₂ : Et F E) (eK : A.K ≃ₐ[F] A₁.K × A₂.K) (eL : A.L ≃ₐ[F] A₁.L × A₂.L)
  (hS : IsSplitting A A₁ A₂ eK eL) (ψ : AddChar F ℂ) (x : A.K)
  (W₁ : SpecialLinearGroup (Fin 2) A₁.K → (A₁.L → ℂ) → A₁.L → ℂ)
  (W₂ : SpecialLinearGroup (Fin 2) A₂.K → (A₂.L → ℂ) → A₂.L → ℂ) (γ₁ γ₂ : ℂ) (μ₁ : Measure A₁.L) (μ₂ : Measure A₂.L)
  (hW₁ : A₁.IsWeil ψ (eK x).1 A₁.etaK μ₁ γ₁ W₁) (hW₂ : A₂.IsWeil ψ (eK x).2 A₂.etaK μ₂ γ₂ W₂)
  (f : A₁.L × A₂.L → ℂ) (hf1 : ∀ u, IsTest (fun v => f (u, v)))
  (hf2 : ∀ h y, IsTest (fun u => W₂ h (fun v => f (u, v)) y))
include hS hW₁ hW₂ hf1 hf2

/- English proof (translation)
Simplify using `only [tensorRep]`. Establish `e2 : (fun u => W₂ (nS (eK z).2) (fun v => f (u, v)) (eL y).2) = fun u => A₂.psiK ψ ((eK z).2 * (eK x).2 * A₂.NL (eL y).2) * f (u, (eL y).2)`. Use function extensionality and compare the values at `fun u => (hW₂.2 _ (hf1 u)).1 _ _`. Establish `t` using `hf2 (nS (eK z).2) (eL y).2`. Rewrite `t`, the goal using `[e2]`.

Rewrite using `[(hW₁.2 _ t).1, psiK_split A A₁ A₂ eK eL hS ψ z x y]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem rel_n (z : A.K) (y : A.L) :
    tensorRep W₁ W₂ (nS (eK z).1, nS (eK z).2) f (eL y) = A.psiK ψ (z * x * A.NL y) * f (eL y) := by
  simp only [tensorRep]
  have e2 : (fun u => W₂ (nS (eK z).2) (fun v => f (u, v)) (eL y).2) =
      fun u => A₂.psiK ψ ((eK z).2 * (eK x).2 * A₂.NL (eL y).2) * f (u, (eL y).2) :=
    funext fun u => (hW₂.2 _ (hf1 u)).1 _ _
  have t := hf2 (nS (eK z).2) (eL y).2
  rw [e2] at t ⊢
  rw [(hW₁.2 _ t).1, psiK_split A A₁ A₂ eK eL hS ψ z x y]
  ring

/- English proof (translation)
Simplify using `only [tensorRep]`. Establish `e2 : (fun u => W₂ (mS s₂) (fun v => f (u, v)) (eL y).2) = fun u => A₂.etaK s₂ * (A₂.absK s₂ : ℂ) * f (u, (s₂ : A₂.K) • (eL y).2)`. Use function extensionality and compare the values at `fun u => (hW₂.2 _ (hf1 u)).2.1 _ _`. Establish `t` using `hf2 (mS s₂) (eL y).2`. Rewrite `t`, the goal using `[e2]`.

Rewrite using `[(hW₁.2 _ t).2.1, smul_split A A₁ A₂ eK eL hS, etaK_split A A₁ A₂ eK s, absK_split F E A A₁ A₂ eK s, hs₁, hs₂]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem rel_m (s : A.Kˣ) (s₁ : A₁.Kˣ) (s₂ : A₂.Kˣ) (hs₁ : (s₁ : A₁.K) = (eK s).1) (hs₂ : (s₂ : A₂.K) = (eK s).2)
    (y : A.L) :
    tensorRep W₁ W₂ (mS s₁, mS s₂) f (eL y) = A.etaK s * (A.absK s : ℂ) * f (eL ((s : A.K) • y)) := by
  simp only [tensorRep]
  have e2 : (fun u => W₂ (mS s₂) (fun v => f (u, v)) (eL y).2) =
      fun u => A₂.etaK s₂ * (A₂.absK s₂ : ℂ) * f (u, (s₂ : A₂.K) • (eL y).2) :=
    funext fun u => (hW₂.2 _ (hf1 u)).2.1 _ _
  have t := hf2 (mS s₂) (eL y).2
  rw [e2] at t ⊢
  rw [(hW₁.2 _ t).2.1, smul_split A A₁ A₂ eK eL hS, etaK_split A A₁ A₂ eK s,
    absK_split F E A A₁ A₂ eK s, hs₁, hs₂]
  push_cast
  ring

/- English proof (translation)
Simplify using `only [tensorRep]`. Establish `e2 : (fun u => W₂ (wS A₂.K) (fun v => f (u, v)) (eL y).2) = fun u => γ₂ * fourB μ₂ (A₂.kerL ψ (eK x).2) (fun v => f (u, v)) (eL y).2`. Use function extensionality and compare the values at `fun u => (hW₂.2 _ (hf1 u)).2.2 _`. Establish `t` using `hf2 (wS A₂.K) (eL y).2`. Rewrite `t`, the goal using `[e2]`.

Rewrite using `[(hW₁.2 _ t).2.2]`. Simplify using `only [fourB, mul_assoc, integral_const_mul]`.
-/
theorem rel_w (y : A.L) :
    tensorRep W₁ W₂ (wS A₁.K, wS A₂.K) f (eL y) = γ₁ * γ₂ *
      ∫ u, (∫ v, f (u, v) * A₂.kerL ψ (eK x).2 v (eL y).2 ∂μ₂) * A₁.kerL ψ (eK x).1 u (eL y).1 ∂μ₁ := by
  simp only [tensorRep]
  have e2 : (fun u => W₂ (wS A₂.K) (fun v => f (u, v)) (eL y).2) =
      fun u => γ₂ * fourB μ₂ (A₂.kerL ψ (eK x).2) (fun v => f (u, v)) (eL y).2 :=
    funext fun u => (hW₂.2 _ (hf1 u)).2.2 _
  have t := hf2 (wS A₂.K) (eL y).2
  rw [e2] at t ⊢
  rw [(hW₁.2 _ t).2.2]
  simp only [fourB, mul_assoc, integral_const_mul]

end rel

/- English proof (translation)
Introduce `F E _ _ _ _ U A A₁ A₂ eK eL hS h₁ h₂ ψ hψ x μ hμ`. Use `U.ultraF` as an intermediate fact. Use `U.lcF` as an intermediate fact. Use `EtMeas.finite_L A` as an intermediate fact. Use `EtMeas.finite_L A₁` as an intermediate fact.

Use `EtMeas.finite_L A₂` as an intermediate fact. Take `⟨_, _, _, _, -⟩` from `EtMeas.top_facts F A.L`. Take `⟨_, _, _, _, -⟩` from `EtMeas.top_facts F A₁.L`. Take `⟨_, _, _, _, -⟩` from `EtMeas.top_facts F A₂.L`. Set `f₁ : A.K →+* A₁.K` to `(RingHom.fst A₁.K A₂.K).comp (eK : A.K →+* A₁.K × A₂.K)`.

Set `f₂ : A.K →+* A₂.K` to `(RingHom.snd A₁.K A₂.K).comp (eK : A.K →+* A₁.K × A₂.K)`. Set `x₁ : A₁.Kˣ` to `Units.map (f₁ : A.K →* A₁.K) x`. Set `x₂ : A₂.Kˣ` to `Units.map (f₂ : A.K →* A₂.K) x`. Take `⟨μ₁, hμ₁⟩` from `EtMeas.exists_selfDual_L A₁ ψ hψ x₁`. Take `⟨μ₂, hμ₂⟩` from `EtMeas.exists_selfDual_L A₂ ψ hψ x₂`.

Take `⟨γ₁, W₁, hW₁⟩` from `h₁ ψ hψ x₁ μ₁ hμ₁`. Take `⟨γ₂, W₂, hW₂⟩` from `h₂ ψ hψ x₂ μ₂ hμ₂`. Establish `hc₁ : Continuous eL` using `IsModuleTopology.continuous_of_linearMap eL.toLinearMap`. Establish `hc₂ : Continuous eL.symm` using `IsModuleTopology.continuous_of_linearMap eL.symm.toLinearMap`. Set `eH : A.L ≃ₜ A₁.L × A₂.L` to `⟨eL.toEquiv, hc₁, hc₂⟩`.

Take `⟨c, hc0, hc⟩` from `fourB_split eL.toRingEquiv.toAddEquiv hc₁ hc₂ (A.kerL ψ x) (A₁.kerL ψ x₁) (A₂.kerL ψ x₂) (continuous_kerL A₁ ψ hψ _) (continuous_kerL A₂ ψ hψ _) (fun y' y => kerL_split A A₁ A₂ eK eL hS ψ x y' y) μ μ₁ μ₂ hμ.1 hμ₁.1 hμ₂.1`. Set `ρ : SpecialLinearGroup (Fin 2) A.K →* SpecialLinearGroup (Fin 2) A₁.K × SpecialLinearGroup (Fin 2) A₂.K` to `(SpecialLinearGroup.map f₁).prod (SpecialLinearGroup.map f₂)`. Take `⟨hT, hfib⟩` from `tensor_isTestRep W₁ W₂ hW₁.1 hW₂.1`. Use `⟨γ₁ * γ₂ / c, transRep ρ eH.toEquiv (tensorRep W₁ W₂), isTestRep_transRep ρ eH _ hT, fun φ hφ => ?_⟩` and prove the remaining obligations. Establish `hf : IsTest (φ ∘ eH.symm)` using `isTest_comp_homeomorph eH.symm hφ`.

Take `⟨hf1, hf2⟩` from `hfib _ hf`. Establish `hy : ∀ y, eH.symm (eL y) = y` using `fun y => eL.symm_apply_apply y`. Establish `hx₁ : ((x₁ : A₁.Kˣ) : A₁.K) = (eK x).1` using `rfl`. Establish `hx₂ : ((x₂ : A₂.Kˣ) : A₂.K) = (eK x).2` using `rfl`. Use `⟨fun z y => ?_, fun s y => ?_, fun y => ?_⟩` and prove the remaining obligations.

Use `show tensorRep W₁ W₂ (ρ (nS z)) (φ ∘ eH.symm) (eL y) = _`. Establish `hρ : ρ (nS z) = (nS (eK z).1, nS (eK z).2)` using `Prod.ext (map_nS f₁ z) (map_nS f₂ z)`. Rewrite using `[hρ, rel_n A A₁ A₂ eK eL hS ψ x W₁ W₂ γ₁ γ₂ μ₁ μ₂ hW₁ hW₂ _ hf1 hf2]`. Simplify using `[hy]`. Use `show tensorRep W₁ W₂ (ρ (mS s)) (φ ∘ eH.symm) (eL y) = _`.

Establish `hρ : ρ (mS s) = (mS (Units.map (f₁ : A.K →* A₁.K) s), mS (Units.map (f₂ : A.K →* A₂.K) s))` using `Prod.ext (map_mS f₁ s) (map_mS f₂ s)`. Rewrite using `[hρ, rel_m A A₁ A₂ eK eL hS ψ x W₁ W₂ γ₁ γ₂ μ₁ μ₂ hW₁ hW₂ _ hf1 hf2 s _ _ rfl rfl]`. Simplify using `[hy]`. Use `show tensorRep W₁ W₂ (ρ (wS A.K)) (φ ∘ eH.symm) (eL y) = _`. Establish `hρ : ρ (wS A.K) = (wS A₁.K, wS A₂.K)` using `Prod.ext (map_wS f₁) (map_wS f₂)`.

Rewrite using `[hρ, rel_w A A₁ A₂ eK eL hS ψ x W₁ W₂ γ₁ γ₂ μ₁ μ₂ hW₁ hW₂ _ hf1 hf2, hc φ hφ y]`. Simplify using `only [Function.comp]`. Clear the denominators using the available nonvanishing facts. Both sides reduce to the same expression.
-/
theorem weilAt_prod : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E]
    [StarRing E] [Unram F E] (A A₁ A₂ : Et F E) (eK : A.K ≃ₐ[F] A₁.K × A₂.K) (eL : A.L ≃ₐ[F] A₁.L × A₂.L),
    IsSplitting A A₁ A₂ eK eL → WeilAt A₁ → WeilAt A₂ → WeilAt A := by
  intro F E _ _ _ _ U A A₁ A₂ eK eL hS h₁ h₂ ψ hψ x μ hμ
  have := U.ultraF; have := U.lcF
  have := EtMeas.finite_L A; have := EtMeas.finite_L A₁; have := EtMeas.finite_L A₂
  obtain ⟨_, _, _, _, -⟩ := EtMeas.top_facts F A.L
  obtain ⟨_, _, _, _, -⟩ := EtMeas.top_facts F A₁.L
  obtain ⟨_, _, _, _, -⟩ := EtMeas.top_facts F A₂.L
  let f₁ : A.K →+* A₁.K := (RingHom.fst A₁.K A₂.K).comp (eK : A.K →+* A₁.K × A₂.K)
  let f₂ : A.K →+* A₂.K := (RingHom.snd A₁.K A₂.K).comp (eK : A.K →+* A₁.K × A₂.K)
  let x₁ : A₁.Kˣ := Units.map (f₁ : A.K →* A₁.K) x
  let x₂ : A₂.Kˣ := Units.map (f₂ : A.K →* A₂.K) x
  obtain ⟨μ₁, hμ₁⟩ := EtMeas.exists_selfDual_L A₁ ψ hψ x₁
  obtain ⟨μ₂, hμ₂⟩ := EtMeas.exists_selfDual_L A₂ ψ hψ x₂
  obtain ⟨γ₁, W₁, hW₁⟩ := h₁ ψ hψ x₁ μ₁ hμ₁
  obtain ⟨γ₂, W₂, hW₂⟩ := h₂ ψ hψ x₂ μ₂ hμ₂
  have hc₁ : Continuous eL := IsModuleTopology.continuous_of_linearMap eL.toLinearMap
  have hc₂ : Continuous eL.symm := IsModuleTopology.continuous_of_linearMap eL.symm.toLinearMap
  let eH : A.L ≃ₜ A₁.L × A₂.L := ⟨eL.toEquiv, hc₁, hc₂⟩
  obtain ⟨c, hc0, hc⟩ := fourB_split eL.toRingEquiv.toAddEquiv hc₁ hc₂ (A.kerL ψ x) (A₁.kerL ψ x₁)
    (A₂.kerL ψ x₂) (continuous_kerL A₁ ψ hψ _) (continuous_kerL A₂ ψ hψ _)
    (fun y' y => kerL_split A A₁ A₂ eK eL hS ψ x y' y) μ μ₁ μ₂ hμ.1 hμ₁.1 hμ₂.1
  let ρ : SpecialLinearGroup (Fin 2) A.K →* SpecialLinearGroup (Fin 2) A₁.K × SpecialLinearGroup (Fin 2) A₂.K :=
    (SpecialLinearGroup.map f₁).prod (SpecialLinearGroup.map f₂)
  obtain ⟨hT, hfib⟩ := tensor_isTestRep W₁ W₂ hW₁.1 hW₂.1
  refine ⟨γ₁ * γ₂ / c, transRep ρ eH.toEquiv (tensorRep W₁ W₂), isTestRep_transRep ρ eH _ hT, fun φ hφ => ?_⟩
  have hf : IsTest (φ ∘ eH.symm) := isTest_comp_homeomorph eH.symm hφ
  obtain ⟨hf1, hf2⟩ := hfib _ hf
  have hy : ∀ y, eH.symm (eL y) = y := fun y => eL.symm_apply_apply y
  have hx₁ : ((x₁ : A₁.Kˣ) : A₁.K) = (eK x).1 := rfl
  have hx₂ : ((x₂ : A₂.Kˣ) : A₂.K) = (eK x).2 := rfl
  refine ⟨fun z y => ?_, fun s y => ?_, fun y => ?_⟩
  · show tensorRep W₁ W₂ (ρ (nS z)) (φ ∘ eH.symm) (eL y) = _
    have hρ : ρ (nS z) = (nS (eK z).1, nS (eK z).2) := Prod.ext (map_nS f₁ z) (map_nS f₂ z)
    rw [hρ, rel_n A A₁ A₂ eK eL hS ψ x W₁ W₂ γ₁ γ₂ μ₁ μ₂ hW₁ hW₂ _ hf1 hf2]
    simp [hy]
  · show tensorRep W₁ W₂ (ρ (mS s)) (φ ∘ eH.symm) (eL y) = _
    have hρ : ρ (mS s) = (mS (Units.map (f₁ : A.K →* A₁.K) s), mS (Units.map (f₂ : A.K →* A₂.K) s)) :=
      Prod.ext (map_mS f₁ s) (map_mS f₂ s)
    rw [hρ, rel_m A A₁ A₂ eK eL hS ψ x W₁ W₂ γ₁ γ₂ μ₁ μ₂ hW₁ hW₂ _ hf1 hf2 s _ _ rfl rfl]
    simp [hy]
  · show tensorRep W₁ W₂ (ρ (wS A.K)) (φ ∘ eH.symm) (eL y) = _
    have hρ : ρ (wS A.K) = (wS A₁.K, wS A₂.K) := Prod.ext (map_wS f₁) (map_wS f₂)
    rw [hρ, rel_w A A₁ A₂ eK eL hS ψ x W₁ W₂ γ₁ γ₂ μ₁ μ₂ hW₁ hW₂ _ hf1 hf2, hc φ hφ y]
    simp only [Function.comp]
    field_simp
    rfl

end GlobalTheory.JR.WeilProd

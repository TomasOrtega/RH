import Mathlib
import Formalism.SharpRestriction.GrowthBounds.WeilJacquetShalikaLaw
import Formalism.SharpRestriction.GrowthBounds.FormalGroupSystem
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.FrameTransport
import Formalism.SharpRestriction.CuspSpanNormBounds.PsiEDef
import Formalism.LocalRingCardinality.DataKerP
import Formalism.SharpRestriction.GlobalSchurBounds.ProductFirstZerothParts
import Formalism.SharpRestriction.Divisibility.ZetaProductPairs
import Formalism.SharpRestriction.Divisibility.InnerProductFormulaField
import Formalism.SharpRestriction.CuspSpanNormBounds.GlobAut
import Formalism.SharpRestriction.CuspSpanNormBounds.RelevantZeroGramTerms
import Formalism.LocalRingCardinality.DataTies
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.T2SpaceNumberFieldInfiniteAdeles
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsUniqueOneVectorStepHaarMeasureStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsBasisInvariantHaarFamilyAdelicUnitaryStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsCoboundaryOfInvariantUnitaryStepConstantsStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UnitaryOneVectorStepCompatibleChangeOfBasisStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UnitaryStabilizerMeasureIndependentOfPathStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NonemptyStandardLocalHaarMeasuresStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.QuadricFibreMeasureEqSmulNormalisedProductStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsUniqueStdHermitianFibreProductOfRankGeThreStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsNontrivialAdeleCharTrivialOnTotallyRealStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UnitaryStabilizerAnisotropicVectorEquivComplemenStatement

open NumberField IsDedekindDomain MeasureTheory Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.GaugeEx
open scoped TensorProduct NNReal ENNReal

namespace GlobalTheory.GaugeEx

section Scale

variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] {σ : E →ₐ[F] E}

/- English proof (translation)
Introduce `f hf sec hsec`. Simplify using `only [lintegral_smul_measure, ENNReal.smul_def, smul_eq_mul]`. Rewrite using `[h f hf sec hsec]`. Simplify using `only [lintegral_const_mul' _ _ ENNReal.coe_ne_top]`. Use `push_cast`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem isCompatible_smul {M : ℕ} {J : Matrix (Fin M) (Fin M) E} {x : Fin 1 → Fin M → E}
    {μ : Measure (HA (AF F) σ J)} {μ' : Measure (Hstab (AF F) σ J x)}
    {ν : Measure (Fin 1 → Fin M → AF F ⊗[F] E)} (h : IsCompatible F E σ M J x μ μ' ν) (c k : ℝ≥0) :
    IsCompatible F E σ M J x ((k * c) • μ) (c • μ') (k • ν) := by
  intro f hf sec hsec
  simp only [lintegral_smul_measure, ENNReal.smul_def, smul_eq_mul]
  rw [h f hf sec hsec]
  simp only [lintegral_const_mul' _ _ ENNReal.coe_ne_top]
  push_cast
  ring

/- English proof (translation)
Introduce `ν hν e he`. Establish `hc` using `isCompatible_smul (h ν hν e he) c 1`. Simplify `hc` using `only [one_mul, one_smul, Measure.map_smul]`.
-/
theorem StepRel.smul {d : ℕ} {b : Module.Basis (Fin d) F E} {s : StdMeas b} {M : ℕ}
    {J : Matrix (Fin (M + 1)) (Fin (M + 1)) E} {x : Fin 1 → Fin (M + 1) → E} {β : F}
    {B : Matrix (Fin (M + 1)) (Fin M) E} {J' : Matrix (Fin M) (Fin M) E}
    {μ : Measure (HA (AF F) σ J)} {μ' : Measure (HA (AF F) σ J')}
    (h : StepRel s σ J x β B J' μ μ') (c : ℝ≥0) : StepRel s σ J x β B J' (c • μ) (c • μ') := by
  intro ν hν e he
  have hc := isCompatible_smul (h ν hν e he) c 1
  simpa only [one_mul, one_smul, Measure.map_smul] using hc

end Scale

/- English proof (translation)
Take `⟨K, hK, hK1⟩` from `exists_compact_mem_nhds (1 : G)`. Establish `hpos : μ K ≠ 0` using `(μ.measure_pos_of_nonempty_interior ⟨1, mem_interior_iff_mem_nhds.2 hK1⟩).ne'`. Establish `htop : μ K ≠ ⊤` using `hK.measure_lt_top.ne`. Establish `h2` using `congrArg (fun m : Measure G => m K) h`. Simplify using `only [Measure.smul_apply, ENNReal.smul_def, smul_eq_mul] at h2`.

Conclude with `ENNReal.coe_injective ((ENNReal.mul_left_inj hpos htop).1 h2)`.
-/
theorem smul_haar_inj {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [LocallyCompactSpace G] [MeasurableSpace G] (μ : Measure G) [μ.IsHaarMeasure] {c c' : ℝ≥0}
    (h : c • μ = c' • μ) : c = c' := by
  obtain ⟨K, hK, hK1⟩ := exists_compact_mem_nhds (1 : G)
  have hpos : μ K ≠ 0 :=
    (μ.measure_pos_of_nonempty_interior ⟨1, mem_interior_iff_mem_nhds.2 hK1⟩).ne'
  have htop : μ K ≠ ⊤ := hK.measure_lt_top.ne
  have h2 := congrArg (fun m : Measure G => m K) h
  simp only [Measure.smul_apply, ENNReal.smul_def, smul_eq_mul] at h2
  exact ENNReal.coe_injective ((ENNReal.mul_left_inj hpos htop).1 h2)

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E}

/- English proof (translation)
Take `⟨-, -, h1, -, h2, -⟩` from `h`. Take `⟨-, -, h1', -, h2', -⟩` from `h'`. Conclude with `⟨(algebraMap F E).injective (h1.symm.trans h1'), h2.trans h2'.symm⟩`.
-/
theorem stepData_unique {M : ℕ} {J : Matrix (Fin (M + 1)) (Fin (M + 1)) E} {x : Fin 1 → Fin (M + 1) → E}
    {a a' : F} {B : Matrix (Fin (M + 1)) (Fin M) E} {J' J'' : Matrix (Fin M) (Fin M) E}
    (h : StepData σ J x a B J') (h' : StepData σ J x a' B J'') : a = a' ∧ J' = J'' := by
  obtain ⟨-, -, h1, -, h2, -⟩ := h
  obtain ⟨-, -, h1', -, h2', -⟩ := h'
  exact ⟨(algebraMap F E).injective (h1.symm.trans h1'), h2.trans h2'.symm⟩

/- English proof (translation)
Use `haveI : FiniteDimensional F E := Module.finite_of_finrank_pos (by rw [hσ.2.2.1]; norm_num)`. Establish `key : ∀ (M : ℕ) (J : Matrix (Fin (M + 1)) (Fin (M + 1)) E) (x : Fin 1 → Fin (M + 1) → E) (a : F) (B : Matrix (Fin (M + 1)) (Fin M) E) (J' : Matrix (Fin M) (Fin M) E), 2 ≤ M → StepData σ J x a B J' → ∃ u : ℝ≥0ˣ, StepRel s σ J x a B J' ((u : ℝ≥0) • G.μ (M + 1) J) (G.μ M J')`. Introduce `M J x a B J' hM hS`. Use `haveI : (G.μ M J').IsHaarMeasure := hG M J' hS.2.2.2.2.2`. Use `haveI : (G.μ (M + 1) J).IsHaarMeasure := hG (M + 1) J hS.1`.

Take `⟨⟨μ, hμ, hrel⟩, -⟩` from `GlobalTheory.T.exists_unique_oneVectorStep_haarMeasure F E σ hσ d b s M J x a B J' (G.μ M J') hM hS inferInstance`. Use `haveI := hμ`. Use `⟨Units.mk0 (Measure.haarScalarFactor μ (G.μ (M + 1) J)) (Measure.haarScalarFactor_pos_of_isHaarMeasure _ _).ne', ?_⟩` and prove the remaining obligations. Rewrite using `[Units.val_mk0, ← Measure.isMulLeftInvariant_eq_smul]`. Conclude with `hrel`.

Use `⟨fun M J x B => if h : ∃ u : ℝ≥0ˣ, ∃ (a : F) (J' : Matrix (Fin M) (Fin M) E), 2 ≤ M ∧ StepData σ J x a B J' ∧ StepRel s σ J x a B J' ((u : ℝ≥0) • G.μ (M + 1) J) (G.μ M J') then h.choose else 1, ?_⟩` and prove the remaining obligations. Introduce `M J x a B J' hM hS`. Establish `hex : ∃ u : ℝ≥0ˣ, ∃ (a : F) (J' : Matrix (Fin M) (Fin M) E), 2 ≤ M ∧ StepData σ J x a B J' ∧ StepRel s σ J x a B J' ((u : ℝ≥0) • G.μ (M + 1) J) (G.μ M J')`. Take `⟨u, hu⟩` from `key M J x a B J' hM hS`. Conclude with `⟨u, a, J', hM, hS, hu⟩`.

Simplify using `only [dif_pos hex]`. Take `⟨a₀, J₀, -, hS₀, hR₀⟩` from `hex.choose_spec`. Take `⟨rfl, rfl⟩` from `stepData_unique hS₀ hS`. Conclude with `hR₀`.
-/
theorem exists_const (hσ : IsCMExt F E σ) {d : ℕ} {b : Module.Basis (Fin d) F E} (s : StdMeas b)
    (G : GaugeFam F E σ) (hG : G.IsHaar) :
    ∃ c : ∀ M : ℕ, Matrix (Fin (M + 1)) (Fin (M + 1)) E → (Fin 1 → Fin (M + 1) → E) →
      Matrix (Fin (M + 1)) (Fin M) E → ℝ≥0ˣ,
      ∀ M J x a B J', 2 ≤ M → StepData σ J x a B J' →
        StepRel s σ J x a B J' ((c M J x B : ℝ≥0) • G.μ (M + 1) J) (G.μ M J') := by
  classical
  haveI : FiniteDimensional F E := Module.finite_of_finrank_pos (by rw [hσ.2.2.1]; norm_num)
  have key : ∀ (M : ℕ) (J : Matrix (Fin (M + 1)) (Fin (M + 1)) E) (x : Fin 1 → Fin (M + 1) → E)
      (a : F) (B : Matrix (Fin (M + 1)) (Fin M) E) (J' : Matrix (Fin M) (Fin M) E),
      2 ≤ M → StepData σ J x a B J' →
      ∃ u : ℝ≥0ˣ, StepRel s σ J x a B J' ((u : ℝ≥0) • G.μ (M + 1) J) (G.μ M J') := by
    intro M J x a B J' hM hS
    haveI : (G.μ M J').IsHaarMeasure := hG M J' hS.2.2.2.2.2
    haveI : (G.μ (M + 1) J).IsHaarMeasure := hG (M + 1) J hS.1
    obtain ⟨⟨μ, hμ, hrel⟩, -⟩ :=
      GlobalTheory.T.exists_unique_oneVectorStep_haarMeasure F E σ hσ d b s M J x a B J' (G.μ M J') hM hS inferInstance
    haveI := hμ
    refine ⟨Units.mk0 (Measure.haarScalarFactor μ (G.μ (M + 1) J))
      (Measure.haarScalarFactor_pos_of_isHaarMeasure _ _).ne', ?_⟩
    rw [Units.val_mk0, ← Measure.isMulLeftInvariant_eq_smul]
    exact hrel
  refine ⟨fun M J x B => if h : ∃ u : ℝ≥0ˣ, ∃ (a : F) (J' : Matrix (Fin M) (Fin M) E), 2 ≤ M ∧
      StepData σ J x a B J' ∧ StepRel s σ J x a B J' ((u : ℝ≥0) • G.μ (M + 1) J) (G.μ M J')
    then h.choose else 1, ?_⟩
  intro M J x a B J' hM hS
  have hex : ∃ u : ℝ≥0ˣ, ∃ (a : F) (J' : Matrix (Fin M) (Fin M) E), 2 ≤ M ∧
      StepData σ J x a B J' ∧ StepRel s σ J x a B J' ((u : ℝ≥0) • G.μ (M + 1) J) (G.μ M J') := by
    obtain ⟨u, hu⟩ := key M J x a B J' hM hS
    exact ⟨u, a, J', hM, hS, hu⟩
  simp only [dif_pos hex]
  obtain ⟨a₀, J₀, -, hS₀, hR₀⟩ := hex.choose_spec
  obtain ⟨rfl, rfl⟩ := stepData_unique hS₀ hS
  exact hR₀

/- English proof (translation)
Take `⟨G, hH, hB⟩` from `GlobalTheory.T.exists_basisInvariant_haar_family_adelicUnitary F E σ hσ`. Take `⟨c, hc⟩` from `exists_const hσ s G hH`. Use `(GlobalTheory.T.exists_coboundary_of_invariant_unitary_step_constants F E σ hσ ℝ≥0ˣ c ?inv ?coc).elim fun α hα => ?main` and prove the remaining obligations. Use `case main =>`. Take `⟨hαinv, hαstep⟩` from `hα`.

Use `⟨G, α, hH, hB, hαinv, ?_⟩` and prove the remaining obligations. Introduce `M J x a B J' hM hS`. Establish `r` using `(hc M J x a B J' hM hS).smul (α M J' : ℝ≥0)`. Rewrite `r` using `[smul_smul]`. Rewrite using `[hαstep M J x a B J' hM hS, Units.val_mul, mul_comm]`.

Conclude with `r`. Use `case inv =>`. Introduce `M J x a B J' x₂ B₂ P Q hM hS hx hPB`. Take `⟨J₂, hJ₂⟩ : ∃ J₂, J₂ = Formalism.UG.cT (σ : E →+* E) (P : Matrix (Fin (M + 1)) (Fin (M + 1)) E) * J * (P : Matrix (Fin (M + 1)) (Fin (M + 1)) E)` from `⟨_, rfl⟩`. Take `⟨J₂', hJ₂'⟩ : ∃ J₂', J₂' = Formalism.UG.cT (σ : E →+* E) (Q : Matrix (Fin M) (Fin M) E) * J' * (Q : Matrix (Fin M) (Fin M) E)` from `⟨_, rfl⟩`.

Rewrite using `[← hJ₂]`. Take `⟨⟨eP, heP⟩, hmapP⟩` from `hB (M + 1) J J₂ P hS.1 hJ₂`. Take `⟨⟨eQ, heQ⟩, hmapQ⟩` from `hB M J' J₂' Q hS.2.2.2.2.2 hJ₂'`. Take `⟨hS₂, hR₂⟩` from `GlobalTheory.T.unitaryOneVectorStep_compatible_changeOfBasis F E σ hσ _ b s M J J₂ x a B J' x₂ B₂ J₂' P Q eP eQ _ _ hS hJ₂ hJ₂' hx hPB heP heQ (hc M J x a B J' hM hS)`. Rewrite `hR₂` using `[Measure.map_smul, hmapP eP heP, hmapQ eQ heQ]`.

Establish `hR₃` using `hc M J₂ x₂ a B₂ J₂' hM hS₂`. Establish `hHaar₂ : (G.μ M J₂').IsHaarMeasure` using `hH M J₂' hS₂.2.2.2.2.2`. Establish `huniq` using `(GlobalTheory.T.exists_unique_oneVectorStep_haarMeasure F E σ hσ _ b s M J₂ x₂ a B₂ J₂' (G.μ M J₂') hM hS₂ hHaar₂).2 _ _ hR₃ hR₂`. Use `haveI : (G.μ (M + 1) J₂).IsHaarMeasure := hH (M + 1) J₂ hS₂.1`. Conclude with `Units.ext (smul_haar_inj _ huniq)`.

Use `case coc =>`. Introduce `M J x₁ x₂ a₁ a₂ B₁ B₂ J₁ J₂ y₁ y₂ b₁ b₂ C₁ C₂ J₀ hM h1 h1' h2 h2' hBC`. Use `haveI : (G.μ M J₀).IsHaarMeasure := hH M J₀ h1'.2.2.2.2.2`. Use `haveI : (G.μ (M + 1 + 1) J).IsHaarMeasure := hH _ J h1.1`. Establish `r1` using `(hc (M + 1) J x₁ a₁ B₁ J₁ (by omega) h1).smul (c M J₁ y₁ C₁ : ℝ≥0)`.

Establish `r2` using `(hc (M + 1) J x₂ a₂ B₂ J₂ (by omega) h2).smul (c M J₂ y₂ C₂ : ℝ≥0)`. Establish `heq` using `GlobalTheory.T.unitaryStabilizer_measure_independent_of_path F E σ hσ _ b s M J x₁ x₂ a₁ a₂ B₁ B₂ J₁ J₂ y₁ y₂ b₁ b₂ C₁ C₂ J₀ (G.μ M J₀) _ _ _ _ hM h1 h1' h2 h2' hBC inferInstance (hc M J₁ y₁ b₁ C₁ J₀ hM h1') r1 (hc M J₂ y₂ b₂ C₂ J₀ hM h2') r2`. Rewrite `heq` using `[smul_smul, smul_smul]`. Establish `he` using `smul_haar_inj _ heq`. Apply `Units.ext` to reduce the goal to its premises.

Rewrite using `[Units.val_mul, Units.val_mul, mul_comm, he, mul_comm]`.
-/
theorem exists_std_family (hσ : IsCMExt F E σ) {d : ℕ} {b : Module.Basis (Fin d) F E} (s : StdMeas b) :
    ∃ (G : GaugeFam F E σ) (α : ∀ M : ℕ, Matrix (Fin M) (Fin M) E → ℝ≥0ˣ), G.IsHaar ∧ G.BasisInv ∧
      (∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E) (P : GL (Fin M) E), IsHermND σ J →
        α M (Formalism.UG.cT (σ : E →+* E) (P : Matrix (Fin M) (Fin M) E) * J * (P : Matrix (Fin M) (Fin M) E)) =
          α M J) ∧
      ∀ M J x a B J', 2 ≤ M → StepData σ J x a B J' →
        StepRel s σ J x a B J' ((α (M + 1) J : ℝ≥0) • G.μ (M + 1) J) ((α M J' : ℝ≥0) • G.μ M J') := by
  classical
  obtain ⟨G, hH, hB⟩ := GlobalTheory.T.exists_basisInvariant_haar_family_adelicUnitary F E σ hσ
  obtain ⟨c, hc⟩ := exists_const hσ s G hH
  refine (GlobalTheory.T.exists_coboundary_of_invariant_unitary_step_constants F E σ hσ ℝ≥0ˣ c ?inv ?coc).elim fun α hα => ?main
  case main =>
    obtain ⟨hαinv, hαstep⟩ := hα
    refine ⟨G, α, hH, hB, hαinv, ?_⟩
    intro M J x a B J' hM hS
    have r := (hc M J x a B J' hM hS).smul (α M J' : ℝ≥0)
    rw [smul_smul] at r
    rw [hαstep M J x a B J' hM hS, Units.val_mul, mul_comm]
    exact r
  case inv =>
    intro M J x a B J' x₂ B₂ P Q hM hS hx hPB
    obtain ⟨J₂, hJ₂⟩ : ∃ J₂, J₂ = Formalism.UG.cT (σ : E →+* E) (P : Matrix (Fin (M + 1)) (Fin (M + 1)) E) *
        J * (P : Matrix (Fin (M + 1)) (Fin (M + 1)) E) := ⟨_, rfl⟩
    obtain ⟨J₂', hJ₂'⟩ : ∃ J₂', J₂' = Formalism.UG.cT (σ : E →+* E) (Q : Matrix (Fin M) (Fin M) E) *
        J' * (Q : Matrix (Fin M) (Fin M) E) := ⟨_, rfl⟩
    rw [← hJ₂]
    obtain ⟨⟨eP, heP⟩, hmapP⟩ := hB (M + 1) J J₂ P hS.1 hJ₂
    obtain ⟨⟨eQ, heQ⟩, hmapQ⟩ := hB M J' J₂' Q hS.2.2.2.2.2 hJ₂'
    obtain ⟨hS₂, hR₂⟩ := GlobalTheory.T.unitaryOneVectorStep_compatible_changeOfBasis F E σ hσ _ b s M J J₂ x a B J' x₂ B₂ J₂' P Q eP eQ _ _ hS hJ₂
      hJ₂' hx hPB heP heQ (hc M J x a B J' hM hS)
    rw [Measure.map_smul, hmapP eP heP, hmapQ eQ heQ] at hR₂
    have hR₃ := hc M J₂ x₂ a B₂ J₂' hM hS₂
    have hHaar₂ : (G.μ M J₂').IsHaarMeasure := hH M J₂' hS₂.2.2.2.2.2
    have huniq := (GlobalTheory.T.exists_unique_oneVectorStep_haarMeasure F E σ hσ _ b s M J₂ x₂ a B₂ J₂' (G.μ M J₂') hM hS₂ hHaar₂).2 _ _
      hR₃ hR₂
    haveI : (G.μ (M + 1) J₂).IsHaarMeasure := hH (M + 1) J₂ hS₂.1
    exact Units.ext (smul_haar_inj _ huniq)
  case coc =>
    intro M J x₁ x₂ a₁ a₂ B₁ B₂ J₁ J₂ y₁ y₂ b₁ b₂ C₁ C₂ J₀ hM h1 h1' h2 h2' hBC
    haveI : (G.μ M J₀).IsHaarMeasure := hH M J₀ h1'.2.2.2.2.2
    haveI : (G.μ (M + 1 + 1) J).IsHaarMeasure := hH _ J h1.1
    have r1 := (hc (M + 1) J x₁ a₁ B₁ J₁ (by omega) h1).smul (c M J₁ y₁ C₁ : ℝ≥0)
    have r2 := (hc (M + 1) J x₂ a₂ B₂ J₂ (by omega) h2).smul (c M J₂ y₂ C₂ : ℝ≥0)
    have heq := GlobalTheory.T.unitaryStabilizer_measure_independent_of_path F E σ hσ _ b s M J x₁ x₂ a₁ a₂ B₁ B₂ J₁ J₂ y₁ y₂ b₁ b₂ C₁ C₂ J₀
      (G.μ M J₀) _ _ _ _ hM h1 h1' h2 h2' hBC inferInstance (hc M J₁ y₁ b₁ C₁ J₀ hM h1') r1
      (hc M J₂ y₂ b₂ C₂ J₀ hM h2') r2
    rw [smul_smul, smul_smul] at heq
    have he := smul_haar_inj _ heq
    apply Units.ext
    rw [Units.val_mul, Units.val_mul, mul_comm, he, mul_comm]

/- English proof (translation)
Use `haveI : FiniteDimensional F E := Module.finite_of_finrank_pos (by rw [hσ.2.2.1]; norm_num)`. Use `haveI : IsTotallyReal F := hσ.1`. Take `⟨s⟩` from `GlobalTheory.T.nonempty_standardLocalHaarMeasures F E _ (Module.finBasis F E)`. Take `⟨G, α, hH, hB, hαinv, hstep⟩` from `exists_std_family hσ s`. Take `⟨κ, hκ0, hκ⟩` from `GlobalTheory.T.quadricFibreMeasure_eq_smul_normalisedProduct F E σ hσ _ _ s`.

Take `⟨ψ, hψ⟩` from `GlobalTheory.T.exists_nontrivial_adeleChar_trivial_on_totallyReal F`. Take `⟨K, hK⟩ : ∃ K : ℕ → ℝ≥0, K = fun M => ∏ i ∈ Finset.range (M + 1), κ i` from `⟨_, rfl⟩`. Establish `hK0 : ∀ M, K M ≠ 0` using `fun M => by`. Rewrite using `[hK]`. Conclude with `Finset.prod_ne_zero_iff.2 fun i _ => hκ0 i`.

Establish `hKs : ∀ M, K (M + 1) = κ (M + 1) * K M` using `fun M => by`. Rewrite using `[hK]`. Simplify using `only [Finset.prod_range_succ (n := M + 1)]`. Expand and normalize the polynomial expressions, which then agree. Use `⟨⟨fun M J => (K M * α M J : ℝ≥0) • G.μ M J⟩, ?_, ?_, ?_⟩` and prove the remaining obligations.

Introduce `M J hJ haveI : (G.μ M J).IsHaarMeasure := hH M J hJ`. Conclude with `Measure.IsHaarMeasure.nnreal_smul _ (mul_ne_zero (hK0 M) (α M J).ne_zero)`. Introduce `M J J' P hJ hJ'`. Take `⟨⟨e, he⟩, hmap⟩` from `hB M J J' P hJ hJ'`. Use `⟨⟨e, he⟩, fun e' he' => ?_⟩` and prove the remaining obligations.

Use `show ((K M * α M J : ℝ≥0) • G.μ M J).map e' = (K M * α M J' : ℝ≥0) • G.μ M J'`. Rewrite using `[Measure.map_smul, hmap e' he', hJ', hαinv M J P hJ]`. Introduce `M J J' x β B hM hJ hβ hx hB' hJ'' hJ'`. Establish `hS : StepData σ J x β B J'` using `⟨hJ, hβ, hx, hB', hJ'', hJ'⟩`. Take `⟨ν, hν, -⟩` from `GlobalTheory.T.existsUnique_stdHermitianFibreProduct_of_rank_ge_three F E σ hσ _ _ s (M + 1) J β hM hJ hβ`.

Take `⟨e, he, -⟩` from `(GlobalTheory.T.unitary_stabilizer_anisotropic_vector_equiv_complement F E σ hσ (AF F) M J x β B J' hS).2.1`. Use `⟨⟨ψ, hψ⟩, fun ψ' hψ' => ?_⟩` and prove the remaining obligations. Establish `hX` using `hκ (M + 1) J β ψ' ν (by omega) hJ hβ hψ' hν`. Use `⟨⟨_, (hX _).2 rfl⟩, fun νX hνX => ?_⟩` and prove the remaining obligations. Rewrite using `[(hX νX).1 hνX]`.

Use `⟨⟨e, he⟩, fun e' he' => ?_⟩` and prove the remaining obligations. Establish `hc` using `isCompatible_smul (hstep M J x β B J' (by omega) hS ν hν e' he') (K M) (κ (M + 1))`. Use `hc using 1` and compare the differences between its conclusion and the goal. Use `show ((K (M + 1) * α (M + 1) J : ℝ≥0) • G.μ (M + 1) J) = _`. Rewrite using `[smul_smul, hKs, mul_assoc]`.

Use `show ((K M * α M J' : ℝ≥0) • G.μ M J').map e'.symm = _`. Simplify using `only [Measure.map_smul, smul_smul]`.
-/
theorem exists_isGauge_of_isCMExt (hσ : IsCMExt F E σ) : ∃ G : GaugeFam F E σ, G.IsGauge := by
  classical
  haveI : FiniteDimensional F E := Module.finite_of_finrank_pos (by rw [hσ.2.2.1]; norm_num)
  haveI : IsTotallyReal F := hσ.1
  obtain ⟨s⟩ := GlobalTheory.T.nonempty_standardLocalHaarMeasures F E _ (Module.finBasis F E)
  obtain ⟨G, α, hH, hB, hαinv, hstep⟩ := exists_std_family hσ s
  obtain ⟨κ, hκ0, hκ⟩ := GlobalTheory.T.quadricFibreMeasure_eq_smul_normalisedProduct F E σ hσ _ _ s
  obtain ⟨ψ, hψ⟩ := GlobalTheory.T.exists_nontrivial_adeleChar_trivial_on_totallyReal F
  obtain ⟨K, hK⟩ : ∃ K : ℕ → ℝ≥0, K = fun M => ∏ i ∈ Finset.range (M + 1), κ i := ⟨_, rfl⟩
  have hK0 : ∀ M, K M ≠ 0 := fun M => by
    rw [hK]; exact Finset.prod_ne_zero_iff.2 fun i _ => hκ0 i
  have hKs : ∀ M, K (M + 1) = κ (M + 1) * K M := fun M => by
    rw [hK]; simp only [Finset.prod_range_succ (n := M + 1)]; ring
  refine ⟨⟨fun M J => (K M * α M J : ℝ≥0) • G.μ M J⟩, ?_, ?_, ?_⟩
  · intro M J hJ
    haveI : (G.μ M J).IsHaarMeasure := hH M J hJ
    exact Measure.IsHaarMeasure.nnreal_smul _ (mul_ne_zero (hK0 M) (α M J).ne_zero)
  · intro M J J' P hJ hJ'
    obtain ⟨⟨e, he⟩, hmap⟩ := hB M J J' P hJ hJ'
    refine ⟨⟨e, he⟩, fun e' he' => ?_⟩
    show ((K M * α M J : ℝ≥0) • G.μ M J).map e' = (K M * α M J' : ℝ≥0) • G.μ M J'
    rw [Measure.map_smul, hmap e' he', hJ', hαinv M J P hJ]
  · intro M J J' x β B hM hJ hβ hx hB' hJ'' hJ'
    have hS : StepData σ J x β B J' := ⟨hJ, hβ, hx, hB', hJ'', hJ'⟩
    obtain ⟨ν, hν, -⟩ := GlobalTheory.T.existsUnique_stdHermitianFibreProduct_of_rank_ge_three F E σ hσ _ _ s (M + 1) J β hM hJ hβ
    obtain ⟨e, he, -⟩ := (GlobalTheory.T.unitary_stabilizer_anisotropic_vector_equiv_complement F E σ hσ (AF F) M J x β B J' hS).2.1
    refine ⟨⟨ψ, hψ⟩, fun ψ' hψ' => ?_⟩
    have hX := hκ (M + 1) J β ψ' ν (by omega) hJ hβ hψ' hν
    refine ⟨⟨_, (hX _).2 rfl⟩, fun νX hνX => ?_⟩
    rw [(hX νX).1 hνX]
    refine ⟨⟨e, he⟩, fun e' he' => ?_⟩
    have hc := isCompatible_smul (hstep M J x β B J' (by omega) hS ν hν e' he') (K M) (κ (M + 1))
    convert hc using 1
    · show ((K (M + 1) * α (M + 1) J : ℝ≥0) • G.μ (M + 1) J) = _
      rw [smul_smul, hKs, mul_assoc]
    · show ((K M * α M J' : ℝ≥0) • G.μ M J').map e'.symm = _
      simp only [Measure.map_smul, smul_smul]

end GlobalTheory.GaugeEx

open Formalism.BasicNotions Formalism.MainNotions.G in

/- English proof (translation)
Introduce `F E _ _ _ _ _ _ cm`. Establish `hσ : IsCMExt F E cm.sig` using `⟨cm.totReal, cm.cmUnram.1, cm.deg2, fun τ x => cm.cmUnram.2.1 τ x⟩`. Conclude with `exists_isGauge_of_isCMExt hσ`.
-/
theorem GlobalTheory.GaugeEx.exists_isGauge : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] (cm : CMData F E), ∃ G : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.GaugeFam F E cm.sig, G.IsGauge := by
  intro F E _ _ _ _ _ _ cm
  have hσ : IsCMExt F E cm.sig :=
    ⟨cm.totReal, cm.cmUnram.1, cm.deg2, fun τ x => cm.cmUnram.2.1 τ x⟩
  exact exists_isGauge_of_isCMExt hσ

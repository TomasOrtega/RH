import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdaptedPlaneSecondVariableStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaBasicPropertiesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqOfComponentTensorAdelicFunctionEq

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

noncomputable section
namespace GlobalTheory.ThKZeroTermA
open scoped ENNReal
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

/- English proof (translation)
Use `haveI := GlobalTheory.AdelicUnitaryTop.locallyCompact_adele F`. Use `haveI := GlobalTheory.AdelicUnitaryTop.secondCountable_adele F`. Use `haveI := GlobalTheory.AdelicUnitaryTop.t2Space_adeleRing_numberField F`. Use `haveI : IsModuleTopology (AF F) (AE F E) := ⟨rfl⟩`. Use `haveI : IsTopologicalRing (AE F E) := IsModuleTopology.isTopologicalRing (AF F) _`.

Take `⟨e⟩` from `GlobalTheory.AdelicUnitaryTop.nonempty_homeomorph (F := F) (E := E) (AF F)`. Use `haveI : LocallyCompactSpace (AE F E) := e.isClosedEmbedding.locallyCompactSpace`. Use `haveI : SecondCountableTopology (AE F E) := e.secondCountableTopology`. Use `haveI : LocallyCompactSpace (Matrix (Fin n) (Fin n) (AE F E)) := inferInstanceAs (LocallyCompactSpace (Fin n → Fin n → AE F E))`. Use `haveI : LocallyCompactSpace (Matrix (Fin n) (Fin n) (AE F E))ᵐᵒᵖ := MulOpposite.opHomeomorph.symm.isClosedEmbedding.locallyCompactSpace`.

Use `haveI : LocallyCompactSpace (GL (Fin n) (AE F E)) := Units.isClosedEmbedding_embedProduct.locallyCompactSpace`. Use `haveI : SecondCountableTopology (Matrix (Fin n) (Fin n) (AE F E)) := inferInstanceAs (SecondCountableTopology (Fin n → Fin n → AE F E))`. Use `haveI : SecondCountableTopology (Matrix (Fin n) (Fin n) (AE F E))ᵐᵒᵖ := MulOpposite.opHomeomorph.symm.isEmbedding.secondCountableTopology`. Use `haveI : SecondCountableTopology (GL (Fin n) (AE F E)) := Units.isEmbedding_embedProduct.secondCountableTopology`. Establish `hcA : Continuous (cA σ : AE F E → AE F E)` using `IsModuleTopology.continuous_of_linearMap (cA σ).toLinearMap`.

Establish `hc : IsClosed (UG (cA σ) (incM F J) : Set (GL (Fin n) (AE F E)))`. Establish `hv : Continuous fun g : GL (Fin n) (AE F E) => (g : Matrix (Fin n) (Fin n) (AE F E))` using `Units.continuous_val`. Conclude with `isClosed_eq ((hv.matrix_transpose.matrix_mul continuous_const).matrix_mul (hv.matrix_map hcA)) continuous_const`. Conclude with `⟨hc.isClosedEmbedding_subtypeVal.locallyCompactSpace, hc.isClosedEmbedding_subtypeVal.isEmbedding.secondCountableTopology⟩`.
-/
theorem lcsc_UA (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) :
    LocallyCompactSpace (UA σ J) ∧ SecondCountableTopology (UA σ J) := by
  haveI := GlobalTheory.AdelicUnitaryTop.locallyCompact_adele F
  haveI := GlobalTheory.AdelicUnitaryTop.secondCountable_adele F
  haveI := GlobalTheory.AdelicUnitaryTop.t2Space_adeleRing_numberField F
  haveI : IsModuleTopology (AF F) (AE F E) := ⟨rfl⟩
  haveI : IsTopologicalRing (AE F E) := IsModuleTopology.isTopologicalRing (AF F) _
  obtain ⟨e⟩ := GlobalTheory.AdelicUnitaryTop.nonempty_homeomorph (F := F) (E := E) (AF F)
  haveI : LocallyCompactSpace (AE F E) := e.isClosedEmbedding.locallyCompactSpace
  haveI : SecondCountableTopology (AE F E) := e.secondCountableTopology
  haveI : LocallyCompactSpace (Matrix (Fin n) (Fin n) (AE F E)) :=
    inferInstanceAs (LocallyCompactSpace (Fin n → Fin n → AE F E))
  haveI : LocallyCompactSpace (Matrix (Fin n) (Fin n) (AE F E))ᵐᵒᵖ :=
    MulOpposite.opHomeomorph.symm.isClosedEmbedding.locallyCompactSpace
  haveI : LocallyCompactSpace (GL (Fin n) (AE F E)) :=
    Units.isClosedEmbedding_embedProduct.locallyCompactSpace
  haveI : SecondCountableTopology (Matrix (Fin n) (Fin n) (AE F E)) :=
    inferInstanceAs (SecondCountableTopology (Fin n → Fin n → AE F E))
  haveI : SecondCountableTopology (Matrix (Fin n) (Fin n) (AE F E))ᵐᵒᵖ :=
    MulOpposite.opHomeomorph.symm.isEmbedding.secondCountableTopology
  haveI : SecondCountableTopology (GL (Fin n) (AE F E)) :=
    Units.isEmbedding_embedProduct.secondCountableTopology
  have hcA : Continuous (cA σ : AE F E → AE F E) :=
    IsModuleTopology.continuous_of_linearMap (cA σ).toLinearMap
  have hc : IsClosed (UG (cA σ) (incM F J) : Set (GL (Fin n) (AE F E))) := by
    have hv : Continuous fun g : GL (Fin n) (AE F E) => (g : Matrix (Fin n) (Fin n) (AE F E)) :=
      Units.continuous_val
    exact isClosed_eq ((hv.matrix_transpose.matrix_mul continuous_const).matrix_mul (hv.matrix_map hcA))
      continuous_const
  exact ⟨hc.isClosedEmbedding_subtypeVal.locallyCompactSpace,
    hc.isClosedEmbedding_subtypeVal.isEmbedding.secondCountableTopology⟩

/- English proof (translation)
Use `haveI : Countable E := (Module.finBasis ℚ E).equivFun.injective.countable`. Use `haveI : Countable (Matrix (Fin n) (Fin n) E) := inferInstanceAs (Countable (Fin n → Fin n → E))`. Use `haveI : Countable (GL (Fin n) E) := Function.Injective.countable (f := (Units.val : GL (Fin n) E → Matrix (Fin n) (Fin n) E)) fun a b h => Units.ext h`. Establish `h : ∀ x : ratU σ J, ∃ y : GL (Fin n) E, Matrix.GeneralLinearGroup.map (n` using `Fin n) (inclR (F := F) (E := E) (AF F)) y = ((x : UA σ J) : GL (Fin n) (AE F E)) := fun x => x.2`. Use `choose f hf using h`.

Use `Function.Injective.countable (f := f) fun x y hxy => ?_` and prove the remaining obligations. Apply `Subtype.ext` to reduce the goal to its premises. Apply `Subtype.ext` to reduce the goal to its premises. Rewrite using `[← hf x, ← hf y, hxy]`.
-/
theorem countable_ratU (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) : Countable (ratU σ J) := by
  haveI : Countable E := (Module.finBasis ℚ E).equivFun.injective.countable
  haveI : Countable (Matrix (Fin n) (Fin n) E) := inferInstanceAs (Countable (Fin n → Fin n → E))
  haveI : Countable (GL (Fin n) E) :=
    Function.Injective.countable (f := (Units.val : GL (Fin n) E → Matrix (Fin n) (Fin n) E)) fun a b h => Units.ext h
  have h : ∀ x : ratU σ J, ∃ y : GL (Fin n) E,
      Matrix.GeneralLinearGroup.map (n := Fin n) (inclR (F := F) (E := E) (AF F)) y = ((x : UA σ J) : GL (Fin n) (AE F E)) :=
    fun x => x.2
  choose f hf using h
  refine Function.Injective.countable (f := f) fun x y hxy => ?_
  apply Subtype.ext; apply Subtype.ext
  rw [← hf x, ← hf y, hxy]

/- English proof (translation)
Take `⟨h1, h2⟩` from `lcsc_UA σ J`. Use `haveI := countable_ratU σ J`. Use `haveI : BorelSpace (UA σ J) := ⟨rfl⟩`. Use `letI : MeasurableSpace (ratU σ J) := ⊤`. Use `haveI : MeasurableSMul (ratU σ J) (UA σ J) := { measurable_const_smul := fun γ => by`.

Establish `: (fun x : UA σ J => γ • x) = fun x => (γ : UA σ J) * x` using `rfl`. Rewrite using `[this]`. Conclude with `(continuous_const.mul continuous_id).measurable`. Use `measurable_smul_const := fun x => measurable_from_top }`. Use `haveI : SMulInvariantMeasure (ratU σ J) (UA σ J) μ₁ := ⟨fun γ A _ => by`.

Establish `: (fun x : UA σ J => γ • x) = fun x => (γ : UA σ J) * x` using `rfl`. Rewrite using `[this]`. Conclude with `measure_preimage_mul μ₁ (γ : UA σ J) A⟩`. Take `⟨c, he, hpos⟩ : ∃ c : ℝ≥0, μ = (c : ℝ≥0∞) • μ₁ ∧ 0 < c` from `⟨_, Measure.isMulLeftInvariant_eq_smul μ μ₁, Measure.haarScalarFactor_pos_of_isHaarMeasure μ μ₁⟩`. Use `⟨(c : ℝ), by exact_mod_cast hpos, fun D D₁ hD hD₁ f hf => ?_⟩` and prove the remaining obligations.

Substitute `he` using the available equality. Establish `hD' : IsFundamentalDomain (ratU σ J) D μ₁` using `hD.mono (Measure.absolutelyContinuous_smul (by exact_mod_cast hpos.ne'))`. Rewrite using `[Measure.restrict_smul, integral_smul_measure, hD'.setIntegral_eq hD₁ fun γ x => hf γ γ.2 x, ENNReal.coe_toReal, Complex.real_smul]`.
-/
theorem setIntegral_haar (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (μ μ₁ : Measure (UA σ J))
    (hμ : μ.IsHaarMeasure) (hμ₁ : μ₁.IsHaarMeasure) :
    ∃ c : ℝ, 0 < c ∧ ∀ D D₁ : Set (UA σ J), IsFundamentalDomain (ratU σ J) D μ →
      IsFundamentalDomain (ratU σ J) D₁ μ₁ → ∀ f : UA σ J → ℂ, (∀ γ ∈ ratU σ J, ∀ g, f (γ * g) = f g) →
        ∫ g in D, f g ∂μ = (c : ℂ) * ∫ g in D₁, f g ∂μ₁ := by
  obtain ⟨h1, h2⟩ := lcsc_UA σ J
  haveI := countable_ratU σ J
  haveI : BorelSpace (UA σ J) := ⟨rfl⟩
  letI : MeasurableSpace (ratU σ J) := ⊤
  haveI : MeasurableSMul (ratU σ J) (UA σ J) :=
    { measurable_const_smul := fun γ => by
        have : (fun x : UA σ J => γ • x) = fun x => (γ : UA σ J) * x := rfl
        rw [this]; exact (continuous_const.mul continuous_id).measurable
      measurable_smul_const := fun x => measurable_from_top }
  haveI : SMulInvariantMeasure (ratU σ J) (UA σ J) μ₁ :=
    ⟨fun γ A _ => by
      have : (fun x : UA σ J => γ • x) = fun x => (γ : UA σ J) * x := rfl
      rw [this]; exact measure_preimage_mul μ₁ (γ : UA σ J) A⟩
  obtain ⟨c, he, hpos⟩ : ∃ c : ℝ≥0, μ = (c : ℝ≥0∞) • μ₁ ∧ 0 < c :=
    ⟨_, Measure.isMulLeftInvariant_eq_smul μ μ₁, Measure.haarScalarFactor_pos_of_isHaarMeasure μ μ₁⟩
  refine ⟨(c : ℝ), by exact_mod_cast hpos, fun D D₁ hD hD₁ f hf => ?_⟩
  subst he
  have hD' : IsFundamentalDomain (ratU σ J) D μ₁ :=
    hD.mono (Measure.absolutelyContinuous_smul (by exact_mod_cast hpos.ne'))
  rw [Measure.restrict_smul, integral_smul_measure, hD'.setIntegral_eq hD₁ fun γ x => hf γ γ.2 x,
    ENNReal.coe_toReal, Complex.real_smul]

/- English proof (translation)
Introduce `a`. Rewrite using `[MonoidHom.div_apply, Circle.coe_div, hα a, hβ a]`. Use `split_ifs`. Simplify using the standard rewrite rules. Rewrite using `[pow_add]`.

Apply the tactic sequence `rcases neg_one_pow_eq_or ℂ m with h | h <;> rw [h] <;> ring`.
-/
theorem resEta_div {K : Subgroup (AF F)ˣ} {α β : Chr F E} {n m : ℕ} (hα : ResEtaPow K α n) (hβ : ResEtaPow K β m) :
    ResEtaPow K (α / β) (n + m) := by
  intro a
  rw [MonoidHom.div_apply, Circle.coe_div, hα a, hβ a]
  split_ifs
  · simp
  · rw [pow_add]
    rcases neg_one_pow_eq_or ℂ m with h | h <;> rw [h] <;> ring

/- English proof (translation)
Use `⟨?_, fun x => ?_⟩` and prove the remaining obligations. Conclude with `hα.1.div' hβ.1`. Rewrite using `[MonoidHom.div_apply, hα.2 x, hβ.2 x, div_one]`.
-/
theorem isHecke_div {α β : Chr F E} (hα : IsHecke F E α) (hβ : IsHecke F E β) : IsHecke F E (α / β) := by
  refine ⟨?_, fun x => ?_⟩
  · exact hα.1.div' hβ.1
  · rw [MonoidHom.div_apply, hα.2 x, hβ.2 x, div_one]

/- English proof (translation)
Introduce `Φ hΦ`. Use `Submodule.span_le.2 ?_ hΦ` and prove the remaining obligations. Introduce and unpack `_ ⟨f, -, φ, hSB, hcof, rfl⟩`. Conclude with `GlobalTheory.TensUniq.pure_mem_schA f φ hSB ((hcof.and hM.std).mono fun v h => h.1.trans h.2)`.
-/
theorem polData_le {σ : E →ₐ[F] E} (B : Base F E) {n d : ℕ} {X : Spc F E n} {W : Spc F E d} (M : Model σ X W)
    (hM : M.IsGood B.ψ) : ∀ Φ ∈ PolData B M, Φ ∈ schA F (Fin n × Fin d) := by
  intro Φ hΦ
  refine Submodule.span_le.2 ?_ hΦ
  rintro _ ⟨f, -, φ, hSB, hcof, rfl⟩
  exact GlobalTheory.TensUniq.pure_mem_schA f φ hSB ((hcof.and hM.std).mono fun v h => h.1.trans h.2)

/- English proof (translation)
Introduce `hKP F E _ _ _ _ _ σ B b a' G G₁ H H' hC e' he'`. Take `⟨p, q, V, V', W, M, M'⟩` from `G`. Take `⟨p₁, q₁, V₁, V₁', W₁, M₁, M₁'⟩` from `G₁`. Take `⟨eV, q0, q1, ep, hH, hH'⟩` from `hC`. Simplify using `only at eV q0 q1 ep hH hH' he' ⊢`.

Substitute `eV q0 q1` using the available equality. Distinguish the cases in `hμ : M'.μ.IsHaarMeasure ∧ M₁'.μ.IsHaarMeasure`. Use `swap`. Conclude with `⟨1, one_ne_zero, fun X om om' om₁ om₁' hT hT₁ => absurd ⟨hT.geo.hM'.haar, hT₁.geo.hM'.haar⟩ hμ⟩`. Take `⟨c, hc, hint⟩` from `setIntegral_haar σ V₁'.J M'.μ M₁'.μ hμ.1 hμ.2`.

Use `⟨(c : ℂ), by exact_mod_cast hc.ne', fun X om om' om₁ om₁' hT hT₁ Φ' hΦ' h => ?_⟩` and prove the remaining obligations. Establish `hP : IsPair B M' X.α (X.α / X.β) om' 0 (a' - 0) _ _` using `{ base := hT.base, herm := hT.geo.hV', skew := hT.geo.hW, good := hT.geo.hM', hX := hT.chars.heckeα, hW := isHecke_div hT.chars.heckeα hT.chars.heckeβ, resX := hT.chars.resα, resW := by rw [show b + 2 + a' = a' + (b + 2) by omega]; exact resEta_div hT.chars.resα hT.chars.resβ, we …`. Establish `hP₁ : IsPair B M₁' X.α (X.α / X.β) om₁' 0 (a' - 0) _ _` using `{ base := hT₁.base, herm := hT₁.geo.hV', skew := hT₁.geo.hW, good := hT₁.geo.hM', hX := hT₁.chars.heckeα, hW := isHecke_div hT₁.chars.heckeα hT₁.chars.heckeβ, resX := hT₁.chars.resα, resW := by rw [show b + a' = a' + b by omega]; exact resEta_div hT₁.chars.resα hT₁.chars.resβ, we …`. Establish `hmix : ∀ g, ∀ Ψ ∈ schA F (Fin a' × Fin (b + 2 + a')), e' (om' (g, 1) Ψ) = om₁' (g, 1) (e' Ψ)`. Introduce `g Ψ hΨ`.

Establish `m1 : mat (1 : UA σ W.J) = 1` using `rfl`. Establish `m2 : mat (1 : UA σ W₁.J) = 1` using `rfl`. Establish `hL : IsLevi (W₁` using `W₁) H' 1 (1 : UA σ W₁.J) (1 : UA σ W.J) := ⟨by simp [m1], by simp [m1], by simp [m1, m2]⟩`. Use `GlobalTheory.T.adapted_plane_second_variable hKP.base F E σ B a' (b + 2 + a') V₁' W M' X.α (X.α / X.β) om' 0 (a' - 0) _ _ hP (b + a') W₁ H' 0 (b + 1) M₁' om₁' _ _ hH' hP₁ e' he' g 1 1 1 hL 1 (one_mem _) Ψ hΨ` as an intermediate fact. Simplify using `using this`.

Establish `hsch : om' (1, h) Φ' ∈ schA F _` using `(IsUWeilPair.isUSplitting hT.weil').pres _ _ (polData_le B M' hT.geo.hM' Φ' hΦ')`. Establish `hΨ : e' (om' (1, h) Φ') ∈ schA F _` using `he'.maps _ hsch`. Establish `hrw : ∀ g, thetaSum F (e' (om' (g, h) Φ')) = thetaSum F (om₁' (g, 1) (e' (om' (1, h) Φ')))`. Introduce `g`. Rewrite using `[← hmix g _ hsch, ← Module.End.mul_apply, ← map_mul, Prod.mk_mul_mk, mul_one, one_mul]`.

Repeatedly rewrite using `[hrw]`. Establish `hinv` using `((GlobalTheory.T.theta_basic_properties hKP.base F E σ B a' (b + a') V₁' W₁ M₁' X.α (X.α / X.β) om₁' _ _ _ _ hP₁).1 _ hΨ).2.1`. Rewrite using `[Model.I]`. Simplify using `only [theta]`. Use `hint _ _ hT.geo.hM'.dom hT₁.geo.hM'.dom _ fun γ hγ g => ?_` and prove the remaining obligations.

Simplify `hinv γ hγ 1 (one_mem _) g 1` using `[theta]`.
-/
theorem integral_zeroTerm_eq_smul : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (b a' : ℕ) (G : Geo σ (b + 2) a') (G₁ : Geo σ b a') (H : Plane E (b + 2) b) (H' : Plane E (b + 2 + a') (b + a')), CfgA B G G₁ H H' → ∀ e', IsEv B G.M' G₁.M' 1 H'.ι (iso0 a' H') e' → ∃ κ : ℂ, κ ≠ 0 ∧ ∀ X om om' om₁ om₁', IsTriple B G X om om' → IsTriple B G₁ X om₁ om₁' → ∀ Φ' ∈ PolData B G.M', ∀ h, ∫ g in G.M'.dom, thetaSum F (e' (om' (g, h) Φ')) ∂G.M'.μ = κ * G₁.M'.I om₁' (e' (om' (1, h) Φ')) 1 := by
  intro hKP F E _ _ _ _ _ σ B b a' G G₁ H H' hC e' he'
  obtain ⟨p, q, V, V', W, M, M'⟩ := G
  obtain ⟨p₁, q₁, V₁, V₁', W₁, M₁, M₁'⟩ := G₁
  obtain ⟨eV, q0, q1, ep, hH, hH'⟩ := hC
  dsimp only at eV q0 q1 ep hH hH' he' ⊢
  subst eV q0 q1
  by_cases hμ : M'.μ.IsHaarMeasure ∧ M₁'.μ.IsHaarMeasure
  swap
  · exact ⟨1, one_ne_zero, fun X om om' om₁ om₁' hT hT₁ => absurd ⟨hT.geo.hM'.haar, hT₁.geo.hM'.haar⟩ hμ⟩
  obtain ⟨c, hc, hint⟩ := setIntegral_haar σ V₁'.J M'.μ M₁'.μ hμ.1 hμ.2
  refine ⟨(c : ℂ), by exact_mod_cast hc.ne', fun X om om' om₁ om₁' hT hT₁ Φ' hΦ' h => ?_⟩
  have hP : IsPair B M' X.α (X.α / X.β) om' 0 (a' - 0) _ _ :=
    { base := hT.base, herm := hT.geo.hV', skew := hT.geo.hW, good := hT.geo.hM', hX := hT.chars.heckeα,
      hW := isHecke_div hT.chars.heckeα hT.chars.heckeβ, resX := hT.chars.resα,
      resW := by rw [show b + 2 + a' = a' + (b + 2) by omega]; exact resEta_div hT.chars.resα hT.chars.resβ,
      weil := hT.weil' }
  have hP₁ : IsPair B M₁' X.α (X.α / X.β) om₁' 0 (a' - 0) _ _ :=
    { base := hT₁.base, herm := hT₁.geo.hV', skew := hT₁.geo.hW, good := hT₁.geo.hM', hX := hT₁.chars.heckeα,
      hW := isHecke_div hT₁.chars.heckeα hT₁.chars.heckeβ, resX := hT₁.chars.resα,
      resW := by rw [show b + a' = a' + b by omega]; exact resEta_div hT₁.chars.resα hT₁.chars.resβ,
      weil := hT₁.weil' }
  have hmix : ∀ g, ∀ Ψ ∈ schA F (Fin a' × Fin (b + 2 + a')), e' (om' (g, 1) Ψ) = om₁' (g, 1) (e' Ψ) := by
    intro g Ψ hΨ
    have m1 : mat (1 : UA σ W.J) = 1 := rfl
    have m2 : mat (1 : UA σ W₁.J) = 1 := rfl
    have hL : IsLevi (W₁ := W₁) H' 1 (1 : UA σ W₁.J) (1 : UA σ W.J) :=
      ⟨by simp [m1], by simp [m1], by simp [m1, m2]⟩
    have := GlobalTheory.T.adapted_plane_second_variable hKP.base F E σ B a' (b + 2 + a') V₁' W M' X.α (X.α / X.β) om' 0 (a' - 0) _ _ hP (b + a') W₁ H'
      0 (b + 1) M₁' om₁' _ _ hH' hP₁ e' he' g 1 1 1 hL 1 (one_mem _) Ψ hΨ
    simpa using this
  have hsch : om' (1, h) Φ' ∈ schA F _ :=
    (IsUWeilPair.isUSplitting hT.weil').pres _ _ (polData_le B M' hT.geo.hM' Φ' hΦ')
  have hΨ : e' (om' (1, h) Φ') ∈ schA F _ := he'.maps _ hsch
  have hrw : ∀ g, thetaSum F (e' (om' (g, h) Φ')) = thetaSum F (om₁' (g, 1) (e' (om' (1, h) Φ'))) := by
    intro g
    rw [← hmix g _ hsch, ← Module.End.mul_apply, ← map_mul, Prod.mk_mul_mk, mul_one, one_mul]
  simp_rw [hrw]
  have hinv := ((GlobalTheory.T.theta_basic_properties hKP.base F E σ B a' (b + a') V₁' W₁ M₁' X.α (X.α / X.β) om₁' _ _ _ _ hP₁).1 _ hΨ).2.1
  rw [Model.I]
  simp only [theta]
  refine hint _ _ hT.geo.hM'.dom hT₁.geo.hM'.dom _ fun γ hγ g => ?_
  simpa [theta] using hinv γ hγ 1 (one_mem _) g 1

end GlobalTheory.ThKZeroTermA

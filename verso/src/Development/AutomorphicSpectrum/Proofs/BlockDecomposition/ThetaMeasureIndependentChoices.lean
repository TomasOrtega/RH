import Mathlib
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.BinaryMassMeans.MeanVal
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.SiegelWeilMeasureOfCongruentForm
import Development.WeilBound.CoreStatements.ThetaDilations.ThetaLint
import Development.WeilBound.CoreStatements.ThetaDilations.SdTransport
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

noncomputable section

namespace GlobalTheory.CompanionTheory.SW.ThetaIndep

/- English proof (translation)
Introduce `F E _ _ _ _ _ σ hcm M J hJ μ μ' 𝓕 𝓕' hμ h𝓕 hμ' h𝓕₂ n T`. Take `⟨⟨_, _, _⟩, -⟩` from `GlobalTheory.T.adeles_locally_compact_second_countable F`. Take `⟨_, _, _, _, -, -, -, hB, -, hg⟩` from `GlobalTheory.T.tensor_locally_compact_ring F E σ hcm (AF F)`. Use `hB n M` as an intermediate fact. Take `⟨_, _, _, _, _, hact⟩` from `GlobalTheory.T.adelic_unitary_group_locally_compact F E σ hcm M J hJ (AF F)`.

Take `⟨ac, a1, a2, ag⟩` from `hact n`. Establish `hrat` using `(GlobalTheory.T.gram_matrix_local_global F E σ hcm M J hJ n 0 T).2`. Establish `hl` using `PositivityTheory.PlacePermOperatorBicommutantSpan.theta_lint F E σ hcm M J hJ μ 𝓕 hμ h𝓕 n {X | gramE σ J X = T}`. Establish `hl'` using `PositivityTheory.PlacePermOperatorBicommutantSpan.theta_lint F E σ hcm M J hJ μ' 𝓕' hμ' h𝓕₂ n {X | gramE σ J X = T}`. Establish `hinj : Function.Injective (inclR (F` using `F) (E := E) (AF F)) := Algebra.TensorProduct.includeRight_injective (AdeleRing.algebraMap_injective _ _)`.

Establish `hri : Function.Injective (ratTup (F` using `F) (AF F) : (Fin n → Fin M → E) → _) := fun X Y h =>`. Use function extensionality and compare the values at `fun a => funext fun i => hinj (congrFun (congrFun h a) i)`. Establish `hfin` using `((GlobalTheory.T.unitary_group_finite_volume F E σ hcm M J hJ).2 μ hμ).2 𝓕 h𝓕`. Establish `: μ.IsHaarMeasure` using `hμ`. Establish `: μ'.IsHaarMeasure` using `hμ'`.

Set `Γ : Subgroup (HA (AF F) σ J)` to `HFinIn (AF F) σ J`. Establish `: Countable Γ` using `(GlobalTheory.T.arithmetic_unitary_group_discrete F E σ hcm M J hJ).1`. Establish `h𝓕₁ : IsFundamentalDomain Γ 𝓕 μ` using `h𝓕`. Establish `h0` using `(GlobalTheory.T.finite_covolume_unimodular (HA (AF F) σ J) Γ μ 𝓕 h𝓕₁ hfin).1`. Establish `hsm : μ' = Measure.haarScalarFactor μ' μ • μ` using `Measure.isMulLeftInvariant_eq_smul μ' μ`.

Establish `hc0 : Measure.haarScalarFactor μ' μ ≠ 0` using `(Measure.haarScalarFactor_pos_of_isHaarMeasure μ' μ).ne'`. Use `set c : ℝ≥0 := Measure.haarScalarFactor μ' μ with hc`. Establish `hac : μ ≪ μ'`. Rewrite using `[hsm]`. Conclude with `Measure.absolutelyContinuous_smul (by exact_mod_cast hc0)`.

Establish `h𝓕₃ : IsFundamentalDomain Γ 𝓕' μ'` using `h𝓕₂`. Establish `h𝓕₄ : IsFundamentalDomain Γ 𝓕' μ` using `h𝓕₃.mono hac`. Establish `hmass : μ 𝓕 = μ 𝓕'` using `h𝓕₁.measure_eq h𝓕₄`. Use `Measure.ext_of_lintegral _ fun Φ hΦ => ?_` and prove the remaining obligations. Rewrite using `[hl _ hΦ, hl' _ hΦ]`.

Use `set f : HA (AF F) σ J → ℝ≥0∞ := fun g => ∑' X : {X | gramE σ J X = T}, Φ (actW (AF F) σ J g⁻¹ (ratTup (AF F) (X : Fin n → Fin M → E))) with hf`. Establish `hle : ∀ (γ : Γ) g, f (γ • g) ≤ f g` using `fun γ g => by choose t ht using fun X : {X | gramE σ J X = T} => PositivityTheory.PlacePermOperatorBicommutantSpan.act_rat (n := n) γ⁻¹ X.1`. Establish `ht' : ∀ X, actW (AF F) σ J (γ : HA (AF F) σ J)⁻¹ (ratTup (AF F) X.1) = ratTup (AF F) (t X)` using `ht`. Establish `hT : ∀ X, gramE σ J (t X) = T` using `fun X => Matrix.map_injective hinj (by simp only [← hrat, ← ht', ag]; rw [hrat, X.2])`. Establish `hti : Function.Injective fun X => (⟨t X, hT X⟩ : {X | gramE σ J X = T})` using `fun X Y e => by`.

Establish `h1` using `congrArg (actW (AF F) σ J γ) ((ht' X).trans ((congrArg (fun Z => ratTup (AF F) Z.1) e).trans (ht' Y).symm))`. Simplify using `only [← a2, mul_inv_cancel, a1] at h1`. Conclude with `Subtype.ext (hri h1)`. Use `le_trans (le_of_eq (tsum_congr fun X => ?_)) (ENNReal.tsum_comp_le_tsum_of_injective hti _)` and prove the remaining obligations. Rewrite using `[Subgroup.smul_def, smul_eq_mul, mul_inv_rev, a2, ht']`.

Establish `hinv : ∀ (γ : Γ) g, f (γ • g) = f g` using `fun γ g => (hle γ g).antisymm (by simpa using hle γ⁻¹ (γ • g))`. Establish `hint : ∫⁻ g in 𝓕, f g ∂μ = ∫⁻ g in 𝓕', f g ∂μ` using `h𝓕₁.setLIntegral_eq h𝓕₄ f hinv`. Establish `hcE0 : (c : ℝ≥0∞) ≠ 0` using `by exact_mod_cast hc0`. Establish `hcT : (c : ℝ≥0∞) ≠ ⊤` using `ENNReal.coe_ne_top`. Rewrite using `[hint, hsm, Measure.restrict_smul, lintegral_smul_measure, Measure.smul_apply, ← hmass]`.

Simplify using `only [ENNReal.smul_def, smul_eq_mul]`. Rewrite using `[ENNReal.mul_inv (Or.inl hcE0) (Or.inl hcT)]`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem thetaMeas_gram_indep : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ (μ μ' : Measure (HA (AF F) σ J)) (𝓕 𝓕' : Set (HA (AF F) σ J)), IsHaarH F E σ M J μ → IsFDH F E σ M J μ 𝓕 → IsHaarH F E σ M J μ' → IsFDH F E σ M J μ' 𝓕' → ∀ (n : ℕ) (T : Matrix (Fin n) (Fin n) E), thetaMeas σ J μ 𝓕 {X | gramE σ J X = T} = thetaMeas σ J μ' 𝓕' {X | gramE σ J X = T} := by
  intro F E _ _ _ _ _ σ hcm M J hJ μ μ' 𝓕 𝓕' hμ h𝓕 hμ' h𝓕₂ n T
  obtain ⟨⟨_, _, _⟩, -⟩ := GlobalTheory.T.adeles_locally_compact_second_countable F
  obtain ⟨_, _, _, _, -, -, -, hB, -, hg⟩ := GlobalTheory.T.tensor_locally_compact_ring F E σ hcm (AF F)
  have := hB n M
  obtain ⟨_, _, _, _, _, hact⟩ := GlobalTheory.T.adelic_unitary_group_locally_compact F E σ hcm M J hJ (AF F)
  obtain ⟨ac, a1, a2, ag⟩ := hact n
  have hrat := (GlobalTheory.T.gram_matrix_local_global F E σ hcm M J hJ n 0 T).2
  have hl := PositivityTheory.PlacePermOperatorBicommutantSpan.theta_lint F E σ hcm M J hJ μ 𝓕 hμ h𝓕 n {X | gramE σ J X = T}
  have hl' := PositivityTheory.PlacePermOperatorBicommutantSpan.theta_lint F E σ hcm M J hJ μ' 𝓕' hμ' h𝓕₂ n {X | gramE σ J X = T}
  have hinj : Function.Injective (inclR (F := F) (E := E) (AF F)) :=
    Algebra.TensorProduct.includeRight_injective (AdeleRing.algebraMap_injective _ _)
  have hri : Function.Injective (ratTup (F := F) (AF F) : (Fin n → Fin M → E) → _) := fun X Y h =>
    funext fun a => funext fun i => hinj (congrFun (congrFun h a) i)
  have hfin := ((GlobalTheory.T.unitary_group_finite_volume F E σ hcm M J hJ).2 μ hμ).2 𝓕 h𝓕
  have : μ.IsHaarMeasure := hμ
  have : μ'.IsHaarMeasure := hμ'
  let Γ : Subgroup (HA (AF F) σ J) := HFinIn (AF F) σ J
  have : Countable Γ := (GlobalTheory.T.arithmetic_unitary_group_discrete F E σ hcm M J hJ).1
  have h𝓕₁ : IsFundamentalDomain Γ 𝓕 μ := h𝓕
  have h0 := (GlobalTheory.T.finite_covolume_unimodular (HA (AF F) σ J) Γ μ 𝓕 h𝓕₁ hfin).1
  have hsm : μ' = Measure.haarScalarFactor μ' μ • μ := Measure.isMulLeftInvariant_eq_smul μ' μ
  have hc0 : Measure.haarScalarFactor μ' μ ≠ 0 := (Measure.haarScalarFactor_pos_of_isHaarMeasure μ' μ).ne'
  set c : ℝ≥0 := Measure.haarScalarFactor μ' μ with hc
  have hac : μ ≪ μ' := by
    rw [hsm]
    exact Measure.absolutelyContinuous_smul (by exact_mod_cast hc0)
  have h𝓕₃ : IsFundamentalDomain Γ 𝓕' μ' := h𝓕₂
  have h𝓕₄ : IsFundamentalDomain Γ 𝓕' μ := h𝓕₃.mono hac
  have hmass : μ 𝓕 = μ 𝓕' := h𝓕₁.measure_eq h𝓕₄
  refine Measure.ext_of_lintegral _ fun Φ hΦ => ?_
  rw [hl _ hΦ, hl' _ hΦ]
  set f : HA (AF F) σ J → ℝ≥0∞ := fun g => ∑' X : {X | gramE σ J X = T},
    Φ (actW (AF F) σ J g⁻¹ (ratTup (AF F) (X : Fin n → Fin M → E))) with hf
  have hle : ∀ (γ : Γ) g, f (γ • g) ≤ f g := fun γ g => by
    choose t ht using fun X : {X | gramE σ J X = T} => PositivityTheory.PlacePermOperatorBicommutantSpan.act_rat (n := n) γ⁻¹ X.1
    have ht' : ∀ X, actW (AF F) σ J (γ : HA (AF F) σ J)⁻¹ (ratTup (AF F) X.1) = ratTup (AF F) (t X) := ht
    have hT : ∀ X, gramE σ J (t X) = T := fun X =>
      Matrix.map_injective hinj (by simp only [← hrat, ← ht', ag]; rw [hrat, X.2])
    have hti : Function.Injective fun X => (⟨t X, hT X⟩ : {X | gramE σ J X = T}) := fun X Y e => by
      have h1 := congrArg (actW (AF F) σ J γ) ((ht' X).trans ((congrArg (fun Z => ratTup (AF F) Z.1) e).trans (ht' Y).symm))
      simp only [← a2, mul_inv_cancel, a1] at h1
      exact Subtype.ext (hri h1)
    refine le_trans (le_of_eq (tsum_congr fun X => ?_)) (ENNReal.tsum_comp_le_tsum_of_injective hti _)
    rw [Subgroup.smul_def, smul_eq_mul, mul_inv_rev, a2, ht']
  have hinv : ∀ (γ : Γ) g, f (γ • g) = f g := fun γ g =>
    (hle γ g).antisymm (by simpa using hle γ⁻¹ (γ • g))
  have hint : ∫⁻ g in 𝓕, f g ∂μ = ∫⁻ g in 𝓕', f g ∂μ := h𝓕₁.setLIntegral_eq h𝓕₄ f hinv
  have hcE0 : (c : ℝ≥0∞) ≠ 0 := by exact_mod_cast hc0
  have hcT : (c : ℝ≥0∞) ≠ ⊤ := ENNReal.coe_ne_top
  rw [hint, hsm, Measure.restrict_smul, lintegral_smul_measure, Measure.smul_apply, ← hmass]
  simp only [ENNReal.smul_def, smul_eq_mul]
  rw [ENNReal.mul_inv (Or.inl hcE0) (Or.inl hcT)]
  calc _ = ((c : ℝ≥0∞)⁻¹ * c) * ((μ 𝓕)⁻¹ * ∫⁻ g in 𝓕', f g ∂μ) := by rw [ENNReal.inv_mul_cancel hcE0 hcT, one_mul]
    _ = _ := by ring

end GlobalTheory.CompanionTheory.SW.ThetaIndep

end

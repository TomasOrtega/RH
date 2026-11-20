import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.IsLatMeasurableConst
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.CovolEqOfAedisjoint
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MapInfiniteGLHaarMeasureMulLeftStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.DetNormSqEqOneOfMemLatticeAutStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MeasureInterTranslateEqZeroOfCovolumeStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsCoordinatesInverseFirstColumnInfiniteGLStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.InfiniteLatticeCovolumeSplitLatticeProdStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsLatticeCovolumeInverseIdealStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsFundamentalDomainEmbeddedRowsLatticeStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LintegralIoiCompConstDivChangeOfVarStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MemLatticeAutSplitIffFirstColSingleStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsScalarStableLatticeAutomorphismFundamentalStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.TranslatedLatticeAtInfinityFullCovolumeDualStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LeftQuotientCovolumeWithDensityDetNormSqStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LatticeNonzeroVectorPairNormalFormsStatement
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.FlagBase

noncomputable section

namespace GlobalTheory.OrbitTerm

variable {E : Type} [Field E] [NumberField E]

/- English proof (translation)
Introduce `h`. Use `hγ (matInf_ext fun w => ?_)` and prove the remaining obligations. Establish `h1 : Matrix.of (γ w) * Matrix.of (x w) = Matrix.of (x w)` using `by rw [← of_mul, h]`. Establish `hu : IsUnit (Matrix.of (x w)).det` using `IsUnit.mk0 _ ((detNorm_pos_iff x).1 hx w)`. Rewrite using `[of_oneInf, ← Matrix.mul_nonsing_inv_cancel_right _ (Matrix.of (γ w)) hu, h1, Matrix.mul_nonsing_inv _ hu]`.
-/
theorem mul_ne_self {j : ℕ} {γ x : MatInf E j} (hγ : γ ≠ oneInf E j) (hx : 0 < detNorm E j x) : γ * x ≠ x := by
  intro h
  refine hγ (matInf_ext fun w => ?_)
  have h1 : Matrix.of (γ w) * Matrix.of (x w) = Matrix.of (x w) := by rw [← of_mul, h]
  have hu : IsUnit (Matrix.of (x w)).det := IsUnit.mk0 _ ((detNorm_pos_iff x).1 hx w)
  rw [of_oneInf, ← Matrix.mul_nonsing_inv_cancel_right _ (Matrix.of (γ w)) hu, h1, Matrix.mul_nonsing_inv _ hu]

/- English proof (translation)
Take `⟨D, hDm, hDU, hcov, -, hint⟩` from `GlobalTheory.T.exists_scalarStable_latticeAutomorphismFundamentalDomain E hE k Λ hΛ`. Rewrite `hint` using `[haarGL_restrict hk]`. Establish `hUinv : ∀ γ ∈ autGL E k Λ, ∀ x ∈ {g | 0 < detNorm E k g}, γ * x ∈ {g | 0 < detNorm E k g}` using `fun γ hγ x hx => by show 0 < detNorm E k (γ * x)`. Rewrite using `[detNorm_mul]`. Conclude with `mul_pos (detNorm_pos_of_mem_autGL hγ) hx`.

Use `⟨D, hDm, hcov, fun γ hγ hne => ?_, fun F hF => ?_⟩` and prove the remaining obligations. Use `haveI : BorelSpace (Fin k → ℂ) := inferInstance haveI : BorelSpace (Fin k → Fin k → ℂ) := inferInstance haveI : BorelSpace (InfinitePlace E → Fin k → Fin k → ℂ) := inferInstance haveI : MeasurableSpace.CountablyGenerated (InfinitePlace E → Fin k → Fin k → ℂ) := inferInstance have …`. Use `GlobalTheory.T.measure_inter_translate_eq_zero_of_covolume (MatInf E k) (autGL E k Λ) (haarGL E k) {g | 0 < detNorm E k g} D (countable_autGL Λ) (fun γ _ => measurable_mul_left γ) (fun γ hγ => GlobalTheory.T.map_infiniteGLHaarMeasure_mul_left E k γ (detNorm_pos_of_mem_autGL hγ)) …` and prove the remaining obligations. Take `⟨δ, hδ, h1, h2⟩` from `exists_inv_mem_autGL hγ`. Conclude with `⟨δ, hδ, fun x => by rw [← matInf_mul_assoc, h1, oneInf_mul], fun x => by rw [← matInf_mul_assoc, h2, oneInf_mul]⟩`.

Use `hint (fun _ => 1) A (measurable_const.indicator measurableSet_detNorm_pos) (fun _ _ _ _ => rfl) hA hAU hAi` as an intermediate fact. Rewrite `this` using `[setLIntegral_one, show (fun _ : MatInf E k => (1 : ENNReal)) = 1 from rfl, withDensity_one]`. Then use the resulting hypothesis. Establish `h1` using `hint (fun h => F (detNorm E k h)) {g | 0 < detNorm E k g} ((hF.comp measurable_detNorm).indicator measurableSet_detNorm_pos) (fun γ hγ g _ => by rw [detNorm_mul, GlobalTheory.T.detNorm_eq_one_of_mem_autGL_var E hE k Λ hΛ γ hγ, one_mul]) measurableSet_detNorm_pos subset_rfl hUinv`. Rewrite `h1` using `[Set.inter_eq_right.2 hDU, GlobalTheory.T.leftQuotientCovolume_withDensity_detNormSq E hE k hk Λ hΛ F hF]`. Conclude with `h1.symm`.
-/
theorem exists_domain (hE : IsTotallyComplex E) {k : ℕ} (hk : 1 ≤ k) (Λ : Submodule (𝓞 E) (Fin k → E))
    (hΛ : Submodule.IsLattice E Λ) : ∃ D : Set (MatInf E k), MeasurableSet D ∧
      (∀ g, 0 < detNorm E k g → ∃ γ ∈ autGL E k Λ, γ * g ∈ D) ∧
      (∀ γ ∈ autGL E k Λ, γ ≠ oneInf E k → haarGL E k {x | x ∈ D ∧ γ * x ∈ D} = 0) ∧
      ∀ F : ℝ → ENNReal, Measurable F → ∫⁻ h in D, F (detNorm E k h) ∂(haarGL E k) =
        slabVol E k Λ * ∫⁻ t in Set.Ioi (0 : ℝ), F t / ENNReal.ofReal t := by
  obtain ⟨D, hDm, hDU, hcov, -, hint⟩ := GlobalTheory.T.exists_scalarStable_latticeAutomorphismFundamentalDomain E hE k Λ hΛ
  rw [haarGL_restrict hk] at hint
  have hUinv : ∀ γ ∈ autGL E k Λ, ∀ x ∈ {g | 0 < detNorm E k g}, γ * x ∈ {g | 0 < detNorm E k g} :=
    fun γ hγ x hx => by
      show 0 < detNorm E k (γ * x)
      rw [detNorm_mul]; exact mul_pos (detNorm_pos_of_mem_autGL hγ) hx
  refine ⟨D, hDm, hcov, fun γ hγ hne => ?_, fun F hF => ?_⟩
  · haveI : BorelSpace (Fin k → ℂ) := inferInstance
    haveI : BorelSpace (Fin k → Fin k → ℂ) := inferInstance
    haveI : BorelSpace (InfinitePlace E → Fin k → Fin k → ℂ) := inferInstance
    haveI : MeasurableSpace.CountablyGenerated (InfinitePlace E → Fin k → Fin k → ℂ) := inferInstance
    haveI : MeasurableSpace.SeparatesPoints (InfinitePlace E → Fin k → Fin k → ℂ) := inferInstance
    haveI : MeasurableSpace.CountablySeparated (MatInf E k) :=
      inferInstanceAs (MeasurableSpace.CountablySeparated (InfinitePlace E → Fin k → Fin k → ℂ))
    refine GlobalTheory.T.measure_inter_translate_eq_zero_of_covolume (MatInf E k) (autGL E k Λ) (haarGL E k) {g | 0 < detNorm E k g} D (countable_autGL Λ)
      (fun γ _ => measurable_mul_left γ) (fun γ hγ => GlobalTheory.T.map_infiniteGLHaarMeasure_mul_left E k γ (detNorm_pos_of_mem_autGL hγ))
      (fun γ hγ δ hδ => ⟨γ * δ, mul_mem_autGL hγ hδ, fun x => matInf_mul_assoc _ _ _⟩) (fun γ hγ => ?_)
      measurableSet_detNorm_pos hUinv hDm hDU (fun A hA hAU hAi => ?_) γ hγ fun x hx => mul_ne_self hne hx
    · obtain ⟨δ, hδ, h1, h2⟩ := exists_inv_mem_autGL hγ
      exact ⟨δ, hδ, fun x => by rw [← matInf_mul_assoc, h1, oneInf_mul],
        fun x => by rw [← matInf_mul_assoc, h2, oneInf_mul]⟩
    · have := hint (fun _ => 1) A (measurable_const.indicator measurableSet_detNorm_pos) (fun _ _ _ _ => rfl)
        hA hAU hAi
      rwa [setLIntegral_one, show (fun _ : MatInf E k => (1 : ENNReal)) = 1 from rfl, withDensity_one] at this
  · have h1 := hint (fun h => F (detNorm E k h)) {g | 0 < detNorm E k g}
      ((hF.comp measurable_detNorm).indicator measurableSet_detNorm_pos)
      (fun γ hγ g _ => by rw [detNorm_mul, GlobalTheory.T.detNorm_eq_one_of_mem_autGL_var E hE k Λ hΛ γ hγ, one_mul])
      measurableSet_detNorm_pos subset_rfl hUinv
    rw [Set.inter_eq_right.2 hDU, GlobalTheory.T.leftQuotientCovolume_withDensity_detNormSq E hE k hk Λ hΛ F hF] at h1
    exact h1.symm

def FixesFirst {k : ℕ} (x : MatInf E (k + 1)) : Prop := ∀ w a, x w a 0 = if a = 0 then 1 else 0

/- English proof (translation)
Use `forall_congr' fun w => ?_` and prove the remaining obligations. Rewrite using `[funext_iff]`. Use `forall_congr' fun a => ?_` and prove the remaining obligations. Simplify using `[Pi.single_apply]`.
-/
theorem fixesFirst_iff {k : ℕ} (x : MatInf E (k + 1)) :
    FixesFirst x ↔ ∀ w, Matrix.of (x w) *ᵥ Pi.single 0 1 = Pi.single 0 1 := by
  refine forall_congr' fun w => ?_
  rw [funext_iff]
  refine forall_congr' fun a => ?_
  simp [Pi.single_apply]

/- English proof (translation)
Rewrite `hx`, `hy`, the goal using `[fixesFirst_iff]`. Introduce `w`. Rewrite using `[of_mul, ← Matrix.mulVec_mulVec, hy, hx]`.
-/
theorem FixesFirst.mul {k : ℕ} {x y : MatInf E (k + 1)} (hx : FixesFirst x) (hy : FixesFirst y) :
    FixesFirst (x * y) := by
  rw [fixesFirst_iff] at hx hy ⊢
  intro w
  rw [of_mul, ← Matrix.mulVec_mulVec, hy, hx]

/- English proof (translation)
Rewrite `hx`, the goal using `[fixesFirst_iff]`. Introduce `w`. Use `conv_lhs => rw [← hx w, Matrix.mulVec_mulVec, ← of_mul, h, of_oneInf, Matrix.one_mulVec]`.
-/
theorem FixesFirst.inv {k : ℕ} {x y : MatInf E (k + 1)} (hx : FixesFirst x) (h : y * x = oneInf E (k + 1)) :
    FixesFirst y := by
  rw [fixesFirst_iff] at hx ⊢
  intro w
  conv_lhs => rw [← hx w, Matrix.mulVec_mulVec, ← of_mul, h, of_oneInf, Matrix.one_mulVec]

/- English proof (translation)
Use function extensionality and compare the values at `u a`. Establish `hu : IsUnit (Matrix.of (x u)).det` using `IsUnit.mk0 _ ((detNorm_pos_iff x).1 hx' u)`. Establish `h1 : (Matrix.of (x u))⁻¹ *ᵥ Pi.single 0 1 = Pi.single 0 1` using `by conv_lhs => rw [← (fixesFirst_iff x).1 hx u, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hu, Matrix.one_mulVec]`. Establish `h2 : (Matrix.of ((x * g) u))⁻¹ *ᵥ Pi.single 0 1 = (Matrix.of (g u))⁻¹ *ᵥ Pi.single 0 1`. Rewrite using `[of_mul, Matrix.mul_inv_rev, ← Matrix.mulVec_mulVec, h1]`.

Simplify using `using congrFun h2 a`.
-/
theorem FixesFirst.inv_col {k : ℕ} {x : MatInf E (k + 1)} (hx : FixesFirst x) (hx' : 0 < detNorm E (k + 1) x)
    (g : MatInf E (k + 1)) :
    (fun u a => (Matrix.of ((x * g) u))⁻¹ a 0) = fun u a => (Matrix.of (g u))⁻¹ a 0 := by
  funext u a
  have hu : IsUnit (Matrix.of (x u)).det := IsUnit.mk0 _ ((detNorm_pos_iff x).1 hx' u)
  have h1 : (Matrix.of (x u))⁻¹ *ᵥ Pi.single 0 1 = Pi.single 0 1 := by
    conv_lhs => rw [← (fixesFirst_iff x).1 hx u, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hu,
      Matrix.one_mulVec]
  have h2 : (Matrix.of ((x * g) u))⁻¹ *ᵥ Pi.single 0 1 = (Matrix.of (g u))⁻¹ *ᵥ Pi.single 0 1 := by
    rw [of_mul, Matrix.mul_inv_rev, ← Matrix.mulVec_mulVec, h1]
  simpa using congrFun h2 a

def blk {k : ℕ} (τ : VecInf E k) (β : MatInf E k) : MatInf E (k + 1) :=
  fun w => Fin.cons (Fin.cons 1 (τ w)) fun a => Fin.cons 0 (β w a)

/- English proof (translation)
Introduce `w a`. Apply the tactic sequence `refine Fin.cases ?_ (fun a => ?_) a <;> simp [blk]`.
-/
theorem fixesFirst_blk {k : ℕ} (τ : VecInf E k) (β : MatInf E k) : FixesFirst (blk τ β) := by
  intro w a
  refine Fin.cases ?_ (fun a => ?_) a <;> simp [blk]

/- English proof (translation)
The claim follows from `measurable_pi_lambda _ fun u => measurable_pi_lambda _ fun a => measurable_inv_entry u a 0`.
-/
theorem measurable_inv_col {k : ℕ} :
    Measurable fun (g : MatInf E (k + 1)) => (fun u a => (Matrix.of (g u))⁻¹ a 0 : VecInf E (k + 1)) :=
  measurable_pi_lambda _ fun u => measurable_pi_lambda _ fun a => measurable_inv_entry u a 0

/- English proof (translation)
Use extensionality with `s hs`. Rewrite using `[Measure.map_apply hf hs, withDensity_apply _ (hf hs), withDensity_apply _ hs]`. Use `conv_rhs => rw [← hμ, setLIntegral_map hs hG hf]`. Simplify using `only [hGf]`.
-/
theorem map_withDensity_of_invariant {X : Type} [MeasurableSpace X] (μ : Measure X) {f : X → X}
    (hf : Measurable f) (hμ : μ.map f = μ) {G : X → ENNReal} (hG : Measurable G) (hGf : ∀ x, G (f x) = G x) :
    (μ.withDensity G).map f = μ.withDensity G := by
  ext s hs
  rw [Measure.map_apply hf hs, withDensity_apply _ (hf hs), withDensity_apply _ hs]
  conv_rhs => rw [← hμ, setLIntegral_map hs hG hf]
  simp only [hGf]

/- English proof (translation)
Take `⟨D', hD'm, hD'c, hD'd, hD'i⟩` from `exists_domain hE hk Λ' hΛ'`. Take `⟨P, hPm, hPv, hPc, hPd⟩` from `GlobalTheory.T.exists_fundamentalDomain_embeddedRowsLattice E hE k Λ₀ Λ' hΛ₀ hΛ'`. Take `⟨hh, TT, hhm, hTm, hdet, hequi, hint⟩` from `GlobalTheory.T.exists_coordinates_inverseFirstColumn_infiniteGL E k hk`. Establish `hstab` using `GlobalTheory.T.mem_latticeAut_split_iff_firstCol_single E k Λ Λ₀ Λ' hmem`. Use `set G : MatInf E (k + 1) → ENNReal := fun g => f (detNorm E (k + 1) g) * Φ fun u a => (Matrix.of (g u))⁻¹ a 0 with hG`.

Establish `hGm : Measurable G` using `(hf.comp measurable_detNorm).mul (hΦ.comp measurable_inv_col)`. Use `set μ := (haarGL E (k + 1)).withDensity G with hμ`. Use `set S : Set (MatInf E (k + 1)) := {x | x ∈ autGL E (k + 1) Λ ∧ FixesFirst x} with hS`. Establish `hbox : ∀ (B : Set (MatInf E k)) (Q : Set (VecInf E k)), MeasurableSet B → MeasurableSet Q → μ {g | 0 < detNorm E (k + 1) g ∧ hh g ∈ B ∧ TT g ∈ Q} = (∫⁻ x, Φ x) * volume Q * ∫⁻ h in B, f (detNorm E k h) * ENNReal.ofReal (detNorm E k h) ∂(haarGL E k)`. Introduce `B Q hB hQ`.

Establish `hm : MeasurableSet {g | 0 < detNorm E (k + 1) g ∧ hh g ∈ B ∧ TT g ∈ Q}` using `measurableSet_detNorm_pos.inter ((hhm hB).inter (hTm hQ))`. Establish `h1` using `hint (B.indicator fun h => f (detNorm E k h)) (Q.indicator 1) Φ ((hf.comp measurable_detNorm).indicator hB) (measurable_const.indicator hQ) hΦ`. Rewrite `h1` using `[lintegral_indicator_one hQ]`. Rewrite using `[hμ, withDensity_apply _ hm, ← lintegral_indicator hm, ← lintegral_indicator hB]`. Establish `h2 : ∀ h, B.indicator (fun h => f (detNorm E k h) * ENNReal.ofReal (detNorm E k h)) h = B.indicator (fun h => f (detNorm E k h)) h * ENNReal.ofReal (detNorm E k h)` using `fun h => by`.

Apply the tactic sequence `by_cases hhB : h ∈ B <;> simp [hhB]`. Simplify using `only [h2]`. Rewrite using `[← h1]`. Use `lintegral_congr_ae ?_` and prove the remaining obligations. Establish `hae : ∀ᵐ g ∂(haarGL E (k + 1)), g ∈ {g | 0 < detNorm E (k + 1) g}` using `haarGL_singular (by omega)`.

Use `filter_upwards [hae] with g hg`. Establish `hg' : 0 < detNorm E (k + 1) g` using `hg`. Apply the tactic sequence `by_cases h3 : hh g ∈ B <;> by_cases h4 : TT g ∈ Q <;> simp [Set.indicator, h3, h4, hg', hG, hdet g hg']`. Establish `hSmul : ∀ γ ∈ S, ∀ δ ∈ S, γ * δ ∈ S` using `fun γ hγ δ hδ => ⟨mul_mem_autGL hγ.1 hδ.1, hγ.2.mul hδ.2⟩`. Establish `hSinv : ∀ γ ∈ S, ∃ δ ∈ S, δ * γ = oneInf E (k + 1) ∧ γ * δ = oneInf E (k + 1)` using `fun γ hγ => by`.

Take `⟨δ, hδ, h1, h2⟩` from `exists_inv_mem_autGL hγ.1`. Conclude with `⟨δ, ⟨hδ, hγ.2.inv h1⟩, h1, h2⟩`. Establish `hSpos : ∀ γ ∈ S, 0 < detNorm E (k + 1) γ` using `fun γ hγ => detNorm_pos_of_mem_autGL hγ.1`. Establish `hμinv : ∀ γ ∈ S, μ.map (fun x => γ * x) = μ` using `fun γ hγ => map_withDensity_of_invariant _ (measurable_mul_left γ) (GlobalTheory.T.map_infiniteGLHaarMeasure_mul_left E _ γ (hSpos γ hγ)) hGm fun x => by`. Simplify using `only [hG]`.

Rewrite using `[detNorm_mul, GlobalTheory.T.detNorm_eq_one_of_mem_autGL_var E hE _ Λ hΛ γ hγ.1, one_mul, hγ.2.inv_col (hSpos γ hγ)]`. Use `set D : Set (MatInf E (k + 1)) := {g | 0 < detNorm E (k + 1) g ∧ hh g ∈ D' ∧ TT g ∈ P} with hD`. Establish `hDm : MeasurableSet D` using `measurableSet_detNorm_pos.inter ((hhm hD'm).inter (hTm hPm))`. Establish `hdis : ∀ γ ∈ S, γ ≠ oneInf E (k + 1) → μ {x | x ∈ D ∧ γ * x ∈ D} = 0`. Introduce `γ hγ hne`.

Take `⟨hβ, τ, hτ, hτγ⟩` from `(hstab γ hγ.2).1 hγ.1`. Use `set β : MatInf E k := fun w a b => γ w a.succ b.succ with hβdef`. Distinguish the cases in `hb : β = oneInf E k`. Establish `: {x | x ∈ D ∧ γ * x ∈ D} = ∅`. Use `Set.eq_empty_of_forall_notMem fun x hx => hne ?_` and prove the remaining obligations.

Take `⟨-, h2⟩` from `hequi x γ hx.1.1 (hSpos γ hγ) hγ.2 β fun _ _ _ => rfl`. Establish `h3 : TT (γ * x) = fun w b => TT x w b + w.embedding (τ b)`. Use function extensionality and compare the values at `w b`. Use `congrFun (h2 w) b` as an intermediate fact. Rewrite `this` using `[hb, of_oneInf, Matrix.vecMul_one]`.

Rewrite using `[this, ← hτγ]`. Both sides reduce to the same expression. Establish `h4 : τ = 0` using `hPd (TT x) τ hτ hx.1.2.2 (h3 ▸ hx.2.2.2)`. Use function extensionality and compare the values at `w a b`. Use `Fin.cases ?_ (fun b => ?_) b` and prove the remaining obligations.

Conclude with `hγ.2 w a`. Use `Fin.cases ?_ (fun a => ?_) a` and prove the remaining obligations. Rewrite using `[hτγ, h4]`. Simplify using `[oneInf, (Fin.succ_ne_zero b).symm]`. Use `congrFun (congrFun (congrFun hb w) a) b` as an intermediate fact.

Simplify `this` using `[oneInf]`. Rewrite using `[this, measure_empty]`. Establish `hBm : MeasurableSet {x | x ∈ D' ∧ β * x ∈ D'}` using `hD'm.inter (measurable_mul_left β hD'm)`. Establish `h0` using `hbox _ Set.univ hBm MeasurableSet.univ`. Rewrite `h0` using `[setLIntegral_measure_zero _ _ (hD'd β hβ hb), mul_zero]`.

Use `measure_mono_null (fun x hx => ?_) h0` and prove the remaining obligations. Take `⟨h1, -⟩` from `hequi x γ hx.1.1 (hSpos γ hγ) hγ.2 β fun _ _ _ => rfl`. Conclude with `⟨hx.1.1, ⟨hx.1.2.1, h1 ▸ hx.2.2.1⟩, trivial⟩`. Rewrite using `[covol_eq_of_aedisjoint S μ {g | 0 < detNorm E (k + 1) g} D ((countable_autGL Λ).mono fun x hx => hx.1) (fun γ _ => measurable_mul_left γ) hμinv ?_ hDm (fun x hx => hx.1) ?_ ?_]`. Rewrite using `[hbox D' P hD'm hPm, hPv, hD'i (fun t => f t * ENNReal.ofReal t) (hf.mul ENNReal.measurable_ofReal)]`.

Introduce `γ hγ`. Take `⟨δ, hδ, h1, h2⟩` from `hSinv γ hγ`. Conclude with `⟨δ, hδ, fun x => by rw [← matInf_mul_assoc, h1, oneInf_mul], fun x => by rw [← matInf_mul_assoc, h2, oneInf_mul]⟩`. Introduce `g hg`. Establish `hg' : 0 < detNorm E (k + 1) g` using `hg`.

Take `⟨β, hβ, hβD⟩` from `hD'c (hh g) (by rw [hdet g hg']; exact hg')`. Establish `hγ₁ : blk 0 β ∈ S` using `⟨(hstab _ (fixesFirst_blk 0 β)).2 ⟨hβ, 0, fun y _ => by`. Rewrite using `[zero_dotProduct]; exact Λ₀.zero_mem, fun w b => by simp [blk]⟩, fixesFirst_blk 0 β⟩`. Establish `hg₁ : 0 < detNorm E (k + 1) (blk 0 β * g)`. Rewrite using `[detNorm_mul]`.

Conclude with `mul_pos (hSpos _ hγ₁) hg'`. Take `⟨h1, -⟩` from `hequi g (blk 0 β) hg' (hSpos _ hγ₁) hγ₁.2 β fun _ _ _ => rfl`. Take `⟨τ, hτ, hτP⟩` from `hPc (TT (blk 0 β * g))`. Establish `hγ₂ : blk (fun w b => w.embedding (τ b)) (oneInf E k) ∈ S` using `⟨(hstab _ (fixesFirst_blk _ _)).2 ⟨oneInf_mem_autGL Λ', τ, hτ, fun w b => rfl⟩, fixesFirst_blk _ _⟩`. Take `⟨h2, h3⟩` from `hequi (blk 0 β * g) _ hg₁ (hSpos _ hγ₂) hγ₂.2 (oneInf E k) fun _ _ _ => rfl`.

Use `⟨_, hSmul _ hγ₂ _ hγ₁, ?_⟩` and prove the remaining obligations. Rewrite using `[matInf_mul_assoc]`. Use `⟨by rw [detNorm_mul]; exact mul_pos (hSpos _ hγ₂) hg₁, by rw [h2, oneInf_mul, h1]; exact hβD, ?_⟩` and prove the remaining obligations. Use `hτP using 1` and compare the differences between its conclusion and the goal. Use function extensionality and compare the values at `w b`.

Use `congrFun (h3 w) b` as an intermediate fact. Rewrite `this` using `[of_oneInf, Matrix.vecMul_one]`. Conclude with `this`. Introduce `γ hγ δ hδ hne`. Take `⟨ε, hε, h1, h2⟩` from `hSinv γ hγ`.

Establish `hne' : δ * ε ≠ oneInf E (k + 1)` using `fun h => hne (by`. Rewrite using `[← oneInf_mul γ, ← h, matInf_mul_assoc, h1, mul_oneInf])`. Establish `h0` using `hdis _ (hSmul δ hδ ε hε) hne'`. Establish `hm : MeasurableSet {x | x ∈ D ∧ δ * ε * x ∈ D}` using `hDm.inter (measurable_mul_left (δ * ε) hDm)`. Rewrite `h0` using `[← hμinv γ hγ, Measure.map_apply (measurable_mul_left γ) hm]`.

Use `measure_mono_null (fun x hx => ?_) h0` and prove the remaining obligations. Use `⟨hx.1, ?_⟩` and prove the remaining obligations. Use `show δ * ε * (γ * x) ∈ D`. Rewrite using `[matInf_mul_assoc, ← matInf_mul_assoc ε, h1, oneInf_mul]`. Conclude with `hx.2`.
-/
theorem covol_stabilizer (hE : IsTotallyComplex E) {k : ℕ} (hk : 1 ≤ k) (Λ : Submodule (𝓞 E) (Fin (k + 1) → E))
    (Λ₀ : Submodule (𝓞 E) (Fin 1 → E)) (Λ' : Submodule (𝓞 E) (Fin k → E)) (hΛ : Submodule.IsLattice E Λ)
    (hΛ₀ : Submodule.IsLattice E Λ₀) (hΛ' : Submodule.IsLattice E Λ')
    (hmem : ∀ y, y ∈ Λ ↔ (fun _ => y 0) ∈ Λ₀ ∧ Fin.tail y ∈ Λ') (f : ℝ → ENNReal) (hf : Measurable f)
    (Φ : VecInf E (k + 1) → ENNReal) (hΦ : Measurable Φ) :
    covol {x | x ∈ autGL E (k + 1) Λ ∧ FixesFirst x}
      ((haarGL E (k + 1)).withDensity fun g => f (detNorm E (k + 1) g) * Φ fun u a => (Matrix.of (g u))⁻¹ a 0)
      {g | 0 < detNorm E (k + 1) g} =
    (∫⁻ x, Φ x) * ENNReal.ofReal (covAt E 1 (latAt E 1 Λ₀ (oneInf E 1)) ^ k *
      (Formalism.HermitianLatticesTheory.vInv E ^ (Formalism.HermitianLatticesTheory.fDeg E * k) / covAt E k (latAt E k Λ' (oneInf E k)))) *
      (slabVol E k Λ' * ∫⁻ t in Set.Ioi (0 : ℝ), f t * ENNReal.ofReal t / ENNReal.ofReal t) := by
  obtain ⟨D', hD'm, hD'c, hD'd, hD'i⟩ := exists_domain hE hk Λ' hΛ'
  obtain ⟨P, hPm, hPv, hPc, hPd⟩ := GlobalTheory.T.exists_fundamentalDomain_embeddedRowsLattice E hE k Λ₀ Λ' hΛ₀ hΛ'
  obtain ⟨hh, TT, hhm, hTm, hdet, hequi, hint⟩ := GlobalTheory.T.exists_coordinates_inverseFirstColumn_infiniteGL E k hk
  have hstab := GlobalTheory.T.mem_latticeAut_split_iff_firstCol_single E k Λ Λ₀ Λ' hmem
  set G : MatInf E (k + 1) → ENNReal :=
    fun g => f (detNorm E (k + 1) g) * Φ fun u a => (Matrix.of (g u))⁻¹ a 0 with hG
  have hGm : Measurable G := (hf.comp measurable_detNorm).mul (hΦ.comp measurable_inv_col)
  set μ := (haarGL E (k + 1)).withDensity G with hμ
  set S : Set (MatInf E (k + 1)) := {x | x ∈ autGL E (k + 1) Λ ∧ FixesFirst x} with hS
  have hbox : ∀ (B : Set (MatInf E k)) (Q : Set (VecInf E k)), MeasurableSet B → MeasurableSet Q →
      μ {g | 0 < detNorm E (k + 1) g ∧ hh g ∈ B ∧ TT g ∈ Q} = (∫⁻ x, Φ x) * volume Q *
        ∫⁻ h in B, f (detNorm E k h) * ENNReal.ofReal (detNorm E k h) ∂(haarGL E k) := by
    intro B Q hB hQ
    have hm : MeasurableSet {g | 0 < detNorm E (k + 1) g ∧ hh g ∈ B ∧ TT g ∈ Q} :=
      measurableSet_detNorm_pos.inter ((hhm hB).inter (hTm hQ))
    have h1 := hint (B.indicator fun h => f (detNorm E k h)) (Q.indicator 1) Φ
      ((hf.comp measurable_detNorm).indicator hB) (measurable_const.indicator hQ) hΦ
    rw [lintegral_indicator_one hQ] at h1
    rw [hμ, withDensity_apply _ hm, ← lintegral_indicator hm, ← lintegral_indicator hB]
    have h2 : ∀ h, B.indicator (fun h => f (detNorm E k h) * ENNReal.ofReal (detNorm E k h)) h =
        B.indicator (fun h => f (detNorm E k h)) h * ENNReal.ofReal (detNorm E k h) := fun h => by
      by_cases hhB : h ∈ B <;> simp [hhB]
    simp only [h2]
    rw [← h1]
    refine lintegral_congr_ae ?_
    have hae : ∀ᵐ g ∂(haarGL E (k + 1)), g ∈ {g | 0 < detNorm E (k + 1) g} := haarGL_singular (by omega)
    filter_upwards [hae] with g hg
    have hg' : 0 < detNorm E (k + 1) g := hg
    by_cases h3 : hh g ∈ B <;> by_cases h4 : TT g ∈ Q <;> simp [Set.indicator, h3, h4, hg', hG, hdet g hg']
  have hSmul : ∀ γ ∈ S, ∀ δ ∈ S, γ * δ ∈ S := fun γ hγ δ hδ => ⟨mul_mem_autGL hγ.1 hδ.1, hγ.2.mul hδ.2⟩
  have hSinv : ∀ γ ∈ S, ∃ δ ∈ S, δ * γ = oneInf E (k + 1) ∧ γ * δ = oneInf E (k + 1) := fun γ hγ => by
    obtain ⟨δ, hδ, h1, h2⟩ := exists_inv_mem_autGL hγ.1
    exact ⟨δ, ⟨hδ, hγ.2.inv h1⟩, h1, h2⟩
  have hSpos : ∀ γ ∈ S, 0 < detNorm E (k + 1) γ := fun γ hγ => detNorm_pos_of_mem_autGL hγ.1
  have hμinv : ∀ γ ∈ S, μ.map (fun x => γ * x) = μ := fun γ hγ =>
    map_withDensity_of_invariant _ (measurable_mul_left γ) (GlobalTheory.T.map_infiniteGLHaarMeasure_mul_left E _ γ (hSpos γ hγ)) hGm fun x => by
      simp only [hG]
      rw [detNorm_mul, GlobalTheory.T.detNorm_eq_one_of_mem_autGL_var E hE _ Λ hΛ γ hγ.1, one_mul, hγ.2.inv_col (hSpos γ hγ)]
  set D : Set (MatInf E (k + 1)) := {g | 0 < detNorm E (k + 1) g ∧ hh g ∈ D' ∧ TT g ∈ P} with hD
  have hDm : MeasurableSet D := measurableSet_detNorm_pos.inter ((hhm hD'm).inter (hTm hPm))
  have hdis : ∀ γ ∈ S, γ ≠ oneInf E (k + 1) → μ {x | x ∈ D ∧ γ * x ∈ D} = 0 := by
    intro γ hγ hne
    obtain ⟨hβ, τ, hτ, hτγ⟩ := (hstab γ hγ.2).1 hγ.1
    set β : MatInf E k := fun w a b => γ w a.succ b.succ with hβdef
    by_cases hb : β = oneInf E k
    · have : {x | x ∈ D ∧ γ * x ∈ D} = ∅ := by
        refine Set.eq_empty_of_forall_notMem fun x hx => hne ?_
        obtain ⟨-, h2⟩ := hequi x γ hx.1.1 (hSpos γ hγ) hγ.2 β fun _ _ _ => rfl
        have h3 : TT (γ * x) = fun w b => TT x w b + w.embedding (τ b) := by
          funext w b
          have := congrFun (h2 w) b
          rw [hb, of_oneInf, Matrix.vecMul_one] at this
          rw [this, ← hτγ]; rfl
        have h4 : τ = 0 := hPd (TT x) τ hτ hx.1.2.2 (h3 ▸ hx.2.2.2)
        funext w a b
        refine Fin.cases ?_ (fun b => ?_) b
        · exact hγ.2 w a
        refine Fin.cases ?_ (fun a => ?_) a
        · rw [hτγ, h4]; simp [oneInf, (Fin.succ_ne_zero b).symm]
        · have := congrFun (congrFun (congrFun hb w) a) b
          simpa [oneInf] using this
      rw [this, measure_empty]
    · have hBm : MeasurableSet {x | x ∈ D' ∧ β * x ∈ D'} := hD'm.inter (measurable_mul_left β hD'm)
      have h0 := hbox _ Set.univ hBm MeasurableSet.univ
      rw [setLIntegral_measure_zero _ _ (hD'd β hβ hb), mul_zero] at h0
      refine measure_mono_null (fun x hx => ?_) h0
      obtain ⟨h1, -⟩ := hequi x γ hx.1.1 (hSpos γ hγ) hγ.2 β fun _ _ _ => rfl
      exact ⟨hx.1.1, ⟨hx.1.2.1, h1 ▸ hx.2.2.1⟩, trivial⟩
  rw [covol_eq_of_aedisjoint S μ {g | 0 < detNorm E (k + 1) g} D ((countable_autGL Λ).mono fun x hx => hx.1)
    (fun γ _ => measurable_mul_left γ) hμinv ?_ hDm (fun x hx => hx.1) ?_ ?_]
  · rw [hbox D' P hD'm hPm, hPv,
      hD'i (fun t => f t * ENNReal.ofReal t) (hf.mul ENNReal.measurable_ofReal)]
  · intro γ hγ
    obtain ⟨δ, hδ, h1, h2⟩ := hSinv γ hγ
    exact ⟨δ, hδ, fun x => by rw [← matInf_mul_assoc, h1, oneInf_mul],
      fun x => by rw [← matInf_mul_assoc, h2, oneInf_mul]⟩
  · intro g hg
    have hg' : 0 < detNorm E (k + 1) g := hg
    obtain ⟨β, hβ, hβD⟩ := hD'c (hh g) (by rw [hdet g hg']; exact hg')
    have hγ₁ : blk 0 β ∈ S := ⟨(hstab _ (fixesFirst_blk 0 β)).2 ⟨hβ, 0, fun y _ => by
      rw [zero_dotProduct]; exact Λ₀.zero_mem, fun w b => by simp [blk]⟩, fixesFirst_blk 0 β⟩
    have hg₁ : 0 < detNorm E (k + 1) (blk 0 β * g) := by
      rw [detNorm_mul]; exact mul_pos (hSpos _ hγ₁) hg'
    obtain ⟨h1, -⟩ := hequi g (blk 0 β) hg' (hSpos _ hγ₁) hγ₁.2 β fun _ _ _ => rfl
    obtain ⟨τ, hτ, hτP⟩ := hPc (TT (blk 0 β * g))
    have hγ₂ : blk (fun w b => w.embedding (τ b)) (oneInf E k) ∈ S :=
      ⟨(hstab _ (fixesFirst_blk _ _)).2 ⟨oneInf_mem_autGL Λ', τ, hτ, fun w b => rfl⟩, fixesFirst_blk _ _⟩
    obtain ⟨h2, h3⟩ := hequi (blk 0 β * g) _ hg₁ (hSpos _ hγ₂) hγ₂.2 (oneInf E k) fun _ _ _ => rfl
    refine ⟨_, hSmul _ hγ₂ _ hγ₁, ?_⟩
    rw [matInf_mul_assoc]
    refine ⟨by rw [detNorm_mul]; exact mul_pos (hSpos _ hγ₂) hg₁, by rw [h2, oneInf_mul, h1]; exact hβD, ?_⟩
    convert hτP using 1
    funext w b
    have := congrFun (h3 w) b
    rw [of_oneInf, Matrix.vecMul_one] at this
    exact this
  · intro γ hγ δ hδ hne
    obtain ⟨ε, hε, h1, h2⟩ := hSinv γ hγ
    have hne' : δ * ε ≠ oneInf E (k + 1) := fun h => hne (by
      rw [← oneInf_mul γ, ← h, matInf_mul_assoc, h1, mul_oneInf])
    have h0 := hdis _ (hSmul δ hδ ε hε) hne'
    have hm : MeasurableSet {x | x ∈ D ∧ δ * ε * x ∈ D} := hDm.inter (measurable_mul_left (δ * ε) hDm)
    rw [← hμinv γ hγ, Measure.map_apply (measurable_mul_left γ) hm] at h0
    refine measure_mono_null (fun x hx => ?_) h0
    refine ⟨hx.1, ?_⟩
    show δ * ε * (γ * x) ∈ D
    rw [matInf_mul_assoc, ← matInf_mul_assoc ε, h1, oneInf_mul]
    exact hx.2

/- English proof (translation)
Introduce `E _ _ hE k hk Lf hLf w Φ hw hΦ 𝔞 Λ' h𝔞 hΛ'`. Take `⟨Λ₀, hmem₀, hΛ₀, hc₀⟩` from `GlobalTheory.T.exists_lattice_covolume_inverse_ideal E hE 𝔞 h𝔞`. Establish `hΛ` using `((GlobalTheory.T.lattice_nonzero_vector_pair_normal_forms E k Lf hLf).1 𝔞 Λ' h𝔞 hΛ').1`. Establish `hmem : ∀ y, y ∈ Lf 𝔞 Λ' ↔ (fun _ => y 0) ∈ Λ₀ ∧ Fin.tail y ∈ Λ'` using `fun y => by rw [hLf, hmem₀]`. Take `⟨κ, hκ, hκc⟩` from `(GlobalTheory.T.translatedLatticeAtInfinity_full_covolume_dual E hE (k + 1)).1 _ hΛ`.

Take `⟨κ', hκ', hκ'c⟩` from `(GlobalTheory.T.translatedLatticeAtInfinity_full_covolume_dual E hE k).1 _ hΛ'`. Establish `e' : covAt E k (latAt E k Λ' (oneInf E k)) = κ'`. Rewrite using `[(hκ'c _ (by rw [detNorm_oneInf]; exact one_pos)).2.1, detNorm_oneInf, div_one]`. Establish `e : κ = Formalism.HermitianLatticesTheory.vInv E ^ Formalism.HermitianLatticesTheory.fDeg E / (Ideal.absNorm 𝔞 : ℝ) * κ'`. Rewrite using `[← hc₀, ← e', ← GlobalTheory.T.infiniteLatticeCovolume_split_lattice_prod E hE k _ Λ₀ Λ' hΛ₀ hΛ' hmem, (hκc _ (by rw [detNorm_oneInf]; exact one_pos)).2.1, detNorm_oneInf, div_one]`.

Establish `hmain` using `covol_stabilizer hE hk _ Λ₀ Λ' hΛ hΛ₀ hΛ' hmem (fun t => w (κ / t)) (hw.comp (measurable_const.div measurable_id)) Φ hΦ`. Establish `hdens : ((haarGL E (k + 1)).withDensity fun g => w (covAt E (k + 1) (latAt E (k + 1) (Lf 𝔞 Λ') g)) * Φ (fun u a => (Matrix.of (g u))⁻¹ a 0)) = (haarGL E (k + 1)).withDensity fun g => w (κ / detNorm E (k + 1) g) * Φ fun u a => (Matrix.of (g u))⁻¹ a 0`. Use `withDensity_congr_ae ?_` and prove the remaining obligations. Establish `hae : ∀ᵐ g ∂(haarGL E (k + 1)), g ∈ {g | 0 < detNorm E (k + 1) g}` using `haarGL_singular (by omega)`. Use `filter_upwards [hae] with g hg`.

Rewrite using `[(hκc g hg).2.1]`. Rewrite using `[hdens]`. Use `hmain.trans ?_` and prove the remaining obligations. Rewrite using `[GlobalTheory.T.lintegral_Ioi_comp_const_div_change_of_var κ hκ w hw, hc₀, e']`. Establish `hconst : ENNReal.ofReal (Formalism.HermitianLatticesTheory.vInv E ^ (Formalism.HermitianLatticesTheory.fDeg E * (2 * k + 1)) * ((Ideal.absNorm 𝔞 : ℝ) ^ (k + 1))⁻¹) = ENNReal.ofReal ((Formalism.HermitianLatticesTheory.vInv E ^ Formalism.HermitianLatticesTheory.fDeg E / (Ideal.absN …`.

Rewrite using `[← ENNReal.ofReal_mul' hκ.le, e]`. Use `congr 1`. Establish `hN : (Ideal.absNorm 𝔞 : ℝ) ≠ 0`. Conclude with `fun h => h𝔞 (Ideal.absNorm_eq_zero_iff.1 h)` after adjusting the coercions. Generalize the expression as in `Formalism.HermitianLatticesTheory.vInv E = v`.

Generalize the expression as in `Formalism.HermitianLatticesTheory.fDeg E = n`. Generalize the expression as in `(Ideal.absNorm 𝔞 : ℝ) = N at hN ⊢`. Establish `hκ0` using `hκ'.ne'`. Rewrite using `[div_pow, ← pow_mul]`. Clear the denominators using the available nonvanishing facts.

Expand and normalize the polynomial expressions, which then agree. Rewrite using `[hconst]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem orbit_term : ∀ (E : Type) [Field E] [NumberField E], IsTotallyComplex E → ∀ k : ℕ, 1 ≤ k → ∀ Lf : Ideal (𝓞 E) → Submodule (𝓞 E) (Fin k → E) → Submodule (𝓞 E) (Fin (k + 1) → E), (∀ 𝔞 Λ' y, y ∈ Lf 𝔞 Λ' ↔ (∀ t ∈ 𝔞, (t : E) * y 0 ∈ (algebraMap (𝓞 E) E).range) ∧ Fin.tail y ∈ Λ') → ∀ (w : ℝ → ENNReal) (Φ : VecInf E (k + 1) → ENNReal), Measurable w → Measurable Φ → ∀ (𝔞 : Ideal (𝓞 E)) (Λ' : Submodule (𝓞 E) (Fin k → E)), 𝔞 ≠ ⊥ → Submodule.IsLattice E Λ' → covol {x | x ∈ autGL E (k + 1) (Lf 𝔞 Λ') ∧ ∀ w a, x w a 0 = if a = 0 then 1 else 0} ((haarGL E (k + 1)).withDensity fun g => w (covAt E (k + 1) (latAt E (k + 1) (Lf 𝔞 Λ') g)) * Φ (fun u a => (Matrix.of (g u))⁻¹ a 0)) {g | 0 < detNorm E (k + 1) g} = slabVol E k Λ' * ENNReal.ofReal (Formalism.HermitianLatticesTheory.vInv E ^ (Formalism.HermitianLatticesTheory.fDeg E * (2 * k + 1)) * ((Ideal.absNorm 𝔞 : ℝ) ^ (k + 1))⁻¹) * (∫⁻ x, Φ x) * ∫⁻ t in Set.Ioi (0 : ℝ), w t / ENNReal.ofReal (t ^ 2) := by
  intro E _ _ hE k hk Lf hLf w Φ hw hΦ 𝔞 Λ' h𝔞 hΛ'
  obtain ⟨Λ₀, hmem₀, hΛ₀, hc₀⟩ := GlobalTheory.T.exists_lattice_covolume_inverse_ideal E hE 𝔞 h𝔞
  have hΛ := ((GlobalTheory.T.lattice_nonzero_vector_pair_normal_forms E k Lf hLf).1 𝔞 Λ' h𝔞 hΛ').1
  have hmem : ∀ y, y ∈ Lf 𝔞 Λ' ↔ (fun _ => y 0) ∈ Λ₀ ∧ Fin.tail y ∈ Λ' := fun y => by rw [hLf, hmem₀]
  obtain ⟨κ, hκ, hκc⟩ := (GlobalTheory.T.translatedLatticeAtInfinity_full_covolume_dual E hE (k + 1)).1 _ hΛ
  obtain ⟨κ', hκ', hκ'c⟩ := (GlobalTheory.T.translatedLatticeAtInfinity_full_covolume_dual E hE k).1 _ hΛ'
  have e' : covAt E k (latAt E k Λ' (oneInf E k)) = κ' := by
    rw [(hκ'c _ (by rw [detNorm_oneInf]; exact one_pos)).2.1, detNorm_oneInf, div_one]
  have e : κ = Formalism.HermitianLatticesTheory.vInv E ^ Formalism.HermitianLatticesTheory.fDeg E / (Ideal.absNorm 𝔞 : ℝ) * κ' := by
    rw [← hc₀, ← e', ← GlobalTheory.T.infiniteLatticeCovolume_split_lattice_prod E hE k _ Λ₀ Λ' hΛ₀ hΛ' hmem,
      (hκc _ (by rw [detNorm_oneInf]; exact one_pos)).2.1, detNorm_oneInf, div_one]
  have hmain := covol_stabilizer hE hk _ Λ₀ Λ' hΛ hΛ₀ hΛ' hmem (fun t => w (κ / t))
    (hw.comp (measurable_const.div measurable_id)) Φ hΦ
  have hdens : ((haarGL E (k + 1)).withDensity fun g => w (covAt E (k + 1) (latAt E (k + 1) (Lf 𝔞 Λ') g)) *
      Φ (fun u a => (Matrix.of (g u))⁻¹ a 0)) = (haarGL E (k + 1)).withDensity fun g =>
      w (κ / detNorm E (k + 1) g) * Φ fun u a => (Matrix.of (g u))⁻¹ a 0 := by
    refine withDensity_congr_ae ?_
    have hae : ∀ᵐ g ∂(haarGL E (k + 1)), g ∈ {g | 0 < detNorm E (k + 1) g} := haarGL_singular (by omega)
    filter_upwards [hae] with g hg
    rw [(hκc g hg).2.1]
  rw [hdens]
  refine hmain.trans ?_
  rw [GlobalTheory.T.lintegral_Ioi_comp_const_div_change_of_var κ hκ w hw, hc₀, e']
  have hconst : ENNReal.ofReal (Formalism.HermitianLatticesTheory.vInv E ^ (Formalism.HermitianLatticesTheory.fDeg E * (2 * k + 1)) *
      ((Ideal.absNorm 𝔞 : ℝ) ^ (k + 1))⁻¹) =
      ENNReal.ofReal ((Formalism.HermitianLatticesTheory.vInv E ^ Formalism.HermitianLatticesTheory.fDeg E / (Ideal.absNorm 𝔞 : ℝ)) ^ k *
        (Formalism.HermitianLatticesTheory.vInv E ^ (Formalism.HermitianLatticesTheory.fDeg E * k) / κ')) * ENNReal.ofReal κ := by
    rw [← ENNReal.ofReal_mul' hκ.le, e]
    congr 1
    have hN : (Ideal.absNorm 𝔞 : ℝ) ≠ 0 := by
      exact_mod_cast fun h => h𝔞 (Ideal.absNorm_eq_zero_iff.1 h)
    generalize Formalism.HermitianLatticesTheory.vInv E = v
    generalize Formalism.HermitianLatticesTheory.fDeg E = n
    generalize (Ideal.absNorm 𝔞 : ℝ) = N at hN ⊢
    have hκ0 := hκ'.ne'
    rw [div_pow, ← pow_mul]
    field_simp
    ring
  rw [hconst]
  ring

end GlobalTheory.OrbitTerm

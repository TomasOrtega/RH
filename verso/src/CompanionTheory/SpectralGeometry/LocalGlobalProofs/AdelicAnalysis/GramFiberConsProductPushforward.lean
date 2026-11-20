import Mathlib
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.StageData
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.OneVectorCcOfSiegelWeil
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.CoordinateHomeomorphTensorProductMeasureStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.HermitianMatricesLocallyCompactBorelStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.TensorLocallyCompactRingStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.CoordinateHaarMeasureStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.GramFiberConsProductIntegralStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.GramFiberConsProductDisintegrationStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.GramFiberMeasureGeneralRankExtensionStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.GramFiberConsProductFubiniStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.GramFiberMeasureConsProductStatement

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.PiLocalization₂ NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

noncomputable section

namespace GlobalTheory.CompanionTheory.SW.PiLocalization₂.Fold

section Alg

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (R : Type) [CommRing R] [Algebra F R] (σ : E →ₐ[F] E) {n : ℕ}

def qM (t : F) (c : Fin n → R ⊗[F] E) : Matrix (Fin n) (Fin n) (R ⊗[F] E) :=
  fun i j => sigR R σ (c i) * inclR R (algebraMap F E t) * c j

/- English proof (translation)
Simplify using `[sigR, inclR]`.
-/
theorem sigR_inclT (t : F) : sigR R σ (inclR R (algebraMap F E t)) = inclR R (algebraMap F E t) := by
  simp [sigR, inclR]

/- English proof (translation)
Introduce `i j`. Establish `h : sigR R σ (sigR R σ (c j)) = c j` using `GlobalTheory.GaussMean.OneVec.sigR_sigR R hσ _`. Use `show sigR R σ (qM R σ t c j i) = qM R σ t c i j`. Simplify using `only [qM, map_mul, sigR_inclT, h]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem qM_mem (hσ : IsCMExt F E σ) (t : F) (c : Fin n → R ⊗[F] E) : qM R σ t c ∈ HermR R σ n := by
  intro i j
  have h : sigR R σ (sigR R σ (c j)) = c j := GlobalTheory.GaussMean.OneVec.sigR_sigR R hσ _
  show sigR R σ (qM R σ t c j i) = qM R σ t c i j
  simp only [qM, map_mul, sigR_inclT, h]
  ring

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem schurM_eq (t : F) (a : R → Rˣ) (S : Matrix (Fin (n + 1)) (Fin (n + 1)) (R ⊗[F] E))
    (i j : Fin n) : schurM R σ t a S i j = S i.succ j.succ - qM R σ t (cvec R t a S) i j := rfl

/- English proof (translation)
Establish `hm : schurM R σ t a (S : Matrix (Fin (n + 1)) (Fin (n + 1)) (R ⊗[F] E)) = (S'' : Matrix (Fin n) (Fin n) (R ⊗[F] E)) - qM R σ t (cvec R t a (S : Matrix _ _ _))`. Use function extensionality and compare the values at `i j`. Rewrite using `[schurM_eq, h]`. Both sides reduce to the same expression. Establish `hmem : schurM R σ t a (S : Matrix (Fin (n + 1)) (Fin (n + 1)) (R ⊗[F] E)) ∈ HermR R σ n`.

Rewrite using `[hm]`. Conclude with `sub_mem S''.2 (qM_mem R σ hσ t _)`. Apply `Subtype.ext` to reduce the goal to its premises. Rewrite using `[schur_coe R σ t a S hmem, hm]`. Both sides reduce to the same expression.
-/
theorem schur_split (hσ : IsCMExt F E σ) (t : F) (a : R → Rˣ) (S : HermR R σ (n + 1))
    (S'' : HermR R σ n)
    (h : ∀ i j, (S : Matrix (Fin (n + 1)) (Fin (n + 1)) (R ⊗[F] E)) i.succ j.succ =
      (S'' : Matrix (Fin n) (Fin n) (R ⊗[F] E)) i j) :
    schur R σ t a S = S'' - ⟨qM R σ t (cvec R t a (S : Matrix _ _ _)), qM_mem R σ hσ t _⟩ := by
  have hm : schurM R σ t a (S : Matrix (Fin (n + 1)) (Fin (n + 1)) (R ⊗[F] E)) =
      (S'' : Matrix (Fin n) (Fin n) (R ⊗[F] E)) - qM R σ t (cvec R t a (S : Matrix _ _ _)) := by
    funext i j
    rw [schurM_eq, h]
    rfl
  have hmem : schurM R σ t a (S : Matrix (Fin (n + 1)) (Fin (n + 1)) (R ⊗[F] E)) ∈ HermR R σ n := by
    rw [hm]
    exact sub_mem S''.2 (qM_mem R σ hσ t _)
  apply Subtype.ext
  rw [schur_coe R σ t a S hmem, hm]
  rfl

/- English proof (translation)
Use `GlobalTheory.GaussMean.OneVec.half_trace (F := F) (E := E) (σ := σ) R hσ x` as an intermediate fact. Rewrite `this` using `[Algebra.TensorProduct.algebraMap_apply]`. Simplify `this` using `[s0, h]`.
-/
theorem corner_half_trace_of_cm_pure_tensor (hσ : IsCMExt F E σ) (S : Matrix (Fin (n + 1)) (Fin (n + 1)) (R ⊗[F] E)) (x : R)
    (h : S 0 0 = x ⊗ₜ[F] (1 : E)) : s0 R S = x := by
  have := GlobalTheory.GaussMean.OneVec.half_trace (F := F) (E := E) (σ := σ) R hσ x
  rw [Algebra.TensorProduct.algebraMap_apply] at this
  simpa [s0, h] using this

end Alg

/- English proof (translation)
Introduce `F E _ _ _ _ _ σ M J t n R _ _ _ _ _ d b lam m₁ m' s B₀ a κ₁ cm D φ hφ`. Take `⟨hTR, hLC, hSC, hT2, -⟩` from `D.hR`. Use `haveI := hTR`. Use `haveI := hLC`. Use `haveI := hSC`.

Use `haveI := hT2`. Establish `hσ` using `D.hCM`. Establish `hlam` using `D.hlam`. Use `haveI := hlam`. Take `⟨hKring, hKlc, hKsc, hKt2, hsig, htr, -, -, -, -⟩` from `GlobalTheory.T.tensor_locally_compact_ring F E σ hσ R`.

Use `haveI := hKring`. Use `haveI := hKlc`. Use `haveI := hKsc`. Use `haveI := hKt2`. Use `haveI : BorelSpace (R ⊗[F] E) := ⟨rfl⟩`.

Take `⟨hκh, -, hνh⟩` from `GlobalTheory.T.coordinate_haar_measure F E σ hσ R d b lam hlam`. Use `haveI := hκh`. Use `haveI hHb : ∀ m, BorelSpace (HermR R σ m) := fun _ => ⟨rfl⟩`. Use `haveI hHlc : ∀ m, LocallyCompactSpace (HermR R σ m) := fun m => (GlobalTheory.T.hermitian_matrices_locally_compact_borel F E σ hσ R m).1`. Use `haveI hHsc : ∀ m, SecondCountableTopology (HermR R σ m) := fun m => (GlobalTheory.T.hermitian_matrices_locally_compact_borel F E σ hσ R m).2.1`.

Use `haveI : (coordHerm R σ b lam n).IsAddHaarMeasure := hνh n`. Use `haveI : SigmaFinite (coordK R b lam) := inferInstance`. Use `haveI : SigmaFinite (coordHerm R σ b lam n) := inferInstance`. Take `⟨e, he00, he0j, heij, hemap⟩` from `GlobalTheory.T.coordinate_homeomorph_tensor_product_measure F E σ hσ R d b lam hlam n`. Take `⟨hs0c, hacS, hcvc, hschc, hBopen⟩` from `GlobalTheory.T.continuousOn_schur_coordinates_and_isOpen_Bset F E σ M J t n R d b lam m₁ m' s B₀ a κ₁ cm D`.

Establish `hGon0` using `GlobalTheory.T.gram_fiber_cons_lintegral_eq_scale_mul_Pint F E σ M J t n R d b lam m₁ m' s B₀ a κ₁ cm D φ hφ`. Establish `hmeas` using `GlobalTheory.T.measurable_Pint' F E σ M J t n R d b lam m₁ m' s B₀ a κ₁ cm D φ hφ`. Establish `hsubst` using `GlobalTheory.T.lintegral_coordK_coordHerm_scale_shear F E σ M J t n R d b lam m₁ m' s B₀ a κ₁ cm D`. Establish `hUnt : IsOpen (Unt σ R n)` using `(GlobalTheory.T.gram_fiber_measure_locally_finite_measurable_supported F E σ hσ M n J D.hJ R D.hR d b lam hlam m' D.hm').1`. Establish `hGoff0 : ∀ S, S ∉ Bset R σ t a B₀ → ∫⁻ v, φ v ∂(fibS σ J t m₁ m' s B₀ a κ₁ cm S) = 0`.

Introduce `S hS`. Establish `h0 : fibS σ J t m₁ m' s B₀ a κ₁ cm S = 0`. Unfold `fibS`. Conclude with `Set.indicator_of_notMem hS _`. Rewrite using `[h0, lintegral_zero_measure]`.

Take `⟨G, hG⟩ : ∃ G : HermR R σ (n + 1) → ℝ≥0∞, G = fun S => ∫⁻ v, φ v ∂(fibS σ J t m₁ m' s B₀ a κ₁ cm S)` from `⟨_, rfl⟩`. Establish `hGoff : ∀ S, S ∉ Bset R σ t a B₀ → G S = 0`. Introduce `S hS`. Rewrite using `[hG]`. Conclude with `hGoff0 S hS`.

Establish `hGon : ∀ S ∈ (Bset R σ t a B₀ : Set (HermR R σ (n + 1))), G S = (κ₁ (a (s0 R (S : Matrix (Fin (n + 1)) (Fin (n + 1)) (R ⊗[F] E)))) : ℝ≥0∞) * (cm (a (s0 R (S : Matrix (Fin (n + 1)) (Fin (n + 1)) (R ⊗[F] E)))) : ℝ≥0∞) ^ n * Pint σ J t m₁ m' s φ ((a (s0 R (S : Matrix (Fin (n + 1)) ( …`. Introduce `S hS`. Rewrite using `[hG]`. Conclude with `hGon0 S hS`. Use `show ∫⁻ S, (fun S => ∫⁻ v, φ v ∂(fibS σ J t m₁ m' s B₀ a κ₁ cm S)) S ∂(coordHerm R σ b lam (n + 1)) = _`.

Rewrite using `[← hG]`. Use `clear hGon0 hGoff0 hG`. Establish `hGm : Measurable G`. Use `measurable_of_restrict_of_restrict_compl hBopen.measurableSet ?_ ?_` and prove the remaining obligations. Establish `hsub : (Bset R σ t a B₀ : Set (HermR R σ (n + 1))) ⊆ {S | s0 R (S : Matrix (Fin (n + 1)) (Fin (n + 1)) (R ⊗[F] E)) ∈ B₀}` using `fun S h => h.1`.

Establish `hk` using `continuousOn_iff_continuous_restrict.1 (hacS.mono hsub)`. Establish `hc` using `continuousOn_iff_continuous_restrict.1 (hcvc.mono hsub)`. Establish `hw` using `continuousOn_iff_continuous_restrict.1 (hschc.mono hsub)`. Establish `hP` using `hmeas.comp (((Units.continuous_val.comp hk).prodMk (hc.prodMk hw)).measurable)`. Establish `hE : (Bset R σ t a B₀ : Set (HermR R σ (n + 1))).domRestrict G = _`.

Use function extensionality and compare the values at `fun S => hGon S S.2`. Rewrite using `[hE]`. Conclude with `(((ENNReal.continuous_coe.comp (D.hκc.comp hk)).measurable).mul (((ENNReal.continuous_coe.comp (D.hcmc.comp hk)).measurable).pow_const n)).mul hP`. Establish `hE : (Bset R σ t a B₀ : Set (HermR R σ (n + 1)))ᶜ.domRestrict G = fun _ => 0`. Use function extensionality and compare the values at `fun S => hGoff S S.2`.

Rewrite using `[hE]`. Conclude with `measurable_const`. Establish `hL : ∫⁻ S, G S ∂(coordHerm R σ b lam (n + 1)) = ∫⁻ x, ∫⁻ r, ∫⁻ S'', G (e (x, r, S'')) ∂(coordHerm R σ b lam n) ∂(Measure.pi fun _ => coordK R b lam) ∂lam`. Establish `hGe : Measurable (fun p => G (e p))` using `hGm.comp e.continuous.measurable`. Rewrite using `[← hemap, lintegral_map hGm e.continuous.measurable, lintegral_prod _ hGe.aemeasurable]`.

Use `lintegral_congr fun x => ?_` and prove the remaining obligations. Conclude with `lintegral_prod _ (hGe.comp measurable_prodMk_left).aemeasurable`. Establish `hs0 : ∀ p, s0 R (e p : Matrix (Fin (n + 1)) (Fin (n + 1)) (R ⊗[F] E)) = p.1` using `fun p => corner_half_trace_of_cm_pure_tensor R σ hσ _ _ (he00 p)`. Establish `hoff : ∀ x, x ∉ B₀ → ∫⁻ r, ∫⁻ S'', G (e (x, r, S'')) ∂(coordHerm R σ b lam n) ∂(Measure.pi fun _ => coordK R b lam) = 0`. Introduce `x hx`.

Establish `h0 : ∀ (r : Fin n → R ⊗[F] E) (S'' : HermR R σ n), G (e (x, r, S'')) = 0`. Introduce `r S''`. Use `hGoff _ fun h => hx ?_` and prove the remaining obligations. Establish `h1` using `h.1`. Rewrite `h1` using `[hs0]`. Then use the resulting hypothesis.

Simplify using `[h0]`. Establish `hon : ∀ x ∈ B₀, ∫⁻ r, ∫⁻ S'', G (e (x, r, S'')) ∂(coordHerm R σ b lam n) ∂(Measure.pi fun _ => coordK R b lam) = (κ₁ (a x) : ℝ≥0∞) * ∫⁻ c : Fin n → R ⊗[F] E, ∫⁻ S' in Unt σ R n, Pint σ J t m₁ m' s φ ((a x : Rˣ) : R) c S' ∂(coordHerm R σ b lam n) ∂(Measure.pi fun _ => coordK R b l …`. Introduce `x hx`. Take `⟨u, hu⟩ : ∃ u : Rˣ, u = a x` from `⟨_, rfl⟩`. Rewrite using `[← hu]`.

Take `⟨cr, hcrdef⟩ : ∃ cr : (Fin n → R ⊗[F] E) → Fin n → R ⊗[F] E, cr = fun r j => ((((u⁻¹ : Rˣ) : R) ⊗ₜ[F] (algebraMap F E t⁻¹)) * r j)` from `⟨_, rfl⟩`. Establish `hcr : Continuous cr`. Rewrite using `[hcrdef]`. Conclude with `continuous_pi fun j => continuous_const.mul (continuous_apply j)`. Set `w : (Fin n → R ⊗[F] E) → HermR R σ n` to `fun r => ⟨qM R σ t (cr r), qM_mem R σ hσ t _⟩`.

Establish `hw : Measurable w`. Establish `hwc : Continuous w`. Use `Continuous.subtype_mk (continuous_pi fun i => continuous_pi fun j => ?_) _` and prove the remaining obligations. Conclude with `((hsig.comp ((continuous_apply i).comp hcr)).mul continuous_const).mul ((continuous_apply j).comp hcr)`. Conclude with `hwc.measurable`.

Set `f : (Fin n → R ⊗[F] E) × HermR R σ n → ℝ≥0∞` to `fun z => (Unt σ R n).indicator (fun S' => Pint σ J t m₁ m' s φ (u : R) z.1 S') z.2`. Establish `hf : Measurable f`. Establish `h1 : Measurable fun z : (Fin n → R ⊗[F] E) × HermR R σ n => Pint σ J t m₁ m' s φ (u : R) z.1 z.2` using `hmeas.comp (measurable_const.prodMk measurable_id)`. Conclude with `h1.indicator (measurable_snd hUnt.measurableSet)`. Establish `hpt : ∀ (r : Fin n → R ⊗[F] E) (S'' : HermR R σ n), G (e (x, r, S'')) = ((κ₁ u : ℝ≥0∞) * (cm u : ℝ≥0∞) ^ n) * f (cr r, S'' - w r)`.

Introduce `r S''`. Establish `h0 : s0 R (e (x, r, S'') : Matrix (Fin (n + 1)) (Fin (n + 1)) (R ⊗[F] E)) = x` using `hs0 _`. Establish `h1 : cvec R t a (e (x, r, S'') : Matrix (Fin (n + 1)) (Fin (n + 1)) (R ⊗[F] E)) = cr r`. Use function extensionality and compare the values at `j`. Rewrite using `[hcrdef]`.

Use `show ((((a (s0 R _))⁻¹ : Rˣ) : R) ⊗ₜ[F] (algebraMap F E t⁻¹)) * _ = _`. Rewrite using `[h0, he0j, ← hu]`. Establish `h2 : schur R σ t a (e (x, r, S'')) = S'' - w r`. Rewrite using `[schur_split R σ hσ t a (e (x, r, S'')) S'' (heij (x, r, S''))]`. Establish `h3 : (⟨qM R σ t (cvec R t a (e (x, r, S'') : Matrix (Fin (n + 1)) (Fin (n + 1)) (R ⊗[F] E))), qM_mem R σ hσ t _⟩ : HermR R σ n) = w r` using `Subtype.ext (congrArg (qM R σ t) h1)`.

Rewrite using `[h3]`. Distinguish the cases in `hU : S'' - w r ∈ Unt σ R n`. Establish `hB : e (x, r, S'') ∈ (Bset R σ t a B₀ : Set (HermR R σ (n + 1)))` using `⟨by show s0 R _ ∈ B₀; rw [h0]; exact hx, by rw [h2]; exact hU⟩`. Rewrite using `[hGon _ hB, h0, h1, h2, ← hu]`. Simplify using `only [f, Set.indicator_of_mem hU]`.

Establish `hB : e (x, r, S'') ∉ (Bset R σ t a B₀ : Set (HermR R σ (n + 1)))`. Introduce `h`. Establish `h3` using `h.2`. Rewrite `h3` using `[h2]`. Conclude with `hU h3`.

Rewrite using `[hGoff _ hB]`. Simplify using `only [f, Set.indicator_of_notMem hU, mul_zero]`. Establish `hC : ((κ₁ u : ℝ≥0∞) * (cm u : ℝ≥0∞) ^ n) ≠ ∞` using `ENNReal.mul_ne_top ENNReal.coe_ne_top (ENNReal.pow_ne_top ENNReal.coe_ne_top)`. Establish `hS : ∫⁻ c, ∫⁻ S', f (c, S') ∂(coordHerm R σ b lam n) ∂(Measure.pi fun _ => coordK R b lam) = (cm u : ℝ≥0∞) ^ n * ∫⁻ r, ∫⁻ S'', f (cr r, S'' - w r) ∂(coordHerm R σ b lam n) ∂(Measure.pi fun _ => coordK R b lam)`. Rewrite using `[hcrdef]`.

Conclude with `hsubst u w hw f hf`. Combine the equalities or inequalities in the displayed calculation. Simplify using `only [hpt]`. Use `_ = ((κ₁ u : ℝ≥0∞) * (cm u : ℝ≥0∞) ^ n) * ∫⁻ r, ∫⁻ S'', f (cr r, S'' - w r) ∂(coordHerm R σ b lam n) ∂(Measure.pi fun _ => coordK R b lam) := by`. Simplify using `only [lintegral_const_mul' _ _ hC]`.

Use `_ = (κ₁ u : ℝ≥0∞) * ((cm u : ℝ≥0∞) ^ n * ∫⁻ r, ∫⁻ S'', f (cr r, S'' - w r) ∂(coordHerm R σ b lam n) ∂(Measure.pi fun _ => coordK R b lam)) := mul_assoc _ _ _`. Use `_ = (κ₁ u : ℝ≥0∞) * ∫⁻ c, ∫⁻ S', f (c, S') ∂(coordHerm R σ b lam n) ∂(Measure.pi fun _ => coordK R b lam) := by rw [hS]`. Use `_ = _ := by`. Use `congr 1`. Use `lintegral_congr fun c => ?_` and prove the remaining obligations.

Conclude with `lintegral_indicator hUnt.measurableSet (fun S' => Pint σ J t m₁ m' s φ (u : R) c S')`. Rewrite using `[hL]`. Unfold `Mid`. Combine the equalities or inequalities in the displayed calculation. Use `lintegral_congr fun x => ?_` and prove the remaining obligations.

Distinguish the cases in `hx : x ∈ B₀`. Rewrite using `[Set.indicator_of_mem hx]`. Rewrite using `[Set.indicator_of_notMem hx, hoff x hx]`. Use `_ = ∫⁻ x in B₀, ∫⁻ r, ∫⁻ S'', G (e (x, r, S'')) ∂(coordHerm R σ b lam n) ∂(Measure.pi fun _ => coordK R b lam) ∂lam := lintegral_indicator D.hB₀.measurableSet _`. Use `_ = _ := setLIntegral_congr_fun D.hB₀.measurableSet hon`.
-/
theorem fold : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (M : ℕ) (J : Matrix (Fin M) (Fin M) E) (t : F) (n : ℕ) (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [MeasurableSpace R] [BorelSpace R] (d : ℕ) (b : Module.Basis (Fin d) F E) (lam : Measure R) (m₁ : HermR R σ 1 → Measure (Fin 1 → Fin (M + 1) → R ⊗[F] E)) (m' : HermR R σ n → Measure (Fin n → Fin M → R ⊗[F] E)) (s : (Fin 1 → Fin (M + 1) → R ⊗[F] E) → HA R σ (blockOne (algebraMap F E t) J)) (B₀ : Set R) (a : R → Rˣ) (κ₁ cm : Rˣ → ℝ≥0), StageData σ J t n b lam m₁ m' s B₀ a κ₁ cm → ∀ φ : (Fin (n + 1) → Fin (M + 1) → R ⊗[F] E) → ℝ≥0∞, Measurable φ → ∫⁻ S, ∫⁻ v, φ v ∂(fibS σ J t m₁ m' s B₀ a κ₁ cm S) ∂(coordHerm R σ b lam (n + 1)) = Mid σ J t m₁ m' s B₀ a κ₁ b lam φ := by
  intro F E _ _ _ _ _ σ M J t n R _ _ _ _ _ d b lam m₁ m' s B₀ a κ₁ cm D φ hφ
  obtain ⟨hTR, hLC, hSC, hT2, -⟩ := D.hR
  haveI := hTR
  haveI := hLC
  haveI := hSC
  haveI := hT2
  have hσ := D.hCM
  have hlam := D.hlam
  haveI := hlam
  obtain ⟨hKring, hKlc, hKsc, hKt2, hsig, htr, -, -, -, -⟩ := GlobalTheory.T.tensor_locally_compact_ring F E σ hσ R
  haveI := hKring
  haveI := hKlc
  haveI := hKsc
  haveI := hKt2
  haveI : BorelSpace (R ⊗[F] E) := ⟨rfl⟩
  obtain ⟨hκh, -, hνh⟩ := GlobalTheory.T.coordinate_haar_measure F E σ hσ R d b lam hlam
  haveI := hκh
  haveI hHb : ∀ m, BorelSpace (HermR R σ m) := fun _ => ⟨rfl⟩
  haveI hHlc : ∀ m, LocallyCompactSpace (HermR R σ m) := fun m =>
    (GlobalTheory.T.hermitian_matrices_locally_compact_borel F E σ hσ R m).1
  haveI hHsc : ∀ m, SecondCountableTopology (HermR R σ m) := fun m =>
    (GlobalTheory.T.hermitian_matrices_locally_compact_borel F E σ hσ R m).2.1
  haveI : (coordHerm R σ b lam n).IsAddHaarMeasure := hνh n
  haveI : SigmaFinite (coordK R b lam) := inferInstance
  haveI : SigmaFinite (coordHerm R σ b lam n) := inferInstance
  obtain ⟨e, he00, he0j, heij, hemap⟩ := GlobalTheory.T.coordinate_homeomorph_tensor_product_measure F E σ hσ R d b lam hlam n
  obtain ⟨hs0c, hacS, hcvc, hschc, hBopen⟩ :=
    GlobalTheory.T.continuousOn_schur_coordinates_and_isOpen_Bset F E σ M J t n R d b lam m₁ m' s B₀ a κ₁ cm D
  have hGon0 := GlobalTheory.T.gram_fiber_cons_lintegral_eq_scale_mul_Pint F E σ M J t n R d b lam m₁ m' s B₀ a κ₁ cm D φ hφ
  have hmeas := GlobalTheory.T.measurable_Pint' F E σ M J t n R d b lam m₁ m' s B₀ a κ₁ cm D φ hφ
  have hsubst := GlobalTheory.T.lintegral_coordK_coordHerm_scale_shear F E σ M J t n R d b lam m₁ m' s B₀ a κ₁ cm D
  have hUnt : IsOpen (Unt σ R n) :=
    (GlobalTheory.T.gram_fiber_measure_locally_finite_measurable_supported F E σ hσ M n J D.hJ R D.hR d b lam hlam m' D.hm').1
  have hGoff0 : ∀ S, S ∉ Bset R σ t a B₀ →
      ∫⁻ v, φ v ∂(fibS σ J t m₁ m' s B₀ a κ₁ cm S) = 0 := by
    intro S hS
    have h0 : fibS σ J t m₁ m' s B₀ a κ₁ cm S = 0 := by
      unfold fibS
      exact Set.indicator_of_notMem hS _
    rw [h0, lintegral_zero_measure]
  obtain ⟨G, hG⟩ : ∃ G : HermR R σ (n + 1) → ℝ≥0∞,
      G = fun S => ∫⁻ v, φ v ∂(fibS σ J t m₁ m' s B₀ a κ₁ cm S) := ⟨_, rfl⟩
  have hGoff : ∀ S, S ∉ Bset R σ t a B₀ → G S = 0 := by
    intro S hS
    rw [hG]
    exact hGoff0 S hS
  have hGon : ∀ S ∈ (Bset R σ t a B₀ : Set (HermR R σ (n + 1))), G S =
      (κ₁ (a (s0 R (S : Matrix (Fin (n + 1)) (Fin (n + 1)) (R ⊗[F] E)))) : ℝ≥0∞) *
      (cm (a (s0 R (S : Matrix (Fin (n + 1)) (Fin (n + 1)) (R ⊗[F] E)))) : ℝ≥0∞) ^ n *
      Pint σ J t m₁ m' s φ ((a (s0 R (S : Matrix (Fin (n + 1)) (Fin (n + 1)) (R ⊗[F] E)))) : R)
        (cvec R t a (S : Matrix (Fin (n + 1)) (Fin (n + 1)) (R ⊗[F] E))) (schur R σ t a S) := by
    intro S hS
    rw [hG]
    exact hGon0 S hS
  show ∫⁻ S, (fun S => ∫⁻ v, φ v ∂(fibS σ J t m₁ m' s B₀ a κ₁ cm S)) S ∂(coordHerm R σ b lam (n + 1)) = _
  rw [← hG]
  clear hGon0 hGoff0 hG
  have hGm : Measurable G := by
    refine measurable_of_restrict_of_restrict_compl hBopen.measurableSet ?_ ?_
    · have hsub : (Bset R σ t a B₀ : Set (HermR R σ (n + 1))) ⊆
          {S | s0 R (S : Matrix (Fin (n + 1)) (Fin (n + 1)) (R ⊗[F] E)) ∈ B₀} := fun S h => h.1
      have hk := continuousOn_iff_continuous_restrict.1 (hacS.mono hsub)
      have hc := continuousOn_iff_continuous_restrict.1 (hcvc.mono hsub)
      have hw := continuousOn_iff_continuous_restrict.1 (hschc.mono hsub)
      have hP := hmeas.comp (((Units.continuous_val.comp hk).prodMk (hc.prodMk hw)).measurable)
      have hE : (Bset R σ t a B₀ : Set (HermR R σ (n + 1))).domRestrict G = _ :=
        funext fun S => hGon S S.2
      rw [hE]
      exact (((ENNReal.continuous_coe.comp (D.hκc.comp hk)).measurable).mul
        (((ENNReal.continuous_coe.comp (D.hcmc.comp hk)).measurable).pow_const n)).mul hP
    · have hE : (Bset R σ t a B₀ : Set (HermR R σ (n + 1)))ᶜ.domRestrict G = fun _ => 0 :=
        funext fun S => hGoff S S.2
      rw [hE]
      exact measurable_const
  have hL : ∫⁻ S, G S ∂(coordHerm R σ b lam (n + 1)) =
      ∫⁻ x, ∫⁻ r, ∫⁻ S'', G (e (x, r, S'')) ∂(coordHerm R σ b lam n)
        ∂(Measure.pi fun _ => coordK R b lam) ∂lam := by
    have hGe : Measurable (fun p => G (e p)) := hGm.comp e.continuous.measurable
    rw [← hemap, lintegral_map hGm e.continuous.measurable, lintegral_prod _ hGe.aemeasurable]
    refine lintegral_congr fun x => ?_
    exact lintegral_prod _ (hGe.comp measurable_prodMk_left).aemeasurable
  have hs0 : ∀ p, s0 R (e p : Matrix (Fin (n + 1)) (Fin (n + 1)) (R ⊗[F] E)) = p.1 :=
    fun p => corner_half_trace_of_cm_pure_tensor R σ hσ _ _ (he00 p)
  have hoff : ∀ x, x ∉ B₀ → ∫⁻ r, ∫⁻ S'', G (e (x, r, S'')) ∂(coordHerm R σ b lam n)
      ∂(Measure.pi fun _ => coordK R b lam) = 0 := by
    intro x hx
    have h0 : ∀ (r : Fin n → R ⊗[F] E) (S'' : HermR R σ n), G (e (x, r, S'')) = 0 := by
      intro r S''
      refine hGoff _ fun h => hx ?_
      have h1 := h.1
      rwa [hs0] at h1
    simp [h0]
  have hon : ∀ x ∈ B₀, ∫⁻ r, ∫⁻ S'', G (e (x, r, S'')) ∂(coordHerm R σ b lam n)
      ∂(Measure.pi fun _ => coordK R b lam) = (κ₁ (a x) : ℝ≥0∞) * ∫⁻ c : Fin n → R ⊗[F] E,
        ∫⁻ S' in Unt σ R n, Pint σ J t m₁ m' s φ ((a x : Rˣ) : R) c S' ∂(coordHerm R σ b lam n)
        ∂(Measure.pi fun _ => coordK R b lam) := by
    intro x hx
    obtain ⟨u, hu⟩ : ∃ u : Rˣ, u = a x := ⟨_, rfl⟩
    rw [← hu]
    obtain ⟨cr, hcrdef⟩ : ∃ cr : (Fin n → R ⊗[F] E) → Fin n → R ⊗[F] E,
        cr = fun r j => ((((u⁻¹ : Rˣ) : R) ⊗ₜ[F] (algebraMap F E t⁻¹)) * r j) := ⟨_, rfl⟩
    have hcr : Continuous cr := by
      rw [hcrdef]
      exact continuous_pi fun j => continuous_const.mul (continuous_apply j)
    let w : (Fin n → R ⊗[F] E) → HermR R σ n := fun r => ⟨qM R σ t (cr r), qM_mem R σ hσ t _⟩
    have hw : Measurable w := by
      have hwc : Continuous w := by
        refine Continuous.subtype_mk (continuous_pi fun i => continuous_pi fun j => ?_) _
        exact ((hsig.comp ((continuous_apply i).comp hcr)).mul continuous_const).mul
          ((continuous_apply j).comp hcr)
      exact hwc.measurable
    let f : (Fin n → R ⊗[F] E) × HermR R σ n → ℝ≥0∞ := fun z =>
      (Unt σ R n).indicator (fun S' => Pint σ J t m₁ m' s φ (u : R) z.1 S') z.2
    have hf : Measurable f := by
      have h1 : Measurable fun z : (Fin n → R ⊗[F] E) × HermR R σ n =>
          Pint σ J t m₁ m' s φ (u : R) z.1 z.2 :=
        hmeas.comp (measurable_const.prodMk measurable_id)
      exact h1.indicator (measurable_snd hUnt.measurableSet)
    have hpt : ∀ (r : Fin n → R ⊗[F] E) (S'' : HermR R σ n), G (e (x, r, S'')) =
        ((κ₁ u : ℝ≥0∞) * (cm u : ℝ≥0∞) ^ n) * f (cr r, S'' - w r) := by
      intro r S''
      have h0 : s0 R (e (x, r, S'') : Matrix (Fin (n + 1)) (Fin (n + 1)) (R ⊗[F] E)) = x := hs0 _
      have h1 : cvec R t a (e (x, r, S'') : Matrix (Fin (n + 1)) (Fin (n + 1)) (R ⊗[F] E)) = cr r := by
        funext j
        rw [hcrdef]
        show ((((a (s0 R _))⁻¹ : Rˣ) : R) ⊗ₜ[F] (algebraMap F E t⁻¹)) * _ = _
        rw [h0, he0j, ← hu]
      have h2 : schur R σ t a (e (x, r, S'')) = S'' - w r := by
        rw [schur_split R σ hσ t a (e (x, r, S'')) S'' (heij (x, r, S''))]
        have h3 : (⟨qM R σ t (cvec R t a (e (x, r, S'') : Matrix (Fin (n + 1)) (Fin (n + 1)) (R ⊗[F] E))),
            qM_mem R σ hσ t _⟩ : HermR R σ n) = w r := Subtype.ext (congrArg (qM R σ t) h1)
        rw [h3]
      by_cases hU : S'' - w r ∈ Unt σ R n
      · have hB : e (x, r, S'') ∈ (Bset R σ t a B₀ : Set (HermR R σ (n + 1))) :=
          ⟨by show s0 R _ ∈ B₀; rw [h0]; exact hx, by rw [h2]; exact hU⟩
        rw [hGon _ hB, h0, h1, h2, ← hu]
        simp only [f, Set.indicator_of_mem hU]
      · have hB : e (x, r, S'') ∉ (Bset R σ t a B₀ : Set (HermR R σ (n + 1))) := by
          intro h
          have h3 := h.2
          rw [h2] at h3
          exact hU h3
        rw [hGoff _ hB]
        simp only [f, Set.indicator_of_notMem hU, mul_zero]
    have hC : ((κ₁ u : ℝ≥0∞) * (cm u : ℝ≥0∞) ^ n) ≠ ∞ :=
      ENNReal.mul_ne_top ENNReal.coe_ne_top (ENNReal.pow_ne_top ENNReal.coe_ne_top)
    have hS : ∫⁻ c, ∫⁻ S', f (c, S') ∂(coordHerm R σ b lam n) ∂(Measure.pi fun _ => coordK R b lam) =
        (cm u : ℝ≥0∞) ^ n * ∫⁻ r, ∫⁻ S'', f (cr r, S'' - w r) ∂(coordHerm R σ b lam n)
          ∂(Measure.pi fun _ => coordK R b lam) := by
      rw [hcrdef]
      exact hsubst u w hw f hf
    calc ∫⁻ r, ∫⁻ S'', G (e (x, r, S'')) ∂(coordHerm R σ b lam n)
          ∂(Measure.pi fun _ => coordK R b lam)
        = ∫⁻ r, ∫⁻ S'', ((κ₁ u : ℝ≥0∞) * (cm u : ℝ≥0∞) ^ n) * f (cr r, S'' - w r)
          ∂(coordHerm R σ b lam n) ∂(Measure.pi fun _ => coordK R b lam) := by
          simp only [hpt]
      _ = ((κ₁ u : ℝ≥0∞) * (cm u : ℝ≥0∞) ^ n) * ∫⁻ r, ∫⁻ S'', f (cr r, S'' - w r)
          ∂(coordHerm R σ b lam n) ∂(Measure.pi fun _ => coordK R b lam) := by
          simp only [lintegral_const_mul' _ _ hC]
      _ = (κ₁ u : ℝ≥0∞) * ((cm u : ℝ≥0∞) ^ n * ∫⁻ r, ∫⁻ S'', f (cr r, S'' - w r)
          ∂(coordHerm R σ b lam n) ∂(Measure.pi fun _ => coordK R b lam)) := mul_assoc _ _ _
      _ = (κ₁ u : ℝ≥0∞) * ∫⁻ c, ∫⁻ S', f (c, S') ∂(coordHerm R σ b lam n)
          ∂(Measure.pi fun _ => coordK R b lam) := by rw [hS]
      _ = _ := by
          congr 1
          refine lintegral_congr fun c => ?_
          exact lintegral_indicator hUnt.measurableSet (fun S' => Pint σ J t m₁ m' s φ (u : R) c S')
  rw [hL]
  unfold Mid
  calc _ = ∫⁻ x, B₀.indicator (fun x => ∫⁻ r, ∫⁻ S'', G (e (x, r, S'')) ∂(coordHerm R σ b lam n)
        ∂(Measure.pi fun _ => coordK R b lam)) x ∂lam := by
        refine lintegral_congr fun x => ?_
        by_cases hx : x ∈ B₀
        · rw [Set.indicator_of_mem hx]
        · rw [Set.indicator_of_notMem hx, hoff x hx]
    _ = ∫⁻ x in B₀, ∫⁻ r, ∫⁻ S'', G (e (x, r, S'')) ∂(coordHerm R σ b lam n)
        ∂(Measure.pi fun _ => coordK R b lam) ∂lam := lintegral_indicator D.hB₀.measurableSet _
    _ = _ := setLIntegral_congr_fun D.hB₀.measurableSet hon

end GlobalTheory.CompanionTheory.SW.PiLocalization₂.Fold

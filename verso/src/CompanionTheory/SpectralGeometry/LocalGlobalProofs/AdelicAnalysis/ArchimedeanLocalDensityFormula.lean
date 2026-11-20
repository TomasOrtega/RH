import Mathlib
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.ArchimedeanCoordinateMeasureTransportStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.GaussQ
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.CoordinateHomeomorphRankOneTuplesStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.HermitianRankOneHomeomorphBase
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.InfiniteAdelesLocalRingTotallyRealStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.TensorLocallyCompactRingStatement
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.BB NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

noncomputable section

namespace GlobalTheory.CompanionTheory.SW.BB.InfDens

section Alg

variable {F E : Type} [Field F] [Field E] [Algebra F E] {σ : E →ₐ[F] E} (R : Type) [CommRing R]
  [Algebra F R]

/- English proof (translation)
Proceed by induction on `z using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `tmul r y => simp [sigR, hs]`. Consider the case `add a c ha hc => rw [map_add, map_add, ha, hc]`.
-/
theorem sigR_sigR (hs : ∀ x, σ (σ x) = x) (z : R ⊗[F] E) : sigR R σ (sigR R σ z) = z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul r y => simp [sigR, hs]
  | add a c ha hc => rw [map_add, map_add, ha, hc]

/- English proof (translation)
Simplify using `[sigR, inclR]`.
-/
theorem sigR_inclR (y : E) : sigR R σ (inclR R y) = inclR R (σ y) := by
  simp [sigR, inclR]

/- English proof (translation)
Simplify using `only [hR, hform, JR, map_sum, map_mul, Matrix.map_apply, sigR_sigR R hs, sigR_inclR, hJ]`. Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Expand and normalize the polynomial expressions, which then agree.
-/
theorem sigR_hR (hs : ∀ x, σ (σ x) = x) {M : ℕ} {J : Matrix (Fin M) (Fin M) E}
    (hJ : ∀ i j, σ (J j i) = J i j) (x y : Fin M → R ⊗[F] E) :
    sigR R σ (hR R σ J x y) = hR R σ J y x := by
  simp only [hR, hform, JR, map_sum, map_mul, Matrix.map_apply, sigR_sigR R hs, sigR_inclR, hJ]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => ?_
  ring

/- English proof (translation)
Introduce `a c` and use `sigR_hR R hs hJ (X c) (X a)`.
-/
theorem gramR_mem (hs : ∀ x, σ (σ x) = x) {M n : ℕ} {J : Matrix (Fin M) (Fin M) E}
    (hJ : ∀ i j, σ (J j i) = J i j) (X : Fin n → Fin M → R ⊗[F] E) :
    gramR R σ J X ∈ HermR R σ n := fun a c => sigR_hR R hs hJ (X c) (X a)

end Alg

section Real

variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E]

/- English proof (translation)
Set `ew : Ainf F →+* ℝ` to `(Pi.evalRingHom (fun _ : InfinitePlace F => ℝ) w).comp (e : Ainf F →+* _)`. Establish `hew : ∀ a, ew a = e a w` using `fun _ => rfl`. Establish `hcomp : ew.comp (algebraMap F (Ainf F)) = ρ w` using `RingHom.ext fun x => hρ x w`. Establish `hx : xw e b X w = ew ∘ cv (Ainf F) b (X 0)` using `rfl`. Establish `hm : B.map (ρ w) = (B.map (algebraMap F (Ainf F))).map ew`.

Rewrite using `[← hcomp]`. Use extensionality with `i j`. Both sides reduce to the same expression. Establish `hhalf : ρ w (1 / 2) = 1 / 2` using `by rw [map_div₀, map_one, map_ofNat]`. Rewrite using `[← hew, map_mul, hew, hρ, hhalf]`.

Use `show _ * ew (Algebra.trace (Ainf F) (Ainf F ⊗[F] E) (hR (Ainf F) σ J (X 0) (X 0))) = _`. Rewrite using `[hB, hx, hm, RingHom.map_dotProduct]`. Establish `hv : ⇑ew ∘ (B.map (algebraMap F (Ainf F)) *ᵥ cv (Ainf F) b (X 0)) = (B.map (algebraMap F (Ainf F))).map ew *ᵥ (⇑ew ∘ cv (Ainf F) b (X 0))`. Use function extensionality and compare the values at `fun i => RingHom.map_mulVec ew _ _ i`. Rewrite using `[hv]`.
-/
theorem e_half_trace {σ : E →ₐ[F] E} {M d : ℕ} {J : Matrix (Fin M) (Fin M) E}
    (b : Module.Basis (Fin d) F E) (B : Matrix (Fin M × Fin d) (Fin M × Fin d) F)
    (hB : ∀ x y : Fin M → Ainf F ⊗[F] E,
      Algebra.trace (Ainf F) (Ainf F ⊗[F] E) (hR (Ainf F) σ J x y) =
        cv (Ainf F) b x ⬝ᵥ (B.map (algebraMap F (Ainf F)) *ᵥ cv (Ainf F) b y))
    (ρ : InfinitePlace F → (F →+* ℝ)) (e : Ainf F ≃+* (InfinitePlace F → ℝ))
    (hρ : ∀ x w, e (algebraMap F (Ainf F) x) w = ρ w x)
    (X : Fin 1 → Fin M → Ainf F ⊗[F] E) (w : InfinitePlace F) :
    e (algebraMap F (Ainf F) (1 / 2) *
        Algebra.trace (Ainf F) (Ainf F ⊗[F] E) (gramR (Ainf F) σ J X 0 0)) w =
      (1 / 2 : ℝ) * (xw e b X w ⬝ᵥ (B.map (ρ w) *ᵥ xw e b X w)) := by
  let ew : Ainf F →+* ℝ := (Pi.evalRingHom (fun _ : InfinitePlace F => ℝ) w).comp (e : Ainf F →+* _)
  have hew : ∀ a, ew a = e a w := fun _ => rfl
  have hcomp : ew.comp (algebraMap F (Ainf F)) = ρ w := RingHom.ext fun x => hρ x w
  have hx : xw e b X w = ew ∘ cv (Ainf F) b (X 0) := rfl
  have hm : B.map (ρ w) = (B.map (algebraMap F (Ainf F))).map ew := by
    rw [← hcomp]
    ext i j
    rfl
  have hhalf : ρ w (1 / 2) = 1 / 2 := by rw [map_div₀, map_one, map_ofNat]
  rw [← hew, map_mul, hew, hρ, hhalf]
  show _ * ew (Algebra.trace (Ainf F) (Ainf F ⊗[F] E) (hR (Ainf F) σ J (X 0) (X 0))) = _
  rw [hB, hx, hm, RingHom.map_dotProduct]
  have hv : ⇑ew ∘ (B.map (algebraMap F (Ainf F)) *ᵥ cv (Ainf F) b (X 0)) =
      (B.map (algebraMap F (Ainf F))).map ew *ᵥ (⇑ew ∘ cv (Ainf F) b (X 0)) :=
    funext fun i => RingHom.map_mulVec ew _ _ i
  rw [hv]

end Real

/- English proof (translation)
Introduce `F E _ _ _ _ _ σ hcm M J hJ hM d b B hB ρ e he hρ Pm laminf hlam hmap Dinf hDc hD0 hDinf U hU`. Take `⟨i1, i2, i3, i4, -⟩` from `GlobalTheory.T.infinite_adeles_local_ring_totally_real F hcm.1`. Use `haveI := i1`. Use `haveI := i2`. Use `haveI := i3`.

Use `haveI := i4`. Use `haveI : BorelSpace (Ainf F) := ⟨rfl⟩`. Use `haveI : BorelSpace (HermR (Ainf F) σ 1) := ⟨rfl⟩`. Use `haveI : SigmaFinite laminf := inferInstance`. Establish `hd : d = 2`.

Establish `h1` using `Module.finrank_eq_card_basis b`. Rewrite `h1` using `[hcm.2.2.1]`. Simplify using `using h1.symm`. Establish `hs : ∀ x, σ (σ x) = x` using `HermOne.sig_sig hcm`. Use `set κ : ℝ := (Real.sqrt |(discr F : ℝ)|)⁻¹ with hκ`.

Establish `hκ0 : 0 ≤ κ` using `inv_nonneg.2 (Real.sqrt_nonneg _)`. Set `tt` to `HermOne.hermHomeo (Ainf F) (σ := σ) hcm`. Set `eH : Ainf F ≃ₜ (InfinitePlace F → ℝ)` to `he.homeomorph e`. Set `τ : HermR (Ainf F) σ 1 ≃ₜ (InfinitePlace F → ℝ)` to `tt.trans eH`. Establish `hτ : ∀ S, τ S = e (algebraMap F (Ainf F) (1 / 2) * Algebra.trace (Ainf F) (Ainf F ⊗[F] E) ((S : Matrix (Fin 1) (Fin 1) (Ainf F ⊗[F] E)) 0 0))` using `fun _ => rfl`.

Establish `hpush : (coordHerm (Ainf F) σ b laminf 1).map τ = ENNReal.ofReal κ • volume`. Establish `h1 : (τ : HermR (Ainf F) σ 1 → _) = e ∘ tt` using `rfl`. Rewrite using `[h1, ← Measure.map_map (f := tt) (g := e) eH.measurable tt.measurable, HermOne.map_coordHerm (Ainf F) hcm b laminf, hmap]`. Use `set U' : Set (InfinitePlace F → ℝ) := τ.symm ⁻¹' U with hU'def`. Establish `hU' : MeasurableSet U'` using `τ.symm.measurable hU`.

Establish `hpre : τ ⁻¹' U' = U`. Use extensionality with `S`. Simplify using `[hU'def]`. Establish `hR1 : ∫⁻ S in U, ENNReal.ofReal (κ ^ (2 * M - 1) * Dinf (e (algebraMap F (Ainf F) (1 / 2) * Algebra.trace (Ainf F) (Ainf F ⊗[F] E) ((S : Matrix (Fin 1) (Fin 1) (Ainf F ⊗[F] E)) 0 0)))) ∂(coordHerm (Ainf F) σ b laminf 1) = ENNReal.ofReal (κ ^ (2 * M)) * ∫⁻ y in U', ENNReal.ofReal …`. Establish `h2` using `setLIntegral_map (μ := coordHerm (Ainf F) σ b laminf 1) (g := τ) (f := fun y => ENNReal.ofReal (κ ^ (2 * M - 1) * Dinf y)) hU' (continuous_const.mul hDc).measurable.ennreal_ofReal τ.measurable`.

Rewrite `h2` using `[hpre, hpush]`. Simplify using `only [hτ] at h2`. Rewrite using `[← h2, Measure.restrict_smul, lintegral_smul_measure]`. Establish `h3 : ∀ y, ENNReal.ofReal (κ ^ (2 * M - 1) * Dinf y) = ENNReal.ofReal (κ ^ (2 * M - 1)) * ENNReal.ofReal (Dinf y)` using `fun y => ENNReal.ofReal_mul (pow_nonneg hκ0 _)`. Simplify using `only [h3]`.

Rewrite using `[lintegral_const_mul _ (hDc.measurable.ennreal_ofReal), smul_eq_mul, ← mul_assoc, ← ENNReal.ofReal_mul hκ0, ← pow_succ', show 2 * M - 1 + 1 = 2 * M by omega]`. Set `Φ : (Fin 1 → Fin M → Ainf F ⊗[F] E) → (InfinitePlace F → Fin M × Fin d → ℝ)` to `fun X w => xw e b X w`. Establish `hcoord` using `(GlobalTheory.T.coordinate_homeomorph_rank_one_tuples F E σ hcm (Ainf F) d b laminf hlam M).2.1`. Establish `hΦm : Measurable Φ`. Establish `hc : Continuous fun (z : Fin M × Fin d → Ainf F) (w : InfinitePlace F) (p : Fin M × Fin d) => e (z p) w` using `continuous_pi fun w => continuous_pi fun p => (continuous_apply w).comp (eH.continuous.comp (continuous_apply p))`.

Conclude with `hc.measurable.comp hcoord.measurable`. Establish `hpushL` using `GlobalTheory.T.archimedean_coordinate_measure_transport F E σ hcm M d b e he laminf hlam hmap`. Set `Q : (InfinitePlace F → Fin M × Fin d → ℝ) → (InfinitePlace F → ℝ)` to `fun x w => (1 / 2 : ℝ) * (x w ⬝ᵥ (B.map (ρ w) *ᵥ x w))`. Establish `hQc : Continuous Q`. Use `continuous_pi fun w => continuous_const.mul ?_` and prove the remaining obligations.

Conclude with `(continuous_apply w).dotProduct (continuous_const.matrix_mulVec (continuous_apply w))`. Set `G : (InfinitePlace F → Fin M × Fin d → ℝ) → ℝ≥0∞` to `fun x => ENNReal.ofReal (Real.exp (-Real.pi * ∑ w, x w ⬝ᵥ (Pm w *ᵥ x w)))`. Establish `hGm : Measurable G`. Establish `hc : Continuous fun x : InfinitePlace F → Fin M × Fin d → ℝ => Real.exp (-Real.pi * ∑ w, x w ⬝ᵥ (Pm w *ᵥ x w))`. Use `Real.continuous_exp.comp (continuous_const.mul (continuous_finset_sum _ fun w _ => ?_))` and prove the remaining obligations.

Conclude with `(continuous_apply w).dotProduct (continuous_const.matrix_mulVec (continuous_apply w))`. Conclude with `hc.measurable.ennreal_ofReal`. Establish `hset : gramR (Ainf F) σ J ⁻¹' (Subtype.val '' U) = Φ ⁻¹' (Q ⁻¹' U')`. Use extensionality with `X`. Establish `hmem` using `gramR_mem (Ainf F) hs hJ.1 X`.

Establish `hQ : Q (Φ X) = τ ⟨gramR (Ainf F) σ J X, hmem⟩`. Use function extensionality and compare the values at `w`. Rewrite using `[hτ]`. Conclude with `(e_half_trace b B hB ρ e hρ X w).symm`. Simplify using `only [Set.mem_preimage, hU'def]`.

Rewrite using `[hQ, Homeomorph.symm_apply_apply]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨S, hS, hSX⟩`. Establish `: (⟨gramR (Ainf F) σ J X, hmem⟩ : HermR (Ainf F) σ 1) = S` using `Subtype.ext hSX.symm`. Rewrite using `[this]` and apply the resulting hypothesis.

Introduce `h`. Conclude with `⟨_, h, rfl⟩`. Establish `hL1 : ∫⁻ X in gramR (Ainf F) σ J ⁻¹' (Subtype.val '' U), ENNReal.ofReal (gaussQ e b Pm X) ∂(coordW (Ainf F) b laminf 1 M) = ENNReal.ofReal (κ ^ (M * d)) * ∫⁻ y in U', ENNReal.ofReal (Dinf y)`. Establish `hA : MeasurableSet (Q ⁻¹' U')` using `hQc.measurable hU'`. Establish `h2` using `setLIntegral_map (μ := coordW (Ainf F) b laminf 1 M) hA hGm hΦm`.

Rewrite using `[hset]`. Establish `h3 : ∀ X, ENNReal.ofReal (gaussQ e b Pm X) = G (Φ X)` using `fun _ => rfl`. Simplify using `only [h3]`. Rewrite using `[← h2]`. Establish `h4 : (coordW (Ainf F) b laminf 1 M).map Φ = ENNReal.ofReal (κ ^ (M * d)) • (volume : Measure (InfinitePlace F → Fin M × Fin d → ℝ))` using `hpushL`.

Rewrite using `[h4, Measure.restrict_smul, lintegral_smul_measure, smul_eq_mul]`. Conclude with `congrArg _ (hDinf U' hU')`. Rewrite using `[hL1, hR1, hd, mul_comm M 2]`.
-/
theorem infDens : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → 3 ≤ M → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (B : Matrix (Fin M × Fin d) (Fin M × Fin d) F), (∀ x y : Fin M → Ainf F ⊗[F] E, Algebra.trace (Ainf F) (Ainf F ⊗[F] E) (hR (Ainf F) σ J x y) = cv (Ainf F) b x ⬝ᵥ (B.map (algebraMap F (Ainf F)) *ᵥ cv (Ainf F) b y)) → ∀ (ρ : InfinitePlace F → (F →+* ℝ)) (e : Ainf F ≃+* (InfinitePlace F → ℝ)), IsHomeomorph e → (∀ x w, e (algebraMap F (Ainf F) x) w = ρ w x) → ∀ (Pm : InfinitePlace F → Matrix (Fin M × Fin d) (Fin M × Fin d) ℝ) (laminf : Measure (Ainf F)), laminf.IsAddHaarMeasure → laminf.map e = ENNReal.ofReal (Real.sqrt |(discr F : ℝ)|)⁻¹ • (volume : Measure (InfinitePlace F → ℝ)) → ∀ Dinf : (InfinitePlace F → ℝ) → ℝ, Continuous Dinf → (∀ y, 0 ≤ Dinf y) → (∀ U : Set (InfinitePlace F → ℝ), MeasurableSet U → ∫⁻ x in {x : InfinitePlace F → Fin M × Fin d → ℝ | (fun w => (1 / 2 : ℝ) * (x w ⬝ᵥ (B.map (ρ w) *ᵥ x w))) ∈ U}, ENNReal.ofReal (Real.exp (-Real.pi * ∑ w, x w ⬝ᵥ (Pm w *ᵥ x w))) = ∫⁻ y in U, ENNReal.ofReal (Dinf y)) → ∀ U : Set (HermR (Ainf F) σ 1), MeasurableSet U → ∫⁻ X in gramR (Ainf F) σ J ⁻¹' (Subtype.val '' U), ENNReal.ofReal (gaussQ e b Pm X) ∂(coordW (Ainf F) b laminf 1 M) = ∫⁻ S in U, ENNReal.ofReal ((Real.sqrt |(discr F : ℝ)|)⁻¹ ^ (2 * M - 1) * Dinf (e (algebraMap F (Ainf F) (1 / 2) * Algebra.trace (Ainf F) (Ainf F ⊗[F] E) ((S : Matrix (Fin 1) (Fin 1) (Ainf F ⊗[F] E)) 0 0)))) ∂(coordHerm (Ainf F) σ b laminf 1) := by
  intro F E _ _ _ _ _ σ hcm M J hJ hM d b B hB ρ e he hρ Pm laminf hlam hmap Dinf hDc hD0 hDinf U hU
  obtain ⟨i1, i2, i3, i4, -⟩ := GlobalTheory.T.infinite_adeles_local_ring_totally_real F hcm.1
  haveI := i1
  haveI := i2
  haveI := i3
  haveI := i4
  haveI : BorelSpace (Ainf F) := ⟨rfl⟩
  haveI : BorelSpace (HermR (Ainf F) σ 1) := ⟨rfl⟩
  haveI : SigmaFinite laminf := inferInstance
  have hd : d = 2 := by
    have h1 := Module.finrank_eq_card_basis b
    rw [hcm.2.2.1] at h1
    simpa using h1.symm
  have hs : ∀ x, σ (σ x) = x := HermOne.sig_sig hcm
  set κ : ℝ := (Real.sqrt |(discr F : ℝ)|)⁻¹ with hκ
  have hκ0 : 0 ≤ κ := inv_nonneg.2 (Real.sqrt_nonneg _)

  let tt := HermOne.hermHomeo (Ainf F) (σ := σ) hcm
  let eH : Ainf F ≃ₜ (InfinitePlace F → ℝ) := he.homeomorph e
  let τ : HermR (Ainf F) σ 1 ≃ₜ (InfinitePlace F → ℝ) := tt.trans eH
  have hτ : ∀ S, τ S = e (algebraMap F (Ainf F) (1 / 2) *
      Algebra.trace (Ainf F) (Ainf F ⊗[F] E) ((S : Matrix (Fin 1) (Fin 1) (Ainf F ⊗[F] E)) 0 0)) :=
    fun _ => rfl
  have hpush : (coordHerm (Ainf F) σ b laminf 1).map τ = ENNReal.ofReal κ • volume := by
    have h1 : (τ : HermR (Ainf F) σ 1 → _) = e ∘ tt := rfl
    rw [h1, ← Measure.map_map (f := tt) (g := e) eH.measurable tt.measurable,
      HermOne.map_coordHerm (Ainf F) hcm b laminf, hmap]
  set U' : Set (InfinitePlace F → ℝ) := τ.symm ⁻¹' U with hU'def
  have hU' : MeasurableSet U' := τ.symm.measurable hU
  have hpre : τ ⁻¹' U' = U := by
    ext S
    simp [hU'def]

  have hR1 : ∫⁻ S in U, ENNReal.ofReal (κ ^ (2 * M - 1) * Dinf (e (algebraMap F (Ainf F) (1 / 2) *
        Algebra.trace (Ainf F) (Ainf F ⊗[F] E) ((S : Matrix (Fin 1) (Fin 1) (Ainf F ⊗[F] E)) 0 0))))
        ∂(coordHerm (Ainf F) σ b laminf 1) =
      ENNReal.ofReal (κ ^ (2 * M)) * ∫⁻ y in U', ENNReal.ofReal (Dinf y) := by
    have h2 := setLIntegral_map (μ := coordHerm (Ainf F) σ b laminf 1) (g := τ)
      (f := fun y => ENNReal.ofReal (κ ^ (2 * M - 1) * Dinf y)) hU'
      (continuous_const.mul hDc).measurable.ennreal_ofReal τ.measurable
    rw [hpre, hpush] at h2
    simp only [hτ] at h2
    rw [← h2, Measure.restrict_smul, lintegral_smul_measure]
    have h3 : ∀ y, ENNReal.ofReal (κ ^ (2 * M - 1) * Dinf y) =
        ENNReal.ofReal (κ ^ (2 * M - 1)) * ENNReal.ofReal (Dinf y) :=
      fun y => ENNReal.ofReal_mul (pow_nonneg hκ0 _)
    simp only [h3]
    rw [lintegral_const_mul _ (hDc.measurable.ennreal_ofReal), smul_eq_mul, ← mul_assoc,
      ← ENNReal.ofReal_mul hκ0, ← pow_succ', show 2 * M - 1 + 1 = 2 * M by omega]

  let Φ : (Fin 1 → Fin M → Ainf F ⊗[F] E) → (InfinitePlace F → Fin M × Fin d → ℝ) :=
    fun X w => xw e b X w
  have hcoord := (GlobalTheory.T.coordinate_homeomorph_rank_one_tuples F E σ hcm (Ainf F) d b laminf hlam M).2.1
  have hΦm : Measurable Φ := by
    have hc : Continuous fun (z : Fin M × Fin d → Ainf F) (w : InfinitePlace F) (p : Fin M × Fin d) =>
        e (z p) w :=
      continuous_pi fun w => continuous_pi fun p =>
        (continuous_apply w).comp (eH.continuous.comp (continuous_apply p))
    exact hc.measurable.comp hcoord.measurable
  have hpushL := GlobalTheory.T.archimedean_coordinate_measure_transport F E σ hcm M d b e he laminf hlam hmap
  let Q : (InfinitePlace F → Fin M × Fin d → ℝ) → (InfinitePlace F → ℝ) :=
    fun x w => (1 / 2 : ℝ) * (x w ⬝ᵥ (B.map (ρ w) *ᵥ x w))
  have hQc : Continuous Q := by
    refine continuous_pi fun w => continuous_const.mul ?_
    exact (continuous_apply w).dotProduct (continuous_const.matrix_mulVec (continuous_apply w))
  let G : (InfinitePlace F → Fin M × Fin d → ℝ) → ℝ≥0∞ :=
    fun x => ENNReal.ofReal (Real.exp (-Real.pi * ∑ w, x w ⬝ᵥ (Pm w *ᵥ x w)))
  have hGm : Measurable G := by
    have hc : Continuous fun x : InfinitePlace F → Fin M × Fin d → ℝ =>
        Real.exp (-Real.pi * ∑ w, x w ⬝ᵥ (Pm w *ᵥ x w)) := by
      refine Real.continuous_exp.comp (continuous_const.mul (continuous_finset_sum _ fun w _ => ?_))
      exact (continuous_apply w).dotProduct (continuous_const.matrix_mulVec (continuous_apply w))
    exact hc.measurable.ennreal_ofReal
  have hset : gramR (Ainf F) σ J ⁻¹' (Subtype.val '' U) = Φ ⁻¹' (Q ⁻¹' U') := by
    ext X
    have hmem := gramR_mem (Ainf F) hs hJ.1 X
    have hQ : Q (Φ X) = τ ⟨gramR (Ainf F) σ J X, hmem⟩ := by
      funext w
      rw [hτ]
      exact (e_half_trace b B hB ρ e hρ X w).symm
    simp only [Set.mem_preimage, hU'def]
    rw [hQ, Homeomorph.symm_apply_apply]
    constructor
    · rintro ⟨S, hS, hSX⟩
      have : (⟨gramR (Ainf F) σ J X, hmem⟩ : HermR (Ainf F) σ 1) = S := Subtype.ext hSX.symm
      rwa [this]
    · intro h
      exact ⟨_, h, rfl⟩
  have hL1 : ∫⁻ X in gramR (Ainf F) σ J ⁻¹' (Subtype.val '' U), ENNReal.ofReal (gaussQ e b Pm X)
        ∂(coordW (Ainf F) b laminf 1 M) =
      ENNReal.ofReal (κ ^ (M * d)) * ∫⁻ y in U', ENNReal.ofReal (Dinf y) := by
    have hA : MeasurableSet (Q ⁻¹' U') := hQc.measurable hU'
    have h2 := setLIntegral_map (μ := coordW (Ainf F) b laminf 1 M) hA hGm hΦm
    rw [hset]
    have h3 : ∀ X, ENNReal.ofReal (gaussQ e b Pm X) = G (Φ X) := fun _ => rfl
    simp only [h3]
    rw [← h2]
    have h4 : (coordW (Ainf F) b laminf 1 M).map Φ =
        ENNReal.ofReal (κ ^ (M * d)) • (volume : Measure (InfinitePlace F → Fin M × Fin d → ℝ)) :=
      hpushL
    rw [h4, Measure.restrict_smul, lintegral_smul_measure, smul_eq_mul]
    exact congrArg _ (hDinf U' hU')
  rw [hL1, hR1, hd, mul_comm M 2]

end GlobalTheory.CompanionTheory.SW.BB.InfDens

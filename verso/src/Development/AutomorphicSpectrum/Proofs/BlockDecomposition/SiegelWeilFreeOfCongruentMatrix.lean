import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HypOneZeroZero
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.SiegelWeilMeasureOfCongruentTarget
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.FibreFamilySmul
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.EqZeroOfSetIntegral
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerOrbitVolume.TensAll

noncomputable section

namespace GlobalTheory.CompanionTheory.WeilSiegel.Free.Scale

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
open GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.WeilSiegel.Free

/- English proof (translation)
Rewrite `hX`, the goal using `[Fintype.linearIndependent_iff]`. Introduce `w hw`. Establish `h1 : ∑ c, (g.mulVec w) c • X c = 0`. Use function extensionality and compare the values at `i`. Establish `h2` using `congrFun hw i`.

Simplify using `only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply, Finset.mul_sum, Matrix.mulVec, dotProduct, Finset.sum_mul] at h2 ⊢`. Rewrite using `[Finset.sum_comm]`. Rewrite using `[← h2]`. Use `Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun c _ => ?_` and prove the remaining obligations. Expand and normalize the polynomial expressions, which then agree.

Establish `h2 : g.mulVec w = 0` using `funext (hX _ h1)`. Establish `h3 : w = h.mulVec (g.mulVec w)`. Rewrite using `[Matrix.mulVec_mulVec, hhg, Matrix.one_mulVec]`. Introduce `a`. Rewrite using `[h3, h2, Matrix.mulVec_zero]`.

Both sides reduce to the same expression.
-/
theorem linInd_mul {K : Type} [CommRing K] {M n : ℕ} (X : Fin n → Fin M → K)
    (g h : Matrix (Fin n) (Fin n) K) (hhg : h * g = 1) (hX : LinearIndependent K X) :
    LinearIndependent K (fun (a : Fin n) (i : Fin M) => ∑ c, X c i * g c a) := by
  rw [Fintype.linearIndependent_iff] at hX ⊢
  intro w hw
  have h1 : ∑ c, (g.mulVec w) c • X c = 0 := by
    funext i
    have h2 := congrFun hw i
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply, Finset.mul_sum,
      Matrix.mulVec, dotProduct, Finset.sum_mul] at h2 ⊢
    rw [Finset.sum_comm]
    rw [← h2]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun c _ => ?_
    ring
  have h2 : g.mulVec w = 0 := funext (hX _ h1)
  have h3 : w = h.mulVec (g.mulVec w) := by
    rw [Matrix.mulVec_mulVec, hhg, Matrix.one_mulVec]
  intro a
  rw [h3, h2, Matrix.mulVec_zero]
  rfl

/- English proof (translation)
Take `⟨h1, h2, h3⟩` from `h`. Establish `hemb : MeasurableEmbedding e` using `e.measurableEmbedding`. Establish `hτ : MeasurableEmbedding τ` using `τ.measurableEmbedding`. Use `⟨?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `b`.

Establish `hset : e ⁻¹' (f ⁻¹' {ι b} ∩ U)ᶜ = (f ⁻¹' {ι (τ.symm b)} ∩ U)ᶜ`. Use extensionality with `x`. Establish `hx : e x ∈ U ↔ x ∈ U` using `Set.ext_iff.1 hU x`. Establish `hb` using `hf x (τ.symm b)`. Rewrite `hb` using `[τ.apply_symm_apply]`.

Simplify using `only [Set.mem_preimage, Set.mem_compl_iff, Set.mem_inter_iff, Set.mem_singleton_iff, hb, hx]`. Use `show ((fib (τ.symm b)).map e) _ = 0`. Rewrite using `[hemb.map_apply, hset]`. Conclude with `h1 _`. Introduce `φ hφ`.

Establish `hr : (μ.map e).restrict U = (μ.restrict U).map e`. Use `hemb.restrict_map μ U` as an intermediate fact. Rewrite `this` using `[hU]`. Then use the resulting hypothesis. Rewrite using `[hr, hemb.lintegral_map, h2 (fun v => φ (e v)) (hφ.comp e.measurable), hτ.lintegral_map]`. Use `lintegral_congr fun b => ?_` and prove the remaining obligations.

Simplify using `only [τ.symm_apply_apply, hemb.lintegral_map, Function.comp]`. Introduce `φ hφ hcs hts`. Establish `hts' : tsupport (φ ∘ e) ⊆ U`. Rewrite using `[tsupport_comp_eq_preimage]`. Introduce `x hx`.

Conclude with `(Set.ext_iff.1 hU x).1 (hts hx)`. Take `⟨hi, hcont⟩` from `h3 (φ ∘ e) (hφ.comp e.continuous) (hcs.comp_isClosedEmbedding e.isClosedEmbedding) hts'`. Use `⟨fun b _ => ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[hemb.integrable_map_iff]`. Conclude with `hi _ (Set.mem_univ _)`.

Establish `: (fun b => ∫ v, φ v ∂((fib (τ.symm b)).map e)) = (fun b => ∫ v, (φ ∘ e) v ∂(fib b)) ∘ τ.symm`. Use function extensionality and compare the values at `b`. Conclude with `hemb.integral_map φ`. Rewrite using `[this]`. Conclude with `hcont.comp τ.symm.continuous.continuousOn (fun _ _ => Set.mem_univ _)`.
-/
theorem transport_univ {V X Y : Type} [TopologicalSpace V] [MeasurableSpace V] [BorelSpace V]
    [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X] (μ : Measure V) (ν : Measure X) (f : V → Y)
    (ι : X → Y) (U : Set V) (e : V ≃ₜ V) (τ : X ≃ₜ X) (fib : X → Measure V)
    (h : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsFibreFamily μ f ι U ν Set.univ fib)
    (hf : ∀ x b, f (e x) = ι (τ b) ↔ f x = ι b) (hU : e ⁻¹' U = U) :
    Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsFibreFamily (μ.map e) f ι U (ν.map τ) Set.univ
      (fun b => (fib (τ.symm b)).map e) := by
  obtain ⟨h1, h2, h3⟩ := h
  have hemb : MeasurableEmbedding e := e.measurableEmbedding
  have hτ : MeasurableEmbedding τ := τ.measurableEmbedding
  refine ⟨?_, ?_, ?_⟩
  · intro b
    have hset : e ⁻¹' (f ⁻¹' {ι b} ∩ U)ᶜ = (f ⁻¹' {ι (τ.symm b)} ∩ U)ᶜ := by
      ext x
      have hx : e x ∈ U ↔ x ∈ U := Set.ext_iff.1 hU x
      have hb := hf x (τ.symm b)
      rw [τ.apply_symm_apply] at hb
      simp only [Set.mem_preimage, Set.mem_compl_iff, Set.mem_inter_iff, Set.mem_singleton_iff, hb, hx]
    show ((fib (τ.symm b)).map e) _ = 0
    rw [hemb.map_apply, hset]
    exact h1 _
  · intro φ hφ
    have hr : (μ.map e).restrict U = (μ.restrict U).map e := by
      have := hemb.restrict_map μ U
      rwa [hU] at this
    rw [hr, hemb.lintegral_map, h2 (fun v => φ (e v)) (hφ.comp e.measurable), hτ.lintegral_map]
    refine lintegral_congr fun b => ?_
    simp only [τ.symm_apply_apply, hemb.lintegral_map, Function.comp]
  · intro φ hφ hcs hts
    have hts' : tsupport (φ ∘ e) ⊆ U := by
      rw [tsupport_comp_eq_preimage]
      intro x hx
      exact (Set.ext_iff.1 hU x).1 (hts hx)
    obtain ⟨hi, hcont⟩ := h3 (φ ∘ e) (hφ.comp e.continuous)
      (hcs.comp_isClosedEmbedding e.isClosedEmbedding) hts'
    refine ⟨fun b _ => ?_, ?_⟩
    · rw [hemb.integrable_map_iff]
      exact hi _ (Set.mem_univ _)
    · have : (fun b => ∫ v, φ v ∂((fib (τ.symm b)).map e))
          = (fun b => ∫ v, (φ ∘ e) v ∂(fib b)) ∘ τ.symm := by
        funext b
        exact hemb.integral_map φ
      rw [this]
      exact hcont.comp τ.symm.continuous.continuousOn (fun _ _ => Set.mem_univ _)

section Loc

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

/- English proof (translation)
Take `⟨hTR, hLC, hSC, hT2, -⟩` from `id hR`. Use `haveI := hTR`. Use `haveI := hLC`. Use `haveI := hSC`. Use `haveI := hT2`.

Take `⟨hTK, hLK, hSK, hTK2, -, -, -, hBor, -, -⟩` from `GlobalTheory.CompanionTheory.SW.TopK.topTens_props F E σ hσ R`. Use `haveI := hTK`. Use `haveI := hLK`. Use `haveI := hSK`. Use `haveI := hTK2`.

Use `haveI := hBor n M`. Take `⟨hLH, hSH, hT2H, hBH, hG⟩` from `GlobalTheory.CompanionTheory.SW.HermTop.herm_top F E σ hσ R n`. Use `haveI := hLH`. Use `haveI := hSH`. Use `haveI := hT2H`.

Use `haveI := hBH`. Take `⟨G, hGc, hGe⟩` from `hG M J hJ`. Take `⟨halg, hcomp, hone, hmem, -⟩` from `GlobalTheory.CompanionTheory.SW.GramAlg.gram_algebra F E σ hσ M J hJ R n`. Establish `hg1 : g * g⁻¹ = 1` using `Matrix.mul_nonsing_inv g hg`. Establish `hg2 : g⁻¹ * g = 1` using `Matrix.nonsing_inv_mul g hg`.

Establish `hrc : ∀ h : Matrix (Fin n) (Fin n) (R ⊗[F] E), Continuous fun X : Fin n → Fin M → R ⊗[F] E => rmul R X h`. Introduce `h`. Use `continuous_pi fun b => continuous_pi fun i => ?_` and prove the remaining obligations. Simplify using `only [rmul]`. Use `continuous_finset_sum _ fun k _ => ?_` and prove the remaining obligations.

Establish `h1 : Continuous fun Y : Fin n → Fin M → R ⊗[F] E => Y k i` using `(continuous_apply i).comp (continuous_apply k)`. Conclude with `h1.mul continuous_const`. Set `e : (Fin n → Fin M → R ⊗[F] E) ≃ₜ (Fin n → Fin M → R ⊗[F] E)` to `{ toFun := fun X => rmul R X g invFun := fun X => rmul R X g⁻¹ left_inv := fun X => by simp only [hcomp, hg1, hone] right_inv := fun X => by simp only [hcomp, hg2, hone] continuous_toFun := hrc g continuous_invFun := hrc g⁻¹ }`. Establish `hc1 : cT (sigR R σ) (1 : Matrix (Fin n) (Fin n) (R ⊗[F] E)) = 1`. Unfold `cT`.

Rewrite using `[Matrix.map_one _ (map_zero _) (map_one _), Matrix.transpose_one]`. Establish `key : ∀ (h h' A : Matrix (Fin n) (Fin n) (R ⊗[F] E)), h * h' = 1 → cT (sigR R σ) h' * (cT (sigR R σ) h * A * h) * h' = A`. Introduce `h h' A hh`. Establish `h1 : cT (sigR R σ) h' * cT (sigR R σ) h = 1`. Rewrite using `[← cT_mul, hh, hc1]`.

Combine the equalities or inequalities in the displayed calculation. Simplify using `only [Matrix.mul_assoc]`. Use `_ = A := by rw [h1, hh, Matrix.one_mul, Matrix.mul_one]`. Set `τ' : HermR R σ n → HermR R σ n` to `fun S => ⟨cT (sigR R σ) g⁻¹ * (S : Matrix (Fin n) (Fin n) (R ⊗[F] E)) * g⁻¹, hmem S g⁻¹⟩`. Establish `hcj : ∀ h : Matrix (Fin n) (Fin n) (R ⊗[F] E), Continuous fun S : HermR R σ n => cT (sigR R σ) h * (S : Matrix (Fin n) (Fin n) (R ⊗[F] E)) * h` using `fun h => (continuous_const.matrix_mul continuous_subtype_val).matrix_mul continuous_const`.

Set `τh : HermR R σ n ≃ₜ HermR R σ n` to `{ toFun := τ invFun := τ' left_inv := fun S => Subtype.ext (by show cT (sigR R σ) g⁻¹ * ((τ S : HermR R σ n) : Matrix (Fin n) (Fin n) (R ⊗[F] E)) * g⁻¹ = S`. Rewrite using `[hτ]`. Conclude with `key _ _ _ hg1)`. Use `right_inv := fun S => Subtype.ext (by`. Rewrite using `[hτ]`.

Conclude with `key _ _ _ hg2)`. Use `continuous_toFun := by`. Use `Topology.IsInducing.subtypeVal.continuous_iff.2 ?_` and prove the remaining obligations. Conclude with `(hcj g).congr fun S => (hτ S).symm`. Use `continuous_invFun := (hcj g⁻¹).subtype_mk _ }`.

Establish `hcomm : ∀ X, G (e X) = τh (G X)`. Introduce `X`. Apply `Subtype.ext` to reduce the goal to its premises. Use `show ((G (rmul R X g) : HermR R σ n) : Matrix (Fin n) (Fin n) (R ⊗[F] E)) = ((τ (G X) : HermR R σ n) : Matrix (Fin n) (Fin n) (R ⊗[F] E))`. Rewrite using `[← hGe, hτ, ← hGe]`.

Conclude with `halg X g`. Establish `hU : e ⁻¹' {X | LinearIndependent (R ⊗[F] E) X} = {X | LinearIndependent (R ⊗[F] E) X}`. Use extensionality with `X`. Prove the components needed by the constructor for the conclusion. Introduce `hX`.

Establish `h1 : LinearIndependent (R ⊗[F] E) (rmul R X g)` using `hX`. Establish `h2` using `linInd_mul (rmul R X g) g⁻¹ g hg1 h1`. Establish `h3 : rmul R (rmul R X g) g⁻¹ = X` using `by simp only [hcomp, hg1, hone]`. Establish `h4 : (fun (a : Fin n) (i : Fin M) => ∑ c, rmul R X g c i * g⁻¹ c a) = X` using `h3`. Rewrite `h2` using `[h4]`.

Conclude with `h2`. Introduce `hX`. Conclude with `linInd_mul X g g⁻¹ hg2 hX`. Establish `hf : ∀ (X : Fin n → Fin M → R ⊗[F] E) (b : HermR R σ n), gramR R σ J (e X) = ((τh b : HermR R σ n) : Matrix (Fin n) (Fin n) (R ⊗[F] E)) ↔ gramR R σ J X = (b : Matrix (Fin n) (Fin n) (R ⊗[F] E))`. Introduce `X b`.

Rewrite using `[hGe (e X), hGe X, hcomm, Subtype.val_inj, Subtype.val_inj, τh.injective.eq_iff]`. Establish `htr` using `transport_univ μ ν (gramR R σ J) Subtype.val _ e τh m hm hf hU`. Establish `hmu' : μ.map e = a • μ` using `hmu`. Establish `hnu' : ν.map τh = c • ν` using `hnu`. Rewrite `htr` using `[hmu', hnu']`.

Establish `ha0 : a ≠ 0`. Introduce and unpack `rfl`. Establish `h0 : μ.map e = 0` using `by rw [hmu', zero_smul]`. Establish `h1 : (μ.map e) Set.univ = μ Set.univ`. Rewrite using `[e.measurableEmbedding.map_apply, Set.preimage_univ]`.

Rewrite `h1` using `[h0]`. Conclude with `(isOpen_univ.measure_pos μ Set.univ_nonempty).ne h1`. Establish `hc0 : c ≠ 0`. Introduce and unpack `rfl`. Establish `h0 : ν.map τh = 0` using `by rw [hnu', zero_smul]`.

Establish `h1 : (ν.map τh) Set.univ = ν Set.univ`. Rewrite using `[τh.measurableEmbedding.map_apply, Set.preimage_univ]`. Rewrite `h1` using `[h0]`. Conclude with `(isOpen_univ.measure_pos ν Set.univ_nonempty).ne h1`. Use `haveI hμa : (a • μ).IsAddHaarMeasure := Measure.IsAddHaarMeasure.nnreal_smul μ ha0`.

Use `haveI hνc : (c • ν).IsAddHaarMeasure := Measure.IsAddHaarMeasure.nnreal_smul ν hc0`. Establish `hres` using `GlobalTheory.CompanionTheory.SW.Rescale.isFibreFamily_rescale _ _ _ μ ν _ _ _ _ m hm a c hc0`. Establish `huq` using `PI.AprimeInfW.FU.fib_eq hres htr hGc hGe Subtype.val_injective hfree`. Establish `h5` using `congrFun huq (τ S)`. Establish `hs : τh.symm (τ S) = S` using `τh.symm_apply_apply S`.

Simplify using `only [hs] at h5`. Establish `hfin : (m S).map (fun X => rmul R X g) = (a / c) • m (τ S)` using `h5.symm`. Rewrite using `[hfin, smul_smul, mul_div_cancel₀ a hc0]`.
-/
theorem free_rmul (σ : E →ₐ[F] E) (hσ : IsCMExt F E σ) {M : ℕ} (J : Matrix (Fin M) (Fin M) E)
    (hJ : IsHermND σ J) (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [MeasurableSpace R]
    [BorelSpace R] (hR : IsLocR R) (n : ℕ) (μ : Measure (Fin n → Fin M → R ⊗[F] E))
    (ν : Measure (HermR R σ n)) (m : HermR R σ n → Measure (Fin n → Fin M → R ⊗[F] E))
    (hμ : μ.IsAddHaarMeasure) (hν : ν.IsAddHaarMeasure) (hm : IsGramFibFree R σ J n μ ν m)
    (hfree : IsOpen {X : Fin n → Fin M → R ⊗[F] E | LinearIndependent (R ⊗[F] E) X})
    (g : Matrix (Fin n) (Fin n) (R ⊗[F] E)) (hg : IsUnit g.det) (τ : HermR R σ n → HermR R σ n)
    (hτ : ∀ S, (τ S : Matrix (Fin n) (Fin n) (R ⊗[F] E)) = cT (sigR R σ) g * S * g) (a c : ℝ≥0)
    (hmu : μ.map (fun X => rmul R X g) = a • μ) (hnu : ν.map τ = c • ν) (S : HermR R σ n) :
    a • m (τ S) = c • (m S).map (fun X => rmul R X g) := by
  obtain ⟨hTR, hLC, hSC, hT2, -⟩ := id hR
  haveI := hTR
  haveI := hLC
  haveI := hSC
  haveI := hT2
  obtain ⟨hTK, hLK, hSK, hTK2, -, -, -, hBor, -, -⟩ := GlobalTheory.CompanionTheory.SW.TopK.topTens_props F E σ hσ R
  haveI := hTK
  haveI := hLK
  haveI := hSK
  haveI := hTK2
  haveI := hBor n M
  obtain ⟨hLH, hSH, hT2H, hBH, hG⟩ := GlobalTheory.CompanionTheory.SW.HermTop.herm_top F E σ hσ R n
  haveI := hLH
  haveI := hSH
  haveI := hT2H
  haveI := hBH
  obtain ⟨G, hGc, hGe⟩ := hG M J hJ
  obtain ⟨halg, hcomp, hone, hmem, -⟩ := GlobalTheory.CompanionTheory.SW.GramAlg.gram_algebra F E σ hσ M J hJ R n
  have hg1 : g * g⁻¹ = 1 := Matrix.mul_nonsing_inv g hg
  have hg2 : g⁻¹ * g = 1 := Matrix.nonsing_inv_mul g hg
  have hrc : ∀ h : Matrix (Fin n) (Fin n) (R ⊗[F] E),
      Continuous fun X : Fin n → Fin M → R ⊗[F] E => rmul R X h := by
    intro h
    refine continuous_pi fun b => continuous_pi fun i => ?_
    simp only [rmul]
    refine continuous_finset_sum _ fun k _ => ?_
    have h1 : Continuous fun Y : Fin n → Fin M → R ⊗[F] E => Y k i :=
      (continuous_apply i).comp (continuous_apply k)
    exact h1.mul continuous_const
  let e : (Fin n → Fin M → R ⊗[F] E) ≃ₜ (Fin n → Fin M → R ⊗[F] E) :=
    { toFun := fun X => rmul R X g
      invFun := fun X => rmul R X g⁻¹
      left_inv := fun X => by simp only [hcomp, hg1, hone]
      right_inv := fun X => by simp only [hcomp, hg2, hone]
      continuous_toFun := hrc g
      continuous_invFun := hrc g⁻¹ }
  have hc1 : cT (sigR R σ) (1 : Matrix (Fin n) (Fin n) (R ⊗[F] E)) = 1 := by
    unfold cT
    rw [Matrix.map_one _ (map_zero _) (map_one _), Matrix.transpose_one]
  have key : ∀ (h h' A : Matrix (Fin n) (Fin n) (R ⊗[F] E)), h * h' = 1 →
      cT (sigR R σ) h' * (cT (sigR R σ) h * A * h) * h' = A := by
    intro h h' A hh
    have h1 : cT (sigR R σ) h' * cT (sigR R σ) h = 1 := by
      rw [← cT_mul, hh, hc1]
    calc cT (sigR R σ) h' * (cT (sigR R σ) h * A * h) * h'
        = (cT (sigR R σ) h' * cT (sigR R σ) h) * A * (h * h') := by
          simp only [Matrix.mul_assoc]
      _ = A := by rw [h1, hh, Matrix.one_mul, Matrix.mul_one]
  let τ' : HermR R σ n → HermR R σ n := fun S =>
    ⟨cT (sigR R σ) g⁻¹ * (S : Matrix (Fin n) (Fin n) (R ⊗[F] E)) * g⁻¹, hmem S g⁻¹⟩
  have hcj : ∀ h : Matrix (Fin n) (Fin n) (R ⊗[F] E), Continuous fun S : HermR R σ n =>
      cT (sigR R σ) h * (S : Matrix (Fin n) (Fin n) (R ⊗[F] E)) * h := fun h =>
    (continuous_const.matrix_mul continuous_subtype_val).matrix_mul continuous_const
  let τh : HermR R σ n ≃ₜ HermR R σ n :=
    { toFun := τ
      invFun := τ'
      left_inv := fun S => Subtype.ext (by
        show cT (sigR R σ) g⁻¹ * ((τ S : HermR R σ n) : Matrix (Fin n) (Fin n) (R ⊗[F] E)) * g⁻¹ = S
        rw [hτ]
        exact key _ _ _ hg1)
      right_inv := fun S => Subtype.ext (by
        rw [hτ]
        exact key _ _ _ hg2)
      continuous_toFun := by
        refine Topology.IsInducing.subtypeVal.continuous_iff.2 ?_
        exact (hcj g).congr fun S => (hτ S).symm
      continuous_invFun := (hcj g⁻¹).subtype_mk _ }
  have hcomm : ∀ X, G (e X) = τh (G X) := by
    intro X
    apply Subtype.ext
    show ((G (rmul R X g) : HermR R σ n) : Matrix (Fin n) (Fin n) (R ⊗[F] E)) =
      ((τ (G X) : HermR R σ n) : Matrix (Fin n) (Fin n) (R ⊗[F] E))
    rw [← hGe, hτ, ← hGe]
    exact halg X g
  have hU : e ⁻¹' {X | LinearIndependent (R ⊗[F] E) X} = {X | LinearIndependent (R ⊗[F] E) X} := by
    ext X
    constructor
    · intro hX
      have h1 : LinearIndependent (R ⊗[F] E) (rmul R X g) := hX
      have h2 := linInd_mul (rmul R X g) g⁻¹ g hg1 h1
      have h3 : rmul R (rmul R X g) g⁻¹ = X := by simp only [hcomp, hg1, hone]
      have h4 : (fun (a : Fin n) (i : Fin M) => ∑ c, rmul R X g c i * g⁻¹ c a) = X := h3
      rw [h4] at h2
      exact h2
    · intro hX
      exact linInd_mul X g g⁻¹ hg2 hX
  have hf : ∀ (X : Fin n → Fin M → R ⊗[F] E) (b : HermR R σ n),
      gramR R σ J (e X) = ((τh b : HermR R σ n) : Matrix (Fin n) (Fin n) (R ⊗[F] E)) ↔
        gramR R σ J X = (b : Matrix (Fin n) (Fin n) (R ⊗[F] E)) := by
    intro X b
    rw [hGe (e X), hGe X, hcomm, Subtype.val_inj, Subtype.val_inj, τh.injective.eq_iff]
  have htr := transport_univ μ ν (gramR R σ J) Subtype.val _ e τh m hm hf hU
  have hmu' : μ.map e = a • μ := hmu
  have hnu' : ν.map τh = c • ν := hnu
  rw [hmu', hnu'] at htr
  have ha0 : a ≠ 0 := by
    rintro rfl
    have h0 : μ.map e = 0 := by rw [hmu', zero_smul]
    have h1 : (μ.map e) Set.univ = μ Set.univ := by
      rw [e.measurableEmbedding.map_apply, Set.preimage_univ]
    rw [h0] at h1
    exact (isOpen_univ.measure_pos μ Set.univ_nonempty).ne h1
  have hc0 : c ≠ 0 := by
    rintro rfl
    have h0 : ν.map τh = 0 := by rw [hnu', zero_smul]
    have h1 : (ν.map τh) Set.univ = ν Set.univ := by
      rw [τh.measurableEmbedding.map_apply, Set.preimage_univ]
    rw [h0] at h1
    exact (isOpen_univ.measure_pos ν Set.univ_nonempty).ne h1
  haveI hμa : (a • μ).IsAddHaarMeasure := Measure.IsAddHaarMeasure.nnreal_smul μ ha0
  haveI hνc : (c • ν).IsAddHaarMeasure := Measure.IsAddHaarMeasure.nnreal_smul ν hc0
  have hres := GlobalTheory.CompanionTheory.SW.Rescale.isFibreFamily_rescale _ _ _ μ ν _ _ _ _ m hm a c hc0
  have huq := PI.AprimeInfW.FU.fib_eq hres htr hGc hGe Subtype.val_injective hfree
  have h5 := congrFun huq (τ S)
  have hs : τh.symm (τ S) = S := τh.symm_apply_apply S
  simp only [hs] at h5
  have hfin : (m S).map (fun X => rmul R X g) = (a / c) • m (τ S) := h5.symm
  rw [hfin, smul_smul, mul_div_cancel₀ a hc0]

end Loc

section Lat

variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E]

def scaleB {d : ℕ} (b : Module.Basis (Fin d) F E) (c : F) (hc : c ≠ 0) : Module.Basis (Fin d) F E :=
  b.unitsSMul (fun _ => (Units.mk0 c hc)⁻¹)

omit [NumberField F] in

/- English proof (translation)
Proceed by induction on `y using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `tmul r e`. Establish `h : (scaleB b c hc).repr e k = c * b.repr e k`. Simplify using `[scaleB, Module.Basis.repr_unitsSMul]`.

Simplify using `only [Algebra.TensorProduct.basis_repr_tmul, Finsupp.smul_apply, Finsupp.mapRange_apply, h, map_mul, smul_eq_mul]`. Expand and normalize the polynomial expressions, which then agree. Consider the case `add x y hx hy => simp only [map_add, Finsupp.add_apply, hx, hy, mul_add]`.
-/
theorem repr_scaleB {d : ℕ} (b : Module.Basis (Fin d) F E) (c : F) (hc : c ≠ 0) (R : Type) [CommRing R]
    [Algebra F R] (y : R ⊗[F] E) (k : Fin d) :
    (Algebra.TensorProduct.basis R (scaleB b c hc)).repr y k =
      algebraMap F R c * (Algebra.TensorProduct.basis R b).repr y k := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul r e =>
    have h : (scaleB b c hc).repr e k = c * b.repr e k := by
      simp [scaleB, Module.Basis.repr_unitsSMul]
    simp only [Algebra.TensorProduct.basis_repr_tmul, Finsupp.smul_apply, Finsupp.mapRange_apply, h,
      map_mul, smul_eq_mul]
    ring
  | add x y hx hy => simp only [map_add, Finsupp.add_apply, hx, hy, mul_add]

/- English proof (translation)
Set `s : Finset F` to `Finset.univ.image (fun p : Fin n × Fin n × Fin d × Fin d => b.repr (b p.2.2.1 * G p.1 p.2.1) p.2.2.2)`. Take `⟨c, hc⟩` from `IsLocalization.exist_integer_multiples_of_finset (nonZeroDivisors (𝓞 F)) s`. Use `⟨algebraMap (𝓞 F) F c, ?_, fun v i j k l => ?_⟩` and prove the remaining obligations. Conclude with `IsLocalization.to_map_ne_zero_of_mem_nonZeroDivisors F le_rfl c.2`. Take `⟨r, hr⟩` from `hc (b.repr (b k * G i j) l) (Finset.mem_image.2 ⟨(i, j, k, l), Finset.mem_univ _, rfl⟩)`.

Establish `h1 : algebraMap (𝓞 F) F c * b.repr (b k * G i j) l = algebraMap (𝓞 F) F r`. Rewrite using `[hr, Algebra.smul_def]`. Establish `h2 : Valued.v (algebraMap F (Fv F v) (algebraMap (𝓞 F) F r)) = v.valuation F (algebraMap (𝓞 F) F r)` using `HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v _`. Rewrite using `[h1, HeightOneSpectrum.mem_adicCompletionIntegers, h2]`. Conclude with `v.valuation_le_one r`.
-/
theorem exists_den {d n : ℕ} (b : Module.Basis (Fin d) F E) (G : Matrix (Fin n) (Fin n) E) :
    ∃ c : F, c ≠ 0 ∧ ∀ (v : HeightOneSpectrum (𝓞 F)) (i j : Fin n) (k l : Fin d),
      algebraMap F (Fv F v) (c * b.repr (b k * G i j) l) ∈ v.adicCompletionIntegers F := by
  classical
  let s : Finset F := Finset.univ.image
    (fun p : Fin n × Fin n × Fin d × Fin d => b.repr (b p.2.2.1 * G p.1 p.2.1) p.2.2.2)
  obtain ⟨c, hc⟩ := IsLocalization.exist_integer_multiples_of_finset (nonZeroDivisors (𝓞 F)) s
  refine ⟨algebraMap (𝓞 F) F c, ?_, fun v i j k l => ?_⟩
  · exact IsLocalization.to_map_ne_zero_of_mem_nonZeroDivisors F le_rfl c.2
  · obtain ⟨r, hr⟩ := hc (b.repr (b k * G i j) l)
      (Finset.mem_image.2 ⟨(i, j, k, l), Finset.mem_univ _, rfl⟩)
    have h1 : algebraMap (𝓞 F) F c * b.repr (b k * G i j) l = algebraMap (𝓞 F) F r := by
      rw [hr, Algebra.smul_def]
    have h2 : Valued.v (algebraMap F (Fv F v) (algebraMap (𝓞 F) F r)) = v.valuation F (algebraMap (𝓞 F) F r) :=
      HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v _
    rw [h1, HeightOneSpectrum.mem_adicCompletionIntegers, h2]
    exact v.valuation_le_one r

/- English proof (translation)
Introduce `a i l`. Use `show (Algebra.TensorProduct.basis (Fv F v) (scaleB b c hc)).repr (rmul (Fv F v) X (G.map (inclR (Fv F v))) a i) l ∈ v.adicCompletionIntegers F`. Rewrite using `[repr_scaleB]`. Simplify using `only [rmul, Matrix.map_apply]`. Rewrite using `[map_sum, Finsupp.finsetSum_apply, Finset.mul_sum]`.

Use `sum_mem fun c' _ => ?_` and prove the remaining obligations. Rewrite using `[LatRat.repr_mul, Finset.mul_sum]`. Use `sum_mem fun k _ => ?_` and prove the remaining obligations. Establish `h : algebraMap F (Fv F v) c * ((Algebra.TensorProduct.basis (Fv F v) b).repr (X c' i) k * algebraMap F (Fv F v) (b.repr (b k * G c' a) l)) = (Algebra.TensorProduct.basis (Fv F v) b).repr (X c' i) k * algebraMap F (Fv F v) (c * b.repr (b k * G c' a) l)`. Rewrite using `[map_mul (algebraMap F (Fv F v))]`.

Expand and normalize the polynomial expressions, which then agree. Rewrite using `[h]`. Conclude with `mul_mem (hX c' i k) (hden c' a k l)`.
-/
theorem rmul_mem_scaleB {d M n : ℕ} (b : Module.Basis (Fin d) F E) (c : F) (hc : c ≠ 0)
    (G : Matrix (Fin n) (Fin n) E) (v : HeightOneSpectrum (𝓞 F))
    (hden : ∀ (i j : Fin n) (k l : Fin d),
      algebraMap F (Fv F v) (c * b.repr (b k * G i j) l) ∈ v.adicCompletionIntegers F)
    {X : Fin n → Fin M → Fv F v ⊗[F] E} (hX : X ∈ latV b v) :
    rmul (Fv F v) X (G.map (inclR (Fv F v))) ∈ latV (scaleB b c hc) v := by
  intro a i l
  show (Algebra.TensorProduct.basis (Fv F v) (scaleB b c hc)).repr
    (rmul (Fv F v) X (G.map (inclR (Fv F v))) a i) l ∈ v.adicCompletionIntegers F
  rw [repr_scaleB]
  simp only [rmul, Matrix.map_apply]
  rw [map_sum, Finsupp.finsetSum_apply, Finset.mul_sum]
  refine sum_mem fun c' _ => ?_
  rw [LatRat.repr_mul, Finset.mul_sum]
  refine sum_mem fun k _ => ?_
  have h : algebraMap F (Fv F v) c * ((Algebra.TensorProduct.basis (Fv F v) b).repr (X c' i) k *
      algebraMap F (Fv F v) (b.repr (b k * G c' a) l)) =
      (Algebra.TensorProduct.basis (Fv F v) b).repr (X c' i) k *
        algebraMap F (Fv F v) (c * b.repr (b k * G c' a) l) := by
    rw [map_mul (algebraMap F (Fv F v))]
    ring
  rw [h]
  exact mul_mem (hX c' i k) (hden c' a k l)

end Lat

section Resc

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

/- English proof (translation)
Take `⟨hTR, hLC, hSC, hT2, -⟩` from `id hR`. Use `haveI := hTR`. Use `haveI := hLC`. Use `haveI := hSC`. Use `haveI := hT2`.

Take `⟨hTK, hLK, hSK, hTK2, -, -, -, hBor, -, -⟩` from `GlobalTheory.CompanionTheory.SW.TopK.topTens_props F E σ hcm R`. Use `haveI := hTK`. Use `haveI := hLK`. Use `haveI := hSK`. Use `haveI := hTK2`.

Use `haveI := hBor n M`. Take `⟨hLH, hSH, hT2H, hBH, -⟩` from `GlobalTheory.CompanionTheory.SW.HermTop.herm_top F E σ hcm R n`. Use `haveI := hLH`. Use `haveI := hSH`. Use `haveI := hT2H`.

Use `haveI := hBH`. Take `⟨-, hW, hH⟩` from `coord_measures_haar F E σ hcm R d b lam hlam`. Take `⟨-, hW', hH'⟩` from `coord_measures_haar F E σ hcm R d b' lam hlam`. Use `haveI := hW n M`. Use `haveI := hW' n M`.

Use `haveI := hH n`. Use `haveI := hH' n`. Take `⟨c1, hc1, e1⟩ : ∃ c : ℝ≥0, c ≠ 0 ∧ coordW R b' lam n M = c • coordW R b lam n M` from `⟨_, (Measure.addHaarScalarFactor_pos_of_isAddHaarMeasure _ _).ne', Measure.isAddLeftInvariant_eq_smul _ _⟩`. Take `⟨c2, hc2, e2⟩ : ∃ c : ℝ≥0, c ≠ 0 ∧ coordHerm R σ b' lam n = c • coordHerm R σ b lam n` from `⟨_, (Measure.addHaarScalarFactor_pos_of_isAddHaarMeasure _ _).ne', Measure.isAddLeftInvariant_eq_smul _ _⟩`. Use `⟨c1 / c2, div_ne_zero hc1 hc2, ?_⟩` and prove the remaining obligations.

Rewrite using `[e1, e2]`. Conclude with `GlobalTheory.CompanionTheory.SW.Rescale.isFibreFamily_rescale _ _ _ _ _ _ _ _ _ m hm c1 c2 hc2`.
-/
theorem coord_rescale (σ : E →ₐ[F] E) (hcm : IsCMExt F E σ) {M : ℕ} (J : Matrix (Fin M) (Fin M) E)
    (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [MeasurableSpace R] [BorelSpace R]
    (hR : IsLocR R) {d : ℕ} (b b' : Module.Basis (Fin d) F E) (lam : Measure R)
    (hlam : lam.IsAddHaarMeasure) (n : ℕ) (m : HermR R σ n → Measure (Fin n → Fin M → R ⊗[F] E))
    (hm : IsGramFibFree R σ J n (coordW R b lam n M) (coordHerm R σ b lam n) m) :
    ∃ k : ℝ≥0, k ≠ 0 ∧
      IsGramFibFree R σ J n (coordW R b' lam n M) (coordHerm R σ b' lam n) (fun S => k • m S) := by
  obtain ⟨hTR, hLC, hSC, hT2, -⟩ := id hR
  haveI := hTR
  haveI := hLC
  haveI := hSC
  haveI := hT2
  obtain ⟨hTK, hLK, hSK, hTK2, -, -, -, hBor, -, -⟩ := GlobalTheory.CompanionTheory.SW.TopK.topTens_props F E σ hcm R
  haveI := hTK
  haveI := hLK
  haveI := hSK
  haveI := hTK2
  haveI := hBor n M
  obtain ⟨hLH, hSH, hT2H, hBH, -⟩ := GlobalTheory.CompanionTheory.SW.HermTop.herm_top F E σ hcm R n
  haveI := hLH
  haveI := hSH
  haveI := hT2H
  haveI := hBH
  obtain ⟨-, hW, hH⟩ := coord_measures_haar F E σ hcm R d b lam hlam
  obtain ⟨-, hW', hH'⟩ := coord_measures_haar F E σ hcm R d b' lam hlam
  haveI := hW n M
  haveI := hW' n M
  haveI := hH n
  haveI := hH' n
  obtain ⟨c1, hc1, e1⟩ : ∃ c : ℝ≥0, c ≠ 0 ∧ coordW R b' lam n M = c • coordW R b lam n M :=
    ⟨_, (Measure.addHaarScalarFactor_pos_of_isAddHaarMeasure _ _).ne',
      Measure.isAddLeftInvariant_eq_smul _ _⟩
  obtain ⟨c2, hc2, e2⟩ : ∃ c : ℝ≥0, c ≠ 0 ∧ coordHerm R σ b' lam n = c • coordHerm R σ b lam n :=
    ⟨_, (Measure.addHaarScalarFactor_pos_of_isAddHaarMeasure _ _).ne',
      Measure.isAddLeftInvariant_eq_smul _ _⟩
  refine ⟨c1 / c2, div_ne_zero hc1 hc2, ?_⟩
  rw [e1, e2]
  exact GlobalTheory.CompanionTheory.SW.Rescale.isFibreFamily_rescale _ _ _ _ _ _ _ _ _ m hm c1 c2 hc2

end Resc

section Main

open GlobalTheory.CompanionTheory.SW.Scale

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

/- English proof (translation)
Take `⟨r1, r2, r3, r4, -, -, r7, -⟩` from `hR`. Establish `hU : IsOpen {r : R | IsUnit r}`. Establish `: {r : R | IsUnit r} = Set.range (Units.val : Rˣ → R)`. Use extensionality with `r`. Both sides reduce to the same expression.

Rewrite using `[this]`. Conclude with `r7.isOpen_range`. Conclude with `PI.VolStabSW.TensAllW.isOpen_linIndep b R hU hL`.
-/
theorem isOpen_free {d : ℕ} (b : Module.Basis (Fin d) F E) [Module.Finite F E] (R : Type) [CommRing R] [Algebra F R]
    [TopologicalSpace R] (hR : IsLocR R) (hL : PI.VolStabSW.TensAllW.LIP R) {n M : ℕ} :
    IsOpen {X : Fin n → Fin M → R ⊗[F] E | LinearIndependent (R ⊗[F] E) X} := by
  obtain ⟨r1, r2, r3, r4, -, -, r7, -⟩ := hR
  have hU : IsOpen {r : R | IsUnit r} := by
    have : {r : R | IsUnit r} = Set.range (Units.val : Rˣ → R) := by
      ext r
      rfl
    rw [this]
    exact r7.isOpen_range
  exact PI.VolStabSW.TensAllW.isOpen_linIndep b R hU hL

/- English proof (translation)
Establish `hR'` using `hR`. Take `⟨r1, r2, r3, r4, -⟩` from `hR'`. Take `⟨-, hW, hHm⟩` from `coord_measures_haar F E σ hcm R d b lam hlam`. Establish `hμ` using `hW n M`. Establish `hν` using `hHm n`.

Establish `hdet : IsUnit (H.map (inclR (F` using `F) R)).det := by`. Establish `h1 : IsUnit ((inclR (F` using `F) R) H.det) := (IsUnit.mk0 _ hH).map (inclR (F := F) R)`. Rewrite `h1` using `[RingHom.map_det]`. Conclude with `h1`. Set `τ` to `tauH R σ hinv (H.map (inclR R))`.

Establish `key` using `free_rmul σ hcm J hJ R hR n _ _ m hμ hν hm hfree (H.map (inclR R)) hdet τ (fun S => rfl) a c (ha _ hμ) (hc' _ hν τ (fun S => rfl)) (hermOf R σ T' hT')`. Establish `hτ : τ (hermOf R σ T' hT') = hermOf R σ T hT` using `tauH_hermOf R σ hinv H T T' hT hT' hrel`. Rewrite `key` using `[hτ]`. Rewrite using `[div_eq_inv_mul, mul_smul, key, inv_smul_smul₀ hc]`.
-/
theorem local_gram_fibration_scaling_free (σ : E →ₐ[F] E) (hcm : IsCMExt F E σ) (hinv : ∀ x, σ (σ x) = x) {M : ℕ}
    (J : Matrix (Fin M) (Fin M) E) (hJ : IsHermND σ J) (R : Type) [CommRing R] [Algebra F R]
    [TopologicalSpace R] [MeasurableSpace R] [BorelSpace R] (hR : IsLocR R) {n d : ℕ}
    (b : Module.Basis (Fin d) F E) (lam : Measure R) (hlam : lam.IsAddHaarMeasure)
    (m : HermR R σ n → Measure (Fin n → Fin M → R ⊗[F] E))
    (hm : IsGramFibFree R σ J n (coordW R b lam n M) (coordHerm R σ b lam n) m)
    (hfree : IsOpen {X : Fin n → Fin M → R ⊗[F] E | LinearIndependent (R ⊗[F] E) X})
    (H T T' : Matrix (Fin n) (Fin n) E) (hH : H.det ≠ 0) (hT : ∀ a b, σ (T b a) = T a b)
    (hT' : ∀ a b, σ (T' b a) = T' a b) (hrel : cT (σ : E →+* E) H * T' * H = T)
    (a c : ℝ≥0) (hc : c ≠ 0)
    (ha : ∀ μ : Measure (Fin n → Fin M → R ⊗[F] E), μ.IsAddHaarMeasure →
      μ.map (fun X => rmul R X (H.map (inclR R))) = a • μ)
    (hc' : ∀ ν : Measure (HermR R σ n), ν.IsAddHaarMeasure → ∀ τ : HermR R σ n → HermR R σ n,
      (∀ S, (τ S : Matrix (Fin n) (Fin n) (R ⊗[F] E)) = cT (sigR R σ) (H.map (inclR R)) *
        (S : Matrix (Fin n) (Fin n) (R ⊗[F] E)) * H.map (inclR R)) → ν.map τ = c • ν) :
    (m (hermOf R σ T' hT')).map (fun X => rmul R X (H.map (inclR R))) =
      (a / c) • m (hermOf R σ T hT) := by
  have hR' := hR
  obtain ⟨r1, r2, r3, r4, -⟩ := hR'
  obtain ⟨-, hW, hHm⟩ := coord_measures_haar F E σ hcm R d b lam hlam
  have hμ := hW n M
  have hν := hHm n
  have hdet : IsUnit (H.map (inclR (F := F) R)).det := by
    have h1 : IsUnit ((inclR (F := F) R) H.det) := (IsUnit.mk0 _ hH).map (inclR (F := F) R)
    rw [RingHom.map_det] at h1
    exact h1
  let τ := tauH R σ hinv (H.map (inclR R))
  have key := free_rmul σ hcm J hJ R hR n _ _ m hμ hν hm hfree (H.map (inclR R)) hdet τ
    (fun S => rfl) a c (ha _ hμ) (hc' _ hν τ (fun S => rfl)) (hermOf R σ T' hT')
  have hτ : τ (hermOf R σ T' hT') = hermOf R σ T hT := tauH_hermOf R σ hinv H T T' hT hT' hrel
  rw [hτ] at key
  rw [div_eq_inv_mul, mul_smul, key, inv_smul_smul₀ hc]

/- English proof (translation)
Use `Measure.ext_of_lintegral _ fun Φ hΦ => ?_` and prove the remaining obligations. Rewrite using `[lintegral_map hΦ he, GlobalTheory.T.siegel_mean_value_nonnegative F E σ hcm M J hJ μ 𝓕 hH hF n _ (fun X => Φ (rmul (AF F) X (H.map (inclR (F := F) (AF F))))) (hΦ.comp he), GlobalTheory.T.siegel_mean_value_nonnegative F E σ hcm M J hJ μ 𝓕 hH hF n _ Φ hΦ]`. Use `congr 1`. Use `lintegral_congr fun h => ?_` and prove the remaining obligations. Set `eqv : (framesE σ J T' : Set (Fin n → Fin M → E)) ≃ (framesE σ J T : Set (Fin n → Fin M → E))` to `{ toFun := fun X => ⟨rE X.1 H, linInd_mul X.1 H G hGH X.2.1, by`.

Establish `hX : gramE σ J X.1 = T'` using `X.2.2`. Rewrite using `[gramE_rE, hX, h1]⟩`. Use `invFun := fun X => ⟨rE X.1 G, linInd_mul X.1 G H hHG X.2.1, by`. Establish `hX : gramE σ J X.1 = T` using `X.2.2`. Rewrite using `[gramE_rE, hX, h2]⟩`.

Use `left_inv := fun X => Subtype.ext (by`. Express the relevant statement in the definitionally equal form `rE (rE X.1 H) G = X.1`. Rewrite using `[rE_rE, hHG, rE_one])`. Use `right_inv := fun X => Subtype.ext (by`. Express the relevant statement in the definitionally equal form `rE (rE X.1 G) H = X.1`.

Rewrite using `[rE_rE, hGH, rE_one]) }`. Rewrite using `[← eqv.tsum_eq (fun X => Φ (actW (AF F) σ J h⁻¹ (ratTup (AF F) (X : Fin n → Fin M → E))))]`. Use `tsum_congr fun X => ?_` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `Φ (rmul (AF F) (actW (AF F) σ J h⁻¹ (ratTup (AF F) X.1)) (H.map (inclR (F := F) (AF F)))) = Φ (actW (AF F) σ J h⁻¹ (ratTup (AF F) (rE X.1 H)))`. Rewrite using `[ratTup_rE]`.

Unfold `actW`. Rewrite using `[(GlobalTheory.T.gram_right_mul_action_laws F E σ hcm (AF F) M n J (ratTup (AF F) X.1) (H.map (inclR (F := F) (AF F))) 1).2.2.2 _]`.
-/
theorem theta_map_free (σ : E →ₐ[F] E) (hcm : IsCMExt F E σ) {M : ℕ} (J : Matrix (Fin M) (Fin M) E)
    (hJ : IsHermND σ J) (μ : Measure (HA (AF F) σ J)) (𝓕 : Set (HA (AF F) σ J))
    (hH : IsHaarH F E σ M J μ) (hF : IsFDH F E σ M J μ 𝓕) {n : ℕ}
    (G H T T' : Matrix (Fin n) (Fin n) E) (hGH : G * H = 1) (hHG : H * G = 1)
    (h1 : cT (σ : E →+* E) H * T' * H = T) (h2 : cT (σ : E →+* E) G * T * G = T')
    (he : Measurable fun X : Fin n → Fin M → AF F ⊗[F] E =>
      rmul (AF F) X (H.map (inclR (F := F) (AF F)))) :
    (thetaMeas σ J μ 𝓕 (framesE σ J T')).map
        (fun X => rmul (AF F) X (H.map (inclR (F := F) (AF F)))) =
      thetaMeas σ J μ 𝓕 (framesE σ J T) := by
  refine Measure.ext_of_lintegral _ fun Φ hΦ => ?_
  rw [lintegral_map hΦ he,
    GlobalTheory.T.siegel_mean_value_nonnegative F E σ hcm M J hJ μ 𝓕 hH hF n _
      (fun X => Φ (rmul (AF F) X (H.map (inclR (F := F) (AF F))))) (hΦ.comp he),
    GlobalTheory.T.siegel_mean_value_nonnegative F E σ hcm M J hJ μ 𝓕 hH hF n _ Φ hΦ]
  congr 1
  refine lintegral_congr fun h => ?_
  let eqv : (framesE σ J T' : Set (Fin n → Fin M → E)) ≃ (framesE σ J T : Set (Fin n → Fin M → E)) :=
    { toFun := fun X => ⟨rE X.1 H, linInd_mul X.1 H G hGH X.2.1, by
        have hX : gramE σ J X.1 = T' := X.2.2
        rw [gramE_rE, hX, h1]⟩
      invFun := fun X => ⟨rE X.1 G, linInd_mul X.1 G H hHG X.2.1, by
        have hX : gramE σ J X.1 = T := X.2.2
        rw [gramE_rE, hX, h2]⟩
      left_inv := fun X => Subtype.ext (by
        change rE (rE X.1 H) G = X.1
        rw [rE_rE, hHG, rE_one])
      right_inv := fun X => Subtype.ext (by
        change rE (rE X.1 G) H = X.1
        rw [rE_rE, hGH, rE_one]) }
  rw [← eqv.tsum_eq (fun X => Φ (actW (AF F) σ J h⁻¹ (ratTup (AF F) (X : Fin n → Fin M → E))))]
  refine tsum_congr fun X => ?_
  change Φ (rmul (AF F) (actW (AF F) σ J h⁻¹ (ratTup (AF F) X.1)) (H.map (inclR (F := F) (AF F)))) =
    Φ (actW (AF F) σ J h⁻¹ (ratTup (AF F) (rE X.1 H)))
  rw [ratTup_rE]
  unfold actW
  rw [(GlobalTheory.T.gram_right_mul_action_laws F E σ hcm (AF F) M n J (ratTup (AF F) X.1)
    (H.map (inclR (F := F) (AF F))) 1).2.2.2 _]

/- English proof (translation)
Introduce `F E _ _ _ _ _ σ hcm M J hJ n T hT g T' hT' hrel hSW d b laminf lam hinf hv μ 𝓕 hH hF minf m hminf hm`. Establish `hinv` using `(HaarCoord.conj_facts hcm).1`. Use `haveI : Module.Finite F E := Module.finite_of_finrank_pos (by rw [hcm.2.2.1]; norm_num)`. Take `⟨G, hG⟩ : ∃ G : Matrix (Fin n) (Fin n) E, G = (g : Matrix (Fin n) (Fin n) E)` from `⟨_, rfl⟩`. Take `⟨H, hHd⟩ : ∃ H : Matrix (Fin n) (Fin n) E, H = ((g⁻¹ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E)` from `⟨_, rfl⟩`.

Establish `hGH : G * H = 1` using `by rw [hG, hHd]; exact Units.mul_inv g`. Establish `hHG : H * G = 1` using `by rw [hG, hHd]; exact Units.inv_mul g`. Rewrite `hrel` using `[← hG]`. Establish `hdetH : H.det ≠ 0`. Introduce `h0`.

Establish `: H.det * G.det = 1` using `by rw [← Matrix.det_mul, hHG, Matrix.det_one]`. Rewrite `this` using `[h0, zero_mul]`. Conclude with `zero_ne_one this`. Establish `hrel' : cT (σ : E →+* E) H * T' * H = T`. Rewrite using `[hrel]`.

Combine the equalities or inequalities in the displayed calculation. Simplify using `only [Matrix.mul_assoc]`. Use `_ = T := by rw [← cT_mul, hGH, cT_one, Matrix.one_mul, Matrix.mul_one]`. Take `⟨ai, a, hau, hai, hav⟩` from `GlobalTheory.T.right_multiplication_euler_product F E σ hcm n M H hdetH`. Take `⟨ci, c, hcu, hci, hcv⟩` from `GlobalTheory.T.hermitian_matrix_euler_product F E σ hcm n H hdetH`.

Take `⟨-, ha0, -, -, hq, -⟩` from `GlobalTheory.T.unit_product_closure_properties F ai ci a c hau hcu`. Take `⟨hci0, hc0, -⟩` from `GlobalTheory.T.unit_product_closure_properties F ci ai c a hcu hau`. Establish `hrI : IsLocR (Ainf F)` using `isLocR_Ainf F hcm.1`. Establish `hrV : ∀ v, IsLocR (Fv F v)` using `fun v => LocFv.isLocR_Fv F v`. Use `haveI : BorelSpace (Ainf F) := ⟨rfl⟩`.

Use `haveI : ∀ v, BorelSpace (Fv F v) := fun _ => ⟨rfl⟩`. Establish `hfI : IsOpen {X : Fin n → Fin M → Ainf F ⊗[F] E | LinearIndependent (Ainf F ⊗[F] E) X}` using `isOpen_free b (Ainf F) hrI (PI.VolStabSW.lip_ainf F)`. Establish `hfV : ∀ v, IsOpen {X : Fin n → Fin M → Fv F v ⊗[F] E | LinearIndependent (Fv F v ⊗[F] E) X}` using `fun v => isOpen_free b (Fv F v) (hrV v) (PI.VolStabSW.TensAllW.lip_field _)`. Establish `sInf` using `local_gram_fibration_scaling_free σ hcm hinv J hJ (Ainf F) hrI b laminf hinf.1 minf hminf hfI H T T' hdetH hT hT' hrel' ai ci hci0 hai hci`. Establish `sV` using `fun v => local_gram_fibration_scaling_free σ hcm hinv J hJ (Fv F v) (hrV v) b (lam v) (hv v).1 (m v) (hm v) (hfV v) H T T' hdetH hT hT' hrel' (a v) (c v) (hc0 v) (hav v) (hcv v)`.

Take `⟨⟨t1, t2, t3⟩, -⟩` from `AdeleTop.adele_top F`. Establish `me` using `measurable_rmul σ hcm (AF F) n M (H.map (inclR (F := F) (AF F)))`. Establish `mi : Measurable fun X : Fin n → Fin M → Ainf F ⊗[F] E => rmul (Ainf F) X (H.map (inclR (F` using `F) (Ainf F))) := by`. Take `⟨r1, r2, r3, r4, -⟩` from `hrI`. Conclude with `measurable_rmul σ hcm (Ainf F) n M _`.

Establish `mv : ∀ v, Measurable fun X : Fin n → Fin M → Fv F v ⊗[F] E => rmul (Fv F v) X (H.map (inclR (F` using `F) (Fv F v))) := by`. Introduce `v`. Take `⟨r1, r2, r3, r4, -⟩` from `hrV v`. Conclude with `measurable_rmul σ hcm (Fv F v) n M _`. Establish `hE` using `hSW d b laminf lam hinf hv μ 𝓕 hH hF minf m hminf hm`.

Establish `hth` using `theta_map_free σ hcm J hJ μ 𝓕 hH hF G H T T' hGH hHG hrel' hrel.symm me`. Establish `hlat` using `(GlobalTheory.T.adelic_tuple_projections F E σ hcm d b n M).2.2.2`. Take `⟨c₀, hc₀, hden⟩` from `exists_den b G`. Take `⟨kinf, -, hkinf⟩` from `coord_rescale σ hcm J (Ainf F) hrI b (scaleB b c₀ hc₀) laminf hinf.1 n minf hminf`. Establish `hkv` using `fun v => coord_rescale σ hcm J (Fv F v) (hrV v) b (scaleB b c₀ hc₀) (lam v) (hv v).1 n (m v) (hm v)`.

Use `choose k hk0 hk using hkv`. Establish `hE'` using `hSW d (scaleB b c₀ hc₀) laminf lam hinf hv μ 𝓕 hH hF (fun S => kinf • minf S) (fun v S => k v • m v S) hkinf hk`. Establish `hfin : ∀ v, m v (hermOf (Fv F v) σ T hT) (latV b v) < ⊤`. Introduce `v`. Take `⟨r1, r2, r3, r4, -⟩` from `id (hrV v)`.

Take `⟨-, -, -, -, -, -, -, hBor, -, -⟩` from `GlobalTheory.CompanionTheory.SW.TopK.topTens_props F E σ hcm (Fv F v)`. Use `haveI := hBor n M`. Establish `hL : MeasurableSet (latV b v : Set (Fin n → Fin M → Fv F v ⊗[F] E))` using `(hlat.1 v).2.measurableSet`. Establish `hs : ∀ (q : ℝ≥0) (ρ : Measure (Fin n → Fin M → Fv F v ⊗[F] E)) (s : Set _), (q • ρ) s = (q : ℝ≥0∞) * ρ s` using `fun q ρ s => by`. Rewrite using `[Measure.smul_apply]`.

Both sides reduce to the same expression. Establish `h1 : (k v • m v (hermOf (Fv F v) σ T' hT')) (latV (scaleB b c₀ hc₀) v) < ⊤` using `hE'.1 v`. Establish `h2 : m v (hermOf (Fv F v) σ T' hT') (latV (scaleB b c₀ hc₀) v) < ⊤`. Assume the negation of the conclusion as `hx`. Rewrite `h1` using `[hs, not_lt_top_iff.1 hx, ENNReal.mul_top (by exact_mod_cast hk0 v)]`.

Conclude with `lt_irrefl _ h1`. Establish `h3 : (fun X : Fin n → Fin M → Fv F v ⊗[F] E => rmul (Fv F v) X (H.map (inclR (F` using `F) (Fv F v)))) ⁻¹' (latV b v) ⊆ latV (scaleB b c₀ hc₀) v := by`. Introduce `X hX`. Establish `h4` using `rmul_mem_scaleB b c₀ hc₀ G v (hden v) hX`. Rewrite `h4` using `[LatRat.rmul_rmul, ← Matrix.map_mul, hHG, Matrix.map_one _ (map_zero _) (map_one _), LatRat.rmul_one]`. Then use the resulting hypothesis.

Establish `e2 : ((m v (hermOf (Fv F v) σ T' hT')).map (fun X => rmul (Fv F v) X (H.map (inclR (F` using `F) (Fv F v))))) (latV b v) = ((a v / c v) • m v (hermOf (Fv F v) σ T hT)) (latV b v) := by rw [sV v]`. Rewrite `e2` using `[Measure.map_apply (mv v) hL, hs]`. Assume the negation of the conclusion as `hx`. Rewrite `e2` using `[not_lt_top_iff.1 hx, ENNReal.mul_top (by exact_mod_cast div_ne_zero (ha0 v) (hc0 v))]`. Establish `h5` using `(measure_mono h3).trans_lt h2`.

Rewrite `h5` using `[e2]`. Conclude with `lt_irrefl _ h5`. Rewrite using `[← hth]`. Conclude with `GlobalTheory.T.euler_product_measure_transport F E σ hcm d b n M _ (minf (hermOf (Ainf F) σ T' hT')) (minf (hermOf (Ainf F) σ T hT)) (fun v => m v (hermOf (Fv F v) σ T' hT')) (fun v => m v (hermOf (Fv F v) σ T hT)) (fun X => rmul (AF F) X (H.map (inclR (F := F) (AF F)))) (fun X = …`.
-/
theorem sw_free_scale : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ (n : ℕ) (T : Matrix (Fin n) (Fin n) E) (hT : ∀ a b, σ (T b a) = T a b) (g : GL (Fin n) E) (T' : Matrix (Fin n) (Fin n) E) (hT' : ∀ a b, σ (T' b a) = T' a b), T' = cT (σ : E →+* E) (g : Matrix (Fin n) (Fin n) E) * T * g → SWFree σ J T' hT' → SWFree σ J T hT := by
  intro F E _ _ _ _ _ σ hcm M J hJ n T hT g T' hT' hrel hSW d b laminf lam hinf hv μ 𝓕 hH hF minf m
    hminf hm
  have hinv := (HaarCoord.conj_facts hcm).1
  haveI : Module.Finite F E := Module.finite_of_finrank_pos (by rw [hcm.2.2.1]; norm_num)
  obtain ⟨G, hG⟩ : ∃ G : Matrix (Fin n) (Fin n) E, G = (g : Matrix (Fin n) (Fin n) E) := ⟨_, rfl⟩
  obtain ⟨H, hHd⟩ : ∃ H : Matrix (Fin n) (Fin n) E, H = ((g⁻¹ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) :=
    ⟨_, rfl⟩
  have hGH : G * H = 1 := by rw [hG, hHd]; exact Units.mul_inv g
  have hHG : H * G = 1 := by rw [hG, hHd]; exact Units.inv_mul g
  rw [← hG] at hrel
  have hdetH : H.det ≠ 0 := by
    intro h0
    have : H.det * G.det = 1 := by rw [← Matrix.det_mul, hHG, Matrix.det_one]
    rw [h0, zero_mul] at this
    exact zero_ne_one this
  have hrel' : cT (σ : E →+* E) H * T' * H = T := by
    rw [hrel]
    calc cT (σ : E →+* E) H * (cT (σ : E →+* E) G * T * G) * H
        = (cT (σ : E →+* E) H * cT (σ : E →+* E) G) * T * (G * H) := by
          simp only [Matrix.mul_assoc]
      _ = T := by rw [← cT_mul, hGH, cT_one, Matrix.one_mul, Matrix.mul_one]
  obtain ⟨ai, a, hau, hai, hav⟩ := GlobalTheory.T.right_multiplication_euler_product F E σ hcm n M H hdetH
  obtain ⟨ci, c, hcu, hci, hcv⟩ := GlobalTheory.T.hermitian_matrix_euler_product F E σ hcm n H hdetH
  obtain ⟨-, ha0, -, -, hq, -⟩ := GlobalTheory.T.unit_product_closure_properties F ai ci a c hau hcu
  obtain ⟨hci0, hc0, -⟩ := GlobalTheory.T.unit_product_closure_properties F ci ai c a hcu hau
  have hrI : IsLocR (Ainf F) := isLocR_Ainf F hcm.1
  have hrV : ∀ v, IsLocR (Fv F v) := fun v => LocFv.isLocR_Fv F v
  haveI : BorelSpace (Ainf F) := ⟨rfl⟩
  haveI : ∀ v, BorelSpace (Fv F v) := fun _ => ⟨rfl⟩
  have hfI : IsOpen {X : Fin n → Fin M → Ainf F ⊗[F] E | LinearIndependent (Ainf F ⊗[F] E) X} :=
    isOpen_free b (Ainf F) hrI (PI.VolStabSW.lip_ainf F)
  have hfV : ∀ v, IsOpen {X : Fin n → Fin M → Fv F v ⊗[F] E | LinearIndependent (Fv F v ⊗[F] E) X} :=
    fun v => isOpen_free b (Fv F v) (hrV v) (PI.VolStabSW.TensAllW.lip_field _)
  have sInf := local_gram_fibration_scaling_free σ hcm hinv J hJ (Ainf F) hrI b laminf hinf.1 minf hminf hfI H T T' hdetH hT
    hT' hrel' ai ci hci0 hai hci
  have sV := fun v => local_gram_fibration_scaling_free σ hcm hinv J hJ (Fv F v) (hrV v) b (lam v) (hv v).1 (m v) (hm v) (hfV v)
    H T T' hdetH hT hT' hrel' (a v) (c v) (hc0 v) (hav v) (hcv v)
  obtain ⟨⟨t1, t2, t3⟩, -⟩ := AdeleTop.adele_top F
  have me := measurable_rmul σ hcm (AF F) n M (H.map (inclR (F := F) (AF F)))
  have mi : Measurable fun X : Fin n → Fin M → Ainf F ⊗[F] E =>
      rmul (Ainf F) X (H.map (inclR (F := F) (Ainf F))) := by
    obtain ⟨r1, r2, r3, r4, -⟩ := hrI
    exact measurable_rmul σ hcm (Ainf F) n M _
  have mv : ∀ v, Measurable fun X : Fin n → Fin M → Fv F v ⊗[F] E =>
      rmul (Fv F v) X (H.map (inclR (F := F) (Fv F v))) := by
    intro v
    obtain ⟨r1, r2, r3, r4, -⟩ := hrV v
    exact measurable_rmul σ hcm (Fv F v) n M _
  have hE := hSW d b laminf lam hinf hv μ 𝓕 hH hF minf m hminf hm
  have hth := theta_map_free σ hcm J hJ μ 𝓕 hH hF G H T T' hGH hHG hrel' hrel.symm me
  have hlat := (GlobalTheory.T.adelic_tuple_projections F E σ hcm d b n M).2.2.2

  obtain ⟨c₀, hc₀, hden⟩ := exists_den b G
  obtain ⟨kinf, -, hkinf⟩ := coord_rescale σ hcm J (Ainf F) hrI b (scaleB b c₀ hc₀) laminf hinf.1 n minf hminf
  have hkv := fun v => coord_rescale σ hcm J (Fv F v) (hrV v) b (scaleB b c₀ hc₀) (lam v) (hv v).1 n (m v) (hm v)
  choose k hk0 hk using hkv
  have hE' := hSW d (scaleB b c₀ hc₀) laminf lam hinf hv μ 𝓕 hH hF (fun S => kinf • minf S)
    (fun v S => k v • m v S) hkinf hk
  have hfin : ∀ v, m v (hermOf (Fv F v) σ T hT) (latV b v) < ⊤ := by
    intro v
    obtain ⟨r1, r2, r3, r4, -⟩ := id (hrV v)
    obtain ⟨-, -, -, -, -, -, -, hBor, -, -⟩ := GlobalTheory.CompanionTheory.SW.TopK.topTens_props F E σ hcm (Fv F v)
    haveI := hBor n M
    have hL : MeasurableSet (latV b v : Set (Fin n → Fin M → Fv F v ⊗[F] E)) := (hlat.1 v).2.measurableSet
    have hs : ∀ (q : ℝ≥0) (ρ : Measure (Fin n → Fin M → Fv F v ⊗[F] E)) (s : Set _),
        (q • ρ) s = (q : ℝ≥0∞) * ρ s := fun q ρ s => by
      rw [Measure.smul_apply]
      rfl
    have h1 : (k v • m v (hermOf (Fv F v) σ T' hT')) (latV (scaleB b c₀ hc₀) v) < ⊤ := hE'.1 v
    have h2 : m v (hermOf (Fv F v) σ T' hT') (latV (scaleB b c₀ hc₀) v) < ⊤ := by
      by_contra hx
      rw [hs, not_lt_top_iff.1 hx, ENNReal.mul_top (by exact_mod_cast hk0 v)] at h1
      exact lt_irrefl _ h1
    have h3 : (fun X : Fin n → Fin M → Fv F v ⊗[F] E => rmul (Fv F v) X (H.map (inclR (F := F) (Fv F v)))) ⁻¹'
        (latV b v) ⊆ latV (scaleB b c₀ hc₀) v := by
      intro X hX
      have h4 := rmul_mem_scaleB b c₀ hc₀ G v (hden v) hX
      rwa [LatRat.rmul_rmul, ← Matrix.map_mul, hHG, Matrix.map_one _ (map_zero _) (map_one _),
        LatRat.rmul_one] at h4
    have e2 : ((m v (hermOf (Fv F v) σ T' hT')).map
        (fun X => rmul (Fv F v) X (H.map (inclR (F := F) (Fv F v))))) (latV b v) =
        ((a v / c v) • m v (hermOf (Fv F v) σ T hT)) (latV b v) := by rw [sV v]
    rw [Measure.map_apply (mv v) hL, hs] at e2
    by_contra hx
    rw [not_lt_top_iff.1 hx, ENNReal.mul_top (by exact_mod_cast div_ne_zero (ha0 v) (hc0 v))] at e2
    have h5 := (measure_mono h3).trans_lt h2
    rw [e2] at h5
    exact lt_irrefl _ h5
  rw [← hth]
  exact GlobalTheory.T.euler_product_measure_transport F E σ hcm d b n M _ (minf (hermOf (Ainf F) σ T' hT')) (minf (hermOf (Ainf F) σ T hT))
    (fun v => m v (hermOf (Fv F v) σ T' hT')) (fun v => m v (hermOf (Fv F v) σ T hT))
    (fun X => rmul (AF F) X (H.map (inclR (F := F) (AF F))))
    (fun X => rmul (Ainf F) X (H.map (inclR (F := F) (Ainf F))))
    (fun v X => rmul (Fv F v) X (H.map (inclR (F := F) (Fv F v)))) me mi mv
    (fun X => ⟨projInf_rmul X H, fun v => projV_rmul v X H⟩)
    ((LatRat.latV_rational F E σ hcm d b n M).1 H hdetH)
    (ai / ci) (fun v => a v / c v) hq sInf sV hfin hE

end Main

end GlobalTheory.CompanionTheory.WeilSiegel.Free.Scale

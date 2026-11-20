import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.OfRoots
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.GramUnipotentStabilizerBruhatCellConjRoot
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.TranslatedLatticeAtInfinityFullCovolumeDual

open NumberField Module Matrix Formalism.MainNotions.S GlobalTheory.LoopV MeasureTheory
open scoped ENNReal Classical

noncomputable section

namespace GlobalTheory.LieCovol

/- English proof (translation)
Establish `hbij : Function.Bijective fun v => InfinitePlace.mk (τ v)`. Use `⟨fun v₁ v₂ h => ?_, fun w => (hτ w).exists⟩` and prove the remaining obligations. Take `⟨v, -, hv⟩` from `hτ (InfinitePlace.mk (τ v₂))`. Conclude with `(hv v₁ h).trans (hv v₂ rfl).symm`. Set `e : ι ≃ InfinitePlace K` to `Equiv.ofBijective _ hbij`.

Establish `he : ∀ w, InfinitePlace.mk (τ (e.symm w)) = w` using `fun w => e.apply_symm_apply w`. Set `g : InfinitePlace K → (ℂ ≃ₗᵢ[ℝ] ℂ)` to `fun w => if w.embedding = τ (e.symm w) then LinearIsometryEquiv.refl ℝ ℂ else Complex.conjLIE`. Set `Ψl : (ι → R → ℂ) ≃ₗ[ℝ] (InfinitePlace K → Fin j → ℂ)` to `((LinearEquiv.funCongrLeft ℝ (R → ℂ) e.symm).trans (LinearEquiv.piCongrRight fun _ => LinearEquiv.funCongrLeft ℝ ℂ r.symm)).trans (LinearEquiv.piCongrRight fun w => LinearEquiv.piCongrRight fun _ => (g w).toLinearEquiv)`. Establish `hΨ : ∀ c w a, Ψl c w a = g w (c (e.symm w) (r.symm a))` using `fun c w a => rfl`. Use `⟨Ψl.toContinuousLinearEquiv, ?_, fun x => ?_⟩` and prove the remaining obligations.

Establish `h12 : MeasurePreserving (MeasurableEquiv.arrowCongr' e (MeasurableEquiv.arrowCongr' r (MeasurableEquiv.refl ℂ))) volume volume` using `volume_preserving_arrowCongr' _ _ (volume_preserving_arrowCongr' _ _ (MeasurePreserving.id _))`. Establish `h3 : MeasurePreserving (fun (y : InfinitePlace K → Fin j → ℂ) w a => g w (y w a)) volume volume` using `measurePreserving_pi _ _ fun w => measurePreserving_pi _ _ fun _ => (g w).measurePreserving`. Use `h3.comp h12 using 1` and compare the differences between its conclusion and the goal. Use function extensionality and compare the values at `c w a`. Both sides reduce to the same expression.

Use function extensionality and compare the values at `w a show Ψl _ w a = _`. Rewrite using `[hΨ]`. Simplify using `only [GlobalTheory.LatFacts.emb, AddMonoidHom.coe_mk, ZeroHom.coe_mk]`. Distinguish the cases in `hw : w.embedding = τ (e.symm w)`. Simplify using `only [g, if_pos hw]`.

Rewrite using `[hw]`. Both sides reduce to the same expression. Simplify using `only [g, if_neg hw, Complex.conjLIE_apply]`. Establish `h2` using `InfinitePlace.embedding_mk_eq (τ (e.symm w))`. Rewrite `h2` using `[he w]`.

Break down `h2 with h2 | h2` into its components or cases. Conclude with `absurd h2 hw`. Rewrite using `[h2, NumberField.ComplexEmbedding.conjugate_coe_eq]`.
-/
theorem exists_transport (K : Type) [Field K] [NumberField K] (ι : Type) [Fintype ι] (τ : ι → (K →+* ℂ))
    (hτ : ∀ w : InfinitePlace K, ∃! v, InfinitePlace.mk (τ v) = w) (R : Type) [Fintype R] (j : ℕ) (r : R ≃ Fin j) :
    ∃ Ψ : (ι → R → ℂ) ≃L[ℝ] (InfinitePlace K → Fin j → ℂ), MeasurePreserving Ψ volume volume ∧
      ∀ x : R → K, Ψ (fun v q => τ v (x q)) = GlobalTheory.LatFacts.emb K j (fun a => x (r.symm a)) := by
  classical
  have hbij : Function.Bijective fun v => InfinitePlace.mk (τ v) := by
    refine ⟨fun v₁ v₂ h => ?_, fun w => (hτ w).exists⟩
    obtain ⟨v, -, hv⟩ := hτ (InfinitePlace.mk (τ v₂))
    exact (hv v₁ h).trans (hv v₂ rfl).symm
  let e : ι ≃ InfinitePlace K := Equiv.ofBijective _ hbij
  have he : ∀ w, InfinitePlace.mk (τ (e.symm w)) = w := fun w => e.apply_symm_apply w
  let g : InfinitePlace K → (ℂ ≃ₗᵢ[ℝ] ℂ) := fun w =>
    if w.embedding = τ (e.symm w) then LinearIsometryEquiv.refl ℝ ℂ else Complex.conjLIE
  let Ψl : (ι → R → ℂ) ≃ₗ[ℝ] (InfinitePlace K → Fin j → ℂ) :=
    ((LinearEquiv.funCongrLeft ℝ (R → ℂ) e.symm).trans
      (LinearEquiv.piCongrRight fun _ => LinearEquiv.funCongrLeft ℝ ℂ r.symm)).trans
      (LinearEquiv.piCongrRight fun w => LinearEquiv.piCongrRight fun _ => (g w).toLinearEquiv)
  have hΨ : ∀ c w a, Ψl c w a = g w (c (e.symm w) (r.symm a)) := fun c w a => rfl
  refine ⟨Ψl.toContinuousLinearEquiv, ?_, fun x => ?_⟩
  · have h12 : MeasurePreserving
        (MeasurableEquiv.arrowCongr' e (MeasurableEquiv.arrowCongr' r (MeasurableEquiv.refl ℂ))) volume volume :=
      volume_preserving_arrowCongr' _ _ (volume_preserving_arrowCongr' _ _ (MeasurePreserving.id _))
    have h3 : MeasurePreserving (fun (y : InfinitePlace K → Fin j → ℂ) w a => g w (y w a)) volume volume :=
      measurePreserving_pi _ _ fun w => measurePreserving_pi _ _ fun _ => (g w).measurePreserving
    convert h3.comp h12 using 1
    funext c w a
    rfl
  · funext w a
    show Ψl _ w a = _
    rw [hΨ]
    simp only [GlobalTheory.LatFacts.emb, AddMonoidHom.coe_mk, ZeroHom.coe_mk]
    by_cases hw : w.embedding = τ (e.symm w)
    · simp only [g, if_pos hw]
      rw [hw]
      rfl
    · simp only [g, if_neg hw, Complex.conjLIE_apply]
      have h2 := InfinitePlace.embedding_mk_eq (τ (e.symm w))
      rw [he w] at h2
      rcases h2 with h2 | h2
      · exact absurd h2 hw
      · rw [h2, NumberField.ComplexEmbedding.conjugate_coe_eq]

/- English proof (translation)
Establish `hinv : ∀ v, Invertible (M v)` using `fun v => Matrix.invertibleOfIsUnitDet _ (by rw [hM v]; exact isUnit_one)`. Set `e : ∀ v, (R → ℂ) ≃ₗ[ℝ] (R → ℂ)` to `fun v => (Matrix.toLinearEquiv' (M v) (hinv v)).restrictScalars ℝ`. Set `Φ : (ι → R → ℂ) ≃ₗ[ℝ] (ι → R → ℂ)` to `LinearEquiv.piCongrRight e`. Use `⟨Φ.toContinuousLinearEquiv, ?_, fun c v => ?_⟩` and prove the remaining obligations. Establish `hv : ∀ v, MeasurePreserving (e v) volume volume`.

Introduce `v`. Establish `hdet : LinearMap.det (e v : (R → ℂ) →ₗ[ℝ] (R → ℂ)) = 1` using `by show LinearMap.det ((Matrix.toLin' (M v)).restrictScalars ℝ) = 1`. Rewrite using `[LinearMap.det_restrictScalars, LinearMap.det_toLin', hM v, map_one]`. Use `⟨(LinearMap.continuous_of_finiteDimensional (e v : (R → ℂ) →ₗ[ℝ] (R → ℂ))).measurable, ?_⟩` and prove the remaining obligations. Establish `h` using `MeasureTheory.Measure.map_linearMap_addHaar_eq_smul_addHaar (volume : Measure (R → ℂ)) (f := (e v : (R → ℂ) →ₗ[ℝ] (R → ℂ))) (by rw [hdet]; norm_num)`.

Rewrite `h` using `[hdet]`. Simplify using `using h`. Conclude with `MeasureTheory.measurePreserving_pi (fun _ => volume) (fun _ => volume) hv`. Both sides reduce to the same expression.
-/
theorem exists_act (ι : Type) [Fintype ι] (R : Type) [Fintype R] [DecidableEq R] (M : ι → Matrix R R ℂ) (hM : ∀ v, (M v).det = 1) :
    ∃ Φ : (ι → R → ℂ) ≃L[ℝ] (ι → R → ℂ), MeasurePreserving Φ volume volume ∧ ∀ c v, Φ c v = M v *ᵥ c v := by
  classical
  have hinv : ∀ v, Invertible (M v) := fun v => Matrix.invertibleOfIsUnitDet _ (by rw [hM v]; exact isUnit_one)
  let e : ∀ v, (R → ℂ) ≃ₗ[ℝ] (R → ℂ) := fun v => (Matrix.toLinearEquiv' (M v) (hinv v)).restrictScalars ℝ
  let Φ : (ι → R → ℂ) ≃ₗ[ℝ] (ι → R → ℂ) := LinearEquiv.piCongrRight e
  refine ⟨Φ.toContinuousLinearEquiv, ?_, fun c v => ?_⟩
  · have hv : ∀ v, MeasurePreserving (e v) volume volume := by
      intro v
      have hdet : LinearMap.det (e v : (R → ℂ) →ₗ[ℝ] (R → ℂ)) = 1 := by
        show LinearMap.det ((Matrix.toLin' (M v)).restrictScalars ℝ) = 1
        rw [LinearMap.det_restrictScalars, LinearMap.det_toLin', hM v, map_one]
      refine ⟨(LinearMap.continuous_of_finiteDimensional (e v : (R → ℂ) →ₗ[ℝ] (R → ℂ))).measurable, ?_⟩
      have h := MeasureTheory.Measure.map_linearMap_addHaar_eq_smul_addHaar (volume : Measure (R → ℂ))
        (f := (e v : (R → ℂ) →ₗ[ℝ] (R → ℂ))) (by rw [hdet]; norm_num)
      rw [hdet] at h
      simpa using h
    exact MeasureTheory.measurePreserving_pi (fun _ => volume) (fun _ => volume) hv
  · rfl

/- English proof (translation)
Establish `hf : 0 < Formalism.HermitianLatticesTheory.fDeg K` using `Fintype.card_pos`. Establish `ha : 0 ≤ |(discr K : ℝ)|` using `abs_nonneg _`. Establish `hroot : (|(discr K : ℝ)| ^ ((1 : ℝ) / (2 * Formalism.HermitianLatticesTheory.fDeg K))) ^ Formalism.HermitianLatticesTheory.fDeg K = |(discr K : ℝ)| ^ (1 / 2 : ℝ)`. Rewrite using `[← Real.rpow_natCast, ← Real.rpow_mul ha]`. Use `congr 1`.

Establish `: (Formalism.HermitianLatticesTheory.fDeg K : ℝ) ≠ 0` using `by exact_mod_cast hf.ne'`. Clear the denominators using the available nonvanishing facts. Unfold `Formalism.HermitianLatticesTheory.vInv`. Rewrite using `[div_pow, hroot]`. Conclude with `div_le_self (Real.rpow_nonneg ha _) (one_le_pow₀ (by norm_num))`.
-/
theorem vInv_pow_le (K : Type) [Field K] [NumberField K] :
    Formalism.HermitianLatticesTheory.vInv K ^ Formalism.HermitianLatticesTheory.fDeg K ≤ |(discr K : ℝ)| ^ (1 / 2 : ℝ) := by
  have hf : 0 < Formalism.HermitianLatticesTheory.fDeg K := Fintype.card_pos
  have ha : 0 ≤ |(discr K : ℝ)| := abs_nonneg _
  have hroot : (|(discr K : ℝ)| ^ ((1 : ℝ) / (2 * Formalism.HermitianLatticesTheory.fDeg K))) ^ Formalism.HermitianLatticesTheory.fDeg K = |(discr K : ℝ)| ^ (1 / 2 : ℝ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul ha]
    congr 1
    have : (Formalism.HermitianLatticesTheory.fDeg K : ℝ) ≠ 0 := by exact_mod_cast hf.ne'
    field_simp
  unfold Formalism.HermitianLatticesTheory.vInv
  rw [div_pow, hroot]
  exact div_le_self (Real.rpow_nonneg ha _) (one_le_pow₀ (by norm_num))

set_option backward.isDefEq.respectTransparency.types false in
/- English proof (translation)
Set `b₂` to `Module.Free.chooseBasis ℤ L₂`. Establish `hc : Fintype.card (Module.Free.ChooseBasisIndex ℤ L₁) = Fintype.card (Module.Free.ChooseBasisIndex ℤ L₂)`. Rewrite using `[← Module.finrank_eq_card_chooseBasisIndex, ← Module.finrank_eq_card_chooseBasisIndex, ZLattice.rank ℝ L₁, ZLattice.rank ℝ L₂]`. Set `b₁` to `(Module.Free.chooseBasis ℤ L₁).reindex (Fintype.equivOfCardEq hc)`. Set `c` to `b₂.ofZLatticeBasis ℝ L₂`.

Establish `hself : ((↑) ∘ b₂ : _ → E) = c`. Use function extensionality and compare the values at `i`. Simplify using `[c]`. Rewrite using `[ZLattice.covolume_eq_det_mul_measureReal L₁ μ b₁ c, ZLattice.covolume_eq_det_mul_measureReal L₂ μ b₂ c, hself, Module.Basis.det_self, abs_one, one_mul, mul_eq_mul_right_iff]`. Use `left`.

Rewrite using `[AddSubgroup.relIndex_eq_natAbs_det L₁.toAddSubgroup L₂.toAddSubgroup h b₁ b₂, Nat.cast_natAbs, Int.cast_abs]`. Use `congr 1`. Rewrite using `[Module.Basis.det_apply, Module.Basis.det_apply, Int.cast_det]`. Use `congr 1`. Use extensionality with `i k`.

Rewrite using `[Matrix.map_apply, Module.Basis.toMatrix_apply, Module.Basis.toMatrix_apply]`. Conclude with `b₂.ofZLatticeBasis_repr_apply ℝ L₂ ⟨b₁ k, h (Submodule.coe_mem _)⟩ i`.
-/
theorem covolume_eq_relIndex_mul {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] (μ : Measure E) [μ.IsAddHaarMeasure] (L₁ L₂ : Submodule ℤ E)
    [DiscreteTopology L₁] [IsZLattice ℝ L₁] [DiscreteTopology L₂] [IsZLattice ℝ L₂] (h : L₁ ≤ L₂) :
    ZLattice.covolume L₁ μ = L₁.toAddSubgroup.relIndex L₂.toAddSubgroup * ZLattice.covolume L₂ μ := by
  classical
  let b₂ := Module.Free.chooseBasis ℤ L₂
  have hc : Fintype.card (Module.Free.ChooseBasisIndex ℤ L₁) = Fintype.card (Module.Free.ChooseBasisIndex ℤ L₂) := by
    rw [← Module.finrank_eq_card_chooseBasisIndex, ← Module.finrank_eq_card_chooseBasisIndex,
      ZLattice.rank ℝ L₁, ZLattice.rank ℝ L₂]
  let b₁ := (Module.Free.chooseBasis ℤ L₁).reindex (Fintype.equivOfCardEq hc)
  let c := b₂.ofZLatticeBasis ℝ L₂
  have hself : ((↑) ∘ b₂ : _ → E) = c := by
    funext i; simp [c]
  rw [ZLattice.covolume_eq_det_mul_measureReal L₁ μ b₁ c, ZLattice.covolume_eq_det_mul_measureReal L₂ μ b₂ c,
    hself, Module.Basis.det_self, abs_one, one_mul, mul_eq_mul_right_iff]
  left
  rw [AddSubgroup.relIndex_eq_natAbs_det L₁.toAddSubgroup L₂.toAddSubgroup h b₁ b₂, Nat.cast_natAbs, Int.cast_abs]
  congr 1
  rw [Module.Basis.det_apply, Module.Basis.det_apply, Int.cast_det]
  congr 1
  ext i k
  rw [Matrix.map_apply, Module.Basis.toMatrix_apply, Module.Basis.toMatrix_apply]
  exact b₂.ofZLatticeBasis_repr_apply ℝ L₂ ⟨b₁ k, h (Submodule.coe_mem _)⟩ i

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `hz`. Proceed by induction on `hz using Submodule.span_induction with`. Consider the case `mem x hx`. Take `⟨⟨a, i⟩, rfl⟩` from `hx`.

Introduce `b`. Simplify using `only [GlobalTheory.LatFacts.ratB, Pi.basis_apply]`. Distinguish the cases in `hb : b = a`. Substitute `hb` using the available equality. Simplify using `[NumberField.integralBasis_apply]`.

Simplify using `[Pi.single_eq_of_ne hb]`. Consider the case `zero => intro b; exact ⟨0, by simp⟩`. Consider the case `add x y _ _ hx hy => intro b`. Simplify using `using add_mem (hx b) (hy b)`. Consider the case `smul n x _ hx => intro b`.

Simplify using `using zsmul_mem (hx b) n`. Introduce `hz`. Rewrite using `[← Finset.univ_sum_single z]`. Use `Submodule.sum_mem _ fun a _ => ?_` and prove the remaining obligations. Establish `h1 : z a ∈ Submodule.span ℤ (Set.range (NumberField.integralBasis K))` using `(NumberField.mem_span_integralBasis K).2 (hz a)`.

Establish `h2` using `Submodule.mem_map_of_mem (f := LinearMap.single ℤ (fun _ : Fin j => K) a) h1`. Rewrite `h2` using `[Submodule.map_span]`. Use `Submodule.span_mono ?_ h2` and prove the remaining obligations. Introduce and unpack `_ ⟨_, ⟨i, rfl⟩, rfl⟩`. Conclude with `⟨⟨a, i⟩, by simp [GlobalTheory.LatFacts.ratB, Pi.basis_apply]⟩`.
-/
private theorem mem_span_ratB_iff_forall_mem_range (K : Type) [Field K] [NumberField K] (j : ℕ) (z : Fin j → K) :
    z ∈ Submodule.span ℤ (Set.range (GlobalTheory.LatFacts.ratB K j)) ↔ ∀ a, z a ∈ (algebraMap (𝓞 K) K).range := by
  constructor
  · intro hz
    induction hz using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨⟨a, i⟩, rfl⟩ := hx
      intro b
      simp only [GlobalTheory.LatFacts.ratB, Pi.basis_apply]
      by_cases hb : b = a
      · subst hb
        simp [NumberField.integralBasis_apply]
      · simp [Pi.single_eq_of_ne hb]
    | zero => intro b; exact ⟨0, by simp⟩
    | add x y _ _ hx hy => intro b; simpa using add_mem (hx b) (hy b)
    | smul n x _ hx => intro b; simpa using zsmul_mem (hx b) n
  · intro hz
    rw [← Finset.univ_sum_single z]
    refine Submodule.sum_mem _ fun a _ => ?_
    have h1 : z a ∈ Submodule.span ℤ (Set.range (NumberField.integralBasis K)) :=
      (NumberField.mem_span_integralBasis K).2 (hz a)
    have h2 := Submodule.mem_map_of_mem (f := LinearMap.single ℤ (fun _ : Fin j => K) a) h1
    rw [Submodule.map_span] at h2
    refine Submodule.span_mono ?_ h2
    rintro _ ⟨_, ⟨i, rfl⟩, rfl⟩
    exact ⟨⟨a, i⟩, by simp [GlobalTheory.LatFacts.ratB, Pi.basis_apply]⟩

/- English proof (translation)
Establish `hr : Set.range (GlobalTheory.LatFacts.intB K j) = (GlobalTheory.LatFacts.emb K j).toIntLinearMap '' Set.range (GlobalTheory.LatFacts.ratB K j)`. Rewrite using `[← Set.range_comp]`. Use `congr 1`. Use function extensionality and compare the values at `i`. Conclude with `GlobalTheory.LatFacts.intB_apply K j i`.

Rewrite using `[hr, ← Submodule.map_span, Submodule.mem_map]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨z, hz, rfl⟩`. Rewrite `hz` using `[mem_span_ratB_iff_forall_mem_range]`. Use `choose x hx using hz`.

Use `⟨x, ?_⟩` and prove the remaining obligations. Use `show GlobalTheory.LatFacts.emb K j _ = GlobalTheory.LatFacts.emb K j z`. Use `congr 1`. Use function extensionality and compare the values at `a`. Conclude with `hx a`.

Introduce and unpack `⟨x, rfl⟩`. Conclude with `⟨fun a => (x a : K), (mem_span_ratB_iff_forall_mem_range K j _).2 fun a => ⟨x a, rfl⟩, rfl⟩`.
-/
private theorem mem_span_intB_iff_exists_emb (K : Type) [Field K] [NumberField K] [IsTotallyComplex K] (j : ℕ)
    (y : GlobalTheory.FlagBase.VecInf K j) :
    y ∈ Submodule.span ℤ (Set.range (GlobalTheory.LatFacts.intB K j)) ↔
      ∃ x : Fin j → 𝓞 K, GlobalTheory.LatFacts.emb K j (fun a => (x a : K)) = y := by
  have hr : Set.range (GlobalTheory.LatFacts.intB K j) =
      (GlobalTheory.LatFacts.emb K j).toIntLinearMap '' Set.range (GlobalTheory.LatFacts.ratB K j) := by
    rw [← Set.range_comp]
    congr 1
    funext i
    exact GlobalTheory.LatFacts.intB_apply K j i
  rw [hr, ← Submodule.map_span, Submodule.mem_map]
  constructor
  · rintro ⟨z, hz, rfl⟩
    rw [mem_span_ratB_iff_forall_mem_range] at hz
    choose x hx using hz
    refine ⟨x, ?_⟩
    show GlobalTheory.LatFacts.emb K j _ = GlobalTheory.LatFacts.emb K j z
    congr 1
    funext a
    exact hx a
  · rintro ⟨x, rfl⟩
    exact ⟨fun a => (x a : K), (mem_span_ratB_iff_forall_mem_range K j _).2 fun a => ⟨x a, rfl⟩, rfl⟩

/- English proof (translation)
Establish `: (MeasureTheory.volume : MeasureTheory.Measure (GlobalTheory.FlagBase.VecInf K (Fintype.card R))).IsAddHaarMeasure` using `MeasureTheory.Measure.pi.isAddHaarMeasure _`. Establish `: (MeasureTheory.volume : MeasureTheory.Measure (ι → R → ℂ)).IsAddHaarMeasure` using `MeasureTheory.Measure.pi.isAddHaarMeasure _`. Use `set j := Fintype.card R with hj`. Set `r : R ≃ Fin j` to `Fintype.equivFin R`. Take `⟨Ψ, hΨ, hΨe⟩` from `exists_transport K ι τ hτ R j r`.

Take `⟨Φ, hΦ, hΦe⟩` from `exists_act ι R M hM`. Set `T : (ι → R → ℂ) ≃L[ℝ] GlobalTheory.FlagBase.VecInf K j` to `Φ.trans Ψ`. Establish `hT : MeasurePreserving T volume volume` using `hΨ.comp hΦ`. Set `g0 : (R → 𝓞 K) →+ (Fin j → K)` to `{ toFun := fun x a => ((x (r.symm a) : 𝓞 K) : K) map_zero' := by ext; simp map_add' := by intros; ext; simp }`. Set `f0 : (R → 𝓞 K) →+ GlobalTheory.FlagBase.VecInf K j` to `(GlobalTheory.LatFacts.emb K j).comp g0`.

Establish `hf0 : ∀ x, f0 x = GlobalTheory.LatFacts.emb K j (fun a => ((x (r.symm a) : 𝓞 K) : K))` using `fun x => rfl`. Establish `hf0inj : Function.Injective f0`. Introduce `x y hxy`. Take `⟨w⟩ : Nonempty (InfinitePlace K)` from `inferInstance`. Use function extensionality and compare the values at `q`.

Establish `h1` using `congrFun (congrFun hxy w) (r q)`. Simplify using `only [hf0, GlobalTheory.LatFacts.emb, AddMonoidHom.coe_mk, ZeroHom.coe_mk, Equiv.symm_apply_apply] at h1`. Conclude with `Subtype.val_injective (w.embedding.injective h1)`. Set `Lf : Submodule ℤ (GlobalTheory.FlagBase.VecInf K j)` to `Submodule.span ℤ (Set.range (GlobalTheory.LatFacts.intB K j))`. Set `LH : Submodule ℤ (GlobalTheory.FlagBase.VecInf K j)` to `AddSubgroup.toIntSubmodule (H.map f0)`.

Establish `hLH : ∀ y, y ∈ LH ↔ ∃ x ∈ H, f0 x = y` using `fun y => AddSubgroup.mem_map`. Establish `hLf : Lf.toAddSubgroup = (⊤ : AddSubgroup (R → 𝓞 K)).map f0`. Use extensionality with `y`. Simplify using `only [Submodule.mem_toAddSubgroup, AddSubgroup.mem_map, AddSubgroup.mem_top, true_and]`. Rewrite using `[mem_span_intB_iff_exists_emb]`.

Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨x, rfl⟩`. Conclude with `⟨fun q => x (r q), by rw [hf0]; simp⟩`. Introduce and unpack `⟨x, rfl⟩`. Conclude with `⟨fun a => x (r.symm a), rfl⟩`.

Establish `hle : LH ≤ Lf`. Introduce `y hy`. Take `⟨x, -, rfl⟩` from `(hLH y).1 hy`. Establish `h2 : f0 x ∈ Lf.toAddSubgroup`. Rewrite using `[hLf]`.

Conclude with `AddSubgroup.mem_map_of_mem _ (AddSubgroup.mem_top x)`. Conclude with `h2`. Establish `hidx : LH.toAddSubgroup.relIndex Lf.toAddSubgroup = H.index`. Rewrite using `[hLf, AddSubgroup.toIntSubmodule_toAddSubgroup, AddSubgroup.relIndex_map_map_of_injective _ _ hf0inj, AddSubgroup.relIndex_top_right]`. Establish `hdLf : DiscreteTopology Lf` using `by dsimp only [Lf] infer_instance`.

Establish `: IsZLattice ℝ Lf` using `by dsimp only [Lf] infer_instance`. Establish `: DiscreteTopology LH` using `DiscreteTopology.of_subset (s := (Lf : Set _)) hdLf hle`. Establish `: IsZLattice ℝ LH`. Use `⟨eq_top_iff.2 ?_⟩` and prove the remaining obligations. Rewrite using `[← IsZLattice.span_top (K := ℝ) (L := Lf), Submodule.span_le]`.

Introduce `y hy`. Establish `hmem : (LH.toAddSubgroup.relIndex Lf.toAddSubgroup) • y ∈ LH.toAddSubgroup` using `AddSubgroup.nsmul_relIndex_mem _ hy`. Rewrite `hmem` using `[hidx]`. Establish `hn : (H.index : ℝ) ≠ 0` using `by exact_mod_cast hH`. Establish `hy' : y = (H.index : ℝ)⁻¹ • ((H.index : ℝ) • y)`.

Rewrite using `[smul_smul, inv_mul_cancel₀ hn, one_smul]`. Rewrite using `[hy']`. Use `Submodule.smul_mem _ _ (Submodule.subset_span ?_)` and prove the remaining obligations. Rewrite using `[Nat.cast_smul_eq_nsmul]`. Conclude with `hmem`.

Establish `hΛeq : Λ = ZLattice.comap ℝ LH T.toLinearMap`. Use extensionality with `c`. Rewrite using `[hΛ]`. Use `show _ ↔ T c ∈ LH`. Rewrite using `[hLH]`.

Establish `hTc : T c = Ψ (fun v => M v *ᵥ c v)` using `by show Ψ (Φ c) = _`. Use `congr 1`. Use function extensionality and compare the values at `v`. Conclude with `hΦe c v`. Rewrite using `[hTc]`.

Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨x, hx, hxe⟩`. Use `⟨x, hx, ?_⟩` and prove the remaining obligations. Establish `e1` using `hΨe (fun q => ((x q : 𝓞 K) : K))`. Rewrite using `[hf0, ← e1]`.

Use `congr 1`. Use function extensionality and compare the values at `v`. Conclude with `(hxe v).symm`. Introduce and unpack `⟨x, hx, hxe⟩`. Use `⟨x, hx, fun v => ?_⟩` and prove the remaining obligations.

Establish `e1` using `hΨe (fun q => ((x q : 𝓞 K) : K))`. Rewrite `hxe` using `[hf0, ← e1]`. Conclude with `(congrFun (Ψ.injective hxe) v).symm`. Substitute `hΛeq` using the available equality. Set `b` to `Module.Free.chooseBasis ℤ (ZLattice.comap ℝ LH T.toLinearMap)`.

Use `⟨ZSpan.fundamentalDomain (b.ofZLatticeBasis ℝ), ZSpan.fundamentalDomain_measurableSet _, ZLattice.isAddFundamentalDomain b volume, ?_⟩` and prove the remaining obligations. Establish `hfin : volume (ZSpan.fundamentalDomain (b.ofZLatticeBasis ℝ)) ≠ ⊤` using `(ZSpan.fundamentalDomain_isBounded _).measure_lt_top.ne`. Establish `hcovLf : ZLattice.covolume Lf volume = Formalism.HermitianLatticesTheory.vInv K ^ (Formalism.HermitianLatticesTheory.fDeg K * j)`. Rewrite using `[ZLattice.covolume_eq_measure_fundamentalDomain Lf volume (ZSpan.isAddFundamentalDomain (GlobalTheory.LatFacts.intB K j) volume)]`. Conclude with `GlobalTheory.LatFacts.volume_fd_intB K j`.

Rewrite using `[← ofReal_measureReal hfin, ← ZLattice.covolume_eq_measure_fundamentalDomain _ volume (ZLattice.isAddFundamentalDomain b volume), ZLattice.covolume_comap LH volume volume hT, covolume_eq_relIndex_mul volume LH Lf hle, hidx, hcovLf]`. Apply `ENNReal.ofReal_le_ofReal` to reduce the goal to its premises. Apply `mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)` to reduce the goal to its premises. Rewrite using `[pow_mul]`. Conclude with `pow_le_pow_left₀ (by unfold Formalism.HermitianLatticesTheory.vInv; positivity) (vInv_pow_le K) _`.
-/
theorem exists_domain (K : Type) [Field K] [NumberField K] [IsTotallyComplex K] (ι : Type) [Fintype ι]
    (τ : ι → (K →+* ℂ)) (hτ : ∀ w : InfinitePlace K, ∃! v, InfinitePlace.mk (τ v) = w) (R : Type) [Fintype R] [DecidableEq R]
    (H : AddSubgroup (R → 𝓞 K)) (hH : H.index ≠ 0) (M : ι → Matrix R R ℂ) (hM : ∀ v, (M v).det = 1)
    (Λ : Submodule ℤ (ι → R → ℂ))
    (hΛ : ∀ c, c ∈ Λ ↔ ∃ x ∈ H, ∀ v, M v *ᵥ c v = fun q => τ v (x q)) :
    ∃ Ω : Set (ι → R → ℂ), MeasurableSet Ω ∧ IsAddFundamentalDomain Λ Ω volume ∧
      volume Ω ≤ ENNReal.ofReal (H.index * (|(discr K : ℝ)| ^ (1 / 2 : ℝ)) ^ Fintype.card R) := by
  classical
  have : (MeasureTheory.volume : MeasureTheory.Measure (GlobalTheory.FlagBase.VecInf K (Fintype.card R))).IsAddHaarMeasure :=
    MeasureTheory.Measure.pi.isAddHaarMeasure _
  have : (MeasureTheory.volume : MeasureTheory.Measure (ι → R → ℂ)).IsAddHaarMeasure :=
    MeasureTheory.Measure.pi.isAddHaarMeasure _
  set j := Fintype.card R with hj
  let r : R ≃ Fin j := Fintype.equivFin R
  obtain ⟨Ψ, hΨ, hΨe⟩ := exists_transport K ι τ hτ R j r
  obtain ⟨Φ, hΦ, hΦe⟩ := exists_act ι R M hM
  let T : (ι → R → ℂ) ≃L[ℝ] GlobalTheory.FlagBase.VecInf K j := Φ.trans Ψ
  have hT : MeasurePreserving T volume volume := hΨ.comp hΦ
  let g0 : (R → 𝓞 K) →+ (Fin j → K) :=
    { toFun := fun x a => ((x (r.symm a) : 𝓞 K) : K)
      map_zero' := by ext; simp
      map_add' := by intros; ext; simp }
  let f0 : (R → 𝓞 K) →+ GlobalTheory.FlagBase.VecInf K j := (GlobalTheory.LatFacts.emb K j).comp g0
  have hf0 : ∀ x, f0 x = GlobalTheory.LatFacts.emb K j (fun a => ((x (r.symm a) : 𝓞 K) : K)) := fun x => rfl
  have hf0inj : Function.Injective f0 := by
    intro x y hxy
    obtain ⟨w⟩ : Nonempty (InfinitePlace K) := inferInstance
    funext q
    have h1 := congrFun (congrFun hxy w) (r q)
    simp only [hf0, GlobalTheory.LatFacts.emb, AddMonoidHom.coe_mk, ZeroHom.coe_mk, Equiv.symm_apply_apply] at h1
    exact Subtype.val_injective (w.embedding.injective h1)
  let Lf : Submodule ℤ (GlobalTheory.FlagBase.VecInf K j) := Submodule.span ℤ (Set.range (GlobalTheory.LatFacts.intB K j))
  let LH : Submodule ℤ (GlobalTheory.FlagBase.VecInf K j) := AddSubgroup.toIntSubmodule (H.map f0)
  have hLH : ∀ y, y ∈ LH ↔ ∃ x ∈ H, f0 x = y := fun y => AddSubgroup.mem_map
  have hLf : Lf.toAddSubgroup = (⊤ : AddSubgroup (R → 𝓞 K)).map f0 := by
    ext y
    simp only [Submodule.mem_toAddSubgroup, AddSubgroup.mem_map, AddSubgroup.mem_top, true_and]
    rw [mem_span_intB_iff_exists_emb]
    constructor
    · rintro ⟨x, rfl⟩
      exact ⟨fun q => x (r q), by rw [hf0]; simp⟩
    · rintro ⟨x, rfl⟩
      exact ⟨fun a => x (r.symm a), rfl⟩
  have hle : LH ≤ Lf := by
    intro y hy
    obtain ⟨x, -, rfl⟩ := (hLH y).1 hy
    have h2 : f0 x ∈ Lf.toAddSubgroup := by
      rw [hLf]
      exact AddSubgroup.mem_map_of_mem _ (AddSubgroup.mem_top x)
    exact h2
  have hidx : LH.toAddSubgroup.relIndex Lf.toAddSubgroup = H.index := by
    rw [hLf, AddSubgroup.toIntSubmodule_toAddSubgroup, AddSubgroup.relIndex_map_map_of_injective _ _ hf0inj,
      AddSubgroup.relIndex_top_right]
  have hdLf : DiscreteTopology Lf := by
    dsimp only [Lf]
    infer_instance
  have : IsZLattice ℝ Lf := by
    dsimp only [Lf]
    infer_instance
  have : DiscreteTopology LH := DiscreteTopology.of_subset (s := (Lf : Set _)) hdLf hle
  have : IsZLattice ℝ LH := by
    refine ⟨eq_top_iff.2 ?_⟩
    rw [← IsZLattice.span_top (K := ℝ) (L := Lf), Submodule.span_le]
    intro y hy
    have hmem : (LH.toAddSubgroup.relIndex Lf.toAddSubgroup) • y ∈ LH.toAddSubgroup :=
      AddSubgroup.nsmul_relIndex_mem _ hy
    rw [hidx] at hmem
    have hn : (H.index : ℝ) ≠ 0 := by exact_mod_cast hH
    have hy' : y = (H.index : ℝ)⁻¹ • ((H.index : ℝ) • y) := by
      rw [smul_smul, inv_mul_cancel₀ hn, one_smul]
    rw [hy']
    refine Submodule.smul_mem _ _ (Submodule.subset_span ?_)
    rw [Nat.cast_smul_eq_nsmul]
    exact hmem
  have hΛeq : Λ = ZLattice.comap ℝ LH T.toLinearMap := by
    ext c
    rw [hΛ]
    show _ ↔ T c ∈ LH
    rw [hLH]
    have hTc : T c = Ψ (fun v => M v *ᵥ c v) := by
      show Ψ (Φ c) = _
      congr 1
      funext v
      exact hΦe c v
    rw [hTc]
    constructor
    · rintro ⟨x, hx, hxe⟩
      refine ⟨x, hx, ?_⟩
      have e1 := hΨe (fun q => ((x q : 𝓞 K) : K))
      rw [hf0, ← e1]
      congr 1
      funext v
      exact (hxe v).symm
    · rintro ⟨x, hx, hxe⟩
      refine ⟨x, hx, fun v => ?_⟩
      have e1 := hΨe (fun q => ((x q : 𝓞 K) : K))
      rw [hf0, ← e1] at hxe
      exact (congrFun (Ψ.injective hxe) v).symm
  subst hΛeq
  let b := Module.Free.chooseBasis ℤ (ZLattice.comap ℝ LH T.toLinearMap)
  refine ⟨ZSpan.fundamentalDomain (b.ofZLatticeBasis ℝ), ZSpan.fundamentalDomain_measurableSet _,
    ZLattice.isAddFundamentalDomain b volume, ?_⟩
  have hfin : volume (ZSpan.fundamentalDomain (b.ofZLatticeBasis ℝ)) ≠ ⊤ :=
    (ZSpan.fundamentalDomain_isBounded _).measure_lt_top.ne
  have hcovLf : ZLattice.covolume Lf volume = Formalism.HermitianLatticesTheory.vInv K ^ (Formalism.HermitianLatticesTheory.fDeg K * j) := by
    rw [ZLattice.covolume_eq_measure_fundamentalDomain Lf volume
      (ZSpan.isAddFundamentalDomain (GlobalTheory.LatFacts.intB K j) volume)]
    exact GlobalTheory.LatFacts.volume_fd_intB K j
  rw [← ofReal_measureReal hfin, ← ZLattice.covolume_eq_measure_fundamentalDomain _ volume
    (ZLattice.isAddFundamentalDomain b volume), ZLattice.covolume_comap LH volume volume hT,
    covolume_eq_relIndex_mul volume LH Lf hle, hidx, hcovLf]
  apply ENNReal.ofReal_le_ofReal
  apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
  rw [pow_mul]
  exact pow_le_pow_left₀ (by unfold Formalism.HermitianLatticesTheory.vInv; positivity) (vInv_pow_le K) _

/- English proof (translation)
Set `gD : (S → 𝓞 K) →ₗ[ℤ] (S → 𝓞 K)` to `(Matrix.toLin' D).restrictScalars ℤ`. Set `fA : (R → 𝓞 K) →+ (S → 𝓞 K)` to `(Matrix.toLin' A).toAddMonoidHom`. Set `N : AddSubgroup (S → 𝓞 K)` to `(LinearMap.range gD).toAddSubgroup`. Establish `hgD : ∀ z, gD z = D *ᵥ z` using `fun z => rfl`. Establish `hfA : ∀ x, fA x = A *ᵥ x` using `fun x => rfl`.

Establish `hinj : Function.Injective gD`. Rewrite using `[← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']`. Introduce `z hz`. Rewrite `hz` using `[hgD]`. Establish `h2 : D.det • z = 0`.

Combine the equalities or inequalities in the displayed calculation. Rewrite using `[Matrix.smul_mulVec, Matrix.one_mulVec]`. Use `_ = D.adjugate *ᵥ (D *ᵥ z) := by rw [← Matrix.adjugate_mul, Matrix.mulVec_mulVec]`. Use `_ = 0 := by rw [hz, Matrix.mulVec_zero]`. Conclude with `(smul_eq_zero.mp h2).resolve_left hD`.

Establish `hdet : LinearMap.det gD = Algebra.norm ℤ D.det`. Rewrite using `[LinearMap.det_restrictScalars, LinearMap.det_toLin']`. Set `e : (S → 𝓞 K) ≃ₗ[ℤ] LinearMap.range gD` to `LinearEquiv.ofInjective gD hinj`. Establish `hN : N.index = (Algebra.norm ℤ D.det).natAbs`. Establish `h1` using `Submodule.natAbs_det_equiv (LinearMap.range gD) e`.

Combine the equalities or inequalities in the displayed calculation. Use `congr 2`. Use `_ = _ := by rw [hdet]`. Establish `hN0 : N.index ≠ 0`. Rewrite using `[hN, Int.natAbs_ne_zero]`.

Conclude with `Algebra.norm_ne_zero_iff.mpr hD`. Establish `hdvd : (N.comap fA).index ∣ N.index`. Rewrite using `[AddSubgroup.index_comap]`. Conclude with `AddSubgroup.relIndex_dvd_index_of_normal _ _`. Use `⟨N.comap fA, ?_, ?_, ?_⟩` and prove the remaining obligations.

Introduce `x`. Rewrite using `[AddSubgroup.mem_comap]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨z, hz⟩`. Use `⟨-z, ?_⟩` and prove the remaining obligations.

Rewrite using `[Matrix.mulVec_neg, ← hgD, hz, hfA, add_neg_cancel]`. Introduce and unpack `⟨z, hz⟩`. Use `⟨-z, ?_⟩` and prove the remaining obligations. Rewrite using `[LinearMap.map_neg, hgD, hfA]`. Conclude with `(neg_eq_of_add_eq_zero_right (by rw [add_comm]; exact hz))`.

Conclude with `fun h0 => hN0 (Nat.eq_zero_of_zero_dvd (h0 ▸ hdvd))`. Establish `hle : ((N.comap fA).index : ℝ) ≤ N.index` using `by exact_mod_cast Nat.le_of_dvd (Nat.pos_of_ne_zero hN0) hdvd`. Use `hle.trans (le_of_eq ?_)` and prove the remaining obligations. Rewrite using `[NumberField.InfinitePlace.prod_eq_abs_norm, ← Algebra.coe_norm_int, hN, Nat.cast_natAbs]`. Use `push_cast`.

Both sides reduce to the same expression.
-/
theorem index_le (K : Type) [Field K] [NumberField K] (R S : Type) [Fintype R] [Fintype S] [DecidableEq S]
    (A : Matrix S R (𝓞 K)) (D : Matrix S S (𝓞 K)) (hD : D.det ≠ 0) :
    ∃ H : AddSubgroup (R → 𝓞 K), (∀ x, x ∈ H ↔ ∃ z, A *ᵥ x + D *ᵥ z = 0) ∧ H.index ≠ 0 ∧
      (H.index : ℝ) ≤ ∏ w : InfinitePlace K, w (D.det : 𝓞 K) ^ w.mult := by
  classical
  let gD : (S → 𝓞 K) →ₗ[ℤ] (S → 𝓞 K) := (Matrix.toLin' D).restrictScalars ℤ
  let fA : (R → 𝓞 K) →+ (S → 𝓞 K) := (Matrix.toLin' A).toAddMonoidHom
  let N : AddSubgroup (S → 𝓞 K) := (LinearMap.range gD).toAddSubgroup
  have hgD : ∀ z, gD z = D *ᵥ z := fun z => rfl
  have hfA : ∀ x, fA x = A *ᵥ x := fun x => rfl
  have hinj : Function.Injective gD := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro z hz
    rw [hgD] at hz
    have h2 : D.det • z = 0 := by
      calc D.det • z = (D.det • (1 : Matrix S S (𝓞 K))) *ᵥ z := by
            rw [Matrix.smul_mulVec, Matrix.one_mulVec]
        _ = D.adjugate *ᵥ (D *ᵥ z) := by rw [← Matrix.adjugate_mul, Matrix.mulVec_mulVec]
        _ = 0 := by rw [hz, Matrix.mulVec_zero]
    exact (smul_eq_zero.mp h2).resolve_left hD
  have hdet : LinearMap.det gD = Algebra.norm ℤ D.det := by
    rw [LinearMap.det_restrictScalars, LinearMap.det_toLin']
  let e : (S → 𝓞 K) ≃ₗ[ℤ] LinearMap.range gD := LinearEquiv.ofInjective gD hinj
  have hN : N.index = (Algebra.norm ℤ D.det).natAbs := by
    have h1 := Submodule.natAbs_det_equiv (LinearMap.range gD) e
    calc N.index = Nat.card ((S → 𝓞 K) ⧸ LinearMap.range gD) := rfl
      _ = _ := h1.symm
      _ = (LinearMap.det gD).natAbs := by
        congr 2
      _ = _ := by rw [hdet]
  have hN0 : N.index ≠ 0 := by
    rw [hN, Int.natAbs_ne_zero]
    exact Algebra.norm_ne_zero_iff.mpr hD
  have hdvd : (N.comap fA).index ∣ N.index := by
    rw [AddSubgroup.index_comap]
    exact AddSubgroup.relIndex_dvd_index_of_normal _ _
  refine ⟨N.comap fA, ?_, ?_, ?_⟩
  · intro x
    rw [AddSubgroup.mem_comap]
    constructor
    · rintro ⟨z, hz⟩
      refine ⟨-z, ?_⟩
      rw [Matrix.mulVec_neg, ← hgD, hz, hfA, add_neg_cancel]
    · rintro ⟨z, hz⟩
      refine ⟨-z, ?_⟩
      rw [LinearMap.map_neg, hgD, hfA]
      exact (neg_eq_of_add_eq_zero_right (by rw [add_comm]; exact hz))
  · exact fun h0 => hN0 (Nat.eq_zero_of_zero_dvd (h0 ▸ hdvd))
  · have hle : ((N.comap fA).index : ℝ) ≤ N.index := by exact_mod_cast Nat.le_of_dvd (Nat.pos_of_ne_zero hN0) hdvd
    refine hle.trans (le_of_eq ?_)
    rw [NumberField.InfinitePlace.prod_eq_abs_norm, ← Algebra.coe_norm_int, hN, Nat.cast_natAbs]
    push_cast
    rfl

/- English proof (translation)
Establish `hrank : β.rank = Fintype.card S`. Rewrite using `[Matrix.rank, LinearMap.finrank_range_of_inj (by simpa [Matrix.coe_mulVecLin] using h), Module.finrank_fintype_fun_eq_card]`. Establish `hspan : Submodule.span K (Set.range β.row) = ⊤`. Apply `Submodule.eq_top_of_finrank_eq` to reduce the goal to its premises. Rewrite using `[← Matrix.rank_eq_finrank_span_row, hrank, Module.finrank_fintype_fun_eq_card]`.

Take `⟨κ, a, ha, hsp, hli⟩` from `exists_linearIndependent' K β.row`. Establish `: Finite κ` using `Finite.of_injective a ha`. Set `_ : Fintype κ` to `Fintype.ofFinite κ`. Establish `hcard : Fintype.card κ = Fintype.card S`. Rewrite using `[linearIndependent_iff_card_eq_finrank_span.mp hli, Set.finrank, hsp, hspan, finrank_top, Module.finrank_fintype_fun_eq_card]`.

Set `f : S ≃ κ` to `Fintype.equivOfCardEq hcard.symm`. Use `⟨a ∘ f, ?_⟩` and prove the remaining obligations. Establish `hli' : LinearIndependent K (β.submatrix (a ∘ f) id).row`. Establish `e : (β.submatrix (a ∘ f) id).row = (β.row ∘ a) ∘ f`. Use extensionality with `s t`.

Both sides reduce to the same expression. Rewrite using `[e]`. Conclude with `hli.comp f f.injective`. Conclude with `((Matrix.isUnit_iff_isUnit_det _).mp (Matrix.linearIndependent_rows_iff_isUnit.mp hli')).ne_zero`.
-/
theorem exists_rows {K : Type} [Field K] {P S : Type} [Fintype P] [Fintype S] [DecidableEq S] (β : Matrix P S K)
    (h : Function.Injective β.mulVec) : ∃ e : S → P, (β.submatrix e id).det ≠ 0 := by
  have hrank : β.rank = Fintype.card S := by
    rw [Matrix.rank, LinearMap.finrank_range_of_inj (by simpa [Matrix.coe_mulVecLin] using h),
      Module.finrank_fintype_fun_eq_card]
  have hspan : Submodule.span K (Set.range β.row) = ⊤ := by
    apply Submodule.eq_top_of_finrank_eq
    rw [← Matrix.rank_eq_finrank_span_row, hrank, Module.finrank_fintype_fun_eq_card]
  obtain ⟨κ, a, ha, hsp, hli⟩ := exists_linearIndependent' K β.row
  have : Finite κ := Finite.of_injective a ha
  let _ : Fintype κ := Fintype.ofFinite κ
  have hcard : Fintype.card κ = Fintype.card S := by
    rw [linearIndependent_iff_card_eq_finrank_span.mp hli, Set.finrank, hsp, hspan, finrank_top,
      Module.finrank_fintype_fun_eq_card]
  let f : S ≃ κ := Fintype.equivOfCardEq hcard.symm
  refine ⟨a ∘ f, ?_⟩
  have hli' : LinearIndependent K (β.submatrix (a ∘ f) id).row := by
    have e : (β.submatrix (a ∘ f) id).row = (β.row ∘ a) ∘ f := by
      ext s t
      rfl
    rw [e]
    exact hli.comp f f.injective
  exact ((Matrix.isUnit_iff_isUnit_det _).mp (Matrix.linearIndependent_rows_iff_isUnit.mp hli')).ne_zero

variable {K : Type} [Field K] {N : ℕ}

/- English proof (translation)
Establish `hz : ∀ q : Fin N × Fin N, q ∉ T → A a q.1 * B q.2 b * x q.1 q.2 = 0` using `fun q hq => by rw [hx q.1 q.2 hq, mul_zero]`. Rewrite using `[Finset.sum_subset (Finset.subset_univ T) (fun q _ hq => hz q hq), Fintype.sum_prod_type, Finset.sum_comm]`. Simplify using `only [Matrix.mul_apply, Finset.sum_mul]`. Conclude with `Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => by ring`.
-/
theorem mul_mul_apply (A x B : Matrix (Fin N) (Fin N) K) (T : Finset (Fin N × Fin N))
    (hx : ∀ i j, (i, j) ∉ T → x i j = 0) (a b : Fin N) :
    (A * x * B) a b = ∑ q ∈ T, A a q.1 * B q.2 b * x q.1 q.2 := by
  have hz : ∀ q : Fin N × Fin N, q ∉ T → A a q.1 * B q.2 b * x q.1 q.2 = 0 :=
    fun q hq => by rw [hx q.1 q.2 hq, mul_zero]
  rw [Finset.sum_subset (Finset.subset_univ T) (fun q _ hq => hz q hq), Fintype.sum_prod_type,
    Finset.sum_comm]
  simp only [Matrix.mul_apply, Finset.sum_mul]
  exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => by ring

/- English proof (translation)
Rewrite using `[Matrix.det_of_isUpperTriangular (fun i j hij => (hU i j).1 hij)]`. Conclude with `Finset.prod_eq_one fun i _ => (hU i i).2 rfl`.
-/
theorem det_upUni {U : Matrix (Fin N) (Fin N) K} (hU : IsUpUni U) : U.det = 1 := by
  rw [Matrix.det_of_isUpperTriangular (fun i j hij => (hU i j).1 hij)]
  exact Finset.prod_eq_one fun i _ => (hU i i).2 rfl

/- English proof (translation)
Establish `hdet : IsUnit U.det` using `by rw [det_upUni hU]; exact isUnit_one`. Use `U.invertibleOfIsUnitDet hdet` as an intermediate fact. Establish `ht : U⁻¹.BlockTriangular id` using `Matrix.blockTriangular_inv_of_blockTriangular (fun i j hij => (hU i j).1 hij)`. Introduce `i j`. Use `⟨fun h => ht h, ?_⟩` and prove the remaining obligations.

Introduce and unpack `rfl`. Establish `h1 : (U * U⁻¹) i i = 1` using `by rw [Matrix.mul_nonsing_inv _ hdet]; simp`. Rewrite `h1` using `[Matrix.mul_apply, Finset.sum_eq_single i]`. Rewrite `h1` using `[(hU i i).2 rfl, one_mul]`. Then use the resulting hypothesis. Introduce `k _ hki`.

Break down `lt_or_gt_of_ne hki with h | h` into its components or cases. Rewrite using `[(hU i k).1 h, zero_mul]`. Rewrite using `[ht h, mul_zero]`. Simplify using the standard rewrite rules.
-/
theorem upUni_inv {U : Matrix (Fin N) (Fin N) K} (hU : IsUpUni U) : IsUpUni U⁻¹ := by
  have hdet : IsUnit U.det := by rw [det_upUni hU]; exact isUnit_one
  have := U.invertibleOfIsUnitDet hdet
  have ht : U⁻¹.BlockTriangular id :=
    Matrix.blockTriangular_inv_of_blockTriangular (fun i j hij => (hU i j).1 hij)
  intro i j
  refine ⟨fun h => ht h, ?_⟩
  rintro rfl
  have h1 : (U * U⁻¹) i i = 1 := by rw [Matrix.mul_nonsing_inv _ hdet]; simp
  rw [Matrix.mul_apply, Finset.sum_eq_single i] at h1
  · rwa [(hU i i).2 rfl, one_mul] at h1
  · intro k _ hki
    rcases lt_or_gt_of_ne hki with h | h
    · rw [(hU i k).1 h, zero_mul]
    · rw [ht h, mul_zero]
  · simp

def conjMat (U : Matrix (Fin N) (Fin N) K) (R : Finset (Fin N × Fin N)) : Matrix R R K :=
  fun q q' => U⁻¹ q.1.1 q'.1.1 * U q'.1.2 q.1.2

/- English proof (translation)
Set `_ : LinearOrder n` to `LinearOrder.lift' k hk`. Use `Matrix.det_of_isUpperTriangular (M := M) (fun i j hij => h i j hij)` and compare the differences between its conclusion and the goal.
-/
theorem det_of_key {n κ : Type} [Fintype n] [DecidableEq n] [LinearOrder κ] (M : Matrix n n K) (k : n → κ)
    (hk : Function.Injective k) (h : ∀ i j, k j < k i → M i j = 0) : M.det = ∏ i, M i i := by
  let _ : LinearOrder n := LinearOrder.lift' k hk
  convert Matrix.det_of_isUpperTriangular (M := M) (fun i j hij => h i j hij)

/- English proof (translation)
Establish `hUi` using `upUni_inv hU`. Rewrite using `[det_of_key (conjMat U R) (fun q : R => toLex (q.1.1, OrderDual.toDual q.1.2))]`. Conclude with `Finset.prod_eq_one fun q _ => by simp [conjMat, (hUi _ _).2 rfl, (hU _ _).2 rfl]`. Introduce `q q' h`. Establish `h'` using `Prod.ext_iff.1 (toLex.injective h)`.

Conclude with `Subtype.ext (Prod.ext h'.1 (OrderDual.toDual.injective h'.2))`. Introduce `q q' h`. Simplify using `only [conjMat]`. Break down `Prod.Lex.lt_iff.1 h with h1 | ⟨_, h2⟩` into its components or cases. Establish `h1' : q'.1.1 < q.1.1` using `h1`.

Rewrite using `[(hUi _ _).1 h1', zero_mul]`. Establish `h2' : q.1.2 < q'.1.2` using `h2`. Rewrite using `[(hU _ _).1 h2', mul_zero]`.
-/
theorem det_conjMat {U : Matrix (Fin N) (Fin N) K} (hU : IsUpUni U) (R : Finset (Fin N × Fin N)) :
    (conjMat U R).det = 1 := by
  have hUi := upUni_inv hU
  rw [det_of_key (conjMat U R) (fun q : R => toLex (q.1.1, OrderDual.toDual q.1.2))]
  · exact Finset.prod_eq_one fun q _ => by simp [conjMat, (hUi _ _).2 rfl, (hU _ _).2 rfl]
  · intro q q' h
    have h' := Prod.ext_iff.1 (toLex.injective h)
    exact Subtype.ext (Prod.ext h'.1 (OrderDual.toDual.injective h'.2))
  · intro q q' h
    simp only [conjMat]
    rcases Prod.Lex.lt_iff.1 h with h1 | ⟨_, h2⟩
    · have h1' : q'.1.1 < q.1.1 := h1
      rw [(hUi _ _).1 h1', zero_mul]
    · have h2' : q.1.2 < q'.1.2 := h2
      rw [(hU _ _).1 h2', mul_zero]

section Cell

variable {Z U : Matrix (Fin N) (Fin N) K} {R : Finset (Fin N × Fin N)}

/- English proof (translation)
Establish `hd : IsUnit U.det` using `by rw [det_upUni hU]; exact isUnit_one`. Establish `hx' : x = U⁻¹ * (U * x * U⁻¹) * U`. Simplify using `only [Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hd, Matrix.mul_one, Matrix.nonsing_inv_mul_cancel_left _ _ hd]`. Use function extensionality and compare the values at `q`. Use `conv_rhs => rw [hx']`.

Rewrite using `[mul_mul_apply U⁻¹ (U * x * U⁻¹) U R hx, ← Finset.sum_coe_sort R]`. Simplify using `only [Matrix.mulVec, dotProduct, conjMat]`.
-/
theorem conjMat_mulVec (hU : IsUpUni U) {x : Matrix (Fin N) (Fin N) K}
    (hx : ∀ i j, (i, j) ∉ R → (U * x * U⁻¹) i j = 0) :
    conjMat U R *ᵥ (fun q : R => (U * x * U⁻¹) q.1.1 q.1.2) = fun q : R => x q.1.1 q.1.2 := by
  have hd : IsUnit U.det := by rw [det_upUni hU]; exact isUnit_one
  have hx' : x = U⁻¹ * (U * x * U⁻¹) * U := by
    simp only [Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hd, Matrix.mul_one,
      Matrix.nonsing_inv_mul_cancel_left _ _ hd]
  funext q
  conv_rhs => rw [hx']
  rw [mul_mul_apply U⁻¹ (U * x * U⁻¹) U R hx, ← Finset.sum_coe_sort R]
  simp only [Matrix.mulVec, dotProduct, conjMat]

/- English proof (translation)
Establish `hd : IsUnit (conjMat U R).det` using `by rw [det_conjMat hU]; exact isUnit_one`. Establish `hUd : IsUnit U.det` using `by rw [det_upUni hU]; exact isUnit_one`. Set `z` to `(conjMat U R)⁻¹ *ᵥ y`. Set `w : Matrix (Fin N) (Fin N) K` to `fun i j => if h : (i, j) ∈ R then z ⟨(i, j), h⟩ else 0`. Establish `hw : U * (U⁻¹ * w * U) * U⁻¹ = w`.

Simplify using `only [Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hUd, Matrix.mul_one, Matrix.mul_nonsing_inv_cancel_left _ _ hUd]`. Establish `hsupp : ∀ i j, (i, j) ∉ R → (U * (U⁻¹ * w * U) * U⁻¹) i j = 0`. Introduce `i j hij`. Rewrite using `[hw]`. Simplify using `[w, hij]`.

Use `⟨U⁻¹ * w * U, hsupp, fun q => ?_⟩` and prove the remaining obligations. Establish `h1` using `congrFun (conjMat_mulVec hU hsupp) q`. Rewrite `h1` using `[hw]`. Establish `hwz : (fun q : R => w q.1.1 q.1.2) = z`. Use function extensionality and compare the values at `q'`.

Simplify using `[w, q'.2]`. Rewrite using `[← h1, hwz]`. Simplify using `only [z, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hd, Matrix.one_mulVec]`.
-/
theorem exists_lie (hU : IsUpUni U) (y : R → K) :
    ∃ x : Matrix (Fin N) (Fin N) K, (∀ i j, (i, j) ∉ R → (U * x * U⁻¹) i j = 0) ∧ ∀ q : R, x q.1.1 q.1.2 = y q := by
  have hd : IsUnit (conjMat U R).det := by rw [det_conjMat hU]; exact isUnit_one
  have hUd : IsUnit U.det := by rw [det_upUni hU]; exact isUnit_one
  let z := (conjMat U R)⁻¹ *ᵥ y
  let w : Matrix (Fin N) (Fin N) K := fun i j => if h : (i, j) ∈ R then z ⟨(i, j), h⟩ else 0
  have hw : U * (U⁻¹ * w * U) * U⁻¹ = w := by
    simp only [Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hUd, Matrix.mul_one,
      Matrix.mul_nonsing_inv_cancel_left _ _ hUd]
  have hsupp : ∀ i j, (i, j) ∉ R → (U * (U⁻¹ * w * U) * U⁻¹) i j = 0 := by
    intro i j hij; rw [hw]; simp [w, hij]
  refine ⟨U⁻¹ * w * U, hsupp, fun q => ?_⟩
  have h1 := congrFun (conjMat_mulVec hU hsupp) q
  rw [hw] at h1
  have hwz : (fun q : R => w q.1.1 q.1.2) = z := by
    funext q'; simp [w, q'.2]
  rw [← h1, hwz]
  simp only [z, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hd, Matrix.one_mulVec]

def coRoots (R : Finset (Fin N × Fin N)) : Finset (Fin N × Fin N) :=
  Finset.univ.filter fun q => q.1 < q.2 ∧ q ∉ R

def eqMat {A : Type} [CommRing A] (Z : Matrix (Fin N) (Fin N) A) (T : Finset (Fin N × Fin N)) :
    Matrix {q : Fin N × Fin N // q.1 ≤ q.2} T A :=
  fun a q => Z a.1.1 q.1.1 * Z.adjugate q.1.2 a.1.2

/- English proof (translation)
Establish `hsupp : ∀ i j, (i, j) ∉ R ∪ coRoots R → x i j = 0`. Introduce `i j hij`. Break down `le_or_gt j i with hji | hij'` into its components or cases. Conclude with `hx i j hji`. It suffices to derive a contradiction.

Apply `hij` to reduce the goal to its premises. Distinguish the cases in `hq : (i, j) ∈ R`. Conclude with `Finset.mem_union_left _ hq`. Conclude with `Finset.mem_union_right _ (by simp [coRoots, hij', hq])`. Establish `hdisj : Disjoint R (coRoots R)`.

Rewrite using `[Finset.disjoint_right]`. Introduce `q hq`. Simplify using `only [coRoots, Finset.mem_filter] at hq`. Conclude with `hq.2.2`. Establish `key : ∀ a : {q : Fin N × Fin N // q.1 ≤ q.2}, (eqMat Z R *ᵥ (fun q : R => x q.1.1 q.1.2) + eqMat Z (coRoots R) *ᵥ (fun q : coRoots R => x q.1.1 q.1.2)) a = (Z * x * Z.adjugate) a.1.1 a.1.2`.

Introduce `a`. Rewrite using `[mul_mul_apply Z x Z.adjugate (R ∪ coRoots R) hsupp, Finset.sum_union hdisj]`. Simplify using `only [Pi.add_apply, mulVec, dotProduct, eqMat]`. Rewrite using `[Finset.sum_coe_sort R (fun q => Z a.1.1 q.1 * Z.adjugate q.2 a.1.2 * x q.1 q.2), Finset.sum_coe_sort (coRoots R) (fun q => Z a.1.1 q.1 * Z.adjugate q.2 a.1.2 * x q.1 q.2)]`. Prove the components needed by the constructor for the conclusion.

Introduce and unpack `⟨-, hlo⟩`. Use function extensionality and compare the values at `a`. Rewrite using `[key]`. Conclude with `hlo _ _ a.2`. Introduce `h`.

Use `⟨hx, fun i j hij => ?_⟩` and prove the remaining obligations. Use `congrFun h ⟨(i, j), hij⟩` as an intermediate fact. Rewrite `this` using `[key]`. Then use the resulting hypothesis.
-/
theorem mem_lieU_iff (hR : ∀ q ∈ R, q.1 < q.2) {x : Matrix (Fin N) (Fin N) K} (hx : StrUp x) :
    x ∈ lieU Z ↔ eqMat Z R *ᵥ (fun q : R => x q.1.1 q.1.2) +
      eqMat Z (coRoots R) *ᵥ (fun q : coRoots R => x q.1.1 q.1.2) = 0 := by
  have hsupp : ∀ i j, (i, j) ∉ R ∪ coRoots R → x i j = 0 := by
    intro i j hij
    rcases le_or_gt j i with hji | hij'
    · exact hx i j hji
    · exfalso
      apply hij
      by_cases hq : (i, j) ∈ R
      · exact Finset.mem_union_left _ hq
      · exact Finset.mem_union_right _ (by simp [coRoots, hij', hq])
  have hdisj : Disjoint R (coRoots R) := by
    rw [Finset.disjoint_right]
    intro q hq
    simp only [coRoots, Finset.mem_filter] at hq
    exact hq.2.2
  have key : ∀ a : {q : Fin N × Fin N // q.1 ≤ q.2},
      (eqMat Z R *ᵥ (fun q : R => x q.1.1 q.1.2) +
        eqMat Z (coRoots R) *ᵥ (fun q : coRoots R => x q.1.1 q.1.2)) a =
        (Z * x * Z.adjugate) a.1.1 a.1.2 := by
    intro a
    rw [mul_mul_apply Z x Z.adjugate (R ∪ coRoots R) hsupp, Finset.sum_union hdisj]
    simp only [Pi.add_apply, mulVec, dotProduct, eqMat]
    rw [Finset.sum_coe_sort R (fun q => Z a.1.1 q.1 * Z.adjugate q.2 a.1.2 * x q.1 q.2),
      Finset.sum_coe_sort (coRoots R) (fun q => Z a.1.1 q.1 * Z.adjugate q.2 a.1.2 * x q.1 q.2)]
  constructor
  · rintro ⟨-, hlo⟩
    funext a
    rw [key]
    exact hlo _ _ a.2
  · intro h
    refine ⟨hx, fun i j hij => ?_⟩
    have := congrFun h ⟨(i, j), hij⟩
    rwa [key] at this

/- English proof (translation)
Introduce `v w hvw`. Establish `h0 : eqMat Z (coRoots R) *ᵥ (v - w) = 0`. Rewrite using `[Matrix.mulVec_sub, hvw, sub_self]`. Rewrite using `[← sub_eq_zero]`. Use `set u := v - w with hu`.

Set `x : Matrix (Fin N) (Fin N) K` to `fun i j => if h : (i, j) ∈ coRoots R then u ⟨(i, j), h⟩ else 0`. Establish `hxs : StrUp x`. Introduce `i j hji`. Simplify using `only [x]`. Rewrite using `[dif_neg]`.

Introduce `hm`. Simplify using `only [coRoots, Finset.mem_filter] at hm`. Conclude with `absurd hm.2.1 (not_lt.2 hji)`. Establish `hxR : (fun q : R => x q.1.1 q.1.2) = 0`. Use function extensionality and compare the values at `q`.

Simplify using `only [x, Pi.zero_apply]`. Rewrite using `[dif_neg]`. Introduce `hm`. Simplify using `only [coRoots, Finset.mem_filter] at hm`. Conclude with `hm.2.2 q.2`.

Establish `hxC : (fun q : coRoots R => x q.1.1 q.1.2) = u`. Use function extensionality and compare the values at `q`. Simplify using `only [x]`. Rewrite using `[dif_pos q.2]`. Establish `hmem : x ∈ lieU Z`.

Rewrite using `[mem_lieU_iff hR hxs, hxR, hxC, Matrix.mulVec_zero, zero_add]`. Conclude with `h0`. Establish `hsupp` using `(hc x).1 hmem`. Establish `hconj` using `conjMat_mulVec hU hsupp`. Rewrite `hconj` using `[hxR]`.

Establish `hy : (fun q : R => (U * x * U⁻¹) q.1.1 q.1.2) = 0` using `Matrix.eq_zero_of_mulVec_eq_zero (by rw [det_conjMat hU R]; exact one_ne_zero) hconj`. Establish `hall : U * x * U⁻¹ = 0`. Use extensionality with `i j`. Distinguish the cases in `hij : (i, j) ∈ R`. Conclude with `congrFun hy ⟨(i, j), hij⟩`.

Conclude with `hsupp i j hij`. Establish `hUu : IsUnit U.det` using `by rw [det_upUni hU]; exact isUnit_one`. Establish `hx0 : x = 0`. Establish `e : U⁻¹ * (U * x * U⁻¹) * U = x`. Combine the equalities or inequalities in the displayed calculation.

Rewrite using `[← e, hall, Matrix.mul_zero, Matrix.zero_mul]`. Rewrite using `[← hxC, hx0]`. Both sides reduce to the same expression.
-/
theorem eqMat_injective (hU : IsUpUni U) (hR : ∀ q ∈ R, q.1 < q.2)
    (hc : ∀ x, x ∈ lieU Z ↔ ∀ i j, (i, j) ∉ R → (U * x * U⁻¹) i j = 0) :
    Function.Injective (eqMat Z (coRoots R)).mulVec := by
  intro v w hvw
  have h0 : eqMat Z (coRoots R) *ᵥ (v - w) = 0 := by
    rw [Matrix.mulVec_sub, hvw, sub_self]
  rw [← sub_eq_zero]
  set u := v - w with hu
  let x : Matrix (Fin N) (Fin N) K := fun i j => if h : (i, j) ∈ coRoots R then u ⟨(i, j), h⟩ else 0
  have hxs : StrUp x := by
    intro i j hji
    simp only [x]
    rw [dif_neg]
    intro hm
    simp only [coRoots, Finset.mem_filter] at hm
    exact absurd hm.2.1 (not_lt.2 hji)
  have hxR : (fun q : R => x q.1.1 q.1.2) = 0 := by
    funext q
    simp only [x, Pi.zero_apply]
    rw [dif_neg]
    intro hm
    simp only [coRoots, Finset.mem_filter] at hm
    exact hm.2.2 q.2
  have hxC : (fun q : coRoots R => x q.1.1 q.1.2) = u := by
    funext q
    simp only [x]
    rw [dif_pos q.2]
  have hmem : x ∈ lieU Z := by
    rw [mem_lieU_iff hR hxs, hxR, hxC, Matrix.mulVec_zero, zero_add]
    exact h0
  have hsupp := (hc x).1 hmem
  have hconj := conjMat_mulVec hU hsupp
  rw [hxR] at hconj
  have hy : (fun q : R => (U * x * U⁻¹) q.1.1 q.1.2) = 0 :=
    Matrix.eq_zero_of_mulVec_eq_zero (by rw [det_conjMat hU R]; exact one_ne_zero) hconj
  have hall : U * x * U⁻¹ = 0 := by
    ext i j
    by_cases hij : (i, j) ∈ R
    · exact congrFun hy ⟨(i, j), hij⟩
    · exact hsupp i j hij
  have hUu : IsUnit U.det := by rw [det_upUni hU]; exact isUnit_one
  have hx0 : x = 0 := by
    have e : U⁻¹ * (U * x * U⁻¹) * U = x := by
      calc U⁻¹ * (U * x * U⁻¹) * U = (U⁻¹ * U) * x * (U⁻¹ * U) := by simp only [Matrix.mul_assoc]
        _ = x := by rw [Matrix.nonsing_inv_mul _ hUu, Matrix.one_mul, Matrix.mul_one]
    rw [← e, hall, Matrix.mul_zero, Matrix.zero_mul]
  rw [← hxC, hx0]
  rfl

/- English proof (translation)
Establish `hdisj : Disjoint T (T.image Prod.swap)`. Rewrite using `[Finset.disjoint_left]`. Introduce `q hq hq'`. Take `⟨p, hp, rfl⟩` from `Finset.mem_image.1 hq'`. Conclude with `absurd ((hT _ hp).trans (hT _ hq)) (lt_irrefl _)`.

Establish `hc : (T.image Prod.swap).card = T.card` using `Finset.card_image_of_injective _ Prod.swap_injective`. Establish `h` using `Finset.card_le_univ (T ∪ T.image Prod.swap)`. Rewrite `h` using `[Finset.card_union_of_disjoint hdisj, hc, Fintype.card_prod, Fintype.card_fin]`. Rewrite using `[sq, two_mul]`. Conclude with `h`.
-/
private theorem two_mul_card_le_sq_of_forall_fst_lt_snd {N : ℕ} (T : Finset (Fin N × Fin N)) (hT : ∀ q ∈ T, q.1 < q.2) :
    2 * T.card ≤ N ^ 2 := by
  have hdisj : Disjoint T (T.image Prod.swap) := by
    rw [Finset.disjoint_left]
    intro q hq hq'
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.1 hq'
    exact absurd ((hT _ hp).trans (hT _ hq)) (lt_irrefl _)
  have hc : (T.image Prod.swap).card = T.card :=
    Finset.card_image_of_injective _ Prod.swap_injective
  have h := Finset.card_le_univ (T ∪ T.image Prod.swap)
  rw [Finset.card_union_of_disjoint hdisj, hc, Fintype.card_prod, Fintype.card_fin] at h
  rw [sq, two_mul]
  exact h

/- English proof (translation)
Break down `Nat.eq_zero_or_pos c with rfl | hc` into its components or cases. Break down `Nat.eq_zero_or_pos m with rfl | hm` into its components or cases. Simplify using the standard rewrite rules. Simplify using `using Nat.one_le_pow m m hm`. Combine the equalities or inequalities in the displayed calculation.
-/
private theorem factorial_sq_le_pow_self_of_two_mul_le (c m : ℕ) (h : 2 * c ≤ m) : c.factorial ^ 2 ≤ m ^ m := by
  rcases Nat.eq_zero_or_pos c with rfl | hc
  · rcases Nat.eq_zero_or_pos m with rfl | hm
    · simp
    · simpa using Nat.one_le_pow m m hm
  · calc c.factorial ^ 2 ≤ (c ^ c) ^ 2 := Nat.pow_le_pow_left (Nat.factorial_le_pow c) 2
      _ = c ^ (2 * c) := by ring
      _ ≤ m ^ (2 * c) := Nat.pow_le_pow_left (by omega) _
      _ ≤ m ^ m := Nat.pow_le_pow_right (by omega) h

end Cell

/- English proof (translation)
Establish `hb1 : 1 ≤ b` using `by simpa using hb 0 Fin.elim0 Fin.elim0`. Rewrite using `[max_eq_right hb1]`. Establish `hZ : ∀ i j, ‖φ (Z i j)‖ ≤ b` using `fun i j => by`. Simplify `hb 1 (fun _ => i) (fun _ => j)` using `[Matrix.det_unique]`. Establish `hA : ∀ i j, ‖φ (Z.adjugate i j)‖ ≤ b`.

Introduce `i j`. Consider the cases of `N with`. Consider the case `zero => exact i.elim0`. Consider the case `succ n`. Rewrite using `[Matrix.adjugate_fin_succ_eq_det_submatrix, map_mul, norm_mul, map_pow, map_neg, map_one, norm_pow, norm_neg, norm_one, one_pow, one_mul]`.

Conclude with `hb n _ _`. Establish `hent : ∀ i j, NormedField.toAbsoluteValue ℂ ((φ.mapMatrix ((eqMat Z T).submatrix e id)) i j) ≤ b ^ 2`. Introduce `i j`. Use `show ‖φ (Z _ _ * Z.adjugate _ _)‖ ≤ b ^ 2`. Rewrite using `[map_mul, norm_mul, sq]`.

Conclude with `mul_le_mul (hZ _ _) (hA _ _) (norm_nonneg _) (by linarith)`. Establish `hdet` using `Matrix.det_le hent`. Rewrite `hdet` using `[← RingHom.map_det, Fintype.card_coe, nsmul_eq_mul]`. Establish `hx : ‖φ ((eqMat Z T).submatrix e id).det‖ ≤ (T.card.factorial : ℝ) * (b ^ 2) ^ T.card` using `hdet`. Establish `hc` using `two_mul_card_le_sq_of_forall_fst_lt_snd T hT`.

Establish `hfac : ((T.card.factorial : ℝ)) ^ 2 ≤ ((N : ℝ) ^ 2) ^ (N ^ 2)`. Conclude with `factorial_sq_le_pow_self_of_two_mul_le T.card (N ^ 2) hc` after adjusting the coercions. Combine the equalities or inequalities in the displayed calculation. Conclude with `mul_le_mul hfac (pow_le_pow_right₀ hb1 (by linarith)) (by positivity) (by positivity)`. Use `_ ≤ (4 * (N : ℝ) ^ 2 * b ^ 4) ^ (N ^ 2) := by`.

Establish `h4 : (4 * (N : ℝ) ^ 2 * b ^ 4) ^ (N ^ 2) = 4 ^ (N ^ 2) * (((N : ℝ) ^ 2) ^ (N ^ 2) * b ^ (4 * N ^ 2))`. Rewrite using `[mul_pow, mul_pow, pow_mul b 4]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[h4]`. Conclude with `le_mul_of_one_le_left (by positivity) (one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 4))`.
-/
theorem norm_det_eqMat_le (φ : K →+* ℂ) (Z : Matrix (Fin N) (Fin N) K) (b : ℝ)
    (hb : ∀ (t : ℕ) (I J : Fin t → Fin N), ‖φ ((Z.submatrix I J).det)‖ ≤ b) (T : Finset (Fin N × Fin N))
    (hT : ∀ q ∈ T, q.1 < q.2) (e : T → {q : Fin N × Fin N // q.1 ≤ q.2}) :
    ‖φ ((eqMat Z T).submatrix e id).det‖ ^ 2 ≤ (4 * (N : ℝ) ^ 2 * max 1 b ^ 4) ^ N ^ 2 := by
  have hb1 : 1 ≤ b := by simpa using hb 0 Fin.elim0 Fin.elim0
  rw [max_eq_right hb1]
  have hZ : ∀ i j, ‖φ (Z i j)‖ ≤ b := fun i j => by
    simpa [Matrix.det_unique] using hb 1 (fun _ => i) (fun _ => j)
  have hA : ∀ i j, ‖φ (Z.adjugate i j)‖ ≤ b := by
    intro i j
    cases N with
    | zero => exact i.elim0
    | succ n =>
      rw [Matrix.adjugate_fin_succ_eq_det_submatrix, map_mul, norm_mul, map_pow, map_neg, map_one,
        norm_pow, norm_neg, norm_one, one_pow, one_mul]
      exact hb n _ _
  have hent : ∀ i j, NormedField.toAbsoluteValue ℂ
      ((φ.mapMatrix ((eqMat Z T).submatrix e id)) i j) ≤ b ^ 2 := by
    intro i j
    show ‖φ (Z _ _ * Z.adjugate _ _)‖ ≤ b ^ 2
    rw [map_mul, norm_mul, sq]
    exact mul_le_mul (hZ _ _) (hA _ _) (norm_nonneg _) (by linarith)
  have hdet := Matrix.det_le hent
  rw [← RingHom.map_det, Fintype.card_coe, nsmul_eq_mul] at hdet
  have hx : ‖φ ((eqMat Z T).submatrix e id).det‖ ≤ (T.card.factorial : ℝ) * (b ^ 2) ^ T.card := hdet
  have hc := two_mul_card_le_sq_of_forall_fst_lt_snd T hT
  have hfac : ((T.card.factorial : ℝ)) ^ 2 ≤ ((N : ℝ) ^ 2) ^ (N ^ 2) := by
    exact_mod_cast factorial_sq_le_pow_self_of_two_mul_le T.card (N ^ 2) hc
  calc ‖φ ((eqMat Z T).submatrix e id).det‖ ^ 2
        ≤ ((T.card.factorial : ℝ) * (b ^ 2) ^ T.card) ^ 2 := by gcongr
      _ = ((T.card.factorial : ℝ)) ^ 2 * b ^ (4 * T.card) := by ring
      _ ≤ ((N : ℝ) ^ 2) ^ (N ^ 2) * b ^ (4 * N ^ 2) := by
        exact mul_le_mul hfac (pow_le_pow_right₀ hb1 (by linarith)) (by positivity) (by positivity)
      _ ≤ (4 * (N : ℝ) ^ 2 * b ^ 4) ^ (N ^ 2) := by
        have h4 : (4 * (N : ℝ) ^ 2 * b ^ 4) ^ (N ^ 2) = 4 ^ (N ^ 2) * (((N : ℝ) ^ 2) ^ (N ^ 2) * b ^ (4 * N ^ 2)) := by
          rw [mul_pow, mul_pow, pow_mul b 4]
          ring
        rw [h4]
        exact le_mul_of_one_le_left (by positivity) (one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 4))

/- English proof (translation)
Establish `hb : Function.Bijective (fun v => InfinitePlace.mk (τ v))` using `⟨fun a b h => (hτ _).unique rfl h.symm, fun w => (hτ w).exists⟩`. Use `⟨hb, ?_⟩` and prove the remaining obligations. Establish `hc` using `Fintype.card_of_bijective hb`. Establish `h1` using `InfinitePlace.card_add_two_mul_card_eq_rank K`. Establish `h2` using `InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces K`.

Rewrite using `[← nrRealPlaces_eq_zero_iff]`. Use linear arithmetic over natural numbers and integers.
-/
private theorem bijective_mk_and_isTotallyComplex_of_unique_place [NumberField K] (ι : Type) [Fintype ι] (τ : ι → (K →+* ℂ))
    (hτ : ∀ w : InfinitePlace K, ∃! v, InfinitePlace.mk (τ v) = w)
    (hrk : finrank ℚ K = 2 * Fintype.card ι) :
    Function.Bijective (fun v => InfinitePlace.mk (τ v)) ∧ IsTotallyComplex K := by
  have hb : Function.Bijective (fun v => InfinitePlace.mk (τ v)) :=
    ⟨fun a b h => (hτ _).unique rfl h.symm, fun w => (hτ w).exists⟩
  refine ⟨hb, ?_⟩
  have hc := Fintype.card_of_bijective hb
  have h1 := InfinitePlace.card_add_two_mul_card_eq_rank K
  have h2 := InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces K
  rw [← nrRealPlaces_eq_zero_iff]
  omega

/- English proof (translation)
Use extensionality with `a q`. Establish `h` using `congrFun (congrFun (RingHom.map_adjugate f Z) q.1.2) a.1.2`. Simplify using `only [RingHom.mapMatrix_apply, Matrix.map_apply] at h`. Simplify using `only [eqMat, Matrix.map_apply, map_mul, h]`.
-/
private theorem eqMat_map_ringHom {A : Type} [CommRing A] (f : A →+* K) (Z : Matrix (Fin N) (Fin N) A)
    (T : Finset (Fin N × Fin N)) : (eqMat Z T).map f = eqMat (Z.map f) T := by
  ext a q
  have h := congrFun (congrFun (RingHom.map_adjugate f Z) q.1.2) a.1.2
  simp only [RingHom.mapMatrix_apply, Matrix.map_apply] at h
  simp only [eqMat, Matrix.map_apply, map_mul, h]

/- English proof (translation)
Take `⟨hbij, hTC⟩` from `bijective_mk_and_isTotallyComplex_of_unique_place ι τ hτ hrk`. Use `choose FinalForm _ hZo using hZ`. Use `set Z' : Matrix (Fin N) (Fin N) (𝓞 K) := Matrix.of FinalForm with hZ'`. Establish `hZmap : Z'.map (algebraMap (𝓞 K) K) = Z`. Use extensionality with `i j`.

Simplify using `[Z', hZo]`. Use `set S := coRoots R with hSdef`. Establish `hinj` using `eqMat_injective hU hR hc`. Take `⟨e, he⟩` from `exists_rows _ hinj`. Use `set Ao : Matrix S R (𝓞 K) := (eqMat Z' R).submatrix e id with hAodef`.

Use `set Do : Matrix S S (𝓞 K) := (eqMat Z' S).submatrix e id with hDodef`. Establish `hAo : Ao.map (algebraMap (𝓞 K) K) = (eqMat Z R).submatrix e id`. Rewrite using `[← hZmap, ← eqMat_map_ringHom]`. Both sides reduce to the same expression. Establish `hDo : Do.map (algebraMap (𝓞 K) K) = (eqMat Z S).submatrix e id`.

Rewrite using `[← hZmap, ← eqMat_map_ringHom]`. Both sides reduce to the same expression. Establish `hDdet : algebraMap (𝓞 K) K Do.det = ((eqMat Z S).submatrix e id).det`. Rewrite using `[RingHom.map_det]`. Conclude with `congrArg Matrix.det hDo`.

Establish `hD : Do.det ≠ 0`. Introduce `h`. Apply `he` to reduce the goal to its premises. Rewrite using `[← hDdet, h, map_zero]`. Take `⟨H, hH, hHi, hHle⟩` from `index_le K R S Ao Do hD`.

Use `set M : ι → Matrix R R ℂ := fun v => (conjMat U R).map (τ v) with hMdef`. Establish `hM : ∀ v, (M v).det = 1` using `fun v => by`. Rewrite using `[show M v = (τ v).mapMatrix (conjMat U R) from rfl, ← RingHom.map_det, det_conjMat hU, map_one]`. Establish `hMinj : ∀ v (a b : R → ℂ), M v *ᵥ a = M v *ᵥ b → a = b` using `fun v a b h => sub_eq_zero.1 (Matrix.eq_zero_of_mulVec_eq_zero (by rw [hM v]; exact one_ne_zero) (by rw [Matrix.mulVec_sub, h, sub_self]))`. Establish `hMx : ∀ x : Matrix (Fin N) (Fin N) K, (∀ i j, (i, j) ∉ R → (U * x * U⁻¹) i j = 0) → ∀ v, M v *ᵥ (fun q : R => τ v ((U * x * U⁻¹) q.1.1 q.1.2)) = fun q : R => τ v (x q.1.1 q.1.2)`.

Introduce `x hsx v`. Use function extensionality and compare the values at `q`. Establish `h` using `RingHom.map_mulVec (τ v) (conjMat U R) (fun q : R => (U * x * U⁻¹) q.1.1 q.1.2) q`. Rewrite `h` using `[conjMat_mulVec hU hsx]`. Conclude with `h.symm`.

Establish `hrows : ∀ x : Matrix (Fin N) (Fin N) K, x ∈ lieU Z → (eqMat Z R).submatrix e id *ᵥ (fun q : R => x q.1.1 q.1.2) + (eqMat Z S).submatrix e id *ᵥ (fun q : S => x q.1.1 q.1.2) = 0`. Introduce `x hx`. Use function extensionality and compare the values at `s`. Conclude with `congrFun ((mem_lieU_iff hR hx.1).1 hx) (e s)`. Establish `hΛ' : ∀ c, c ∈ Λ ↔ ∃ y ∈ H, ∀ v, M v *ᵥ c v = fun q => τ v (y q)`.

Introduce `c`. Rewrite using `[hΛ c]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨x, hx, hxi, hcx⟩ choose xo _ hxo using hxi`. Establish `hsx` using `(hc x).1 hx`.

Use `⟨fun q => xo q.1.1 q.1.2, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[hH]`. Use `⟨fun s => xo s.1.1 s.1.2, ?_⟩` and prove the remaining obligations. Use function extensionality and compare the values at `s`. Apply `RingOfIntegers.coe_injective` to reduce the goal to its premises.

Establish `key` using `congrFun (hrows x hx) s`. Establish `e1` using `RingHom.map_mulVec (algebraMap (𝓞 K) K) Ao (fun q : R => xo q.1.1 q.1.2) s`. Establish `e2` using `RingHom.map_mulVec (algebraMap (𝓞 K) K) Do (fun q : S => xo q.1.1 q.1.2) s`. Rewrite `e1` using `[hAo]`. Rewrite `e2` using `[hDo]`.

Establish `e3 : (algebraMap (𝓞 K) K ∘ fun q : R => xo q.1.1 q.1.2) = fun q : R => x q.1.1 q.1.2`. Use function extensionality and compare the values at `q`. Conclude with `hxo _ _`. Establish `e4 : (algebraMap (𝓞 K) K ∘ fun q : S => xo q.1.1 q.1.2) = fun q : S => x q.1.1 q.1.2`. Use function extensionality and compare the values at `q`.

Conclude with `hxo _ _`. Rewrite `e1` using `[e3]`. Rewrite `e2` using `[e4]`. Establish `: algebraMap (𝓞 K) K ((Ao *ᵥ fun q : R => xo q.1.1 q.1.2) s + (Do *ᵥ fun q : S => xo q.1.1 q.1.2) s) = 0`. Rewrite using `[map_add, e1, e2]`.

Conclude with `key`. Simplify using `using this`. Introduce `v`. Rewrite using `[show c v = fun q : R => τ v ((U * x * U⁻¹) q.1.1 q.1.2) from funext (hcx v), hMx x hsx v]`. Use function extensionality and compare the values at `q`.

Simplify using `[hxo]`. Introduce and unpack `⟨y, hy, hMy⟩`. Take `⟨z, hz⟩` from `(hH y).1 hy`. Take `⟨x, hsx, hxy⟩` from `exists_lie hU (fun q : R => (y q : K))`. Establish `hx : x ∈ lieU Z` using `(hc x).2 hsx`.

Establish `hxz : (fun q : S => x q.1.1 q.1.2) = fun q : S => (z q : K)`. Establish `k1` using `hrows x hx`. Establish `k2 : (eqMat Z R).submatrix e id *ᵥ (fun q : R => (y q : K)) + (eqMat Z S).submatrix e id *ᵥ (fun q : S => (z q : K)) = 0`. Use function extensionality and compare the values at `s`. Establish `e1` using `RingHom.map_mulVec (algebraMap (𝓞 K) K) Ao y s`.

Establish `e2` using `RingHom.map_mulVec (algebraMap (𝓞 K) K) Do z s`. Rewrite `e1` using `[hAo]`. Rewrite `e2` using `[hDo]`. Use `congrArg (algebraMap (𝓞 K) K) (congrFun hz s)` as an intermediate fact. Rewrite `this` using `[Pi.add_apply, map_add, e1, e2]`.

Conclude with `this`. Establish `hxR : (fun q : R => x q.1.1 q.1.2) = fun q : R => (y q : K)` using `funext hxy`. Rewrite `k1` using `[hxR]`. Establish `k3 : (eqMat Z S).submatrix e id *ᵥ ((fun q : S => x q.1.1 q.1.2) - fun q : S => (z q : K)) = 0`. Rewrite using `[Matrix.mulVec_sub]`.

Use `k1.trans k2.symm` as an intermediate fact. Rewrite `this` using `[add_right_inj]`. Rewrite using `[this, sub_self]`. Conclude with `sub_eq_zero.1 (Matrix.eq_zero_of_mulVec_eq_zero he k3)`. Use `⟨x, hx, ?_, ?_⟩` and prove the remaining obligations.

Introduce `i j`. Distinguish the cases in `hij : j ≤ i`. Conclude with `⟨0, Submodule.mem_top, by simp [hx.1 i j hij]⟩`. Distinguish the cases in `hR' : (i, j) ∈ R`. Conclude with `⟨y ⟨(i, j), hR'⟩, Submodule.mem_top, (hxy ⟨(i, j), hR'⟩).symm⟩`.

Establish `hS : (i, j) ∈ S`. Simplify using `only [hSdef, coRoots, Finset.mem_filter, Finset.mem_univ, true_and]`. Conclude with `⟨lt_of_not_ge hij, hR'⟩`. Conclude with `⟨z ⟨(i, j), hS⟩, Submodule.mem_top, (congrFun hxz ⟨(i, j), hS⟩).symm⟩`. Introduce `v`.

Establish `h2 : M v *ᵥ c v = M v *ᵥ (fun q : R => τ v ((U * x * U⁻¹) q.1.1 q.1.2))`. Rewrite using `[hMy v, hMx x hsx v]`. Use function extensionality and compare the values at `q`. Simplify using `[hxy]`. Conclude with `congrFun (hMinj v _ _ h2)`.

Take `⟨Ω, hΩm, hΩf, hΩv⟩` from `exists_domain K ι τ hτ R H hHi M hM Λ hΛ'`. Use `⟨Ω, hΩm, hΩf, hΩv.trans (ENNReal.ofReal_le_ofReal ?_)⟩` and prove the remaining obligations. Establish `hmult : ∀ w : InfinitePlace K, w.mult = 2` using `fun w => InfinitePlace.mult_isComplex ⟨w, hTC.isComplex w⟩`. Establish `hDK : ((Do.det : 𝓞 K) : K) = ((eqMat Z S).submatrix e id).det` using `hDdet`. Establish `hSup : ∀ q ∈ S, q.1 < q.2` using `fun q hq => (Finset.mem_filter.1 hq).2.1`.

Establish `hidx : (H.index : ℝ) ≤ ((4 * (N : ℝ) ^ 2) ^ Fintype.card ι * B ^ 4) ^ (N ^ 2)`. Use `hHle.trans ?_` and prove the remaining obligations. Establish `hp : ∏ w : InfinitePlace K, w ((Do.det : 𝓞 K) : K) ^ w.mult = ∏ v, ‖τ v (((eqMat Z S).submatrix e id).det)‖ ^ 2`. Use `(Fintype.prod_bijective _ hbij _ _ (fun v => ?_)).symm` and prove the remaining obligations. Rewrite using `[hmult, hDK, InfinitePlace.apply]`.

Rewrite using `[hp]`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[Finset.prod_pow, Finset.prod_mul_distrib, Finset.prod_const, Finset.prod_pow, Finset.card_univ]`. Use `_ ≤ ((4 * (N : ℝ) ^ 2) ^ Fintype.card ι * B ^ 4) ^ N ^ 2 := by`. Establish `h0 : 0 ≤ ∏ v, max 1 (Bv v)` using `Finset.prod_nonneg (fun v _ => le_trans zero_le_one (le_max_left _ _))`.

Use `gcongr`. Establish `hd1 : (1 : ℝ) ≤ |(discr K : ℝ)|` using `by exact_mod_cast Int.one_le_abs (discr_ne_zero K)`. Establish `ha : (1 : ℝ) ≤ |(discr K : ℝ)| ^ (1 / 2 : ℝ)` using `Real.one_le_rpow hd1 (by norm_num)`. Establish `hcard : Fintype.card R ≤ N ^ 2`. Simplify `Finset.card_le_univ R` using `[Fintype.card_coe, sq]`.

Establish `hpow : (|(discr K : ℝ)| ^ (1 / 2 : ℝ)) ^ Fintype.card R ≤ (|(discr K : ℝ)| ^ (1 / 2 : ℝ)) ^ (N ^ 2)` using `pow_le_pow_right₀ ha hcard`. Establish `hC : 0 ≤ ((4 * (N : ℝ) ^ 2) ^ Fintype.card ι * B ^ 4) ^ (N ^ 2)` using `le_trans (Nat.cast_nonneg _) hidx`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem domain_of_cell [NumberField K] (ι : Type) [Fintype ι] (τ : ι → (K →+* ℂ)) {Z U : Matrix (Fin N) (Fin N) K}
    {R : Finset (Fin N × Fin N)} (B : ℝ) (Bv : ι → ℝ) (hτ : ∀ w : InfinitePlace K, ∃! v, InfinitePlace.mk (τ v) = w)
    (hrk : finrank ℚ K = 2 * Fintype.card ι) (hU : IsUpUni U) (hZ : EntIn ⊤ Z)
    (hBv : ∀ (t : ℕ) (I J : Fin t → Fin N) (v : ι), ‖τ v ((Z.submatrix I J).det)‖ ≤ Bv v)
    (hprod : ∏ v, max 1 (Bv v) ≤ B) (hR : ∀ q ∈ R, q.1 < q.2)
    (hc : ∀ x, x ∈ lieU Z ↔ ∀ i j, (i, j) ∉ R → (U * x * U⁻¹) i j = 0) (Λ : Submodule ℤ (ι → R → ℂ))
    (hΛ : ∀ c, c ∈ Λ ↔ ∃ x ∈ lieU Z, EntIn ⊤ x ∧ ∀ v (q : R), c v q = τ v ((U * x * U⁻¹) q.1.1 q.1.2)) :
    ∃ Ω : Set (ι → R → ℂ), MeasurableSet Ω ∧ IsAddFundamentalDomain Λ Ω volume ∧ volume Ω ≤
      ENNReal.ofReal ((|(discr K : ℝ)| ^ (1 / 2 : ℝ)) ^ (N ^ 2) *
        ((4 * (N : ℝ) ^ 2) ^ (Fintype.card ι) * B ^ 4) ^ (N ^ 2)) := by
  classical
  obtain ⟨hbij, hTC⟩ := bijective_mk_and_isTotallyComplex_of_unique_place ι τ hτ hrk
  choose FinalForm _ hZo using hZ
  set Z' : Matrix (Fin N) (Fin N) (𝓞 K) := Matrix.of FinalForm with hZ'
  have hZmap : Z'.map (algebraMap (𝓞 K) K) = Z := by
    ext i j; simp [Z', hZo]
  set S := coRoots R with hSdef
  have hinj := eqMat_injective hU hR hc
  obtain ⟨e, he⟩ := exists_rows _ hinj
  set Ao : Matrix S R (𝓞 K) := (eqMat Z' R).submatrix e id with hAodef
  set Do : Matrix S S (𝓞 K) := (eqMat Z' S).submatrix e id with hDodef
  have hAo : Ao.map (algebraMap (𝓞 K) K) = (eqMat Z R).submatrix e id := by
    rw [← hZmap, ← eqMat_map_ringHom]; rfl
  have hDo : Do.map (algebraMap (𝓞 K) K) = (eqMat Z S).submatrix e id := by
    rw [← hZmap, ← eqMat_map_ringHom]; rfl
  have hDdet : algebraMap (𝓞 K) K Do.det = ((eqMat Z S).submatrix e id).det := by
    rw [RingHom.map_det]; exact congrArg Matrix.det hDo
  have hD : Do.det ≠ 0 := by
    intro h; apply he; rw [← hDdet, h, map_zero]
  obtain ⟨H, hH, hHi, hHle⟩ := index_le K R S Ao Do hD
  set M : ι → Matrix R R ℂ := fun v => (conjMat U R).map (τ v) with hMdef
  have hM : ∀ v, (M v).det = 1 := fun v => by
    rw [show M v = (τ v).mapMatrix (conjMat U R) from rfl, ← RingHom.map_det, det_conjMat hU, map_one]
  have hMinj : ∀ v (a b : R → ℂ), M v *ᵥ a = M v *ᵥ b → a = b := fun v a b h =>
    sub_eq_zero.1 (Matrix.eq_zero_of_mulVec_eq_zero (by rw [hM v]; exact one_ne_zero)
      (by rw [Matrix.mulVec_sub, h, sub_self]))
  have hMx : ∀ x : Matrix (Fin N) (Fin N) K, (∀ i j, (i, j) ∉ R → (U * x * U⁻¹) i j = 0) → ∀ v,
      M v *ᵥ (fun q : R => τ v ((U * x * U⁻¹) q.1.1 q.1.2)) = fun q : R => τ v (x q.1.1 q.1.2) := by
    intro x hsx v
    funext q
    have h := RingHom.map_mulVec (τ v) (conjMat U R) (fun q : R => (U * x * U⁻¹) q.1.1 q.1.2) q
    rw [conjMat_mulVec hU hsx] at h
    exact h.symm
  have hrows : ∀ x : Matrix (Fin N) (Fin N) K, x ∈ lieU Z →
      (eqMat Z R).submatrix e id *ᵥ (fun q : R => x q.1.1 q.1.2) +
        (eqMat Z S).submatrix e id *ᵥ (fun q : S => x q.1.1 q.1.2) = 0 := by
    intro x hx
    funext s
    exact congrFun ((mem_lieU_iff hR hx.1).1 hx) (e s)
  have hΛ' : ∀ c, c ∈ Λ ↔ ∃ y ∈ H, ∀ v, M v *ᵥ c v = fun q => τ v (y q) := by
    intro c
    rw [hΛ c]
    constructor
    · rintro ⟨x, hx, hxi, hcx⟩
      choose xo _ hxo using hxi
      have hsx := (hc x).1 hx
      refine ⟨fun q => xo q.1.1 q.1.2, ?_, ?_⟩
      · rw [hH]
        refine ⟨fun s => xo s.1.1 s.1.2, ?_⟩
        funext s
        apply RingOfIntegers.coe_injective
        have key := congrFun (hrows x hx) s
        have e1 := RingHom.map_mulVec (algebraMap (𝓞 K) K) Ao (fun q : R => xo q.1.1 q.1.2) s
        have e2 := RingHom.map_mulVec (algebraMap (𝓞 K) K) Do (fun q : S => xo q.1.1 q.1.2) s
        rw [hAo] at e1
        rw [hDo] at e2
        have e3 : (algebraMap (𝓞 K) K ∘ fun q : R => xo q.1.1 q.1.2) = fun q : R => x q.1.1 q.1.2 := by
          funext q; exact hxo _ _
        have e4 : (algebraMap (𝓞 K) K ∘ fun q : S => xo q.1.1 q.1.2) = fun q : S => x q.1.1 q.1.2 := by
          funext q; exact hxo _ _
        rw [e3] at e1
        rw [e4] at e2
        have : algebraMap (𝓞 K) K ((Ao *ᵥ fun q : R => xo q.1.1 q.1.2) s + (Do *ᵥ fun q : S => xo q.1.1 q.1.2) s) = 0 := by
          rw [map_add, e1, e2]; exact key
        simpa using this
      · intro v
        rw [show c v = fun q : R => τ v ((U * x * U⁻¹) q.1.1 q.1.2) from funext (hcx v), hMx x hsx v]
        funext q
        simp [hxo]
    · rintro ⟨y, hy, hMy⟩
      obtain ⟨z, hz⟩ := (hH y).1 hy
      obtain ⟨x, hsx, hxy⟩ := exists_lie hU (fun q : R => (y q : K))
      have hx : x ∈ lieU Z := (hc x).2 hsx
      have hxz : (fun q : S => x q.1.1 q.1.2) = fun q : S => (z q : K) := by
        have k1 := hrows x hx
        have k2 : (eqMat Z R).submatrix e id *ᵥ (fun q : R => (y q : K)) +
            (eqMat Z S).submatrix e id *ᵥ (fun q : S => (z q : K)) = 0 := by
          funext s
          have e1 := RingHom.map_mulVec (algebraMap (𝓞 K) K) Ao y s
          have e2 := RingHom.map_mulVec (algebraMap (𝓞 K) K) Do z s
          rw [hAo] at e1
          rw [hDo] at e2
          have := congrArg (algebraMap (𝓞 K) K) (congrFun hz s)
          rw [Pi.add_apply, map_add, e1, e2] at this
          exact this
        have hxR : (fun q : R => x q.1.1 q.1.2) = fun q : R => (y q : K) := funext hxy
        rw [hxR] at k1
        have k3 : (eqMat Z S).submatrix e id *ᵥ ((fun q : S => x q.1.1 q.1.2) - fun q : S => (z q : K)) = 0 := by
          rw [Matrix.mulVec_sub]
          have := k1.trans k2.symm
          rw [add_right_inj] at this
          rw [this, sub_self]
        exact sub_eq_zero.1 (Matrix.eq_zero_of_mulVec_eq_zero he k3)
      refine ⟨x, hx, ?_, ?_⟩
      · intro i j
        by_cases hij : j ≤ i
        · exact ⟨0, Submodule.mem_top, by simp [hx.1 i j hij]⟩
        · by_cases hR' : (i, j) ∈ R
          · exact ⟨y ⟨(i, j), hR'⟩, Submodule.mem_top, (hxy ⟨(i, j), hR'⟩).symm⟩
          · have hS : (i, j) ∈ S := by
              simp only [hSdef, coRoots, Finset.mem_filter, Finset.mem_univ, true_and]
              exact ⟨lt_of_not_ge hij, hR'⟩
            exact ⟨z ⟨(i, j), hS⟩, Submodule.mem_top, (congrFun hxz ⟨(i, j), hS⟩).symm⟩
      · intro v
        have h2 : M v *ᵥ c v = M v *ᵥ (fun q : R => τ v ((U * x * U⁻¹) q.1.1 q.1.2)) := by
          rw [hMy v, hMx x hsx v]
          funext q
          simp [hxy]
        exact congrFun (hMinj v _ _ h2)
  obtain ⟨Ω, hΩm, hΩf, hΩv⟩ := exists_domain K ι τ hτ R H hHi M hM Λ hΛ'
  refine ⟨Ω, hΩm, hΩf, hΩv.trans (ENNReal.ofReal_le_ofReal ?_)⟩
  have hmult : ∀ w : InfinitePlace K, w.mult = 2 := fun w => InfinitePlace.mult_isComplex ⟨w, hTC.isComplex w⟩
  have hDK : ((Do.det : 𝓞 K) : K) = ((eqMat Z S).submatrix e id).det := hDdet
  have hSup : ∀ q ∈ S, q.1 < q.2 := fun q hq => (Finset.mem_filter.1 hq).2.1
  have hidx : (H.index : ℝ) ≤ ((4 * (N : ℝ) ^ 2) ^ Fintype.card ι * B ^ 4) ^ (N ^ 2) := by
    refine hHle.trans ?_
    have hp : ∏ w : InfinitePlace K, w ((Do.det : 𝓞 K) : K) ^ w.mult =
        ∏ v, ‖τ v (((eqMat Z S).submatrix e id).det)‖ ^ 2 := by
      refine (Fintype.prod_bijective _ hbij _ _ (fun v => ?_)).symm
      rw [hmult, hDK, InfinitePlace.apply]
    rw [hp]
    calc ∏ v, ‖τ v (((eqMat Z S).submatrix e id).det)‖ ^ 2
        ≤ ∏ v, (4 * (N : ℝ) ^ 2 * max 1 (Bv v) ^ 4) ^ N ^ 2 :=
          Finset.prod_le_prod (fun v _ => by positivity)
            (fun v _ => norm_det_eqMat_le (τ v) Z (Bv v) (fun t I J => hBv t I J v) S hSup e)
      _ = ((4 * (N : ℝ) ^ 2) ^ Fintype.card ι * (∏ v, max 1 (Bv v)) ^ 4) ^ N ^ 2 := by
          rw [Finset.prod_pow, Finset.prod_mul_distrib, Finset.prod_const, Finset.prod_pow, Finset.card_univ]
      _ ≤ ((4 * (N : ℝ) ^ 2) ^ Fintype.card ι * B ^ 4) ^ N ^ 2 := by
          have h0 : 0 ≤ ∏ v, max 1 (Bv v) := Finset.prod_nonneg (fun v _ => le_trans zero_le_one (le_max_left _ _))
          gcongr
  have hd1 : (1 : ℝ) ≤ |(discr K : ℝ)| := by exact_mod_cast Int.one_le_abs (discr_ne_zero K)
  have ha : (1 : ℝ) ≤ |(discr K : ℝ)| ^ (1 / 2 : ℝ) := Real.one_le_rpow hd1 (by norm_num)
  have hcard : Fintype.card R ≤ N ^ 2 := by
    simpa [Fintype.card_coe, sq] using Finset.card_le_univ R
  have hpow : (|(discr K : ℝ)| ^ (1 / 2 : ℝ)) ^ Fintype.card R ≤ (|(discr K : ℝ)| ^ (1 / 2 : ℝ)) ^ (N ^ 2) :=
    pow_le_pow_right₀ ha hcard
  have hC : 0 ≤ ((4 * (N : ℝ) ^ 2) ^ Fintype.card ι * B ^ 4) ^ (N ^ 2) := le_trans (Nat.cast_nonneg _) hidx
  calc (H.index : ℝ) * (|(discr K : ℝ)| ^ (1 / 2 : ℝ)) ^ Fintype.card R
      ≤ ((4 * (N : ℝ) ^ 2) ^ Fintype.card ι * B ^ 4) ^ (N ^ 2) * (|(discr K : ℝ)| ^ (1 / 2 : ℝ)) ^ (N ^ 2) :=
        mul_le_mul hidx hpow (by positivity) hC
    _ = _ := mul_comm _ _

/- English proof (translation)
Introduce `K _ _ _ ι _ τ N L U p B Bv _ hτ hrk hL hU hZ _ hBv hprod Λ hΛ`. Take `⟨-, h2, -, h4⟩` from `GlobalTheory.LoopV.Cell.stab_cell K N L U p hL hU`. Conclude with `domain_of_cell ι τ B Bv hτ hrk hU hZ hBv hprod (fun q hq => (Finset.mem_filter.1 hq).2.1) (fun x => (h2 x).trans (h4 _)) Λ hΛ`.
-/
theorem lie_lattice_domain : ∀ (K : Type) [Field K] [NumberField K] [StarRing K] (ι : Type) [Fintype ι] (τ : ι → (K →+* ℂ)) (N : ℕ) (L U : Matrix (Fin N) (Fin N) K) (p : Point K N) (B : ℝ) (Bv : ι → ℝ), (∀ v a, τ v (star a) = starRingEnd ℂ (τ v a)) → (∀ w : InfinitePlace K, ∃! v, InfinitePlace.mk (τ v) = w) → finrank ℚ K = 2 * Fintype.card ι → IsLoUni L → IsUpUni U → EntIn ⊤ (L * ptMat p * U) → 1 ≤ B → (∀ (t : ℕ) (I J : Fin t → Fin N) (v : ι), ‖τ v (((L * ptMat p * U).submatrix I J).det)‖ ≤ Bv v) → ∏ v, max 1 (Bv v) ≤ B → ∀ Λ : Submodule ℤ (ι → roots (ptMat p) → ℂ), (∀ c, c ∈ Λ ↔ ∃ x ∈ lieU (L * ptMat p * U), EntIn ⊤ x ∧ ∀ v (q : roots (ptMat p)), c v q = τ v ((U * x * U⁻¹) q.1.1 q.1.2)) → ∃ Ω : Set (ι → roots (ptMat p) → ℂ), MeasurableSet Ω ∧ MeasureTheory.IsAddFundamentalDomain Λ Ω MeasureTheory.volume ∧ MeasureTheory.volume Ω ≤ ENNReal.ofReal ((|(discr K : ℝ)| ^ (1 / 2 : ℝ)) ^ (N ^ 2) * ((4 * (N : ℝ) ^ 2) ^ (Fintype.card ι) * B ^ 4) ^ (N ^ 2)) := by
  intro K _ _ _ ι _ τ N L U p B Bv _ hτ hrk hL hU hZ _ hBv hprod Λ hΛ
  obtain ⟨-, h2, -, h4⟩ := GlobalTheory.LoopV.Cell.stab_cell K N L U p hL hU
  exact domain_of_cell ι τ B Bv hτ hrk hU hZ hBv hprod
    (fun q hq => (Finset.mem_filter.1 hq).2.1) (fun x => (h2 x).trans (h4 _)) Λ hΛ

end GlobalTheory.LieCovol

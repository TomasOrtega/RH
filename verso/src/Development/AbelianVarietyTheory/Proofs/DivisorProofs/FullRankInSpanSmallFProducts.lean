import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiffsZeroOfLev
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FullRk
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FullRankCoinvariantInducedIso
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FullRankNormalFormOrbit
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FullRankZetaSurjective
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzBruhatBoxDecomposition
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegrableFullRankZeta
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.DescB
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
attribute [-instance] Formalism.DoubleCosetMeasures.instMeasGL

namespace GlobalTheory.FullRankCoinv.SpanProd
open GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.RankCoinv ValuativeRel

/- English proof (translation)
Introduce `k _ _ _ _ _ _ n d ν hnd hν`. Take `⟨_, _⟩` from `GlobalTheory.SplitWeil.Model.secondCountable_and_t2_local_field (k := k)`. Take `⟨ϖ, hϖ⟩` from `GlobalTheory.SplitFlip.exists_isUnif (k := k)`. Establish `hU₁ : {g : GL (Fin n) k | g ∈ KO k (Fin n) ∧ ν (gdet g) = 1} ∈ 𝓝 (1 : GL (Fin n) k)`. Use `Filter.inter_mem (isOpen_KO.mem_nhds (one_mem _)) ?_` and prove the remaining obligations.

Establish `ho : IsOpen ((fun g : GL (Fin n) k => gdet g) ⁻¹' (ν.ker : Set kˣ))` using `hν.preimage (GlobalTheory.FullRankCoinv.continuous_gdet n)`. Establish `h1 : (1 : GL (Fin n) k) ∈ (fun g : GL (Fin n) k => gdet g) ⁻¹' (ν.ker : Set kˣ)`. Simplify using `[MonoidHom.mem_ker]`. Use `filter_upwards [ho.mem_nhds h1] with g hg`. Conclude with `hg`.

Rewrite `hU₁` using `[isEmbedding_val_GL.isInducing.nhds_eq_comap, Filter.mem_comap]`. Take `⟨O, hO, hOU⟩` from `hU₁`. Establish `hdet : {M : Matrix (Fin n) (Fin n) k | M.det ≠ 0} ∈ 𝓝 (1 : Matrix (Fin n) (Fin n) k)` using `(isOpen_ne_fun (continuous_id.matrix_det) continuous_const).mem_nhds (by simp)`. Establish `ht : Tendsto (fun Y : Matrix (Fin n) (Fin d) k => Y * (GlobalTheory.FullRankCoinv.Y0 k n d)ᵀ) (𝓝 (GlobalTheory.FullRankCoinv.Y0 k n d)) (𝓝 1)`. Use `((continuous_id.matrix_mul continuous_const : Continuous fun Y : Matrix (Fin n) (Fin d) k => Y * (GlobalTheory.FullRankCoinv.Y0 k n d)ᵀ)).tendsto (GlobalTheory.FullRankCoinv.Y0 k n d)` as an intermediate fact.

Simplify `this` using `only [id, GlobalTheory.FullRankOnto.Y0_mul_transpose hnd]`. Take `⟨m, hm⟩` from `GlobalTheory.RankCoinv.Decomp.exists_box_subset hϖ (ht (Filter.inter_mem hO hdet))`. Establish `hrank : ∀ Y ∈ box ϖ (GlobalTheory.FullRankCoinv.Y0 k n d) (fun _ => m), Y.rank = n`. Introduce `Y hY`. Establish `h1 : (Y * (GlobalTheory.FullRankCoinv.Y0 k n d)ᵀ).det ≠ 0` using `(hm hY).2`.

Use `le_antisymm (by simpa using Matrix.rank_le_height Y) ?_` and prove the remaining obligations. Establish `h2` using `Matrix.rank_mul_le_left Y (GlobalTheory.FullRankCoinv.Y0 k n d)ᵀ`. Establish `h3 : (Y * (GlobalTheory.FullRankCoinv.Y0 k n d)ᵀ).rank = n`. Rewrite using `[Matrix.rank_of_isUnit _ ((Matrix.isUnit_iff_isUnit_det _).2 (isUnit_iff_ne_zero.2 h1)), Fintype.card_fin]`. Use linear arithmetic over natural numbers and integers.

Use `⟨boxFn ϖ (GlobalTheory.FullRankCoinv.Y0 k n d) (fun _ => m), ⟨boxFn_mem_SB ϖ _ _, fun Y hY => Set.indicator_of_notMem (fun h => hY (hrank Y h)) _⟩, ?_⟩` and prove the remaining obligations. Use `set A : Set (GL (Fin n) k) := {g | g.val * GlobalTheory.FullRankCoinv.Y0 k n d ∈ box ϖ (GlobalTheory.FullRankCoinv.Y0 k n d) (fun _ => m)} with hAdef`. Establish `hA : ∀ g ∈ A, g ∈ KO k (Fin n) ∧ ν (gdet g) = 1`. Introduce `g hg`. Apply `hOU` to reduce the goal to its premises.

Use `(hm hg).1` as an intermediate fact. Simplify `this` using `only [Set.mem_preimage, Matrix.mul_assoc, GlobalTheory.FullRankOnto.Y0_mul_transpose hnd, Matrix.mul_one]`. Establish `hint : (fun g : GL (Fin n) k => boxFn ϖ (GlobalTheory.FullRankCoinv.Y0 k n d) (fun _ => m) (g.val * GlobalTheory.FullRankCoinv.Y0 k n d) * (ν (gdet g) : ℂ) * apow (gdet g) ((Fintype.card (Fin d) : ℂ) / 2)) = A.indicator (fun _ => (1 : ℂ))`. Use function extensionality and compare the values at `g`. Distinguish the cases in `hg : g ∈ A`.

Rewrite using `[Set.indicator_of_mem hg]`. Take `⟨hK, hν1⟩` from `hA g hg`. Establish `hb : boxFn ϖ (GlobalTheory.FullRankCoinv.Y0 k n d) (fun _ => m) (g.val * GlobalTheory.FullRankCoinv.Y0 k n d) = 1`. Simplify using `only [boxFn]`. Conclude with `Set.indicator_of_mem (show g.val * GlobalTheory.FullRankCoinv.Y0 k n d ∈ box ϖ (GlobalTheory.FullRankCoinv.Y0 k n d) (fun _ => m) from hg) _`.

Rewrite using `[hb, hν1, apow_of_valuation_eq_one (valuation_gdet_of_mem_KO hK)]`. Simplify using the standard rewrite rules. Rewrite using `[Set.indicator_of_notMem hg]`. Establish `hb : boxFn ϖ (GlobalTheory.FullRankCoinv.Y0 k n d) (fun _ => m) (g.val * GlobalTheory.FullRankCoinv.Y0 k n d) = 0`. Simplify using `only [boxFn]`.

Conclude with `Set.indicator_of_notMem (show g.val * GlobalTheory.FullRankCoinv.Y0 k n d ∉ box ϖ (GlobalTheory.FullRankCoinv.Y0 k n d) (fun _ => m) from hg) _`. Rewrite using `[hb]`. Simplify using the standard rewrite rules. Establish `hAo : IsOpen A` using `(isClopen_box ϖ _ _).isOpen.preimage (Units.continuous_val.matrix_mul continuous_const)`. Establish `hAm : @MeasurableSet (GL (Fin n) k) Units.instMeasurableSpace A` using `@IsOpen.measurableSet _ _ _ Units.instMeasurableSpace (@BorelSpace.opensMeasurable _ _ Units.instMeasurableSpace borel_GL) hAo`.

Use `haveI := isHaarMeasure_haarVol (k := k) (n := Fin n) isOpen_KO le_rfl`. Establish `h1A : (1 : GL (Fin n) k) ∈ A`. Simplify using `only [hAdef, Set.mem_setOf_eq, Units.val_one, Matrix.one_mul]`. Conclude with `GlobalTheory.RankCoinv.Decomp.mem_box_self ϖ _ _`. Establish `hpos : haarVol (KO k (Fin n)) A ≠ 0` using `(hAo.measure_pos _ ⟨1, h1A⟩).ne'`.

Establish `hfin : haarVol (KO k (Fin n)) A ≠ ⊤`. Use `ne_top_of_le_ne_top (b := haarVol (KO k (Fin n)) (KO k (Fin n) : Set (GL (Fin n) k))) ?_ (measure_mono fun g hg => (hA g hg).1)` and prove the remaining obligations. Rewrite using `[haarVol_self isOpen_KO le_rfl]`. Conclude with `ENNReal.one_ne_top`. Establish `hI` using `integral_indicator_const (μ := haarVol (KO k (Fin n))) (1 : ℂ) hAm`.

Rewrite using `[smallF, hint]`. Use `erw [hI]`. Simplify using `only [Measure.real, Complex.real_smul, mul_one, ne_eq, Complex.ofReal_eq_zero]`. Conclude with `(ENNReal.toReal_eq_zero_iff _).not.2 (by tauto)`.
-/
theorem exists_smallF_Y0_ne_zero : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k]
    (n d : ℕ) (ν : kˣ →* ℂˣ), n ≤ d → GlobalTheory.SmGL.IsSmoothChar ν →
    ∃ Ψ ∈ GlobalTheory.FullRankCoinv.fullRk k n d,
      GlobalTheory.SplitFlip.smallF (GlobalTheory.SplitFlip.haarVol (GlobalTheory.SplitWeil.KO k (Fin n))) ν Ψ (GlobalTheory.FullRankCoinv.Y0 k n d) ≠ 0 := by
  intro k _ _ _ _ _ _ n d ν hnd hν
  classical
  obtain ⟨_, _⟩ := GlobalTheory.SplitWeil.Model.secondCountable_and_t2_local_field (k := k)
  obtain ⟨ϖ, hϖ⟩ := GlobalTheory.SplitFlip.exists_isUnif (k := k)
  have hU₁ : {g : GL (Fin n) k | g ∈ KO k (Fin n) ∧ ν (gdet g) = 1} ∈ 𝓝 (1 : GL (Fin n) k) := by
    refine Filter.inter_mem (isOpen_KO.mem_nhds (one_mem _)) ?_
    have ho : IsOpen ((fun g : GL (Fin n) k => gdet g) ⁻¹' (ν.ker : Set kˣ)) :=
      hν.preimage (GlobalTheory.FullRankCoinv.continuous_gdet n)
    have h1 : (1 : GL (Fin n) k) ∈ (fun g : GL (Fin n) k => gdet g) ⁻¹' (ν.ker : Set kˣ) := by
      simp [MonoidHom.mem_ker]
    filter_upwards [ho.mem_nhds h1] with g hg
    exact hg
  rw [isEmbedding_val_GL.isInducing.nhds_eq_comap, Filter.mem_comap] at hU₁
  obtain ⟨O, hO, hOU⟩ := hU₁
  have hdet : {M : Matrix (Fin n) (Fin n) k | M.det ≠ 0} ∈ 𝓝 (1 : Matrix (Fin n) (Fin n) k) :=
    (isOpen_ne_fun (continuous_id.matrix_det) continuous_const).mem_nhds (by simp)
  have ht : Tendsto (fun Y : Matrix (Fin n) (Fin d) k => Y * (GlobalTheory.FullRankCoinv.Y0 k n d)ᵀ)
      (𝓝 (GlobalTheory.FullRankCoinv.Y0 k n d)) (𝓝 1) := by
    have := ((continuous_id.matrix_mul continuous_const :
      Continuous fun Y : Matrix (Fin n) (Fin d) k => Y * (GlobalTheory.FullRankCoinv.Y0 k n d)ᵀ)).tendsto
        (GlobalTheory.FullRankCoinv.Y0 k n d)
    simpa only [id, GlobalTheory.FullRankOnto.Y0_mul_transpose hnd] using this
  obtain ⟨m, hm⟩ := GlobalTheory.RankCoinv.Decomp.exists_box_subset hϖ (ht (Filter.inter_mem hO hdet))
  have hrank : ∀ Y ∈ box ϖ (GlobalTheory.FullRankCoinv.Y0 k n d) (fun _ => m), Y.rank = n := by
    intro Y hY
    have h1 : (Y * (GlobalTheory.FullRankCoinv.Y0 k n d)ᵀ).det ≠ 0 := (hm hY).2
    refine le_antisymm (by simpa using Matrix.rank_le_height Y) ?_
    have h2 := Matrix.rank_mul_le_left Y (GlobalTheory.FullRankCoinv.Y0 k n d)ᵀ
    have h3 : (Y * (GlobalTheory.FullRankCoinv.Y0 k n d)ᵀ).rank = n := by
      rw [Matrix.rank_of_isUnit _ ((Matrix.isUnit_iff_isUnit_det _).2 (isUnit_iff_ne_zero.2 h1)), Fintype.card_fin]
    omega
  refine ⟨boxFn ϖ (GlobalTheory.FullRankCoinv.Y0 k n d) (fun _ => m),
    ⟨boxFn_mem_SB ϖ _ _, fun Y hY => Set.indicator_of_notMem (fun h => hY (hrank Y h)) _⟩, ?_⟩
  set A : Set (GL (Fin n) k) := {g | g.val * GlobalTheory.FullRankCoinv.Y0 k n d ∈ box ϖ (GlobalTheory.FullRankCoinv.Y0 k n d) (fun _ => m)}
    with hAdef
  have hA : ∀ g ∈ A, g ∈ KO k (Fin n) ∧ ν (gdet g) = 1 := by
    intro g hg
    apply hOU
    have := (hm hg).1
    simpa only [Set.mem_preimage, Matrix.mul_assoc, GlobalTheory.FullRankOnto.Y0_mul_transpose hnd, Matrix.mul_one] using this
  have hint : (fun g : GL (Fin n) k => boxFn ϖ (GlobalTheory.FullRankCoinv.Y0 k n d) (fun _ => m) (g.val * GlobalTheory.FullRankCoinv.Y0 k n d) *
      (ν (gdet g) : ℂ) * apow (gdet g) ((Fintype.card (Fin d) : ℂ) / 2)) = A.indicator (fun _ => (1 : ℂ)) := by
    funext g
    by_cases hg : g ∈ A
    · rw [Set.indicator_of_mem hg]
      obtain ⟨hK, hν1⟩ := hA g hg
      have hb : boxFn ϖ (GlobalTheory.FullRankCoinv.Y0 k n d) (fun _ => m) (g.val * GlobalTheory.FullRankCoinv.Y0 k n d) = 1 := by
        simp only [boxFn]; exact Set.indicator_of_mem (show g.val * GlobalTheory.FullRankCoinv.Y0 k n d ∈ box ϖ (GlobalTheory.FullRankCoinv.Y0 k n d) (fun _ => m) from hg) _
      rw [hb, hν1, apow_of_valuation_eq_one (valuation_gdet_of_mem_KO hK)]
      simp
    · rw [Set.indicator_of_notMem hg]
      have hb : boxFn ϖ (GlobalTheory.FullRankCoinv.Y0 k n d) (fun _ => m) (g.val * GlobalTheory.FullRankCoinv.Y0 k n d) = 0 := by
        simp only [boxFn]; exact Set.indicator_of_notMem (show g.val * GlobalTheory.FullRankCoinv.Y0 k n d ∉ box ϖ (GlobalTheory.FullRankCoinv.Y0 k n d) (fun _ => m) from hg) _
      rw [hb]; simp
  have hAo : IsOpen A :=
    (isClopen_box ϖ _ _).isOpen.preimage (Units.continuous_val.matrix_mul continuous_const)
  have hAm : @MeasurableSet (GL (Fin n) k) Units.instMeasurableSpace A :=
    @IsOpen.measurableSet _ _ _ Units.instMeasurableSpace
      (@BorelSpace.opensMeasurable _ _ Units.instMeasurableSpace borel_GL) hAo
  haveI := isHaarMeasure_haarVol (k := k) (n := Fin n) isOpen_KO le_rfl
  have h1A : (1 : GL (Fin n) k) ∈ A := by
    simp only [hAdef, Set.mem_setOf_eq, Units.val_one, Matrix.one_mul]; exact GlobalTheory.RankCoinv.Decomp.mem_box_self ϖ _ _
  have hpos : haarVol (KO k (Fin n)) A ≠ 0 := (hAo.measure_pos _ ⟨1, h1A⟩).ne'
  have hfin : haarVol (KO k (Fin n)) A ≠ ⊤ := by
    refine ne_top_of_le_ne_top (b := haarVol (KO k (Fin n)) (KO k (Fin n) : Set (GL (Fin n) k))) ?_
      (measure_mono fun g hg => (hA g hg).1)
    rw [haarVol_self isOpen_KO le_rfl]; exact ENNReal.one_ne_top
  have hI := integral_indicator_const (μ := haarVol (KO k (Fin n))) (1 : ℂ) hAm
  rw [smallF, hint]
  erw [hI]
  simp only [Measure.real, Complex.real_smul, mul_one, ne_eq, Complex.ofReal_eq_zero]
  exact (ENNReal.toReal_eq_zero_iff _).not.2 (by tauto)

end GlobalTheory.FullRankCoinv.SpanProd

noncomputable section
namespace GlobalTheory.FullRankCoinv.SpanProd

open GlobalTheory.SplitFlip GlobalTheory.RankCoinv

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  [MeasurableSpace k] [BorelSpace k] {n d : ℕ}

/- English proof (translation)
Use `⟨Ψ, hΨ, fun Y => (starRingEnd ℂ) (χ Y * c⁻¹), ⟨⟨?_, ?_⟩, ?_⟩, ?_⟩` and prove the remaining obligations. Conclude with `hχ.1.1.comp (fun z => (starRingEnd ℂ) (z * c⁻¹))`. Conclude with `hχ.1.2.comp_left (g := fun z => (starRingEnd ℂ) (z * c⁻¹)) (by simp)`. Introduce `Y hY`. Simplify using `[hχ.2 Y hY]`.

Use function extensionality and compare the values at `Y`. Simplify using `only [Complex.conj_conj]`. Distinguish the cases in `h : χ Y = 0`. Simplify using `[h]`. Rewrite using `[hB Y h]`.

Clear the denominators using the available nonvanishing facts.
-/
theorem mem_gen_of_const (ν : kˣ →* ℂˣ) {Ψ χ : Matrix (Fin n) (Fin d) k → ℂ}
    (hΨ : Ψ ∈ GlobalTheory.FullRankCoinv.fullRk k n d) (hχ : χ ∈ GlobalTheory.FullRankCoinv.fullRk k n d) {c : ℂ} (hc : c ≠ 0)
    (hB : ∀ Y, χ Y ≠ 0 → smallF (haarVol (GlobalTheory.SplitWeil.KO k (Fin n))) ν Ψ Y = c) :
    χ ∈ {ψ : Matrix (Fin n) (Fin d) k → ℂ | ∃ Ψ₁ ∈ GlobalTheory.FullRankCoinv.fullRk k n d,
      ∃ Ψ₂ ∈ GlobalTheory.FullRankCoinv.fullRk k n d,
        ψ = fun Y => smallF (haarVol (GlobalTheory.SplitWeil.KO k (Fin n))) ν Ψ₁ Y * (starRingEnd ℂ) (Ψ₂ Y)} := by
  refine ⟨Ψ, hΨ, fun Y => (starRingEnd ℂ) (χ Y * c⁻¹), ⟨⟨?_, ?_⟩, ?_⟩, ?_⟩
  · exact hχ.1.1.comp (fun z => (starRingEnd ℂ) (z * c⁻¹))
  · exact hχ.1.2.comp_left (g := fun z => (starRingEnd ℂ) (z * c⁻¹)) (by simp)
  · intro Y hY; simp [hχ.2 Y hY]
  · funext Y
    simp only [Complex.conj_conj]
    by_cases h : χ Y = 0
    · simp [h]
    · rw [hB Y h]; field_simp

/- English proof (translation)
Use `⟨⟨?_, ?_⟩, fun Y hY => by simp [Set.indicator_apply, hχ.2 Y hY]⟩` and prove the remaining obligations. Conclude with `(LocallyConstant.indicator ⟨χ, hχ.1.1⟩ hB).isLocallyConstant`. Conclude with `hχ.1.2.mono' fun x hx => subset_tsupport _ fun h => hx (by simp [Set.indicator_apply, h])`.
-/
theorem indicator_mem_fullRk {χ : Matrix (Fin n) (Fin d) k → ℂ} (hχ : χ ∈ GlobalTheory.FullRankCoinv.fullRk k n d)
    {B : Set (Matrix (Fin n) (Fin d) k)} (hB : IsClopen B) : B.indicator χ ∈ GlobalTheory.FullRankCoinv.fullRk k n d := by
  refine ⟨⟨?_, ?_⟩, fun Y hY => by simp [Set.indicator_apply, hχ.2 Y hY]⟩
  · exact (LocallyConstant.indicator ⟨χ, hχ.1.1⟩ hB).isLocallyConstant
  · exact hχ.1.2.mono' fun x hx => subset_tsupport _ fun h => hx (by simp [Set.indicator_apply, h])

/- English proof (translation)
Take `⟨U, hU, hinv⟩` from `GlobalTheory.FullRankCoinv.sb_right_invariant k n d Ψ hΨ`. Establish `hF : ∀ (Y : Matrix (Fin n) (Fin d) k), ∀ u ∈ U, smallF (haarVol (GlobalTheory.SplitWeil.KO k (Fin n))) ν Ψ (Y * u.val) = smallF (haarVol (GlobalTheory.SplitWeil.KO k (Fin n))) ν Ψ Y`. Introduce `Y u hu`. Simplify using `only [smallF]`. Use `congr 1`.

Use function extensionality and compare the values at `g`. Rewrite using `[← Matrix.mul_assoc, hinv u hu]`. Take `⟨h, rfl⟩` from `GlobalTheory.FullRankCoinv.exists_eq_normal_form_mul_of_rank_eq k n d hnd Y hY`. Use `set V : Set (GL (Fin d) k) := {u | h⁻¹ * u * h ∈ U} with hVdef`. Establish `hV : V ∈ 𝓝 1`.

Establish `hc : Continuous fun u : GL (Fin d) k => h⁻¹ * u * h` using `(continuous_const.mul continuous_id).mul continuous_const`. Use `hc.tendsto 1` as an intermediate fact. Simplify using `only [mul_one, inv_mul_cancel] at this`. Conclude with `this hU`. Establish `ht : Filter.Tendsto (fun Z : Matrix (Fin n) (Fin d) k => Z * (h⁻¹).val) (𝓝 (GlobalTheory.FullRankCoinv.Y0 k n d * h.val)) (𝓝 (GlobalTheory.FullRankCoinv.Y0 k n d))`.

Use `((continuous_id.matrix_mul continuous_const : Continuous fun Z : Matrix (Fin n) (Fin d) k => Z * (h⁻¹).val)).tendsto (GlobalTheory.FullRankCoinv.Y0 k n d * h.val)` as an intermediate fact. Simplify `this` using `only [id, Matrix.mul_assoc, Units.mul_inv, Matrix.mul_one]`. Use `filter_upwards [ht (GlobalTheory.FullRankOnto.eventually_Y0_mul hnd hV)] with Z hZ`. Take `⟨u, hu, e⟩` from `hZ`. Establish `e' : Z = (GlobalTheory.FullRankCoinv.Y0 k n d * h.val) * (h⁻¹ * u * h).val`.

Establish `e2 : Z = Z * (h⁻¹).val * h.val`. Rewrite using `[Matrix.mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.mul_one]`. Rewrite using `[e2]`. Simplify using `only at e`. Rewrite using `[e]`.

Simplify using `only [Units.val_mul, Matrix.mul_assoc]`. Rewrite using `[← Matrix.mul_assoc h.val (h⁻¹).val, ← Units.val_mul h h⁻¹, mul_inv_cancel, Units.val_one, Matrix.one_mul]`. Establish `hu' : h⁻¹ * u * h ∈ U` using `hu`. Rewrite using `[e', hF _ _ hu']`.
-/
theorem eventually_smallF_eq (ν : kˣ →* ℂˣ) (hnd : n ≤ d) {Ψ : Matrix (Fin n) (Fin d) k → ℂ}
    (hΨ : Ψ ∈ GlobalTheory.WeilM.SB (Matrix (Fin n) (Fin d) k)) {Y : Matrix (Fin n) (Fin d) k} (hY : Y.rank = n) :
    ∀ᶠ Z in 𝓝 Y, smallF (haarVol (GlobalTheory.SplitWeil.KO k (Fin n))) ν Ψ Z =
      smallF (haarVol (GlobalTheory.SplitWeil.KO k (Fin n))) ν Ψ Y := by
  obtain ⟨U, hU, hinv⟩ := GlobalTheory.FullRankCoinv.sb_right_invariant k n d Ψ hΨ
  have hF : ∀ (Y : Matrix (Fin n) (Fin d) k), ∀ u ∈ U,
      smallF (haarVol (GlobalTheory.SplitWeil.KO k (Fin n))) ν Ψ (Y * u.val) =
        smallF (haarVol (GlobalTheory.SplitWeil.KO k (Fin n))) ν Ψ Y := by
    intro Y u hu
    simp only [smallF]
    congr 1; funext g
    rw [← Matrix.mul_assoc, hinv u hu]
  obtain ⟨h, rfl⟩ := GlobalTheory.FullRankCoinv.exists_eq_normal_form_mul_of_rank_eq k n d hnd Y hY
  set V : Set (GL (Fin d) k) := {u | h⁻¹ * u * h ∈ U} with hVdef
  have hV : V ∈ 𝓝 1 := by
    have hc : Continuous fun u : GL (Fin d) k => h⁻¹ * u * h :=
      (continuous_const.mul continuous_id).mul continuous_const
    have := hc.tendsto 1
    simp only [mul_one, inv_mul_cancel] at this
    exact this hU
  have ht : Filter.Tendsto (fun Z : Matrix (Fin n) (Fin d) k => Z * (h⁻¹).val)
      (𝓝 (GlobalTheory.FullRankCoinv.Y0 k n d * h.val)) (𝓝 (GlobalTheory.FullRankCoinv.Y0 k n d)) := by
    have := ((continuous_id.matrix_mul continuous_const :
      Continuous fun Z : Matrix (Fin n) (Fin d) k => Z * (h⁻¹).val)).tendsto (GlobalTheory.FullRankCoinv.Y0 k n d * h.val)
    simpa only [id, Matrix.mul_assoc, Units.mul_inv, Matrix.mul_one] using this
  filter_upwards [ht (GlobalTheory.FullRankOnto.eventually_Y0_mul hnd hV)] with Z hZ
  obtain ⟨u, hu, e⟩ := hZ
  have e' : Z = (GlobalTheory.FullRankCoinv.Y0 k n d * h.val) * (h⁻¹ * u * h).val := by
    have e2 : Z = Z * (h⁻¹).val * h.val := by
      rw [Matrix.mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.mul_one]
    rw [e2]
    simp only at e
    rw [e]
    simp only [Units.val_mul, Matrix.mul_assoc]
    rw [← Matrix.mul_assoc h.val (h⁻¹).val, ← Units.val_mul h h⁻¹, mul_inv_cancel, Units.val_one, Matrix.one_mul]
  have hu' : h⁻¹ * u * h ∈ U := hu
  rw [e', hF _ _ hu']

/- English proof (translation)
Take `⟨Ψ₀, hΨ₀, hne⟩` from `GlobalTheory.FullRankCoinv.SpanProd.exists_smallF_Y0_ne_zero k n d ν hnd hν`. Take `⟨h, hh⟩` from `GlobalTheory.FullRankCoinv.exists_eq_normal_form_mul_of_rank_eq k n d hnd Y hY`. Set `Ψ : Matrix (Fin n) (Fin d) k → ℂ` to `fun X => Ψ₀ (X * (h⁻¹).val)`. Establish `hΨ : Ψ ∈ GlobalTheory.FullRankCoinv.fullRk k n d`. Set `e : Matrix (Fin n) (Fin d) k ≃ₜ Matrix (Fin n) (Fin d) k` to `{ toFun := fun X => X * (h⁻¹).1 invFun := fun X => X * h.1 left_inv := fun X => by simp [Matrix.mul_assoc] right_inv := fun X => by simp [Matrix.mul_assoc] continuous_toFun := by fun_prop continuous_invFun := by fun_prop }`.

Use `⟨⟨hΨ₀.1.1.comp_continuous e.continuous, hΨ₀.1.2.comp_homeomorph e⟩, fun X hX => hΨ₀.2 _ ?_⟩` and prove the remaining obligations. Rewrite using `[Matrix.rank_mul_eq_left_of_isUnit_det _ _ (Matrix.isUnits_det_units h⁻¹)]` and apply the resulting hypothesis. Establish `hval : smallF (haarVol (GlobalTheory.SplitWeil.KO k (Fin n))) ν Ψ Y = smallF (haarVol (GlobalTheory.SplitWeil.KO k (Fin n))) ν Ψ₀ (GlobalTheory.FullRankCoinv.Y0 k n d)`. Simplify using `only [smallF, Ψ, hh, Matrix.mul_assoc, Units.mul_inv, Matrix.mul_one]`. Take `⟨m, hm⟩` from `GlobalTheory.RankCoinv.Decomp.exists_box_subset hϖ (eventually_smallF_eq ν hnd hΨ.1 hY)`.

Conclude with `⟨Ψ, hΨ, m, by rw [hval]; exact hne, fun Z hZ => hm hZ⟩`.
-/
theorem exists_local (ν : kˣ →* ℂˣ) (hnd : n ≤ d) (hν : GlobalTheory.SmGL.IsSmoothChar ν) {ϖ : kˣ} (hϖ : IsUnif ϖ)
    {Y : Matrix (Fin n) (Fin d) k} (hY : Y.rank = n) :
    ∃ Ψ ∈ GlobalTheory.FullRankCoinv.fullRk k n d, ∃ m : ℕ, smallF (haarVol (GlobalTheory.SplitWeil.KO k (Fin n))) ν Ψ Y ≠ 0 ∧
      ∀ Z ∈ box ϖ Y (fun _ => m), smallF (haarVol (GlobalTheory.SplitWeil.KO k (Fin n))) ν Ψ Z =
        smallF (haarVol (GlobalTheory.SplitWeil.KO k (Fin n))) ν Ψ Y := by
  obtain ⟨Ψ₀, hΨ₀, hne⟩ := GlobalTheory.FullRankCoinv.SpanProd.exists_smallF_Y0_ne_zero k n d ν hnd hν
  obtain ⟨h, hh⟩ := GlobalTheory.FullRankCoinv.exists_eq_normal_form_mul_of_rank_eq k n d hnd Y hY
  let Ψ : Matrix (Fin n) (Fin d) k → ℂ := fun X => Ψ₀ (X * (h⁻¹).val)
  have hΨ : Ψ ∈ GlobalTheory.FullRankCoinv.fullRk k n d := by
    let e : Matrix (Fin n) (Fin d) k ≃ₜ Matrix (Fin n) (Fin d) k :=
      { toFun := fun X => X * (h⁻¹).1
        invFun := fun X => X * h.1
        left_inv := fun X => by simp [Matrix.mul_assoc]
        right_inv := fun X => by simp [Matrix.mul_assoc]
        continuous_toFun := by fun_prop
        continuous_invFun := by fun_prop }
    refine ⟨⟨hΨ₀.1.1.comp_continuous e.continuous, hΨ₀.1.2.comp_homeomorph e⟩, fun X hX => hΨ₀.2 _ ?_⟩
    rwa [Matrix.rank_mul_eq_left_of_isUnit_det _ _ (Matrix.isUnits_det_units h⁻¹)]
  have hval : smallF (haarVol (GlobalTheory.SplitWeil.KO k (Fin n))) ν Ψ Y =
      smallF (haarVol (GlobalTheory.SplitWeil.KO k (Fin n))) ν Ψ₀ (GlobalTheory.FullRankCoinv.Y0 k n d) := by
    simp only [smallF, Ψ, hh, Matrix.mul_assoc, Units.mul_inv, Matrix.mul_one]
  obtain ⟨m, hm⟩ := GlobalTheory.RankCoinv.Decomp.exists_box_subset hϖ (eventually_smallF_eq ν hnd hΨ.1 hY)
  exact ⟨Ψ, hΨ, m, by rw [hval]; exact hne, fun Z hZ => hm hZ⟩

end GlobalTheory.FullRankCoinv.SpanProd

open GlobalTheory.SplitFlip GlobalTheory.RankCoinv in

/- English proof (translation)
Introduce `k _ _ _ _ _ _ n d ν hnd hν φ hφ`. Take `⟨ϖ, hϖ⟩` from `GlobalTheory.SplitFlip.exists_isUnif (k := k)`. Establish `hloc` using `fun (Y : Matrix (Fin n) (Fin d) k) (hY : Y.rank = n) => GlobalTheory.FullRankCoinv.SpanProd.exists_local ν hnd hν hϖ hY`. Use `choose! Ψf hΨf m hm using hloc`. Establish `key : ∀ t : Finset (Matrix (Fin n) (Fin d) k), (∀ Y ∈ t, Y.rank = n) → ∀ χ ∈ GlobalTheory.FullRankCoinv.fullRk k n d, (∀ Z, χ Z ≠ 0 → ∃ Y ∈ t, Z ∈ box ϖ Y (fun _ => m Y)) → χ ∈ Submodule.span ℂ {ψ : Matrix (Fin n) (Fin d) k → ℂ | ∃ Ψ₁ ∈ GlobalTheory.FullRankCoinv.fullRk k n d, ∃ …`.

Introduce `t`. Proceed by induction on `t using Finset.induction_on with`. Consider the case `empty`. Introduce `_ χ _ hcov`. Establish `: χ = 0` using `funext fun Z => by`.

Assume the negation of the conclusion as `h`. Take `⟨Y, hY, _⟩` from `hcov Z h`. Simplify using `at hY`. Rewrite using `[this]`. Conclude with `zero_mem _`.

Consider the case `insert Y t hYt ih`. Introduce `hrk χ hχ hcov`. Establish `hYr : Y.rank = n` using `hrk Y (Finset.mem_insert_self _ _)`. Establish `hBc : IsClopen (box ϖ Y (fun _ => m Y))` using `isClopen_box ϖ Y _`. Rewrite using `[← Set.indicator_self_add_compl (box ϖ Y (fun _ => m Y)) χ]`.

Use `add_mem (Submodule.subset_span ?_) (ih (fun Y' h => hrk Y' (Finset.mem_insert_of_mem h)) _ (GlobalTheory.FullRankCoinv.SpanProd.indicator_mem_fullRk hχ hBc.compl) ?_)` and prove the remaining obligations. Use `GlobalTheory.FullRankCoinv.SpanProd.mem_gen_of_const ν (hΨf Y hYr) (GlobalTheory.FullRankCoinv.SpanProd.indicator_mem_fullRk hχ hBc) (hm Y hYr).1 fun Z hZ => ?_` and prove the remaining obligations. Conclude with `(hm Y hYr).2 Z (Set.mem_of_indicator_ne_zero hZ)`. Introduce `Z hZ`. Establish `hZB : Z ∈ (box ϖ Y (fun _ => m Y))ᶜ` using `Set.mem_of_indicator_ne_zero hZ`.

Establish `hχZ : χ Z ≠ 0` using `by rwa [Set.indicator_of_mem hZB] at hZ`. Take `⟨Y', hY', hZY'⟩` from `hcov Z hχZ`. Break down `Finset.mem_insert.1 hY' with rfl | h` into its components or cases. Conclude with `absurd hZY' hZB`. Conclude with `⟨Y', h, hZY'⟩`.

Take `⟨⟨hlc, hcs⟩, hz⟩` from `hφ`. Establish `hcl : IsClosed (Function.support φ)`. Establish `h` using `(hlc.isOpen_fiber 0).isClosed_compl`. Use `h using 1` and compare the differences between its conclusion and the goal. Use extensionality with `Y`.

Simplify using `[Function.mem_support]`. Establish `hK : IsCompact (Function.support φ)` using `hcs.of_isClosed_subset hcl (subset_tsupport φ)`. Establish `hrk : ∀ Y ∈ Function.support φ, Y.rank = n` using `fun Y hY => by`. Assume the negation of the conclusion as `h`. Conclude with `hY (hz Y h)`.

Take `⟨t₀, ht₀⟩` from `hK.elim_finite_subcover (fun Y : Function.support φ => box ϖ (Y : Matrix (Fin n) (Fin d) k) (fun _ => m Y)) (fun Y => (isClopen_box ϖ _ _).isOpen) (fun Y hY => Set.mem_iUnion.2 ⟨⟨Y, hY⟩, GlobalTheory.RankCoinv.Decomp.mem_box_self ϖ Y _⟩)`. Use `key (t₀.image Subtype.val) ?_ φ ⟨⟨hlc, hcs⟩, hz⟩ ?_` and prove the remaining obligations. Introduce `Y hY`. Take `⟨Y', _, rfl⟩` from `Finset.mem_image.1 hY`. Conclude with `hrk _ Y'.2`.

Introduce `Z hZ`. Take `⟨Y, hY, hZY⟩` from `Set.mem_iUnion₂.1 (ht₀ hZ)`. Conclude with `⟨Y, Finset.mem_image_of_mem _ hY, hZY⟩`.
-/
theorem GlobalTheory.FullRankCoinv.mem_span_smallF_mul_conj : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k]
    (n d : ℕ) (ν : kˣ →* ℂˣ), n ≤ d → GlobalTheory.SmGL.IsSmoothChar ν →
    ∀ φ ∈ GlobalTheory.FullRankCoinv.fullRk k n d, φ ∈ Submodule.span ℂ {ψ : Matrix (Fin n) (Fin d) k → ℂ |
      ∃ Ψ₁ ∈ GlobalTheory.FullRankCoinv.fullRk k n d, ∃ Ψ₂ ∈ GlobalTheory.FullRankCoinv.fullRk k n d,
        ψ = fun Y => GlobalTheory.SplitFlip.smallF (GlobalTheory.SplitFlip.haarVol (GlobalTheory.SplitWeil.KO k (Fin n))) ν Ψ₁ Y * (starRingEnd ℂ) (Ψ₂ Y)} := by
  intro k _ _ _ _ _ _ n d ν hnd hν φ hφ
  classical
  obtain ⟨ϖ, hϖ⟩ := GlobalTheory.SplitFlip.exists_isUnif (k := k)
  have hloc := fun (Y : Matrix (Fin n) (Fin d) k) (hY : Y.rank = n) =>
    GlobalTheory.FullRankCoinv.SpanProd.exists_local ν hnd hν hϖ hY
  choose! Ψf hΨf m hm using hloc
  have key : ∀ t : Finset (Matrix (Fin n) (Fin d) k), (∀ Y ∈ t, Y.rank = n) →
      ∀ χ ∈ GlobalTheory.FullRankCoinv.fullRk k n d, (∀ Z, χ Z ≠ 0 → ∃ Y ∈ t, Z ∈ box ϖ Y (fun _ => m Y)) →
      χ ∈ Submodule.span ℂ {ψ : Matrix (Fin n) (Fin d) k → ℂ |
        ∃ Ψ₁ ∈ GlobalTheory.FullRankCoinv.fullRk k n d, ∃ Ψ₂ ∈ GlobalTheory.FullRankCoinv.fullRk k n d,
          ψ = fun Y => smallF (haarVol (GlobalTheory.SplitWeil.KO k (Fin n))) ν Ψ₁ Y * (starRingEnd ℂ) (Ψ₂ Y)} := by
    intro t
    induction t using Finset.induction_on with
    | empty =>
      intro _ χ _ hcov
      have : χ = 0 := funext fun Z => by
        by_contra h
        obtain ⟨Y, hY, _⟩ := hcov Z h
        simp at hY
      rw [this]; exact zero_mem _
    | insert Y t hYt ih =>
      intro hrk χ hχ hcov
      have hYr : Y.rank = n := hrk Y (Finset.mem_insert_self _ _)
      have hBc : IsClopen (box ϖ Y (fun _ => m Y)) := isClopen_box ϖ Y _
      rw [← Set.indicator_self_add_compl (box ϖ Y (fun _ => m Y)) χ]
      refine add_mem (Submodule.subset_span ?_)
        (ih (fun Y' h => hrk Y' (Finset.mem_insert_of_mem h)) _
          (GlobalTheory.FullRankCoinv.SpanProd.indicator_mem_fullRk hχ hBc.compl) ?_)
      · refine GlobalTheory.FullRankCoinv.SpanProd.mem_gen_of_const ν (hΨf Y hYr)
          (GlobalTheory.FullRankCoinv.SpanProd.indicator_mem_fullRk hχ hBc) (hm Y hYr).1 fun Z hZ => ?_
        exact (hm Y hYr).2 Z (Set.mem_of_indicator_ne_zero hZ)
      · intro Z hZ
        have hZB : Z ∈ (box ϖ Y (fun _ => m Y))ᶜ := Set.mem_of_indicator_ne_zero hZ
        have hχZ : χ Z ≠ 0 := by rwa [Set.indicator_of_mem hZB] at hZ
        obtain ⟨Y', hY', hZY'⟩ := hcov Z hχZ
        rcases Finset.mem_insert.1 hY' with rfl | h
        · exact absurd hZY' hZB
        · exact ⟨Y', h, hZY'⟩
  obtain ⟨⟨hlc, hcs⟩, hz⟩ := hφ
  have hcl : IsClosed (Function.support φ) := by
    have h := (hlc.isOpen_fiber 0).isClosed_compl
    convert h using 1
    ext Y; simp [Function.mem_support]
  have hK : IsCompact (Function.support φ) := hcs.of_isClosed_subset hcl (subset_tsupport φ)
  have hrk : ∀ Y ∈ Function.support φ, Y.rank = n := fun Y hY => by
    by_contra h; exact hY (hz Y h)
  obtain ⟨t₀, ht₀⟩ := hK.elim_finite_subcover (fun Y : Function.support φ => box ϖ (Y : Matrix (Fin n) (Fin d) k)
    (fun _ => m Y)) (fun Y => (isClopen_box ϖ _ _).isOpen)
    (fun Y hY => Set.mem_iUnion.2 ⟨⟨Y, hY⟩, GlobalTheory.RankCoinv.Decomp.mem_box_self ϖ Y _⟩)
  refine key (t₀.image Subtype.val) ?_ φ ⟨⟨hlc, hcs⟩, hz⟩ ?_
  · intro Y hY
    obtain ⟨Y', _, rfl⟩ := Finset.mem_image.1 hY
    exact hrk _ Y'.2
  · intro Z hZ
    obtain ⟨Y, hY, hZY⟩ := Set.mem_iUnion₂.1 (ht₀ hZ)
    exact ⟨Y, Finset.mem_image_of_mem _ hY, hZY⟩

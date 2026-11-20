import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLocPart
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrimitiveFrameDatumZetaIntegralEqSmaller

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes ValuativeRel
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.StdPairCone
open GlobalTheory.Doubling (absE)

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable local instance measFvZetaB {F : Type} [Field F] [NumberField F] (v : Pl F) : MeasurableSpace (Fv F v) := borel _

local instance borelFvZetaB {F : Type} [Field F] [NumberField F] (v : Pl F) : BorelSpace (Fv F v) := ⟨rfl⟩

open GlobalTheory.SplitFlip GlobalTheory.SplitWeil

noncomputable section
namespace GlobalTheory.StdPairZetaB
open GlobalTheory.SplitWeil GlobalTheory.SplitFlip

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

/- English proof (translation)
Use extensionality with `i j`. Simplify using `[blk₁, Matrix.mul_apply]`.
-/
theorem blk₁_mul_left {m a a' : ℕ} (M : Matrix (Fin m) (Fin m) k) (X : Matrix (Fin m) (Fin (a + a')) k) :
    blk₁ (M * X) = M * blk₁ X := by
  ext i j; simp [blk₁, Matrix.mul_apply]

/- English proof (translation)
Use extensionality with `i j`. Simplify using `[blk₂, Matrix.mul_apply]`.
-/
theorem blk₂_mul_left {m a a' : ℕ} (M : Matrix (Fin m) (Fin m) k) (X : Matrix (Fin m) (Fin (a + a')) k) :
    blk₂ (M * X) = M * blk₂ X := by
  ext i j; simp [blk₂, Matrix.mul_apply]

/- English proof (translation)
Introduce `i j` and use `by have hN' : ∀ i j, valuation k (N i j) ≤ valuation k (s : k) := hN change valuation k _ ≤ valuation k (s : k) rw [Matrix.mul_apply] refine Valuation.map_sum_le _ fun l _ => ?_ rw [map_mul] exact (mul_le_mul' (hM i l) (hN' l j)).trans (by rw [one_mul])`.
-/
theorem cball_mul_left {m n : ℕ} {s : kˣ} {M : Matrix (Fin m) (Fin m) k} (hM : ∀ i j, M i j ∈ 𝒪[k])
    {N : Matrix (Fin m) (Fin n) k} (hN : ∀ i j, N i j ∈ cball s) : ∀ i j, (M * N) i j ∈ cball s := fun i j => by
  have hN' : ∀ i j, valuation k (N i j) ≤ valuation k (s : k) := hN
  change valuation k _ ≤ valuation k (s : k)
  rw [Matrix.mul_apply]
  refine Valuation.map_sum_le _ fun l _ => ?_
  rw [map_mul]
  exact (mul_le_mul' (hM i l) (hN' l j)).trans (by rw [one_mul])

/- English proof (translation)
Set `A : Matrix (Fin n) (Fin n) 𝒪[k]` to `fun i j => ⟨g.val i j, h.1 i j⟩`. Establish `e : (algebraMap 𝒪[k] k).mapMatrix A = g.val` using `rfl`. Establish `hu : IsUnit A.det`. Use `(Valuation.integer.integers (valuation k)).isUnit_iff_valuation_eq_one.2 ?_` and prove the remaining obligations. Rewrite using `[RingHom.map_det, e]`.

Conclude with `h.2`. Take `⟨u, hu'⟩` from `(Matrix.isUnit_iff_isUnit_det A).2 hu`. Use `⟨u, Units.ext ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `(algebraMap 𝒪[k] k).mapMatrix u.val = g.val`. Rewrite using `[hu', e]`.
-/
theorem mem_KO_of_isGLO {n : ℕ} (g : GL (Fin n) k) (h : IsGLO g.val) : g ∈ KO k (Fin n) := by
  let A : Matrix (Fin n) (Fin n) 𝒪[k] := fun i j => ⟨g.val i j, h.1 i j⟩
  have e : (algebraMap 𝒪[k] k).mapMatrix A = g.val := rfl
  have hu : IsUnit A.det := by
    refine (Valuation.integer.integers (valuation k)).isUnit_iff_valuation_eq_one.2 ?_
    rw [RingHom.map_det, e]; exact h.2
  obtain ⟨u, hu'⟩ := (Matrix.isUnit_iff_isUnit_det A).2 hu
  refine ⟨u, Units.ext ?_⟩
  change (algebraMap 𝒪[k] k).mapMatrix u.val = g.val
  rw [hu', e]

/- English proof (translation)
Assemble the required witnesses or components as `⟨((mem_KO_iff g).1 h).1, valuation_gdet_of_mem_KO h⟩`.
-/
theorem isGLO_of_mem_KO {n : ℕ} {g : GL (Fin n) k} (h : g ∈ KO k (Fin n)) : IsGLO g.val :=
  ⟨((mem_KO_iff g).1 h).1, valuation_gdet_of_mem_KO h⟩

end GlobalTheory.StdPairZetaB

open GlobalTheory.StdPairZetaB in

/- English proof (translation)
Introduce `k _ _ _ _ _ _ ν ϖ c a a'`. Use `⟨fun Y hY => ?_, fun Y g₂ hg₂ => ?_⟩` and prove the remaining obligations. Establish `h0 : ∀ g : GL (Fin a') k, stdB ν ϖ c a a' (g.val * Y) = 0` using `fun g => by`. Unfold `stdB`. Rewrite using `[dif_neg]`.

Introduce and unpack `⟨h0, -⟩`. Apply `h0` to reduce the goal to its premises. Rewrite using `[blk₂_mul_left, Matrix.det_mul, hY, mul_zero]`. Simplify using `[smallF, h0]`. Use `set d : ℂ := (Fintype.card (Fin (a + a')) : ℂ) / 2 with hd set C : ℂ := (((ν (gdet g₂))⁻¹ : ℂˣ) : ℂ) * apow (gdet g₂) (-d) * Set.indicator {M : Matrix (Fin a') (Fin a) k | ∀ i j, M i j ∈ cball (ϖ ^ c)} 1 ((g₂⁻¹).val * blk₁ Y) with hC set S : Set (GL (Fin a') k) := (fun g => g * g …`.

Establish `hSm : @MeasurableSet (GL (Fin a') k) Units.instMeasurableSpace S`. Use `letI : MeasurableSpace (GL (Fin a') k) := Units.instMeasurableSpace`. Use `haveI : BorelSpace (GL (Fin a') k) := borel_GL`. Conclude with `(isOpen_KO.preimage (continuous_mul_right _)).measurableSet`. Establish `hS1 : (haarVol (KO k (Fin a'))).real S = 1`.

Simplify using `[hSdef, Measure.real, measure_preimage_mul_right, haarVol_self isOpen_KO le_rfl]`. Establish `hint : ∀ g : GL (Fin a') k, stdB ν ϖ c a a' (g.val * Y) * (ν (gdet g) : ℂ) * apow (gdet g) d = S.indicator (fun _ => C) g`. Introduce `g`. Establish `hb₂ : blk₂ (g.val * Y) = g.val * blk₂ Y` using `blk₂_mul_left _ _`. Establish `hb₁ : blk₁ (g.val * Y) = g.val * blk₁ Y` using `blk₁_mul_left _ _`.

Distinguish the cases in `hg : g ∈ S`. Rewrite using `[Set.indicator_of_mem hg]`. Establish `hκ : g * g₂ ∈ KO k (Fin a')` using `hg`. Establish `hG` using `isGLO_of_mem_KO hκ`. Establish `e₂ : blk₂ (g.val * Y) = (g * g₂).val` using `by rw [hb₂, ← hg₂, Units.val_mul]`.

Establish `e₁ : blk₁ (g.val * Y) = (g * g₂).val * ((g₂⁻¹).val * blk₁ Y)`. Rewrite using `[hb₁, ← Matrix.mul_assoc, Units.val_mul, Matrix.mul_assoc g.val, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.mul_one]`. Establish `hgd : gdet g = gdet (g * g₂) * (gdet g₂)⁻¹` using `by rw [gdet_mul]; group`. Establish `hap : apow (gdet g) d = apow (gdet g₂) (-d)`. Rewrite using `[hgd, apow_mul, apow_of_valuation_eq_one (valuation_gdet_of_mem_KO hκ), one_mul, apow_inv]`.

Unfold `stdB`. Distinguish the cases in `hP : ∀ i j, ((g₂⁻¹).val * blk₁ Y) i j ∈ cball (ϖ ^ c)`. Establish `hcond : (blk₂ (g.val * Y)).det ≠ 0 ∧ IsGLO (blk₂ (g.val * Y)) ∧ ∀ i j, blk₁ (g.val * Y) i j ∈ GlobalTheory.SplitWeil.cball (ϖ ^ c)`. Rewrite using `[e₂, e₁]`. Conclude with `⟨(g * g₂).det_ne_zero, hG, cball_mul_left hG.1 hP⟩`.

Rewrite using `[dif_pos hcond, hC, Set.indicator_of_mem (show ((g₂⁻¹).val * blk₁ Y) ∈ {M : Matrix (Fin a') (Fin a) k | ∀ i j, M i j ∈ cball (ϖ ^ c)} from hP), Pi.one_apply, mul_one, hap]`. Establish `hu : Units.mk0 _ hcond.1 = gdet g * gdet g₂` using `Units.ext (by`. Rewrite using `[Units.val_mk0, Units.val_mul, Matrix.GeneralLinearGroup.val_det_apply, Matrix.GeneralLinearGroup.val_det_apply, hb₂, ← hg₂, Matrix.det_mul])`. Rewrite using `[hu, map_mul, mul_inv_rev, Units.val_mul]`. Establish `h1 : ((ν (gdet g))⁻¹ : ℂˣ) * (ν (gdet g) : ℂ) = 1`.

Rewrite using `[← Units.val_mul, inv_mul_cancel, Units.val_one]`. Take the linear combination `((((ν (gdet g₂))⁻¹ : ℂˣ) : ℂ) * apow (gdet g₂) (-d)) * h1`. Establish `hcond : ¬ ((blk₂ (g.val * Y)).det ≠ 0 ∧ IsGLO (blk₂ (g.val * Y)) ∧ ∀ i j, blk₁ (g.val * Y) i j ∈ GlobalTheory.SplitWeil.cball (ϖ ^ c))`. Introduce and unpack `⟨-, -, h3⟩`. Apply `hP` to reduce the goal to its premises.

Establish `hinv` using `(mem_KO_iff (g * g₂)).1 hκ`. Use `cball_mul_left hinv.2 h3` as an intermediate fact. Rewrite `this` using `[e₁, ← Matrix.mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mul]`. Then use the resulting hypothesis. Rewrite using `[dif_neg hcond, hC, Set.indicator_of_notMem (show ((g₂⁻¹).val * blk₁ Y) ∉ {M : Matrix (Fin a') (Fin a) k | ∀ i j, M i j ∈ cball (ϖ ^ c)} from hP)]`. Simplify using the standard rewrite rules.

Rewrite using `[Set.indicator_of_notMem hg]`. Unfold `stdB`. Rewrite using `[dif_neg, zero_mul, zero_mul]`. Introduce and unpack `⟨-, h2, -⟩`. Apply `hg` to reduce the goal to its premises.

Use `show g * g₂ ∈ KO k (Fin a')`. Apply `mem_KO_of_isGLO` to reduce the goal to its premises. Rewrite using `[Units.val_mul, hg₂, ← hb₂]` and apply the resulting hypothesis. Rewrite using `[smallF, ← hd]`. Repeatedly rewrite using `[hint]`.

Rewrite using `[integral_indicator_const (μ := haarVol (KO k (Fin a'))) C hSm, hS1, one_smul]`.
-/
theorem GlobalTheory.StdPairZetaB.smallF_stdB : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    [MeasurableSpace k] [BorelSpace k] (ν : kˣ →* ℂˣ) (ϖ : kˣ) (c a a' : ℕ),
    (∀ Y : Matrix (Fin a') (Fin (a + a')) k, (blk₂ Y).det = 0 →
      smallF (haarVol (KO k (Fin a'))) ν (stdB ν ϖ c a a') Y = 0) ∧
    ∀ (Y : Matrix (Fin a') (Fin (a + a')) k) (g₂ : GL (Fin a') k), g₂.val = blk₂ Y →
      smallF (haarVol (KO k (Fin a'))) ν (stdB ν ϖ c a a') Y =
        (((ν (gdet g₂))⁻¹ : ℂˣ) : ℂ) * apow (gdet g₂) (-((Fintype.card (Fin (a + a')) : ℂ) / 2)) *
          Set.indicator {M : Matrix (Fin a') (Fin a) k | ∀ i j, M i j ∈ cball (ϖ ^ c)} 1 ((g₂⁻¹).val * blk₁ Y) := by
  intro k _ _ _ _ _ _ ν ϖ c a a'
  refine ⟨fun Y hY => ?_, fun Y g₂ hg₂ => ?_⟩
  · have h0 : ∀ g : GL (Fin a') k, stdB ν ϖ c a a' (g.val * Y) = 0 := fun g => by
      unfold stdB
      rw [dif_neg]
      rintro ⟨h0, -⟩
      apply h0
      rw [blk₂_mul_left, Matrix.det_mul, hY, mul_zero]
    simp [smallF, h0]
  · set d : ℂ := (Fintype.card (Fin (a + a')) : ℂ) / 2 with hd
    set C : ℂ := (((ν (gdet g₂))⁻¹ : ℂˣ) : ℂ) * apow (gdet g₂) (-d) *
      Set.indicator {M : Matrix (Fin a') (Fin a) k | ∀ i j, M i j ∈ cball (ϖ ^ c)} 1 ((g₂⁻¹).val * blk₁ Y) with hC
    set S : Set (GL (Fin a') k) := (fun g => g * g₂) ⁻¹' (KO k (Fin a') : Set (GL (Fin a') k)) with hSdef
    have hSm : @MeasurableSet (GL (Fin a') k) Units.instMeasurableSpace S := by
      letI : MeasurableSpace (GL (Fin a') k) := Units.instMeasurableSpace
      haveI : BorelSpace (GL (Fin a') k) := borel_GL
      exact (isOpen_KO.preimage (continuous_mul_right _)).measurableSet
    have hS1 : (haarVol (KO k (Fin a'))).real S = 1 := by
      simp [hSdef, Measure.real, measure_preimage_mul_right, haarVol_self isOpen_KO le_rfl]
    have hint : ∀ g : GL (Fin a') k, stdB ν ϖ c a a' (g.val * Y) * (ν (gdet g) : ℂ) * apow (gdet g) d =
        S.indicator (fun _ => C) g := by
      intro g
      have hb₂ : blk₂ (g.val * Y) = g.val * blk₂ Y := blk₂_mul_left _ _
      have hb₁ : blk₁ (g.val * Y) = g.val * blk₁ Y := blk₁_mul_left _ _
      by_cases hg : g ∈ S
      · rw [Set.indicator_of_mem hg]
        have hκ : g * g₂ ∈ KO k (Fin a') := hg
        have hG := isGLO_of_mem_KO hκ
        have e₂ : blk₂ (g.val * Y) = (g * g₂).val := by rw [hb₂, ← hg₂, Units.val_mul]
        have e₁ : blk₁ (g.val * Y) = (g * g₂).val * ((g₂⁻¹).val * blk₁ Y) := by
          rw [hb₁, ← Matrix.mul_assoc, Units.val_mul, Matrix.mul_assoc g.val, ← Units.val_mul, mul_inv_cancel,
            Units.val_one, Matrix.mul_one]
        have hgd : gdet g = gdet (g * g₂) * (gdet g₂)⁻¹ := by rw [gdet_mul]; group
        have hap : apow (gdet g) d = apow (gdet g₂) (-d) := by
          rw [hgd, apow_mul, apow_of_valuation_eq_one (valuation_gdet_of_mem_KO hκ), one_mul, apow_inv]
        unfold stdB
        by_cases hP : ∀ i j, ((g₂⁻¹).val * blk₁ Y) i j ∈ cball (ϖ ^ c)
        · have hcond : (blk₂ (g.val * Y)).det ≠ 0 ∧ IsGLO (blk₂ (g.val * Y)) ∧
              ∀ i j, blk₁ (g.val * Y) i j ∈ GlobalTheory.SplitWeil.cball (ϖ ^ c) := by
            rw [e₂, e₁]
            exact ⟨(g * g₂).det_ne_zero, hG, cball_mul_left hG.1 hP⟩
          rw [dif_pos hcond, hC, Set.indicator_of_mem (show ((g₂⁻¹).val * blk₁ Y) ∈
            {M : Matrix (Fin a') (Fin a) k | ∀ i j, M i j ∈ cball (ϖ ^ c)} from hP), Pi.one_apply, mul_one, hap]
          have hu : Units.mk0 _ hcond.1 = gdet g * gdet g₂ := Units.ext (by
            rw [Units.val_mk0, Units.val_mul, Matrix.GeneralLinearGroup.val_det_apply,
              Matrix.GeneralLinearGroup.val_det_apply, hb₂, ← hg₂, Matrix.det_mul])
          rw [hu, map_mul, mul_inv_rev, Units.val_mul]
          have h1 : ((ν (gdet g))⁻¹ : ℂˣ) * (ν (gdet g) : ℂ) = 1 := by
            rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
          linear_combination ((((ν (gdet g₂))⁻¹ : ℂˣ) : ℂ) * apow (gdet g₂) (-d)) * h1
        · have hcond : ¬ ((blk₂ (g.val * Y)).det ≠ 0 ∧ IsGLO (blk₂ (g.val * Y)) ∧
              ∀ i j, blk₁ (g.val * Y) i j ∈ GlobalTheory.SplitWeil.cball (ϖ ^ c)) := by
            rintro ⟨-, -, h3⟩
            apply hP
            have hinv := (mem_KO_iff (g * g₂)).1 hκ
            have := cball_mul_left hinv.2 h3
            rwa [e₁, ← Matrix.mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mul] at this
          rw [dif_neg hcond, hC, Set.indicator_of_notMem (show ((g₂⁻¹).val * blk₁ Y) ∉
            {M : Matrix (Fin a') (Fin a) k | ∀ i j, M i j ∈ cball (ϖ ^ c)} from hP)]
          simp
      · rw [Set.indicator_of_notMem hg]
        unfold stdB
        rw [dif_neg, zero_mul, zero_mul]
        rintro ⟨-, h2, -⟩
        apply hg
        show g * g₂ ∈ KO k (Fin a')
        apply mem_KO_of_isGLO
        rwa [Units.val_mul, hg₂, ← hb₂]
    rw [smallF, ← hd]
    simp_rw [hint]
    rw [integral_indicator_const (μ := haarVol (KO k (Fin a'))) C hSm, hS1, one_smul]

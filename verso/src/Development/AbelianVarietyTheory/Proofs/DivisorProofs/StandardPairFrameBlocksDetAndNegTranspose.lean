import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLocPart
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrimitiveFrameDatumZetaIntegralEqSmaller

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes ValuativeRel
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.StdPairCone
open GlobalTheory.Doubling (absE)

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.StdPairLoc
open GlobalTheory.SplitFlip GlobalTheory.SplitWeil

section Helpers
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

/- English proof (translation)
Use extensionality with `i j`. Simplify using `[blk₁, Matrix.mul_apply]`.
-/
theorem blk₁_mul {m m' a a' : ℕ} (M : Matrix (Fin m') (Fin m) k) (X : Matrix (Fin m) (Fin (a + a')) k) :
    blk₁ (M * X) = M * blk₁ X := by
  ext i j; simp [blk₁, Matrix.mul_apply]

/- English proof (translation)
Use extensionality with `i j`. Simplify using `[blk₂, Matrix.mul_apply]`.
-/
theorem blk₂_mul {m m' a a' : ℕ} (M : Matrix (Fin m') (Fin m) k) (X : Matrix (Fin m) (Fin (a + a')) k) :
    blk₂ (M * X) = M * blk₂ X := by
  ext i j; simp [blk₂, Matrix.mul_apply]

/- English proof (translation)
Set `M₀ : Matrix (Fin n) (Fin n) 𝒪[k]` to `fun i j => ⟨g.val i j, hg.1 i j⟩`. Establish `hM : (algebraMap 𝒪[k] k).mapMatrix M₀ = g.val` using `by ext i j; rfl`. Establish `hv : valuation k (algebraMap 𝒪[k] k M₀.det) = 1` using `by rw [RingHom.map_det, hM]; exact hg.2`. Establish `hdet : IsUnit M₀.det` using `(Valuation.integer.integers (valuation k)).isUnit_of_one (isUnit_iff_ne_zero.2 (by rw [RingHom.map_det, hM]; exact g.det_ne_zero)) hv`. Take `⟨u, hu⟩` from `(Matrix.isUnit_iff_isUnit_det M₀).2 hdet`.

Conclude with `⟨u, Units.ext (by rw [← hM, ← hu]; rfl)⟩`.
-/
theorem mem_KO_of_isGLO {n : ℕ} (g : GL (Fin n) k) (hg : IsGLO g.val) : g ∈ KO k (Fin n) := by
  let M₀ : Matrix (Fin n) (Fin n) 𝒪[k] := fun i j => ⟨g.val i j, hg.1 i j⟩
  have hM : (algebraMap 𝒪[k] k).mapMatrix M₀ = g.val := by ext i j; rfl
  have hv : valuation k (algebraMap 𝒪[k] k M₀.det) = 1 := by rw [RingHom.map_det, hM]; exact hg.2
  have hdet : IsUnit M₀.det :=
    (Valuation.integer.integers (valuation k)).isUnit_of_one
      (isUnit_iff_ne_zero.2 (by rw [RingHom.map_det, hM]; exact g.det_ne_zero)) hv
  obtain ⟨u, hu⟩ := (Matrix.isUnit_iff_isUnit_det M₀).2 hdet
  exact ⟨u, Units.ext (by rw [← hM, ← hu]; rfl)⟩

/- English proof (translation)
Use `⟨((mem_KO_iff g).1 hg).1, ?_⟩` and prove the remaining obligations. Simplify `valuation_gdet_of_mem_KO hg` using `[gdet, Matrix.GeneralLinearGroup.val_det_apply]`.
-/
theorem isGLO_of_mem_KO {n : ℕ} {g : GL (Fin n) k} (hg : g ∈ KO k (Fin n)) : IsGLO g.val := by
  refine ⟨((mem_KO_iff g).1 hg).1, ?_⟩
  simpa [gdet, Matrix.GeneralLinearGroup.val_det_apply] using valuation_gdet_of_mem_KO hg

/- English proof (translation)
Introduce `i j`. Use `show valuation k ((κ * N) i j) ≤ valuation k (s : k)`. Rewrite using `[Matrix.mul_apply]`. Use `Valuation.map_sum_le _ fun l _ => ?_` and prove the remaining obligations. Rewrite using `[map_mul]`.

Establish `h1 : valuation k (κ i l) ≤ 1` using `(Valuation.mem_integer_iff _ _).1 (hκ i l)`. Establish `h2 : valuation k (N l j) ≤ valuation k (s : k)` using `hN l j`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem mul_mem_cball {m n p : ℕ} (s : kˣ) (κ : Matrix (Fin m) (Fin n) k) (hκ : ∀ i j, κ i j ∈ 𝒪[k])
    (N : Matrix (Fin n) (Fin p) k) (hN : ∀ i j, N i j ∈ cball s) : ∀ i j, (κ * N) i j ∈ cball s := by
  intro i j
  show valuation k ((κ * N) i j) ≤ valuation k (s : k)
  rw [Matrix.mul_apply]
  refine Valuation.map_sum_le _ fun l _ => ?_
  rw [map_mul]
  have h1 : valuation k (κ i l) ≤ 1 := (Valuation.mem_integer_iff _ _).1 (hκ i l)
  have h2 : valuation k (N l j) ≤ valuation k (s : k) := hN l j
  calc valuation k (κ i l) * valuation k (N l j) ≤ 1 * valuation k (s : k) := mul_le_mul' h1 h2
    _ = _ := one_mul _

/- English proof (translation)
Use `⟨fun h => ?_, fun h => mul_mem_cball s κ.val ((mem_KO_iff κ).1 hκ).1 N h⟩` and prove the remaining obligations. Use `mul_mem_cball s (κ⁻¹).val ((mem_KO_iff κ).1 hκ).2 _ h` as an intermediate fact. Rewrite `this` using `[← Matrix.mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mul]`. Then use the resulting hypothesis.
-/
theorem mem_cball_iff_KO {n p : ℕ} (s : kˣ) {κ : GL (Fin n) k} (hκ : κ ∈ KO k (Fin n)) (N : Matrix (Fin n) (Fin p) k) :
    (∀ i j, (κ.val * N) i j ∈ cball s) ↔ ∀ i j, N i j ∈ cball s := by
  refine ⟨fun h => ?_, fun h => mul_mem_cball s κ.val ((mem_KO_iff κ).1 hκ).1 N h⟩
  have := mul_mem_cball s (κ⁻¹).val ((mem_KO_iff κ).1 hκ).2 _ h
  rwa [← Matrix.mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mul] at this

/- English proof (translation)
Distinguish the cases in `hS : g * g₁ ∈ KO k (Fin n)`. Rewrite using `[Set.indicator_of_mem (show g ∈ (fun g => g * g₁) ⁻¹' (KO k (Fin n) : Set (GL (Fin n) k)) from hS)]`. Establish `hN : (∀ i j, (g.val * N) i j ∈ cball s) ↔ ∀ i j, ((g₁⁻¹).val * N) i j ∈ cball s`. Rewrite using `[← mem_cball_iff_KO s hS ((g₁⁻¹).val * N), ← Matrix.mul_assoc, ← Units.val_mul, mul_inv_cancel_right]`. Distinguish the cases in `hc : ∀ i j, ((g₁⁻¹).val * N) i j ∈ cball s`.

Establish `hP : (g.val * g₁.val).det ≠ 0 ∧ IsGLO (g.val * g₁.val) ∧ ∀ i j, (g.val * N) i j ∈ cball s` using `⟨(g * g₁).det_ne_zero, isGLO_of_mem_KO hS, hN.2 hc⟩`. Rewrite using `[hpos hP, Set.indicator_of_mem (show ((g₁⁻¹).val * N) ∈ {M : Matrix (Fin n) (Fin p) k | ∀ i j, M i j ∈ cball s} from hc)]`. Establish `e1 : Units.mk0 _ hP.1 = gdet g * gdet g₁` using `Units.ext (by simp [gdet, Matrix.GeneralLinearGroup.val_det_apply, Matrix.det_mul])`. Establish `hunit : apow (gdet (g * g₁)) z = 1` using `apow_of_valuation_eq_one (valuation_gdet_of_mem_KO hS) z`. Establish `e2 : apow (gdet g) z = apow (gdet g₁) (-z)`.

Establish `: gdet g = gdet (g * g₁) * (gdet g₁)⁻¹` using `by rw [gdet_mul]; group`. Rewrite using `[this, apow_mul, hunit, one_mul, apow_inv]`. Establish `e3 : (((ν (gdet g))⁻¹ : ℂˣ) : ℂ) * (ν (gdet g) : ℂ) = 1`. Rewrite using `[← Units.val_mul, inv_mul_cancel, Units.val_one]`. Rewrite using `[e1, e2, map_mul, _root_.mul_inv, Units.val_mul, Pi.one_apply]`.

Take the linear combination `(((ν (gdet g₁))⁻¹ : ℂˣ) : ℂ) * apow (gdet g₁) (-z) * e3`. Rewrite using `[hneg (fun h => hc (hN.1 h.2.2)), Set.indicator_of_notMem (show ((g₁⁻¹).val * N) ∉ {M : Matrix (Fin n) (Fin p) k | ∀ i j, M i j ∈ cball s} from hc)]`. Simplify using the standard rewrite rules. Rewrite using `[Set.indicator_of_notMem (show g ∉ (fun g => g * g₁) ⁻¹' (KO k (Fin n) : Set (GL (Fin n) k)) from hS), hneg (fun h => hS (mem_KO_of_isGLO (g * g₁) h.2.1))]`. Simplify using the standard rewrite rules.
-/
theorem integrand_eq {n p : ℕ} (ν : kˣ →* ℂˣ) (s : kˣ) (z : ℂ) (N : Matrix (Fin n) (Fin p) k) (g₁ g : GL (Fin n) k)
    (Φv : ℂ)
    (hpos : ∀ h : (g.val * g₁.val).det ≠ 0 ∧ IsGLO (g.val * g₁.val) ∧ ∀ i j, (g.val * N) i j ∈ cball s,
      Φv = (((ν (Units.mk0 _ h.1))⁻¹ : ℂˣ) : ℂ))
    (hneg : ¬ ((g.val * g₁.val).det ≠ 0 ∧ IsGLO (g.val * g₁.val) ∧ ∀ i j, (g.val * N) i j ∈ cball s) → Φv = 0) :
    Φv * (ν (gdet g) : ℂ) * apow (gdet g) z =
      ((fun g => g * g₁) ⁻¹' (KO k (Fin n) : Set (GL (Fin n) k))).indicator (fun _ =>
        (((ν (gdet g₁))⁻¹ : ℂˣ) : ℂ) * apow (gdet g₁) (-z) *
          Set.indicator {M : Matrix (Fin n) (Fin p) k | ∀ i j, M i j ∈ cball s} 1 ((g₁⁻¹).val * N)) g := by
  by_cases hS : g * g₁ ∈ KO k (Fin n)
  · rw [Set.indicator_of_mem (show g ∈ (fun g => g * g₁) ⁻¹' (KO k (Fin n) : Set (GL (Fin n) k)) from hS)]
    have hN : (∀ i j, (g.val * N) i j ∈ cball s) ↔ ∀ i j, ((g₁⁻¹).val * N) i j ∈ cball s := by
      rw [← mem_cball_iff_KO s hS ((g₁⁻¹).val * N), ← Matrix.mul_assoc, ← Units.val_mul, mul_inv_cancel_right]
    by_cases hc : ∀ i j, ((g₁⁻¹).val * N) i j ∈ cball s
    · have hP : (g.val * g₁.val).det ≠ 0 ∧ IsGLO (g.val * g₁.val) ∧ ∀ i j, (g.val * N) i j ∈ cball s :=
        ⟨(g * g₁).det_ne_zero, isGLO_of_mem_KO hS, hN.2 hc⟩
      rw [hpos hP, Set.indicator_of_mem (show ((g₁⁻¹).val * N) ∈
        {M : Matrix (Fin n) (Fin p) k | ∀ i j, M i j ∈ cball s} from hc)]
      have e1 : Units.mk0 _ hP.1 = gdet g * gdet g₁ :=
        Units.ext (by simp [gdet, Matrix.GeneralLinearGroup.val_det_apply, Matrix.det_mul])
      have hunit : apow (gdet (g * g₁)) z = 1 := apow_of_valuation_eq_one (valuation_gdet_of_mem_KO hS) z
      have e2 : apow (gdet g) z = apow (gdet g₁) (-z) := by
        have : gdet g = gdet (g * g₁) * (gdet g₁)⁻¹ := by rw [gdet_mul]; group
        rw [this, apow_mul, hunit, one_mul, apow_inv]
      have e3 : (((ν (gdet g))⁻¹ : ℂˣ) : ℂ) * (ν (gdet g) : ℂ) = 1 := by
        rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
      rw [e1, e2, map_mul, _root_.mul_inv, Units.val_mul, Pi.one_apply]
      linear_combination (((ν (gdet g₁))⁻¹ : ℂˣ) : ℂ) * apow (gdet g₁) (-z) * e3
    · rw [hneg (fun h => hc (hN.1 h.2.2)), Set.indicator_of_notMem (show ((g₁⁻¹).val * N) ∉
        {M : Matrix (Fin n) (Fin p) k | ∀ i j, M i j ∈ cball s} from hc)]
      simp
  · rw [Set.indicator_of_notMem (show g ∉ (fun g => g * g₁) ⁻¹' (KO k (Fin n) : Set (GL (Fin n) k)) from hS),
      hneg (fun h => hS (mem_KO_of_isGLO (g * g₁) h.2.1))]
    simp

variable [MeasurableSpace k] [BorelSpace k]

/- English proof (translation)
Use `⟨?_, ?_⟩` and prove the remaining obligations. Use `letI : MeasurableSpace (GL (Fin a) k) := Units.instMeasurableSpace haveI : BorelSpace (GL (Fin a) k) := borel_GL`. Conclude with `(isOpen_KO.preimage (continuous_mul_right _)).measurableSet`. Simplify using `[Measure.real, measure_preimage_mul_right, haarVol_self isOpen_KO le_rfl]`.
-/
theorem measurableSet_and_vol {a : ℕ} (g₁ : GL (Fin a) k) :
    @MeasurableSet (GL (Fin a) k) Units.instMeasurableSpace ((fun g => g * g₁) ⁻¹' (KO k (Fin a) : Set (GL (Fin a) k))) ∧
    (haarVol (KO k (Fin a))).real ((fun g => g * g₁) ⁻¹' (KO k (Fin a) : Set (GL (Fin a) k))) = 1 := by
  refine ⟨?_, ?_⟩
  · letI : MeasurableSpace (GL (Fin a) k) := Units.instMeasurableSpace
    haveI : BorelSpace (GL (Fin a) k) := borel_GL
    exact (isOpen_KO.preimage (continuous_mul_right _)).measurableSet
  · simp [Measure.real, measure_preimage_mul_right, haarVol_self isOpen_KO le_rfl]

/- English proof (translation)
Use `set S := (fun g => g * g₁) ⁻¹' (KO k (Fin a) : Set (GL (Fin a) k)) with hSdef`. Take `⟨hSm, hS1⟩` from `measurableSet_and_vol (k := k) g₁`. Take `⟨⟨m₀, hm₀⟩, hmem, huniq⟩` from `GlobalTheory.OneSquareZeta.exists_unique_shell hϖ g₁⁻¹`. Establish `hshell : ∀ m : {m : Fin a → ℤ // Antitone m}, shell (haarVol (KO k (Fin a))) ϖ ν z φ m.1 = (haarVol (KO k (Fin a))).real (shellSet ϖ m.1 ∩ S) • C`. Introduce `m`.

Rewrite using `[shell]`. Repeatedly rewrite using `[hφ]`. Establish `e1` using `setIntegral_indicator (μ := haarVol (KO k (Fin a))) (s := shellSet ϖ m.1) (f := fun _ => C) hSm`. Rewrite using `[e1, setIntegral_const]`. Establish `hsub : S ⊆ shellSet ϖ m₀`.

Introduce `g hg`. Take `⟨x, hx, y, hy, e⟩` from `mem_shellSet.1 hmem`. Use `mem_shellSet.2 ⟨g * g₁ * x, mul_mem hg hx, y, hy, ?_⟩` and prove the remaining obligations. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[shellSum, finsum_eq_single _ ⟨m₀, hm₀⟩]`.

Rewrite using `[hshell, Set.inter_eq_right.2 hsub, hS1, one_smul]`. Introduce `m hm`. Rewrite using `[hshell]`. Establish `: shellSet ϖ m.1 ∩ S = ∅`. Use `Set.eq_empty_of_forall_notMem fun g ⟨hg1, hg2⟩ => hm (huniq m ?_)` and prove the remaining obligations.

Take `⟨x, hx, y, hy, e⟩` from `mem_shellSet.1 hg1`. Use `mem_shellSet.2 ⟨(g * g₁)⁻¹ * x, mul_mem (inv_mem hg2) hx, y, hy, ?_⟩` and prove the remaining obligations. Combine the equalities or inequalities in the displayed calculation. Simplify using `[this]`.
-/
theorem shellSum_indicator {ϖ : kˣ} (hϖ : IsUnif ϖ) {a : ℕ} (ν : kˣ →* ℂˣ) (z C : ℂ)
    (φ : Matrix (Fin a) (Fin a) k → ℂ) (g₁ : GL (Fin a) k)
    (hφ : ∀ g : GL (Fin a) k, φ g.val * (ν (gdet g) : ℂ) * apow (gdet g) z =
      ((fun g => g * g₁) ⁻¹' (KO k (Fin a) : Set (GL (Fin a) k))).indicator (fun _ => C) g) :
    shellSum (haarVol (KO k (Fin a))) ϖ ν z φ = C := by
  set S := (fun g => g * g₁) ⁻¹' (KO k (Fin a) : Set (GL (Fin a) k)) with hSdef
  obtain ⟨hSm, hS1⟩ := measurableSet_and_vol (k := k) g₁
  obtain ⟨⟨m₀, hm₀⟩, hmem, huniq⟩ := GlobalTheory.OneSquareZeta.exists_unique_shell hϖ g₁⁻¹
  have hshell : ∀ m : {m : Fin a → ℤ // Antitone m}, shell (haarVol (KO k (Fin a))) ϖ ν z φ m.1 =
      (haarVol (KO k (Fin a))).real (shellSet ϖ m.1 ∩ S) • C := by
    intro m
    rw [shell]
    simp_rw [hφ]
    have e1 := setIntegral_indicator (μ := haarVol (KO k (Fin a))) (s := shellSet ϖ m.1) (f := fun _ => C) hSm
    rw [e1, setIntegral_const]
  have hsub : S ⊆ shellSet ϖ m₀ := by
    intro g hg
    obtain ⟨x, hx, y, hy, e⟩ := mem_shellSet.1 hmem
    refine mem_shellSet.2 ⟨g * g₁ * x, mul_mem hg hx, y, hy, ?_⟩
    calc g = g * g₁ * g₁⁻¹ := by group
      _ = _ := by rw [e]; simp only [mul_assoc]; try rfl
  rw [shellSum, finsum_eq_single _ ⟨m₀, hm₀⟩]
  · rw [hshell, Set.inter_eq_right.2 hsub, hS1, one_smul]
  · intro m hm
    rw [hshell]
    have : shellSet ϖ m.1 ∩ S = ∅ := by
      refine Set.eq_empty_of_forall_notMem fun g ⟨hg1, hg2⟩ => hm (huniq m ?_)
      obtain ⟨x, hx, y, hy, e⟩ := mem_shellSet.1 hg1
      refine mem_shellSet.2 ⟨(g * g₁)⁻¹ * x, mul_mem (inv_mem hg2) hx, y, hy, ?_⟩
      calc g₁⁻¹ = (g * g₁)⁻¹ * g := by group
        _ = _ := by rw [e]; simp only [mul_assoc]; try rfl
    simp [this]

/- English proof (translation)
Take `⟨hSm, hS1⟩` from `measurableSet_and_vol (k := k) g₁`. Establish `e` using `integral_indicator_const (μ := haarVol (KO k (Fin a))) C hSm`. Rewrite using `[show f = _ from funext hf]`. Conclude with `e.trans (by rw [hS1, one_smul])`.
-/
theorem integral_indicator_KO {a : ℕ} (f : GL (Fin a) k → ℂ) (C : ℂ) (g₁ : GL (Fin a) k)
    (hf : ∀ g, f g = ((fun g => g * g₁) ⁻¹' (KO k (Fin a) : Set (GL (Fin a) k))).indicator (fun _ => C) g) :
    ∫ g, f g ∂(haarVol (KO k (Fin a))) = C := by
  obtain ⟨hSm, hS1⟩ := measurableSet_and_vol (k := k) g₁
  have e := integral_indicator_const (μ := haarVol (KO k (Fin a))) C hSm
  rw [show f = _ from funext hf]
  exact e.trans (by rw [hS1, one_smul])

end Helpers

end GlobalTheory.StdPairLoc

namespace GlobalTheory.StdPairLoc
open GlobalTheory.SplitFlip GlobalTheory.SplitWeil

/- English proof (translation)
Introduce `k _ _ _ _ _ _ ν ϖ c a a' hϖ`. Use `⟨fun X hX => ?_, fun X g₁ hg => ?_⟩` and prove the remaining obligations. Establish `h0 : ∀ g : GL (Fin a) k, stdA ν ϖ c a a' (g.val * X) = 0` using `fun g => by`. Rewrite using `[stdA, dif_neg]`. Introduce and unpack `⟨h, -⟩`.

Conclude with `h (by rw [blk₁_mul, Matrix.det_mul, hX, mul_zero])`. Simplify using `[bigF, shellSum, shell, h0]`. Unfold `bigF`. Use `shellSum_indicator hϖ ν _ _ _ g₁ fun g => ?_` and prove the remaining obligations. Use `integrand_eq ν (ϖ ^ c) _ (blk₂ X) g₁ g _ (fun h => ?_) (fun h => ?_)` and prove the remaining obligations.

Establish `h' : (blk₁ (g.val * X)).det ≠ 0 ∧ IsGLO (blk₁ (g.val * X)) ∧ ∀ i j, blk₂ (g.val * X) i j ∈ cball (ϖ ^ c)`. Rewrite using `[blk₁_mul, blk₂_mul, ← hg]`. Conclude with `h`. Rewrite using `[stdA, dif_pos h']`. Use `congr 3`.

Conclude with `Units.ext (by simp [blk₁_mul, hg])`. Rewrite using `[stdA, dif_neg]`. Rewrite using `[blk₁_mul, blk₂_mul, ← hg]` and apply the resulting hypothesis.
-/
theorem bigF_stdA : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    [MeasurableSpace k] [BorelSpace k] (ν : kˣ →* ℂˣ) (ϖ : kˣ) (c a a' : ℕ), IsUnif ϖ →
    (∀ X : Matrix (Fin a) (Fin (a + a')) k, (blk₁ X).det = 0 →
      bigF (haarVol (KO k (Fin a))) ϖ ν (stdA ν ϖ c a a') X = 0) ∧
    ∀ (X : Matrix (Fin a) (Fin (a + a')) k) (g₁ : GL (Fin a) k), g₁.val = blk₁ X →
      bigF (haarVol (KO k (Fin a))) ϖ ν (stdA ν ϖ c a a') X =
        (((ν (gdet g₁))⁻¹ : ℂˣ) : ℂ) * apow (gdet g₁) (-((Fintype.card (Fin (a + a')) : ℂ) / 2)) *
          Set.indicator {M : Matrix (Fin a) (Fin a') k | ∀ i j, M i j ∈ cball (ϖ ^ c)} 1 ((g₁⁻¹).val * blk₂ X) := by
  intro k _ _ _ _ _ _ ν ϖ c a a' hϖ
  refine ⟨fun X hX => ?_, fun X g₁ hg => ?_⟩
  · have h0 : ∀ g : GL (Fin a) k, stdA ν ϖ c a a' (g.val * X) = 0 := fun g => by
      rw [stdA, dif_neg]
      rintro ⟨h, -⟩
      exact h (by rw [blk₁_mul, Matrix.det_mul, hX, mul_zero])
    simp [bigF, shellSum, shell, h0]
  · unfold bigF
    refine shellSum_indicator hϖ ν _ _ _ g₁ fun g => ?_
    refine integrand_eq ν (ϖ ^ c) _ (blk₂ X) g₁ g _ (fun h => ?_) (fun h => ?_)
    · have h' : (blk₁ (g.val * X)).det ≠ 0 ∧ IsGLO (blk₁ (g.val * X)) ∧
          ∀ i j, blk₂ (g.val * X) i j ∈ cball (ϖ ^ c) := by
        rw [blk₁_mul, blk₂_mul, ← hg]; exact h
      rw [stdA, dif_pos h']
      congr 3
      exact Units.ext (by simp [blk₁_mul, hg])
    · rw [stdA, dif_neg]
      rwa [blk₁_mul, blk₂_mul, ← hg]

/- English proof (translation)
Introduce `k _ _ _ _ _ _ ν ϖ c a a'`. Use `⟨fun Y hY => ?_, fun Y g₂ hg => ?_⟩` and prove the remaining obligations. Establish `h0 : ∀ g : GL (Fin a') k, stdB ν ϖ c a a' (g.val * Y) = 0` using `fun g => by`. Rewrite using `[stdB, dif_neg]`. Introduce and unpack `⟨h, -⟩`.

Conclude with `h (by rw [blk₂_mul, Matrix.det_mul, hY, mul_zero])`. Simplify using `[smallF, h0]`. Unfold `smallF`. Use `integral_indicator_KO _ _ g₂ fun g => ?_` and prove the remaining obligations. Use `integrand_eq ν (ϖ ^ c) _ (blk₁ Y) g₂ g _ (fun h => ?_) (fun h => ?_)` and prove the remaining obligations.

Establish `h' : (blk₂ (g.val * Y)).det ≠ 0 ∧ IsGLO (blk₂ (g.val * Y)) ∧ ∀ i j, blk₁ (g.val * Y) i j ∈ cball (ϖ ^ c)`. Rewrite using `[blk₁_mul, blk₂_mul, ← hg]`. Conclude with `h`. Rewrite using `[stdB, dif_pos h']`. Use `congr 3`.

Conclude with `Units.ext (by simp [blk₂_mul, hg])`. Rewrite using `[stdB, dif_neg]`. Rewrite using `[blk₁_mul, blk₂_mul, ← hg]` and apply the resulting hypothesis.
-/
theorem smallF_stdB : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    [MeasurableSpace k] [BorelSpace k] (ν : kˣ →* ℂˣ) (ϖ : kˣ) (c a a' : ℕ),
    (∀ Y : Matrix (Fin a') (Fin (a + a')) k, (blk₂ Y).det = 0 →
      smallF (haarVol (KO k (Fin a'))) ν (stdB ν ϖ c a a') Y = 0) ∧
    ∀ (Y : Matrix (Fin a') (Fin (a + a')) k) (g₂ : GL (Fin a') k), g₂.val = blk₂ Y →
      smallF (haarVol (KO k (Fin a'))) ν (stdB ν ϖ c a a') Y =
        (((ν (gdet g₂))⁻¹ : ℂˣ) : ℂ) * apow (gdet g₂) (-((Fintype.card (Fin (a + a')) : ℂ) / 2)) *
          Set.indicator {M : Matrix (Fin a') (Fin a) k | ∀ i j, M i j ∈ cball (ϖ ^ c)} 1 ((g₂⁻¹).val * blk₁ Y) := by
  intro k _ _ _ _ _ _ ν ϖ c a a'
  refine ⟨fun Y hY => ?_, fun Y g₂ hg => ?_⟩
  · have h0 : ∀ g : GL (Fin a') k, stdB ν ϖ c a a' (g.val * Y) = 0 := fun g => by
      rw [stdB, dif_neg]
      rintro ⟨h, -⟩
      exact h (by rw [blk₂_mul, Matrix.det_mul, hY, mul_zero])
    simp [smallF, h0]
  · unfold smallF
    refine integral_indicator_KO _ _ g₂ fun g => ?_
    refine integrand_eq ν (ϖ ^ c) _ (blk₁ Y) g₂ g _ (fun h => ?_) (fun h => ?_)
    · have h' : (blk₂ (g.val * Y)).det ≠ 0 ∧ IsGLO (blk₂ (g.val * Y)) ∧
          ∀ i j, blk₁ (g.val * Y) i j ∈ cball (ϖ ^ c) := by
        rw [blk₁_mul, blk₂_mul, ← hg]; exact h
      rw [stdB, dif_pos h']
      congr 3
      exact Units.ext (by simp [blk₂_mul, hg])
    · rw [stdB, dif_neg]
      rwa [blk₁_mul, blk₂_mul, ← hg]

/- English proof (translation)
Introduce `k _ _ _ _ a a' h`. Use `set σ := finSumFinEquiv (m := a) (n := a') with hσ`. Use `set X := X0 k σ * (invT h).val with hX`. Use `set Y := Y0 k σ * h.val with hY`. Establish `hU : ∀ x y, ∑ l, h.val x l * (h⁻¹).val l y = (1 : Matrix (Fin (a + a')) (Fin (a + a')) k) x y`.

Introduce `x y`. Rewrite using `[← Matrix.mul_apply, ← Units.val_mul, mul_inv_cancel, Units.val_one]`. Establish `hX1 : blk₁ X = (Matrix.of fun i j : Fin a => (h⁻¹).val (σ (Sum.inl i)) (σ (Sum.inl j)))ᵀ`. Use extensionality with `i j`. Simplify using `[X, blk₁, frameMatrixFirstColumnBlock_mul_apply, invT_val, σ]`.

Establish `hX2 : blk₂ X = Matrix.of fun (i : Fin a) (j : Fin a') => (h⁻¹).val (σ (Sum.inr j)) (σ (Sum.inl i))`. Use extensionality with `i j`. Simplify using `[X, blk₂, frameMatrixFirstColumnBlock_mul_apply, invT_val, σ]`. Establish `hY1 : blk₁ Y = Matrix.of fun (i : Fin a') (j : Fin a) => h.val (σ (Sum.inr i)) (σ (Sum.inl j))`. Use extensionality with `i j`.

Simplify using `[Y, blk₁, frameMatrixSecondColumnBlock_mul_apply, σ]`. Establish `hY2 : blk₂ Y = Matrix.of fun (i j : Fin a') => h.val (σ (Sum.inr i)) (σ (Sum.inr j))`. Use extensionality with `i j`. Simplify using `[Y, blk₂, frameMatrixSecondColumnBlock_mul_apply, σ]`. Establish `hrel0 : blk₁ Y * (blk₁ X)ᵀ + blk₂ Y * (blk₂ X)ᵀ = 0`.

Use extensionality with `i j`. Use `hU (σ (Sum.inr i)) (σ (Sum.inl j))` as an intermediate fact. Rewrite `this` using `[← Equiv.sum_comp σ, Fintype.sum_sum_type, Matrix.one_apply_ne (σ.injective.ne Sum.inr_ne_inl)]`. Simplify using `only [Matrix.add_apply, Matrix.mul_apply, Matrix.transpose_apply, Matrix.of_apply, hX1, hX2, hY1, hY2, Matrix.zero_apply]`. Conclude with `this`.

Use `⟨?_, fun g₁ g₂ h1 h2 => ?_⟩` and prove the remaining obligations. Set `H' : Matrix (Fin a ⊕ Fin a') (Fin a ⊕ Fin a') k` to `h.val.submatrix σ σ`. Set `U' : Matrix (Fin a ⊕ Fin a') (Fin a ⊕ Fin a') k` to `(h⁻¹).val.submatrix σ σ`. Establish `hHU : ∀ x y, ∑ l, H' x l * U' l y = (1 : Matrix (Fin a ⊕ Fin a') (Fin a ⊕ Fin a') k) x y`. Introduce `x y`.

Use `hU (σ x) (σ y)` as an intermediate fact. Rewrite `this` using `[← Equiv.sum_comp σ]`. Conclude with `this.trans (by simp [Matrix.one_apply])`. Set `L : Matrix (Fin a ⊕ Fin a') (Fin a ⊕ Fin a') k` to `Matrix.fromBlocks (Matrix.of fun i j => U' (Sum.inl i) (Sum.inl j)) 0 (Matrix.of fun i j => U' (Sum.inr i) (Sum.inl j)) 1`. Establish `hL : H' * L = Matrix.fromBlocks 1 (Matrix.of fun i j => H' (Sum.inl i) (Sum.inr j)) 0 (Matrix.of fun i j => H' (Sum.inr i) (Sum.inr j))`.

Use extensionality with `(i | i) (j | j)`. Use `hHU (Sum.inl i) (Sum.inl j)` as an intermediate fact. Simplify using `only [Fintype.sum_sum_type] at this`. Simplify `this` using `[Matrix.mul_apply, Fintype.sum_sum_type, L, Matrix.one_apply]`. Simplify using `[Matrix.mul_apply, Fintype.sum_sum_type, L, Matrix.one_apply]`.

Use `hHU (Sum.inr i) (Sum.inl j)` as an intermediate fact. Simplify using `only [Fintype.sum_sum_type] at this`. Simplify `this` using `[Matrix.mul_apply, Fintype.sum_sum_type, L, Matrix.one_apply]`. Simplify using `[Matrix.mul_apply, Fintype.sum_sum_type, L, Matrix.one_apply]`. Establish `hd` using `congrArg Matrix.det hL`.

Rewrite `hd` using `[Matrix.det_mul, Matrix.det_fromBlocks_zero₁₂, Matrix.det_fromBlocks_zero₂₁, Matrix.det_one, Matrix.det_one, mul_one, one_mul, Matrix.det_submatrix_equiv_self]`. Rewrite using `[hX1, hY2, Matrix.det_transpose, mul_comm]`. Conclude with `hd`. Establish `e1 : (blk₁ X)ᵀ * ((g₁⁻¹).val)ᵀ = 1`. Rewrite using `[← h1, ← Matrix.transpose_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.transpose_one]`.

Establish `e2 : (g₂⁻¹).val * blk₂ Y = 1` using `by rw [← h2, ← Units.val_mul, inv_mul_cancel, Units.val_one]`. Establish `E : blk₁ Y * (blk₁ X)ᵀ = -(blk₂ Y * (blk₂ X)ᵀ)` using `eq_neg_of_add_eq_zero_left hrel0`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[E]`. Simplify using `only [Matrix.neg_mul, Matrix.mul_neg, Matrix.mul_assoc]`.

Use `_ = -((g₁⁻¹).val * blk₂ X)ᵀ := by rw [e2, Matrix.one_mul, Matrix.transpose_mul]`.
-/
theorem standardPair_frameBlocks_det_and_neg_transpose : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (a a' : ℕ) (h : GL (Fin (a + a')) k),
    (blk₁ (X0 k (finSumFinEquiv (m := a) (n := a')) * (invT h).val)).det * h.val.det = (blk₂ (Y0 k (finSumFinEquiv (m := a) (n := a')) * h.val)).det ∧
    ∀ g₁ : GL (Fin a) k, ∀ g₂ : GL (Fin a') k, g₁.val = blk₁ (X0 k (finSumFinEquiv (m := a) (n := a')) * (invT h).val) →
      g₂.val = blk₂ (Y0 k (finSumFinEquiv (m := a) (n := a')) * h.val) →
      ((g₂⁻¹).val * blk₁ (Y0 k (finSumFinEquiv (m := a) (n := a')) * h.val) : Matrix (Fin a') (Fin a) k) =
        -(((g₁⁻¹).val * blk₂ (X0 k (finSumFinEquiv (m := a) (n := a')) * (invT h).val) : Matrix (Fin a) (Fin a') k))ᵀ := by
  intro k _ _ _ _ a a' h
  set σ := finSumFinEquiv (m := a) (n := a') with hσ
  set X := X0 k σ * (invT h).val with hX
  set Y := Y0 k σ * h.val with hY
  have hU : ∀ x y, ∑ l, h.val x l * (h⁻¹).val l y = (1 : Matrix (Fin (a + a')) (Fin (a + a')) k) x y := by
    intro x y; rw [← Matrix.mul_apply, ← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hX1 : blk₁ X = (Matrix.of fun i j : Fin a => (h⁻¹).val (σ (Sum.inl i)) (σ (Sum.inl j)))ᵀ := by
    ext i j; simp [X, blk₁, frameMatrixFirstColumnBlock_mul_apply, invT_val, σ]
  have hX2 : blk₂ X = Matrix.of fun (i : Fin a) (j : Fin a') => (h⁻¹).val (σ (Sum.inr j)) (σ (Sum.inl i)) := by
    ext i j; simp [X, blk₂, frameMatrixFirstColumnBlock_mul_apply, invT_val, σ]
  have hY1 : blk₁ Y = Matrix.of fun (i : Fin a') (j : Fin a) => h.val (σ (Sum.inr i)) (σ (Sum.inl j)) := by
    ext i j; simp [Y, blk₁, frameMatrixSecondColumnBlock_mul_apply, σ]
  have hY2 : blk₂ Y = Matrix.of fun (i j : Fin a') => h.val (σ (Sum.inr i)) (σ (Sum.inr j)) := by
    ext i j; simp [Y, blk₂, frameMatrixSecondColumnBlock_mul_apply, σ]
  have hrel0 : blk₁ Y * (blk₁ X)ᵀ + blk₂ Y * (blk₂ X)ᵀ = 0 := by
    ext i j
    have := hU (σ (Sum.inr i)) (σ (Sum.inl j))
    rw [← Equiv.sum_comp σ, Fintype.sum_sum_type, Matrix.one_apply_ne (σ.injective.ne Sum.inr_ne_inl)] at this
    simp only [Matrix.add_apply, Matrix.mul_apply, Matrix.transpose_apply, Matrix.of_apply, hX1, hX2, hY1, hY2,
      Matrix.zero_apply]
    exact this
  refine ⟨?_, fun g₁ g₂ h1 h2 => ?_⟩
  · let H' : Matrix (Fin a ⊕ Fin a') (Fin a ⊕ Fin a') k := h.val.submatrix σ σ
    let U' : Matrix (Fin a ⊕ Fin a') (Fin a ⊕ Fin a') k := (h⁻¹).val.submatrix σ σ
    have hHU : ∀ x y, ∑ l, H' x l * U' l y = (1 : Matrix (Fin a ⊕ Fin a') (Fin a ⊕ Fin a') k) x y := by
      intro x y
      have := hU (σ x) (σ y)
      rw [← Equiv.sum_comp σ] at this
      exact this.trans (by simp [Matrix.one_apply])
    let L : Matrix (Fin a ⊕ Fin a') (Fin a ⊕ Fin a') k :=
      Matrix.fromBlocks (Matrix.of fun i j => U' (Sum.inl i) (Sum.inl j)) 0
        (Matrix.of fun i j => U' (Sum.inr i) (Sum.inl j)) 1
    have hL : H' * L = Matrix.fromBlocks 1 (Matrix.of fun i j => H' (Sum.inl i) (Sum.inr j)) 0
        (Matrix.of fun i j => H' (Sum.inr i) (Sum.inr j)) := by
      ext (i | i) (j | j)
      · have := hHU (Sum.inl i) (Sum.inl j)
        simp only [Fintype.sum_sum_type] at this
        simpa [Matrix.mul_apply, Fintype.sum_sum_type, L, Matrix.one_apply] using this
      · simp [Matrix.mul_apply, Fintype.sum_sum_type, L, Matrix.one_apply]
      · have := hHU (Sum.inr i) (Sum.inl j)
        simp only [Fintype.sum_sum_type] at this
        simpa [Matrix.mul_apply, Fintype.sum_sum_type, L, Matrix.one_apply] using this
      · simp [Matrix.mul_apply, Fintype.sum_sum_type, L, Matrix.one_apply]
    have hd := congrArg Matrix.det hL
    rw [Matrix.det_mul, Matrix.det_fromBlocks_zero₁₂, Matrix.det_fromBlocks_zero₂₁, Matrix.det_one, Matrix.det_one,
      mul_one, one_mul, Matrix.det_submatrix_equiv_self] at hd
    rw [hX1, hY2, Matrix.det_transpose, mul_comm]
    exact hd
  · have e1 : (blk₁ X)ᵀ * ((g₁⁻¹).val)ᵀ = 1 := by
      rw [← h1, ← Matrix.transpose_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.transpose_one]
    have e2 : (g₂⁻¹).val * blk₂ Y = 1 := by rw [← h2, ← Units.val_mul, inv_mul_cancel, Units.val_one]
    have E : blk₁ Y * (blk₁ X)ᵀ = -(blk₂ Y * (blk₂ X)ᵀ) := eq_neg_of_add_eq_zero_left hrel0
    calc (g₂⁻¹).val * blk₁ Y = (g₂⁻¹).val * (blk₁ Y * ((blk₁ X)ᵀ * ((g₁⁻¹).val)ᵀ)) := by rw [e1, Matrix.mul_one]
      _ = (g₂⁻¹).val * ((blk₁ Y * (blk₁ X)ᵀ) * ((g₁⁻¹).val)ᵀ) := by rw [Matrix.mul_assoc (blk₁ Y)]
      _ = -(((g₂⁻¹).val * blk₂ Y) * ((blk₂ X)ᵀ * ((g₁⁻¹).val)ᵀ)) := by
        rw [E]; simp only [Matrix.neg_mul, Matrix.mul_neg, Matrix.mul_assoc]
      _ = -((g₁⁻¹).val * blk₂ X)ᵀ := by rw [e2, Matrix.one_mul, Matrix.transpose_mul]

/- English proof (translation)
Establish `: (-Mᵀ ∈ {M : Matrix (Fin n) (Fin m) k | ∀ i j, M i j ∈ cball s}) ↔ M ∈ {M : Matrix (Fin m) (Fin n) k | ∀ i j, M i j ∈ cball s}`. Simplify using `only [Set.mem_setOf_eq, cball, Matrix.neg_apply, Matrix.transpose_apply, Valuation.map_neg]`. Conclude with `forall_comm`. Distinguish the cases in `hM : M ∈ {M : Matrix (Fin m) (Fin n) k | ∀ i j, M i j ∈ cball s}`. Rewrite using `[Set.indicator_of_mem hM, Set.indicator_of_mem (this.2 hM)]`.

Both sides reduce to the same expression. Rewrite using `[Set.indicator_of_notMem hM, Set.indicator_of_notMem (fun h => hM (this.1 h))]`.
-/
theorem cball_neg_transpose {k : Type} [Field k] [ValuativeRel k] {m n : ℕ} (s : kˣ) (M : Matrix (Fin m) (Fin n) k) :
    Set.indicator {M : Matrix (Fin n) (Fin m) k | ∀ i j, M i j ∈ cball s} (1 : Matrix (Fin n) (Fin m) k → ℂ) (-Mᵀ) =
      Set.indicator {M : Matrix (Fin m) (Fin n) k | ∀ i j, M i j ∈ cball s} (1 : Matrix (Fin m) (Fin n) k → ℂ) M := by
  have : (-Mᵀ ∈ {M : Matrix (Fin n) (Fin m) k | ∀ i j, M i j ∈ cball s}) ↔
      M ∈ {M : Matrix (Fin m) (Fin n) k | ∀ i j, M i j ∈ cball s} := by
    simp only [Set.mem_setOf_eq, cball, Matrix.neg_apply, Matrix.transpose_apply, Valuation.map_neg]
    exact forall_comm
  by_cases hM : M ∈ {M : Matrix (Fin m) (Fin n) k | ∀ i j, M i j ∈ cball s}
  · rw [Set.indicator_of_mem hM, Set.indicator_of_mem (this.2 hM)]; rfl
  · rw [Set.indicator_of_notMem hM, Set.indicator_of_notMem (fun h => hM (this.1 h))]

end GlobalTheory.StdPairLoc

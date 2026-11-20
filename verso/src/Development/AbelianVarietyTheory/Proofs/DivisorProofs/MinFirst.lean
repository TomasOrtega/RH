import Mathlib
import Formalism.SharpRestriction.Divisibility.SchurIrreducible
import Development.AbelianVarietyTheory.Definitions.Foundations.IsFockIPOfFockData
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeightDegreeLeOfHomogeneousFockWeightVector
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockHarmonicHomogeneousOfKType
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FischerDecompositionFockNoncompactParts
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockHarmonicsGradedCompactStableStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GlBlockFiniteDimModuleStructureStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockOperatorsLieRepresentationCommuteStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OmEFormAndDegree
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockPolynomialsLocallyFiniteRationalWeights

open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible GlobalTheory.FockAlg MvPolynomial

noncomputable section
namespace GlobalTheory.FockAlg.MinFirst

section General

variable {p q : ℕ} {V V' : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup V'] [Module ℂ V']

/- English proof (translation)
Simplify using `only [hwSub, wtSub, Submodule.mem_inf, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply]`.
-/
theorem mem_hwSub (act : Mat p q →ₗ[ℂ] Module.End ℂ V) (μ : Ix p q → ℚ) (v : V) :
    v ∈ hwSub act μ ↔ (∀ a, act (Eab a a) v - ((μ a : ℚ) : ℂ) • v = 0) ∧
      ∀ a b, posC a b → act (Eab a b) v = 0 := by
  simp only [hwSub, wtSub, Submodule.mem_inf, Submodule.mem_iInf, LinearMap.mem_ker,
    LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply]

/- English proof (translation)
Introduce `c d h`. Rewrite using `[Eab, Matrix.single_apply, if_neg]`. Introduce and unpack `⟨rfl, rfl⟩`. Apply the tactic sequence `cases a <;> simp [sameBlock] at h`.
-/
theorem isKC_diag (a : Ix p q) : IsKC (Eab a a) := by
  intro c d h
  rw [Eab, Matrix.single_apply, if_neg]
  rintro ⟨rfl, rfl⟩
  cases a <;> simp [sameBlock] at h

/- English proof (translation)
Introduce `c d h`. Rewrite using `[Eab, Matrix.single_apply, if_neg]`. Introduce and unpack `⟨rfl, rfl⟩`. Apply the tactic sequence `cases a <;> cases b <;> simp_all [sameBlock, posC]`.
-/
theorem isKC_pos {a b : Ix p q} (hab : posC a b) : IsKC (Eab a b) := by
  intro c d h
  rw [Eab, Matrix.single_apply, if_neg]
  rintro ⟨rfl, rfl⟩
  cases a <;> cases b <;> simp_all [sameBlock, posC]

/- English proof (translation)
Rewrite `hv`, the goal using `[mem_hwSub]`. Use `⟨fun i => ?_, fun i j hij => ?_⟩` and prove the remaining obligations. Rewrite using `[← hg _ (isKC_diag i), ← map_smul, ← map_sub, hv.1 i, map_zero]`. Rewrite using `[← hg _ (isKC_pos hij), hv.2 i j hij, map_zero]`.
-/
theorem hw_map {a : Mat p q →ₗ[ℂ] Module.End ℂ V} {b : Mat p q →ₗ[ℂ] Module.End ℂ V'}
    (g : V →ₗ[ℂ] V') (hg : ∀ Z, IsKC Z → ∀ v, g (a Z v) = b Z (g v)) {μ : Ix p q → ℚ} {v : V}
    (hv : v ∈ hwSub a μ) : g v ∈ hwSub b μ := by
  rw [mem_hwSub] at hv ⊢
  refine ⟨fun i => ?_, fun i j hij => ?_⟩
  · rw [← hg _ (isKC_diag i), ← map_smul, ← map_sub, hv.1 i, map_zero]
  · rw [← hg _ (isKC_pos hij), hv.2 i j hij, map_zero]

/- English proof (translation)
Rewrite `hv`, the goal using `[mem_hwSub]`. Use `⟨fun i => hinj _ (U.sub_mem (hU _ (isKC_diag i) _ hu) (U.smul_mem _ hu)) ?_, fun i j hij => hinj _ (hU _ (isKC_pos hij) _ hu) ?_⟩` and prove the remaining obligations. Rewrite using `[map_sub, map_smul, hg _ (isKC_diag i), hv.1 i]`. Rewrite using `[hg _ (isKC_pos hij), hv.2 i j hij]`.
-/
theorem hw_of_map {a : Mat p q →ₗ[ℂ] Module.End ℂ V} {b : Mat p q →ₗ[ℂ] Module.End ℂ V'}
    (g : V →ₗ[ℂ] V') (hg : ∀ Z, IsKC Z → ∀ v, g (a Z v) = b Z (g v)) {μ : Ix p q → ℚ}
    {U : Submodule ℂ V} (hU : KStable a U) (hinj : ∀ u ∈ U, g u = 0 → u = 0) {u : V} (hu : u ∈ U)
    (hv : g u ∈ hwSub b μ) : u ∈ hwSub a μ := by
  rw [mem_hwSub] at hv ⊢
  refine ⟨fun i => hinj _ (U.sub_mem (hU _ (isKC_diag i) _ hu) (U.smul_mem _ hu)) ?_,
    fun i j hij => hinj _ (hU _ (isKC_pos hij) _ hu) ?_⟩
  · rw [map_sub, map_smul, hg _ (isKC_diag i), hv.1 i]
  · rw [hg _ (isKC_pos hij), hv.2 i j hij]

/- English proof (translation)
Introduce `X hX w hw` and use `⟨hU X hX w hw.1, hW X hX w hw.2⟩`.
-/
theorem kStable_inf {a : Mat p q →ₗ[ℂ] Module.End ℂ V} {U W : Submodule ℂ V} (hU : KStable a U)
    (hW : KStable a W) : KStable a (U ⊓ W) :=
  fun X hX w hw => ⟨hU X hX w hw.1, hW X hX w hw.2⟩

/- English proof (translation)
Introduce `X hX w hw`. Take `⟨y, hy, z, hz, rfl⟩` from `Submodule.mem_sup.1 hw`. Rewrite using `[map_add]`. Conclude with `Submodule.add_mem_sup (hU X hX y hy) (hW X hX z hz)`.
-/
theorem kStable_sup {a : Mat p q →ₗ[ℂ] Module.End ℂ V} {U W : Submodule ℂ V} (hU : KStable a U)
    (hW : KStable a W) : KStable a (U ⊔ W) := by
  intro X hX w hw
  obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.1 hw
  rw [map_add]
  exact Submodule.add_mem_sup (hU X hX y hy) (hW X hX z hz)

/- English proof (translation)
Introduce `X hX w hw`. Rewrite `hw`, the goal using `[LinearMap.mem_ker]`. Rewrite using `[hg X hX, hw, map_zero]`.
-/
theorem kStable_ker {a : Mat p q →ₗ[ℂ] Module.End ℂ V} {b : Mat p q →ₗ[ℂ] Module.End ℂ V'}
    (g : V →ₗ[ℂ] V') (hg : ∀ Z, IsKC Z → ∀ v, g (a Z v) = b Z (g v)) :
    KStable a (LinearMap.ker g) := by
  intro X hX w hw
  rw [LinearMap.mem_ker] at hw ⊢
  rw [hg X hX, hw, map_zero]

variable {a : Mat p q →ₗ[ℂ] Module.End ℂ V} (ha : IsKLieAct a)
  (hwt : ∀ v, v ∈ ⨆ μ : Ix p q → ℚ, wtSub a μ)
include ha hwt

/- English proof (translation)
Take `⟨U, sU, h1, h2⟩` from `(GlobalTheory.T.glBlock_finiteDim_module_structure p q V a ha W hW sW fun v _ => hwt v).1 (W ⊓ N) inf_le_left (kStable_inf sW sN)`. Establish `hle : U ≤ W` using `h2 ▸ le_sup_right`. Establish `hne : U ≠ ⊥`. Introduce and unpack `rfl`. Rewrite `h2` using `[sup_bot_eq]`.

Conclude with `h (h2 ▸ inf_le_right)`. Take `⟨ν, u, hu, hhw⟩` from `(GlobalTheory.T.glBlock_finiteDim_module_structure p q V a ha U (Submodule.finiteDimensional_of_le hle) sU fun v _ => hwt v).2.1 hne`. Use `⟨ν, u, hle hu, hhw, fun hN => hhw.1 ?_⟩` and prove the remaining obligations. Establish `: u ∈ W ⊓ N ⊓ U` using `⟨⟨hle hu, hN⟩, hu⟩`. Rewrite `this` using `[h1]`. Then use the resulting hypothesis.
-/
theorem exists_hw_notMem {W N : Submodule ℂ V} (hW : FiniteDimensional ℂ W) (sW : KStable a W)
    (sN : KStable a N) (h : ¬ W ≤ N) : ∃ ν u, u ∈ W ∧ IsHW a ν u ∧ u ∉ N := by
  obtain ⟨U, sU, h1, h2⟩ :=
    (GlobalTheory.T.glBlock_finiteDim_module_structure p q V a ha W hW sW fun v _ => hwt v).1 (W ⊓ N) inf_le_left (kStable_inf sW sN)
  have hle : U ≤ W := h2 ▸ le_sup_right
  have hne : U ≠ ⊥ := by
    rintro rfl
    rw [sup_bot_eq] at h2
    exact h (h2 ▸ inf_le_right)
  obtain ⟨ν, u, hu, hhw⟩ := (GlobalTheory.T.glBlock_finiteDim_module_structure p q V a ha U (Submodule.finiteDimensional_of_le hle) sU
    fun v _ => hwt v).2.1 hne
  refine ⟨ν, u, hle hu, hhw, fun hN => hhw.1 ?_⟩
  have : u ∈ W ⊓ N ⊓ U := ⟨⟨hle hu, hN⟩, hu⟩
  rwa [h1] at this

/- English proof (translation)
Take `⟨U, sU, h1, h2⟩` from `(GlobalTheory.T.glBlock_finiteDim_module_structure p q V a ha W hW sW fun v _ => hwt v).1 (W ⊓ LinearMap.ker g) inf_le_left (kStable_inf sW (kStable_ker g hg))`. Establish `hle : U ≤ W` using `h2 ▸ le_sup_right`. Rewrite `hw` using `[← h2]`. Take `⟨y, hy, u, hu, rfl⟩` from `Submodule.mem_sup.1 hw`. Establish `e : g u = g (y + u)` using `by rw [map_add, LinearMap.mem_ker.1 hy.2, zero_add]`.

Use `⟨u, hle hu, hw_of_map g hg sU (fun x hx h0 => ?_) hu (e ▸ h), e⟩` and prove the remaining obligations. Establish `: x ∈ W ⊓ LinearMap.ker g ⊓ U` using `⟨⟨hle hx, h0⟩, hx⟩`. Rewrite `this` using `[h1]`. Then use the resulting hypothesis.
-/
theorem hw_lift {b : Mat p q →ₗ[ℂ] Module.End ℂ V'}
    (g : V →ₗ[ℂ] V') (hg : ∀ Z, IsKC Z → ∀ v, g (a Z v) = b Z (g v)) {μ : Ix p q → ℚ}
    {W : Submodule ℂ V} (hW : FiniteDimensional ℂ W) (sW : KStable a W) {w : V} (hw : w ∈ W)
    (h : g w ∈ hwSub b μ) : ∃ u ∈ W, u ∈ hwSub a μ ∧ g u = g w := by
  obtain ⟨U, sU, h1, h2⟩ :=
    (GlobalTheory.T.glBlock_finiteDim_module_structure p q V a ha W hW sW fun v _ => hwt v).1 (W ⊓ LinearMap.ker g) inf_le_left
      (kStable_inf sW (kStable_ker g hg))
  have hle : U ≤ W := h2 ▸ le_sup_right
  rw [← h2] at hw
  obtain ⟨y, hy, u, hu, rfl⟩ := Submodule.mem_sup.1 hw
  have e : g u = g (y + u) := by rw [map_add, LinearMap.mem_ker.1 hy.2, zero_add]
  refine ⟨u, hle hu, hw_of_map g hg sU (fun x hx h0 => ?_) hu (e ▸ h), e⟩
  have : x ∈ W ⊓ LinearMap.ker g ⊓ U := ⟨⟨hle hx, h0⟩, hx⟩
  rwa [h1] at this

/- English proof (translation)
Take `⟨U', sU', h1, h2⟩` from `(GlobalTheory.T.glBlock_finiteDim_module_structure p q V a ha W hW sW fun v _ => hwt v).1 (W ⊓ U) inf_le_left (kStable_inf sW sU)`. Establish `hle : U' ≤ W` using `h2 ▸ le_sup_right`. Take `⟨y, hy, z, hz, rfl⟩` from `Submodule.mem_sup.1 hv`. Take `⟨z0, hz0, rfl⟩ : ∃ z0 ∈ W ⊓ U ⊔ U', z0 = z` from `⟨z, by rw [h2]; exact hz, rfl⟩`. Use `clear hz`.

Take `⟨y', hy', z, hz, rfl⟩` from `Submodule.mem_sup.1 hz0`. Establish `hyy : y + y' ∈ U` using `U.add_mem hy hy'.2`. Establish `key : ∀ s ∈ U, ∀ t ∈ U', s + t = 0 → t = 0`. Introduce `s hs t ht e`. Establish `: t ∈ W ⊓ U ⊓ U'` using `⟨⟨hle ht, by`.

Rewrite using `[eq_neg_of_add_eq_zero_right e]`. Conclude with `U.neg_mem hs⟩, ht⟩`. Rewrite `this` using `[h1]`. Then use the resulting hypothesis. Establish `hzh : z ∈ hwSub a μ`. Rewrite `h` using `[← add_assoc, mem_hwSub]`.

Rewrite using `[mem_hwSub]`. Use `⟨fun i => key _ (U.sub_mem (sU _ (isKC_diag i) _ hyy) (U.smul_mem ((μ i : ℚ) : ℂ) hyy)) _ (U'.sub_mem (sU' _ (isKC_diag i) _ hz) (U'.smul_mem _ hz)) ?_, fun i j hij => key _ (sU _ (isKC_pos hij) _ hyy) _ (sU' _ (isKC_pos hij) _ hz) ?_⟩` and prove the remaining obligations. Rewrite using `[← h.1 i, map_add (a _) (y + y'), smul_add _ (y + y')]`. Normalize the expressions using the abelian group laws. Rewrite using `[← map_add, h.2 i j hij]`.

Use `⟨y + y', hyy, z, hle hz, ?_, hzh, add_assoc _ _ _⟩` and prove the remaining obligations. Use `(hwSub a μ).sub_mem h hzh` as an intermediate fact. Rewrite `this` using `[← add_assoc, add_sub_cancel_right]`. Then use the resulting hypothesis.
-/
theorem hw_sup {μ : Ix p q → ℚ} {U W : Submodule ℂ V} (hW : FiniteDimensional ℂ W)
    (sU : KStable a U) (sW : KStable a W) {v : V} (hv : v ∈ U ⊔ W) (h : v ∈ hwSub a μ) :
    ∃ y ∈ U, ∃ z ∈ W, y ∈ hwSub a μ ∧ z ∈ hwSub a μ ∧ y + z = v := by
  obtain ⟨U', sU', h1, h2⟩ :=
    (GlobalTheory.T.glBlock_finiteDim_module_structure p q V a ha W hW sW fun v _ => hwt v).1 (W ⊓ U) inf_le_left (kStable_inf sW sU)
  have hle : U' ≤ W := h2 ▸ le_sup_right
  obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.1 hv
  obtain ⟨z0, hz0, rfl⟩ : ∃ z0 ∈ W ⊓ U ⊔ U', z0 = z := ⟨z, by rw [h2]; exact hz, rfl⟩
  clear hz
  obtain ⟨y', hy', z, hz, rfl⟩ := Submodule.mem_sup.1 hz0
  have hyy : y + y' ∈ U := U.add_mem hy hy'.2
  have key : ∀ s ∈ U, ∀ t ∈ U', s + t = 0 → t = 0 := by
    intro s hs t ht e
    have : t ∈ W ⊓ U ⊓ U' := ⟨⟨hle ht, by
      rw [eq_neg_of_add_eq_zero_right e]; exact U.neg_mem hs⟩, ht⟩
    rwa [h1] at this
  have hzh : z ∈ hwSub a μ := by
    rw [← add_assoc, mem_hwSub] at h
    rw [mem_hwSub]
    refine ⟨fun i => key _ (U.sub_mem (sU _ (isKC_diag i) _ hyy) (U.smul_mem ((μ i : ℚ) : ℂ) hyy)) _
      (U'.sub_mem (sU' _ (isKC_diag i) _ hz) (U'.smul_mem _ hz)) ?_,
      fun i j hij => key _ (sU _ (isKC_pos hij) _ hyy) _ (sU' _ (isKC_pos hij) _ hz) ?_⟩
    · rw [← h.1 i, map_add (a _) (y + y'), smul_add _ (y + y')]; abel
    · rw [← map_add, h.2 i j hij]
  refine ⟨y + y', hyy, z, hle hz, ?_, hzh, add_assoc _ _ _⟩
  have := (hwSub a μ).sub_mem h hzh
  rwa [← add_assoc, add_sub_cancel_right] at this

/- English proof (translation)
It suffices to establish `∃ U : Submodule ℂ V, FiniteDimensional ℂ U ∧ KStable a U ∧ (∀ y ∈ U, y ∈ hwSub a μ → y ∈ T) ∧ v ∈ U by`. Take `⟨U, -, -, h1, h2⟩` from `this`. Conclude with `h1 v h2 h`. Use `clear h`. Proceed by induction on `hv using Submodule.span_induction with`.

Consider the case `mem x hx => exact hS x hx`. Consider the case `zero`. Use `⟨⊥, inferInstance, fun X _ w hw => ?_, fun y hy _ => ?_, Submodule.zero_mem _⟩` and prove the remaining obligations. Rewrite `hw`, the goal using `[Submodule.mem_bot]`. Rewrite using `[hw, map_zero]`.

Rewrite `hy` using `[Submodule.mem_bot]`. Rewrite using `[hy]`. Conclude with `T.zero_mem`. Consider the case `add x y _ _ hx hy`. Take `⟨U, fU, sU, tU, hx⟩` from `hx`.

Take `⟨W, fW, sW, tW, hy⟩` from `hy`. Use `⟨U ⊔ W, inferInstance, kStable_sup sU sW, fun v hv h => ?_, Submodule.add_mem_sup hx hy⟩` and prove the remaining obligations. Take `⟨y, hy, z, hz, h1, h2, rfl⟩` from `hw_sup ha hwt fW sU sW hv h`. Conclude with `T.add_mem (tU y hy h1) (tW z hz h2)`. Consider the case `smul c x _ hx`.

Take `⟨U, fU, sU, tU, hx⟩` from `hx`. Conclude with `⟨U, fU, sU, tU, U.smul_mem c hx⟩`.
-/
theorem hw_span {μ : Ix p q → ℚ} (T : Submodule ℂ V) (S : Set V)
    (hS : ∀ x ∈ S, ∃ U : Submodule ℂ V, FiniteDimensional ℂ U ∧ KStable a U ∧
      (∀ y ∈ U, y ∈ hwSub a μ → y ∈ T) ∧ x ∈ U) {v : V} (hv : v ∈ Submodule.span ℂ S)
    (h : v ∈ hwSub a μ) : v ∈ T := by
  suffices ∃ U : Submodule ℂ V, FiniteDimensional ℂ U ∧ KStable a U ∧
      (∀ y ∈ U, y ∈ hwSub a μ → y ∈ T) ∧ v ∈ U by
    obtain ⟨U, -, -, h1, h2⟩ := this
    exact h1 v h2 h
  clear h
  induction hv using Submodule.span_induction with
  | mem x hx => exact hS x hx
  | zero =>
    refine ⟨⊥, inferInstance, fun X _ w hw => ?_, fun y hy _ => ?_, Submodule.zero_mem _⟩
    · rw [Submodule.mem_bot] at hw ⊢; rw [hw, map_zero]
    · rw [Submodule.mem_bot] at hy; rw [hy]; exact T.zero_mem
  | add x y _ _ hx hy =>
    obtain ⟨U, fU, sU, tU, hx⟩ := hx
    obtain ⟨W, fW, sW, tW, hy⟩ := hy
    refine ⟨U ⊔ W, inferInstance, kStable_sup sU sW, fun v hv h => ?_, Submodule.add_mem_sup hx hy⟩
    obtain ⟨y, hy, z, hz, h1, h2, rfl⟩ := hw_sup ha hwt fW sU sW hv h
    exact T.add_mem (tU y hy h1) (tW z hz h2)
  | smul c x _ hx =>
    obtain ⟨U, fU, sU, tU, hx⟩ := hx
    exact ⟨U, fU, sU, tU, U.smul_mem c hx⟩

end General

section Degree

variable {p q r s : ℕ}

/- English proof (translation)
The claim follows from `Submodule.finiteDimensional_of_le (S₂ := restrictTotalDegree (Ix p q × Ix r s) ℂ d) fun P hP => (mem_restrictTotalDegree _ _ _).2 (IsHomogeneous.totalDegree_le hP)`.
-/
theorem homog_fd (d : ℕ) : FiniteDimensional ℂ (homog (Ix p q × Ix r s) d) :=
  Submodule.finiteDimensional_of_le (S₂ := restrictTotalDegree (Ix p q × Ix r s) ℂ d) fun P hP =>
    (mem_restrictTotalDegree _ _ _).2 (IsHomogeneous.totalDegree_le hP)

/- English proof (translation)
Rewrite using `[omAct_apply, LinearMap.sum_apply]`. Use `Submodule.sum_mem _ fun l _ => ?_` and prove the remaining obligations. Rewrite using `[LinearMap.sum_apply]`. Use `Submodule.sum_mem _ fun l' _ => ?_` and prove the remaining obligations. Rewrite using `[LinearMap.smul_apply]`.

Distinguish the cases in `h0 : Z l l' = 0`. Rewrite using `[h0, zero_smul]`. Conclude with `Submodule.zero_mem _`. Conclude with `Submodule.smul_mem _ _ (h l l' h0)`.
-/
theorem omAct_mem (N : Submodule ℂ (Pol p q r s)) (Z : Matrix (Ln p q r s) (Ln p q r s) ℂ)
    (P : Pol p q r s) (h : ∀ l l', Z l l' ≠ 0 → omE l l' P ∈ N) : omAct p q r s Z P ∈ N := by
  rw [omAct_apply, LinearMap.sum_apply]
  refine Submodule.sum_mem _ fun l _ => ?_
  rw [LinearMap.sum_apply]
  refine Submodule.sum_mem _ fun l' _ => ?_
  rw [LinearMap.smul_apply]
  by_cases h0 : Z l l' = 0
  · rw [h0, zero_smul]; exact Submodule.zero_mem _
  · exact Submodule.smul_mem _ _ (h l l' h0)

/- English proof (translation)
Introduce `Z hZ P hP`. Use `omAct_mem _ _ P ?_` and prove the remaining obligations. Introduce and unpack `⟨a, c⟩ ⟨b, e⟩ h`. Use `(GlobalTheory.FockOm.omE_form_and_degree p q r s _ _ d P hP).1 ?_` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `Z a b * (1 : Mat r s) c e ≠ 0 at h`.

Establish `hc : c = e`. Assume the negation of the conclusion as `hc`. Conclude with `h (by rw [Matrix.one_apply_ne hc, mul_zero])`. Substitute `hc` using the available equality. Establish `hab : sameBlock a b`.

Assume the negation of the conclusion as `hab`. Conclude with `h (by rw [hZ a b hab, zero_mul])`. Apply the tactic sequence `rcases a with a | a <;> rcases b with b | b <;> rcases c with c | c <;>`. Simplify using `[linePos, sameBlock]`.
-/
theorem kStable_homog (d : ℕ) : KStable (fockAct1 p q r s) (homog (Ix p q × Ix r s) d) := by
  intro Z hZ P hP
  refine omAct_mem _ _ P ?_
  rintro ⟨a, c⟩ ⟨b, e⟩ h
  refine (GlobalTheory.FockOm.omE_form_and_degree p q r s _ _ d P hP).1 ?_
  change Z a b * (1 : Mat r s) c e ≠ 0 at h
  have hc : c = e := by
    by_contra hc
    exact h (by rw [Matrix.one_apply_ne hc, mul_zero])
  subst hc
  have hab : sameBlock a b := by
    by_contra hab
    exact h (by rw [hZ a b hab, zero_mul])
  rcases a with a | a <;> rcases b with b | b <;> rcases c with c | c <;>
    simp_all [linePos, sameBlock]

/- English proof (translation)
Use `omAct_mem (LinearMap.ker (homogeneousComponent e)) Z P fun l l' _ => ?_` and prove the remaining obligations. Take `⟨h1, h2, h3⟩` from `GlobalTheory.FockOm.omE_form_and_degree p q r s l l' d P hP`. Rewrite using `[LinearMap.mem_ker]`. Apply the tactic sequence `cases hl : linePos l <;> cases hl' : linePos l'`. Rewrite using `[homogeneousComponent_of_mem (h1 (hl.trans hl'.symm)), if_neg (by omega)]`.

Establish `: (pderiv l (pderiv l' P)).IsHomogeneous (d - 1 - 1)` using `(IsHomogeneous.pderiv (IsHomogeneous.pderiv hP))`. Rewrite using `[h3 hl hl', map_neg, homogeneousComponent_of_mem this, if_neg (by omega), neg_zero]`. Establish `: (X l * X l' * P).IsHomogeneous (1 + 1 + d)` using `((isHomogeneous_X ℂ l).mul (isHomogeneous_X ℂ l')).mul hP`. Rewrite using `[h2 hl hl', homogeneousComponent_of_mem this, if_neg (by omega)]`. Rewrite using `[homogeneousComponent_of_mem (h1 (hl.trans hl'.symm)), if_neg (by omega)]`.
-/
theorem comp_omAct (Z : Matrix (Ln p q r s) (Ln p q r s) ℂ) {d e : ℕ} (he : d + 2 < e)
    {P : Pol p q r s} (hP : P ∈ homog (Ix p q × Ix r s) d) :
    homogeneousComponent e (omAct p q r s Z P) = 0 := by
  refine omAct_mem (LinearMap.ker (homogeneousComponent e)) Z P fun l l' _ => ?_
  obtain ⟨h1, h2, h3⟩ := GlobalTheory.FockOm.omE_form_and_degree p q r s l l' d P hP
  rw [LinearMap.mem_ker]
  cases hl : linePos l <;> cases hl' : linePos l'
  · rw [homogeneousComponent_of_mem (h1 (hl.trans hl'.symm)), if_neg (by omega)]
  · have : (pderiv l (pderiv l' P)).IsHomogeneous (d - 1 - 1) :=
      (IsHomogeneous.pderiv (IsHomogeneous.pderiv hP))
    rw [h3 hl hl', map_neg, homogeneousComponent_of_mem this, if_neg (by omega), neg_zero]
  · have : (X l * X l' * P).IsHomogeneous (1 + 1 + d) :=
      ((isHomogeneous_X ℂ l).mul (isHomogeneous_X ℂ l')).mul hP
    rw [h2 hl hl', homogeneousComponent_of_mem this, if_neg (by omega)]
  · rw [homogeneousComponent_of_mem (h1 (hl.trans hl'.symm)), if_neg (by omega)]

/- English proof (translation)
Rewrite using `[← sum_homogeneousComponent P]`. Conclude with `T.sum_mem fun e _ => h e`.
-/
theorem mem_of_comp (T : Submodule ℂ (Pol p q r s)) (P : Pol p q r s)
    (h : ∀ e, homogeneousComponent e P ∈ T) : P ∈ T := by
  rw [← sum_homogeneousComponent P]
  exact T.sum_mem fun e _ => h e

/- English proof (translation)
Establish `: P - homogeneousComponent n P ∈ T`. Use `mem_of_comp T _ fun e => ?_` and prove the remaining obligations. Rewrite using `[map_sub, homogeneousComponent_of_mem (homogeneousComponent_mem n P)]`. Break down `lt_trichotomy e n with h | rfl | h` into its components or cases. Rewrite using `[if_neg h.ne, sub_zero]`.

Conclude with `h1 e h`. Rewrite using `[if_pos rfl, sub_self]`. Conclude with `T.zero_mem`. Rewrite using `[if_neg h.ne', sub_zero, h2 e h]`. Conclude with `T.zero_mem`.

Simplify using `using T.sub_mem hP this`.
-/
theorem top_mem (T : Submodule ℂ (Pol p q r s)) (P : Pol p q r s) (n : ℕ) (hP : P ∈ T)
    (h1 : ∀ e, e < n → homogeneousComponent e P ∈ T)
    (h2 : ∀ e, n < e → homogeneousComponent e P = 0) : homogeneousComponent n P ∈ T := by
  have : P - homogeneousComponent n P ∈ T := by
    refine mem_of_comp T _ fun e => ?_
    rw [map_sub, homogeneousComponent_of_mem (homogeneousComponent_mem n P)]
    rcases lt_trichotomy e n with h | rfl | h
    · rw [if_neg h.ne, sub_zero]; exact h1 e h
    · rw [if_pos rfl, sub_self]; exact T.zero_mem
    · rw [if_neg h.ne', sub_zero, h2 e h]; exact T.zero_mem
  simpa using T.sub_mem hP this

/- English proof (translation)
Establish `: P ∈ LinearMap.eqLocus (homogeneousComponent e ∘ₗ fockAct1 p q r s Z) (fockAct1 p q r s Z ∘ₗ homogeneousComponent e)`. Use `mem_of_comp _ P fun d => ?_` and prove the remaining obligations. Establish `h` using `homogeneousComponent_mem d P`. Rewrite using `[LinearMap.mem_eqLocus, LinearMap.comp_apply, LinearMap.comp_apply, homogeneousComponent_of_mem h, homogeneousComponent_of_mem (kStable_homog d Z hZ _ h)]`. Apply the tactic sequence `split_ifs <;> simp`.

Conclude with `this`.
-/
theorem comp_comm (Z : Mat p q) (hZ : IsKC Z) (e : ℕ) (P : Pol p q r s) :
    homogeneousComponent e (fockAct1 p q r s Z P) =
      fockAct1 p q r s Z (homogeneousComponent e P) := by
  have : P ∈ LinearMap.eqLocus (homogeneousComponent e ∘ₗ fockAct1 p q r s Z)
      (fockAct1 p q r s Z ∘ₗ homogeneousComponent e) := by
    refine mem_of_comp _ P fun d => ?_
    have h := homogeneousComponent_mem d P
    rw [LinearMap.mem_eqLocus, LinearMap.comp_apply, LinearMap.comp_apply,
      homogeneousComponent_of_mem h, homogeneousComponent_of_mem (kStable_homog d Z hZ _ h)]
    split_ifs <;> simp
  exact this

/- English proof (translation)
Unfold `plusPart`. Rewrite using `[finsum_eq_single _ d]`. Rewrite using `[homogeneousComponent_of_mem hP, if_pos rfl]`. Introduce `e he`. Rewrite using `[homogeneousComponent_of_mem hP, if_neg he, map_zero, map_zero]`.
-/
theorem plusPart_homog (A : Module.End ℂ (Pol p q r s)) {d : ℕ} {P : Pol p q r s}
    (hP : P ∈ homog (Ix p q × Ix r s) d) : plusPart A P = homogeneousComponent (d + 2) (A P) := by
  unfold plusPart
  rw [finsum_eq_single _ d]
  · rw [homogeneousComponent_of_mem hP, if_pos rfl]
  · intro e he
    rw [homogeneousComponent_of_mem hP, if_neg he, map_zero, map_zero]

/- English proof (translation)
Unfold `minusPart`. Use `finsum_eq_zero_of_forall_eq_zero fun e => ?_` and prove the remaining obligations. Rewrite using `[homogeneousComponent_of_mem hP, if_neg (by omega), map_zero, map_zero]`.
-/
theorem minusPart_low (A : Module.End ℂ (Pol p q r s)) {d : ℕ} (hd : d < 2) {P : Pol p q r s}
    (hP : P ∈ homog (Ix p q × Ix r s) d) : minusPart A P = 0 := by
  unfold minusPart
  refine finsum_eq_zero_of_forall_eq_zero fun e => ?_
  rw [homogeneousComponent_of_mem hP, if_neg (by omega), map_zero, map_zero]

end Degree

section Main

variable {p q r s : ℕ} {M1 : GKMod p q} {M2 : GKMod r s}
  {f : Pol p q r s →ₗ[ℂ] TensorProduct ℂ M1.V M2.V}

/- English proof (translation)
Introduce `Y Z _ _` and use `(GlobalTheory.T.fockOperators_lie_representation_commute p q r s).2.1 Y Z`.
-/
theorem kLie1 : IsKLieAct (fockAct1 p q r s) := fun Y Z _ _ => (GlobalTheory.T.fockOperators_lie_representation_commute p q r s).2.1 Y Z

/- English proof (translation)
Introduce `Y Z _ _` and use `(GlobalTheory.T.fockOperators_lie_representation_commute p q r s).2.2.1 Y Z`.
-/
theorem kLie2 : IsKLieAct (fockAct2 p q r s) := fun Y Z _ _ => (GlobalTheory.T.fockOperators_lie_representation_commute p q r s).2.2.1 Y Z

/- English proof (translation)
The claim follows from `((GlobalTheory.FockPolGK.pol_locFin_weights p q r s).1 P).2`.
-/
theorem wts1 (P : Pol p q r s) : P ∈ ⨆ μ : Ix p q → ℚ, wtSub (fockAct1 p q r s) μ :=
  ((GlobalTheory.FockPolGK.pol_locFin_weights p q r s).1 P).2

/- English proof (translation)
The claim follows from `((GlobalTheory.FockPolGK.pol_locFin_weights p q r s).2 P).2`.
-/
theorem wts2 (P : Pol p q r s) : P ∈ ⨆ μ : Ix r s → ℚ, wtSub (fockAct2 p q r s) μ :=
  ((GlobalTheory.FockPolGK.pol_locFin_weights p q r s).2 P).2

/- English proof (translation)
The claim follows from `(LinearMap.congr_fun ((GlobalTheory.T.fockOperators_lie_representation_commute p q r s).2.2.2 Y Z) P).symm`.
-/
theorem fockAct1_fockAct2_commute (Y : Mat p q) (Z : Mat r s) (P : Pol p q r s) :
    fockAct2 p q r s Z (fockAct1 p q r s Y P) = fockAct1 p q r s Y (fockAct2 p q r s Z P) :=
  (LinearMap.congr_fun ((GlobalTheory.T.fockOperators_lie_representation_commute p q r s).2.2.2 Y Z) P).symm

/- English proof (translation)
Distinguish the cases in `h0 : P = 0`. Substitute `h0` using the available equality. Use `⟨⊥, inferInstance, Submodule.zero_mem _, fun X _ w hw => ?_, fun ν w hw h => absurd ((Submodule.mem_bot ℂ).1 hw) h.1⟩` and prove the remaining obligations. Rewrite `hw`, the goal using `[Submodule.mem_bot]`. Rewrite using `[hw, map_zero]`.

Take `⟨W, fW, hP, sW⟩` from `((GlobalTheory.FockPolGK.pol_locFin_weights p q r s).1 P).1`. Conclude with `((GlobalTheory.T.glBlock_finiteDim_module_structure p q _ _ kLie1 W fW sW fun v _ => wts1 v).2.2.2 μ P hP ⟨h0, h⟩).2.1`.
-/
theorem ofType_of_hw {μ : Ix p q → ℚ} {P : Pol p q r s} (h : P ∈ hwSub (fockAct1 p q r s) μ) :
    OfType (fockAct1 p q r s) μ P := by
  by_cases h0 : P = 0
  · subst h0
    refine ⟨⊥, inferInstance, Submodule.zero_mem _, fun X _ w hw => ?_,
      fun ν w hw h => absurd ((Submodule.mem_bot ℂ).1 hw) h.1⟩
    rw [Submodule.mem_bot] at hw ⊢; rw [hw, map_zero]
  · obtain ⟨W, fW, hP, sW⟩ := ((GlobalTheory.FockPolGK.pol_locFin_weights p q r s).1 P).1
    exact ((GlobalTheory.T.glBlock_finiteDim_module_structure p q _ _ kLie1 W fW sW fun v _ => wts1 v).2.2.2 μ P hP ⟨h0, h⟩).2.1

/- English proof (translation)
Set `b` to `Module.Basis.ofVectorSpace ℂ M2.V`. Establish `h1 : TensorProduct.equivFinsuppOfBasisRight b (f P) ≠ 0`. Rewrite using `[Ne, LinearEquiv.map_eq_zero_iff]` and apply the resulting hypothesis. Take `⟨i, hi⟩` from `Finsupp.ne_iff.1 h1`. Rewrite `hi` using `[TensorProduct.equivFinsuppOfBasisRight_apply]`.

Use `⟨(TensorProduct.rid ℂ M1.V).toLinearMap ∘ₗ (b.coord i).lTensor M1.V ∘ₗ f, fun Z v => ?_, hi, fun v hv => by simp [hv]⟩` and prove the remaining obligations. Use `LinearMap.congr_fun (hI.1 Z) v` as an intermediate fact. Simplify using `only [LinearMap.comp_apply] at this ⊢`. Rewrite using `[this]`. Generalize the expression as in `f v = y`.

Proceed by induction on `y using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `tmul x y => simp`. Consider the case `add x y hx hy => simp only [map_add, hx, hy]`.
-/
theorem exists_contr (hI : Intw M1 M2 f) {P : Pol p q r s} (hP : f P ≠ 0) :
    ∃ g : Pol p q r s →ₗ[ℂ] M1.V, (∀ Z v, g (fockAct1 p q r s Z v) = M1.act Z (g v)) ∧
      g P ≠ 0 ∧ ∀ v, f v = 0 → g v = 0 := by
  classical
  let b := Module.Basis.ofVectorSpace ℂ M2.V
  have h1 : TensorProduct.equivFinsuppOfBasisRight b (f P) ≠ 0 := by
    rwa [Ne, LinearEquiv.map_eq_zero_iff]
  obtain ⟨i, hi⟩ := Finsupp.ne_iff.1 h1
  rw [TensorProduct.equivFinsuppOfBasisRight_apply] at hi
  refine ⟨(TensorProduct.rid ℂ M1.V).toLinearMap ∘ₗ (b.coord i).lTensor M1.V ∘ₗ f, fun Z v => ?_,
    hi, fun v hv => by simp [hv]⟩
  have := LinearMap.congr_fun (hI.1 Z) v
  simp only [LinearMap.comp_apply] at this ⊢
  rw [this]
  generalize f v = y
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul x y => simp
  | add x y hx hy => simp only [map_add, hx, hy]

/- English proof (translation)
Rewrite `h`, the goal using `[LinearMap.mem_ker]`. Use `LinearMap.congr_fun (hI.1 Z) P` as an intermediate fact. Simplify using `only [LinearMap.comp_apply] at this`. Rewrite using `[this, h, map_zero]`.
-/
theorem ker_stable1 (hI : Intw M1 M2 f) (Z : Mat p q) {P : Pol p q r s} (h : P ∈ LinearMap.ker f) :
    fockAct1 p q r s Z P ∈ LinearMap.ker f := by
  rw [LinearMap.mem_ker] at h ⊢
  have := LinearMap.congr_fun (hI.1 Z) P
  simp only [LinearMap.comp_apply] at this
  rw [this, h, map_zero]

/- English proof (translation)
Rewrite `h`, the goal using `[LinearMap.mem_ker]`. Use `LinearMap.congr_fun (hI.2 Z) P` as an intermediate fact. Simplify using `only [LinearMap.comp_apply] at this`. Rewrite using `[this, h, map_zero]`.
-/
theorem ker_stable2 (hI : Intw M1 M2 f) (Z : Mat r s) {P : Pol p q r s} (h : P ∈ LinearMap.ker f) :
    fockAct2 p q r s Z P ∈ LinearMap.ker f := by
  rw [LinearMap.mem_ker] at h ⊢
  have := LinearMap.congr_fun (hI.2 Z) P
  simp only [LinearMap.comp_apply] at this
  rw [this, h, map_zero]

/- English proof (translation)
Assume the negation of the conclusion as `h`. Take `⟨ν, u, hu, hhw, hN⟩` from `exists_hw_notMem kLie1 wts1 (homog_fd d) (kStable_homog d) (fun Z _ P hP => ker_stable1 hI Z hP) h`. Take `⟨g, hg, h0, -⟩` from `exists_contr hI hN`. Establish `h1` using `hmin ν (g u) ⟨h0, hw_map g (fun Z _ => hg Z) hhw.2⟩`. Establish `h2` using `(degW_le_of_homog_wtSub p q r s).1 d ν u hu hhw.1 hhw.2.1`.

Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem low_vanish (hI : Intw M1 M2 f) {μ : Ix p q → ℚ}
    (hmin : ∀ ν w, IsHW M1.act ν w → degW (cPair r s) μ ≤ degW (cPair r s) ν) {d : ℕ}
    (hd : (d : ℚ) < degW (cPair r s) μ) : homog (Ix p q × Ix r s) d ≤ LinearMap.ker f := by
  by_contra h
  obtain ⟨ν, u, hu, hhw, hN⟩ := exists_hw_notMem kLie1 wts1 (homog_fd d) (kStable_homog d)
    (fun Z _ P hP => ker_stable1 hI Z hP) h
  obtain ⟨g, hg, h0, -⟩ := exists_contr hI hN
  have h1 := hmin ν (g u) ⟨h0, hw_map g (fun Z _ => hg Z) hhw.2⟩
  have h2 := (degW_le_of_homog_wtSub p q r s).1 d ν u hu hhw.1 hhw.2.1
  linarith

/- English proof (translation)
Introduce `x hx` and use `Submodule.mem_sInf.2 fun _ hN => hN.1 hx`.
-/
theorem subset_genSub {V : Type} [AddCommGroup V] [Module ℂ V]
    (a : Mat p q →ₗ[ℂ] Module.End ℂ V) (S : Set V) : S ⊆ genSub a S := fun x hx =>
  Submodule.mem_sInf.2 fun _ hN => hN.1 hx

/- English proof (translation)
The claim follows from `Submodule.mem_sInf.2 fun N hN => hN.2 Z x (Submodule.mem_sInf.1 hx N hN)`.
-/
theorem genSub_stable {V : Type} [AddCommGroup V] [Module ℂ V]
    (a : Mat p q →ₗ[ℂ] Module.End ℂ V) (S : Set V) (Z : Mat p q) {x : V} (hx : x ∈ genSub a S) :
    a Z x ∈ genSub a S :=
  Submodule.mem_sInf.2 fun N hN => hN.2 Z x (Submodule.mem_sInf.1 hx N hN)

/- English proof (translation)
Establish `hcomp : ∀ e, ∀ P ∈ hwSub (fockAct1 p q r s) μ, homogeneousComponent e P ∈ hwSub (fockAct1 p q r s) μ` using `fun e P hP => hw_map (homogeneousComponent e) (fun Z hZ v => comp_comm Z hZ e v) hP`. It suffices to establish `H : ∀ d, ∀ P ∈ homog (Ix p q × Ix r s) d, P ∈ hwSub (fockAct1 p q r s) μ → P ∈ T from mem_of_comp T P fun e => H e _ (homogeneousComponent_mem e P) (hcomp e P hP)`. Introduce `d`. Proceed by induction on `d using Nat.strong_induction_on with`. Consider the case `_ d ih`.

Introduce `P hPd hP`. Break down `lt_or_ge d 2 with h2 | h2` into its components or cases. Conclude with `hJ P ⟨fun Z _ => minusPart_low _ h2 hPd, fun Z _ => minusPart_low _ h2 hPd⟩ hP`. Take `⟨d, rfl⟩` from `Nat.exists_eq_add_of_le' h2`. Break down `lt_trichotomy ((d + 2 : ℕ) : ℚ) (degW (cPair r s) μ) with h | h | h` into its components or cases.

Conclude with `hker (low_vanish hI hmin h hPd)`. Take `⟨e1, s1, -, -⟩` from `GlobalTheory.T.fockHarmonics_graded_compactStable p q r s _ (Or.inr (Or.inr rfl))`. Establish `hlow : ∀ e, e < d + 2 → homog (Ix p q × Ix r s) e ≤ LinearMap.ker f` using `fun e he => low_vanish hI hmin (h ▸ (by exact_mod_cast he))`. Rewrite `hPd` using `[(GlobalTheory.FischerParts.fischer_parts p q r s d).2.2]`. Establish `hR : P ∈ LinearMap.ker f ⊔ (homog (Ix p q × Ix r s) (d + 2) ⊓ Submodule.span ℂ (jointHarm p q r s))`.

Rewrite using `[sup_comm]`. Use `SetLike.le_def.1 (sup_le_sup_left (Submodule.span_le.2 ?_) _) hPd` and prove the remaining obligations. Introduce and unpack `R ⟨Q, hQ, ⟨Z, -, rfl⟩ | ⟨Z, -, rfl⟩⟩`. Rewrite using `[plusPart_homog _ hQ]`. Conclude with `top_mem _ _ _ (ker_stable1 hI Z (hlow d (by omega) hQ)) (fun e he => hlow e he (homogeneousComponent_mem e _)) fun e he => comp_omAct _ he hQ`.

Rewrite using `[plusPart_homog _ hQ]`. Conclude with `top_mem _ _ _ (ker_stable2 hI Z (hlow d (by omega) hQ)) (fun e he => hlow e he (homogeneousComponent_mem e _)) fun e he => comp_omAct _ he hQ`. Use `haveI := homog_fd (p := p) (q := q) (r := r) (s := s) (d + 2)`. Take `⟨y, hy, z, hz, -, h1, rfl⟩` from `hw_sup kLie1 wts1 inferInstance (fun Z _ P hP => ker_stable1 hI Z hP) (kStable_inf (kStable_homog (d + 2)) s1) hR hP`. Conclude with `T.add_mem (hker hy) (hJ z (e1 ▸ hz.2) h1)`.

Take `⟨e1, s1, -, -⟩` from `GlobalTheory.T.fockHarmonics_graded_compactStable p q r s _ (Or.inl rfl)`. Use `haveI := homog_fd (p := p) (q := q) (r := r) (s := s) (d + 2)`. Use `haveI := homog_fd (p := p) (q := q) (r := r) (s := s) d`. Rewrite `hPd` using `[(GlobalTheory.FischerParts.fischer_parts p q r s d).2.1, ← Submodule.span_eq (homog (Ix p q × Ix r s) (d + 2) ⊓ Submodule.span ℂ (harm1 p q r s)), ← Submodule.span_union]`. Use `hw_span kLie1 wts1 T _ ?_ hPd hP` and prove the remaining obligations.

Introduce and unpack `x (hx | ⟨Q, hQ, Z, -, rfl⟩)`. Use `⟨_, inferInstance, kStable_inf (kStable_homog (d + 2)) s1, fun y hy hh => ?_, hx⟩` and prove the remaining obligations. Distinguish the cases in `h0 : y = 0`. Rewrite using `[h0]`. Conclude with `T.zero_mem`.

Take `⟨d', hd', hy'⟩` from `(harmonic_homog_of_type p q r s).1 μ y h0 (ofType_of_hw hh) (e1 ▸ hy.2)`. Use `IsHomogeneous.inj_right hy.1 hy' h0` as an intermediate fact. Rewrite `h` using `[← hd', this]`. Conclude with `absurd h (lt_irrefl _)`. Set `g : Pol p q r s →ₗ[ℂ] Pol p q r s` to `homogeneousComponent (d + 2) ∘ₗ fockAct2 p q r s Z`.

Establish `hg : ∀ Y, IsKC Y → ∀ v, g (fockAct1 p q r s Y v) = fockAct1 p q r s Y (g v)`. Introduce `Y hY v`. Simplify using `only [g, LinearMap.comp_apply]`. Rewrite using `[fockAct1_fockAct2_commute, comp_comm Y hY]`. Use `⟨(homog (Ix p q × Ix r s) d).map g, inferInstance, ?_, ?_, ⟨Q, hQ, (plusPart_homog _ hQ).symm⟩⟩` and prove the remaining obligations.

Introduce and unpack `Y hY _ ⟨v, hv, rfl⟩`. Conclude with `⟨_, kStable_homog d Y hY v hv, hg Y hY v⟩`. Introduce and unpack `_ ⟨v, hv, rfl⟩ hh`. Take `⟨u, hu, huh, e⟩` from `hw_lift kLie1 wts1 g hg inferInstance (kStable_homog d) hv hh`. Rewrite using `[← e]`.

Establish `hZu : fockAct2 p q r s Z u ∈ hwSub (fockAct1 p q r s) μ` using `hw_map (fockAct2 p q r s Z) (fun Y _ v => fockAct1_fockAct2_commute Y Z v) huh`. Conclude with `top_mem T _ _ (hst Z u (ih d (by omega) u hu huh)) (fun e he => ih e he _ (homogeneousComponent_mem e _) (hcomp e _ hZu)) fun e he => comp_omAct _ he hu`.
-/
theorem hw_mem (hI : Intw M1 M2 f) {μ : Ix p q → ℚ}
    (hmin : ∀ ν w, IsHW M1.act ν w → degW (cPair r s) μ ≤ degW (cPair r s) ν)
    (T : Submodule ℂ (Pol p q r s)) (hker : LinearMap.ker f ≤ T)
    (hst : ∀ Z, ∀ P ∈ T, fockAct2 p q r s Z P ∈ T)
    (hJ : ∀ P ∈ jointHarm p q r s, P ∈ hwSub (fockAct1 p q r s) μ → P ∈ T)
    {P : Pol p q r s} (hP : P ∈ hwSub (fockAct1 p q r s) μ) : P ∈ T := by
  have hcomp : ∀ e, ∀ P ∈ hwSub (fockAct1 p q r s) μ,
      homogeneousComponent e P ∈ hwSub (fockAct1 p q r s) μ := fun e P hP =>
    hw_map (homogeneousComponent e) (fun Z hZ v => comp_comm Z hZ e v) hP
  suffices H : ∀ d, ∀ P ∈ homog (Ix p q × Ix r s) d, P ∈ hwSub (fockAct1 p q r s) μ → P ∈ T from
    mem_of_comp T P fun e => H e _ (homogeneousComponent_mem e P) (hcomp e P hP)
  intro d
  induction d using Nat.strong_induction_on with
  | _ d ih =>
  intro P hPd hP
  rcases lt_or_ge d 2 with h2 | h2
  · exact hJ P ⟨fun Z _ => minusPart_low _ h2 hPd, fun Z _ => minusPart_low _ h2 hPd⟩ hP
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le' h2
  rcases lt_trichotomy ((d + 2 : ℕ) : ℚ) (degW (cPair r s) μ) with h | h | h
  · exact hker (low_vanish hI hmin h hPd)
  ·
    obtain ⟨e1, s1, -, -⟩ := GlobalTheory.T.fockHarmonics_graded_compactStable p q r s _ (Or.inr (Or.inr rfl))
    have hlow : ∀ e, e < d + 2 → homog (Ix p q × Ix r s) e ≤ LinearMap.ker f := fun e he =>
      low_vanish hI hmin (h ▸ (by exact_mod_cast he))
    rw [(GlobalTheory.FischerParts.fischer_parts p q r s d).2.2] at hPd
    have hR : P ∈ LinearMap.ker f ⊔
        (homog (Ix p q × Ix r s) (d + 2) ⊓ Submodule.span ℂ (jointHarm p q r s)) := by
      rw [sup_comm]
      refine SetLike.le_def.1 (sup_le_sup_left (Submodule.span_le.2 ?_) _) hPd
      rintro R ⟨Q, hQ, ⟨Z, -, rfl⟩ | ⟨Z, -, rfl⟩⟩
      · rw [plusPart_homog _ hQ]
        exact top_mem _ _ _ (ker_stable1 hI Z (hlow d (by omega) hQ))
          (fun e he => hlow e he (homogeneousComponent_mem e _)) fun e he => comp_omAct _ he hQ
      · rw [plusPart_homog _ hQ]
        exact top_mem _ _ _ (ker_stable2 hI Z (hlow d (by omega) hQ))
          (fun e he => hlow e he (homogeneousComponent_mem e _)) fun e he => comp_omAct _ he hQ
    haveI := homog_fd (p := p) (q := q) (r := r) (s := s) (d + 2)
    obtain ⟨y, hy, z, hz, -, h1, rfl⟩ := hw_sup kLie1 wts1 inferInstance
      (fun Z _ P hP => ker_stable1 hI Z hP) (kStable_inf (kStable_homog (d + 2)) s1) hR hP
    exact T.add_mem (hker hy) (hJ z (e1 ▸ hz.2) h1)
  ·
    obtain ⟨e1, s1, -, -⟩ := GlobalTheory.T.fockHarmonics_graded_compactStable p q r s _ (Or.inl rfl)
    haveI := homog_fd (p := p) (q := q) (r := r) (s := s) (d + 2)
    haveI := homog_fd (p := p) (q := q) (r := r) (s := s) d
    rw [(GlobalTheory.FischerParts.fischer_parts p q r s d).2.1,
      ← Submodule.span_eq (homog (Ix p q × Ix r s) (d + 2) ⊓ Submodule.span ℂ (harm1 p q r s)),
      ← Submodule.span_union] at hPd
    refine hw_span kLie1 wts1 T _ ?_ hPd hP
    rintro x (hx | ⟨Q, hQ, Z, -, rfl⟩)
    · refine ⟨_, inferInstance, kStable_inf (kStable_homog (d + 2)) s1, fun y hy hh => ?_, hx⟩
      by_cases h0 : y = 0
      · rw [h0]; exact T.zero_mem
      obtain ⟨d', hd', hy'⟩ := (harmonic_homog_of_type p q r s).1 μ y h0 (ofType_of_hw hh)
        (e1 ▸ hy.2)
      have := IsHomogeneous.inj_right hy.1 hy' h0
      rw [← hd', this] at h
      exact absurd h (lt_irrefl _)
    · let g : Pol p q r s →ₗ[ℂ] Pol p q r s := homogeneousComponent (d + 2) ∘ₗ fockAct2 p q r s Z
      have hg : ∀ Y, IsKC Y → ∀ v, g (fockAct1 p q r s Y v) = fockAct1 p q r s Y (g v) := by
        intro Y hY v
        simp only [g, LinearMap.comp_apply]
        rw [fockAct1_fockAct2_commute, comp_comm Y hY]
      refine ⟨(homog (Ix p q × Ix r s) d).map g, inferInstance, ?_, ?_,
        ⟨Q, hQ, (plusPart_homog _ hQ).symm⟩⟩
      · rintro Y hY _ ⟨v, hv, rfl⟩
        exact ⟨_, kStable_homog d Y hY v hv, hg Y hY v⟩
      · rintro _ ⟨v, hv, rfl⟩ hh
        obtain ⟨u, hu, huh, e⟩ := hw_lift kLie1 wts1 g hg inferInstance (kStable_homog d) hv hh
        rw [← e]
        have hZu : fockAct2 p q r s Z u ∈ hwSub (fockAct1 p q r s) μ :=
          hw_map (fockAct2 p q r s Z) (fun Y _ v => fockAct1_fockAct2_commute Y Z v) huh
        exact top_mem T _ _ (hst Z u (ih d (by omega) u hu huh))
          (fun e he => ih e he _ (homogeneousComponent_mem e _) (hcomp e _ hZu))
          fun e he => comp_omAct _ he hu

end Main

end GlobalTheory.FockAlg.MinFirst

open GlobalTheory.FockAlg.MinFirst in

/- English proof (translation)
Introduce `p q r s M1 M2 f hirr _ hI hf μ hμ hmin`. Take `⟨e1, s1, s2, -⟩` from `GlobalTheory.T.fockHarmonics_graded_compactStable p q r s _ (Or.inr (Or.inr rfl))`. Prove the components needed by the constructor for the conclusion. Take `⟨v, hv⟩` from `hμ`. Take `⟨P0, hP0⟩` from `DFunLike.ne_iff.1 hf`.

Take `⟨g, hg, h0, hfg⟩` from `exists_contr hI (P := P0) hP0`. Establish `htop : LinearMap.range g = ⊤`. Use `(hirr.2 _ ?_).resolve_left fun h => h0 ?_` and prove the remaining obligations. Introduce and unpack `Z _ ⟨y, rfl⟩`. Conclude with `⟨_, hg Z y⟩`.

Rewrite using `[← Submodule.mem_bot ℂ, ← h]`. Conclude with `⟨P0, rfl⟩`. Take `⟨w, rfl⟩ : v ∈ LinearMap.range g` from `htop ▸ Submodule.mem_top`. Take `⟨W, fW, hw, sW⟩` from `((GlobalTheory.FockPolGK.pol_locFin_weights p q r s).1 w).1`. Take `⟨u, -, huh, e⟩` from `hw_lift kLie1 wts1 g (fun Z _ => hg Z) fW sW hw hv.2`.

Establish `hex : ∃ Q ∈ jointHarm p q r s, Q ∈ hwSub (fockAct1 p q r s) μ ∧ Q ∉ LinearMap.ker f`. Assume the negation of the conclusion as `hno`. Use `push Not at hno`. Conclude with `hv.1 (e ▸ hfg u (hw_mem hI hmin (LinearMap.ker f) le_rfl (fun Z P hP => ker_stable2 hI Z hP) hno huh))`. Take `⟨Q, hQ, hQh, hQf⟩` from `hex`.

Take `⟨U, fU, hU, sU⟩` from `((GlobalTheory.FockPolGK.pol_locFin_weights p q r s).2 Q).1`. Establish `sH : KStable (fockAct2 p q r s) (hwSub (fockAct1 p q r s) μ)` using `fun Z _ w hw => hw_map (fockAct2 p q r s Z) (fun Y _ v => fockAct1_fockAct2_commute Y Z v) hw`. Take `⟨ν, P, hP, hhw, hN⟩` from `exists_hw_notMem kLie2 wts2 (W := U ⊓ (Submodule.span ℂ (jointHarm p q r s) ⊓ hwSub (fockAct1 p q r s) μ)) (N := LinearMap.ker f) inferInstance (kStable_inf sU (kStable_inf s2 sH)) (fun Z _ P hP => ker_stable2 hI Z hP) (fun h => hQf (h ⟨hU, Submodule.subset_span hQ, hQh⟩))`. Conclude with `⟨ν, P, e1 ▸ hP.2.1, ⟨hhw.1, hP.2.2⟩, hhw, hN⟩`. Introduce `P ⟨W, fW, hP, sW, hW⟩ set S := {Q | Q ∈ jointHarm p q r s ∧ OfType (fockAct1 p q r s) μ Q} with hS`.

Rewrite using `[← Submodule.mem_comap, Submodule.comap_map_eq]`. Establish `sG : KStable (fockAct1 p q r s) (genSub (fockAct2 p q r s) S)`. Introduce `X hX y hy`. Use `Submodule.mem_sInf.1 hy ((genSub (fockAct2 p q r s) S).comap (fockAct1 p q r s X)) ⟨?_, fun Z y hy => ?_⟩` and prove the remaining obligations. Introduce and unpack `Q ⟨hQ, U, fU, hU, sU, tU⟩`.

Use `subset_genSub _ S ⟨?_, U, fU, sU X hX Q hU, sU, tU⟩` and prove the remaining obligations. Rewrite using `[← e1]`. Conclude with `s1 X hX Q (Submodule.subset_span hQ)`. Rewrite using `[Submodule.mem_comap, ← fockAct1_fockAct2_commute]`. Conclude with `genSub_stable _ _ Z hy`.

Establish `hle : W ≤ genSub (fockAct2 p q r s) S ⊔ LinearMap.ker f`. Assume the negation of the conclusion as `h`. Take `⟨ν, u, hu, hhw, hN⟩` from `exists_hw_notMem kLie1 wts1 fW sW (kStable_sup sG fun Z _ P hP => ker_stable1 hI Z hP) h`. Take `rfl` from `hW ν u hu hhw`. Use `hN (hw_mem hI hmin _ le_sup_right ?_ ?_ hhw.2)` and prove the remaining obligations.

Introduce `Z y hy`. Take `⟨a, ha, b, hb, rfl⟩` from `Submodule.mem_sup.1 hy`. Rewrite using `[map_add]`. Conclude with `Submodule.add_mem_sup (genSub_stable _ _ Z ha) (ker_stable2 hI Z hb)`. Conclude with `fun Q hQ hh => Submodule.mem_sup_left (subset_genSub _ S ⟨hQ, ofType_of_hw hh⟩)`.

Conclude with `hle hP`.
-/
theorem GlobalTheory.FockAlg.min_first : ∀ (p q r s : ℕ) (M1 : GKMod p q) (M2 : GKMod r s) (f : Pol p q r s →ₗ[ℂ] TensorProduct ℂ M1.V M2.V), IrrGK M1 → AdmGK M1 → Intw M1 M2 f → f ≠ 0 → ∀ (μ : Ix p q → ℚ), (∃ v, IsHW M1.act μ v) → (∀ ν w, IsHW M1.act ν w → degW (cPair r s) μ ≤ degW (cPair r s) ν) → (∃ (μ' : Ix r s → ℚ) (P : Pol p q r s), P ∈ jointHarm p q r s ∧ IsHW (fockAct1 p q r s) μ P ∧ IsHW (fockAct2 p q r s) μ' P ∧ f P ≠ 0) ∧ ∀ P, OfType (fockAct1 p q r s) μ P → f P ∈ Submodule.map f (genSub (fockAct2 p q r s) {Q | Q ∈ jointHarm p q r s ∧ OfType (fockAct1 p q r s) μ Q}) := by
  intro p q r s M1 M2 f hirr _ hI hf μ hμ hmin
  obtain ⟨e1, s1, s2, -⟩ := GlobalTheory.T.fockHarmonics_graded_compactStable p q r s _ (Or.inr (Or.inr rfl))
  constructor
  · obtain ⟨v, hv⟩ := hμ
    obtain ⟨P0, hP0⟩ := DFunLike.ne_iff.1 hf
    obtain ⟨g, hg, h0, hfg⟩ := exists_contr hI (P := P0) hP0
    have htop : LinearMap.range g = ⊤ := by
      refine (hirr.2 _ ?_).resolve_left fun h => h0 ?_
      · rintro Z _ ⟨y, rfl⟩
        exact ⟨_, hg Z y⟩
      · rw [← Submodule.mem_bot ℂ, ← h]; exact ⟨P0, rfl⟩
    obtain ⟨w, rfl⟩ : v ∈ LinearMap.range g := htop ▸ Submodule.mem_top
    obtain ⟨W, fW, hw, sW⟩ := ((GlobalTheory.FockPolGK.pol_locFin_weights p q r s).1 w).1
    obtain ⟨u, -, huh, e⟩ := hw_lift kLie1 wts1 g (fun Z _ => hg Z) fW sW hw hv.2
    have hex : ∃ Q ∈ jointHarm p q r s, Q ∈ hwSub (fockAct1 p q r s) μ ∧ Q ∉ LinearMap.ker f := by
      by_contra hno
      push Not at hno
      exact hv.1 (e ▸ hfg u
        (hw_mem hI hmin (LinearMap.ker f) le_rfl (fun Z P hP => ker_stable2 hI Z hP) hno huh))
    obtain ⟨Q, hQ, hQh, hQf⟩ := hex
    obtain ⟨U, fU, hU, sU⟩ := ((GlobalTheory.FockPolGK.pol_locFin_weights p q r s).2 Q).1
    have sH : KStable (fockAct2 p q r s) (hwSub (fockAct1 p q r s) μ) := fun Z _ w hw =>
      hw_map (fockAct2 p q r s Z) (fun Y _ v => fockAct1_fockAct2_commute Y Z v) hw
    obtain ⟨ν, P, hP, hhw, hN⟩ := exists_hw_notMem kLie2 wts2
      (W := U ⊓ (Submodule.span ℂ (jointHarm p q r s) ⊓ hwSub (fockAct1 p q r s) μ))
      (N := LinearMap.ker f) inferInstance (kStable_inf sU (kStable_inf s2 sH))
      (fun Z _ P hP => ker_stable2 hI Z hP)
      (fun h => hQf (h ⟨hU, Submodule.subset_span hQ, hQh⟩))
    exact ⟨ν, P, e1 ▸ hP.2.1, ⟨hhw.1, hP.2.2⟩, hhw, hN⟩
  · intro P ⟨W, fW, hP, sW, hW⟩
    set S := {Q | Q ∈ jointHarm p q r s ∧ OfType (fockAct1 p q r s) μ Q} with hS
    rw [← Submodule.mem_comap, Submodule.comap_map_eq]
    have sG : KStable (fockAct1 p q r s) (genSub (fockAct2 p q r s) S) := by
      intro X hX y hy
      refine Submodule.mem_sInf.1 hy ((genSub (fockAct2 p q r s) S).comap (fockAct1 p q r s X))
        ⟨?_, fun Z y hy => ?_⟩
      · rintro Q ⟨hQ, U, fU, hU, sU, tU⟩
        refine subset_genSub _ S ⟨?_, U, fU, sU X hX Q hU, sU, tU⟩
        rw [← e1]
        exact s1 X hX Q (Submodule.subset_span hQ)
      · rw [Submodule.mem_comap, ← fockAct1_fockAct2_commute]
        exact genSub_stable _ _ Z hy
    have hle : W ≤ genSub (fockAct2 p q r s) S ⊔ LinearMap.ker f := by
      by_contra h
      obtain ⟨ν, u, hu, hhw, hN⟩ := exists_hw_notMem kLie1 wts1 fW sW
        (kStable_sup sG fun Z _ P hP => ker_stable1 hI Z hP) h
      obtain rfl := hW ν u hu hhw
      refine hN (hw_mem hI hmin _ le_sup_right ?_ ?_ hhw.2)
      · intro Z y hy
        obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.1 hy
        rw [map_add]
        exact Submodule.add_mem_sup (genSub_stable _ _ Z ha) (ker_stable2 hI Z hb)
      · exact fun Q hQ hh => Submodule.mem_sup_left (subset_genSub _ S ⟨hQ, ofType_of_hw hh⟩)
    exact hle hP

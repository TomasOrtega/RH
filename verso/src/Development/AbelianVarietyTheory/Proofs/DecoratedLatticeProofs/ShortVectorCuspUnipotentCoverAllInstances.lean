import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsRealCoord
import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.AdelicPair
import CompanionTheory.HarishChandraModules.KFiniteAnalyticVectors.FundamentalDomainCusps.AutomorphicFormsFiniteDimensional

noncomputable section

open NumberField Matrix Formalism.MainNotions.S GlobalTheory.CuspGeo GlobalTheory.ClassFin
open scoped Topology

namespace GlobalTheory.CuspGeo

section

variable (I : AutInst)

/- English proof (translation)
Simplify using `only [Formalism.UG.hform, dotProduct, mulVec, Finset.mul_sum, Pi.star_apply, starRingEnd_apply]`. Use `Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Expand and normalize the polynomial expressions, which then agree.
-/
theorem hform_eq_dot {K : Type} [Field K] [StarRing K] {n : ℕ} (J : Matrix (Fin n) (Fin n) K)
    (x y : Fin n → K) : Formalism.UG.hform (starRingEnd K) J x y = star x ⬝ᵥ (J *ᵥ y) := by
  simp only [Formalism.UG.hform, dotProduct, mulVec, Finset.mul_sum, Pi.star_apply, starRingEnd_apply]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

/- English proof (translation)
Introduce `v`. Take `⟨h1, h2, h3⟩` from `hm.1 v`. Use `show CompanionTheory.D.gk.RF.Lowers (Formalism.REAL.Jm (I.ε v)) (CompanionTheory.D.gk.RF.Wv I W v) (uMat (m v) - 1)`. Establish `hdet` using `CompanionTheory.D.gk.RF.P_det I v`. Establish `hPi : I.P v * (I.P v)⁻¹ = 1` using `mul_nonsing_inv _ hdet`.

Establish `hiP : (I.P v)⁻¹ * I.P v = 1` using `nonsing_inv_mul _ hdet`. Establish `hB : ∀ z, (I.P v * uMat (m v) * (I.P v)⁻¹ - 1) *ᵥ (I.P v *ᵥ z) = I.P v *ᵥ ((uMat (m v) - 1) *ᵥ z)` using `fun z => by`. Rewrite using `[mulVec_mulVec, mulVec_mulVec, Matrix.sub_mul, Matrix.one_mul, Matrix.mul_assoc _ (I.P v)⁻¹ (I.P v), hiP, Matrix.mul_one, Matrix.mul_sub, Matrix.mul_one]`. Establish `hWC : ∀ w ∈ CompanionTheory.D.gk.RF.Wv I W v, I.P v *ᵥ w ∈ Submodule.span ℂ ((fun w : Fin I.n → I.E => fun i => I.φ v (w i)) '' (W : Set _))` using `fun w hw => by`. Proceed by induction on `hw using Submodule.span_induction with`.

Consider the case `mem x hx`. Take `⟨u, hu, rfl⟩` from `hx`. Rewrite using `[CompanionTheory.D.gk.RF.P_atV]`. Conclude with `Submodule.subset_span ⟨u, hu, rfl⟩`. Consider the case `zero => rw [mulVec_zero]`.

Conclude with `Submodule.zero_mem _`. Consider the case `add a b _ _ ha hb => rw [mulVec_add]`. Conclude with `Submodule.add_mem _ ha hb`. Consider the case `smul c a _ ha => rw [mulVec_smul]`. Conclude with `Submodule.smul_mem _ _ ha`.

Establish `hWv : ∀ x ∈ Submodule.span ℂ ((fun w : Fin I.n → I.E => fun i => I.φ v (w i)) '' (W : Set _)), (I.P v)⁻¹ *ᵥ x ∈ CompanionTheory.D.gk.RF.Wv I W v` using `fun x hx => by`. Proceed by induction on `hx using Submodule.span_induction with`. Consider the case `mem x hx`. Take `⟨u, hu, rfl⟩` from `hx`. Conclude with `Submodule.subset_span ⟨u, hu, rfl⟩`.

Consider the case `zero => rw [mulVec_zero]`. Conclude with `Submodule.zero_mem _`. Consider the case `add a b _ _ ha hb => rw [mulVec_add]`. Conclude with `Submodule.add_mem _ ha hb`. Consider the case `smul c a _ ha => rw [mulVec_smul]`.

Conclude with `Submodule.smul_mem _ _ ha`. Establish `hfP : ∀ w z, CompanionTheory.D.gk.RF.hf (Formalism.REAL.Jm (I.ε v)) w z = Formalism.UG.hform (starRingEnd ℂ) (I.J.map (I.φ v)) (I.P v *ᵥ w) (I.P v *ᵥ z)` using `fun w z => by`. Rewrite using `[hform_eq_dot, CompanionTheory.D.gk.RF.hf, ← I.P_spec v, star_mulVec, ← dotProduct_mulVec, mulVec_mulVec, mulVec_mulVec, Matrix.mul_assoc]`. Establish `hc1 : ∀ z ∈ CompanionTheory.D.gk.RF.perp (Formalism.REAL.Jm (I.ε v)) (CompanionTheory.D.gk.RF.Wv I W v), ∀ x ∈ Submodule.span ℂ ((fun w : Fin I.n → I.E => fun i => I.φ v (w i)) '' (W : Set _)), Formalism.UG.hform (starRingEnd ℂ) (I.J.map (I.φ v)) x (I.P v *ᵥ z) = 0` using `fun z hz x hx => by`. Establish `e : x = I.P v *ᵥ ((I.P v)⁻¹ *ᵥ x)` using `by rw [mulVec_mulVec, hPi, one_mulVec]`.

Rewrite using `[e, ← hfP]`. Conclude with `hz _ (hWv x hx)`. Establish `hc2 : ∀ z, (∀ x ∈ Submodule.span ℂ ((fun w : Fin I.n → I.E => fun i => I.φ v (w i)) '' (W : Set _)), Formalism.UG.hform (starRingEnd ℂ) (I.J.map (I.φ v)) x (I.P v *ᵥ z) = 0) → z ∈ CompanionTheory.D.gk.RF.perp (Formalism.REAL.Jm (I.ε v)) (CompanionTheory.D.gk.RF.Wv I W v)` using `fun z h w hw => by`. Rewrite using `[hfP]`. Conclude with `h _ (hWC w hw)`.

Establish `inj : ∀ a : Fin I.n → ℂ, a = (I.P v)⁻¹ *ᵥ (I.P v *ᵥ a)` using `fun a => by`. Rewrite using `[mulVec_mulVec, hiP, one_mulVec]`. Use `⟨fun w hw => ?_, fun z hz => ?_, fun z => ?_⟩` and prove the remaining obligations. Use `h1 _ (hWC w hw)` as an intermediate fact. Rewrite `this` using `[hB]`.

Rewrite using `[inj ((uMat (m v) - 1) *ᵥ w), this, mulVec_zero]`. Use `h2 _ (hc1 z hz)` as an intermediate fact. Rewrite `this` using `[hB]`. Rewrite using `[inj ((uMat (m v) - 1) *ᵥ z)]`. Conclude with `hWv _ this`.

Use `hc2 _ fun x hx => ?_` and prove the remaining obligations. Use `h3 (I.P v *ᵥ z)` as an intermediate fact. Rewrite `this` using `[hB]`. Conclude with `this x hx`.
-/
theorem mem_NInf_of_NA {W : Submodule I.E (Fin I.n → I.E)} {m : I.Ginf} (hm : ((m, 1) : I.GA) ∈ I.NA W) :
    m ∈ CompanionTheory.D.gk.RF.NInf I W := by
  intro v
  obtain ⟨h1, h2, h3⟩ := hm.1 v
  show CompanionTheory.D.gk.RF.Lowers (Formalism.REAL.Jm (I.ε v)) (CompanionTheory.D.gk.RF.Wv I W v) (uMat (m v) - 1)
  have hdet := CompanionTheory.D.gk.RF.P_det I v
  have hPi : I.P v * (I.P v)⁻¹ = 1 := mul_nonsing_inv _ hdet
  have hiP : (I.P v)⁻¹ * I.P v = 1 := nonsing_inv_mul _ hdet
  have hB : ∀ z, (I.P v * uMat (m v) * (I.P v)⁻¹ - 1) *ᵥ (I.P v *ᵥ z) =
      I.P v *ᵥ ((uMat (m v) - 1) *ᵥ z) := fun z => by
    rw [mulVec_mulVec, mulVec_mulVec, Matrix.sub_mul, Matrix.one_mul, Matrix.mul_assoc _ (I.P v)⁻¹ (I.P v), hiP,
      Matrix.mul_one, Matrix.mul_sub, Matrix.mul_one]
  have hWC : ∀ w ∈ CompanionTheory.D.gk.RF.Wv I W v, I.P v *ᵥ w ∈
      Submodule.span ℂ ((fun w : Fin I.n → I.E => fun i => I.φ v (w i)) '' (W : Set _)) := fun w hw => by
    induction hw using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨u, hu, rfl⟩ := hx
      rw [CompanionTheory.D.gk.RF.P_atV]
      exact Submodule.subset_span ⟨u, hu, rfl⟩
    | zero => rw [mulVec_zero]; exact Submodule.zero_mem _
    | add a b _ _ ha hb => rw [mulVec_add]; exact Submodule.add_mem _ ha hb
    | smul c a _ ha => rw [mulVec_smul]; exact Submodule.smul_mem _ _ ha
  have hWv : ∀ x ∈ Submodule.span ℂ ((fun w : Fin I.n → I.E => fun i => I.φ v (w i)) '' (W : Set _)),
      (I.P v)⁻¹ *ᵥ x ∈ CompanionTheory.D.gk.RF.Wv I W v := fun x hx => by
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨u, hu, rfl⟩ := hx
      exact Submodule.subset_span ⟨u, hu, rfl⟩
    | zero => rw [mulVec_zero]; exact Submodule.zero_mem _
    | add a b _ _ ha hb => rw [mulVec_add]; exact Submodule.add_mem _ ha hb
    | smul c a _ ha => rw [mulVec_smul]; exact Submodule.smul_mem _ _ ha
  have hfP : ∀ w z, CompanionTheory.D.gk.RF.hf (Formalism.REAL.Jm (I.ε v)) w z =
      Formalism.UG.hform (starRingEnd ℂ) (I.J.map (I.φ v)) (I.P v *ᵥ w) (I.P v *ᵥ z) := fun w z => by
    rw [hform_eq_dot, CompanionTheory.D.gk.RF.hf, ← I.P_spec v, star_mulVec, ← dotProduct_mulVec, mulVec_mulVec,
      mulVec_mulVec, Matrix.mul_assoc]
  have hc1 : ∀ z ∈ CompanionTheory.D.gk.RF.perp (Formalism.REAL.Jm (I.ε v)) (CompanionTheory.D.gk.RF.Wv I W v),
      ∀ x ∈ Submodule.span ℂ ((fun w : Fin I.n → I.E => fun i => I.φ v (w i)) '' (W : Set _)),
      Formalism.UG.hform (starRingEnd ℂ) (I.J.map (I.φ v)) x (I.P v *ᵥ z) = 0 := fun z hz x hx => by
    have e : x = I.P v *ᵥ ((I.P v)⁻¹ *ᵥ x) := by rw [mulVec_mulVec, hPi, one_mulVec]
    rw [e, ← hfP]
    exact hz _ (hWv x hx)
  have hc2 : ∀ z, (∀ x ∈ Submodule.span ℂ ((fun w : Fin I.n → I.E => fun i => I.φ v (w i)) '' (W : Set _)),
      Formalism.UG.hform (starRingEnd ℂ) (I.J.map (I.φ v)) x (I.P v *ᵥ z) = 0) →
      z ∈ CompanionTheory.D.gk.RF.perp (Formalism.REAL.Jm (I.ε v)) (CompanionTheory.D.gk.RF.Wv I W v) := fun z h w hw => by
    rw [hfP]
    exact h _ (hWC w hw)
  have inj : ∀ a : Fin I.n → ℂ, a = (I.P v)⁻¹ *ᵥ (I.P v *ᵥ a) := fun a => by
    rw [mulVec_mulVec, hiP, one_mulVec]
  refine ⟨fun w hw => ?_, fun z hz => ?_, fun z => ?_⟩
  · have := h1 _ (hWC w hw)
    rw [hB] at this
    rw [inj ((uMat (m v) - 1) *ᵥ w), this, mulVec_zero]
  · have := h2 _ (hc1 z hz)
    rw [hB] at this
    rw [inj ((uMat (m v) - 1) *ᵥ z)]
    exact hWv _ this
  · refine hc2 _ fun x hx => ?_
    have := h3 (I.P v *ᵥ z)
    rw [hB] at this
    exact this x hx

/- English proof (translation)
Introduce `U hU`. Take `⟨M, hM, hMU⟩` from `CompanionTheory.D.gk.RF.congruence_subgroup_compact_open I U hU`. Take `⟨s₁, hs₁, hSI⟩` from `CompanionTheory.D.gk.RF.short_isotropic_vector_of CompanionTheory.D.gk.RF.transport_to_standard_form I`. Take `⟨C₁, hC₁, hCS⟩` from `CompanionTheory.D.gk.RF.covolume_span I`. Take `⟨C₂, hC₂, hCP⟩` from `CompanionTheory.D.gk.RF.covolume_orthogonal_complement CompanionTheory.D.gk.RF.transport_to_standard_form I`.

Take `⟨C₃, hC₃, hNC⟩` from `CompanionTheory.D.gk.RF.nilpotent_cover_of CompanionTheory.D.gk.RF.transport_to_standard_form CompanionTheory.D.gk.RF.gamSub CompanionTheory.D.gk.RF.nilpotent_lie_algebra CompanionTheory.D.gk.RF.nilpotent_subgroup_representation I M hM`. Use `set s₀ := min s₁ 1`. Establish `hs₀ : 0 < s₀` using `lt_min hs₁ one_pos`. Establish `hD : 0 < 2 * (C₁ + C₂ + 1)` using `by positivity`. Use `⟨s₀, 1 / (2 * (C₁ + C₂ + 1)), C₃ * (C₁ + C₂), hs₀, by positivity, fun y η hη hηη₀ hc => ?_⟩` and prove the remaining obligations.

Establish `hηD : η * (2 * (C₁ + C₂ + 1)) ≤ 1` using `(le_div_iff₀ hD).1 hηη₀`. Establish `hη1 : η < 1` using `by nlinarith [mul_pos hη hC₁, mul_pos hη hC₂]`. Establish `hηb : (C₁ + C₂) * η ≤ 1` using `by nlinarith [mul_pos hη hC₁, mul_pos hη hC₂]`. Establish `hηa : 2 * C₁ * η ≤ 1` using `by nlinarith [mul_pos hη hC₁, mul_pos hη hC₂]`. Take `⟨u, hu, hu0, hus⟩` from `hc`.

Establish `hc' : ∃ u ∈ CompanionTheory.D.gk.RF.IntV I, u ≠ 0 ∧ ‖CompanionTheory.D.gk.RF.vecAt I y u‖ ≤ s₀ * η ^ (I.n + 1)` using `⟨u, hu, hu0, hus⟩`. Take `⟨t, ht, hts, d, w, hd, hw, hne, hall⟩` from `CompanionTheory.D.gk.RF.successive_minima_gap I.E I.n (CompanionTheory.D.gk.RF.IntV I) (fun u => ‖CompanionTheory.D.gk.RF.vecAt I y u‖) s₀ η hs₀ hη hη1 hc'`. Establish `ht1 : t ≤ 1` using `hts.trans (min_le_right _ _)`. Establish `hs : η * t ≤ s₁` using `(mul_le_of_le_one_left ht.le hη1.le).trans (hts.trans (min_le_left _ _))`. Establish `hI : CompanionTheory.D.gk.RF.Isot I.J (Submodule.span I.E (Set.range w))` using `Submodule.span_le.2 (by`.

Introduce and unpack `_ ⟨j, rfl⟩`. Conclude with `CompanionTheory.D.gk.RF.mem_perp_spanC fun i => hSI y _ (hw i).1 _ (hw j).1 ((hw i).2.trans hs) ((hw j).2.trans hs))`. Establish `c1` using `hCS y d w (η * t) hd (by positivity) hw`. Establish `c2` using `hCP y _ _ t ht (by nlinarith) c1 fun u hu hn => by`. Assume the negation of the conclusion as `h`.

Conclude with `hn (hall u hu (not_le.1 h).le)`. Establish `hρ : η * t * (C₁ * (η * t) + C₂ / t) ≤ (C₁ + C₂) * η`. Establish `e : η * t * (C₁ * (η * t) + C₂ / t) = C₁ * η * (η * t * t) + C₂ * η` using `by field_simp`. Establish `: η * t * t ≤ 1` using `mul_le_one₀ (mul_le_one₀ hη1.le ht.le ht1) ht.le ht1`. Use `mul_le_of_le_one_right (by positivity : 0 ≤ C₁ * η) this` as an intermediate fact.

Rewrite using `[e]`. Combine the linear equalities and inequalities to obtain the conclusion. Use `⟨Submodule.span I.E (Set.range w), ⟨hne, fun x hx z hz => ?_⟩, fun m hm => ?_⟩` and prove the remaining obligations. Use `hI hz x hx` as an intermediate fact. Rewrite using `[hform_eq_dot]`.

Conclude with `this`. Take `⟨γ, h1, -, h3⟩` from `hNC y d w (η * t) (C₁ * (η * t) + C₂ / t) hd (by positivity) (by positivity) (hρ.trans hηb) hw hI (c1.mono (le_add_of_nonneg_right (by positivity))) (c2.mono (le_add_of_nonneg_left (by positivity))) m (mem_NInf_of_NA I hm)`. Take `⟨x, hxU, hx⟩` from `hMU γ h1`. Use `⟨(γ, x), hx, hxU, fun v i j => (h3 v i j).trans ?_⟩` and prove the remaining obligations. Rewrite using `[mul_assoc C₃]`.

Conclude with `mul_le_mul_of_nonneg_left hρ hC₃.le`.
-/
theorem shortCusp_holds : ShortCusp I := by
  intro U hU
  obtain ⟨M, hM, hMU⟩ := CompanionTheory.D.gk.RF.congruence_subgroup_compact_open I U hU
  obtain ⟨s₁, hs₁, hSI⟩ := CompanionTheory.D.gk.RF.short_isotropic_vector_of CompanionTheory.D.gk.RF.transport_to_standard_form I
  obtain ⟨C₁, hC₁, hCS⟩ := CompanionTheory.D.gk.RF.covolume_span I
  obtain ⟨C₂, hC₂, hCP⟩ := CompanionTheory.D.gk.RF.covolume_orthogonal_complement CompanionTheory.D.gk.RF.transport_to_standard_form I
  obtain ⟨C₃, hC₃, hNC⟩ := CompanionTheory.D.gk.RF.nilpotent_cover_of CompanionTheory.D.gk.RF.transport_to_standard_form CompanionTheory.D.gk.RF.gamSub
    CompanionTheory.D.gk.RF.nilpotent_lie_algebra CompanionTheory.D.gk.RF.nilpotent_subgroup_representation I M hM
  set s₀ := min s₁ 1
  have hs₀ : 0 < s₀ := lt_min hs₁ one_pos
  have hD : 0 < 2 * (C₁ + C₂ + 1) := by positivity
  refine ⟨s₀, 1 / (2 * (C₁ + C₂ + 1)), C₃ * (C₁ + C₂), hs₀, by positivity, fun y η hη hηη₀ hc => ?_⟩
  have hηD : η * (2 * (C₁ + C₂ + 1)) ≤ 1 := (le_div_iff₀ hD).1 hηη₀
  have hη1 : η < 1 := by nlinarith [mul_pos hη hC₁, mul_pos hη hC₂]
  have hηb : (C₁ + C₂) * η ≤ 1 := by nlinarith [mul_pos hη hC₁, mul_pos hη hC₂]
  have hηa : 2 * C₁ * η ≤ 1 := by nlinarith [mul_pos hη hC₁, mul_pos hη hC₂]
  obtain ⟨u, hu, hu0, hus⟩ := hc
  have hc' : ∃ u ∈ CompanionTheory.D.gk.RF.IntV I, u ≠ 0 ∧ ‖CompanionTheory.D.gk.RF.vecAt I y u‖ ≤ s₀ * η ^ (I.n + 1) :=
    ⟨u, hu, hu0, hus⟩
  obtain ⟨t, ht, hts, d, w, hd, hw, hne, hall⟩ := CompanionTheory.D.gk.RF.successive_minima_gap I.E I.n (CompanionTheory.D.gk.RF.IntV I)
    (fun u => ‖CompanionTheory.D.gk.RF.vecAt I y u‖) s₀ η hs₀ hη hη1 hc'
  have ht1 : t ≤ 1 := hts.trans (min_le_right _ _)
  have hs : η * t ≤ s₁ := (mul_le_of_le_one_left ht.le hη1.le).trans (hts.trans (min_le_left _ _))
  have hI : CompanionTheory.D.gk.RF.Isot I.J (Submodule.span I.E (Set.range w)) := Submodule.span_le.2 (by
    rintro _ ⟨j, rfl⟩
    exact CompanionTheory.D.gk.RF.mem_perp_spanC fun i => hSI y _ (hw i).1 _ (hw j).1 ((hw i).2.trans hs) ((hw j).2.trans hs))
  have c1 := hCS y d w (η * t) hd (by positivity) hw
  have c2 := hCP y _ _ t ht (by nlinarith) c1 fun u hu hn => by
    by_contra h
    exact hn (hall u hu (not_le.1 h).le)
  have hρ : η * t * (C₁ * (η * t) + C₂ / t) ≤ (C₁ + C₂) * η := by
    have e : η * t * (C₁ * (η * t) + C₂ / t) = C₁ * η * (η * t * t) + C₂ * η := by field_simp
    have : η * t * t ≤ 1 := mul_le_one₀ (mul_le_one₀ hη1.le ht.le ht1) ht.le ht1
    have := mul_le_of_le_one_right (by positivity : 0 ≤ C₁ * η) this
    rw [e]; linarith
  refine ⟨Submodule.span I.E (Set.range w), ⟨hne, fun x hx z hz => ?_⟩, fun m hm => ?_⟩
  · have := hI hz x hx
    rw [hform_eq_dot]
    exact this
  obtain ⟨γ, h1, -, h3⟩ := hNC y d w (η * t) (C₁ * (η * t) + C₂ / t) hd (by positivity) (by positivity)
    (hρ.trans hηb) hw hI (c1.mono (le_add_of_nonneg_right (by positivity)))
    (c2.mono (le_add_of_nonneg_left (by positivity))) m (mem_NInf_of_NA I hm)
  obtain ⟨x, hxU, hx⟩ := hMU γ h1
  refine ⟨(γ, x), hx, hxU, fun v i j => (h3 v i j).trans ?_⟩
  rw [mul_assoc C₃]
  exact mul_le_mul_of_nonneg_left hρ hC₃.le

end

/- English proof (translation)
The claim follows from `shortCusp_holds`.
-/
theorem shortCusp_all : ∀ I : AutInst, ShortCusp I := shortCusp_holds

end GlobalTheory.CuspGeo

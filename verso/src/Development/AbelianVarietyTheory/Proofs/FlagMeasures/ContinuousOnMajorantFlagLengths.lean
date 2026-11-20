import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.BlockAnti
import Formalism.FormalDegreeBessel.FinalG

noncomputable section

open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp Filter Topology
open scoped InnerProductSpace ENNReal

namespace GlobalTheory.Amp.LenCont

/- English proof (translation)
Rewrite using `[EuclideanSpace.norm_eq]`. Simplify using `[eucl, Complex.normSq_eq_norm_sq]`.
-/
theorem eucl_eq {n : ℕ} (v : Fin n → ℂ) : eucl v = ‖(WithLp.toLp 2 v : EuclideanSpace ℂ (Fin n))‖ := by
  rw [EuclideanSpace.norm_eq]
  simp [eucl, Complex.normSq_eq_norm_sq]

/- English proof (translation)
Rewrite using `[eucl_eq, eucl_eq, opn, ← Matrix.toEuclideanCLM_toLp]`. Conclude with `ContinuousLinearMap.le_opNorm _ _`.
-/
theorem eucl_mulVec_le {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) (v : Fin n → ℂ) :
    eucl (A *ᵥ v) ≤ opn A * eucl v := by
  rw [eucl_eq, eucl_eq, opn, ← Matrix.toEuclideanCLM_toLp]
  exact ContinuousLinearMap.le_opNorm _ _

/- English proof (translation)
Unfold `opn`. Use `continuous_norm.comp ?_` and prove the remaining obligations. Conclude with `LinearMap.continuous_of_finiteDimensional ((Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin n)).toAlgEquiv.toLinearMap)`.
-/
theorem opn_continuous {n : ℕ} : Continuous (opn (n := n)) := by
  unfold opn
  refine continuous_norm.comp ?_
  exact LinearMap.continuous_of_finiteDimensional
    ((Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin n)).toAlgEquiv.toLinearMap)

/- English proof (translation)
Rewrite using `[opn, map_one, norm_one]`.
-/
theorem opn_one {n : ℕ} : opn (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) = 1 := by
  rw [opn, map_one, norm_one]

def len {n : ℕ} (Y : Submodule ℂ (Fin n → ℂ)) (f : Fin n → ℂ) (g : Matrix (Fin n) (Fin n) ℂ) : ℝ :=
  sInf {t | ∃ y ∈ Y, t = eucl (g⁻¹ *ᵥ (f - y))}

/- English proof (translation)
Establish `hb : BddBelow {t | ∃ y ∈ Y, t = eucl (g⁻¹ *ᵥ (f - y))}` using `⟨0, by rintro t ⟨y, -, rfl⟩; exact Real.sqrt_nonneg _⟩`. Establish `hne : {t | ∃ y ∈ Y, t = eucl (h⁻¹ *ᵥ (f - y))}.Nonempty` using `⟨_, 0, Y.zero_mem, rfl⟩`. Establish `key : ∀ t ∈ {t | ∃ y ∈ Y, t = eucl (h⁻¹ *ᵥ (f - y))}, len Y f g ≤ opn (g⁻¹ * h) * t`. Introduce and unpack `t ⟨y, hy, rfl⟩`. Use `(csInf_le hb ⟨y, hy, rfl⟩).trans ?_` and prove the remaining obligations.

Use `eucl_mulVec_le (g⁻¹ * h) (h⁻¹ *ᵥ (f - y))` as an intermediate fact. Rewrite `this` using `[Matrix.mulVec_mulVec, Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hh, Matrix.mul_one]`. Then use the resulting hypothesis. Establish `h0 : 0 ≤ opn (g⁻¹ * h)` using `norm_nonneg _`. Break down `h0.eq_or_lt with h0 | h0` into its components or cases. Take `⟨t, ht⟩` from `hne`.

Use `key t ht` as an intermediate fact. Rewrite `this`, the goal using `[← h0]`. Simplify using `using this`. Rewrite using `[mul_comm, ← div_le_iff₀ h0]`. Use `le_csInf hne fun t ht => ?_` and prove the remaining obligations.

Rewrite using `[div_le_iff₀ h0, mul_comm]`. Conclude with `key t ht`.
-/
theorem len_le {n : ℕ} (Y : Submodule ℂ (Fin n → ℂ)) (f : Fin n → ℂ) (g h : Matrix (Fin n) (Fin n) ℂ)
    (hh : IsUnit h.det) : len Y f g ≤ opn (g⁻¹ * h) * len Y f h := by
  have hb : BddBelow {t | ∃ y ∈ Y, t = eucl (g⁻¹ *ᵥ (f - y))} :=
    ⟨0, by rintro t ⟨y, -, rfl⟩; exact Real.sqrt_nonneg _⟩
  have hne : {t | ∃ y ∈ Y, t = eucl (h⁻¹ *ᵥ (f - y))}.Nonempty := ⟨_, 0, Y.zero_mem, rfl⟩
  have key : ∀ t ∈ {t | ∃ y ∈ Y, t = eucl (h⁻¹ *ᵥ (f - y))}, len Y f g ≤ opn (g⁻¹ * h) * t := by
    rintro t ⟨y, hy, rfl⟩
    refine (csInf_le hb ⟨y, hy, rfl⟩).trans ?_
    have := eucl_mulVec_le (g⁻¹ * h) (h⁻¹ *ᵥ (f - y))
    rwa [Matrix.mulVec_mulVec, Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hh, Matrix.mul_one] at this
  have h0 : 0 ≤ opn (g⁻¹ * h) := norm_nonneg _
  rcases h0.eq_or_lt with h0 | h0
  · obtain ⟨t, ht⟩ := hne
    have := key t ht
    rw [← h0] at this ⊢
    simpa using this
  · rw [mul_comm, ← div_le_iff₀ h0]
    refine le_csInf hne fun t ht => ?_
    rw [div_le_iff₀ h0, mul_comm]
    exact key t ht

/- English proof (translation)
Introduce `x₀ hx₀`. Establish `hx₀' : IsUnit x₀.det` using `hx₀`. Establish `hinv : ContinuousAt (Inv.inv : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ → _) x₀`. Use `continuousAt_matrix_inv x₀ ?_` and prove the remaining obligations. Take `⟨u, hu⟩` from `hx₀'`.

Rewrite using `[← hu]`. Conclude with `NormedRing.inverse_continuousAt u`. Establish `h1 : Tendsto (fun x => opn (x⁻¹ * x₀)) (𝓝 x₀) (𝓝 1)`. Establish `: ContinuousAt (fun x : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ => opn (x⁻¹ * x₀)) x₀` using `opn_continuous.continuousAt.comp (hinv.mul continuousAt_const)`. Simplify `this` using `[ContinuousAt, Matrix.nonsing_inv_mul _ hx₀', opn_one]`.

Establish `h2 : Tendsto (fun x => opn (x₀⁻¹ * x)) (𝓝 x₀) (𝓝 1)`. Establish `: ContinuousAt (fun x : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ => opn (x₀⁻¹ * x)) x₀` using `opn_continuous.continuousAt.comp (continuousAt_const.mul continuousAt_id)`. Simplify `this` using `[ContinuousAt, Matrix.nonsing_inv_mul _ hx₀', opn_one]`. Establish `hU : Tendsto (fun x => opn (x⁻¹ * x₀) * len Y f x₀) (𝓝 x₀) (𝓝 (len Y f x₀))`. Simplify using `using h1.mul_const (len Y f x₀)`.

Establish `hL : Tendsto (fun x => len Y f x₀ / opn (x₀⁻¹ * x)) (𝓝 x₀) (𝓝 (len Y f x₀))`. Use `(tendsto_const_nhds (x := len Y f x₀)).div h2 one_ne_zero` as an intermediate fact. Rewrite `this` using `[div_one]`. Conclude with `this`. Use `tendsto_of_tendsto_of_tendsto_of_le_of_le' (hL.mono_left nhdsWithin_le_nhds) (hU.mono_left nhdsWithin_le_nhds) ?_ (Eventually.of_forall fun x => len_le Y f x x₀ hx₀')` and prove the remaining obligations.

Use `filter_upwards [self_mem_nhdsWithin, (h2.eventually (lt_mem_nhds zero_lt_one)).filter_mono nhdsWithin_le_nhds] with x hx hpos`. Rewrite using `[div_le_iff₀ hpos, mul_comm]`. Conclude with `len_le Y f x₀ x hx`.
-/
theorem len_continuousOn {n : ℕ} (Y : Submodule ℂ (Fin (n + 1) → ℂ)) (f : Fin (n + 1) → ℂ) :
    ContinuousOn (len Y f) {g | IsUnit g.det} := by
  intro x₀ hx₀
  have hx₀' : IsUnit x₀.det := hx₀
  have hinv : ContinuousAt (Inv.inv : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ → _) x₀ := by
    refine continuousAt_matrix_inv x₀ ?_
    obtain ⟨u, hu⟩ := hx₀'
    rw [← hu]
    exact NormedRing.inverse_continuousAt u
  have h1 : Tendsto (fun x => opn (x⁻¹ * x₀)) (𝓝 x₀) (𝓝 1) := by
    have : ContinuousAt (fun x : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ => opn (x⁻¹ * x₀)) x₀ :=
      opn_continuous.continuousAt.comp (hinv.mul continuousAt_const)
    simpa [ContinuousAt, Matrix.nonsing_inv_mul _ hx₀', opn_one] using this
  have h2 : Tendsto (fun x => opn (x₀⁻¹ * x)) (𝓝 x₀) (𝓝 1) := by
    have : ContinuousAt (fun x : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ => opn (x₀⁻¹ * x)) x₀ :=
      opn_continuous.continuousAt.comp (continuousAt_const.mul continuousAt_id)
    simpa [ContinuousAt, Matrix.nonsing_inv_mul _ hx₀', opn_one] using this
  have hU : Tendsto (fun x => opn (x⁻¹ * x₀) * len Y f x₀) (𝓝 x₀) (𝓝 (len Y f x₀)) := by
    simpa using h1.mul_const (len Y f x₀)
  have hL : Tendsto (fun x => len Y f x₀ / opn (x₀⁻¹ * x)) (𝓝 x₀) (𝓝 (len Y f x₀)) := by
    have := (tendsto_const_nhds (x := len Y f x₀)).div h2 one_ne_zero
    rw [div_one] at this
    exact this
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' (hL.mono_left nhdsWithin_le_nhds)
    (hU.mono_left nhdsWithin_le_nhds) ?_ (Eventually.of_forall fun x => len_le Y f x x₀ hx₀')
  filter_upwards [self_mem_nhdsWithin, (h2.eventually (lt_mem_nhds zero_lt_one)).filter_mono nhdsWithin_le_nhds]
    with x hx hpos
  rw [div_le_iff₀ hpos, mul_comm]
  exact len_le Y f x₀ x hx

/- English proof (translation)
Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty => simpa using continuousOn_const`. Consider the case `insert a s ha ih`. Simplify using `only [Finset.fold_insert ha]`. Conclude with `continuous_max.comp_continuousOn ((hF a).prodMk ih)`.
-/
theorem fold_continuousOn {X ι : Type*} [TopologicalSpace X] [DecidableEq ι] (S : Set X) (F : ι → X → ℝ)
    (hF : ∀ a, ContinuousOn (F a) S) (s : Finset ι) :
    ContinuousOn (fun x => s.fold max 1 fun a => F a x) S := by
  induction s using Finset.induction_on with
  | empty => simpa using continuousOn_const
  | insert a s ha ih =>
    simp only [Finset.fold_insert ha]
    exact continuous_max.comp_continuousOn ((hF a).prodMk ih)

/- English proof (translation)
Introduce `k r z`. Establish `hH : IsUnit (Hpk k r).det` using `Matrix.isUnit_det_of_left_inverse (hpkFacts k r).2.1`. Establish `h : ∀ a, ContinuousOn (fun x => lA k r z x a) (GG k r)` using `fun a => (len_continuousOn _ (fvec k r z a)).mono fun g hg => ((uHGroup _ _ hH).2.2 g hg).1`. Conclude with `⟨h, fold_continuousOn (GG k r) (fun a x => lA k r z x a) h Finset.univ⟩`.
-/
theorem lA_Sg_continuousOn : ∀ (k r : ℕ) (z : (Fin (2 * r + k + 1) → ℂ)),
    (∀ a, ContinuousOn (fun x => lA k r z x a) (GG k r)) ∧ ContinuousOn (Sg k r z) (GG k r) := by
  intro k r z
  have hH : IsUnit (Hpk k r).det := Matrix.isUnit_det_of_left_inverse (hpkFacts k r).2.1
  have h : ∀ a, ContinuousOn (fun x => lA k r z x a) (GG k r) := fun a =>
    (len_continuousOn _ (fvec k r z a)).mono fun g hg => ((uHGroup _ _ hH).2.2 g hg).1
  exact ⟨h, fold_continuousOn (GG k r) (fun a x => lA k r z x a) h Finset.univ⟩

end GlobalTheory.Amp.LenCont

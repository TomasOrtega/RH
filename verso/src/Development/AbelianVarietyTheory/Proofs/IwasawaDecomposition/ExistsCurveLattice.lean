import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsIntegralHalf
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.LatticeInvariantsPeriodPairDictionary

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Ker GlobalTheory.Mem GlobalTheory.Mem.Col2 Matrix
open scoped BigOperators

noncomputable section

namespace GlobalTheory.Mem.Col2.CurveLat

/- English proof (translation)
Set `b : Module.Basis (Fin 2) ℤ (𝓞 K)` to `Module.finBasisOfFinrankEq ℤ _ ((RingOfIntegers.rank K).trans hK)`. Establish `hs : ∀ x : 𝓞 K, σ x = b.repr x 0 * σ (b 0) + b.repr x 1 * σ (b 1)`. Introduce `x`. Use `congrArg σ (b.sum_repr x)` as an intermediate fact. Rewrite `this` using `[Fin.sum_univ_two]`.

Simplify using `using this.symm`. Establish `hb0 : σ (b 0) ≠ 0` using `(map_ne_zero_iff σ hσ).2 (b.ne_zero 0)`. Establish `h0 : (σ (b 1) * starRingEnd ℂ (σ (b 0))).im ≠ 0`. Introduce `h0`. Establish `e` using `hs (a * b 0)`.

Establish `e'` using `congrArg (fun z => (z * starRingEnd ℂ (σ (b 0))).im) e`. Simplify using `only [map_mul] at e'`. Rewrite `e'` using `[add_mul, _root_.mul_assoc, _root_.mul_assoc, _root_.mul_assoc, Complex.mul_conj, Complex.add_im, Complex.mul_im, Complex.mul_im, Complex.mul_im, h0]`. Simplify using `[ha, hb0] at e'`. Use `⟨⟨δ * σ (b 0), δ * σ (b 1), ?_⟩, fun z => ?_⟩` and prove the remaining obligations.

Rewrite using `[LinearIndependent.pair_iff]`. Introduce `x y e0`. Establish `e : (x : ℂ) * σ (b 0) + (y : ℂ) * σ (b 1) = 0`. Apply `mul_left_cancel₀ hδ` to reduce the goal to its premises. Simplify using `only [Complex.real_smul] at e0`.

Take the linear combination `e0`. Establish `e1` using `congrArg Complex.re e`. Establish `e2` using `congrArg Complex.im e`. Simplify using `at e1 e2 h0`. Prove the components needed by the constructor for the conclusion.

Use `mul_right_cancel₀ h0 ?_` and prove the remaining obligations. Take the linear combination `(σ (b 1)).im * e1 - (σ (b 1)).re * e2`. Use `mul_right_cancel₀ h0 ?_` and prove the remaining obligations. Take the linear combination `(σ (b 0)).re * e2 - (σ (b 0)).im * e1`. Rewrite using `[PeriodPair.mem_lattice]`.

Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨m, n, rfl⟩`. Conclude with `⟨m • b 0 + n • b 1, by simp; ring⟩`. Introduce and unpack `⟨x, rfl⟩`. Conclude with `⟨b.repr x 0, b.repr x 1, by rw [hs x]; ring⟩`.
-/
theorem exists_periodPair_mul_image {K : Type} [Field K] [NumberField K] (hK : Module.finrank ℚ K = 2)
    (σ : 𝓞 K →+* ℂ) (hσ : Function.Injective σ) (a : 𝓞 K) (ha : (σ a).im ≠ 0) (δ : ℂ) (hδ : δ ≠ 0) :
    ∃ L : PeriodPair, ∀ z, z ∈ L.lattice ↔ ∃ c : 𝓞 K, z = δ * σ c := by
  let b : Module.Basis (Fin 2) ℤ (𝓞 K) := Module.finBasisOfFinrankEq ℤ _ ((RingOfIntegers.rank K).trans hK)
  have hs : ∀ x : 𝓞 K, σ x = b.repr x 0 * σ (b 0) + b.repr x 1 * σ (b 1) := by
    intro x
    have := congrArg σ (b.sum_repr x)
    rw [Fin.sum_univ_two] at this
    simpa using this.symm
  have hb0 : σ (b 0) ≠ 0 := (map_ne_zero_iff σ hσ).2 (b.ne_zero 0)
  have h0 : (σ (b 1) * starRingEnd ℂ (σ (b 0))).im ≠ 0 := by
    intro h0
    have e := hs (a * b 0)
    have e' := congrArg (fun z => (z * starRingEnd ℂ (σ (b 0))).im) e
    simp only [map_mul] at e'
    rw [add_mul, _root_.mul_assoc, _root_.mul_assoc, _root_.mul_assoc, Complex.mul_conj, Complex.add_im,
      Complex.mul_im, Complex.mul_im, Complex.mul_im, h0] at e'
    simp [ha, hb0] at e'
  refine ⟨⟨δ * σ (b 0), δ * σ (b 1), ?_⟩, fun z => ?_⟩
  · rw [LinearIndependent.pair_iff]
    intro x y e0
    have e : (x : ℂ) * σ (b 0) + (y : ℂ) * σ (b 1) = 0 := by
      apply mul_left_cancel₀ hδ
      simp only [Complex.real_smul] at e0
      linear_combination e0
    have e1 := congrArg Complex.re e
    have e2 := congrArg Complex.im e
    simp at e1 e2 h0
    constructor
    · refine mul_right_cancel₀ h0 ?_
      linear_combination (σ (b 1)).im * e1 - (σ (b 1)).re * e2
    · refine mul_right_cancel₀ h0 ?_
      linear_combination (σ (b 0)).re * e2 - (σ (b 0)).im * e1
  · rw [PeriodPair.mem_lattice]
    constructor
    · rintro ⟨m, n, rfl⟩
      exact ⟨m • b 0 + n • b 1, by simp; ring⟩
    · rintro ⟨x, rfl⟩
      exact ⟨b.repr x 0, b.repr x 1, by rw [hs x]; ring⟩

/- English proof (translation)
Introduce `h`. Establish `h1 : IsIntegral ℤ (1 / 2 : ℚ)`. Use `(isIntegral_algHom_iff (algebraMap ℚ ℂ).toIntAlgHom (algebraMap ℚ ℂ).injective).1 ?_` and prove the remaining obligations. Simplify using `using h`. Take `⟨y, hy⟩` from `IsIntegrallyClosed.algebraMap_eq_of_integral h1`.

Establish `h2 : (2 * y : ℚ) = 1`. Simplify using `only [eq_intCast] at hy`. Rewrite using `[hy]`. Evaluate the numerical expressions. Establish `h3 : 2 * y = 1` using `by exact_mod_cast h2`.

Use linear arithmetic over natural numbers and integers.
-/
theorem not_isIntegral_half : ¬ IsIntegral ℤ (1 / 2 : ℂ) := by
  intro h
  have h1 : IsIntegral ℤ (1 / 2 : ℚ) := by
    refine (isIntegral_algHom_iff (algebraMap ℚ ℂ).toIntAlgHom (algebraMap ℚ ℂ).injective).1 ?_
    simpa using h
  obtain ⟨y, hy⟩ := IsIntegrallyClosed.algebraMap_eq_of_integral h1
  have h2 : (2 * y : ℚ) = 1 := by
    simp only [eq_intCast] at hy
    rw [hy]; norm_num
  have h3 : 2 * y = 1 := by exact_mod_cast h2
  omega

/- English proof (translation)
Introduce `h`. Establish `h1 : IsIntegral ℤ (starRingEnd ℂ z)` using `h.map (starRingEnd ℂ).toIntAlgHom`. Establish `h2` using `h.add h1`. Rewrite `h2` using `[Complex.add_conj, hz]`. Apply `not_isIntegral_half` to reduce the goal to its premises.

Establish `e : ((2 * (1 / 4) : ℝ) : ℂ) = 1 / 2`. Use `push_cast`. Evaluate the numerical expressions. Rewrite `h2` using `[e]`. Then use the resulting hypothesis.
-/
theorem not_isIntegral_of_re {z : ℂ} (hz : z.re = 1 / 4) : ¬ IsIntegral ℤ z := by
  intro h
  have h1 : IsIntegral ℤ (starRingEnd ℂ z) := h.map (starRingEnd ℂ).toIntAlgHom
  have h2 := h.add h1
  rw [Complex.add_conj, hz] at h2
  apply not_isIntegral_half
  have e : ((2 * (1 / 4) : ℝ) : ℂ) = 1 / 2 := by
    push_cast
    norm_num
  rwa [e] at h2

variable {R : Ranks} (H : Host R)

def embO : 𝓞 H.K →+* ℂ := (H.φ₀.comp H.K.val.toRingHom).comp (algebraMap (𝓞 H.K) H.K)

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `hz`. Proceed by induction on `hz using AddSubgroup.closure_induction with`. Consider the case `mem x hx`. Take `⟨c, -, rfl⟩` from `hx`.

Conclude with `⟨c, rfl⟩`. Consider the case `zero => exact ⟨0, by simp⟩`. Consider the case `add x y _ _ hx hy`. Take `⟨c, rfl⟩` from `hx`. Take `⟨c', rfl⟩` from `hy`.

Conclude with `⟨c + c', by rw [map_add, mul_add]⟩`. Consider the case `neg x _ hx`. Take `⟨c, rfl⟩` from `hx`. Conclude with `⟨-c, by rw [map_neg, mul_neg]⟩`. Introduce and unpack `⟨c, rfl⟩`.

Conclude with `AddSubgroup.subset_closure ⟨c, Submodule.mem_top, rfl⟩`.
-/
theorem mem_lamOf_top (δ z : ℂ) : z ∈ Th.lamOf H ⊤ δ ↔ ∃ c : 𝓞 H.K, z = δ * embO H c := by
  constructor
  · intro hz
    induction hz using AddSubgroup.closure_induction with
    | mem x hx =>
      obtain ⟨c, -, rfl⟩ := hx
      exact ⟨c, rfl⟩
    | zero => exact ⟨0, by simp⟩
    | add x y _ _ hx hy =>
      obtain ⟨c, rfl⟩ := hx
      obtain ⟨c', rfl⟩ := hy
      exact ⟨c + c', by rw [map_add, mul_add]⟩
    | neg x _ hx =>
      obtain ⟨c, rfl⟩ := hx
      exact ⟨-c, by rw [map_neg, mul_neg]⟩
  · rintro ⟨c, rfl⟩
    exact AddSubgroup.subset_closure ⟨c, Submodule.mem_top, rfl⟩

/- English proof (translation)
Establish `hK : Module.finrank ℚ H.K = 2` using `Formalism.FrobeniusOrbits.SplitK.finrank_K H.hyp.2.1.pos H.sqrtMinusD_sq`. Establish `hinj : Function.Injective (embO H)` using `(H.φ₀.comp H.K.val.toRingHom).injective.comp RingOfIntegers.coe_injective`. Establish `ha : (embO H ⟨_, HostK.isIntegral_half H⟩).im ≠ 0`. Establish `e : embO H ⟨_, HostK.isIntegral_half H⟩ = (1 + Complex.I * (Real.sqrt H.d : ℂ)) / 2`. Rewrite using `[← HostK.φ₀_sqrt]`.

Express the relevant statement in the definitionally equal form `(H.φ₀.comp H.K.val.toRingHom) ((1 + (⟨H.sqrtMinusD, HostK.sqrt_mem H⟩ : H.K)) / 2) = _`. Rewrite using `[map_div₀, map_add, map_one, map_ofNat]`. Both sides reduce to the same expression. Establish `hd : (0 : ℝ) < Real.sqrt H.d` using `Real.sqrt_pos.2 (by exact_mod_cast H.hyp.2.1.pos)`. Rewrite using `[e]`.

Simplify using `[hd.ne']`. Take `⟨L, hL⟩` from `exists_periodPair_mul_image hK (embO H) hinj _ ha δ hδ`. Conclude with `⟨L, fun z => by rw [mem_lamOf_top, hL]⟩`.
-/
theorem exists_periodPair_lamOf (δ : ℂ) (hδ : δ ≠ 0) :
    ∃ L : PeriodPair, ∀ z, z ∈ Th.lamOf H ⊤ δ ↔ z ∈ L.lattice := by
  have hK : Module.finrank ℚ H.K = 2 := Formalism.FrobeniusOrbits.SplitK.finrank_K H.hyp.2.1.pos H.sqrtMinusD_sq
  have hinj : Function.Injective (embO H) :=
    (H.φ₀.comp H.K.val.toRingHom).injective.comp RingOfIntegers.coe_injective
  have ha : (embO H ⟨_, HostK.isIntegral_half H⟩).im ≠ 0 := by
    have e : embO H ⟨_, HostK.isIntegral_half H⟩ = (1 + Complex.I * (Real.sqrt H.d : ℂ)) / 2 := by
      rw [← HostK.φ₀_sqrt]
      change (H.φ₀.comp H.K.val.toRingHom) ((1 + (⟨H.sqrtMinusD, HostK.sqrt_mem H⟩ : H.K)) / 2) = _
      rw [map_div₀, map_add, map_one, map_ofNat]
      rfl
    have hd : (0 : ℝ) < Real.sqrt H.d := Real.sqrt_pos.2 (by exact_mod_cast H.hyp.2.1.pos)
    rw [e]
    simp [hd.ne']
  obtain ⟨L, hL⟩ := exists_periodPair_mul_image hK (embO H) hinj _ ha δ hδ
  exact ⟨L, fun z => by rw [mem_lamOf_top, hL]⟩

/- English proof (translation)
Rewrite using `[mem_lamOf_top]`. Introduce and unpack `⟨c, hc⟩`. Apply `not_isIntegral_of_re hz` to reduce the goal to its premises. Rewrite using `[mul_left_cancel₀ hδ hc]`. Conclude with `(Algebra.IsIntegral.isIntegral (R := ℤ) c).map (embO H).toIntAlgHom`.
-/
theorem not_mem_lamOf (δ : ℂ) (hδ : δ ≠ 0) {z : ℂ} (hz : z.re = 1 / 4) : δ * z ∉ Th.lamOf H ⊤ δ := by
  rw [mem_lamOf_top]
  rintro ⟨c, hc⟩
  apply not_isIntegral_of_re hz
  rw [mul_left_cancel₀ hδ hc]
  exact (Algebra.IsIntegral.isIntegral (R := ℤ) c).map (embO H).toIntAlgHom

end GlobalTheory.Mem.Col2.CurveLat

namespace GlobalTheory.Mem.Col2

open CurveLat

/- English proof (translation)
Introduce `R H`. Take `⟨L₁, h₁⟩` from `exists_periodPair_lamOf H 1 one_ne_zero`. Establish `hΔ` using `(GlobalTheory.LatticeInvariants.invariants_dictionary L₁ _ h₁).2.2.1`. Take `⟨δ, hδ⟩` from `IsAlgClosed.exists_pow_nat_eq (TaylorLogMetric.discr (Th.lamOf H ⊤ 1)) (n := 12) (by norm_num)`. Establish `hδ0 : δ ≠ 0`.

Introduce and unpack `rfl`. Conclude with `hΔ (by rw [← hδ]; norm_num)`. Take `⟨L, hL⟩` from `exists_periodPair_lamOf H δ hδ0`. Use `⟨δ, L, δ, hδ, AddSubgroup.ext fun z => (hL z).symm, ?_, ?_, ?_⟩` and prove the remaining obligations. Conclude with `(mem_lamOf_top H δ _).2 ⟨1, by rw [map_one]; ring⟩`.

Use `not_mem_lamOf H δ hδ0 (z := (1 + Complex.I * (Real.sqrt H.d : ℂ)) / 4) (by simp)` as an intermediate fact. Use `this using 2` and compare the differences between its conclusion and the goal. Expand and normalize the polynomial expressions, which then agree. Use `not_mem_lamOf H δ hδ0 (z := (1 - Complex.I * (Real.sqrt H.d : ℂ)) / 4) (by simp)` as an intermediate fact. Use `this using 2` and compare the differences between its conclusion and the goal.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem exists_curve_lattice : ∀ (R : Ranks) (H : Host R), ∃ (δ : ℂ) (L : PeriodPair) (ω₀ : ℂ), Th.IsDiscriminantTwelfthRootOfIdealLattice H ⊤ δ ∧ L.lattice.toAddSubgroup = Th.lamOf H ⊤ δ ∧ Th.IsTwoTorsionPointUnkilled H (Th.lamOf H ⊤ δ) (ω₀ / 2) := by
  intro R H
  obtain ⟨L₁, h₁⟩ := exists_periodPair_lamOf H 1 one_ne_zero
  have hΔ := (GlobalTheory.LatticeInvariants.invariants_dictionary L₁ _ h₁).2.2.1
  obtain ⟨δ, hδ⟩ := IsAlgClosed.exists_pow_nat_eq (TaylorLogMetric.discr (Th.lamOf H ⊤ 1)) (n := 12) (by norm_num)
  have hδ0 : δ ≠ 0 := by
    rintro rfl
    exact hΔ (by rw [← hδ]; norm_num)
  obtain ⟨L, hL⟩ := exists_periodPair_lamOf H δ hδ0
  refine ⟨δ, L, δ, hδ, AddSubgroup.ext fun z => (hL z).symm, ?_, ?_, ?_⟩
  · exact (mem_lamOf_top H δ _).2 ⟨1, by rw [map_one]; ring⟩
  · have := not_mem_lamOf H δ hδ0 (z := (1 + Complex.I * (Real.sqrt H.d : ℂ)) / 4) (by simp)
    convert this using 2
    ring
  · have := not_mem_lamOf H δ hδ0 (z := (1 - Complex.I * (Real.sqrt H.d : ℂ)) / 4) (by simp)
    convert this using 2
    ring

end GlobalTheory.Mem.Col2

end

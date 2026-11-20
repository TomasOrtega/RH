import Development.AutomorphicArithmetic.Foundations.Convolution.TwistedLocalOrbits.HoweSpace

open GlobalTheory.PRep MeasureTheory

namespace UpperTheory.ConvolutionTheory.Loc

variable {G V : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [AddCommGroup V] [Module ℂ V]

/- English proof (translation)
Establish `h : IsLocallyConstant fun g : G => ρ g w`. Rewrite using `[IsLocallyConstant.iff_exists_open]`. Introduce `x`. Use `⟨(fun g => x⁻¹ * g) ⁻¹' {g | ρ g w = w}, (hρ w).preimage (continuous_const.mul continuous_id), by simp, ?_⟩` and prove the remaining obligations. Introduce `y hy`.

Establish `hy' : ρ (x⁻¹ * y) w = w` using `hy`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[← Module.End.mul_apply, ← map_mul, mul_inv_cancel_left]`. Use `_ = ρ x w := by rw [hy']`. Conclude with `(h.comp l).continuous`.
-/
private theorem cont_coeff {ρ : Representation ℂ G V} (hρ : IsSmooth ρ) (l : V →ₗ[ℂ] ℂ) (w : V) :
    Continuous fun g : G => l (ρ g w) := by
  have h : IsLocallyConstant fun g : G => ρ g w := by
    rw [IsLocallyConstant.iff_exists_open]
    intro x
    refine ⟨(fun g => x⁻¹ * g) ⁻¹' {g | ρ g w = w}, (hρ w).preimage (continuous_const.mul continuous_id), by simp, ?_⟩
    intro y hy
    have hy' : ρ (x⁻¹ * y) w = w := hy
    calc ρ y w = ρ x (ρ (x⁻¹ * y) w) := by
          rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel_left]
      _ = ρ x w := by rw [hy']
  exact (h.comp l).continuous

open Classical in
/- English proof (translation)
Use `haveI : CompactSpace C := isCompact_iff_compactSpace.1 hC`. Use `letI : MeasurableSpace C := borel C`. Use `haveI : BorelSpace C := ⟨rfl⟩`. Set `μ : Measure C` to `Measure.haar`. Establish `hc : ∀ w, Continuous fun c : C => θ c * l (ρ (c : G)⁻¹ w)` using `fun w => (hθ.comp continuous_subtype_val).mul ((cont_coeff hρ l w).comp continuous_subtype_val.inv)`.

Establish `hi : ∀ w, Integrable (fun c : C => θ c * l (ρ (c : G)⁻¹ w)) μ` using `fun w => (hc w).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)`. Set `L : V →ₗ[ℂ] ℂ` to `{ toFun := fun w => ∫ c : C, θ c * l (ρ (c : G)⁻¹ w) ∂μ map_add' := fun a b => by`. Rewrite using `[← integral_add (hi a) (hi b)]`. Simplify using `only [map_add, mul_add]`. Use the proof step `map_smul' := fun t a => by`.

Simplify using `only [map_smul, smul_eq_mul, RingHom.id_apply]`. Rewrite using `[← integral_const_mul]`. Use `congr 1`. Use function extensionality and compare the values at `c`. Use `ring }`.

Establish `hL : ∀ c ∈ C, ∀ w, L (ρ c w) = θ c * L w`. Introduce `c hc w`. Express the relevant statement in the definitionally equal form `∫ x : C, θ x * l (ρ (x : G)⁻¹ (ρ c w)) ∂μ = θ c * ∫ x : C, θ x * l (ρ (x : G)⁻¹ w) ∂μ`. Rewrite using `[← integral_const_mul, ← integral_mul_left_eq_self _ (⟨c, hc⟩ : C)]`. Use `congr 1`.

Use function extensionality and compare the values at `x`. Simplify using `only [Subgroup.coe_mul]`. Rewrite using `[hmul c hc x x.2, ← Module.End.mul_apply, ← map_mul, mul_inv_rev, inv_mul_cancel_right, mul_assoc]`. Establish `hT : IsOpen ((Subtype.val : C → G) ⁻¹' S)` using `hS.preimage continuous_subtype_val`. Establish `hLv : L v = (μ.real ((Subtype.val : C → G) ⁻¹' S) : ℂ)`.

Express the relevant statement in the definitionally equal form `∫ x : C, θ x * l (ρ (x : G)⁻¹ v) ∂μ = _`. Establish `: (fun x : C => θ x * l (ρ (x : G)⁻¹ v)) = ((Subtype.val : C → G) ⁻¹' S).indicator fun _ => (1 : ℂ)`. Use function extensionality and compare the values at `x`. Rewrite using `[hv x x.2, Set.indicator_apply]`. Both sides reduce to the same expression.

Rewrite using `[this, integral_indicator_const _ hT.measurableSet]`. Simplify using the standard rewrite rules. Establish `hne : L v ≠ 0`. Rewrite using `[hLv, Complex.ofReal_ne_zero, measureReal_ne_zero_iff (measure_ne_top _ _)]`. Conclude with `hT.measure_ne_zero μ ⟨1, h1⟩`.

Use `⟨(L v)⁻¹ • L, fun c hc w => ?_, ?_⟩` and prove the remaining obligations. Simplify using `only [LinearMap.smul_apply, hL c hc, smul_eq_mul]`. Expand and normalize the polynomial expressions, which then agree. Simplify using `[hne]`.
-/
private theorem avg {ρ : Representation ℂ G V} (hρ : IsSmooth ρ) (C : Subgroup G) (hC : IsCompact (C : Set G))
    (θ : G → ℂ) (hθ : Continuous θ) (hmul : ∀ a ∈ C, ∀ b ∈ C, θ (a * b) = θ a * θ b) (l : V →ₗ[ℂ] ℂ) (v : V)
    (S : Set G) (hS : IsOpen S) (h1 : 1 ∈ S) (hv : ∀ c ∈ C, θ c * l (ρ c⁻¹ v) = if c ∈ S then 1 else 0) :
    ∃ l' : V →ₗ[ℂ] ℂ, (∀ c ∈ C, ∀ w, l' (ρ c w) = θ c * l' w) ∧ l' v = 1 := by
  haveI : CompactSpace C := isCompact_iff_compactSpace.1 hC
  letI : MeasurableSpace C := borel C
  haveI : BorelSpace C := ⟨rfl⟩
  let μ : Measure C := Measure.haar
  have hc : ∀ w, Continuous fun c : C => θ c * l (ρ (c : G)⁻¹ w) := fun w =>
    (hθ.comp continuous_subtype_val).mul ((cont_coeff hρ l w).comp continuous_subtype_val.inv)
  have hi : ∀ w, Integrable (fun c : C => θ c * l (ρ (c : G)⁻¹ w)) μ := fun w =>
    (hc w).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  let L : V →ₗ[ℂ] ℂ :=
    { toFun := fun w => ∫ c : C, θ c * l (ρ (c : G)⁻¹ w) ∂μ
      map_add' := fun a b => by
        rw [← integral_add (hi a) (hi b)]
        simp only [map_add, mul_add]
      map_smul' := fun t a => by
        simp only [map_smul, smul_eq_mul, RingHom.id_apply]
        rw [← integral_const_mul]
        congr 1
        funext c
        ring }
  have hL : ∀ c ∈ C, ∀ w, L (ρ c w) = θ c * L w := by
    intro c hc w
    change ∫ x : C, θ x * l (ρ (x : G)⁻¹ (ρ c w)) ∂μ = θ c * ∫ x : C, θ x * l (ρ (x : G)⁻¹ w) ∂μ
    rw [← integral_const_mul, ← integral_mul_left_eq_self _ (⟨c, hc⟩ : C)]
    congr 1
    funext x
    simp only [Subgroup.coe_mul]
    rw [hmul c hc x x.2, ← Module.End.mul_apply, ← map_mul, mul_inv_rev, inv_mul_cancel_right, mul_assoc]
  have hT : IsOpen ((Subtype.val : C → G) ⁻¹' S) := hS.preimage continuous_subtype_val
  have hLv : L v = (μ.real ((Subtype.val : C → G) ⁻¹' S) : ℂ) := by
    change ∫ x : C, θ x * l (ρ (x : G)⁻¹ v) ∂μ = _
    have : (fun x : C => θ x * l (ρ (x : G)⁻¹ v)) = ((Subtype.val : C → G) ⁻¹' S).indicator fun _ => (1 : ℂ) := by
      funext x
      rw [hv x x.2, Set.indicator_apply]
      rfl
    rw [this, integral_indicator_const _ hT.measurableSet]
    simp
  have hne : L v ≠ 0 := by
    rw [hLv, Complex.ofReal_ne_zero, measureReal_ne_zero_iff (measure_ne_top _ _)]
    exact hT.measure_ne_zero μ ⟨1, h1⟩
  refine ⟨(L v)⁻¹ • L, fun c hc w => ?_, ?_⟩
  · simp only [LinearMap.smul_apply, hL c hc, smul_eq_mul]
    ring
  · simp [hne]

/- English proof (translation)
Assume the negation of the conclusion as `h0`. Take `⟨l₀, hl₀⟩` from `Module.Projective.exists_dual_eq_one ℂ h0`. Establish `hK1 : ∀ k ∈ K, χ k = l₀ (ρ k v)` using `fun k hk => by rw [hv k hk, map_smul, hl₀, smul_eq_mul, mul_one]`. Establish `hKmul : ∀ a ∈ K, ∀ b ∈ K, χ (a * b) = χ a * χ b` using `fun a ha b hb => by`. Rewrite using `[hK1 _ (K.mul_mem ha hb), map_mul, Module.End.mul_apply, hv b hb, map_smul, map_smul, ← hK1 a ha, smul_eq_mul, mul_comm]`.

Establish `hinv : ∀ a ∈ K, χ a * χ a⁻¹ = 1` using `fun a ha => by`. Rewrite using `[← hKmul a ha _ (K.inv_mem ha), mul_inv_cancel, hK1 1 K.one_mem, map_one, Module.End.one_apply, hl₀]`. Take `⟨l₁, hl₁, hl₁v⟩` from `avg hρ K hK χ hχ hKmul l₀ v Set.univ isOpen_univ trivial (fun c hc => by`. Rewrite using `[← hK1 _ (K.inv_mem hc), hinv c hc]`. Use the proof step `simp)`.

Establish `hF : ∃ F : Finset G, (∀ u ∈ F, u ∈ N) ∧ ∀ l' : V →ₗ[ℂ] ℂ, (∀ c ∈ F, ∀ w, l' (ρ c w) = χ c * l' w) → l' v = 0` using `by clear hl₁v hv hK1 hl₀ h0`. Proceed by induction on `hker using Submodule.span_induction with`. Consider the case `mem w hw`. Take `⟨u, hu, x, rfl⟩` from `hw`. Conclude with `⟨{u}, by simpa using hu, fun l' h => by simp [h u (by simp)]⟩`.

Consider the case `zero => exact ⟨∅, by simp, by simp⟩`. Consider the case `add a b _ _ ha hb`. Take `⟨F, hF, h⟩` from `ha`. Take `⟨F', hF', h'⟩` from `hb`. Use `⟨F ∪ F', fun u hu => (Finset.mem_union.1 hu).elim (hF u) (hF' u), fun l' hl => ?_⟩` and prove the remaining obligations.

Rewrite using `[map_add, h l' fun c hc => hl c (Finset.mem_union_left _ hc), h' l' fun c hc => hl c (Finset.mem_union_right _ hc), add_zero]`. Consider the case `smul t a _ ha`. Take `⟨F, hF, h⟩` from `ha`. Conclude with `⟨F, hF, fun l' hl => by rw [map_smul, h l' hl, smul_zero]⟩`. Take `⟨F, hFN, hF⟩` from `hF`.

Take `⟨C, hC, hCN, hFC⟩` from `hN F hFN`. Take `⟨l₂, hl₂, hl₂v⟩` from `avg hρ C hC χ hχ (fun a ha b hb => hmul a (hCN ha) b (hCN hb)) l₁ v K hK' K.one_mem (fun c hc => by`. Distinguish the cases in `hcK : c ∈ K`. Rewrite using `[if_pos (by exact hcK), hv _ (K.inv_mem hcK), map_smul, hl₁v, smul_eq_mul, mul_one, hinv c hcK]`. Rewrite using `[if_neg (by exact hcK)]`.

Take `⟨k, hk, hk', hne⟩` from `hint c⁻¹ (N.inv_mem (hCN hc)) (fun h => hcK (by simpa using K.inv_mem h))`. Establish `h1` using `hl₁ _ hk' (ρ c⁻¹ v)`. Rewrite `h1` using `[← Module.End.mul_apply, ← map_mul, inv_mul_cancel_right, map_mul, Module.End.mul_apply, hv k hk, map_smul, map_smul, smul_eq_mul]`. Rewrite using `[(mul_eq_mul_right_iff.1 h1).resolve_left hne.symm, mul_zero])`. Conclude with `one_ne_zero (hl₂v.symm.trans (hF l₂ fun c hc => hl₂ c (hFC c hc)))`.
-/
theorem eq_zero_of_no_intertwining {ρ : Representation ℂ G V} (hρ : IsSmooth ρ) (K N : Subgroup G)
    (hK : IsCompact (K : Set G)) (hK' : IsOpen (K : Set G))
    (hN : ∀ F : Finset G, (∀ u ∈ F, u ∈ N) → ∃ C : Subgroup G, IsCompact (C : Set G) ∧ C ≤ N ∧ ∀ u ∈ F, u ∈ C)
    (χ : G → ℂ) (hχ : Continuous χ) (hmul : ∀ a ∈ N, ∀ b ∈ N, χ (a * b) = χ a * χ b)
    (hint : ∀ u ∈ N, u ∉ K → ∃ k ∈ K, u * k * u⁻¹ ∈ K ∧ χ (u * k * u⁻¹) ≠ χ k)
    (v : V) (hv : ∀ k ∈ K, ρ k v = χ k • v)
    (hker : v ∈ Submodule.span ℂ {w | ∃ u ∈ N, ∃ x, w = ρ u x - χ u • x}) : v = 0 := by
  classical
  by_contra h0
  obtain ⟨l₀, hl₀⟩ := Module.Projective.exists_dual_eq_one ℂ h0
  have hK1 : ∀ k ∈ K, χ k = l₀ (ρ k v) := fun k hk => by rw [hv k hk, map_smul, hl₀, smul_eq_mul, mul_one]
  have hKmul : ∀ a ∈ K, ∀ b ∈ K, χ (a * b) = χ a * χ b := fun a ha b hb => by
    rw [hK1 _ (K.mul_mem ha hb), map_mul, Module.End.mul_apply, hv b hb, map_smul, map_smul, ← hK1 a ha, smul_eq_mul,
      mul_comm]
  have hinv : ∀ a ∈ K, χ a * χ a⁻¹ = 1 := fun a ha => by
    rw [← hKmul a ha _ (K.inv_mem ha), mul_inv_cancel, hK1 1 K.one_mem, map_one, Module.End.one_apply, hl₀]
  obtain ⟨l₁, hl₁, hl₁v⟩ := avg hρ K hK χ hχ hKmul l₀ v Set.univ isOpen_univ trivial (fun c hc => by
    rw [← hK1 _ (K.inv_mem hc), hinv c hc]; simp)
  have hF : ∃ F : Finset G, (∀ u ∈ F, u ∈ N) ∧
      ∀ l' : V →ₗ[ℂ] ℂ, (∀ c ∈ F, ∀ w, l' (ρ c w) = χ c * l' w) → l' v = 0 := by
    clear hl₁v hv hK1 hl₀ h0
    induction hker using Submodule.span_induction with
    | mem w hw =>
      obtain ⟨u, hu, x, rfl⟩ := hw
      exact ⟨{u}, by simpa using hu, fun l' h => by simp [h u (by simp)]⟩
    | zero => exact ⟨∅, by simp, by simp⟩
    | add a b _ _ ha hb =>
      obtain ⟨F, hF, h⟩ := ha
      obtain ⟨F', hF', h'⟩ := hb
      refine ⟨F ∪ F', fun u hu => (Finset.mem_union.1 hu).elim (hF u) (hF' u), fun l' hl => ?_⟩
      rw [map_add, h l' fun c hc => hl c (Finset.mem_union_left _ hc), h' l' fun c hc => hl c (Finset.mem_union_right _ hc),
        add_zero]
    | smul t a _ ha =>
      obtain ⟨F, hF, h⟩ := ha
      exact ⟨F, hF, fun l' hl => by rw [map_smul, h l' hl, smul_zero]⟩
  obtain ⟨F, hFN, hF⟩ := hF
  obtain ⟨C, hC, hCN, hFC⟩ := hN F hFN
  obtain ⟨l₂, hl₂, hl₂v⟩ := avg hρ C hC χ hχ (fun a ha b hb => hmul a (hCN ha) b (hCN hb)) l₁ v K hK' K.one_mem
    (fun c hc => by
      by_cases hcK : c ∈ K
      · rw [if_pos (by exact hcK), hv _ (K.inv_mem hcK), map_smul, hl₁v, smul_eq_mul, mul_one, hinv c hcK]
      · rw [if_neg (by exact hcK)]
        obtain ⟨k, hk, hk', hne⟩ := hint c⁻¹ (N.inv_mem (hCN hc)) (fun h => hcK (by simpa using K.inv_mem h))
        have h1 := hl₁ _ hk' (ρ c⁻¹ v)
        rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel_right, map_mul, Module.End.mul_apply, hv k hk, map_smul,
          map_smul, smul_eq_mul] at h1
        rw [(mul_eq_mul_right_iff.1 h1).resolve_left hne.symm, mul_zero])
  exact one_ne_zero (hl₂v.symm.trans (hF l₂ fun c hc => hl₂ c (hFC c hc)))

end UpperTheory.ConvolutionTheory.Loc

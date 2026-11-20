import Mathlib
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.PAdicHodge

namespace SenTateChar

variable {p : ℕ} [hp : Fact p.Prime]
variable {G : Type*} [Group G] [TopologicalSpace G] [CompactSpace G]

/- English proof (translation)
Use `set f : G → ℝ := fun τ => ‖((η τ : ℚ_[p]ˣ) : ℚ_[p])‖ with hf`. Establish `hcont : Continuous f` using `(Units.continuous_val.comp hη).norm`. Take `⟨τ₀, -, hτ₀⟩` from `isCompact_univ.exists_isMaxOn Set.univ_nonempty hcont.continuousOn`. Establish `hbound : ∀ τ, f τ ≤ f τ₀` using `fun τ => hτ₀ (Set.mem_univ τ)`. Establish `hpow : ∀ τ : G, ∀ n : ℕ, f (τ ^ n) = f τ ^ n`.

Introduce `τ n`. Simplify using `only [hf, map_pow, Units.val_pow_eq_pow_val, norm_pow]`. Establish `hle : ∀ τ, f τ ≤ 1`. Introduce `τ`. Assume the negation of the conclusion as `hgt`.

Use `push Not at hgt`. Take `⟨n, hn⟩` from `(tendsto_pow_atTop_atTop_of_one_lt hgt).eventually_gt_atTop (f τ₀) |>.exists`. Use `hbound (τ ^ n)` as an intermediate fact. Rewrite `this` using `[hpow]`. Combine the linear equalities and inequalities to obtain the conclusion.

Establish `hmul : f σ * f σ⁻¹ = 1`. Simplify using `only [hf, map_inv, ← norm_mul, Units.val_inv_eq_inv_val]`. Rewrite using `[mul_inv_cancel₀ (Units.ne_zero _), norm_one]`. Establish `h0 : 0 ≤ f σ⁻¹` using `norm_nonneg _`. Apply `le_antisymm (hle σ)` to reduce the goal to its premises.

Assume the negation of the conclusion as `hlt`. Use `push Not at hlt`. Use `mul_lt_one_of_nonneg_of_lt_one_left (norm_nonneg _) hlt (hle σ⁻¹)` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem norm_eq_one_of_compactSpace (η : G →* ℚ_[p]ˣ) (hη : Continuous η) (σ : G) :
    ‖((η σ : ℚ_[p]ˣ) : ℚ_[p])‖ = 1 := by
  set f : G → ℝ := fun τ => ‖((η τ : ℚ_[p]ˣ) : ℚ_[p])‖ with hf
  have hcont : Continuous f := (Units.continuous_val.comp hη).norm
  obtain ⟨τ₀, -, hτ₀⟩ := isCompact_univ.exists_isMaxOn Set.univ_nonempty hcont.continuousOn
  have hbound : ∀ τ, f τ ≤ f τ₀ := fun τ => hτ₀ (Set.mem_univ τ)
  have hpow : ∀ τ : G, ∀ n : ℕ, f (τ ^ n) = f τ ^ n := by
    intro τ n
    simp only [hf, map_pow, Units.val_pow_eq_pow_val, norm_pow]
  have hle : ∀ τ, f τ ≤ 1 := by
    intro τ
    by_contra hgt
    push Not at hgt
    obtain ⟨n, hn⟩ := (tendsto_pow_atTop_atTop_of_one_lt hgt).eventually_gt_atTop (f τ₀) |>.exists
    have := hbound (τ ^ n)
    rw [hpow] at this
    linarith
  have hmul : f σ * f σ⁻¹ = 1 := by
    simp only [hf, map_inv, ← norm_mul, Units.val_inv_eq_inv_val]
    rw [mul_inv_cancel₀ (Units.ne_zero _), norm_one]
  have h0 : 0 ≤ f σ⁻¹ := norm_nonneg _
  apply le_antisymm (hle σ)
  by_contra hlt
  push Not at hlt
  have := mul_lt_one_of_nonneg_of_lt_one_left (norm_nonneg _) hlt (hle σ⁻¹)
  linarith

/- English proof (translation)
Establish `h1` using `norm_eq_one_of_compactSpace η hη`. Set `η' : G →* ℤ_[p]ˣ` to `{ toFun := fun σ => PadicInt.mkUnits (h1 σ) map_one' := by`. Apply `Units.ext` to reduce the goal to its premises. Apply `PadicInt.ext` to reduce the goal to its premises. Rewrite using `[PadicInt.mkUnits_eq, map_one]`.

Both sides reduce to the same expression. Use the proof step `map_mul' := fun σ τ => by`. Apply `Units.ext` to reduce the goal to its premises. Apply `PadicInt.ext` to reduce the goal to its premises. Rewrite using `[PadicInt.mkUnits_eq, Units.val_mul, PadicInt.coe_mul, PadicInt.mkUnits_eq, PadicInt.mkUnits_eq, map_mul, Units.val_mul] }`.

Use `⟨η', ?_, fun σ => PadicInt.mkUnits_eq (h1 σ)⟩` and prove the remaining obligations. Establish `hval : Continuous fun σ => ((η σ : ℚ_[p]ˣ) : ℚ_[p])` using `Units.continuous_val.comp hη`. Establish `hinv : Continuous fun σ => (((η σ)⁻¹ : ℚ_[p]ˣ) : ℚ_[p])` using `Units.continuous_val.comp (continuous_inv.comp hη)`. Rewrite using `[Units.continuous_iff]`. Prove the components needed by the constructor for the conclusion.

Express the relevant statement in the definitionally equal form `Continuous fun σ => (⟨((η σ : ℚ_[p]ˣ) : ℚ_[p]), (h1 σ).le⟩ : ℤ_[p])`. Conclude with `hval.subtype_mk _`. Establish `hn : ∀ σ, ‖(((η σ)⁻¹ : ℚ_[p]ˣ) : ℚ_[p])‖ ≤ 1` using `fun σ => by`. Rewrite using `[← map_inv]`. Conclude with `(h1 σ⁻¹).le`.

Establish `e : (fun σ => (((η' σ)⁻¹ : ℤ_[p]ˣ) : ℤ_[p])) = fun σ => (⟨(((η σ)⁻¹ : ℚ_[p]ˣ) : ℚ_[p]), hn σ⟩ : ℤ_[p])`. Use function extensionality and compare the values at `σ`. Apply `PadicInt.ext` to reduce the goal to its premises. Rewrite using `[← map_inv η' σ]`. Use `show ((PadicInt.mkUnits (h1 σ⁻¹) : ℤ_[p]) : ℚ_[p]) = (((η σ)⁻¹ : ℚ_[p]ˣ) : ℚ_[p])`.

Rewrite using `[PadicInt.mkUnits_eq, map_inv]`. Express the relevant statement in the definitionally equal form `Continuous fun σ => (((η' σ)⁻¹ : ℤ_[p]ˣ) : ℤ_[p])`. Rewrite using `[e]`. Conclude with `hinv.subtype_mk _`.
-/
theorem exists_continuous_units_padicInt_lift (η : G →* ℚ_[p]ˣ) (hη : Continuous η) :
    ∃ η' : G →* ℤ_[p]ˣ, Continuous η' ∧ ∀ σ, (((η' σ : ℤ_[p]ˣ) : ℤ_[p]) : ℚ_[p]) = η σ := by
  have h1 := norm_eq_one_of_compactSpace η hη
  let η' : G →* ℤ_[p]ˣ :=
    { toFun := fun σ => PadicInt.mkUnits (h1 σ)
      map_one' := by
        apply Units.ext
        apply PadicInt.ext
        rw [PadicInt.mkUnits_eq, map_one]
        rfl
      map_mul' := fun σ τ => by
        apply Units.ext
        apply PadicInt.ext
        rw [PadicInt.mkUnits_eq, Units.val_mul, PadicInt.coe_mul, PadicInt.mkUnits_eq,
          PadicInt.mkUnits_eq, map_mul, Units.val_mul] }
  refine ⟨η', ?_, fun σ => PadicInt.mkUnits_eq (h1 σ)⟩
  have hval : Continuous fun σ => ((η σ : ℚ_[p]ˣ) : ℚ_[p]) := Units.continuous_val.comp hη
  have hinv : Continuous fun σ => (((η σ)⁻¹ : ℚ_[p]ˣ) : ℚ_[p]) :=
    Units.continuous_val.comp (continuous_inv.comp hη)
  rw [Units.continuous_iff]
  constructor
  · change Continuous fun σ => (⟨((η σ : ℚ_[p]ˣ) : ℚ_[p]), (h1 σ).le⟩ : ℤ_[p])
    exact hval.subtype_mk _
  · have hn : ∀ σ, ‖(((η σ)⁻¹ : ℚ_[p]ˣ) : ℚ_[p])‖ ≤ 1 := fun σ => by
      rw [← map_inv]; exact (h1 σ⁻¹).le
    have e : (fun σ => (((η' σ)⁻¹ : ℤ_[p]ˣ) : ℤ_[p])) =
        fun σ => (⟨(((η σ)⁻¹ : ℚ_[p]ˣ) : ℚ_[p]), hn σ⟩ : ℤ_[p]) := by
      funext σ
      apply PadicInt.ext
      rw [← map_inv η' σ]
      show ((PadicInt.mkUnits (h1 σ⁻¹) : ℤ_[p]) : ℚ_[p]) = (((η σ)⁻¹ : ℚ_[p]ˣ) : ℚ_[p])
      rw [PadicInt.mkUnits_eq, map_inv]
    change Continuous fun σ => (((η' σ)⁻¹ : ℤ_[p]ˣ) : ℤ_[p])
    rw [e]
    exact hinv.subtype_mk _

end SenTateChar

end GroundTheory.PAdicHodge

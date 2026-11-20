import Mathlib
import GroundTheory.AutomorphicForms.GL2Classical.GrowthReduction
import GroundTheory.AutomorphicForms.GL2Classical.KFinite

open NumberField IsDedekindDomain Matrix Set Filter Topology CongruenceSubgroup
open UpperHalfPlane hiding I I_re I_im
open scoped NumberField.AdeleRing MatrixGroups ModularForm Manifold

namespace GroundTheory.Automorphic

noncomputable section

namespace GL2Classical

open AdelicGLn AutomorphicForm GroundTheory.Global ModularForm

set_option linter.unusedSectionVars false

local notation "𝔸f" => FiniteAdeleRing (𝓞 ℚ) ℚ

variable {N : ℕ} [NeZero N] {k : ℤ}

/- English proof (translation)
Establish `hc : IsCusp (toReal δ • (OnePoint.infty : OnePoint ℝ)) (Gamma0 N : Subgroup (GL (Fin 2) ℝ))`. Rewrite using `[Subgroup.IsArithmetic.isCusp_iff_isCusp_SL2Z, isCusp_SL2Z_iff]`. Use `⟨δ • OnePoint.infty, ?_⟩` and prove the remaining obligations. Rewrite using `[← Rat.coe_castHom, OnePoint.map_smul, OnePoint.map_infty]`. Both sides reduce to the same expression.

Conclude with `f.bdd_at_cusps' hc (toReal δ) rfl`.
-/
theorem isBoundedAtImInfty_slash_toReal_of_modularForm (f : ModularForm (Gamma0 N : Subgroup (GL (Fin 2) ℝ)) k)
    (δ : GL (Fin 2) ℚ) : IsBoundedAtImInfty ((f : ℍ → ℂ) ∣[k] toReal δ) := by
  have hc : IsCusp (toReal δ • (OnePoint.infty : OnePoint ℝ)) (Gamma0 N : Subgroup (GL (Fin 2) ℝ)) := by
    rw [Subgroup.IsArithmetic.isCusp_iff_isCusp_SL2Z, isCusp_SL2Z_iff]
    refine ⟨δ • OnePoint.infty, ?_⟩
    rw [← Rat.coe_castHom, OnePoint.map_smul, OnePoint.map_infty]
    rfl
  exact f.bdd_at_cusps' hc (toReal δ) rfl

/- English proof (translation)
Take `⟨M, hM, hconj⟩` from `exists_level_conj N (finiteDiagonal ℚ 2 δ⁻¹)`. Use `⟨M, hM, fun z => ?_⟩` and prove the remaining obligations. Establish `hMmem : algebraMap ℚ 𝔸f (M : ℚ) ∈ levelIdeal M` using `⟨1, one_mem _, by simp⟩`. Establish `hmem : finiteDiagonal ℚ 2 (δ * unipRat M * δ⁻¹) ∈ Gamma0Level N`. Use `finiteDiagonal_conj_mem (N := N) hconj (γ := δ⁻¹) (u := 1) (one_mem _) (by rw [mul_one]) hMmem` as an intermediate fact.

Rewrite `this` using `[inv_inv]`. Then use the resulting hypothesis. Establish `hf : ∀ γ ∈ (Gamma0 N : Subgroup (GL (Fin 2) ℝ)), (f : ℍ → ℂ) ∣[k] γ = f` using `fun γ hγ => SlashInvariantForm.slash_action_eqn f γ hγ`. Use `slash_periodic hf (M : ℚ) hmem z` as an intermediate fact. Simplify using `using this`.
-/
theorem exists_period_slash_toReal (f : SlashInvariantForm (Gamma0 N : Subgroup (GL (Fin 2) ℝ)) k)
    (δ : GL (Fin 2) ℚ) : ∃ M : ℕ, 0 < M ∧ ∀ z : ℍ,
      ((f : ℍ → ℂ) ∣[k] toReal δ) ((M : ℝ) +ᵥ z) = ((f : ℍ → ℂ) ∣[k] toReal δ) z := by
  obtain ⟨M, hM, hconj⟩ := exists_level_conj N (finiteDiagonal ℚ 2 δ⁻¹)
  refine ⟨M, hM, fun z => ?_⟩
  have hMmem : algebraMap ℚ 𝔸f (M : ℚ) ∈ levelIdeal M := ⟨1, one_mem _, by simp⟩
  have hmem : finiteDiagonal ℚ 2 (δ * unipRat M * δ⁻¹) ∈ Gamma0Level N := by
    have := finiteDiagonal_conj_mem (N := N) hconj (γ := δ⁻¹) (u := 1) (one_mem _)
      (by rw [mul_one]) hMmem
    rwa [inv_inv] at this
  have hf : ∀ γ ∈ (Gamma0 N : Subgroup (GL (Fin 2) ℝ)), (f : ℍ → ℂ) ∣[k] γ = f := fun γ hγ =>
    SlashInvariantForm.slash_action_eqn f γ hγ
  have := slash_periodic hf (M : ℚ) hmem z
  simpa using this

/- English proof (translation)
Use `set F := (f : ℍ → ℂ) ∣[k] toReal δ with hF`. Take `⟨B₁, A, hA⟩` from `isBoundedAtImInfty_iff.1 (isBoundedAtImInfty_slash_toReal_of_modularForm f δ)`. Take `⟨M, hM, hper⟩` from `exists_period_slash_toReal f.toSlashInvariantForm δ`. Establish `hMpos : (0 : ℝ) < M` using `by exact_mod_cast hM`. Establish `hcont : Continuous F` using `(f.holo'.slash k (toReal δ)).continuous`.

Establish `hpos : ∀ p : ℝ × ℝ, 0 < ((p.1 : ℂ) + ((max p.2 t₀ : ℝ) : ℂ) * Complex.I).im` using `fun p => by`. Establish `: (0 : ℝ) < max p.2 t₀` using `lt_max_of_lt_right ht₀`. Simplify using `using this`. Use `set P : ℝ × ℝ → ℍ := fun p => ⟨(p.1 : ℂ) + ((max p.2 t₀ : ℝ) : ℂ) * Complex.I, hpos p⟩ with hPdef`. Establish `hP : Continuous P`.

Use `(UpperHalfPlane.isOpenEmbedding_coe.isInducing.continuous_iff).2 ?_` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `Continuous fun p : ℝ × ℝ => (p.1 : ℂ) + ((max p.2 t₀ : ℝ) : ℂ) * Complex.I`. Use `fun_prop`. Establish `hK : IsCompact (Set.Icc (0 : ℝ) M ×ˢ Set.Icc t₀ (max A t₀))` using `isCompact_Icc.prod isCompact_Icc`. Take `⟨B₂, hB₂⟩` from `hK.exists_bound_of_continuousOn (hcont.comp hP).continuousOn`.

Use `⟨max B₁ B₂, fun z hz => ?_⟩` and prove the remaining obligations. Distinguish the cases in `hzA : A ≤ z.im`. Conclude with `(hA z hzA).trans (le_max_left _ _)`. Use `push Not at hzA`. Use `set n : ℤ := ⌊z.re / M⌋ with hn`.

Use `set G : ℝ → ℂ := fun t => F (t +ᵥ z) with hG`. Establish `hGper : Function.Periodic G M` using `fun t => by`. Simplify using `only [hG]`. Rewrite using `[add_comm, add_vadd]`. Conclude with `hper _`.

Establish `hFz : F (((-n : ℤ) : ℝ) * M +ᵥ z) = F z`. Use `hGper.int_mul (-n) 0` as an intermediate fact. Simplify `this` using `[hG]`. Use `set z' : ℍ := ((-n : ℤ) : ℝ) * M +ᵥ z with hz'`. Establish `hre : z'.re = z.re - n * M`.

Rewrite using `[hz', vadd_re]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Establish `him : z'.im = z.im` using `by rw [hz', vadd_im]`. Establish `hfl1 : (n : ℝ) ≤ z.re / M` using `Int.floor_le _`.

Establish `hfl2 : z.re / M < n + 1` using `Int.lt_floor_add_one _`. Establish `hre0 : 0 ≤ z'.re`. Rewrite using `[hre]`. Use `(le_div_iff₀ hMpos).1 hfl1` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion.

Establish `hreM : z'.re ≤ M`. Rewrite using `[hre]`. Use `(div_lt_iff₀ hMpos).1 hfl2` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hzP : z' = P (z'.re, z'.im)`.

Apply `UpperHalfPlane.ext` to reduce the goal to its premises. Simplify using `only [hPdef, UpperHalfPlane.coe_mk]`. Rewrite using `[max_eq_left (him ▸ hz)]`. Conclude with `(Complex.re_add_im _).symm`. Establish `hmem : (z'.re, z'.im) ∈ Set.Icc (0 : ℝ) M ×ˢ Set.Icc t₀ (max A t₀)` using `⟨⟨hre0, hreM⟩, ⟨him ▸ hz, him ▸ (hzA.le.trans (le_max_left _ _))⟩⟩`.

Use `hB₂ _ hmem` as an intermediate fact. Rewrite `this` using `[Function.comp_apply, ← hzP, hz', hFz]`. Conclude with `this.trans (le_max_right _ _)`.
-/
theorem exists_bound_slash_toReal_of_le_im (f : ModularForm (Gamma0 N : Subgroup (GL (Fin 2) ℝ)) k)
    (δ : GL (Fin 2) ℚ) {t₀ : ℝ} (ht₀ : 0 < t₀) :
    ∃ B : ℝ, ∀ z : ℍ, t₀ ≤ z.im → ‖((f : ℍ → ℂ) ∣[k] toReal δ) z‖ ≤ B := by
  set F := (f : ℍ → ℂ) ∣[k] toReal δ with hF
  obtain ⟨B₁, A, hA⟩ := isBoundedAtImInfty_iff.1 (isBoundedAtImInfty_slash_toReal_of_modularForm f δ)
  obtain ⟨M, hM, hper⟩ := exists_period_slash_toReal f.toSlashInvariantForm δ
  have hMpos : (0 : ℝ) < M := by exact_mod_cast hM
  have hcont : Continuous F := (f.holo'.slash k (toReal δ)).continuous
  have hpos : ∀ p : ℝ × ℝ, 0 < ((p.1 : ℂ) + ((max p.2 t₀ : ℝ) : ℂ) * Complex.I).im := fun p => by
    have : (0 : ℝ) < max p.2 t₀ := lt_max_of_lt_right ht₀
    simpa using this
  set P : ℝ × ℝ → ℍ := fun p => ⟨(p.1 : ℂ) + ((max p.2 t₀ : ℝ) : ℂ) * Complex.I, hpos p⟩ with hPdef
  have hP : Continuous P := by
    refine (UpperHalfPlane.isOpenEmbedding_coe.isInducing.continuous_iff).2 ?_
    change Continuous fun p : ℝ × ℝ => (p.1 : ℂ) + ((max p.2 t₀ : ℝ) : ℂ) * Complex.I
    fun_prop
  have hK : IsCompact (Set.Icc (0 : ℝ) M ×ˢ Set.Icc t₀ (max A t₀)) := isCompact_Icc.prod isCompact_Icc
  obtain ⟨B₂, hB₂⟩ := hK.exists_bound_of_continuousOn (hcont.comp hP).continuousOn
  refine ⟨max B₁ B₂, fun z hz => ?_⟩
  by_cases hzA : A ≤ z.im
  · exact (hA z hzA).trans (le_max_left _ _)
  push Not at hzA
  set n : ℤ := ⌊z.re / M⌋ with hn
  set G : ℝ → ℂ := fun t => F (t +ᵥ z) with hG
  have hGper : Function.Periodic G M := fun t => by
    simp only [hG]
    rw [add_comm, add_vadd]
    exact hper _
  have hFz : F (((-n : ℤ) : ℝ) * M +ᵥ z) = F z := by
    have := hGper.int_mul (-n) 0
    simpa [hG] using this
  set z' : ℍ := ((-n : ℤ) : ℝ) * M +ᵥ z with hz'
  have hre : z'.re = z.re - n * M := by
    rw [hz', vadd_re]; push_cast; ring
  have him : z'.im = z.im := by rw [hz', vadd_im]
  have hfl1 : (n : ℝ) ≤ z.re / M := Int.floor_le _
  have hfl2 : z.re / M < n + 1 := Int.lt_floor_add_one _
  have hre0 : 0 ≤ z'.re := by
    rw [hre]
    have := (le_div_iff₀ hMpos).1 hfl1
    linarith
  have hreM : z'.re ≤ M := by
    rw [hre]
    have := (div_lt_iff₀ hMpos).1 hfl2
    linarith
  have hzP : z' = P (z'.re, z'.im) := by
    apply UpperHalfPlane.ext
    simp only [hPdef, UpperHalfPlane.coe_mk]
    rw [max_eq_left (him ▸ hz)]
    exact (Complex.re_add_im _).symm
  have hmem : (z'.re, z'.im) ∈ Set.Icc (0 : ℝ) M ×ˢ Set.Icc t₀ (max A t₀) :=
    ⟨⟨hre0, hreM⟩, ⟨him ▸ hz, him ▸ (hzA.le.trans (le_max_left _ _))⟩⟩
  have := hB₂ _ hmem
  rw [Function.comp_apply, ← hzP, hz', hFz] at this
  exact this.trans (le_max_right _ _)

/- English proof (translation)
Take `⟨B, hB⟩` from `exists_bound_slash_toReal_of_le_im f τ ht₀`. Establish `hf : ∀ γ ∈ (Gamma0 N : Subgroup (GL (Fin 2) ℝ)), (f : ℍ → ℂ) ∣[k] γ = f` using `fun γ hγ => SlashInvariantForm.slash_action_eqn f γ hγ`. Establish `hτR : 0 < (toReal τ).det.val` using `by rw [det_toReal]; exact_mod_cast hτ`. Take `⟨c, hcdef⟩ : ∃ c : ℂ, c = (((toReal τ).det.val : ℂ) ^ (k - 1))⁻¹ * (Real.sqrt (toReal τ).det.val : ℂ) ^ k` from `⟨_, rfl⟩`. Use `⟨‖c‖ * B, fun z hz => ?_⟩` and prove the remaining obligations.

Establish `hdet : 0 < (toReal τ * borelGL z).det.val`. Rewrite using `[map_mul, Units.val_mul]`. Conclude with `mul_pos hτR (det_borelGL_pos z)`. Establish `h1` using `archLift_mul_left (k := k) (f : ℍ → ℂ) hτR (det_borelGL_pos z)`. Rewrite `h1` using `[archLift_borelGL]`.

Establish `hne : ((toReal τ).det.val : ℂ) ^ (k - 1) ≠ 0` using `zpow_ne_zero _ (by exact_mod_cast hτR.ne')`. Establish `e : archLift k f (toReal τ * borelGL z) = c * ((Real.sqrt z.im : ℂ) ^ k * ((f : ℍ → ℂ) ∣[k] toReal τ) z)`. Rewrite using `[eq_inv_mul_iff_mul_eq₀ hne |>.2 h1]`. Rewrite using `[hcdef]`. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[liftEquiv_apply]`. Express the relevant statement in the definitionally equal form `‖adelicLift N k f (realEmb (toReal τ * borelGL z))‖ ≤ _`. Rewrite using `[adelicLift_realEmb hf hdet, e, norm_mul, norm_mul, norm_zpow, Complex.norm_real, Real.norm_of_nonneg (Real.sqrt_nonneg _)]`. Establish `hB'` using `hB z hz`. Establish `hc0` using `norm_nonneg c`.

Establish `hs : 0 ≤ Real.sqrt z.im ^ k` using `zpow_nonneg (Real.sqrt_nonneg _) _`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem exists_bound_liftEquiv_toReal_mul_borelGL
    (f : ModularForm (Gamma0 N : Subgroup (GL (Fin 2) ℝ)) k) (τ : GL (Fin 2) ℚ)
    (hτ : 0 < (τ.det.val : ℚ)) {t₀ : ℝ} (ht₀ : 0 < t₀) :
    ∃ B : ℝ, ∀ z : ℍ, t₀ ≤ z.im →
      ‖(liftEquiv N k f.toSlashInvariantForm : AdelicGL ℚ 2 → ℂ) (realEmb (toReal τ * borelGL z))‖ ≤
        B * Real.sqrt z.im ^ k := by
  obtain ⟨B, hB⟩ := exists_bound_slash_toReal_of_le_im f τ ht₀
  have hf : ∀ γ ∈ (Gamma0 N : Subgroup (GL (Fin 2) ℝ)), (f : ℍ → ℂ) ∣[k] γ = f := fun γ hγ =>
    SlashInvariantForm.slash_action_eqn f γ hγ
  have hτR : 0 < (toReal τ).det.val := by rw [det_toReal]; exact_mod_cast hτ
  obtain ⟨c, hcdef⟩ : ∃ c : ℂ,
      c = (((toReal τ).det.val : ℂ) ^ (k - 1))⁻¹ * (Real.sqrt (toReal τ).det.val : ℂ) ^ k := ⟨_, rfl⟩
  refine ⟨‖c‖ * B, fun z hz => ?_⟩
  have hdet : 0 < (toReal τ * borelGL z).det.val := by
    rw [map_mul, Units.val_mul]
    exact mul_pos hτR (det_borelGL_pos z)
  have h1 := archLift_mul_left (k := k) (f : ℍ → ℂ) hτR (det_borelGL_pos z)
  rw [archLift_borelGL] at h1
  have hne : ((toReal τ).det.val : ℂ) ^ (k - 1) ≠ 0 := zpow_ne_zero _ (by exact_mod_cast hτR.ne')
  have e : archLift k f (toReal τ * borelGL z) =
      c * ((Real.sqrt z.im : ℂ) ^ k * ((f : ℍ → ℂ) ∣[k] toReal τ) z) := by
    rw [eq_inv_mul_iff_mul_eq₀ hne |>.2 h1]
    rw [hcdef]
    ring
  rw [liftEquiv_apply]
  change ‖adelicLift N k f (realEmb (toReal τ * borelGL z))‖ ≤ _
  rw [adelicLift_realEmb hf hdet, e, norm_mul, norm_mul, norm_zpow, Complex.norm_real,
    Real.norm_of_nonneg (Real.sqrt_nonneg _)]
  have hB' := hB z hz
  have hc0 := norm_nonneg c
  have hs : 0 ≤ Real.sqrt z.im ^ k := zpow_nonneg (Real.sqrt_nonneg _) _
  calc ‖c‖ * (Real.sqrt z.im ^ k * ‖((f : ℍ → ℂ) ∣[k] toReal τ) z‖)
      ≤ ‖c‖ * (Real.sqrt z.im ^ k * B) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hB' hs) hc0
    _ = ‖c‖ * B * Real.sqrt z.im ^ k := by ring

/- English proof (translation)
Use `hφ.apply_realEmb_mul_finiteDiagonal epsilon y (u := (finiteDiagonal ℚ 2 epsilon)⁻¹) (inv_mem (finiteDiagonal_epsilon_mem N))` as an intermediate fact. Rewrite `this` using `[mul_inv_cancel, map_one, mul_one]`. Rewrite using `[this, ← map_inv, epsilon_inv]`.
-/
theorem IsWeightLevel.apply_realEmb_epsilon_mul {φ : AdelicGL ℚ 2 → ℂ} (hφ : IsWeightLevel N k φ)
    (y : GL (Fin 2) ℝ) : φ (realEmb (toReal epsilon * y)) = φ (realEmb y) := by
  have := hφ.apply_realEmb_mul_finiteDiagonal epsilon y
    (u := (finiteDiagonal ℚ 2 epsilon)⁻¹) (inv_mem (finiteDiagonal_epsilon_mem N))
  rw [mul_inv_cancel, map_one, mul_one] at this
  rw [this, ← map_inv, epsilon_inv]

/- English proof (translation)
Use `det_toReal_epsilon` as an intermediate fact. Rewrite `this` using `[det_toReal]`. Conclude with `this` after adjusting the coercions.
-/
theorem det_epsilon_val : (epsilon.det.val : ℚ) = -1 := by
  have := det_toReal_epsilon
  rw [det_toReal] at this
  exact_mod_cast this

/- English proof (translation)
Use `set φ := (liftEquiv N k f.toSlashInvariantForm : AdelicGL ℚ 2 → ℂ)`. Establish `hφ : IsWeightLevel N k φ` using `(liftEquiv N k f.toSlashInvariantForm).2`. Take `⟨γ, u, hu, hc⟩` from `exists_eq_finiteDiagonal_mul N c`. Use `set σ : GL (Fin 2) ℚ := γ⁻¹ * (if e then epsilon else 1) with hσ`. Establish `hval : ∀ z : ℍ, φ (realEmb ((if e then toReal epsilon else 1) * borelGL z) * finEmb ℚ 2 c) = φ (realEmb (toReal σ * borelGL z))`.

Introduce `z`. Rewrite using `[hc, hφ.apply_realEmb_mul_finiteDiagonal γ _ hu]`. Use `congr 2`. Rewrite using `[hσ, map_mul, map_inv, mul_assoc]`. Apply the tactic sequence `cases e <;> simp`.

Distinguish the cases in `hσpos : 0 < (σ.det.val : ℚ)`. Take `⟨B, hB⟩` from `exists_bound_liftEquiv_toReal_mul_borelGL f σ hσpos ht₀`. Conclude with `⟨B, fun z hz => (hval z).symm ▸ hB z hz⟩`. Establish `hneg : (σ.det.val : ℚ) < 0` using `lt_of_le_of_ne (not_lt.1 hσpos) (Units.ne_zero _)`. Establish `hpos : 0 < ((epsilon * σ).det.val : ℚ)`.

Rewrite using `[map_mul, Units.val_mul, det_epsilon_val]`. Combine the linear equalities and inequalities to obtain the conclusion. Take `⟨B, hB⟩` from `exists_bound_liftEquiv_toReal_mul_borelGL f (epsilon * σ) hpos ht₀`. Use `⟨B, fun z hz => ?_⟩` and prove the remaining obligations. Rewrite using `[hval z, ← hφ.apply_realEmb_epsilon_mul, ← mul_assoc, ← map_mul]`.

Conclude with `hB z hz`.
-/
theorem exists_bound_liftEquiv_borelGL_mul_finEmb
    (f : ModularForm (Gamma0 N : Subgroup (GL (Fin 2) ℝ)) k) (c : FiniteAdelicGL ℚ 2) (e : Bool)
    {t₀ : ℝ} (ht₀ : 0 < t₀) :
    ∃ B : ℝ, ∀ z : ℍ, t₀ ≤ z.im →
      ‖(liftEquiv N k f.toSlashInvariantForm : AdelicGL ℚ 2 → ℂ)
          (realEmb ((if e then toReal epsilon else 1) * borelGL z) * finEmb ℚ 2 c)‖ ≤
        B * Real.sqrt z.im ^ k := by
  set φ := (liftEquiv N k f.toSlashInvariantForm : AdelicGL ℚ 2 → ℂ)
  have hφ : IsWeightLevel N k φ := (liftEquiv N k f.toSlashInvariantForm).2
  obtain ⟨γ, u, hu, hc⟩ := exists_eq_finiteDiagonal_mul N c
  set σ : GL (Fin 2) ℚ := γ⁻¹ * (if e then epsilon else 1) with hσ
  have hval : ∀ z : ℍ, φ (realEmb ((if e then toReal epsilon else 1) * borelGL z) * finEmb ℚ 2 c) =
      φ (realEmb (toReal σ * borelGL z)) := by
    intro z
    rw [hc, hφ.apply_realEmb_mul_finiteDiagonal γ _ hu]
    congr 2
    rw [hσ, map_mul, map_inv, mul_assoc]
    cases e <;> simp
  by_cases hσpos : 0 < (σ.det.val : ℚ)
  · obtain ⟨B, hB⟩ := exists_bound_liftEquiv_toReal_mul_borelGL f σ hσpos ht₀
    exact ⟨B, fun z hz => (hval z).symm ▸ hB z hz⟩
  · have hneg : (σ.det.val : ℚ) < 0 := lt_of_le_of_ne (not_lt.1 hσpos) (Units.ne_zero _)
    have hpos : 0 < ((epsilon * σ).det.val : ℚ) := by
      rw [map_mul, Units.val_mul, det_epsilon_val]
      linarith
    obtain ⟨B, hB⟩ := exists_bound_liftEquiv_toReal_mul_borelGL f (epsilon * σ) hpos ht₀
    refine ⟨B, fun z hz => ?_⟩
    rw [hval z, ← hφ.apply_realEmb_epsilon_mul, ← mul_assoc, ← map_mul]
    exact hB z hz

/- English proof (translation)
Rewrite using `[map_mul, map_mul]`. Simplify using `only [mul_assoc]`. Rewrite using `[← mul_assoc (finEmb ℚ 2 b) (realEmb c), ← realEmb_mul_finEmb_comm c b]`. Simplify using `only [mul_assoc]`.
-/
theorem diagonal_mul_realEmb_mul_finEmb_mul (δ : GL (Fin 2) ℚ) (a c : GL (Fin 2) ℝ)
    (b d : FiniteAdelicGL ℚ 2) :
    diagonal ℚ 2 δ * realEmb a * finEmb ℚ 2 b * (realEmb c * finEmb ℚ 2 d) =
      diagonal ℚ 2 δ * (realEmb (a * c) * finEmb ℚ 2 (b * d)) := by
  rw [map_mul, map_mul]
  simp only [mul_assoc]
  rw [← mul_assoc (finEmb ℚ 2 b) (realEmb c), ← realEmb_mul_finEmb_comm c b]
  simp only [mul_assoc]

/- English proof (translation)
Establish `e : realEmb (X * kGL w hw) * finEmb ℚ 2 c = realEmb X * finEmb ℚ 2 c * realEmb (kGL w hw)`. Rewrite using `[map_mul, mul_assoc, realEmb_mul_finEmb_comm (kGL w hw) c, ← mul_assoc]`. Establish `hn : ‖w / (‖w‖ : ℂ)‖ = 1`. Rewrite using `[norm_div, Complex.norm_real, Real.norm_of_nonneg (norm_nonneg _), div_self (norm_ne_zero_iff.2 hw)]`. Rewrite using `[e, hφ.right_kGL, norm_mul, norm_zpow, hn, _root_.one_zpow, one_mul]`.
-/
theorem IsWeightLevel.norm_apply_realEmb_mul_kGL_mul_finEmb {φ : AdelicGL ℚ 2 → ℂ}
    (hφ : IsWeightLevel N k φ) (X : GL (Fin 2) ℝ) {w : ℂ} (hw : w ≠ 0) (c : FiniteAdelicGL ℚ 2) :
    ‖φ (realEmb (X * kGL w hw) * finEmb ℚ 2 c)‖ = ‖φ (realEmb X * finEmb ℚ 2 c)‖ := by
  have e : realEmb (X * kGL w hw) * finEmb ℚ 2 c = realEmb X * finEmb ℚ 2 c * realEmb (kGL w hw) := by
    rw [map_mul, mul_assoc, realEmb_mul_finEmb_comm (kGL w hw) c, ← mul_assoc]
  have hn : ‖w / (‖w‖ : ℂ)‖ = 1 := by
    rw [norm_div, Complex.norm_real, Real.norm_of_nonneg (norm_nonneg _), div_self (norm_ne_zero_iff.2 hw)]
  rw [e, hφ.right_kGL, norm_mul, norm_zpow, hn, _root_.one_zpow, one_mul]

/- English proof (translation)
Establish `hpos : 0 < (-(starRingEnd ℂ) (z : ℂ)).im` using `by simpa using z.im_pos`. Use `⟨⟨-(starRingEnd ℂ) (z : ℂ), hpos⟩, by change (-(starRingEnd ℂ) (z : ℂ)).im = _; simp, ?_⟩` and prove the remaining obligations. Use `Units.ext ?_` and prove the remaining obligations. Simplify using `only [Units.val_mul, coe_borelGL, coe_kGL, coe_toReal_epsilon]`. Establish `h1 : UpperHalfPlane.im ⟨-(starRingEnd ℂ) (z : ℂ), hpos⟩ = z.im`.

Express the relevant statement in the definitionally equal form `(-(starRingEnd ℂ) (z : ℂ)).im = _`. Simplify using the standard rewrite rules. Establish `h2 : UpperHalfPlane.re ⟨-(starRingEnd ℂ) (z : ℂ), hpos⟩ = -z.re`. Express the relevant statement in the definitionally equal form `(-(starRingEnd ℂ) (z : ℂ)).re = _`. Simplify using the standard rewrite rules.

Rewrite using `[h1, h2]`. Use extensionality with `i j`. Apply the tactic sequence `fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]`.
-/
theorem exists_borelGL_mul_kGL_mul_epsilon (z : ℍ) (r : ℝ) (hr : (r : ℂ) ≠ 0) :
    ∃ z' : ℍ, z'.im = z.im ∧
      borelGL z * kGL (r : ℂ) hr * toReal epsilon = toReal epsilon * borelGL z' * kGL (r : ℂ) hr := by
  have hpos : 0 < (-(starRingEnd ℂ) (z : ℂ)).im := by simpa using z.im_pos
  refine ⟨⟨-(starRingEnd ℂ) (z : ℂ), hpos⟩, by change (-(starRingEnd ℂ) (z : ℂ)).im = _; simp, ?_⟩
  refine Units.ext ?_
  simp only [Units.val_mul, coe_borelGL, coe_kGL, coe_toReal_epsilon]
  have h1 : UpperHalfPlane.im ⟨-(starRingEnd ℂ) (z : ℂ), hpos⟩ = z.im := by
    change (-(starRingEnd ℂ) (z : ℂ)).im = _; simp
  have h2 : UpperHalfPlane.re ⟨-(starRingEnd ℂ) (z : ℂ), hpos⟩ = -z.re := by
    change (-(starRingEnd ℂ) (z : ℂ)).re = _; simp
  rw [h1, h2]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

/- English proof (translation)
Establish `hYpos : 0 < Y` using `ht₀.trans_le hY`. Establish `hH0 : 0 < H` using `zero_lt_one.trans_le hH`. Establish `hC : 0 ≤ C`. Assume the negation of the conclusion as `h`. Use `push Not at h`.

Use polynomial arithmetic with `[pow_pos hH0 4]`. Take `⟨m, rfl | rfl⟩` from `Int.eq_nat_or_neg k`. Simplify using `only [Int.natAbs_natCast, zpow_natCast]`. Establish `hs : Real.sqrt Y ≤ Real.sqrt C * H ^ 2`. Combine the equalities or inequalities in the displayed calculation.

Rewrite using `[Real.sqrt_mul hC, show H ^ 4 = (H ^ 2) ^ 2 by ring, Real.sqrt_sq (by positivity)]`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[one_mul]`. Conclude with `mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (Real.sqrt_nonneg _) (le_max_right _ _) _) (by positivity)`. Use `_ ≤ (max 1 (Real.sqrt t₀)⁻¹) ^ m * (max 1 (Real.sqrt C)) ^ m * H ^ (2 * m) := by gcongr`.

Conclude with `one_le_pow₀ (le_max_left _ _)`. Simplify using `only [Int.natAbs_neg, Int.natAbs_natCast, _root_.zpow_neg, zpow_natCast]`. Establish `hst : 0 < Real.sqrt t₀` using `Real.sqrt_pos.2 ht₀`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[mul_one, mul_one]`.

Conclude with `pow_le_pow_left₀ (inv_nonneg.2 hst.le) (le_max_right _ _) _`. Use `_ ≤ (max 1 (Real.sqrt t₀)⁻¹) ^ m * (max 1 (Real.sqrt C)) ^ m * H ^ (2 * m) := by gcongr`. Conclude with `one_le_pow₀ (le_max_left _ _)`. Conclude with `one_le_pow₀ hH`.
-/
theorem sqrt_zpow_le_of_le_of_le {Y t₀ C H : ℝ} (ht₀ : 0 < t₀) (hY : t₀ ≤ Y) (hYC : Y ≤ C * H ^ 4)
    (hH : 1 ≤ H) (k : ℤ) :
    Real.sqrt Y ^ k ≤
      (max 1 (Real.sqrt t₀)⁻¹) ^ k.natAbs * (max 1 (Real.sqrt C)) ^ k.natAbs * H ^ (2 * k.natAbs) := by
  have hYpos : 0 < Y := ht₀.trans_le hY
  have hH0 : 0 < H := zero_lt_one.trans_le hH
  have hC : 0 ≤ C := by
    by_contra h
    push Not at h
    nlinarith [pow_pos hH0 4]
  obtain ⟨m, rfl | rfl⟩ := Int.eq_nat_or_neg k
  · simp only [Int.natAbs_natCast, zpow_natCast]
    have hs : Real.sqrt Y ≤ Real.sqrt C * H ^ 2 := by
      calc Real.sqrt Y ≤ Real.sqrt (C * H ^ 4) := Real.sqrt_le_sqrt hYC
        _ = Real.sqrt C * H ^ 2 := by
          rw [Real.sqrt_mul hC, show H ^ 4 = (H ^ 2) ^ 2 by ring, Real.sqrt_sq (by positivity)]
    calc Real.sqrt Y ^ m ≤ (Real.sqrt C * H ^ 2) ^ m := pow_le_pow_left₀ (Real.sqrt_nonneg _) hs _
      _ = Real.sqrt C ^ m * H ^ (2 * m) := by rw [mul_pow, ← pow_mul]
      _ ≤ 1 * (max 1 (Real.sqrt C)) ^ m * H ^ (2 * m) := by
          rw [one_mul]
          exact mul_le_mul_of_nonneg_right
            (pow_le_pow_left₀ (Real.sqrt_nonneg _) (le_max_right _ _) _) (by positivity)
      _ ≤ (max 1 (Real.sqrt t₀)⁻¹) ^ m * (max 1 (Real.sqrt C)) ^ m * H ^ (2 * m) := by
          gcongr
          exact one_le_pow₀ (le_max_left _ _)
  · simp only [Int.natAbs_neg, Int.natAbs_natCast, _root_.zpow_neg, zpow_natCast]
    have hst : 0 < Real.sqrt t₀ := Real.sqrt_pos.2 ht₀
    calc (Real.sqrt Y ^ m)⁻¹ ≤ (Real.sqrt t₀ ^ m)⁻¹ :=
          inv_anti₀ (pow_pos hst _) (pow_le_pow_left₀ hst.le (Real.sqrt_le_sqrt hY) _)
      _ = (Real.sqrt t₀)⁻¹ ^ m := (inv_pow _ _).symm
      _ ≤ (max 1 (Real.sqrt t₀)⁻¹) ^ m * 1 * 1 := by
          rw [mul_one, mul_one]
          exact pow_le_pow_left₀ (inv_nonneg.2 hst.le) (le_max_right _ _) _
      _ ≤ (max 1 (Real.sqrt t₀)⁻¹) ^ m * (max 1 (Real.sqrt C)) ^ m * H ^ (2 * m) := by
          gcongr
          · exact one_le_pow₀ (le_max_left _ _)
          · exact one_le_pow₀ hH

/- English proof (translation)
Use `set φ := (liftEquiv N k f.toSlashInvariantForm : AdelicGL ℚ 2 → ℂ) with hφdef`. Establish `hφ : IsWeightLevel N k φ` using `(liftEquiv N k f.toSlashInvariantForm).2`. Take `⟨t₀, ht₀, hred⟩` from `Reduction.exists_reduced (K := ℚ)`. Take `⟨C, hC⟩` from `exists_finset_cover N`. Establish `hB : ∀ p : C × Bool, ∃ B : ℝ, ∀ z : ℍ, t₀ ≤ z.im → ‖φ (realEmb ((if p.2 then toReal epsilon else 1) * borelGL z) * finEmb ℚ 2 p.1)‖ ≤ B * Real.sqrt z.im ^ k` using `fun p => exists_bound_liftEquiv_borelGL_mul_finEmb f p.1 p.2 ht₀`.

Use `choose B hBp using hB`. Use `set B₀ : ℝ := ∑ p, |B p| with hB₀def`. Establish `hB₀0 : 0 ≤ B₀` using `Finset.sum_nonneg fun p _ => abs_nonneg _`. Establish `hB₀ : ∀ c ∈ C, ∀ (e : Bool) (z : ℍ), t₀ ≤ z.im → ‖φ (realEmb ((if e then toReal epsilon else 1) * borelGL z) * finEmb ℚ 2 c)‖ ≤ B₀ * Real.sqrt z.im ^ k`. Introduce `c hc e z hz`.

Use `(hBp (⟨c, hc⟩, e) z hz).trans (mul_le_mul_of_nonneg_right ?_ (zpow_nonneg (Real.sqrt_nonneg _) _))` and prove the remaining obligations. Conclude with `(le_abs_self _).trans (Finset.single_le_sum (f := fun p => |B p|) (fun p _ => abs_nonneg _) (Finset.mem_univ _))`. Use `set C4 : ℝ := (∏ w : InfinitePlace ℚ, (2 : ℝ) ^ w.mult) * (∏ w : InfinitePlace ℚ, (√((2 : ℕ) : ℝ) * ((2 : ℕ) : ℝ)) ^ w.mult) ^ 2 with hC4`. Use `⟨B₀ * ((max 1 (Real.sqrt t₀)⁻¹) ^ k.natAbs * (max 1 (Real.sqrt C4)) ^ k.natAbs), 2 * k.natAbs, fun g => ?_⟩` and prove the remaining obligations. Take `⟨γ, b, hb, κ, hκ, heq, hr⟩` from `hred 2 g`.

Establish `hr01` using `hr 0 1 rfl`. Take `⟨δ, z, r, hr0, hzim, w, hw, hbdec⟩` from `exists_eq_diagonal_mul_borelGL_mul hb`. Establish `hratio` using `adeleAbs_div_le_height_pow_four hb hκ heq`. Rewrite `hratio` using `[← hzim]`. Establish `hd : 0 < Reduction.adeleAbs ((b : Matrix (Fin 2) (Fin 2) 𝔸[ℚ]) 1 1)`.

Rewrite using `[← IsUnit.unit_spec (Reduction.isUnit_apply_self_of_mem_adelicBorel hb 1), Reduction.adeleAbs_units]`. Conclude with `(GroundTheory.Global.IdeleGroup.ideleModule ℚ _).2`. Establish `hY0 : t₀ ≤ z.im`. Rewrite using `[hzim, le_div_iff₀ hd]`. Conclude with `hr01`.

Establish `hval : ‖φ g‖ ≤ B₀ * Real.sqrt z.im ^ k`. Establish `h1 : φ g = φ (b * κ)`. Rewrite using `[← heq]`. Conclude with `(hφ.isLeftInvariant γ g).symm`. Rewrite using `[h1, hbdec, ← realEmb_realPart_mul_finEmb κ, diagonal_mul_realEmb_mul_finEmb_mul, hφ.isLeftInvariant]`.

Take `⟨c, hcC, hcu⟩` from `hC (w * (prodEquiv ℚ 2 κ).2) (mul_mem hw (finitePart_mem_integralFiniteGL hκ))`. Establish `e2 : finEmb ℚ 2 (w * (prodEquiv ℚ 2 κ).2) = finEmb ℚ 2 c * finEmb ℚ 2 (c⁻¹ * (w * (prodEquiv ℚ 2 κ).2))`. Rewrite using `[← map_mul, mul_inv_cancel_left]`. Rewrite using `[e2, ← mul_assoc, hφ.right_level _ _ hcu]`. Take `⟨h1o, h2o, h3o⟩` from `realPart_orthogonal hκ`.

Take `⟨w', hw'0, -, hK⟩` from `exists_eq_kGL_of_orthogonal (realPart κ) h1o h2o h3o`. Break down `hK with hK | hK` into its components or cases. Rewrite using `[hK, mul_assoc, kGL_mul, hφ.norm_apply_realEmb_mul_kGL_mul_finEmb]`. Simplify using `using hB₀ c hcC false z hY0`. Take `⟨z', hz'im, hz'eq⟩` from `exists_borelGL_mul_kGL_mul_epsilon z r hr0`.

Rewrite using `[hK, ← mul_assoc, hz'eq, mul_assoc, kGL_mul, hφ.norm_apply_realEmb_mul_kGL_mul_finEmb]`. Use `hB₀ c hcC true z' (hz'im ▸ hY0)` as an intermediate fact. Rewrite `this` using `[hz'im]`. Simplify using `using this`. Use `hval.trans ?_` and prove the remaining obligations.

Rewrite using `[mul_assoc]`. Conclude with `mul_le_mul_of_nonneg_left (sqrt_zpow_le_of_le_of_le ht₀ hY0 hratio (one_le_height g) k) hB₀0`.
-/
theorem hasModerateGrowth_liftEquiv_modularForm
    (f : ModularForm (Gamma0 N : Subgroup (GL (Fin 2) ℝ)) k) :
    HasModerateGrowth (liftEquiv N k f.toSlashInvariantForm : AdelicGL ℚ 2 → ℂ) := by
  set φ := (liftEquiv N k f.toSlashInvariantForm : AdelicGL ℚ 2 → ℂ) with hφdef
  have hφ : IsWeightLevel N k φ := (liftEquiv N k f.toSlashInvariantForm).2
  obtain ⟨t₀, ht₀, hred⟩ := Reduction.exists_reduced (K := ℚ)
  obtain ⟨C, hC⟩ := exists_finset_cover N
  have hB : ∀ p : C × Bool, ∃ B : ℝ, ∀ z : ℍ, t₀ ≤ z.im →
      ‖φ (realEmb ((if p.2 then toReal epsilon else 1) * borelGL z) * finEmb ℚ 2 p.1)‖ ≤
        B * Real.sqrt z.im ^ k := fun p => exists_bound_liftEquiv_borelGL_mul_finEmb f p.1 p.2 ht₀
  choose B hBp using hB
  set B₀ : ℝ := ∑ p, |B p| with hB₀def
  have hB₀0 : 0 ≤ B₀ := Finset.sum_nonneg fun p _ => abs_nonneg _
  have hB₀ : ∀ c ∈ C, ∀ (e : Bool) (z : ℍ), t₀ ≤ z.im →
      ‖φ (realEmb ((if e then toReal epsilon else 1) * borelGL z) * finEmb ℚ 2 c)‖ ≤
        B₀ * Real.sqrt z.im ^ k := by
    intro c hc e z hz
    refine (hBp (⟨c, hc⟩, e) z hz).trans
      (mul_le_mul_of_nonneg_right ?_ (zpow_nonneg (Real.sqrt_nonneg _) _))
    exact (le_abs_self _).trans (Finset.single_le_sum (f := fun p => |B p|)
      (fun p _ => abs_nonneg _) (Finset.mem_univ _))
  set C4 : ℝ := (∏ w : InfinitePlace ℚ, (2 : ℝ) ^ w.mult) *
    (∏ w : InfinitePlace ℚ, (√((2 : ℕ) : ℝ) * ((2 : ℕ) : ℝ)) ^ w.mult) ^ 2 with hC4
  refine ⟨B₀ * ((max 1 (Real.sqrt t₀)⁻¹) ^ k.natAbs * (max 1 (Real.sqrt C4)) ^ k.natAbs),
    2 * k.natAbs, fun g => ?_⟩
  obtain ⟨γ, b, hb, κ, hκ, heq, hr⟩ := hred 2 g
  have hr01 := hr 0 1 rfl
  obtain ⟨δ, z, r, hr0, hzim, w, hw, hbdec⟩ := exists_eq_diagonal_mul_borelGL_mul hb
  have hratio := adeleAbs_div_le_height_pow_four hb hκ heq
  rw [← hzim] at hratio
  have hd : 0 < Reduction.adeleAbs ((b : Matrix (Fin 2) (Fin 2) 𝔸[ℚ]) 1 1) := by
    rw [← IsUnit.unit_spec (Reduction.isUnit_apply_self_of_mem_adelicBorel hb 1), Reduction.adeleAbs_units]
    exact (GroundTheory.Global.IdeleGroup.ideleModule ℚ _).2
  have hY0 : t₀ ≤ z.im := by
    rw [hzim, le_div_iff₀ hd]
    exact hr01
  have hval : ‖φ g‖ ≤ B₀ * Real.sqrt z.im ^ k := by
    have h1 : φ g = φ (b * κ) := by
      rw [← heq]
      exact (hφ.isLeftInvariant γ g).symm
    rw [h1, hbdec, ← realEmb_realPart_mul_finEmb κ, diagonal_mul_realEmb_mul_finEmb_mul,
      hφ.isLeftInvariant]
    obtain ⟨c, hcC, hcu⟩ := hC (w * (prodEquiv ℚ 2 κ).2) (mul_mem hw (finitePart_mem_integralFiniteGL hκ))
    have e2 : finEmb ℚ 2 (w * (prodEquiv ℚ 2 κ).2) =
        finEmb ℚ 2 c * finEmb ℚ 2 (c⁻¹ * (w * (prodEquiv ℚ 2 κ).2)) := by
      rw [← map_mul, mul_inv_cancel_left]
    rw [e2, ← mul_assoc, hφ.right_level _ _ hcu]
    obtain ⟨h1o, h2o, h3o⟩ := realPart_orthogonal hκ
    obtain ⟨w', hw'0, -, hK⟩ := exists_eq_kGL_of_orthogonal (realPart κ) h1o h2o h3o
    rcases hK with hK | hK
    · rw [hK, mul_assoc, kGL_mul, hφ.norm_apply_realEmb_mul_kGL_mul_finEmb]
      simpa using hB₀ c hcC false z hY0
    · obtain ⟨z', hz'im, hz'eq⟩ := exists_borelGL_mul_kGL_mul_epsilon z r hr0
      rw [hK, ← mul_assoc, hz'eq, mul_assoc, kGL_mul, hφ.norm_apply_realEmb_mul_kGL_mul_finEmb]
      have := hB₀ c hcC true z' (hz'im ▸ hY0)
      rw [hz'im] at this
      simpa using this
  refine hval.trans ?_
  rw [mul_assoc]
  exact mul_le_mul_of_nonneg_left
    (sqrt_zpow_le_of_le_of_le ht₀ hY0 hratio (one_le_height g) k) hB₀0

end GL2Classical

end

end GroundTheory.Automorphic

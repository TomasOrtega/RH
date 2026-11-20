import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.StrSMul
import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.Imports
import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.SmoothVectorFixedByOpenSubgroup
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.LocallyConstantOfKernel

open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.U3 UpperTheory.V.Fr

/- English proof (translation)
The claim follows from `_root_.UpperTheory.Reformulated.B.LocallyConstantOfKernel.lc_of_ker f hf`.
-/
private theorem lc_of_ker {G H : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [Group H] (f : G →* H)
    (hf : IsOpen (f.ker : Set G)) : IsLocallyConstant f :=
  _root_.UpperTheory.Reformulated.B.LocallyConstantOfKernel.lc_of_ker f hf

/- English proof (translation)
Introduce `l _ k _ _ F C₀ h`. Establish `hχ0 : ∀ g : F.G0, (F.Ψ⁻¹ ^ 2 * F.delK k) g = (F.Ψ g)⁻¹ ^ 2` using `fun g => by`. Establish `: F.del g = 1` using `g.2`. Simplify using `[Frame.delK, this]`. Establish `hχ : ∀ g : F.G0, (((F.Ψ⁻¹ ^ 2 * F.delK k) g : kˣ) : k) = ((F.Ψ g : k))⁻¹ ^ 2` using `fun g => by`.

Rewrite using `[hχ0]`. Simplify using the standard rewrite rules. Establish `hc : (F.Ψ⁻¹ ^ 2 * F.delK k) F.c = -1`. Apply `Units.ext` to reduce the goal to its premises. Simplify using `[Frame.delK, h.Ψ_c, h.del_c]`.

Take `⟨x, x1, x2, x3, x4, g₁, x5⟩` from `UpperTheory.smooth_vector_fixed_by_open_subgroup h (F.Ψ⁻¹ ^ 2 * F.delK k) hc (fun v => by`. Take `⟨s, hs⟩` from `h.f3 v`. Use `⟨s, fun e => hs ?_⟩` and prove the remaining obligations. Establish `e'` using `(hχ0 (F.loc0 v s)).symm.trans e`. Rewrite `e'` using `[inv_pow, inv_eq_one]`.

Conclude with `e') h.f4'`. Establish `x0 : x 1 = 0`. Use `x2 1 1` as an intermediate fact. Rewrite `this` using `[mul_one, map_one]`. Simplify using `using this`.

Establish `hci : F.c⁻¹ = F.c` using `inv_eq_of_mul_eq_one_right h.c_sq`. Use `⟨fun g => x g * F.Ψ g, ⟨?_, fun g g' => ?_, fun g => ?_, fun v => ?_⟩, fun e => ?_⟩` and prove the remaining obligations. Conclude with `(x1.mul ((lc_of_ker F.Ψ h.Ψ_open).comp Units.val)).comp_continuous continuous_subtype_val`. Use `(F.Ψ g).ne_zero` as an intermediate fact. Simplify using `only [Subgroup.coe_mul, x2, hχ, map_mul, Units.val_mul, smul_eq_mul, Units.val_inv_eq_inv_val]`.

Clear the denominators using the available nonvanishing facts. Establish `hs : ((F.star g : F.G0) : F.Γ) = F.c * ((g : F.Γ)⁻¹ * F.c)`. Rewrite using `[← mul_assoc]`. Use `nth_rewrite 2 [← hci]`. Both sides reduce to the same expression.

Establish `h0` using `(F.Ψ g).ne_zero`. Establish `e1` using `x2 g (g : F.Γ)⁻¹`. Rewrite `e1` using `[mul_inv_cancel, x0, hχ]`. Use `show x (F.star g) * F.Ψ (F.star g) = x g * F.Ψ g`. Rewrite using `[(star h).2.2.1 g, hs, x2, x2, x3, hc, Units.val_inv_eq_inv_val]`.

Establish `e2 : x g = -((F.Ψ g : k)⁻¹ ^ 2 * x (g : F.Γ)⁻¹)` using `by linear_combination -e1`. Rewrite using `[e2]`. Simplify using `only [Units.val_neg, Units.val_one]`. Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree.

Take `⟨Y, hY⟩` from `x4 v`. Use `⟨-Y, fun s => ?_⟩` and prove the remaining obligations. Establish `h0` using `(F.Ψ (F.loc v s)).ne_zero`. Establish `e : (((F.Ψ⁻¹ ^ 2 * F.delK k) (F.loc v s) : kˣ) : k) = ((F.Ψ (F.loc v s) : k))⁻¹ ^ 2` using `hχ (F.loc0 v s)`. Use `show x (F.loc v s) * F.Ψ (F.loc v s) = _`.

Rewrite using `[hY, e, Units.val_inv_eq_inv_val, smul_eq_mul]`. Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree. Conclude with `mul_ne_zero x5 (F.Ψ g₁).ne_zero (congrFun e g₁)`.
-/
theorem UpperTheory.exists_mem_strS_ne_zero_of_frameOk :
    ∀ {l : ℕ} [Fact l.Prime] {k : Type} [Field k] [CharP k l] {F : Frame l k} {C₀ : ℕ}, F.Ok C₀ → ∃ b ∈ F.strS k, b ≠ 0 := by
  intro l _ k _ _ F C₀ h
  have hχ0 : ∀ g : F.G0, (F.Ψ⁻¹ ^ 2 * F.delK k) g = (F.Ψ g)⁻¹ ^ 2 := fun g => by
    have : F.del g = 1 := g.2
    simp [Frame.delK, this]
  have hχ : ∀ g : F.G0, (((F.Ψ⁻¹ ^ 2 * F.delK k) g : kˣ) : k) = ((F.Ψ g : k))⁻¹ ^ 2 := fun g => by
    rw [hχ0]; simp
  have hc : (F.Ψ⁻¹ ^ 2 * F.delK k) F.c = -1 := by
    apply Units.ext
    simp [Frame.delK, h.Ψ_c, h.del_c]
  obtain ⟨x, x1, x2, x3, x4, g₁, x5⟩ := UpperTheory.smooth_vector_fixed_by_open_subgroup h (F.Ψ⁻¹ ^ 2 * F.delK k) hc (fun v => by
    obtain ⟨s, hs⟩ := h.f3 v
    refine ⟨s, fun e => hs ?_⟩
    have e' := (hχ0 (F.loc0 v s)).symm.trans e
    rw [inv_pow, inv_eq_one] at e'
    exact e') h.f4'
  have x0 : x 1 = 0 := by
    have := x2 1 1
    rw [mul_one, map_one] at this
    simpa using this
  have hci : F.c⁻¹ = F.c := inv_eq_of_mul_eq_one_right h.c_sq
  refine ⟨fun g => x g * F.Ψ g, ⟨?_, fun g g' => ?_, fun g => ?_, fun v => ?_⟩, fun e => ?_⟩
  · exact (x1.mul ((lc_of_ker F.Ψ h.Ψ_open).comp Units.val)).comp_continuous continuous_subtype_val
  · have := (F.Ψ g).ne_zero
    simp only [Subgroup.coe_mul, x2, hχ, map_mul, Units.val_mul, smul_eq_mul, Units.val_inv_eq_inv_val]
    field_simp
  · have hs : ((F.star g : F.G0) : F.Γ) = F.c * ((g : F.Γ)⁻¹ * F.c) := by
      rw [← mul_assoc]
      nth_rewrite 2 [← hci]
      rfl
    have h0 := (F.Ψ g).ne_zero
    have e1 := x2 g (g : F.Γ)⁻¹
    rw [mul_inv_cancel, x0, hχ] at e1
    show x (F.star g) * F.Ψ (F.star g) = x g * F.Ψ g
    rw [(star h).2.2.1 g, hs, x2, x2, x3, hc, Units.val_inv_eq_inv_val]
    have e2 : x g = -((F.Ψ g : k)⁻¹ ^ 2 * x (g : F.Γ)⁻¹) := by linear_combination -e1
    rw [e2]
    simp only [Units.val_neg, Units.val_one]
    field_simp
    ring
  · obtain ⟨Y, hY⟩ := x4 v
    refine ⟨-Y, fun s => ?_⟩
    have h0 := (F.Ψ (F.loc v s)).ne_zero
    have e : (((F.Ψ⁻¹ ^ 2 * F.delK k) (F.loc v s) : kˣ) : k) = ((F.Ψ (F.loc v s) : k))⁻¹ ^ 2 := hχ (F.loc0 v s)
    show x (F.loc v s) * F.Ψ (F.loc v s) = _
    rw [hY, e, Units.val_inv_eq_inv_val, smul_eq_mul]
    field_simp
    ring
  · exact mul_ne_zero x5 (F.Ψ g₁).ne_zero (congrFun e g₁)

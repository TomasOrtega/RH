import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.StrYMap
import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.Imports
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.LocallyConstantOfKernel

open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.U3 UpperTheory.V.Fr

/- English proof (translation)
The claim follows from `_root_.UpperTheory.Reformulated.B.LocallyConstantOfKernel.lc_of_ker f hf`.
-/
private theorem lc_of_open_ker {G H : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [Group H]
    (f : G →* H) (hf : IsOpen (f.ker : Set G)) : IsLocallyConstant f :=
  _root_.UpperTheory.Reformulated.B.LocallyConstantOfKernel.lc_of_ker f hf

/- English proof (translation)
Introduce `l _ k _ _ F C₀ h a ha`. Take `⟨a1, a2, a3, a4⟩` from `ha`. Use `choose γ hγ using a4`. Establish `hd : ∀ g : F.G0, F.del g = 1` using `fun g => g.2`. Establish `hcc : F.c⁻¹ = F.c` using `inv_eq_of_mul_eq_one_right h.c_sq`.

Establish `hconj : ∀ g : F.G0, ((F.conj g : F.G0) : F.Γ) = F.c * g * F.c` using `fun g => by`. Rewrite using `[← hcc]`. Use `nth_rewrite 1 [hcc]`. Both sides reduce to the same expression. Establish `a0 : a 1 = 0`.

Use `a2 1 1` as an intermediate fact. Simplify using `using this`. Establish `ainv : ∀ g, a g⁻¹ = - a g` using `fun g => by`. Use `a2 g g⁻¹` as an intermediate fact. Rewrite `this` using `[mul_inv_cancel, a0]`.

Simplify using `only [smul_eq_mul, Subgroup.coe_inv, map_inv] at this`. Rewrite `this` using `[← mul_add]`. Establish `h2` using `(mul_eq_zero.1 this.symm).resolve_left (Units.ne_zero _)`. Take the linear combination `h2`. Establish `ac : ∀ g, a (F.conj g) = - a g` using `fun g => by`.

Rewrite using `[← ainv, ← a3 g⁻¹]`. Simplify using `[Frame.star]`. Establish `Ψc : ∀ g : F.G0, F.Ψ (F.conj g) = F.Ψ g` using `fun g => by simp [hconj, h.Ψ_c]`. Set `b : F.G0 → k` to `fun g => a g * (((F.Ψ g)⁻¹ : kˣ) : k)`. Establish `b1 : IsLocallyConstant b`.

Use `a1.mul ?_` and prove the remaining obligations. Conclude with `((lc_of_open_ker F.Ψ h.Ψ_open).comp_continuous continuous_subtype_val).comp (fun u : kˣ => ((u⁻¹ : kˣ) : k))`. Establish `b2 : ∀ g g' : F.G0, b (g * g') = b g + ((F.Ψ g : k)⁻¹) ^ 2 * b g'` using `fun g g' => by`. Simplify using `only [b, a2, smul_eq_mul, Subgroup.coe_mul, map_mul, Units.val_inv_eq_inv_val, Units.val_mul]`. Use `(F.Ψ g).ne_zero` as an intermediate fact.

Use `(F.Ψ g').ne_zero` as an intermediate fact. Clear the denominators using the available nonvanishing facts. Establish `bc : ∀ g, b (F.conj g) = - b g` using `fun g => by simp only [b, ac, Ψc, neg_mul]`. Set `e : ℤˣ → F.Γ` to `fun u => if u = 1 then 1 else F.c`. Establish `he : ∀ s : F.Γ, s * e (F.del s) ∈ F.del.ker` using `fun s => by`.

Rewrite using `[MonoidHom.mem_ker, map_mul]`. Apply the tactic sequence `rcases Int.units_eq_one_or (F.del s) with h1 | h1 <;> simp [e, h1, h.del_c]`. Set `p : F.Γ → F.G0` to `fun s => ⟨s * e (F.del s), he s⟩`. Establish `pc : Continuous p` using `Continuous.subtype_mk (continuous_id.mul ((lc_of_open_ker F.del h.del_open).comp e).continuous) _`. Establish `p1 : ∀ g : F.G0, p g = g` using `fun g => Subtype.ext (by simp [p, e, hd])`.

Establish `p2 : ∀ g : F.G0, p (g * F.c) = g` using `fun g => Subtype.ext (by simp [p, e, hd, h.del_c, mul_assoc, h.c_sq])`. Establish `dec : ∀ s : F.Γ, ∃ g : F.G0, s = g ∨ s = g * F.c` using `fun s => by`. Use `⟨p s, ?_⟩` and prove the remaining obligations. Break down `Int.units_eq_one_or (F.del s) with h1 | h1` into its components or cases. Use `left`.

Simplify using `[p, e, h1]`. Use `right`. Simplify using `[p, e, h1, mul_assoc, h.c_sq]`. Establish `χ1 : ∀ g : F.G0, (((F.Ψ⁻¹ ^ 2 * F.delK k) g : kˣ) : k) = ((F.Ψ g : k)⁻¹) ^ 2` using `fun g => by`. Simplify using `[Frame.delK, hd]`.

Establish `χ2 : ∀ g : F.G0, (((F.Ψ⁻¹ ^ 2 * F.delK k) (g * F.c) : kˣ) : k) = -((F.Ψ g : k)⁻¹) ^ 2` using `fun g => by`. Simplify using `[Frame.delK, hd, h.del_c, h.Ψ_c]`. Use `⟨(fun s => b (p s), fun v => - γ v), ⟨b1.comp_continuous pc, fun s t => ?_, fun v s => ?_⟩, ?_, fun g => ?_⟩` and prove the remaining obligations. Use `show b (p (s * t)) = b (p s) + chRep _ s (b (p t))`. Rewrite using `[chRep_apply]`.

Apply the tactic sequence `obtain ⟨g, rfl | rfl⟩ := dec s <;> obtain ⟨g', rfl | rfl⟩ := dec t`. Rewrite using `[← Subgroup.coe_mul, p1, p1, p1, χ1, b2]`. Rewrite using `[← mul_assoc, ← Subgroup.coe_mul, p2, p1, p2, χ1, b2]`. Establish `: (g : F.Γ) * F.c * g' = ((g * F.conj g' : F.G0) : F.Γ) * F.c`. Simplify using `[hconj, mul_assoc, h.c_sq]`.

Rewrite using `[this, p2, p2, p1, χ2, b2, bc]`. Expand and normalize the polynomial expressions, which then agree. Establish `: (g : F.Γ) * F.c * (g' * F.c) = ((g * F.conj g' : F.G0) : F.Γ)`. Simplify using `[hconj, mul_assoc]`. Rewrite using `[this, p1, p2, p2, χ2, b2, bc]`.

Expand and normalize the polynomial expressions, which then agree. Use `show b (p (F.loc0 v s)) - (chRep _ (F.loc0 v s : F.Γ) (- γ v) - - γ v) ∈ (⊥ : Submodule k k)`. Rewrite using `[chRep_apply, p1, χ1, Submodule.mem_bot]`. Establish `h1 : F.loc v s = (F.loc0 v s : F.Γ)` using `rfl`. Simplify using `only [b, hγ, h1, smul_eq_mul, Units.val_inv_eq_inv_val]`.

Use `(F.Ψ (F.loc0 v s)).ne_zero` as an intermediate fact. Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree. Use `show b (p F.c) = 0`. Use `p2 1` as an intermediate fact.

Simplify using `only [OneMemClass.coe_one, one_mul] at this`. Simplify using `[this, b, a0]`. Use `show a g = b (p g) * _`. Rewrite using `[p1]`. Simplify using `[b]`.
-/
theorem UpperTheory.V.Fr.frame_extension_of_locallyConstant :
    ∀ {l : ℕ} [Fact l.Prime] {k : Type} [Field k] [CharP k l] {F : Frame l k} {C₀ : ℕ}, F.Ok C₀ → ∀ a ∈ F.strS k, ∃ x ∈ Z1C F.loc (chRep (F.Ψ⁻¹ ^ 2 * F.delK k)) (fun _ => ⊥), x.1 F.c = 0 ∧ ∀ g : F.G0, a g = x.1 g * F.Ψ g := by
  classical
  intro l _ k _ _ F C₀ h a ha
  obtain ⟨a1, a2, a3, a4⟩ := ha
  choose γ hγ using a4
  have hd : ∀ g : F.G0, F.del g = 1 := fun g => g.2
  have hcc : F.c⁻¹ = F.c := inv_eq_of_mul_eq_one_right h.c_sq
  have hconj : ∀ g : F.G0, ((F.conj g : F.G0) : F.Γ) = F.c * g * F.c := fun g => by
    rw [← hcc]; nth_rewrite 1 [hcc]; rfl
  have a0 : a 1 = 0 := by
    have := a2 1 1
    simpa using this
  have ainv : ∀ g, a g⁻¹ = - a g := fun g => by
    have := a2 g g⁻¹
    rw [mul_inv_cancel, a0] at this
    simp only [smul_eq_mul, Subgroup.coe_inv, map_inv] at this
    rw [← mul_add] at this
    have h2 := (mul_eq_zero.1 this.symm).resolve_left (Units.ne_zero _)
    linear_combination h2
  have ac : ∀ g, a (F.conj g) = - a g := fun g => by
    rw [← ainv, ← a3 g⁻¹]; simp [Frame.star]
  have Ψc : ∀ g : F.G0, F.Ψ (F.conj g) = F.Ψ g := fun g => by simp [hconj, h.Ψ_c]
  let b : F.G0 → k := fun g => a g * (((F.Ψ g)⁻¹ : kˣ) : k)
  have b1 : IsLocallyConstant b := by
    refine a1.mul ?_
    exact ((lc_of_open_ker F.Ψ h.Ψ_open).comp_continuous continuous_subtype_val).comp
      (fun u : kˣ => ((u⁻¹ : kˣ) : k))
  have b2 : ∀ g g' : F.G0, b (g * g') = b g + ((F.Ψ g : k)⁻¹) ^ 2 * b g' := fun g g' => by
    simp only [b, a2, smul_eq_mul, Subgroup.coe_mul, map_mul, Units.val_inv_eq_inv_val, Units.val_mul]
    have := (F.Ψ g).ne_zero
    have := (F.Ψ g').ne_zero
    field_simp
  have bc : ∀ g, b (F.conj g) = - b g := fun g => by simp only [b, ac, Ψc, neg_mul]
  let e : ℤˣ → F.Γ := fun u => if u = 1 then 1 else F.c
  have he : ∀ s : F.Γ, s * e (F.del s) ∈ F.del.ker := fun s => by
    rw [MonoidHom.mem_ker, map_mul]
    rcases Int.units_eq_one_or (F.del s) with h1 | h1 <;> simp [e, h1, h.del_c]
  let p : F.Γ → F.G0 := fun s => ⟨s * e (F.del s), he s⟩
  have pc : Continuous p :=
    Continuous.subtype_mk (continuous_id.mul ((lc_of_open_ker F.del h.del_open).comp e).continuous) _
  have p1 : ∀ g : F.G0, p g = g := fun g => Subtype.ext (by simp [p, e, hd])
  have p2 : ∀ g : F.G0, p (g * F.c) = g := fun g =>
    Subtype.ext (by simp [p, e, hd, h.del_c, mul_assoc, h.c_sq])
  have dec : ∀ s : F.Γ, ∃ g : F.G0, s = g ∨ s = g * F.c := fun s => by
    refine ⟨p s, ?_⟩
    rcases Int.units_eq_one_or (F.del s) with h1 | h1
    · left; simp [p, e, h1]
    · right; simp [p, e, h1, mul_assoc, h.c_sq]
  have χ1 : ∀ g : F.G0, (((F.Ψ⁻¹ ^ 2 * F.delK k) g : kˣ) : k) = ((F.Ψ g : k)⁻¹) ^ 2 := fun g => by
    simp [Frame.delK, hd]
  have χ2 : ∀ g : F.G0, (((F.Ψ⁻¹ ^ 2 * F.delK k) (g * F.c) : kˣ) : k) = -((F.Ψ g : k)⁻¹) ^ 2 := fun g => by
    simp [Frame.delK, hd, h.del_c, h.Ψ_c]
  refine ⟨(fun s => b (p s), fun v => - γ v), ⟨b1.comp_continuous pc, fun s t => ?_, fun v s => ?_⟩, ?_, fun g => ?_⟩
  · show b (p (s * t)) = b (p s) + chRep _ s (b (p t))
    rw [chRep_apply]
    obtain ⟨g, rfl | rfl⟩ := dec s <;> obtain ⟨g', rfl | rfl⟩ := dec t
    · rw [← Subgroup.coe_mul, p1, p1, p1, χ1, b2]
    · rw [← mul_assoc, ← Subgroup.coe_mul, p2, p1, p2, χ1, b2]
    · have : (g : F.Γ) * F.c * g' = ((g * F.conj g' : F.G0) : F.Γ) * F.c := by
        simp [hconj, mul_assoc, h.c_sq]
      rw [this, p2, p2, p1, χ2, b2, bc]; ring
    · have : (g : F.Γ) * F.c * (g' * F.c) = ((g * F.conj g' : F.G0) : F.Γ) := by
        simp [hconj, mul_assoc]
      rw [this, p1, p2, p2, χ2, b2, bc]; ring
  · show b (p (F.loc0 v s)) - (chRep _ (F.loc0 v s : F.Γ) (- γ v) - - γ v) ∈ (⊥ : Submodule k k)
    rw [chRep_apply, p1, χ1, Submodule.mem_bot]
    have h1 : F.loc v s = (F.loc0 v s : F.Γ) := rfl
    simp only [b, hγ, h1, smul_eq_mul, Units.val_inv_eq_inv_val]
    have := (F.Ψ (F.loc0 v s)).ne_zero
    field_simp
    ring
  · show b (p F.c) = 0
    have := p2 1
    simp only [OneMemClass.coe_one, one_mul] at this
    simp [this, b, a0]
  · show a g = b (p g) * _
    rw [p1]
    simp [b]

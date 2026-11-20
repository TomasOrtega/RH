import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.StrYMap
import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.Imports

open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.U3 UpperTheory.V.Fr

/- English proof (translation)
Introduce `l _ k _ _ F C₀ hF`. Take `⟨-, -, hΨst, -, -⟩` from `UpperTheory.V.Fr.star hF`. Use `choose gv hgv using hF.f3`. Use `set ρ := chRep (F.Ψ⁻¹.comp F.del.ker.subtype) with hρ`. Establish `hρapp : ∀ (g : F.G0) (w : k), ρ g w = ((F.Ψ (g : F.Γ) : k))⁻¹ * w`.

Introduce `g w`. Simplify using `[hρ, chRep]`. Establish `hne : ∀ γ : F.Γ, ((F.Ψ γ : k)) ≠ 0` using `fun γ => Units.ne_zero _`. Establish `hl : ∀ v s, ((F.loc0 v s : F.G0) : F.Γ) = F.loc v s` using `fun _ _ => rfl`. Establish `ha : ∀ v, ((F.Ψ (F.loc v (gv v)) : k)) ≠ 1`.

Introduce `v h`. Apply `hgv v` to reduce the goal to its premises. Rewrite using `[Units.val_eq_one.mp h, one_pow]`. Establish `hΨlc : IsLocallyConstant (fun g : F.G0 => F.Ψ (g : F.Γ))`. Rewrite using `[IsLocallyConstant.iff_exists_open]`.

Introduce `g`. Use `⟨(fun h : F.G0 => g⁻¹ * h) ⁻¹' ((↑) ⁻¹' (F.Ψ.ker : Set F.Γ)), ?_, ?_, ?_⟩` and prove the remaining obligations. Conclude with `(hF.Ψ_open.preimage continuous_subtype_val).preimage (continuous_const.mul continuous_id)`. Simplify using the standard rewrite rules. Introduce `h hh`.

Simplify using `only [Set.mem_preimage, SetLike.mem_coe, MonoidHom.mem_ker, Subgroup.coe_mul, Subgroup.coe_inv, map_mul, map_inv] at hh`. Conclude with `(inv_mul_eq_one.mp hh).symm`. Set `xf : (F.G0 → k) → F.G0 → k` to `fun y g => ((F.Ψ (g : F.Γ) : k))⁻¹ * y g`. Set `af : (F.G0 → k) → F.V × Bool → k` to `fun y p => if p.2 then (1 - ((F.Ψ (F.loc p.1 (gv p.1)) : k))⁻¹)⁻¹ * y (F.star (F.loc0 p.1 (gv p.1))) else -((((F.Ψ (F.loc p.1 (gv p.1)) : k)) - 1)⁻¹ * y (F.loc0 p.1 (gv p.1)))`. Establish `hmem : ∀ y ∈ F.strY k, (xf y, af y) ∈ Z1C F.loc2 ρ (fun _ => ⊥)`.

Introduce `y hy`. Take `⟨hlc, hcoc, hg0, hα, hβ⟩` from `hy`. Use `⟨?_, ?_, ?_⟩` and prove the remaining obligations. Conclude with `hΨlc.comp₂ hlc (fun u w => ((u : k))⁻¹ * w)`. Introduce `s t`.

Rewrite using `[hρapp]`. Simplify using `only [xf]`. Rewrite using `[hcoc s t, Subgroup.coe_mul, map_mul, Units.val_mul, smul_eq_mul]`. Use `hne s` as an intermediate fact. Use `hne t` as an intermediate fact.

Clear the denominators using the available nonvanishing facts. Introduce and unpack `⟨v, b⟩ s`. Rewrite using `[Submodule.mem_bot, hρapp]`. Simplify using `only`. Establish `h1 : ((F.Ψ (F.loc v (gv v)) : k)) - 1 ≠ 0` using `sub_ne_zero.mpr (ha v)`.

Establish `h2 : 1 - ((F.Ψ (F.loc v (gv v)) : k))⁻¹ ≠ 0`. Rewrite using `[sub_ne_zero]`. Introduce `h`. Conclude with `ha v (inv_eq_one.mp h.symm)`. Use `hne (F.loc v (gv v))` as an intermediate fact.

Use `hne (F.loc v s)` as an intermediate fact. Consider the cases of `b`. Take `⟨α, hα'⟩` from `hα v`. Establish `key : af y (v, false) = -α`. Simplify using `only [af, Bool.false_eq_true, if_false]`.

Rewrite using `[hα' (gv v), smul_eq_mul]`. Clear the denominators using the available nonvanishing facts. Rewrite using `[key]`. Simplify using `only [xf, Frame.loc2, Bool.false_eq_true, if_false]`. Rewrite using `[hl, hα' s, smul_eq_mul]`.

Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree. Take `⟨β, hβ'⟩` from `hβ v`. Establish `key : af y (v, true) = β`. Simplify using `only [af, if_true]`.

Rewrite using `[hβ' (gv v), smul_eq_mul, Units.val_inv_eq_inv_val]`. Clear the denominators using the available nonvanishing facts. Establish `hc : F.star (F.loc0 v s⁻¹) = F.conj (F.loc0 v s)` using `by show F.conj ((F.loc0 v s⁻¹)⁻¹) = _`. Rewrite using `[map_inv (F.loc0 v) s, inv_inv]`. Establish `hcv : F.Ψ ((F.conj (F.loc0 v s) : F.G0) : F.Γ) = F.Ψ (F.loc v s)`.

Rewrite using `[← hc, hΨst, hl, map_inv, map_inv, inv_inv]`. Rewrite using `[key]`. Simplify using `only [xf, Frame.loc2, if_true, MonoidHom.comp_apply]`. Rewrite using `[hcv, ← hc, hβ' s⁻¹]`. Simplify using `only [map_inv, inv_inv, Units.val_inv_eq_inv_val, smul_eq_mul]`.

Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree. Set `φ : F.strY k →ₗ[k] Z1C F.loc2 ρ (fun _ => ⊥)` to `{ toFun := fun y => ⟨(xf y.1, af y.1), hmem y.1 y.2⟩ map_add' := by`. Introduce `y z`. Apply `Subtype.ext` to reduce the goal to its premises.

Use `Prod.ext (funext fun g => ?_) (funext fun p => ?_)` and prove the remaining obligations. Simplify using `[xf, mul_add]`. Apply the tactic sequence `simp only [af, Submodule.coe_add, Prod.snd_add, Pi.add_apply] split_ifs <;> ring`. Use the proof step `map_smul' := by`. Introduce `a y`.

Apply `Subtype.ext` to reduce the goal to its premises. Use `Prod.ext (funext fun g => ?_) (funext fun p => ?_)` and prove the remaining obligations. Simplify using `[xf]`. Expand and normalize the polynomial expressions, which then agree. Apply the tactic sequence `simp only [af, SetLike.val_smul, Prod.smul_snd, Pi.smul_apply, smul_eq_mul, RingHom.id_apply] split_ifs <;> ring }`.

Establish `hinj : Function.Injective ((Submodule.mkQ (Submodule.comap (Z1C F.loc2 ρ (fun _ => ⊥)).subtype (continuousCoboundaries1 ρ (fun _ => ⊥)))).comp φ)`. Rewrite using `[← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]`. Introduce `y hy`. Rewrite `hy` using `[LinearMap.mem_ker, LinearMap.comp_apply, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero, Submodule.mem_comap]`. Take `⟨X, hX, -⟩` from `hy`.

Take `⟨-, -, hg0, -, -⟩` from `y.2`. Establish `hy' : ∀ g, (y : F.G0 → k) g = X - ((F.Ψ (g : F.Γ) : k)) * X`. Introduce `g`. Establish `h` using `hX g`. Rewrite `h` using `[hρapp]`.

Use `hne g` as an intermediate fact. Express the relevant statement in the definitionally equal form `((F.Ψ (g : F.Γ) : k))⁻¹ * (y : F.G0 → k) g = _ at h`. Clear denominators, using `at h` for the nonvanishing conditions. Take the linear combination `h`. Establish `hd : ((F.Ψ (F.g0 : F.Γ) : k)) - ((F.Ψ (F.g0 : F.Γ) : k))⁻¹ ≠ 0`.

Introduce `h`. Apply `hF.baseSubgroup_spec` to reduce the goal to its premises. Establish `hu` using `hne F.g0`. Rewrite `h` using `[sub_eq_zero]`. Rewrite using `[Units.ext_iff, Units.val_pow_eq_pow_val, Units.val_one, pow_two]`.

Combine the equalities or inequalities in the displayed calculation. Establish `hX0 : X = 0`. Establish `h` using `hg0`. Rewrite `h` using `[hy', hy', hΨst, Units.val_inv_eq_inv_val]`. Establish `h' : (((F.Ψ (F.g0 : F.Γ) : k)) - ((F.Ψ (F.g0 : F.Γ) : k))⁻¹) * X = 0`.

Take the linear combination `-h`. Conclude with `(mul_eq_zero.mp h').resolve_left hd`. Apply `Subtype.ext` to reduce the goal to its premises. Use function extensionality and compare the values at `g`. Rewrite using `[hy', hX0]`.

Simplify using the standard rewrite rules. Conclude with `(LinearMap.rank_le_of_injective _ hinj).trans hF.b1`.
-/
theorem UpperTheory.V.Fr.finrank_structMapY_range :
    ∀ {l : ℕ} [Fact l.Prime] {k : Type} [Field k] [CharP k l] {F : Frame l k} {C₀ : ℕ}, F.Ok C₀ → Module.rank k (F.strY k) ≤ C₀ := by
  intro l _ k _ _ F C₀ hF
  obtain ⟨-, -, hΨst, -, -⟩ := UpperTheory.V.Fr.star hF
  choose gv hgv using hF.f3
  set ρ := chRep (F.Ψ⁻¹.comp F.del.ker.subtype) with hρ
  have hρapp : ∀ (g : F.G0) (w : k), ρ g w = ((F.Ψ (g : F.Γ) : k))⁻¹ * w := by
    intro g w
    simp [hρ, chRep]
  have hne : ∀ γ : F.Γ, ((F.Ψ γ : k)) ≠ 0 := fun γ => Units.ne_zero _
  have hl : ∀ v s, ((F.loc0 v s : F.G0) : F.Γ) = F.loc v s := fun _ _ => rfl
  have ha : ∀ v, ((F.Ψ (F.loc v (gv v)) : k)) ≠ 1 := by
    intro v h
    apply hgv v
    rw [Units.val_eq_one.mp h, one_pow]
  have hΨlc : IsLocallyConstant (fun g : F.G0 => F.Ψ (g : F.Γ)) := by
    rw [IsLocallyConstant.iff_exists_open]
    intro g
    refine ⟨(fun h : F.G0 => g⁻¹ * h) ⁻¹' ((↑) ⁻¹' (F.Ψ.ker : Set F.Γ)), ?_, ?_, ?_⟩
    · exact (hF.Ψ_open.preimage continuous_subtype_val).preimage (continuous_const.mul continuous_id)
    · simp
    · intro h hh
      simp only [Set.mem_preimage, SetLike.mem_coe, MonoidHom.mem_ker, Subgroup.coe_mul,
        Subgroup.coe_inv, map_mul, map_inv] at hh
      exact (inv_mul_eq_one.mp hh).symm
  let xf : (F.G0 → k) → F.G0 → k := fun y g => ((F.Ψ (g : F.Γ) : k))⁻¹ * y g
  let af : (F.G0 → k) → F.V × Bool → k := fun y p =>
    if p.2 then (1 - ((F.Ψ (F.loc p.1 (gv p.1)) : k))⁻¹)⁻¹ * y (F.star (F.loc0 p.1 (gv p.1)))
    else -((((F.Ψ (F.loc p.1 (gv p.1)) : k)) - 1)⁻¹ * y (F.loc0 p.1 (gv p.1)))
  have hmem : ∀ y ∈ F.strY k, (xf y, af y) ∈ Z1C F.loc2 ρ (fun _ => ⊥) := by
    intro y hy
    obtain ⟨hlc, hcoc, hg0, hα, hβ⟩ := hy
    refine ⟨?_, ?_, ?_⟩
    · exact hΨlc.comp₂ hlc (fun u w => ((u : k))⁻¹ * w)
    · intro s t
      rw [hρapp]
      simp only [xf]
      rw [hcoc s t, Subgroup.coe_mul, map_mul, Units.val_mul, smul_eq_mul]
      have := hne s
      have := hne t
      field_simp
    · rintro ⟨v, b⟩ s
      rw [Submodule.mem_bot, hρapp]
      dsimp only
      have h1 : ((F.Ψ (F.loc v (gv v)) : k)) - 1 ≠ 0 := sub_ne_zero.mpr (ha v)
      have h2 : 1 - ((F.Ψ (F.loc v (gv v)) : k))⁻¹ ≠ 0 := by
        rw [sub_ne_zero]
        intro h
        exact ha v (inv_eq_one.mp h.symm)
      have := hne (F.loc v (gv v))
      have := hne (F.loc v s)
      cases b
      · obtain ⟨α, hα'⟩ := hα v
        have key : af y (v, false) = -α := by
          simp only [af, Bool.false_eq_true, if_false]
          rw [hα' (gv v), smul_eq_mul]
          field_simp
        rw [key]
        simp only [xf, Frame.loc2, Bool.false_eq_true, if_false]
        rw [hl, hα' s, smul_eq_mul]
        field_simp
        ring
      · obtain ⟨β, hβ'⟩ := hβ v
        have key : af y (v, true) = β := by
          simp only [af, if_true]
          rw [hβ' (gv v), smul_eq_mul, Units.val_inv_eq_inv_val]
          field_simp
        have hc : F.star (F.loc0 v s⁻¹) = F.conj (F.loc0 v s) := by
          show F.conj ((F.loc0 v s⁻¹)⁻¹) = _
          rw [map_inv (F.loc0 v) s, inv_inv]
        have hcv : F.Ψ ((F.conj (F.loc0 v s) : F.G0) : F.Γ) = F.Ψ (F.loc v s) := by
          rw [← hc, hΨst, hl, map_inv, map_inv, inv_inv]
        rw [key]
        simp only [xf, Frame.loc2, if_true, MonoidHom.comp_apply]
        rw [hcv, ← hc, hβ' s⁻¹]
        simp only [map_inv, inv_inv, Units.val_inv_eq_inv_val, smul_eq_mul]
        field_simp
        ring
  let φ : F.strY k →ₗ[k] Z1C F.loc2 ρ (fun _ => ⊥) :=
    { toFun := fun y => ⟨(xf y.1, af y.1), hmem y.1 y.2⟩
      map_add' := by
        intro y z
        apply Subtype.ext
        refine Prod.ext (funext fun g => ?_) (funext fun p => ?_)
        · simp [xf, mul_add]
        · simp only [af, Submodule.coe_add, Prod.snd_add, Pi.add_apply]
          split_ifs <;> ring
      map_smul' := by
        intro a y
        apply Subtype.ext
        refine Prod.ext (funext fun g => ?_) (funext fun p => ?_)
        · simp [xf]
          ring
        · simp only [af, SetLike.val_smul, Prod.smul_snd, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
          split_ifs <;> ring }
  have hinj : Function.Injective
      ((Submodule.mkQ (Submodule.comap (Z1C F.loc2 ρ (fun _ => ⊥)).subtype (continuousCoboundaries1 ρ (fun _ => ⊥)))).comp φ) := by
    rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
    intro y hy
    rw [LinearMap.mem_ker, LinearMap.comp_apply, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero,
      Submodule.mem_comap] at hy
    obtain ⟨X, hX, -⟩ := hy
    obtain ⟨-, -, hg0, -, -⟩ := y.2
    have hy' : ∀ g, (y : F.G0 → k) g = X - ((F.Ψ (g : F.Γ) : k)) * X := by
      intro g
      have h := hX g
      rw [hρapp] at h
      have := hne g
      change ((F.Ψ (g : F.Γ) : k))⁻¹ * (y : F.G0 → k) g = _ at h
      field_simp at h
      linear_combination h
    have hd : ((F.Ψ (F.g0 : F.Γ) : k)) - ((F.Ψ (F.g0 : F.Γ) : k))⁻¹ ≠ 0 := by
      intro h
      apply hF.baseSubgroup_spec
      have hu := hne F.g0
      rw [sub_eq_zero] at h
      rw [Units.ext_iff, Units.val_pow_eq_pow_val, Units.val_one, pow_two]
      calc ((F.Ψ (F.g0 : F.Γ) : k)) * (F.Ψ (F.g0 : F.Γ) : k)
          = (F.Ψ (F.g0 : F.Γ) : k) * ((F.Ψ (F.g0 : F.Γ) : k))⁻¹ := by rw [← h]
        _ = 1 := mul_inv_cancel₀ hu
    have hX0 : X = 0 := by
      have h := hg0
      rw [hy', hy', hΨst, Units.val_inv_eq_inv_val] at h
      have h' : (((F.Ψ (F.g0 : F.Γ) : k)) - ((F.Ψ (F.g0 : F.Γ) : k))⁻¹) * X = 0 := by
        linear_combination -h
      exact (mul_eq_zero.mp h').resolve_left hd
    apply Subtype.ext
    funext g
    rw [hy', hX0]
    simp
  exact (LinearMap.rank_le_of_injective _ hinj).trans hF.b1

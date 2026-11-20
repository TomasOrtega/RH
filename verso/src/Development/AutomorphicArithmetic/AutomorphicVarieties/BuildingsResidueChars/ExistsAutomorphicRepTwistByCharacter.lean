import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.IsTheta
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.BcDefs
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Polynomial GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.UnitaryBC UpperTheory.V UpperTheory.V.Hi
open UpperTheory.V.W (Plc)
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

private noncomputable def mulCh {Γ : Type} [Group Γ] (χ : Γ →* ℂˣ) : (Γ → ℂ) ≃ₗ[ℂ] (Γ → ℂ) where
  toFun φ g := (χ g : ℂ) * φ g
  invFun φ g := ((χ g)⁻¹ : ℂˣ) * φ g
  map_add' φ ψ := by ext g; simp [mul_add]
  map_smul' c φ := by ext g; simp [mul_left_comm]
  left_inv φ := by ext g; simp
  right_inv φ := by ext g; simp

/- English proof (translation)
Use `Units.continuous_val.comp (continuous_of_continuousAt_one χ ?_)` and prove the remaining obligations. Use `(continuousAt_const (y := (1 : ℂˣ))).congr ?_` and prove the remaining obligations. Use `filter_upwards [h.mem_nhds χ.ker.one_mem] with g hg`. Conclude with `(MonoidHom.mem_ker.1 hg).symm`.
-/
private theorem cont_ch {Γ : Type} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] (χ : Γ →* ℂˣ)
    (h : IsOpen (χ.ker : Set Γ)) : Continuous fun g => (χ g : ℂ) := by
  refine Units.continuous_val.comp (continuous_of_continuousAt_one χ ?_)
  refine (continuousAt_const (y := (1 : ℂˣ))).congr ?_
  filter_upwards [h.mem_nhds χ.ker.one_mem] with g hg
  exact (MonoidHom.mem_ker.1 hg).symm

/- English proof (translation)
Rewrite using `[isIrreducible_iff, isIrreducible_iff]`. Use `and_congr_right fun _ => forall_congr' fun W => imp_congr_left ?_` and prove the remaining obligations. Use `forall_congr' fun g => forall_congr' fun v => forall_congr' fun _ => ?_` and prove the remaining obligations. Conclude with `(W.smul_mem_iff (Units.ne_zero (η g))).symm`.
-/
private theorem irr_tw {H M : Type} [Group H] [AddCommGroup M] [Module ℂ M] (ρ : Representation ℂ H M) (η : H →* ℂˣ) :
    ρ.IsIrreducible ↔ (twRep ρ η).IsIrreducible := by
  rw [isIrreducible_iff, isIrreducible_iff]
  refine and_congr_right fun _ => forall_congr' fun W => imp_congr_left ?_
  refine forall_congr' fun g => forall_congr' fun v => forall_congr' fun _ => ?_
  exact (W.smul_mem_iff (Units.ne_zero (η g))).symm

section
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ} (χ : UA E n →* ℂˣ)

/- English proof (translation)
Use extensionality with `g`. Express the relevant statement in the definitionally equal form `(χ (g * x) : ℂ) * φ (g * x) = (χ x : ℂ) * ((χ g : ℂ) * φ (g * x))`. Rewrite using `[map_mul, Units.val_mul]`. Expand and normalize the polynomial expressions, which then agree.
-/
private theorem RU_mulCh (x : UA E n) (φ : UA E n → ℂ) :
    RU E n x (mulCh χ φ) = (χ x : ℂ) • mulCh χ (RU E n x φ) := by
  ext g
  change (χ (g * x) : ℂ) * φ (g * x) = (χ x : ℂ) * ((χ g : ℂ) * φ (g * x))
  rw [map_mul, Units.val_mul]; ring

/- English proof (translation)
Use `⟨(cont_ch χ ho).mul h.cont, fun γ hγ g => ?_, ?_, ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `(χ (γ * g) : ℂ) * φ (γ * g) = (χ g : ℂ) * φ g`. Rewrite using `[map_mul, hr γ hγ, one_mul, h.left γ hγ]`. Use `isOpen_stab_of_mem_nhds ((RU E n).comp (finU E n).subtype) (mulCh χ φ) ?_` and prove the remaining obligations. Establish `h2 : IsOpen ((Subtype.val : finU E n → UA E n) ⁻¹' (χ.ker : Set (UA E n)))` using `ho.preimage continuous_subtype_val`.

Use `Filter.mem_of_superset ((h.level.inter h2).mem_nhds ⟨?_, ?_⟩) fun k hk => ?_` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `RU E n 1 φ = φ`. Simplify using the standard rewrite rules. Conclude with `χ.ker.one_mem`. Establish `h1 : RU E n k φ = φ` using `hk.1`.

Establish `h3 : χ k = 1` using `hk.2`. Express the relevant statement in the definitionally equal form `RU E n k (mulCh χ φ) = mulCh χ φ`. Rewrite using `[RU_mulCh, h1, h3]`. Simplify using the standard rewrite rules. Use `haveI := h.kfin`.

Use `Submodule.finiteDimensional_of_le (S₂ := (Submodule.span ℂ (Set.range fun k : infU E n => RU E n k φ)).map (mulCh χ).toLinearMap) (Submodule.span_le.2 ?_)` and prove the remaining obligations. Introduce and unpack `_ ⟨k, rfl⟩`. Express the relevant statement in the definitionally equal form `RU E n k (mulCh χ φ) ∈ _`. Rewrite using `[RU_mulCh]`. Conclude with `Submodule.smul_mem _ _ (Submodule.mem_map_of_mem (Submodule.subset_span ⟨k, rfl⟩))`.
-/
private theorem form_mulCh (ho : IsOpen (χ.ker : Set (UA E n))) (hr : ∀ g ∈ ratU E n, χ g = 1) {φ : UA E n → ℂ}
    (h : IsAutFormU φ) : IsAutFormU (mulCh χ φ) := by
  refine ⟨(cont_ch χ ho).mul h.cont, fun γ hγ g => ?_, ?_, ?_⟩
  · change (χ (γ * g) : ℂ) * φ (γ * g) = (χ g : ℂ) * φ g
    rw [map_mul, hr γ hγ, one_mul, h.left γ hγ]
  · refine isOpen_stab_of_mem_nhds ((RU E n).comp (finU E n).subtype) (mulCh χ φ) ?_
    have h2 : IsOpen ((Subtype.val : finU E n → UA E n) ⁻¹' (χ.ker : Set (UA E n))) := ho.preimage continuous_subtype_val
    refine Filter.mem_of_superset ((h.level.inter h2).mem_nhds ⟨?_, ?_⟩) fun k hk => ?_
    · change RU E n 1 φ = φ
      simp
    · exact χ.ker.one_mem
    · have h1 : RU E n k φ = φ := hk.1
      have h3 : χ k = 1 := hk.2
      change RU E n k (mulCh χ φ) = mulCh χ φ
      rw [RU_mulCh, h1, h3]; simp
  · haveI := h.kfin
    refine Submodule.finiteDimensional_of_le (S₂ := (Submodule.span ℂ (Set.range fun k : infU E n => RU E n k φ)).map
      (mulCh χ).toLinearMap) (Submodule.span_le.2 ?_)
    rintro _ ⟨k, rfl⟩
    change RU E n k (mulCh χ φ) ∈ _
    rw [RU_mulCh]
    exact Submodule.smul_mem _ _ (Submodule.mem_map_of_mem (Submodule.subset_span ⟨k, rfl⟩))
end

/- English proof (translation)
Introduce `E _ _ _ n χ ho hr σ hσ`. Use `⟨σ.comap (mulCh χ).symm.toLinearMap, ⟨fun φ hφ => ?_, fun x φ hφ => ?_, fun e => ?_, fun W hW hs => ?_⟩, fun w hw ⟨φ, hφ, h0, hf⟩ => ?_, fun Gv H M _ _ _ p ρ η hη => and_congr (irr_tw ρ η) ⟨?_, ?_⟩⟩` and prove the remaining obligations. Take `⟨ψ, rfl⟩` from `(mulCh χ).surjective φ`. Conclude with `form_mulCh χ ho hr (hσ.aut ψ (by simpa using hφ))`. Take `⟨ψ, rfl⟩` from `(mulCh χ).surjective φ`.

Rewrite using `[RU_mulCh]`. Use `Submodule.smul_mem _ _ ?_` and prove the remaining obligations. Simplify `hφ)` using `using hσ.stable x ψ (by simpa`. Use `hσ.ne_bot (eq_bot_iff.2 fun φ hφ => ?_)` and prove the remaining obligations. Establish `: mulCh χ φ ∈ σ.comap (mulCh χ).symm.toLinearMap` using `by simpa using hφ`.

Rewrite `this` using `[e]`. Simplify using `using this`. Use `hσ.irred (W.comap (mulCh χ).toLinearMap) (fun φ hφ => by simpa using hW hφ) fun x φ hφ => by` as an intermediate fact. Use `hs x _ hφ` as an intermediate fact. Express the relevant statement in the definitionally equal form `RU E n x (mulCh χ φ) ∈ W at this`.

Rewrite `this` using `[RU_mulCh]`. Conclude with `(W.smul_mem_iff (Units.ne_zero (χ x))).1 this`. Use `this.imp (fun e => eq_bot_iff.2 fun φ hφ => ?_) fun e => le_antisymm hW fun φ hφ => ?_` and prove the remaining obligations. Take `⟨ψ, rfl⟩` from `(mulCh χ).surjective φ`. Establish `: ψ ∈ W.comap (mulCh χ).toLinearMap` using `hφ`.

Rewrite `this` using `[e]`. Simplify using `using this`. Take `⟨ψ, rfl⟩` from `(mulCh χ).surjective φ`. Establish `: ψ ∈ σ` using `by simpa using hφ`. Rewrite `this` using `[← e]`.

Conclude with `this`. Use `⟨mulCh χ φ, by simpa using hφ, by simpa using h0, fun x hx hk => ?_⟩` and prove the remaining obligations. Rewrite using `[RU_mulCh, hf x hx hk, hw x hx hk]`. Simplify using the standard rewrite rules. Introduce and unpack `⟨f, h0, h1, h2⟩`.

Use `⟨(mulCh χ).toLinearMap ∘ₗ f, fun e => h0 (LinearMap.ext fun v => ?_), fun v => by simpa using h1 v, fun x v => ?_⟩` and prove the remaining obligations. Simplify using `using LinearMap.congr_fun e v`. Express the relevant statement in the definitionally equal form `mulCh χ (f ((η (p x) : ℂ) • ρ (p x) v)) = RU E n x (mulCh χ (f v))`. Rewrite using `[RU_mulCh, map_smul, map_smul, h2, hη]`. Introduce and unpack `⟨f, h0, h1, h2⟩`.

Use `⟨(mulCh χ).symm.toLinearMap ∘ₗ f, fun e => h0 (LinearMap.ext fun v => ?_), fun v => h1 v, fun x v => ?_⟩` and prove the remaining obligations. Simplify using `using LinearMap.congr_fun e v`. Apply `(mulCh χ).injective` to reduce the goal to its premises. Apply `smul_right_injective _ (Units.ne_zero (χ x))` to reduce the goal to its premises. Use `h2 x v` as an intermediate fact.

Rewrite `this` using `[twRep_apply, map_smul, ← hη]`. Express the relevant statement in the definitionally equal form `(χ x : ℂ) • mulCh χ ((mulCh χ).symm (f (ρ (p x) v))) = (χ x : ℂ) • mulCh χ (RU E n x ((mulCh χ).symm (f v)))`. Rewrite using `[← RU_mulCh, LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply, this]`.
-/
theorem UpperTheory.exists_automorphicRep_twist_by_character :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (χ : UA E n →* ℂˣ), IsOpen (χ.ker : Set (UA E n)) → (∀ g ∈ ratU E n, χ g = 1) → ∀ σ : Submodule ℂ (UA E n → ℂ), IsAutRepU σ → ∃ σ' : Submodule ℂ (UA E n → ℂ), IsAutRepU σ' ∧ (∀ w : Plc E, (∀ g ∈ locU n w, cLoc w g ∈ GlobalTheory.LFun.KGL w n → χ g = 1) → IsUnramU σ w → IsUnramU σ' w) ∧ ∀ (Gv : Subgroup (UA E n)) (H M : Type) [Group H] [AddCommGroup M] [Module ℂ M] (p : Gv →* H) (ρ : Representation ℂ H M) (η : H →* ℂˣ), (∀ x : Gv, χ x = η (p x)) → (IsCompAlong σ Gv p ρ ↔ IsCompAlong σ' Gv p (twRep ρ η)) := by
  intro E _ _ _ n χ ho hr σ hσ
  refine ⟨σ.comap (mulCh χ).symm.toLinearMap, ⟨fun φ hφ => ?_, fun x φ hφ => ?_, fun e => ?_, fun W hW hs => ?_⟩,
    fun w hw ⟨φ, hφ, h0, hf⟩ => ?_, fun Gv H M _ _ _ p ρ η hη => and_congr (irr_tw ρ η) ⟨?_, ?_⟩⟩
  · obtain ⟨ψ, rfl⟩ := (mulCh χ).surjective φ
    exact form_mulCh χ ho hr (hσ.aut ψ (by simpa using hφ))
  · obtain ⟨ψ, rfl⟩ := (mulCh χ).surjective φ
    rw [RU_mulCh]
    refine Submodule.smul_mem _ _ ?_
    simpa using hσ.stable x ψ (by simpa using hφ)
  · refine hσ.ne_bot (eq_bot_iff.2 fun φ hφ => ?_)
    have : mulCh χ φ ∈ σ.comap (mulCh χ).symm.toLinearMap := by simpa using hφ
    rw [e] at this
    simpa using this
  · have := hσ.irred (W.comap (mulCh χ).toLinearMap) (fun φ hφ => by simpa using hW hφ) fun x φ hφ => by
      have := hs x _ hφ
      change RU E n x (mulCh χ φ) ∈ W at this
      rw [RU_mulCh] at this
      exact (W.smul_mem_iff (Units.ne_zero (χ x))).1 this
    refine this.imp (fun e => eq_bot_iff.2 fun φ hφ => ?_) fun e => le_antisymm hW fun φ hφ => ?_
    · obtain ⟨ψ, rfl⟩ := (mulCh χ).surjective φ
      have : ψ ∈ W.comap (mulCh χ).toLinearMap := hφ
      rw [e] at this
      simpa using this
    · obtain ⟨ψ, rfl⟩ := (mulCh χ).surjective φ
      have : ψ ∈ σ := by simpa using hφ
      rw [← e] at this
      exact this
  · refine ⟨mulCh χ φ, by simpa using hφ, by simpa using h0, fun x hx hk => ?_⟩
    rw [RU_mulCh, hf x hx hk, hw x hx hk]; simp
  · rintro ⟨f, h0, h1, h2⟩
    refine ⟨(mulCh χ).toLinearMap ∘ₗ f, fun e => h0 (LinearMap.ext fun v => ?_), fun v => by simpa using h1 v, fun x v => ?_⟩
    · simpa using LinearMap.congr_fun e v
    · change mulCh χ (f ((η (p x) : ℂ) • ρ (p x) v)) = RU E n x (mulCh χ (f v))
      rw [RU_mulCh, map_smul, map_smul, h2, hη]
  · rintro ⟨f, h0, h1, h2⟩
    refine ⟨(mulCh χ).symm.toLinearMap ∘ₗ f, fun e => h0 (LinearMap.ext fun v => ?_), fun v => h1 v, fun x v => ?_⟩
    · simpa using LinearMap.congr_fun e v
    · apply (mulCh χ).injective
      apply smul_right_injective _ (Units.ne_zero (χ x))
      have := h2 x v
      rw [twRep_apply, map_smul, ← hη] at this
      change (χ x : ℂ) • mulCh χ ((mulCh χ).symm (f (ρ (p x) v))) = (χ x : ℂ) • mulCh χ (RU E n x ((mulCh χ).symm (f v)))
      rw [← RU_mulCh, LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply, this]

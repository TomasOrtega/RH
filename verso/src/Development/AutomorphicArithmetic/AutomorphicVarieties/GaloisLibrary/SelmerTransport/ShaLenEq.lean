import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.ConjStableShaFam
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.ShaModel
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.InflAct
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.InflUnique

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.Base

set_option maxHeartbeats 800000 in
/- English proof (translation)
Introduce `k E Ω _ _ _ _ _ _ _ _ _ _ _ l _ D e`. Take `⟨Φ, hΦ⟩` from `shaModel k E Ω l D e`. Use `⟨Φ.length_eq, ?_⟩` and prove the remaining obligations. Introduce `_ τ σ hτσ s`. Establish `key : ∀ x : ↥(Sha D e), ∃ h : galoisActionOnCohomology D e τ (x : H1 (qzTw D e)) ∈ Sha D e, Φ ⟨_, h⟩ = shaRep (LDataCardLeFinrank.qzG k Ω l e) l (galOf k E Ω) σ (Φ x)`.

Introduce `x`. Use `set y := shaRep (LDataCardLeFinrank.qzG k Ω l e) l (galOf k E Ω) σ (Φ x) with hy`. Establish `h1 : Infl k D e (galoisActionOnCohomology D e τ (x : H1 (qzTw D e))) (y : H1U (LDataCardLeFinrank.qzG k Ω l e) (galOf k E Ω))` using `inflAct k E Ω l D e τ σ hτσ _ _ (hΦ x)`. Establish `h2` using `hΦ (Φ.symm y)`. Rewrite `h2` using `[LinearEquiv.apply_symm_apply]`.

Establish `heq : galoisActionOnCohomology D e τ (x : H1 (qzTw D e)) = ((Φ.symm y : ↥(Sha D e)) : H1 (qzTw D e))` using `((inflUnique k E Ω l D e).2 _ _ _ _ h1 h2).2 rfl`. Establish `hmem : galoisActionOnCohomology D e τ (x : H1 (qzTw D e)) ∈ Sha D e`. Rewrite using `[heq]`. Conclude with `(Φ.symm y).2`. Use `⟨hmem, ?_⟩` and prove the remaining obligations.

Establish `hsub : (⟨_, hmem⟩ : ↥(Sha D e)) = Φ.symm y` using `Subtype.ext heq`. Rewrite using `[hsub, LinearEquiv.apply_symm_apply]`. Establish `hle : Sha D e ⊓ Module.End.eigenspace (galoisActionOnCohomology D e τ) s ≤ Sha D e` using `inf_le_left`. Establish `hmap : Submodule.map (Φ : ↥(Sha D e) →ₗ[ℤ_[l]] ↥(ShaU (LDataCardLeFinrank.qzG k Ω l e) l (galOf k E Ω))) (Submodule.comap (Sha D e).subtype (Sha D e ⊓ Module.End.eigenspace (galoisActionOnCohomology D e τ) s)) = Module.End.eigenspace (shaRep (LDataCardLeFinrank.qzG k Ω l e) l (ga …`. Rewrite using `[Submodule.map_equiv_eq_comap_symm]`.

Use extensionality with `y`. Take `⟨h, hk⟩` from `key (Φ.symm y)`. Rewrite `hk` using `[LinearEquiv.apply_symm_apply]`. Rewrite using `[Module.End.mem_eigenspace_iff, Submodule.mem_comap, Submodule.mem_comap, Submodule.subtype_apply, Submodule.mem_inf, Module.End.mem_eigenspace_iff]`. Use `⟨fun hx => ?_, fun hx => ⟨(Φ.symm y).2, ?_⟩⟩` and prove the remaining obligations.

Establish `hs : (⟨_, h⟩ : ↥(Sha D e)) = s • Φ.symm y` using `Subtype.ext hx.2`. Use `hk.symm.trans ?_` and prove the remaining obligations. Rewrite using `[hs, map_smul, LinearEquiv.apply_symm_apply]`. Establish `hs : (⟨_, h⟩ : ↥(Sha D e)) = s • Φ.symm y`. Apply `Φ.injective` to reduce the goal to its premises.

Use `hk.trans (hx.trans ?_)` and prove the remaining obligations. Rewrite using `[map_smul, LinearEquiv.apply_symm_apply]`. Conclude with `congrArg Subtype.val hs`. Rewrite using `[← hmap]`. Conclude with `((Submodule.comapSubtypeEquivOfLe hle).symm.trans (Φ.submoduleMap _)).length_eq`.
-/
theorem UpperTheory.V.Base.shaLenEq :
    ∀ (k E Ω : Type) [Field k] [NumberField k] [Field E] [NumberField E] [Field Ω] [Algebra k E] [Algebra k Ω] [Algebra E Ω]
      [IsScalarTower k E Ω] [IsAlgClosure k Ω] [IsAlgClosure E Ω] (l : ℕ) [Fact l.Prime] (D : LData E Ω l) (e : ℤ),
      shaLen D e = Module.length ℤ_[l] (ShaU (LDataCardLeFinrank.qzG k Ω l e) l (galOf k E Ω)) ∧
      ∀ [Normal k E] (τ : E ≃+* E) (σ : G k Ω), IsLift τ σ.toRingEquiv → ∀ s : ℤ_[l],
        Module.length ℤ_[l] ↥(Sha D e ⊓ Module.End.eigenspace (galoisActionOnCohomology D e τ) s) =
          Module.length ℤ_[l] (Module.End.eigenspace (shaRep (LDataCardLeFinrank.qzG k Ω l e) l (galOf k E Ω) σ) s) := by
  intro k E Ω _ _ _ _ _ _ _ _ _ _ _ l _ D e
  obtain ⟨Φ, hΦ⟩ := shaModel k E Ω l D e
  refine ⟨Φ.length_eq, ?_⟩
  intro _ τ σ hτσ s
  have key : ∀ x : ↥(Sha D e), ∃ h : galoisActionOnCohomology D e τ (x : H1 (qzTw D e)) ∈ Sha D e,
      Φ ⟨_, h⟩ = shaRep (LDataCardLeFinrank.qzG k Ω l e) l (galOf k E Ω) σ (Φ x) := by
    intro x
    set y := shaRep (LDataCardLeFinrank.qzG k Ω l e) l (galOf k E Ω) σ (Φ x) with hy
    have h1 : Infl k D e (galoisActionOnCohomology D e τ (x : H1 (qzTw D e))) (y : H1U (LDataCardLeFinrank.qzG k Ω l e) (galOf k E Ω)) :=
      inflAct k E Ω l D e τ σ hτσ _ _ (hΦ x)
    have h2 := hΦ (Φ.symm y)
    rw [LinearEquiv.apply_symm_apply] at h2
    have heq : galoisActionOnCohomology D e τ (x : H1 (qzTw D e)) = ((Φ.symm y : ↥(Sha D e)) : H1 (qzTw D e)) :=
      ((inflUnique k E Ω l D e).2 _ _ _ _ h1 h2).2 rfl
    have hmem : galoisActionOnCohomology D e τ (x : H1 (qzTw D e)) ∈ Sha D e := by
      rw [heq]
      exact (Φ.symm y).2
    refine ⟨hmem, ?_⟩
    have hsub : (⟨_, hmem⟩ : ↥(Sha D e)) = Φ.symm y := Subtype.ext heq
    rw [hsub, LinearEquiv.apply_symm_apply]
  have hle : Sha D e ⊓ Module.End.eigenspace (galoisActionOnCohomology D e τ) s ≤ Sha D e := inf_le_left
  have hmap : Submodule.map (Φ : ↥(Sha D e) →ₗ[ℤ_[l]] ↥(ShaU (LDataCardLeFinrank.qzG k Ω l e) l (galOf k E Ω)))
      (Submodule.comap (Sha D e).subtype (Sha D e ⊓ Module.End.eigenspace (galoisActionOnCohomology D e τ) s)) =
      Module.End.eigenspace (shaRep (LDataCardLeFinrank.qzG k Ω l e) l (galOf k E Ω) σ) s := by
    rw [Submodule.map_equiv_eq_comap_symm]
    ext y
    obtain ⟨h, hk⟩ := key (Φ.symm y)
    rw [LinearEquiv.apply_symm_apply] at hk
    rw [Module.End.mem_eigenspace_iff, Submodule.mem_comap, Submodule.mem_comap, Submodule.subtype_apply,
      Submodule.mem_inf, Module.End.mem_eigenspace_iff]
    refine ⟨fun hx => ?_, fun hx => ⟨(Φ.symm y).2, ?_⟩⟩
    · have hs : (⟨_, h⟩ : ↥(Sha D e)) = s • Φ.symm y := Subtype.ext hx.2
      refine hk.symm.trans ?_
      rw [hs, map_smul, LinearEquiv.apply_symm_apply]
    · have hs : (⟨_, h⟩ : ↥(Sha D e)) = s • Φ.symm y := by
        apply Φ.injective
        refine hk.trans (hx.trans ?_)
        rw [map_smul, LinearEquiv.apply_symm_apply]
      exact congrArg Subtype.val hs
  rw [← hmap]
  exact ((Submodule.comapSubtypeEquivOfLe hle).symm.trans (Φ.submoduleMap _)).length_eq

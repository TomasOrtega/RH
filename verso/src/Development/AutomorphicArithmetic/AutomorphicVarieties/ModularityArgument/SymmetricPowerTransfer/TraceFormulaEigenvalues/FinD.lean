import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.TraceFormulaEigenvalues.IsGenEig

namespace UpperTheory.V.Z.Sym.Tf

/- English proof (translation)
Use `set L : Subgroup Γ := Subgroup.comap B.ι (Subgroup.map (MulEquiv.toMonoidHom (MulAut.conj g')) B.U) with hL`. Use `haveI hfi : (B.Γ₀.subgroupOf L).FiniteIndex := ⟨hB.stab g'⟩`. Use `haveI : Finite (L ⧸ B.Γ₀.subgroupOf L) := Subgroup.finite_quotient_of_finiteIndex`. Establish `hcomm' : ∀ γ, s.θ.symm (B.ι γ) = B.ι (s.θΓ.symm γ)`. Introduce `γ`.

Apply `s.θ.injective` to reduce the goal to its premises. Rewrite using `[MulEquiv.apply_symm_apply, s.comm, MulEquiv.apply_symm_apply]`. Set `T : Set Γ` to `{δ | f (g⁻¹ * B.ι δ * s.θ g') ≠ 0}`. Set `key : Γ → G ⧸ B.U` to `fun δ => (QuotientGroup.mk (s.θ.symm (g⁻¹ * B.ι δ * s.θ g')) : G ⧸ B.U)`. Establish `hkey : ∀ δ ∈ T, key δ ∈ {x : G ⧸ B.U | f (s.θ (Quotient.out x)) ≠ 0}`.

Introduce `δ hδ`. Take `⟨u, hu⟩` from `QuotientGroup.mk_out_eq_mul B.U (s.θ.symm (g⁻¹ * B.ι δ * s.θ g'))`. Use `show f (s.θ (Quotient.out (key δ))) ≠ 0`. Establish `hu' : Quotient.out (key δ) = s.θ.symm (g⁻¹ * B.ι δ * s.θ g') * u` using `hu`. Rewrite using `[hu', map_mul, MulEquiv.apply_symm_apply, hf.right]`.

Conclude with `mul_ne_zero (Units.ne_zero _) hδ`. Establish `himg : ((QuotientGroup.mk : Γ → Γ ⧸ B.Γ₀) '' T).Finite`. Establish `hsub : T ⊆ ⋃ c ∈ {x : G ⧸ B.U | f (s.θ (Quotient.out x)) ≠ 0}, {δ | key δ = c}` using `fun δ hδ => Set.mem_biUnion (hkey δ hδ) rfl`. Use `Set.Finite.subset ?_ (Set.image_mono hsub)` and prove the remaining obligations. Rewrite using `[Set.image_iUnion₂]`.

Use `hf.fin.biUnion fun c _ => ?_` and prove the remaining obligations. Distinguish the cases in `hne : ∃ δ₁, key δ₁ = c`. Take `⟨δ₁, hδ₁⟩` from `hne`. Set `φ : L ⧸ B.Γ₀.subgroupOf L → Γ ⧸ B.Γ₀` to `fun q => ((δ₁ * s.θΓ ((Quotient.out q : L) : Γ) : Γ) : Γ ⧸ B.Γ₀)`. Use `(Set.finite_range φ).subset ?_` and prove the remaining obligations.

Introduce and unpack `_ ⟨δ, hδ, rfl⟩`. Establish `hab` using `QuotientGroup.eq.mp (hδ₁.trans hδ.symm)`. Establish `hl : s.θΓ.symm (δ₁⁻¹ * δ) ∈ L`. Rewrite using `[hL, Subgroup.mem_comap, Subgroup.mem_map]`. Use `⟨_, hab, ?_⟩` and prove the remaining obligations.

Rewrite using `[← hcomm']`. Simplify using `only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, map_mul, map_inv, MulEquiv.symm_apply_apply, mul_inv_rev, inv_inv]`. Use `group`. Take `⟨z, hz⟩` from `QuotientGroup.mk_out_eq_mul (B.Γ₀.subgroupOf L) (⟨s.θΓ.symm (δ₁⁻¹ * δ), hl⟩ : L)`. Use `⟨(QuotientGroup.mk (⟨s.θΓ.symm (δ₁⁻¹ * δ), hl⟩ : L) : L ⧸ B.Γ₀.subgroupOf L), ?_⟩` and prove the remaining obligations.

Establish `hz0 : ((z : L) : Γ) ∈ B.Γ₀` using `Subgroup.mem_subgroupOf.mp z.2`. Use `show ((δ₁ * s.θΓ ((Quotient.out _ : L) : Γ) : Γ) : Γ ⧸ B.Γ₀) = _`. Rewrite using `[show Quotient.out (QuotientGroup.mk (⟨s.θΓ.symm (δ₁⁻¹ * δ), hl⟩ : L) : L ⧸ B.Γ₀.subgroupOf L) = _ from hz]`. Rewrite using `[Subgroup.coe_mul, map_mul, MulEquiv.apply_symm_apply, s.fix _ hz0, ← mul_assoc, mul_inv_cancel_left]`. Apply `QuotientGroup.eq.mpr` to reduce the goal to its premises.

Simplify using `using B.Γ₀.inv_mem hz0`. Use `Set.finite_empty.subset ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨δ, hδ, rfl⟩`. Conclude with `(hne ⟨δ, hδ⟩).elim`. Use `⟨himg.toFinset.image (fun q => Quotient.out q), fun δ hδ => ?_⟩` and prove the remaining obligations.

Use `⟨Quotient.out ((δ : Γ ⧸ B.Γ₀)), Finset.mem_image.mpr ⟨_, himg.mem_toFinset.mpr ⟨δ, hδ, rfl⟩, rfl⟩, (Quotient.out ((δ : Γ ⧸ B.Γ₀)))⁻¹ * δ, ?_, by group⟩` and prove the remaining obligations. Conclude with `QuotientGroup.eq.mp (QuotientGroup.out_eq' _)`.
-/
theorem finD {Γ G V : Type} [Group Γ] [Group G] [AddCommGroup V] [Module ℂ V] (B : Base Γ G V) (hB : B.Fin) (s : B.Tw)
    (f : G → ℂ) (hf : s.IsTest f) (g g' : G) :
    ∃ D : Finset Γ, ∀ δ, f (g⁻¹ * B.ι δ * s.θ g') ≠ 0 → ∃ d ∈ D, ∃ z ∈ B.Γ₀, δ = d * z := by
  classical
  set L : Subgroup Γ :=
    Subgroup.comap B.ι (Subgroup.map (MulEquiv.toMonoidHom (MulAut.conj g')) B.U) with hL
  haveI hfi : (B.Γ₀.subgroupOf L).FiniteIndex := ⟨hB.stab g'⟩
  haveI : Finite (L ⧸ B.Γ₀.subgroupOf L) := Subgroup.finite_quotient_of_finiteIndex
  have hcomm' : ∀ γ, s.θ.symm (B.ι γ) = B.ι (s.θΓ.symm γ) := by
    intro γ
    apply s.θ.injective
    rw [MulEquiv.apply_symm_apply, s.comm, MulEquiv.apply_symm_apply]
  let T : Set Γ := {δ | f (g⁻¹ * B.ι δ * s.θ g') ≠ 0}
  let key : Γ → G ⧸ B.U := fun δ => (QuotientGroup.mk (s.θ.symm (g⁻¹ * B.ι δ * s.θ g')) : G ⧸ B.U)
  have hkey : ∀ δ ∈ T, key δ ∈ {x : G ⧸ B.U | f (s.θ (Quotient.out x)) ≠ 0} := by
    intro δ hδ
    obtain ⟨u, hu⟩ := QuotientGroup.mk_out_eq_mul B.U (s.θ.symm (g⁻¹ * B.ι δ * s.θ g'))
    show f (s.θ (Quotient.out (key δ))) ≠ 0
    have hu' : Quotient.out (key δ) = s.θ.symm (g⁻¹ * B.ι δ * s.θ g') * u := hu
    rw [hu', map_mul, MulEquiv.apply_symm_apply, hf.right]
    exact mul_ne_zero (Units.ne_zero _) hδ
  have himg : ((QuotientGroup.mk : Γ → Γ ⧸ B.Γ₀) '' T).Finite := by
    have hsub : T ⊆ ⋃ c ∈ {x : G ⧸ B.U | f (s.θ (Quotient.out x)) ≠ 0}, {δ | key δ = c} :=
      fun δ hδ => Set.mem_biUnion (hkey δ hδ) rfl
    refine Set.Finite.subset ?_ (Set.image_mono hsub)
    rw [Set.image_iUnion₂]
    refine hf.fin.biUnion fun c _ => ?_
    by_cases hne : ∃ δ₁, key δ₁ = c
    · obtain ⟨δ₁, hδ₁⟩ := hne
      let φ : L ⧸ B.Γ₀.subgroupOf L → Γ ⧸ B.Γ₀ :=
        fun q => ((δ₁ * s.θΓ ((Quotient.out q : L) : Γ) : Γ) : Γ ⧸ B.Γ₀)
      refine (Set.finite_range φ).subset ?_
      rintro _ ⟨δ, hδ, rfl⟩
      have hab := QuotientGroup.eq.mp (hδ₁.trans hδ.symm)
      have hl : s.θΓ.symm (δ₁⁻¹ * δ) ∈ L := by
        rw [hL, Subgroup.mem_comap, Subgroup.mem_map]
        refine ⟨_, hab, ?_⟩
        rw [← hcomm']
        simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, map_mul, map_inv,
          MulEquiv.symm_apply_apply, mul_inv_rev, inv_inv]
        group
      obtain ⟨z, hz⟩ := QuotientGroup.mk_out_eq_mul (B.Γ₀.subgroupOf L)
        (⟨s.θΓ.symm (δ₁⁻¹ * δ), hl⟩ : L)
      refine ⟨(QuotientGroup.mk (⟨s.θΓ.symm (δ₁⁻¹ * δ), hl⟩ : L) : L ⧸ B.Γ₀.subgroupOf L), ?_⟩
      have hz0 : ((z : L) : Γ) ∈ B.Γ₀ := Subgroup.mem_subgroupOf.mp z.2
      show ((δ₁ * s.θΓ ((Quotient.out _ : L) : Γ) : Γ) : Γ ⧸ B.Γ₀) = _
      rw [show Quotient.out (QuotientGroup.mk (⟨s.θΓ.symm (δ₁⁻¹ * δ), hl⟩ : L) :
          L ⧸ B.Γ₀.subgroupOf L) = _ from hz]
      rw [Subgroup.coe_mul, map_mul, MulEquiv.apply_symm_apply, s.fix _ hz0, ← mul_assoc,
        mul_inv_cancel_left]
      apply QuotientGroup.eq.mpr
      simpa using B.Γ₀.inv_mem hz0
    · refine Set.finite_empty.subset ?_
      rintro _ ⟨δ, hδ, rfl⟩
      exact (hne ⟨δ, hδ⟩).elim
  refine ⟨himg.toFinset.image (fun q => Quotient.out q), fun δ hδ => ?_⟩
  refine ⟨Quotient.out ((δ : Γ ⧸ B.Γ₀)), Finset.mem_image.mpr ⟨_, himg.mem_toFinset.mpr ⟨δ, hδ, rfl⟩, rfl⟩,
    (Quotient.out ((δ : Γ ⧸ B.Γ₀)))⁻¹ * δ, ?_, by group⟩
  exact QuotientGroup.eq.mp (QuotientGroup.out_eq' _)

end UpperTheory.V.Z.Sym.Tf

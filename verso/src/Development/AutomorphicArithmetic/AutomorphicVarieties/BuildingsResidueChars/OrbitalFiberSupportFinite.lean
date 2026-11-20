import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GlobalUnitaryForms.FibAbs

/- English proof (translation)
Introduce `Γ G V _ _ _ _ B hB h0 f hf g`. Establish `hK : Finite ((B.U.map (MulAut.conj g).toMonoidHom).comap B.ι)`. Establish `h` using `hB.stab g`. Rewrite `h` using `[h0, Subgroup.relIndex_bot_left]`. Conclude with `Nat.finite_of_card_ne_zero h`.

Establish `hKs : (((B.U.map (MulAut.conj g).toMonoidHom).comap B.ι : Subgroup Γ) : Set Γ).Finite` using `Set.toFinite _`. Establish `hfib : ∀ x : G ⧸ B.U, ((fun γ => ((g⁻¹ * B.ι γ * g : G) : G ⧸ B.U)) ⁻¹' {x}).Finite`. Introduce `x`. Break down `Set.eq_empty_or_nonempty ((fun γ => ((g⁻¹ * B.ι γ * g : G) : G ⧸ B.U)) ⁻¹' {x}) with he | ⟨γ₀, h₀⟩` into its components or cases. Rewrite using `[he]`.

Conclude with `Set.finite_empty`. Use `(hKs.image (fun k => γ₀ * k)).subset fun γ hγ => ⟨γ₀⁻¹ * γ, ?_, by simp⟩` and prove the remaining obligations. Establish `e : ((g⁻¹ * B.ι γ₀ * g : G) : G ⧸ B.U) = ((g⁻¹ * B.ι γ * g : G) : G ⧸ B.U)` using `(Set.mem_singleton_iff.1 h₀).trans (Set.mem_singleton_iff.1 hγ).symm`. Use `⟨_, QuotientGroup.eq.1 e, ?_⟩` and prove the remaining obligations. Simplify using `[mul_assoc]`.

Use `(hf.fin.preimage' (f := fun γ => ((g⁻¹ * B.ι γ * g : G) : G ⧸ B.U)) fun x _ => hfib x).subset ?_` and prove the remaining obligations. Introduce `γ hγ h`. Apply `hγ` to reduce the goal to its premises. Take `⟨u, hu⟩` from `QuotientGroup.mk_out_eq_mul B.U (g⁻¹ * B.ι γ * g)`. Establish `hr` using `hf.right u (g⁻¹ * B.ι γ * g)`.

Express the relevant statement in the definitionally equal form `f (((g⁻¹ * B.ι γ * g : G) : G ⧸ B.U).out) = 0 at h`. Express the relevant statement in the definitionally equal form `f (g⁻¹ * B.ι γ * g * u) = _ at hr`. Rewrite `h` using `[hu, hr]`. Conclude with `(mul_eq_zero.1 h).resolve_left (Units.ne_zero _)`.
-/
theorem UpperTheory.orbitalFiber_support_finite :
    UpperTheory.V.Z.Sym.Glob.Fib.SuppFin := by
  intro Γ G V _ _ _ _ B hB h0 f hf g
  have hK : Finite ((B.U.map (MulAut.conj g).toMonoidHom).comap B.ι) := by
    have h := hB.stab g
    rw [h0, Subgroup.relIndex_bot_left] at h
    exact Nat.finite_of_card_ne_zero h
  have hKs : (((B.U.map (MulAut.conj g).toMonoidHom).comap B.ι : Subgroup Γ) : Set Γ).Finite := Set.toFinite _
  have hfib : ∀ x : G ⧸ B.U, ((fun γ => ((g⁻¹ * B.ι γ * g : G) : G ⧸ B.U)) ⁻¹' {x}).Finite := by
    intro x
    rcases Set.eq_empty_or_nonempty ((fun γ => ((g⁻¹ * B.ι γ * g : G) : G ⧸ B.U)) ⁻¹' {x}) with he | ⟨γ₀, h₀⟩
    · rw [he]; exact Set.finite_empty
    · refine (hKs.image (fun k => γ₀ * k)).subset fun γ hγ => ⟨γ₀⁻¹ * γ, ?_, by simp⟩
      have e : ((g⁻¹ * B.ι γ₀ * g : G) : G ⧸ B.U) = ((g⁻¹ * B.ι γ * g : G) : G ⧸ B.U) :=
        (Set.mem_singleton_iff.1 h₀).trans (Set.mem_singleton_iff.1 hγ).symm
      refine ⟨_, QuotientGroup.eq.1 e, ?_⟩
      simp [mul_assoc]
  refine (hf.fin.preimage' (f := fun γ => ((g⁻¹ * B.ι γ * g : G) : G ⧸ B.U)) fun x _ => hfib x).subset ?_
  intro γ hγ h
  apply hγ
  obtain ⟨u, hu⟩ := QuotientGroup.mk_out_eq_mul B.U (g⁻¹ * B.ι γ * g)
  have hr := hf.right u (g⁻¹ * B.ι γ * g)
  change f (((g⁻¹ * B.ι γ * g : G) : G ⧸ B.U).out) = 0 at h
  change f (g⁻¹ * B.ι γ * g * u) = _ at hr
  rw [hu, hr] at h
  exact (mul_eq_zero.1 h).resolve_left (Units.ne_zero _)

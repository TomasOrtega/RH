import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GlobalUnitaryForms.FibAbs

namespace UpperTheory

/- English proof (translation)
Introduce `H G _ _ S U U' ι x hS hidx hfin`. Set `ψ : H →* G` to `(MulAut.conj x⁻¹).toMonoidHom.comp (S.subtype.comp ι)`. Establish `hψ : ∀ h, ψ h = x⁻¹ * ι h * x` using `fun h => by simp [ψ]`. Establish `hB : (U' ⊓ S).comap ψ = U'.comap ψ`. Use extensionality with `h`.

Simplify using `only [Subgroup.mem_comap, Subgroup.mem_inf, and_iff_left_iff_imp]`. Introduce `_`. Rewrite using `[hψ]`. Simplify using `using hS.conj_mem _ (ι h).2 x⁻¹`. Establish `h1 : (U.comap ψ).relIndex (U'.comap ψ) ≠ 0`.

Rewrite using `[← hB]`. Conclude with `Subgroup.relIndex_comap_ne_zero ψ hidx`. Establish `hA : Finite (U.comap ψ)`. Establish `: ((U.comap ψ : Subgroup H) : Set H).Finite`. Use `hfin using 1` and compare the differences between its conclusion and the goal.

Use extensionality with `h`. Simplify using `[hψ]`. Conclude with `this.to_subtype`. Establish `hA' : Finite ((U.comap ψ).subgroupOf (U'.comap ψ))` using `Finite.of_injective (fun a => (⟨a.1.1, a.2⟩ : U.comap ψ)) (fun a b hab => by`. Apply `Subtype.ext` to reduce the goal to its premises.

Apply `Subtype.ext` to reduce the goal to its premises. Conclude with `congrArg (fun z : U.comap ψ => (z : H)) hab)`. Establish `hq : Finite ((U'.comap ψ) ⧸ (U.comap ψ).subgroupOf (U'.comap ψ))` using `Nat.finite_of_card_ne_zero h1`. Establish `hfB : Finite (U'.comap ψ)` using `Finite.of_equiv _ (Subgroup.groupEquivQuotientProdSubgroup (s := (U.comap ψ).subgroupOf (U'.comap ψ))).symm`. Establish `: ((U'.comap ψ : Subgroup H) : Set H).Finite` using `Set.toFinite _`.

Use `this using 1` and compare the differences between its conclusion and the goal. Use extensionality with `h`. Simplify using `[hψ]`.
-/
theorem orbitalFiber_stabilizer_finite : UpperTheory.V.Z.Sym.Glob.Fib.StabFin := by
  intro H G _ _ S U U' ι x hS hidx hfin
  let ψ : H →* G := (MulAut.conj x⁻¹).toMonoidHom.comp (S.subtype.comp ι)
  have hψ : ∀ h, ψ h = x⁻¹ * ι h * x := fun h => by simp [ψ]
  have hB : (U' ⊓ S).comap ψ = U'.comap ψ := by
    ext h
    simp only [Subgroup.mem_comap, Subgroup.mem_inf, and_iff_left_iff_imp]
    intro _
    rw [hψ]
    simpa using hS.conj_mem _ (ι h).2 x⁻¹
  have h1 : (U.comap ψ).relIndex (U'.comap ψ) ≠ 0 := by
    rw [← hB]
    exact Subgroup.relIndex_comap_ne_zero ψ hidx
  have hA : Finite (U.comap ψ) := by
    have : ((U.comap ψ : Subgroup H) : Set H).Finite := by
      convert hfin using 1
      ext h
      simp [hψ]
    exact this.to_subtype
  have hA' : Finite ((U.comap ψ).subgroupOf (U'.comap ψ)) :=
    Finite.of_injective (fun a => (⟨a.1.1, a.2⟩ : U.comap ψ)) (fun a b hab => by
      apply Subtype.ext
      apply Subtype.ext
      exact congrArg (fun z : U.comap ψ => (z : H)) hab)
  have hq : Finite ((U'.comap ψ) ⧸ (U.comap ψ).subgroupOf (U'.comap ψ)) :=
    Nat.finite_of_card_ne_zero h1
  have hfB : Finite (U'.comap ψ) :=
    Finite.of_equiv _ (Subgroup.groupEquivQuotientProdSubgroup
      (s := (U.comap ψ).subgroupOf (U'.comap ψ))).symm
  have : ((U'.comap ψ : Subgroup H) : Set H).Finite := Set.toFinite _
  convert this using 1
  ext h
  simp [hψ]

end UpperTheory

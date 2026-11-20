import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.NewformCoefficients.CuspCritAlt

open UpperTheory.V in
/- English proof (translation)
Introduce `F _ _ _ a φ hφ hmem`. Take `⟨s, hs⟩` from `Submodule.mem_iSup_iff_exists_finset.1 hmem`. Establish `hst : ∀ t : Finset (TR.CuspSub F a), TR.IsStable (⨆ π ∈ t, π.V)`. Introduce `t o x hx`. Establish `: (⨆ π ∈ t, π.V) ≤ (⨆ π ∈ t, π.V).comap (TR.act o)` using `iSup₂_le fun π hπ y hy => (le_iSup₂ (f := fun (π : TR.CuspSub F a) (_ : π ∈ t) => π.V) π hπ) (π.stable o y hy)`.

Conclude with `this hx`. Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty => exact absurd (by simpa using hs) hφ`. Consider the case `insert π t _ ih`. Distinguish the cases in `ht : φ ∈ ⨆ π ∈ t, π.V`.

Conclude with `ih ht`. Rewrite `hs` using `[Finset.iSup_insert]`. Take `⟨ψ, hψ, w, hw, e⟩` from `Submodule.mem_sup.1 hs`. Break down `π.irred (π.V ⊓ ⨆ π ∈ t, π.V) inf_le_left (fun o x hx => ⟨π.stable o x hx.1, hst t o x hx.2⟩) with h | h` into its components or cases. Use `⟨π, ⟨ψ, hψ⟩, _, ?_, hst t, disjoint_iff.2 h, ?_⟩` and prove the remaining obligations.

Introduce `h0`. Establish `h1 : ψ = 0` using `congrArg Subtype.val h0`. Rewrite `e` using `[h1, zero_add]`. Conclude with `ht (e ▸ hw)`. Rewrite using `[← e]`.

Simplify using `using hw`. Conclude with `absurd (e ▸ Submodule.add_mem _ (inf_eq_left.1 h hψ) hw) ht`.
-/
theorem UpperTheory.V.Af.Nf.split :
    UpperTheory.V.Af.Nf.Split := by
  intro F _ _ _ a φ hφ hmem
  classical
  obtain ⟨s, hs⟩ := Submodule.mem_iSup_iff_exists_finset.1 hmem
  have hst : ∀ t : Finset (TR.CuspSub F a), TR.IsStable (⨆ π ∈ t, π.V) := by
    intro t o x hx
    have : (⨆ π ∈ t, π.V) ≤ (⨆ π ∈ t, π.V).comap (TR.act o) :=
      iSup₂_le fun π hπ y hy =>
        (le_iSup₂ (f := fun (π : TR.CuspSub F a) (_ : π ∈ t) => π.V) π hπ) (π.stable o y hy)
    exact this hx
  induction s using Finset.induction_on with
  | empty => exact absurd (by simpa using hs) hφ
  | insert π t _ ih =>
    by_cases ht : φ ∈ ⨆ π ∈ t, π.V
    · exact ih ht
    rw [Finset.iSup_insert] at hs
    obtain ⟨ψ, hψ, w, hw, e⟩ := Submodule.mem_sup.1 hs
    rcases π.irred (π.V ⊓ ⨆ π ∈ t, π.V) inf_le_left
      (fun o x hx => ⟨π.stable o x hx.1, hst t o x hx.2⟩) with h | h
    · refine ⟨π, ⟨ψ, hψ⟩, _, ?_, hst t, disjoint_iff.2 h, ?_⟩
      · intro h0
        have h1 : ψ = 0 := congrArg Subtype.val h0
        rw [h1, zero_add] at e
        exact ht (e ▸ hw)
      · rw [← e]
        simpa using hw
    · exact absurd (e ▸ Submodule.add_mem _ (inf_eq_left.1 h hψ) hw) ht

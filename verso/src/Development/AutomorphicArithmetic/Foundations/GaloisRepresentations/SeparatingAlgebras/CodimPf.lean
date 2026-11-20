import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SeparatingAlgebras.GroupDetAlt

namespace UpperTheory.Gal.Gen

/- English proof (translation)
Introduce `k V M _ _ _ _ _ _ Ψ A B _ h`. Set `f : V →ₗ[k] M ⧸ A` to `A.mkQ ∘ₗ Ψ`. Establish `hker : LinearMap.ker f = A.comap Ψ`. Use extensionality with `v`. Simplify using `[f, Submodule.Quotient.mk_eq_zero]`.

Establish `hrange : LinearMap.range f ≤ B.map A.mkQ`. Introduce and unpack `_ ⟨v, rfl⟩`. Take `⟨a, ha, b, hb, hab⟩` from `Submodule.mem_sup.mp (h v)`. Use `⟨b, hb, ?_⟩` and prove the remaining obligations. Establish `hz : A.mkQ a = 0` using `by simpa [Submodule.Quotient.mk_eq_zero] using ha`.

Simplify using `only [f, LinearMap.comp_apply, ← hab, map_add, hz, zero_add]`. Use `haveI : FiniteDimensional k (B.map A.mkQ) := Module.Finite.map B A.mkQ`. Establish `h1 : Module.finrank k (LinearMap.range f) ≤ Module.finrank k (B.map A.mkQ)` using `Submodule.finrank_mono hrange`. Establish `h2 : Module.finrank k (B.map A.mkQ) ≤ Module.finrank k B` using `Submodule.finrank_map_le A.mkQ B`. Establish `h3` using `LinearMap.finrank_range_add_finrank_ker f`.

Rewrite `h3` using `[hker]`. Use linear arithmetic over natural numbers and integers.
-/
theorem codim_pf : Codim := by
  intro k V M _ _ _ _ _ _ Ψ A B _ h
  let f : V →ₗ[k] M ⧸ A := A.mkQ ∘ₗ Ψ
  have hker : LinearMap.ker f = A.comap Ψ := by
    ext v
    simp [f, Submodule.Quotient.mk_eq_zero]
  have hrange : LinearMap.range f ≤ B.map A.mkQ := by
    rintro _ ⟨v, rfl⟩
    obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.mp (h v)
    refine ⟨b, hb, ?_⟩
    have hz : A.mkQ a = 0 := by simpa [Submodule.Quotient.mk_eq_zero] using ha
    simp only [f, LinearMap.comp_apply, ← hab, map_add, hz, zero_add]
  haveI : FiniteDimensional k (B.map A.mkQ) :=
    Module.Finite.map B A.mkQ
  have h1 : Module.finrank k (LinearMap.range f) ≤ Module.finrank k (B.map A.mkQ) :=
    Submodule.finrank_mono hrange
  have h2 : Module.finrank k (B.map A.mkQ) ≤ Module.finrank k B :=
    Submodule.finrank_map_le A.mkQ B
  have h3 := LinearMap.finrank_range_add_finrank_ker f
  rw [hker] at h3
  omega

end UpperTheory.Gal.Gen

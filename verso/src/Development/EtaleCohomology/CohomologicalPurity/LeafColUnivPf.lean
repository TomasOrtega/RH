import Development.EtaleCohomology.CohomologicalPurity.LeafHensCutDef

noncomputable section
open CategoryTheory Limits

namespace LateralTheory.CohomologicalPurity.Hz

/- English proof (translation)
Introduce `A _ I Δ c hc η hη B _ J hJ ψ hψ`. Establish `hu : ∀ j, ∃! χ : Δ.D.obj j →+* B, χ.comp (Δ.s j) = ψ` using `fun j => (Δ.good j).univ B J hJ ψ hψ`. Use `choose χ hχ hχu using hu`. Establish `hnat : ∀ {j k : Δ.J} (e : j ⟶ k), (χ k).comp (Δ.D.map e).hom = χ j` using `fun {j k} e => by`. Apply `hχu j` to reduce the goal to its premises.

Rewrite using `[RingHom.comp_assoc, Δ.nat e, hχ k]`. Set `cB : Cocone Δ.D` to `⟨CommRingCat.of B, ⟨fun j => CommRingCat.ofHom (χ j), fun j k e => by`. Apply `CommRingCat.hom_ext` to reduce the goal to its premises. Simplify using `using hnat e⟩⟩`. Set `d` to `hc.desc cB`.

Establish `hfac : ∀ j, d.hom.comp (Δ.leg c j) = χ j` using `fun j => by`. Use `hc.fac cB j` as an intermediate fact. Conclude with `congrArg CommRingCat.Hom.hom this`. Take `⟨j₀⟩ : Nonempty Δ.J` from `IsFiltered.nonempty`. Use `⟨d.hom, ?_, fun χ' h' => ?_⟩` and prove the remaining obligations.

Use `show d.hom.comp η = ψ`. Rewrite using `[← hη j₀, ← RingHom.comp_assoc, hfac, hχ]`. Establish `h2 : ∀ j, χ'.comp (Δ.leg c j) = χ j` using `fun j => by`. Apply `hχu j` to reduce the goal to its premises. Rewrite using `[RingHom.comp_assoc, hη j, h']`.

Establish `: CommRingCat.ofHom χ' = d` using `hc.hom_ext fun j => by`. Apply `CommRingCat.hom_ext` to reduce the goal to its premises. Express the relevant statement in the definitionally equal form `χ'.comp (Δ.leg c j) = d.hom.comp (Δ.leg c j)`. Rewrite using `[h2, hfac]`. Rewrite using `[← this]`.

Both sides reduce to the same expression.
-/
theorem LeafColUniv_of : LeafColUniv := by
  intro A _ I Δ c hc η hη B _ J hJ ψ hψ
  have hu : ∀ j, ∃! χ : Δ.D.obj j →+* B, χ.comp (Δ.s j) = ψ := fun j => (Δ.good j).univ B J hJ ψ hψ
  choose χ hχ hχu using hu
  have hnat : ∀ {j k : Δ.J} (e : j ⟶ k), (χ k).comp (Δ.D.map e).hom = χ j := fun {j k} e => by
    apply hχu j
    rw [RingHom.comp_assoc, Δ.nat e, hχ k]
  let cB : Cocone Δ.D := ⟨CommRingCat.of B, ⟨fun j => CommRingCat.ofHom (χ j), fun j k e => by
    apply CommRingCat.hom_ext
    simpa using hnat e⟩⟩
  let d := hc.desc cB
  have hfac : ∀ j, d.hom.comp (Δ.leg c j) = χ j := fun j => by
    have := hc.fac cB j
    exact congrArg CommRingCat.Hom.hom this
  obtain ⟨j₀⟩ : Nonempty Δ.J := IsFiltered.nonempty
  refine ⟨d.hom, ?_, fun χ' h' => ?_⟩
  · show d.hom.comp η = ψ
    rw [← hη j₀, ← RingHom.comp_assoc, hfac, hχ]
  · have h2 : ∀ j, χ'.comp (Δ.leg c j) = χ j := fun j => by
      apply hχu j
      rw [RingHom.comp_assoc, hη j, h']
    have : CommRingCat.ofHom χ' = d := hc.hom_ext fun j => by
      apply CommRingCat.hom_ext
      change χ'.comp (Δ.leg c j) = d.hom.comp (Δ.leg c j)
      rw [h2, hfac]
    rw [← this]
    rfl

end LateralTheory.CohomologicalPurity.Hz

import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.ShapeFacts
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.GalEmbTop

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V.Af UpperTheory.V.Base UpperTheory.V.Sd

/- English proof (translation)
Take `⟨h1, -, h3⟩` from `hr`. Use `⟨h1, fun _ _ _ => Submodule.mem_top, fun W hW hi => h3 W hW fun g v hv => ?_⟩` and prove the remaining obligations. Take `⟨g', e⟩` from `h g`. Rewrite using `[← e]`. Conclude with `hi g' v hv`.
-/
private theorem isIrr_of_range {Γ Γ' k : Type} [Group Γ] [Group Γ'] [Field k] {n : ℕ}
    (r : Γ →* GL (Fin n) k) (r' : Γ' →* GL (Fin n) k) (h : ∀ g, ∃ g', r' g' = r g) (hr : IsIrr r) : IsIrr r' := by
  obtain ⟨h1, -, h3⟩ := hr
  refine ⟨h1, fun _ _ _ => Submodule.mem_top, fun W hW hi => h3 W hW fun g v hv => ?_⟩
  obtain ⟨g', e⟩ := h g
  rw [← e]
  exact hi g' v hv

/- English proof (translation)
Introduce `F E Ω _ _ _ _ _ _ _ _ _ _ l _ n r`. Use `haveI : FiniteDimensional F E := Module.Finite.of_restrictScalars_finite ℚ F E`. Use `haveI : IsAlgClosure F Ω := ⟨IsAlgClosure.isAlgClosed E, Algebra.IsAlgebraic.trans F E Ω⟩`. Take `⟨hemb, hopen, -⟩` from `galEmbTop F E Ω`. Establish `hoe : Topology.IsOpenEmbedding (galEmb F E Ω)`.

Use `⟨hemb, ?_⟩` and prove the remaining obligations. Rewrite using `[← MonoidHom.coe_range, range_galEmb]`. Conclude with `hopen`. Establish `hcyc : (cycBar F Ω l).comp (galEmb F E Ω) = cycBar E Ω l` using `rfl`. Establish `hD : ∀ (A : ValuationSubring Ω) (s : G E Ω), s ∈ Dec (F` using `E) A → galEmb F E Ω s ∈ Dec (F := F) A := fun A s hs => hs`.

Establish `hI : ∀ (A : ValuationSubring Ω) (s : G E Ω), s ∈ Ine (F` using `E) A → galEmb F E Ω s ∈ Ine (F := F) A := fun A s hs => ⟨hD A s hs.1, hs.2⟩`. Use `⟨hemb.continuous, hopen, hcyc, ⟨isIrr_of_range _ _ ?_, isIrr_of_range _ _ ?_⟩, ?_, ?_, ?_⟩` and prove the remaining obligations. Introduce and unpack `⟨g, hg⟩`. Rewrite `hg` using `[← range_galEmb]`. Take `⟨g', rfl⟩` from `hg`.

Conclude with `⟨g', rfl⟩`. Conclude with `fun g => ⟨⟨_, galEmb_mem F E Ω g⟩, rfl⟩`. Introduce `h H hH`. Use `isIrr_of_range _ _ ?_ (h (H.map (galEmb F E Ω)) (hoe.isOpenMap _ hH))` and prove the remaining obligations. Introduce and unpack `⟨g, g', hg', rfl⟩`.

Conclude with `⟨⟨g', hg'⟩, rfl⟩`. Introduce `τ h A hA`. Take `⟨g, hg⟩` from `h A hA`. Conclude with `⟨g, fun s hs => hg _ (hI A s hs)⟩`. Introduce and unpack `m ψ A ⟨κ, ⟨g, hg⟩, h2, h3⟩`.

Set `j : ↥(Dec (F` to `E) A) →* ↥(Dec (F := F) A) := ((galEmb F E Ω).comp (Dec (F := E) A).subtype).codRestrict _ fun s => hD A s s.2`. Conclude with `⟨fun i => (κ i).comp j, ⟨g, fun s => hg (j s)⟩, fun i s hs => h2 i (j s) (hI A s hs), fun i s => h3 i (j s)⟩`.
-/
theorem UpperTheory.V.Sd.resFacts :
    UpperTheory.V.Sd.ResFacts := by
  intro F E Ω _ _ _ _ _ _ _ _ _ _ l _ n r
  haveI : FiniteDimensional F E := Module.Finite.of_restrictScalars_finite ℚ F E
  haveI : IsAlgClosure F Ω :=
    ⟨IsAlgClosure.isAlgClosed E, Algebra.IsAlgebraic.trans F E Ω⟩
  obtain ⟨hemb, hopen, -⟩ := galEmbTop F E Ω
  have hoe : Topology.IsOpenEmbedding (galEmb F E Ω) := by
    refine ⟨hemb, ?_⟩
    rw [← MonoidHom.coe_range, range_galEmb]
    exact hopen
  have hcyc : (cycBar F Ω l).comp (galEmb F E Ω) = cycBar E Ω l := rfl
  have hD : ∀ (A : ValuationSubring Ω) (s : G E Ω), s ∈ Dec (F := E) A → galEmb F E Ω s ∈ Dec (F := F) A :=
    fun A s hs => hs
  have hI : ∀ (A : ValuationSubring Ω) (s : G E Ω), s ∈ Ine (F := E) A → galEmb F E Ω s ∈ Ine (F := F) A :=
    fun A s hs => ⟨hD A s hs.1, hs.2⟩
  refine ⟨hemb.continuous, hopen, hcyc, ⟨isIrr_of_range _ _ ?_, isIrr_of_range _ _ ?_⟩, ?_, ?_, ?_⟩
  · rintro ⟨g, hg⟩
    rw [← range_galEmb] at hg
    obtain ⟨g', rfl⟩ := hg
    exact ⟨g', rfl⟩
  · exact fun g => ⟨⟨_, galEmb_mem F E Ω g⟩, rfl⟩
  · intro h H hH
    refine isIrr_of_range _ _ ?_ (h (H.map (galEmb F E Ω)) (hoe.isOpenMap _ hH))
    rintro ⟨g, g', hg', rfl⟩
    exact ⟨⟨g', hg'⟩, rfl⟩
  · intro τ h A hA
    obtain ⟨g, hg⟩ := h A hA
    exact ⟨g, fun s hs => hg _ (hI A s hs)⟩
  · rintro m ψ A ⟨κ, ⟨g, hg⟩, h2, h3⟩
    let j : ↥(Dec (F := E) A) →* ↥(Dec (F := F) A) :=
      ((galEmb F E Ω).comp (Dec (F := E) A).subtype).codRestrict _ fun s => hD A s s.2
    exact ⟨fun i => (κ i).comp j, ⟨g, fun s => hg (j s)⟩, fun i s hs => h2 i (j s) (hI A s hs), fun i s => h3 i (j s)⟩

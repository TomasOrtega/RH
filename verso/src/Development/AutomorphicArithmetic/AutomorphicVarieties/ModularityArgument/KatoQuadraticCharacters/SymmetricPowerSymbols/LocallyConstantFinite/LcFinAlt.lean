import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.SymmetricPowerSymbols.LocallyConstantFinite.LcFin
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.SymmetricPowerSymbols.CycSpec

open GlobalTheory.KZ GlobalTheory.K4 Polynomial UpperTheory.V.Z.Kato.Sym UpperTheory.V.Z.Kato.Sym.PE

/- English proof (translation)
Introduce `F E A _ _ _ _ U hU η hη`. Establish `hS : ∀ g : U, IsOpen {x : Gal(E/F) | x ∈ U ∧ η x = η g}`. Introduce `g`. Use `hU.isOpenMap_subtype_val _ (hη.isOpen_fiber (η g))` as an intermediate fact. Use `this using 1` and compare the differences between its conclusion and the goal.

Use extensionality with `x`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨hx, hxg⟩`. Conclude with `⟨⟨x, hx⟩, hxg, rfl⟩`. Introduce and unpack `⟨y, hy, rfl⟩`.

Conclude with `⟨y.2, hy⟩`. Establish `hN : ∀ g : U, ∃ L : IntermediateField F E, FiniteDimensional F L ∧ (L.fixingSubgroup : Set Gal(E/F)) ⊆ {y | (g : Gal(E/F)) * y ∈ U ∧ η ((g : Gal(E/F)) * y) = η g}`. Introduce `g`. Rewrite using `[← krullTopology_mem_nhds_one_iff]`. Use `IsOpen.mem_nhds ((hS g).preimage (continuous_const.mul continuous_id)) ?_` and prove the remaining obligations.

Simplify using `[g.2]`. Use `choose L hLfd hLsub using hN`. Establish `hfg : ∀ g : U, ∃ s : Finset E, Submodule.span F (s : Set E) = Subalgebra.toSubmodule (L g).toSubalgebra`. Introduce `g`. Use `haveI := hLfd g`.

Conclude with `(Submodule.fg_iff_finiteDimensional _).2 (inferInstanceAs (FiniteDimensional F (L g)))`. Use `choose s hs using hfg`. Establish `hcpt : IsCompact (U : Set Gal(E/F))` using `(Subgroup.isClosed_of_isOpen U hU).isCompact`. Take `⟨t, ht⟩` from `hcpt.elim_finite_subcover (fun g : U => {x : Gal(E/F) | (g : Gal(E/F))⁻¹ * x ∈ (L g).fixingSubgroup}) (fun g => by haveI := hLfd g`. Conclude with `(IntermediateField.fixingSubgroup_isOpen (L g)).preimage (continuous_const.mul continuous_id))`.

Use the proof step `(fun x hx => Set.mem_iUnion.2 ⟨⟨x, hx⟩, by simp [one_mem]⟩)`. Use `⟨t.biUnion s, ?_⟩` and prove the remaining obligations. Introduce `h hh h' hh' hag`. Take `⟨g, hgt, hg⟩` from `Set.mem_iUnion₂.1 (ht hh)`. Establish `hg0 : (g : Gal(E/F))⁻¹ * h ∈ (L g).fixingSubgroup` using `hg`.

Establish `hsame : ∀ x ∈ L g, h x = h' x`. Introduce `x hx`. Establish `hx' : x ∈ Submodule.span F (s g : Set E)`. Rewrite using `[hs g]`. Conclude with `hx`.

Conclude with `LinearMap.eqOn_span' (f := h.toLinearMap) (g := h'.toLinearMap) (fun b hb => hag b (Finset.mem_biUnion.2 ⟨g, hgt, hb⟩)) hx'`. Establish `hg' : (g : Gal(E/F))⁻¹ * h' ∈ (L g).fixingSubgroup`. Rewrite `hg0`, the goal using `[IntermediateField.mem_fixingSubgroup_iff]`. Introduce `x hx`. Rewrite using `[AlgEquiv.mul_apply, ← hsame x hx, ← AlgEquiv.mul_apply]`.

Conclude with `hg0 x hx`. Establish `e1` using `(hLsub g hg0).2`. Establish `e2` using `(hLsub g hg').2`. Simplify using `only [mul_inv_cancel_left] at e1 e2`. Rewrite using `[e1, e2]`.
-/
theorem UpperTheory.V.Z.Kato.Sym.PE.lcFin :
    UpperTheory.V.Z.Kato.Sym.PE.LcFin := by
  classical
  intro F E A _ _ _ _ U hU η hη
  have hS : ∀ g : U, IsOpen {x : Gal(E/F) | x ∈ U ∧ η x = η g} := by
    intro g
    have := hU.isOpenMap_subtype_val _ (hη.isOpen_fiber (η g))
    convert this using 1
    ext x
    constructor
    · rintro ⟨hx, hxg⟩
      exact ⟨⟨x, hx⟩, hxg, rfl⟩
    · rintro ⟨y, hy, rfl⟩
      exact ⟨y.2, hy⟩
  have hN : ∀ g : U, ∃ L : IntermediateField F E, FiniteDimensional F L ∧
      (L.fixingSubgroup : Set Gal(E/F)) ⊆
        {y | (g : Gal(E/F)) * y ∈ U ∧ η ((g : Gal(E/F)) * y) = η g} := by
    intro g
    rw [← krullTopology_mem_nhds_one_iff]
    refine IsOpen.mem_nhds ((hS g).preimage (continuous_const.mul continuous_id)) ?_
    simp [g.2]
  choose L hLfd hLsub using hN
  have hfg : ∀ g : U, ∃ s : Finset E,
      Submodule.span F (s : Set E) = Subalgebra.toSubmodule (L g).toSubalgebra := by
    intro g
    haveI := hLfd g
    exact (Submodule.fg_iff_finiteDimensional _).2 (inferInstanceAs (FiniteDimensional F (L g)))
  choose s hs using hfg
  have hcpt : IsCompact (U : Set Gal(E/F)) := (Subgroup.isClosed_of_isOpen U hU).isCompact
  obtain ⟨t, ht⟩ := hcpt.elim_finite_subcover
    (fun g : U => {x : Gal(E/F) | (g : Gal(E/F))⁻¹ * x ∈ (L g).fixingSubgroup})
    (fun g => by
      haveI := hLfd g
      exact (IntermediateField.fixingSubgroup_isOpen (L g)).preimage
        (continuous_const.mul continuous_id))
    (fun x hx => Set.mem_iUnion.2 ⟨⟨x, hx⟩, by simp [one_mem]⟩)
  refine ⟨t.biUnion s, ?_⟩
  intro h hh h' hh' hag
  obtain ⟨g, hgt, hg⟩ := Set.mem_iUnion₂.1 (ht hh)
  have hg0 : (g : Gal(E/F))⁻¹ * h ∈ (L g).fixingSubgroup := hg
  have hsame : ∀ x ∈ L g, h x = h' x := by
    intro x hx
    have hx' : x ∈ Submodule.span F (s g : Set E) := by
      rw [hs g]
      exact hx
    exact LinearMap.eqOn_span' (f := h.toLinearMap) (g := h'.toLinearMap)
      (fun b hb => hag b (Finset.mem_biUnion.2 ⟨g, hgt, hb⟩)) hx'
  have hg' : (g : Gal(E/F))⁻¹ * h' ∈ (L g).fixingSubgroup := by
    rw [IntermediateField.mem_fixingSubgroup_iff] at hg0 ⊢
    intro x hx
    rw [AlgEquiv.mul_apply, ← hsame x hx, ← AlgEquiv.mul_apply]
    exact hg0 x hx
  have e1 := (hLsub g hg0).2
  have e2 := (hLsub g hg').2
  simp only [mul_inv_cancel_left] at e1 e2
  rw [e1, e2]

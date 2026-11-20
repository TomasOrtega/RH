import Development.AbelianVarietyTheory.Definitions.Divisors.IsThetaCompact
open AlgebraicGeometry CategoryTheory Limits IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.SiegelTor

open TopologicalSpace

namespace GlobalTheory.CompPart

/- English proof (translation)
Use `haveI := hd x`. Rewrite using `[← Scheme.range_fromSpecStalk, ← Set.image_univ]`. Conclude with `(IrreducibleSpace.isIrreducible_univ (Spec (Z.presheaf.stalk x))).image _ (Z.fromSpecStalk x).continuous.continuousOn`.
-/
theorem isIrreducible_generizations {Z : Scheme.{0}} (hd : ∀ x : Z, IsDomain (Z.presheaf.stalk x)) (x : Z) :
    IsIrreducible {y : Z | y ⤳ x} := by
  haveI := hd x
  rw [← Scheme.range_fromSpecStalk, ← Set.image_univ]
  exact (IrreducibleSpace.isIrreducible_univ (Spec (Z.presheaf.stalk x))).image _
    (Z.fromSpecStalk x).continuous.continuousOn

/- English proof (translation)
Establish `hcl : IsClosed C` using `isClosed_of_mem_irreducibleComponents C hC`. Take `⟨η, hη⟩` from `QuasiSober.sober hC.1 hcl`. Establish `hηx : η ⤳ x`. Rewrite using `[specializes_iff_mem_closure, hη.def]`. Conclude with `hx`.

Establish `hsub : C ⊆ closure {y : Z | y ⤳ x}`. Rewrite using `[← hη.def]`. Conclude with `closure_mono (Set.singleton_subset_iff.2 hηx)`. Conclude with `hsub.antisymm (hC.2 (isIrreducible_generizations hd x).closure hsub)`.
-/
theorem eq_closure_generizations {Z : Scheme.{0}} (hd : ∀ x : Z, IsDomain (Z.presheaf.stalk x))
    {C : Set Z} (hC : C ∈ irreducibleComponents Z) {x : Z} (hx : x ∈ C) :
    C = closure {y : Z | y ⤳ x} := by
  have hcl : IsClosed C := isClosed_of_mem_irreducibleComponents C hC
  obtain ⟨η, hη⟩ := QuasiSober.sober hC.1 hcl
  have hηx : η ⤳ x := by
    rw [specializes_iff_mem_closure, hη.def]; exact hx
  have hsub : C ⊆ closure {y : Z | y ⤳ x} := by
    rw [← hη.def]
    exact closure_mono (Set.singleton_subset_iff.2 hηx)
  exact hsub.antisymm (hC.2 (isIrreducible_generizations hd x).closure hsub)

/- English proof (translation)
Assemble the required witnesses or components as `⟨⟨_, irreducibleComponent_mem_irreducibleComponents x⟩, mem_irreducibleComponent, fun C hC => Subtype.ext ((eq_closure_generizations hd C.2 hC).trans (eq_closure_generizations hd (irreducibleComponent_mem_irreducibleComponents x) mem_irreducibleComponent).symm)⟩`.
-/
theorem existsUnique_mem {Z : Scheme.{0}} (hd : ∀ x : Z, IsDomain (Z.presheaf.stalk x)) (x : Z) :
    ∃! C : irreducibleComponents Z, x ∈ (C : Set Z) :=
  ⟨⟨_, irreducibleComponent_mem_irreducibleComponents x⟩, mem_irreducibleComponent, fun C hC =>
    Subtype.ext ((eq_closure_generizations hd C.2 hC).trans
      (eq_closure_generizations hd (irreducibleComponent_mem_irreducibleComponents x)
        mem_irreducibleComponent).symm)⟩

/- English proof (translation)
Establish `hfin : (irreducibleComponents Z).Finite` using `NoetherianSpace.finite_irreducibleComponents`. Establish `hcompl : Cᶜ = ⋃ D ∈ {D ∈ irreducibleComponents Z | D ≠ C}, D`. Use extensionality with `y`. Simplify using `only [Set.mem_compl_iff, Set.mem_iUnion, Set.mem_ofPred_eq, exists_prop]`. Prove the components needed by the constructor for the conclusion.

Introduce `hy`. Conclude with `⟨irreducibleComponent y, ⟨irreducibleComponent_mem_irreducibleComponents y, fun h => hy (h ▸ mem_irreducibleComponent)⟩, mem_irreducibleComponent⟩`. Introduce and unpack `⟨D, ⟨hD, hne⟩, hyD⟩ hyC`. Conclude with `hne (congrArg Subtype.val ((existsUnique_mem hd y).unique (y₁ := ⟨D, hD⟩) (y₂ := ⟨C, hC⟩) hyD hyC))`. Rewrite using `[← isClosed_compl_iff, hcompl]`.

Conclude with `(hfin.subset fun D hD => hD.1).isClosed_biUnion fun D hD => isClosed_of_mem_irreducibleComponents D hD.1`.
-/
theorem isOpen_of_mem {Z : Scheme.{0}} [NoetherianSpace Z] (hd : ∀ x : Z, IsDomain (Z.presheaf.stalk x))
    {C : Set Z} (hC : C ∈ irreducibleComponents Z) : IsOpen C := by
  have hfin : (irreducibleComponents Z).Finite := NoetherianSpace.finite_irreducibleComponents
  have hcompl : Cᶜ = ⋃ D ∈ {D ∈ irreducibleComponents Z | D ≠ C}, D := by
    ext y
    simp only [Set.mem_compl_iff, Set.mem_iUnion, Set.mem_ofPred_eq, exists_prop]
    constructor
    · intro hy
      exact ⟨irreducibleComponent y, ⟨irreducibleComponent_mem_irreducibleComponents y,
        fun h => hy (h ▸ mem_irreducibleComponent)⟩, mem_irreducibleComponent⟩
    · rintro ⟨D, ⟨hD, hne⟩, hyD⟩ hyC
      exact hne (congrArg Subtype.val ((existsUnique_mem hd y).unique (y₁ := ⟨D, hD⟩) (y₂ := ⟨C, hC⟩) hyD hyC))
  rw [← isClosed_compl_iff, hcompl]
  exact (hfin.subset fun D hD => hD.1).isClosed_biUnion fun D hD =>
    isClosed_of_mem_irreducibleComponents D hD.1

end GlobalTheory.CompPart

/- English proof (translation)
Introduce `n Z z hz hN`. Use `haveI : IsNoetherianRing (cycAway n) := is_noetherian_subring_closure _ (Set.toFinite _)`. Use `haveI : AlgebraicGeometry.IsNoetherian Z := GlobalTheory.isNoetherian_of_isProjOver hz`. Establish `hd : ∀ x : Z, IsDomain (Z.presheaf.stalk x)` using `fun x => hN.isDomain_stalk x`. Establish `hfin : (irreducibleComponents Z).Finite` using `NoetherianSpace.finite_irreducibleComponents`.

Conclude with `⟨irreducibleComponents Z, hfin.fintype, fun C => (C : Set Z), fun C => ⟨isClosed_of_mem_irreducibleComponents _ C.2, GlobalTheory.CompPart.isOpen_of_mem hd C.2⟩, fun C => C.2.1, GlobalTheory.CompPart.existsUnique_mem hd⟩`.
-/
theorem GlobalTheory.irreducibleComponents_clopen_partition : ∀ (n : ℕ) (Z : Scheme.{0}) (z : Z ⟶ Sp (cycAway n)),
    IsProjOver z → GlobalTheory.IsNormalScheme Z → ∃ (ι : Type) (_ : Fintype ι) (W : ι → Set Z),
      (∀ c, IsClopen (W c)) ∧ (∀ c, IsIrreducible (W c)) ∧ ∀ x, ∃! c, x ∈ W c := by
  intro n Z z hz hN
  haveI : IsNoetherianRing (cycAway n) :=
    is_noetherian_subring_closure _ (Set.toFinite _)
  haveI : AlgebraicGeometry.IsNoetherian Z := GlobalTheory.isNoetherian_of_isProjOver hz
  have hd : ∀ x : Z, IsDomain (Z.presheaf.stalk x) := fun x => hN.isDomain_stalk x
  have hfin : (irreducibleComponents Z).Finite := NoetherianSpace.finite_irreducibleComponents
  exact ⟨irreducibleComponents Z, hfin.fintype, fun C => (C : Set Z),
    fun C => ⟨isClosed_of_mem_irreducibleComponents _ C.2, GlobalTheory.CompPart.isOpen_of_mem hd C.2⟩,
    fun C => C.2.1, GlobalTheory.CompPart.existsUnique_mem hd⟩

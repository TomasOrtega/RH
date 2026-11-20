import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusOfSpec
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedOrbitalIntegralSummandGoodPlaceIndicator
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsOrthonormalBasisUnimodularHermitianLocalRi
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsWittBasis
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnramifiedQuadraticNormsTraceUniformizerFactsStatement

namespace GlobalTheory.LatticeIntegralCoordinates

/- English proof (translation)
Use `haveI : Module.IsTorsionFree O V := by`. Use `Module.IsTorsionFree.of_smul_eq_zero ?_` and prove the remaining obligations. Introduce `c v h`. Rewrite `h` using `[← algebraMap_smul E c v]`. Break down `smul_eq_zero.mp h with h | h` into its components or cases.

Use the proof step `left; exact (IsFractionRing.injective O E) (by simpa using h)`. Use `right`. Conclude with `h`. Use `haveI : Module.Finite O L := Module.Finite.iff_fg.mpr hfg`. Use `haveI : Module.Free O L := inferInstance`.

Set `bL` to `Module.Free.chooseBasis O L`. Set `v : Module.Free.ChooseBasisIndex O L → V` to `fun i => (bL i : V)`. Establish `hli : LinearIndependent O v` using `bL.linearIndependent.map' L.subtype (Submodule.ker_subtype L)`. Establish `hliE : LinearIndependent E v` using `hli.localization E (nonZeroDivisors O)`. Establish `hL : Submodule.span O (Set.range v) = L`.

Establish `: Set.range v = L.subtype '' Set.range bL`. Rewrite using `[← Set.range_comp]`. Both sides reduce to the same expression. Rewrite using `[this, Submodule.span_image, bL.span_eq, Submodule.map_top, Submodule.range_subtype]`. Establish `htop : ⊤ ≤ Submodule.span E (Set.range v)`.

Rewrite using `[← hspan, Submodule.span_le]`. Introduce `x hx`. Conclude with `Submodule.span_subset_span O E _ (hL.ge hx)`. Set `b0` to `Module.Basis.mk hliE htop`. Establish `hb0 : ∀ j, b0 j = v j` using `fun j => Module.Basis.mk_apply hliE htop j`.

Establish `hcard` using `Module.finrank_eq_card_basis b0`. Set `e` to `Fintype.equivFinOfCardEq hcard.symm`. Use `⟨b0.reindex e, fun y => ⟨fun hy i => ?_, fun hy => ?_⟩⟩` and prove the remaining obligations. Take `⟨c, rfl⟩` from `(Submodule.mem_span_range_iff_exists_fun O).1 (hL.ge hy)`. Establish `h1 : ∑ j, c j • v j = ∑ j, algebraMap O E (c j) • b0 j` using `Finset.sum_congr rfl fun j _ => by rw [hb0, algebraMap_smul]`.

Rewrite using `[Module.Basis.repr_reindex_apply, h1, b0.repr_sum_self]`. Conclude with `⟨_, rfl⟩`. Rewrite using `[← b0.sum_repr y]`. Use `L.sum_mem fun j _ => ?_` and prove the remaining obligations. Take `⟨c, hc⟩` from `hy (e j)`.

Rewrite `hc` using `[Module.Basis.repr_reindex_apply, Equiv.symm_apply_apply]`. Rewrite using `[← hc, algebraMap_smul, hb0]`. Conclude with `L.smul_mem c (bL j).2`.
-/
theorem exists_basis_of_lattice (O E V : Type) [CommRing O] [IsDomain O] [IsPrincipalIdealRing O]
    [Field E] [Algebra O E] [IsFractionRing O E] [AddCommGroup V] [Module E V] [Module O V]
    [IsScalarTower O E V] (L : Submodule O V) (hfg : L.FG)
    (hspan : Submodule.span E (L : Set V) = ⊤) :
    ∃ b : Module.Basis (Fin (Module.finrank E V)) E V,
      ∀ y : V, y ∈ L ↔ ∀ i, b.repr y i ∈ (algebraMap O E).range := by
  classical
  haveI : Module.IsTorsionFree O V := by
    refine Module.IsTorsionFree.of_smul_eq_zero ?_
    intro c v h
    rw [← algebraMap_smul E c v] at h
    rcases smul_eq_zero.mp h with h | h
    · left; exact (IsFractionRing.injective O E) (by simpa using h)
    · right; exact h
  haveI : Module.Finite O L := Module.Finite.iff_fg.mpr hfg
  haveI : Module.Free O L := inferInstance
  let bL := Module.Free.chooseBasis O L
  let v : Module.Free.ChooseBasisIndex O L → V := fun i => (bL i : V)
  have hli : LinearIndependent O v :=
    bL.linearIndependent.map' L.subtype (Submodule.ker_subtype L)
  have hliE : LinearIndependent E v := hli.localization E (nonZeroDivisors O)
  have hL : Submodule.span O (Set.range v) = L := by
    have : Set.range v = L.subtype '' Set.range bL := by
      rw [← Set.range_comp]; rfl
    rw [this, Submodule.span_image, bL.span_eq, Submodule.map_top, Submodule.range_subtype]
  have htop : ⊤ ≤ Submodule.span E (Set.range v) := by
    rw [← hspan, Submodule.span_le]
    intro x hx
    exact Submodule.span_subset_span O E _ (hL.ge hx)
  let b0 := Module.Basis.mk hliE htop
  have hb0 : ∀ j, b0 j = v j := fun j => Module.Basis.mk_apply hliE htop j
  have hcard := Module.finrank_eq_card_basis b0
  let e := Fintype.equivFinOfCardEq hcard.symm
  refine ⟨b0.reindex e, fun y => ⟨fun hy i => ?_, fun hy => ?_⟩⟩
  · obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun O).1 (hL.ge hy)
    have h1 : ∑ j, c j • v j = ∑ j, algebraMap O E (c j) • b0 j :=
      Finset.sum_congr rfl fun j _ => by rw [hb0, algebraMap_smul]
    rw [Module.Basis.repr_reindex_apply, h1, b0.repr_sum_self]
    exact ⟨_, rfl⟩
  · rw [← b0.sum_repr y]
    refine L.sum_mem fun j _ => ?_
    obtain ⟨c, hc⟩ := hy (e j)
    rw [Module.Basis.repr_reindex_apply, Equiv.symm_apply_apply] at hc
    rw [← hc, algebraMap_smul, hb0]
    exact L.smul_mem c (bL j).2

/- English proof (translation)
Introduce `K V _ _ _ _ _ L hfg hspan` and use `exists_basis_of_lattice K.O K.E V L hfg hspan`.
-/
theorem lattice_eq_integral_coords :
    ∀ (K : GlobalTheory.UnitLemma.UQ) (V : Type) [AddCommGroup V] [Module K.E V] [Module K.O V]
      [IsScalarTower K.O K.E V] [FiniteDimensional K.E V] (L : Submodule K.O V),
      L.FG → Submodule.span K.E (L : Set V) = ⊤ →
      ∃ b : Module.Basis (Fin (Module.finrank K.E V)) K.E V,
        ∀ y : V, y ∈ L ↔ ∀ i, b.repr y i ∈ (algebraMap K.O K.E).range :=
  fun K V _ _ _ _ _ L hfg hspan => exists_basis_of_lattice K.O K.E V L hfg hspan

end GlobalTheory.LatticeIntegralCoordinates

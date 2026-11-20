import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.CompactOrbits.NilpotentOrbits.OrbitIntegrals.ModulusBounds.MemStabIff

noncomputable section

set_option linter.unusedSectionVars false

open Matrix Module ValuativeRel MeasureTheory GroundTheory.Automorphic.GLnLocal

namespace PositivityTheory.RgUd.T.Nil.Orb.BModbound

open PositivityTheory.RgUd.T PositivityTheory.RgUd.T.Nil PositivityTheory.RgUd.T.Nil.Orb

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n : ℕ}

/- English proof (translation)
Rewrite using `[Subgroup.mem_inf, mem_lat, mem_C_iff]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨h1, h2⟩`. Use `⟨(mem_Gz_iff Z u).1 h2, fun i j => ?_⟩` and prove the remaining obligations. Use `((mem_congruenceSubgroup_iff k n).1 h1).2 i j` as an intermediate fact.

Simplify `this` using `[Matrix.sub_apply]`. Introduce and unpack `⟨h1, h2⟩`. Take `⟨w, hw, hwv⟩` from `exists_unit (k := k) m hm (u.val - 1) h2`. Establish `: w = u` using `Units.ext (by rw [hwv]; abel)`. Conclude with `⟨this ▸ hw, (mem_Gz_iff Z u).2 h1⟩`.
-/
theorem memK (Z : Subalgebra k (Matrix (Fin n) (Fin n) k)) (m : ℕ) (hm : 1 ≤ m) (u : GL (Fin n) k) :
    u ∈ congruenceSubgroup k n m ⊓ GzS Z ↔
      u.val - 1 ∈ lat (Subalgebra.centralizer k (Z : Set (Matrix (Fin n) (Fin n) k))).toSubmodule
        (valuation k (uniformizer k : k) ^ m) := by
  rw [Subgroup.mem_inf, mem_lat, mem_C_iff]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨(mem_Gz_iff Z u).1 h2, fun i j => ?_⟩
    have := ((mem_congruenceSubgroup_iff k n).1 h1).2 i j
    simpa [Matrix.sub_apply] using this
  · rintro ⟨h1, h2⟩
    obtain ⟨w, hw, hwv⟩ := exists_unit (k := k) m hm (u.val - 1) h2
    have : w = u := Units.ext (by rw [hwv]; abel)
    exact ⟨this ▸ hw, (mem_Gz_iff Z u).2 h1⟩

/- English proof (translation)
Rewrite using `[Subgroup.mem_map_equiv, MulAut.conj_symm_apply]`.
-/
theorem memK' (K : Subgroup (GL (Fin n) k)) (g u : GL (Fin n) k) :
    u ∈ K.map (MulAut.conj g).toMonoidHom ↔ g⁻¹ * u * g ∈ K := by
  rw [Subgroup.mem_map_equiv, MulAut.conj_symm_apply]

end PositivityTheory.RgUd.T.Nil.Orb.BModbound

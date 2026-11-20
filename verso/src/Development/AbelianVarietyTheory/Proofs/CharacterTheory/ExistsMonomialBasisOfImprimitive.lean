import Mathlib
import Development.AbelianVarietyTheory.Definitions.CommutativeAlgebra.AbByPOfComm
import Development.AbelianVarietyTheory.Definitions.CommutativeAlgebra.InvariantSubspaceMobiusInverseRecEqOfFinrankLt
open Polynomial GlobalTheory.CuspGL GlobalTheory.BI

namespace GlobalTheory.CuspGL

/- English proof (translation)
Take `⟨n, b, hb⟩` from `hW`. Establish `hinj : ∀ g : G, Function.Injective (ρ g)`. Introduce `g x y h`. Establish `h2` using `congrArg (ρ g⁻¹) h`. Simplify `h2` using `[← Module.End.mul_apply, ← map_mul]`.

Establish `hint : DirectSum.IsInternal (fun q : G ⧸ T => W.map (ρ q.out))` using `DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top hind hsup`. Set `bq : ∀ q : G ⧸ T, Module.Basis (Fin n) k (W.map (ρ q.out))` to `fun q => b.map (Submodule.equivMapOfInjective (ρ q.out) (hinj _) W)`. Set `B` to `hint.collectedBasis bq`. Establish `hB : ∀ (q : G ⧸ T) (i : Fin n), B ⟨q, i⟩ = ρ q.out (b i : V)`. Introduce `q i`.

Simplify using `[B, bq]`. Use `haveI : Fintype (G ⧸ T) := Fintype.ofFinite _`. Set `e` to `Fintype.equivFin (Σ _ : G ⧸ T, Fin n)`. Use `⟨_, B.reindex e, fun g i => ?_⟩` and prove the remaining obligations. Take `⟨⟨q, i⟩, rfl⟩` from `e.surjective i`.

Take `⟨t, ht⟩` from `QuotientGroup.mk_out_eq_mul T (g * q.out)`. Take `⟨j, c, hj⟩` from `hb (t⁻¹ : T) (t⁻¹).2 i`. Use `⟨e ⟨(QuotientGroup.mk (g * q.out) : G ⧸ T), j⟩, c, ?_⟩` and prove the remaining obligations. Simplify using `only [Module.Basis.reindex_apply, Equiv.symm_apply_apply, hB]`. Rewrite using `[← map_smul, ← hj, ht, ← Module.End.mul_apply, ← Module.End.mul_apply, ← map_mul, ← map_mul]`.

Simplify using the standard rewrite rules.
-/
theorem exists_monomial_basis_of_imprimitive (k : Type) [Field k] (G : Type) [Group G] [Finite G]
    (V : Type) [AddCommGroup V] [Module k V] [FiniteDimensional k V] (ρ : Representation k G V)
    (T : Subgroup G) (W : Submodule k V)
    (hind : iSupIndep (fun q : G ⧸ T => W.map (ρ q.out)))
    (hsup : ⨆ q : G ⧸ T, W.map (ρ q.out) = ⊤)
    (hW : ∃ (n : ℕ) (b : Module.Basis (Fin n) k W), ∀ t ∈ T, ∀ i : Fin n,
      ∃ (j : Fin n) (c : k), ρ t (b i : V) = c • (b j : V)) :
    ∃ (n : ℕ) (b : Module.Basis (Fin n) k V), ∀ (g : G) (i : Fin n),
      ∃ (j : Fin n) (c : k), ρ g (b i) = c • b j := by
  classical
  obtain ⟨n, b, hb⟩ := hW
  have hinj : ∀ g : G, Function.Injective (ρ g) := by
    intro g x y h
    have h2 := congrArg (ρ g⁻¹) h
    simpa [← Module.End.mul_apply, ← map_mul] using h2
  have hint : DirectSum.IsInternal (fun q : G ⧸ T => W.map (ρ q.out)) :=
    DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top hind hsup
  let bq : ∀ q : G ⧸ T, Module.Basis (Fin n) k (W.map (ρ q.out)) := fun q =>
    b.map (Submodule.equivMapOfInjective (ρ q.out) (hinj _) W)
  let B := hint.collectedBasis bq
  have hB : ∀ (q : G ⧸ T) (i : Fin n), B ⟨q, i⟩ = ρ q.out (b i : V) := by
    intro q i
    simp [B, bq]
  haveI : Fintype (G ⧸ T) := Fintype.ofFinite _
  let e := Fintype.equivFin (Σ _ : G ⧸ T, Fin n)
  refine ⟨_, B.reindex e, fun g i => ?_⟩
  obtain ⟨⟨q, i⟩, rfl⟩ := e.surjective i
  obtain ⟨t, ht⟩ := QuotientGroup.mk_out_eq_mul T (g * q.out)
  obtain ⟨j, c, hj⟩ := hb (t⁻¹ : T) (t⁻¹).2 i
  refine ⟨e ⟨(QuotientGroup.mk (g * q.out) : G ⧸ T), j⟩, c, ?_⟩
  simp only [Module.Basis.reindex_apply, Equiv.symm_apply_apply, hB]
  rw [← map_smul, ← hj, ht, ← Module.End.mul_apply, ← Module.End.mul_apply, ← map_mul, ← map_mul]
  simp

end GlobalTheory.CuspGL

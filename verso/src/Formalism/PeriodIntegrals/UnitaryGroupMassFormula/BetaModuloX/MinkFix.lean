import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.BetaModuloX.MapEqOfIff
import Formalism.FlagUnipotentLattices.MinkowskiFactorialBounds.IdealsOfNormEqIndexSet

noncomputable section

open scoped Classical

open NumberField Module

namespace PI.UnitaryGroupMassFormula.BetaModX

section Q4

variable {E : Type} [Field E] [NumberField E] [StarRing E]
variable {Q : Type} [AddCommGroup Q] [Module E Q] [Module (𝓞 E) Q] [IsScalarTower (𝓞 E) E Q]

/- English proof (translation)
Establish `hfinO : Module.Finite (𝓞 E) L` using `Module.Finite.iff_fg.2 hL`. Establish `hfinZ : Module.Finite ℤ L` using `Module.Finite.trans (𝓞 E) L`. Use `Formalism.HermitianLatticesTheory.isAddTorsionFree_ringOfIntegers_submodule (K := E) L` as an intermediate fact. Establish `hfree : Module.Free ℤ L` using `Module.free_of_finite_type_torsion_free'`. Set `ψ : L →ₗ[ℤ] L` to `(((φ.restrictScalars (𝓞 E)).restrict hφL : L →ₗ[𝓞 E] L) : L →+ L).toIntLinearMap`.

Establish `hψ : ∀ x : L, (ψ x : Q) = φ x` using `fun x => rfl`. Establish `hiter : ∀ (k : ℕ) (x : L), ((ψ^[k] x : L) : Q) = φ^[k] x`. Introduce `k`. Proceed by induction on `k with`. Consider the case `zero => intro x`.

Both sides reduce to the same expression. Consider the case `succ k ih`. Introduce `x`. Rewrite using `[Function.iterate_succ_apply', Function.iterate_succ_apply', hψ, ih]`. Establish `hψn : ψ ^ n = 1`.

Use `LinearMap.ext fun x => Subtype.ext ?_` and prove the remaining obligations. Rewrite using `[Module.End.pow_apply, hiter, hpow]`. Both sides reduce to the same expression. Establish `hc : ∀ x : L, ∃ y : L, ψ x - x = (g : ℤ) • y`. Introduce `x`.

Take `⟨y, hy, h⟩` from `hcong x x.2`. Use `⟨⟨y, hy⟩, Subtype.ext ?_⟩` and prove the remaining obligations. Simplify using `only [Submodule.coe_sub, hψ, h, Submodule.coe_smul_of_tower, natCast_zsmul]`. Use `choose yf hyf using hc`. Set `b` to `(Module.Free.chooseBasis ℤ L).reindex (Fintype.equivFin (Module.Free.ChooseBasisIndex ℤ L))`.

Set `A` to `LinearMap.toMatrixAlgEquiv b ψ`. Set `B : Matrix (Fin (Fintype.card (Module.Free.ChooseBasisIndex ℤ L))) (Fin (Fintype.card (Module.Free.ChooseBasisIndex ℤ L))) ℤ` to `Matrix.of fun i j => b.repr (yf (b j)) i`. Establish `hAn : A ^ n = 1` using `by show (LinearMap.toMatrixAlgEquiv b ψ) ^ n = 1`. Rewrite using `[← map_pow, hψn, map_one]`. Establish `hAB : A = 1 + (g : ℤ) • B`.

Use extensionality with `i j`. Use `show (LinearMap.toMatrixAlgEquiv b ψ) i j = _`. Rewrite using `[LinearMap.toMatrixAlgEquiv_apply]`. Establish `h` using `hyf (b j)`. Rewrite `h` using `[sub_eq_iff_eq_add']`.

Rewrite using `[h, map_add, map_zsmul, Finsupp.add_apply, Finsupp.smul_apply, Module.Basis.repr_self, Finsupp.single_apply]`. Simplify using `[B, Matrix.one_apply, eq_comm]`. Establish `hA1` using `Formalism.HermitianLatticeCounting.P.finite_order_congruence _ n (g : ℤ) A B (by exact_mod_cast hg) hn hAn hAB`. Establish `hψ1 : ψ = 1`. Apply `(LinearMap.toMatrixAlgEquiv b).injective` to reduce the goal to its premises.

Rewrite using `[map_one]`. Conclude with `hA1`. Introduce `x hx`. Use `congrArg (fun f : L →ₗ[ℤ] L => ((f ⟨x, hx⟩ : L) : Q)) hψ1` as an intermediate fact. Simplify `this` using `[hψ]`.
-/
theorem mink_fix (L : Submodule (𝓞 E) Q) (hL : L.FG) (φ : Q →ₗ[E] Q) (hφL : ∀ x ∈ L, φ x ∈ L)
    (n : ℕ) (hn : 0 < n) (hpow : ∀ x, φ^[n] x = x) (g : ℕ) (hg : 3 ≤ g)
    (hcong : ∀ x ∈ L, ∃ y ∈ L, φ x - x = g • y) : ∀ x ∈ L, φ x = x := by
  have hfinO : Module.Finite (𝓞 E) L := Module.Finite.iff_fg.2 hL
  have hfinZ : Module.Finite ℤ L := Module.Finite.trans (𝓞 E) L
  have := Formalism.HermitianLatticesTheory.isAddTorsionFree_ringOfIntegers_submodule (K := E) L
  have hfree : Module.Free ℤ L := Module.free_of_finite_type_torsion_free'
  let ψ : L →ₗ[ℤ] L :=
    (((φ.restrictScalars (𝓞 E)).restrict hφL : L →ₗ[𝓞 E] L) : L →+ L).toIntLinearMap
  have hψ : ∀ x : L, (ψ x : Q) = φ x := fun x => rfl
  have hiter : ∀ (k : ℕ) (x : L), ((ψ^[k] x : L) : Q) = φ^[k] x := by
    intro k
    induction k with
    | zero => intro x; rfl
    | succ k ih =>
      intro x
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply', hψ, ih]
  have hψn : ψ ^ n = 1 := by
    refine LinearMap.ext fun x => Subtype.ext ?_
    rw [Module.End.pow_apply, hiter, hpow]
    rfl
  have hc : ∀ x : L, ∃ y : L, ψ x - x = (g : ℤ) • y := by
    intro x
    obtain ⟨y, hy, h⟩ := hcong x x.2
    refine ⟨⟨y, hy⟩, Subtype.ext ?_⟩
    simp only [Submodule.coe_sub, hψ, h, Submodule.coe_smul_of_tower, natCast_zsmul]
  choose yf hyf using hc
  let b := (Module.Free.chooseBasis ℤ L).reindex (Fintype.equivFin (Module.Free.ChooseBasisIndex ℤ L))
  let A := LinearMap.toMatrixAlgEquiv b ψ
  let B : Matrix (Fin (Fintype.card (Module.Free.ChooseBasisIndex ℤ L)))
      (Fin (Fintype.card (Module.Free.ChooseBasisIndex ℤ L))) ℤ :=
    Matrix.of fun i j => b.repr (yf (b j)) i
  have hAn : A ^ n = 1 := by
    show (LinearMap.toMatrixAlgEquiv b ψ) ^ n = 1
    rw [← map_pow, hψn, map_one]
  have hAB : A = 1 + (g : ℤ) • B := by
    ext i j
    show (LinearMap.toMatrixAlgEquiv b ψ) i j = _
    rw [LinearMap.toMatrixAlgEquiv_apply]
    have h := hyf (b j)
    rw [sub_eq_iff_eq_add'] at h
    rw [h, map_add, map_zsmul, Finsupp.add_apply, Finsupp.smul_apply, Module.Basis.repr_self,
      Finsupp.single_apply]
    simp [B, Matrix.one_apply, eq_comm]
  have hA1 := Formalism.HermitianLatticeCounting.P.finite_order_congruence _ n (g : ℤ) A B (by exact_mod_cast hg) hn hAn hAB
  have hψ1 : ψ = 1 := by
    apply (LinearMap.toMatrixAlgEquiv b).injective
    rw [map_one]
    exact hA1
  intro x hx
  have := congrArg (fun f : L →ₗ[ℤ] L => ((f ⟨x, hx⟩ : L) : Q)) hψ1
  simpa [hψ] using this

end Q4

end PI.UnitaryGroupMassFormula.BetaModX

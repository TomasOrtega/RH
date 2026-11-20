import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.WeakApproximationFinitePlace
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.JacobiMapsExist
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.UnitaryUnnSubgroupEqTopOfLeviUnipotentWeylStatement

noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open IsDedekindDomain NumberField

open GlobalTheory.CompanionTheory.JacobiMaps GlobalTheory.StdUnn.Model

namespace PositivityTheory.Rg.Rsw.L.UnitaryGroupMatrix

variable {D : D7} {n : ℕ}

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem matG_mul (g h : G D n) : mat (g * h) = mat g * mat h := rfl

/- English proof (translation)
Apply `Subtype.ext` to reduce the goal to its premises. Apply `Units.ext` to reduce the goal to its premises. Conclude with `e`.
-/
theorem matG_ext {g h : G D n} (e : mat g = mat h) : g = h := by
  apply Subtype.ext; apply Units.ext; exact e

/- English proof (translation)
Establish `e : mat g⁻¹ * mat g = 1`. Rewrite using `[← matG_mul, inv_mul_cancel]`. Both sides reduce to the same expression. Combine the equalities or inequalities in the displayed calculation.
-/
theorem matG_inv {g : G D n} {M : Mx D (n + n) (n + n)} (h : mat g * M = 1) : mat g⁻¹ = M := by
  have e : mat g⁻¹ * mat g = 1 := by
    rw [← matG_mul, inv_mul_cancel]; rfl
  calc mat g⁻¹ = mat g⁻¹ * (mat g * M) := by rw [h, Matrix.mul_one]
    _ = M := by rw [← Matrix.mul_assoc, e, Matrix.one_mul]

/- English proof (translation)
Simplify using `only [adj, Matrix.map_mul, Matrix.transpose_mul]`.
-/
theorem adjM_mul {a b c : ℕ} (x : Mx D a b) (y : Mx D b c) : adj (x * y) = adj y * adj x := by
  simp only [adj, Matrix.map_mul, Matrix.transpose_mul]

/- English proof (translation)
Simplify using `only [adj, Matrix.map_one _ (map_zero _) (map_one _), Matrix.transpose_one]`.
-/
theorem adjM_one {a : ℕ} : adj (1 : Mx D a a) = 1 := by
  simp only [adj, Matrix.map_one _ (map_zero _) (map_one _), Matrix.transpose_one]

end PositivityTheory.Rg.Rsw.L.UnitaryGroupMatrix

namespace PositivityTheory.Rg.Rsw.L

open UnitaryGroupMatrix in

/- English proof (translation)
Introduce `D n A _ h1 hA`. Set `S : Subgroup (G D n)` to `{ carrier := {g | (∀ x ∈ A, g * x ∈ A) ∧ ∀ x ∈ A, g⁻¹ * x ∈ A} mul_mem' := fun {g h} hg hh => ⟨fun x hx => by rw [mul_assoc]; exact hg.1 _ (hh.1 x hx), fun x hx => by rw [mul_inv_rev, mul_assoc]; exact hh.2 _ (hg.2 x hx)⟩ one_mem' := ⟨fun x hx => by rwa [one_mul], fun x hx => by …`. Establish `hS : S = ⊤`. Use `GlobalTheory.T.unitaryUnn_subgroup_eq_top_of_leviUnipotentWeyl D n S ?_ ?_ ?_` and prove the remaining obligations. Introduce `g a hg`.

Use `⟨hA g (Or.inr (Or.inl ⟨a, hg⟩)), hA g⁻¹ (Or.inr (Or.inl ⟨a⁻¹, ?_⟩))⟩` and prove the remaining obligations. Rewrite using `[inv_inv]`. Apply `matG_inv` to reduce the goal to its premises. Rewrite using `[hg, submatrix_fromBlocks_mul]`. Simplify using `only [mul_zero, zero_mul, add_zero, zero_add]`.

Rewrite using `[← adjM_mul, a.mul_inv, adjM_one, block_matrix_one]`. Introduce `g b hg`. Use `⟨hA g (Or.inl ⟨b, hg⟩), hA g⁻¹ (Or.inl ⟨-b, ?_⟩)⟩` and prove the remaining obligations. Apply `matG_inv` to reduce the goal to its premises. Rewrite using `[hg, submatrix_fromBlocks_mul]`.

Simplify using `[block_matrix_one]`. Introduce `g hg`. Establish `e : g⁻¹ = g * (g * g)`. Apply `matG_ext` to reduce the goal to its premises. Rewrite using `[matG_inv (M := blk4 0 (-1) 1 0), matG_mul, matG_mul, hg, submatrix_fromBlocks_mul, submatrix_fromBlocks_mul]`.

Simplify using the standard rewrite rules. Rewrite using `[hg, submatrix_fromBlocks_mul]`. Simplify using `[block_matrix_one]`. Establish `hw` using `hA g (Or.inr (Or.inr hg))`. Use `⟨hw, fun x hx => ?_⟩` and prove the remaining obligations.

Rewrite using `[e, mul_assoc, mul_assoc]`. Conclude with `hw _ (hw _ (hw x hx))`. Use extensionality with `g`. Simplify using `only [Set.mem_univ, iff_true]`. Establish `hg : g ∈ S` using `hS ▸ Subgroup.mem_top g`.

Simplify using `using hg.1 1 h1`.
-/
theorem geng : GenG := by
  intro D n A _ h1 hA
  let S : Subgroup (G D n) :=
    { carrier := {g | (∀ x ∈ A, g * x ∈ A) ∧ ∀ x ∈ A, g⁻¹ * x ∈ A}
      mul_mem' := fun {g h} hg hh =>
        ⟨fun x hx => by rw [mul_assoc]; exact hg.1 _ (hh.1 x hx),
         fun x hx => by rw [mul_inv_rev, mul_assoc]; exact hh.2 _ (hg.2 x hx)⟩
      one_mem' := ⟨fun x hx => by rwa [one_mul], fun x hx => by rwa [inv_one, one_mul]⟩
      inv_mem' := fun {g} hg => ⟨hg.2, fun x hx => by rw [inv_inv]; exact hg.1 x hx⟩ }
  have hS : S = ⊤ := by
    refine GlobalTheory.T.unitaryUnn_subgroup_eq_top_of_leviUnipotentWeyl D n S ?_ ?_ ?_
    · intro g a hg
      refine ⟨hA g (Or.inr (Or.inl ⟨a, hg⟩)), hA g⁻¹ (Or.inr (Or.inl ⟨a⁻¹, ?_⟩))⟩
      rw [inv_inv]
      apply matG_inv
      rw [hg, submatrix_fromBlocks_mul]
      simp only [mul_zero, zero_mul, add_zero, zero_add]
      rw [← adjM_mul, a.mul_inv, adjM_one, block_matrix_one]
    · intro g b hg
      refine ⟨hA g (Or.inl ⟨b, hg⟩), hA g⁻¹ (Or.inl ⟨-b, ?_⟩)⟩
      apply matG_inv
      rw [hg, submatrix_fromBlocks_mul]
      simp [block_matrix_one]
    · intro g hg
      have e : g⁻¹ = g * (g * g) := by
        apply matG_ext
        rw [matG_inv (M := blk4 0 (-1) 1 0), matG_mul, matG_mul, hg, submatrix_fromBlocks_mul, submatrix_fromBlocks_mul]
        · simp
        · rw [hg, submatrix_fromBlocks_mul]; simp [block_matrix_one]
      have hw := hA g (Or.inr (Or.inr hg))
      refine ⟨hw, fun x hx => ?_⟩
      rw [e, mul_assoc, mul_assoc]
      exact hw _ (hw _ (hw x hx))
  ext g
  simp only [Set.mem_univ, iff_true]
  have hg : g ∈ S := hS ▸ Subgroup.mem_top g
  simpa using hg.1 1 h1

end PositivityTheory.Rg.Rsw.L

end

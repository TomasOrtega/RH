import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.LeftEquivariantFunctions.ComplexMatrixCalculus.ExtraSt
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.LeftEquivariantFunctions.ComplexMatrixCalculus.ContractionDerivatives.ToLinSmulOne
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.LeftEquivariantFunctions.ComplexMatrixCalculus.ContractionDerivatives.DerTop
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.LeftEquivariantFunctions.ComplexMatrixCalculus.ConjugateTransposeDerivatives.TraceSingleMulSingle

noncomputable section

open Matrix
open scoped ComplexConjugate

namespace PositivityTheory.RgBcC.Cxi

open PositivityTheory.RgBcC
open PositivityTheory.RgTw (Mat hb)

variable {n : ℕ}

/- English proof (translation)
Rewrite using `[ExteriorAlgebra.map_apply_ιMulti]`. Establish `h : (⇑(Matrix.toLin' (diagonal v)) ∘ fun i => Pi.single (e i) (1 : ℂ)) = fun i => v (e i) • Pi.single (e i) (1 : ℂ)`. Use function extensionality and compare the values at `i`. Use extensionality with `j`. Simplify using `[Matrix.toLin'_apply, Pi.single_apply, diagonal_apply]`.

Rewrite using `[h, AlternatingMap.map_smul_univ]`.
-/
theorem map_diag_ιMulti {k : ℕ} (v : Md n → ℂ) (e : Fin k → Md n) :
    ExteriorAlgebra.map (Matrix.toLin' (diagonal v)) (ExteriorAlgebra.ιMulti ℂ k fun i => Pi.single (e i) (1 : ℂ)) =
      (∏ i, v (e i)) • ExteriorAlgebra.ιMulti ℂ k fun i => Pi.single (e i) (1 : ℂ) := by
  rw [ExteriorAlgebra.map_apply_ιMulti]
  have h : (⇑(Matrix.toLin' (diagonal v)) ∘ fun i => Pi.single (e i) (1 : ℂ)) =
      fun i => v (e i) • Pi.single (e i) (1 : ℂ) := by
    funext i
    ext j
    simp [Matrix.toLin'_apply, Pi.single_apply, diagonal_apply]
  rw [h, AlternatingMap.map_smul_univ]

/- English proof (translation)
Establish `hb : (⇑(Pi.basisFun ℂ (Md n)) ∘ ⇑(Set.powersetCard.ofFinEmbEquiv.symm s)) = fun i => Pi.single (Set.powersetCard.ofFinEmbEquiv.symm s i) (1 : ℂ)`. Use function extensionality and compare the values at `i`. Simplify using the standard rewrite rules. Establish `hs : s.val = Finset.univ.map (Set.powersetCard.ofFinEmbEquiv.symm s).toEmbedding`. Use extensionality with `m`.

Use `Set.powersetCard.mem_range_ofFinEmbEquiv_symm_iff_mem s m` as an intermediate fact. Simplify using `only [Set.mem_range] at this`. Simplify using `only [Finset.mem_map, Finset.mem_univ, true_and, RelEmbedding.coe_toEmbedding, this]`. Use `first`. Consider the case `rfl`.

Consider the case `exact Iff.rfl`. Establish `hp : ∏ i, v (Set.powersetCard.ofFinEmbEquiv.symm s i) = ∏ m ∈ s.val, v m`. Rewrite using `[hs, Finset.prod_map]`. Both sides reduce to the same expression. Simplify using `only [ExteriorAlgebra.ιMulti_family]`.

Rewrite using `[hb, map_diag_ιMulti, hp]`.
-/
private theorem exteriorAlgebra_map_diagonal_ιMulti_eq_prod_smul (v : Md n → ℂ) {k : ℕ} (s : Set.powersetCard (Md n) k) :
    ExteriorAlgebra.map (Matrix.toLin' (diagonal v))
        (ExteriorAlgebra.ιMulti_family ℂ k (Pi.basisFun ℂ (Md n)) s) =
      (∏ m ∈ s.val, v m) • ExteriorAlgebra.ιMulti_family ℂ k (Pi.basisFun ℂ (Md n)) s := by
  have hb : (⇑(Pi.basisFun ℂ (Md n)) ∘ ⇑(Set.powersetCard.ofFinEmbEquiv.symm s)) =
      fun i => Pi.single (Set.powersetCard.ofFinEmbEquiv.symm s i) (1 : ℂ) := by
    funext i
    simp
  have hs : s.val = Finset.univ.map (Set.powersetCard.ofFinEmbEquiv.symm s).toEmbedding := by
    ext m
    have := Set.powersetCard.mem_range_ofFinEmbEquiv_symm_iff_mem s m
    simp only [Set.mem_range] at this
    simp only [Finset.mem_map, Finset.mem_univ, true_and, RelEmbedding.coe_toEmbedding, this]
    first
      | rfl
      | exact Iff.rfl
  have hp : ∏ i, v (Set.powersetCard.ofFinEmbEquiv.symm s i) = ∏ m ∈ s.val, v m := by
    rw [hs, Finset.prod_map]
    rfl
  simp only [ExteriorAlgebra.ιMulti_family]
  rw [hb, map_diag_ιMulti, hp]

/- English proof (translation)
Establish `key : ∀ B : Finset (Md n), ExteriorAlgebra.map (toLin' (diagonal v)) (fb n B) = (∏ m ∈ B, v m) • fb n B`. Introduce `B`. Establish `h1 : fb n B = ExteriorAlgebra.ιMulti_family ℂ B.card (Pi.basisFun ℂ (Md n)) (Set.powersetCard.ofCard (s` using `B) rfl) := ExteriorAlgebra.basis_apply _ B`. Rewrite using `[h1]`. Conclude with `exteriorAlgebra_map_diagonal_ιMulti_eq_prod_smul v _`.

Use extensionality with `A B`. Express the relevant statement in the definitionally equal form `(LinearMap.toMatrix (fb n) (fb n) (ExteriorAlgebra.map (toLin' (diagonal v))).toLinearMap) A B = _`. Rewrite using `[LinearMap.toMatrix_apply]`. Express the relevant statement in the definitionally equal form `(fb n).repr (ExteriorAlgebra.map (toLin' (diagonal v)) (fb n B)) A = _`. Rewrite using `[key, map_smul, Module.Basis.repr_self, diagonal_apply]`.

Simplify using `only [Finsupp.smul_apply, Finsupp.single_apply, smul_eq_mul, mul_ite, mul_one, mul_zero]`. Use `split_ifs with h1 h2 h2`. Substitute `h1` using the available equality. Both sides reduce to the same expression. Conclude with `absurd h1.symm h2`.

Conclude with `absurd h2.symm h1`. Both sides reduce to the same expression.
-/
theorem gam_diag (v : Md n → ℂ) : gamM (diagonal v) = diagonal fun A : Finset (Md n) => ∏ m ∈ A, v m := by
  have key : ∀ B : Finset (Md n),
      ExteriorAlgebra.map (toLin' (diagonal v)) (fb n B) = (∏ m ∈ B, v m) • fb n B := by
    intro B
    have h1 : fb n B = ExteriorAlgebra.ιMulti_family ℂ B.card (Pi.basisFun ℂ (Md n))
        (Set.powersetCard.ofCard (s := B) rfl) := ExteriorAlgebra.basis_apply _ B
    rw [h1]
    exact exteriorAlgebra_map_diagonal_ιMulti_eq_prod_smul v _
  ext A B
  change (LinearMap.toMatrix (fb n) (fb n)
    (ExteriorAlgebra.map (toLin' (diagonal v))).toLinearMap) A B = _
  rw [LinearMap.toMatrix_apply]
  change (fb n).repr (ExteriorAlgebra.map (toLin' (diagonal v)) (fb n B)) A = _
  rw [key, map_smul, Module.Basis.repr_self, diagonal_apply]
  simp only [Finsupp.smul_apply, Finsupp.single_apply, smul_eq_mul, mul_ite, mul_one, mul_zero]
  split_ifs with h1 h2 h2
  · subst h1
    rfl
  · exact absurd h1.symm h2
  · exact absurd h2.symm h1
  · rfl

/- English proof (translation)
Rewrite using `[gam_diag, trace_diagonal, Finset.prod_one_add, Finset.powerset_univ]`.
-/
theorem trace_gam_diag (v : Md n → ℂ) : (gamM (diagonal v)).trace = ∏ m, (1 + v m) := by
  rw [gam_diag, trace_diagonal, Finset.prod_one_add, Finset.powerset_univ]

end PositivityTheory.RgBcC.Cxi

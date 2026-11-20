import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BrPairFApply
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.InfClassAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniqueIsFunForm
import Formalism.SharpRestriction.Divisibility.PrimeDegreeVariant
import Formalism.PieriBlockIdeals.StatementLA
import Formalism.MirabolicMackeyTheory.MirabolicMackeyProofs.RamBasic
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.FormulaAt
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.CsGlob

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim GlobalTheory.TestLat GlobalTheory.SumSize
open Formalism.DivisionValues (vw lw)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

/- English proof (translation)
Set `e : (n → K) ≃ₗ[K] (n → K)` to `LinearEquiv.ofLinear g.1.mulVecLin (g⁻¹).1.mulVecLin (by rw [← Matrix.mulVecLin_mul, Units.mul_inv, Matrix.mulVecLin_one]) (by rw [← Matrix.mulVecLin_mul, Units.inv_mul, Matrix.mulVecLin_one])`. Establish `h : M.comap (g.1.mulVecLin.restrictScalars R) = M.map ((e.symm : (n → K) →ₗ[K] (n → K)).restrictScalars R)`. Use extensionality with `x`. Prove the components needed by the constructor for the conclusion. Introduce `hx`.

Conclude with `⟨e x, hx, e.symm_apply_apply x⟩`. Introduce and unpack `⟨y, hy, rfl⟩`. Establish `: e (e.symm y) ∈ M` using `by rw [e.apply_symm_apply]; exact hy`. Conclude with `this`. Rewrite using `[h]`.

Use `⟨hM.fg.map _, ?_⟩` and prove the remaining obligations. Establish `h2 : ((M.map ((e.symm : (n → K) →ₗ[K] (n → K)).restrictScalars R) : Submodule R (n → K)) : Set (n → K)) = (e.symm : (n → K) →ₗ[K] (n → K)) '' (M : Set (n → K))` using `rfl`. Rewrite using `[h2, ← Submodule.map_span, hM.span_eq_top, Submodule.map_top, LinearEquiv.range]`.
-/
private theorem isLattice_comap_gl {R K : Type} [CommRing R] [Field K] [Algebra R K] {n : Type} [Fintype n] [DecidableEq n]
    (g : GL n K) (M : Submodule R (n → K)) (hM : Submodule.IsLattice K M) :
    Submodule.IsLattice K (M.comap (g.1.mulVecLin.restrictScalars R)) := by
  let e : (n → K) ≃ₗ[K] (n → K) := LinearEquiv.ofLinear g.1.mulVecLin (g⁻¹).1.mulVecLin
    (by rw [← Matrix.mulVecLin_mul, Units.mul_inv, Matrix.mulVecLin_one])
    (by rw [← Matrix.mulVecLin_mul, Units.inv_mul, Matrix.mulVecLin_one])
  have h : M.comap (g.1.mulVecLin.restrictScalars R) = M.map ((e.symm : (n → K) →ₗ[K] (n → K)).restrictScalars R) := by
    ext x
    constructor
    · intro hx
      exact ⟨e x, hx, e.symm_apply_apply x⟩
    · rintro ⟨y, hy, rfl⟩
      have : e (e.symm y) ∈ M := by rw [e.apply_symm_apply]; exact hy
      exact this
  rw [h]
  refine ⟨hM.fg.map _, ?_⟩
  have h2 : ((M.map ((e.symm : (n → K) →ₗ[K] (n → K)).restrictScalars R) : Submodule R (n → K)) : Set (n → K)) =
      (e.symm : (n → K) →ₗ[K] (n → K)) '' (M : Set (n → K)) := rfl
  rw [h2, ← Submodule.map_span, hM.span_eq_top, Submodule.map_top, LinearEquiv.range]

/- English proof (translation)
Introduce `D T L sc G W S y`. Establish `hm` using `D.R.two_le_m`. Establish `hΛ : Submodule.IsLattice D.host.E (G.Λ (.grid D.R.m D.R.m))` using `(G.isV (X := .grid D.R.m D.R.m) ⟨le_rfl, le_rfl⟩ fun j e => by`. Establish `: D.R.m = 0` using `(Node.grid.inj e).1`. Use the proof step `omega).sd.1`.

Conclude with `isLattice_comap_gl _ _ (Formalism.UG.P.global_lattice_isLattice_holds _ _ _ _ (Module.Finite.iff_fg.2 hΛ.fg) hΛ.span_eq_top _)`.
-/
theorem _root_.GlobalTheory.T.isLattice_vertexLattice_gridCorner : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} (S : GridChoice W Set.univ)
    (y : FinPt G (.grid D.R.m D.R.m)), Submodule.IsLattice D.host.E (GlobalTheory.SumSize.latAt S (.grid D.R.m D.R.m) y) := by
  intro D T L sc G W S y
  have hm := D.R.two_le_m
  have hΛ : Submodule.IsLattice D.host.E (G.Λ (.grid D.R.m D.R.m)) :=
    (G.isV (X := .grid D.R.m D.R.m) ⟨le_rfl, le_rfl⟩ fun j e => by
      have : D.R.m = 0 := (Node.grid.inj e).1
      omega).sd.1
  exact isLattice_comap_gl _ _
    (Formalism.UG.P.global_lattice_isLattice_holds _ _ _ _ (Module.Finite.iff_fg.2 hΛ.fg) hΛ.span_eq_top _)

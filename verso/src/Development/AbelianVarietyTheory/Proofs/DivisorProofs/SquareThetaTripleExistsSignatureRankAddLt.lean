import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SquareTriple
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.UnifModGrowthOfIsUnifModerate

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.Grid

namespace GlobalTheory.FunObj

/- English proof (translation)
Introduce `D T L sc G W t i j hT M hM`. Take `⟨e, Bs, Γ, X, om, om', hX, hY, -⟩` from `hT M hM`. Set `w : InfinitePlace D.host.F` to `Classical.arbitrary _`. Take `⟨hrs, A, hA⟩` from `hY.geo.hV.sig w`. Take `⟨τ, hτ, -⟩` from `hX.cart w`.

Use `⟨Γ.p, ⟨τ, ?_⟩, ?_⟩` and prove the remaining obligations. Establish `hJ : Γ.V.J.map (Bs.emb w).1 = (gramAt D (G.V (.grid (↑i + 1) (↑j + 1))) τ).map (starRingEnd ℂ)`. Use extensionality with `k l`. Simplify using `[hX.JW, hτ, gramAt]`. Rewrite `hA` using `[hJ]`.

Generalize the expression as in `gramAt D (G.V (.grid (↑i + 1) (↑j + 1))) τ = J at hA ⊢`. Establish `h' : (A.map (starRingEnd ℂ))ᵀ * J * A = Matrix.fromBlocks 1 0 0 (-1)`. Use `congrArg (fun Z => Z.map (starRingEnd ℂ)) hA` as an intermediate fact. Simplify using `only [Matrix.map_mul, Matrix.transpose_map] at this`. Establish `e1 : (J.map (starRingEnd ℂ)).map (starRingEnd ℂ) = J` using `by ext; simp`.

Establish `e2 : (A.map star).map (starRingEnd ℂ) = A` using `by ext; simp`. Establish `e3 : (Matrix.fromBlocks 1 0 0 (-1) : Matrix (Fin ((G.V (.grid (↑i + 1) (↑j + 1))).rank - Γ.p) ⊕ Fin Γ.p) (Fin ((G.V (.grid (↑i + 1) (↑j + 1))).rank - Γ.p) ⊕ Fin Γ.p) ℂ).map (starRingEnd ℂ) = Matrix.fromBlocks 1 0 0 (-1)`. Apply the tactic sequence `ext (k | k) (l | l) <;> simp [Matrix.fromBlocks_map, Matrix.one_apply] <;> split_ifs <;> simp`. Rewrite `this` using `[e1, e2, e3]`. Simplify `this` using `only [Matrix.transpose_map]`.

Set `f : Fin (G.V (.grid (↑i + 1) (↑j + 1))).rank ≃ Fin ((G.V (.grid (↑i + 1) (↑j + 1))).rank - Γ.p) ⊕ Fin Γ.p` to `(finSumFinEquiv.trans (finCongr hrs)).symm`. Set `P : Matrix (Fin ((G.V (.grid (↑i + 1) (↑j + 1))).rank - Γ.p) ⊕ Fin Γ.p) (Fin ((G.V (.grid (↑i + 1) (↑j + 1))).rank - Γ.p) ⊕ Fin Γ.p) ℂ` to `A.submatrix f.symm id`. Establish `hP : Formalism.UG.cT (starRingEnd ℂ) P * J.reindex f f * P = Formalism.UG.Jpq ((G.V (.grid (↑i + 1) (↑j + 1))).rank - Γ.p) Γ.p`. Establish `: Formalism.UG.cT (starRingEnd ℂ) P = (A.map (starRingEnd ℂ))ᵀ.submatrix id f.symm`. Use extensionality with `k l`.

Both sides reduce to the same expression. Rewrite using `[this, Matrix.reindex_apply, Matrix.submatrix_mul_equiv, Matrix.submatrix_mul_equiv, h']`. Both sides reduce to the same expression. Establish `hJJ : Formalism.UG.Jpq ((G.V (.grid (↑i + 1) (↑j + 1))).rank - Γ.p) Γ.p * Formalism.UG.Jpq ((G.V (.grid (↑i + 1) (↑j + 1))).rank - Γ.p) Γ.p = 1`. Simplify using `[Formalism.UG.Jpq, Matrix.fromBlocks_multiply]`.

Establish `hl : (Formalism.UG.Jpq ((G.V (.grid (↑i + 1) (↑j + 1))).rank - Γ.p) Γ.p * (Formalism.UG.cT (starRingEnd ℂ) P * J.reindex f f)) * P = 1`. Rewrite using `[Matrix.mul_assoc, hP, hJJ]`. Conclude with `⟨f, ⟨P, _, mul_eq_one_comm.mp hl, hl⟩, hP⟩`. Establish `h1` using `Fintype.card_congr e`. Simplify using `only [Fintype.card_sum, Fintype.card_fin] at h1`.

Establish `h2` using `hY.geo.lt`. Establish `h3` using `hY.geo.eBig`. Simplify using `only [GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.spV₁, GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.spW₁, GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.spW, GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.spV] at h1 h2 h3`. Use linear arithmetic over natural numbers and integers.
-/
theorem squareTriple_sig_rank_lt : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc}
    (W : G.Weil) (t : T) (i j : Fin D.R.m) (hT : SquareTriple W t i j) (M : Vol G) (hM : M.Is t),
    ∃ p : ℕ, (∃ τ, Formalism.UG.HasSignature (gramAt D (G.V (.grid (i + 1) (j + 1))) τ) ((G.V (.grid (i + 1) (j + 1))).rank - p) p) ∧
      (G.V (.grid i (j + 1))).rank + (G.V (.grid (i + 1) j)).rank < 2 * ((G.V (.grid (i + 1) (j + 1))).rank - p) := by
  intro D T L sc G W t i j hT M hM
  obtain ⟨e, Bs, Γ, X, om, om', hX, hY, -⟩ := hT M hM
  let w : InfinitePlace D.host.F := Classical.arbitrary _
  obtain ⟨hrs, A, hA⟩ := hY.geo.hV.sig w
  obtain ⟨τ, hτ, -⟩ := hX.cart w
  refine ⟨Γ.p, ⟨τ, ?_⟩, ?_⟩
  · have hJ : Γ.V.J.map (Bs.emb w).1 = (gramAt D (G.V (.grid (↑i + 1) (↑j + 1))) τ).map (starRingEnd ℂ) := by
      ext k l
      simp [hX.JW, hτ, gramAt]
    rw [hJ] at hA
    generalize gramAt D (G.V (.grid (↑i + 1) (↑j + 1))) τ = J at hA ⊢
    have h' : (A.map (starRingEnd ℂ))ᵀ * J * A = Matrix.fromBlocks 1 0 0 (-1) := by
      have := congrArg (fun Z => Z.map (starRingEnd ℂ)) hA
      simp only [Matrix.map_mul, Matrix.transpose_map] at this
      have e1 : (J.map (starRingEnd ℂ)).map (starRingEnd ℂ) = J := by ext; simp
      have e2 : (A.map star).map (starRingEnd ℂ) = A := by ext; simp
      have e3 : (Matrix.fromBlocks 1 0 0 (-1) : Matrix (Fin ((G.V (.grid (↑i + 1) (↑j + 1))).rank - Γ.p) ⊕ Fin Γ.p) (Fin ((G.V (.grid (↑i + 1) (↑j + 1))).rank - Γ.p) ⊕ Fin Γ.p) ℂ).map
          (starRingEnd ℂ) = Matrix.fromBlocks 1 0 0 (-1) := by
        ext (k | k) (l | l) <;> simp [Matrix.fromBlocks_map, Matrix.one_apply] <;> split_ifs <;> simp
      rw [e1, e2, e3] at this
      simpa only [Matrix.transpose_map] using this
    let f : Fin (G.V (.grid (↑i + 1) (↑j + 1))).rank ≃ Fin ((G.V (.grid (↑i + 1) (↑j + 1))).rank - Γ.p) ⊕ Fin Γ.p := (finSumFinEquiv.trans (finCongr hrs)).symm
    let P : Matrix (Fin ((G.V (.grid (↑i + 1) (↑j + 1))).rank - Γ.p) ⊕ Fin Γ.p) (Fin ((G.V (.grid (↑i + 1) (↑j + 1))).rank - Γ.p) ⊕ Fin Γ.p) ℂ := A.submatrix f.symm id
    have hP : Formalism.UG.cT (starRingEnd ℂ) P * J.reindex f f * P = Formalism.UG.Jpq ((G.V (.grid (↑i + 1) (↑j + 1))).rank - Γ.p) Γ.p := by
      have : Formalism.UG.cT (starRingEnd ℂ) P = (A.map (starRingEnd ℂ))ᵀ.submatrix id f.symm := by
        ext k l; rfl
      rw [this, Matrix.reindex_apply, Matrix.submatrix_mul_equiv, Matrix.submatrix_mul_equiv, h']
      rfl
    have hJJ : Formalism.UG.Jpq ((G.V (.grid (↑i + 1) (↑j + 1))).rank - Γ.p) Γ.p * Formalism.UG.Jpq ((G.V (.grid (↑i + 1) (↑j + 1))).rank - Γ.p) Γ.p = 1 := by
      simp [Formalism.UG.Jpq, Matrix.fromBlocks_multiply]
    have hl : (Formalism.UG.Jpq ((G.V (.grid (↑i + 1) (↑j + 1))).rank - Γ.p) Γ.p * (Formalism.UG.cT (starRingEnd ℂ) P * J.reindex f f)) * P = 1 := by
      rw [Matrix.mul_assoc, hP, hJJ]
    exact ⟨f, ⟨P, _, mul_eq_one_comm.mp hl, hl⟩, hP⟩
  · have h1 := Fintype.card_congr e
    simp only [Fintype.card_sum, Fintype.card_fin] at h1
    have h2 := hY.geo.lt
    have h3 := hY.geo.eBig
    simp only [GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.spV₁, GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.spW₁, GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.spW, GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.spV] at h1 h2 h3
    omega

end GlobalTheory.FunObj

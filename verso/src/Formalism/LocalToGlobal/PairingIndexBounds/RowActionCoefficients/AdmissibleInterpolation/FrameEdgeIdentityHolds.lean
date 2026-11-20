import Formalism.LocalToGlobal.PairingIndexBounds.RowActionCoefficients.NumericalIdentityScalar
import Formalism.LocalToGlobal.GroupLattices.FockModels.TestSideEdge

open MvPolynomial

noncomputable section

namespace Formalism.L2.PairingIndexBounds.Ent

open Formalism.GradedWeylDivisibility Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend

attribute [local instance] Formalism.MainNotions.G.GAtP.ringO Formalism.MainNotions.G.GAtP.domO Formalism.MainNotions.G.GAtP.dvrO Formalism.MainNotions.G.GAtP.fieldK
  Formalism.MainNotions.G.GAtP.algOK

variable {p : ℕ} [Fact p.Prime] (X : Sys p)

def dgQ (K : Type) [Field K] (p k r : ℕ) : Matrix (Fin k) (Fin k) K := Matrix.diagonal fun c => if c.val < r then (p : K)⁻¹ else 1

/- English proof (translation)
Unfold `dgQ`. Rewrite using `[Matrix.det_diagonal]`. Use `Finset.prod_ne_zero_iff.2 fun c _ => ?_` and prove the remaining obligations. Use `split_ifs`. Conclude with `inv_ne_zero hp`.

Conclude with `one_ne_zero`.
-/
theorem dgQ_det_ne (K : Type) [Field K] (p k r : ℕ) (hp : (p : K) ≠ 0) : (dgQ K p k r).det ≠ 0 := by
  unfold dgQ
  rw [Matrix.det_diagonal]
  refine Finset.prod_ne_zero_iff.2 fun c _ => ?_
  split_ifs
  · exact inv_ne_zero hp
  · exact one_ne_zero

/- English proof (translation)
Unfold `mF dgQ DgX`. Use extensionality with `a c`. Simplify using `only [Matrix.submatrix_apply, Matrix.map_apply, Matrix.diagonal_apply]`. Distinguish the cases in `hac : a = c`. Substitute `hac` using the available equality.

Rewrite using `[if_pos rfl, if_pos rfl]`. Establish `: ((finCongr (rank_eq X (j + 1)).symm) a).val = a.val` using `rfl`. Rewrite using `[this]`. Use `split_ifs`. Rewrite using `[map_inv₀, map_inv₀, map_natCast, map_natCast]`.

Rewrite using `[map_one, map_one]`. Rewrite using `[if_neg hac, if_neg (fun h => hac ((finCongr (rank_eq X (j + 1)).symm).injective h)), map_zero, map_zero]`.
-/
theorem mF_dgQ (j : ℕ) (b : BX X) (i0 : X.Pl → ℕ) :
    mF X (j + 1) b (dgQ (X.G.P.Qq b.1) p _ (i0 b.1)) = DgX X X.G.Kf j i0 b.1 := by
  unfold mF dgQ DgX
  ext a c
  simp only [Matrix.submatrix_apply, Matrix.map_apply, Matrix.diagonal_apply]
  by_cases hac : a = c
  · subst hac
    rw [if_pos rfl, if_pos rfl]
    have : ((finCongr (rank_eq X (j + 1)).symm) a).val = a.val := rfl
    rw [this]
    split_ifs
    · rw [map_inv₀, map_inv₀, map_natCast, map_natCast]
    · rw [map_one, map_one]
  · rw [if_neg hac, if_neg (fun h => hac ((finCongr (rank_eq X (j + 1)).symm).injective h)), map_zero, map_zero]

/- English proof (translation)
Introduce `p _ X j L' L'' i0 h2 h4`. Establish `key : ∀ v : X.Pl, ∃ g' h' : GL (Fin ((X.Pj (j + 1)).m + 1)) (X.G.P.Qq v), X.latAt v (j + 1) L'' = colSpan (X.G.P.W v) (g' : Matrix _ _ (X.G.P.Qq v)) ∧ X.latAt v (j + 1) L' = colSpan (X.G.P.W v) (h' : Matrix _ _ (X.G.P.Qq v)) ∧ (h' : Matrix (Fin ((X.Pj (j + 1)).m + 1)) (Fin ((X.Pj …`. Introduce `v`. Establish `hS` using `X.G.P.setting v`. Use `hS.frac_alt` as an intermediate fact.

Establish `hp0 : (p : X.G.P.Qq v) ≠ 0` using `pQ_ne hS.p_unif`. Break down `h4 v with ⟨h0, hL⟩ | ⟨_, he⟩` into its components or cases. Take `⟨g, hg, hgL⟩` from `h2 v`. Establish `h0' : i0 v = 0` using `h0`. Use `⟨Matrix.nonsingInvUnit g hg, Matrix.nonsingInvUnit g hg, ?_, hgL, ?_⟩` and prove the remaining obligations.

Use `show L'' v = _`. Rewrite using `[hL]`. Conclude with `hgL`. Establish `: dgQ (X.G.P.Qq v) p ((X.Pj (j + 1)).m + 1) (i0 v) = 1`. Unfold `dgQ`.

Rewrite using `[h0']`. Simplify using the standard rewrite rules. Rewrite using `[this, mul_one]`. Take `⟨g, hg, hsrc, htgt⟩` from `Formalism.L2.G.Model.edgeBasis hS _ _ _ he`. Establish `hd : IsUnit (g * dgQ (X.G.P.Qq v) p ((X.Pj (j + 1)).m + 1) (i0 v)).det`.

Rewrite using `[Matrix.det_mul]`. Conclude with `hg.mul (isUnit_iff_ne_zero.2 (dgQ_det_ne _ _ _ _ hp0))`. Conclude with `⟨Matrix.nonsingInvUnit g hg, Matrix.nonsingInvUnit _ hd, hsrc, htgt, rfl⟩`. Use `choose g' h' h1 h2' h3 using key`. Use `⟨g', h', h1, h2', fun b => ?_⟩` and prove the remaining obligations.

Rewrite using `[h3 b.1, ← mF_dgQ X j b i0]`. Unfold `mF`. Rewrite using `[Matrix.submatrix_mul_equiv]`. Use `congr 1`. Conclude with `Matrix.map_mul (f := (X.G.P.ι b.1).comp (X.G.P.σ b.1 ^ b.2.val : X.G.P.Qq b.1 ≃+* X.G.P.Qq b.1).toRingHom)`.
-/
theorem frame_edge_identity_holds : XEdge := by
  intro p _ X j L' L'' i0 h2 h4
  have key : ∀ v : X.Pl, ∃ g' h' : GL (Fin ((X.Pj (j + 1)).m + 1)) (X.G.P.Qq v),
      X.latAt v (j + 1) L'' = colSpan (X.G.P.W v) (g' : Matrix _ _ (X.G.P.Qq v)) ∧
      X.latAt v (j + 1) L' = colSpan (X.G.P.W v) (h' : Matrix _ _ (X.G.P.Qq v)) ∧
      (h' : Matrix (Fin ((X.Pj (j + 1)).m + 1)) (Fin ((X.Pj (j + 1)).m + 1)) (X.G.P.Qq v)) =
        (g' : Matrix (Fin ((X.Pj (j + 1)).m + 1)) (Fin ((X.Pj (j + 1)).m + 1)) (X.G.P.Qq v)) *
          dgQ (X.G.P.Qq v) p ((X.Pj (j + 1)).m + 1) (i0 v) := by
    intro v
    have hS := X.G.P.setting v
    have := hS.frac_alt
    have hp0 : (p : X.G.P.Qq v) ≠ 0 := pQ_ne hS.p_unif
    rcases h4 v with ⟨h0, hL⟩ | ⟨_, he⟩
    · obtain ⟨g, hg, hgL⟩ := h2 v
      have h0' : i0 v = 0 := h0
      refine ⟨Matrix.nonsingInvUnit g hg, Matrix.nonsingInvUnit g hg, ?_, hgL, ?_⟩
      · show L'' v = _
        rw [hL]; exact hgL
      · have : dgQ (X.G.P.Qq v) p ((X.Pj (j + 1)).m + 1) (i0 v) = 1 := by
          unfold dgQ
          rw [h0']
          simp
        rw [this, mul_one]
    · obtain ⟨g, hg, hsrc, htgt⟩ := Formalism.L2.G.Model.edgeBasis hS _ _ _ he
      have hd : IsUnit (g * dgQ (X.G.P.Qq v) p ((X.Pj (j + 1)).m + 1) (i0 v)).det := by
        rw [Matrix.det_mul]
        exact hg.mul (isUnit_iff_ne_zero.2 (dgQ_det_ne _ _ _ _ hp0))
      exact ⟨Matrix.nonsingInvUnit g hg, Matrix.nonsingInvUnit _ hd, hsrc, htgt, rfl⟩
  choose g' h' h1 h2' h3 using key
  refine ⟨g', h', h1, h2', fun b => ?_⟩
  rw [h3 b.1, ← mF_dgQ X j b i0]
  unfold mF
  rw [Matrix.submatrix_mul_equiv]
  congr 1
  exact Matrix.map_mul (f := (X.G.P.ι b.1).comp (X.G.P.σ b.1 ^ b.2.val : X.G.P.Qq b.1 ≃+* X.G.P.Qq b.1).toRingHom)

end Formalism.L2.PairingIndexBounds.Ent

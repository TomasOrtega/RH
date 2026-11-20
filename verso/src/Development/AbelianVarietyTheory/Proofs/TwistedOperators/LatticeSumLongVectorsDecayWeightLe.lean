import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.DepthPays
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LatticeSumProdNormLeOfProdNormLowerBoundStatement

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.ChainFr GlobalTheory.SepRows GlobalTheory.SepPer Matrix
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SepPer

variable {D : D7}

def compVec (θ : InfFam D) (V : HSp D) (B : Fr V) (g : GA D V) :
    (Fin V.rank → D.host.E) →+ (D.what₂.Tau → EuclideanSpace ℂ (Fin V.rank)) where
  toFun w τ := WithLp.toLp 2 (B.fr τ *ᵥ (cmp θ τ g⁻¹ *ᵥ fun i => tauE D τ (w i)))
  map_zero' := by
    funext τ
    have h : (fun i => tauE D τ ((0 : Fin V.rank → D.host.E) i)) = 0 := by
      funext i; simp
    show WithLp.toLp 2 (B.fr τ *ᵥ (cmp θ τ g⁻¹ *ᵥ fun i => tauE D τ ((0 : Fin V.rank → D.host.E) i))) = 0
    rw [h, Matrix.mulVec_zero, Matrix.mulVec_zero]
    rfl
  map_add' x y := by
    funext τ
    have h : (fun i => tauE D τ ((x + y) i)) = (fun i => tauE D τ (x i)) + fun i => tauE D τ (y i) := by
      funext i; simp
    show WithLp.toLp 2 (B.fr τ *ᵥ (cmp θ τ g⁻¹ *ᵥ fun i => tauE D τ ((x + y) i))) =
      WithLp.toLp 2 (B.fr τ *ᵥ (cmp θ τ g⁻¹ *ᵥ fun i => tauE D τ (x i))) +
        WithLp.toLp 2 (B.fr τ *ᵥ (cmp θ τ g⁻¹ *ᵥ fun i => tauE D τ (y i)))
    rw [h, Matrix.mulVec_add, Matrix.mulVec_add, WithLp.toLp_add]

/- English proof (translation)
Rewrite using `[EuclideanSpace.norm_eq]`. Both sides reduce to the same expression.
-/
theorem norm_compVec (θ : InfFam D) (V : HSp D) (B : Fr V) (g : GA D V) (w : Fin V.rank → D.host.E) (τ : D.what₂.Tau) :
    ‖compVec θ V B g w τ‖ = nrm θ B g τ w := by
  rw [EuclideanSpace.norm_eq]; rfl

/- English proof (translation)
Introduce `D θ V B g L R hn hR hL s hs`. Establish `hnorm : ∀ w τ, ‖compVec θ V B g w τ‖ = nrm θ B g τ w` using `norm_compVec θ V B g`. Distinguish the cases in `hι : IsEmpty D.what₂.Tau`. Establish `hs0 : s = ∅`. Rewrite using `[Finset.eq_empty_iff_forall_notMem]`.

Introduce `w hw`. Establish `h1` using `hL w (hs w hw).1 (hs w hw).2`. Rewrite `h1` using `[Finset.univ_eq_empty, Finset.prod_empty]`. Combine the linear equalities and inequalities to obtain the conclusion. Substitute `hs0` using the available equality.

Rewrite using `[Finset.sum_empty]`. Conclude with `div_nonneg (Real.exp_pos _).le (by linarith)`. Use `haveI : Nonempty D.what₂.Tau := not_isEmpty_iff.mp hι`. Establish `hzero : ∀ w, compVec θ V B g w = 0 → ∏ τ, nrm θ B g τ w = 0`. Introduce `w h0`.

Use `Finset.prod_eq_zero (Finset.mem_univ (Classical.arbitrary _)) ?_` and prove the remaining obligations. Rewrite using `[← hnorm, h0, Pi.zero_apply, norm_zero]`. Establish `hinj : Set.InjOn (compVec θ V B g) (s : Set _)`. Introduce `x hx y hy hxy`. Assume the negation of the conclusion as `hne`.

Establish `hm : x - y ∈ L` using `L.sub_mem (hs x hx).1 (hs y hy).1`. Establish `h1` using `hL _ hm (sub_ne_zero.mpr hne)`. Establish `hz : compVec θ V B g (x - y) = 0` using `by rw [map_sub, hxy, sub_self]`. Rewrite `h1` using `[hzero _ hz]`. Combine the linear equalities and inequalities to obtain the conclusion.

Establish `key` using `GlobalTheory.T.lattice_sum_prod_norm_le_of_prod_norm_lower_bound D.what₂.Tau V.rank (L.toAddSubgroup.map (compVec θ V B g)) R hn hR ?_ (s.image (compVec θ V B g)) ?_`. Rewrite `key` using `[Finset.sum_image hinj]`. Simplify `key` using `only [hnorm]`. Introduce `v hv hv0`. Take `⟨w, hwL, rfl⟩` from `AddSubgroup.mem_map.mp hv`.

Establish `hwL' : w ∈ L` using `hwL`. Establish `hw0 : w ≠ 0` using `by rintro rfl; exact hv0 (map_zero _)`. Simplify `hL w hwL' hw0` using `only [hnorm]`. Introduce `v hv`. Take `⟨w, hw, rfl⟩` from `Finset.mem_image.mp hv`.

Use `⟨AddSubgroup.mem_map_of_mem _ (hs w hw).1, ?_⟩` and prove the remaining obligations. Introduce `h0`. Establish `h1` using `hL w (hs w hw).1 (hs w hw).2`. Rewrite `h1` using `[hzero w h0]`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem latSum_le : ∀ (D : D7) (θ : InfFam D) (V : HSp D) (B : Fr V) (g : GA D V) (L : Lat V) (R : ℝ), 1 ≤ V.rank → 1 < R → (∀ w ∈ L, w ≠ 0 → R ≤ ∏ τ, nrm θ B g τ w) → ∀ s : Finset (Fin V.rank → D.host.E), (∀ w ∈ s, w ∈ L ∧ w ≠ 0) → ∑ w ∈ s, ∏ τ, (((1 + nrm θ B g τ w) / 3) ^ (2 * V.rank + 5))⁻¹ ≤ Real.exp ((6 * (V.rank : ℝ) + 9) * Fintype.card D.what₂.Tau) / R := by
  intro D θ V B g L R hn hR hL s hs
  classical
  have hnorm : ∀ w τ, ‖compVec θ V B g w τ‖ = nrm θ B g τ w := norm_compVec θ V B g
  by_cases hι : IsEmpty D.what₂.Tau
  · have hs0 : s = ∅ := by
      rw [Finset.eq_empty_iff_forall_notMem]
      intro w hw
      have h1 := hL w (hs w hw).1 (hs w hw).2
      rw [Finset.univ_eq_empty, Finset.prod_empty] at h1
      linarith
    subst hs0
    rw [Finset.sum_empty]
    exact div_nonneg (Real.exp_pos _).le (by linarith)
  · haveI : Nonempty D.what₂.Tau := not_isEmpty_iff.mp hι
    have hzero : ∀ w, compVec θ V B g w = 0 → ∏ τ, nrm θ B g τ w = 0 := by
      intro w h0
      refine Finset.prod_eq_zero (Finset.mem_univ (Classical.arbitrary _)) ?_
      rw [← hnorm, h0, Pi.zero_apply, norm_zero]
    have hinj : Set.InjOn (compVec θ V B g) (s : Set _) := by
      intro x hx y hy hxy
      by_contra hne
      have hm : x - y ∈ L := L.sub_mem (hs x hx).1 (hs y hy).1
      have h1 := hL _ hm (sub_ne_zero.mpr hne)
      have hz : compVec θ V B g (x - y) = 0 := by rw [map_sub, hxy, sub_self]
      rw [hzero _ hz] at h1
      linarith
    have key := GlobalTheory.T.lattice_sum_prod_norm_le_of_prod_norm_lower_bound D.what₂.Tau V.rank (L.toAddSubgroup.map (compVec θ V B g)) R hn hR ?_
      (s.image (compVec θ V B g)) ?_
    · rw [Finset.sum_image hinj] at key
      simpa only [hnorm] using key
    · intro v hv hv0
      obtain ⟨w, hwL, rfl⟩ := AddSubgroup.mem_map.mp hv
      have hwL' : w ∈ L := hwL
      have hw0 : w ≠ 0 := by rintro rfl; exact hv0 (map_zero _)
      simpa only [hnorm] using hL w hwL' hw0
    · intro v hv
      obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hv
      refine ⟨AddSubgroup.mem_map_of_mem _ (hs w hw).1, ?_⟩
      intro h0
      have h1 := hL w (hs w hw).1 (hs w hw).2
      rw [hzero w h0] at h1
      linarith

end GlobalTheory.SepPer

end

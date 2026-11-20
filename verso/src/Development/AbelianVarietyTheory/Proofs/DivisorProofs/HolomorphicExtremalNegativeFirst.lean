import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothReal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExtremalVectorAnnihilatedStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiscreteSeriesModelUnitaryIrreducibleOrthonormal
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HolomorphicDiscreteSeries

open NumberField IsDedekindDomain Matrix MeasureTheory ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Pj Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT GlobalTheory.HolRead
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.HolRead

open GlobalTheory.HolDict.ModelRep in

/- English proof (translation)
Introduce `D θ V S M h p q hθ hpq hr hS v hv`. Establish `hn : p + q = V.rank` using `hpq.trans hr.symm`. Establish `hp : p ≤ V.rank` using `by omega`. Establish `he : ∀ ρ, IsEnum (Formalism.L2.NTheta.holPar p q (Formalism.L2.NTheta.kapW (h ρ) p q)) (M.lam ρ) (M.ε ρ)` using `fun ρ => hS ρ ▸ M.enum ρ`. Establish `hok` using `fun ρ => Formalism.L2.NTheta.holOK_kapW (h ρ) p q hpq`.

Establish `hε : ∀ ρ a, M.ε ρ a = decide ((a : ℕ) < p)` using `fun ρ a => by`. Take `⟨hn', hx⟩` from `GlobalTheory.HolDS.enum_holPar (hok ρ) (he ρ)`. Distinguish the cases in `ha : (a : ℕ) < p`. Use `(hx (Sum.inl ⟨a, ha⟩)).2` as an intermediate fact. Rewrite `this` using `[show Fin.cast hn' (finSumFinEquiv (Sum.inl ⟨a, ha⟩ : Fin p ⊕ Fin q)) = a from Fin.ext (by simp)]`.

Simplify using `[this, ha]`. Use `(hx (Sum.inr ⟨a - p, by have := a.2; omega⟩)).2` as an intermediate fact. Rewrite `this` using `[show Fin.cast hn' (finSumFinEquiv (Sum.inr ⟨a - p, by have := a.2; omega⟩ : Fin p ⊕ Fin q)) = a from Fin.ext (by simp; omega)]`. Simplify using `[this, ha]`. Establish `hq : ∀ ρ, nNeg (M.ε ρ) = q` using `fun ρ => by rw [nNeg_shape hp (hε ρ)]; omega`.

Establish `hw : ∀ ρ c, extWt M ρ (arr (nNeg (M.ε ρ)) c) = (wtCol (h ρ) p q c : ℝ)` using `fun ρ c => by`. Take `⟨hn', hx⟩` from `GlobalTheory.HolDS.lowK_holPar (hok ρ) (he ρ)`. Establish `hc` using `c.2`. Distinguish the cases in `hcq : (c : ℕ) < q`. Rewrite using `[extWt_arr M ρ hp (hε ρ) c (Fin.cast hn' (finSumFinEquiv (Sum.inr ⟨c, hcq⟩ : Fin p ⊕ Fin q))) (by rw [if_pos (by omega)]; simp), hx]`.

Simplify using `only [wtCol, if_pos hcq, Formalism.L2.NTheta.kapW, Formalism.L2.NTheta.kapQ, Sum.elim_inr]`. Rewrite using `[extWt_arr M ρ hp (hε ρ) c (Fin.cast hn' (finSumFinEquiv (Sum.inl ⟨c - q, by omega⟩ : Fin p ⊕ Fin q))) (by rw [if_neg (by omega)]; simp; omega), hx]`. Simplify using `only [wtCol, if_neg hcq, Formalism.L2.NTheta.kapW, Formalism.L2.NTheta.kapQ, Sum.elim_inl]`. Establish `hneg : NegFirst V q (x0Mat M)` using `fun ρ => by`. Use `orth_sub (M.fr_unit ρ) (M.fr_gram ρ) (arr (nNeg (M.ε ρ)))` as an intermediate fact.

Use `this.trans ?_` and prove the remaining obligations. Unfold `Formalism.REAL.Jm`. Rewrite using `[Matrix.submatrix_diagonal _ _ (arr_injective (nNeg_le (M.ε ρ)))]`. Use `congr 1`. Use function extensionality and compare the values at `a`.

Use `a.2` as an intermediate fact. Simplify using `only [Function.comp, hε, hq, arr, decide_eq_true_eq]`. Apply the tactic sequence `split_ifs <;> first | rfl | (exfalso; simp only at *; omega)`. Use `⟨x0Mat M, hneg, fun J χ T hT => ⟨(hT.aut v).smooth, fun ρ c d hcd => ?_, fun ρ t g => ?_⟩⟩` and prove the remaining obligations. Apply the tactic sequence `have hk := (GlobalTheory.T.extremal_vector_annihilated D θ V S M J χ T hθ hT v hv ρ p true (fun a => by rw [hε]; by_cases ha : (a : ℕ) < p <;> simp [ha])).1`.

Establish `e` using `conj_single (M.fr_unit ρ) (arrEquiv (nNeg_le (M.ε ρ))) c d`. Express the relevant statement in the definitionally equal form `x0Mat M ρ * _ * (x0Mat M ρ)⁻¹ = _ * Matrix.single (arr (nNeg (M.ε ρ)) c) (arr (nNeg (M.ε ρ)) d) 1 * _ at e`. Rewrite using `[e]`. Apply `hk` to reduce the goal to its premises. Establish `h1 : (c : ℕ) < d` using `hcd`.

Establish `h2` using `d.2`. Simplify using `only [KillPair, hε, hq, arr, Fin.lt_def, decide_eq_true_eq, decide_eq_false_iff_not, ne_eq, decide_eq_decide]`. Apply the tactic sequence `split_ifs <;> simp only <;> omega`. Apply the tactic sequence `have hk := (GlobalTheory.T.extremal_vector_annihilated D θ V S M J χ T hθ hT v hv ρ p true (fun a => by rw [hε]; by_cases ha : (a : ℕ) < p <;> simp [ha])).2 set e := arrEquiv (nNeg_le (M.ε ρ)) with hedef`. Establish `hx : IsUnit (x0Mat M ρ).det`.

Establish `h1` using `congrArg Matrix.det (hneg ρ)`. Rewrite `h1` using `[det_mul, det_diagonal]`. Use `isUnit_iff_ne_zero.2 fun h0 => ?_` and prove the remaining obligations. Rewrite `h1` using `[h0, mul_zero]`. Apply the tactic sequence `exact Finset.prod_ne_zero_iff.2 (fun a _ => by split_ifs <;> simp) h1.symm`.

Establish `h1` using `torus_x0Mat M ρ fun a => Complex.exp ((t (e.symm a) : ℂ) * Complex.I)`. Establish `h2 : ∀ c, e.symm (arr (nNeg (M.ε ρ)) c) = c` using `fun c => e.symm_apply_apply c`. Simplify using `only [h2] at h1`. Rewrite using `[← h1, Matrix.mul_nonsing_inv_cancel_right _ _ hx, hk (fun a => t (e.symm a)) g, ← e.sum_comp]`. Simplify using `only [Equiv.symm_apply_apply]`.

Use `congr 5`. Use function extensionality and compare the values at `c`. Rewrite using `[← hw ρ c]`. Both sides reduce to the same expression.
-/
theorem isHolFor_extVec_holPar : ∀ (D : D7) (θ : InfFam D) (V : HSp D) (S : D.what₂.Tau → SPar) (M : DSModel V S) (h : D.what₂.Tau → HCParam D.R) (p q : ℕ), IsInfFam θ → p + q = D.R.r → V.rank = D.R.r → (∀ ρ, S ρ = Formalism.L2.NTheta.holPar p q (Formalism.L2.NTheta.kapW (h ρ) p q)) → ∀ v : M.Vec, IsExtVec M v → ∃ x : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ, NegFirst V q x ∧ ∀ (J : Set (GA D V)) (χ : GA D V → ℂ) (T : MMap M), IsMultMap θ M J χ T → IsHolFor θ V x (fun ρ c => wtCol (h ρ) p q c) (T v) := by
  intro D θ V S M h p q hθ hpq hr hS v hv
  have hn : p + q = V.rank := hpq.trans hr.symm
  have hp : p ≤ V.rank := by omega
  have he : ∀ ρ, IsEnum (Formalism.L2.NTheta.holPar p q (Formalism.L2.NTheta.kapW (h ρ) p q)) (M.lam ρ) (M.ε ρ) :=
    fun ρ => hS ρ ▸ M.enum ρ
  have hok := fun ρ => Formalism.L2.NTheta.holOK_kapW (h ρ) p q hpq
  have hε : ∀ ρ a, M.ε ρ a = decide ((a : ℕ) < p) := fun ρ a => by
    obtain ⟨hn', hx⟩ := GlobalTheory.HolDS.enum_holPar (hok ρ) (he ρ)
    by_cases ha : (a : ℕ) < p
    · have := (hx (Sum.inl ⟨a, ha⟩)).2
      rw [show Fin.cast hn' (finSumFinEquiv (Sum.inl ⟨a, ha⟩ : Fin p ⊕ Fin q)) = a from Fin.ext (by simp)] at this
      simp [this, ha]
    · have := (hx (Sum.inr ⟨a - p, by have := a.2; omega⟩)).2
      rw [show Fin.cast hn' (finSumFinEquiv (Sum.inr ⟨a - p, by have := a.2; omega⟩ : Fin p ⊕ Fin q)) = a from
        Fin.ext (by simp; omega)] at this
      simp [this, ha]
  have hq : ∀ ρ, nNeg (M.ε ρ) = q := fun ρ => by rw [nNeg_shape hp (hε ρ)]; omega
  have hw : ∀ ρ c, extWt M ρ (arr (nNeg (M.ε ρ)) c) = (wtCol (h ρ) p q c : ℝ) := fun ρ c => by
    obtain ⟨hn', hx⟩ := GlobalTheory.HolDS.lowK_holPar (hok ρ) (he ρ)
    have hc := c.2
    by_cases hcq : (c : ℕ) < q
    · rw [extWt_arr M ρ hp (hε ρ) c (Fin.cast hn' (finSumFinEquiv (Sum.inr ⟨c, hcq⟩ : Fin p ⊕ Fin q)))
        (by rw [if_pos (by omega)]; simp), hx]
      simp only [wtCol, if_pos hcq, Formalism.L2.NTheta.kapW, Formalism.L2.NTheta.kapQ, Sum.elim_inr]
    · rw [extWt_arr M ρ hp (hε ρ) c (Fin.cast hn' (finSumFinEquiv (Sum.inl ⟨c - q, by omega⟩ : Fin p ⊕ Fin q)))
        (by rw [if_neg (by omega)]; simp; omega), hx]
      simp only [wtCol, if_neg hcq, Formalism.L2.NTheta.kapW, Formalism.L2.NTheta.kapQ, Sum.elim_inl]
  have hneg : NegFirst V q (x0Mat M) := fun ρ => by
    have := orth_sub (M.fr_unit ρ) (M.fr_gram ρ) (arr (nNeg (M.ε ρ)))
    refine this.trans ?_
    unfold Formalism.REAL.Jm
    rw [Matrix.submatrix_diagonal _ _ (arr_injective (nNeg_le (M.ε ρ)))]
    congr 1
    funext a
    have := a.2
    simp only [Function.comp, hε, hq, arr, decide_eq_true_eq]
    split_ifs <;> first | rfl | (exfalso; simp only at *; omega)
  refine ⟨x0Mat M, hneg, fun J χ T hT => ⟨(hT.aut v).smooth, fun ρ c d hcd => ?_, fun ρ t g => ?_⟩⟩
  · have hk := (GlobalTheory.T.extremal_vector_annihilated D θ V S M J χ T hθ hT v hv ρ p true (fun a => by rw [hε]; by_cases ha : (a : ℕ) < p <;> simp [ha])).1
    have e := conj_single (M.fr_unit ρ) (arrEquiv (nNeg_le (M.ε ρ))) c d
    change x0Mat M ρ * _ * (x0Mat M ρ)⁻¹ =
      _ * Matrix.single (arr (nNeg (M.ε ρ)) c) (arr (nNeg (M.ε ρ)) d) 1 * _ at e
    rw [e]
    apply hk
    have h1 : (c : ℕ) < d := hcd
    have h2 := d.2
    simp only [KillPair, hε, hq, arr, Fin.lt_def, decide_eq_true_eq, decide_eq_false_iff_not, ne_eq, decide_eq_decide]
    split_ifs <;> simp only <;> omega
  · have hk := (GlobalTheory.T.extremal_vector_annihilated D θ V S M J χ T hθ hT v hv ρ p true (fun a => by rw [hε]; by_cases ha : (a : ℕ) < p <;> simp [ha])).2
    set e := arrEquiv (nNeg_le (M.ε ρ)) with hedef
    have hx : IsUnit (x0Mat M ρ).det := by
      have h1 := congrArg Matrix.det (hneg ρ)
      rw [det_mul, det_diagonal] at h1
      refine isUnit_iff_ne_zero.2 fun h0 => ?_
      rw [h0, mul_zero] at h1
      exact Finset.prod_ne_zero_iff.2 (fun a _ => by split_ifs <;> simp) h1.symm
    have h1 := torus_x0Mat M ρ fun a => Complex.exp ((t (e.symm a) : ℂ) * Complex.I)
    have h2 : ∀ c, e.symm (arr (nNeg (M.ε ρ)) c) = c := fun c => e.symm_apply_apply c
    simp only [h2] at h1
    rw [← h1, Matrix.mul_nonsing_inv_cancel_right _ _ hx, hk (fun a => t (e.symm a)) g, ← e.sum_comp]
    simp only [Equiv.symm_apply_apply]
    congr 5
    funext c
    rw [← hw ρ c]
    rfl

end GlobalTheory.HolRead

import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJDHatJDRStepALevel
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJDHatJDCapRGrpPTop
import Formalism.HermitianCurvature.HermitianCurvatureProofs.HermitianInvariantCellAction

open Matrix Filter Topology

noncomputable section

namespace Formalism.FourierDecayAlt.P.CutMP

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.P.Qx6

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

namespace CapelliExpansionLemmas

variable {k r : ℕ}

/- English proof (translation)
Establish `hu : IsUnit (w1 k r l a).det` using `Formalism.QuantumDeterminants.WeylGroupFacts.isUnit_of_uh (Formalism.FourierDecayAlt.P.Qx3.weyl_cell_mem_unitary l ha)`. Establish `hf` using `TemperedBoundGL3.unipotent_fixes_base_vector (k := k) l a hz`. Rewrite using `[Matrix.mul_inv_rev, ← Matrix.mulVec_mulVec]`. Use `congr 1`. Use `conv_lhs => rw [← hf]`.

Rewrite using `[Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hu, Matrix.one_mulVec]`.
-/
theorem inv_w1_mul_mulVec_of_inWb (l : Fin r) {a : ℂ} (ha : a ≠ 0) {z : Fin (2 * r + k + 1) → ℂ} (hz : inWb k r z) (g : Mx k r) :
    (w1 k r l a * g)⁻¹ *ᵥ z = g⁻¹ *ᵥ z := by
  have hu : IsUnit (w1 k r l a).det := Formalism.QuantumDeterminants.WeylGroupFacts.isUnit_of_uh (Formalism.FourierDecayAlt.P.Qx3.weyl_cell_mem_unitary l ha)
  have hf := TemperedBoundGL3.unipotent_fixes_base_vector (k := k) l a hz
  rw [Matrix.mul_inv_rev, ← Matrix.mulVec_mulVec]
  congr 1
  conv_lhs => rw [← hf]
  rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hu, Matrix.one_mulVec]

/- English proof (translation)
Establish `hu : IsUnit (wCell k r i c).det` using `Formalism.QuantumDeterminants.WeylGroupFacts.isUnit_of_uh (Formalism.FourierDecayAlt.P.Qx3.wlist_glev hc _).1`. Establish `hf` using `TemperedBoundGL3.wCell_fix_wb (k := k) i c hz`. Rewrite using `[Matrix.mul_inv_rev, ← Matrix.mulVec_mulVec]`. Use `congr 1`. Use `conv_lhs => rw [← hf]`.

Rewrite using `[Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hu, Matrix.one_mulVec]`.
-/
theorem cell_inverse_fixes_vector (i : Fin (r + 1)) {c : Fin r → ℂ} (hc : c ∈ OmX r) {z : Fin (2 * r + k + 1) → ℂ}
    (hz : inWb k r z) (g : Mx k r) : (wCell k r i c * g)⁻¹ *ᵥ z = g⁻¹ *ᵥ z := by
  have hu : IsUnit (wCell k r i c).det :=
    Formalism.QuantumDeterminants.WeylGroupFacts.isUnit_of_uh (Formalism.FourierDecayAlt.P.Qx3.wlist_glev hc _).1
  have hf := TemperedBoundGL3.wCell_fix_wb (k := k) i c hz
  rw [Matrix.mul_inv_rev, ← Matrix.mulVec_mulVec]
  congr 1
  conv_lhs => rw [← hf]
  rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hu, Matrix.one_mulVec]

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]

/- English proof (translation)
Introduce `α f`. Use function extensionality and compare the values at `g`. Simplify using `only [NL, Pi.smul_apply, Finset.smul_sum]`. Use `Finset.sum_congr rfl fun s _ => Finset.sum_congr rfl fun t _ => ?_` and prove the remaining obligations. Rewrite using `[Formalism.FourierDecayAlt.P5.qminorOp_smulC (fun a b => Formalism.FourierDecayAlt.P5.eH_smulC a b) _ _ u α f, Pi.smul_apply]`.

Conclude with `smul_comm _ _ _`.
-/
theorem NL_smulC (z z' : Fin (2 * r + k + 1) → ℂ) (l : Fin (r + 1)) (u : ℂ) :
    Formalism.FourierDecayAlt.P5.SmulC (E := E) (NL k r z z' l u) := by
  intro α f
  funext g
  simp only [NL, Pi.smul_apply, Finset.smul_sum]
  refine Finset.sum_congr rfl fun s _ => Finset.sum_congr rfl fun t _ => ?_
  rw [Formalism.FourierDecayAlt.P5.qminorOp_smulC (fun a b => Formalism.FourierDecayAlt.P5.eH_smulC a b) _ _ u α f, Pi.smul_apply]
  exact smul_comm _ _ _

/- English proof (translation)
Use function extensionality and compare the values at `x`. Simplify using `only [NL]`. Use `Finset.sum_congr rfl fun s _ => Finset.sum_congr rfl fun t _ => ?_` and prove the remaining obligations. Rewrite using `[show qminorOp (EH k r) (rowsN k r l s) (rowsN k r l t) u (fun x => f (wCell k r i c * x)) x = qminorOp (EH k r) (rowsN k r l s) (rowsN k r l t) u f (wCell k r i c * x) from congrFun (Formalism.FourierDecayAlt.P.quantum_minor_left_hermitian E _ _ (Hpk k r) f _ _ u _) x, cell_inve …`.
-/
theorem NL_left (z z' : Fin (2 * r + k + 1) → ℂ) (hz : inWb k r z) (l : Fin (r + 1)) (u : ℂ) (i : Fin (r + 1))
    {c : Fin r → ℂ} (hc : c ∈ OmX r) (f : Mx k r → E) :
    NL k r z z' l u (fun x => f (wCell k r i c * x)) = fun x => NL k r z z' l u f (wCell k r i c * x) := by
  funext x
  simp only [NL]
  refine Finset.sum_congr rfl fun s _ => Finset.sum_congr rfl fun t _ => ?_
  rw [show qminorOp (EH k r) (rowsN k r l s) (rowsN k r l t) u (fun x => f (wCell k r i c * x)) x =
      qminorOp (EH k r) (rowsN k r l s) (rowsN k r l t) u f (wCell k r i c * x) from
    congrFun (Formalism.FourierDecayAlt.P.quantum_minor_left_hermitian E _ _ (Hpk k r) f _ _ u _) x, cell_inverse_fixes_vector i hc hz x]

end CapelliExpansionLemmas

namespace CapelliExpansionLemmas

section Idx
variable {k r : ℕ}

/- English proof (translation)
Simplify using `[mdim]`.
-/
theorem mdimL_eq : mdim k (r + 1) (Fin.last r).succ = k + 1 := by simp [mdim]

/- English proof (translation)
Use function extensionality and compare the values at `j`. Apply `Fin.ext` to reduce the goal to its premises. Break down `j with ⟨j, hj⟩` into its components or cases. Break down `j with _ | j` into its components or cases. Simplify using `[rowsN, posL, bE, e0]`.

Rewrite using `[show (⟨j + 1, hj⟩ : Fin (mdim k (r + 1) (Fin.last r).succ - 1 + 1)) = Fin.succ ⟨j, by omega⟩ from rfl]`. Simplify using `only [Function.comp_apply, Qx6.bE_succ, rowsN, posL, v0, skip1, Fin.val_cast, Fin.val_succ, Fin.val_castSucc, Fin.val_last]`. Apply the tactic sequence `split_ifs <;> simp_all <;> omega`.
-/
theorem rowsN_eq (s : Fin (mdim k (r + 1) (Fin.last r).succ))
    (h : mdim k (r + 1) (Fin.last r).succ - 1 + 1 = r + 1 - ((Fin.last r).castSucc : Fin (r + 2)).val + k) :
    rowsN k (r + 1) (Fin.last r).castSucc (Fin.cast mdimL_eq s) ∘ Fin.cast h =
      posL k (r + 1) (Fin.last r).castSucc ∘ bE (e0 k (Fin.last r)) (v0 k (Fin.last r) ∘ skip1 s) := by
  funext j
  apply Fin.ext
  rcases j with ⟨j, hj⟩
  rcases j with _ | j
  · simp [rowsN, posL, bE, e0]
  · rw [show (⟨j + 1, hj⟩ : Fin (mdim k (r + 1) (Fin.last r).succ - 1 + 1)) = Fin.succ ⟨j, by omega⟩ from rfl]
    simp only [Function.comp_apply, Qx6.bE_succ, rowsN, posL, v0, skip1, Fin.val_cast, Fin.val_succ,
      Fin.val_castSucc, Fin.val_last]
    split_ifs <;> simp_all <;> omega

end Idx

end CapelliExpansionLemmas

namespace CapelliExpansionLemmas

section Re
variable {k r : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]

/- English proof (translation)
Apply `Fin.ext` to reduce the goal to its premises. Simplify using `[posL, wI]`. Use linear arithmetic over natural numbers and integers.
-/
theorem posL_last_wI (s : Fin (k + 1)) :
    posL k (r + 1) (Fin.last r).succ (Fin.cast mdimL_eq.symm s) = wI k (r + 1) s := by
  apply Fin.ext
  simp [posL, wI]
  omega

/- English proof (translation)
Establish `h : mdim k (r + 1) (Fin.last r).succ - 1 + 1 = r + 1 - ((Fin.last r).castSucc : Fin (r + 2)).val + k`. Simplify using `[mdim]`. Use linear arithmetic over natural numbers and integers. Establish `hf : fvec k (r + 1) z' (Fin.last r).succ = z'` using `Formalism.FourierDecayAlt.P.Qx5.fvec_last k (r + 1) z'`. Unfold `NL`.

Use `Fintype.sum_equiv (finCongr mdimL_eq.symm) _ _ fun s => ?_` and prove the remaining obligations. Use `Fintype.sum_equiv (finCongr mdimL_eq.symm) _ _ fun t => ?_` and prove the remaining obligations. Simplify using `only [finCongr_apply]`. Establish `hs` using `rowsN_eq (Fin.cast mdimL_eq.symm s) h`. Establish `ht` using `rowsN_eq (Fin.cast mdimL_eq.symm t) h`.

Simplify using `only [Fin.cast_cast, Fin.cast_eq_self] at hs ht`. Rewrite using `[← hs, ← ht, Formalism.FourierDecayAlt.P.CutMP.top_qminor_cast]`. Use `congr 1`. Simplify using `only [xbv, hf, posL_last_wI, Fin.val_cast]`. Use `push_cast`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem NL_re (z z' : Fin (2 * (r + 1) + k + 1) → ℂ) (u : ℂ) (f : Mx k (r + 1) → E) (x : Mx k (r + 1)) :
    NL k (r + 1) z z' (Fin.last r).castSucc u f x =
      ∑ s : Fin (mdim k (r + 1) (Fin.last r).succ), ∑ t : Fin (mdim k (r + 1) (Fin.last r).succ),
        ((((-1 : ℤ) ^ ((s : ℕ) + (t : ℕ)) : ℤ) : ℂ) * xbv k (r + 1) z' (Fin.last r).succ s *
          (x⁻¹ *ᵥ z) (posL k (r + 1) (Fin.last r).succ t)) •
          qminorOp (EH k (r + 1)) (posL k (r + 1) (Fin.last r).castSucc ∘ bE (e0 k (Fin.last r)) (v0 k (Fin.last r) ∘ skip1 s))
            (posL k (r + 1) (Fin.last r).castSucc ∘ bE (e0 k (Fin.last r)) (v0 k (Fin.last r) ∘ skip1 t)) u f x := by
  have h : mdim k (r + 1) (Fin.last r).succ - 1 + 1 = r + 1 - ((Fin.last r).castSucc : Fin (r + 2)).val + k := by
    simp [mdim]; omega
  have hf : fvec k (r + 1) z' (Fin.last r).succ = z' := Formalism.FourierDecayAlt.P.Qx5.fvec_last k (r + 1) z'
  unfold NL
  refine Fintype.sum_equiv (finCongr mdimL_eq.symm) _ _ fun s => ?_
  refine Fintype.sum_equiv (finCongr mdimL_eq.symm) _ _ fun t => ?_
  simp only [finCongr_apply]
  have hs := rowsN_eq (Fin.cast mdimL_eq.symm s) h
  have ht := rowsN_eq (Fin.cast mdimL_eq.symm t) h
  simp only [Fin.cast_cast, Fin.cast_eq_self] at hs ht
  rw [← hs, ← ht, Formalism.FourierDecayAlt.P.CutMP.top_qminor_cast]
  congr 1
  simp only [xbv, hf, posL_last_wI, Fin.val_cast]
  push_cast
  ring

end Re

end CapelliExpansionLemmas

namespace CapelliExpansionLemmas

section Core
variable {k r : ℕ}

/- English proof (translation)
Use `set l : Fin (r + 1) := Fin.last r with hl`. Take `⟨hΦ, hD'⟩` from `TemperedBoundGL3.br1 (π := π) (π' := π') hz hz' hD hJ hc l`. Establish `hgD : g ∈ Dc1 l (Dcell D l.castSucc c) c` using `TemperedBoundGL3.cell_preimage_mem_domain l hcg`. Take `⟨hs, hle, hri, -⟩` from `hΦ`. Set `R : Rules` to `⟨Formalism.FourierDecayAlt.P.generator_gl_level, Formalism.FourierDecayAlt.P.generator_action_preserved, Formalism.FourierDecayAlt.P.quantum_minor_left_hermitian, Formalism.FourierDecayAlt.P.right_action_rule, Formalism.FourierDecayAlt.P.left_action_rule, Formalism.FourierDecayAl …`.

Use `set Φ := resG k (r + 1) l.castSucc J c with hΦdef`. Use `set γ : (Fin (r + 1) → ℂ) → ℂ := fun c' => ((‖c' l‖ ^ (Mdim k (r + 1) l - 1) : ℝ) : ℂ) with hγ`. Use `set WorkedExample : (Fin (r + 1) → ℂ) → (Wq →L[ℂ] Wp) := fun c' => ((tB (Wq →L[ℂ] Wp) l.succ (ho1 l hD'.1) z z' Y 1 0 (rho (Wq →L[ℂ] Wp) R.w l hD'.1 (J0 hD'.1 hs)) : (sfData (Wq →L[ℂ] Wp) l.succ (ho1 l hD'.1)).V) : Fn k (r + 1) (Wq →L[ℂ] Wp)) c' g with hF10`. Use `set LargeParameterEstimates : (Fin (r + 1) → ℂ) → (Wq →L[ℂ] Wp) := fun c' => ((tB (Wq →L[ℂ] Wp) l.succ (ho1 l hD'.1) z z' Y 1 1 (rho (Wq →L[ℂ] Wp) R.w l hD'.1 (J0 hD'.1 hs)) : (sfData (Wq →L[ℂ] Wp) l.succ (ho1 l hD'.1)).V) : Fn k (r + 1) (Wq →L[ℂ] Wp)) c' g with hF11`. Establish `hloc : ∀ (a b : Fin 2) (c' : Fin (r + 1) → ℂ), c' ∈ OmX (r + 1) → g ∈ Dc1 l (Dcell D l.castSucc c) c' → ((tB (Wq →L[ℂ] Wp) l.succ (ho1 l hD'.1) z z' Y a b (rho (Wq →L[ℂ] Wp) R.w l hD'.1 (J0 hD'.1 hs)) : (sfData (Wq →L[ℂ] Wp) l.succ (ho1 l hD'.1)).V) : Fn k (r + 1) (Wq →L[ℂ] Wp)) …`.

Introduce `a b c' hc' hgD'`. Rewrite using `[stp_tB_apply (ho1 l hD'.1) z z' Y a b _ hc' hg hgD']`. Use `(Formalism.FourierDecayAlt.P.Qx2.ll_tL (open_slice (ho1 l hD'.1) hc') z z' Y a b).loc _ _ (fun x hx => ?_) g ⟨hg, hgD'⟩` and prove the remaining obligations. Rewrite using `[rho_apply R.w l hD'.1 _ hc' hx.1 hx.2, restricted_function_on_level hD'.1 hs (pt_mem R.w l hc' hx.1 hx.2)]`. Establish `hline : ∀ c'' ∈ OmX (r + 1), (∀ a : Fin (r + 1), a.val < l.val → c'' a = c a) → g ∈ Dc1 l (Dcell D l.castSucc c) c'' → FN k (r + 1) z z' Y J l.succ c'' g = -(γ c'' • WorkedExample c'') ∧ Q.QL k (r + 1) z z' l.succ Y 1 1 (Q.resG k (r + 1) l.succ J) c'' g = γ c'' • LargeParameterEs …`.

Introduce `c'' hc'' hag hgD''`. Establish `hW : wCell k (r + 1) l.castSucc c'' = wCell k (r + 1) l.castSucc c` using `wCell_congr (fun a ha => hag a ha)`. Establish `hcg'' : wCell k (r + 1) l.succ c'' * g ∈ D`. Establish `: wCell k (r + 1) l.castSucc c * (w1 k (r + 1) l (c'' l) * g) ∈ D` using `hgD''`. Rewrite using `[wCell_succ, hW, Matrix.mul_assoc]`.

Conclude with `this`. Establish `hres : Q.resG k (r + 1) l.succ J c'' = γ c'' • (fun x => Φ (w1 k (r + 1) l (c'' l) * x))`. Use function extensionality and compare the values at `x`. Rewrite using `[resG_succ]`. Simplify using `only [Res, Pi.smul_apply]`.

Rewrite using `[ind_resG l.castSucc J c'' hc'' c hc (fun a ha => hag a ha)]`. Establish `hT` using `residue_top_holds Wp Wq k (r + 1) z z' π π' D Y hz hz' hD J hJ c'' hc'' g hg hcg''`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Use `show FN k (r + 1) z z' Y J (Fin.last (r + 1)) c'' g = _`. Rewrite using `[hT]`.

Use `show -(tL k (r + 1) z z' l.succ Y 1 0 (Q.resG k (r + 1) l.succ J c'') g) = _`. Rewrite using `[hres, Formalism.FourierDecayAlt.P5.tL_smulC z z' l.succ Y 1 0, Pi.smul_apply]`. Simplify using `only [hF10]`. Rewrite using `[hloc 1 0 c'' hc'' hgD'']`. Use `show tL k (r + 1) z z' l.succ Y 1 1 (Q.resG k (r + 1) l.succ J c'') g = _`.

Rewrite using `[hres, Formalism.FourierDecayAlt.P5.tL_smulC z z' l.succ Y 1 1, Pi.smul_apply]`. Simplify using `only [hF11]`. Rewrite using `[hloc 1 1 c'' hc'' hgD'']`. Take `⟨hv10, hv11⟩` from `hline c hc (fun _ _ => rfl) hgD`. Establish `eL : FN k (r + 1) z z' Y J l.castSucc c g = γ c • NL k (r + 1) z z' l.castSucc (uC k (r + 1) l.castSucc Y) Φ (w1 k (r + 1) l (c l) * g)` using `TemperedBoundGL3.br2 l (NL k (r + 1) z z' l.castSucc (uC k (r + 1) l.castSucc Y)) (NL_smulC z z' _ _) c (NL_left z z' hz _ _ _ hc) J g`.

Establish `eN : NL k (r + 1) z z' l.castSucc (uC k (r + 1) l.castSucc Y) Φ (w1 k (r + 1) l (c l) * g) = evP (ho1 l hD'.1) (rho (Wq →L[ℂ] Wp) R.w l hD'.1 (J0 hD'.1 hs)) c g (-(bTee (Wq →L[ℂ] Wp) l hD'.1 (uC k (r + 1) l.castSucc Y) * tB (Wq →L[ℂ] Wp) l.succ (ho1 l hD'.1) z z' Y 1 0) - mulB (W …`. Rewrite using `[← capelli_key_first_term hD'.1 z z' Y, ← capelli_key_second_identity hD'.1 z z' Y, ← Finset.sum_sub_distrib]`. Simplify using `only [← Finset.sum_sub_distrib, ← smul_sub, ← mul_sub]`. Rewrite using `[NL_re, map_sum]`. Use `Finset.sum_congr rfl fun s _ => ?_` and prove the remaining obligations.

Rewrite using `[map_sum]`. Use `Finset.sum_congr rfl fun t _ => ?_` and prove the remaining obligations. Rewrite using `[map_smul, stp_ev_mul (ho1 l hD'.1) (sf_aY z t) _ hc hg hgD, smul_smul, inv_w1_mul_mulVec_of_inWb l (hc l) hz g, quantum_minor_point_evaluation R hz hz' hD' hs hle hri (skip1 s) (skip1 t) _ hc hg hgD]`. Use `congr 1`. Simplify using `only [aY, yv]`.

Rewrite using `[show fvec k (r + 1) z (Fin.last r).succ = z from Formalism.FourierDecayAlt.P.Qx5.fvec_last k (r + 1) z]`. Establish `e1 : evP (ho1 l hD'.1) (rho (Wq →L[ℂ] Wp) R.w l hD'.1 (J0 hD'.1 hs)) c g (opB (Wq →L[ℂ] Wp) l.succ (ho1 l hD'.1) l 0 * tB (Wq →L[ℂ] Wp) l.succ (ho1 l hD'.1) z z' Y 1 0) = pOp l WorkedExample c` using `by show ((opB (Wq →L[ℂ] Wp) l.succ (ho1 l hD'.1) l 0 (tB (Wq →L[ℂ] Wp) l.succ (ho1 l hD'.1) z z' Y 1 0 (rho (Wq →L[ℂ] Wp) R.w l hD'.1 (J0 hD'.1 hs))) : (sfData (Wq →L[ℂ] Wp) l.succ (ho1 l hD'.1)).V) : Fn k (r + 1) (Wq →L[ℂ] Wp)) c g = _`. Unfold `opB`. Rewrite using `[sf_hat_apply _ (sf_good_crd _ l 0) _ hc hg hgD]`. Both sides reduce to the same expression.

Establish `eE : evP (ho1 l hD'.1) (rho (Wq →L[ℂ] Wp) R.w l hD'.1 (J0 hD'.1 hs)) c g (-(bTee (Wq →L[ℂ] Wp) l hD'.1 (uC k (r + 1) l.castSucc Y) * tB (Wq →L[ℂ] Wp) l.succ (ho1 l hD'.1) z z' Y 1 0) - mulB (Wq →L[ℂ] Wp) l.succ (ho1 l hD'.1) (aCi k l) * tB (Wq →L[ℂ] Wp) l.succ (ho1 l hD'.1) z z' …`. Rewrite using `[map_sub, map_neg, stp_ev_mul (ho1 l hD'.1) (sf_aCi l) _ hc hg hgD]`. Unfold `bTee`. Rewrite using `[add_mul, map_add, smul_mul_assoc, one_mul, map_smul, e1]`. Both sides reduce to the same expression.

Establish `hnear` using `near_pt (ho1 l hD'.1) hc hgD`. Establish `htend : Tendsto (fun s : ℂ => Function.update c l s) (𝓝 (c l)) (𝓝 c)`. Establish `h` using `((continuous_const (y := c)).update l continuous_id).tendsto (c l)`. Simplify using `using h`. Establish `hev : ∀ᶠ s in 𝓝 (c l), FN k (r + 1) z z' Y J l.succ (Function.update c l s) g = (-1 : ℂ) • (γ (Function.update c l s) • WorkedExample (Function.update c l s))` using `by filter_upwards [htend.eventually hnear] with s hs`.

Rewrite using `[(hline _ hs.1 (fun a ha => Function.update_of_ne (fun h => by rw [h] at ha; exact lt_irrefl _ ha) s c) hs.2).1, neg_one_smul]`. Establish `hd1 : DifferentiableAt ℝ (fun c' => FN k (r + 1) z z' Y J l.succ c' g) c`. Establish `hfam` using `fam_QL (π := π) (π' := π') Formalism.FourierDecayAlt.P.operator_preserves_fusion_forms hz hz' (dom_Dcell Formalism.FourierDecayAlt.P.restriction_mem hz hz' hD l.succ) Y 1 0 (Formalism.FourierDecayAlt.P.restriction_good_family Wp Wq k (r + 1) z z' π π' D hz hz' hD J hJ l.succ)`. Use `((fam_diff hfam hc hg hcg).neg).congr_of_eventuallyEq ?_` and prove the remaining obligations. Use `filter_upwards [near_pt (open_Dcell hD.1 l.succ) hc hcg] with c' hc'`.

Conclude with `residue_top_holds Wp Wq k (r + 1) z z' π π' D Y hz hz' hD J hJ c' hc'.1 g hg hc'.2`. Establish `hd2F : DifferentiableAt ℝ WorkedExample c` using `sf_diff (tB (Wq →L[ℂ] Wp) l.succ (ho1 l hD'.1) z z' Y 1 0 (rho (Wq →L[ℂ] Wp) R.w l hD'.1 (J0 hD'.1 hs))).2.1 hc hg hgD`. Establish `hd2 : DifferentiableAt ℝ (fun c' => γ c' • WorkedExample c') c` using `(diff_gamma l _ hc).smul hd2F`. Establish `hp : pOp l (fun c' => FN k (r + 1) z z' Y J l.succ c' g) c = (-1 : ℂ) • pOp l (fun c' => γ c' • WorkedExample c') c` using `opL_dir l 0 (-1) hd1 hd2 hev`. Establish `hp2 : pOp l (fun c' => γ c' • WorkedExample c') c = γ c • pOp l WorkedExample c + pOp l γ c • WorkedExample c` using `pOp_smul l hc (diff_gamma l _ hc) hd2F`.

Establish `hp3 : pOp l γ c = (((Mdim k (r + 1) l - 1 : ℕ) : ℂ) / 2) * γ c` using `pOp_gamma l hc _`. Simplify using `only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, Q.crd, ciOp]`. Rewrite using `[eL, eN, eE, hv10, hv11, hp, hp2, hp3, stp_uC l Y, stp_Mdim l]`. Use `module`.
-/
theorem stepA_core (Wp Wq : Type) [NormedAddCommGroup Wp] [NormedSpace ℂ Wp] [NormedAddCommGroup Wq]
    [NormedSpace ℂ Wq] (z z' : Fin (2 * (r + 1) + k + 1) → ℂ) (π : Mx k (r + 1) → (Wp →L[ℂ] Wp))
    (π' : Mx k (r + 1) → (Wq →L[ℂ] Wq)) (D : Set (Mx k (r + 1))) (Y : ℂ) (hz : inWb k (r + 1) z)
    (hz' : inWb k (r + 1) z') (hD : IsDom k (r + 1) z z' 0 D) (J : Mx k (r + 1) → (Wq →L[ℂ] Wp))
    (hJ : J ∈ FFl k (r + 1) z z' π π' 0 D) (c : Fin (r + 1) → ℂ) (hc : c ∈ OmX (r + 1)) (g : Mx k (r + 1))
    (hg : g ∈ Glev k (r + 1) (Fin.last r).succ) (hcg : wCell k (r + 1) (Fin.last r).succ c * g ∈ D) :
    FN k (r + 1) z z' Y J (Fin.last r).castSucc c g =
      (Y • FN k (r + 1) z z' Y J (Fin.last r).succ + Q.crd (pOp (Fin.last r)) (FN k (r + 1) z z' Y J (Fin.last r).succ) -
        Q.crd (ciOp (Fin.last r)) (Q.QL k (r + 1) z z' (Fin.last r).succ Y 1 1
          (Q.resG k (r + 1) (Fin.last r).succ J))) c g := by
  set l : Fin (r + 1) := Fin.last r with hl
  obtain ⟨hΦ, hD'⟩ := TemperedBoundGL3.br1 (π := π) (π' := π') hz hz' hD hJ hc l
  have hgD : g ∈ Dc1 l (Dcell D l.castSucc c) c := TemperedBoundGL3.cell_preimage_mem_domain l hcg
  obtain ⟨hs, hle, hri, -⟩ := hΦ
  let R : Rules := ⟨Formalism.FourierDecayAlt.P.generator_gl_level, Formalism.FourierDecayAlt.P.generator_action_preserved, Formalism.FourierDecayAlt.P.quantum_minor_left_hermitian,
    Formalism.FourierDecayAlt.P.right_action_rule, Formalism.FourierDecayAlt.P.left_action_rule, Formalism.FourierDecayAlt.P.torus_action_rule,
    Formalism.FourierDecayAlt.P.weyl_level_element_properties⟩
  set Φ := resG k (r + 1) l.castSucc J c with hΦdef
  set γ : (Fin (r + 1) → ℂ) → ℂ := fun c' => ((‖c' l‖ ^ (Mdim k (r + 1) l - 1) : ℝ) : ℂ) with hγ
  set WorkedExample : (Fin (r + 1) → ℂ) → (Wq →L[ℂ] Wp) := fun c' =>
    ((tB (Wq →L[ℂ] Wp) l.succ (ho1 l hD'.1) z z' Y 1 0 (rho (Wq →L[ℂ] Wp) R.w l hD'.1 (J0 hD'.1 hs)) : (sfData (Wq →L[ℂ] Wp) l.succ (ho1 l hD'.1)).V) : Fn k (r + 1) (Wq →L[ℂ] Wp)) c' g
    with hF10
  set LargeParameterEstimates : (Fin (r + 1) → ℂ) → (Wq →L[ℂ] Wp) := fun c' =>
    ((tB (Wq →L[ℂ] Wp) l.succ (ho1 l hD'.1) z z' Y 1 1 (rho (Wq →L[ℂ] Wp) R.w l hD'.1 (J0 hD'.1 hs)) : (sfData (Wq →L[ℂ] Wp) l.succ (ho1 l hD'.1)).V) : Fn k (r + 1) (Wq →L[ℂ] Wp)) c' g
    with hF11

  have hloc : ∀ (a b : Fin 2) (c' : Fin (r + 1) → ℂ), c' ∈ OmX (r + 1) → g ∈ Dc1 l (Dcell D l.castSucc c) c' →
      ((tB (Wq →L[ℂ] Wp) l.succ (ho1 l hD'.1) z z' Y a b (rho (Wq →L[ℂ] Wp) R.w l hD'.1 (J0 hD'.1 hs)) : (sfData (Wq →L[ℂ] Wp) l.succ (ho1 l hD'.1)).V) :
        Fn k (r + 1) (Wq →L[ℂ] Wp)) c' g = tL k (r + 1) z z' l.succ Y a b (fun x => Φ (w1 k (r + 1) l (c' l) * x)) g := by
    intro a b c' hc' hgD'
    rw [stp_tB_apply (ho1 l hD'.1) z z' Y a b _ hc' hg hgD']
    refine (Formalism.FourierDecayAlt.P.Qx2.ll_tL (open_slice (ho1 l hD'.1) hc') z z' Y a b).loc _ _ (fun x hx => ?_) g ⟨hg, hgD'⟩
    rw [rho_apply R.w l hD'.1 _ hc' hx.1 hx.2, restricted_function_on_level hD'.1 hs (pt_mem R.w l hc' hx.1 hx.2)]
  have hline : ∀ c'' ∈ OmX (r + 1), (∀ a : Fin (r + 1), a.val < l.val → c'' a = c a) →
      g ∈ Dc1 l (Dcell D l.castSucc c) c'' →
      FN k (r + 1) z z' Y J l.succ c'' g = -(γ c'' • WorkedExample c'') ∧
        Q.QL k (r + 1) z z' l.succ Y 1 1 (Q.resG k (r + 1) l.succ J) c'' g = γ c'' • LargeParameterEstimates c'' := by
    intro c'' hc'' hag hgD''
    have hW : wCell k (r + 1) l.castSucc c'' = wCell k (r + 1) l.castSucc c := wCell_congr (fun a ha => hag a ha)
    have hcg'' : wCell k (r + 1) l.succ c'' * g ∈ D := by
      have : wCell k (r + 1) l.castSucc c * (w1 k (r + 1) l (c'' l) * g) ∈ D := hgD''
      rw [wCell_succ, hW, Matrix.mul_assoc]
      exact this
    have hres : Q.resG k (r + 1) l.succ J c'' = γ c'' • (fun x => Φ (w1 k (r + 1) l (c'' l) * x)) := by
      funext x
      rw [resG_succ]
      simp only [Res, Pi.smul_apply]
      rw [ind_resG l.castSucc J c'' hc'' c hc (fun a ha => hag a ha)]
    have hT := residue_top_holds Wp Wq k (r + 1) z z' π π' D Y hz hz' hD J hJ c'' hc'' g hg hcg''
    refine ⟨?_, ?_⟩
    · show FN k (r + 1) z z' Y J (Fin.last (r + 1)) c'' g = _
      rw [hT]
      show -(tL k (r + 1) z z' l.succ Y 1 0 (Q.resG k (r + 1) l.succ J c'') g) = _
      rw [hres, Formalism.FourierDecayAlt.P5.tL_smulC z z' l.succ Y 1 0, Pi.smul_apply]
      simp only [hF10]
      rw [hloc 1 0 c'' hc'' hgD'']
    · show tL k (r + 1) z z' l.succ Y 1 1 (Q.resG k (r + 1) l.succ J c'') g = _
      rw [hres, Formalism.FourierDecayAlt.P5.tL_smulC z z' l.succ Y 1 1, Pi.smul_apply]
      simp only [hF11]
      rw [hloc 1 1 c'' hc'' hgD'']
  obtain ⟨hv10, hv11⟩ := hline c hc (fun _ _ => rfl) hgD

  have eL : FN k (r + 1) z z' Y J l.castSucc c g =
      γ c • NL k (r + 1) z z' l.castSucc (uC k (r + 1) l.castSucc Y) Φ (w1 k (r + 1) l (c l) * g) :=
    TemperedBoundGL3.br2 l (NL k (r + 1) z z' l.castSucc (uC k (r + 1) l.castSucc Y)) (NL_smulC z z' _ _) c
      (NL_left z z' hz _ _ _ hc) J g
  have eN : NL k (r + 1) z z' l.castSucc (uC k (r + 1) l.castSucc Y) Φ (w1 k (r + 1) l (c l) * g) =
      evP (ho1 l hD'.1) (rho (Wq →L[ℂ] Wp) R.w l hD'.1 (J0 hD'.1 hs)) c g
        (-(bTee (Wq →L[ℂ] Wp) l hD'.1 (uC k (r + 1) l.castSucc Y) * tB (Wq →L[ℂ] Wp) l.succ (ho1 l hD'.1) z z' Y 1 0) -
          mulB (Wq →L[ℂ] Wp) l.succ (ho1 l hD'.1) (aCi k l) * tB (Wq →L[ℂ] Wp) l.succ (ho1 l hD'.1) z z' Y 1 1) := by
    rw [← capelli_key_first_term hD'.1 z z' Y, ← capelli_key_second_identity hD'.1 z z' Y, ← Finset.sum_sub_distrib]
    simp only [← Finset.sum_sub_distrib, ← smul_sub, ← mul_sub]
    rw [NL_re, map_sum]
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [map_sum]
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [map_smul, stp_ev_mul (ho1 l hD'.1) (sf_aY z t) _ hc hg hgD, smul_smul, inv_w1_mul_mulVec_of_inWb l (hc l) hz g,
      quantum_minor_point_evaluation R hz hz' hD' hs hle hri (skip1 s) (skip1 t) _ hc hg hgD]
    congr 1
    simp only [aY, yv]
    rw [show fvec k (r + 1) z (Fin.last r).succ = z from Formalism.FourierDecayAlt.P.Qx5.fvec_last k (r + 1) z]
  have e1 : evP (ho1 l hD'.1) (rho (Wq →L[ℂ] Wp) R.w l hD'.1 (J0 hD'.1 hs)) c g
      (opB (Wq →L[ℂ] Wp) l.succ (ho1 l hD'.1) l 0 * tB (Wq →L[ℂ] Wp) l.succ (ho1 l hD'.1) z z' Y 1 0) = pOp l WorkedExample c := by
    show ((opB (Wq →L[ℂ] Wp) l.succ (ho1 l hD'.1) l 0 (tB (Wq →L[ℂ] Wp) l.succ (ho1 l hD'.1) z z' Y 1 0
      (rho (Wq →L[ℂ] Wp) R.w l hD'.1 (J0 hD'.1 hs))) : (sfData (Wq →L[ℂ] Wp) l.succ (ho1 l hD'.1)).V) :
        Fn k (r + 1) (Wq →L[ℂ] Wp)) c g = _
    unfold opB
    rw [sf_hat_apply _ (sf_good_crd _ l 0) _ hc hg hgD]
    rfl
  have eE : evP (ho1 l hD'.1) (rho (Wq →L[ℂ] Wp) R.w l hD'.1 (J0 hD'.1 hs)) c g
        (-(bTee (Wq →L[ℂ] Wp) l hD'.1 (uC k (r + 1) l.castSucc Y) * tB (Wq →L[ℂ] Wp) l.succ (ho1 l hD'.1) z z' Y 1 0) -
          mulB (Wq →L[ℂ] Wp) l.succ (ho1 l hD'.1) (aCi k l) * tB (Wq →L[ℂ] Wp) l.succ (ho1 l hD'.1) z z' Y 1 1) =
      -(uC k (r + 1) l.castSucc Y • WorkedExample c + pOp l WorkedExample c) - (c l)⁻¹ • LargeParameterEstimates c := by
    rw [map_sub, map_neg, stp_ev_mul (ho1 l hD'.1) (sf_aCi l) _ hc hg hgD]
    unfold bTee
    rw [add_mul, map_add, smul_mul_assoc, one_mul, map_smul, e1]
    rfl

  have hnear := near_pt (ho1 l hD'.1) hc hgD
  have htend : Tendsto (fun s : ℂ => Function.update c l s) (𝓝 (c l)) (𝓝 c) := by
    have h := ((continuous_const (y := c)).update l continuous_id).tendsto (c l)
    simpa using h
  have hev : ∀ᶠ s in 𝓝 (c l), FN k (r + 1) z z' Y J l.succ (Function.update c l s) g =
      (-1 : ℂ) • (γ (Function.update c l s) • WorkedExample (Function.update c l s)) := by
    filter_upwards [htend.eventually hnear] with s hs
    rw [(hline _ hs.1 (fun a ha => Function.update_of_ne (fun h => by rw [h] at ha; exact lt_irrefl _ ha) s c)
      hs.2).1, neg_one_smul]
  have hd1 : DifferentiableAt ℝ (fun c' => FN k (r + 1) z z' Y J l.succ c' g) c := by
    have hfam := fam_QL (π := π) (π' := π') Formalism.FourierDecayAlt.P.operator_preserves_fusion_forms hz hz'
      (dom_Dcell Formalism.FourierDecayAlt.P.restriction_mem hz hz' hD l.succ) Y 1 0
      (Formalism.FourierDecayAlt.P.restriction_good_family Wp Wq k (r + 1) z z' π π' D hz hz' hD J hJ l.succ)
    refine ((fam_diff hfam hc hg hcg).neg).congr_of_eventuallyEq ?_
    filter_upwards [near_pt (open_Dcell hD.1 l.succ) hc hcg] with c' hc'
    exact residue_top_holds Wp Wq k (r + 1) z z' π π' D Y hz hz' hD J hJ c' hc'.1 g hg hc'.2
  have hd2F : DifferentiableAt ℝ WorkedExample c := sf_diff (tB (Wq →L[ℂ] Wp) l.succ (ho1 l hD'.1) z z' Y 1 0
    (rho (Wq →L[ℂ] Wp) R.w l hD'.1 (J0 hD'.1 hs))).2.1 hc hg hgD
  have hd2 : DifferentiableAt ℝ (fun c' => γ c' • WorkedExample c') c := (diff_gamma l _ hc).smul hd2F
  have hp : pOp l (fun c' => FN k (r + 1) z z' Y J l.succ c' g) c =
      (-1 : ℂ) • pOp l (fun c' => γ c' • WorkedExample c') c := opL_dir l 0 (-1) hd1 hd2 hev
  have hp2 : pOp l (fun c' => γ c' • WorkedExample c') c = γ c • pOp l WorkedExample c + pOp l γ c • WorkedExample c :=
    pOp_smul l hc (diff_gamma l _ hc) hd2F
  have hp3 : pOp l γ c = (((Mdim k (r + 1) l - 1 : ℕ) : ℂ) / 2) * γ c := pOp_gamma l hc _

  simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, Q.crd, ciOp]
  rw [eL, eN, eE, hv10, hv11, hp, hp2, hp3, stp_uC l Y, stp_Mdim l]
  module

end Core

end CapelliExpansionLemmas

/- English proof (translation)
Introduce `Wp Wq _ _ _ _ k r hr z z' π π' D Y hz hz' hD J hJ c hc g hg hcg`. Take `⟨r, rfl⟩ : ∃ r', r = r' + 1` from `⟨r - 1, by omega⟩`. Conclude with `CapelliExpansionLemmas.stepA_core Wp Wq z z' π π' D Y hz hz' hD J hJ c hc g hg hcg`.
-/
theorem residue_first_move_holds : JDRStepA := by
  intro Wp Wq _ _ _ _ k r hr z z' π π' D Y hz hz' hD J hJ c hc g hg hcg
  obtain ⟨r, rfl⟩ : ∃ r', r = r' + 1 := ⟨r - 1, by omega⟩
  exact CapelliExpansionLemmas.stepA_core Wp Wq z z' π π' D Y hz hz' hD J hJ c hc g hg hcg

end Formalism.FourierDecayAlt.P.CutMP

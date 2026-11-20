import Formalism.HermitianCurvature.HermitianCurvatureProofs.QxChain
import Formalism.HermitianCurvature.HermitianCurvatureProofs.HasFDerivAtFsvOther
import Formalism.HermitianCurvature.HermitianCurvatureProofs.MemLevelZeroOfMemGroup
import Formalism.HermitianCurvature.HermitianCurvatureProofs.ResGDifferentiableAt

open Matrix
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q

namespace Formalism.FourierDecayAlt.P.CutMP.TemperedBoundGL3

noncomputable section

variable {k r : ℕ}

def lr (hr : 1 ≤ r) : Fin r := ⟨r - 1, by omega⟩

/- English proof (translation)
The claim follows from `Fin.ext (by simp [lr]; omega)`.
-/
theorem lr_succ (hr : 1 ≤ r) : (lr hr).succ = Fin.last r := Fin.ext (by simp [lr]; omega)

section Br1

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [NormedSpace ℂ Wp] [NormedAddCommGroup Wq] [NormedSpace ℂ Wq]
  {z z' : Fin (2 * r + k + 1) → ℂ} {π : Mx k r → (Wp →L[ℂ] Wp)} {π' : Mx k r → (Wq →L[ℂ] Wq)}

/- English proof (translation)
Assemble the required witnesses or components as `⟨(Formalism.FourierDecayAlt.P.restriction_good_family Wp Wq k r z z' π π' D hz hz' hD J hJ l.castSucc).2 c hc, Qx6.dom_Dcell Formalism.FourierDecayAlt.P.restriction_mem hz hz' hD l.castSucc c hc⟩`.
-/
theorem br1 (hz : inWb k r z) (hz' : inWb k r z') {D : Set (Mx k r)} (hD : IsDom k r z z' 0 D)
    {J : Mx k r → (Wq →L[ℂ] Wp)} (hJ : J ∈ FFl k r z z' π π' 0 D) {c : Fin r → ℂ} (hc : c ∈ OmX r) (l : Fin r) :
    resG k r l.castSucc J c ∈ FFl k r z z' π π' l.castSucc (Qx6.Dcell D l.castSucc c) ∧
      IsDom k r z z' l.castSucc (Qx6.Dcell D l.castSucc c) :=
  ⟨(Formalism.FourierDecayAlt.P.restriction_good_family Wp Wq k r z z' π π' D hz hz' hD J hJ l.castSucc).2 c hc,
    Qx6.dom_Dcell Formalism.FourierDecayAlt.P.restriction_mem hz hz' hD l.castSucc c hc⟩

end Br1

/- English proof (translation)
Use `show wCell k r l.castSucc c * (w1 k r l (c l) * g) ∈ D`. Rewrite using `[← Matrix.mul_assoc, ← Qx6.wCell_succ]`. Conclude with `hg`.
-/
theorem cell_preimage_mem_domain {D : Set (Mx k r)} {c : Fin r → ℂ} (l : Fin r) {g : Mx k r}
    (hg : wCell k r l.succ c * g ∈ D) : g ∈ Qx6.Dc1 l (Qx6.Dcell D l.castSucc c) c := by
  show wCell k r l.castSucc c * (w1 k r l (c l) * g) ∈ D
  rw [← Matrix.mul_assoc, ← Qx6.wCell_succ]
  exact hg

section Br2

variable {X : Type} [NormedAddCommGroup X] [NormedSpace ℂ X]

/- English proof (translation)
Rewrite using `[Qx6.resG_succ]`. Use `show ((‖c l‖ ^ (Mdim k r l - 1) : ℝ) : ℂ) • resG k r l.castSucc (Θ J) c (w1 k r l (c l) * g) = _`. Use `congr 1`. Establish `e : resG k r l.castSucc J c = ((Qx6.gam k r l.castSucc c : ℝ) : ℂ) • fun x => J (wCell k r l.castSucc c * x)`. Use function extensionality and compare the values at `x`.

Both sides reduce to the same expression. Rewrite using `[e, hS, hL]`. Both sides reduce to the same expression.
-/
theorem br2 (l : Fin r) (Θ : (Mx k r → X) → (Mx k r → X)) (hS : Formalism.FourierDecayAlt.P5.SmulC Θ) (c : Fin r → ℂ)
    (hL : ∀ f : Mx k r → X,
      Θ (fun x => f (wCell k r l.castSucc c * x)) = fun x => Θ f (wCell k r l.castSucc c * x))
    (J : Mx k r → X) (g : Mx k r) :
    resG k r l.succ (Θ J) c g =
      ((‖c l‖ ^ (Mdim k r l - 1) : ℝ) : ℂ) • Θ (resG k r l.castSucc J c) (w1 k r l (c l) * g) := by
  rw [Qx6.resG_succ]
  show ((‖c l‖ ^ (Mdim k r l - 1) : ℝ) : ℂ) • resG k r l.castSucc (Θ J) c (w1 k r l (c l) * g) = _
  congr 1
  have e : resG k r l.castSucc J c =
      ((Qx6.gam k r l.castSucc c : ℝ) : ℂ) • fun x => J (wCell k r l.castSucc c * x) := by
    funext x
    rfl
  rw [e, hS, hL]
  rfl

def sumQ {ι : Type} (s : Finset ι) {t : ℕ} (κ : ι → Mx k r → ℂ) (a b : ι → Fin t → Fin (2 * r + k + 1))
    (u : ι → ℂ) (f : Mx k r → X) : Mx k r → X :=
  fun x => ∑ i ∈ s, κ i x • qminorOp (EH k r) (a i) (b i) (u i) f x

/- English proof (translation)
Introduce `α f`. Use function extensionality and compare the values at `x`. Simplify using `only [sumQ, Pi.smul_apply, Finset.smul_sum]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[Formalism.FourierDecayAlt.P5.qminorOp_smulC (fun a b => Formalism.FourierDecayAlt.P5.eabH_smulC _ a b) (a i) (b i) (u i) α f]`.

Rewrite using `[Pi.smul_apply, smul_comm]`.
-/
theorem sumQ_smulC {ι : Type} (s : Finset ι) {t : ℕ} (κ : ι → Mx k r → ℂ)
    (a b : ι → Fin t → Fin (2 * r + k + 1)) (u : ι → ℂ) : Formalism.FourierDecayAlt.P5.SmulC (sumQ (X := X) s κ a b u) := by
  intro α f
  funext x
  simp only [sumQ, Pi.smul_apply, Finset.smul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Formalism.FourierDecayAlt.P5.qminorOp_smulC (fun a b => Formalism.FourierDecayAlt.P5.eabH_smulC _ a b) (a i) (b i) (u i) α f]
  rw [Pi.smul_apply, smul_comm]

/- English proof (translation)
Use function extensionality and compare the values at `x`. Simplify using `only [sumQ]`. Use `Finset.sum_congr rfl fun i hi => ?_` and prove the remaining obligations. Rewrite using `[hκ i hi x]`. Use `congr 1`.

Conclude with `congrFun (Formalism.FourierDecayAlt.P.quantum_minor_left_hermitian X _ _ (Hpk k r) f (a i) (b i) (u i) P) x`.
-/
theorem sumQ_left {ι : Type} (s : Finset ι) {t : ℕ} (κ : ι → Mx k r → ℂ)
    (a b : ι → Fin t → Fin (2 * r + k + 1)) (u : ι → ℂ) (P : Mx k r) (hκ : ∀ i ∈ s, ∀ x, κ i (P * x) = κ i x)
    (f : Mx k r → X) : sumQ s κ a b u (fun x => f (P * x)) = fun x => sumQ s κ a b u f (P * x) := by
  funext x
  simp only [sumQ]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [hκ i hi x]
  congr 1
  exact congrFun (Formalism.FourierDecayAlt.P.quantum_minor_left_hermitian X _ _ (Hpk k r) f (a i) (b i) (u i) P) x

end Br2

/- English proof (translation)
Establish `hl` using `l.isLt`. Establish `ze : z (eI k r l) = 0` using `hz _ (Or.inl (by simp [eI]))`. Establish `zs : z (esI k r l) = 0` using `hz _ (Or.inr (by simp [esI]; omega))`. Use function extensionality and compare the values at `p`. Simplify using `only [Matrix.mulVec, dotProduct]`.

Rewrite using `[Finset.sum_eq_single (Qx3.sw k l p)]`. Rewrite using `[Qx3.w1_apply, Qx3.sw_sw, if_pos rfl]`. Break down `Qx3.tri l p with h | h | ⟨h1, h2⟩` into its components or cases. Substitute `h` using the available equality. Rewrite using `[Qx3.sw_e, zs, ze, mul_zero]`.

Substitute `h` using the available equality. Rewrite using `[Qx3.sw_es, ze, zs, mul_zero]`. Rewrite using `[Qx3.sw_o l h1 h2, Qx3.dd_o l a h1 h2, one_mul]`. Introduce `q _ hq`. Establish `: p ≠ Qx3.sw k l q` using `fun h => hq (by rw [h, Qx3.sw_sw])`.

Rewrite using `[Qx3.w1_apply, if_neg this, zero_mul]`. Introduce `h`. Conclude with `absurd (Finset.mem_univ _) h`.
-/
theorem unipotent_fixes_base_vector (l : Fin r) (a : ℂ) {z : Fin (2 * r + k + 1) → ℂ} (hz : inWb k r z) :
    w1 k r l a *ᵥ z = z := by
  have hl := l.isLt
  have ze : z (eI k r l) = 0 := hz _ (Or.inl (by simp [eI]))
  have zs : z (esI k r l) = 0 := hz _ (Or.inr (by simp [esI]; omega))
  funext p
  simp only [Matrix.mulVec, dotProduct]
  rw [Finset.sum_eq_single (Qx3.sw k l p)]
  · rw [Qx3.w1_apply, Qx3.sw_sw, if_pos rfl]
    rcases Qx3.tri l p with h | h | ⟨h1, h2⟩
    · subst h; rw [Qx3.sw_e, zs, ze, mul_zero]
    · subst h; rw [Qx3.sw_es, ze, zs, mul_zero]
    · rw [Qx3.sw_o l h1 h2, Qx3.dd_o l a h1 h2, one_mul]
  · intro q _ hq
    have : p ≠ Qx3.sw k l q := fun h => hq (by rw [h, Qx3.sw_sw])
    rw [Qx3.w1_apply, if_neg this, zero_mul]
  · intro h
    exact absurd (Finset.mem_univ _) h

/- English proof (translation)
Unfold `wCell`. Proceed by induction on `((List.finRange r).filter fun a => a.val < i.val) with`. Consider the case `nil => simp`. Consider the case `cons a l ih => rw [List.map_cons, List.prod_cons, ← Matrix.mulVec_mulVec, ih, unipotent_fixes_base_vector a _ hz]`.
-/
theorem wCell_fix_wb (i : Fin (r + 1)) (c : Fin r → ℂ) {z : Fin (2 * r + k + 1) → ℂ} (hz : inWb k r z) :
    wCell k r i c *ᵥ z = z := by
  unfold wCell
  induction ((List.finRange r).filter fun a => a.val < i.val) with
  | nil => simp
  | cons a l ih => rw [List.map_cons, List.prod_cons, ← Matrix.mulVec_mulVec, ih, unipotent_fixes_base_vector a _ hz]

/- English proof (translation)
Rewrite using `[← Matrix.mulVec_mulVec]`. Use `conv_lhs => rw [← unipotent_fixes_base_vector l a hz]`. Conclude with `Formalism.FourierDecayAlt.P.TwoByOneBlock.herm_UH (Qx3.weyl_cell_mem_unitary l ha) _ _`.
-/
theorem hermitian_invariant_unipotent (l : Fin r) {a : ℂ} (ha : a ≠ 0) {z : Fin (2 * r + k + 1) → ℂ} (hz : inWb k r z)
    (x : Mx k r) (v : Fin (2 * r + k + 1) → ℂ) :
    herm (Hpk k r) ((w1 k r l a * x) *ᵥ v) z = herm (Hpk k r) (x *ᵥ v) z := by
  rw [← Matrix.mulVec_mulVec]
  conv_lhs => rw [← unipotent_fixes_base_vector l a hz]
  exact Formalism.FourierDecayAlt.P.TwoByOneBlock.herm_UH (Qx3.weyl_cell_mem_unitary l ha) _ _

/- English proof (translation)
Rewrite using `[← Matrix.mulVec_mulVec]`. Use `conv_lhs => rw [← wCell_fix_wb i c hz]`. Conclude with `Formalism.FourierDecayAlt.P.TwoByOneBlock.herm_UH (Formalism.FourierDecayAlt.P.PBF.prod_w1_mem_unitary_Hpk c hc _) _ _`.
-/
theorem hermitian_invariant_cell_action (i : Fin (r + 1)) {c : Fin r → ℂ} (hc : c ∈ OmX r) {z : Fin (2 * r + k + 1) → ℂ}
    (hz : inWb k r z) (x : Mx k r) (v : Fin (2 * r + k + 1) → ℂ) :
    herm (Hpk k r) ((wCell k r i c * x) *ᵥ v) z = herm (Hpk k r) (x *ᵥ v) z := by
  rw [← Matrix.mulVec_mulVec]
  conv_lhs => rw [← wCell_fix_wb i c hz]
  exact Formalism.FourierDecayAlt.P.TwoByOneBlock.herm_UH (Formalism.FourierDecayAlt.P.PBF.prod_w1_mem_unitary_Hpk c hc _) _ _

end

end Formalism.FourierDecayAlt.P.CutMP.TemperedBoundGL3

import Formalism.HermitianCurvature.HermitianCurvatureProofs.RightTypeAction0
import Formalism.HermitianCurvature.HermitianCurvatureProofs.LeftTypeAction

open Matrix Finset Filter Topology

noncomputable section

namespace Formalism.FourierDecayAlt.P.CutMP.SmoothTransferRegularity

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

namespace LeftTypeActionHermitianCurvature

variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [NormedSpace ℂ Wp] [NormedAddCommGroup Wq]
  [NormedSpace ℂ Wq] [FiniteDimensional ℂ Wp] {z z' : Fin (2 * r + k + 1) → ℂ} {π : Mx k r → (Wp →L[ℂ] Wp)}
  {π' : Mx k r → (Wq →L[ℂ] Wq)} {D : Set (Mx k r)} {J : Mx k r → (Wq →L[ℂ] Wp)} {i : Fin (r + 1)} {mm : ℕ∞}

/- English proof (translation)
Establish an intermediate fact. Simplify to obtain the desired conclusion from the available facts.
-/
theorem mem_left (hD : IsDom k r z z' i D) {g h : Mx k r} (hg : g ∈ Glev k r i ∩ D)
    (hh : h ∈ UWset k r z) : h * g ∈ Glev k r i ∩ D := by
  have := Qx8.dom_mem hD hg hh (Qx8.nlev_one _) (Qx8.uw_one z') (Qx8.nlev_one _)
  simpa using this

/- English proof (translation)
Establish an intermediate fact. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Rewrite the indicated hypotheses using the stated equalities. Establish an intermediate fact.

Rewrite the indicated hypotheses using the stated equalities. Rewrite the conclusion using the stated equalities.
-/
theorem J_left (hπ : IsCRepOn (UWset k r z) π) (hJ : J ∈ Gr.FFlM mm k r z z' π π' i D) {g h : Mx k r}
    (hg : g ∈ Glev k r i ∩ D) (hh : h ∈ UWset k r z) : J (h * g) = (π h).comp (J g) := by
  have e1 := hJ.2.2.2 g hg 1 (Qx8.uw_one z) 1 (Qx8.uw_one z')
  have e2 := hJ.2.2.2 g hg h hh 1 (Qx8.uw_one z')
  rw [Matrix.one_mul, Matrix.mul_one, hπ.1] at e1
  rw [Matrix.mul_one] at e2
  have e3 : (1 : Wp →L[ℂ] Wp).comp ((J g).comp (π' 1)) = (J g).comp (π' 1) := ContinuousLinearMap.id_comp _
  rw [e3] at e1
  rw [e2, ← e1]

/- English proof (translation)
Establish an intermediate fact. Introduce a local definition for the expression. Establish an intermediate fact. Establish an intermediate fact. Apply function extensionality and compare values at an arbitrary argument.

Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression. Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem ld_left (hD : IsDom k r z z' i D) (hπ : IsCRepOn (UWset k r z) π)
    (hc : ContinuousOn π (UWset k r z)) (hJ : J ∈ Gr.FFlM mm k r z z' π π' i D)
    {F : Mx k r → (Wq →L[ℂ] Wp)} {B : Wp →L[ℂ] Wp}
    (hF : ∀ g ∈ Glev k r i ∩ D, F g = B.comp (J g)) {X : Mx k r} (hX : QrD.InLieW k r z X)
    {g : Mx k r} (hg : g ∈ Glev k r i ∩ D) : LdV X F g = (B.comp (QrD.dOp π X)).comp (J g) := by
  have h := QrD.dOp_hasDeriv hπ hc hX
  let L : (Wp →L[ℂ] Wp) →L[ℂ] (Wq →L[ℂ] Wp) :=
    (ContinuousLinearMap.compL ℂ Wq Wp Wp B).comp ((ContinuousLinearMap.compL ℂ Wq Wp Wp).flip (J g))
  have h2 := (L.restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt (0 : ℝ) h
  have h3 : (fun t : ℝ => F (NormedSpace.exp ((t : ℂ) • X) * g)) =
      (L.restrictScalars ℝ) ∘ fun t : ℝ => π (NormedSpace.exp ((t : ℂ) • X)) := by
    funext t
    rw [hF _ (mem_left hD hg (QrD.exp_uw hX t)), J_left hπ hJ hg (QrD.exp_uw hX t)]
    rfl
  unfold LdV
  rw [h3]
  exact h2.deriv

/- English proof (translation)
Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities. By extensionality, compare the relevant components. Simplify using the standard rewrite rules.
-/
theorem lz_left (hD : IsDom k r z z' i D) (hπ : IsCRepOn (UWset k r z) π)
    (hc : ContinuousOn π (UWset k r z)) (hJ : J ∈ Gr.FFlM mm k r z z' π π' i D)
    {F : Mx k r → (Wq →L[ℂ] Wp)} {B : Wp →L[ℂ] Wp}
    (hF : ∀ g ∈ Glev k r i ∩ D, F g = B.comp (J g)) {Z : Mx k r}
    (h1 : QrD.InLieW k r z (hpart1 (Hpk k r) Z)) (h2 : QrD.InLieW k r z (hpart2 (Hpk k r) Z))
    {g : Mx k r} (hg : g ∈ Glev k r i ∩ D) :
    LZ (Hpk k r) Z F g = (B.comp (QrD.ecOp π Z)).comp (J g) := by
  unfold LZ QrD.ecOp
  rw [ld_left hD hπ hc hJ hF h1 hg, ld_left hD hπ hc hJ hF h2 hg]
  ext v
  simp

/- English proof (translation)
Proceed by induction. Treat this case separately. Fix the arbitrary inputs or assume the hypotheses. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities.

Both sides reduce to the same expression. Treat this case separately. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Simplify using the standard rewrite rules.

Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. By extensionality, compare the relevant components. Simplify using the standard rewrite rules.

A detailed English derivation is pending.
-/
theorem fold_left (hD : IsDom k r z z' i D) (hπ : IsCRepOn (UWset k r z) π)
    (hc : ContinuousOn π (UWset k r z)) (hJ : J ∈ Gr.FFlM mm k r z z' π π' i D)
    (L : List (ℂ × Mx k r))
    (hL : ∀ p ∈ L, QrD.InLieW k r z (hpart1 (Hpk k r) p.2) ∧ QrD.InLieW k r z (hpart2 (Hpk k r) p.2)) :
    ∀ (F : Mx k r → (Wq →L[ℂ] Wp)) (B : Wp →L[ℂ] Wp), (∀ g ∈ Glev k r i ∩ D, F g = B.comp (J g)) →
      ∀ g ∈ Glev k r i ∩ D, ∀ v,
        (L.map fun p => fun y : Mx k r → (Wq →L[ℂ] Wp) => p.1 • y + LZ (Hpk k r) p.2 y).foldl (fun h T => T h) F g v =
          B ((L.map fun p => fun y : Wp => p.1 • y + EcRep (Hpk k r) π p.2 y).foldr (fun T h => T h) (J g v)) := by
  induction L with
  | nil =>
    intro F B hF g hg v
    simp only [List.map_nil, List.foldl_nil, List.foldr_nil]
    rw [hF g hg]
    rfl
  | cons p L ih =>
    intro F B hF g hg v
    have hp := hL p (by simp)
    simp only [List.map_cons, List.foldl_cons, List.foldr_cons]
    rw [ih (fun q hq => hL q (by simp [hq])) (p.1 • F + LZ (Hpk k r) p.2 F) (p.1 • B + B.comp (QrD.ecOp π p.2))
      (fun x hx => by
        simp only [Pi.add_apply, Pi.smul_apply]
        rw [lz_left hD hπ hc hJ hF hp.1 hp.2 hx, hF x hx]
        ext v
        simp) g hg v, QrD.ecRep_eq hπ hc hp.1 hp.2]
    simp

end LeftTypeActionHermitianCurvature

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Replace the relevant objects with their definitions. Simplify using the standard rewrite rules. Reduce the conclusion to the remaining proof obligations. Reduce the equality to equality of the corresponding arguments.

Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Rewrite the indicated hypotheses using the stated equalities. Extract witnesses or component facts from the available result. Simplify using the standard rewrite rules.

Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression. A detailed English derivation is pending.
-/
theorem left_type_action_holds : LeftTypeAction0 := by
  intro Wp Wq _ _ _ _ _ k r m z z' π π' D mm _ _ hD hπ hc J hJ g hg Bs hB w v
  unfold capLft capRep qmFrev qmF
  simp only [Finset.sum_apply, Pi.smul_apply, _root_.sum_apply, _root_.smul_apply]
  refine Finset.sum_congr rfl fun σ _ => ?_
  congr 1
  have e1 := LeftTypeActionHermitianCurvature.fold_left hD hπ hc hJ
    (List.ofFn fun j : Fin m => ((if σ j = j then w - ((j : ℕ) : ℂ) else 0 : ℂ), unitB (Hpk k r) Bs (σ j) j))
    (by
      intro p hp
      rw [List.mem_ofFn] at hp
      obtain ⟨j, rfl⟩ := hp
      exact QrD.frame_lie hB (σ j) j) J 1 (fun x _ => (ContinuousLinearMap.id_comp _).symm) g hg v
  simp only [List.map_ofFn, Function.comp_def, ite_smul, zero_smul] at e1
  simp only [id]
  rw [e1]
  rfl

end Formalism.FourierDecayAlt.P.CutMP.SmoothTransferRegularity

import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsSumFrame
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.SelfDualLatticePairingDual

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.FinPl IsDedekindDomain NumberField
open scoped TensorProduct

noncomputable section

set_option synthInstance.maxHeartbeats 160000

namespace GlobalTheory.SelfDualAt

variable {D : D7}

open Classical in

def indP (P : Pl D → Prop) : Af D.host.F :=
  ⟨fun v => if P v then 1 else 0, Filter.Eventually.of_forall fun v => by
    by_cases h : P v
    · simp only [h, if_true]; exact one_mem _
    · simp only [h, if_false]; exact zero_mem _⟩

open Classical in
/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem evalV_indP (P : Pl D → Prop) (v : Pl D) : evalV D.host.F v (indP P) = if P v then 1 else 0 := rfl

def cP (P : Pl D → Prop) : AF D.host.F := pairA D.host.F 0 (indP P)

/- English proof (translation)
Express the relevant assertion in an equivalent form by its definition. Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression.
-/
theorem cA_alg (a : AF D.host.F) : cA D (algebraMap (AF D.host.F) (AE D) a) = algebraMap (AF D.host.F) (AE D) a := by
  change a ⊗ₜ[D.host.F] D.sp.cm.sig 1 = _
  rw [map_one]
  rfl

/- English proof (translation)
Replace the relevant objects with their definitions. Simplify using the standard rewrite rules. Reduce the conclusion to the remaining proof obligations.
-/
theorem hO_smul_swap (S T : HSp D) (c : AF D.host.F) (x y : WO S T) : hO S T x (c • y) = hO S T (c • x) y := by
  unfold hO
  simp only [Matrix.smul_apply, Algebra.smul_def, map_mul, cA_alg]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ =>
    Finset.sum_congr rfl fun c' _ => Finset.sum_congr rfl fun d _ => by ring

/- English proof (translation)
Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities.
-/
theorem symplO_smul_swap (S T : HSp D) (c : AF D.host.F) (x y : WO S T) :
    symplO S T x (c • y) = symplO S T (c • x) y := by
  unfold symplO
  rw [hO_smul_swap]

set_option maxHeartbeats 800000 in

/- English proof (translation)
Proceed by induction. Treat this case separately. Treat this case separately. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.

Simplify using the standard rewrite rules. Treat this case separately. Simplify using the standard rewrite rules. A detailed English derivation is pending.
-/
theorem compFin_repr (w : Pl D) (y : Af D.host.F ⊗[D.host.F] D.host.E) (k : Fin (Module.finrank D.host.F D.host.E)) :
    (Algebra.TensorProduct.basis (Fv D.host.F w) (Module.finBasis D.host.F D.host.E)).repr
        (GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter.compFin D w y) k =
      evalV D.host.F w ((Algebra.TensorProduct.basis (Af D.host.F) (Module.finBasis D.host.F D.host.E)).repr y k) := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul a e =>
    have h : GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter.compFin D w (a ⊗ₜ[D.host.F] e) = evalV D.host.F w a ⊗ₜ[D.host.F] e := rfl
    rw [h, Algebra.TensorProduct.basis_repr_tmul, Algebra.TensorProduct.basis_repr_tmul]
    simp [Finsupp.smul_apply, Finsupp.mapRange_apply, map_mul, AlgHom.commutes]
  | add x y hx hy =>
    simp only [RingHom.map_add, LinearEquiv.map_add, Finsupp.add_apply, hx, hy]
    exact (RingHom.map_add (evalV D.host.F w).toRingHom _ _).symm

/- English proof (translation)
Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression.

Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Simplify to obtain the desired conclusion from the available facts. A detailed English derivation is pending.
-/
theorem eq_zero_of_compFin (y : Af D.host.F ⊗[D.host.F] D.host.E) (h : ∀ w, GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter.compFin D w y = 0) :
    y = 0 := by
  have hr : (Algebra.TensorProduct.basis (Af D.host.F) (Module.finBasis D.host.F D.host.E)).repr y = 0 := by
    refine Finsupp.ext fun k => ?_
    have hk : ∀ w : Pl D, evalV D.host.F w
        ((Algebra.TensorProduct.basis (Af D.host.F) (Module.finBasis D.host.F D.host.E)).repr y k) = 0 := fun w => by
      rw [← compFin_repr, h w, map_zero]; rfl
    rw [Finsupp.zero_apply]
    refine FiniteAdeleRing.ext (R := 𝓞 D.host.F) D.host.F fun w => ?_
    exact hk w
  simpa using hr

set_option maxHeartbeats 800000 in
/- English proof (translation)
Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Simplify using the standard rewrite rules. Both sides reduce to the same expression. Rewrite the conclusion using the stated equalities.

A detailed English derivation is pending.
-/
theorem compFin_alg_cP (P : Pl D → Prop) (w : Pl D) (hw : P w) :
    GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter.compFin D w (finPart D (algebraMap (AF D.host.F) (AE D) (cP P))) = 1 := by
  rw [Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply, GlobalTheory.LatVac.finPart_tmul]
  have h : GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter.compFin D w (sndA D.host.F (cP P) ⊗ₜ[D.host.F] (1 : D.host.E)) =
      evalV D.host.F w (indP P) ⊗ₜ[D.host.F] (1 : D.host.E) := by
    simp only [GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter.compFin, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, Algebra.TensorProduct.map_tmul,
      AlgHom.id_apply]
    rfl
  rw [h, evalV_indP, if_pos hw]
  exact Algebra.TensorProduct.one_def.symm

set_option maxHeartbeats 800000 in

/- English proof (translation)
Rewrite the indicated hypotheses using the stated equalities. Extract witnesses or component facts from the available result. Rewrite the indicated hypotheses using the stated equalities. Establish an intermediate fact. Reduce the claim to the hypotheses of an applicable result.

Rewrite the conclusion using the stated equalities. Reduce the claim to the hypotheses of an applicable result. Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities. Consider separately whether the proposition holds or fails.

Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Rewrite the conclusion using the stated equalities. Rewrite the indicated hypotheses using the stated equalities.

A detailed English derivation is pending.
-/
theorem algebraMap_placeIdempotent_mul (P : Pl D → Prop) (z : AE D) (hz : z ∈ idAt D P) :
    algebraMap (AF D.host.F) (AE D) (cP P) * z = z := by
  rw [idAt, Ideal.mem_inf, Ideal.mem_iInf] at hz
  obtain ⟨hinf, hfin⟩ := hz
  rw [RingHom.mem_ker] at hinf
  have h0 : (1 - algebraMap (AF D.host.F) (AE D) (cP P)) * z = 0 := by
    apply GlobalTheory.LatVac.eq_zero_of_parts
    · rw [RingHom.map_mul, hinf, mul_zero]
    · apply eq_zero_of_compFin
      intro w
      rw [RingHom.map_mul, RingHom.map_mul]
      by_cases hw : P w
      · rw [RingHom.map_sub, RingHom.map_sub, RingHom.map_one, RingHom.map_one, compFin_alg_cP P w hw, sub_self, zero_mul]
      · have h1 := hfin ⟨w, hw⟩
        rw [RingHom.mem_ker] at h1
        rw [show GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter.compFin D w (finPart D z) = compAt D w z from rfl, h1, mul_zero]
  rw [sub_mul, one_mul, sub_eq_zero] at h0
  exact h0.symm

/- English proof (translation)
Proceed by induction. Treat this case separately. Extract witnesses or component facts from the available result. Reduce the claim to the hypotheses of an applicable result. Reduce the conclusion to the remaining proof obligations.

Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses.

Rewrite the conclusion using the stated equalities. By extensionality, compare the relevant components. Rewrite the conclusion using the stated equalities. Reduce the equality to equality of the corresponding arguments. Reduce the conclusion to the remaining proof obligations.

Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression. Treat this case separately. Treat this case separately. Treat this case separately.

A detailed English derivation is pending.
-/
theorem smul_mem_latO (S T : HSp D) (LS : Set (Fin S.rank → D.host.E)) (LT : Set (Fin T.rank → D.host.E))
    (P : Pl D → Prop) (y : WO S T) (hy : y ∈ latO S T LS LT fun _ => True) : cP P • y ∈ latO S T LS LT P := by
  induction hy using AddSubgroup.closure_induction with
  | mem y hy =>
    obtain ⟨α, hα, -, a, ha, s, hs, t, ht, rfl⟩ := hy
    apply AddSubgroup.subset_closure
    refine ⟨indP P * α, ?_, ?_, a, ha, s, hs, t, ht, ?_⟩
    · intro v
      rw [map_mul]
      refine mul_mem ?_ (hα v)
      rw [evalV_indP]
      split_ifs
      · exact one_mem _
      · exact zero_mem _
    · intro v hv
      rw [map_mul, evalV_indP, if_neg hv, zero_mul]
    · ext i j
      rw [Matrix.smul_apply, Matrix.of_apply, Matrix.of_apply, TensorProduct.smul_tmul', smul_eq_mul]
      congr 1
      refine Prod.ext ?_ ?_
      · show (0 : Ainf D.host.F) * 0 = 0
        rw [zero_mul]
      · rfl
  | zero => rw [smul_zero]; exact zero_mem _
  | add x y _ _ h1 h2 => rw [smul_add]; exact add_mem h1 h2
  | neg x _ h => rw [smul_neg]; exact neg_mem h

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Establish an intermediate fact. By extensionality, compare the relevant components. Establish an intermediate fact.

Rewrite the indicated hypotheses using the stated equalities. Simplify to obtain the desired conclusion from the available facts. Establish an intermediate fact. Reduce the claim to the hypotheses of an applicable result. Assume the hypotheses and unpack their components.

Supply the required witnesses or components. Establish an intermediate fact. By extensionality, compare the relevant components. Rewrite the conclusion using the stated equalities. Prove the components needed by the constructor for the conclusion.

Fix the arbitrary inputs or assume the hypotheses. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact.

Rewrite the indicated hypotheses using the stated equalities. Use the resulting assumption. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem latO_ann_at : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (S T : HSp D) (LS : Lat S) (LT : Lat T), IsSelfDualC S LS → IsSelfDualC T LT → ∀ (P : Pl D → Prop) (u : WO S T), MxAt P u → (u ∈ latO S T (LS : Set _) (LT : Set _) P ↔ ∀ u' ∈ latO S T (LS : Set _) (LT : Set _) P, ψ (symplO S T u u') = 1) := by
  intro D ψ hψ S T LS LT hS hT P u hu
  have key := (GlobalTheory.LatVac.latO_selfDual_approx_sign D ψ S T LS LT hψ hS hT).1
  have hinf : u.map (infPart D) = 0 := by
    ext i j
    have h := (Ideal.mem_inf.1 (hu i j)).1
    rw [RingHom.mem_ker] at h
    simpa using h
  have hle : latO S T (LS : Set _) (LT : Set _) P ≤ latO S T (LS : Set _) (LT : Set _) fun _ => True := by
    apply AddSubgroup.closure_mono
    rintro w ⟨α, hα, -, rest⟩
    exact ⟨α, hα, fun v h => (h trivial).elim, rest⟩
  have hfix : cP P • u = u := by
    ext i j
    rw [Matrix.smul_apply, Algebra.smul_def]
    exact algebraMap_placeIdempotent_mul P _ (hu i j)
  constructor
  · intro hm u' hu'
    exact (key u hinf).1 (hle hm) u' (hle hu')
  · intro hann
    have h2 : ∀ y ∈ latO S T (LS : Set _) (LT : Set _) (fun _ => True), ψ (symplO S T u y) = 1 := by
      intro y hy
      have h := hann _ (smul_mem_latO S T _ _ P y hy)
      rwa [symplO_smul_swap, hfix] at h
    rw [← hfix]
    exact smul_mem_latO S T _ _ P u ((key u hinf).2 h2)

end GlobalTheory.SelfDualAt

end

import Formalism.LocalToGlobal.IndefiniteReal.FrameExistence.FramesExistOfDiagonalTypePlaces

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mi
open IsDedekindDomain NumberField
open scoped TensorProduct

namespace Formalism.IndefR.Seed.FrmP

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

def coordMap (V : HSp D) : (Fin V.rank → D.host.E) →ₗ[𝓞 D.host.E] V.V :=
  (V.frame.equivFun.symm.toLinearMap).restrictScalars (𝓞 D.host.E)

/- English proof (translation)
Simplify using the standard rewrite rules.
-/
theorem coordMap_apply (V : HSp D) (x : Fin V.rank → D.host.E) : coordMap V x = ∑ i, x i • V.frame i := by
  simp [coordMap, Module.Basis.equivFun_symm_apply]

def coordL (V : HSp D) : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E) := V.L0.comap (coordMap V)

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression. A detailed English derivation is pending.
-/
theorem mem_coordL (V : HSp D) (x : Fin V.rank → D.host.E) : x ∈ coordL V ↔ x ∈ Formalism.MainNotions.StandardLattice.L0c D V := by
  show coordMap V x ∈ V.L0 ↔ _
  rw [coordMap_apply]
  rfl

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Reduce the conclusion to the remaining proof obligations. Expand and normalize the polynomial expressions, which then agree. A detailed English derivation is pending.
-/
theorem hform_coord (V : HSp D) (x y : Fin V.rank → D.host.E) :
    Formalism.UG.hform (D.sp.cm.sig : D.host.E →+* D.host.E) V.gram x y = V.hT (coordMap V x) (coordMap V y) := by
  rw [coordMap_apply, coordMap_apply]
  simp only [Formalism.UG.hform, HSpace.gram, map_sum, LinearMap.map_smulₛₗ, LinearMap.sum_apply, LinearMap.smul_apply,
    smul_eq_mul, Finset.mul_sum]
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  show star (x i) * _ * y j = y j * (star (x i) * _)
  ring

/- English proof (translation)
By extensionality, compare the relevant components. Establish an intermediate fact. Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules.

Prove the components needed by the constructor for the conclusion. Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Supply the required witnesses or components.

Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Supply the required witnesses or components. A detailed English derivation is pending.
-/
theorem dualSet_coordL (V : HSp D) :
    Formalism.BasicNotions.dualSet (D.sp.cm.sig : D.host.E →+* D.host.E) V.gram (coordL V) = (coordL V : Set _) := by
    ext y
    have hU := V.baseLattice_isUnimodular
    unfold Formalism.HermitianLatticesTheory.IsUnimodular Formalism.HermitianLatticesTheory.dual at hU
    show (∀ x ∈ coordL V, _ ∈ _) ↔ coordMap V y ∈ V.L0
    rw [← hU]
    simp only [Formalism.E.hdual, Submodule.mem_iInf, Submodule.mem_comap, LinearMap.restrictScalars_apply, Submodule.mem_one]
    constructor
    · intro h v hv
      obtain ⟨x, rfl⟩ : ∃ x, coordMap V x = v := ⟨V.frame.equivFun v, by simp [coordMap]⟩
      obtain ⟨b, hb⟩ := h x hv
      exact ⟨b, by rw [hb, hform_coord]⟩
    · intro h x hx
      obtain ⟨b, hb⟩ := h (coordMap V x) hx
      exact ⟨b, by rw [hform_coord, hb]⟩

/- English proof (translation)
Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities.
-/
theorem dualL_coordL (V : HSp D) : Formalism.L2.Herm.dualL D.sp.cm V (coordL V) = coordL V := by
  unfold Formalism.L2.Herm.dualL
  rw [dualSet_coordL, Submodule.span_eq]

/- English proof (translation)
Extract witnesses or component facts from the available result. A detailed English derivation is pending.
-/
theorem eToEAf_mem_intAf_of_isIntegral {a : D.host.E} (ha : IsIntegral ℤ a) :
    eToEAf D a ∈ Formalism.L2.Herm.intAf D.host.F D.host.E := by
  obtain ⟨b, rfl⟩ := (IsIntegralClosure.isIntegral_iff (A := 𝓞 D.host.E)).1 ha
  exact Subring.subset_closure (Or.inl ⟨⟨((b : 𝓞 D.host.E) : D.host.E), ⟨b, rfl⟩⟩, rfl⟩)

set_option synthInstance.maxHeartbeats 400000 in

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Simplify using the standard rewrite rules. Prove the components needed by the constructor for the conclusion. Fix the arbitrary inputs or assume the hypotheses. Proceed by induction.

Treat this case separately. Extract witnesses or component facts from the available result. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Treat this case separately.

Treat this case separately. Treat this case separately. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses.

Reduce the conclusion to the remaining proof obligations. Reduce the conclusion to the remaining proof obligations. Consider separately whether the proposition holds or fails. Substitute using the available equality. Simplify to obtain the desired conclusion from the available facts.

Simplify to obtain the desired conclusion from the available facts. Establish an intermediate fact. Establish an intermediate fact. Apply function extensionality and compare values at an arbitrary argument. Rewrite the conclusion using the stated equalities.

Simplify using the standard rewrite rules. Fix the arbitrary inputs or assume the hypotheses. Simplify using the standard rewrite rules. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities.

A detailed English derivation is pending.
-/
theorem isFrame_one_std (V : HSp D) (hV : FrmC.StdLat V) :
    Formalism.L2.DIV.IsFrame (1 : GL (Fin V.rank) (EAf D)) (coordL V) := by
  intro x
  simp only [inv_one, Units.val_one, Matrix.one_mulVec]
  constructor
  · intro hx
    induction hx using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨lv, hlv, rfl⟩ := hy
      intro i
      have hi := ((hV lv).1 ((mem_coordL V lv).1 hlv)) i
      exact eToEAf_mem_intAf_of_isIntegral hi
    | zero => intro i; exact zero_mem _
    | add x y _ _ hx hy => intro i; exact add_mem (hx i) (hy i)
    | smul c x _ hx => intro i; exact mul_mem c.2 (hx i)
  · intro hx
    have hv : ∀ i, (fun l => eToEAf D ((Pi.single i (1 : D.host.E) : Fin V.rank → D.host.E) l)) ∈
        Formalism.L2.Herm.hatL (F := D.host.F) (coordL V) := by
      intro i
      refine Submodule.subset_span ⟨_, ?_, rfl⟩
      refine (mem_coordL V _).2 ((hV _).2 fun l => ?_)
      by_cases h : l = i
      · subst h; simpa using isIntegral_one
      · simpa [Pi.single_apply, h] using isIntegral_zero
    have hc : ∀ i, (fun l => x i * eToEAf D ((Pi.single i (1 : D.host.E) : Fin V.rank → D.host.E) l)) ∈
        Formalism.L2.Herm.hatL (F := D.host.F) (coordL V) := fun i =>
      Submodule.smul_mem (Formalism.L2.Herm.hatL (F := D.host.F) (coordL V))
        (⟨x i, hx i⟩ : Formalism.L2.Herm.intAf D.host.F D.host.E) (hv i)
    have hsum : (∑ i, (fun l => x i * eToEAf D ((Pi.single i (1 : D.host.E) : Fin V.rank → D.host.E) l))) = x := by
      funext l
      rw [Finset.sum_apply, Finset.sum_eq_single l]
      · simp
      · intro b _ hb; simp [Pi.single_apply, hb.symm]
      · simp
    rw [← hsum]
    exact Submodule.sum_mem _ fun i _ => hc i

/- English proof (translation)
Reduce the conclusion to the remaining proof obligations. Simplify to obtain the desired conclusion from the available facts. Simplify to obtain the desired conclusion from the available facts.
-/
theorem isSDFrame_std (V : HSp D) (hV : FrmC.StdLat V) (N : ℕ) :
    IsSDFrame V (1 : GL (Fin V.rank) (EAf D)) (coordL V) N := by
  refine ⟨0, isFrame_one_std V hV, dualL_coordL V, by simp, fun x hx => ?_, fun x hx => ?_⟩
  · simpa using (mem_coordL V x).2 hx
  · simpa using (mem_coordL V x).1 hx

variable (D) in

def SDFramesExist : Prop :=
  ∃ (ΛY : ∀ j, Submodule (𝓞 D.host.E) (Fin (Yc D j).rank → D.host.E))
    (ΛX : Submodule (𝓞 D.host.E) (Fin D.sp.X'.rank → D.host.E))
    (ΛV : ∀ i, Submodule (𝓞 D.host.E) (Fin (Vc D i).rank → D.host.E))
    (ΛW : ∀ i, Submodule (𝓞 D.host.E) (Fin (Wc D i).rank → D.host.E))
    (βY : ∀ j, GL (Fin (Yc D j).rank) (EAf D)) (βX : GL (Fin D.sp.X'.rank) (EAf D))
    (βV : ∀ i, GL (Fin (Vc D i).rank) (EAf D)) (βW : ∀ i, GL (Fin (Wc D i).rank) (EAf D)),
    Seed.Frm.SDFrames ΛY ΛX ΛV ΛW βY βX βV βW

/- English proof (translation)
Supply the required witnesses or components.
-/
theorem sdFramesExist_of_std (hY : ∀ j, FrmC.StdLat (D.sp.Y j)) (hX : FrmC.StdLat D.sp.X')
    (hV : ∀ j, FrmC.StdLat (D.sp.V j)) (hW : ∀ j, FrmC.StdLat (D.sp.W j)) : SDFramesExist D :=
  ⟨fun j => coordL (Yc D j), coordL D.sp.X', fun i => coordL (Vc D i), fun i => coordL (Wc D i),
    fun _ => 1, 1, fun _ => 1, fun _ => 1,
    fun j _ => isSDFrame_std _ (hY _) _, isSDFrame_std _ hX _, fun i => isSDFrame_std _ (hV _) _,
    fun i => isSDFrame_std _ (hW _) _⟩

/- English proof (translation)
Extract witnesses or component facts from the available result. A detailed English derivation is pending.
-/
theorem self_dual_frames_exist_of_diagonal (h : FrmC.IsG2 D) : SDFramesExist D := by
  obtain ⟨pz, lam, hF⟩ := FrmC.diagonal_entries_exist D h
  exact sdFramesExist_of_std hF.standard_lattice_Y hF.standard_lattice_X hF.standard_lattice_V hF.standard_lattice_W

end Formalism.IndefR.Seed.FrmP

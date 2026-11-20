import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.BaseCoefJump
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CoefficientBaseChange.CoordBaseChange
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CoefficientBaseChange.FinrankIInfKerEquiv

open TensorProduct

namespace CJ

section Ext

variable {K L : Type} [Field K] [Field L] [Algebra K L] {W : Type} [AddCommGroup W] [Module K W]

noncomputable def extS (L : Type) [Field L] [Algebra K L] (S : Submodule K W) : Submodule L (L ⊗[K] W) :=
  LinearMap.range (S.subtype.baseChange L)

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Assume the hypotheses and unpack their components. Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact.

Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Supply the required witnesses or components. A detailed English derivation is pending.
-/
theorem mem_extS {ι : Type} [DecidableEq ι] (b : Module.Basis ι K L) (S : Submodule K W) (x : L ⊗[K] W) :
    x ∈ extS L S ↔ ∀ i, equivFinsuppOfBasisLeft b x i ∈ S := by
  constructor
  · rintro ⟨y, rfl⟩ i
    rw [PI.CoefExt.coord_baseChange, Finsupp.mapRange_apply]
    exact (equivFinsuppOfBasisLeft b y i).2
  · intro hc
    have hx' : x = (equivFinsuppOfBasisLeft b x).sum fun i n => b i ⊗ₜ n := by
      rw [← equivFinsuppOfBasisLeft_symm_apply, LinearEquiv.symm_apply_apply]
    rw [hx', Finsupp.sum]
    refine Submodule.sum_mem _ fun i _ => ?_
    exact ⟨b i ⊗ₜ ⟨equivFinsuppOfBasisLeft b x i, hc i⟩, by simp [LinearMap.baseChange_tmul]⟩

/- English proof (translation)
Introduce a local definition for the expression. By extensionality, compare the relevant components. Simplify using the standard rewrite rules.
-/
theorem extS_inf (S T : Submodule K W) : extS L (S ⊓ T) = extS L S ⊓ extS L T := by
  classical
  let b := Module.Basis.ofVectorSpace K L
  ext x
  simp only [Submodule.mem_inf, mem_extS b, forall_and]

/- English proof (translation)
Introduce a local definition for the expression. By extensionality, compare the relevant components. Simplify using the standard rewrite rules. A detailed English derivation is pending.
-/
theorem extS_iInf {J : Type} (S : J → Submodule K W) : extS L (⨅ j, S j) = ⨅ j, extS L (S j) := by
  classical
  let b := Module.Basis.ofVectorSpace K L
  ext x
  simp only [Submodule.mem_iInf, mem_extS b]
  exact forall_comm

/- English proof (translation)
Introduce a local definition for the expression. By extensionality, compare the relevant components. Rewrite the conclusion using the stated equalities. Prove the components needed by the constructor for the conclusion. Fix the arbitrary inputs or assume the hypotheses.

Rewrite the conclusion using the stated equalities. Reduce the claim to the hypotheses of an applicable result. Rewrite the conclusion using the stated equalities. By extensionality, compare the relevant components. Simplify to obtain the desired conclusion from the available facts.

Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Simplify using the standard rewrite rules. A detailed English derivation is pending.
-/
theorem extS_ker {W₂ : Type} [AddCommGroup W₂] [Module K W₂] (N : W →ₗ[K] W₂) :
    extS L (LinearMap.ker N) = LinearMap.ker (N.baseChange L) := by
  classical
  let b := Module.Basis.ofVectorSpace K L
  ext x
  rw [mem_extS b]
  constructor
  · intro h
    rw [LinearMap.mem_ker]
    apply (equivFinsuppOfBasisLeft b).injective
    rw [PI.CoefExt.coord_baseChange, map_zero]
    ext i
    simpa using h i
  · intro h i
    have h2 := congrArg (fun z => equivFinsuppOfBasisLeft b z i) (LinearMap.mem_ker.mp h)
    simp only [PI.CoefExt.coord_baseChange, Finsupp.mapRange_apply, map_zero, Finsupp.coe_zero,
      Pi.zero_apply] at h2
    exact h2

/- English proof (translation)
Introduce a local definition for the expression. Reduce the claim to the hypotheses of an applicable result. Assume the hypotheses and unpack their components. Proceed by induction. Treat this case separately.

Treat this case separately. Extract witnesses or component facts from the available result. Supply the required witnesses or components. Treat this case separately. Assume the hypotheses and unpack their components.

Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem extS_range {U : Type} [AddCommGroup U] [Module K U] (N : U →ₗ[K] W) :
    extS L (LinearMap.range N) = LinearMap.range (N.baseChange L) := by
  classical
  let b := Module.Basis.ofVectorSpace K L
  apply le_antisymm
  · rintro _ ⟨y, rfl⟩
    induction y using TensorProduct.induction_on with
    | zero => simp
    | tmul l s =>
      obtain ⟨u, hu⟩ := s.2
      exact ⟨l ⊗ₜ u, by simp [LinearMap.baseChange_tmul, hu]⟩
    | add y z hy hz => rw [map_add]; exact Submodule.add_mem _ hy hz
  · rintro _ ⟨y, rfl⟩
    rw [mem_extS b]
    intro i
    rw [PI.CoefExt.coord_baseChange, Finsupp.mapRange_apply]
    exact LinearMap.mem_range_self _ _

/- English proof (translation)
Introduce a local definition for the expression. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Establish an intermediate fact.

Extract witnesses or component facts from the available result. Establish an intermediate fact. Establish an intermediate fact. Simplify using the standard rewrite rules. Establish an intermediate fact.

Rewrite the indicated hypotheses using the stated equalities. Use the resulting assumption.
-/
theorem le_of_extS_le {S T : Submodule K W} (h : extS L S ≤ extS L T) : S ≤ T := by
  classical
  let b := Module.Basis.ofVectorSpace K L
  intro s hs
  have h1 : (1 : L) ⊗ₜ[K] s ∈ extS L T :=
    h ⟨(1 : L) ⊗ₜ[K] (⟨s, hs⟩ : S), by simp [LinearMap.baseChange_tmul]⟩
  rw [mem_extS b] at h1
  have hne : b.repr 1 ≠ 0 := fun h0 => one_ne_zero (b.repr.map_eq_zero_iff.mp h0)
  obtain ⟨i, hi⟩ := Finsupp.support_nonempty_iff.mpr hne
  have hi' : b.repr 1 i ≠ 0 := Finsupp.mem_support_iff.mp hi
  have hc : equivFinsuppOfBasisLeft b ((1 : L) ⊗ₜ[K] s) i = b.repr 1 i • s := by
    simp
  have h2 := T.smul_mem (b.repr 1 i)⁻¹ (hc ▸ h1 i)
  rwa [smul_smul, inv_mul_cancel₀ hi', one_smul] at h2

/- English proof (translation)
Fix the arbitrary inputs and assume any hypotheses. A detailed English derivation is pending.
-/
theorem extS_injective : Function.Injective (extS (K := K) (W := W) L) := fun _ _ h =>
  le_antisymm (le_of_extS_le h.le) (le_of_extS_le h.ge)

end Ext

section Equiv

variable {R X Y : Type} [Field R] [AddCommGroup X] [AddCommGroup Y] [Module R X] [Module R Y]

/- English proof (translation)
By extensionality, compare the relevant components. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Reduce the conclusion to the remaining proof obligations. Prove the components needed by the constructor for the conclusion.

Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Use the resulting assumption. Fix the arbitrary inputs or assume the hypotheses. Reduce the claim to the hypotheses of an applicable result.

Rewrite the conclusion using the stated equalities.
-/
theorem map_iInf_ker {J : Type} (e : X ≃ₗ[R] Y) (N : J → X →ₗ[R] X) (N' : J → Y →ₗ[R] Y)
    (h : ∀ j x, e (N j x) = N' j (e x)) :
    (⨅ j, LinearMap.ker (N j)).map (e : X →ₗ[R] Y) = ⨅ j, LinearMap.ker (N' j) := by
  ext y
  rw [Submodule.map_equiv_eq_comap_symm, Submodule.mem_comap]
  simp only [Submodule.mem_iInf, LinearMap.mem_ker, LinearEquiv.coe_coe]
  refine forall_congr' fun j => ?_
  constructor
  · intro hy
    have := congrArg e hy
    rwa [h, LinearEquiv.apply_symm_apply, map_zero] at this
  · intro hy
    apply e.injective
    rw [h, LinearEquiv.apply_symm_apply, hy, map_zero]

/- English proof (translation)
Simplify using the standard rewrite rules.
-/
theorem map_inf_equiv (e : X ≃ₗ[R] Y) (A C : Submodule R X) :
    (A ⊓ C).map (e : X →ₗ[R] Y) = A.map (e : X →ₗ[R] Y) ⊓ C.map (e : X →ₗ[R] Y) := by
  simp only [Submodule.map_equiv_eq_comap_symm, Submodule.comap_inf]

end Equiv

section Main

open Formalism.WeaklyAdmissibleFiltrations

variable {G : Type} [Group G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR) {LL LL' : Type} [Field LL] [Field LL'] [Algebra Qp LL] [Algebra Qp LL']
    [Algebra LL LL'] [IsScalarTower Qp LL LL'] {k : ℕ}

noncomputable abbrev rep {F : Type} [Field F] (M : G →* Matrix (Fin k) (Fin k) F) :
    Representation F G (Fin k → F) :=
  (Matrix.toLinAlgEquiv' : Matrix (Fin k) (Fin k) F ≃ₐ[F] _).toAlgHom.toRingHom.toMonoidHom.comp M

noncomputable abbrev EE (BB : Type) [AddCommGroup BB] [Module Qp BB] :
    LL' ⊗[LL] ((Fin k → LL) ⊗[Qp] BB) ≃ₗ[LL'] (Fin k → LL') ⊗[Qp] BB :=
  PI.CoefExt.coefEquiv

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Reduce the equality to equality of the corresponding arguments. A detailed English derivation is pending.
-/
theorem comm_act (A : Matrix (Fin k) (Fin k) LL) (β : BdR →ₗ[Qp] BdR) (x : LL' ⊗[LL] ((Fin k → LL) ⊗[Qp] BdR)) :
    EE (Qp := Qp) (LL' := LL') BdR ((PI.CoefExt.actT A β - LinearMap.id).baseChange LL' x)
      = (PI.CoefExt.actT (A.map (algebraMap LL LL')) β - LinearMap.id :
        (Fin k → LL') ⊗[Qp] BdR →ₗ[LL'] (Fin k → LL') ⊗[Qp] BdR) (EE BdR x) := by
  rw [LinearMap.baseChange_sub, LinearMap.baseChange_id, LinearMap.sub_apply, map_sub, LinearMap.sub_apply,
    LinearMap.id_apply, LinearMap.id_apply]
  congr 1
  exact PI.CoefExt.coefEquiv_comm A β x

/- English proof (translation)
Proceed by induction. Treat this case separately. Treat this case separately. Treat this case separately. Proceed by induction.

Treat this case separately. Treat this case separately. Treat this case separately. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules.

Establish an intermediate fact. Apply function extensionality and compare values at an arbitrary argument. Simplify using the standard rewrite rules. Expand and normalize the polynomial expressions, which then agree. Rewrite the conclusion using the stated equalities.
-/
theorem comm_mul (β : BdR →ₗ[Qp] BdR) (r : LL) (x : LL' ⊗[LL] ((Fin k → LL) ⊗[Qp] BdR)) :
    EE (Qp := Qp) (LL' := LL') BdR
        ((AlgebraTensorModule.map (LinearMap.id : (Fin k → LL) →ₗ[LL] _) β - r • LinearMap.id).baseChange LL' x)
      = (AlgebraTensorModule.map (LinearMap.id : (Fin k → LL') →ₗ[LL'] _) β
          - (algebraMap LL LL' r) • LinearMap.id :
        (Fin k → LL') ⊗[Qp] BdR →ₗ[LL'] (Fin k → LL') ⊗[Qp] BdR) (EE BdR x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul c y =>
    induction y using TensorProduct.induction_on with
    | zero => simp
    | add y z hy hz => simp only [tmul_add, map_add, hy, hz]
    | tmul v b =>
      rw [LinearMap.baseChange_tmul]
      simp only [LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply, AlgebraTensorModule.map_tmul,
        tmul_sub, map_sub, PI.CoefExt.coefEquiv_tmul, TensorProduct.smul_tmul']
      have hv : (fun i => (r • v) i • c) = (algebraMap LL LL' r • fun i => v i • c) := by
        funext i
        simp only [Pi.smul_apply, smul_eq_mul, Algebra.smul_def, map_mul]
        ring
      rw [hv]

/- English proof (translation)
Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. A detailed English derivation is pending.
-/
theorem dR_ext (M : G →* Matrix (Fin k) (Fin k) LL) :
    (extS LL' (DdR PD (rep M))).map ((EE (Qp := Qp) (LL := LL) (LL' := LL') (k := k) BdR :
        _ ≃ₗ[LL'] _) : _ →ₗ[LL'] _)
      = DdR PD (rep (((IsScalarTower.toAlgHom Qp LL LL').mapMatrix :
          Matrix (Fin k) (Fin k) LL →ₐ[Qp] Matrix (Fin k) (Fin k) LL').toRingHom.toMonoidHom.comp M)) := by
  unfold DdR
  rw [extS_iInf]
  simp only [extS_ker]
  exact map_iInf_ker _ _ _ (fun g x => comm_act (M g) _ x)

/- English proof (translation)
Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Reduce the equality to equality of the corresponding arguments. A detailed English derivation is pending.
-/
theorem dRE_ext (M : G →* Matrix (Fin k) (Fin k) LL) (τ : K →ₐ[Qp] LL) :
    (extS LL' (DdRE PD (rep M) τ)).map ((EE (Qp := Qp) (LL := LL) (LL' := LL') (k := k) BdR :
        _ ≃ₗ[LL'] _) : _ →ₗ[LL'] _)
      = DdRE PD (rep (((IsScalarTower.toAlgHom Qp LL LL').mapMatrix :
          Matrix (Fin k) (Fin k) LL →ₐ[Qp] Matrix (Fin k) (Fin k) LL').toRingHom.toMonoidHom.comp M))
          ((IsScalarTower.toAlgHom Qp LL LL').comp τ) := by
  unfold DdRE
  rw [extS_inf, map_inf_equiv, dR_ext, extS_iInf]
  simp only [extS_ker]
  congr 1
  exact map_iInf_ker _ _ _ (fun c x => comm_mul _ (τ c) x)

/- English proof (translation)
Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Reduce the claim to the hypotheses of an applicable result. Fix the arbitrary inputs or assume the hypotheses.

Proceed by induction. Treat this case separately. Treat this case separately. Rewrite the conclusion using the stated equalities. Treat this case separately.

Proceed by induction. Treat this case separately. Treat this case separately. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities.

Treat this case separately. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities.
-/
theorem fil_ext (a : ℤ) :
    (extS LL' (FilV PD (LL := LL) (V := Fin k → LL) a)).map ((EE (Qp := Qp) (LL := LL) (LL' := LL') (k := k) BdR :
        _ ≃ₗ[LL'] _) : _ →ₗ[LL'] _)
      = FilV PD (LL := LL') (V := Fin k → LL') a := by
  unfold FilV
  rw [extS_range, ← LinearMap.range_comp]
  have hc : ((EE (Qp := Qp) (LL := LL) (LL' := LL') (k := k) BdR : _ ≃ₗ[LL'] _) : _ →ₗ[LL'] _) ∘ₗ
        (AlgebraTensorModule.map (LinearMap.id : (Fin k → LL) →ₗ[LL] _)
          ((PD.Fil a).restrictScalars Qp).subtype).baseChange LL'
      = AlgebraTensorModule.map (LinearMap.id : (Fin k → LL') →ₗ[LL'] _) ((PD.Fil a).restrictScalars Qp).subtype ∘ₗ
          ((EE (Qp := Qp) (LL := LL) (LL' := LL') (k := k) ((PD.Fil a).restrictScalars Qp) :
            _ ≃ₗ[LL'] _) : _ →ₗ[LL'] _) := by
    apply LinearMap.ext
    intro x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy => simp only [LinearMap.comp_apply, map_add] at hx hy ⊢; rw [hx, hy]
    | tmul c y =>
      induction y using TensorProduct.induction_on with
      | zero => simp
      | add y z hy hz =>
        simp only [LinearMap.comp_apply, tmul_add, map_add] at hy hz ⊢; rw [hy, hz]
      | tmul v b =>
        simp [LinearMap.baseChange_tmul, AlgebraTensorModule.map_tmul, PI.CoefExt.coefEquiv_tmul]
  rw [hc, LinearMap.range_comp_of_range_eq_top _ (LinearEquiv.range _)]

/- English proof (translation)
Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities.
-/
theorem fildR_ext (M : G →* Matrix (Fin k) (Fin k) LL) (τ : K →ₐ[Qp] LL) (a : ℤ) :
    (extS LL' (FildR PD (rep M) τ a)).map ((EE (Qp := Qp) (LL := LL) (LL' := LL') (k := k) BdR :
        _ ≃ₗ[LL'] _) : _ →ₗ[LL'] _)
      = FildR PD (rep (((IsScalarTower.toAlgHom Qp LL LL').mapMatrix :
          Matrix (Fin k) (Fin k) LL →ₐ[Qp] Matrix (Fin k) (Fin k) LL').toRingHom.toMonoidHom.comp M))
          ((IsScalarTower.toAlgHom Qp LL LL').comp τ) a := by
  unfold FildR
  rw [extS_inf, map_inf_equiv, dRE_ext, fil_ext]

/- English proof (translation)
Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities. Prove the components needed by the constructor for the conclusion. Fix the arbitrary inputs or assume the hypotheses. Fix the arbitrary inputs or assume the hypotheses.

A detailed English derivation is pending.
-/
theorem jump_iff (M : G →* Matrix (Fin k) (Fin k) LL) (τ : K →ₐ[Qp] LL) (a : ℤ) :
    IsJumpV PD (rep M) τ a ↔
      IsJumpV PD (rep (((IsScalarTower.toAlgHom Qp LL LL').mapMatrix :
          Matrix (Fin k) (Fin k) LL →ₐ[Qp] Matrix (Fin k) (Fin k) LL').toRingHom.toMonoidHom.comp M))
          ((IsScalarTower.toAlgHom Qp LL LL').comp τ) a := by
  unfold IsJumpV
  rw [← fildR_ext, ← fildR_ext]
  constructor
  · intro h h'
    exact h (extS_injective (Submodule.map_injective_of_injective (LinearEquiv.injective _) h'))
  · intro h h'
    exact h (by rw [h'])

end Main

end CJ

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Introduce a local definition for the expression. Establish an intermediate fact. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.

A detailed English derivation is pending.
-/
theorem Formalism.MainNotions.N.GlobalTheory.coefficient_jump_general : Formalism.MainNotions.N.GlobalTheory.CoefJumpGen := by
  intro G _ Qp K₀ K _ _ _ _ _ _ _ B BdR _ _ _ _ _ _ _ _ _ _ _ PD LL LL' _ _ _ _ f k M τ a
  let _ : Algebra LL LL' := f.toRingHom.toAlgebra
  have _ : IsScalarTower Qp LL LL' := IsScalarTower.of_algebraMap_eq (fun x => (f.commutes x).symm)
  have hf : IsScalarTower.toAlgHom Qp LL LL' = f := AlgHom.ext fun _ => rfl
  rw [← hf]
  exact CJ.jump_iff PD M τ a

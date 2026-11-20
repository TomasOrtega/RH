import Mathlib
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsUniqueInvariantVectorFieldOfTangentStatement
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.InvariantVectorFieldsAlongGroupHomStatement
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsInvDer
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.LeISupInfPreimage
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaUnifAV
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct ContDiff
open GlobalTheory.KS
noncomputable section
namespace GlobalTheory.KS.SquareField
variable {K : Type} [Field K]

def zeroPt (K : Type) [Field K] : 𝟙_ (Over (Sp K)) ⟶ epsR K :=
  Over.homMk (spMap (TrivSqZeroExt.fstHom K K K).toRingHom) (by
    change Spec.map _ ≫ Spec.map _ = 𝟙 _
    rw [← Spec.map_comp, ← Spec.map_id]
    congr 1)

/- English proof (translation)
Unfold `IsTangent`. Prove the components needed by the constructor for the conclusion. Introduce `h ext1`. Simplify `h` using `[zeroPt]`. Introduce `h`.

Simplify `congrArg (fun u => u.left) h` using `[zeroPt]`.
-/
theorem isTangent_iff {G : Over (Sp K)} [GrpObj G] (v : epsR K ⟶ G) :
    IsTangent v ↔ zeroPt K ≫ v = η[G] := by
  unfold IsTangent
  constructor
  · intro h
    ext1
    simpa [zeroPt] using h
  · intro h
    simpa [zeroPt] using congrArg (fun u => u.left) h

/- English proof (translation)
Rewrite using `[isTangent_iff, Hom.one_def, ← Category.assoc, toUnit_unique (zeroPt K ≫ toUnit _) (𝟙 _), Category.id_comp]`.
-/
theorem isTangent_one {G : Over (Sp K)} [GrpObj G] : IsTangent (1 : epsR K ⟶ G) := by
  rw [isTangent_iff, Hom.one_def, ← Category.assoc, toUnit_unique (zeroPt K ≫ toUnit _) (𝟙 _),
    Category.id_comp]

/- English proof (translation)
Rewrite `hv`, `hw`, the goal using `[isTangent_iff]`. Apply `CartesianMonoidalCategory.hom_ext` to reduce the goal to its premises. Simplify using `[hv]`. Simplify using `[hw]`.
-/
theorem isTangent_lift {G H : Over (Sp K)} [GrpObj G] [GrpObj H] {v : epsR K ⟶ G} {w : epsR K ⟶ H}
    (hv : IsTangent v) (hw : IsTangent w) : IsTangent (lift v w) := by
  rw [isTangent_iff] at hv hw ⊢
  apply CartesianMonoidalCategory.hom_ext
  · simp [hv]
  · simp [hw]

/- English proof (translation)
Use `⟨fun _ => v, fun _ => ?_, by simp⟩` and prove the remaining obligations. Simplify using `only [epsScaleR, one_smul, TrivSqZeroExt.map_id]`. Simplify using `[spMap]`.
-/
theorem isLieComb_one {G : Over (Sp K)} [GrpObj G] (v : epsR K ⟶ G) :
    IsLieComb (fun _ : Fin 1 => (1 : K)) (fun _ => v) v := by
  refine ⟨fun _ => v, fun _ => ?_, by simp⟩
  simp only [epsScaleR, one_smul, TrivSqZeroExt.map_id]
  simp [spMap]

/- English proof (translation)
Conclude with `⟨fun i => i.elim0, fun i => i.elim0, by simp⟩`.
-/
theorem isLieComb_zero {G : Over (Sp K)} [GrpObj G] :
    IsLieComb (fun _ : Fin 0 => (1 : K)) (fun _ => (1 : epsR K ⟶ G)) 1 := by
  exact ⟨fun i => i.elim0, fun i => i.elim0, by simp⟩

/- English proof (translation)
Unfold `pbT`. Rewrite using `[dif_pos le_rfl, Scheme.Hom.app_eq_appLE]`.
-/
theorem app_eq_pbT {Z Y : Scheme.{0}} (f : Z ⟶ Y) (W : Y.Opens) (h : Γ(Y, W)) :
    (f.app W).hom h = pbT f h (f ⁻¹ᵁ W) := by
  unfold pbT
  rw [dif_pos le_rfl, Scheme.Hom.app_eq_appLE]

/- English proof (translation)
Simplify using `[constFn]`.
-/
theorem constFn_one {Y : Scheme.{0}} (q : Y ⟶ Sp K) (O : Y.Opens) : constFn q O 1 = 1 := by
  simp [constFn]

/- English proof (translation)
Unfold `pbT rsT`. Rewrite using `[dif_pos hO, dif_pos hO, dif_pos (le_refl _), resG, ← CommRingCat.comp_apply, Scheme.Hom.appLE_map]`.
-/
private theorem pbT_eq_rsT_pbT_preimage {Z Y : Scheme.{0}} (f : Z ⟶ Y) {O₀ : Y.Opens} (s : Γ(Y, O₀))
    (O : Z.Opens) (hO : O ≤ f ⁻¹ᵁ O₀) : pbT f s O = rsT (pbT f s (f ⁻¹ᵁ O₀)) O := by
  unfold pbT rsT
  rw [dif_pos hO, dif_pos hO, dif_pos (le_refl _), resG, ← CommRingCat.comp_apply, Scheme.Hom.appLE_map]

/- English proof (translation)
Unfold `rsT`. Apply the tactic sequence `split <;> simp`.
-/
private theorem rsT_zero_moduli {Y : Scheme.{0}} {O₀ : Y.Opens} (O : Y.Opens) :
    rsT (0 : Γ(Y, O₀)) O = 0 := by
  unfold rsT
  split <;> simp

section
variable {A₁ A₀ : Over (Sp K)} [GrpObj A₁] [GrpObj A₀] (f : A₁ ⟶ A₀) [IsMonHom f]
  {w : epsR K ⟶ A₁} {dw : ∀ O : A₁.left.Opens, Γ(A₁.left, O) → Γ(A₁.left, O)}

/- English proof (translation)
Take `⟨-, hprop⟩` from `GlobalTheory.T.exists_unique_invariantVectorField_of_tangent K A₁ w hw`. Take `⟨-, -, hres, -, -⟩` from `hprop dw hdw`. Establish `hkey` using `GlobalTheory.T.invariantVectorFields_along_groupHom K A₁ A₀ f 1 (fun _ => v) (fun _ => dd) w dw (fun _ => 1) inferInstance (fun _ => hv) hw (fun _ => hd) hdw (by rw [e]; exact isLieComb_one v) W h`. Simplify using `only [Fin.sum_univ_one, constFn_one] at hkey`. Rewrite using `[pbT_eq_rsT_pbT_preimage f.left h O hO, hres _ _ _ hO, ← app_eq_pbT, hkey, _root_.one_mul, app_eq_pbT, ← pbT_eq_rsT_pbT_preimage f.left (dd W h) O hO]`.
-/
theorem field_pb {v : epsR K ⟶ A₀} {dd : ∀ O : A₀.left.Opens, Γ(A₀.left, O) → Γ(A₀.left, O)}
    (hv : IsTangent v) (hd : IsInvDer v dd) (hw : IsTangent w) (hdw : IsInvDer w dw) (e : w ≫ f = v)
    (W : A₀.left.Opens) (h : Γ(A₀.left, W)) (O : A₁.left.Opens) (hO : O ≤ f.left ⁻¹ᵁ W) :
    dw O (pbT f.left h O) = pbT f.left (dd W h) O := by
  obtain ⟨-, hprop⟩ := GlobalTheory.T.exists_unique_invariantVectorField_of_tangent K A₁ w hw
  obtain ⟨-, -, hres, -, -⟩ := hprop dw hdw
  have hkey := GlobalTheory.T.invariantVectorFields_along_groupHom K A₁ A₀ f 1 (fun _ => v) (fun _ => dd) w dw (fun _ => 1) inferInstance
    (fun _ => hv) hw (fun _ => hd) hdw (by rw [e]; exact isLieComb_one v) W h
  simp only [Fin.sum_univ_one, constFn_one] at hkey
  rw [pbT_eq_rsT_pbT_preimage f.left h O hO, hres _ _ _ hO, ← app_eq_pbT, hkey, _root_.one_mul, app_eq_pbT,
    ← pbT_eq_rsT_pbT_preimage f.left (dd W h) O hO]

/- English proof (translation)
Take `⟨-, hprop⟩` from `GlobalTheory.T.exists_unique_invariantVectorField_of_tangent K A₁ w hw`. Take `⟨-, -, hres, -, -⟩` from `hprop dw hdw`. Establish `hkey` using `GlobalTheory.T.invariantVectorFields_along_groupHom K A₁ A₀ f 0 (fun _ => 1) (fun _ _ x => x) w dw (fun _ => 1) inferInstance (fun i => i.elim0) hw (fun i => i.elim0) hdw (by rw [e]; exact isLieComb_zero) W h`. Simplify using `only [Fin.sum_univ_zero] at hkey`. Rewrite using `[pbT_eq_rsT_pbT_preimage f.left h O hO, hres _ _ _ hO, ← app_eq_pbT, hkey, rsT_zero_moduli]`.
-/
theorem field_pb_zero (hw : IsTangent w) (hdw : IsInvDer w dw) (e : w ≫ f = 1)
    (W : A₀.left.Opens) (h : Γ(A₀.left, W)) (O : A₁.left.Opens) (hO : O ≤ f.left ⁻¹ᵁ W) :
    dw O (pbT f.left h O) = 0 := by
  obtain ⟨-, hprop⟩ := GlobalTheory.T.exists_unique_invariantVectorField_of_tangent K A₁ w hw
  obtain ⟨-, -, hres, -, -⟩ := hprop dw hdw
  have hkey := GlobalTheory.T.invariantVectorFields_along_groupHom K A₁ A₀ f 0 (fun _ => 1) (fun _ _ x => x) w dw (fun _ => 1) inferInstance
    (fun i => i.elim0) hw (fun i => i.elim0) hdw (by rw [e]; exact isLieComb_zero) W h
  simp only [Fin.sum_univ_zero] at hkey
  rw [pbT_eq_rsT_pbT_preimage f.left h O hO, hres _ _ _ hO, ← app_eq_pbT, hkey, rsT_zero_moduli]
end

/- English proof (translation)
Introduce `K _ A₀ _ _ v dd hv hd n n' hnn'`. Choose the witnesses or unpack the hypotheses as in `⟨w, hw, hwn, hwn', hwm⟩ : ∃ w : epsR K ⟶ A₀ ⊗ A₀, IsTangent w ∧ w ≫ n = v ∧ w ≫ n' = 1 ∧ w ≫ (fst A₀ A₀ * snd A₀ A₀) = v := by`. Break down `hnn' with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩` into its components or cases. Conclude with `⟨lift v 1, isTangent_lift hv isTangent_one, lift_fst _ _, lift_snd _ _, by`. Rewrite using `[MonObj.comp_mul, lift_fst, lift_snd, _root_.mul_one]⟩`.

Conclude with `⟨lift 1 v, isTangent_lift isTangent_one hv, lift_snd _ _, lift_fst _ _, by`. Rewrite using `[MonObj.comp_mul, lift_fst, lift_snd, _root_.one_mul]⟩`. Apply the tactic sequence `have hn : IsMonHom n := by rcases hnn' with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> infer_instance`. Apply the tactic sequence `have hn' : IsMonHom n' := by rcases hnn' with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> infer_instance`. Establish `hm : IsMonHom (fst A₀ A₀ * snd A₀ A₀)`.

Rewrite using `[← MonObj.mul_eq_mul]`. Use `infer_instance`. Take `⟨-, hprop⟩` from `GlobalTheory.T.exists_unique_invariantVectorField_of_tangent K (A₀ ⊗ A₀) w hw`. Take `⟨dw, hdw⟩` from `(GlobalTheory.T.exists_unique_invariantVectorField_of_tangent K (A₀ ⊗ A₀) w hw).1`. Take `⟨hadd, hmul, hres, hconst, -⟩` from `hprop dw hdw`.

Use `⟨dw, hadd, hmul, hres, hconst, ?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `W h O hO`. Conclude with `field_pb _ hv hd hw hdw hwm W h O hO`. Introduce `W h O hO`. Conclude with `field_pb _ hv hd hw hdw hwn W h O hO`.

Introduce `W h O hO`. Conclude with `field_pb_zero _ hw hdw hwn' W h O hO`.
-/
theorem main : ∀ (K : Type) [Field K] (A₀ : Over (Sp K)) [GrpObj A₀] [IsCommMonObj A₀] (v : epsR K ⟶ A₀) (dd : ∀ O : A₀.left.Opens, Γ(A₀.left, O) → Γ(A₀.left, O)), IsTangent v → IsInvDer v dd → ∀ (n n' : A₀ ⊗ A₀ ⟶ A₀), ((n = fst A₀ A₀ ∧ n' = snd A₀ A₀) ∨ (n = snd A₀ A₀ ∧ n' = fst A₀ A₀)) → ∃ dw : ∀ O : (A₀ ⊗ A₀).left.Opens, Γ((A₀ ⊗ A₀).left, O) → Γ((A₀ ⊗ A₀).left, O), (∀ W f f', dw W (f + f') = dw W f + dw W f') ∧ (∀ W f f', dw W (f * f') = f * dw W f' + f' * dw W f) ∧ (∀ W W' (f : Γ((A₀ ⊗ A₀).left, W)), W' ≤ W → dw W' (rsT f W') = rsT (dw W f) W') ∧ (∀ W a, dw W (constFn (A₀ ⊗ A₀).hom W a) = 0) ∧ (∀ (W : A₀.left.Opens) (h : Γ(A₀.left, W)) O, O ≤ (fst A₀ A₀ * snd A₀ A₀).left ⁻¹ᵁ W → dw O (pbT (fst A₀ A₀ * snd A₀ A₀).left h O) = pbT (fst A₀ A₀ * snd A₀ A₀).left (dd W h) O) ∧ (∀ (W : A₀.left.Opens) (h : Γ(A₀.left, W)) O, O ≤ n.left ⁻¹ᵁ W → dw O (pbT n.left h O) = pbT n.left (dd W h) O) ∧ (∀ (W : A₀.left.Opens) (h : Γ(A₀.left, W)) O, O ≤ n'.left ⁻¹ᵁ W → dw O (pbT n'.left h O) = 0) := by
  intro K _ A₀ _ _ v dd hv hd n n' hnn'
  obtain ⟨w, hw, hwn, hwn', hwm⟩ : ∃ w : epsR K ⟶ A₀ ⊗ A₀, IsTangent w ∧ w ≫ n = v ∧ w ≫ n' = 1 ∧
      w ≫ (fst A₀ A₀ * snd A₀ A₀) = v := by
    rcases hnn' with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact ⟨lift v 1, isTangent_lift hv isTangent_one, lift_fst _ _, lift_snd _ _, by
        rw [MonObj.comp_mul, lift_fst, lift_snd, _root_.mul_one]⟩
    · exact ⟨lift 1 v, isTangent_lift isTangent_one hv, lift_snd _ _, lift_fst _ _, by
        rw [MonObj.comp_mul, lift_fst, lift_snd, _root_.one_mul]⟩
  have hn : IsMonHom n := by rcases hnn' with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> infer_instance
  have hn' : IsMonHom n' := by rcases hnn' with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> infer_instance
  have hm : IsMonHom (fst A₀ A₀ * snd A₀ A₀) := by
    rw [← MonObj.mul_eq_mul]
    infer_instance
  obtain ⟨-, hprop⟩ := GlobalTheory.T.exists_unique_invariantVectorField_of_tangent K (A₀ ⊗ A₀) w hw
  obtain ⟨dw, hdw⟩ := (GlobalTheory.T.exists_unique_invariantVectorField_of_tangent K (A₀ ⊗ A₀) w hw).1
  obtain ⟨hadd, hmul, hres, hconst, -⟩ := hprop dw hdw
  refine ⟨dw, hadd, hmul, hres, hconst, ?_, ?_, ?_⟩
  · intro W h O hO
    exact field_pb _ hv hd hw hdw hwm W h O hO
  · intro W h O hO
    exact field_pb _ hv hd hw hdw hwn W h O hO
  · intro W h O hO
    exact field_pb_zero _ hw hdw hwn' W h O hO

end GlobalTheory.KS.SquareField
end

import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.L2UnitaryRepresentationData
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsFiniteDimensionalKill
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.S Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum
open Formalism.IndefR.Mult (DSModel dualPar parA parB)
open Formalism.MainNotions.SchurIrreducible (AdmGK ARi ARiiiUp ARiiiDown ARiiiLine DiscreteSeriesBlattner admQ5)
open GlobalTheory.IndefiniteRowSideFullHecke.ThetaSourceAction hiding Mat
open GlobalTheory.IndefiniteRowSideFullHecke.BarMatrix (SignCompat plainMat barMat)
open GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting (fockIp)
open GlobalTheory.Chain (signed)
open GlobalTheory.Chain.RealIt (LPol locS locT IsPolyIso)
open MeasureTheory Matrix
open scoped TensorProduct InnerProductSpace ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.ArchRec

namespace GlobalTheory.ArchRec.PairTensor

open GlobalTheory.InvPairingTensor (exists_real_parts inner_act_skew exists_frame)

variable {p q : ℕ} {T : GrpData p q} (R : DSRep T)

/- English proof (translation)
Set `m : R.HK.V → R.HK.V →ₗ[ℂ] ℂ` to `fun v => innerₛₗ ℂ (R.ι v) ∘ₗ R.ι`. Establish `sepm : ∀ b, (∀ v, m v b = 0) → b = 0` using `fun b h => by`. Apply `R.ι_inj` to reduce the goal to its premises. Rewrite using `[map_zero]`. Conclude with `inner_self_eq_zero.1 (h b)`.

Establish `key : ∀ v (z : R.HK.V ⊗[ℂ] U), GlobalTheory.PairingTensor.contrR (m v) (TensorProduct.comm ℂ _ _ z) = ctr R U v z`. Introduce `v z`. Proceed by induction on `z using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `tmul a b => rw [TensorProduct.comm_tmul, GlobalTheory.PairingTensor.contrR_tmul, ctr_tmul]`.

Both sides reduce to the same expression. Consider the case `add x y hx hy => simp only [map_add, hx, hy]`. Apply `(TensorProduct.comm ℂ _ _).injective` to reduce the goal to its premises. Rewrite using `[map_zero]`. Conclude with `GlobalTheory.PairingTensor.eq_zero_of_contrR m sepm _ fun v => by rw [key, hy]`.
-/
theorem eq_zero_of_ctr (U : Type) [AddCommGroup U] [Module ℂ U] (y : R.HK.V ⊗[ℂ] U)
    (hy : ∀ v, ctr R U v y = 0) : y = 0 := by
  let m : R.HK.V → R.HK.V →ₗ[ℂ] ℂ := fun v => innerₛₗ ℂ (R.ι v) ∘ₗ R.ι
  have sepm : ∀ b, (∀ v, m v b = 0) → b = 0 := fun b h => by
    apply R.ι_inj
    rw [map_zero]
    exact inner_self_eq_zero.1 (h b)
  have key : ∀ v (z : R.HK.V ⊗[ℂ] U),
      GlobalTheory.PairingTensor.contrR (m v) (TensorProduct.comm ℂ _ _ z) = ctr R U v z := by
    intro v z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul a b => rw [TensorProduct.comm_tmul, GlobalTheory.PairingTensor.contrR_tmul, ctr_tmul]; rfl
    | add x y hx hy => simp only [map_add, hx, hy]
  apply (TensorProduct.comm ℂ _ _).injective
  rw [map_zero]
  exact GlobalTheory.PairingTensor.eq_zero_of_contrR m sepm _ fun v => by rw [key, hy]

/- English proof (translation)
Rewrite using `[← sub_eq_zero]`. Conclude with `eq_zero_of_ctr R U _ fun v => by rw [map_sub, h, sub_self]`.
-/
theorem ext_ctr (U : Type) [AddCommGroup U] [Module ℂ U] (z w : R.HK.V ⊗[ℂ] U)
    (h : ∀ v, ctr R U v z = ctr R U v w) : z = w := by
  rw [← sub_eq_zero]
  exact eq_zero_of_ctr R U _ fun v => by rw [map_sub, h, sub_self]

/- English proof (translation)
Proceed by induction on `z using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `tmul a b => simp only [ctr_tmul, map_add, inner_add_left, add_smul]`. Consider the case `add x y hx hy => simp only [map_add, hx, hy]`. Normalize the expressions using the abelian group laws.
-/
theorem ctr_add (U : Type) [AddCommGroup U] [Module ℂ U] (v w : R.HK.V) (z : R.HK.V ⊗[ℂ] U) :
    ctr R U (v + w) z = ctr R U v z + ctr R U w z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul a b => simp only [ctr_tmul, map_add, inner_add_left, add_smul]
  | add x y hx hy => simp only [map_add, hx, hy]; abel

/- English proof (translation)
Proceed by induction on `z using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `tmul a b => simp only [ctr_tmul, map_smul, inner_smul_left, mul_smul]`. Consider the case `add x y hx hy => simp only [map_add, hx, hy, smul_add]`.
-/
theorem ctr_smul (U : Type) [AddCommGroup U] [Module ℂ U] (c : ℂ) (v : R.HK.V)
    (z : R.HK.V ⊗[ℂ] U) : ctr R U (c • v) z = (starRingEnd ℂ) c • ctr R U v z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul a b => simp only [ctr_tmul, map_smul, inner_smul_left, mul_smul]
  | add x y hx hy => simp only [map_add, hx, hy, smul_add]

/- English proof (translation)
Proceed by induction on `z using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `tmul a b`. Rewrite using `[TensorProduct.map_tmul, ctr_tmul, ctr_tmul, eq_neg_of_add_eq_zero_left (inner_act_skew R hX v a), neg_smul, LinearMap.id_apply]`. Consider the case `add x y hx hy => simp only [map_add, hx, hy, neg_add]`.
-/
theorem ctr_act (U : Type) [AddCommGroup U] [Module ℂ U] {X : Mat p q} (hX : X ∈ upq p q)
    (v : R.HK.V) (z : R.HK.V ⊗[ℂ] U) :
    ctr R U v (TensorProduct.map (R.HK.act X) LinearMap.id z) = -ctr R U (R.HK.act X v) z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul a b =>
    rw [TensorProduct.map_tmul, ctr_tmul, ctr_tmul,
      eq_neg_of_add_eq_zero_left (inner_act_skew R hX v a), neg_smul, LinearMap.id_apply]
  | add x y hx hy => simp only [map_add, hx, hy, neg_add]

variable {W U : Type} [AddCommGroup W] [Module ℂ W] [AddCommGroup U] [Module ℂ U]
  (a : Mat p q →ₗ[ℂ] Module.End ℂ W)

/- English proof (translation)
Take `⟨W₀, hW, hP, hst⟩` from `ha.2.1 P`. Take `⟨E, hE, hE'⟩` from `GlobalTheory.T.exists_finiteDimensional_forall_map_mem' p q R.HK hA _ a (fun Y Z _ _ => ha.1 Y Z) W₀ hW hst (fun v _ => ha.2.2 v)`. Use `⟨E, hE, fun y hy => ?_⟩` and prove the remaining obligations. Rewrite using `[← Module.forall_dual_apply_eq_zero_iff ℂ]`. Introduce `l`.

Take `⟨F, hF, hyF, hFst⟩` from `R.HK.kfin y`. Take `⟨n, e, heF, he⟩` from `exists_frame R.ι R.ι_inj F`. Set `φ : W →ₗ[ℂ] R.HK.V` to `∑ j, (l ∘ₗ B.flip (e j)).smulRight (e j)`. Establish `hφ : ∀ w, φ w = ∑ j, l (B w (e j)) • e j` using `fun w => by`. Simplify using `[φ, LinearMap.sum_apply]`.

Establish `hφF : ∀ w, φ w ∈ F` using `fun w => by`. Rewrite using `[hφ]`. Conclude with `F.sum_mem fun j _ => F.smul_mem _ (heF j)`. Establish `hR : ∀ w, ∀ x ∈ F, inner ℂ (R.ι x) (R.ι (φ w)) = l (B w x)` using `fun w x hx => by conv_rhs => rw [← he x hx]`. Rewrite using `[hφ]`.

Simplify using `only [map_sum, map_smul, inner_sum, inner_smul_right, LinearMap.map_smulₛₗ, inner_conj_symm, smul_eq_mul, mul_comm]`. Establish `hreal : ∀ X ∈ upq p q, IsKC X → ∀ w, φ (a X w) = R.HK.act X (φ w)`. Introduce `X hX hK w`. Establish `hd : φ (a X w) - R.HK.act X (φ w) ∈ F` using `F.sub_mem (hφF _) (hFst X hK _ (hφF w))`. Establish `h0 : ∀ x ∈ F, inner ℂ (R.ι x) (R.ι (φ (a X w) - R.HK.act X (φ w))) = 0`.

Introduce `x hx`. Establish `h1` using `inner_act_skew R hX x (φ w)`. Establish `h2` using `congrArg l (hB X hX w x)`. Rewrite `h2` using `[map_add, map_zero]`. Rewrite `h1` using `[hR w _ (hFst X hK x hx)]`.

Rewrite using `[map_sub, inner_sub_right, hR _ x hx]`. Take the linear combination `h2 - h1`. Rewrite using `[← sub_eq_zero]`. Apply `R.ι_inj` to reduce the goal to its premises. Rewrite using `[map_zero]`.

Conclude with `inner_self_eq_zero.1 (h0 _ hd)`. Establish `heq : ∀ Z, IsKC Z → ∀ w, φ (a Z w) = R.HK.act Z (φ w)`. Introduce `Z hZ w`. Take `⟨X, Y, hX, hY, hK, rfl⟩` from `exists_real_parts Z`. Simplify using `only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, hreal X hX (hK hZ).1, hreal Y hY (hK hZ).2]`.

Rewrite using `[← hR P y hyF]`. Conclude with `hy _ (hE' φ heq P hP)`.
-/
theorem exists_finiteDimensional_kill (ha : IsGK a) (hA : AdmGK R.HK)
    (B : W →ₗ[ℂ] R.HK.V →ₛₗ[starRingEnd ℂ] U) (hB : PInv a R B) (P : W) :
    ∃ E : Submodule ℂ R.HK.V, FiniteDimensional ℂ E ∧
      ∀ y, (∀ x ∈ E, inner ℂ (R.ι y) (R.ι x) = 0) → B P y = 0 := by
  obtain ⟨W₀, hW, hP, hst⟩ := ha.2.1 P
  obtain ⟨E, hE, hE'⟩ := GlobalTheory.T.exists_finiteDimensional_forall_map_mem' p q R.HK hA _ a
    (fun Y Z _ _ => ha.1 Y Z) W₀ hW hst (fun v _ => ha.2.2 v)
  refine ⟨E, hE, fun y hy => ?_⟩
  rw [← Module.forall_dual_apply_eq_zero_iff ℂ]
  intro l
  obtain ⟨F, hF, hyF, hFst⟩ := R.HK.kfin y
  obtain ⟨n, e, heF, he⟩ := exists_frame R.ι R.ι_inj F
  let φ : W →ₗ[ℂ] R.HK.V := ∑ j, (l ∘ₗ B.flip (e j)).smulRight (e j)
  have hφ : ∀ w, φ w = ∑ j, l (B w (e j)) • e j := fun w => by
    simp [φ, LinearMap.sum_apply]
  have hφF : ∀ w, φ w ∈ F := fun w => by
    rw [hφ]; exact F.sum_mem fun j _ => F.smul_mem _ (heF j)
  have hR : ∀ w, ∀ x ∈ F, inner ℂ (R.ι x) (R.ι (φ w)) = l (B w x) := fun w x hx => by
    conv_rhs => rw [← he x hx]
    rw [hφ]
    simp only [map_sum, map_smul, inner_sum, inner_smul_right, LinearMap.map_smulₛₗ,
      inner_conj_symm, smul_eq_mul, mul_comm]
  have hreal : ∀ X ∈ upq p q, IsKC X → ∀ w, φ (a X w) = R.HK.act X (φ w) := by
    intro X hX hK w
    have hd : φ (a X w) - R.HK.act X (φ w) ∈ F :=
      F.sub_mem (hφF _) (hFst X hK _ (hφF w))
    have h0 : ∀ x ∈ F, inner ℂ (R.ι x) (R.ι (φ (a X w) - R.HK.act X (φ w))) = 0 := by
      intro x hx
      have h1 := inner_act_skew R hX x (φ w)
      have h2 := congrArg l (hB X hX w x)
      rw [map_add, map_zero] at h2
      rw [hR w _ (hFst X hK x hx)] at h1
      rw [map_sub, inner_sub_right, hR _ x hx]
      linear_combination h2 - h1
    rw [← sub_eq_zero]
    apply R.ι_inj
    rw [map_zero]
    exact inner_self_eq_zero.1 (h0 _ hd)
  have heq : ∀ Z, IsKC Z → ∀ w, φ (a Z w) = R.HK.act Z (φ w) := by
    intro Z hZ w
    obtain ⟨X, Y, hX, hY, hK, rfl⟩ := exists_real_parts Z
    simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply,
      hreal X hX (hK hZ).1, hreal Y hY (hK hZ).2]
  rw [← hR P y hyF]
  exact hy _ (hE' φ heq P hP)

/- English proof (translation)
Set `B : W →ₗ[ℂ] R.HK.V →ₛₗ[starRingEnd ℂ] U` to `{ toFun := fun P => { toFun := fun v => ctr R U v (f P) map_add' := fun v w => ctr_add R U v w _ map_smul' := fun c v => ctr_smul R U c v _ } map_add' := fun P Q => by ext v; simp map_smul' := fun c P => by ext v; simp }`. Use `⟨B, fun Z hZ P v => ?_, fun _ _ => rfl⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `ctr R U v (f (a Z P)) + ctr R U (R.HK.act Z v) (f P) = 0`. Use `LinearMap.congr_fun (hf Z) P` as an intermediate fact. Rewrite `this` using `[LinearMap.comp_apply, LinearMap.comp_apply]`.

Rewrite using `[this, ctr_act R U hZ, neg_add_cancel]`.
-/
theorem exists_pairing (f : W →ₗ[ℂ] R.HK.V ⊗[ℂ] U)
    (hf : ∀ Z, f ∘ₗ a Z = TensorProduct.map (R.HK.act Z) LinearMap.id ∘ₗ f) :
    ∃ B : W →ₗ[ℂ] R.HK.V →ₛₗ[starRingEnd ℂ] U, PInv a R B ∧ ∀ P v, B P v = ctr R U v (f P) := by
  let B : W →ₗ[ℂ] R.HK.V →ₛₗ[starRingEnd ℂ] U :=
    { toFun := fun P =>
        { toFun := fun v => ctr R U v (f P)
          map_add' := fun v w => ctr_add R U v w _
          map_smul' := fun c v => ctr_smul R U c v _ }
      map_add' := fun P Q => by ext v; simp
      map_smul' := fun c P => by ext v; simp }
  refine ⟨B, fun Z hZ P v => ?_, fun _ _ => rfl⟩
  change ctr R U v (f (a Z P)) + ctr R U (R.HK.act Z v) (f P) = 0
  have := LinearMap.congr_fun (hf Z) P
  rw [LinearMap.comp_apply, LinearMap.comp_apply] at this
  rw [this, ctr_act R U hZ, neg_add_cancel]

/- English proof (translation)
Establish `ex : ∀ P, ∃ z : R.HK.V ⊗[ℂ] U, ∀ y, ctr R U y z = B P y`. Introduce `P`. Take `⟨E, hE, hkill⟩` from `exists_finiteDimensional_kill R a ha hA B hB P`. Take `⟨n, e, heE, he⟩` from `exists_frame R.ι R.ι_inj E`. Use `⟨∑ j, e j ⊗ₜ[ℂ] B P (e j), fun y => ?_⟩` and prove the remaining obligations.

Establish `h1` using `hkill (y - ∑ j, inner ℂ (R.ι (e j)) (R.ι y) • e j) (fun x hx => by`. Rewrite using `[map_sub, inner_sub_left, sub_eq_zero]`. Use `conv_lhs => rw [← he x hx]`. Simplify using `only [map_sum, map_smul, inner_sum, sum_inner, inner_smul_right, inner_smul_left, inner_conj_symm, mul_comm])`. Rewrite `h1` using `[map_sub, sub_eq_zero]`.

Rewrite using `[h1]`. Simplify using `only [map_sum, ctr_tmul, LinearMap.map_smulₛₗ, inner_conj_symm]`. Use `choose g hg using ex`. Set `f : W →ₗ[ℂ] R.HK.V ⊗[ℂ] U` to `{ toFun := g map_add' := fun P Q => ext_ctr R U _ _ fun y => by`. Rewrite using `[map_add, hg, hg, hg, map_add, LinearMap.add_apply]`.

Use the proof step `map_smul' := fun t P => ext_ctr R U _ _ fun y => by`. Rewrite using `[map_smul, hg, hg, map_smul, RingHom.id_apply, LinearMap.smul_apply] }`. Establish `hf : ∀ P y, ctr R U y (f P) = B P y` using `hg`. Establish `hreal : ∀ X ∈ upq p q, ∀ P, f (a X P) = TensorProduct.map (R.HK.act X) LinearMap.id (f P)`. Introduce `X hX P`.

Use `ext_ctr R U _ _ fun y => ?_` and prove the remaining obligations. Rewrite using `[ctr_act R U hX, hf, hf]`. Conclude with `eq_neg_of_add_eq_zero_left (hB X hX P y)`. Use `⟨f, fun Z => ?_, fun P y => (hf P y).symm⟩` and prove the remaining obligations. Take `⟨X, Y, hX, hY, -, rfl⟩` from `exists_real_parts Z`.

Use `LinearMap.ext fun P => ?_` and prove the remaining obligations. Simplify using `only [LinearMap.comp_apply, map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, TensorProduct.map_add_left, TensorProduct.map_smul_left, hreal X hX, hreal Y hY]`.
-/
theorem exists_map (ha : IsGK a) (hA : AdmGK R.HK)
    (B : W →ₗ[ℂ] R.HK.V →ₛₗ[starRingEnd ℂ] U) (hB : PInv a R B) :
    ∃ f : W →ₗ[ℂ] R.HK.V ⊗[ℂ] U,
      (∀ Z, f ∘ₗ a Z = TensorProduct.map (R.HK.act Z) LinearMap.id ∘ₗ f) ∧
        ∀ P v, B P v = ctr R U v (f P) := by
  have ex : ∀ P, ∃ z : R.HK.V ⊗[ℂ] U, ∀ y, ctr R U y z = B P y := by
    intro P
    obtain ⟨E, hE, hkill⟩ := exists_finiteDimensional_kill R a ha hA B hB P
    obtain ⟨n, e, heE, he⟩ := exists_frame R.ι R.ι_inj E
    refine ⟨∑ j, e j ⊗ₜ[ℂ] B P (e j), fun y => ?_⟩
    have h1 := hkill (y - ∑ j, inner ℂ (R.ι (e j)) (R.ι y) • e j) (fun x hx => by
      rw [map_sub, inner_sub_left, sub_eq_zero]
      conv_lhs => rw [← he x hx]
      simp only [map_sum, map_smul, inner_sum, sum_inner, inner_smul_right, inner_smul_left,
        inner_conj_symm, mul_comm])
    rw [map_sub, sub_eq_zero] at h1
    rw [h1]
    simp only [map_sum, ctr_tmul, LinearMap.map_smulₛₗ, inner_conj_symm]
  choose g hg using ex
  let f : W →ₗ[ℂ] R.HK.V ⊗[ℂ] U :=
    { toFun := g
      map_add' := fun P Q => ext_ctr R U _ _ fun y => by
        rw [map_add, hg, hg, hg, map_add, LinearMap.add_apply]
      map_smul' := fun t P => ext_ctr R U _ _ fun y => by
        rw [map_smul, hg, hg, map_smul, RingHom.id_apply, LinearMap.smul_apply] }
  have hf : ∀ P y, ctr R U y (f P) = B P y := hg
  have hreal : ∀ X ∈ upq p q, ∀ P,
      f (a X P) = TensorProduct.map (R.HK.act X) LinearMap.id (f P) := by
    intro X hX P
    refine ext_ctr R U _ _ fun y => ?_
    rw [ctr_act R U hX, hf, hf]
    exact eq_neg_of_add_eq_zero_left (hB X hX P y)
  refine ⟨f, fun Z => ?_, fun P y => (hf P y).symm⟩
  obtain ⟨X, Y, hX, hY, -, rfl⟩ := exists_real_parts Z
  refine LinearMap.ext fun P => ?_
  simp only [LinearMap.comp_apply, map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply,
    TensorProduct.map_add_left, TensorProduct.map_smul_left, hreal X hX, hreal Y hY]

end GlobalTheory.ArchRec.PairTensor

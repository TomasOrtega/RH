import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LevelSplitting.RatVMemSpan
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicLocalCompactness.T2SpaceTensorProductFiniteExtension

noncomputable section

namespace PI.LevelKSplit.W.ExC

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub NumberField IsDedekindDomain PI.LevelKSplit PI.LevelKSplit.W.Glob
open scoped TensorProduct

section Alg

variable {F E : Type} [Field F] [Field E] [Algebra F E] {R : Type} [CommRing R] [Algebra F R]
  {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E}

open Classical in

def projD (R : Type) [CommRing R] [Algebra F R] (σ : E →ₐ[F] E) (J : Matrix (Fin n) (Fin n) E)
    {m : ℕ} (Y D : Fin m → Fin n → E) (s : Set (Fin m)) (y : Fin n → R ⊗[F] E) :
    Fin n → R ⊗[F] E :=
  ∑ a, (if a ∈ s then covR R σ J (D a) ⬝ᵥ y else 0) • ratV (F := F) R (Y a)

/- English proof (translation)
Unfold `projD`. Rewrite using `[← Finset.sum_add_distrib]`. Use `Finset.sum_congr rfl fun a _ => ?_` and prove the remaining obligations. Use `split_ifs`. Rewrite using `[dotProduct_add, add_smul]`.

Rewrite using `[zero_smul, add_zero]`.
-/
theorem projD_add {m : ℕ} (Y D : Fin m → Fin n → E) (s : Set (Fin m)) (x y : Fin n → R ⊗[F] E) :
    projD R σ J Y D s (x + y) = projD R σ J Y D s x + projD R σ J Y D s y := by
  unfold projD
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun a _ => ?_
  split_ifs
  · rw [dotProduct_add, add_smul]
  · rw [zero_smul, add_zero]

/- English proof (translation)
Unfold `projD`. Rewrite using `[Finset.smul_sum]`. Use `Finset.sum_congr rfl fun a _ => ?_` and prove the remaining obligations. Use `split_ifs`. Rewrite using `[dotProduct_smul, smul_eq_mul, mul_smul]`.

Rewrite using `[zero_smul, smul_zero]`.
-/
theorem projD_smul {m : ℕ} (Y D : Fin m → Fin n → E) (s : Set (Fin m)) (c : R ⊗[F] E)
    (y : Fin n → R ⊗[F] E) :
    projD R σ J Y D s (c • y) = c • projD R σ J Y D s y := by
  unfold projD
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  split_ifs
  · rw [dotProduct_smul, smul_eq_mul, mul_smul]
  · rw [zero_smul, smul_zero]

/- English proof (translation)
Unfold `projD`. Use `Finset.sum_eq_zero fun a _ => ?_` and prove the remaining obligations. Use `split_ifs`. Rewrite using `[dotProduct_zero, zero_smul]`. Rewrite using `[zero_smul]`.
-/
theorem projD_zero {m : ℕ} (Y D : Fin m → Fin n → E) (s : Set (Fin m)) :
    projD R σ J Y D s 0 = 0 := by
  unfold projD
  refine Finset.sum_eq_zero fun a _ => ?_
  split_ifs
  · rw [dotProduct_zero, zero_smul]
  · rw [zero_smul]

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `hy`. Proceed by induction on `hy using Submodule.span_induction with`. Consider the case `mem x hx`. Take `⟨a0, ha0, rfl⟩` from `hx`.

Use `symm`. Unfold `projD`. Rewrite using `[Finset.sum_eq_single a0]`. Rewrite using `[if_pos ha0, covR_ratV, hD, if_pos rfl, map_one, one_smul]`. Introduce `a _ hne split_ifs`.

Rewrite using `[covR_ratV, hD, if_neg (Ne.symm hne), map_zero, zero_smul]`. Conclude with `zero_smul _ _`. Introduce `h`. Conclude with `absurd (Finset.mem_univ _) h`. Consider the case `zero => rw [projD_zero]`.

Consider the case `add x y _ _ hx hy => rw [projD_add, ← hx, ← hy]`. Consider the case `smul c x _ hx => rw [projD_smul, ← hx]`. Introduce `h`. Rewrite using `[h]`. Unfold `projD`.

Use `Submodule.sum_mem _ fun a _ => ?_` and prove the remaining obligations. Use `split_ifs with ha`. Conclude with `Submodule.smul_mem _ _ (Submodule.subset_span ⟨a, ha, rfl⟩)`. Rewrite using `[zero_smul]`. Conclude with `Submodule.zero_mem _`.
-/
theorem mem_spanR_iff {m : ℕ} (Y D : Fin m → Fin n → E)
    (hD : ∀ a a', hE σ J (D a') (Y a) = if a = a' then 1 else 0) (s : Set (Fin m))
    (y : Fin n → R ⊗[F] E) :
    y ∈ spanR (F := F) R Y s ↔ y = projD R σ J Y D s y := by
  constructor
  · intro hy
    induction hy using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨a0, ha0, rfl⟩ := hx
      symm
      unfold projD
      rw [Finset.sum_eq_single a0]
      · rw [if_pos ha0, covR_ratV, hD, if_pos rfl, map_one, one_smul]
      · intro a _ hne
        split_ifs
        · rw [covR_ratV, hD, if_neg (Ne.symm hne), map_zero, zero_smul]
        · exact zero_smul _ _
      · intro h
        exact absurd (Finset.mem_univ _) h
    | zero => rw [projD_zero]
    | add x y _ _ hx hy => rw [projD_add, ← hx, ← hy]
    | smul c x _ hx => rw [projD_smul, ← hx]
  · intro h
    rw [h]
    unfold projD
    refine Submodule.sum_mem _ fun a _ => ?_
    split_ifs with ha
    · exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨a, ha, rfl⟩)
    · rw [zero_smul]
      exact Submodule.zero_mem _

/- English proof (translation)
Simplify using `only [hE, Formalism.UG.hform, Pi.smul_apply, smul_eq_mul, AlgHom.coe_toRingHom, map_mul, Finset.mul_sum, mul_assoc]`.
-/
theorem hE_smul_left (c : E) (x y : Fin n → E) : hE σ J (c • x) y = σ c * hE σ J x y := by
  simp only [hE, Formalism.UG.hform, Pi.smul_apply, smul_eq_mul, AlgHom.coe_toRingHom, map_mul,
    Finset.mul_sum, mul_assoc]

/- English proof (translation)
Rewrite using `[hE_swap hJ hinv, hP.2.2.1 a a']`. Apply the tactic sequence `split_ifs <;> simp`.
-/
theorem dual_e (hJ : IsHermND σ J) (hinv : ∀ x, σ (σ x) = x) {r : ℕ} (P : Frame E n r) (T : F)
    (hP : P.IsStd σ J T) (a a' : Fin r) :
    hE σ J (P.f a') (P.e a) = if a = a' then 1 else 0 := by
  rw [hE_swap hJ hinv, hP.2.2.1 a a']
  split_ifs <;> simp

def dualFrameAlt {r : ℕ} (P : Frame E n r) (T : F) : Fin (r + 1) → Fin n → E :=
  Fin.snoc P.f (algebraMap F E (-T)⁻¹ • P.z)

/- English proof (translation)
Establish `hc : σ (algebraMap F E (-T)⁻¹) = algebraMap F E (-T)⁻¹` using `σ.commutes _`. Proceed by induction on `a using Fin.lastCases with`. Consider the case `last`. Proceed by induction on `a' using Fin.lastCases with`. Consider the case `last`.

Simplify using `only [dualFrameAlt, F0, Fin.snoc_last, hE_smul_left, hc, if_true]`. Rewrite using `[hP.2.2.2.2.2.1, ← map_mul, inv_mul_cancel₀ (neg_ne_zero.2 hP.2.2.2.2.2.2), map_one]`. Consider the case `cast j`. Simplify using `only [dualFrameAlt, F0, Fin.snoc_last, Fin.snoc_castSucc, hP.2.2.2.2.1 j]`. Rewrite using `[if_neg (fun h => Fin.castSucc_ne_last j h.symm)]`.

Consider the case `cast i`. Proceed by induction on `a' using Fin.lastCases with`. Consider the case `last`. Simplify using `only [dualFrameAlt, F0, Fin.snoc_last, Fin.snoc_castSucc, hE_smul_left]`. Rewrite using `[hE_swap hJ hinv, hP.2.2.2.1 i, map_zero, mul_zero]`.

Simplify using `[Fin.castSucc_ne_last]`. Consider the case `cast j`. Simplify using `only [dualFrameAlt, F0, Fin.snoc_castSucc, Fin.castSucc_inj]`. Conclude with `dual_e hJ hinv P T hP i j`.
-/
theorem dual_frame_pairing (hJ : IsHermND σ J) (hinv : ∀ x, σ (σ x) = x) {r : ℕ} (P : Frame E n r) (T : F)
    (hP : P.IsStd σ J T) (a a' : Fin (r + 1)) :
    hE σ J (dualFrameAlt P T a') (F0 P a) = if a = a' then 1 else 0 := by
  have hc : σ (algebraMap F E (-T)⁻¹) = algebraMap F E (-T)⁻¹ := σ.commutes _
  induction a using Fin.lastCases with
  | last =>
    induction a' using Fin.lastCases with
    | last =>
      simp only [dualFrameAlt, F0, Fin.snoc_last, hE_smul_left, hc, if_true]
      rw [hP.2.2.2.2.2.1, ← map_mul, inv_mul_cancel₀ (neg_ne_zero.2 hP.2.2.2.2.2.2), map_one]
    | cast j =>
      simp only [dualFrameAlt, F0, Fin.snoc_last, Fin.snoc_castSucc, hP.2.2.2.2.1 j]
      rw [if_neg (fun h => Fin.castSucc_ne_last j h.symm)]
  | cast i =>
    induction a' using Fin.lastCases with
    | last =>
      simp only [dualFrameAlt, F0, Fin.snoc_last, Fin.snoc_castSucc, hE_smul_left]
      rw [hE_swap hJ hinv, hP.2.2.2.1 i, map_zero, mul_zero]
      simp [Fin.castSucc_ne_last]
    | cast j =>
      simp only [dualFrameAlt, F0, Fin.snoc_castSucc, Fin.castSucc_inj]
      exact dual_e hJ hinv P T hP i j

end Alg

section Top

variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] [FiniteDimensional F E]
  {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E}

/- English proof (translation)
Unfold `projD`. Use `continuous_finsetSum _ fun a _ => ?_` and prove the remaining obligations. Establish `hc : Continuous fun y : Fin n → Af F ⊗[F] E => covR (Af F) σ J (D a) ⬝ᵥ y`. Simplify using `only [dotProduct]`. Conclude with `continuous_finsetSum _ fun i _ => Continuous.mul continuous_const (continuous_apply i)`.

Conclude with `(continuous_if_const _ (fun _ => hc) (fun _ => continuous_const)).smul continuous_const`.
-/
theorem continuous_projD {m : ℕ} (Y D : Fin m → Fin n → E) (s : Set (Fin m)) :
    Continuous (projD (Af F) σ J Y D s) := by
  classical
  unfold projD
  refine continuous_finsetSum _ fun a _ => ?_
  have hc : Continuous fun y : Fin n → Af F ⊗[F] E => covR (Af F) σ J (D a) ⬝ᵥ y := by
    simp only [dotProduct]
    exact continuous_finsetSum _ fun i _ => Continuous.mul continuous_const (continuous_apply i)
  exact (continuous_if_const _ (fun _ => hc) (fun _ => continuous_const)).smul continuous_const

/- English proof (translation)
Establish `h : (spanR (F` using `F) (Af F) Y s : Set (Fin n → Af F ⊗[F] E)) = {y | y = projD (Af F) σ J Y D s y} := Set.ext fun y => mem_spanR_iff Y D hD s y`. Rewrite using `[h]`. Conclude with `isClosed_eq continuous_id (continuous_projD Y D s)`.
-/
theorem isClosed_spanR {m : ℕ} (Y D : Fin m → Fin n → E)
    (hD : ∀ a a', hE σ J (D a') (Y a) = if a = a' then 1 else 0) (s : Set (Fin m)) :
    IsClosed (spanR (F := F) (Af F) Y s : Set (Fin n → Af F ⊗[F] E)) := by
  have h : (spanR (F := F) (Af F) Y s : Set (Fin n → Af F ⊗[F] E)) =
      {y | y = projD (Af F) σ J Y D s y} := Set.ext fun y => mem_spanR_iff Y D hD s y
  rw [h]
  exact isClosed_eq continuous_id (continuous_projD Y D s)

/- English proof (translation)
Establish `hv : Continuous (fun g : HA (Af F) σ J => ((HA.mat (Af F) σ J g : GL (Fin n) (Af F ⊗[F] E)) : Matrix (Fin n) (Fin n) (Af F ⊗[F] E)))` using `Units.continuous_val.comp continuous_subtype_val`. Simplify using `only [lin, Matrix.mulVecLin_apply]`. Conclude with `hv.matrix_mulVec continuous_const`.
-/
theorem continuous_lin (v : Fin n → Af F ⊗[F] E) :
    Continuous (fun g : HA (Af F) σ J => lin (Af F) σ J g v) := by
  have hv : Continuous (fun g : HA (Af F) σ J =>
      ((HA.mat (Af F) σ J g : GL (Fin n) (Af F ⊗[F] E)) : Matrix (Fin n) (Fin n) (Af F ⊗[F] E))) :=
    Units.continuous_val.comp continuous_subtype_val
  simp only [lin, Matrix.mulVecLin_apply]
  exact hv.matrix_mulVec continuous_const

/- English proof (translation)
Establish `h : (uniFlag (Af F) σ J Y : Set (HA (Af F) σ J)) = ⋂ b, (fun g => lin (Af F) σ J g (ratV (F` using `F) (Af F) (Y b)) - ratV (F := F) (Af F) (Y b)) ⁻¹' (spanR (F := F) (Af F) Y {a | a < b} : Set (Fin n → Af F ⊗[F] E)) := by`. Use extensionality with `g`. Simplify using `only [Set.mem_iInter, Set.mem_preimage, SetLike.mem_coe]`. Conclude with `Iff.rfl`. Rewrite using `[h]`.

Conclude with `isClosed_iInter fun b => (isClosed_spanR Y D hD _).preimage ((continuous_lin _).sub continuous_const)`.
-/
theorem isClosed_uniFlag {m : ℕ} (Y D : Fin m → Fin n → E)
    (hD : ∀ a a', hE σ J (D a') (Y a) = if a = a' then 1 else 0) :
    IsClosed (uniFlag (Af F) σ J Y : Set (HA (Af F) σ J)) := by
  have h : (uniFlag (Af F) σ J Y : Set (HA (Af F) σ J)) =
      ⋂ b, (fun g => lin (Af F) σ J g (ratV (F := F) (Af F) (Y b)) - ratV (F := F) (Af F) (Y b)) ⁻¹'
        (spanR (F := F) (Af F) Y {a | a < b} : Set (Fin n → Af F ⊗[F] E)) := by
    ext g
    simp only [Set.mem_iInter, Set.mem_preimage, SetLike.mem_coe]
    exact Iff.rfl
  rw [h]
  exact isClosed_iInter fun b =>
    (isClosed_spanR Y D hD _).preimage ((continuous_lin _).sub continuous_const)

/- English proof (translation)
Establish `h : (Nsub (Af F) σ J P : Set (HA (Af F) σ J)) = (uniFlag (Af F) σ J P.e : Set (HA (Af F) σ J)) ∩ ⋂ v, ⋂ (_ : InXperp (Af F) σ J P v), (fun g => lin (Af F) σ J g v - v) ⁻¹' (spanR (F` using `F) (Af F) P.e Set.univ : Set (Fin n → Af F ⊗[F] E)) := by`. Use extensionality with `g`. Simplify using `only [Set.mem_inter_iff, Set.mem_iInter, Set.mem_preimage, SetLike.mem_coe]`. Conclude with `Iff.rfl`. Rewrite using `[h]`.

Use `(isClosed_uniFlag P.e P.f (dual_e hJ hinv P T hP)).inter (isClosed_iInter fun v => isClosed_iInter fun _ => ?_)` and prove the remaining obligations. Conclude with `(isClosed_spanR P.e P.f (dual_e hJ hinv P T hP) _).preimage ((continuous_lin _).sub continuous_const)`.
-/
theorem isClosed_Nsub (hJ : IsHermND σ J) (hinv : ∀ x, σ (σ x) = x) {r : ℕ} (P : Frame E n r)
    (T : F) (hP : P.IsStd σ J T) :
    IsClosed (Nsub (Af F) σ J P : Set (HA (Af F) σ J)) := by
  have h : (Nsub (Af F) σ J P : Set (HA (Af F) σ J)) =
      (uniFlag (Af F) σ J P.e : Set (HA (Af F) σ J)) ∩
        ⋂ v, ⋂ (_ : InXperp (Af F) σ J P v), (fun g => lin (Af F) σ J g v - v) ⁻¹'
          (spanR (F := F) (Af F) P.e Set.univ : Set (Fin n → Af F ⊗[F] E)) := by
    ext g
    simp only [Set.mem_inter_iff, Set.mem_iInter, Set.mem_preimage, SetLike.mem_coe]
    exact Iff.rfl
  rw [h]
  refine (isClosed_uniFlag P.e P.f (dual_e hJ hinv P T hP)).inter
    (isClosed_iInter fun v => isClosed_iInter fun _ => ?_)
  exact (isClosed_spanR P.e P.f (dual_e hJ hinv P T hP) _).preimage
    ((continuous_lin _).sub continuous_const)

/- English proof (translation)
Establish `h : (stabT (Af F) σ J X : Set (HA (Af F) σ J)) = ⋂ b, {g | lin (Af F) σ J g (ratV (F` using `F) (Af F) (X b)) = ratV (F := F) (Af F) (X b)} := by`. Use extensionality with `g`. Simplify using `only [Set.mem_iInter, Set.mem_ofPred_eq, SetLike.mem_coe]`. Conclude with `mem_stabT (Af F) σ J X g`. Rewrite using `[h]`.

Conclude with `isClosed_iInter fun b => isClosed_eq (continuous_lin _) continuous_const`.
-/
theorem isClosed_stabT {a : ℕ} (X : Fin a → Fin n → E) :
    IsClosed (stabT (Af F) σ J X : Set (HA (Af F) σ J)) := by
  have h : (stabT (Af F) σ J X : Set (HA (Af F) σ J)) =
      ⋂ b, {g | lin (Af F) σ J g (ratV (F := F) (Af F) (X b)) = ratV (F := F) (Af F) (X b)} := by
    ext g
    simp only [Set.mem_iInter, Set.mem_ofPred_eq, SetLike.mem_coe]
    exact mem_stabT (Af F) σ J X g
  rw [h]
  exact isClosed_iInter fun b => isClosed_eq (continuous_lin _) continuous_const

/- English proof (translation)
Assemble the required witnesses or components as `⟨isClosed_uniFlag (F0 P) (dualFrameAlt P T) (dual_frame_pairing hJ hinv P T hP), isClosed_Nsub hJ hinv P T hP, isClosed_stabT (tupH P)⟩`.
-/
theorem closed_SNH (hJ : IsHermND σ J) (hinv : ∀ x, σ (σ x) = x) {r : ℕ} (P : Frame E n r) (T : F)
    (hP : P.IsStd σ J T) :
    IsClosed (Ssub (Af F) σ J P : Set (HA (Af F) σ J)) ∧
      IsClosed (Nsub (Af F) σ J P : Set (HA (Af F) σ J)) ∧
      IsClosed (Hsub (Af F) σ J P : Set (HA (Af F) σ J)) :=
  ⟨isClosed_uniFlag (F0 P) (dualFrameAlt P T) (dual_frame_pairing hJ hinv P T hP), isClosed_Nsub hJ hinv P T hP,
    isClosed_stabT (tupH P)⟩

/- English proof (translation)
Take `⟨ι, _, ⟨h⟩⟩` from `PI.AdicCompletionValuation.exists_homeomorph_tens (F := F) (E := E) (Af F)`. Establish `: SecondCountableTopology (Af F ⊗[F] E)` using `h.isEmbedding.secondCountableTopology`. Establish `: SecondCountableTopology (Matrix (Fin n) (Fin n) (Af F ⊗[F] E))` using `inferInstanceAs (SecondCountableTopology (Fin n → Fin n → Af F ⊗[F] E))`. Establish `: SecondCountableTopology (Matrix (Fin n) (Fin n) (Af F ⊗[F] E))ᵐᵒᵖ` using `MulOpposite.opHomeomorph.symm.isEmbedding.secondCountableTopology`. Establish `: T2Space (Matrix (Fin n) (Fin n) (Af F ⊗[F] E))ᵐᵒᵖ` using `MulOpposite.opHomeomorph.symm.isEmbedding.t2Space`.

Establish `: SecondCountableTopology (GL (Fin n) (Af F ⊗[F] E))` using `Units.isEmbedding_embedProduct.secondCountableTopology`. Establish `: T2Space (GL (Fin n) (Af F ⊗[F] E))` using `Units.isEmbedding_embedProduct.t2Space`. Establish `hemb : Topology.IsEmbedding (Subtype.val : HR (Af F) σ J → GL (Fin n) (Af F ⊗[F] E))` using `Topology.IsEmbedding.subtypeVal`. Establish `h1 : SecondCountableTopology (HR (Af F) σ J)` using `hemb.secondCountableTopology`. Establish `h2 : T2Space (HR (Af F) σ J)` using `hemb.t2Space`.

Conclude with `⟨inferInstanceAs (SecondCountableTopology (HR (Af F) σ J)), inferInstanceAs (T2Space (HR (Af F) σ J))⟩`.
-/
theorem unitary_group_secondCountable_t2 (hsc : SecondCountableTopology (Af F)) :
    SecondCountableTopology (HA (Af F) σ J) ∧ T2Space (HA (Af F) σ J) := by
  obtain ⟨ι, _, ⟨h⟩⟩ := PI.AdicCompletionValuation.exists_homeomorph_tens (F := F) (E := E) (Af F)
  have : SecondCountableTopology (Af F ⊗[F] E) := h.isEmbedding.secondCountableTopology
  have : SecondCountableTopology (Matrix (Fin n) (Fin n) (Af F ⊗[F] E)) :=
    inferInstanceAs (SecondCountableTopology (Fin n → Fin n → Af F ⊗[F] E))
  have : SecondCountableTopology (Matrix (Fin n) (Fin n) (Af F ⊗[F] E))ᵐᵒᵖ :=
    MulOpposite.opHomeomorph.symm.isEmbedding.secondCountableTopology
  have : T2Space (Matrix (Fin n) (Fin n) (Af F ⊗[F] E))ᵐᵒᵖ :=
    MulOpposite.opHomeomorph.symm.isEmbedding.t2Space
  have : SecondCountableTopology (GL (Fin n) (Af F ⊗[F] E)) :=
    Units.isEmbedding_embedProduct.secondCountableTopology
  have : T2Space (GL (Fin n) (Af F ⊗[F] E)) := Units.isEmbedding_embedProduct.t2Space
  have hemb : Topology.IsEmbedding (Subtype.val : HR (Af F) σ J → GL (Fin n) (Af F ⊗[F] E)) :=
    Topology.IsEmbedding.subtypeVal
  have h1 : SecondCountableTopology (HR (Af F) σ J) := hemb.secondCountableTopology
  have h2 : T2Space (HR (Af F) σ J) := hemb.t2Space
  exact ⟨inferInstanceAs (SecondCountableTopology (HR (Af F) σ J)),
    inferInstanceAs (T2Space (HR (Af F) σ J))⟩

end Top

end PI.LevelKSplit.W.ExC

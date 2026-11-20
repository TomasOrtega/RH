import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittSmallGroupEmbeddingMemPointwiseStabilizerIso
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.MixModel GlobalTheory.MixPer
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.JacClosed

open GlobalTheory.MixModel.HypDec

variable {D : D7} {S S₀ : HSp D} {ρ : ℕ}

def uniOnX (d : HypDec S S₀ ρ) : Set (GA D S) :=
  {g | mt S g ⬝ d.jX = d.jX ⬝ blockX d g ∧ (∀ i j : Fin ρ, j < i → blockX d g i j = 0) ∧ ∀ i, blockX d g i i = 1}

/- English proof (translation)
Use `haveI : T2Space (Mx D 1 1) := (lattice_Mx D 1 1).2.2.2.1`. Conclude with `@T2Space.of_injective_continuous _ _ _ _ this (fun a : AE D => (Matrix.of fun _ _ => a : Mx D 1 1)) (fun a b h => congrFun (congrFun h 0) 0) (continuous_pi fun _ => continuous_pi fun _ => continuous_id)`.
-/
theorem t2Space_cm_host_adeles : T2Space (AE D) := by
  haveI : T2Space (Mx D 1 1) := (lattice_Mx D 1 1).2.2.2.1
  exact @T2Space.of_injective_continuous _ _ _ _ this (fun a : AE D => (Matrix.of fun _ _ => a : Mx D 1 1))
    (fun a b h => congrFun (congrFun h 0) 0) (continuous_pi fun _ => continuous_pi fun _ => continuous_id)

/- English proof (translation)
Use `haveI : T2Space (AE D) := t2Space_cm_host_adeles`. Establish `hm` using `GlobalTheory.MixModel.continuous_mt (D := D) S`. Establish `hb : Continuous fun g : GA D S => blockX d g` using `continuous_const.matrix_mul (hm.matrix_mul continuous_const)`. Establish `e1 : {g : GA D S | ∀ i j : Fin ρ, j < i → blockX d g i j = 0} = ⋂ i : Fin ρ, ⋂ j : Fin ρ, ⋂ (_ : j < i), {g | blockX d g i j = 0}` using `by ext; simp only [Set.mem_setOf_eq, Set.mem_iInter]`. Establish `e2 : {g : GA D S | ∀ i : Fin ρ, blockX d g i i = 1} = ⋂ i : Fin ρ, {g | blockX d g i i = 1}` using `by ext; simp only [Set.mem_setOf_eq, Set.mem_iInter]`.

Establish `c1 : IsClosed {g : GA D S | ∀ i j : Fin ρ, j < i → blockX d g i j = 0}`. Rewrite using `[e1]`. Conclude with `isClosed_iInter fun i => isClosed_iInter fun j => isClosed_iInter fun _ => isClosed_eq ((continuous_apply j).comp ((continuous_apply i).comp hb)) continuous_const`. Establish `c2 : IsClosed {g : GA D S | ∀ i : Fin ρ, blockX d g i i = 1}`. Rewrite using `[e2]`.

Conclude with `isClosed_iInter fun i => isClosed_eq ((continuous_apply i).comp ((continuous_apply i).comp hb)) continuous_const`. Conclude with `(isClosed_eq (hm.matrix_mul continuous_const) (continuous_const.matrix_mul hb)).inter (c1.inter c2)`.
-/
theorem isClosed_uniOnX (d : HypDec S S₀ ρ) : IsClosed (uniOnX d) := by
  haveI : T2Space (AE D) := t2Space_cm_host_adeles
  have hm := GlobalTheory.MixModel.continuous_mt (D := D) S
  have hb : Continuous fun g : GA D S => blockX d g := continuous_const.matrix_mul (hm.matrix_mul continuous_const)
  have e1 : {g : GA D S | ∀ i j : Fin ρ, j < i → blockX d g i j = 0} =
      ⋂ i : Fin ρ, ⋂ j : Fin ρ, ⋂ (_ : j < i), {g | blockX d g i j = 0} := by ext; simp only [Set.mem_setOf_eq, Set.mem_iInter]
  have e2 : {g : GA D S | ∀ i : Fin ρ, blockX d g i i = 1} = ⋂ i : Fin ρ, {g | blockX d g i i = 1} := by ext; simp only [Set.mem_setOf_eq, Set.mem_iInter]
  have c1 : IsClosed {g : GA D S | ∀ i j : Fin ρ, j < i → blockX d g i j = 0} := by
    rw [e1]
    exact isClosed_iInter fun i => isClosed_iInter fun j => isClosed_iInter fun _ =>
      isClosed_eq ((continuous_apply j).comp ((continuous_apply i).comp hb)) continuous_const
  have c2 : IsClosed {g : GA D S | ∀ i : Fin ρ, blockX d g i i = 1} := by
    rw [e2]
    exact isClosed_iInter fun i => isClosed_eq ((continuous_apply i).comp ((continuous_apply i).comp hb)) continuous_const
  exact (isClosed_eq (hm.matrix_mul continuous_const) (continuous_const.matrix_mul hb)).inter (c1.inter c2)

/- English proof (translation)
Establish `hb : blockX d g = u.1` using `by rw [blockX, h, ← Matrix.mul_assoc, d.pX_jX, Matrix.one_mul]`. Use `⟨by rw [hb]; exact h, fun i j hij => ?_, fun i => ?_⟩` and prove the remaining obligations. Rewrite using `[hb]`. Conclude with `(hu i j).1 hij`. Rewrite using `[hb]`.

Conclude with `(hu i i).2`.
-/
theorem mem_uniOnX_of (d : HypDec S S₀ ρ) {g : GA D S} {u : GL (Fin ρ) (AE D)} (hu : u ∈ upperUni ρ (AE D))
    (h : mt S g ⬝ d.jX = d.jX ⬝ u.1) : g ∈ uniOnX d := by
  have hb : blockX d g = u.1 := by rw [blockX, h, ← Matrix.mul_assoc, d.pX_jX, Matrix.one_mul]
  refine ⟨by rw [hb]; exact h, fun i j hij => ?_, fun i => ?_⟩
  · rw [hb]; exact (hu i j).1 hij
  · rw [hb]; exact (hu i i).2

def uniOnXSub (d : HypDec S S₀ ρ) : Subgroup (GA D S) where
  carrier := {g | ∃ u ∈ UX D ρ, mt S g ⬝ d.jX = d.jX ⬝ u.1}
  one_mem' := ⟨1, one_mem _, by rw [mt_one, Matrix.one_mul, Units.val_one, Matrix.mul_one]⟩
  mul_mem' := by
    rintro a b ⟨u, hu, ha⟩ ⟨v, hv, hb⟩
    exact ⟨u * v, mul_mem hu hv, by
      rw [mt_mul, Matrix.mul_assoc, hb, ← Matrix.mul_assoc, ha, Matrix.mul_assoc, Units.val_mul]⟩
  inv_mem' := by
    rintro a ⟨u, hu, ha⟩
    refine ⟨u⁻¹, inv_mem hu, ?_⟩
    have h1 : mt S a⁻¹ ⬝ d.jX ⬝ u.1 = d.jX := by
      rw [Matrix.mul_assoc, ← ha, ← Matrix.mul_assoc, mt_inv_mul, Matrix.one_mul]
    calc mt S a⁻¹ ⬝ d.jX = mt S a⁻¹ ⬝ d.jX ⬝ (u.1 ⬝ (u⁻¹).1) := by
          rw [← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.mul_one]
      _ = d.jX ⬝ (u⁻¹).1 := by rw [← Matrix.mul_assoc, h1]

def uniUnit (U : Mx D ρ ρ) (h0 : ∀ i j : Fin ρ, j < i → U i j = 0) (h1 : ∀ i, U i i = 1) : GL (Fin ρ) (AE D) :=
  Matrix.nonsingInvUnit U (by
    rw [Matrix.det_of_upperTriangular (fun i j (h : j < i) => h0 i j h)]
    simp [h1])

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem uniUnit_val (U : Mx D ρ ρ) (h0 : ∀ i j : Fin ρ, j < i → U i j = 0) (h1 : ∀ i, U i i = 1) :
    (uniUnit U h0 h1).1 = U := rfl

/- English proof (translation)
Introduce `i j` and use `⟨h0 i j, h1 i⟩`.
-/
theorem uniUnit_mem (U : Mx D ρ ρ) (h0 : ∀ i j : Fin ρ, j < i → U i j = 0) (h1 : ∀ i, U i i = 1) :
    uniUnit U h0 h1 ∈ upperUni ρ (AE D) := fun i j => ⟨h0 i j, h1 i⟩

/- English proof (translation)
Use `show Subgroup.closure _ ≤ _`. Rewrite using `[Subgroup.closure_le]`. Introduce and unpack `g ⟨hX, -⟩`. Use `choose a ha1 ha2 using hX`. Set `A : Mx D ρ ρ` to `Matrix.of fun j i => a i j`.

Establish `hcol : subOne S g ⬝ d.jX = d.jX ⬝ A`. Use extensionality with `k i`. Conclude with `congrFun (ha2 i) k`. Establish `h0 : ∀ i j : Fin ρ, j < i → (1 + A) i j = 0` using `fun i j h => by`. Simplify using `only [Matrix.add_apply, A, Matrix.of_apply, Matrix.one_apply_ne h.ne', ha1 j i h.le, add_zero]`.

Establish `h1 : ∀ i, (1 + A) i i = 1` using `fun i => by`. Simplify using `only [Matrix.add_apply, A, Matrix.of_apply, Matrix.one_apply_eq, ha1 i i le_rfl, add_zero]`. Use `⟨uniUnit (1 + A) h0 h1, uniUnit_mem _ h0 h1, ?_⟩` and prove the remaining obligations. Rewrite using `[uniUnit_val, Matrix.mul_add, Matrix.mul_one, ← hcol, GlobalTheory.MixModel.HypDec.subOne_mul, add_sub_cancel]`.
-/
theorem flagN_le (d : HypDec S S₀ ρ) : flagN d ≤ uniOnXSub d := by
  show Subgroup.closure _ ≤ _
  rw [Subgroup.closure_le]
  rintro g ⟨hX, -⟩
  choose a ha1 ha2 using hX
  let A : Mx D ρ ρ := Matrix.of fun j i => a i j
  have hcol : subOne S g ⬝ d.jX = d.jX ⬝ A := by
    ext k i
    exact congrFun (ha2 i) k
  have h0 : ∀ i j : Fin ρ, j < i → (1 + A) i j = 0 := fun i j h => by
    simp only [Matrix.add_apply, A, Matrix.of_apply, Matrix.one_apply_ne h.ne', ha1 j i h.le, add_zero]
  have h1 : ∀ i, (1 + A) i i = 1 := fun i => by
    simp only [Matrix.add_apply, A, Matrix.of_apply, Matrix.one_apply_eq, ha1 i i le_rfl, add_zero]
  refine ⟨uniUnit (1 + A) h0 h1, uniUnit_mem _ h0 h1, ?_⟩
  rw [uniUnit_val, Matrix.mul_add, Matrix.mul_one, ← hcol, GlobalTheory.MixModel.HypDec.subOne_mul, add_sub_cancel]

/- English proof (translation)
Use `sup_le (flagN_le d) ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨h, rfl⟩`. Conclude with `⟨1, one_mem _, by rw [wittDecomp_anisotropicEmbedding_inclX, Units.val_one, Matrix.mul_one]⟩`.
-/
theorem jacGrp_le (d : HypDec S S₀ ρ) : jacGrp d ≤ uniOnXSub d := by
  refine sup_le (flagN_le d) ?_
  rintro _ ⟨h, rfl⟩
  exact ⟨1, one_mem _, by rw [wittDecomp_anisotropicEmbedding_inclX, Units.val_one, Matrix.mul_one]⟩

set_option maxHeartbeats 2000000 in

/- English proof (translation)
Establish `hU : adj (mt S g) ⬝ (gA S ⬝ (mt S g ⬝ d.j0)) = gA S ⬝ d.j0` using `cancel₃ (mt_unitary S g) d.j0`. Establish `hY : d.pY ⬝ (mt S g ⬝ d.j0) = 0`. Establish `h1 : adj d.jX ⬝ (gA S ⬝ (mt S g ⬝ d.j0)) = adj (mt S g ⬝ d.jX) ⬝ (gA S ⬝ (mt S g ⬝ d.j0))` using `by rw [hg]`. Rewrite using `[d.pY_eq, Matrix.mul_assoc, h1, adj_mul, Matrix.mul_assoc, hU, d.wittDecomp_gram_X_anisotropic]`. Take `⟨b, hb⟩ : ∃ b, d.pX ⬝ (mt S g ⬝ d.j0) = b` from `⟨_, rfl⟩`.

Take `⟨A, hA⟩ : ∃ A, d.p0 ⬝ (mt S g ⬝ d.j0) = A` from `⟨_, rfl⟩`. Establish `hdec : mt S g ⬝ d.j0 = d.jX ⬝ b + d.j0 ⬝ A`. Establish `he : (d.jX ⬝ d.pX + d.j0 ⬝ d.p0 + d.jY ⬝ d.pY) ⬝ (mt S g ⬝ d.j0) = (1 : Mx D S.rank S.rank) ⬝ (mt S g ⬝ d.j0)` using `by rw [d.sum_eq_one]`. Simplify using `only [Matrix.add_mul, Matrix.one_mul, Matrix.mul_assoc, hY, hb, hA, Matrix.mul_zero, add_zero] at he`. Conclude with `he.symm`.

Establish `hAu : adj A * (gA S₀ * A) = gA S₀`. Establish `h1 : adj (mt S g ⬝ d.j0) ⬝ (gA S ⬝ (mt S g ⬝ d.j0)) = gA S₀`. Rewrite using `[adj_mul, Matrix.mul_assoc, hU, d.gram_00]`. Rewrite `h1` using `[hdec]`. Simplify using `only [adj_add, adj_mul, Matrix.add_mul, Matrix.mul_add, Matrix.mul_assoc, cancel₃ d.gram_XX, cancel₃ d.wittDecomp_gram_X_anisotropic, cancel₃ d.gram_0X, cancel₃ d.gram_00, Matrix.zero_mul, Matrix.mul_zero, add_zero, zero_add] at h1`.

Conclude with `h1`. Take `⟨h, hAh⟩ : ∃ h : GA D S₀, mt S₀ h = A` from `⟨ofMat S₀ A hAu, rfl⟩`. Establish `hAi : A ⬝ mt S₀ h⁻¹ = mt S₀ 1` using `by rw [← hAh, ← mt_mul, mul_inv_cancel]`. Establish `hi : (d.emb0 h)⁻¹ = d.emb0 h⁻¹` using `(map_inv d.emb0 h).symm`. Establish `hm0 : mt S (g * d.emb0 h⁻¹) = mt S g ⬝ mt S (d.emb0 h⁻¹)` using `mt_mul S _ _`.

Establish `he0 : mt S (d.emb0 h⁻¹) ⬝ d.j0 = d.j0 ⬝ mt S₀ h⁻¹` using `d.wittDecomp_anisotropicEmbedding_inclAnisotropic h⁻¹`. Establish `heX : mt S (d.emb0 h⁻¹) ⬝ d.jX = d.jX` using `d.wittDecomp_anisotropicEmbedding_inclX h⁻¹`. Establish `hj : d.j0 ⬝ mt S₀ (1 : GA D S₀) = d.j0` using `by rw [mt_one, Matrix.mul_one]`. Establish `hn0' : mt S (g * (d.emb0 h)⁻¹) ⬝ d.j0 = d.jX ⬝ (b ⬝ mt S₀ h⁻¹) + d.j0`. Establish `s1 : mt S (g * (d.emb0 h)⁻¹) ⬝ d.j0 = (mt S g ⬝ d.j0) ⬝ mt S₀ h⁻¹`.

Rewrite using `[hi, hm0, Matrix.mul_assoc, he0, Matrix.mul_assoc]`. Establish `s2 : (d.jX ⬝ b + d.j0 ⬝ A) ⬝ mt S₀ h⁻¹ = d.jX ⬝ (b ⬝ mt S₀ h⁻¹) + d.j0 ⬝ (A ⬝ mt S₀ h⁻¹)` using `(Matrix.add_mul (d.jX ⬝ b) (d.j0 ⬝ A) (mt S₀ h⁻¹)).trans (congrArg₂ (· + ·) (Matrix.mul_assoc d.jX b (mt S₀ h⁻¹)) (Matrix.mul_assoc d.j0 A (mt S₀ h⁻¹)))`. Establish `s3 : d.jX ⬝ (b ⬝ mt S₀ h⁻¹) + d.j0 ⬝ (A ⬝ mt S₀ h⁻¹) = d.jX ⬝ (b ⬝ mt S₀ h⁻¹) + d.j0` using `(congrArg (fun M : Mx D S₀.rank S₀.rank => d.jX ⬝ (b ⬝ mt S₀ h⁻¹) + d.j0 ⬝ M) hAi).trans (congrArg (fun M : Mx D S.rank S₀.rank => d.jX ⬝ (b ⬝ mt S₀ h⁻¹) + M) hj)`. Conclude with `s1.trans ((congrArg (fun M : Mx D S.rank S₀.rank => M ⬝ mt S₀ h⁻¹) hdec).trans (s2.trans s3))`. Establish `hn0 : mt S (g * (d.emb0 h)⁻¹) ⬝ d.j0 = d.j0 + d.jX ⬝ (b ⬝ mt S₀ h⁻¹)` using `hn0'.trans (add_comm _ _)`.

Establish `hnX' : mt S (g * (d.emb0 h)⁻¹) ⬝ d.jX = d.jX`. Rewrite using `[hi, hm0, Matrix.mul_assoc, heX, hg]`. Establish `hnX : mt S (g * (d.emb0 h)⁻¹) ⬝ d.jX = d.jX ⬝ (1 : GL (Fin ρ) (AE D)).1`. Rewrite using `[Units.val_one, Matrix.mul_one]`. Conclude with `hnX'`.

Establish `hn : g * (d.emb0 h)⁻¹ ∈ flagN d` using `d.mem_NFlag one_mem_upperUni hnX hn0`. Establish `hm : g * (d.emb0 h)⁻¹ * d.emb0 h ∈ jacGrp d` using `mul_mem (Subgroup.mem_sup_left hn) (Subgroup.mem_sup_right ⟨h, rfl⟩)`. Rewrite `hm` using `[inv_mul_cancel_right]`. Then use the resulting hypothesis.
-/
theorem mem_jacGrp_of_fix (d : HypDec S S₀ ρ) {g : GA D S} (hg : mt S g ⬝ d.jX = d.jX) : g ∈ jacGrp d := by
  have hU : adj (mt S g) ⬝ (gA S ⬝ (mt S g ⬝ d.j0)) = gA S ⬝ d.j0 := cancel₃ (mt_unitary S g) d.j0
  have hY : d.pY ⬝ (mt S g ⬝ d.j0) = 0 := by
    have h1 : adj d.jX ⬝ (gA S ⬝ (mt S g ⬝ d.j0)) = adj (mt S g ⬝ d.jX) ⬝ (gA S ⬝ (mt S g ⬝ d.j0)) := by rw [hg]
    rw [d.pY_eq, Matrix.mul_assoc, h1, adj_mul, Matrix.mul_assoc, hU, d.wittDecomp_gram_X_anisotropic]
  obtain ⟨b, hb⟩ : ∃ b, d.pX ⬝ (mt S g ⬝ d.j0) = b := ⟨_, rfl⟩
  obtain ⟨A, hA⟩ : ∃ A, d.p0 ⬝ (mt S g ⬝ d.j0) = A := ⟨_, rfl⟩
  have hdec : mt S g ⬝ d.j0 = d.jX ⬝ b + d.j0 ⬝ A := by
    have he : (d.jX ⬝ d.pX + d.j0 ⬝ d.p0 + d.jY ⬝ d.pY) ⬝ (mt S g ⬝ d.j0) = (1 : Mx D S.rank S.rank) ⬝ (mt S g ⬝ d.j0) := by rw [d.sum_eq_one]
    simp only [Matrix.add_mul, Matrix.one_mul, Matrix.mul_assoc, hY, hb, hA, Matrix.mul_zero, add_zero] at he
    exact he.symm
  have hAu : adj A * (gA S₀ * A) = gA S₀ := by
    have h1 : adj (mt S g ⬝ d.j0) ⬝ (gA S ⬝ (mt S g ⬝ d.j0)) = gA S₀ := by
      rw [adj_mul, Matrix.mul_assoc, hU, d.gram_00]
    rw [hdec] at h1
    simp only [adj_add, adj_mul, Matrix.add_mul, Matrix.mul_add, Matrix.mul_assoc, cancel₃ d.gram_XX, cancel₃ d.wittDecomp_gram_X_anisotropic,
      cancel₃ d.gram_0X, cancel₃ d.gram_00, Matrix.zero_mul, Matrix.mul_zero, add_zero, zero_add] at h1
    exact h1
  obtain ⟨h, hAh⟩ : ∃ h : GA D S₀, mt S₀ h = A := ⟨ofMat S₀ A hAu, rfl⟩
  have hAi : A ⬝ mt S₀ h⁻¹ = mt S₀ 1 := by rw [← hAh, ← mt_mul, mul_inv_cancel]
  have hi : (d.emb0 h)⁻¹ = d.emb0 h⁻¹ := (map_inv d.emb0 h).symm
  have hm0 : mt S (g * d.emb0 h⁻¹) = mt S g ⬝ mt S (d.emb0 h⁻¹) := mt_mul S _ _
  have he0 : mt S (d.emb0 h⁻¹) ⬝ d.j0 = d.j0 ⬝ mt S₀ h⁻¹ := d.wittDecomp_anisotropicEmbedding_inclAnisotropic h⁻¹
  have heX : mt S (d.emb0 h⁻¹) ⬝ d.jX = d.jX := d.wittDecomp_anisotropicEmbedding_inclX h⁻¹
  have hj : d.j0 ⬝ mt S₀ (1 : GA D S₀) = d.j0 := by rw [mt_one, Matrix.mul_one]
  have hn0' : mt S (g * (d.emb0 h)⁻¹) ⬝ d.j0 = d.jX ⬝ (b ⬝ mt S₀ h⁻¹) + d.j0 := by
    have s1 : mt S (g * (d.emb0 h)⁻¹) ⬝ d.j0 = (mt S g ⬝ d.j0) ⬝ mt S₀ h⁻¹ := by
      rw [hi, hm0, Matrix.mul_assoc, he0, Matrix.mul_assoc]
    have s2 : (d.jX ⬝ b + d.j0 ⬝ A) ⬝ mt S₀ h⁻¹ = d.jX ⬝ (b ⬝ mt S₀ h⁻¹) + d.j0 ⬝ (A ⬝ mt S₀ h⁻¹) :=
      (Matrix.add_mul (d.jX ⬝ b) (d.j0 ⬝ A) (mt S₀ h⁻¹)).trans
        (congrArg₂ (· + ·) (Matrix.mul_assoc d.jX b (mt S₀ h⁻¹)) (Matrix.mul_assoc d.j0 A (mt S₀ h⁻¹)))
    have s3 : d.jX ⬝ (b ⬝ mt S₀ h⁻¹) + d.j0 ⬝ (A ⬝ mt S₀ h⁻¹) = d.jX ⬝ (b ⬝ mt S₀ h⁻¹) + d.j0 :=
      (congrArg (fun M : Mx D S₀.rank S₀.rank => d.jX ⬝ (b ⬝ mt S₀ h⁻¹) + d.j0 ⬝ M) hAi).trans (congrArg (fun M : Mx D S.rank S₀.rank => d.jX ⬝ (b ⬝ mt S₀ h⁻¹) + M) hj)
    exact s1.trans ((congrArg (fun M : Mx D S.rank S₀.rank => M ⬝ mt S₀ h⁻¹) hdec).trans (s2.trans s3))
  have hn0 : mt S (g * (d.emb0 h)⁻¹) ⬝ d.j0 = d.j0 + d.jX ⬝ (b ⬝ mt S₀ h⁻¹) := hn0'.trans (add_comm _ _)
  have hnX' : mt S (g * (d.emb0 h)⁻¹) ⬝ d.jX = d.jX := by
    rw [hi, hm0, Matrix.mul_assoc, heX, hg]
  have hnX : mt S (g * (d.emb0 h)⁻¹) ⬝ d.jX = d.jX ⬝ (1 : GL (Fin ρ) (AE D)).1 := by
    rw [Units.val_one, Matrix.mul_one]; exact hnX'
  have hn : g * (d.emb0 h)⁻¹ ∈ flagN d := d.mem_NFlag one_mem_upperUni hnX hn0
  have hm : g * (d.emb0 h)⁻¹ * d.emb0 h ∈ jacGrp d :=
    mul_mem (Subgroup.mem_sup_left hn) (Subgroup.mem_sup_right ⟨h, rfl⟩)
  rwa [inv_mul_cancel_right] at hm

/- English proof (translation)
Introduce and unpack `g ⟨hX, h0, h1⟩`. Use `set u := uniUnit (blockX d g) h0 h1`. Establish `hl : d.levi u ∈ flagN d` using `d.levi_mem_NFlag (uniUnit_mem _ h0 h1)`. Establish `hf : mt S ((d.levi u)⁻¹ * g) ⬝ d.jX = d.jX`. Rewrite using `[← map_inv, mt_mul, Matrix.mul_assoc, hX, ← Matrix.mul_assoc, levi_jX, Matrix.mul_assoc, show (u⁻¹).1 ⬝ blockX d g = 1 from Units.inv_mul u, Matrix.mul_one]`.

Use `mul_mem (Subgroup.mem_sup_left (T := d.emb0.range) hl) (mem_jacGrp_of_fix d hf)` as an intermediate fact. Rewrite `this` using `[mul_inv_cancel_left]`. Then use the resulting hypothesis.
-/
theorem uniOnX_subset (d : HypDec S S₀ ρ) : uniOnX d ⊆ jacGrp d := by
  rintro g ⟨hX, h0, h1⟩
  set u := uniUnit (blockX d g) h0 h1
  have hl : d.levi u ∈ flagN d := d.levi_mem_NFlag (uniUnit_mem _ h0 h1)
  have hf : mt S ((d.levi u)⁻¹ * g) ⬝ d.jX = d.jX := by
    rw [← map_inv, mt_mul, Matrix.mul_assoc, hX, ← Matrix.mul_assoc, levi_jX, Matrix.mul_assoc,
      show (u⁻¹).1 ⬝ blockX d g = 1 from Units.inv_mul u, Matrix.mul_one]
  have := mul_mem (Subgroup.mem_sup_left (T := d.emb0.range) hl) (mem_jacGrp_of_fix d hf)
  rwa [mul_inv_cancel_left] at this

/- English proof (translation)
Use `Set.Subset.antisymm (fun g hg => ?_) (uniOnX_subset d)` and prove the remaining obligations. Take `⟨u, hu, h⟩` from `jacGrp_le d hg`. Conclude with `mem_uniOnX_of d hu h`.
-/
theorem jacGrp_eq (d : HypDec S S₀ ρ) : (jacGrp d : Set (GA D S)) = uniOnX d := by
  refine Set.Subset.antisymm (fun g hg => ?_) (uniOnX_subset d)
  obtain ⟨u, hu, h⟩ := jacGrp_le d hg
  exact mem_uniOnX_of d hu h

end GlobalTheory.JacClosed

namespace GlobalTheory

/- English proof (translation)
Introduce `D S S₀ ρ d`. Rewrite using `[GlobalTheory.JacClosed.jacGrp_eq]`. Conclude with `GlobalTheory.JacClosed.isClosed_uniOnX d`.
-/
theorem jacGrp_isClosed : ∀ (D : D7) (S S₀ : HSp D) (ρ : ℕ) (d : HypDec S S₀ ρ), IsClosed (jacGrp d : Set (GA D S)) := by
  intro D S S₀ ρ d
  rw [GlobalTheory.JacClosed.jacGrp_eq]
  exact GlobalTheory.JacClosed.isClosed_uniOnX d

end GlobalTheory

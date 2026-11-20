import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.FStarCohPfD

noncomputable section

open ValuativeRel Matrix

namespace Formalism.MainNotions.S.Loc.HermSp.LprU

open Formalism.MainNotions.S.Loc.HermSp.CohU

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
variable {M : Model F E} {V : Type} [AddCommGroup V] [Module E V] {H : HermSp M V}

def GramInvE {ι : Type} [Fintype ι] [DecidableEq ι] (H : HermSp M V) (v : ι → V) : Prop :=
  ∃ N : Matrix ι ι E, N * H.gram v = 1

/- English proof (translation)
Take `⟨N, hN⟩` from `hN`. Establish `hz0 : ∀ y, H.h 0 y = 0` using `fun y => by`. Establish `h1` using `H.h_add_left 0 0 y`. Rewrite `h1` using `[add_zero]`. Conclude with `left_eq_add.mp h1`.

Establish `hsum : ∀ (s : Finset ι) (c : ι → E) (y : V), H.h (∑ a ∈ s, c a • v a) y = ∑ a ∈ s, c a * H.h (v a) y`. Introduce `s c y`. Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty => simp [hz0]`. Consider the case `insert a s ha ih`.

Rewrite using `[Finset.sum_insert ha, Finset.sum_insert ha, H.h_add_left, H.h_smul_left, ih]`. Take `⟨c, rfl⟩` from `(Submodule.mem_span_range_iff_exists_fun E).mp hz`. Establish `hg : H.gram v *ᵥ c = 0`. Use function extensionality and compare the values at `i`. Rewrite using `[Pi.zero_apply, ← h0 i, hsum]`.

Conclude with `Finset.sum_congr rfl fun j _ => mul_comm _ _`. Establish `hc : c = 0`. Establish `h2` using `congrArg (fun u => N *ᵥ u) hg`. Simplify using `only [Matrix.mulVec_mulVec, hN, Matrix.one_mulVec, Matrix.mulVec_zero] at h2`. Conclude with `h2`.

Simplify using `[hc]`.
-/
theorem eqz {ι : Type} [Fintype ι] [DecidableEq ι] {v : ι → V} (hN : GramInvE H v) {z : V}
    (hz : z ∈ Submodule.span E (Set.range v)) (h0 : ∀ i, H.h z (v i) = 0) : z = 0 := by
  obtain ⟨N, hN⟩ := hN
  have hz0 : ∀ y, H.h 0 y = 0 := fun y => by
    have h1 := H.h_add_left 0 0 y
    rw [add_zero] at h1
    exact left_eq_add.mp h1
  have hsum : ∀ (s : Finset ι) (c : ι → E) (y : V),
      H.h (∑ a ∈ s, c a • v a) y = ∑ a ∈ s, c a * H.h (v a) y := by
    intro s c y
    induction s using Finset.induction_on with
    | empty => simp [hz0]
    | insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha, H.h_add_left, H.h_smul_left, ih]
  obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun E).mp hz
  have hg : H.gram v *ᵥ c = 0 := by
    funext i
    rw [Pi.zero_apply, ← h0 i, hsum]
    exact Finset.sum_congr rfl fun j _ => mul_comm _ _
  have hc : c = 0 := by
    have h2 := congrArg (fun u => N *ᵥ u) hg
    simp only [Matrix.mulVec_mulVec, hN, Matrix.one_mulVec, Matrix.mulVec_zero] at h2
    exact h2
  simp [hc]

/- English proof (translation)
Take `⟨N, hN⟩` from `hN`. Establish `hN' : H.gram v * N = 1` using `mul_eq_one_comm.mp hN`. Establish `h0 : ∀ y, H.h 0 y = 0` using `fun y => by`. Establish `h1` using `H.h_add_left 0 0 y`. Rewrite `h1` using `[add_zero]`.

Conclude with `left_eq_add.mp h1`. Establish `hsum : ∀ (s : Finset ι) (c : ι → E) (y : V), H.h (∑ a ∈ s, c a • v a) y = ∑ a ∈ s, c a * H.h (v a) y`. Introduce `s c y`. Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty => simp [h0]`.

Consider the case `insert a s ha ih`. Rewrite using `[Finset.sum_insert ha, Finset.sum_insert ha, H.h_add_left, H.h_smul_left, ih]`. Set `w : ι → E` to `fun i => H.h x (v i)`. Use `⟨N *ᵥ w, fun i => ?_⟩` and prove the remaining obligations. Establish `hsub : ∀ y z : V, H.h (y - z) (v i) = H.h y (v i) - H.h z (v i)` using `fun y z => by`.

Rewrite using `[sub_eq_add_neg, H.h_add_left, ← neg_one_smul E z, H.h_smul_left]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[hsub, hsum]`. Establish `e : ∑ j, (N *ᵥ w) j * H.h (v j) (v i) = (H.gram v *ᵥ (N *ᵥ w)) i` using `Finset.sum_congr rfl fun j _ => mul_comm _ _`. Rewrite using `[e, Matrix.mulVec_mulVec, hN', Matrix.one_mulVec, sub_self]`.
-/
theorem decompE {ι : Type} [Fintype ι] [DecidableEq ι] {v : ι → V} (hN : GramInvE H v) (x : V) :
    ∃ c : ι → E, ∀ i, H.h (x - ∑ j, c j • v j) (v i) = 0 := by
  obtain ⟨N, hN⟩ := hN
  have hN' : H.gram v * N = 1 := mul_eq_one_comm.mp hN
  have h0 : ∀ y, H.h 0 y = 0 := fun y => by
    have h1 := H.h_add_left 0 0 y
    rw [add_zero] at h1
    exact left_eq_add.mp h1
  have hsum : ∀ (s : Finset ι) (c : ι → E) (y : V),
      H.h (∑ a ∈ s, c a • v a) y = ∑ a ∈ s, c a * H.h (v a) y := by
    intro s c y
    induction s using Finset.induction_on with
    | empty => simp [h0]
    | insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha, H.h_add_left, H.h_smul_left, ih]
  let w : ι → E := fun i => H.h x (v i)
  refine ⟨N *ᵥ w, fun i => ?_⟩
  have hsub : ∀ y z : V, H.h (y - z) (v i) = H.h y (v i) - H.h z (v i) := fun y z => by
    rw [sub_eq_add_neg, H.h_add_left, ← neg_one_smul E z, H.h_smul_left]
    ring
  rw [hsub, hsum]
  have e : ∑ j, (N *ᵥ w) j * H.h (v j) (v i) = (H.gram v *ᵥ (N *ᵥ w)) i :=
    Finset.sum_congr rfl fun j _ => mul_comm _ _
  rw [e, Matrix.mulVec_mulVec, hN', Matrix.one_mulVec, sub_self]

/- English proof (translation)
Establish `h0 : ∀ y, H.h 0 y = 0` using `fun y => by`. Establish `h1` using `H.h_add_left 0 0 y`. Rewrite `h1` using `[add_zero]`. Conclude with `left_eq_add.mp h1`. Establish `hsum : ∀ (s : Finset (Fin (r + 1))) (c : (Fin (r + 1)) → E) (y : V), H.h (∑ a ∈ s, c a • f a) y = ∑ a ∈ s, c a * H.h (f a) y`.

Introduce `s c y`. Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty => simp [h0]`. Consider the case `insert a s ha ih`. Rewrite using `[Finset.sum_insert ha, Finset.sum_insert ha, H.h_add_left, H.h_smul_left, ih]`.

Use `set Z := H.Zhat f f' with hZ`. Use `set W := Z.map M.L.cj with hW`. Use `set β : Fin (r + 1) → E := fun b => H.h (∑ a, α a • f a) (f' b) with hβdef`. Establish `hβ : β = Wᵀ *ᵥ α`. Use function extensionality and compare the values at `b`.

Simplify using `only [hβdef]`. Rewrite using `[hsum]`. Conclude with `Finset.sum_congr rfl fun a _ => by`. Rewrite using `[H.h_herm (f' b) (f a)]`. Conclude with `mul_comm _ _`.

Establish `hcr : W.det • α = W.adjugateᵀ *ᵥ β`. Rewrite using `[hβ, Matrix.mulVec_mulVec, Matrix.adjugate_transpose, Matrix.adjugate_mul, Matrix.det_transpose]`. Use `first`. Consider the case `rw [Matrix.smul_mulVec_assoc, Matrix.one_mulVec]`. Consider the case `rw [Matrix.smul_mulVec, Matrix.one_mulVec]`.

Consider the case `(ext a; simp [Matrix.mulVec, dotProduct, Matrix.one_apply])`. Establish `hdet : W.det = M.L.cj Z.det` using `by first`. Consider the case `exact (RingHom.map_det M.L.cj Z).symm`. Consider the case `exact (RingHom.map_det (M.L.cj : E →+* E) Z).symm`. Establish `hadj : W.adjugate = Z.adjugate.map M.L.cj` using `by first`.

Consider the case `(have h := RingHom.map_adjugate (M.L.cj : E →+* E) Z`. Simplify using `only [RingHom.mapMatrix_apply, RingHom.coe_coe] at h`. Conclude with `h.symm)`. Establish `hcomp : ∀ a, M.L.cj Z.det * α a = β (Fin.last r) * M.L.cj (Z.adjugate (Fin.last r) a)`. Introduce `a`.

Establish `h1` using `congrFun hcr a`. Rewrite `h1` using `[Pi.smul_apply, smul_eq_mul, hdet]`. Rewrite using `[h1, Matrix.mulVec, dotProduct, Finset.sum_eq_single (Fin.last r)]`. Rewrite using `[Matrix.transpose_apply, hadj, Matrix.map_apply]`. Expand and normalize the polynomial expressions, which then agree.

Introduce `b _ hb`. Establish `hb0 : β b = 0` using `hy b hb`. Rewrite using `[hb0, mul_zero]`. Introduce `h`. Conclude with `absurd (Finset.mem_univ _) h`.

Unfold `Formalism.MainNotions.S.Loc.HermSp.om`. Rewrite using `[Finset.smul_sum, Finset.smul_sum]`. Use `Finset.sum_congr rfl fun a _ => ?_` and prove the remaining obligations. Rewrite using `[smul_smul, smul_smul, hcomp a]`.
-/
theorem y_eq_om {r : ℕ} (f f' : Fin (r + 1) → V) (α : Fin (r + 1) → E)
    (hy : ∀ b, b ≠ Fin.last r → H.h (∑ a, α a • f a) (f' b) = 0) :
    M.L.cj (H.Zhat f f').det • ∑ a, α a • f a = H.h (∑ a, α a • f a) (f' (Fin.last r)) • H.om f f' := by
  have h0 : ∀ y, H.h 0 y = 0 := fun y => by
    have h1 := H.h_add_left 0 0 y
    rw [add_zero] at h1
    exact left_eq_add.mp h1
  have hsum : ∀ (s : Finset (Fin (r + 1))) (c : (Fin (r + 1)) → E) (y : V),
      H.h (∑ a ∈ s, c a • f a) y = ∑ a ∈ s, c a * H.h (f a) y := by
    intro s c y
    induction s using Finset.induction_on with
    | empty => simp [h0]
    | insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha, H.h_add_left, H.h_smul_left, ih]
  set Z := H.Zhat f f' with hZ
  set W := Z.map M.L.cj with hW
  set β : Fin (r + 1) → E := fun b => H.h (∑ a, α a • f a) (f' b) with hβdef

  have hβ : β = Wᵀ *ᵥ α := by
    funext b
    simp only [hβdef]
    rw [hsum]
    exact Finset.sum_congr rfl fun a _ => by
      rw [H.h_herm (f' b) (f a)]
      exact mul_comm _ _

  have hcr : W.det • α = W.adjugateᵀ *ᵥ β := by
    rw [hβ, Matrix.mulVec_mulVec, Matrix.adjugate_transpose, Matrix.adjugate_mul, Matrix.det_transpose]
    first
      | rw [Matrix.smul_mulVec_assoc, Matrix.one_mulVec]
      | rw [Matrix.smul_mulVec, Matrix.one_mulVec]
      | (ext a; simp [Matrix.mulVec, dotProduct, Matrix.one_apply])
  have hdet : W.det = M.L.cj Z.det := by
    first
      | exact (RingHom.map_det M.L.cj Z).symm
      | exact (RingHom.map_det (M.L.cj : E →+* E) Z).symm
  have hadj : W.adjugate = Z.adjugate.map M.L.cj := by
    first
      | (have h := RingHom.map_adjugate (M.L.cj : E →+* E) Z
         simp only [RingHom.mapMatrix_apply, RingHom.coe_coe] at h
         exact h.symm)
  have hcomp : ∀ a, M.L.cj Z.det * α a = β (Fin.last r) * M.L.cj (Z.adjugate (Fin.last r) a) := by
    intro a
    have h1 := congrFun hcr a
    rw [Pi.smul_apply, smul_eq_mul, hdet] at h1
    rw [h1, Matrix.mulVec, dotProduct, Finset.sum_eq_single (Fin.last r)]
    · rw [Matrix.transpose_apply, hadj, Matrix.map_apply]
      ring
    · intro b _ hb
      have hb0 : β b = 0 := hy b hb
      rw [hb0, mul_zero]
    · intro h
      exact absurd (Finset.mem_univ _) h
  unfold Formalism.MainNotions.S.Loc.HermSp.om
  rw [Finset.smul_sum, Finset.smul_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [smul_smul, smul_smul, hcomp a]

end Formalism.MainNotions.S.Loc.HermSp.LprU

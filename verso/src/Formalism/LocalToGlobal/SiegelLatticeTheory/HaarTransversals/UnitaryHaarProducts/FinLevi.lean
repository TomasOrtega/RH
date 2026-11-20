import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.HermitianETransportInvariant
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.RightInvOfLattice

noncomputable section

open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.PoincareInHH.Cut
open scoped TensorProduct
open Matrix

namespace Formalism.L2.SG.Pf.FinLeviPf

attribute [local instance] Formalism.BasicNotions.Host.cmStar

open Formalism.L2.SG Formalism.L2.SG.PoincareInHH Formalism.L2.SG.Pf

section Form

variable {D : D7} (X : HidaSetting D) (u : D.what₂.Word)

abbrev eA : Fin D.R.rS → VA X.B.I := fun a => incl X.B.I (X.eR a)

abbrev fA : Fin D.R.rS → VA X.B.I := fun a => incl X.B.I (X.fR a)

abbrev zA : VA X.B.I := incl X.B.I (X.zR u)

def zinv : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F :=
  Formalism.UG.inclE (F := X.B.I.F) (Af X.B.I.F) ((Level.hE X (X.zR u) (X.zR u))⁻¹)

/- English proof (translation)
Rewrite using `[unitaryCongruence.hA_incl, zinv, ← map_mul]`. Rewrite using `[show Formalism.UG.hform (starRingEnd X.B.I.E) X.B.I.J (X.zR u) (X.zR u) = Level.hE X (X.zR u) (X.zR u) from rfl, inv_mul_cancel₀ (Level.hE_z_z_ne X u), map_one]`.
-/
theorem hermitian_z_normalized : zinv X u * hA X.B.I (zA X u) (zA X u) = 1 := by
  rw [unitaryCongruence.hA_incl, zinv, ← map_mul]
  rw [show Formalism.UG.hform (starRingEnd X.B.I.E) X.B.I.J (X.zR u) (X.zR u) = Level.hE X (X.zR u) (X.zR u) from rfl,
    inv_mul_cancel₀ (Level.hE_z_z_ne X u), map_one]

/- English proof (translation)
Establish `h` using `Level.hE_e_e X a b`. Unfold `Level.hE at h`. Rewrite using `[unitaryCongruence.hA_incl, h, map_zero]`.
-/
theorem hA_e_e (a b : Fin D.R.rS) : hA X.B.I (eA X a) (eA X b) = 0 := by
  have h := Level.hE_e_e X a b; unfold Level.hE at h; rw [unitaryCongruence.hA_incl, h, map_zero]

/- English proof (translation)
Establish `h` using `Level.hE_f_f X a b`. Unfold `Level.hE at h`. Rewrite using `[unitaryCongruence.hA_incl, h, map_zero]`.
-/
theorem hA_f_f (a b : Fin D.R.rS) : hA X.B.I (fA X a) (fA X b) = 0 := by
  have h := Level.hE_f_f X a b; unfold Level.hE at h; rw [unitaryCongruence.hA_incl, h, map_zero]

/- English proof (translation)
Apply the tactic sequence `have h := Level.hE_e_f X a b; unfold Level.hE at h; rw [unitaryCongruence.hA_incl, h]; split_ifs <;> simp`.
-/
theorem hA_e_f (a b : Fin D.R.rS) : hA X.B.I (eA X a) (fA X b) = if a = b then 1 else 0 := by
  have h := Level.hE_e_f X a b; unfold Level.hE at h; rw [unitaryCongruence.hA_incl, h]; split_ifs <;> simp

/- English proof (translation)
Apply the tactic sequence `have h := Level.hE_f_e X a b; unfold Level.hE at h; rw [unitaryCongruence.hA_incl, h]; split_ifs <;> simp`.
-/
theorem hA_f_e (a b : Fin D.R.rS) : hA X.B.I (fA X a) (eA X b) = if b = a then 1 else 0 := by
  have h := Level.hE_f_e X a b; unfold Level.hE at h; rw [unitaryCongruence.hA_incl, h]; split_ifs <;> simp

/- English proof (translation)
Establish `h` using `Level.hermitian_e_z_zero X u a`. Unfold `Level.hE at h`. Rewrite using `[unitaryCongruence.hA_incl, h, map_zero]`.
-/
theorem adelicHermitian_hyperbolicE_anisotropic_eq_zero (a : Fin D.R.rS) : hA X.B.I (eA X a) (zA X u) = 0 := by
  have h := Level.hermitian_e_z_zero X u a; unfold Level.hE at h; rw [unitaryCongruence.hA_incl, h, map_zero]

/- English proof (translation)
Establish `h` using `Level.hermitian_f_z_zero X u a`. Unfold `Level.hE at h`. Rewrite using `[unitaryCongruence.hA_incl, h, map_zero]`.
-/
theorem adelicHermitian_hyperbolicF_anisotropic_eq_zero (a : Fin D.R.rS) : hA X.B.I (fA X a) (zA X u) = 0 := by
  have h := Level.hermitian_f_z_zero X u a; unfold Level.hE at h; rw [unitaryCongruence.hA_incl, h, map_zero]

/- English proof (translation)
Establish `h` using `Level.hE_z_e X u a`. Unfold `Level.hE at h`. Rewrite using `[unitaryCongruence.hA_incl, h, map_zero]`.
-/
theorem hA_z_e (a : Fin D.R.rS) : hA X.B.I (zA X u) (eA X a) = 0 := by
  have h := Level.hE_z_e X u a; unfold Level.hE at h; rw [unitaryCongruence.hA_incl, h, map_zero]

/- English proof (translation)
Establish `h` using `Level.hE_z_f X u a`. Unfold `Level.hE at h`. Rewrite using `[unitaryCongruence.hA_incl, h, map_zero]`.
-/
theorem hA_z_f (a : Fin D.R.rS) : hA X.B.I (zA X u) (fA X a) = 0 := by
  have h := Level.hE_z_f X u a; unfold Level.hE at h; rw [unitaryCongruence.hA_incl, h, map_zero]

/- English proof (translation)
Simplify using `only [hA, Formalism.UG.hform, Pi.sub_apply, mul_sub, Finset.sum_sub_distrib]`.
-/
theorem hA_sub_right (x y y' : VA X.B.I) : hA X.B.I x (y - y') = hA X.B.I x y - hA X.B.I x y' := by
  simp only [hA, Formalism.UG.hform, Pi.sub_apply, mul_sub, Finset.sum_sub_distrib]

/- English proof (translation)
Simplify using `[hA, Formalism.UG.hform]`.
-/
theorem hA_zero_left (y : VA X.B.I) : hA X.B.I 0 y = 0 := by
  simp [hA, Formalism.UG.hform]

/- English proof (translation)
Simplify using `only [hA, Formalism.UG.hform, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]`. Use `Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Expand and normalize the polynomial expressions, which then agree.
-/
private theorem hA_smul_right_lemma (x y : VA X.B.I) (c : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) :
    hA X.B.I x (c • y) = c * hA X.B.I x y := by
  simp only [hA, Formalism.UG.hform, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

/- English proof (translation)
Simplify using `only [hA, Formalism.UG.hform, Pi.add_apply, mul_add, Finset.sum_add_distrib]`.
-/
private theorem hA_add_right_lemma_2 (x y y' : VA X.B.I) : hA X.B.I x (y + y') = hA X.B.I x y + hA X.B.I x y' := by
  simp only [hA, Formalism.UG.hform, Pi.add_apply, mul_add, Finset.sum_add_distrib]

/- English proof (translation)
Simplify using `[hA, Formalism.UG.hform]`.
-/
private theorem hA_zero_right_lemma_7 (x : VA X.B.I) : hA X.B.I x 0 = 0 := by
  simp [hA, Formalism.UG.hform]

/- English proof (translation)
Use `Finset.induction_on s ?_ ?_` and prove the remaining obligations. Simplify using `only [Finset.sum_empty, hA_zero_right_lemma_7]`. Introduce `a s ha ih`. Rewrite using `[Finset.sum_insert ha, Finset.sum_insert ha, hA_add_right_lemma_2, ih]`.
-/
private theorem hA_sum_right_lemma_3 {ι : Type*} (s : Finset ι) (x : VA X.B.I) (f : ι → VA X.B.I) :
    hA X.B.I x (∑ i ∈ s, f i) = ∑ i ∈ s, hA X.B.I x (f i) := by
  classical
  refine Finset.induction_on s ?_ ?_
  · simp only [Finset.sum_empty, hA_zero_right_lemma_7]
  · intro a s ha ih
    rw [Finset.sum_insert ha, Finset.sum_insert ha, hA_add_right_lemma_2, ih]

/- English proof (translation)
Simplify using `only [hA, Formalism.UG.hform, Pi.add_apply, map_add, add_mul, Finset.sum_add_distrib]`.
-/
private theorem hA_add_left_lemma_4 (x x' y : VA X.B.I) : hA X.B.I (x + x') y = hA X.B.I x y + hA X.B.I x' y := by
  simp only [hA, Formalism.UG.hform, Pi.add_apply, map_add, add_mul, Finset.sum_add_distrib]

/- English proof (translation)
Use `Finset.induction_on s ?_ ?_` and prove the remaining obligations. Simplify using `only [Finset.sum_empty, hA_zero_left]`. Introduce `a s ha ih`. Rewrite using `[Finset.sum_insert ha, Finset.sum_insert ha, hA_add_left_lemma_4, ih]`.
-/
private theorem hA_sum_left_lemma_5 {ι : Type*} (s : Finset ι) (f : ι → VA X.B.I) (y : VA X.B.I) :
    hA X.B.I (∑ i ∈ s, f i) y = ∑ i ∈ s, hA X.B.I (f i) y := by
  classical
  refine Finset.induction_on s ?_ ?_
  · simp only [Finset.sum_empty, hA_zero_left]
  · intro a s ha ih
    rw [Finset.sum_insert ha, Finset.sum_insert ha, hA_add_left_lemma_4, ih]

/- English proof (translation)
Simplify using `only [hA, Formalism.UG.hform, Pi.smul_apply, smul_eq_mul, map_mul, mul_assoc] at h ⊢`. Simplify using `only [← Finset.mul_sum] at h ⊢`. Use `first`. Consider the case `rw [h, mul_zero]`. Consider the case `simp [h]`.
-/
private theorem hA_smul_left_zero_lemma_6 (c : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) (x y : VA X.B.I)
    (h : hA X.B.I x y = 0) : hA X.B.I (c • x) y = 0 := by
  simp only [hA, Formalism.UG.hform, Pi.smul_apply, smul_eq_mul, map_mul, mul_assoc] at h ⊢
  simp only [← Finset.mul_sum] at h ⊢
  first
  | rw [h, mul_zero]
  | simp [h]

/- English proof (translation)
Rewrite using `[unitaryCongruence.hA_symm, h, map_zero]`.
-/
theorem hA_symm_zero {x y : VA X.B.I} (h : hA X.B.I x y = 0) : hA X.B.I y x = 0 := by
  rw [unitaryCongruence.hA_symm, h, map_zero]

def PWl : VA X.B.I →ₗ[X.B.I.E ⊗[X.B.I.F] Af X.B.I.F] VA X.B.I :=
  LinearMap.id - ∑ a, (unitaryCongruence.hL X.B.I (fA X a)).smulRight (eA X a) -
    ∑ a, (unitaryCongruence.hL X.B.I (eA X a)).smulRight (fA X a) -
    (zinv X u • unitaryCongruence.hL X.B.I (zA X u)).smulRight (zA X u)

/- English proof (translation)
Use `first`. Consider the case `rfl`. Consider the case `(simp only [PWl, LinearMap.sub_apply, LinearMap.id_apply, LinearMap.coeFn_sum, Finset.sum_apply, LinearMap.smulRight_apply, LinearMap.smul_apply, smul_eq_mul]; rfl)`. Consider the case `simp [PWl, unitaryCongruence.hL, LinearMap.smulRight_apply]`.
-/
theorem PWl_apply (y : VA X.B.I) : PWl X u y = y - ∑ a, hA X.B.I (fA X a) y • eA X a -
    ∑ a, hA X.B.I (eA X a) y • fA X a - (zinv X u * hA X.B.I (zA X u) y) • zA X u := by
  first
  | rfl
  | (simp only [PWl, LinearMap.sub_apply, LinearMap.id_apply, LinearMap.coeFn_sum, Finset.sum_apply,
      LinearMap.smulRight_apply, LinearMap.smul_apply, smul_eq_mul]; rfl)
  | simp [PWl, unitaryCongruence.hL, LinearMap.smulRight_apply]

/- English proof (translation)
Rewrite using `[PWl_apply]`. Simplify using `[hA_sub_right, hA_sum_right_lemma_3, hA_smul_right_lemma, hA_e_e, hA_e_f, adelicHermitian_hyperbolicE_anisotropic_eq_zero]`.
-/
theorem hA_e_PW (a : Fin D.R.rS) (y : VA X.B.I) : hA X.B.I (eA X a) (PWl X u y) = 0 := by
  rw [PWl_apply]
  simp [hA_sub_right, hA_sum_right_lemma_3, hA_smul_right_lemma, hA_e_e, hA_e_f, adelicHermitian_hyperbolicE_anisotropic_eq_zero]

/- English proof (translation)
Rewrite using `[PWl_apply]`. Simplify using `[hA_sub_right, hA_sum_right_lemma_3, hA_smul_right_lemma, hA_f_f, hA_f_e, adelicHermitian_hyperbolicF_anisotropic_eq_zero]`.
-/
theorem hA_f_PW (a : Fin D.R.rS) (y : VA X.B.I) : hA X.B.I (fA X a) (PWl X u y) = 0 := by
  rw [PWl_apply]
  simp [hA_sub_right, hA_sum_right_lemma_3, hA_smul_right_lemma, hA_f_f, hA_f_e, adelicHermitian_hyperbolicF_anisotropic_eq_zero]

/- English proof (translation)
Rewrite using `[PWl_apply]`. Simplify using `only [hA_sub_right, hA_sum_right_lemma_3, hA_smul_right_lemma, hA_z_e, hA_z_f, mul_zero, Finset.sum_const_zero, sub_zero]`. Take the linear combination `(-(hA X.B.I (zA X u) y)) * hermitian_z_normalized X u`.
-/
theorem hA_z_PW (y : VA X.B.I) : hA X.B.I (zA X u) (PWl X u y) = 0 := by
  rw [PWl_apply]
  simp only [hA_sub_right, hA_sum_right_lemma_3, hA_smul_right_lemma, hA_z_e, hA_z_f, mul_zero, Finset.sum_const_zero,
    sub_zero]
  linear_combination (-(hA X.B.I (zA X u) y)) * hermitian_z_normalized X u

/- English proof (translation)
Rewrite using `[PWl_apply]`. Simplify using `[he, hf, hz]`.
-/
theorem PW_fix (w : VA X.B.I) (he : ∀ a, hA X.B.I (eA X a) w = 0) (hf : ∀ a, hA X.B.I (fA X a) w = 0)
    (hz : hA X.B.I (zA X u) w = 0) : PWl X u w = w := by
  rw [PWl_apply]
  simp [he, hf, hz]

/- English proof (translation)
Conclude with `PW_fix X u (PWl X u y) (fun a => hA_e_PW X u a y) (fun a => hA_f_PW X u a y) (hA_z_PW X u y)`.
-/
theorem PW_idem (y : VA X.B.I) : PWl X u (PWl X u y) = PWl X u y := by
  exact PW_fix X u (PWl X u y) (fun a => hA_e_PW X u a y) (fun a => hA_f_PW X u a y) (hA_z_PW X u y)

/- English proof (translation)
Rewrite using `[map_sub, PW_idem X u y, sub_self]`.
-/
theorem PW_sub_self (y : VA X.B.I) : PWl X u (y - PWl X u y) = 0 := by
  rw [map_sub, PW_idem X u y, sub_self]

/- English proof (translation)
Rewrite using `[PWl_apply]`. Simplify using `[hA_f_e, hA_e_e, hA_z_e]`.
-/
theorem PW_e (b : Fin D.R.rS) : PWl X u (eA X b) = 0 := by
  rw [PWl_apply]
  simp [hA_f_e, hA_e_e, hA_z_e]

/- English proof (translation)
Rewrite using `[PWl_apply]`. Simplify using `[hA_f_f, hA_e_f, hA_z_f]`.
-/
theorem PW_f (b : Fin D.R.rS) : PWl X u (fA X b) = 0 := by
  rw [PWl_apply]
  simp [hA_f_f, hA_e_f, hA_z_f]

/- English proof (translation)
Rewrite using `[PWl_apply]`. Simplify using `[adelicHermitian_hyperbolicF_anisotropic_eq_zero, adelicHermitian_hyperbolicE_anisotropic_eq_zero, hermitian_z_normalized]`.
-/
theorem levi_projection_z_zero : PWl X u (zA X u) = 0 := by
  rw [PWl_apply]
  simp [adelicHermitian_hyperbolicF_anisotropic_eq_zero, adelicHermitian_hyperbolicE_anisotropic_eq_zero, hermitian_z_normalized]

/- English proof (translation)
Use `first`. Consider the case `(induction hs using Submodule.span_induction with`. Consider the case `mem x hx => obtain ⟨a, rfl⟩ := hx`. Conclude with `PW_e X u a`. Consider the case `zero => exact map_zero _`.

Consider the case `add x y _ _ hx hy => rw [map_add, hx, hy, add_zero]`. Consider the case `smul c x _ hx => rw [map_smul, hx, smul_zero])`. Consider the case `(refine Submodule.span_induction hs ?_ ?_ ?_ ?_`. Introduce and unpack `x ⟨a, rfl⟩`. Conclude with `PW_e X u a`.

Conclude with `map_zero _`. Introduce `x y hx hy`. Rewrite using `[map_add, hx, hy, add_zero]`. Introduce `c x hx`. Rewrite using `[map_smul, hx, smul_zero])`.
-/
theorem PW_span (s : VA X.B.I)
    (hs : s ∈ Submodule.span (X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) (Set.range (eA X))) : PWl X u s = 0 := by
  first
  | (induction hs using Submodule.span_induction with
      | mem x hx => obtain ⟨a, rfl⟩ := hx; exact PW_e X u a
      | zero => exact map_zero _
      | add x y _ _ hx hy => rw [map_add, hx, hy, add_zero]
      | smul c x _ hx => rw [map_smul, hx, smul_zero])
  | (refine Submodule.span_induction hs ?_ ?_ ?_ ?_
      · rintro x ⟨a, rfl⟩
        exact PW_e X u a
      · exact map_zero _
      · intro x y hx hy
        rw [map_add, hx, hy, add_zero]
      · intro c x hx
        rw [map_smul, hx, smul_zero])

/- English proof (translation)
Rewrite using `[PWl_apply]`. Normalize the expressions using the abelian group laws.
-/
theorem sub_PW (y : VA X.B.I) : y - PWl X u y = ∑ a, hA X.B.I (fA X a) y • eA X a +
    ∑ a, hA X.B.I (eA X a) y • fA X a + (zinv X u * hA X.B.I (zA X u) y) • zA X u := by
  rw [PWl_apply]
  abel

/- English proof (translation)
Establish `hpe : ∀ a, hA X.B.I p (eA X a) = 0` using `fun a => hA_symm_zero X (he a)`. Establish `hpf : ∀ a, hA X.B.I p (fA X a) = 0` using `fun a => hA_symm_zero X (hf a)`. Establish `hpz : hA X.B.I p (zA X u) = 0` using `hA_symm_zero X hz`. Rewrite using `[sub_PW]`. Prove the components needed by the constructor for the conclusion.

Simplify using `only [hA_add_left_lemma_4, hA_sum_left_lemma_5, hA_smul_left_zero_lemma_6, he, hf, hz, Finset.sum_const_zero, add_zero]`. Simplify using `only [hA_add_right_lemma_2, hA_sum_right_lemma_3, hA_smul_right_lemma, hpe, hpf, hpz, mul_zero, Finset.sum_const_zero, add_zero]`.
-/
theorem hA_perp_sub (p y : VA X.B.I) (he : ∀ a, hA X.B.I (eA X a) p = 0)
    (hf : ∀ a, hA X.B.I (fA X a) p = 0) (hz : hA X.B.I (zA X u) p = 0) :
    hA X.B.I (y - PWl X u y) p = 0 ∧ hA X.B.I p (y - PWl X u y) = 0 := by
  have hpe : ∀ a, hA X.B.I p (eA X a) = 0 := fun a => hA_symm_zero X (he a)
  have hpf : ∀ a, hA X.B.I p (fA X a) = 0 := fun a => hA_symm_zero X (hf a)
  have hpz : hA X.B.I p (zA X u) = 0 := hA_symm_zero X hz
  rw [sub_PW]
  constructor
  · simp only [hA_add_left_lemma_4, hA_sum_left_lemma_5, hA_smul_left_zero_lemma_6, he, hf, hz, Finset.sum_const_zero, add_zero]
  · simp only [hA_add_right_lemma_2, hA_sum_right_lemma_3, hA_smul_right_lemma, hpe, hpf, hpz, mul_zero, Finset.sum_const_zero,
      add_zero]

/- English proof (translation)
Use `first`. Consider the case `(induction hs using Submodule.span_induction with`. Consider the case `mem x hx => obtain ⟨a, rfl⟩ := hx`. Conclude with `hw a`. Consider the case `zero => exact hA_zero_left X w`.

Consider the case `add x y _ _ hx hy => rw [hA_add_left_lemma_4, hx, hy, add_zero]`. Consider the case `smul c x _ hx => exact hA_smul_left_zero_lemma_6 X c x w hx)`. Consider the case `(refine Submodule.span_induction hs ?_ ?_ ?_ ?_`. Introduce and unpack `x ⟨a, rfl⟩`. Conclude with `hw a`.

Conclude with `hA_zero_left X w`. Introduce `x y hx hy`. Rewrite using `[hA_add_left_lemma_4, hx, hy, add_zero]`. Introduce `c x hx`. Conclude with `hA_smul_left_zero_lemma_6 X c x w hx)`.
-/
theorem hA_span_left (s w : VA X.B.I)
    (hs : s ∈ Submodule.span (X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) (Set.range (eA X)))
    (hw : ∀ a, hA X.B.I (eA X a) w = 0) : hA X.B.I s w = 0 := by
  first
  | (induction hs using Submodule.span_induction with
      | mem x hx => obtain ⟨a, rfl⟩ := hx; exact hw a
      | zero => exact hA_zero_left X w
      | add x y _ _ hx hy => rw [hA_add_left_lemma_4, hx, hy, add_zero]
      | smul c x _ hx => exact hA_smul_left_zero_lemma_6 X c x w hx)
  | (refine Submodule.span_induction hs ?_ ?_ ?_ ?_
      · rintro x ⟨a, rfl⟩
        exact hw a
      · exact hA_zero_left X w
      · intro x y hx hy
        rw [hA_add_left_lemma_4, hx, hy, add_zero]
      · intro c x hx
        exact hA_smul_left_zero_lemma_6 X c x w hx)

/- English proof (translation)
Use `first`. Consider the case `(induction hs using Submodule.span_induction with`. Consider the case `mem y hy => obtain ⟨a, rfl⟩ := hy`. Conclude with `hx a`. Consider the case `zero => exact hA_zero_right_lemma_7 X x`.

Consider the case `add y z _ _ hy hz => rw [hA_add_right_lemma_2, hy, hz, add_zero]`. Consider the case `smul c y _ hy => rw [hA_smul_right_lemma, hy, mul_zero])`. Consider the case `(refine Submodule.span_induction hs ?_ ?_ ?_ ?_`. Introduce and unpack `y ⟨a, rfl⟩`. Conclude with `hx a`.

Conclude with `hA_zero_right_lemma_7 X x`. Introduce `y z hy hz`. Rewrite using `[hA_add_right_lemma_2, hy, hz, add_zero]`. Introduce `c y hy`. Rewrite using `[hA_smul_right_lemma, hy, mul_zero])`.
-/
theorem hA_span_right (x s : VA X.B.I)
    (hs : s ∈ Submodule.span (X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) (Set.range (eA X)))
    (hx : ∀ a, hA X.B.I x (eA X a) = 0) : hA X.B.I x s = 0 := by
  first
  | (induction hs using Submodule.span_induction with
      | mem y hy => obtain ⟨a, rfl⟩ := hy; exact hx a
      | zero => exact hA_zero_right_lemma_7 X x
      | add y z _ _ hy hz => rw [hA_add_right_lemma_2, hy, hz, add_zero]
      | smul c y _ hy => rw [hA_smul_right_lemma, hy, mul_zero])
  | (refine Submodule.span_induction hs ?_ ?_ ?_ ?_
      · rintro y ⟨a, rfl⟩
        exact hx a
      · exact hA_zero_right_lemma_7 X x
      · intro y z hy hz
        rw [hA_add_right_lemma_2, hy, hz, add_zero]
      · intro c y hy
        rw [hA_smul_right_lemma, hy, mul_zero])

/- English proof (translation)
Conclude with `Submodule.subset_span ⟨a, rfl⟩`.
-/
theorem e_mem_span (a : Fin D.R.rS) :
    eA X a ∈ Submodule.span (X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) (Set.range (eA X)) := by
  exact Submodule.subset_span ⟨a, rfl⟩

/- English proof (translation)
Establish `h1` using `(hA_perp_sub X u (PWl X u y) y' (fun a => hA_e_PW X u a y) (fun a => hA_f_PW X u a y) (hA_z_PW X u y)).2`. Establish `h2` using `(hA_perp_sub X u (PWl X u y') y (fun a => hA_e_PW X u a y') (fun a => hA_f_PW X u a y') (hA_z_PW X u y')).1`. Establish `hy : y = PWl X u y + (y - PWl X u y)` using `by abel`. Establish `hy' : y' = PWl X u y' + (y' - PWl X u y')` using `by abel`. Use `conv_lhs => rw [hy, hy']`.

Simplify using `only [hA_add_left_lemma_4, hA_add_right_lemma_2, h1, h2, add_zero, zero_add]`.
-/
theorem hA_sub_PW_self (y y' : VA X.B.I) :
    hA X.B.I y y' = hA X.B.I (PWl X u y) (PWl X u y') + hA X.B.I (y - PWl X u y) (y' - PWl X u y') := by
  have h1 := (hA_perp_sub X u (PWl X u y) y' (fun a => hA_e_PW X u a y) (fun a => hA_f_PW X u a y)
    (hA_z_PW X u y)).2
  have h2 := (hA_perp_sub X u (PWl X u y') y (fun a => hA_e_PW X u a y') (fun a => hA_f_PW X u a y')
    (hA_z_PW X u y')).1
  have hy : y = PWl X u y + (y - PWl X u y) := by abel
  have hy' : y' = PWl X u y' + (y' - PWl X u y') := by abel
  conv_lhs => rw [hy, hy']
  simp only [hA_add_left_lemma_4, hA_add_right_lemma_2, h1, h2, add_zero, zero_add]

/- English proof (translation)
Establish `hf : ∀ a b : VA X.B.I, hA X.B.I a b = (fun i => (sigA X.B.I) (a i)) ⬝ᵥ (X.B.I.J.map (Formalism.UG.inclE (F` using `X.B.I.F) (Af X.B.I.F)) *ᵥ b) := by`. Introduce `a b`. Apply the tactic sequence `simp only [hA, Formalism.UG.hform, dotProduct, Matrix.mulVec, Finset.mul_sum, mul_assoc] <;> rfl`. Use extensionality with `k l`. Establish `h1` using `hM (Pi.single k (1 : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) : Fin X.B.I.n → X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) (Pi.single l (1 : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) : Fin X.B.I.n → X.B.I.E ⊗[X.B.I.F] Af X.B.I.F)`.

Rewrite `h1` using `[hf, hf]`. Establish `hσ : (fun i => (sigA X.B.I) ((M *ᵥ (Pi.single k (1 : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) : Fin X.B.I.n → X.B.I.E ⊗[X.B.I.F] Af X.B.I.F)) i)) = (M.map (sigA X.B.I)) *ᵥ (fun i => (sigA X.B.I) ((Pi.single k (1 : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) : Fin X.B.I.n → X.B.I.E ⊗[X.B.I.F] Af X.B.I.F …`. Use function extensionality and compare the values at `i`. Conclude with `RingHom.map_mulVec _ _ _ _`. Rewrite `h1` using `[hσ, ← Matrix.vecMul_transpose, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, show (M.map (sigA X.B.I))ᵀ = Formalism.UG.cT (sigA X.B.I) M from rfl]`.

Establish `hs : (fun i => (sigA X.B.I) ((Pi.single k (1 : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) : Fin X.B.I.n → X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) i)) = (Pi.single k (1 : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) : Fin X.B.I.n → X.B.I.E ⊗[X.B.I.F] Af X.B.I.F)`. Use function extensionality and compare the values at `i`. Distinguish the cases in `hi : i = k`. Substitute `hi` using the available equality. Simplify using the standard rewrite rules.

Simplify using `[Pi.single_apply, hi]`. Rewrite `h1` using `[hs]`. Simplify `h1` using `[Matrix.mulVec, dotProduct, Pi.single_apply]`.
-/
theorem unit_of_formA (M : Matrix (Fin X.B.I.n) (Fin X.B.I.n) (X.B.I.E ⊗[X.B.I.F] Af X.B.I.F))
    (hM : ∀ x y, hA X.B.I (M *ᵥ x) (M *ᵥ y) = hA X.B.I x y) :
    Formalism.UG.cT (sigA X.B.I) M * X.B.I.J.map (Formalism.UG.inclE (F := X.B.I.F) (Af X.B.I.F)) * M =
      X.B.I.J.map (Formalism.UG.inclE (F := X.B.I.F) (Af X.B.I.F)) := by
  have hf : ∀ a b : VA X.B.I, hA X.B.I a b = (fun i => (sigA X.B.I) (a i)) ⬝ᵥ (X.B.I.J.map (Formalism.UG.inclE (F := X.B.I.F) (Af X.B.I.F)) *ᵥ b) := by
    intro a b
    simp only [hA, Formalism.UG.hform, dotProduct, Matrix.mulVec, Finset.mul_sum, mul_assoc] <;> rfl
  ext k l
  have h1 := hM (Pi.single k (1 : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) : Fin X.B.I.n → X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) (Pi.single l (1 : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) : Fin X.B.I.n → X.B.I.E ⊗[X.B.I.F] Af X.B.I.F)
  rw [hf, hf] at h1
  have hσ : (fun i => (sigA X.B.I) ((M *ᵥ (Pi.single k (1 : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) : Fin X.B.I.n → X.B.I.E ⊗[X.B.I.F] Af X.B.I.F)) i)) =
      (M.map (sigA X.B.I)) *ᵥ (fun i => (sigA X.B.I) ((Pi.single k (1 : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) : Fin X.B.I.n → X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) i)) := by
    funext i
    exact RingHom.map_mulVec _ _ _ _
  rw [hσ, ← Matrix.vecMul_transpose, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec,
    show (M.map (sigA X.B.I))ᵀ = Formalism.UG.cT (sigA X.B.I) M from rfl] at h1
  have hs : (fun i => (sigA X.B.I) ((Pi.single k (1 : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) : Fin X.B.I.n → X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) i)) =
      (Pi.single k (1 : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) : Fin X.B.I.n → X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) := by
    funext i
    by_cases hi : i = k
    · subst hi; simp
    · simp [Pi.single_apply, hi]
  rw [hs] at h1
  simpa [Matrix.mulVec, dotProduct, Pi.single_apply] using h1

end Form

section Levi

variable {D : D7} {X : HidaSetting D} {u : D.what₂.Word}

structure SA (G G' : Matrix (Fin X.B.I.n) (Fin X.B.I.n) (X.B.I.E ⊗[X.B.I.F] Af X.B.I.F)) : Prop where
  unit : Formalism.UG.cT (sigA X.B.I) G * X.B.I.J.map (Formalism.UG.inclE (F := X.B.I.F) (Af X.B.I.F)) * G =
    X.B.I.J.map (Formalism.UG.inclE (F := X.B.I.F) (Af X.B.I.F))
  inv1 : G' * G = 1
  inv2 : G * G' = 1
  c1 : C1 (eA X) G
  c2 : (G - 1) *ᵥ zA X u ∈ SpL (eA X) D.R.rS

variable {G G' : Matrix (Fin X.B.I.n) (Fin X.B.I.n) (X.B.I.E ⊗[X.B.I.F] Af X.B.I.F)}

/- English proof (translation)
Establish `hc1 : ∀ b, (G - 1) *ᵥ eA X b ∈ SpL (eA X) b.1` using `h.c1`. Establish `hmono : ∀ {m m' : ℕ}, m ≤ m' → SpL (eA X) m ≤ SpL (eA X) m'`. Introduce `m m' hm`. Unfold `SpL`. Conclude with `Submodule.span_mono (Set.image_mono fun c hc => lt_of_lt_of_le hc hm)`.

Establish `hemem : ∀ (c : Fin D.R.rS) (m : ℕ), c.1 < m → eA X c ∈ SpL (eA X) m`. Introduce `c m hc`. Unfold `SpL`. Conclude with `Submodule.subset_span ⟨c, hc, rfl⟩`. Establish `hGe : ∀ c : Fin D.R.rS, G' *ᵥ eA X c = eA X c + (G' - 1) *ᵥ eA X c`.

Introduce `c`. Rewrite using `[Matrix.sub_mulVec, Matrix.one_mulVec]`. Normalize the expressions using the abelian group laws. Establish `key : ∀ k : ℕ, ∀ b : Fin D.R.rS, b.1 < k → (G' - 1) *ᵥ eA X b ∈ SpL (eA X) b.1`. Introduce `k`.

Proceed by induction on `k with`. Consider the case `zero => intro b hb`. Conclude with `absurd hb (Nat.not_lt_zero _)`. Consider the case `succ k ih`. Introduce `b hb`.

Establish `e1 : (G' - 1) *ᵥ eA X b = -(G' *ᵥ ((G - 1) *ᵥ eA X b))`. Rewrite using `[Matrix.mulVec_mulVec, mul_sub, h.inv1, mul_one, Matrix.sub_mulVec, Matrix.sub_mulVec, Matrix.one_mulVec]`. Normalize the expressions using the abelian group laws. Rewrite using `[e1]`. Use `Submodule.neg_mem _ ?_` and prove the remaining obligations.

Establish `hle : SpL (eA X) b.1 ≤ (SpL (eA X) b.1).comap (Matrix.mulVecLin G')` using `by conv_lhs => unfold SpL`. Rewrite using `[Submodule.span_le]`. Introduce and unpack `_ ⟨c, hc, rfl⟩`. Rewrite using `[SetLike.mem_coe, Submodule.mem_comap, Matrix.mulVecLin_apply]`. Establish `hc' : c.1 < b.1` using `hc`.

Rewrite using `[hGe c]`. Conclude with `Submodule.add_mem _ (hemem c b.1 hc') (hmono (le_of_lt hc') (ih c (lt_of_lt_of_le hc' (Nat.lt_succ_iff.mp hb))))`. Establish `h3` using `hle (hc1 b)`. Rewrite `h3` using `[Submodule.mem_comap, Matrix.mulVecLin_apply]`. Then use the resulting hypothesis. Use `⟨hu, h.inv2, h.inv1, fun a => key _ a (Nat.lt_succ_self _), ?_⟩` and prove the remaining obligations.

Establish `e1 : (G' - 1) *ᵥ zA X u = -(G' *ᵥ ((G - 1) *ᵥ zA X u))`. Rewrite using `[Matrix.mulVec_mulVec, mul_sub, h.inv1, mul_one, Matrix.sub_mulVec, Matrix.sub_mulVec, Matrix.one_mulVec]`. Normalize the expressions using the abelian group laws. Rewrite using `[e1]`. Use `Submodule.neg_mem _ ?_` and prove the remaining obligations.

Establish `hle : SpL (eA X) D.R.rS ≤ (SpL (eA X) D.R.rS).comap (Matrix.mulVecLin G')` using `by conv_lhs => unfold SpL`. Rewrite using `[Submodule.span_le]`. Introduce and unpack `_ ⟨c, hc, rfl⟩`. Rewrite using `[SetLike.mem_coe, Submodule.mem_comap, Matrix.mulVecLin_apply, hGe c]`. Conclude with `Submodule.add_mem _ (hemem c _ c.2) (hmono (le_of_lt c.2) (key _ c (Nat.lt_succ_self _)))`.

Establish `h3` using `hle h.c2`. Rewrite `h3` using `[Submodule.mem_comap, Matrix.mulVecLin_apply]`. Then use the resulting hypothesis.
-/
theorem SA.symm (h : SA (u := u) G G')
    (hu : Formalism.UG.cT (sigA X.B.I) G' * X.B.I.J.map (Formalism.UG.inclE (F := X.B.I.F) (Af X.B.I.F)) * G' =
      X.B.I.J.map (Formalism.UG.inclE (F := X.B.I.F) (Af X.B.I.F))) : SA (u := u) G' G := by
  have hc1 : ∀ b, (G - 1) *ᵥ eA X b ∈ SpL (eA X) b.1 := h.c1
  have hmono : ∀ {m m' : ℕ}, m ≤ m' → SpL (eA X) m ≤ SpL (eA X) m' := by
    intro m m' hm
    unfold SpL
    exact Submodule.span_mono (Set.image_mono fun c hc => lt_of_lt_of_le hc hm)
  have hemem : ∀ (c : Fin D.R.rS) (m : ℕ), c.1 < m → eA X c ∈ SpL (eA X) m := by
    intro c m hc
    unfold SpL
    exact Submodule.subset_span ⟨c, hc, rfl⟩
  have hGe : ∀ c : Fin D.R.rS, G' *ᵥ eA X c = eA X c + (G' - 1) *ᵥ eA X c := by
    intro c
    rw [Matrix.sub_mulVec, Matrix.one_mulVec]
    abel
  have key : ∀ k : ℕ, ∀ b : Fin D.R.rS, b.1 < k → (G' - 1) *ᵥ eA X b ∈ SpL (eA X) b.1 := by
    intro k
    induction k with
    | zero => intro b hb; exact absurd hb (Nat.not_lt_zero _)
    | succ k ih =>
      intro b hb
      have e1 : (G' - 1) *ᵥ eA X b = -(G' *ᵥ ((G - 1) *ᵥ eA X b)) := by
        rw [Matrix.mulVec_mulVec, mul_sub, h.inv1, mul_one, Matrix.sub_mulVec, Matrix.sub_mulVec, Matrix.one_mulVec]
        abel
      rw [e1]
      refine Submodule.neg_mem _ ?_
      have hle : SpL (eA X) b.1 ≤ (SpL (eA X) b.1).comap (Matrix.mulVecLin G') := by
        conv_lhs => unfold SpL
        rw [Submodule.span_le]
        rintro _ ⟨c, hc, rfl⟩
        rw [SetLike.mem_coe, Submodule.mem_comap, Matrix.mulVecLin_apply]
        have hc' : c.1 < b.1 := hc
        rw [hGe c]
        exact Submodule.add_mem _ (hemem c b.1 hc')
          (hmono (le_of_lt hc') (ih c (lt_of_lt_of_le hc' (Nat.lt_succ_iff.mp hb))))
      have h3 := hle (hc1 b)
      rwa [Submodule.mem_comap, Matrix.mulVecLin_apply] at h3
  refine ⟨hu, h.inv2, h.inv1, fun a => key _ a (Nat.lt_succ_self _), ?_⟩
  have e1 : (G' - 1) *ᵥ zA X u = -(G' *ᵥ ((G - 1) *ᵥ zA X u)) := by
    rw [Matrix.mulVec_mulVec, mul_sub, h.inv1, mul_one, Matrix.sub_mulVec, Matrix.sub_mulVec, Matrix.one_mulVec]
    abel
  rw [e1]
  refine Submodule.neg_mem _ ?_
  have hle : SpL (eA X) D.R.rS ≤ (SpL (eA X) D.R.rS).comap (Matrix.mulVecLin G') := by
    conv_lhs => unfold SpL
    rw [Submodule.span_le]
    rintro _ ⟨c, hc, rfl⟩
    rw [SetLike.mem_coe, Submodule.mem_comap, Matrix.mulVecLin_apply, hGe c]
    exact Submodule.add_mem _ (hemem c _ c.2) (hmono (le_of_lt c.2) (key _ c (Nat.lt_succ_self _)))
  have h3 := hle h.c2
  rwa [Submodule.mem_comap, Matrix.mulVecLin_apply] at h3

/- English proof (translation)
Establish `hf : ∀ a b : VA X.B.I, hA X.B.I a b = (fun i => (sigA X.B.I) (a i)) ⬝ᵥ (X.B.I.J.map (Formalism.UG.inclE (F` using `X.B.I.F) (Af X.B.I.F)) *ᵥ b) := by`. Introduce `a b`. Apply the tactic sequence `simp only [hA, Formalism.UG.hform, dotProduct, Matrix.mulVec, Finset.mul_sum, mul_assoc] <;> rfl`. Rewrite using `[hf, hf]`. Establish `hσ : (fun i => (sigA X.B.I) ((G *ᵥ x) i)) = (G.map (sigA X.B.I)) *ᵥ (fun i => (sigA X.B.I) (x i))`.

Use function extensionality and compare the values at `i`. Conclude with `RingHom.map_mulVec _ _ _ _`. Rewrite using `[hσ, ← Matrix.vecMul_transpose, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, show (G.map (sigA X.B.I))ᵀ = Formalism.UG.cT (sigA X.B.I) G from rfl, h.unit]`.
-/
theorem SA.hA_G (h : SA (u := u) G G') (x y : VA X.B.I) : hA X.B.I (G *ᵥ x) (G *ᵥ y) = hA X.B.I x y := by
  have hf : ∀ a b : VA X.B.I, hA X.B.I a b = (fun i => (sigA X.B.I) (a i)) ⬝ᵥ (X.B.I.J.map (Formalism.UG.inclE (F := X.B.I.F) (Af X.B.I.F)) *ᵥ b) := by
    intro a b
    simp only [hA, Formalism.UG.hform, dotProduct, Matrix.mulVec, Finset.mul_sum, mul_assoc] <;> rfl
  rw [hf, hf]
  have hσ : (fun i => (sigA X.B.I) ((G *ᵥ x) i)) = (G.map (sigA X.B.I)) *ᵥ (fun i => (sigA X.B.I) (x i)) := by
    funext i
    exact RingHom.map_mulVec _ _ _ _
  rw [hσ, ← Matrix.vecMul_transpose, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec,
    show (G.map (sigA X.B.I))ᵀ = Formalism.UG.cT (sigA X.B.I) G from rfl, h.unit]

/- English proof (translation)
Establish `hc1 : ∀ b, (G - 1) *ᵥ eA X b ∈ SpL (eA X) b.1` using `h.c1`. Establish `hmem : ∀ a, G *ᵥ eA X a ∈ Submodule.span (X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) (Set.range (eA X))`. Introduce `a`. Establish `h2 : G *ᵥ eA X a = (G - 1) *ᵥ eA X a + eA X a`. Rewrite using `[Matrix.sub_mulVec, Matrix.one_mulVec]`.

Normalize the expressions using the abelian group laws. Rewrite using `[h2]`. Use `Submodule.add_mem _ ?_ (e_mem_span X a)` and prove the remaining obligations. Conclude with `Submodule.span_mono (Set.image_subset_range _ _) (hc1 a)`. Establish `hle : Submodule.span (X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) (Set.range (eA X)) ≤ (Submodule.span (X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) (Set.range (eA X))).comap (Matrix.mulVecLin G)`.

Rewrite using `[Submodule.span_le]`. Introduce and unpack `_ ⟨a, rfl⟩`. Rewrite using `[SetLike.mem_coe, Submodule.mem_comap, Matrix.mulVecLin_apply]`. Conclude with `hmem a`. Establish `h3` using `hle hs`.

Rewrite `h3` using `[Submodule.mem_comap, Matrix.mulVecLin_apply]`. Then use the resulting hypothesis.
-/
theorem SA.pres (h : SA (u := u) G G') (s : VA X.B.I)
    (hs : s ∈ Submodule.span (X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) (Set.range (eA X))) :
    G *ᵥ s ∈ Submodule.span (X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) (Set.range (eA X)) := by
  have hc1 : ∀ b, (G - 1) *ᵥ eA X b ∈ SpL (eA X) b.1 := h.c1
  have hmem : ∀ a, G *ᵥ eA X a ∈ Submodule.span (X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) (Set.range (eA X)) := by
    intro a
    have h2 : G *ᵥ eA X a = (G - 1) *ᵥ eA X a + eA X a := by
      rw [Matrix.sub_mulVec, Matrix.one_mulVec]
      abel
    rw [h2]
    refine Submodule.add_mem _ ?_ (e_mem_span X a)
    exact Submodule.span_mono (Set.image_subset_range _ _) (hc1 a)
  have hle : Submodule.span (X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) (Set.range (eA X)) ≤ (Submodule.span (X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) (Set.range (eA X))).comap (Matrix.mulVecLin G) := by
    rw [Submodule.span_le]
    rintro _ ⟨a, rfl⟩
    rw [SetLike.mem_coe, Submodule.mem_comap, Matrix.mulVecLin_apply]
    exact hmem a
  have h3 := hle hs
  rwa [Submodule.mem_comap, Matrix.mulVecLin_apply] at h3

/- English proof (translation)
Establish `hc1 : ∀ b, (G - 1) *ᵥ eA X b ∈ SpL (eA X) b.1` using `h.c1`. It suffices to establish `H : ∀ k : ℕ, ∀ b : Fin D.R.rS, b.1 < k → G' *ᵥ eA X b ∈ Submodule.span (X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) (Set.range (eA X)) from H _ a (Nat.lt_succ_self _)`. Introduce `k`. Proceed by induction on `k with`. Consider the case `zero => intro b hb`.

Conclude with `absurd hb (Nat.not_lt_zero _)`. Consider the case `succ k ih`. Introduce `b hb`. Establish `key : G' *ᵥ eA X b = eA X b - G' *ᵥ ((G - 1) *ᵥ eA X b)`. Rewrite using `[Matrix.mulVec_mulVec, mul_sub, h.inv1, mul_one, Matrix.sub_mulVec, Matrix.one_mulVec, sub_sub_cancel]`.

Rewrite using `[key]`. Use `Submodule.sub_mem _ (e_mem_span X b) ?_` and prove the remaining obligations. Establish `hle : SpL (eA X) b.1 ≤ (Submodule.span (X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) (Set.range (eA X))).comap (Matrix.mulVecLin G')`. Unfold `SpL`. Rewrite using `[Submodule.span_le]`.

Introduce and unpack `_ ⟨c, hc, rfl⟩`. Rewrite using `[SetLike.mem_coe, Submodule.mem_comap, Matrix.mulVecLin_apply]`. Establish `hc' : c.1 < b.1` using `hc`. Conclude with `ih c (lt_of_lt_of_le hc' (Nat.lt_succ_iff.mp hb))`. Establish `h3` using `hle (hc1 b)`.

Rewrite `h3` using `[Submodule.mem_comap, Matrix.mulVecLin_apply]`. Then use the resulting hypothesis.
-/
theorem SA.inv_e (h : SA (u := u) G G') (a : Fin D.R.rS) :
    G' *ᵥ eA X a ∈ Submodule.span (X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) (Set.range (eA X)) := by
  have hc1 : ∀ b, (G - 1) *ᵥ eA X b ∈ SpL (eA X) b.1 := h.c1
  suffices H : ∀ k : ℕ, ∀ b : Fin D.R.rS, b.1 < k → G' *ᵥ eA X b ∈ Submodule.span (X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) (Set.range (eA X)) from
    H _ a (Nat.lt_succ_self _)
  intro k
  induction k with
  | zero => intro b hb; exact absurd hb (Nat.not_lt_zero _)
  | succ k ih =>
    intro b hb
    have key : G' *ᵥ eA X b = eA X b - G' *ᵥ ((G - 1) *ᵥ eA X b) := by
      rw [Matrix.mulVec_mulVec, mul_sub, h.inv1, mul_one, Matrix.sub_mulVec, Matrix.one_mulVec, sub_sub_cancel]
    rw [key]
    refine Submodule.sub_mem _ (e_mem_span X b) ?_
    have hle : SpL (eA X) b.1 ≤ (Submodule.span (X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) (Set.range (eA X))).comap (Matrix.mulVecLin G') := by
      unfold SpL
      rw [Submodule.span_le]
      rintro _ ⟨c, hc, rfl⟩
      rw [SetLike.mem_coe, Submodule.mem_comap, Matrix.mulVecLin_apply]
      have hc' : c.1 < b.1 := hc
      exact ih c (lt_of_lt_of_le hc' (Nat.lt_succ_iff.mp hb))
    have h3 := hle (hc1 b)
    rwa [Submodule.mem_comap, Matrix.mulVecLin_apply] at h3

/- English proof (translation)
Establish `hc2 : (G - 1) *ᵥ zA X u ∈ SpL (eA X) D.R.rS` using `h.c2`. Establish `key : (G' - 1) *ᵥ zA X u = -(G' *ᵥ ((G - 1) *ᵥ zA X u))`. Rewrite using `[Matrix.mulVec_mulVec, mul_sub, h.inv1, mul_one, Matrix.sub_mulVec, Matrix.sub_mulVec, Matrix.one_mulVec]`. Normalize the expressions using the abelian group laws. Rewrite using `[key]`.

Use `Submodule.neg_mem _ ?_` and prove the remaining obligations. Establish `hle : SpL (eA X) D.R.rS ≤ (Submodule.span (X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) (Set.range (eA X))).comap (Matrix.mulVecLin G')`. Unfold `SpL`. Rewrite using `[Submodule.span_le]`. Introduce and unpack `_ ⟨b, _, rfl⟩`.

Rewrite using `[SetLike.mem_coe, Submodule.mem_comap, Matrix.mulVecLin_apply]`. Conclude with `h.inv_e b`. Establish `h3` using `hle hc2`. Rewrite `h3` using `[Submodule.mem_comap, Matrix.mulVecLin_apply]`. Then use the resulting hypothesis.
-/
theorem SA.coordinate_inverse_zeta (h : SA (u := u) G G') :
    (G' - 1) *ᵥ zA X u ∈ Submodule.span (X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) (Set.range (eA X)) := by
  have hc2 : (G - 1) *ᵥ zA X u ∈ SpL (eA X) D.R.rS := h.c2
  have key : (G' - 1) *ᵥ zA X u = -(G' *ᵥ ((G - 1) *ᵥ zA X u)) := by
    rw [Matrix.mulVec_mulVec, mul_sub, h.inv1, mul_one, Matrix.sub_mulVec, Matrix.sub_mulVec, Matrix.one_mulVec]
    abel
  rw [key]
  refine Submodule.neg_mem _ ?_
  have hle : SpL (eA X) D.R.rS ≤ (Submodule.span (X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) (Set.range (eA X))).comap (Matrix.mulVecLin G') := by
    unfold SpL
    rw [Submodule.span_le]
    rintro _ ⟨b, _, rfl⟩
    rw [SetLike.mem_coe, Submodule.mem_comap, Matrix.mulVecLin_apply]
    exact h.inv_e b
  have h3 := hle hc2
  rwa [Submodule.mem_comap, Matrix.mulVecLin_apply] at h3

/- English proof (translation)
Establish `hG : ∀ x y, hA X.B.I (G *ᵥ x) (G *ᵥ y) = hA X.B.I x y` using `h.hA_G`. Establish `hGG : ∀ x, G *ᵥ (G' *ᵥ x) = x` using `fun x => by rw [Matrix.mulVec_mulVec, h.inv2, Matrix.one_mulVec]`. Prove the components needed by the constructor for the conclusion. Introduce `a`. Rewrite using `[← hGG (eA X a), hG]`.

Conclude with `hA_span_left X _ w (h.inv_e a) he`. Rewrite using `[← hGG (zA X u), hG]`. Establish `e1 : G' *ᵥ zA X u = zA X u + (G' - 1) *ᵥ zA X u`. Rewrite using `[Matrix.sub_mulVec, Matrix.one_mulVec]`. Normalize the expressions using the abelian group laws.

Rewrite using `[e1, hA_add_left_lemma_4, hz, hA_span_left X _ w h.coordinate_inverse_zeta he, add_zero]`.
-/
theorem SA.perp (h : SA (u := u) G G') (w : VA X.B.I) (he : ∀ a, hA X.B.I (eA X a) w = 0)
    (hz : hA X.B.I (zA X u) w = 0) :
    (∀ a, hA X.B.I (eA X a) (G *ᵥ w) = 0) ∧ hA X.B.I (zA X u) (G *ᵥ w) = 0 := by
  have hG : ∀ x y, hA X.B.I (G *ᵥ x) (G *ᵥ y) = hA X.B.I x y := h.hA_G
  have hGG : ∀ x, G *ᵥ (G' *ᵥ x) = x := fun x => by rw [Matrix.mulVec_mulVec, h.inv2, Matrix.one_mulVec]
  constructor
  · intro a
    rw [← hGG (eA X a), hG]
    exact hA_span_left X _ w (h.inv_e a) he
  · rw [← hGG (zA X u), hG]
    have e1 : G' *ᵥ zA X u = zA X u + (G' - 1) *ᵥ zA X u := by
      rw [Matrix.sub_mulVec, Matrix.one_mulVec]
      abel
    rw [e1, hA_add_left_lemma_4, hz, hA_span_left X _ w h.coordinate_inverse_zeta he, add_zero]

/- English proof (translation)
Take `⟨hpe, hpz⟩` from `h.perp w he hz`. Rewrite using `[sub_PW]`. Simplify using `only [hpe, hpz, zero_smul, Finset.sum_const_zero, add_zero, mul_zero]`. Conclude with `Submodule.sum_mem _ fun a _ => Submodule.smul_mem _ _ (e_mem_span X a)`.
-/
theorem SA.sub_PW_mem (h : SA (u := u) G G') (w : VA X.B.I) (he : ∀ a, hA X.B.I (eA X a) w = 0)
    (hz : hA X.B.I (zA X u) w = 0) :
    G *ᵥ w - PWl X u (G *ᵥ w) ∈ Submodule.span (X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) (Set.range (eA X)) := by
  obtain ⟨hpe, hpz⟩ := h.perp w he hz
  rw [sub_PW]
  simp only [hpe, hpz, zero_smul, Finset.sum_const_zero, add_zero, mul_zero]
  exact Submodule.sum_mem _ fun a _ => Submodule.smul_mem _ _ (e_mem_span X a)

variable (X u) in

def Hf (G : Matrix (Fin X.B.I.n) (Fin X.B.I.n) (X.B.I.E ⊗[X.B.I.F] Af X.B.I.F)) (y : VA X.B.I) : VA X.B.I :=
  PWl X u (G *ᵥ PWl X u y) + (y - PWl X u y)

variable (X u) in
def Hl (G : Matrix (Fin X.B.I.n) (Fin X.B.I.n) (X.B.I.E ⊗[X.B.I.F] Af X.B.I.F)) :
    VA X.B.I →ₗ[X.B.I.E ⊗[X.B.I.F] Af X.B.I.F] VA X.B.I where
  toFun := Hf X u G
  map_add' y y' := by
    simp only [Hf, map_add, mulVec_add]; abel
  map_smul' c y := by
    simp only [Hf, map_smul, mulVec_smul, RingHom.id_apply, smul_add, smul_sub]

variable (X u) in
def Hm (G : Matrix (Fin X.B.I.n) (Fin X.B.I.n) (X.B.I.E ⊗[X.B.I.F] Af X.B.I.F)) :
    Matrix (Fin X.B.I.n) (Fin X.B.I.n) (X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) :=
  LinearMap.toMatrix' (Hl X u G)

/- English proof (translation)
Use `first`. Consider the case `(rw [Hm, LinearMap.toMatrix'_mulVec]; rfl)`. Consider the case `simp [Hm, Hl, LinearMap.toMatrix'_mulVec]`.
-/
theorem Hm_mulVec (y : VA X.B.I) : Hm X u G *ᵥ y = Hf X u G y := by
  first
  | (rw [Hm, LinearMap.toMatrix'_mulVec]; rfl)
  | simp [Hm, Hl, LinearMap.toMatrix'_mulVec]

/- English proof (translation)
Rewrite using `[Hm_mulVec]`. Use `first`. Consider the case `simp [Hf, hy]`. Consider the case `(simp only [Hf, hy, Matrix.mulVec_zero, map_zero, zero_add, sub_zero])`.
-/
theorem Hm_fix (y : VA X.B.I) (hy : PWl X u y = 0) : Hm X u G *ᵥ y = y := by
  rw [Hm_mulVec]
  first
  | simp [Hf, hy]
  | (simp only [Hf, hy, Matrix.mulVec_zero, map_zero, zero_add, sub_zero])

/- English proof (translation)
Conclude with `Hm_fix _ (PW_e X u a)`.
-/
theorem Hm_e (a : Fin D.R.rS) : Hm X u G *ᵥ eA X a = eA X a := by
  exact Hm_fix _ (PW_e X u a)

/- English proof (translation)
Conclude with `Hm_fix _ (PW_f X u a)`.
-/
theorem Hm_f (a : Fin D.R.rS) : Hm X u G *ᵥ fA X a = fA X a := by
  exact Hm_fix _ (PW_f X u a)

/- English proof (translation)
Conclude with `Hm_fix _ (levi_projection_z_zero X u)`.
-/
theorem levi_fixes_z : Hm X u G *ᵥ zA X u = zA X u := by
  exact Hm_fix _ (levi_projection_z_zero X u)

/- English proof (translation)
Establish `hPH : ∀ z, PWl X u (Hm X u G *ᵥ z) = PWl X u (G *ᵥ PWl X u z)`. Introduce `z`. Rewrite using `[Hm_mulVec]`. Simplify using `only [Hf, map_add, PW_idem, PW_sub_self, add_zero]`. Establish `hRH : ∀ z, Hm X u G *ᵥ z - PWl X u (Hm X u G *ᵥ z) = z - PWl X u z`.

Introduce `z`. Rewrite using `[hPH, Hm_mulVec]`. Simplify using `only [Hf]`. Normalize the expressions using the abelian group laws. Establish `core : hA X.B.I (PWl X u (G *ᵥ PWl X u x)) (PWl X u (G *ᵥ PWl X u y)) = hA X.B.I (PWl X u x) (PWl X u y)`.

Establish `hs` using `h.sub_PW_mem (PWl X u x) (fun a => hA_e_PW X u a x) (hA_z_PW X u x)`. Establish `hs'` using `h.sub_PW_mem (PWl X u y) (fun a => hA_e_PW X u a y) (hA_z_PW X u y)`. Establish `z1 : hA X.B.I (PWl X u (G *ᵥ PWl X u x)) ((G *ᵥ PWl X u y) - PWl X u (G *ᵥ PWl X u y)) = 0` using `hA_span_right X _ _ hs' (fun a => hA_symm_zero X (hA_e_PW X u a (G *ᵥ PWl X u x)))`. Establish `z2 : hA X.B.I ((G *ᵥ PWl X u x) - PWl X u (G *ᵥ PWl X u x)) (PWl X u (G *ᵥ PWl X u y)) = 0` using `hA_span_left X _ _ hs (fun a => hA_e_PW X u a (G *ᵥ PWl X u y))`. Establish `z3 : hA X.B.I ((G *ᵥ PWl X u x) - PWl X u (G *ᵥ PWl X u x)) ((G *ᵥ PWl X u y) - PWl X u (G *ᵥ PWl X u y)) = 0` using `hA_span_left X _ _ hs (fun a => hA_span_right X (eA X a) _ hs' (fun b => hA_e_e X a b))`.

Establish `h0` using `h.hA_G (PWl X u x) (PWl X u y)`. Establish `ex : PWl X u (G *ᵥ PWl X u x) + ((G *ᵥ PWl X u x) - PWl X u (G *ᵥ PWl X u x)) = (G *ᵥ PWl X u x)` using `by abel`. Establish `ey : PWl X u (G *ᵥ PWl X u y) + ((G *ᵥ PWl X u y) - PWl X u (G *ᵥ PWl X u y)) = (G *ᵥ PWl X u y)` using `by abel`. Rewrite `h0` using `[← ex, ← ey]`. Simplify using `only [hA_add_left_lemma_4, hA_add_right_lemma_2, z1, z2, z3, add_zero] at h0`.

Conclude with `h0`. Rewrite using `[hA_sub_PW_self X u (Hm X u G *ᵥ x) (Hm X u G *ᵥ y), hRH, hRH, hPH, hPH, core, ← hA_sub_PW_self X u x y]`.
-/
theorem SA.hA_H (h : SA (u := u) G G') (x y : VA X.B.I) :
    hA X.B.I (Hm X u G *ᵥ x) (Hm X u G *ᵥ y) = hA X.B.I x y := by
  have hPH : ∀ z, PWl X u (Hm X u G *ᵥ z) = PWl X u (G *ᵥ PWl X u z) := by
    intro z
    rw [Hm_mulVec]
    simp only [Hf, map_add, PW_idem, PW_sub_self, add_zero]
  have hRH : ∀ z, Hm X u G *ᵥ z - PWl X u (Hm X u G *ᵥ z) = z - PWl X u z := by
    intro z
    rw [hPH, Hm_mulVec]
    simp only [Hf]
    abel
  have core : hA X.B.I (PWl X u (G *ᵥ PWl X u x)) (PWl X u (G *ᵥ PWl X u y)) = hA X.B.I (PWl X u x) (PWl X u y) := by
    have hs := h.sub_PW_mem (PWl X u x) (fun a => hA_e_PW X u a x) (hA_z_PW X u x)
    have hs' := h.sub_PW_mem (PWl X u y) (fun a => hA_e_PW X u a y) (hA_z_PW X u y)
    have z1 : hA X.B.I (PWl X u (G *ᵥ PWl X u x)) ((G *ᵥ PWl X u y) - PWl X u (G *ᵥ PWl X u y)) = 0 :=
      hA_span_right X _ _ hs' (fun a => hA_symm_zero X (hA_e_PW X u a (G *ᵥ PWl X u x)))
    have z2 : hA X.B.I ((G *ᵥ PWl X u x) - PWl X u (G *ᵥ PWl X u x)) (PWl X u (G *ᵥ PWl X u y)) = 0 :=
      hA_span_left X _ _ hs (fun a => hA_e_PW X u a (G *ᵥ PWl X u y))
    have z3 : hA X.B.I ((G *ᵥ PWl X u x) - PWl X u (G *ᵥ PWl X u x)) ((G *ᵥ PWl X u y) - PWl X u (G *ᵥ PWl X u y)) = 0 :=
      hA_span_left X _ _ hs (fun a => hA_span_right X (eA X a) _ hs' (fun b => hA_e_e X a b))
    have h0 := h.hA_G (PWl X u x) (PWl X u y)
    have ex : PWl X u (G *ᵥ PWl X u x) + ((G *ᵥ PWl X u x) - PWl X u (G *ᵥ PWl X u x)) = (G *ᵥ PWl X u x) := by abel
    have ey : PWl X u (G *ᵥ PWl X u y) + ((G *ᵥ PWl X u y) - PWl X u (G *ᵥ PWl X u y)) = (G *ᵥ PWl X u y) := by abel
    rw [← ex, ← ey] at h0
    simp only [hA_add_left_lemma_4, hA_add_right_lemma_2, z1, z2, z3, add_zero] at h0
    exact h0
  rw [hA_sub_PW_self X u (Hm X u G *ᵥ x) (Hm X u G *ᵥ y), hRH, hRH, hPH, hPH, core, ← hA_sub_PW_self X u x y]

/- English proof (translation)
Use `LinearMap.ext fun y => ?_` and prove the remaining obligations. Use `show Hf X u G (Hf X u G' y) = y`. Establish `hp1 : PWl X u (Hf X u G' y) = PWl X u (G' *ᵥ PWl X u y)`. Simplify using `only [Hf, map_add, PW_idem, PW_sub_self, add_zero]`. Establish `hp2 : Hf X u G' y - PWl X u (Hf X u G' y) = y - PWl X u y`.

Rewrite using `[hp1]`. Simplify using `only [Hf]`. Normalize the expressions using the abelian group laws. Establish `hs` using `h'.sub_PW_mem (PWl X u y) (fun a => hA_e_PW X u a y) (hA_z_PW X u y)`. Establish `hGs` using `h.pres _ hs`.

Establish `key : PWl X u (G *ᵥ PWl X u (G' *ᵥ PWl X u y)) = PWl X u y`. Establish `e1 : PWl X u (G' *ᵥ PWl X u y) = G' *ᵥ PWl X u y - (G' *ᵥ PWl X u y - PWl X u (G' *ᵥ PWl X u y))` using `by abel`. Rewrite using `[e1, Matrix.mulVec_sub, map_sub, PW_span X u _ hGs, sub_zero, Matrix.mulVec_mulVec, h.inv2, Matrix.one_mulVec, PW_idem]`. Use `show PWl X u (G *ᵥ PWl X u (Hf X u G' y)) + (Hf X u G' y - PWl X u (Hf X u G' y)) = y`. Rewrite using `[hp2, hp1, key]`.

Normalize the expressions using the abelian group laws.
-/
theorem Hl_comp (h : SA (u := u) G G') (h' : SA (u := u) G' G) : (Hl X u G).comp (Hl X u G') = LinearMap.id := by
  refine LinearMap.ext fun y => ?_
  show Hf X u G (Hf X u G' y) = y
  have hp1 : PWl X u (Hf X u G' y) = PWl X u (G' *ᵥ PWl X u y) := by
    simp only [Hf, map_add, PW_idem, PW_sub_self, add_zero]
  have hp2 : Hf X u G' y - PWl X u (Hf X u G' y) = y - PWl X u y := by
    rw [hp1]
    simp only [Hf]
    abel
  have hs := h'.sub_PW_mem (PWl X u y) (fun a => hA_e_PW X u a y) (hA_z_PW X u y)
  have hGs := h.pres _ hs
  have key : PWl X u (G *ᵥ PWl X u (G' *ᵥ PWl X u y)) = PWl X u y := by
    have e1 : PWl X u (G' *ᵥ PWl X u y) =
        G' *ᵥ PWl X u y - (G' *ᵥ PWl X u y - PWl X u (G' *ᵥ PWl X u y)) := by abel
    rw [e1, Matrix.mulVec_sub, map_sub, PW_span X u _ hGs, sub_zero, Matrix.mulVec_mulVec, h.inv2,
      Matrix.one_mulVec, PW_idem]
  show PWl X u (G *ᵥ PWl X u (Hf X u G' y)) + (Hf X u G' y - PWl X u (Hf X u G' y)) = y
  rw [hp2, hp1, key]
  abel

/- English proof (translation)
Rewrite using `[Hm, Hm, ← LinearMap.toMatrix'_comp, Hl_comp h h', LinearMap.toMatrix'_id]`.
-/
theorem Hm_mul (h : SA (u := u) G G') (h' : SA (u := u) G' G) : Hm X u G * Hm X u G' = 1 := by
  rw [Hm, Hm, ← LinearMap.toMatrix'_comp, Hl_comp h h', LinearMap.toMatrix'_id]

def HGL (h : SA (u := u) G G') (h' : SA (u := u) G' G) : GL (Fin X.B.I.n) (X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) :=
  ⟨Hm X u G, Hm X u G', Hm_mul h h', Hm_mul h' h⟩

/- English proof (translation)
Use `first`. Consider the case `exact unit_of_formA X (Hm X u G) (h.hA_H)`. Consider the case `(simp only [Formalism.UG.UPts, Set.mem_setOf_eq, Subgroup.mem_mk, Submonoid.mem_mk, Subsemigroup.mem_mk]`. Conclude with `unit_of_formA X (Hm X u G) (h.hA_H))`. Consider the case `(show Formalism.UG.cT (sigA X.B.I) (Hm X u G) * X.B.I.J.map (Formalism.UG.inclE (F := X.B.I.F) (Af X.B.I.F)) * Hm X u G = X.B.I.J.map (Formalism.UG.inclE (F := X.B.I.F) (Af X.B.I.F))`.

Conclude with `unit_of_formA X (Hm X u G) (h.hA_H))`.
-/
theorem HGL_unit (h : SA (u := u) G G') (h' : SA (u := u) G' G) :
    HGL h h' ∈ Formalism.UG.UPts X.B.I.cm.sig X.B.I.J (Af X.B.I.F) := by
  first
  | exact unit_of_formA X (Hm X u G) (h.hA_H)
  | (simp only [Formalism.UG.UPts, Set.mem_setOf_eq, Subgroup.mem_mk, Submonoid.mem_mk, Subsemigroup.mem_mk]
     exact unit_of_formA X (Hm X u G) (h.hA_H))
  | (show Formalism.UG.cT (sigA X.B.I) (Hm X u G) * X.B.I.J.map (Formalism.UG.inclE (F := X.B.I.F) (Af X.B.I.F)) * Hm X u G =
       X.B.I.J.map (Formalism.UG.inclE (F := X.B.I.F) (Af X.B.I.F))
     exact unit_of_formA X (Hm X u G) (h.hA_H))

def HGf (h : SA (u := u) G G') (h' : SA (u := u) G' G) : X.B.I.Gf := ⟨HGL h h', HGL_unit h h'⟩

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem HGf_fmat (h : SA (u := u) G G') (h' : SA (u := u) G' G) : X.B.I.fmat (HGf h h') = Hm X u G := rfl

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem HGf_fmat_inv (h : SA (u := u) G G') (h' : SA (u := u) G' G) :
    X.B.I.fmat (HGf h h')⁻¹ = Hm X u G' := rfl

/- English proof (translation)
Introduce `x hx`. Rewrite using `[HGf_fmat]`. Break down `hx with (⟨a, rfl⟩ | ⟨a, rfl⟩) | hz` into its components or cases. Conclude with `Hm_e a`. Conclude with `Hm_f a`.

Rewrite `hz` using `[Set.mem_singleton_iff]`. Rewrite using `[hz]`. Conclude with `levi_fixes_z`.
-/
theorem HGf_mem (h : SA (u := u) G G') (h' : SA (u := u) G' G) : HGf h h' ∈ Hfin X u := by
  intro x hx
  rw [HGf_fmat]
  rcases hx with (⟨a, rfl⟩ | ⟨a, rfl⟩) | hz
  · exact Hm_e a
  · exact Hm_f a
  · rw [Set.mem_singleton_iff] at hz; rw [hz]; exact levi_fixes_z

/- English proof (translation)
Use `set Hi := Hm X u G'`. Establish `hF : X.B.I.fmat (y * (HGf h h')⁻¹) = G * Hi` using `by show X.B.I.fmat y * X.B.I.fmat (HGf h h')⁻¹ = G * Hi`. Rewrite using `[hy, HGf_fmat_inv]`. Establish `hiH : Hi * Hm X u G = 1` using `Hm_mul h' h`. Establish `hHi : Hm X u G * Hi = 1` using `Hm_mul h h'`.

Establish `hie : ∀ a, Hi *ᵥ eA X a = eA X a` using `fun a => Hm_e a`. Establish `hiz : Hi *ᵥ zA X u = zA X u` using `levi_fixes_z`. Use `⟨fun a => ?_, ?_, fun y0 hy0 => ?_⟩` and prove the remaining obligations. Rewrite using `[hF]`. Establish `e : (G * Hi - 1) *ᵥ eA X a = (G - 1) *ᵥ eA X a`.

Rewrite using `[sub_mulVec, sub_mulVec, one_mulVec, ← mulVec_mulVec, hie]`. Rewrite using `[e]`. Conclude with `h.c1 a`. Rewrite using `[hF]`. Establish `e : (G * Hi - 1) *ᵥ zA X u = (G - 1) *ᵥ zA X u`.

Rewrite using `[sub_mulVec, sub_mulVec, one_mulVec, ← mulVec_mulVec, hiz]`. Rewrite using `[e, spL_range]`. Conclude with `h.c2`. Rewrite using `[hF] set y₁ := Hi *ᵥ y0`. Establish `hy1 : Hm X u G *ᵥ y₁ = y0` using `by rw [mulVec_mulVec, hHi, one_mulVec]`.

Establish `he1 : ∀ a, hA X.B.I (eA X a) y₁ = 0` using `fun a => by`. Rewrite using `[← h.hA_H (eA X a) y₁, Hm_e, hy1]`. Conclude with `hy0 a`. Use `set w := PWl X u y₁`. Use `set b := y₁ - PWl X u y₁`.

Establish `e : (G * Hi - 1) *ᵥ y0 = (G *ᵥ w - PWl X u (G *ᵥ w)) + (G - 1) *ᵥ b`. Establish `h1 : (G * Hi - 1) *ᵥ y0 = G *ᵥ y₁ - y0` using `by rw [sub_mulVec, one_mulVec, ← mulVec_mulVec]`. Rewrite using `[h1]`. Establish `h2 : y0 = PWl X u (G *ᵥ w) + b` using `by rw [← hy1, Hm_mulVec, Hf]`. Establish `h3 : y₁ = w + b` using `by simp only [w, b]; abel`.

Rewrite using `[h2, sub_mulVec, one_mulVec]`. Use `nth_rewrite 1 [h3]`. Rewrite using `[mulVec_add]`. Normalize the expressions using the abelian group laws. Rewrite using `[e]`.

Use `add_mem (h.sub_PW_mem w (fun a => hA_e_PW X u a y₁) (hA_z_PW X u y₁)) ?_` and prove the remaining obligations. Rewrite using `[show b = y₁ - PWl X u y₁ from rfl, sub_PW]`. Simplify using `only [he1, zero_smul, Finset.sum_const_zero, add_zero, mulVec_add, mulVec_sum, mulVec_smul]`. Use `add_mem (Submodule.sum_mem _ fun c _ => Submodule.smul_mem _ _ ?_) (Submodule.smul_mem _ _ ?_)` and prove the remaining obligations. Conclude with `Submodule.span_mono (Set.image_subset_range _ _) (h.c1 c)`.

Rewrite using `[spL_range]`. Conclude with `h.c2`.
-/
theorem SA.nfin (h : SA (u := u) G G') (h' : SA (u := u) G' G) (y : X.B.I.Gf) (hy : X.B.I.fmat y = G) :
    y * (HGf h h')⁻¹ ∈ X.NfinU u := by
  set Hi := Hm X u G'
  have hF : X.B.I.fmat (y * (HGf h h')⁻¹) = G * Hi := by
    show X.B.I.fmat y * X.B.I.fmat (HGf h h')⁻¹ = G * Hi
    rw [hy, HGf_fmat_inv]
  have hiH : Hi * Hm X u G = 1 := Hm_mul h' h
  have hHi : Hm X u G * Hi = 1 := Hm_mul h h'
  have hie : ∀ a, Hi *ᵥ eA X a = eA X a := fun a => Hm_e a
  have hiz : Hi *ᵥ zA X u = zA X u := levi_fixes_z
  refine ⟨fun a => ?_, ?_, fun y0 hy0 => ?_⟩
  · rw [hF]
    have e : (G * Hi - 1) *ᵥ eA X a = (G - 1) *ᵥ eA X a := by
      rw [sub_mulVec, sub_mulVec, one_mulVec, ← mulVec_mulVec, hie]
    rw [e]; exact h.c1 a
  · rw [hF]
    have e : (G * Hi - 1) *ᵥ zA X u = (G - 1) *ᵥ zA X u := by
      rw [sub_mulVec, sub_mulVec, one_mulVec, ← mulVec_mulVec, hiz]
    rw [e, spL_range]; exact h.c2
  · rw [hF]
    set y₁ := Hi *ᵥ y0
    have hy1 : Hm X u G *ᵥ y₁ = y0 := by rw [mulVec_mulVec, hHi, one_mulVec]
    have he1 : ∀ a, hA X.B.I (eA X a) y₁ = 0 := fun a => by
      rw [← h.hA_H (eA X a) y₁, Hm_e, hy1]; exact hy0 a
    set w := PWl X u y₁
    set b := y₁ - PWl X u y₁
    have e : (G * Hi - 1) *ᵥ y0 = (G *ᵥ w - PWl X u (G *ᵥ w)) + (G - 1) *ᵥ b := by
      have h1 : (G * Hi - 1) *ᵥ y0 = G *ᵥ y₁ - y0 := by rw [sub_mulVec, one_mulVec, ← mulVec_mulVec]
      rw [h1]
      have h2 : y0 = PWl X u (G *ᵥ w) + b := by rw [← hy1, Hm_mulVec, Hf]
      have h3 : y₁ = w + b := by simp only [w, b]; abel
      rw [h2, sub_mulVec, one_mulVec]
      nth_rewrite 1 [h3]
      rw [mulVec_add]; abel
    rw [e]
    refine add_mem (h.sub_PW_mem w (fun a => hA_e_PW X u a y₁) (hA_z_PW X u y₁)) ?_
    rw [show b = y₁ - PWl X u y₁ from rfl, sub_PW]
    simp only [he1, zero_smul, Finset.sum_const_zero, add_zero, mulVec_add, mulVec_sum, mulVec_smul]
    refine add_mem (Submodule.sum_mem _ fun c _ => Submodule.smul_mem _ _ ?_) (Submodule.smul_mem _ _ ?_)
    · exact Submodule.span_mono (Set.image_subset_range _ _) (h.c1 c)
    · rw [spL_range]; exact h.c2

end Levi

section Final

variable {D : D7} (X : HidaSetting D) (u : D.what₂.Word)

/- English proof (translation)
Introduce `y hy`. Take `⟨hc1, hc2⟩` from `(Formalism.L2.SG.PoincareInHH.Cut.sfin_iff X u y).1 hy`. Establish `inv1 : X.B.I.fmat y⁻¹ * X.B.I.fmat y = 1` using `by simp [AutInst.fmat]`. Establish `inv2 : X.B.I.fmat y * X.B.I.fmat y⁻¹ = 1` using `by simp [AutInst.fmat]`. Establish `hS : SA (u` using `u) (X.B.I.fmat y) (X.B.I.fmat y⁻¹) := ⟨y.2, inv1, inv2, hc1, hc2⟩`.

Establish `hS' : SA (u` using `u) (X.B.I.fmat y⁻¹) (X.B.I.fmat y) := hS.symm (y⁻¹).2`. Set `H : Hfin X u` to `⟨HGf hS hS', HGf_mem hS hS'⟩`. Establish `hn'` using `hS.nfin hS' y rfl`. Establish `hc` using `(nfinConj_holds X u H⁻¹ _ hn').1`. Use `⟨H, (HGf hS hS')⁻¹ * y, ?_, ?_⟩` and prove the remaining obligations.

Use `swap`. Use `show y = HGf hS hS' * ((HGf hS hS')⁻¹ * y) group`. Use `hc using 1` and compare the differences between its conclusion and the goal. Simplify using `only [H, Subgroup.coe_inv, inv_inv]`. Use `group`.
-/
theorem finLevi_holds : Formalism.L2.SG.Pf.FinLevi X u := by
  intro y hy
  obtain ⟨hc1, hc2⟩ := (Formalism.L2.SG.PoincareInHH.Cut.sfin_iff X u y).1 hy
  have inv1 : X.B.I.fmat y⁻¹ * X.B.I.fmat y = 1 := by simp [AutInst.fmat]
  have inv2 : X.B.I.fmat y * X.B.I.fmat y⁻¹ = 1 := by simp [AutInst.fmat]
  have hS : SA (u := u) (X.B.I.fmat y) (X.B.I.fmat y⁻¹) := ⟨y.2, inv1, inv2, hc1, hc2⟩
  have hS' : SA (u := u) (X.B.I.fmat y⁻¹) (X.B.I.fmat y) := hS.symm (y⁻¹).2
  let H : Hfin X u := ⟨HGf hS hS', HGf_mem hS hS'⟩
  have hn' := hS.nfin hS' y rfl
  have hc := (nfinConj_holds X u H⁻¹ _ hn').1
  refine ⟨H, (HGf hS hS')⁻¹ * y, ?_, ?_⟩
  swap
  · show y = HGf hS hS' * ((HGf hS hS')⁻¹ * y)
    group
  convert hc using 1
  simp only [H, Subgroup.coe_inv, inv_inv]
  group

/- English proof (translation)
Introduce `D X u`. Conclude with `finLevi_holds X u`.
-/
theorem finLeviC_holds : Formalism.L2.SG.Pf.FinLeviC := by
  intro D X u
  exact finLevi_holds X u

end Final

end Formalism.L2.SG.Pf.FinLeviPf

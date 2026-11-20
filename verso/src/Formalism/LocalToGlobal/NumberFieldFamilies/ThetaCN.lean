import Formalism.LocalToGlobal.NumberFieldFamilies.ThetaCG
import Formalism.LocalToGlobal.NumberFieldFamilies.ThetaCR

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct ContDiff

namespace Formalism.L2.Fam.ThC

open Formalism.L2.Theta

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Tri

variable {R : Type} [CommRing R] {ρ : ℕ}

def UTri (T : Matrix (Fin ρ) (Fin ρ) R) : Prop := ∀ j i, i ≤ j → (T - 1) j i = 0

/- English proof (translation)
Use `h j i e.le` as an intermediate fact. Rewrite `this` using `[Matrix.sub_apply, Matrix.one_apply_ne e.ne', sub_zero]`. Then use the resulting hypothesis.
-/
theorem UTri.low {T : Matrix (Fin ρ) (Fin ρ) R} (h : UTri T) {j i : Fin ρ} (e : i < j) : T j i = 0 := by
  have := h j i e.le
  rwa [Matrix.sub_apply, Matrix.one_apply_ne e.ne', sub_zero] at this

/- English proof (translation)
Use `h i i le_rfl` as an intermediate fact. Rewrite `this` using `[Matrix.sub_apply, Matrix.one_apply_eq, sub_eq_zero]`. Then use the resulting hypothesis.
-/
theorem UTri.diag {T : Matrix (Fin ρ) (Fin ρ) R} (h : UTri T) (i : Fin ρ) : T i i = 1 := by
  have := h i i le_rfl
  rwa [Matrix.sub_apply, Matrix.one_apply_eq, sub_eq_zero] at this

/- English proof (translation)
Introduce `j i e`. Break down `e.lt_or_eq with e | rfl` into its components or cases. Rewrite using `[Matrix.sub_apply, Matrix.one_apply_ne e.ne', sub_zero, h1 j i e]`. Rewrite using `[Matrix.sub_apply, Matrix.one_apply_eq, h2, sub_self]`.
-/
theorem uTri_of {T : Matrix (Fin ρ) (Fin ρ) R} (h1 : ∀ j i, i < j → T j i = 0) (h2 : ∀ i, T i i = 1) : UTri T := by
  intro j i e
  rcases e.lt_or_eq with e | rfl
  · rw [Matrix.sub_apply, Matrix.one_apply_ne e.ne', sub_zero, h1 j i e]
  · rw [Matrix.sub_apply, Matrix.one_apply_eq, h2, sub_self]

/- English proof (translation)
Rewrite using `[Matrix.mul_apply, Finset.sum_eq_single i]`. Introduce `k _ hk`. Break down `lt_or_gt_of_ne hk with e | e` into its components or cases. Rewrite using `[h i k e, zero_mul]`. Rewrite using `[h' k i e, mul_zero]`.

Conclude with `fun h => absurd (Finset.mem_univ i) h`.
-/
theorem tri_diag {T W : Matrix (Fin ρ) (Fin ρ) R} (h : ∀ j i, i < j → T j i = 0) (h' : ∀ j i, i < j → W j i = 0) (i : Fin ρ) :
    (T * W) i i = T i i * W i i := by
  rw [Matrix.mul_apply, Finset.sum_eq_single i]
  · intro k _ hk
    rcases lt_or_gt_of_ne hk with e | e
    · rw [h i k e, zero_mul]
    · rw [h' k i e, mul_zero]
  · exact fun h => absurd (Finset.mem_univ i) h

/- English proof (translation)
Use `uTri_of (fun j i e => ?_) fun i => by rw [tri_diag (fun _ _ => h.low) (fun _ _ => h'.low), h.diag, h'.diag, one_mul]` and prove the remaining obligations. Rewrite using `[Matrix.mul_apply]`. Use `Finset.sum_eq_zero fun k _ => ?_` and prove the remaining obligations. Break down `lt_or_ge k j with a | a` into its components or cases. Rewrite using `[h.low a, zero_mul]`.

Rewrite using `[h'.low (lt_of_lt_of_le e a), mul_zero]`.
-/
theorem UTri.mul {T W : Matrix (Fin ρ) (Fin ρ) R} (h : UTri T) (h' : UTri W) : UTri (T * W) := by
  refine uTri_of (fun j i e => ?_) fun i => by rw [tri_diag (fun _ _ => h.low) (fun _ _ => h'.low), h.diag, h'.diag, one_mul]
  rw [Matrix.mul_apply]
  refine Finset.sum_eq_zero fun k _ => ?_
  rcases lt_or_ge k j with a | a
  · rw [h.low a, zero_mul]
  · rw [h'.low (lt_of_lt_of_le e a), mul_zero]

/- English proof (translation)
Establish `hij : i ≠ j` using `fun a => by rw [a] at e; omega`. Rewrite using `[Matrix.mul_apply, Finset.sum_eq_add i j hij, h.diag, h'.diag, one_mul, mul_one, add_comm]`. Introduce `k _ hk`. Distinguish the cases in `a : k < i`. Rewrite using `[h.low a, zero_mul]`.

Establish `: j < k`. Establish `h1 : k.1 ≠ i.1` using `fun b => hk.1 (Fin.ext b)`. Establish `h2 : k.1 ≠ j.1` using `fun b => hk.2 (Fin.ext b)`. Establish `h3 : ¬ k.1 < i.1` using `a`. Use `show j.1 < k.1`.

Use linear arithmetic over natural numbers and integers. Rewrite using `[h'.low this, mul_zero]`. Conclude with `fun h => absurd (Finset.mem_univ i) h`. Conclude with `fun h => absurd (Finset.mem_univ j) h`.
-/
theorem UTri.sup {T W : Matrix (Fin ρ) (Fin ρ) R} (h : UTri T) (h' : UTri W) {i j : Fin ρ} (e : j.1 = i.1 + 1) :
    (T * W) i j = T i j + W i j := by
  have hij : i ≠ j := fun a => by rw [a] at e; omega
  rw [Matrix.mul_apply, Finset.sum_eq_add i j hij, h.diag, h'.diag, one_mul, mul_one, add_comm]
  · intro k _ hk
    by_cases a : k < i
    · rw [h.low a, zero_mul]
    · have : j < k := by
        have h1 : k.1 ≠ i.1 := fun b => hk.1 (Fin.ext b)
        have h2 : k.1 ≠ j.1 := fun b => hk.2 (Fin.ext b)
        have h3 : ¬ k.1 < i.1 := a
        show j.1 < k.1
        omega
      rw [h'.low this, mul_zero]
  · exact fun h => absurd (Finset.mem_univ i) h
  · exact fun h => absurd (Finset.mem_univ j) h

/- English proof (translation)
Take `⟨g, hg⟩` from `LinearMap.exists_leftInverse_of_injective (Matrix.toLin' C) (LinearMap.ker_eq_bot.2 (Matrix.mulVec_injective_iff.2 h))`. Use `⟨LinearMap.toMatrix' g, ?_⟩` and prove the remaining obligations. Rewrite using `[← LinearMap.toMatrix'_toLin' C, ← LinearMap.toMatrix'_comp, hg, LinearMap.toMatrix'_id]`.
-/
theorem left_inv {K : Type} [Field K] {n : ℕ} (C : Matrix (Fin n) (Fin ρ) K) (h : LinearIndependent K C.transpose) :
    ∃ L : Matrix (Fin ρ) (Fin n) K, L * C = 1 := by
  obtain ⟨g, hg⟩ := LinearMap.exists_leftInverse_of_injective (Matrix.toLin' C)
    (LinearMap.ker_eq_bot.2 (Matrix.mulVec_injective_iff.2 h))
  refine ⟨LinearMap.toMatrix' g, ?_⟩
  rw [← LinearMap.toMatrix'_toLin' C, ← LinearMap.toMatrix'_comp, hg, LinearMap.toMatrix'_id]

end Tri

variable {D : D7} {A B : HSp D} {ι : A.V →ₗ[D.host.E] B.V} (d : BesDat A B ι)

def eA : Matrix (Fin B.rank) (Fin d.ρ) (AE D) := d.e.map (incA D)

def lA : Matrix (Fin d.ρ) (Fin B.rank) (AE D) := (left_inv d.e d.e_iso.1).choose.map (incA D)

/- English proof (translation)
Unfold `lA eA`. Rewrite using `[← Matrix.map_mul, (left_inv d.e d.e_iso.1).choose_spec, Matrix.map_one _ (incA D).map_zero (incA D).map_one]`.
-/
theorem lA_eA : HMul.hMul (lA d) (eA d) = (1 : Matrix (Fin d.ρ) (Fin d.ρ) (AE D)) := by
  unfold lA eA
  rw [← Matrix.map_mul, (left_inv d.e d.e_iso.1).choose_spec, Matrix.map_one _ (incA D).map_zero (incA D).map_one]

/- English proof (translation)
Rewrite using `[Matrix.mulVec_mulVec, lA_eA, Matrix.one_mulVec]`.
-/
theorem lA_vec (a : Fin d.ρ → AE D) : (lA d).mulVec ((eA d).mulVec a) = a := by
  rw [Matrix.mulVec_mulVec, lA_eA, Matrix.one_mulVec]

def tM (n : GA D B) : Matrix (Fin d.ρ) (Fin d.ρ) (AE D) := HMul.hMul (lA d) (HMul.hMul (mt B n) (eA d))

def bV (n : GA D B) (x : Fin B.rank → D.host.E) : Fin d.ρ → AE D := (lA d).mulVec ((mt B n).mulVec (ratV x) - ratV x)

def Perp (x : Fin B.rank → D.host.E) : Prop :=
  (Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) d.e * B.gram).mulVec x = 0

def Good (n : GA D B) : Prop :=
  HMul.hMul (mt B n) (eA d) = HMul.hMul (eA d) (tM d n) ∧ UTri (tM d n) ∧
    ∀ x, Perp d x → (mt B n).mulVec (ratV x) = ratV x + (eA d).mulVec (bV d n x)

variable {d}

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem mt_mul (g h : GA D B) : mt B (g * h) = mt B g * mt B h := rfl

/- English proof (translation)
Establish `e : tM d n = T` using `by rw [tM, h1, ← Matrix.mul_assoc, lA_eA, Matrix.one_mul]`. Use `⟨⟨e ▸ h1, e ▸ h2, fun x hx => ?_⟩, e⟩` and prove the remaining obligations. Take `⟨a, ha⟩` from `h3 x hx`. Rewrite using `[bV, ha, add_sub_cancel_left, lA_vec]`.
-/
theorem good_of {n : GA D B} (T : Matrix (Fin d.ρ) (Fin d.ρ) (AE D)) (h1 : HMul.hMul (mt B n) (eA d) = HMul.hMul (eA d) T)
    (h2 : UTri T) (h3 : ∀ x, Perp d x → ∃ a, (mt B n).mulVec (ratV x) = ratV x + (eA d).mulVec a) : Good d n ∧ tM d n = T := by
  have e : tM d n = T := by rw [tM, h1, ← Matrix.mul_assoc, lA_eA, Matrix.one_mul]
  refine ⟨⟨e ▸ h1, e ▸ h2, fun x hx => ?_⟩, e⟩
  obtain ⟨a, ha⟩ := h3 x hx
  rw [bV, ha, add_sub_cancel_left, lA_vec]

/- English proof (translation)
Establish `key : ∀ x, Perp d x → (mt B (n * n')).mulVec (ratV x) = ratV x + (eA d).mulVec (bV d n x + (tM d n).mulVec (bV d n' x))` using `fun x hx => by`. Rewrite using `[mt_mul, ← Matrix.mulVec_mulVec, h'.2.2 x hx, Matrix.mulVec_add, h.2.2 x hx, Matrix.mulVec_mulVec, h.1, ← Matrix.mulVec_mulVec, Matrix.mulVec_add, add_assoc]`. Use `⟨good_of _ ?_ (h.2.1.mul h'.2.1) fun x hx => ⟨_, key x hx⟩, fun x hx => ?_⟩` and prove the remaining obligations. Rewrite using `[mt_mul, Matrix.mul_assoc, h'.1, ← Matrix.mul_assoc, h.1, Matrix.mul_assoc]`. Rewrite using `[bV, key x hx, add_sub_cancel_left, lA_vec]`.
-/
theorem Good.mul {n n' : GA D B} (h : Good d n) (h' : Good d n') : (Good d (n * n') ∧ tM d (n * n') = tM d n * tM d n') ∧
    ∀ x, Perp d x → bV d (n * n') x = bV d n x + (tM d n).mulVec (bV d n' x) := by
  have key : ∀ x, Perp d x → (mt B (n * n')).mulVec (ratV x) =
      ratV x + (eA d).mulVec (bV d n x + (tM d n).mulVec (bV d n' x)) := fun x hx => by
    rw [mt_mul, ← Matrix.mulVec_mulVec, h'.2.2 x hx, Matrix.mulVec_add, h.2.2 x hx, Matrix.mulVec_mulVec, h.1,
      ← Matrix.mulVec_mulVec, Matrix.mulVec_add, add_assoc]
  refine ⟨good_of _ ?_ (h.2.1.mul h'.2.1) fun x hx => ⟨_, key x hx⟩, fun x hx => ?_⟩
  · rw [mt_mul, Matrix.mul_assoc, h'.1, ← Matrix.mul_assoc, h.1, Matrix.mul_assoc]
  · rw [bV, key x hx, add_sub_cancel_left, lA_vec]

variable (d) in

def valN (n : GA D B) : AE D :=
  (∑ i : Fin d.ρ, ∑ j : Fin d.ρ, if j.1 = i.1 + 1 then incA D (d.c i) * (tM d n - 1) i j else 0) +
    ∑ i : Fin d.ρ, if i.1 + 1 = d.ρ then incA D (d.c i) * bV d n d.z i else 0

/- English proof (translation)
Rewrite using `[Algebra.trace_apply, Algebra.trace_apply, ← LinearMap.trace_baseChange, Algebra.baseChange_lmul]`. Both sides reduce to the same expression.
-/
theorem trace_gen {F E R : Type} [Field F] [Field E] [Algebra F E] [FiniteDimensional F E] [CommRing R] [Algebra F R] (r : E) :
    Algebra.trace R (R ⊗[F] E) (inclR R r) = algebraMap F R (Algebra.trace F E r) := by
  rw [Algebra.trace_apply, Algebra.trace_apply, ← LinearMap.trace_baseChange, Algebra.baseChange_lmul]
  rfl

def NFCpt (D : D7) : Prop := ∀ (B : HSp D) (ρ : ℕ) (e : Matrix (Fin B.rank) (Fin ρ) D.host.E), IsIsoSub B e → CoCpt (NFlag B e)

end Formalism.L2.Fam.ThC

end

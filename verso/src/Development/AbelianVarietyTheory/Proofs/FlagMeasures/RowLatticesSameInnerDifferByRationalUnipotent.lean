import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.NGData
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.TermLoc
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.LocClosed
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.Saturated
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SesquilinearRowSplitting.CoreStepOf
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SesquilinearRowSplitting.FrameReduction
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SesquilinearRowSplitting.MeasureIsomorphismAtInfinity
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SesquilinearRowSplitting.SecondDualReduction
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SesquilinearRowSplitting.AdjointActionReduction

open scoped Classical
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SameInner

section Gen

variable {E : Type} [Field E] [NumberField E] [StarRing E] {S : HSpace E} {r : ℕ}

/- English proof (translation)
The claim follows from `Formalism.MainNotions.LatticeGluingRadicals.b_herm y x`.
-/
theorem herm (x y : S.V) : S.hT x y = star (S.hT y x) := Formalism.MainNotions.LatticeGluingRadicals.b_herm y x

def pr (e f : Fin r → S.V) : S.V →ₗ[E] S.V :=
  LinearMap.id - ∑ a, (S.hT (f a)).smulRight (e a) - ∑ a, (S.hT (e a)).smulRight (f a)

/- English proof (translation)
Simplify using `[pr, LinearMap.sub_apply, LinearMap.sum_apply, LinearMap.smulRight_apply]`.
-/
theorem pr_apply (e f : Fin r → S.V) (v : S.V) :
    pr e f v = v - ∑ a, S.hT (f a) v • e a - ∑ a, S.hT (e a) v • f a := by
  simp [pr, LinearMap.sub_apply, LinearMap.sum_apply, LinearMap.smulRight_apply]

def DualFr (e f : Fin r → S.V) : Prop :=
  (∀ a b, S.hT (e a) (e b) = 0) ∧ (∀ a b, S.hT (f a) (f b) = 0) ∧
    ∀ a b, S.hT (e a) (f b) = if a = b then 1 else 0

variable {e f : Fin r → S.V}

/- English proof (translation)
Rewrite using `[herm, h.2.2 b a]`. Distinguish the cases in `hab : a = b`. Substitute `hab` using the available equality. Simplify using the standard rewrite rules. Simplify using `[hab, Ne.symm hab]`.
-/
theorem fe (h : DualFr e f) (a b : Fin r) : S.hT (f a) (e b) = if a = b then 1 else 0 := by
  rw [herm, h.2.2 b a]
  by_cases hab : a = b
  · subst hab; simp
  · simp [hab, Ne.symm hab]

/- English proof (translation)
Simplify using `[pr_apply, h.1, fe h]`.
-/
theorem pr_e (h : DualFr e f) (b : Fin r) : pr e f (e b) = 0 := by
  simp [pr_apply, h.1, fe h]

/- English proof (translation)
Simplify using `[pr_apply, h.2.1, h.2.2]`.
-/
theorem pr_f (h : DualFr e f) (b : Fin r) : pr e f (f b) = 0 := by
  simp [pr_apply, h.2.1, h.2.2]

/- English proof (translation)
Simplify using `[pr_apply, map_sub, map_sum, map_smul, h.1, h.2.2]`.
-/
theorem perp_e (h : DualFr e f) (b : Fin r) (v : S.V) : S.hT (e b) (pr e f v) = 0 := by
  simp [pr_apply, map_sub, map_sum, map_smul, h.1, h.2.2]

/- English proof (translation)
Simplify using `[pr_apply, map_sub, map_sum, map_smul, h.2.1, fe h]`.
-/
theorem perp_f (h : DualFr e f) (b : Fin r) (v : S.V) : S.hT (f b) (pr e f v) = 0 := by
  simp [pr_apply, map_sub, map_sum, map_smul, h.2.1, fe h]

/- English proof (translation)
Simplify using `[pr_apply, he, hf]`.
-/
theorem pr_of_perp (w : S.V) (he : ∀ a, S.hT (e a) w = 0) (hf : ∀ a, S.hT (f a) w = 0) :
    pr e f w = w := by
  simp [pr_apply, he, hf]

/- English proof (translation)
Rewrite using `[pr_apply]`. Normalize the expressions using the abelian group laws.
-/
theorem decomp (e f : Fin r → S.V) (v : S.V) :
    v = ∑ a, S.hT (f a) v • e a + ∑ a, S.hT (e a) v • f a + pr e f v := by
  rw [pr_apply]; abel

/- English proof (translation)
Establish `h1 : S.hT x u = 0`. Proceed by induction on `hx using Submodule.span_induction with`. Consider the case `mem y hy => obtain ⟨a, rfl⟩ := hy`. Conclude with `hu a`. Consider the case `zero => simp`.

Consider the case `add y z _ _ hy hz => simp [hy, hz]`. Consider the case `smul c y _ hy => simp [hy]`. Conclude with `⟨h1, by rw [herm, h1]; simp⟩`.
-/
theorem perpX {u x : S.V} (hu : ∀ a, S.hT (e a) u = 0) (hx : x ∈ Submodule.span E (Set.range e)) :
    S.hT x u = 0 ∧ S.hT u x = 0 := by
  have h1 : S.hT x u = 0 := by
    induction hx using Submodule.span_induction with
    | mem y hy => obtain ⟨a, rfl⟩ := hy; exact hu a
    | zero => simp
    | add y z _ _ hy hz => simp [hy, hz]
    | smul c y _ hy => simp [hy]
  exact ⟨h1, by rw [herm, h1]; simp⟩

/- English proof (translation)
Proceed by induction on `hx using Submodule.span_induction with`. Consider the case `mem y hy => obtain ⟨a, rfl⟩ := hy`. Conclude with `hv a`. Consider the case `zero => simp`. Consider the case `add y z _ _ hy hz => simp [hy, hz]`.

Consider the case `smul c y _ hy => simp [hy]`.
-/
theorem perp_span {g : Fin r → S.V} {v x : S.V} (hv : ∀ a, S.hT v (g a) = 0)
    (hx : x ∈ Submodule.span E (Set.range g)) : S.hT v x = 0 := by
  induction hx using Submodule.span_induction with
  | mem y hy => obtain ⟨a, rfl⟩ := hy; exact hv a
  | zero => simp
  | add y z _ _ hy hz => simp [hy, hz]
  | smul c y _ hy => simp [hy]

/- English proof (translation)
The claim follows from `(perpX (fun a => perp_span (fun b => h.1 a b) hy) hx).1`.
-/
theorem isoX (h : DualFr e f) {x y : S.V} (hx : x ∈ Submodule.span E (Set.range e))
    (hy : y ∈ Submodule.span E (Set.range e)) : S.hT x y = 0 :=
  (perpX (fun a => perp_span (fun b => h.1 a b) hy) hx).1

/- English proof (translation)
Establish `: Submodule.span E (Set.range e) ≤ LinearMap.ker (pr e f)`. Rewrite using `[Submodule.span_le]`. Introduce and unpack `_ ⟨a, rfl⟩`. Conclude with `pr_e h a`. Conclude with `this hx`.
-/
theorem pr_spanE (h : DualFr e f) {x : S.V} (hx : x ∈ Submodule.span E (Set.range e)) : pr e f x = 0 := by
  have : Submodule.span E (Set.range e) ≤ LinearMap.ker (pr e f) := by
    rw [Submodule.span_le]; rintro _ ⟨a, rfl⟩; exact pr_e h a
  exact this hx

/- English proof (translation)
Establish `: Submodule.span E (Set.range f) ≤ LinearMap.ker (pr e f)`. Rewrite using `[Submodule.span_le]`. Introduce and unpack `_ ⟨a, rfl⟩`. Conclude with `pr_f h a`. Conclude with `this hx`.
-/
theorem pr_spanF (h : DualFr e f) {x : S.V} (hx : x ∈ Submodule.span E (Set.range f)) : pr e f x = 0 := by
  have : Submodule.span E (Set.range f) ≤ LinearMap.ker (pr e f) := by
    rw [Submodule.span_le]; rintro _ ⟨a, rfl⟩; exact pr_f h a
  exact this hx

/- English proof (translation)
Establish `hf : ∀ a, S.hT (f a) t = 0` using `fun a => perp_span (fun b => h.2.1 a b) ht`. Rewrite using `[← pr_of_perp t he hf, pr_spanF h ht]`.
-/
theorem spanF_zero (h : DualFr e f) {t : S.V} (ht : t ∈ Submodule.span E (Set.range f))
    (he : ∀ a, S.hT (e a) t = 0) : t = 0 := by
  have hf : ∀ a, S.hT (f a) t = 0 := fun a => perp_span (fun b => h.2.1 a b) ht
  rw [← pr_of_perp t he hf, pr_spanF h ht]

/- English proof (translation)
Rewrite using `[pr_apply]`. Simplify using `only [hu, zero_smul, Finset.sum_const_zero, sub_zero, sub_sub_cancel_left]`. Conclude with `Submodule.neg_mem _ (Submodule.sum_mem _ fun a _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨a, rfl⟩))`.
-/
theorem pr_sub_mem (u : S.V) (hu : ∀ a, S.hT (e a) u = 0) :
    pr e f u - u ∈ Submodule.span E (Set.range e) := by
  rw [pr_apply]
  simp only [hu, zero_smul, Finset.sum_const_zero, sub_zero, sub_sub_cancel_left]
  exact Submodule.neg_mem _ (Submodule.sum_mem _ fun a _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨a, rfl⟩))

end Gen

end GlobalTheory.SameInner

namespace GlobalTheory.SameInner

section Gen2

variable {E : Type} [Field E] [NumberField E] [StarRing E] {S : HSpace E} {r : ℕ}
variable {e f fa fb : Fin r → S.V}

/- English proof (translation)
Rewrite using `[herm, hw a]`. Simplify using the standard rewrite rules.
-/
theorem perp_e' {w : S.V} (hw : ∀ a, S.hT (e a) w = 0) (a : Fin r) : S.hT w (e a) = 0 := by
  rw [herm, hw a]; simp

/- English proof (translation)
Establish `h1` using `perp_e' hwe`. Establish `h2` using `perp_e' (e := f) hwf`. Simplify using `[map_add, map_sum, LinearMap.add_apply, LinearMap.sum_apply, LinearMap.map_smulₛₗ₂, map_smul, h.1, h.2.1, h.2.2, fe h, hwe, hwf, hwe', hwf', h1, h2, Finset.sum_add_distrib]`. Rewrite using `[add_comm]`. Apply the tactic sequence `congr 1 <;> refine Finset.sum_congr rfl fun x _ => ?_ <;> simp [starRingEnd_apply, mul_comm]`.
-/
theorem expand (h : DualFr e f) (c d c' d' : Fin r → E) (w w' : S.V)
    (hwe : ∀ a, S.hT (e a) w = 0) (hwf : ∀ a, S.hT (f a) w = 0)
    (hwe' : ∀ a, S.hT (e a) w' = 0) (hwf' : ∀ a, S.hT (f a) w' = 0) :
    S.hT (∑ a, c a • e a + ∑ a, d a • f a + w) (∑ a, c' a • e a + ∑ a, d' a • f a + w') =
      ∑ a, (star (c a) * d' a + star (d a) * c' a) + S.hT w w' := by
  have h1 := perp_e' hwe
  have h2 := perp_e' (e := f) hwf
  simp [map_add, map_sum, LinearMap.add_apply, LinearMap.sum_apply, LinearMap.map_smulₛₗ₂, map_smul,
    h.1, h.2.1, h.2.2, fe h, hwe, hwf, hwe', hwf', h1, h2, Finset.sum_add_distrib]
  rw [add_comm]
  congr 1 <;> refine Finset.sum_congr rfl fun x _ => ?_ <;> simp [starRingEnd_apply, mul_comm]

def G (e fa fb : Fin r → S.V) (σ : S.V →ₗ[E] S.V) : S.V →ₗ[E] S.V :=
  ∑ a, (S.hT (fa a)).smulRight (e a) + ∑ a, (S.hT (e a)).smulRight (fb a) + pr e fb ∘ₗ σ ∘ₗ pr e fa

/- English proof (translation)
Simplify using `[G, LinearMap.add_apply, LinearMap.sum_apply, LinearMap.smulRight_apply]`.
-/
theorem G_apply (σ : S.V →ₗ[E] S.V) (v : S.V) :
    G e fa fb σ v = ∑ a, S.hT (fa a) v • e a + ∑ a, S.hT (e a) v • fb a + pr e fb (σ (pr e fa v)) := by
  simp [G, LinearMap.add_apply, LinearMap.sum_apply, LinearMap.smulRight_apply]

variable (σ : S.V ≃ₗ[E] S.V) (hσ : ∀ x y, S.hT (σ x) (σ y) = S.hT x y)
  (hσX : ∀ x ∈ Submodule.span E (Set.range e), σ x ∈ Submodule.span E (Set.range e))
  (hσX' : ∀ x ∈ Submodule.span E (Set.range e), σ.symm x ∈ Submodule.span E (Set.range e))

include hσ hσX' in
/- English proof (translation)
Use `hσ (σ.symm (e a)) u` as an intermediate fact. Rewrite `this` using `[LinearEquiv.apply_symm_apply]`. Rewrite using `[this]`. Conclude with `(perpX hu (hσX' _ (Submodule.subset_span ⟨a, rfl⟩))).1`.
-/
theorem sig_perp {u : S.V} (hu : ∀ a, S.hT (e a) u = 0) (a : Fin r) : S.hT (e a) (σ u) = 0 := by
  have := hσ (σ.symm (e a)) u
  rw [LinearEquiv.apply_symm_apply] at this
  rw [this]
  exact (perpX hu (hσX' _ (Submodule.subset_span ⟨a, rfl⟩))).1

include hσ hσX' in
/- English proof (translation)
Establish `k : ∀ x ∈ Submodule.span E (Set.range e), ∀ x' ∈ Submodule.span E (Set.range e), S.hT (σ u + x) (σ u' + x') = S.hT u u'`. Introduce `x hx x' hx'`. Establish `p1` using `sig_perp σ hσ hσX' hu`. Establish `p2` using `sig_perp σ hσ hσX' hu'`. Simplify using `only [map_add, LinearMap.add_apply, hσ, (perpX p2 hx).1, (perpX p1 hx').2, isoX hb hx hx']`.

Simplify using the standard rewrite rules. Use `k _ (pr_sub_mem (f := fb) _ (sig_perp σ hσ hσX' hu)) _ (pr_sub_mem (f := fb) _ (sig_perp σ hσ hσX' hu'))` as an intermediate fact. Simplify using `using this`.
-/
theorem pr_sig_isom (hb : DualFr e fb) {u u' : S.V} (hu : ∀ a, S.hT (e a) u = 0)
    (hu' : ∀ a, S.hT (e a) u' = 0) :
    S.hT (pr e fb (σ u)) (pr e fb (σ u')) = S.hT u u' := by
  have k : ∀ x ∈ Submodule.span E (Set.range e), ∀ x' ∈ Submodule.span E (Set.range e),
      S.hT (σ u + x) (σ u' + x') = S.hT u u' := by
    intro x hx x' hx'
    have p1 := sig_perp σ hσ hσX' hu
    have p2 := sig_perp σ hσ hσX' hu'
    simp only [map_add, LinearMap.add_apply, hσ, (perpX p2 hx).1, (perpX p1 hx').2, isoX hb hx hx']
    simp
  have := k _ (pr_sub_mem (f := fb) _ (sig_perp σ hσ hσX' hu)) _ (pr_sub_mem (f := fb) _ (sig_perp σ hσ hσX' hu'))
  simpa using this

include hσ hσX' in
/- English proof (translation)
Establish `h1` using `expand ha (fun a => S.hT (fa a) v) (fun a => S.hT (e a) v) (fun a => S.hT (fa a) v') (fun a => S.hT (e a) v') (pr e fa v) (pr e fa v') (fun a => perp_e ha a v) (fun a => perp_f ha a v) (fun a => perp_e ha a v') (fun a => perp_f ha a v')`. Establish `h2` using `expand hb (fun a => S.hT (fa a) v) (fun a => S.hT (e a) v) (fun a => S.hT (fa a) v') (fun a => S.hT (e a) v') (pr e fb (σ (pr e fa v))) (pr e fb (σ (pr e fa v'))) (fun a => perp_e hb a _) (fun a => perp_f hb a _) (fun a => perp_e hb a _) (fun a => perp_f hb a _)`. Use `beta_reduce at h1 h2`. Rewrite `h1` using `[← decomp e fa v, ← decomp e fa v']`. Rewrite using `[G_apply, G_apply]`.

Simplify using `only [LinearEquiv.coe_coe]`. Rewrite using `[h2, h1, pr_sig_isom σ hσ hσX' hb (fun a => perp_e ha a v) (fun a => perp_e ha a v')]`.
-/
theorem G_isom (ha : DualFr e fa) (hb : DualFr e fb) (v v' : S.V) :
    S.hT (G e fa fb σ v) (G e fa fb σ v') = S.hT v v' := by
  have h1 := expand ha (fun a => S.hT (fa a) v) (fun a => S.hT (e a) v) (fun a => S.hT (fa a) v')
    (fun a => S.hT (e a) v') (pr e fa v) (pr e fa v') (fun a => perp_e ha a v) (fun a => perp_f ha a v)
    (fun a => perp_e ha a v') (fun a => perp_f ha a v')
  have h2 := expand hb (fun a => S.hT (fa a) v) (fun a => S.hT (e a) v) (fun a => S.hT (fa a) v')
    (fun a => S.hT (e a) v') (pr e fb (σ (pr e fa v))) (pr e fb (σ (pr e fa v')))
    (fun a => perp_e hb a _) (fun a => perp_f hb a _) (fun a => perp_e hb a _) (fun a => perp_f hb a _)
  beta_reduce at h1 h2
  rw [← decomp e fa v, ← decomp e fa v'] at h1
  rw [G_apply, G_apply]
  simp only [LinearEquiv.coe_coe]
  rw [h2, h1, pr_sig_isom σ hσ hσX' hb (fun a => perp_e ha a v) (fun a => perp_e ha a v')]

include hσ hσX' in
/- English proof (translation)
Rewrite using `[← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]`. Introduce `v hv`. Rewrite `hv` using `[LinearMap.mem_ker]`. Use `S.nondeg.1 v fun y => ?_` and prove the remaining obligations. Rewrite using `[← G_isom σ hσ hσX' ha hb v y, hv]`.

Simplify using the standard rewrite rules.
-/
theorem G_inj (ha : DualFr e fa) (hb : DualFr e fb) : Function.Injective (G e fa fb σ) := by
  rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
  intro v hv
  rw [LinearMap.mem_ker] at hv
  refine S.nondeg.1 v fun y => ?_
  rw [← G_isom σ hσ hσX' ha hb v y, hv]; simp

/- English proof (translation)
Simplify using `[G_apply, fe ha, ha.1, pr_e ha]`.
-/
theorem G_e (ha : DualFr e fa) (b : Fin r) : G e fa fb σ (e b) = e b := by
  simp [G_apply, fe ha, ha.1, pr_e ha]

/- English proof (translation)
Simplify using `[G_apply, ha.2.1, ha.2.2, pr_f ha]`.
-/
theorem G_f (ha : DualFr e fa) (b : Fin r) : G e fa fb σ (fa b) = fb b := by
  simp [G_apply, ha.2.1, ha.2.2, pr_f ha]

/- English proof (translation)
Establish `: Submodule.span E (Set.range e) ≤ LinearMap.ker (G e fa fb (σ : S.V →ₗ[E] S.V) - LinearMap.id)`. Rewrite using `[Submodule.span_le]`. Introduce and unpack `_ ⟨a, rfl⟩`. Simplify using `[G_e σ ha]`. Use `this hx` as an intermediate fact.

Simplify `this` using `[sub_eq_zero]`.
-/
theorem G_X (ha : DualFr e fa) {x : S.V} (hx : x ∈ Submodule.span E (Set.range e)) : G e fa fb σ x = x := by
  have : Submodule.span E (Set.range e) ≤ LinearMap.ker (G e fa fb (σ : S.V →ₗ[E] S.V) - LinearMap.id) := by
    rw [Submodule.span_le]; rintro _ ⟨a, rfl⟩
    simp [G_e σ ha]
  have := this hx
  simpa [sub_eq_zero] using this

/- English proof (translation)
Simplify using `[G_apply, he, hf, pr_of_perp w he hf]`.
-/
theorem G_w {w : S.V} (he : ∀ a, S.hT (e a) w = 0) (hf : ∀ a, S.hT (fa a) w = 0) :
    G e fa fb σ w = pr e fb (σ w) := by
  simp [G_apply, he, hf, pr_of_perp w he hf]

include hσ hσX hσX' in
/- English proof (translation)
Establish `hσ' : ∀ x y, S.hT (σ.symm x) (σ.symm y) = S.hT x y`. Introduce `x y`. Rewrite using `[← hσ]`. Simplify using the standard rewrite rules. Establish `hy : ∀ a, S.hT (e a) (σ.symm x) = 0` using `sig_perp σ.symm hσ' (by simpa using hσX) hx`.

Use `set y := σ.symm x`. Use `set p := pr e fa y`. Establish `hp : ∀ a, S.hT (e a) p = 0` using `fun a => perp_e ha a y`. Establish `e1 : G e fa fb σ y - x = (∑ a, S.hT (fa a) y • e a) + (pr e fb (σ p) - σ p) + σ (p - y)`. Rewrite using `[G_apply]`.

Simplify using `only [hy, zero_smul, Finset.sum_const_zero, add_zero, map_sub]`. Simplify using `[y]`. Normalize the expressions using the abelian group laws. Rewrite using `[e1]`. Use `Submodule.add_mem _ (Submodule.add_mem _ ?_ (pr_sub_mem _ (sig_perp σ hσ hσX' hp))) ?_` and prove the remaining obligations.

Conclude with `Submodule.sum_mem _ fun a _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨a, rfl⟩)`. Conclude with `hσX _ (pr_sub_mem _ hy)`.
-/
theorem G_perp (ha : DualFr e fa) (hb : DualFr e fb) {x : S.V} (hx : ∀ a, S.hT (e a) x = 0) :
    G e fa fb σ (σ.symm x) - x ∈ Submodule.span E (Set.range e) := by
  have hσ' : ∀ x y, S.hT (σ.symm x) (σ.symm y) = S.hT x y := by
    intro x y; rw [← hσ]; simp
  have hy : ∀ a, S.hT (e a) (σ.symm x) = 0 := sig_perp σ.symm hσ' (by simpa using hσX) hx
  set y := σ.symm x
  set p := pr e fa y
  have hp : ∀ a, S.hT (e a) p = 0 := fun a => perp_e ha a y
  have e1 : G e fa fb σ y - x = (∑ a, S.hT (fa a) y • e a) + (pr e fb (σ p) - σ p) + σ (p - y) := by
    rw [G_apply]; simp only [hy, zero_smul, Finset.sum_const_zero, add_zero, map_sub]
    simp [y]; abel
  rw [e1]
  refine Submodule.add_mem _ (Submodule.add_mem _ ?_ (pr_sub_mem _ (sig_perp σ hσ hσX' hp))) ?_
  · exact Submodule.sum_mem _ fun a _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨a, rfl⟩)
  · exact hσX _ (pr_sub_mem _ hy)

end Gen2

end GlobalTheory.SameInner

namespace GlobalTheory.SameInner

section Gen3

variable {E : Type} [Field E] [NumberField E] [StarRing E] {S : HSpace E} {r : ℕ}

open Formalism.L2.SG.Saturated in
/- English proof (translation)
Rewrite using `[latSpan, Submodule.span_le]`. Introduce and unpack `_ ⟨a, x, _, rfl⟩`. Conclude with `(Submodule.span E (Set.range v)).smul_mem x (Submodule.subset_span (Set.mem_range_self a))`.
-/
theorem latSpan_le (aa : Fin r → FractionalIdeal (nonZeroDivisors (𝓞 E)) E) (v : Fin r → S.V) :
    latSpan aa v ≤ (Submodule.span E (Set.range v)).restrictScalars (𝓞 E) := by
  rw [latSpan, Submodule.span_le]
  rintro _ ⟨a, x, _, rfl⟩
  exact (Submodule.span E (Set.range v)).smul_mem x (Submodule.subset_span (Set.mem_range_self a))

open Formalism.L2.SG.Saturated in
/- English proof (translation)
Rewrite using `[latSpan, latSpan, Submodule.map_span]`. Use `congr 1`. Use extensionality with `y`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨_, ⟨a, x, hx, rfl⟩, rfl⟩`.

Conclude with `⟨a, x, hx, by simp⟩`. Introduce and unpack `⟨a, x, hx, rfl⟩`. Conclude with `⟨_, ⟨a, x, hx, rfl⟩, by simp⟩`.
-/
theorem map_latSpan (aa : Fin r → FractionalIdeal (nonZeroDivisors (𝓞 E)) E) (v : Fin r → S.V)
    (φ : S.V →ₗ[E] S.V) :
    (latSpan aa v).map (φ.restrictScalars (𝓞 E)) = latSpan aa (fun a => φ (v a)) := by
  rw [latSpan, latSpan, Submodule.map_span]
  congr 1
  ext y
  constructor
  · rintro ⟨_, ⟨a, x, hx, rfl⟩, rfl⟩
    exact ⟨a, x, hx, by simp⟩
  · rintro ⟨a, x, hx, rfl⟩
    exact ⟨_, ⟨a, x, hx, rfl⟩, by simp⟩

/- English proof (translation)
Simplify using `[orth, Submodule.mem_iInf]`.
-/
theorem mem_orth_iff {U : Submodule E S.V} {v : S.V} : v ∈ orth S U ↔ ∀ x ∈ U, S.hT x v = 0 := by
  simp [orth, Submodule.mem_iInf]

variable {T : E} (F0 : FlagG S r T)

/- English proof (translation)
Rewrite using `[mem_orth_iff]`. Prove the components needed by the constructor for the conclusion. Introduce `h a`. Conclude with `h _ (Submodule.subset_span ⟨a, rfl⟩)`. Introduce `h x hx`.

Conclude with `(perpX h hx).1`.
-/
theorem perp_iff {v : S.V} : v ∈ orth S F0.X ↔ ∀ a, S.hT (F0.e a) v = 0 := by
  rw [mem_orth_iff]
  constructor
  · intro h a; exact h _ (Submodule.subset_span ⟨a, rfl⟩)
  · intro h x hx; exact (perpX h hx).1

/- English proof (translation)
Establish `hp' : v ∈ orth S F0.X` using `(perp_iff F0).2 hp`. Unfold `Lsub Lrep`. Conclude with `Submodule.mem_inf.2 ⟨Submodule.mem_sup_left (Submodule.mem_inf.2 ⟨hv, hp'⟩), hp'⟩`.
-/
theorem mem_Lsub {Λ : Submodule (𝓞 E) S.V} {v : S.V} (hv : v ∈ Λ) (hp : ∀ a, S.hT (F0.e a) v = 0) :
    v ∈ Lsub Λ (⟨F0, F0.z⟩ : LFlag S r T) := by
  have hp' : v ∈ orth S F0.X := (perp_iff F0).2 hp
  unfold Lsub Lrep
  exact Submodule.mem_inf.2 ⟨Submodule.mem_sup_left (Submodule.mem_inf.2 ⟨hv, hp'⟩), hp'⟩

/- English proof (translation)
Take `⟨h1, -⟩` from `hv`. Take `⟨m, ⟨hm, hmp⟩, x, hx, rfl⟩` from `Submodule.mem_sup.1 h1`. Use `⟨m, hm, (perp_iff F0).1 hmp, ?_⟩` and prove the remaining obligations. Simplify `hx` using `[Xsp, FlagG.X]`.
-/
theorem of_mem_Lsub {Λ : Submodule (𝓞 E) S.V} {v : S.V} (hv : v ∈ Lsub Λ (⟨F0, F0.z⟩ : LFlag S r T)) :
    ∃ m ∈ Λ, (∀ a, S.hT (F0.e a) m = 0) ∧ v - m ∈ Submodule.span E (Set.range F0.e) := by
  obtain ⟨h1, -⟩ := hv
  obtain ⟨m, ⟨hm, hmp⟩, x, hx, rfl⟩ := Submodule.mem_sup.1 h1
  refine ⟨m, hm, (perp_iff F0).1 hmp, ?_⟩
  simpa [Xsp, FlagG.X] using hx

open Formalism.L2.SG.Saturated in
/- English proof (translation)
Rewrite `hm` using `[hΛ]`. Take `⟨y, hy, t, ht, rfl⟩` from `Submodule.mem_sup.1 hm`. Take `⟨s, hs, l, hl, rfl⟩` from `Submodule.mem_sup.1 hy`. Establish `hs'` using `latSpan_le aa F0.e hs`. Establish `ht'` using `latSpan_le aa' f ht`.

Establish `ht0 : t = 0`. Use `spanF_zero hd ht' fun a => ?_` and prove the remaining obligations. Use `hp a` as an intermediate fact. Simplify using `only [map_add, isoX hd (Submodule.subset_span ⟨a, rfl⟩) hs', (hL l hl a).1, zero_add] at this`. Conclude with `this`.

Conclude with `⟨s, hs', l, hl, by simp [ht0]⟩`.
-/
theorem split_perp {f : Fin r → S.V} (hd : DualFr F0.e f) {aa aa' : Fin r → FractionalIdeal (nonZeroDivisors (𝓞 E)) E}
    {L Λ : Submodule (𝓞 E) S.V} (hL : ∀ x ∈ L, ∀ a, S.hT (F0.e a) x = 0 ∧ S.hT (f a) x = 0)
    (hΛ : Λ = latSpan aa F0.e ⊔ L ⊔ latSpan aa' f) {m : S.V} (hm : m ∈ Λ) (hp : ∀ a, S.hT (F0.e a) m = 0) :
    ∃ s ∈ Submodule.span E (Set.range F0.e), ∃ l ∈ L, m = s + l := by
  rw [hΛ] at hm
  obtain ⟨y, hy, t, ht, rfl⟩ := Submodule.mem_sup.1 hm
  obtain ⟨s, hs, l, hl, rfl⟩ := Submodule.mem_sup.1 hy
  have hs' := latSpan_le aa F0.e hs
  have ht' := latSpan_le aa' f ht
  have ht0 : t = 0 := by
    refine spanF_zero hd ht' fun a => ?_
    have := hp a
    simp only [map_add, isoX hd (Submodule.subset_span ⟨a, rfl⟩) hs', (hL l hl a).1, zero_add] at this
    exact this
  exact ⟨s, hs', l, hl, by simp [ht0]⟩

end Gen3

end GlobalTheory.SameInner

namespace GlobalTheory.SameInner

section Gen4

variable {E : Type} [Field E] [NumberField E] [StarRing E] {S : HSpace E} {r : ℕ} {T : E} (F0 : FlagG S r T)

open Formalism.L2.SG.Saturated in
/- English proof (translation)
Establish `hA : ∀ l ∈ La, G F0.e fa fb σ l ∈ Lb`. Introduce `l hl`. Establish `hle : ∀ a, S.hT (F0.e a) l = 0` using `fun a => (hLa l hl a).1`. Establish `hσl : σ l ∈ Formalism.HermitianLatticesTheory.gmap σ Λa`. Use `Submodule.mem_map_of_mem (f := ((σ : S.V →ₗ[E] S.V).restrictScalars (𝓞 E))) ?_` and prove the remaining obligations.

Rewrite using `[hΛa]`. Conclude with `Submodule.mem_sup_left (Submodule.mem_sup_right hl)`. Establish `hp` using `sig_perp σ hσ hσX' hle`. Establish `h1` using `mem_Lsub F0 hσl hp`. Rewrite `h1` using `[hL]`.

Take `⟨m, hm, hmp, hmx⟩` from `of_mem_Lsub F0 h1`. Take `⟨s, hs, l', hl', rfl⟩` from `split_perp F0 hb hLb hΛb hm hmp`. Establish `e1 : σ l = l' + ((σ l - (s + l')) + s)` using `by abel`. Rewrite using `[G_w σ hle (fun a => (hLa l hl a).2)]`. Apply the tactic sequence `try simp only [LinearEquiv.coe_coe]`.

Rewrite using `[e1, map_add, pr_spanE hb (Submodule.add_mem _ hmx hs), add_zero, pr_of_perp l' (fun a => (hLb l' hl' a).1) (fun a => (hLb l' hl' a).2)]`. Conclude with `hl'`. Establish `hB : ∀ l' ∈ Lb, ∃ l ∈ La, G F0.e fa fb σ l = l'`. Introduce `l' hl'`. Establish `hle' : ∀ a, S.hT (F0.e a) l' = 0` using `fun a => (hLb l' hl' a).1`.

Establish `hl'Λ : l' ∈ Λb` using `by rw [hΛb]; exact Submodule.mem_sup_left (Submodule.mem_sup_right hl')`. Establish `h1` using `mem_Lsub F0 hl'Λ hle'`. Rewrite `h1` using `[← hL]`. Take `⟨m, hm, hmp, hmx⟩` from `of_mem_Lsub F0 h1`. Take `⟨m0, hm0, rfl⟩` from `Submodule.mem_map.1 hm`.

Simplify using `only [LinearMap.coe_restrictScalars, LinearEquiv.coe_coe] at hmp hmx`. Establish `hm0p : ∀ a, S.hT (F0.e a) m0 = 0`. Introduce `a`. Rewrite using `[← hσ]`. Conclude with `(perpX hmp (hσX _ (Submodule.subset_span ⟨a, rfl⟩))).1`.

Take `⟨s, hs, l, hl, rfl⟩` from `split_perp F0 ha hLa hΛa hm0 hm0p`. Use `⟨l, hl, ?_⟩` and prove the remaining obligations. Establish `e1 : σ l = l' - ((l' - σ (s + l)) + σ s)` using `by rw [map_add]; abel`. Rewrite using `[G_w σ (fun a => (hLa l hl a).1) (fun a => (hLa l hl a).2)]`. Apply the tactic sequence `try simp only [LinearEquiv.coe_coe]`.

Rewrite using `[e1, map_sub, pr_spanE hb (Submodule.add_mem _ hmx (hσX _ hs)), sub_zero, pr_of_perp l' hle' (fun a => (hLb l' hl' a).2)]`. Establish `hLL : La.map ((G F0.e fa fb σ).restrictScalars (𝓞 E)) = Lb`. Apply `le_antisymm` to reduce the goal to its premises. Rewrite using `[Submodule.map_le_iff_le_comap]`. Introduce `l hl`.

Conclude with `hA l hl`. Introduce `l' hl'`. Take `⟨l, hl, he⟩` from `hB l' hl'`. Conclude with `⟨l, hl, he⟩`. Establish `g1 : (fun a => G F0.e fa fb σ (F0.e a)) = F0.e` using `funext (G_e σ ha)`.

Establish `g2 : (fun a => G F0.e fa fb σ (fa a)) = fb` using `funext (G_f σ ha)`. Rewrite using `[hΛa, Submodule.map_sup, Submodule.map_sup, map_latSpan, map_latSpan, hLL, hΛb, g1, g2]`.
-/
theorem map_G_eq {aa : Fin r → FractionalIdeal (nonZeroDivisors (𝓞 E)) E} {Λa Λb La Lb : Submodule (𝓞 E) S.V}
    {fa fb : Fin r → S.V} (ha : DualFr F0.e fa) (hb : DualFr F0.e fb)
    (hLa : ∀ x ∈ La, ∀ a, S.hT (F0.e a) x = 0 ∧ S.hT (fa a) x = 0)
    (hLb : ∀ x ∈ Lb, ∀ a, S.hT (F0.e a) x = 0 ∧ S.hT (fb a) x = 0)
    (hΛa : Λa = latSpan aa F0.e ⊔ La ⊔ latSpan (fun a => (aa a)⁻¹) fa)
    (hΛb : Λb = latSpan aa F0.e ⊔ Lb ⊔ latSpan (fun a => (aa a)⁻¹) fb)
    (σ : S.V ≃ₗ[E] S.V) (hσ : ∀ x y, S.hT (σ x) (σ y) = S.hT x y)
    (hσX : ∀ x ∈ Submodule.span E (Set.range F0.e), σ x ∈ Submodule.span E (Set.range F0.e))
    (hσX' : ∀ x ∈ Submodule.span E (Set.range F0.e), σ.symm x ∈ Submodule.span E (Set.range F0.e))
    (hL : Lsub (Formalism.HermitianLatticesTheory.gmap σ Λa) (⟨F0, F0.z⟩ : LFlag S r T) = Lsub Λb ⟨F0, F0.z⟩) :
    Λa.map ((G F0.e fa fb σ).restrictScalars (𝓞 E)) = Λb := by
  have hA : ∀ l ∈ La, G F0.e fa fb σ l ∈ Lb := by
    intro l hl
    have hle : ∀ a, S.hT (F0.e a) l = 0 := fun a => (hLa l hl a).1
    have hσl : σ l ∈ Formalism.HermitianLatticesTheory.gmap σ Λa := by
      refine Submodule.mem_map_of_mem (f := ((σ : S.V →ₗ[E] S.V).restrictScalars (𝓞 E))) ?_
      rw [hΛa]; exact Submodule.mem_sup_left (Submodule.mem_sup_right hl)
    have hp := sig_perp σ hσ hσX' hle
    have h1 := mem_Lsub F0 hσl hp
    rw [hL] at h1
    obtain ⟨m, hm, hmp, hmx⟩ := of_mem_Lsub F0 h1
    obtain ⟨s, hs, l', hl', rfl⟩ := split_perp F0 hb hLb hΛb hm hmp
    have e1 : σ l = l' + ((σ l - (s + l')) + s) := by abel
    rw [G_w σ hle (fun a => (hLa l hl a).2)]
    try simp only [LinearEquiv.coe_coe]
    rw [e1, map_add, pr_spanE hb (Submodule.add_mem _ hmx hs), add_zero,
      pr_of_perp l' (fun a => (hLb l' hl' a).1) (fun a => (hLb l' hl' a).2)]
    exact hl'
  have hB : ∀ l' ∈ Lb, ∃ l ∈ La, G F0.e fa fb σ l = l' := by
    intro l' hl'
    have hle' : ∀ a, S.hT (F0.e a) l' = 0 := fun a => (hLb l' hl' a).1
    have hl'Λ : l' ∈ Λb := by rw [hΛb]; exact Submodule.mem_sup_left (Submodule.mem_sup_right hl')
    have h1 := mem_Lsub F0 hl'Λ hle'
    rw [← hL] at h1
    obtain ⟨m, hm, hmp, hmx⟩ := of_mem_Lsub F0 h1
    obtain ⟨m0, hm0, rfl⟩ := Submodule.mem_map.1 hm
    simp only [LinearMap.coe_restrictScalars, LinearEquiv.coe_coe] at hmp hmx
    have hm0p : ∀ a, S.hT (F0.e a) m0 = 0 := by
      intro a
      rw [← hσ]
      exact (perpX hmp (hσX _ (Submodule.subset_span ⟨a, rfl⟩))).1
    obtain ⟨s, hs, l, hl, rfl⟩ := split_perp F0 ha hLa hΛa hm0 hm0p
    refine ⟨l, hl, ?_⟩
    have e1 : σ l = l' - ((l' - σ (s + l)) + σ s) := by rw [map_add]; abel
    rw [G_w σ (fun a => (hLa l hl a).1) (fun a => (hLa l hl a).2)]
    try simp only [LinearEquiv.coe_coe]
    rw [e1, map_sub, pr_spanE hb (Submodule.add_mem _ hmx (hσX _ hs)), sub_zero,
      pr_of_perp l' hle' (fun a => (hLb l' hl' a).2)]
  have hLL : La.map ((G F0.e fa fb σ).restrictScalars (𝓞 E)) = Lb := by
    apply le_antisymm
    · rw [Submodule.map_le_iff_le_comap]; intro l hl; exact hA l hl
    · intro l' hl'
      obtain ⟨l, hl, he⟩ := hB l' hl'
      exact ⟨l, hl, he⟩
  have g1 : (fun a => G F0.e fa fb σ (F0.e a)) = F0.e := funext (G_e σ ha)
  have g2 : (fun a => G F0.e fa fb σ (fa a)) = fb := funext (G_f σ ha)
  rw [hΛa, Submodule.map_sup, Submodule.map_sup, map_latSpan, map_latSpan, hLL, hΛb, g1, g2]

/- English proof (translation)
The claim follows from `Submodule.span_mono (Set.image_subset_range _ _)`.
-/
theorem Xa_le_X (j : ℕ) : F0.Xa j ≤ F0.X := Submodule.span_mono (Set.image_subset_range _ _)

/- English proof (translation)
The claim follows from `Submodule.span_mono (Set.image_mono fun i (hi : i.1 < j) => show i.1 < k from lt_of_lt_of_le hi h)`.
-/
theorem Xa_mono {j k : ℕ} (h : j ≤ k) : F0.Xa j ≤ F0.Xa k :=
  Submodule.span_mono (Set.image_mono fun i (hi : i.1 < j) => show i.1 < k from lt_of_lt_of_le hi h)

omit [NumberField E] in
/- English proof (translation)
Establish `h1 : U.map (σ : V →ₗ[E] V) ≤ U` using `by rintro _ ⟨y, hy, rfl⟩; exact hU y hy`. Establish `h2 : Module.finrank E (U.map (σ : V →ₗ[E] V)) = Module.finrank E U` using `LinearEquiv.finrank_map_eq σ U`. Establish `h3 : U.map (σ : V →ₗ[E] V) = U` using `Submodule.eq_of_le_of_finrank_eq h1 h2`. Introduce `x hx`. Rewrite `hx` using `[← h3]`.

Take `⟨y, hy, rfl⟩` from `hx`. Simplify using `using hy`.
-/
theorem symm_mem {V : Type} [AddCommGroup V] [Module E V] [FiniteDimensional E V] {U : Submodule E V}
    (σ : V ≃ₗ[E] V) (hU : ∀ x ∈ U, σ x ∈ U) : ∀ x ∈ U, σ.symm x ∈ U := by
  have h1 : U.map (σ : V →ₗ[E] V) ≤ U := by rintro _ ⟨y, hy, rfl⟩; exact hU y hy
  have h2 : Module.finrank E (U.map (σ : V →ₗ[E] V)) = Module.finrank E U := LinearEquiv.finrank_map_eq σ U
  have h3 : U.map (σ : V →ₗ[E] V) = U := Submodule.eq_of_le_of_finrank_eq h1 h2
  intro x hx
  rw [← h3] at hx
  obtain ⟨y, hy, rfl⟩ := hx
  simpa using hy

variable {F0} (σ : S.V ≃ₗ[E] S.V) (hσe : ∀ i : Fin r, σ (F0.e i) - F0.e i ∈ F0.Xa i.val)
include hσe

/- English proof (translation)
Establish `: F0.Xa j ≤ (F0.Xa j).comap (σ : S.V →ₗ[E] S.V)` using `by show Submodule.span E (F0.e '' {i | i.1 < j}) ≤ _`. Rewrite using `[Submodule.span_le]`. Introduce and unpack `_ ⟨i, hi, rfl⟩`. Establish `h1 : F0.e i ∈ F0.Xa j` using `Submodule.subset_span ⟨i, hi, rfl⟩`. Establish `h2` using `Xa_mono F0 (le_of_lt hi) (hσe i)`.

Use `Submodule.add_mem _ h1 h2` as an intermediate fact. Simplify using `using this`. Conclude with `fun x hx => this hx`.
-/
theorem sig_Xa (j : ℕ) : ∀ x ∈ F0.Xa j, σ x ∈ F0.Xa j := by
  have : F0.Xa j ≤ (F0.Xa j).comap (σ : S.V →ₗ[E] S.V) := by
    show Submodule.span E (F0.e '' {i | i.1 < j}) ≤ _
    rw [Submodule.span_le]
    rintro _ ⟨i, hi, rfl⟩
    have h1 : F0.e i ∈ F0.Xa j := Submodule.subset_span ⟨i, hi, rfl⟩
    have h2 := Xa_mono F0 (le_of_lt hi) (hσe i)
    have := Submodule.add_mem _ h1 h2
    simpa using this
  exact fun x hx => this hx

/- English proof (translation)
Establish `: F0.Xa (j + 1) ≤ (F0.Xa j).comap ((σ : S.V →ₗ[E] S.V) - LinearMap.id)` using `by show Submodule.span E (F0.e '' {i | i.1 < j + 1}) ≤ _`. Rewrite using `[Submodule.span_le]`. Introduce and unpack `_ ⟨i, hi, rfl⟩`. Establish `h2` using `Xa_mono F0 (Nat.lt_succ_iff.1 hi) (hσe i)`. Simplify using `using h2`.

Introduce `x hx`. Simplify using `using this hx`.
-/
theorem sig_step (j : ℕ) : ∀ x ∈ F0.Xa (j + 1), σ x - x ∈ F0.Xa j := by
  have : F0.Xa (j + 1) ≤ (F0.Xa j).comap ((σ : S.V →ₗ[E] S.V) - LinearMap.id) := by
    show Submodule.span E (F0.e '' {i | i.1 < j + 1}) ≤ _
    rw [Submodule.span_le]
    rintro _ ⟨i, hi, rfl⟩
    have h2 := Xa_mono F0 (Nat.lt_succ_iff.1 hi) (hσe i)
    simpa using h2
  intro x hx
  simpa using this hx

/- English proof (translation)
Establish `: Submodule.span E (Set.range F0.e) ≤ (Submodule.span E (Set.range F0.e)).comap (σ : S.V →ₗ[E] S.V)`. Rewrite using `[Submodule.span_le]`. Introduce and unpack `_ ⟨i, rfl⟩`. Establish `h1 : F0.e i ∈ Submodule.span E (Set.range F0.e)` using `Submodule.subset_span ⟨i, rfl⟩`. Establish `h2` using `Xa_le_X F0 _ (hσe i)`.

Use `Submodule.add_mem _ h1 h2` as an intermediate fact. Simplify using `using this`. Conclude with `fun x hx => this hx`.
-/
theorem sig_X : ∀ x ∈ Submodule.span E (Set.range F0.e), σ x ∈ Submodule.span E (Set.range F0.e) := by
  have : Submodule.span E (Set.range F0.e) ≤ (Submodule.span E (Set.range F0.e)).comap (σ : S.V →ₗ[E] S.V) := by
    rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    have h1 : F0.e i ∈ Submodule.span E (Set.range F0.e) := Submodule.subset_span ⟨i, rfl⟩
    have h2 := Xa_le_X F0 _ (hσe i)
    have := Submodule.add_mem _ h1 h2
    simpa using this
  exact fun x hx => this hx

end Gen4

end GlobalTheory.SameInner

namespace GlobalTheory.SameInner

/- English proof (translation)
Take `⟨_, ⟨hlat, huni, ⟨hz, _⟩, ⟨_, hprim⟩⟩, hX⟩` from `hR`. Conclude with `PI.SRW.coreStep_of PI.SRW.frame_reduction PI.SRW.measure_isomorphism_at_infinity PI.SRW.assembly_reduction D.host.E (VS D) D.R.rS _ (Formalism.L2.SG.Saturated.aaS D) F0 Λ ⟨hlat, huni, hz, hprim, hX, fun a => (PI.SRW.adjoint_action_reduction D a).1, fun a => (PI.SRW.adjoint_action …`.
-/
theorem isSplitRow_of_rowLat (D : D7) {T : D.host.E} (F0 : FlagG (VS D) D.R.rS T)
    (Λ : Submodule (𝓞 D.host.E) (VS D).V) (hR : IsRowLat D F0 Λ) :
    Formalism.L2.SG.Saturated.IsSplitRow D F0 Λ := by
  obtain ⟨_, ⟨hlat, huni, ⟨hz, _⟩, ⟨_, hprim⟩⟩, hX⟩ := hR
  exact PI.SRW.coreStep_of PI.SRW.frame_reduction PI.SRW.measure_isomorphism_at_infinity PI.SRW.assembly_reduction
    D.host.E (VS D) D.R.rS _ (Formalism.L2.SG.Saturated.aaS D) F0 Λ
    ⟨hlat, huni, hz, hprim, hX, fun a => (PI.SRW.adjoint_action_reduction D a).1, fun a => (PI.SRW.adjoint_action_reduction D a).2,
      PI.SRW.trace_reduction D⟩

end GlobalTheory.SameInner

namespace GlobalTheory.SameInner

section Gen5

variable {E : Type} [Field E] [NumberField E] [StarRing E] {S : HSpace E} {r : ℕ} {T : E}

open Formalism.L2.SG.Saturated in

/- English proof (translation)
Take `⟨fa, La, hfa, hefa, hLa, -, hΛa⟩` from `ha`. Take `⟨fb, Lb, hfb, hefb, hLb, -, hΛb⟩` from `hb`. Establish `dA : DualFr F0.e fa` using `⟨F0.e_iso, hfa, hefa⟩`. Establish `dB : DualFr F0.e fb` using `⟨F0.e_iso, hfb, hefb⟩`. Establish `hσX` using `sig_X σ hσe`.

Establish `hσX'` using `symm_mem σ hσX`. Establish `hinj` using `G_inj σ hσ hσX' dA dB`. Set `Gl` to `LinearEquiv.ofInjectiveEndo (G F0.e fa fb σ) hinj`. Establish `hGl : ∀ v, Gl v = G F0.e fa fb σ v` using `fun v => rfl`. Establish `hσ' : ∀ x y, S.hT (σ.symm x) (σ.symm y) = S.hT x y`.

Introduce `x y`. Rewrite using `[← hσ]`. Simplify using the standard rewrite rules. Use `⟨Gl * σ.symm, ?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Use `show ∀ x y, S.hT ((Gl * σ.symm) x) ((Gl * σ.symm) y) = S.hT x y`.

Introduce `x y`. Rewrite using `[LinearEquiv.mul_apply, LinearEquiv.mul_apply, hGl, hGl, G_isom σ hσ hσX' dA dB, hσ']`. Introduce `j x hx`. Rewrite using `[LinearEquiv.mul_apply, hGl, G_X σ dA (hσX' _ (Xa_le_X F0 (j + 1) hx))]`. Establish `h1` using `sig_step σ hσe j x hx`.

Establish `e1 : σ.symm x - x = σ.symm (-(σ x - x))` using `by simp [map_sub]`. Rewrite using `[e1]`. Conclude with `symm_mem σ (sig_Xa σ hσe j) _ (Submodule.neg_mem _ h1)`. Introduce `x hx`. Rewrite using `[LinearEquiv.mul_apply, hGl]`.

Conclude with `G_perp σ hσ hσX hσX' dA dB ((perp_iff F0).1 hx)`. Establish `e2 : Gl * σ.symm * σ = Gl` using `by ext v; simp`. Rewrite using `[e2]`. Establish `e3 : (Gl : S.V →ₗ[E] S.V) = G F0.e fa fb σ` using `LinearMap.ext hGl`. Unfold `Formalism.HermitianLatticesTheory.gmap`.

Rewrite using `[e3]`. Conclude with `map_G_eq F0 dA dB hLa hLb hΛa hΛb σ hσ hσX hσX' hL`.
-/
theorem exists_unip (F0 : FlagG S r T) (aa : Fin r → FractionalIdeal (nonZeroDivisors (𝓞 E)) E)
    (Λa Λb : Submodule (𝓞 E) S.V) (σ : S.V ≃ₗ[E] S.V) (hσ : ∀ x y, S.hT (σ x) (σ y) = S.hT x y)
    (hσe : ∀ i : Fin r, σ (F0.e i) - F0.e i ∈ F0.Xa i.val)
    (ha : IsSplitBy aa F0 Λa) (hb : IsSplitBy aa F0 Λb)
    (hL : Lsub (Formalism.HermitianLatticesTheory.gmap σ Λa) (⟨F0, F0.z⟩ : LFlag S r T) = Lsub Λb ⟨F0, F0.z⟩) :
    ∃ n : S.V ≃ₗ[E] S.V, n ∈ Formalism.HermitianLatticesTheory.isom S.hT ∧ (∀ j, ∀ x ∈ F0.Xa (j + 1), n x - x ∈ F0.Xa j) ∧
      (∀ x ∈ orth S F0.X, n x - x ∈ F0.X) ∧ Formalism.HermitianLatticesTheory.gmap (n * σ) Λa = Λb := by
  obtain ⟨fa, La, hfa, hefa, hLa, -, hΛa⟩ := ha
  obtain ⟨fb, Lb, hfb, hefb, hLb, -, hΛb⟩ := hb
  have dA : DualFr F0.e fa := ⟨F0.e_iso, hfa, hefa⟩
  have dB : DualFr F0.e fb := ⟨F0.e_iso, hfb, hefb⟩
  have hσX := sig_X σ hσe
  have hσX' := symm_mem σ hσX
  have hinj := G_inj σ hσ hσX' dA dB
  let Gl := LinearEquiv.ofInjectiveEndo (G F0.e fa fb σ) hinj
  have hGl : ∀ v, Gl v = G F0.e fa fb σ v := fun v => rfl
  have hσ' : ∀ x y, S.hT (σ.symm x) (σ.symm y) = S.hT x y := by
    intro x y; rw [← hσ]; simp
  refine ⟨Gl * σ.symm, ?_, ?_, ?_, ?_⟩
  · show ∀ x y, S.hT ((Gl * σ.symm) x) ((Gl * σ.symm) y) = S.hT x y
    intro x y
    rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, hGl, hGl, G_isom σ hσ hσX' dA dB, hσ']
  · intro j x hx
    rw [LinearEquiv.mul_apply, hGl, G_X σ dA (hσX' _ (Xa_le_X F0 (j + 1) hx))]
    have h1 := sig_step σ hσe j x hx
    have e1 : σ.symm x - x = σ.symm (-(σ x - x)) := by simp [map_sub]
    rw [e1]
    exact symm_mem σ (sig_Xa σ hσe j) _ (Submodule.neg_mem _ h1)
  · intro x hx
    rw [LinearEquiv.mul_apply, hGl]
    exact G_perp σ hσ hσX hσX' dA dB ((perp_iff F0).1 hx)
  · have e2 : Gl * σ.symm * σ = Gl := by ext v; simp
    rw [e2]
    have e3 : (Gl : S.V →ₗ[E] S.V) = G F0.e fa fb σ := LinearMap.ext hGl
    unfold Formalism.HermitianLatticesTheory.gmap
    rw [e3]
    exact map_G_eq F0 dA dB hLa hLb hΛa hΛb σ hσ hσX hσX' hL

end Gen5

end GlobalTheory.SameInner

namespace GlobalTheory.Unfold

open Formalism.L2.SG.NGData

/- English proof (translation)
Introduce `D T F0 Λa Λb σ ha hb hσ hL`. Establish `hσe : ∀ i : Fin D.R.rS, σ (F0.e i) - F0.e i ∈ F0.Xa i.val`. Introduce `i`. Use `hσ.2 i.castSucc` as an intermediate fact. Simplify `this` using `[frame, FlagG.fvec, Xflag]`.

Take `⟨n, h1, h2, h3, h4⟩` from `GlobalTheory.SameInner.exists_unip F0 (Formalism.L2.SG.Saturated.aaS D) Λa Λb σ (fun x y => hσ.1 x y) hσe (GlobalTheory.SameInner.isSplitRow_of_rowLat D F0 Λa ha) (GlobalTheory.SameInner.isSplitRow_of_rowLat D F0 Λb hb) hL`. Conclude with `⟨n, ⟨h1, h2, h3⟩, h4⟩`.
-/
theorem sameInner_unip : ∀ (D : D7) (T : D.host.E) (F0 : FlagG (VS D) D.R.rS T) (Λa Λb : LV D) (σ : GV D),
    IsRowLat D F0 Λa → IsRowLat D F0 Λb → Adapt σ (lf D F0) (lf D F0) →
    Lsub (Formalism.HermitianLatticesTheory.gmap σ Λa) (lf D F0) = Lsub Λb (lf D F0) →
    ∃ n ∈ NRat (lf D F0), Formalism.HermitianLatticesTheory.gmap (n * σ) Λa = Λb := by
  intro D T F0 Λa Λb σ ha hb hσ hL
  have hσe : ∀ i : Fin D.R.rS, σ (F0.e i) - F0.e i ∈ F0.Xa i.val := by
    intro i
    have := hσ.2 i.castSucc
    simpa [frame, FlagG.fvec, Xflag] using this
  obtain ⟨n, h1, h2, h3, h4⟩ := GlobalTheory.SameInner.exists_unip F0 (Formalism.L2.SG.Saturated.aaS D) Λa Λb σ
    (fun x y => hσ.1 x y) hσe (GlobalTheory.SameInner.isSplitRow_of_rowLat D F0 Λa ha)
    (GlobalTheory.SameInner.isSplitRow_of_rowLat D F0 Λb hb) hL
  exact ⟨n, ⟨h1, h2, h3⟩, h4⟩

end GlobalTheory.Unfold

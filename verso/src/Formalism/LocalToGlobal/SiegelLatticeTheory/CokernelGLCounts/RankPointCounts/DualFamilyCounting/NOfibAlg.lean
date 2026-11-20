import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.NOfibCut

noncomputable section

open scoped Classical
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Matrix

namespace Formalism.L2.SG.Pf.NcReal.JX.NOf

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace Alg

variable {D : D7} (X : HidaSetting D)

/- English proof (translation)
The claim follows from `((VS D).herm.eq x y).symm`.
-/
theorem hsw (x y : (VS D).V) : (VS D).hT y x = star ((VS D).hT x y) := ((VS D).herm.eq x y).symm

/- English proof (translation)
Rewrite using `[hsw, X.ef b a]`. Distinguish the cases in `h : a = b`. Substitute `h` using the available equality. Simplify using the standard rewrite rules. Simplify using `[h, Ne.symm h]`.
-/
theorem hfe (a b : Fin D.R.rS) : (VS D).hT (X.fY a) (X.eX b) = if a = b then 1 else 0 := by
  rw [hsw, X.ef b a]
  by_cases h : a = b
  · subst h; simp
  · simp [h, Ne.symm h]

/- English proof (translation)
Simplify using `[map_sum, LinearMap.sum_apply, map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul, starRingEnd_apply]`.
-/
theorem hT_sumL {ι : Type*} (s : Finset ι) (c : ι → D.host.E) (y : ι → (VS D).V) (x : (VS D).V) :
    (VS D).hT (∑ i ∈ s, c i • y i) x = ∑ i ∈ s, star (c i) * (VS D).hT (y i) x := by
  simp [map_sum, LinearMap.sum_apply, map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul, starRingEnd_apply]

/- English proof (translation)
Simplify using `[map_sum, map_smul, smul_eq_mul]`.
-/
theorem hT_sumR {ι : Type*} (s : Finset ι) (c : ι → D.host.E) (y : ι → (VS D).V) (x : (VS D).V) :
    (VS D).hT x (∑ i ∈ s, c i • y i) = ∑ i ∈ s, c i * (VS D).hT x (y i) := by
  simp [map_sum, map_smul, smul_eq_mul]

/- English proof (translation)
Simplify using `[map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul, starRingEnd_apply]`.
-/
theorem hT_smulL (c : D.host.E) (x y : (VS D).V) : (VS D).hT (c • x) y = star c * (VS D).hT x y := by
  simp [map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul, starRingEnd_apply]

/- English proof (translation)
Proceed by induction on `hx using Submodule.span_induction with`. Consider the case `mem y hy`. Take `⟨a, ha, rfl⟩` from `hy`. Use `⟨?_, fun b hb => ?_⟩` and prove the remaining obligations. Simplify using `only [hfe, ite_smul, one_smul, zero_smul, Finset.sum_ite_eq', Finset.mem_univ, if_true]`.

Rewrite using `[hfe, if_neg]`. Introduce and unpack `rfl`. Conclude with `hb ha`. Consider the case `zero => simp`. Consider the case `add x y _ _ hx hy`.

Use `⟨?_, fun b hb => ?_⟩` and prove the remaining obligations. Use `conv_lhs => rw [hx.1, hy.1]`. Simplify using `only [map_add, add_smul, Finset.sum_add_distrib]`. Rewrite using `[map_add, hx.2 b hb, hy.2 b hb, add_zero]`. Consider the case `smul c x _ hx`.

Use `⟨?_, fun b hb => ?_⟩` and prove the remaining obligations. Use `conv_lhs => rw [hx.1]`. Simplify using `only [map_smul, smul_eq_mul, Finset.smul_sum, smul_smul]`. Rewrite using `[map_smul, hx.2 b hb, smul_zero]`.
-/
theorem coef_e (S : Set (Fin D.R.rS)) {x : (VS D).V} (hx : x ∈ Submodule.span D.host.E (X.eX '' S)) :
    x = ∑ b, (VS D).hT (X.fY b) x • X.eX b ∧ ∀ b, b ∉ S → (VS D).hT (X.fY b) x = 0 := by
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨a, ha, rfl⟩ := hy
    refine ⟨?_, fun b hb => ?_⟩
    · simp only [hfe, ite_smul, one_smul, zero_smul, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    · rw [hfe, if_neg]; rintro rfl; exact hb ha
  | zero => simp
  | add x y _ _ hx hy =>
    refine ⟨?_, fun b hb => ?_⟩
    · conv_lhs => rw [hx.1, hy.1]
      simp only [map_add, add_smul, Finset.sum_add_distrib]
    · rw [map_add, hx.2 b hb, hy.2 b hb, add_zero]
  | smul c x _ hx =>
    refine ⟨?_, fun b hb => ?_⟩
    · conv_lhs => rw [hx.1]
      simp only [map_smul, smul_eq_mul, Finset.smul_sum, smul_smul]
    · rw [map_smul, hx.2 b hb, smul_zero]

/- English proof (translation)
Rewrite `hx` using `[← Set.image_univ]`. Conclude with `(coef_e X Set.univ hx).1`.
-/
theorem coef_range {x : (VS D).V} (hx : x ∈ Submodule.span D.host.E (Set.range X.eX)) :
    x = ∑ b, (VS D).hT (X.fY b) x • X.eX b := by
  rw [← Set.image_univ] at hx
  exact (coef_e X Set.univ hx).1

/- English proof (translation)
Introduce `c`. Prove the components needed by the constructor for the conclusion. Simplify using `only [pW, map_sub, hT_sumR, X.ee, X.ef, mul_zero, Finset.sum_const_zero, sub_zero, mul_ite, mul_one, Finset.sum_ite_eq, Finset.mem_univ, if_true, sub_self]`. Simplify using `only [pW, map_sub, hT_sumR, X.ff, hfe, mul_zero, Finset.sum_const_zero, sub_zero, mul_ite, mul_one, Finset.sum_ite_eq, Finset.mem_univ, if_true, sub_self]`.
-/
theorem pW_inW (y : (VS D).V) : InW X (pW X y) := by
  intro c
  constructor
  · simp only [pW, map_sub, hT_sumR, X.ee, X.ef, mul_zero, Finset.sum_const_zero, sub_zero, mul_ite, mul_one,
      Finset.sum_ite_eq, Finset.mem_univ, if_true, sub_self]
  · simp only [pW, map_sub, hT_sumR, X.ff, hfe, mul_zero, Finset.sum_const_zero, sub_zero, mul_ite, mul_one,
      Finset.sum_ite_eq, Finset.mem_univ, if_true, sub_self]

/- English proof (translation)
Simplify using `only [pW]`. Normalize the expressions using the abelian group laws.
-/
theorem decomp (y : (VS D).V) :
    y = ∑ d, (VS D).hT (X.fY d) y • X.eX d + ∑ d, (VS D).hT (X.eX d) y • X.fY d + pW X y := by
  simp only [pW]; abel

/- English proof (translation)
Simplify using `only [pW, (hw _).1, (hw _).2, zero_smul, Finset.sum_const_zero, sub_zero]`.
-/
theorem pW_of_inW {w : (VS D).V} (hw : InW X w) : pW X w = w := by
  simp only [pW, (hw _).1, (hw _).2, zero_smul, Finset.sum_const_zero, sub_zero]

/- English proof (translation)
Simplify using `only [pW, map_add, add_smul, Finset.sum_add_distrib]`. Normalize the expressions using the abelian group laws.
-/
theorem pW_add (x y : (VS D).V) : pW X (x + y) = pW X x + pW X y := by
  simp only [pW, map_add, add_smul, Finset.sum_add_distrib]; abel

/- English proof (translation)
Simplify using `only [pW, map_smul, smul_eq_mul, mul_smul, ← Finset.smul_sum, smul_sub]`.
-/
theorem pW_smul (c : D.host.E) (x : (VS D).V) : pW X (c • x) = c • pW X x := by
  simp only [pW, map_smul, smul_eq_mul, mul_smul, ← Finset.smul_sum, smul_sub]

/- English proof (translation)
Simplify using `only [pW, X.ee, hfe, ite_smul, one_smul, zero_smul, Finset.sum_ite_eq', Finset.mem_univ, if_true, Finset.sum_const_zero, sub_zero, sub_self]`.
-/
theorem pW_e (a : Fin D.R.rS) : pW X (X.eX a) = 0 := by
  simp only [pW, X.ee, hfe, ite_smul, one_smul, zero_smul, Finset.sum_ite_eq', Finset.mem_univ, if_true,
    Finset.sum_const_zero, sub_zero, sub_self]

/- English proof (translation)
Proceed by induction on `(Finset.univ : Finset (Fin D.R.rS)) using Finset.induction_on with`. Consider the case `empty => simp [pW]`. Consider the case `insert a s ha ih`. Rewrite using `[Finset.sum_insert ha, pW_add, pW_smul, pW_e, smul_zero, zero_add, ih]`.
-/
theorem pW_sum_e (c : Fin D.R.rS → D.host.E) : pW X (∑ d, c d • X.eX d) = 0 := by
  induction (Finset.univ : Finset (Fin D.R.rS)) using Finset.induction_on with
  | empty => simp [pW]
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, pW_add, pW_smul, pW_e, smul_zero, zero_add, ih]

/- English proof (translation)
Rewrite using `[hsw, (hw a).1, star_zero]`.
-/
theorem hT_w_e {w : (VS D).V} (hw : InW X w) (a : Fin D.R.rS) : (VS D).hT w (X.eX a) = 0 := by
  rw [hsw, (hw a).1, star_zero]

/- English proof (translation)
Rewrite using `[hsw, (hw a).2, star_zero]`.
-/
theorem hT_w_f {w : (VS D).V} (hw : InW X w) (a : Fin D.R.rS) : (VS D).hT w (X.fY a) = 0 := by
  rw [hsw, (hw a).2, star_zero]

/- English proof (translation)
Establish `h1 : (VS D).hT (pW X y) y' = (VS D).hT (pW X y) (pW X y')` using `by conv_lhs => rw [decomp X y']`. Rewrite using `[map_add, map_add, hT_sumR, hT_sumR]`. Simplify using `only [hT_w_e X (pW_inW X y), hT_w_f X (pW_inW X y), mul_zero, Finset.sum_const_zero, zero_add]`. Use `conv_lhs => rw [decomp X y]`. Rewrite using `[map_add, map_add, LinearMap.add_apply, LinearMap.add_apply, hT_sumL, hT_sumL, h1]`.
-/
theorem parseval (y y' : (VS D).V) :
    (VS D).hT y y' = ∑ d, star ((VS D).hT (X.fY d) y) * (VS D).hT (X.eX d) y' +
      ∑ d, star ((VS D).hT (X.eX d) y) * (VS D).hT (X.fY d) y' + (VS D).hT (pW X y) (pW X y') := by
  have h1 : (VS D).hT (pW X y) y' = (VS D).hT (pW X y) (pW X y') := by
    conv_lhs => rw [decomp X y']
    rw [map_add, map_add, hT_sumR, hT_sumR]
    simp only [hT_w_e X (pW_inW X y), hT_w_f X (pW_inW X y), mul_zero, Finset.sum_const_zero, zero_add]
  conv_lhs => rw [decomp X y]
  rw [map_add, map_add, LinearMap.add_apply, LinearMap.add_apply, hT_sumL, hT_sumL, h1]

section N

variable {X} {u : D.what₂.Word} {n : (VS D).V ≃ₗ[D.host.E] (VS D).V}

/- English proof (translation)
The claim follows from `hn.1 x y`.
-/
theorem iso (hn : NFl X u n) (x y : (VS D).V) : (VS D).hT (n x) (n y) = (VS D).hT x y := hn.1 x y

/- English proof (translation)
Rewrite using `[← iso hn (n.symm x) y, LinearEquiv.apply_symm_apply]`.
-/
theorem iso_symm (hn : NFl X u n) (x y : (VS D).V) : (VS D).hT (n.symm x) y = (VS D).hT x (n y) := by
  rw [← iso hn (n.symm x) y, LinearEquiv.apply_symm_apply]

/- English proof (translation)
Establish `hx : X.eX a ∈ Xflag (lf D (X.Fu u)) (a.1 + 1)`. Express the relevant statement in the definitionally equal form `X.eX a ∈ Submodule.span D.host.E ((X.Fu u).e '' {i | i.1 < a.1 + 1})`. Rewrite using `[X.Fu_e]`. Conclude with `Submodule.subset_span ⟨a, by simp, rfl⟩`. Use `hn.2.1 a.1 _ hx` as an intermediate fact.

Express the relevant statement in the definitionally equal form `_ ∈ Submodule.span D.host.E ((X.Fu u).e '' {i | i.1 < a.1}) at this`. Rewrite `this` using `[X.Fu_e]`. Then use the resulting hypothesis.
-/
theorem ne_mem (hn : NFl X u n) (a : Fin D.R.rS) :
    n (X.eX a) - X.eX a ∈ Submodule.span D.host.E (X.eX '' {b | b.1 < a.1}) := by
  have hx : X.eX a ∈ Xflag (lf D (X.Fu u)) (a.1 + 1) := by
    change X.eX a ∈ Submodule.span D.host.E ((X.Fu u).e '' {i | i.1 < a.1 + 1})
    rw [X.Fu_e]
    exact Submodule.subset_span ⟨a, by simp, rfl⟩
  have := hn.2.1 a.1 _ hx
  change _ ∈ Submodule.span D.host.E ((X.Fu u).e '' {i | i.1 < a.1}) at this
  rwa [X.Fu_e] at this

/- English proof (translation)
Establish `h` using `(coef_e X _ (ne_mem hn a)).1`. Establish `e : n (X.eX a) = (n (X.eX a) - X.eX a) + X.eX a` using `by abel`. Use `conv_lhs => rw [e, h]`. Use `conv_rhs => rw [show (∑ b, Xq X n b a • X.eX b) = ∑ b, ((VS D).hT (X.fY b) (n (X.eX a) - X.eX a) + (if b = a then 1 else 0)) • X.eX b from Finset.sum_congr rfl fun b _ => by`. Rewrite using `[map_sub, hfe, sub_add_cancel]`.

Use the proof step `rfl]`. Simplify using `only [add_smul, Finset.sum_add_distrib, ite_smul, one_smul, zero_smul, Finset.sum_ite_eq', Finset.mem_univ, if_true]`.
-/
theorem Xq_expand (hn : NFl X u n) (a : Fin D.R.rS) : n (X.eX a) = ∑ b, Xq X n b a • X.eX b := by
  have h := (coef_e X _ (ne_mem hn a)).1
  have e : n (X.eX a) = (n (X.eX a) - X.eX a) + X.eX a := by abel
  conv_lhs => rw [e, h]
  conv_rhs => rw [show (∑ b, Xq X n b a • X.eX b) = ∑ b, ((VS D).hT (X.fY b) (n (X.eX a) - X.eX a) +
    (if b = a then 1 else 0)) • X.eX b from Finset.sum_congr rfl fun b _ => by
      rw [map_sub, hfe, sub_add_cancel]; rfl]
  simp only [add_smul, Finset.sum_add_distrib, ite_smul, one_smul, zero_smul, Finset.sum_ite_eq',
    Finset.mem_univ, if_true]

/- English proof (translation)
Rewrite using `[map_sub, hfe, sub_add_cancel]`. Both sides reduce to the same expression.
-/
theorem Xq_entry (hn : NFl X u n) (b a : Fin D.R.rS) :
    Xq X n b a = (VS D).hT (X.fY b) (n (X.eX a) - X.eX a) + if b = a then 1 else 0 := by
  rw [map_sub, hfe, sub_add_cancel]; rfl

/- English proof (translation)
Apply the tactic sequence `rw [Xq_entry hn, (coef_e X _ (ne_mem hn a)).2 b (by simp only [Set.mem_setOf_eq, not_lt]; exact le_of_lt h), if_neg (ne_of_gt h), add_zero]`.
-/
theorem Xq_lower (hn : NFl X u n) {b a : Fin D.R.rS} (h : a < b) : Xq X n b a = 0 := by
  rw [Xq_entry hn, (coef_e X _ (ne_mem hn a)).2 b (by simp only [Set.mem_setOf_eq, not_lt]; exact le_of_lt h),
    if_neg (ne_of_gt h), add_zero]

/- English proof (translation)
Apply the tactic sequence `rw [Xq_entry hn, (coef_e X _ (ne_mem hn a)).2 a (by simp), if_pos rfl, zero_add]`.
-/
theorem Xq_diag (hn : NFl X u n) (a : Fin D.R.rS) : Xq X n a a = 1 := by
  rw [Xq_entry hn, (coef_e X _ (ne_mem hn a)).2 a (by simp), if_pos rfl, zero_add]

/- English proof (translation)
Express the relevant statement in the definitionally equal form `w ∈ orth (VS D) (Submodule.span D.host.E (Set.range (X.Fu u).e))`. Rewrite using `[X.Fu_e]`. Simplify using `only [orth, Submodule.mem_iInf, LinearMap.mem_ker]`. Introduce `x hx`. Proceed by induction on `hx using Submodule.span_induction with`.

Consider the case `mem y hy => obtain ⟨a, rfl⟩ := hy`. Conclude with `(hw a).1`. Consider the case `zero => simp`. Consider the case `add x y _ _ hx hy => rw [map_add, LinearMap.add_apply, hx, hy, add_zero]`. Consider the case `smul c x _ hx => rw [hT_smulL, hx, mul_zero]`.
-/
theorem inW_orth {w : (VS D).V} (hw : InW X w) : w ∈ orth (VS D) (Xsp (lf D (X.Fu u))) := by
  change w ∈ orth (VS D) (Submodule.span D.host.E (Set.range (X.Fu u).e))
  rw [X.Fu_e]
  simp only [orth, Submodule.mem_iInf, LinearMap.mem_ker]
  intro x hx
  induction hx using Submodule.span_induction with
  | mem y hy => obtain ⟨a, rfl⟩ := hy; exact (hw a).1
  | zero => simp
  | add x y _ _ hx hy => rw [map_add, LinearMap.add_apply, hx, hy, add_zero]
  | smul c x _ hx => rw [hT_smulL, hx, mul_zero]

/- English proof (translation)
Establish `h1` using `hn.2.2 w (inW_orth hw)`. Express the relevant statement in the definitionally equal form `_ ∈ Submodule.span D.host.E (Set.range (X.Fu u).e) at h1`. Rewrite `h1` using `[X.Fu_e]`. Establish `h2` using `coef_range X h1`. Establish `e : ∀ d, (VS D).hT (X.fY d) (n w - w) = (VS D).hT (X.fY d) (n w)` using `fun d => by`.

Rewrite using `[map_sub, (hw d).2, sub_zero]`. Simplify using `only [e] at h2`. Rewrite using `[← h2]`. Normalize the expressions using the abelian group laws.
-/
theorem nw (hn : NFl X u n) {w : (VS D).V} (hw : InW X w) :
    n w = w + ∑ d, (VS D).hT (X.fY d) (n w) • X.eX d := by
  have h1 := hn.2.2 w (inW_orth hw)
  change _ ∈ Submodule.span D.host.E (Set.range (X.Fu u).e) at h1
  rw [X.Fu_e] at h1
  have h2 := coef_range X h1
  have e : ∀ d, (VS D).hT (X.fY d) (n w - w) = (VS D).hT (X.fY d) (n w) := fun d => by
    rw [map_sub, (hw d).2, sub_zero]
  simp only [e] at h2
  rw [← h2]; abel

/- English proof (translation)
Rewrite using `[← iso_symm hn, parseval X _ w]`. Simplify using `only [(hw _).1, (hw _).2, mul_zero, Finset.sum_const_zero, zero_add, pW_of_inW X hw]`. Both sides reduce to the same expression.
-/
theorem row (hn : NFl X u n) (b : Fin D.R.rS) {w : (VS D).V} (hw : InW X w) :
    (VS D).hT (X.fY b) (n w) = (VS D).hT (xq X n b) w := by
  rw [← iso_symm hn, parseval X _ w]
  simp only [(hw _).1, (hw _).2, mul_zero, Finset.sum_const_zero, zero_add, pW_of_inW X hw]
  rfl

def Bq (n : (VS D).V ≃ₗ[D.host.E] (VS D).V) : Matrix (Fin D.R.rS) (Fin D.R.rS) D.host.E :=
  fun d a => (VS D).hT (X.eX d) (n (X.fY a))

/- English proof (translation)
Use extensionality with `b a`. Simplify using `only [Matrix.mul_apply, Matrix.conjTranspose_apply, Bq]`. Rewrite using `[← hT_sumL, ← Xq_expand hn, iso hn, X.ef, Matrix.one_apply]`.
-/
theorem XB (hn : NFl X u n) : (Xq X n)ᴴ * Bq (X := X) n = 1 := by
  ext b a
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Bq]
  rw [← hT_sumL, ← Xq_expand hn, iso hn, X.ef, Matrix.one_apply]

/- English proof (translation)
Establish `h` using `parseval X (n (X.fY a)) (n (X.fY c))`. Rewrite `h` using `[iso hn, X.ff]`. Rewrite using `[h, Matrix.add_apply, Matrix.mul_apply, Matrix.mul_apply]`. Simplify using `only [Matrix.conjTranspose_apply, Aq, Bq]`.
-/
theorem ff_rel (hn : NFl X u n) (a c : Fin D.R.rS) :
    ((Aq X n)ᴴ * Bq (X := X) n + (Bq (X := X) n)ᴴ * Aq X n) a c +
      (VS D).hT (pW X (n (X.fY a))) (pW X (n (X.fY c))) = 0 := by
  have h := parseval X (n (X.fY a)) (n (X.fY c))
  rw [iso hn, X.ff] at h
  rw [h, Matrix.add_apply, Matrix.mul_apply, Matrix.mul_apply]
  simp only [Matrix.conjTranspose_apply, Aq, Bq]

/- English proof (translation)
Establish `h` using `parseval X (n (X.fY a)) (n w)`. Rewrite `h` using `[iso hn]`. Establish `he : ∀ d, (VS D).hT (X.eX d) (n w) = 0` using `fun d => by`. Rewrite using `[nw hn hw, map_add, hT_sumR, (hw d).1, zero_add]`. Simplify using `only [X.ee, mul_zero, Finset.sum_const_zero]`.

Establish `hp : pW X (n w) = w` using `by conv_lhs => rw [nw hn hw]`. Rewrite using `[pW_add, pW_sum_e, add_zero, pW_of_inW X hw]`. Simplify using `only [he, mul_zero, Finset.sum_const_zero, zero_add, row hn _ hw, hp] at h`. Rewrite `h` using `[(hw a).2]`. Simplify using `only [Bq]`.

Take the linear combination `-h`.
-/
theorem omega_rel (hn : NFl X u n) (a : Fin D.R.rS) {w : (VS D).V} (hw : InW X w) :
    (VS D).hT (pW X (n (X.fY a))) w = -∑ d, star (Bq (X := X) n d a) * (VS D).hT (xq X n d) w := by
  have h := parseval X (n (X.fY a)) (n w)
  rw [iso hn] at h
  have he : ∀ d, (VS D).hT (X.eX d) (n w) = 0 := fun d => by
    rw [nw hn hw, map_add, hT_sumR, (hw d).1, zero_add]
    simp only [X.ee, mul_zero, Finset.sum_const_zero]
  have hp : pW X (n w) = w := by
    conv_lhs => rw [nw hn hw]
    rw [pW_add, pW_sum_e, add_zero, pW_of_inW X hw]
  simp only [he, mul_zero, Finset.sum_const_zero, zero_add, row hn _ hw, hp] at h
  rw [(hw a).2] at h
  simp only [Bq]
  linear_combination -h

/- English proof (translation)
The claim follows from `pW_inW X _`.
-/
theorem xq_inW (d : Fin D.R.rS) : InW X (xq X n d) := pW_inW X _

/- English proof (translation)
Rewrite using `[omega_rel hn a (pW_inW X (n (X.fY c)))]`. Establish `h2 : ∀ d, (VS D).hT (xq X n d) (pW X (n (X.fY c))) = -∑ d', Bq (X` using `X) n d' c * (VS D).hT (xq X n d) (xq X n d') := by`. Introduce `d`. Rewrite using `[hsw, omega_rel hn c (xq_inW d)]`. Simplify using `only [star_neg, star_sum, star_mul', star_star, ← hsw]`.

Simplify using `only [h2, Matrix.mul_apply, Matrix.conjTranspose_apply, Gq, Finset.mul_sum, Finset.sum_mul, mul_neg, Finset.sum_neg_distrib, neg_neg]`. Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_congr rfl fun d' _ => Finset.sum_congr rfl fun d _ => by ring` and prove the remaining obligations.
-/
theorem gram_omega (hn : NFl X u n) (a c : Fin D.R.rS) :
    (VS D).hT (pW X (n (X.fY a))) (pW X (n (X.fY c))) =
      ((Bq (X := X) n)ᴴ * Gq D (xq X n) * Bq (X := X) n) a c := by
  rw [omega_rel hn a (pW_inW X (n (X.fY c)))]
  have h2 : ∀ d, (VS D).hT (xq X n d) (pW X (n (X.fY c))) =
      -∑ d', Bq (X := X) n d' c * (VS D).hT (xq X n d) (xq X n d') := by
    intro d
    rw [hsw, omega_rel hn c (xq_inW d)]
    simp only [star_neg, star_sum, star_mul', star_star, ← hsw]
  simp only [h2, Matrix.mul_apply, Matrix.conjTranspose_apply, Gq, Finset.mul_sum, Finset.sum_mul, mul_neg,
    Finset.sum_neg_distrib, neg_neg]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun d' _ => Finset.sum_congr rfl fun d _ => by ring

/- English proof (translation)
Rewrite using `[Matrix.det_of_isUpperTriangular]`. Simplify using `[Xq_diag hn]`. Introduce `i j hij`. Conclude with `Xq_lower hn hij`.
-/
theorem Xq_det (hn : NFl X u n) : (Xq X n).det = 1 := by
  rw [Matrix.det_of_isUpperTriangular]
  · simp [Xq_diag hn]
  · intro i j hij
    exact Xq_lower hn hij

end N

end Alg

open Alg in

/- English proof (translation)
Introduce `D X u n hn`. Use `⟨fun b a h => Xq_lower hn h, fun a => Xq_diag hn a, fun b => pW_inW X _, ?_⟩` and prove the remaining obligations. Establish `hdet : IsUnit (Xq X n).det` using `by rw [Xq_det hn]; exact isUnit_one`. Establish `hB : Bq (X` using `X) n = ((Xq X n)⁻¹)ᴴ := by`. Rewrite using `[Matrix.conjTranspose_nonsing_inv]`.

Conclude with `(Matrix.inv_eq_right_inv (XB hn)).symm`. Establish `hBh : (Bq (X` using `X) n)ᴴ = (Xq X n)⁻¹ := by rw [hB, Matrix.conjTranspose_conjTranspose]`. Establish `hM : Mq X n = (Bq (X` using `X) n)ᴴ * Aq X n := by rw [hBh]; rfl`. Establish `hMh : (Mq X n)ᴴ = (Aq X n)ᴴ * Bq (X` using `X) n := by`. Rewrite using `[hM, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]`.

Establish `hG : Gp D (Xq X n) (xq X n) = (Bq (X` using `X) n)ᴴ * Gq D (xq X n) * Bq (X := X) n := by`. Rewrite using `[Gp, hBh, hB]`. Rewrite using `[hMh, hM, hG]`. Use `Matrix.ext fun a c => ?_` and prove the remaining obligations. Use `ff_rel hn a c` as an intermediate fact.

Rewrite `this` using `[gram_omega hn a c]`. Simplify using `only [Matrix.add_apply, Matrix.neg_apply] at this ⊢`. Take the linear combination `this`.
-/
theorem dictGram_holds : DictGram := by
  intro D X u n hn
  refine ⟨fun b a h => Xq_lower hn h, fun a => Xq_diag hn a, fun b => pW_inW X _, ?_⟩
  have hdet : IsUnit (Xq X n).det := by rw [Xq_det hn]; exact isUnit_one
  have hB : Bq (X := X) n = ((Xq X n)⁻¹)ᴴ := by
    rw [Matrix.conjTranspose_nonsing_inv]
    exact (Matrix.inv_eq_right_inv (XB hn)).symm
  have hBh : (Bq (X := X) n)ᴴ = (Xq X n)⁻¹ := by rw [hB, Matrix.conjTranspose_conjTranspose]
  have hM : Mq X n = (Bq (X := X) n)ᴴ * Aq X n := by rw [hBh]; rfl
  have hMh : (Mq X n)ᴴ = (Aq X n)ᴴ * Bq (X := X) n := by
    rw [hM, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
  have hG : Gp D (Xq X n) (xq X n) = (Bq (X := X) n)ᴴ * Gq D (xq X n) * Bq (X := X) n := by
    rw [Gp, hBh, hB]
  rw [hMh, hM, hG]
  refine Matrix.ext fun a c => ?_
  have := ff_rel hn a c
  rw [gram_omega hn a c] at this
  simp only [Matrix.add_apply, Matrix.neg_apply] at this ⊢
  linear_combination this

end Formalism.L2.SG.Pf.NcReal.JX.NOf

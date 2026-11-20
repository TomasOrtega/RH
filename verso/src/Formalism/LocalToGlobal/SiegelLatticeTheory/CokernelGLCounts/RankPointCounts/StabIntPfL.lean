import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.StabIntPfSk
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.LocFacts

noncomputable section

open scoped Classical

open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.TermDef Formalism.L2.SG.PairVal Formalism.MainNotions.S.LocalSplitGroups

namespace Formalism.L2.SG.Pf.StabIntSh

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} (δ : ∀ p : PlF D, (D.s.atP p).Fp)
  (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep) (hA : ∀ q, Agree δ M q) (p : PlF D)

include δ M hA

omit M hA in

abbrev cc : (D.s.atP p).Ep :=
  algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (δ p) * (D.s.atP p).ιE (uP p : D.host.E)

/- English proof (translation)
The claim follows from `LocFacts.isUnit_localConstant p ⟨δ, M, hA⟩`.
-/
theorem cc_unit : IsUnit (cc δ p) := LocFacts.isUnit_localConstant p ⟨δ, M, hA⟩

/- English proof (translation)
Unfold `frFac`. Conclude with `Ring.inverse_mul_cancel _ ((cc_unit δ M hA p).pow _)`.
-/
theorem frFac_mul (a : Fin (D.R.rS + 1)) : frFac δ p a * cc δ p ^ (D.R.rS - a.val) = 1 := by
  unfold frFac
  exact Ring.inverse_mul_cancel _ ((cc_unit δ M hA p).pow _)

/- English proof (translation)
Unfold `frFac`. Conclude with `Ring.inverse_inverse ((cc_unit δ M hA p).pow _)`.
-/
theorem inv_frFac (a : Fin (D.R.rS + 1)) : Ring.inverse (frFac δ p a) = cc δ p ^ (D.R.rS - a.val) := by
  unfold frFac
  exact Ring.inverse_inverse ((cc_unit δ M hA p).pow _)

/- English proof (translation)
Establish `hE : (D.s.atP p).ιE (uP p : D.host.E) = algebraMap (D.s.atP p).Fp (D.s.atP p).Ep ((uP p : ℚ) : (D.s.atP p).Fp)`. Rewrite using `[← map_ratCast (algebraMap D.host.F D.host.E), (D.s.atP p).compat, map_ratCast]`. Simplify using `only [cc, map_mul, hE, AlgEquiv.commutes]`.
-/
theorem cj_cc : (D.s.atP p).cj (cc δ p) = cc δ p := by
  have hE : (D.s.atP p).ιE (uP p : D.host.E) =
      algebraMap (D.s.atP p).Fp (D.s.atP p).Ep ((uP p : ℚ) : (D.s.atP p).Fp) := by
    rw [← map_ratCast (algebraMap D.host.F D.host.E), (D.s.atP p).compat, map_ratCast]
  simp only [cc, map_mul, hE, AlgEquiv.commutes]

/- English proof (translation)
Establish `h` using `frFac_mul δ M hA p a`. Establish `h' : (D.s.atP p).cj (frFac δ p a) * cc δ p ^ (D.R.rS - a.val) = 1`. Rewrite using `[← cj_cc δ M hA p, ← map_pow, ← map_mul, h, map_one]`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[mul_comm (cc δ p ^ _), h, mul_one]`.

Use `_ = frFac δ p a := by rw [← mul_assoc, h', one_mul]`.
-/
theorem cj_frFac (a : Fin (D.R.rS + 1)) : (D.s.atP p).cj (frFac δ p a) = frFac δ p a := by
  have h := frFac_mul δ M hA p a
  have h' : (D.s.atP p).cj (frFac δ p a) * cc δ p ^ (D.R.rS - a.val) = 1 := by
    rw [← cj_cc δ M hA p, ← map_pow, ← map_mul, h, map_one]
  calc (D.s.atP p).cj (frFac δ p a)
      = (D.s.atP p).cj (frFac δ p a) * (cc δ p ^ (D.R.rS - a.val) * frFac δ p a) := by
        rw [mul_comm (cc δ p ^ _), h, mul_one]
    _ = frFac δ p a := by rw [← mul_assoc, h', one_mul]

/- English proof (translation)
Establish `hD` using `locDiffC_holds D ⟨δ, M, hA⟩ p ⟨D.R.rS - k, by omega⟩`. Establish `e1 : (-((D.R.rS : ℤ) - ((D.R.rS - k : ℕ) : ℤ))) = -(k : ℤ)`. Rewrite using `[Nat.cast_sub hk]`. Expand and normalize the polynomial expressions, which then agree. Simplify using `only at hD`.

Rewrite `hD` using `[e1]`. Establish `hg` using `frFac_mul δ M hA p ⟨D.R.rS - k, by omega⟩`. Simplify using `only [Nat.sub_sub_self hk] at hg`. Establish `hO : (M p).L.O = (D.s.atP p).O` using `(hA p).2.2.2.1`. Unfold `LocMem ddPow`.

Rewrite using `[← SetLike.mem_coe, ← LocFacts.lf_span_coe_of_eq hO, hD, LocFacts.lf_span_coe_of_eq hO, SetLike.mem_coe, Submodule.mem_span_singleton]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨o, ho⟩`. Rewrite using `[← ho, Subring.smul_def, smul_eq_mul, mul_left_comm, mul_comm (cc δ p ^ k), hg, mul_one]`. Conclude with `o.2`.

Introduce `h`. Use `⟨⟨_, h⟩, ?_⟩` and prove the remaining obligations. Rewrite using `[Subring.smul_def, smul_eq_mul]`. Use `show cc δ p ^ k * (D.s.atP p).ιE x * frFac δ p ⟨D.R.rS - k, by omega⟩ = (D.s.atP p).ιE x`. Rewrite using `[mul_comm (cc δ p ^ k), mul_assoc, mul_comm (cc δ p ^ k), hg, mul_one]`.
-/
theorem locMem_iff {k : ℕ} (hk : k ≤ D.R.rS) (x : D.host.E) :
    LocMem D p (ddPow D k) x ↔ cc δ p ^ k * (D.s.atP p).ιE x ∈ (D.s.atP p).O := by
  have hD := locDiffC_holds D ⟨δ, M, hA⟩ p ⟨D.R.rS - k, by omega⟩
  have e1 : (-((D.R.rS : ℤ) - ((D.R.rS - k : ℕ) : ℤ))) = -(k : ℤ) := by
    rw [Nat.cast_sub hk]; ring
  dsimp only at hD
  rw [e1] at hD
  have hg := frFac_mul δ M hA p ⟨D.R.rS - k, by omega⟩
  simp only [Nat.sub_sub_self hk] at hg
  have hO : (M p).L.O = (D.s.atP p).O := (hA p).2.2.2.1
  unfold LocMem ddPow
  rw [← SetLike.mem_coe, ← LocFacts.lf_span_coe_of_eq hO, hD, LocFacts.lf_span_coe_of_eq hO, SetLike.mem_coe,
    Submodule.mem_span_singleton]
  constructor
  · rintro ⟨o, ho⟩
    rw [← ho, Subring.smul_def, smul_eq_mul, mul_left_comm, mul_comm (cc δ p ^ k), hg, mul_one]
    exact o.2
  · intro h
    refine ⟨⟨_, h⟩, ?_⟩
    rw [Subring.smul_def, smul_eq_mul]
    show cc δ p ^ k * (D.s.atP p).ιE x * frFac δ p ⟨D.R.rS - k, by omega⟩ = (D.s.atP p).ιE x
    rw [mul_comm (cc δ p ^ k), mul_assoc, mul_comm (cc δ p ^ k), hg, mul_one]

/- English proof (translation)
Unfold `LocMem at *`. Rewrite using `[map_sub]`. Conclude with `sub_mem hx hy`.
-/
theorem locMem_sub (I : FI D) {x y : D.host.E} (hx : LocMem D p I x) (hy : LocMem D p I y) :
    LocMem D p I (x - y) := by
  unfold LocMem at *
  rw [map_sub]
  exact sub_mem hx hy

/- English proof (translation)
Rewrite `*` using `[locMem_iff δ M hA p hk]`. Rewrite using `[← (D.s.atP p).cj_ιE, ← cj_cc δ M hA p, ← map_pow, ← map_mul]`. Conclude with `LocFacts.lf_cj_mem p _ h`.
-/
theorem locMem_conj {k : ℕ} (hk : k ≤ D.R.rS) {y : D.host.E} (h : LocMem D p (ddPow D k) y) :
    LocMem D p (ddPow D k) (D.conjF y) := by
  rw [locMem_iff δ M hA p hk] at *
  rw [← (D.s.atP p).cj_ιE, ← cj_cc δ M hA p, ← map_pow, ← map_mul]
  exact LocFacts.lf_cj_mem p _ h

/- English proof (translation)
Establish `h6` using `(hA p).2.2.2.2.2`. Establish `hsD : (D.s.atP p).split = none`. Consider the cases of `hD : (D.s.atP p).split with`. Consider the case `none => rfl`. Consider the case `some sg => rw [hs, hD] at h6`.

Conclude with `h6.elim`. Use `(D.s_split p).not.1 (by rw [hsD]; simp)` as an intermediate fact. Simplify using `only [Finset.mem_insert, Finset.mem_singleton, not_or] at this`. Conclude with `this`.
-/
theorem untyped (hs : (M p).split = none) :
    Loc.resChar p ≠ D.host.g 0 ∧ Loc.resChar p ≠ D.host.g 1 := by
  have h6 := (hA p).2.2.2.2.2
  have hsD : (D.s.atP p).split = none := by
    cases hD : (D.s.atP p).split with
    | none => rfl
    | some sg => rw [hs, hD] at h6; exact h6.elim
  have := (D.s_split p).not.1 (by rw [hsD]; simp)
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at this
  exact this

/- English proof (translation)
Take `⟨h0, h1⟩` from `untyped δ M hA p hs`. Unfold `uP gpart`. Rewrite using `[if_neg h0, if_neg h1]`. Simplify using the standard rewrite rules.
-/
theorem unitAt_untyped (hs : (M p).split = none) : (uP p : ℚ) = 1 / (gS D : ℚ) := by
  obtain ⟨h0, h1⟩ := untyped δ M hA p hs
  unfold uP gpart
  rw [if_neg h0, if_neg h1]
  simp

/- English proof (translation)
Rewrite using `[← map_mul, unitAt_untyped δ M hA p hs]`. Establish `hg : (gS D : ℚ) ≠ 0`. Unfold `gS`. Use `push_cast`. Conclude with `mul_ne_zero (by exact_mod_cast (D.host.g_prime 0).ne_zero) (by exact_mod_cast (D.host.g_prime 1).ne_zero)`.

Establish `: ((gS D : ℕ) : D.host.E) * (((1 / (gS D : ℚ)) : ℚ) : D.host.E) = 1`. Rewrite using `[show ((gS D : ℕ) : D.host.E) = (((gS D : ℚ)) : D.host.E) by push_cast; rfl, ← Rat.cast_mul, mul_one_div_cancel hg, Rat.cast_one]`. Rewrite using `[this, map_one]`.
-/
theorem gS_mul_uP (hs : (M p).split = none) :
    (D.s.atP p).ιE ((gS D : ℕ) : D.host.E) * (D.s.atP p).ιE (uP p : D.host.E) = 1 := by
  rw [← map_mul, unitAt_untyped δ M hA p hs]
  have hg : (gS D : ℚ) ≠ 0 := by
    unfold gS; push_cast
    exact mul_ne_zero (by exact_mod_cast (D.host.g_prime 0).ne_zero) (by exact_mod_cast (D.host.g_prime 1).ne_zero)
  have : ((gS D : ℕ) : D.host.E) * (((1 / (gS D : ℚ)) : ℚ) : D.host.E) = 1 := by
    rw [show ((gS D : ℕ) : D.host.E) = (((gS D : ℚ)) : D.host.E) by push_cast; rfl, ← Rat.cast_mul,
      mul_one_div_cancel hg, Rat.cast_one]
  rw [this, map_one]

omit δ M hA in
/- English proof (translation)
The claim follows from `Ideal.mem_span_singleton_self _`.
-/
theorem gS_mem_qq : ((gS D : ℕ) : 𝓞 D.host.E) ∈ qq D :=
  Ideal.mem_span_singleton_self _

/- English proof (translation)
Unfold `LocMem at *`. Use `set ι := (D.s.atP p).ιE`. Establish `key : ∀ y ∈ Submodule.span (D.s.atP p).O (ι '' (ddPow D k : Set D.host.E)), ι ((gS D : ℕ) : D.host.E) * y ∈ Submodule.span (D.s.atP p).O (ι '' (qdPow D k : Set D.host.E))`. Introduce `y hy`. Proceed by induction on `hy using Submodule.span_induction with`.

Consider the case `mem y hy`. Take `⟨z, hz, rfl⟩` from `hy`. Rewrite using `[← map_mul]`. Apply `Submodule.subset_span` to reduce the goal to its premises. Use `⟨_, ?_, rfl⟩` and prove the remaining obligations.

Unfold `qdPow`. Establish `hq : ((gS D : ℕ) : D.host.E) ∈ (qq D : FI D)`. Rewrite using `[FractionalIdeal.mem_coeIdeal]`. Conclude with `⟨_, gS_mem_qq, map_natCast _ _⟩`. Conclude with `FractionalIdeal.mul_mem_mul hq hz`.

Consider the case `zero => rw [mul_zero]`. Conclude with `zero_mem _`. Consider the case `add y z _ _ hy hz => rw [mul_add]`. Conclude with `add_mem hy hz`. Consider the case `smul o y _ hy`.

Rewrite using `[Subring.smul_def, smul_eq_mul, mul_left_comm, ← smul_eq_mul, ← Subring.smul_def]`. Conclude with `Submodule.smul_mem _ o hy`. Establish `hu : ι (uP p : D.host.E) ∈ (D.s.atP p).O` using `LocFacts.unitPart_mem₂ p`. Establish `e : ι x = ι (uP p : D.host.E) * (ι ((gS D : ℕ) : D.host.E) * ι x)`. Rewrite using `[← mul_assoc, mul_comm (ι (uP p : D.host.E)), gS_mul_uP δ M hA p hs, one_mul]`.

Rewrite using `[e, show ι (uP p : D.host.E) * (ι ((gS D : ℕ) : D.host.E) * ι x) = (⟨_, hu⟩ : (D.s.atP p).O) • (ι ((gS D : ℕ) : D.host.E) * ι x) by rw [Subring.smul_def, smul_eq_mul]]`. Conclude with `Submodule.smul_mem _ _ (key _ h)`.
-/
theorem locMem_qd_of (hs : (M p).split = none) (k : ℕ) {x : D.host.E} (h : LocMem D p (ddPow D k) x) :
    LocMem D p (qdPow D k) x := by
  unfold LocMem at *
  set ι := (D.s.atP p).ιE
  have key : ∀ y ∈ Submodule.span (D.s.atP p).O (ι '' (ddPow D k : Set D.host.E)),
      ι ((gS D : ℕ) : D.host.E) * y ∈ Submodule.span (D.s.atP p).O (ι '' (qdPow D k : Set D.host.E)) := by
    intro y hy
    induction hy using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨z, hz, rfl⟩ := hy
      rw [← map_mul]
      apply Submodule.subset_span
      refine ⟨_, ?_, rfl⟩
      unfold qdPow
      have hq : ((gS D : ℕ) : D.host.E) ∈ (qq D : FI D) := by
        rw [FractionalIdeal.mem_coeIdeal]
        exact ⟨_, gS_mem_qq, map_natCast _ _⟩
      exact FractionalIdeal.mul_mem_mul hq hz
    | zero => rw [mul_zero]; exact zero_mem _
    | add y z _ _ hy hz => rw [mul_add]; exact add_mem hy hz
    | smul o y _ hy =>
      rw [Subring.smul_def, smul_eq_mul, mul_left_comm, ← smul_eq_mul, ← Subring.smul_def]
      exact Submodule.smul_mem _ o hy
  have hu : ι (uP p : D.host.E) ∈ (D.s.atP p).O := LocFacts.unitPart_mem₂ p
  have e : ι x = ι (uP p : D.host.E) * (ι ((gS D : ℕ) : D.host.E) * ι x) := by
    rw [← mul_assoc, mul_comm (ι (uP p : D.host.E)), gS_mul_uP δ M hA p hs, one_mul]
  rw [e, show ι (uP p : D.host.E) * (ι ((gS D : ℕ) : D.host.E) * ι x) =
    (⟨_, hu⟩ : (D.s.atP p).O) • (ι ((gS D : ℕ) : D.host.E) * ι x) by rw [Subring.smul_def, smul_eq_mul]]
  exact Submodule.smul_mem _ _ (key _ h)

/- English proof (translation)
Establish `hcj : (M p).L.cj = (D.s.atP p).cj` using `(hA p).2.2.1`. Simplify using `only [StabShape.lL, Matrix.of_apply, hcj, RingHom.coe_coe]`. Rewrite using `[cj_frFac δ M hA p i, cj_frFac δ M hA p j, inv_frFac δ M hA p j]`. Establish `hi` using `frFac_mul δ M hA p i`. Establish `hji' : j.val < i.val` using `hji`.

Establish `hi' : i.val < D.R.rS + 1` using `i.isLt`. Establish `e : D.R.rS - j.val = (D.R.rS - i.val) + (i.val - j.val)` using `by omega`. Rewrite using `[e, pow_add]`. Take the linear combination `(cc δ p ^ (i.val - j.val) * (D.s.atP p).ιE (a i j)) * hi`.
-/
theorem lL_low (a : MatR D) (i j : Fin (D.R.rS + 1)) (hji : j < i) :
    StabShape.lL (D.s.atP p).ιE ((M p).L.cj : (D.s.atP p).Ep →+* (D.s.atP p).Ep) (frFac δ p) a i j =
      cc δ p ^ (i.val - j.val) * (D.s.atP p).ιE (a i j) := by
  have hcj : (M p).L.cj = (D.s.atP p).cj := (hA p).2.2.1
  simp only [StabShape.lL, Matrix.of_apply, hcj, RingHom.coe_coe]
  rw [cj_frFac δ M hA p i, cj_frFac δ M hA p j, inv_frFac δ M hA p j]
  have hi := frFac_mul δ M hA p i
  have hji' : j.val < i.val := hji
  have hi' : i.val < D.R.rS + 1 := i.isLt
  have e : D.R.rS - j.val = (D.R.rS - i.val) + (i.val - j.val) := by omega
  rw [e, pow_add]
  linear_combination (cc δ p ^ (i.val - j.val) * (D.s.atP p).ιE (a i j)) * hi

/- English proof (translation)
Simplify using `only [StabShape.ρL, Matrix.of_apply, bt]`. Rewrite using `[inv_frFac δ M hA p i]`. Establish `hj` using `frFac_mul δ M hA p j`. Establish `hij' : i.val < j.val` using `hij`. Establish `hj' : j.val < D.R.rS + 1` using `j.isLt`.

Establish `e : D.R.rS - i.val = (D.R.rS - j.val) + (j.val - i.val)` using `by omega`. Rewrite using `[show cc δ p ^ (D.R.rS - i.val) = cc δ p ^ (D.R.rS - j.val) * cc δ p ^ (j.val - i.val) by rw [← pow_add, ← e]]`. Take the linear combination `(cc δ p ^ (j.val - i.val) * (D.s.atP p).ιE ((-1) ^ (D.R.rS - i.val) * b i j * (-1) ^ (D.R.rS - j.val))) * hj`.
-/
theorem ρL_up (b : MatR D) (i j : Fin (D.R.rS + 1)) (hij : i < j) :
    StabShape.ρL (D.s.atP p).ιE (frFac δ p) b i j = cc δ p ^ (j.val - i.val) * (D.s.atP p).ιE (bt D b i j) := by
  simp only [StabShape.ρL, Matrix.of_apply, bt]
  rw [inv_frFac δ M hA p i]
  have hj := frFac_mul δ M hA p j
  have hij' : i.val < j.val := hij
  have hj' : j.val < D.R.rS + 1 := j.isLt
  have e : D.R.rS - i.val = (D.R.rS - j.val) + (j.val - i.val) := by omega
  rw [show cc δ p ^ (D.R.rS - i.val) = cc δ p ^ (D.R.rS - j.val) * cc δ p ^ (j.val - i.val) by rw [← pow_add, ← e]]
  linear_combination (cc δ p ^ (j.val - i.val) *
    (D.s.atP p).ιE ((-1) ^ (D.R.rS - i.val) * b i j * (-1) ^ (D.R.rS - j.val))) * hj

/- English proof (translation)
Unfold `Loc.Model.R`. Rewrite using `[hs]`. Conclude with `(hA p).2.2.2.1`.
-/
theorem R_none (hs : (M p).split = none) : (M p).R = (D.s.atP p).O := by
  unfold Loc.Model.R
  rw [hs]
  exact (hA p).2.2.2.1

/- English proof (translation)
Establish `hR` using `R_none δ M hA p hs`. Establish `hl : StabShape.lOf δ M p a b = StabShape.lL (D.s.atP p).ιE ((M p).L.cj : (D.s.atP p).Ep →+* (D.s.atP p).Ep) (frFac δ p) a`. Simplify using `only [StabShape.lOf, hs]`. Prove the components needed by the constructor for the conclusion. Introduce `h i j hji`.

Use `h.2.2 i j` as an intermediate fact. Rewrite `this` using `[hR, hl, lL_low δ M hA p a i j hji]`. Conclude with `this`. Introduce `h`. Use `⟨StabShape.lOf_diag δ M (hA p) a b ha hb, fun i j hij => ?_, fun i j => ?_⟩` and prove the remaining obligations.

Rewrite using `[hl]`. Simplify using `[StabShape.lL, (ha i j).1 hij]`. Rewrite using `[hR]`. Break down `lt_trichotomy j i with hji | rfl | hij` into its components or cases. Rewrite using `[hl, lL_low δ M hA p a i j hji]`.

Conclude with `h i j hji`. Rewrite using `[StabShape.lOf_diag δ M (hA p) a b ha hb]`. Conclude with `Subring.one_mem _`. Rewrite using `[hl]`. Simplify using `[StabShape.lL, (ha i j).1 hij]`.
-/
theorem intLow_iff_L (hs : (M p).split = none) {a b : MatR D} (ha : IsLoUni a) (hb : IsUpUni b) :
    Formalism.MainNotions.S.TieN.IntLow (M p) (StabShape.lOf δ M p a b) ↔
      ∀ i j : Fin (D.R.rS + 1), j < i → cc δ p ^ (i.val - j.val) * (D.s.atP p).ιE (a i j) ∈ (D.s.atP p).O := by
  have hR := R_none δ M hA p hs
  have hl : StabShape.lOf δ M p a b =
      StabShape.lL (D.s.atP p).ιE ((M p).L.cj : (D.s.atP p).Ep →+* (D.s.atP p).Ep) (frFac δ p) a := by
    simp only [StabShape.lOf, hs]
  constructor
  · intro h i j hji
    have := h.2.2 i j
    rw [hR, hl, lL_low δ M hA p a i j hji] at this
    exact this
  · intro h
    refine ⟨StabShape.lOf_diag δ M (hA p) a b ha hb, fun i j hij => ?_, fun i j => ?_⟩
    · rw [hl]; simp [StabShape.lL, (ha i j).1 hij]
    · rw [hR]
      rcases lt_trichotomy j i with hji | rfl | hij
      · rw [hl, lL_low δ M hA p a i j hji]; exact h i j hji
      · rw [StabShape.lOf_diag δ M (hA p) a b ha hb]; exact Subring.one_mem _
      · rw [hl]; simp [StabShape.lL, (ha i j).1 hij]

/- English proof (translation)
Establish `hR` using `R_none δ M hA p hs`. Establish `hr : StabShape.ρOf δ M p a b = StabShape.ρL (D.s.atP p).ιE (frFac δ p) b`. Simplify using `only [StabShape.ρOf, hs]`. Prove the components needed by the constructor for the conclusion. Introduce `h i j hji`.

Use `h.2.2 j i` as an intermediate fact. Rewrite `this` using `[hR, hr, ρL_up δ M hA p b j i hji]`. Conclude with `this`. Introduce `h`. Use `⟨StabShape.ρOf_diag δ M (hA p) a b ha hb, fun i j hji => ?_, fun i j => ?_⟩` and prove the remaining obligations.

Rewrite using `[hr]`. Simplify using `[StabShape.ρL, (hb i j).1 hji]`. Rewrite using `[hR]`. Break down `lt_trichotomy i j with hij | rfl | hji` into its components or cases. Rewrite using `[hr, ρL_up δ M hA p b i j hij]`.

Conclude with `h j i hij`. Rewrite using `[StabShape.ρOf_diag δ M (hA p) a b ha hb]`. Conclude with `Subring.one_mem _`. Rewrite using `[hr]`. Simplify using `[StabShape.ρL, (hb i j).1 hji]`.
-/
theorem intUp_iff_L (hs : (M p).split = none) {a b : MatR D} (ha : IsLoUni a) (hb : IsUpUni b) :
    Formalism.MainNotions.S.TieN.IntUp (M p) (StabShape.ρOf δ M p a b) ↔
      ∀ i j : Fin (D.R.rS + 1), j < i → cc δ p ^ (i.val - j.val) * (D.s.atP p).ιE (bt D b j i) ∈ (D.s.atP p).O := by
  have hR := R_none δ M hA p hs
  have hr : StabShape.ρOf δ M p a b = StabShape.ρL (D.s.atP p).ιE (frFac δ p) b := by
    simp only [StabShape.ρOf, hs]
  constructor
  · intro h i j hji
    have := h.2.2 j i
    rw [hR, hr, ρL_up δ M hA p b j i hji] at this
    exact this
  · intro h
    refine ⟨StabShape.ρOf_diag δ M (hA p) a b ha hb, fun i j hji => ?_, fun i j => ?_⟩
    · rw [hr]; simp [StabShape.ρL, (hb i j).1 hji]
    · rw [hR]
      rcases lt_trichotomy i j with hij | rfl | hji
      · rw [hr, ρL_up δ M hA p b i j hij]; exact h j i hij
      · rw [StabShape.ρOf_diag δ M (hA p) a b ha hb]; exact Subring.one_mem _
      · rw [hr]; simp [StabShape.ρL, (hb i j).1 hji]

omit δ M hA p in

/- English proof (translation)
Introduce `δ M p hA hs a b ha hb`. Rewrite using `[intLow_iff_L δ M hA p hs ha hb, intUp_iff_L δ M hA p hs ha hb]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨h1, h2⟩ i j hji`. Establish `hk : i.val - j.val ≤ D.R.rS` using `by have := i.isLt; omega`.

Establish `m1` using `(locMem_iff δ M hA p hk (a i j)).2 (h1 i j hji)`. Establish `m2` using `(locMem_iff δ M hA p hk (bt D b j i)).2 (h2 i j hji)`. Conclude with `⟨m1, m2, locMem_qd_of δ M hA p hs _ (locMem_sub δ M hA p _ m1 (locMem_conj δ M hA p hk m2))⟩`. Introduce `h`. Conclude with `⟨fun i j hji => (locMem_iff δ M hA p (by have := i.isLt; omega) _).1 (h i j hji).1, fun i j hji => (locMem_iff δ M hA p (by have := i.isLt; omega) _).1 (h i j hji).2.1⟩`.
-/
theorem locShapeL : LocShapeL D := by
  intro δ M p hA hs a b ha hb
  rw [intLow_iff_L δ M hA p hs ha hb, intUp_iff_L δ M hA p hs ha hb]
  constructor
  · rintro ⟨h1, h2⟩ i j hji
    have hk : i.val - j.val ≤ D.R.rS := by have := i.isLt; omega
    have m1 := (locMem_iff δ M hA p hk (a i j)).2 (h1 i j hji)
    have m2 := (locMem_iff δ M hA p hk (bt D b j i)).2 (h2 i j hji)
    exact ⟨m1, m2, locMem_qd_of δ M hA p hs _ (locMem_sub δ M hA p _ m1 (locMem_conj δ M hA p hk m2))⟩
  · intro h
    exact ⟨fun i j hji => (locMem_iff δ M hA p (by have := i.isLt; omega) _).1 (h i j hji).1,
      fun i j hji => (locMem_iff δ M hA p (by have := i.isLt; omega) _).1 (h i j hji).2.1⟩

end Formalism.L2.SG.Pf.StabIntSh

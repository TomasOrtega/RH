import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsStratHom
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BhattScholzeIntegral
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.KerThetaLocalizedEqSpanFontaineXiElement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdicCompletionPrincipalPerfect
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EisensteinDivClosedDiscOfTopBasis
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AinfAdicTopologicalBasisOverBreuilKisinStatement
import Development.AbelianVarietyTheory.CrystallinePeriods.RingIface
import Development.AbelianVarietyTheory.CrystallinePeriods.AdicMaps

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc
open scoped Formalism.Per NNReal

noncomputable section

namespace GlobalTheory.AcrisDisc

variable {l : ℕ} [hl : Fact l.Prime] {K : FinExt l} (bk : BK K)

/- English proof (translation)
The claim follows from `GlobalTheory.RingIface.ev_alg l n x`.
-/
theorem ev_alg (n : ℕ) (x : Per.AinfP l) :
    Per.ev l n (algebraMap (Per.AinfP l) (Per.BdRp l) x) = Ideal.Quotient.mk _ x :=
  GlobalTheory.RingIface.ev_alg l n x

/- English proof (translation)
Establish `hl0 : (0 : ℝ) < l` using `Nat.cast_pos.2 hl.out.pos`. Establish `e : ((l : ℕ) : bk.DA bk.ρ₀) = ofPre l (bk.ev X) bk.ρ₀ (algebraMap (Ainf l) (PreDisc l (bk.ev X) bk.ρ₀) (((l : ℕ) : Ainf l) ^ 1 * (bk.ev X) ^ 0) * IsLocalization.Away.invSelf ((l : ℕ) : Ainf l) ^ 0)`. Simplify using `[map_natCast]`. Rewrite using `[e, norm_ofPre]`. Conclude with `gauge_le l (bk.ev X) bk.ρ₀ (inv_pos.2 hl0) (Submodule.subset_span ⟨1, 0, 0, by`.

Rewrite using `[pow_zero, pow_zero, pow_one, inv_mul_cancel₀ hl0.ne', mul_one], rfl⟩)`.
-/
theorem norm_l_le : ‖((l : ℕ) : bk.DA bk.ρ₀)‖ ≤ (l : ℝ)⁻¹ := by
  have hl0 : (0 : ℝ) < l := Nat.cast_pos.2 hl.out.pos
  have e : ((l : ℕ) : bk.DA bk.ρ₀) = ofPre l (bk.ev X) bk.ρ₀
      (algebraMap (Ainf l) (PreDisc l (bk.ev X) bk.ρ₀) (((l : ℕ) : Ainf l) ^ 1 * (bk.ev X) ^ 0) *
        IsLocalization.Away.invSelf ((l : ℕ) : Ainf l) ^ 0) := by
    simp [map_natCast]
  rw [e, norm_ofPre]
  exact gauge_le l (bk.ev X) bk.ρ₀ (inv_pos.2 hl0) (Submodule.subset_span ⟨1, 0, 0, by
    rw [pow_zero, pow_zero, pow_one, inv_mul_cancel₀ hl0.ne', mul_one], rfl⟩)

/- English proof (translation)
Proceed by induction on `r with`. Consider the case `zero => simpa using norm_toDisc_le (l := l) (u := bk.ev X) (ρ := bk.ρ₀) (1 : Ainf l)`. Consider the case `succ r ih`. Rewrite using `[pow_succ, pow_succ]`. Conclude with `(norm_mul_le _ _).trans (mul_le_mul ih (norm_l_le bk) (norm_nonneg _) (by positivity))`.
-/
theorem norm_l_pow_le (r : ℕ) : ‖((l : ℕ) : bk.DA bk.ρ₀) ^ r‖ ≤ ((l : ℝ)⁻¹) ^ r := by
  induction r with
  | zero => simpa using norm_toDisc_le (l := l) (u := bk.ev X) (ρ := bk.ρ₀) (1 : Ainf l)
  | succ r ih =>
    rw [pow_succ, pow_succ]
    exact (norm_mul_le _ _).trans (mul_le_mul ih (norm_l_le bk) (norm_nonneg _) (by positivity))

def psi : Per.AinfP l →+* bk.DA bk.ρ₀ :=
  IsLocalization.Away.lift (S := Per.AinfP l) ((l : ℕ) : Per.Ainf l) (g := bk.iA)
    (by rw [map_natCast]; exact isUnit_l_disc l (bk.ev X) bk.ρ₀)

/- English proof (translation)
The claim follows from `IsLocalization.Away.lift_eq _ _ a`.
-/
theorem psi_alg_pt (a : Per.Ainf l) : psi bk (algebraMap (Per.Ainf l) (Per.AinfP l) a) = bk.iA a :=
  IsLocalization.Away.lift_eq _ _ a

/- English proof (translation)
Use `set ψ : Per.AinfP l →+* bk.DA bk.ρ₀ := psi bk with hψ`. Establish `hψa : ∀ a : Ainf l, ψ (algebraMap (Ainf l) (Per.AinfP l) a) = bk.iA a` using `psi_alg_pt bk`. Take `⟨n, a, h⟩` from `IsLocalization.Away.surj ((l : ℕ) : Per.Ainf l) (s : Per.AinfP l)`. Establish `hs : s * ((l : ℕ) : Per.Acris0 l) ^ n = algebraMap (Per.Ainf l) (Per.Acris0 l) a`. Apply `Subtype.ext` to reduce the goal to its premises.

Use `show (s : Per.AinfP l) * ((l : ℕ) : Per.AinfP l) ^ n = algebraMap (Per.Ainf l) (Per.AinfP l) a`. Rewrite using `[← h, map_natCast]`. Establish `hu : IsUnit (((l : ℕ) : bk.DA bk.ρ₀) ^ n)` using `(isUnit_l_disc l (bk.ev X) bk.ρ₀).pow n`. Use `hu.mul_left_injective ?_` and prove the remaining obligations. Establish `h1` using `congrArg (fun t => γ (algebraMap (Per.Acris0 l) (Per.Acris l) t)) hs`.

Simplify using `only [map_mul, map_pow, map_natCast] at h1`. Establish `h2` using `congrArg ψ h`. Simplify using `only [map_mul, map_pow, map_natCast] at h2`. Rewrite `h1` using `[← GlobalTheory.RingIface.tower l a]`. Conclude with `h1.trans ((hγ a).trans ((hψa a).symm.trans h2.symm))`.
-/
theorem gamma_acris0 (γ : Per.Acris l →+* bk.DA bk.ρ₀)
    (hγ : ∀ a : Ainf l, γ (algebraMap (Ainf l) (Per.Acris l) a) = bk.iA a) (s : Per.Acris0 l) :
    γ (algebraMap (Per.Acris0 l) (Per.Acris l) s) =
      psi bk (s : Per.AinfP l) := by
  set ψ : Per.AinfP l →+* bk.DA bk.ρ₀ := psi bk with hψ
  have hψa : ∀ a : Ainf l, ψ (algebraMap (Ainf l) (Per.AinfP l) a) = bk.iA a := psi_alg_pt bk
  obtain ⟨n, a, h⟩ := IsLocalization.Away.surj ((l : ℕ) : Per.Ainf l) (s : Per.AinfP l)
  have hs : s * ((l : ℕ) : Per.Acris0 l) ^ n = algebraMap (Per.Ainf l) (Per.Acris0 l) a := by
    apply Subtype.ext
    show (s : Per.AinfP l) * ((l : ℕ) : Per.AinfP l) ^ n = algebraMap (Per.Ainf l) (Per.AinfP l) a
    rw [← h, map_natCast]
  have hu : IsUnit (((l : ℕ) : bk.DA bk.ρ₀) ^ n) := (isUnit_l_disc l (bk.ev X) bk.ρ₀).pow n
  refine hu.mul_left_injective ?_
  have h1 := congrArg (fun t => γ (algebraMap (Per.Acris0 l) (Per.Acris l) t)) hs
  simp only [map_mul, map_pow, map_natCast] at h1
  have h2 := congrArg ψ h
  simp only [map_mul, map_pow, map_natCast] at h2
  rw [← GlobalTheory.RingIface.tower l a] at h1
  exact h1.trans ((hγ a).trans ((hψa a).symm.trans h2.symm))

end GlobalTheory.AcrisDisc

namespace GlobalTheory.AcrisDisc

/- English proof (translation)
Take `⟨ι, ⟨TB⟩⟩` from `GlobalTheory.T.ainf_adicTopologicalBasis_over_breuilKisin l K bk`. Establish `hρ0 : 0 < bk.ρ₀` using `NNReal.rpow_pos (Nat.cast_pos.2 hl.out.pos)`. Establish `hρ1 : bk.ρ₀ < 1` using `NNReal.rpow_lt_one_of_one_lt_of_neg (Nat.one_lt_cast.2 hl.out.one_lt) (neg_neg_of_pos (one_div_pos.2 (Nat.cast_pos.2 bk.deg_pos)))`. Establish `hnorm` using `norm_E_mul_of_topBasis l K bk (Ainf l) bk.ev ι TB bk.ρ₀ le_rfl hρ1`. Use `set c : ℝ := (bk.ρ₀ : ℝ) ^ bk.Ep.natDegree with hc_def`.

Establish `hc : 0 < c` using `pow_pos (by exact_mod_cast hρ0) _`. Establish `hpow : ∀ (k : ℕ) (v : bk.DA bk.ρ₀), c ^ k * ‖v‖ ≤ ‖bk.iS bk.E ^ k * v‖`. Introduce `k`. Proceed by induction on `k with`. Consider the case `zero => intro v`.

Simplify using the standard rewrite rules. Consider the case `succ k ih`. Introduce `v`. Establish `e` using `hnorm (bk.iS bk.E ^ k * v)`. Express the relevant statement in the definitionally equal form `‖bk.iS bk.E * (bk.iS bk.E ^ k * v)‖ = c * ‖bk.iS bk.E ^ k * v‖ at e`.

Establish `e2 : bk.iS bk.E ^ (k + 1) * v = bk.iS bk.E * (bk.iS bk.E ^ k * v)` using `by rw [pow_succ', mul_assoc]`. Rewrite using `[e2, e, pow_succ', mul_assoc]`. Conclude with `mul_le_mul_of_nonneg_left (ih v) hc.le`. Use `set f := AddMonoidHom.mulLeft (bk.iS bk.E ^ m) with hf`. Establish `hcm : 0 < c ^ m` using `pow_pos hc m`.

Establish `hb : ∀ v, ‖v‖ ≤ ((Real.toNNReal (c ^ m)⁻¹ : ℝ≥0) : ℝ) * ‖f v‖` using `fun v => by`. Rewrite using `[Real.coe_toNNReal _ (inv_nonneg.2 hcm.le), hf, AddMonoidHom.coe_mulLeft, inv_mul_eq_div, le_div_iff₀ hcm, mul_comm]`. Conclude with `hpow m v`. Conclude with `(AddMonoidHomClass.antilipschitz_of_bound f hb).isClosed_range (AddMonoidHomClass.uniformContinuous_of_bound f ‖bk.iS bk.E ^ m‖ fun v => norm_mul_le _ _)`.
-/
theorem isClosed_range_E_pow {l : ℕ} [hl : Fact l.Prime] {K : FinExt l} (bk : BK K) (m : ℕ) :
    IsClosed (Set.range fun v : bk.DA bk.ρ₀ => bk.iS bk.E ^ m * v) := by
  obtain ⟨ι, ⟨TB⟩⟩ := GlobalTheory.T.ainf_adicTopologicalBasis_over_breuilKisin l K bk
  have hρ0 : 0 < bk.ρ₀ := NNReal.rpow_pos (Nat.cast_pos.2 hl.out.pos)
  have hρ1 : bk.ρ₀ < 1 := NNReal.rpow_lt_one_of_one_lt_of_neg (Nat.one_lt_cast.2 hl.out.one_lt)
    (neg_neg_of_pos (one_div_pos.2 (Nat.cast_pos.2 bk.deg_pos)))
  have hnorm := norm_E_mul_of_topBasis l K bk (Ainf l) bk.ev ι TB bk.ρ₀ le_rfl hρ1
  set c : ℝ := (bk.ρ₀ : ℝ) ^ bk.Ep.natDegree with hc_def
  have hc : 0 < c := pow_pos (by exact_mod_cast hρ0) _
  have hpow : ∀ (k : ℕ) (v : bk.DA bk.ρ₀), c ^ k * ‖v‖ ≤ ‖bk.iS bk.E ^ k * v‖ := by
    intro k
    induction k with
    | zero => intro v; simp
    | succ k ih =>
      intro v
      have e := hnorm (bk.iS bk.E ^ k * v)
      change ‖bk.iS bk.E * (bk.iS bk.E ^ k * v)‖ = c * ‖bk.iS bk.E ^ k * v‖ at e
      have e2 : bk.iS bk.E ^ (k + 1) * v = bk.iS bk.E * (bk.iS bk.E ^ k * v) := by rw [pow_succ', mul_assoc]
      rw [e2, e, pow_succ', mul_assoc]
      exact mul_le_mul_of_nonneg_left (ih v) hc.le
  set f := AddMonoidHom.mulLeft (bk.iS bk.E ^ m) with hf
  have hcm : 0 < c ^ m := pow_pos hc m
  have hb : ∀ v, ‖v‖ ≤ ((Real.toNNReal (c ^ m)⁻¹ : ℝ≥0) : ℝ) * ‖f v‖ := fun v => by
    rw [Real.coe_toNNReal _ (inv_nonneg.2 hcm.le), hf, AddMonoidHom.coe_mulLeft, inv_mul_eq_div,
      le_div_iff₀ hcm, mul_comm]
    exact hpow m v
  exact (AddMonoidHomClass.antilipschitz_of_bound f hb).isClosed_range
    (AddMonoidHomClass.uniformContinuous_of_bound f ‖bk.iS bk.E ^ m‖ fun v => norm_mul_le _ _)

/- English proof (translation)
Rewrite using `[← Ideal.Quotient.eq_zero_iff_mem]`. Establish `hmemF : C.j (((l : ℕ) : Per.Acris l) ^ N * (algebraMap (Per.Acris0 l) (Per.Acris l) s + ((l : ℕ) : Per.Acris l) ^ r * z)) ∈ Per.FilP l m`. Rewrite using `[map_mul]`. Conclude with `Ideal.mul_mem_left _ _ hy`. Establish `h0 : Per.ev l m (C.j (((l : ℕ) : Per.Acris l) ^ N * (algebraMap (Per.Acris0 l) (Per.Acris l) s + ((l : ℕ) : Per.Acris l) ^ r * z))) = 0` using `(GlobalTheory.RingIface.mem_filtration_iff_mem_kerTheta_pow l m _).1 hmemF`.

Establish `e : C.j (((l : ℕ) : Per.Acris l) ^ N * (algebraMap (Per.Acris0 l) (Per.Acris l) s + ((l : ℕ) : Per.Acris l) ^ r * z)) = ((l : ℕ) : Per.BdRp l) ^ N * algebraMap (Per.AinfP l) (Per.BdRp l) (s : Per.AinfP l) + ((l : ℕ) : Per.BdRp l) ^ r * (((l : ℕ) : Per.BdRp l) ^ N * C.j z)`. Rewrite using `[map_mul, map_add, map_mul, map_pow, map_pow, map_natCast, C.j_cris.on0]`. Expand and normalize the polynomial expressions, which then agree. Rewrite `h0` using `[e, map_add, map_mul, map_mul, ha, map_pow, map_pow, map_natCast, ev_alg]`. Rewrite using `[map_add, map_mul, map_mul, map_pow, map_pow, map_natCast]`.

Conclude with `h0`.
-/
theorem mem_kerTheta_pow_of_mem_filtration {l : ℕ} [hl : Fact l.Prime] (C : Core l) (m N r : ℕ) (s : Per.Acris0 l) (z : Per.Acris l)
    (a : Per.Ainf l)
    (ha : Per.ev l m (((l : ℕ) : Per.BdRp l) ^ N * C.j z) =
      Ideal.Quotient.mk _ (algebraMap (Per.Ainf l) (Per.AinfP l) a))
    (hy : C.j (algebraMap (Per.Acris0 l) (Per.Acris l) s + ((l : ℕ) : Per.Acris l) ^ r * z) ∈ Per.FilP l m) :
    ((l : ℕ) : Per.AinfP l) ^ N * (s : Per.AinfP l) +
      ((l : ℕ) : Per.AinfP l) ^ r * algebraMap (Per.Ainf l) (Per.AinfP l) a ∈ Per.kerP l ^ m := by
  rw [← Ideal.Quotient.eq_zero_iff_mem]
  have hmemF : C.j (((l : ℕ) : Per.Acris l) ^ N *
      (algebraMap (Per.Acris0 l) (Per.Acris l) s + ((l : ℕ) : Per.Acris l) ^ r * z)) ∈ Per.FilP l m := by
    rw [map_mul]; exact Ideal.mul_mem_left _ _ hy
  have h0 : Per.ev l m (C.j (((l : ℕ) : Per.Acris l) ^ N *
      (algebraMap (Per.Acris0 l) (Per.Acris l) s + ((l : ℕ) : Per.Acris l) ^ r * z))) = 0 :=
    (GlobalTheory.RingIface.mem_filtration_iff_mem_kerTheta_pow l m _).1 hmemF
  have e : C.j (((l : ℕ) : Per.Acris l) ^ N *
      (algebraMap (Per.Acris0 l) (Per.Acris l) s + ((l : ℕ) : Per.Acris l) ^ r * z)) =
      ((l : ℕ) : Per.BdRp l) ^ N * algebraMap (Per.AinfP l) (Per.BdRp l) (s : Per.AinfP l) +
      ((l : ℕ) : Per.BdRp l) ^ r * (((l : ℕ) : Per.BdRp l) ^ N * C.j z) := by
    rw [map_mul, map_add, map_mul, map_pow, map_pow, map_natCast, C.j_cris.on0]
    ring
  rw [e, map_add, map_mul, map_mul, ha, map_pow, map_pow, map_natCast, ev_alg] at h0
  rw [map_add, map_mul, map_mul, map_pow, map_pow, map_natCast]
  exact h0

/- English proof (translation)
Take `⟨e, he⟩` from `GlobalTheory.AdicMaps.exists_acris_completion l`. Take `⟨s, z, h⟩` from `GlobalTheory.PerfectCompletion.dense ((l : ℕ) : Per.Acris0 l) (e y) r`. Use `⟨s, e.symm z, e.injective ?_⟩` and prove the remaining obligations. Rewrite using `[map_add, map_mul, map_pow, map_natCast, he, e.apply_symm_apply, ← map_natCast (algebraMap (Per.Acris0 l) (AdicCompletion (Ideal.span {((l : ℕ) : Per.Acris0 l)}) (Per.Acris0 l)))]`. Conclude with `h`.
-/
theorem acris_dense {l : ℕ} [Fact l.Prime] (y : Per.Acris l) (r : ℕ) :
    ∃ (s : Per.Acris0 l) (z : Per.Acris l),
      y = algebraMap (Per.Acris0 l) (Per.Acris l) s + ((l : ℕ) : Per.Acris l) ^ r * z := by
  obtain ⟨e, he⟩ := GlobalTheory.AdicMaps.exists_acris_completion l
  obtain ⟨s, z, h⟩ := GlobalTheory.PerfectCompletion.dense ((l : ℕ) : Per.Acris0 l) (e y) r
  refine ⟨s, e.symm z, e.injective ?_⟩
  rw [map_add, map_mul, map_pow, map_natCast, he, e.apply_symm_apply,
    ← map_natCast (algebraMap (Per.Acris0 l) (AdicCompletion (Ideal.span {((l : ℕ) : Per.Acris0 l)}) (Per.Acris0 l)))]
  exact h

/- English proof (translation)
Use `set ψ : Per.AinfP l →+* bk.DA bk.ρ₀ := psi bk with hψ`. Establish `hE : ψ (algebraMap (Per.Ainf l) (Per.AinfP l) (bk.ev bk.E)) = bk.iS bk.E` using `psi_alg_pt bk _`. Establish `ha : ψ (algebraMap (Per.Ainf l) (Per.AinfP l) a) = bk.iA a` using `psi_alg_pt bk _`. Establish `hx` using `congrArg ψ hw`. Rewrite `hx` using `[map_add, map_mul, map_mul, map_pow, map_pow, map_natCast, ha, map_mul, map_pow, hE]`.

Establish `hdiff : ((l : ℕ) : bk.DA bk.ρ₀) ^ N * γ (algebraMap (Per.Acris0 l) (Per.Acris l) s + ((l : ℕ) : Per.Acris l) ^ r * z) - bk.iS bk.E ^ m * ψ w = ((l : ℕ) : bk.DA bk.ρ₀) ^ r * (γ (((l : ℕ) : Per.Acris l) ^ N * z) - bk.iA a)`. Rewrite using `[← hx, map_add, gamma_acris0 bk γ hγ s, map_mul, map_mul, map_pow, map_pow, map_natCast]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[hdiff]`. Use `(norm_mul_le _ _).trans (mul_le_mul (norm_l_pow_le bk r) ?_ (norm_nonneg _) (by positivity))` and prove the remaining obligations.

Use `(norm_sub_le _ _).trans ?_` and prove the remaining obligations. Use `norm_toDisc_le (l := l) (u := bk.ev X) (ρ := bk.ρ₀) a` as an intermediate fact. Use `h1 (((l : ℕ) : Per.Acris l) ^ N * z)` as an intermediate fact. Express the relevant statement in the definitionally equal form `‖bk.iA a‖ ≤ 1 at *`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem approx {l : ℕ} [hl : Fact l.Prime] {K : FinExt l} (bk : BK K) (γ : Per.Acris l →+* bk.DA bk.ρ₀)
    (hγ : ∀ a : Ainf l, γ (algebraMap (Ainf l) (Per.Acris l) a) = bk.iA a) (h1 : ∀ x, ‖γ x‖ ≤ 1)
    (m N r : ℕ) (s : Per.Acris0 l) (z : Per.Acris l) (a : Per.Ainf l) (w : Per.AinfP l)
    (hw : ((l : ℕ) : Per.AinfP l) ^ N * (s : Per.AinfP l) +
      ((l : ℕ) : Per.AinfP l) ^ r * algebraMap (Per.Ainf l) (Per.AinfP l) a =
        algebraMap (Per.Ainf l) (Per.AinfP l) (bk.ev bk.E) ^ m * w) :
    ‖((l : ℕ) : bk.DA bk.ρ₀) ^ N * γ (algebraMap (Per.Acris0 l) (Per.Acris l) s + ((l : ℕ) : Per.Acris l) ^ r * z) -
      bk.iS bk.E ^ m * psi bk w‖ ≤ ((l : ℝ)⁻¹) ^ r * 2 := by
  set ψ : Per.AinfP l →+* bk.DA bk.ρ₀ := psi bk with hψ
  have hE : ψ (algebraMap (Per.Ainf l) (Per.AinfP l) (bk.ev bk.E)) = bk.iS bk.E := psi_alg_pt bk _
  have ha : ψ (algebraMap (Per.Ainf l) (Per.AinfP l) a) = bk.iA a := psi_alg_pt bk _
  have hx := congrArg ψ hw
  rw [map_add, map_mul, map_mul, map_pow, map_pow, map_natCast, ha, map_mul, map_pow, hE] at hx
  have hdiff : ((l : ℕ) : bk.DA bk.ρ₀) ^ N *
      γ (algebraMap (Per.Acris0 l) (Per.Acris l) s + ((l : ℕ) : Per.Acris l) ^ r * z) - bk.iS bk.E ^ m * ψ w =
      ((l : ℕ) : bk.DA bk.ρ₀) ^ r * (γ (((l : ℕ) : Per.Acris l) ^ N * z) - bk.iA a) := by
    rw [← hx, map_add, gamma_acris0 bk γ hγ s, map_mul, map_mul, map_pow, map_pow, map_natCast]
    ring
  rw [hdiff]
  refine (norm_mul_le _ _).trans (mul_le_mul (norm_l_pow_le bk r) ?_ (norm_nonneg _) (by positivity))
  refine (norm_sub_le _ _).trans ?_
  have := norm_toDisc_le (l := l) (u := bk.ev X) (ρ := bk.ρ₀) a
  have := h1 (((l : ℕ) : Per.Acris l) ^ N * z)
  change ‖bk.iA a‖ ≤ 1 at *
  linarith

/- English proof (translation)
Introduce `l hl K bk C γ hγ h1 m y hy`. Establish `hker : Per.kerP l ^ m = Ideal.span {algebraMap (Per.Ainf l) (Per.AinfP l) (bk.ev bk.E) ^ m}`. Rewrite using `[ker_localizedTheta_eq_span_of_dvd l (bk.ev bk.E) fun a => by`. Rewrite using `[← RingHom.mem_ker, ← bk.span_ev, Ideal.mem_span_singleton], Ideal.span_singleton_pow]`. Take `⟨N, hN⟩` from `C.j_cris.bdd m`.

Establish `hmem : ((l : ℕ) : bk.DA bk.ρ₀) ^ N * γ y ∈ closure (Set.range fun v : bk.DA bk.ρ₀ => bk.iS bk.E ^ m * v)`. Rewrite using `[Metric.mem_closure_iff]`. Introduce `ε hε`. Establish `hlt : (l : ℝ)⁻¹ < 1` using `inv_lt_one_of_one_lt₀ (Nat.one_lt_cast.2 hl.out.one_lt)`. Take `⟨r, hr⟩` from `exists_pow_lt_of_lt_one (half_pos hε) hlt`.

Take `⟨s, z, hyz⟩` from `acris_dense y r`. Take `⟨a, ha⟩` from `hN z`. Establish `hx` using `mem_kerTheta_pow_of_mem_filtration C m N r s z a ha (hyz ▸ hy)`. Rewrite `hx` using `[hker, Ideal.mem_span_singleton]`. Take `⟨w, hw⟩` from `hx`.

Use `⟨bk.iS bk.E ^ m * psi bk w, ⟨psi bk w, rfl⟩, ?_⟩` and prove the remaining obligations. Rewrite using `[dist_eq_norm, hyz]`. Use `approx bk γ hγ h1 m N r s z a w hw` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion. Rewrite `hmem` using `[(isClosed_range_E_pow bk m).closure_eq]`.

Take `⟨v, hv⟩` from `hmem`. Establish `hu : IsUnit (((l : ℕ) : bk.DA bk.ρ₀) ^ N)` using `(isUnit_l_disc l (bk.ev X) bk.ρ₀).pow N`. Rewrite using `[← hu.dvd_mul_left]`. Conclude with `⟨v, hv.symm⟩`.
-/
theorem main : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (C : Core l) (γ : Per.Acris l →+* bk.DA bk.ρ₀),
    (∀ a : Ainf l, γ (algebraMap (Ainf l) (Per.Acris l) a) = bk.iA a) → (∀ x, ‖γ x‖ ≤ 1) →
    ∀ (m : ℕ) (y : Per.Acris l), C.j y ∈ Per.FilP l m → bk.iS bk.E ^ m ∣ γ y := by
  intro l hl K bk C γ hγ h1 m y hy
  have hker : Per.kerP l ^ m = Ideal.span {algebraMap (Per.Ainf l) (Per.AinfP l) (bk.ev bk.E) ^ m} := by
    rw [ker_localizedTheta_eq_span_of_dvd l (bk.ev bk.E) fun a => by
      rw [← RingHom.mem_ker, ← bk.span_ev, Ideal.mem_span_singleton], Ideal.span_singleton_pow]
  obtain ⟨N, hN⟩ := C.j_cris.bdd m
  have hmem : ((l : ℕ) : bk.DA bk.ρ₀) ^ N * γ y ∈ closure (Set.range fun v : bk.DA bk.ρ₀ => bk.iS bk.E ^ m * v) := by
    rw [Metric.mem_closure_iff]
    intro ε hε
    have hlt : (l : ℝ)⁻¹ < 1 := inv_lt_one_of_one_lt₀ (Nat.one_lt_cast.2 hl.out.one_lt)
    obtain ⟨r, hr⟩ := exists_pow_lt_of_lt_one (half_pos hε) hlt
    obtain ⟨s, z, hyz⟩ := acris_dense y r
    obtain ⟨a, ha⟩ := hN z
    have hx := mem_kerTheta_pow_of_mem_filtration C m N r s z a ha (hyz ▸ hy)
    rw [hker, Ideal.mem_span_singleton] at hx
    obtain ⟨w, hw⟩ := hx
    refine ⟨bk.iS bk.E ^ m * psi bk w, ⟨psi bk w, rfl⟩, ?_⟩
    rw [dist_eq_norm, hyz]
    have := approx bk γ hγ h1 m N r s z a w hw
    linarith
  rw [(isClosed_range_E_pow bk m).closure_eq] at hmem
  obtain ⟨v, hv⟩ := hmem
  have hu : IsUnit (((l : ℕ) : bk.DA bk.ρ₀) ^ N) := (isUnit_l_disc l (bk.ev X) bk.ρ₀).pow N
  rw [← hu.dvd_mul_left]
  exact ⟨v, hv.symm⟩

end GlobalTheory.AcrisDisc

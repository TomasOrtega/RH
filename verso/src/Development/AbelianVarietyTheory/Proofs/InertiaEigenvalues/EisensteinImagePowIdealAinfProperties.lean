import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TrivIsCr
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TwistStep
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AcrisTorsionFreeComplete
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DeRhamPotSemistable
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinEvWIsUnitInjectiveDvd
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ExistsGenIsUnitSub
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BdRPlusFiltrationEqFontaineXiPow
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.KerThetaLocalizedEqSpanFontaineXiElement
import Development.AbelianVarietyTheory.CrystallinePeriods.RingIface
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal

namespace GlobalTheory.AinfEPow

variable {l : ℕ} [hl : Fact l.Prime] {K : FinExt l} (bk : BK K)

/- English proof (translation)
Introduce `h` and use `bk.E_ne_zero (bk.ev_injective (by rw [h, map_zero]))`.
-/
theorem evE_ne_zero : bk.ev bk.E ≠ 0 := fun h =>
  bk.E_ne_zero (bk.ev_injective (by rw [h, map_zero]))

/- English proof (translation)
Rewrite using `[← RingHom.mem_ker, ← bk.span_ev, Ideal.mem_span_singleton]`.
-/
theorem theta_eq_zero_iff (x : Ainf l) : Per.θ l x = 0 ↔ bk.ev bk.E ∣ x := by
  rw [← RingHom.mem_ker, ← bk.span_ev, Ideal.mem_span_singleton]

/- English proof (translation)
Rewrite `h` using `[map_mul, map_pow, map_natCast]`. Establish `hne : ((l : Per.OC l)) ^ n ≠ 0` using `pow_ne_zero _ (Nat.cast_ne_zero.mpr hl.out.ne_zero)`. Conclude with `(mul_eq_zero.mp h).resolve_left hne`.
-/
theorem theta_of_natPow_mul (n : ℕ) (c : Ainf l) (h : Per.θ l ((l : Ainf l) ^ n * c) = 0) :
    Per.θ l c = 0 := by
  rw [map_mul, map_pow, map_natCast] at h
  have hne : ((l : Per.OC l)) ^ n ≠ 0 := pow_ne_zero _ (Nat.cast_ne_zero.mpr hl.out.ne_zero)
  exact (mul_eq_zero.mp h).resolve_left hne

/- English proof (translation)
Rewrite `h`, the goal using `[← theta_eq_zero_iff]`. Conclude with `theta_of_natPow_mul n c h`.
-/
theorem dvd_of_dvd_natPow_mul (n : ℕ) (c : Ainf l) (h : bk.ev bk.E ∣ (l : Ainf l) ^ n * c) :
    bk.ev bk.E ∣ c := by
  rw [← theta_eq_zero_iff] at h ⊢
  exact theta_of_natPow_mul n c h

/- English proof (translation)
Proceed by induction on `m with`. Consider the case `zero => intro a _`. Simplify using the standard rewrite rules. Consider the case `succ m ih`. Introduce `a h`.

Establish `h1 : bk.ev bk.E ∣ (l : Ainf l) ^ 1 * a`. Rewrite using `[pow_one]`. Conclude with `dvd_trans (dvd_pow_self _ (Nat.succ_ne_zero m)) h`. Take `⟨a', rfl⟩` from `dvd_of_dvd_natPow_mul bk 1 a h1`. Rewrite using `[pow_succ']`.

Apply `mul_dvd_mul_left` to reduce the goal to its premises. Apply `ih` to reduce the goal to its premises. Rewrite `h` using `[pow_succ', mul_left_comm]`. Conclude with `(mul_dvd_mul_iff_left (evE_ne_zero bk)).mp h`.
-/
theorem pow_dvd_of_pow_dvd_l_mul (m : ℕ) : ∀ a : Ainf l,
    bk.ev bk.E ^ m ∣ (l : Ainf l) * a → bk.ev bk.E ^ m ∣ a := by
  induction m with
  | zero => intro a _; simp
  | succ m ih =>
    intro a h
    have h1 : bk.ev bk.E ∣ (l : Ainf l) ^ 1 * a := by
      rw [pow_one]; exact dvd_trans (dvd_pow_self _ (Nat.succ_ne_zero m)) h
    obtain ⟨a', rfl⟩ := dvd_of_dvd_natPow_mul bk 1 a h1
    rw [pow_succ']
    apply mul_dvd_mul_left
    apply ih
    rw [pow_succ', mul_left_comm] at h
    exact (mul_dvd_mul_iff_left (evE_ne_zero bk)).mp h

/- English proof (translation)
Proceed by induction on `k generalizing a with`. Consider the case `zero => simpa using h`. Consider the case `succ k ih`. Apply `ih` to reduce the goal to its premises. Apply `pow_dvd_of_pow_dvd_l_mul bk m` to reduce the goal to its premises.

Rewrite using `[← mul_assoc, ← pow_succ']`. Conclude with `h`.
-/
theorem pow_dvd_of_pow_dvd_lpow_mul (m k : ℕ) (a : Ainf l)
    (h : bk.ev bk.E ^ m ∣ (l : Ainf l) ^ k * a) : bk.ev bk.E ^ m ∣ a := by
  induction k generalizing a with
  | zero => simpa using h
  | succ k ih =>
    apply ih
    apply pow_dvd_of_pow_dvd_l_mul bk m
    rw [← mul_assoc, ← pow_succ']
    exact h

/- English proof (translation)
Proceed by induction on `m with`. Consider the case `zero => intro s _`. Simplify using the standard rewrite rules. Consider the case `succ m ih`. Introduce `s h`.

Establish `h1 : bk.ev bk.E ∣ bk.ev s` using `dvd_trans (dvd_pow_self _ (Nat.succ_ne_zero m)) h`. Establish `hE : bk.E ∣ s` using `by set r := bk.str.symm (Ideal.Quotient.mk (Ideal.span {(bk.Ep : bk.S)}) s) with hr`. Establish `hmk : Ideal.Quotient.mk (Ideal.span {(bk.Ep : bk.S)}) s = bk.str r`. Rewrite using `[hr, RingEquiv.apply_symm_apply]`. Establish `hθ` using `bk.θ_ev r s hmk`.

Rewrite `hθ` using `[(theta_eq_zero_iff bk _).mpr h1]`. Establish `hr0 : r = 0` using `intToOC_injective K (by rw [← hθ, map_zero])`. Rewrite `hmk` using `[hr0, map_zero, Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton]`. Conclude with `hmk`. Take `⟨s', rfl⟩` from `hE`.

Rewrite using `[pow_succ']`. Apply `mul_dvd_mul_left` to reduce the goal to its premises. Apply `ih` to reduce the goal to its premises. Rewrite `h` using `[pow_succ', map_mul]`. Conclude with `(mul_dvd_mul_iff_left (evE_ne_zero bk)).mp h`.
-/
theorem pow_dvd_of_ev_pow_dvd (m : ℕ) : ∀ s : bk.S,
    bk.ev bk.E ^ m ∣ bk.ev s → bk.E ^ m ∣ s := by
  induction m with
  | zero => intro s _; simp
  | succ m ih =>
    intro s h
    have h1 : bk.ev bk.E ∣ bk.ev s := dvd_trans (dvd_pow_self _ (Nat.succ_ne_zero m)) h
    have hE : bk.E ∣ s := by
      set r := bk.str.symm (Ideal.Quotient.mk (Ideal.span {(bk.Ep : bk.S)}) s) with hr
      have hmk : Ideal.Quotient.mk (Ideal.span {(bk.Ep : bk.S)}) s = bk.str r := by
        rw [hr, RingEquiv.apply_symm_apply]
      have hθ := bk.θ_ev r s hmk
      rw [(theta_eq_zero_iff bk _).mpr h1] at hθ
      have hr0 : r = 0 := intToOC_injective K (by rw [← hθ, map_zero])
      rw [hr0, map_zero, Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton] at hmk
      exact hmk
    obtain ⟨s', rfl⟩ := hE
    rw [pow_succ']
    apply mul_dvd_mul_left
    apply ih
    rw [pow_succ', map_mul] at h
    exact (mul_dvd_mul_iff_left (evE_ne_zero bk)).mp h

/- English proof (translation)
Apply `IsHausdorff.haus (IsAdicComplete.toIsHausdorff (I := Ideal.span {(l : Per.OC l)})) y` to reduce the goal to its premises. Introduce `n`. Take `⟨z, hz⟩` from `h n`. Rewrite using `[SModEq.zero, smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow, Ideal.mem_span_singleton]`. Conclude with `⟨z, hz⟩`.
-/
theorem theta_eq_zero_of_forall (y : Per.OC l) (h : ∀ n : ℕ, ∃ z : Per.OC l, y = (l : Per.OC l) ^ n * z) :
    y = 0 := by
  apply IsHausdorff.haus (IsAdicComplete.toIsHausdorff (I := Ideal.span {(l : Per.OC l)})) y
  intro n
  obtain ⟨z, hz⟩ := h n
  rw [SModEq.zero, smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow, Ideal.mem_span_singleton]
  exact ⟨z, hz⟩

/- English proof (translation)
Proceed by induction on `m with`. Consider the case `zero => intro a _`. Simplify using the standard rewrite rules. Consider the case `succ m ih`. Introduce `a h`.

Establish `hθ : Per.θ l a = 0`. Apply `theta_eq_zero_of_forall` to reduce the goal to its premises. Introduce `n`. Take `⟨b, c, hbc⟩` from `h n`. Use `⟨Per.θ l c, ?_⟩` and prove the remaining obligations.

Establish `hE : Per.θ l (bk.ev bk.E) = 0` using `(theta_eq_zero_iff bk _).mpr dvd_rfl`. Rewrite using `[hbc, map_add, map_mul, map_mul, map_pow, map_pow, hE, map_natCast]`. Simplify using the standard rewrite rules. Take `⟨a', rfl⟩` from `(theta_eq_zero_iff bk a).mp hθ`. Rewrite using `[pow_succ']`.

Apply `mul_dvd_mul_left` to reduce the goal to its premises. Apply `ih` to reduce the goal to its premises. Introduce `n`. Take `⟨b, c, hbc⟩` from `h n`. Establish `hc : bk.ev bk.E ∣ (l : Ainf l) ^ n * c` using `⟨a' - bk.ev bk.E ^ m * b, by rw [mul_sub, ← mul_assoc, ← pow_succ', hbc]; ring⟩`.

Take `⟨c', rfl⟩` from `dvd_of_dvd_natPow_mul bk n c hc`. Use `⟨b, c', ?_⟩` and prove the remaining obligations. Apply `mul_left_cancel₀ (evE_ne_zero bk)` to reduce the goal to its premises. Rewrite using `[hbc]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem pow_dvd_of_forall_approx (m : ℕ) : ∀ a : Ainf l,
    (∀ n : ℕ, ∃ b c : Ainf l, a = bk.ev bk.E ^ m * b + (l : Ainf l) ^ n * c) →
      bk.ev bk.E ^ m ∣ a := by
  induction m with
  | zero => intro a _; simp
  | succ m ih =>
    intro a h
    have hθ : Per.θ l a = 0 := by
      apply theta_eq_zero_of_forall
      intro n
      obtain ⟨b, c, hbc⟩ := h n
      refine ⟨Per.θ l c, ?_⟩
      have hE : Per.θ l (bk.ev bk.E) = 0 := (theta_eq_zero_iff bk _).mpr dvd_rfl
      rw [hbc, map_add, map_mul, map_mul, map_pow, map_pow, hE, map_natCast]
      simp
    obtain ⟨a', rfl⟩ := (theta_eq_zero_iff bk a).mp hθ
    rw [pow_succ']
    apply mul_dvd_mul_left
    apply ih
    intro n
    obtain ⟨b, c, hbc⟩ := h n
    have hc : bk.ev bk.E ∣ (l : Ainf l) ^ n * c :=
      ⟨a' - bk.ev bk.E ^ m * b, by rw [mul_sub, ← mul_assoc, ← pow_succ', hbc]; ring⟩
    obtain ⟨c', rfl⟩ := dvd_of_dvd_natPow_mul bk n c hc
    refine ⟨b, c', ?_⟩
    apply mul_left_cancel₀ (evE_ne_zero bk)
    rw [hbc]; ring

/- English proof (translation)
The claim follows from `GlobalTheory.MemLoc.ker_localizedTheta_eq_span_of_dvd l _ (fun a => theta_eq_zero_iff bk a)`.
-/
theorem ker_localizedTheta_eq_span_eisenstein (bk : BK K) : Per.kerP l = Ideal.span {(algebraMap (Per.Ainf l) (Per.AinfP l)) (bk.ev bk.E)} :=
  GlobalTheory.MemLoc.ker_localizedTheta_eq_span_of_dvd l _ (fun a => theta_eq_zero_iff bk a)

/- English proof (translation)
Establish `key : aDp l a ∈ Per.FilP l m ↔ (algebraMap (Per.Ainf l) (Per.AinfP l)) a ∈ Per.kerP l ^ m`. Rewrite using `[GlobalTheory.RingIface.mem_filtration_iff_mem_kerTheta_pow]`. Unfold `aDp`. Rewrite using `[RingHom.comp_apply, GlobalTheory.RingIface.ev_alg]`. Conclude with `Ideal.Quotient.eq_zero_iff_mem`.

Rewrite using `[key, ker_localizedTheta_eq_span_eisenstein bk, Ideal.span_singleton_pow, Ideal.mem_span_singleton, ← map_pow]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨y, hy⟩ haveI : IsLocalization (Submonoid.powers (l : Per.Ainf l)) (Per.AinfP l) := inferInstance`. Take `⟨⟨b, s⟩, hs⟩` from `IsLocalization.surj (Submonoid.powers (l : Per.Ainf l)) y`. Take `⟨k, hk⟩` from `s.2`.

Simplify using `only at hs hk`. Rewrite `hs` using `[← hk]`. Establish `hl0 : (l : Per.Ainf l) ≠ 0` using `fun h => by`. Establish `h'` using `congrArg (Per.θ l) h`. Rewrite `h'` using `[map_natCast, map_zero]`.

Conclude with `(Nat.cast_ne_zero.mpr hl.out.ne_zero) h'`. Establish `hinj : Function.Injective (algebraMap (Per.Ainf l) (Per.AinfP l))` using `IsLocalization.injective (Per.AinfP l) (powers_le_nonZeroDivisors_of_noZeroDivisors hl0)`. Establish `heq : (l : Ainf l) ^ k * a = bk.ev bk.E ^ m * b`. Apply `hinj` to reduce the goal to its premises. Rewrite using `[map_mul, map_mul, ← hs, hy]`.

Expand and normalize the polynomial expressions, which then agree. Conclude with `pow_dvd_of_pow_dvd_lpow_mul bk m k a ⟨b, heq⟩`. Conclude with `fun h => map_dvd _ h`.
-/
theorem mem_filtration_iff_eisenstein_pow_dvd (m : ℕ) (a : Ainf l) :
    aDp l a ∈ Per.FilP l m ↔ bk.ev bk.E ^ m ∣ a := by
  have key : aDp l a ∈ Per.FilP l m ↔
      (algebraMap (Per.Ainf l) (Per.AinfP l)) a ∈ Per.kerP l ^ m := by
    rw [GlobalTheory.RingIface.mem_filtration_iff_mem_kerTheta_pow]
    unfold aDp
    rw [RingHom.comp_apply, GlobalTheory.RingIface.ev_alg]
    exact Ideal.Quotient.eq_zero_iff_mem
  rw [key, ker_localizedTheta_eq_span_eisenstein bk, Ideal.span_singleton_pow, Ideal.mem_span_singleton, ← map_pow]
  constructor
  · rintro ⟨y, hy⟩
    haveI : IsLocalization (Submonoid.powers (l : Per.Ainf l)) (Per.AinfP l) :=
      inferInstance
    obtain ⟨⟨b, s⟩, hs⟩ := IsLocalization.surj (Submonoid.powers (l : Per.Ainf l)) y
    obtain ⟨k, hk⟩ := s.2
    simp only at hs hk
    rw [← hk] at hs
    have hl0 : (l : Per.Ainf l) ≠ 0 := fun h => by
      have h' := congrArg (Per.θ l) h
      rw [map_natCast, map_zero] at h'
      exact (Nat.cast_ne_zero.mpr hl.out.ne_zero) h'
    have hinj : Function.Injective (algebraMap (Per.Ainf l) (Per.AinfP l)) :=
      IsLocalization.injective (Per.AinfP l) (powers_le_nonZeroDivisors_of_noZeroDivisors hl0)
    have heq : (l : Ainf l) ^ k * a = bk.ev bk.E ^ m * b := by
      apply hinj
      rw [map_mul, map_mul, ← hs, hy]
      ring
    exact pow_dvd_of_pow_dvd_lpow_mul bk m k a ⟨b, heq⟩
  · exact fun h => map_dvd _ h

/- English proof (translation)
Introduce `l _ K bk m`. Conclude with `⟨pow_dvd_of_pow_dvd_l_mul bk m, pow_dvd_of_ev_pow_dvd bk m, mem_filtration_iff_eisenstein_pow_dvd bk m, pow_dvd_of_forall_approx bk m⟩`.
-/
theorem ePow_facts : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (m : ℕ), (∀ a : Ainf l, bk.ev bk.E ^ m ∣ (l : Ainf l) * a → bk.ev bk.E ^ m ∣ a) ∧ (∀ s : bk.S, bk.ev bk.E ^ m ∣ bk.ev s → bk.E ^ m ∣ s) ∧ (∀ a : Ainf l, aDp l a ∈ Per.FilP l m ↔ bk.ev bk.E ^ m ∣ a) ∧ ∀ a : Ainf l, (∀ n : ℕ, ∃ b c : Ainf l, a = bk.ev bk.E ^ m * b + (l : Ainf l) ^ n * c) → bk.ev bk.E ^ m ∣ a := by
  intro l _ K bk m
  exact ⟨pow_dvd_of_pow_dvd_l_mul bk m, pow_dvd_of_ev_pow_dvd bk m, mem_filtration_iff_eisenstein_pow_dvd bk m,
    pow_dvd_of_forall_approx bk m⟩

end GlobalTheory.AinfEPow

import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsCrisP
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsAlgClosedTiltFieldAndValuationRing
import Development.AbelianVarietyTheory.CrystallinePeriods.RingBasics
open Formalism
open scoped Formalism.Per

noncomputable section
namespace GlobalTheory.PeriodSol
open Polynomial

variable {l : ℕ} [Fact l.Prime]

/- English proof (translation)
Establish `h0` using `WittVector.dvd_sub_sum_teichmuller_iterateFrobeniusEquiv_coeff (p := l) x 0`. Establish `hI : (Finset.Iic 0 : Finset ℕ) = {0}` using `by ext i; simp`. Rewrite `h0` using `[hI, Finset.sum_singleton]`. Rewrite `h` using `[WittVector.constantCoeff_apply]`. Simplify `h0` using `[h]`.
-/
theorem dvd_of_constantCoeff (x : Per.Ainf l) (h : WittVector.constantCoeff x = 0) :
    (l : Per.Ainf l) ∣ x := by
  have h0 := WittVector.dvd_sub_sum_teichmuller_iterateFrobeniusEquiv_coeff (p := l) x 0
  have hI : (Finset.Iic 0 : Finset ℕ) = {0} := by ext i; simp
  rw [hI, Finset.sum_singleton] at h0
  rw [WittVector.constantCoeff_apply] at h
  simpa [h] using h0

/- English proof (translation)
Rewrite using `[map_mul, map_natCast, CharP.cast_eq_zero, zero_mul]`.
-/
theorem constantCoeff_natCast_mul (x : Per.Ainf l) :
    WittVector.constantCoeff ((l : Per.Ainf l) * x) = 0 := by
  rw [map_mul, map_natCast, CharP.cast_eq_zero, zero_mul]

/- English proof (translation)
Proceed by induction on `n with`. Consider the case `zero => simp`. Consider the case `succ n ih`. Rewrite using `[Function.iterate_succ_apply', ih]`. Rewrite using `[GlobalTheory.RingBasics.φA_apply, WittVector.frobenius_eq_map_frobenius, WittVector.map_teichmuller, frobenius_def, ← pow_mul, ← pow_succ]`.
-/
theorem iterate_tm (n : ℕ) (y : Per.Fl l) :
    (⇑(Per.φA l))^[n] (Per.tm y) = Per.tm (y ^ (l ^ n)) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply', ih]
    rw [GlobalTheory.RingBasics.φA_apply, WittVector.frobenius_eq_map_frobenius, WittVector.map_teichmuller,
      frobenius_def, ← pow_mul, ← pow_succ]

/- English proof (translation)
Rewrite using `[SModEq.sub_mem, smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow, Ideal.mem_span_singleton]`.
-/
theorem smod_iff (m : ℕ) (x y : Per.Ainf l) :
    x ≡ y [SMOD ((Ideal.span {(l : Per.Ainf l)}) ^ m • ⊤ : Submodule (Per.Ainf l) (Per.Ainf l))] ↔
      (l : Per.Ainf l) ^ m ∣ x - y := by
  rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow, Ideal.mem_span_singleton]

/- English proof (translation)
Use `set e' := (frobeniusEquiv (Per.Fl l) l).symm e with he'`. Establish `hxi : WittVector.constantCoeff (GlobalTheory.MemLoc.xi e) = ∑ i ∈ Finset.range l, e' ^ i`. Simplify using `[GlobalTheory.MemLoc.xi, map_sum, map_pow, WittVector.constantCoeff_apply, WittVector.teichmuller_coeff_zero, he']`. Establish `hpow : e' ^ l = e`. Use `(frobeniusEquiv (Per.Fl l) l).apply_symm_apply e` as an intermediate fact.

Rewrite `this` using `[frobeniusEquiv_apply, ← he']`. Then use the resulting hypothesis. Introduce `h0`. Rewrite `h0` using `[hxi]`. Establish `h1` using `geom_sum_mul e' l`. Rewrite `h1` using `[h0, zero_mul, hpow]`.

Establish `he1 : e = 1` using `(sub_eq_zero.1 h1.symm)`. Apply `he.2` to reduce the goal to its premises. Rewrite using `[he1, map_one]`. Simplify using the standard rewrite rules.
-/
theorem xi_bar_ne_zero (e : Per.Fl l) (he : GlobalTheory.MemLoc.IsEps e) :
    WittVector.constantCoeff (GlobalTheory.MemLoc.xi e) ≠ 0 := by
  set e' := (frobeniusEquiv (Per.Fl l) l).symm e with he'
  have hxi : WittVector.constantCoeff (GlobalTheory.MemLoc.xi e) = ∑ i ∈ Finset.range l, e' ^ i := by
    simp [GlobalTheory.MemLoc.xi, map_sum, map_pow, WittVector.constantCoeff_apply,
      WittVector.teichmuller_coeff_zero, he']
  have hpow : e' ^ l = e := by
    have := (frobeniusEquiv (Per.Fl l) l).apply_symm_apply e
    rwa [frobeniusEquiv_apply, ← he'] at this
  intro h0
  rw [hxi] at h0
  have h1 := geom_sum_mul e' l
  rw [h0, zero_mul, hpow] at h1
  have he1 : e = 1 := (sub_eq_zero.1 h1.symm)
  apply he.2
  rw [he1, map_one]
  simp

end GlobalTheory.PeriodSol

namespace GlobalTheory.PeriodSol
open Polynomial

variable {l : ℕ} [Fact l.Prime]

/- English proof (translation)
Establish `hq : 1 < l ^ n` using `Nat.one_lt_pow hn.ne' (Fact.out : l.Prime).one_lt`. Use `set a := WittVector.constantCoeff (GlobalTheory.MemLoc.xi e)`. Use `set b := WittVector.constantCoeff c`. Establish `hdeg : (C b - C a * X : (Per.Fl l)[X]).degree < ((l ^ n : ℕ) : WithBot ℕ)`. Establish `h1 : (C b - C a * X : (Per.Fl l)[X]).degree ≤ 1` using `by compute_degree`.

Conclude with `lt_of_le_of_lt h1 (by exact_mod_cast hq)`. Establish `hmon : (X ^ (l ^ n) + (C b - C a * X) : (Per.Fl l)[X]).Monic` using `monic_X_pow_add hdeg`. Establish `hnd : (X ^ (l ^ n) + (C b - C a * X) : (Per.Fl l)[X]).natDegree ≠ 0`. Rewrite using `[natDegree_add_eq_left_of_degree_lt (by rwa [degree_X_pow]), natDegree_X_pow]`. Use linear arithmetic over natural numbers and integers.

Take `⟨y, hy⟩` from `GlobalTheory.TiltAlgClosed.exists_root_preTilt ℂ_[l] hmon hnd`. Use `⟨y, dvd_of_constantCoeff _ ?_⟩` and prove the remaining obligations. Rewrite using `[iterate_tm]`. Simplify using `only [eval_add, eval_sub, eval_pow, eval_X, eval_C, eval_mul] at hy`. Rewrite using `[map_add, map_sub, map_mul, WittVector.constantCoeff_apply (x := Per.tm _), WittVector.constantCoeff_apply (x := Per.tm _), WittVector.teichmuller_coeff_zero, WittVector.teichmuller_coeff_zero]`.

Rewrite using `[← hy]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem exists_step (e : Per.Fl l) (he : GlobalTheory.MemLoc.IsEps e) (n : ℕ) (hn : 0 < n) (c : Per.Ainf l) :
    ∃ y : Per.Fl l, (l : Per.Ainf l) ∣
      c + ((⇑(Per.φA l))^[n] (Per.tm y) - GlobalTheory.MemLoc.xi e * Per.tm y) := by
  have hq : 1 < l ^ n := Nat.one_lt_pow hn.ne' (Fact.out : l.Prime).one_lt
  set a := WittVector.constantCoeff (GlobalTheory.MemLoc.xi e)
  set b := WittVector.constantCoeff c
  have hdeg : (C b - C a * X : (Per.Fl l)[X]).degree < ((l ^ n : ℕ) : WithBot ℕ) := by
    have h1 : (C b - C a * X : (Per.Fl l)[X]).degree ≤ 1 := by compute_degree
    exact lt_of_le_of_lt h1 (by exact_mod_cast hq)
  have hmon : (X ^ (l ^ n) + (C b - C a * X) : (Per.Fl l)[X]).Monic := monic_X_pow_add hdeg
  have hnd : (X ^ (l ^ n) + (C b - C a * X) : (Per.Fl l)[X]).natDegree ≠ 0 := by
    rw [natDegree_add_eq_left_of_degree_lt (by rwa [degree_X_pow]), natDegree_X_pow]
    omega
  obtain ⟨y, hy⟩ := GlobalTheory.TiltAlgClosed.exists_root_preTilt ℂ_[l] hmon hnd
  refine ⟨y, dvd_of_constantCoeff _ ?_⟩
  rw [iterate_tm]
  simp only [eval_add, eval_sub, eval_pow, eval_X, eval_C, eval_mul] at hy
  rw [map_add, map_sub, map_mul, WittVector.constantCoeff_apply (x := Per.tm _),
    WittVector.constantCoeff_apply (x := Per.tm _), WittVector.teichmuller_coeff_zero,
    WittVector.teichmuller_coeff_zero]
  rw [← hy]
  ring

/- English proof (translation)
Establish `hq : 1 < l ^ n` using `Nat.one_lt_pow hn.ne' (Fact.out : l.Prime).one_lt`. Use `set a := WittVector.constantCoeff (GlobalTheory.MemLoc.xi e)`. Establish `hq1 : l ^ n - 1 ≠ 0` using `by omega`. Establish `hmon : (X ^ (l ^ n - 1) - C a : (Per.Fl l)[X]).Monic` using `monic_X_pow_sub_C a hq1`. Establish `hnd : (X ^ (l ^ n - 1) - C a : (Per.Fl l)[X]).natDegree ≠ 0`.

Rewrite using `[natDegree_X_pow_sub_C]`. Conclude with `hq1`. Take `⟨y, hy⟩` from `GlobalTheory.TiltAlgClosed.exists_root_preTilt ℂ_[l] hmon hnd`. Simplify using `only [eval_sub, eval_pow, eval_X, eval_C, sub_eq_zero] at hy`. Use `⟨y, ?_, ?_⟩` and prove the remaining obligations.

Introduce and unpack `rfl`. Rewrite `hy` using `[zero_pow hq1]`. Conclude with `xi_bar_ne_zero e he hy.symm`. Rewrite using `[← hy, ← pow_succ, Nat.sub_add_cancel hq.le]`.
-/
theorem exists_start (e : Per.Fl l) (he : GlobalTheory.MemLoc.IsEps e) (n : ℕ) (hn : 0 < n) :
    ∃ w₀ : Per.Fl l, w₀ ≠ 0 ∧ w₀ ^ (l ^ n) = WittVector.constantCoeff (GlobalTheory.MemLoc.xi e) * w₀ := by
  have hq : 1 < l ^ n := Nat.one_lt_pow hn.ne' (Fact.out : l.Prime).one_lt
  set a := WittVector.constantCoeff (GlobalTheory.MemLoc.xi e)
  have hq1 : l ^ n - 1 ≠ 0 := by omega
  have hmon : (X ^ (l ^ n - 1) - C a : (Per.Fl l)[X]).Monic := monic_X_pow_sub_C a hq1
  have hnd : (X ^ (l ^ n - 1) - C a : (Per.Fl l)[X]).natDegree ≠ 0 := by
    rw [natDegree_X_pow_sub_C]; exact hq1
  obtain ⟨y, hy⟩ := GlobalTheory.TiltAlgClosed.exists_root_preTilt ℂ_[l] hmon hnd
  simp only [eval_sub, eval_pow, eval_X, eval_C, sub_eq_zero] at hy
  refine ⟨y, ?_, ?_⟩
  · rintro rfl
    rw [zero_pow hq1] at hy
    exact xi_bar_ne_zero e he hy.symm
  · rw [← hy, ← pow_succ, Nat.sub_add_cancel hq.le]

/- English proof (translation)
Introduce `l _ e he n hn`. Use `set ξ := GlobalTheory.MemLoc.xi e`. Set `Φ : Per.Ainf l →+* Per.Ainf l` to `Per.φA l ^ n`. Establish `hΦ : ∀ x, (⇑(Per.φA l))^[n] x = Φ x` using `fun x => by simp [Φ, RingHom.coe_pow]`. Set `F : Per.Ainf l → Per.Ainf l` to `fun w => Φ w - ξ * w`.

Establish `F_sub : ∀ a b, F (a - b) = F a - F b` using `fun a b => by simp only [F, map_sub]; ring`. Establish `F_lin : ∀ (m : ℕ) a b, F (a + (l : Per.Ainf l) ^ m * b) = F a + (l : Per.Ainf l) ^ m * F b` using `fun m a b => by simp only [F, map_add, map_mul, map_pow, map_natCast]; ring`. Establish `step : ∀ (k : ℕ) (w : Per.Ainf l), ∃ w' : Per.Ainf l, (l : Per.Ainf l) ^ (k + 1) ∣ F w → (l : Per.Ainf l) ^ (k + 2) ∣ F w' ∧ (l : Per.Ainf l) ^ (k + 1) ∣ w' - w`. Introduce `k w`. Distinguish the cases in `hw : (l : Per.Ainf l) ^ (k + 1) ∣ F w`.

Take `⟨c, hc⟩` from `hw`. Take `⟨y, d, hd⟩` from `exists_step e he n hn c`. Use `⟨w + (l : Per.Ainf l) ^ (k + 1) * Per.tm y, fun _ => ⟨⟨d, ?_⟩, ⟨Per.tm y, by ring⟩⟩⟩` and prove the remaining obligations. Rewrite using `[F_lin, hc, ← mul_add]`. Establish `: F (Per.tm y) = (⇑(Per.φA l))^[n] (Per.tm y) - ξ * Per.tm y` using `by simp only [F, hΦ]`.

Rewrite using `[this, hd]`. Expand and normalize the polynomial expressions, which then agree. Conclude with `⟨w, fun h => absurd h hw⟩`. Use `choose g hg using step`. Take `⟨w₀, hw₀, hw₀q⟩` from `exists_start e he n hn`.

Set `seq : ℕ → Per.Ainf l` to `fun k => Nat.rec (Per.tm w₀) (fun k w => g k w) k`. Establish `hseq0 : seq 0 = Per.tm w₀` using `rfl`. Establish `hseqS : ∀ k, seq (k + 1) = g k (seq k)` using `fun k => rfl`. Establish `hF0 : (l : Per.Ainf l) ^ (0 + 1) ∣ F (seq 0)`. Rewrite using `[zero_add, pow_one, hseq0]`.

Apply `dvd_of_constantCoeff` to reduce the goal to its premises. Simplify using `only [F, ← hΦ, iterate_tm, map_sub, map_mul, WittVector.constantCoeff_apply (x := Per.tm _), WittVector.teichmuller_coeff_zero, hw₀q]`. Conclude with `sub_self _`. Establish `hF : ∀ k, (l : Per.Ainf l) ^ (k + 1) ∣ F (seq k)`. Introduce `k`.

Proceed by induction on `k with`. Consider the case `zero => exact hF0`. Consider the case `succ k ih => rw [hseqS]`. Conclude with `(hg k (seq k) ih).1`. Establish `hdiff : ∀ k, (l : Per.Ainf l) ^ (k + 1) ∣ seq (k + 1) - seq k` using `fun k => by`.

Rewrite using `[hseqS]`. Conclude with `(hg k (seq k) (hF k)).2`. Establish `hcau : ∀ m d, (l : Per.Ainf l) ^ m ∣ seq m - seq (m + d)`. Introduce `m d`. Proceed by induction on `d with`.

Consider the case `zero => simp`. Consider the case `succ d ih`. Establish `h2 : (l : Per.Ainf l) ^ m ∣ seq (m + d + 1) - seq (m + d)` using `(pow_dvd_pow _ (by omega)).trans (hdiff (m + d))`. Establish `: seq m - seq (m + (d + 1)) = (seq m - seq (m + d)) - (seq (m + d + 1) - seq (m + d))`. Rewrite using `[← add_assoc]`.

Expand and normalize the polynomial expressions, which then agree. Rewrite using `[this]`. Conclude with `dvd_sub ih h2`. Establish `hcomp : IsAdicComplete (Ideal.span {(l : Per.Ainf l)}) (Per.Ainf l)` using `WittVector.isAdicCompleteIdealSpanP`. Take `⟨L, hL⟩` from `hcomp.toIsPrecomplete.prec (f := seq) (fun {m n} hmn => by`.

Rewrite using `[smod_iff]`. Take `⟨d, rfl⟩` from `Nat.exists_eq_add_of_le hmn`. Conclude with `hcau m d)`. Establish `hL' : ∀ k, (l : Per.Ainf l) ^ k ∣ seq k - L` using `fun k => (smod_iff k _ _).1 (hL k)`. Establish `hFL : F L = 0`.

Use `hcomp.toIsHausdorff.haus (F L) fun k => ?_` and prove the remaining obligations. Rewrite using `[smod_iff, sub_zero]`. Take `⟨c, hc⟩` from `hL' k`. Establish `e1 : L = seq k + (l : Per.Ainf l) ^ k * (-c)` using `by rw [mul_neg, ← hc]; ring`. Rewrite using `[e1, F_lin]`.

Conclude with `dvd_add ((pow_dvd_pow _ (Nat.le_succ k)).trans (hF k)) (dvd_mul_right _ _)`. Establish `hL0 : WittVector.constantCoeff L = w₀`. Take `⟨c, hc⟩` from `hL' 1`. Take `⟨c', hc'⟩` from `hdiff 0`. Establish `e1 : L = Per.tm w₀ + (l : Per.Ainf l) * (c' - c)`.

Rewrite `hc` using `[pow_one]`. Rewrite `hc'` using `[zero_add, pow_one]`. Rewrite using `[mul_sub, ← hc, ← hc', ← hseq0]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e1, map_add, constantCoeff_natCast_mul, add_zero, WittVector.constantCoeff_apply, WittVector.teichmuller_coeff_zero]`.

Use `⟨L, fun h0 => ?_, ?_⟩` and prove the remaining obligations. Use `congrArg WittVector.constantCoeff h0` as an intermediate fact. Rewrite `this` using `[map_mul, map_zero, hL0]`. Conclude with `mul_ne_zero (xi_bar_ne_zero e he) hw₀ this`. Rewrite using `[hΦ]`.

Conclude with `sub_eq_zero.1 hFL`.
-/
theorem period_solution : ∀ (l : ℕ) [Fact l.Prime] (e : Per.Fl l), GlobalTheory.MemLoc.IsEps e →
    ∀ n : ℕ, 0 < n → ∃ w : Per.Ainf l, GlobalTheory.MemLoc.xi e * w ≠ 0 ∧
      (⇑(Per.φA l))^[n] w = GlobalTheory.MemLoc.xi e * w := by
  intro l _ e he n hn
  set ξ := GlobalTheory.MemLoc.xi e
  let Φ : Per.Ainf l →+* Per.Ainf l := Per.φA l ^ n
  have hΦ : ∀ x, (⇑(Per.φA l))^[n] x = Φ x := fun x => by simp [Φ, RingHom.coe_pow]
  let F : Per.Ainf l → Per.Ainf l := fun w => Φ w - ξ * w
  have F_sub : ∀ a b, F (a - b) = F a - F b := fun a b => by simp only [F, map_sub]; ring
  have F_lin : ∀ (m : ℕ) a b, F (a + (l : Per.Ainf l) ^ m * b) = F a + (l : Per.Ainf l) ^ m * F b :=
    fun m a b => by simp only [F, map_add, map_mul, map_pow, map_natCast]; ring
  have step : ∀ (k : ℕ) (w : Per.Ainf l), ∃ w' : Per.Ainf l,
      (l : Per.Ainf l) ^ (k + 1) ∣ F w →
        (l : Per.Ainf l) ^ (k + 2) ∣ F w' ∧ (l : Per.Ainf l) ^ (k + 1) ∣ w' - w := by
    intro k w
    by_cases hw : (l : Per.Ainf l) ^ (k + 1) ∣ F w
    · obtain ⟨c, hc⟩ := hw
      obtain ⟨y, d, hd⟩ := exists_step e he n hn c
      refine ⟨w + (l : Per.Ainf l) ^ (k + 1) * Per.tm y, fun _ => ⟨⟨d, ?_⟩, ⟨Per.tm y, by ring⟩⟩⟩
      rw [F_lin, hc, ← mul_add]
      have : F (Per.tm y) = (⇑(Per.φA l))^[n] (Per.tm y) - ξ * Per.tm y := by simp only [F, hΦ]
      rw [this, hd]; ring
    · exact ⟨w, fun h => absurd h hw⟩
  choose g hg using step
  obtain ⟨w₀, hw₀, hw₀q⟩ := exists_start e he n hn
  let seq : ℕ → Per.Ainf l := fun k => Nat.rec (Per.tm w₀) (fun k w => g k w) k
  have hseq0 : seq 0 = Per.tm w₀ := rfl
  have hseqS : ∀ k, seq (k + 1) = g k (seq k) := fun k => rfl
  have hF0 : (l : Per.Ainf l) ^ (0 + 1) ∣ F (seq 0) := by
    rw [zero_add, pow_one, hseq0]
    apply dvd_of_constantCoeff
    simp only [F, ← hΦ, iterate_tm, map_sub, map_mul, WittVector.constantCoeff_apply (x := Per.tm _),
      WittVector.teichmuller_coeff_zero, hw₀q]
    exact sub_self _
  have hF : ∀ k, (l : Per.Ainf l) ^ (k + 1) ∣ F (seq k) := by
    intro k
    induction k with
    | zero => exact hF0
    | succ k ih => rw [hseqS]; exact (hg k (seq k) ih).1
  have hdiff : ∀ k, (l : Per.Ainf l) ^ (k + 1) ∣ seq (k + 1) - seq k := fun k => by
    rw [hseqS]; exact (hg k (seq k) (hF k)).2
  have hcau : ∀ m d, (l : Per.Ainf l) ^ m ∣ seq m - seq (m + d) := by
    intro m d
    induction d with
    | zero => simp
    | succ d ih =>
      have h2 : (l : Per.Ainf l) ^ m ∣ seq (m + d + 1) - seq (m + d) :=
        (pow_dvd_pow _ (by omega)).trans (hdiff (m + d))
      have : seq m - seq (m + (d + 1)) = (seq m - seq (m + d)) - (seq (m + d + 1) - seq (m + d)) := by
        rw [← add_assoc]; ring
      rw [this]; exact dvd_sub ih h2
  have hcomp : IsAdicComplete (Ideal.span {(l : Per.Ainf l)}) (Per.Ainf l) :=
    WittVector.isAdicCompleteIdealSpanP
  obtain ⟨L, hL⟩ := hcomp.toIsPrecomplete.prec (f := seq) (fun {m n} hmn => by
    rw [smod_iff]
    obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hmn
    exact hcau m d)
  have hL' : ∀ k, (l : Per.Ainf l) ^ k ∣ seq k - L := fun k => (smod_iff k _ _).1 (hL k)
  have hFL : F L = 0 := by
    refine hcomp.toIsHausdorff.haus (F L) fun k => ?_
    rw [smod_iff, sub_zero]
    obtain ⟨c, hc⟩ := hL' k
    have e1 : L = seq k + (l : Per.Ainf l) ^ k * (-c) := by rw [mul_neg, ← hc]; ring
    rw [e1, F_lin]
    exact dvd_add ((pow_dvd_pow _ (Nat.le_succ k)).trans (hF k)) (dvd_mul_right _ _)
  have hL0 : WittVector.constantCoeff L = w₀ := by
    obtain ⟨c, hc⟩ := hL' 1
    obtain ⟨c', hc'⟩ := hdiff 0
    have e1 : L = Per.tm w₀ + (l : Per.Ainf l) * (c' - c) := by
      rw [pow_one] at hc; rw [zero_add, pow_one] at hc'
      rw [mul_sub, ← hc, ← hc', ← hseq0]; ring
    rw [e1, map_add, constantCoeff_natCast_mul, add_zero, WittVector.constantCoeff_apply,
      WittVector.teichmuller_coeff_zero]
  refine ⟨L, fun h0 => ?_, ?_⟩
  · have := congrArg WittVector.constantCoeff h0
    rw [map_mul, map_zero, hL0] at this
    exact mul_ne_zero (xi_bar_ne_zero e he) hw₀ this
  · rw [hΦ]; exact sub_eq_zero.1 hFL

end GlobalTheory.PeriodSol

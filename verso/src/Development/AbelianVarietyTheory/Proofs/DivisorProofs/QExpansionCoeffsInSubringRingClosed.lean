import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HasQIff

open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam

namespace GlobalTheory.QFam.QAllSubring

variable {R : Subring ℂ} {N : ℕ}

open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators in
variable {R : Subring ℂ} {N : ℕ} in
/- English proof (translation)
Use `⟨fun n => if n = 0 then c else 0, ?_, fun n => ?_⟩` and prove the remaining obligations. Rewrite using `[_root_.GlobalTheory.QFam.hasQ_iff]`. Introduce `τ`. Establish `h` using `hasSum_single (f := fun n : ℕ => (if n = 0 then c else 0) * Complex.exp (2 * ↑Real.pi * Complex.I * ↑τ / ↑N) ^ n) 0 (fun m hm => by simp [hm])`. Simplify using `using h`.

Use `show (if n = 0 then c else 0) ∈ R split_ifs`. Conclude with `hc`. Conclude with `R.zero_mem`.
-/
theorem _root_.GlobalTheory.QFam.QAllSubring.const {c : ℂ} (hc : c ∈ R) :
    _root_.GlobalTheory.QFam.QAll (· ∈ R) N fun _ => c := by
  refine ⟨fun n => if n = 0 then c else 0, ?_, fun n => ?_⟩
  · rw [_root_.GlobalTheory.QFam.hasQ_iff]
    intro τ
    have h := hasSum_single (f := fun n : ℕ =>
      (if n = 0 then c else 0) * Complex.exp (2 * ↑Real.pi * Complex.I * ↑τ / ↑N) ^ n) 0
      (fun m hm => by simp [hm])
    simpa using h
  · show (if n = 0 then c else 0) ∈ R
    split_ifs
    · exact hc
    · exact R.zero_mem

open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators in
variable {R : Subring ℂ} {N : ℕ} in
/- English proof (translation)
Take `⟨a, ha, haR⟩` from `hf`. Take `⟨b, hb, hbR⟩` from `hg`. Use `⟨fun n => a n + b n, ?_, fun n => R.add_mem (haR n) (hbR n)⟩` and prove the remaining obligations. Rewrite `ha`, `hb`, the goal using `[_root_.GlobalTheory.QFam.hasQ_iff]`. Introduce `τ`.

Simplify `(ha τ).add (hb τ)` using `[add_mul]`.
-/
theorem _root_.GlobalTheory.QFam.QAllSubring.add {f g : ℍ → ℂ} (hf : _root_.GlobalTheory.QFam.QAll (· ∈ R) N f)
    (hg : _root_.GlobalTheory.QFam.QAll (· ∈ R) N g) :
    _root_.GlobalTheory.QFam.QAll (· ∈ R) N fun τ => f τ + g τ := by
  obtain ⟨a, ha, haR⟩ := hf
  obtain ⟨b, hb, hbR⟩ := hg
  refine ⟨fun n => a n + b n, ?_, fun n => R.add_mem (haR n) (hbR n)⟩
  rw [_root_.GlobalTheory.QFam.hasQ_iff] at ha hb ⊢
  intro τ
  simpa [add_mul] using (ha τ).add (hb τ)

open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators in
variable {R : Subring ℂ} {N : ℕ} in
/- English proof (translation)
Take `⟨a, ha, haR⟩` from `hf`. Take `⟨b, hb, hbR⟩` from `hg`. Use `⟨fun n => a n - b n, ?_, fun n => R.sub_mem (haR n) (hbR n)⟩` and prove the remaining obligations. Rewrite `ha`, `hb`, the goal using `[_root_.GlobalTheory.QFam.hasQ_iff]`. Introduce `τ`.

Simplify `(ha τ).sub (hb τ)` using `[sub_mul]`.
-/
theorem _root_.GlobalTheory.QFam.QAllSubring.sub {f g : ℍ → ℂ} (hf : _root_.GlobalTheory.QFam.QAll (· ∈ R) N f)
    (hg : _root_.GlobalTheory.QFam.QAll (· ∈ R) N g) :
    _root_.GlobalTheory.QFam.QAll (· ∈ R) N fun τ => f τ - g τ := by
  obtain ⟨a, ha, haR⟩ := hf
  obtain ⟨b, hb, hbR⟩ := hg
  refine ⟨fun n => a n - b n, ?_, fun n => R.sub_mem (haR n) (hbR n)⟩
  rw [_root_.GlobalTheory.QFam.hasQ_iff] at ha hb ⊢
  intro τ
  simpa [sub_mul] using (ha τ).sub (hb τ)

open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators in
variable {R : Subring ℂ} {N : ℕ} in
/- English proof (translation)
Take `⟨a, ha, haR⟩` from `hf`. Take `⟨b, hb, hbR⟩` from `hg`. Use `⟨fun n => ∑ kl ∈ Finset.HasAntidiagonal.antidiagonal n, a kl.1 * b kl.2, ?_, fun n => R.sum_mem fun kl _ => R.mul_mem (haR kl.1) (hbR kl.2)⟩` and prove the remaining obligations. Rewrite `ha`, `hb`, the goal using `[_root_.GlobalTheory.QFam.hasQ_iff]`. Introduce `τ`.

Use `set q := Complex.exp (2 * ↑Real.pi * Complex.I * ↑τ / ↑N)`. Establish `hsa : Summable fun n => ‖a n * q ^ n‖` using `summable_norm_iff.mpr (ha τ).summable`. Establish `hsb : Summable fun n => ‖b n * q ^ n‖` using `summable_norm_iff.mpr (hb τ).summable`. Establish `hterm : ∀ n, ∑ kl ∈ Finset.HasAntidiagonal.antidiagonal n, a kl.1 * q ^ kl.1 * (b kl.2 * q ^ kl.2) = (∑ kl ∈ Finset.HasAntidiagonal.antidiagonal n, a kl.1 * b kl.2) * q ^ n`. Introduce `n`.

Rewrite using `[Finset.sum_mul]`. Use `Finset.sum_congr rfl fun kl hkl => ?_` and prove the remaining obligations. Rewrite using `[← Finset.HasAntidiagonal.mem_antidiagonal.mp hkl, pow_add]`. Expand and normalize the polynomial expressions, which then agree. Establish `hs` using `summable_norm_sum_mul_antidiagonal_of_summable_norm hsa hsb`.

Establish `heq` using `tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_summable_norm hsa hsb`. Rewrite `heq` using `[(ha τ).tsum_eq, (hb τ).tsum_eq]`. Rewrite using `[heq]`. Simplify using `only [hterm] at hs ⊢`. Conclude with `(summable_norm_iff.mp hs).hasSum`.
-/
theorem _root_.GlobalTheory.QFam.QAllSubring.mul {f g : ℍ → ℂ} (hf : _root_.GlobalTheory.QFam.QAll (· ∈ R) N f)
    (hg : _root_.GlobalTheory.QFam.QAll (· ∈ R) N g) :
    _root_.GlobalTheory.QFam.QAll (· ∈ R) N fun τ => f τ * g τ := by
  obtain ⟨a, ha, haR⟩ := hf
  obtain ⟨b, hb, hbR⟩ := hg
  refine ⟨fun n => ∑ kl ∈ Finset.HasAntidiagonal.antidiagonal n, a kl.1 * b kl.2, ?_,
    fun n => R.sum_mem fun kl _ => R.mul_mem (haR kl.1) (hbR kl.2)⟩
  rw [_root_.GlobalTheory.QFam.hasQ_iff] at ha hb ⊢
  intro τ
  set q := Complex.exp (2 * ↑Real.pi * Complex.I * ↑τ / ↑N)
  have hsa : Summable fun n => ‖a n * q ^ n‖ := summable_norm_iff.mpr (ha τ).summable
  have hsb : Summable fun n => ‖b n * q ^ n‖ := summable_norm_iff.mpr (hb τ).summable
  have hterm : ∀ n, ∑ kl ∈ Finset.HasAntidiagonal.antidiagonal n,
      a kl.1 * q ^ kl.1 * (b kl.2 * q ^ kl.2) =
      (∑ kl ∈ Finset.HasAntidiagonal.antidiagonal n, a kl.1 * b kl.2) * q ^ n := by
    intro n
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun kl hkl => ?_
    rw [← Finset.HasAntidiagonal.mem_antidiagonal.mp hkl, pow_add]
    ring
  have hs := summable_norm_sum_mul_antidiagonal_of_summable_norm hsa hsb
  have heq := tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_summable_norm hsa hsb
  rw [(ha τ).tsum_eq, (hb τ).tsum_eq] at heq
  rw [heq]
  simp only [hterm] at hs ⊢
  exact (summable_norm_iff.mp hs).hasSum

open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators in
variable {R : Subring ℂ} {N : ℕ} in
/- English proof (translation)
Proceed by induction on `k with`. Consider the case `zero => simpa using _root_.GlobalTheory.QFam.QAllSubring.const (N := N) R.one_mem`. Consider the case `succ k ih => simpa [pow_succ] using _root_.GlobalTheory.QFam.QAllSubring.mul ih hf`.
-/
theorem _root_.GlobalTheory.QFam.QAllSubring.pow {f : ℍ → ℂ} (k : ℕ)
    (hf : _root_.GlobalTheory.QFam.QAll (· ∈ R) N f) :
    _root_.GlobalTheory.QFam.QAll (· ∈ R) N fun τ => f τ ^ k := by
  induction k with
  | zero => simpa using _root_.GlobalTheory.QFam.QAllSubring.const (N := N) R.one_mem
  | succ k ih => simpa [pow_succ] using _root_.GlobalTheory.QFam.QAllSubring.mul ih hf

open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators in
variable {R : Subring ℂ} {N : ℕ} in
/- English proof (translation)
Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty => simpa using _root_.GlobalTheory.QFam.QAllSubring.const (N := N) R.zero_mem`. Consider the case `insert i s hi ih`. Simplify using `only [Finset.sum_insert hi]`. Conclude with `_root_.GlobalTheory.QFam.QAllSubring.add (hf i (Finset.mem_insert_self i s)) (ih fun k hk => hf k (Finset.mem_insert_of_mem hk))`.
-/
theorem _root_.GlobalTheory.QFam.QAllSubring.sum {κ : Type} (s : Finset κ) {f : κ → ℍ → ℂ}
    (hf : ∀ k ∈ s, _root_.GlobalTheory.QFam.QAll (· ∈ R) N (f k)) :
    _root_.GlobalTheory.QFam.QAll (· ∈ R) N fun τ => ∑ k ∈ s, f k τ := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using _root_.GlobalTheory.QFam.QAllSubring.const (N := N) R.zero_mem
  | insert i s hi ih =>
    simp only [Finset.sum_insert hi]
    exact _root_.GlobalTheory.QFam.QAllSubring.add (hf i (Finset.mem_insert_self i s))
      (ih fun k hk => hf k (Finset.mem_insert_of_mem hk))

open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators in
variable {R : Subring ℂ} {N : ℕ} in
/- English proof (translation)
Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty => simpa using _root_.GlobalTheory.QFam.QAllSubring.const (N := N) R.one_mem`. Consider the case `insert i s hi ih`. Simplify using `only [Finset.prod_insert hi]`. Conclude with `_root_.GlobalTheory.QFam.QAllSubring.mul (hf i (Finset.mem_insert_self i s)) (ih fun k hk => hf k (Finset.mem_insert_of_mem hk))`.
-/
theorem _root_.GlobalTheory.QFam.QAllSubring.prod {κ : Type} (s : Finset κ) {f : κ → ℍ → ℂ}
    (hf : ∀ k ∈ s, _root_.GlobalTheory.QFam.QAll (· ∈ R) N (f k)) :
    _root_.GlobalTheory.QFam.QAll (· ∈ R) N fun τ => ∏ k ∈ s, f k τ := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using _root_.GlobalTheory.QFam.QAllSubring.const (N := N) R.one_mem
  | insert i s hi ih =>
    simp only [Finset.prod_insert hi]
    exact _root_.GlobalTheory.QFam.QAllSubring.mul (hf i (Finset.mem_insert_self i s))
      (ih fun k hk => hf k (Finset.mem_insert_of_mem hk))

open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators in
variable {R : Subring ℂ} {N : ℕ} in

/- English proof (translation)
Introduce `R N _`. Conclude with `⟨fun c hc => _root_.GlobalTheory.QFam.QAllSubring.const hc, fun f g hf hg => _root_.GlobalTheory.QFam.QAllSubring.add hf hg, fun f g hf hg => _root_.GlobalTheory.QFam.QAllSubring.sub hf hg, fun f g hf hg => _root_.GlobalTheory.QFam.QAllSubring.mul hf hg, fun f k hf => _root_.Glob …`.
-/
theorem _root_.GlobalTheory.QFam.QAllSubring.ring_closed : ∀ (R : Subring ℂ) (N : ℕ), 0 < N →
    (∀ c ∈ R, _root_.GlobalTheory.QFam.QAll (· ∈ R) N fun _ => c) ∧
    (∀ f g, _root_.GlobalTheory.QFam.QAll (· ∈ R) N f → _root_.GlobalTheory.QFam.QAll (· ∈ R) N g →
      _root_.GlobalTheory.QFam.QAll (· ∈ R) N fun τ => f τ + g τ) ∧
    (∀ f g, _root_.GlobalTheory.QFam.QAll (· ∈ R) N f → _root_.GlobalTheory.QFam.QAll (· ∈ R) N g →
      _root_.GlobalTheory.QFam.QAll (· ∈ R) N fun τ => f τ - g τ) ∧
    (∀ f g, _root_.GlobalTheory.QFam.QAll (· ∈ R) N f → _root_.GlobalTheory.QFam.QAll (· ∈ R) N g →
      _root_.GlobalTheory.QFam.QAll (· ∈ R) N fun τ => f τ * g τ) ∧
    (∀ f (k : ℕ), _root_.GlobalTheory.QFam.QAll (· ∈ R) N f →
      _root_.GlobalTheory.QFam.QAll (· ∈ R) N fun τ => f τ ^ k) ∧
    (∀ (κ : Type) (s : Finset κ) (f : κ → ℍ → ℂ),
      (∀ k ∈ s, _root_.GlobalTheory.QFam.QAll (· ∈ R) N (f k)) →
      (_root_.GlobalTheory.QFam.QAll (· ∈ R) N fun τ => ∑ k ∈ s, f k τ) ∧
        _root_.GlobalTheory.QFam.QAll (· ∈ R) N fun τ => ∏ k ∈ s, f k τ) := by
  intro R N _
  exact ⟨fun c hc => _root_.GlobalTheory.QFam.QAllSubring.const hc,
    fun f g hf hg => _root_.GlobalTheory.QFam.QAllSubring.add hf hg,
    fun f g hf hg => _root_.GlobalTheory.QFam.QAllSubring.sub hf hg,
    fun f g hf hg => _root_.GlobalTheory.QFam.QAllSubring.mul hf hg,
    fun f k hf => _root_.GlobalTheory.QFam.QAllSubring.pow k hf,
    fun κ s f hf => ⟨_root_.GlobalTheory.QFam.QAllSubring.sum s hf,
      _root_.GlobalTheory.QFam.QAllSubring.prod s hf⟩⟩

end GlobalTheory.QFam.QAllSubring

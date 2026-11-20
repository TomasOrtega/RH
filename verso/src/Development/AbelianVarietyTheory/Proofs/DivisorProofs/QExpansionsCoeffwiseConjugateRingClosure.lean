import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HasQIff
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasQExpansionOfLevelLinearOperations
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasQExpansionOfLevelMulOfPosLevel

open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators

namespace GlobalTheory.QFam

variable {g : ℂ ≃+* ℂ} {N : ℕ}

/- English proof (translation)
Use `⟨fun n => if n = 0 then c else 0, HasQ.const N c, ?_⟩` and prove the remaining obligations. Establish `e : (fun n : ℕ => g (if n = 0 then c else 0)) = fun n => if n = 0 then g c else 0`. Use function extensionality and compare the values at `n`. Apply the tactic sequence `split_ifs <;> simp`. Rewrite using `[e]`.

Conclude with `HasQ.const N (g c)`.
-/
theorem QConj.const (g : ℂ ≃+* ℂ) (N : ℕ) (c : ℂ) : QConj g N (fun _ => c) fun _ => g c := by
  refine ⟨fun n => if n = 0 then c else 0, HasQ.const N c, ?_⟩
  have e : (fun n : ℕ => g (if n = 0 then c else 0)) = fun n => if n = 0 then g c else 0 := by
    funext n
    split_ifs <;> simp
  rw [e]
  exact HasQ.const N (g c)

/- English proof (translation)
Take `⟨a, ha, ha'⟩` from `hf`. Take `⟨b, hb, hb'⟩` from `hh`. Use `⟨fun n => a n + b n, ha.add hb, ?_⟩` and prove the remaining obligations. Simplify `ha'.add hb'` using `only [map_add]`.
-/
theorem QConj.add {f f' h h' : ℍ → ℂ} (hf : QConj g N f f') (hh : QConj g N h h') :
    QConj g N (fun τ => f τ + h τ) fun τ => f' τ + h' τ := by
  obtain ⟨a, ha, ha'⟩ := hf
  obtain ⟨b, hb, hb'⟩ := hh
  refine ⟨fun n => a n + b n, ha.add hb, ?_⟩
  simpa only [map_add] using ha'.add hb'

/- English proof (translation)
Take `⟨a, ha, ha'⟩` from `hf`. Take `⟨b, hb, hb'⟩` from `hh`. Use `⟨fun n => a n - b n, ha.sub hb, ?_⟩` and prove the remaining obligations. Simplify `ha'.sub hb'` using `only [map_sub]`.
-/
theorem QConj.sub {f f' h h' : ℍ → ℂ} (hf : QConj g N f f') (hh : QConj g N h h') :
    QConj g N (fun τ => f τ - h τ) fun τ => f' τ - h' τ := by
  obtain ⟨a, ha, ha'⟩ := hf
  obtain ⟨b, hb, hb'⟩ := hh
  refine ⟨fun n => a n - b n, ha.sub hb, ?_⟩
  simpa only [map_sub] using ha'.sub hb'

/- English proof (translation)
Simplify using `only [conv, map_sum, map_mul]`.
-/
theorem map_conv (g : ℂ ≃+* ℂ) (a b : ℕ → ℂ) (n : ℕ) :
    g (conv a b n) = conv (fun n => g (a n)) (fun n => g (b n)) n := by
  simp only [conv, map_sum, map_mul]

/- English proof (translation)
Take `⟨a, ha, ha'⟩` from `hf`. Take `⟨b, hb, hb'⟩` from `hh`. Use `⟨conv a b, ha.mul_conv hb, ?_⟩` and prove the remaining obligations. Establish `e : (fun n => g (conv a b n)) = conv (fun n => g (a n)) (fun n => g (b n))`. Use function extensionality and compare the values at `(map_conv g a b)`.

Rewrite using `[e]`. Conclude with `ha'.mul_conv hb'`.
-/
theorem QConj.mul (hN : 0 < N) {f f' h h' : ℍ → ℂ} (hf : QConj g N f f') (hh : QConj g N h h') :
    QConj g N (fun τ => f τ * h τ) fun τ => f' τ * h' τ := by
  obtain ⟨a, ha, ha'⟩ := hf
  obtain ⟨b, hb, hb'⟩ := hh
  refine ⟨conv a b, ha.mul_conv hb, ?_⟩
  have e : (fun n => g (conv a b n)) = conv (fun n => g (a n)) (fun n => g (b n)) :=
    funext (map_conv g a b)
  rw [e]
  exact ha'.mul_conv hb'

/- English proof (translation)
Proceed by induction on `k with`. Consider the case `zero`. Simplify using `only [pow_zero]`. Simplify using `using QConj.const g N 1`. Consider the case `succ k ih`.

Simplify using `only [pow_succ]`. Conclude with `QConj.mul hN ih hf`.
-/
theorem QConj.pow (hN : 0 < N) {f f' : ℍ → ℂ} (k : ℕ) (hf : QConj g N f f') :
    QConj g N (fun τ => f τ ^ k) fun τ => f' τ ^ k := by
  induction k with
  | zero =>
    simp only [pow_zero]
    simpa using QConj.const g N 1
  | succ k ih =>
    simp only [pow_succ]
    exact QConj.mul hN ih hf

/- English proof (translation)
Use `revert h`. Use `Finset.induction_on s ?_ ?_` and prove the remaining obligations. Introduce `_`. Simplify using `only [Finset.sum_empty]`. Simplify using `using QConj.const g N 0`.

Introduce `j s hj ih h`. Simplify using `only [Finset.sum_insert hj]`. Conclude with `QConj.add (h j (Finset.mem_insert_self j s)) (ih fun k hk => h k (Finset.mem_insert_of_mem hk))`.
-/
theorem QConj.sum {κ : Type} (s : Finset κ) {f f' : κ → ℍ → ℂ}
    (h : ∀ k ∈ s, QConj g N (f k) (f' k)) :
    QConj g N (fun τ => ∑ k ∈ s, f k τ) fun τ => ∑ k ∈ s, f' k τ := by
  classical
  revert h
  refine Finset.induction_on s ?_ ?_
  · intro _
    simp only [Finset.sum_empty]
    simpa using QConj.const g N 0
  · intro j s hj ih h
    simp only [Finset.sum_insert hj]
    exact QConj.add (h j (Finset.mem_insert_self j s))
      (ih fun k hk => h k (Finset.mem_insert_of_mem hk))

/- English proof (translation)
Use `revert h`. Use `Finset.induction_on s ?_ ?_` and prove the remaining obligations. Introduce `_`. Simplify using `only [Finset.prod_empty]`. Simplify using `using QConj.const g N 1`.

Introduce `j s hj ih h`. Simplify using `only [Finset.prod_insert hj]`. Conclude with `QConj.mul hN (h j (Finset.mem_insert_self j s)) (ih fun k hk => h k (Finset.mem_insert_of_mem hk))`.
-/
theorem QConj.prod (hN : 0 < N) {κ : Type} (s : Finset κ) {f f' : κ → ℍ → ℂ}
    (h : ∀ k ∈ s, QConj g N (f k) (f' k)) :
    QConj g N (fun τ => ∏ k ∈ s, f k τ) fun τ => ∏ k ∈ s, f' k τ := by
  classical
  revert h
  refine Finset.induction_on s ?_ ?_
  · intro _
    simp only [Finset.prod_empty]
    simpa using QConj.const g N 1
  · intro j s hj ih h
    simp only [Finset.prod_insert hj]
    exact QConj.mul hN (h j (Finset.mem_insert_self j s))
      (ih fun k hk => h k (Finset.mem_insert_of_mem hk))

/- English proof (translation)
Introduce `g N hN`. Conclude with `⟨fun c => QConj.const g N c, fun _ _ _ _ hf hh => QConj.add hf hh, fun _ _ _ _ hf hh => QConj.sub hf hh, fun _ _ _ _ hf hh => QConj.mul hN hf hh, fun _ _ k hf => QConj.pow hN k hf, fun _ s _ _ h => ⟨QConj.sum s h, QConj.prod hN s h⟩⟩`.
-/
theorem qConj_ring : ∀ (g : ℂ ≃+* ℂ) (N : ℕ), 0 < N → (∀ c : ℂ, QConj g N (fun _ => c) fun _ => g c) ∧ (∀ f f' h h', QConj g N f f' → QConj g N h h' → QConj g N (fun τ => f τ + h τ) fun τ => f' τ + h' τ) ∧ (∀ f f' h h', QConj g N f f' → QConj g N h h' → QConj g N (fun τ => f τ - h τ) fun τ => f' τ - h' τ) ∧ (∀ f f' h h', QConj g N f f' → QConj g N h h' → QConj g N (fun τ => f τ * h τ) fun τ => f' τ * h' τ) ∧ (∀ f f' (k : ℕ), QConj g N f f' → QConj g N (fun τ => f τ ^ k) fun τ => f' τ ^ k) ∧ (∀ (κ : Type) (s : Finset κ) (f f' : κ → ℍ → ℂ), (∀ k ∈ s, QConj g N (f k) (f' k)) → (QConj g N (fun τ => ∑ k ∈ s, f k τ) fun τ => ∑ k ∈ s, f' k τ) ∧ QConj g N (fun τ => ∏ k ∈ s, f k τ) fun τ => ∏ k ∈ s, f' k τ) := by
  intro g N hN
  exact ⟨fun c => QConj.const g N c,
    fun _ _ _ _ hf hh => QConj.add hf hh,
    fun _ _ _ _ hf hh => QConj.sub hf hh,
    fun _ _ _ _ hf hh => QConj.mul hN hf hh,
    fun _ _ k hf => QConj.pow hN k hf,
    fun _ s _ _ h => ⟨QConj.sum s h, QConj.prod hN s h⟩⟩

end GlobalTheory.QFam

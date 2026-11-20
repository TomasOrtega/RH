import Mathlib
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
import Development.AbelianVarietyTheory.Definitions.Foundations.HTBasis
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsAlgClosedTiltFieldAndValuationRing
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CoeffZeroEqZeroIff
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SubOneBijectiveQuotientOfTopNilpotent

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc GlobalTheory.Decompl
open scoped TensorProduct

namespace GlobalTheory.DecomplMat

variable {R A : Type} [CommRing R] [CommRing A] {ι : A →+* R} {p : ℕ} {t : R}

/- English proof (translation)
Proceed by induction on `n with`. Consider the case `zero => exact ⟨1, 0, by simp⟩`. Consider the case `succ n ih`. Establish `h` using `ih.mul hx`. Rewrite `h` using `[← pow_succ]`.

Conclude with `h`.
-/
theorem near_pow_two {x : R} (hx : Near ι p t 2 x) (n : ℕ) : Near ι p t (2 * n) (x ^ n) := by
  induction n with
  | zero => exact ⟨1, 0, by simp⟩
  | succ n ih =>
    have h := ih.mul hx
    rw [← pow_succ] at h
    exact h

/- English proof (translation)
Take `⟨a, r, rfl⟩` from `hv`. Take `⟨a', ha'⟩` from `hι a`. Rewrite using `[map_add, map_mul, map_mul, map_pow, map_natCast, ha', mul_comm _ (ι a')]`. Conclude with `((near_pow_two ht n).mul_ι a').add (Near.of_mul _ _)`.
-/
theorem near_frob (φ : R →+* R) (hι : ∀ a, ∃ a', φ (ι a) = ι a') (ht : Near ι p t 2 (φ t))
    {n : ℕ} {v : R} (hv : Near ι p t n v) : Near ι p t (2 * n) (φ v) := by
  obtain ⟨a, r, rfl⟩ := hv
  obtain ⟨a', ha'⟩ := hι a
  rw [map_add, map_mul, map_mul, map_pow, map_natCast, ha', mul_comm _ (ι a')]
  exact ((near_pow_two ht n).mul_ι a').add (Near.of_mul _ _)

/- English proof (translation)
Take `⟨a, r, rfl⟩` from `hw`. Take `⟨b, s, h⟩` from `hq`. Use `⟨b * a, t ^ m * ι a * s + q * r, ?_⟩` and prove the remaining obligations. Rewrite using `[map_mul, pow_add]`. Take the linear combination `(t ^ m * ι a) * h`.
-/
theorem near_mul_of_bound {c m : ℕ} {q w : R} (hq : Near ι p t 0 (t ^ c * q))
    (hw : Near ι p t (m + c) w) : Near ι p t m (q * w) := by
  obtain ⟨a, r, rfl⟩ := hw
  obtain ⟨b, s, h⟩ := hq
  refine ⟨b * a, t ^ m * ι a * s + q * r, ?_⟩
  rw [map_mul, pow_add]
  linear_combination (t ^ m * ι a) * h

/- English proof (translation)
Take `⟨k, rfl⟩` from `Nat.exists_eq_add_of_le h`. Establish `h1` using `hq.mul_ι (τ ^ k)`. Rewrite `h1` using `[map_pow, hτ]`. Use `h1 using 1` and compare the differences between its conclusion and the goal. Expand and normalize the polynomial expressions, which then agree.
-/
theorem near_bound_mono {τ : A} (hτ : ι τ = t) {c c' : ℕ} (h : c ≤ c') {q : R}
    (hq : Near ι p t 0 (t ^ c * q)) : Near ι p t 0 (t ^ c' * q) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le h
  have h1 := hq.mul_ι (τ ^ k)
  rw [map_pow, hτ] at h1
  convert h1 using 1
  ring

def nearSub (ι : A →+* R) (p : ℕ) (t : R) (m : ℕ) : AddSubgroup R where
  carrier := {x | Near ι p t m x}
  add_mem' := Near.add
  zero_mem' := Near.zero m
  neg_mem' := Near.neg

def vecs (d : ℕ) (H : AddSubgroup R) : AddSubgroup (Fin d → R) where
  carrier := {v | ∀ i, v i ∈ H}
  add_mem' := fun ha hb i => H.add_mem (ha i) (hb i)
  zero_mem' := fun _ => H.zero_mem
  neg_mem' := fun ha i => H.neg_mem (ha i)

def semi {d : ℕ} (Q : Fin d → Fin d → R) (φ : R →+* R) : (Fin d → R) →+ (Fin d → R) where
  toFun v := fun i => ∑ k, Q i k * φ (v k)
  map_zero' := by ext i; simp
  map_add' v w := by ext i; simp [mul_add, Finset.sum_add_distrib]

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem semi_apply {d : ℕ} (Q : Fin d → Fin d → R) (φ : R →+* R) (v : Fin d → R) (i : Fin d) :
    semi Q φ v i = ∑ k, Q i k * φ (v k) := rfl

/- English proof (translation)
Use `choose ψ hψ using hφ`. Proceed by induction on `n with`. Consider the case `zero`. Use `⟨fun i k => if i = k then 1 else 0, fun v i => ?_⟩` and prove the remaining obligations. Simplify using `[apply_ite j]`.

Consider the case `succ n ih`. Take `⟨q, hq⟩` from `ih`. Use `⟨fun i l => ∑ k, Pm i k * ψ (q k l), fun v i => ?_⟩` and prove the remaining obligations. Rewrite using `[Function.iterate_succ_apply', semi_apply]`. Simplify using `only [hq, map_sum, map_mul, hψ, Function.iterate_succ_apply', Finset.mul_sum, Finset.sum_mul]`.

Rewrite using `[Finset.sum_comm]`. Simplify using `only [mul_assoc]`.
-/
theorem semi_iterate {EE : Type} [CommRing EE] (j : EE →+* R) (φ : R →+* R)
    (hφ : ∀ e, ∃ e', φ (j e) = j e') {d : ℕ} (Pm : Matrix (Fin d) (Fin d) EE) (n : ℕ) :
    ∃ q : Fin d → Fin d → EE, ∀ v i,
      (semi (fun i k => j (Pm i k)) φ)^[n] v i = ∑ k, j (q i k) * φ^[n] (v k) := by
  classical
  choose ψ hψ using hφ
  induction n with
  | zero =>
    refine ⟨fun i k => if i = k then 1 else 0, fun v i => ?_⟩
    simp [apply_ite j]
  | succ n ih =>
    obtain ⟨q, hq⟩ := ih
    refine ⟨fun i l => ∑ k, Pm i k * ψ (q k l), fun v i => ?_⟩
    rw [Function.iterate_succ_apply', semi_apply]
    simp only [hq, map_sum, map_mul, hψ, Function.iterate_succ_apply', Finset.mul_sum,
      Finset.sum_mul]
    rw [Finset.sum_comm]
    simp only [mul_assoc]

/- English proof (translation)
Proceed by induction on `h with`. Consider the case `refl => exact hy`. Consider the case `step _ ih`. Take `⟨e, r, h⟩` from `ih`. Take `⟨e', he'⟩` from `hφ e`.

Use `⟨e', φ r, ?_⟩` and prove the remaining obligations. Rewrite using `[Function.iterate_succ_apply', h, map_add, map_mul, map_natCast, he']`.
-/
theorem iterate_persist {EE : Type} [CommRing EE] (j : EE →+* R) (φ : R →+* R)
    (hφ : ∀ e, ∃ e', φ (j e) = j e') {n n' : ℕ} (h : n ≤ n') {y : R}
    (hy : ∃ e r, φ^[n] y = j e + (p : R) * r) : ∃ e r, φ^[n'] y = j e + (p : R) * r := by
  induction h with
  | refl => exact hy
  | step _ ih =>
    obtain ⟨e, r, h⟩ := ih
    obtain ⟨e', he'⟩ := hφ e
    refine ⟨e', φ r, ?_⟩
    rw [Function.iterate_succ_apply', h, map_add, map_mul, map_natCast, he']

/- English proof (translation)
Introduce `R EE A _ _ _ j ι φ S p t τ hτ hjS hφS hφj hφι hφt hbd hSs hEs hc hcl hnil hpc hEc d Pm`. Take `⟨c, hcP⟩ : ∃ c : ℕ, ∀ i k, Near ι p t 0 (t ^ c * j (Pm i k))` from `by choose cf hcf using hbd`. Conclude with `⟨Finset.univ.sup (fun x : Fin d × Fin d => cf (Pm x.1 x.2)), fun i k => near_bound_mono hτ (Finset.le_sup (f := fun x : Fin d × Fin d => cf (Pm x.1 x.2)) (Finset.mem_univ (i, k))) (hcf _)⟩`. Use `set Φ := semi (fun i k => j (Pm i k)) φ with hΦ`. Establish `hF : ∀ m, ∀ x ∈ vecs d (nearSub ι p t (m + (c + 1))), Φ x ∈ vecs d (nearSub ι p t (m + 1 + (c + 1)))`.

Introduce `m x hx i`. Express the relevant statement in the definitionally equal form `Near ι p t _ (∑ k, j (Pm i k) * φ (x k))`. Use `Near.sum _ fun k _ => near_mul_of_bound (hcP i k) ?_` and prove the remaining obligations. Conclude with `(near_frob φ hφι hφt (hx k)).mono hτ (by omega)`. Establish `hFa : ∀ m, vecs d (nearSub ι p t (m + 1 + (c + 1))) ≤ vecs d (nearSub ι p t (m + (c + 1)))` using `fun m x hx i => Near.mono hτ (by omega) (hx i)`.

Establish `key` using `sub_one_bijective_quotient_of_topNilpotent (Fin d → R) p Φ (vecs d S.toAddSubgroup) (vecs d j.range.toAddSubgroup) (fun m => vecs d (nearSub ι p t (m + (c + 1)))) (fun x hx i => by obtain ⟨e, he⟩ := hx i; exact he ▸ hjS e) (fun x hx i => show ∑ k, j (Pm i k) * φ (x k) ∈ S from S. …`. Take `⟨e, he⟩` from `hx k`. Take `⟨e', he'⟩` from `hφj e`. Conclude with `⟨e', by rw [← he', he]⟩))`. Use `hF hFa`.

Use the proof step `(fun x hx i => hSs _ (by simpa using hx i))`. Use the proof step `(fun x hx i => by`. Take `⟨e, he⟩` from `hx i`. Take `⟨e', he'⟩` from `hEs (x i) e (by simpa using he.symm)`. Conclude with `⟨e', he'.symm⟩)`.

Use the proof step `(fun f hf hf' => by choose s hs hs' using fun i => hc (c + 1) (fun n => f n i) (fun n => hf n i) (fun n => hf' n i)`. Use `⟨s, hs, fun m i => ?_⟩` and prove the remaining obligations. Use `hs' i m` as an intermediate fact. Rewrite using `[Pi.sub_apply, Finset.sum_apply]`. Conclude with `this)`.

Use the proof step `(fun x hx => by choose e r h using fun i => hcl (x i) (fun m => by`. Take `⟨w, hw, hw'⟩` from `hx m`. Take `⟨e, he⟩` from `hw i`. Conclude with `⟨e, he ▸ Near.mono hτ (Nat.le_add_right _ _) (hw' i)⟩)`. Use `⟨fun i => j (e i), fun i => ⟨_, rfl⟩, r, ?_⟩` and prove the remaining obligations.

Use extensionality with `i`. Simplify using `using h i)`. Use the proof step `(fun y hy => by choose n y0 e r h1 h2 using fun i => hnil (y i) (hy i) (c + 1)`. Take `⟨q, hq⟩` from `semi_iterate j φ hφj Pm (Finset.univ.sup n)`. Use `choose e' r' h' using fun i => iterate_persist (p := p) j φ hφj (Finset.le_sup (f := n) (Finset.mem_univ i)) ⟨e i, r i, h1 i⟩`.

Establish `it : ∀ N : ℕ, Φ^[N] y - Φ^[N] y0 ∈ vecs d (nearSub ι p t (0 + (c + 1)))`. Introduce `N`. Proceed by induction on `N with`. Consider the case `zero => intro i`. Rewrite using `[Nat.zero_add]`.

Conclude with `h2 i`. Consider the case `succ N ih`. Rewrite using `[Function.iterate_succ_apply', Function.iterate_succ_apply', ← map_sub]`. Conclude with `hFa 0 (hF 0 _ ih)`. Use `⟨Finset.univ.sup n, fun i => j (∑ k, q i k * e' k), fun i => ⟨_, rfl⟩, fun i => ?_⟩` and prove the remaining obligations.

Establish `h3 : Near ι p t (0 + (c + 1)) _` using `it (Finset.univ.sup n) i`. Establish `h4` using `h3.add (Near.of_mul _ (∑ k, j (q i k) * r' k))`. Express the relevant statement in the definitionally equal form `Near ι p t (0 + (c + 1)) _`. Use `h4 using 1` and compare the differences between its conclusion and the goal. Simplify using `only [Pi.sub_apply]`.

Rewrite using `[hq y0 i]`. Simplify using `only [h', mul_add, Finset.sum_add_distrib, map_sum, map_mul, Finset.mul_sum, mul_left_comm (p : R)]`. Use the proof step `ring)`. Use the proof step `(fun x hx => by choose s hs hs' using fun i => hpc (fun n => x n i) (fun n => hx n i)`. Use `⟨s, hs, fun k => ?_⟩` and prove the remaining obligations.

Use `choose r hr using fun i => hs' i k`. Use `⟨r, ?_⟩` and prove the remaining obligations. Use extensionality with `i`. Simplify `hr i)` using `[Finset.sum_apply]`. Use the proof step `(fun x hx i => by`.

Take `⟨e, he⟩` from `hEc (x i) (fun k => by`. Take `⟨w, hw, r, hr⟩` from `hx k`. Take `⟨e, he⟩` from `hw i`. Use `⟨e, r i, ?_⟩` and prove the remaining obligations. Rewrite using `[he]`.

Simplify using `using congrFun hr i)`. Conclude with `⟨e, he.symm⟩)`. Use `⟨fun y hy => ?_, fun z hz h i => ?_⟩` and prove the remaining obligations. Take `⟨z, hz, h⟩` from `key.1 y hy`. Use `⟨z, hz, fun i => ?_⟩` and prove the remaining obligations.

Take `⟨e, he⟩` from `h i`. Conclude with `⟨e, he.symm⟩`. Take `⟨e, he⟩` from `key.2 z hz (fun i => by`. Take `⟨e, he⟩` from `h i`. Conclude with `⟨e, he.symm⟩) i`.

Conclude with `⟨e, he.symm⟩`.
-/
theorem matrix_frob_sub_one_bijective :
    ∀ (R EE A : Type) [CommRing R] [CommRing EE] [CommRing A] (j : EE →+* R) (ι : A →+* R) (φ : R →+* R) (S : Subring R) (p : ℕ) (t : R) (τ : A), ι τ = t → (∀ e, j e ∈ S) → (∀ x ∈ S, φ x ∈ S) → (∀ e, ∃ e', φ (j e) = j e') → (∀ a, ∃ a', φ (ι a) = ι a') → Near ι p t 2 (φ t) → (∀ e, ∃ c : ℕ, Near ι p t 0 (t ^ c * j e)) → (∀ x, (p : R) * x ∈ S → x ∈ S) → (∀ x e, (p : R) * x = j e → ∃ e', x = j e') → (∀ (k : ℕ) (f : ℕ → R), (∀ i, f i ∈ S) → (∀ i, Near ι p t (i + k) (f i)) → ∃ s ∈ S, ∀ m, Near ι p t (m + k) (s - ∑ i ∈ Finset.range m, f i)) → (∀ x, (∀ m, ∃ e, Near ι p t m (x - j e)) → ∃ e r, x - j e = (p : R) * r) → (∀ y ∈ S, ∀ m, ∃ (n : ℕ) (y0 : R) (e : EE) (r : R), φ^[n] y0 = j e + (p : R) * r ∧ Near ι p t m (y - y0)) → (∀ x : ℕ → R, (∀ i, x i ∈ S) → ∃ s ∈ S, ∀ k, ∃ r, s - ∑ i ∈ Finset.range k, (p : R) ^ i * x i = (p : R) ^ k * r) → (∀ x, (∀ k : ℕ, ∃ e r, x - j e = (p : R) ^ k * r) → ∃ e, x = j e) → ∀ (d : ℕ) (Pm : Matrix (Fin d) (Fin d) EE), (∀ y : Fin d → R, (∀ i, y i ∈ S) → ∃ z : Fin d → R, (∀ i, z i ∈ S) ∧ ∀ i, ∃ e, y i - (∑ k, j (Pm i k) * φ (z k) - z i) = j e) ∧ (∀ z : Fin d → R, (∀ i, z i ∈ S) → (∀ i, ∃ e, ∑ k, j (Pm i k) * φ (z k) - z i = j e) → ∀ i, ∃ e, z i = j e) := by
  intro R EE A _ _ _ j ι φ S p t τ hτ hjS hφS hφj hφι hφt hbd hSs hEs hc hcl hnil hpc hEc d Pm
  classical
  obtain ⟨c, hcP⟩ : ∃ c : ℕ, ∀ i k, Near ι p t 0 (t ^ c * j (Pm i k)) := by
    choose cf hcf using hbd
    exact ⟨Finset.univ.sup (fun x : Fin d × Fin d => cf (Pm x.1 x.2)), fun i k =>
      near_bound_mono hτ (Finset.le_sup (f := fun x : Fin d × Fin d => cf (Pm x.1 x.2))
        (Finset.mem_univ (i, k))) (hcf _)⟩
  set Φ := semi (fun i k => j (Pm i k)) φ with hΦ
  have hF : ∀ m, ∀ x ∈ vecs d (nearSub ι p t (m + (c + 1))),
      Φ x ∈ vecs d (nearSub ι p t (m + 1 + (c + 1))) := by
    intro m x hx i
    change Near ι p t _ (∑ k, j (Pm i k) * φ (x k))
    refine Near.sum _ fun k _ => near_mul_of_bound (hcP i k) ?_
    exact (near_frob φ hφι hφt (hx k)).mono hτ (by omega)
  have hFa : ∀ m, vecs d (nearSub ι p t (m + 1 + (c + 1))) ≤
      vecs d (nearSub ι p t (m + (c + 1))) :=
    fun m x hx i => Near.mono hτ (by omega) (hx i)
  have key := sub_one_bijective_quotient_of_topNilpotent (Fin d → R) p Φ
    (vecs d S.toAddSubgroup) (vecs d j.range.toAddSubgroup)
    (fun m => vecs d (nearSub ι p t (m + (c + 1))))
    (fun x hx i => by obtain ⟨e, he⟩ := hx i; exact he ▸ hjS e)
    (fun x hx i => show ∑ k, j (Pm i k) * φ (x k) ∈ S from S.sum_mem fun k _ => S.mul_mem (hjS _) (hφS _ (hx k)))
    (fun x hx i => show ∑ k, j (Pm i k) * φ (x k) ∈ j.range from
      j.range.sum_mem fun k _ => j.range.mul_mem ⟨_, rfl⟩ (by
      obtain ⟨e, he⟩ := hx k
      obtain ⟨e', he'⟩ := hφj e
      exact ⟨e', by rw [← he', he]⟩))
    hF hFa
    (fun x hx i => hSs _ (by simpa using hx i))
    (fun x hx i => by
      obtain ⟨e, he⟩ := hx i
      obtain ⟨e', he'⟩ := hEs (x i) e (by simpa using he.symm)
      exact ⟨e', he'.symm⟩)
    (fun f hf hf' => by
      choose s hs hs' using fun i => hc (c + 1) (fun n => f n i) (fun n => hf n i)
        (fun n => hf' n i)
      refine ⟨s, hs, fun m i => ?_⟩
      have := hs' i m
      rw [Pi.sub_apply, Finset.sum_apply]
      exact this)
    (fun x hx => by
      choose e r h using fun i => hcl (x i) (fun m => by
        obtain ⟨w, hw, hw'⟩ := hx m
        obtain ⟨e, he⟩ := hw i
        exact ⟨e, he ▸ Near.mono hτ (Nat.le_add_right _ _) (hw' i)⟩)
      refine ⟨fun i => j (e i), fun i => ⟨_, rfl⟩, r, ?_⟩
      ext i
      simpa using h i)
    (fun y hy => by
      choose n y0 e r h1 h2 using fun i => hnil (y i) (hy i) (c + 1)
      obtain ⟨q, hq⟩ := semi_iterate j φ hφj Pm (Finset.univ.sup n)
      choose e' r' h' using fun i => iterate_persist (p := p) j φ hφj
        (Finset.le_sup (f := n) (Finset.mem_univ i)) ⟨e i, r i, h1 i⟩
      have it : ∀ N : ℕ, Φ^[N] y - Φ^[N] y0 ∈ vecs d (nearSub ι p t (0 + (c + 1))) := by
        intro N
        induction N with
        | zero => intro i; rw [Nat.zero_add]; exact h2 i
        | succ N ih =>
          rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ← map_sub]
          exact hFa 0 (hF 0 _ ih)
      refine ⟨Finset.univ.sup n, fun i => j (∑ k, q i k * e' k), fun i => ⟨_, rfl⟩, fun i => ?_⟩
      have h3 : Near ι p t (0 + (c + 1)) _ := it (Finset.univ.sup n) i
      have h4 := h3.add (Near.of_mul _ (∑ k, j (q i k) * r' k))
      change Near ι p t (0 + (c + 1)) _
      convert h4 using 1
      simp only [Pi.sub_apply]
      rw [hq y0 i]
      simp only [h', mul_add, Finset.sum_add_distrib, map_sum, map_mul, Finset.mul_sum,
        mul_left_comm (p : R)]
      ring)
    (fun x hx => by
      choose s hs hs' using fun i => hpc (fun n => x n i) (fun n => hx n i)
      refine ⟨s, hs, fun k => ?_⟩
      choose r hr using fun i => hs' i k
      refine ⟨r, ?_⟩
      ext i
      simpa [Finset.sum_apply] using hr i)
    (fun x hx i => by
      obtain ⟨e, he⟩ := hEc (x i) (fun k => by
        obtain ⟨w, hw, r, hr⟩ := hx k
        obtain ⟨e, he⟩ := hw i
        refine ⟨e, r i, ?_⟩
        rw [he]
        simpa using congrFun hr i)
      exact ⟨e, he.symm⟩)
  refine ⟨fun y hy => ?_, fun z hz h i => ?_⟩
  · obtain ⟨z, hz, h⟩ := key.1 y hy
    refine ⟨z, hz, fun i => ?_⟩
    obtain ⟨e, he⟩ := h i
    exact ⟨e, he.symm⟩
  · obtain ⟨e, he⟩ := key.2 z hz (fun i => by
      obtain ⟨e, he⟩ := h i
      exact ⟨e, he.symm⟩) i
    exact ⟨e, he.symm⟩

end GlobalTheory.DecomplMat

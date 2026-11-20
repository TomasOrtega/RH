import Formalism.CharacterColumnKernels.StatOntoLattice

open Polynomial

noncomputable section

namespace Formalism.NG

namespace IdemLiftAlt

def nP : ℕ → ℤ[X]
  | 0 => X
  | k + 1 => 3 * nP k ^ 2 - 2 * nP k ^ 3

/- English proof (translation)
Proceed by induction on `k with`. Consider the case `zero => exact ⟨1, by simp [nP]⟩`. Consider the case `succ k ih`. Take `⟨U, hU⟩` from `ih`. Use `⟨U ^ 2 * (4 * (nP k ^ 2 - nP k) - 3), ?_⟩` and prove the remaining obligations.

Establish `h : nP (k + 1) ^ 2 - nP (k + 1) = (nP k ^ 2 - nP k) ^ 2 * (4 * (nP k ^ 2 - nP k) - 3)`. Simplify using `only [nP]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[h, hU, pow_succ 2 k, pow_mul]`. Expand and normalize the polynomial expressions, which then agree.
-/
lemma pow_dvd_nP_sq_sub (k : ℕ) : ∃ U : ℤ[X], nP k ^ 2 - nP k = (X ^ 2 - X) ^ (2 ^ k) * U := by
  induction k with
  | zero => exact ⟨1, by simp [nP]⟩
  | succ k ih =>
    obtain ⟨U, hU⟩ := ih
    refine ⟨U ^ 2 * (4 * (nP k ^ 2 - nP k) - 3), ?_⟩
    have h : nP (k + 1) ^ 2 - nP (k + 1) =
        (nP k ^ 2 - nP k) ^ 2 * (4 * (nP k ^ 2 - nP k) - 3) := by
      simp only [nP]; ring
    rw [h, hU, pow_succ 2 k, pow_mul]; ring

/- English proof (translation)
Proceed by induction on `k with`. Consider the case `zero => exact dvd_refl _`. Consider the case `succ k ih`. Take `⟨R, hR⟩` from `ih`. Conclude with `⟨R * (3 * nP k - 2 * nP k ^ 2), by simp only [nP]; rw [hR]; ring⟩`.
-/
lemma X_dvd_nP (k : ℕ) : X ∣ nP k := by
  induction k with
  | zero => exact dvd_refl _
  | succ k ih =>
    obtain ⟨R, hR⟩ := ih
    exact ⟨R * (3 * nP k - 2 * nP k ^ 2), by simp only [nP]; rw [hR]; ring⟩

variable {O A : Type*} [CommRing O] [Ring A] [Algebra O A]

/- English proof (translation)
Use `Submodule.smul_induction_on hx (fun r hr a _ => ?_) (fun u v hu hv => ?_)` and prove the remaining obligations. Rewrite using `[smul_mul_assoc]`. Conclude with `Submodule.smul_mem_smul hr Submodule.mem_top`. Rewrite using `[add_mul]`. Conclude with `Submodule.add_mem _ hu hv`.
-/
lemma mul_mem_left (I : Ideal O) {x : A} (y : A) (hx : x ∈ I • (⊤ : Submodule O A)) :
    x * y ∈ I • (⊤ : Submodule O A) := by
  refine Submodule.smul_induction_on hx (fun r hr a _ => ?_) (fun u v hu hv => ?_)
  · rw [smul_mul_assoc]; exact Submodule.smul_mem_smul hr Submodule.mem_top
  · rw [add_mul]; exact Submodule.add_mem _ hu hv

/- English proof (translation)
Use `Submodule.smul_induction_on hx (fun r hr a _ => ?_) (fun u v hu hv => ?_)` and prove the remaining obligations. Rewrite using `[mul_smul_comm]`. Conclude with `Submodule.smul_mem_smul hr Submodule.mem_top`. Rewrite using `[mul_add]`. Conclude with `Submodule.add_mem _ hu hv`.
-/
lemma mul_mem_right (I : Ideal O) (y : A) {x : A} (hx : x ∈ I • (⊤ : Submodule O A)) :
    y * x ∈ I • (⊤ : Submodule O A) := by
  refine Submodule.smul_induction_on hx (fun r hr a _ => ?_) (fun u v hu hv => ?_)
  · rw [mul_smul_comm]; exact Submodule.smul_mem_smul hr Submodule.mem_top
  · rw [mul_add]; exact Submodule.add_mem _ hu hv

/- English proof (translation)
Use `Submodule.smul_induction_on hx (fun r hr a _ => ?_) (fun u v hu hv => ?_)` and prove the remaining obligations. Rewrite using `[smul_mul_assoc, pow_add, Submodule.mul_smul]`. Conclude with `Submodule.smul_mem_smul hr (mul_mem_right _ a hy)`. Rewrite using `[add_mul]`. Conclude with `Submodule.add_mem _ hu hv`.
-/
lemma mul_mem_pow (I : Ideal O) {i j : ℕ} {x y : A} (hx : x ∈ I ^ i • (⊤ : Submodule O A))
    (hy : y ∈ I ^ j • (⊤ : Submodule O A)) : x * y ∈ I ^ (i + j) • (⊤ : Submodule O A) := by
  refine Submodule.smul_induction_on hx (fun r hr a _ => ?_) (fun u v hu hv => ?_)
  · rw [smul_mul_assoc, pow_add, Submodule.mul_smul]
    exact Submodule.smul_mem_smul hr (mul_mem_right _ a hy)
  · rw [add_mul]; exact Submodule.add_mem _ hu hv

/- English proof (translation)
The claim follows from `Submodule.smul_mono_left (Ideal.pow_le_pow_right h) hx`.
-/
lemma pow_smul_mono (I : Ideal O) {i j : ℕ} (h : i ≤ j) {x : A}
    (hx : x ∈ I ^ j • (⊤ : Submodule O A)) : x ∈ I ^ i • (⊤ : Submodule O A) :=
  Submodule.smul_mono_left (Ideal.pow_le_pow_right h) hx

/- English proof (translation)
Use `Submodule.smul_induction_on hx (fun r hr a _ => ?_) (fun u v hu hv => ?_)` and prove the remaining obligations. Rewrite using `[map_smul]`. Conclude with `Submodule.smul_mem_smul hr Submodule.mem_top`. Rewrite using `[map_add]`. Conclude with `Submodule.add_mem _ hu hv`.
-/
lemma map_mem_smul_top (I : Ideal O) {M N : Type*} [AddCommGroup M] [Module O M]
    [AddCommGroup N] [Module O N] (φ : M →ₗ[O] N) {x : M} (hx : x ∈ I • (⊤ : Submodule O M)) :
    φ x ∈ I • (⊤ : Submodule O N) := by
  refine Submodule.smul_induction_on hx (fun r hr a _ => ?_) (fun u v hu hv => ?_)
  · rw [map_smul]; exact Submodule.smul_mem_smul hr Submodule.mem_top
  · rw [map_add]; exact Submodule.add_mem _ hu hv

/- English proof (translation)
Rewrite using `[← AdicCompletion.of_surjective_iff]`. Introduce `y`. Take `⟨t, rfl⟩` from `(AdicCompletion.ofTensorProduct_bijective_of_finite_of_isNoetherian I (Fin n → O)).2 y`. Proceed by induction on `t using TensorProduct.induction_on with`. Consider the case `zero => exact ⟨0, by simp⟩`.

Consider the case `tmul r x`. Take `⟨c, rfl⟩` from `AdicCompletion.of_surjective I O r`. Use `⟨c • x, ?_⟩` and prove the remaining obligations. Rewrite using `[AdicCompletion.ofTensorProduct_tmul, map_smul]`. Establish `hc : AdicCompletion.of I O c = algebraMap O (AdicCompletion I O) c`.

Rewrite using `[AdicCompletion.algebraMap_apply, Algebra.algebraMap_self_apply]`. Rewrite using `[hc, algebraMap_smul]`. Consider the case `add u v hu hv`. Take `⟨p, hp⟩` from `hu`. Take `⟨q, hq⟩` from `hv`.

Conclude with `⟨p + q, by rw [map_add, map_add, hp, hq]⟩`.
-/
lemma precomplete_pi (I : Ideal O) [IsNoetherianRing O] [IsAdicComplete I O] (n : ℕ) :
    IsPrecomplete I (Fin n → O) := by
  rw [← AdicCompletion.of_surjective_iff]
  intro y
  obtain ⟨t, rfl⟩ :=
    (AdicCompletion.ofTensorProduct_bijective_of_finite_of_isNoetherian I (Fin n → O)).2 y
  induction t using TensorProduct.induction_on with
  | zero => exact ⟨0, by simp⟩
  | tmul r x =>
    obtain ⟨c, rfl⟩ := AdicCompletion.of_surjective I O r
    refine ⟨c • x, ?_⟩
    rw [AdicCompletion.ofTensorProduct_tmul, map_smul]
    have hc : AdicCompletion.of I O c = algebraMap O (AdicCompletion I O) c := by
      rw [AdicCompletion.algebraMap_apply, Algebra.algebraMap_self_apply]
    rw [hc, algebraMap_smul]
  | add u v hu hv =>
    obtain ⟨p, hp⟩ := hu
    obtain ⟨q, hq⟩ := hv
    exact ⟨p + q, by rw [map_add, map_add, hp, hq]⟩

/- English proof (translation)
Use `⟨fun f hf => ?_⟩` and prove the remaining obligations. Establish `hmap : ∀ k, (I ^ k • (⊤ : Submodule O M)).map π = I ^ k • (⊤ : Submodule O N)`. Introduce `k`. Rewrite using `[Submodule.map_smul'', Submodule.map_top, LinearMap.range_eq_top.2 hπ]`. Establish `hd : ∀ k, ∃ d ∈ I ^ k • (⊤ : Submodule O M), π d = f (k + 1) - f k`.

Introduce `k`. Establish `h1 : f (k + 1) - f k ∈ I ^ k • (⊤ : Submodule O N)`. Use `(SModEq.sub_mem).1 (hf (show k ≤ k + 1 by omega))` as an intermediate fact. Use `Submodule.neg_mem _ this` as an intermediate fact. Simplify using `using this`.

Rewrite `h1` using `[← hmap]`. Take `⟨d, hd, hd'⟩` from `h1`. Conclude with `⟨d, hd, hd'⟩`. Use `choose d hdm hdπ using hd`. Take `⟨g0, hg0⟩` from `hπ (f 0)`.

Set `g : ℕ → M` to `fun k => g0 + ∑ i ∈ Finset.range k, d i`. Establish `hg : ∀ k, π (g k) = f k`. Introduce `k`. Proceed by induction on `k with`. Consider the case `zero => simp [g, hg0]`.

Consider the case `succ k ih`. Establish `e : g (k + 1) = g k + d k` using `by simp [g, Finset.sum_range_succ, add_assoc]`. Rewrite using `[e, map_add, ih, hdπ]`. Normalize the expressions using the abelian group laws. Establish `hgc : ∀ m k, m ≤ k → g m - g k ∈ I ^ m • (⊤ : Submodule O M)`.

Introduce `m k hmk`. Proceed by induction on `k, hmk using Nat.le_induction with`. Consider the case `base => simp`. Consider the case `succ k hmk ih`. Establish `e : g m - g (k + 1) = (g m - g k) - d k`.

Simplify using `only [g, Finset.sum_range_succ]`. Normalize the expressions using the abelian group laws. Rewrite using `[e]`. Conclude with `Submodule.sub_mem _ ih (Submodule.smul_mono_left (Ideal.pow_le_pow_right hmk) (hdm k))`. Take `⟨L, hL⟩` from `IsPrecomplete.prec ‹_› (f := g) (fun {m k} hmk => (SModEq.sub_mem).2 (hgc m k hmk))`.

Use `⟨π L, fun k => ?_⟩` and prove the remaining obligations. Rewrite using `[SModEq.sub_mem, ← hg k, ← map_sub]`. Conclude with `map_mem_smul_top _ π ((SModEq.sub_mem).1 (hL k))`.
-/
lemma precomplete_of_surjective (I : Ideal O) {M N : Type*} [AddCommGroup M] [Module O M]
    [AddCommGroup N] [Module O N] [IsPrecomplete I M] (π : M →ₗ[O] N)
    (hπ : Function.Surjective π) : IsPrecomplete I N := by
  refine ⟨fun f hf => ?_⟩
  have hmap : ∀ k, (I ^ k • (⊤ : Submodule O M)).map π = I ^ k • (⊤ : Submodule O N) := by
    intro k
    rw [Submodule.map_smul'', Submodule.map_top, LinearMap.range_eq_top.2 hπ]
  have hd : ∀ k, ∃ d ∈ I ^ k • (⊤ : Submodule O M), π d = f (k + 1) - f k := by
    intro k
    have h1 : f (k + 1) - f k ∈ I ^ k • (⊤ : Submodule O N) := by
      have := (SModEq.sub_mem).1 (hf (show k ≤ k + 1 by omega))
      have := Submodule.neg_mem _ this
      simpa using this
    rw [← hmap] at h1
    obtain ⟨d, hd, hd'⟩ := h1
    exact ⟨d, hd, hd'⟩
  choose d hdm hdπ using hd
  obtain ⟨g0, hg0⟩ := hπ (f 0)
  let g : ℕ → M := fun k => g0 + ∑ i ∈ Finset.range k, d i
  have hg : ∀ k, π (g k) = f k := by
    intro k
    induction k with
    | zero => simp [g, hg0]
    | succ k ih =>
      have e : g (k + 1) = g k + d k := by simp [g, Finset.sum_range_succ, add_assoc]
      rw [e, map_add, ih, hdπ]; abel
  have hgc : ∀ m k, m ≤ k → g m - g k ∈ I ^ m • (⊤ : Submodule O M) := by
    intro m k hmk
    induction k, hmk using Nat.le_induction with
    | base => simp
    | succ k hmk ih =>
      have e : g m - g (k + 1) = (g m - g k) - d k := by
        simp only [g, Finset.sum_range_succ]; abel
      rw [e]
      exact Submodule.sub_mem _ ih
        (Submodule.smul_mono_left (Ideal.pow_le_pow_right hmk) (hdm k))
  obtain ⟨L, hL⟩ := IsPrecomplete.prec ‹_› (f := g) (fun {m k} hmk => (SModEq.sub_mem).2 (hgc m k hmk))
  refine ⟨π L, fun k => ?_⟩
  rw [SModEq.sub_mem, ← hg k, ← map_sub]
  exact map_mem_smul_top _ π ((SModEq.sub_mem).1 (hL k))

/- English proof (translation)
Take `⟨n, π, hπ⟩` from `Module.Finite.exists_fin' O M`. Use `precomplete_pi I n` as an intermediate fact. Conclude with `precomplete_of_surjective I π hπ`.
-/
lemma precomplete_of_finite (I : Ideal O) [IsNoetherianRing O] [IsAdicComplete I O]
    (M : Type*) [AddCommGroup M] [Module O M] [Module.Finite O M] : IsPrecomplete I M := by
  obtain ⟨n, π, hπ⟩ := Module.Finite.exists_fin' O M
  have := precomplete_pi I n
  exact precomplete_of_surjective I π hπ

variable [IsLocalRing O] [IsNoetherianRing O] [IsAdicComplete (IsLocalRing.maximalIdeal O) O]
  [Module.Finite O A]

/- English proof (translation)
Use `set I := IsLocalRing.maximalIdeal O`. Use `set S : ℕ → Submodule O A := fun j => I ^ j • (⊤ : Submodule O A) with hS`. Establish `hS1 : S 1 = I • ⊤` using `by simp [hS]`. Use `set ak : ℕ → A := fun k => aeval a (nP k) with hak`. Establish `hrec : ∀ k, ak (k + 1) = 3 * ak k ^ 2 - 2 * ak k ^ 3`.

Introduce `k`. Simplify using `[hak, nP, map_ofNat]`. Establish `hxrec : ∀ k, ak (k + 1) ^ 2 - ak (k + 1) = (ak k ^ 2 - ak k) * ((ak k ^ 2 - ak k) * (4 * (ak k ^ 2 - ak k) - 3))`. Introduce `k`. Rewrite using `[hrec]`.

Use `noncomm_ring`. Establish `hdiff : ∀ k, ak (k + 1) - ak k = (ak k ^ 2 - ak k) * (1 - 2 * ak k)`. Introduce `k`. Rewrite using `[hrec]`. Use `noncomm_ring`.

Establish `hx0 : ak n ^ 2 - ak n ∈ S 1`. Take `⟨U, hU⟩` from `pow_dvd_nP_sq_sub n`. Establish `h1 : ak n ^ 2 - ak n = (a ^ 2 - a) ^ (2 ^ n) * aeval a U`. Use `congrArg (aeval a) hU` as an intermediate fact. Simplify `this` using `[hak]`.

Rewrite using `[h1, hS1]`. Apply `mul_mem_left` to reduce the goal to its premises. Establish `h2 : 2 ^ n = n + (2 ^ n - n)` using `(Nat.add_sub_cancel' (Nat.lt_two_pow_self).le).symm`. Rewrite using `[h2, pow_add]`. Conclude with `mul_mem_left _ _ hn`.

Establish `hx : ∀ j, ak (n + j) ^ 2 - ak (n + j) ∈ S (j + 1)`. Introduce `j`. Proceed by induction on `j with`. Consider the case `zero => simpa using hx0`. Consider the case `succ j ih`.

Rewrite using `[← add_assoc, hxrec]`. Establish `h3 : (ak (n + j) ^ 2 - ak (n + j)) * (4 * (ak (n + j) ^ 2 - ak (n + j)) - 3) ∈ S 1`. Rewrite using `[hS1]`. Apply `mul_mem_left` to reduce the goal to its premises. Use `pow_smul_mono I (show 1 ≤ j + 1 by omega) ih` as an intermediate fact.

Simplify using `using this`. Conclude with `mul_mem_pow I ih h3`. Use `set b : ℕ → A := fun j => ak (n + j) with hb`. Establish `hbstep : ∀ k, b (k + 1) - b k ∈ S (k + 1)`. Introduce `k`.

Simplify using `only [hb]`. Rewrite using `[← add_assoc, hdiff]`. Conclude with `mul_mem_left _ _ (hx k)`. Establish `hcauchy : ∀ m k, m ≤ k → b m - b k ∈ S m`. Introduce `m k hmk`.

Proceed by induction on `k, hmk using Nat.le_induction with`. Consider the case `base => simp`. Consider the case `succ k hmk ih`. Establish `e : b m - b (k + 1) = (b m - b k) - (b (k + 1) - b k)` using `by abel`. Rewrite using `[e]`.

Conclude with `Submodule.sub_mem _ ih (pow_smul_mono I (by omega) (hbstep k))`. Establish `hpre : IsPrecomplete I A` using `precomplete_of_finite I A`. Take `⟨L, hL⟩` from `hpre.prec (f := b) (fun {m k} hmk => (SModEq.sub_mem).2 (hcauchy m k hmk))`. Establish `hL' : ∀ j, b j - L ∈ S j` using `fun j => (SModEq.sub_mem).1 (hL j)`. Use `⟨L, ?_, hL'⟩` and prove the remaining obligations.

Establish `hzero : L * L - L = 0`. Use `IsHausdorff.haus (inferInstance : IsHausdorff I A) _ (fun j => ?_)` and prove the remaining obligations. Rewrite using `[SModEq.sub_mem, sub_zero]`. Establish `hLb : L - b j ∈ S j`. Use `Submodule.neg_mem _ (hL' j)` as an intermediate fact.

Simplify using `using this`. Establish `e : L * L - L = (L - b j) * L + b j * (L - b j) + (b j ^ 2 - b j) - (L - b j)` using `by noncomm_ring`. Rewrite using `[e]`. Use `Submodule.sub_mem _ (Submodule.add_mem _ (Submodule.add_mem _ ?_ ?_) ?_) hLb` and prove the remaining obligations. Conclude with `mul_mem_left _ _ hLb`.

Conclude with `mul_mem_right _ _ hLb`. Conclude with `pow_smul_mono I (by omega) (hx j)`. Conclude with `sub_eq_zero.1 hzero`.
-/
lemma newton (a : A) (n : ℕ)
    (hn : (a ^ 2 - a) ^ n ∈ IsLocalRing.maximalIdeal O • (⊤ : Submodule O A)) :
    ∃ L : A, IsIdempotentElem L ∧ ∀ j : ℕ,
      aeval a (nP (n + j)) - L ∈ IsLocalRing.maximalIdeal O ^ j • (⊤ : Submodule O A) := by
  set I := IsLocalRing.maximalIdeal O
  set S : ℕ → Submodule O A := fun j => I ^ j • (⊤ : Submodule O A) with hS
  have hS1 : S 1 = I • ⊤ := by simp [hS]
  set ak : ℕ → A := fun k => aeval a (nP k) with hak
  have hrec : ∀ k, ak (k + 1) = 3 * ak k ^ 2 - 2 * ak k ^ 3 := by
    intro k; simp [hak, nP, map_ofNat]
  have hxrec : ∀ k, ak (k + 1) ^ 2 - ak (k + 1) =
      (ak k ^ 2 - ak k) * ((ak k ^ 2 - ak k) * (4 * (ak k ^ 2 - ak k) - 3)) := by
    intro k; rw [hrec]; noncomm_ring
  have hdiff : ∀ k, ak (k + 1) - ak k = (ak k ^ 2 - ak k) * (1 - 2 * ak k) := by
    intro k; rw [hrec]; noncomm_ring
  have hx0 : ak n ^ 2 - ak n ∈ S 1 := by
    obtain ⟨U, hU⟩ := pow_dvd_nP_sq_sub n
    have h1 : ak n ^ 2 - ak n = (a ^ 2 - a) ^ (2 ^ n) * aeval a U := by
      have := congrArg (aeval a) hU
      simpa [hak] using this
    rw [h1, hS1]
    apply mul_mem_left
    have h2 : 2 ^ n = n + (2 ^ n - n) := (Nat.add_sub_cancel' (Nat.lt_two_pow_self).le).symm
    rw [h2, pow_add]
    exact mul_mem_left _ _ hn
  have hx : ∀ j, ak (n + j) ^ 2 - ak (n + j) ∈ S (j + 1) := by
    intro j
    induction j with
    | zero => simpa using hx0
    | succ j ih =>
      rw [← add_assoc, hxrec]
      have h3 : (ak (n + j) ^ 2 - ak (n + j)) * (4 * (ak (n + j) ^ 2 - ak (n + j)) - 3) ∈ S 1 := by
        rw [hS1]; apply mul_mem_left
        have := pow_smul_mono I (show 1 ≤ j + 1 by omega) ih
        simpa using this
      exact mul_mem_pow I ih h3
  set b : ℕ → A := fun j => ak (n + j) with hb
  have hbstep : ∀ k, b (k + 1) - b k ∈ S (k + 1) := by
    intro k
    simp only [hb]
    rw [← add_assoc, hdiff]
    exact mul_mem_left _ _ (hx k)
  have hcauchy : ∀ m k, m ≤ k → b m - b k ∈ S m := by
    intro m k hmk
    induction k, hmk using Nat.le_induction with
    | base => simp
    | succ k hmk ih =>
      have e : b m - b (k + 1) = (b m - b k) - (b (k + 1) - b k) := by abel
      rw [e]
      exact Submodule.sub_mem _ ih (pow_smul_mono I (by omega) (hbstep k))
  have hpre : IsPrecomplete I A := precomplete_of_finite I A
  obtain ⟨L, hL⟩ := hpre.prec (f := b) (fun {m k} hmk => (SModEq.sub_mem).2 (hcauchy m k hmk))
  have hL' : ∀ j, b j - L ∈ S j := fun j => (SModEq.sub_mem).1 (hL j)
  refine ⟨L, ?_, hL'⟩
  have hzero : L * L - L = 0 := by
    refine IsHausdorff.haus (inferInstance : IsHausdorff I A) _ (fun j => ?_)
    rw [SModEq.sub_mem, sub_zero]
    have hLb : L - b j ∈ S j := by
      have := Submodule.neg_mem _ (hL' j); simpa using this
    have e : L * L - L = (L - b j) * L + b j * (L - b j) + (b j ^ 2 - b j) - (L - b j) := by
      noncomm_ring
    rw [e]
    refine Submodule.sub_mem _ (Submodule.add_mem _ (Submodule.add_mem _ ?_ ?_) ?_) hLb
    · exact mul_mem_left _ _ hLb
    · exact mul_mem_right _ _ hLb
    · exact pow_smul_mono I (by omega) (hx j)
  exact sub_eq_zero.1 hzero

omit [IsAdicComplete (IsLocalRing.maximalIdeal O) O] in

/- English proof (translation)
Use `set I := IsLocalRing.maximalIdeal O`. Establish `h : φ L - c = 0`. Use `IsHausdorff.haus (inferInstance : IsHausdorff I M) _ (fun j => ?_)` and prove the remaining obligations. Rewrite using `[SModEq.sub_mem, sub_zero]`. Establish `e : φ L - c = -φ (aeval a (nP (n + j)) - L)` using `by rw [map_sub, hφ]; abel`.

Rewrite using `[e]`. Use `Submodule.neg_mem _ ?_` and prove the remaining obligations. Conclude with `map_mem_smul_top _ φ (hL j)`. Conclude with `sub_eq_zero.1 h`.
-/
lemma limit_map (a L : A) (n : ℕ)
    (hL : ∀ j : ℕ, aeval a (nP (n + j)) - L ∈ IsLocalRing.maximalIdeal O ^ j • (⊤ : Submodule O A))
    {M : Type*} [AddCommGroup M] [Module O M] [Module.Finite O M] (φ : A →ₗ[O] M) (c : M)
    (hφ : ∀ k, φ (aeval a (nP k)) = c) : φ L = c := by
  set I := IsLocalRing.maximalIdeal O
  have h : φ L - c = 0 := by
    refine IsHausdorff.haus (inferInstance : IsHausdorff I M) _ (fun j => ?_)
    rw [SModEq.sub_mem, sub_zero]
    have e : φ L - c = -φ (aeval a (nP (n + j)) - L) := by rw [map_sub, hφ]; abel
    rw [e]
    refine Submodule.neg_mem _ ?_
    exact map_mem_smul_top _ φ (hL j)
  exact sub_eq_zero.1 h

end IdemLiftAlt

open IdemLiftAlt in
/- English proof (translation)
Introduce `O A B _ _ _ _ _ _ _ _ f hf hnil e₁ e₂ h1 h2 h12 h21`. Use `set I := IsLocalRing.maximalIdeal O`. Set `K : Submodule O A` to `(RingHom.ker f).restrictScalars O`. Establish `hK : ∀ x, x ∈ K ↔ f x = 0` using `fun x => by simp [K, RingHom.mem_ker]`. Establish `hfa : ∀ (x : A) (k : ℕ), f (aeval x (nP k)) = aeval (f x) (nP k)`.

Introduce `x k`. Conclude with `(Polynomial.aeval_algHom_apply f.toIntAlgHom x (nP k)).symm`. Establish `hidem : ∀ (e : B), IsIdempotentElem e → ∀ k, aeval e (nP k) = e`. Introduce `e he k`. Proceed by induction on `k with`.

Consider the case `zero => simp [nP]`. Consider the case `succ k ih`. Establish `he2 : e ^ 2 = e` using `by rw [pow_two]; exact he`. Establish `he3 : e ^ 3 = e` using `by rw [pow_succ, he2]; exact he`. Simplify using `only [nP, map_sub, map_mul, map_pow, ih, map_ofNat]`.

Rewrite using `[he2, he3]`. Use `noncomm_ring`. Establish `lift : ∀ (a : A), IsIdempotentElem (f a) → ∃ n L, IsIdempotentElem L ∧ (∀ j : ℕ, aeval a (nP (n + j)) - L ∈ I ^ j • (⊤ : Submodule O A)) ∧ f L = f a`. Introduce `a ha`. Establish `hx : f (a ^ 2 - a) = 0`.

Rewrite using `[map_sub, map_pow, pow_two, ha, sub_self]`. Take `⟨n, hn⟩` from `hnil _ hx`. Take `⟨L, hLi, hL⟩` from `newton a n hn`. Use `⟨n, L, hLi, hL, ?_⟩` and prove the remaining obligations. Establish `hq` using `limit_map a L n hL K.mkQ (K.mkQ a) (fun k => by`.

Rewrite using `[Submodule.mkQ_apply, Submodule.mkQ_apply, Submodule.Quotient.eq, hK, map_sub, hfa, hidem _ ha, sub_self])`. Rewrite `hq` using `[Submodule.mkQ_apply, Submodule.mkQ_apply, Submodule.Quotient.eq, hK, map_sub, sub_eq_zero]`. Conclude with `hq`. Take `⟨a₁, rfl⟩` from `hf e₁`. Take `⟨n₁, E₁, hE₁, -, hfE₁⟩` from `lift a₁ h1`.

Take `⟨b, rfl⟩` from `hf e₂`. Use `set a₂ : A := (1 - E₁) * b * (1 - E₁) with ha₂`. Establish `hfa₂ : f a₂ = f b`. Rewrite using `[ha₂, map_mul, map_mul, map_sub, map_one, hfE₁]`. Establish `e : (1 - f a₁) * f b * (1 - f a₁) = f b - f a₁ * f b - f b * f a₁ + f a₁ * (f b * f a₁)` using `by noncomm_ring`.

Rewrite using `[e, h12, h21]`. Simplify using the standard rewrite rules. Take `⟨n₂, E₂, hE₂, hL₂, hfE₂⟩` from `lift a₂ (by rw [hfa₂]; exact h2)`. Establish `hE1c : E₁ * (1 - E₁) = 0` using `by rw [mul_sub, mul_one, hE₁.eq, sub_self]`. Establish `hE1c' : (1 - E₁) * E₁ = 0` using `by rw [sub_mul, one_mul, hE₁.eq, sub_self]`.

Establish `hl : E₁ * a₂ = 0` using `by rw [ha₂, ← mul_assoc, ← mul_assoc, hE1c]; simp`. Establish `hr : a₂ * E₁ = 0` using `by rw [ha₂, mul_assoc, hE1c']; simp`. Establish `hseq : ∀ k, E₁ * aeval a₂ (nP k) = 0 ∧ aeval a₂ (nP k) * E₁ = 0`. Introduce `k`. Take `⟨R, hR⟩` from `X_dvd_nP k`.

Establish `h' : aeval a₂ (nP k) = a₂ * aeval a₂ R` using `by rw [hR, map_mul, aeval_X]`. Establish `h'' : aeval a₂ (nP k) = aeval a₂ R * a₂` using `by rw [hR, mul_comm, map_mul, aeval_X]`. Prove the components needed by the constructor for the conclusion. Rewrite using `[h', ← mul_assoc, hl, zero_mul]`. Rewrite using `[h'', mul_assoc, hr, mul_zero]`.

Establish `h12' : E₁ * E₂ = 0` using `limit_map a₂ E₂ n₂ hL₂ (LinearMap.mulLeft O E₁) 0 (fun k => (hseq k).1)`. Establish `h21' : E₂ * E₁ = 0` using `limit_map a₂ E₂ n₂ hL₂ (LinearMap.mulRight O E₁) 0 (fun k => (hseq k).2)`. Conclude with `⟨E₁, E₂, hE₁, hE₂, h12', h21', hfE₁, by rw [hfE₂, hfa₂]⟩`.
-/
theorem idemLift : IdempotentLift := by
  intro O A B _ _ _ _ _ _ _ _ f hf hnil e₁ e₂ h1 h2 h12 h21
  set I := IsLocalRing.maximalIdeal O
  let K : Submodule O A := (RingHom.ker f).restrictScalars O
  have hK : ∀ x, x ∈ K ↔ f x = 0 := fun x => by simp [K, RingHom.mem_ker]
  have hfa : ∀ (x : A) (k : ℕ), f (aeval x (nP k)) = aeval (f x) (nP k) := by
    intro x k
    exact (Polynomial.aeval_algHom_apply f.toIntAlgHom x (nP k)).symm
  have hidem : ∀ (e : B), IsIdempotentElem e → ∀ k, aeval e (nP k) = e := by
    intro e he k
    induction k with
    | zero => simp [nP]
    | succ k ih =>
      have he2 : e ^ 2 = e := by rw [pow_two]; exact he
      have he3 : e ^ 3 = e := by rw [pow_succ, he2]; exact he
      simp only [nP, map_sub, map_mul, map_pow, ih, map_ofNat]
      rw [he2, he3]
      noncomm_ring
  have lift : ∀ (a : A), IsIdempotentElem (f a) → ∃ n L, IsIdempotentElem L ∧
      (∀ j : ℕ, aeval a (nP (n + j)) - L ∈ I ^ j • (⊤ : Submodule O A)) ∧ f L = f a := by
    intro a ha
    have hx : f (a ^ 2 - a) = 0 := by
      rw [map_sub, map_pow, pow_two, ha, sub_self]
    obtain ⟨n, hn⟩ := hnil _ hx
    obtain ⟨L, hLi, hL⟩ := newton a n hn
    refine ⟨n, L, hLi, hL, ?_⟩
    have hq := limit_map a L n hL K.mkQ (K.mkQ a) (fun k => by
      rw [Submodule.mkQ_apply, Submodule.mkQ_apply, Submodule.Quotient.eq, hK, map_sub, hfa,
        hidem _ ha, sub_self])
    rw [Submodule.mkQ_apply, Submodule.mkQ_apply, Submodule.Quotient.eq, hK, map_sub,
      sub_eq_zero] at hq
    exact hq
  obtain ⟨a₁, rfl⟩ := hf e₁
  obtain ⟨n₁, E₁, hE₁, -, hfE₁⟩ := lift a₁ h1
  obtain ⟨b, rfl⟩ := hf e₂
  set a₂ : A := (1 - E₁) * b * (1 - E₁) with ha₂
  have hfa₂ : f a₂ = f b := by
    rw [ha₂, map_mul, map_mul, map_sub, map_one, hfE₁]
    have e : (1 - f a₁) * f b * (1 - f a₁) =
        f b - f a₁ * f b - f b * f a₁ + f a₁ * (f b * f a₁) := by noncomm_ring
    rw [e, h12, h21]; simp
  obtain ⟨n₂, E₂, hE₂, hL₂, hfE₂⟩ := lift a₂ (by rw [hfa₂]; exact h2)
  have hE1c : E₁ * (1 - E₁) = 0 := by rw [mul_sub, mul_one, hE₁.eq, sub_self]
  have hE1c' : (1 - E₁) * E₁ = 0 := by rw [sub_mul, one_mul, hE₁.eq, sub_self]
  have hl : E₁ * a₂ = 0 := by rw [ha₂, ← mul_assoc, ← mul_assoc, hE1c]; simp
  have hr : a₂ * E₁ = 0 := by rw [ha₂, mul_assoc, hE1c']; simp
  have hseq : ∀ k, E₁ * aeval a₂ (nP k) = 0 ∧ aeval a₂ (nP k) * E₁ = 0 := by
    intro k
    obtain ⟨R, hR⟩ := X_dvd_nP k
    have h' : aeval a₂ (nP k) = a₂ * aeval a₂ R := by rw [hR, map_mul, aeval_X]
    have h'' : aeval a₂ (nP k) = aeval a₂ R * a₂ := by rw [hR, mul_comm, map_mul, aeval_X]
    constructor
    · rw [h', ← mul_assoc, hl, zero_mul]
    · rw [h'', mul_assoc, hr, mul_zero]
  have h12' : E₁ * E₂ = 0 :=
    limit_map a₂ E₂ n₂ hL₂ (LinearMap.mulLeft O E₁) 0 (fun k => (hseq k).1)
  have h21' : E₂ * E₁ = 0 :=
    limit_map a₂ E₂ n₂ hL₂ (LinearMap.mulRight O E₁) 0 (fun k => (hseq k).2)
  exact ⟨E₁, E₂, hE₁, hE₂, h12', h21', hfE₁, by rw [hfE₂, hfa₂]⟩

end Formalism.NG

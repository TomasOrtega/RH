import Mathlib
import Development.AutomorphicArithmetic.CommutativeAlgebra.EtaleCohomology.GoodRoot

noncomputable section
open IsLocalRing UpperTheory.Et

namespace UpperTheory.LineDecomposition

variable {A D : Type} [CommRing A] [CommRing D] [Algebra A D]

/- English proof (translation)
Rewrite using `[← mul_pow, T.ts, one_pow]`.
-/
private lemma tsPow (T : TC A D) (i : ℕ) : T.t ^ i * T.s ^ i = 1 := by
  rw [← mul_pow, T.ts, one_pow]

/- English proof (translation)
Unfold both sides. The equivalence is reflexive.
-/
private lemma memS (T : TC A D) {j : ℕ} {x : D} : x ∈ T.S j ↔ x ∈ T.B ∧ T.s ^ j * x ∈ T.C :=
  Iff.rfl

/- English proof (translation)
Take `⟨k, hk⟩` from `T.locB x`. Use `⟨k, fun m hm => ?_⟩` and prove the remaining obligations. Establish `e : T.t ^ m * x = T.t ^ (m - k) * (T.t ^ k * x)`. Rewrite using `[← mul_assoc, ← pow_add, Nat.sub_add_cancel hm]`. Rewrite using `[e]`.

Conclude with `T.B.mul_mem (T.B.pow_mem T.tB _) hk`.
-/
private lemma evB (T : TC A D) (x : D) : ∃ k : ℕ, ∀ m ≥ k, T.t ^ m * x ∈ T.B := by
  obtain ⟨k, hk⟩ := T.locB x
  refine ⟨k, fun m hm => ?_⟩
  have e : T.t ^ m * x = T.t ^ (m - k) * (T.t ^ k * x) := by
    rw [← mul_assoc, ← pow_add, Nat.sub_add_cancel hm]
  rw [e]
  exact T.B.mul_mem (T.B.pow_mem T.tB _) hk

/- English proof (translation)
Take `⟨k, hk⟩` from `T.locC x`. Use `⟨k, fun m hm => ?_⟩` and prove the remaining obligations. Establish `e : T.s ^ m * x = T.s ^ (m - k) * (T.s ^ k * x)`. Rewrite using `[← mul_assoc, ← pow_add, Nat.sub_add_cancel hm]`. Rewrite using `[e]`.

Conclude with `T.C.mul_mem (T.C.pow_mem T.sC _) hk`.
-/
private lemma evC (T : TC A D) (x : D) : ∃ k : ℕ, ∀ m ≥ k, T.s ^ m * x ∈ T.C := by
  obtain ⟨k, hk⟩ := T.locC x
  refine ⟨k, fun m hm => ?_⟩
  have e : T.s ^ m * x = T.s ^ (m - k) * (T.s ^ k * x) := by
    rw [← mul_assoc, ← pow_add, Nat.sub_add_cancel hm]
  rw [e]
  exact T.C.mul_mem (T.C.pow_mem T.sC _) hk

/- English proof (translation)
Use `choose k hk using fun z => evC T z`. Conclude with `⟨F.sup k, fun m hm z hz => hk z m (le_trans (Finset.le_sup hz) hm)⟩`.
-/
private lemma evCfin (T : TC A D) (F : Finset D) :
    ∃ k : ℕ, ∀ m ≥ k, ∀ z ∈ F, T.s ^ m * z ∈ T.C := by
  choose k hk using fun z => evC T z
  exact ⟨F.sup k, fun m hm z hz => hk z m (le_trans (Finset.le_sup hz) hm)⟩

private def NN (T : TC A D) (X : Finset D) : Submodule A D :=
  Submodule.span A {y | ∃ x ∈ X, ∃ j : ℕ, y = T.s ^ j * x}

/- English proof (translation)
Unfold `NN at hn`. Proceed by induction on `hn using Submodule.span_induction with`. Consider the case `mem y hy`. Take `⟨x, hx, j, rfl⟩` from `hy`. Establish `h` using `T.C.mul_mem (T.C.pow_mem T.sC j) (hu x hx)`.

Use `h using 1` and compare the differences between its conclusion and the goal. Expand and normalize the polynomial expressions, which then agree. Consider the case `zero`. Rewrite using `[mul_zero]`. Conclude with `T.C.zero_mem`.

Consider the case `add y z _ _ hy hz`. Rewrite using `[mul_add]`. Conclude with `T.C.add_mem hy hz`. Consider the case `smul a y _ hy`. Rewrite using `[mul_smul_comm]`.

Conclude with `T.C.smul_mem hy a`.
-/
private lemma NN_mul (T : TC A D) (X : Finset D) {u : D} (hu : ∀ x ∈ X, u * x ∈ T.C)
    {n : D} (hn : n ∈ NN T X) : u * n ∈ T.C := by
  unfold NN at hn
  induction hn using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨x, hx, j, rfl⟩ := hy
    have h := T.C.mul_mem (T.C.pow_mem T.sC j) (hu x hx)
    convert h using 1
    ring
  | zero =>
    rw [mul_zero]
    exact T.C.zero_mem
  | add y z _ _ hy hz =>
    rw [mul_add]
    exact T.C.add_mem hy hz
  | smul a y _ hy =>
    rw [mul_smul_comm]
    exact T.C.smul_mem hy a

/- English proof (translation)
Take `⟨k, hk⟩` from `T.locB y`. Establish `key : ∀ z ∈ Submodule.span A {y | ∃ x ∈ X, ∃ i : ℕ, y = T.t ^ i * x}, T.s ^ k * z ∈ Subalgebra.toSubmodule T.B ⊔ NN T X`. Introduce `z hz`. Proceed by induction on `hz using Submodule.span_induction with`. Consider the case `mem w hw`.

Take `⟨x, hx, i, rfl⟩` from `hw`. Break down `le_or_gt k i with hki | hki` into its components or cases. Take `⟨d, rfl⟩` from `Nat.exists_eq_add_of_le hki`. Apply `Submodule.mem_sup_left` to reduce the goal to its premises. Establish `e : T.s ^ k * (T.t ^ (k + d) * x) = T.t ^ d * x`.

Take the linear combination `(T.t ^ d * x) * tsPow T k`. Rewrite using `[e]`. Conclude with `T.B.mul_mem (T.B.pow_mem T.tB d) (hXB x hx)`. Take `⟨d, rfl⟩` from `Nat.exists_eq_add_of_lt hki`. Apply `Submodule.mem_sup_right` to reduce the goal to its premises.

Establish `e : T.s ^ (i + d + 1) * (T.t ^ i * x) = T.s ^ (d + 1) * x`. Take the linear combination `(T.s ^ (d + 1) * x) * tsPow T i`. Rewrite using `[e]`. Conclude with `Submodule.subset_span ⟨x, hx, d + 1, rfl⟩`. Consider the case `zero`.

Rewrite using `[mul_zero]`. Conclude with `Submodule.zero_mem _`. Consider the case `add a b _ _ ha hb`. Rewrite using `[mul_add]`. Conclude with `Submodule.add_mem _ ha hb`.

Consider the case `smul r a _ ha`. Rewrite using `[mul_smul_comm]`. Conclude with `Submodule.smul_mem _ r ha`. Establish `hy` using `key _ (hX _ hk)`. Establish `e : T.s ^ k * (T.t ^ k * y) = y`.

Take the linear combination `y * tsPow T k`. Rewrite `hy` using `[e]`. Take `⟨b, hb, n, hn, hbn⟩` from `Submodule.mem_sup.mp hy`. Conclude with `⟨b, hb, n, hn, hbn.symm⟩`.
-/
private lemma split (T : TC A D) (X : Finset D) (hXB : ∀ x ∈ X, x ∈ T.B)
    (hX : ∀ b ∈ T.B, b ∈ Submodule.span A {y | ∃ x ∈ X, ∃ i : ℕ, y = T.t ^ i * x})
    (y : D) : ∃ b ∈ T.B, ∃ n ∈ NN T X, y = b + n := by
  obtain ⟨k, hk⟩ := T.locB y
  have key : ∀ z ∈ Submodule.span A {y | ∃ x ∈ X, ∃ i : ℕ, y = T.t ^ i * x},
      T.s ^ k * z ∈ Subalgebra.toSubmodule T.B ⊔ NN T X := by
    intro z hz
    induction hz using Submodule.span_induction with
    | mem w hw =>
      obtain ⟨x, hx, i, rfl⟩ := hw
      rcases le_or_gt k i with hki | hki
      · obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hki
        apply Submodule.mem_sup_left
        have e : T.s ^ k * (T.t ^ (k + d) * x) = T.t ^ d * x := by
          linear_combination (T.t ^ d * x) * tsPow T k
        rw [e]
        exact T.B.mul_mem (T.B.pow_mem T.tB d) (hXB x hx)
      · obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_lt hki
        apply Submodule.mem_sup_right
        have e : T.s ^ (i + d + 1) * (T.t ^ i * x) = T.s ^ (d + 1) * x := by
          linear_combination (T.s ^ (d + 1) * x) * tsPow T i
        rw [e]
        exact Submodule.subset_span ⟨x, hx, d + 1, rfl⟩
    | zero =>
      rw [mul_zero]
      exact Submodule.zero_mem _
    | add a b _ _ ha hb =>
      rw [mul_add]
      exact Submodule.add_mem _ ha hb
    | smul r a _ ha =>
      rw [mul_smul_comm]
      exact Submodule.smul_mem _ r ha
  have hy := key _ (hX _ hk)
  have e : T.s ^ k * (T.t ^ k * y) = y := by
    linear_combination y * tsPow T k
  rw [e] at hy
  obtain ⟨b, hb, n, hn, hbn⟩ := Submodule.mem_sup.mp hy
  exact ⟨b, hb, n, hn, hbn.symm⟩

/- English proof (translation)
Take `⟨b₀, hb₀, n₀, hn₀, hz⟩` from `split T X hXB hX (ω * T.t ^ m * y)`. Take `⟨b₂, hb₂, n₂, hn₂, hq⟩` from `split T X hXB hX (η * T.s ^ m * b₀)`. Establish `hts` using `tsPow T m`. Use `⟨b₂, hb₂, η * T.s ^ m * n₀, NN_mul T X h4 hn₀, n₂, ?_, ?_, NN_mul T X h3 hn₂⟩` and prove the remaining obligations. Take the linear combination `hq + η * T.s ^ m * hz - T.t ^ m * T.s ^ m * y * hηω - y * hts`.

Establish `e : ω * T.t ^ m * n₂ = b₀ - ω * T.t ^ m * b₂`. Take the linear combination `(-(ω * T.t ^ m)) * hq + b₀ * T.t ^ m * T.s ^ m * hηω + b₀ * hts`. Rewrite using `[e]`. Conclude with `T.B.sub_mem hb₀ (T.B.mul_mem h1 hb₂)`.
-/
private lemma decomp (T : TC A D) (X : Finset D) (hXB : ∀ x ∈ X, x ∈ T.B)
    (hX : ∀ b ∈ T.B, b ∈ Submodule.span A {y | ∃ x ∈ X, ∃ i : ℕ, y = T.t ^ i * x})
    {ω η : D} (hηω : η * ω = 1) {m : ℕ} (h1 : ω * T.t ^ m ∈ T.B)
    (h3 : ∀ x ∈ X, ω * T.s ^ m * x ∈ T.C) (h4 : ∀ x ∈ X, η * T.s ^ m * x ∈ T.C) (y : D) :
    ∃ b ∈ T.B, ∃ c' ∈ T.C, ∃ p' : D, y = b + c' + p' ∧ ω * T.t ^ m * p' ∈ T.B ∧
      ω * T.s ^ m * p' ∈ T.C := by
  obtain ⟨b₀, hb₀, n₀, hn₀, hz⟩ := split T X hXB hX (ω * T.t ^ m * y)
  obtain ⟨b₂, hb₂, n₂, hn₂, hq⟩ := split T X hXB hX (η * T.s ^ m * b₀)
  have hts := tsPow T m
  refine ⟨b₂, hb₂, η * T.s ^ m * n₀, NN_mul T X h4 hn₀, n₂, ?_, ?_, NN_mul T X h3 hn₂⟩
  · linear_combination hq + η * T.s ^ m * hz - T.t ^ m * T.s ^ m * y * hηω - y * hts
  · have e : ω * T.t ^ m * n₂ = b₀ - ω * T.t ^ m * b₂ := by
      linear_combination (-(ω * T.t ^ m)) * hq + b₀ * T.t ^ m * T.s ^ m * hηω + b₀ * hts
    rw [e]
    exact T.B.sub_mem hb₀ (T.B.mul_mem h1 hb₂)

end UpperTheory.LineDecomposition

open UpperTheory.LineDecomposition in
/- English proof (translation)
Introduce `A D _ _ _ T hF q hq hq0 ω hω`. Take `⟨X, hXB, hX⟩` from `hF`. Establish `hηω : ω ^ (q - 1) * ω = 1`. Rewrite using `[← pow_succ, Nat.sub_add_cancel hq0, hω]`. Take `⟨k₁, hk₁⟩` from `evB T ω`.

Take `⟨k₂, hk₂⟩` from `evC T ω`. Take `⟨k₃, hk₃⟩` from `evCfin T (X.image (fun x => ω * x))`. Take `⟨k₄, hk₄⟩` from `evCfin T (X.image (fun x => ω ^ (q - 1) * x))`. Take `⟨r, hr⟩` from `hq.exists_left_inv`. Use `⟨max (max k₁ k₂) (max k₃ k₄), fun m hm => ?_⟩` and prove the remaining obligations.

Establish `hm₁ : k₁ ≤ m` using `le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hm`. Establish `hm₂ : k₂ ≤ m` using `le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hm`. Establish `hm₃ : k₃ ≤ m` using `le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hm`. Establish `hm₄ : k₄ ≤ m` using `le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hm`. Establish `hB : ω * T.t ^ m ∈ T.B`.

Rewrite using `[mul_comm]`. Conclude with `hk₁ m hm₁`. Establish `hC : ω * T.s ^ m ∈ T.C`. Rewrite using `[mul_comm]`. Conclude with `hk₂ m hm₂`.

Establish `h3 : ∀ x ∈ X, ω * T.s ^ m * x ∈ T.C` using `fun x hx => by`. Establish `h` using `hk₃ m hm₃ (ω * x) (Finset.mem_image_of_mem _ hx)`. Use `h using 1` and compare the differences between its conclusion and the goal. Expand and normalize the polynomial expressions, which then agree. Establish `h4 : ∀ x ∈ X, ω ^ (q - 1) * T.s ^ m * x ∈ T.C` using `fun x hx => by`.

Establish `h` using `hk₄ m hm₄ (ω ^ (q - 1) * x) (Finset.mem_image_of_mem _ hx)`. Use `h using 1` and compare the differences between its conclusion and the goal. Expand and normalize the polynomial expressions, which then agree. Establish `hts` using `tsPow T m`. Establish `hu : ω * T.t ^ m ∈ T.S (2 * m)`.

Rewrite using `[memS]`. Use `⟨hB, ?_⟩` and prove the remaining obligations. Establish `e : T.s ^ (2 * m) * (ω * T.t ^ m) = ω * T.s ^ m`. Rewrite using `[two_mul, pow_add]`. Take the linear combination `ω * T.s ^ m * hts`.

Rewrite using `[e]`. Conclude with `hC`. Use `⟨hu, fun σ hσ => ?_⟩` and prove the remaining obligations. Rewrite `hσ` using `[memS]`. Take `⟨b₁, hb₁, c₁, hc₁, p₁, hy, hp1, hp2⟩` from `decomp T X hXB hX hηω hB h3 h4 (T.s ^ (q * m) * σ)`.

Establish `hqm` using `tsPow T (q * m)`. Establish `hupow : (ω * T.t ^ m) ^ q = T.t ^ (q * m)`. Rewrite using `[mul_pow, hω, one_mul, ← pow_mul, Nat.mul_comm]`. Establish `hspow : (ω * T.s ^ m) ^ q = T.s ^ (q * m)`. Rewrite using `[mul_pow, hω, one_mul, ← pow_mul, Nat.mul_comm]`.

Establish `hup : (ω * T.t ^ m) ^ (q - 1) * (ω * T.t ^ m * p₁) = T.t ^ (q * m) * p₁`. Rewrite using `[← mul_assoc, pow_sub_one_mul hq0.ne', hupow]`. Establish `hsp : (ω * T.s ^ m) ^ (q - 1) * (ω * T.s ^ m * p₁) = T.s ^ (q * m) * p₁`. Rewrite using `[← mul_assoc, pow_sub_one_mul hq0.ne', hspow]`. Establish `ha : T.t ^ (q * m) * c₁ ∈ T.S (q * m)`.

Rewrite using `[memS]`. Prove the components needed by the constructor for the conclusion. Establish `ea : T.t ^ (q * m) * c₁ = σ - T.t ^ (q * m) * b₁ - (ω * T.t ^ m) ^ (q - 1) * (ω * T.t ^ m * p₁)`. Rewrite using `[hup]`. Take the linear combination `(-T.t ^ (q * m)) * hy + σ * hqm`.

Rewrite using `[ea]`. Conclude with `T.B.sub_mem (T.B.sub_mem hσ.1 (T.B.mul_mem (T.B.pow_mem T.tB _) hb₁)) (T.B.mul_mem (T.B.pow_mem hB _) hp1)`. Establish `ec : T.s ^ (q * m) * (T.t ^ (q * m) * c₁) = c₁`. Take the linear combination `c₁ * hqm`. Rewrite using `[ec]`.

Conclude with `hc₁`. Establish `hb : b₁ ∈ T.S (q * m)`. Rewrite using `[memS]`. Use `⟨hb₁, ?_⟩` and prove the remaining obligations. Establish `eb : T.s ^ (q * m) * b₁ = T.s ^ (2 * q * m) * σ - T.s ^ (q * m) * c₁ - (ω * T.s ^ m) ^ (q - 1) * (ω * T.s ^ m * p₁)`.

Rewrite using `[hsp, show 2 * q * m = q * m + q * m by ring, pow_add]`. Take the linear combination `(-T.s ^ (q * m)) * hy`. Rewrite using `[eb]`. Conclude with `T.C.sub_mem (T.C.sub_mem hσ.2 (T.C.mul_mem (T.C.pow_mem T.sC _) hc₁)) (T.C.mul_mem (T.C.pow_mem hC _) hp2)`. Establish `hpS : ω * T.t ^ m * p₁ ∈ T.S (2 * m)`.

Rewrite using `[memS]`. Use `⟨hp1, ?_⟩` and prove the remaining obligations. Establish `e : T.s ^ (2 * m) * (ω * T.t ^ m * p₁) = ω * T.s ^ m * p₁`. Rewrite using `[two_mul, pow_add]`. Take the linear combination `(ω * T.s ^ m * p₁) * hts`.

Rewrite using `[e]`. Conclude with `hp2`. Use `⟨T.t ^ (q * m) * c₁, ha, b₁, hb, -(r • (ω * T.t ^ m * p₁)), Submodule.neg_mem _ (Submodule.smul_mem _ r hpS), ?_⟩` and prove the remaining obligations. Establish `hrq : algebraMap A D r * (q : D) = 1`. Rewrite using `[← map_natCast (algebraMap A D), ← map_mul, hr, map_one]`.

Rewrite using `[Algebra.smul_def]`. Take the linear combination `(-(q : D) * algebraMap A D r) * hup - T.t ^ (q * m) * p₁ * hrq + T.t ^ (q * m) * hy - σ * hqm`.
-/
theorem UpperTheory.exists_power_decomposition_of_root_of_unity :
    ∀ (A D : Type) [CommRing A] [CommRing D] [Algebra A D] (T : TC A D), T.Fin → ∀ (q : ℕ), IsUnit (q : A) → 0 < q → ∀ ω : D, ω ^ q = 1 → ∃ m₀ : ℕ, ∀ m ≥ m₀, ω * T.t ^ m ∈ T.S (2 * m) ∧
      ∀ σ ∈ T.S (2 * q * m), ∃ a ∈ T.S (q * m), ∃ b ∈ T.S (q * m), ∃ c ∈ T.S (2 * m), σ = a + T.t ^ (q * m) * b - (q : D) * (ω * T.t ^ m) ^ (q - 1) * c := by
  classical
  intro A D _ _ _ T hF q hq hq0 ω hω
  obtain ⟨X, hXB, hX⟩ := hF
  have hηω : ω ^ (q - 1) * ω = 1 := by
    rw [← pow_succ, Nat.sub_add_cancel hq0, hω]
  obtain ⟨k₁, hk₁⟩ := evB T ω
  obtain ⟨k₂, hk₂⟩ := evC T ω
  obtain ⟨k₃, hk₃⟩ := evCfin T (X.image (fun x => ω * x))
  obtain ⟨k₄, hk₄⟩ := evCfin T (X.image (fun x => ω ^ (q - 1) * x))
  obtain ⟨r, hr⟩ := hq.exists_left_inv
  refine ⟨max (max k₁ k₂) (max k₃ k₄), fun m hm => ?_⟩
  have hm₁ : k₁ ≤ m := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hm
  have hm₂ : k₂ ≤ m := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hm
  have hm₃ : k₃ ≤ m := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hm
  have hm₄ : k₄ ≤ m := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hm
  have hB : ω * T.t ^ m ∈ T.B := by
    rw [mul_comm]
    exact hk₁ m hm₁
  have hC : ω * T.s ^ m ∈ T.C := by
    rw [mul_comm]
    exact hk₂ m hm₂
  have h3 : ∀ x ∈ X, ω * T.s ^ m * x ∈ T.C := fun x hx => by
    have h := hk₃ m hm₃ (ω * x) (Finset.mem_image_of_mem _ hx)
    convert h using 1
    ring
  have h4 : ∀ x ∈ X, ω ^ (q - 1) * T.s ^ m * x ∈ T.C := fun x hx => by
    have h := hk₄ m hm₄ (ω ^ (q - 1) * x) (Finset.mem_image_of_mem _ hx)
    convert h using 1
    ring
  have hts := tsPow T m
  have hu : ω * T.t ^ m ∈ T.S (2 * m) := by
    rw [memS]
    refine ⟨hB, ?_⟩
    have e : T.s ^ (2 * m) * (ω * T.t ^ m) = ω * T.s ^ m := by
      rw [two_mul, pow_add]
      linear_combination ω * T.s ^ m * hts
    rw [e]
    exact hC
  refine ⟨hu, fun σ hσ => ?_⟩
  rw [memS] at hσ
  obtain ⟨b₁, hb₁, c₁, hc₁, p₁, hy, hp1, hp2⟩ :=
    decomp T X hXB hX hηω hB h3 h4 (T.s ^ (q * m) * σ)
  have hqm := tsPow T (q * m)
  have hupow : (ω * T.t ^ m) ^ q = T.t ^ (q * m) := by
    rw [mul_pow, hω, one_mul, ← pow_mul, Nat.mul_comm]
  have hspow : (ω * T.s ^ m) ^ q = T.s ^ (q * m) := by
    rw [mul_pow, hω, one_mul, ← pow_mul, Nat.mul_comm]
  have hup : (ω * T.t ^ m) ^ (q - 1) * (ω * T.t ^ m * p₁) = T.t ^ (q * m) * p₁ := by
    rw [← mul_assoc, pow_sub_one_mul hq0.ne', hupow]
  have hsp : (ω * T.s ^ m) ^ (q - 1) * (ω * T.s ^ m * p₁) = T.s ^ (q * m) * p₁ := by
    rw [← mul_assoc, pow_sub_one_mul hq0.ne', hspow]
  have ha : T.t ^ (q * m) * c₁ ∈ T.S (q * m) := by
    rw [memS]
    constructor
    · have ea : T.t ^ (q * m) * c₁ =
          σ - T.t ^ (q * m) * b₁ - (ω * T.t ^ m) ^ (q - 1) * (ω * T.t ^ m * p₁) := by
        rw [hup]
        linear_combination (-T.t ^ (q * m)) * hy + σ * hqm
      rw [ea]
      exact T.B.sub_mem (T.B.sub_mem hσ.1 (T.B.mul_mem (T.B.pow_mem T.tB _) hb₁))
        (T.B.mul_mem (T.B.pow_mem hB _) hp1)
    · have ec : T.s ^ (q * m) * (T.t ^ (q * m) * c₁) = c₁ := by
        linear_combination c₁ * hqm
      rw [ec]
      exact hc₁
  have hb : b₁ ∈ T.S (q * m) := by
    rw [memS]
    refine ⟨hb₁, ?_⟩
    have eb : T.s ^ (q * m) * b₁ =
        T.s ^ (2 * q * m) * σ - T.s ^ (q * m) * c₁ - (ω * T.s ^ m) ^ (q - 1) * (ω * T.s ^ m * p₁) := by
      rw [hsp, show 2 * q * m = q * m + q * m by ring, pow_add]
      linear_combination (-T.s ^ (q * m)) * hy
    rw [eb]
    exact T.C.sub_mem (T.C.sub_mem hσ.2 (T.C.mul_mem (T.C.pow_mem T.sC _) hc₁))
      (T.C.mul_mem (T.C.pow_mem hC _) hp2)
  have hpS : ω * T.t ^ m * p₁ ∈ T.S (2 * m) := by
    rw [memS]
    refine ⟨hp1, ?_⟩
    have e : T.s ^ (2 * m) * (ω * T.t ^ m * p₁) = ω * T.s ^ m * p₁ := by
      rw [two_mul, pow_add]
      linear_combination (ω * T.s ^ m * p₁) * hts
    rw [e]
    exact hp2
  refine ⟨T.t ^ (q * m) * c₁, ha, b₁, hb, -(r • (ω * T.t ^ m * p₁)),
    Submodule.neg_mem _ (Submodule.smul_mem _ r hpS), ?_⟩
  have hrq : algebraMap A D r * (q : D) = 1 := by
    rw [← map_natCast (algebraMap A D), ← map_mul, hr, map_one]
  rw [Algebra.smul_def]
  linear_combination (-(q : D) * algebraMap A D r) * hup - T.t ^ (q * m) * p₁ * hrq +
    T.t ^ (q * m) * hy - σ * hqm

end

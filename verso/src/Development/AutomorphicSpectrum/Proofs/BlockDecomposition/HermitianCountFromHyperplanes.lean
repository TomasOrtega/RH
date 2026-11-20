import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MemRiemannRochSpaceIffRegularAtEverywhere
open Matrix Classical PositivityTheory.Rg.Rs GlobalTheory.CompanionTheory.GLFirstBasisOrbit

namespace GlobalTheory.CompanionTheory.GapOpLower

open Finset

/- English proof (translation)
Simplify using `only [map_sum, LinearMap.sum_apply, Complex.re_sum]`. Rewrite using `[Finset.sum_comm]`.
-/
theorem re_sesq_sum {V ι : Type} [AddCommGroup V] [Module ℂ V] (B : V →ₗ[ℂ] V →ₗ⋆[ℂ] ℂ)
    (s t : Finset ι) (f : ι → V) :
    (B (∑ a ∈ s, f a) (∑ b ∈ t, f b)).re = ∑ a ∈ s, ∑ b ∈ t, (B (f a) (f b)).re := by
  simp only [map_sum, LinearMap.sum_apply, Complex.re_sum]
  rw [Finset.sum_comm]

/- English proof (translation)
Establish `h` using `Finset.card_filter_add_card_filter_not (s := (univ : Finset α)) (fun a => a ≠ 0)`. Establish `h0 : ((univ : Finset α).filter (fun a => ¬ a ≠ 0)).card = 1`. Establish `: (univ : Finset α).filter (fun a => ¬ a ≠ 0) = {0}`. Use extensionality with `a`. Simplify using the standard rewrite rules.

Rewrite using `[this, card_singleton]`. Rewrite `h` using `[h0, card_univ]`. Rewrite using `[← h]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem card_filter_ne_zero {α : Type} [Fintype α] [Zero α] :
    (((univ : Finset α).filter (fun a => a ≠ 0)).card : ℝ) = (Fintype.card α : ℝ) - 1 := by
  have h := Finset.card_filter_add_card_filter_not (s := (univ : Finset α)) (fun a => a ≠ 0)
  have h0 : ((univ : Finset α).filter (fun a => ¬ a ≠ 0)).card = 1 := by
    have : (univ : Finset α).filter (fun a => ¬ a ≠ 0) = {0} := by
      ext a; simp
    rw [this, card_singleton]
  rw [h0, card_univ] at h
  rw [← h]; push_cast; ring

/- English proof (translation)
Establish `hinj : Function.Injective (fun s : k => s • a)` using `smul_left_injective k ha`. Rewrite using `[← Finset.sum_image (f := D) (g := fun s : k => s • a) hinj.injOn]`. Use `symm`. Use `Finset.sum_subset ?_ ?_` and prove the remaining obligations. Introduce `b hb`.

Take `⟨s, hs, rfl⟩` from `Finset.mem_image.mp hb`. Simplify using `only [mem_filter, mem_univ, true_and] at hs ⊢`. Conclude with `smul_ne_zero hs ha`. Introduce `b hb hb'`. Use `hD b ?_` and prove the remaining obligations.

Introduce `s hs`. Apply `hb'` to reduce the goal to its premises. Use `Finset.mem_image.mpr ⟨s, ?_, hs.symm⟩` and prove the remaining obligations. Simplify using `only [mem_filter, mem_univ, true_and] at hb ⊢`. Introduce and unpack `rfl`.

Conclude with `hb (by simpa using hs)`.
-/
theorem sum_line {k : Type} [Field k] [Fintype k] {n : ℕ} (a : Fin (n + 1) → k) (ha : a ≠ 0)
    (D : (Fin (n + 1) → k) → ℝ) (hD : ∀ b, (∀ s : k, b ≠ s • a) → D b = 0) :
    ∑ b ∈ (univ : Finset (Fin (n + 1) → k)).filter (fun b => b ≠ 0), D b
      = ∑ s ∈ (univ : Finset k).filter (fun s => s ≠ 0), D (s • a) := by
  have hinj : Function.Injective (fun s : k => s • a) := smul_left_injective k ha
  rw [← Finset.sum_image (f := D) (g := fun s : k => s • a) hinj.injOn]
  symm
  refine Finset.sum_subset ?_ ?_
  · intro b hb
    obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp hb
    simp only [mem_filter, mem_univ, true_and] at hs ⊢
    exact smul_ne_zero hs ha
  · intro b hb hb'
    refine hD b ?_
    intro s hs
    apply hb'
    refine Finset.mem_image.mpr ⟨s, ?_, hs.symm⟩
    simp only [mem_filter, mem_univ, true_and] at hb ⊢
    rintro rfl
    exact hb (by simpa using hs)

/- English proof (translation)
Use `set q : ℝ := (Fintype.card k : ℝ) with hq`. Establish `hZ : ∑ b, N b * R b = ∑ b ∈ (univ : Finset (Fin (n + 1) → k)).filter (fun b => b ≠ 0), N b * R b`. Use `symm`. Use `Finset.sum_subset (filter_subset _ _) ?_` and prove the remaining obligations. Introduce `b _ hb`.

Establish `: b = 0` using `by simpa using hb`. Simplify using `[this, hN0]`. Establish `hD` using `sum_line a ha (fun b => (q * N b - q ^ n) * R b) (fun b hb => by show (q * N b - q ^ n) * R b = 0; rw [hNo b hb]; ring)`. Establish `hterm : ∀ s ∈ (univ : Finset k).filter (fun s => s ≠ 0), (q * N (s • a) - q ^ n) * R (s • a) = (if s = 1 then q ^ (n + 1) * c else 0) - q ^ n * c`. Introduce `s hs`.

Establish `s0 : s ≠ 0` using `by simpa using hs`. Rewrite using `[hR s s0]`. Distinguish the cases in `h : s = 1`. Substitute `h` using the available equality. Rewrite using `[one_smul, hNa]`.

Simplify using the standard rewrite rules. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[hNs s h]`. Simplify using `[h]`. Establish `h1mem : (1 : k) ∈ (univ : Finset k).filter (fun s => s ≠ 0)` using `by simp`.

Rewrite `hD` using `[Finset.sum_congr rfl hterm, Finset.sum_sub_distrib, Finset.sum_ite_eq', if_pos h1mem, Finset.sum_const, nsmul_eq_mul, card_filter_ne_zero]`. Establish `hsplit : q * ∑ b ∈ (univ : Finset (Fin (n + 1) → k)).filter (fun b => b ≠ 0), N b * R b = q ^ n * ∑ b ∈ (univ : Finset (Fin (n + 1) → k)).filter (fun b => b ≠ 0), R b + ∑ b ∈ (univ : Finset (Fin (n + 1) → k)).filter (fun b => b ≠ 0), (q * N b - q ^ n) * R b`. Rewrite using `[Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]`. Use `Finset.sum_congr rfl fun b _ => ?_` and prove the remaining obligations. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[hZ, hsplit, hD]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem row_identity {k : Type} [Field k] [Fintype k] {n : ℕ} (a : Fin (n + 1) → k) (ha : a ≠ 0)
    (N R : (Fin (n + 1) → k) → ℝ) (c : ℝ)
    (hN0 : N 0 = 0)
    (hNa : (Fintype.card k : ℝ) * N a = (Fintype.card k : ℝ) ^ (n + 1))
    (hNs : ∀ s : k, s ≠ 1 → N (s • a) = 0)
    (hNo : ∀ b, (∀ s : k, b ≠ s • a) → (Fintype.card k : ℝ) * N b = (Fintype.card k : ℝ) ^ n)
    (hR : ∀ s : k, s ≠ 0 → R (s • a) = c) :
    (Fintype.card k : ℝ) * ∑ b, N b * R b
      = (Fintype.card k : ℝ) ^ n *
          ∑ b ∈ (univ : Finset (Fin (n + 1) → k)).filter (fun b => b ≠ 0), R b
        + (Fintype.card k : ℝ) ^ n * c := by
  set q : ℝ := (Fintype.card k : ℝ) with hq
  have hZ : ∑ b, N b * R b
      = ∑ b ∈ (univ : Finset (Fin (n + 1) → k)).filter (fun b => b ≠ 0), N b * R b := by
    symm
    refine Finset.sum_subset (filter_subset _ _) ?_
    intro b _ hb
    have : b = 0 := by simpa using hb
    simp [this, hN0]
  have hD := sum_line a ha (fun b => (q * N b - q ^ n) * R b)
    (fun b hb => by show (q * N b - q ^ n) * R b = 0; rw [hNo b hb]; ring)
  have hterm : ∀ s ∈ (univ : Finset k).filter (fun s => s ≠ 0),
      (q * N (s • a) - q ^ n) * R (s • a) = (if s = 1 then q ^ (n + 1) * c else 0) - q ^ n * c := by
    intro s hs
    have s0 : s ≠ 0 := by simpa using hs
    rw [hR s s0]
    by_cases h : s = 1
    · subst h
      rw [one_smul, hNa]; simp; ring
    · rw [hNs s h]; simp [h]
  have h1mem : (1 : k) ∈ (univ : Finset k).filter (fun s => s ≠ 0) := by simp
  rw [Finset.sum_congr rfl hterm, Finset.sum_sub_distrib, Finset.sum_ite_eq', if_pos h1mem,
    Finset.sum_const, nsmul_eq_mul, card_filter_ne_zero] at hD
  have hsplit : q * ∑ b ∈ (univ : Finset (Fin (n + 1) → k)).filter (fun b => b ≠ 0), N b * R b
      = q ^ n * ∑ b ∈ (univ : Finset (Fin (n + 1) → k)).filter (fun b => b ≠ 0), R b
        + ∑ b ∈ (univ : Finset (Fin (n + 1) → k)).filter (fun b => b ≠ 0),
            (q * N b - q ^ n) * R b := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun b _ => ?_
    ring
  rw [hZ, hsplit, hD]
  ring

/- English proof (translation)
Combine the equalities or inequalities in the displayed calculation. Use `Finset.sum_congr rfl fun x _ => ?_` and prove the remaining obligations. Rewrite using `[Finset.sum_filter]`. Use `Finset.sum_congr rfl fun a _ => ?_` and prove the remaining obligations. Distinguish the cases in `ha : a ⬝ᵥ x = 1`.

Simplify using `[ha, Finset.sum_filter]`. Simplify using `[ha]`. Use `_ = ∑ a, ∑ x : Fin (n + 1) → k, ∑ b, if (a ⬝ᵥ x = 1 ∧ b ⬝ᵥ x = 1) then R a b else 0 := Finset.sum_comm`. Use `_ = ∑ a, ∑ b, ∑ x : Fin (n + 1) → k, if (a ⬝ᵥ x = 1 ∧ b ⬝ᵥ x = 1) then R a b else 0 := Finset.sum_congr rfl fun a _ => Finset.sum_comm`. Use `_ = _ := by`.

Use `Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_` and prove the remaining obligations. Rewrite using `[← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]`.
-/
theorem sum_expand {k : Type} [Field k] [Fintype k] {n : ℕ}
    (R : (Fin (n + 1) → k) → (Fin (n + 1) → k) → ℝ) :
    ∑ x : Fin (n + 1) → k,
      ∑ a ∈ univ.filter (fun a : Fin (n + 1) → k => a ⬝ᵥ x = 1),
        ∑ b ∈ univ.filter (fun a : Fin (n + 1) → k => a ⬝ᵥ x = 1), R a b
      = ∑ a, ∑ b, ((univ.filter (fun x : Fin (n + 1) → k => a ⬝ᵥ x = 1 ∧ b ⬝ᵥ x = 1)).card : ℝ)
          * R a b := by
  calc ∑ x : Fin (n + 1) → k,
      ∑ a ∈ univ.filter (fun a : Fin (n + 1) → k => a ⬝ᵥ x = 1),
        ∑ b ∈ univ.filter (fun a : Fin (n + 1) → k => a ⬝ᵥ x = 1), R a b
      = ∑ x : Fin (n + 1) → k, ∑ a, ∑ b, if (a ⬝ᵥ x = 1 ∧ b ⬝ᵥ x = 1) then R a b else 0 := by
        refine Finset.sum_congr rfl fun x _ => ?_
        rw [Finset.sum_filter]
        refine Finset.sum_congr rfl fun a _ => ?_
        by_cases ha : a ⬝ᵥ x = 1
        · simp [ha, Finset.sum_filter]
        · simp [ha]
    _ = ∑ a, ∑ x : Fin (n + 1) → k, ∑ b, if (a ⬝ᵥ x = 1 ∧ b ⬝ᵥ x = 1) then R a b else 0 :=
        Finset.sum_comm
    _ = ∑ a, ∑ b, ∑ x : Fin (n + 1) → k, if (a ⬝ᵥ x = 1 ∧ b ⬝ᵥ x = 1) then R a b else 0 :=
        Finset.sum_congr rfl fun a _ => Finset.sum_comm
    _ = _ := by
        refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
        rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]

/- English proof (translation)
Introduce `k _ _ n V _ _ B w c A hpos h1 h2 hw hc hA`. Establish `hq1 : (1 : ℝ) < (Fintype.card k : ℝ)` using `by exact_mod_cast Fintype.one_lt_card`. Use `set q : ℝ := (Fintype.card k : ℝ) with hq`. Establish `hq0 : q ≠ 0` using `by linarith`. Set `N : (Fin (n + 1) → k) → (Fin (n + 1) → k) → ℝ` to `fun a b => ((univ.filter (fun x : Fin (n + 1) → k => a ⬝ᵥ x = 1 ∧ b ⬝ᵥ x = 1)).card : ℝ)`.

Set `R : (Fin (n + 1) → k) → (Fin (n + 1) → k) → ℝ` to `fun a b => (B (w a) (w b)).re`. Set `Z : Finset (Fin (n + 1) → k)` to `univ.filter (fun b => b ≠ 0)`. Establish `hZc : (Z.card : ℝ) = q ^ (n + 1) - 1`. Establish `h` using `card_filter_ne_zero (α := Fin (n + 1) → k)`. Establish `hc' : (Fintype.card (Fin (n + 1) → k) : ℝ) = q ^ (n + 1)` using `by simp [hq]`.

Rewrite `h` using `[hc']`. Rewrite using `[← h]`. Simplify using `only [Z]`. Use `congr!`. Establish `hrow : ∀ a, a ≠ 0 → q * ∑ b, N a b * R a b = q ^ n * ∑ b ∈ Z, R a b + q ^ n * c`.

Introduce `a ha`. Use `row_identity a ha (N a) (R a) c ?_ ?_ ?_ ?_ ?_` and prove the remaining obligations. Simplify using `[N]`. Establish `h` using `h1 a ha`. Establish `: N a a = ((univ.filter (fun x : Fin (n + 1) → k => a ⬝ᵥ x = 1)).card : ℝ)`.

Simplify using `only [N, and_self]`. Rewrite using `[this]`. Conclude with `h` after adjusting the coercions. Introduce `s hs`. Establish `: univ.filter (fun x : Fin (n + 1) → k => a ⬝ᵥ x = 1 ∧ (s • a) ⬝ᵥ x = 1) = ∅`.

Use `Finset.filter_eq_empty_iff.mpr ?_` and prove the remaining obligations. Introduce and unpack `x - ⟨hx, hx'⟩`. Rewrite `hx'` using `[smul_dotProduct, hx]`. Conclude with `hs (by simpa using hx')`. Simplify using `only [N, this, card_empty, Nat.cast_zero]`.

Introduce `b hb`. Establish `h` using `h2 a b ha hb`. Establish `h' : q ^ 2 * N a b = q ^ (n + 1)`. Simplify using `only [N]`. Rewrite using `[hq]`.

Conclude with `h` after adjusting the coercions. Apply `mul_left_cancel₀ hq0` to reduce the goal to its premises. Rewrite using `[← mul_assoc, ← pow_two, h', pow_succ]`. Expand and normalize the polynomial expressions, which then agree. Introduce `s hs`.

Simplify using `only [R, hw a ha s hs, hc a ha]`. Establish `hleft : ∑ x : Fin (n + 1) → k, ∑ a ∈ univ.filter (fun a : Fin (n + 1) → k => a ⬝ᵥ x = 1), ∑ b ∈ univ.filter (fun a : Fin (n + 1) → k => a ⬝ᵥ x = 1), R a b = (q ^ (n + 1) - 1) * A`. Establish `hZ : ∑ x ∈ Z, ∑ a ∈ univ.filter (fun a : Fin (n + 1) → k => a ⬝ᵥ x = 1), ∑ b ∈ univ.filter (fun a : Fin (n + 1) → k => a ⬝ᵥ x = 1), R a b = ∑ x : Fin (n + 1) → k, ∑ a ∈ univ.filter (fun a : Fin (n + 1) → k => a ⬝ᵥ x = 1), ∑ b ∈ univ.filter (fun a : Fin (n + 1) → k => a ⬝ᵥ x = 1), …`. Use `Finset.sum_subset (filter_subset _ _) ?_` and prove the remaining obligations. Introduce `x _ hx`.

Establish `hx0 : x = 0` using `by simpa [Z] using hx`. Substitute `hx0` using the available equality. Simplify using the standard rewrite rules. Rewrite using `[← hZ]`. Establish `hconst : ∀ x ∈ Z, ∑ a ∈ univ.filter (fun a : Fin (n + 1) → k => a ⬝ᵥ x = 1), ∑ b ∈ univ.filter (fun a : Fin (n + 1) → k => a ⬝ᵥ x = 1), R a b = A`.

Introduce `x hx`. Establish `hx0 : x ≠ 0` using `by simpa [Z] using hx`. Rewrite using `[← hA x hx0, re_sesq_sum]`. Rewrite using `[Finset.sum_congr rfl hconst, Finset.sum_const, nsmul_eq_mul, hZc]`. Establish `hright : q * ∑ a, ∑ b, N a b * R a b = q ^ n * ∑ a ∈ Z, ∑ b ∈ Z, R a b + (q ^ (n + 1) - 1) * (q ^ n * c)`.

Establish `hZ : ∑ a ∈ Z, ∑ b, N a b * R a b = ∑ a, ∑ b, N a b * R a b`. Use `Finset.sum_subset (filter_subset _ _) ?_` and prove the remaining obligations. Introduce `a _ ha`. Establish `ha0 : a = 0` using `by simpa [Z] using ha`. Substitute `ha0` using the available equality.

Simplify using `[N]`. Rewrite using `[← hZ, Finset.mul_sum, Finset.sum_congr rfl (fun a ha => hrow a (by simpa [Z] using ha)), Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, nsmul_eq_mul, hZc]`. Establish `hP : 0 ≤ ∑ a ∈ Z, ∑ b ∈ Z, R a b`. Use `hpos (∑ a ∈ Z, w a)` as an intermediate fact. Rewrite `this` using `[re_sesq_sum]`. Then use the resulting hypothesis.

Establish `hmain : q * ((q ^ (n + 1) - 1) * A) = q ^ n * ∑ a ∈ Z, ∑ b ∈ Z, R a b + (q ^ (n + 1) - 1) * (q ^ n * c)`. Rewrite using `[← hleft, sum_expand R]`. Conclude with `hright`. Establish `hQ : 0 < q ^ (n + 1) - 1`. Establish `: 1 < q ^ (n + 1)` using `one_lt_pow₀ hq1 (Nat.succ_ne_zero n)`.

Combine the linear equalities and inequalities to obtain the conclusion. Establish `hqn : 0 ≤ q ^ n` using `by positivity`. Establish `hfin : 0 ≤ (q ^ (n + 1) - 1) * (q * A - q ^ n * c)`. Establish `: (q ^ (n + 1) - 1) * (q * A - q ^ n * c) = q ^ n * ∑ a ∈ Z, ∑ b ∈ Z, R a b`. Take the linear combination `hmain`.

Rewrite using `[this]`. Conclude with `mul_nonneg hqn hP`. Use `nonneg_of_mul_nonneg_right hfin hQ` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem lower_from_counts : ∀ (k : Type) [Field k] [Fintype k] (n : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (B : V →ₗ[ℂ] V →ₗ⋆[ℂ] ℂ)
  (w : (Fin (n + 1) → k) → V) (c A : ℝ),
  (∀ x, 0 ≤ (B x x).re) →
  (∀ a : Fin (n + 1) → k, a ≠ 0 →
    Fintype.card k * (Finset.univ.filter (fun x : Fin (n + 1) → k => a ⬝ᵥ x = 1)).card = Fintype.card k ^ (n + 1)) →
  (∀ a b : Fin (n + 1) → k, a ≠ 0 → (∀ s : k, b ≠ s • a) →
    Fintype.card k ^ 2 * (Finset.univ.filter (fun x : Fin (n + 1) → k => a ⬝ᵥ x = 1 ∧ b ⬝ᵥ x = 1)).card = Fintype.card k ^ (n + 1)) →
  (∀ a : Fin (n + 1) → k, a ≠ 0 → ∀ s : k, s ≠ 0 → w (s • a) = w a) →
  (∀ a : Fin (n + 1) → k, a ≠ 0 → (B (w a) (w a)).re = c) →
  (∀ x : Fin (n + 1) → k, x ≠ 0 →
    (B (∑ a ∈ Finset.univ.filter (fun a : Fin (n + 1) → k => a ⬝ᵥ x = 1), w a)
       (∑ a ∈ Finset.univ.filter (fun a : Fin (n + 1) → k => a ⬝ᵥ x = 1), w a)).re = A) →
  (Fintype.card k : ℝ) ^ n * c ≤ (Fintype.card k : ℝ) * A := by
  intro k _ _ n V _ _ B w c A hpos h1 h2 hw hc hA
  have hq1 : (1 : ℝ) < (Fintype.card k : ℝ) := by exact_mod_cast Fintype.one_lt_card
  set q : ℝ := (Fintype.card k : ℝ) with hq
  have hq0 : q ≠ 0 := by linarith
  let N : (Fin (n + 1) → k) → (Fin (n + 1) → k) → ℝ := fun a b =>
    ((univ.filter (fun x : Fin (n + 1) → k => a ⬝ᵥ x = 1 ∧ b ⬝ᵥ x = 1)).card : ℝ)
  let R : (Fin (n + 1) → k) → (Fin (n + 1) → k) → ℝ := fun a b => (B (w a) (w b)).re
  let Z : Finset (Fin (n + 1) → k) := univ.filter (fun b => b ≠ 0)
  have hZc : (Z.card : ℝ) = q ^ (n + 1) - 1 := by
    have h := card_filter_ne_zero (α := Fin (n + 1) → k)
    have hc' : (Fintype.card (Fin (n + 1) → k) : ℝ) = q ^ (n + 1) := by simp [hq]
    rw [hc'] at h
    rw [← h]
    simp only [Z]
    congr!
  have hrow : ∀ a, a ≠ 0 → q * ∑ b, N a b * R a b
      = q ^ n * ∑ b ∈ Z, R a b + q ^ n * c := by
    intro a ha
    refine row_identity a ha (N a) (R a) c ?_ ?_ ?_ ?_ ?_
    · simp [N]
    · have h := h1 a ha
      have : N a a = ((univ.filter (fun x : Fin (n + 1) → k => a ⬝ᵥ x = 1)).card : ℝ) := by
        simp only [N, and_self]
      rw [this]
      exact_mod_cast h
    · intro s hs
      have : univ.filter (fun x : Fin (n + 1) → k => a ⬝ᵥ x = 1 ∧ (s • a) ⬝ᵥ x = 1) = ∅ := by
        refine Finset.filter_eq_empty_iff.mpr ?_
        rintro x - ⟨hx, hx'⟩
        rw [smul_dotProduct, hx] at hx'
        exact hs (by simpa using hx')
      simp only [N, this, card_empty, Nat.cast_zero]
    · intro b hb
      have h := h2 a b ha hb
      have h' : q ^ 2 * N a b = q ^ (n + 1) := by
        simp only [N]; rw [hq]; exact_mod_cast h
      apply mul_left_cancel₀ hq0
      rw [← mul_assoc, ← pow_two, h', pow_succ]; ring
    · intro s hs
      simp only [R, hw a ha s hs, hc a ha]

  have hleft : ∑ x : Fin (n + 1) → k,
      ∑ a ∈ univ.filter (fun a : Fin (n + 1) → k => a ⬝ᵥ x = 1),
        ∑ b ∈ univ.filter (fun a : Fin (n + 1) → k => a ⬝ᵥ x = 1), R a b
      = (q ^ (n + 1) - 1) * A := by
    have hZ : ∑ x ∈ Z, ∑ a ∈ univ.filter (fun a : Fin (n + 1) → k => a ⬝ᵥ x = 1),
        ∑ b ∈ univ.filter (fun a : Fin (n + 1) → k => a ⬝ᵥ x = 1), R a b
        = ∑ x : Fin (n + 1) → k,
      ∑ a ∈ univ.filter (fun a : Fin (n + 1) → k => a ⬝ᵥ x = 1),
        ∑ b ∈ univ.filter (fun a : Fin (n + 1) → k => a ⬝ᵥ x = 1), R a b := by
      refine Finset.sum_subset (filter_subset _ _) ?_
      intro x _ hx
      have hx0 : x = 0 := by simpa [Z] using hx
      subst hx0
      simp
    rw [← hZ]
    have hconst : ∀ x ∈ Z, ∑ a ∈ univ.filter (fun a : Fin (n + 1) → k => a ⬝ᵥ x = 1),
        ∑ b ∈ univ.filter (fun a : Fin (n + 1) → k => a ⬝ᵥ x = 1), R a b = A := by
      intro x hx
      have hx0 : x ≠ 0 := by simpa [Z] using hx
      rw [← hA x hx0, re_sesq_sum]
    rw [Finset.sum_congr rfl hconst, Finset.sum_const, nsmul_eq_mul, hZc]

  have hright : q * ∑ a, ∑ b, N a b * R a b
      = q ^ n * ∑ a ∈ Z, ∑ b ∈ Z, R a b + (q ^ (n + 1) - 1) * (q ^ n * c) := by
    have hZ : ∑ a ∈ Z, ∑ b, N a b * R a b = ∑ a, ∑ b, N a b * R a b := by
      refine Finset.sum_subset (filter_subset _ _) ?_
      intro a _ ha
      have ha0 : a = 0 := by simpa [Z] using ha
      subst ha0
      simp [N]
    rw [← hZ, Finset.mul_sum, Finset.sum_congr rfl (fun a ha => hrow a (by simpa [Z] using ha)),
      Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, nsmul_eq_mul, hZc]
  have hP : 0 ≤ ∑ a ∈ Z, ∑ b ∈ Z, R a b := by
    have := hpos (∑ a ∈ Z, w a)
    rwa [re_sesq_sum] at this
  have hmain : q * ((q ^ (n + 1) - 1) * A)
      = q ^ n * ∑ a ∈ Z, ∑ b ∈ Z, R a b + (q ^ (n + 1) - 1) * (q ^ n * c) := by
    rw [← hleft, sum_expand R]
    exact hright
  have hQ : 0 < q ^ (n + 1) - 1 := by
    have : 1 < q ^ (n + 1) := one_lt_pow₀ hq1 (Nat.succ_ne_zero n)
    linarith
  have hqn : 0 ≤ q ^ n := by positivity
  have hfin : 0 ≤ (q ^ (n + 1) - 1) * (q * A - q ^ n * c) := by
    have : (q ^ (n + 1) - 1) * (q * A - q ^ n * c) = q ^ n * ∑ a ∈ Z, ∑ b ∈ Z, R a b := by
      linear_combination hmain
    rw [this]
    exact mul_nonneg hqn hP
  have := nonneg_of_mul_nonneg_right hfin hQ
  linarith

end GlobalTheory.CompanionTheory.GapOpLower

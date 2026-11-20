import Mathlib
import Development.WeilBound.CoreStatements.FiniteTypeHarishChandra.SupportExistsAll

open ReciprocityTheory.Ty.Fin

noncomputable section

namespace GlobalTheory.CompanionTheory.PatGrp

variable {K : Type} [Field K] [Fintype K] [DecidableEq K]
variable {ι : Type} [Fintype ι] [DecidableEq ι] {Φ : ι → ι → Prop}

def Supp (Φ : ι → ι → Prop) (N : Matrix ι ι K) : Prop := ∀ i j, N i j ≠ 0 → Φ i j

/- English proof (translation)
Unfold `patSet`. Rewrite using `[Set.mem_setOf_eq]`. Prove the components needed by the constructor for the conclusion. Introduce `hu i j hN`. Assume the negation of the conclusion as `hΦ`.

Apply `hN` to reduce the goal to its premises. Break down `eq_or_ne i j with rfl | hij` into its components or cases. Rewrite using `[Matrix.sub_apply, Matrix.one_apply_eq, (hu i i).1 rfl, sub_self]`. Rewrite using `[Matrix.sub_apply, Matrix.one_apply_ne hij, (hu i j).2 hij hΦ, sub_zero]`. Introduce `hS i j`.

Use `⟨fun hij => ?_, fun hij hΦ => ?_⟩` and prove the remaining obligations. Substitute `hij` using the available equality. Establish `h0 : ((u : Matrix ι ι K) - 1) i i = 0`. Assume the negation of the conclusion as `hne`. Conclude with `h.1 i (hS i i hne)`.

Rewrite `h0` using `[Matrix.sub_apply, Matrix.one_apply_eq, sub_eq_zero]`. Then use the resulting hypothesis. Establish `h0 : ((u : Matrix ι ι K) - 1) i j = 0`. Assume the negation of the conclusion as `hne`. Conclude with `hΦ (hS i j hne)`. Rewrite `h0` using `[Matrix.sub_apply, Matrix.one_apply_ne hij, sub_zero]`. Then use the resulting hypothesis.
-/
theorem mem_patSet_iff (h : IsPat Φ) (u : GL ι K) :
    u ∈ patSet K Φ ↔ Supp Φ ((u : Matrix ι ι K) - 1) := by
  unfold patSet
  rw [Set.mem_setOf_eq]
  constructor
  · intro hu i j hN
    by_contra hΦ
    apply hN
    rcases eq_or_ne i j with rfl | hij
    · rw [Matrix.sub_apply, Matrix.one_apply_eq, (hu i i).1 rfl, sub_self]
    · rw [Matrix.sub_apply, Matrix.one_apply_ne hij, (hu i j).2 hij hΦ, sub_zero]
  · intro hS i j
    refine ⟨fun hij => ?_, fun hij hΦ => ?_⟩
    · subst hij
      have h0 : ((u : Matrix ι ι K) - 1) i i = 0 := by
        by_contra hne
        exact h.1 i (hS i i hne)
      rwa [Matrix.sub_apply, Matrix.one_apply_eq, sub_eq_zero] at h0
    · have h0 : ((u : Matrix ι ι K) - 1) i j = 0 := by
        by_contra hne
        exact hΦ (hS i j hne)
      rwa [Matrix.sub_apply, Matrix.one_apply_ne hij, sub_zero] at h0

/- English proof (translation)
Introduce `i j hij`. Rewrite `hij` using `[Matrix.mul_apply]`. Take `⟨k, -, hk⟩` from `Finset.exists_ne_zero_of_sum_ne_zero hij`. Conclude with `h.2 i k j (hA i k (left_ne_zero_of_mul hk)) (hB k j (right_ne_zero_of_mul hk))`.
-/
theorem Supp.mul (h : IsPat Φ) {A B : Matrix ι ι K} (hA : Supp Φ A) (hB : Supp Φ B) :
    Supp Φ (A * B) := by
  intro i j hij
  rw [Matrix.mul_apply] at hij
  obtain ⟨k, -, hk⟩ := Finset.exists_ne_zero_of_sum_ne_zero hij
  exact h.2 i k j (hA i k (left_ne_zero_of_mul hk)) (hB k j (right_ne_zero_of_mul hk))

/- English proof (translation)
Introduce `i j hij`. Distinguish the cases in `ha : A i j = 0`. Apply `hB` to reduce the goal to its premises. Introduce `hb`. Apply `hij` to reduce the goal to its premises.

Rewrite using `[Matrix.add_apply, ha, hb, add_zero]`. Conclude with `hA i j ha`.
-/
theorem Supp.add {A B : Matrix ι ι K} (hA : Supp Φ A) (hB : Supp Φ B) : Supp Φ (A + B) := by
  intro i j hij
  by_cases ha : A i j = 0
  · apply hB
    intro hb
    apply hij
    rw [Matrix.add_apply, ha, hb, add_zero]
  · exact hA i j ha

/- English proof (translation)
Set `b : ι → ℕ` to `fun i => (Finset.univ.filter fun k => Φ k i).card`. Establish `hb : ∀ i j, Φ i j → b i < b j`. Introduce `i j hij`. Apply `Finset.card_lt_card` to reduce the goal to its premises. Use `(Finset.ssubset_iff_of_subset ?_).2 ⟨i, ?_, ?_⟩` and prove the remaining obligations.

Introduce `k hk`. Simplify using `only [Finset.mem_filter, Finset.mem_univ, true_and] at hk ⊢`. Conclude with `h.2 k i j hk hij`. Simplify using `only [Finset.mem_filter, Finset.mem_univ, true_and]`. Conclude with `hij`.

Simplify using `only [Finset.mem_filter, Finset.mem_univ, true_and]`. Conclude with `h.1 i`. Establish `hN0 : ∀ i j, b j ≤ b i → N i j = 0`. Introduce `i j hle`. Assume the negation of the conclusion as `hne`.

Conclude with `absurd (hb i j (hN i j hne)) (not_lt.2 hle)`. Establish `hT : (1 + N).BlockTriangular b`. Introduce `i j hlt`. Establish `hij : i ≠ j`. Introduce and unpack `rfl`.

Conclude with `lt_irrefl _ hlt`. Rewrite using `[Matrix.add_apply, Matrix.one_apply_ne hij, hN0 i j hlt.le, add_zero]`. Rewrite using `[hT.det]`. Use `Finset.prod_eq_one fun a _ => ?_` and prove the remaining obligations. Establish `hblk : (1 + N).toSquareBlock b a = 1`.

Use extensionality with `⟨i, hi⟩ ⟨j, hj⟩`. Use `show (1 + N) i j = (1 : Matrix {a' // b a' = a} {a' // b a' = a} K) ⟨i, hi⟩ ⟨j, hj⟩`. Establish `hNij : N i j = 0` using `hN0 i j (by rw [hi, hj])`. Break down `eq_or_ne i j with rfl | hij` into its components or cases. Rewrite using `[Matrix.add_apply, hNij, add_zero, Matrix.one_apply_eq, Matrix.one_apply_eq]`.

Rewrite using `[Matrix.add_apply, Matrix.one_apply_ne hij, hNij, add_zero, Matrix.one_apply_ne (fun e => hij (congrArg Subtype.val e))]`. Rewrite using `[hblk, Matrix.det_one]`.
-/
theorem det_one_add (h : IsPat Φ) {N : Matrix ι ι K} (hN : Supp Φ N) : (1 + N).det = 1 := by
  classical
  let b : ι → ℕ := fun i => (Finset.univ.filter fun k => Φ k i).card
  have hb : ∀ i j, Φ i j → b i < b j := by
    intro i j hij
    apply Finset.card_lt_card
    refine (Finset.ssubset_iff_of_subset ?_).2 ⟨i, ?_, ?_⟩
    · intro k hk
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk ⊢
      exact h.2 k i j hk hij
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact hij
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact h.1 i
  have hN0 : ∀ i j, b j ≤ b i → N i j = 0 := by
    intro i j hle
    by_contra hne
    exact absurd (hb i j (hN i j hne)) (not_lt.2 hle)
  have hT : (1 + N).BlockTriangular b := by
    intro i j hlt
    have hij : i ≠ j := by
      rintro rfl
      exact lt_irrefl _ hlt
    rw [Matrix.add_apply, Matrix.one_apply_ne hij, hN0 i j hlt.le, add_zero]
  rw [hT.det]
  refine Finset.prod_eq_one fun a _ => ?_
  have hblk : (1 + N).toSquareBlock b a = 1 := by
    ext ⟨i, hi⟩ ⟨j, hj⟩
    show (1 + N) i j = (1 : Matrix {a' // b a' = a} {a' // b a' = a} K) ⟨i, hi⟩ ⟨j, hj⟩
    have hNij : N i j = 0 := hN0 i j (by rw [hi, hj])
    rcases eq_or_ne i j with rfl | hij
    · rw [Matrix.add_apply, hNij, add_zero, Matrix.one_apply_eq, Matrix.one_apply_eq]
    · rw [Matrix.add_apply, Matrix.one_apply_ne hij, hNij, add_zero,
        Matrix.one_apply_ne (fun e => hij (congrArg Subtype.val e))]
  rw [hblk, Matrix.det_one]

def patSubgroup (h : IsPat Φ) : Subgroup (GL ι K) :=
  let M : Submonoid (GL ι K) :=
    { carrier := patSet K Φ
      mul_mem' := by
        intro u v hu hv
        have hu' := (mem_patSet_iff h u).1 hu
        have hv' := (mem_patSet_iff h v).1 hv
        refine (mem_patSet_iff h _).2 ?_
        have e : ((u * v : GL ι K) : Matrix ι ι K) - 1 =
            ((u : Matrix ι ι K) - 1) + ((v : Matrix ι ι K) - 1) +
              ((u : Matrix ι ι K) - 1) * ((v : Matrix ι ι K) - 1) := by
          rw [Units.val_mul]
          noncomm_ring
        rw [e]
        exact (hu'.add hv').add (hu'.mul h hv')
      one_mem' := by
        refine (mem_patSet_iff h _).2 ?_
        intro i j hij
        simp at hij }
  { M with
    inv_mem' := by
      intro u hu
      have hn : orderOf u ≠ 0 := (orderOf_pos u).ne'
      have : u⁻¹ = u ^ (orderOf u - 1) :=
        inv_eq_of_mul_eq_one_right (by rw [mul_pow_sub_one hn, pow_orderOf_eq_one])
      rw [this]
      exact M.pow_mem hu _ }

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem coe_patSubgroup (h : IsPat Φ) :
    ((patSubgroup h : Subgroup (GL ι K)) : Set (GL ι K)) = patSet K Φ := rfl

open Classical in

def fill (Φ : ι → ι → Prop) (f : {p : ι × ι // Φ p.1 p.2} → K) : Matrix ι ι K :=
  fun i j => if h : Φ i j then f ⟨(i, j), h⟩ else 0

/- English proof (translation)
Introduce `i j hij`. Assume the negation of the conclusion as `hΦ`. Apply `hij` to reduce the goal to its premises. Simplify using `[fill, hΦ]`.
-/
theorem supp_fill (f : {p : ι × ι // Φ p.1 p.2} → K) : Supp Φ (fill Φ f) := by
  intro i j hij
  by_contra hΦ
  apply hij
  simp [fill, hΦ]

/- English proof (translation)
Establish `hunit : ∀ f : {p : ι × ι // Φ p.1 p.2} → K, IsUnit (1 + fill Φ f).det` using `fun f => by`. Rewrite using `[det_one_add h (supp_fill f)]`. Conclude with `isUnit_one`. Set `e : patSet K Φ ≃ ({p : ι × ι // Φ p.1 p.2} → K)` to `{ toFun := fun u p => (u.1 : Matrix ι ι K) p.1.1 p.1.2 invFun := fun f => ⟨Matrix.nonsingInvUnit (1 + fill Φ f) (hunit f), by`. Use `(mem_patSet_iff h _).2 ?_` and prove the remaining obligations.

Use `show Supp Φ ((1 + fill Φ f) - 1)`. Rewrite using `[add_sub_cancel_left]`. Conclude with `supp_fill f⟩`. Use `left_inv := fun u => by`. Apply `Subtype.ext` to reduce the goal to its premises.

Apply `Units.ext` to reduce the goal to its premises. Use `show 1 + fill Φ (fun p => (u.1 : Matrix ι ι K) p.1.1 p.1.2) = (u.1 : Matrix ι ι K)`. Use extensionality with `i j`. Establish `hu` using `(show ∀ i j, (i = j → (u.1 : Matrix ι ι K) i j = 1) ∧ (i ≠ j → ¬Φ i j → (u.1 : Matrix ι ι K) i j = 0) from u.2) i j`. Rewrite using `[Matrix.add_apply]`.

Simplify using `only [fill]`. Break down `eq_or_ne i j with rfl | hij` into its components or cases. Rewrite using `[Matrix.one_apply_eq, dif_neg (h.1 i), add_zero, hu.1 rfl]`. Rewrite using `[Matrix.one_apply_ne hij, zero_add]`. Distinguish the cases in `hΦ : Φ i j`.

Rewrite using `[dif_pos hΦ]`. Rewrite using `[dif_neg hΦ, hu.2 hij hΦ]`. Use `right_inv := fun f => by`. Use function extensionality and compare the values at `p`. Use `show (1 + fill Φ f) p.1.1 p.1.2 = f p`.

Establish `hne : p.1.1 ≠ p.1.2` using `fun e => h.1 p.1.2 (by have hp := p.2; rw [e] at hp; exact hp)`. Rewrite using `[Matrix.add_apply, Matrix.one_apply_ne hne, zero_add]`. Simplify using `only [fill]`. Rewrite using `[dif_pos p.2] }`. Rewrite using `[← Nat.card_coe_set_eq, Nat.card_congr e, Nat.card_fun, Nat.card_eq_fintype_card (α := K)]`.
-/
theorem card_patSet (h : IsPat Φ) :
    (patSet K Φ).ncard = Fintype.card K ^ Nat.card {p : ι × ι // Φ p.1 p.2} := by
  classical
  have hunit : ∀ f : {p : ι × ι // Φ p.1 p.2} → K, IsUnit (1 + fill Φ f).det := fun f => by
    rw [det_one_add h (supp_fill f)]
    exact isUnit_one
  let e : patSet K Φ ≃ ({p : ι × ι // Φ p.1 p.2} → K) :=
    { toFun := fun u p => (u.1 : Matrix ι ι K) p.1.1 p.1.2
      invFun := fun f => ⟨Matrix.nonsingInvUnit (1 + fill Φ f) (hunit f), by
        refine (mem_patSet_iff h _).2 ?_
        show Supp Φ ((1 + fill Φ f) - 1)
        rw [add_sub_cancel_left]
        exact supp_fill f⟩
      left_inv := fun u => by
        apply Subtype.ext
        apply Units.ext
        show 1 + fill Φ (fun p => (u.1 : Matrix ι ι K) p.1.1 p.1.2) = (u.1 : Matrix ι ι K)
        ext i j
        have hu := (show ∀ i j, (i = j → (u.1 : Matrix ι ι K) i j = 1) ∧
          (i ≠ j → ¬Φ i j → (u.1 : Matrix ι ι K) i j = 0) from u.2) i j
        rw [Matrix.add_apply]
        simp only [fill]
        rcases eq_or_ne i j with rfl | hij
        · rw [Matrix.one_apply_eq, dif_neg (h.1 i), add_zero, hu.1 rfl]
        · rw [Matrix.one_apply_ne hij, zero_add]
          by_cases hΦ : Φ i j
          · rw [dif_pos hΦ]
          · rw [dif_neg hΦ, hu.2 hij hΦ]
      right_inv := fun f => by
        funext p
        show (1 + fill Φ f) p.1.1 p.1.2 = f p
        have hne : p.1.1 ≠ p.1.2 := fun e => h.1 p.1.2 (by have hp := p.2; rw [e] at hp; exact hp)
        rw [Matrix.add_apply, Matrix.one_apply_ne hne, zero_add]
        simp only [fill]
        rw [dif_pos p.2] }
  rw [← Nat.card_coe_set_eq, Nat.card_congr e, Nat.card_fun, Nat.card_eq_fintype_card (α := K)]

def pair (E : ι → ι → K) (M : Matrix ι ι K) : K := ∑ i, ∑ j, E i j * M i j

/- English proof (translation)
Unfold `pair`. Simplify using `only [Matrix.add_apply, mul_add, Finset.sum_add_distrib]`.
-/
theorem pair_add (E : ι → ι → K) (A B : Matrix ι ι K) : pair E (A + B) = pair E A + pair E B := by
  unfold pair
  simp only [Matrix.add_apply, mul_add, Finset.sum_add_distrib]

/- English proof (translation)
Unfold `pair`. Use `Finset.sum_eq_zero fun i _ => Finset.sum_eq_zero fun j _ => ?_` and prove the remaining obligations. Break down `eq_or_ne i j with rfl | hij` into its components or cases. Establish `hEi : E i i = 0`. Assume the negation of the conclusion as `hne`.

Conclude with `h.1 i (hE.1 i i hne)`. Rewrite using `[hEi, zero_mul]`. Rewrite using `[Matrix.one_apply_ne hij, mul_zero]`.
-/
theorem pair_one (h : IsPat Φ) {E : ι → ι → K} (hE : IsPatChar Φ E) : pair E (1 : Matrix ι ι K) = 0 := by
  unfold pair
  refine Finset.sum_eq_zero fun i _ => Finset.sum_eq_zero fun j _ => ?_
  rcases eq_or_ne i j with rfl | hij
  · have hEi : E i i = 0 := by
      by_contra hne
      exact h.1 i (hE.1 i i hne)
    rw [hEi, zero_mul]
  · rw [Matrix.one_apply_ne hij, mul_zero]

/- English proof (translation)
Unfold `pair`. Use `Finset.sum_eq_zero fun i _ => Finset.sum_eq_zero fun j _ => ?_` and prove the remaining obligations. Rewrite using `[Matrix.mul_apply, Finset.mul_sum]`. Use `Finset.sum_eq_zero fun k _ => ?_` and prove the remaining obligations. Distinguish the cases in `hAk : A i k = 0`.

Rewrite using `[hAk, zero_mul, mul_zero]`. Distinguish the cases in `hBk : B k j = 0`. Rewrite using `[hBk, mul_zero, mul_zero]`. Rewrite using `[hE.2 i k j (hA i k hAk) (hB k j hBk), zero_mul]`.
-/
theorem pair_mul {E : ι → ι → K} (hE : IsPatChar Φ E) {A B : Matrix ι ι K}
    (hA : Supp Φ A) (hB : Supp Φ B) : pair E (A * B) = 0 := by
  unfold pair
  refine Finset.sum_eq_zero fun i _ => Finset.sum_eq_zero fun j _ => ?_
  rw [Matrix.mul_apply, Finset.mul_sum]
  refine Finset.sum_eq_zero fun k _ => ?_
  by_cases hAk : A i k = 0
  · rw [hAk, zero_mul, mul_zero]
  by_cases hBk : B k j = 0
  · rw [hBk, mul_zero, mul_zero]
  rw [hE.2 i k j (hA i k hAk) (hB k j hBk), zero_mul]

/- English proof (translation)
Establish `hu'` using `(mem_patSet_iff h u).1 hu`. Establish `hv'` using `(mem_patSet_iff h v).1 hv`. Establish `key : ∀ w : GL ι K, patChar E ψ₀ w = ψ₀ (pair E (w : Matrix ι ι K))` using `fun w => rfl`. Rewrite using `[key, key, key, ← AddChar.map_add_eq_mul]`. Use `congr 1`.

Use `set A := (u : Matrix ι ι K) - 1 with hAdef`. Use `set Bm := (v : Matrix ι ι K) - 1 with hBdef`. Establish `eu : (u : Matrix ι ι K) = 1 + A`. Rewrite using `[hAdef]`. Normalize the expressions using the abelian group laws.

Establish `ev : (v : Matrix ι ι K) = 1 + Bm`. Rewrite using `[hBdef]`. Normalize the expressions using the abelian group laws. Rewrite using `[Units.val_mul, eu, ev]`. Establish `e2 : (1 + A) * (1 + Bm) = 1 + (A + Bm + A * Bm)` using `by noncomm_ring`.

Rewrite using `[e2]`. Simplify using `only [pair_add]`. Rewrite using `[pair_one h hE, pair_mul hE hu' hv']`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem patChar_mul (h : IsPat Φ) {E : ι → ι → K} (hE : IsPatChar Φ E) (ψ₀ : AddChar K ℂ)
    {u v : GL ι K} (hu : u ∈ patSet K Φ) (hv : v ∈ patSet K Φ) :
    patChar E ψ₀ (u * v) = patChar E ψ₀ u * patChar E ψ₀ v := by
  have hu' := (mem_patSet_iff h u).1 hu
  have hv' := (mem_patSet_iff h v).1 hv
  have key : ∀ w : GL ι K, patChar E ψ₀ w = ψ₀ (pair E (w : Matrix ι ι K)) := fun w => rfl
  rw [key, key, key, ← AddChar.map_add_eq_mul]
  congr 1
  set A := (u : Matrix ι ι K) - 1 with hAdef
  set Bm := (v : Matrix ι ι K) - 1 with hBdef
  have eu : (u : Matrix ι ι K) = 1 + A := by
    rw [hAdef]
    abel
  have ev : (v : Matrix ι ι K) = 1 + Bm := by
    rw [hBdef]
    abel
  rw [Units.val_mul, eu, ev]
  have e2 : (1 + A) * (1 + Bm) = 1 + (A + Bm + A * Bm) := by noncomm_ring
  rw [e2]
  simp only [pair_add]
  rw [pair_one h hE, pair_mul hE hu' hv']
  ring

/- English proof (translation)
Use `show ψ₀ (pair E ((1 : GL ι K) : Matrix ι ι K)) = 1`. Rewrite using `[Units.val_one, pair_one h hE, AddChar.map_zero_eq_one]`.
-/
theorem patChar_one (h : IsPat Φ) {E : ι → ι → K} (hE : IsPatChar Φ E) (ψ₀ : AddChar K ℂ) :
    patChar E ψ₀ (1 : GL ι K) = 1 := by
  show ψ₀ (pair E ((1 : GL ι K) : Matrix ι ι K)) = 1
  rw [Units.val_one, pair_one h hE, AddChar.map_zero_eq_one]

/- English proof (translation)
Distinguish the cases in `h1 : L 1 = 0`. Use `⟨0, ?_⟩` and prove the remaining obligations. Establish `hL0 : ∀ x, L x = 0` using `fun x => by rw [← mul_one x, hL, h1, mul_zero]`. Simplify using `[hL0]`. Establish `hL1 : L 1 = 1`.

Establish `h11` using `hL 1 1`. Rewrite `h11` using `[mul_one]`. Conclude with `(mul_left_cancel₀ h1 (by rw [mul_one]; exact h11)).symm`. Set `σ' : Representation ℂ H V` to `{ toFun := fun x => L x • σ x map_one' := by show L 1 • σ 1 = 1`. Rewrite using `[map_one, hL1, one_smul]`.

Use the proof step `map_mul' := fun a b => by show L (a * b) • σ (a * b) = (L a • σ a) * (L b • σ b)`. Rewrite using `[hL, map_mul, smul_mul_smul_comm] }`. Use `haveI : Invertible (Nat.card H : ℂ) := invertibleOfNonzero (Nat.cast_ne_zero.2 Nat.card_pos.ne')`. Use `⟨Module.finrank ℂ (Representation.invariants (FDRep.of σ').ρ), ?_⟩` and prove the remaining obligations. Rewrite using `[← FDRep.average_char_eq_finrank_invariants, Nat.card_eq_fintype_card]`.

Use `congr 1`. Use `Finset.sum_congr rfl fun x _ => ?_` and prove the remaining obligations. Use `show L x * LinearMap.trace ℂ V (σ x) = LinearMap.trace ℂ V (L x • σ x)`. Rewrite using `[LinearMap.map_smul, smul_eq_mul]`.
-/
theorem exists_nat_avg {H V : Type} [Group H] [Fintype H] [AddCommGroup V] [Module ℂ V]
    [FiniteDimensional ℂ V] (L : H → ℂ) (hL : ∀ a b, L (a * b) = L a * L b)
    (σ : H →* Module.End ℂ V) :
    ∃ m : ℕ, (Fintype.card H : ℂ)⁻¹ * ∑ h, L h * LinearMap.trace ℂ V (σ h) = m := by
  by_cases h1 : L 1 = 0
  · refine ⟨0, ?_⟩
    have hL0 : ∀ x, L x = 0 := fun x => by rw [← mul_one x, hL, h1, mul_zero]
    simp [hL0]
  · have hL1 : L 1 = 1 := by
      have h11 := hL 1 1
      rw [mul_one] at h11
      exact (mul_left_cancel₀ h1 (by rw [mul_one]; exact h11)).symm
    let σ' : Representation ℂ H V :=
      { toFun := fun x => L x • σ x
        map_one' := by
          show L 1 • σ 1 = 1
          rw [map_one, hL1, one_smul]
        map_mul' := fun a b => by
          show L (a * b) • σ (a * b) = (L a • σ a) * (L b • σ b)
          rw [hL, map_mul, smul_mul_smul_comm] }
    haveI : Invertible (Nat.card H : ℂ) :=
      invertibleOfNonzero (Nat.cast_ne_zero.2 Nat.card_pos.ne')
    refine ⟨Module.finrank ℂ (Representation.invariants (FDRep.of σ').ρ), ?_⟩
    rw [← FDRep.average_char_eq_finrank_invariants, Nat.card_eq_fintype_card]
    congr 1
    refine Finset.sum_congr rfl fun x _ => ?_
    show L x * LinearMap.trace ℂ V (σ x) = LinearMap.trace ℂ V (L x • σ x)
    rw [LinearMap.map_smul, smul_eq_mul]

/- English proof (translation)
Use `set G' := patSubgroup (K := K) h with hG'`. Establish `hmem : ∀ u : GL ι K, u ∈ G' ↔ u ∈ patSet K Φ` using `fun u => by`. Rewrite using `[← coe_patSubgroup h]`. Both sides reduce to the same expression. Take `⟨m, hm⟩` from `exists_nat_avg (H := G') (V := V) (fun x => (patChar E ψ₀ (x : GL ι K))⁻¹) (fun a b => by show (patChar E ψ₀ ((a : GL ι K) * b))⁻¹ = _`.

Rewrite using `[patChar_mul h hE ψ₀ ((hmem _).1 a.2) ((hmem _).1 b.2), mul_inv])`. Use the proof step `(ρ.comp G'.subtype)`. Use `⟨m, ?_⟩` and prove the remaining obligations. Rewrite using `[← hm]`. Unfold `wh`.

Establish `hcard : ((patSet K Φ).ncard : ℂ) = (Fintype.card G' : ℂ)`. Rewrite using `[← Nat.card_eq_fintype_card, ← coe_patSubgroup h]`. Conclude with `congrArg _ (Nat.card_coe_set_eq _).symm`. Rewrite using `[hcard, ← Finset.sum_filter]`. Use `congr 1`.

Conclude with `Finset.sum_subtype _ (fun u => by simp [hmem]) _`.
-/
theorem exists_nat_wh (h : IsPat Φ) {E : ι → ι → K} (hE : IsPatChar Φ E) (ψ₀ : AddChar K ℂ)
    {V : Type} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (ρ : Representation ℂ (GL ι K) V) : ∃ m : ℕ, wh Φ E ψ₀ ρ.character = m := by
  classical
  set G' := patSubgroup (K := K) h with hG'
  have hmem : ∀ u : GL ι K, u ∈ G' ↔ u ∈ patSet K Φ := fun u => by
    rw [← coe_patSubgroup h]
    rfl
  obtain ⟨m, hm⟩ := exists_nat_avg (H := G') (V := V) (fun x => (patChar E ψ₀ (x : GL ι K))⁻¹)
    (fun a b => by
      show (patChar E ψ₀ ((a : GL ι K) * b))⁻¹ = _
      rw [patChar_mul h hE ψ₀ ((hmem _).1 a.2) ((hmem _).1 b.2), mul_inv])
    (ρ.comp G'.subtype)
  refine ⟨m, ?_⟩
  rw [← hm]
  unfold wh
  have hcard : ((patSet K Φ).ncard : ℂ) = (Fintype.card G' : ℂ) := by
    rw [← Nat.card_eq_fintype_card, ← coe_patSubgroup h]
    exact congrArg _ (Nat.card_coe_set_eq _).symm
  rw [hcard, ← Finset.sum_filter]
  congr 1
  exact Finset.sum_subtype _ (fun u => by simp [hmem]) _

/- English proof (translation)
Introduce `K _ _ _ ι _ _ Φ h`. Use `⟨⟨patSubgroup h, coe_patSubgroup h⟩, card_patSet h, fun E ψ₀ hE => ⟨fun u hu v hv => patChar_mul h hE ψ₀ hu hv, patChar_one h hE ψ₀, fun u hu => ?_, fun V _ _ _ ρ => exists_nat_wh h hE ψ₀ ρ⟩⟩` and prove the remaining obligations. Establish `hu' : u ∈ ((patSubgroup h : Subgroup (GL ι K)) : Set (GL ι K))`. Rewrite using `[coe_patSubgroup h]`. Conclude with `hu`.

Establish `hinv : u⁻¹ ∈ patSet K Φ`. Rewrite using `[← coe_patSubgroup h]`. Conclude with `(patSubgroup (K := K) h).inv_mem hu'`. Establish `hm` using `patChar_mul h hE ψ₀ hu hinv`. Rewrite `hm` using `[mul_inv_cancel, patChar_one h hE ψ₀]`.

Conclude with `eq_inv_of_mul_eq_one_right hm.symm`.
-/
theorem patGroup : ReciprocityTheory.Ty.Fin.St.PatGroup := by
  intro K _ _ _ ι _ _ Φ h
  refine ⟨⟨patSubgroup h, coe_patSubgroup h⟩, card_patSet h, fun E ψ₀ hE =>
    ⟨fun u hu v hv => patChar_mul h hE ψ₀ hu hv, patChar_one h hE ψ₀, fun u hu => ?_,
      fun V _ _ _ ρ => exists_nat_wh h hE ψ₀ ρ⟩⟩
  have hu' : u ∈ ((patSubgroup h : Subgroup (GL ι K)) : Set (GL ι K)) := by
    rw [coe_patSubgroup h]
    exact hu
  have hinv : u⁻¹ ∈ patSet K Φ := by
    rw [← coe_patSubgroup h]
    exact (patSubgroup (K := K) h).inv_mem hu'
  have hm := patChar_mul h hE ψ₀ hu hinv
  rw [mul_inv_cancel, patChar_one h hE ψ₀] at hm
  exact eq_inv_of_mul_eq_one_right hm.symm

end GlobalTheory.CompanionTheory.PatGrp

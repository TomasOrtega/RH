import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.RatBasisLinearIndependentInt
open DividedPowers GlobalTheory.Cris GlobalTheory.PDA

namespace GlobalTheory.DerFil

/- English proof (translation)
The claim follows from `Ideal.span_mono fun _ ⟨l, h1, h2, h3⟩ ↦ ⟨l, h1, by omega, h3⟩`.
-/
theorem fil_succ_le {B : Type} [CommRing B] {J : Ideal B} (δ : DividedPowers J) (N : ℕ) :
    fil δ (N + 1) ≤ fil δ N :=
  Ideal.span_mono fun _ ⟨l, h1, h2, h3⟩ ↦ ⟨l, h1, by omega, h3⟩

/- English proof (translation)
The claim follows from `Ideal.subset_span ⟨l, hl, hN, rfl⟩`.
-/
theorem prod_mem_fil {B : Type} [CommRing B] {J : Ideal B} (δ : DividedPowers J) (N : ℕ)
    (l : List (ℕ × B)) (hl : ∀ p ∈ l, p.2 ∈ J) (hN : N ≤ (l.map Prod.fst).sum) :
    (l.map fun p ↦ δ.dpow p.1 p.2).prod ∈ fil δ N :=
  Ideal.subset_span ⟨l, hl, hN, rfl⟩

/- English proof (translation)
Introduce `l`. Proceed by induction on `l with`. Consider the case `nil => intro _ l' _ _`. Simplify using the standard rewrite rules. Consider the case `cons p l ih`.

Introduce `hl l' hl' hs`. Establish `hp : p.2 ∈ J` using `hl p (by simp)`. Establish `hl2 : ∀ q ∈ l, q.2 ∈ J` using `fun q hq ↦ hl q (by simp [hq])`. Simplify using `only [List.map_cons, List.prod_cons, List.sum_cons] at hs ⊢`. Rewrite using `[Derivation.leibniz, smul_add, smul_smul, smul_smul]`.

Use `add_mem ?_ ?_` and prove the remaining obligations. Establish `hl3 : ∀ q ∈ p :: l', q.2 ∈ J`. Introduce `q hq`. Break down `List.mem_cons.1 hq with rfl | hq` into its components or cases. Conclude with `hp`.

Conclude with `hl' q hq`. Use `ih hl2 (p :: l') hl3 (by simp only [List.map_cons, List.sum_cons]; omega)` as an intermediate fact. Simplify `this` using `only [List.map_cons, List.prod_cons, mul_comm]`. Break down `p with ⟨k, x⟩` into its components or cases. Consider the cases of `k with`.

Consider the case `zero => simp [δ.dpow_zero hp]`. Consider the case `succ m`. Establish `h` using `hD m x hp`. Use `set c := (l'.map fun p ↦ δ.dpow p.1 p.2).prod * (l.map fun p ↦ δ.dpow p.1 p.2).prod`. Establish `e : c • D (δ.dpow (m + 1) x) = c • (D (δ.dpow (m + 1) x) - δ.dpow m x • D x) + (c * δ.dpow m x) • D x`.

Rewrite using `[smul_sub, smul_smul, sub_add_cancel]`. Rewrite using `[e]`. Use `add_mem (Submodule.mem_sup_right (N₀.smul_mem _ h)) (Submodule.mem_sup_left ?_)` and prove the remaining obligations. Use `Submodule.smul_mem_smul ?_ Submodule.mem_top` and prove the remaining obligations. Establish `hm` using `prod_mem_fil δ N (l' ++ (m, x) :: l) (by`.

Introduce `q hq`. Break down `List.mem_append.1 hq with hq | hq` into its components or cases. Conclude with `hl' q hq`. Break down `List.mem_cons.1 hq with rfl | hq` into its components or cases. Conclude with `hp`.

Conclude with `hl2 q hq)`. Use the proof step `(by simp only [List.map_append, List.map_cons, List.sum_append, List.sum_cons] at hs ⊢; omega)`. Simplify using `only [List.map_append, List.map_cons, List.prod_append, List.prod_cons] at hm`. Use `hm using 1` and compare the differences between its conclusion and the goal. Simplify using `only [c]`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem smul_deriv_prod_mem {R B M : Type} [CommRing R] [CommRing B] [Algebra R B] [AddCommGroup M]
    [Module B M] [Module R M] [IsScalarTower R B M] (J : Ideal B) (δ : DividedPowers J)
    (D : Derivation R B M) (N₀ : Submodule B M)
    (hD : ∀ n, ∀ a ∈ J, D (δ.dpow (n + 1) a) - δ.dpow n a • D a ∈ N₀) (N : ℕ) :
    ∀ (l : List (ℕ × B)), (∀ p ∈ l, p.2 ∈ J) → ∀ (l' : List (ℕ × B)), (∀ p ∈ l', p.2 ∈ J) →
      N + 1 ≤ (l'.map Prod.fst).sum + (l.map Prod.fst).sum →
      (l'.map fun p ↦ δ.dpow p.1 p.2).prod • D ((l.map fun p ↦ δ.dpow p.1 p.2).prod) ∈
        fil δ N • (⊤ : Submodule B M) ⊔ N₀ := by
  intro l
  induction l with
  | nil => intro _ l' _ _; simp
  | cons p l ih =>
    intro hl l' hl' hs
    have hp : p.2 ∈ J := hl p (by simp)
    have hl2 : ∀ q ∈ l, q.2 ∈ J := fun q hq ↦ hl q (by simp [hq])
    simp only [List.map_cons, List.prod_cons, List.sum_cons] at hs ⊢
    rw [Derivation.leibniz, smul_add, smul_smul, smul_smul]
    refine add_mem ?_ ?_
    · have hl3 : ∀ q ∈ p :: l', q.2 ∈ J := by
        intro q hq
        rcases List.mem_cons.1 hq with rfl | hq
        · exact hp
        · exact hl' q hq
      have := ih hl2 (p :: l') hl3 (by simp only [List.map_cons, List.sum_cons]; omega)
      simpa only [List.map_cons, List.prod_cons, mul_comm] using this
    · rcases p with ⟨k, x⟩
      cases k with
      | zero => simp [δ.dpow_zero hp]
      | succ m =>
        have h := hD m x hp
        set c := (l'.map fun p ↦ δ.dpow p.1 p.2).prod * (l.map fun p ↦ δ.dpow p.1 p.2).prod
        have e : c • D (δ.dpow (m + 1) x) =
            c • (D (δ.dpow (m + 1) x) - δ.dpow m x • D x) + (c * δ.dpow m x) • D x := by
          rw [smul_sub, smul_smul, sub_add_cancel]
        rw [e]
        refine add_mem (Submodule.mem_sup_right (N₀.smul_mem _ h)) (Submodule.mem_sup_left ?_)
        refine Submodule.smul_mem_smul ?_ Submodule.mem_top
        have hm := prod_mem_fil δ N (l' ++ (m, x) :: l)
          (by
            intro q hq
            rcases List.mem_append.1 hq with hq | hq
            · exact hl' q hq
            · rcases List.mem_cons.1 hq with rfl | hq
              · exact hp
              · exact hl2 q hq)
          (by simp only [List.map_append, List.map_cons, List.sum_append, List.sum_cons] at hs ⊢; omega)
        simp only [List.map_append, List.map_cons, List.prod_append, List.prod_cons] at hm
        convert hm using 1
        simp only [c]; ring

end GlobalTheory.DerFil

open GlobalTheory.DerFil in

/- English proof (translation)
Introduce `R B M _ _ _ _ _ _ _ J δ D N₀ hD N x hx`. Proceed by induction on `hx using Submodule.span_induction with`. Consider the case `mem b hb`. Take `⟨l, hl, hs, rfl⟩` from `hb`. Simplify `hs)` using `using smul_deriv_prod_mem J δ D N₀ hD N l hl [] (by simp) (by simpa`.

Consider the case `zero => simp`. Consider the case `add x y _ _ hx hy => rw [map_add]`. Conclude with `add_mem hx hy`. Consider the case `smul c x hx ih`. Rewrite using `[smul_eq_mul, Derivation.leibniz]`.

Conclude with `add_mem (Submodule.smul_mem _ _ ih) (Submodule.mem_sup_left (Submodule.smul_mem_smul (fil_succ_le δ N hx) Submodule.mem_top))`.
-/
theorem GlobalTheory.DerFil.deriv_fil_succ_le : ∀ (R B M : Type) [CommRing R] [CommRing B] [Algebra R B] [AddCommGroup M]
    [Module B M] [Module R M] [IsScalarTower R B M] (J : Ideal B) (δ : DividedPowers J) (D : Derivation R B M)
    (N₀ : Submodule B M), (∀ n, ∀ a ∈ J, D (δ.dpow (n + 1) a) - δ.dpow n a • D a ∈ N₀) →
    ∀ N, ∀ x ∈ fil δ (N + 1), D x ∈ fil δ N • (⊤ : Submodule B M) ⊔ N₀ := by
  intro R B M _ _ _ _ _ _ _ J δ D N₀ hD N x hx
  induction hx using Submodule.span_induction with
  | mem b hb =>
    obtain ⟨l, hl, hs, rfl⟩ := hb
    simpa using smul_deriv_prod_mem J δ D N₀ hD N l hl [] (by simp) (by simpa using hs)
  | zero => simp
  | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
  | smul c x hx ih =>
    rw [smul_eq_mul, Derivation.leibniz]
    exact add_mem (Submodule.smul_mem _ _ ih)
      (Submodule.mem_sup_left (Submodule.smul_mem_smul (fil_succ_le δ N hx) Submodule.mem_top))

import Mathlib
import Development.AutomorphicSpectrum.Definitions.JetCones.SymCapRev
import Formalism.RealPlaceAnalysis.ThirdArithmeticHolds
import Formalism.RealPlaceAnalysis.FinalF
open GlobalTheory.CompanionTheory.AlgRepEndIrreducible PI.UpqRep Matrix
open scoped InnerProductSpace

namespace GlobalTheory.CompanionTheory.AlgRepEndIrreducible.Vev

private noncomputable def ev {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] {n : ℕ}
    (D : Fin n → Fin n → Module.End ℂ V) (v : V) (l : List (Fin n × Fin n)) : ℂ :=
  ⟪v, (l.map fun x => D x.1 x.2).prod v⟫_ℂ

/- English proof (translation)
Establish `h1` using `h x.1 x.2 y.1 y.2 hx hy`. Establish `h2 : D x.1 x.2 * D y.1 y.2 = D y.1 y.2 * D x.1 x.2 + (if x.2 = y.1 then D x.1 y.2 else 0) - (if y.2 = x.1 then D y.1 x.2 else 0)`. Rewrite using `[add_sub_assoc, ← h1]`. Normalize the expressions using the abelian group laws. Simplify using `only [ev, List.map_append, List.map_cons, List.prod_append, List.prod_cons, List.map_nil, List.prod_nil, mul_one]`.

Rewrite using `[← mul_assoc (D x.1 x.2), h2]`. Apply the tactic sequence `split_ifs <;>`. Simplify using `[mul_add, add_mul, mul_sub, sub_mul, mul_assoc, inner_add_right, inner_sub_right]`.
-/
private theorem ev_swap {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] {n : ℕ}
    {ε : Fin n → Bool} {D : Fin n → Fin n → Module.End ℂ V} (h : KRel ε D) (v : V)
    (l₁ l₂ : List (Fin n × Fin n)) (x y : Fin n × Fin n) (hx : ε x.1 = ε x.2) (hy : ε y.1 = ε y.2) :
    ev D v (l₁ ++ x :: y :: l₂) = ev D v ((l₁ ++ [y]) ++ x :: l₂)
      + (if x.2 = y.1 then ev D v (l₁ ++ (x.1, y.2) :: l₂) else 0)
      - (if y.2 = x.1 then ev D v (l₁ ++ (y.1, x.2) :: l₂) else 0) := by
  have h1 := h x.1 x.2 y.1 y.2 hx hy
  have h2 : D x.1 x.2 * D y.1 y.2 = D y.1 y.2 * D x.1 x.2 + (if x.2 = y.1 then D x.1 y.2 else 0)
      - (if y.2 = x.1 then D y.1 x.2 else 0) := by
    rw [add_sub_assoc, ← h1]; abel
  simp only [ev, List.map_append, List.map_cons, List.prod_append, List.prod_cons, List.map_nil,
    List.prod_nil, mul_one]
  rw [← mul_assoc (D x.1 x.2), h2]
  split_ifs <;>
    simp [mul_add, add_mul, mul_sub, sub_mul, mul_assoc, inner_add_right, inner_sub_right]

/- English proof (translation)
Simplify using `only [ev, List.map_append, List.map_cons, List.prod_append, List.prod_cons, List.map_nil, List.prod_nil, mul_one, Module.End.mul_apply]`. Use `split_ifs with he`. Rewrite using `[← he, h.1 x.1, map_smul, inner_smul_right]`. Rewrite using `[h.2 x.1 x.2 (lt_of_le_of_ne hle he) hx]`. Simplify using the standard rewrite rules.
-/
private theorem ev_last {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] {n : ℕ}
    {ε : Fin n → Bool} {D : Fin n → Fin n → Module.End ℂ V} {μ : Fin n → ℝ} {v : V}
    (h : Formalism.REAL.KHighest ε D μ v)
    (l₁ : List (Fin n × Fin n)) (x : Fin n × Fin n) (hx : ε x.1 = ε x.2) (hle : x.1 ≤ x.2) :
    ev D v (l₁ ++ [x]) = (if x.1 = x.2 then (μ x.1 : ℂ) else 0) * ev D v l₁ := by
  simp only [ev, List.map_append, List.map_cons, List.prod_append, List.prod_cons, List.map_nil,
    List.prod_nil, mul_one, Module.End.mul_apply]
  split_ifs with he
  · rw [← he, h.1 x.1, map_smul, inner_smul_right]
  · rw [h.2 x.1 x.2 (lt_of_le_of_ne hle he) hx]; simp

/- English proof (translation)
Simplify using `only [ev, List.map_cons, List.prod_cons, Module.End.mul_apply]`. Rewrite using `[← ha x.2 x.1 hx.symm, h.2 x.2 x.1 hlt hx.symm, inner_zero_left]`.
-/
private theorem ev_first {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] {n : ℕ}
    {ε : Fin n → Bool} {D : Fin n → Fin n → Module.End ℂ V} {μ : Fin n → ℝ} {v : V}
    (ha : KAdj ε D) (h : Formalism.REAL.KHighest ε D μ v)
    (l : List (Fin n × Fin n)) (x : Fin n × Fin n) (hx : ε x.1 = ε x.2) (hlt : x.2 < x.1) :
    ev D v (x :: l) = 0 := by
  simp only [ev, List.map_cons, List.prod_cons, Module.End.mul_apply]
  rw [← ha x.2 x.1 hx.symm, h.2 x.2 x.1 hlt hx.symm, inner_zero_left]

/- English proof (translation)
Introduce `n ε V V' _ _ _ _ D D' μ v v' hR hR' hA hA' hH hH'`. It suffices to establish `H : ∀ (N : ℕ) (l : List (Fin n × Fin n)), l.length = N → (∀ x ∈ l, ε x.1 = ε x.2) → ev D v l * ⟪v', v'⟫_ℂ = ev D' v' l * ⟪v, v⟫_ℂ from fun l hl => H _ l rfl hl`. Introduce `N`. Proceed by induction on `N with`. Consider the case `zero`.

Introduce `l hl _`. Take `rfl` from `List.length_eq_zero_iff.mp hl`. Simplify using `only [ev, List.map_nil, List.prod_nil, Module.End.one_apply]`. Expand and normalize the polynomial expressions, which then agree. Consider the case `succ N ih`.

Establish `key : ∀ (x : Fin n × Fin n), ε x.1 = ε x.2 → x.1 ≤ x.2 → ∀ (l₂ l₁ : List (Fin n × Fin n)), l₁.length + l₂.length = N → (∀ z ∈ l₁, ε z.1 = ε z.2) → (∀ z ∈ l₂, ε z.1 = ε z.2) → ev D v (l₁ ++ x :: l₂) * ⟪v', v'⟫_ℂ = ev D' v' (l₁ ++ x :: l₂) * ⟪v, v⟫_ℂ`. Introduce `x hx hle l₂`. Proceed by induction on `l₂ with`. Consider the case `nil`. Introduce `l₁ hl h₁ _`.

Rewrite using `[ev_last hH l₁ x hx hle, ev_last hH' l₁ x hx hle, mul_assoc, mul_assoc, ih l₁ (by simpa using hl) h₁]`. Consider the case `cons y l₂ ih₂`. Introduce `l₁ hl h₁ h₂`. Establish `hy : ε y.1 = ε y.2` using `h₂ y (by simp)`. Establish `h₂' : ∀ z ∈ l₂, ε z.1 = ε z.2` using `fun z hz => h₂ z (by simp [hz])`.

Establish `hs : ∀ w : Fin n × Fin n, ε w.1 = ε w.2 → ev D v (l₁ ++ w :: l₂) * ⟪v', v'⟫_ℂ = ev D' v' (l₁ ++ w :: l₂) * ⟪v, v⟫_ℂ`. Introduce `w hw`. Use `ih _ (by simpa using hl) ?_` and prove the remaining obligations. Introduce `z hz`. Simplify using `only [List.mem_append, List.mem_cons] at hz`.

Break down `hz with hz | rfl | hz` into its components or cases. Use `exacts [h₁ z hz, hw, h₂' z hz]`. Establish `hm` using `ih₂ (l₁ ++ [y]) (by simp at hl ⊢; omega) (by`. Introduce `z hz`. Simplify using `only [List.mem_append, List.mem_singleton] at hz`.

Break down `hz with hz | rfl` into its components or cases. Use `exacts [h₁ z hz, hy]) h₂'`. Rewrite using `[ev_swap hR v l₁ l₂ x y hx hy, ev_swap hR' v' l₁ l₂ x y hx hy]`. Simplify using `only [sub_mul, add_mul, hm, ite_mul, zero_mul]`. Use `congr 1`.

Use `congr 1 split_ifs with e`. Conclude with `hs _ (by simp only; rw [hx, e, hy])`. Both sides reduce to the same expression. Use `split_ifs with e`. Conclude with `hs _ (by simp only; rw [hy, e, hx])`.

Both sides reduce to the same expression. Introduce `l hl hc`. Consider the cases of `l with`. Consider the case `nil => simp at hl`. Consider the case `cons x l`.

Establish `hx : ε x.1 = ε x.2` using `hc x (by simp)`. Break down `le_or_gt x.1 x.2 with hle | hlt` into its components or cases. Conclude with `key x hx hle l [] (by simpa using hl) (by simp) (fun z hz => hc z (by simp [hz]))`. Rewrite using `[ev_first hA hH l x hx hlt, ev_first hA' hH' l x hx hlt]`. Simplify using the standard rewrite rules.
-/
theorem vev_eq : ∀ (n : ℕ) (ε : Fin n → Bool) (V V' : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] [NormedAddCommGroup V'] [InnerProductSpace ℂ V'] (D : Fin n → Fin n → Module.End ℂ V) (D' : Fin n → Fin n → Module.End ℂ V') (μ : Fin n → ℝ) (v : V) (v' : V'), KRel ε D → KRel ε D' → KAdj ε D → KAdj ε D' → Formalism.REAL.KHighest ε D μ v → Formalism.REAL.KHighest ε D' μ v' → ∀ l : List (Fin n × Fin n), (∀ x ∈ l, ε x.1 = ε x.2) → ⟪v, (l.map fun x => D x.1 x.2).prod v⟫_ℂ * ⟪v', v'⟫_ℂ = ⟪v', (l.map fun x => D' x.1 x.2).prod v'⟫_ℂ * ⟪v, v⟫_ℂ := by
  intro n ε V V' _ _ _ _ D D' μ v v' hR hR' hA hA' hH hH'
  suffices H : ∀ (N : ℕ) (l : List (Fin n × Fin n)), l.length = N → (∀ x ∈ l, ε x.1 = ε x.2) →
      ev D v l * ⟪v', v'⟫_ℂ = ev D' v' l * ⟪v, v⟫_ℂ from fun l hl => H _ l rfl hl
  intro N
  induction N with
  | zero =>
    intro l hl _
    obtain rfl := List.length_eq_zero_iff.mp hl
    simp only [ev, List.map_nil, List.prod_nil, Module.End.one_apply]
    ring
  | succ N ih =>
    have key : ∀ (x : Fin n × Fin n), ε x.1 = ε x.2 → x.1 ≤ x.2 → ∀ (l₂ l₁ : List (Fin n × Fin n)),
        l₁.length + l₂.length = N → (∀ z ∈ l₁, ε z.1 = ε z.2) → (∀ z ∈ l₂, ε z.1 = ε z.2) →
        ev D v (l₁ ++ x :: l₂) * ⟪v', v'⟫_ℂ = ev D' v' (l₁ ++ x :: l₂) * ⟪v, v⟫_ℂ := by
      intro x hx hle l₂
      induction l₂ with
      | nil =>
        intro l₁ hl h₁ _
        rw [ev_last hH l₁ x hx hle, ev_last hH' l₁ x hx hle, mul_assoc, mul_assoc,
          ih l₁ (by simpa using hl) h₁]
      | cons y l₂ ih₂ =>
        intro l₁ hl h₁ h₂
        have hy : ε y.1 = ε y.2 := h₂ y (by simp)
        have h₂' : ∀ z ∈ l₂, ε z.1 = ε z.2 := fun z hz => h₂ z (by simp [hz])
        have hs : ∀ w : Fin n × Fin n, ε w.1 = ε w.2 →
            ev D v (l₁ ++ w :: l₂) * ⟪v', v'⟫_ℂ = ev D' v' (l₁ ++ w :: l₂) * ⟪v, v⟫_ℂ := by
          intro w hw
          refine ih _ (by simpa using hl) ?_
          intro z hz
          simp only [List.mem_append, List.mem_cons] at hz
          rcases hz with hz | rfl | hz
          exacts [h₁ z hz, hw, h₂' z hz]
        have hm := ih₂ (l₁ ++ [y]) (by simp at hl ⊢; omega) (by
          intro z hz
          simp only [List.mem_append, List.mem_singleton] at hz
          rcases hz with hz | rfl
          exacts [h₁ z hz, hy]) h₂'
        rw [ev_swap hR v l₁ l₂ x y hx hy, ev_swap hR' v' l₁ l₂ x y hx hy]
        simp only [sub_mul, add_mul, hm, ite_mul, zero_mul]
        congr 1
        · congr 1
          split_ifs with e
          · exact hs _ (by simp only; rw [hx, e, hy])
          · rfl
        · split_ifs with e
          · exact hs _ (by simp only; rw [hy, e, hx])
          · rfl
    intro l hl hc
    cases l with
    | nil => simp at hl
    | cons x l =>
      have hx : ε x.1 = ε x.2 := hc x (by simp)
      rcases le_or_gt x.1 x.2 with hle | hlt
      · exact key x hx hle l [] (by simpa using hl) (by simp) (fun z hz => hc z (by simp [hz]))
      · rw [ev_first hA hH l x hx hlt, ev_first hA' hH' l x hx hlt]; simp

end GlobalTheory.CompanionTheory.AlgRepEndIrreducible.Vev

import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSBArgs
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField Matrix MeasureTheory ValuativeRel
open scoped TensorProduct nonZeroDivisors
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StepData GlobalTheory.StdFrames Formalism.L2.Host Formalism.L2.DIV

namespace GlobalTheory.MovedBound

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

/- English proof (translation)
Establish `h1 : valuation k (ϖ : k) < 1` using `hϖ ▸ uniformizer_lt_one`. Distinguish the cases in `hx : x = 0`. Conclude with `⟨0, by simp [hx]⟩`. Establish `hv : (valuation k x)⁻¹ ≠ 0` using `by simp [hx]`. Take `⟨m, hm⟩` from `exists_pow_lt₀ h1 (Units.mk0 _ hv)`.

Establish `hu : 0 < valuation k (ϖ : k) ^ m`. Rewrite using `[pos_iff_ne_zero]`. Simplify using the standard rewrite rules. Use `⟨m, ?_⟩` and prove the remaining obligations. Establish `hx0 : 0 < valuation k x` using `by rw [pos_iff_ne_zero]; simp [hx]`.

Conclude with `(le_inv_comm₀ hu hx0).1 (by simpa using hm.le)`.
-/
theorem exists_le_inv_pow {ϖ : kˣ} (hϖ : IsUnif ϖ) (x : k) :
    ∃ n : ℕ, valuation k x ≤ (valuation k (ϖ : k) ^ n)⁻¹ := by
  have h1 : valuation k (ϖ : k) < 1 := hϖ ▸ uniformizer_lt_one
  by_cases hx : x = 0
  · exact ⟨0, by simp [hx]⟩
  have hv : (valuation k x)⁻¹ ≠ 0 := by simp [hx]
  obtain ⟨m, hm⟩ := exists_pow_lt₀ h1 (Units.mk0 _ hv)
  have hu : 0 < valuation k (ϖ : k) ^ m := by
    rw [pos_iff_ne_zero]; simp
  refine ⟨m, ?_⟩
  have hx0 : 0 < valuation k x := by rw [pos_iff_ne_zero]; simp [hx]
  exact (le_inv_comm₀ hu hx0).1 (by simpa using hm.le)

/- English proof (translation)
Establish `h1 : valuation k (ϖ : k) < 1` using `hϖ ▸ uniformizer_lt_one`. Establish `hu : 0 < valuation k (ϖ : k) ^ N` using `by rw [pos_iff_ne_zero]; simp`. Conclude with `inv_anti₀ hu (pow_le_pow_right_of_le_one' h1.le h)`.
-/
theorem inv_pow_mono {ϖ : kˣ} (hϖ : IsUnif ϖ) {n N : ℕ} (h : n ≤ N) :
    (valuation k (ϖ : k) ^ n)⁻¹ ≤ (valuation k (ϖ : k) ^ N)⁻¹ := by
  have h1 : valuation k (ϖ : k) < 1 := hϖ ▸ uniformizer_lt_one
  have hu : 0 < valuation k (ϖ : k) ^ N := by rw [pos_iff_ne_zero]; simp
  exact inv_anti₀ hu (pow_le_pow_right_of_le_one' h1.le h)

/- English proof (translation)
Use `choose f hf using h`. Conclude with `⟨s.attach.sup fun a => f a.1 a.2, fun a ha => hP _ _ _ (Finset.le_sup (f := fun a : s => f a.1 a.2) (Finset.mem_attach s ⟨a, ha⟩)) (hf a ha)⟩`.
-/
theorem exists_uniform {α : Type*} (s : Finset α) (P : α → ℕ → Prop)
    (hP : ∀ a n N, n ≤ N → P a n → P a N) (h : ∀ a ∈ s, ∃ n, P a n) : ∃ n, ∀ a ∈ s, P a n := by
  classical
  choose f hf using h
  exact ⟨s.attach.sup fun a => f a.1 a.2, fun a ha =>
    hP _ _ _ (Finset.le_sup (f := fun a : s => f a.1 a.2) (Finset.mem_attach s ⟨a, ha⟩)) (hf a ha)⟩

/- English proof (translation)
Take `⟨N, hN⟩` from `exists_uniform (Finset.univ : Finset (m × n)) (fun rs N => valuation k (P rs.1 rs.2) ≤ (valuation k (ϖ : k) ^ N)⁻¹) (fun _ _ _ h h' => h'.trans (inv_pow_mono hϖ h)) (fun rs _ => exists_le_inv_pow hϖ _)`. Conclude with `⟨N, fun r s => hN (r, s) (Finset.mem_univ _)⟩`.
-/
theorem exists_matrix_bound {ϖ : kˣ} (hϖ : IsUnif ϖ) {m n : Type*} [Fintype m] [Fintype n] (P : Matrix m n k) :
    ∃ N : ℕ, ∀ r s, valuation k (P r s) ≤ (valuation k (ϖ : k) ^ N)⁻¹ := by
  obtain ⟨N, hN⟩ := exists_uniform (Finset.univ : Finset (m × n))
    (fun rs N => valuation k (P rs.1 rs.2) ≤ (valuation k (ϖ : k) ^ N)⁻¹)
    (fun _ _ _ h h' => h'.trans (inv_pow_mono hϖ h)) (fun rs _ => exists_le_inv_pow hϖ _)
  exact ⟨N, fun r s => hN (r, s) (Finset.mem_univ _)⟩

/- English proof (translation)
Rewrite using `[Matrix.mul_apply]`. Use `Valuation.map_sum_le _ fun j _ => ?_` and prove the remaining obligations. Rewrite using `[map_mul, Matrix.mul_apply]`. Use `mul_le_mul' (Valuation.map_sum_le _ fun i _ => ?_) (hQ _ _)` and prove the remaining obligations. Rewrite using `[map_mul]`.

Conclude with `mul_le_mul' (hP _ _) (hX _ _)`.
-/
theorem val_mul_mul_le {a b c d : Type*} [Fintype b] [Fintype c] (P : Matrix a b k) (X : Matrix b c k)
    (Q : Matrix c d k) (p x q : ValueGroupWithZero k) (hP : ∀ r s, valuation k (P r s) ≤ p)
    (hX : ∀ r s, valuation k (X r s) ≤ x) (hQ : ∀ r s, valuation k (Q r s) ≤ q) (r : a) (s : d) :
    valuation k ((P * X * Q) r s) ≤ p * x * q := by
  rw [Matrix.mul_apply]
  refine Valuation.map_sum_le _ fun j _ => ?_
  rw [map_mul, Matrix.mul_apply]
  refine mul_le_mul' (Valuation.map_sum_le _ fun i _ => ?_) (hQ _ _)
  rw [map_mul]
  exact mul_le_mul' (hP _ _) (hX _ _)

end GlobalTheory.MovedBound

namespace GlobalTheory.MovedBound

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

/- English proof (translation)
Simplify using `[Units.val_inv_eq_inv_val, Units.val_pow_eq_pow_val, map_inv₀, map_pow]`.
-/
theorem val_unitsPow_inv (ϖ : kˣ) (n : ℕ) :
    valuation k (((ϖ ^ n)⁻¹ : kˣ) : k) = (valuation k (ϖ : k) ^ n)⁻¹ := by
  simp [Units.val_inv_eq_inv_val, Units.val_pow_eq_pow_val, map_inv₀, map_pow]

/- English proof (translation)
Simplify using `[Units.val_pow_eq_pow_val, map_pow]`.
-/
theorem val_unitsPow (ϖ : kˣ) (n : ℕ) :
    valuation k ((ϖ ^ n : kˣ) : k) = valuation k (ϖ : k) ^ n := by
  simp [Units.val_pow_eq_pow_val, map_pow]

end GlobalTheory.MovedBound

open GlobalTheory.MovedBound in

/- English proof (translation)
Introduce `k _ _ _ _ G ϖ e T keep g hϖ hT`. Use `set u := valuation k (ϖ : k) with hu_def`. Establish `hu0 : u ≠ 0` using `by simp [u]`. Establish `hu1 : u ≤ 1` using `(hϖ ▸ uniformizer_lt_one).le`. Set `A : ∀ b : Edge, Matrix (Fin (G.rank b.tgt)) (Fin (G.rank b.tgt)) k` to `fun b => ((Assignment.one.read (g b.tgt))⁻¹).val`.

Set `Ai : ∀ b : Edge, Matrix (Fin (G.rank b.tgt)) (Fin (G.rank b.tgt)) k` to `fun b => (Assignment.one.read (g b.tgt)).val`. Set `B : ∀ b : Edge, Matrix (Fin (G.rank b.src)) (Fin (G.rank b.src)) k` to `fun b => (Assignment.one.read (g b.src)).val`. Set `Bi : ∀ b : Edge, Matrix (Fin (G.rank b.src)) (Fin (G.rank b.src)) k` to `fun b => ((Assignment.one.read (g b.src))⁻¹).val`. Take `⟨n0, hn0⟩` from `exists_uniform (oppositePath G.m).toFinset (fun b N => (∀ r s, valuation k (A b r s) ≤ (u ^ N)⁻¹) ∧ (∀ r s, valuation k (Ai b r s) ≤ (u ^ N)⁻¹) ∧ (∀ r s, valuation k (B b r s) ≤ (u ^ N)⁻¹) ∧ (∀ r s, valuation k (Bi b r s) ≤ (u ^ N)⁻¹)) (fun _ _ _ h ⟨h1, h2, h3, h4⟩ => ⟨fun r s => …`. Take `⟨n1, h1⟩` from `exists_matrix_bound hϖ (A b)`.

Take `⟨n2, h2⟩` from `exists_matrix_bound hϖ (Ai b)`. Take `⟨n3, h3⟩` from `exists_matrix_bound hϖ (B b)`. Take `⟨n4, h4⟩` from `exists_matrix_bound hϖ (Bi b)`. Use `⟨n1 + n2 + n3 + n4, fun r s => (h1 r s).trans (inv_pow_mono hϖ (by omega)), fun r s => (h2 r s).trans (inv_pow_mono hϖ (by omega)), fun r s => (h3 r s).trans (inv_pow_mono hϖ (by omega)), fun r s => (h4 r s).trans (inv_pow_mono hϖ (by omega))⟩)` and prove the remaining obligations. Establish `hmv : ∀ x : G.Args, ∀ b, G.moveArgs .one g x b = A b * x b * B b` using `fun _ _ => rfl`.

Use `⟨2 * n0 + e, ?_, ?_⟩` and prove the remaining obligations. Introduce `z hz b hb r s`. Establish `hT0 : T (G.moveArgs .one g z) ≠ 0`. Introduce `h0`. Apply `hz` to reduce the goal to its premises.

Simplify using `[moved, Grid.pathAct, h0]`. Establish `hint : G.moveArgs .one g z b ∈ matLat _ (stdLat k _)`. Assume the negation of the conclusion as `hc`. Conclude with `hT0 (hT.2.1 _ b hb hc)`. Establish `hint'` using `mem_matLat_stdLat.1 hint`.

Establish `hz' : z b = Ai b * G.moveArgs .one g z b * Bi b`. Simplify using `[hmv, A, Ai, B, Bi, ← Matrix.mul_assoc]`. Take `⟨-, h2, -, h4⟩` from `hn0 b (List.mem_toFinset.2 hb)`. Rewrite using `[hz', val_unitsPow_inv]`. Use `(val_mul_mul_le _ _ _ _ 1 _ h2 (fun r s => (hint' r s)) h4 r s).trans ?_` and prove the remaining obligations.

Rewrite using `[mul_one, ← mul_inv, ← pow_add]`. Conclude with `inv_pow_mono hϖ (by omega)`. Introduce `z δ hδ`. Set `δ' : G.Args` to `fun b => if b ∈ oppositePath G.m then G.moveArgs .one g δ b else 0`. Establish `h1 : T (G.moveArgs .one g (z + δ)) = T (G.moveArgs .one g z + δ')`.

Use `hT.1 fun b hb => ?_` and prove the remaining obligations. Simplify using `only [Set.mem_setOf_eq] at hb`. Simplify using `[δ', hb, hmv, Matrix.mul_add, Matrix.add_mul]`. Establish `h2 : T (G.moveArgs .one g z + δ') = T (G.moveArgs .one g z)`. Use `hT.2.2 _ _ fun b => ?_` and prove the remaining obligations.

Distinguish the cases in `hb : b ∈ oppositePath G.m`. Simplify using `only [δ', hb, if_true]`. Take `⟨h1, -, h3, -⟩` from `hn0 b (List.mem_toFinset.2 hb)`. Establish `hd : ∀ r s, valuation k (δ b r s) ≤ u ^ (2 * n0 + e)` using `fun r s => by`. Rewrite using `[← val_unitsPow]`.

Conclude with `hδ b hb r s`. Establish `hbd : ∀ r s, valuation k (G.moveArgs .one g δ b r s) ≤ u ^ e` using `fun r s => by`. Rewrite using `[hmv]`. Use `(val_mul_mul_le _ _ _ _ _ _ h1 hd h3 r s).trans (le_of_eq ?_)` and prove the remaining obligations. Rewrite using `[show 2 * n0 + e = n0 + (n0 + e) by ring, pow_add, pow_add]`.

Clear the denominators using the available nonvanishing facts. Rewrite using `[mem_matLat]`. Introduce `i`. Rewrite using `[mem_smul_lat, mem_stdLat]`. Introduce `j`.

Rewrite using `[Valuation.mem_integer_iff]`. Simplify using `only [Units.smul_def, Pi.smul_apply, smul_eq_mul, Matrix.row_apply]`. Rewrite using `[map_mul, val_unitsPow_inv]`. Combine the equalities or inequalities in the displayed calculation. Simplify using `only [δ', hb, if_false]`.

Conclude with `zero_mem _`. Simplify using `only [moved, Grid.pathAct, h1, h2]`.
-/
theorem GlobalTheory.MovedBound.moved_bounded_locConst : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (G : Grid k) (ϖ : kˣ) (e : ℕ) (T : G.Args → ℂ) (keep : Bool) (g : G.VertexGroup), IsUnif ϖ → G.IsTensor ϖ e (oppositePath G.m) T → ∃ n : ℕ, (∀ z : G.Args, moved G keep g T z ≠ 0 → ∀ b ∈ oppositePath G.m, ∀ r s, valuation k (z b r s) ≤ valuation k (((ϖ ^ n)⁻¹ : kˣ) : k)) ∧ ∀ z δ : G.Args, (∀ b ∈ oppositePath G.m, ∀ r s, valuation k (δ b r s) ≤ valuation k ((ϖ ^ n : kˣ) : k)) → moved G keep g T (z + δ) = moved G keep g T z := by
  intro k _ _ _ _ G ϖ e T keep g hϖ hT
  classical
  set u := valuation k (ϖ : k) with hu_def
  have hu0 : u ≠ 0 := by simp [u]
  have hu1 : u ≤ 1 := (hϖ ▸ uniformizer_lt_one).le
  let A : ∀ b : Edge, Matrix (Fin (G.rank b.tgt)) (Fin (G.rank b.tgt)) k := fun b => ((Assignment.one.read (g b.tgt))⁻¹).val
  let Ai : ∀ b : Edge, Matrix (Fin (G.rank b.tgt)) (Fin (G.rank b.tgt)) k := fun b => (Assignment.one.read (g b.tgt)).val
  let B : ∀ b : Edge, Matrix (Fin (G.rank b.src)) (Fin (G.rank b.src)) k := fun b => (Assignment.one.read (g b.src)).val
  let Bi : ∀ b : Edge, Matrix (Fin (G.rank b.src)) (Fin (G.rank b.src)) k := fun b => ((Assignment.one.read (g b.src))⁻¹).val
  obtain ⟨n0, hn0⟩ := exists_uniform (oppositePath G.m).toFinset
    (fun b N => (∀ r s, valuation k (A b r s) ≤ (u ^ N)⁻¹) ∧ (∀ r s, valuation k (Ai b r s) ≤ (u ^ N)⁻¹) ∧
      (∀ r s, valuation k (B b r s) ≤ (u ^ N)⁻¹) ∧ (∀ r s, valuation k (Bi b r s) ≤ (u ^ N)⁻¹))
    (fun _ _ _ h ⟨h1, h2, h3, h4⟩ => ⟨fun r s => (h1 r s).trans (inv_pow_mono hϖ h),
      fun r s => (h2 r s).trans (inv_pow_mono hϖ h), fun r s => (h3 r s).trans (inv_pow_mono hϖ h),
      fun r s => (h4 r s).trans (inv_pow_mono hϖ h)⟩)
    (fun b _ => by
      obtain ⟨n1, h1⟩ := exists_matrix_bound hϖ (A b)
      obtain ⟨n2, h2⟩ := exists_matrix_bound hϖ (Ai b)
      obtain ⟨n3, h3⟩ := exists_matrix_bound hϖ (B b)
      obtain ⟨n4, h4⟩ := exists_matrix_bound hϖ (Bi b)
      refine ⟨n1 + n2 + n3 + n4, fun r s => (h1 r s).trans (inv_pow_mono hϖ (by omega)),
        fun r s => (h2 r s).trans (inv_pow_mono hϖ (by omega)), fun r s => (h3 r s).trans (inv_pow_mono hϖ (by omega)),
        fun r s => (h4 r s).trans (inv_pow_mono hϖ (by omega))⟩)
  have hmv : ∀ x : G.Args, ∀ b, G.moveArgs .one g x b = A b * x b * B b := fun _ _ => rfl
  refine ⟨2 * n0 + e, ?_, ?_⟩
  · intro z hz b hb r s
    have hT0 : T (G.moveArgs .one g z) ≠ 0 := by
      intro h0; apply hz; simp [moved, Grid.pathAct, h0]
    have hint : G.moveArgs .one g z b ∈ matLat _ (stdLat k _) := by
      by_contra hc; exact hT0 (hT.2.1 _ b hb hc)
    have hint' := mem_matLat_stdLat.1 hint
    have hz' : z b = Ai b * G.moveArgs .one g z b * Bi b := by
      simp [hmv, A, Ai, B, Bi, ← Matrix.mul_assoc]
    obtain ⟨-, h2, -, h4⟩ := hn0 b (List.mem_toFinset.2 hb)
    rw [hz', val_unitsPow_inv]
    refine (val_mul_mul_le _ _ _ _ 1 _ h2 (fun r s => (hint' r s)) h4 r s).trans ?_
    rw [mul_one, ← mul_inv, ← pow_add]
    exact inv_pow_mono hϖ (by omega)
  · intro z δ hδ
    let δ' : G.Args := fun b => if b ∈ oppositePath G.m then G.moveArgs .one g δ b else 0
    have h1 : T (G.moveArgs .one g (z + δ)) = T (G.moveArgs .one g z + δ') := by
      refine hT.1 fun b hb => ?_
      simp only [Set.mem_setOf_eq] at hb
      simp [δ', hb, hmv, Matrix.mul_add, Matrix.add_mul]
    have h2 : T (G.moveArgs .one g z + δ') = T (G.moveArgs .one g z) := by
      refine hT.2.2 _ _ fun b => ?_
      by_cases hb : b ∈ oppositePath G.m
      · simp only [δ', hb, if_true]
        obtain ⟨h1, -, h3, -⟩ := hn0 b (List.mem_toFinset.2 hb)
        have hd : ∀ r s, valuation k (δ b r s) ≤ u ^ (2 * n0 + e) := fun r s => by
          rw [← val_unitsPow]; exact hδ b hb r s
        have hbd : ∀ r s, valuation k (G.moveArgs .one g δ b r s) ≤ u ^ e := fun r s => by
          rw [hmv]
          refine (val_mul_mul_le _ _ _ _ _ _ h1 hd h3 r s).trans (le_of_eq ?_)
          rw [show 2 * n0 + e = n0 + (n0 + e) by ring, pow_add, pow_add]
          field_simp
        rw [mem_matLat]
        intro i
        rw [mem_smul_lat, mem_stdLat]
        intro j
        rw [Valuation.mem_integer_iff]
        simp only [Units.smul_def, Pi.smul_apply, smul_eq_mul, Matrix.row_apply]
        rw [map_mul, val_unitsPow_inv]
        calc (u ^ e)⁻¹ * valuation k (G.moveArgs .one g δ b i j) ≤ (u ^ e)⁻¹ * u ^ e := mul_le_mul' le_rfl (hbd i j)
          _ = 1 := inv_mul_cancel₀ (pow_ne_zero _ hu0)
      · simp only [δ', hb, if_false]
        exact zero_mem _
    simp only [moved, Grid.pathAct, h1, h2]

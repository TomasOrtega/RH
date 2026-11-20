import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ChLApply
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SchwartzBruhatCompAffineMatrixStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IntegralCoordinateShearHaarLocalFieldStatement
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData

noncomputable section
namespace GlobalTheory.PartRed.UpperLaw
open GlobalTheory.PartRed

section Alg
variable {k : Type} [Field k] {n n' : Type} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] {c : ℕ}

def elem (l m : Fin c) (h : l ≠ m) (a : k) : GL (Fin c) k :=
  ⟨transvection l m a, transvection l m (-a),
    by rw [transvection_mul_transvection_same _ _ h]; simp,
    by rw [transvection_mul_transvection_same _ _ h]; simp⟩

/- English proof (translation)
Establish `: (embA n (elem l m h a)).val = fromBlocks 1 0 0 (transvection l m a)` using `rfl`. Rewrite using `[this]`. Apply the tactic sequence `rcases r with r | r <;> rcases s with s | s <;>`. Simplify using `[transvection, Matrix.one_apply, Matrix.single_apply, eq_comm]`.
-/
theorem embA_elem_apply (l m : Fin c) (h : l ≠ m) (a : k) (r s : n ⊕ Fin c) :
    (embA n (elem l m h a)).val r s
      = (1 : Matrix (n ⊕ Fin c) (n ⊕ Fin c) k) r s + if r = Sum.inr l ∧ s = Sum.inr m then a else 0 := by
  have : (embA n (elem l m h a)).val = fromBlocks 1 0 0 (transvection l m a) := rfl
  rw [this]
  rcases r with r | r <;> rcases s with s | s <;>
    simp [transvection, Matrix.one_apply, Matrix.single_apply, eq_comm]

/- English proof (translation)
Use `ext1`. Use `show transvection l m (- -a) = transvection l m a`. Rewrite using `[neg_neg]`.
-/
theorem elem_inv (l m : Fin c) (h : l ≠ m) (a : k) : (elem l m h (-a))⁻¹ = elem l m h a := by
  ext1
  show transvection l m (- -a) = transvection l m a
  rw [neg_neg]

/- English proof (translation)
Simplify using `only [Matrix.mul_apply, embA_elem_apply, add_mul, Finset.sum_add_distrib]`. Use `congr 1`. Simplify using `[Matrix.one_apply]`. Distinguish the cases in `hr : r = Sum.inr l`. Simplify using `[hr]`.

Simplify using `[hr]`.
-/
theorem embA_elem_mul {Q : Type} (l m : Fin c) (h : l ≠ m) (a : k) (t : Matrix (n ⊕ Fin c) Q k) (r : n ⊕ Fin c) (q : Q) :
    ((embA n (elem l m h a)).val * t) r q = t r q + if r = Sum.inr l then a * t (Sum.inr m) q else 0 := by
  simp only [Matrix.mul_apply, embA_elem_apply, add_mul, Finset.sum_add_distrib]
  congr 1
  · simp [Matrix.one_apply]
  · by_cases hr : r = Sum.inr l
    · simp [hr]
    · simp [hr]

/- English proof (translation)
Unfold `simpleSum`. Establish `: ∀ i j : Fin c, (if j.val = i.val + 1 then (embA n (elem l m h a)).val (Sum.inr i) (Sum.inr j) else 0) = if i = l then (if j = m then (if m.val = l.val + 1 then a else 0) else 0) else 0`. Introduce `i j`. Rewrite using `[embA_elem_apply]`. Distinguish the cases in `h1 : j.val = i.val + 1`.

Establish `: i ≠ j` using `by intro e; subst e; omega`. Apply the tactic sequence `by_cases h2 : i = l <;> by_cases h3 : j = m <;> simp_all [Matrix.one_apply]`. Apply the tactic sequence `by_cases h2 : i = l <;> by_cases h3 : j = m <;> simp_all`. Simplify using `[this]`.
-/
theorem simpleSum_elem (l m : Fin c) (h : l ≠ m) (a : k) :
    simpleSum (embA n (elem l m h a)) = if m.val = l.val + 1 then a else 0 := by
  unfold simpleSum
  have : ∀ i j : Fin c, (if j.val = i.val + 1 then (embA n (elem l m h a)).val (Sum.inr i) (Sum.inr j) else 0)
      = if i = l then (if j = m then (if m.val = l.val + 1 then a else 0) else 0) else 0 := by
    intro i j
    rw [embA_elem_apply]
    by_cases h1 : j.val = i.val + 1
    · have : i ≠ j := by intro e; subst e; omega
      by_cases h2 : i = l <;> by_cases h3 : j = m <;> simp_all [Matrix.one_apply]
    · by_cases h2 : i = l <;> by_cases h3 : j = m <;> simp_all
  simp [this]

/- English proof (translation)
Apply `Subgroup.subset_closure` to reduce the goal to its premises. Introduce `r s hrs`. Rewrite using `[embA_elem_apply, if_neg, add_zero]`. Introduce and unpack `⟨rfl, rfl⟩`. Simplify using `only [lev, Sum.elim_inr] at hrs`.

Use linear arithmetic over natural numbers and integers.
-/
theorem elem_mem_N (ρ : ℕ) (l m : Fin c) (h : l ≠ m) (hlm : l.val < m.val) (hm : m.val ≤ ρ) (a : k) :
    embA n (elem l m h a) ∈ N k n c (ρ + 1) := by
  apply Subgroup.subset_closure
  intro r s hrs
  rw [embA_elem_apply, if_neg, add_zero]
  rintro ⟨rfl, rfl⟩
  simp only [lev, Sum.elim_inr] at hrs
  omega

variable {ρ : ℕ} {I : Finset ((n ⊕ Fin c) × (n' ⊕ Fin (c + 1)))}

/- English proof (translation)
Break down `Finset.mem_union.1 (hI he) with h | h` into its components or cases. Simplify using `only [transSet, Finset.mem_filter] at h`. Conclude with `h.2.1`. Simplify using `only [upSet, Finset.mem_filter] at h`. Take `⟨-, l, i, rfl, h1, -⟩` from `h`.

Conclude with `h1`.
-/
theorem free_of_mem (hI : I ⊆ transSet ρ ∪ upSet ρ) {e : (n ⊕ Fin c) × (n' ⊕ Fin (c + 1))} (he : e ∈ I) :
    Free (ρ + 1) e := by
  rcases Finset.mem_union.1 (hI he) with h | h
  · simp only [transSet, Finset.mem_filter] at h
    exact h.2.1
  · simp only [upSet, Finset.mem_filter] at h
    obtain ⟨-, l, i, rfl, h1, -⟩ := h
    exact h1

/- English proof (translation)
Establish `hf : ¬ Free (ρ + 1) ((Sum.inr m, Sum.inr j) : (n ⊕ Fin c) × (n' ⊕ Fin (c + 1)))` using `by show ¬ (m.val < j.val)`. Use linear arithmetic over natural numbers and integers. Establish `h1 : (Sum.inr m, Sum.inr j) ∉ I` using `fun h => hf (free_of_mem hI h)`. Establish `h2 : ((Sum.inr m, Sum.inr j) : (n ⊕ Fin c) × (n' ⊕ Fin (c + 1))) ∈ fixSet ρ ∪ lowSet ρ`. Apply `Finset.mem_union_left` to reduce the goal to its premises.

Simplify using `only [fixSet, Finset.mem_filter, Finset.mem_univ, true_and]`. Conclude with `Or.inl ⟨j, rfl, hm, hf⟩`. Simplify using `only [fillAt, Matrix.of_apply, dif_neg h1, if_pos h2]`. Simplify using `[basePt]`.
-/
theorem fill_low (hI : I ⊆ transSet ρ ∪ upSet ρ) (x : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k) (y : I → k)
    (m : Fin c) (j : Fin (c + 1)) (hj : j.val ≤ m.val) (hm : j.val ≤ ρ) :
    fillAt (basePt c (0 : Matrix n n' k)) (fixSet ρ ∪ lowSet ρ) I x y (Sum.inr m) (Sum.inr j)
      = if m.val = j.val then 1 else 0 := by
  have hf : ¬ Free (ρ + 1) ((Sum.inr m, Sum.inr j) : (n ⊕ Fin c) × (n' ⊕ Fin (c + 1))) := by
    show ¬ (m.val < j.val)
    omega
  have h1 : (Sum.inr m, Sum.inr j) ∉ I := fun h => hf (free_of_mem hI h)
  have h2 : ((Sum.inr m, Sum.inr j) : (n ⊕ Fin c) × (n' ⊕ Fin (c + 1))) ∈ fixSet ρ ∪ lowSet ρ := by
    apply Finset.mem_union_left
    simp only [fixSet, Finset.mem_filter, Finset.mem_univ, true_and]
    exact Or.inl ⟨j, rfl, hm, hf⟩
  simp only [fillAt, Matrix.of_apply, dif_neg h1, if_pos h2]
  simp [basePt]

def shear (ρ : ℕ) (I : Finset ((n ⊕ Fin c) × (n' ⊕ Fin (c + 1)))) (l m : Fin c) (a : k)
    (x : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k) (y : I → k) : I → k :=
  fun e => if e.1.1 = Sum.inr l then
    a * fillAt (basePt c (0 : Matrix n n' k)) (fixSet ρ ∪ lowSet ρ) I x y (Sum.inr m) e.1.2 else 0

/- English proof (translation)
Use extensionality with `r q`. Rewrite using `[embA_elem_mul]`. Distinguish the cases in `hr : (r, q) ∈ I`. Use `conv_rhs => rw [fillAt, Matrix.of_apply, dif_pos hr] conv_lhs => enter [1]`. Rewrite using `[fillAt, Matrix.of_apply, dif_pos hr]`.

Both sides reduce to the same expression. Use `conv_rhs => rw [fillAt, Matrix.of_apply, dif_neg hr] conv_lhs => enter [1]`. Rewrite using `[fillAt, Matrix.of_apply, dif_neg hr]`. Distinguish the cases in `hrl : r = Sum.inr l`. Substitute `hrl` using the available equality.

Rewrite using `[if_pos rfl]`. Establish `hT : ∀ q : n' ⊕ Fin (c + 1), Free (ρ + 1) ((Sum.inr l, q) : (n ⊕ Fin c) × (n' ⊕ Fin (c + 1))) → (∀ j, q = Sum.inr j → ρ < j.val) → (Sum.inr l, q) ∈ I`. Introduce `q hq hq'`. Apply `h1` to reduce the goal to its premises. Simplify using `only [transSet, Finset.mem_filter, Finset.mem_univ, true_and]`.

Conclude with `⟨hq, hq'⟩`. Break down `q with s | j` into its components or cases. Conclude with `absurd (hT (Sum.inl s) (show l.val + 1 < ρ + 1 by omega) (by simp)) hr`. Establish `hj : j.val ≤ i.val`. Assume the negation of the conclusion as `hj`.

Apply `hr` to reduce the goal to its premises. Distinguish the cases in `hρ : ρ < j.val`. Use `hT _ (show l.val < j.val by omega) ?_` and prove the remaining obligations. Introduce `j' e`. Consider the cases of `e`.

Conclude with `hρ`. Apply `h2` to reduce the goal to its premises. Simplify using `only [upSet, Finset.mem_filter, Finset.mem_univ, true_and]`. Conclude with `⟨⟨l, j, rfl, by omega, by omega⟩, by simp only [colIx, Sum.elim_inr]; omega⟩`. Rewrite using `[fill_low hI x y m j (by omega) (by omega)]`.

Distinguish the cases in `hE : ((Sum.inr l, Sum.inr j) : (n ⊕ Fin c) × (n' ⊕ Fin (c + 1))) ∈ fixSet ρ ∪ lowSet ρ`. Rewrite using `[if_pos hE, if_pos hE]`. Establish `: j.val ≤ l.val`. Break down `Finset.mem_union.1 hE with h | h` into its components or cases. Simplify using `only [fixSet, Finset.mem_filter, Finset.mem_univ, true_and] at h`.

Break down `h with ⟨j', e, -, hf⟩ | ⟨_, _, -, -, e⟩` into its components or cases. Establish `: ¬ (l.val < j.val)` using `hf`. Use linear arithmetic over natural numbers and integers. Consider the cases of `e`. Simplify using `only [lowSet, Finset.mem_filter, Finset.mem_univ, true_and] at h`.

Take `⟨l', j', e, -, hf⟩` from `h`. Consider the cases of `e`. Conclude with `hf`. Rewrite using `[if_neg (by omega)]`. Simplify using the standard rewrite rules.

Rewrite using `[if_neg hE, if_neg hE, Matrix.add_apply]`. Use `congr 1`. Distinguish the cases in `hij : i = j`. Substitute `hij` using the available equality. Simplify using `[hmi]`.

Establish `: ¬ m.val = j.val` using `fun e => hij (Fin.ext (by omega))`. Simplify using `[this, hij]`. Rewrite using `[if_neg hrl, add_zero, Matrix.add_apply, Matrix.single_apply_of_ne _ _ _ _ _ (fun e => hrl e.1.symm), add_zero]`.
-/
theorem elem_mul_fill (l m : Fin c) (i : Fin (c + 1)) (h : l ≠ m) (hmi : m.val = i.val) (hl : l.val < i.val)
    (hi : i.val ≤ ρ) (h1 : transSet ρ ⊆ I) (h2 : (upSet ρ).filter (fun e => i.val < colIx e) ⊆ I)
    (hI : I ⊆ transSet ρ ∪ upSet ρ) (hli : (Sum.inr l, Sum.inr i) ∉ I) (a : k)
    (x : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k) (y : I → k) :
    (embA n (elem l m h a)).val * fillAt (basePt c (0 : Matrix n n' k)) (fixSet ρ ∪ lowSet ρ) I x y
      = fillAt (basePt c (0 : Matrix n n' k)) (fixSet ρ ∪ lowSet ρ) I (x + Matrix.single (Sum.inr l) (Sum.inr i) a)
          (y + shear ρ I l m a x y) := by
  ext r q
  rw [embA_elem_mul]
  by_cases hr : (r, q) ∈ I
  · conv_rhs => rw [fillAt, Matrix.of_apply, dif_pos hr]
    conv_lhs => enter [1]; rw [fillAt, Matrix.of_apply, dif_pos hr]
    rfl
  · conv_rhs => rw [fillAt, Matrix.of_apply, dif_neg hr]
    conv_lhs => enter [1]; rw [fillAt, Matrix.of_apply, dif_neg hr]
    by_cases hrl : r = Sum.inr l
    · subst hrl
      rw [if_pos rfl]
      have hT : ∀ q : n' ⊕ Fin (c + 1), Free (ρ + 1) ((Sum.inr l, q) : (n ⊕ Fin c) × (n' ⊕ Fin (c + 1))) →
          (∀ j, q = Sum.inr j → ρ < j.val) → (Sum.inr l, q) ∈ I := by
        intro q hq hq'
        apply h1
        simp only [transSet, Finset.mem_filter, Finset.mem_univ, true_and]
        exact ⟨hq, hq'⟩
      rcases q with s | j
      · exact absurd (hT (Sum.inl s) (show l.val + 1 < ρ + 1 by omega) (by simp)) hr
      · have hj : j.val ≤ i.val := by
          by_contra hj
          apply hr
          by_cases hρ : ρ < j.val
          · refine hT _ (show l.val < j.val by omega) ?_
            intro j' e
            cases e
            exact hρ
          · apply h2
            simp only [upSet, Finset.mem_filter, Finset.mem_univ, true_and]
            exact ⟨⟨l, j, rfl, by omega, by omega⟩, by simp only [colIx, Sum.elim_inr]; omega⟩
        rw [fill_low hI x y m j (by omega) (by omega)]
        by_cases hE : ((Sum.inr l, Sum.inr j) : (n ⊕ Fin c) × (n' ⊕ Fin (c + 1))) ∈ fixSet ρ ∪ lowSet ρ
        · rw [if_pos hE, if_pos hE]
          have : j.val ≤ l.val := by
            rcases Finset.mem_union.1 hE with h | h
            · simp only [fixSet, Finset.mem_filter, Finset.mem_univ, true_and] at h
              rcases h with ⟨j', e, -, hf⟩ | ⟨_, _, -, -, e⟩
              · have : ¬ (l.val < j.val) := hf
                omega
              · cases e
            · simp only [lowSet, Finset.mem_filter, Finset.mem_univ, true_and] at h
              obtain ⟨l', j', e, -, hf⟩ := h
              cases e
              exact hf
          rw [if_neg (by omega)]
          simp
        · rw [if_neg hE, if_neg hE, Matrix.add_apply]
          congr 1
          by_cases hij : i = j
          · subst hij
            simp [hmi]
          · have : ¬ m.val = j.val := fun e => hij (Fin.ext (by omega))
            simp [this, hij]
    · rw [if_neg hrl, add_zero, Matrix.add_apply, Matrix.single_apply_of_ne _ _ _ _ _ (fun e => hrl e.1.symm), add_zero]

/- English proof (translation)
Simplify using `[ch, embA_elem_mul, Finset.sum_add_distrib]`.
-/
theorem ch_elem_mul (l m : Fin c) (h : l ≠ m) (a : k) (t : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k) :
    ch ((embA n (elem l m h a)).val * t) = ch t + a * t (Sum.inr m) (Sum.inr l.succ) := by
  simp [ch, embA_elem_mul, Finset.sum_add_distrib]

end Alg

/- English proof (translation)
Introduce `k _ _ _ _ _ _ ψ ν hψ hν n n' _ _ _ _ c ρ M _ _ L hc hL l i hl hi I h1 h2 hI hli a Φ`. Set `m : Fin c` to `⟨i.val, by omega⟩`. Establish `hmi : m.val = i.val` using `rfl`. Establish `h : l ≠ m` using `by intro e; rw [e] at hl; omega`. Set `d : k` to `if m.val = l.val + 1 then a else 0`.

Set `Φ₁ : SB (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k)` to `⟨fun x => Φ.1 ((embA n (elem l m h a)).val * x + 0), GlobalTheory.T.schwartzBruhat_comp_affine_matrix k _ _ _ 0 Φ.1 Φ.2⟩`. Establish `hΦ₁ : ∀ x, Φ₁.1 x = Φ.1 ((embA n (elem l m h a)).val * x)` using `fun x => by simp only [Φ₁, add_zero]`. Establish `hL₁ : L Φ₁ = (ψ d : ℂ) • L Φ`. Use `hL (elem l m h (-a)) (elem_mem_N ρ l m h (by omega) (by omega) _) Φ Φ₁ (fun t => by` as an intermediate fact. Rewrite using `[hΦ₁, ← map_inv, elem_inv])`.

Rewrite using `[this, simpleSum_elem]`. Use `congr 3`. Simplify using `only [d]`. Apply the tactic sequence `split_ifs <;> simp`. Use `⟨(ψ (-d) : ℂ) • Φ₁, ?_, fun x => ?_⟩` and prove the remaining obligations.

Rewrite using `[map_smul, hL₁, smul_smul, ← Circle.coe_mul, ← AddChar.map_add_eq_mul]`. Simplify using the standard rewrite rules. Unfold `red`. Rewrite using `[← GlobalTheory.T.integral_coordinate_shear_haar_localField k ν hν I (Finset.univ.filter fun e : I => e.1.1 = Sum.inr l) (shear ρ I l m a x) ?_ ?_ ?_ (fun y => Φ.1 (fillAt (basePt c (0 : Matrix n n' k)) (fixSet ρ ∪ lowSet ρ) I (x + Matrix.single (Sum.inr l) (Sum.inr i) a) y) * (ψ …`. Use `congr 1`.

Use function extensionality and compare the values at `y`. Rewrite using `[← elem_mul_fill l m i h hmi hl hi h1 h2 hI hli a x y, chL_apply, chL_apply, ch_elem_mul, fill_low hI x y m l.succ (by rw [Fin.val_succ]; omega) (by rw [Fin.val_succ]; omega)]`. Establish `hd : (a * if m.val = l.succ.val then 1 else 0) = d`. Simplify using `only [d, Fin.val_succ]`. Apply the tactic sequence `split_ifs <;> simp`.

Rewrite using `[hd, Submodule.coe_smul, Pi.smul_apply, hΦ₁, smul_eq_mul, neg_add, AddChar.map_add_eq_mul, Circle.coe_mul]`. Expand and normalize the polynomial expressions, which then agree. Use `continuous_pi fun e => ?_` and prove the remaining obligations. Unfold `shear`. Use `split_ifs`.

Use `continuous_const.mul ?_` and prove the remaining obligations. Simplify using `only [fillAt, Matrix.of_apply]`. Use `split_ifs`. Conclude with `continuous_apply _`. Conclude with `continuous_const`.

Conclude with `continuous_const`. Conclude with `continuous_const`. Introduce `y y' hy`. Use function extensionality and compare the values at `e`. Unfold `shear`.

Use `split_ifs`. Use `congr 1`. Simplify using `only [fillAt, Matrix.of_apply]`. Use `split_ifs with he`. Apply `hy` to reduce the goal to its premises.

Simplify using `only [Finset.mem_filter, Finset.mem_univ, true_and]`. Introduce `e`. Conclude with `h (Sum.inr_injective e).symm`. Both sides reduce to the same expression. Both sides reduce to the same expression.

Both sides reduce to the same expression. Introduce `y j hj`. Simplify using `only [Finset.mem_filter, Finset.mem_univ, true_and] at hj`. Simplify using `only [shear, if_neg hj]`.
-/
theorem intLaw_up : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (ψ : AddChar k Circle) (ν : Measure k), Continuous ψ → ν.IsAddHaarMeasure → ∀ (n n' : Type) [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] (c ρ : ℕ) (M : Type) [AddCommGroup M] [Module ℂ M] (L : SB (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k) →ₗ[ℂ] M), c = 2 * ρ + 1 → (∀ u : GL (Fin c) k, embA n u ∈ N k n c (ρ + 1) → ∀ (Φ Φ' : SB (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k)), (∀ t, Φ'.1 t = Φ.1 (((embA n u)⁻¹).val * t)) → L Φ' = (ψ (-simpleSum (embA n u)) : ℂ) • L Φ) → ∀ (l : Fin c) (i : Fin (c + 1)), l.val < i.val → i.val ≤ ρ → ∀ I : Finset ((n ⊕ Fin c) × (n' ⊕ Fin (c + 1))), GlobalTheory.PartRed.transSet ρ ⊆ I → (GlobalTheory.PartRed.upSet ρ).filter (fun e => i.val < GlobalTheory.PartRed.colIx e) ⊆ I → I ⊆ GlobalTheory.PartRed.transSet ρ ∪ GlobalTheory.PartRed.upSet ρ → (Sum.inr l, Sum.inr i) ∉ I → GlobalTheory.PartRed.IntLaw L ψ ν GlobalTheory.PartRed.chL (basePt c (0 : Matrix n n' k)) (GlobalTheory.PartRed.fixSet ρ ∪ GlobalTheory.PartRed.lowSet ρ) I (Sum.inr l, Sum.inr i) := by
  intro k _ _ _ _ _ _ ψ ν hψ hν n n' _ _ _ _ c ρ M _ _ L hc hL l i hl hi I h1 h2 hI hli a Φ
  let m : Fin c := ⟨i.val, by omega⟩
  have hmi : m.val = i.val := rfl
  have h : l ≠ m := by intro e; rw [e] at hl; omega
  let d : k := if m.val = l.val + 1 then a else 0
  let Φ₁ : SB (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k) :=
    ⟨fun x => Φ.1 ((embA n (elem l m h a)).val * x + 0), GlobalTheory.T.schwartzBruhat_comp_affine_matrix k _ _ _ 0 Φ.1 Φ.2⟩
  have hΦ₁ : ∀ x, Φ₁.1 x = Φ.1 ((embA n (elem l m h a)).val * x) := fun x => by simp only [Φ₁, add_zero]
  have hL₁ : L Φ₁ = (ψ d : ℂ) • L Φ := by
    have := hL (elem l m h (-a)) (elem_mem_N ρ l m h (by omega) (by omega) _) Φ Φ₁ (fun t => by
      rw [hΦ₁, ← map_inv, elem_inv])
    rw [this, simpleSum_elem]
    congr 3
    simp only [d]
    split_ifs <;> simp
  refine ⟨(ψ (-d) : ℂ) • Φ₁, ?_, fun x => ?_⟩
  · rw [map_smul, hL₁, smul_smul, ← Circle.coe_mul, ← AddChar.map_add_eq_mul]
    simp
  · unfold red
    rw [← GlobalTheory.T.integral_coordinate_shear_haar_localField k ν hν I (Finset.univ.filter fun e : I => e.1.1 = Sum.inr l) (shear ρ I l m a x) ?_ ?_ ?_
      (fun y => Φ.1 (fillAt (basePt c (0 : Matrix n n' k)) (fixSet ρ ∪ lowSet ρ) I
        (x + Matrix.single (Sum.inr l) (Sum.inr i) a) y) *
        (ψ (-chL (fillAt (basePt c (0 : Matrix n n' k)) (fixSet ρ ∪ lowSet ρ) I
          (x + Matrix.single (Sum.inr l) (Sum.inr i) a) y)) : ℂ))]
    · congr 1
      funext y
      rw [← elem_mul_fill l m i h hmi hl hi h1 h2 hI hli a x y, chL_apply, chL_apply, ch_elem_mul,
        fill_low hI x y m l.succ (by rw [Fin.val_succ]; omega) (by rw [Fin.val_succ]; omega)]
      have hd : (a * if m.val = l.succ.val then 1 else 0) = d := by
        simp only [d, Fin.val_succ]
        split_ifs <;> simp
      rw [hd, Submodule.coe_smul, Pi.smul_apply, hΦ₁, smul_eq_mul, neg_add, AddChar.map_add_eq_mul, Circle.coe_mul]
      ring
    · refine continuous_pi fun e => ?_
      unfold shear
      split_ifs
      · refine continuous_const.mul ?_
        simp only [fillAt, Matrix.of_apply]
        split_ifs
        · exact continuous_apply _
        · exact continuous_const
        · exact continuous_const
      · exact continuous_const
    · intro y y' hy
      funext e
      unfold shear
      split_ifs
      · congr 1
        simp only [fillAt, Matrix.of_apply]
        split_ifs with he
        · apply hy
          simp only [Finset.mem_filter, Finset.mem_univ, true_and]
          intro e
          exact h (Sum.inr_injective e).symm
        · rfl
        · rfl
      · rfl
    · intro y j hj
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj
      simp only [shear, if_neg hj]

end GlobalTheory.PartRed.UpperLaw

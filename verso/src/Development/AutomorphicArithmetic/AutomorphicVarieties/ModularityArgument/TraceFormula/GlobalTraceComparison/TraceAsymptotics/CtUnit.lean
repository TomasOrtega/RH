import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.TraceAsymptotics.FinprodSplitAlt

noncomputable section

open NumberField IsDedekindDomain Matrix Polynomial Filter Topology
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.LFun
open PositivityTheory.Rg.BcB.G8
open UpperTheory.V.Af.Bc (cPl)
open scoped Classical

namespace UpperTheory.V.Z.Tf.GlobalTraceComparison.Asm

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨a, rfl⟩`. Use `⟨fun i j => (a.val i j).2, fun i j => ?_⟩` and prove the remaining obligations. Rewrite using `[← map_inv]`. Conclude with `((a⁻¹).val i j).2`.

Introduce and unpack `⟨h1, h2⟩`. Set `A : Matrix (Fin n) (Fin n) (Ov E w)` to `fun i j => ⟨g.val i j, h1 i j⟩`. Set `B : Matrix (Fin n) (Fin n) (Ov E w)` to `fun i j => ⟨(g⁻¹).val i j, h2 i j⟩`. Establish `hA : A.map (Ov E w).subtype = g.val` using `by ext i j; rfl`. Establish `hB : B.map (Ov E w).subtype = (g⁻¹).val` using `by ext i j; rfl`.

Establish `inj : Function.Injective (fun M : Matrix (Fin n) (Fin n) (Ov E w) => M.map (Ov E w).subtype)` using `Matrix.map_injective Subtype.val_injective`. Establish `hAB : A * B = 1` using `inj (by`. Express the relevant statement in the definitionally equal form `(A * B).map (Ov E w).subtype = (1 : Matrix (Fin n) (Fin n) (Ov E w)).map (Ov E w).subtype`. Rewrite using `[Matrix.map_mul, hA, hB, Matrix.map_one _ (map_zero _) (map_one _)]`. Conclude with `congrArg Units.val (mul_inv_cancel g))`.

Establish `hBA : B * A = 1` using `inj (by`. Express the relevant statement in the definitionally equal form `(B * A).map (Ov E w).subtype = (1 : Matrix (Fin n) (Fin n) (Ov E w)).map (Ov E w).subtype`. Rewrite using `[Matrix.map_mul, hA, hB, Matrix.map_one _ (map_zero _) (map_one _)]`. Conclude with `congrArg Units.val (inv_mul_cancel g))`. Conclude with `⟨⟨A, B, hAB, hBA⟩, Units.ext hA⟩`.
-/
private lemma mem_K {n : ℕ} {w : Pl E} (g : GLw n w) :
    g ∈ KGL w n ↔ (∀ i j, Valued.v (g.val i j) ≤ 1) ∧ (∀ i j, Valued.v ((g⁻¹).val i j) ≤ 1) := by
  constructor
  · rintro ⟨a, rfl⟩
    refine ⟨fun i j => (a.val i j).2, fun i j => ?_⟩
    rw [← map_inv]
    exact ((a⁻¹).val i j).2
  · rintro ⟨h1, h2⟩
    let A : Matrix (Fin n) (Fin n) (Ov E w) := fun i j => ⟨g.val i j, h1 i j⟩
    let B : Matrix (Fin n) (Fin n) (Ov E w) := fun i j => ⟨(g⁻¹).val i j, h2 i j⟩
    have hA : A.map (Ov E w).subtype = g.val := by ext i j; rfl
    have hB : B.map (Ov E w).subtype = (g⁻¹).val := by ext i j; rfl
    have inj : Function.Injective (fun M : Matrix (Fin n) (Fin n) (Ov E w) => M.map (Ov E w).subtype) :=
      Matrix.map_injective Subtype.val_injective
    have hAB : A * B = 1 := inj (by
      change (A * B).map (Ov E w).subtype = (1 : Matrix (Fin n) (Fin n) (Ov E w)).map (Ov E w).subtype
      rw [Matrix.map_mul, hA, hB, Matrix.map_one _ (map_zero _) (map_one _)]
      exact congrArg Units.val (mul_inv_cancel g))
    have hBA : B * A = 1 := inj (by
      change (B * A).map (Ov E w).subtype = (1 : Matrix (Fin n) (Fin n) (Ov E w)).map (Ov E w).subtype
      rw [Matrix.map_mul, hA, hB, Matrix.map_one _ (map_zero _) (map_one _)]
      exact congrArg Units.val (inv_mul_cancel g))
    exact ⟨⟨A, B, hAB, hBA⟩, Units.ext hA⟩

/- English proof (translation)
Rewrite using `[Matrix.mul_apply]`. Use `Valuation.map_sum_le _ fun k _ => ?_` and prove the remaining obligations. Rewrite using `[map_mul]`. Conclude with `mul_le_one' (hA i k) (hB k j)`.
-/
private lemma int_mul {w : Pl E} {α β γ : Type} [Fintype β] (A : Matrix α β (w.adicCompletion E))
    (B : Matrix β γ (w.adicCompletion E)) (hA : ∀ i j, Valued.v (A i j) ≤ 1) (hB : ∀ i j, Valued.v (B i j) ≤ 1) (i : α) (j : γ) :
    Valued.v ((A * B) i j) ≤ 1 := by
  rw [Matrix.mul_apply]
  refine Valuation.map_sum_le _ fun k _ => ?_
  rw [map_mul]
  exact mul_le_one' (hA i k) (hB k j)

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `h`. Proceed by induction on `h using Subgroup.closure_induction with`. Consider the case `mem x hx => exact hx`. Consider the case `one => intro i j`.

Simplify using the standard rewrite rules. Consider the case `mul x y _ _ hx hy`. Introduce `i j`. Simplify using `using Valuation.map_add_le _ (hx i j) (hy i j)`. Consider the case `inv x _ hx`.

Introduce `i j`. Simplify using `using hx i j`. Conclude with `fun h => Subgroup.subset_closure h`.
-/
private lemma mem_intMat {a b : ℕ} {w : Pl E} (X : Multiplicative (Matrix (Fin a) (Fin b) (w.adicCompletion E))) :
    X ∈ intMat a b w ↔ ∀ i j, Valued.v (Multiplicative.toAdd X i j) ≤ 1 := by
  constructor
  · intro h
    induction h using Subgroup.closure_induction with
    | mem x hx => exact hx
    | one => intro i j; simp
    | mul x y _ _ hx hy =>
      intro i j
      simpa using Valuation.map_add_le _ (hx i j) (hy i j)
    | inv x _ hx =>
      intro i j
      simpa using hx i j
  · exact fun h => Subgroup.subset_closure h

/- English proof (translation)
Establish `h : rStab (fun _ : H => c) = ⊤`. Use extensionality with `k`. Simplify using `[rStab]`. Unfold `avg`. Rewrite using `[h, Subgroup.index_top]`.

Use `haveI : Subsingleton (H ⧸ (⊤ : Subgroup H)) := QuotientGroup.subsingleton_quotient_top`. Use `haveI : Unique (H ⧸ (⊤ : Subgroup H)) := ⟨⟨QuotientGroup.mk 1⟩, fun _ => Subsingleton.elim _ _⟩`. Rewrite using `[finsum_unique]`. Simplify using the standard rewrite rules.
-/
private lemma avg_const {H : Type} [Group H] (c : ℂ) : avg (fun _ : H => c) = c := by
  have h : rStab (fun _ : H => c) = ⊤ := by
    ext k
    simp [rStab]
  unfold avg
  rw [h, Subgroup.index_top]
  haveI : Subsingleton (H ⧸ (⊤ : Subgroup H)) := QuotientGroup.subsingleton_quotient_top
  haveI : Unique (H ⧸ (⊤ : Subgroup H)) := ⟨⟨QuotientGroup.mk 1⟩, fun _ => Subsingleton.elim _ _⟩
  rw [finsum_unique]
  simp

/- English proof (translation)
Simplify using `[hint]`.
-/
private lemma hint_zero {H : Type} [Group H] (K : Subgroup H) : hint K (fun _ : H => (0 : ℂ)) = 0 := by
  simp [hint]

/- English proof (translation)
Establish `hs : rStab ((K : Set H).indicator (1 : H → ℂ)) ⊓ K = K`. Use `inf_eq_right.2 fun k hk x => ?_` and prove the remaining obligations. Distinguish the cases in `hx : x ∈ K`. Rewrite using `[Set.indicator_of_mem (show x * k ∈ (K : Set H) from K.mul_mem hx hk), Set.indicator_of_mem (show x ∈ (K : Set H) from hx)]`. Both sides reduce to the same expression.

Rewrite using `[Set.indicator_of_notMem (show x * k ∉ (K : Set H) from fun h => hx (by simpa using K.mul_mem h (K.inv_mem hk))), Set.indicator_of_notMem (show x ∉ (K : Set H) from hx)]`. Unfold `hint`. Rewrite using `[hs, Subgroup.relIndex_self]`. Rewrite using `[finsum_eq_single _ (QuotientGroup.mk 1 : H ⧸ K)]`. Establish `: Quotient.out (QuotientGroup.mk 1 : H ⧸ K) ∈ K`.

Establish `h` using `QuotientGroup.eq.1 (QuotientGroup.out_eq' (QuotientGroup.mk 1 : H ⧸ K))`. Simplify using `using h`. Rewrite using `[Set.indicator_of_mem (show _ ∈ (K : Set H) from this)]`. Simplify using the standard rewrite rules. Introduce `q hq`.

Use `Set.indicator_of_notMem (fun h => hq ?_) _` and prove the remaining obligations. Rewrite using `[← QuotientGroup.out_eq' q]`. Conclude with `QuotientGroup.eq.2 (by simpa using h)`.
-/
private lemma hint_ind {H : Type} [Group H] (K : Subgroup H) : hint K ((K : Set H).indicator 1) = 1 := by
  have hs : rStab ((K : Set H).indicator (1 : H → ℂ)) ⊓ K = K := by
    refine inf_eq_right.2 fun k hk x => ?_
    by_cases hx : x ∈ K
    · rw [Set.indicator_of_mem (show x * k ∈ (K : Set H) from K.mul_mem hx hk),
        Set.indicator_of_mem (show x ∈ (K : Set H) from hx)]
      rfl
    · rw [Set.indicator_of_notMem (show x * k ∉ (K : Set H) from fun h => hx (by simpa using K.mul_mem h (K.inv_mem hk))),
        Set.indicator_of_notMem (show x ∉ (K : Set H) from hx)]
  unfold hint
  rw [hs, Subgroup.relIndex_self]
  rw [finsum_eq_single _ (QuotientGroup.mk 1 : H ⧸ K)]
  · have : Quotient.out (QuotientGroup.mk 1 : H ⧸ K) ∈ K := by
      have h := QuotientGroup.eq.1 (QuotientGroup.out_eq' (QuotientGroup.mk 1 : H ⧸ K))
      simpa using h
    rw [Set.indicator_of_mem (show _ ∈ (K : Set H) from this)]
    simp
  · intro q hq
    refine Set.indicator_of_notMem (fun h => hq ?_) _
    rw [← QuotientGroup.out_eq' q]
    exact QuotientGroup.eq.2 (by simpa using h)

/- English proof (translation)
Establish `h1 : m.1.val * (m.1⁻¹).val = 1` using `Units.mul_inv m.1`. Establish `h1' : (m.1⁻¹).val * m.1.val = 1` using `Units.inv_mul m.1`. Establish `h2 : m.2.val * (m.2⁻¹).val = 1` using `Units.mul_inv m.2`. Establish `h2' : (m.2⁻¹).val * m.2.val = 1` using `Units.inv_mul m.2`. Use `set e := finSumFinEquiv.trans (finCongr h) with he`.

Establish `hAB : Matrix.fromBlocks m.1.val (m.1.val * X) 0 m.2.val * Matrix.fromBlocks (m.1⁻¹).val (-(X * (m.2⁻¹).val)) 0 (m.2⁻¹).val = 1`. Rewrite using `[Matrix.fromBlocks_multiply]`. Simplify using `[h1, h2, Matrix.mul_assoc]`. Establish `hBA : Matrix.fromBlocks (m.1⁻¹).val (-(X * (m.2⁻¹).val)) 0 (m.2⁻¹).val * Matrix.fromBlocks m.1.val (m.1.val * X) 0 m.2.val = 1`. Rewrite using `[Matrix.fromBlocks_multiply]`.

Simplify using `[h1', h2', Matrix.mul_assoc, ← Matrix.mul_assoc (m.1⁻¹).val]`. Establish `hMN : Matrix.reindex e e (Matrix.fromBlocks m.1.val (m.1.val * X) 0 m.2.val) * Matrix.reindex e e (Matrix.fromBlocks (m.1⁻¹).val (-(X * (m.2⁻¹).val)) 0 (m.2⁻¹).val) = 1`. Simplify using `only [Matrix.reindex_apply, Matrix.submatrix_mul_equiv, hAB, Matrix.submatrix_one_equiv]`. Establish `hNM : Matrix.reindex e e (Matrix.fromBlocks (m.1⁻¹).val (-(X * (m.2⁻¹).val)) 0 (m.2⁻¹).val) * Matrix.reindex e e (Matrix.fromBlocks m.1.val (m.1.val * X) 0 m.2.val) = 1`. Simplify using `only [Matrix.reindex_apply, Matrix.submatrix_mul_equiv, hBA, Matrix.submatrix_one_equiv]`.

Establish `hU : IsUnit (Matrix.reindex e e (Matrix.fromBlocks m.1.val (m.1.val * X) 0 m.2.val))` using `(⟨_, _, hMN, hNM⟩ : (Matrix (Fin n) (Fin n) (w.adicCompletion E))ˣ).isUnit`. Establish `hv : (blk h w m X).val = Matrix.reindex e e (Matrix.fromBlocks m.1.val (m.1.val * X) 0 m.2.val)`. Unfold `blk`. Simplify using `only [← he]`. Rewrite using `[dif_pos hU]`.

Conclude with `hU.unit_spec`. Use `⟨hv, Units.inv_eq_of_mul_eq_one_right ?_⟩` and prove the remaining obligations. Rewrite using `[hv]`. Conclude with `hMN`.
-/
private lemma blk_eq {a b n : ℕ} (h : a + b = n) (w : Pl E) (m : GLw a w × GLw b w)
    (X : Matrix (Fin a) (Fin b) (w.adicCompletion E)) :
    (blk h w m X).val = Matrix.reindex (finSumFinEquiv.trans (finCongr h)) (finSumFinEquiv.trans (finCongr h))
        (Matrix.fromBlocks m.1.val (m.1.val * X) 0 m.2.val) ∧
    ((blk h w m X)⁻¹).val = Matrix.reindex (finSumFinEquiv.trans (finCongr h)) (finSumFinEquiv.trans (finCongr h))
        (Matrix.fromBlocks (m.1⁻¹).val (-(X * (m.2⁻¹).val)) 0 (m.2⁻¹).val) := by
  have h1 : m.1.val * (m.1⁻¹).val = 1 := Units.mul_inv m.1
  have h1' : (m.1⁻¹).val * m.1.val = 1 := Units.inv_mul m.1
  have h2 : m.2.val * (m.2⁻¹).val = 1 := Units.mul_inv m.2
  have h2' : (m.2⁻¹).val * m.2.val = 1 := Units.inv_mul m.2
  set e := finSumFinEquiv.trans (finCongr h) with he
  have hAB : Matrix.fromBlocks m.1.val (m.1.val * X) 0 m.2.val *
      Matrix.fromBlocks (m.1⁻¹).val (-(X * (m.2⁻¹).val)) 0 (m.2⁻¹).val = 1 := by
    rw [Matrix.fromBlocks_multiply]
    simp [h1, h2, Matrix.mul_assoc]
  have hBA : Matrix.fromBlocks (m.1⁻¹).val (-(X * (m.2⁻¹).val)) 0 (m.2⁻¹).val *
      Matrix.fromBlocks m.1.val (m.1.val * X) 0 m.2.val = 1 := by
    rw [Matrix.fromBlocks_multiply]
    simp [h1', h2', Matrix.mul_assoc, ← Matrix.mul_assoc (m.1⁻¹).val]
  have hMN : Matrix.reindex e e (Matrix.fromBlocks m.1.val (m.1.val * X) 0 m.2.val) *
      Matrix.reindex e e (Matrix.fromBlocks (m.1⁻¹).val (-(X * (m.2⁻¹).val)) 0 (m.2⁻¹).val) = 1 := by
    simp only [Matrix.reindex_apply, Matrix.submatrix_mul_equiv, hAB, Matrix.submatrix_one_equiv]
  have hNM : Matrix.reindex e e (Matrix.fromBlocks (m.1⁻¹).val (-(X * (m.2⁻¹).val)) 0 (m.2⁻¹).val) *
      Matrix.reindex e e (Matrix.fromBlocks m.1.val (m.1.val * X) 0 m.2.val) = 1 := by
    simp only [Matrix.reindex_apply, Matrix.submatrix_mul_equiv, hBA, Matrix.submatrix_one_equiv]
  have hU : IsUnit (Matrix.reindex e e (Matrix.fromBlocks m.1.val (m.1.val * X) 0 m.2.val)) :=
    (⟨_, _, hMN, hNM⟩ : (Matrix (Fin n) (Fin n) (w.adicCompletion E))ˣ).isUnit
  have hv : (blk h w m X).val = Matrix.reindex e e (Matrix.fromBlocks m.1.val (m.1.val * X) 0 m.2.val) := by
    unfold blk
    simp only [← he]
    rw [dif_pos hU]
    exact hU.unit_spec
  refine ⟨hv, Units.inv_eq_of_mul_eq_one_right ?_⟩
  rw [hv]
  exact hMN

/- English proof (translation)
Take `⟨hv, hi⟩` from `blk_eq h w m X`. Use `set e := finSumFinEquiv.trans (finCongr h) with he`. Establish `e1 : ∀ (A : Matrix (Fin a) (Fin a) (w.adicCompletion E)) (B : Matrix (Fin a) (Fin b) (w.adicCompletion E)) (C : Matrix (Fin b) (Fin a) (w.adicCompletion E)) (D : Matrix (Fin b) (Fin b) (w.adicCompletion E)) p q, Matrix.reindex e e (Matrix.fromBlocks A B C D) (e p) (e q) = Matrix. …`. Introduce `A B C D p q`. Simplify using `[Matrix.reindex_apply, Matrix.submatrix_apply]`.

Rewrite using `[mem_K, hv, hi]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨g1, g2⟩`. Establish `m1 : ∀ i j, Valued.v (m.1.val i j) ≤ 1` using `fun i j => by`. Use `g1 (e (Sum.inl i)) (e (Sum.inl j))` as an intermediate fact.

Rewrite `this` using `[e1]`. Simplify using `using this`. Establish `m2 : ∀ i j, Valued.v (m.2.val i j) ≤ 1` using `fun i j => by`. Use `g1 (e (Sum.inr i)) (e (Sum.inr j))` as an intermediate fact. Rewrite `this` using `[e1]`.

Simplify using `using this`. Establish `m1X : ∀ i j, Valued.v ((m.1.val * X) i j) ≤ 1` using `fun i j => by`. Use `g1 (e (Sum.inl i)) (e (Sum.inr j))` as an intermediate fact. Rewrite `this` using `[e1]`. Simplify using `using this`.

Establish `i1 : ∀ i j, Valued.v ((m.1⁻¹).val i j) ≤ 1` using `fun i j => by`. Use `g2 (e (Sum.inl i)) (e (Sum.inl j))` as an intermediate fact. Rewrite `this` using `[e1]`. Simplify using `using this`. Establish `i2 : ∀ i j, Valued.v ((m.2⁻¹).val i j) ≤ 1` using `fun i j => by`.

Use `g2 (e (Sum.inr i)) (e (Sum.inr j))` as an intermediate fact. Rewrite `this` using `[e1]`. Simplify using `using this`. Use `⟨Subgroup.mem_prod.2 ⟨(mem_K _).2 ⟨m1, i1⟩, (mem_K _).2 ⟨m2, i2⟩⟩, fun i j => ?_⟩` and prove the remaining obligations. Establish `hX : X = (m.1⁻¹).val * (m.1.val * X)`.

Rewrite using `[← Matrix.mul_assoc, Units.inv_mul m.1, Matrix.one_mul]`. Rewrite using `[hX]`. Conclude with `int_mul _ _ i1 m1X i j`. Introduce and unpack `⟨hm, hX⟩`. Take `⟨k1, k2⟩` from `Subgroup.mem_prod.1 hm`.

Take `⟨m1, i1⟩` from `(mem_K _).1 k1`. Take `⟨m2, i2⟩` from `(mem_K _).1 k2`. Prove the components needed by the constructor for the conclusion. Introduce `i j`. Take `⟨p, rfl⟩` from `e.surjective i`.

Take `⟨q, rfl⟩` from `e.surjective j`. Rewrite using `[e1]`. Apply the tactic sequence `rcases p with p | p <;> rcases q with q | q`. Simplify using `using m1 p q`. Simplify using `using int_mul _ _ m1 hX p q`.

Simplify using the standard rewrite rules. Simplify using `using m2 p q`. Introduce `i j`. Take `⟨p, rfl⟩` from `e.surjective i`. Take `⟨q, rfl⟩` from `e.surjective j`.

Rewrite using `[e1]`. Apply the tactic sequence `rcases p with p | p <;> rcases q with q | q`. Simplify using `using i1 p q`. Simplify using `using int_mul _ _ hX i2 p q`. Simplify using the standard rewrite rules.

Simplify using `using i2 p q`.
-/
private lemma blk_mem_iff {a b n : ℕ} (h : a + b = n) (w : Pl E) (m : GLw a w × GLw b w)
    (X : Matrix (Fin a) (Fin b) (w.adicCompletion E)) :
    blk h w m X ∈ KGL w n ↔ m ∈ K2 a b w ∧ ∀ i j, Valued.v (X i j) ≤ 1 := by
  obtain ⟨hv, hi⟩ := blk_eq h w m X
  set e := finSumFinEquiv.trans (finCongr h) with he
  have e1 : ∀ (A : Matrix (Fin a) (Fin a) (w.adicCompletion E)) (B : Matrix (Fin a) (Fin b) (w.adicCompletion E))
      (C : Matrix (Fin b) (Fin a) (w.adicCompletion E)) (D : Matrix (Fin b) (Fin b) (w.adicCompletion E)) p q,
      Matrix.reindex e e (Matrix.fromBlocks A B C D) (e p) (e q) = Matrix.fromBlocks A B C D p q := by
    intro A B C D p q
    simp [Matrix.reindex_apply, Matrix.submatrix_apply]
  rw [mem_K, hv, hi]
  constructor
  · rintro ⟨g1, g2⟩
    have m1 : ∀ i j, Valued.v (m.1.val i j) ≤ 1 := fun i j => by
      have := g1 (e (Sum.inl i)) (e (Sum.inl j))
      rw [e1] at this
      simpa using this
    have m2 : ∀ i j, Valued.v (m.2.val i j) ≤ 1 := fun i j => by
      have := g1 (e (Sum.inr i)) (e (Sum.inr j))
      rw [e1] at this
      simpa using this
    have m1X : ∀ i j, Valued.v ((m.1.val * X) i j) ≤ 1 := fun i j => by
      have := g1 (e (Sum.inl i)) (e (Sum.inr j))
      rw [e1] at this
      simpa using this
    have i1 : ∀ i j, Valued.v ((m.1⁻¹).val i j) ≤ 1 := fun i j => by
      have := g2 (e (Sum.inl i)) (e (Sum.inl j))
      rw [e1] at this
      simpa using this
    have i2 : ∀ i j, Valued.v ((m.2⁻¹).val i j) ≤ 1 := fun i j => by
      have := g2 (e (Sum.inr i)) (e (Sum.inr j))
      rw [e1] at this
      simpa using this
    refine ⟨Subgroup.mem_prod.2 ⟨(mem_K _).2 ⟨m1, i1⟩, (mem_K _).2 ⟨m2, i2⟩⟩, fun i j => ?_⟩
    have hX : X = (m.1⁻¹).val * (m.1.val * X) := by
      rw [← Matrix.mul_assoc, Units.inv_mul m.1, Matrix.one_mul]
    rw [hX]
    exact int_mul _ _ i1 m1X i j
  · rintro ⟨hm, hX⟩
    obtain ⟨k1, k2⟩ := Subgroup.mem_prod.1 hm
    obtain ⟨m1, i1⟩ := (mem_K _).1 k1
    obtain ⟨m2, i2⟩ := (mem_K _).1 k2
    constructor
    · intro i j
      obtain ⟨p, rfl⟩ := e.surjective i
      obtain ⟨q, rfl⟩ := e.surjective j
      rw [e1]
      rcases p with p | p <;> rcases q with q | q
      · simpa using m1 p q
      · simpa using int_mul _ _ m1 hX p q
      · simp
      · simpa using m2 p q
    · intro i j
      obtain ⟨p, rfl⟩ := e.surjective i
      obtain ⟨q, rfl⟩ := e.surjective j
      rw [e1]
      rcases p with p | p <;> rcases q with q | q
      · simpa using i1 p q
      · simpa using int_mul _ _ hX i2 p q
      · simp
      · simpa using i2 p q

/- English proof (translation)
Establish `h1 : ∀ k ∈ KGL w r, Valued.v (k : GLw r w).val.det ≤ 1`. Introduce and unpack `_ ⟨c, rfl⟩`. Establish `: (GeneralLinearGroup.map (Ov E w).subtype c).val.det = ((c.val.det : Ov E w) : w.adicCompletion E)` using `((Ov E w).subtype.map_det c.val).symm`. Express the relevant statement in the definitionally equal form `Valued.v (GeneralLinearGroup.map (Ov E w).subtype c).val.det ≤ 1`. Rewrite using `[this]`.

Conclude with `c.val.det.2`. Establish `hm : k.val.det * (k⁻¹).val.det = 1`. Rewrite using `[← Matrix.det_mul, Units.mul_inv, Matrix.det_one]`. Establish `hv : Valued.v k.val.det * Valued.v (k⁻¹).val.det = 1`. Rewrite using `[← map_mul, hm, map_one]`.

Use `le_antisymm (h1 k hk) ?_` and prove the remaining obligations. Combine the equalities or inequalities in the displayed calculation.
-/
private lemma det_K {r : ℕ} {w : Pl E} {k : GLw r w} (hk : k ∈ KGL w r) : Valued.v k.val.det = 1 := by
  have h1 : ∀ k ∈ KGL w r, Valued.v (k : GLw r w).val.det ≤ 1 := by
    rintro _ ⟨c, rfl⟩
    have : (GeneralLinearGroup.map (Ov E w).subtype c).val.det = ((c.val.det : Ov E w) : w.adicCompletion E) :=
      ((Ov E w).subtype.map_det c.val).symm
    change Valued.v (GeneralLinearGroup.map (Ov E w).subtype c).val.det ≤ 1
    rw [this]
    exact c.val.det.2
  have hm : k.val.det * (k⁻¹).val.det = 1 := by
    rw [← Matrix.det_mul, Units.mul_inv, Matrix.det_one]
  have hv : Valued.v k.val.det * Valued.v (k⁻¹).val.det = 1 := by
    rw [← map_mul, hm, map_one]
  refine le_antisymm (h1 k hk) ?_
  calc (1 : _) = Valued.v k.val.det * Valued.v (k⁻¹).val.det := hv.symm
    _ ≤ Valued.v k.val.det := mul_le_of_le_one_right' (h1 _ (inv_mem hk))

/- English proof (translation)
Establish `h0 : ordL x = 0`. Establish `hne : Valued.v x ≠ 0` using `by rw [hx]; exact one_ne_zero`. Unfold `ordL`. Rewrite using `[dif_neg hne]`. Establish `: WithZero.unzero hne = 1`.

Apply `WithZero.coe_injective` to reduce the goal to its premises. Rewrite using `[WithZero.coe_unzero, hx]`. Both sides reduce to the same expression. Rewrite using `[this]`. Simplify using the standard rewrite rules.

Simplify using `[absHalf, h0]`.
-/
private lemma absHalf_one {w : Pl E} {x : w.adicCompletion E} (hx : Valued.v x = 1) : absHalf w x = 1 := by
  have h0 : ordL x = 0 := by
    have hne : Valued.v x ≠ 0 := by rw [hx]; exact one_ne_zero
    unfold ordL
    rw [dif_neg hne]
    have : WithZero.unzero hne = 1 := by
      apply WithZero.coe_injective
      rw [WithZero.coe_unzero, hx]
      rfl
    rw [this]
    simp
  simp [absHalf, h0]

end UpperTheory.V.Z.Tf.GlobalTraceComparison.Asm

open UpperTheory.V.Z.Tf.GlobalTraceComparison.Asm in
/- English proof (translation)
Introduce `E _ _ _ w n a b h`. Use function extensionality and compare the values at `m`. Unfold `ct`. Establish `hconj : ∀ y : GLw n w, (avg fun k : KGL w n => (KGL w n : Set (GLw n w)).indicator (1 : GLw n w → ℂ) ((k : GLw n w)⁻¹ * y * k)) = (KGL w n : Set (GLw n w)).indicator (1 : GLw n w → ℂ) y`. Introduce `y`.

Establish `hf : (fun k : KGL w n => (KGL w n : Set (GLw n w)).indicator (1 : GLw n w → ℂ) ((k : GLw n w)⁻¹ * y * k)) = fun _ => (KGL w n : Set (GLw n w)).indicator (1 : GLw n w → ℂ) y`. Use function extensionality and compare the values at `k`. Establish `hiff : (k : GLw n w)⁻¹ * y * k ∈ KGL w n ↔ y ∈ KGL w n`. Prove the components needed by the constructor for the conclusion. Introduce `hy`.

Use `(KGL w n).mul_mem ((KGL w n).mul_mem k.2 hy) ((KGL w n).inv_mem k.2)` as an intermediate fact. Simplify `this` using `[mul_assoc]`. Introduce `hy`. Conclude with `(KGL w n).mul_mem ((KGL w n).mul_mem ((KGL w n).inv_mem k.2) hy) k.2`. Distinguish the cases in `hy : y ∈ KGL w n`.

Rewrite using `[Set.indicator_of_mem (show _ ∈ (KGL w n : Set (GLw n w)) from hiff.2 hy), Set.indicator_of_mem (show _ ∈ (KGL w n : Set (GLw n w)) from hy)]`. Both sides reduce to the same expression. Rewrite using `[Set.indicator_of_notMem (show _ ∉ (KGL w n : Set (GLw n w)) from fun h' => hy (hiff.1 h')), Set.indicator_of_notMem (show _ ∉ (KGL w n : Set (GLw n w)) from hy)]`. Rewrite using `[hf, avg_const]`. Simplify using `only [hconj]`.

Distinguish the cases in `hm : m ∈ K2 a b w`. Establish `hu : (fun X : Multiplicative (Matrix (Fin a) (Fin b) (w.adicCompletion E)) => (KGL w n : Set (GLw n w)).indicator (1 : GLw n w → ℂ) (blk h w m (Multiplicative.toAdd X))) = (intMat a b w : Set _).indicator 1`. Use function extensionality and compare the values at `X`. Distinguish the cases in `hX : X ∈ intMat a b w`. Rewrite using `[Set.indicator_of_mem (show _ ∈ (KGL w n : Set (GLw n w)) from (blk_mem_iff h w m _).2 ⟨hm, (mem_intMat X).1 hX⟩), Set.indicator_of_mem (show X ∈ (intMat a b w : Set _) from hX)]`.

Both sides reduce to the same expression. Rewrite using `[Set.indicator_of_notMem (show _ ∉ (KGL w n : Set (GLw n w)) from fun h' => hX ((mem_intMat X).2 ((blk_mem_iff h w m _).1 h').2)), Set.indicator_of_notMem (show X ∉ (intMat a b w : Set _) from hX)]`. Take `⟨k1, k2⟩` from `Subgroup.mem_prod.1 hm`. Establish `hx : Valued.v (m.1.val.det ^ b / m.2.val.det ^ a) = 1`. Rewrite using `[map_div₀, map_pow, map_pow, det_K k1, det_K k2]`.

Simplify using the standard rewrite rules. Rewrite using `[hu, hint_ind, absHalf_one hx, Set.indicator_of_mem (show m ∈ (K2 a b w : Set _) from hm)]`. Simplify using the standard rewrite rules. Establish `hu : (fun X : Multiplicative (Matrix (Fin a) (Fin b) (w.adicCompletion E)) => (KGL w n : Set (GLw n w)).indicator (1 : GLw n w → ℂ) (blk h w m (Multiplicative.toAdd X))) = fun _ => 0`. Use function extensionality and compare the values at `X`.

Conclude with `Set.indicator_of_notMem (fun h' => hm ((blk_mem_iff h w m _).1 h').1) _`. Rewrite using `[hu, hint_zero, mul_zero, Set.indicator_of_notMem (show m ∉ (K2 a b w : Set _) from hm)]`.
-/
theorem UpperTheory.V.Z.Tf.GlobalTraceComparison.Asm.ctUnit :
    UpperTheory.V.Z.Tf.GlobalTraceComparison.Asm.CtUnit := by
  intro E _ _ _ w n a b h
  funext m
  unfold ct
  have hconj : ∀ y : GLw n w, (avg fun k : KGL w n =>
      (KGL w n : Set (GLw n w)).indicator (1 : GLw n w → ℂ) ((k : GLw n w)⁻¹ * y * k)) =
      (KGL w n : Set (GLw n w)).indicator (1 : GLw n w → ℂ) y := by
    intro y
    have hf : (fun k : KGL w n => (KGL w n : Set (GLw n w)).indicator (1 : GLw n w → ℂ) ((k : GLw n w)⁻¹ * y * k)) =
        fun _ => (KGL w n : Set (GLw n w)).indicator (1 : GLw n w → ℂ) y := by
      funext k
      have hiff : (k : GLw n w)⁻¹ * y * k ∈ KGL w n ↔ y ∈ KGL w n := by
        constructor
        · intro hy
          have := (KGL w n).mul_mem ((KGL w n).mul_mem k.2 hy) ((KGL w n).inv_mem k.2)
          simpa [mul_assoc] using this
        · intro hy
          exact (KGL w n).mul_mem ((KGL w n).mul_mem ((KGL w n).inv_mem k.2) hy) k.2
      by_cases hy : y ∈ KGL w n
      · rw [Set.indicator_of_mem (show _ ∈ (KGL w n : Set (GLw n w)) from hiff.2 hy),
          Set.indicator_of_mem (show _ ∈ (KGL w n : Set (GLw n w)) from hy)]
        rfl
      · rw [Set.indicator_of_notMem (show _ ∉ (KGL w n : Set (GLw n w)) from fun h' => hy (hiff.1 h')),
          Set.indicator_of_notMem (show _ ∉ (KGL w n : Set (GLw n w)) from hy)]
    rw [hf, avg_const]
  simp only [hconj]
  by_cases hm : m ∈ K2 a b w
  · have hu : (fun X : Multiplicative (Matrix (Fin a) (Fin b) (w.adicCompletion E)) =>
        (KGL w n : Set (GLw n w)).indicator (1 : GLw n w → ℂ) (blk h w m (Multiplicative.toAdd X))) =
        (intMat a b w : Set _).indicator 1 := by
      funext X
      by_cases hX : X ∈ intMat a b w
      · rw [Set.indicator_of_mem (show _ ∈ (KGL w n : Set (GLw n w)) from
            (blk_mem_iff h w m _).2 ⟨hm, (mem_intMat X).1 hX⟩),
          Set.indicator_of_mem (show X ∈ (intMat a b w : Set _) from hX)]
        rfl
      · rw [Set.indicator_of_notMem (show _ ∉ (KGL w n : Set (GLw n w)) from
            fun h' => hX ((mem_intMat X).2 ((blk_mem_iff h w m _).1 h').2)),
          Set.indicator_of_notMem (show X ∉ (intMat a b w : Set _) from hX)]
    obtain ⟨k1, k2⟩ := Subgroup.mem_prod.1 hm
    have hx : Valued.v (m.1.val.det ^ b / m.2.val.det ^ a) = 1 := by
      rw [map_div₀, map_pow, map_pow, det_K k1, det_K k2]
      simp
    rw [hu, hint_ind, absHalf_one hx, Set.indicator_of_mem (show m ∈ (K2 a b w : Set _) from hm)]
    simp
  · have hu : (fun X : Multiplicative (Matrix (Fin a) (Fin b) (w.adicCompletion E)) =>
        (KGL w n : Set (GLw n w)).indicator (1 : GLw n w → ℂ) (blk h w m (Multiplicative.toAdd X))) =
        fun _ => 0 := by
      funext X
      exact Set.indicator_of_notMem (fun h' => hm ((blk_mem_iff h w m _).1 h').1) _
    rw [hu, hint_zero, mul_zero, Set.indicator_of_notMem (show m ∉ (K2 a b w : Set _) from hm)]

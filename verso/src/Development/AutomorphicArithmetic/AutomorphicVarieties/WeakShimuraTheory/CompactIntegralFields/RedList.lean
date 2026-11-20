import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.RedIdeal
import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.GeAlgTop

open IsLocalRing Polynomial UpperTheory.V.Alg UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws

private def UpperTheory.V.Ws.redM (a b c d e f g h : Bool) : Fin 4 → Fin 4 → Bool :=
  ![![true, a, b, c], ![d, true, e, b], ![f, g, true, a], ![h, f, d, true]]

/- English proof (translation)
Use `decide +kernel`.
-/
private theorem UpperTheory.V.Ws.redM_key : ∀ a b c d e f g h : Bool,
    (∀ i j k, redM a b c d e f g h i j = true → redM a b c d e f g h j k = true → redM a b c d e f g h i k = true) →
    (∀ i j, redM a b c d e f g h i j = true) ∨
      ∃ S ∈ redTypes, ∀ i j, i ≠ j → wt i j ∉ S → redM a b c d e f g h i j = false := by
  decide +kernel

/- English proof (translation)
Use `decide +kernel`.
-/
private theorem UpperTheory.V.Ws.redT_ex : ∀ S ∈ redTypes, ∃ i j, i ≠ j ∧ wt i j ∉ S := by
  decide +kernel

/- English proof (translation)
Establish `h3 : ∀ i j, G i j ↔ G j.rev i.rev` using `fun i j => ⟨h2 i j, fun h => by simpa using h2 _ _ h⟩`. Establish `hM : ∀ i j, redM (decide (G 0 1)) (decide (G 0 2)) (decide (G 0 3)) (decide (G 1 0)) (decide (G 1 2)) (decide (G 2 0)) (decide (G 2 1)) (decide (G 3 0)) i j = true ↔ G i j`. Establish `e1 : G 0 1 ↔ G 2 3` using `h3 0 1`. Establish `e2 : G 0 2 ↔ G 1 3` using `h3 0 2`. Establish `e3 : G 1 0 ↔ G 3 2` using `h3 1 0`.

Establish `e4 : G 2 0 ↔ G 3 1` using `h3 2 0`. Introduce `i j`. Apply the tactic sequence `fin_cases i <;> fin_cases j <;> simp [redM, h0, e1, e2, e3, e4]`. Break down `redM_key _ _ _ _ _ _ _ _ (fun i j k a b => (hM i k).2 (h1 i j k ((hM i j).1 a) ((hM j k).1 b))) with h | ⟨S, hS, h⟩` into its components or cases. Conclude with `Or.inl fun i j => (hM i j).1 (h i j)`.

Use `Or.inr ⟨S, hS, fun i j hij hw hG => ?_⟩` and prove the remaining obligations. Use `h i j hij hw` as an intermediate fact. Rewrite `this` using `[(hM i j).2 hG]`. Conclude with `Bool.noConfusion this`.
-/
private theorem UpperTheory.V.Ws.red_rel (G : Fin 4 → Fin 4 → Prop) (h0 : ∀ i, G i i)
    (h1 : ∀ i j k, G i j → G j k → G i k) (h2 : ∀ i j, G i j → G j.rev i.rev) :
    (∀ i j, G i j) ∨ ∃ S ∈ redTypes, ∀ i j, i ≠ j → wt i j ∉ S → ¬ G i j := by
  classical
  have h3 : ∀ i j, G i j ↔ G j.rev i.rev := fun i j => ⟨h2 i j, fun h => by simpa using h2 _ _ h⟩
  have hM : ∀ i j, redM (decide (G 0 1)) (decide (G 0 2)) (decide (G 0 3)) (decide (G 1 0)) (decide (G 1 2))
      (decide (G 2 0)) (decide (G 2 1)) (decide (G 3 0)) i j = true ↔ G i j := by
    have e1 : G 0 1 ↔ G 2 3 := h3 0 1
    have e2 : G 0 2 ↔ G 1 3 := h3 0 2
    have e3 : G 1 0 ↔ G 3 2 := h3 1 0
    have e4 : G 2 0 ↔ G 3 1 := h3 2 0
    intro i j
    fin_cases i <;> fin_cases j <;> simp [redM, h0, e1, e2, e3, e4]
  rcases redM_key _ _ _ _ _ _ _ _ (fun i j k a b => (hM i k).2 (h1 i j k ((hM i j).1 a) ((hM j k).1 b))) with h | ⟨S, hS, h⟩
  · exact Or.inl fun i j => (hM i j).1 (h i j)
  · refine Or.inr ⟨S, hS, fun i j hij hw hG => ?_⟩
    have := h i j hij hw
    rw [(hM i j).2 hG] at this
    exact Bool.noConfusion this

/- English proof (translation)
Use `set W := Submodule.span K (Set.range r) with hW`. Establish `hmem : ∀ g, r g ∈ W` using `fun g => Submodule.subset_span ⟨g, rfl⟩`. Establish `hone : (1 : M4 K) ∈ W`. Rewrite using `[← map_one r]`. Conclude with `hmem 1`.

Establish `hmul : ∀ M ∈ W, ∀ N ∈ W, M * N ∈ W`. Introduce `M hM N hN`. Proceed by induction on `hM using Submodule.span_induction with`. Consider the case `mem x hx`. Proceed by induction on `hN using Submodule.span_induction with`.

Consider the case `mem y hy`. Take `⟨a, rfl⟩` from `hx`. Take `⟨b, rfl⟩` from `hy`. Rewrite using `[← map_mul]`. Conclude with `hmem _`.

Consider the case `zero => simp`. Consider the case `add y z _ _ hy hz`. Rewrite using `[mul_add]`. Conclude with `add_mem hy hz`. Consider the case `smul c y _ hy`.

Rewrite using `[mul_smul_comm]`. Conclude with `Submodule.smul_mem _ c hy`. Consider the case `zero => simp`. Consider the case `add x z _ _ hx hz`. Rewrite using `[add_mul]`.

Conclude with `add_mem hx hz`. Consider the case `smul c x _ hx`. Rewrite using `[smul_mul_assoc]`. Conclude with `Submodule.smul_mem _ c hx`. Use `set d : Fin 4 → K := fun k => r g0 k k with hdd`.

Establish `hD : r g0 = Matrix.diagonal d`. Use extensionality with `a b`. Distinguish the cases in `hab : a = b`. Substitute `hab` using the available equality. Simplify using `[d]`.

Rewrite using `[Matrix.diagonal_apply_ne _ hab]`. Conclude with `hd hab`. Establish `key : ∀ s : Finset (Fin 4), i ∉ s → Matrix.diagonal (fun k => ∏ j ∈ s, (d k - d j) / (d i - d j)) ∈ W`. Introduce `s`. Use `Finset.induction_on s ?_ ?_` and prove the remaining obligations.

Introduce `_`. Simplify using `only [Finset.prod_empty, Matrix.diagonal_one]`. Conclude with `hone`. Introduce `j s hjs ih hi`. Establish `hs : i ∉ s` using `fun h => hi (Finset.mem_insert_of_mem h)`.

Establish `hfac : (d i - d j)⁻¹ • (r g0 - d j • (1 : M4 K)) = Matrix.diagonal (fun k => (d k - d j) / (d i - d j))`. Rewrite using `[hD]`. Use extensionality with `a b`. Distinguish the cases in `hab : a = b`. Substitute `hab` using the available equality.

Simplify using `[Matrix.one_apply, div_eq_inv_mul]`. Simplify using `[Matrix.diagonal_apply_ne _ hab, Matrix.one_apply_ne hab]`. Establish `hprod : Matrix.diagonal (fun k => ∏ j' ∈ insert j s, (d k - d j') / (d i - d j')) = Matrix.diagonal (fun k => (d k - d j) / (d i - d j)) * Matrix.diagonal (fun k => ∏ j' ∈ s, (d k - d j') / (d i - d j'))`. Rewrite using `[Matrix.diagonal_mul_diagonal]`. Use `congr 1`.

Use function extensionality and compare the values at `k`. Rewrite using `[Finset.prod_insert hjs]`. Rewrite using `[hprod, ← hfac]`. Conclude with `hmul _ (Submodule.smul_mem _ _ (Submodule.sub_mem _ (hmem g0) (Submodule.smul_mem _ _ hone))) _ (ih hs)`. Establish `h` using `key (Finset.univ.erase i) (by simp)`.

Use `h using 1` and compare the differences between its conclusion and the goal. Use extensionality with `a b`. Rewrite using `[Matrix.diagonal_apply, Matrix.single_apply]`. Distinguish the cases in `hab : a = b`. Substitute `hab` using the available equality.

Distinguish the cases in `hai : i = a`. Substitute `hai` using the available equality. Simplify using `only [and_self, if_true]`. Rewrite using `[Finset.prod_eq_one]`. Introduce `j hj`.

Conclude with `div_self (sub_ne_zero.2 (hne _ _ (Finset.ne_of_mem_erase hj).symm))`. Simplify using `only [hai, and_self, if_false, if_true]`. Conclude with `(Finset.prod_eq_zero (Finset.mem_erase.2 ⟨Ne.symm hai, Finset.mem_univ a⟩) (by simp)).symm`. Simplify using `only [hab, if_false] split_ifs with h'`. Conclude with `absurd (h'.1.symm.trans h'.2) hab`.

Both sides reduce to the same expression.
-/
private theorem UpperTheory.V.Ws.red_eii {Γ K : Type} [Group Γ] [Field K] (r : Γ →* M4 K) (g0 : Γ) (hd : (r g0).IsDiag)
    (hne : ∀ i j, i ≠ j → r g0 i i ≠ r g0 j j) (i : Fin 4) :
    Matrix.single i i (1 : K) ∈ Submodule.span K (Set.range r) := by
  classical
  set W := Submodule.span K (Set.range r) with hW
  have hmem : ∀ g, r g ∈ W := fun g => Submodule.subset_span ⟨g, rfl⟩
  have hone : (1 : M4 K) ∈ W := by
    rw [← map_one r]
    exact hmem 1
  have hmul : ∀ M ∈ W, ∀ N ∈ W, M * N ∈ W := by
    intro M hM N hN
    induction hM using Submodule.span_induction with
    | mem x hx =>
      induction hN using Submodule.span_induction with
      | mem y hy =>
        obtain ⟨a, rfl⟩ := hx
        obtain ⟨b, rfl⟩ := hy
        rw [← map_mul]
        exact hmem _
      | zero => simp
      | add y z _ _ hy hz =>
        rw [mul_add]
        exact add_mem hy hz
      | smul c y _ hy =>
        rw [mul_smul_comm]
        exact Submodule.smul_mem _ c hy
    | zero => simp
    | add x z _ _ hx hz =>
      rw [add_mul]
      exact add_mem hx hz
    | smul c x _ hx =>
      rw [smul_mul_assoc]
      exact Submodule.smul_mem _ c hx
  set d : Fin 4 → K := fun k => r g0 k k with hdd
  have hD : r g0 = Matrix.diagonal d := by
    ext a b
    by_cases hab : a = b
    · subst hab
      simp [d]
    · rw [Matrix.diagonal_apply_ne _ hab]
      exact hd hab
  have key : ∀ s : Finset (Fin 4), i ∉ s →
      Matrix.diagonal (fun k => ∏ j ∈ s, (d k - d j) / (d i - d j)) ∈ W := by
    intro s
    refine Finset.induction_on s ?_ ?_
    · intro _
      simp only [Finset.prod_empty, Matrix.diagonal_one]
      exact hone
    · intro j s hjs ih hi
      have hs : i ∉ s := fun h => hi (Finset.mem_insert_of_mem h)
      have hfac : (d i - d j)⁻¹ • (r g0 - d j • (1 : M4 K)) =
          Matrix.diagonal (fun k => (d k - d j) / (d i - d j)) := by
        rw [hD]
        ext a b
        by_cases hab : a = b
        · subst hab
          simp [Matrix.one_apply, div_eq_inv_mul]
        · simp [Matrix.diagonal_apply_ne _ hab, Matrix.one_apply_ne hab]
      have hprod : Matrix.diagonal (fun k => ∏ j' ∈ insert j s, (d k - d j') / (d i - d j')) =
          Matrix.diagonal (fun k => (d k - d j) / (d i - d j)) *
            Matrix.diagonal (fun k => ∏ j' ∈ s, (d k - d j') / (d i - d j')) := by
        rw [Matrix.diagonal_mul_diagonal]
        congr 1
        funext k
        rw [Finset.prod_insert hjs]
      rw [hprod, ← hfac]
      exact hmul _ (Submodule.smul_mem _ _ (Submodule.sub_mem _ (hmem g0) (Submodule.smul_mem _ _ hone))) _ (ih hs)
  have h := key (Finset.univ.erase i) (by simp)
  convert h using 1
  ext a b
  rw [Matrix.diagonal_apply, Matrix.single_apply]
  by_cases hab : a = b
  · subst hab
    by_cases hai : i = a
    · subst hai
      simp only [and_self, if_true]
      rw [Finset.prod_eq_one]
      intro j hj
      exact div_self (sub_ne_zero.2 (hne _ _ (Finset.ne_of_mem_erase hj).symm))
    · simp only [hai, and_self, if_false, if_true]
      exact (Finset.prod_eq_zero (Finset.mem_erase.2 ⟨Ne.symm hai, Finset.mem_univ a⟩) (by simp)).symm
  · simp only [hab, if_false]
    split_ifs with h'
    · exact absurd (h'.1.symm.trans h'.2) hab
    · rfl

/- English proof (translation)
Introduce `Γ K _ _ r ν g0 hν hd hne`. Take `⟨-, h0, h1, h2, h3, -⟩` from `geAlg K r ν hν (red_eii r g0 hd hne)`. Rewrite using `[h3]`. Prove the components needed by the constructor for the conclusion. Introduce `h`.

Take `⟨S, hS, h'⟩` from `(red_rel (Ge r) h0 h1 h2).resolve_left h`. Use `⟨S, hS, fun g i j hij hw => ?_⟩` and prove the remaining obligations. Assume the negation of the conclusion as `hn`. Conclude with `h' i j hij hw ⟨g, hn⟩`. Introduce and unpack `⟨S, hS, h⟩ hall`.

Take `⟨i, j, hij, hw⟩` from `redT_ex S hS`. Take `⟨g, hg⟩` from `hall i j`. Conclude with `hg (h g i j hij hw)`.
-/
theorem UpperTheory.V.Ws.redList :
    ∀ {Γ K : Type} [Group Γ] [Field K] (r : Γ →* M4 K) (ν : Γ → K) (g0 : Γ), (∀ g, IsGSp (ν g) (r g)) → (r g0).IsDiag →
      (∀ i j, i ≠ j → r g0 i i ≠ r g0 j j) → (¬ Irr r ↔ ∃ S ∈ redTypes, Supp S r) := by
  intro Γ K _ _ r ν g0 hν hd hne
  obtain ⟨-, h0, h1, h2, h3, -⟩ := geAlg K r ν hν (red_eii r g0 hd hne)
  rw [h3]
  constructor
  · intro h
    obtain ⟨S, hS, h'⟩ := (red_rel (Ge r) h0 h1 h2).resolve_left h
    refine ⟨S, hS, fun g i j hij hw => ?_⟩
    by_contra hn
    exact h' i j hij hw ⟨g, hn⟩
  · rintro ⟨S, hS, h⟩ hall
    obtain ⟨i, j, hij, hw⟩ := redT_ex S hS
    obtain ⟨g, hg⟩ := hall i j
    exact hg (h g i j hij hw)

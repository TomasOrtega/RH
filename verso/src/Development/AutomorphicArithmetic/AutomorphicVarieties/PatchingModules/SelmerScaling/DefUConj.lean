import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.SelmerScaling.EpC
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.SelmerScaling.OddDiag
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.SelmerScaling.BndOps

open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.AlgebraTools UpperTheory.V.Pa

namespace UpperTheory.V.Pa

section Comp

variable {X : Type} [CommRing X] {e n : ℕ}

/- English proof (translation)
Both sides reduce to the same expression.
-/
private theorem dd_a_add (x y : DD X e) : (x + y).a = x.a + y.a := rfl

/- English proof (translation)
Both sides reduce to the same expression.
-/
private theorem ep_component_add (x y : DD X e) : (x + y).ep = x.ep + y.ep := rfl

/- English proof (translation)
Both sides reduce to the same expression.
-/
private theorem dd_ep'_add (x y : DD X e) : (x + y).ep' = x.ep' + y.ep' := rfl

/- English proof (translation)
Both sides reduce to the same expression.
-/
private theorem dd_eta_add (x y : DD X e) : (x + y).eta = x.eta + y.eta := rfl

/- English proof (translation)
Both sides reduce to the same expression.
-/
private theorem dd_a_zero : (0 : DD X e).a = 0 := rfl

/- English proof (translation)
Both sides reduce to the same expression.
-/
private theorem dd_ep_zero : (0 : DD X e).ep = 0 := rfl

/- English proof (translation)
Both sides reduce to the same expression.
-/
private theorem dd_ep'_zero : (0 : DD X e).ep' = 0 := rfl

/- English proof (translation)
Both sides reduce to the same expression.
-/
private theorem dd_eta_zero : (0 : DD X e).eta = 0 := rfl

/- English proof (translation)
Both sides reduce to the same expression.
-/
private theorem dd_a_one : (1 : DD X e).a = 1 := rfl

/- English proof (translation)
Both sides reduce to the same expression.
-/
private theorem dd_ep_one : (1 : DD X e).ep = 0 := rfl

/- English proof (translation)
Both sides reduce to the same expression.
-/
private theorem dd_ep'_one : (1 : DD X e).ep' = 0 := rfl

/- English proof (translation)
Both sides reduce to the same expression.
-/
private theorem dd_eta_one : (1 : DD X e).eta = 0 := rfl

/- English proof (translation)
Use `Finset.induction_on s rfl ?_` and prove the remaining obligations. Introduce `i s hi ih`. Rewrite using `[Finset.sum_insert hi, Finset.sum_insert hi, ← ih]`. Both sides reduce to the same expression.
-/
private theorem sum_a {ι : Type} (s : Finset ι) (f : ι → DD X e) : (∑ i ∈ s, f i).a = ∑ i ∈ s, (f i).a := by
  classical
  refine Finset.induction_on s rfl ?_
  intro i s hi ih
  rw [Finset.sum_insert hi, Finset.sum_insert hi, ← ih]
  rfl

/- English proof (translation)
Use `Finset.induction_on s rfl ?_` and prove the remaining obligations. Introduce `i s hi ih`. Rewrite using `[Finset.sum_insert hi, Finset.sum_insert hi, ← ih]`. Both sides reduce to the same expression.
-/
private theorem sum_ep {ι : Type} (s : Finset ι) (f : ι → DD X e) (k : Fin e) :
    (∑ i ∈ s, f i).ep k = ∑ i ∈ s, (f i).ep k := by
  classical
  refine Finset.induction_on s rfl ?_
  intro i s hi ih
  rw [Finset.sum_insert hi, Finset.sum_insert hi, ← ih]
  rfl

/- English proof (translation)
Use `Finset.induction_on s rfl ?_` and prove the remaining obligations. Introduce `i s hi ih`. Rewrite using `[Finset.sum_insert hi, Finset.sum_insert hi, ← ih]`. Both sides reduce to the same expression.
-/
private theorem sum_ep' {ι : Type} (s : Finset ι) (f : ι → DD X e) (k : Fin e) :
    (∑ i ∈ s, f i).ep' k = ∑ i ∈ s, (f i).ep' k := by
  classical
  refine Finset.induction_on s rfl ?_
  intro i s hi ih
  rw [Finset.sum_insert hi, Finset.sum_insert hi, ← ih]
  rfl

/- English proof (translation)
Use `Finset.induction_on s rfl ?_` and prove the remaining obligations. Introduce `i s hi ih`. Rewrite using `[Finset.sum_insert hi, Finset.sum_insert hi, ← ih]`. Both sides reduce to the same expression.
-/
private theorem sum_eta {ι : Type} (s : Finset ι) (f : ι → DD X e) : (∑ i ∈ s, f i).eta = ∑ i ∈ s, (f i).eta := by
  classical
  refine Finset.induction_on s rfl ?_
  intro i s hi ih
  rw [Finset.sum_insert hi, Finset.sum_insert hi, ← ih]
  rfl

/- English proof (translation)
Use extensionality with `i j`. Simplify using `[Matrix.mul_apply, sum_a]`.
-/
private theorem mmul_a (M N : Matrix (Fin n) (Fin n) (DD X e)) :
    (M * N).map (fun a => a.a) = M.map (fun a => a.a) * N.map (fun a => a.a) := by
  ext i j
  simp [Matrix.mul_apply, sum_a]

/- English proof (translation)
Use extensionality with `i j`. Simplify using `[Matrix.mul_apply, sum_ep, Finset.sum_add_distrib]`.
-/
private theorem mmul_ep (M N : Matrix (Fin n) (Fin n) (DD X e)) (k : Fin e) :
    (M * N).map (fun a => a.ep k) =
      M.map (fun a => a.a) * N.map (fun a => a.ep k) + M.map (fun a => a.ep k) * N.map (fun a => a.a) := by
  ext i j
  simp [Matrix.mul_apply, sum_ep, Finset.sum_add_distrib]

/- English proof (translation)
Use extensionality with `i j`. Simplify using `[Matrix.mul_apply, sum_ep', Finset.sum_add_distrib]`.
-/
private theorem mmul_ep' (M N : Matrix (Fin n) (Fin n) (DD X e)) (k : Fin e) :
    (M * N).map (fun a => a.ep' k) =
      M.map (fun a => a.a) * N.map (fun a => a.ep' k) + M.map (fun a => a.ep' k) * N.map (fun a => a.a) := by
  ext i j
  simp [Matrix.mul_apply, sum_ep', Finset.sum_add_distrib]

/- English proof (translation)
Use extensionality with `i j`. Distinguish the cases in `hij : i = j`. Substitute `hij` using the available equality. Simplify using `[Matrix.one_apply, DD.epM, dd_a_add, dd_a_one]`. Simplify using `[Matrix.one_apply, DD.epM, hij, dd_a_add, dd_a_zero]`.
-/
private theorem P_a (Y : Fin e → Matrix (Fin n) (Fin n) X) : (1 + DD.epM Y).map (fun a => a.a) = 1 := by
  ext i j
  by_cases hij : i = j
  · subst hij
    simp [Matrix.one_apply, DD.epM, dd_a_add, dd_a_one]
  · simp [Matrix.one_apply, DD.epM, hij, dd_a_add, dd_a_zero]

/- English proof (translation)
Use extensionality with `i j`. Distinguish the cases in `hij : i = j`. Substitute `hij` using the available equality. Simplify using `[Matrix.one_apply, DD.epM, ep_component_add, dd_ep_one]`. Simplify using `[Matrix.one_apply, DD.epM, hij, ep_component_add, dd_ep_zero]`.
-/
private theorem P_ep (Y : Fin e → Matrix (Fin n) (Fin n) X) (k : Fin e) :
    (1 + DD.epM Y).map (fun a => a.ep k) = Y k := by
  ext i j
  by_cases hij : i = j
  · subst hij
    simp [Matrix.one_apply, DD.epM, ep_component_add, dd_ep_one]
  · simp [Matrix.one_apply, DD.epM, hij, ep_component_add, dd_ep_zero]

/- English proof (translation)
Use extensionality with `i j`. Distinguish the cases in `hij : i = j`. Substitute `hij` using the available equality. Simplify using `[Matrix.one_apply, DD.epM, dd_ep'_add, dd_ep'_one]`. Simplify using `[Matrix.one_apply, DD.epM, hij, dd_ep'_add, dd_ep'_zero]`.
-/
private theorem P_ep' (Y : Fin e → Matrix (Fin n) (Fin n) X) (k : Fin e) :
    (1 + DD.epM Y).map (fun a => a.ep' k) = 0 := by
  ext i j
  by_cases hij : i = j
  · subst hij
    simp [Matrix.one_apply, DD.epM, dd_ep'_add, dd_ep'_one]
  · simp [Matrix.one_apply, DD.epM, hij, dd_ep'_add, dd_ep'_zero]

/- English proof (translation)
Use `Matrix.ext fun i j => ?_` and prove the remaining obligations. Simplify using `only [Matrix.mul_apply, Matrix.zero_apply]`. Use `Finset.sum_eq_zero fun k _ => ?_` and prove the remaining obligations. Apply `DD.ext` to reduce the goal to its premises. Simplify using `[DD.mul_a, DD.epM, dd_a_zero]`.

Use function extensionality and compare the values at `m`. Simplify using `[DD.mul_ep, DD.epM, dd_ep_zero]`. Use function extensionality and compare the values at `m`. Simplify using `[DD.mul_ep', DD.epM, dd_ep'_zero]`. Simplify using `[DD.mul_eta, DD.epM, dd_eta_zero]`.
-/
private theorem epM_mul (Y Z : Fin e → Matrix (Fin n) (Fin n) X) : DD.epM Y * DD.epM Z = 0 := by
  refine Matrix.ext fun i j => ?_
  simp only [Matrix.mul_apply, Matrix.zero_apply]
  refine Finset.sum_eq_zero fun k _ => ?_
  apply DD.ext
  · simp [DD.mul_a, DD.epM, dd_a_zero]
  · funext m
    simp [DD.mul_ep, DD.epM, dd_ep_zero]
  · funext m
    simp [DD.mul_ep', DD.epM, dd_ep'_zero]
  · simp [DD.mul_eta, DD.epM, dd_eta_zero]

/- English proof (translation)
Apply the tactic sequence `ext i j <;> simp [DD.epM]`.
-/
private theorem epM_add (Y Z : Fin e → Matrix (Fin n) (Fin n) X) : DD.epM Y + DD.epM Z = DD.epM (Y + Z) := by
  ext i j <;> simp [DD.epM]

/- English proof (translation)
Apply the tactic sequence `ext i j <;> rfl`.
-/
private theorem epM_zero : DD.epM (0 : Fin e → Matrix (Fin n) (Fin n) X) = 0 := by
  ext i j <;> rfl

/- English proof (translation)
Rewrite using `[add_mul, one_mul, mul_add, mul_one, epM_mul, add_zero, add_assoc, add_comm (DD.epM Z), epM_add, h, epM_zero, add_zero]`.
-/
private theorem twoPow_mul_twoPow (Y Z : Fin e → Matrix (Fin n) (Fin n) X) (h : Y + Z = 0) :
    (1 + DD.epM Y) * (1 + DD.epM Z) = 1 := by
  rw [add_mul, one_mul, mul_add, mul_one, epM_mul, add_zero, add_assoc, add_comm (DD.epM Z),
    epM_add, h, epM_zero, add_zero]

/- English proof (translation)
Rewrite using `[transpose_add, transpose_one]`. Use `congr 1`. Apply the tactic sequence `ext i j <;> simp [DD.epM, ← h]`.
-/
private theorem P_tr (Y Z : Fin e → Matrix (Fin n) (Fin n) X) (h : ∀ k, (Y k)ᵀ = Z k) :
    (1 + DD.epM Y)ᵀ = 1 + DD.epM Z := by
  rw [transpose_add, transpose_one]
  congr 1
  ext i j <;> simp [DD.epM, ← h]

/- English proof (translation)
Proceed by induction on `s with`. Consider the case `nil => simp [h1]`. Consider the case `cons a s ih`. Rewrite using `[List.map_cons, List.prod_cons, ih, List.prod_cons]`. Simplify using `only [mul_assoc]`.

Rewrite using `[← mul_assoc Q P, h2, one_mul]`.
-/
private theorem conj_prod {R : Type} [Ring R] (P Q : R) (h1 : P * Q = 1) (h2 : Q * P = 1) (s : List R) :
    (s.map fun a => P * a * Q).prod = P * s.prod * Q := by
  induction s with
  | nil => simp [h1]
  | cons a s ih =>
    rw [List.map_cons, List.prod_cons, ih, List.prod_cons]
    simp only [mul_assoc]
    rw [← mul_assoc Q P, h2, one_mul]

variable {A : Type} [CommRing A] [Algebra A X]

/- English proof (translation)
Express the relevant statement in the definitionally equal form `(_ ∧ _ ∧ _ ∧ _) ↔ _`. Simplify using the standard rewrite rules.
-/
private theorem mem_ev (x : DD X e) : x ∈ ddPart A X e true false true false ↔ x.ep = 0 ∧ x.eta = 0 := by
  change (_ ∧ _ ∧ _ ∧ _) ↔ _
  simp

/- English proof (translation)
Express the relevant statement in the definitionally equal form `(_ ∧ _ ∧ _ ∧ _) ↔ _`. Simplify using the standard rewrite rules.
-/
private theorem mem_od (x : DD X e) : x ∈ ddPart A X e false true false true ↔ x.a = 0 ∧ x.ep' = 0 := by
  change (_ ∧ _ ∧ _ ∧ _) ↔ _
  simp

/- English proof (translation)
Take `⟨hx1, hx2⟩` from `hx`. Take `⟨hy1, hy2⟩` from `hy`. Prove the components needed by the constructor for the conclusion. Use function extensionality and compare the values at `j`. Simplify using `[DD.mul_ep, hx1, hy1]`.

Simplify using `[DD.mul_eta, hx1, hx2, hy1, hy2]`.
-/
private theorem ep_eta_mul_eq_zero_of_ep_eta_eq_zero (x y : DD X e) (hx : x.ep = 0 ∧ x.eta = 0) (hy : y.ep = 0 ∧ y.eta = 0) :
    (x * y).ep = 0 ∧ (x * y).eta = 0 := by
  obtain ⟨hx1, hx2⟩ := hx
  obtain ⟨hy1, hy2⟩ := hy
  constructor
  · funext j
    simp [DD.mul_ep, hx1, hy1]
  · simp [DD.mul_eta, hx1, hx2, hy1, hy2]

/- English proof (translation)
Take `⟨hx1, hx2⟩` from `hx`. Take `⟨hy1, hy2⟩` from `hy`. Prove the components needed by the constructor for the conclusion. Use function extensionality and compare the values at `j`. Simplify using `[DD.mul_ep, hx1, hy1]`.

Simplify using `[DD.mul_eta, hx1, hx2, hy1, hy2]`.
-/
private theorem ep_eta_mul_eq_zero_of_a_ep'_eq_zero (x y : DD X e) (hx : x.a = 0 ∧ x.ep' = 0) (hy : y.a = 0 ∧ y.ep' = 0) :
    (x * y).ep = 0 ∧ (x * y).eta = 0 := by
  obtain ⟨hx1, hx2⟩ := hx
  obtain ⟨hy1, hy2⟩ := hy
  constructor
  · funext j
    simp [DD.mul_ep, hx1, hy1]
  · simp [DD.mul_eta, hx1, hx2, hy1, hy2]

/- English proof (translation)
Take `⟨hx1, hx2⟩` from `hx`. Take `⟨hy1, hy2⟩` from `hy`. Prove the components needed by the constructor for the conclusion. Simplify using `[DD.mul_a, hy1]`. Use function extensionality and compare the values at `j`.

Simplify using `[DD.mul_ep', hx1, hy1, hy2]`.
-/
private theorem a_ep'_mul_eq_zero_of_ep_eta_zero_of_a_ep'_zero (x y : DD X e) (hx : x.ep = 0 ∧ x.eta = 0) (hy : y.a = 0 ∧ y.ep' = 0) :
    (x * y).a = 0 ∧ (x * y).ep' = 0 := by
  obtain ⟨hx1, hx2⟩ := hx
  obtain ⟨hy1, hy2⟩ := hy
  constructor
  · simp [DD.mul_a, hy1]
  · funext j
    simp [DD.mul_ep', hx1, hy1, hy2]

/- English proof (translation)
Take `⟨hx1, hx2⟩` from `hx`. Take `⟨hy1, hy2⟩` from `hy`. Prove the components needed by the constructor for the conclusion. Simplify using `[DD.mul_a, hx1]`. Use function extensionality and compare the values at `j`.

Simplify using `[DD.mul_ep', hx1, hx2]`.
-/
private theorem a_ep'_mul_eq_zero_of_a_ep'_zero_of_ep_eta_zero (x y : DD X e) (hx : x.a = 0 ∧ x.ep' = 0) (hy : y.ep = 0 ∧ y.eta = 0) :
    (x * y).a = 0 ∧ (x * y).ep' = 0 := by
  obtain ⟨hx1, hx2⟩ := hx
  obtain ⟨hy1, hy2⟩ := hy
  constructor
  · simp [DD.mul_a, hx1]
  · funext j
    simp [DD.mul_ep', hx1, hx2]

/- English proof (translation)
Establish `hM' : ∀ i j : Fin n, ((↑i < a ↔ ↑j < a) → M i j ∈ ddPart A X e true false true false) ∧ (¬(↑i < a ↔ ↑j < a) → M i j ∈ ddPart A X e false true false true)` using `hM`. Establish `hN' : ∀ i j : Fin n, ((↑i < a ↔ ↑j < a) → N i j ∈ ddPart A X e true false true false) ∧ (¬(↑i < a ↔ ↑j < a) → N i j ∈ ddPart A X e false true false true)` using `hN`. Introduce `i j`. Prove the components needed by the constructor for the conclusion. Introduce `hij`.

Rewrite using `[Matrix.mul_apply]`. Use `Submodule.sum_mem _ fun k _ => ?_` and prove the remaining obligations. Rewrite using `[mem_ev]`. Distinguish the cases in `hik : (↑i < a ↔ ↑k < a)`. Establish `h1` using `(hM' i k).1 hik`.

Establish `h2` using `(hN' k j).1 (hik.symm.trans hij)`. Rewrite `h1`, `h2` using `[mem_ev]`. Conclude with `ep_eta_mul_eq_zero_of_ep_eta_eq_zero _ _ h1 h2`. Establish `h1` using `(hM' i k).2 hik`. Establish `h2` using `(hN' k j).2 (fun hkj => hik (hij.trans hkj.symm))`.

Rewrite `h1`, `h2` using `[mem_od]`. Conclude with `ep_eta_mul_eq_zero_of_a_ep'_eq_zero _ _ h1 h2`. Introduce `hij`. Rewrite using `[Matrix.mul_apply]`. Use `Submodule.sum_mem _ fun k _ => ?_` and prove the remaining obligations.

Rewrite using `[mem_od]`. Distinguish the cases in `hik : (↑i < a ↔ ↑k < a)`. Establish `h1` using `(hM' i k).1 hik`. Establish `h2` using `(hN' k j).2 (fun hkj => hij (hik.trans hkj))`. Rewrite `h1` using `[mem_ev]`.

Rewrite `h2` using `[mem_od]`. Conclude with `a_ep'_mul_eq_zero_of_ep_eta_zero_of_a_ep'_zero _ _ h1 h2`. Establish `h1` using `(hM' i k).2 hik`. Establish `h2` using `(hN' k j).1 (by tauto)`. Rewrite `h1` using `[mem_od]`.

Rewrite `h2` using `[mem_ev]`. Conclude with `a_ep'_mul_eq_zero_of_a_ep'_zero_of_ep_eta_zero _ _ h1 h2`.
-/
private theorem even_mul (a : ℕ) (M N : Matrix (Fin n) (Fin n) (DD X e))
    (hM : M ∈ blkMat n a (ddPart A X e true false true false) (ddPart A X e false true false true))
    (hN : N ∈ blkMat n a (ddPart A X e true false true false) (ddPart A X e false true false true)) :
    M * N ∈ blkMat n a (ddPart A X e true false true false) (ddPart A X e false true false true) := by
  have hM' : ∀ i j : Fin n,
      ((↑i < a ↔ ↑j < a) → M i j ∈ ddPart A X e true false true false) ∧
        (¬(↑i < a ↔ ↑j < a) → M i j ∈ ddPart A X e false true false true) := hM
  have hN' : ∀ i j : Fin n,
      ((↑i < a ↔ ↑j < a) → N i j ∈ ddPart A X e true false true false) ∧
        (¬(↑i < a ↔ ↑j < a) → N i j ∈ ddPart A X e false true false true) := hN
  intro i j
  constructor
  · intro hij
    rw [Matrix.mul_apply]
    refine Submodule.sum_mem _ fun k _ => ?_
    rw [mem_ev]
    by_cases hik : (↑i < a ↔ ↑k < a)
    · have h1 := (hM' i k).1 hik
      have h2 := (hN' k j).1 (hik.symm.trans hij)
      rw [mem_ev] at h1 h2
      exact ep_eta_mul_eq_zero_of_ep_eta_eq_zero _ _ h1 h2
    · have h1 := (hM' i k).2 hik
      have h2 := (hN' k j).2 (fun hkj => hik (hij.trans hkj.symm))
      rw [mem_od] at h1 h2
      exact ep_eta_mul_eq_zero_of_a_ep'_eq_zero _ _ h1 h2
  · intro hij
    rw [Matrix.mul_apply]
    refine Submodule.sum_mem _ fun k _ => ?_
    rw [mem_od]
    by_cases hik : (↑i < a ↔ ↑k < a)
    · have h1 := (hM' i k).1 hik
      have h2 := (hN' k j).2 (fun hkj => hij (hik.trans hkj))
      rw [mem_ev] at h1
      rw [mem_od] at h2
      exact a_ep'_mul_eq_zero_of_ep_eta_zero_of_a_ep'_zero _ _ h1 h2
    · have h1 := (hM' i k).2 hik
      have h2 := (hN' k j).1 (by tauto)
      rw [mem_od] at h1
      rw [mem_ev] at h2
      exact a_ep'_mul_eq_zero_of_a_ep'_zero_of_ep_eta_zero _ _ h1 h2

/- English proof (translation)
Establish `hYk : ∀ k, ∀ i j : Fin n, ((↑i < a ↔ ↑j < a) → Y k i j ∈ (⊥ : Submodule A X)) ∧ (¬(↑i < a ↔ ↑j < a) → Y k i j ∈ (⊤ : Submodule A X))` using `hY`. Introduce `i j`. Prove the components needed by the constructor for the conclusion. Introduce `hij`. Rewrite using `[mem_ev]`.

Establish `h0 : ∀ k, Y k i j = 0` using `fun k => (Submodule.mem_bot A).1 ((hYk k i j).1 hij)`. Prove the components needed by the constructor for the conclusion. Use function extensionality and compare the values at `k`. Distinguish the cases in `hij' : i = j`. Substitute `hij'` using the available equality.

Simplify using `[Matrix.one_apply, DD.epM, h0, ep_component_add, dd_ep_one]`. Simplify using `[Matrix.one_apply, DD.epM, hij', h0, ep_component_add, dd_ep_zero]`. Distinguish the cases in `hij' : i = j`. Substitute `hij'` using the available equality. Simplify using `[Matrix.one_apply, DD.epM, dd_eta_add, dd_eta_one]`.

Simplify using `[Matrix.one_apply, DD.epM, hij', dd_eta_add, dd_eta_zero]`. Introduce `hij`. Rewrite using `[mem_od]`. Establish `hne : i ≠ j` using `fun h => hij (h ▸ Iff.rfl)`. Prove the components needed by the constructor for the conclusion.

Simplify using `[Matrix.one_apply, DD.epM, hne, dd_a_add, dd_a_zero]`. Use function extensionality and compare the values at `k`. Simplify using `[Matrix.one_apply, DD.epM, hne, dd_ep'_add, dd_ep'_zero]`.
-/
private theorem even_P (a : ℕ) (Y : Fin e → Matrix (Fin n) (Fin n) X) (hY : ∀ k, Y k ∈ Od A X n a) :
    1 + DD.epM Y ∈ blkMat n a (ddPart A X e true false true false) (ddPart A X e false true false true) := by
  have hYk : ∀ k, ∀ i j : Fin n,
      ((↑i < a ↔ ↑j < a) → Y k i j ∈ (⊥ : Submodule A X)) ∧
        (¬(↑i < a ↔ ↑j < a) → Y k i j ∈ (⊤ : Submodule A X)) := hY
  intro i j
  constructor
  · intro hij
    rw [mem_ev]
    have h0 : ∀ k, Y k i j = 0 := fun k => (Submodule.mem_bot A).1 ((hYk k i j).1 hij)
    constructor
    · funext k
      by_cases hij' : i = j
      · subst hij'
        simp [Matrix.one_apply, DD.epM, h0, ep_component_add, dd_ep_one]
      · simp [Matrix.one_apply, DD.epM, hij', h0, ep_component_add, dd_ep_zero]
    · by_cases hij' : i = j
      · subst hij'
        simp [Matrix.one_apply, DD.epM, dd_eta_add, dd_eta_one]
      · simp [Matrix.one_apply, DD.epM, hij', dd_eta_add, dd_eta_zero]
  · intro hij
    rw [mem_od]
    have hne : i ≠ j := fun h => hij (h ▸ Iff.rfl)
    constructor
    · simp [Matrix.one_apply, DD.epM, hne, dd_a_add, dd_a_zero]
    · funext k
      simp [Matrix.one_apply, DD.epM, hne, dd_ep'_add, dd_ep'_zero]

end Comp

section Bnd

variable {K G : Type} [Field K] [TopologicalSpace G] [Group G] [IsTopologicalGroup G] {n e : ℕ}

/- English proof (translation)
Introduce `i j`. Take `⟨hc, -⟩` from `bndOps K G`. Conclude with `⟨hc _, fun _ => hc _, fun _ => hc _, hc _⟩`.
-/
private theorem bnd_const (M : Matrix (Fin n) (Fin n) (DD (FractionRing (PowerSeries K)) e)) :
    BndD (PowerSeries.X : PowerSeries K) fun _ : G => M := by
  intro i j
  obtain ⟨hc, -⟩ := bndOps K G
  exact ⟨hc _, fun _ => hc _, fun _ => hc _, hc _⟩

/- English proof (translation)
Take `⟨-, hops, hsum, -, -⟩` from `bndOps K G`. Establish `hadd : ∀ φ ψ : G → FractionRing (PowerSeries K), BndF (PowerSeries.X : PowerSeries K) φ → BndF (PowerSeries.X : PowerSeries K) ψ → BndF (PowerSeries.X : PowerSeries K) fun g => φ g + ψ g` using `fun φ ψ hφ hψ => (hops φ ψ hφ hψ).1`. Establish `hmul : ∀ φ ψ : G → FractionRing (PowerSeries K), BndF (PowerSeries.X : PowerSeries K) φ → BndF (PowerSeries.X : PowerSeries K) ψ → BndF (PowerSeries.X : PowerSeries K) fun g => φ g * ψ g` using `fun φ ψ hφ hψ => (hops φ ψ hφ hψ).2.1`. Introduce `i j`. Use `⟨?_, fun m => ?_, fun m => ?_, ?_⟩` and prove the remaining obligations.

Establish `hf : (fun g => (((fun g => M g * N g) g) i j).a) = fun g => ∑ k ∈ Finset.univ, (M g i k).a * (N g k j).a`. Use function extensionality and compare the values at `g`. Simplify using `only [Matrix.mul_apply, sum_a, DD.mul_a]`. Rewrite using `[hf]`. Conclude with `hsum (Fin n) Finset.univ (fun k g => (M g i k).a * (N g k j).a) (fun k _ => hmul _ _ (hM i k).1 (hN k j).1)`.

Establish `hf : (fun g => (((fun g => M g * N g) g) i j).ep m) = fun g => ∑ k ∈ Finset.univ, ((M g i k).a * (N g k j).ep m + (M g i k).ep m * (N g k j).a)`. Use function extensionality and compare the values at `g`. Simplify using `only [Matrix.mul_apply, sum_ep, DD.mul_ep]`. Rewrite using `[hf]`. Conclude with `hsum (Fin n) Finset.univ (fun k g => (M g i k).a * (N g k j).ep m + (M g i k).ep m * (N g k j).a) (fun k _ => hadd _ _ (hmul _ _ (hM i k).1 ((hN k j).2.1 m)) (hmul _ _ ((hM i k).2.1 m) (hN k j).1))`.

Establish `hf : (fun g => (((fun g => M g * N g) g) i j).ep' m) = fun g => ∑ k ∈ Finset.univ, ((M g i k).a * (N g k j).ep' m + (M g i k).ep' m * (N g k j).a)`. Use function extensionality and compare the values at `g`. Simplify using `only [Matrix.mul_apply, sum_ep', DD.mul_ep']`. Rewrite using `[hf]`. Conclude with `hsum (Fin n) Finset.univ (fun k g => (M g i k).a * (N g k j).ep' m + (M g i k).ep' m * (N g k j).a) (fun k _ => hadd _ _ (hmul _ _ (hM i k).1 ((hN k j).2.2.1 m)) (hmul _ _ ((hM i k).2.2.1 m) (hN k j).1))`.

Establish `hf : (fun g => (((fun g => M g * N g) g) i j).eta) = fun g => ∑ k ∈ Finset.univ, ((M g i k).a * (N g k j).eta + (M g i k).eta * (N g k j).a + ∑ m ∈ Finset.univ, ((M g i k).ep m * (N g k j).ep' m + (M g i k).ep' m * (N g k j).ep m))`. Use function extensionality and compare the values at `g`. Simplify using `only [Matrix.mul_apply, sum_eta, DD.mul_eta]`. Rewrite using `[hf]`. Use `hsum (Fin n) Finset.univ _ (fun k _ => ?_)` and prove the remaining obligations.

Use `hadd _ _ (hadd _ _ (hmul _ _ (hM i k).1 (hN k j).2.2.2) (hmul _ _ (hM i k).2.2.2 (hN k j).1)) ?_` and prove the remaining obligations. Conclude with `hsum (Fin e) Finset.univ _ (fun m _ => hadd _ _ (hmul _ _ ((hM i k).2.1 m) ((hN k j).2.2.1 m)) (hmul _ _ ((hM i k).2.2.1 m) ((hN k j).2.1 m)))`.
-/
private theorem bnd_mul (M N : G → Matrix (Fin n) (Fin n) (DD (FractionRing (PowerSeries K)) e))
    (hM : BndD (PowerSeries.X : PowerSeries K) M) (hN : BndD (PowerSeries.X : PowerSeries K) N) :
    BndD (PowerSeries.X : PowerSeries K) fun g => M g * N g := by
  obtain ⟨-, hops, hsum, -, -⟩ := bndOps K G
  have hadd : ∀ φ ψ : G → FractionRing (PowerSeries K), BndF (PowerSeries.X : PowerSeries K) φ →
      BndF (PowerSeries.X : PowerSeries K) ψ → BndF (PowerSeries.X : PowerSeries K) fun g => φ g + ψ g :=
    fun φ ψ hφ hψ => (hops φ ψ hφ hψ).1
  have hmul : ∀ φ ψ : G → FractionRing (PowerSeries K), BndF (PowerSeries.X : PowerSeries K) φ →
      BndF (PowerSeries.X : PowerSeries K) ψ → BndF (PowerSeries.X : PowerSeries K) fun g => φ g * ψ g :=
    fun φ ψ hφ hψ => (hops φ ψ hφ hψ).2.1
  intro i j
  refine ⟨?_, fun m => ?_, fun m => ?_, ?_⟩
  · have hf : (fun g => (((fun g => M g * N g) g) i j).a) =
        fun g => ∑ k ∈ Finset.univ, (M g i k).a * (N g k j).a := by
      funext g
      simp only [Matrix.mul_apply, sum_a, DD.mul_a]
    rw [hf]
    exact hsum (Fin n) Finset.univ (fun k g => (M g i k).a * (N g k j).a)
      (fun k _ => hmul _ _ (hM i k).1 (hN k j).1)
  · have hf : (fun g => (((fun g => M g * N g) g) i j).ep m) =
        fun g => ∑ k ∈ Finset.univ, ((M g i k).a * (N g k j).ep m + (M g i k).ep m * (N g k j).a) := by
      funext g
      simp only [Matrix.mul_apply, sum_ep, DD.mul_ep]
    rw [hf]
    exact hsum (Fin n) Finset.univ (fun k g => (M g i k).a * (N g k j).ep m + (M g i k).ep m * (N g k j).a)
      (fun k _ => hadd _ _ (hmul _ _ (hM i k).1 ((hN k j).2.1 m)) (hmul _ _ ((hM i k).2.1 m) (hN k j).1))
  · have hf : (fun g => (((fun g => M g * N g) g) i j).ep' m) =
        fun g => ∑ k ∈ Finset.univ, ((M g i k).a * (N g k j).ep' m + (M g i k).ep' m * (N g k j).a) := by
      funext g
      simp only [Matrix.mul_apply, sum_ep', DD.mul_ep']
    rw [hf]
    exact hsum (Fin n) Finset.univ (fun k g => (M g i k).a * (N g k j).ep' m + (M g i k).ep' m * (N g k j).a)
      (fun k _ => hadd _ _ (hmul _ _ (hM i k).1 ((hN k j).2.2.1 m)) (hmul _ _ ((hM i k).2.2.1 m) (hN k j).1))
  · have hf : (fun g => (((fun g => M g * N g) g) i j).eta) =
        fun g => ∑ k ∈ Finset.univ, ((M g i k).a * (N g k j).eta + (M g i k).eta * (N g k j).a +
          ∑ m ∈ Finset.univ, ((M g i k).ep m * (N g k j).ep' m + (M g i k).ep' m * (N g k j).ep m)) := by
      funext g
      simp only [Matrix.mul_apply, sum_eta, DD.mul_eta]
    rw [hf]
    refine hsum (Fin n) Finset.univ _ (fun k _ => ?_)
    refine hadd _ _ (hadd _ _ (hmul _ _ (hM i k).1 (hN k j).2.2.2) (hmul _ _ (hM i k).2.2.2 (hN k j).1)) ?_
    exact hsum (Fin e) Finset.univ _
      (fun m _ => hadd _ _ (hmul _ _ ((hM i k).2.1 m) ((hN k j).2.2.1 m))
        (hmul _ _ ((hM i k).2.2.1 m) ((hN k j).2.1 m)))

end Bnd

end UpperTheory.V.Pa

/- English proof (translation)
Introduce `l _ L G G0 h n x e u ψ z hu hB`. Establish `hB' : ∀ k, ∃ Y ∈ Od x.A x.Fr n x.a, Yᵀ = -Y ∧ epC h x u k - z k = dY G.frame (fun g => x.ρX x.Fr (h.p₀ g)) Y` using `hB`. Use `choose Y hYod hYt hYz using hB'`. Take `⟨P, hP⟩ : ∃ P : Matrix (Fin n) (Fin n) (DD x.Fr e), P = 1 + DD.epM Y` from `⟨_, rfl⟩`. Take `⟨Q, hQ⟩ : ∃ Q : Matrix (Fin n) (Fin n) (DD x.Fr e), Q = 1 + DD.epM (-Y)` from `⟨_, rfl⟩`.

Establish `hPQ : P * Q = 1`. Rewrite using `[hP, hQ]`. Conclude with `twoPow_mul_twoPow Y (-Y) (add_neg_cancel Y)`. Establish `hQP : Q * P = 1`. Rewrite using `[hP, hQ]`.

Conclude with `twoPow_mul_twoPow (-Y) Y (neg_add_cancel Y)`. Establish `hPa : P.map (fun a => a.a) = 1`. Rewrite using `[hP]`. Conclude with `P_a Y`. Establish `hQa : Q.map (fun a => a.a) = 1`.

Rewrite using `[hQ]`. Conclude with `P_a (-Y)`. Establish `hPep : ∀ k, P.map (fun a => a.ep k) = Y k`. Introduce `k`. Rewrite using `[hP]`.

Conclude with `P_ep Y k`. Establish `hQep : ∀ k, Q.map (fun a => a.ep k) = -Y k`. Introduce `k`. Rewrite using `[hQ]`. Conclude with `P_ep (-Y) k`.

Establish `hPep' : ∀ k, P.map (fun a => a.ep' k) = 0`. Introduce `k`. Rewrite using `[hP]`. Conclude with `P_ep' Y k`. Establish `hQep' : ∀ k, Q.map (fun a => a.ep' k) = 0`.

Introduce `k`. Rewrite using `[hQ]`. Conclude with `P_ep' (-Y) k`. Establish `hPt : Pᵀ = Q`. Rewrite using `[hP, hQ]`.

Conclude with `P_tr Y (-Y) (fun k => by rw [hYt k]; rfl)`. Establish `hQt : Qᵀ = P`. Rewrite using `[hP, hQ]`. Conclude with `P_tr (-Y) Y (fun k => by show (-Y k)ᵀ = Y k`. Rewrite using `[Matrix.transpose_neg, hYt k, neg_neg])`.

Establish `hPev` using `even_P x.a Y hYod`. Establish `hQev` using `even_P x.a (-Y) (fun k => Submodule.neg_mem _ (hYod k))`. Rewrite `hPev` using `[← hP]`. Rewrite `hQev` using `[← hQ]`. Establish `hinv : ∀ γ : G.G₀, x.ρX x.Fr (h.p₀ γ) * x.ρX x.Fr (h.p₀ γ⁻¹) = 1`.

Introduce `γ`. Simplify using `only [NP.ρX, ← Matrix.map_mul, map_inv]`. Rewrite using `[← map_mul, mul_inv_cancel, map_one]`. Conclude with `Matrix.map_one _ (map_zero _) (map_one _)`. Establish `hc : ∀ c : DD x.Fr e, P * algebraMap (DD x.Fr e) (Matrix (Fin n) (Fin n) (DD x.Fr e)) c * Q = algebraMap (DD x.Fr e) (Matrix (Fin n) (Fin n) (DD x.Fr e)) c`.

Introduce `c`. Rewrite using `[Algebra.algebraMap_eq_smul_one, Matrix.mul_smul, mul_one, Matrix.smul_mul, hPQ]`. Use `⟨fun g => P * u g * Q, { one := ?_, mul := ?_, red := ?_, even := ?_, form := ?_, ine := ?_, ψ_red := hu.ψ_red, ψ_even := hu.ψ_even, ψ_mu := hu.ψ_mu, ord := ?_, bnd := ?_ }, ?_, ?_⟩` and prove the remaining obligations. Use `show P * u 1 * Q = 1`. Rewrite using `[hu.one, mul_one, hPQ]`.

Introduce `g g' show P * u (g * g') * Q = P * u g * Q * (P * u g' * Q)`. Rewrite using `[hu.mul]`. Simplify using `only [mul_assoc]`. Rewrite using `[← mul_assoc Q P, hQP, one_mul]`. Introduce `g show (P * u g * Q).map (fun a => a.a) = _`.

Rewrite using `[mmul_a, mmul_a, hPa, hQa, one_mul, mul_one, hu.red]`. Introduce `g`. Conclude with `even_mul x.a _ _ (even_mul x.a _ _ hPev (hu.even g)) hQev`. Introduce `g show (P * u g * Q)ᵀ * (P * u (G.frame.conj g) * Q) = _`. Rewrite using `[Matrix.transpose_mul, Matrix.transpose_mul, hPt, hQt]`.

Simplify using `only [mul_assoc]`. Rewrite using `[← mul_assoc Q P, hQP, one_mul, ← mul_assoc (u g)ᵀ, hu.form g, Matrix.smul_mul, one_mul, Matrix.mul_smul, hPQ]`. Introduce `w g hg show P * u g * Q = 1`. Rewrite using `[hu.ine w g hg, mul_one, hPQ]`. Introduce `v g show (List.ofFn fun i => P * u ((G.φ v) (g i)) * Q - algebraMap (DD x.Fr e) (Matrix (Fin n) (Fin n) (DD x.Fr e)) ↑((ψ v i) (g i))).prod = 0`.

Establish `key : ∀ i, P * u ((G.φ v) (g i)) * Q - algebraMap (DD x.Fr e) (Matrix (Fin n) (Fin n) (DD x.Fr e)) ↑((ψ v i) (g i)) = P * (u ((G.φ v) (g i)) - algebraMap (DD x.Fr e) (Matrix (Fin n) (Fin n) (DD x.Fr e)) ↑((ψ v i) (g i))) * Q`. Introduce `i`. Rewrite using `[mul_sub, sub_mul, hc]`. Establish `hl : ∀ W : Fin n → Matrix (Fin n) (Fin n) (DD x.Fr e), List.ofFn (fun i => P * W i * Q) = (List.ofFn W).map (fun a => P * a * Q)`. Introduce `W`.

Rewrite using `[List.map_ofFn]`. Both sides reduce to the same expression. Simplify using `only [key]`. Rewrite using `[hl, conj_prod P Q hPQ hQP, hu.ord v g, mul_zero, zero_mul]`. Use `show BndD x.t fun g => P * u g * Q`.

Conclude with `bnd_mul (K := x.K) (G := G.G₀) (fun g => P * u g) (fun _ => Q) (bnd_mul (K := x.K) (G := G.G₀) (fun _ => P) u (bnd_const P) hu.bnd) (bnd_const Q)`. Introduce `k`. Use function extensionality and compare the values at `γ`. Establish `hz : epC h x u k γ - z k γ = x.ρX x.Fr (h.p₀ γ) * Y k * x.ρX x.Fr (h.p₀ γ⁻¹) - Y k` using `congrFun (hYz k) γ`. Establish `hz' : z k γ = epC h x u k γ - (x.ρX x.Fr (h.p₀ γ) * Y k * x.ρX x.Fr (h.p₀ γ⁻¹) - Y k)`.

Rewrite using `[← hz, sub_sub_cancel]`. Rewrite using `[hz']`. Use `show ((P * u γ * Q).map fun a => a.ep k) * x.ρX x.Fr (h.p₀ γ⁻¹) = ((u γ).map fun a => a.ep k) * x.ρX x.Fr (h.p₀ γ⁻¹) - (x.ρX x.Fr (h.p₀ γ) * Y k * x.ρX x.Fr (h.p₀ γ⁻¹) - Y k)`. Simplify using `only [mmul_ep, mmul_a, hPa, hQa, hPep, hQep, one_mul, mul_one, hu.red]`. Simplify using `only [add_mul, mul_neg, neg_mul, Matrix.mul_assoc, hinv, Matrix.mul_one]`.

Normalize the expressions using the abelian group laws. Introduce `k`. Use function extensionality and compare the values at `γ`. Use `show ((P * u γ * Q).map fun a => a.ep' k) * x.ρX x.Fr (h.p₀ γ⁻¹) = ((u γ).map fun a => a.ep' k) * x.ρX x.Fr (h.p₀ γ⁻¹)`. Simplify using `only [mmul_ep', mmul_a, hPa, hQa, hPep', hQep', one_mul, mul_one, mul_zero, zero_mul, zero_add, add_zero]`.
-/
theorem UpperTheory.V.Pa.defUConj :
    ∀ (l : ℕ) [Fact l.Prime] (L : Loc) (G G0 : Glob l L) (h : G.Hom G0) (n : ℕ) (x : NP G0.frame n), ∀ (e : ℕ) (u : G.G₀ → Matrix (Fin n) (Fin n) (DD x.Fr e)) (ψ : ∀ v, Fin n → L.Gv v →* (DD x.Fr e)ˣ) (z : Fin e → G.G₀ → Matrix (Fin n) (Fin n) x.Fr), DefU h x u ψ → (∀ k, epC h x u k - z k ∈ BdM h x x.Fr) → ∃ u', DefU h x u' ψ ∧ (∀ k, epC h x u' k = z k) ∧ ∀ k, epC' h x u' k = epC' h x u k := by
  intro l _ L G G0 h n x e u ψ z hu hB
  have hB' : ∀ k, ∃ Y ∈ Od x.A x.Fr n x.a, Yᵀ = -Y ∧
      epC h x u k - z k = dY G.frame (fun g => x.ρX x.Fr (h.p₀ g)) Y := hB
  choose Y hYod hYt hYz using hB'
  obtain ⟨P, hP⟩ : ∃ P : Matrix (Fin n) (Fin n) (DD x.Fr e), P = 1 + DD.epM Y := ⟨_, rfl⟩
  obtain ⟨Q, hQ⟩ : ∃ Q : Matrix (Fin n) (Fin n) (DD x.Fr e), Q = 1 + DD.epM (-Y) := ⟨_, rfl⟩
  have hPQ : P * Q = 1 := by
    rw [hP, hQ]
    exact twoPow_mul_twoPow Y (-Y) (add_neg_cancel Y)
  have hQP : Q * P = 1 := by
    rw [hP, hQ]
    exact twoPow_mul_twoPow (-Y) Y (neg_add_cancel Y)
  have hPa : P.map (fun a => a.a) = 1 := by
    rw [hP]
    exact P_a Y
  have hQa : Q.map (fun a => a.a) = 1 := by
    rw [hQ]
    exact P_a (-Y)
  have hPep : ∀ k, P.map (fun a => a.ep k) = Y k := by
    intro k
    rw [hP]
    exact P_ep Y k
  have hQep : ∀ k, Q.map (fun a => a.ep k) = -Y k := by
    intro k
    rw [hQ]
    exact P_ep (-Y) k
  have hPep' : ∀ k, P.map (fun a => a.ep' k) = 0 := by
    intro k
    rw [hP]
    exact P_ep' Y k
  have hQep' : ∀ k, Q.map (fun a => a.ep' k) = 0 := by
    intro k
    rw [hQ]
    exact P_ep' (-Y) k
  have hPt : Pᵀ = Q := by
    rw [hP, hQ]
    exact P_tr Y (-Y) (fun k => by rw [hYt k]; rfl)
  have hQt : Qᵀ = P := by
    rw [hP, hQ]
    exact P_tr (-Y) Y (fun k => by
      show (-Y k)ᵀ = Y k
      rw [Matrix.transpose_neg, hYt k, neg_neg])
  have hPev := even_P x.a Y hYod
  have hQev := even_P x.a (-Y) (fun k => Submodule.neg_mem _ (hYod k))
  rw [← hP] at hPev
  rw [← hQ] at hQev
  have hinv : ∀ γ : G.G₀, x.ρX x.Fr (h.p₀ γ) * x.ρX x.Fr (h.p₀ γ⁻¹) = 1 := by
    intro γ
    simp only [NP.ρX, ← Matrix.map_mul, map_inv]
    rw [← map_mul, mul_inv_cancel, map_one]
    exact Matrix.map_one _ (map_zero _) (map_one _)
  have hc : ∀ c : DD x.Fr e,
      P * algebraMap (DD x.Fr e) (Matrix (Fin n) (Fin n) (DD x.Fr e)) c * Q =
        algebraMap (DD x.Fr e) (Matrix (Fin n) (Fin n) (DD x.Fr e)) c := by
    intro c
    rw [Algebra.algebraMap_eq_smul_one, Matrix.mul_smul, mul_one, Matrix.smul_mul, hPQ]
  refine ⟨fun g => P * u g * Q,
    { one := ?_, mul := ?_, red := ?_, even := ?_, form := ?_, ine := ?_,
      ψ_red := hu.ψ_red, ψ_even := hu.ψ_even, ψ_mu := hu.ψ_mu, ord := ?_, bnd := ?_ }, ?_, ?_⟩
  · show P * u 1 * Q = 1
    rw [hu.one, mul_one, hPQ]
  · intro g g'
    show P * u (g * g') * Q = P * u g * Q * (P * u g' * Q)
    rw [hu.mul]
    simp only [mul_assoc]
    rw [← mul_assoc Q P, hQP, one_mul]
  · intro g
    show (P * u g * Q).map (fun a => a.a) = _
    rw [mmul_a, mmul_a, hPa, hQa, one_mul, mul_one, hu.red]
  · intro g
    exact even_mul x.a _ _ (even_mul x.a _ _ hPev (hu.even g)) hQev
  · intro g
    show (P * u g * Q)ᵀ * (P * u (G.frame.conj g) * Q) = _
    rw [Matrix.transpose_mul, Matrix.transpose_mul, hPt, hQt]
    simp only [mul_assoc]
    rw [← mul_assoc Q P, hQP, one_mul, ← mul_assoc (u g)ᵀ, hu.form g, Matrix.smul_mul, one_mul,
      Matrix.mul_smul, hPQ]
  · intro w g hg
    show P * u g * Q = 1
    rw [hu.ine w g hg, mul_one, hPQ]
  · intro v g
    show (List.ofFn fun i => P * u ((G.φ v) (g i)) * Q -
      algebraMap (DD x.Fr e) (Matrix (Fin n) (Fin n) (DD x.Fr e)) ↑((ψ v i) (g i))).prod = 0
    have key : ∀ i, P * u ((G.φ v) (g i)) * Q -
        algebraMap (DD x.Fr e) (Matrix (Fin n) (Fin n) (DD x.Fr e)) ↑((ψ v i) (g i)) =
        P * (u ((G.φ v) (g i)) -
          algebraMap (DD x.Fr e) (Matrix (Fin n) (Fin n) (DD x.Fr e)) ↑((ψ v i) (g i))) * Q := by
      intro i
      rw [mul_sub, sub_mul, hc]
    have hl : ∀ W : Fin n → Matrix (Fin n) (Fin n) (DD x.Fr e),
        List.ofFn (fun i => P * W i * Q) = (List.ofFn W).map (fun a => P * a * Q) := by
      intro W
      rw [List.map_ofFn]
      rfl
    simp only [key]
    rw [hl, conj_prod P Q hPQ hQP, hu.ord v g, mul_zero, zero_mul]
  · show BndD x.t fun g => P * u g * Q
    exact bnd_mul (K := x.K) (G := G.G₀) (fun g => P * u g) (fun _ => Q)
      (bnd_mul (K := x.K) (G := G.G₀) (fun _ => P) u (bnd_const P) hu.bnd) (bnd_const Q)
  · intro k
    funext γ
    have hz : epC h x u k γ - z k γ =
        x.ρX x.Fr (h.p₀ γ) * Y k * x.ρX x.Fr (h.p₀ γ⁻¹) - Y k := congrFun (hYz k) γ
    have hz' : z k γ = epC h x u k γ -
        (x.ρX x.Fr (h.p₀ γ) * Y k * x.ρX x.Fr (h.p₀ γ⁻¹) - Y k) := by
      rw [← hz, sub_sub_cancel]
    rw [hz']
    show ((P * u γ * Q).map fun a => a.ep k) * x.ρX x.Fr (h.p₀ γ⁻¹) =
      ((u γ).map fun a => a.ep k) * x.ρX x.Fr (h.p₀ γ⁻¹) -
        (x.ρX x.Fr (h.p₀ γ) * Y k * x.ρX x.Fr (h.p₀ γ⁻¹) - Y k)
    simp only [mmul_ep, mmul_a, hPa, hQa, hPep, hQep, one_mul, mul_one, hu.red]
    simp only [add_mul, mul_neg, neg_mul, Matrix.mul_assoc, hinv, Matrix.mul_one]
    abel
  · intro k
    funext γ
    show ((P * u γ * Q).map fun a => a.ep' k) * x.ρX x.Fr (h.p₀ γ⁻¹) =
      ((u γ).map fun a => a.ep' k) * x.ρX x.Fr (h.p₀ γ⁻¹)
    simp only [mmul_ep', mmul_a, hPa, hQa, hPep', hQep', one_mul, mul_one, mul_zero, zero_mul,
      zero_add, add_zero]

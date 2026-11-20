import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ClassCounting.HasVal

noncomputable section

namespace UpperTheory.V.ZK

variable (A : Type) [CommRing A] {G : Type}

def hbd (G : Type) (n : ℕ) : Ch A G (n + 1) →ₗ[A] Ch A G n :=
  Finsupp.linearCombination A fun x =>
    ∑ j : Fin (n + 1), ((-1 : A) ^ (j : ℕ)) • Finsupp.single (fun i => x (j.succAbove i)) 1

def cone (a : G) (n : ℕ) : Ch A G n →ₗ[A] Ch A G (n + 1) :=
  Finsupp.lmapDomain A A fun x => (Fin.cons a x : Fin (n + 1) → G)

def hmap {H : Type} (f : G → H) (n : ℕ) : Ch A G n →ₗ[A] Ch A H n :=
  Finsupp.lmapDomain A A fun x i => f (x i)

/- English proof (translation)
Simplify using `only [hbd, Finsupp.linearCombination_single]`.
-/
theorem hbd_single (n : ℕ) (x : Fin (n + 1) → G) (c : A) : hbd A G n (Finsupp.single x c) =
    c • ∑ j : Fin (n + 1), ((-1 : A) ^ (j : ℕ)) • Finsupp.single (fun i => x (j.succAbove i)) 1 := by
  simp only [hbd, Finsupp.linearCombination_single]

/- English proof (translation)
Simplify using `[cone]`.
-/
@[simp] theorem cone_single (a : G) (n : ℕ) (x : Fin n → G) (c : A) :
    cone A a n (Finsupp.single x c) = Finsupp.single (Fin.cons a x : Fin (n + 1) → G) c := by
  simp [cone]

/- English proof (translation)
Simplify using `[hmap]`.
-/
@[simp] theorem hmap_single {H : Type} (f : G → H) (n : ℕ) (x : Fin n → G) (c : A) :
    hmap A f n (Finsupp.single x c) = Finsupp.single (fun i => f (x i)) c := by
  simp [hmap]

/- English proof (translation)
Establish `: f = g` using `Finsupp.lhom_ext' fun x => LinearMap.ext_ring (h x)`. Rewrite using `[this]`.
-/
theorem ch_ext {n : ℕ} {M : Type} [AddCommGroup M] [Module A M] {f g : Ch A G n →ₗ[A] M}
    (h : ∀ x, f (Finsupp.single x 1) = g (Finsupp.single x 1)) (z : Ch A G n) : f z = g z := by
  have : f = g := Finsupp.lhom_ext' fun x => LinearMap.ext_ring (h x)
  rw [this]

/- English proof (translation)
Use `ch_ext A (f := (hbd A G (n + 1)).comp (cone A a (n + 1))) (g := LinearMap.id - (cone A a n).comp (hbd A G n)) (fun x => ?_) y` and prove the remaining obligations. Simplify using `only [LinearMap.comp_apply, LinearMap.sub_apply, LinearMap.id_apply, cone_single, hbd_single, one_smul, map_sum, map_smul]`. Rewrite using `[Fin.sum_univ_succ, sub_eq_add_neg, ← Finset.sum_neg_distrib]`. Use `congr 1`. Simplify using the standard rewrite rules.

Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Rewrite using `[Fin.val_succ, pow_succ, mul_neg_one, neg_smul]`. Use `congr 3`. Use function extensionality and compare the values at `i`. Apply the tactic sequence `refine Fin.cases ?_ (fun i => ?_) i <;> simp`.
-/
theorem hbd_cone (a : G) (n : ℕ) (y : Ch A G (n + 1)) :
    hbd A G (n + 1) (cone A a (n + 1) y) = y - cone A a n (hbd A G n y) := by
  refine ch_ext A (f := (hbd A G (n + 1)).comp (cone A a (n + 1)))
    (g := LinearMap.id - (cone A a n).comp (hbd A G n)) (fun x => ?_) y
  simp only [LinearMap.comp_apply, LinearMap.sub_apply, LinearMap.id_apply, cone_single, hbd_single, one_smul, map_sum,
    map_smul]
  rw [Fin.sum_univ_succ, sub_eq_add_neg, ← Finset.sum_neg_distrib]
  congr 1
  · simp
  · refine Finset.sum_congr rfl fun j _ => ?_
    rw [Fin.val_succ, pow_succ, mul_neg_one, neg_smul]
    congr 3
    funext i
    refine Fin.cases ?_ (fun i => ?_) i <;> simp

/- English proof (translation)
Use `ch_ext A (f := (hbd A G 0).comp (cone A a 0)) (g := LinearMap.id) (fun x => ?_) y` and prove the remaining obligations. Simplify using `only [LinearMap.comp_apply, LinearMap.id_apply, cone_single, hbd_single, one_smul]`. Rewrite using `[Fin.sum_univ_succ]`. Simplify using `only [Finset.univ_eq_empty, Finset.sum_empty, add_zero, Fin.val_zero, pow_zero, one_smul]`. Use `congr 1`.
-/
theorem hbd_cone_zero (a : G) (y : Ch A G 0) : hbd A G 0 (cone A a 0 y) = y := by
  refine ch_ext A (f := (hbd A G 0).comp (cone A a 0)) (g := LinearMap.id) (fun x => ?_) y
  simp only [LinearMap.comp_apply, LinearMap.id_apply, cone_single, hbd_single, one_smul]
  rw [Fin.sum_univ_succ]
  simp only [Finset.univ_eq_empty, Finset.sum_empty, add_zero, Fin.val_zero, pow_zero, one_smul]
  congr 1

/- English proof (translation)
Use `ch_ext A (f := (hbd A H n).comp (hmap A f (n + 1))) (g := (hmap A f n).comp (hbd A G n)) (fun x => ?_) y` and prove the remaining obligations. Simplify using `only [LinearMap.comp_apply, hmap_single, hbd_single, one_smul, map_sum, map_smul]`.
-/
theorem hbd_hmap {H : Type} (f : G → H) (n : ℕ) (y : Ch A G (n + 1)) :
    hbd A H n (hmap A f (n + 1) y) = hmap A f n (hbd A G n y) := by
  refine ch_ext A (f := (hbd A H n).comp (hmap A f (n + 1))) (g := (hmap A f n).comp (hbd A G n)) (fun x => ?_) y
  simp only [LinearMap.comp_apply, hmap_single, hbd_single, one_smul, map_sum, map_smul]

/- English proof (translation)
Use `ch_ext A (f := (hmap A f (n + 1)).comp (cone A a n)) (g := (cone A (f a) n).comp (hmap A f n)) (fun x => ?_) y` and prove the remaining obligations. Simplify using `only [LinearMap.comp_apply, hmap_single, cone_single]`. Use `congr 1`. Use function extensionality and compare the values at `i`. Apply the tactic sequence `refine Fin.cases ?_ (fun i => ?_) i <;> simp`.
-/
theorem hmap_cone {H : Type} (f : G → H) (a : G) (n : ℕ) (y : Ch A G n) :
    hmap A f (n + 1) (cone A a n y) = cone A (f a) n (hmap A f n y) := by
  refine ch_ext A (f := (hmap A f (n + 1)).comp (cone A a n)) (g := (cone A (f a) n).comp (hmap A f n)) (fun x => ?_) y
  simp only [LinearMap.comp_apply, hmap_single, cone_single]
  congr 1
  funext i
  refine Fin.cases ?_ (fun i => ?_) i <;> simp

def pv (f : G → G) {n : ℕ} (i : Fin n) (x : Fin n → G) : Fin (n + 1) → G :=
  fun j => if (j : ℕ) ≤ i then x (i.predAbove j) else f (x (i.predAbove j))

def hprism (f : G → G) (n : ℕ) : Ch A G n →ₗ[A] Ch A G (n + 1) :=
  Finsupp.linearCombination A fun x => ∑ i : Fin n, ((-1 : A) ^ (i : ℕ)) • Finsupp.single (pv f i x) 1

/- English proof (translation)
Simplify using `only [hprism, Finsupp.linearCombination_single]`.
-/
theorem hprism_single (f : G → G) (n : ℕ) (x : Fin n → G) (c : A) : hprism A f n (Finsupp.single x c) =
    c • ∑ i : Fin n, ((-1 : A) ^ (i : ℕ)) • Finsupp.single (pv f i x) 1 := by
  simp only [hprism, Finsupp.linearCombination_single]

/- English proof (translation)
Use `ch_ext A (f := hprism A f 0) (g := 0) (fun x => ?_) y` and prove the remaining obligations. Simplify using `[hprism_single]`.
-/
theorem hprism_zero (f : G → G) (y : Ch A G 0) : hprism A f 0 y = 0 := by
  refine ch_ext A (f := hprism A f 0) (g := 0) (fun x => ?_) y
  simp [hprism_single]

/- English proof (translation)
Use `ch_ext A (f := (hprism A f (n + 1)).comp (cone A a n)) (g := (cone A a (n + 1)).comp ((cone A (f a) n).comp (hmap A f n)) - (cone A a (n + 1)).comp (hprism A f n)) (fun x => ?_) y` and prove the remaining obligations. Simplify using `only [LinearMap.comp_apply, LinearMap.sub_apply, cone_single, hmap_single, hprism_single, one_smul, map_sum, map_smul]`. Rewrite using `[Fin.sum_univ_succ, sub_eq_add_neg, ← Finset.sum_neg_distrib]`. Use `congr 1`. Simplify using `only [Fin.val_zero, pow_zero, one_smul]`.

Use `congr 1`. Use function extensionality and compare the values at `j`. Use `Fin.cases ?_ (fun j => ?_) j` and prove the remaining obligations. Simplify using `[pv]`. Apply the tactic sequence `refine Fin.cases ?_ (fun j => ?_) j <;> simp [pv]`.

Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[Fin.val_succ, pow_succ, mul_neg_one, neg_smul]`. Use `congr 3`. Use function extensionality and compare the values at `j`. Apply the tactic sequence `refine Fin.cases ?_ (fun j => ?_) j <;> simp [pv]`.
-/
theorem hprism_cone (f : G → G) (a : G) (n : ℕ) (y : Ch A G n) :
    hprism A f (n + 1) (cone A a n y) =
      cone A a (n + 1) (cone A (f a) n (hmap A f n y)) - cone A a (n + 1) (hprism A f n y) := by
  refine ch_ext A (f := (hprism A f (n + 1)).comp (cone A a n))
    (g := (cone A a (n + 1)).comp ((cone A (f a) n).comp (hmap A f n)) - (cone A a (n + 1)).comp (hprism A f n))
    (fun x => ?_) y
  simp only [LinearMap.comp_apply, LinearMap.sub_apply, cone_single, hmap_single, hprism_single, one_smul, map_sum,
    map_smul]
  rw [Fin.sum_univ_succ, sub_eq_add_neg, ← Finset.sum_neg_distrib]
  congr 1
  · simp only [Fin.val_zero, pow_zero, one_smul]
    congr 1
    funext j
    refine Fin.cases ?_ (fun j => ?_) j
    · simp [pv]
    · refine Fin.cases ?_ (fun j => ?_) j <;> simp [pv]
  · refine Finset.sum_congr rfl fun i _ => ?_
    rw [Fin.val_succ, pow_succ, mul_neg_one, neg_smul]
    congr 3
    funext j
    refine Fin.cases ?_ (fun j => ?_) j <;> simp [pv]

/- English proof (translation)
Proceed by induction on `n with`. Consider the case `zero`. Use `ch_ext A (f := (hbd A G 1).comp (hprism A f 1) + (hprism A f 0).comp (hbd A G 0)) (g := hmap A f 1 - LinearMap.id) (fun x => ?_) y` and prove the remaining obligations. Establish `hx : Finsupp.single x (1 : A) = cone A (x 0) 0 (Finsupp.single (Fin.tail x) 1)` using `by simp`. Simplify using `only [LinearMap.comp_apply, LinearMap.add_apply, LinearMap.sub_apply, LinearMap.id_apply]`.

Rewrite using `[hx, hprism_cone, hprism_zero, hprism_zero, map_zero, sub_zero, add_zero, hbd_cone, hbd_cone_zero, hmap_cone]`. Use `congr 2`. Simplify using `only [hmap_single]`. Use `congr 1`. Conclude with `Subsingleton.elim _ _`.

Consider the case `succ n ih`. Use `ch_ext A (f := (hbd A G (n + 2)).comp (hprism A f (n + 2)) + (hprism A f (n + 1)).comp (hbd A G (n + 1))) (g := hmap A f (n + 2) - LinearMap.id) (fun x => ?_) y` and prove the remaining obligations. Establish `hx : Finsupp.single x (1 : A) = cone A (x 0) (n + 1) (Finsupp.single (Fin.tail x) 1)` using `by simp`. Simplify using `only [LinearMap.comp_apply, LinearMap.add_apply, LinearMap.sub_apply, LinearMap.id_apply]`. Rewrite using `[hx]`.

Generalize the expression as in `Finsupp.single (Fin.tail x) (1 : A) = y`. Establish `h` using `eq_sub_of_add_eq (ih y)`. Simplify using `only [hprism_cone, map_sub, hbd_cone, hmap_cone, hbd_hmap, h]`. Normalize the expressions using the abelian group laws.
-/
theorem hbd_hprism (f : G → G) (n : ℕ) (y : Ch A G (n + 1)) :
    hbd A G (n + 1) (hprism A f (n + 1) y) + hprism A f n (hbd A G n y) = hmap A f (n + 1) y - y := by
  induction n with
  | zero =>
    refine ch_ext A (f := (hbd A G 1).comp (hprism A f 1) + (hprism A f 0).comp (hbd A G 0))
      (g := hmap A f 1 - LinearMap.id) (fun x => ?_) y
    have hx : Finsupp.single x (1 : A) = cone A (x 0) 0 (Finsupp.single (Fin.tail x) 1) := by simp
    simp only [LinearMap.comp_apply, LinearMap.add_apply, LinearMap.sub_apply, LinearMap.id_apply]
    rw [hx, hprism_cone, hprism_zero, hprism_zero, map_zero, sub_zero, add_zero, hbd_cone, hbd_cone_zero, hmap_cone]
    congr 2
    simp only [hmap_single]
    congr 1
    exact Subsingleton.elim _ _
  | succ n ih =>
    refine ch_ext A (f := (hbd A G (n + 2)).comp (hprism A f (n + 2)) + (hprism A f (n + 1)).comp (hbd A G (n + 1)))
      (g := hmap A f (n + 2) - LinearMap.id) (fun x => ?_) y
    have hx : Finsupp.single x (1 : A) = cone A (x 0) (n + 1) (Finsupp.single (Fin.tail x) 1) := by simp
    simp only [LinearMap.comp_apply, LinearMap.add_apply, LinearMap.sub_apply, LinearMap.id_apply]
    rw [hx]
    generalize Finsupp.single (Fin.tail x) (1 : A) = y
    have h := eq_sub_of_add_eq (ih y)
    simp only [hprism_cone, map_sub, hbd_cone, hmap_cone, hbd_hmap, h]
    abel

variable [Group G]

def toInh (G : Type) [Group G] (n : ℕ) : Ch A G (n + 1) →ₗ[A] Ch A G n :=
  Finsupp.lmapDomain A A fun x i => (x i.castSucc)⁻¹ * x i.succ

/- English proof (translation)
Simplify using `[toInh]`.
-/
@[simp] theorem toInh_single (n : ℕ) (x : Fin (n + 1) → G) (c : A) :
    toInh A G n (Finsupp.single x c) = Finsupp.single (fun i => (x i.castSucc)⁻¹ * x i.succ) c := by
  simp [toInh]

/- English proof (translation)
Simplify using `[Fin.partialProd_right_inv]`.
-/
theorem toInh_partialProd (n : ℕ) (g : Fin n → G) (c : A) :
    toInh A G n (Finsupp.single (Fin.partialProd g) c) = Finsupp.single g c := by
  simp [Fin.partialProd_right_inv]

/- English proof (translation)
Introduce `z` and use `by induction z using Finsupp.induction_linear with | zero => exact ⟨0, map_zero _⟩ | add a b ha hb => obtain ⟨a, rfl⟩ := ha obtain ⟨b, rfl⟩ := hb exact ⟨a + b, map_add _ _ _⟩ | single g c => exact ⟨_, toInh_partialProd A n g c⟩`.
-/
theorem toInh_surjective (n : ℕ) : Function.Surjective (toInh A G n) := fun z => by
  induction z using Finsupp.induction_linear with
  | zero => exact ⟨0, map_zero _⟩
  | add a b ha hb =>
    obtain ⟨a, rfl⟩ := ha
    obtain ⟨b, rfl⟩ := hb
    exact ⟨a + b, map_add _ _ _⟩
  | single g c => exact ⟨_, toInh_partialProd A n g c⟩

/- English proof (translation)
Use `ch_ext A (f := (bd A G n).comp (toInh A G (n + 1))) (g := (toInh A G n).comp (hbd A G (n + 1))) (fun x => ?_) y` and prove the remaining obligations. Simplify using `only [LinearMap.comp_apply, toInh_single, hbd_single, one_smul, map_sum, map_smul, bd, Finsupp.linearCombination_single]`. Rewrite using `[Fin.sum_univ_succ (n := n + 1)]`. Use `congr 1`. Simplify using `only [Fin.val_zero, pow_zero, one_smul, Fin.succAbove_zero, Fin.succ_castSucc]`.

Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Rewrite using `[Fin.val_succ]`. Use `congr 2`. Use function extensionality and compare the values at `i`. Establish `h1 : ∀ (p : Fin (n + 2)) (q : Fin (n + 1)), (q : ℕ) < p → p.succAbove q = q.castSucc` using `fun p q h => Fin.succAbove_of_castSucc_lt _ _ h`.

Establish `h2 : ∀ (p : Fin (n + 2)) (q : Fin (n + 1)), (p : ℕ) ≤ q → p.succAbove q = q.succ` using `fun p q h => Fin.succAbove_of_le_castSucc _ _ h`. Break down `lt_trichotomy (i : ℕ) j with h | h | h` into its components or cases. Rewrite using `[Fin.contractNth_apply_of_lt _ _ _ _ h, h1 _ _ (by simp; omega), h1 _ _ (by simp; omega), Fin.succ_castSucc]`. Rewrite using `[Fin.contractNth_apply_of_eq _ _ _ _ h, h1 _ _ (by simp; omega), h2 _ _ (by simp; omega), Fin.succ_castSucc] group`. Rewrite using `[Fin.contractNth_apply_of_gt _ _ _ _ h, h2 _ _ (by simp; omega), h2 _ _ (by simp; omega), Fin.succ_castSucc]`.
-/
theorem bd_toInh (n : ℕ) (y : Ch A G (n + 2)) : bd A G n (toInh A G (n + 1) y) = toInh A G n (hbd A G (n + 1) y) := by
  refine ch_ext A (f := (bd A G n).comp (toInh A G (n + 1))) (g := (toInh A G n).comp (hbd A G (n + 1))) (fun x => ?_) y
  simp only [LinearMap.comp_apply, toInh_single, hbd_single, one_smul, map_sum, map_smul, bd,
    Finsupp.linearCombination_single]
  rw [Fin.sum_univ_succ (n := n + 1)]
  congr 1
  · simp only [Fin.val_zero, pow_zero, one_smul, Fin.succAbove_zero, Fin.succ_castSucc]
  · refine Finset.sum_congr rfl fun j _ => ?_
    rw [Fin.val_succ]
    congr 2
    funext i
    have h1 : ∀ (p : Fin (n + 2)) (q : Fin (n + 1)), (q : ℕ) < p → p.succAbove q = q.castSucc :=
      fun p q h => Fin.succAbove_of_castSucc_lt _ _ h
    have h2 : ∀ (p : Fin (n + 2)) (q : Fin (n + 1)), (p : ℕ) ≤ q → p.succAbove q = q.succ :=
      fun p q h => Fin.succAbove_of_le_castSucc _ _ h
    rcases lt_trichotomy (i : ℕ) j with h | h | h
    · rw [Fin.contractNth_apply_of_lt _ _ _ _ h, h1 _ _ (by simp; omega), h1 _ _ (by simp; omega), Fin.succ_castSucc]
    · rw [Fin.contractNth_apply_of_eq _ _ _ _ h, h1 _ _ (by simp; omega), h2 _ _ (by simp; omega), Fin.succ_castSucc]
      group
    · rw [Fin.contractNth_apply_of_gt _ _ _ _ h, h2 _ _ (by simp; omega), h2 _ _ (by simp; omega), Fin.succ_castSucc]

/- English proof (translation)
Use `ch_ext A (f := (prism A k n).comp (toInh A G n)) (g := (toInh A G (n + 1)).comp (hprism A (· * k) (n + 1))) (fun x => ?_) y` and prove the remaining obligations. Simplify using `only [LinearMap.comp_apply, toInh_single, hprism_single, one_smul, map_sum, map_smul, prism, Finsupp.linearCombination_single]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Use `congr 2`. Use function extensionality and compare the values at `j`.

Establish `h1 : ∀ (q : Fin (n + 2)) (r : Fin (n + 1)), (q : ℕ) ≤ i → (r : ℕ) = q → pv (· * k) i x q = x r`. Introduce `q r h hr`. Rewrite using `[pv, if_pos h, Fin.predAbove_of_le_castSucc _ _ h]`. Conclude with `congrArg x (Fin.ext hr.symm)`. Establish `h2 : ∀ (q : Fin (n + 2)) (r : Fin (n + 1)), (i : ℕ) < q → (r : ℕ) + 1 = q → pv (· * k) i x q = x r * k`.

Introduce `q r h hr`. Rewrite using `[pv, if_neg (not_le.mpr h), Fin.predAbove_of_castSucc_lt _ _ h]`. Conclude with `congrArg (fun t => x t * k) (Fin.ext (by simp; omega))`. Use `Fin.succAboveCases i ?_ (fun j => ?_) j` and prove the remaining obligations. Rewrite using `[Fin.insertNth_apply_same, h1 _ i (by simp) (by simp), h2 _ i (by simp) (by simp)] group`.

Rewrite using `[Fin.insertNth_apply_succAbove] split_ifs with h`. Rewrite using `[Fin.succAbove_of_castSucc_lt _ _ h, h1 _ j.castSucc (by simp; omega) (by simp), h1 _ j.succ (by simp; omega) (by simp)]`. Rewrite using `[Fin.succAbove_of_le_castSucc _ _ (not_lt.mp h), h2 _ j.castSucc (by simp; omega) (by simp), h2 _ j.succ (by simp; omega) (by simp)] group`.
-/
theorem prism_toInh (k : G) (n : ℕ) (y : Ch A G (n + 1)) :
    prism A k n (toInh A G n y) = toInh A G (n + 1) (hprism A (· * k) (n + 1) y) := by
  refine ch_ext A (f := (prism A k n).comp (toInh A G n))
    (g := (toInh A G (n + 1)).comp (hprism A (· * k) (n + 1))) (fun x => ?_) y
  simp only [LinearMap.comp_apply, toInh_single, hprism_single, one_smul, map_sum, map_smul, prism,
    Finsupp.linearCombination_single]
  refine Finset.sum_congr rfl fun i _ => ?_
  congr 2
  funext j
  have h1 : ∀ (q : Fin (n + 2)) (r : Fin (n + 1)), (q : ℕ) ≤ i → (r : ℕ) = q → pv (· * k) i x q = x r := by
    intro q r h hr
    rw [pv, if_pos h, Fin.predAbove_of_le_castSucc _ _ h]
    exact congrArg x (Fin.ext hr.symm)
  have h2 : ∀ (q : Fin (n + 2)) (r : Fin (n + 1)), (i : ℕ) < q → (r : ℕ) + 1 = q → pv (· * k) i x q = x r * k := by
    intro q r h hr
    rw [pv, if_neg (not_le.mpr h), Fin.predAbove_of_castSucc_lt _ _ h]
    exact congrArg (fun t => x t * k) (Fin.ext (by simp; omega))
  refine Fin.succAboveCases i ?_ (fun j => ?_) j
  · rw [Fin.insertNth_apply_same, h1 _ i (by simp) (by simp), h2 _ i (by simp) (by simp)]
    group
  · rw [Fin.insertNth_apply_succAbove]
    split_ifs with h
    · rw [Fin.succAbove_of_castSucc_lt _ _ h, h1 _ j.castSucc (by simp; omega) (by simp),
        h1 _ j.succ (by simp; omega) (by simp)]
    · rw [Fin.succAbove_of_le_castSucc _ _ (not_lt.mp h), h2 _ j.castSucc (by simp; omega) (by simp),
        h2 _ j.succ (by simp; omega) (by simp)]
      group

/- English proof (translation)
Use `ch_ext A (f := (cm A (MulAut.conj k⁻¹).toMonoidHom n).comp (toInh A G n)) (g := (toInh A G n).comp (hmap A (· * k) (n + 1))) (fun x => ?_) y` and prove the remaining obligations. Simplify using `[cm, mul_assoc]`.
-/
theorem conj_toInh (k : G) (n : ℕ) (y : Ch A G (n + 1)) :
    cm A (MulAut.conj k⁻¹).toMonoidHom n (toInh A G n y) = toInh A G n (hmap A (· * k) (n + 1) y) := by
  refine ch_ext A (f := (cm A (MulAut.conj k⁻¹).toMonoidHom n).comp (toInh A G n))
    (g := (toInh A G n).comp (hmap A (· * k) (n + 1))) (fun x => ?_) y
  simp [cm, mul_assoc]

end UpperTheory.V.ZK

end

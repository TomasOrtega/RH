import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ClassCounting.LemmaKOfSteps

noncomputable section
open UpperTheory.V.ZK

namespace LateralTheory.Q.SChainPf

variable {A : Type} [CommRing A]

/- English proof (translation)
Simplify using `only [bd, Finsupp.linearCombination_single, smul_add, Finset.smul_sum, Finsupp.smul_single, smul_eq_mul, mul_one]`. Use `congr 1`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Rewrite using `[mul_comm]`.
-/
lemma bd_single {G : Type} [Group G] (m : ℕ) (g : Fin (m + 1) → G) (a : A) :
    bd A G m (Finsupp.single g a) = Finsupp.single (fun i => g i.succ) a +
      ∑ j : Fin (m + 1), ((-1 : A) ^ ((j : ℕ) + 1)) • Finsupp.single (Fin.contractNth j (· * ·) g) a := by
  simp only [bd, Finsupp.linearCombination_single, smul_add, Finset.smul_sum, Finsupp.smul_single,
    smul_eq_mul, mul_one]
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [mul_comm]

/- English proof (translation)
Use `Finsupp.lhom_ext fun g a => ?_` and prove the remaining obligations. Rewrite using `[bd_single, groupHomology.inhomogeneousChains.d_single]`. Simplify using the standard rewrite rules.
-/
lemma bd_eq {G : Type} [Group G] (m : ℕ) :
    bd A G m = (groupHomology.inhomogeneousChains.d (Rep.trivial A G A) m).hom := by
  refine Finsupp.lhom_ext fun g a => ?_
  rw [bd_single, groupHomology.inhomogeneousChains.d_single]
  simp

/- English proof (translation)
Rewrite using `[bd_eq, bd_eq]`. Establish `h` using `groupHomology.inhomogeneousChains.d_comp_d (Rep.trivial A G A) m`. Use `congrArg (fun φ => φ.hom z) h` as an intermediate fact. Simplify using `using this`.
-/
lemma bd_bd {G : Type} [Group G] (m : ℕ) (z : Ch A G (m + 2)) : bd A G m (bd A G (m + 1) z) = 0 := by
  rw [bd_eq, bd_eq]
  have h := groupHomology.inhomogeneousChains.d_comp_d (Rep.trivial A G A) m
  have := congrArg (fun φ => φ.hom z) h
  simpa using this

/- English proof (translation)
Simplify using `[cm, Finsupp.lmapDomain_apply, Finsupp.mapDomain_single]`.
-/
lemma cm_single {G H : Type} [Group G] [Group H] (f : G →* H) (m : ℕ) (g : Fin m → G) (a : A) :
    cm A f m (Finsupp.single g a) = Finsupp.single (fun i => f (g i)) a := by
  simp [cm, Finsupp.lmapDomain_apply, Finsupp.mapDomain_single]

/- English proof (translation)
Use function extensionality and compare the values at `i`. Simplify using `only [Fin.contractNth]`. Apply the tactic sequence `split_ifs <;> simp [map_mul]`.
-/
lemma contract_map {G H : Type} [Group G] [Group H] (f : G →* H) (m : ℕ) (j : Fin (m + 1))
    (g : Fin (m + 1) → G) :
    (fun i => f (Fin.contractNth j (· * ·) g i)) = Fin.contractNth j (· * ·) (fun i => f (g i)) := by
  funext i
  simp only [Fin.contractNth]
  split_ifs <;> simp [map_mul]

/- English proof (translation)
Establish `: (bd A H m).comp (cm A f (m + 1)) = (cm A f m).comp (bd A G m)`. Use `Finsupp.lhom_ext fun g a => ?_` and prove the remaining obligations. Simplify using `only [LinearMap.comp_apply, cm_single, bd_single, map_add, map_sum, map_smul]`. Simplify using `only [contract_map]`. Conclude with `LinearMap.congr_fun this z`.
-/
lemma bd_cm {G H : Type} [Group G] [Group H] (f : G →* H) (m : ℕ) (z : Ch A G (m + 1)) :
    bd A H m (cm A f (m + 1) z) = cm A f m (bd A G m z) := by
  have : (bd A H m).comp (cm A f (m + 1)) = (cm A f m).comp (bd A G m) := by
    refine Finsupp.lhom_ext fun g a => ?_
    simp only [LinearMap.comp_apply, cm_single, bd_single, map_add, map_sum, map_smul]
    simp only [contract_map]
  exact LinearMap.congr_fun this z

/- English proof (translation)
Establish `: cm A (g.comp f) m = (cm A g m).comp (cm A f m)`. Use `Finsupp.lhom_ext fun x a => ?_` and prove the remaining obligations. Simplify using `[cm_single]`. Conclude with `LinearMap.congr_fun this z`.
-/
lemma cm_comp {G H K : Type} [Group G] [Group H] [Group K] (f : G →* H) (g : H →* K) (m : ℕ)
    (z : Ch A G m) : cm A (g.comp f) m z = cm A g m (cm A f m z) := by
  have : cm A (g.comp f) m = (cm A g m).comp (cm A f m) := by
    refine Finsupp.lhom_ext fun x a => ?_
    simp [cm_single]
  exact LinearMap.congr_fun this z

/- English proof (translation)
Simplify using `only [prism, Finsupp.linearCombination_single, Finset.smul_sum, Finsupp.smul_single, smul_eq_mul, mul_one]`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Rewrite using `[mul_comm]`.
-/
lemma prism_single {G : Type} [Group G] (k : G) (m : ℕ) (g : Fin m → G) (a : A) :
    prism A k m (Finsupp.single g a) = ∑ i : Fin (m + 1), ((-1 : A) ^ (i : ℕ)) •
      Finsupp.single (Fin.insertNth (α := fun _ => G) i k
        fun j => if (j : ℕ) < i then g j else k⁻¹ * g j * k) a := by
  simp only [prism, Finsupp.linearCombination_single, Finset.smul_sum, Finsupp.smul_single,
    smul_eq_mul, mul_one]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [mul_comm]

/- English proof (translation)
Use function extensionality and compare the values at `j`. Apply the tactic sequence `refine Fin.succAboveCases i ?_ (fun j => ?_) j <;> simp`.
-/
lemma insert_map {G H : Type} [Group G] [Group H] (f : G →* H) (m : ℕ) (i : Fin (m + 1)) (k : G)
    (h : Fin m → G) :
    (fun j => f (Fin.insertNth (α := fun _ => G) i k h j)) =
      Fin.insertNth (α := fun _ => H) i (f k) (fun j => f (h j)) := by
  funext j
  refine Fin.succAboveCases i ?_ (fun j => ?_) j <;> simp

/- English proof (translation)
Use function extensionality and compare the values at `j`. Apply the tactic sequence `split_ifs <;> simp [map_mul, map_inv]`.
-/
lemma conj_map {G H : Type} [Group G] [Group H] (f : G →* H) (m : ℕ) (i : Fin (m + 1)) (k : G)
    (g : Fin m → G) :
    (fun j : Fin m => f (if (j : ℕ) < i then g j else k⁻¹ * g j * k)) =
      fun j : Fin m => if (j : ℕ) < i then f (g j) else (f k)⁻¹ * f (g j) * f k := by
  funext j
  split_ifs <;> simp [map_mul, map_inv]

/- English proof (translation)
Establish `: (cm A f (m + 1)).comp (prism A k m) = (prism A (f k) m).comp (cm A f m)`. Use `Finsupp.lhom_ext fun g a => ?_` and prove the remaining obligations. Simplify using `only [LinearMap.comp_apply, cm_single, prism_single, map_sum, map_smul]`. Simplify using `only [insert_map, conj_map]`. Conclude with `LinearMap.congr_fun this z`.
-/
lemma cm_prism {G H : Type} [Group G] [Group H] (f : G →* H) (k : G) (m : ℕ) (z : Ch A G m) :
    cm A f (m + 1) (prism A k m z) = prism A (f k) m (cm A f m z) := by
  have : (cm A f (m + 1)).comp (prism A k m) = (prism A (f k) m).comp (cm A f m) := by
    refine Finsupp.lhom_ext fun g a => ?_
    simp only [LinearMap.comp_apply, cm_single, prism_single, map_sum, map_smul]
    simp only [insert_map, conj_map]
  exact LinearMap.congr_fun this z

def S (n : ℕ) : A := ∑ j : Fin n, (-1 : A) ^ ((j : ℕ) + 1)

/- English proof (translation)
Proceed by induction on `n with`. Consider the case `zero => simp [S]`. Consider the case `succ n ih`. Establish `h2 : (S (n + 2) : A) = S n`. Simplify using `only [S, Fin.sum_univ_castSucc, Fin.val_castSucc, Fin.val_last]`.

Expand and normalize the polynomial expressions, which then agree. Rewrite using `[h2, add_comm]`. Conclude with `ih`.
-/
lemma S_pair (n : ℕ) : (S n : A) + S (n + 1) = -1 := by
  induction n with
  | zero => simp [S]
  | succ n ih =>
    have h2 : (S (n + 2) : A) = S n := by
      simp only [S, Fin.sum_univ_castSucc, Fin.val_castSucc, Fin.val_last]
      ring
    rw [h2, add_comm]; exact ih

/- English proof (translation)
Rewrite using `[bd_single]`. Establish `e1 : (fun i => g i.succ) = h` using `Subsingleton.elim _ _`. Establish `e2 : ∀ j : Fin (m + 1), Fin.contractNth j (· * ·) g = h` using `fun _ => Subsingleton.elim _ _`. Simplify using `only [e1, e2, Finsupp.smul_single, smul_eq_mul, ← Finsupp.single_finsetSum, ← Finsupp.single_add, S, add_mul, Finset.sum_mul, one_mul]`.
-/
lemma bd_single_triv {G : Type} [Group G] [Subsingleton G] (m : ℕ) (g : Fin (m + 1) → G)
    (h : Fin m → G) (a : A) : bd A G m (Finsupp.single g a) = Finsupp.single h ((1 + S (m + 1)) * a) := by
  rw [bd_single]
  have e1 : (fun i => g i.succ) = h := Subsingleton.elim _ _
  have e2 : ∀ j : Fin (m + 1), Fin.contractNth j (· * ·) g = h := fun _ => Subsingleton.elim _ _
  simp only [e1, e2, Finsupp.smul_single, smul_eq_mul, ← Finsupp.single_finsetSum, ← Finsupp.single_add,
    S, add_mul, Finset.sum_mul, one_mul]

/- English proof (translation)
Set `g1 : Fin (m + 1) → G` to `fun _ => 1`. Set `g0 : Fin m → G` to `fun _ => 1`. Set `g2 : Fin (m + 2) → G` to `fun _ => 1`. Establish `hz1 : z = Finsupp.single g1 (z g1)`. Use extensionality with `x`.

Rewrite using `[Subsingleton.elim x g1]`. Simplify using the standard rewrite rules. Generalize the expression as in `z g1 = c at hz1`. Substitute `hz1` using the available equality. Establish `hc : (1 + S (m + 1)) * c = 0`.

Use `hz` as an intermediate fact. Unfold `Cyc at this`. Rewrite `this` using `[bd_single_triv m g1 g0]`. Simplify using `using congrArg (fun w => w g0) this`. Use `⟨Finsupp.single g2 (c), ?_⟩` and prove the remaining obligations.

Rewrite using `[bd_single_triv (m + 1) g2 g1]`. Use `congr 1`. Use `S_pair (A := A) (m + 1)` as an intermediate fact. Take the linear combination `(-1 : A) * hc + (c) * this`.
-/
lemma triv_bd {G : Type} [Group G] [Subsingleton G] (m : ℕ) (z : Ch A G (m + 1)) (hz : Cyc z) : Bd z := by
  let g1 : Fin (m + 1) → G := fun _ => 1
  let g0 : Fin m → G := fun _ => 1
  let g2 : Fin (m + 2) → G := fun _ => 1
  have hz1 : z = Finsupp.single g1 (z g1) := by
    ext x; rw [Subsingleton.elim x g1]; simp
  generalize z g1 = c at hz1
  subst hz1
  have hc : (1 + S (m + 1)) * c = 0 := by
    have := hz
    unfold Cyc at this
    rw [bd_single_triv m g1 g0] at this
    simpa using congrArg (fun w => w g0) this
  refine ⟨Finsupp.single g2 (c), ?_⟩
  rw [bd_single_triv (m + 1) g2 g1]
  congr 1
  have := S_pair (A := A) (m + 1)
  linear_combination (-1 : A) * hc + (c) * this

/- English proof (translation)
Introduce `_ _` and use `⟨fun _ _ m z => bd_bd m z, fun _ _ _ _ f m z => bd_cm f m z, fun _ _ _ _ _ _ f g m z => cm_comp f g m z, fun _ _ _ _ f k m z => cm_prism f k m z, fun _ _ _ m z hz => triv_bd m z hz⟩`.
-/
theorem SChain_of : UpperTheory.V.ZK.SChain :=
  fun _ _ => ⟨fun _ _ m z => bd_bd m z, fun _ _ _ _ f m z => bd_cm f m z,
    fun _ _ _ _ _ _ f g m z => cm_comp f g m z, fun _ _ _ _ f k m z => cm_prism f k m z,
    fun _ _ _ m z hz => triv_bd m z hz⟩

end LateralTheory.Q.SChainPf

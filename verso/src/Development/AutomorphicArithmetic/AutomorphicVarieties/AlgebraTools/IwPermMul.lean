import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.HeckePairTop
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.IwHkMul
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.IwSimpleOrbit
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.IwPermCard
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.IwLenStep
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.IwHeckePairIwC

open ValuativeRel Matrix GlobalTheory.SmGL GlobalTheory.SplitWeil UpperTheory.V.Hi UpperTheory.V.AlgebraTools

/- English proof (translation)
Establish `hinv : (pm R n w)⁻¹ = pm R n w⁻¹` using `(map_inv _ _).symm`. Rewrite using `[hinv, Units.val_mul, Units.val_mul, Matrix.mul_apply]`. Simplify using `[-map_inv, Matrix.mul_apply, pm_apply, Equiv.Perm.eq_inv_iff_eq, Equiv.eq_symm_apply]`.
-/
private theorem pm_conj_apply (R : Type) [CommRing R] {n : ℕ} (w : Equiv.Perm (Fin n)) (g : GL (Fin n) R)
    (a b : Fin n) :
    (((pm R n w)⁻¹ * g * pm R n w : GL (Fin n) R) : Matrix (Fin n) (Fin n) R) a b =
      (g : Matrix (Fin n) (Fin n) R) (w a) (w b) := by
  have hinv : (pm R n w)⁻¹ = pm R n w⁻¹ := (map_inv _ _).symm
  rw [hinv, Units.val_mul, Units.val_mul, Matrix.mul_apply]
  simp [-map_inv, Matrix.mul_apply, pm_apply, Equiv.Perm.eq_inv_iff_eq, Equiv.eq_symm_apply]

/- English proof (translation)
Use `⟨pm 𝒪[k] n w, ?_⟩` and prove the remaining obligations. Use extensionality with `a b`. Simplify using `[pm_apply]`.
-/
private theorem pm_mem_KO (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    {n : ℕ} (w : Equiv.Perm (Fin n)) : pm k n w ∈ KO k (Fin n) := by
  refine ⟨pm 𝒪[k] n w, ?_⟩
  ext a b
  simp [pm_apply]

/- English proof (translation)
Unfold `invLen`. Rewrite using `[Finset.card_eq_zero, Finset.filter_eq_empty_iff]`. Introduce and unpack `p - ⟨h1, h2⟩`. Conclude with `lt_asymm h1 h2`.
-/
private theorem invLen_one (n : ℕ) : invLen (1 : Equiv.Perm (Fin n)) = 0 := by
  unfold invLen
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  rintro p - ⟨h1, h2⟩
  exact lt_asymm h1 h2

/- English proof (translation)
Introduce `k _ _ _ _ n C A M _ _ _ ρ w i j hij hlt`. Rewrite using `[map_mul]`. Establish `hP` using `(heckePairIwC k n C).1`. Establish `hne : i ≠ j`. Introduce `h`.

Rewrite `hij` using `[h]`. Use linear arithmetic over natural numbers and integers. Establish `hU : unipO k n ≤ iwC k n C`. Unfold `iwC`. Conclude with `le_sup_right.trans le_sup_left`.

Apply `hkMul A _ M ρ _ _ _ hP` to reduce the goal to its premises. Introduce `b hb`. Take `⟨r, hr⟩ : ∃ r : 𝓀[k] → 𝒪[k], ∀ c, IsLocalRing.residue 𝒪[k] (r c) = c` from `⟨fun c => (IsLocalRing.residue_surjective c).choose, fun c => (IsLocalRing.residue_surjective c).choose_spec⟩`. Take `⟨x, hx1, hx2, -, hx4⟩` from `simpleOrbit k n C i j hij r hr`. Take `⟨c, b', hb', he⟩` from `hx4 b hb`.

Establish `hxc : x c ∈ unipB k (Fin n) ⊓ KO k (Fin n)` using `hx2 c`. Establish `hmem : (pm k n w)⁻¹ * x c * pm k n w ∈ unipO k n`. Unfold `unipO`. Use `Subgroup.mem_inf.2 ⟨(mem_unipB k).2 ⟨?_, ?_⟩, ?_⟩` and prove the remaining obligations. Introduce `a b hba`.

Rewrite using `[pm_conj_apply, hx1 c]`. Establish `hab : w a ≠ w b` using `fun h => (ne_of_lt hba) (w.injective h).symm`. Rewrite using `[Matrix.add_apply, Matrix.one_apply_ne hab, zero_add, Matrix.single_apply, if_neg]`. Introduce and unpack `⟨h1, h2⟩`. Apply `absurd hlt` to reduce the goal to its premises.

Rewrite using `[h1, h2]`. Simplify using `using hba.le`. Introduce `a`. Rewrite using `[pm_conj_apply, hx1 c]`. Rewrite using `[Matrix.add_apply, Matrix.one_apply_eq, Matrix.single_apply, if_neg, add_zero]`.

Introduce and unpack `⟨h1, h2⟩`. Conclude with `hne (h1.trans h2.symm)`. Conclude with `Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ (pm_mem_KO k w)) (Subgroup.mem_inf.1 hxc).2) (pm_mem_KO k w)`. Use `⟨b', hb', (pm k n w)⁻¹ * x c * pm k n w, hU hmem, ?_⟩` and prove the remaining obligations. Rewrite using `[he]`.

Use `group`. Rewrite using `[← map_mul, permCard, permCard, permCard, ((lenStep n w).1 i j hij).1 hlt]`. Establish `hij' : (1 : Equiv.Perm (Fin n))⁻¹ i < (1 : Equiv.Perm (Fin n))⁻¹ j`. Rewrite using `[inv_one]`. Use `show i < j`.

Rewrite using `[Fin.lt_def]`. Use linear arithmetic over natural numbers and integers. Establish `h1` using `((lenStep n 1).1 i j hij).1 hij'`. Rewrite `h1` using `[mul_one, invLen_one]`. Rewrite using `[h1]`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem UpperTheory.V.AlgebraTools.permMul :
    ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ) (C : Subgroup 𝓀[k]ˣ) (A M : Type) [CommRing A] [AddCommGroup M] [Module A M] (ρ : Representation A (GL (Fin n) k) M) (w : Equiv.Perm (Fin n)) (i j : Fin n), (j : ℕ) = i + 1 → w⁻¹ i < w⁻¹ j → hk ρ (iwC k n C) (pm k n (Equiv.swap i j)) * hk ρ (iwC k n C) (pm k n w) = hk ρ (iwC k n C) (pm k n (Equiv.swap i j * w)) := by
  intro k _ _ _ _ n C A M _ _ _ ρ w i j hij hlt
  rw [map_mul]
  have hP := (heckePairIwC k n C).1
  have hne : i ≠ j := by
    intro h
    rw [h] at hij
    omega
  have hU : unipO k n ≤ iwC k n C := by
    unfold iwC
    exact le_sup_right.trans le_sup_left
  apply hkMul A _ M ρ _ _ _ hP
  · intro b hb
    obtain ⟨r, hr⟩ : ∃ r : 𝓀[k] → 𝒪[k], ∀ c, IsLocalRing.residue 𝒪[k] (r c) = c :=
      ⟨fun c => (IsLocalRing.residue_surjective c).choose,
        fun c => (IsLocalRing.residue_surjective c).choose_spec⟩
    obtain ⟨x, hx1, hx2, -, hx4⟩ := simpleOrbit k n C i j hij r hr
    obtain ⟨c, b', hb', he⟩ := hx4 b hb
    have hxc : x c ∈ unipB k (Fin n) ⊓ KO k (Fin n) := hx2 c
    have hmem : (pm k n w)⁻¹ * x c * pm k n w ∈ unipO k n := by
      unfold unipO
      refine Subgroup.mem_inf.2 ⟨(mem_unipB k).2 ⟨?_, ?_⟩, ?_⟩
      · intro a b hba
        rw [pm_conj_apply, hx1 c]
        have hab : w a ≠ w b := fun h => (ne_of_lt hba) (w.injective h).symm
        rw [Matrix.add_apply, Matrix.one_apply_ne hab, zero_add, Matrix.single_apply, if_neg]
        rintro ⟨h1, h2⟩
        apply absurd hlt
        rw [h1, h2]
        simpa using hba.le
      · intro a
        rw [pm_conj_apply, hx1 c]
        rw [Matrix.add_apply, Matrix.one_apply_eq, Matrix.single_apply, if_neg, add_zero]
        rintro ⟨h1, h2⟩
        exact hne (h1.trans h2.symm)
      · exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ (pm_mem_KO k w))
          (Subgroup.mem_inf.1 hxc).2) (pm_mem_KO k w)
    refine ⟨b', hb', (pm k n w)⁻¹ * x c * pm k n w, hU hmem, ?_⟩
    rw [he]
    group
  · rw [← map_mul, permCard, permCard, permCard, ((lenStep n w).1 i j hij).1 hlt]
    have hij' : (1 : Equiv.Perm (Fin n))⁻¹ i < (1 : Equiv.Perm (Fin n))⁻¹ j := by
      rw [inv_one]
      show i < j
      rw [Fin.lt_def]
      omega
    have h1 := ((lenStep n 1).1 i j hij).1 hij'
    rw [mul_one, invLen_one] at h1
    rw [h1]
    ring

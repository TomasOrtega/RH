import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.KTypeLemma.QuotientHighestWeightTensorStandard
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.JDichoA

noncomputable section

open Finset Matrix ComplexConjugate
open ReciprocityTheory.ChartRestriction.DS.Mult1.ConjugateHilbertSpace

namespace ReciprocityTheory.ChartRestriction.DS.Lap.LemK.DualRepresentationReversal

open ReciprocityTheory.ChartRestriction.DS

variable {n : ℕ}

def sub (A : Matrix (Fin n) (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ := A.submatrix Fin.revPerm Fin.revPerm

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem sub_apply (A : Matrix (Fin n) (Fin n) ℂ) (a b : Fin n) : sub A a b = A (Fin.rev a) (Fin.rev b) := rfl

/- English proof (translation)
Simplify using `only [sub]`. Conclude with `(Matrix.submatrix_mul_equiv _ _ _ _ _).symm`.
-/
theorem sub_mul (A B : Matrix (Fin n) (Fin n) ℂ) : sub (A * B) = sub A * sub B := by
  simp only [sub]
  exact (Matrix.submatrix_mul_equiv _ _ _ _ _).symm

/- English proof (translation)
Simplify using `only [sub]`. Conclude with `Matrix.submatrix_one_equiv _`.
-/
theorem sub_one : sub (1 : Matrix (Fin n) (Fin n) ℂ) = 1 := by
  simp only [sub]
  exact Matrix.submatrix_one_equiv _

/- English proof (translation)
Simplify using `[sub, Matrix.conjTranspose_submatrix]`.
-/
theorem sub_H (A : Matrix (Fin n) (Fin n) ℂ) : (sub A)ᴴ = sub Aᴴ := by
  simp [sub, Matrix.conjTranspose_submatrix]

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem sub_add (A B : Matrix (Fin n) (Fin n) ℂ) : sub (A + B) = sub A + sub B := rfl

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem sub_smul (c : ℂ) (A : Matrix (Fin n) (Fin n) ℂ) : sub (c • A) = c • sub A := rfl

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem sub_zero : sub (0 : Matrix (Fin n) (Fin n) ℂ) = 0 := rfl

def Pr (n : ℕ) : Matrix (Fin n) (Fin n) ℂ := Matrix.of fun i j => if i = Fin.rev j then 1 else 0

/- English proof (translation)
Use extensionality with `i j`. Rewrite using `[Matrix.mul_apply, Finset.sum_eq_single (Fin.rev i)]`. Simplify using `[Pr]`. Introduce `k _ hk`. Simplify using `only [Pr, Matrix.of_apply]`.

Rewrite using `[if_neg (fun h => hk (by rw [h, Fin.rev_rev]))]`. Expand and normalize the polynomial expressions, which then agree. Simplify using the standard rewrite rules.
-/
theorem Pr_mul (A : Matrix (Fin n) (Fin n) ℂ) : Pr n * A = A.submatrix Fin.rev id := by
  ext i j
  rw [Matrix.mul_apply, Finset.sum_eq_single (Fin.rev i)]
  · simp [Pr]
  · intro k _ hk
    simp only [Pr, Matrix.of_apply]
    rw [if_neg (fun h => hk (by rw [h, Fin.rev_rev]))]
    ring
  · simp

/- English proof (translation)
Use extensionality with `i j`. Rewrite using `[Matrix.mul_apply, Finset.sum_eq_single (Fin.rev j)]`. Simplify using `[Pr]`. Introduce `k _ hk`. Simplify using `only [Pr, Matrix.of_apply]`.

Rewrite using `[if_neg hk]`. Expand and normalize the polynomial expressions, which then agree. Simplify using the standard rewrite rules.
-/
theorem mul_Pr (A : Matrix (Fin n) (Fin n) ℂ) : A * Pr n = A.submatrix id Fin.rev := by
  ext i j
  rw [Matrix.mul_apply, Finset.sum_eq_single (Fin.rev j)]
  · simp [Pr]
  · intro k _ hk
    simp only [Pr, Matrix.of_apply]
    rw [if_neg hk]
    ring
  · simp

/- English proof (translation)
Rewrite using `[Pr_mul, mul_Pr]`. Use extensionality with `i j`. Simplify using `[sub]`.
-/
theorem Pr_conj (A : Matrix (Fin n) (Fin n) ℂ) : Pr n * A * Pr n = sub A := by
  rw [Pr_mul, mul_Pr]
  ext i j
  simp [sub]

/- English proof (translation)
Rewrite using `[Pr_mul]`. Use extensionality with `i j`. Simplify using `[Pr, Matrix.one_apply]`.
-/
theorem Pr_Pr : Pr n * Pr n = 1 := by
  rw [Pr_mul]
  ext i j
  simp [Pr, Matrix.one_apply]

/- English proof (translation)
Conclude with `Matrix.inv_eq_left_inv Pr_Pr`.
-/
theorem Pr_inv : (Pr n)⁻¹ = Pr n := by
  exact Matrix.inv_eq_left_inv Pr_Pr

/- English proof (translation)
Establish `hu : IsUnit (Pr n)` using `⟨⟨Pr n, Pr n, Pr_Pr, Pr_Pr⟩, rfl⟩`. Rewrite using `[← Pr_conj, ← Pr_conj (NormedSpace.exp A)]`. Establish `h1 : Pr n * A * Pr n = Pr n * A * (Pr n)⁻¹` using `by rw [Pr_inv]`. Rewrite using `[h1, Matrix.exp_conj _ _ hu, Pr_inv]`.
-/
theorem exp_sub (A : Matrix (Fin n) (Fin n) ℂ) : NormedSpace.exp (sub A) = sub (NormedSpace.exp A) := by
  have hu : IsUnit (Pr n) := ⟨⟨Pr n, Pr n, Pr_Pr, Pr_Pr⟩, rfl⟩
  rw [← Pr_conj, ← Pr_conj (NormedSpace.exp A)]
  have h1 : Pr n * A * Pr n = Pr n * A * (Pr n)⁻¹ := by rw [Pr_inv]
  rw [h1, Matrix.exp_conj _ _ hu, Pr_inv]

/- English proof (translation)
Use extensionality with `a b`. Simplify using `[sub, Jm, Matrix.diagonal_apply]`.
-/
theorem Jm_rev (ε : Fin n → Bool) : sub (Jm (ε ∘ Fin.rev)) = Jm ε := by
  ext a b
  simp [sub, Jm, Matrix.diagonal_apply]

/- English proof (translation)
Use `show (sub g)ᴴ * Jm ε * sub g = Jm ε`. Establish `hg' : gᴴ * Jm (ε ∘ Fin.rev) * g = Jm (ε ∘ Fin.rev)` using `hg`. Rewrite using `[← Jm_rev ε, sub_H, ← sub_mul, ← sub_mul, hg']`.
-/
theorem inUJ_sub {ε : Fin n → Bool} {g : Matrix (Fin n) (Fin n) ℂ} (hg : g ∈ UJset (ε ∘ Fin.rev)) :
    sub g ∈ UJset ε := by
  show (sub g)ᴴ * Jm ε * sub g = Jm ε
  have hg' : gᴴ * Jm (ε ∘ Fin.rev) * g = Jm (ε ∘ Fin.rev) := hg
  rw [← Jm_rev ε, sub_H, ← sub_mul, ← sub_mul, hg']

/- English proof (translation)
Unfold `inG at *`. Rewrite using `[← Jm_rev ε, sub_H, ← sub_mul, ← sub_mul, ← sub_add, hX, sub_zero]`.
-/
theorem inG_sub {ε : Fin n → Bool} {X : Matrix (Fin n) (Fin n) ℂ} (hX : inG (ε ∘ Fin.rev) X) :
    inG ε (sub X) := by
  unfold inG at *
  rw [← Jm_rev ε, sub_H, ← sub_mul, ← sub_mul, ← sub_add, hX, sub_zero]

/- English proof (translation)
Simplify using `only [Kset, Set.mem_setOf_eq] at hk ⊢`. Take `⟨hu, hc⟩` from `hk`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Rewrite `hu`, the goal using `[Matrix.mem_unitaryGroup_iff]`. Rewrite `hu`, the goal using `[Matrix.star_eq_conjTranspose]`.

Rewrite using `[sub_H, ← sub_mul, hu, sub_one]`. Rewrite using `[← Jm_rev ε, ← sub_mul, ← sub_mul, hc]`.
-/
theorem K_sub {ε : Fin n → Bool} {k : Matrix (Fin n) (Fin n) ℂ} (hk : k ∈ Kset (ε ∘ Fin.rev)) :
    sub k ∈ Kset ε := by
  simp only [Kset, Set.mem_setOf_eq] at hk ⊢
  obtain ⟨hu, hc⟩ := hk
  refine ⟨?_, ?_⟩
  · rw [Matrix.mem_unitaryGroup_iff] at hu ⊢
    rw [Matrix.star_eq_conjTranspose] at hu ⊢
    rw [sub_H, ← sub_mul, hu, sub_one]
  · rw [← Jm_rev ε, ← sub_mul, ← sub_mul, hc]

/- English proof (translation)
Establish `h` using `congrFun (congrFun hX b) a`. Rewrite `h` using `[Matrix.add_apply, Jm, Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.conjTranspose_apply, Matrix.zero_apply]`. Apply the tactic sequence `cases hεa : ε a <;> cases hεb : ε b <;> simp [hεa, hεb, Complex.star_def] at h ⊢ <;> first | linear_combination h | linear_combination -h`.
-/
theorem inG_entry {ε : Fin n → Bool} {X : Matrix (Fin n) (Fin n) ℂ} (hX : inG ε X) (a b : Fin n) :
    X b a = (if ε a = ε b then -1 else 1) * conj (X a b) := by
  have h := congrFun (congrFun hX b) a
  rw [Matrix.add_apply, Jm, Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.conjTranspose_apply,
    Matrix.zero_apply] at h
  cases hεa : ε a <;> cases hεb : ε b <;> simp [hεa, hεb, Complex.star_def] at h ⊢ <;>
    first | linear_combination h | linear_combination -h

section Conj

variable {n : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

def cjSub (S : Submodule ℂ H) : Submodule ℂ (Cj H) where
  carrier := {x | ofCj x ∈ S}
  add_mem' hx hy := S.add_mem hx hy
  zero_mem' := S.zero_mem
  smul_mem' c _ hx := S.smul_mem (conj c) hx

variable {D : Submodule ℂ H}

def toD (x : cjSub D) : D := ⟨ofCj (x : Cj H), x.2⟩

def ofD (u : D) : cjSub D := ⟨toCj (u : H), u.2⟩

/- English proof (translation)
Both sides reduce to the same expression.
-/
@[simp] theorem toD_ofD (u : D) : toD (ofD u) = u := rfl

/- English proof (translation)
Both sides reduce to the same expression.
-/
@[simp] theorem ofD_toD (x : cjSub D) : ofD (toD x) = x := rfl

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem ofD_add (u v : D) : ofD (u + v) = ofD u + ofD v := rfl

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem ofD_sub (u v : D) : ofD (u - v) = ofD u - ofD v := rfl

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem ofD_neg (u : D) : ofD (-u) = -ofD u := rfl

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem ofD_zero : ofD (0 : D) = 0 := rfl

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem toD_add (x y : cjSub D) : toD (x + y) = toD x + toD y := rfl

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem toD_smul (c : ℂ) (x : cjSub D) : toD (c • x) = conj c • toD x := rfl

/- English proof (translation)
Establish `h` using `toD_smul (conj c) (ofD u)`. Rewrite `h` using `[toD_ofD, Complex.conj_conj]`. Rewrite using `[← h, ofD_toD]`.
-/
theorem ofD_smul (c : ℂ) (u : D) : ofD (c • u) = conj c • ofD u := by
  have h := toD_smul (conj c) (ofD u)
  rw [toD_ofD, Complex.conj_conj] at h
  rw [← h, ofD_toD]

/- English proof (translation)
Introduce `u v h`. Use `congrArg toD h` as an intermediate fact. Simplify using `using this`.
-/
theorem ofD_injective : Function.Injective (ofD : D → cjSub D) := by
  intro u v h
  have := congrArg toD h
  simpa using this

def ofDh : D →+ cjSub D where
  toFun := ofD
  map_zero' := rfl
  map_add' := ofD_add

/- English proof (translation)
Conclude with `map_sum ofDh f s`.
-/
theorem ofD_sum {ι : Type*} (s : Finset ι) (f : ι → D) : ofD (∑ i ∈ s, f i) = ∑ i ∈ s, ofD (f i) := by
  exact map_sum ofDh f s

def ofDL : D →ₛₗ[starRingEnd ℂ] cjSub D where
  toFun := ofD
  map_add' := ofD_add
  map_smul' := ofD_smul

def cjEnd (A : Module.End ℂ D) : Module.End ℂ (cjSub D) where
  toFun x := ofD (A (toD x))
  map_add' x y := by rw [toD_add, map_add, ofD_add]
  map_smul' c x := by
    show ofD (A (toD (c • x))) = c • ofD (A (toD x))
    rw [toD_smul, A.map_smul, ofD_smul]
    simp

def sg (ε : Fin n → Bool) (a : Fin n) : ℂ := if ε (Fin.rev a) then 1 else -1

/- English proof (translation)
Unfold `sg`. Apply the tactic sequence `split_ifs <;> norm_num`.
-/
theorem sg_sq (ε : Fin n → Bool) (a : Fin n) : sg ε a * sg ε a = 1 := by
  unfold sg
  split_ifs <;> norm_num

/- English proof (translation)
Unfold `sg`. Apply the tactic sequence `split_ifs <;> simp`.
-/
theorem conj_sg (ε : Fin n → Bool) (a : Fin n) : conj (sg ε a) = sg ε a := by
  unfold sg
  split_ifs <;> simp

/- English proof (translation)
Unfold `sg`. Apply the tactic sequence `split_ifs <;> norm_num`.
-/
theorem sg_ne (ε : Fin n → Bool) (a : Fin n) : sg ε a ≠ 0 := by
  unfold sg
  split_ifs <;> norm_num

def Edd (ε : Fin n → Bool) (E : Fin n → Fin n → Module.End ℂ D) (a b : Fin n) : Module.End ℂ (cjSub D) :=
  cjEnd ((-(sg ε a * sg ε b)) • E (Fin.rev b) (Fin.rev a))

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem Edd_ofD (ε : Fin n → Bool) (E : Fin n → Fin n → Module.End ℂ D) (a b : Fin n) (u : D) :
    Edd ε E a b (ofD u) = ofD ((-(sg ε a * sg ε b)) • E (Fin.rev b) (Fin.rev a) u) := rfl

/- English proof (translation)
Introduce `a b c d`. Apply `LinearMap.ext` to reduce the goal to its premises. Introduce `x`. Take `⟨u, rfl⟩ : ∃ u, x = ofD u` from `⟨toD x, (ofD_toD x).symm⟩`. Establish `key` using `congrArg (fun T : Module.End ℂ D => T u) (hE (Fin.rev b) (Fin.rev a) (Fin.rev d) (Fin.rev c))`.

Simplify using `only [LinearMap.sub_apply, Module.End.mul_apply, Fin.rev_inj] at key`. Establish `lhs : (Edd ε E a b * Edd ε E c d - Edd ε E c d * Edd ε E a b) (ofD u) = ofD ((sg ε a * sg ε b * (sg ε c * sg ε d)) • (E (Fin.rev b) (Fin.rev a) (E (Fin.rev d) (Fin.rev c) u) - E (Fin.rev d) (Fin.rev c) (E (Fin.rev b) (Fin.rev a) u)))`. Simplify using `only [LinearMap.sub_apply, Module.End.mul_apply, Edd_ofD, LinearMap.map_smul]`. Rewrite using `[← ofD_sub]`. Use `congr 1`.

Use `module`. Rewrite using `[lhs, key, LinearMap.sub_apply]`. Apply the tactic sequence `by_cases hbc : b = c <;> by_cases hda : d = a`. Substitute `c` using the available equality. Substitute `d` using the available equality.

Simplify using `only [eq_self_iff_true, if_true, Edd_ofD]`. Rewrite using `[← ofD_sub]`. Use `congr 1`. Unfold `sg`. Apply the tactic sequence `split_ifs <;> module`.

Substitute `c` using the available equality. Establish `hda' : ¬ Fin.rev a = Fin.rev d` using `fun h => hda (Fin.rev_injective h).symm`. Simplify using `only [eq_self_iff_true, if_true, if_neg hda, if_neg (Ne.symm hda), if_neg hda', LinearMap.zero_apply, Edd_ofD, sub_zero, zero_sub]`. Use `first`. Consider the case `(congr 1; unfold sg; split_ifs <;> module)`.

Consider the case `(rw [← ofD_neg]; congr 1; unfold sg; split_ifs <;> module)`. Consider the case `(apply ofD_injective; unfold sg; split_ifs <;> module)`. Consider the case `(simp only [← ofD_neg, ← ofD_sub, ← ofD_zero]; congr 1; unfold sg; split_ifs <;> module)`. Substitute `d` using the available equality. Establish `hbc' : ¬ Fin.rev c = Fin.rev b` using `fun h => hbc (Fin.rev_injective h).symm`.

Simplify using `only [eq_self_iff_true, if_true, if_neg hbc, if_neg (Ne.symm hbc), if_neg hbc', LinearMap.zero_apply, Edd_ofD, sub_zero, zero_sub]`. Simplify using `only [sub_zero, zero_sub, LinearMap.zero_apply, ← ofD_neg, ← ofD_sub]`. Use `congr 1`. Unfold `sg`. Apply the tactic sequence `split_ifs <;> module`.

Establish `hda' : ¬ Fin.rev a = Fin.rev d` using `fun h => hda (Fin.rev_injective h).symm`. Establish `hbc' : ¬ Fin.rev c = Fin.rev b` using `fun h => hbc (Fin.rev_injective h).symm`. Simplify using `only [if_neg hbc, if_neg (Ne.symm hbc), if_neg hda, if_neg (Ne.symm hda), if_neg hda', if_neg hbc', LinearMap.zero_apply, sub_zero, smul_zero]`. Simplify using `[ofD_zero]`.
-/
theorem glRep_Edd (ε : Fin n → Bool) {E : Fin n → Fin n → Module.End ℂ D} (hE : IsGlRep E) :
    IsGlRep (Edd ε E) := by
  intro a b c d
  apply LinearMap.ext
  intro x
  obtain ⟨u, rfl⟩ : ∃ u, x = ofD u := ⟨toD x, (ofD_toD x).symm⟩
  have key := congrArg (fun T : Module.End ℂ D => T u) (hE (Fin.rev b) (Fin.rev a) (Fin.rev d) (Fin.rev c))
  simp only [LinearMap.sub_apply, Module.End.mul_apply, Fin.rev_inj] at key
  have lhs : (Edd ε E a b * Edd ε E c d - Edd ε E c d * Edd ε E a b) (ofD u) =
      ofD ((sg ε a * sg ε b * (sg ε c * sg ε d)) • (E (Fin.rev b) (Fin.rev a) (E (Fin.rev d) (Fin.rev c) u) -
        E (Fin.rev d) (Fin.rev c) (E (Fin.rev b) (Fin.rev a) u))) := by
    simp only [LinearMap.sub_apply, Module.End.mul_apply, Edd_ofD, LinearMap.map_smul]
    rw [← ofD_sub]
    congr 1
    module
  rw [lhs, key, LinearMap.sub_apply]
  by_cases hbc : b = c <;> by_cases hda : d = a
  · subst c
    subst d
    simp only [eq_self_iff_true, if_true, Edd_ofD]
    rw [← ofD_sub]
    congr 1
    unfold sg
    split_ifs <;> module
  · subst c
    have hda' : ¬ Fin.rev a = Fin.rev d := fun h => hda (Fin.rev_injective h).symm
    simp only [eq_self_iff_true, if_true, if_neg hda, if_neg (Ne.symm hda), if_neg hda', LinearMap.zero_apply, Edd_ofD,
      sub_zero, zero_sub]
    first
    | (congr 1; unfold sg; split_ifs <;> module)
    | (rw [← ofD_neg]; congr 1; unfold sg; split_ifs <;> module)
    | (apply ofD_injective; unfold sg; split_ifs <;> module)
    | (simp only [← ofD_neg, ← ofD_sub, ← ofD_zero]; congr 1; unfold sg; split_ifs <;> module)
  · subst d
    have hbc' : ¬ Fin.rev c = Fin.rev b := fun h => hbc (Fin.rev_injective h).symm
    simp only [eq_self_iff_true, if_true, if_neg hbc, if_neg (Ne.symm hbc), if_neg hbc', LinearMap.zero_apply, Edd_ofD,
      sub_zero, zero_sub]
    simp only [sub_zero, zero_sub, LinearMap.zero_apply, ← ofD_neg, ← ofD_sub]
    congr 1
    unfold sg
    split_ifs <;> module
  · have hda' : ¬ Fin.rev a = Fin.rev d := fun h => hda (Fin.rev_injective h).symm
    have hbc' : ¬ Fin.rev c = Fin.rev b := fun h => hbc (Fin.rev_injective h).symm
    simp only [if_neg hbc, if_neg (Ne.symm hbc), if_neg hda, if_neg (Ne.symm hda), if_neg hda', if_neg hbc', LinearMap.zero_apply,
      sub_zero, smul_zero]
    simp [ofD_zero]

end Conj

end ReciprocityTheory.ChartRestriction.DS.Lap.LemK.DualRepresentationReversal

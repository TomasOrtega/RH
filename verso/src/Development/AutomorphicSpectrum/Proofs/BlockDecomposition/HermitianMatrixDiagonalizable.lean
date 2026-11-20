import Mathlib
import Development.WeilBound.CoreStatements.AutomorphicKernels.UnitarySchrodingerModel.LocalDefs
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ResAlgSplitTwo
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FixedNondeg
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnramifiedQuotientCardStatement
open PositivityTheory.PfSWUS.Loc GlobalTheory.CompanionTheory.UnrDens GlobalTheory.CompanionTheory.SiegLoc Filter Topology

noncomputable section

namespace GlobalTheory.CompanionTheory.HermDiag

variable {R : Type} [CommRing R]

def ct (σ : R →+* R) {a b : Type} (x : Matrix a b R) : Matrix b a R := (x.map σ).transpose

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem ct_apply (σ : R →+* R) {a b : Type} (x : Matrix a b R) (i : b) (j : a) :
    ct σ x i j = σ (x j i) := rfl

/- English proof (translation)
Unfold `ct`. Rewrite using `[Matrix.map_mul, Matrix.transpose_mul]`.
-/
theorem ct_mul (σ : R →+* R) {a b c : Type} [Fintype b] (x : Matrix a b R) (y : Matrix b c R) :
    ct σ (x * y) = ct σ y * ct σ x := by
  unfold ct
  rw [Matrix.map_mul, Matrix.transpose_mul]

def Hm (σ : R →+* R) {ι : Type} (h : Matrix ι ι R) : Prop := ∀ i j, σ (h i j) = h j i

def Diagble (σ : R →+* R) {ι : Type} [Fintype ι] [DecidableEq ι] (h : Matrix ι ι R) : Prop :=
  ∃ (g g' : Matrix ι ι R) (d : ι → R), g * g' = 1 ∧ g' * g = 1 ∧ (∀ i, σ (d i) = d i) ∧
    ct σ g * h * g = Matrix.diagonal d

section basic
variable {σ : R →+* R} {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

/- English proof (translation)
Establish `hc : ct σ (ct σ p * h * p) = ct σ p * h * p`. Establish `h1 : ct σ h = h` using `by ext i j; exact hh j i`. Establish `h2 : ct σ (ct σ p) = p` using `by ext i j; exact hinv _`. Rewrite using `[ct_mul, ct_mul, h1, h2, Matrix.mul_assoc]`. Introduce `i j`.

Conclude with `congrFun (congrFun hc j) i`.
-/
theorem hm_congr (hinv : ∀ a, σ (σ a) = a) {h : Matrix ι ι R} (hh : Hm σ h) (p : Matrix ι ι R) :
    Hm σ (ct σ p * h * p) := by
  have hc : ct σ (ct σ p * h * p) = ct σ p * h * p := by
    have h1 : ct σ h = h := by ext i j; exact hh j i
    have h2 : ct σ (ct σ p) = p := by ext i j; exact hinv _
    rw [ct_mul, ct_mul, h1, h2, Matrix.mul_assoc]
  intro i j
  exact congrFun (congrFun hc j) i

/- English proof (translation)
Assemble the required witnesses or components as `⟨1, 1, 0, by simp, by simp, by simp, by simp⟩`.
-/
theorem diagble_zero : Diagble σ (0 : Matrix ι ι R) :=
  ⟨1, 1, 0, by simp, by simp, by simp, by simp⟩

/- English proof (translation)
Take `⟨g, g', d, hg, hg', hfix, hdiag⟩` from `hd`. Use `⟨p * g, g' * p', d, ?_, ?_, hfix, ?_⟩` and prove the remaining obligations. Combine the equalities or inequalities in the displayed calculation. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[ct_mul, ← hdiag]`.

Simplify using `only [Matrix.mul_assoc]`.
-/
theorem diagble_of_congr {h p p' : Matrix ι ι R} (h1 : p * p' = 1) (h2 : p' * p = 1)
    (hd : Diagble σ (ct σ p * h * p)) : Diagble σ h := by
  obtain ⟨g, g', d, hg, hg', hfix, hdiag⟩ := hd
  refine ⟨p * g, g' * p', d, ?_, ?_, hfix, ?_⟩
  · calc p * g * (g' * p') = p * (g * g') * p' := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hg, Matrix.mul_one, h1]
  · calc g' * p' * (p * g) = g' * (p' * p) * g := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [h2, Matrix.mul_one, hg']
  · rw [ct_mul, ← hdiag]
    simp only [Matrix.mul_assoc]

/- English proof (translation)
Take `⟨g, g', d, hg, hg', hfix, hdiag⟩` from `hd`. Use `⟨g, g', fun i => c * d i, hg, hg', fun i => by simp [hc, hfix], ?_⟩` and prove the remaining obligations. Establish `: Matrix.diagonal (fun i => c * d i) = c • Matrix.diagonal d`. Use extensionality with `i j`. Apply the tactic sequence `by_cases hij : i = j <;> simp [Matrix.diagonal_apply, hij]`.

Rewrite using `[this, ← hdiag]`. Simplify using `[Matrix.mul_smul, Matrix.smul_mul]`.
-/
theorem diagble_smul {h : Matrix ι ι R} {c : R} (hc : σ c = c) (hd : Diagble σ h) :
    Diagble σ (c • h) := by
  obtain ⟨g, g', d, hg, hg', hfix, hdiag⟩ := hd
  refine ⟨g, g', fun i => c * d i, hg, hg', fun i => by simp [hc, hfix], ?_⟩
  have : Matrix.diagonal (fun i => c * d i) = c • Matrix.diagonal d := by
    ext i j
    by_cases hij : i = j <;> simp [Matrix.diagonal_apply, hij]
  rw [this, ← hdiag]
  simp [Matrix.mul_smul, Matrix.smul_mul]

/- English proof (translation)
Take `⟨g, g', d, hg, hg', hfix, hdiag⟩` from `hd`. Use `⟨g.submatrix e.symm e.symm, g'.submatrix e.symm e.symm, fun i => d (e.symm i), ?_, ?_, fun i => hfix _, ?_⟩` and prove the remaining obligations. Rewrite using `[Matrix.submatrix_mul_equiv, hg]`. Simplify using the standard rewrite rules. Rewrite using `[Matrix.submatrix_mul_equiv, hg']`.

Simplify using the standard rewrite rules. Establish `hct : ct σ (g.submatrix e.symm e.symm) = (ct σ g).submatrix e.symm e.symm` using `rfl`. Establish `hh : h = (h.submatrix e e).submatrix e.symm e.symm` using `by ext i j; simp`. Rewrite using `[hct, hh, Matrix.submatrix_mul_equiv, Matrix.submatrix_mul_equiv, hdiag]`. Use extensionality with `i j`.

Simplify using `[Matrix.diagonal_apply]`.
-/
theorem diagble_reindex (e : κ ≃ ι) {h : Matrix ι ι R} (hd : Diagble σ (h.submatrix e e)) :
    Diagble σ h := by
  obtain ⟨g, g', d, hg, hg', hfix, hdiag⟩ := hd
  refine ⟨g.submatrix e.symm e.symm, g'.submatrix e.symm e.symm, fun i => d (e.symm i),
    ?_, ?_, fun i => hfix _, ?_⟩
  · rw [Matrix.submatrix_mul_equiv, hg]; simp
  · rw [Matrix.submatrix_mul_equiv, hg']; simp
  · have hct : ct σ (g.submatrix e.symm e.symm) = (ct σ g).submatrix e.symm e.symm := rfl
    have hh : h = (h.submatrix e e).submatrix e.symm e.symm := by ext i j; simp
    rw [hct, hh, Matrix.submatrix_mul_equiv, Matrix.submatrix_mul_equiv, hdiag]
    ext i j
    simp [Matrix.diagonal_apply]

/- English proof (translation)
Take `⟨g, g', d, hg, hg', hfix, hdiag⟩` from `hd`. Use `⟨Matrix.fromBlocks 1 0 0 g, Matrix.fromBlocks 1 0 0 g', Sum.elim (fun _ => a) d, ?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[Matrix.fromBlocks_multiply]`. Simplify using `[hg]`. Rewrite using `[Matrix.fromBlocks_multiply]`.

Simplify using `[hg']`. Introduce and unpack `(i | i)`. Simplify using `using ha`. Simplify using `using hfix i`. Establish `hct : ct σ (Matrix.fromBlocks (1 : Matrix Unit Unit R) 0 0 g) = Matrix.fromBlocks 1 0 0 (ct σ g)`.

Apply the tactic sequence `ext (i | i) (j | j) <;> simp [ct_apply, Matrix.one_apply]`. Rewrite using `[hct, Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply, ← Matrix.fromBlocks_diagonal]`. Simplify using `[hdiag]`.
-/
theorem diagble_block {a : R} (ha : σ a = a) {D : Matrix ι ι R} (hd : Diagble σ D) :
    Diagble σ (Matrix.fromBlocks (Matrix.diagonal fun _ : Unit => a) 0 0 D) := by
  obtain ⟨g, g', d, hg, hg', hfix, hdiag⟩ := hd
  refine ⟨Matrix.fromBlocks 1 0 0 g, Matrix.fromBlocks 1 0 0 g', Sum.elim (fun _ => a) d,
    ?_, ?_, ?_, ?_⟩
  · rw [Matrix.fromBlocks_multiply]; simp [hg]
  · rw [Matrix.fromBlocks_multiply]; simp [hg']
  · rintro (i | i)
    · simpa using ha
    · simpa using hfix i
  · have hct : ct σ (Matrix.fromBlocks (1 : Matrix Unit Unit R) 0 0 g) =
        Matrix.fromBlocks 1 0 0 (ct σ g) := by
      ext (i | i) (j | j) <;> simp [ct_apply, Matrix.one_apply]
    rw [hct, Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply, ← Matrix.fromBlocks_diagonal]
    simp [hdiag]

/- English proof (translation)
Take `⟨v, hv⟩` from `hu.exists_right_inv`. Use `set a := h (Sum.inl ()) (Sum.inl ()) with ha`. Establish `hfa : σ a = a` using `hh _ _`. Establish `hfv : σ v = v`. Establish `h1 : a * σ v = 1`.

Use `congrArg σ hv` as an intermediate fact. Rewrite `this` using `[map_mul, map_one, hfa]`. Then use the resulting hypothesis. Combine the equalities or inequalities in the displayed calculation. Set `B : Matrix Unit ι R` to `h.toBlocks₁₂`. Set `C : Matrix ι Unit R` to `h.toBlocks₂₁`.

Set `D : Matrix ι ι R` to `h.toBlocks₂₂`. Establish `hA : h.toBlocks₁₁ = Matrix.diagonal fun _ : Unit => a`. Use extensionality with `i j`. Consider the cases of `i`. Consider the cases of `j`.

Simplify using `[Matrix.toBlocks₁₁, ha]`. Establish `hblocks : h = Matrix.fromBlocks (Matrix.diagonal fun _ : Unit => a) B C D`. Rewrite using `[← hA]`. Conclude with `(Matrix.fromBlocks_toBlocks h).symm`. Establish `hCB : ∀ i, σ (B () i) = C i ()` using `fun i => hh _ _`.

Establish `hCB' : ∀ i, σ (C i ()) = B () i` using `fun i => hh _ _`. Establish `hD : ∀ i j, σ (D i j) = D j i` using `fun i j => hh _ _`. Set `p : Matrix (Unit ⊕ ι) (Unit ⊕ ι) R` to `Matrix.fromBlocks 1 (-(v • B)) 0 1`. Set `p' : Matrix (Unit ⊕ ι) (Unit ⊕ ι) R` to `Matrix.fromBlocks 1 (v • B) 0 1`. Establish `hpp : p * p' = 1`.

Simplify using `only [p, p']`. Rewrite using `[Matrix.fromBlocks_multiply]`. Simplify using the standard rewrite rules. Establish `hpp' : p' * p = 1`. Simplify using `only [p, p']`.

Rewrite using `[Matrix.fromBlocks_multiply]`. Simplify using the standard rewrite rules. Set `E : Matrix ι ι R` to `D - v • (C * B)`. Establish `hE : Hm σ E`. Introduce `i j`.

Simplify using `only [E, Matrix.sub_apply, Matrix.smul_apply, Matrix.mul_apply, Finset.univ_unique, Finset.sum_singleton, smul_eq_mul, map_sub, map_mul, hfv, hD, hCB, hCB']`. Simplify using `only [PUnit.default_eq_unit]`. Expand and normalize the polynomial expressions, which then agree. Establish `hct : ct σ p = Matrix.fromBlocks 1 0 (-(v • C)) 1`. Use extensionality with `(i | i) (j | j)`.

Simplify using `[p, ct_apply, Matrix.one_apply]`. Simplify using `[p, ct_apply]`. Consider the cases of `j`. Simplify using `[p, ct_apply, hfv, hCB]`. Distinguish the cases in `hij : i = j`.

Substitute `hij` using the available equality. Simplify using `[p, ct_apply]`. Simplify using `[p, ct_apply, Matrix.one_apply, hij, Ne.symm hij]`. Establish `hcongr : ct σ p * h * p = Matrix.fromBlocks (Matrix.diagonal fun _ : Unit => a) 0 0 E`. Establish `hav : ∀ {c : Type} (X : Matrix Unit c R), (Matrix.diagonal fun _ : Unit => a) * (v • X) = X`.

Introduce `c X`. Use extensionality with `i j`. Consider the cases of `i`. Rewrite using `[Matrix.diagonal_mul]`. Simplify using `only [Matrix.smul_apply, smul_eq_mul]`.

Take the linear combination `(X () j) * hv`. Establish `hva : ∀ {c : Type} (X : Matrix c Unit R), (v • X) * (Matrix.diagonal fun _ : Unit => a) = X`. Introduce `c X`. Use extensionality with `i j`. Consider the cases of `j`.

Rewrite using `[Matrix.mul_diagonal]`. Simplify using `only [Matrix.smul_apply, smul_eq_mul]`. Take the linear combination `(X i ()) * hv`. Rewrite using `[hct, hblocks]`. Simplify using `only [p]`.

Rewrite using `[Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply]`. Simplify using `[hva, hav, E, Matrix.mul_neg, Matrix.neg_mul, Matrix.mul_smul, Matrix.smul_mul, sub_eq_add_neg, add_comm]`. Apply `diagble_of_congr hpp hpp'` to reduce the goal to its premises. Rewrite using `[hcongr]`. Conclude with `diagble_block hfa (ih E hE)`.
-/
theorem diagble_schur (hinv : ∀ a, σ (σ a) = a) (ih : ∀ h : Matrix ι ι R, Hm σ h → Diagble σ h)
    {h : Matrix (Unit ⊕ ι) (Unit ⊕ ι) R} (hh : Hm σ h)
    (hu : IsUnit (h (Sum.inl ()) (Sum.inl ()))) : Diagble σ h := by
  obtain ⟨v, hv⟩ := hu.exists_right_inv
  set a := h (Sum.inl ()) (Sum.inl ()) with ha
  have hfa : σ a = a := hh _ _
  have hfv : σ v = v := by
    have h1 : a * σ v = 1 := by
      have := congrArg σ hv
      rwa [map_mul, map_one, hfa] at this
    calc σ v = (a * v) * σ v := by rw [hv, one_mul]
      _ = (a * σ v) * v := by ring
      _ = v := by rw [h1, one_mul]
  let B : Matrix Unit ι R := h.toBlocks₁₂
  let C : Matrix ι Unit R := h.toBlocks₂₁
  let D : Matrix ι ι R := h.toBlocks₂₂
  have hA : h.toBlocks₁₁ = Matrix.diagonal fun _ : Unit => a := by
    ext i j
    cases i; cases j
    simp [Matrix.toBlocks₁₁, ha]
  have hblocks : h = Matrix.fromBlocks (Matrix.diagonal fun _ : Unit => a) B C D := by
    rw [← hA]; exact (Matrix.fromBlocks_toBlocks h).symm
  have hCB : ∀ i, σ (B () i) = C i () := fun i => hh _ _
  have hCB' : ∀ i, σ (C i ()) = B () i := fun i => hh _ _
  have hD : ∀ i j, σ (D i j) = D j i := fun i j => hh _ _
  let p : Matrix (Unit ⊕ ι) (Unit ⊕ ι) R := Matrix.fromBlocks 1 (-(v • B)) 0 1
  let p' : Matrix (Unit ⊕ ι) (Unit ⊕ ι) R := Matrix.fromBlocks 1 (v • B) 0 1
  have hpp : p * p' = 1 := by
    simp only [p, p']
    rw [Matrix.fromBlocks_multiply]; simp
  have hpp' : p' * p = 1 := by
    simp only [p, p']
    rw [Matrix.fromBlocks_multiply]; simp
  let E : Matrix ι ι R := D - v • (C * B)
  have hE : Hm σ E := by
    intro i j
    simp only [E, Matrix.sub_apply, Matrix.smul_apply, Matrix.mul_apply, Finset.univ_unique,
      Finset.sum_singleton, smul_eq_mul, map_sub, map_mul, hfv, hD, hCB, hCB']
    simp only [PUnit.default_eq_unit]
    ring
  have hct : ct σ p = Matrix.fromBlocks 1 0 (-(v • C)) 1 := by
    ext (i | i) (j | j)
    · simp [p, ct_apply, Matrix.one_apply]
    · simp [p, ct_apply]
    · cases j; simp [p, ct_apply, hfv, hCB]
    · by_cases hij : i = j
      · subst hij; simp [p, ct_apply]
      · simp [p, ct_apply, Matrix.one_apply, hij, Ne.symm hij]
  have hcongr : ct σ p * h * p = Matrix.fromBlocks (Matrix.diagonal fun _ : Unit => a) 0 0 E := by
    have hav : ∀ {c : Type} (X : Matrix Unit c R), (Matrix.diagonal fun _ : Unit => a) * (v • X) = X := by
      intro c X
      ext i j
      cases i
      rw [Matrix.diagonal_mul]
      simp only [Matrix.smul_apply, smul_eq_mul]
      linear_combination (X () j) * hv
    have hva : ∀ {c : Type} (X : Matrix c Unit R), (v • X) * (Matrix.diagonal fun _ : Unit => a) = X := by
      intro c X
      ext i j
      cases j
      rw [Matrix.mul_diagonal]
      simp only [Matrix.smul_apply, smul_eq_mul]
      linear_combination (X i ()) * hv
    rw [hct, hblocks]
    simp only [p]
    rw [Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply]
    simp [hva, hav, E, Matrix.mul_neg, Matrix.neg_mul, Matrix.mul_smul, Matrix.smul_mul, sub_eq_add_neg, add_comm]
  apply diagble_of_congr hpp hpp'
  rw [hcongr]
  exact diagble_block hfa (ih E hE)

end basic

section local_ring
variable {σ : R →+* R} {ϖ : R} {q : ℕ} {ε : ℤ}

/- English proof (translation)
Assume the negation of the conclusion as `hcon`. Use `push_neg at hcon`. Take `⟨u, hu, -⟩` from `hR.basis`. Apply `hy` to reduce the goal to its premises. Establish `h3 : (u - σ u) * y ∈ lev ϖ 1`.

Establish `: (u - σ u) * y = (u * y + σ (u * y)) - σ u * (1 * y + σ (1 * y))`. Simplify using `only [map_mul, map_one]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[this]`. Conclude with `Ideal.sub_mem _ (hcon u) (Ideal.mul_mem_left _ _ (hcon 1))`.

Take `⟨v, hv⟩` from `hu.exists_left_inv`. Establish `: y = v * ((u - σ u) * y)` using `by rw [← mul_assoc, hv, one_mul]`. Rewrite using `[this]`. Conclude with `Ideal.mul_mem_left _ _ h3`.
-/
theorem exists_trace (hR : IsUnrQuad R σ ϖ q ε) {y : R} (hy : y ∉ lev ϖ 1) :
    ∃ s, s * y + σ (s * y) ∉ lev ϖ 1 := by
  by_contra hcon
  push_neg at hcon
  obtain ⟨u, hu, -⟩ := hR.basis
  apply hy
  have h3 : (u - σ u) * y ∈ lev ϖ 1 := by
    have : (u - σ u) * y = (u * y + σ (u * y)) - σ u * (1 * y + σ (1 * y)) := by
      simp only [map_mul, map_one]; ring
    rw [this]
    exact Ideal.sub_mem _ (hcon u) (Ideal.mul_mem_left _ _ (hcon 1))
  obtain ⟨v, hv⟩ := hu.exists_left_inv
  have : y = v * ((u - σ u) * y) := by rw [← mul_assoc, hv, one_mul]
  rw [this]
  exact Ideal.mul_mem_left _ _ h3

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/- English proof (translation)
Unfold `ct`. Rewrite using `[Matrix.map_one σ (map_zero σ) (map_one σ), Matrix.transpose_one]`.
-/
theorem ct_one : ct σ (1 : Matrix ι ι R) = 1 := by
  unfold ct
  rw [Matrix.map_one σ (map_zero σ) (map_one σ), Matrix.transpose_one]

/- English proof (translation)
Unfold `ct Matrix.transvection`. Use extensionality with `a b`. Simplify using `only [Matrix.transpose_apply, Matrix.map_apply, Matrix.add_apply, map_add, Matrix.one_apply, Matrix.single_apply]`. Distinguish the cases in `hab : a = b`. Substitute `hab` using the available equality.

Distinguish the cases in `h1 : j = a ∧ i = a`. Take `⟨rfl, rfl⟩` from `h1`. Simplify using the standard rewrite rules. Establish `h2 : ¬ (i = a ∧ j = a)` using `fun h => h1 ⟨h.2, h.1⟩`. Simplify using `[h1, h2]`.

Establish `hba : ¬ b = a` using `fun h => hab h.symm`. Distinguish the cases in `h1 : j = b ∧ i = a`. Establish `h2 : i = a ∧ j = b` using `⟨h1.2, h1.1⟩`. Simplify using `[hab, hba, h1, h2]`. Establish `h2 : ¬ (i = a ∧ j = b)` using `fun h => h1 ⟨h.2, h.1⟩`.

Simplify using `[hab, hba, h1, h2]`.
-/
theorem ct_transvection (i j : ι) (s : R) :
    ct σ (Matrix.transvection j i s) = Matrix.transvection i j (σ s) := by
  unfold ct Matrix.transvection
  ext a b
  simp only [Matrix.transpose_apply, Matrix.map_apply, Matrix.add_apply, map_add,
    Matrix.one_apply, Matrix.single_apply]
  by_cases hab : a = b
  · subst hab
    by_cases h1 : j = a ∧ i = a
    · obtain ⟨rfl, rfl⟩ := h1; simp
    · have h2 : ¬ (i = a ∧ j = a) := fun h => h1 ⟨h.2, h.1⟩
      simp [h1, h2]
  · have hba : ¬ b = a := fun h => hab h.symm
    by_cases h1 : j = b ∧ i = a
    · have h2 : i = a ∧ j = b := ⟨h1.2, h1.1⟩
      simp [hab, hba, h1, h2]
    · have h2 : ¬ (i = a ∧ j = b) := fun h => h1 ⟨h.2, h.1⟩
      simp [hab, hba, h1, h2]

/- English proof (translation)
Take `⟨s, hs⟩` from `exists_trace hR hy`. Use `⟨Matrix.transvection j i s, Matrix.transvection j i (-s), ?_, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[Matrix.transvection_mul_transvection_same _ _ hij.symm]`. Simplify using the standard rewrite rules. Rewrite using `[Matrix.transvection_mul_transvection_same _ _ hij.symm]`.

Simplify using the standard rewrite rules. Rewrite using `[ct_transvection, Matrix.mul_transvection_apply_same, Matrix.transvection_mul_apply_same, Matrix.transvection_mul_apply_same]`. Introduce `hmem`. Apply `hs` to reduce the goal to its premises. Establish `: s * h i j + σ (s * h i j) = (h i i + σ s * h j i + s * (h i j + σ s * h j j)) - h i i - s * σ s * h j j`.

Rewrite using `[map_mul, hh i j]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[this]`. Conclude with `Ideal.sub_mem _ (Ideal.sub_mem _ hmem hi) (Ideal.mul_mem_left _ _ hj)`.
-/
theorem pivot_offdiag (hR : IsUnrQuad R σ ϖ q ε) {h : Matrix ι ι R} (hh : Hm σ h) {i j : ι}
    (hij : i ≠ j) (hi : h i i ∈ lev ϖ 1) (hj : h j j ∈ lev ϖ 1) (hy : h i j ∉ lev ϖ 1) :
    ∃ p p' : Matrix ι ι R, p * p' = 1 ∧ p' * p = 1 ∧ (ct σ p * h * p) i i ∉ lev ϖ 1 := by
  obtain ⟨s, hs⟩ := exists_trace hR hy
  refine ⟨Matrix.transvection j i s, Matrix.transvection j i (-s), ?_, ?_, ?_⟩
  · rw [Matrix.transvection_mul_transvection_same _ _ hij.symm]; simp
  · rw [Matrix.transvection_mul_transvection_same _ _ hij.symm]; simp
  · rw [ct_transvection, Matrix.mul_transvection_apply_same, Matrix.transvection_mul_apply_same,
      Matrix.transvection_mul_apply_same]
    intro hmem
    apply hs
    have : s * h i j + σ (s * h i j) =
        (h i i + σ s * h j i + s * (h i j + σ s * h j j)) - h i i - s * σ s * h j j := by
      rw [map_mul, hh i j]; ring
    rw [this]
    exact Ideal.sub_mem _ (Ideal.sub_mem _ hmem hi) (Ideal.mul_mem_left _ _ hj)

/- English proof (translation)
Distinguish the cases in `h1 : ∃ k, h k k ∉ lev ϖ 1`. Take `⟨k, hk⟩` from `h1`. Conclude with `⟨k, 1, 1, by simp, by simp, by simpa [ct_one] using hk⟩`. Use `push_neg at h1`. Establish `hij : i ≠ j`.

Introduce and unpack `rfl`. Conclude with `hy (h1 i)`. Take `⟨p, p', a, b, c⟩` from `pivot_offdiag hR hh hij (h1 i) (h1 j) hy`. Conclude with `⟨i, p, p', a, b, c⟩`.
-/
theorem exists_pivot (hR : IsUnrQuad R σ ϖ q ε) {h : Matrix ι ι R} (hh : Hm σ h) {i j : ι}
    (hy : h i j ∉ lev ϖ 1) :
    ∃ (k : ι) (p p' : Matrix ι ι R), p * p' = 1 ∧ p' * p = 1 ∧
      (ct σ p * h * p) k k ∉ lev ϖ 1 := by
  by_cases h1 : ∃ k, h k k ∉ lev ϖ 1
  · obtain ⟨k, hk⟩ := h1
    exact ⟨k, 1, 1, by simp, by simp, by simpa [ct_one] using hk⟩
  · push_neg at h1
    have hij : i ≠ j := by
      rintro rfl
      exact hy (h1 i)
    obtain ⟨p, p', a, b, c⟩ := pivot_offdiag hR hh hij (h1 i) (h1 j) hy
    exact ⟨i, p, p', a, b, c⟩

/- English proof (translation)
Establish `hex : ∃ k, ∃ i j, h i j ∉ lev ϖ k`. Assume the negation of the conclusion as `hcon`. Use `push_neg at hcon`. Apply `h0` to reduce the goal to its premises. Use extensionality with `i j`.

Conclude with `hR.sep _ (fun k => hcon k i j)`. Establish `hk0 : Nat.find hex ≠ 0`. Introduce `h00`. Take `⟨i, j, hij⟩` from `Nat.find_spec hex`. Rewrite `hij` using `[h00]`.

Conclude with `hij (by simp [lev])`. Take `⟨a, ha⟩` from `Nat.exists_eq_succ_of_ne_zero hk0`. Take `⟨i, j, hij⟩` from `Nat.find_spec hex`. Rewrite `hij` using `[ha]`. Establish `hall : ∀ i j, h i j ∈ lev ϖ a`.

Use `Nat.find_min hex (m := a) (by omega)` as an intermediate fact. Use `push_neg at this`. Conclude with `this`. Use `choose c hc using fun i j => mem_lev_iff.1 (hall i j)`. Use `⟨a, Matrix.of c, ?_, ?_, i, j, ?_⟩` and prove the remaining obligations.

Introduce `x y`. Apply `hR.reg.pow a` to reduce the goal to its premises. Use `hh x y` as an intermediate fact. Rewrite `this` using `[hc x y, hc y x, map_mul, map_pow, hR.fix_ϖ]`. Simplify using `using this`.

Use extensionality with `x y`. Conclude with `hc x y`. Introduce `hm`. Take `⟨d, hd⟩` from `mem_lev_iff.1 hm`. Apply `hij` to reduce the goal to its premises.

Use `mem_lev_iff.2 ⟨d, ?_⟩` and prove the remaining obligations. Establish `hd' : c i j = ϖ ^ 1 * d` using `hd`. Rewrite using `[hc i j, hd', Nat.succ_eq_add_one]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem exists_prim (hR : IsUnrQuad R σ ϖ q ε) {h : Matrix ι ι R} (hh : Hm σ h) (h0 : h ≠ 0) :
    ∃ (a : ℕ) (h' : Matrix ι ι R), Hm σ h' ∧ h = (ϖ ^ a) • h' ∧ ∃ i j, h' i j ∉ lev ϖ 1 := by
  classical
  have hex : ∃ k, ∃ i j, h i j ∉ lev ϖ k := by
    by_contra hcon
    push_neg at hcon
    apply h0
    ext i j
    exact hR.sep _ (fun k => hcon k i j)
  have hk0 : Nat.find hex ≠ 0 := by
    intro h00
    obtain ⟨i, j, hij⟩ := Nat.find_spec hex
    rw [h00] at hij
    exact hij (by simp [lev])
  obtain ⟨a, ha⟩ := Nat.exists_eq_succ_of_ne_zero hk0
  obtain ⟨i, j, hij⟩ := Nat.find_spec hex
  rw [ha] at hij
  have hall : ∀ i j, h i j ∈ lev ϖ a := by
    have := Nat.find_min hex (m := a) (by omega)
    push_neg at this
    exact this
  choose c hc using fun i j => mem_lev_iff.1 (hall i j)
  refine ⟨a, Matrix.of c, ?_, ?_, i, j, ?_⟩
  · intro x y
    apply hR.reg.pow a
    have := hh x y
    rw [hc x y, hc y x, map_mul, map_pow, hR.fix_ϖ] at this
    simpa using this
  · ext x y
    exact hc x y
  · intro hm
    obtain ⟨d, hd⟩ := mem_lev_iff.1 hm
    apply hij
    refine mem_lev_iff.2 ⟨d, ?_⟩
    have hd' : c i j = ϖ ^ 1 * d := hd
    rw [hc i j, hd', Nat.succ_eq_add_one]
    ring

/- English proof (translation)
Take `⟨k, p, p', h1, h2, hp⟩` from `exists_pivot hR hh hy`. Apply `diagble_of_congr h1 h2` to reduce the goal to its premises. Establish `hh2` using `hm_congr hR.inv hh p`. Establish `hcard : Fintype.card (Unit ⊕ Fin n) = n + 1` using `by simp; omega`. Set `e0` to `Fintype.equivFinOfCardEq hcard`.

Set `e` to `e0.trans (Equiv.swap (e0 (Sum.inl ())) k)`. Establish `he : e (Sum.inl ()) = k` using `by simp [e]`. Apply `diagble_reindex e` to reduce the goal to its premises. Use `diagble_schur hR.inv ih (fun a b => hh2 _ _) ?_` and prove the remaining obligations. Simplify using `only [Matrix.submatrix_apply, he]`.

Conclude with `hR.fixLocal _ (hh2 _ _) hp`.
-/
theorem diagble_prim (hR : IsUnrQuad R σ ϖ q ε) {n : ℕ}
    (ih : ∀ h : Matrix (Fin n) (Fin n) R, Hm σ h → Diagble σ h)
    {h : Matrix (Fin (n + 1)) (Fin (n + 1)) R} (hh : Hm σ h) {i j : Fin (n + 1)}
    (hy : h i j ∉ lev ϖ 1) : Diagble σ h := by
  obtain ⟨k, p, p', h1, h2, hp⟩ := exists_pivot hR hh hy
  apply diagble_of_congr h1 h2
  have hh2 := hm_congr hR.inv hh p
  have hcard : Fintype.card (Unit ⊕ Fin n) = n + 1 := by simp; omega
  let e0 := Fintype.equivFinOfCardEq hcard
  let e := e0.trans (Equiv.swap (e0 (Sum.inl ())) k)
  have he : e (Sum.inl ()) = k := by simp [e]
  apply diagble_reindex e
  refine diagble_schur hR.inv ih (fun a b => hh2 _ _) ?_
  simp only [Matrix.submatrix_apply, he]
  exact hR.fixLocal _ (hh2 _ _) hp

/- English proof (translation)
Introduce `n`. Proceed by induction on `n with`. Consider the case `zero`. Introduce `h _`. Rewrite using `[Subsingleton.elim h 0]`.

Conclude with `diagble_zero`. Consider the case `succ n ih`. Introduce `h hh`. Distinguish the cases in `h0 : h = 0`. Rewrite using `[h0]`.

Conclude with `diagble_zero`. Take `⟨a, h', hh', rfl, i, j, hy⟩` from `exists_prim hR hh h0`. Conclude with `diagble_smul (by simp [hR.fix_ϖ]) (diagble_prim hR ih hh' hy)`.
-/
theorem diagble_fin (hR : IsUnrQuad R σ ϖ q ε) :
    ∀ (n : ℕ) (h : Matrix (Fin n) (Fin n) R), Hm σ h → Diagble σ h := by
  intro n
  induction n with
  | zero =>
    intro h _
    rw [Subsingleton.elim h 0]
    exact diagble_zero
  | succ n ih =>
    intro h hh
    by_cases h0 : h = 0
    · rw [h0]; exact diagble_zero
    · obtain ⟨a, h', hh', rfl, i, j, hy⟩ := exists_prim hR hh h0
      exact diagble_smul (by simp [hR.fix_ϖ]) (diagble_prim hR ih hh' hy)

end local_ring

/- English proof (translation)
Introduce `R _ σ ϖ q ε hR n h hh`. Take `⟨g, g', d, h1, h2, h3, h4⟩` from `diagble_fin hR n h (fun i j => congrFun (congrFun hh j) i)`. Conclude with `⟨g, g', d, h1, h2, h3, h4⟩`.
-/
theorem herm_diag : ∀ (R : Type) [CommRing R] (σ : R →+* R) (ϖ : R) (q : ℕ) (ε : ℤ),
    IsUnrQuad R σ ϖ q ε → ∀ (n : ℕ) (h : Matrix (Fin n) (Fin n) R), cT σ h = h →
    ∃ (g g' : Matrix (Fin n) (Fin n) R) (d : Fin n → R), g * g' = 1 ∧ g' * g = 1 ∧
      (∀ i, σ (d i) = d i) ∧ cT σ g * h * g = Matrix.diagonal d := by
  intro R _ σ ϖ q ε hR n h hh
  obtain ⟨g, g', d, h1, h2, h3, h4⟩ :=
    diagble_fin hR n h (fun i j => congrFun (congrFun hh j) i)
  exact ⟨g, g', d, h1, h2, h3, h4⟩

end GlobalTheory.CompanionTheory.HermDiag
end

import ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.HaarVolumes.OmegaPQA
import Formalism.LocalRingCardinality.DataCD

noncomputable section

open Finset Matrix MeasureTheory

namespace ReciprocityTheory.ChartRestriction.DS.OmegaPQAux

open ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.S7

variable {n P Q : ℕ}

def sg (ε : Fin n → Bool) (a : Fin n) : ℂ := if ε a then 1 else -1

/- English proof (translation)
Use extensionality with `(i | i) (j | j)`. Apply the tactic sequence `by_cases h : i = j <;> simp [Formalism.UG.Jpq, Matrix.one_apply, Matrix.diagonal_apply, h]`. Simplify using `[Formalism.UG.Jpq, Matrix.diagonal_apply]`. Simplify using `[Formalism.UG.Jpq, Matrix.diagonal_apply]`. Apply the tactic sequence `by_cases h : i = j <;> simp [Formalism.UG.Jpq, Matrix.one_apply, Matrix.diagonal_apply, h]`.
-/
theorem Jpq_eq : Formalism.UG.Jpq P Q = Matrix.diagonal (Sum.elim (fun _ => (1 : ℂ)) (fun _ => -1)) := by
  ext (i | i) (j | j)
  · by_cases h : i = j <;> simp [Formalism.UG.Jpq, Matrix.one_apply, Matrix.diagonal_apply, h]
  · simp [Formalism.UG.Jpq, Matrix.diagonal_apply]
  · simp [Formalism.UG.Jpq, Matrix.diagonal_apply]
  · by_cases h : i = j <;> simp [Formalism.UG.Jpq, Matrix.one_apply, Matrix.diagonal_apply, h]

/- English proof (translation)
Use `show Xᴴ * Formalism.UG.Jpq P Q + Formalism.UG.Jpq P Q * X = 0 ↔ _`. Rewrite using `[Jpq_eq]`. Prove the components needed by the constructor for the conclusion. Introduce `h i j`. Establish `hij` using `congrFun (congrFun h i) j`.

Simplify `hij` using `[Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.conjTranspose_apply]`. Introduce `h`. Use extensionality with `i j`. Simplify `h i j` using `[Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.conjTranspose_apply]`.
-/
theorem mem_lieU_iff (X : Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ) :
    X ∈ Formalism.BasicNotions.lieU P Q ↔ ∀ i j, star (X j i) * Sum.elim (fun _ => (1 : ℂ)) (fun _ => -1) j +
      Sum.elim (fun _ => (1 : ℂ)) (fun _ => -1) i * X i j = 0 := by
  show Xᴴ * Formalism.UG.Jpq P Q + Formalism.UG.Jpq P Q * X = 0 ↔ _
  rw [Jpq_eq]
  constructor
  · intro h i j
    have hij := congrFun (congrFun h i) j
    simpa [Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.conjTranspose_apply] using hij
  · intro h
    ext i j
    simpa [Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.conjTranspose_apply] using h i j

/- English proof (translation)
Rewrite using `[mem_lieU_iff]`. Establish `hs : ∀ i, Sum.elim (fun _ => (1 : ℂ)) (fun _ => -1) i = sg ε (e i)`. Apply the tactic sequence `rintro (i | i) <;> simp [sg, he1, he2]`. Simplify using `only [Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.symm_symm, hs]`. Prove the components needed by the constructor for the conclusion.

Introduce `h a b`. Simplify using `using h (e.symm a) (e.symm b)`. Introduce `h i j`. Conclude with `h (e i) (e j)`.
-/
theorem mem_reindex_iff (e : Fin P ⊕ Fin Q ≃ Fin n) {ε : Fin n → Bool}
    (he1 : ∀ i, ε (e (Sum.inl i)) = true) (he2 : ∀ j, ε (e (Sum.inr j)) = false)
    (Y : Matrix (Fin n) (Fin n) ℂ) :
    Matrix.reindex e.symm e.symm Y ∈ Formalism.BasicNotions.lieU P Q ↔
      ∀ a b, star (Y b a) * sg ε b + sg ε a * Y a b = 0 := by
  rw [mem_lieU_iff]
  have hs : ∀ i, Sum.elim (fun _ => (1 : ℂ)) (fun _ => -1) i = sg ε (e i) := by
    rintro (i | i) <;> simp [sg, he1, he2]
  simp only [Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.symm_symm, hs]
  constructor
  · intro h a b
    simpa using h (e.symm a) (e.symm b)
  · intro h i j
    exact h (e i) (e j)

/- English proof (translation)
Break down `lt_trichotomy a b with h | rfl | h` into its components or cases. Establish `h1 : ¬ b < a` using `lt_asymm h`. Establish `h2 : a ≠ b` using `ne_of_lt h`. Establish `h3 : b ≠ a` using `ne_of_gt h`. Apply the tactic sequence `cases ha : ε a <;> cases hb : ε b <;> simp [gMat, kMat, pmat, sg, h, h1, h2, h3, ha, hb]`.

Apply the tactic sequence `cases ha : ε a <;> simp [gMat, kMat, pmat, sg, ha]`. Establish `h1 : ¬ a < b` using `lt_asymm h`. Establish `h2 : a ≠ b` using `ne_of_gt h`. Establish `h3 : b ≠ a` using `ne_of_lt h`. Apply the tactic sequence `cases ha : ε a <;> cases hb : ε b <;> simp [gMat, kMat, pmat, sg, h, h1, h2, h3, ha, hb]`.
-/
theorem gMat_mem {ε : Fin n → Bool} (s : GCo ε) (a b : Fin n) :
    star (gMat s b a) * sg ε b + sg ε a * gMat s a b = 0 := by
  rcases lt_trichotomy a b with h | rfl | h
  · have h1 : ¬ b < a := lt_asymm h
    have h2 : a ≠ b := ne_of_lt h
    have h3 : b ≠ a := ne_of_gt h
    cases ha : ε a <;> cases hb : ε b <;> simp [gMat, kMat, pmat, sg, h, h1, h2, h3, ha, hb]
  · cases ha : ε a <;> simp [gMat, kMat, pmat, sg, ha]
  · have h1 : ¬ a < b := lt_asymm h
    have h2 : a ≠ b := ne_of_gt h
    have h3 : b ≠ a := ne_of_lt h
    cases ha : ε a <;> cases hb : ε b <;> simp [gMat, kMat, pmat, sg, h, h1, h2, h3, ha, hb]

/- English proof (translation)
Use extensionality with `a b`. Simplify using `only [gMat, kMat, pmat, Matrix.add_apply, Prod.fst_add, Prod.snd_add, Pi.add_apply]`. Apply the tactic sequence `split_ifs <;> (try simp only [star_add, neg_add, Complex.ofReal_add]) <;> ring`.
-/
theorem gMat_add {ε : Fin n → Bool} (s t : GCo ε) : gMat (s + t) = gMat s + gMat t := by
  ext a b
  simp only [gMat, kMat, pmat, Matrix.add_apply, Prod.fst_add, Prod.snd_add, Pi.add_apply]
  split_ifs <;> (try simp only [star_add, neg_add, Complex.ofReal_add]) <;> ring

/- English proof (translation)
Use extensionality with `a b`. Simplify using `only [gMat, kMat, pmat, Matrix.add_apply, Matrix.smul_apply, Prod.smul_fst, Prod.smul_snd, Pi.smul_apply]`. Apply the tactic sequence `split_ifs <;> (try simp only [smul_eq_mul, Complex.real_smul, Complex.ofReal_mul, star_mul', Complex.star_def, map_mul, Complex.conj_ofReal]) <;> ring`.
-/
theorem gMat_smul {ε : Fin n → Bool} (c : ℝ) (s : GCo ε) : gMat (c • s) = c • gMat s := by
  ext a b
  simp only [gMat, kMat, pmat, Matrix.add_apply, Matrix.smul_apply, Prod.smul_fst, Prod.smul_snd,
    Pi.smul_apply]
  split_ifs <;> (try simp only [smul_eq_mul, Complex.real_smul, Complex.ofReal_mul, star_mul',
    Complex.star_def, map_mul, Complex.conj_ofReal]) <;> ring

def coordOf {ε : Fin n → Bool} (Y : Matrix (Fin n) (Fin n) ℂ) : GCo ε :=
  ((fun a => (Y a a).im, fun k => Y k.1.1 k.1.2), fun p => Y p.1.1 p.1.2)

/- English proof (translation)
Use `Prod.ext (Prod.ext ?_ ?_) ?_` and prove the remaining obligations. Use function extensionality and compare the values at `a`. Simplify using `[coordOf, gMat, kMat, pmat]`. Use function extensionality and compare the values at `k`. Take `⟨⟨a, b⟩, hk⟩` from `k`.

Establish `h1 : a ≠ b` using `ne_of_gt hk.1`. Establish `h2 : ¬ a < b` using `lt_asymm hk.1`. Simplify using `[coordOf, gMat, kMat, pmat, h1, h2, hk.1, hk.2]`. Use function extensionality and compare the values at `q`. Take `⟨⟨a, b⟩, hq⟩` from `q`.

Establish `h1 : a ≠ b` using `ne_of_gt hq.1`. Establish `h2 : ¬ a < b` using `lt_asymm hq.1`. Simplify using `[coordOf, gMat, kMat, pmat, h1, h2, hq.1, hq.2]`.
-/
theorem coordOf_gMat {ε : Fin n → Bool} (s : GCo ε) : coordOf (gMat s) = s := by
  refine Prod.ext (Prod.ext ?_ ?_) ?_
  · funext a
    simp [coordOf, gMat, kMat, pmat]
  · funext k
    obtain ⟨⟨a, b⟩, hk⟩ := k
    have h1 : a ≠ b := ne_of_gt hk.1
    have h2 : ¬ a < b := lt_asymm hk.1
    simp [coordOf, gMat, kMat, pmat, h1, h2, hk.1, hk.2]
  · funext q
    obtain ⟨⟨a, b⟩, hq⟩ := q
    have h1 : a ≠ b := ne_of_gt hq.1
    have h2 : ¬ a < b := lt_asymm hq.1
    simp [coordOf, gMat, kMat, pmat, h1, h2, hq.1, hq.2]

/- English proof (translation)
Use extensionality with `a b`. Establish `key` using `hY a b`. Break down `lt_trichotomy a b with h | rfl | h` into its components or cases. Establish `h1 : ¬ b < a` using `lt_asymm h`. Establish `h2 : a ≠ b` using `ne_of_lt h`.

Apply the tactic sequence `cases ha : ε a <;> cases hb : ε b <;>`. Apply the tactic sequence `simp [gMat, kMat, pmat, coordOf, sg, h, h1, h2, ha, hb] at key ⊢ <;>`. Apply the tactic sequence `first | linear_combination key | linear_combination -key`. Establish `hre : (Y a a).re = 0`. Establish `hk` using `congrArg Complex.re key`.

Apply the tactic sequence `cases ha : ε a <;> simp [sg, ha] at hk <;> linarith`. Apply the tactic sequence `apply Complex.ext <;> simp [gMat, kMat, pmat, coordOf, hre]`. Establish `h1 : ¬ a < b` using `lt_asymm h`. Establish `h2 : a ≠ b` using `ne_of_gt h`. Apply the tactic sequence `cases ha : ε a <;> cases hb : ε b <;>`.

Apply the tactic sequence `simp [gMat, kMat, pmat, coordOf, sg, h, h1, h2, ha, hb] at key ⊢ <;>`. Apply the tactic sequence `first | linear_combination key | linear_combination -key`.
-/
theorem gMat_coordOf {ε : Fin n → Bool} (Y : Matrix (Fin n) (Fin n) ℂ)
    (hY : ∀ a b, star (Y b a) * sg ε b + sg ε a * Y a b = 0) : gMat (coordOf (ε := ε) Y) = Y := by
  ext a b
  have key := hY a b
  rcases lt_trichotomy a b with h | rfl | h
  · have h1 : ¬ b < a := lt_asymm h
    have h2 : a ≠ b := ne_of_lt h
    cases ha : ε a <;> cases hb : ε b <;>
      simp [gMat, kMat, pmat, coordOf, sg, h, h1, h2, ha, hb] at key ⊢ <;>
      first | linear_combination key | linear_combination -key
  · have hre : (Y a a).re = 0 := by
      have hk := congrArg Complex.re key
      cases ha : ε a <;> simp [sg, ha] at hk <;> linarith
    apply Complex.ext <;> simp [gMat, kMat, pmat, coordOf, hre]
  · have h1 : ¬ a < b := lt_asymm h
    have h2 : a ≠ b := ne_of_gt h
    cases ha : ε a <;> cases hb : ε b <;>
      simp [gMat, kMat, pmat, coordOf, sg, h, h1, h2, ha, hb] at key ⊢ <;>
      first | linear_combination key | linear_combination -key

end ReciprocityTheory.ChartRestriction.DS.OmegaPQAux

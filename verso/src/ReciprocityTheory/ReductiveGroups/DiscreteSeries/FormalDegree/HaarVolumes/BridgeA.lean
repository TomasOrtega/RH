import ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.HaarVolumes.VolUDensity
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.HaarVolumes.IntegralGaussEOmPhiOmE

noncomputable section

open Finset Matrix MeasureTheory Filter Topology

namespace ReciprocityTheory.ChartRestriction.DS

open ReciprocityTheory.ChartRestriction.DS.S7

namespace PolarCoordinateComparison

variable {N : ℕ}

abbrev eN (N : ℕ) : Fin N ⊕ Fin 0 ≃ Fin N := Equiv.sumEmpty (Fin N) (Fin 0)

/- English proof (translation)
Use extensionality with `i j`. Break down `i with i | i` into its components or cases. Break down `j with j | j` into its components or cases. Simplify using `[Formalism.UG.Jpq, Matrix.one_apply]`. Conclude with `j.elim0`.

Conclude with `i.elim0`.
-/
lemma Jpq_zero (N : ℕ) : Formalism.UG.Jpq N 0 = 1 := by
  ext i j
  rcases i with i | i
  · rcases j with j | j
    · simp [Formalism.UG.Jpq, Matrix.one_apply]
    · exact j.elim0
  · exact i.elim0

/- English proof (translation)
Simplify using `[Jm, Formalism.REAL.Jm]`.
-/
lemma Jm_true (N : ℕ) : Jm (fun _ : Fin N => true) = 1 := by
  simp [Jm, Formalism.REAL.Jm]

/- English proof (translation)
Use extensionality with `i j`. Simplify using `[Formalism.UG.cT]`.
-/
lemma cT_eq {m : Type} [Fintype m] (M : Matrix m m ℂ) : Formalism.UG.cT (starRingEnd ℂ) M = Mᴴ := by
  ext i j
  simp [Formalism.UG.cT]

def psi (N : ℕ) : GL (Fin N ⊕ Fin 0) ℂ ≃* (Matrix (Fin N) (Fin N) ℂ)ˣ :=
  Units.mapEquiv (reindexAlgEquiv ℂ ℂ (eN N)).toMulEquiv

/- English proof (translation)
Both sides reduce to the same expression.
-/
lemma psi_val (N : ℕ) (u : GL (Fin N ⊕ Fin 0) ℂ) :
    ((psi N u : (Matrix (Fin N) (Fin N) ℂ)ˣ) : Matrix (Fin N) (Fin N) ℂ) = reindex (eN N) (eN N) u := by
  rfl

/- English proof (translation)
Both sides reduce to the same expression.
-/
lemma psi_symm_val (N : ℕ) (u : (Matrix (Fin N) (Fin N) ℂ)ˣ) :
    (((psi N).symm u : GL (Fin N ⊕ Fin 0) ℂ) : Matrix (Fin N ⊕ Fin 0) (Fin N ⊕ Fin 0) ℂ) =
      reindex (eN N).symm (eN N).symm u := by
  rfl

/- English proof (translation)
Use `show Formalism.UG.cT (starRingEnd ℂ) (u : Matrix (Fin N ⊕ Fin 0) (Fin N ⊕ Fin 0) ℂ) * Formalism.UG.Jpq N 0 * u = Formalism.UG.Jpq N 0 ↔ _`. Rewrite using `[Jpq_zero, cT_eq, Matrix.mul_one]`.
-/
lemma mem_upq_iff (N : ℕ) (u : GL (Fin N ⊕ Fin 0) ℂ) :
    u ∈ Formalism.UG.Upq N 0 ↔ (u : Matrix (Fin N ⊕ Fin 0) (Fin N ⊕ Fin 0) ℂ)ᴴ * u = 1 := by
  show Formalism.UG.cT (starRingEnd ℂ) (u : Matrix (Fin N ⊕ Fin 0) (Fin N ⊕ Fin 0) ℂ) * Formalism.UG.Jpq N 0 * u =
    Formalism.UG.Jpq N 0 ↔ _
  rw [Jpq_zero, cT_eq, Matrix.mul_one]

/- English proof (translation)
Use `show (u : Matrix (Fin N) (Fin N) ℂ)ᴴ * Formalism.REAL.Jm (fun _ : Fin N => true) * u = Formalism.REAL.Jm (fun _ : Fin N => true) ↔ _`. Rewrite using `[show Formalism.REAL.Jm (fun _ : Fin N => true) = 1 by simp [Formalism.REAL.Jm], Matrix.mul_one]`.
-/
lemma mem_un_iff (N : ℕ) (u : (Matrix (Fin N) (Fin N) ℂ)ˣ) :
    u ∈ UNgrp N ↔ (u : Matrix (Fin N) (Fin N) ℂ)ᴴ * u = 1 := by
  show (u : Matrix (Fin N) (Fin N) ℂ)ᴴ * Formalism.REAL.Jm (fun _ : Fin N => true) * u =
    Formalism.REAL.Jm (fun _ : Fin N => true) ↔ _
  rw [show Formalism.REAL.Jm (fun _ : Fin N => true) = 1 by simp [Formalism.REAL.Jm], Matrix.mul_one]

/- English proof (translation)
Rewrite using `[Matrix.conjTranspose_reindex]`. Establish `hm` using `(Matrix.reindexAlgEquiv ℂ ℂ e).map_mul Aᴴ A`. Rewrite `hm` using `[h, map_one]`. Conclude with `hm.symm`.
-/
lemma reindex_unitary {m n : Type} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n] (e : m ≃ n)
    (A : Matrix m m ℂ) (h : Aᴴ * A = 1) : (reindex e e A)ᴴ * reindex e e A = 1 := by
  rw [Matrix.conjTranspose_reindex]
  have hm := (Matrix.reindexAlgEquiv ℂ ℂ e).map_mul Aᴴ A
  rw [h, map_one] at hm
  exact hm.symm

def iso (N : ℕ) : Formalism.BasicNotions.UpqT N 0 ≃* UNgrp N where
  toFun g := ⟨psi N (g : Formalism.UG.Upq N 0).1, by
    rw [mem_un_iff, psi_val]
    exact reindex_unitary _ _ ((mem_upq_iff N _).1 (g : Formalism.UG.Upq N 0).2)⟩
  invFun k := (⟨(psi N).symm k.1, by
    rw [mem_upq_iff, psi_symm_val]
    exact reindex_unitary _ _ ((mem_un_iff N _).1 k.2)⟩ : Formalism.UG.Upq N 0)
  left_inv g := Subtype.ext ((psi N).symm_apply_apply _)
  right_inv k := Subtype.ext ((psi N).apply_symm_apply _)
  map_mul' g h := Subtype.ext (map_mul (psi N) _ _)

/- English proof (translation)
The claim follows from `psi_val N _`.
-/
lemma toM_iso (N : ℕ) (g : Formalism.BasicNotions.UpqT N 0) :
    toM (iso N g) = reindex (eN N) (eN N) (Formalism.BasicNotions.UpqT.mat g) := psi_val N _

/- English proof (translation)
The claim follows from `psi_symm_val N _`.
-/
lemma mat_iso_symm (N : ℕ) (k : UNgrp N) :
    Formalism.BasicNotions.UpqT.mat ((iso N).symm k) = reindex (eN N).symm (eN N).symm (toM k) := psi_symm_val N _

/- English proof (translation)
The claim follows from `Units.continuous_val.comp continuous_subtype_val`.
-/
lemma continuous_mat (N : ℕ) : Continuous (fun g : Formalism.BasicNotions.UpqT N 0 => Formalism.BasicNotions.UpqT.mat g) :=
  Units.continuous_val.comp continuous_subtype_val

/- English proof (translation)
Establish `hpsi : Continuous fun u : GL (Fin N ⊕ Fin 0) ℂ => psi N u` using `Units.continuous_iff.2 ⟨Units.continuous_val.matrix_reindex _ _, Units.continuous_coe_inv.matrix_reindex _ _⟩`. Conclude with `(hpsi.comp continuous_subtype_val).subtype_mk _`.
-/
lemma continuous_iso (N : ℕ) : Continuous (iso N) := by
  have hpsi : Continuous fun u : GL (Fin N ⊕ Fin 0) ℂ => psi N u :=
    Units.continuous_iff.2 ⟨Units.continuous_val.matrix_reindex _ _, Units.continuous_coe_inv.matrix_reindex _ _⟩
  exact (hpsi.comp continuous_subtype_val).subtype_mk _

instance instBorelUpqT (P Q : ℕ) : BorelSpace (Formalism.BasicNotions.UpqT P Q) := ⟨rfl⟩

instance instBorelLieU (P Q : ℕ) : BorelSpace (Formalism.BasicNotions.lieU P Q) := ⟨rfl⟩

instance instContMulUpqT (N : ℕ) : ContinuousMul (Formalism.BasicNotions.UpqT N 0) :=
  inferInstanceAs (ContinuousMul (Formalism.UG.Upq N 0))

/- English proof (translation)
Establish `hv : (Units.val ∘ fun u : (Matrix (Fin N) (Fin N) ℂ)ˣ => (psi N).symm u) = fun u : (Matrix (Fin N) (Fin N) ℂ)ˣ => reindex (eN N).symm (eN N).symm (u : Matrix (Fin N) (Fin N) ℂ)`. Use function extensionality and compare the values at `u`. Conclude with `psi_symm_val N u`. Use `Units.continuous_iff.2 ⟨?_, ?_⟩` and prove the remaining obligations. Rewrite using `[hv]`.

Conclude with `Units.continuous_val.matrix_reindex _ _`. Establish `hf : (fun u : (Matrix (Fin N) (Fin N) ℂ)ˣ => ((((psi N).symm u)⁻¹ : GL (Fin N ⊕ Fin 0) ℂ) : Matrix (Fin N ⊕ Fin 0) (Fin N ⊕ Fin 0) ℂ)) = fun u => reindex (eN N).symm (eN N).symm (((u⁻¹ : (Matrix (Fin N) (Fin N) ℂ)ˣ)) : Matrix (Fin N) (Fin N) ℂ)`. Use function extensionality and compare the values at `u`. Rewrite using `[← map_inv, psi_symm_val]`. Rewrite using `[hf]`.

Conclude with `Units.continuous_coe_inv.matrix_reindex _ _`.
-/
lemma continuous_psi_symm (N : ℕ) : Continuous (fun u : (Matrix (Fin N) (Fin N) ℂ)ˣ => (psi N).symm u) := by
  have hv : (Units.val ∘ fun u : (Matrix (Fin N) (Fin N) ℂ)ˣ => (psi N).symm u) =
      fun u : (Matrix (Fin N) (Fin N) ℂ)ˣ => reindex (eN N).symm (eN N).symm (u : Matrix (Fin N) (Fin N) ℂ) := by
    funext u
    exact psi_symm_val N u
  refine Units.continuous_iff.2 ⟨?_, ?_⟩
  · rw [hv]
    exact Units.continuous_val.matrix_reindex _ _
  have hf : (fun u : (Matrix (Fin N) (Fin N) ℂ)ˣ =>
      ((((psi N).symm u)⁻¹ : GL (Fin N ⊕ Fin 0) ℂ) : Matrix (Fin N ⊕ Fin 0) (Fin N ⊕ Fin 0) ℂ)) =
      fun u => reindex (eN N).symm (eN N).symm (((u⁻¹ : (Matrix (Fin N) (Fin N) ℂ)ˣ)) : Matrix (Fin N) (Fin N) ℂ) := by
    funext u
    rw [← map_inv, psi_symm_val]
  rw [hf]
  exact Units.continuous_coe_inv.matrix_reindex _ _

/- English proof (translation)
The claim follows from `((continuous_psi_symm N).comp continuous_subtype_val).subtype_mk _`.
-/
lemma continuous_iso_symm (N : ℕ) : Continuous (iso N).symm :=
  ((continuous_psi_symm N).comp continuous_subtype_val).subtype_mk _

def homeo (N : ℕ) : Formalism.BasicNotions.UpqT N 0 ≃ₜ UNgrp N where
  toEquiv := (iso N).toEquiv
  continuous_toFun := continuous_iso N
  continuous_invFun := continuous_iso_symm N

/- English proof (translation)
The claim follows from `(homeo N).toMeasurableEquiv.map_apply T`.
-/
lemma map_iso_apply (N : ℕ) (μ : Measure (Formalism.BasicNotions.UpqT N 0)) (T : Set (UNgrp N)) :
    μ.map (iso N) T = μ ((iso N) ⁻¹' T) :=
  (homeo N).toMeasurableEquiv.map_apply T

def coords {N : ℕ} (M : Matrix (Fin N) (Fin N) ℂ) : UCo N :=
  (fun a => (M a a).im, fun ab => M ab.1.1 ab.1.2)

/- English proof (translation)
Use extensionality with `a b`. Establish `hab` using `congrFun (congrFun hM a) b`. Rewrite `hab` using `[Matrix.conjTranspose_apply, Matrix.neg_apply]`. Simplify using `only [skMat, coords]`. Use `split_ifs with h1 h2 h3`.

Substitute `h1` using the available equality. Establish `hre : (M a a).re = 0`. Establish `h4` using `congrArg Complex.re hab`. Simplify using `only [Complex.star_def, Complex.conj_re, Complex.neg_re] at h4`. Combine the linear equalities and inequalities to obtain the conclusion.

Apply `Complex.ext` to reduce the goal to its premises. Simplify using `only [Complex.mul_re, Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im]`. Rewrite using `[hre]`. Expand and normalize the polynomial expressions, which then agree. Simplify using `only [Complex.mul_im, Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im]`.

Expand and normalize the polynomial expressions, which then agree. Both sides reduce to the same expression. Rewrite using `[hab, neg_neg]`. Break down `lt_trichotomy a b with h | h | h` into its components or cases. Conclude with `absurd h h3`.

Conclude with `absurd h h1`. Conclude with `absurd h h2`.
-/
lemma skMat_coords {N : ℕ} (M : Matrix (Fin N) (Fin N) ℂ) (hM : Mᴴ = -M) : skMat (coords M) = M := by
  ext a b
  have hab := congrFun (congrFun hM a) b
  rw [Matrix.conjTranspose_apply, Matrix.neg_apply] at hab
  simp only [skMat, coords]
  split_ifs with h1 h2 h3
  · subst h1
    have hre : (M a a).re = 0 := by
      have h4 := congrArg Complex.re hab
      simp only [Complex.star_def, Complex.conj_re, Complex.neg_re] at h4
      linarith
    apply Complex.ext
    · simp only [Complex.mul_re, Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im]
      rw [hre]
      ring
    · simp only [Complex.mul_im, Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im]
      ring
  · rfl
  · rw [hab, neg_neg]
  · rcases lt_trichotomy a b with h | h | h
    · exact absurd h h3
    · exact absurd h h1
    · exact absurd h h2

/- English proof (translation)
Establish `h' : (X : Matrix (Fin N ⊕ Fin 0) (Fin N ⊕ Fin 0) ℂ)ᴴ * Formalism.UG.Jpq N 0 + Formalism.UG.Jpq N 0 * (X : Matrix (Fin N ⊕ Fin 0) (Fin N ⊕ Fin 0) ℂ) = 0` using `X.2`. Rewrite `h'` using `[Jpq_zero, Matrix.mul_one, Matrix.one_mul]`. Conclude with `eq_neg_of_add_eq_zero_left h'`.
-/
lemma lie_skew {N : ℕ} (X : Formalism.BasicNotions.lieU N 0) :
    (X : Matrix (Fin N ⊕ Fin 0) (Fin N ⊕ Fin 0) ℂ)ᴴ = -(X : Matrix (Fin N ⊕ Fin 0) (Fin N ⊕ Fin 0) ℂ) := by
  have h' : (X : Matrix (Fin N ⊕ Fin 0) (Fin N ⊕ Fin 0) ℂ)ᴴ * Formalism.UG.Jpq N 0 +
      Formalism.UG.Jpq N 0 * (X : Matrix (Fin N ⊕ Fin 0) (Fin N ⊕ Fin 0) ℂ) = 0 := X.2
  rw [Jpq_zero, Matrix.mul_one, Matrix.one_mul] at h'
  exact eq_neg_of_add_eq_zero_left h'

/- English proof (translation)
Establish `hsk : (reindex (eN N) (eN N) (X : Matrix (Fin N ⊕ Fin 0) (Fin N ⊕ Fin 0) ℂ))ᴴ = -reindex (eN N) (eN N) (X : Matrix (Fin N ⊕ Fin 0) (Fin N ⊕ Fin 0) ℂ)`. Rewrite using `[Matrix.conjTranspose_reindex, lie_skew X]`. Apply the tactic sequence `try rfl`. Apply `Subtype.ext` to reduce the goal to its premises. Use `show uToLieMat (coords (reindex (eN N) (eN N) (X : Matrix (Fin N ⊕ Fin 0) (Fin N ⊕ Fin 0) ℂ))) = X`.

Simplify using `only [uToLieMat]`. Rewrite using `[skMat_coords _ hsk]`. Use extensionality with `i j`. Simplify using the standard rewrite rules.
-/
lemma uToLie_coords {N : ℕ} (X : Formalism.BasicNotions.lieU N 0) :
    uToLie (coords (reindex (eN N) (eN N) (X : Matrix (Fin N ⊕ Fin 0) (Fin N ⊕ Fin 0) ℂ))) = X := by
  have hsk : (reindex (eN N) (eN N) (X : Matrix (Fin N ⊕ Fin 0) (Fin N ⊕ Fin 0) ℂ))ᴴ =
      -reindex (eN N) (eN N) (X : Matrix (Fin N ⊕ Fin 0) (Fin N ⊕ Fin 0) ℂ) := by
    rw [Matrix.conjTranspose_reindex, lie_skew X]
    try rfl
  apply Subtype.ext
  show uToLieMat (coords (reindex (eN N) (eN N) (X : Matrix (Fin N ⊕ Fin 0) (Fin N ⊕ Fin 0) ℂ))) = X
  simp only [uToLieMat]
  rw [skMat_coords _ hsk]
  ext i j
  simp

/- English proof (translation)
Use `letI : NormedRing (Matrix m m ℂ) := Matrix.linftyOpNormedRing`. Use `letI : NormedRing (Matrix n n ℂ) := Matrix.linftyOpNormedRing`. Use `letI : NormedAlgebra ℂ (Matrix m m ℂ) := Matrix.linftyOpNormedAlgebra`. Use `letI : NormedAlgebra ℂ (Matrix n n ℂ) := Matrix.linftyOpNormedAlgebra`. Use `letI : NormedAlgebra ℚ (Matrix m m ℂ) := Matrix.linftyOpNormedAlgebra`.

Use `letI : NormedAlgebra ℚ (Matrix n n ℂ) := Matrix.linftyOpNormedAlgebra`. Conclude with `NormedSpace.map_exp (Matrix.reindexAlgEquiv ℂ ℂ e) (Matrix.reindexAlgEquiv ℂ ℂ e).toLinearEquiv.toLinearMap.continuous_of_finiteDimensional A`.
-/
lemma reindex_exp {m n : Type} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n] (e : m ≃ n)
    (A : Matrix m m ℂ) : reindex e e (NormedSpace.exp A) = NormedSpace.exp (reindex e e A) := by
  letI : NormedRing (Matrix m m ℂ) := Matrix.linftyOpNormedRing
  letI : NormedRing (Matrix n n ℂ) := Matrix.linftyOpNormedRing
  letI : NormedAlgebra ℂ (Matrix m m ℂ) := Matrix.linftyOpNormedAlgebra
  letI : NormedAlgebra ℂ (Matrix n n ℂ) := Matrix.linftyOpNormedAlgebra
  letI : NormedAlgebra ℚ (Matrix m m ℂ) := Matrix.linftyOpNormedAlgebra
  letI : NormedAlgebra ℚ (Matrix n n ℂ) := Matrix.linftyOpNormedAlgebra
  exact NormedSpace.map_exp (Matrix.reindexAlgEquiv ℂ ℂ e)
    (Matrix.reindexAlgEquiv ℂ ℂ e).toLinearEquiv.toLinearMap.continuous_of_finiteDimensional A

/- English proof (translation)
Use extensionality with `g`. Simplify using `only [Set.mem_preimage, Set.mem_setOf_eq, toM_iso]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨x, hx, hxe⟩`. Use `⟨uToLie x, hx, ?_⟩` and prove the remaining obligations.

Establish `hm : Formalism.BasicNotions.UpqT.mat g = reindex (eN N).symm (eN N).symm (reindex (eN N) (eN N) (Formalism.BasicNotions.UpqT.mat g))`. Use extensionality with `i j`. Simplify using the standard rewrite rules. Rewrite using `[hm, hxe, reindex_exp]`. Apply the tactic sequence `try rfl`.

Introduce and unpack `⟨X, hX, hXe⟩`. Use `⟨coords (reindex (eN N) (eN N) (X : Matrix (Fin N ⊕ Fin 0) (Fin N ⊕ Fin 0) ℂ)), ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[uToLie_coords]`. Conclude with `hX`. Rewrite using `[hXe, reindex_exp, skMat_coords]`.

Rewrite using `[Matrix.conjTranspose_reindex, lie_skew X]`. Apply the tactic sequence `try rfl`.
-/
lemma toM_preimage_exp_ball_eq_upqT_exp_ball (N : ℕ) (r : ℝ) :
    (iso N) ⁻¹' {k : UNgrp N | ∃ x ∈ uToLie ⁻¹' Formalism.BasicNotions.ballU N 0 r, toM k = NormedSpace.exp (skMat x)} =
      {g | ∃ X ∈ Formalism.BasicNotions.ballU N 0 r, Formalism.BasicNotions.UpqT.mat g =
        NormedSpace.exp (X : Matrix (Fin N ⊕ Fin 0) (Fin N ⊕ Fin 0) ℂ)} := by
  ext g
  simp only [Set.mem_preimage, Set.mem_setOf_eq, toM_iso]
  constructor
  · rintro ⟨x, hx, hxe⟩
    refine ⟨uToLie x, hx, ?_⟩
    have hm : Formalism.BasicNotions.UpqT.mat g = reindex (eN N).symm (eN N).symm
        (reindex (eN N) (eN N) (Formalism.BasicNotions.UpqT.mat g)) := by
      ext i j
      simp
    rw [hm, hxe, reindex_exp]
    try rfl
  · rintro ⟨X, hX, hXe⟩
    refine ⟨coords (reindex (eN N) (eN N) (X : Matrix (Fin N ⊕ Fin 0) (Fin N ⊕ Fin 0) ℂ)), ?_, ?_⟩
    · rw [uToLie_coords]
      exact hX
    · rw [hXe, reindex_exp, skMat_coords]
      rw [Matrix.conjTranspose_reindex, lie_skew X]
      try rfl

/- English proof (translation)
Unfold `volU`. Apply `Finset.prod_pos` to reduce the goal to its premises. Introduce `i _`. Check the signs of the components of the expression.
-/
lemma volU_pos (N : ℕ) : 0 < volU N := by
  unfold volU
  apply Finset.prod_pos
  intro i _
  positivity

/- English proof (translation)
Use `continuous_pi fun a => continuous_pi fun b => ?_` and prove the remaining obligations. Simplify using `only [skMat]`. Distinguish the cases in `h1 : a = b`. Simplify using `only [if_pos h1]`. Conclude with `continuous_const.mul (Complex.continuous_ofReal.comp ((continuous_apply a).comp continuous_fst))`.

Simplify using `only [if_neg h1]`. Distinguish the cases in `h2 : b < a`. Simplify using `only [dif_pos h2]`. Conclude with `(continuous_apply _).comp continuous_snd`. Simplify using `only [dif_neg h2]`.

Distinguish the cases in `h3 : a < b`. Simplify using `only [dif_pos h3]`. Conclude with `((continuous_apply _).comp continuous_snd).star.neg`. Simplify using `only [dif_neg h3]`. Conclude with `continuous_const`.
-/
lemma continuous_skMat (N : ℕ) : Continuous (skMat : UCo N → Matrix (Fin N) (Fin N) ℂ) := by
  refine continuous_pi fun a => continuous_pi fun b => ?_
  simp only [skMat]
  by_cases h1 : a = b
  · simp only [if_pos h1]
    exact continuous_const.mul (Complex.continuous_ofReal.comp ((continuous_apply a).comp continuous_fst))
  · simp only [if_neg h1]
    by_cases h2 : b < a
    · simp only [dif_pos h2]
      exact (continuous_apply _).comp continuous_snd
    · simp only [dif_neg h2]
      by_cases h3 : a < b
      · simp only [dif_pos h3]
        exact ((continuous_apply _).comp continuous_snd).star.neg
      · simp only [dif_neg h3]
        exact continuous_const

/- English proof (translation)
Use `show Continuous fun x : UCo N => (⟨uToLieMat x, uToLieMat_mem x⟩ : Formalism.BasicNotions.lieU N 0)`. Conclude with `Continuous.subtype_mk ((continuous_skMat N).matrix_reindex _ _) _`.
-/
lemma continuous_uToLie (N : ℕ) : Continuous (uToLie (N := N)) := by
  show Continuous fun x : UCo N => (⟨uToLieMat x, uToLieMat_mem x⟩ : Formalism.BasicNotions.lieU N 0)
  exact Continuous.subtype_mk ((continuous_skMat N).matrix_reindex _ _) _

/- English proof (translation)
Establish `hv : Continuous (fun X : Formalism.BasicNotions.lieU N 0 => (X : Matrix (Fin N ⊕ Fin 0) (Fin N ⊕ Fin 0) ℂ))` using `continuous_subtype_val`. Unfold `Formalism.BasicNotions.ballU`. Conclude with `isOpen_lt (continuous_finset_sum _ fun i _ => continuous_finset_sum _ fun j _ => ((continuous_apply j).comp ((continuous_apply i).comp hv)).norm) continuous_const`.
-/
lemma isOpen_ballU (N : ℕ) (r : ℝ) : IsOpen (Formalism.BasicNotions.ballU N 0 r) := by
  have hv : Continuous (fun X : Formalism.BasicNotions.lieU N 0 => (X : Matrix (Fin N ⊕ Fin 0) (Fin N ⊕ Fin 0) ℂ)) :=
    continuous_subtype_val
  unfold Formalism.BasicNotions.ballU
  exact isOpen_lt (continuous_finset_sum _ fun i _ => continuous_finset_sum _ fun j _ =>
    ((continuous_apply j).comp ((continuous_apply i).comp hv)).norm) continuous_const

/- English proof (translation)
Simplify using `[uToLieMat]`.
-/
lemma uToLieMat_apply (x : UCo N) (a b : Fin N) : uToLieMat x ((eN N).symm a) ((eN N).symm b) = skMat x a b := by
  simp [uToLieMat]

/- English proof (translation)
Establish `hx' : ∑ i, ∑ j, ‖uToLieMat x i j‖ < r` using `hx`. Rewrite using `[← uToLieMat_apply]`. Combine the equalities or inequalities in the displayed calculation.
-/
lemma norm_skMat_lt (x : UCo N) (r : ℝ) (hx : uToLie x ∈ Formalism.BasicNotions.ballU N 0 r) (a b : Fin N) :
    ‖skMat x a b‖ < r := by
  have hx' : ∑ i, ∑ j, ‖uToLieMat x i j‖ < r := hx
  rw [← uToLieMat_apply]
  calc ‖uToLieMat x ((eN N).symm a) ((eN N).symm b)‖
      ≤ ∑ j, ‖uToLieMat x ((eN N).symm a) j‖ :=
        Finset.single_le_sum (f := fun j => ‖uToLieMat x ((eN N).symm a) j‖) (fun j _ => norm_nonneg _)
          (Finset.mem_univ _)
    _ ≤ ∑ i, ∑ j, ‖uToLieMat x i j‖ :=
        Finset.single_le_sum (f := fun i => ∑ j, ‖uToLieMat x i j‖)
          (fun i _ => Finset.sum_nonneg fun j _ => norm_nonneg _) (Finset.mem_univ _)
    _ < r := hx'

/- English proof (translation)
Establish `h1 : ‖x.1‖ < r`. Use `(pi_norm_lt_iff hr).2 fun a => ?_` and prove the remaining obligations. Establish `h5` using `norm_skMat_lt x r hx a a`. Simplify `h5` using `[skMat]`. Establish `h2 : ‖x.2‖ < r`.

Use `(pi_norm_lt_iff hr).2 ?_` and prove the remaining obligations. Introduce and unpack `⟨⟨a, b⟩, hab⟩`. Establish `h5` using `norm_skMat_lt x r hx a b`. Simplify `h5` using `[skMat, ne_of_gt hab, hab]`. Rewrite using `[Prod.norm_def]`.

Conclude with `max_lt h1 h2`.
-/
lemma norm_lt_of_mem (x : UCo N) (r : ℝ) (hr : 0 < r) (hx : uToLie x ∈ Formalism.BasicNotions.ballU N 0 r) : ‖x‖ < r := by
  have h1 : ‖x.1‖ < r := by
    refine (pi_norm_lt_iff hr).2 fun a => ?_
    have h5 := norm_skMat_lt x r hx a a
    simpa [skMat] using h5
  have h2 : ‖x.2‖ < r := by
    refine (pi_norm_lt_iff hr).2 ?_
    rintro ⟨⟨a, b⟩, hab⟩
    have h5 := norm_skMat_lt x r hx a b
    simpa [skMat, ne_of_gt hab, hab] using h5
  rw [Prod.norm_def]
  exact max_lt h1 h2

/- English proof (translation)
Use `show ∑ i, ∑ j, ‖uToLieMat (0 : UCo N) i j‖ < r`. Establish `h0 : ∀ i j, uToLieMat (0 : UCo N) i j = 0`. Introduce `i j`. Simplify using `only [uToLieMat, Matrix.reindex_apply, Matrix.submatrix_apply, skMat]`. Apply the tactic sequence `split_ifs <;> simp`.

Simplify using `[h0, hr]`.
-/
lemma zero_mem_B (r : ℝ) (hr : 0 < r) : (0 : UCo N) ∈ uToLie ⁻¹' Formalism.BasicNotions.ballU N 0 r := by
  show ∑ i, ∑ j, ‖uToLieMat (0 : UCo N) i j‖ < r
  have h0 : ∀ i j, uToLieMat (0 : UCo N) i j = 0 := by
    intro i j
    simp only [uToLieMat, Matrix.reindex_apply, Matrix.submatrix_apply, skMat]
    split_ifs <;> simp
  simp [h0, hr]

/- English proof (translation)
The claim follows from `div_pos one_pos (mul_pos (by positivity) (volU_pos N))`.
-/
theorem cOmega_pos' (N : ℕ) : 0 < 1 / (2 ^ (N * (N - 1) / 2) * volU N) :=
  div_pos one_pos (mul_pos (by positivity) (volU_pos N))

/- English proof (translation)
Establish `hH : (μ.map (iso N)).IsHaarMeasure` using `(iso N).isHaarMeasure_map μ (continuous_iso N) (continuous_iso_symm N)`. Establish `hP : IsProbabilityMeasure (μ.map (iso N))` using `Measure.isProbabilityMeasure_map (continuous_iso N).measurable.aemeasurable`. Use `⟨_, isOmegaLeb_uToLie, ?_⟩` and prove the remaining obligations. Establish `hκ : (0 : ℝ) < 2 ^ (N * (N - 1) / 2)` using `by positivity`. Establish `hV : 0 < volU N` using `volU_pos N`.

Establish `hcpos` using `cOmega_pos' N`. Rewrite using `[ENNReal.tendsto_nhds ENNReal.ofReal_ne_top]`. Introduce `ε hε`. Take `⟨e, he0, he1, he2⟩` from `ENNReal.lt_iff_exists_real_btwn.1 hε`. Establish `he : 0 < e` using `ENNReal.ofReal_pos.1 he1`.

Take `⟨δ, hδ, hB⟩` from `volU_density (μ.map (iso N)) (e / (1 / (2 ^ (N * (N - 1) / 2) * volU N))) (div_pos he hcpos)`. Use `filter_upwards [Ioo_mem_nhdsGT hδ] with r hr`. Establish `hBo : IsOpen (uToLie ⁻¹' Formalism.BasicNotions.ballU N 0 r)` using `(isOpen_ballU N r).preimage (continuous_uToLie N)`. Establish `hBn : ∀ x ∈ uToLie ⁻¹' Formalism.BasicNotions.ballU N 0 r, ‖x‖ < δ` using `fun x hx => (norm_lt_of_mem x r hr.1 hx).trans hr.2`. Establish `hB0 : volume (uToLie ⁻¹' Formalism.BasicNotions.ballU N 0 r) ≠ 0` using `(hBo.measure_pos volume ⟨0, zero_mem_B r hr.1⟩).ne'`.

Establish `hBt : volume (uToLie ⁻¹' Formalism.BasicNotions.ballU N 0 r) ≠ ⊤` using `ne_of_lt (lt_of_le_of_lt (measure_mono fun x hx => mem_ball_zero_iff.2 (norm_lt_of_mem x r hr.1 hx)) measure_ball_lt_top)`. Establish `hnum : μ {g | ∃ X ∈ Formalism.BasicNotions.ballU N 0 r, Formalism.BasicNotions.UpqT.mat g = NormedSpace.exp (X : Matrix (Fin N ⊕ Fin 0) (Fin N ⊕ Fin 0) ℂ)} = μ.map (iso N) {k : UNgrp N | ∃ x ∈ uToLie ⁻¹' Formalism.BasicNotions.ballU N 0 r, toM k = NormedSpace.exp (skMat x)}`. Rewrite using `[map_iso_apply, toM_preimage_exp_ball_eq_upqT_exp_ball]`. Establish `hden : (ENNReal.ofReal (2 ^ (N * (N - 1) / 2)) • Measure.map (uToLie (N` using `N)) volume) (Formalism.BasicNotions.ballU N 0 r) = ENNReal.ofReal (2 ^ (N * (N - 1) / 2)) * volume (uToLie ⁻¹' Formalism.BasicNotions.ballU N 0 r) := by`. Rewrite using `[Measure.smul_apply, Measure.map_apply (continuous_uToLie N).measurable (isOpen_ballU N r).measurableSet, smul_eq_mul]`.

Take `⟨hup, hlo⟩` from `hB _ hBo.measurableSet hBn`. Simplify using `only [Set.mem_Icc]`. Rewrite using `[hnum, hden]`. Establish `hκ0 : ENNReal.ofReal (2 ^ (N * (N - 1) / 2)) ≠ 0` using `(ENNReal.ofReal_pos.2 hκ).ne'`. Prove the components needed by the constructor for the conclusion.

Combine the equalities or inequalities in the displayed calculation. Rewrite using `[ENNReal.le_div_iff_mul_le (Or.inl (mul_ne_zero hκ0 hB0)) (Or.inl (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hBt))]`. Use `le_trans (le_of_eq ?_) hlo` and prove the remaining obligations. Rewrite using `[← mul_assoc, ← ENNReal.ofReal_mul' hκ.le]`. Use `congr 2`.

Clear the denominators using the available nonvanishing facts. Combine the equalities or inequalities in the displayed calculation. Use `ENNReal.div_le_of_le_mul (le_trans hup (le_of_eq ?_))` and prove the remaining obligations. Rewrite using `[← mul_assoc, ← ENNReal.ofReal_mul (by positivity)]`. Use `congr 2`.

Clear the denominators using the available nonvanishing facts. Use `_ = ENNReal.ofReal (1 / (2 ^ (N * (N - 1) / 2) * volU N)) + ENNReal.ofReal e := ENNReal.ofReal_add hcpos.le he.le`. Use `_ ≤ _ := by gcongr`.
-/
theorem omegaDensity_main (μ : Measure (Formalism.BasicNotions.UpqT N 0)) [μ.IsHaarMeasure] [IsProbabilityMeasure μ] :
    Formalism.BasicNotions.OmegaDensity μ (ENNReal.ofReal (1 / (2 ^ (N * (N - 1) / 2) * volU N))) := by
  have hH : (μ.map (iso N)).IsHaarMeasure := (iso N).isHaarMeasure_map μ (continuous_iso N) (continuous_iso_symm N)
  have hP : IsProbabilityMeasure (μ.map (iso N)) :=
    Measure.isProbabilityMeasure_map (continuous_iso N).measurable.aemeasurable
  refine ⟨_, isOmegaLeb_uToLie, ?_⟩
  have hκ : (0 : ℝ) < 2 ^ (N * (N - 1) / 2) := by positivity
  have hV : 0 < volU N := volU_pos N
  have hcpos := cOmega_pos' N
  rw [ENNReal.tendsto_nhds ENNReal.ofReal_ne_top]
  intro ε hε
  obtain ⟨e, he0, he1, he2⟩ := ENNReal.lt_iff_exists_real_btwn.1 hε
  have he : 0 < e := ENNReal.ofReal_pos.1 he1
  obtain ⟨δ, hδ, hB⟩ := volU_density (μ.map (iso N)) (e / (1 / (2 ^ (N * (N - 1) / 2) * volU N)))
    (div_pos he hcpos)
  filter_upwards [Ioo_mem_nhdsGT hδ] with r hr
  have hBo : IsOpen (uToLie ⁻¹' Formalism.BasicNotions.ballU N 0 r) := (isOpen_ballU N r).preimage (continuous_uToLie N)
  have hBn : ∀ x ∈ uToLie ⁻¹' Formalism.BasicNotions.ballU N 0 r, ‖x‖ < δ :=
    fun x hx => (norm_lt_of_mem x r hr.1 hx).trans hr.2
  have hB0 : volume (uToLie ⁻¹' Formalism.BasicNotions.ballU N 0 r) ≠ 0 :=
    (hBo.measure_pos volume ⟨0, zero_mem_B r hr.1⟩).ne'
  have hBt : volume (uToLie ⁻¹' Formalism.BasicNotions.ballU N 0 r) ≠ ⊤ :=
    ne_of_lt (lt_of_le_of_lt (measure_mono fun x hx => mem_ball_zero_iff.2 (norm_lt_of_mem x r hr.1 hx))
      measure_ball_lt_top)
  have hnum : μ {g | ∃ X ∈ Formalism.BasicNotions.ballU N 0 r, Formalism.BasicNotions.UpqT.mat g =
        NormedSpace.exp (X : Matrix (Fin N ⊕ Fin 0) (Fin N ⊕ Fin 0) ℂ)} =
      μ.map (iso N) {k : UNgrp N | ∃ x ∈ uToLie ⁻¹' Formalism.BasicNotions.ballU N 0 r, toM k = NormedSpace.exp (skMat x)} := by
    rw [map_iso_apply, toM_preimage_exp_ball_eq_upqT_exp_ball]
  have hden : (ENNReal.ofReal (2 ^ (N * (N - 1) / 2)) • Measure.map (uToLie (N := N)) volume)
      (Formalism.BasicNotions.ballU N 0 r) = ENNReal.ofReal (2 ^ (N * (N - 1) / 2)) * volume (uToLie ⁻¹' Formalism.BasicNotions.ballU N 0 r) := by
    rw [Measure.smul_apply, Measure.map_apply (continuous_uToLie N).measurable (isOpen_ballU N r).measurableSet,
      smul_eq_mul]
  obtain ⟨hup, hlo⟩ := hB _ hBo.measurableSet hBn
  simp only [Set.mem_Icc]
  rw [hnum, hden]
  have hκ0 : ENNReal.ofReal (2 ^ (N * (N - 1) / 2)) ≠ 0 := (ENNReal.ofReal_pos.2 hκ).ne'
  constructor
  · calc ENNReal.ofReal (1 / (2 ^ (N * (N - 1) / 2) * volU N)) - ε
        ≤ ENNReal.ofReal (1 / (2 ^ (N * (N - 1) / 2) * volU N)) - ENNReal.ofReal e := tsub_le_tsub_left he2.le _
      _ = ENNReal.ofReal (1 / (2 ^ (N * (N - 1) / 2) * volU N) - e) := (ENNReal.ofReal_sub _ he.le).symm
      _ ≤ _ := by
        rw [ENNReal.le_div_iff_mul_le (Or.inl (mul_ne_zero hκ0 hB0))
          (Or.inl (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hBt))]
        refine le_trans (le_of_eq ?_) hlo
        rw [← mul_assoc, ← ENNReal.ofReal_mul' hκ.le]
        congr 2
        field_simp
  · calc _ ≤ ENNReal.ofReal (1 / (2 ^ (N * (N - 1) / 2) * volU N) + e) := by
          refine ENNReal.div_le_of_le_mul (le_trans hup (le_of_eq ?_))
          rw [← mul_assoc, ← ENNReal.ofReal_mul (by positivity)]
          congr 2
          field_simp
      _ = ENNReal.ofReal (1 / (2 ^ (N * (N - 1) / 2) * volU N)) + ENNReal.ofReal e :=
          ENNReal.ofReal_add hcpos.le he.le
      _ ≤ _ := by gcongr

end PolarCoordinateComparison

end ReciprocityTheory.ChartRestriction.DS

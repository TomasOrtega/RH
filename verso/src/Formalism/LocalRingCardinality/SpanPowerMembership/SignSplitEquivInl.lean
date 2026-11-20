import Formalism.LocalRingCardinality.SpanPowerMembership.HaarDensityNeZero
import Formalism.RealPlaceAnalysis.RealPlaceTaylor.FrobeniusBoundOfMulNearOne

noncomputable section

namespace Formalism.BasicNotions.Examples₂.CD

open MeasureTheory Matrix Formalism.REAL Formalism.UG.P Topology
open scoped ENNReal NNReal

section One

variable {n P Q : ℕ} (ε : Fin n → Bool) (e : Fin P ⊕ Fin Q ≃ Fin n)
  (h1 : ∀ i, ε (e (Sum.inl i)) = true) (h2 : ∀ j, ε (e (Sum.inr j)) = false)

abbrev re : MM P Q ≃ₐ[ℂ] Matrix (Fin n) (Fin n) ℂ := Matrix.reindexAlgEquiv ℂ ℂ e

/- English proof (translation)
Simplify using `[re, Matrix.reindexAlgEquiv_apply, Matrix.conjTranspose_reindex]`.
-/
theorem re_star (X : MM P Q) : re e Xᴴ = (re e X)ᴴ := by
  simp [re, Matrix.reindexAlgEquiv_apply, Matrix.conjTranspose_reindex]

include h1 h2 in
/- English proof (translation)
Use extensionality with `i j`. Take `⟨a, rfl⟩` from `e.surjective i`. Take `⟨b, rfl⟩` from `e.surjective j`. Simplify using `only [re, Matrix.reindexAlgEquiv_apply, Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.symm_apply_apply, Jm, Matrix.diagonal_apply, e.injective.eq_iff, Formalism.UG.Jpq]`. Apply the tactic sequence `rcases a with a | a <;> rcases b with b | b <;>`.

Apply the tactic sequence `simp [Matrix.fromBlocks, Matrix.one_apply, h1, h2] <;> split_ifs <;> simp`.
-/
theorem re_J : re e (Formalism.UG.Jpq P Q) = Jm ε := by
  ext i j
  obtain ⟨a, rfl⟩ := e.surjective i
  obtain ⟨b, rfl⟩ := e.surjective j
  simp only [re, Matrix.reindexAlgEquiv_apply, Matrix.reindex_apply, Matrix.submatrix_apply,
    Equiv.symm_apply_apply, Jm, Matrix.diagonal_apply, e.injective.eq_iff, Formalism.UG.Jpq]
  rcases a with a | a <;> rcases b with b | b <;>
    simp [Matrix.fromBlocks, Matrix.one_apply, h1, h2] <;> split_ifs <;> simp

include h1 h2 in
/- English proof (translation)
Unfold `inUJ`. Rewrite using `[← re_J ε e h1 h2, ← re_star, ← map_mul, ← map_mul]`. Conclude with `(re e).injective.eq_iff`.
-/
theorem re_mem (M : MM P Q) : inUJ ε (re e M) ↔ Mᴴ * Formalism.UG.Jpq P Q * M = Formalism.UG.Jpq P Q := by
  unfold inUJ
  rw [← re_J ε e h1 h2, ← re_star, ← map_mul, ← map_mul]
  exact (re e).injective.eq_iff

def ofMatJ (h : Matrix (Fin n) (Fin n) ℂ) (hh : inUJ ε h) : UJ ε :=
  ⟨⟨h, Jm ε * hᴴ * Jm ε, mul_eq_one_comm.mp (coeMatrix_left_inv ε h hh), coeMatrix_left_inv ε h hh⟩, hh⟩

def ofMatU (h : MM P Q) (hh : hᴴ * Formalism.UG.Jpq P Q * h = Formalism.UG.Jpq P Q) : UpqT P Q :=
  (exists_of_mem P Q h hh).choose

/- English proof (translation)
The claim follows from `(exists_of_mem P Q h hh).choose_spec`.
-/
theorem mat_ofMatU (h : MM P Q) (hh : hᴴ * Formalism.UG.Jpq P Q * h = Formalism.UG.Jpq P Q) :
    UpqT.mat (ofMatU h hh) = h := (exists_of_mem P Q h hh).choose_spec

include h1 h2 in
/- English proof (translation)
The claim follows from `(re_mem ε e h1 h2 _).mp (by rw [AlgEquiv.apply_symm_apply]; exact a.2)`.
-/
theorem symm_mem (a : UJ ε) : ((re e).symm (coeMatrixAlt ε a))ᴴ * Formalism.UG.Jpq P Q * (re e).symm (coeMatrixAlt ε a) =
    Formalism.UG.Jpq P Q :=
  (re_mem ε e h1 h2 _).mp (by rw [AlgEquiv.apply_symm_apply]; exact a.2)

def phi : UpqT P Q ≃* UJ ε where
  toFun g := ofMatJ ε (re e (UpqT.mat g)) ((re_mem ε e h1 h2 _).mpr (mat_mem P Q g))
  invFun a := ofMatU ((re e).symm (coeMatrixAlt ε a)) (symm_mem ε e h1 h2 a)
  left_inv g := mat_injective P Q (by
    rw [mat_ofMatU]
    exact (re e).symm_apply_apply _)
  right_inv a := Subtype.ext (Units.ext
    ((congrArg (re e) (mat_ofMatU _ (symm_mem ε e h1 h2 a))).trans
      ((re e).apply_symm_apply _)))
  map_mul' g g' := Subtype.ext (Units.ext (map_mul (re e) _ _))

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem coe_phi (g : UpqT P Q) : coeMatrixAlt ε (phi ε e h1 h2 g) = Matrix.reindex e e (UpqT.mat g) := rfl

/- English proof (translation)
Rewrite using `[(isInducing_coeMatrix ε).continuous_iff]`. Establish `h : coeMatrixAlt ε ∘ (phi ε e h1 h2) = fun g => (UpqT.mat g).submatrix e.symm e.symm`. Use function extensionality and compare the values at `g`. Rewrite using `[Function.comp_apply, coe_phi, Matrix.reindex_apply]`. Rewrite using `[h]`.

Conclude with `(mat_cont P Q).matrix_submatrix _ _`.
-/
theorem phi_cont : Continuous (phi ε e h1 h2) := by
  rw [(isInducing_coeMatrix ε).continuous_iff]
  have h : coeMatrixAlt ε ∘ (phi ε e h1 h2) = fun g => (UpqT.mat g).submatrix e.symm e.symm := by
    funext g
    rw [Function.comp_apply, coe_phi, Matrix.reindex_apply]
  rw [h]
  exact (mat_cont P Q).matrix_submatrix _ _

/- English proof (translation)
Rewrite using `[(mat_inducing P Q).continuous_iff]`. Establish `h : UpqT.mat ∘ (phi ε e h1 h2).symm = fun a => (coeMatrixAlt ε a).submatrix e e`. Use function extensionality and compare the values at `a`. Rewrite using `[Function.comp_apply]`. Conclude with `mat_ofMatU _ (symm_mem ε e h1 h2 a)`.

Rewrite using `[h]`. Conclude with `(continuous_coeMatrix ε).matrix_submatrix _ _`.
-/
theorem phi_symm_cont : Continuous (phi ε e h1 h2).symm := by
  rw [(mat_inducing P Q).continuous_iff]
  have h : UpqT.mat ∘ (phi ε e h1 h2).symm = fun a => (coeMatrixAlt ε a).submatrix e e := by
    funext a
    rw [Function.comp_apply]
    exact mat_ofMatU _ (symm_mem ε e h1 h2 a)
  rw [h]
  exact (continuous_coeMatrix ε).matrix_submatrix _ _

/- English proof (translation)
Use extensionality with `g`. Simplify using `only [Set.mem_preimage, Set.mem_setOf_eq]`. Prove the components needed by the constructor for the conclusion. Introduce `hg`. Conclude with `⟨_, hg, coe_phi ε e h1 h2 g⟩`.

Introduce and unpack `⟨a, ha, hag⟩`. Establish `: a = phi ε e h1 h2 g` using `injective_coeMatrix ε (by rw [coe_phi]; exact hag)`. Rewrite using `[← this]`. Conclude with `ha`.
-/
theorem preimage_phi (A : Set (UJ ε)) : (phi ε e h1 h2) ⁻¹' A =
    {g | ∃ a ∈ A, ((a : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ) =
      Matrix.reindex e e (UpqT.mat g)} := by
  ext g
  simp only [Set.mem_preimage, Set.mem_setOf_eq]
  constructor
  · intro hg
    exact ⟨_, hg, coe_phi ε e h1 h2 g⟩
  · rintro ⟨a, ha, hag⟩
    have : a = phi ε e h1 h2 g := injective_coeMatrix ε (by rw [coe_phi]; exact hag)
    rw [← this]
    exact ha

def TR (P Q : ℕ) (R : ℝ) : Set (UpqT P Q) := {g | ∑ i, ∑ j, ‖UpqT.mat g i j‖ ^ 2 ≤ R}

/- English proof (translation)
Use extensionality with `g`. Simplify using `only [Set.mem_preimage, Set.mem_setOf_eq, TR]`. Establish `h : hsG (phi ε e h1 h2 g) = ∑ i, ∑ j, ‖UpqT.mat g i j‖ ^ 2` using `by show hs (coeMatrixAlt ε (phi ε e h1 h2 g)) = _`. Rewrite using `[coe_phi, hs]`. Use `(Fintype.sum_equiv e.symm _ _ fun i => ?_)` and prove the remaining obligations.

Conclude with `Fintype.sum_equiv e.symm _ _ fun j => by simp [Matrix.reindex_apply]`. Rewrite using `[h]`.
-/
theorem preimage_ball (R : ℝ) : (phi ε e h1 h2) ⁻¹' {a | hsG a ≤ R} = TR P Q R := by
  ext g
  simp only [Set.mem_preimage, Set.mem_setOf_eq, TR]
  have h : hsG (phi ε e h1 h2 g) = ∑ i, ∑ j, ‖UpqT.mat g i j‖ ^ 2 := by
    show hs (coeMatrixAlt ε (phi ε e h1 h2 g)) = _
    rw [coe_phi, hs]
    refine (Fintype.sum_equiv e.symm _ _ fun i => ?_)
    exact Fintype.sum_equiv e.symm _ _ fun j => by simp [Matrix.reindex_apply]
  rw [h]

end One

def rad (n : ℕ) : ℝ := hs (1 : Matrix (Fin n) (Fin n) ℂ) + 1

/- English proof (translation)
Establish `h : (hsG : UJ ε → ℝ) = fun g => ∑ i, ∑ j, ‖coeMatrixAlt ε g i j‖ ^ 2` using `rfl`. Rewrite using `[h]`. Use `continuous_finset_sum _ fun i _ => continuous_finset_sum _ fun j _ => ?_` and prove the remaining obligations. Conclude with `(((continuous_apply j).comp ((continuous_apply i).comp (continuous_coeMatrix ε))).norm).pow 2`.
-/
theorem hsG_cont {n : ℕ} (ε : Fin n → Bool) : Continuous (hsG : UJ ε → ℝ) := by
  have h : (hsG : UJ ε → ℝ) = fun g => ∑ i, ∑ j, ‖coeMatrixAlt ε g i j‖ ^ 2 := rfl
  rw [h]
  refine continuous_finset_sum _ fun i _ => continuous_finset_sum _ fun j _ => ?_
  exact (((continuous_apply j).comp ((continuous_apply i).comp (continuous_coeMatrix ε))).norm).pow 2

/- English proof (translation)
The claim follows from `(isClosed_le (hsG_cont ε) continuous_const).measurableSet`.
-/
theorem ball_meas {n : ℕ} (ε : Fin n → Bool) (R : ℝ) : MeasurableSet {a : UJ ε | hsG a ≤ R} :=
  (isClosed_le (hsG_cont ε) continuous_const).measurableSet

/- English proof (translation)
Establish `hopen : IsOpen {a : UJ ε | hsG a < rad n}` using `isOpen_lt (hsG_cont ε) continuous_const`. Establish `hne : ({a : UJ ε | hsG a < rad n}).Nonempty` using `⟨1, by show hs (((1 : UJ ε) : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ) < rad n`. Simplify using `[rad]⟩`. Establish `hpos : 0 < muG ε {a | hsG a < rad n}`. Unfold `muG`.

Conclude with `hopen.measure_pos _ hne`. Conclude with `(hpos.trans_le (measure_mono fun a (ha : hsG a < rad n) => ha.le)).ne'`.
-/
theorem ball_ne_zero {n : ℕ} (ε : Fin n → Bool) : muG ε {a | hsG a ≤ rad n} ≠ 0 := by
  have hopen : IsOpen {a : UJ ε | hsG a < rad n} := isOpen_lt (hsG_cont ε) continuous_const
  have hne : ({a : UJ ε | hsG a < rad n}).Nonempty := ⟨1, by
    show hs (((1 : UJ ε) : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ) < rad n
    simp [rad]⟩
  have hpos : 0 < muG ε {a | hsG a < rad n} := by
    unfold muG
    exact hopen.measure_pos _ hne
  exact (hpos.trans_le (measure_mono fun a (ha : hsG a < rad n) => ha.le)).ne'

/- English proof (translation)
Establish `hemb : Topology.IsClosedEmbedding (coeMatrixAlt ε)` using `⟨⟨isInducing_coeMatrix ε, injective_coeMatrix ε⟩, by rw [range_coeMatrix]; exact isClosed_pseudoUnitary ε⟩`. Use `set K : Set (Matrix (Fin n) (Fin n) ℂ) := {M | hs M ≤ rad n} with hK`. Establish `hKc : IsClosed K`. Use `isClosed_le ?_ continuous_const` and prove the remaining obligations. Use `continuous_finset_sum _ fun i _ => continuous_finset_sum _ fun j _ => ?_` and prove the remaining obligations.

Conclude with `(((continuous_apply j).comp (continuous_apply i)).norm).pow 2`. Establish `hKsub : K ⊆ Set.pi Set.univ fun _ => Set.pi Set.univ fun _ => Metric.closedBall (0 : ℂ) (Real.sqrt (rad n))`. Introduce `M hM i _ j _`. Rewrite using `[Metric.mem_closedBall, dist_zero_right]`. Use `Real.le_sqrt_of_sq_le (le_trans ?_ hM)` and prove the remaining obligations.

Combine the equalities or inequalities in the displayed calculation. Establish `hKcomp : IsCompact K` using `(isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => isCompact_closedBall _ _).of_isClosed_subset hKc hKsub`. Establish `hball : {a : UJ ε | hsG a ≤ rad n} = coeMatrixAlt ε ⁻¹' K` using `rfl`. Rewrite using `[hball]`. Unfold `muG`.

Conclude with `(hemb.isCompact_preimage hKcomp).measure_lt_top.ne`.
-/
theorem ball_ne_top {n : ℕ} (ε : Fin n → Bool) : muG ε {a | hsG a ≤ rad n} ≠ ⊤ := by

  have hemb : Topology.IsClosedEmbedding (coeMatrixAlt ε) :=
    ⟨⟨isInducing_coeMatrix ε, injective_coeMatrix ε⟩, by rw [range_coeMatrix]; exact isClosed_pseudoUnitary ε⟩
  set K : Set (Matrix (Fin n) (Fin n) ℂ) := {M | hs M ≤ rad n} with hK
  have hKc : IsClosed K := by
    refine isClosed_le ?_ continuous_const
    refine continuous_finset_sum _ fun i _ => continuous_finset_sum _ fun j _ => ?_
    exact (((continuous_apply j).comp (continuous_apply i)).norm).pow 2
  have hKsub : K ⊆ Set.pi Set.univ fun _ => Set.pi Set.univ fun _ =>
      Metric.closedBall (0 : ℂ) (Real.sqrt (rad n)) := by
    intro M hM i _ j _
    rw [Metric.mem_closedBall, dist_zero_right]
    refine Real.le_sqrt_of_sq_le (le_trans ?_ hM)
    calc ‖M i j‖ ^ 2 ≤ ∑ j', ‖M i j'‖ ^ 2 :=
          Finset.single_le_sum (f := fun j' => ‖M i j'‖ ^ 2) (fun _ _ => by positivity) (Finset.mem_univ j)
      _ ≤ ∑ i', ∑ j', ‖M i' j'‖ ^ 2 :=
          Finset.single_le_sum (f := fun i' => ∑ j', ‖M i' j'‖ ^ 2)
            (fun _ _ => Finset.sum_nonneg fun _ _ => by positivity) (Finset.mem_univ i)
  have hKcomp : IsCompact K :=
    (isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => isCompact_closedBall _ _).of_isClosed_subset
      hKc hKsub
  have hball : {a : UJ ε | hsG a ≤ rad n} = coeMatrixAlt ε ⁻¹' K := rfl
  rw [hball]
  unfold muG
  exact (hemb.isCompact_preimage hKcomp).measure_lt_top.ne

def nT {n : ℕ} (ε : Fin n → Bool) : ℕ := Fintype.card {i // ε i = true}
def nF {n : ℕ} (ε : Fin n → Bool) : ℕ := Fintype.card {i // ¬ ε i = true}

/- English proof (translation)
Establish `hc : Fintype.card (Fin P) = Fintype.card {i // ε i = true}`. Use `Fintype.card_congr (Equiv.ofBijective (fun i => ⟨e (Sum.inl i), h1 i⟩) ⟨?_, ?_⟩)` and prove the remaining obligations. Introduce `a b hab`. Use `congrArg Subtype.val hab` as an intermediate fact. Simplify using `using this`.

Introduce and unpack `⟨i, hi⟩`. Consider the cases of `hx : e.symm i with`. Consider the case `inl a => exact ⟨a, Subtype.ext (by simp [← hx])⟩`. Consider the case `inr b`. It suffices to derive a contradiction.

Establish `h` using `h2 b`. Rewrite `h` using `[← hx, e.apply_symm_apply]`. Simplify using `[hi] at h`. Simplify `hc` using `[nT]`.
-/
theorem eq_nT {n P Q : ℕ} (ε : Fin n → Bool) (e : Fin P ⊕ Fin Q ≃ Fin n)
    (h1 : ∀ i, ε (e (Sum.inl i)) = true) (h2 : ∀ j, ε (e (Sum.inr j)) = false) : P = nT ε := by
  have hc : Fintype.card (Fin P) = Fintype.card {i // ε i = true} := by
    refine Fintype.card_congr (Equiv.ofBijective (fun i => ⟨e (Sum.inl i), h1 i⟩) ⟨?_, ?_⟩)
    · intro a b hab
      have := congrArg Subtype.val hab
      simpa using this
    · rintro ⟨i, hi⟩
      cases hx : e.symm i with
      | inl a => exact ⟨a, Subtype.ext (by simp [← hx])⟩
      | inr b =>
        exfalso
        have h := h2 b
        rw [← hx, e.apply_symm_apply] at h
        simp [hi] at h
  simpa [nT] using hc

/- English proof (translation)
Establish `hc : Fintype.card (Fin Q) = Fintype.card {i // ¬ ε i = true}`. Use `Fintype.card_congr (Equiv.ofBijective (fun j => ⟨e (Sum.inr j), by simp [h2 j]⟩) ⟨?_, ?_⟩)` and prove the remaining obligations. Introduce `a b hab`. Use `congrArg Subtype.val hab` as an intermediate fact. Simplify using `using this`.

Introduce and unpack `⟨i, hi⟩`. Consider the cases of `hx : e.symm i with`. Consider the case `inl a`. It suffices to derive a contradiction. Establish `h` using `h1 a`.

Rewrite `h` using `[← hx, e.apply_symm_apply]`. Conclude with `hi h`. Consider the case `inr b => exact ⟨b, Subtype.ext (by simp [← hx])⟩`. Simplify `hc` using `[nF]`.
-/
theorem eq_nF {n P Q : ℕ} (ε : Fin n → Bool) (e : Fin P ⊕ Fin Q ≃ Fin n)
    (h1 : ∀ i, ε (e (Sum.inl i)) = true) (h2 : ∀ j, ε (e (Sum.inr j)) = false) : Q = nF ε := by
  have hc : Fintype.card (Fin Q) = Fintype.card {i // ¬ ε i = true} := by
    refine Fintype.card_congr (Equiv.ofBijective (fun j => ⟨e (Sum.inr j), by simp [h2 j]⟩) ⟨?_, ?_⟩)
    · intro a b hab
      have := congrArg Subtype.val hab
      simpa using this
    · rintro ⟨i, hi⟩
      cases hx : e.symm i with
      | inl a =>
        exfalso
        have h := h1 a
        rw [← hx, e.apply_symm_apply] at h
        exact hi h
      | inr b => exact ⟨b, Subtype.ext (by simp [← hx])⟩
  simpa [nF] using hc

def e0 {n : ℕ} (ε : Fin n → Bool) : Fin (nT ε) ⊕ Fin (nF ε) ≃ Fin n :=
  (Equiv.sumCongr (Fintype.equivFin {i // ε i = true}).symm
    (Fintype.equivFin {i // ¬ ε i = true}).symm).trans (Equiv.sumCompl fun i => ε i = true)

/- English proof (translation)
Simplify using `only [e0, Equiv.trans_apply, Equiv.sumCongr_apply, Sum.map_inl, Equiv.sumCompl_apply_inl]`. Conclude with `((Fintype.equivFin {i // ε i = true}).symm i).2`.
-/
theorem sign_split_equiv_inl {n : ℕ} (ε : Fin n → Bool) (i) : ε (e0 ε (Sum.inl i)) = true := by
  simp only [e0, Equiv.trans_apply, Equiv.sumCongr_apply, Sum.map_inl, Equiv.sumCompl_apply_inl]
  exact ((Fintype.equivFin {i // ε i = true}).symm i).2

/- English proof (translation)
Use `show ε (((Fintype.equivFin {i // ¬ ε i = true}).symm j : {i // ¬ ε i = true}) : Fin n) = false`. Simplify using `using ((Fintype.equivFin {i // ¬ ε i = true}).symm j).2`.
-/
theorem sign_split_equiv_inr {n : ℕ} (ε : Fin n → Bool) (j) : ε (e0 ε (Sum.inr j)) = false := by
  show ε (((Fintype.equivFin {i // ¬ ε i = true}).symm j : {i // ¬ ε i = true}) : Fin n) = false
  simpa using ((Fintype.equivFin {i // ¬ ε i = true}).symm j).2

variable (C : CDHaar)

def cdScaleOf (n : ℕ) (ε : Fin n → Bool) : ℝ≥0 :=
  (C.cd (nT ε) (nF ε) (TR (nT ε) (nF ε) (rad n)) / muG ε {a | hsG a ≤ rad n}).toNNReal

/- English proof (translation)
Take `rfl` from `eq_nT ε e h1 h2`. Take `rfl` from `eq_nF ε e h1 h2`. Use `haveI := C.haar (nT ε) (nF ε)`. Use `haveI : (muG ε).IsHaarMeasure := by unfold muG; infer_instance`. Use `haveI : ((C.cd (nT ε) (nF ε)).map (phi ε e h1 h2)).IsHaarMeasure := (phi ε e h1 h2).isHaarMeasure_map (C.cd (nT ε) (nF ε)) (phi_cont ε e h1 h2) (phi_symm_cont ε e h1 h2)`.

Use `set ν := (C.cd (nT ε) (nF ε)).map (phi ε e h1 h2) with hν_def`. Establish `hν : ν = Measure.haarScalarFactor ν (muG ε) • muG ε` using `Measure.isMulLeftInvariant_eq_smul ν (muG ε)`. Establish `hB : ν {a | hsG a ≤ rad n} = C.cd (nT ε) (nF ε) (TR (nT ε) (nF ε) (rad n))`. Rewrite using `[hν_def, Measure.map_apply (phi_cont ε e h1 h2).measurable (ball_meas ε _), preimage_ball]`. Establish `hscale : cdScaleOf C n ε = Measure.haarScalarFactor ν (muG ε)`.

Unfold `cdScaleOf`. Rewrite using `[← hB]`. Use `conv_lhs => rw [hν]`. Rewrite using `[Measure.coe_nnreal_smul_apply, ENNReal.mul_div_cancel_right (ball_ne_zero ε) (ball_ne_top ε), ENNReal.toNNReal_coe]`. Use `⟨?_, ?_⟩` and prove the remaining obligations.

Rewrite using `[hscale]`. Conclude with `Measure.haarScalarFactor_pos_of_isHaarMeasure _ _`. Rewrite using `[hscale]`. Conclude with `hν`.
-/
theorem cdScaleOf_spec {n P Q : ℕ} (ε : Fin n → Bool) (e : Fin P ⊕ Fin Q ≃ Fin n)
    (h1 : ∀ i, ε (e (Sum.inl i)) = true) (h2 : ∀ j, ε (e (Sum.inr j)) = false) :
    0 < cdScaleOf C n ε ∧ (C.cd P Q).map (phi ε e h1 h2) = cdScaleOf C n ε • muG ε := by
  obtain rfl := eq_nT ε e h1 h2
  obtain rfl := eq_nF ε e h1 h2
  haveI := C.haar (nT ε) (nF ε)
  haveI : (muG ε).IsHaarMeasure := by unfold muG; infer_instance
  haveI : ((C.cd (nT ε) (nF ε)).map (phi ε e h1 h2)).IsHaarMeasure :=
    (phi ε e h1 h2).isHaarMeasure_map (C.cd (nT ε) (nF ε)) (phi_cont ε e h1 h2)
      (phi_symm_cont ε e h1 h2)
  set ν := (C.cd (nT ε) (nF ε)).map (phi ε e h1 h2) with hν_def
  have hν : ν = Measure.haarScalarFactor ν (muG ε) • muG ε :=
    Measure.isMulLeftInvariant_eq_smul ν (muG ε)
  have hB : ν {a | hsG a ≤ rad n} = C.cd (nT ε) (nF ε) (TR (nT ε) (nF ε) (rad n)) := by
    rw [hν_def, Measure.map_apply (phi_cont ε e h1 h2).measurable (ball_meas ε _), preimage_ball]
  have hscale : cdScaleOf C n ε = Measure.haarScalarFactor ν (muG ε) := by
    unfold cdScaleOf
    rw [← hB]
    conv_lhs => rw [hν]
    rw [Measure.coe_nnreal_smul_apply, ENNReal.mul_div_cancel_right (ball_ne_zero ε) (ball_ne_top ε),
      ENNReal.toNNReal_coe]
  refine ⟨?_, ?_⟩
  · rw [hscale]
    exact Measure.haarScalarFactor_pos_of_isHaarMeasure _ _
  · rw [hscale]
    exact hν

/- English proof (translation)
The claim follows from `(cdScaleOf_spec C ε (e0 ε) (sign_split_equiv_inl ε) (sign_split_equiv_inr ε)).1`.
-/
theorem cdScaleOf_pos (n : ℕ) (ε : Fin n → Bool) : 0 < cdScaleOf C n ε :=
  (cdScaleOf_spec C ε (e0 ε) (sign_split_equiv_inl ε) (sign_split_equiv_inr ε)).1

/- English proof (translation)
Rewrite using `[← preimage_phi ε e h1 h2 A, ← Measure.map_apply (phi_cont ε e h1 h2).measurable hA, (cdScaleOf_spec C ε e h1 h2).2]`. Both sides reduce to the same expression.
-/
theorem cdScaleOf_tie (n : ℕ) (ε : Fin n → Bool) (P Q : ℕ) (e : Fin P ⊕ Fin Q ≃ Fin n)
    (h1 : ∀ i, ε (e (Sum.inl i)) = true) (h2 : ∀ j, ε (e (Sum.inr j)) = false)
    (A : Set (UJ ε)) (hA : MeasurableSet A) :
    ((cdScaleOf C n ε : ℝ≥0∞) • muG ε) A =
      C.cd P Q {g | ∃ a ∈ A, ((a : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ) =
        Matrix.reindex e e (UpqT.mat g)} := by
  rw [← preimage_phi ε e h1 h2 A, ← Measure.map_apply (phi_cont ε e h1 h2).measurable hA,
    (cdScaleOf_spec C ε e h1 h2).2]
  rfl

end Formalism.BasicNotions.Examples₂.CD

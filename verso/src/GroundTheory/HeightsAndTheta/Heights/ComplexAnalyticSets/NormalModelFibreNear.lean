import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Statements
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PNormalModelProper
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PModelLocalizationMaximalPoint
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial Filter Topology ComplexSets Metric

noncomputable section

namespace NormalModelFibre

variable {n : ℕ} {J : Ideal (MvPolynomial (Fin n) ℂ)} (M : IndefiniteRowSideFullHecke.ComplexSets.NormalModel J)

/- English proof (translation)
Introduce `f hf`. Establish `h1 : f ∈ M.ideal.comap (rename Sum.inl : MvPolynomial (Fin n) ℂ →ₐ[ℂ] MvPolynomial (Fin n ⊕ Fin M.m) ℂ)`. Rewrite using `[M.comap_eq]`. Conclude with `hf`. Establish `h0` using `hw _ (Ideal.mem_comap.1 h1)`.

Rewrite `h0` using `[eval_rename]`. Conclude with `h0`.
-/
theorem firstCoords_mem_zeroSet {w : Fin n ⊕ Fin M.m → ℂ} (hw : w ∈ IndefiniteRowSideFullHecke.ComplexSets.zeroSetIn M.ideal) :
    IndefiniteRowSideFullHecke.ComplexSets.firstCoords w ∈ zeroSet J := by
  intro f hf
  have h1 : f ∈ M.ideal.comap
      (rename Sum.inl : MvPolynomial (Fin n) ℂ →ₐ[ℂ] MvPolynomial (Fin n ⊕ Fin M.m) ℂ) := by
    rw [M.comap_eq]
    exact hf
  have h0 := hw _ (Ideal.mem_comap.1 h1)
  rw [eval_rename] at h0
  exact h0

/- English proof (translation)
Establish `: M.ideal.IsPrime` using `M.isPrime`. Establish `h0 : (0 : MvPolynomial (Fin n ⊕ Fin M.m) ℂ ⧸ M.ideal) ∉ normalModelSubmonoid M q`. Introduce `h`. Take `⟨f, hf, hf0⟩` from `Submonoid.mem_map.1 h`. Apply `(Ideal.mem_primeCompl_iff).1 hf` to reduce the goal to its premises.

Rewrite using `[RingHom.mem_ker]`. Establish `h1 : rename Sum.inl f ∈ M.ideal` using `Ideal.Quotient.eq_zero_iff_mem.1 hf0`. Establish `h2 : f ∈ J`. Rewrite using `[← M.comap_eq]`. Conclude with `h1`.

Conclude with `hq f h2`. Establish `hle` using `le_nonZeroDivisors_of_noZeroDivisors h0`. Establish `: Nontrivial (Localization (normalModelSubmonoid M q))` using `(IsLocalization.injective (M := normalModelSubmonoid M q) (S := Localization (normalModelSubmonoid M q)) hle).nontrivial`. Take `⟨P, hP⟩` from `Ideal.exists_maximal (Localization (normalModelSubmonoid M q))`. Take `⟨w, hw, hwq, -⟩` from `ModelLocalizationMaximalPoint.proof n J q M P hP`.

Conclude with `⟨w, hw, hwq⟩`.
-/
theorem exists_mem_fibre {q : Fin n → ℂ} (hq : q ∈ zeroSet J) :
    ∃ w ∈ IndefiniteRowSideFullHecke.ComplexSets.zeroSetIn M.ideal, IndefiniteRowSideFullHecke.ComplexSets.firstCoords w = q := by
  have : M.ideal.IsPrime := M.isPrime
  have h0 : (0 : MvPolynomial (Fin n ⊕ Fin M.m) ℂ ⧸ M.ideal) ∉ normalModelSubmonoid M q := by
    intro h
    obtain ⟨f, hf, hf0⟩ := Submonoid.mem_map.1 h
    apply (Ideal.mem_primeCompl_iff).1 hf
    rw [RingHom.mem_ker]
    have h1 : rename Sum.inl f ∈ M.ideal := Ideal.Quotient.eq_zero_iff_mem.1 hf0
    have h2 : f ∈ J := by
      rw [← M.comap_eq]
      exact h1
    exact hq f h2
  have hle := le_nonZeroDivisors_of_noZeroDivisors h0
  have : Nontrivial (Localization (normalModelSubmonoid M q)) :=
    (IsLocalization.injective (M := normalModelSubmonoid M q)
      (S := Localization (normalModelSubmonoid M q)) hle).nontrivial
  obtain ⟨P, hP⟩ := Ideal.exists_maximal (Localization (normalModelSubmonoid M q))
  obtain ⟨w, hw, hwq, -⟩ := ModelLocalizationMaximalPoint.proof n J q M P hP
  exact ⟨w, hw, hwq⟩

/- English proof (translation)
Use `choose P hPm hP using M.integral`. Establish `hroots : (Set.univ.pi fun i : Fin M.m => {a : ℂ | ((P i).map (eval q)).IsRoot a}).Finite` using `Set.Finite.pi fun i => Polynomial.finite_setOfPred_isRoot ((hPm i).map _).ne_zero`. Use `(hroots.image fun y : Fin M.m → ℂ => Sum.elim q y).subset ?_` and prove the remaining obligations. Introduce and unpack `w ⟨hw, rfl⟩`. Use `⟨fun i => w (Sum.inr i), fun i _ => ?_, ?_⟩` and prove the remaining obligations.

Conclude with `IndefiniteRowSideFullHecke.ComplexSets.isRoot_map_eval_of_mem_zeroSetIn hw i (P i) (hP i)`. Use function extensionality and compare the values at `s`. Apply the tactic sequence `rcases s with i | i <;> rfl`.
-/
theorem fibre_finite (q : Fin n → ℂ) :
    {w | w ∈ IndefiniteRowSideFullHecke.ComplexSets.zeroSetIn M.ideal ∧ IndefiniteRowSideFullHecke.ComplexSets.firstCoords w = q}.Finite := by
  choose P hPm hP using M.integral
  have hroots : (Set.univ.pi fun i : Fin M.m => {a : ℂ | ((P i).map (eval q)).IsRoot a}).Finite :=
    Set.Finite.pi fun i => Polynomial.finite_setOfPred_isRoot ((hPm i).map _).ne_zero
  refine (hroots.image fun y : Fin M.m → ℂ => Sum.elim q y).subset ?_
  rintro w ⟨hw, rfl⟩
  refine ⟨fun i => w (Sum.inr i), fun i _ => ?_, ?_⟩
  · exact IndefiniteRowSideFullHecke.ComplexSets.isRoot_map_eval_of_mem_zeroSetIn hw i (P i) (hP i)
  · funext s
    rcases s with i | i <;> rfl

/- English proof (translation)
Establish `h : IndefiniteRowSideFullHecke.ComplexSets.zeroSetIn M.ideal = ⋂ f ∈ M.ideal, {z | eval z f = 0}`. Use extensionality with `z`. Simplify using `[IndefiniteRowSideFullHecke.ComplexSets.zeroSetIn]`. Rewrite using `[h]`. Conclude with `isClosed_biInter fun f _ => isClosed_eq (MvPolynomial.continuous_eval f) continuous_const`.
-/
theorem isClosed_zeroSetIn : IsClosed (IndefiniteRowSideFullHecke.ComplexSets.zeroSetIn M.ideal) := by
  have h : IndefiniteRowSideFullHecke.ComplexSets.zeroSetIn M.ideal = ⋂ f ∈ M.ideal, {z | eval z f = 0} := by
    ext z
    simp [IndefiniteRowSideFullHecke.ComplexSets.zeroSetIn]
  rw [h]
  exact isClosed_biInter fun f _ => isClosed_eq (MvPolynomial.continuous_eval f) continuous_const

/- English proof (translation)
The claim follows from `continuous_pi fun _ => continuous_apply _`.
-/
theorem continuous_firstCoords : Continuous (IndefiniteRowSideFullHecke.ComplexSets.firstCoords (n := n) (m := M.m)) :=
  continuous_pi fun _ => continuous_apply _

/- English proof (translation)
Use `set K : Set (Fin n ⊕ Fin M.m → ℂ) := {w | w ∈ IndefiniteRowSideFullHecke.ComplexSets.zeroSetIn M.ideal ∧ IndefiniteRowSideFullHecke.ComplexSets.firstCoords w ∈ closedBall q 1} ∩ Uᶜ with hKdef`. Establish `hKb : Bornology.IsBounded K` using `(IndefiniteRowSideFullHecke.ComplexSets.NormalModelProper.proof n J M (closedBall q 1) isBounded_closedBall).subset Set.inter_subset_left`. Establish `hKc : IsClosed K` using `((isClosed_zeroSetIn M).inter (isClosed_closedBall.preimage (continuous_firstCoords M))).inter hU.isClosed_compl`. Establish `hK : IsCompact K` using `isCompact_of_isClosed_isBounded hKc hKb`. Establish `hKi : IsClosed (IndefiniteRowSideFullHecke.ComplexSets.firstCoords '' K)` using `(hK.image (continuous_firstCoords M)).isClosed`.

Establish `hq : q ∉ IndefiniteRowSideFullHecke.ComplexSets.firstCoords '' K`. Introduce and unpack `⟨w, ⟨⟨hw, -⟩, hwU⟩, hwq⟩`. Conclude with `hwU (hfib w hw hwq)`. Use `⟨closedBall q 1 ∩ (IndefiniteRowSideFullHecke.ComplexSets.firstCoords '' K)ᶜ, inter_mem (closedBall_mem_nhds q one_pos) (hKi.isOpen_compl.mem_nhds hq), ?_⟩` and prove the remaining obligations. Introduce `w hw hwN`.

Assume the negation of the conclusion as `hwU`. Conclude with `hwN.2 ⟨w, ⟨⟨hw, hwN.1⟩, hwU⟩, rfl⟩`.
-/
theorem eventually_mem_of_fibre_subset {q : Fin n → ℂ} {U : Set (Fin n ⊕ Fin M.m → ℂ)} (hU : IsOpen U)
    (hfib : ∀ w ∈ IndefiniteRowSideFullHecke.ComplexSets.zeroSetIn M.ideal, IndefiniteRowSideFullHecke.ComplexSets.firstCoords w = q → w ∈ U) :
    ∃ N ∈ 𝓝 q, ∀ w ∈ IndefiniteRowSideFullHecke.ComplexSets.zeroSetIn M.ideal, IndefiniteRowSideFullHecke.ComplexSets.firstCoords w ∈ N → w ∈ U := by
  set K : Set (Fin n ⊕ Fin M.m → ℂ) := {w | w ∈ IndefiniteRowSideFullHecke.ComplexSets.zeroSetIn M.ideal ∧
    IndefiniteRowSideFullHecke.ComplexSets.firstCoords w ∈ closedBall q 1} ∩ Uᶜ with hKdef
  have hKb : Bornology.IsBounded K :=
    (IndefiniteRowSideFullHecke.ComplexSets.NormalModelProper.proof n J M (closedBall q 1) isBounded_closedBall).subset
      Set.inter_subset_left
  have hKc : IsClosed K :=
    ((isClosed_zeroSetIn M).inter (isClosed_closedBall.preimage (continuous_firstCoords M))).inter
      hU.isClosed_compl
  have hK : IsCompact K := isCompact_of_isClosed_isBounded hKc hKb
  have hKi : IsClosed (IndefiniteRowSideFullHecke.ComplexSets.firstCoords '' K) :=
    (hK.image (continuous_firstCoords M)).isClosed
  have hq : q ∉ IndefiniteRowSideFullHecke.ComplexSets.firstCoords '' K := by
    rintro ⟨w, ⟨⟨hw, -⟩, hwU⟩, hwq⟩
    exact hwU (hfib w hw hwq)
  refine ⟨closedBall q 1 ∩ (IndefiniteRowSideFullHecke.ComplexSets.firstCoords '' K)ᶜ,
    inter_mem (closedBall_mem_nhds q one_pos) (hKi.isOpen_compl.mem_nhds hq), ?_⟩
  intro w hw hwN
  by_contra hwU
  exact hwN.2 ⟨w, ⟨⟨hw, hwN.1⟩, hwU⟩, rfl⟩

end NormalModelFibre

end

end GroundTheory.Heights₂.Heights

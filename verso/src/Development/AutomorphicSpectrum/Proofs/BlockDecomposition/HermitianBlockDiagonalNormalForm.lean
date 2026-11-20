import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MeanTransport
import Development.AbelianVarietyTheory.Proofs.HermitianTraceForms.ExistsOrthogonalBasisDotProductApplyEq
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.StdUnn GlobalTheory.StdUnn.Model PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS PositivityTheory.Rg.Rsw GlobalTheory.CompanionTheory.PcFc
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.PcFc

section Field
variable {E : Type} [Field E] {c : E →+* E}

/- English proof (translation)
Take `⟨P, d, hP, hPG, hd, -⟩` from `GlobalTheory.HermDiag.exists_congr_diagonal h2 hc hG`. Establish `hQ : (P.map c).det ≠ 0`. Rewrite using `[← RingHom.mapMatrix_apply, ← RingHom.map_det]`. Conclude with `(map_ne_zero c).mpr hP`. Establish `hrk : (Matrix.diagonal d).rank = G.rank`.

Rewrite using `[← hPG, Matrix.rank_mul_eq_left_of_isUnit_det _ _ (isUnit_iff_ne_zero.mpr hQ), Matrix.rank_mul_eq_right_of_isUnit_det _ _ (by rw [Matrix.det_transpose]; exact isUnit_iff_ne_zero.mpr hP)]`. Rewrite `hrk` using `[Matrix.rank_diagonal, Fintype.card_subtype]`. Take `⟨T, hTS, hTc⟩` from `Finset.exists_subset_card_eq (hr.trans hrk.ge)`. Set `e : Fin ρ ⊕ Fin p ≃ Fin n` to `finSumFinEquiv.trans (finCongr hn)`. Set `A : Finset (Fin n)` to `Finset.univ.map ⟨fun i : Fin ρ => e (Sum.inl i), fun i j h => Sum.inl_injective (e.injective h)⟩`.

Establish `hAc : A.card = ρ` using `by simp [A]`. Set `e' : {x // x ∈ A} ≃ {x // x ∈ T}` to `Fintype.equivOfCardEq (by rw [Fintype.card_coe, Fintype.card_coe, hAc, hTc])`. Set `σ : Equiv.Perm (Fin n)` to `e'.extendSubtype`. Establish `hσ : ∀ i : Fin ρ, d (σ (e (Sum.inl i))) ≠ 0`. Introduce `i`.

Establish `hm : σ (e (Sum.inl i)) ∈ T` using `Equiv.extendSubtype_mem e' _ (Finset.mem_map.mpr ⟨i, Finset.mem_univ _, rfl⟩)`. Simplify using `using hTS hm`. Use `⟨(P.map c).submatrix id σ, fun i => d (σ (e (Sum.inl i))), fun j => d (σ (e (Sum.inr j))), ?_, ?_, fun i => hd _, fun j => hd _, hσ⟩` and prove the remaining obligations. Rewrite using `[Matrix.det_permute']`. Use `mul_ne_zero ?_ hQ` and prove the remaining obligations.

Apply the tactic sequence `rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h <;> simp [h]`. Establish `hmc : (((P.map c).submatrix id σ).map c).transpose * G * (P.map c).submatrix id σ = (P.transpose * G * P.map c).submatrix σ σ`. Use extensionality with `i j`. Simplify using `only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, Matrix.submatrix_apply, id, hc]`. Rewrite using `[hmc, hPG, Matrix.submatrix_diagonal_equiv]`.

Unfold `PositivityTheory.Rg.Rsw.bl`. Rewrite using `[Matrix.fromBlocks_diagonal, Matrix.submatrix_diagonal_equiv]`. Use `congr 1`. Use function extensionality and compare the values at `x`. Take `⟨y, rfl⟩` from `e.surjective x`.

Apply the tactic sequence `cases y <;> simp [e]`.
-/
theorem exists_congr_diag_rank (h2 : (2 : E) ≠ 0) (hc : ∀ t, c (c t) = t) {n ρ p : ℕ} (hn : ρ + p = n)
    {G : Matrix (Fin n) (Fin n) E} (hG : ∀ a b, c (G a b) = G b a) (hr : ρ ≤ G.rank) :
    ∃ (a : Matrix (Fin n) (Fin n) E) (d₁ : Fin ρ → E) (d₂ : Fin p → E), a.det ≠ 0 ∧
      (a.map c).transpose * G * a = bl hn (Matrix.diagonal d₁) 0 0 (Matrix.diagonal d₂) ∧
      (∀ i, c (d₁ i) = d₁ i) ∧ (∀ i, c (d₂ i) = d₂ i) ∧ ∀ i, d₁ i ≠ 0 := by
  classical
  obtain ⟨P, d, hP, hPG, hd, -⟩ := GlobalTheory.HermDiag.exists_congr_diagonal h2 hc hG
  have hQ : (P.map c).det ≠ 0 := by
    rw [← RingHom.mapMatrix_apply, ← RingHom.map_det]
    exact (map_ne_zero c).mpr hP
  have hrk : (Matrix.diagonal d).rank = G.rank := by
    rw [← hPG, Matrix.rank_mul_eq_left_of_isUnit_det _ _ (isUnit_iff_ne_zero.mpr hQ),
      Matrix.rank_mul_eq_right_of_isUnit_det _ _ (by rw [Matrix.det_transpose]; exact isUnit_iff_ne_zero.mpr hP)]
  rw [Matrix.rank_diagonal, Fintype.card_subtype] at hrk
  obtain ⟨T, hTS, hTc⟩ := Finset.exists_subset_card_eq (hr.trans hrk.ge)
  let e : Fin ρ ⊕ Fin p ≃ Fin n := finSumFinEquiv.trans (finCongr hn)
  let A : Finset (Fin n) := Finset.univ.map ⟨fun i : Fin ρ => e (Sum.inl i), fun i j h => Sum.inl_injective (e.injective h)⟩
  have hAc : A.card = ρ := by simp [A]
  let e' : {x // x ∈ A} ≃ {x // x ∈ T} :=
    Fintype.equivOfCardEq (by rw [Fintype.card_coe, Fintype.card_coe, hAc, hTc])
  let σ : Equiv.Perm (Fin n) := e'.extendSubtype
  have hσ : ∀ i : Fin ρ, d (σ (e (Sum.inl i))) ≠ 0 := by
    intro i
    have hm : σ (e (Sum.inl i)) ∈ T := Equiv.extendSubtype_mem e' _ (Finset.mem_map.mpr ⟨i, Finset.mem_univ _, rfl⟩)
    simpa using hTS hm
  refine ⟨(P.map c).submatrix id σ, fun i => d (σ (e (Sum.inl i))), fun j => d (σ (e (Sum.inr j))), ?_, ?_,
    fun i => hd _, fun j => hd _, hσ⟩
  · rw [Matrix.det_permute']
    refine mul_ne_zero ?_ hQ
    rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h <;> simp [h]
  · have hmc : (((P.map c).submatrix id σ).map c).transpose * G * (P.map c).submatrix id σ
        = (P.transpose * G * P.map c).submatrix σ σ := by
      ext i j
      simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, Matrix.submatrix_apply, id, hc]
    rw [hmc, hPG, Matrix.submatrix_diagonal_equiv]
    unfold PositivityTheory.Rg.Rsw.bl
    rw [Matrix.fromBlocks_diagonal, Matrix.submatrix_diagonal_equiv]
    congr 1
    funext x
    obtain ⟨y, rfl⟩ := e.surjective x
    cases y <;> simp [e]

end Field

/- English proof (translation)
Take `⟨G, hG⟩` from `β`. Establish `hc : ∀ t : D.host.E, D.sp.cm.sig.toRingHom (D.sp.cm.sig.toRingHom t) = t` using `fun t => star_star t`. Take `⟨a, d₁, d₂, ha, hEq, hd₁, hd₂, hne⟩` from `exists_congr_diag_rank (c := D.sp.cm.sig.toRingHom) two_ne_zero hc hn (G := G) (fun i j => congrFun (congrFun hG j) i) hr`. Establish `hdiag : ∀ {m : ℕ} (d : Fin m → D.host.E), (∀ i, D.sp.cm.sig.toRingHom (d i) = d i) → ((Matrix.diagonal d).map ⇑D.sp.cm.sig).transpose = Matrix.diagonal d`. Introduce `m d hd`.

Rewrite using `[Matrix.diagonal_map (map_zero _), Matrix.diagonal_transpose]`. Use `congr 1`. Use function extensionality and compare the values at `i`. Conclude with `hd i`. Use `⟨Matrix.GeneralLinearGroup.mkOfDetNeZero a ha, ⟨Matrix.diagonal d₁, hdiag d₁ hd₁⟩, ⟨Matrix.diagonal d₂, hdiag d₂ hd₂⟩, ⟨Matrix.isDiag_diagonal _, ?_⟩, ?_⟩` and prove the remaining obligations.

Rewrite using `[Matrix.det_diagonal]`. Conclude with `Finset.prod_ne_zero_iff.mpr fun i _ => hne i`. Conclude with `Subtype.ext hEq`.
-/
theorem exists_cg_dsum {D : D7} {n ρ p : ℕ} (hn : ρ + p = n) (β : HermE D n) (hr : ρ ≤ β.1.rank) :
    ∃ (a : GL (Fin n) D.host.E) (b₀ : HermE D ρ) (β' : HermE D p), IsDiagInv b₀ ∧ cg a β = dsum hn b₀ β' := by
  obtain ⟨G, hG⟩ := β
  have hc : ∀ t : D.host.E, D.sp.cm.sig.toRingHom (D.sp.cm.sig.toRingHom t) = t := fun t => star_star t
  obtain ⟨a, d₁, d₂, ha, hEq, hd₁, hd₂, hne⟩ := exists_congr_diag_rank (c := D.sp.cm.sig.toRingHom) two_ne_zero hc hn
    (G := G) (fun i j => congrFun (congrFun hG j) i) hr
  have hdiag : ∀ {m : ℕ} (d : Fin m → D.host.E), (∀ i, D.sp.cm.sig.toRingHom (d i) = d i) →
      ((Matrix.diagonal d).map ⇑D.sp.cm.sig).transpose = Matrix.diagonal d := by
    intro m d hd
    rw [Matrix.diagonal_map (map_zero _), Matrix.diagonal_transpose]
    congr 1
    funext i
    exact hd i
  refine ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero a ha, ⟨Matrix.diagonal d₁, hdiag d₁ hd₁⟩,
    ⟨Matrix.diagonal d₂, hdiag d₂ hd₂⟩, ⟨Matrix.isDiag_diagonal _, ?_⟩, ?_⟩
  · rw [Matrix.det_diagonal]
    exact Finset.prod_ne_zero_iff.mpr fun i _ => hne i
  · exact Subtype.ext hEq

end GlobalTheory.CompanionTheory.PcFc

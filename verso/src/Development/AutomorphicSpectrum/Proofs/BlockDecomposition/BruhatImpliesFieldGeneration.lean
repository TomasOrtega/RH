import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.BlockMatrixMul
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsBlockMatrixTwoByTwoFinEq
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ComplementSubspace

noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.EC GlobalTheory.CompanionTheory.EisCovar
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.EisCovar.FieldGenPf

open GlobalTheory.CompanionTheory.BruhatCell (cT_mul cT_one cT_zero cT_neg cT_cT isUnit_det_cT cT_inv cT_blk4 cT_eId cT_extB
  eId_mul_eId exists_blockMatrixTwoByTwoFin_eq is_siegel_parabolic_block_iff unitary_mul blockMatrixTwoByTwoFin_injective)

variable {K : Type} [Field K]

/- English proof (translation)
The claim follows from `_root_.UpperTheory.Reformulated.B.ComplementSubspace.main U`.
-/
theorem exists_rows {n : ℕ} (U : Submodule K (Fin n → K)) :
    ∃ (c : Matrix (Fin (Module.finrank K U)) (Fin n) K) (a : Matrix (Fin n) (Fin n) K),
      (LinearIndependent K c ∧ Submodule.span K (Set.range c) = U) ∧ IsCompl c a :=
  _root_.UpperTheory.Reformulated.B.ComplementSubspace.main U

/- English proof (translation)
Take `⟨A, B, C, E, rfl⟩` from `exists_blockMatrixTwoByTwoFin_eq p`. Take `rfl` from `(is_siegel_parabolic_block_iff A B C E).1 hs`. Unfold `IsUnitary EC.Jm at hp`. Rewrite `hp` using `[cT_blk4, submatrix_fromBlocks_mul, submatrix_fromBlocks_mul]`. Take `⟨-, h2, h3, h4⟩` from `blockMatrixTwoByTwoFin_injective hp`.

Simplify using `only [cT_zero, Matrix.mul_zero, Matrix.zero_mul, Matrix.mul_one, Matrix.mul_neg, add_zero, zero_add, Matrix.neg_mul, neg_inj, neg_zero] at h2 h3 h4`. Establish `hEA : cT σ E * A = 1` using `h3`. Establish `hAE : cT σ A * E = 1` using `h2`. Establish `hA : IsUnit A.det` using `Matrix.isUnit_det_of_left_inverse hEA`. Establish `hinv : (cT σ A)⁻¹ = E` using `Matrix.inv_eq_right_inv hAE`.

Establish `hAE' : A * cT σ E = 1` using `mul_eq_one_comm.1 hEA`. Establish `hEA' : E * cT σ A = 1` using `mul_eq_one_comm.1 hAE`. Establish `hBE : cT σ B * E = cT σ E * B`. Use `h4` as an intermediate fact. Rewrite `this` using `[add_comm, ← sub_eq_add_neg, sub_eq_zero]`.

Conclude with `this`. Use `⟨B * cT σ A, A, ?_, hA, ?_⟩` and prove the remaining obligations. Rewrite using `[cT_mul, cT_cT σ hσ]`. Combine the equalities or inequalities in the displayed calculation. Unfold `nB mA`.

Rewrite using `[submatrix_fromBlocks_mul, hinv]`. Simplify using `[Matrix.mul_assoc, hAE]`.
-/
theorem siegel_factor (σ : K →+* K) (hσ : ∀ x, σ (σ x) = x) {n : ℕ}
    {p : Matrix (Fin (n + n)) (Fin (n + n)) K} (hp : IsUnitary σ (Jm K n) p) (hs : IsSiegelP p) :
    ∃ X A : Matrix (Fin n) (Fin n) K, cT σ X = X ∧ IsUnit A.det ∧ p = nB X * mA σ A := by
  obtain ⟨A, B, C, E, rfl⟩ := exists_blockMatrixTwoByTwoFin_eq p
  obtain rfl := (is_siegel_parabolic_block_iff A B C E).1 hs
  unfold IsUnitary EC.Jm at hp
  rw [cT_blk4, submatrix_fromBlocks_mul, submatrix_fromBlocks_mul] at hp
  obtain ⟨-, h2, h3, h4⟩ := blockMatrixTwoByTwoFin_injective hp
  simp only [cT_zero, Matrix.mul_zero, Matrix.zero_mul, Matrix.mul_one, Matrix.mul_neg, add_zero, zero_add,
    Matrix.neg_mul, neg_inj, neg_zero] at h2 h3 h4
  have hEA : cT σ E * A = 1 := h3
  have hAE : cT σ A * E = 1 := h2
  have hA : IsUnit A.det := Matrix.isUnit_det_of_left_inverse hEA
  have hinv : (cT σ A)⁻¹ = E := Matrix.inv_eq_right_inv hAE
  have hAE' : A * cT σ E = 1 := mul_eq_one_comm.1 hEA
  have hEA' : E * cT σ A = 1 := mul_eq_one_comm.1 hAE
  have hBE : cT σ B * E = cT σ E * B := by
    have := h4
    rw [add_comm, ← sub_eq_add_neg, sub_eq_zero] at this
    exact this
  refine ⟨B * cT σ A, A, ?_, hA, ?_⟩
  · rw [cT_mul, cT_cT σ hσ]
    calc A * cT σ B = A * cT σ B * (E * cT σ A) := by rw [hEA', Matrix.mul_one]
      _ = A * (cT σ B * E) * cT σ A := by simp only [Matrix.mul_assoc]
      _ = (A * cT σ E) * B * cT σ A := by rw [hBE]; simp only [Matrix.mul_assoc]
      _ = B * cT σ A := by rw [hAE', Matrix.one_mul]
  · unfold nB mA
    rw [submatrix_fromBlocks_mul, hinv]
    simp [Matrix.mul_assoc, hAE]

/- English proof (translation)
Establish `s1 : blk4 1 e 0 1 * blk4 0 1 (-1) 0 = blk4 (-e) 1 (-1) 0`. Rewrite using `[submatrix_fromBlocks_mul]`. Simplify using the standard rewrite rules. Establish `s2 : blk4 (-e) 1 (-1) 0 * blk4 1 e 0 1 = blk4 (-e) (1 - e) (-1) (-e)`. Rewrite using `[submatrix_fromBlocks_mul]`.

Simplify using `[he, sub_eq_add_neg, add_comm]`. Establish `s3 : blk4 (-e) (1 - e) (-1) (-e) * blk4 0 (-1) 1 0 = blk4 (1 - e) e (-e) 1`. Rewrite using `[submatrix_fromBlocks_mul]`. Simplify using the standard rewrite rules. Establish `s4 : blk4 (1 - e) e (-e) 1 * blk4 1 e 0 1 = blk4 (1 - e) e (-e) (1 - e)`.

Establish `h0 : (-e + 1) * e = 0` using `by simp [Matrix.add_mul, he]`. Rewrite using `[submatrix_fromBlocks_mul]`. Simplify using `[Matrix.sub_mul, he, h0, sub_eq_add_neg, add_comm]`. Rewrite using `[s1, s2, s3, s4]`.
-/
theorem wr_word {n : ℕ} (e : Matrix (Fin n) (Fin n) K) (he : e * e = e) :
    blk4 (1 - e) e (-e) (1 - e) =
      blk4 1 e 0 1 * blk4 0 1 (-1) 0 * blk4 1 e 0 1 * blk4 0 (-1) 1 0 * blk4 1 e 0 1 := by
  have s1 : blk4 1 e 0 1 * blk4 0 1 (-1) 0 = blk4 (-e) 1 (-1) 0 := by
    rw [submatrix_fromBlocks_mul]; simp
  have s2 : blk4 (-e) 1 (-1) 0 * blk4 1 e 0 1 = blk4 (-e) (1 - e) (-1) (-e) := by
    rw [submatrix_fromBlocks_mul]; simp [he, sub_eq_add_neg, add_comm]
  have s3 : blk4 (-e) (1 - e) (-1) (-e) * blk4 0 (-1) 1 0 = blk4 (1 - e) e (-e) 1 := by
    rw [submatrix_fromBlocks_mul]; simp
  have s4 : blk4 (1 - e) e (-e) 1 * blk4 1 e 0 1 = blk4 (1 - e) e (-e) (1 - e) := by
    have h0 : (-e + 1) * e = 0 := by simp [Matrix.add_mul, he]
    rw [submatrix_fromBlocks_mul]; simp [Matrix.sub_mul, he, h0, sub_eq_add_neg, add_comm]
  rw [s1, s2, s3, s4]

/- English proof (translation)
Establish `h : (cT σ (-1 : Matrix (Fin n) (Fin n) K))⁻¹ = -1`. Rewrite using `[cT_neg, cT_one]; exact Matrix.inv_eq_right_inv (by simp)`. Unfold `EC.Jm mA`. Rewrite using `[h, submatrix_fromBlocks_mul]`. Simplify using the standard rewrite rules.
-/
theorem Jm_mul_mA_neg (σ : K →+* K) (n : ℕ) :
    Jm K n * mA σ (-1 : Matrix (Fin n) (Fin n) K) = blk4 0 (-1) 1 0 := by
  have h : (cT σ (-1 : Matrix (Fin n) (Fin n) K))⁻¹ = -1 := by
    rw [cT_neg, cT_one]; exact Matrix.inv_eq_right_inv (by simp)
  unfold EC.Jm mA
  rw [h, submatrix_fromBlocks_mul]; simp

/- English proof (translation)
Unfold `IsUnitary at *`. Establish `h1 : cT σ r⁻¹ * cT σ r = 1`. Rewrite using `[cT_inv σ hd]`. Conclude with `Matrix.nonsing_inv_mul _ (isUnit_det_cT σ hd)`. Establish `h2 : r * r⁻¹ = 1` using `Matrix.mul_nonsing_inv _ hd`.

Combine the equalities or inequalities in the displayed calculation.
-/
theorem unitary_inv (σ : K →+* K) {N : ℕ} {J r : Matrix (Fin N) (Fin N) K} (hd : IsUnit r.det)
    (hr : IsUnitary σ J r) : IsUnitary σ J r⁻¹ := by
  unfold IsUnitary at *
  have h1 : cT σ r⁻¹ * cT σ r = 1 := by
    rw [cT_inv σ hd]; exact Matrix.nonsing_inv_mul _ (isUnit_det_cT σ hd)
  have h2 : r * r⁻¹ = 1 := Matrix.mul_nonsing_inv _ hd
  calc cT σ r⁻¹ * J * r⁻¹ = cT σ r⁻¹ * (cT σ r * J * r) * r⁻¹ := by rw [hr]
    _ = (cT σ r⁻¹ * cT σ r) * J * (r * r⁻¹) := by simp only [Matrix.mul_assoc]
    _ = J := by rw [h1, h2, Matrix.one_mul, Matrix.mul_one]

/- English proof (translation)
Introduce `hB K _ σ hσ h2 n T hmul hm hn hJ g hg hu`. Use `choose c a hc ha using exists_rows (K := K) (n := n)`. Take `⟨hrep, hex⟩` from `hB K σ hσ h2 n c hc a ha`. Take `⟨⟨U, b, hb⟩, hq, -⟩` from `hex g hg hu`. Take `⟨hrd, hru⟩` from `hrep U b hb`.

Establish `hq' : IsSiegelP (g * (repMat σ b (a U))⁻¹)` using `hq`. Establish `hTw : ∀ r, T (wr K n r)`. Introduce `r`. Establish `hne : ∀ r, T (nB (eId K n r))` using `fun r => hn _ (cT_eId σ n r)`. Establish `hJi : T (blk4 0 (-1) 1 0)`.

Rewrite using `[← Jm_mul_mA_neg σ n]`. Use `hmul _ _ hJ (hm _ ?_)` and prove the remaining obligations. Rewrite using `[Matrix.det_neg, Matrix.det_one]`. Simplify using the standard rewrite rules. Unfold `wr`.

Rewrite using `[wr_word _ (eId_mul_eId n r)]`. Conclude with `hmul _ _ (hmul _ _ (hmul _ _ (hmul _ _ (hne r) hJ) (hne r)) hJi) (hne r)`. Establish `hTrep : T (repMat σ b (a U))` using `hmul _ _ (hmul _ _ (hTw _) (hn _ (by rw [cT_extB, hb]))) (hm _ (ha U).1)`. Take `⟨X, A, hX, hA, hp⟩` from `siegel_factor σ hσ (unitary_mul σ hu (unitary_inv σ hrd hru)) hq'`. Establish `hTp : T (g * (repMat σ b (a U))⁻¹)`.

Rewrite using `[hp]`. Conclude with `hmul _ _ (hn X hX) (hm A hA)`. Establish `e : g = g * (repMat σ b (a U))⁻¹ * repMat σ b (a U)`. Rewrite using `[Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hrd, Matrix.mul_one]`. Rewrite using `[e]`.

Conclude with `hmul _ _ hTp hTrep`.
-/
theorem fieldGen_of_bruhat : Bruhat → ∀ (K : Type) [Field K] (σ : K →+* K), (∀ x, σ (σ x) = x) → (2 : K) ≠ 0 →
    ∀ n : ℕ, FieldGen K σ n := by
  intro hB K _ σ hσ h2 n T hmul hm hn hJ g hg hu
  choose c a hc ha using exists_rows (K := K) (n := n)
  obtain ⟨hrep, hex⟩ := hB K σ hσ h2 n c hc a ha
  obtain ⟨⟨U, b, hb⟩, hq, -⟩ := hex g hg hu
  obtain ⟨hrd, hru⟩ := hrep U b hb
  have hq' : IsSiegelP (g * (repMat σ b (a U))⁻¹) := hq
  have hTw : ∀ r, T (wr K n r) := by
    intro r
    have hne : ∀ r, T (nB (eId K n r)) := fun r => hn _ (cT_eId σ n r)
    have hJi : T (blk4 0 (-1) 1 0) := by
      rw [← Jm_mul_mA_neg σ n]
      refine hmul _ _ hJ (hm _ ?_)
      rw [Matrix.det_neg, Matrix.det_one]
      simp
    unfold wr
    rw [wr_word _ (eId_mul_eId n r)]
    exact hmul _ _ (hmul _ _ (hmul _ _ (hmul _ _ (hne r) hJ) (hne r)) hJi) (hne r)
  have hTrep : T (repMat σ b (a U)) :=
    hmul _ _ (hmul _ _ (hTw _) (hn _ (by rw [cT_extB, hb]))) (hm _ (ha U).1)
  obtain ⟨X, A, hX, hA, hp⟩ := siegel_factor σ hσ (unitary_mul σ hu (unitary_inv σ hrd hru)) hq'
  have hTp : T (g * (repMat σ b (a U))⁻¹) := by
    rw [hp]; exact hmul _ _ (hn X hX) (hm A hA)
  have e : g = g * (repMat σ b (a U))⁻¹ * repMat σ b (a U) := by
    rw [Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hrd, Matrix.mul_one]
  rw [e]
  exact hmul _ _ hTp hTrep

end GlobalTheory.CompanionTheory.EisCovar.FieldGenPf

import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BlockMatrixTwoByTwoFinTranspose
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Doubling GlobalTheory.MixModel GlobalTheory.SWLit
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (UA incM ratU)
open GlobalTheory.WeilM (Darboux symp schA thetaSum UG)
open GlobalTheory.SiegelFormula (coord)
open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SWLink

namespace GlobalTheory.SWLink.LeviChart
open GlobalTheory.StdUnn GlobalTheory.StdUnn.Model

/- English proof (translation)
Use `⟨(M.submatrix finSumFinEquiv finSumFinEquiv).toBlocks₁₁, (M.submatrix finSumFinEquiv finSumFinEquiv).toBlocks₁₂, (M.submatrix finSumFinEquiv finSumFinEquiv).toBlocks₂₁, (M.submatrix finSumFinEquiv finSumFinEquiv).toBlocks₂₂, ?_⟩` and prove the remaining obligations. Unfold `blk4`. Rewrite using `[Matrix.fromBlocks_toBlocks]`. Simplify using the standard rewrite rules.
-/
theorem exists_blockMatrixTwoByTwoFin_eq {R : Type} {n : ℕ} (M : Matrix (Fin (n + n)) (Fin (n + n)) R) : ∃ a b c d, M = blk4 a b c d := by
  refine ⟨(M.submatrix finSumFinEquiv finSumFinEquiv).toBlocks₁₁, (M.submatrix finSumFinEquiv finSumFinEquiv).toBlocks₁₂,
    (M.submatrix finSumFinEquiv finSumFinEquiv).toBlocks₂₁, (M.submatrix finSumFinEquiv finSumFinEquiv).toBlocks₂₂, ?_⟩
  unfold blk4
  rw [Matrix.fromBlocks_toBlocks]
  simp

/- English proof (translation)
Simplify using `[blk4]`.
-/
theorem submatrix_fromBlocks_levi {R : Type} {n : ℕ} (a b c d : Matrix (Fin n) (Fin n) R) :
    (blk4 a b c d).submatrix finSumFinEquiv finSumFinEquiv = Matrix.fromBlocks a b c d := by
  simp [blk4]

/- English proof (translation)
Take `⟨p, q, r, s, rfl⟩` from `exists_blockMatrixTwoByTwoFin_eq U`. Rewrite `h` using `[submatrix_fromBlocks_mul, submatrix_fromBlocks_mul]`. Take `⟨h1, -, h3, -⟩` from `blockMatrixTwoByTwoFin_injective h`. Simplify using `only [KeepsDiag, leviMat, submatrix_fromBlocks_levi, Matrix.toBlocks_fromBlocks₁₁, Matrix.toBlocks_fromBlocks₁₂, Matrix.toBlocks_fromBlocks₂₁, Matrix.toBlocks_fromBlocks₂₂] at hU ⊢`. Simplify using `only [mul_one, one_mul, neg_mul] at h1 h3`.

Establish `h4 : Z * c = 0` using `h2 _ (by`. Establish `: a + Z * c = a + -(Z * c)` using `by rw [← h1, ← h3, hU]`. Conclude with `eq_neg_iff_add_eq_zero.1 (add_left_cancel this))`. Use `⟨by rw [← one_mul c, ← hZ, mul_assoc, h4, mul_zero], by rw [h1, h4, add_zero]⟩` and prove the remaining obligations.
-/
theorem diag_blocks {R : Type} [CommRing R] {n : ℕ} (h2 : ∀ z : Matrix (Fin n) (Fin n) R, z + z = 0 → z = 0)
    {U : Matrix (Fin (n + n)) (Fin (n + n)) R} {Z Z' a b c d : Matrix (Fin n) (Fin n) R} (hZ : Z' * Z = 1)
    (h : U * blk4 1 Z 1 (-Z) = blk4 1 Z 1 (-Z) * blk4 a b c d) (hU : KeepsDiag finSumFinEquiv U) :
    c = 0 ∧ a = leviMat finSumFinEquiv U := by
  obtain ⟨p, q, r, s, rfl⟩ := exists_blockMatrixTwoByTwoFin_eq U
  rw [submatrix_fromBlocks_mul, submatrix_fromBlocks_mul] at h
  obtain ⟨h1, -, h3, -⟩ := blockMatrixTwoByTwoFin_injective h
  simp only [KeepsDiag, leviMat, submatrix_fromBlocks_levi, Matrix.toBlocks_fromBlocks₁₁, Matrix.toBlocks_fromBlocks₁₂,
    Matrix.toBlocks_fromBlocks₂₁, Matrix.toBlocks_fromBlocks₂₂] at hU ⊢
  simp only [mul_one, one_mul, neg_mul] at h1 h3
  have h4 : Z * c = 0 := h2 _ (by
    have : a + Z * c = a + -(Z * c) := by rw [← h1, ← h3, hU]
    exact eq_neg_iff_add_eq_zero.1 (add_left_cancel this))
  refine ⟨by rw [← one_mul c, ← hZ, mul_assoc, h4, mul_zero], by rw [h1, h4, add_zero]⟩

/- English proof (translation)
Take `⟨p, q, r, s, rfl⟩` from `exists_blockMatrixTwoByTwoFin_eq U`. Rewrite `h` using `[submatrix_fromBlocks_mul, submatrix_fromBlocks_mul]`. Take `⟨-, h1, -, h3⟩` from `blockMatrixTwoByTwoFin_injective h`. Establish `h4 : p * Z + q * -Z = -(r * Z + s * -Z)`. Use `Matrix.ext_of_mulVec_single fun j => ?_` and prove the remaining obligations.

Use `hU _ ((pairVec_mem_antiSub finSumFinEquiv).2 (neg_neg _).symm : pairVec finSumFinEquiv (Z *ᵥ Pi.single j 1) (-(Z *ᵥ Pi.single j 1)) ∈ _)` as an intermediate fact. Rewrite `this` using `[mulVec_pairVec, pairVec_mem_antiSub, submatrix_fromBlocks_levi]`. Simplify using `only [Matrix.toBlocks_fromBlocks₁₁, Matrix.toBlocks_fromBlocks₁₂, Matrix.toBlocks_fromBlocks₂₁, Matrix.toBlocks_fromBlocks₂₂, ← Matrix.neg_mulVec, Matrix.mulVec_mulVec, ← Matrix.add_mulVec] at this`. Conclude with `this`. Rewrite `h4` using `[h1, h3]`.

Simplify using `only [one_mul, neg_mul] at h4`. Use `h2 _ ?_` and prove the remaining obligations. Use `eq_neg_iff_add_eq_zero.1 h4` as an intermediate fact. Rewrite using `[← this]`. Normalize the expressions using the abelian group laws.
-/
theorem anti_blocks {R : Type} [CommRing R] {n : ℕ} (h2 : ∀ z : Matrix (Fin n) (Fin n) R, z + z = 0 → z = 0)
    {U : Matrix (Fin (n + n)) (Fin (n + n)) R} {Z a b c d : Matrix (Fin n) (Fin n) R}
    (h : U * blk4 1 Z 1 (-Z) = blk4 1 Z 1 (-Z) * blk4 a b c d)
    (hU : ∀ w ∈ antiSub R finSumFinEquiv, U *ᵥ w ∈ antiSub R finSumFinEquiv) : b = 0 := by
  obtain ⟨p, q, r, s, rfl⟩ := exists_blockMatrixTwoByTwoFin_eq U
  rw [submatrix_fromBlocks_mul, submatrix_fromBlocks_mul] at h
  obtain ⟨-, h1, -, h3⟩ := blockMatrixTwoByTwoFin_injective h
  have h4 : p * Z + q * -Z = -(r * Z + s * -Z) := by
    refine Matrix.ext_of_mulVec_single fun j => ?_
    have := hU _ ((pairVec_mem_antiSub finSumFinEquiv).2
      (neg_neg _).symm : pairVec finSumFinEquiv (Z *ᵥ Pi.single j 1) (-(Z *ᵥ Pi.single j 1)) ∈ _)
    rw [mulVec_pairVec, pairVec_mem_antiSub, submatrix_fromBlocks_levi] at this
    simp only [Matrix.toBlocks_fromBlocks₁₁, Matrix.toBlocks_fromBlocks₁₂,
      Matrix.toBlocks_fromBlocks₂₁, Matrix.toBlocks_fromBlocks₂₂, ← Matrix.neg_mulVec, Matrix.mulVec_mulVec,
      ← Matrix.add_mulVec] at this
    exact this
  rw [h1, h3] at h4
  simp only [one_mul, neg_mul] at h4
  refine h2 _ ?_
  have := eq_neg_iff_add_eq_zero.1 h4
  rw [← this]; abel

/- English proof (translation)
Rewrite using `[← one_mul d, ← h1, mul_assoc, h2, mul_one]`.
-/
theorem inv_cancel {M : Type} [Monoid M] {x y d : M} (h1 : y * x = 1) (h2 : x * d = 1) : d = y := by
  rw [← one_mul d, ← h1, mul_assoc, h2, mul_one]

variable {D : D7} {n : ℕ}

/- English proof (translation)
Rewrite using `[← adj_mul]`. Simplify using `[adj_one]`.
-/
theorem adj_inv_mul (a : GL (Fin n) (AE D)) : (adj (a⁻¹).1 : Mx D n n) * adj a.1 = 1 := by
  rw [← adj_mul]; simp [adj_one]

/- English proof (translation)
Establish `h : adj (mat g) * JR (AF D.host.F) (Jst D n) * mat g = JR (AF D.host.F) (Jst D n)` using `g.2`. Rewrite `h` using `[JR_Jst, hg]`. Simplify using `only [adelicConjTranspose_blockMatrixTwoByTwoFin, submatrix_fromBlocks_mul, adj_zero, mul_zero, zero_mul, mul_one, add_zero, zero_add] at h`. Conclude with `(blockMatrixTwoByTwoFin_injective h).2.1`.
-/
theorem adj_mul_eq_one {g : G D n} {a b d : Mx D n n} (hg : mat g = blk4 a b 0 d) : adj a * d = 1 := by
  have h : adj (mat g) * JR (AF D.host.F) (Jst D n) * mat g = JR (AF D.host.F) (Jst D n) := g.2
  rw [JR_Jst, hg] at h
  simp only [adelicConjTranspose_blockMatrixTwoByTwoFin, submatrix_fromBlocks_mul, adj_zero, mul_zero, zero_mul, mul_one, add_zero, zero_add] at h
  exact (blockMatrixTwoByTwoFin_injective h).2.1

/- English proof (translation)
Take `⟨Z, hZ, hT⟩` from `hT`. Rewrite `hZ` using `[one_smul, ← Matrix.smul_mul]`. Establish `h1 : (rat ((2 : D.host.E) • J) : Mx D n n) * cj (rat Z) = 1` using `by rw [cj_rat, ← rat_mul, hZ, rat_one]`. Establish `h2 : (cj (rat ((2 : D.host.E) • J)) : Mx D n n) * rat Z = 1`. Use `congrArg cj h1` as an intermediate fact.

Rewrite `this` using `[cj_mul, cj_cj, cj_one]`. Then use the resulting hypothesis. Conclude with `⟨rat Z, _, h2, by rw [hT, blk_eq, rat_fromBlocks_map, rat_one, rat_neg]⟩`.
-/
theorem rat_witt {J : Matrix (Fin n) (Fin n) D.host.E} {T : GL (Fin (n + n)) D.host.E}
    (hT : IsWittBasis D.sp.cm.sig J 1 T) :
    ∃ Z Z' : Mx D n n, Z' * Z = 1 ∧ (rat T.1 : Mx D (n + n) (n + n)) = blk4 1 Z 1 (-Z) := by
  obtain ⟨Z, hZ, hT⟩ := hT
  rw [one_smul, ← Matrix.smul_mul] at hZ
  have h1 : (rat ((2 : D.host.E) • J) : Mx D n n) * cj (rat Z) = 1 := by rw [cj_rat, ← rat_mul, hZ, rat_one]
  have h2 : (cj (rat ((2 : D.host.E) • J)) : Mx D n n) * rat Z = 1 := by
    have := congrArg cj h1
    rwa [cj_mul, cj_cj, cj_one] at this
  exact ⟨rat Z, _, h2, by rw [hT, blk_eq, rat_fromBlocks_map, rat_one, rat_neg]⟩

/- English proof (translation)
Substitute `e` using the available equality. Rewrite using `[h, hb, inv_cancel (adj_inv_mul a) hd]`.
-/
theorem levi_form {M : Mx D (n + n) (n + n)} {x b d : Mx D n n} (a : GL (Fin n) (AE D)) (e : x = a.1)
    (h : M = blk4 x b 0 d) (hb : b = 0) (hd : adj x * d = 1) : M = blk4 a.1 0 0 (adj (a⁻¹).1) := by
  subst e
  rw [h, hb, inv_cancel (adj_inv_mul a) hd]

section
variable {J₂ : Matrix (Fin (n + n)) (Fin (n + n)) D.host.E} {T : GL (Fin (n + n)) D.host.E} {κ : UD D J₂ ≃* G D n}
  {J : Matrix (Fin n) (Fin n) D.host.E}

/- English proof (translation)
Take `⟨Z, Z', hZ, hT⟩` from `rat_witt hT`. Take `⟨a, b, c, d, h⟩` from `exists_blockMatrixTwoByTwoFin_eq (mat (κ g))`. Establish `h1` using `hκ.mul_eq g`. Rewrite `h1` using `[hT, h]`. Establish `h2 : ∀ z : Mx D n n, z + z = 0 → z = 0` using `fun z hz => eq_zero_of_add_self hz`.

Take `⟨hc, ha⟩` from `diag_blocks (R := AE D) h2 hZ h1 hk`. Establish `h3` using `anti_blocks (R := AE D) h2 h1`. Rewrite `h` using `[hc, ha]`. Conclude with `⟨b, d, h, adj_mul_eq_one h, h3⟩`.
-/
theorem siegel_blocks (hκ : IsChartW T κ) (hT : IsWittBasis D.sp.cm.sig J 1 T) {g : UD D J₂}
    (hk : KeepsDiag finSumFinEquiv (umat g)) : ∃ b d : Mx D n n,
      mat (κ g) = blk4 (leviMat finSumFinEquiv (umat g)) b 0 d ∧ adj (leviMat finSumFinEquiv (umat g)) * d = 1 ∧
      ((∀ w ∈ antiSub (AE D) finSumFinEquiv, umat g *ᵥ w ∈ antiSub (AE D) finSumFinEquiv) → b = 0) := by
  obtain ⟨Z, Z', hZ, hT⟩ := rat_witt hT
  obtain ⟨a, b, c, d, h⟩ := exists_blockMatrixTwoByTwoFin_eq (mat (κ g))
  have h1 := hκ.mul_eq g
  rw [hT, h] at h1
  have h2 : ∀ z : Mx D n n, z + z = 0 → z = 0 := fun z hz => eq_zero_of_add_self hz
  obtain ⟨hc, ha⟩ := diag_blocks (R := AE D) h2 hZ h1 hk
  have h3 := anti_blocks (R := AE D) h2 h1
  rw [hc, ha] at h
  exact ⟨b, d, h, adj_mul_eq_one h, h3⟩

/- English proof (translation)
Take `⟨hp1, hp2⟩` from `Subgroup.mem_inf.1 hp`. Take `⟨b, d, h, hd, hb⟩` from `siegel_blocks hκ hT (g := g) (mem_siegelOf.1 hp1)`. Conclude with `levi_form a e h (hb fun w hw => (hp2 w).1 hw) hd`.
-/
theorem levi_chart (hκ : IsChartW T κ) (hT : IsWittBasis D.sp.cm.sig J 1 T) {g : UD D J₂}
    (hp : g ∈ leviSubOf finSumFinEquiv (uinc D J₂)) (a : GL (Fin n) (AE D))
    (e : leviMat finSumFinEquiv (umat g) = a.1) : mat (κ g) = blk4 a.1 0 0 (adj (a⁻¹).1) := by
  obtain ⟨hp1, hp2⟩ := Subgroup.mem_inf.1 hp
  obtain ⟨b, d, h, hd, hb⟩ := siegel_blocks hκ hT (g := g) (mem_siegelOf.1 hp1)
  exact levi_form a e h (hb fun w hw => (hp2 w).1 hw) hd

/- English proof (translation)
Take `⟨hg1, hg2⟩` from `mem_unipOf.1 hg`. Take `⟨b, d, h, hd, -⟩` from `siegel_blocks hκ hT (g := g) (mem_siegelOf.1 hg1)`. Establish `e : leviMat finSumFinEquiv (umat g) = 1` using `hg2`. Rewrite `h`, `hd` using `[e]`. Rewrite `hd` using `[adj_one, one_mul]`.

Conclude with `⟨b, by rw [h, hd]⟩`.
-/
theorem unip_chart (hκ : IsChartW T κ) (hT : IsWittBasis D.sp.cm.sig J 1 T) {g : UD D J₂}
    (hg : g ∈ unipOf finSumFinEquiv (uinc D J₂)) : ∃ β : Mx D n n, mat (κ g) = blk4 1 β 0 1 := by
  obtain ⟨hg1, hg2⟩ := mem_unipOf.1 hg
  obtain ⟨b, d, h, hd, -⟩ := siegel_blocks hκ hT (g := g) (mem_siegelOf.1 hg1)
  have e : leviMat finSumFinEquiv (umat g) = 1 := hg2
  rw [e] at h hd
  rw [adj_one, one_mul] at hd
  exact ⟨b, by rw [h, hd]⟩

end

/- English proof (translation)
Introduce `_ _ _ _ _ hκ _ hT` and use `⟨fun p hp => levi_chart hκ hT hp _ (val_leviOf p).symm, fun _ hg => unip_chart hκ hT hg⟩`.
-/
theorem levi_unip_chart : ∀ (D : D7) (n : ℕ) (J₂ : Matrix (Fin (n + n)) (Fin (n + n)) D.host.E) (T : GL (Fin (n + n)) D.host.E) (κ : UD D J₂ ≃* GlobalTheory.StdUnn.G D n), IsChartW T κ → ∀ J : Matrix (Fin n) (Fin n) D.host.E, IsWittBasis D.sp.cm.sig J 1 T → (∀ p : siegelOf finSumFinEquiv (uinc D J₂), (p : UD D J₂) ∈ leviSubOf finSumFinEquiv (uinc D J₂) → GlobalTheory.StdUnn.mat (κ p) = GlobalTheory.StdUnn.blk4 (leviOf finSumFinEquiv (uinc D J₂) p).1 0 0 (adj ((leviOf finSumFinEquiv (uinc D J₂) p)⁻¹).1)) ∧ ∀ b ∈ unipOf finSumFinEquiv (uinc D J₂), ∃ β : Mx D n n, GlobalTheory.StdUnn.mat (κ b) = GlobalTheory.StdUnn.blk4 1 β 0 1 :=
  fun _ _ _ _ _ hκ _ hT => ⟨fun p hp => levi_chart hκ hT hp _ (val_leviOf p).symm, fun _ hg => unip_chart hκ hT hg⟩

end GlobalTheory.SWLink.LeviChart

import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.CornerConj

noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermDef Formalism.L2.SG.DataCut
  Formalism.L2.SG.LsDatumB Formalism.L2.SG.Pf.PCount Formalism.L2.SG.Pf.AtPt Formalism.L2.SG.TermLoc
open Classical

namespace Formalism.L2.SG.Pf.TupGlob

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : Formalism.BasicNotions.D7} (Zd : LocDat D)

def StabApprox (u u' : D.what₂.Word) : Prop :=
  ∀ (w : Point D.host.E (D.R.rS + 1)) (Z₁ A₀ B₀ : PairVal.MatR D), AtMat w Z₁ → IsLo A₀ → IsUp B₀ →
    (∀ p, ∃ l ρ : MatP D p, TieN.IntLow (Zd.M p) l ∧ TieN.IntUp (Zd.M p) ρ ∧
      locL Zd p A₀ B₀ * (CntLocal.ZZP (M := Zd.M) Zd.δ u u' p Z₁ * LsDatumB.sgnP p) * locR Zd p A₀ B₀ =
        l * (CntLocal.ZZP (M := Zd.M) Zd.δ u u' p Z₁ * LsDatumB.sgnP p) * ρ) →
    ∃ X Y : PairVal.MatR D, IsLo X ∧ IsUp Y ∧
      X * (Z₁ * Sg D.host.E D.R.rS) * Y = Z₁ * Sg D.host.E D.R.rS ∧
      ∀ p, TieN.IntLow (Zd.M p) (locL Zd p (A₀ * X) (Y * B₀)) ∧ TieN.IntUp (Zd.M p) (locR Zd p (A₀ * X) (Y * B₀))

def Dict : Prop :=
  ∀ A B : PairVal.MatR D, IsLo A → IsUp B →
    (∀ p, TieN.IntLow (Zd.M p) (locL Zd p A B) ∧ TieN.IntUp (Zd.M p) (locR Zd p A B)) →
    IntFr A.conjTranspose ∧ IntFr (Sg D.host.E D.R.rS * B * Sg D.host.E D.R.rS) ∧
      TieG A.conjTranspose (Sg D.host.E D.R.rS * B * Sg D.host.E D.R.rS)

variable {Zd}

/- English proof (translation)
Introduce `i j` and use `⟨fun hji => h.2 j i hji, by rintro rfl; exact h.1 i⟩`.
-/
theorem isUpUni_of {K : Type*} [CommRing K] {n : ℕ} {U : Matrix (Fin n) (Fin n) K} (h : IsUp U) : IsUpUni U :=
  fun i j => ⟨fun hji => h.2 j i hji, by rintro rfl; exact h.1 i⟩

/- English proof (translation)
Assemble the required witnesses or components as `⟨fun a => by simp [Matrix.conjTranspose_apply, h.1 a], fun a b hab => by simp [Matrix.conjTranspose_apply, h.2 a b hab]⟩`.
-/
theorem isUp_conjT {n : ℕ} {A : Matrix (Fin n) (Fin n) D.host.E} (h : IsLo A) : IsUp A.conjTranspose :=
  ⟨fun a => by simp [Matrix.conjTranspose_apply, h.1 a],
    fun a b hab => by simp [Matrix.conjTranspose_apply, h.2 a b hab]⟩

/- English proof (translation)
Introduce `w Z₁ Z₂ _ hZ₁ hZ₂ htup`. Establish `hZ₁'` using `hZ₁`. Take `⟨L1, U1, hL1, hU1, e1⟩` from `hZ₁`. Take `⟨L2, U2, hL2, hU2, e2⟩` from `hZ₂`. Rewrite `e1`, `e2` using `[Formalism.L2.SG.Pf.AtPt.zhatOM_eq]`.

Establish `lo : ∀ L : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) D.host.E, IsLoUni L → Formalism.DoubleCosetMeasures.IsLowUni L` using `fun L h => ⟨fun i j hij => (h i j).1 hij, fun a => (h a a).2 rfl⟩`. Establish `up : ∀ U : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) D.host.E, IsUpUni U → Formalism.DoubleCosetMeasures.IsUpUni U` using `fun U h => ⟨fun i j hji => (h i j).1 hji, fun a => (h a a).2 rfl⟩`. Establish `lo' : ∀ L : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) D.host.E, Formalism.DoubleCosetMeasures.IsLowUni L → IsLo L` using `fun L h => ⟨h.2, fun a b hab => h.1 hab⟩`. Establish `up' : ∀ U : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) D.host.E, Formalism.DoubleCosetMeasures.IsUpUni U → IsUp U` using `fun U h => ⟨h.2, fun a b hab => h.1 hab⟩`. Establish `detL : ∀ L : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) D.host.E, Formalism.DoubleCosetMeasures.IsLowUni L → IsUnit L.det` using `fun L h => by`.

Rewrite using `[Matrix.det_of_lowerTriangular L h.1]`. Simplify using `[h.2]`. Establish `detU : ∀ U : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) D.host.E, Formalism.DoubleCosetMeasures.IsUpUni U → IsUnit U.det` using `fun U h => by`. Rewrite using `[Matrix.det_of_upperTriangular h.1]`. Simplify using `[h.2]`.

Establish `hA₀lo : IsLo (L2 * L1⁻¹)` using `isLo_mul (lo' _ (lo _ hL2)) (lo' _ (Formalism.DoubleCosetMeasures.isLowUni_inv (hx := lo _ hL1)))`. Establish `hB₀up : IsUp (U1⁻¹ * U2)` using `isUp_mul (up' _ (Formalism.DoubleCosetMeasures.isUpUni_inv (hx := up _ hU1))) (up' _ (up _ hU2))`. Establish `hmove : Z₂ * Sg D.host.E D.R.rS = (L2 * L1⁻¹) * (Z₁ * Sg D.host.E D.R.rS) * (U1⁻¹ * U2)`. Rewrite using `[e2, e1]`. Establish `i1 : L1⁻¹ * L1 = 1` using `Matrix.nonsing_inv_mul L1 (detL _ (lo _ hL1))`.

Establish `i2 : U1 * U1⁻¹ = 1` using `Matrix.mul_nonsing_inv U1 (detU _ (up _ hU1))`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[i1, i2, Matrix.mul_one, Matrix.one_mul]`. Use `_ = L2 * L1⁻¹ * (L1 * ptMat w * U1) * (U1⁻¹ * U2) := by simp only [Matrix.mul_assoc]`. Establish `hstab : ∀ p, ∃ l ρ : MatP D p, TieN.IntLow (Zd.M p) l ∧ TieN.IntUp (Zd.M p) ρ ∧ locL Zd p (L2 * L1⁻¹) (U1⁻¹ * U2) * (CntLocal.ZZP (M` using `Zd.M) Zd.δ u u' p Z₁ * LsDatumB.sgnP p) * locR Zd p (L2 * L1⁻¹) (U1⁻¹ * U2) = l * (CntLocal.ZZP (M := Zd.M) Zd.δ u u' p Z₁ * LsDatumB.sgnP p) * ρ := by`.

Introduce `p`. Establish `hmem` using `mem_kkOrb_self (M := Zd.M) p (CntLocal.ZZP (M := Zd.M) Zd.δ u u' p Z₂ * LsDatumB.sgnP p)`. Establish `ht` using `htup p`. Unfold `tupZ at ht`. Rewrite `hmem` using `[← ht]`.

Take `⟨l, ρ, hl, hρ, heq⟩` from `hmem`. Use `⟨l, ρ, hl, hρ, ?_⟩` and prove the remaining obligations. Rewrite using `[← locMove (Zd := Zd) u u' p hA₀lo hB₀up hmove]`. Conclude with `heq`. Take `⟨X, Y, hX, hY, hXY, hint⟩` from `hS w Z₁ (L2 * L1⁻¹) (U1⁻¹ * U2) hZ₁' hA₀lo hB₀up hstab`.

Take `⟨hIA, hIB, hT⟩` from `hD (L2 * L1⁻¹ * X) (Y * (U1⁻¹ * U2)) (isLo_mul hA₀lo hX) (isUp_mul hY hB₀up) hint`. Establish `hSg : Sg D.host.E D.R.rS = Matrix.diagonal (fun b : Fin (D.R.rS + 1) => (-1 : D.host.E) ^ (D.R.rS - b.val))`. Establish `h1` using `(Formalism.L2.SG.Pf.AtPt.zhatOM_eq (1 : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) D.host.E)).symm.trans (Formalism.L2.SG.Pf.zhatOM_eq_pv 1)`. Simplify using `using h1`. Establish `hsq : ∀ b : Fin (D.R.rS + 1), (-1 : D.host.E) ^ (D.R.rS - b.val) * (-1 : D.host.E) ^ (D.R.rS - b.val) = 1`.

Introduce `b`. Rewrite using `[← pow_add, ← two_mul, pow_mul]`. Simplify using the standard rewrite rules. Establish `hSS : Sg D.host.E D.R.rS * Sg D.host.E D.R.rS = 1`. Rewrite using `[hSg, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]`.

Use `congr 1`. Use function extensionality and compare the values at `b`. Conclude with `hsq b`. Use `⟨(L2 * L1⁻¹ * X).conjTranspose, Sg D.host.E D.R.rS * (Y * (U1⁻¹ * U2)) * Sg D.host.E D.R.rS, isUpUni_of (isUp_conjT (isLo_mul hA₀lo hX)), isUpUni_of ?_, hIA, hIB, hT, ?_⟩` and prove the remaining obligations. Rewrite using `[hSg]`.

Conclude with `isUp_conj (isUp_mul hY hB₀up) _ _ hsq`. Rewrite using `[Matrix.conjTranspose_conjTranspose]`. Establish `h3 : Z₂ * Sg D.host.E D.R.rS = L2 * L1⁻¹ * X * (Z₁ * Sg D.host.E D.R.rS) * (Y * (U1⁻¹ * U2))`. Rewrite using `[hmove]`. Use `conv_lhs => rw [← hXY]`.

Simplify using `only [Matrix.mul_assoc]`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[Matrix.mul_assoc, hSS, Matrix.mul_one]`. Use `_ = L2 * L1⁻¹ * X * Z₁ * (Sg D.host.E D.R.rS * (Y * (U1⁻¹ * U2)) * Sg D.host.E D.R.rS) := by`. Rewrite using `[h3]`.

Simplify using `only [Matrix.mul_assoc]`.
-/
theorem globMove_of (u u' : D.what₂.Word) (hS : StabApprox Zd u u') (hD : Dict Zd) : GlobMove D Zd.M Zd.δ u u' := by
  intro w Z₁ Z₂ _ hZ₁ hZ₂ htup
  have hZ₁' := hZ₁
  obtain ⟨L1, U1, hL1, hU1, e1⟩ := hZ₁
  obtain ⟨L2, U2, hL2, hU2, e2⟩ := hZ₂
  rw [Formalism.L2.SG.Pf.AtPt.zhatOM_eq] at e1 e2
  have lo : ∀ L : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) D.host.E, IsLoUni L → Formalism.DoubleCosetMeasures.IsLowUni L :=
    fun L h => ⟨fun i j hij => (h i j).1 hij, fun a => (h a a).2 rfl⟩
  have up : ∀ U : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) D.host.E, IsUpUni U → Formalism.DoubleCosetMeasures.IsUpUni U :=
    fun U h => ⟨fun i j hji => (h i j).1 hji, fun a => (h a a).2 rfl⟩
  have lo' : ∀ L : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) D.host.E, Formalism.DoubleCosetMeasures.IsLowUni L → IsLo L :=
    fun L h => ⟨h.2, fun a b hab => h.1 hab⟩
  have up' : ∀ U : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) D.host.E, Formalism.DoubleCosetMeasures.IsUpUni U → IsUp U :=
    fun U h => ⟨h.2, fun a b hab => h.1 hab⟩
  have detL : ∀ L : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) D.host.E, Formalism.DoubleCosetMeasures.IsLowUni L →
      IsUnit L.det := fun L h => by
    rw [Matrix.det_of_lowerTriangular L h.1]
    simp [h.2]
  have detU : ∀ U : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) D.host.E, Formalism.DoubleCosetMeasures.IsUpUni U →
      IsUnit U.det := fun U h => by
    rw [Matrix.det_of_upperTriangular h.1]
    simp [h.2]
  have hA₀lo : IsLo (L2 * L1⁻¹) :=
    isLo_mul (lo' _ (lo _ hL2)) (lo' _ (Formalism.DoubleCosetMeasures.isLowUni_inv (hx := lo _ hL1)))
  have hB₀up : IsUp (U1⁻¹ * U2) :=
    isUp_mul (up' _ (Formalism.DoubleCosetMeasures.isUpUni_inv (hx := up _ hU1))) (up' _ (up _ hU2))
  have hmove : Z₂ * Sg D.host.E D.R.rS = (L2 * L1⁻¹) * (Z₁ * Sg D.host.E D.R.rS) * (U1⁻¹ * U2) := by
    rw [e2, e1]
    have i1 : L1⁻¹ * L1 = 1 := Matrix.nonsing_inv_mul L1 (detL _ (lo _ hL1))
    have i2 : U1 * U1⁻¹ = 1 := Matrix.mul_nonsing_inv U1 (detU _ (up _ hU1))
    calc L2 * ptMat w * U2 = L2 * (L1⁻¹ * L1) * ptMat w * ((U1 * U1⁻¹) * U2) := by
          rw [i1, i2, Matrix.mul_one, Matrix.one_mul]
      _ = L2 * L1⁻¹ * (L1 * ptMat w * U1) * (U1⁻¹ * U2) := by simp only [Matrix.mul_assoc]
  have hstab : ∀ p, ∃ l ρ : MatP D p, TieN.IntLow (Zd.M p) l ∧ TieN.IntUp (Zd.M p) ρ ∧
      locL Zd p (L2 * L1⁻¹) (U1⁻¹ * U2) * (CntLocal.ZZP (M := Zd.M) Zd.δ u u' p Z₁ * LsDatumB.sgnP p) *
          locR Zd p (L2 * L1⁻¹) (U1⁻¹ * U2) =
        l * (CntLocal.ZZP (M := Zd.M) Zd.δ u u' p Z₁ * LsDatumB.sgnP p) * ρ := by
    intro p
    have hmem := mem_kkOrb_self (M := Zd.M) p (CntLocal.ZZP (M := Zd.M) Zd.δ u u' p Z₂ * LsDatumB.sgnP p)
    have ht := htup p
    unfold tupZ at ht
    rw [← ht] at hmem
    obtain ⟨l, ρ, hl, hρ, heq⟩ := hmem
    refine ⟨l, ρ, hl, hρ, ?_⟩
    rw [← locMove (Zd := Zd) u u' p hA₀lo hB₀up hmove]
    exact heq
  obtain ⟨X, Y, hX, hY, hXY, hint⟩ := hS w Z₁ (L2 * L1⁻¹) (U1⁻¹ * U2) hZ₁' hA₀lo hB₀up hstab
  obtain ⟨hIA, hIB, hT⟩ := hD (L2 * L1⁻¹ * X) (Y * (U1⁻¹ * U2)) (isLo_mul hA₀lo hX) (isUp_mul hY hB₀up) hint
  have hSg : Sg D.host.E D.R.rS =
      Matrix.diagonal (fun b : Fin (D.R.rS + 1) => (-1 : D.host.E) ^ (D.R.rS - b.val)) := by
    have h1 := (Formalism.L2.SG.Pf.AtPt.zhatOM_eq (1 : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) D.host.E)).symm.trans
      (Formalism.L2.SG.Pf.zhatOM_eq_pv 1)
    simpa using h1
  have hsq : ∀ b : Fin (D.R.rS + 1), (-1 : D.host.E) ^ (D.R.rS - b.val) * (-1 : D.host.E) ^ (D.R.rS - b.val) = 1 := by
    intro b
    rw [← pow_add, ← two_mul, pow_mul]
    simp
  have hSS : Sg D.host.E D.R.rS * Sg D.host.E D.R.rS = 1 := by
    rw [hSg, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext b
    exact hsq b
  refine ⟨(L2 * L1⁻¹ * X).conjTranspose, Sg D.host.E D.R.rS * (Y * (U1⁻¹ * U2)) * Sg D.host.E D.R.rS,
    isUpUni_of (isUp_conjT (isLo_mul hA₀lo hX)), isUpUni_of ?_, hIA, hIB, hT, ?_⟩
  · rw [hSg]
    exact isUp_conj (isUp_mul hY hB₀up) _ _ hsq
  · rw [Matrix.conjTranspose_conjTranspose]
    have h3 : Z₂ * Sg D.host.E D.R.rS =
        L2 * L1⁻¹ * X * (Z₁ * Sg D.host.E D.R.rS) * (Y * (U1⁻¹ * U2)) := by
      rw [hmove]
      conv_lhs => rw [← hXY]
      simp only [Matrix.mul_assoc]
    calc Z₂ = Z₂ * Sg D.host.E D.R.rS * Sg D.host.E D.R.rS := by
          rw [Matrix.mul_assoc, hSS, Matrix.mul_one]
      _ = L2 * L1⁻¹ * X * Z₁ * (Sg D.host.E D.R.rS * (Y * (U1⁻¹ * U2)) * Sg D.host.E D.R.rS) := by
          rw [h3]
          simp only [Matrix.mul_assoc]

end Formalism.L2.SG.Pf.TupGlob

import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.FrFacInvMul

noncomputable section

open scoped Classical Matrix

namespace Formalism.L2.SG.Pf.FibQ

open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups PI.PairValDefs PI.NRCW IsDedekindDomain
  Formalism.L2.SG.TermLoc

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section ModeL

variable {D : D7} (Z : LocDat D) (p : PlF D)

/- English proof (translation)
Unfold `Formalism.L2.SG.LsDatumB.sgnP`. Rewrite using `[Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]`. Use `congr 1`. Use function extensionality and compare the values at `b`. Rewrite using `[← pow_add, ← two_mul, pow_mul]`.

Simplify using the standard rewrite rules.
-/
theorem permSign_mul_self₂ : Formalism.L2.SG.LsDatumB.sgnP (D := D) p * Formalism.L2.SG.LsDatumB.sgnP p = 1 := by
  unfold Formalism.L2.SG.LsDatumB.sgnP
  rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1
  funext b
  rw [← pow_add, ← two_mul, pow_mul]
  simp

/- English proof (translation)
Establish `e : ∀ a b, (Formalism.L2.SG.LsDatumB.sgnP p * ρ * Formalism.L2.SG.LsDatumB.sgnP p) a b = ((-1 : (D.s.atP p).Ep) ^ (D.R.rS - a.val)) * ρ a b * (-1) ^ (D.R.rS - b.val)`. Introduce `a b`. Simplify using `[Formalism.L2.SG.LsDatumB.sgnP, Matrix.mul_diagonal, Matrix.diagonal_mul]`. Use `⟨fun a => ?_, fun a b h => ?_, fun a b => ?_⟩` and prove the remaining obligations. Rewrite using `[e, hρ.1 a, mul_one, ← pow_add, ← two_mul, pow_mul]`.

Simplify using the standard rewrite rules. Rewrite using `[e, hρ.2.1 a b h]`. Simplify using the standard rewrite rules. Rewrite using `[e]`. Use `Subring.mul_mem _ (Subring.mul_mem _ (Subring.pow_mem _ (Subring.neg_mem _ (Subring.one_mem _)) _) (hρ.2.2 a b)) (Subring.pow_mem _ (Subring.neg_mem _ (Subring.one_mem _)) _)` and prove the remaining obligations.
-/
theorem sgn_conj_intUp {ρ : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) (D.s.atP p).Ep}
    (hρ : (∀ a, ρ a a = 1) ∧ (∀ a b, b < a → ρ a b = 0) ∧ ∀ a b, ρ a b ∈ (Z.M p).R) :
    (∀ a, (Formalism.L2.SG.LsDatumB.sgnP p * ρ * Formalism.L2.SG.LsDatumB.sgnP p) a a = 1) ∧
      (∀ a b, b < a → (Formalism.L2.SG.LsDatumB.sgnP p * ρ * Formalism.L2.SG.LsDatumB.sgnP p) a b = 0) ∧
      ∀ a b, (Formalism.L2.SG.LsDatumB.sgnP p * ρ * Formalism.L2.SG.LsDatumB.sgnP p) a b ∈ (Z.M p).R := by
  have e : ∀ a b, (Formalism.L2.SG.LsDatumB.sgnP p * ρ * Formalism.L2.SG.LsDatumB.sgnP p) a b =
      ((-1 : (D.s.atP p).Ep) ^ (D.R.rS - a.val)) * ρ a b * (-1) ^ (D.R.rS - b.val) := by
    intro a b
    simp [Formalism.L2.SG.LsDatumB.sgnP, Matrix.mul_diagonal, Matrix.diagonal_mul]
  refine ⟨fun a => ?_, fun a b h => ?_, fun a b => ?_⟩
  · rw [e, hρ.1 a, mul_one, ← pow_add, ← two_mul, pow_mul]; simp
  · rw [e, hρ.2.1 a b h]; simp
  · rw [e]
    refine Subring.mul_mem _ (Subring.mul_mem _ (Subring.pow_mem _ (Subring.neg_mem _ (Subring.one_mem _)) _)
      (hρ.2.2 a b)) (Subring.pow_mem _ (Subring.neg_mem _ (Subring.one_mem _)) _)

/- English proof (translation)
Establish `hR : (Z.M p).R = (Z.M p).L.O`. Unfold `Formalism.MainNotions.S.Loc.Model.R`. Rewrite using `[hs]`. Establish `eZZ : ∀ X, Formalism.L2.SG.CntLocal.ZZP (M` using `Z.M) Z.δ u u' p X = Formalism.L2.SG.CntLocal.ZhatLoc Z.M Z.δ p X := by`. Introduce `X`.

Simplify using `only [Formalism.L2.SG.CntLocal.ZZP, Formalism.MainNotions.S.Loc.HermSp.ZZplusOf, hs]`. Take `⟨hN1, hN0, hNO⟩` from `locU_int Z p N hNU hNd hNb`. Take `⟨hM1, hM0, hMO⟩` from `locU_int Z p M hMU hMd hMb`. Use `set K := ((locU Z p N).map (Z.M p).L.cj)ᵀ with hKdef`. Establish `hK` using `key_rel Z p N M Z₁ Z₂ hrel`.

Establish `hKlow : Formalism.MainNotions.S.TieN.IntLow (Z.M p) K`. Use `⟨fun a => ?_, fun a b h => ?_, fun a b => ?_⟩` and prove the remaining obligations. Simplify using `only [hKdef, Matrix.transpose_apply, Matrix.map_apply, hN1 a, map_one]`. Simplify using `only [hKdef, Matrix.transpose_apply, Matrix.map_apply, hN0 b a h, map_zero]`. Rewrite using `[hR]`.

Simplify using `only [hKdef, Matrix.transpose_apply, Matrix.map_apply]`. Conclude with `PI.LocCntLat.GC.cj_mem_O _ (hNO b a)`. Establish `hρ : Formalism.MainNotions.S.TieN.IntUp (Z.M p) (locU Z p M)` using `⟨hM1, hM0, fun a b => by rw [hR]; exact hMO a b⟩`. Establish `hdet : IsUnit K.det`. Establish `hb : K.BlockTriangular OrderDual.toDual` using `fun i j hij => hKlow.2.1 i j hij`.

Establish `hd : K.det = 1`. Rewrite using `[Matrix.det_of_lowerTriangular K hb]`. Simplify using `[hKlow.1]`. Rewrite using `[hd]`. Conclude with `isUnit_one`.

Establish `hY : Formalism.L2.SG.CntLocal.ZhatLoc Z.M Z.δ p Z₂ = K⁻¹ * Formalism.L2.SG.CntLocal.ZhatLoc Z.M Z.δ p Z₁ * locU Z p M`. Rewrite using `[Matrix.mul_assoc, ← hK, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul K hdet, Matrix.one_mul]`. Use `⟨K⁻¹, Formalism.L2.SG.LsDatumB.sgnP p * locU Z p M * Formalism.L2.SG.LsDatumB.sgnP p, Formalism.L2.SG.Pf.LocOrbCut.intLow_inv (Z.M p) hKlow, sgn_conj_intUp Z p hρ, ?_⟩` and prove the remaining obligations. Rewrite using `[eZZ, eZZ, hY]`. Simplify using `only [Matrix.mul_assoc]`.

Rewrite using `[← Matrix.mul_assoc (Formalism.L2.SG.LsDatumB.sgnP p) (Formalism.L2.SG.LsDatumB.sgnP p), permSign_mul_self₂, Matrix.one_mul]`.
-/
theorem modeL (hs : (Z.M p).split = none) (u u' : D.what₂.Word)
    (N M Z₁ Z₂ : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) D.host.E)
    (hNU : ∀ a b, b < a → N a b = 0) (hNd : ∀ a, N a a = 1) (hMU : ∀ a b, b < a → M a b = 0)
    (hMd : ∀ a, M a a = 1)
    (hNb : ∀ c b, c < b → ∀ x ∈ aaF D b, x * N c b ∈ aaF D c)
    (hMb : ∀ c b, c < b → ∀ x ∈ aaF D b, x * M c b ∈ aaF D c) (hrel : Nᴴ * Z₂ = Z₁ * M) :
    ∃ l ρ, Formalism.MainNotions.S.TieN.IntLow (Z.M p) l ∧ Formalism.MainNotions.S.TieN.IntUp (Z.M p) ρ ∧
      Formalism.L2.SG.CntLocal.ZZP (M := Z.M) Z.δ u u' p Z₂ * Formalism.L2.SG.LsDatumB.sgnP p =
        l * (Formalism.L2.SG.CntLocal.ZZP (M := Z.M) Z.δ u u' p Z₁ * Formalism.L2.SG.LsDatumB.sgnP p) * ρ := by
  have hR : (Z.M p).R = (Z.M p).L.O := by
    unfold Formalism.MainNotions.S.Loc.Model.R
    rw [hs]
  have eZZ : ∀ X, Formalism.L2.SG.CntLocal.ZZP (M := Z.M) Z.δ u u' p X = Formalism.L2.SG.CntLocal.ZhatLoc Z.M Z.δ p X := by
    intro X
    simp only [Formalism.L2.SG.CntLocal.ZZP, Formalism.MainNotions.S.Loc.HermSp.ZZplusOf, hs]
  obtain ⟨hN1, hN0, hNO⟩ := locU_int Z p N hNU hNd hNb
  obtain ⟨hM1, hM0, hMO⟩ := locU_int Z p M hMU hMd hMb
  set K := ((locU Z p N).map (Z.M p).L.cj)ᵀ with hKdef
  have hK := key_rel Z p N M Z₁ Z₂ hrel
  have hKlow : Formalism.MainNotions.S.TieN.IntLow (Z.M p) K := by
    refine ⟨fun a => ?_, fun a b h => ?_, fun a b => ?_⟩
    · simp only [hKdef, Matrix.transpose_apply, Matrix.map_apply, hN1 a, map_one]
    · simp only [hKdef, Matrix.transpose_apply, Matrix.map_apply, hN0 b a h, map_zero]
    · rw [hR]
      simp only [hKdef, Matrix.transpose_apply, Matrix.map_apply]
      exact PI.LocCntLat.GC.cj_mem_O _ (hNO b a)
  have hρ : Formalism.MainNotions.S.TieN.IntUp (Z.M p) (locU Z p M) := ⟨hM1, hM0, fun a b => by rw [hR]; exact hMO a b⟩
  have hdet : IsUnit K.det := by
    have hb : K.BlockTriangular OrderDual.toDual := fun i j hij => hKlow.2.1 i j hij
    have hd : K.det = 1 := by
      rw [Matrix.det_of_lowerTriangular K hb]
      simp [hKlow.1]
    rw [hd]
    exact isUnit_one
  have hY : Formalism.L2.SG.CntLocal.ZhatLoc Z.M Z.δ p Z₂ =
      K⁻¹ * Formalism.L2.SG.CntLocal.ZhatLoc Z.M Z.δ p Z₁ * locU Z p M := by
    rw [Matrix.mul_assoc, ← hK, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul K hdet, Matrix.one_mul]
  refine ⟨K⁻¹, Formalism.L2.SG.LsDatumB.sgnP p * locU Z p M * Formalism.L2.SG.LsDatumB.sgnP p,
    Formalism.L2.SG.Pf.LocOrbCut.intLow_inv (Z.M p) hKlow, sgn_conj_intUp Z p hρ, ?_⟩
  rw [eZZ, eZZ, hY]
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc (Formalism.L2.SG.LsDatumB.sgnP p) (Formalism.L2.SG.LsDatumB.sgnP p), permSign_mul_self₂, Matrix.one_mul]

end ModeL

end Formalism.L2.SG.Pf.FibQ

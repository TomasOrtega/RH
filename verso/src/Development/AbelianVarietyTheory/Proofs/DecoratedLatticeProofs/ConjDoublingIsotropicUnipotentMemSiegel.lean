import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MulVecPairVecDiag
open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec ThetaClause SectionClause CoefClause)
open GlobalTheory.Mem.Th (CptF)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.IP GlobalTheory.Core.Rk.Dich
open Matrix

namespace GlobalTheory.Core.Rk.Dich

/- English proof (translation)
Establish `hinj : Function.Injective C.mulVec` using `Matrix.mulVec_injective_iff.2 hC`. Take `⟨g, hg⟩` from `LinearMap.exists_leftInverse_of_injective (Matrix.toLin' C) (LinearMap.ker_eq_bot.2 fun x y h => hinj (by simpa [Matrix.toLin'_apply] using h))`. Use `⟨LinearMap.toMatrix' g, ?_⟩` and prove the remaining obligations. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[LinearMap.toMatrix'_toLin']`.

Use `_ = LinearMap.toMatrix' (g ∘ₗ Matrix.toLin' C) := (LinearMap.toMatrix'_comp _ _).symm`. Use `_ = 1 := by rw [hg, LinearMap.toMatrix'_id]`.
-/
theorem exists_leftInv_of_linInd {K : Type} [Field K] {a b : ℕ} (C : Matrix (Fin a) (Fin b) K)
    (hC : LinearIndependent K C.transpose) : ∃ L : Matrix (Fin b) (Fin a) K, L * C = 1 := by
  have hinj : Function.Injective C.mulVec := Matrix.mulVec_injective_iff.2 hC
  obtain ⟨g, hg⟩ := LinearMap.exists_leftInverse_of_injective (Matrix.toLin' C)
    (LinearMap.ker_eq_bot.2 fun x y h => hinj (by simpa [Matrix.toLin'_apply] using h))
  refine ⟨LinearMap.toMatrix' g, ?_⟩
  calc LinearMap.toMatrix' g * C = LinearMap.toMatrix' g * LinearMap.toMatrix' (Matrix.toLin' C) := by
        rw [LinearMap.toMatrix'_toLin']
    _ = LinearMap.toMatrix' (g ∘ₗ Matrix.toLin' C) := (LinearMap.toMatrix'_comp _ _).symm
    _ = 1 := by rw [hg, LinearMap.toMatrix'_id]

variable {D : D7}

set_option maxHeartbeats 1000000 in

/- English proof (translation)
Use `set σ : D.host.E →+* D.host.E := (D.sp.cm.sig : D.host.E →+* D.host.E) with hσ`. Use `set J := V.gram with hJ`. Establish `hinjA : Function.Injective (incA D)` using `by haveI : Nontrivial (AF D.host.F) := inferInstanceAs (Nontrivial (Ainf D.host.F × Af D.host.F))`. Conclude with `Algebra.TensorProduct.includeRight_injective (algebraMap D.host.F (AF D.host.F)).injective`. Take `⟨g0, hg0, -, hinv⟩` from `exists_rat (dblSp V) hγ`.

Establish `hγi' : γi = (g0⁻¹).1` using `Matrix.map_injective hinjA (hγi.symm.trans hinv)`. Establish `hu : Formalism.UG.cT σ γi * GlobalTheory.Doubling.dblGram finSumFinEquiv J * γi = GlobalTheory.Doubling.dblGram finSumFinEquiv J`. Rewrite using `[hγi', hJ, ← gram_hdbl V]`. Conclude with `(Formalism.UG.UJ _ _).inv_mem hg0`. Establish `hiso` using `isotropic_diag hu`.

Use `set P := leviMat finSumFinEquiv γi with hP`. Use `set Q' := diagSnd γi with hQ'`. Use `set C := P * K with hCdef`. Establish `hCJP : Formalism.UG.cT σ C * J * P = 0`. Combine the equalities or inequalities in the displayed calculation.

Rewrite using `[hCdef, Formalism.UG.cT_mul]`. Simplify using `only [Matrix.mul_assoc]`. Use `_ = Formalism.UG.cT σ (Q' * K) * J * Q' := by rw [hiso, Formalism.UG.cT_mul]; simp only [Matrix.mul_assoc]`. Use `_ = 0 := by rw [hK]; simp [Formalism.UG.cT]`. Establish `hcol : ∀ i, (Formalism.UG.cT σ C * J).mulVec (fun j => P j i) = 0` using `fun i => by`.

Use function extensionality and compare the values at `k`. Use `congrFun (congrFun hCJP k) i` as an intermediate fact. Simplify `this` using `[Matrix.mulVec, dotProduct, Matrix.mul_apply]`. Use `choose a ha using fun i => h3 _ (hcol i)`. Use `set G := (Formalism.L2.Theta.matHom V g).1 with hG`.

Use `set m := G - 1 with hm`. Set `A : Matrix (Fin r) (Fin V.rank) (AE D)` to `Matrix.of fun k i => a i k`. Establish `hmP : m * P.map (incA D) = HMul.hMul (C.map (incA D)) A`. Use extensionality with `j i`. Use `congrFun (ha i) j` as an intermediate fact.

Simplify `this` using `[Matrix.mulVec, dotProduct, Matrix.mul_apply, A]`. Establish `hCm : C.map (incA D) = HMul.hMul (P.map (incA D)) (K.map (incA D))` using `Matrix.map_mul`. Take `⟨L, hL⟩` from `exists_leftInv_of_linInd C hC.2.1`. Establish `hAK : A * K.map (incA D) = 0`. Establish `e1 : C.map (incA D) * (A * K.map (incA D)) = 0`.

Rewrite using `[← Matrix.mul_assoc, ← hmP, Matrix.mul_assoc, ← hCm, h1]`. Establish `e2 : L.map (incA D) * C.map (incA D) = 1`. Rewrite using `[← Matrix.map_mul, hL, Matrix.map_one _ (map_zero _) (map_one _)]`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[e2, Matrix.one_mul]`.

Use `_ = 0 := by rw [Matrix.mul_assoc, e1, Matrix.mul_zero]`. Use `set Γ := (Formalism.L2.Theta.matHom (dblSp V) γ).1 with hΓ`. Use `set Γi := (Formalism.L2.Theta.matHom (dblSp V) γ⁻¹).1 with hΓi`. Establish `hΓΓi : Γ * Γi = 1`. Rewrite using `[hΓ, hΓi, ← Units.val_mul, ← map_mul, mul_inv_cancel, map_one, Units.val_one]`.

Establish `hMg : (Formalism.L2.Theta.matHom (dblSp V) (γ * io V (g, 1) * γ⁻¹)).1 = Γ * blkMat finSumFinEquiv G 1 * Γi`. Rewrite using `[map_mul, map_mul, Units.val_mul, Units.val_mul, matHom_io, val_blkGL, map_one, Units.val_one]`. Establish `hdiag : ∀ x : Fin V.rank → AE D, Γi *ᵥ pairVec finSumFinEquiv x x = pairVec finSumFinEquiv (P.map (incA D) *ᵥ x) (Q'.map (incA D) *ᵥ x)` using `fun x => by`. Rewrite using `[hγi, mulVec_pairVec_diag, leviMat_map, diagSnd_map]`. Establish `hact : ∀ x : Fin V.rank → AE D, (Γ * blkMat finSumFinEquiv G 1 * Γi) *ᵥ pairVec finSumFinEquiv x x = pairVec finSumFinEquiv (x + (K.map (incA D) * A) *ᵥ x) (x + (K.map (incA D) * A) *ᵥ x)` using `fun x => by`.

Establish `hy : Γi *ᵥ pairVec finSumFinEquiv (x + (K.map (incA D) * A) *ᵥ x) (x + (K.map (incA D) * A) *ᵥ x) = blkMat finSumFinEquiv G 1 *ᵥ (Γi *ᵥ pairVec finSumFinEquiv x x)`. Rewrite using `[hdiag, hdiag, blkMat_mulVec, one_mulVec]`. Use `congr 1`. Rewrite using `[mulVec_add, mulVec_mulVec, ← Matrix.mul_assoc, ← hCm, ← hmP, ← mulVec_mulVec, show G = m + 1 from (sub_add_cancel G 1).symm, add_mulVec, one_mulVec, add_comm]`. Rewrite using `[mulVec_add, mulVec_mulVec, ← Matrix.mul_assoc, ← Matrix.map_mul, hK, Matrix.map_zero _ (map_zero _), Matrix.zero_mul, zero_mulVec, add_zero]`.

Rewrite using `[← mulVec_mulVec, ← mulVec_mulVec, ← hy, mulVec_mulVec, hΓΓi, one_mulVec]`. Establish `hKD : KeepsDiag finSumFinEquiv (Γ * blkMat finSumFinEquiv G 1 * Γi)` using `keepsDiag_of_mulVec fun w hw => by`. Take `⟨x, rfl⟩` from `(mem_diagSub finSumFinEquiv).1 hw`. Rewrite using `[hact]`. Conclude with `(pairVec_mem_diagSub finSumFinEquiv).2 rfl`.

Establish `hmem : γ * io V (g, 1) * γ⁻¹ ∈ siegel V` using `mem_siegelOf.2 (by`. Express the relevant statement in the definitionally equal form `KeepsDiag finSumFinEquiv (Formalism.L2.Theta.matHom (dblSp V) (γ * io V (g, 1) * γ⁻¹)).1`. Rewrite using `[hMg]`. Conclude with `hKD)`. Establish `hlevi : leviMat finSumFinEquiv (Γ * blkMat finSumFinEquiv G 1 * Γi) = 1 + K.map (incA D) * A`.

Use `Matrix.ext_of_mulVec_single fun j => ?_` and prove the remaining obligations. Establish `h` using `(hKD.mulVec_diag (Pi.single j 1)).symm.trans (hact _)`. Use function extensionality and compare the values at `i`. Use `congrFun h (finSumFinEquiv (.inl i))` as an intermediate fact. Rewrite `this` using `[pairVec_inl, pairVec_inl]`.

Rewrite using `[this, add_mulVec, one_mulVec]`. Use `⟨hmem, Units.ext ?_⟩` and prove the remaining obligations. Rewrite using `[Units.val_one]`. Express the relevant statement in the definitionally equal form `(leviMat finSumFinEquiv (Formalism.L2.Theta.matHom (dblSp V) (γ * io V (g, 1) * γ⁻¹)).1).det = 1`. Rewrite using `[hMg, hlevi, Matrix.det_one_add_mul_comm, hAK, add_zero, Matrix.det_one]`.
-/
theorem conj_io_gen_mem (V : HSp D) (γ : GA D (dblSp V)) (hγ : γ ∈ GQ (dblSp V))
    (γi : Matrix (Fin (V.rank + V.rank)) (Fin (V.rank + V.rank)) D.host.E)
    (hγi : (Formalism.L2.Theta.matHom (dblSp V) γ⁻¹).1 = γi.map (incA D)) (r : ℕ)
    (K : Matrix (Fin V.rank) (Fin r) D.host.E) (hK : diagSnd γi * K = 0)
    (hC : IsIsoFrame V (leviMat finSumFinEquiv γi * K)) (g : GA D V)
    (h1 : HMul.hMul ((Formalism.L2.Theta.matHom V g).1 - 1) ((leviMat finSumFinEquiv γi * K).map (incA D)) = 0)
    (h3 : ∀ x : Fin V.rank → D.host.E,
      (Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) (leviMat finSumFinEquiv γi * K) * V.gram).mulVec x = 0 →
      ∃ a : Fin r → AE D, ((Formalism.L2.Theta.matHom V g).1 - 1).mulVec (fun i => incA D (x i)) =
        ((leviMat finSumFinEquiv γi * K).map (incA D)).mulVec a) :
    ∃ h : γ * io V (g, 1) * γ⁻¹ ∈ siegel V, aP V ⟨_, h⟩ = 1 := by
  classical
  set σ : D.host.E →+* D.host.E := (D.sp.cm.sig : D.host.E →+* D.host.E) with hσ
  set J := V.gram with hJ
  have hinjA : Function.Injective (incA D) := by
    haveI : Nontrivial (AF D.host.F) := inferInstanceAs (Nontrivial (Ainf D.host.F × Af D.host.F))
    exact Algebra.TensorProduct.includeRight_injective (algebraMap D.host.F (AF D.host.F)).injective
  obtain ⟨g0, hg0, -, hinv⟩ := exists_rat (dblSp V) hγ
  have hγi' : γi = (g0⁻¹).1 := Matrix.map_injective hinjA (hγi.symm.trans hinv)
  have hu : Formalism.UG.cT σ γi * GlobalTheory.Doubling.dblGram finSumFinEquiv J * γi = GlobalTheory.Doubling.dblGram finSumFinEquiv J := by
    rw [hγi', hJ, ← gram_hdbl V]; exact (Formalism.UG.UJ _ _).inv_mem hg0
  have hiso := isotropic_diag hu
  set P := leviMat finSumFinEquiv γi with hP
  set Q' := diagSnd γi with hQ'
  set C := P * K with hCdef
  have hCJP : Formalism.UG.cT σ C * J * P = 0 := by
    calc Formalism.UG.cT σ C * J * P = Formalism.UG.cT σ K * (Formalism.UG.cT σ P * J * P) := by
          rw [hCdef, Formalism.UG.cT_mul]; simp only [Matrix.mul_assoc]
      _ = Formalism.UG.cT σ (Q' * K) * J * Q' := by rw [hiso, Formalism.UG.cT_mul]; simp only [Matrix.mul_assoc]
      _ = 0 := by rw [hK]; simp [Formalism.UG.cT]
  have hcol : ∀ i, (Formalism.UG.cT σ C * J).mulVec (fun j => P j i) = 0 := fun i => by
    funext k
    have := congrFun (congrFun hCJP k) i
    simpa [Matrix.mulVec, dotProduct, Matrix.mul_apply] using this
  choose a ha using fun i => h3 _ (hcol i)
  set G := (Formalism.L2.Theta.matHom V g).1 with hG
  set m := G - 1 with hm
  let A : Matrix (Fin r) (Fin V.rank) (AE D) := Matrix.of fun k i => a i k
  have hmP : m * P.map (incA D) = HMul.hMul (C.map (incA D)) A := by
    ext j i
    have := congrFun (ha i) j
    simpa [Matrix.mulVec, dotProduct, Matrix.mul_apply, A] using this
  have hCm : C.map (incA D) = HMul.hMul (P.map (incA D)) (K.map (incA D)) := Matrix.map_mul
  obtain ⟨L, hL⟩ := exists_leftInv_of_linInd C hC.2.1
  have hAK : A * K.map (incA D) = 0 := by
    have e1 : C.map (incA D) * (A * K.map (incA D)) = 0 := by
      rw [← Matrix.mul_assoc, ← hmP, Matrix.mul_assoc, ← hCm, h1]
    have e2 : L.map (incA D) * C.map (incA D) = 1 := by
      rw [← Matrix.map_mul, hL, Matrix.map_one _ (map_zero _) (map_one _)]
    calc A * K.map (incA D) = L.map (incA D) * C.map (incA D) * (A * K.map (incA D)) := by
          rw [e2, Matrix.one_mul]
      _ = 0 := by rw [Matrix.mul_assoc, e1, Matrix.mul_zero]
  set Γ := (Formalism.L2.Theta.matHom (dblSp V) γ).1 with hΓ
  set Γi := (Formalism.L2.Theta.matHom (dblSp V) γ⁻¹).1 with hΓi
  have hΓΓi : Γ * Γi = 1 := by
    rw [hΓ, hΓi, ← Units.val_mul, ← map_mul, mul_inv_cancel, map_one, Units.val_one]
  have hMg : (Formalism.L2.Theta.matHom (dblSp V) (γ * io V (g, 1) * γ⁻¹)).1 = Γ * blkMat finSumFinEquiv G 1 * Γi := by
    rw [map_mul, map_mul, Units.val_mul, Units.val_mul, matHom_io, val_blkGL, map_one, Units.val_one]
  have hdiag : ∀ x : Fin V.rank → AE D, Γi *ᵥ pairVec finSumFinEquiv x x =
      pairVec finSumFinEquiv (P.map (incA D) *ᵥ x) (Q'.map (incA D) *ᵥ x) := fun x => by
    rw [hγi, mulVec_pairVec_diag, leviMat_map, diagSnd_map]
  have hact : ∀ x : Fin V.rank → AE D, (Γ * blkMat finSumFinEquiv G 1 * Γi) *ᵥ pairVec finSumFinEquiv x x =
      pairVec finSumFinEquiv (x + (K.map (incA D) * A) *ᵥ x) (x + (K.map (incA D) * A) *ᵥ x) := fun x => by
    have hy : Γi *ᵥ pairVec finSumFinEquiv (x + (K.map (incA D) * A) *ᵥ x) (x + (K.map (incA D) * A) *ᵥ x) =
        blkMat finSumFinEquiv G 1 *ᵥ (Γi *ᵥ pairVec finSumFinEquiv x x) := by
      rw [hdiag, hdiag, blkMat_mulVec, one_mulVec]
      congr 1
      · rw [mulVec_add, mulVec_mulVec, ← Matrix.mul_assoc, ← hCm, ← hmP, ← mulVec_mulVec,
          show G = m + 1 from (sub_add_cancel G 1).symm, add_mulVec, one_mulVec, add_comm]
      · rw [mulVec_add, mulVec_mulVec, ← Matrix.mul_assoc, ← Matrix.map_mul, hK,
          Matrix.map_zero _ (map_zero _), Matrix.zero_mul, zero_mulVec, add_zero]
    rw [← mulVec_mulVec, ← mulVec_mulVec, ← hy, mulVec_mulVec, hΓΓi, one_mulVec]
  have hKD : KeepsDiag finSumFinEquiv (Γ * blkMat finSumFinEquiv G 1 * Γi) :=
    keepsDiag_of_mulVec fun w hw => by
      obtain ⟨x, rfl⟩ := (mem_diagSub finSumFinEquiv).1 hw
      rw [hact]; exact (pairVec_mem_diagSub finSumFinEquiv).2 rfl
  have hmem : γ * io V (g, 1) * γ⁻¹ ∈ siegel V := mem_siegelOf.2 (by
    change KeepsDiag finSumFinEquiv (Formalism.L2.Theta.matHom (dblSp V) (γ * io V (g, 1) * γ⁻¹)).1
    rw [hMg]; exact hKD)
  have hlevi : leviMat finSumFinEquiv (Γ * blkMat finSumFinEquiv G 1 * Γi) = 1 + K.map (incA D) * A := by
    refine Matrix.ext_of_mulVec_single fun j => ?_
    have h := (hKD.mulVec_diag (Pi.single j 1)).symm.trans (hact _)
    funext i
    have := congrFun h (finSumFinEquiv (.inl i))
    rw [pairVec_inl, pairVec_inl] at this
    rw [this, add_mulVec, one_mulVec]
  refine ⟨hmem, Units.ext ?_⟩
  rw [Units.val_one]
  change (leviMat finSumFinEquiv (Formalism.L2.Theta.matHom (dblSp V) (γ * io V (g, 1) * γ⁻¹)).1).det = 1
  rw [hMg, hlevi, Matrix.det_one_add_mul_comm, hAK, add_zero, Matrix.det_one]

/- English proof (translation)
Introduce `D V γ hγ γi hγi r K hK hC n hn`. Set `φ : GA D V →* GA D (dblSp V)` to `(MulAut.conj γ).toMonoidHom.comp ((io V).comp (MonoidHom.inl _ _))`. Set `H : Subgroup (GA D (dblSp V))` to `(aP V).ker.map (siegel V).subtype`. Establish `hle : NI V (leviMat finSumFinEquiv γi * K) ≤ H.comap φ`. Use `(Subgroup.closure_le _).2 fun g hg => ?_` and prove the remaining obligations.

Take `⟨h1, -, h3⟩` from `hg`. Take `⟨hmem, ha⟩` from `conj_io_gen_mem V γ hγ γi hγi r K hK hC g h1 h3`. Conclude with `⟨⟨_, hmem⟩, ha, rfl⟩`. Take `⟨p, hp, hpe⟩` from `hle hn`. Use `⟨p, ?_, hp⟩` and prove the remaining obligations.

Establish `: (p : GA D (dblSp V)) = γ * io V (n, 1) * γ⁻¹` using `hpe`. Rewrite using `[this, inv_mul_cancel_right]`.
-/
theorem conj_io_unip_siegel : ∀ (D : D7) (V : HSp D), ∀ γ ∈ GQ (dblSp V), ∀ γi : Matrix (Fin (V.rank + V.rank)) (Fin (V.rank + V.rank)) D.host.E, (matHom (dblSp V) γ⁻¹).1 = γi.map (incA D) → ∀ (r : ℕ) (K : Matrix (Fin V.rank) (Fin r) D.host.E), diagSnd γi * K = 0 → IsIsoFrame V (leviMat finSumFinEquiv γi * K) → ∀ n ∈ NI V (leviMat finSumFinEquiv γi * K), ∃ p : siegel V, γ * io V (n, 1) = p * γ ∧ aP V p = 1 := by
  intro D V γ hγ γi hγi r K hK hC n hn
  let φ : GA D V →* GA D (dblSp V) := (MulAut.conj γ).toMonoidHom.comp ((io V).comp (MonoidHom.inl _ _))
  let H : Subgroup (GA D (dblSp V)) := (aP V).ker.map (siegel V).subtype
  have hle : NI V (leviMat finSumFinEquiv γi * K) ≤ H.comap φ := by
    refine (Subgroup.closure_le _).2 fun g hg => ?_
    obtain ⟨h1, -, h3⟩ := hg
    obtain ⟨hmem, ha⟩ := conj_io_gen_mem V γ hγ γi hγi r K hK hC g h1 h3
    exact ⟨⟨_, hmem⟩, ha, rfl⟩
  obtain ⟨p, hp, hpe⟩ := hle hn
  refine ⟨p, ?_, hp⟩
  have : (p : GA D (dblSp V)) = γ * io V (n, 1) * γ⁻¹ := hpe
  rw [this, inv_mul_cancel_right]

end GlobalTheory.Core.Rk.Dich

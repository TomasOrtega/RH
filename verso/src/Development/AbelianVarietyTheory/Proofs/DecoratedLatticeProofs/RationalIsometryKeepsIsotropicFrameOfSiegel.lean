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
Establish `h1 : (matHom (dblSp V) (io V (δ, 1))).1 = blkMat finSumFinEquiv (matHom V δ).1 1`. Rewrite using `[matHom_io, val_blkGL]`. Simplify using the standard rewrite rules. Rewrite using `[map_mul, map_mul, Units.val_mul, Units.val_mul, h1, hg1, hγi, hδ₀, Matrix.map_mul, Matrix.map_mul, blkMat_map _ _ (map_zero _), Matrix.map_one _ (map_zero _) (map_one _)]`.
-/
theorem matHom_conj_io (D : D7) (V : HSp D) (γ : GA D (dblSp V)) (δ : GA D V) (g : GL (Fin (V.rank + V.rank)) D.host.E)
    (γi : Matrix (Fin (V.rank + V.rank)) (Fin (V.rank + V.rank)) D.host.E) (δ₀ : Matrix (Fin V.rank) (Fin V.rank) D.host.E)
    (hg1 : (matHom (dblSp V) γ).1 = g.1.map (incA D)) (hγi : (matHom (dblSp V) γ⁻¹).1 = γi.map (incA D))
    (hδ₀ : (matHom V δ).1 = δ₀.map (incA D)) :
    (matHom (dblSp V) (γ * io V (δ, 1) * γ⁻¹)).1 = (g.1 * blkMat finSumFinEquiv δ₀ 1 * γi).map (incA D) := by
  have h1 : (matHom (dblSp V) (io V (δ, 1))).1 = blkMat finSumFinEquiv (matHom V δ).1 1 := by
    rw [matHom_io, val_blkGL]
    simp
  rw [map_mul, map_mul, Units.val_mul, Units.val_mul, h1, hg1, hγi, hδ₀, Matrix.map_mul, Matrix.map_mul,
    blkMat_map _ _ (map_zero _), Matrix.map_one _ (map_zero _) (map_one _)]

/- English proof (translation)
Introduce `D V γ hγ γi hγi r K hK hKsurj hC δ hδ δ₀ hδ₀ hsieg`. Establish `inj : Function.Injective (incA D)` using `Algebra.TensorProduct.includeRight_injective (AdeleRing.algebraMap_injective (𝓞 D.host.F) D.host.F)`. Take `⟨g, -, hg1, hg2⟩` from `exists_rat (dblSp V) hγ`. Take `⟨d, -, hd1, -⟩` from `exists_rat V hδ`. Establish `hγi' : γi = (g⁻¹).1` using `Matrix.map_injective inj (hγi.symm.trans hg2)`.

Establish `hδ₀' : δ₀ = d.1` using `Matrix.map_injective inj (hδ₀.symm.trans hd1)`. Establish `hgi0 : γi * g.1 = 1` using `by rw [hγi']; exact g.inv_mul`. Take `⟨X, hX⟩ : ∃ X, X = g.1 * blkMat finSumFinEquiv δ₀ 1 * γi` from `⟨_, rfl⟩`. Establish `hXmap` using `matHom_conj_io D V γ δ g γi δ₀ hg1 hγi hδ₀`. Rewrite `hXmap` using `[← hX]`.

Establish `hKX : KeepsDiag finSumFinEquiv X`. Establish `h : KeepsDiag finSumFinEquiv (matHom (dblSp V) (γ * io V (δ, 1) * γ⁻¹)).1` using `mem_siegelOf.1 hsieg`. Rewrite `h` using `[hXmap]`. Use `(keepsDiag_iff finSumFinEquiv).2 fun i j => inj ?_` and prove the remaining obligations. Simplify using `using (keepsDiag_iff finSumFinEquiv).1 h i j`.

Take `⟨C, hCdef⟩ : ∃ C, C = leviMat finSumFinEquiv γi * K` from `⟨_, rfl⟩`. Rewrite `hC`, the goal using `[← hCdef]`. Establish `key : ∀ v : Fin r → D.host.E, ∃ w, δ₀ *ᵥ (C *ᵥ v) = C *ᵥ w`. Introduce `v`. Establish `h1 : γi *ᵥ pairVec finSumFinEquiv (K *ᵥ v) (K *ᵥ v) = pairVec finSumFinEquiv (C *ᵥ v) 0`.

Rewrite using `[mulVec_pairVec_diag, mulVec_mulVec (M := diagSnd γi), hK, zero_mulVec, mulVec_mulVec, hCdef]`. Establish `h2 : X *ᵥ pairVec finSumFinEquiv (K *ᵥ v) (K *ᵥ v) = g.1 *ᵥ pairVec finSumFinEquiv (δ₀ *ᵥ (C *ᵥ v)) 0`. Rewrite using `[hX, ← mulVec_mulVec, ← mulVec_mulVec, h1, blkMat_mulVec, mulVec_zero]`. Establish `h3 : pairVec finSumFinEquiv (δ₀ *ᵥ (C *ᵥ v)) 0 = γi *ᵥ pairVec finSumFinEquiv (leviMat finSumFinEquiv X *ᵥ (K *ᵥ v)) (leviMat finSumFinEquiv X *ᵥ (K *ᵥ v))`. Rewrite using `[← hKX.mulVec_diag, h2, mulVec_mulVec (M := γi), hgi0, one_mulVec]`.

Rewrite `h3` using `[mulVec_pairVec_diag]`. Establish `h4a : δ₀ *ᵥ (C *ᵥ v) = leviMat finSumFinEquiv γi *ᵥ (leviMat finSumFinEquiv X *ᵥ (K *ᵥ v))`. Use function extensionality and compare the values at `i`. Use `congrFun h3 (finSumFinEquiv (.inl i))` as an intermediate fact. Rewrite `this` using `[pairVec_inl, pairVec_inl]`.

Conclude with `this`. Establish `h4b : diagSnd γi *ᵥ (leviMat finSumFinEquiv X *ᵥ (K *ᵥ v)) = 0`. Use function extensionality and compare the values at `i`. Use `congrFun h3 (finSumFinEquiv (.inr i))` as an intermediate fact. Rewrite `this` using `[pairVec_inr, pairVec_inr]`.

Conclude with `this.symm`. Take `⟨w, hw⟩` from `hKsurj _ h4b`. Conclude with `⟨w, by rw [h4a, hw, mulVec_mulVec, hCdef]⟩`. Use `choose w hw using fun j => key (Pi.single j 1)`. Establish `hCG : δ₀ * C = C * Matrix.of fun i j => w j i`.

Use `Matrix.ext fun i j => ?_` and prove the remaining obligations. Use `congrFun (hw j) i` as an intermediate fact. Rewrite `this` using `[mulVec_mulVec, mulVec_single_one]`. Simplify `this` using `[Matrix.mul_apply, mulVec, dotProduct, transpose_apply]`. Use `⟨Matrix.of fun i j => w j i, ?_, hCG⟩` and prove the remaining obligations.

Rewrite using `[← mulVec_injective_iff_isUnit]`. Introduce `a b hab`. Establish `h0 : (Matrix.of fun i j => w j i) *ᵥ (a - b) = 0` using `by rw [mulVec_sub, hab, sub_self]`. Establish `h5 : C *ᵥ (a - b) = 0`. Establish `h6 : δ₀ *ᵥ (C *ᵥ (a - b)) = 0` using `by rw [mulVec_mulVec, hCG, ← mulVec_mulVec, h0, mulVec_zero]`.

Establish `h7` using `congrArg (fun x => (d⁻¹).1 *ᵥ x) h6`. Simplify using `only [hδ₀', mulVec_mulVec, ← Matrix.mul_assoc, Units.inv_mul, Matrix.one_mul, mulVec_zero] at h7`. Conclude with `h7`. Take `⟨-, hli, -⟩` from `hC`. Establish `h8` using `Fintype.linearIndependent_iff.1 hli (a - b) (by`.

Use function extensionality and compare the values at `i`. Simplify `congrFun h5 i)` using `[Finset.sum_apply, mulVec, dotProduct, mul_comm]`. Conclude with `sub_eq_zero.1 (funext h8)`.
-/
theorem isoFrame_keep : ∀ (D : D7) (V : HSp D), ∀ γ ∈ GQ (dblSp V), ∀ γi : Matrix (Fin (V.rank + V.rank)) (Fin (V.rank + V.rank)) D.host.E, (matHom (dblSp V) γ⁻¹).1 = γi.map (incA D) → ∀ (r : ℕ) (K : Matrix (Fin V.rank) (Fin r) D.host.E), diagSnd γi * K = 0 → (∀ x : Fin V.rank → D.host.E, diagSnd γi *ᵥ x = 0 → ∃ y, x = K *ᵥ y) → IsIsoFrame V (leviMat finSumFinEquiv γi * K) → ∀ δ ∈ GQ V, ∀ δ₀ : Matrix (Fin V.rank) (Fin V.rank) D.host.E, (matHom V δ).1 = δ₀.map (incA D) → γ * io V (δ, 1) * γ⁻¹ ∈ siegel V → ∃ G : Matrix (Fin r) (Fin r) D.host.E, IsUnit G ∧ δ₀ * (leviMat finSumFinEquiv γi * K) = leviMat finSumFinEquiv γi * K * G := by
  intro D V γ hγ γi hγi r K hK hKsurj hC δ hδ δ₀ hδ₀ hsieg
  have inj : Function.Injective (incA D) :=
    Algebra.TensorProduct.includeRight_injective (AdeleRing.algebraMap_injective (𝓞 D.host.F) D.host.F)
  obtain ⟨g, -, hg1, hg2⟩ := exists_rat (dblSp V) hγ
  obtain ⟨d, -, hd1, -⟩ := exists_rat V hδ
  have hγi' : γi = (g⁻¹).1 := Matrix.map_injective inj (hγi.symm.trans hg2)
  have hδ₀' : δ₀ = d.1 := Matrix.map_injective inj (hδ₀.symm.trans hd1)
  have hgi0 : γi * g.1 = 1 := by rw [hγi']; exact g.inv_mul
  obtain ⟨X, hX⟩ : ∃ X, X = g.1 * blkMat finSumFinEquiv δ₀ 1 * γi := ⟨_, rfl⟩
  have hXmap := matHom_conj_io D V γ δ g γi δ₀ hg1 hγi hδ₀
  rw [← hX] at hXmap
  have hKX : KeepsDiag finSumFinEquiv X := by
    have h : KeepsDiag finSumFinEquiv (matHom (dblSp V) (γ * io V (δ, 1) * γ⁻¹)).1 := mem_siegelOf.1 hsieg
    rw [hXmap] at h
    refine (keepsDiag_iff finSumFinEquiv).2 fun i j => inj ?_
    simpa using (keepsDiag_iff finSumFinEquiv).1 h i j
  obtain ⟨C, hCdef⟩ : ∃ C, C = leviMat finSumFinEquiv γi * K := ⟨_, rfl⟩
  rw [← hCdef] at hC ⊢
  have key : ∀ v : Fin r → D.host.E, ∃ w, δ₀ *ᵥ (C *ᵥ v) = C *ᵥ w := by
    intro v
    have h1 : γi *ᵥ pairVec finSumFinEquiv (K *ᵥ v) (K *ᵥ v) = pairVec finSumFinEquiv (C *ᵥ v) 0 := by
      rw [mulVec_pairVec_diag, mulVec_mulVec (M := diagSnd γi), hK, zero_mulVec, mulVec_mulVec, hCdef]
    have h2 : X *ᵥ pairVec finSumFinEquiv (K *ᵥ v) (K *ᵥ v) =
        g.1 *ᵥ pairVec finSumFinEquiv (δ₀ *ᵥ (C *ᵥ v)) 0 := by
      rw [hX, ← mulVec_mulVec, ← mulVec_mulVec, h1, blkMat_mulVec, mulVec_zero]
    have h3 : pairVec finSumFinEquiv (δ₀ *ᵥ (C *ᵥ v)) 0 =
        γi *ᵥ pairVec finSumFinEquiv (leviMat finSumFinEquiv X *ᵥ (K *ᵥ v)) (leviMat finSumFinEquiv X *ᵥ (K *ᵥ v)) := by
      rw [← hKX.mulVec_diag, h2, mulVec_mulVec (M := γi), hgi0, one_mulVec]
    rw [mulVec_pairVec_diag] at h3
    have h4a : δ₀ *ᵥ (C *ᵥ v) = leviMat finSumFinEquiv γi *ᵥ (leviMat finSumFinEquiv X *ᵥ (K *ᵥ v)) := by
      funext i
      have := congrFun h3 (finSumFinEquiv (.inl i))
      rw [pairVec_inl, pairVec_inl] at this
      exact this
    have h4b : diagSnd γi *ᵥ (leviMat finSumFinEquiv X *ᵥ (K *ᵥ v)) = 0 := by
      funext i
      have := congrFun h3 (finSumFinEquiv (.inr i))
      rw [pairVec_inr, pairVec_inr] at this
      exact this.symm
    obtain ⟨w, hw⟩ := hKsurj _ h4b
    exact ⟨w, by rw [h4a, hw, mulVec_mulVec, hCdef]⟩
  choose w hw using fun j => key (Pi.single j 1)
  have hCG : δ₀ * C = C * Matrix.of fun i j => w j i := by
    refine Matrix.ext fun i j => ?_
    have := congrFun (hw j) i
    rw [mulVec_mulVec, mulVec_single_one] at this
    simpa [Matrix.mul_apply, mulVec, dotProduct, transpose_apply] using this
  refine ⟨Matrix.of fun i j => w j i, ?_, hCG⟩
  rw [← mulVec_injective_iff_isUnit]
  intro a b hab
  have h0 : (Matrix.of fun i j => w j i) *ᵥ (a - b) = 0 := by rw [mulVec_sub, hab, sub_self]
  have h5 : C *ᵥ (a - b) = 0 := by
    have h6 : δ₀ *ᵥ (C *ᵥ (a - b)) = 0 := by rw [mulVec_mulVec, hCG, ← mulVec_mulVec, h0, mulVec_zero]
    have h7 := congrArg (fun x => (d⁻¹).1 *ᵥ x) h6
    simp only [hδ₀', mulVec_mulVec, ← Matrix.mul_assoc, Units.inv_mul, Matrix.one_mul, mulVec_zero] at h7
    exact h7
  obtain ⟨-, hli, -⟩ := hC
  have h8 := Fintype.linearIndependent_iff.1 hli (a - b) (by
    funext i
    simpa [Finset.sum_apply, mulVec, dotProduct, mul_comm] using congrFun h5 i)
  exact sub_eq_zero.1 (funext h8)

end GlobalTheory.Core.Rk.Dich

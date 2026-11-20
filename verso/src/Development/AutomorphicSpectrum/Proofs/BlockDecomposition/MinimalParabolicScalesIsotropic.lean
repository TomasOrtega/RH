import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RatVInjective
open NumberField MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet PositivityTheory.ThKR GlobalTheory.CompanionTheory.RedCov
open Formalism.UG (cT)
open scoped TensorProduct NNReal ENNReal

noncomputable section

namespace GlobalTheory.CompanionTheory.RedCov

/- English proof (translation)
Introduce `F E _ _ _ _ _ σ hcm n J hJ r X Y hW δ hδ hp`. Establish `hF` using `pfrA hcm hJ hW`. Establish `hinc : Function.Injective (inclR (F` using `F) (E := E) (AF F)) := fun a b h => congrFun (ratV_injective (F := F) (n := 1) (a₁ := fun _ => a) (a₂ := fun _ => b) (funext fun _ => h)) 0`. Take `⟨g, hg⟩ : ∃ g : GL (Fin n) E, (matHom _ σ J δ).1 = (g : Matrix (Fin n) (Fin n) E).map (inclR (F` from `F) (AF F)) := by`. Take `⟨g, -, hg⟩` from `Subgroup.mem_map.1 (show (((show ↥(HR (AF F) σ J) from δ) : HR (AF F) σ J) : GL (Fin n) (AF F ⊗[F] E)) ∈ (Formalism.UG.UJ (σ : E →+* E) J).map (Formalism.UG.bc (inclR (AF F))) from hδ)`.

Conclude with `⟨g, (congrArg Units.val hg).symm⟩`. Use `set Bq : Matrix (Fin (r + 1)) (Fin (r + 1)) E := cT (σ : E →+* E) Y * J * ((g : Matrix (Fin n) (Fin n) E) * X) with hBq`. Establish `hBm : Bm σ J X Y δ = Bq.map (inclR (F` using `F) (AF F)) := by`. Unfold `Bm coefM JR`. Rewrite using `[hg, hBq, Matrix.map_mul, Matrix.map_mul, Matrix.map_mul, cT_map_inclR]`.

Take `⟨hbt, he⟩` from `(mem_minPar_iff hF).1 hp`. Rewrite `hbt`, `he` using `[hBm]`. Establish `hgX : (g : Matrix (Fin n) (Fin n) E) * X = X * Bq`. Apply `Matrix.map_injective hinc` to reduce the goal to its premises. Simplify using `only`.

Rewrite using `[Matrix.map_mul, Matrix.map_mul, ← hg]`. Conclude with `he`. Establish `hlow : ∀ k : Fin (r + 1), k ≠ 0 → Bq k 0 = 0` using `fun k hk => by`. Apply `hinc` to reduce the goal to its premises. Use `hbt (show id (0 : Fin (r + 1)) < id k from Fin.pos_of_ne_zero hk)` as an intermediate fact.

Simplify using `using this`. Establish `hcol : (g : Matrix (Fin n) (Fin n) E) *ᵥ Xᵀ 0 = Bq 0 0 • Xᵀ 0`. Use function extensionality and compare the values at `i`. Establish `h1` using `congrFun (congrFun hgX i) 0`. Rewrite `h1` using `[Matrix.mul_apply, Matrix.mul_apply, Finset.sum_eq_single (0 : Fin (r + 1)) (fun k _ hk => by rw [hlow k hk, mul_zero]) (fun h => absurd (Finset.mem_univ _) h)]`.

Simplify `h1` using `[Matrix.mulVec, dotProduct, mul_comm]`. Establish `hx : Xᵀ 0 ≠ 0` using `fun h0 => by`. Establish `h1` using `congrFun (congrFun hW.xy 0) 0`. Rewrite `h1` using `[GlobalTheory.SiegelSet.gram_apply, h0, map_zero, LinearMap.zero_apply, Matrix.one_apply_eq]`. Conclude with `zero_ne_one h1`.

Establish `hb : Bq 0 0 ≠ 0` using `fun h0 => hx (by`. Rewrite `hcol` using `[h0, zero_smul]`. Establish `h2` using `congrArg (fun v => ((g⁻¹ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) *ᵥ v) hcol`. Simplify `h2)` using `[Matrix.mulVec_mulVec, ← Units.val_mul]`. Use `⟨(Bq 0 0)⁻¹, inv_ne_zero hb, ?_⟩` and prove the remaining obligations.

Establish `h3 : (g : Matrix (Fin n) (Fin n) E) *ᵥ ((Bq 0 0)⁻¹ • Xᵀ 0) = Xᵀ 0`. Rewrite using `[Matrix.mulVec_smul, hcol, smul_smul, inv_mul_cancel₀ hb, one_smul]`. Unfold `Sends`. Rewrite using `[hg]`. Use function extensionality and compare the values at `i`.

Establish `h4` using `RingHom.map_mulVec (inclR (F := F) (E := E) (AF F)) (g : Matrix (Fin n) (Fin n) E) ((Bq 0 0)⁻¹ • Xᵀ 0) i`. Rewrite `h4` using `[h3]`. Conclude with `h4.symm`.
-/
theorem exists_sends_of_rat_mem_minPar : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J →
    ∀ (r : ℕ) (X Y : Matrix (Fin n) (Fin (r + 1)) E), IsWittFrame σ J X Y →
    ∀ δ ∈ ratPts σ J, δ ∈ minPar σ J X → ∃ e : E, e ≠ 0 ∧ Sends σ J δ (e • Xᵀ 0) (Xᵀ 0) := by
  intro F E _ _ _ _ _ σ hcm n J hJ r X Y hW δ hδ hp
  have hF := pfrA hcm hJ hW
  have hinc : Function.Injective (inclR (F := F) (E := E) (AF F)) := fun a b h =>
    congrFun (ratV_injective (F := F) (n := 1) (a₁ := fun _ => a) (a₂ := fun _ => b) (funext fun _ => h)) 0
  obtain ⟨g, hg⟩ : ∃ g : GL (Fin n) E,
      (matHom _ σ J δ).1 = (g : Matrix (Fin n) (Fin n) E).map (inclR (F := F) (AF F)) := by
    obtain ⟨g, -, hg⟩ := Subgroup.mem_map.1 (show (((show ↥(HR (AF F) σ J) from δ) : HR (AF F) σ J) :
      GL (Fin n) (AF F ⊗[F] E)) ∈ (Formalism.UG.UJ (σ : E →+* E) J).map (Formalism.UG.bc (inclR (AF F))) from hδ)
    exact ⟨g, (congrArg Units.val hg).symm⟩
  set Bq : Matrix (Fin (r + 1)) (Fin (r + 1)) E := cT (σ : E →+* E) Y * J * ((g : Matrix (Fin n) (Fin n) E) * X) with hBq
  have hBm : Bm σ J X Y δ = Bq.map (inclR (F := F) (AF F)) := by
    unfold Bm coefM JR
    rw [hg, hBq, Matrix.map_mul, Matrix.map_mul, Matrix.map_mul, cT_map_inclR]
  obtain ⟨hbt, he⟩ := (mem_minPar_iff hF).1 hp
  rw [hBm] at hbt he
  have hgX : (g : Matrix (Fin n) (Fin n) E) * X = X * Bq := by
    apply Matrix.map_injective hinc
    dsimp only
    rw [Matrix.map_mul, Matrix.map_mul, ← hg]
    exact he
  have hlow : ∀ k : Fin (r + 1), k ≠ 0 → Bq k 0 = 0 := fun k hk => by
    apply hinc
    have := hbt (show id (0 : Fin (r + 1)) < id k from Fin.pos_of_ne_zero hk)
    simpa using this
  have hcol : (g : Matrix (Fin n) (Fin n) E) *ᵥ Xᵀ 0 = Bq 0 0 • Xᵀ 0 := by
    funext i
    have h1 := congrFun (congrFun hgX i) 0
    rw [Matrix.mul_apply, Matrix.mul_apply, Finset.sum_eq_single (0 : Fin (r + 1))
      (fun k _ hk => by rw [hlow k hk, mul_zero]) (fun h => absurd (Finset.mem_univ _) h)] at h1
    simpa [Matrix.mulVec, dotProduct, mul_comm] using h1
  have hx : Xᵀ 0 ≠ 0 := fun h0 => by
    have h1 := congrFun (congrFun hW.xy 0) 0
    rw [GlobalTheory.SiegelSet.gram_apply, h0, map_zero, LinearMap.zero_apply, Matrix.one_apply_eq] at h1
    exact zero_ne_one h1
  have hb : Bq 0 0 ≠ 0 := fun h0 => hx (by
    rw [h0, zero_smul] at hcol
    have h2 := congrArg (fun v => ((g⁻¹ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) *ᵥ v) hcol
    simpa [Matrix.mulVec_mulVec, ← Units.val_mul] using h2)
  refine ⟨(Bq 0 0)⁻¹, inv_ne_zero hb, ?_⟩
  have h3 : (g : Matrix (Fin n) (Fin n) E) *ᵥ ((Bq 0 0)⁻¹ • Xᵀ 0) = Xᵀ 0 := by
    rw [Matrix.mulVec_smul, hcol, smul_smul, inv_mul_cancel₀ hb, one_smul]
  unfold Sends
  rw [hg]
  funext i
  have h4 := RingHom.map_mulVec (inclR (F := F) (E := E) (AF F)) (g : Matrix (Fin n) (Fin n) E) ((Bq 0 0)⁻¹ • Xᵀ 0) i
  rw [h3] at h4
  exact h4.symm

end GlobalTheory.CompanionTheory.RedCov

end

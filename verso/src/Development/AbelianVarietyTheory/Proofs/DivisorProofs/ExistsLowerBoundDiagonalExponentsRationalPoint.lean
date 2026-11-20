import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsLv
import Development.AbelianVarietyTheory.Definitions.Divisors.LocallyCompactUnipFlag
open scoped TensorProduct NNReal ENNReal Matrix
open NumberField MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.EisLine GlobalTheory.SphEis
open GlobalTheory.ResLine (IsHt SemiLat)
open GlobalTheory.Doubling (absE npow)
open Formalism.UG (cT bc)

noncomputable section

namespace GlobalTheory.SphEis

/- English proof (translation)
Introduce `F E _ _ _ _ _ σ n J j m C D Z J₀ hF lv hlv W hW`. Establish `: IsModuleTopology (AF F) (AF F ⊗[F] E)` using `⟨rfl⟩`. Establish `: IsTopologicalRing (AF F ⊗[F] E)` using `IsModuleTopology.isTopologicalRing (AF F) _`. Use `set P : Matrix (Fin j) (Fin n) (AF F ⊗[F] E) := adMat F (cT (σ : E →+* E) C * J) with hP`. Establish `hq : ∀ q ∈ fixG σ J C, P * (matHom _ σ J q).1 = P`.

Introduce `q hq`. Establish `h1 : (matHom _ σ J q⁻¹).1 * adMat F C = adMat F C * (1 : Matrix (Fin j) (Fin j) (AF F ⊗[F] E))`. Rewrite using `[Matrix.mul_one]`. Conclude with `inv_mem hq`. Establish `h` using `form_mul_of_mul_cols h1`.

Rewrite `h` using `[inv_inv, Formalism.UG.cT_one, Matrix.one_mul]`. Then use the resulting hypothesis. Establish `hl : ∀ α, P * (matHom _ σ J (lv α)).1 = cT (sigR (AF F) σ) (α⁻¹).1 * P`. Introduce `α`. Establish `h` using `form_mul_of_mul_cols (hlv.onC α⁻¹)`. Rewrite `h` using `[map_inv lv α, inv_inv]`. Then use the resulting hypothesis.

Establish `hc : Continuous fun w : GAd σ J => P * (matHom _ σ J w).1` using `continuous_const.matrix_mul (Units.continuous_val.comp (isEmbedding_matHom (AF F) σ J).continuous)`. Establish `hb : GlobalTheory.Eis.Conv.Bdd fun w : W => (w : GAd σ J)` using `⟨W, hW, fun w => w.2⟩`. Take `⟨Ω, hΩ, hΩw⟩` from `GlobalTheory.Eis.Conv.Bdd.entries (GlobalTheory.Eis.Conv.Bdd.map hb hc)`. Take `⟨m₀, hm₀⟩` from `(GlobalTheory.T.compact_adeles_rational_points_finite_eventually_zero F E Ω hΩ).2`. Use `⟨m₀, fun q hqm l w hw hg i => ?_⟩` and prove the remaining obligations.

Establish `ht : cT (sigR (AF F) σ) (tor F E l)⁻¹.1 = (tor F E l)⁻¹.1` using `congrArg Units.val (GlobalTheory.Eis.Conv.cti_dg (GlobalTheory.Eis.Conv.sigR_halfE σ) l)`. Establish `h1 : P * (matHom _ σ J (q * lv (tor F E l) * w)).1 = (tor F E l)⁻¹.1 * (P * (matHom _ σ J w).1)`. Rewrite using `[map_mul, map_mul, Units.val_mul, Units.val_mul, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hq q hqm, hl, ht, Matrix.mul_assoc]`. Generalize the expression as in `q * lv (tor F E l) * w = g at hg h1`. Establish `hg' : matHom _ σ J g ∈ HFin (AF F) σ J` using `Subgroup.mem_subgroupOf.1 hg`.

Take `⟨γ, -, e⟩` from `Subgroup.mem_map.1 hg'`. Establish `hm : (matHom _ σ J g).1 = γ.1.map (inclR (F` using `F) (AF F)) := by`. Rewrite using `[← e]`. Both sides reduce to the same expression. Establish `hy : (cT (σ : E →+* E) C * J * γ.1).map (inclR (F` using `F) (AF F)) = P * (matHom _ σ J g).1 := by`.

Rewrite using `[hm, Matrix.map_mul]`. Establish `hrow : ¬∀ x, (cT (σ : E →+* E) C * J * γ.1) i x = 0` using `GlobalTheory.GodementSectionReduction.row_ne_zero (N := γ⁻¹.1 * D) (by`. Rewrite using `[Matrix.mul_assoc, ← Matrix.mul_assoc γ.1, Units.mul_inv, Matrix.one_mul, hF.cd]) i`. Establish `hrow' : ¬∀ x, (cT (σ : E →+* E) C * J * γ.1).map (inclR (F` using `F) (AF F)) i x = 0 := fun h => hrow fun x => by`. Use `h x` as an intermediate fact.

Rewrite `this` using `[Matrix.map_apply, map_eq_zero_iff _ GlobalTheory.AutFunCompare.inclA_injective]`. Then use the resulting hypothesis. Conclude with `GlobalTheory.GodementSectionReduction.bound_aux (inclR (F := F) (AF F)) hm₀ (fun i x => hΩw ⟨w, hw⟩ i x) (hy.trans h1) i hrow'`.
-/
theorem exists_bound_exponents : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (j m : ℕ) (C D : Matrix (Fin n) (Fin j) E) (Z : Matrix (Fin n) (Fin m) E) (J₀ : Matrix (Fin m) (Fin m) E), Fr σ J C D Z J₀ → ∀ lv : GL (Fin j) (AF F ⊗[F] E) →* GAd σ J, IsLv σ J C D Z lv → ∀ W : Set (GAd σ J), IsCompact W → ∃ m₀ : ℕ, ∀ q ∈ fixG σ J C, ∀ l : Fin j → ℤ, ∀ w ∈ W, q * lv (tor F E l) * w ∈ ratPts σ J → ∀ i, -(m₀ : ℤ) ≤ l i := by
  intro F E _ _ _ _ _ σ n J j m C D Z J₀ hF lv hlv W hW
  have : IsModuleTopology (AF F) (AF F ⊗[F] E) := ⟨rfl⟩
  have : IsTopologicalRing (AF F ⊗[F] E) := IsModuleTopology.isTopologicalRing (AF F) _
  set P : Matrix (Fin j) (Fin n) (AF F ⊗[F] E) := adMat F (cT (σ : E →+* E) C * J) with hP
  have hq : ∀ q ∈ fixG σ J C, P * (matHom _ σ J q).1 = P := by
    intro q hq
    have h1 : (matHom _ σ J q⁻¹).1 * adMat F C = adMat F C * (1 : Matrix (Fin j) (Fin j) (AF F ⊗[F] E)) := by
      rw [Matrix.mul_one]; exact inv_mem hq
    have h := form_mul_of_mul_cols h1
    rwa [inv_inv, Formalism.UG.cT_one, Matrix.one_mul] at h
  have hl : ∀ α, P * (matHom _ σ J (lv α)).1 = cT (sigR (AF F) σ) (α⁻¹).1 * P := by
    intro α
    have h := form_mul_of_mul_cols (hlv.onC α⁻¹)
    rwa [map_inv lv α, inv_inv] at h
  have hc : Continuous fun w : GAd σ J => P * (matHom _ σ J w).1 :=
    continuous_const.matrix_mul (Units.continuous_val.comp (isEmbedding_matHom (AF F) σ J).continuous)
  have hb : GlobalTheory.Eis.Conv.Bdd fun w : W => (w : GAd σ J) := ⟨W, hW, fun w => w.2⟩
  obtain ⟨Ω, hΩ, hΩw⟩ := GlobalTheory.Eis.Conv.Bdd.entries (GlobalTheory.Eis.Conv.Bdd.map hb hc)
  obtain ⟨m₀, hm₀⟩ := (GlobalTheory.T.compact_adeles_rational_points_finite_eventually_zero F E Ω hΩ).2
  refine ⟨m₀, fun q hqm l w hw hg i => ?_⟩
  have ht : cT (sigR (AF F) σ) (tor F E l)⁻¹.1 = (tor F E l)⁻¹.1 :=
    congrArg Units.val (GlobalTheory.Eis.Conv.cti_dg (GlobalTheory.Eis.Conv.sigR_halfE σ) l)
  have h1 : P * (matHom _ σ J (q * lv (tor F E l) * w)).1 = (tor F E l)⁻¹.1 * (P * (matHom _ σ J w).1) := by
    rw [map_mul, map_mul, Units.val_mul, Units.val_mul, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hq q hqm, hl, ht,
      Matrix.mul_assoc]
  generalize q * lv (tor F E l) * w = g at hg h1
  have hg' : matHom _ σ J g ∈ HFin (AF F) σ J := Subgroup.mem_subgroupOf.1 hg
  obtain ⟨γ, -, e⟩ := Subgroup.mem_map.1 hg'
  have hm : (matHom _ σ J g).1 = γ.1.map (inclR (F := F) (AF F)) := by
    rw [← e]; rfl
  have hy : (cT (σ : E →+* E) C * J * γ.1).map (inclR (F := F) (AF F)) = P * (matHom _ σ J g).1 := by
    rw [hm, Matrix.map_mul]
  have hrow : ¬∀ x, (cT (σ : E →+* E) C * J * γ.1) i x = 0 :=
    GlobalTheory.GodementSectionReduction.row_ne_zero (N := γ⁻¹.1 * D) (by
      rw [Matrix.mul_assoc, ← Matrix.mul_assoc γ.1, Units.mul_inv, Matrix.one_mul, hF.cd]) i
  have hrow' : ¬∀ x, (cT (σ : E →+* E) C * J * γ.1).map (inclR (F := F) (AF F)) i x = 0 := fun h =>
    hrow fun x => by
      have := h x
      rwa [Matrix.map_apply, map_eq_zero_iff _ GlobalTheory.AutFunCompare.inclA_injective] at this
  exact GlobalTheory.GodementSectionReduction.bound_aux (inclR (F := F) (AF F)) hm₀ (fun i x => hΩw ⟨w, hw⟩ i x) (hy.trans h1) i hrow'

end GlobalTheory.SphEis

end

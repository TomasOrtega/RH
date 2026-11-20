import Mathlib
import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.ModelsAt
import Development.AbelianVarietyTheory.Definitions.RegularCharts.BaseNorm
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.SmulMemOfIsIntegral

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FreeQuotientRank
open Formalism.L2.Pj Formalism.L2.PjFree Formalism.L2.Pj.QAt Formalism.L2.LamCM GlobalTheory GlobalTheory.ArcQ GlobalTheory.LamF GlobalTheory.ArcCM
open scoped LaurentSeries

namespace GlobalTheory.TransvPrinc

/- English proof (translation)
Introduce `ξ hξ s hs hc`. Establish `hκ : cc (s * X.κ0) = -(s * X.κ0)`. Establish `h0` using `X.ξ0_im`. Simplify using `only [cc] at hs h0 ⊢`. Apply the tactic sequence `rcases X.κ0_xi with h | h <;> simp [h, hs, h0, map_ofNat]`.

Establish `hn : ∀ (n : ℕ) u, u ∈ X.Λ → (n : E) • u ∈ X.Λ` using `fun n u hu => by`. Rewrite using `[Nat.cast_smul_eq_nsmul]`. Conclude with `nsmul_mem hu n`. Establish `hmem : GlobalTheory.FlagData.transv X.Gm hξ.2.1 (s * X.κ0) ∈ X.Γ`. Use `hP _ ⟨fun x y => ?_, fun x => ⟨fun hx => ?_, fun hx => ?_⟩⟩ (fun x hx => ?_)` and prove the remaining obligations.

Conclude with `GlobalTheory.FlagData.herm_transvMat X.Gm_herm hξ.2.1 hκ x y`. Take `⟨u, hu, e⟩` from `hc x hx`. Rewrite `e` using `[sub_eq_iff_eq_add]`. Express the relevant statement in the definitionally equal form `(transvMat _ _ _).mulVec x ∈ _`. Rewrite using `[e]`.

Conclude with `add_mem (hn _ u hu) hx`. Express the relevant statement in the definitionally equal form `(transvMat _ _ _).mulVec x ∈ _ at hx`. Take `⟨u, hu, e⟩` from `hc _ hx`. Establish `: x = (transvMat X.Gm ξ (s * X.κ0)).mulVec x - (N : E) • u`. Rewrite using `[← e, GlobalTheory.FlagData.transvMat_mulVec _ _ (Matrix.mulVec _ _), GlobalTheory.FlagData.transvMat_mulVec, GlobalTheory.FlagData.herm_add_smul_left, hξ.2.1]`.

Simplify using the standard rewrite rules. Rewrite using `[this]`. Conclude with `sub_mem hx (hn _ u hu)`. Take `⟨m, hm⟩` from `hMN`. Take `⟨u, hu, e⟩` from `hc x hx`.

Use `⟨(m : E) • u, hn m u hu, ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `(transvMat _ _ _).mulVec x - x = _`. Rewrite using `[e, hm, smul_smul]`. Use `push_cast`. Both sides reduce to the same expression.

Conclude with `⟨_, hmem, rfl, hχ _ hmem⟩`.
-/
theorem transvIn_of_princ {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r) {M N : ℕ}
    (hMN : M ∣ N) (la : Wt X.Ψ r)
    (hP : ∀ gm : GL (Fin r) E, IsUStab X.Gm X.Λ gm →
      (∀ x ∈ X.Λ, ∃ y ∈ X.Λ, Matrix.mulVec (gm : Matrix (Fin r) (Fin r) E) x - x = (M : E) • y) → gm ∈ X.Γ)
    (hχ : ∀ gm ∈ X.Γ, X.χ la gm = 1) : TransvIn X N la := by
  intro ξ hξ s hs hc
  have hκ : cc (s * X.κ0) = -(s * X.κ0) := by
    have h0 := X.ξ0_im
    simp only [cc] at hs h0 ⊢
    rcases X.κ0_xi with h | h <;> simp [h, hs, h0, map_ofNat]
  have hn : ∀ (n : ℕ) u, u ∈ X.Λ → (n : E) • u ∈ X.Λ := fun n u hu => by
    rw [Nat.cast_smul_eq_nsmul]; exact nsmul_mem hu n
  have hmem : GlobalTheory.FlagData.transv X.Gm hξ.2.1 (s * X.κ0) ∈ X.Γ := by
    refine hP _ ⟨fun x y => ?_, fun x => ⟨fun hx => ?_, fun hx => ?_⟩⟩ (fun x hx => ?_)
    · exact GlobalTheory.FlagData.herm_transvMat X.Gm_herm hξ.2.1 hκ x y
    · obtain ⟨u, hu, e⟩ := hc x hx
      rw [sub_eq_iff_eq_add] at e
      change (transvMat _ _ _).mulVec x ∈ _
      rw [e]; exact add_mem (hn _ u hu) hx
    · change (transvMat _ _ _).mulVec x ∈ _ at hx
      obtain ⟨u, hu, e⟩ := hc _ hx
      have : x = (transvMat X.Gm ξ (s * X.κ0)).mulVec x - (N : E) • u := by
        rw [← e, GlobalTheory.FlagData.transvMat_mulVec _ _ (Matrix.mulVec _ _), GlobalTheory.FlagData.transvMat_mulVec,
          GlobalTheory.FlagData.herm_add_smul_left, hξ.2.1]
        simp
      rw [this]; exact sub_mem hx (hn _ u hu)
    · obtain ⟨m, hm⟩ := hMN
      obtain ⟨u, hu, e⟩ := hc x hx
      refine ⟨(m : E) • u, hn m u hu, ?_⟩
      change (transvMat _ _ _).mulVec x - x = _
      rw [e, hm, smul_smul]
      push_cast; rfl
  exact ⟨_, hmem, rfl, hχ _ hmem⟩

/- English proof (translation)
Introduce `E _ _ _ H Dw l Xo c σ r U a' n hP hχ k`. Conclude with `transvIn_of_princ (U.X k) (Nat.dvd_lcm_left _ _) _ (hP k) (hχ k)`.
-/
theorem transvIn_of_hasPrinc : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (r : ℕ) (U : Unf Xo c σ r) (a' : (E →+* ℂ) × ℕ → ℕ) (n : ℕ), GlobalTheory.FrameNorm.HasPrinc U l.M → (∀ k, ∀ gm ∈ (U.X k).Γ, (U.X k).χ (laU U a' n k) gm = 1) → ∀ k, TransvIn (U.X k) l.M' (laU U a' n k) := by
  intro E _ _ _ H Dw l Xo c σ r U a' n hP hχ k
  exact transvIn_of_princ (U.X k) (Nat.dvd_lcm_left _ _) _ (hP k) (hχ k)

end GlobalTheory.TransvPrinc

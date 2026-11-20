import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.TiedAt
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TensorOneApply
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LocalSelfDualLatticeSplitPlaceDecomposition
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ContinuousSingleAt
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPlaceIdempotentMulIdemSumEqZeroOfNotMem
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ContinuousSplitPlaceHermitianFrameGLEmbedding
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPlaceCharacterConductorIntegers

noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.SeeSaw GlobalTheory.AdForm GlobalTheory.LocMod
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.LocMod.StdHomDown

variable {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

/- English proof (translation)
Establish `h1 : IsIntegral ℤ (q.pr (incA D x))` using `hx.map ((q.pr.comp (incA D)).toIntAlgHom)`. Conclude with `(Valuation.integer.integers (valuation k)).mem_of_integral h1.tower_top`.
-/
theorem pr_int_of_isIntegral (q : GlobalTheory.FinPl.SplitPt D k) {x : D.host.E} (hx : IsIntegral ℤ x) :
    q.pr (incA D x) ∈ 𝒪[k] := by
  have h1 : IsIntegral ℤ (q.pr (incA D x)) := hx.map ((q.pr.comp (incA D)).toIntAlgHom)
  exact (Valuation.integer.integers (valuation k)).mem_of_integral h1.tower_top

/- English proof (translation)
The claim follows from `hx.map (starRingEnd D.host.E).toIntAlgHom`.
-/
theorem star_isIntegral {x : D.host.E} (hx : IsIntegral ℤ x) : IsIntegral ℤ (star x) :=
  hx.map (starRingEnd D.host.E).toIntAlgHom

/- English proof (translation)
Express the relevant statement in the definitionally equal form `_ = (α ⊗ₜ[D.host.F] (1 : D.host.E)) * ((1 : AF D.host.F) ⊗ₜ[D.host.F] y)`. Rewrite using `[Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]`.
-/
theorem tmul_eq (α : AF D.host.F) (y : D.host.E) :
    (α ⊗ₜ[D.host.F] y : AE D) = algebraMap (AF D.host.F) (AE D) α * incA D y := by
  change _ = (α ⊗ₜ[D.host.F] (1 : D.host.E)) * ((1 : AF D.host.F) ⊗ₜ[D.host.F] y)
  rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]

/- English proof (translation)
Introduce `D k _ _ _ _ q S T c hc hAA FS FT _ hγT hγS u hu`. Use `set Gw : Matrix (Fin S.rank) (Fin S.rank) k := (HSpace.gram S).map (fun a => q.pr (incA D a)) with hGw`. Establish `hGβ : Gw * FS.β = c⁻¹ • (1 : Matrix (Fin S.rank) (Fin S.rank) k)`. Establish `h` using `FS.γβ`. Rewrite `h` using `[hγS, Matrix.smul_mul]`.

Rewrite using `[← h, smul_smul, inv_mul_cancel₀ hc, one_smul]`. Proceed by induction on `hu using AddSubgroup.closure_induction with`. Consider the case `mem w hw`. Take `⟨α, hα, -, a, ha, s, hs, t, ht, rfl⟩` from `hw`. Introduce `r j`.

Use `set lam : k := q.pr (algebraMap (AF D.host.F) (AE D) (pairA D.host.F 0 α)) * q.pr (incA D a) with hlam`. Set `M : Matrix (Fin T.rank) (Fin S.rank) k` to `Matrix.of fun i l => lam * q.pr (incA D (t i)) * q.pr (incA D (star (s l)))`. Establish `hmap : (Matrix.of fun i j => (pairA D.host.F 0 α) ⊗ₜ[D.host.F] (a * t i * ∑ l, star (s l) * S.gram l j) : WO S T).map q.pr = M * Gw`. Use extensionality with `i j`. Simplify using `only [Matrix.map_apply, Matrix.of_apply, Matrix.mul_apply, M, hGw, tmul_eq, map_mul, map_sum, hlam]`.

Simplify using `only [Finset.mul_sum]`. Conclude with `Finset.sum_congr rfl fun l _ => by ring`. Establish `hd : (Place.ofSplitPt q).down FS FT (Matrix.of fun i j => (pairA D.host.F 0 α) ⊗ₜ[D.host.F] (a * t i * ∑ l, star (s l) * S.gram l j)) = c⁻¹ • M`. Establish `hπ : (Place.ofSplitPt q).π = q.pr` using `rfl`. Simplify using `only [Place.down, hπ]`.

Rewrite using `[hγT, Matrix.one_mul, hmap, Matrix.mul_assoc, hGβ, Matrix.mul_smul, Matrix.mul_one]`. Rewrite using `[hd, Matrix.smul_apply, smul_eq_mul]`. Establish `e : c⁻¹ * M r j = q.pr (algebraMap (AF D.host.F) (AE D) (pairA D.host.F 0 α)) * (q.pr (incA D a) / c) * q.pr (incA D (t r)) * q.pr (incA D (star (s j)))`. Simplify using `only [M, Matrix.of_apply, hlam]`. Clear the denominators using the available nonvanishing facts.

Rewrite using `[e]`. Use `mul_mem (mul_mem (mul_mem (GlobalTheory.SplitCharCond.pr_pair_int q hα) (hAA a ha)) ?_) ?_` and prove the remaining obligations. Conclude with `pr_int_of_isIntegral q (ht r)`. Conclude with `pr_int_of_isIntegral q (star_isIntegral (hs j))`. Consider the case `zero`.

Introduce `r j`. Establish `: (Place.ofSplitPt q).down FS FT 0 = 0` using `map_zero (Witness.downH (Place.ofSplitPt q) FS FT)`. Rewrite using `[this]`. Conclude with `zero_mem _`. Consider the case `add x y _ _ hx hy`.

Introduce `r j`. Rewrite using `[Witness.down_add, Matrix.add_apply]`. Conclude with `add_mem (hx r j) (hy r j)`. Consider the case `neg x _ hx`. Introduce `r j`.

Establish `: (Place.ofSplitPt q).down FS FT (-x) = -(Place.ofSplitPt q).down FS FT x` using `map_neg (Witness.downH (Place.ofSplitPt q) FS FT) x`. Rewrite using `[this, Matrix.neg_apply]`. Conclude with `neg_mem (hx r j)`.
-/
theorem down_mem_integer : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (q : GlobalTheory.FinPl.SplitPt D k) (S T : HSp D) (c : k), c ≠ 0 → (∀ a ∈ (D.host.AA : Set D.host.E), q.pr (incA D a) / c ∈ 𝒪[k]) → ∀ (FS : Frame k S.rank (Fin S.rank)) (FT : Frame k T.rank (Fin T.rank)), FT.β = 1 → FT.γ = 1 → FS.γ = c • (HSpace.gram S).map (fun a => q.pr (incA D a)) → ∀ u ∈ stdHom S T, ∀ r s, (Place.ofSplitPt q).down FS FT u r s ∈ 𝒪[k] := by
  intro D k _ _ _ _ q S T c hc hAA FS FT _ hγT hγS u hu
  set Gw : Matrix (Fin S.rank) (Fin S.rank) k := (HSpace.gram S).map (fun a => q.pr (incA D a)) with hGw
  have hGβ : Gw * FS.β = c⁻¹ • (1 : Matrix (Fin S.rank) (Fin S.rank) k) := by
    have h := FS.γβ
    rw [hγS, Matrix.smul_mul] at h
    rw [← h, smul_smul, inv_mul_cancel₀ hc, one_smul]
  induction hu using AddSubgroup.closure_induction with
  | mem w hw =>
    obtain ⟨α, hα, -, a, ha, s, hs, t, ht, rfl⟩ := hw
    intro r j
    set lam : k := q.pr (algebraMap (AF D.host.F) (AE D) (pairA D.host.F 0 α)) * q.pr (incA D a) with hlam
    let M : Matrix (Fin T.rank) (Fin S.rank) k := Matrix.of fun i l => lam * q.pr (incA D (t i)) * q.pr (incA D (star (s l)))
    have hmap : (Matrix.of fun i j => (pairA D.host.F 0 α) ⊗ₜ[D.host.F] (a * t i * ∑ l, star (s l) * S.gram l j) :
        WO S T).map q.pr = M * Gw := by
      ext i j
      simp only [Matrix.map_apply, Matrix.of_apply, Matrix.mul_apply, M, hGw, tmul_eq, map_mul, map_sum, hlam]
      simp only [Finset.mul_sum]
      exact Finset.sum_congr rfl fun l _ => by ring
    have hd : (Place.ofSplitPt q).down FS FT (Matrix.of fun i j => (pairA D.host.F 0 α) ⊗ₜ[D.host.F]
        (a * t i * ∑ l, star (s l) * S.gram l j)) = c⁻¹ • M := by
      have hπ : (Place.ofSplitPt q).π = q.pr := rfl
      simp only [Place.down, hπ]
      rw [hγT, Matrix.one_mul, hmap, Matrix.mul_assoc, hGβ, Matrix.mul_smul, Matrix.mul_one]
    rw [hd, Matrix.smul_apply, smul_eq_mul]
    have e : c⁻¹ * M r j = q.pr (algebraMap (AF D.host.F) (AE D) (pairA D.host.F 0 α)) * (q.pr (incA D a) / c) *
        q.pr (incA D (t r)) * q.pr (incA D (star (s j))) := by
      simp only [M, Matrix.of_apply, hlam]; field_simp
    rw [e]
    refine mul_mem (mul_mem (mul_mem (GlobalTheory.SplitCharCond.pr_pair_int q hα) (hAA a ha)) ?_) ?_
    · exact pr_int_of_isIntegral q (ht r)
    · exact pr_int_of_isIntegral q (star_isIntegral (hs j))
  | zero =>
    intro r j
    have : (Place.ofSplitPt q).down FS FT 0 = 0 := map_zero (Witness.downH (Place.ofSplitPt q) FS FT)
    rw [this]; exact zero_mem _
  | add x y _ _ hx hy =>
    intro r j
    rw [Witness.down_add, Matrix.add_apply]
    exact add_mem (hx r j) (hy r j)
  | neg x _ hx =>
    intro r j
    have : (Place.ofSplitPt q).down FS FT (-x) = -(Place.ofSplitPt q).down FS FT x :=
      map_neg (Witness.downH (Place.ofSplitPt q) FS FT) x
    rw [this, Matrix.neg_apply]
    exact neg_mem (hx r j)

end GlobalTheory.LocMod.StdHomDown
end

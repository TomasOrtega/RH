import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFramePullbackSections
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.VB GlobalTheory.FlagBundle GlobalTheory.ProjVar GlobalTheory.FlagCell GlobalTheory.CovTest GlobalTheory.FlagOverField
open scoped Classical

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.FlagOverField

open GlobalTheory.Cartier

variable {F : Type} [Field F] {Y : Var F}

/- English proof (translation)
Establish `hd : ((N.map (fnOf W (gen_mem hy))).transpose).det = fnOf W (gen_mem hy) N.det`. Rewrite using `[Matrix.det_transpose, RingHom.map_det]`. Both sides reduce to the same expression. Establish `hu : UnitAt y (fnOf W (gen_mem hy) N.det)` using `unitAt_fnOf hy (gen_mem hy) hN.unit`. Use `⟨fun i j => regAt_fnOf hy _ _, ?_, ?_⟩` and prove the remaining obligations.

Rewrite using `[hd]`. Conclude with `hu.ne_zero`. Rewrite using `[hd]`. Conclude with `hu.inv.regAt`.
-/
theorem par_transpose_fnOf {n : ℕ} {y : Y.X} {W : Y.X.Opens} (hy : y ∈ W)
    (N : Matrix (Fin n) (Fin n) Γ(Y.X, W)) (hN : IsUnit N.det) :
    (∀ i j, RegAt y ((N.map (fnOf W (gen_mem hy))).transpose i j)) ∧
      ((N.map (fnOf W (gen_mem hy))).transpose).det ≠ 0 ∧
      RegAt y ((N.map (fnOf W (gen_mem hy))).transpose).det⁻¹ := by
  have hd : ((N.map (fnOf W (gen_mem hy))).transpose).det = fnOf W (gen_mem hy) N.det := by
    rw [Matrix.det_transpose, RingHom.map_det]; rfl
  have hu : UnitAt y (fnOf W (gen_mem hy) N.det) := unitAt_fnOf hy (gen_mem hy) hN.unit
  refine ⟨fun i j => regAt_fnOf hy _ _, ?_, ?_⟩
  · rw [hd]; exact hu.ne_zero
  · rw [hd]; exact hu.inv.regAt

/- English proof (translation)
Introduce `F _ Y ι _ r E e fl hE he y A hA`. Establish `hO : ∀ g : Y.Fn, RegAt y g → g ∈ ((ratOf Y).O y).toSubring` using `fun g hg => mem_O_ratOf.2 hg`. Establish `hdet : ∀ a, (A a).det ≠ 0` using `fun a => by`. Take `⟨U, hy, M, hM, hA⟩` from `hA a`. Use `haveI := (hE a).isQuasicoherent`.

Rewrite using `[hA]`. Conclude with `(par_transpose_fnOf hy M (isUnit_det_of_spans Y.str (he a) le_top hM)).2.1`. Use `⟨fun a => ?_, fun A' hA' a => ?_⟩` and prove the remaining obligations. Take `⟨U, hy, M, hM, hA⟩` from `hA a haveI := (hE a).isQuasicoherent`. Establish `h` using `par_transpose_fnOf hy M (isUnit_det_of_spans Y.str (he a) le_top hM)`.

Rewrite using `[hA]`. Conclude with `⟨fun i j => hO _ (h.1 i j), h.2.1, hO _ h.2.2, fun i j hi => absurd hi (Nat.not_lt_zero _)⟩`. Take `⟨U, hy, M, hM, hA⟩` from `hA a`. Take `⟨U', hy', M', hM', hA'⟩` from `hA' a`. Use `haveI := (hE a).isQuasicoherent`.

Establish `hyW : y ∈ U ⊓ U'` using `⟨hy, hy'⟩`. Establish `h₁` using `spans_pullCol_res Y.str (e a) le_top (inf_le_left : U ⊓ U' ≤ U) hM`. Establish `h₂` using `spans_pullCol_res Y.str (e a) le_top (inf_le_right : U ⊓ U' ≤ U') hM'`. Take `⟨T, hT, hTu, hTe⟩` from `exists_upper_of_spans Y.str (he a) (le_top.trans le_top) h₁ h₂`. Use `set φ := fnOf (U ⊓ U') (gen_mem hyW)`.

Establish `eA : A a = ((M.map (resG Y.X inf_le_left)).map φ).transpose`. Rewrite using `[hA]`. Use `congr 1`. Use extensionality with `i j`. Simplify using `[φ]`.

Establish `eA' : A' a = ((M'.map (resG Y.X inf_le_right)).map φ).transpose`. Rewrite using `[hA']`. Use `congr 1`. Use extensionality with `i j`. Simplify using `[φ]`.

Establish `key : (A' * A⁻¹) a = (T.map φ).transpose`. Rewrite using `[Pi.mul_apply, Pi.inv_apply, eA', hTe, Matrix.map_mul, Matrix.transpose_mul, ← eA, Matrix.mul_assoc, Matrix.mul_nonsing_inv _ (Ne.isUnit (hdet a)), Matrix.mul_one]`. Establish `h` using `par_transpose_fnOf hyW T hTu`. Rewrite using `[key]`. Use `⟨fun i j => hO _ (h.1 i j), h.2.1, hO _ h.2.2, fun i j _ hij => ?_⟩` and prove the remaining obligations.

Use `show φ (T j i) = 0`. Rewrite using `[hT hij, map_zero]`.
-/
theorem adFrame_par : ∀ (F : Type) [Field F] (Y : Var F) (ι : Type) [Fintype ι] (r : ι → ℕ) (E : ι → (Sp F).Modules) (e : ∀ a, Fin (r a) → Γ(E a, ⊤)) (fl : ∀ a, Vert.Flag ((Scheme.Modules.pullback Y.str).obj (E a)) (r a)), (∀ a, IsVB (E a) (r a)) → (∀ a, IsFrame (e a)) → ∀ (y : Y.X) (A : Mat r Y.Fn), AdFrame e fl y A → Par 0 ((ratOf Y).O y).toSubring A ∧ ∀ A' : Mat r Y.Fn, AdFrame e fl y A' → Par r ((ratOf Y).O y).toSubring (A' * A⁻¹) := by
  intro F _ Y ι _ r E e fl hE he y A hA
  have hO : ∀ g : Y.Fn, RegAt y g → g ∈ ((ratOf Y).O y).toSubring := fun g hg => mem_O_ratOf.2 hg
  have hdet : ∀ a, (A a).det ≠ 0 := fun a => by
    obtain ⟨U, hy, M, hM, hA⟩ := hA a
    haveI := (hE a).isQuasicoherent
    rw [hA]
    exact (par_transpose_fnOf hy M (isUnit_det_of_spans Y.str (he a) le_top hM)).2.1
  refine ⟨fun a => ?_, fun A' hA' a => ?_⟩
  · obtain ⟨U, hy, M, hM, hA⟩ := hA a
    haveI := (hE a).isQuasicoherent
    have h := par_transpose_fnOf hy M (isUnit_det_of_spans Y.str (he a) le_top hM)
    rw [hA]
    exact ⟨fun i j => hO _ (h.1 i j), h.2.1, hO _ h.2.2, fun i j hi => absurd hi (Nat.not_lt_zero _)⟩
  · obtain ⟨U, hy, M, hM, hA⟩ := hA a
    obtain ⟨U', hy', M', hM', hA'⟩ := hA' a
    haveI := (hE a).isQuasicoherent
    have hyW : y ∈ U ⊓ U' := ⟨hy, hy'⟩
    have h₁ := spans_pullCol_res Y.str (e a) le_top (inf_le_left : U ⊓ U' ≤ U) hM
    have h₂ := spans_pullCol_res Y.str (e a) le_top (inf_le_right : U ⊓ U' ≤ U') hM'
    obtain ⟨T, hT, hTu, hTe⟩ := exists_upper_of_spans Y.str (he a) (le_top.trans le_top) h₁ h₂
    set φ := fnOf (U ⊓ U') (gen_mem hyW)
    have eA : A a = ((M.map (resG Y.X inf_le_left)).map φ).transpose := by
      rw [hA]; congr 1; ext i j; simp [φ]
    have eA' : A' a = ((M'.map (resG Y.X inf_le_right)).map φ).transpose := by
      rw [hA']; congr 1; ext i j; simp [φ]
    have key : (A' * A⁻¹) a = (T.map φ).transpose := by
      rw [Pi.mul_apply, Pi.inv_apply, eA', hTe, Matrix.map_mul, Matrix.transpose_mul, ← eA, Matrix.mul_assoc,
        Matrix.mul_nonsing_inv _ (Ne.isUnit (hdet a)), Matrix.mul_one]
    have h := par_transpose_fnOf hyW T hTu
    rw [key]
    refine ⟨fun i j => hO _ (h.1 i j), h.2.1, hO _ h.2.2, fun i j _ hij => ?_⟩
    show φ (T j i) = 0
    rw [hT hij, map_zero]

end GlobalTheory.FlagOverField

import Mathlib
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsStabForm
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.WeilActionPreservesThetaAndInnerProduct
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.LevelStructureProperties
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.TensorLatticeVacuaExistUnique

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level
open GlobalTheory.SW hiding Level
open Formalism.L2.Pj Formalism.L2.PjFree
open scoped ComplexConjugate Classical
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Dict

namespace GlobalTheory.Dict

/- English proof (translation)
Unfold `mapL`. Simplify using the standard rewrite rules.
-/
private lemma mapL_one' {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (L : Lt E r) : mapL (1 : GL (Fin r) E) L = L := by
  unfold mapL
  simp

/- English proof (translation)
Unfold `mapL`. Rewrite using `[← Submodule.map_comp]`. Use `congr 1`. Use `LinearMap.ext fun v => ?_` and prove the remaining obligations. Simplify using `[Matrix.mulVec_mulVec]`.
-/
private lemma mapL_mul' {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (a b : GL (Fin r) E) (L : Lt E r) :
    mapL (a * b) L = mapL a (mapL b L) := by
  unfold mapL
  rw [← Submodule.map_comp]
  congr 1
  refine LinearMap.ext fun v => ?_
  simp [Matrix.mulVec_mulVec]

/- English proof (translation)
Establish `ha` using `TensVac.ip_smul_left a hv hv`. Establish `hb` using `TensVac.ip_smul_left b hv hv`. Rewrite `ha`, `hb` using `[h1, _root_.mul_one]`. Rewrite using `[← ha, ← hb, h]`.
-/
private lemma smul_left_cancel_of_ip_self_eq_one {n g : ℕ} {v : TF n g} (hv : IsSB v) (h1 : ip v v = 1) {a b : ℂ}
    (h : a • v = b • v) : a = b := by
  have ha := TensVac.ip_smul_left a hv hv
  have hb := TensVac.ip_smul_left b hv hv
  rw [h1, _root_.mul_one] at ha hb
  rw [← ha, ← hb, h]

/- English proof (translation)
Introduce `E _ _ _ r X g bas idx n hs hn D v₀ hvac mu hmu`. Establish `hsd : SelfD X X.Λ` using `Lev.selfD_of_sympl hs`. Establish `hlat : ∀ L ∈ D.lats, ∀ ga ∈ D.grp, mapL ga L ∈ D.lats` using `fun L hL ga hga => Lev.mapL_mem_lats hsd hga hL`. Establish `hred : ∀ ga ∈ D.grp, ∃ k : D.J, D.Red (fun i => (ga : Matrix (Fin r) (Fin r) E) *ᵥ D.β i) k`. Introduce `ga hga`.

Take `⟨-, k, hk, h⟩` from `(Lev.mem_grp ga).mp hga`. Conclude with `⟨⟨k, hk⟩, h⟩`. Establish `hun : ∀ ga ∈ D.grp, IsUn X ga` using `fun ga hga => ((Lev.mem_grp ga).mp hga).1`. Establish `hvsb : ∀ L ∈ D.lats, IsSB (v₀ L)`. Introduce `L hL`.

Take `⟨h, -, -⟩` from `hvac L hL`. Conclude with `h`. Establish `hvone : ∀ L ∈ D.lats, ip (v₀ L) (v₀ L) = 1`. Introduce `L hL`. Take `⟨-, h, -⟩` from `hvac L hL`.

Conclude with `h`. Establish `hnorm : ∀ ga ∈ D.grp, ∀ L ∈ D.lats, ‖mu ga L‖ = 1`. Introduce `ga hga L hL`. Take `⟨k, hk⟩` from `hred ga hga`. Establish `hL'` using `hlat L hL ga hga`.

Establish `hip` using `((wG_laws E r X g bas idx n hs hn ga (hun ga hga) (v₀ L) (hvsb L hL)).2.2.1 (v₀ L) (hvsb L hL)).1`. Rewrite `hip` using `[hmu ga hga L hL k hk, hvone L hL, TensVac.ip_smul_left _ (hvsb _ hL') (TensVac.sb_smul _ (hvsb _ hL')), TensVac.ip_smul_right _ (hvsb _ hL') (hvsb _ hL'), hvone _ hL', _root_.mul_one, Complex.mul_conj, Complex.normSq_eq_norm_sq]`. Establish `h2 : ‖mu ga L * ((D.lam k : ℂˣ) : ℂ)‖ ^ 2 = 1` using `by exact_mod_cast hip`. Rewrite `h2` using `[norm_mul, Lev.norm_lam k, _root_.mul_one]`. Conclude with `(pow_eq_one_iff_of_nonneg (norm_nonneg _) two_ne_zero).mp h2`.

Establish `hlam : ∀ ga ∈ D.grp, ∀ ga' ∈ D.grp, ∀ k k' k'' : D.J, D.Red (fun i => (ga : Matrix (Fin r) (Fin r) E) *ᵥ D.β i) k → D.Red (fun i => (ga' : Matrix (Fin r) (Fin r) E) *ᵥ D.β i) k' → D.Red (fun i => ((ga * ga' : GL (Fin r) E) : Matrix (Fin r) (Fin r) E) *ᵥ D.β i) k'' → ((D.lam k'' : …`. Introduce `ga _ ga' _ k k' k'' hk hk' hk''`. Set `y0 : Matrix (Fin r) (Fin r) E` to `Matrix.of fun i => D.β i`. Establish `hy : ∀ M : Matrix (Fin r) (Fin r) E, y0 * Mᵀ = Matrix.of fun i => M *ᵥ D.β i`. Introduce `M`.

Use extensionality with `i j`. Simplify using `[y0, Matrix.mul_apply, Matrix.mulVec, dotProduct, _root_.mul_comm]`. Establish `e1` using `Lev.dat_lin (le_refl r) hk'' y0`. Establish `e2` using `Lev.dat_lin (le_refl r) hk (y0 * (ga' : Matrix (Fin r) (Fin r) E)ᵀ)`. Establish `e3` using `Lev.dat_lin (le_refl r) hk' y0`.

Establish `hne : D.dat (le_refl r) (y0 * (ga' : Matrix (Fin r) (Fin r) E)ᵀ) ≠ 0`. Rewrite using `[hy]`. Unfold `SW.Level.dat`. Use `split_ifs with hc`. Conclude with `Units.ne_zero _`.

Conclude with `absurd ⟨⟨k', hk'⟩, fun j hj => absurd j.isLt (not_lt.mpr hj)⟩ hc`. Establish `hd0 : D.dat (le_refl r) y0 ≠ 0`. Introduce `h0`. Apply `hne` to reduce the goal to its premises. Rewrite using `[e3, h0]`.

Simplify using the standard rewrite rules. Establish `hm : y0 * ((ga * ga' : GL (Fin r) E) : Matrix (Fin r) (Fin r) E)ᵀ = y0 * (ga' : Matrix (Fin r) (Fin r) E)ᵀ * (ga : Matrix (Fin r) (Fin r) E)ᵀ`. Rewrite using `[Units.val_mul, Matrix.transpose_mul, Matrix.mul_assoc]`. Rewrite `e1` using `[hm, e2, e3]`. Apply `mul_right_cancel₀ hd0` to reduce the goal to its premises.

Rewrite using `[← e1]`. Expand and normalize the polynomial expressions, which then agree. Establish `hcoc : ∀ ga ∈ D.grp, ∀ ga' ∈ D.grp, ∀ L ∈ D.lats, mu (ga * ga') L = mu ga (mapL ga' L) * mu ga' L`. Introduce `ga hga ga' hga' L hL`. Take `⟨k, hk⟩` from `hred ga hga`.

Take `⟨k', hk'⟩` from `hred ga' hga'`. Establish `hgg : ga * ga' ∈ D.grp` using `Subgroup.mul_mem _ hga hga'`. Take `⟨k'', hk''⟩` from `hred _ hgg`. Establish `hL'` using `hlat L hL ga' hga'`. Establish `hL''` using `hlat _ hL' ga hga`.

Establish `hcomp` using `(wG_laws E r X g bas idx n hs hn ga' (hun ga' hga') (v₀ L) (hvsb L hL)).2.2.2.2.2.1 ga (hun ga hga)`. Establish `hsm` using `(wG_laws E r X g bas idx n hs hn ga (hun ga hga) (v₀ (mapL ga' L)) (hvsb _ hL')).2.2.2.1 (mu ga' L * ((D.lam k' : ℂˣ) : ℂ))`. Rewrite `hcomp` using `[hmu _ hgg L hL k'' hk'', hmu ga' hga' L hL k' hk', hsm, hmu ga hga _ hL' k hk, smul_smul, mapL_mul']`. Establish `hc` using `smul_left_cancel_of_ip_self_eq_one (hvsb _ hL'') (hvone _ hL'') hcomp`. Rewrite `hc` using `[hlam ga hga ga' hga' k k' k'' hk hk' hk'']`.

Establish `hk0 : ((D.lam k : ℂˣ) : ℂ) * (D.lam k' : ℂˣ) ≠ 0` using `mul_ne_zero (Units.ne_zero _) (Units.ne_zero _)`. Apply `mul_right_cancel₀ hk0` to reduce the goal to its premises. Take the linear combination `hc`. Use `⟨hnorm, ?_, hcoc⟩` and prove the remaining obligations. Introduce `L hL`.

Establish `h1` using `hcoc 1 (Subgroup.one_mem _) 1 (Subgroup.one_mem _) L hL`. Rewrite `h1` using `[_root_.mul_one, mapL_one']`. Establish `hn1` using `hnorm 1 (Subgroup.one_mem _) L hL`. Establish `hne : mu 1 L ≠ 0`. Introduce `h`.

Rewrite `hn1` using `[h, norm_zero]`. Conclude with `zero_ne_one hn1`. Conclude with `mul_left_cancel₀ hne (h1.symm.trans (_root_.mul_one _).symm)`.
-/
theorem vac_multiplier_cocycle : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (g : ℕ) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin r) (n : ℕ), IsSympl X bas → Even n → ∀ D : SW.Level X, ∀ v₀ : Lt E r → TF n g, (∀ L ∈ D.lats, IsVac X bas D.w (tens (stdL E n) (D.sh L)) (v₀ L)) → ∀ mu : GL (Fin r) E → Lt E r → ℂ, (∀ ga ∈ D.grp, ∀ L ∈ D.lats, ∀ k : D.J, D.Red (fun i => (ga : Matrix (Fin r) (Fin r) E) *ᵥ D.β i) k → wG X bas idx ga (v₀ L) = (mu ga L * (D.lam k : ℂˣ)) • v₀ (mapL ga L)) → (∀ ga ∈ D.grp, ∀ L ∈ D.lats, ‖mu ga L‖ = 1) ∧ (∀ L ∈ D.lats, mu 1 L = 1) ∧ ∀ ga ∈ D.grp, ∀ ga' ∈ D.grp, ∀ L ∈ D.lats, mu (ga * ga') L = mu ga (mapL ga' L) * mu ga' L := by
  intro E _ _ _ r X g bas idx n hs hn D v₀ hvac mu hmu
  have hsd : SelfD X X.Λ := Lev.selfD_of_sympl hs
  have hlat : ∀ L ∈ D.lats, ∀ ga ∈ D.grp, mapL ga L ∈ D.lats := fun L hL ga hga =>
    Lev.mapL_mem_lats hsd hga hL
  have hred : ∀ ga ∈ D.grp, ∃ k : D.J,
      D.Red (fun i => (ga : Matrix (Fin r) (Fin r) E) *ᵥ D.β i) k := by
    intro ga hga
    obtain ⟨-, k, hk, h⟩ := (Lev.mem_grp ga).mp hga
    exact ⟨⟨k, hk⟩, h⟩
  have hun : ∀ ga ∈ D.grp, IsUn X ga := fun ga hga => ((Lev.mem_grp ga).mp hga).1
  have hvsb : ∀ L ∈ D.lats, IsSB (v₀ L) := by
    intro L hL
    obtain ⟨h, -, -⟩ := hvac L hL
    exact h
  have hvone : ∀ L ∈ D.lats, ip (v₀ L) (v₀ L) = 1 := by
    intro L hL
    obtain ⟨-, h, -⟩ := hvac L hL
    exact h

  have hnorm : ∀ ga ∈ D.grp, ∀ L ∈ D.lats, ‖mu ga L‖ = 1 := by
    intro ga hga L hL
    obtain ⟨k, hk⟩ := hred ga hga
    have hL' := hlat L hL ga hga
    have hip := ((wG_laws E r X g bas idx n hs hn ga (hun ga hga) (v₀ L) (hvsb L hL)).2.2.1
      (v₀ L) (hvsb L hL)).1
    rw [hmu ga hga L hL k hk, hvone L hL,
      TensVac.ip_smul_left _ (hvsb _ hL') (TensVac.sb_smul _ (hvsb _ hL')),
      TensVac.ip_smul_right _ (hvsb _ hL') (hvsb _ hL'), hvone _ hL', _root_.mul_one,
      Complex.mul_conj, Complex.normSq_eq_norm_sq] at hip
    have h2 : ‖mu ga L * ((D.lam k : ℂˣ) : ℂ)‖ ^ 2 = 1 := by exact_mod_cast hip
    rw [norm_mul, Lev.norm_lam k, _root_.mul_one] at h2
    exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) two_ne_zero).mp h2

  have hlam : ∀ ga ∈ D.grp, ∀ ga' ∈ D.grp, ∀ k k' k'' : D.J,
      D.Red (fun i => (ga : Matrix (Fin r) (Fin r) E) *ᵥ D.β i) k →
      D.Red (fun i => (ga' : Matrix (Fin r) (Fin r) E) *ᵥ D.β i) k' →
      D.Red (fun i => ((ga * ga' : GL (Fin r) E) : Matrix (Fin r) (Fin r) E) *ᵥ D.β i) k'' →
      ((D.lam k'' : ℂˣ) : ℂ) = (D.lam k : ℂˣ) * (D.lam k' : ℂˣ) := by
    intro ga _ ga' _ k k' k'' hk hk' hk''
    let y0 : Matrix (Fin r) (Fin r) E := Matrix.of fun i => D.β i
    have hy : ∀ M : Matrix (Fin r) (Fin r) E, y0 * Mᵀ = Matrix.of fun i => M *ᵥ D.β i := by
      intro M
      ext i j
      simp [y0, Matrix.mul_apply, Matrix.mulVec, dotProduct, _root_.mul_comm]
    have e1 := Lev.dat_lin (le_refl r) hk'' y0
    have e2 := Lev.dat_lin (le_refl r) hk (y0 * (ga' : Matrix (Fin r) (Fin r) E)ᵀ)
    have e3 := Lev.dat_lin (le_refl r) hk' y0
    have hne : D.dat (le_refl r) (y0 * (ga' : Matrix (Fin r) (Fin r) E)ᵀ) ≠ 0 := by
      rw [hy]
      unfold SW.Level.dat
      split_ifs with hc
      · exact Units.ne_zero _
      · exact absurd ⟨⟨k', hk'⟩, fun j hj => absurd j.isLt (not_lt.mpr hj)⟩ hc
    have hd0 : D.dat (le_refl r) y0 ≠ 0 := by
      intro h0
      apply hne
      rw [e3, h0]
      simp
    have hm : y0 * ((ga * ga' : GL (Fin r) E) : Matrix (Fin r) (Fin r) E)ᵀ =
        y0 * (ga' : Matrix (Fin r) (Fin r) E)ᵀ * (ga : Matrix (Fin r) (Fin r) E)ᵀ := by
      rw [Units.val_mul, Matrix.transpose_mul, Matrix.mul_assoc]
    rw [hm, e2, e3] at e1
    apply mul_right_cancel₀ hd0
    rw [← e1]
    ring

  have hcoc : ∀ ga ∈ D.grp, ∀ ga' ∈ D.grp, ∀ L ∈ D.lats,
      mu (ga * ga') L = mu ga (mapL ga' L) * mu ga' L := by
    intro ga hga ga' hga' L hL
    obtain ⟨k, hk⟩ := hred ga hga
    obtain ⟨k', hk'⟩ := hred ga' hga'
    have hgg : ga * ga' ∈ D.grp := Subgroup.mul_mem _ hga hga'
    obtain ⟨k'', hk''⟩ := hred _ hgg
    have hL' := hlat L hL ga' hga'
    have hL'' := hlat _ hL' ga hga
    have hcomp := (wG_laws E r X g bas idx n hs hn ga' (hun ga' hga') (v₀ L)
      (hvsb L hL)).2.2.2.2.2.1 ga (hun ga hga)
    have hsm := (wG_laws E r X g bas idx n hs hn ga (hun ga hga) (v₀ (mapL ga' L))
      (hvsb _ hL')).2.2.2.1 (mu ga' L * ((D.lam k' : ℂˣ) : ℂ))
    rw [hmu _ hgg L hL k'' hk'', hmu ga' hga' L hL k' hk', hsm, hmu ga hga _ hL' k hk, smul_smul,
      mapL_mul'] at hcomp
    have hc := smul_left_cancel_of_ip_self_eq_one (hvsb _ hL'') (hvone _ hL'') hcomp
    rw [hlam ga hga ga' hga' k k' k'' hk hk' hk''] at hc
    have hk0 : ((D.lam k : ℂˣ) : ℂ) * (D.lam k' : ℂˣ) ≠ 0 :=
      mul_ne_zero (Units.ne_zero _) (Units.ne_zero _)
    apply mul_right_cancel₀ hk0
    linear_combination hc
  refine ⟨hnorm, ?_, hcoc⟩

  intro L hL
  have h1 := hcoc 1 (Subgroup.one_mem _) 1 (Subgroup.one_mem _) L hL
  rw [_root_.mul_one, mapL_one'] at h1
  have hn1 := hnorm 1 (Subgroup.one_mem _) L hL
  have hne : mu 1 L ≠ 0 := by
    intro h
    rw [h, norm_zero] at hn1
    exact zero_ne_one hn1
  exact mul_left_cancel₀ hne (h1.symm.trans (_root_.mul_one _).symm)

end GlobalTheory.Dict

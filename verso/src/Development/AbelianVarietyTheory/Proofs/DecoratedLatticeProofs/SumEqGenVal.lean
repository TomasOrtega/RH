import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsCoType
import Formalism.LocalToGlobal.Columns.HeckeSp
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CardParahoricDoubleCosetRepsInvEqStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsParahoricAndIntegralGLDoubleCosetRepsStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.TwoBlockParahoricLowerBlockDetTameCharacterStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ParahoricDatumEigenvectorTwoBlockParahoricStatement
open MeasureTheory ValuativeRel Matrix GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.Doubling GlobalTheory.GLDoubling GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection GlobalTheory.ZonalCellDecomposition GlobalTheory.SatakeBound GlobalTheory.ParHecke

noncomputable section

namespace GlobalTheory.ParHeckeTransfer

/- English proof (translation)
Unfold `mtor torusElt`. Rewrite using `[← map_inv]`. Use `congr 1`. Use function extensionality and compare the values at `i`. Apply the tactic sequence `rcases i with i | i <;> simp [_root_.zpow_neg]`.
-/
theorem mtor_neg {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    {A D : Type} [Fintype A] [DecidableEq A] [Fintype D] [DecidableEq D] (ϖ : kˣ) (e : D → ℤ) :
    (mtor ϖ (-e) : GL (A ⊕ D) k) = (mtor ϖ e)⁻¹ := by
  unfold mtor torusElt
  rw [← map_inv]
  congr 1
  funext i
  rcases i with i | i <;> simp [_root_.zpow_neg]

/- English proof (translation)
Introduce `k _ _ _ _ A D D' _ _ _ _ _ _ ϖ ξ μS μT hξ hμ W hW hΦ X _ _ ρ x B hx X' _ _ ρ' b hb s R d hR`. Use `set g : GL (A ⊕ D) k := mtor ϖ (indic s) with hg`. Establish `hginv : (mtor ϖ (-indic s) : GL (A ⊕ D) k) = g⁻¹` using `mtor_neg ϖ (indic s)`. Rewrite `hR`, the goal using `[hginv]`. Use `set Φ : W := ⟨datum ξ⁻¹, hΦ⟩ with hΦdef`.

Establish `h1 : ∀ j ∈ R, (ξ (d j) : ℂ) • b ⟨omTwo μS μT (j * g⁻¹) 1 (datum ξ⁻¹), hW _ _ _ hΦ⟩ x = b Φ (ρ g x)`. Introduce `j hj`. Take `⟨hjJ, hdj⟩` from `hR.1 j hj`. Establish `hjiJ : j⁻¹ ∈ parahoric k A D` using `inv_mem hjJ`. Establish `hne` using `(GlobalTheory.T.twoBlockParahoric_lowerBlock_det_tameCharacter k A D ξ hξ j⁻¹ hjiJ).1`.

Establish `hprod` using `(GlobalTheory.T.twoBlockParahoric_lowerBlock_det_tameCharacter k A D ξ hξ j hjJ).2 (d j) (Units.mk0 _ hne) hdj rfl`. Establish `hx1 : ρ j⁻¹ x = (ξ (Units.mk0 _ hne) : ℂ) • x` using `hx.1 j⁻¹ hjiJ (Units.mk0 _ hne) rfl`. Establish `he` using `hb (j * g⁻¹) 1 Φ (ρ (g * j⁻¹) x)`. Establish `hone : (j * g⁻¹) * (g * j⁻¹) = 1` using `by group`. Rewrite `he` using `[← Module.End.mul_apply, ← map_mul, hone, map_one, Module.End.one_apply, map_one, Module.End.one_apply, map_mul, Module.End.mul_apply, hx1, map_smul, map_smul]`.

Rewrite using `[show (⟨omTwo μS μT (j * g⁻¹) 1 (datum ξ⁻¹), hW _ _ _ hΦ⟩ : W) = ⟨omTwo μS μT (j * g⁻¹) 1 Φ, hW _ _ Φ Φ.2⟩ from rfl, he, smul_smul, hprod, one_smul]`. Establish `htame : IsTame ξ⁻¹` using `fun y hy => by simp [hξ y hy]`. Establish `hunr : IsUnram (μT⁻¹ * ξ)` using `fun y hy => by`. Use `hμ y hy` as an intermediate fact. Simplify using `only [MonoidHom.mul_apply, MonoidHom.inv_apply] at this ⊢`.

Rewrite using `[← inv_inv (ξ y), ← mul_inv, this, inv_one]`. Establish `h2 : ∀ j ∈ parahoric k A D, ∀ dd : kˣ, (dd : k) = (j : Matrix (A ⊕ D) (A ⊕ D) k).toBlocks₂₂.det → ∀ z, b Φ (ρ j z) = (ξ dd : ℂ) • b Φ z`. Introduce `j hj dd hdd z`. Establish `hom : omTwo μS μT j (1 : GL (A ⊕ D') k) (datum ξ⁻¹) = ((ξ⁻¹ dd : ℂˣ) : ℂ) • datum ξ⁻¹`. Use `GlobalTheory.T.parahoricDatum_eigenvector_twoBlockParahoric k A D D' ξ⁻¹ (μT⁻¹ * ξ) htame hunr j hj dd hdd` as an intermediate fact.

Rewrite `this` using `[show μT⁻¹ * ξ * ξ⁻¹ = μT⁻¹ by rw [mul_assoc, mul_inv_cancel, mul_one]]`. Unfold `omTwo`. Rewrite using `[this]`. Use function extensionality and compare the values at `y`. Simplify using the standard rewrite rules.

Establish `he` using `hb j 1 Φ z`. Establish `hsub : (⟨omTwo μS μT j 1 Φ, hW j 1 Φ Φ.2⟩ : W) = ((ξ⁻¹ dd : ℂˣ) : ℂ) • Φ` using `Subtype.ext hom`. Rewrite `he` using `[hsub, map_smul, LinearMap.smul_apply, map_one, Module.End.one_apply]`. Rewrite using `[← he, smul_smul]`. Simplify using the standard rewrite rules.

Take `⟨R'', d'', hR''⟩` from `(GlobalTheory.T.exists_parahoric_and_integralGL_doubleCosetReps k A D).1 g`. Establish `hcard` using `(GlobalTheory.T.card_parahoricDoubleCosetReps_inv_eq k A D g R'' R d'' d hR'' hR).1`. Establish `hT` using `hx.2.2 s R'' d'' hR''`. Establish `hsum2 : genVal (resCard k) (Fintype.card A) (Fintype.card D) B s.card • b Φ x = R''.card • b Φ (ρ g x)`. Rewrite using `[← map_smul, hT, map_sum, ← Finset.sum_const]`.

Use `Finset.sum_congr rfl fun j hj => ?_` and prove the remaining obligations. Take `⟨hjJ, hdj⟩` from `hR''.1 j hj`. Rewrite using `[map_smul, show (mtor ϖ (indic s) : GL (A ⊕ D) k) = g from rfl, map_mul, Module.End.mul_apply, h2 j hjJ (d'' j) hdj, smul_smul]`. Simplify using the standard rewrite rules. Rewrite using `[Finset.sum_congr rfl h1, Finset.sum_const, hsum2, hcard]`.
-/
theorem sum_eq_genVal : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (A D D' : Type) [Fintype A] [DecidableEq A] [Fintype D] [DecidableEq D] [Fintype D'] [DecidableEq D'] (ϖ : kˣ) (ξ μS μT : kˣ →* ℂˣ), IsTame ξ → IsUnram (μT * ξ⁻¹) → ∀ (W : Submodule ℂ (Matrix (A ⊕ D') (A ⊕ D) k → ℂ)) (hW : ∀ g h, ∀ u ∈ W, omTwo μS μT g h u ∈ W) (hΦ : datum ξ⁻¹ ∈ W) (X : Type) [AddCommGroup X] [Module ℂ X] (ρ : Representation ℂ (GL (A ⊕ D) k) X) (x : X) (B : Multiset ℂˣ), IsGen ρ ξ ϖ B x → ∀ (X' : Type) [AddCommGroup X'] [Module ℂ X'] (ρ' : Representation ℂ (GL (A ⊕ D') k) X') (b : W →ₗ[ℂ] X →ₗ[ℂ] X'), (∀ g h (u : W) y, b ⟨omTwo μS μT g h u, hW g h u u.2⟩ (ρ g y) = ρ' h (b u y)) → ∀ (s : Finset D) (R : Finset (GL (A ⊕ D) k)) (d : GL (A ⊕ D) k → kˣ), IsReps (mtor ϖ (-indic s)) R d → ∑ j ∈ R, (ξ (d j) : ℂ) • b ⟨omTwo μS μT (j * mtor ϖ (-indic s)) 1 (datum ξ⁻¹), hW _ _ _ hΦ⟩ x = genVal (resCard k) (Fintype.card A) (Fintype.card D) B s.card • b ⟨datum ξ⁻¹, hΦ⟩ x := by
  intro k _ _ _ _ A D D' _ _ _ _ _ _ ϖ ξ μS μT hξ hμ W hW hΦ X _ _ ρ x B hx X' _ _ ρ' b hb s R d hR
  set g : GL (A ⊕ D) k := mtor ϖ (indic s) with hg
  have hginv : (mtor ϖ (-indic s) : GL (A ⊕ D) k) = g⁻¹ := mtor_neg ϖ (indic s)
  rw [hginv] at hR ⊢
  set Φ : W := ⟨datum ξ⁻¹, hΦ⟩ with hΦdef

  have h1 : ∀ j ∈ R, (ξ (d j) : ℂ) • b ⟨omTwo μS μT (j * g⁻¹) 1 (datum ξ⁻¹), hW _ _ _ hΦ⟩ x = b Φ (ρ g x) := by
    intro j hj
    obtain ⟨hjJ, hdj⟩ := hR.1 j hj
    have hjiJ : j⁻¹ ∈ parahoric k A D := inv_mem hjJ
    have hne := (GlobalTheory.T.twoBlockParahoric_lowerBlock_det_tameCharacter k A D ξ hξ j⁻¹ hjiJ).1
    have hprod := (GlobalTheory.T.twoBlockParahoric_lowerBlock_det_tameCharacter k A D ξ hξ j hjJ).2 (d j) (Units.mk0 _ hne) hdj rfl
    have hx1 : ρ j⁻¹ x = (ξ (Units.mk0 _ hne) : ℂ) • x := hx.1 j⁻¹ hjiJ (Units.mk0 _ hne) rfl
    have he := hb (j * g⁻¹) 1 Φ (ρ (g * j⁻¹) x)
    have hone : (j * g⁻¹) * (g * j⁻¹) = 1 := by group
    rw [← Module.End.mul_apply, ← map_mul, hone, map_one, Module.End.one_apply, map_one, Module.End.one_apply,
      map_mul, Module.End.mul_apply, hx1, map_smul, map_smul] at he
    rw [show (⟨omTwo μS μT (j * g⁻¹) 1 (datum ξ⁻¹), hW _ _ _ hΦ⟩ : W) = ⟨omTwo μS μT (j * g⁻¹) 1 Φ, hW _ _ Φ Φ.2⟩ from rfl,
      he, smul_smul, hprod, one_smul]

  have htame : IsTame ξ⁻¹ := fun y hy => by simp [hξ y hy]
  have hunr : IsUnram (μT⁻¹ * ξ) := fun y hy => by
    have := hμ y hy
    simp only [MonoidHom.mul_apply, MonoidHom.inv_apply] at this ⊢
    rw [← inv_inv (ξ y), ← mul_inv, this, inv_one]
  have h2 : ∀ j ∈ parahoric k A D, ∀ dd : kˣ, (dd : k) = (j : Matrix (A ⊕ D) (A ⊕ D) k).toBlocks₂₂.det →
      ∀ z, b Φ (ρ j z) = (ξ dd : ℂ) • b Φ z := by
    intro j hj dd hdd z
    have hom : omTwo μS μT j (1 : GL (A ⊕ D') k) (datum ξ⁻¹) = ((ξ⁻¹ dd : ℂˣ) : ℂ) • datum ξ⁻¹ := by
      have := GlobalTheory.T.parahoricDatum_eigenvector_twoBlockParahoric k A D D' ξ⁻¹ (μT⁻¹ * ξ) htame hunr j hj dd hdd
      rw [show μT⁻¹ * ξ * ξ⁻¹ = μT⁻¹ by rw [mul_assoc, mul_inv_cancel, mul_one]] at this
      unfold omTwo
      rw [this]
      funext y
      simp
    have he := hb j 1 Φ z
    have hsub : (⟨omTwo μS μT j 1 Φ, hW j 1 Φ Φ.2⟩ : W) = ((ξ⁻¹ dd : ℂˣ) : ℂ) • Φ := Subtype.ext hom
    rw [hsub, map_smul, LinearMap.smul_apply, map_one, Module.End.one_apply] at he
    rw [← he, smul_smul]
    simp

  obtain ⟨R'', d'', hR''⟩ := (GlobalTheory.T.exists_parahoric_and_integralGL_doubleCosetReps k A D).1 g
  have hcard := (GlobalTheory.T.card_parahoricDoubleCosetReps_inv_eq k A D g R'' R d'' d hR'' hR).1
  have hT := hx.2.2 s R'' d'' hR''
  have hsum2 : genVal (resCard k) (Fintype.card A) (Fintype.card D) B s.card • b Φ x = R''.card • b Φ (ρ g x) := by
    rw [← map_smul, hT, map_sum, ← Finset.sum_const]
    refine Finset.sum_congr rfl fun j hj => ?_
    obtain ⟨hjJ, hdj⟩ := hR''.1 j hj
    rw [map_smul, show (mtor ϖ (indic s) : GL (A ⊕ D) k) = g from rfl, map_mul, Module.End.mul_apply,
      h2 j hjJ (d'' j) hdj, smul_smul]
    simp
  rw [Finset.sum_congr rfl h1, Finset.sum_const, hsum2, hcard]

end GlobalTheory.ParHeckeTransfer

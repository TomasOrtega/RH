import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GapGeSubKapBase
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FrMoveTransfer
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions
open GlobalTheory.LevDesc (move)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.OrbitSep

namespace GlobalTheory.OrbitSep

/- English proof (translation)
Introduce `E _ _ _ H Dw l I γ hI hU`. Take `⟨m, hm⟩` from `hU`. Use `set M : Submodule (𝓞 E) Dw.La := I • ⊤ with hMdef`. Use `set f := liftLa γ with hfdef`. Use `set g := liftLa γ⁻¹ with hgdef`.

Establish `hN : l.Mb • (⊤ : Submodule (𝓞 E) Dw.La) ≤ M` using `Submodule.smul_mono_left hI`. Establish `hpres : ∀ φ : Dw.La →ₗ[𝓞 E] Dw.La, M ≤ M.comap φ`. Introduce `φ`. Rewrite using `[← Submodule.map_le_iff_le_comap, hMdef, Submodule.map_smul'']`. Conclude with `Submodule.smul_mono le_rfl le_top`.

Establish `hgf : ∀ x, g (f x) - x ∈ M`. Introduce `x`. Apply `hN` to reduce the goal to its premises. Rewrite using `[← Submodule.Quotient.eq]`. Establish `h1` using `liftLa_spec (γ⁻¹) (f x)`.

Establish `h2` using `liftLa_spec γ x`. Simplify using `only [Submodule.mkQ_apply] at h1 h2`. Rewrite using `[hgdef, h1, hfdef, h2]`. Conclude with `γ.symm_apply_apply _`. Establish `hfg : ∀ x, f (g x) - x ∈ M`.

Introduce `x`. Apply `hN` to reduce the goal to its premises. Rewrite using `[← Submodule.Quotient.eq]`. Establish `h1` using `liftLa_spec γ (g x)`. Establish `h2` using `liftLa_spec (γ⁻¹) x`.

Simplify using `only [Submodule.mkQ_apply] at h1 h2`. Rewrite using `[hfdef, h1, hgdef, h2]`. Conclude with `γ.apply_symm_apply _`. Set `A` to `M.mapQ M f (hpres f)`. Set `B` to `M.mapQ M g (hpres g)`.

Establish `hBA : B * A = 1`. Use extensionality with `x`. Simplify using `only [Module.End.mul_apply, A, B, Submodule.mapQ_apply, Module.End.one_apply, LinearMap.coe_comp, Function.comp_apply, Submodule.mkQ_apply]`. Conclude with `(Submodule.Quotient.eq M).2 (hgf x)`. Establish `hAB : A * B = 1`.

Use extensionality with `x`. Simplify using `only [Module.End.mul_apply, A, B, Submodule.mapQ_apply, Module.End.one_apply, LinearMap.coe_comp, Function.comp_apply, Submodule.mkQ_apply]`. Conclude with `(Submodule.Quotient.eq M).2 (hfg x)`. Establish `hdesc : ∀ (φ : Dw.La →ₗ[𝓞 E] Dw.La) (k : ℕ) (x : Dw.La), M.mkQ (((φ - 1) ^ k) x) = ((M.mapQ M φ (hpres φ) - 1) ^ k) (M.mkQ x)`. Introduce `φ k`.

Proceed by induction on `k with`. Consider the case `zero => intro x`. Simplify using the standard rewrite rules. Consider the case `succ k ih`. Introduce `x`.

Rewrite using `[pow_succ, pow_succ, Module.End.mul_apply, Module.End.mul_apply, ih]`. Use `congr 1`. Establish `hA0 : (A - 1) ^ m = 0`. Use extensionality with `x`. Simplify using `only [LinearMap.coe_comp, Function.comp_apply, Submodule.mkQ_apply, LinearMap.zero_apply]`.

Rewrite using `[← Submodule.mkQ_apply, ← hdesc f m x, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]`. Conclude with `hm x`. Establish `hcomm : Commute B (1 - A)`. Use `Commute.sub_right (Commute.one_right B) ?_` and prove the remaining obligations. Conclude with `(hBA.trans hAB.symm)`.

Establish `hB0 : (B - 1) ^ m = 0`. Establish `e : B - 1 = B * (1 - A)` using `by rw [mul_sub, mul_one, hBA]`. Rewrite using `[e, hcomm.mul_pow, show (1 - A) = -(A - 1) by abel, neg_pow, hA0, mul_zero, mul_zero]`. Use `⟨m, fun x => ?_⟩` and prove the remaining obligations. Rewrite using `[← Submodule.Quotient.mk_eq_zero, ← Submodule.mkQ_apply, hdesc g m x, hB0, LinearMap.zero_apply]`.
-/
theorem unipAt_inv_liftLa : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (I : Ideal (𝓞 E)) («γ» : LevelAut Dw l), l.Mb ≤ I → UnipAt I «γ» → ∃ m : ℕ, ∀ x : Dw.La, ((liftLa «γ»⁻¹ - 1) ^ m) x ∈ I • (⊤ : Submodule (𝓞 E) Dw.La) := by
  intro E _ _ _ H Dw l I γ hI hU
  obtain ⟨m, hm⟩ := hU
  set M : Submodule (𝓞 E) Dw.La := I • ⊤ with hMdef
  set f := liftLa γ with hfdef
  set g := liftLa γ⁻¹ with hgdef
  have hN : l.Mb • (⊤ : Submodule (𝓞 E) Dw.La) ≤ M := Submodule.smul_mono_left hI
  have hpres : ∀ φ : Dw.La →ₗ[𝓞 E] Dw.La, M ≤ M.comap φ := by
    intro φ
    rw [← Submodule.map_le_iff_le_comap, hMdef, Submodule.map_smul'']
    exact Submodule.smul_mono le_rfl le_top
  have hgf : ∀ x, g (f x) - x ∈ M := by
    intro x
    apply hN
    rw [← Submodule.Quotient.eq]
    have h1 := liftLa_spec (γ⁻¹) (f x)
    have h2 := liftLa_spec γ x
    simp only [Submodule.mkQ_apply] at h1 h2
    rw [hgdef, h1, hfdef, h2]
    exact γ.symm_apply_apply _
  have hfg : ∀ x, f (g x) - x ∈ M := by
    intro x
    apply hN
    rw [← Submodule.Quotient.eq]
    have h1 := liftLa_spec γ (g x)
    have h2 := liftLa_spec (γ⁻¹) x
    simp only [Submodule.mkQ_apply] at h1 h2
    rw [hfdef, h1, hgdef, h2]
    exact γ.apply_symm_apply _
  let A := M.mapQ M f (hpres f)
  let B := M.mapQ M g (hpres g)
  have hBA : B * A = 1 := by
    ext x
    simp only [Module.End.mul_apply, A, B, Submodule.mapQ_apply, Module.End.one_apply, LinearMap.coe_comp,
      Function.comp_apply, Submodule.mkQ_apply]
    exact (Submodule.Quotient.eq M).2 (hgf x)
  have hAB : A * B = 1 := by
    ext x
    simp only [Module.End.mul_apply, A, B, Submodule.mapQ_apply, Module.End.one_apply, LinearMap.coe_comp,
      Function.comp_apply, Submodule.mkQ_apply]
    exact (Submodule.Quotient.eq M).2 (hfg x)
  have hdesc : ∀ (φ : Dw.La →ₗ[𝓞 E] Dw.La) (k : ℕ) (x : Dw.La),
      M.mkQ (((φ - 1) ^ k) x) = ((M.mapQ M φ (hpres φ) - 1) ^ k) (M.mkQ x) := by
    intro φ k
    induction k with
    | zero => intro x; simp
    | succ k ih =>
      intro x
      rw [pow_succ, pow_succ, Module.End.mul_apply, Module.End.mul_apply, ih]
      congr 1
  have hA0 : (A - 1) ^ m = 0 := by
    ext x
    simp only [LinearMap.coe_comp, Function.comp_apply, Submodule.mkQ_apply, LinearMap.zero_apply]
    rw [← Submodule.mkQ_apply, ← hdesc f m x, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    exact hm x
  have hcomm : Commute B (1 - A) := by
    refine Commute.sub_right (Commute.one_right B) ?_
    exact (hBA.trans hAB.symm)
  have hB0 : (B - 1) ^ m = 0 := by
    have e : B - 1 = B * (1 - A) := by rw [mul_sub, mul_one, hBA]
    rw [e, hcomm.mul_pow, show (1 - A) = -(A - 1) by abel, neg_pow, hA0, mul_zero, mul_zero]
  refine ⟨m, fun x => ?_⟩
  rw [← Submodule.Quotient.mk_eq_zero, ← Submodule.mkQ_apply, hdesc g m x, hB0, LinearMap.zero_apply]

end GlobalTheory.OrbitSep

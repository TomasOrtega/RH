import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsBaseFrame
import Development.AbelianVarietyTheory.Definitions.Divisors.P22
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS
open GlobalTheory.FlagMod (ev frX frVec)
open GlobalTheory.FlagTan (psiSet HIx VIx TIx IsDef IsVert KSIso)
open ReciprocityTheory.ChartRestriction.G.PullbackSections (tv)
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory.LogPole
open scoped Classical

namespace GlobalTheory

/- English proof (translation)
Introduce `F A R _ _ _ _ _ _ _ _ _ P _ _ I n b hb D' hD'`. Establish `hloc : IsLocalizedModule P.primeCompl (Algebra.linearMap A R)` using `isLocalizedModule_iff_isLocalization.mpr inferInstance`. Establish `: Module.FinitePresentation A Ω[A⁄F]` using `Module.finitePresentation_of_finite _ _`. Set `Dc : Derivation F A R` to `D'.compAlgebraMap A`. Take `⟨h, s, hs⟩` from `Module.FinitePresentation.exists_lift_of_isLocalizedModule P.primeCompl (Algebra.linearMap A R) Dc.liftKaehlerDifferential`.

Set `D₀ : Derivation F A A` to `h.compDer (KaehlerDifferential.D F A)`. Establish `hD₀ : ∀ y : A, algebraMap A R (D₀ y) = algebraMap A R (s : A) * D' (algebraMap A R y)`. Introduce `y`. Use `congrArg (fun φ => φ (KaehlerDifferential.D F A y)) hs` as an intermediate fact. Simplify using `only [LinearMap.coe_comp, Function.comp_apply, Algebra.linearMap_apply, LinearMap.smul_apply, Derivation.liftKaehlerDifferential_comp_D] at this`.

Rewrite `this` using `[Submonoid.smul_def, Algebra.smul_def]`. Simplify `this` using `[D₀, Dc]`. Take `⟨G, hG⟩` from `(IsNoetherian.noetherian I : I.FG)`. Establish `hgen : ∀ g ∈ G, ∃ t ∈ P.primeCompl, t * D₀ g ∈ I`. Introduce `g hg`.

Establish `hgI : g ∈ I` using `hG ▸ Ideal.subset_span hg`. Establish `: algebraMap A R (D₀ g) ∈ I.map (algebraMap A R)`. Rewrite using `[hD₀]`. Conclude with `Ideal.mul_mem_left _ _ (hD' _ (Ideal.mem_map_of_mem _ hgI))`. Conclude with `(IsLocalization.algebraMap_mem_map_algebraMap_iff P.primeCompl R I _).mp this`.

Use `choose! tg htgP htgI using hgen`. Set `t' : A` to `∏ g ∈ G, tg g`. Establish `ht'P : t' ∈ P.primeCompl`. Use `prod_mem (S := P.primeCompl) (t := G) (f := tg) (fun g hg => htgP g hg)` as an intermediate fact. Simplify `this` using `[t']`.

Set `D₁ : Derivation ℤ A A` to `t' • (D₀.restrictScalars ℤ)`. Establish `hD₁ : ∀ x, D₁ x = t' * D₀ x` using `fun x => by simp [D₁, smul_eq_mul]`. Establish `hkill : ∀ c, D₁ (algebraMap F A c) = 0` using `fun c => by`. Rewrite using `[hD₁, Derivation.map_algebraMap, mul_zero]`. Establish `hkeep : ∀ f ∈ I, D₁ f ∈ I`.

Introduce `f hf`. Rewrite `hf` using `[← hG]`. Proceed by induction on `hf using Submodule.span_induction with`. Consider the case `mem x hx`. Rewrite using `[hD₁]`.

Establish `hd : tg x ∣ t'` using `Finset.dvd_prod_of_mem _ hx`. Take `⟨k, hk⟩` from `hd`. Rewrite using `[hk, mul_comm (tg x) k, mul_assoc]`. Conclude with `Ideal.mul_mem_left _ _ (htgI x hx)`. Consider the case `zero => simp`.

Consider the case `add x y _ _ hx hy => rw [map_add]`. Conclude with `Ideal.add_mem _ hx hy`. Consider the case `smul a x hxs hx`. Rewrite using `[smul_eq_mul, Derivation.leibniz, smul_eq_mul, smul_eq_mul]`. Use `Ideal.add_mem _ (Ideal.mul_mem_left _ _ hx) (Ideal.mul_mem_right _ _ ?_)` and prove the remaining obligations.

Rewrite `hxs` using `[hG]`. Conclude with `hxs`. Take `⟨c, hc⟩` from `hb D₁ hkill hkeep`. Establish `hu : IsUnit (algebraMap A R (t' * s))` using `IsLocalization.map_units R (⟨t' * s, P.primeCompl.mul_mem ht'P s.2⟩ : P.primeCompl)`. Use `⟨fun j => hu.unit⁻¹ * algebraMap A R (c j), fun a => ?_⟩` and prove the remaining obligations.

Establish `e1 : algebraMap A R (D₁ a) = ∑ j, algebraMap A R (c j) * algebraMap A R (b j a)`. Rewrite using `[hc]`. Establish `: ∀ (s : Finset (Fin n)), (∑ j ∈ s, c j • b j) a = ∑ j ∈ s, c j * b j a`. Introduce `s`. Proceed by induction on `s using Finset.induction_on with`.

Consider the case `empty => simp`. Consider the case `insert x s hx ih => rw [Finset.sum_insert hx, Finset.sum_insert hx, Derivation.add_apply, ih, Derivation.smul_apply, smul_eq_mul]`. Rewrite using `[this, map_sum]`. Simplify using `only [map_mul]`. Establish `e2 : algebraMap A R (D₁ a) = algebraMap A R (t' * s) * D' (algebraMap A R a)`.

Rewrite using `[hD₁, map_mul, hD₀, map_mul, mul_assoc]`. Rewrite `e1` using `[e2]`. Establish `: D' (algebraMap A R a) = (hu.unit⁻¹ : Rˣ) * ∑ j, algebraMap A R (c j) * algebraMap A R (b j a)`. Rewrite using `[← e1, ← mul_assoc, IsUnit.val_inv_mul, one_mul]`. Rewrite using `[this, Finset.mul_sum]`.

Simplify using `only [mul_assoc]`.
-/
theorem logDerivation_atPrime_span : ∀ (F A R : Type) [Field F] [CommRing A] [CommRing R] [IsNoetherianRing A] [Algebra F A] [Algebra A R] [Algebra F R] [IsScalarTower F A R] [Algebra.FiniteType F A] (P : Ideal A) [P.IsPrime] [IsLocalization.AtPrime R P] (I : Ideal A) (n : ℕ) (b : Fin n → Derivation ℤ A A), (∀ D : Derivation ℤ A A, (∀ c, D (algebraMap F A c) = 0) → (∀ f ∈ I, D f ∈ I) → ∃ c : Fin n → A, D = ∑ j, c j • b j) → ∀ D' : Derivation F R R, (∀ f ∈ I.map (algebraMap A R), D' f ∈ I.map (algebraMap A R)) → ∃ c : Fin n → R, ∀ a : A, D' (algebraMap A R a) = ∑ j, c j * algebraMap A R (b j a) := by
  intro F A R _ _ _ _ _ _ _ _ _ P _ _ I n b hb D' hD'
  classical

  have hloc : IsLocalizedModule P.primeCompl (Algebra.linearMap A R) :=
    isLocalizedModule_iff_isLocalization.mpr inferInstance
  have : Module.FinitePresentation A Ω[A⁄F] := Module.finitePresentation_of_finite _ _
  let Dc : Derivation F A R := D'.compAlgebraMap A
  obtain ⟨h, s, hs⟩ := Module.FinitePresentation.exists_lift_of_isLocalizedModule
    P.primeCompl (Algebra.linearMap A R) Dc.liftKaehlerDifferential
  let D₀ : Derivation F A A := h.compDer (KaehlerDifferential.D F A)
  have hD₀ : ∀ y : A, algebraMap A R (D₀ y) = algebraMap A R (s : A) * D' (algebraMap A R y) := by
    intro y
    have := congrArg (fun φ => φ (KaehlerDifferential.D F A y)) hs
    simp only [LinearMap.coe_comp, Function.comp_apply, Algebra.linearMap_apply,
      LinearMap.smul_apply, Derivation.liftKaehlerDifferential_comp_D] at this
    rw [Submonoid.smul_def, Algebra.smul_def] at this
    simpa [D₀, Dc] using this

  obtain ⟨G, hG⟩ := (IsNoetherian.noetherian I : I.FG)
  have hgen : ∀ g ∈ G, ∃ t ∈ P.primeCompl, t * D₀ g ∈ I := by
    intro g hg
    have hgI : g ∈ I := hG ▸ Ideal.subset_span hg
    have : algebraMap A R (D₀ g) ∈ I.map (algebraMap A R) := by
      rw [hD₀]
      exact Ideal.mul_mem_left _ _ (hD' _ (Ideal.mem_map_of_mem _ hgI))
    exact (IsLocalization.algebraMap_mem_map_algebraMap_iff P.primeCompl R I _).mp this
  choose! tg htgP htgI using hgen
  let t' : A := ∏ g ∈ G, tg g
  have ht'P : t' ∈ P.primeCompl := by
    have := prod_mem (S := P.primeCompl) (t := G) (f := tg) (fun g hg => htgP g hg)
    simpa [t'] using this
  let D₁ : Derivation ℤ A A := t' • (D₀.restrictScalars ℤ)
  have hD₁ : ∀ x, D₁ x = t' * D₀ x := fun x => by simp [D₁, smul_eq_mul]
  have hkill : ∀ c, D₁ (algebraMap F A c) = 0 := fun c => by
    rw [hD₁, Derivation.map_algebraMap, mul_zero]
  have hkeep : ∀ f ∈ I, D₁ f ∈ I := by
    intro f hf
    rw [← hG] at hf
    induction hf using Submodule.span_induction with
    | mem x hx =>
      rw [hD₁]
      have hd : tg x ∣ t' := Finset.dvd_prod_of_mem _ hx
      obtain ⟨k, hk⟩ := hd
      rw [hk, mul_comm (tg x) k, mul_assoc]
      exact Ideal.mul_mem_left _ _ (htgI x hx)
    | zero => simp
    | add x y _ _ hx hy => rw [map_add]; exact Ideal.add_mem _ hx hy
    | smul a x hxs hx =>
      rw [smul_eq_mul, Derivation.leibniz, smul_eq_mul, smul_eq_mul]
      refine Ideal.add_mem _ (Ideal.mul_mem_left _ _ hx) (Ideal.mul_mem_right _ _ ?_)
      rw [hG] at hxs; exact hxs
  obtain ⟨c, hc⟩ := hb D₁ hkill hkeep

  have hu : IsUnit (algebraMap A R (t' * s)) :=
    IsLocalization.map_units R (⟨t' * s, P.primeCompl.mul_mem ht'P s.2⟩ : P.primeCompl)
  refine ⟨fun j => hu.unit⁻¹ * algebraMap A R (c j), fun a => ?_⟩
  have e1 : algebraMap A R (D₁ a) = ∑ j, algebraMap A R (c j) * algebraMap A R (b j a) := by
    rw [hc]
    have : ∀ (s : Finset (Fin n)), (∑ j ∈ s, c j • b j) a = ∑ j ∈ s, c j * b j a := by
      intro s; induction s using Finset.induction_on with
      | empty => simp
      | insert x s hx ih => rw [Finset.sum_insert hx, Finset.sum_insert hx, Derivation.add_apply, ih, Derivation.smul_apply, smul_eq_mul]
    rw [this, map_sum]; simp only [map_mul]
  have e2 : algebraMap A R (D₁ a) = algebraMap A R (t' * s) * D' (algebraMap A R a) := by
    rw [hD₁, map_mul, hD₀, map_mul, mul_assoc]
  rw [e2] at e1
  have : D' (algebraMap A R a) = (hu.unit⁻¹ : Rˣ) * ∑ j, algebraMap A R (c j) * algebraMap A R (b j a) := by
    rw [← e1, ← mul_assoc, IsUnit.val_inv_mul, one_mul]
  rw [this, Finset.mul_sum]
  simp only [mul_assoc]

end GlobalTheory

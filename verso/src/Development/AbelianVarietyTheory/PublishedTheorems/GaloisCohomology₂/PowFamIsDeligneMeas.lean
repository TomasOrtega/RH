import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.DeligneLocalConstants
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GaussSumNeZeroOfRamified
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ExistsOfLocalLanglands

noncomputable section

open NumberField IsDedekindDomain ValuativeRel
open Formalism.ConjugateSelfDual ReciprocityTheory.Gal
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.WeilDeligne

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.LocLanglands.MeasTest

section Tate

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {ψ : AddChar k Circle} {χ : kˣ →* ℂˣ} {t : ℝ}

/- English proof (translation)
Take `⟨c, a, R, hc, ha, hR, rfl⟩` from `h`. Take `⟨c', a', R', hc', ha', hR', rfl⟩` from `h'`. Take `rfl` from `ha.unique ha'`. Establish `h1 : valuation k (c' : k) = valuation k (c : k)` using `le_antisymm ((hc _).1 ((hc' _).2 le_rfl)) ((hc' _).1 ((hc _).2 le_rfl))`. Establish `h2` using `valuation_eq_iff_ord.1 h1`.

Rewrite `hR'` using `[IsShellReps, h2, h1]`. Use `hR.sum_eq hR' (gaussTerm_eq hc ha (x := 1) (by simp))` as an intermediate fact. Simplify using `only [one_mul] at this`. Rewrite using `[this, GlobalTheory.LGrp.nabs_eq_zpow, GlobalTheory.LGrp.nabs_eq_zpow, h2]`.
-/
theorem tate_unique {e e' : ℂ} (h : IsTateMeas ψ t χ e) (h' : IsTateMeas ψ t χ e') : e = e' := by
  obtain ⟨c, a, R, hc, ha, hR, rfl⟩ := h
  obtain ⟨c', a', R', hc', ha', hR', rfl⟩ := h'
  obtain rfl := ha.unique ha'
  have h1 : valuation k (c' : k) = valuation k (c : k) :=
    le_antisymm ((hc _).1 ((hc' _).2 le_rfl)) ((hc' _).1 ((hc _).2 le_rfl))
  have h2 := valuation_eq_iff_ord.1 h1
  rw [IsShellReps, h2, h1] at hR'
  have := hR.sum_eq hR' (gaussTerm_eq hc ha (x := 1) (by simp))
  simp only [one_mul] at this
  rw [this, GlobalTheory.LGrp.nabs_eq_zpow, GlobalTheory.LGrp.nabs_eq_zpow, h2]

/- English proof (translation)
Take `⟨c', a, R, hc', ha, hR, he⟩` from `isTateEps_of_isUnram hψ hχ`. Take `rfl` from `ha.unique (hasExponent_zero_iff.2 hχ)`. Establish `h1 : valuation k (c' : k) = valuation k (c : k)` using `le_antisymm ((hψ _).1 ((hc' _).2 le_rfl)) ((hc' _).1 ((hψ _).2 le_rfl))`. Use `⟨c', 0, R, hc', ha, hR, ?_⟩` and prove the remaining obligations. Rewrite using `[he, GlobalTheory.LGrp.nabs_eq_zpow, GlobalTheory.LGrp.nabs_eq_zpow, valuation_eq_iff_ord.1 h1]`.

Simplify using the standard rewrite rules.
-/
theorem tate_unram {c : kˣ} (hψ : HasConductor ψ c) (hχ : IsUnram χ) :
    IsTateMeas ψ t χ (((t * nabs k c : ℝ) : ℂ) * ((χ c)⁻¹ : ℂˣ)) := by
  obtain ⟨c', a, R, hc', ha, hR, he⟩ := isTateEps_of_isUnram hψ hχ
  obtain rfl := ha.unique (hasExponent_zero_iff.2 hχ)
  have h1 : valuation k (c' : k) = valuation k (c : k) :=
    le_antisymm ((hψ _).1 ((hc' _).2 le_rfl)) ((hc' _).1 ((hψ _).2 le_rfl))
  refine ⟨c', 0, R, hc', ha, hR, ?_⟩
  rw [he, GlobalTheory.LGrp.nabs_eq_zpow, GlobalTheory.LGrp.nabs_eq_zpow, valuation_eq_iff_ord.1 h1]
  simp

/- English proof (translation)
Take `⟨⟨e, he, -⟩, hne⟩` from `existsUnique_isTateEps ψ hψ h1 χ hχ`. Establish `h0` using `hne e he`. Take `⟨c, a, R, hc, ha, hR, rfl⟩` from `he`. Establish `hn : (0 : ℝ) < nabs k c`. Unfold `nabs`.

Conclude with `MeasureTheory.distribHaarChar_pos` after adjusting the coercions. Use `⟨Units.mk0 _ (mul_ne_zero (Complex.ofReal_ne_zero.2 (mul_pos ht hn).ne') (right_ne_zero_of_mul h0)), c, a, R, hc, ha, hR, rfl⟩` and prove the remaining obligations.
-/
theorem tate_exists (hψ : Continuous ψ) (h1 : ψ ≠ 1) (hχ : IsSmoothChar χ) (ht : 0 < t) :
    ∃ e : ℂˣ, IsTateMeas ψ t χ e := by
  obtain ⟨⟨e, he, -⟩, hne⟩ := existsUnique_isTateEps ψ hψ h1 χ hχ
  have h0 := hne e he
  obtain ⟨c, a, R, hc, ha, hR, rfl⟩ := he
  have hn : (0 : ℝ) < nabs k c := by
    unfold nabs; exact_mod_cast MeasureTheory.distribHaarChar_pos
  refine ⟨Units.mk0 _ (mul_ne_zero (Complex.ofReal_ne_zero.2 (mul_pos ht hn).ne') (right_ne_zero_of_mul h0)),
    c, a, R, hc, ha, hR, rfl⟩

/- English proof (translation)
Take `⟨c, a, R, hc, ha, hR, rfl⟩` from `h`. Conclude with `⟨c, a, R, hc, ha, hR, by push_cast; ring⟩`.
-/
theorem tate_scale {e : ℂ} (h : IsTateMeas ψ t χ e) (s : ℝ) : IsTateMeas ψ (s * t) χ (s * e) := by
  obtain ⟨c, a, R, hc, ha, hR, rfl⟩ := h
  exact ⟨c, a, R, hc, ha, hR, by push_cast; ring⟩

end Tate

variable {Ω : Type} [Field Ω] {A : ValuationSubring Ω}

/- English proof (translation)
The claim follows from `tate_unique (hε.char L v h ψ hψ h1 t ht a ha χ (isSmoothChar_of_isUnram hχ)) (tate_unram hc hχ)`.
-/
theorem eps_unram {ε : EpsMeasFamily A} (hε : IsDeligneMeas ε) {L : Type} [Field L] [NumberField L] [Algebra L Ω]
    [IsAlgClosure L Ω] {v : HeightOneSpectrum (𝓞 L)} {h : IsPlaceOver A v} {ψ : AddChar (v.adicCompletion L) Circle}
    (hψ : Continuous ψ) (h1 : ψ ≠ 1) {t : ℝ} (ht : 0 < t) {a : Weil h →* (v.adicCompletion L)ˣ} (ha : IsLocalArtin h a)
    {c : (v.adicCompletion L)ˣ} (hc : HasConductor ψ c) {χ : (v.adicCompletion L)ˣ →* ℂˣ} (hχ : IsUnram χ) :
    (ε L v h ψ t (WD.lpOfChar h (χ.comp a) (ha.smooth (isSmoothChar_of_isUnram hχ))) : ℂ) =
      ((t * nabs _ c : ℝ) : ℂ) * ((χ c)⁻¹ : ℂˣ) :=
  tate_unique (hε.char L v h ψ hψ h1 t ht a ha χ (isSmoothChar_of_isUnram hχ)) (tate_unram hc hχ)

/- English proof (translation)
The claim follows from `hε.ind L L v v h h (isLocalExt_self h) ψ ψ hψ h1 hψ (fun z => by simp) t t' ht ht' x y x y (induces_self x) (induces_self y) hd`.
-/
theorem eps_degree_zero {ε : EpsMeasFamily A} (hε : IsDeligneMeas ε) {L : Type} [Field L] [NumberField L] [Algebra L Ω]
    [IsAlgClosure L Ω] {v : HeightOneSpectrum (𝓞 L)} {h : IsPlaceOver A v} {ψ : AddChar (v.adicCompletion L) Circle}
    (hψ : Continuous ψ) (h1 : ψ ≠ 1) {t t' : ℝ} (ht : 0 < t) (ht' : 0 < t') (x y : WD h) (hd : x.lpDim = y.lpDim) :
    ε L v h ψ t x * ε L v h ψ t' y = ε L v h ψ t y * ε L v h ψ t' x :=
  hε.ind L L v v h h (isLocalExt_self h) ψ ψ hψ h1 hψ (fun z => by simp) t t' ht ht' x y x y
    (induces_self x) (induces_self y) hd

def powFam : EpsMeasFamily A := fun _ _ _ _ _ _ _ _ t x => WD.unitOf (t : ℂ) ^ x.lpDim

/- English proof (translation)
Take `⟨n, a, rfl⟩` from `x.exists_rep`. Take `⟨m, b, rfl⟩` from `y.exists_rep`. Simplify using `[powFam, pow_add]`. Use `scale L _ _ _ _ v h ψ _ _ t ht a ha x := by`. Establish `h1 : (t : ℂ) ≠ 0` using `Complex.ofReal_ne_zero.2 ht.ne'`.

Establish `h2 : ((a * t : ℝ) : ℂ) ≠ 0` using `Complex.ofReal_ne_zero.2 (mul_pos ha ht).ne'`. Simplify using `only [powFam, Units.val_pow_eq_pow_val, WD.coe_unitOf h1, WD.coe_unitOf h2]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Use `ind K L _ _ _ _ _ _ _ _ _ _ v v' h h' _ ψ ψ' _ _ _ _ t t' _ _ x₁ x₂ y₁ y₂ i₁ i₂ hd := by`.

Take `⟨m, n, a, b, j, rfl, rfl, hn, -⟩` from `i₁`. Take `⟨m', n', a', b', j', rfl, rfl, hn', -⟩` from `i₂`. Establish `: m = m'` using `by simpa using hd`. Substitute `this` using the available equality. Simplify using `[powFam, hn, hn']`.

Use `char L _ _ _ _ v h ψ _ _ t _ a ha := absurd ha (H L v h a)`.
-/
theorem powFam_isDeligneMeas
    (H : ∀ (L : Type) [Field L] [NumberField L] [Algebra L Ω] [IsAlgClosure L Ω] (v : HeightOneSpectrum (𝓞 L))
      (h : IsPlaceOver A v) (a : Weil h →* (v.adicCompletion L)ˣ), ¬ IsLocalArtin h a) :
    IsDeligneMeas (powFam (A := A)) where
  add L _ _ _ _ v h ψ _ _ t _ x y := by
    obtain ⟨n, a, rfl⟩ := x.exists_rep
    obtain ⟨m, b, rfl⟩ := y.exists_rep
    simp [powFam, pow_add]
  scale L _ _ _ _ v h ψ _ _ t ht a ha x := by
    have h1 : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 ht.ne'
    have h2 : ((a * t : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 (mul_pos ha ht).ne'
    simp only [powFam, Units.val_pow_eq_pow_val, WD.coe_unitOf h1, WD.coe_unitOf h2]
    push_cast; ring
  ind K L _ _ _ _ _ _ _ _ _ _ v v' h h' _ ψ ψ' _ _ _ _ t t' _ _ x₁ x₂ y₁ y₂ i₁ i₂ hd := by
    obtain ⟨m, n, a, b, j, rfl, rfl, hn, -⟩ := i₁
    obtain ⟨m', n', a', b', j', rfl, rfl, hn', -⟩ := i₂
    have : m = m' := by simpa using hd
    subst this
    simp [powFam, hn, hn']
  char L _ _ _ _ v h ψ _ _ t _ a ha := absurd ha (H L v h a)

/- English proof (translation)
Use `⟨powFam, powFam_isDeligneMeas fun L _ _ _ _ v h _ _ => ?_⟩` and prove the remaining obligations. Take `⟨x, hx, hx0⟩` from `Submodule.exists_mem_ne_zero_of_ne_bot v.ne_bot`. Use `(valuation_lt_one_iff' _ _).1 ((h x).2 hx)` as an intermediate fact. Break down `this.2 with h0 | h0` into its components or cases. Conclude with `hx0 (by simpa using h0)`.

Conclude with `h0 trivial`.
-/
theorem trivial_place : ∃ ε : EpsMeasFamily (⊤ : ValuationSubring Ω), IsDeligneMeas ε := by
  refine ⟨powFam, powFam_isDeligneMeas fun L _ _ _ _ v h _ _ => ?_⟩
  obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot v.ne_bot
  have := (valuation_lt_one_iff' _ _).1 ((h x).2 hx)
  rcases this.2 with h0 | h0
  · exact hx0 (by simpa using h0)
  · exact h0 trivial

/- English proof (translation)
Introduce `Ω _ A`. Distinguish the cases in `H : ∀ (L : Type) [Field L] [NumberField L] [Algebra L Ω] [IsAlgClosure L Ω] (v : HeightOneSpectrum (𝓞 L)) (h : IsPlaceOver A v) (a : Weil h →* (v.adicCompletion L)ˣ), ¬ IsLocalArtin h a`. Conclude with `⟨powFam, powFam_isDeligneMeas H⟩`. Assume the negation of the conclusion as `hn`. Conclude with `H fun L _ _ _ _ v h _ _ => hn (MeasModel.exists_of_localLanglands hL L v h).2`.
-/
theorem of_localLanglands (hL : GlobalTheory.Published.LocalLanglandsGL) : GlobalTheory.Published.DeligneLocalConstants := by
  intro Ω _ A
  by_cases H : ∀ (L : Type) [Field L] [NumberField L] [Algebra L Ω] [IsAlgClosure L Ω] (v : HeightOneSpectrum (𝓞 L))
      (h : IsPlaceOver A v) (a : Weil h →* (v.adicCompletion L)ˣ), ¬ IsLocalArtin h a
  · exact ⟨powFam, powFam_isDeligneMeas H⟩
  · by_contra hn
    exact H fun L _ _ _ _ v h _ _ => hn (MeasModel.exists_of_localLanglands hL L v h).2

/- English proof (translation)
Introduce `H`. Use `eps_unram H hψ h1 one_pos ha hc (χ := 1) (fun _ _ => rfl)` as an intermediate fact. Simplify using `[powFam, WD.lpOfChar, WD.coe_unitOf] at this`. Conclude with `hc1 (by exact_mod_cast this.symm)`.
-/
theorem not_powFam {L : Type} [Field L] [NumberField L] [Algebra L Ω]
    [IsAlgClosure L Ω] {v : HeightOneSpectrum (𝓞 L)} {h : IsPlaceOver A v} {ψ : AddChar (v.adicCompletion L) Circle}
    (hψ : Continuous ψ) (h1 : ψ ≠ 1) {a : Weil h →* (v.adicCompletion L)ˣ} (ha : IsLocalArtin h a)
    {c : (v.adicCompletion L)ˣ} (hc : HasConductor ψ c) (hc1 : nabs _ c ≠ 1) : ¬ IsDeligneMeas (powFam (A := A)) := by
  intro H
  have := eps_unram H hψ h1 one_pos ha hc (χ := 1) (fun _ _ => rfl)
  simp [powFam, WD.lpOfChar, WD.coe_unitOf] at this
  exact hc1 (by exact_mod_cast this.symm)

end GlobalTheory.LocLanglands.MeasTest

end

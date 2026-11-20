import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ToroidalChartsForFan

noncomputable section

open AlgebraicGeometry CategoryTheory NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.MumfordChart

namespace GlobalTheory.FanChartTest

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Geo.Tor.Level H}
  {Xo : Moduli D l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F}
  {φ : InvFun (𝓞 E)} {Z : Model Xo c β} {BD : EffCartierData Z.X} {d : ℕ} {x : gen Z}

omit [IsCMField E] in

/- English proof (translation)
Establish `: Module.IsTorsionFree (𝓞 E) X`. Use `Module.IsTorsionFree.of_smul_eq_zero fun a y h => ?_` and prove the remaining obligations. Distinguish the cases in `ha : a = 0`. Conclude with `Or.inl ha`. Use `right`.

Choose the witnesses or unpack the hypotheses as in `⟨b, n, hn, hb⟩ : ∃ (b : 𝓞 E) (n : ℤ), n ≠ 0 ∧ b * a = n := by`. Take `⟨b, hb⟩` from `Ideal.mem_span_singleton'.1 (Ideal.absNorm_mem (Ideal.span {a}))`. Use `⟨b, Ideal.absNorm (Ideal.span {a}), ?_, by simpa using hb⟩` and prove the remaining obligations. Simplify `ha` using `[Ideal.absNorm_eq_zero_iff]`. Establish `: n • y = 0`.

Rewrite using `[← Int.cast_smul_eq_zsmul (𝓞 E), ← hb, mul_smul, h, smul_zero]`. Conclude with `(smul_eq_zero.1 this).resolve_left hn`. Establish `: Module.Flat (𝓞 E) X` using `inferInstance`. Establish `: Module.FinitePresentation (𝓞 E) X` using `Module.finitePresentation_of_finite _ _`. Conclude with `Module.Flat.projective_of_finitePresentation`.
-/
theorem projective_of_free_int (X : Type) [AddCommGroup X] [Module (𝓞 E) X] [Module.Free ℤ X] [Module.Finite (𝓞 E) X] :
    Module.Projective (𝓞 E) X := by
  have : Module.IsTorsionFree (𝓞 E) X := by
    refine Module.IsTorsionFree.of_smul_eq_zero fun a y h => ?_
    by_cases ha : a = 0
    · exact Or.inl ha
    · right
      obtain ⟨b, n, hn, hb⟩ : ∃ (b : 𝓞 E) (n : ℤ), n ≠ 0 ∧ b * a = n := by
        obtain ⟨b, hb⟩ := Ideal.mem_span_singleton'.1 (Ideal.absNorm_mem (Ideal.span {a}))
        refine ⟨b, Ideal.absNorm (Ideal.span {a}), ?_, by simpa using hb⟩
        simpa [Ideal.absNorm_eq_zero_iff] using ha
      have : n • y = 0 := by
        rw [← Int.cast_smul_eq_zsmul (𝓞 E), ← hb, mul_smul, h, smul_zero]
      exact (smul_eq_zero.1 this).resolve_left hn
  have : Module.Flat (𝓞 E) X := inferInstance
  have : Module.FinitePresentation (𝓞 E) X := Module.finitePresentation_of_finite _ _
  exact Module.Flat.projective_of_finitePresentation

/- English proof (translation)
Break down `Nat.eq_zero_or_pos m with rfl | hm` into its components or cases. Use `(h _).1 hx` as an intermediate fact. Rewrite `this` using `[Finset.univ_eq_empty, Finset.prod_empty]`. Conclude with `absurd ((Ideal.eq_top_iff_one _).2 this) (closedPoint _ : PrimeSpectrum _).isPrime.ne_top`. Conclude with `hm`.
-/
theorem pos_of_mem {k : Type} [Field k] {m e : ℕ} {ξ : Sp (ChartRing k m e) ⟶ gen Z}
    (h : ∀ p : Sp (ChartRing k m e), ξ p ∈ genBd Z ↔ ∏ i, bdParam k m e i ∈ p.asIdeal)
    (hx : ξ (closedPoint _) ∈ genBd Z) : 0 < m := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · have := (h _).1 hx
    rw [Finset.univ_eq_empty, Finset.prod_empty] at this
    exact absurd ((Ideal.eq_top_iff_one _).2 this) (closedPoint _ : PrimeSpectrum _).isPrime.ne_top
  · exact hm

/- English proof (translation)
Introduce and unpack `⟨k, _, m, e, ξ, t, P, γ, δ, a, rfl, -, -, h₃, -, -, h₀, h₆, -⟩`. Use `projective_of_free_int (E := E) P.D.toPre.X` as an intermediate fact. Establish `: Subsingleton P.D.toPre.X` using `Module.finrank_zero_iff.1 (Nat.le_zero.1 (h0 ▸ h₀))`. Conclude with `h₆.linearIndependent.ne_zero ⟨0, pos_of_mem h₃ hx⟩ (Subsingleton.elim _ _)`.
-/
theorem not_hasChartOf_of_min_eq_zero (h0 : min D.p D.q = 0) (hx : x ∈ genBd Z) : ¬ HasChartOf φ Z BD d x := by
  rintro ⟨k, _, m, e, ξ, t, P, γ, δ, a, rfl, -, -, h₃, -, -, h₀, h₆, -⟩
  have := projective_of_free_int (E := E) P.D.toPre.X
  have : Subsingleton P.D.toPre.X := Module.finrank_zero_iff.1 (Nat.le_zero.1 (h0 ▸ h₀))
  exact h₆.linearIndependent.ne_zero ⟨0, pos_of_mem h₃ hx⟩ (Subsingleton.elim _ _)

/- English proof (translation)
Take `⟨k, _, m, e, ξ, t, P, γ, δ, a, rfl, -, -, h₃, -, -, h₀, h₆, h₇, h₈, h₉⟩` from `h`. Use `projective_of_free_int (E := E) P.D.toPre.X` as an intermediate fact. Set `i : Fin m` to `⟨0, pos_of_mem h₃ hx⟩`. Establish `hp` using `(hφ _ h₀).pos _ (h₆.mem i) (h₆.nonneg i) (h₆.linearIndependent.ne_zero i)`. Establish `ha : a i ≠ 0`.

Establish `e` using `h₈ i`. Rewrite `e` using `[h₇, h₆.evalZ_smul]`. Establish `h1 : (0 : ℝ) < d` using `by exact_mod_cast hd`. Establish `h2 : (0 : ℝ) < l.M'` using `by exact_mod_cast Nat.pos_of_ne_zero (level_ne_zero l)`. Establish `: (0 : ℝ) < a i` using `by rw [e]; positivity`.

Conclude with `this.ne'` after adjusting the coercions. Introduce `ht`. Establish `ht' : FinalTheorems.stalkId BD.idealSheaf ((ξ ≫ genι Z) (closedPoint _)) = ⊤` using `ht`. Rewrite `h₉` using `[idlAlong, ht', Ideal.map_top, eq_comm, Ideal.span_singleton_eq_top]`. Establish `hu` using `(isUnit_pow_iff ha).1 (isUnit_of_dvd_unit (Finset.dvd_prod_of_mem (fun j => bdParam k m e j ^ a j) (Finset.mem_univ i)) h₉)`.

Simplify `hu` using `[MvPowerSeries.isUnit_iff_constantCoeff]`.
-/
theorem idlAlong_ne_top (hφ : IsPolFan H.bar (min D.p D.q) φ) (hd : 1 ≤ d) (hx : x ∈ genBd Z)
    (h : HasChartOf φ Z BD d x) : FinalTheorems.stalkId BD.idealSheaf (genι Z x) ≠ ⊤ := by
  obtain ⟨k, _, m, e, ξ, t, P, γ, δ, a, rfl, -, -, h₃, -, -, h₀, h₆, h₇, h₈, h₉⟩ := h
  have := projective_of_free_int (E := E) P.D.toPre.X
  let i : Fin m := ⟨0, pos_of_mem h₃ hx⟩
  have hp := (hφ _ h₀).pos _ (h₆.mem i) (h₆.nonneg i) (h₆.linearIndependent.ne_zero i)
  have ha : a i ≠ 0 := by
    have e := h₈ i
    rw [h₇, h₆.evalZ_smul] at e
    have h1 : (0 : ℝ) < d := by exact_mod_cast hd
    have h2 : (0 : ℝ) < l.M' := by exact_mod_cast Nat.pos_of_ne_zero (level_ne_zero l)
    have : (0 : ℝ) < a i := by rw [e]; positivity
    exact_mod_cast this.ne'
  intro ht
  have ht' : FinalTheorems.stalkId BD.idealSheaf ((ξ ≫ genι Z) (closedPoint _)) = ⊤ := ht
  rw [idlAlong, ht', Ideal.map_top, eq_comm, Ideal.span_singleton_eq_top] at h₉
  have hu := (isUnit_pow_iff ha).1 (isUnit_of_dvd_unit (Finset.dvd_prod_of_mem (fun j => bdParam k m e j ^ a j) (Finset.mem_univ i)) h₉)
  simpa [MvPowerSeries.isUnit_iff_constantCoeff] using hu

/- English proof (translation)
Introduce `h` and use `idlAlong_ne_top hφ hd hx h (by rw [EffCartierData.stalkId_idealSheaf (EffCartierData.zero Z.X) PUnit.unit _ (Set.mem_univ _), Ideal.span_singleton_eq_top] exact (isUnit_one.map _))`.
-/
theorem not_hasChartOf_zero (hφ : IsPolFan H.bar (min D.p D.q) φ) (hd : 1 ≤ d) (hx : x ∈ genBd Z) :
    ¬ HasChartOf φ Z (EffCartierData.zero Z.X) d x := fun h => idlAlong_ne_top hφ hd hx h (by
  rw [EffCartierData.stalkId_idealSheaf (EffCartierData.zero Z.X) PUnit.unit _ (Set.mem_univ _), Ideal.span_singleton_eq_top]
  exact (isUnit_one.map _))

/- English proof (translation)
Establish `h0 : min Dw.p Dw.q = 0` using `by omega`. Take `⟨Y, BD, d, k, -, -, -, -, -, h₅, -⟩` from `h E H Dw (by omega) (InvFun.minVal _) (h0 ▸ isPolFan_zero) (h0 ▸ noSelfInt_zero) l Xo c`. Conclude with `⟨Y, fun x hx => not_hasChartOf_of_min_eq_zero h0 hx (h₅ x hx)⟩`.
-/
theorem exists_model_definite (h : GlobalTheory.Published.ToroidalChartsForFan) {Dw : Datum H} (hp : 1 ≤ Dw.p) (hq : Dw.q = 0)
    {l : Geo.Tor.Level H} (Xo : Moduli Dw l) (c : Coeff l) :
    ∃ Y : Model Xo c (RingHom.id c.F), ∀ x, x ∉ genBd Y := by
  have h0 : min Dw.p Dw.q = 0 := by omega
  obtain ⟨Y, BD, d, k, -, -, -, -, -, h₅, -⟩ := h E H Dw (by omega) (InvFun.minVal _) (h0 ▸ isPolFan_zero)
    (h0 ▸ noSelfInt_zero) l Xo c
  exact ⟨Y, fun x hx => not_hasChartOf_of_min_eq_zero h0 hx (h₅ x hx)⟩

end GlobalTheory.FanChartTest

import Development.AbelianVarietyTheory.Definitions.Divisors.SemiposAtOfPositive
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NefFibOfCurveDegreesNonneg
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NefFibOfSurjectivePullback
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PsumSmul
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CurveTopSelfIntersectionVanishStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CurveDegreeDataOutsideSetStatement
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsX
open CategoryTheory AlgebraicGeometry TopologicalSpace NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.CechPic
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.TrueGeo
open scoped ENNReal Classical
open Limits

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.NefDeRhamRoots

/- English proof (translation)
Introduce `hX hP hH D O hO A T H h B hB w hdom hnef c X' p' hp' ρ hρ q _ hq Z i _ _ _ hd`. Establish `hq3 : (2 : ℝ) < q`. Establish `h2 : (2 : ℕ) ∈ FlagAr.setB O.Y B`. Use `Finset.mem_union_right _ (Finset.mem_union_left _ ?_)` and prove the remaining obligations. Rewrite using `[Nat.mem_primeFactors]`.

Use `⟨Nat.prime_two, dvd_mul_right _ _, ?_⟩` and prove the remaining obligations. Conclude with `mul_ne_zero two_ne_zero (Int.natAbs_ne_zero.2 (NumberField.discr_ne_zero _))`. Establish `hne : q ≠ 2` using `fun e => hq (e ▸ h2)`. Use `(Fact.out : q.Prime).two_le` as an intermediate fact. Establish `: 3 ≤ q` using `by omega`.

Conclude with `(show 2 < q by omega)` after adjusting the coercions. Establish `hBq : B ≤ q`. Establish `hq' : q ∉ (Finset.range (⌊B⌋₊ + 1)).filter Nat.Prime` using `fun hm => hq (Finset.mem_union_left _ hm)`. Rewrite `hq'` using `[Finset.mem_filter, Finset.mem_range]`. Establish `: ⌊B⌋₊ + 1 ≤ q`.

Assume the negation of the conclusion as `hc`. Conclude with `hq' ⟨by omega, Fact.out⟩`. Establish `hfl` using `Nat.lt_floor_add_one B`. Establish `hc : ((⌊B⌋₊ + 1 : ℕ) : ℝ) ≤ q` using `by exact_mod_cast this`. Move the coercions through the operations in `at hc`.

Combine the linear equalities and inequalities to obtain the conclusion. Establish `hS : ∀ τ (k : Fin O.N), |w τ k| ≤ WeightThresholdDefs.supAbs O.Y w` using `fun τ k => le_ciSup (f := fun x : DV.Rt D.what₂.Tau O.Y.N => |w x.1 x.2|) (Set.finite_range _).bddAbove (τ, k)`. Establish `hgap : ∀ τ, 4 * (D.R.f : ℝ) * WeightThresholdDefs.supAbs O.Y w ≤ ((q : ℝ) - 2) * (w τ ⟨O.j - 1, by have` using `O.indef; exact (show O.j - 1 < O.N by omega)⟩ - w τ ⟨O.j, O.indef.2⟩) := fun τ => by`. Establish `h1` using `hnef τ`. Establish `hg0 : 0 ≤ WeightThresholdDefs.gap O.Y w τ`.

Unfold `WeightThresholdDefs.gap`. Use `hdom τ ⟨O.Y.j - 1, by have := O.Y.j_lt; omega⟩ ⟨O.Y.j, O.Y.j_lt⟩ (by rw [Fin.le_iff_val_le_val]; simp)` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion. Establish `h2 : ((B : ℝ) - 2) * WeightThresholdDefs.gap O.Y w τ ≤ ((q : ℝ) - 2) * WeightThresholdDefs.gap O.Y w τ` using `mul_le_mul_of_nonneg_right (by linarith) hg0`. Conclude with `h1.trans (h2.trans_eq rfl)`.

Establish `hsum : ∀ r : D.what₂.Tau → Fin O.N → ℝ, GlobalTheory.PowerSumSmul.DegData O.j (q : ℝ) r → 0 ≤ ∑ τ, ∑ k, -(w τ k) * r τ k` using `fun r hr => GlobalTheory.PowerSumSmul.chain O.j O.indef.1 O.indef.2 (q : ℝ) (D.R.f : ℝ) (WeightThresholdDefs.supAbs O.Y w) hq3 (by rw [D.what₂.card_Tau]) w r hdom hS hgap hr`. Rewrite using `[Fintype.sum_prod_type]`. Break down `GlobalTheory.T.curve_top_self_intersection_vanish (𝓞 D.what₂.LL) (h.mdl (FlagAr.setB O.Y B) c).V.X X' (h.mdl (FlagAr.setB O.Y B) c).V.p p' (h.mdl (FlagAr.setB O.Y B) c).V.ar.isProjOver hp' ρ hρ q Z i hd with h0 | ⟨m, Z', i', _, _, _, hd', hm⟩` into its components or cases. Establish `e : (fun (τ : D.what₂.Tau) (k : Fin O.N) => (topSelfIntersection (ZMod q) ((((h.mdl (FlagAr.setB O.Y B) c).root (FlagAr.setB O.Y B) (τ, k)).pull ρ hρ).B.pull i) 1 : ℝ)) = fun _ _ => (0 : ℝ)`. Use function extensionality and compare the values at `τ k`.

Use `h0 _ ((h.mdl (FlagAr.setB O.Y B) c).root (FlagAr.setB O.Y B) (τ, k)).isLB` as an intermediate fact. Conclude with `this` after adjusting the coercions. Use `hsum _ (e ▸ GlobalTheory.PowerSumSmul.DegData.zero O.j (q : ℝ) hq3.le)` as an intermediate fact. Conclude with `this`. Establish `hD` using `(GlobalTheory.T.curve_degree_data_outside_set hX hP hH D O hO A T H h B hB c q hq Z' i' hd').smul (Nat.cast_nonneg m)`.

Establish `e : (fun (τ : D.what₂.Tau) (k : Fin O.N) => (topSelfIntersection (ZMod q) ((((h.mdl (FlagAr.setB O.Y B) c).root (FlagAr.setB O.Y B) (τ, k)).pull ρ hρ).B.pull i) 1 : ℝ)) = fun τ k => (m : ℝ) * (topSelfIntersection (ZMod q) (((h.mdl (FlagAr.setB O.Y B) c).root (FlagAr.setB O.Y B) ( …`. Use function extensionality and compare the values at `τ k`. Use `hm _ ((h.mdl (FlagAr.setB O.Y B) c).root (FlagAr.setB O.Y B) (τ, k)).isLB` as an intermediate fact. Conclude with `this` after adjusting the coercions. Conclude with `hsum _ (e ▸ hD)`.
-/
theorem nonneg_roots : GlobalTheory.CovTop.HypothesesXH → Hypotheses2 → HypothesesH → ∀ (D : D7) (O : Setup D), O.Core → ∀ (A : SlopeTestRemainingChoices O.Y) (T : Real0 O.Y) (H : Ht O.Y) (h : O.Reads A T H),
  ∀ (B : ℝ), 2 ≤ B → ∀ (w : Wt O.Y), WeightThresholdDefs.Dominant O.Y w → NefCond O.Y B w →
  ∀ (c : O.s.Comp) (X' : Scheme.{0}) (p' : X' ⟶ Sp (𝓞 D.what₂.LL)), IsProjOver p' →
  ∀ (ρ : X' ⟶ (h.mdl (FlagAr.setB O.Y B) c).V.X) (hρ : ρ ≫ (h.mdl (FlagAr.setB O.Y B) c).V.p = p')
    (q : ℕ) [Fact q.Prime], q ∉ FlagAr.setB O.Y B →
  ∀ (Z : Scheme.{0}) (i : Z ⟶ X') [IsClosedImmersion i] [IsIntegral Z] [Algebra (ZMod q) Γ(Z, ⊤)],
    topologicalKrullDim Z = 1 →
    0 ≤ ∑ x, -(w x.1 x.2) *
      (topSelfIntersection (ZMod q) ((((h.mdl (FlagAr.setB O.Y B) c).root (FlagAr.setB O.Y B) x).pull ρ hρ).B.pull i) 1 : ℝ) := by
  intro hX hP hH D O hO A T H h B hB w hdom hnef c X' p' hp' ρ hρ q _ hq Z i _ _ _ hd

  have hq3 : (2 : ℝ) < q := by
    have h2 : (2 : ℕ) ∈ FlagAr.setB O.Y B := by
      refine Finset.mem_union_right _ (Finset.mem_union_left _ ?_)
      rw [Nat.mem_primeFactors]
      refine ⟨Nat.prime_two, dvd_mul_right _ _, ?_⟩
      exact mul_ne_zero two_ne_zero (Int.natAbs_ne_zero.2 (NumberField.discr_ne_zero _))
    have hne : q ≠ 2 := fun e => hq (e ▸ h2)
    have := (Fact.out : q.Prime).two_le
    have : 3 ≤ q := by omega
    exact_mod_cast (show 2 < q by omega)
  have hBq : B ≤ q := by
    have hq' : q ∉ (Finset.range (⌊B⌋₊ + 1)).filter Nat.Prime := fun hm => hq (Finset.mem_union_left _ hm)
    rw [Finset.mem_filter, Finset.mem_range] at hq'
    have : ⌊B⌋₊ + 1 ≤ q := by
      by_contra hc
      exact hq' ⟨by omega, Fact.out⟩
    have hfl := Nat.lt_floor_add_one B
    have hc : ((⌊B⌋₊ + 1 : ℕ) : ℝ) ≤ q := by exact_mod_cast this
    push_cast at hc
    linarith
  have hS : ∀ τ (k : Fin O.N), |w τ k| ≤ WeightThresholdDefs.supAbs O.Y w := fun τ k =>
    le_ciSup (f := fun x : DV.Rt D.what₂.Tau O.Y.N => |w x.1 x.2|) (Set.finite_range _).bddAbove (τ, k)
  have hgap : ∀ τ, 4 * (D.R.f : ℝ) * WeightThresholdDefs.supAbs O.Y w ≤
      ((q : ℝ) - 2) * (w τ ⟨O.j - 1, by have := O.indef; exact (show O.j - 1 < O.N by omega)⟩ - w τ ⟨O.j, O.indef.2⟩) := fun τ => by
    have h1 := hnef τ
    have hg0 : 0 ≤ WeightThresholdDefs.gap O.Y w τ := by
      unfold WeightThresholdDefs.gap
      have := hdom τ ⟨O.Y.j - 1, by have := O.Y.j_lt; omega⟩ ⟨O.Y.j, O.Y.j_lt⟩
        (by rw [Fin.le_iff_val_le_val]; simp)
      linarith
    have h2 : ((B : ℝ) - 2) * WeightThresholdDefs.gap O.Y w τ ≤ ((q : ℝ) - 2) * WeightThresholdDefs.gap O.Y w τ :=
      mul_le_mul_of_nonneg_right (by linarith) hg0
    exact h1.trans (h2.trans_eq rfl)

  have hsum : ∀ r : D.what₂.Tau → Fin O.N → ℝ, GlobalTheory.PowerSumSmul.DegData O.j (q : ℝ) r →
      0 ≤ ∑ τ, ∑ k, -(w τ k) * r τ k := fun r hr =>
    GlobalTheory.PowerSumSmul.chain O.j O.indef.1 O.indef.2 (q : ℝ) (D.R.f : ℝ) (WeightThresholdDefs.supAbs O.Y w) hq3
      (by rw [D.what₂.card_Tau]) w r hdom hS hgap hr
  rw [Fintype.sum_prod_type]
  rcases GlobalTheory.T.curve_top_self_intersection_vanish (𝓞 D.what₂.LL) (h.mdl (FlagAr.setB O.Y B) c).V.X X' (h.mdl (FlagAr.setB O.Y B) c).V.p p' (h.mdl (FlagAr.setB O.Y B) c).V.ar.isProjOver hp' ρ hρ q Z i hd with h0 | ⟨m, Z', i', _, _, _, hd', hm⟩
  · have e : (fun (τ : D.what₂.Tau) (k : Fin O.N) =>
        (topSelfIntersection (ZMod q) ((((h.mdl (FlagAr.setB O.Y B) c).root (FlagAr.setB O.Y B) (τ, k)).pull ρ hρ).B.pull i) 1 : ℝ)) =
        fun _ _ => (0 : ℝ) := by
      funext τ k
      have := h0 _ ((h.mdl (FlagAr.setB O.Y B) c).root (FlagAr.setB O.Y B) (τ, k)).isLB
      exact_mod_cast this
    have := hsum _ (e ▸ GlobalTheory.PowerSumSmul.DegData.zero O.j (q : ℝ) hq3.le)
    exact this
  · have hD := (GlobalTheory.T.curve_degree_data_outside_set hX hP hH D O hO A T H h B hB c q hq Z' i' hd').smul (Nat.cast_nonneg m)
    have e : (fun (τ : D.what₂.Tau) (k : Fin O.N) =>
        (topSelfIntersection (ZMod q) ((((h.mdl (FlagAr.setB O.Y B) c).root (FlagAr.setB O.Y B) (τ, k)).pull ρ hρ).B.pull i) 1 : ℝ)) =
        fun τ k => (m : ℝ) * (topSelfIntersection (ZMod q) (((h.mdl (FlagAr.setB O.Y B) c).root (FlagAr.setB O.Y B) (τ, k)).B.pull i') 1 : ℝ) := by
      funext τ k
      have := hm _ ((h.mdl (FlagAr.setB O.Y B) c).root (FlagAr.setB O.Y B) (τ, k)).isLB
      exact_mod_cast this
    exact hsum _ (e ▸ hD)

end GlobalTheory.NefDeRhamRoots

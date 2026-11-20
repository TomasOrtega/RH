import Mathlib
import Development.AbelianVarietyTheory.Statements.HeightBoundStatement.HTBoundSt
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.AmpleOnAbelianBase
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.AdmissibleStageOfPackage
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IntOIsLocalRing
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LatDRSubsetLatHT

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.Geo GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad
open Formalism.MainNotions.DIV.Cons (intO)
open GlobalTheory.FactorDepth

namespace GlobalTheory.HTFrame

attribute [local instance] Over.cartesianMonoidalCategory

/- English proof (translation)
Establish `hc0 : 0 < c` using `by linarith`. Break down `B.eq_empty_or_nonempty with rfl | hne` into its components or cases. Rewrite using `[Set.subset_empty_iff.1 hAB, sub_self, abs_zero]`. Conclude with `Real.log_nonneg hc`. Take `⟨r0, hr0⟩` from `hne`.

Establish `bB : BddBelow B` using `⟨0, hB⟩`. Establish `bA : BddBelow A` using `bB.mono hAB`. Establish `h1 : sInf B ≤ sInf A` using `csInf_le_csInf bB ⟨_, hBA r0 hr0⟩ hAB`. Establish `h2 : sInf A ≤ c * sInf B`. Rewrite using `[← div_le_iff₀' hc0]`.

Conclude with `le_csInf ⟨r0, hr0⟩ fun r hr => (div_le_iff₀' hc0).2 (csInf_le bA (hBA r hr))`. Establish `h0 : 0 ≤ sInf B` using `le_csInf ⟨r0, hr0⟩ hB`. Break down `h0.eq_or_lt with h | h` into its components or cases. Establish `: sInf A = sInf B` using `le_antisymm (by rw [← h] at h2 ⊢; simpa using h2) h1`. Rewrite using `[this, sub_self, abs_zero]`.

Conclude with `Real.log_nonneg hc`. Establish `h3` using `Real.log_le_log h h1`. Establish `h4` using `Real.log_le_log (h.trans_le h1) h2`. Rewrite `h4` using `[Real.log_mul hc0.ne' h.ne']`. Rewrite using `[abs_of_nonneg (by linarith)]`.

Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem abs_log_sInf_sub_le {A B : Set ℝ} {c : ℝ} (hc : 1 ≤ c) (hB : ∀ r ∈ B, 0 ≤ r) (hAB : A ⊆ B)
    (hBA : ∀ r ∈ B, c * r ∈ A) : |Real.log (sInf A) - Real.log (sInf B)| ≤ Real.log c := by
  have hc0 : 0 < c := by linarith
  rcases B.eq_empty_or_nonempty with rfl | hne
  · rw [Set.subset_empty_iff.1 hAB, sub_self, abs_zero]
    exact Real.log_nonneg hc
  obtain ⟨r0, hr0⟩ := hne
  have bB : BddBelow B := ⟨0, hB⟩
  have bA : BddBelow A := bB.mono hAB
  have h1 : sInf B ≤ sInf A := csInf_le_csInf bB ⟨_, hBA r0 hr0⟩ hAB
  have h2 : sInf A ≤ c * sInf B := by
    rw [← div_le_iff₀' hc0]
    exact le_csInf ⟨r0, hr0⟩ fun r hr => (div_le_iff₀' hc0).2 (csInf_le bA (hBA r hr))
  have h0 : 0 ≤ sInf B := le_csInf ⟨r0, hr0⟩ hB
  rcases h0.eq_or_lt with h | h
  · have : sInf A = sInf B := le_antisymm (by rw [← h] at h2 ⊢; simpa using h2) h1
    rw [this, sub_self, abs_zero]
    exact Real.log_nonneg hc
  · have h3 := Real.log_le_log h h1
    have h4 := Real.log_le_log (h.trans_le h1) h2
    rw [Real.log_mul hc0.ne' h.ne'] at h4
    rw [abs_of_nonneg (by linarith)]
    linarith

section Lat

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {X : Scheme.{0}}
  (t : SAB H X)

open MonObj in

/- English proof (translation)
Take `⟨u, hu, rfl⟩` from `h`. Set `δ : tEpsG x ⟶ tEpsG x` to `Over.homMk (spMap (epsMul a)) (by show spMap (epsMul a) ≫ spMap (algebraMap S (DualNumber S)) ≫ x = spMap (algebraMap S (DualNumber S)) ≫ x`. Rewrite using `[← Category.assoc, spMap_comp']`. Use `congr 2`. Use `RingHom.ext fun r => ?_` and prove the remaining obligations.

Apply the tactic sequence `ext <;> simp [epsMul, TrivSqZeroExt.algebraMap_eq_inl])`. Use `⟨fun i => δ ≫ u i, fun i => ?_, ?_⟩` and prove the remaining obligations. Simplify using `only [Over.comp_left, δ, Over.homMk_left]`. Rewrite using `[hu i, ← Category.assoc, spMap_comp']`. Use `congr 2`.

Use `RingHom.ext fun r => ?_` and prove the remaining obligations. Use `ext`. Simplify using `[epsMul]`. Simplify using `[epsMul]`. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[List.prod_ofFn, List.prod_ofFn, ← comp_prodT]`. Both sides reduce to the same expression.
-/
theorem comb_smul {S : Type} [CommRing S] (a : S) {x : Sp S ⟶ X} {m : ℕ}
    {v : Fin m → (Sp (DualNumber S) ⟶ t.G.left)} {cf : Fin m → S} {w : Sp (DualNumber S) ⟶ t.G.left}
    (h : IsCombAtG t x v cf w) : IsCombAtG t x v (fun i => a * cf i) (spMap (epsMul a) ≫ w) := by
  obtain ⟨u, hu, rfl⟩ := h
  let δ : tEpsG x ⟶ tEpsG x := Over.homMk (spMap (epsMul a)) (by
    show spMap (epsMul a) ≫ spMap (algebraMap S (DualNumber S)) ≫ x = spMap (algebraMap S (DualNumber S)) ≫ x
    rw [← Category.assoc, spMap_comp']
    congr 2
    refine RingHom.ext fun r => ?_
    ext <;> simp [epsMul, TrivSqZeroExt.algebraMap_eq_inl])
  refine ⟨fun i => δ ≫ u i, fun i => ?_, ?_⟩
  · simp only [Over.comp_left, δ, Over.homMk_left]
    rw [hu i, ← Category.assoc, spMap_comp']
    congr 2
    refine RingHom.ext fun r => ?_
    ext
    · simp [epsMul]
    · simp [epsMul]
      ring
  · rw [List.prod_ofFn, List.prod_ofFn, ← comp_prodT]
    rfl

variable {C : Type} [NontriviallyNormedField C] [IsUltrametricDist C]

/- English proof (translation)
The claim follows from `|Real.log (grNorm t x Λ u i) - Real.log (grNorm t x Λ' u i)| ≤ Real.log ‖a‖⁻¹ := by refine abs_log_sInf_sub_le ((one_le_inv₀ (norm_pos_iff.2 ha)).2 ha1) ?_ ?_ ?_ · rintro r ⟨cf, -, -, -, rfl⟩ positivity · rintro r ⟨cf, h3, h4, ⟨w, hw, hc⟩, rfl⟩ exact ⟨cf, h3, h4, ⟨w, h1 hw, hc⟩, …`.
-/
theorem abs_log_grNorm_sub_le (x : Sp C ⟶ X) {Λ Λ' : Set (Sp (DualNumber C) ⟶ t.G.left)} {a : C} (ha : a ≠ 0)
    (ha1 : ‖a‖ ≤ 1) (h1 : Λ ⊆ Λ') (h2 : ∀ v ∈ Λ', spMap (epsMul a) ≫ v ∈ Λ) {m : ℕ}
    (u : Fin m → (Sp (DualNumber C) ⟶ t.G.left)) (i : Fin m) :
    |Real.log (grNorm t x Λ u i) - Real.log (grNorm t x Λ' u i)| ≤ Real.log ‖a‖⁻¹ := by
  refine abs_log_sInf_sub_le ((one_le_inv₀ (norm_pos_iff.2 ha)).2 ha1) ?_ ?_ ?_
  · rintro r ⟨cf, -, -, -, rfl⟩
    positivity
  · rintro r ⟨cf, h3, h4, ⟨w, hw, hc⟩, rfl⟩
    exact ⟨cf, h3, h4, ⟨w, h1 hw, hc⟩, rfl⟩
  · rintro r ⟨cf, h3, h4, ⟨w, hw, hc⟩, rfl⟩
    refine ⟨fun k => a * cf k, mul_ne_zero ha h3, fun k hk => by simp [h4 k hk], ⟨_, h2 w hw, comb_smul t a hc⟩, ?_⟩
    rw [norm_mul, mul_inv]

end Lat

section Ext

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l}

/- English proof (translation)
Take `⟨-, xO, hx, -⟩` from `GlobalTheory.ShFam.Pad.Test.latDR_nonempty Z x`. Use `⟨xO, hx, fun xO' hx' => ?_⟩` and prove the remaining obligations. Use `isProper_toroidalModel_structureMap Z` as an intermediate fact. Establish `hs : IsSeparated (terminal.from Z.X)`. Rewrite using `[← terminal.comp_from Z.s]`.

Use `infer_instance`. Set `S : ValuativeCommSq (terminal.from Z.X)` to `{ R := intO C, K := C, i₁ := x, i₂ := terminal.from _, commSq := ⟨terminal.hom_ext _ _⟩ }`. Establish `hu` using `IsSeparated.valuativeCriterion (terminal.from Z.X) S`. Conclude with `congrArg CommSq.LiftStruct.l (hu.elim ⟨xO', hx', terminal.hom_ext _ _⟩ ⟨xO, hx, terminal.hom_ext _ _⟩)`.
-/
theorem existsUnique_ext (Z : Model Xo c (algebraMap (𝓞 c.F) c.F)) {C : Type} [NontriviallyNormedField C]
    [IsUltrametricDist C] (x : Sp C ⟶ Z.X) : ∃! xO : Sp ↥(intO C) ⟶ Z.X, spMap (intO C).subtype ≫ xO = x := by
  obtain ⟨-, xO, hx, -⟩ := GlobalTheory.ShFam.Pad.Test.latDR_nonempty Z x
  refine ⟨xO, hx, fun xO' hx' => ?_⟩
  have := isProper_toroidalModel_structureMap Z
  have hs : IsSeparated (terminal.from Z.X) := by
    rw [← terminal.comp_from Z.s]
    infer_instance
  let S : ValuativeCommSq (terminal.from Z.X) :=
    { R := intO C, K := C, i₁ := x, i₂ := terminal.from _, commSq := ⟨terminal.hom_ext _ _⟩ }
  have hu := IsSeparated.valuativeCriterion (terminal.from Z.X) S
  exact congrArg CommSq.LiftStruct.l
    (hu.elim ⟨xO', hx', terminal.hom_ext _ _⟩ ⟨xO, hx, terminal.hom_ext _ _⟩)

end Ext

end GlobalTheory.HTFrame

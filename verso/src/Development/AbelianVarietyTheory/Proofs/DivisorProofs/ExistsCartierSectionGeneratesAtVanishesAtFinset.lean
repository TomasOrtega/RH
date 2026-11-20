import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GapGeSubKapBase
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.HSApp GlobalTheory.Cartier
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW secZ ptF LiesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR levDet secRing move)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.OrbitSep

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.Cartier.CommonEqnOpen

variable {X : Scheme.{0}} [IsIntegral X]

/- English proof (translation)
Proceed by induction. Treat this case separately. Treat this case separately. A detailed English derivation is pending.
-/
theorem unitAt_pow {x : X} {f : X.functionField} (h : UnitAt x f) (n : ℕ) : UnitAt x (f ^ n) := by
  induction n with
  | zero => rw [pow_zero]; exact unitAt_one x
  | succ n ih => rw [pow_succ]; exact ih.mul h

/- English proof (translation)
Extract witnesses or component facts from the available result. Establish an intermediate fact. Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact.

Rewrite the indicated hypotheses using the stated equalities. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Rewrite the conclusion using the stated equalities.
-/
theorem exists_pow_mul_eq {U : X.Opens} (hU : IsAffineOpen U) (hg : genericPoint X ∈ U) (t : Γ(X, U))
    (ht : genericPoint X ∈ X.basicOpen t) {f : X.functionField}
    (h : ∀ z ∈ X.basicOpen t, RegAt z f) :
    ∃ (n : ℕ) (a : Γ(X, U)), fnOf U hg t ^ n * f = fnOf U hg a := by
  obtain ⟨b, rfl⟩ := exists_fnOf_eq ht h
  have := hU.isLocalization_basicOpen t
  obtain ⟨n, a, e⟩ := IsLocalization.Away.surj t b
  refine ⟨n, a, ?_⟩
  have e' := congrArg (fnOf _ ht) e
  rw [map_mul, map_pow] at e'
  have k (c : Γ(X, U)) : fnOf _ ht (algebraMap Γ(X, U) Γ(X, X.basicOpen t) c) =
      fnOf U hg c := fnOf_resG (X.basicOpen_le t) ht c
  rw [k, k] at e'
  rw [← e', mul_comm]

/- English proof (translation)
Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Establish an intermediate fact.

Rewrite the conclusion using the stated equalities. Supply the required witnesses or components. Extract witnesses or component facts from the available result. Rewrite the indicated hypotheses using the stated equalities. Establish an intermediate fact.

Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities.

Apply an available result and prove the equalities needed to match it to the conclusion. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Rewrite the conclusion using the stated equalities. Clear the denominators using the available nonvanishing facts.

A detailed English derivation is pending.
-/
theorem exists_regularAt {U : X.Opens} (hU : IsAffineOpen U) {D : CartierDiv X} {x : X}
    (hxU : x ∈ U) {g : X.functionFieldˣ} (hg : D.IsEqn x g) {y : X} (hyU : y ∈ U) :
    ∃ s : Γ(X, U), x ∈ X.basicOpen s ∧
      D.RegularAt y (fnOf U (gen_mem hxU) s * (g : X.functionField)⁻¹) := by
  obtain ⟨W, hW, hgW⟩ := hg.exists_nhds
  obtain ⟨V, hV, g', hgV⟩ := D.exists_isEqn_nhds y
  obtain ⟨t, htW, ht⟩ := hU.exists_basicOpen_le ⟨x, hW⟩ hxU
  obtain ⟨t', htV, ht'⟩ := hU.exists_basicOpen_le ⟨y, hV⟩ hyU
  have hgen : genericPoint X ∈ X.basicOpen (t * t') := by
    rw [X.basicOpen_mul]; exact ⟨gen_mem ht, gen_mem ht'⟩
  obtain ⟨n, a, e⟩ := exists_pow_mul_eq hU (gen_mem hxU) (t * t') hgen
    (f := (g' : X.functionField) / g) fun z hz => by
      rw [X.basicOpen_mul] at hz
      exact ((hgW z (htW hz.1)).iff_unitAt.1 (hgV z (htV hz.2))).regAt
  have hu : UnitAt y (fnOf U (gen_mem hxU) (t' ^ n)) := by
    rw [map_pow]; exact unitAt_pow ((unitAt_fnOf_iff hyU _ _).2 ht') n
  refine ⟨t ^ n, (unitAt_fnOf_iff hxU (gen_mem hxU) _).1 (by
    rw [map_pow]; exact unitAt_pow ((unitAt_fnOf_iff hxU _ _).2 ht) n), g', hgV y hV, ?_⟩
  have := (regAt_fnOf hyU (gen_mem hxU) a).mul hu.inv.regAt
  rw [← e] at this
  convert this using 1
  have h0 := hu.ne_zero
  rw [map_pow] at h0
  rw [map_mul, map_pow, map_pow, mul_pow]
  field_simp

/- English proof (translation)
Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. Extract witnesses or component facts from the available result.

Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem exists_vanishesAt {U : X.Opens} (hU : IsAffineOpen U) {D : CartierDiv X} {x : X}
    (hxU : x ∈ U) {g : X.functionFieldˣ} (hg : D.IsEqn x g) {y : X} (hyU : y ∈ U)
    (hxy : x ∉ closure ({y} : Set X)) :
    ∃ s : Γ(X, U), x ∈ X.basicOpen s ∧
      D.VanishesAt y (fnOf U (gen_mem hxU) s * (g : X.functionField)⁻¹) := by
  obtain ⟨s, hs, hreg⟩ := exists_regularAt hU hxU hg hyU
  obtain ⟨t, htU, ht⟩ := hU.exists_basicOpen_le
    (V := ⟨(closure ({y} : Set X))ᶜ, isClosed_closure.isOpen_compl⟩) ⟨x, hxy⟩ hxU
  have hz : ZeroAt y (fnOf U (gen_mem hxU) t) := zeroAt_iff.2 ⟨regAt_fnOf hyU _ _,
    fun h => htU ((unitAt_fnOf_iff hyU _ _).1 h) (subset_closure rfl)⟩
  refine ⟨t * s, by rw [X.basicOpen_mul]; exact ⟨ht, hs⟩, ?_⟩
  obtain ⟨g', hg', hr⟩ := hreg
  refine ⟨g', hg', ?_⟩
  rw [map_mul, mul_assoc, mul_assoc, ← mul_assoc (fnOf U (gen_mem hxU) s)]
  exact hz.mul hr

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Reduce the argument to an intermediate assertion. Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations.

Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact.

Apply an available result and prove the equalities needed to match it to the conclusion. Rewrite the conclusion using the stated equalities. Expand and normalize the polynomial expressions, which then agree. Proceed by induction. Treat this case separately.

Treat this case separately. Extract witnesses or component facts from the available result. Consider separately whether the proposition holds or fails. Reduce the conclusion to the remaining proof obligations. Separate the alternatives or extract the components of the hypothesis.

Establish an intermediate fact. Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. Separate the alternatives or extract the components of the hypothesis. Rewrite the conclusion using the stated equalities.

A detailed English derivation is pending.
-/
theorem exists_generatesAt_vanishesAt : ∀ (X : Scheme.{0}) [IsIntegral X] (U : X.Opens), IsAffineOpen U →
    ∀ (D : CartierDiv X) (x : X), x ∈ U →
    ∀ (T : Finset X), (∀ y ∈ T, y ∈ U) → (∀ y ∈ T, y ≠ x → x ∉ closure ({y} : Set X)) →
    ∃ f : X.functionField, D.GeneratesAt x f ∧ ∀ y ∈ T, y ≠ x → D.VanishesAt y f := by
  intro X _ U hU D x hxU T hTU hT
  classical
  obtain ⟨g, hg⟩ := D.exists_isEqn x
  suffices ∃ s : Γ(X, U), x ∈ X.basicOpen s ∧ ∀ y ∈ T, y ≠ x →
      D.VanishesAt y (fnOf U (gen_mem hxU) s * (g : X.functionField)⁻¹) by
    obtain ⟨s, hs, h⟩ := this
    refine ⟨_, ⟨g, hg, ?_⟩, h⟩
    rw [mul_assoc, inv_mul_cancel₀ g.ne_zero, mul_one]
    exact (unitAt_fnOf_iff hxU _ _).2 hs
  have key (y : X) (hyU : y ∈ U) (s t : Γ(X, U))
      (h : D.VanishesAt y (fnOf U (gen_mem hxU) s * (g : X.functionField)⁻¹)) :
      D.VanishesAt y (fnOf U (gen_mem hxU) (s * t) * (g : X.functionField)⁻¹) := by
    obtain ⟨g', hg', hr⟩ := h
    refine ⟨g', hg', ?_⟩
    have := hr.mul (regAt_fnOf hyU (gen_mem hxU) t)
    convert this using 1
    rw [map_mul]; ring
  induction T using Finset.induction_on with
  | empty => exact ⟨1, by simpa using hxU, by simp⟩
  | insert y T _ ih =>
    obtain ⟨s, hs, h⟩ := ih (fun z hz => hTU z (Finset.mem_insert_of_mem hz))
      fun z hz => hT z (Finset.mem_insert_of_mem hz)
    by_cases hyx : y = x
    · refine ⟨s, hs, fun z hz hzx => ?_⟩
      rcases Finset.mem_insert.1 hz with rfl | hz
      · exact (hzx hyx).elim
      · exact h z hz hzx
    have hyU := hTU y (Finset.mem_insert_self _ _)
    obtain ⟨t, ht, h'⟩ := exists_vanishesAt hU hxU hg hyU (hT y (Finset.mem_insert_self _ _) hyx)
    refine ⟨s * t, by rw [X.basicOpen_mul]; exact ⟨hs, ht⟩, fun z hz hzx => ?_⟩
    rcases Finset.mem_insert.1 hz with rfl | hz
    · rw [mul_comm s]; exact key _ hyU _ _ h'
    · exact key _ (hTU z (Finset.mem_insert_of_mem hz)) _ _ (h z hz hzx)

end GlobalTheory.Cartier.CommonEqnOpen

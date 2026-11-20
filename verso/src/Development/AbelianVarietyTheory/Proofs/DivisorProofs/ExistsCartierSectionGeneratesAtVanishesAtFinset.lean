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
Proceed by induction on `n with`. Consider the case `zero => rw [pow_zero]`. Conclude with `unitAt_one x`. Consider the case `succ n ih => rw [pow_succ]`. Conclude with `ih.mul h`.
-/
theorem unitAt_pow {x : X} {f : X.functionField} (h : UnitAt x f) (n : ℕ) : UnitAt x (f ^ n) := by
  induction n with
  | zero => rw [pow_zero]; exact unitAt_one x
  | succ n ih => rw [pow_succ]; exact ih.mul h

/- English proof (translation)
Take `⟨b, rfl⟩` from `exists_fnOf_eq ht h`. Use `hU.isLocalization_basicOpen t` as an intermediate fact. Take `⟨n, a, e⟩` from `IsLocalization.Away.surj t b`. Use `⟨n, a, ?_⟩` and prove the remaining obligations. Establish `e'` using `congrArg (fnOf _ ht) e`.

Rewrite `e'` using `[map_mul, map_pow]`. Establish `k (c : Γ(X, U)) : fnOf _ ht (algebraMap Γ(X, U) Γ(X, X.basicOpen t) c) = fnOf U hg c` using `fnOf_resG (X.basicOpen_le t) ht c`. Rewrite `e'` using `[k, k]`. Rewrite using `[← e', mul_comm]`.
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
Take `⟨W, hW, hgW⟩` from `hg.exists_nhds`. Take `⟨V, hV, g', hgV⟩` from `D.exists_isEqn_nhds y`. Take `⟨t, htW, ht⟩` from `hU.exists_basicOpen_le ⟨x, hW⟩ hxU`. Take `⟨t', htV, ht'⟩` from `hU.exists_basicOpen_le ⟨y, hV⟩ hyU`. Establish `hgen : genericPoint X ∈ X.basicOpen (t * t')`.

Rewrite using `[X.basicOpen_mul]`. Conclude with `⟨gen_mem ht, gen_mem ht'⟩`. Take `⟨n, a, e⟩` from `exists_pow_mul_eq hU (gen_mem hxU) (t * t') hgen (f := (g' : X.functionField) / g) fun z hz => by`. Rewrite `hz` using `[X.basicOpen_mul]`. Conclude with `((hgW z (htW hz.1)).iff_unitAt.1 (hgV z (htV hz.2))).regAt`.

Establish `hu : UnitAt y (fnOf U (gen_mem hxU) (t' ^ n))`. Rewrite using `[map_pow]`. Conclude with `unitAt_pow ((unitAt_fnOf_iff hyU _ _).2 ht') n`. Use `⟨t ^ n, (unitAt_fnOf_iff hxU (gen_mem hxU) _).1 (by` and prove the remaining obligations. Rewrite using `[map_pow]`.

Conclude with `unitAt_pow ((unitAt_fnOf_iff hxU _ _).2 ht) n), g', hgV y hV, ?_⟩`. Use `(regAt_fnOf hyU (gen_mem hxU) a).mul hu.inv.regAt` as an intermediate fact. Rewrite `this` using `[← e]`. Use `this using 1` and compare the differences between its conclusion and the goal. Establish `h0` using `hu.ne_zero`.

Rewrite `h0` using `[map_pow]`. Rewrite using `[map_mul, map_pow, map_pow, mul_pow]`. Clear the denominators using the available nonvanishing facts.
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
Take `⟨s, hs, hreg⟩` from `exists_regularAt hU hxU hg hyU`. Take `⟨t, htU, ht⟩` from `hU.exists_basicOpen_le (V := ⟨(closure ({y} : Set X))ᶜ, isClosed_closure.isOpen_compl⟩) ⟨x, hxy⟩ hxU`. Establish `hz : ZeroAt y (fnOf U (gen_mem hxU) t)` using `zeroAt_iff.2 ⟨regAt_fnOf hyU _ _, fun h => htU ((unitAt_fnOf_iff hyU _ _).1 h) (subset_closure rfl)⟩`. Use `⟨t * s, by rw [X.basicOpen_mul]; exact ⟨ht, hs⟩, ?_⟩` and prove the remaining obligations. Take `⟨g', hg', hr⟩` from `hreg`.

Use `⟨g', hg', ?_⟩` and prove the remaining obligations. Rewrite using `[map_mul, mul_assoc, mul_assoc, ← mul_assoc (fnOf U (gen_mem hxU) s)]`. Conclude with `hz.mul hr`.
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
Introduce `X _ U hU D x hxU T hTU hT`. Take `⟨g, hg⟩` from `D.exists_isEqn x`. It suffices to establish `∃ s : Γ(X, U), x ∈ X.basicOpen s ∧ ∀ y ∈ T, y ≠ x → D.VanishesAt y (fnOf U (gen_mem hxU) s * (g : X.functionField)⁻¹) by`. Take `⟨s, hs, h⟩` from `this`. Use `⟨_, ⟨g, hg, ?_⟩, h⟩` and prove the remaining obligations.

Rewrite using `[mul_assoc, inv_mul_cancel₀ g.ne_zero, mul_one]`. Conclude with `(unitAt_fnOf_iff hxU _ _).2 hs`. Establish `key (y : X) (hyU : y ∈ U) (s t : Γ(X, U)) (h : D.VanishesAt y (fnOf U (gen_mem hxU) s * (g : X.functionField)⁻¹)) : D.VanishesAt y (fnOf U (gen_mem hxU) (s * t) * (g : X.functionField)⁻¹)`. Take `⟨g', hg', hr⟩` from `h`. Use `⟨g', hg', ?_⟩` and prove the remaining obligations.

Use `hr.mul (regAt_fnOf hyU (gen_mem hxU) t)` as an intermediate fact. Use `this using 1` and compare the differences between its conclusion and the goal. Rewrite using `[map_mul]`. Expand and normalize the polynomial expressions, which then agree. Proceed by induction on `T using Finset.induction_on with`.

Consider the case `empty => exact ⟨1, by simpa using hxU, by simp⟩`. Consider the case `insert y T _ ih`. Take `⟨s, hs, h⟩` from `ih (fun z hz => hTU z (Finset.mem_insert_of_mem hz)) fun z hz => hT z (Finset.mem_insert_of_mem hz)`. Distinguish the cases in `hyx : y = x`. Use `⟨s, hs, fun z hz hzx => ?_⟩` and prove the remaining obligations.

Break down `Finset.mem_insert.1 hz with rfl | hz` into its components or cases. Conclude with `(hzx hyx).elim`. Conclude with `h z hz hzx`. Establish `hyU` using `hTU y (Finset.mem_insert_self _ _)`. Take `⟨t, ht, h'⟩` from `exists_vanishesAt hU hxU hg hyU (hT y (Finset.mem_insert_self _ _) hyx)`.

Use `⟨s * t, by rw [X.basicOpen_mul]; exact ⟨hs, ht⟩, fun z hz hzx => ?_⟩` and prove the remaining obligations. Break down `Finset.mem_insert.1 hz with rfl | hz` into its components or cases. Rewrite using `[mul_comm s]`. Conclude with `key _ hyU _ _ h'`. Conclude with `key _ (hTU z (Finset.mem_insert_of_mem hz)) _ _ (h z hz hzx)`.
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

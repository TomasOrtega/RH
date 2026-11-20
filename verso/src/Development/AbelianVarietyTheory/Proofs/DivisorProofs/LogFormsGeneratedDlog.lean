import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsLifted
import Development.AbelianVarietyTheory.Definitions.Divisors.IsEtCoord

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace GlobalTheory GlobalTheory.DI GlobalTheory.LogDR GlobalTheory.LogPair GlobalTheory.Cartier ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.DI

set_option autoImplicit false in
open CategoryTheory AlgebraicGeometry TopologicalSpace in
/- English proof (translation)
Unfold `_root_.GlobalTheory.DI.forms`. Use `AddSubgroup.subset_closure ⟨b, hb, fun _ => _root_.GlobalTheory.LogDR.dlog g, fun _ => ⟨g, hg, rfl⟩, ?_⟩` and prove the remaining obligations. Rewrite using `[map_smul, ExteriorAlgebra.ιMulti_apply]`. Simplify using the standard rewrite rules.
-/
private lemma smul_dlog_mem_forms {X : Scheme.{0}} [IsIntegral X] (Z : Set X) (y : X)
    (g : X.functionFieldˣ) (hg : _root_.GlobalTheory.LogDR.LogUnit Z y g) (b : X.functionField)
    (hb : b ∈ _root_.GlobalTheory.LogDR.locRing y) :
    ExteriorAlgebra.ι X.functionField (b • _root_.GlobalTheory.LogDR.dlog g) ∈
      _root_.GlobalTheory.DI.forms (_root_.GlobalTheory.LogDR.locRing y : Set X.functionField)
        (_root_.GlobalTheory.LogDR.dlog '' {g | _root_.GlobalTheory.LogDR.LogUnit Z y g}) 1 := by
  unfold _root_.GlobalTheory.DI.forms
  refine AddSubgroup.subset_closure ⟨b, hb, fun _ => _root_.GlobalTheory.LogDR.dlog g,
    fun _ => ⟨g, hg, rfl⟩, ?_⟩
  rw [map_smul, ExteriorAlgebra.ιMulti_apply]
  simp

set_option autoImplicit false in
open CategoryTheory AlgebraicGeometry TopologicalSpace in
/- English proof (translation)
Introduce `z hz _`. Use `⟨X.presheaf.stalkSpecializes hz a, ha.map (X.presheaf.stalkSpecializes hz).hom, ?_⟩` and prove the remaining obligations. Rewrite using `[← hg]`. Express the relevant statement in the definitionally equal form `(X.presheaf.stalkSpecializes _) ((X.presheaf.stalkSpecializes hz) a) = (X.presheaf.stalkSpecializes _) a`. Rewrite using `[← CategoryTheory.comp_apply, TopCat.Presheaf.stalkSpecializes_comp]`.
-/
private lemma logUnit_of_isUnit_stalk {X : Scheme.{0}} [IsIntegral X] (Z : Set X)
    (y : X) (g : X.functionFieldˣ) (a : X.presheaf.stalk y) (ha : IsUnit a)
    (hg : algebraMap (X.presheaf.stalk y) X.functionField a = g) :
    _root_.GlobalTheory.LogDR.LogUnit Z y g := by
  intro z hz _
  refine ⟨X.presheaf.stalkSpecializes hz a, ha.map (X.presheaf.stalkSpecializes hz).hom, ?_⟩
  rw [← hg]
  change (X.presheaf.stalkSpecializes _) ((X.presheaf.stalkSpecializes hz) a) =
    (X.presheaf.stalkSpecializes _) a
  rw [← CategoryTheory.comp_apply, TopCat.Presheaf.stalkSpecializes_comp]

set_option autoImplicit false in
open CategoryTheory AlgebraicGeometry TopologicalSpace in

/- English proof (translation)
Introduce `X _ Z y`. Use `⟨fun w hw => ?_, fun g hg => ?_⟩` and prove the remaining obligations. Take `⟨a, rfl⟩` from `_root_.GlobalTheory.LogDR.mem_locRing.mp hw`. Break down `IsLocalRing.isUnit_or_isUnit_one_sub_self a with ha | ha` into its components or cases. Use `set U := (ha.map (algebraMap (X.presheaf.stalk y) X.functionField)).unit with hU`.

Establish `hUv : (U : X.functionField) = algebraMap (X.presheaf.stalk y) X.functionField a` using `rfl`. Establish `key` using `smul_dlog_mem_forms Z y U (logUnit_of_isUnit_stalk Z y U a ha hUv.symm) _ hw`. Use `key using 2` and compare the differences between its conclusion and the goal. Unfold `_root_.GlobalTheory.LogDR.dlog _root_.GlobalTheory.LogDR.dK`. Rewrite using `[smul_smul, ← hUv, Units.mul_inv, one_smul]`.

Use `set U := (ha.map (algebraMap (X.presheaf.stalk y) X.functionField)).unit with hU`. Establish `hUv : (U : X.functionField) = algebraMap (X.presheaf.stalk y) X.functionField (1 - a)` using `rfl`. Establish `hmem : -(U : X.functionField) ∈ _root_.GlobalTheory.LogDR.locRing y` using `neg_mem (_root_.GlobalTheory.LogDR.mem_locRing.mpr ⟨1 - a, hUv.symm⟩)`. Establish `key` using `smul_dlog_mem_forms Z y U (logUnit_of_isUnit_stalk Z y U (1 - a) ha hUv.symm) _ hmem`. Use `key using 2` and compare the differences between its conclusion and the goal.

Unfold `_root_.GlobalTheory.LogDR.dlog _root_.GlobalTheory.LogDR.dK`. Rewrite using `[smul_smul, neg_mul, Units.mul_inv, neg_smul, one_smul, hUv, map_sub, map_one, map_sub, Derivation.map_one_eq_zero, zero_sub, neg_neg]`. Simplify using `using smul_dlog_mem_forms Z y g hg 1 (one_mem _)`.
-/
theorem _root_.GlobalTheory.DI.dK_dlog_mem_forms_one : ∀ {X : Scheme.{0}} [IsIntegral X]
    (Z : Set X) (y : X), (∀ w ∈ _root_.GlobalTheory.LogDR.locRing y,
      ExteriorAlgebra.ι X.functionField (_root_.GlobalTheory.LogDR.dK w) ∈
        _root_.GlobalTheory.DI.forms (_root_.GlobalTheory.LogDR.locRing y : Set X.functionField)
          (_root_.GlobalTheory.LogDR.dlog '' {g | _root_.GlobalTheory.LogDR.LogUnit Z y g}) 1) ∧
      ∀ g, _root_.GlobalTheory.LogDR.LogUnit Z y g → ExteriorAlgebra.ι X.functionField (_root_.GlobalTheory.LogDR.dlog g) ∈
        _root_.GlobalTheory.DI.forms (_root_.GlobalTheory.LogDR.locRing y : Set X.functionField)
          (_root_.GlobalTheory.LogDR.dlog '' {g | _root_.GlobalTheory.LogDR.LogUnit Z y g}) 1 := by
  intro X _ Z y
  refine ⟨fun w hw => ?_, fun g hg => ?_⟩
  · obtain ⟨a, rfl⟩ := _root_.GlobalTheory.LogDR.mem_locRing.mp hw
    rcases IsLocalRing.isUnit_or_isUnit_one_sub_self a with ha | ha
    · set U := (ha.map (algebraMap (X.presheaf.stalk y) X.functionField)).unit with hU
      have hUv : (U : X.functionField) = algebraMap (X.presheaf.stalk y) X.functionField a := rfl
      have key := smul_dlog_mem_forms Z y U
        (logUnit_of_isUnit_stalk Z y U a ha hUv.symm) _ hw
      convert key using 2
      unfold _root_.GlobalTheory.LogDR.dlog _root_.GlobalTheory.LogDR.dK
      rw [smul_smul, ← hUv, Units.mul_inv, one_smul]
    · set U := (ha.map (algebraMap (X.presheaf.stalk y) X.functionField)).unit with hU
      have hUv : (U : X.functionField) =
          algebraMap (X.presheaf.stalk y) X.functionField (1 - a) := rfl
      have hmem : -(U : X.functionField) ∈ _root_.GlobalTheory.LogDR.locRing y :=
        neg_mem (_root_.GlobalTheory.LogDR.mem_locRing.mpr ⟨1 - a, hUv.symm⟩)
      have key := smul_dlog_mem_forms Z y U
        (logUnit_of_isUnit_stalk Z y U (1 - a) ha hUv.symm) _ hmem
      convert key using 2
      unfold _root_.GlobalTheory.LogDR.dlog _root_.GlobalTheory.LogDR.dK
      rw [smul_smul, neg_mul, Units.mul_inv, neg_smul, one_smul, hUv, map_sub, map_one,
        map_sub, Derivation.map_one_eq_zero, zero_sub, neg_neg]
  · simpa using smul_dlog_mem_forms Z y g hg 1 (one_mem _)

end GlobalTheory.DI

import Mathlib
import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.StatementsFibreFinite
import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.StatementsDegZeroLocalRing
import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.StatementsFiniteAlgebraLengthSum
import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.StatementsSemilocalMaxIdeals
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.FieldNumbers

open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR

noncomputable section

universe u

set_option synthInstance.maxHeartbeats 400000 in

/- English proof (translation)
Introduce `F _ K K' _ _ _ _ j ι' _ P' hP' n hP'n hPn c a h ha hh haP W hW hWn hPW hhW d hd α hα β hβ`. Use `hP'.isPrime` as an intermediate fact. Establish `hfin` using `h1 F K K' j ι' P' hP' n hP'n hPn W hW hWn hPW`. Use `⟨hfin, ?_⟩` and prove the remaining obligations. Use `(h2 F K K' j ι' P' hP' n hP'n hPn W hW hWn hPW).1` as an intermediate fact.

Use `(h3 F K (fun k => ι' (j k)) (contractPrime j P') (isMultiProjPrime_contractPrime j ι' hP') W hW hPW).1.2` as an intermediate fact. Take `⟨𝔪, h𝔪, hinj, hcov, hloc⟩` from `h5 F K K' j ι' P' hP' n hP'n hPn W hW hWn hPW`. Set `: Fintype (fibrePrimes j P' W)` to `hfin.fintype`. Set `alg : ∀ W' : fibrePrimes j P' W, Algebra (degZeroLoc P' (fibrePrimes j P' W)) (degZeroLoc P' {W'.1})` to `fun W' => degZeroLoc.algebraOfSubset P' (Set.singleton_subset_iff.mpr W'.2)`. Rewrite using `[h4 _ _ _ 𝔪 h𝔪 hinj hcov (fun W' => degZeroLoc P' {W'.1}) (fun W' => (hloc W').1) α, Finset.sum_filter, Finset.sum_subtype hfin.toFinset (fun _ => Set.Finite.mem_toFinset hfin)]`.

Use `Finset.sum_congr rfl fun W' _ => ?_` and prove the remaining obligations. Take `⟨hW'p, -, hW'c⟩` from `W'.2`. Use `hW'p.isPrime` as an intermediate fact. Establish `hb : algebraMap _ (degZeroLoc P' {W'.1}) (algebraMap (degZeroLoc (contractPrime j P') {W}) (degZeroLoc P' (fibrePrimes j P' W)) α) = β W'.1` using `Subtype.ext (hβ W'.1 W'.2).symm`. Rewrite using `[hb, (hloc W').2, ← hd W'.1 hW'p hW'c]`.

Use `split_ifs with haW'`. Both sides reduce to the same expression. Rewrite using `[Ring.ord_of_isUnit, zero_mul]`. Establish `hne : ∀ g, g ∉ contractPrime j P' → algebraMap (MRing ι' F ⧸ P') (FractionRing (MRing ι' F ⧸ P')) (Ideal.Quotient.mk P' (rename (blockIncl j ι') g)) ≠ 0` using `fun g hg => by`. Rewrite using `[Ne, IsFractionRing.to_map_eq_zero_iff, Ideal.Quotient.eq_zero_iff_mem]`.

Conclude with `hg`. Establish `hhP : h ∉ contractPrime j P'` using `fun hm => hhW (hPW hm)`. Use `IsUnit.of_mul_eq_one ⟨_, div_mem_degZeroLoc P' {W'.1} (isMultiHomog_rename j ι' hh) (isMultiHomog_rename j ι' ha) haP (fun W'' hW'' => (Set.mem_singleton_iff.mp hW'') ▸ haW')⟩ ?_` and prove the remaining obligations. Apply `Subtype.ext` to reduce the goal to its premises. Express the relevant statement in the definitionally equal form `(β W'.1 : FractionRing (MRing ι' F ⧸ P')) * _ = 1`.

Rewrite using `[hβ W'.1 W'.2, hα, map_div₀, contractFracMap_algebraMap, contractFracMap_algebraMap]`. Use `hne h hhP` as an intermediate fact. Use `hne a haP` as an intermediate fact. Clear the denominators using the available nonvanishing facts.
-/
theorem SemilocalLengthSum.proof (h1 : FibreFinite.Statement.{u})
    (h2 : SemilocalFiniteRank.Statement.{u}) (h3 : DegZeroLocalRing.Statement.{u})
    (h4 : FiniteAlgebraLengthSum.Statement.{u}) (h5 : SemilocalMaxIdeals.Statement.{u}) :
    SemilocalLengthSum.Statement.{u} := by
  intro F _ K K' _ _ _ _ j ι' _ P' hP' n hP'n hPn c a h ha hh haP W hW hWn hPW hhW d hd α hα β hβ
  have := hP'.isPrime
  have hfin := h1 F K K' j ι' P' hP' n hP'n hPn W hW hWn hPW
  refine ⟨hfin, ?_⟩
  have := (h2 F K K' j ι' P' hP' n hP'n hPn W hW hWn hPW).1
  have := (h3 F K (fun k => ι' (j k)) (contractPrime j P') (isMultiProjPrime_contractPrime j ι' hP')
    W hW hPW).1.2
  obtain ⟨𝔪, h𝔪, hinj, hcov, hloc⟩ := h5 F K K' j ι' P' hP' n hP'n hPn W hW hWn hPW
  let : Fintype (fibrePrimes j P' W) := hfin.fintype
  let alg : ∀ W' : fibrePrimes j P' W,
      Algebra (degZeroLoc P' (fibrePrimes j P' W)) (degZeroLoc P' {W'.1}) :=
    fun W' => degZeroLoc.algebraOfSubset P' (Set.singleton_subset_iff.mpr W'.2)
  rw [h4 _ _ _ 𝔪 h𝔪 hinj hcov (fun W' => degZeroLoc P' {W'.1}) (fun W' => (hloc W').1) α,
    Finset.sum_filter, Finset.sum_subtype hfin.toFinset (fun _ => Set.Finite.mem_toFinset hfin)]
  refine Finset.sum_congr rfl fun W' _ => ?_
  obtain ⟨hW'p, -, hW'c⟩ := W'.2
  have := hW'p.isPrime
  have hb : algebraMap _ (degZeroLoc P' {W'.1}) (algebraMap (degZeroLoc (contractPrime j P') {W})
      (degZeroLoc P' (fibrePrimes j P' W)) α) = β W'.1 :=
    Subtype.ext (hβ W'.1 W'.2).symm
  rw [hb, (hloc W').2, ← hd W'.1 hW'p hW'c]
  split_ifs with haW'
  · rfl
  rw [Ring.ord_of_isUnit, zero_mul]
  have hne : ∀ g, g ∉ contractPrime j P' → algebraMap (MRing ι' F ⧸ P')
      (FractionRing (MRing ι' F ⧸ P')) (Ideal.Quotient.mk P' (rename (blockIncl j ι') g)) ≠ 0 :=
    fun g hg => by
      rw [Ne, IsFractionRing.to_map_eq_zero_iff, Ideal.Quotient.eq_zero_iff_mem]
      exact hg
  have hhP : h ∉ contractPrime j P' := fun hm => hhW (hPW hm)
  refine IsUnit.of_mul_eq_one ⟨_, div_mem_degZeroLoc P' {W'.1} (isMultiHomog_rename j ι' hh)
    (isMultiHomog_rename j ι' ha) haP (fun W'' hW'' => (Set.mem_singleton_iff.mp hW'') ▸ haW')⟩ ?_
  apply Subtype.ext
  change (β W'.1 : FractionRing (MRing ι' F ⧸ P')) * _ = 1
  rw [hβ W'.1 W'.2, hα, map_div₀, contractFracMap_algebraMap, contractFracMap_algebraMap]
  have := hne h hhP
  have := hne a haP
  field_simp

end

end GroundTheory.Heights₂.Heights.FieldNumbers

import Mathlib
import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.StatementsSemilocalIntegral
import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.StatementsValuativeCentre
import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.PContractRelDimLe
import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.PPFContracted
import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.PPFContractedDim
import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.PExistsForm
import GroundTheory.HeightsAndTheta.Heights.Intersections.TableDegreeThreeBase
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.FieldNumbers

open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR

noncomputable section

universe u

namespace SemilocalIntegral

section Dim

variable {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)]
  {F : Type u} [Field F]

omit [DecidableEq K] in

/- English proof (translation)
Establish `h1 : (0 : WithBot ℕ∞) ≤ ringKrullDim (MRing ι F ⧸ Q)` using `ringKrullDim_nonneg_of_nontrivial`. Establish `h2` using `PFContracted.ringKrullDim_lt_top (F := F) Q`. Consider the cases of `h : ringKrullDim (MRing ι F ⧸ Q) with`. Consider the case `bot`. Rewrite `h1` using `[h]`.

Conclude with `absurd h1 (by simp)`. Consider the case `coe e`. Proceed by induction on `e using ENat.recTopCoe with`. Consider the case `top`. Rewrite `h2` using `[h]`.

Conclude with `absurd h2 (by simp)`. Consider the case `coe D => exact ⟨D, rfl⟩`.
-/
theorem exists_ringKrullDim_eq_nat (Q : Ideal (MRing ι F)) [Q.IsPrime] :
    ∃ D : ℕ, ringKrullDim (MRing ι F ⧸ Q) = D := by
  have h1 : (0 : WithBot ℕ∞) ≤ ringKrullDim (MRing ι F ⧸ Q) := ringKrullDim_nonneg_of_nontrivial
  have h2 := PFContracted.ringKrullDim_lt_top (F := F) Q
  cases h : ringKrullDim (MRing ι F ⧸ Q) with
  | bot =>
    rw [h] at h1
    exact absurd h1 (by simp)
  | coe e =>
    induction e using ENat.recTopCoe with
    | top =>
      rw [h] at h2
      exact absurd h2 (by simp)
    | coe D => exact ⟨D, rfl⟩

/- English proof (translation)
Take `⟨D, hD⟩` from `exists_ringKrullDim_eq_nat Q`. Conclude with `⟨_, PFContracted.relDim_eq_int hD⟩`.
-/
theorem exists_relDim_eq_int (Q : Ideal (MRing ι F)) [Q.IsPrime] :
    ∃ d : ℤ, relDim Q = ((d : WithTop ℤ) : WithBot (WithTop ℤ)) := by
  obtain ⟨D, hD⟩ := exists_ringKrullDim_eq_nat Q
  exact ⟨_, PFContracted.relDim_eq_int hD⟩

/- English proof (translation)
Take `⟨x, hx, hxQ⟩` from `SetLike.exists_of_lt h`. Establish `hle` using `Inter.krullDim_quot_add_one_le h.le hx hxQ`. Take `⟨D, hD⟩` from `exists_ringKrullDim_eq_nat Q`. Take `⟨D₂, hD₂⟩` from `exists_ringKrullDim_eq_nat Q₂`. Rewrite `hle` using `[hD, hD₂]`.

Establish `: D₂ + 1 ≤ D` using `by exact_mod_cast hle`. Rewrite using `[PFContracted.relDim_eq_int hD, PFContracted.relDim_eq_int hD₂]`. Conclude with `WithBot.coe_lt_coe.mpr (WithTop.coe_lt_coe.mpr (by omega))`.
-/
theorem relDim_lt_of_lt {Q Q₂ : Ideal (MRing ι F)} [Q.IsPrime] [Q₂.IsPrime] (h : Q < Q₂) :
    relDim Q₂ < relDim Q := by
  obtain ⟨x, hx, hxQ⟩ := SetLike.exists_of_lt h
  have hle := Inter.krullDim_quot_add_one_le h.le hx hxQ
  obtain ⟨D, hD⟩ := exists_ringKrullDim_eq_nat Q
  obtain ⟨D₂, hD₂⟩ := exists_ringKrullDim_eq_nat Q₂
  rw [hD, hD₂] at hle
  have : D₂ + 1 ≤ D := by exact_mod_cast hle
  rw [PFContracted.relDim_eq_int hD, PFContracted.relDim_eq_int hD₂]
  exact WithBot.coe_lt_coe.mpr (WithTop.coe_lt_coe.mpr (by omega))

end Dim

section Centre

variable {F : Type u} [Field F] {K K' : Type} [Fintype K] [DecidableEq K] [Fintype K']
  [DecidableEq K'] {j : K ↪ K'} {ι' : K' → Type} [∀ k, Fintype (ι' k)]

omit [Fintype K'] [∀ k, Fintype (ι' k)] in

/- English proof (translation)
Establish `hy₀` using `isMultiProjPrime_contractPrime j ι' hy`. Introduce `a ha`. Rewrite using `[← sum_weightedHomogeneousComponent (blockWeight _) a]`. Use `finsum_induction (· ∈ W) W.zero_mem (fun _ _ => W.add_mem) (fun c => ?_)` and prove the remaining obligations. Establish `hac` using `hy₀.multiHomog a ha c`.

Establish `hf : IsMultiHomog (weightedHomogeneousComponent (blockWeight _) c a) c` using `weightedHomogeneousComponent_isWeightedHomogeneous _ _`. Assume the negation of the conclusion as `hfW`. Use `choose i hi using hy₀.relevant`. Establish `hu` using `isMultiHomog_prod_pow (R := F) i c`. Establish `huy` using `(haveI := hy₀.isPrime; prod_pow_not_mem _ i hi c)`.

Establish `hmem` using `hR _ (div_mem_degZeroLoc _ {W} hu hf (fun h => hfW (hPW h)) (fun W' hW' => (Set.mem_singleton_iff.mp hW') ▸ hfW))`. Rewrite `hmem` using `[map_div₀, contractFracMap_algebraMap, contractFracMap_algebraMap]`. Establish `h2` using `((hcen _ _ _ (isMultiHomog_rename j ι' hf) (isMultiHomog_rename j ι' hu) huy).2).mp hac`. Establish `hne : ∀ g, g ∉ P' → algebraMap (MRing ι' F ⧸ P') (FractionRing (MRing ι' F ⧸ P')) (Ideal.Quotient.mk P' g) ≠ 0` using `fun g hg => by`. Rewrite using `[Ne, IsFractionRing.to_map_eq_zero_iff, Ideal.Quotient.eq_zero_iff_mem]` and apply the resulting hypothesis.

Establish `ha0` using `hne _ (fun h => hfW (hPW h))`. Establish `hu0` using `hne _ (fun h => huy (hP'y h))`. Rewrite `h2` using `[ValuationSubring.mem_nonunits_iff]`. Establish `h3` using `(R.valuation_le_one_iff _).mpr hmem`. Establish `h4` using `mul_lt_one_of_lt_of_le h2 h3`.

Rewrite `h4` using `[← map_mul, div_mul_div_cancel₀ hu0, div_self ha0, map_one]`. Conclude with `lt_irrefl _ h4`.
-/
theorem contract_le {P' : Ideal (MRing ι' F)} [P'.IsPrime] {W : Ideal (MRing (fun k => ι' (j k)) F)}
    (hPW : contractPrime j P' ≤ W) (R : ValuationSubring (FractionRing (MRing ι' F ⧸ P')))
    (hR : ∀ a ∈ degZeroLoc (contractPrime j P') {W}, contractFracMap j P' a ∈ R)
    {y : Ideal (MRing ι' F)} (hy : IsMultiProjPrime y) (hP'y : P' ≤ y)
    (hcen : ∀ (b : K' → ℕ) (f g : MRing ι' F), IsMultiHomog f b → IsMultiHomog g b → g ∉ y →
      algebraMap (MRing ι' F ⧸ P') (FractionRing (MRing ι' F ⧸ P')) (Ideal.Quotient.mk P' f) /
          algebraMap (MRing ι' F ⧸ P') _ (Ideal.Quotient.mk P' g) ∈ R ∧
        (f ∈ y ↔ algebraMap (MRing ι' F ⧸ P') (FractionRing (MRing ι' F ⧸ P'))
            (Ideal.Quotient.mk P' f) / algebraMap (MRing ι' F ⧸ P') _ (Ideal.Quotient.mk P' g) ∈
          R.nonunits)) :
    contractPrime j y ≤ W := by
  have hy₀ := isMultiProjPrime_contractPrime j ι' hy
  intro a ha
  rw [← sum_weightedHomogeneousComponent (blockWeight _) a]
  refine finsum_induction (· ∈ W) W.zero_mem (fun _ _ => W.add_mem) (fun c => ?_)
  have hac := hy₀.multiHomog a ha c
  have hf : IsMultiHomog (weightedHomogeneousComponent (blockWeight _) c a) c :=
    weightedHomogeneousComponent_isWeightedHomogeneous _ _
  by_contra hfW
  choose i hi using hy₀.relevant
  have hu := isMultiHomog_prod_pow (R := F) i c
  have huy := (haveI := hy₀.isPrime; prod_pow_not_mem _ i hi c)
  have hmem := hR _ (div_mem_degZeroLoc _ {W} hu hf (fun h => hfW (hPW h))
    (fun W' hW' => (Set.mem_singleton_iff.mp hW') ▸ hfW))
  rw [map_div₀, contractFracMap_algebraMap, contractFracMap_algebraMap] at hmem
  have h2 := ((hcen _ _ _ (isMultiHomog_rename j ι' hf) (isMultiHomog_rename j ι' hu) huy).2).mp hac
  have hne : ∀ g, g ∉ P' → algebraMap (MRing ι' F ⧸ P') (FractionRing (MRing ι' F ⧸ P'))
      (Ideal.Quotient.mk P' g) ≠ 0 := fun g hg => by
    rwa [Ne, IsFractionRing.to_map_eq_zero_iff, Ideal.Quotient.eq_zero_iff_mem]
  have ha0 := hne _ (fun h => hfW (hPW h))
  have hu0 := hne _ (fun h => huy (hP'y h))
  rw [ValuationSubring.mem_nonunits_iff] at h2
  have h3 := (R.valuation_le_one_iff _).mpr hmem
  have h4 := mul_lt_one_of_lt_of_le h2 h3
  rw [← map_mul, div_mul_div_cancel₀ hu0, div_self ha0, map_one] at h4
  exact lt_irrefl _ h4

/- English proof (translation)
Establish `hF : ∀ c : F, algebraMap F (FractionRing (MRing ι' F ⧸ P')) c ∈ R` using `fun c => by`. Rewrite using `[← (contractFracMap j P').commutes c]`. Conclude with `hR _ (Subalgebra.algebraMap_mem _ c)`. Take `⟨y, hy, hP'y, hcen⟩` from `hC F K' ι' P' hP' R hF`. Establish `hle` using `contract_le hPW R hR hy hP'y hcen`.

Use `hy.isPrime` as an intermediate fact. Use `hW.isPrime` as an intermediate fact. Establish `hcases : contractPrime j y = contractPrime j P' ∨ contractPrime j y = W`. Assume the negation of the conclusion as `hne`. Use `push Not at hne`.

Establish `d1 : relDim (contractPrime j y) < relDim (contractPrime j P')` using `relDim_lt_of_lt (lt_of_le_of_ne (Ideal.comap_mono hP'y) hne.1.symm)`. Establish `d2 : relDim W < relDim (contractPrime j y)` using `relDim_lt_of_lt (lt_of_le_of_ne hle hne.2)`. Take `⟨d, hd⟩` from `exists_relDim_eq_int (contractPrime j y)`. Rewrite `d1` using `[hd, hPn, PFContracted.natCast_withBot_withTop]`. Rewrite `d2` using `[hd, hWn, PFContracted.natCast_withBot_withTop]`.

Establish `e1` using `WithTop.coe_lt_coe.mp (WithBot.coe_lt_coe.mp d1)`. Establish `e2` using `WithTop.coe_lt_coe.mp (WithBot.coe_lt_coe.mp d2)`. Move the coercions through the operations in `at e1`. Use linear arithmetic over natural numbers and integers. Establish `havoid : ∀ g, g ∉ P' → (∀ W' ∈ fibrePrimes j P' W, g ∉ W') → g ∉ y`.

Break down `hcases with h | h` into its components or cases. Establish `hyP' : y = P'`. Assume the negation of the conclusion as `hne`. Establish `d1` using `relDim_lt_of_lt (lt_of_le_of_ne hP'y (Ne.symm hne))`. Establish `d2` using `ContractRelDimLe.proof F K K' j ι' y hy`.

Rewrite `d2` using `[h, hPn, ← hP'n]`. Conclude with `lt_irrefl _ (lt_of_lt_of_le d1 d2)`. Conclude with `fun g hg _ => hyP' ▸ hg`. Conclude with `fun g _ hgW => hgW y ⟨hy, hP'y, h⟩`. Introduce `x hx`.

Unfold `degZeroLoc at hx`. Proceed by induction on `hx using Algebra.adjoin_induction with`. Consider the case `mem x hx`. Take `⟨b, f, g, hf, hg, hgP, hgW, rfl⟩` from `hx`. Conclude with `(hcen b f g hf hg (havoid g hgP hgW)).1`.

Consider the case `algebraMap c => exact hF c`. Consider the case `add a a' _ _ ha ha' => exact R.add_mem _ _ ha ha'`. Consider the case `mul a a' _ _ ha ha' => exact R.mul_mem _ _ ha ha'`.
-/
theorem semilocal_le (hC : ValuativeCentre.Statement.{u}) {P' : Ideal (MRing ι' F)} [P'.IsPrime]
    (hP' : IsMultiProjPrime P') {n : ℕ} (hP'n : relDim P' = (n + 1 : ℕ))
    (hPn : relDim (contractPrime j P') = (n + 1 : ℕ)) {W : Ideal (MRing (fun k => ι' (j k)) F)}
    (hW : IsMultiProjPrime W) (hWn : relDim W = (n : ℕ)) (hPW : contractPrime j P' ≤ W)
    (R : ValuationSubring (FractionRing (MRing ι' F ⧸ P')))
    (hR : ∀ a ∈ degZeroLoc (contractPrime j P') {W}, contractFracMap j P' a ∈ R) :
    ∀ x ∈ degZeroLoc P' (fibrePrimes j P' W), x ∈ R := by
  have hF : ∀ c : F, algebraMap F (FractionRing (MRing ι' F ⧸ P')) c ∈ R := fun c => by
    rw [← (contractFracMap j P').commutes c]
    exact hR _ (Subalgebra.algebraMap_mem _ c)
  obtain ⟨y, hy, hP'y, hcen⟩ := hC F K' ι' P' hP' R hF
  have hle := contract_le hPW R hR hy hP'y hcen
  have := hy.isPrime
  have := hW.isPrime
  have hcases : contractPrime j y = contractPrime j P' ∨ contractPrime j y = W := by
    by_contra hne
    push Not at hne
    have d1 : relDim (contractPrime j y) < relDim (contractPrime j P') :=
      relDim_lt_of_lt (lt_of_le_of_ne (Ideal.comap_mono hP'y) hne.1.symm)
    have d2 : relDim W < relDim (contractPrime j y) := relDim_lt_of_lt (lt_of_le_of_ne hle hne.2)
    obtain ⟨d, hd⟩ := exists_relDim_eq_int (contractPrime j y)
    rw [hd, hPn, PFContracted.natCast_withBot_withTop] at d1
    rw [hd, hWn, PFContracted.natCast_withBot_withTop] at d2
    have e1 := WithTop.coe_lt_coe.mp (WithBot.coe_lt_coe.mp d1)
    have e2 := WithTop.coe_lt_coe.mp (WithBot.coe_lt_coe.mp d2)
    push_cast at e1
    omega
  have havoid : ∀ g, g ∉ P' → (∀ W' ∈ fibrePrimes j P' W, g ∉ W') → g ∉ y := by
    rcases hcases with h | h
    · have hyP' : y = P' := by
        by_contra hne
        have d1 := relDim_lt_of_lt (lt_of_le_of_ne hP'y (Ne.symm hne))
        have d2 := ContractRelDimLe.proof F K K' j ι' y hy
        rw [h, hPn, ← hP'n] at d2
        exact lt_irrefl _ (lt_of_lt_of_le d1 d2)
      exact fun g hg _ => hyP' ▸ hg
    · exact fun g _ hgW => hgW y ⟨hy, hP'y, h⟩
  intro x hx
  unfold degZeroLoc at hx
  induction hx using Algebra.adjoin_induction with
  | mem x hx =>
    obtain ⟨b, f, g, hf, hg, hgP, hgW, rfl⟩ := hx
    exact (hcen b f g hf hg (havoid g hgP hgW)).1
  | algebraMap c => exact hF c
  | add a a' _ _ ha ha' => exact R.add_mem _ _ ha ha'
  | mul a a' _ _ ha ha' => exact R.mul_mem _ _ ha ha'

end Centre

/- English proof (translation)
Introduce `F _ K K' _ _ _ _ j ι' _ P' hP' n hP'n hPn W hW hWn hPW`. Use `hP'.isPrime` as an intermediate fact. Set `f : degZeroLoc (contractPrime j P') {W} →+* FractionRing (MRing ι' F ⧸ P')` to `(algebraMap (degZeroLoc P' (fibrePrimes j P' W)) (FractionRing (MRing ι' F ⧸ P'))).comp (algebraMap (degZeroLoc (contractPrime j P') {W}) (degZeroLoc P' (fibrePrimes j P' W)))`. Use `⟨fun b => ?_⟩` and prove the remaining obligations. Use `RingHom.IsIntegralElem.of_map (g := algebraMap (degZeroLoc P' (fibrePrimes j P' W)) (FractionRing (MRing ι' F ⧸ P'))) Subtype.val_injective ?_` and prove the remaining obligations.

Establish `hmem : (b : FractionRing (MRing ι' F ⧸ P')) ∈ ⨅ V : {V : ValuationSubring (FractionRing (MRing ι' F ⧸ P')) // Set.range f ⊆ V.toSubring}, V.1.toSubring`. Rewrite using `[Subring.mem_iInf]`. Introduce and unpack `⟨V, hV⟩`. Conclude with `semilocal_le hC hP' hP'n hPn hW hWn hPW V (fun a ha => hV ⟨⟨a, ha⟩, rfl⟩) b b.2`. Rewrite `hmem` using `[iInf_valuationSubring_superset, ← RingHom.coe_range, Subring.closure_eq]`.

Take `⟨p, hp, hpx⟩` from `(hmem : IsIntegral f.range (b : FractionRing (MRing ι' F ⧸ P')))`. Take `⟨q, hq, -, hqm⟩` from `Polynomial.lifts_and_natDegree_eq_and_monic ((Polynomial.mem_lifts p).mpr (Polynomial.map_surjective f.rangeRestrict (fun ⟨_, a, ha⟩ => ⟨a, Subtype.ext ha⟩) p)) hp`. Use `⟨q, hqm, ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `Polynomial.eval₂ (f.range.subtype.comp f.rangeRestrict) (b : FractionRing _) q = 0`. Rewrite using `[← Polynomial.eval₂_map, hq]`.

Conclude with `hpx`.
-/
theorem proof (hC : ValuativeCentre.Statement.{u}) : SemilocalIntegral.Statement.{u} := by
  intro F _ K K' _ _ _ _ j ι' _ P' hP' n hP'n hPn W hW hWn hPW
  have := hP'.isPrime
  let f : degZeroLoc (contractPrime j P') {W} →+* FractionRing (MRing ι' F ⧸ P') :=
    (algebraMap (degZeroLoc P' (fibrePrimes j P' W)) (FractionRing (MRing ι' F ⧸ P'))).comp
      (algebraMap (degZeroLoc (contractPrime j P') {W}) (degZeroLoc P' (fibrePrimes j P' W)))
  refine ⟨fun b => ?_⟩
  refine RingHom.IsIntegralElem.of_map (g := algebraMap (degZeroLoc P' (fibrePrimes j P' W))
    (FractionRing (MRing ι' F ⧸ P'))) Subtype.val_injective ?_
  have hmem : (b : FractionRing (MRing ι' F ⧸ P')) ∈ ⨅ V : {V : ValuationSubring
      (FractionRing (MRing ι' F ⧸ P')) // Set.range f ⊆ V.toSubring}, V.1.toSubring := by
    rw [Subring.mem_iInf]
    rintro ⟨V, hV⟩
    exact semilocal_le hC hP' hP'n hPn hW hWn hPW V (fun a ha => hV ⟨⟨a, ha⟩, rfl⟩) b b.2
  rw [iInf_valuationSubring_superset, ← RingHom.coe_range, Subring.closure_eq] at hmem
  obtain ⟨p, hp, hpx⟩ := (hmem : IsIntegral f.range (b : FractionRing (MRing ι' F ⧸ P')))
  obtain ⟨q, hq, -, hqm⟩ := Polynomial.lifts_and_natDegree_eq_and_monic
    ((Polynomial.mem_lifts p).mpr
      (Polynomial.map_surjective f.rangeRestrict (fun ⟨_, a, ha⟩ => ⟨a, Subtype.ext ha⟩) p)) hp
  refine ⟨q, hqm, ?_⟩
  change Polynomial.eval₂ (f.range.subtype.comp f.rangeRestrict) (b : FractionRing _) q = 0
  rw [← Polynomial.eval₂_map, hq]
  exact hpx

end SemilocalIntegral

end

end GroundTheory.Heights₂.Heights.FieldNumbers

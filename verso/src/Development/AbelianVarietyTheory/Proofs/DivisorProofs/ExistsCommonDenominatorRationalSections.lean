import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsAmbOfIsArithVar
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEffectiveCartierDivisorAddEffective
open CategoryTheory AlgebraicGeometry TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt GlobalTheory.MixHt

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.MixHt.Denom

variable {Y : Scheme.{0}} [IsIntegral Y]

/- English proof (translation)
Establish `P` using `(presents_divOfRatSec hL hr).tens (presents_divOfRatSec hM (isRatSec_ratOfSec u hu))`. Take `⟨t, ht⟩` from `P.exists_rat_eq (f := 1) (CartierDiv.mem_sections.2 fun x => hE x)`. Establish `hη : genericPoint Y ∈ nonzeroLocus t` using `(P.generatesAt_rat_iff t).1 (ht ▸ CartierDiv.generatesAt_genericPoint _ one_ne_zero)`. Use `⟨t, hη, fun i j hi hj => Units.ext ?_⟩` and prove the remaining obligations. Establish `e` using `P.rat_mul t (i, j) ⟨hi, hj⟩`.

Rewrite `e` using `[ht, one_mul]`. Rewrite using `[val_ratOfSec (show genericPoint Y ∈ (tens L M).U (i, j) from ⟨hi, hj⟩), ← e]`.
-/
theorem exists_sec_tens {L M : LB Y} (hL : L.IsLB) (hM : M.IsLB) {r : L.ι → Y.functionFieldˣ}
    (hr : IsRatSec L r) (u : M.Sec) (hu : genericPoint Y ∈ nonzeroLocus u)
    (hE : (divOfRatSec hL hr + divOfSec hM u hu).Eff) :
    ∃ (t : (tens L M).Sec) (ht : genericPoint Y ∈ nonzeroLocus t), ∀ i j, genericPoint Y ∈ L.U i →
      genericPoint Y ∈ M.U j → ratOfSec t ht (i, j) = r i * ratOfSec u hu j := by
  have P := (presents_divOfRatSec hL hr).tens (presents_divOfRatSec hM (isRatSec_ratOfSec u hu))
  obtain ⟨t, ht⟩ := P.exists_rat_eq (f := 1) (CartierDiv.mem_sections.2 fun x => hE x)
  have hη : genericPoint Y ∈ nonzeroLocus t :=
    (P.generatesAt_rat_iff t).1 (ht ▸ CartierDiv.generatesAt_genericPoint _ one_ne_zero)
  refine ⟨t, hη, fun i j hi hj => Units.ext ?_⟩
  have e := P.rat_mul t (i, j) ⟨hi, hj⟩
  rw [ht, one_mul] at e
  rw [val_ratOfSec (show genericPoint Y ∈ (tens L M).U (i, j) from ⟨hi, hj⟩), ← e]

/- English proof (translation)
Take `⟨i, hi⟩` from `exists_chart hL (genericPoint Y)`. Establish `hj : genericPoint Y ∈ (lbPow L m).U (fun _ => i)` using `(lbPow_U L m _).ge hi`. Use `(mem_nonzeroLocus_iff _ _ hj).2 ((unitAt_fnOf_iff hj hj _).1 (unitAt_genericPoint ?_))` and prove the remaining obligations. Use `show fnOf _ hj (resG Y _ (t.f i) ^ m) ≠ 0`. Rewrite using `[map_pow, fnOf_resG]`.

Conclude with `pow_ne_zero _ (fnOf_sec_ne_zero ht hi)`.
-/
theorem gen_mem_secPow {L : LB Y} (hL : L.IsLB) (t : L.Sec) (ht : genericPoint Y ∈ nonzeroLocus t)
    (m : ℕ) : genericPoint Y ∈ nonzeroLocus (Cartier.secPow t m) := by
  obtain ⟨i, hi⟩ := exists_chart hL (genericPoint Y)
  have hj : genericPoint Y ∈ (lbPow L m).U (fun _ => i) := (lbPow_U L m _).ge hi
  refine (mem_nonzeroLocus_iff _ _ hj).2 ((unitAt_fnOf_iff hj hj _).1 (unitAt_genericPoint ?_))
  show fnOf _ hj (resG Y _ (t.f i) ^ m) ≠ 0
  rw [map_pow, fnOf_resG]
  exact pow_ne_zero _ (fnOf_sec_ne_zero ht hi)

/- English proof (translation)
Use `CartierDiv.ext_of_isEqn fun x => ?_` and prove the remaining obligations. Take `⟨i, hi⟩` from `exists_chart hL x`. Establish `hj : x ∈ (lbPow L m).U (fun _ => i)` using `(lbPow_U L m _).ge hi`. Establish `e : ratOfSec (Cartier.secPow t m) hm (fun _ => i) = ratOfSec t ht i ^ m`. Use `Units.ext ?_` and prove the remaining obligations.

Rewrite using `[Units.val_pow_eq_pow_val, val_ratOfSec (gen_mem hi), val_ratOfSec (gen_mem hj)]`. Use `show fnOf _ (gen_mem hj) (resG Y _ (t.f i) ^ m) = _`. Rewrite using `[map_pow, fnOf_resG]`. Use `⟨ratOfSec t ht i ^ m, ?_, ((presents_divOfRatSec hL (isRatSec_ratOfSec t ht)).isEqn i x hi).nsmul m⟩` and prove the remaining obligations. Rewrite using `[← e]`.

Conclude with `(presents_divOfRatSec (isLB_lbPow hL m) (isRatSec_ratOfSec _ hm)).isEqn _ x hj`.
-/
theorem divOfSec_secPow {L : LB Y} (hL : L.IsLB) (t : L.Sec) (ht : genericPoint Y ∈ nonzeroLocus t)
    (m : ℕ) (hm : genericPoint Y ∈ nonzeroLocus (Cartier.secPow t m)) :
    divOfSec (isLB_lbPow hL m) (Cartier.secPow t m) hm = m • divOfSec hL t ht := by
  refine CartierDiv.ext_of_isEqn fun x => ?_
  obtain ⟨i, hi⟩ := exists_chart hL x
  have hj : x ∈ (lbPow L m).U (fun _ => i) := (lbPow_U L m _).ge hi
  have e : ratOfSec (Cartier.secPow t m) hm (fun _ => i) = ratOfSec t ht i ^ m := by
    refine Units.ext ?_
    rw [Units.val_pow_eq_pow_val, val_ratOfSec (gen_mem hi), val_ratOfSec (gen_mem hj)]
    show fnOf _ (gen_mem hj) (resG Y _ (t.f i) ^ m) = _
    rw [map_pow, fnOf_resG]
  refine ⟨ratOfSec t ht i ^ m, ?_,
    ((presents_divOfRatSec hL (isRatSec_ratOfSec t ht)).isEqn i x hi).nsmul m⟩
  rw [← e]
  exact (presents_divOfRatSec (isLB_lbPow hL m) (isRatSec_ratOfSec _ hm)).isEqn _ x hj

/- English proof (translation)
Take `⟨i, hi⟩` from `exists_chart hL (genericPoint Y)`. Take `⟨U, hU, a, ha⟩` from `(regAt_genericPoint (r i : Y.functionField)).exists_fnOf`. Use `⟨L.U i ⊓ U, ⟨hi, hU⟩, fun x hx => ?_⟩` and prove the remaining obligations. Use `((presents_divOfRatSec hL hr).isEqn i x hx.1).regularAt_iff.2 ?_` and prove the remaining obligations. Rewrite using `[one_mul, ← ha]`.

Conclude with `regAt_fnOf hx.2 _ a`.
-/
theorem exists_open_regularAt {L : LB Y} (hL : L.IsLB) {r : L.ι → Y.functionFieldˣ}
    (hr : IsRatSec L r) :
    ∃ W : Y.Opens, genericPoint Y ∈ W ∧ ∀ x ∈ W, (divOfRatSec hL hr).RegularAt x 1 := by
  obtain ⟨i, hi⟩ := exists_chart hL (genericPoint Y)
  obtain ⟨U, hU, a, ha⟩ := (regAt_genericPoint (r i : Y.functionField)).exists_fnOf
  refine ⟨L.U i ⊓ U, ⟨hi, hU⟩, fun x hx => ?_⟩
  refine ((presents_divOfRatSec hL hr).isEqn i x hx.1).regularAt_iff.2 ?_
  rw [one_mul, ← ha]
  exact regAt_fnOf hx.2 _ a

end GlobalTheory.MixHt.Denom

open GlobalTheory.MixHt.Denom in

/- English proof (translation)
Introduce `k _ Y _ q hq N r r' hr hr'`. Take `⟨n₀, j, hj, hjq⟩` from `hq.isProjOver`. Set `H : HermLB q` to `(ProjSpace.hermitianTwistingSheaf k n₀).pull j hjq`. Establish `hH : IsAmpleLB H.B` using `(isAmple_projective_O_one k n₀).pull_of_isClosedImmersion j`. Use `haveI := hH.compactSpace`.

Take `⟨W, hW, hWr⟩` from `exists_open_regularAt N.isLB hr`. Take `⟨W', hW', hWr'⟩` from `exists_open_regularAt N.isLB hr'`. Take `⟨n, -, t, ht, hle, -⟩` from `hH.exists_affine_le (x := genericPoint Y) (U := W ⊓ W') ⟨hW, hW'⟩`. Establish `hL` using `isLB_lbPow H.isLB n`. Take `⟨N₁, h₁⟩` from `EffDiff.eventually_eff_add_nsmul hL t ht _ fun x hx => hWr x (hle hx).1`.

Take `⟨N₂, h₂⟩` from `EffDiff.eventually_eff_add_nsmul hL t ht _ fun x hx => hWr' x (hle hx).2`. Establish `hu` using `gen_mem_secPow hL t ht (max N₁ N₂)`. Establish `hD` using `divOfSec_secPow hL t ht (max N₁ N₂) hu`. Take `⟨s, hs, e⟩` from `exists_sec_tens N.isLB (isLB_lbPow hL _) hr (Cartier.secPow t (max N₁ N₂)) hu (by rw [hD]; exact h₁ _ (le_max_left _ _))`. Take `⟨s', hs', e'⟩` from `exists_sec_tens N.isLB (isLB_lbPow hL _) hr' (Cartier.secPow t (max N₁ N₂)) hu (by rw [hD]; exact h₂ _ (le_max_right _ _))`.

Conclude with `⟨(H.pow n).pow (max N₁ N₂), Cartier.secPow t (max N₁ N₂), s, s', hu, hs, hs', fun i j hi hj => ⟨e i j hi hj, e' i j hi hj⟩⟩`.
-/
theorem GlobalTheory.MixHt.exists_common_denom : ∀ (k : Type) [CommRing k] (Y : Scheme.{0}) [IsIntegral Y]
    (q : Y ⟶ Sp k), IsAmb q → ∀ (N : HermLB q) (r r' : N.B.ι → Y.functionFieldˣ), IsRatSec N.B r →
    IsRatSec N.B r' → ∃ (A : HermLB q) (u : A.B.Sec) (t t' : (N.tens A).B.Sec)
    (hu : genericPoint Y ∈ nonzeroLocus u) (ht : genericPoint Y ∈ nonzeroLocus t)
    (ht' : genericPoint Y ∈ nonzeroLocus t'), ∀ (i : N.B.ι) (j : A.B.ι), genericPoint Y ∈ N.B.U i →
    genericPoint Y ∈ A.B.U j → ratOfSec t ht (i, j) = r i * ratOfSec u hu j ∧
      ratOfSec t' ht' (i, j) = r' i * ratOfSec u hu j := by
  intro k _ Y _ q hq N r r' hr hr'
  obtain ⟨n₀, j, hj, hjq⟩ := hq.isProjOver
  let H : HermLB q := (ProjSpace.hermitianTwistingSheaf k n₀).pull j hjq
  have hH : IsAmpleLB H.B := (isAmple_projective_O_one k n₀).pull_of_isClosedImmersion j
  haveI := hH.compactSpace
  obtain ⟨W, hW, hWr⟩ := exists_open_regularAt N.isLB hr
  obtain ⟨W', hW', hWr'⟩ := exists_open_regularAt N.isLB hr'
  obtain ⟨n, -, t, ht, hle, -⟩ :=
    hH.exists_affine_le (x := genericPoint Y) (U := W ⊓ W') ⟨hW, hW'⟩
  have hL := isLB_lbPow H.isLB n
  obtain ⟨N₁, h₁⟩ := EffDiff.eventually_eff_add_nsmul hL t ht _ fun x hx => hWr x (hle hx).1
  obtain ⟨N₂, h₂⟩ := EffDiff.eventually_eff_add_nsmul hL t ht _ fun x hx => hWr' x (hle hx).2
  have hu := gen_mem_secPow hL t ht (max N₁ N₂)
  have hD := divOfSec_secPow hL t ht (max N₁ N₂) hu
  obtain ⟨s, hs, e⟩ := exists_sec_tens N.isLB (isLB_lbPow hL _) hr (Cartier.secPow t (max N₁ N₂)) hu
    (by rw [hD]; exact h₁ _ (le_max_left _ _))
  obtain ⟨s', hs', e'⟩ := exists_sec_tens N.isLB (isLB_lbPow hL _) hr' (Cartier.secPow t (max N₁ N₂)) hu
    (by rw [hD]; exact h₂ _ (le_max_right _ _))
  exact ⟨(H.pow n).pow (max N₁ N₂), Cartier.secPow t (max N₁ N₂), s, s', hu, hs, hs',
    fun i j hi hj => ⟨e i j hi hj, e' i j hi hj⟩⟩

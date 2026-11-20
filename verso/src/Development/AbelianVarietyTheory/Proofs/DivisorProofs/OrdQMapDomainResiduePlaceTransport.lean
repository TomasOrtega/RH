import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GeometricallyConnectedOfIsIsoRestrict
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsLocModelIsPrimeOf
import Development.AbelianVarietyTheory.Definitions.Divisors.NotDominatesTopPlace
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy GlobalTheory.FieldPair
open scoped TensorProduct

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.FieldPair.ResidueTransport

variable {k M : Type} [Field k] [Field M] {c : k →+* M}

/- English proof (translation)
Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty => simp`. Consider the case `insert a s ha ih`. Rewrite using `[Finset.prod_insert ha, Finset.sum_insert ha, P.ord_mul (zpow_ne_zero _ (hf a (Finset.mem_insert_self a s))) (Finset.prod_ne_zero_iff.2 fun i hi => zpow_ne_zero _ (hf i (Finset.mem_insert_of_mem hi))), P.ord_zpow, ih fun i hi => hf i (Finset.mem_insert_of_mem hi)]`.
-/
theorem ord_prod_zpow {ι : Type} (P : Place c) (s : Finset ι) (f : ι → M) (n : ι → ℤ)
    (hf : ∀ i ∈ s, f i ≠ 0) : P.ord (∏ i ∈ s, f i ^ n i) = ∑ i ∈ s, n i * P.ord (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.sum_insert ha,
      P.ord_mul (zpow_ne_zero _ (hf a (Finset.mem_insert_self a s)))
        (Finset.prod_ne_zero_iff.2 fun i hi => zpow_ne_zero _ (hf i (Finset.mem_insert_of_mem hi))),
      P.ord_zpow, ih fun i hi => hf i (Finset.mem_insert_of_mem hi)]

/- English proof (translation)
Rewrite using `[Place.ordQ, Finsupp.linearCombination_mapDomain, Finsupp.linearCombination_apply, Finsupp.sum]`. Simplify using `[smul_eq_mul]`.
-/
theorem ordQ_mapDomain {ι : Type} (P : Place c) (φ : ι →₀ ℚ) (f : ι → M) :
    P.ordQ (Finsupp.mapDomain f φ) = ∑ g ∈ φ.support, φ g * P.ord (f g) := by
  rw [Place.ordQ, Finsupp.linearCombination_mapDomain, Finsupp.linearCombination_apply, Finsupp.sum]
  simp [smul_eq_mul]

/- English proof (translation)
Rewrite using `[ord_prod_zpow P _ f m hf, ordQ_mapDomain, Finset.mul_sum]`. Use `push_cast`. Use `Finset.sum_congr rfl fun g hg => ?_` and prove the remaining obligations. Rewrite using `[hm g hg]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem ord_prod_eq_mul_ordQ {ι : Type} (P : Place c) (φ : ι →₀ ℚ) (f : ι → M) (N : ℕ)
    (m : ι → ℤ) (hm : ∀ g ∈ φ.support, (m g : ℚ) = N * φ g) (hf : ∀ g ∈ φ.support, f g ≠ 0) :
    (P.ord (∏ g ∈ φ.support, f g ^ m g) : ℚ) = N * P.ordQ (Finsupp.mapDomain f φ) := by
  rw [ord_prod_zpow P _ f m hf, ordQ_mapDomain, Finset.mul_sum]
  push_cast
  refine Finset.sum_congr rfl fun g hg => ?_
  rw [hm g hg]
  ring

/- English proof (translation)
Use `⟨∏ g ∈ s, (φ g).den, Finset.prod_pos fun g _ => (φ g).den_pos, fun g hg => ⟨(φ g).num * ∏ x ∈ s.erase g, ((φ x).den : ℤ), ?_⟩⟩` and prove the remaining obligations. Rewrite using `[← Finset.mul_prod_erase s _ hg]`. Use `push_cast`. Rewrite using `[← Rat.mul_den_eq_num]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem exists_common_den {ι : Type} (s : Finset ι) (φ : ι → ℚ) :
    ∃ N : ℕ, 0 < N ∧ ∀ g ∈ s, ∃ m : ℤ, (m : ℚ) = N * φ g := by
  classical
  refine ⟨∏ g ∈ s, (φ g).den, Finset.prod_pos fun g _ => (φ g).den_pos, fun g hg =>
    ⟨(φ g).num * ∏ x ∈ s.erase g, ((φ x).den : ℤ), ?_⟩⟩
  rw [← Finset.mul_prod_erase s _ hg]
  push_cast
  rw [← Rat.mul_den_eq_num]
  ring

end GlobalTheory.FieldPair.ResidueTransport

namespace GlobalTheory.FieldPair

open ResidueTransport in

/- English proof (translation)
Establish `hker : RingHom.ker ψ = IsLocalRing.maximalIdeal S.ring` using `IsLocalRing.eq_maximalIdeal (RingHom.ker_isMaximal_of_surjective ψ hψ)`. Establish `hunit : ∀ g ∈ φ.support, IsUnit g` using `fun g hg => IsLocalRing.notMem_maximalIdeal.1 (by rw [← hker, RingHom.mem_ker]; exact hsupp g hg)`. Use `choose! w hw using hunit`. Take `⟨N, hN, hm⟩` from `exists_common_den φ.support φ`. Use `choose! m hm using hm`.

Establish `hg0 : ∀ g ∈ φ.support, ((g : S.ring) : L) ≠ 0` using `fun g hg h => hsupp g hg (by rw [show g = 0 from Subtype.ext h, map_zero])`. Use `set G : L := ∏ g ∈ φ.support, ((g : S.ring) : L) ^ m g with hGdef`. Use `set H : K := ∏ g ∈ φ.support, ψ g ^ m g with hHdef`. Establish `hGord` using `fun P : Place cL => ord_prod_eq_mul_ordQ P φ (fun g : S.ring => (g : L)) N m hm hg0`. Establish `hHord` using `ord_prod_eq_mul_ordQ F φ ψ N m hm hsupp`.

Establish `hG0 : G ≠ 0` using `Finset.prod_ne_zero_iff.2 fun g hg => zpow_ne_zero _ (hg0 g hg)`. Establish `hPG : ∀ P : Place cL, P.IsPrimeOf Q → P.ring ≠ E.ring → P.ord G = 0`. Introduce `P hP hPE`. Distinguish the cases in `hPS : P.ring = S.ring`. Take `rfl : P = S` from `Place.ext hPS`.

Rewrite using `[hGdef, ord_prod_zpow P _ _ m hg0]`. Use `Finset.sum_eq_zero fun g hg => ?_` and prove the remaining obligations. Rewrite using `[← hw g hg, P.ord_eq_zero (w g).isUnit, mul_zero]`. Establish `h` using `hGord P`. Rewrite `h` using `[hPφ P hP hPS hPE, mul_zero]`.

Conclude with `h` after adjusting the coercions. Take `⟨q, hqU, hGq⟩` from `hG G hG0 hPG`. Use `set b := E.ord G with hb`. Set `uS : S.ring` to `⟨u, hSQ _ u.2⟩`. Establish `huS : IsUnit uS`.

Establish `h1 : (u : L) ∈ S.ring` using `hSQ _ u.2`. Establish `h2 : (u : L)⁻¹ ∈ S.ring`. Rewrite using `[← S.ord_nonneg_iff (inv_ne_zero hu0), S.ord_inv, hSu]`. Simplify using the standard rewrite rules. Conclude with `IsUnit.of_mul_eq_one (⟨_, h2⟩ : S.ring) (Subtype.ext (mul_inv_cancel₀ hu0))`.

Take `⟨r, hr⟩` from `hqU.exists_right_inv`. Set `qS : S.ring` to `⟨q, hSQ _ q.2⟩`. Set `rS : S.ring` to `⟨r, hSQ _ r.2⟩`. Establish `hqr : qS * rS = 1` using `Subtype.ext (by change ((q * r : Q) : L) = 1; rw [hr]; rfl)`. Set `qU : S.ringˣ` to `(IsUnit.of_mul_eq_one rS hqr).unit`.

Set `uU : S.ringˣ` to `huS.unit`. Set `W : S.ringˣ` to `∏ g ∈ φ.support, w g ^ m g`. Set `e : S.ringˣ →* Lˣ` to `Units.map (S.ring.subtype : S.ring →* L)`. Set `f : S.ringˣ →* Kˣ` to `Units.map (ψ : S.ring →* K)`. Establish `he : ∀ x, ((e x : Lˣ) : L) = ((x : S.ring) : L)` using `fun _ => rfl`.

Establish `hf : ∀ x, ((f x : Kˣ) : K) = ψ x` using `fun _ => rfl`. Establish `heW : ((e W : Lˣ) : L) = G`. Simplify using `only [W, map_prod, map_zpow, Units.coe_prod, Units.val_zpow_eq_zpow_val, he]`. Conclude with `Finset.prod_congr rfl fun g hg => by rw [hw g hg]`. Establish `hfW : ((f W : Kˣ) : K) = H`.

Simplify using `only [W, map_prod, map_zpow, Units.coe_prod, Units.val_zpow_eq_zpow_val, hf]`. Conclude with `Finset.prod_congr rfl fun g hg => by rw [hw g hg]`. Establish `hWeq : W = qU * uU ^ b`. Establish `hinj : Function.Injective e` using `fun x y h => Units.ext (Subtype.ext (by rw [← he, ← he, h]))`. Apply `hinj` to reduce the goal to its premises.

Apply `Units.ext` to reduce the goal to its premises. Rewrite using `[heW, map_mul, map_zpow, Units.val_mul, Units.val_zpow_eq_zpow_val, he, he, IsUnit.unit_spec, IsUnit.unit_spec]`. Conclude with `hGq`. Establish `hH : H = ψ qS * ψ uS ^ b`. Rewrite using `[← hfW, hWeq, map_mul, map_zpow, Units.val_mul, Units.val_zpow_eq_zpow_val, hf, hf, IsUnit.unit_spec, IsUnit.unit_spec]`.

Establish `hq0 : ψ qS * ψ rS = 1` using `by rw [← map_mul, hqr, map_one]`. Establish `hψq0 : ψ qS ≠ 0` using `left_ne_zero_of_mul_eq_one hq0`. Establish `hψu0 : ψ uS ≠ 0` using `(huS.map ψ).ne_zero`. Establish `hFq : F.ord (ψ qS) = 0`. Establish `h1 : 0 ≤ F.ord (ψ qS)` using `(F.ord_nonneg_iff hψq0).2 ((hF _).2 ⟨qS, q.2, rfl⟩)`.

Establish `hinv : (ψ qS)⁻¹ = ψ rS` using `inv_eq_of_mul_eq_one_right hq0`. Establish `h2 : 0 ≤ F.ord (ψ qS)⁻¹` using `(F.ord_nonneg_iff (inv_ne_zero hψq0)).2 (by rw [hinv]; exact (hF _).2 ⟨rS, r.2, rfl⟩)`. Rewrite `h2` using `[F.ord_inv]`. Use linear arithmetic over natural numbers and integers. Establish `hFH : F.ord H = b`.

Rewrite using `[hH, F.ord_mul hψq0 (zpow_ne_zero _ hψu0), F.ord_zpow, hFq, hFu uS rfl]`. Expand and normalize the polynomial expressions, which then agree. Establish `hNq : (N : ℚ) ≠ 0` using `by exact_mod_cast hN.ne'`. Establish `hEG` using `hGord E`. Rewrite `hEG` using `[← hb, ← hFH, hHord]`.

Conclude with `mul_left_cancel₀ hNq hEG`.
-/
theorem ordQ_mapDomain_residue_eq {L K : Type} [Field L] [Field K] (cL : ℂ →+* L) (cK : ℂ →+* K)
    (Q : Subring L) (u : Q) (S E : Place cL) (ψ : S.ring →+* K) (F : Place cK)
    (hSQ : S.Contains Q) (hSu : S.ord (u : L) = 0) (hu0 : (u : L) ≠ 0)
    (hψ : Function.Surjective ψ)
    (hF : ∀ a : K, a ∈ F.ring ↔ ∃ q : S.ring, (q : L) ∈ Q ∧ ψ q = a)
    (hFu : ∀ us : S.ring, (us : L) = u → F.ord (ψ us) = 1)
    (hG : ∀ G : L, G ≠ 0 → (∀ P : Place cL, P.IsPrimeOf Q → P.ring ≠ E.ring → P.ord G = 0) →
      ∃ q : Q, IsUnit q ∧ G = (q : L) * (u : L) ^ E.ord G)
    (φ : S.ring →₀ ℚ) (hsupp : ∀ g ∈ φ.support, ψ g ≠ 0)
    (hPφ : ∀ P : Place cL, P.IsPrimeOf Q → P.ring ≠ S.ring → P.ring ≠ E.ring →
      P.ordQ (Finsupp.mapDomain (fun g : S.ring => (g : L)) φ) = 0) :
    F.ordQ (Finsupp.mapDomain ψ φ) =
      E.ordQ (Finsupp.mapDomain (fun g : S.ring => (g : L)) φ) := by

  have hker : RingHom.ker ψ = IsLocalRing.maximalIdeal S.ring :=
    IsLocalRing.eq_maximalIdeal (RingHom.ker_isMaximal_of_surjective ψ hψ)
  have hunit : ∀ g ∈ φ.support, IsUnit g := fun g hg =>
    IsLocalRing.notMem_maximalIdeal.1 (by rw [← hker, RingHom.mem_ker]; exact hsupp g hg)
  choose! w hw using hunit
  obtain ⟨N, hN, hm⟩ := exists_common_den φ.support φ
  choose! m hm using hm
  have hg0 : ∀ g ∈ φ.support, ((g : S.ring) : L) ≠ 0 := fun g hg h =>
    hsupp g hg (by rw [show g = 0 from Subtype.ext h, map_zero])
  set G : L := ∏ g ∈ φ.support, ((g : S.ring) : L) ^ m g with hGdef
  set H : K := ∏ g ∈ φ.support, ψ g ^ m g with hHdef
  have hGord := fun P : Place cL => ord_prod_eq_mul_ordQ P φ (fun g : S.ring => (g : L)) N m hm hg0
  have hHord := ord_prod_eq_mul_ordQ F φ ψ N m hm hsupp
  have hG0 : G ≠ 0 := Finset.prod_ne_zero_iff.2 fun g hg => zpow_ne_zero _ (hg0 g hg)

  have hPG : ∀ P : Place cL, P.IsPrimeOf Q → P.ring ≠ E.ring → P.ord G = 0 := by
    intro P hP hPE
    by_cases hPS : P.ring = S.ring
    · obtain rfl : P = S := Place.ext hPS
      rw [hGdef, ord_prod_zpow P _ _ m hg0]
      refine Finset.sum_eq_zero fun g hg => ?_
      rw [← hw g hg, P.ord_eq_zero (w g).isUnit, mul_zero]
    · have h := hGord P
      rw [hPφ P hP hPS hPE, mul_zero] at h
      exact_mod_cast h
  obtain ⟨q, hqU, hGq⟩ := hG G hG0 hPG
  set b := E.ord G with hb

  let uS : S.ring := ⟨u, hSQ _ u.2⟩
  have huS : IsUnit uS := by
    have h1 : (u : L) ∈ S.ring := hSQ _ u.2
    have h2 : (u : L)⁻¹ ∈ S.ring := by
      rw [← S.ord_nonneg_iff (inv_ne_zero hu0), S.ord_inv, hSu]; simp
    exact IsUnit.of_mul_eq_one (⟨_, h2⟩ : S.ring) (Subtype.ext (mul_inv_cancel₀ hu0))
  obtain ⟨r, hr⟩ := hqU.exists_right_inv
  let qS : S.ring := ⟨q, hSQ _ q.2⟩
  let rS : S.ring := ⟨r, hSQ _ r.2⟩
  have hqr : qS * rS = 1 := Subtype.ext (by change ((q * r : Q) : L) = 1; rw [hr]; rfl)
  let qU : S.ringˣ := (IsUnit.of_mul_eq_one rS hqr).unit
  let uU : S.ringˣ := huS.unit
  let W : S.ringˣ := ∏ g ∈ φ.support, w g ^ m g
  let e : S.ringˣ →* Lˣ := Units.map (S.ring.subtype : S.ring →* L)
  let f : S.ringˣ →* Kˣ := Units.map (ψ : S.ring →* K)
  have he : ∀ x, ((e x : Lˣ) : L) = ((x : S.ring) : L) := fun _ => rfl
  have hf : ∀ x, ((f x : Kˣ) : K) = ψ x := fun _ => rfl
  have heW : ((e W : Lˣ) : L) = G := by
    simp only [W, map_prod, map_zpow, Units.coe_prod, Units.val_zpow_eq_zpow_val, he]
    exact Finset.prod_congr rfl fun g hg => by rw [hw g hg]
  have hfW : ((f W : Kˣ) : K) = H := by
    simp only [W, map_prod, map_zpow, Units.coe_prod, Units.val_zpow_eq_zpow_val, hf]
    exact Finset.prod_congr rfl fun g hg => by rw [hw g hg]
  have hWeq : W = qU * uU ^ b := by
    have hinj : Function.Injective e := fun x y h =>
      Units.ext (Subtype.ext (by rw [← he, ← he, h]))
    apply hinj
    apply Units.ext
    rw [heW, map_mul, map_zpow, Units.val_mul, Units.val_zpow_eq_zpow_val, he, he,
      IsUnit.unit_spec, IsUnit.unit_spec]
    exact hGq
  have hH : H = ψ qS * ψ uS ^ b := by
    rw [← hfW, hWeq, map_mul, map_zpow, Units.val_mul, Units.val_zpow_eq_zpow_val, hf, hf,
      IsUnit.unit_spec, IsUnit.unit_spec]

  have hq0 : ψ qS * ψ rS = 1 := by rw [← map_mul, hqr, map_one]
  have hψq0 : ψ qS ≠ 0 := left_ne_zero_of_mul_eq_one hq0
  have hψu0 : ψ uS ≠ 0 := (huS.map ψ).ne_zero
  have hFq : F.ord (ψ qS) = 0 := by
    have h1 : 0 ≤ F.ord (ψ qS) := (F.ord_nonneg_iff hψq0).2 ((hF _).2 ⟨qS, q.2, rfl⟩)
    have hinv : (ψ qS)⁻¹ = ψ rS := inv_eq_of_mul_eq_one_right hq0
    have h2 : 0 ≤ F.ord (ψ qS)⁻¹ := (F.ord_nonneg_iff (inv_ne_zero hψq0)).2
      (by rw [hinv]; exact (hF _).2 ⟨rS, r.2, rfl⟩)
    rw [F.ord_inv] at h2
    omega
  have hFH : F.ord H = b := by
    rw [hH, F.ord_mul hψq0 (zpow_ne_zero _ hψu0), F.ord_zpow, hFq, hFu uS rfl]
    ring
  have hNq : (N : ℚ) ≠ 0 := by exact_mod_cast hN.ne'
  have hEG := hGord E
  rw [← hb, ← hFH, hHord] at hEG
  exact mul_left_cancel₀ hNq hEG

end GlobalTheory.FieldPair

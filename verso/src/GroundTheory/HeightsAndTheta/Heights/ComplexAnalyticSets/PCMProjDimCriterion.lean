import Mathlib
import GroundTheory.ArithmeticGeometry.SchemeCohomology.RegularUFDSerre
import GroundTheory.ArithmeticGeometry.SchemeCohomology.RegularSmooth
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StCMProjDimCriterion
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StAuslanderBuchsbaumDepthLower
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StAuslanderBuchsbaumProjDimUpper
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StRegularSequenceLengthLeDim
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StCMHeightAddDim
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open IsLocalRing CategoryTheory RingTheory.Sequence

/- English proof (translation)
Proceed by induction on `x using WithBot.recBotCoe with`. Consider the case `bot => exact absurd rfl h0`. Consider the case `coe y`. Establish `hy : y ≤ (d : ℕ∞)` using `by exact_mod_cast hle`. Establish `hyt : y ≠ ⊤` using `ne_top_of_le_ne_top (ENat.natCast_ne_top d) hy`.

Conclude with `⟨y.toNat, by rw [← ENat.natCast_toNat hyt]; rfl⟩`.
-/
theorem exists_nat_eq_of_ne_bot_of_le {x : WithBot ℕ∞} {d : ℕ} (h0 : x ≠ ⊥) (hle : x ≤ (d : WithBot ℕ∞)) :
    ∃ e : ℕ, x = e := by
  induction x using WithBot.recBotCoe with
  | bot => exact absurd rfl h0
  | coe y =>
    have hy : y ≤ (d : ℕ∞) := by exact_mod_cast hle
    have hyt : y ≠ ⊤ := ne_top_of_le_ne_top (ENat.natCast_ne_top d) hy
    exact ⟨y.toNat, by rw [← ENat.natCast_toNat hyt]; rfl⟩

/- English proof (translation)
Rewrite using `[mem_maximalIdeal, mem_nonunits_iff]`. Introduce `hu`. Take `⟨t, ht⟩` from `hu.exists_right_inv`. Take `⟨s, rfl⟩` from `Ideal.Quotient.mk_surjective t`. Establish `h1 : r * s - 1 ∈ J`.

Rewrite using `[← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_mul, ht, map_one, sub_self]`. Establish `h2 : (1 : S) ∈ maximalIdeal S`. Use `sub_mem ((maximalIdeal S).mul_mem_right s hr) (hJ h1)` as an intermediate fact. Rewrite `this` using `[sub_sub_cancel]`. Then use the resulting hypothesis. Conclude with `(maximalIdeal.isMaximal S).ne_top ((Ideal.eq_top_iff_one _).mpr h2)`.
-/
theorem quotient_mk_mem_maximalIdeal {S : Type*} [CommRing S] [IsLocalRing S] {J : Ideal S}
    [IsLocalRing (S ⧸ J)] (hJ : J ≤ maximalIdeal S) {r : S} (hr : r ∈ maximalIdeal S) :
    Ideal.Quotient.mk J r ∈ maximalIdeal (S ⧸ J) := by
  rw [mem_maximalIdeal, mem_nonunits_iff]
  intro hu
  obtain ⟨t, ht⟩ := hu.exists_right_inv
  obtain ⟨s, rfl⟩ := Ideal.Quotient.mk_surjective t
  have h1 : r * s - 1 ∈ J := by
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_mul, ht, map_one, sub_self]
  have h2 : (1 : S) ∈ maximalIdeal S := by
    have := sub_mem ((maximalIdeal S).mul_mem_right s hr) (hJ h1)
    rwa [sub_sub_cancel] at this
  exact (maximalIdeal.isMaximal S).ne_top ((Ideal.eq_top_iff_one _).mpr h2)

/- English proof (translation)
Rewrite `hr`, the goal using `[mem_maximalIdeal, mem_nonunits_iff]`. Conclude with `fun hu => hr (hu.map _)`.
-/
theorem mem_maximalIdeal_of_quotient_mk {S : Type*} [CommRing S] [IsLocalRing S] {J : Ideal S}
    [IsLocalRing (S ⧸ J)] {r : S} (hr : Ideal.Quotient.mk J r ∈ maximalIdeal (S ⧸ J)) : r ∈ maximalIdeal S := by
  rw [mem_maximalIdeal, mem_nonunits_iff] at hr ⊢
  exact fun hu => hr (hu.map _)

/- English proof (translation)
Establish `hJ : J ≠ ⊤` using `fun h => (maximalIdeal.isMaximal S).ne_top (top_le_iff.mp (h ▸ hJm))`. Establish `: Nontrivial (S ⧸ J)` using `Ideal.Quotient.nontrivial_iff.mpr hJ`. Establish `: IsLocalRing (S ⧸ J)` using `.of_surjective' _ Ideal.Quotient.mk_surjective`. Take `⟨rs0, hrs0, hofl, hlen0⟩` from `GroundTheory.Arith.SchemeCoh.exists_isRegular_ofList_eq_maximalIdeal (R := S)`. Establish `hrs0m : ∀ r ∈ rs0, r ∈ maximalIdeal S` using `fun r hr => hofl ▸ Ideal.subset_span hr`.

Use `set d := rs0.length with hd_def`. Establish `hcmS : IsCohenMacaulayLocalRing S` using `{ exists_isWeaklyRegular := ⟨rs0, hrs0m, hrs0.toIsWeaklyRegular, hlen0.symm⟩ }`. Establish `hsum` using `hcm S J hJ`. Rewrite `hsum` using `[← hlen0]`. Take `⟨e, he⟩` from `exists_nat_eq_of_ne_bot_of_le (x := ringKrullDim (S ⧸ J)) (d := d) (ringKrullDim_ne_bot) (hlen0 ▸ ringKrullDim_quotient_le J)`.

Establish `hht : J.height ≠ ⊤`. Introduce `h`. Rewrite `hsum` using `[h, he]`. Establish `h2 : ((⊤ : ℕ∞) + e : ℕ∞) = d` using `by exact_mod_cast hsum`. Simplify using `at h2`.

Take `⟨h, hh⟩ : ∃ h : ℕ, J.height = h` from `⟨J.height.toNat, (ENat.natCast_toNat hht).symm⟩`. Establish `hhe : h + e = d`. Rewrite `hsum` using `[hh, he]`. Conclude with `hsum` after adjusting the coercions. Establish `hserre : HasProjectiveDimensionLE (ModuleCat.of S (S ⧸ J)) d` using `GroundTheory.Arith.SchemeCoh.hasProjectiveDimensionLT_of_isRegularLocalRing hlen0.symm (S ⧸ J)`.

Prove the components needed by the constructor for the conclusion. Introduce `hCM`. Take `⟨as, has_m, has_reg, has_len⟩` from `hCM.exists_isWeaklyRegular`. Take `⟨ms, hms⟩ : ∃ ms : List S, ms.map (algebraMap S (S ⧸ J)) = as` from `⟨as.map fun a => (Ideal.Quotient.mk_surjective a).choose, by`. Rewrite using `[List.map_map]`.

Use `conv_rhs => rw [← List.map_id as]`. Conclude with `List.map_congr_left fun a _ => (Ideal.Quotient.mk_surjective a).choose_spec⟩`. Establish `hmsreg : IsWeaklyRegular (S ⧸ J) ms`. Rewrite using `[← isWeaklyRegular_map_algebraMap_iff (S ⧸ J) (S ⧸ J) ms, hms]`. Conclude with `has_reg`.

Establish `hmsm : ∀ r ∈ ms, r ∈ maximalIdeal S` using `fun r hr => mem_maximalIdeal_of_quotient_mk (has_m _ (hms ▸ List.mem_map_of_mem hr))`. Establish `hmslen : ms.length = e`. Establish `: (as.length : WithBot ℕ∞) = e` using `has_len.symm.trans he`. Rewrite `this` using `[← hms, List.length_map]`. Conclude with `this` after adjusting the coercions.

Establish `hbound : ∀ rs : List S, (∀ r ∈ rs, r ∈ maximalIdeal S) → IsWeaklyRegular S rs → rs.length ≤ d` using `fun rs hm hr => by have := hlen S rs hm hr; rw [← hlen0] at this; exact_mod_cast this`. Use `⟨d - e, ?_, ?_⟩` and prove the remaining obligations. Use `hup S (S ⧸ J) d d ms hserre hbound hmsm hmsreg` as an intermediate fact. Rewrite `this` using `[hmslen]`. Then use the resulting hypothesis. Rewrite using `[hh]; exact_mod_cast (by omega : d - e ≤ h)`.

Introduce and unpack `⟨ℓ, hpd, hℓ⟩`. Take `⟨ms, hmsm, hmsreg, hmslen⟩` from `hlow S (S ⧸ J) ℓ rs0 hpd hrs0m hrs0.toIsWeaklyRegular`. Establish `hℓh : ℓ ≤ h` using `by rw [hh] at hℓ; exact_mod_cast hℓ`. Establish `hle : e ≤ ms.length` using `by rw [hmslen]; omega`. Establish `hreg' : IsWeaklyRegular (S ⧸ J) (ms.take e)`.

Use `hmsreg` as an intermediate fact. Rewrite `this` using `[← List.take_append_drop e ms]`. Conclude with `((isWeaklyRegular_append_iff (S ⧸ J) _ _).mp this).1`. Use `{ exists_isWeaklyRegular := ⟨(ms.take e).map (algebraMap S (S ⧸ J)), ?_, ?_, ?_⟩ }` and prove the remaining obligations. Introduce `a ha`.

Take `⟨r, hr, rfl⟩` from `List.mem_map.mp ha`. Conclude with `quotient_mk_mem_maximalIdeal hJm (hmsm r (List.mem_of_mem_take hr))`. Conclude with `(isWeaklyRegular_map_algebraMap_iff (S ⧸ J) (S ⧸ J) _).mpr hreg'`. Rewrite using `[he, List.length_map, List.length_take, min_eq_left hle]`.
-/
theorem isCohenMacaulayLocalRing_quotient_iff_of_isRegularLocalRing
    (hlow : AuslanderBuchsbaumDepthLower.Statement.{0}) (hup : AuslanderBuchsbaumProjDimUpper.Statement.{0})
    (hlen : RegularSequenceLengthLeDim.Statement.{0}) (hcm : CMHeightAddDim.Statement.{0})
    {S : Type} [CommRing S] [IsRegularLocalRing S] (J : Ideal S) (hJm : J ≤ maximalIdeal S) :
    IsCohenMacaulayLocalRing (S ⧸ J) ↔
      ∃ ℓ : ℕ, HasProjectiveDimensionLE (ModuleCat.of S (S ⧸ J)) ℓ ∧ (ℓ : ℕ∞) ≤ J.height := by
  have hJ : J ≠ ⊤ := fun h => (maximalIdeal.isMaximal S).ne_top (top_le_iff.mp (h ▸ hJm))
  have : Nontrivial (S ⧸ J) := Ideal.Quotient.nontrivial_iff.mpr hJ
  have : IsLocalRing (S ⧸ J) := .of_surjective' _ Ideal.Quotient.mk_surjective
  obtain ⟨rs0, hrs0, hofl, hlen0⟩ := GroundTheory.Arith.SchemeCoh.exists_isRegular_ofList_eq_maximalIdeal (R := S)
  have hrs0m : ∀ r ∈ rs0, r ∈ maximalIdeal S := fun r hr => hofl ▸ Ideal.subset_span hr
  set d := rs0.length with hd_def
  have hcmS : IsCohenMacaulayLocalRing S :=
    { exists_isWeaklyRegular := ⟨rs0, hrs0m, hrs0.toIsWeaklyRegular, hlen0.symm⟩ }
  have hsum := hcm S J hJ
  rw [← hlen0] at hsum
  obtain ⟨e, he⟩ := exists_nat_eq_of_ne_bot_of_le (x := ringKrullDim (S ⧸ J)) (d := d)
    (ringKrullDim_ne_bot) (hlen0 ▸ ringKrullDim_quotient_le J)
  have hht : J.height ≠ ⊤ := by
    intro h
    rw [h, he] at hsum
    have h2 : ((⊤ : ℕ∞) + e : ℕ∞) = d := by exact_mod_cast hsum
    simp at h2
  obtain ⟨h, hh⟩ : ∃ h : ℕ, J.height = h := ⟨J.height.toNat, (ENat.natCast_toNat hht).symm⟩
  have hhe : h + e = d := by
    rw [hh, he] at hsum; exact_mod_cast hsum
  have hserre : HasProjectiveDimensionLE (ModuleCat.of S (S ⧸ J)) d :=
    GroundTheory.Arith.SchemeCoh.hasProjectiveDimensionLT_of_isRegularLocalRing hlen0.symm (S ⧸ J)
  constructor
  · intro hCM
    obtain ⟨as, has_m, has_reg, has_len⟩ := hCM.exists_isWeaklyRegular
    obtain ⟨ms, hms⟩ : ∃ ms : List S, ms.map (algebraMap S (S ⧸ J)) = as :=
      ⟨as.map fun a => (Ideal.Quotient.mk_surjective a).choose, by
        rw [List.map_map]; conv_rhs => rw [← List.map_id as]
        exact List.map_congr_left fun a _ => (Ideal.Quotient.mk_surjective a).choose_spec⟩
    have hmsreg : IsWeaklyRegular (S ⧸ J) ms := by
      rw [← isWeaklyRegular_map_algebraMap_iff (S ⧸ J) (S ⧸ J) ms, hms]; exact has_reg
    have hmsm : ∀ r ∈ ms, r ∈ maximalIdeal S := fun r hr =>
      mem_maximalIdeal_of_quotient_mk (has_m _ (hms ▸ List.mem_map_of_mem hr))
    have hmslen : ms.length = e := by
      have : (as.length : WithBot ℕ∞) = e := has_len.symm.trans he
      rw [← hms, List.length_map] at this; exact_mod_cast this
    have hbound : ∀ rs : List S, (∀ r ∈ rs, r ∈ maximalIdeal S) → IsWeaklyRegular S rs → rs.length ≤ d :=
      fun rs hm hr => by have := hlen S rs hm hr; rw [← hlen0] at this; exact_mod_cast this
    refine ⟨d - e, ?_, ?_⟩
    · have := hup S (S ⧸ J) d d ms hserre hbound hmsm hmsreg
      rwa [hmslen] at this
    · rw [hh]; exact_mod_cast (by omega : d - e ≤ h)
  · rintro ⟨ℓ, hpd, hℓ⟩
    obtain ⟨ms, hmsm, hmsreg, hmslen⟩ := hlow S (S ⧸ J) ℓ rs0 hpd hrs0m hrs0.toIsWeaklyRegular
    have hℓh : ℓ ≤ h := by rw [hh] at hℓ; exact_mod_cast hℓ
    have hle : e ≤ ms.length := by rw [hmslen]; omega
    have hreg' : IsWeaklyRegular (S ⧸ J) (ms.take e) := by
      have := hmsreg; rw [← List.take_append_drop e ms] at this
      exact ((isWeaklyRegular_append_iff (S ⧸ J) _ _).mp this).1
    refine { exists_isWeaklyRegular := ⟨(ms.take e).map (algebraMap S (S ⧸ J)), ?_, ?_, ?_⟩ }
    · intro a ha
      obtain ⟨r, hr, rfl⟩ := List.mem_map.mp ha
      exact quotient_mk_mem_maximalIdeal hJm (hmsm r (List.mem_of_mem_take hr))
    · exact (isWeaklyRegular_map_algebraMap_iff (S ⧸ J) (S ⧸ J) _).mpr hreg'
    · rw [he, List.length_map, List.length_take, min_eq_left hle]

/- English proof (translation)
Introduce `n I Q _ hIQ`. Establish `: Algebra.Smooth ℂ (MvPolynomial (Fin n) ℂ)` using `{}`. Establish `: IsRegularLocalRing (Localization.AtPrime Q)` using `GroundTheory.Arith.SchemeCoh.isRegularLocalRing_localization_of_smooth ℂ (MvPolynomial (Fin n) ℂ) Q`. Use `isCohenMacaulayLocalRing_quotient_iff_of_isRegularLocalRing hlow hup hlen hcm _ ?_` and prove the remaining obligations. Rewrite using `[← Localization.AtPrime.map_eq_maximalIdeal]`.

Conclude with `Ideal.map_mono hIQ`.
-/
theorem CMProjDimCriterion.proof (hlow : AuslanderBuchsbaumDepthLower.Statement.{0})
    (hup : AuslanderBuchsbaumProjDimUpper.Statement.{0}) (hlen : RegularSequenceLengthLeDim.Statement.{0})
    (hcm : CMHeightAddDim.Statement.{0}) : CMProjDimCriterion.Statement := by
  intro n I Q _ hIQ
  have : Algebra.Smooth ℂ (MvPolynomial (Fin n) ℂ) := {}
  have : IsRegularLocalRing (Localization.AtPrime Q) :=
    GroundTheory.Arith.SchemeCoh.isRegularLocalRing_localization_of_smooth ℂ (MvPolynomial (Fin n) ℂ) Q
  refine isCohenMacaulayLocalRing_quotient_iff_of_isRegularLocalRing hlow hup hlen hcm _ ?_
  rw [← Localization.AtPrime.map_eq_maximalIdeal]
  exact Ideal.map_mono hIQ

end GroundTheory.Heights₂.Heights

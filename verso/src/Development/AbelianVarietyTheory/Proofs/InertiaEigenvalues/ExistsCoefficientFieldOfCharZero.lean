import Mathlib
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.CohenStructureFiniteOverNormalCompleteSubring

open IsLocalRing

namespace GlobalTheory.CohenRegular

section Field
open Polynomial

/- English proof (translation)
Set `T : Set (Subring S)` to `{Λ | ∀ x ∈ Λ, x ∈ maximalIdeal S → x = 0}`. Establish `hbot : (⊥ : Subring S) ∈ T`. Introduce `x hx hm`. Take `⟨n, rfl⟩` from `Subring.mem_bot.1 hx`. Rewrite `hm` using `[← residue_eq_zero_iff, map_intCast, Int.cast_eq_zero]`.

Simplify using `[hm]`. Take `⟨Λ, -, hΛ⟩` from `zorn_le_nonempty₀ T (fun c hc hch y hy => by`. Use `⟨sSup c, fun x hx => ?_, fun z hz => le_sSup hz⟩` and prove the remaining obligations. Take `⟨K, hK, hxK⟩` from `(Subring.mem_sSup_of_directedOn ⟨y, hy⟩ hch.directedOn).1 hx`. Conclude with `hc hK x hxK) ⊥ hbot`.

Establish `hT : ∀ x ∈ Λ, x ∈ maximalIdeal S → x = 0` using `hΛ.prop`. Establish `hF : IsField Λ`. Use `⟨exists_pair_ne _, mul_comm, fun {x} hx => ?_⟩` and prove the remaining obligations. Establish `hu : IsUnit (x : S)`. Assume the negation of the conclusion as `h`.

Conclude with `hx (Subtype.ext (hT _ x.2 h))`. Set `Λ' : Subring S` to `{ carrier := {s | ∃ n : ℕ, (x : S) ^ n * s ∈ Λ} one_mem' := ⟨0, by simp⟩ zero_mem' := ⟨0, by simp⟩ mul_mem' := by`. Introduce and unpack `a b ⟨n, hn⟩ ⟨m, hm⟩`. Conclude with `⟨n + m, by convert Λ.mul_mem hn hm using 1; ring⟩`. Use the proof step `add_mem' := by`.

Introduce and unpack `a b ⟨n, hn⟩ ⟨m, hm⟩`. Conclude with `⟨n + m, by`. Use `Λ.add_mem (Λ.mul_mem (Λ.pow_mem x.2 m) hn) (Λ.mul_mem (Λ.pow_mem x.2 n) hm) using 1` and compare the differences between its conclusion and the goal. Use the proof step `ring⟩`. Use the proof step `neg_mem' := by`.

Introduce and unpack `a ⟨n, hn⟩`. Conclude with `⟨n, by convert Λ.neg_mem hn using 1; ring⟩ }`. Establish `h' : Λ' ∈ T`. Introduce and unpack `s ⟨n, hn⟩ hm`. Conclude with `(hu.pow n).mul_right_eq_zero.1 (hT _ hn (Ideal.mul_mem_left _ _ hm))`.

Establish `hle : Λ' ≤ Λ` using `hΛ.le_of_ge h' fun s hs => ⟨0, by simpa using hs⟩`. Take `⟨y, hy⟩` from `hu.exists_right_inv`. Conclude with `⟨⟨y, hle ⟨1, by rw [pow_one, hy]; exact Λ.one_mem⟩⟩, Subtype.ext hy⟩`. Use `⟨Λ, hF, fun s => ?_⟩` and prove the remaining obligations. Use `letI := hF.toField`.

Establish `key : ∀ a : S, (∀ f : Λ[X], aeval a f ∈ maximalIdeal S → aeval a f = 0) → a ∈ Λ` using `fun a ha => by`. Establish `h' : (aeval (R` using `Λ) a).toRingHom.range ∈ T := by`. Introduce and unpack `_ ⟨f, rfl⟩ hm`. Conclude with `ha f hm`. Conclude with `hΛ.le_of_ge h' (fun y hy => ⟨C ⟨y, hy⟩, by simp; rfl⟩) ⟨X, by simp⟩`.

Establish `hres : ∀ (a : S) (f : Λ[X]), residue S (aeval a f) = aeval (residue S a) f` using `fun a f => (aeval_algHom_apply (IsScalarTower.toAlgHom Λ S (ResidueField S)) a f).symm`. Distinguish the cases in `hs : IsAlgebraic Λ (residue S s)`. Establish `hi` using `hs.isIntegral haveI : CharZero Λ := RingHom.charZero (algebraMap Λ (ResidueField S))`. Establish `hsep : (minpoly Λ (residue S s)).Separable` using `(minpoly.irreducible hi).separable`. Take `⟨a, ha, has⟩` from `HenselianRing.is_henselian (I := maximalIdeal S) ((minpoly Λ (residue S s)).map (algebraMap Λ S)) ((minpoly.monic hi).map _) s (by rw [eval_map_algebraMap, ← residue_eq_zero_iff, hres, minpoly.aeval]) (by`.

Rewrite using `[derivative_map, eval_map_algebraMap]`. Use `hsep.aeval_derivative_ne_zero (minpoly.aeval Λ (residue S s))` as an intermediate fact. Rewrite `this` using `[← hres]`. Conclude with `(isUnit_iff_ne_zero (G₀ := ResidueField S)).2 this)`. Establish `e : residue S a = residue S s` using `by rw [← sub_eq_zero, ← map_sub, residue_eq_zero_iff]; exact has`.

Use `⟨a, key a fun f hf => ?_, by rw [← neg_sub]; exact neg_mem has⟩` and prove the remaining obligations. Rewrite `hf` using `[← residue_eq_zero_iff, hres, e]`. Take `⟨q, rfl⟩` from `minpoly.dvd _ _ hf`. Rewrite `ha` using `[IsRoot.def, eval_map_algebraMap]`. Rewrite using `[map_mul, ha, zero_mul]`.

Use `⟨s, key s fun f hf => ?_, by simp⟩` and prove the remaining obligations. Rewrite `hf` using `[← residue_eq_zero_iff, hres]`. Assume the negation of the conclusion as `h`. Conclude with `hs ⟨f, by rintro rfl; simp at h, hf⟩`.
-/
theorem exists_coefficientField_of_charZero (S : Type) [CommRing S] [IsLocalRing S] [IsAdicComplete (maximalIdeal S) S]
    [CharZero (ResidueField S)] :
    ∃ Λ : Subring S, IsField Λ ∧ ∀ s : S, ∃ a ∈ Λ, s - a ∈ maximalIdeal S := by
  let T : Set (Subring S) := {Λ | ∀ x ∈ Λ, x ∈ maximalIdeal S → x = 0}
  have hbot : (⊥ : Subring S) ∈ T := by
    intro x hx hm
    obtain ⟨n, rfl⟩ := Subring.mem_bot.1 hx
    rw [← residue_eq_zero_iff, map_intCast, Int.cast_eq_zero] at hm
    simp [hm]
  obtain ⟨Λ, -, hΛ⟩ := zorn_le_nonempty₀ T (fun c hc hch y hy => by
    refine ⟨sSup c, fun x hx => ?_, fun z hz => le_sSup hz⟩
    obtain ⟨K, hK, hxK⟩ := (Subring.mem_sSup_of_directedOn ⟨y, hy⟩ hch.directedOn).1 hx
    exact hc hK x hxK) ⊥ hbot
  have hT : ∀ x ∈ Λ, x ∈ maximalIdeal S → x = 0 := hΛ.prop
  have hF : IsField Λ := by
    refine ⟨exists_pair_ne _, mul_comm, fun {x} hx => ?_⟩
    have hu : IsUnit (x : S) := by
      by_contra h
      exact hx (Subtype.ext (hT _ x.2 h))
    let Λ' : Subring S :=
      { carrier := {s | ∃ n : ℕ, (x : S) ^ n * s ∈ Λ}
        one_mem' := ⟨0, by simp⟩
        zero_mem' := ⟨0, by simp⟩
        mul_mem' := by
          rintro a b ⟨n, hn⟩ ⟨m, hm⟩
          exact ⟨n + m, by convert Λ.mul_mem hn hm using 1; ring⟩
        add_mem' := by
          rintro a b ⟨n, hn⟩ ⟨m, hm⟩
          exact ⟨n + m, by
            convert Λ.add_mem (Λ.mul_mem (Λ.pow_mem x.2 m) hn) (Λ.mul_mem (Λ.pow_mem x.2 n) hm) using 1; ring⟩
        neg_mem' := by
          rintro a ⟨n, hn⟩
          exact ⟨n, by convert Λ.neg_mem hn using 1; ring⟩ }
    have h' : Λ' ∈ T := by
      rintro s ⟨n, hn⟩ hm
      exact (hu.pow n).mul_right_eq_zero.1 (hT _ hn (Ideal.mul_mem_left _ _ hm))
    have hle : Λ' ≤ Λ := hΛ.le_of_ge h' fun s hs => ⟨0, by simpa using hs⟩
    obtain ⟨y, hy⟩ := hu.exists_right_inv
    exact ⟨⟨y, hle ⟨1, by rw [pow_one, hy]; exact Λ.one_mem⟩⟩, Subtype.ext hy⟩
  refine ⟨Λ, hF, fun s => ?_⟩
  letI := hF.toField
  have key : ∀ a : S, (∀ f : Λ[X], aeval a f ∈ maximalIdeal S → aeval a f = 0) → a ∈ Λ := fun a ha => by
    have h' : (aeval (R := Λ) a).toRingHom.range ∈ T := by
      rintro _ ⟨f, rfl⟩ hm
      exact ha f hm
    exact hΛ.le_of_ge h' (fun y hy => ⟨C ⟨y, hy⟩, by simp; rfl⟩) ⟨X, by simp⟩
  have hres : ∀ (a : S) (f : Λ[X]), residue S (aeval a f) = aeval (residue S a) f := fun a f =>
    (aeval_algHom_apply (IsScalarTower.toAlgHom Λ S (ResidueField S)) a f).symm
  by_cases hs : IsAlgebraic Λ (residue S s)
  · have hi := hs.isIntegral
    haveI : CharZero Λ := RingHom.charZero (algebraMap Λ (ResidueField S))
    have hsep : (minpoly Λ (residue S s)).Separable := (minpoly.irreducible hi).separable
    obtain ⟨a, ha, has⟩ := HenselianRing.is_henselian (I := maximalIdeal S)
      ((minpoly Λ (residue S s)).map (algebraMap Λ S)) ((minpoly.monic hi).map _) s
      (by rw [eval_map_algebraMap, ← residue_eq_zero_iff, hres, minpoly.aeval])
      (by
        rw [derivative_map, eval_map_algebraMap]
        have := hsep.aeval_derivative_ne_zero (minpoly.aeval Λ (residue S s))
        rw [← hres] at this
        exact (isUnit_iff_ne_zero (G₀ := ResidueField S)).2 this)
    have e : residue S a = residue S s := by rw [← sub_eq_zero, ← map_sub, residue_eq_zero_iff]; exact has
    refine ⟨a, key a fun f hf => ?_, by rw [← neg_sub]; exact neg_mem has⟩
    rw [← residue_eq_zero_iff, hres, e] at hf
    obtain ⟨q, rfl⟩ := minpoly.dvd _ _ hf
    rw [IsRoot.def, eval_map_algebraMap] at ha
    rw [map_mul, ha, zero_mul]
  · refine ⟨s, key s fun f hf => ?_, by simp⟩
    rw [← residue_eq_zero_iff, hres] at hf
    by_contra h
    exact hs ⟨f, by rintro rfl; simp at h, hf⟩

end Field

/- English proof (translation)
Establish `h0 : (p : S) ∈ maximalIdeal S` using `by rw [hp0]; exact zero_mem _`. Take `⟨B, hB, hB'⟩` from `GlobalTheory.PBasis.exists_pBasis (ResidueField S) p hp (by rw [← map_natCast (residue S), residue_eq_zero_iff]; exact h0)`. Use `choose l hl using residue_surjective (R := S)`. Establish `hL : residue S '' (l '' B) = B` using `by simp [Set.image_image, hl]`. Establish `hinj : Set.InjOn (residue S) (l '' B)`.

Introduce and unpack `_ ⟨x, -, rfl⟩ _ ⟨y, -, rfl⟩ h`. Rewrite `h` using `[hl, hl]`. Rewrite using `[h]`. Rewrite `hB`, `hB'` using `[← hL]`. Establish `hs` using `CoeffSubring.exists_level_sub_mem hp h0 hB`.

Establish `h1` using `CoeffSubring.exists_iInf_sub_mem h0 hs`. Use `set Λ : Subring S := ⨅ n, CoeffSubring.level p (l '' B) n`. Establish `h2 : ∀ a ∈ Λ, a ∈ maximalIdeal S → a = 0` using `fun a ha hm => by`. Rewrite using `[← zero_dvd_iff, ← hp0]`. Use `CoeffSubring.dvd_of_forall_sub_mul_mem fun n => ?_` and prove the remaining obligations.

Take `⟨t, -, ht⟩` from `CoeffSubring.exists_sub_mul_mem hp h0 hinj hB' hs n (Subring.mem_iInf.1 ha n) hm`. Conclude with `⟨t, Ideal.pow_le_pow_right n.le_succ ht⟩`. Use `⟨Λ, ⟨exists_pair_ne _, mul_comm, fun {x} hx => ?_⟩, h1⟩` and prove the remaining obligations. Establish `hu : IsUnit (x : S)`. Assume the negation of the conclusion as `h`.

Conclude with `hx (Subtype.ext (h2 _ x.2 h))`. Take `⟨y, hy⟩` from `hu.exists_right_inv`. Take `⟨a, ha, hya⟩` from `h1 y`. Use `⟨⟨a, ha⟩, Subtype.ext (sub_eq_zero.1 (h2 _ (Λ.sub_mem (Λ.mul_mem x.2 ha) Λ.one_mem) ?_))⟩` and prove the remaining obligations. Establish `: (x : S) * a - 1 = -x * (y - a)` using `by rw [← hy]; ring`.

Use `show (x : S) * a - 1 ∈ _`. Rewrite using `[this]`. Conclude with `Ideal.mul_mem_left _ _ hya`.
-/
theorem exists_coefficientField_of_prime (S : Type) [CommRing S] [IsLocalRing S] [IsNoetherianRing S]
    [IsAdicComplete (maximalIdeal S) S] {p : ℕ} (hp : p.Prime) (hp0 : (p : S) = 0) :
    ∃ Λ : Subring S, IsField Λ ∧ ∀ s : S, ∃ a ∈ Λ, s - a ∈ maximalIdeal S := by
  have h0 : (p : S) ∈ maximalIdeal S := by rw [hp0]; exact zero_mem _
  obtain ⟨B, hB, hB'⟩ := GlobalTheory.PBasis.exists_pBasis (ResidueField S) p hp
    (by rw [← map_natCast (residue S), residue_eq_zero_iff]; exact h0)
  choose l hl using residue_surjective (R := S)
  have hL : residue S '' (l '' B) = B := by simp [Set.image_image, hl]
  have hinj : Set.InjOn (residue S) (l '' B) := by
    rintro _ ⟨x, -, rfl⟩ _ ⟨y, -, rfl⟩ h
    rw [hl, hl] at h
    rw [h]
  rw [← hL] at hB hB'
  have hs := CoeffSubring.exists_level_sub_mem hp h0 hB
  have h1 := CoeffSubring.exists_iInf_sub_mem h0 hs
  set Λ : Subring S := ⨅ n, CoeffSubring.level p (l '' B) n
  have h2 : ∀ a ∈ Λ, a ∈ maximalIdeal S → a = 0 := fun a ha hm => by
    rw [← zero_dvd_iff, ← hp0]
    refine CoeffSubring.dvd_of_forall_sub_mul_mem fun n => ?_
    obtain ⟨t, -, ht⟩ :=
      CoeffSubring.exists_sub_mul_mem hp h0 hinj hB' hs n (Subring.mem_iInf.1 ha n) hm
    exact ⟨t, Ideal.pow_le_pow_right n.le_succ ht⟩
  refine ⟨Λ, ⟨exists_pair_ne _, mul_comm, fun {x} hx => ?_⟩, h1⟩
  have hu : IsUnit (x : S) := by
    by_contra h
    exact hx (Subtype.ext (h2 _ x.2 h))
  obtain ⟨y, hy⟩ := hu.exists_right_inv
  obtain ⟨a, ha, hya⟩ := h1 y
  refine ⟨⟨a, ha⟩, Subtype.ext (sub_eq_zero.1 (h2 _ (Λ.sub_mem (Λ.mul_mem x.2 ha) Λ.one_mem) ?_))⟩
  have : (x : S) * a - 1 = -x * (y - a) := by rw [← hy]; ring
  show (x : S) * a - 1 ∈ _
  rw [this]
  exact Ideal.mul_mem_left _ _ hya

open MvPowerSeries GlobalTheory.CohenStructure

/- English proof (translation)
Distinguish the cases in `hm : maximalIdeal S = ⊥`. Use `letI := (isField_iff_maximalIdeal_eq.2 hm).toField`. Conclude with `⟨S, inferInstance, inferInstance, RingHom.id S, Function.injective_id, RingHom.Finite.id S⟩`. Take `⟨a, ha, ha0⟩` from `Submodule.exists_mem_ne_zero_of_ne_bot hm`. Use `letI := hF.toField`.

Take `⟨n, x₀, hx₀, hd, N, hN⟩` from `GlobalTheory.exists_systemOfParameters_insert S a ha0 ha`. Set `x : Fin (n + 1) → S` to `Fin.cons a x₀`. Establish `hx : ∀ i, x i ∈ maximalIdeal S` using `fun i => Fin.cases ha hx₀ i`. Set `A` to `MvPowerSeries (Fin (n + 1)) Λ`. Set `φ : A →ₐ[Λ] S` to `mvEvalAdic Λ (maximalIdeal S) x hx`.

Use `letI : Algebra A S := φ.toRingHom.toAlgebra`. Establish `: IsDomain A` using `isDomain_mvPowerSeries Λ (n + 1)`. Establish `hb : maximalIdeal Λ = ⊥` using `isField_iff_maximalIdeal_eq.1 hF`. Establish `: IsAdicComplete (maximalIdeal Λ) Λ` using `by rw [hb]; infer_instance`. Establish `hA` using `isAdicComplete_mvPowerSeries Λ (n + 1)`.

Establish `hle : (maximalIdeal A).map (algebraMap A S) ≤ maximalIdeal S`. Use `Ideal.map_le_iff_le_comap.2 fun g hg => ?_` and prove the remaining obligations. Establish `h4` using `algHom_sub_constantCoeff_mem φ (K := maximalIdeal S) (fun j => by simpa [φ] using hx j) g`. Establish `h5` using `FormalIsogeny.mem_maximalIdeal_iff_constantCoeff.1 hg`. Rewrite `h5` using `[hb, Ideal.mem_bot]`.

Rewrite `h4` using `[h5, map_zero, sub_zero]`. Then use the resulting hypothesis. Establish `hge : maximalIdeal S ^ N ≤ (maximalIdeal A).map (algebraMap A S)`. Use `hN.trans (Ideal.span_le.2 ?_)` and prove the remaining obligations. Rewrite using `[← Fin.range_cons]`. Introduce and unpack `_ ⟨i, rfl⟩`.

Use `show x i ∈ _`. Rewrite using `[← mvEvalAdic_X (A := Λ) (maximalIdeal S) x hx i]`. Conclude with `Ideal.mem_map_of_mem (algebraMap A S) (FormalIsogeny.mem_maximalIdeal_iff_constantCoeff.2 (by simp))`. Establish `: IsHausdorff ((maximalIdeal A).map (algebraMap A S)) S` using `IsHausdorff.of_isLocalRing _ _ (ne_top_of_le_ne_top (maximalIdeal.isMaximal _).ne_top hle)`. Establish `: Module.Finite A (S ⧸ (maximalIdeal A).map (algebraMap A S))`.

Use `finite_quotient_of_pow_le (fun s => ?_) hge` and prove the remaining obligations. Take `⟨a, ha, h⟩` from `h1 s`. Use `⟨C ⟨a, ha⟩, ?_⟩` and prove the remaining obligations. Rewrite using `[show algebraMap A S (C ⟨a, ha⟩) = a from mvEvalAdic_C _ x hx _]` and apply the resulting hypothesis. Establish `hfin : Module.Finite A S` using `FormalIsogeny.finite_of_finite_quotient_map (maximalIdeal A)`.

Use `⟨A, inferInstance, FormalIsogeny.isRegularLocalRing_mvPowerSeries Λ (Fin (n + 1)), algebraMap A S, injective_of_ringKrullDim_eq (n := n + 1) ?_ (by rw [hd]; norm_cast), hfin⟩` and prove the remaining obligations. Rewrite using `[FormalIsogeny.ringKrullDim_mvPowerSeries, ringKrullDim_eq_zero_of_isField hF, Nat.card_eq_fintype_card, Fintype.card_fin, zero_add]`.
-/
theorem exists_of_coefficientField (S : Type) [CommRing S] [IsDomain S] [IsLocalRing S]
    [IsNoetherianRing S] [hc : IsAdicComplete (maximalIdeal S) S] (Λ : Subring S) (hF : IsField Λ)
    (h1 : ∀ s : S, ∃ a ∈ Λ, s - a ∈ maximalIdeal S) :
    ∃ (A : Type) (_ : CommRing A) (_ : IsRegularLocalRing A) (i : A →+* S),
      Function.Injective i ∧ i.Finite := by
  by_cases hm : maximalIdeal S = ⊥
  · letI := (isField_iff_maximalIdeal_eq.2 hm).toField
    exact ⟨S, inferInstance, inferInstance, RingHom.id S, Function.injective_id, RingHom.Finite.id S⟩
  obtain ⟨a, ha, ha0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hm
  letI := hF.toField
  obtain ⟨n, x₀, hx₀, hd, N, hN⟩ := GlobalTheory.exists_systemOfParameters_insert S a ha0 ha
  let x : Fin (n + 1) → S := Fin.cons a x₀
  have hx : ∀ i, x i ∈ maximalIdeal S := fun i => Fin.cases ha hx₀ i
  let A := MvPowerSeries (Fin (n + 1)) Λ
  let φ : A →ₐ[Λ] S := mvEvalAdic Λ (maximalIdeal S) x hx
  letI : Algebra A S := φ.toRingHom.toAlgebra
  have : IsDomain A := isDomain_mvPowerSeries Λ (n + 1)
  have hb : maximalIdeal Λ = ⊥ := isField_iff_maximalIdeal_eq.1 hF
  have : IsAdicComplete (maximalIdeal Λ) Λ := by rw [hb]; infer_instance
  have hA := isAdicComplete_mvPowerSeries Λ (n + 1)
  have hle : (maximalIdeal A).map (algebraMap A S) ≤ maximalIdeal S := by
    refine Ideal.map_le_iff_le_comap.2 fun g hg => ?_
    have h4 := algHom_sub_constantCoeff_mem φ (K := maximalIdeal S)
      (fun j => by simpa [φ] using hx j) g
    have h5 := FormalIsogeny.mem_maximalIdeal_iff_constantCoeff.1 hg
    rw [hb, Ideal.mem_bot] at h5
    rwa [h5, map_zero, sub_zero] at h4
  have hge : maximalIdeal S ^ N ≤ (maximalIdeal A).map (algebraMap A S) := by
    refine hN.trans (Ideal.span_le.2 ?_)
    rw [← Fin.range_cons]
    rintro _ ⟨i, rfl⟩
    show x i ∈ _
    rw [← mvEvalAdic_X (A := Λ) (maximalIdeal S) x hx i]
    exact Ideal.mem_map_of_mem (algebraMap A S)
      (FormalIsogeny.mem_maximalIdeal_iff_constantCoeff.2 (by simp))
  have : IsHausdorff ((maximalIdeal A).map (algebraMap A S)) S :=
    IsHausdorff.of_isLocalRing _ _ (ne_top_of_le_ne_top (maximalIdeal.isMaximal _).ne_top hle)
  have : Module.Finite A (S ⧸ (maximalIdeal A).map (algebraMap A S)) := by
    refine finite_quotient_of_pow_le (fun s => ?_) hge
    obtain ⟨a, ha, h⟩ := h1 s
    refine ⟨C ⟨a, ha⟩, ?_⟩
    rwa [show algebraMap A S (C ⟨a, ha⟩) = a from mvEvalAdic_C _ x hx _]
  have hfin : Module.Finite A S := FormalIsogeny.finite_of_finite_quotient_map (maximalIdeal A)
  refine ⟨A, inferInstance, FormalIsogeny.isRegularLocalRing_mvPowerSeries Λ (Fin (n + 1)),
    algebraMap A S, injective_of_ringKrullDim_eq (n := n + 1) ?_ (by rw [hd]; norm_cast), hfin⟩
  rw [FormalIsogeny.ringKrullDim_mvPowerSeries, ringKrullDim_eq_zero_of_isField hF,
    Nat.card_eq_fintype_card, Fintype.card_fin, zero_add]

/- English proof (translation)
Take `⟨B, hB, hB'⟩` from `GlobalTheory.PBasis.exists_pBasis (ResidueField S) p hp (by rw [← map_natCast (residue S), residue_eq_zero_iff]; exact h0)`. Take `⟨Λ, h1, h2, h3⟩` from `CoeffSubring.exists_coeffSubring hp hp0 h0 hB hB'`. Take `⟨_, hm, hΛ⟩` from `GlobalTheory.isDVR_of_closed_subring_principal S Λ p (by simpa using hp0) (by simpa using h0) hc h1 h2 h3`. Take `⟨n, x, hx, hd, N, hN⟩` from `GlobalTheory.exists_systemOfParameters_insert S p hp0 h0`. Set `A` to `MvPowerSeries (Fin n) Λ`.

Set `φ : A →ₐ[Λ] S` to `mvEvalAdic Λ (maximalIdeal S) x hx`. Use `letI : Algebra A S := φ.toRingHom.toAlgebra`. Establish `: IsDomain A` using `isDomain_mvPowerSeries Λ n`. Establish `hA` using `isAdicComplete_mvPowerSeries Λ n`. Establish `hle : (maximalIdeal A).map (algebraMap A S) ≤ maximalIdeal S`.

Use `Ideal.map_le_iff_le_comap.2 fun g hg => ?_` and prove the remaining obligations. Establish `h4` using `algHom_sub_constantCoeff_mem φ (K := maximalIdeal S) (fun j => by simpa [φ] using hx j) g`. Establish `h5` using `FormalIsogeny.mem_maximalIdeal_iff_constantCoeff.1 hg`. Rewrite `h5` using `[hm, Ideal.mem_span_singleton]`. Take `⟨c, hc⟩` from `h5`.

Establish `h6 : algebraMap Λ S (constantCoeff g) ∈ maximalIdeal S`. Rewrite using `[hc, map_mul, map_natCast]`. Conclude with `Ideal.mul_mem_right _ _ h0`. Establish `h7` using `add_mem h4 h6`. Rewrite `h7` using `[sub_add_cancel]`. Then use the resulting hypothesis.

Establish `hge : maximalIdeal S ^ N ≤ (maximalIdeal A).map (algebraMap A S)`. Use `hN.trans (Ideal.span_le.2 ?_)` and prove the remaining obligations. Introduce and unpack `_ (rfl | ⟨i, rfl⟩)`. Rewrite using `[← map_natCast (algebraMap A S)]`. Use `Ideal.mem_map_of_mem _ (FormalIsogeny.mem_maximalIdeal_iff_constantCoeff.2 ?_)` and prove the remaining obligations.

Rewrite using `[map_natCast, hm]`. Conclude with `Ideal.mem_span_singleton_self _`. Rewrite using `[← mvEvalAdic_X (A := Λ) (maximalIdeal S) x hx i]`. Conclude with `Ideal.mem_map_of_mem (algebraMap A S) (FormalIsogeny.mem_maximalIdeal_iff_constantCoeff.2 (by simp))`. Establish `: IsHausdorff ((maximalIdeal A).map (algebraMap A S)) S` using `IsHausdorff.of_isLocalRing _ _ (ne_top_of_le_ne_top (maximalIdeal.isMaximal _).ne_top hle)`.

Establish `: Module.Finite A (S ⧸ (maximalIdeal A).map (algebraMap A S))`. Use `finite_quotient_of_pow_le (fun s => ?_) hge` and prove the remaining obligations. Take `⟨a, ha, h⟩` from `h1 s`. Use `⟨C ⟨a, ha⟩, ?_⟩` and prove the remaining obligations. Rewrite using `[show algebraMap A S (C ⟨a, ha⟩) = a from mvEvalAdic_C _ x hx _]` and apply the resulting hypothesis.

Establish `hfin : Module.Finite A S` using `FormalIsogeny.finite_of_finite_quotient_map (maximalIdeal A)`. Use `⟨A, inferInstance, FormalIsogeny.isRegularLocalRing_mvPowerSeries Λ (Fin n), algebraMap A S, injective_of_ringKrullDim_eq (n := n + 1) ?_ (by rw [hd]; norm_cast), hfin⟩` and prove the remaining obligations. Rewrite using `[FormalIsogeny.ringKrullDim_mvPowerSeries, IsDiscreteValuationRing.ringKrullDim_eq_one, Nat.card_eq_fintype_card, Fintype.card_fin, add_comm]`. Use `norm_cast`.
-/
theorem exists_of_mixed (S : Type) [CommRing S] [IsDomain S] [IsLocalRing S]
    [IsNoetherianRing S] [hc : IsAdicComplete (maximalIdeal S) S] {p : ℕ} (hp : p.Prime)
    (h0 : (p : S) ∈ maximalIdeal S) (hp0 : (p : S) ≠ 0) :
    ∃ (A : Type) (_ : CommRing A) (_ : IsRegularLocalRing A) (i : A →+* S),
      Function.Injective i ∧ i.Finite := by
  obtain ⟨B, hB, hB'⟩ := GlobalTheory.PBasis.exists_pBasis (ResidueField S) p hp
    (by rw [← map_natCast (residue S), residue_eq_zero_iff]; exact h0)
  obtain ⟨Λ, h1, h2, h3⟩ := CoeffSubring.exists_coeffSubring hp hp0 h0 hB hB'
  obtain ⟨_, hm, hΛ⟩ := GlobalTheory.isDVR_of_closed_subring_principal S Λ p (by simpa using hp0) (by simpa using h0) hc h1 h2 h3
  obtain ⟨n, x, hx, hd, N, hN⟩ := GlobalTheory.exists_systemOfParameters_insert S p hp0 h0
  let A := MvPowerSeries (Fin n) Λ
  let φ : A →ₐ[Λ] S := mvEvalAdic Λ (maximalIdeal S) x hx
  letI : Algebra A S := φ.toRingHom.toAlgebra
  have : IsDomain A := isDomain_mvPowerSeries Λ n
  have hA := isAdicComplete_mvPowerSeries Λ n
  have hle : (maximalIdeal A).map (algebraMap A S) ≤ maximalIdeal S := by
    refine Ideal.map_le_iff_le_comap.2 fun g hg => ?_
    have h4 := algHom_sub_constantCoeff_mem φ (K := maximalIdeal S)
      (fun j => by simpa [φ] using hx j) g
    have h5 := FormalIsogeny.mem_maximalIdeal_iff_constantCoeff.1 hg
    rw [hm, Ideal.mem_span_singleton] at h5
    obtain ⟨c, hc⟩ := h5
    have h6 : algebraMap Λ S (constantCoeff g) ∈ maximalIdeal S := by
      rw [hc, map_mul, map_natCast]
      exact Ideal.mul_mem_right _ _ h0
    have h7 := add_mem h4 h6
    rwa [sub_add_cancel] at h7
  have hge : maximalIdeal S ^ N ≤ (maximalIdeal A).map (algebraMap A S) := by
    refine hN.trans (Ideal.span_le.2 ?_)
    rintro _ (rfl | ⟨i, rfl⟩)
    · rw [← map_natCast (algebraMap A S)]
      refine Ideal.mem_map_of_mem _ (FormalIsogeny.mem_maximalIdeal_iff_constantCoeff.2 ?_)
      rw [map_natCast, hm]
      exact Ideal.mem_span_singleton_self _
    · rw [← mvEvalAdic_X (A := Λ) (maximalIdeal S) x hx i]
      exact Ideal.mem_map_of_mem (algebraMap A S)
        (FormalIsogeny.mem_maximalIdeal_iff_constantCoeff.2 (by simp))
  have : IsHausdorff ((maximalIdeal A).map (algebraMap A S)) S :=
    IsHausdorff.of_isLocalRing _ _ (ne_top_of_le_ne_top (maximalIdeal.isMaximal _).ne_top hle)
  have : Module.Finite A (S ⧸ (maximalIdeal A).map (algebraMap A S)) := by
    refine finite_quotient_of_pow_le (fun s => ?_) hge
    obtain ⟨a, ha, h⟩ := h1 s
    refine ⟨C ⟨a, ha⟩, ?_⟩
    rwa [show algebraMap A S (C ⟨a, ha⟩) = a from mvEvalAdic_C _ x hx _]
  have hfin : Module.Finite A S := FormalIsogeny.finite_of_finite_quotient_map (maximalIdeal A)
  refine ⟨A, inferInstance, FormalIsogeny.isRegularLocalRing_mvPowerSeries Λ (Fin n),
    algebraMap A S, injective_of_ringKrullDim_eq (n := n + 1) ?_ (by rw [hd]; norm_cast), hfin⟩
  rw [FormalIsogeny.ringKrullDim_mvPowerSeries, IsDiscreteValuationRing.ringKrullDim_eq_one,
    Nat.card_eq_fintype_card, Fintype.card_fin, add_comm]
  norm_cast

/- English proof (translation)
Introduce `S _ _ _ _ _`. Take `⟨p, hp⟩` from `CharP.exists (ResidueField S)`. Break down `CharP.char_is_prime_or_zero (ResidueField S) p with h | rfl` into its components or cases. Distinguish the cases in `hp0 : (p : S) = 0`. Take `⟨Λ, hF, h1⟩` from `exists_coefficientField_of_prime S h hp0`.

Conclude with `exists_of_coefficientField S Λ hF h1`. Conclude with `exists_of_mixed S h (by rw [← residue_eq_zero_iff, map_natCast]; exact CharP.cast_eq_zero _ p) hp0`. Use `haveI := CharP.charP_to_charZero (ResidueField S)`. Take `⟨Λ, hF, h1⟩` from `exists_coefficientField_of_charZero S`. Conclude with `exists_of_coefficientField S Λ hF h1`.
-/
theorem exists_finite_over_regular :
    ∀ (S : Type) [CommRing S] [IsDomain S] [IsLocalRing S] [IsNoetherianRing S]
      [IsAdicComplete (IsLocalRing.maximalIdeal S) S],
      ∃ (A : Type) (_ : CommRing A) (_ : IsRegularLocalRing A) (i : A →+* S),
        Function.Injective i ∧ i.Finite := by
  intro S _ _ _ _ _
  obtain ⟨p, hp⟩ := CharP.exists (ResidueField S)
  rcases CharP.char_is_prime_or_zero (ResidueField S) p with h | rfl
  · by_cases hp0 : (p : S) = 0
    · obtain ⟨Λ, hF, h1⟩ := exists_coefficientField_of_prime S h hp0
      exact exists_of_coefficientField S Λ hF h1
    · exact exists_of_mixed S h
        (by rw [← residue_eq_zero_iff, map_natCast]; exact CharP.cast_eq_zero _ p) hp0
  · haveI := CharP.charP_to_charZero (ResidueField S)
    obtain ⟨Λ, hF, h1⟩ := exists_coefficientField_of_charZero S
    exact exists_of_coefficientField S Λ hF h1

end GlobalTheory.CohenRegular

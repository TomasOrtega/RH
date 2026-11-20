import Mathlib
import Formalism.PairingDivisors.StatementA
import Development.AbelianVarietyTheory.Definitions.Divisors.IsFinSetSplitPlacesCoprimeConductor
import Formalism.LocalToGlobal.UnitaryNorms.CharTransport
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsWeakApproxUnitFinitePlace
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HeckeCharacterUnramifiedAeAndExistsLevel

open NumberField IsDedekindDomain GlobalTheory.CMVal

noncomputable section

namespace GlobalTheory.CMVal.InvConj

open Formalism.L2.Host Formalism.L2.Host.CT

variable {E : Type} [Field E] [NumberField E]

/- English proof (translation)
Use `choose n hn using fun P => GlobalTheory.Mem.UnrAe.exists_levelLe ψ P`. Take `⟨y, hy0, hyw, hyv⟩` from `GlobalTheory.HkFin.exists_weak_approx_unit E S w x (S.sup n + 1)`. Establish `lev : ∀ P ∈ S, ∀ z : (P.adicCompletion E)ˣ, Valued.v ((z : P.adicCompletion E) - 1) ≤ WithZero.exp (-((S.sup n + 1 : ℕ) : ℤ)) → ψ.loc P z = 1`. Introduce `P hP z hz`. Establish `h1 : Valued.v ((z : P.adicCompletion E) - 1) < Valued.v (1 : P.adicCompletion E)`.

Rewrite using `[map_one]`. Use `lt_of_le_of_lt hz ?_` and prove the remaining obligations. Rewrite using `[← WithZero.exp_zero, WithZero.exp_lt_exp]`. Use linear arithmetic over natural numbers and integers. Establish `hu : IsUnitAt P z`.

Unfold `IsUnitAt`. Establish `e : (z : P.adicCompletion E) = ((z : P.adicCompletion E) - 1) + 1` using `by ring`. Rewrite using `[e, Valuation.map_add_eq_of_lt_right _ h1, map_one]`. Use `hn P z hu (hz.trans ?_)` and prove the remaining obligations. Rewrite using `[WithZero.exp_le_exp]`.

Establish `: n P ≤ S.sup n` using `Finset.le_sup hP`. Use linear arithmetic over natural numbers and integers. Establish `hS` using `h (Units.mk0 y hy0)`. Rewrite `hS` using `[← Finset.mul_prod_erase S _ hw, Finset.prod_eq_one (fun P hP => ?_), mul_one]`. Establish `e : ψ.loc w x = ψ.locK w (Units.mk0 y hy0) * (ψ.loc w (atFin w (Units.mk0 y hy0) * x⁻¹))⁻¹`.

Rewrite using `[map_mul, map_inv, mul_inv, inv_inv, ← mul_assoc]`. Simplify using `[HChar.locK]`. Establish `h2 : ψ.loc w (atFin w (Units.mk0 y hy0) * x⁻¹) = 1` using `lev w hw _ (by`. Use `hyw` as an intermediate fact. Conclude with `this)`.

Rewrite using `[e, hS, h2, inv_one, mul_one]`. Take `⟨hPw, hPS⟩` from `Finset.mem_erase.1 hP`. Use `lev P hPS _ ?_` and prove the remaining obligations. Establish `h3` using `hyv P hPS hPw`. Use `show Valued.v (algebraMap E (P.adicCompletion E) y - 1) ≤ _`.

Rewrite using `[← map_one (algebraMap E (P.adicCompletion E)), ← map_sub]`. Use `first`. Consider the case `exact (HeightOneSpectrum.valuedAdicCompletion_eq_valuation' P (y - 1)).trans_le h3`. Consider the case `(rw [HeightOneSpectrum.valuedAdicCompletion_eq_valuation]; exact h3)`.
-/
theorem loc_eq_one_of_prod (ψ : HChar E) (S : Finset (HeightOneSpectrum (𝓞 E)))
    (h : ∀ k : Eˣ, ∏ P ∈ S, ψ.locK P k = 1) {w : HeightOneSpectrum (𝓞 E)} (hw : w ∈ S)
    (x : (w.adicCompletion E)ˣ) : ψ.loc w x = 1 := by
  classical
  choose n hn using fun P => GlobalTheory.Mem.UnrAe.exists_levelLe ψ P
  obtain ⟨y, hy0, hyw, hyv⟩ := GlobalTheory.HkFin.exists_weak_approx_unit E S w x (S.sup n + 1)
  have lev : ∀ P ∈ S, ∀ z : (P.adicCompletion E)ˣ,
      Valued.v ((z : P.adicCompletion E) - 1) ≤ WithZero.exp (-((S.sup n + 1 : ℕ) : ℤ)) → ψ.loc P z = 1 := by
    intro P hP z hz
    have h1 : Valued.v ((z : P.adicCompletion E) - 1) < Valued.v (1 : P.adicCompletion E) := by
      rw [map_one]
      refine lt_of_le_of_lt hz ?_
      rw [← WithZero.exp_zero, WithZero.exp_lt_exp]; omega
    have hu : IsUnitAt P z := by
      unfold IsUnitAt
      have e : (z : P.adicCompletion E) = ((z : P.adicCompletion E) - 1) + 1 := by ring
      rw [e, Valuation.map_add_eq_of_lt_right _ h1, map_one]
    refine hn P z hu (hz.trans ?_)
    rw [WithZero.exp_le_exp]
    have : n P ≤ S.sup n := Finset.le_sup hP
    omega
  have hS := h (Units.mk0 y hy0)
  rw [← Finset.mul_prod_erase S _ hw, Finset.prod_eq_one (fun P hP => ?_), mul_one] at hS
  · have e : ψ.loc w x = ψ.locK w (Units.mk0 y hy0) * (ψ.loc w (atFin w (Units.mk0 y hy0) * x⁻¹))⁻¹ := by
      rw [map_mul, map_inv, mul_inv, inv_inv, ← mul_assoc]; simp [HChar.locK]
    have h2 : ψ.loc w (atFin w (Units.mk0 y hy0) * x⁻¹) = 1 := lev w hw _ (by
      have := hyw
      exact this)
    rw [e, hS, h2, inv_one, mul_one]
  · obtain ⟨hPw, hPS⟩ := Finset.mem_erase.1 hP
    refine lev P hPS _ ?_
    have h3 := hyv P hPS hPw
    show Valued.v (algebraMap E (P.adicCompletion E) y - 1) ≤ _
    rw [← map_one (algebraMap E (P.adicCompletion E)), ← map_sub]
    first
      | exact (HeightOneSpectrum.valuedAdicCompletion_eq_valuation' P (y - 1)).trans_le h3
      | (rw [HeightOneSpectrum.valuedAdicCompletion_eq_valuation]; exact h3)

end GlobalTheory.CMVal.InvConj

namespace GlobalTheory.CMVal.InvConj

open Formalism.L2.Host Formalism.L2.Host.CT

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

abbrev conjE : E ≃+* E := (IsCMField.complexConj E).toRingEquiv

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem conjE_apply (x : E) : conjE x = IsCMField.complexConj E x := rfl

/- English proof (translation)
Rewrite using `[RingEquiv.symm_apply_eq, conjE_apply, IsCMField.complexConj_apply_apply]`.
-/
theorem conjE_symm_apply (x : E) : (conjE (E := E)).symm x = IsCMField.complexConj E x := by
  rw [RingEquiv.symm_apply_eq, conjE_apply, IsCMField.complexConj_apply_apply]

/- English proof (translation)
Use extensionality with `a`. Establish `e : RingOfIntegers.mapRingEquiv j (algebraMap (OF E) (𝓞 E) a) = algebraMap (OF E) (𝓞 E) a` using `RingOfIntegers.ext (hj (a : maximalRealSubfield E))`. Use `show algebraMap (OF E) (𝓞 E) a ∈ (plMap j P).asIdeal ↔ algebraMap (OF E) (𝓞 E) a ∈ P.asIdeal`. Rewrite using `[← mem_plMap j P, e]`.
-/
theorem under_plMap (j : E ≃+* E) (hj : ∀ x : maximalRealSubfield E, j (x : E) = x) (P : HeightOneSpectrum (𝓞 E)) :
    (plMap j P).under (OF E) = P.under (OF E) := by
  ext a
  have e : RingOfIntegers.mapRingEquiv j (algebraMap (OF E) (𝓞 E) a) = algebraMap (OF E) (𝓞 E) a :=
    RingOfIntegers.ext (hj (a : maximalRealSubfield E))
  show algebraMap (OF E) (𝓞 E) a ∈ (plMap j P).asIdeal ↔ algebraMap (OF E) (𝓞 E) a ∈ P.asIdeal
  rw [← mem_plMap j P, e]

/- English proof (translation)
Unfold `aboveF`. Rewrite using `[Set.Finite.mem_toFinset]`. Both sides reduce to the same expression.
-/
theorem mem_aboveF (v : HeightOneSpectrum (OF E)) (P : HeightOneSpectrum (𝓞 E)) :
    P ∈ aboveF (L := E) (maximalRealSubfield E) v ↔ P.under (OF E) = v := by
  unfold aboveF
  rw [Set.Finite.mem_toFinset]
  rfl

/- English proof (translation)
Establish `h1 : ∀ P, (χ * transport conjE χ).locK P k = χ.locK P k * (transport conjE χ).locK P k` using `fun P => rfl`. Establish `hs : ∀ x : maximalRealSubfield E, (conjE (E` using `E)).symm (x : E) = x := fun x => by`. Rewrite using `[conjE_symm_apply]`. Conclude with `IsCMField.complexConj_apply_eq_self E x`. Establish `hc : ∀ x : maximalRealSubfield E, (conjE (E` using `E)) (x : E) = x := fun x => IsCMField.complexConj_apply_eq_self E x`.

Establish `h2 : ∏ P ∈ aboveF (L` using `E) (maximalRealSubfield E) v, (transport conjE χ).locK P k = ∏ P ∈ aboveF (L := E) (maximalRealSubfield E) v, χ.locK P (Units.map (conjE (E := E)).toMonoidHom k) := by`. Use `symm`. Use `Finset.prod_nbij' (fun P => plMap (conjE (E := E)).symm P) (fun P => plMap conjE P) ?_ ?_ ?_ ?_ ?_` and prove the remaining obligations. Introduce `P hP`. Rewrite `hP`, the goal using `[mem_aboveF]`.

Rewrite using `[under_plMap _ hs P]`. Conclude with `hP`. Introduce `P hP`. Rewrite `hP`, the goal using `[mem_aboveF]`. Rewrite using `[under_plMap _ hc P]`.

Conclude with `hP`. Introduce `P _`. Conclude with `plMap_plMap_symm conjE P`. Introduce `P _`. Conclude with `plMap_symm_plMap conjE P`.

Introduce `P _ show χ.loc P (atFin P _) = (transport conjE χ).loc (plMap (conjE (E := E)).symm P) (atFin _ k)`. Rewrite using `[transport_loc, locMap_atFin]`. Rewrite using `[Finset.prod_congr rfl (fun P _ => h1 P), Finset.prod_mul_distrib, h2, ← Finset.prod_mul_distrib]`. Establish `hN : (k : E) * conjE (k : E) ∈ maximalRealSubfield E`. Rewrite using `[← IsCMField.complexConj_eq_self_iff, map_mul, conjE_apply, IsCMField.complexConj_apply_apply, mul_comm]`.

Establish `hN0 : (⟨_, hN⟩ : maximalRealSubfield E) ≠ 0` using `fun h0 => mul_ne_zero k.ne_zero ((map_ne_zero _).2 k.ne_zero) (congrArg Subtype.val h0)`. Establish `h3` using `hχ.1 v (Units.mk0 _ hN0)`. Unfold `HChar.resFin at h3`. Rewrite `h3` using `[MonoidHom.finset_prod_apply]`. Rewrite using `[← h3]`.

Use `Finset.prod_congr rfl fun P _ => ?_` and prove the remaining obligations. Rewrite using `[← map_mul]`. Conclude with `congrArg _ (Units.ext rfl)`.
-/
theorem prod_locK_conj (χ : HChar E) (hχ : TrivOnF χ) (v : HeightOneSpectrum (OF E)) (k : Eˣ) :
    ∏ P ∈ aboveF (L := E) (maximalRealSubfield E) v, (χ * transport conjE χ).locK P k = 1 := by
  have h1 : ∀ P, (χ * transport conjE χ).locK P k = χ.locK P k * (transport conjE χ).locK P k := fun P => rfl
  have hs : ∀ x : maximalRealSubfield E, (conjE (E := E)).symm (x : E) = x := fun x => by
    rw [conjE_symm_apply]; exact IsCMField.complexConj_apply_eq_self E x
  have hc : ∀ x : maximalRealSubfield E, (conjE (E := E)) (x : E) = x := fun x =>
    IsCMField.complexConj_apply_eq_self E x
  have h2 : ∏ P ∈ aboveF (L := E) (maximalRealSubfield E) v, (transport conjE χ).locK P k =
      ∏ P ∈ aboveF (L := E) (maximalRealSubfield E) v, χ.locK P (Units.map (conjE (E := E)).toMonoidHom k) := by
    symm
    refine Finset.prod_nbij' (fun P => plMap (conjE (E := E)).symm P) (fun P => plMap conjE P) ?_ ?_ ?_ ?_ ?_
    · intro P hP
      rw [mem_aboveF] at hP ⊢
      rw [under_plMap _ hs P]; exact hP
    · intro P hP
      rw [mem_aboveF] at hP ⊢
      rw [under_plMap _ hc P]; exact hP
    · intro P _; exact plMap_plMap_symm conjE P
    · intro P _; exact plMap_symm_plMap conjE P
    · intro P _
      show χ.loc P (atFin P _) = (transport conjE χ).loc (plMap (conjE (E := E)).symm P) (atFin _ k)
      rw [transport_loc, locMap_atFin]
  rw [Finset.prod_congr rfl (fun P _ => h1 P), Finset.prod_mul_distrib, h2, ← Finset.prod_mul_distrib]
  have hN : (k : E) * conjE (k : E) ∈ maximalRealSubfield E := by
    rw [← IsCMField.complexConj_eq_self_iff, map_mul, conjE_apply, IsCMField.complexConj_apply_apply, mul_comm]
  have hN0 : (⟨_, hN⟩ : maximalRealSubfield E) ≠ 0 := fun h0 =>
    mul_ne_zero k.ne_zero ((map_ne_zero _).2 k.ne_zero) (congrArg Subtype.val h0)
  have h3 := hχ.1 v (Units.mk0 _ hN0)
  unfold HChar.resFin at h3
  rw [MonoidHom.finset_prod_apply] at h3
  rw [← h3]
  refine Finset.prod_congr rfl fun P _ => ?_
  rw [← map_mul]
  exact congrArg _ (Units.ext rfl)

/- English proof (translation)
Establish `h` using `loc_eq_one_of_prod (χ * transport conjE χ) _ (prod_locK_conj χ hχ (P.under (OF E))) (w := P) ((mem_aboveF _ P).2 rfl) x`. Rewrite `h` using `[HChar.loc_mul]`. Conclude with `eq_inv_of_mul_eq_one_right h`.
-/
theorem loc_transport (χ : HChar E) (hχ : TrivOnF χ) (P : HeightOneSpectrum (𝓞 E)) (x : (P.adicCompletion E)ˣ) :
    (transport conjE χ).loc P x = (χ.loc P x)⁻¹ := by
  have h := loc_eq_one_of_prod (χ * transport conjE χ) _ (prod_locK_conj χ hχ (P.under (OF E)))
    (w := P) ((mem_aboveF _ P).2 rfl) x
  rw [HChar.loc_mul] at h
  exact eq_inv_of_mul_eq_one_right h

/- English proof (translation)
Rewrite using `[← transport_unrAt_iff]`. Unfold `HChar.UnrAt`. Simplify using `only [HChar.loc_inv, loc_transport χ hχ]`.
-/
theorem unrAt_inv_iff (χ : HChar E) (hχ : TrivOnF χ) (P : HeightOneSpectrum (𝓞 E)) :
    χ⁻¹.UnrAt P ↔ χ.UnrAt (plMap conjE P) := by
  rw [← transport_unrAt_iff]
  unfold HChar.UnrAt
  simp only [HChar.loc_inv, loc_transport χ hχ]

/- English proof (translation)
Rewrite using `[← transport_val conjE χ P h]`. Use `show (χ.loc P _)⁻¹ = (transport conjE χ).loc P _`. Rewrite using `[loc_transport χ hχ]`.
-/
theorem val_inv_eq (χ : HChar E) (hχ : TrivOnF χ) (P : HeightOneSpectrum (𝓞 E)) (h : χ.UnrAt (plMap conjE P)) :
    χ⁻¹.val P = χ.val (plMap conjE P) := by
  rw [← transport_val conjE χ P h]
  show (χ.loc P _)⁻¹ = (transport conjE χ).loc P _
  rw [loc_transport χ hχ]

/- English proof (translation)
Unfold `eulerFactor`. Distinguish the cases in `h : χ.UnrAt (plMap conjE P)`. Rewrite using `[if_pos ((unrAt_inv_iff χ hχ P).2 h), if_pos h, val_inv_eq χ hχ P h, absNorm_plMap]`. Rewrite using `[if_neg (fun h' => h ((unrAt_inv_iff χ hχ P).1 h')), if_neg h]`.
-/
theorem eulerFactor_inv (χ : HChar E) (hχ : TrivOnF χ) (s : ℂ) (P : HeightOneSpectrum (𝓞 E)) :
    eulerFactor χ⁻¹ s P = eulerFactor χ s (plMap conjE P) := by
  unfold eulerFactor
  by_cases h : χ.UnrAt (plMap conjE P)
  · rw [if_pos ((unrAt_inv_iff χ hχ P).2 h), if_pos h, val_inv_eq χ hχ P h, absNorm_plMap]
  · rw [if_neg (fun h' => h ((unrAt_inv_iff χ hχ P).1 h')), if_neg h]

end GlobalTheory.CMVal.InvConj

open Formalism.L2.Host.CT GlobalTheory.CMVal.InvConj in

/- English proof (translation)
Introduce `E _ _ _ χ Λ hχ hL`. Use `⟨hL.1, fun s hs => ?_⟩` and prove the remaining obligations. Set `e : HeightOneSpectrum (𝓞 E) ≃ HeightOneSpectrum (𝓞 E)` to `⟨plMap conjE, plMap (conjE (E := E)).symm, plMap_symm_plMap conjE, plMap_plMap_symm conjE⟩`. Establish `he : eulerFactor χ⁻¹ s = eulerFactor χ s ∘ e` using `funext fun P => eulerFactor_inv χ hχ s P`. Rewrite using `[he, Equiv.hasProd_iff]`.

Conclude with `hL.2 s hs`.
-/
theorem GlobalTheory.CMVal.isHeckeL_inv_of_trivOnF : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (χ : HChar E)
    (Λ : ℂ → ℂ), TrivOnF χ → IsHeckeL χ Λ → IsHeckeL χ⁻¹ Λ := by
  intro E _ _ _ χ Λ hχ hL
  refine ⟨hL.1, fun s hs => ?_⟩
  let e : HeightOneSpectrum (𝓞 E) ≃ HeightOneSpectrum (𝓞 E) :=
    ⟨plMap conjE, plMap (conjE (E := E)).symm, plMap_symm_plMap conjE, plMap_plMap_symm conjE⟩
  have he : eulerFactor χ⁻¹ s = eulerFactor χ s ∘ e := funext fun P => eulerFactor_inv χ hχ s P
  rw [he, Equiv.hasProd_iff]
  exact hL.2 s hs

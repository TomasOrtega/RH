import Formalism.LocalToGlobal.GroupLattices.FockModels.TransposeWords.FormSK

open MvPolynomial

noncomputable section

namespace Formalism.L2.G.Model.TS

open Formalism.MainNotions.G Formalism.GradedWeylDivisibility Formalism.InvariantFactorPaths.INST

/- English proof (translation)
Break down `CharP.char_is_prime_or_zero W (ringChar W) with hq | hq` into its components or cases. Use `exfalso haveI : CharP W (ringChar W) := ringChar.charP W haveI : Fact (ringChar W).Prime := ⟨hq⟩`. Distinguish the cases in `hpq : p = ringChar W`. Conclude with `h.ne_zero (by rw [hpq]; exact CharP.cast_eq_zero W _)`. Apply `h.not_isUnit` to reduce the goal to its premises.

Establish `hu : IsUnit (p : ZMod (ringChar W))`. Rewrite using `[ZMod.isUnit_iff_coprime]`. Conclude with `(Nat.coprime_primes hp hq).mpr hpq`. Establish `hu'` using `hu.map (ZMod.castHom (dvd_refl _) W)`. Simplify using `using hu'`.

Use `haveI : CharP W 0 := by`. Rewrite using `[← hq]`. Conclude with `ringChar.charP W`. Conclude with `CharP.charP_to_charZero W`.
-/
theorem charZero_of_irreducible_natCast {W : Type*} [CommRing W] [IsDomain W] {p : ℕ} (hp : p.Prime)
    (h : Irreducible (p : W)) : CharZero W := by
  rcases CharP.char_is_prime_or_zero W (ringChar W) with hq | hq
  · exfalso
    haveI : CharP W (ringChar W) := ringChar.charP W
    haveI : Fact (ringChar W).Prime := ⟨hq⟩
    by_cases hpq : p = ringChar W
    · exact h.ne_zero (by rw [hpq]; exact CharP.cast_eq_zero W _)
    · apply h.not_isUnit
      have hu : IsUnit (p : ZMod (ringChar W)) := by
        rw [ZMod.isUnit_iff_coprime]
        exact (Nat.coprime_primes hp hq).mpr hpq
      have hu' := hu.map (ZMod.castHom (dvd_refl _) W)
      simpa using hu'
  · haveI : CharP W 0 := by
      rw [← hq]
      exact ringChar.charP W
    exact CharP.charP_to_charZero W

/- English proof (translation)
Introduce `a b hab`. Conclude with `Int.toNat_le_toNat (sub_le_sub_right (hl hab) _)`.
-/
theorem nuOf_antitone {m : ℕ} {lam : Fin (m + 1) → ℤ} (hl : Antitone lam) : Antitone (nuOf lam) := by
  intro a b hab
  exact Int.toNat_le_toNat (sub_le_sub_right (hl hab) _)

/- English proof (translation)
Use `ext`. Simplify using `[lastIdx]`.
-/
theorem lastIdx_succ (m : ℕ) : lastIdx (m + 1) = Fin.last m := by
  ext
  simp [lastIdx]

/- English proof (translation)
Unfold `ellWt`. Rewrite using `[lastIdx_succ]`. Conclude with `Int.toNat_le_toNat (sub_le_sub_right (hl (Fin.zero_le t)) _)`.
-/
theorem nuOf_le_ellWt {m : ℕ} {lam : Fin (m + 1) → ℤ} (hl : Antitone lam) (t : Fin (m + 1)) :
    nuOf lam t ≤ ellWt lam := by
  unfold ellWt
  rw [lastIdx_succ]
  exact Int.toNat_le_toNat (sub_le_sub_right (hl (Fin.zero_le t)) _)

/- English proof (translation)
Introduce `p n' W Qq O Kf _ _ _ _ _ _ _ _ _ _ ι σ j w hS m lam hl`. Establish `: Fact p.Prime` using `⟨hS.prime⟩`. Establish `: IsFractionRing O Kf` using `hS.frac_O`. Establish `: IsFractionRing W Qq` using `hS.frac_alt`. Establish `: CharZero W` using `charZero_of_irreducible_natCast hS.prime hS.p_unif`.

Establish `hinj : Function.Injective (ι.comp (algebraMap W Qq))` using `ι.injective.comp (IsFractionRing.injective W Qq)`. Establish `: CharZero Kf` using `charZero_of_injective_ringHom hinj`. Establish `hj : Function.Injective j`. Introduce `x y hxy`. Apply `hinj` to reduce the goal to its premises.

Simplify using `only [RingHom.comp_apply, hS.ι_comp, hxy]`. Establish `hp : ¬ IsUnit ((p : ℕ) : O)`. Introduce `hu`. Use `hS.finite.to_isIntegral.isLocalHom hj` as an intermediate fact. Establish `hu' : IsUnit (j (p : W))` using `by rwa [map_natCast]`.

Conclude with `hS.p_unif.not_isUnit (isUnit_of_map_unit j _ hu')`. Take `⟨B, ha, hb, hc, hd, he⟩` from `h p O Kf hp (m + 1) (m + 1) le_rfl (nuOf lam) (nuOf_antitone hl)`. Use `⟨B, ha, hb, hc, ?_⟩` and prove the remaining obligations. Introduce `Q hQ P hP`. Unfold `expN`.

Use `split_ifs with h0`. Rewrite using `[pow_zero, one_smul]`. Use `he (fun t => ?_) Q hQ P hP` and prove the remaining obligations. Use `nuOf_le_ellWt hl t` as an intermediate fact. Use linear arithmetic over natural numbers and integers.

Conclude with `hd (ellWt lam) (Or.inl (nuOf_le_ellWt hl)) Q hQ P hP`.
-/
theorem formCoreSK_of (h : FormCoreG) : FormCoreSK := by
  intro p n' W Qq O Kf _ _ _ _ _ _ _ _ _ _ ι σ j w hS m lam hl
  have : Fact p.Prime := ⟨hS.prime⟩
  have : IsFractionRing O Kf := hS.frac_O
  have : IsFractionRing W Qq := hS.frac_alt
  have : CharZero W := charZero_of_irreducible_natCast hS.prime hS.p_unif
  have hinj : Function.Injective (ι.comp (algebraMap W Qq)) :=
    ι.injective.comp (IsFractionRing.injective W Qq)
  have : CharZero Kf := charZero_of_injective_ringHom hinj
  have hj : Function.Injective j := by
    intro x y hxy
    apply hinj
    simp only [RingHom.comp_apply, hS.ι_comp, hxy]
  have hp : ¬ IsUnit ((p : ℕ) : O) := by
    intro hu
    have := hS.finite.to_isIntegral.isLocalHom hj
    have hu' : IsUnit (j (p : W)) := by rwa [map_natCast]
    exact hS.p_unif.not_isUnit (isUnit_of_map_unit j _ hu')
  obtain ⟨B, ha, hb, hc, hd, he⟩ := h p O Kf hp (m + 1) (m + 1) le_rfl (nuOf lam) (nuOf_antitone hl)
  refine ⟨B, ha, hb, hc, ?_⟩
  intro Q hQ P hP
  unfold expN
  split_ifs with h0
  · rw [pow_zero, one_smul]
    refine he (fun t => ?_) Q hQ P hP
    have := nuOf_le_ellWt hl t
    omega
  · exact hd (ellWt lam) (Or.inl (nuOf_le_ellWt hl)) Q hQ P hP

end Formalism.L2.G.Model.TS

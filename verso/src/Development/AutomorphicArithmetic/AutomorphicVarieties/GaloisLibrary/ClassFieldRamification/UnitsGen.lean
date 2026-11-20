import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.ClassFieldRamification.IsClassFieldHilbert
import GroundTheory.GlobalFields.TateThesis.Chebotarev
import Development.AutomorphicArithmetic.CyclotomicBounds.ClassNumberBounds.InertiaRamification.CycInertia

open NumberField IsDedekindDomain IntermediateField UpperTheory.V.Kum UpperTheory.V.CF
open scoped Pointwise

/- English proof (translation)
Rewrite using `[MonoidHom.mem_ker, ZMod.unitsMap_def, Units.ext_iff, Units.coe_map, Units.val_one]`. Simplify using `only [MonoidHom.coe_coe, ZMod.castHom_apply, ZMod.cast_eq_val]`. Rewrite using `[← Nat.cast_one, ZMod.natCast_eq_natCast_iff]`.
-/
private theorem mem_ker_iff {N d : ℕ} [NeZero N] (h : d ∣ N) (u : (ZMod N)ˣ) :
    u ∈ (ZMod.unitsMap h).ker ↔ (u : ZMod N).val ≡ 1 [MOD d] := by
  rw [MonoidHom.mem_ker, ZMod.unitsMap_def, Units.ext_iff, Units.coe_map, Units.val_one]
  simp only [MonoidHom.coe_coe, ZMod.castHom_apply, ZMod.cast_eq_val]
  rw [← Nat.cast_one, ZMod.natCast_eq_natCast_iff]

/- English proof (translation)
Introduce `u hu`. Rewrite `hu` using `[mem_ker_iff hg]`. Establish `hx1 : 1 ≡ (u : ZMod N).val [MOD Nat.gcd d e]` using `(Nat.ModEq.of_dvd hgcd hu).symm`. Take `⟨k, hk1, hk2⟩` from `Nat.chineseRemainder' hx1`. Establish `hxN : (u : ZMod N).val.Coprime N` using `ZMod.val_coe_unit_coprime u`.

Establish `hkd : k.Coprime d`. Unfold `Nat.Coprime`. Rewrite using `[hk1.gcd_eq]`. Conclude with `Nat.gcd_one_left d`. Establish `hke : k.Coprime e`.

Unfold `Nat.Coprime`. Rewrite using `[hk2.gcd_eq]`. Conclude with `Nat.Coprime.coprime_dvd_right he hxN`. Establish `hkN : k.Coprime N` using `Nat.Coprime.coprime_dvd_right hN (Nat.Coprime.mul_right hkd hke)`. Establish `hvval : ((ZMod.unitOfCoprime k hkN : (ZMod N)ˣ) : ZMod N).val = k % N`.

Rewrite using `[ZMod.coe_unitOfCoprime, ZMod.val_natCast]`. Establish `hv : ZMod.unitOfCoprime k hkN ∈ (ZMod.unitsMap hd).ker`. Rewrite using `[mem_ker_iff hd, hvval]`. Conclude with `((Nat.mod_modEq k N).of_dvd hd).trans hk1`. Establish `key : ZMod.unitsMap he (ZMod.unitOfCoprime k hkN) = ZMod.unitsMap he u`.

Use `ext`. Rewrite using `[ZMod.unitsMap_def, Units.coe_map, Units.coe_map]`. Simplify using `only [MonoidHom.coe_coe, ZMod.castHom_apply, ZMod.cast_eq_val]`. Rewrite using `[hvval, ZMod.natCast_eq_natCast_iff]`. Conclude with `((Nat.mod_modEq k N).of_dvd he).trans hk2`.

Establish `hw : (ZMod.unitOfCoprime k hkN)⁻¹ * u ∈ (ZMod.unitsMap he).ker`. Rewrite using `[MonoidHom.mem_ker, map_mul, map_inv, key, inv_mul_cancel]`. Establish `hu' : u = ZMod.unitOfCoprime k hkN * ((ZMod.unitOfCoprime k hkN)⁻¹ * u)`. Rewrite using `[mul_inv_cancel_left]`. Rewrite using `[hu']`.

Conclude with `Subgroup.mul_mem_sup hv hw`.
-/
private theorem ker_le_sup {N g d e : ℕ} [NeZero N] (hg : g ∣ N) (hd : d ∣ N) (he : e ∣ N)
    (hgcd : Nat.gcd d e ∣ g) (hN : N ∣ d * e) :
    (ZMod.unitsMap hg).ker ≤ (ZMod.unitsMap hd).ker ⊔ (ZMod.unitsMap he).ker := by
  intro u hu
  rw [mem_ker_iff hg] at hu
  have hx1 : 1 ≡ (u : ZMod N).val [MOD Nat.gcd d e] := (Nat.ModEq.of_dvd hgcd hu).symm
  obtain ⟨k, hk1, hk2⟩ := Nat.chineseRemainder' hx1
  have hxN : (u : ZMod N).val.Coprime N := ZMod.val_coe_unit_coprime u
  have hkd : k.Coprime d := by
    unfold Nat.Coprime
    rw [hk1.gcd_eq]
    exact Nat.gcd_one_left d
  have hke : k.Coprime e := by
    unfold Nat.Coprime
    rw [hk2.gcd_eq]
    exact Nat.Coprime.coprime_dvd_right he hxN
  have hkN : k.Coprime N := Nat.Coprime.coprime_dvd_right hN (Nat.Coprime.mul_right hkd hke)
  have hvval : ((ZMod.unitOfCoprime k hkN : (ZMod N)ˣ) : ZMod N).val = k % N := by
    rw [ZMod.coe_unitOfCoprime, ZMod.val_natCast]
  have hv : ZMod.unitOfCoprime k hkN ∈ (ZMod.unitsMap hd).ker := by
    rw [mem_ker_iff hd, hvval]
    exact ((Nat.mod_modEq k N).of_dvd hd).trans hk1
  have key : ZMod.unitsMap he (ZMod.unitOfCoprime k hkN) = ZMod.unitsMap he u := by
    ext
    rw [ZMod.unitsMap_def, Units.coe_map, Units.coe_map]
    simp only [MonoidHom.coe_coe, ZMod.castHom_apply, ZMod.cast_eq_val]
    rw [hvval, ZMod.natCast_eq_natCast_iff]
    exact ((Nat.mod_modEq k N).of_dvd he).trans hk2
  have hw : (ZMod.unitOfCoprime k hkN)⁻¹ * u ∈ (ZMod.unitsMap he).ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, key, inv_mul_cancel]
  have hu' : u = ZMod.unitOfCoprime k hkN * ((ZMod.unitOfCoprime k hkN)⁻¹ * u) := by
    rw [mul_inv_cancel_left]
  rw [hu']
  exact Subgroup.mul_mem_sup hv hw

/- English proof (translation)
Proceed by induction on `b using Nat.strong_induction_on with`. Consider the case `_ b ih`. Introduce `a ha hab hcop`. Establish `hN0 : N ≠ 0` using `NeZero.ne N`. Establish `hb0 : b ≠ 0`.

Introduce and unpack `rfl`. Conclude with `hN0 (by rw [← hab, mul_zero])`. Establish `ha0 : a ≠ 0`. Introduce and unpack `rfl`. Conclude with `hN0 (by rw [← hab, zero_mul])`.

Distinguish the cases in `hb1 : b = 1`. Substitute `hb1` using the available equality. Rewrite `hab` using `[mul_one]`. Substitute `hab` using the available equality. Introduce `u hu`.

Rewrite `hu` using `[mem_ker_iff ha]`. Establish `hu1 : u = 1`. Use `ext`. Rewrite using `[Units.val_one, ← ZMod.natCast_zmod_val (u : ZMod a), ← Nat.cast_one, ZMod.natCast_eq_natCast_iff]`. Conclude with `hu`.

Rewrite using `[hu1]`. Conclude with `one_mem _`. Take `⟨p, hp, hpb⟩` from `Nat.exists_prime_and_dvd hb1`. Establish `hpa : ¬ p ∣ a`. Introduce `h`.

Establish `h1` using `Nat.dvd_gcd h hpb`. Rewrite `h1` using `[hcop.gcd_eq_one]`. Conclude with `hp.ne_one (Nat.dvd_one.mp h1)`. Establish `hbsplit` using `Nat.ordProj_mul_ordCompl_eq_self b p`. Establish `hk0 : 0 < b.factorization p` using `hp.factorization_pos_of_dvd hb0 hpb`.

Establish `hb'pos : 0 < b / p ^ b.factorization p` using `Nat.ordCompl_pos p hb0`. Establish `hpk : 2 ≤ p ^ b.factorization p` using `le_trans hp.two_le (Nat.le_self_pow (by omega) p)`. Establish `hb'lt : b / p ^ b.factorization p < b`. Establish `h2 : 2 * (b / p ^ b.factorization p) ≤ p ^ b.factorization p * (b / p ^ b.factorization p)` using `Nat.mul_le_mul_right _ hpk`. Use linear arithmetic over natural numbers and integers.

Establish `hb'dvd : b / p ^ b.factorization p ∣ b` using `Nat.ordCompl_dvd b p`. Establish `hpb' : Nat.Coprime p (b / p ^ b.factorization p)` using `Nat.coprime_ordCompl hp hb0`. Establish `ha'N : a * p ^ b.factorization p * (b / p ^ b.factorization p) = N`. Rewrite using `[mul_assoc, hbsplit, hab]`. Establish `ha'dvd : a * p ^ b.factorization p ∣ N` using `⟨_, ha'N.symm⟩`.

Establish `ha'cop : (a * p ^ b.factorization p).Coprime (b / p ^ b.factorization p)` using `Nat.Coprime.mul (Nat.Coprime.coprime_dvd_right hb'dvd hcop) (Nat.Coprime.pow_left _ hpb')`. Establish `IH` using `ih _ hb'lt (a * p ^ b.factorization p) ha'dvd ha'N ha'cop`. Establish `hvN : N.factorization p = b.factorization p`. Rewrite using `[← hab, Nat.factorization_mul ha0 hb0, Finsupp.add_apply, Nat.factorization_eq_zero_of_not_dvd hpa, zero_add]`. Establish `hNsplit` using `Nat.ordProj_mul_ordCompl_eq_self N p`.

Establish `hcopE : (p ^ b.factorization p).Coprime (N / p ^ N.factorization p)` using `Nat.Coprime.pow_left _ (Nat.coprime_ordCompl hp hN0)`. Establish `hgcd : Nat.gcd (a * p ^ b.factorization p) (N / p ^ N.factorization p) ∣ a`. Rewrite using `[Nat.Coprime.gcd_mul_right_cancel a hcopE]`. Conclude with `Nat.gcd_dvd_left _ _`. Establish `hNde : N ∣ (a * p ^ b.factorization p) * (N / p ^ N.factorization p)`.

Use `⟨a, ?_⟩` and prove the remaining obligations. Rewrite using `[← hvN, mul_assoc, hNsplit, mul_comm]`. Establish `hstep` using `ker_le_sup ha ha'dvd (Nat.ordCompl_dvd N p) hgcd hNde`. Use `hstep.trans (sup_le (IH.trans ?_) ?_)` and prove the remaining obligations. Conclude with `iSup₂_le fun q hq => le_iSup₂ (f := fun q (_ : q ∈ b.primeFactors) => KStar.Ram.inertiaUnits N q) q (Nat.primeFactors_mono hb'dvd hb0 hq)`.

Conclude with `le_iSup₂ (f := fun q (_ : q ∈ b.primeFactors) => KStar.Ram.inertiaUnits N q) p (Nat.mem_primeFactors.2 ⟨hp, hpb, hb0⟩)`.
-/
private theorem aux (N : ℕ) [NeZero N] (b : ℕ) : ∀ (a : ℕ) (ha : a ∣ N), a * b = N → a.Coprime b →
    (ZMod.unitsMap ha).ker ≤ ⨆ p ∈ b.primeFactors, KStar.Ram.inertiaUnits N p := by
  induction b using Nat.strong_induction_on with
  | _ b ih =>
  intro a ha hab hcop
  have hN0 : N ≠ 0 := NeZero.ne N
  have hb0 : b ≠ 0 := by
    rintro rfl
    exact hN0 (by rw [← hab, mul_zero])
  have ha0 : a ≠ 0 := by
    rintro rfl
    exact hN0 (by rw [← hab, zero_mul])
  by_cases hb1 : b = 1
  · subst hb1
    rw [mul_one] at hab
    subst hab
    intro u hu
    rw [mem_ker_iff ha] at hu
    have hu1 : u = 1 := by
      ext
      rw [Units.val_one, ← ZMod.natCast_zmod_val (u : ZMod a), ← Nat.cast_one,
        ZMod.natCast_eq_natCast_iff]
      exact hu
    rw [hu1]
    exact one_mem _
  · obtain ⟨p, hp, hpb⟩ := Nat.exists_prime_and_dvd hb1
    have hpa : ¬ p ∣ a := by
      intro h
      have h1 := Nat.dvd_gcd h hpb
      rw [hcop.gcd_eq_one] at h1
      exact hp.ne_one (Nat.dvd_one.mp h1)
    have hbsplit := Nat.ordProj_mul_ordCompl_eq_self b p
    have hk0 : 0 < b.factorization p := hp.factorization_pos_of_dvd hb0 hpb
    have hb'pos : 0 < b / p ^ b.factorization p := Nat.ordCompl_pos p hb0
    have hpk : 2 ≤ p ^ b.factorization p := le_trans hp.two_le (Nat.le_self_pow (by omega) p)
    have hb'lt : b / p ^ b.factorization p < b := by
      have h2 : 2 * (b / p ^ b.factorization p) ≤ p ^ b.factorization p * (b / p ^ b.factorization p) :=
        Nat.mul_le_mul_right _ hpk
      omega
    have hb'dvd : b / p ^ b.factorization p ∣ b := Nat.ordCompl_dvd b p
    have hpb' : Nat.Coprime p (b / p ^ b.factorization p) := Nat.coprime_ordCompl hp hb0
    have ha'N : a * p ^ b.factorization p * (b / p ^ b.factorization p) = N := by
      rw [mul_assoc, hbsplit, hab]
    have ha'dvd : a * p ^ b.factorization p ∣ N := ⟨_, ha'N.symm⟩
    have ha'cop : (a * p ^ b.factorization p).Coprime (b / p ^ b.factorization p) :=
      Nat.Coprime.mul (Nat.Coprime.coprime_dvd_right hb'dvd hcop) (Nat.Coprime.pow_left _ hpb')
    have IH := ih _ hb'lt (a * p ^ b.factorization p) ha'dvd ha'N ha'cop
    have hvN : N.factorization p = b.factorization p := by
      rw [← hab, Nat.factorization_mul ha0 hb0, Finsupp.add_apply,
        Nat.factorization_eq_zero_of_not_dvd hpa, zero_add]
    have hNsplit := Nat.ordProj_mul_ordCompl_eq_self N p
    have hcopE : (p ^ b.factorization p).Coprime (N / p ^ N.factorization p) :=
      Nat.Coprime.pow_left _ (Nat.coprime_ordCompl hp hN0)
    have hgcd : Nat.gcd (a * p ^ b.factorization p) (N / p ^ N.factorization p) ∣ a := by
      rw [Nat.Coprime.gcd_mul_right_cancel a hcopE]
      exact Nat.gcd_dvd_left _ _
    have hNde : N ∣ (a * p ^ b.factorization p) * (N / p ^ N.factorization p) := by
      refine ⟨a, ?_⟩
      rw [← hvN, mul_assoc, hNsplit, mul_comm]
    have hstep := ker_le_sup ha ha'dvd (Nat.ordCompl_dvd N p) hgcd hNde
    refine hstep.trans (sup_le (IH.trans ?_) ?_)
    · exact iSup₂_le fun q hq =>
        le_iSup₂ (f := fun q (_ : q ∈ b.primeFactors) => KStar.Ram.inertiaUnits N q) q
          (Nat.primeFactors_mono hb'dvd hb0 hq)
    · exact le_iSup₂ (f := fun q (_ : q ∈ b.primeFactors) => KStar.Ram.inertiaUnits N q) p
        (Nat.mem_primeFactors.2 ⟨hp, hpb, hb0⟩)

/- English proof (translation)
Introduce `a b _ h`. Conclude with `aux (a * b) b a _ rfl h`.
-/
theorem UpperTheory.V.CF.unitsGen :
    ∀ (a b : ℕ) [NeZero (a * b)], a.Coprime b → (ZMod.unitsMap (dvd_mul_right a b)).ker ≤ ⨆ p ∈ b.primeFactors, KStar.Ram.inertiaUnits (a * b) p := by
  intro a b _ h
  exact aux (a * b) b a _ rfl h

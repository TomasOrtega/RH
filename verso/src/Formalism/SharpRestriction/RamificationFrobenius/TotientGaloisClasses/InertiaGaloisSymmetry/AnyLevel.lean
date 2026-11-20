import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.InertiaGaloisSymmetry.OfCharLevel
import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.InertiaGaloisSymmetry.AnyFrame

noncomputable section

namespace Formalism.HC

open Formalism.FrobeniusOrbits

namespace AnyGrp

open EvenGrp hiding data frame frame_e o_eq twoGroup QS_le exact_data theta theta_mem host host_q host_d host_QS psQ exact muPM
  coprimeFifteen_of_coprime exists_sqq prim_theta keptInXp exceptional_character_condition o_eq_level

variable {M : ℕ} [NeZero M] (Ξ : Subgroup (DirichletCharacter ℂ M)) (e : ℕ)

def data : ModData where
  e := e
  m := QS Ξ e
  m_pos := QS_pos Ξ e
  tower := (good_QS Ξ e).2.1
  B := B Ξ
  ξ := xi Ξ e

abbrev frame : Frame := (data Ξ e).frame

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem frame_e : (frame Ξ e).e = e := rfl

/- English proof (translation)
Use `show (data Ξ e).frame.o = _`. Rewrite using `[ModData.o_eq]`. Use `show Nat.card (xi Ξ e).range = _`. Rewrite using `[MonoidHom.range_eq_top.mpr (EvenGrp.xi_surj Ξ e), Subgroup.card_top]`. Conclude with `EvenGrp.card_B Ξ`.
-/
theorem o_eq : (frame Ξ e).o = Nat.card Ξ := by
  show (data Ξ e).frame.o = _
  rw [ModData.o_eq]
  show Nat.card (xi Ξ e).range = _
  rw [MonoidHom.range_eq_top.mpr (EvenGrp.xi_surj Ξ e), Subgroup.card_top]
  exact EvenGrp.card_B Ξ

/- English proof (translation)
Take `⟨j, hj⟩` from `h`. Apply `ModData.twoGroup` to reduce the goal to its premises. Use `⟨j, fun u => ?_⟩` and prove the remaining obligations. Establish `h2 : Nat.card (B Ξ) = 2 ^ j` using `(EvenGrp.card_B Ξ).trans hj`. Rewrite using `[← h2]`.

Conclude with `pow_card_eq_one'`.
-/
theorem twoGroup (h : ∃ j : ℕ, Nat.card Ξ = 2 ^ j) : (frame Ξ e).TwoGroup := by
  obtain ⟨j, hj⟩ := h
  apply ModData.twoGroup
  refine ⟨j, fun u => ?_⟩
  have h2 : Nat.card (B Ξ) = 2 ^ j := (EvenGrp.card_B Ξ).trans hj
  rw [← h2]
  exact pow_card_eq_one'

/- English proof (translation)
Establish `h1` using `Nat.le_of_dvd (Nat.mul_pos (by positivity) (Nat.pos_of_ne_zero (NeZero.ne M))) (QS_dvd_mul Ξ e)`. Establish `h2 : 2 ^ e ≤ (frame Ξ e).ord` using `(frame Ξ e).two_pow_le_ord`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem QS_le (h : 4 * M ≤ 2 ^ e) : QS Ξ e ≤ (frame Ξ e).ord ^ 2 := by
  have h1 := Nat.le_of_dvd (Nat.mul_pos (by positivity) (Nat.pos_of_ne_zero (NeZero.ne M))) (QS_dvd_mul Ξ e)
  have h2 : 2 ^ e ≤ (frame Ξ e).ord := (frame Ξ e).two_pow_le_ord
  calc QS Ξ e ≤ 2 ^ e * (4 * M) := by rw [pow_add] at h1; linarith
    _ ≤ 2 ^ e * 2 ^ e := Nat.mul_le_mul_left _ h
    _ ≤ _ := by rw [sq]; exact Nat.mul_le_mul h2 h2

/- English proof (translation)
Establish `hlt : QS Ξ e / l < QS Ξ e` using `Nat.div_lt_self (QS_pos Ξ e) hl.one_lt`. Establish `hdv : QS Ξ e / l ∣ QS Ξ e` using `Nat.div_dvd_of_dvd hd`. Distinguish the cases in `h2 : 2 ^ (e + 2) ∣ QS Ξ e / l`. Assume the negation of the conclusion as `hn`. Use `not_good Ξ e hlt ⟨hdv.trans (QS_dvd Ξ e), h2, fun u hu => ?_⟩` and prove the remaining obligations.

Assume the negation of the conclusion as `h3`. Use `hn ⟨ZMod.unitsMap (QS_dvd Ξ e) u, ((unitsMap_val_modEq (QS_dvd Ξ e) u).of_dvd hdv).symm.trans hu, fun h4 => h3 ?_⟩` and prove the remaining obligations. Rewrite using `[← xi_unitsMap]`. Conclude with `congrArg Prod.snd h4`. Take `⟨c, hc⟩` from `(good_QS Ξ e).2.1`.

Establish `hl2 : l = 2`. Assume the negation of the conclusion as `h3`. Establish `h4 : Nat.Coprime (2 ^ (e + 2)) l` using `Nat.Coprime.pow_left _ ((Nat.coprime_primes Nat.prime_two hl).mpr (Ne.symm h3))`. Conclude with `h2 (h4.dvd_of_dvd_mul_right (by rw [Nat.div_mul_cancel hd]; exact (good_QS Ξ e).2.1))`. Substitute `hl2` using the available equality.

Take `⟨k, rfl⟩ : ∃ k, e = k + 1` from `⟨e - 1, by omega⟩`. Establish `hdiv : QS Ξ (k + 1) / 2 = 2 ^ (k + 2) * c`. Rewrite using `[hc, show 2 ^ (k + 1 + 2) * c = 2 * (2 ^ (k + 2) * c) by ring, Nat.mul_div_cancel_left _ (by norm_num)]`. Establish `hQ : QS Ξ (k + 1) = 2 * (2 ^ (k + 2) * c)` using `by rw [hc]; ring`. Establish `hcop : Nat.Coprime (2 ^ (k + 2) * c + 1) (QS Ξ (k + 1))`.

Rewrite using `[hQ]`. Use `Nat.Coprime.mul_right ?_ (by simp)` and prove the remaining obligations. Rewrite using `[Nat.coprime_two_right]`. Conclude with `⟨2 ^ (k + 1) * c, by ring⟩`. Establish `hval : ((ZMod.unitOfCoprime _ hcop : (ZMod (QS Ξ (k + 1)))ˣ) : ZMod (QS Ξ (k + 1))).val ≡ 2 ^ (k + 2) * c + 1 [MOD QS Ξ (k + 1)]`.

Rewrite using `[ZMod.coe_unitOfCoprime, ZMod.val_natCast]`. Conclude with `Nat.mod_modEq _ _`. Use `⟨ZMod.unitOfCoprime _ hcop, (hval.of_dvd hdv).trans ?_, fun h4 => ?_⟩` and prove the remaining obligations. Rewrite using `[hdiv]`. Simplify using `[Nat.ModEq]`.

Establish `h5 : hcl (k + 1) (ZMod.unitsMap (good_QS Ξ (k + 1)).2.1 (ZMod.unitOfCoprime _ hcop)) = hcl (k + 1) 1` using `congrArg Prod.fst h4`. Rewrite `h5` using `[unitsMap_unitOfCoprime, hcl_eq_hcl_iff, Units.ext_iff, Units.ext_iff, ZMod.coe_unitOfCoprime, Units.val_neg, Units.val_one, Nat.cast_add, Nat.cast_one]`. Break down `h5 with h5 | h5` into its components or cases. Use `h2 ?_` and prove the remaining obligations. Rewrite using `[hdiv, ← ZMod.natCast_eq_zero_iff]`.

Take the linear combination `h5`. Establish `h6 : 2 ^ (k + 1 + 2) ∣ 2 ^ (k + 2) * c + 2`. Rewrite using `[← ZMod.natCast_eq_zero_iff, Nat.cast_add, Nat.cast_ofNat]`. Take the linear combination `h5`. Establish `h7 : 4 ∣ 2 ^ (k + 2) * c + 2` using `Dvd.dvd.trans ⟨2 ^ (k + 1), by ring⟩ h6`.

Establish `h8 : 4 ∣ 2 ^ (k + 2) * c` using `⟨2 ^ k * c, by ring⟩`. Use linear arithmetic over natural numbers and integers.
-/
theorem exact_data (he : 1 ≤ e) (l : ℕ) (hl : l.Prime) (hd : l ∣ QS Ξ e) :
    ∃ v : (ZMod (QS Ξ e))ˣ, (v : ZMod (QS Ξ e)).val ≡ 1 [MOD QS Ξ e / l] ∧ (data Ξ e).eta v ≠ 1 := by
  have hlt : QS Ξ e / l < QS Ξ e := Nat.div_lt_self (QS_pos Ξ e) hl.one_lt
  have hdv : QS Ξ e / l ∣ QS Ξ e := Nat.div_dvd_of_dvd hd
  by_cases h2 : 2 ^ (e + 2) ∣ QS Ξ e / l
  · by_contra hn
    refine not_good Ξ e hlt ⟨hdv.trans (QS_dvd Ξ e), h2, fun u hu => ?_⟩
    by_contra h3
    refine hn ⟨ZMod.unitsMap (QS_dvd Ξ e) u, ((unitsMap_val_modEq (QS_dvd Ξ e) u).of_dvd hdv).symm.trans hu, fun h4 => h3 ?_⟩
    rw [← xi_unitsMap]
    exact congrArg Prod.snd h4
  · obtain ⟨c, hc⟩ := (good_QS Ξ e).2.1
    have hl2 : l = 2 := by
      by_contra h3
      have h4 : Nat.Coprime (2 ^ (e + 2)) l := Nat.Coprime.pow_left _ ((Nat.coprime_primes Nat.prime_two hl).mpr (Ne.symm h3))
      exact h2 (h4.dvd_of_dvd_mul_right (by rw [Nat.div_mul_cancel hd]; exact (good_QS Ξ e).2.1))
    subst hl2
    obtain ⟨k, rfl⟩ : ∃ k, e = k + 1 := ⟨e - 1, by omega⟩
    have hdiv : QS Ξ (k + 1) / 2 = 2 ^ (k + 2) * c := by
      rw [hc, show 2 ^ (k + 1 + 2) * c = 2 * (2 ^ (k + 2) * c) by ring, Nat.mul_div_cancel_left _ (by norm_num)]
    have hQ : QS Ξ (k + 1) = 2 * (2 ^ (k + 2) * c) := by rw [hc]; ring
    have hcop : Nat.Coprime (2 ^ (k + 2) * c + 1) (QS Ξ (k + 1)) := by
      rw [hQ]
      refine Nat.Coprime.mul_right ?_ (by simp)
      rw [Nat.coprime_two_right]
      exact ⟨2 ^ (k + 1) * c, by ring⟩
    have hval : ((ZMod.unitOfCoprime _ hcop : (ZMod (QS Ξ (k + 1)))ˣ) : ZMod (QS Ξ (k + 1))).val ≡ 2 ^ (k + 2) * c + 1
        [MOD QS Ξ (k + 1)] := by
      rw [ZMod.coe_unitOfCoprime, ZMod.val_natCast]
      exact Nat.mod_modEq _ _
    refine ⟨ZMod.unitOfCoprime _ hcop, (hval.of_dvd hdv).trans ?_, fun h4 => ?_⟩
    · rw [hdiv]
      simp [Nat.ModEq]
    · have h5 : hcl (k + 1) (ZMod.unitsMap (good_QS Ξ (k + 1)).2.1 (ZMod.unitOfCoprime _ hcop)) = hcl (k + 1) 1 :=
        congrArg Prod.fst h4
      rw [unitsMap_unitOfCoprime, hcl_eq_hcl_iff, Units.ext_iff, Units.ext_iff, ZMod.coe_unitOfCoprime, Units.val_neg,
        Units.val_one, Nat.cast_add, Nat.cast_one] at h5
      rcases h5 with h5 | h5
      · refine h2 ?_
        rw [hdiv, ← ZMod.natCast_eq_zero_iff]
        linear_combination h5
      · have h6 : 2 ^ (k + 1 + 2) ∣ 2 ^ (k + 2) * c + 2 := by
          rw [← ZMod.natCast_eq_zero_iff, Nat.cast_add, Nat.cast_ofNat]
          linear_combination h5
        have h7 : 4 ∣ 2 ^ (k + 2) * c + 2 := Dvd.dvd.trans ⟨2 ^ (k + 1), by ring⟩ h6
        have h8 : 4 ∣ 2 ^ (k + 2) * c := ⟨2 ^ k * c, by ring⟩
        omega

def thetaA (χ : DirichletCharacter ℂ M) (hχ : χ ∈ Ξ) : (frame Ξ e).MA →* ℂˣ := (thetaB Ξ χ hχ).comp (data Ξ e).xiA

def theta (χ : DirichletCharacter ℂ M) (hχ : χ ∈ Ξ) : (frame Ξ e).Char :=
  (thetaA Ξ e χ hχ).comp (MonoidHom.snd G0 (frame Ξ e).MA * (data Ξ e).w.comp (frame Ξ e).chQ)

/- English proof (translation)
Use `⟨fun s hs => ?_, ?_⟩` and prove the remaining obligations. Establish `h1 : (frame Ξ e).iota s * (data Ξ e).w 1 = (frame Ξ e).iota s` using `(congrArg ((frame Ξ e).iota s * ·) (map_one (data Ξ e).w)).trans (mul_one _)`. Conclude with `(congrArg (thetaA Ξ e χ hχ) h1).trans ((congrArg (thetaB Ξ χ hχ) (((data Ξ e).mem_cusp_forms_iff_automorphic_compact s).mp hs)).trans (map_one _))`. Conclude with `(congrArg (thetaA Ξ e χ hχ) ((one_mul _).trans (map_one (data Ξ e).w))).trans (map_one _)`.
-/
theorem theta_mem (χ : DirichletCharacter ℂ M) (hχ : χ ∈ Ξ) : theta Ξ e χ hχ ∈ (frame Ξ e).Xp := by
  refine ⟨fun s hs => ?_, ?_⟩
  · have h1 : (frame Ξ e).iota s * (data Ξ e).w 1 = (frame Ξ e).iota s :=
      (congrArg ((frame Ξ e).iota s * ·) (map_one (data Ξ e).w)).trans (mul_one _)
    exact (congrArg (thetaA Ξ e χ hχ) h1).trans
      ((congrArg (thetaB Ξ χ hχ) (((data Ξ e).mem_cusp_forms_iff_automorphic_compact s).mp hs)).trans (map_one _))
  · exact (congrArg (thetaA Ξ e χ hχ) ((one_mul _).trans (map_one (data Ξ e).w))).trans (map_one _)

/- English proof (translation)
The claim follows from `congrArg (thetaB Ξ χ hχ) (((data Ξ e).xiA_toA _).trans (xi_unitsMap Ξ e u))`.
-/
theorem thetaA_toA (χ : DirichletCharacter ℂ M) (hχ : χ ∈ Ξ) (u : (ZMod (Nat.lcm (2 ^ (e + 2)) M))ˣ) :
    thetaA Ξ e χ hχ ((data Ξ e).toA (ZMod.unitsMap (QS_dvd Ξ e) u)) =
      χ.toUnitHom (ZMod.unitsMap (Nat.dvd_lcm_right _ _) u) :=
  congrArg (thetaB Ξ χ hχ) (((data Ξ e).xiA_toA _).trans (xi_unitsMap Ξ e u))

section Host

variable {q d : ℕ} (hH : HostHyp q d) (hc : Nat.Coprime M (q * d)) (he : 2 ≤ e)
  (hs : ∀ l : ℕ, l.Prime → l ≠ 2 → l ∣ M → jacobiSym (-(d : ℤ)) l = 1)

def host : HostRaw (frame Ξ e) :=
  (data Ξ e).host hH (coprime_QS Ξ e hH hc) he fun l hl h2 h => hs l hl h2 (dvd_of_dvd_QS Ξ e hl h2 h)

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem host_q : (host Ξ e hH hc he hs).q = q := rfl
/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem host_d : (host Ξ e hH hc he hs).d = d := rfl
/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem host_QS : (host Ξ e hH hc he hs).QS = QS Ξ e := rfl

/- English proof (translation)
Unfold `host`. Apply `ModData.psQ` to reduce the goal to its premises.
-/
theorem psQ : (host Ξ e hH hc he hs).PsQ := by
  unfold host
  apply ModData.psQ

/- English proof (translation)
Unfold `host`. Apply `ModData.exact` to reduce the goal to its premises. Introduce `l hl hd`. Conclude with `exact_data Ξ e (by omega) l hl hd`.
-/
theorem exact : (host Ξ e hH hc he hs).Exact := by
  unfold host
  apply ModData.exact
  intro l hl hd
  exact exact_data Ξ e (by omega) l hl hd

/- English proof (translation)
Unfold `host`. Apply `ModData.muPM (hq := hq) (hmu := hmu)` to reduce the goal to its premises.
-/
theorem muPM (hq : q ≠ 3) (hmu : ∀ k : ℕ, k ∣ QS Ξ e →
    (∀ v : (ZMod (QS Ξ e))ˣ, (data Ξ e).eta v = 1 → (v : ZMod (QS Ξ e)).val ≡ 1 [MOD k]) → k ∣ 2) :
    (host Ξ e hH hc he hs).MuPM := by
  unfold host
  apply ModData.muPM (hq := hq) (hmu := hmu)

/- English proof (translation)
The claim follows from `(Nat.Coprime.mul_left (Nat.Coprime.pow_left _ (by norm_num)) h).coprime_dvd_left (QS_dvd_mul Ξ e)`.
-/
theorem coprimeFifteen_of_coprime (h : Nat.Coprime M 15) : (host Ξ e hH hc he hs).CoprimeFifteen :=
  (Nat.Coprime.mul_left (Nat.Coprime.pow_left _ (by norm_num)) h).coprime_dvd_left (QS_dvd_mul Ξ e)

/- English proof (translation)
Unfold `host`. Apply `ModData.exists_sqq` to reduce the goal to its premises.
-/
theorem exists_sqq : ∃ s : (host Ξ e hH hc he hs).E, s ^ 2 = -((host Ξ e hH hc he hs).q : (host Ξ e hH hc he hs).E) ∧
    ∀ σ : (host Ξ e hH hc he hs).E ≃ₐ[ℚ] (host Ξ e hH hc he hs).E,
      σ s = (((((host Ξ e hH hc he hs).gal σ).1.1 : ℤˣ) : ℤ) : (host Ξ e hH hc he hs).E) * s := by
  unfold host
  apply ModData.exists_sqq

/- English proof (translation)
The claim follows from `congrArg (thetaA Ξ e χ hχ) ((mul_assoc _ _ _).trans ((congrArg (_ * ·) ((data Ξ e).w_mul_self ((data Ξ e).art hH u).1.1)).trans (mul_one _)))`.
-/
theorem theta_art (χ : DirichletCharacter ℂ M) (hχ : χ ∈ Ξ) (u : (ZMod (QS Ξ e * q * d))ˣ) :
    theta Ξ e χ hχ ((host Ξ e hH hc he hs).art u) =
      thetaA Ξ e χ hχ ((data Ξ e).toA (ZMod.unitsMap ((data Ξ e).m_dvd q d) u)) :=
  congrArg (thetaA Ξ e χ hχ) ((mul_assoc _ _ _).trans
    ((congrArg (_ * ·) ((data Ξ e).w_mul_self ((data Ξ e).art hH u).1.1)).trans (mul_one _)))

/- English proof (translation)
Use `set H := host Ξ e hH hc he hs with hHdef`. Use `An.Induces.unique (f := fun a => χ (a : ZMod M)) (M := H.condN * M) (mul_ne_zero H.condN_pos.ne' (NeZero.ne M)) ⟨(PChar.of χ).prim, fun a ha => (An.induces_of χ).2 a ha.coprime_mul_left_right⟩ ⟨(H.prim _).prim, fun a ha => ?_⟩` and prove the remaining obligations. Establish `haN : a.Coprime H.condN` using `ha.coprime_mul_right_right`. Establish `haM : a.Coprime M` using `ha.coprime_mul_left_right`. Establish `haW : a.Coprime (Nat.lcm (2 ^ (e + 2)) M)` using `(Nat.Coprime.mul_right (haN.coprime_dvd_right ((H.tower_dvd.mul_right _).mul_right _)) haM).coprime_dvd_right (Nat.lcm_dvd_mul _ _)`.

Use `((H.isPrimOf_prim _).2 a haN).trans ?_` and prove the remaining obligations. Use `show _ = χ (a : ZMod M)`. Rewrite using `[HostRaw.dirAt, ← ZMod.coe_unitOfCoprime a haN, H.dir_unit, ← ZMod.coe_unitOfCoprime a haM, ← MulChar.coe_toUnitHom]`. Use `congrArg Units.val ?_` and prove the remaining obligations. Establish `h1` using `thetaA_toA Ξ e χ hχ (ZMod.unitOfCoprime a haW)`.

Rewrite `h1` using `[unitsMap_unitOfCoprime, unitsMap_unitOfCoprime]`. Conclude with `(theta_art Ξ e hH hc he hs χ hχ _).trans ((congrArg (fun v => thetaA Ξ e χ hχ ((data Ξ e).toA v)) (unitsMap_unitOfCoprime ((data Ξ e).m_dvd q d) a haN)).trans h1)`.
-/
theorem prim_theta (χ : DirichletCharacter ℂ M) (hχ : χ ∈ Ξ) :
    PChar.of χ = (host Ξ e hH hc he hs).prim (theta Ξ e χ hχ) := by
  set H := host Ξ e hH hc he hs with hHdef
  refine An.Induces.unique (f := fun a => χ (a : ZMod M)) (M := H.condN * M) (mul_ne_zero H.condN_pos.ne' (NeZero.ne M))
    ⟨(PChar.of χ).prim, fun a ha => (An.induces_of χ).2 a ha.coprime_mul_left_right⟩ ⟨(H.prim _).prim, fun a ha => ?_⟩
  have haN : a.Coprime H.condN := ha.coprime_mul_right_right
  have haM : a.Coprime M := ha.coprime_mul_left_right
  have haW : a.Coprime (Nat.lcm (2 ^ (e + 2)) M) :=
    (Nat.Coprime.mul_right (haN.coprime_dvd_right ((H.tower_dvd.mul_right _).mul_right _)) haM).coprime_dvd_right
      (Nat.lcm_dvd_mul _ _)
  refine ((H.isPrimOf_prim _).2 a haN).trans ?_
  show _ = χ (a : ZMod M)
  rw [HostRaw.dirAt, ← ZMod.coe_unitOfCoprime a haN, H.dir_unit, ← ZMod.coe_unitOfCoprime a haM, ← MulChar.coe_toUnitHom]
  refine congrArg Units.val ?_
  have h1 := thetaA_toA Ξ e χ hχ (ZMod.unitOfCoprime a haW)
  rw [unitsMap_unitOfCoprime, unitsMap_unitOfCoprime] at h1
  exact (theta_art Ξ e hH hc he hs χ hχ _).trans ((congrArg (fun v => thetaA Ξ e χ hχ ((data Ξ e).toA v))
    (unitsMap_unitOfCoprime ((data Ξ e).m_dvd q d) a haN)).trans h1)

/- English proof (translation)
Introduce `ψ hψ` and use `by obtain ⟨χ, hχ, rfl⟩ := (Level.mem_ofSub Ξ ψ).mp hψ exact ⟨_, theta_mem Ξ e χ hχ, (HostRaw.isPrimOf_iff _ _ _).mpr (prim_theta Ξ e hH hc he hs χ hχ)⟩`.
-/
theorem keptInXp : (host Ξ e hH hc he hs).KeptInXp (Level.ofSub Ξ).KEPT := fun ψ hψ => by
  obtain ⟨χ, hχ, rfl⟩ := (Level.mem_ofSub Ξ ψ).mp hψ
  exact ⟨_, theta_mem Ξ e χ hχ, (HostRaw.isPrimOf_iff _ _ _).mpr (prim_theta Ξ e hH hc he hs χ hχ)⟩

/- English proof (translation)
Use `⟨fun ψ h => (by cases h), fun _ h => ?_⟩` and prove the remaining obligations. Take `⟨χ, hχ, h1⟩` from `(Level.mem_ofSub Ξ _).mp ((HostRaw.kept_iff _ _ _).mp h)`. Rewrite `h1` using `[prim_theta Ξ e hH hc he hs χ hχ]`. Establish `: NeZero (QS Ξ e * q * d)` using `(data Ξ e).neZeroN hH`. Establish `: NeZero ((data Ξ e).m * q * d)` using `this`.

Establish `hco` using `coprime_QS Ξ e hH hc`. Take `⟨y, cy, hy⟩` from `D7.exists_sign hH.1 (D7.q4 hH) (-1)`. Take `⟨u, u1, u2, -⟩` from `exists_unit_three hco.coprime_mul_right_right hco.coprime_mul_left_right (D7.cop_qd hH) 1 y 1 (Nat.coprime_one_left _) cy (Nat.coprime_one_left _)`. Establish `h2` using `(theta_art Ξ e hH hc he hs χ hχ u).symm.trans (HostRaw.art_eq_of_prim_eq _ h1 u)`. Establish `h3 : thetaA Ξ e χ hχ ((data Ξ e).toA (ZMod.unitsMap ((data Ξ e).m_dvd q d) u)) = 1` using `(congrArg (fun v => thetaA Ξ e χ hχ ((data Ξ e).toA v)) ((unitsMap_eq_one_iff ((data Ξ e).m_dvd q d) u).mpr u1)).trans ((congrArg (thetaA Ξ e χ hχ) (map_one (data Ξ e).toA)).trans (map_one _))`.

Establish `h4 : ((((data Ξ e).art hH u).1.1 : ℤˣ) : ℤ) = -1` using `((data Ξ e).art_ps hH u).trans ((D7.jac_congr u2).trans hy)`. Establish `h5 : (1 : ℂ) = (((((data Ξ e).art hH u).1.1 : ℤˣ) : ℤ) : ℂ)` using `congrArg Units.val (h3.symm.trans h2)`. Rewrite `h5` using `[h4]`. Evaluate the numerical expressions using `at h5`.
-/
theorem exceptional_character_condition : (host Ξ e hH hc he hs).ExceptionalCharacterKept (Level.ofSub Ξ).KEPT (Level.ofSub Ξ).psK := by
  refine ⟨fun ψ h => (by cases h), fun _ h => ?_⟩
  obtain ⟨χ, hχ, h1⟩ := (Level.mem_ofSub Ξ _).mp ((HostRaw.kept_iff _ _ _).mp h)
  rw [prim_theta Ξ e hH hc he hs χ hχ] at h1
  have : NeZero (QS Ξ e * q * d) := (data Ξ e).neZeroN hH
  have : NeZero ((data Ξ e).m * q * d) := this
  have hco := coprime_QS Ξ e hH hc
  obtain ⟨y, cy, hy⟩ := D7.exists_sign hH.1 (D7.q4 hH) (-1)
  obtain ⟨u, u1, u2, -⟩ := exists_unit_three hco.coprime_mul_right_right hco.coprime_mul_left_right (D7.cop_qd hH)
    1 y 1 (Nat.coprime_one_left _) cy (Nat.coprime_one_left _)
  have h2 := (theta_art Ξ e hH hc he hs χ hχ u).symm.trans (HostRaw.art_eq_of_prim_eq _ h1 u)
  have h3 : thetaA Ξ e χ hχ ((data Ξ e).toA (ZMod.unitsMap ((data Ξ e).m_dvd q d) u)) = 1 :=
    (congrArg (fun v => thetaA Ξ e χ hχ ((data Ξ e).toA v))
      ((unitsMap_eq_one_iff ((data Ξ e).m_dvd q d) u).mpr u1)).trans
      ((congrArg (thetaA Ξ e χ hχ) (map_one (data Ξ e).toA)).trans (map_one _))
  have h4 : ((((data Ξ e).art hH u).1.1 : ℤˣ) : ℤ) = -1 := ((data Ξ e).art_ps hH u).trans ((D7.jac_congr u2).trans hy)
  have h5 : (1 : ℂ) = (((((data Ξ e).art hH u).1.1 : ℤˣ) : ℤ) : ℂ) := congrArg Units.val (h3.symm.trans h2)
  rw [h4] at h5
  norm_num at h5

/- English proof (translation)
Rewrite using `[o_eq]`. Both sides reduce to the same expression.
-/
theorem o_eq_level : (frame Ξ e).o = (Level.ofSub Ξ).o := by
  rw [o_eq]
  rfl

end Host

end AnyGrp

end Formalism.HC

end

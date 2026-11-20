import Development.AutomorphicArithmetic.CoprimeRanks.OfPInjective
import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.InertiaGaloisSymmetry.AnyLevel

open NumberField Formalism.HC Formalism.FrobeniusOrbits

namespace HostParam.Seam

/- English proof (translation)
Establish `h1 : Nat.card D.p1.ker = Nat.card (D.cl.ker.map D.ξ)`. Use `Nat.card_congr (Equiv.ofBijective (fun x => ⟨D.p2 x.1, ?_⟩) ⟨fun x y h => ?_, ?_⟩)` and prove the remaining obligations. Take `⟨⟨_, u, rfl⟩, hx⟩` from `x`. Conclude with `⟨u, hx, rfl⟩`. Establish `h2 : D.p2 x.1 = D.p2 y.1` using `congrArg Subtype.val h`.

Establish `h3 : D.p1 x.1 = D.p1 y.1` using `(x.2 : D.p1 x.1 = 1).trans (y.2 : D.p1 y.1 = 1).symm`. Conclude with `Subtype.ext (Subtype.ext (Prod.ext h3 h2))`. Introduce and unpack `⟨_, u, hu, rfl⟩`. Conclude with `⟨⟨D.eta.rangeRestrict u, hu⟩, rfl⟩`. Rewrite using `[D.ord_eq, ← h1, ← Subgroup.card_mul_index D.p1.ker, Subgroup.index_ker, MonoidHom.range_eq_top.mpr D.projection_surjective, Subgroup.card_top, (hostGroup D.e).2.2.2.2.2.2.1]`.
-/
private theorem ord_eq_mul (D : ModData) : D.frame.ord = Nat.card (D.cl.ker.map D.ξ) * 2 ^ D.e := by
  have h1 : Nat.card D.p1.ker = Nat.card (D.cl.ker.map D.ξ) := by
    refine Nat.card_congr (Equiv.ofBijective (fun x => ⟨D.p2 x.1, ?_⟩) ⟨fun x y h => ?_, ?_⟩)
    · obtain ⟨⟨_, u, rfl⟩, hx⟩ := x
      exact ⟨u, hx, rfl⟩
    · have h2 : D.p2 x.1 = D.p2 y.1 := congrArg Subtype.val h
      have h3 : D.p1 x.1 = D.p1 y.1 := (x.2 : D.p1 x.1 = 1).trans (y.2 : D.p1 y.1 = 1).symm
      exact Subtype.ext (Subtype.ext (Prod.ext h3 h2))
    · rintro ⟨_, u, hu, rfl⟩
      exact ⟨⟨D.eta.rangeRestrict u, hu⟩, rfl⟩
  rw [D.ord_eq, ← h1, ← Subgroup.card_mul_index D.p1.ker, Subgroup.index_ker,
    MonoidHom.range_eq_top.mpr D.projection_surjective, Subgroup.card_top, (hostGroup D.e).2.2.2.2.2.2.1]

/- English proof (translation)
The claim follows from `hcl_eq_hcl_iff (e := D.e) (u := ZMod.unitsMap D.tower u) (v := 1)`.
-/
private theorem cl_eq_one_iff (D : ModData) (u : (ZMod D.m)ˣ) :
    D.cl u = 1 ↔ ZMod.unitsMap D.tower u = 1 ∨ ZMod.unitsMap D.tower u = -1 :=
  hcl_eq_hcl_iff (e := D.e) (u := ZMod.unitsMap D.tower u) (v := 1)

/- English proof (translation)
Rewrite using `[← MonoidHom.comp_apply, ZMod.unitsMap_comp]`.
-/
private theorem unitsMap_unitsMap {a b c : ℕ} (h1 : a ∣ b) (h2 : b ∣ c) (u : (ZMod c)ˣ) :
    ZMod.unitsMap h1 (ZMod.unitsMap h2 u) = ZMod.unitsMap (h1.trans h2) u := by
  rw [← MonoidHom.comp_apply, ZMod.unitsMap_comp]

/- English proof (translation)
Take `⟨v, hv, rfl⟩` from `hb`. Take `⟨u, rfl⟩` from `ZMod.unitsMap_surjective (EvenGrp.QS_dvd Ξ (e + 1)) v`. Establish `hp : 2 ^ (e + 2) ∣ 2 ^ (e + 1 + 2)` using `pow_dvd_pow 2 (by omega)`. Establish `hd : Nat.lcm (2 ^ (e + 2)) M ∣ Nat.lcm (2 ^ (e + 1 + 2)) M` using `Nat.lcm_dvd (hp.trans (Nat.dvd_lcm_left _ _)) (Nat.dvd_lcm_right _ _)`. Use `⟨ZMod.unitsMap (EvenGrp.QS_dvd Ξ e) (ZMod.unitsMap hd u), ?_, ?_⟩` and prove the remaining obligations.

Establish `h1` using `(cl_eq_one_iff (AnyGrp.data Ξ (e + 1)) _).mp hv`. Use `(cl_eq_one_iff (AnyGrp.data Ξ e) _).mpr ?_` and prove the remaining obligations. Establish `h2 : ZMod.unitsMap (EvenGrp.good_QS Ξ e).2.1 (ZMod.unitsMap (EvenGrp.QS_dvd Ξ e) (ZMod.unitsMap hd u)) = ZMod.unitsMap hp (ZMod.unitsMap (EvenGrp.good_QS Ξ (e + 1)).2.1 (ZMod.unitsMap (EvenGrp.QS_dvd Ξ (e + 1)) u))`. Simplify using `only [unitsMap_unitsMap]`. Break down `h1 with h1 | h1` into its components or cases.

Conclude with `Or.inl (h2.trans ((congrArg (ZMod.unitsMap hp) h1).trans (map_one _)))`. Conclude with `Or.inr (h2.trans ((congrArg (ZMod.unitsMap hp) h1).trans (D7.unitsMap_neg_one hp)))`. Use `(EvenGrp.xi_unitsMap Ξ e _).trans (Eq.trans ?_ (EvenGrp.xi_unitsMap Ξ (e + 1) u).symm)` and prove the remaining obligations. Simplify using `only [EvenGrp.xiW, MonoidHom.comp_apply, unitsMap_unitsMap]`.
-/
private theorem step {M : ℕ} [NeZero M] (Ξ : Subgroup (DirichletCharacter ℂ M)) (e : ℕ) (b : EvenGrp.B Ξ)
    (hb : b ∈ (AnyGrp.data Ξ (e + 1)).cl.ker.map (AnyGrp.data Ξ (e + 1)).ξ) :
    b ∈ (AnyGrp.data Ξ e).cl.ker.map (AnyGrp.data Ξ e).ξ := by
  obtain ⟨v, hv, rfl⟩ := hb
  obtain ⟨u, rfl⟩ := ZMod.unitsMap_surjective (EvenGrp.QS_dvd Ξ (e + 1)) v
  have hp : 2 ^ (e + 2) ∣ 2 ^ (e + 1 + 2) := pow_dvd_pow 2 (by omega)
  have hd : Nat.lcm (2 ^ (e + 2)) M ∣ Nat.lcm (2 ^ (e + 1 + 2)) M :=
    Nat.lcm_dvd (hp.trans (Nat.dvd_lcm_left _ _)) (Nat.dvd_lcm_right _ _)
  refine ⟨ZMod.unitsMap (EvenGrp.QS_dvd Ξ e) (ZMod.unitsMap hd u), ?_, ?_⟩
  · have h1 := (cl_eq_one_iff (AnyGrp.data Ξ (e + 1)) _).mp hv
    refine (cl_eq_one_iff (AnyGrp.data Ξ e) _).mpr ?_
    have h2 : ZMod.unitsMap (EvenGrp.good_QS Ξ e).2.1 (ZMod.unitsMap (EvenGrp.QS_dvd Ξ e) (ZMod.unitsMap hd u)) =
        ZMod.unitsMap hp (ZMod.unitsMap (EvenGrp.good_QS Ξ (e + 1)).2.1 (ZMod.unitsMap (EvenGrp.QS_dvd Ξ (e + 1)) u)) := by
      simp only [unitsMap_unitsMap]
    rcases h1 with h1 | h1
    · exact Or.inl (h2.trans ((congrArg (ZMod.unitsMap hp) h1).trans (map_one _)))
    · exact Or.inr (h2.trans ((congrArg (ZMod.unitsMap hp) h1).trans (D7.unitsMap_neg_one hp)))
  · refine (EvenGrp.xi_unitsMap Ξ e _).trans (Eq.trans ?_ (EvenGrp.xi_unitsMap Ξ (e + 1) u).symm)
    simp only [EvenGrp.xiW, MonoidHom.comp_apply, unitsMap_unitsMap]

/- English proof (translation)
Set `U : ℕ → Subgroup (EvenGrp.B Ξ)` to `fun e => (AnyGrp.data Ξ e).cl.ker.map (AnyGrp.data Ξ e).ξ`. Establish `h0 : (AnyGrp.frame Ξ e).ord = Nat.card (U e) * 2 ^ e` using `ord_eq_mul (AnyGrp.data Ξ e)`. Establish `h1 : (AnyGrp.frame Ξ (e + 1)).ord = Nat.card (U (e + 1)) * 2 ^ (e + 1)` using `ord_eq_mul (AnyGrp.data Ξ (e + 1))`. Establish `h2 : Nat.card (U (e + 1)) ≤ Nat.card (U e)` using `Subgroup.card_le_of_le fun b hb => step Ξ e b hb`. Rewrite using `[h0, h1]`.

Combine the equalities or inequalities in the displayed calculation.
-/
private theorem ord_succ_le {M : ℕ} [NeZero M] (Ξ : Subgroup (DirichletCharacter ℂ M)) (e : ℕ) :
    (AnyGrp.frame Ξ (e + 1)).ord ≤ 2 * (AnyGrp.frame Ξ e).ord := by
  let U : ℕ → Subgroup (EvenGrp.B Ξ) := fun e => (AnyGrp.data Ξ e).cl.ker.map (AnyGrp.data Ξ e).ξ
  have h0 : (AnyGrp.frame Ξ e).ord = Nat.card (U e) * 2 ^ e := ord_eq_mul (AnyGrp.data Ξ e)
  have h1 : (AnyGrp.frame Ξ (e + 1)).ord = Nat.card (U (e + 1)) * 2 ^ (e + 1) := ord_eq_mul (AnyGrp.data Ξ (e + 1))
  have h2 : Nat.card (U (e + 1)) ≤ Nat.card (U e) := Subgroup.card_le_of_le fun b hb => step Ξ e b hb
  rw [h0, h1]
  calc Nat.card (U (e + 1)) * 2 ^ (e + 1) ≤ Nat.card (U e) * 2 ^ (e + 1) := Nat.mul_le_mul_right _ h2
    _ = _ := by ring

/- English proof (translation)
Set `U : Subgroup (EvenGrp.B Ξ)` to `(AnyGrp.data Ξ e).cl.ker.map (AnyGrp.data Ξ e).ξ`. Establish `h0 : (AnyGrp.frame Ξ e).ord = Nat.card U * 2 ^ e` using `ord_eq_mul (AnyGrp.data Ξ e)`. Rewrite using `[h0, ← EvenGrp.card_B]`. Conclude with `Nat.mul_le_mul_right _ (Subgroup.card_le_card_group _)`.
-/
private theorem ord_le {M : ℕ} [NeZero M] (Ξ : Subgroup (DirichletCharacter ℂ M)) (e : ℕ) :
    (AnyGrp.frame Ξ e).ord ≤ Nat.card Ξ * 2 ^ e := by
  let U : Subgroup (EvenGrp.B Ξ) := (AnyGrp.data Ξ e).cl.ker.map (AnyGrp.data Ξ e).ξ
  have h0 : (AnyGrp.frame Ξ e).ord = Nat.card U * 2 ^ e := ord_eq_mul (AnyGrp.data Ξ e)
  rw [h0, ← EvenGrp.card_B]
  exact Nat.mul_le_mul_right _ (Subgroup.card_le_card_group _)

/- English proof (translation)
Introduce `M _ Ξ`. Use `⟨ord_succ_le Ξ, fun e hev => ?_, fun e₀ W hW => ?_⟩` and prove the remaining obligations. Conclude with `(EvenData.ord_eq _).trans (ModData.ord_eq (AnyGrp.data Ξ e)).symm`. Establish `hex : ∃ k : ℕ, W ≤ (AnyGrp.frame Ξ (e₀ + k)).ord`. Take `⟨n, hn⟩` from `exists_nat_ge W`.

Use `⟨n, hn.trans ?_⟩` and prove the remaining obligations. Establish `h2 : 2 ^ (e₀ + n) ≤ (AnyGrp.frame Ξ (e₀ + n)).ord` using `(AnyGrp.frame Ξ (e₀ + n)).two_pow_le_ord`. Establish `h3 : e₀ + n < 2 ^ (e₀ + n)` using `Nat.lt_two_pow_self`. Conclude with `(by omega : n ≤ (AnyGrp.frame Ξ (e₀ + n)).ord)` after adjusting the coercions. Use `⟨e₀ + Nat.find hex, Nat.le_add_right _ _, Nat.find_spec hex, ?_⟩` and prove the remaining obligations.

Break down `h : Nat.find hex with _ | k` into its components or cases. Establish `h1 : ((AnyGrp.frame Ξ (e₀ + 0)).ord : ℝ) ≤ ((Nat.card Ξ * 2 ^ e₀ : ℕ) : ℝ)` using `Nat.cast_le.mpr (ord_le Ξ e₀)`. Establish `h2 : (0 : ℝ) ≤ ((Nat.card Ξ * 2 ^ e₀ : ℕ) : ℝ)` using `Nat.cast_nonneg _`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `h1` using `not_le.mp (Nat.find_min hex (by omega : k < Nat.find hex))`.

Establish `h2 : ((AnyGrp.frame Ξ (e₀ + (k + 1))).ord : ℝ) ≤ ((2 * (AnyGrp.frame Ξ (e₀ + k)).ord : ℕ) : ℝ)` using `Nat.cast_le.mpr (ord_succ_le Ξ (e₀ + k))`. Move the coercions through the operations in `at h2`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem anyFrame_window :
    ∀ {M : ℕ} [NeZero M] (Ξ : Subgroup (DirichletCharacter ℂ M)),
      (∀ e : ℕ, (AnyGrp.frame Ξ (e + 1)).ord ≤ 2 * (AnyGrp.frame Ξ e).ord) ∧
      (∀ (e : ℕ) (hev : ∀ χ ∈ Ξ, χ.Even), (EvenGrp.frame Ξ e hev).ord = (AnyGrp.frame Ξ e).ord) ∧
      ∀ (e₀ : ℕ) (W : ℝ), ((Nat.card Ξ * 2 ^ e₀ : ℕ) : ℝ) ≤ W →
        ∃ e : ℕ, e₀ ≤ e ∧ W ≤ (AnyGrp.frame Ξ e).ord ∧ ((AnyGrp.frame Ξ e).ord : ℝ) ≤ 2 * W := by
  intro M _ Ξ
  refine ⟨ord_succ_le Ξ, fun e hev => ?_, fun e₀ W hW => ?_⟩
  · exact (EvenData.ord_eq _).trans (ModData.ord_eq (AnyGrp.data Ξ e)).symm
  · classical
    have hex : ∃ k : ℕ, W ≤ (AnyGrp.frame Ξ (e₀ + k)).ord := by
      obtain ⟨n, hn⟩ := exists_nat_ge W
      refine ⟨n, hn.trans ?_⟩
      have h2 : 2 ^ (e₀ + n) ≤ (AnyGrp.frame Ξ (e₀ + n)).ord := (AnyGrp.frame Ξ (e₀ + n)).two_pow_le_ord
      have h3 : e₀ + n < 2 ^ (e₀ + n) := Nat.lt_two_pow_self
      exact_mod_cast (by omega : n ≤ (AnyGrp.frame Ξ (e₀ + n)).ord)
    refine ⟨e₀ + Nat.find hex, Nat.le_add_right _ _, Nat.find_spec hex, ?_⟩
    rcases h : Nat.find hex with _ | k
    · have h1 : ((AnyGrp.frame Ξ (e₀ + 0)).ord : ℝ) ≤ ((Nat.card Ξ * 2 ^ e₀ : ℕ) : ℝ) :=
        Nat.cast_le.mpr (ord_le Ξ e₀)
      have h2 : (0 : ℝ) ≤ ((Nat.card Ξ * 2 ^ e₀ : ℕ) : ℝ) := Nat.cast_nonneg _
      linarith
    · have h1 := not_le.mp (Nat.find_min hex (by omega : k < Nat.find hex))
      have h2 : ((AnyGrp.frame Ξ (e₀ + (k + 1))).ord : ℝ) ≤ ((2 * (AnyGrp.frame Ξ (e₀ + k)).ord : ℕ) : ℝ) :=
        Nat.cast_le.mpr (ord_succ_le Ξ (e₀ + k))
      push_cast at h2
      linarith

end HostParam.Seam

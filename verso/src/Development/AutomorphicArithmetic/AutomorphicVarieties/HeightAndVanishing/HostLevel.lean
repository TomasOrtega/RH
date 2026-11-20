import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.LayerLe
import Development.AutomorphicArithmetic.AutomorphicVarieties.CharacterLevelBounds.AbLevel

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.Base UpperTheory.Top UpperTheory.V.HV

/- English proof (translation)
Use `show ZMod.castHom h (ZMod g) (u : ZMod N) = _`. Rewrite using `[ZMod.castHom_apply, ZMod.cast_eq_val]`.
-/
private theorem coe_unitsMap {g N : ℕ} [NeZero N] (h : g ∣ N) (u : (ZMod N)ˣ) :
    ((ZMod.unitsMap h u : (ZMod g)ˣ) : ZMod g) = (((u : ZMod N).val : ℕ) : ZMod g) := by
  show ZMod.castHom h (ZMod g) (u : ZMod N) = _
  rw [ZMod.castHom_apply, ZMod.cast_eq_val]

/- English proof (translation)
Establish `key : v ∈ Subgroup.zpowers (-1 : (ZMod n)ˣ) ↔ v = 1 ∨ v = -1`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨k, rfl⟩`. Break down `Int.even_or_odd k with he | ho` into its components or cases. Use `left`.

Conclude with `he.neg_one_zpow`. Use `right`. Conclude with `ho.neg_one_zpow`. Introduce and unpack `(rfl | rfl)`. Conclude with `Subgroup.one_mem _`.

Conclude with `Subgroup.mem_zpowers _`. Rewrite using `[key, ← ZMod.natCast_eq_natCast_iff, ← ZMod.natCast_eq_natCast_iff]`. Use `push_cast`. Rewrite using `[← hv]`. Simplify using `only [Units.ext_iff, Units.val_one, Units.val_neg, eq_neg_iff_add_eq_zero]`.
-/
private theorem pm_iff {n : ℕ} (v : (ZMod n)ˣ) (a : ℕ) (hv : (v : ZMod n) = (a : ZMod n)) :
    (a ≡ 1 [MOD n] ∨ a + 1 ≡ 0 [MOD n]) ↔ v ∈ Subgroup.zpowers (-1 : (ZMod n)ˣ) := by
  have key : v ∈ Subgroup.zpowers (-1 : (ZMod n)ˣ) ↔ v = 1 ∨ v = -1 := by
    constructor
    · rintro ⟨k, rfl⟩
      rcases Int.even_or_odd k with he | ho
      · left
        exact he.neg_one_zpow
      · right
        exact ho.neg_one_zpow
    · rintro (rfl | rfl)
      · exact Subgroup.one_mem _
      · exact Subgroup.mem_zpowers _
  rw [key, ← ZMod.natCast_eq_natCast_iff, ← ZMod.natCast_eq_natCast_iff]
  push_cast
  rw [← hv]
  simp only [Units.ext_iff, Units.val_one, Units.val_neg, eq_neg_iff_add_eq_zero]

/- English proof (translation)
Use `haveI := Fact.mk hp`. Establish `ha : ((a : ℤ) : ZMod p) ≠ 0`. Use `push_cast`. Rewrite using `[← hv]`. Conclude with `v.ne_zero`.

Rewrite using `[← jacobiSym.legendreSym.to_jacobiSym, legendreSym.eq_one_iff p ha]`. Use `push_cast`. Rewrite using `[← hv]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨r, hr⟩`.

Establish `hr0 : r ≠ 0`. Introduce and unpack `rfl`. Conclude with `v.ne_zero (by simpa using hr)`. Use `⟨Units.mk0 r hr0, ?_⟩` and prove the remaining obligations. Use `ext`.

Simplify using `[hr, sq]`. Introduce and unpack `⟨w, hw⟩`. Use `⟨w, ?_⟩` and prove the remaining obligations. Rewrite using `[← hw]`. Simplify using `[sq]`.
-/
private theorem jac_iff {p : ℕ} (hp : p.Prime) (v : (ZMod p)ˣ) (a : ℕ) (hv : (v : ZMod p) = (a : ZMod p)) :
    jacobiSym (a : ℤ) p = 1 ↔ v ∈ (powMonoidHom 2 : (ZMod p)ˣ →* (ZMod p)ˣ).range := by
  haveI := Fact.mk hp
  have ha : ((a : ℤ) : ZMod p) ≠ 0 := by
    push_cast
    rw [← hv]
    exact v.ne_zero
  rw [← jacobiSym.legendreSym.to_jacobiSym, legendreSym.eq_one_iff p ha]
  push_cast
  rw [← hv]
  constructor
  · rintro ⟨r, hr⟩
    have hr0 : r ≠ 0 := by
      rintro rfl
      exact v.ne_zero (by simpa using hr)
    refine ⟨Units.mk0 r hr0, ?_⟩
    ext
    simp [hr, sq]
  · rintro ⟨w, hw⟩
    refine ⟨w, ?_⟩
    rw [← hw]
    simp [sq]

/- English proof (translation)
Introduce `h E _ _ hchi`. Establish `hc` using `(isCompField_ofChar h.chi h.ex h.q1 h.d E).mpr hchi`. Take `⟨H', hlev, hmem⟩` from `Chr.abLevel.2 (AbF.ofChar h.chi) h.ex h.q1 h.d E hc h.N h.two_pow_dvd h.q_dvd h.host_q1_dvd_N h.d_dvd`. Establish `hq1 : h.q1.Prime` using `h.pair.1`. Establish `hd : h.d.Prime` using `h.pair.2.2.1`.

Use `hlev using 1` and compare the differences between its conclusion and the goal. Use extensionality with `u`. Establish `hu : (u : ZMod h.N) = (((u : ZMod h.N).val : ℕ) : ZMod h.N)` using `(ZMod.natCast_zmod_val _).symm`. Rewrite using `[hmem u _ hu]`. Simplify using `only [Host.H, Subgroup.mem_inf, Subgroup.mem_comap]`.

Rewrite using `[← pm_iff (ZMod.unitsMap h.two_pow_dvd u) _ (coe_unitsMap _ u), ← jac_iff hq1 (ZMod.unitsMap h.host_q1_dvd_N u) _ (coe_unitsMap _ u), ← jac_iff hd (ZMod.unitsMap h.d_dvd u) _ (coe_unitsMap _ u)]`. Establish `hk : (ZMod.unitsMap h.q_dvd u) ∈ (MulChar.toUnitHom h.chi.χ).ker ↔ (AbF.ofChar h.chi).ker ((u : ZMod h.N).val)`. Prove the components needed by the constructor for the conclusion. Introduce `hv`. Conclude with `⟨_, hv, coe_unitsMap _ u⟩`.

Introduce and unpack `⟨w, hw, hwa⟩`. Establish `hweq : w = ZMod.unitsMap h.q_dvd u` using `Units.ext (hwa.trans (coe_unitsMap _ u).symm)`. Rewrite using `[← hweq]` and apply the resulting hypothesis. Rewrite using `[hk]`. The claim follows by propositional logic.
-/
theorem UpperTheory.V.HV.hostLevel :
    ∀ (h : Host) (E : Type) [Field E] [NumberField E], IsChiField h.chi h.ex h.q1 h.d E → Chr.HasLevel E h.N h.H := by
  intro h E _ _ hchi
  have hc := (isCompField_ofChar h.chi h.ex h.q1 h.d E).mpr hchi
  obtain ⟨H', hlev, hmem⟩ := Chr.abLevel.2 (AbF.ofChar h.chi) h.ex h.q1 h.d E hc h.N h.two_pow_dvd h.q_dvd h.host_q1_dvd_N h.d_dvd
  have hq1 : h.q1.Prime := h.pair.1
  have hd : h.d.Prime := h.pair.2.2.1
  convert hlev using 1
  ext u
  have hu : (u : ZMod h.N) = (((u : ZMod h.N).val : ℕ) : ZMod h.N) := (ZMod.natCast_zmod_val _).symm
  rw [hmem u _ hu]
  simp only [Host.H, Subgroup.mem_inf, Subgroup.mem_comap]
  rw [← pm_iff (ZMod.unitsMap h.two_pow_dvd u) _ (coe_unitsMap _ u),
    ← jac_iff hq1 (ZMod.unitsMap h.host_q1_dvd_N u) _ (coe_unitsMap _ u),
    ← jac_iff hd (ZMod.unitsMap h.d_dvd u) _ (coe_unitsMap _ u)]
  have hk : (ZMod.unitsMap h.q_dvd u) ∈ (MulChar.toUnitHom h.chi.χ).ker ↔
      (AbF.ofChar h.chi).ker ((u : ZMod h.N).val) := by
    constructor
    · intro hv
      exact ⟨_, hv, coe_unitsMap _ u⟩
    · rintro ⟨w, hw, hwa⟩
      have hweq : w = ZMod.unitsMap h.q_dvd u := Units.ext (hwa.trans (coe_unitsMap _ u).symm)
      rwa [← hweq]
  rw [hk]
  tauto

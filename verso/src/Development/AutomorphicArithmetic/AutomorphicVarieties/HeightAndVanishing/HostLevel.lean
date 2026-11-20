import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.LayerLe
import Development.AutomorphicArithmetic.AutomorphicVarieties.CharacterLevelBounds.AbLevel

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.Base UpperTheory.Top UpperTheory.V.HV

/- English proof (translation)
Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
private theorem coe_unitsMap {g N : ℕ} [NeZero N] (h : g ∣ N) (u : (ZMod N)ˣ) :
    ((ZMod.unitsMap h u : (ZMod g)ˣ) : ZMod g) = (((u : ZMod N).val : ℕ) : ZMod g) := by
  show ZMod.castHom h (ZMod g) (u : ZMod N) = _
  rw [ZMod.castHom_apply, ZMod.cast_eq_val]

/- English proof (translation)
Establish an intermediate fact. Prove the components needed by the constructor for the conclusion. Assume the hypotheses and unpack their components. Separate the alternatives or extract the components of the hypothesis. Assume the hypotheses and unpack their components.

Rewrite the conclusion using the stated equalities. Move the embeddings inside the algebraic operations. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. A detailed English derivation is pending.
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
Establish an intermediate fact. Move the embeddings inside the algebraic operations. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. Move the embeddings inside the algebraic operations.

Rewrite the conclusion using the stated equalities. Prove the components needed by the constructor for the conclusion. Assume the hypotheses and unpack their components. Establish an intermediate fact. Assume the hypotheses and unpack their components.

Reduce the conclusion to the remaining proof obligations. By extensionality, compare the relevant components. Simplify using the standard rewrite rules. Assume the hypotheses and unpack their components. Reduce the conclusion to the remaining proof obligations.

Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. A detailed English derivation is pending.
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
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Extract witnesses or component facts from the available result. Establish an intermediate fact. Establish an intermediate fact.

Apply an available result and prove the equalities needed to match it to the conclusion. By extensionality, compare the relevant components. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules.

Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Prove the components needed by the constructor for the conclusion. Fix the arbitrary inputs or assume the hypotheses. Supply the required witnesses or components.

Assume the hypotheses and unpack their components. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Use the resulting assumption. Rewrite the conclusion using the stated equalities. The claim follows by propositional logic.
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

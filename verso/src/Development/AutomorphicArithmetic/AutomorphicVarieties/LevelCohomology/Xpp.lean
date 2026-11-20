import Development.AutomorphicArithmetic.AutomorphicVarieties.LevelCohomology.DirGPowOne
import Development.AutomorphicArithmetic.AutomorphicVarieties.LevelCohomology.HcVanOf
import Development.AutomorphicArithmetic.AutomorphicVarieties.LevelCohomology.HcUnrOf
import Development.AutomorphicArithmetic.AutomorphicVarieties.LevelCohomology.HcXppOf
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.DvrFacts
import Development.AutomorphicArithmetic.AutomorphicVarieties.LevelCohomology.HcDefs
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.EtaKer
import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeDeformations.HostNumber
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing UpperTheory.V UpperTheory.V.Base UpperTheory.V.HV UpperTheory.V.X

/- English proof (translation)
Introduce `hX Ω _ _ _ l hlp c N _ e ψ o₁ hD q hq S A F hF`. Take `⟨d, f, n, _, φ, ξ, hx, hγ⟩` from `dir Ω l c N e ψ o₁ hD q hq`. Use `haveI : Finite (ResidueField c.O) := by haveI : IsLocalHom (algebraMap ℤ_[l] c.O) := (dvrFacts l c.O).2.2.1 haveI : Finite (ResidueField ℤ_[l]) := Finite.of_equiv _ (PadicInt.residueField (p := l)).symm.toEquiv`. Conclude with `Module.finite_of_finite (ResidueField ℤ_[l])`. Use `haveI : CharP (ResidueField c.O) l := (CharP.charP_iff_prime_eq_zero hlp.out).2 (by`.

Establish `h` using `(dvrFacts l c.O).2.2.1`. Establish `h1 : (l : c.O) ∈ maximalIdeal c.O`. Establish `: ¬ IsUnit (algebraMap ℤ_[l] c.O l)` using `fun h2 => PadicInt.irreducible_p.not_isUnit (h.map_nonunit _ h2)`. Rewrite `this` using `[map_natCast]`. Conclude with `this`.

Use `(residue_eq_zero_iff _).2 h1` as an intermediate fact. Rewrite using `[map_natCast] at this)` and apply the resulting hypothesis. Use `set γ : G ℚ Ω →* (ResidueField c.O)ˣ := (redChar Ω (residue c.O) (prodX φ ξ))⁻¹ with hγd`. Set `κ : G ℚ Ω →* ℤˣ × (ResidueField c.O)ˣ` to `(F.η.prod F.Ψbar).comp F.π`. Establish `hidx : ¬ l ∣ κ.ker.index`.

Rewrite using `[Subgroup.index_ker]`. Introduce `h`. Establish `h1` using `h.trans (Subgroup.card_subgroup_dvd_card κ.range)`. Rewrite `h1` using `[Nat.card_prod, Nat.card_units, Nat.card_eq_fintype_card, Fintype.card_units_int]`. Use `haveI := Fintype.ofFinite (ResidueField c.O)`.

Take `⟨r, -, hr⟩` from `FiniteField.card (ResidueField c.O) l`. Break down `hlp.out.dvd_mul.1 h1 with h2 | h2` into its components or cases. Conclude with `hD.l_odd ((Nat.prime_dvd_prime_iff_eq hlp.out Nat.prime_two).1 h2)`. Rewrite `h2` using `[Nat.card_eq_fintype_card, hr]`. Establish `h3 : l ∣ l ^ (r : ℕ)` using `dvd_pow_self l r.ne_zero`.

Establish `h4` using `Nat.dvd_sub h3 h2`. Rewrite `h4` using `[Nat.sub_sub_self (Nat.one_le_pow _ _ hlp.out.pos)]`. Conclude with `hlp.out.one_lt.ne' (Nat.dvd_one.1 h4)`. Establish `hπ : F.π = toGS Ω _` using `hF.π`. Set `γ' : UnitaryThreeInertia.Gam Ω S → ResidueField c.O` to `fun g => (((F.Ψbar g)⁻¹ : (ResidueField c.O)ˣ) : ResidueField c.O) ^ 2 * ((F.η g : ℤ) : ResidueField c.O)`.

Establish `hred : ∀ g, (redChar Ω (residue c.O) (prodX φ ξ) g : ResidueField c.O) = (F.Ψbar (F.π g) : ResidueField c.O) ^ 2 * ((F.η (F.π g) : ℤ) : ResidueField c.O)` using `fun g => by`. Rewrite using `[hγ, ← hF.Ψ, ← hF.η]`. Both sides reduce to the same expression. Establish `hγ' : ∀ g, γ' (toGS Ω _ g) = γ g` using `fun g => by`. Rewrite using `[← hπ, hγd, MonoidHom.inv_apply, Units.val_inv_eq_inv_val, hred]`.

Simplify using `only [γ', Units.val_inv_eq_inv_val, mul_inv, inv_pow]`. Apply the tactic sequence `rcases Int.units_eq_one_or (F.η (F.π g)) with h | h <;> simp [h]`. Establish `hK : κ.ker ≤ γ.ker` using `fun g hg => by`. Establish `h1 : F.η (F.π g) = 1` using `congrArg Prod.fst hg`. Establish `h2 : F.Ψbar (F.π g) = 1` using `congrArg Prod.snd hg`.

Use `Units.ext ?_` and prove the remaining obligations. Rewrite using `[← hγ', ← hπ]`. Simplify using `[γ', h1, h2]`. Establish `hl : (A F.vl).valuation (l : Ω) < 1`. Establish `h` using `(hF.isOver F.vl ((l : ℕ) : 𝓞 ℚ)).2 hF.vl`.

Simplify using `using h`. Establish `hV` using `vanOf Ω l _ γ (hX Ω l c _ (residue c.O) d f n φ ξ hx γ (.inr rfl)) {l} (fun _ => A F.vl) κ.ker (by simpa using ⟨Fact.out, hl⟩) inferInstance hidx`. Use `xppOf F γ' (fun g => by simp only [γ']; rw [mul_right_comm, ← mul_pow]; simp) fun z z1 z2 z3 z4 => ?_` and prove the remaining obligations. Establish `hz : ∀ g h, z (toGS Ω _ (g * h)) = z (toGS Ω _ g) + (γ g : ResidueField c.O) * z (toGS Ω _ h)` using `fun g h => by`. Rewrite using `[map_mul, z2, hγ']`.

Take `⟨m, hm⟩` from `hV (fun g => z (toGS Ω _ g)) (z1.comp_continuous (continuous_toGS Ω _)) hz (unrOf Ω _ γ κ.ker hK _ {l} z hz fun v hv => by`. Distinguish the cases in `h : (⟨v, hv⟩ : S) = F.vl`. Conclude with `.inl ⟨l, Finset.mem_singleton_self l, by have := hF.vl; rwa [← h] at this⟩`. Use `.inr ⟨A ⟨v, hv⟩, hF.isOver _, fun g hg hk => ?_⟩` and prove the remaining obligations. Establish `hgD : g ∈ F.D ⟨v, hv⟩` using `hF.D _ ▸ Ine_le_Dec _ hg`.

Establish `hgI : g ∈ F.I ⟨v, hv⟩` using `hF.I _ ▸ hg`. Rewrite using `[← hπ]`. Conclude with `z3 _ h ⟨g, hgD⟩ ⟨⟨hgI, congrArg Prod.fst hk⟩, congrArg Prod.snd hk⟩)`. Use the proof step `(fun v _ => by`. Take `⟨m, hm⟩` from `z4`.

Use `⟨m, fun g hg => ?_⟩` and prove the remaining obligations. Establish `hgD : g ∈ F.D F.vl` using `hF.D _ ▸ hg`. Rewrite using `[← hγ', ← hπ]`. Conclude with `hm ⟨g, hgD⟩)`. Use `⟨m, fun g => ?_⟩` and prove the remaining obligations.

Take `⟨g, rfl⟩` from `QuotientGroup.mk_surjective g`. Conclude with `(hm g).trans (by rw [← hγ']; rfl)`.
-/
theorem UpperTheory.V.X.xpp :
    CorX → UnitaryThreeInertia.HostXpp := by
  intro hX Ω _ _ _ l hlp c N _ e ψ o₁ hD q hq S A F hF
  obtain ⟨d, f, n, _, φ, ξ, hx, hγ⟩ := dir Ω l c N e ψ o₁ hD q hq
  haveI : Finite (ResidueField c.O) := by
    haveI : IsLocalHom (algebraMap ℤ_[l] c.O) := (dvrFacts l c.O).2.2.1
    haveI : Finite (ResidueField ℤ_[l]) := Finite.of_equiv _ (PadicInt.residueField (p := l)).symm.toEquiv
    exact Module.finite_of_finite (ResidueField ℤ_[l])
  haveI : CharP (ResidueField c.O) l := (CharP.charP_iff_prime_eq_zero hlp.out).2 (by
    have h := (dvrFacts l c.O).2.2.1
    have h1 : (l : c.O) ∈ maximalIdeal c.O := by
      have : ¬ IsUnit (algebraMap ℤ_[l] c.O l) := fun h2 => PadicInt.irreducible_p.not_isUnit (h.map_nonunit _ h2)
      rw [map_natCast] at this
      exact this
    have := (residue_eq_zero_iff _).2 h1
    rwa [map_natCast] at this)
  set γ : G ℚ Ω →* (ResidueField c.O)ˣ := (redChar Ω (residue c.O) (prodX φ ξ))⁻¹ with hγd
  let κ : G ℚ Ω →* ℤˣ × (ResidueField c.O)ˣ := (F.η.prod F.Ψbar).comp F.π
  have hidx : ¬ l ∣ κ.ker.index := by
    rw [Subgroup.index_ker]
    intro h
    have h1 := h.trans (Subgroup.card_subgroup_dvd_card κ.range)
    rw [Nat.card_prod, Nat.card_units, Nat.card_eq_fintype_card, Fintype.card_units_int] at h1
    haveI := Fintype.ofFinite (ResidueField c.O)
    obtain ⟨r, -, hr⟩ := FiniteField.card (ResidueField c.O) l
    rcases hlp.out.dvd_mul.1 h1 with h2 | h2
    · exact hD.l_odd ((Nat.prime_dvd_prime_iff_eq hlp.out Nat.prime_two).1 h2)
    · rw [Nat.card_eq_fintype_card, hr] at h2
      have h3 : l ∣ l ^ (r : ℕ) := dvd_pow_self l r.ne_zero
      have h4 := Nat.dvd_sub h3 h2
      rw [Nat.sub_sub_self (Nat.one_le_pow _ _ hlp.out.pos)] at h4
      exact hlp.out.one_lt.ne' (Nat.dvd_one.1 h4)
  have hπ : F.π = toGS Ω _ := hF.π
  let γ' : UnitaryThreeInertia.Gam Ω S → ResidueField c.O := fun g =>
    (((F.Ψbar g)⁻¹ : (ResidueField c.O)ˣ) : ResidueField c.O) ^ 2 * ((F.η g : ℤ) : ResidueField c.O)
  have hred : ∀ g, (redChar Ω (residue c.O) (prodX φ ξ) g : ResidueField c.O) =
      (F.Ψbar (F.π g) : ResidueField c.O) ^ 2 * ((F.η (F.π g) : ℤ) : ResidueField c.O) := fun g => by
    rw [hγ, ← hF.Ψ, ← hF.η]; rfl
  have hγ' : ∀ g, γ' (toGS Ω _ g) = γ g := fun g => by
    rw [← hπ, hγd, MonoidHom.inv_apply, Units.val_inv_eq_inv_val, hred]
    simp only [γ', Units.val_inv_eq_inv_val, mul_inv, inv_pow]
    rcases Int.units_eq_one_or (F.η (F.π g)) with h | h <;> simp [h]
  have hK : κ.ker ≤ γ.ker := fun g hg => by
    have h1 : F.η (F.π g) = 1 := congrArg Prod.fst hg
    have h2 : F.Ψbar (F.π g) = 1 := congrArg Prod.snd hg
    refine Units.ext ?_
    rw [← hγ', ← hπ]
    simp [γ', h1, h2]
  have hl : (A F.vl).valuation (l : Ω) < 1 := by
    have h := (hF.isOver F.vl ((l : ℕ) : 𝓞 ℚ)).2 hF.vl
    simpa using h
  have hV := vanOf Ω l _ γ (hX Ω l c _ (residue c.O) d f n φ ξ hx γ (.inr rfl)) {l} (fun _ => A F.vl) κ.ker
    (by simpa using ⟨Fact.out, hl⟩) inferInstance hidx
  refine xppOf F γ' (fun g => by simp only [γ']; rw [mul_right_comm, ← mul_pow]; simp) fun z z1 z2 z3 z4 => ?_
  have hz : ∀ g h, z (toGS Ω _ (g * h)) = z (toGS Ω _ g) + (γ g : ResidueField c.O) * z (toGS Ω _ h) := fun g h => by
    rw [map_mul, z2, hγ']
  obtain ⟨m, hm⟩ := hV (fun g => z (toGS Ω _ g)) (z1.comp_continuous (continuous_toGS Ω _)) hz
    (unrOf Ω _ γ κ.ker hK _ {l} z hz fun v hv => by
      by_cases h : (⟨v, hv⟩ : S) = F.vl
      · exact .inl ⟨l, Finset.mem_singleton_self l, by have := hF.vl; rwa [← h] at this⟩
      · refine .inr ⟨A ⟨v, hv⟩, hF.isOver _, fun g hg hk => ?_⟩
        have hgD : g ∈ F.D ⟨v, hv⟩ := hF.D _ ▸ Ine_le_Dec _ hg
        have hgI : g ∈ F.I ⟨v, hv⟩ := hF.I _ ▸ hg
        rw [← hπ]
        exact z3 _ h ⟨g, hgD⟩ ⟨⟨hgI, congrArg Prod.fst hk⟩, congrArg Prod.snd hk⟩)
    (fun v _ => by
      obtain ⟨m, hm⟩ := z4
      refine ⟨m, fun g hg => ?_⟩
      have hgD : g ∈ F.D F.vl := hF.D _ ▸ hg
      rw [← hγ', ← hπ]
      exact hm ⟨g, hgD⟩)
  refine ⟨m, fun g => ?_⟩
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective g
  exact (hm g).trans (by rw [← hγ']; rfl)

import Mathlib
import Formalism.LocalToGlobal.ProjectiveLattices.HasDataCondition
import Formalism.LocalToGlobal.ProjectiveLattices.LatPAddRight
import Formalism.LocalToGlobal.ProjectiveLattices.FamilyUniformisationBasePointOrthogonalBis
import Formalism.LocalToGlobal.ProjectiveLattices.ParCanon
import Formalism.LocalToGlobal.ProjectiveLattices.ExistsParameterConditions
import Formalism.LocalToGlobal.ProjectiveLattices.DepLaws
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ThExprUniqOfChartIndep2
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsLocalModelSystemAmpleFramesFullLevelStatement
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.HomExtensionSemiAbelianDiscreteValuationRingStatement
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsFullLevelAmpleModelOfSemistableReductionStatement
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.SemistableReductionPpavPadicFieldStatement
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ModuliSchemeLevelMapsHeckePointsStatement
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.AllUniformizationLawsHoldStatement
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsTransitionMapRaisedModelsStatement
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.SemiAbelianHomExtendsUniquelyOverDvrStatement
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.TypeFnPeriodExistModuliNonemptyStatement
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.CmModuliConsequenceOfAbelianSchemeLawsStatement
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.CoefficientFieldIntegersDedekindFractionField
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.PrimeToPartLevelExistsUniqueMono
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.ExistsValuationSubringComapEqNonunits
import Development.AbelianVarietyTheory.Counterexamples.ModuliSurvey.ExistsGoodLevel

open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain IsLocalRing ReciprocityTheory.ChartRestriction.G.Geo.Tor
  Formalism.L2.Pj GlobalTheory.Models

namespace GlobalTheory.LocalData.Towers

/- English proof (translation)
Break down `Nat.eq_zero_or_pos n with rfl | hn` into its components or cases. Establish `: zeta 0 = 1` using `by simp [zeta]`. Rewrite using `[this]`. Conclude with `isIntegral_one`. Establish `h` using `Complex.isPrimitiveRoot_exp n hn.ne'`.

Conclude with `(h.isIntegral hn).tower_top`.
-/
theorem isIntegral_rat_zeta_of_coeff (n : ℕ) : IsIntegral ℚ (zeta n) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · have : zeta 0 = 1 := by simp [zeta]
    rw [this]; exact isIntegral_one
  · have h := Complex.isPrimitiveRoot_exp n hn.ne'
    exact (h.isIntegral hn).tower_top

/- English proof (translation)
Introduce `E _ _ _ H l s hs`. Set `b` to `Module.finBasis ℚ E`. Set `S : Set ℂ` to `(s : Set ℂ) ∪ Set.range (fun p : (E →+* ℂ) × Fin (Module.finrank ℚ E) => p.1 (b p.2)) ∪ {zeta l.M', H.rt0, zeta l.A}`. Establish `hfin : S.Finite` using `((s.finite_toSet).union (Set.finite_range _)).union (Set.toFinite _)`. Use `haveI : Finite S := hfin.to_subtype`.

Establish `hint : ∀ x ∈ S, IsIntegral ℚ x`. Introduce and unpack `x ((hx | ⟨p, rfl⟩) | hx)`. Conclude with `(hs x hx).isIntegral`. Conclude with `(Algebra.IsIntegral.isIntegral (R := ℚ) (b p.2)).map p.1.toRatAlgHom`. Break down `hx with rfl | rfl | rfl` into its components or cases.

Conclude with `isIntegral_rat_zeta_of_coeff _`. Use `IsIntegral.of_pow (n := 2) (by norm_num) ?_` and prove the remaining obligations. Rewrite using `[H.sqrt_neg_disc_sq]`. Conclude with `(isIntegral_natCast _).neg`. Conclude with `isIntegral_rat_zeta_of_coeff _`.

Establish `hsub : S ⊆ IntermediateField.adjoin ℚ S` using `IntermediateField.subset_adjoin _ _`. Use `⟨⟨IntermediateField.adjoin ℚ S, IntermediateField.finiteDimensional_adjoin hint, ?_, ?_, ?_⟩, ?_⟩` and prove the remaining obligations. Introduce `τ a`. Rewrite using `[← b.sum_repr a, map_sum]`. Use `sum_mem fun i _ => ?_` and prove the remaining obligations.

Rewrite using `[map_rat_smul]`. Conclude with `IntermediateField.smul_mem _ (hsub (Or.inl (Or.inr ⟨(τ, i), rfl⟩)))`. Conclude with `hsub (Or.inr (by simp))`. Use `IntermediateField.adjoin.mono _ _ _ ?_` and prove the remaining obligations. Introduce `x hx`.

Conclude with `Or.inr (Or.inr hx)`. Introduce `z hz`. Conclude with `hsub (Or.inl (Or.inl hz))`.
-/
theorem exists_coeff_containing :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (l : Level H) (s : Finset ℂ), (∀ z ∈ s, IsAlgebraic ℚ z) → ∃ c : Coeff l, ∀ z ∈ s, z ∈ c.F := by
  intro E _ _ _ H l s hs
  classical
  let b := Module.finBasis ℚ E
  let S : Set ℂ := (s : Set ℂ) ∪ Set.range (fun p : (E →+* ℂ) × Fin (Module.finrank ℚ E) => p.1 (b p.2)) ∪
    {zeta l.M', H.rt0, zeta l.A}
  have hfin : S.Finite := ((s.finite_toSet).union (Set.finite_range _)).union (Set.toFinite _)
  haveI : Finite S := hfin.to_subtype
  have hint : ∀ x ∈ S, IsIntegral ℚ x := by
    rintro x ((hx | ⟨p, rfl⟩) | hx)
    · exact (hs x hx).isIntegral
    · exact (Algebra.IsIntegral.isIntegral (R := ℚ) (b p.2)).map p.1.toRatAlgHom
    · rcases hx with rfl | rfl | rfl
      · exact isIntegral_rat_zeta_of_coeff _
      · refine IsIntegral.of_pow (n := 2) (by norm_num) ?_
        rw [H.sqrt_neg_disc_sq]
        exact (isIntegral_natCast _).neg
      · exact isIntegral_rat_zeta_of_coeff _
  have hsub : S ⊆ IntermediateField.adjoin ℚ S := IntermediateField.subset_adjoin _ _
  refine ⟨⟨IntermediateField.adjoin ℚ S, IntermediateField.finiteDimensional_adjoin hint, ?_, ?_, ?_⟩, ?_⟩
  · intro τ a
    rw [← b.sum_repr a, map_sum]
    refine sum_mem fun i _ => ?_
    rw [map_rat_smul]
    exact IntermediateField.smul_mem _ (hsub (Or.inl (Or.inr ⟨(τ, i), rfl⟩)))
  · exact hsub (Or.inr (by simp))
  · refine IntermediateField.adjoin.mono _ _ _ ?_
    intro x hx
    exact Or.inr (Or.inr hx)
  · intro z hz
    exact hsub (Or.inl (Or.inl hz))

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}

/- English proof (translation)
Take `⟨W, hWe, hWn⟩` from `GlobalTheory.Reg.exists_valuationSubring_comap_eq_nonunits c.F.val.toRingHom (v.valuation c.F).valuationSubring`. Establish `hpU : (p : c.F) ∈ (v.valuation c.F).valuationSubring.nonunits`. Rewrite using `[ValuationSubring.mem_nonunits_iff, ← (Valuation.isEquiv_valuation_valuationSubring (v.valuation c.F)).lt_one_iff_lt_one]`. Use `(v.valuation_lt_one_iff_mem (K := c.F) (p : 𝓞 c.F)).2 hv` as an intermediate fact. Simplify using `using this`.

Conclude with `⟨W, by simpa using hWn _ hpU, hWe⟩`.
-/
theorem exists_valuationSubring {l : Level H} (c : Coeff l) (p : ℕ) (v : HeightOneSpectrum (𝓞 c.F))
    (hv : (p : 𝓞 c.F) ∈ v.asIdeal) :
    ∃ W : ValuationSubring ℂ, (p : ℂ) ∈ W.nonunits ∧ c.V W = (v.valuation c.F).valuationSubring := by
  obtain ⟨W, hWe, hWn⟩ := GlobalTheory.Reg.exists_valuationSubring_comap_eq_nonunits c.F.val.toRingHom
    (v.valuation c.F).valuationSubring
  have hpU : (p : c.F) ∈ (v.valuation c.F).valuationSubring.nonunits := by
    rw [ValuationSubring.mem_nonunits_iff,
      ← (Valuation.isEquiv_valuation_valuationSubring (v.valuation c.F)).lt_one_iff_lt_one]
    have := (v.valuation_lt_one_iff_mem (K := c.F) (p : 𝓞 c.F)).2 hv
    simpa using this
  exact ⟨W, by simpa using hWn _ hpU, hWe⟩

/- English proof (translation)
Substitute `h` using the available equality. Use `⟨Subtype.val_injective, fun x => ⟨?_, fun hx => ⟨⟨x, hx⟩, rfl⟩⟩⟩` and prove the remaining obligations. Introduce and unpack `⟨y, rfl⟩`. Conclude with `y.2`.
-/
theorem baseAt_of_eq {l : Level H} {c : Coeff l} {v : HeightOneSpectrum (𝓞 c.F)} {V : ValuationSubring c.F}
    (h : V = (v.valuation c.F).valuationSubring) : PointsOfFlagModel.BaseAt v V.subtype := by
  subst h
  refine ⟨Subtype.val_injective, fun x => ⟨?_, fun hx => ⟨⟨x, hx⟩, rfl⟩⟩⟩
  rintro ⟨y, rfl⟩
  exact y.2

/- English proof (translation)
Use `haveI := c.fin`. Set `b` to `Module.finBasis ℚ c.F`. Take `⟨c₂, h⟩` from `exists_coeff_containing E H l₂ (Finset.univ.image fun i => ((b i : c.F) : ℂ)) (by`. Introduce `z hz`. Take `⟨i, -, rfl⟩` from `Finset.mem_image.1 hz`.

Conclude with `(Algebra.IsAlgebraic.isAlgebraic (R := ℚ) (b i)).algHom c.F.val)`. Use `⟨c₂, fun x hx => ?_⟩` and prove the remaining obligations. Establish `key : ∀ y : c.F, (y : ℂ) ∈ c₂.F`. Introduce `y`. Establish `hy : y ∈ Submodule.span ℚ (Set.range b)` using `b.span_eq ▸ Submodule.mem_top`.

Proceed by induction on `hy using Submodule.span_induction with`. Consider the case `mem z hz`. Take `⟨i, rfl⟩` from `hz`. Conclude with `h _ (Finset.mem_image_of_mem _ (Finset.mem_univ i))`. Consider the case `zero => exact zero_mem _`.

Consider the case `add y z _ _ hy hz => exact add_mem hy hz`. Consider the case `smul a y _ hy`. Establish `e : ((a • y : c.F) : ℂ) = (a : ℂ) * (y : ℂ)` using `by simp [Rat.smul_def]`. Rewrite using `[e]`. Conclude with `mul_mem (SubfieldClass.ratCast_mem _ a) hy`.

Conclude with `key ⟨x, hx⟩`.
-/
theorem exists_coeff_ge {l : Level H} (c : Coeff l) (l₂ : Level H) : ∃ c₂ : Coeff l₂, c.F ≤ c₂.F := by
  classical
  haveI := c.fin
  let b := Module.finBasis ℚ c.F
  obtain ⟨c₂, h⟩ := exists_coeff_containing E H l₂ (Finset.univ.image fun i => ((b i : c.F) : ℂ)) (by
    intro z hz
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 hz
    exact (Algebra.IsAlgebraic.isAlgebraic (R := ℚ) (b i)).algHom c.F.val)
  refine ⟨c₂, fun x hx => ?_⟩
  have key : ∀ y : c.F, (y : ℂ) ∈ c₂.F := by
    intro y
    have hy : y ∈ Submodule.span ℚ (Set.range b) := b.span_eq ▸ Submodule.mem_top
    induction hy using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨i, rfl⟩ := hz
      exact h _ (Finset.mem_image_of_mem _ (Finset.mem_univ i))
    | zero => exact zero_mem _
    | add y z _ _ hy hz => exact add_mem hy hz
    | smul a y _ hy =>
      have e : ((a • y : c.F) : ℂ) = (a : ℂ) * (y : ℂ) := by simp [Rat.smul_def]
      rw [e]
      exact mul_mem (SubfieldClass.ratCast_mem _ a) hy
  exact key ⟨x, hx⟩

def deeper (l : Level H) (k : ℕ) (hk : 0 < k) : Level H :=
  { l with A := k * l.A, A_pos := Nat.mul_pos hk l.A_pos }

/- English proof (translation)
Assemble the required witnesses or components as `⟨dvd_rfl, le_rfl, Dvd.intro_left k rfl⟩`.
-/
theorem dvd_deeper (l : Level H) (k : ℕ) (hk : 0 < k) : l.Dvd (deeper l k hk) :=
  ⟨dvd_rfl, le_rfl, Dvd.intro_left k rfl⟩

variable {D : Datum H}

/- English proof (translation)
Take `⟨L1, L2, L3, -⟩` from `GlobalTheory.T.all_uniformization_laws_hold`. Take `⟨l₀, h₀, r₀⟩` from `S.raises p W hp hW i`. Take `⟨l₀', h₀', r₀'⟩` from `S.raises p W' hp hW' i'`. Take `⟨-, hsp, hmono⟩` from `GlobalTheory.Models.primeToPart_spec E H p hp`. Set `b : i.c.V W →+* i'.c.V W'` to `((IntermediateField.inclusion hc).toRingHom.comp (i.c.V W).subtype).codRestrict (i'.c.V W') fun x => by`.

Establish `hx : (x : i.c.F) ∈ i.c.V W'` using `he ▸ x.2`. Conclude with `hx`. Take `⟨π, hπ⟩` from `GlobalTheory.T.exists_transition_map_raised_models GlobalTheory.T.semiAbelian_hom_extends_uniquely_over_dvr L1 L2 L3 E H D Xo _ _ (S.T (S.ch p)) hN l₀ l₀' _ _ i.l i.c _ _ (S.Y p W hp hW i) i'.l i'.c _ _ (S.Y p W' hp hW' i') b (S.aux _).1.pos ⟨_, dvd_rfl⟩ (hmono _ _ _ _ h₀ h₀' hl) …`. Conclude with `⟨b, π, hπ⟩`.
-/
theorem exists_transition {Xo : ∀ l : Level H, Moduli D l} (S : System Xo) (hN : ToroidalLevelCompatibility (H := H) (D := D)) {p : ℕ}
    (hp : p.Prime) {W W' : ValuationSubring ℂ} (hW : (p : ℂ) ∈ W.nonunits) (hW' : (p : ℂ) ∈ W'.nonunits)
    (i i' : Idx H p) (hl : i.l.Dvd i'.l) (hc : i.c.F ≤ i'.c.F) (he : i.c.V W = i.c.V W') :
    ∃ (b : i.c.V W →+* i'.c.V W') (π : (S.Y p W' hp hW' i').X ⟶ (S.Y p W hp hW i).X),
      IsTransition (S.Y p W hp hW i) (S.Y p W' hp hW' i') b π := by
  obtain ⟨L1, L2, L3, -⟩ := GlobalTheory.T.all_uniformization_laws_hold
  obtain ⟨l₀, h₀, r₀⟩ := S.raises p W hp hW i
  obtain ⟨l₀', h₀', r₀'⟩ := S.raises p W' hp hW' i'
  obtain ⟨-, hsp, hmono⟩ := GlobalTheory.Models.primeToPart_spec E H p hp
  let b : i.c.V W →+* i'.c.V W' :=
    ((IntermediateField.inclusion hc).toRingHom.comp (i.c.V W).subtype).codRestrict (i'.c.V W') fun x => by
      have hx : (x : i.c.F) ∈ i.c.V W' := he ▸ x.2
      exact hx
  obtain ⟨π, hπ⟩ := GlobalTheory.T.exists_transition_map_raised_models GlobalTheory.T.semiAbelian_hom_extends_uniquely_over_dvr L1 L2 L3 E H D Xo _ _ (S.T (S.ch p)) hN l₀ l₀' _ _ i.l i.c _ _
    (S.Y p W hp hW i) i'.l i'.c _ _ (S.Y p W' hp hW' i') b (S.aux _).1.pos ⟨_, dvd_rfl⟩
    (hmono _ _ _ _ h₀ h₀' hl) (hsp _ _ h₀).1 (hsp _ _ h₀').1 hl hc
    ((GlobalTheory.CoeffRings.coeff_isDedFrac E H i.l i.c).2.2.2 p W hp hW).1
    ((GlobalTheory.CoeffRings.coeff_isDedFrac E H i'.l i'.c).2.2.2 p W' hp hW').1 (fun _ => rfl) r₀ r₀'
  exact ⟨b, π, hπ⟩

/- English proof (translation)
Establish `hN` using `(GlobalTheory.T.moduliScheme_levelMaps_heckePoints'.2 E H D hD).1`. Establish `hne : ∀ (l : Level H) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model (Xo l) c β), Nonempty Y.X` using `fun l c O _ β Y => ((GlobalTheory.T.typeFn_period_exist_moduli_nonempty E H D).2.2 GlobalTheory.T.cmModuli_consequence_of_abelianSchemeLaws hD l (Xo l) c).map fun x => Y.j x`. Set `lv : ℕ → Level H` to `fun n => deeper l (p ^ n) (pow_pos hp.pos n)`. Use `choose cN hcN using fun n => exists_coeff_ge c (lv n)`. Use `choose W hW hWe using fun v : PointsOfFlagModel.abelian₂ p c => exists_valuationSubring c p v.1 v.2`.

Use `choose WN hWN hWNe using fun n (w : PointsOfFlagModel.abelian₂ p (cN n)) => exists_valuationSubring (cN n) p w.1 w.2`. Use `⟨{ O := fun v => c.V (W v) β := fun v => (c.V (W v)).subtype Y := fun v => S.Y p (W v) hp (hW v) ⟨l, c, hg⟩ lvN := lv XoN := fun n => Xo (lv n) cN := cN ON := fun n w => (cN n).V (WN n w) βN := fun n w => ((cN n).V (WN n w)).subtype YN := fun n w => S.Y p (WN n w) hp (hWN n w) ⟨l …` and prove the remaining obligations. Take `⟨v, hv, hve⟩` from `GlobalTheory.GlobalModelGuards.exists_prime_eq c (WN n w) p hp (hWN n w)`. Rewrite `hve` using `[HeightOneSpectrum.valuationSubringAtPrime_eq_valuationSubring]`. Conclude with `⟨⟨v, hv⟩, exists_transition S hN hp (hW ⟨v, hv⟩) (hWN n w) ⟨l, c, hg⟩ ⟨lv n, cN n, hg⟩ (dvd_deeper l _ (pow_pos hp.pos n)) (hcN n) ((hWe ⟨v, hv⟩).trans hve)⟩`.
-/
theorem exists_towerAt {Xo : ∀ l : Level H, Moduli D l} (S : System Xo) (hD : 1 ≤ D.p + D.q) (l : Level H)
    (c : Coeff l) {p : ℕ} (hp : p.Prime) (hg : l.GoodAt p) : ∃ Tw : PointsOfFlagModel.Tower p (Xo l) c, PointsOfFlagModel.TowerAt Tw := by
  have hN := (GlobalTheory.T.moduliScheme_levelMaps_heckePoints'.2 E H D hD).1
  have hne : ∀ (l : Level H) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model (Xo l) c β),
      Nonempty Y.X := fun l c O _ β Y =>
    ((GlobalTheory.T.typeFn_period_exist_moduli_nonempty E H D).2.2 GlobalTheory.T.cmModuli_consequence_of_abelianSchemeLaws hD l (Xo l) c).map fun x => Y.j x
  let lv : ℕ → Level H := fun n => deeper l (p ^ n) (pow_pos hp.pos n)
  choose cN hcN using fun n => exists_coeff_ge c (lv n)
  choose W hW hWe using fun v : PointsOfFlagModel.abelian₂ p c => exists_valuationSubring c p v.1 v.2
  choose WN hWN hWNe using fun n (w : PointsOfFlagModel.abelian₂ p (cN n)) => exists_valuationSubring (cN n) p w.1 w.2
  refine ⟨{ O := fun v => c.V (W v)
            β := fun v => (c.V (W v)).subtype
            Y := fun v => S.Y p (W v) hp (hW v) ⟨l, c, hg⟩
            lvN := lv
            XoN := fun n => Xo (lv n)
            cN := cN
            ON := fun n w => (cN n).V (WN n w)
            βN := fun n w => ((cN n).V (WN n w)).subtype
            YN := fun n w => S.Y p (WN n w) hp (hWN n w) ⟨lv n, cN n, hg⟩ },
    fun v => ⟨baseAt_of_eq (hWe v), hne _ _ _ _ _⟩,
    fun n => ⟨dvd_deeper l _ (pow_pos hp.pos n), dvd_rfl, fun w => ⟨⟨baseAt_of_eq (hWNe n w), hne _ _ _ _ _⟩, ?_⟩⟩⟩
  obtain ⟨v, hv, hve⟩ := GlobalTheory.GlobalModelGuards.exists_prime_eq c (WN n w) p hp (hWN n w)
  rw [HeightOneSpectrum.valuationSubringAtPrime_eq_valuationSubring] at hve
  exact ⟨⟨v, hv⟩, exists_transition S hN hp (hW ⟨v, hv⟩) (hWN n w) ⟨l, c, hg⟩ ⟨lv n, cN n, hg⟩ (dvd_deeper l _ (pow_pos hp.pos n))
    (hcN n) ((hWe ⟨v, hv⟩).trans hve)⟩

/- English proof (translation)
Use `choose q hq hqv using fun v : PointsOfFlagModel.abelian₂ p c => GlobalTheory.Reg.exists_prime_natCast_mem v.1`. Use `choose W hW _ using fun v : PointsOfFlagModel.abelian₂ p c => exists_valuationSubring c (q v) v.1 (hqv v)`. Conclude with `⟨{ O := fun v => c.V (W v) β := fun v => (c.V (W v)).subtype Y := fun v => S.Y (q v) (W v) (hq v) (hW v) ⟨l, c, hg _ (hq v)⟩ lvN := fun _ => l XoN := fun _ => Xo l cN := fun _ => c ON := fun _ v => c.V (W v) βN := fun _ v => (c.V (W v)).subtype YN := fun _ v => S.Y (q v) (W v) (h …`.
-/
theorem nonempty_tower {Xo : ∀ l : Level H, Moduli D l} (S : System Xo) (l : Level H) (c : Coeff l)
    (hg : ∀ p : ℕ, p.Prime → l.GoodAt p) (p : ℕ) : Nonempty (PointsOfFlagModel.Tower p (Xo l) c) := by
  choose q hq hqv using fun v : PointsOfFlagModel.abelian₂ p c => GlobalTheory.Reg.exists_prime_natCast_mem v.1
  choose W hW _ using fun v : PointsOfFlagModel.abelian₂ p c => exists_valuationSubring c (q v) v.1 (hqv v)
  exact ⟨{ O := fun v => c.V (W v)
           β := fun v => (c.V (W v)).subtype
           Y := fun v => S.Y (q v) (W v) (hq v) (hW v) ⟨l, c, hg _ (hq v)⟩
           lvN := fun _ => l
           XoN := fun _ => Xo l
           cN := fun _ => c
           ON := fun _ v => c.V (W v)
           βN := fun _ v => (c.V (W v)).subtype
           YN := fun _ v => S.Y (q v) (W v) (hq v) (hW v) ⟨l, c, hg _ (hq v)⟩ }⟩

/- English proof (translation)
Introduce `E _ _ _ H D l Xo c hD hg p`. Take `⟨Xf, rfl⟩ : ∃ Xf : ∀ l : Level H, Moduli D l, Xf l = Xo` from `⟨Function.update (fun l => (GlobalTheory.T.moduliScheme_levelMaps_heckePoints'.1 E H D l hD).some) l Xo, Function.update_self ..⟩`. Take `⟨L1, L2, L3, -⟩` from `GlobalTheory.T.all_uniformization_laws_hold`. Take `⟨S, -⟩` from `GlobalTheory.T.exists_localModelSystem_ampleFrames_fullLevel GlobalTheory.T.homExtension_semiAbelian_discreteValuationRing L1 L2 L3 (GlobalTheory.T.exists_fullLevelAmpleModel_of_semistableReduction GlobalTheory.T.semistableReduction_ppav_padicField) E H D Xf hD (GlobalTheory.T.mo …`. Distinguish the cases in `hp : p.Prime`.

Take `⟨Tw, h⟩` from `exists_towerAt S hD l c hp (hg p hp)`. Conclude with `⟨Tw, fun _ => h⟩`. Take `⟨Tw⟩` from `nonempty_tower S l c hg p`. Conclude with `⟨Tw, fun h => absurd h hp⟩`.
-/
theorem exists_tower : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), 1 ≤ Dw.p + Dw.q → (∀ p : ℕ, p.Prime → l.GoodAt p) → ∀ p : ℕ, ∃ Tw : PointsOfFlagModel.Tower p Xo c, p.Prime → PointsOfFlagModel.TowerAt Tw := by
  intro E _ _ _ H D l Xo c hD hg p
  classical
  obtain ⟨Xf, rfl⟩ : ∃ Xf : ∀ l : Level H, Moduli D l, Xf l = Xo :=
    ⟨Function.update (fun l => (GlobalTheory.T.moduliScheme_levelMaps_heckePoints'.1 E H D l hD).some) l Xo, Function.update_self ..⟩
  obtain ⟨L1, L2, L3, -⟩ := GlobalTheory.T.all_uniformization_laws_hold
  obtain ⟨S, -⟩ := GlobalTheory.T.exists_localModelSystem_ampleFrames_fullLevel GlobalTheory.T.homExtension_semiAbelian_discreteValuationRing L1 L2 L3 (GlobalTheory.T.exists_fullLevelAmpleModel_of_semistableReduction GlobalTheory.T.semistableReduction_ppav_padicField) E H D Xf hD (GlobalTheory.T.moduliScheme_levelMaps_heckePoints'.2 E H D hD).1
  by_cases hp : p.Prime
  · obtain ⟨Tw, h⟩ := exists_towerAt S hD l c hp (hg p hp)
    exact ⟨Tw, fun _ => h⟩
  · obtain ⟨Tw⟩ := nonempty_tower S l c hg p
    exact ⟨Tw, fun h => absurd h hp⟩

end GlobalTheory.LocalData.Towers

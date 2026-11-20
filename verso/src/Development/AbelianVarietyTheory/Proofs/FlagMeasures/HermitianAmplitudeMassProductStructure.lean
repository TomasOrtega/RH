import Mathlib
import Formalism.SharpRestriction.CuspSpanNormBounds.FractionFieldToGenericStalkAlgebraMapEq
import Formalism.SharpRestriction.CuspSpanNormBounds.PsiEDef
import Development.AbelianVarietyTheory.Definitions.Foundations.IsHermND
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ComplementReferenceCompactSubgroup
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.GFrames
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.GlobalHermitianFramesTermsOrbitsLocalStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianLatticeMassEqFinprodLocalStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.CoordinateLatticeUniqueTermAlmostAllPlacesStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.NumberFieldLatticeDeterminedByLocalLatticesStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianDoubleCosetMassLeAndFiniteStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianFramesStabilizerActsOnTermsStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.CommonStabilizerStabilizersCommensurableVolumeStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianDoubleCosetTermBasicFactsStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianFramesComplementUnitaryNormalisesStabilStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.AmplitudeMassEqOneOfSingleOrbitStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LocalAmplitudeSummandAtTermOrbitStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.SumProdOfLocalChoicesBijectionStatement
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL NumberField IsDedekindDomain
open scoped Pointwise ENNReal Classical

noncomputable section

namespace GlobalTheory.HL.ProdStruct

def instLf {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {sig : E →ₐ[F] E}
    {p : HeightOneSpectrum (𝓞 F)} (X : LocAt F E sig p) : IsNonarchimedeanLocalField X.Fp := X.lf

def instChar0 {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {sig : E →ₐ[F] E}
    {p : HeightOneSpectrum (𝓞 F)} (X : LocAt F E sig p) : CharZero X.Fp := X.char0
attribute [local instance] instLf instChar0

/- English proof (translation)
Rewrite using `[Quotient.eq'', MulAction.orbitRel_apply, MulAction.mem_orbit_iff]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨⟨h, hh⟩, e⟩`. Conclude with `⟨h, hh, e.symm⟩`. Introduce and unpack `⟨h, hh, e⟩`.

Conclude with `⟨⟨h, hh⟩, e.symm⟩`.
-/
theorem orb_eq_iff {G α : Type*} [Group G] [MulAction G α] (H : Subgroup G) (a b : α) :
    (Quotient.mk'' a : MulAction.orbitRel.Quotient H α) = Quotient.mk'' b ↔ ∃ h ∈ H, a = h • b := by
  rw [Quotient.eq'', MulAction.orbitRel_apply, MulAction.mem_orbit_iff]
  constructor
  · rintro ⟨⟨h, hh⟩, e⟩
    exact ⟨h, hh, e.symm⟩
  · rintro ⟨h, hh, e⟩
    exact ⟨⟨h, hh⟩, e.symm⟩

/- English proof (translation)
Introduce `F _ _ _ _ _ E _ _ _ L r k S Λs d₀ hlat hK hterm hom hall hdat d Λ Λ' hΛ hΛ'`. Take `⟨h, hh, rfl⟩` from `hdat d Λ hΛ`. Establish `tr` using `GlobalTheory.T.hermitianFrames_complementUnitary_normalises_stabiliser L r k S h⁻¹ (S.H0.inv_mem hh)`. Establish `tr2` using `GlobalTheory.T.hermitianFrames_complementUnitary_normalises_stabiliser L r k S h hh`. Establish `key : ∀ Λ, S.IsTerm (h • d₀) Λ → ∃ s ∈ S.St, h⁻¹ • Λ = s • Λs ∧ S.mu Λ = 1 ∧ S.om (h • d₀) Λ = 1`.

Introduce `Λ hΛ`. Establish `e` using `tr.2 (h • d₀) Λ hΛ`. Simplify using `only [inv_smul_smul] at e`. Take `⟨s, hs, hsΛ⟩` from `hall _ e.1`. Use `⟨s, hs, hsΛ, ?_, ?_⟩` and prove the remaining obligations.

Rewrite using `[← e.2.2, hsΛ, ((GlobalTheory.T.commonStabilizer_stabilizers_commensurable_volume L r k S).1 Λs hlat).2.2 s hs]`. Unfold `Frames.mu`. Rewrite using `[hK]`. Simplify using `[invVol, Subgroup.relIndex_self]`. Rewrite using `[← e.2.1, hsΛ, (GlobalTheory.T.hermitianFrames_stabilizer_acts_on_terms L r k S d₀ Λs hterm s hs).2.1, hom]`.

Take `⟨s, hs, e1, hmu, hom1⟩` from `key Λ hΛ`. Take `⟨s', hs', e2, -, -⟩` from `key Λ' hΛ'`. Use `⟨⟨h * (s' * s⁻¹) * h⁻¹, tr2.1 _ (S.St.mul_mem hs' (S.St.inv_mem hs)), ?_⟩, hmu, hom1⟩` and prove the remaining obligations. Establish `hl : Λs = s⁻¹ • h⁻¹ • Λ` using `by rw [e1, inv_smul_smul]`. Establish `hl' : Λ' = h • s' • Λs` using `by rw [← e2, smul_inv_smul]`.

Rewrite using `[hl', hl]`. Simplify using `only [mul_smul]`.
-/
theorem std_one : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ (r k : ℕ) (S : Frames L r k), ∀ (Λs : Submodule L.O S.V) (d₀ : S.Datum), IsLat L Λs → S.St ⊓ MulAction.stabilizer S.GLV Λs = S.K0 → S.IsTerm d₀ Λs → S.om d₀ Λs = 1 → (∀ Λ, S.IsTerm d₀ Λ → ∃ h ∈ S.St, Λ = h • Λs) → (∀ d Λ, S.IsTerm d Λ → ∃ h ∈ S.H0, d = h • d₀) → ∀ (d : S.Datum) (Λ Λ' : Submodule L.O S.V), S.IsTerm d Λ → S.IsTerm d Λ' → (∃ h ∈ S.St, Λ' = h • Λ) ∧ S.mu Λ = 1 ∧ S.om d Λ = 1 := by
  intro F _ _ _ _ _ E _ _ _ L r k S Λs d₀ hlat hK hterm hom hall hdat d Λ Λ' hΛ hΛ'
  obtain ⟨h, hh, rfl⟩ := hdat d Λ hΛ
  have tr := GlobalTheory.T.hermitianFrames_complementUnitary_normalises_stabiliser L r k S h⁻¹ (S.H0.inv_mem hh)
  have tr2 := GlobalTheory.T.hermitianFrames_complementUnitary_normalises_stabiliser L r k S h hh
  have key : ∀ Λ, S.IsTerm (h • d₀) Λ → ∃ s ∈ S.St, h⁻¹ • Λ = s • Λs ∧ S.mu Λ = 1 ∧ S.om (h • d₀) Λ = 1 := by
    intro Λ hΛ
    have e := tr.2 (h • d₀) Λ hΛ
    simp only [inv_smul_smul] at e
    obtain ⟨s, hs, hsΛ⟩ := hall _ e.1
    refine ⟨s, hs, hsΛ, ?_, ?_⟩
    · rw [← e.2.2, hsΛ, ((GlobalTheory.T.commonStabilizer_stabilizers_commensurable_volume L r k S).1 Λs hlat).2.2 s hs]
      unfold Frames.mu
      rw [hK]
      simp [invVol, Subgroup.relIndex_self]
    · rw [← e.2.1, hsΛ, (GlobalTheory.T.hermitianFrames_stabilizer_acts_on_terms L r k S d₀ Λs hterm s hs).2.1, hom]
  obtain ⟨s, hs, e1, hmu, hom1⟩ := key Λ hΛ
  obtain ⟨s', hs', e2, -, -⟩ := key Λ' hΛ'
  refine ⟨⟨h * (s' * s⁻¹) * h⁻¹, tr2.1 _ (S.St.mul_mem hs' (S.St.inv_mem hs)), ?_⟩, hmu, hom1⟩
  have hl : Λs = s⁻¹ • h⁻¹ • Λ := by rw [e1, inv_smul_smul]
  have hl' : Λ' = h • s' • Λs := by rw [← e2, smul_inv_smul]
  rw [hl', hl]
  simp only [mul_smul]

end GlobalTheory.HL.ProdStruct

namespace GlobalTheory.HL.ProdStruct
attribute [local instance] instLf instChar0

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {sig : E →ₐ[F] E}

/- English proof (translation)
Take `⟨g, -, rfl⟩` from `h`. Use `⟨hΓ.fg.map _, ?_⟩` and prove the remaining obligations. Rewrite using `[Submodule.map_coe]`. Establish `: (((g : G.V →ₗ[E] G.V).restrictScalars (𝓞 E)) : G.V → G.V) = ((g : G.V →ₗ[E] G.V) : G.V → G.V)` using `rfl`. Rewrite using `[this, Submodule.span_image, hΓ.span_eq_top, Submodule.map_top, LinearMap.range_eq_top]`.

Conclude with `g.surjective`.
-/
theorem isLattice_of_LRel {A : Places F E sig} {r k : ℕ} (G : GFrames A r k) {Γ Γ' : G.Lt}
    (hΓ : Submodule.IsLattice E Γ) (h : G.LRel Γ Γ') : Submodule.IsLattice E Γ' := by
  obtain ⟨g, -, rfl⟩ := h
  refine ⟨hΓ.fg.map _, ?_⟩
  rw [Submodule.map_coe]
  have : (((g : G.V →ₗ[E] G.V).restrictScalars (𝓞 E)) : G.V → G.V) = ((g : G.V →ₗ[E] G.V) : G.V → G.V) := rfl
  rw [this, Submodule.span_image, hΓ.span_eq_top, Submodule.map_top, LinearMap.range_eq_top]
  exact g.surjective

/- English proof (translation)
Establish `hl` using `isLattice_of_LRel G hΓ.1 h`. Establish `e` using `((GlobalTheory.T.globalHermitianFrames_terms_orbits_local A r k G hk d hex).2.1 Γ Γ' hΓ hl).1 h`. Use `⟨hl, fun p => ?_⟩` and prove the remaining obligations. Take `⟨s, hs, hsp⟩` from `e p`. Rewrite using `[hsp]`.

Conclude with `(GlobalTheory.T.hermitianFrames_stabilizer_acts_on_terms (A.L p) r k (G.S p) (d p) _ (hΓ.2 p) s hs).1`.
-/
theorem term_of_LRel {A : Places F E sig} {r k : ℕ} (G : GFrames A r k) (hk : 4 * r + 7 ≤ k) {d : G.Dat}
    (hex : ∃ Λ₀, G.IsTerm d Λ₀) {Γ Γ' : G.Lt} (hΓ : G.IsTerm d Γ) (h : G.LRel Γ Γ') : G.IsTerm d Γ' := by
  have hl := isLattice_of_LRel G hΓ.1 h
  have e := ((GlobalTheory.T.globalHermitianFrames_terms_orbits_local A r k G hk d hex).2.1 Γ Γ' hΓ hl).1 h
  refine ⟨hl, fun p => ?_⟩
  obtain ⟨s, hs, hsp⟩ := e p
  rw [hsp]
  exact (GlobalTheory.T.hermitianFrames_stabilizer_acts_on_terms (A.L p) r k (G.S p) (d p) _ (hΓ.2 p) s hs).1

end GlobalTheory.HL.ProdStruct

namespace GlobalTheory.HL.ProdStruct
attribute [local instance] instLf instChar0

/- English proof (translation)
Introduce `F E _ _ _ _ _ sig A r k G hk d hex P hPinv hPfin`. Take `⟨Λ₀, hΛ₀⟩` from `id hex`. Establish `orb` using `GlobalTheory.T.globalHermitianFrames_terms_orbits_local A r k G hk d hex`. Establish `hstd` using `GlobalTheory.T.coordinateLattice_unique_term_almost_all_places A r k G hk`. Establish `hrec` using `GlobalTheory.T.numberField_lattice_determined_by_local_lattices A _ Λ₀ hΛ₀.1`.

Establish `hfin` using `(hstd.union hrec.2.2).union hPfin`. Use `set s := hfin.toFinset with hs_def`. Establish `KF : ∀ p, p ∉ s → ∀ Λ Λ', (G.S p).IsTerm (d p) Λ → (G.S p).IsTerm (d p) Λ' → (∃ h ∈ (G.S p).St, Λ' = h • Λ) ∧ (G.S p).mu Λ = 1 ∧ (G.S p).om (d p) Λ = 1 ∧ P p Λ`. Introduce `p hp Λ Λ' hΛ hΛ'`. Simplify using `only [hs_def, Set.Finite.mem_toFinset, Set.mem_union, Set.mem_setOf_eq, not_or, not_not] at hp`.

Take `⟨⟨hs1, hs2⟩, hs3⟩` from `hp`. Take `⟨_, _, hK, d₀, hW, hom, _, hall, _, hdat⟩` from `hs1`. Establish `hlat : IsLat (A.L p) (Submodule.span (A.L p).O (Set.range fun i => (Pi.single i 1 : (G.S p).V)))`. Rewrite using `[← hs2]`. Conclude with `hrec.2.1 p`.

Establish `t` using `std_one (A.L p) r k (G.S p) _ d₀ hlat hK ⟨(1, 1), hW⟩ hom hall hdat (d p) Λ Λ' hΛ hΛ'`. Conclude with `⟨t.1, t.2.1, t.2.2, by by_contra hc; exact hs3 ⟨Λ, hΛ, hc⟩⟩`. Establish `L1 : ∀ p, p ∉ s → (G.S p).amp (d p) (P p) = 1 ∧ (G.S p).mass (d p) (P p) = 1` using `fun p hp => GlobalTheory.T.amplitude_mass_eq_one_of_single_orbit (A.L p) r k (G.S p) (d p) (P p) ⟨_, hΛ₀.2 p⟩ (fun Λ Λ' h1 h2 => (KF p hp Λ Λ' h1 h2).1) (fun Λ h1 => ⟨(KF p hp Λ Λ h1 h1).2.2.2, (KF p hp Λ Λ h1 h1).2.1, (KF p hp Λ Λ h1 h1).2.2.1⟩)`. Establish `hmuG : ∀ Γ, G.IsTerm d Γ → G.mu Γ = ∏ p ∈ s, (G.S p).mu (A.lat p Γ)`. Introduce `Γ hΓ`.

Rewrite using `[(GlobalTheory.T.hermitianLattice_mass_eq_finprod_local A r k G hk Γ hΓ.1).2]`. Apply `finprod_eq_prod_of_mulSupport_subset` to reduce the goal to its premises. Introduce `p hp`. Assume the negation of the conclusion as `hps`. Conclude with `hp (KF p hps _ _ (hΓ.2 p) (hΓ.2 p)).2.1`.

Establish `homG : ∀ Γ, G.IsTerm d Γ → G.om d Γ = ∏ p ∈ s, (G.S p).om (d p) (A.lat p Γ)`. Introduce `Γ hΓ`. Unfold `GFrames.om`. Apply `finprod_eq_prod_of_mulSupport_subset` to reduce the goal to its premises. Introduce `p hp`.

Assume the negation of the conclusion as `hps`. Conclude with `hp (KF p hps _ _ (hΓ.2 p) (hΓ.2 p)).2.2.1`. Establish `hPinv' : ∀ p, ∀ Λ, ∀ h ∈ (G.S p).St, ((G.S p).IsTerm (d p) (h • Λ) ∧ P p (h • Λ)) ↔ ((G.S p).IsTerm (d p) Λ ∧ P p Λ)`. Introduce `p Λ h hh`. Prove the components needed by the constructor for the conclusion.

Introduce and unpack `⟨h1, h2⟩`. Establish `e` using `GlobalTheory.T.hermitianFrames_stabilizer_acts_on_terms (A.L p) r k (G.S p) (d p) _ h1 h⁻¹ ((G.S p).St.inv_mem hh)`. Rewrite `e` using `[inv_smul_smul]`. Conclude with `⟨e.1, by simpa using hPinv p h⁻¹ ((G.S p).St.inv_mem hh) _ h1 h2⟩`. Introduce and unpack `⟨h1, h2⟩`.

Conclude with `⟨(GlobalTheory.T.hermitianFrames_stabilizer_acts_on_terms (A.L p) r k (G.S p) (d p) _ h1 h hh).1, hPinv p h hh Λ h1 h2⟩`. Set `O` to `fun p => MulAction.orbitRel.Quotient (G.S p).St (Submodule (A.L p).O (G.S p).V)`. Set `Φ : Quot G.LRel → ∀ p, O p` to `fun c p => Quotient.mk'' (A.lat p c.out)`. Set `U : ∀ p, Set (O p)` to `fun p => {o | (G.S p).IsTerm (d p) o.out}`. Set `Tq : Set (Quot G.LRel)` to `{c | G.IsTerm d c.out}`.

Set `gC : ∀ p, O p → ℂ` to `fun p o => if (G.S p).IsTerm (d p) o.out ∧ P p o.out then ((G.S p).mu o.out : ℂ) * (G.S p).om (d p) o.out else 0`. Set `gM : ∀ p, O p → ℝ≥0∞` to `fun p o => if (G.S p).IsTerm (d p) o.out ∧ P p o.out then ENNReal.ofReal ((G.S p).mu o.out) else 0`. Establish `hcls : ∀ Γ, G.IsTerm d Γ → ∀ p, (G.S p).IsTerm (d p) (Quotient.mk'' (A.lat p Γ) : O p).out ∧ gC p (Quotient.mk'' (A.lat p Γ)) = (if P p (A.lat p Γ) then ((G.S p).mu (A.lat p Γ) : ℂ) * (G.S p).om (d p) (A.lat p Γ) else 0) ∧ gM p (Quotient.mk'' (A.lat p Γ)) = (if P p (A.lat p Γ) th …`. Introduce `Γ hΓ p`. Establish `t` using `GlobalTheory.T.localAmplitude_summand_at_term_orbit (A.L p) r k (G.S p) (d p) (fun Λ => (G.S p).IsTerm (d p) Λ ∧ P p Λ) (hPinv' p) (A.lat p Γ) (hΓ.2 p) ((GlobalTheory.T.numberField_lattice_determined_by_local_lattices A _ Γ hΓ.1).2.1 p) _ rfl`.

Simplify using `only [and_self_left, hΓ.2 p, true_and] at t`. Conclude with `⟨t.1, t.2.2.1, t.2.2.2⟩`. Establish `hUfin : ∀ p ∈ s, (U p).Finite` using `fun p _ => (GlobalTheory.T.hermitianDoubleCoset_mass_le_and_finite (A.L p) r k (G.S p) (by omega) (d p)).2`. Establish `hinj : ∀ c ∈ Tq, ∀ c' ∈ Tq, (∀ p ∈ s, Φ c p = Φ c' p) → c = c'`. Introduce `c hc c' hc' he`.

Establish `hc1 : G.IsTerm d c.out` using `hc`. Establish `hc2 : G.IsTerm d c'.out` using `hc'`. Establish `hrel : G.LRel c.out c'.out`. Rewrite using `[orb.2.1 c.out c'.out hc1 hc2.1]`. Introduce `p`.

Distinguish the cases in `hp : p ∈ s`. Conclude with `(orb_eq_iff _ _ _).1 (he p hp).symm`. Conclude with `(KF p hp _ _ (hc1.2 p) (hc2.2 p)).1`. Rewrite using `[← Quot.out_eq c, ← Quot.out_eq c']`. Conclude with `Quot.sound hrel`.

Establish `hmaps : ∀ c ∈ Tq, ∀ p ∈ s, Φ c p ∈ U p` using `fun c hc p _ => (hcls c.out hc p).1`. Establish `hsurj : ∀ x : ∀ p, O p, (∀ p ∈ s, x p ∈ U p) → ∃ c ∈ Tq, ∀ p ∈ s, Φ c p = x p`. Introduce `x hx`. Take `⟨Γ, hΓ, hloc⟩` from `orb.1 (fun p => if p ∈ s then (x p).out else A.lat p Λ₀) (by`. Introduce `p`.

Distinguish the cases in `hp : p ∈ s`. Simplify using `only [hp, if_true]`. Conclude with `hx p hp`. Simplify using `only [hp, if_false]`. Conclude with `hΛ₀.2 p)`.

Establish `hr : G.LRel Γ (Quot.mk G.LRel Γ).out` using `orb.2.2.1.symm ((Equivalence.eqvGen_iff orb.2.2.1).1 (Quot.eqvGen_exact (Quot.out_eq _)))`. Establish `hct : G.IsTerm d (Quot.mk G.LRel Γ).out` using `term_of_LRel G hk hex hΓ hr`. Establish `hloc2` using `(orb.2.1 Γ _ hΓ hct.1).1 hr`. Use `⟨Quot.mk G.LRel Γ, hct, fun p hp => ?_⟩` and prove the remaining obligations. Take `⟨h1, hh1, e1⟩` from `hloc2 p`.

Take `⟨h2, hh2, e2⟩` from `hloc p`. Simplify using `only [hp, if_true] at e2`. Use `show (Quotient.mk'' (A.lat p (Quot.mk G.LRel Γ).out) : O p) = x p`. Rewrite using `[e1, e2, ← mul_smul, (orb_eq_iff _ _ _).2 ⟨h1 * h2, (G.S p).St.mul_mem hh1 hh2, rfl⟩, Quotient.out_eq']`. Use `haveI : ∀ p, Nonempty (O p) := fun p => ⟨Quotient.mk'' ⊥⟩`.

Establish `T5C` using `GlobalTheory.T.sum_prod_of_local_choices_bijection s Φ Tq U hUfin hinj hmaps hsurj gC`. Establish `T5M` using `GlobalTheory.T.sum_prod_of_local_choices_bijection s Φ Tq U hUfin hinj hmaps hsurj gM`. Establish `hPs : ∀ Γ, G.IsTerm d Γ → ((∀ p, P p (A.lat p Γ)) ↔ ∀ p ∈ s, P p (A.lat p Γ))` using `fun Γ hΓ => ⟨fun h p _ => h p, fun h p => if hp : p ∈ s then h p hp else (KF p hp _ _ (hΓ.2 p) (hΓ.2 p)).2.2.2⟩`. Establish `hsumC : G.amp d (fun Λ => ∀ p, P p (A.lat p Λ)) = ∑' c, if c ∈ Tq then ∏ p ∈ s, gC p (Φ c p) else 0`. Unfold `GFrames.amp`.

Apply `tsum_congr` to reduce the goal to its premises. Introduce `c`. Distinguish the cases in `hc : c ∈ Tq`. Establish `hc' : G.IsTerm d c.out` using `hc`. Rewrite using `[if_pos hc, show (∏ p ∈ s, gC p (Φ c p)) = ∏ p ∈ s, (if P p (A.lat p c.out) then ((G.S p).mu (A.lat p c.out) : ℂ) * (G.S p).om (d p) (A.lat p c.out) else 0) from Finset.prod_congr rfl (fun p _ => (hcls c.out hc' p).2.1), Finset.prod_ite_zero]`.

Simplify using `only [hc', true_and, hPs _ hc']`. Use `split_ifs`. Rewrite using `[hmuG _ hc', homG _ hc', Complex.ofReal_prod, Finset.prod_mul_distrib]`. Both sides reduce to the same expression. Rewrite using `[if_neg hc, if_neg (fun h => hc h.1)]`.

Establish `hsumM : G.mass d (fun Λ => ∀ p, P p (A.lat p Λ)) = ∑' c, if c ∈ Tq then ∏ p ∈ s, gM p (Φ c p) else 0`. Unfold `GFrames.mass`. Apply `tsum_congr` to reduce the goal to its premises. Introduce `c`. Distinguish the cases in `hc : c ∈ Tq`.

Establish `hc' : G.IsTerm d c.out` using `hc`. Rewrite using `[if_pos hc, show (∏ p ∈ s, gM p (Φ c p)) = ∏ p ∈ s, (if P p (A.lat p c.out) then ENNReal.ofReal ((G.S p).mu (A.lat p c.out)) else 0) from Finset.prod_congr rfl (fun p _ => (hcls c.out hc' p).2.2), Finset.prod_ite_zero]`. Simplify using `only [hc', true_and, hPs _ hc']`. Use `split_ifs`. Rewrite using `[hmuG _ hc', ENNReal.ofReal_prod_of_nonneg]`.

Introduce `p _`. Unfold `Frames.mu invVol`. Check the signs of the components of the expression. Both sides reduce to the same expression. Rewrite using `[if_neg hc, if_neg (fun h => hc h.1)]`.

Establish `hampC : ∀ p, (G.S p).amp (d p) (P p) = ∑' o : O p, if o ∈ U p then gC p o else 0`. Introduce `p`. Unfold `Frames.amp`. Apply `tsum_congr` to reduce the goal to its premises. Introduce `o`.

Distinguish the cases in `ho : (G.S p).IsTerm (d p) o.out`. Establish `: o ∈ U p` using `ho`. Rewrite using `[if_pos this]`. Establish `: o ∉ U p` using `ho`. Rewrite using `[if_neg this, if_neg (fun h => ho h.1)]`.

Establish `hampM : ∀ p, (G.S p).mass (d p) (P p) = ∑' o : O p, if o ∈ U p then gM p o else 0`. Introduce `p`. Unfold `Frames.mass`. Apply `tsum_congr` to reduce the goal to its premises. Introduce `o`.

Distinguish the cases in `ho : (G.S p).IsTerm (d p) o.out`. Establish `: o ∈ U p` using `ho`. Rewrite using `[if_pos this]`. Establish `: o ∉ U p` using `ho`. Rewrite using `[if_neg this, if_neg (fun h => ho h.1)]`.

Use `⟨?_, ?_, ?_, T5C.1⟩` and prove the remaining obligations. Rewrite using `[hsumC, T5C.2, finprod_eq_prod_of_mulSupport_subset _ (s := s) (fun p hp => by`. Assume the negation of the conclusion as `hps`. Conclude with `hp (L1 p hps).1)]`. Conclude with `Finset.prod_congr rfl (fun p _ => (hampC p).symm)`.

Rewrite using `[hsumM, T5M.2, finprod_eq_prod_of_mulSupport_subset _ (s := s) (fun p hp => by`. Assume the negation of the conclusion as `hps`. Conclude with `hp (L1 p hps).2)]`. Conclude with `Finset.prod_congr rfl (fun p _ => (hampM p).symm)`. Use `s.finite_toSet.subset (fun p hp => ?_)` and prove the remaining obligations.

Assume the negation of the conclusion as `hps`. Break down `hp with h | h` into its components or cases. Conclude with `h (L1 p hps).1`. Conclude with `h (L1 p hps).2`.
-/
theorem product_structure : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {sig : E →ₐ[F] E} (A : Places F E sig), ∀ (r k : ℕ) (G : GFrames A r k), 4 * r + 7 ≤ k → ∀ d : G.Dat, (∃ Λ₀, G.IsTerm d Λ₀) → ∀ P : ∀ p, Submodule (A.L p).O (G.S p).V → Prop, (∀ p, ∀ h ∈ (G.S p).St, ∀ Λ, (G.S p).IsTerm (d p) Λ → P p Λ → P p (h • Λ)) → {p | ∃ Λ, (G.S p).IsTerm (d p) Λ ∧ ¬ P p Λ}.Finite → G.amp d (fun Λ => ∀ p, P p (A.lat p Λ)) = ∏ᶠ p, (G.S p).amp (d p) (P p) ∧ G.mass d (fun Λ => ∀ p, P p (A.lat p Λ)) = ∏ᶠ p, (G.S p).mass (d p) (P p) ∧ {p | (G.S p).amp (d p) (P p) ≠ 1 ∨ (G.S p).mass (d p) (P p) ≠ 1}.Finite ∧ {o : Quot G.LRel | G.IsTerm d o.out}.Finite := by
  intro F E _ _ _ _ _ sig A r k G hk d hex P hPinv hPfin
  obtain ⟨Λ₀, hΛ₀⟩ := id hex
  have orb := GlobalTheory.T.globalHermitianFrames_terms_orbits_local A r k G hk d hex
  have hstd := GlobalTheory.T.coordinateLattice_unique_term_almost_all_places A r k G hk
  have hrec := GlobalTheory.T.numberField_lattice_determined_by_local_lattices A _ Λ₀ hΛ₀.1
  have hfin := (hstd.union hrec.2.2).union hPfin
  set s := hfin.toFinset with hs_def

  have KF : ∀ p, p ∉ s → ∀ Λ Λ', (G.S p).IsTerm (d p) Λ → (G.S p).IsTerm (d p) Λ' →
      (∃ h ∈ (G.S p).St, Λ' = h • Λ) ∧ (G.S p).mu Λ = 1 ∧ (G.S p).om (d p) Λ = 1 ∧ P p Λ := by
    intro p hp Λ Λ' hΛ hΛ'
    simp only [hs_def, Set.Finite.mem_toFinset, Set.mem_union, Set.mem_setOf_eq, not_or, not_not] at hp
    obtain ⟨⟨hs1, hs2⟩, hs3⟩ := hp
    obtain ⟨_, _, hK, d₀, hW, hom, _, hall, _, hdat⟩ := hs1
    have hlat : IsLat (A.L p) (Submodule.span (A.L p).O (Set.range fun i => (Pi.single i 1 : (G.S p).V))) := by
      rw [← hs2]; exact hrec.2.1 p
    have t := std_one (A.L p) r k (G.S p) _ d₀ hlat hK ⟨(1, 1), hW⟩ hom hall hdat (d p) Λ Λ' hΛ hΛ'
    exact ⟨t.1, t.2.1, t.2.2, by by_contra hc; exact hs3 ⟨Λ, hΛ, hc⟩⟩
  have L1 : ∀ p, p ∉ s → (G.S p).amp (d p) (P p) = 1 ∧ (G.S p).mass (d p) (P p) = 1 := fun p hp =>
    GlobalTheory.T.amplitude_mass_eq_one_of_single_orbit (A.L p) r k (G.S p) (d p) (P p) ⟨_, hΛ₀.2 p⟩
      (fun Λ Λ' h1 h2 => (KF p hp Λ Λ' h1 h2).1)
      (fun Λ h1 => ⟨(KF p hp Λ Λ h1 h1).2.2.2, (KF p hp Λ Λ h1 h1).2.1, (KF p hp Λ Λ h1 h1).2.2.1⟩)
  have hmuG : ∀ Γ, G.IsTerm d Γ → G.mu Γ = ∏ p ∈ s, (G.S p).mu (A.lat p Γ) := by
    intro Γ hΓ
    rw [(GlobalTheory.T.hermitianLattice_mass_eq_finprod_local A r k G hk Γ hΓ.1).2]
    apply finprod_eq_prod_of_mulSupport_subset
    intro p hp
    by_contra hps
    exact hp (KF p hps _ _ (hΓ.2 p) (hΓ.2 p)).2.1
  have homG : ∀ Γ, G.IsTerm d Γ → G.om d Γ = ∏ p ∈ s, (G.S p).om (d p) (A.lat p Γ) := by
    intro Γ hΓ
    unfold GFrames.om
    apply finprod_eq_prod_of_mulSupport_subset
    intro p hp
    by_contra hps
    exact hp (KF p hps _ _ (hΓ.2 p) (hΓ.2 p)).2.2.1
  have hPinv' : ∀ p, ∀ Λ, ∀ h ∈ (G.S p).St,
      ((G.S p).IsTerm (d p) (h • Λ) ∧ P p (h • Λ)) ↔ ((G.S p).IsTerm (d p) Λ ∧ P p Λ) := by
    intro p Λ h hh
    constructor
    · rintro ⟨h1, h2⟩
      have e := GlobalTheory.T.hermitianFrames_stabilizer_acts_on_terms (A.L p) r k (G.S p) (d p) _ h1 h⁻¹ ((G.S p).St.inv_mem hh)
      rw [inv_smul_smul] at e
      exact ⟨e.1, by simpa using hPinv p h⁻¹ ((G.S p).St.inv_mem hh) _ h1 h2⟩
    · rintro ⟨h1, h2⟩
      exact ⟨(GlobalTheory.T.hermitianFrames_stabilizer_acts_on_terms (A.L p) r k (G.S p) (d p) _ h1 h hh).1, hPinv p h hh Λ h1 h2⟩
  let O := fun p => MulAction.orbitRel.Quotient (G.S p).St (Submodule (A.L p).O (G.S p).V)
  let Φ : Quot G.LRel → ∀ p, O p := fun c p => Quotient.mk'' (A.lat p c.out)
  let U : ∀ p, Set (O p) := fun p => {o | (G.S p).IsTerm (d p) o.out}
  let Tq : Set (Quot G.LRel) := {c | G.IsTerm d c.out}
  let gC : ∀ p, O p → ℂ := fun p o => if (G.S p).IsTerm (d p) o.out ∧ P p o.out then
    ((G.S p).mu o.out : ℂ) * (G.S p).om (d p) o.out else 0
  let gM : ∀ p, O p → ℝ≥0∞ := fun p o => if (G.S p).IsTerm (d p) o.out ∧ P p o.out then
    ENNReal.ofReal ((G.S p).mu o.out) else 0
  have hcls : ∀ Γ, G.IsTerm d Γ → ∀ p, (G.S p).IsTerm (d p) (Quotient.mk'' (A.lat p Γ) : O p).out ∧
      gC p (Quotient.mk'' (A.lat p Γ)) = (if P p (A.lat p Γ) then
        ((G.S p).mu (A.lat p Γ) : ℂ) * (G.S p).om (d p) (A.lat p Γ) else 0) ∧
      gM p (Quotient.mk'' (A.lat p Γ)) = (if P p (A.lat p Γ) then ENNReal.ofReal ((G.S p).mu (A.lat p Γ)) else 0) := by
    intro Γ hΓ p
    have t := GlobalTheory.T.localAmplitude_summand_at_term_orbit (A.L p) r k (G.S p) (d p) (fun Λ => (G.S p).IsTerm (d p) Λ ∧ P p Λ) (hPinv' p)
      (A.lat p Γ) (hΓ.2 p) ((GlobalTheory.T.numberField_lattice_determined_by_local_lattices A _ Γ hΓ.1).2.1 p) _ rfl
    simp only [and_self_left, hΓ.2 p, true_and] at t
    exact ⟨t.1, t.2.2.1, t.2.2.2⟩
  have hUfin : ∀ p ∈ s, (U p).Finite := fun p _ => (GlobalTheory.T.hermitianDoubleCoset_mass_le_and_finite (A.L p) r k (G.S p) (by omega) (d p)).2
  have hinj : ∀ c ∈ Tq, ∀ c' ∈ Tq, (∀ p ∈ s, Φ c p = Φ c' p) → c = c' := by
    intro c hc c' hc' he
    have hc1 : G.IsTerm d c.out := hc
    have hc2 : G.IsTerm d c'.out := hc'
    have hrel : G.LRel c.out c'.out := by
      rw [orb.2.1 c.out c'.out hc1 hc2.1]
      intro p
      by_cases hp : p ∈ s
      · exact (orb_eq_iff _ _ _).1 (he p hp).symm
      · exact (KF p hp _ _ (hc1.2 p) (hc2.2 p)).1
    rw [← Quot.out_eq c, ← Quot.out_eq c']
    exact Quot.sound hrel
  have hmaps : ∀ c ∈ Tq, ∀ p ∈ s, Φ c p ∈ U p := fun c hc p _ => (hcls c.out hc p).1
  have hsurj : ∀ x : ∀ p, O p, (∀ p ∈ s, x p ∈ U p) → ∃ c ∈ Tq, ∀ p ∈ s, Φ c p = x p := by
    intro x hx
    obtain ⟨Γ, hΓ, hloc⟩ := orb.1 (fun p => if p ∈ s then (x p).out else A.lat p Λ₀) (by
      intro p
      by_cases hp : p ∈ s
      · simp only [hp, if_true]; exact hx p hp
      · simp only [hp, if_false]; exact hΛ₀.2 p)
    have hr : G.LRel Γ (Quot.mk G.LRel Γ).out :=
      orb.2.2.1.symm ((Equivalence.eqvGen_iff orb.2.2.1).1 (Quot.eqvGen_exact (Quot.out_eq _)))
    have hct : G.IsTerm d (Quot.mk G.LRel Γ).out := term_of_LRel G hk hex hΓ hr
    have hloc2 := (orb.2.1 Γ _ hΓ hct.1).1 hr
    refine ⟨Quot.mk G.LRel Γ, hct, fun p hp => ?_⟩
    obtain ⟨h1, hh1, e1⟩ := hloc2 p
    obtain ⟨h2, hh2, e2⟩ := hloc p
    simp only [hp, if_true] at e2
    show (Quotient.mk'' (A.lat p (Quot.mk G.LRel Γ).out) : O p) = x p
    rw [e1, e2, ← mul_smul, (orb_eq_iff _ _ _).2 ⟨h1 * h2, (G.S p).St.mul_mem hh1 hh2, rfl⟩, Quotient.out_eq']
  haveI : ∀ p, Nonempty (O p) := fun p => ⟨Quotient.mk'' ⊥⟩
  have T5C := GlobalTheory.T.sum_prod_of_local_choices_bijection s Φ Tq U hUfin hinj hmaps hsurj gC
  have T5M := GlobalTheory.T.sum_prod_of_local_choices_bijection s Φ Tq U hUfin hinj hmaps hsurj gM
  have hPs : ∀ Γ, G.IsTerm d Γ → ((∀ p, P p (A.lat p Γ)) ↔ ∀ p ∈ s, P p (A.lat p Γ)) := fun Γ hΓ =>
    ⟨fun h p _ => h p, fun h p => if hp : p ∈ s then h p hp else (KF p hp _ _ (hΓ.2 p) (hΓ.2 p)).2.2.2⟩
  have hsumC : G.amp d (fun Λ => ∀ p, P p (A.lat p Λ)) = ∑' c, if c ∈ Tq then ∏ p ∈ s, gC p (Φ c p) else 0 := by
    unfold GFrames.amp
    apply tsum_congr
    intro c
    by_cases hc : c ∈ Tq
    · have hc' : G.IsTerm d c.out := hc
      rw [if_pos hc, show (∏ p ∈ s, gC p (Φ c p)) = ∏ p ∈ s, (if P p (A.lat p c.out) then
          ((G.S p).mu (A.lat p c.out) : ℂ) * (G.S p).om (d p) (A.lat p c.out) else 0) from
          Finset.prod_congr rfl (fun p _ => (hcls c.out hc' p).2.1), Finset.prod_ite_zero]
      simp only [hc', true_and, hPs _ hc']
      split_ifs
      · rw [hmuG _ hc', homG _ hc', Complex.ofReal_prod, Finset.prod_mul_distrib]
      · rfl
    · rw [if_neg hc, if_neg (fun h => hc h.1)]
  have hsumM : G.mass d (fun Λ => ∀ p, P p (A.lat p Λ)) = ∑' c, if c ∈ Tq then ∏ p ∈ s, gM p (Φ c p) else 0 := by
    unfold GFrames.mass
    apply tsum_congr
    intro c
    by_cases hc : c ∈ Tq
    · have hc' : G.IsTerm d c.out := hc
      rw [if_pos hc, show (∏ p ∈ s, gM p (Φ c p)) = ∏ p ∈ s, (if P p (A.lat p c.out) then
          ENNReal.ofReal ((G.S p).mu (A.lat p c.out)) else 0) from
          Finset.prod_congr rfl (fun p _ => (hcls c.out hc' p).2.2), Finset.prod_ite_zero]
      simp only [hc', true_and, hPs _ hc']
      split_ifs
      · rw [hmuG _ hc', ENNReal.ofReal_prod_of_nonneg]
        intro p _
        unfold Frames.mu invVol
        positivity
      · rfl
    · rw [if_neg hc, if_neg (fun h => hc h.1)]
  have hampC : ∀ p, (G.S p).amp (d p) (P p) = ∑' o : O p, if o ∈ U p then gC p o else 0 := by
    intro p
    unfold Frames.amp
    apply tsum_congr
    intro o
    by_cases ho : (G.S p).IsTerm (d p) o.out
    · have : o ∈ U p := ho
      rw [if_pos this]
    · have : o ∉ U p := ho
      rw [if_neg this, if_neg (fun h => ho h.1)]
  have hampM : ∀ p, (G.S p).mass (d p) (P p) = ∑' o : O p, if o ∈ U p then gM p o else 0 := by
    intro p
    unfold Frames.mass
    apply tsum_congr
    intro o
    by_cases ho : (G.S p).IsTerm (d p) o.out
    · have : o ∈ U p := ho
      rw [if_pos this]
    · have : o ∉ U p := ho
      rw [if_neg this, if_neg (fun h => ho h.1)]
  refine ⟨?_, ?_, ?_, T5C.1⟩
  · rw [hsumC, T5C.2, finprod_eq_prod_of_mulSupport_subset _ (s := s) (fun p hp => by
      by_contra hps; exact hp (L1 p hps).1)]
    exact Finset.prod_congr rfl (fun p _ => (hampC p).symm)
  · rw [hsumM, T5M.2, finprod_eq_prod_of_mulSupport_subset _ (s := s) (fun p hp => by
      by_contra hps; exact hp (L1 p hps).2)]
    exact Finset.prod_congr rfl (fun p _ => (hampM p).symm)
  · refine s.finite_toSet.subset (fun p hp => ?_)
    by_contra hps
    rcases hp with h | h
    · exact h (L1 p hps).1
    · exact h (L1 p hps).2

end GlobalTheory.HL.ProdStruct

import Formalism.SharpRestriction.GrowthBounds.BinomialPolynomialIdentities.LowerSetTypesSpan
import Formalism.SharpRestriction.GrowthBounds.BinomialPolynomialIdentities.AdmissibleWordBasis
import Formalism.SharpRestriction.GrowthBounds.RootWeights.GeneratedWeightLemmaOfReducibility
import Formalism.SharpRestriction.GrowthBounds.RootWeights.WeightConditionFromIntegralForm
import Formalism.SharpRestriction.GrowthBounds.RootWeights.ContravariantOrthogonalityHolds
import Formalism.SharpRestriction.GrowthBounds.RootWeights.IsotypicProjectorSelfAdjoint

noncomputable section

open MvPolynomial Finset

namespace Formalism.MainNotions.G.ColumnFamilies

open Formalism.MainNotions.G Formalism.MainNotions.CovariantDegrees Formalism.MainNotions.G.GLWeightTheory Formalism.MainNotions.G.Joints

/- English proof (translation)
Assemble the required witnesses or components as `⟨fun _ => le_rfl, rfl⟩`.
-/
theorem dominanceOrder_refl {n : ℕ} (a : Fin n → ℤ) : DomLE a a := ⟨fun _ => le_rfl, rfl⟩

/- English proof (translation)
Assemble the required witnesses or components as `⟨fun x => (h1.1 x).trans (h2.1 x), h1.2.trans h2.2⟩`.
-/
theorem dominanceOrder_trans {n : ℕ} {a b c : Fin n → ℤ} (h1 : DomLE a b) (h2 : DomLE b c) : DomLE a c :=
  ⟨fun x => (h1.1 x).trans (h2.1 x), h1.2.trans h2.2⟩

/- English proof (translation)
Establish `h1'` using `(dominanceOrder_iff a b).1 h1`. Establish `h2'` using `(dominanceOrder_iff b a).1 h2`. Conclude with `(Formalism.InvariantFactorPaths.GelfandTsetlinBases.A3ev.domLe_eq h1' (Finset.sum_le_sum fun j _ => h2'.2 j)).symm`.
-/
theorem dominanceOrder_antisymm {n : ℕ} {a b : Fin n → ℤ} (h1 : DomLE a b) (h2 : DomLE b a) : a = b := by
  have h1' := (dominanceOrder_iff a b).1 h1
  have h2' := (dominanceOrder_iff b a).1 h2
  exact (Formalism.InvariantFactorPaths.GelfandTsetlinBases.A3ev.domLe_eq h1' (Finset.sum_le_sum fun j _ => h2'.2 j)).symm

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `a`. Simplify using `only [Pi.add_apply, rootW, Pi.sub_apply, Finset.sum_add_distrib, Finset.sum_sub_distrib, Pi.single_apply, Finset.sum_ite_eq', Finset.mem_filter, Finset.mem_univ, true_and]`. Use `split_ifs with h1 h2 h2`. Use linear arithmetic over natural numbers and integers.

Conclude with `absurd (h.le.trans h1) h2`. Use linear arithmetic over natural numbers and integers. Use linear arithmetic over natural numbers and integers. Simplify using `only [Pi.add_apply, rootW, Pi.sub_apply, Finset.sum_add_distrib, Finset.sum_sub_distrib, Pi.single_apply, Finset.sum_ite_eq', Finset.mem_univ, if_true]`. Use linear arithmetic over natural numbers and integers.
-/
theorem dominanceOrder_add_negative_root {n : ℕ} (ν : Fin n → ℤ) {c d : Fin n} (h : d < c) : DomLE (ν + rootW c d) ν := by
  classical
  constructor
  · intro a
    simp only [Pi.add_apply, rootW, Pi.sub_apply, Finset.sum_add_distrib, Finset.sum_sub_distrib, Pi.single_apply,
      Finset.sum_ite_eq', Finset.mem_filter, Finset.mem_univ, true_and]
    split_ifs with h1 h2 h2
    · omega
    · exact absurd (h.le.trans h1) h2
    · omega
    · omega
  · simp only [Pi.add_apply, rootW, Pi.sub_apply, Finset.sum_add_distrib, Finset.sum_sub_distrib, Pi.single_apply,
      Finset.sum_ite_eq', Finset.mem_univ, if_true]
    omega

/- English proof (translation)
Unfold `loweringMonoid at hu`. Proceed by induction on `hu using Submonoid.closure_induction_left with`. Consider the case `one => exact ⟨mu, dominanceOrder_refl mu, by simpa using hw⟩`. Consider the case `mul_left g hg y _ ih`. Take `⟨c, d, hcd, rfl⟩` from `hg`.

Take `⟨ν, h1, h2⟩` from `ih`. Conclude with `⟨ν + rootW c d, dominanceOrder_trans (dominanceOrder_add_negative_root ν hcd) h1, by`. Rewrite using `[Module.End.mul_apply]`. Conclude with `v2rep_shift E hR c d ν _ h2⟩`.
-/
theorem lowering_weight_dominated {n : ℕ} {K V : Type*} [Field K] [AddCommGroup V] [Module K V] (E : GLOps n K V) (hR : SatisfiesGLRelations E)
    (mu : Fin n → ℤ) (w : V) (hw : w ∈ weightSp E mu) {u : Module.End K V} (hu : u ∈ loweringMonoid E) :
    ∃ ν, DomLE ν mu ∧ u w ∈ weightSp E ν := by
  unfold loweringMonoid at hu
  induction hu using Submonoid.closure_induction_left with
  | one => exact ⟨mu, dominanceOrder_refl mu, by simpa using hw⟩
  | mul_left g hg y _ ih =>
    obtain ⟨c, d, hcd, rfl⟩ := hg
    obtain ⟨ν, h1, h2⟩ := ih
    exact ⟨ν + rootW c d, dominanceOrder_trans (dominanceOrder_add_negative_root ν hcd) h1, by
      rw [Module.End.mul_apply]; exact v2rep_shift E hR c d ν _ h2⟩

section concrete

variable {R : Type} [Field R] [CharZero R] {N : ℕ} (LL : Letters (Fin N)) {n : ℕ} (S : Set (Fin N))

/- English proof (translation)
Establish `hE` using `isGLRep_glOps R (Fin N) LL n S`. Use `(isotypic_le_lowering_span hE mu).trans ?_` and prove the remaining obligations. Unfold `hwvLoweringSpan`. Rewrite using `[Submodule.span_le]`. Introduce and unpack `_ ⟨u, hu, w, hw, rfl⟩`.

Take `⟨ν, hd, hmem⟩` from `lowering_weight_dominated (glOps R n LL S) hE.1 mu w hw.2.1 hu`. Rewrite using `[SetLike.mem_coe, MvPolynomial.mem_restrictSupport_iff]`. Introduce `m hm`. Use `(monomials_are_weight_vectors R (Fin N) LL n S).2 ν _ hmem m (by simpa using hm)` as an intermediate fact. Express the relevant statement in the definitionally equal form `DomLE (wtS LL S m) mu`.

Rewrite using `[this]`. Conclude with `hd`.
-/
theorem isotypic_le_restrictSupport_dominated (mu : Fin n → ℤ) :
    isoSub (glOps R n LL S) mu ≤ MvPolynomial.restrictSupport R {m | DomLE (wtS LL S m) mu} := by
  have hE := isGLRep_glOps R (Fin N) LL n S
  refine (isotypic_le_lowering_span hE mu).trans ?_
  unfold hwvLoweringSpan
  rw [Submodule.span_le]
  rintro _ ⟨u, hu, w, hw, rfl⟩
  obtain ⟨ν, hd, hmem⟩ := lowering_weight_dominated (glOps R n LL S) hE.1 mu w hw.2.1 hu
  rw [SetLike.mem_coe, MvPolynomial.mem_restrictSupport_iff]
  intro m hm
  have := (monomials_are_weight_vectors R (Fin N) LL n S).2 ν _ hmem m (by simpa using hm)
  change DomLE (wtS LL S m) mu
  rw [this]
  exact hd

/- English proof (translation)
Distinguish the cases in `h0 : n = 0`. Substitute `h0` using the available equality. Introduce `a`. Conclude with `a.elim0`. Establish `: NeZero n` using `⟨h0⟩`.

Conclude with `Formalism.MainNotions.G.PolBridge.hwv_dominant D (weight_condition_from_integral_form D) LL S mu v hv`.
-/
theorem dominant_of_isHighestWeightVector (D : Formalism.BasicNotions.D7) (mu : Fin n → ℤ) (v : MvPolynomial (Fin N × Fin n) R)
    (hv : IsHWV (glOps R n LL S) mu v) : Dominant mu := by
  by_cases h0 : n = 0
  · subst h0
    intro a
    exact a.elim0
  · have : NeZero n := ⟨h0⟩
    exact Formalism.MainNotions.G.PolBridge.hwv_dominant D (weight_condition_from_integral_form D) LL S mu v hv

/- English proof (translation)
Rewrite using `[isoSub, Submodule.span_eq_bot]`. Introduce and unpack `x ⟨u, _, v, hv, rfl⟩`. Conclude with `absurd (dominant_of_isHighestWeightVector LL S D mu v hv) hmu`.
-/
theorem isoSub_glOps_eq_bot_of_not_dominant (D : Formalism.BasicNotions.D7) (mu : Fin n → ℤ) (hmu : ¬ Dominant mu) : isoSub (glOps R n LL S) mu = ⊥ := by
  rw [isoSub, Submodule.span_eq_bot]
  rintro x ⟨u, _, v, hv, rfl⟩
  exact absurd (dominant_of_isHighestWeightVector LL S D mu v hv) hmu

/- English proof (translation)
Assemble the required witnesses or components as `⟨sys.id_on mu, fun nu hne x hx => sys.zero_on mu nu hne x hx⟩`.
-/
theorem isIsotypicProj_of_decomposition {e : (Fin n → ℤ) → Module.End R (MvPolynomial (Fin N × Fin n) R)}
    (sys : DecSys (isoSub (glOps R n LL S)) e) (mu : Fin n → ℤ) : IsIsoProj (glOps R n LL S) mu (e mu) :=
  ⟨sys.id_on mu, fun nu hne x hx => sys.zero_on mu nu hne x hx⟩

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `hG mu hne`. Assume the negation of the conclusion as `hmu`. Apply `hne` to reduce the goal to its premises. Establish `hle : (⨆ lam ∈ pi, isoSub (glOps R n LL S) lam) ≤ LinearMap.ker (e mu)`.

Use `iSup₂_le fun lam hlam => ?_` and prove the remaining obligations. Introduce `x hx`. Establish `: lam ≠ mu` using `fun h => hmu (h ▸ hlam)`. Conclude with `sys.zero_on mu lam this x hx`. Conclude with `hle hG`.

Introduce `h`. Take `⟨T, hT⟩` from `sys.cover G`. Rewrite using `[hT]`. Use `Submodule.sum_mem _ fun mu _ => ?_` and prove the remaining obligations. Distinguish the cases in `h0 : e mu G = 0`.

Rewrite using `[h0]`. Conclude with `Submodule.zero_mem _`. Conclude with `(le_iSup₂ (f := fun lam (_ : lam ∈ pi) => isoSub (glOps R n LL S) lam) mu (h mu h0)) (sys.mem mu G)`.
-/
theorem mem_iSup_isotypic_iff_projections {e : (Fin n → ℤ) → Module.End R (MvPolynomial (Fin N × Fin n) R)}
    (sys : DecSys (isoSub (glOps R n LL S)) e) (pi : Set (Fin n → ℤ)) (G : MvPolynomial (Fin N × Fin n) R) :
    G ∈ (⨆ lam ∈ pi, isoSub (glOps R n LL S) lam) ↔ ∀ mu, e mu G ≠ 0 → mu ∈ pi := by
  classical
  constructor
  · intro hG mu hne
    by_contra hmu
    apply hne
    have hle : (⨆ lam ∈ pi, isoSub (glOps R n LL S) lam) ≤ LinearMap.ker (e mu) := by
      refine iSup₂_le fun lam hlam => ?_
      intro x hx
      have : lam ≠ mu := fun h => hmu (h ▸ hlam)
      exact sys.zero_on mu lam this x hx
    exact hle hG
  · intro h
    obtain ⟨T, hT⟩ := sys.cover G
    rw [hT]
    refine Submodule.sum_mem _ fun mu _ => ?_
    by_cases h0 : e mu G = 0
    · rw [h0]; exact Submodule.zero_mem _
    · exact (le_iSup₂ (f := fun lam (_ : lam ∈ pi) => isoSub (glOps R n LL S) lam) mu (h mu h0)) (sys.mem mu G)

/- English proof (translation)
Establish `he` using `isIsotypicProj_of_decomposition LL S sys`. Rewrite using `[polynomial_generated_eq_enveloping LL S dividedPower_formula_char_zero binomial_formula_char_zero]`. Introduce and unpack `ν ⟨x, hx, hx0, hxν⟩`. Establish `htop` using `isoSub_top (glOps R n LL S) D (weight_condition_from_integral_form D) (isGLRep_glOps R (Fin N) LL n S)`. Establish `hker : ∀ mu, e mu G = 0 → e mu x = 0`.

Introduce `mu h0`. Establish `hle : generatedSubmodule (glOps R n LL S) G ≤ LinearMap.ker (e mu)`. Rewrite using `[generatedSubmodule, Submodule.span_le]`. Introduce and unpack `_ ⟨u, hu, rfl⟩`. Express the relevant statement in the definitionally equal form `e mu (u G) = 0`.

Rewrite using `[isotypic_projection_commutes_monoid _ htop e he mu hu, h0, map_zero]`. Conclude with `hle hx`. Establish `hxZ : x ∈ MvPolynomial.restrictSupport R {m | ∃ lam ∈ pi, DomLE (wtS LL S m) lam}`. Take `⟨T, hT⟩` from `sys.cover x`. Rewrite using `[hT]`.

Use `Submodule.sum_mem _ fun mu _ => ?_` and prove the remaining obligations. Distinguish the cases in `h0 : e mu x = 0`. Rewrite using `[h0]`. Conclude with `Submodule.zero_mem _`. Establish `hG : e mu G ≠ 0` using `fun hz => h0 (hker mu hz)`.

Establish `h1` using `isotypic_le_restrictSupport_dominated LL S mu (sys.mem mu x)`. Rewrite `h1`, the goal using `[MvPolynomial.mem_restrictSupport_iff]`. Introduce `m hm`. Conclude with `⟨mu, h mu hG, h1 hm⟩`. Take `⟨m, hm⟩` from `MvPolynomial.support_nonempty.2 hx0`.

Establish `h2` using `(MvPolynomial.mem_restrictSupport_iff R).1 hxZ (by simpa using hm : m ∈ (x.support : Set _))`. Take `⟨lam, hlam, hle⟩` from `h2`. Conclude with `⟨lam, hlam, by rw [← hxν m hm]; exact hle⟩`.
-/
theorem weights_generated_dominated (D : Formalism.BasicNotions.D7) {e : (Fin n → ℤ) → Module.End R (MvPolynomial (Fin N × Fin n) R)}
    (sys : DecSys (isoSub (glOps R n LL S)) e) (G : MvPolynomial (Fin N × Fin n) R) (pi : Set (Fin n → ℤ))
    (h : ∀ mu, e mu G ≠ 0 → mu ∈ pi) :
    ∀ ν ∈ polWts LL S (polGenSub R LL S G), ∃ lam ∈ pi, DomLE ν lam := by
  classical
  have he := isIsotypicProj_of_decomposition LL S sys
  rw [polynomial_generated_eq_enveloping LL S dividedPower_formula_char_zero binomial_formula_char_zero]
  rintro ν ⟨x, hx, hx0, hxν⟩
  have htop := isoSub_top (glOps R n LL S) D (weight_condition_from_integral_form D) (isGLRep_glOps R (Fin N) LL n S)
  have hker : ∀ mu, e mu G = 0 → e mu x = 0 := by
    intro mu h0
    have hle : generatedSubmodule (glOps R n LL S) G ≤ LinearMap.ker (e mu) := by
      rw [generatedSubmodule, Submodule.span_le]
      rintro _ ⟨u, hu, rfl⟩
      change e mu (u G) = 0
      rw [isotypic_projection_commutes_monoid _ htop e he mu hu, h0, map_zero]
    exact hle hx
  have hxZ : x ∈ MvPolynomial.restrictSupport R {m | ∃ lam ∈ pi, DomLE (wtS LL S m) lam} := by
    obtain ⟨T, hT⟩ := sys.cover x
    rw [hT]
    refine Submodule.sum_mem _ fun mu _ => ?_
    by_cases h0 : e mu x = 0
    · rw [h0]; exact Submodule.zero_mem _
    · have hG : e mu G ≠ 0 := fun hz => h0 (hker mu hz)
      have h1 := isotypic_le_restrictSupport_dominated LL S mu (sys.mem mu x)
      rw [MvPolynomial.mem_restrictSupport_iff] at h1 ⊢
      intro m hm
      exact ⟨mu, h mu hG, h1 hm⟩
  obtain ⟨m, hm⟩ := MvPolynomial.support_nonempty.2 hx0
  have h2 := (MvPolynomial.mem_restrictSupport_iff R).1 hxZ (by simpa using hm : m ∈ (x.support : Set _))
  obtain ⟨lam, hlam, hle⟩ := h2
  exact ⟨lam, hlam, by rw [← hxν m hm]; exact hle⟩

end concrete

/- English proof (translation)
Introduce `F _ _ N LL n S pi hpi G`. Establish `h2` using `weight_condition_from_integral_form D`. Take `⟨e, sys⟩` from `isoDecomp (glOps F n LL S) D h2 (isGLRep_glOps F (Fin N) LL n S)`. Rewrite using `[mem_iSup_isotypic_iff_projections LL S sys pi G]`. Prove the components needed by the constructor for the conclusion.

Introduce `h ν hν hdom`. Take `⟨lam, hlam, hle⟩` from `weights_generated_dominated LL S D sys G pi h ν hν`. Conclude with `hpi.2 lam hlam ν hdom hle`. Introduce `h mu hne`. Establish `hw` using `isotypic_component_weight_mem LL S (stable_subspace_complete_reducibility D h2) polynomial_operators_gl_relations monomials_are_weight_vectors polynomial_locally_finite dividedPower_formula_char_zero binomial_formula_char_zero e (isIsotypicProj_of_decomposition LL S sys) G mu hne`.

Use `h mu hw ?_` and prove the remaining obligations. Assume the negation of the conclusion as `hnd`. Establish `h3` using `sys.mem mu G`. Rewrite `h3` using `[isoSub_glOps_eq_bot_of_not_dominant LL S D mu hnd]`. Conclude with `hne ((Submodule.mem_bot F).1 h3)`.
-/
theorem restTypes (D : Formalism.BasicNotions.D7) : RestTypes := by
  classical
  intro F _ _ N LL n S pi hpi G
  have h2 := weight_condition_from_integral_form D
  obtain ⟨e, sys⟩ := isoDecomp (glOps F n LL S) D h2 (isGLRep_glOps F (Fin N) LL n S)
  rw [mem_iSup_isotypic_iff_projections LL S sys pi G]
  constructor
  · intro h ν hν hdom
    obtain ⟨lam, hlam, hle⟩ := weights_generated_dominated LL S D sys G pi h ν hν
    exact hpi.2 lam hlam ν hdom hle
  · intro h mu hne
    have hw := isotypic_component_weight_mem LL S (stable_subspace_complete_reducibility D h2) polynomial_operators_gl_relations monomials_are_weight_vectors polynomial_locally_finite dividedPower_formula_char_zero binomial_formula_char_zero
      e (isIsotypicProj_of_decomposition LL S sys) G mu hne
    refine h mu hw ?_
    by_contra hnd
    have h3 := sys.mem mu G
    rw [isoSub_glOps_eq_bot_of_not_dominant LL S D mu hnd] at h3
    exact hne ((Submodule.mem_bot F).1 h3)

/- English proof (translation)
Establish `hidx : Formalism.InvariantFactorPaths.GelfandTsetlinBases.IsIndex (pEnd P.mu) I` using `((restStd n N P.mu I).1 hI).1`. Establish `hidx' : Formalism.InvariantFactorPaths.GelfandTsetlinBases.IsIndex (ext P.mu N) I` using `by rw [ext_last]; exact hidx`. Establish `h1` using `restPsi R n N LL B P I hidx`. Establish `h2 : Formalism.InvariantFactorPaths.GelfandTsetlinBases.psiPath R (isV LL) (ext P.mu) N I ∈ Formalism.InvariantFactorPaths.GelfandTsetlinBases.polB R n N (Bn B)`. Rewrite using `[Formalism.InvariantFactorPaths.GelfandTsetlinBases.polB, Submodule.mem_iInf]`.

Introduce `j`. Conclude with `(Formalism.InvariantFactorPaths.GelfandTsetlinBases.pathProductDegrees R n N (isV LL) (Bn B) (ext P.mu) I (restPathTo n N LL B P) hidx').2 j`. Rewrite `h2` using `[← h1, ← restPol R n N B]`. Take `⟨y, hy, hyx⟩` from `h2`. Establish `: y = Psi R P.mu I` using `rename_injective _ (iv_inj N n) hyx`.

Rewrite using `[← this]`. Conclude with `hy`.
-/
theorem standardWord_mem_multihomogeneous (R : Type) [CommRing R] {n N : ℕ} {LL : Letters (Fin N)} {B : Fin N → ℕ} (P : PPath n N LL B)
    (I : ℤ → Finset (Fin n)) (hI : IsSt P.mu I) : Psi R P.mu I ∈ Pol R n B := by
  have hidx : Formalism.InvariantFactorPaths.GelfandTsetlinBases.IsIndex (pEnd P.mu) I := ((restStd n N P.mu I).1 hI).1
  have hidx' : Formalism.InvariantFactorPaths.GelfandTsetlinBases.IsIndex (ext P.mu N) I := by rw [ext_last]; exact hidx
  have h1 := restPsi R n N LL B P I hidx
  have h2 : Formalism.InvariantFactorPaths.GelfandTsetlinBases.psiPath R (isV LL) (ext P.mu) N I ∈ Formalism.InvariantFactorPaths.GelfandTsetlinBases.polB R n N (Bn B) := by
    rw [Formalism.InvariantFactorPaths.GelfandTsetlinBases.polB, Submodule.mem_iInf]
    intro j
    exact (Formalism.InvariantFactorPaths.GelfandTsetlinBases.pathProductDegrees R n N (isV LL) (Bn B) (ext P.mu) I (restPathTo n N LL B P) hidx').2 j
  rw [← h1, ← restPol R n N B] at h2
  obtain ⟨y, hy, hyx⟩ := h2
  have : y = Psi R P.mu I := rename_injective _ (iv_inj N n) hyx
  rw [← this]
  exact hy

/- English proof (translation)
Introduce `F _ _ N n LL B i pi hpi`. Use extensionality with `G`. Rewrite using `[Submodule.mem_inf]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨hG, hT⟩`.

Conclude with `(admissible_word_basis D F N n LL B i pi hpi G hG).2 ((restTypes D F N LL n _ pi hpi G).1 hT)`. Introduce `hG`. Establish `hP : G ∈ Pol F n B`. Use `(Submodule.span_le.2 ?_) hG` and prove the remaining obligations. Introduce and unpack `_ ⟨P, I, hI, -, rfl⟩`.

Conclude with `standardWord_mem_multihomogeneous F P I hI`. Conclude with `⟨hP, (restTypes D F N LL n _ pi hpi G).2 ((admissible_word_basis D F N n LL B i pi hpi G hP).1 hG)⟩`.
-/
theorem lower_set_types_span (D : Formalism.BasicNotions.D7) : LowerSetTypesSpan := by
  intro F _ _ N n LL B i pi hpi
  ext G
  rw [Submodule.mem_inf]
  constructor
  · rintro ⟨hG, hT⟩
    exact (admissible_word_basis D F N n LL B i pi hpi G hG).2 ((restTypes D F N LL n _ pi hpi G).1 hT)
  · intro hG
    have hP : G ∈ Pol F n B := by
      refine (Submodule.span_le.2 ?_) hG
      rintro _ ⟨P, I, hI, -, rfl⟩
      exact standardWord_mem_multihomogeneous F P I hI
    exact ⟨hP, (restTypes D F N LL n _ pi hpi G).2 ((admissible_word_basis D F N n LL B i pi hpi G hP).1 hG)⟩

section comm

variable {F : Type} [Field F] {N : ℕ} (LL : Letters (Fin N)) {n : ℕ}

/- English proof (translation)
Simplify using `only [glAct, ← Finset.sum_add_distrib]`. Use `Finset.sum_congr rfl fun l _ => ?_` and prove the remaining obligations. Distinguish the cases in `h1 : l ∈ S`. Establish `h2 : l ∈ S'` using `h h1`. Simplify using `[h1, h2, Set.mem_diff]`.

Distinguish the cases in `h2 : l ∈ S'`. Simplify using `[h1, h2, Set.mem_diff]`. Simplify using `[h1, h2, Set.mem_diff]`.
-/
theorem glAct_eq_add_glAct_diff (S S' : Set (Fin N)) (h : S ⊆ S') (a b : Fin n) :
    glAct F LL S' a b = glAct F LL S a b + glAct F LL (S' \ S) a b := by
  classical
  simp only [glAct, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun l _ => ?_
  by_cases h1 : l ∈ S
  · have h2 : l ∈ S' := h h1
    simp [h1, h2, Set.mem_diff]
  · by_cases h2 : l ∈ S'
    · simp [h1, h2, Set.mem_diff]
    · simp [h1, h2, Set.mem_diff]

/- English proof (translation)
Apply `MvPolynomial.derivation_ext` to reduce the goal to its premises. Introduce and unpack `⟨l, x⟩`. Rewrite using `[Derivation.commutator_apply]`. Distinguish the cases in `hS : l ∈ S`. Establish `hT` using `hd l hS`.

Simplify using `only [isoPolDer_X, hS, hT, if_true, if_false, map_zero]`. Apply the tactic sequence `split_ifs <;> simp [isoPolDer_X, hT]`. Apply the tactic sequence `simp only [isoPolDer_X, hS, if_false, map_zero] split_ifs <;> simp [isoPolDer_X, hS]`.
-/
theorem lie_polarizationDer_eq_zero_of_disjoint (S T : Set (Fin N)) (hd : ∀ l, l ∈ S → l ∉ T) (a b c d : Fin n) :
    ⁅isoPolDer F LL S a b, isoPolDer F LL T c d⁆ = 0 := by
  apply MvPolynomial.derivation_ext
  rintro ⟨l, x⟩
  rw [Derivation.commutator_apply]
  by_cases hS : l ∈ S
  · have hT := hd l hS
    simp only [isoPolDer_X, hS, hT, if_true, if_false, map_zero]
    split_ifs <;> simp [isoPolDer_X, hT]
  · simp only [isoPolDer_X, hS, if_false, map_zero]
    split_ifs <;> simp [isoPolDer_X, hS]

/- English proof (translation)
Establish `hsumD : ∀ (s : Finset (Fin N)) (f : Fin N → Derivation F (MvPolynomial (Fin N × Fin n) F) (MvPolynomial (Fin N × Fin n) F)) (H : MvPolynomial (Fin N × Fin n) F), (∑ l ∈ s, f l) H = ∑ l ∈ s, f l H`. Introduce `s f H`. Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty => simp`. Consider the case `insert i s hi ih => rw [Finset.sum_insert hi, Finset.sum_insert hi, Derivation.add_apply, ih]`.

Establish `hS : ∀ (U : Set (Fin N)) (p q : Fin n) (H : MvPolynomial (Fin N × Fin n) F), glAct F LL U p q H = isoPolDer F LL U p q H`. Introduce `U p q H`. Simplify using `only [glAct, isoPolDer, LinearMap.sum_apply, hsumD]`. Use `Finset.sum_congr rfl fun l _ => ?_` and prove the remaining obligations. Apply the tactic sequence `split_ifs <;> simp [smul_eq_mul]`.

Establish `h` using `congrArg (fun D => D G) (lie_polarizationDer_eq_zero_of_disjoint LL S T hd a b c d)`. Simplify using `only [Derivation.commutator_apply] at h`. Rewrite using `[hS, hS, hS, hS]`. Conclude with `sub_eq_zero.1 h`.
-/
theorem glAct_commute_of_disjoint (S T : Set (Fin N)) (hd : ∀ l, l ∈ S → l ∉ T) (a b c d : Fin n)
    (G : MvPolynomial (Fin N × Fin n) F) :
    glAct F LL S a b (glAct F LL T c d G) = glAct F LL T c d (glAct F LL S a b G) := by
  have hsumD : ∀ (s : Finset (Fin N))
      (f : Fin N → Derivation F (MvPolynomial (Fin N × Fin n) F) (MvPolynomial (Fin N × Fin n) F))
      (H : MvPolynomial (Fin N × Fin n) F), (∑ l ∈ s, f l) H = ∑ l ∈ s, f l H := by
    intro s f H
    classical
    induction s using Finset.induction_on with
    | empty => simp
    | insert i s hi ih => rw [Finset.sum_insert hi, Finset.sum_insert hi, Derivation.add_apply, ih]
  have hS : ∀ (U : Set (Fin N)) (p q : Fin n) (H : MvPolynomial (Fin N × Fin n) F),
      glAct F LL U p q H = isoPolDer F LL U p q H := by
    intro U p q H
    simp only [glAct, isoPolDer, LinearMap.sum_apply, hsumD]
    refine Finset.sum_congr rfl fun l _ => ?_
    split_ifs <;> simp [smul_eq_mul]
  have h := congrArg (fun D => D G) (lie_polarizationDer_eq_zero_of_disjoint LL S T hd a b c d)
  simp only [Derivation.commutator_apply] at h
  rw [hS, hS, hS, hS]
  exact sub_eq_zero.1 h

variable [CharZero F]

/- English proof (translation)
Establish `h2` using `weight_condition_from_integral_form D`. Establish `hT` using `isoSub_top (glOps F n LL S) D h2 (isGLRep_glOps F (Fin N) LL n S)`. Establish `hT'` using `isoSub_top (glOps F n LL S') D h2 (isGLRep_glOps F (Fin N) LL n S')`. Establish `h1 : ∀ a b, e * (glOps F n LL S' a b) = (glOps F n LL S' a b) * e`. Introduce `a b`.

Use `isotypic_projector_commutes _ hT lam e he _ ?_` and prove the remaining obligations. Introduce `mu x hx`. Establish `hs : glOps F n LL S' a b x = glOps F n LL S a b x + glAct F LL (S' \ S) a b x` using `by show glAct F LL S' a b x = _`. Rewrite using `[glAct_eq_add_glAct_diff LL S S' h a b]`. Both sides reduce to the same expression.

Rewrite using `[hs]`. Use `Submodule.add_mem _ (isotypic_stable_operator _ mu a b hx) ?_` and prove the remaining obligations. Conclude with `isoSub_map_of_comm _ (glAct F LL (S' \ S) a b) (fun c d y => glAct_commute_of_disjoint LL (S' \ S) S (fun l hl => hl.2) a b c d y) mu x hx`. Establish `h3 : ∀ mu, ∀ x ∈ isoSub (glOps F n LL S') mu, e x ∈ isoSub (glOps F n LL S') mu` using `fun mu => isoSub_map_of_comm _ e (fun a b x => by`. Use `congrArg (fun f : Module.End F (MvPolynomial (Fin N × Fin n) F) => f x) (h1 a b)` as an intermediate fact.

Simplify using `using this) mu`. Conclude with `(isotypic_projector_commutes _ hT' lam' e' he' e h3).symm`.
-/
theorem isotypicProj_commute_of_subset (D : Formalism.BasicNotions.D7) (S S' : Set (Fin N)) (h : S ⊆ S') (lam lam' : Fin n → ℤ)
    (e e' : Module.End F (MvPolynomial (Fin N × Fin n) F)) (he : IsIsoProj (glOps F n LL S) lam e)
    (he' : IsIsoProj (glOps F n LL S') lam' e') : e * e' = e' * e := by
  have h2 := weight_condition_from_integral_form D
  have hT := isoSub_top (glOps F n LL S) D h2 (isGLRep_glOps F (Fin N) LL n S)
  have hT' := isoSub_top (glOps F n LL S') D h2 (isGLRep_glOps F (Fin N) LL n S')
  have h1 : ∀ a b, e * (glOps F n LL S' a b) = (glOps F n LL S' a b) * e := by
    intro a b
    refine isotypic_projector_commutes _ hT lam e he _ ?_
    intro mu x hx
    have hs : glOps F n LL S' a b x = glOps F n LL S a b x + glAct F LL (S' \ S) a b x := by
      show glAct F LL S' a b x = _
      rw [glAct_eq_add_glAct_diff LL S S' h a b]
      rfl
    rw [hs]
    refine Submodule.add_mem _ (isotypic_stable_operator _ mu a b hx) ?_
    exact isoSub_map_of_comm _ (glAct F LL (S' \ S) a b)
      (fun c d y => glAct_commute_of_disjoint LL (S' \ S) S (fun l hl => hl.2) a b c d y) mu x hx
  have h3 : ∀ mu, ∀ x ∈ isoSub (glOps F n LL S') mu, e x ∈ isoSub (glOps F n LL S') mu :=
    fun mu => isoSub_map_of_comm _ e (fun a b x => by
      have := congrArg (fun f : Module.End F (MvPolynomial (Fin N × Fin n) F) => f x) (h1 a b)
      simpa using this) mu
  exact (isotypic_projector_commutes _ hT' lam' e' he' e h3).symm

/- English proof (translation)
Break down `le_total i j with hij | hij` into its components or cases. Conclude with `isotypicProj_commute_of_subset LL D _ _ (fun l (hl : l.val < i.val) => lt_of_lt_of_le hl hij) lam lam' e e' he he'`. Conclude with `(isotypicProj_commute_of_subset LL D _ _ (fun l (hl : l.val < j.val) => lt_of_lt_of_le hl hij) lam' lam e' e he' he).symm`.
-/
theorem isotypicProj_commute_prefix (D : Formalism.BasicNotions.D7) (i j : Fin (N + 1)) (lam lam' : Fin n → ℤ)
    (e e' : Module.End F (MvPolynomial (Fin N × Fin n) F))
    (he : IsIsoProj (glOps F n LL {l | l.val < i.val}) lam e)
    (he' : IsIsoProj (glOps F n LL {l | l.val < j.val}) lam' e') : e * e' = e' * e := by
  rcases le_total i j with hij | hij
  · exact isotypicProj_commute_of_subset LL D _ _ (fun l (hl : l.val < i.val) => lt_of_lt_of_le hl hij) lam lam' e e' he he'
  · exact (isotypicProj_commute_of_subset LL D _ _ (fun l (hl : l.val < j.val) => lt_of_lt_of_le hl hij) lam' lam e' e he' he).symm

end comm

/- English proof (translation)
Introduce `F _ _ N n LL i j lam lam' e e' he he'`. Conclude with `isotypicProj_commute_prefix LL D i j lam lam' e e' he he'`.
-/
theorem isotypic_projections_commute_holds (D : Formalism.BasicNotions.D7) : Formalism.MainNotions.CovariantDegrees.TypeDecompositionsCommute D := by
  intro F _ _ N n LL i j lam lam' e e' he he'
  exact isotypicProj_commute_prefix LL D i j lam lam' e e' he he'

end Formalism.MainNotions.G.ColumnFamilies

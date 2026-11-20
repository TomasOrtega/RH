import Mathlib
import Development.AutomorphicSpectrum.Statements.GeometryStatements.CmpPair
import Development.AutomorphicSpectrum.Statements.GeometryStatements.CmpSt
import Development.AutomorphicSpectrum.Statements.GeometryStatements.PadicIntegersHenselianFiniteResidue
import Development.AutomorphicSpectrum.Statements.GeometryStatements.HodgeComparisonCompatibility
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaUnifAV
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.Proportional
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.GrGenOfIsFlagVBOn
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.DegreeLatticeQuotientFormsStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.FlagVectorBundleTransportStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.SectionNormIsomorphicLinesStatement

open MvPolynomial AlgebraicGeometry CategoryTheory NumberField Filter Topology ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cmp
open ReciprocityTheory.ChartRestriction.G.AI.I1 (IsBlockMap pullDeg)
open ReciprocityTheory.ChartRestriction.G.AI.I4 (IsPullHerm imageZ blockFnField)
open scoped ComplexOrder

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Cmp.RootIso

section Scheme

variable {X X' : Scheme.{0}} {Ω : Type} [Field Ω]

/- English proof (translation)
Use `h.map e.inv.continuous` as an intermediate fact. Simplify using `using this`.
-/
theorem specializes_iso (e : X' ≅ X) {a b : X'} (h : e.hom a ⤳ e.hom b) : a ⤳ b := by
  have := h.map e.inv.continuous
  simpa using this

/- English proof (translation)
The claim follows from `ConcreteCategory.bijective_of_isIso _`.
-/
theorem stalkMap_bijective (e : X' ≅ X) (x : X') : Function.Bijective (e.hom.stalkMap x).hom :=
  ConcreteCategory.bijective_of_isIso _

/- English proof (translation)
Establish `e` using `Scheme.Hom.stalkSpecializes_stalkMap g _ _ q.2`. Establish `e2` using `congrArg (fun t => (t ≫ Scheme.stalkClosedPointTo ξ').hom s) e`. Establish `e3` using `Scheme.stalkClosedPointTo_comp ξ' g`. Establish `e4` using `congrArg (fun t => (X.presheaf.stalkSpecializes h ≫ t).hom s) e3`. Conclude with `e2.symm.trans e4.symm`.
-/
theorem genMap_stalk (ξ' : Spec (CommRingCat.of Ω) ⟶ X') (g : X' ⟶ X) (q : Cpt ξ')
    (h : genPt (ξ' ≫ g) ⤳ g q.1) (s : X.presheaf.stalk (g q.1)) :
    genMap ξ' q ((g.stalkMap q.1).hom s) = genMap (ξ' ≫ g) ⟨g q.1, h⟩ s := by
  have e := Scheme.Hom.stalkSpecializes_stalkMap g _ _ q.2
  have e2 := congrArg (fun t => (t ≫ Scheme.stalkClosedPointTo ξ').hom s) e
  have e3 := Scheme.stalkClosedPointTo_comp ξ' g
  have e4 := congrArg (fun t => (X.presheaf.stalkSpecializes h ≫ t).hom s) e3
  exact e2.symm.trans e4.symm

/- English proof (translation)
Substitute `hξ` using the available equality. Use extensionality with `a`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨s, rfl⟩`. Take `⟨t, rfl⟩` from `(stalkMap_bijective e q.1).2 s`.

Conclude with `⟨t, (genMap_stalk ξ' e.hom q h t).symm⟩`. Introduce and unpack `⟨t, rfl⟩`. Conclude with `⟨_, genMap_stalk ξ' e.hom q h t⟩`.
-/
theorem regAt_eq (e : X' ≅ X) {ξ : Spec (CommRingCat.of Ω) ⟶ X} {ξ' : Spec (CommRingCat.of Ω) ⟶ X'}
    (hξ : ξ' ≫ e.hom = ξ) (q : Cpt ξ') (h : genPt ξ ⤳ e.hom q.1) :
    regAt ξ' q = regAt ξ ⟨e.hom q.1, h⟩ := by
  subst hξ
  ext a
  constructor
  · rintro ⟨s, rfl⟩
    obtain ⟨t, rfl⟩ := (stalkMap_bijective e q.1).2 s
    exact ⟨t, (genMap_stalk ξ' e.hom q h t).symm⟩
  · rintro ⟨t, rfl⟩
    exact ⟨_, genMap_stalk ξ' e.hom q h t⟩

/- English proof (translation)
Simplify using `only [InChart, regAt_eq e hξ q h]`.
-/
theorem inChart_iff (e : X' ≅ X) {ξ : Spec (CommRingCat.of Ω) ⟶ X} {ξ' : Spec (CommRingCat.of Ω) ⟶ X'}
    (hξ : ξ' ≫ e.hom = ξ) (q : Cpt ξ') (h : genPt ξ ⤳ e.hom q.1) {κ : Type} (x : κ → Ω) (c : κ) :
    InChart ξ x c ⟨e.hom q.1, h⟩ ↔ InChart ξ' x c q := by
  simp only [InChart, regAt_eq e hξ q h]

variable {R : Type} [CommRing R] [IsLocalRing R]

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨h, s, hs, hr⟩`. Establish `h' : genPt ξ' ⤳ centre z` using `specializes_iso e h`. Use `⟨h', (e.hom.stalkMap (centre z)).hom s, ?_, ?_⟩` and prove the remaining obligations. Conclude with `(genMap_stalk ξ' e.hom ⟨centre z, h'⟩ h s).trans hs`.

Rewrite using `[← hr]`. Conclude with `(congrArg (fun t => t.hom s) (Scheme.stalkClosedPointTo_comp z e.hom)).symm`. Introduce and unpack `⟨h', s', hs, hr⟩`. Take `⟨s, rfl⟩` from `(stalkMap_bijective e (centre z)).2 s'`. Establish `h : genPt (ξ' ≫ e.hom) ⤳ e.hom (centre z)` using `h'.map e.hom.continuous`.

Use `⟨h, s, ?_, ?_⟩` and prove the remaining obligations. Conclude with `(genMap_stalk ξ' e.hom ⟨centre z, h'⟩ h s).symm.trans hs`. Rewrite using `[← hr]`. Conclude with `congrArg (fun t => t.hom s) (Scheme.stalkClosedPointTo_comp z e.hom)`.
-/
theorem valAt_iso (e : X' ≅ X) (ξ' : Spec (CommRingCat.of Ω) ⟶ X') (z : Spec (CommRingCat.of R) ⟶ X') (a : Ω) (r : R) :
    ValAt (ξ' ≫ e.hom) (z ≫ e.hom) a r ↔ ValAt ξ' z a r := by
  constructor
  · rintro ⟨h, s, hs, hr⟩
    have h' : genPt ξ' ⤳ centre z := specializes_iso e h
    refine ⟨h', (e.hom.stalkMap (centre z)).hom s, ?_, ?_⟩
    · exact (genMap_stalk ξ' e.hom ⟨centre z, h'⟩ h s).trans hs
    · rw [← hr]
      exact (congrArg (fun t => t.hom s) (Scheme.stalkClosedPointTo_comp z e.hom)).symm
  · rintro ⟨h', s', hs, hr⟩
    obtain ⟨s, rfl⟩ := (stalkMap_bijective e (centre z)).2 s'
    have h : genPt (ξ' ≫ e.hom) ⤳ e.hom (centre z) := h'.map e.hom.continuous
    refine ⟨h, s, ?_, ?_⟩
    · exact (genMap_stalk ξ' e.hom ⟨centre z, h'⟩ h s).symm.trans hs
    · rw [← hr]
      exact congrArg (fun t => t.hom s) (Scheme.stalkClosedPointTo_comp z e.hom)

/- English proof (translation)
Simplify using `only [CoordsAt, valAt_iso]`.
-/
theorem coordsAt_iso (e : X' ≅ X) (ξ' : Spec (CommRingCat.of Ω) ⟶ X') (z : Spec (CommRingCat.of R) ⟶ X')
    {K : Type} {ι : K → Type} (y : (Σ k, ι k) → Ω) (w : (Σ k, ι k) → R) :
    CoordsAt (ξ' ≫ e.hom) y (z ≫ e.hom) w ↔ CoordsAt ξ' y z w := by
  simp only [CoordsAt, valAt_iso]

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {y : (Σ k, ι k) → Ω}

/- English proof (translation)
Take `⟨h1, h2, h3⟩` from `h`. Use `⟨h1, (coordsAt_iso e ξ' z y w).2 h2, fun d hd => ?_⟩` and prove the remaining obligations. Take `⟨u, hu, hν⟩` from `h3 d hd`. Conclude with `⟨u, (valAt_iso e ξ' z _ u).2 hu, hν⟩`.
-/
theorem secNorm_iso (e : X' ≅ X) {ξ' : Spec (CommRingCat.of Ω) ⟶ X'} {z : Spec (CommRingCat.of ℂ) ⟶ X'}
    {A : HermLine ι} {c : Ω} {w : (Σ k, ι k) → ℂ} {t : Ω} {ν : ℝ} (h : SecNorm ξ' y A c z w t ν) :
    SecNorm (ξ' ≫ e.hom) y A c (z ≫ e.hom) w t ν := by
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨h1, (coordsAt_iso e ξ' z y w).2 h2, fun d hd => ?_⟩
  obtain ⟨u, hu, hν⟩ := h3 d hd
  exact ⟨u, (valAt_iso e ξ' z _ u).2 hu, hν⟩

/- English proof (translation)
Take `⟨h1, h2, h3⟩` from `h`. Use `⟨mul_ne_zero hκ h1, h2, fun d hd => ?_⟩` and prove the remaining obligations. Take `⟨u, hu, hν⟩` from `h3 d hd`. Use `⟨u, ?_, hν⟩` and prove the remaining obligations. Rewrite using `[mul_left_comm, mul_div_mul_left _ _ hκ]` and apply the resulting hypothesis.
-/
theorem secNorm_scale {ξ : Spec (CommRingCat.of Ω) ⟶ X} {z : Spec (CommRingCat.of ℂ) ⟶ X}
    {A : HermLine ι} {c : Ω} {w : (Σ k, ι k) → ℂ} {t : Ω} {ν : ℝ} (h : SecNorm ξ y A c z w t ν) {κ : Ω} (hκ : κ ≠ 0) :
    SecNorm ξ y A (κ * c) z w (κ * t) ν := by
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨mul_ne_zero hκ h1, h2, fun d hd => ?_⟩
  obtain ⟨u, hu, hν⟩ := h3 d hd
  refine ⟨u, ?_, hν⟩
  rwa [mul_left_comm, mul_div_mul_left _ _ hκ]

end Scheme

section FlagAlg

variable {Ω : Type} [Field Ω] {E E' : Type} [AddCommGroup E] [Module Ω E] [AddCommGroup E'] [Module Ω E']

/- English proof (translation)
Unfold `flagStep`. Rewrite using `[Submodule.map_span, Set.image_image]`.
-/
theorem flagStep_comp (f : E →ₗ[Ω] E') {r : ℕ} (b : Fin r → E) (i : ℕ) :
    flagStep Ω (fun k => f (b k)) i = (flagStep Ω b i).map f := by
  unfold flagStep
  rw [Submodule.map_span, Set.image_image]

/- English proof (translation)
Establish `hmem : b₁ j ∈ flagStep Ω b₂ ((j : ℕ) + 1)`. Rewrite using `[← hF]`. Conclude with `Submodule.subset_span ⟨j, by simp, rfl⟩`. Establish `hsub : flagStep Ω b₂ ((j : ℕ) + 1) ≤ Submodule.span Ω {b₂ j} ⊔ flagStep Ω b₂ j`. Use `Submodule.span_le.2 ?_` and prove the remaining obligations.

Introduce and unpack `_ ⟨l, hl, rfl⟩`. Break down `Nat.lt_succ_iff_lt_or_eq.1 hl with h | h` into its components or cases. Conclude with `Submodule.mem_sup_right (Submodule.subset_span ⟨l, h, rfl⟩)`. Establish `: l = j` using `Fin.ext h`. Substitute `this` using the available equality.

Conclude with `Submodule.mem_sup_left (Submodule.mem_span_singleton_self _)`. Take `⟨a, ha, c, hc, e⟩` from `Submodule.mem_sup.1 (hsub hmem)`. Take `⟨μ, rfl⟩` from `Submodule.mem_span_singleton.1 ha`. Establish `hd : b₁ j - μ • b₂ j ∈ flagStep Ω b₂ j` using `by rw [← e]; simpa using hc`. Use `⟨μ, fun h0 => ?_, hd⟩` and prove the remaining obligations.

Rewrite `hd` using `[h0, zero_smul, sub_zero, ← hF]`. Conclude with `hb.notMem_span_image (s := {k | (k : ℕ) < j}) (x := j) (by simp) hd`.
-/
theorem exists_scale {r : ℕ} {b₁ b₂ : Fin r → E} (hF : ∀ s : ℕ, flagStep Ω b₁ s = flagStep Ω b₂ s)
    (hb : LinearIndependent Ω b₁) (j : Fin r) : ∃ μ : Ω, μ ≠ 0 ∧ b₁ j - μ • b₂ j ∈ flagStep Ω b₂ j := by
  have hmem : b₁ j ∈ flagStep Ω b₂ ((j : ℕ) + 1) := by
    rw [← hF]
    exact Submodule.subset_span ⟨j, by simp, rfl⟩
  have hsub : flagStep Ω b₂ ((j : ℕ) + 1) ≤ Submodule.span Ω {b₂ j} ⊔ flagStep Ω b₂ j := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨l, hl, rfl⟩
    rcases Nat.lt_succ_iff_lt_or_eq.1 hl with h | h
    · exact Submodule.mem_sup_right (Submodule.subset_span ⟨l, h, rfl⟩)
    · have : l = j := Fin.ext h
      subst this
      exact Submodule.mem_sup_left (Submodule.mem_span_singleton_self _)
  obtain ⟨a, ha, c, hc, e⟩ := Submodule.mem_sup.1 (hsub hmem)
  obtain ⟨μ, rfl⟩ := Submodule.mem_span_singleton.1 ha
  have hd : b₁ j - μ • b₂ j ∈ flagStep Ω b₂ j := by rw [← e]; simpa using hc
  refine ⟨μ, fun h0 => ?_, hd⟩
  rw [h0, zero_smul, sub_zero, ← hF] at hd
  exact hb.notMem_span_image (s := {k | (k : ℕ) < j}) (x := j) (by simp) hd

variable {X : Scheme.{0}} {ξ : Spec (CommRingCat.of Ω) ⟶ X}

/- English proof (translation)
Proceed by induction on `hx using Submodule.span_induction with`. Consider the case `mem t ht`. Take `⟨v, hv, hd⟩` from `ht`. Use `Submodule.subset_span ⟨v, hv, ?_⟩` and prove the remaining obligations. Rewrite `hd` using `[hF]`.

Establish `: v - (μ * t) • b₂ j = (v - t • b₁ j) + t • (b₁ j - μ • b₂ j)`. Simplify using `only [smul_sub, smul_smul, mul_comm t μ]`. Normalize the expressions using the abelian group laws. Rewrite using `[this]`. Conclude with `add_mem hd (Submodule.smul_mem _ _ h)`.

Consider the case `zero => simp`. Consider the case `add a c _ _ ha hc => rw [mul_add]`. Conclude with `add_mem ha hc`. Consider the case `smul c a _ ha`. Establish `: μ * c • a = c • (μ * a)` using `by show μ * ((c : Ω) * a) = (c : Ω) * (μ * a)`.

Expand and normalize the polynomial expressions, which then agree. Rewrite using `[this]`. Conclude with `Submodule.smul_mem _ _ ha`.
-/
theorem graded_line_scale (L : Lat ξ E) {r : ℕ} {b₁ b₂ : Fin r → E} (j : Fin r) {μ : Ω}
    (hF : flagStep Ω b₁ j = flagStep Ω b₂ j) (h : b₁ j - μ • b₂ j ∈ flagStep Ω b₂ j) (p : Cpt ξ) {x : Ω}
    (hx : x ∈ L.gr b₁ j p) : μ * x ∈ L.gr b₂ j p := by
  induction hx using Submodule.span_induction with
  | mem t ht =>
    obtain ⟨v, hv, hd⟩ := ht
    refine Submodule.subset_span ⟨v, hv, ?_⟩
    rw [hF] at hd
    have : v - (μ * t) • b₂ j = (v - t • b₁ j) + t • (b₁ j - μ • b₂ j) := by
      simp only [smul_sub, smul_smul, mul_comm t μ]
      abel
    rw [this]
    exact add_mem hd (Submodule.smul_mem _ _ h)
  | zero => simp
  | add a c _ _ ha hc => rw [mul_add]; exact add_mem ha hc
  | smul c a _ ha =>
    have : μ * c • a = c • (μ * a) := by
      show μ * ((c : Ω) * a) = (c : Ω) * (μ * a)
      ring
    rw [this]
    exact Submodule.smul_mem _ _ ha

/- English proof (translation)
Use `⟨graded_line_scale L j hF h p, fun hx => ?_⟩` and prove the remaining obligations. Establish `h' : b₂ j - μ⁻¹ • b₁ j ∈ flagStep Ω b₁ j`. Establish `: b₂ j - μ⁻¹ • b₁ j = (-μ⁻¹) • (b₁ j - μ • b₂ j)`. Simplify using `only [smul_sub, smul_smul, neg_mul, inv_mul_cancel₀ hμ, neg_smul, one_smul]`. Normalize the expressions using the abelian group laws.

Rewrite using `[this, hF]`. Conclude with `Submodule.smul_mem _ _ h`. Use `graded_line_scale L j hF.symm h' p hx` as an intermediate fact. Rewrite `this` using `[inv_mul_cancel_left₀ hμ]`. Then use the resulting hypothesis.
-/
theorem gr_scale (L : Lat ξ E) {r : ℕ} {b₁ b₂ : Fin r → E} (j : Fin r) {μ : Ω} (hμ : μ ≠ 0)
    (hF : flagStep Ω b₁ j = flagStep Ω b₂ j) (h : b₁ j - μ • b₂ j ∈ flagStep Ω b₂ j) (p : Cpt ξ) (x : Ω) :
    x ∈ L.gr b₁ j p ↔ μ * x ∈ L.gr b₂ j p := by
  refine ⟨graded_line_scale L j hF h p, fun hx => ?_⟩
  have h' : b₂ j - μ⁻¹ • b₁ j ∈ flagStep Ω b₁ j := by
    have : b₂ j - μ⁻¹ • b₁ j = (-μ⁻¹) • (b₁ j - μ • b₂ j) := by
      simp only [smul_sub, smul_smul, neg_mul, inv_mul_cancel₀ hμ, neg_smul, one_smul]
      abel
    rw [this, hF]
    exact Submodule.smul_mem _ _ h
  have := graded_line_scale L j hF.symm h' p hx
  rwa [inv_mul_cancel_left₀ hμ] at this

/- English proof (translation)
Rewrite using `[Submodule.mem_span_singleton]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨c, rfl⟩`. Establish `: c • g / g = (c : Ω)` using `by show (c : Ω) * g / g = c`. Clear the denominators using the available nonvanishing facts.

Rewrite using `[this]`. Conclude with `c.2`. Introduce `h`. Use `⟨⟨_, h⟩, ?_⟩` and prove the remaining obligations. Use `show a / g * g = a`.

Clear the denominators using the available nonvanishing facts.
-/
theorem mem_span_iff {R : Subring Ω} {g a : Ω} (hg : g ≠ 0) : a ∈ Submodule.span R {g} ↔ a / g ∈ R := by
  rw [Submodule.mem_span_singleton]
  constructor
  · rintro ⟨c, rfl⟩
    have : c • g / g = (c : Ω) := by
      show (c : Ω) * g / g = c
      field_simp
    rw [this]
    exact c.2
  · intro h
    refine ⟨⟨_, h⟩, ?_⟩
    show a / g * g = a
    field_simp

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `h`. Use `⟨(mem_span_iff hg').1 (h ▸ Submodule.mem_span_singleton_self _), (mem_span_iff hg).1 (h ▸ Submodule.mem_span_singleton_self _)⟩` and prove the remaining obligations. Introduce and unpack `⟨h1, h2⟩`. Use `le_antisymm ?_ ?_` and prove the remaining obligations.

Conclude with `(Submodule.span_singleton_le_iff_mem _ _).2 ((mem_span_iff hg').2 h1)`. Conclude with `(Submodule.span_singleton_le_iff_mem _ _).2 ((mem_span_iff hg).2 h2)`.
-/
theorem span_eq_iff {R : Subring Ω} {g g' : Ω} (hg : g ≠ 0) (hg' : g' ≠ 0) :
    Submodule.span R {g} = Submodule.span R {g'} ↔ g / g' ∈ R ∧ g' / g ∈ R := by
  constructor
  · intro h
    refine ⟨(mem_span_iff hg').1 (h ▸ Submodule.mem_span_singleton_self _),
      (mem_span_iff hg).1 (h ▸ Submodule.mem_span_singleton_self _)⟩
  · rintro ⟨h1, h2⟩
    refine le_antisymm ?_ ?_
    · exact (Submodule.span_singleton_le_iff_mem _ _).2 ((mem_span_iff hg').2 h1)
    · exact (Submodule.span_singleton_le_iff_mem _ _).2 ((mem_span_iff hg).2 h2)

/- English proof (translation)
Substitute `h` using the available equality. Both sides reduce to the same expression.
-/
theorem span_ring_congr {R R' : Subring Ω} (h : R = R') (S : Set E) (x : E) :
    x ∈ Submodule.span R S ↔ x ∈ Submodule.span R' S := by
  subst h
  rfl

end FlagAlg

section Move

variable {X X' : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Spec (CommRingCat.of Ω) ⟶ X}
  {ξ' : Spec (CommRingCat.of Ω) ⟶ X'}

/- English proof (translation)
Use `⟨mul_ne_zero hμ ht.1, ?_⟩` and prove the remaining obligations. Use extensionality with `a`. Establish `e1 : a ∈ Λ ⟨e.hom q.1, h⟩ ↔ a / μ ∈ Λ' q`. Rewrite using `[hmem, mul_div_cancel₀ _ hμ]`. Rewrite using `[e1, ht.2, mem_span_iff ht.1, mem_span_iff (mul_ne_zero hμ ht.1), regAt_eq e hξ q h, div_div, mul_comm μ t]`.
-/
theorem isGenAt_move (e : X' ≅ X) (hξ : ξ' ≫ e.hom = ξ) {Λ : Lat ξ Ω} {Λ' : Lat ξ' Ω} {μ : Ω} (hμ : μ ≠ 0)
    {q : Cpt ξ'} {h : genPt ξ ⤳ e.hom q.1} (hmem : ∀ x, x ∈ Λ' q ↔ μ * x ∈ Λ ⟨e.hom q.1, h⟩) {t : Ω}
    (ht : Λ'.IsGenAt q t) : Λ.IsGenAt ⟨e.hom q.1, h⟩ (μ * t) := by
  refine ⟨mul_ne_zero hμ ht.1, ?_⟩
  ext a
  have e1 : a ∈ Λ ⟨e.hom q.1, h⟩ ↔ a / μ ∈ Λ' q := by
    rw [hmem, mul_div_cancel₀ _ hμ]
  rw [e1, ht.2, mem_span_iff ht.1, mem_span_iff (mul_ne_zero hμ ht.1), regAt_eq e hξ q h, div_div,
    mul_comm μ t]

/- English proof (translation)
Use `⟨mul_ne_zero (zpow_ne_zero _ hμ) hD.1, fun p _ c hc => ?_⟩` and prove the remaining obligations. Choose the witnesses or unpack the hypotheses as in `⟨q, h, rfl⟩ : ∃ (q : Cpt ξ') (h : genPt ξ ⤳ e.hom q.1), p = ⟨e.hom q.1, h⟩ := by`. Establish `hq : genPt ξ' ⤳ e.inv p.1`. Apply `specializes_iso e` to reduce the goal to its premises. Establish `: e.hom (e.inv p.1) = p.1` using `by simp`.

Rewrite using `[this]`. Substitute `hξ` using the available equality. Conclude with `p.2`. Use `⟨⟨e.inv p.1, hq⟩, ?_, ?_⟩` and prove the remaining obligations. Establish `: e.hom (e.inv p.1) = p.1` using `by simp show genPt ξ ⤳ e.hom (e.inv p.1)`.

Rewrite using `[this]`. Conclude with `p.2`. Conclude with `Subtype.ext (by simp)`. Establish `hc'` using `(inChart_iff e hξ q h _ c).1 hc`. Take `⟨t, ht⟩` from `hgen q`.

Establish `g'` using `Flag.tens_gen (fun _ : Unit => Λ') (fun _ => n) q (fun _ => t) fun _ => ht`. Establish `g` using `Flag.tens_gen (fun _ : Unit => Λ) (fun _ => n) ⟨e.hom q.1, h⟩ (fun _ => μ * t) fun _ => isGenAt_move e hξ hμ (hmem q h) ht`. Establish `d` using `hD.2 q trivial c hc'`. Rewrite `d` using `[g'.2]`. Rewrite using `[g.2]`.

Simplify using `only [Finset.univ_unique, Finset.prod_singleton] at d ⊢`. Establish `hP : (∏ k, y ⟨k, c k⟩ ^ a k) ≠ 0`. Use `Finset.prod_ne_zero_iff.2 fun k _ => zpow_ne_zero _ fun hk => hc.1 ?_` and prove the remaining obligations. Conclude with `Finset.prod_eq_zero (Finset.mem_univ k) hk`. Use `set P := ∏ k, y ⟨k, c k⟩ ^ a k with hPdef`.

Establish `ht0` using `ht.1`. Establish `hc0` using `hD.1`. Establish `hm0 : μ ^ n ≠ 0` using `zpow_ne_zero _ hμ`. Establish `htn : t ^ n ≠ 0` using `zpow_ne_zero _ ht0`. Rewrite `d` using `[smul_eq_mul]`.

Rewrite using `[smul_eq_mul]`. Take `⟨d1, d2⟩` from `(span_eq_iff htn (mul_ne_zero hP hc0)).1 d`. Rewrite `d1`, `d2` using `[regAt_eq e hξ q h]`. Rewrite using `[mul_zpow]`. Use `(span_eq_iff (mul_ne_zero hm0 htn) (mul_ne_zero hP (mul_ne_zero hm0 hc0))).2 ⟨?_, ?_⟩` and prove the remaining obligations.

Use `d1 using 1` and compare the differences between its conclusion and the goal. Clear the denominators using the available nonvanishing facts. Use `d2 using 1` and compare the differences between its conclusion and the goal. Clear the denominators using the available nonvanishing facts.
-/
theorem isDegOn_move (e : X' ≅ X) (hξ : ξ' ≫ e.hom = ξ) {Λ : Lat ξ Ω} {Λ' : Lat ξ' Ω} {μ : Ω} (hμ : μ ≠ 0)
    (hgen : ∀ q, ∃ t, Λ'.IsGenAt q t)
    (hmem : ∀ (q : Cpt ξ') (h : genPt ξ ⤳ e.hom q.1) (x : Ω), x ∈ Λ' q ↔ μ * x ∈ Λ ⟨e.hom q.1, h⟩) (n : ℤ)
    {K : Type} [Fintype K] {ι : K → Type} {y : (Σ k, ι k) → Ω} {a : K → ℤ} {c₀ : Ω}
    (hD : (Lat.tens (fun _ : Unit => Λ') fun _ => n).IsDegOn Set.univ y a c₀) :
    (Lat.tens (fun _ : Unit => Λ) fun _ => n).IsDegOn Set.univ y a (μ ^ n * c₀) := by
  refine ⟨mul_ne_zero (zpow_ne_zero _ hμ) hD.1, fun p _ c hc => ?_⟩
  obtain ⟨q, h, rfl⟩ : ∃ (q : Cpt ξ') (h : genPt ξ ⤳ e.hom q.1), p = ⟨e.hom q.1, h⟩ := by
    have hq : genPt ξ' ⤳ e.inv p.1 := by
      apply specializes_iso e
      have : e.hom (e.inv p.1) = p.1 := by simp
      rw [this]
      subst hξ
      exact p.2
    refine ⟨⟨e.inv p.1, hq⟩, ?_, ?_⟩
    · have : e.hom (e.inv p.1) = p.1 := by simp
      show genPt ξ ⤳ e.hom (e.inv p.1)
      rw [this]
      exact p.2
    · exact Subtype.ext (by simp)
  have hc' := (inChart_iff e hξ q h _ c).1 hc
  obtain ⟨t, ht⟩ := hgen q
  have g' := Flag.tens_gen (fun _ : Unit => Λ') (fun _ => n) q (fun _ => t) fun _ => ht
  have g := Flag.tens_gen (fun _ : Unit => Λ) (fun _ => n) ⟨e.hom q.1, h⟩ (fun _ => μ * t) fun _ =>
    isGenAt_move e hξ hμ (hmem q h) ht
  have d := hD.2 q trivial c hc'
  rw [g'.2] at d
  rw [g.2]
  simp only [Finset.univ_unique, Finset.prod_singleton] at d ⊢
  have hP : (∏ k, y ⟨k, c k⟩ ^ a k) ≠ 0 := by
    refine Finset.prod_ne_zero_iff.2 fun k _ => zpow_ne_zero _ fun hk => hc.1 ?_
    exact Finset.prod_eq_zero (Finset.mem_univ k) hk
  set P := ∏ k, y ⟨k, c k⟩ ^ a k with hPdef
  have ht0 := ht.1
  have hc0 := hD.1
  have hm0 : μ ^ n ≠ 0 := zpow_ne_zero _ hμ
  have htn : t ^ n ≠ 0 := zpow_ne_zero _ ht0
  rw [smul_eq_mul] at d
  rw [smul_eq_mul]
  obtain ⟨d1, d2⟩ := (span_eq_iff htn (mul_ne_zero hP hc0)).1 d
  rw [regAt_eq e hξ q h] at d1 d2
  rw [mul_zpow]
  refine (span_eq_iff (mul_ne_zero hm0 htn) (mul_ne_zero hP (mul_ne_zero hm0 hc0))).2 ⟨?_, ?_⟩
  · convert d1 using 1
    field_simp
  · convert d2 using 1
    field_simp

/- English proof (translation)
Use `⟨hb.1.map' (φ : V →ₗ[Ω] V') (LinearEquiv.ker φ), ?_⟩` and prove the remaining obligations. Use extensionality with `x`. Establish `e1 : x ∈ L' q ↔ φ.symm x ∈ L ⟨e.hom q.1, h⟩`. Rewrite using `[hL]`. Simplify using the standard rewrite rules.

Establish `e2 : ∀ R : Subring Ω, Submodule.span R (Set.range fun k => φ (b k)) = (Submodule.span R (Set.range b)).map ((φ : V →ₗ[Ω] V').restrictScalars R)`. Introduce `R`. Rewrite using `[Submodule.map_span, ← Set.range_comp]`. Both sides reduce to the same expression. Rewrite using `[e1, hb.2, span_ring_congr (regAt_eq e hξ q h), e2, Submodule.mem_map]`.

Prove the components needed by the constructor for the conclusion. Introduce `hx`. Conclude with `⟨_, hx, by simp⟩`. Introduce and unpack `⟨v, hv, rfl⟩`. Simplify using `using hv`.
-/
theorem frame_move (e : X' ≅ X) (hξ : ξ' ≫ e.hom = ξ) {V V' : Type} [AddCommGroup V] [Module Ω V] [AddCommGroup V']
    [Module Ω V'] (φ : V ≃ₗ[Ω] V') {L : Lat ξ V} {L' : Lat ξ' V'} (q : Cpt ξ') (h : genPt ξ ⤳ e.hom q.1)
    (hL : ∀ v : V, v ∈ L ⟨e.hom q.1, h⟩ ↔ φ v ∈ L' q) {r : ℕ} {b : Fin r → V}
    (hb : L.IsFrameAt b ⟨e.hom q.1, h⟩) : L'.IsFrameAt (fun k => φ (b k)) q := by
  refine ⟨hb.1.map' (φ : V →ₗ[Ω] V') (LinearEquiv.ker φ), ?_⟩
  ext x
  have e1 : x ∈ L' q ↔ φ.symm x ∈ L ⟨e.hom q.1, h⟩ := by
    rw [hL]
    simp
  have e2 : ∀ R : Subring Ω, Submodule.span R (Set.range fun k => φ (b k)) =
      (Submodule.span R (Set.range b)).map ((φ : V →ₗ[Ω] V').restrictScalars R) := by
    intro R
    rw [Submodule.map_span, ← Set.range_comp]
    rfl
  rw [e1, hb.2, span_ring_congr (regAt_eq e hξ q h), e2, Submodule.mem_map]
  constructor
  · intro hx
    exact ⟨_, hx, by simp⟩
  · rintro ⟨v, hv, rfl⟩
    simpa using hv

end Move

section Core

open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi

variable {X X' : Scheme.{0}} {Ω : Type} [Field Ω]

/- English proof (translation)
Establish `hF' : ∀ s : ℕ, flagStep Ω b' s = flagStep Ω (fun k => φ (b k)) s` using `fun s => by`. Rewrite using `[← hF s]`. Conclude with `(flagStep_comp (φ : Li →ₗ[Ω] Li') b s).symm`. Take `⟨μ, hμ, hμb⟩` from `exists_scale hF' hb' j`. Establish `hmem : ∀ (q : Cpt ξ') (h : genPt ξ ⤳ e.hom q.1) (x : Ω), x ∈ V'.gr b' j q ↔ μ * x ∈ V.gr b j ⟨e.hom q.1, h⟩`.

Introduce `q h x`. Use `(gr_scale V' j hμ (hF' j) hμb q x).trans ?_` and prove the remaining obligations. Use `(GlobalTheory.T.flag_vector_bundle_transport X X' Ω ξ ξ' e Li Li' φ V V' r b hξ hV).2 j q h` as an intermediate fact. Conclude with `Set.ext_iff.1 this (μ * x)`. Establish `hmove` using `isDegOn_move e hξ hμ (fun q => Flag.gr_gen_of_isFlagVBOn hfl' (Set.mem_univ q) j) hmem n hD'`.

Establish `he0 : e₀ ≠ 0` using `hD.1`. Establish `hκ : μ ^ n ≠ 0` using `zpow_ne_zero _ hμ`. Use `set ρ : Ω := μ ^ n * e₀' / e₀ with hρ`. Establish `hρe : ρ * e₀ = μ ^ n * e₀'` using `by rw [hρ]; field_simp`. Establish `hD₂ : (Lat.tens (fun _ : Unit => V.gr b j) fun _ => n).IsDegOn Set.univ y L'.a (ρ • e₀)`.

Rewrite using `[smul_eq_mul, hρe]`. Conclude with `hmove`. Establish `hne : ∀ k, ∃ i, y ⟨k, i⟩ ≠ 0`. Take `⟨c, hc⟩` from `tie.cover ⟨genPt ξ, specializes_rfl⟩`. Conclude with `fun k => ⟨c k, fun h0 => hc.1 (Finset.prod_eq_zero (Finset.mem_univ k) h0)⟩`.

Take `⟨f, g, hfg, hval⟩` from `GlobalTheory.T.degree_lattice_quotient_forms X Ω ξ K ι y Ω _ L.a L'.a e₀ ρ tie hB hne hD hD₂`. Use `⟨f, g, hfg, ?_⟩` and prove the remaining obligations. Introduce and unpack `w ⟨z, hzw, hzI⟩ u v huv hu`. Take `⟨z', rfl⟩ : ∃ z', z = z' ≫ e.hom` from `⟨z ≫ e.inv, by simp⟩`. Take `⟨h, c, Γ, hcb, hfr, hgram, hpos⟩` from `hG _ hzI`.

Take `⟨t₀, -, ht⟩` from `exists_scale hcb hfr.1 j`. Establish `hN : M.IsGrNorm Lb V b j (z' ≫ e.hom) t₀ _` using `⟨h, c, Γ, hcb, hfr, ht, hgram, hpos, rfl⟩`. Establish `hνpos` using `hN.pos`. Establish `s1` using `hH _ w hzw hzI t₀ _ hN`. Establish `hI' : Int' z'` using `(hI z').1.2 hzI`.

Substitute `hξ` using the available equality. Establish `h' : genPt ξ' ⤳ centre z'` using `specializes_iso e h`. Establish `hfr' : V'.IsFrameAt (fun k => φ (c k)) ⟨centre z', h'⟩` using `frame_move e rfl φ ⟨centre z', h'⟩ h (hV ⟨centre z', h'⟩ h) hfr`. Establish `hcls : φ (c j) - (t₀ / μ) • b' j ∈ flagStep Ω b' j`. Establish `a1 : φ (c j) - t₀ • φ (b j) ∈ flagStep Ω b' j`.

Rewrite using `[← hF]`. Use `⟨c j - t₀ • b j, ht, ?_⟩` and prove the remaining obligations. Simplify using the standard rewrite rules. Establish `a2 : b' j - μ • φ (b j) ∈ flagStep Ω b' j`. Rewrite using `[hF' j]`.

Conclude with `hμb`. Establish `: φ (c j) - (t₀ / μ) • b' j = (φ (c j) - t₀ • φ (b j)) - (t₀ / μ) • (b' j - μ • φ (b j))`. Simplify using `only [smul_sub, smul_smul, div_mul_cancel₀ _ hμ]`. Normalize the expressions using the abelian group laws. Rewrite using `[this]`.

Conclude with `sub_mem a1 (Submodule.smul_mem _ _ a2)`. Establish `hstep : ∀ k : ℕ, flagStep Ω (fun k => φ (c k)) k = flagStep Ω b' k` using `fun k => by`. Use `(flagStep_comp (φ : Li →ₗ[Ω] Li') c k).trans ?_` and prove the remaining obligations. Rewrite using `[hcb k]`. Conclude with `hF k`.

Establish `hN' : M'.IsGrNorm Lb' V' b' j z' (t₀ / μ) _` using `⟨h', fun k => φ (c k), Γ, hstep, hfr', hcls, ((hI z').2 hI' c Γ).1 hgram, hpos, rfl⟩`. Establish `s2` using `hH' z' w ((coordsAt_iso e ξ' z' y w).1 hzw) hI' _ _ hN'`. Establish `s3` using `secNorm_scale (secNorm_iso e s2) hκ`. Establish `et : μ ^ n * (t₀ / μ) ^ n = t₀ ^ n`. Rewrite using `[← mul_zpow, mul_div_cancel₀ _ hμ]`.

Rewrite `s3` using `[et, ← hρe]`. Establish `key` using `GlobalTheory.T.section_norm_isomorphic_lines X Ω _ K ι y L L' e₀ ρ (t₀ ^ n) f g u v _ w _ tie.gen hzw he0 hfg hval s1 s3 (zpow_pos hνpos n) huv hu`. Establish `hpt : ∀ k, ∃ i, w ⟨k, i⟩ ≠ 0` using `fun k => (hzw.1 k).imp fun _ hc => hc.ne_zero`. Establish `hA` using `L.pos w hpt`. Establish `hu' : ‖evC w u‖ ≠ 0` using `norm_ne_zero_iff.2 hu`.

Use `show (0 : ℝ) = Real.log (‖evC w v‖ / ‖evC w u‖ * L'.h w / L.h w)`. Establish `: ‖evC w v‖ / ‖evC w u‖ * L'.h w / L.h w = 1`. Rewrite using `[div_mul_eq_mul_div, key]`. Clear the denominators using the available nonvanishing facts. Rewrite using `[this, Real.log_one]`.
-/
theorem core (e : X' ≅ X) {ξ : Spec (CommRingCat.of Ω) ⟶ X} {ξ' : Spec (CommRingCat.of Ω) ⟶ X'}
    (hξ : ξ' ≫ e.hom = ξ) {G : Over X} [GrpObj G] {G' : Over X'} [GrpObj G'] {Li Li' : Type} [AddCommGroup Li]
    [Module Ω Li] [AddCommGroup Li'] [Module Ω Li'] (M : LieModel G ξ Li) (M' : LieModel G' ξ' Li')
    (Lb : LB G.left) (Lb' : LB G'.left) (φ : Li ≃ₗ[Ω] Li') (V : Lat ξ Li) (V' : Lat ξ' Li') {r : ℕ}
    (b b' : Fin r → _) (j : Fin r) (n : ℤ) (hb' : LinearIndependent Ω b')
    (hfl' : V'.IsFlagVBOn Set.univ b')
    {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] (y : (Σ k, ι k) → Ω) (L L' : HermLine ι)
    (e₀ e₀' : Ω) (Int : (Spec (CommRingCat.of ℂ) ⟶ X) → Prop) (Int' : (Spec (CommRingCat.of ℂ) ⟶ X') → Prop)
    (tie : CoordTie ℤ ξ fun c' : (k : K) → ι k => ∏ k, y ⟨k, c' k⟩) (hB : Birational y)
    (hV : ∀ (q : Cpt ξ') (h : genPt ξ ⤳ e.hom q.1) (v : Li), v ∈ V ⟨e.hom q.1, h⟩ ↔ φ v ∈ V' q)
    (hF : ∀ k : ℕ, (flagStep Ω b k).map (φ : Li →ₗ[Ω] Li') = flagStep Ω b' k)
    (hI : ∀ z : Spec (CommRingCat.of ℂ) ⟶ X', (Int' z ↔ Int (z ≫ e.hom)) ∧ (Int' z →
      ∀ (b : Fin r → Li) (Γ : Matrix (Fin r) (Fin r) ℂ),
        M.GramAt Lb (z ≫ e.hom) b Γ ↔ M'.GramAt Lb' z (fun i => φ (b i)) Γ))
    (hD : (Lat.tens (fun _ : Unit => V.gr b j) fun _ => n).IsDegOn Set.univ y L.a e₀)
    (hD' : (Lat.tens (fun _ : Unit => V'.gr b' j) fun _ => n).IsDegOn Set.univ y L'.a e₀')
    (hH : ∀ (z : Spec (CommRingCat.of ℂ) ⟶ X) (w : (Σ k, ι k) → ℂ), CoordsAt ξ y z w → Int z →
      ∀ t ν, M.IsGrNorm Lb V b j z t ν → SecNorm ξ y L e₀ z w (t ^ n) (ν ^ n))
    (hH' : ∀ (z : Spec (CommRingCat.of ℂ) ⟶ X') (w : (Σ k, ι k) → ℂ), CoordsAt ξ' y z w → Int' z →
      ∀ t ν, M'.IsGrNorm Lb' V' b' j z t ν → SecNorm ξ' y L' e₀' z w (t ^ n) (ν ^ n))
    (hG : ∀ z : Spec (CommRingCat.of ℂ) ⟶ X, Int z → ∃ (h : genPt ξ ⤳ centre z) (c : Fin r → Li)
      (Γ : Matrix (Fin r) (Fin r) ℂ), (∀ k, flagStep Ω c k = flagStep Ω b k) ∧ V.IsFrameAt c ⟨centre z, h⟩ ∧
        M.GramAt Lb z c Γ ∧ Γ.PosDef) :
    IsoLineOn (mCoordIdeal y) {w | ∃ z : Spec (CommRingCat.of ℂ) ⟶ X, CoordsAt ξ y z w ∧ Int z} L L' := by
  have hF' : ∀ s : ℕ, flagStep Ω b' s = flagStep Ω (fun k => φ (b k)) s := fun s => by
    rw [← hF s]
    exact (flagStep_comp (φ : Li →ₗ[Ω] Li') b s).symm
  obtain ⟨μ, hμ, hμb⟩ := exists_scale hF' hb' j
  have hmem : ∀ (q : Cpt ξ') (h : genPt ξ ⤳ e.hom q.1) (x : Ω),
      x ∈ V'.gr b' j q ↔ μ * x ∈ V.gr b j ⟨e.hom q.1, h⟩ := by
    intro q h x
    refine (gr_scale V' j hμ (hF' j) hμb q x).trans ?_
    have := (GlobalTheory.T.flag_vector_bundle_transport X X' Ω ξ ξ' e Li Li' φ V V' r b hξ hV).2 j q h
    exact Set.ext_iff.1 this (μ * x)
  have hmove := isDegOn_move e hξ hμ (fun q => Flag.gr_gen_of_isFlagVBOn hfl' (Set.mem_univ q) j) hmem n hD'
  have he0 : e₀ ≠ 0 := hD.1
  have hκ : μ ^ n ≠ 0 := zpow_ne_zero _ hμ
  set ρ : Ω := μ ^ n * e₀' / e₀ with hρ
  have hρe : ρ * e₀ = μ ^ n * e₀' := by rw [hρ]; field_simp
  have hD₂ : (Lat.tens (fun _ : Unit => V.gr b j) fun _ => n).IsDegOn Set.univ y L'.a (ρ • e₀) := by
    rw [smul_eq_mul, hρe]
    exact hmove
  have hne : ∀ k, ∃ i, y ⟨k, i⟩ ≠ 0 := by
    obtain ⟨c, hc⟩ := tie.cover ⟨genPt ξ, specializes_rfl⟩
    exact fun k => ⟨c k, fun h0 => hc.1 (Finset.prod_eq_zero (Finset.mem_univ k) h0)⟩
  obtain ⟨f, g, hfg, hval⟩ := GlobalTheory.T.degree_lattice_quotient_forms X Ω ξ K ι y Ω _ L.a L'.a e₀ ρ tie hB hne hD hD₂
  refine ⟨f, g, hfg, ?_⟩
  rintro w ⟨z, hzw, hzI⟩ u v huv hu
  obtain ⟨z', rfl⟩ : ∃ z', z = z' ≫ e.hom := ⟨z ≫ e.inv, by simp⟩
  obtain ⟨h, c, Γ, hcb, hfr, hgram, hpos⟩ := hG _ hzI
  obtain ⟨t₀, -, ht⟩ := exists_scale hcb hfr.1 j
  have hN : M.IsGrNorm Lb V b j (z' ≫ e.hom) t₀ _ := ⟨h, c, Γ, hcb, hfr, ht, hgram, hpos, rfl⟩
  have hνpos := hN.pos
  have s1 := hH _ w hzw hzI t₀ _ hN
  have hI' : Int' z' := (hI z').1.2 hzI
  subst hξ
  have h' : genPt ξ' ⤳ centre z' := specializes_iso e h
  have hfr' : V'.IsFrameAt (fun k => φ (c k)) ⟨centre z', h'⟩ :=
    frame_move e rfl φ ⟨centre z', h'⟩ h (hV ⟨centre z', h'⟩ h) hfr
  have hcls : φ (c j) - (t₀ / μ) • b' j ∈ flagStep Ω b' j := by
    have a1 : φ (c j) - t₀ • φ (b j) ∈ flagStep Ω b' j := by
      rw [← hF]
      refine ⟨c j - t₀ • b j, ht, ?_⟩
      simp
    have a2 : b' j - μ • φ (b j) ∈ flagStep Ω b' j := by
      rw [hF' j]
      exact hμb
    have : φ (c j) - (t₀ / μ) • b' j = (φ (c j) - t₀ • φ (b j)) - (t₀ / μ) • (b' j - μ • φ (b j)) := by
      simp only [smul_sub, smul_smul, div_mul_cancel₀ _ hμ]
      abel
    rw [this]
    exact sub_mem a1 (Submodule.smul_mem _ _ a2)
  have hstep : ∀ k : ℕ, flagStep Ω (fun k => φ (c k)) k = flagStep Ω b' k := fun k => by
    refine (flagStep_comp (φ : Li →ₗ[Ω] Li') c k).trans ?_
    rw [hcb k]
    exact hF k
  have hN' : M'.IsGrNorm Lb' V' b' j z' (t₀ / μ) _ :=
    ⟨h', fun k => φ (c k), Γ, hstep, hfr', hcls, ((hI z').2 hI' c Γ).1 hgram, hpos, rfl⟩
  have s2 := hH' z' w ((coordsAt_iso e ξ' z' y w).1 hzw) hI' _ _ hN'
  have s3 := secNorm_scale (secNorm_iso e s2) hκ
  have et : μ ^ n * (t₀ / μ) ^ n = t₀ ^ n := by
    rw [← mul_zpow, mul_div_cancel₀ _ hμ]
  rw [et, ← hρe] at s3
  have key := GlobalTheory.T.section_norm_isomorphic_lines X Ω _ K ι y L L' e₀ ρ (t₀ ^ n) f g u v _ w _ tie.gen hzw he0 hfg hval s1 s3
    (zpow_pos hνpos n) huv hu
  have hpt : ∀ k, ∃ i, w ⟨k, i⟩ ≠ 0 := fun k => (hzw.1 k).imp fun _ hc => hc.ne_zero
  have hA := L.pos w hpt
  have hu' : ‖evC w u‖ ≠ 0 := norm_ne_zero_iff.2 hu
  show (0 : ℝ) = Real.log (‖evC w v‖ / ‖evC w u‖ * L'.h w / L.h w)
  have : ‖evC w v‖ / ‖evC w u‖ * L'.h w / L.h w = 1 := by
    rw [div_mul_eq_mul_div, key]
    field_simp
  rw [this, Real.log_one]

end Core

section Main

open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi HodgeCpt

/- English proof (translation)
Introduce `E _ _ _ H D l Xo c O O' _ _ β β' Y Y' S Ω _ K _ ι _ y A A' e φ Fl Fl' τ τ' i e₀ e₀' L L' hB hξ hV hF hI hD hD' hH hH' hG`. Establish `hind : ∀ s, LinearIndependent Ω (Fl'.b s)`. Take `⟨_, _, _, _, _, h4, _⟩` from `Fl'.generic`. Conclude with `h4`. Unfold `Flag.rootLat at hD hD'`.

Unfold `Flag.IsHodgeLine at hH hH'`. Distinguish the cases in `hp : (i : ℕ) < D.p`. Establish `e1 : rootIdx D (τ, i) = ⟨.inl τ, ⟨i, hp⟩⟩` using `by simp [rootIdx, hp]`. Establish `e2 : rootIdx D (τ', i) = ⟨.inl τ', ⟨i, hp⟩⟩` using `by simp [rootIdx, hp]`. Establish `g1 : rootSgn D (τ, i) = 1` using `by simp [rootSgn, hp]`.

Establish `g2 : rootSgn D (τ', i) = 1` using `by simp [rootSgn, hp]`. Rewrite `hD`, `hH` using `[g1]`. Rewrite `hD'`, `hH'` using `[g2]`. Generalize the expression as in `rootIdx D (τ, i) = q at hD hH e1`. Generalize the expression as in `rootIdx D (τ', i) = q' at hD' hH' e2`.

Substitute `e1 e2` using the available equality. Conclude with `core e hξ A.M A'.M A.t.PP.L A'.t.PP.L φ (A.V (.inl τ)) (A'.V (.inl τ')) (Fl.b (.inl τ)) (Fl'.b (.inl τ')) ⟨i, hp⟩ 1 (hind _) (Fl'.sub _) y L L' e₀ e₀' (fun z => A.Interior z) (fun z => A'.Interior z) A.tie hB (fun q h v => (hV q h v).1) (fun k => (hF k).1) (fun z => ⟨(hI z).1, fu …`. Establish `hj : D.p + D.q - 1 - (i : ℕ) < D.q` using `by have := i.2; omega`. Establish `e1 : rootIdx D (τ, i) = ⟨.inr τ, ⟨D.p + D.q - 1 - i, hj⟩⟩` using `by simp [rootIdx, hp]`. Establish `e2 : rootIdx D (τ', i) = ⟨.inr τ', ⟨D.p + D.q - 1 - i, hj⟩⟩` using `by simp [rootIdx, hp]`.

Establish `g1 : rootSgn D (τ, i) = -1` using `by simp [rootSgn, hp]`. Establish `g2 : rootSgn D (τ', i) = -1` using `by simp [rootSgn, hp]`. Rewrite `hD`, `hH` using `[g1]`. Rewrite `hD'`, `hH'` using `[g2]`. Generalize the expression as in `rootIdx D (τ, i) = q at hD hH e1`.

Generalize the expression as in `rootIdx D (τ', i) = q' at hD' hH' e2`. Substitute `e1 e2` using the available equality. Conclude with `core e hξ A.M A'.M A.t.PP.L A'.t.PP.L φ (A.V (.inr τ)) (A'.V (.inr τ')) (Fl.b (.inr τ)) (Fl'.b (.inr τ')) ⟨D.p + D.q - 1 - i, hj⟩ (-1) (hind _) (Fl'.sub _) y L L' e₀ e₀' (fun z => A.Interior z) (fun z => A'.Interior z) A.tie hB (fun q h v => (hV q h v).2) (fun k => (hF k).2) (fun …`.
-/
theorem rootLine_iso : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O O' : Type) [CommRing O] [CommRing O'] (β : O →+* c.F) (β' : O' →+* c.F) (Y : Model Xo c β) (Y' : Model Xo c β') (S : Finset ℕ) (Ω : Type) [Field Ω] (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (y : (Σ k, ι k) → Ω) (A : HodgeCpt Y S y) (A' : HodgeCpt Y' S y) (e : A'.X ≅ A.X) (φ : A.Li ≃ₗ[Ω] A'.Li) (Fl : A.Flag) (Fl' : A'.Flag) (τ τ' : CMType H) (i : Fin (D.p + D.q)) (e₀ e₀' : Ω) (L L' : HermLine ι), Birational y → A'.ξ ≫ e.hom = A.ξ → (∀ (q : Cpt A'.ξ) (h : genPt A.ξ ⤳ e.hom q.1) (v : A.Li), (v ∈ A.V (.inl τ) ⟨e.hom q.1, h⟩ ↔ φ v ∈ A'.V (.inl τ') q) ∧ (v ∈ A.V (.inr τ) ⟨e.hom q.1, h⟩ ↔ φ v ∈ A'.V (.inr τ') q)) → (∀ k, (flagStep Ω (Fl.b (.inl τ)) k).map (φ : A.Li →ₗ[Ω] A'.Li) = flagStep Ω (Fl'.b (.inl τ')) k ∧ (flagStep Ω (Fl.b (.inr τ)) k).map (φ : A.Li →ₗ[Ω] A'.Li) = flagStep Ω (Fl'.b (.inr τ')) k) → (∀ z : Sp ℂ ⟶ A'.X, (A'.Interior z ↔ A.Interior (z ≫ e.hom)) ∧ (A'.Interior z → ∀ (r : ℕ) (b : Fin r → A.Li) (Γ : Matrix (Fin r) (Fin r) ℂ), A.M.GramAt A.t.PP.L (z ≫ e.hom) b Γ ↔ A'.M.GramAt A'.t.PP.L z (fun i => φ (b i)) Γ)) → (Fl.rootLat (τ, i)).IsDegOn Set.univ y L.a e₀ → (Fl'.rootLat (τ', i)).IsDegOn Set.univ y L'.a e₀' → Fl.IsHodgeLine (τ, i) e₀ L → Fl'.IsHodgeLine (τ', i) e₀' L' → (∀ (z : Sp ℂ ⟶ A.X), A.Interior z → ∀ s, ∃ (h : genPt A.ξ ⤳ centre z) (b : Fin (labelRk D s) → A.Li) (Γ : Matrix (Fin (labelRk D s)) (Fin (labelRk D s)) ℂ), (∀ k, flagStep Ω b k = flagStep Ω (Fl.b s) k) ∧ (A.V s).IsFrameAt b ⟨centre z, h⟩ ∧ A.M.GramAt A.t.PP.L z b Γ ∧ Γ.PosDef) → IsoLineOn (mCoordIdeal y) {w | ∃ z : Sp ℂ ⟶ A.X, CoordsAt A.ξ y z w ∧ A.Interior z} L L' := by
  intro E _ _ _ H D l Xo c O O' _ _ β β' Y Y' S Ω _ K _ ι _ y A A' e φ Fl Fl' τ τ' i e₀ e₀' L L' hB hξ hV hF hI hD hD'
    hH hH' hG
  have hind : ∀ s, LinearIndependent Ω (Fl'.b s) := by
    obtain ⟨_, _, _, _, _, h4, _⟩ := Fl'.generic
    exact h4
  unfold Flag.rootLat at hD hD'
  unfold Flag.IsHodgeLine at hH hH'
  by_cases hp : (i : ℕ) < D.p
  · have e1 : rootIdx D (τ, i) = ⟨.inl τ, ⟨i, hp⟩⟩ := by simp [rootIdx, hp]
    have e2 : rootIdx D (τ', i) = ⟨.inl τ', ⟨i, hp⟩⟩ := by simp [rootIdx, hp]
    have g1 : rootSgn D (τ, i) = 1 := by simp [rootSgn, hp]
    have g2 : rootSgn D (τ', i) = 1 := by simp [rootSgn, hp]
    rw [g1] at hD hH
    rw [g2] at hD' hH'
    generalize rootIdx D (τ, i) = q at hD hH e1
    generalize rootIdx D (τ', i) = q' at hD' hH' e2
    subst e1 e2
    exact core e hξ A.M A'.M A.t.PP.L A'.t.PP.L φ (A.V (.inl τ)) (A'.V (.inl τ')) (Fl.b (.inl τ)) (Fl'.b (.inl τ'))
      ⟨i, hp⟩ 1 (hind _) (Fl'.sub _) y L L' e₀ e₀' (fun z => A.Interior z) (fun z => A'.Interior z) A.tie hB
      (fun q h v => (hV q h v).1) (fun k => (hF k).1) (fun z => ⟨(hI z).1, fun h => (hI z).2 h _⟩) hD hD' hH hH'
      (fun z hz => hG z hz (.inl τ))
  · have hj : D.p + D.q - 1 - (i : ℕ) < D.q := by have := i.2; omega
    have e1 : rootIdx D (τ, i) = ⟨.inr τ, ⟨D.p + D.q - 1 - i, hj⟩⟩ := by simp [rootIdx, hp]
    have e2 : rootIdx D (τ', i) = ⟨.inr τ', ⟨D.p + D.q - 1 - i, hj⟩⟩ := by simp [rootIdx, hp]
    have g1 : rootSgn D (τ, i) = -1 := by simp [rootSgn, hp]
    have g2 : rootSgn D (τ', i) = -1 := by simp [rootSgn, hp]
    rw [g1] at hD hH
    rw [g2] at hD' hH'
    generalize rootIdx D (τ, i) = q at hD hH e1
    generalize rootIdx D (τ', i) = q' at hD' hH' e2
    subst e1 e2
    exact core e hξ A.M A'.M A.t.PP.L A'.t.PP.L φ (A.V (.inr τ)) (A'.V (.inr τ')) (Fl.b (.inr τ)) (Fl'.b (.inr τ'))
      ⟨D.p + D.q - 1 - i, hj⟩ (-1) (hind _) (Fl'.sub _) y L L' e₀ e₀' (fun z => A.Interior z)
      (fun z => A'.Interior z) A.tie hB (fun q h v => (hV q h v).2) (fun k => (hF k).2)
      (fun z => ⟨(hI z).1, fun h => (hI z).2 h _⟩) hD hD' hH hH' (fun z hz => hG z hz (.inr τ))

end Main

end GlobalTheory.CompanionTheory.Ar.Cmp.RootIso

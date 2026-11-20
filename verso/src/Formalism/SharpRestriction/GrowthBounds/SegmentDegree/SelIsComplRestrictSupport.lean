import Formalism.SharpRestriction.GrowthBounds.SegmentDegree.NonemptyDvrSettingOfStandard
import Lemmata.ComplementLifts.ComplLift

noncomputable section

open MvPolynomial

namespace Formalism.MainNotions.SelectionLemmas.Pf

open Formalism.MainNotions.G

/- English proof (translation)
Conclude with `Bl.ComplementLifts.goal1 N N' S hNN' hS hsat`.
-/
theorem sel_compl {R M : Type*} [CommRing R] [IsDomain R] [IsPrincipalIdealRing R] [AddCommGroup M] [Module R M]
    (N N' S : Submodule R M) (hNN' : IsCompl N N') [Module.Finite R N] (hS : S ≤ N)
    (hsat : ∀ (a : R) (x : M), a ≠ 0 → a • x ∈ S → x ∈ S) : ∃ T : Submodule R M, IsCompl S T := by
  exact Bl.ComplementLifts.goal1 N N' S hNN' hS hsat

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Rewrite using `[Submodule.disjoint_def]`. Introduce `x hx hx'`. Rewrite `hx`, `hx'` using `[mem_restrictSupport_iff]`. Rewrite using `[← support_eq_empty]`.

Use extensionality with `m`. Simplify using `only [Finset.notMem_empty, iff_false]`. Introduce `hm`. Conclude with `hx' (Finset.mem_coe.mpr hm) (hx (Finset.mem_coe.mpr hm))`. Rewrite using `[codisjoint_iff, restrictSupport_eq_span, restrictSupport_eq_span, ← Submodule.span_union, ← Set.image_union, Set.union_compl_self, ← restrictSupport_eq_span, restrictSupport_univ]`.
-/
theorem sel_isCompl_restrictSupport (R : Type*) [CommRing R] {σ : Type*} (s : Set (σ →₀ ℕ)) :
    IsCompl (restrictSupport R s) (restrictSupport R sᶜ) := by
  constructor
  · rw [Submodule.disjoint_def]
    intro x hx hx'
    rw [mem_restrictSupport_iff] at hx hx'
    rw [← support_eq_empty]
    ext m
    simp only [Finset.notMem_empty, iff_false]
    intro hm
    exact hx' (Finset.mem_coe.mpr hm) (hx (Finset.mem_coe.mpr hm))
  · rw [codisjoint_iff, restrictSupport_eq_span, restrictSupport_eq_span, ← Submodule.span_union, ← Set.image_union,
      Set.union_compl_self, ← restrictSupport_eq_span, restrictSupport_univ]

section DVR

variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {σ : Type}

/- English proof (translation)
Rewrite using `[map_sum]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[smul_eq_C_mul, map_mul, map_C, ← smul_eq_C_mul]`.
-/
theorem sel_red_sum {ι : Type} [Fintype ι] (c : ι → O) (v : ι → MvPolynomial σ O) :
    MvPolynomial.map (IsLocalRing.residue O) (∑ i, c i • v i) =
      ∑ i, IsLocalRing.residue O (c i) • MvPolynomial.map (IsLocalRing.residue O) (v i) := by
  rw [map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [smul_eq_C_mul, map_mul, map_C, ← smul_eq_C_mul]

/- English proof (translation)
Establish `hres : IsLocalRing.residue O ϖ = 0`. Rewrite using `[IsLocalRing.residue_eq_zero_iff, IsLocalRing.mem_maximalIdeal]`. Conclude with `hϖ.not_isUnit`. Establish `h1 : ∑ i, IsLocalRing.residue O (c i) • MvPolynomial.map (IsLocalRing.residue O) (v i) = 0`. Rewrite using `[← sel_red_sum, h, smul_eq_C_mul, map_mul, map_C, hres, C_0, zero_mul]`.

Establish `h2` using `Fintype.linearIndependent_iff.mp hv _ h1`. Establish `h3 : ∀ i, ϖ ∣ c i` using `fun i => by`. Use `(IsLocalRing.residue_eq_zero_iff _).mp (h2 i)` as an intermediate fact. Rewrite `this` using `[hϖ.maximalIdeal_eq, Ideal.mem_span_singleton]`. Then use the resulting hypothesis. Use `choose c' hc' using h3`.

Use `⟨c', hc', ?_⟩` and prove the remaining obligations. Establish `h4 : ϖ • ∑ i, c' i • v i = ϖ • x`. Rewrite using `[← h, Finset.smul_sum]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[hc' i, mul_smul]`.

Conclude with `smul_right_injective _ hϖ.ne_zero h4`.
-/
theorem sel_key {ι : Type} [Fintype ι] (v : ι → MvPolynomial σ O)
    (hv : LinearIndependent (FF O) fun i => MvPolynomial.map (IsLocalRing.residue O) (v i))
    {ϖ : O} (hϖ : Irreducible ϖ) (c : ι → O) (x : MvPolynomial σ O) (h : ∑ i, c i • v i = ϖ • x) :
    ∃ c' : ι → O, (∀ i, c i = ϖ * c' i) ∧ ∑ i, c' i • v i = x := by
  have hres : IsLocalRing.residue O ϖ = 0 := by
    rw [IsLocalRing.residue_eq_zero_iff, IsLocalRing.mem_maximalIdeal]
    exact hϖ.not_isUnit
  have h1 : ∑ i, IsLocalRing.residue O (c i) • MvPolynomial.map (IsLocalRing.residue O) (v i) = 0 := by
    rw [← sel_red_sum, h, smul_eq_C_mul, map_mul, map_C, hres, C_0, zero_mul]
  have h2 := Fintype.linearIndependent_iff.mp hv _ h1
  have h3 : ∀ i, ϖ ∣ c i := fun i => by
    have := (IsLocalRing.residue_eq_zero_iff _).mp (h2 i)
    rwa [hϖ.maximalIdeal_eq, Ideal.mem_span_singleton] at this
  choose c' hc' using h3
  refine ⟨c', hc', ?_⟩
  have h4 : ϖ • ∑ i, c' i • v i = ϖ • x := by
    rw [← h, Finset.smul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hc' i, mul_smul]
  exact smul_right_injective _ hϖ.ne_zero h4

/- English proof (translation)
Take `⟨ϖ, hϖ⟩` from `IsDiscreteValuationRing.exists_irreducible O`. Establish `hP : ∀ n : ℕ, ∀ c : ι → O, ∑ i, c i • v i = 0 → ∀ i, ϖ ^ n ∣ c i`. Introduce `n`. Proceed by induction on `n with`. Consider the case `zero => intro c _ i`.

Simplify using the standard rewrite rules. Consider the case `succ n ih`. Introduce `c hc i`. Take `⟨c', hc', hs⟩` from `sel_key v hv hϖ c 0 (by rw [hc, smul_zero])`. Take `⟨e, he⟩` from `ih c' hs i`.

Conclude with `⟨e, by rw [hc' i, he, pow_succ]; ring⟩`. Rewrite using `[Fintype.linearIndependent_iff]`. Introduce `c hc i`. Assume the negation of the conclusion as `hne`. Take `⟨n, u, hu⟩` from `IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hne hϖ`.

Take `⟨e, he⟩` from `hP (n + 1) c hc i`. Establish `h1 : ϖ ^ n * (u : O) = ϖ ^ n * (ϖ * e)`. Rewrite using `[← mul_assoc, ← pow_succ, ← he, hu]`. Expand and normalize the polynomial expressions, which then agree. Establish `h2 : (u : O) = ϖ * e` using `mul_left_cancel₀ (pow_ne_zero n hϖ.ne_zero) h1`.

Conclude with `hϖ.not_isUnit (isUnit_of_mul_isUnit_left (h2 ▸ u.isUnit))`.
-/
theorem sel_li {ι : Type} [Fintype ι] (v : ι → MvPolynomial σ O)
    (hv : LinearIndependent (FF O) fun i => MvPolynomial.map (IsLocalRing.residue O) (v i)) :
    LinearIndependent O v := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible O
  have hP : ∀ n : ℕ, ∀ c : ι → O, ∑ i, c i • v i = 0 → ∀ i, ϖ ^ n ∣ c i := by
    intro n
    induction n with
    | zero => intro c _ i; simp
    | succ n ih =>
      intro c hc i
      obtain ⟨c', hc', hs⟩ := sel_key v hv hϖ c 0 (by rw [hc, smul_zero])
      obtain ⟨e, he⟩ := ih c' hs i
      exact ⟨e, by rw [hc' i, he, pow_succ]; ring⟩
  rw [Fintype.linearIndependent_iff]
  intro c hc i
  by_contra hne
  obtain ⟨n, u, hu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hne hϖ
  obtain ⟨e, he⟩ := hP (n + 1) c hc i
  have h1 : ϖ ^ n * (u : O) = ϖ ^ n * (ϖ * e) := by
    rw [← mul_assoc, ← pow_succ, ← he, hu]; ring
  have h2 : (u : O) = ϖ * e := mul_left_cancel₀ (pow_ne_zero n hϖ.ne_zero) h1
  exact hϖ.not_isUnit (isUnit_of_mul_isUnit_left (h2 ▸ u.isUnit))

/- English proof (translation)
Take `⟨ϖ, hϖ⟩` from `IsDiscreteValuationRing.exists_irreducible O`. Take `⟨n, u, rfl⟩` from `IsDiscreteValuationRing.eq_unit_mul_pow_irreducible ha hϖ`. Establish `h1 : ϖ ^ n • x ∈ Submodule.span O (Set.range v)`. Use `Submodule.smul_mem _ ((u⁻¹ : Oˣ) : O) h` as an intermediate fact. Rewrite `this` using `[smul_smul, ← mul_assoc, Units.inv_mul, one_mul]`. Then use the resulting hypothesis.

Use `clear h ha`. Proceed by induction on `n with`. Consider the case `zero => simpa using h1`. Consider the case `succ n ih`. Apply `ih` to reduce the goal to its premises.

Take `⟨c, hc⟩` from `(Submodule.mem_span_range_iff_exists_fun O).mp h1`. Take `⟨c', -, hs⟩` from `sel_key v hv hϖ c (ϖ ^ n • x) (by rw [hc, smul_smul, ← pow_succ'])`. Conclude with `(Submodule.mem_span_range_iff_exists_fun O).mpr ⟨c', hs⟩`.
-/
theorem sel_sat {ι : Type} [Fintype ι] (v : ι → MvPolynomial σ O)
    (hv : LinearIndependent (FF O) fun i => MvPolynomial.map (IsLocalRing.residue O) (v i))
    (a : O) (x : MvPolynomial σ O) (ha : a ≠ 0) (h : a • x ∈ Submodule.span O (Set.range v)) :
    x ∈ Submodule.span O (Set.range v) := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible O
  obtain ⟨n, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible ha hϖ
  have h1 : ϖ ^ n • x ∈ Submodule.span O (Set.range v) := by
    have := Submodule.smul_mem _ ((u⁻¹ : Oˣ) : O) h
    rwa [smul_smul, ← mul_assoc, Units.inv_mul, one_mul] at this
  clear h ha
  induction n with
  | zero => simpa using h1
  | succ n ih =>
    apply ih
    obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun O).mp h1
    obtain ⟨c', -, hs⟩ := sel_key v hv hϖ c (ϖ ^ n • x) (by rw [hc, smul_smul, ← pow_succ'])
    exact (Submodule.mem_span_range_iff_exists_fun O).mpr ⟨c', hs⟩

end DVR

/- English proof (translation)
Introduce `O _ _ _ σ s hs G hG`. Take `⟨b, hbG, hspan, hli⟩` from `exists_linearIndependent (FF O) (MvPolynomial.map (IsLocalRing.residue O) '' G)`. Establish `hsub : ∀ y ∈ MvPolynomial.map (IsLocalRing.residue O) '' G, y ∈ restrictSupport (FF O) s`. Introduce and unpack `y ⟨g, hg, rfl⟩`. Establish `hg'` using `hG g hg`.

Rewrite `hg'`, the goal using `[mem_restrictSupport_iff]`. Conclude with `fun m hm => hg' (Finset.mem_coe.mpr (support_map_subset _ _ hm))`. Establish `: Finite ((fun m : σ →₀ ℕ => (monomial m (1 : FF O))) '' s)` using `(hs.image _).to_subtype`. Establish `hfin : Finite b`. Use `hli.finite_of_le_span_finite _ ((fun m : σ →₀ ℕ => (monomial m (1 : FF O))) '' s) ?_` and prove the remaining obligations.

Introduce and unpack `y ⟨⟨y', hy'⟩, rfl⟩`. Use `hsub y' (hbG hy')` as an intermediate fact. Rewrite `this` using `[restrictSupport_eq_span]`. Then use the resulting hypothesis. Set `: Fintype b` to `Fintype.ofFinite b`. Establish `hpre : ∀ y : b, ∃ g ∈ G, MvPolynomial.map (IsLocalRing.residue O) g = (y : MvPolynomial σ (FF O))` using `fun y => hbG y.2`.

Use `choose v hvG hv using hpre`. Establish `hli' : LinearIndependent (FF O) fun i => MvPolynomial.map (IsLocalRing.residue O) (v i)`. Establish `: (fun i => MvPolynomial.map (IsLocalRing.residue O) (v i)) = ((↑) : b → MvPolynomial σ (FF O))`. Use function extensionality and compare the values at `hv`. Rewrite using `[this]`.

Conclude with `hli`. Establish `hliO : LinearIndependent O v` using `sel_li v hli'`. Establish `: Finite s` using `hs.to_subtype`. Establish `: Module.Finite O (restrictSupport O s)` using `Module.Finite.of_basis (basisRestrictSupport O s)`. Establish `hle : Submodule.span O (Set.range v) ≤ Submodule.span O G` using `Submodule.span_mono (by rintro _ ⟨i, rfl⟩; exact hvG i)`.

Establish `hleN : Submodule.span O (Set.range v) ≤ restrictSupport O s` using `Submodule.span_le.mpr (by rintro _ ⟨i, rfl⟩; exact hG _ (hvG i))`. Use `⟨Submodule.span O (Set.range v), hle, ?_, ⟨b, Module.Basis.span hliO, fun i => ?_⟩, ?_⟩` and prove the remaining obligations. Conclude with `sel_compl _ _ _ (sel_isCompl_restrictSupport O s) hleN (fun a x ha h => sel_sat v hli' a x ha h)`. Rewrite using `[Module.Basis.span_apply]`. Conclude with `hvG i`.

Rewrite using `[finrank_span_eq_card hliO, ← hspan]`. Establish `: Submodule.span (FF O) b = Submodule.span (FF O) (Set.range ((↑) : b → MvPolynomial σ (FF O)))`. Rewrite using `[Subtype.range_coe]`. Rewrite using `[this, finrank_span_eq_card hli]`.
-/
theorem restSel : RestSel := by
  intro O _ _ _ σ s hs G hG
  classical
  obtain ⟨b, hbG, hspan, hli⟩ := exists_linearIndependent (FF O) (MvPolynomial.map (IsLocalRing.residue O) '' G)

  have hsub : ∀ y ∈ MvPolynomial.map (IsLocalRing.residue O) '' G, y ∈ restrictSupport (FF O) s := by
    rintro y ⟨g, hg, rfl⟩
    have hg' := hG g hg
    rw [mem_restrictSupport_iff] at hg' ⊢
    exact fun m hm => hg' (Finset.mem_coe.mpr (support_map_subset _ _ hm))
  have : Finite ((fun m : σ →₀ ℕ => (monomial m (1 : FF O))) '' s) := (hs.image _).to_subtype
  have hfin : Finite b := by
    refine hli.finite_of_le_span_finite _ ((fun m : σ →₀ ℕ => (monomial m (1 : FF O))) '' s) ?_
    rintro y ⟨⟨y', hy'⟩, rfl⟩
    have := hsub y' (hbG hy')
    rwa [restrictSupport_eq_span] at this
  let : Fintype b := Fintype.ofFinite b

  have hpre : ∀ y : b, ∃ g ∈ G, MvPolynomial.map (IsLocalRing.residue O) g = (y : MvPolynomial σ (FF O)) :=
    fun y => hbG y.2
  choose v hvG hv using hpre
  have hli' : LinearIndependent (FF O) fun i => MvPolynomial.map (IsLocalRing.residue O) (v i) := by
    have : (fun i => MvPolynomial.map (IsLocalRing.residue O) (v i)) = ((↑) : b → MvPolynomial σ (FF O)) :=
      funext hv
    rw [this]; exact hli
  have hliO : LinearIndependent O v := sel_li v hli'
  have : Finite s := hs.to_subtype
  have : Module.Finite O (restrictSupport O s) := Module.Finite.of_basis (basisRestrictSupport O s)
  have hle : Submodule.span O (Set.range v) ≤ Submodule.span O G :=
    Submodule.span_mono (by rintro _ ⟨i, rfl⟩; exact hvG i)
  have hleN : Submodule.span O (Set.range v) ≤ restrictSupport O s :=
    Submodule.span_le.mpr (by rintro _ ⟨i, rfl⟩; exact hG _ (hvG i))
  refine ⟨Submodule.span O (Set.range v), hle, ?_, ⟨b, Module.Basis.span hliO, fun i => ?_⟩, ?_⟩
  · exact sel_compl _ _ _ (sel_isCompl_restrictSupport O s) hleN (fun a x ha h => sel_sat v hli' a x ha h)
  · rw [Module.Basis.span_apply]; exact hvG i
  · rw [finrank_span_eq_card hliO, ← hspan]
    have : Submodule.span (FF O) b = Submodule.span (FF O) (Set.range ((↑) : b → MvPolynomial σ (FF O))) := by
      rw [Subtype.range_coe]
    rw [this, finrank_span_eq_card hli]

end Formalism.MainNotions.SelectionLemmas.Pf

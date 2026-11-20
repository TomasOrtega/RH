import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.OpenField
import GroundTheory.LocalFields.MainTheorem
import GroundTheory.LocalFields.PrincipalUnitsRank
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FixingSubgroupEquivBicontinuous

open Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc ReciprocityTheory.Gal Module UpperTheory.V.Loc Topology

/- English proof (translation)
Establish `hle : (commutator G).topologicalClosure ≤ q.ker` using `Subgroup.topologicalClosure_minimal _ (Abelianization.commutator_subset_ker q) (isClosed_singleton.preimage hq)`. Use `⟨QuotientGroup.lift _ q hle, ?_, fun g => rfl⟩` and prove the remaining obligations. Conclude with `continuous_coinduced_dom.2 hq`.
-/
private theorem ag_lift {G C : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CommGroup C]
    [TopologicalSpace C] [T2Space C] (q : G →* C) (hq : Continuous q) :
    ∃ F : TopologicalAbelianization G →* C, Continuous F ∧ ∀ g : G, F g = q g := by
  have hle : (commutator G).topologicalClosure ≤ q.ker :=
    Subgroup.topologicalClosure_minimal _ (Abelianization.commutator_subset_ker q)
      (isClosed_singleton.preimage hq)
  refine ⟨QuotientGroup.lift _ q hle, ?_, fun g => rfl⟩
  exact continuous_coinduced_dom.2 hq

/- English proof (translation)
Use `set M := (commutator G').topologicalClosure`. Establish `hker : ((QuotientGroup.mk' M).comp f).ker = M.comap f`. Use extensionality with `x`. Simplify using the standard rewrite rules. Establish `hle : (commutator G).topologicalClosure ≤ M.comap f`.

Apply `Subgroup.topologicalClosure_minimal` to reduce the goal to its premises. Rewrite using `[← hker]`. Conclude with `Abelianization.commutator_subset_ker _`. Conclude with `(Subgroup.isClosed_topologicalClosure _).preimage hf`. Use `⟨QuotientGroup.map _ M f hle, ?_, fun g => rfl⟩` and prove the remaining obligations.

Conclude with `continuous_coinduced_dom.2 (continuous_quotient_mk'.comp hf)`.
-/
private theorem ag_map {G G' : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [Group G']
    [TopologicalSpace G'] [IsTopologicalGroup G'] (f : G →* G') (hf : Continuous f) :
    ∃ F : TopologicalAbelianization G →* TopologicalAbelianization G', Continuous F ∧ ∀ g : G, F g = (f g : G') := by
  set M := (commutator G').topologicalClosure
  have hker : ((QuotientGroup.mk' M).comp f).ker = M.comap f := by
    ext x
    simp
  have hle : (commutator G).topologicalClosure ≤ M.comap f := by
    apply Subgroup.topologicalClosure_minimal
    · rw [← hker]
      exact Abelianization.commutator_subset_ker _
    · exact (Subgroup.isClosed_topologicalClosure _).preimage hf
  refine ⟨QuotientGroup.map _ M f hle, ?_, fun g => rfl⟩
  exact continuous_coinduced_dom.2 (continuous_quotient_mk'.comp hf)

open GroundTheory.LocalField ValuativeRel GroundTheory.LocalField.Abstract in
/- English proof (translation)
Take `⟨F, hF, hFe⟩` from `ag_map (ε : G →* (Ω ≃ₐ[K] Ω)) hε`. Take `⟨F', hF', hF'e⟩` from `ag_map (ε.symm : (Ω ≃ₐ[K] Ω) →* G) hε'`. Establish `hFF' : ∀ b, F (F' b) = b`. Introduce `b`. Take `⟨g, rfl⟩` from `QuotientGroup.mk_surjective b`.

Rewrite using `[hF'e, hFe]`. Simplify using the standard rewrite rules. Establish `hF'F : ∀ a, F' (F a) = a`. Introduce `a`. Take `⟨g, rfl⟩` from `QuotientGroup.mk_surjective a`.

Rewrite using `[hFe, hF'e]`. Simplify using the standard rewrite rules. Take `⟨U, hU, hUe⟩` from `ag_lift (unramifiedDegree K Ω) continuous_unramifiedDegree`. Use `set L := localReciprocityLimit K Ω`. Establish `hLart : ∀ x, localArtinMap K Ω x = topologicalAbelianizationEquiv K Ω (L x)` using `fun x => localArtinMap_apply x`.

Establish `hLc : Continuous L`. Establish `h : (L : Kˣ → _) = (topologicalAbelianizationEquiv K Ω).symm ∘ localArtinMap K Ω`. Use function extensionality and compare the values at `x`. Simplify using `[hLart]`. Rewrite using `[h]`.

Conclude with `(topologicalAbelianizationEquiv K Ω).symm.continuous.comp continuous_localArtinMap`. Establish `hLi : Function.Injective L`. Introduce `x y hxy`. Apply `injective_localArtinMap (K := K) (Ω := Ω)` to reduce the goal to its premises. Rewrite using `[hLart, hLart, hxy]`.

Establish `hU' : ∀ x : Kˣ, U (L x) = Multiplicative.ofAdd ((ord (x : K) : ℤ) : ProfiniteInteger)`. Introduce `x`. Take `⟨g, hg⟩` from `QuotientGroup.mk_surjective (L x)`. Rewrite using `[← hg, hUe]`. Conclude with `unramifiedDegree_of_mk_eq_localReciprocityLimit hg`.

Use `⟨F'.comp L, U.comp F, hF'.comp hLc, ?_, ?_, ?_, hU.comp hF, ?_, ?_⟩` and prove the remaining obligations. Introduce `x y hxy`. Apply `hLi` to reduce the goal to its premises. Use `congrArg F hxy` as an intermediate fact. Simplify `this` using `[hFF']`.

Conclude with `(Function.Surjective.denseRange (fun a => ⟨F a, hF'F a⟩)).comp (denseRange_localReciprocityLimit (K := K) (Ω := Ω)) hF'`. Introduce `H hHo hHf`. Set `H' : openFiniteIndex Kˣ` to `⟨H, hHo, hHf⟩`. Set `ψ` to `((artinCoord K Ω H').comp (topologicalAbelianizationEquiv K Ω).toMulEquiv.toMonoidHom).comp F`. Establish `hψ : Continuous ψ` using `(continuous_artinCoord H').comp ((topologicalAbelianizationEquiv K Ω).continuous.comp hF)`.

Use `haveI := openCompletion.discreteTopology_quotient H'`. Use `⟨ψ.ker, ?_, ?_⟩` and prove the remaining obligations. Conclude with `(isOpen_discrete ({1} : Set (Kˣ ⧸ (H : Subgroup Kˣ)))).preimage hψ`. Use extensionality with `y`. Simplify using `only [Subgroup.mem_comap, MonoidHom.mem_ker, ψ, MonoidHom.comp_apply, hFF']`.

Express the relevant statement in the definitionally equal form `artinCoord K Ω H' (topologicalAbelianizationEquiv K Ω (L y)) = 1 ↔ y ∈ H`. Rewrite using `[← hLart, artinCoord_localArtinMap]`. Conclude with `QuotientGroup.eq_one_iff y`. Introduce `y`. Simplify using `[hFF', hU']`.

Introduce `g`. Simplify using `[hFe, hUe]`.
-/
private theorem ag_field (K Ω : Type) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] [Field Ω] [Algebra K Ω] [IsSepClosure K Ω]
    {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (ε : G ≃* (Ω ≃ₐ[K] Ω))
    (hε : Continuous ε) (hε' : Continuous ε.symm) :
    ∃ (θ : Kˣ →* TopologicalAbelianization G) (D : TopologicalAbelianization G →* Multiplicative ProfiniteInteger),
      Continuous θ ∧ Function.Injective θ ∧ DenseRange θ ∧
      (∀ H : Subgroup Kˣ, IsOpen (H : Set Kˣ) → H.FiniteIndex →
        ∃ V : Subgroup (TopologicalAbelianization G), IsOpen (V : Set (TopologicalAbelianization G)) ∧ V.comap θ = H) ∧
      Continuous D ∧ (∀ y : Kˣ, D (θ y) = Multiplicative.ofAdd ((ord (y : K) : ℤ) : ProfiniteInteger)) ∧
      ∀ g : G, D (QuotientGroup.mk' _ g) = unramifiedDegree K Ω (ε g) := by
  obtain ⟨F, hF, hFe⟩ := ag_map (ε : G →* (Ω ≃ₐ[K] Ω)) hε
  obtain ⟨F', hF', hF'e⟩ := ag_map (ε.symm : (Ω ≃ₐ[K] Ω) →* G) hε'
  have hFF' : ∀ b, F (F' b) = b := by
    intro b
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective b
    rw [hF'e, hFe]
    simp
  have hF'F : ∀ a, F' (F a) = a := by
    intro a
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective a
    rw [hFe, hF'e]
    simp
  obtain ⟨U, hU, hUe⟩ := ag_lift (unramifiedDegree K Ω) continuous_unramifiedDegree
  set L := localReciprocityLimit K Ω
  have hLart : ∀ x, localArtinMap K Ω x = topologicalAbelianizationEquiv K Ω (L x) :=
    fun x => localArtinMap_apply x
  have hLc : Continuous L := by
    have h : (L : Kˣ → _) = (topologicalAbelianizationEquiv K Ω).symm ∘ localArtinMap K Ω := by
      funext x
      simp [hLart]
    rw [h]
    exact (topologicalAbelianizationEquiv K Ω).symm.continuous.comp continuous_localArtinMap
  have hLi : Function.Injective L := by
    intro x y hxy
    apply injective_localArtinMap (K := K) (Ω := Ω)
    rw [hLart, hLart, hxy]
  have hU' : ∀ x : Kˣ, U (L x) = Multiplicative.ofAdd ((ord (x : K) : ℤ) : ProfiniteInteger) := by
    intro x
    obtain ⟨g, hg⟩ := QuotientGroup.mk_surjective (L x)
    rw [← hg, hUe]
    exact unramifiedDegree_of_mk_eq_localReciprocityLimit hg
  refine ⟨F'.comp L, U.comp F, hF'.comp hLc, ?_, ?_, ?_, hU.comp hF, ?_, ?_⟩
  · intro x y hxy
    apply hLi
    have := congrArg F hxy
    simpa [hFF'] using this
  · exact (Function.Surjective.denseRange (fun a => ⟨F a, hF'F a⟩)).comp
      (denseRange_localReciprocityLimit (K := K) (Ω := Ω)) hF'
  · intro H hHo hHf
    let H' : openFiniteIndex Kˣ := ⟨H, hHo, hHf⟩
    let ψ := ((artinCoord K Ω H').comp
      (topologicalAbelianizationEquiv K Ω).toMulEquiv.toMonoidHom).comp F
    have hψ : Continuous ψ :=
      (continuous_artinCoord H').comp ((topologicalAbelianizationEquiv K Ω).continuous.comp hF)
    haveI := openCompletion.discreteTopology_quotient H'
    refine ⟨ψ.ker, ?_, ?_⟩
    · exact (isOpen_discrete ({1} : Set (Kˣ ⧸ (H : Subgroup Kˣ)))).preimage hψ
    · ext y
      simp only [Subgroup.mem_comap, MonoidHom.mem_ker, ψ, MonoidHom.comp_apply, hFF']
      change artinCoord K Ω H' (topologicalAbelianizationEquiv K Ω (L y)) = 1 ↔ y ∈ H
      rw [← hLart, artinCoord_localArtinMap]
      exact QuotientGroup.eq_one_iff y
  · intro y
    simp [hFF', hU']
  · intro g
    simp [hFe, hUe]

open GroundTheory.LocalField ValuativeRel IsLocalRing in
/- English proof (translation)
Rewrite using `[CharP.charP_iff_prime_eq_zero (Fact.out : l.Prime)]`. Establish `hnu : ¬ IsUnit ((l : 𝒪[k]))`. Introduce and unpack `⟨u, hu⟩`. Establish `h1 : ((u⁻¹ : 𝒪[k]ˣ) : 𝒪[k]) * (l : 𝒪[k]) = 1`. Rewrite using `[← hu]`.

Simplify using the standard rewrite rules. Establish `h2 : ((((u⁻¹ : 𝒪[k]ˣ) : 𝒪[k]) : k)) = algebraMap ℚ_[l] k ((l : ℚ_[l])⁻¹)`. Use `congrArg (fun x : 𝒪[k] => (x : k)) h1` as an intermediate fact. Simplify using `only [Subring.coe_mul, Subring.coe_natCast, Subring.coe_one] at this`. Rewrite using `[map_inv₀, map_natCast]`.

Conclude with `eq_inv_of_mul_eq_one_left this`. Establish `h3 : algebraMap ℚ_[l] k ((l : ℚ_[l])⁻¹) ∈ (ValuativeRel.valuation k).integer`. Rewrite using `[← h2]`. Conclude with `(((u⁻¹ : 𝒪[k]ˣ) : 𝒪[k])).2`. Rewrite `h3` using `[algebraMap_mem_integer_iff, PadicRank.mem_integer_padic_iff]`.

Rewrite `h3` using `[norm_inv, Padic.norm_p, inv_inv]`. Establish `: (1 : ℝ) < l` using `by exact_mod_cast (Fact.out : l.Prime).one_lt`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hmem : (l : 𝒪[k]) ∈ maximalIdeal 𝒪[k]` using `(mem_maximalIdeal _).2 hnu`. Rewrite using `[← map_natCast (residue 𝒪[k]) l]`.

Conclude with `(residue_eq_zero_iff _).2 hmem`.
-/
private theorem ag_char (l : ℕ) [Fact l.Prime] (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] [Algebra ℚ_[l] k] [ValuativeExtension ℚ_[l] k] : CharP 𝓀[k] l := by
  rw [CharP.charP_iff_prime_eq_zero (Fact.out : l.Prime)]
  have hnu : ¬ IsUnit ((l : 𝒪[k])) := by
    rintro ⟨u, hu⟩
    have h1 : ((u⁻¹ : 𝒪[k]ˣ) : 𝒪[k]) * (l : 𝒪[k]) = 1 := by
      rw [← hu]
      simp
    have h2 : ((((u⁻¹ : 𝒪[k]ˣ) : 𝒪[k]) : k)) = algebraMap ℚ_[l] k ((l : ℚ_[l])⁻¹) := by
      have := congrArg (fun x : 𝒪[k] => (x : k)) h1
      simp only [Subring.coe_mul, Subring.coe_natCast, Subring.coe_one] at this
      rw [map_inv₀, map_natCast]
      exact eq_inv_of_mul_eq_one_left this
    have h3 : algebraMap ℚ_[l] k ((l : ℚ_[l])⁻¹) ∈ (ValuativeRel.valuation k).integer := by
      rw [← h2]
      exact (((u⁻¹ : 𝒪[k]ˣ) : 𝒪[k])).2
    rw [algebraMap_mem_integer_iff, PadicRank.mem_integer_padic_iff] at h3
    rw [norm_inv, Padic.norm_p, inv_inv] at h3
    have : (1 : ℝ) < l := by exact_mod_cast (Fact.out : l.Prime).one_lt
    linarith
  have hmem : (l : 𝒪[k]) ∈ maximalIdeal 𝒪[k] := (mem_maximalIdeal _).2 hnu
  rw [← map_natCast (residue 𝒪[k]) l]
  exact (residue_eq_zero_iff _).2 hmem

/- English proof (translation)
Introduce `l _ G _ _ _ φ hφ`. Take `⟨K, e, he, he', hcomp, -, hidx, -⟩` from `openField φ hφ`. Use `haveI hfin : FiniteDimensional ℚ_[l] K.1 := K.2`. Take `⟨vr, tp, hloc, hext⟩` from `GroundTheory.LocalField.exists_isNonarchimedeanLocalField_valuativeExtension ℚ_[l] K.1`. Use `letI := vr`.

Use `letI := tp`. Use `haveI := hloc`. Use `haveI := hext`. Use `haveI : Algebra.IsAlgebraic K.1 (Om l) := Algebra.IsAlgebraic.tower_top (K := ℚ_[l]) K.1`. Use `haveI : IsAlgClosure K.1 (Om l) := ⟨inferInstance, inferInstance⟩`.

Use `haveI : IsSepClosure K.1 (Om l) := inferInstance`. Take `⟨hc1, hc2⟩` from `GlobalTheory.fixingSubgroupEquiv_bicontinuous ℚ_[l] (Om l) K.1`. Set `ε : G ≃* Gal(Om l/K.1)` to `e.trans K.1.fixingSubgroupEquiv`. Establish `hε : Continuous ε` using `hc1.comp he`. Establish `hε' : Continuous ε.symm` using `he'.comp hc2`.

Take `⟨θ, D, h1, h2, h3, h4, h5, h6, hD⟩` from `ag_field K.1 (Om l) ε hε hε'`. Use `⟨K.1, inferInstance, vr, tp, hloc, inferInstance, hext, hfin, hidx, θ, D, h1, h2, h3, h4, h5, h6, ?_⟩` and prove the remaining obligations. Introduce `g`. Establish `hεg : ∀ x, (ε g) x = φ g x`. Introduce `x`.

Rewrite using `[← hcomp]`. Both sides reduce to the same expression. Use `haveI := ag_char l K.1`. Rewrite using `[hD g, GroundTheory.LocalField.unramifiedDegree_eq_one_iff]`. Simplify using `only [Iq, MaximalUnramifiedExtension, GroundTheory.LocalField.mem_fixingSubgroup_adjoin_iff, GroundTheory.LocalField.mem_unramifiedRoots_iff, hεg]`.

Prove the components needed by the constructor for the conclusion. Introduce and unpack `h ξ ⟨m, hm, hξ⟩`. Apply `h` to reduce the goal to its premises. Use `⟨m, ?_, ?_, hξ⟩` and prove the remaining obligations. Break down `Nat.eq_zero_or_pos m with rfl | hpos` into its components or cases.

Simplify using `at hm`. Conclude with `hpos`. Introduce `hdvd`. Conclude with `hm ((CharP.cast_eq_zero_iff _ l m).2 hdvd)`. Introduce and unpack `h ξ ⟨m, -, hml, hξ⟩`.

Apply `h` to reduce the goal to its premises. Conclude with `⟨m, fun h0 => hml ((CharP.cast_eq_zero_iff _ l m).1 h0), hξ⟩`.
-/
theorem UpperTheory.local_class_field_theory_of_open_embedding :
    ∀ {l : ℕ} [Fact l.Prime] {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (φ : G →* GQ l) (hφ : IsOpenEmbedding φ), ∃ (K : Type) (_ : Field K) (_ : ValuativeRel K) (_ : TopologicalSpace K) (_ : IsNonarchimedeanLocalField K) (_ : Algebra ℚ_[l] K) (_ : ValuativeExtension ℚ_[l] K) (_ : FiniteDimensional ℚ_[l] K), φ.range.index = Module.finrank ℚ_[l] K ∧ ∃ (θ : Kˣ →* TopologicalAbelianization G) (D : TopologicalAbelianization G →* Multiplicative GroundTheory.LocalField.Abstract.ProfiniteInteger), Continuous θ ∧ Function.Injective θ ∧ DenseRange θ ∧ (∀ H : Subgroup Kˣ, IsOpen (H : Set Kˣ) → H.FiniteIndex → ∃ V : Subgroup (TopologicalAbelianization G), IsOpen (V : Set (TopologicalAbelianization G)) ∧ V.comap θ = H) ∧ Continuous D ∧ (∀ y : Kˣ, D (θ y) = Multiplicative.ofAdd ((GroundTheory.LocalField.ord (y : K) : ℤ) : GroundTheory.LocalField.Abstract.ProfiniteInteger)) ∧ ∀ g : G, φ g ∈ Iq l ↔ D (QuotientGroup.mk' _ g) = 1 := by
  intro l _ G _ _ _ φ hφ
  obtain ⟨K, e, he, he', hcomp, -, hidx, -⟩ := openField φ hφ
  haveI hfin : FiniteDimensional ℚ_[l] K.1 := K.2
  obtain ⟨vr, tp, hloc, hext⟩ :=
    GroundTheory.LocalField.exists_isNonarchimedeanLocalField_valuativeExtension ℚ_[l] K.1
  letI := vr
  letI := tp
  haveI := hloc
  haveI := hext
  haveI : Algebra.IsAlgebraic K.1 (Om l) := Algebra.IsAlgebraic.tower_top (K := ℚ_[l]) K.1
  haveI : IsAlgClosure K.1 (Om l) := ⟨inferInstance, inferInstance⟩
  haveI : IsSepClosure K.1 (Om l) := inferInstance
  obtain ⟨hc1, hc2⟩ := GlobalTheory.fixingSubgroupEquiv_bicontinuous ℚ_[l] (Om l) K.1
  let ε : G ≃* Gal(Om l/K.1) := e.trans K.1.fixingSubgroupEquiv
  have hε : Continuous ε := hc1.comp he
  have hε' : Continuous ε.symm := he'.comp hc2
  obtain ⟨θ, D, h1, h2, h3, h4, h5, h6, hD⟩ := ag_field K.1 (Om l) ε hε hε'
  refine ⟨K.1, inferInstance, vr, tp, hloc, inferInstance, hext, hfin, hidx, θ, D,
    h1, h2, h3, h4, h5, h6, ?_⟩
  intro g
  have hεg : ∀ x, (ε g) x = φ g x := by
    intro x
    rw [← hcomp]
    rfl
  haveI := ag_char l K.1
  rw [hD g, GroundTheory.LocalField.unramifiedDegree_eq_one_iff]
  simp only [Iq, MaximalUnramifiedExtension, GroundTheory.LocalField.mem_fixingSubgroup_adjoin_iff,
    GroundTheory.LocalField.mem_unramifiedRoots_iff, hεg]
  constructor
  · rintro h ξ ⟨m, hm, hξ⟩
    apply h
    refine ⟨m, ?_, ?_, hξ⟩
    · rcases Nat.eq_zero_or_pos m with rfl | hpos
      · simp at hm
      · exact hpos
    · intro hdvd
      exact hm ((CharP.cast_eq_zero_iff _ l m).2 hdvd)
  · rintro h ξ ⟨m, -, hml, hξ⟩
    apply h
    exact ⟨m, fun h0 => hml ((CharP.cast_eq_zero_iff _ l m).1 h0), hξ⟩

import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeDeformations.IsHostFrame
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.PoitouTateNormalised
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.ArtKer
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.ToGalDict
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.Places
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.GalEmbTop
import Development.AutomorphicArithmetic.AutomorphicVarieties.PartsConj

open Matrix IsLocalRing ReciprocityTheory.Gal UpperTheory.V.HV UpperTheory.V.U3 UpperTheory.V.Alg UpperTheory.V.UnitaryThreeInertia

open NumberField NumberField.InfinitePlace Real in
/- English proof (translation)
Apply `RingOfIntegers.isPrincipalIdealRing_of_abs_discr_lt` to reduce the goal to its premises. Rewrite using `[IsCyclotomicExtension.Rat.discr_prime_pow 2 2 K, IsCyclotomicExtension.Rat.finrank (2 ^ 2) K, IsCyclotomicExtension.Rat.nrComplexPlaces_eq_totient_div_two (2 ^ 2) K]`. Establish `h4 : (2 ^ 2 : ℕ).totient = 2` using `by decide`. Rewrite using `[h4]`. Evaluate the numerical expressions using `[Nat.factorial]`.

Use polynomial arithmetic with `[Real.pi_gt_three]`.
-/
private theorem pid4 (K : Type) [Field K] [NumberField K] [IsCyclotomicExtension {2 ^ 2} ℚ K] :
    IsPrincipalIdealRing (𝓞 K) := by
  apply RingOfIntegers.isPrincipalIdealRing_of_abs_discr_lt
  rw [IsCyclotomicExtension.Rat.discr_prime_pow 2 2 K, IsCyclotomicExtension.Rat.finrank (2 ^ 2) K,
    IsCyclotomicExtension.Rat.nrComplexPlaces_eq_totient_div_two (2 ^ 2) K]
  have h4 : (2 ^ 2 : ℕ).totient = 2 := by decide
  rw [h4]
  norm_num [Nat.factorial]
  nlinarith [Real.pi_gt_three]

open NumberField Formalism.ConjugateSelfDual UpperTheory.V UpperTheory.V.Base UpperTheory.V.Kum in
/- English proof (translation)
Use `haveI : IsPrincipalIdealRing (𝓞 K) := pid4 K`. Establish `hc : Fintype.card (ClassGroup (𝓞 K)) = 1`. Use `card_classGroup_eq_one (R := 𝓞 K)` and compare the differences between its conclusion and the goal. Establish `hsub : Subsingleton (ClassGroup (𝓞 K))` using `Fintype.card_le_one_iff_subsingleton.mp (le_of_eq hc)`. Establish `hopen : IsOpen (χ.ker : Set (G K Ω))`.

Establish `: (χ.ker : Set (G K Ω)) = χ ⁻¹' {1}`. Use extensionality with `x`. Simplify using `[MonoidHom.mem_ker]`. Rewrite using `[this]`. Conclude with `h.isOpen_fiber 1`.

Establish `hconj : ∀ c : G K Ω, UpperTheory.V.IsConjOm c.toRingEquiv → χ c = 1`. Introduce and unpack `c ⟨j, hj⟩`. It suffices to derive a contradiction. Establish `hζ` using `IsCyclotomicExtension.zeta_spec (2 ^ 2) ℚ K`. Use `set z : Ω := algebraMap K Ω (IsCyclotomicExtension.zeta (2 ^ 2) ℚ K) with hz`.

Establish `hz4 : z ^ 4 = 1`. Rewrite using `[hz, ← map_pow, show (4 : ℕ) = 2 ^ 2 by norm_num, hζ.pow_eq_one, map_one]`. Establish `hz2 : z ^ 2 ≠ 1`. Introduce `h2`. Establish `hinj` using `(algebraMap K Ω).injective`.

Establish `: (IsCyclotomicExtension.zeta (2 ^ 2) ℚ K) ^ 2 = 1`. Apply `hinj` to reduce the goal to its premises. Rewrite using `[map_pow, map_one]`. Conclude with `h2`. Use `(hζ.pow_eq_one_iff_dvd 2).1 this` as an intermediate fact.

Evaluate the numerical expressions using `at this`. Establish `hsq : z ^ 2 = -1`. Establish `hf : (z ^ 2 - 1) * (z ^ 2 + 1) = 0`. Establish `: (z ^ 2 - 1) * (z ^ 2 + 1) = z ^ 4 - 1` using `by ring`. Rewrite using `[this, hz4, sub_self]`.

Break down `mul_eq_zero.1 hf with h0 | h0` into its components or cases. Conclude with `absurd (sub_eq_zero.1 h0) hz2`. Conclude with `eq_neg_of_add_eq_zero_left h0`. Establish `hfix : c z = z`. Rewrite using `[hz]`.

Conclude with `c.commutes _`. Establish `hw` using `hj z`. Establish `hcz : c.toRingEquiv z = z` using `hfix`. Rewrite `hw` using `[hcz]`. Establish `hw2 : (j z) ^ 2 = -1`.

Rewrite using `[← map_pow, hsq, map_neg, map_one]`. Establish `him : (j z).im = 0`. Use `congrArg Complex.im hw` as an intermediate fact. Simplify using `at this`. Combine the linear equalities and inequalities to obtain the conclusion.

Establish `hre` using `congrArg Complex.re hw2`. Simplify using `[pow_two, Complex.mul_re, him] at hre`. Use polynomial arithmetic with `[sq_nonneg (j z).re]`. Establish `hk` using `UpperTheory.V.Kum.artKer K Ω C χ hopen hI hconj`. Establish `hg : g ∈ (UpperTheory.V.Kum.artCl K Ω).ker`.

Rewrite using `[MonoidHom.mem_ker]`. Conclude with `Subsingleton.elim _ _`. Conclude with `hk hg`.
-/
private theorem char_triv (K Ω : Type) [Field K] [NumberField K] [IsCyclotomicExtension {2 ^ 2} ℚ K] [Field Ω]
    [Algebra K Ω] [IsAlgClosure K Ω] (C : Type) [CommGroup C] (χ : G K Ω →* C) (h : IsLocallyConstant χ)
    (hI : ∀ A : ValuationSubring Ω, Ine (F := K) A ≤ χ.ker) (g : G K Ω) : χ g = 1 := by
  haveI : IsPrincipalIdealRing (𝓞 K) := pid4 K
  have hc : Fintype.card (ClassGroup (𝓞 K)) = 1 := by
    convert card_classGroup_eq_one (R := 𝓞 K)
  have hsub : Subsingleton (ClassGroup (𝓞 K)) :=
    Fintype.card_le_one_iff_subsingleton.mp (le_of_eq hc)
  have hopen : IsOpen (χ.ker : Set (G K Ω)) := by
    have : (χ.ker : Set (G K Ω)) = χ ⁻¹' {1} := by
      ext x
      simp [MonoidHom.mem_ker]
    rw [this]
    exact h.isOpen_fiber 1
  have hconj : ∀ c : G K Ω, UpperTheory.V.IsConjOm c.toRingEquiv → χ c = 1 := by
    rintro c ⟨j, hj⟩
    exfalso
    have hζ := IsCyclotomicExtension.zeta_spec (2 ^ 2) ℚ K
    set z : Ω := algebraMap K Ω (IsCyclotomicExtension.zeta (2 ^ 2) ℚ K) with hz
    have hz4 : z ^ 4 = 1 := by
      rw [hz, ← map_pow, show (4 : ℕ) = 2 ^ 2 by norm_num, hζ.pow_eq_one, map_one]
    have hz2 : z ^ 2 ≠ 1 := by
      intro h2
      have hinj := (algebraMap K Ω).injective
      have : (IsCyclotomicExtension.zeta (2 ^ 2) ℚ K) ^ 2 = 1 := by
        apply hinj
        rw [map_pow, map_one]
        exact h2
      have := (hζ.pow_eq_one_iff_dvd 2).1 this
      norm_num at this
    have hsq : z ^ 2 = -1 := by
      have hf : (z ^ 2 - 1) * (z ^ 2 + 1) = 0 := by
        have : (z ^ 2 - 1) * (z ^ 2 + 1) = z ^ 4 - 1 := by ring
        rw [this, hz4, sub_self]
      rcases mul_eq_zero.1 hf with h0 | h0
      · exact absurd (sub_eq_zero.1 h0) hz2
      · exact eq_neg_of_add_eq_zero_left h0
    have hfix : c z = z := by
      rw [hz]
      exact c.commutes _
    have hw := hj z
    have hcz : c.toRingEquiv z = z := hfix
    rw [hcz] at hw
    have hw2 : (j z) ^ 2 = -1 := by
      rw [← map_pow, hsq, map_neg, map_one]
    have him : (j z).im = 0 := by
      have := congrArg Complex.im hw
      simp at this
      linarith
    have hre := congrArg Complex.re hw2
    simp [pow_two, Complex.mul_re, him] at hre
    nlinarith [sq_nonneg (j z).re]
  have hk := UpperTheory.V.Kum.artKer K Ω C χ hopen hI hconj
  have hg : g ∈ (UpperTheory.V.Kum.artCl K Ω).ker := by
    rw [MonoidHom.mem_ker]
    exact Subsingleton.elim _ _
  exact hk hg

open NumberField Formalism.ConjugateSelfDual UpperTheory.V UpperTheory.V.Base UpperTheory.V.Kum IntermediateField in
/- English proof (translation)
Establish `hz : ζ ≠ 0` using `hζ.ne_zero (by norm_num)`. Establish `h1 : ζ ≠ 1` using `hζ.ne_one (by norm_num)`. Establish `h2 : ζ ^ 2 ≠ 1`. Introduce `h`. Use `(hζ.pow_eq_one_iff_dvd 2).1 h` as an intermediate fact.

Use linear arithmetic over natural numbers and integers. Establish `hcls : ∀ τ : Formalism.ConjugateSelfDual.G ℚ Ω, τ ζ = ζ ↔ eta4 Ω τ = 1`. Introduce `τ`. Establish `hs` using `UpperTheory.V.Chr.cls_spec (k := ℚ) 4 τ ζ hζ.pow_eq_one`. Establish `he : eta4 Ω τ = 1 ↔ ZMod.χ₄ ((UpperTheory.V.Chr.cls ℚ Ω 4 τ : (ZMod 4)ˣ) : ZMod 4) = 1`.

Rewrite using `[Units.ext_iff]`. Both sides reduce to the same expression. Rewrite using `[he]`. Generalize the expression as in `((UpperTheory.V.Chr.cls ℚ Ω 4 τ : (ZMod 4)ˣ) : ZMod 4) = c at hs`. Rewrite using `[← ZMod.natCast_zmod_val c]`.

Establish `hn : c.val < 4` using `ZMod.val_lt c`. Generalize the expression as in `c.val = n at hs hn`. Rewrite using `[hs]`. Use `interval_cases n`. Prove the components needed by the constructor for the conclusion.

Introduce `h`. Conclude with `absurd (by simpa using h.symm) h1`. Introduce `h`. Conclude with `absurd h (by decide)`. Prove the components needed by the constructor for the conclusion.

Introduce `_`. Evaluate the decidable proposition. Introduce `_`. Conclude with `pow_one ζ`. Prove the components needed by the constructor for the conclusion.

Introduce `h`. It suffices to derive a contradiction. Apply `h1` to reduce the goal to its premises. Establish `h' : ζ * ζ = ζ * 1`. Rewrite using `[mul_one, ← pow_two]`.

Conclude with `h`. Conclude with `mul_left_cancel₀ hz h'`. Introduce `h`. Conclude with `absurd h (by decide)`. Prove the components needed by the constructor for the conclusion.

Introduce `h`. It suffices to derive a contradiction. Apply `h2` to reduce the goal to its premises. Establish `h' : ζ ^ 2 * ζ = 1 * ζ`. Rewrite using `[one_mul, ← pow_succ]`.

Conclude with `h`. Conclude with `mul_right_cancel₀ hz h'`. Introduce `h`. Conclude with `absurd h (by decide)`. Prove the components needed by the constructor for the conclusion.

Introduce `h`. Conclude with `(hcls σ).1 (h ⟨ζ, IntermediateField.mem_adjoin_simple_self ℚ ζ⟩)`. Introduce `h x`. Establish `hs : σ ζ = ζ` using `(hcls σ).2 h`. Establish `hle : ℚ⟮ζ⟯ ≤ IntermediateField.fixedField (Subgroup.zpowers σ)`.

Rewrite using `[IntermediateField.adjoin_simple_le_iff, IntermediateField.mem_fixedField_iff]`. Introduce `τ hτ`. Establish `hst : σ ∈ MulAction.stabilizer (Formalism.ConjugateSelfDual.G ℚ Ω) ζ` using `hs`. Use `(Subgroup.zpowers_le (H := MulAction.stabilizer (Formalism.ConjugateSelfDual.G ℚ Ω) ζ)).2 hst hτ` as an intermediate fact. Conclude with `this`.

Establish `hx` using `(IntermediateField.mem_fixedField_iff _ _).1 (hle x.2) σ (Subgroup.mem_zpowers σ)`. Conclude with `hx`.
-/
private theorem mem_iff (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (ζ : Ω) (hζ : IsPrimitiveRoot ζ 4)
    (σ : G ℚ Ω) : σ ∈ galOf ℚ ℚ⟮ζ⟯ Ω ↔ eta4 Ω σ = 1 := by
  have hz : ζ ≠ 0 := hζ.ne_zero (by norm_num)
  have h1 : ζ ≠ 1 := hζ.ne_one (by norm_num)
  have h2 : ζ ^ 2 ≠ 1 := by
    intro h
    have := (hζ.pow_eq_one_iff_dvd 2).1 h
    omega
  have hcls : ∀ τ : Formalism.ConjugateSelfDual.G ℚ Ω, τ ζ = ζ ↔ eta4 Ω τ = 1 := by
    intro τ
    have hs := UpperTheory.V.Chr.cls_spec (k := ℚ) 4 τ ζ hζ.pow_eq_one
    have he : eta4 Ω τ = 1 ↔ ZMod.χ₄ ((UpperTheory.V.Chr.cls ℚ Ω 4 τ : (ZMod 4)ˣ) : ZMod 4) = 1 := by
      rw [Units.ext_iff]
      rfl
    rw [he]
    generalize ((UpperTheory.V.Chr.cls ℚ Ω 4 τ : (ZMod 4)ˣ) : ZMod 4) = c at hs
    rw [← ZMod.natCast_zmod_val c]
    have hn : c.val < 4 := ZMod.val_lt c
    generalize c.val = n at hs hn
    rw [hs]
    interval_cases n
    · constructor
      · intro h
        exact absurd (by simpa using h.symm) h1
      · intro h
        exact absurd h (by decide)
    · constructor
      · intro _
        decide
      · intro _
        exact pow_one ζ
    · constructor
      · intro h
        exfalso
        apply h1
        have h' : ζ * ζ = ζ * 1 := by
          rw [mul_one, ← pow_two]
          exact h
        exact mul_left_cancel₀ hz h'
      · intro h
        exact absurd h (by decide)
    · constructor
      · intro h
        exfalso
        apply h2
        have h' : ζ ^ 2 * ζ = 1 * ζ := by
          rw [one_mul, ← pow_succ]
          exact h
        exact mul_right_cancel₀ hz h'
      · intro h
        exact absurd h (by decide)
  constructor
  · intro h
    exact (hcls σ).1 (h ⟨ζ, IntermediateField.mem_adjoin_simple_self ℚ ζ⟩)
  · intro h x
    have hs : σ ζ = ζ := (hcls σ).2 h
    have hle : ℚ⟮ζ⟯ ≤ IntermediateField.fixedField (Subgroup.zpowers σ) := by
      rw [IntermediateField.adjoin_simple_le_iff, IntermediateField.mem_fixedField_iff]
      intro τ hτ
      have hst : σ ∈ MulAction.stabilizer (Formalism.ConjugateSelfDual.G ℚ Ω) ζ := hs
      have := (Subgroup.zpowers_le (H := MulAction.stabilizer (Formalism.ConjugateSelfDual.G ℚ Ω) ζ)).2 hst hτ
      exact this
    have hx := (IntermediateField.mem_fixedField_iff _ _).1 (hle x.2) σ (Subgroup.mem_zpowers σ)
    exact hx

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual UpperTheory.V in
open scoped Pointwise in
/- English proof (translation)
Take `⟨σ, hσ⟩` from `exists_smul_eq_of_isPlaceOver hA hB`. Establish `hl : UpperTheory.V.IsLift (RingEquiv.refl k) σ.toRingEquiv` using `fun x => σ.commutes x`. Establish `hm : ∀ x : Ω, σ.toRingEquiv x ∈ B ↔ x ∈ A`. Introduce `x`. Rewrite using `[← hσ]`.

Conclude with `ValuationSubring.smul_mem_pointwise_smul_iff`. Establish `key` using `UpperTheory.V.conjGal_mem_Ine hl hm hτ`. Use `⟨σ, ?_⟩` and prove the remaining obligations. Establish `he : UpperTheory.V.conjGal hl τ = σ⁻¹ * τ * σ`. Use extensionality with `x`.

Both sides reduce to the same expression. Rewrite `key` using `[he]`. Then use the resulting hypothesis.
-/
private theorem conj_ine {k Ω : Type} [Field k] [NumberField k] [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω]
    {A B : ValuationSubring Ω} {v : HeightOneSpectrum (𝓞 k)} (hA : IsPlaceOver A v) (hB : IsPlaceOver B v)
    {τ : G k Ω} (hτ : τ ∈ Ine (F := k) B) : ∃ g : G k Ω, g⁻¹ * τ * g ∈ Ine (F := k) A := by
  obtain ⟨σ, hσ⟩ := exists_smul_eq_of_isPlaceOver hA hB
  have hl : UpperTheory.V.IsLift (RingEquiv.refl k) σ.toRingEquiv := fun x => σ.commutes x
  have hm : ∀ x : Ω, σ.toRingEquiv x ∈ B ↔ x ∈ A := by
    intro x
    rw [← hσ]
    exact ValuationSubring.smul_mem_pointwise_smul_iff
  have key := UpperTheory.V.conjGal_mem_Ine hl hm hτ
  refine ⟨σ, ?_⟩
  have he : UpperTheory.V.conjGal hl τ = σ⁻¹ * τ * σ := by
    ext x
    rfl
  rwa [he] at key

open NumberField Formalism.ConjugateSelfDual UpperTheory.V UpperTheory.V.Base UpperTheory.V.Kum IntermediateField in
/- English proof (translation)
Introduce `Ω _ _ _ l _ c N _ e ψ o₁ hD S A F hF`. Introduce `Ab _ χ hloc hχ`. Use `haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ`. Choose the witnesses or unpack the hypotheses as in `⟨ζ, hζ⟩ : ∃ ζ : Ω, IsPrimitiveRoot ζ 4 := by`. Take `⟨z, hz⟩` from `IsAlgClosed.exists_root (Polynomial.cyclotomic 4 Ω) (Polynomial.degree_cyclotomic_pos 4 Ω (by norm_num)).ne.symm`.

Conclude with `⟨z, (Polynomial.isRoot_cyclotomic_iff).1 hz⟩`. Use `haveI : Algebra.IsAlgebraic ℚ Ω := IsAlgClosure.isAlgebraic`. Establish `hint : IsIntegral ℚ ζ` using `Algebra.IsIntegral.isIntegral ζ`. Use `haveI : FiniteDimensional ℚ ℚ⟮ζ⟯ := IntermediateField.adjoin.finiteDimensional hint`. Use `haveI : NumberField ℚ⟮ζ⟯ := {}`.

Use `haveI : IsCyclotomicExtension {2 ^ 2} ℚ ℚ⟮ζ⟯ := by`. Establish `h4` using `hζ.intermediateField_adjoin_isCyclotomicExtension ℚ`. Evaluate the numerical expressions. Conclude with `h4`. Use `haveI : IsAlgClosure ℚ⟮ζ⟯ Ω := ⟨inferInstance, Algebra.IsAlgebraic.tower_top (K := ℚ) ℚ⟮ζ⟯⟩`.

Take `⟨hDec, hIne, hcont, hhom⟩` from `UpperTheory.V.Kum.toGalDict ℚ Ω ℚ⟮ζ⟯ (galOf ℚ ℚ⟮ζ⟯ Ω) le_rfl`. Take `⟨hh, _⟩` from `hhom le_rfl`. Set `eq` to `MulEquiv.ofBijective (UpperTheory.V.Kum.toGal ℚ⟮ζ⟯ (le_refl (galOf ℚ ℚ⟮ζ⟯ Ω))) hh.bijective`. Establish `hker : ∀ u : galOf ℚ ℚ⟮ζ⟯ Ω, F.π u ∈ F.η.ker`. Introduce `u`.

Rewrite using `[MonoidHom.mem_ker]`. Establish `h1` using `DFunLike.congr_fun hF.η (u : Formalism.ConjugateSelfDual.G ℚ Ω)`. Rewrite `h1` using `[MonoidHom.comp_apply]`. Rewrite using `[h1]`. Conclude with `(mem_iff Ω ζ hζ u).1 u.2`.

Set `ρ : galOf ℚ ℚ⟮ζ⟯ Ω →* F.η.ker` to `(F.π.comp (galOf ℚ ℚ⟮ζ⟯ Ω).subtype).codRestrict F.η.ker hker`. Establish `hπc : Continuous F.π`. Rewrite using `[hF.π]`. Conclude with `continuous_toGS Ω _`. Establish `hρc : Continuous ρ` using `Continuous.subtype_mk (hπc.comp continuous_subtype_val) _`.

Establish `hec : Continuous eq.symm`. Establish `hs` using `(hh.homeomorph _).symm.continuous`. Use `hs using 1` and compare the differences between its conclusion and the goal. Use function extensionality and compare the values at `x`. Apply `eq.injective` to reduce the goal to its premises.

Rewrite using `[MulEquiv.apply_symm_apply]`. Conclude with `((hh.homeomorph _).apply_symm_apply x).symm`. Establish `key : ∀ (B : ValuationSubring Ω) (u : galOf ℚ ℚ⟮ζ⟯ Ω), (u : Formalism.ConjugateSelfDual.G ℚ Ω) ∈ Ine (F` using `ℚ) B → χ (ρ u) = 1 := by`. Introduce `B u hu`. Distinguish the cases in `hB : B = ⊤`.

Establish `h0` using `((UpperTheory.V.Base.places ℚ Ω l B).2.1 hB).1`. Rewrite `hu` using `[h0, Subgroup.mem_bot]`. Establish `: u = 1` using `Subtype.ext hu`. Rewrite using `[this, map_one, map_one]`. Take `⟨v, hv⟩` from `(UpperTheory.V.Base.places ℚ Ω l B).1 hB`.

Distinguish the cases in `hvS : v ∈ S`. Take `⟨g, hg⟩` from `conj_ine (hF.isOver ⟨v, hvS⟩) hv hu`. Establish `hgD : g⁻¹ * (u : Formalism.ConjugateSelfDual.G ℚ Ω) * g ∈ F.D ⟨v, hvS⟩`. Rewrite using `[hF.D]`. Conclude with `hg.1`.

Establish `hgI : (⟨_, hgD⟩ : F.D ⟨v, hvS⟩) ∈ F.Iv ⟨v, hvS⟩`. Rewrite using `[Subgroup.mem_subgroupOf, hF.I]`. Conclude with `hg`. Establish `heq : F.π g * (F.loc ⟨v, hvS⟩) ⟨_, hgD⟩ * (F.π g)⁻¹ = F.π u`. Simplify using `only [UpperTheory.V.UnitaryThreeInertia.Frame.loc, MonoidHom.comp_apply, Subgroup.coe_subtype, map_mul, map_inv]`.

Use `group`. Establish `hmem : F.π g * (F.loc ⟨v, hvS⟩) ⟨_, hgD⟩ * (F.π g)⁻¹ ∈ F.η.ker`. Rewrite using `[heq]`. Conclude with `hker u`. Use `hχ ⟨v, hvS⟩ ⟨_, hgD⟩ (F.π g) hmem hgI` as an intermediate fact.

Rewrite using `[← this]`. Use `congr 1`. Conclude with `Subtype.ext heq.symm`. Establish `hN : (u : Formalism.ConjugateSelfDual.G ℚ Ω) ∈ NS Ω (↑S : Set Pl)`. Apply `Subgroup.le_topologicalClosure` to reduce the goal to its premises.

Apply `Subgroup.subset_normalClosure` to reduce the goal to its premises. Use `Set.mem_iUnion₂.2 ⟨v, ?_, Set.mem_iUnion₂.2 ⟨B, hv, hu⟩⟩` and prove the remaining obligations. Simplify using `using hvS`. Establish `: ρ u = 1`. Apply `Subtype.ext` to reduce the goal to its premises.

Use `show F.π u = 1`. Rewrite using `[hF.π]`. Conclude with `(QuotientGroup.eq_one_iff _).2 hN`. Rewrite using `[this, map_one]`. Establish `htriv` using `char_triv ℚ⟮ζ⟯ Ω Ab ((χ.comp ρ).comp eq.symm.toMonoidHom) ((hloc.comp_continuous (hρc.comp hec))) (by`.

Introduce `B τ hτ`. Rewrite using `[MonoidHom.mem_ker, MonoidHom.comp_apply, MonoidHom.comp_apply]`. Apply `key B` to reduce the goal to its premises. Rewrite using `[← hIne B]`. Establish `: UpperTheory.V.Kum.toGal ℚ⟮ζ⟯ (le_refl (galOf ℚ ℚ⟮ζ⟯ Ω)) (eq.symm τ) = τ` using `eq.apply_symm_apply τ`.

Rewrite using `[MulEquiv.coe_toMonoidHom, this]`. Conclude with `hτ)`. Use extensionality with `⟨γ, hγ⟩`. Choose the witnesses or unpack the hypotheses as in `⟨u, rfl⟩ : ∃ u : Formalism.ConjugateSelfDual.G ℚ Ω, F.π u = γ := by`. Rewrite using `[hF.π]`.

Conclude with `QuotientGroup.mk'_surjective _ γ`. Establish `hu : u ∈ galOf ℚ ℚ⟮ζ⟯ Ω`. Rewrite using `[mem_iff Ω ζ hζ u]`. Establish `h1` using `DFunLike.congr_fun hF.η u`. Rewrite `h1` using `[MonoidHom.comp_apply]`.

Rewrite using `[← h1]`. Conclude with `hγ`. Use `htriv (eq ⟨u, hu⟩)` as an intermediate fact. Simplify using `only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulEquiv.symm_apply_apply] at this`. Rewrite using `[MonoidHom.one_apply, ← this]`.

Both sides reduce to the same expression.
-/
theorem UpperTheory.V.UnitaryThreeInertia.frame_class_one :
    ∀ (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] (c : Coef l) {N : ℕ} [NeZero N] (e : ℕ) (ψ : DirichletCharacter c.O N) (o₁ : ℕ), HostData l e ψ o₁ →
    ∀ (S : Finset Pl) (A : S → ValuationSubring Ω) (F : Frame c.O (Formalism.ConjugateSelfDual.G ℚ Ω) (Gam Ω S) S), IsHostFrame Ω c e ψ S A F →
    F.Cl1 := by
  intro Ω _ _ _ l _ c N _ e ψ o₁ hD S A F hF
  intro Ab _ χ hloc hχ
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  obtain ⟨ζ, hζ⟩ : ∃ ζ : Ω, IsPrimitiveRoot ζ 4 := by
    obtain ⟨z, hz⟩ := IsAlgClosed.exists_root (Polynomial.cyclotomic 4 Ω)
      (Polynomial.degree_cyclotomic_pos 4 Ω (by norm_num)).ne.symm
    exact ⟨z, (Polynomial.isRoot_cyclotomic_iff).1 hz⟩
  haveI : Algebra.IsAlgebraic ℚ Ω := IsAlgClosure.isAlgebraic
  have hint : IsIntegral ℚ ζ := Algebra.IsIntegral.isIntegral ζ
  haveI : FiniteDimensional ℚ ℚ⟮ζ⟯ := IntermediateField.adjoin.finiteDimensional hint
  haveI : NumberField ℚ⟮ζ⟯ := {}
  haveI : IsCyclotomicExtension {2 ^ 2} ℚ ℚ⟮ζ⟯ := by
    have h4 := hζ.intermediateField_adjoin_isCyclotomicExtension ℚ
    norm_num
    exact h4
  haveI : IsAlgClosure ℚ⟮ζ⟯ Ω := ⟨inferInstance, Algebra.IsAlgebraic.tower_top (K := ℚ) ℚ⟮ζ⟯⟩
  obtain ⟨hDec, hIne, hcont, hhom⟩ := UpperTheory.V.Kum.toGalDict ℚ Ω ℚ⟮ζ⟯ (galOf ℚ ℚ⟮ζ⟯ Ω) le_rfl
  obtain ⟨hh, _⟩ := hhom le_rfl
  let eq := MulEquiv.ofBijective (UpperTheory.V.Kum.toGal ℚ⟮ζ⟯ (le_refl (galOf ℚ ℚ⟮ζ⟯ Ω))) hh.bijective
  have hker : ∀ u : galOf ℚ ℚ⟮ζ⟯ Ω, F.π u ∈ F.η.ker := by
    intro u
    rw [MonoidHom.mem_ker]
    have h1 := DFunLike.congr_fun hF.η (u : Formalism.ConjugateSelfDual.G ℚ Ω)
    rw [MonoidHom.comp_apply] at h1
    rw [h1]
    exact (mem_iff Ω ζ hζ u).1 u.2
  let ρ : galOf ℚ ℚ⟮ζ⟯ Ω →* F.η.ker := (F.π.comp (galOf ℚ ℚ⟮ζ⟯ Ω).subtype).codRestrict F.η.ker hker
  have hπc : Continuous F.π := by
    rw [hF.π]
    exact continuous_toGS Ω _
  have hρc : Continuous ρ := Continuous.subtype_mk (hπc.comp continuous_subtype_val) _
  have hec : Continuous eq.symm := by
    have hs := (hh.homeomorph _).symm.continuous
    convert hs using 1
    funext x
    apply eq.injective
    rw [MulEquiv.apply_symm_apply]
    exact ((hh.homeomorph _).apply_symm_apply x).symm
  have key : ∀ (B : ValuationSubring Ω) (u : galOf ℚ ℚ⟮ζ⟯ Ω), (u : Formalism.ConjugateSelfDual.G ℚ Ω) ∈ Ine (F := ℚ) B → χ (ρ u) = 1 := by
    intro B u hu
    by_cases hB : B = ⊤
    · have h0 := ((UpperTheory.V.Base.places ℚ Ω l B).2.1 hB).1
      rw [h0, Subgroup.mem_bot] at hu
      have : u = 1 := Subtype.ext hu
      rw [this, map_one, map_one]
    · obtain ⟨v, hv⟩ := (UpperTheory.V.Base.places ℚ Ω l B).1 hB
      by_cases hvS : v ∈ S
      · obtain ⟨g, hg⟩ := conj_ine (hF.isOver ⟨v, hvS⟩) hv hu
        have hgD : g⁻¹ * (u : Formalism.ConjugateSelfDual.G ℚ Ω) * g ∈ F.D ⟨v, hvS⟩ := by
          rw [hF.D]
          exact hg.1
        have hgI : (⟨_, hgD⟩ : F.D ⟨v, hvS⟩) ∈ F.Iv ⟨v, hvS⟩ := by
          rw [Subgroup.mem_subgroupOf, hF.I]
          exact hg
        have heq : F.π g * (F.loc ⟨v, hvS⟩) ⟨_, hgD⟩ * (F.π g)⁻¹ = F.π u := by
          simp only [UpperTheory.V.UnitaryThreeInertia.Frame.loc, MonoidHom.comp_apply, Subgroup.coe_subtype, map_mul, map_inv]
          group
        have hmem : F.π g * (F.loc ⟨v, hvS⟩) ⟨_, hgD⟩ * (F.π g)⁻¹ ∈ F.η.ker := by
          rw [heq]
          exact hker u
        have := hχ ⟨v, hvS⟩ ⟨_, hgD⟩ (F.π g) hmem hgI
        rw [← this]
        congr 1
        exact Subtype.ext heq.symm
      · have hN : (u : Formalism.ConjugateSelfDual.G ℚ Ω) ∈ NS Ω (↑S : Set Pl) := by
          apply Subgroup.le_topologicalClosure
          apply Subgroup.subset_normalClosure
          refine Set.mem_iUnion₂.2 ⟨v, ?_, Set.mem_iUnion₂.2 ⟨B, hv, hu⟩⟩
          simpa using hvS
        have : ρ u = 1 := by
          apply Subtype.ext
          show F.π u = 1
          rw [hF.π]
          exact (QuotientGroup.eq_one_iff _).2 hN
        rw [this, map_one]
  have htriv := char_triv ℚ⟮ζ⟯ Ω Ab ((χ.comp ρ).comp eq.symm.toMonoidHom)
    ((hloc.comp_continuous (hρc.comp hec)))
    (by
      intro B τ hτ
      rw [MonoidHom.mem_ker, MonoidHom.comp_apply, MonoidHom.comp_apply]
      apply key B
      rw [← hIne B]
      have : UpperTheory.V.Kum.toGal ℚ⟮ζ⟯ (le_refl (galOf ℚ ℚ⟮ζ⟯ Ω)) (eq.symm τ) = τ := eq.apply_symm_apply τ
      rw [MulEquiv.coe_toMonoidHom, this]
      exact hτ)
  ext ⟨γ, hγ⟩
  obtain ⟨u, rfl⟩ : ∃ u : Formalism.ConjugateSelfDual.G ℚ Ω, F.π u = γ := by
    rw [hF.π]
    exact QuotientGroup.mk'_surjective _ γ
  have hu : u ∈ galOf ℚ ℚ⟮ζ⟯ Ω := by
    rw [mem_iff Ω ζ hζ u]
    have h1 := DFunLike.congr_fun hF.η u
    rw [MonoidHom.comp_apply] at h1
    rw [← h1]
    exact hγ
  have := htriv (eq ⟨u, hu⟩)
  simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulEquiv.symm_apply_apply] at this
  rw [MonoidHom.one_apply, ← this]
  rfl

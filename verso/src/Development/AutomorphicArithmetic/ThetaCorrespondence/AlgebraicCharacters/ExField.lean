import Development.AutomorphicArithmetic.ThetaCorrespondence.AlgebraicCharacters.EmbOrbit
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsRootOfUnityFixedDvdWeilGroupDegree
open UpperTheory.Lit.CharWD GlobalTheory.Published
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.WeilDeligne GlobalTheory.LocLanglands

/- English proof (translation)
Take `⟨y, hy⟩` from `(IsIntegrallyClosed.isIntegral_iff (R := A) (K := Ω)).1 ((x.isIntegral_coe.algebraMap (B := Ω)).tower_top (A := A))`. Conclude with `hy ▸ y.2`.
-/
private theorem val_int_le {L Ω : Type} [Field L] [NumberField L] [Field Ω] [Algebra L Ω]
    (A : ValuationSubring Ω) (x : 𝓞 L) : algebraMap L Ω x ∈ A := by
  obtain ⟨y, hy⟩ := (IsIntegrallyClosed.isIntegral_iff (R := A) (K := Ω)).1
    ((x.isIntegral_coe.algebraMap (B := Ω)).tower_top (A := A))
  exact hy ▸ y.2

/- English proof (translation)
Set `φ : 𝓞 L →+* A` to `((algebraMap L Ω).comp (algebraMap (𝓞 L) L)).codRestrict A.toSubring (val_int_le A)`. Set `P : Ideal (𝓞 L)` to `(IsLocalRing.maximalIdeal A).comap φ`. Establish `hP : ∀ x : 𝓞 L, A.valuation (algebraMap L Ω (x : L)) < 1 ↔ x ∈ P` using `fun x => (A.valuation_lt_one_iff (φ x)).symm`. Establish `hu : v.asIdeal = P.under (𝓞 F)`. Use extensionality with `x`.

Rewrite using `[← hA x, IsScalarTower.algebraMap_apply F L Ω]`. Conclude with `hP (algebraMap (𝓞 F) (𝓞 L) x)`. Use `haveI : P.LiesOver v.asIdeal := ⟨hu⟩`. Establish `hne : P ≠ ⊥` using `Ideal.ne_bot_of_liesOver_of_ne_bot v.ne_bot _`. Use `⟨⟨P, inferInstance, hne⟩, hP, ?_⟩` and prove the remaining obligations.

Use `haveI : Finite (𝓞 L ⧸ P) := Ideal.finiteQuotientOfFreeOfNeBot _ hne`. Conclude with `Nat.card_le_card_of_injective _ (FaithfulSMul.algebraMap_injective (𝓞 F ⧸ v.asIdeal) (𝓞 L ⧸ P))`.
-/
private theorem place_above {F L Ω : Type} [Field F] [NumberField F] [Field L] [NumberField L] [Field Ω]
    [Algebra F L] [Algebra F Ω] [Algebra L Ω] [IsScalarTower F L Ω] {v : HeightOneSpectrum (𝓞 F)}
    {A : ValuationSubring Ω} (hA : IsPlaceOver A v) :
    ∃ w : HeightOneSpectrum (𝓞 L), IsPlaceOver A w ∧ normV v ≤ normV w := by
  let φ : 𝓞 L →+* A := ((algebraMap L Ω).comp (algebraMap (𝓞 L) L)).codRestrict A.toSubring (val_int_le A)
  let P : Ideal (𝓞 L) := (IsLocalRing.maximalIdeal A).comap φ
  have hP : ∀ x : 𝓞 L, A.valuation (algebraMap L Ω (x : L)) < 1 ↔ x ∈ P :=
    fun x => (A.valuation_lt_one_iff (φ x)).symm
  have hu : v.asIdeal = P.under (𝓞 F) := by
    ext x
    rw [← hA x, IsScalarTower.algebraMap_apply F L Ω]
    exact hP (algebraMap (𝓞 F) (𝓞 L) x)
  haveI : P.LiesOver v.asIdeal := ⟨hu⟩
  have hne : P ≠ ⊥ := Ideal.ne_bot_of_liesOver_of_ne_bot v.ne_bot _
  refine ⟨⟨P, inferInstance, hne⟩, hP, ?_⟩
  haveI : Finite (𝓞 L ⧸ P) := Ideal.finiteQuotientOfFreeOfNeBot _ hne
  exact Nat.card_le_card_of_injective _ (FaithfulSMul.algebraMap_injective (𝓞 F ⧸ v.asIdeal) (𝓞 L ⧸ P))

/- English proof (translation)
Use `w.isMaximal` as an intermediate fact. Use `letI : Field (𝓞 K ⧸ w.asIdeal) := Ideal.Quotient.field _`. Establish `: Finite (𝓞 K ⧸ w.asIdeal)` using `Ideal.finiteQuotientOfFreeOfNeBot _ w.ne_bot`. Use `letI := Fintype.ofFinite (𝓞 K ⧸ w.asIdeal)`. Establish `e : normV w = (Finset.univ : Finset (𝓞 K ⧸ w.asIdeal)).card` using `Nat.card_eq_fintype_card`.

Rewrite using `[e, ← FiniteField.X_pow_card_sub_X_natDegree_eq (𝓞 K ⧸ w.asIdeal) hq]`. Use `Polynomial.card_le_degree_of_subset_roots fun y _ => ?_` and prove the remaining obligations. Take `⟨x, rfl⟩` from `Ideal.Quotient.mk_surjective y`. Rewrite using `[Polynomial.mem_roots (FiniteField.X_pow_card_sub_X_ne_zero _ hq)]`. Simplify using `using Ideal.Quotient.eq_zero_iff_mem.2 (h x)`.
-/
private theorem norm_le_of_pow {K : Type} [Field K] [NumberField K] (w : HeightOneSpectrum (𝓞 K)) {q : ℕ}
    (hq : 1 < q) (h : ∀ x : 𝓞 K, x ^ q - x ∈ w.asIdeal) : normV w ≤ q := by
  classical
  have := w.isMaximal
  letI : Field (𝓞 K ⧸ w.asIdeal) := Ideal.Quotient.field _
  have : Finite (𝓞 K ⧸ w.asIdeal) := Ideal.finiteQuotientOfFreeOfNeBot _ w.ne_bot
  letI := Fintype.ofFinite (𝓞 K ⧸ w.asIdeal)
  have e : normV w = (Finset.univ : Finset (𝓞 K ⧸ w.asIdeal)).card := Nat.card_eq_fintype_card
  rw [e, ← FiniteField.X_pow_card_sub_X_natDegree_eq (𝓞 K ⧸ w.asIdeal) hq]
  refine Polynomial.card_le_degree_of_subset_roots fun y _ => ?_
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective y
  rw [Polynomial.mem_roots (FiniteField.X_pow_card_sub_X_ne_zero _ hq)]
  simpa using Ideal.Quotient.eq_zero_iff_mem.2 (h x)

/- English proof (translation)
Establish `: IsGalois F Ω` using `IsAlgClosure.isGalois F Ω`. Take `⟨N, hN⟩` from `ProfiniteGrp.exist_openNormalSubgroup_sub_open_nhds_of_one ht h1`. Use `haveI : Finite (G F Ω ⧸ N.toSubgroup) := Subgroup.quotient_finite_of_isOpen _ N.isOpen`. Take `⟨ζ, hζ⟩` from `GlobalTheory.exists_fixed_dvd_deg F Ω A w h (Nat.card (G F Ω ⧸ N.toSubgroup)) Nat.card_pos`. Establish `hst : IsOpen (MulAction.stabilizer (G F Ω) ζ : Set (G F Ω))` using `stabilizer_isOpen_of_isIntegral ζ`.

Take `⟨N', hN'⟩` from `ProfiniteGrp.exist_openNormalSubgroup_sub_open_nhds_of_one hst (Subgroup.one_mem _)`. Set `M : Subgroup (G F Ω)` to `N.toSubgroup ⊓ N'.toSubgroup`. Establish `hM : IsOpen (M : Set (G F Ω))` using `N.isOpen.inter N'.isOpen`. Use `⟨Subgroup.zpowers (σ : G F Ω) ⊔ M, Subgroup.isOpen_mono le_sup_right hM, Subgroup.mem_sup_left (Subgroup.mem_zpowers _), fun s hs hd => ?_⟩` and prove the remaining obligations. Take `⟨_, ⟨k, rfl⟩, n, hn, e⟩` from `Subgroup.mem_sup_of_normal_right.1 hs`.

Establish `e1 : n = ((σ ^ (-k) * s : Weil h) : G F Ω)`. Rewrite using `[Subgroup.coe_mul, Subgroup.coe_zpow, ← e, zpow_neg, inv_mul_cancel_left]`. Take `⟨j, hj⟩` from `hζ (σ ^ (-k) * s) (e1 ▸ hN' hn.2)`. Establish `hk : k = Nat.card (G F Ω ⧸ N.toSubgroup) * j`. Rewrite using `[← hj, deg_mul, deg_zpow, hσ, hd]`.

Expand and normalize the polynomial expressions, which then agree. Use `hN ?_` and prove the remaining obligations. Rewrite using `[← e]`. Use `N.toSubgroup.mul_mem ?_ hn.1` and prove the remaining obligations. Use `show (σ : G F Ω) ^ k ∈ N.toSubgroup`.

Rewrite using `[hk, zpow_mul, zpow_natCast]`. Conclude with `Subgroup.zpow_mem _ (Subgroup.pow_index_mem _ _) _`.
-/
private theorem open_sub {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω]
    {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 F)} (h : IsPlaceOver A w) (σ : Weil h) (hσ : deg σ = -1)
    (t : Set (G F Ω)) (ht : IsOpen t) (h1 : (1 : G F Ω) ∈ t) :
    ∃ U : Subgroup (G F Ω), IsOpen (U : Set (G F Ω)) ∧ (σ : G F Ω) ∈ U ∧
      ∀ s : Weil h, (s : G F Ω) ∈ U → deg s = 0 → (s : G F Ω) ∈ t := by
  have : IsGalois F Ω := IsAlgClosure.isGalois F Ω
  obtain ⟨N, hN⟩ := ProfiniteGrp.exist_openNormalSubgroup_sub_open_nhds_of_one ht h1
  haveI : Finite (G F Ω ⧸ N.toSubgroup) := Subgroup.quotient_finite_of_isOpen _ N.isOpen
  obtain ⟨ζ, hζ⟩ := GlobalTheory.exists_fixed_dvd_deg F Ω A w h (Nat.card (G F Ω ⧸ N.toSubgroup)) Nat.card_pos
  have hst : IsOpen (MulAction.stabilizer (G F Ω) ζ : Set (G F Ω)) := stabilizer_isOpen_of_isIntegral ζ
  obtain ⟨N', hN'⟩ := ProfiniteGrp.exist_openNormalSubgroup_sub_open_nhds_of_one hst (Subgroup.one_mem _)
  let M : Subgroup (G F Ω) := N.toSubgroup ⊓ N'.toSubgroup
  have hM : IsOpen (M : Set (G F Ω)) := N.isOpen.inter N'.isOpen
  refine ⟨Subgroup.zpowers (σ : G F Ω) ⊔ M, Subgroup.isOpen_mono le_sup_right hM,
    Subgroup.mem_sup_left (Subgroup.mem_zpowers _), fun s hs hd => ?_⟩
  obtain ⟨_, ⟨k, rfl⟩, n, hn, e⟩ := Subgroup.mem_sup_of_normal_right.1 hs
  have e1 : n = ((σ ^ (-k) * s : Weil h) : G F Ω) := by
    rw [Subgroup.coe_mul, Subgroup.coe_zpow, ← e, zpow_neg, inv_mul_cancel_left]
  obtain ⟨j, hj⟩ := hζ (σ ^ (-k) * s) (e1 ▸ hN' hn.2)
  have hk : k = Nat.card (G F Ω ⧸ N.toSubgroup) * j := by
    rw [← hj, deg_mul, deg_zpow, hσ, hd]; ring
  refine hN ?_
  rw [← e]
  refine N.toSubgroup.mul_mem ?_ hn.1
  show (σ : G F Ω) ^ k ∈ N.toSubgroup
  rw [hk, zpow_mul, zpow_natCast]
  exact Subgroup.zpow_mem _ (Subgroup.pow_index_mem _ _) _

/- English proof (translation)
Introduce `_ F Ω _ _ _ _ _ A w h a ha σ hσ V hV`. Establish `: IsGalois F Ω` using `IsAlgClosure.isGalois F Ω`. Take `⟨V', hVV, hV', h1⟩` from `mem_nhds_iff.1 hV`. Take `⟨t, ht, hts⟩` from `isOpen_induced_iff.mp (hV'.preimage ha.cont)`. Establish `h1t : (1 : G F Ω) ∈ t`.

Establish `: (1 : Ine (F` using `F) A) ∈ (fun σ : Ine (F := F) A => a (ineIncl h σ)) ⁻¹' V' := by simpa using h1`. Rewrite `this` using `[← hts]`. Conclude with `this`. Take `⟨U, hU, hσU, H⟩` from `open_sub h σ hσ t ht h1t`. Set `F'` to `IntermediateField.fixedField U`.

Establish `hfix : F'.fixingSubgroup = U` using `InfiniteGalois.fixingSubgroup_fixedField ⟨U, U.isClosed_of_isOpen hU⟩`. Use `haveI : FiniteDimensional F F' := by`. Rewrite using `[← InfiniteGalois.isOpen_iff_finite, hfix]`. Conclude with `hU`. Use `haveI nf : NumberField F' := NumberField.of_module_finite F F'`.

Use `haveI ac : IsAlgClosure F' Ω := ⟨IsAlgClosure.isAlgClosed F, Algebra.IsAlgebraic.tower_top (K := F) _⟩`. Take `⟨w', h', hle⟩` from `place_above (L := F') h`. Establish `hact : ActsAs A (normV w) (σ : G F Ω) 0 1` using `actsAs_of_deg (by simpa using hσ)`. Establish `hσF : ∀ x : F', (σ : G F Ω) (x : Ω) = x` using `fun x => x.2 ⟨_, hσU⟩`. Establish `hq : normV w' = normV w`.

Use `le_antisymm (norm_le_of_pow w' (one_lt_normV w) fun x => ?_) hle` and prove the remaining obligations. Rewrite using `[← h']`. Establish `h3` using `hact.2 _ ((A.valuation_le_one_iff _).2 (val_int_le A x))`. Rewrite `h3` using `[show (σ : G F Ω) (algebraMap F' Ω x) = algebraMap F' Ω x from hσF x]`. Simplify using `using h3`.

Use `⟨F', nf, ac, w', h', ?_, fun s s' hd hs => ?_⟩` and prove the remaining obligations. Set `σ' : G F' Ω` to `{ (σ : G F Ω) with commutes' := hσF }`. Use `⟨⟨σ', 0, 1, ?_, ?_⟩, fun z => rfl⟩` and prove the remaining obligations. Conclude with `hact.1`. Rewrite using `[hq]`.

Conclude with `hact.2`. Establish `hI` using `deg_eq_zero_iff.1 hd`. Establish `hI' : (s : G F Ω) ∈ Ine (F` using `F) A := ⟨Weil_le_Dec h s.2, fun x hx => by`. Rewrite using `[hs]`. Conclude with `hI.2 x hx⟩`.

Establish `hsU : (s : G F Ω) ∈ U`. Rewrite using `[← hfix, IntermediateField.mem_fixingSubgroup_iff]`. Introduce `x hx`. Rewrite using `[hs]`. Conclude with `(s' : G F' Ω).commutes ⟨x, hx⟩`.

Establish `h4 : (⟨s, hI'⟩ : Ine (F` using `F) A) ∈ Subtype.val ⁻¹' t := H s hsU (deg_eq_zero_iff.2 hI')`. Rewrite `h4` using `[hts]`. Conclude with `hVV h4`.
-/
theorem UpperTheory.Lit.CharWD.exField :
    GlobalArtinReciprocity → ExField := by
  intro _ F Ω _ _ _ _ _ A w h a ha σ hσ V hV
  have : IsGalois F Ω := IsAlgClosure.isGalois F Ω
  obtain ⟨V', hVV, hV', h1⟩ := mem_nhds_iff.1 hV
  obtain ⟨t, ht, hts⟩ := isOpen_induced_iff.mp (hV'.preimage ha.cont)
  have h1t : (1 : G F Ω) ∈ t := by
    have : (1 : Ine (F := F) A) ∈ (fun σ : Ine (F := F) A => a (ineIncl h σ)) ⁻¹' V' := by simpa using h1
    rw [← hts] at this
    exact this
  obtain ⟨U, hU, hσU, H⟩ := open_sub h σ hσ t ht h1t
  let F' := IntermediateField.fixedField U
  have hfix : F'.fixingSubgroup = U := InfiniteGalois.fixingSubgroup_fixedField ⟨U, U.isClosed_of_isOpen hU⟩
  haveI : FiniteDimensional F F' := by
    rw [← InfiniteGalois.isOpen_iff_finite, hfix]
    exact hU
  haveI nf : NumberField F' := NumberField.of_module_finite F F'
  haveI ac : IsAlgClosure F' Ω := ⟨IsAlgClosure.isAlgClosed F, Algebra.IsAlgebraic.tower_top (K := F) _⟩
  obtain ⟨w', h', hle⟩ := place_above (L := F') h
  have hact : ActsAs A (normV w) (σ : G F Ω) 0 1 := actsAs_of_deg (by simpa using hσ)
  have hσF : ∀ x : F', (σ : G F Ω) (x : Ω) = x := fun x => x.2 ⟨_, hσU⟩
  have hq : normV w' = normV w := by
    refine le_antisymm (norm_le_of_pow w' (one_lt_normV w) fun x => ?_) hle
    rw [← h']
    have h3 := hact.2 _ ((A.valuation_le_one_iff _).2 (val_int_le A x))
    rw [show (σ : G F Ω) (algebraMap F' Ω x) = algebraMap F' Ω x from hσF x] at h3
    simpa using h3
  refine ⟨F', nf, ac, w', h', ?_, fun s s' hd hs => ?_⟩
  · let σ' : G F' Ω := { (σ : G F Ω) with commutes' := hσF }
    refine ⟨⟨σ', 0, 1, ?_, ?_⟩, fun z => rfl⟩
    · exact hact.1
    · rw [hq]; exact hact.2
  · have hI := deg_eq_zero_iff.1 hd
    have hI' : (s : G F Ω) ∈ Ine (F := F) A := ⟨Weil_le_Dec h s.2, fun x hx => by
      rw [hs]; exact hI.2 x hx⟩
    have hsU : (s : G F Ω) ∈ U := by
      rw [← hfix, IntermediateField.mem_fixingSubgroup_iff]
      intro x hx
      rw [hs]
      exact (s' : G F' Ω).commutes ⟨x, hx⟩
    have h4 : (⟨s, hI'⟩ : Ine (F := F) A) ∈ Subtype.val ⁻¹' t := H s hsU (deg_eq_zero_iff.2 hI')
    rw [hts] at h4
    exact hVV h4

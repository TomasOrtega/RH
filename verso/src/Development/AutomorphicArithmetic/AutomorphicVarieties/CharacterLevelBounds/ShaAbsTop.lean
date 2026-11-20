import Development.AutomorphicArithmetic.AutomorphicVarieties.CharacterLevelBounds.ShaFamMono
import Development.AutomorphicArithmetic.AutomorphicVarieties.PartsSign
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.GaloisCohomologyLength.ShaInfl
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.GaloisCohomologyLength.InfUnram
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.Places
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.KerResSmul
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.DvrFacts

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.Base UpperTheory.V.Chr

/- English proof (translation)
Unfold `resH1 H1 at *`. Proceed by induction on `x using Submodule.Quotient.induction_on with`. Consider the case `H z`. Simplify using `only [Submodule.mapQ_apply]`. Both sides reduce to the same expression.
-/
private theorem resH1_comp {R : Type} [CommRing R] {G H K : Type} [Group G] [TopologicalSpace G] [Group H] [TopologicalSpace H] [Group K] [TopologicalSpace K] {M : Type} [AddCommGroup M] [Module R M] [TopologicalSpace M] [IsTopologicalAddGroup M] [ContinuousConstSMul R M] (ρ : Representation R G M) (φ : H →* G) (ψ : K →* H) (hφ : Continuous φ) (hψ : Continuous ψ) (x : H1 ρ) :
    resH1 ρ (φ.comp ψ) (hφ.comp hψ) x = resH1 (ρ.comp φ) ψ hψ (resH1 ρ φ hφ x) := by
  unfold resH1 H1 at *
  induction x using Submodule.Quotient.induction_on with
  | H z =>
    simp only [Submodule.mapQ_apply]
    rfl

/- English proof (translation)
Unfold `resU pairH1DecompositionMap resH1 H1U H1 at *`. Proceed by induction on `x using Submodule.Quotient.induction_on with`. Consider the case `H z`. Simplify using `only [Submodule.mapQ_apply]`. Both sides reduce to the same expression.
-/
private theorem resU_eq_resH1_inclusion {R G M : Type} [CommRing R] [Group G] [TopologicalSpace G] [AddCommGroup M] [Module R M] [TopologicalSpace M] [IsTopologicalAddGroup M] [ContinuousConstSMul R M] (ρ : Representation R G M) (U' U : Subgroup G) (h : U' ≤ U) (hc : Continuous (Subgroup.inclusion h)) (x : H1U ρ U) :
    resU ρ h x = resH1 (ρ.comp U.subtype) (Subgroup.inclusion h) hc x := by
  unfold resU pairH1DecompositionMap resH1 H1U H1 at *
  induction x using Submodule.Quotient.induction_on with
  | H z =>
    simp only [Submodule.mapQ_apply]
    rfl

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Rewrite using `[injective_iff_map_eq_zero]`. Introduce `x hx`. Unfold `resH1 H1 at *`. Proceed by induction on `x using Submodule.Quotient.induction_on with`.

Consider the case `H z`. Rewrite `hx` using `[Submodule.mapQ_apply, Submodule.Quotient.mk_eq_zero, Submodule.mem_comap]`. Rewrite using `[Submodule.Quotient.mk_eq_zero, Submodule.mem_comap]`. Take `⟨m, hm⟩` from `hx`. Use `⟨m, ?_⟩` and prove the remaining obligations.

Use function extensionality and compare the values at `g`. Establish `hg` using `congrFun hm ⟨g, Subgroup.mem_top g⟩`. Simplify `hg` using `[d0, restrictCocycles1]`. Introduce `y`. Unfold `resH1 H1 at *`.

Proceed by induction on `y using Submodule.Quotient.induction_on with`. Consider the case `H w`. Establish `hw` using `w.2`. Unfold `Z1 at hw`. Take `⟨hwc, hwz⟩` from `hw`.

Establish `hz : (fun g : G => w.1 ⟨g, Subgroup.mem_top g⟩) ∈ Z1 ρ`. Unfold `Z1`. Use `⟨hwc.comp (Continuous.subtype_mk continuous_id _), ?_⟩` and prove the remaining obligations. Introduce `g h`. Conclude with `hwz ⟨g, Subgroup.mem_top g⟩ ⟨h, Subgroup.mem_top h⟩`.

Use `⟨Submodule.Quotient.mk ⟨_, hz⟩, ?_⟩` and prove the remaining obligations. Rewrite using `[Submodule.mapQ_apply]`. Both sides reduce to the same expression.
-/
private theorem resH1_subtype_whole_bijective {R G M : Type} [CommRing R] [Group G] [TopologicalSpace G] [AddCommGroup M] [Module R M] [TopologicalSpace M] [IsTopologicalAddGroup M] [ContinuousConstSMul R M] (ρ : Representation R G M) (hc : Continuous (⊤ : Subgroup G).subtype) :
    Function.Bijective (resH1 ρ (⊤ : Subgroup G).subtype hc) := by
  constructor
  · rw [injective_iff_map_eq_zero]
    intro x hx
    unfold resH1 H1 at *
    induction x using Submodule.Quotient.induction_on with
    | H z =>
      rw [Submodule.mapQ_apply, Submodule.Quotient.mk_eq_zero, Submodule.mem_comap] at hx
      rw [Submodule.Quotient.mk_eq_zero, Submodule.mem_comap]
      obtain ⟨m, hm⟩ := hx
      refine ⟨m, ?_⟩
      funext g
      have hg := congrFun hm ⟨g, Subgroup.mem_top g⟩
      simpa [d0, restrictCocycles1] using hg
  · intro y
    unfold resH1 H1 at *
    induction y using Submodule.Quotient.induction_on with
    | H w =>
      have hw := w.2
      unfold Z1 at hw
      obtain ⟨hwc, hwz⟩ := hw
      have hz : (fun g : G => w.1 ⟨g, Subgroup.mem_top g⟩) ∈ Z1 ρ := by
        unfold Z1
        refine ⟨hwc.comp (Continuous.subtype_mk continuous_id _), ?_⟩
        intro g h
        exact hwz ⟨g, Subgroup.mem_top g⟩ ⟨h, Subgroup.mem_top h⟩
      refine ⟨Submodule.Quotient.mk ⟨_, hz⟩, ?_⟩
      rw [Submodule.mapQ_apply]
      rfl

/- English proof (translation)
Unfold `H1U H1 at *`. Proceed by induction on `x using Submodule.Quotient.induction_on with`. Consider the case `H z`. Rewrite using `[Submodule.Quotient.mk_eq_zero, Submodule.mem_comap]`. Establish `hz0` using `z.2`.

Unfold `Z1 at hz0`. Take `⟨-, hz⟩` from `hz0`. Use `⟨0, ?_⟩` and prove the remaining obligations. Use function extensionality and compare the values at `g`. Establish `hg : g = 1` using `Subsingleton.elim _ _`.

Establish `h1` using `hz 1 1`. Simplify using `only [mul_one, map_one, Module.End.one_apply, left_eq_add] at h1`. Substitute `hg` using the available equality. Simplify using `[d0, h1]`.
-/
private theorem H1U_bot_eq_zero {R G M : Type} [CommRing R] [Group G] [TopologicalSpace G] [AddCommGroup M] [Module R M] [TopologicalSpace M] [IsTopologicalAddGroup M] [ContinuousConstSMul R M] (ρ : Representation R G M) (x : H1U ρ ⊥) : x = 0 := by
  unfold H1U H1 at *
  induction x using Submodule.Quotient.induction_on with
  | H z =>
    rw [Submodule.Quotient.mk_eq_zero, Submodule.mem_comap]
    have hz0 := z.2
    unfold Z1 at hz0
    obtain ⟨-, hz⟩ := hz0
    refine ⟨0, ?_⟩
    funext g
    have hg : g = 1 := Subsingleton.elim _ _
    have h1 := hz 1 1
    simp only [mul_one, map_one, Module.End.one_apply, left_eq_add] at h1
    subst hg
    simp [d0, h1]

/- English proof (translation)
Unfold `H1U H1 at *`. Proceed by induction on `x using Submodule.Quotient.induction_on with`. Consider the case `H z`. Rewrite using `[Submodule.Quotient.mk_eq_zero, Submodule.mem_comap]`. Establish `hz0` using `z.2`.

Unfold `Z1 at hz0`. Take `⟨-, hz⟩` from `hz0`. Use `set cc : Subgroup.zpowers c := ⟨c, Subgroup.mem_zpowers c⟩ with hcc_def`. Establish `hcc : cc * cc = 1` using `Subtype.ext hc`. Establish `h1 : z.1 1 = 0`.

Use `hz 1 1` as an intermediate fact. Simplify using `using this`. Establish `h2 : ρ c (z.1 cc) = - z.1 cc`. Use `hz cc cc` as an intermediate fact. Rewrite `this` using `[hcc, h1]`.

Conclude with `(neg_eq_of_add_eq_zero_right this.symm).symm`. Use `⟨-(u • z.1 cc), ?_⟩` and prove the remaining obligations. Use function extensionality and compare the values at `g`. Establish `hg : g = 1 ∨ g = cc`. Take `⟨k, hk⟩` from `Subgroup.mem_zpowers_iff.1 g.2`.

Establish `hc2 : c ^ (2 : ℤ) = 1` using `by rw [zpow_two, hc]`. Rewrite `hk` using `[zpow_eq_zpow_emod k hc2]`. Break down `Int.emod_two_eq k with h | h` into its components or cases. Use `left`. Apply `Subtype.ext` to reduce the goal to its premises.

Rewrite using `[← hk, h]`. Simplify using the standard rewrite rules. Use `right`. Apply `Subtype.ext` to reduce the goal to its premises. Rewrite using `[← hk, h]`.

Simplify using `[hcc_def]`. Break down `hg with rfl | rfl` into its components or cases. Simplify using `[d0, h1]`. Simplify using `[d0]`. Rewrite using `[show ((cc : G)) = c from rfl, h2, smul_neg, neg_neg, ← two_smul R (u • z.1 cc), smul_smul, hu, one_smul]`.
-/
private theorem H1U_zpowers_involution_eq_zero_of_two_unit {R G M : Type} [CommRing R] [Group G] [TopologicalSpace G] [AddCommGroup M] [Module R M] [TopologicalSpace M] [IsTopologicalAddGroup M] [ContinuousConstSMul R M] (ρ : Representation R G M) (c : G) (hc : c * c = 1) (u : R) (hu : 2 * u = 1) (x : H1U ρ (Subgroup.zpowers c)) : x = 0 := by
  unfold H1U H1 at *
  induction x using Submodule.Quotient.induction_on with
  | H z =>
    rw [Submodule.Quotient.mk_eq_zero, Submodule.mem_comap]
    have hz0 := z.2
    unfold Z1 at hz0
    obtain ⟨-, hz⟩ := hz0
    set cc : Subgroup.zpowers c := ⟨c, Subgroup.mem_zpowers c⟩ with hcc_def
    have hcc : cc * cc = 1 := Subtype.ext hc
    have h1 : z.1 1 = 0 := by
      have := hz 1 1
      simpa using this
    have h2 : ρ c (z.1 cc) = - z.1 cc := by
      have := hz cc cc
      rw [hcc, h1] at this
      exact (neg_eq_of_add_eq_zero_right this.symm).symm
    refine ⟨-(u • z.1 cc), ?_⟩
    funext g
    have hg : g = 1 ∨ g = cc := by
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 g.2
      have hc2 : c ^ (2 : ℤ) = 1 := by rw [zpow_two, hc]
      rw [zpow_eq_zpow_emod k hc2] at hk
      rcases Int.emod_two_eq k with h | h
      · left; apply Subtype.ext; rw [← hk, h]; simp
      · right; apply Subtype.ext; rw [← hk, h]; simp [hcc_def]
    rcases hg with rfl | rfl
    · simp [d0, h1]
    · simp [d0]
      rw [show ((cc : G)) = c from rfl, h2, smul_neg, neg_neg, ← two_smul R (u • z.1 cc), smul_smul, hu, one_smul]

/- English proof (translation)
Establish `h2 : IsUnit (2 : ℤ_[l])`. Rewrite using `[PadicInt.isUnit_iff]`. Use `le_antisymm (PadicInt.norm_le_one _) (not_lt.1 fun h => ?_)` and prove the remaining obligations. Establish `h' : ‖((2 : ℤ) : ℤ_[l])‖ < 1` using `by simpa using h`. Rewrite `h'` using `[PadicInt.norm_int_lt_one_iff_dvd]`.

Establish `: l ∣ 2` using `by exact_mod_cast h'`. Conclude with `hl ((Nat.prime_dvd_prime_iff_eq (Fact.out) Nat.prime_two).1 this)`. Take `⟨u, hu⟩` from `(h2.map (algebraMap ℤ_[l] O)).exists_right_inv`. Rewrite `hu` using `[map_ofNat]`. Conclude with `⟨u, hu⟩`.
-/
private theorem exists_half_of_padicInt_algebra_of_ne_two (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O] [Algebra ℤ_[l] O] (hl : l ≠ 2) : ∃ u : O, 2 * u = 1 := by
  have h2 : IsUnit (2 : ℤ_[l]) := by
    rw [PadicInt.isUnit_iff]
    refine le_antisymm (PadicInt.norm_le_one _) (not_lt.1 fun h => ?_)
    have h' : ‖((2 : ℤ) : ℤ_[l])‖ < 1 := by simpa using h
    rw [PadicInt.norm_int_lt_one_iff_dvd] at h'
    have : l ∣ 2 := by exact_mod_cast h'
    exact hl ((Nat.prime_dvd_prime_iff_eq (Fact.out) Nat.prime_two).1 this)
  obtain ⟨u, hu⟩ := (h2.map (algebraMap ℤ_[l] O)).exists_right_inv
  rw [map_ofNat] at hu
  exact ⟨u, hu⟩

/- English proof (translation)
Rewrite using `[resU_eq_resH1_inclusion ρ D ⊤ hD (continuous_subtype_val.subtype_mk _)]`. Conclude with `(resH1_comp ρ (⊤ : Subgroup G).subtype (Subgroup.inclusion hD) continuous_subtype_val _ x).symm`.
-/
private theorem resU_resH1_whole_eq_resH1_subtype {R G M : Type} [CommRing R] [Group G] [TopologicalSpace G] [AddCommGroup M] [Module R M] [TopologicalSpace M] [IsTopologicalAddGroup M] [ContinuousConstSMul R M] (ρ : Representation R G M) (D : Subgroup G) (hD : D ≤ ⊤) (x : H1 ρ) :
    resU ρ hD (resH1 ρ (⊤ : Subgroup G).subtype continuous_subtype_val x) = resH1 ρ D.subtype continuous_subtype_val x := by
  rw [resU_eq_resH1_inclusion ρ D ⊤ hD (continuous_subtype_val.subtype_mk _)]
  exact (resH1_comp ρ (⊤ : Subgroup G).subtype (Subgroup.inclusion hD) continuous_subtype_val _ x).symm

/- English proof (translation)
Unfold `IsPlaceOver at hA`. Establish `h` using `hA (n : 𝓞 k)`. Simplify using `only [map_natCast] at h`. Unfold `Above`. Conclude with `h`.
-/
private theorem valuation_natCast_lt_one_iff_mem_above {k Ω : Type} [Field k] [NumberField k] [Field Ω] [Algebra k Ω] (n : ℕ) (A : ValuationSubring Ω) (v : HeightOneSpectrum (𝓞 k)) (hA : IsPlaceOver A v) :
    A.valuation (n : Ω) < 1 ↔ v ∈ Above k n := by
  unfold IsPlaceOver at hA
  have h := hA (n : 𝓞 k)
  simp only [map_natCast] at h
  unfold Above
  exact h

/- English proof (translation)
Introduce `hlt`. Establish `h1 : (⊤ : ValuationSubring Ω).valuation x⁻¹ ≤ 1` using `(ValuationSubring.valuation_le_one_iff _ _).2 trivial`. Rewrite `h1` using `[map_inv₀]`. Establish `h0 : (⊤ : ValuationSubring Ω).valuation x ≠ 0` using `by simpa using hx`. Conclude with `absurd hlt (not_lt.2 ((inv_le_one₀ (zero_lt_iff.2 h0)).1 h1))`.
-/
private theorem not_valuation_lt_one_of_whole_valuationSubring {Ω : Type} [Field Ω] (x : Ω) (hx : x ≠ 0) : ¬ (⊤ : ValuationSubring Ω).valuation x < 1 := by
  intro hlt
  have h1 : (⊤ : ValuationSubring Ω).valuation x⁻¹ ≤ 1 := (ValuationSubring.valuation_le_one_iff _ _).2 trivial
  rw [map_inv₀] at h1
  have h0 : (⊤ : ValuationSubring Ω).valuation x ≠ 0 := by simpa using hx
  exact absurd hlt (not_lt.2 ((inv_le_one₀ (zero_lt_iff.2 h0)).1 h1))

/- English proof (translation)
Unfold `LocSel shaFam UpperTheory.V.LDataCardLeFinrank.ShaAbs`. Simplify using `only [Submodule.mem_iInf, Submodule.mem_inf, LinearMap.mem_ker, resU_resH1_whole_eq_resH1_subtype]`. Establish `hcongr : ∀ D D' : Subgroup (G k Ω), D = D' → (resH1 ρ D.subtype continuous_subtype_val x = 0 ↔ resH1 ρ D'.subtype continuous_subtype_val x = 0)`. Introduce and unpack `D D' rfl`. Both sides reduce to the same expression.

Establish `hbot : ∀ D : Subgroup (G k Ω), D = ⊥ → resH1 ρ D.subtype continuous_subtype_val x = 0`. Introduce and unpack `D rfl`. Conclude with `H1U_bot_eq_zero ρ _`. Establish `hine : ∀ A : ValuationSubring Ω, resH1 ρ (Dec A).subtype continuous_subtype_val x = 0 → resH1 ρ (Ine (F` using `k) A).subtype continuous_subtype_val x = 0 := by`. Introduce `A h`.

Establish `hle : Ine (F` using `k) A ≤ Dec A := fun g hg => hg.1`. Use `resH1_comp ρ (Dec A).subtype (Subgroup.inclusion hle) continuous_subtype_val (continuous_subtype_val.subtype_mk _) x` as an intermediate fact. Rewrite `this` using `[h, map_zero]`. Conclude with `this`. Establish `hn' : ((n : Ω)) ≠ 0`.

Establish `h0 : algebraMap k Ω (n : k) ≠ 0` using `(map_ne_zero _).2 (Nat.cast_ne_zero.2 hn)`. Simplify using `using h0`. Prove the components needed by the constructor for the conclusion. Introduce `h`. Use `⟨fun v hv A hA => ?_, fun v hv A hA => ?_⟩` and prove the remaining obligations.

Conclude with `(hcongr _ _ (top_inf_eq _)).1 (h (Dec A) (Or.inl ⟨A, (valuation_natCast_lt_one_iff_mem_above n A v hA).2 hv, rfl⟩))`. Conclude with `(hcongr _ _ (top_inf_eq _)).1 (h (Ine (F := k) A) (Or.inr ⟨A, rfl⟩))`. Introduce and unpack `⟨h1, h2⟩ D (⟨A, hA, rfl⟩ | ⟨A, rfl⟩)`. Use `(hcongr _ _ (top_inf_eq _)).2 ?_` and prove the remaining obligations. Establish `hAt : A ≠ ⊤`.

Introduce and unpack `rfl`. Conclude with `not_valuation_lt_one_of_whole_valuationSubring _ hn' hA`. Take `⟨v, hv⟩` from `(places k Ω 2 A).1 hAt`. Conclude with `h1 v ((valuation_natCast_lt_one_iff_mem_above n A v hv).1 hA) A hv`. Use `(hcongr _ _ (top_inf_eq _)).2 ?_` and prove the remaining obligations.

Distinguish the cases in `hAt : A = ⊤`. Conclude with `hbot _ ((places k Ω 2 A).2.1 hAt).1`. Take `⟨v, hv⟩` from `(places k Ω 2 A).1 hAt`. Distinguish the cases in `hvn : v ∈ Above k n`. Conclude with `hine A (h1 v hvn A hv)`.

Conclude with `h2 v hvn A hv`.
-/
private theorem resH1_whole_mem_locSel_shaFam_iff_mem_shaAbs (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω] (O M : Type) [CommRing O] [AddCommGroup M] [Module O M] [TopologicalSpace M] [IsTopologicalAddGroup M] [ContinuousConstSMul O M] (ρ : Representation O (G k Ω) M) (n : ℕ) (hn : n ≠ 0) (x : H1 ρ) :
    resH1 ρ (⊤ : Subgroup (G k Ω)).subtype continuous_subtype_val x ∈ LocSel ρ ⊤ (shaFam k Ω n) ↔ x ∈ UpperTheory.V.LDataCardLeFinrank.ShaAbs ρ (Above k n) := by
  unfold LocSel shaFam UpperTheory.V.LDataCardLeFinrank.ShaAbs
  simp only [Submodule.mem_iInf, Submodule.mem_inf, LinearMap.mem_ker, resU_resH1_whole_eq_resH1_subtype]
  have hcongr : ∀ D D' : Subgroup (G k Ω), D = D' →
      (resH1 ρ D.subtype continuous_subtype_val x = 0 ↔ resH1 ρ D'.subtype continuous_subtype_val x = 0) := by
    rintro D D' rfl
    rfl
  have hbot : ∀ D : Subgroup (G k Ω), D = ⊥ → resH1 ρ D.subtype continuous_subtype_val x = 0 := by
    rintro D rfl
    exact H1U_bot_eq_zero ρ _
  have hine : ∀ A : ValuationSubring Ω, resH1 ρ (Dec A).subtype continuous_subtype_val x = 0 →
      resH1 ρ (Ine (F := k) A).subtype continuous_subtype_val x = 0 := by
    intro A h
    have hle : Ine (F := k) A ≤ Dec A := fun g hg => hg.1
    have := resH1_comp ρ (Dec A).subtype (Subgroup.inclusion hle) continuous_subtype_val (continuous_subtype_val.subtype_mk _) x
    rw [h, map_zero] at this
    exact this
  have hn' : ((n : Ω)) ≠ 0 := by
    have h0 : algebraMap k Ω (n : k) ≠ 0 := (map_ne_zero _).2 (Nat.cast_ne_zero.2 hn)
    simpa using h0
  constructor
  · intro h
    refine ⟨fun v hv A hA => ?_, fun v hv A hA => ?_⟩
    · exact (hcongr _ _ (top_inf_eq _)).1 (h (Dec A) (Or.inl ⟨A, (valuation_natCast_lt_one_iff_mem_above n A v hA).2 hv, rfl⟩))
    · exact (hcongr _ _ (top_inf_eq _)).1 (h (Ine (F := k) A) (Or.inr ⟨A, rfl⟩))
  · rintro ⟨h1, h2⟩ D (⟨A, hA, rfl⟩ | ⟨A, rfl⟩)
    · refine (hcongr _ _ (top_inf_eq _)).2 ?_
      have hAt : A ≠ ⊤ := by
        rintro rfl
        exact not_valuation_lt_one_of_whole_valuationSubring _ hn' hA
      obtain ⟨v, hv⟩ := (places k Ω 2 A).1 hAt
      exact h1 v ((valuation_natCast_lt_one_iff_mem_above n A v hv).1 hA) A hv
    · refine (hcongr _ _ (top_inf_eq _)).2 ?_
      by_cases hAt : A = ⊤
      · exact hbot _ ((places k Ω 2 A).2.1 hAt).1
      · obtain ⟨v, hv⟩ := (places k Ω 2 A).1 hAt
        by_cases hvn : v ∈ Above k n
        · exact hine A (h1 v hvn A hv)
        · exact h2 v hvn A hv

/- English proof (translation)
Set `E` to `LinearEquiv.ofBijective (resH1 ρ (⊤ : Subgroup (G k Ω)).subtype continuous_subtype_val) (resH1_subtype_whole_bijective ρ _)`. Establish `hE : LocSel ρ ⊤ (shaFam k Ω n) = (UpperTheory.V.LDataCardLeFinrank.ShaAbs ρ (Above k n)).map (E : H1 ρ →ₗ[O] H1U ρ ⊤)`. Use extensionality with `y`. Take `⟨x, rfl⟩` from `E.surjective y`. Prove the components needed by the constructor for the conclusion.

Introduce `hy`. Conclude with `⟨x, (resH1_whole_mem_locSel_shaFam_iff_mem_shaAbs k Ω O M ρ n hn x).1 hy, rfl⟩`. Introduce and unpack `⟨x', hx', hxx⟩`. Establish `hx : x' = x` using `E.injective hxx`. Substitute `hx` using the available equality.

Conclude with `(resH1_whole_mem_locSel_shaFam_iff_mem_shaAbs k Ω O M ρ n hn x').2 hx'`. Rewrite using `[hE]`. Conclude with `((Submodule.equivMapOfInjective _ E.injective _).length_eq).symm`.
-/
private theorem length_locSel_whole_shaFam_eq_length_shaAbs (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω] (O M : Type) [CommRing O] [AddCommGroup M] [Module O M] [TopologicalSpace M] [IsTopologicalAddGroup M] [ContinuousConstSMul O M] (ρ : Representation O (G k Ω) M) (n : ℕ) (hn : n ≠ 0) :
    Module.length O (LocSel ρ ⊤ (shaFam k Ω n)) = Module.length O (UpperTheory.V.LDataCardLeFinrank.ShaAbs ρ (Above k n)) := by
  let E := LinearEquiv.ofBijective (resH1 ρ (⊤ : Subgroup (G k Ω)).subtype continuous_subtype_val) (resH1_subtype_whole_bijective ρ _)
  have hE : LocSel ρ ⊤ (shaFam k Ω n) = (UpperTheory.V.LDataCardLeFinrank.ShaAbs ρ (Above k n)).map (E : H1 ρ →ₗ[O] H1U ρ ⊤) := by
    ext y
    obtain ⟨x, rfl⟩ := E.surjective y
    constructor
    · intro hy
      exact ⟨x, (resH1_whole_mem_locSel_shaFam_iff_mem_shaAbs k Ω O M ρ n hn x).1 hy, rfl⟩
    · rintro ⟨x', hx', hxx⟩
      have hx : x' = x := E.injective hxx
      subst hx
      exact (resH1_whole_mem_locSel_shaFam_iff_mem_shaAbs k Ω O M ρ n hn x').2 hx'
  rw [hE]
  exact ((Submodule.equivMapOfInjective _ E.injective _).length_eq).symm

/- English proof (translation)
Introduce `k Ω _ _ _ _ _ l _ O _ _ _ _ _ e ψ`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Introduce `n S A hn hS hA θ hθ hc`. Take `⟨hinj, -⟩` from `UpperTheory.V.LDataCardLeFinrank.infUnram k Ω (S : Set (HeightOneSpectrum (𝓞 k))) O (QO l O) (twist₂ l θ) hc`. Establish `hinfl` using `UpperTheory.V.LDataCardLeFinrank.shaInfl k Ω S A hA O (QO l O) (twist₂ l θ) hc`.

Rewrite using `[(Submodule.equivMapOfInjective _ hinj _).length_eq, hinfl]`. Establish `hrep : (twist₂ l θ).comp (toGS Ω (S : Set (HeightOneSpectrum (𝓞 k)))) = twist₂ l (ψ⁻¹ * chiO k Ω l O ^ (-(e : ℤ)))` using `by show twist₂ l (θ.comp _) = _`. Rewrite using `[hθ]`. Unfold `Psi`. Rewrite using `[mul_inv_rev, zpow_neg]`.

Rewrite using `[hrep, hS]`. Unfold `VS ShaU rho`. Conclude with `(length_locSel_whole_shaFam_eq_length_shaAbs k Ω O (QO l O) _ n hn).symm`. Introduce `hl c hc`. Take `⟨u, hu⟩` from `exists_half_of_padicInt_algebra_of_ne_two l O hl`.

Conclude with `⟨fun x y => (H1U_zpowers_involution_eq_zero_of_two_unit _ c hc u hu x).trans (H1U_zpowers_involution_eq_zero_of_two_unit _ c hc u hu y).symm⟩`.
-/
theorem UpperTheory.V.Chr.litV :
    ∀ (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω] (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Algebra ℤ_[l] O] [Module.Finite ℤ_[l] O] (e : ℕ) (ψ : G k Ω →* Oˣ),
          (∀ (n : ℕ) (S : Finset (HeightOneSpectrum (𝓞 k))) (A : S → ValuationSubring Ω), n ≠ 0 → (S : Set (HeightOneSpectrum (𝓞 k))) = Above k n →
            (∀ v, IsPlaceOver (A v) v.1) → ∀ θ : GS Ω (S : Set (HeightOneSpectrum (𝓞 k))) →* Oˣ, θ.comp (toGS Ω _) = (Psi l e ψ)⁻¹ →
            ContAction (twist₂ l θ) → Module.length O (Sha1 (twist₂ l θ) (locFam S A) (continuous_locFam S A)) = VS l n e ψ) ∧
          (l ≠ 2 → ∀ c : G k Ω, c * c = 1 → Subsingleton (H1U (rho l e ψ) (Subgroup.zpowers c))) := by
  intro k Ω _ _ _ _ _ l _ O _ _ _ _ _ e ψ
  refine ⟨?_, ?_⟩
  · intro n S A hn hS hA θ hθ hc
    obtain ⟨hinj, -⟩ := UpperTheory.V.LDataCardLeFinrank.infUnram k Ω (S : Set (HeightOneSpectrum (𝓞 k))) O (QO l O) (twist₂ l θ) hc
    have hinfl := UpperTheory.V.LDataCardLeFinrank.shaInfl k Ω S A hA O (QO l O) (twist₂ l θ) hc
    rw [(Submodule.equivMapOfInjective _ hinj _).length_eq, hinfl]
    have hrep : (twist₂ l θ).comp (toGS Ω (S : Set (HeightOneSpectrum (𝓞 k)))) = twist₂ l (ψ⁻¹ * chiO k Ω l O ^ (-(e : ℤ))) := by
      show twist₂ l (θ.comp _) = _
      rw [hθ]
      unfold Psi
      rw [mul_inv_rev, zpow_neg]
    rw [hrep, hS]
    unfold VS ShaU rho
    exact (length_locSel_whole_shaFam_eq_length_shaAbs k Ω O (QO l O) _ n hn).symm
  · intro hl c hc
    obtain ⟨u, hu⟩ := exists_half_of_padicInt_algebra_of_ne_two l O hl
    exact ⟨fun x y => (H1U_zpowers_involution_eq_zero_of_two_unit _ c hc u hu x).trans (H1U_zpowers_involution_eq_zero_of_two_unit _ c hc u hu y).symm⟩

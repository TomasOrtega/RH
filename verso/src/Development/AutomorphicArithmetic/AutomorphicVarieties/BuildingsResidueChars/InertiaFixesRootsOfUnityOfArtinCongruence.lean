import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.LocIsotypic
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.ConclusionAbsPow
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsPadicAlgClRingEquivComplexCompEqOfCountabl
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.CyclotomicCharEqLocPowOfLocalArtinUnit
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.NormLocPowSubOneLeOfValuationSubOneLe
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.FixesRootsOfUnityOfCyclotomicCharNearOne
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.InertiaFixesRootsOfUnityPrimeToResidueChar

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N ValuativeRel
open GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

/- English proof (translation)
Establish `hle : Cardinal.mk ℚ_[p] ≤ Cardinal.continuum`. Establish `h1 : Cardinal.mk ℚ_[p] ≤ Cardinal.mk (CauSeq ℚ (padicNorm p))` using `Cardinal.mk_quotient_le`. Establish `h2 : Cardinal.mk (CauSeq ℚ (padicNorm p)) ≤ Cardinal.mk (ℕ → ℚ)` using `Cardinal.mk_subtype_le _`. Use `h1.trans (h2.trans ?_)` and prove the remaining obligations. Rewrite using `[Cardinal.mk_arrow, Cardinal.mk_eq_aleph0 ℚ, Cardinal.mk_nat]`.

Simplify using the standard rewrite rules. Establish `hge : Cardinal.continuum ≤ Cardinal.mk ℚ_[p]`. Take `⟨f, -, -, hf⟩` from `Perfect.exists_nat_bool_injection (PerfectSpace.univ_perfect (α := ℚ_[p])) Set.univ_nonempty`. Use `Cardinal.mk_le_of_injective hf` as an intermediate fact. Simplify using `using this`.

Apply `le_antisymm` to reduce the goal to its premises. Use `Algebra.IsAlgebraic.cardinalMk_le_max ℚ_[p] (PadicAlgCl p)` as an intermediate fact. Use `this.trans ?_` and prove the remaining obligations. Conclude with `max_le hle Cardinal.aleph0_le_continuum`. Conclude with `hge.trans (Cardinal.mk_le_of_injective (algebraMap ℚ_[p] (PadicAlgCl p)).injective)`.
-/
private theorem UpperTheory.card_padicAlgCl_eq_continuum (p : ℕ) [Fact p.Prime] :
    Cardinal.mk (PadicAlgCl p) = Cardinal.continuum := by
  have hle : Cardinal.mk ℚ_[p] ≤ Cardinal.continuum := by
    have h1 : Cardinal.mk ℚ_[p] ≤ Cardinal.mk (CauSeq ℚ (padicNorm p)) := Cardinal.mk_quotient_le
    have h2 : Cardinal.mk (CauSeq ℚ (padicNorm p)) ≤ Cardinal.mk (ℕ → ℚ) := Cardinal.mk_subtype_le _
    refine h1.trans (h2.trans ?_)
    rw [Cardinal.mk_arrow, Cardinal.mk_eq_aleph0 ℚ, Cardinal.mk_nat]
    simp
  have hge : Cardinal.continuum ≤ Cardinal.mk ℚ_[p] := by
    obtain ⟨f, -, -, hf⟩ :=
      Perfect.exists_nat_bool_injection (PerfectSpace.univ_perfect (α := ℚ_[p])) Set.univ_nonempty
    have := Cardinal.mk_le_of_injective hf
    simpa using this
  apply le_antisymm
  · have := Algebra.IsAlgebraic.cardinalMk_le_max ℚ_[p] (PadicAlgCl p)
    refine this.trans ?_
    exact max_le hle Cardinal.aleph0_le_continuum
  · exact hge.trans (Cardinal.mk_le_of_injective (algebraMap ℚ_[p] (PadicAlgCl p)).injective)

/- English proof (translation)
Establish `hc` using `UpperTheory.card_padicAlgCl_eq_continuum p`. Take `⟨s, hs⟩` from `exists_isTranscendenceBasis ℚ (PadicAlgCl p)`. Take `⟨t, ht⟩` from `exists_isTranscendenceBasis ℚ ℂ`. Establish `hQ : Cardinal.mk ℚ ≤ Cardinal.aleph0` using `Cardinal.mk_le_aleph0`. Establish `h1` using `IsAlgClosed.cardinal_eq_cardinal_transcendence_basis_of_aleph0_lt _ hs hQ (by rw [hc]; exact Cardinal.aleph0_lt_continuum)`.

Establish `h2` using `IsAlgClosed.cardinal_eq_cardinal_transcendence_basis_of_aleph0_lt _ ht hQ (by rw [Cardinal.mk_complex]; exact Cardinal.aleph0_lt_continuum)`. Simplify using `only [Cardinal.lift_id] at h1 h2`. Establish `hst : Cardinal.mk s = Cardinal.mk t` using `by rw [← h1, ← h2, hc, Cardinal.mk_complex]`. Take `⟨e⟩` from `Cardinal.eq.mp hst`. Conclude with `⟨IsAlgClosed.equivOfTranscendenceBasis _ _ e hs ht⟩`.
-/
private theorem UpperTheory.nonempty_qbar_ringEquiv_complex (p : ℕ) [Fact p.Prime] : Nonempty (Qbar p ≃+* ℂ) := by
  have hc := UpperTheory.card_padicAlgCl_eq_continuum p
  obtain ⟨s, hs⟩ := exists_isTranscendenceBasis ℚ (PadicAlgCl p)
  obtain ⟨t, ht⟩ := exists_isTranscendenceBasis ℚ ℂ
  have hQ : Cardinal.mk ℚ ≤ Cardinal.aleph0 := Cardinal.mk_le_aleph0
  have h1 := IsAlgClosed.cardinal_eq_cardinal_transcendence_basis_of_aleph0_lt _ hs hQ
    (by rw [hc]; exact Cardinal.aleph0_lt_continuum)
  have h2 := IsAlgClosed.cardinal_eq_cardinal_transcendence_basis_of_aleph0_lt _ ht hQ
    (by rw [Cardinal.mk_complex]; exact Cardinal.aleph0_lt_continuum)
  simp only [Cardinal.lift_id] at h1 h2
  have hst : Cardinal.mk s = Cardinal.mk t := by rw [← h1, ← h2, hc, Cardinal.mk_complex]
  obtain ⟨e⟩ := Cardinal.eq.mp hst
  exact ⟨IsAlgClosed.equivOfTranscendenceBasis _ _ e hs ht⟩

/- English proof (translation)
Introduce `d`. Proceed by induction on `d using Nat.recOnPosPrimePosCoprime with`. Consider the case `prime_pow p n hp hn`. Introduce `_ H ζ hζ`. Conclude with `H p n hp dvd_rfl ζ hζ`.

Consider the case `zero`. Introduce `h`. Conclude with `absurd rfl h`. Consider the case `one`. Introduce `_ _ ζ hζ`.

Rewrite `hζ` using `[pow_one]`. Rewrite using `[hζ, map_one]`. Consider the case `coprime a b ha hb hab iha ihb`. Introduce `hd H ζ hζ`. Establish `ha0 : a ≠ 0` using `by omega`.

Establish `hb0 : b ≠ 0` using `by omega`. Establish `hA : g (ζ ^ b) = ζ ^ b` using `iha ha0 (fun p c hp hpc => H p c hp (hpc.trans (Dvd.intro _ rfl))) _ (by rw [← pow_mul, mul_comm, hζ])`. Establish `hB : g (ζ ^ a) = ζ ^ a` using `ihb hb0 (fun p c hp hpc => H p c hp (hpc.trans (Dvd.intro_left _ rfl))) _ (by rw [← pow_mul, hζ])`. Establish `hζ0 : ζ ≠ 0`. Introduce and unpack `rfl`.

Rewrite `hζ` using `[zero_pow (mul_ne_zero ha0 hb0)]`. Conclude with `zero_ne_one hζ`. Establish `hbez : (1 : ℤ) = a * Nat.gcdA a b + b * Nat.gcdB a b`. Use `Nat.gcd_eq_gcd_ab a b` as an intermediate fact. Rewrite `this` using `[Nat.Coprime.gcd_eq_one hab]`.

Conclude with `this` after adjusting the coercions. Establish `e : ζ = (ζ ^ a) ^ Nat.gcdA a b * (ζ ^ b) ^ Nat.gcdB a b`. Rewrite using `[← zpow_natCast ζ a, ← zpow_natCast ζ b, ← zpow_mul, ← zpow_mul, ← zpow_add₀ hζ0, ← hbez, zpow_one]`. Rewrite using `[e, map_mul, map_zpow₀, map_zpow₀, hA, hB]`.
-/
private theorem UpperTheory.algEquiv_fixes_root_of_fixes_prime_power_roots {F K : Type} [Field F] [Field K] [Algebra F K] (g : K ≃ₐ[F] K) :
    ∀ d : ℕ, d ≠ 0 → (∀ p b : ℕ, p.Prime → p ^ b ∣ d → ∀ ζ : K, ζ ^ (p ^ b) = 1 → g ζ = ζ) →
    ∀ ζ : K, ζ ^ d = 1 → g ζ = ζ := by
  intro d
  induction d using Nat.recOnPosPrimePosCoprime with
  | prime_pow p n hp hn =>
    intro _ H ζ hζ
    exact H p n hp dvd_rfl ζ hζ
  | zero =>
    intro h
    exact absurd rfl h
  | one =>
    intro _ _ ζ hζ
    rw [pow_one] at hζ
    rw [hζ, map_one]
  | coprime a b ha hb hab iha ihb =>
    intro hd H ζ hζ
    have ha0 : a ≠ 0 := by omega
    have hb0 : b ≠ 0 := by omega
    have hA : g (ζ ^ b) = ζ ^ b :=
      iha ha0 (fun p c hp hpc => H p c hp (hpc.trans (Dvd.intro _ rfl))) _
        (by rw [← pow_mul, mul_comm, hζ])
    have hB : g (ζ ^ a) = ζ ^ a :=
      ihb hb0 (fun p c hp hpc => H p c hp (hpc.trans (Dvd.intro_left _ rfl))) _
        (by rw [← pow_mul, hζ])
    have hζ0 : ζ ≠ 0 := by
      rintro rfl
      rw [zero_pow (mul_ne_zero ha0 hb0)] at hζ
      exact zero_ne_one hζ
    have hbez : (1 : ℤ) = a * Nat.gcdA a b + b * Nat.gcdB a b := by
      have := Nat.gcd_eq_gcd_ab a b
      rw [Nat.Coprime.gcd_eq_one hab] at this
      exact_mod_cast this
    have e : ζ = (ζ ^ a) ^ Nat.gcdA a b * (ζ ^ b) ^ Nat.gcdB a b := by
      rw [← zpow_natCast ζ a, ← zpow_natCast ζ b, ← zpow_mul, ← zpow_mul, ← zpow_add₀ hζ0, ← hbez,
        zpow_one]
    rw [e, map_mul, map_zpow₀, map_zpow₀, hA, hB]

/- English proof (translation)
Introduce `hGAR F Ω _ _ _ _ _ w A h a ha M hM σ hv hvM`. Establish `hord : GlobalTheory.SmGL.ord (w.adicCompletion F) (a σ) = 0` using `GlobalTheory.SmGL.ord_eq_zero_iff.mpr hv`. Establish `hdeg : deg σ = 0`. Use `ha.ord_eq σ` as an intermediate fact. Rewrite `this` using `[hord]`.

Use linear arithmetic over natural numbers and integers. Use `⟨deg_eq_zero_iff.mp hdeg, ?_⟩` and prove the remaining obligations. Establish `hnat : ∀ n : ℕ, valuation (w.adicCompletion F) (n : w.adicCompletion F) ≤ 1`. Introduce `n`. Proceed by induction on `n with`.

Consider the case `zero => simp`. Consider the case `succ k ih`. Rewrite using `[Nat.cast_succ]`. Conclude with `(Valuation.map_add _ _ _).trans (max_le ih (by rw [map_one]))`. Apply `UpperTheory.algEquiv_fixes_root_of_fixes_prime_power_roots (σ : G F Ω) M (by omega)` to reduce the goal to its premises.

Introduce `p b hp hpb ζ hζ`. Use `haveI : Fact p.Prime := ⟨hp⟩`. Take `⟨ι⟩` from `UpperTheory.nonempty_qbar_ringEquiv_complex p`. Establish `hle : valuation (w.adicCompletion F) ((a σ : w.adicCompletion F) - 1) ≤ valuation (w.adicCompletion F) ((p ^ b : ℕ) : w.adicCompletion F)`. Take `⟨c, hc⟩` from `hpb`.

Use `hvM.trans ?_` and prove the remaining obligations. Rewrite using `[hc, Nat.cast_mul, map_mul]`. Conclude with `mul_le_of_le_one_right' (hnat c)`. Establish `h82` using `UpperTheory.norm_locPow_sub_one_le_of_valuation_sub_one_le F w p ι (p ^ b) (a σ) hle`. Establish `h78` using `UpperTheory.cyclotomicChar_eq_locPow_of_localArtin_unit hGAR F Ω w A h a ha p ι σ hv`.

Rewrite `h82` using `[← h78]`. Conclude with `UpperTheory.fixes_roots_of_unity_of_cyclotomicChar_near_one F Ω p b (σ : G F Ω) h82 ζ hζ`.
-/
theorem UpperTheory.inertia_fixes_roots_of_unity_of_artin_congruence :
    GlobalTheory.Published.GlobalArtinReciprocity → ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (w : HeightOneSpectrum (𝓞 F)) (A : ValuationSubring Ω) (h : IsPlaceOver A w)
    (a : Weil h →* (w.adicCompletion F)ˣ), IsLocalArtin h a → ∀ M : ℕ, 1 ≤ M → ∀ σ : Weil h,
    valuation (w.adicCompletion F) (a σ : w.adicCompletion F) = 1 →
    valuation (w.adicCompletion F) ((a σ : w.adicCompletion F) - 1) ≤ valuation (w.adicCompletion F) (M : w.adicCompletion F) →
    (σ : G F Ω) ∈ Ine (F := F) A ∧ ∀ ζ : Ω, ζ ^ M = 1 → (σ : G F Ω) ζ = ζ := by
  intro hGAR F Ω _ _ _ _ _ w A h a ha M hM σ hv hvM
  have hord : GlobalTheory.SmGL.ord (w.adicCompletion F) (a σ) = 0 := GlobalTheory.SmGL.ord_eq_zero_iff.mpr hv
  have hdeg : deg σ = 0 := by
    have := ha.ord_eq σ
    rw [hord] at this
    omega
  refine ⟨deg_eq_zero_iff.mp hdeg, ?_⟩
  have hnat : ∀ n : ℕ, valuation (w.adicCompletion F) (n : w.adicCompletion F) ≤ 1 := by
    intro n
    induction n with
    | zero => simp
    | succ k ih =>
      rw [Nat.cast_succ]
      exact (Valuation.map_add _ _ _).trans (max_le ih (by rw [map_one]))
  apply UpperTheory.algEquiv_fixes_root_of_fixes_prime_power_roots (σ : G F Ω) M (by omega)
  intro p b hp hpb ζ hζ
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨ι⟩ := UpperTheory.nonempty_qbar_ringEquiv_complex p
  have hle : valuation (w.adicCompletion F) ((a σ : w.adicCompletion F) - 1) ≤
      valuation (w.adicCompletion F) ((p ^ b : ℕ) : w.adicCompletion F) := by
    obtain ⟨c, hc⟩ := hpb
    refine hvM.trans ?_
    rw [hc, Nat.cast_mul, map_mul]
    exact mul_le_of_le_one_right' (hnat c)
  have h82 := UpperTheory.norm_locPow_sub_one_le_of_valuation_sub_one_le F w p ι (p ^ b) (a σ) hle
  have h78 := UpperTheory.cyclotomicChar_eq_locPow_of_localArtin_unit hGAR F Ω w A h a ha p ι σ hv
  rw [← h78] at h82
  exact UpperTheory.fixes_roots_of_unity_of_cyclotomicChar_near_one F Ω p b (σ : G F Ω) h82 ζ hζ

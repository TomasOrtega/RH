import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.VecPairApply
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.ExistsCoprimePowOfMemIneKer
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TamePairing

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen GlobalTheory.TwSys GlobalTheory.SelFun GlobalTheory.Published GlobalTheory.ResSel GlobalTheory.StepTwo GlobalTheory.TwistDet GlobalTheory.NewPrime GlobalTheory.Published.PoitouTate

namespace GlobalTheory.TamePairing

open GlobalTheory.TameQuot

/- English proof (translation)
Take `⟨-, -, -, ⟨t, ht, htsurj, htker⟩, -, -⟩` from `hQ F Ω l A v hA hv`. Establish `hJd : ∀ σ : G F Ω, σ ∈ ineKer F A l → d σ = 1`. Introduce `σ hσ`. Take `⟨τ, hτ, rfl⟩` from `Subgroup.mem_map.1 hσ`. Rewrite `hτ` using `[mem_proKer]`.

Establish `: NeZero (l ^ M)` using `⟨pow_ne_zero _ hl.out.ne_zero⟩`. Establish `key` using `hτ ((d.comp (Ine (F := F) A).subtype).ker) inferInstance (continuous_subtype_val.isOpen_preimage _ hd) (by`. Rewrite using `[Subgroup.index_ker]`. Establish `hdvd : Nat.card (d.comp (Ine (F` using `F) A).subtype).range ∣ l ^ M := by`. Establish `h1` using `Subgroup.card_subgroup_dvd_card (d.comp (Ine (F := F) A).subtype).range`.

Establish `h2 : Nat.card (Multiplicative (ZMod (l ^ M))) = l ^ M` using `Nat.card_zmod (l ^ M)`. Rewrite `h1` using `[h2]`. Then use the resulting hypothesis. Take `⟨j, -, hj⟩` from `(Nat.dvd_prime_pow hl.out).1 hdvd`. Conclude with `⟨j, hj⟩)`. Simplify using `using key`.

Use `set s : Ine (F := F) A → ℤ_[l] := fun σ => Multiplicative.toAdd (t σ) with hs`. Establish `hsmul : ∀ σ τ, s (σ * τ) = s σ + s τ` using `fun σ τ => by`. Simplify using `only [hs, map_mul, toAdd_mul]`. Establish `hscont : Continuous s` using `continuous_toAdd.comp ht`. Use `set γ' : Ine (F := F) A := ⟨γ, hγ⟩ with hγ'`.

Establish `hunit : IsUnit (s γ')`. Assume the negation of the conclusion as `hnu`. Take `⟨b, hb⟩` from `(PadicInt.norm_lt_one_iff_dvd _).1 (PadicInt.mem_nonunits.1 hnu)`. Take `⟨σ, hσ⟩` from `htsurj (Multiplicative.ofAdd b)`. Establish `h1 : t (σ ^ l) = t γ'`.

Apply `Multiplicative.toAdd.injective` to reduce the goal to its premises. Rewrite using `[map_pow, hσ, toAdd_pow, toAdd_ofAdd, nsmul_eq_mul]`. Conclude with `hb.symm`. Establish `h2 : ((((σ ^ l)⁻¹ * γ' : Ine (F` using `F) A)) : G F Ω) ∈ ineKer F A l := by`. Rewrite using `[← htker, map_mul, map_inv, h1, inv_mul_cancel]`.

Establish `h3` using `hJd _ h2`. Simplify using `only [Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_pow, map_mul, map_inv, map_pow, hγ'] at h3`. Rewrite `h3` using `[hdγ, inv_mul_eq_one]`. Establish `h4 : (1 : ZMod (l ^ M)) = l • Multiplicative.toAdd (d σ)`. Rewrite using `[← toAdd_pow, h3, toAdd_ofAdd]`.

Establish `h5` using `congrArg (ZMod.castHom (dvd_pow_self l (by omega : M ≠ 0)) (ZMod l)) h4`. Rewrite `h5` using `[map_one, map_nsmul, nsmul_eq_mul, ZMod.natCast_self, zero_mul]`. Conclude with `one_ne_zero h5`. Use `⟨hγ, ?_⟩` and prove the remaining obligations. Introduce `σ hσ`.

Use `set C := (Subgroup.zpowers γ ⊔ ineKer F A l).topologicalClosure with hC`. Establish `hCc : IsClosed (C : Set (G F Ω))` using `Subgroup.isClosed_topologicalClosure _`. Establish `: CharZero Ω` using `charZero_of_injective_algebraMap (algebraMap F Ω).injective`. Establish `: IsGalois F Ω` using `isGalois_iff.2 ⟨inferInstance, inferInstance⟩`. Establish `: CompactSpace (Ine (F` using `F) A) := isCompact_iff_compactSpace.1 (isClosed_Ine (F := F) A).isCompact`.

Use `set K : Set (Ine (F := F) A) := Subtype.val ⁻¹' (C : Set (G F Ω)) with hK`. Establish `hKc : IsCompact K` using `(hCc.preimage continuous_subtype_val).isCompact`. Establish `hKimg : IsClosed (s '' K)` using `(hKc.image hscont).isClosed`. Establish `hdense : DenseRange (fun m : ℤ => (m : ℤ_[l]) * s γ')`. Establish `hsurj : Function.Surjective (fun a : ℤ_[l] => a * s γ')` using `fun a => ⟨a * ↑hunit.unit⁻¹, by simp [mul_assoc]⟩`.

Conclude with `hsurj.denseRange.comp PadicInt.denseRange_intCast (continuous_id.mul continuous_const)`. Establish `hsub : Set.range (fun m : ℤ => (m : ℤ_[l]) * s γ') ⊆ s '' K`. Introduce and unpack `_ ⟨m, rfl⟩`. Use `⟨γ' ^ m, ?_, ?_⟩` and prove the remaining obligations. Use `show ((γ' ^ m : Ine (F := F) A) : G F Ω) ∈ C`.

Apply `Subgroup.le_topologicalClosure` to reduce the goal to its premises. Apply `Subgroup.mem_sup_left` to reduce the goal to its premises. Rewrite using `[Subgroup.coe_zpow]`. Conclude with `Subgroup.zpow_mem_zpowers γ m`. Simplify using `only [hs, map_zpow, toAdd_zpow, zsmul_eq_mul]`.

Establish `hall : s '' K = Set.univ`. Apply `Set.eq_univ_of_univ_subset` to reduce the goal to its premises. Rewrite using `[← hdense.closure_range]`. Conclude with `hKimg.closure_subset_iff.2 hsub`. Take `⟨κ, hκ, hκs⟩ : s ⟨σ, hσ⟩ ∈ s '' K` from `by rw [hall]; trivial`.

Establish `htk : t κ = t ⟨σ, hσ⟩` using `Multiplicative.toAdd.injective hκs`. Establish `hJ : ((κ⁻¹ * ⟨σ, hσ⟩ : Ine (F` using `F) A) : G F Ω) ∈ ineKer F A l := by`. Rewrite using `[← htker, map_mul, map_inv, htk, inv_mul_cancel]`. Establish `hmem : ((κ⁻¹ * ⟨σ, hσ⟩ : Ine (F` using `F) A) : G F Ω) ∈ C := Subgroup.le_topologicalClosure _ (Subgroup.mem_sup_right hJ)`. Use `C.mul_mem hκ hmem` as an intermediate fact.

Simplify using `using this`.
-/
theorem isProGen_of_char_eq_one (hQ : TameQuotient) {F Ω : Type} [Field F] [NumberField F] [Field Ω]
    [Algebra F Ω] [IsAlgClosure F Ω] {l : ℕ} [hl : Fact l.Prime] {A : ValuationSubring Ω}
    {v : HeightOneSpectrum (𝓞 F)} (hA : IsPlaceOver A v) (hv : ((l : ℕ) : 𝓞 F) ∉ v.asIdeal)
    {M : ℕ} (hM : 1 ≤ M) (d : G F Ω →* Multiplicative (ZMod (l ^ M)))
    (hd : IsOpen (d.ker : Set (G F Ω))) {γ : G F Ω} (hγ : γ ∈ Ine (F := F) A)
    (hdγ : d γ = Multiplicative.ofAdd 1) : IsProGen F A l γ := by
  classical
  obtain ⟨-, -, -, ⟨t, ht, htsurj, htker⟩, -, -⟩ := hQ F Ω l A v hA hv

  have hJd : ∀ σ : G F Ω, σ ∈ ineKer F A l → d σ = 1 := by
    intro σ hσ
    obtain ⟨τ, hτ, rfl⟩ := Subgroup.mem_map.1 hσ
    rw [mem_proKer] at hτ
    have : NeZero (l ^ M) := ⟨pow_ne_zero _ hl.out.ne_zero⟩
    have key := hτ ((d.comp (Ine (F := F) A).subtype).ker) inferInstance
      (continuous_subtype_val.isOpen_preimage _ hd) (by
        rw [Subgroup.index_ker]
        have hdvd : Nat.card (d.comp (Ine (F := F) A).subtype).range ∣ l ^ M := by
          have h1 := Subgroup.card_subgroup_dvd_card (d.comp (Ine (F := F) A).subtype).range
          have h2 : Nat.card (Multiplicative (ZMod (l ^ M))) = l ^ M := Nat.card_zmod (l ^ M)
          rwa [h2] at h1
        obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow hl.out).1 hdvd
        exact ⟨j, hj⟩)
    simpa using key

  set s : Ine (F := F) A → ℤ_[l] := fun σ => Multiplicative.toAdd (t σ) with hs
  have hsmul : ∀ σ τ, s (σ * τ) = s σ + s τ := fun σ τ => by
    simp only [hs, map_mul, toAdd_mul]
  have hscont : Continuous s := continuous_toAdd.comp ht
  set γ' : Ine (F := F) A := ⟨γ, hγ⟩ with hγ'

  have hunit : IsUnit (s γ') := by
    by_contra hnu
    obtain ⟨b, hb⟩ := (PadicInt.norm_lt_one_iff_dvd _).1 (PadicInt.mem_nonunits.1 hnu)
    obtain ⟨σ, hσ⟩ := htsurj (Multiplicative.ofAdd b)
    have h1 : t (σ ^ l) = t γ' := by
      apply Multiplicative.toAdd.injective
      rw [map_pow, hσ, toAdd_pow, toAdd_ofAdd, nsmul_eq_mul]
      exact hb.symm
    have h2 : ((((σ ^ l)⁻¹ * γ' : Ine (F := F) A)) : G F Ω) ∈ ineKer F A l := by
      rw [← htker, map_mul, map_inv, h1, inv_mul_cancel]
    have h3 := hJd _ h2
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_pow, map_mul, map_inv,
      map_pow, hγ'] at h3
    rw [hdγ, inv_mul_eq_one] at h3
    have h4 : (1 : ZMod (l ^ M)) = l • Multiplicative.toAdd (d σ) := by
      rw [← toAdd_pow, h3, toAdd_ofAdd]
    have h5 := congrArg (ZMod.castHom (dvd_pow_self l (by omega : M ≠ 0)) (ZMod l)) h4
    rw [map_one, map_nsmul, nsmul_eq_mul, ZMod.natCast_self, zero_mul] at h5
    exact one_ne_zero h5
  refine ⟨hγ, ?_⟩
  intro σ hσ
  set C := (Subgroup.zpowers γ ⊔ ineKer F A l).topologicalClosure with hC
  have hCc : IsClosed (C : Set (G F Ω)) := Subgroup.isClosed_topologicalClosure _
  have : CharZero Ω := charZero_of_injective_algebraMap (algebraMap F Ω).injective
  have : IsGalois F Ω := isGalois_iff.2 ⟨inferInstance, inferInstance⟩
  have : CompactSpace (Ine (F := F) A) :=
    isCompact_iff_compactSpace.1 (isClosed_Ine (F := F) A).isCompact
  set K : Set (Ine (F := F) A) := Subtype.val ⁻¹' (C : Set (G F Ω)) with hK
  have hKc : IsCompact K := (hCc.preimage continuous_subtype_val).isCompact
  have hKimg : IsClosed (s '' K) := (hKc.image hscont).isClosed
  have hdense : DenseRange (fun m : ℤ => (m : ℤ_[l]) * s γ') := by
    have hsurj : Function.Surjective (fun a : ℤ_[l] => a * s γ') := fun a =>
      ⟨a * ↑hunit.unit⁻¹, by simp [mul_assoc]⟩
    exact hsurj.denseRange.comp PadicInt.denseRange_intCast (continuous_id.mul continuous_const)
  have hsub : Set.range (fun m : ℤ => (m : ℤ_[l]) * s γ') ⊆ s '' K := by
    rintro _ ⟨m, rfl⟩
    refine ⟨γ' ^ m, ?_, ?_⟩
    · show ((γ' ^ m : Ine (F := F) A) : G F Ω) ∈ C
      apply Subgroup.le_topologicalClosure
      apply Subgroup.mem_sup_left
      rw [Subgroup.coe_zpow]
      exact Subgroup.zpow_mem_zpowers γ m
    · simp only [hs, map_zpow, toAdd_zpow, zsmul_eq_mul]
  have hall : s '' K = Set.univ := by
    apply Set.eq_univ_of_univ_subset
    rw [← hdense.closure_range]
    exact hKimg.closure_subset_iff.2 hsub
  obtain ⟨κ, hκ, hκs⟩ : s ⟨σ, hσ⟩ ∈ s '' K := by rw [hall]; trivial
  have htk : t κ = t ⟨σ, hσ⟩ := Multiplicative.toAdd.injective hκs
  have hJ : ((κ⁻¹ * ⟨σ, hσ⟩ : Ine (F := F) A) : G F Ω) ∈ ineKer F A l := by
    rw [← htker, map_mul, map_inv, htk, inv_mul_cancel]
  have hmem : ((κ⁻¹ * ⟨σ, hσ⟩ : Ine (F := F) A) : G F Ω) ∈ C :=
    Subgroup.le_topologicalClosure _ (Subgroup.mem_sup_right hJ)
  have := C.mul_mem hκ hmem
  simpa using this

/- English proof (translation)
Introduce `hTL F Ω _ _ _ _ _ l hl n A v hn hA hv hq e he M hM d hd γ φ hγ hdγ hφ`. Take `⟨hQ, hS⟩` from `hTL`. Establish `hN : NeZero (l ^ n)` using `⟨pow_ne_zero _ hl.out.ne_zero⟩`. Establish `hpg : IsProGen F A l (γ : G F Ω)` using `isProGen_of_char_eq_one hQ hA hv hM d hd hγ hdγ`. Take `⟨-, -, -, -, -, hgen⟩` from `hQ F Ω l A v hA hv`.

Take `⟨hdense, -, hhom⟩` from `hgen φ γ hφ hpg`. Establish `hall : ∀ S : Subgroup (Dec (F` using `F) A), IsClosed (S : Set (Dec (F := F) A)) → φ ∈ S → (∀ σ : Dec (F := F) A, (σ : G F Ω) ∈ Ine (F := F) A → σ ∈ S) → S = ⊤ := by`. Introduce `S hSc hφS hIS`. Rewrite using `[eq_top_iff, ← hdense]`. Apply `Subgroup.topologicalClosure_minimal _ _ hSc` to reduce the goal to its premises.

Rewrite using `[sup_le_iff]`. Prove the components needed by the constructor for the conclusion. Rewrite using `[Subgroup.closure_le]`. Introduce `x hx`. Simplify using `only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx`.

Break down `hx with rfl | rfl` into its components or cases. Conclude with `hφS`. Conclude with `hIS _ hγ`. Introduce `x hx`. Conclude with `hIS x (ineKer_le_Ine A l (Subgroup.mem_subgroupOf.1 hx))`.

Establish `hχ : ∀ g : Dec (F` using `F) A, cycMod F Ω l n (g : G F Ω) = 1 := by`. Establish `hcont : Continuous fun g : Dec (F` using `F) A => ((cycMod F Ω l n (g : G F Ω) : (ZMod (l ^ n))ˣ) : ZMod (l ^ n)) := (GlobalTheory.TameQuot.continuous_cycMod (F := F) (Ω := Ω) l n).comp continuous_subtype_val`. Set `S : Subgroup (Dec (F` to `F) A) := ((cycMod F Ω l n).comp (Dec (F := F) A).subtype).ker`. Establish `hSc : IsClosed (S : Set (Dec (F` using `F) A)) := by`. Establish `: (S : Set (Dec (F` using `F) A)) = (fun g : Dec (F := F) A => ((cycMod F Ω l n (g : G F Ω) : (ZMod (l ^ n))ˣ) : ZMod (l ^ n))) ⁻¹' {1} := by`.

Use extensionality with `g`. Simplify using `[S, MonoidHom.mem_ker, Units.val_eq_one]`. Rewrite using `[this]`. Conclude with `isClosed_singleton.preimage hcont`. Establish `hone : ∀ σ : G F Ω, (∀ x : Ω, A.valuation x ≤ 1 → A.valuation (σ x - x ^ 1) < 1) → cycMod F Ω l n σ = 1`.

Introduce `σ hσ`. Use `cycZ_toZModPow_eq hv hA hσ n` as an intermediate fact. Use `ext`. Simplify using `only [cycMod, MonoidHom.coe_comp, Function.comp_apply, Units.coe_map, RingHom.toMonoidHom_eq_coe, MonoidHom.coe_coe, Units.val_one]`. Rewrite using `[this, Nat.cast_one, map_one]`.

Establish `hSt` using `hall S hSc (by show cycMod F Ω l n (φ : G F Ω) = 1`. Establish `h1` using `cycZ_of_isFrob hv hA hφ`. Use `ext`. Simplify using `only [cycMod, MonoidHom.coe_comp, Function.comp_apply, Units.coe_map, RingHom.toMonoidHom_eq_coe, MonoidHom.coe_coe, Units.val_one]`. Rewrite using `[h1, map_natCast, ← Nat.cast_one, ZMod.natCast_eq_natCast_iff]`.

Conclude with `hq)`. Use the proof step `(fun σ hσ => by show cycMod F Ω l n (σ : G F Ω) = 1`. Apply `hone` to reduce the goal to its premises. Introduce `x hx`. Rewrite using `[pow_one]`.

Conclude with `((mem_Ine.1 hσ).2 x hx))`. Introduce `g`. Establish `hg : g ∈ S` using `hSt ▸ Subgroup.mem_top g`. Conclude with `hg`. Take `⟨f, hfker, -, hfφ, hfγ⟩` from `hhom (Multiplicative (ZMod (l ^ n))) (Multiplicative.ofAdd 1) 1 ⟨0, by simp⟩ (by simp)`.

Establish `hfc : Continuous f`. Rewrite using `[continuous_discrete_rng]`. Introduce `b`. Distinguish the cases in `hb : ∃ a, f a = b`. Take `⟨a, rfl⟩` from `hb`.

Establish `: f ⁻¹' {f a} = (fun x => a⁻¹ * x) ⁻¹' (f.ker : Set (Dec (F` using `F) A)) := by`. Use extensionality with `x`. Simplify using `only [Set.mem_preimage, Set.mem_singleton_iff, SetLike.mem_coe, MonoidHom.mem_ker, map_mul, map_inv]`. Rewrite using `[inv_mul_eq_one]`. Conclude with `eq_comm`.

Rewrite using `[this]`. Conclude with `hfker.preimage (continuous_const.mul continuous_id)`. Establish `: f ⁻¹' {b} = ∅`. Use extensionality with `x`. Simplify using `only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_empty_iff_false, iff_false]`.

Conclude with `fun h => hb ⟨x, h⟩`. Rewrite using `[this]`. Conclude with `isOpen_empty`. Use `set k : Dec (F := F) A → ZMod (l ^ n) := fun g => Multiplicative.toAdd (f g) with hk`. Establish `hkc : Continuous k` using `continuous_toAdd.comp hfc`.

Establish `hkadd : ∀ g h, k (g * h) = k g + k h` using `fun g h => by simp [hk, toAdd_mul]`. Establish `hkγ : k γ = 0` using `by simp [hk, hfγ]`. Establish `hkφ : k φ = 1` using `by simp [hk, hfφ]`. Establish `hkI : ∀ σ : Dec (F` using `F) A, (σ : G F Ω) ∈ Ine (F := F) A → k σ = 0 := fun σ hσ => eq_zero_of_isProGen hpg k hkc hkadd hkγ σ hσ`. Establish `hCZ : CharZero Ω` using `charZero_of_injective_algebraMap (algebraMap F Ω).injective`.

Establish `hAC : IsAlgClosed Ω` using `IsAlgClosure.isAlgClosed F`. Establish `hNZ : NeZero ((l ^ n : ℕ) : Ω)` using `⟨by exact_mod_cast pow_ne_zero n hl.out.ne_zero⟩`. Take `⟨ζ, hζ⟩` from `HasEnoughRootsOfUnity.exists_primitiveRoot Ω (l ^ n)`. Take `⟨u₀, hu₀⟩` from `TameSymbol.of_equiv hS hA hv hq hζ (LinearEquiv.ofBijective e he)`. Take `⟨x₀, hx₀⟩` from `exists_isUnifRoot (F := F) (Ω := Ω) v (N := l ^ n) (pow_pos hl.out.pos n)`.

Take `⟨c, hc⟩` from `exists_apply_eq_pow_mul hζ hx₀ (γ : G F Ω)`. Establish `hcu : IsUnit c` using `((hS F Ω l n A v hA hv hq ζ hζ).2 x₀ hx₀ γ c hγ hc).1 hpg`. Use `⟨hcu.unit⁻¹ * u₀, ?_⟩` and prove the remaining obligations. Introduce `W W' _ _ _ _ _ _ P x y hW' hxc hyc hxadd hyadd hyI w hw`. Establish `hψ0 : zmultiplesHom W' (y φ) ((l ^ n : ℕ) : ℤ) = 0`.

Simplify using `only [zmultiplesHom_apply, natCast_zsmul]`. Conclude with `hW' _`. Set `ψ : ZMod (l ^ n) →+ W'` to `ZMod.lift (l ^ n) ⟨zmultiplesHom W' (y φ), hψ0⟩`. Establish `hψ : ∀ a : ZMod (l ^ n), ψ a = (a.cast : ℤ) • y φ`. Introduce `a`.

Establish `h` using `ZMod.lift_coe (l ^ n) ⟨zmultiplesHom W' (y φ), hψ0⟩ (a.cast : ℤ)`. Rewrite `h` using `[ZMod.intCast_zmod_cast]`. Conclude with `h.trans (by simp)`. Establish `hψ1 : ψ 1 = y φ` using `(by simpa using ZMod.lift_coe (l ^ n) ⟨zmultiplesHom W' (y φ), hψ0⟩ 1 : ZMod.lift (l ^ n) ⟨zmultiplesHom W' (y φ), hψ0⟩ 1 = y φ)`. Set `yH : Dec (F` to `F) A →* Multiplicative W' := MonoidHom.mk' (fun g => Multiplicative.ofAdd (y g)) (fun a b => by rw [hyadd, ofAdd_add])`.

Set `kH : Dec (F` to `F) A →* Multiplicative W' := MonoidHom.mk' (fun g => Multiplicative.ofAdd (ψ (k g))) (fun a b => by`. Rewrite using `[hkadd, map_add, ofAdd_add])`. Establish `hE` using `hall (yH.eqLocus kH) (by`. Establish `: ((yH.eqLocus kH : Subgroup (Dec (F` using `F) A)) : Set (Dec (F := F) A)) = {g | Multiplicative.ofAdd (y g) = Multiplicative.ofAdd (ψ (k g))} := rfl`. Rewrite using `[this]`.

Conclude with `isClosed_eq (continuous_ofAdd.comp hyc) (continuous_ofAdd.comp (continuous_of_discreteTopology.comp hkc)))`. Use the proof step `(by show Multiplicative.ofAdd (y φ) = Multiplicative.ofAdd (ψ (k φ))`. Rewrite using `[hkφ, hψ1])`. Use the proof step `(fun σ hσ => by show Multiplicative.ofAdd (y σ) = Multiplicative.ofAdd (ψ (k σ))`. Rewrite using `[hyI σ hσ, hkI σ hσ, map_zero ψ])`.

Establish `hyk : ∀ h, y h = ψ (k h)` using `fun h => by`. Establish `hh : h ∈ yH.eqLocus kH` using `hE ▸ Subgroup.mem_top h`. Conclude with `Multiplicative.ofAdd.injective hh`. Use `set z : Dec (F := F) A → ZMod (l ^ n) := fun g => P (x g) (y φ) with hz`. Establish `hzc : Continuous z` using `(continuous_of_discreteTopology (f := fun m : W => P m (y φ))).comp hxc`.

Establish `hzadd : ∀ g h, z (g * h) = z g + z h` using `fun g h => by`. Simplify using `only [hz, hxadd, map_add, AddMonoidHom.add_apply]`. Establish `hw' : ∀ g h, w.1 (g, h) = z g * k h` using `fun g h => by`. Rewrite using `[hw, hyk h, hψ, map_zsmul, zsmul_eq_mul, ZMod.intCast_zmod_cast, mul_comm]`. Set `zZ : Z1 (trivDec F A l n)` to `⟨z, (mem_Z1_iff_cocycle _ _).2 ⟨hzc, fun g h => by`.

Rewrite using `[hzadd, Representation.trivial_apply]⟩⟩`. Set `kZ : Z1 (muDec F A l n)` to `⟨k, (mem_Z1_iff_cocycle _ _).2 ⟨hkc, fun g h => by`. Rewrite using `[hkadd, charRep_apply, MonoidHom.comp_apply, Subgroup.coe_subtype, hχ g, Units.val_one, one_mul]⟩⟩`. Establish `hur : (Submodule.Quotient.mk kZ : H1 (muDec F A l n)) ∈ H1ur (muDec F A l n) ((Ine (F` using `F) A).subgroupOf (Dec (F := F) A)) := by`. Rewrite using `[H1ur, LinearMap.mem_ker]`.

Use `delta ReciprocityTheory.Gal.resH1`. Rewrite using `[Submodule.mapQ_apply]`. Establish `: ReciprocityTheory.Gal.restrictCocycles1 (muDec F A l n) ((Ine (F` using `F) A).subgroupOf (Dec (F := F) A)).subtype continuous_subtype_val kZ = 0 := by`. Apply `Subtype.ext` to reduce the goal to its premises. Use function extensionality and compare the values at `h`.

Use `show k (h : Dec (F := F) A) = 0`. Conclude with `hkI _ (Subgroup.mem_subgroupOf.1 h.2)`. Rewrite using `[this, Submodule.Quotient.mk_zero]`. Establish `hcup` using `cupMu_mk zZ kZ w (fun g h => by`. Rewrite using `[hw', charRep_apply, MonoidHom.comp_apply, Subgroup.coe_subtype, hχ g, Units.val_one, one_mul])`.

Establish `key` using `hu₀ x₀ hx₀ γ c hγ hc φ hφ zZ kZ hur`. Rewrite `key` using `[hcup]`. Express the relevant statement in the definitionally equal form `c * e (Submodule.Quotient.mk w) = u₀ * (z γ * k φ) at key`. Rewrite `key` using `[hkφ, mul_one]`. Combine the equalities or inequalities in the displayed calculation.

Rewrite using `[← mul_assoc, hcu.val_inv_mul, one_mul]`. Use `_ = ((hcu.unit⁻¹ * u₀ : (ZMod (l ^ n))ˣ) : ZMod (l ^ n)) * P (x γ) (y φ) := by`. Rewrite using `[key, Units.val_mul, mul_assoc]`.
-/
theorem tame_pairing_hom : TameLocal → ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (l : ℕ) [Fact l.Prime] (n : ℕ) (A : ValuationSubring Ω) (v : HeightOneSpectrum (𝓞 F)), 0 < n → IsPlaceOver A v → ((l : ℕ) : 𝓞 F) ∉ v.asIdeal → normV v ≡ 1 [MOD l ^ n] → ∀ e : H2 (muLoc F l n A) →ₗ[ZMod (l ^ n)] ZMod (l ^ n), Function.Bijective e → ∀ (M : ℕ), 1 ≤ M → ∀ d : G F Ω →* Multiplicative (ZMod (l ^ M)), IsOpen (d.ker : Set (G F Ω)) → ∀ γ φ : Dec (F := F) A, (γ : G F Ω) ∈ Ine (F := F) A → d γ = Multiplicative.ofAdd 1 → IsFrob A (normV v) (φ : G F Ω) → ∃ u : (ZMod (l ^ n))ˣ, ∀ (W W' : Type) [AddCommGroup W] [TopologicalSpace W] [DiscreteTopology W] [AddCommGroup W'] [TopologicalSpace W'] [DiscreteTopology W'] (P : W →+ W' →+ ZMod (l ^ n)) (x : Dec (F := F) A → W) (y : Dec (F := F) A → W'), (∀ m : W', l ^ n • m = 0) → Continuous x → Continuous y → (∀ g h, x (g * h) = x g + x h) → (∀ g h, y (g * h) = y g + y h) → (∀ g : Dec (F := F) A, (g : G F Ω) ∈ Ine (F := F) A → y g = 0) → ∀ w : Z2 (muLoc F l n A), (∀ g h, w.1 (g, h) = P (x g) (y h)) → e (Submodule.Quotient.mk w) = (u : ZMod (l ^ n)) * P (x γ) (y φ) := by
  intro hTL F Ω _ _ _ _ _ l hl n A v hn hA hv hq e he M hM d hd γ φ hγ hdγ hφ
  classical
  obtain ⟨hQ, hS⟩ := hTL
  have hN : NeZero (l ^ n) := ⟨pow_ne_zero _ hl.out.ne_zero⟩
  have hpg : IsProGen F A l (γ : G F Ω) := isProGen_of_char_eq_one hQ hA hv hM d hd hγ hdγ
  obtain ⟨-, -, -, -, -, hgen⟩ := hQ F Ω l A v hA hv
  obtain ⟨hdense, -, hhom⟩ := hgen φ γ hφ hpg

  have hall : ∀ S : Subgroup (Dec (F := F) A), IsClosed (S : Set (Dec (F := F) A)) → φ ∈ S →
      (∀ σ : Dec (F := F) A, (σ : G F Ω) ∈ Ine (F := F) A → σ ∈ S) → S = ⊤ := by
    intro S hSc hφS hIS
    rw [eq_top_iff, ← hdense]
    apply Subgroup.topologicalClosure_minimal _ _ hSc
    rw [sup_le_iff]
    constructor
    · rw [Subgroup.closure_le]
      intro x hx
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with rfl | rfl
      · exact hφS
      · exact hIS _ hγ
    · intro x hx
      exact hIS x (ineKer_le_Ine A l (Subgroup.mem_subgroupOf.1 hx))

  have hχ : ∀ g : Dec (F := F) A, cycMod F Ω l n (g : G F Ω) = 1 := by
    have hcont : Continuous fun g : Dec (F := F) A =>
        ((cycMod F Ω l n (g : G F Ω) : (ZMod (l ^ n))ˣ) : ZMod (l ^ n)) :=
      (GlobalTheory.TameQuot.continuous_cycMod (F := F) (Ω := Ω) l n).comp continuous_subtype_val
    let S : Subgroup (Dec (F := F) A) := ((cycMod F Ω l n).comp (Dec (F := F) A).subtype).ker
    have hSc : IsClosed (S : Set (Dec (F := F) A)) := by
      have : (S : Set (Dec (F := F) A)) = (fun g : Dec (F := F) A =>
          ((cycMod F Ω l n (g : G F Ω) : (ZMod (l ^ n))ˣ) : ZMod (l ^ n))) ⁻¹' {1} := by
        ext g
        simp [S, MonoidHom.mem_ker, Units.val_eq_one]
      rw [this]
      exact isClosed_singleton.preimage hcont
    have hone : ∀ σ : G F Ω, (∀ x : Ω, A.valuation x ≤ 1 → A.valuation (σ x - x ^ 1) < 1) →
        cycMod F Ω l n σ = 1 := by
      intro σ hσ
      have := cycZ_toZModPow_eq hv hA hσ n
      ext
      simp only [cycMod, MonoidHom.coe_comp, Function.comp_apply, Units.coe_map,
        RingHom.toMonoidHom_eq_coe, MonoidHom.coe_coe, Units.val_one]
      rw [this, Nat.cast_one, map_one]
    have hSt := hall S hSc (by
        show cycMod F Ω l n (φ : G F Ω) = 1
        have h1 := cycZ_of_isFrob hv hA hφ
        ext
        simp only [cycMod, MonoidHom.coe_comp, Function.comp_apply, Units.coe_map,
          RingHom.toMonoidHom_eq_coe, MonoidHom.coe_coe, Units.val_one]
        rw [h1, map_natCast, ← Nat.cast_one, ZMod.natCast_eq_natCast_iff]
        exact hq)
      (fun σ hσ => by
        show cycMod F Ω l n (σ : G F Ω) = 1
        apply hone
        intro x hx
        rw [pow_one]
        exact ((mem_Ine.1 hσ).2 x hx))
    intro g
    have hg : g ∈ S := hSt ▸ Subgroup.mem_top g
    exact hg

  obtain ⟨f, hfker, -, hfφ, hfγ⟩ := hhom (Multiplicative (ZMod (l ^ n)))
    (Multiplicative.ofAdd 1) 1 ⟨0, by simp⟩ (by simp)
  have hfc : Continuous f := by
    rw [continuous_discrete_rng]
    intro b
    by_cases hb : ∃ a, f a = b
    · obtain ⟨a, rfl⟩ := hb
      have : f ⁻¹' {f a} = (fun x => a⁻¹ * x) ⁻¹' (f.ker : Set (Dec (F := F) A)) := by
        ext x
        simp only [Set.mem_preimage, Set.mem_singleton_iff, SetLike.mem_coe, MonoidHom.mem_ker,
          map_mul, map_inv]
        rw [inv_mul_eq_one]
        exact eq_comm
      rw [this]
      exact hfker.preimage (continuous_const.mul continuous_id)
    · have : f ⁻¹' {b} = ∅ := by
        ext x
        simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_empty_iff_false, iff_false]
        exact fun h => hb ⟨x, h⟩
      rw [this]
      exact isOpen_empty
  set k : Dec (F := F) A → ZMod (l ^ n) := fun g => Multiplicative.toAdd (f g) with hk
  have hkc : Continuous k := continuous_toAdd.comp hfc
  have hkadd : ∀ g h, k (g * h) = k g + k h := fun g h => by simp [hk, toAdd_mul]
  have hkγ : k γ = 0 := by simp [hk, hfγ]
  have hkφ : k φ = 1 := by simp [hk, hfφ]
  have hkI : ∀ σ : Dec (F := F) A, (σ : G F Ω) ∈ Ine (F := F) A → k σ = 0 :=
    fun σ hσ => eq_zero_of_isProGen hpg k hkc hkadd hkγ σ hσ

  have hCZ : CharZero Ω := charZero_of_injective_algebraMap (algebraMap F Ω).injective
  have hAC : IsAlgClosed Ω := IsAlgClosure.isAlgClosed F
  have hNZ : NeZero ((l ^ n : ℕ) : Ω) := ⟨by exact_mod_cast pow_ne_zero n hl.out.ne_zero⟩
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot Ω (l ^ n)
  obtain ⟨u₀, hu₀⟩ := TameSymbol.of_equiv hS hA hv hq hζ (LinearEquiv.ofBijective e he)
  obtain ⟨x₀, hx₀⟩ := exists_isUnifRoot (F := F) (Ω := Ω) v (N := l ^ n) (pow_pos hl.out.pos n)
  obtain ⟨c, hc⟩ := exists_apply_eq_pow_mul hζ hx₀ (γ : G F Ω)
  have hcu : IsUnit c := ((hS F Ω l n A v hA hv hq ζ hζ).2 x₀ hx₀ γ c hγ hc).1 hpg
  refine ⟨hcu.unit⁻¹ * u₀, ?_⟩
  intro W W' _ _ _ _ _ _ P x y hW' hxc hyc hxadd hyadd hyI w hw

  have hψ0 : zmultiplesHom W' (y φ) ((l ^ n : ℕ) : ℤ) = 0 := by
    simp only [zmultiplesHom_apply, natCast_zsmul]
    exact hW' _
  let ψ : ZMod (l ^ n) →+ W' := ZMod.lift (l ^ n) ⟨zmultiplesHom W' (y φ), hψ0⟩
  have hψ : ∀ a : ZMod (l ^ n), ψ a = (a.cast : ℤ) • y φ := by
    intro a
    have h := ZMod.lift_coe (l ^ n) ⟨zmultiplesHom W' (y φ), hψ0⟩ (a.cast : ℤ)
    rw [ZMod.intCast_zmod_cast] at h
    exact h.trans (by simp)
  have hψ1 : ψ 1 = y φ :=
    (by simpa using ZMod.lift_coe (l ^ n) ⟨zmultiplesHom W' (y φ), hψ0⟩ 1 :
      ZMod.lift (l ^ n) ⟨zmultiplesHom W' (y φ), hψ0⟩ 1 = y φ)
  let yH : Dec (F := F) A →* Multiplicative W' :=
    MonoidHom.mk' (fun g => Multiplicative.ofAdd (y g)) (fun a b => by rw [hyadd, ofAdd_add])
  let kH : Dec (F := F) A →* Multiplicative W' :=
    MonoidHom.mk' (fun g => Multiplicative.ofAdd (ψ (k g))) (fun a b => by
      rw [hkadd, map_add, ofAdd_add])
  have hE := hall (yH.eqLocus kH) (by
      have : ((yH.eqLocus kH : Subgroup (Dec (F := F) A)) : Set (Dec (F := F) A)) =
          {g | Multiplicative.ofAdd (y g) = Multiplicative.ofAdd (ψ (k g))} := rfl
      rw [this]
      exact isClosed_eq (continuous_ofAdd.comp hyc)
        (continuous_ofAdd.comp (continuous_of_discreteTopology.comp hkc)))
    (by
      show Multiplicative.ofAdd (y φ) = Multiplicative.ofAdd (ψ (k φ))
      rw [hkφ, hψ1])
    (fun σ hσ => by
      show Multiplicative.ofAdd (y σ) = Multiplicative.ofAdd (ψ (k σ))
      rw [hyI σ hσ, hkI σ hσ, map_zero ψ])
  have hyk : ∀ h, y h = ψ (k h) := fun h => by
    have hh : h ∈ yH.eqLocus kH := hE ▸ Subgroup.mem_top h
    exact Multiplicative.ofAdd.injective hh

  set z : Dec (F := F) A → ZMod (l ^ n) := fun g => P (x g) (y φ) with hz
  have hzc : Continuous z :=
    (continuous_of_discreteTopology (f := fun m : W => P m (y φ))).comp hxc
  have hzadd : ∀ g h, z (g * h) = z g + z h := fun g h => by
    simp only [hz, hxadd, map_add, AddMonoidHom.add_apply]
  have hw' : ∀ g h, w.1 (g, h) = z g * k h := fun g h => by
    rw [hw, hyk h, hψ, map_zsmul, zsmul_eq_mul, ZMod.intCast_zmod_cast, mul_comm]
  let zZ : Z1 (trivDec F A l n) := ⟨z, (mem_Z1_iff_cocycle _ _).2 ⟨hzc, fun g h => by
    rw [hzadd, Representation.trivial_apply]⟩⟩
  let kZ : Z1 (muDec F A l n) := ⟨k, (mem_Z1_iff_cocycle _ _).2 ⟨hkc, fun g h => by
    rw [hkadd, charRep_apply, MonoidHom.comp_apply, Subgroup.coe_subtype, hχ g, Units.val_one,
      one_mul]⟩⟩
  have hur : (Submodule.Quotient.mk kZ : H1 (muDec F A l n)) ∈
      H1ur (muDec F A l n) ((Ine (F := F) A).subgroupOf (Dec (F := F) A)) := by
    rw [H1ur, LinearMap.mem_ker]
    delta ReciprocityTheory.Gal.resH1
    rw [Submodule.mapQ_apply]
    have : ReciprocityTheory.Gal.restrictCocycles1 (muDec F A l n) ((Ine (F := F) A).subgroupOf (Dec (F := F) A)).subtype
        continuous_subtype_val kZ = 0 := by
      apply Subtype.ext
      funext h
      show k (h : Dec (F := F) A) = 0
      exact hkI _ (Subgroup.mem_subgroupOf.1 h.2)
    rw [this, Submodule.Quotient.mk_zero]
  have hcup := cupMu_mk zZ kZ w (fun g h => by
    rw [hw', charRep_apply, MonoidHom.comp_apply, Subgroup.coe_subtype, hχ g, Units.val_one,
      one_mul])
  have key := hu₀ x₀ hx₀ γ c hγ hc φ hφ zZ kZ hur
  rw [hcup] at key
  change c * e (Submodule.Quotient.mk w) = u₀ * (z γ * k φ) at key
  rw [hkφ, mul_one] at key
  calc e (Submodule.Quotient.mk w)
      = ((hcu.unit⁻¹ : (ZMod (l ^ n))ˣ) : ZMod (l ^ n)) * (c * e (Submodule.Quotient.mk w)) := by
        rw [← mul_assoc, hcu.val_inv_mul, one_mul]
    _ = ((hcu.unit⁻¹ * u₀ : (ZMod (l ^ n))ˣ) : ZMod (l ^ n)) * P (x γ) (y φ) := by
        rw [key, Units.val_mul, mul_assoc]

end GlobalTheory.TamePairing

import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.PoitouTateNormalised
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.ExistsCoprimePowOfMemIneKer

open NumberField IsDedekindDomain Representation Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.Published GlobalTheory.Published.PoitouTate

namespace GlobalTheory.CompanionTheory.TameAction

open GlobalTheory.TameQuot GlobalTheory.WeilDeligne in

/- English proof (translation)
Introduce `F Ω _ _ _ _ _ A v hA φ hφ N hN ξ hξ' a t i haN hi hfix`. Establish `: IsAlgClosed Ω` using `IsAlgClosure.isAlgClosed F`. Establish `: CharZero Ω` using `charZero_of_injective_algebraMap (algebraMap F Ω).injective`. Establish `hq` using `one_lt_normV v`. Take `⟨n, hn⟩ : ∃ n, normV v ^ N = n + 1` from `⟨_, (Nat.sub_add_cancel (Nat.one_le_pow _ _ (by omega))).symm⟩`.

Establish `hn0 : n ≠ 0`. Use `one_lt_pow₀ hq hN.ne'` as an intermediate fact. Use linear arithmetic over natural numbers and integers. Establish `: NeZero n` using `⟨hn0⟩`. Establish `: NeZero (n : Ω)` using `⟨Nat.cast_ne_zero.2 hn0⟩`.

Establish `hξ : IsPrimitiveRoot ξ n`. Establish `e : normV v ^ N - 1 = n` using `by omega`. Rewrite `hξ'` using `[e]`. Then use the resulting hypothesis. Establish `hnv : ¬ A.valuation (n : Ω) < 1`. Introduce `h`.

Establish `h1 : ((normV v : ℕ) : 𝓞 F) ∈ v.asIdeal`. Rewrite using `[← Ideal.Quotient.eq_zero_iff_mem, map_natCast, ← nsmul_one]`. Conclude with `card_nsmul_eq_zero'`. Establish `h2 : ((n : ℕ) : 𝓞 F) ∈ v.asIdeal` using `(hA _).1 (by simpa using h)`. Establish `h3` using `v.asIdeal.sub_mem (v.asIdeal.pow_mem_of_mem h1 N hN) h2`.

Rewrite `h3` using `[← Nat.cast_pow, hn]`. Conclude with `v.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 (by simpa using h3))`. Establish `hξ1 : A.valuation ξ ≤ 1` using `(valuation_eq_one_of_pow_eq_one A hn0 hξ.pow_eq_one).le`. Set `θ : Dec (F` to `F) A →* (ZMod n)ˣ := (hξ.autToPow F).comp (Dec (F := F) A).subtype`. Establish `hθ : ∀ (g : Dec (F` using `F) A) (k : ℕ), (θ g : ZMod n) = k ↔ g.1 ξ = ξ ^ k := fun g k => by`.

Establish `hu : IsPrimitiveRoot (hξ.isUnit hn0).unit n` using `IsPrimitiveRoot.coe_units_iff.mp (by simpa using hξ)`. Rewrite using `[← hξ.autToPow_spec F g.1]`. Express the relevant statement in the definitionally equal form `(θ g : ZMod n) = k ↔ ξ ^ (θ g : ZMod n).val = _`. Use `conv_lhs => rw [← ZMod.natCast_zmod_val (θ g : ZMod n)]`. Rewrite using `[ZMod.natCast_eq_natCast_iff]`.

Generalize the expression as in `(θ g : ZMod n).val = m`. Use `conv_lhs => rw [hu.eq_orderOf, ← pow_eq_pow_iff_modEq, Units.ext_iff]`. Simplify using the standard rewrite rules. Establish `hθ' : ∀ (g : Dec (F` using `F) A) (k : ℕ), A.valuation (g.1 ξ - ξ ^ k) < 1 → (θ g : ZMod n) = k := fun g k h => (hθ g k).2 (eq_of_pow_eq_one A hnv (by rw [← map_pow, hξ.pow_eq_one, map_one]) (by rw [← pow_mul, mul_comm, pow_mul, hξ.pow_eq_one, one_pow]) h)`. Establish `hI : ∀ σ : Dec (F` using `F) A, σ.1 ∈ Ine (F := F) A → θ σ = 1 := fun σ hσ => Units.ext (by simpa using hθ' σ 1 (by simpa using hσ.2 ξ hξ1))`.

Establish `hF : (θ φ : ZMod n) = (normV v : ℕ)` using `hθ' φ _ (hφ.2 ξ hξ1)`. Establish `ho : IsOpen (θ.ker : Set (Dec (F` using `F) A)) := by`. Establish `e : (θ.ker : Set (Dec (F` using `F) A)) = Subtype.val ⁻¹' {σ : G F Ω | σ ξ = ξ} := by`. Use extensionality with `g`. Use `hθ g 1` as an intermediate fact.

Rewrite `this` using `[pow_one, Nat.cast_one]`. Conclude with `Units.ext_iff.trans this`. Rewrite using `[e]`. Conclude with `(isOpen_setOf_apply (F := F) ξ (fun t => t = ξ)).preimage continuous_subtype_val`. Establish `h3 : θ φ ^ N = 1` using `Units.ext (by`.

Rewrite using `[Units.val_pow_eq_pow_val, hF, ← Nat.cast_pow, hn]`. Use the proof step `simp)`. Establish `hr : ∀ g, θ g ∈ Subgroup.zpowers (θ φ)`. Establish `h4 : ⊤ ≤ (Subgroup.zpowers (θ φ)).comap θ`. Rewrite using `[← closure_frob_sup_Ine F Ω A v hA φ hφ]`.

Use `Subgroup.topologicalClosure_minimal _ (sup_le (Subgroup.zpowers_le.2 (Subgroup.mem_zpowers _)) fun σ hσ => ?_) (Subgroup.isClosed_of_isOpen _ (Subgroup.isOpen_mono (fun σ hσ => ?_) ho))` and prove the remaining obligations. Rewrite using `[Subgroup.mem_comap, hI σ hσ]`. Conclude with `one_mem _`. Rewrite using `[Subgroup.mem_comap, MonoidHom.mem_ker.1 hσ]`. Conclude with `one_mem _`.

Conclude with `fun g => h4 (Subgroup.mem_top g)`. Establish `ht : θ t ^ N = 1`. Take `⟨b, hb⟩` from `hr t`. Rewrite using `[← hb, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, h3, one_zpow]`. Establish `h5 : θ φ ^ a = 1`.

Establish `h6 : θ (φ ^ a * t ^ N * i) = 1` using `Units.ext (by simpa using (hθ (φ ^ a * t ^ N * i) 1).2 (by simpa using hfix))`. Rewrite `h6` using `[map_mul, map_mul, map_pow, map_pow, ht, hI i hi, mul_one, mul_one]`. Then use the resulting hypothesis. Establish `h1 : ((θ φ ^ a : (ZMod n)ˣ) : ZMod n) = ((1 : ℕ) : ZMod n)`. Rewrite using `[Nat.cast_one]`. Conclude with `congrArg Units.val h5`.

Rewrite `h1` using `[Units.val_pow_eq_pow_val, hF, ← Nat.cast_pow, ZMod.natCast_eq_natCast_iff]`. Establish `h2` using `(Nat.modEq_iff_dvd' (Nat.one_le_pow _ _ (by omega))).1 h1.symm`. Establish `h4` using `pow_lt_pow_right₀ hq haN`. Establish `h7` using `Nat.eq_zero_of_dvd_of_lt h2 (by`. Use `Nat.one_le_pow a (normV v) (by omega)` as an intermediate fact.

Use the proof step `omega)`. Assume the negation of the conclusion as `h`. Use `one_lt_pow₀ hq h` as an intermediate fact. Use linear arithmetic over natural numbers and integers.
-/
theorem eq_zero_of_fixes_primitiveRoot : ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (A : ValuationSubring Ω) (v : HeightOneSpectrum (𝓞 F)), IsPlaceOver A v → ∀ φ : Dec (F := F) A, IsFrob (F := F) A (normV v) (φ : G F Ω) → ∀ N : ℕ, 0 < N → ∀ ξ : Ω, IsPrimitiveRoot ξ (normV v ^ N - 1) → ∀ (a : ℕ) (t i : Dec (F := F) A), a < N → (i : G F Ω) ∈ Ine (F := F) A → ((φ ^ a * t ^ N * i : Dec (F := F) A) : G F Ω) ξ = ξ → a = 0 := by
  intro F Ω _ _ _ _ _ A v hA φ hφ N hN ξ hξ' a t i haN hi hfix
  have : IsAlgClosed Ω := IsAlgClosure.isAlgClosed F
  have : CharZero Ω := charZero_of_injective_algebraMap (algebraMap F Ω).injective
  have hq := one_lt_normV v
  obtain ⟨n, hn⟩ : ∃ n, normV v ^ N = n + 1 :=
    ⟨_, (Nat.sub_add_cancel (Nat.one_le_pow _ _ (by omega))).symm⟩
  have hn0 : n ≠ 0 := by
    have := one_lt_pow₀ hq hN.ne'
    omega
  have : NeZero n := ⟨hn0⟩
  have : NeZero (n : Ω) := ⟨Nat.cast_ne_zero.2 hn0⟩
  have hξ : IsPrimitiveRoot ξ n := by
    have e : normV v ^ N - 1 = n := by omega
    rwa [e] at hξ'
  have hnv : ¬ A.valuation (n : Ω) < 1 := by
    intro h
    have h1 : ((normV v : ℕ) : 𝓞 F) ∈ v.asIdeal := by
      rw [← Ideal.Quotient.eq_zero_iff_mem, map_natCast, ← nsmul_one]
      exact card_nsmul_eq_zero'
    have h2 : ((n : ℕ) : 𝓞 F) ∈ v.asIdeal := (hA _).1 (by simpa using h)
    have h3 := v.asIdeal.sub_mem (v.asIdeal.pow_mem_of_mem h1 N hN) h2
    rw [← Nat.cast_pow, hn] at h3
    exact v.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 (by simpa using h3))
  have hξ1 : A.valuation ξ ≤ 1 := (valuation_eq_one_of_pow_eq_one A hn0 hξ.pow_eq_one).le
  let θ : Dec (F := F) A →* (ZMod n)ˣ := (hξ.autToPow F).comp (Dec (F := F) A).subtype
  have hθ : ∀ (g : Dec (F := F) A) (k : ℕ), (θ g : ZMod n) = k ↔ g.1 ξ = ξ ^ k := fun g k => by
    have hu : IsPrimitiveRoot (hξ.isUnit hn0).unit n :=
      IsPrimitiveRoot.coe_units_iff.mp (by simpa using hξ)
    rw [← hξ.autToPow_spec F g.1]
    change (θ g : ZMod n) = k ↔ ξ ^ (θ g : ZMod n).val = _
    conv_lhs => rw [← ZMod.natCast_zmod_val (θ g : ZMod n)]
    rw [ZMod.natCast_eq_natCast_iff]
    generalize (θ g : ZMod n).val = m
    conv_lhs => rw [hu.eq_orderOf, ← pow_eq_pow_iff_modEq, Units.ext_iff]
    simp
  have hθ' : ∀ (g : Dec (F := F) A) (k : ℕ), A.valuation (g.1 ξ - ξ ^ k) < 1 → (θ g : ZMod n) = k :=
    fun g k h => (hθ g k).2 (eq_of_pow_eq_one A hnv (by rw [← map_pow, hξ.pow_eq_one, map_one])
      (by rw [← pow_mul, mul_comm, pow_mul, hξ.pow_eq_one, one_pow]) h)
  have hI : ∀ σ : Dec (F := F) A, σ.1 ∈ Ine (F := F) A → θ σ = 1 := fun σ hσ =>
    Units.ext (by simpa using hθ' σ 1 (by simpa using hσ.2 ξ hξ1))
  have hF : (θ φ : ZMod n) = (normV v : ℕ) := hθ' φ _ (hφ.2 ξ hξ1)
  have ho : IsOpen (θ.ker : Set (Dec (F := F) A)) := by
    have e : (θ.ker : Set (Dec (F := F) A)) = Subtype.val ⁻¹' {σ : G F Ω | σ ξ = ξ} := by
      ext g
      have := hθ g 1
      rw [pow_one, Nat.cast_one] at this
      exact Units.ext_iff.trans this
    rw [e]
    exact (isOpen_setOf_apply (F := F) ξ (fun t => t = ξ)).preimage continuous_subtype_val
  have h3 : θ φ ^ N = 1 := Units.ext (by
    rw [Units.val_pow_eq_pow_val, hF, ← Nat.cast_pow, hn]; simp)
  have hr : ∀ g, θ g ∈ Subgroup.zpowers (θ φ) := by
    have h4 : ⊤ ≤ (Subgroup.zpowers (θ φ)).comap θ := by
      rw [← closure_frob_sup_Ine F Ω A v hA φ hφ]
      refine Subgroup.topologicalClosure_minimal _ (sup_le (Subgroup.zpowers_le.2
        (Subgroup.mem_zpowers _)) fun σ hσ => ?_) (Subgroup.isClosed_of_isOpen _
          (Subgroup.isOpen_mono (fun σ hσ => ?_) ho))
      · rw [Subgroup.mem_comap, hI σ hσ]
        exact one_mem _
      · rw [Subgroup.mem_comap, MonoidHom.mem_ker.1 hσ]
        exact one_mem _
    exact fun g => h4 (Subgroup.mem_top g)
  have ht : θ t ^ N = 1 := by
    obtain ⟨b, hb⟩ := hr t
    rw [← hb, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, h3, one_zpow]
  have h5 : θ φ ^ a = 1 := by
    have h6 : θ (φ ^ a * t ^ N * i) = 1 :=
      Units.ext (by simpa using (hθ (φ ^ a * t ^ N * i) 1).2 (by simpa using hfix))
    rwa [map_mul, map_mul, map_pow, map_pow, ht, hI i hi, mul_one, mul_one] at h6
  have h1 : ((θ φ ^ a : (ZMod n)ˣ) : ZMod n) = ((1 : ℕ) : ZMod n) := by
    rw [Nat.cast_one]; exact congrArg Units.val h5
  rw [Units.val_pow_eq_pow_val, hF, ← Nat.cast_pow, ZMod.natCast_eq_natCast_iff] at h1
  have h2 := (Nat.modEq_iff_dvd' (Nat.one_le_pow _ _ (by omega))).1 h1.symm
  have h4 := pow_lt_pow_right₀ hq haN
  have h7 := Nat.eq_zero_of_dvd_of_lt h2 (by
    have := Nat.one_le_pow a (normV v) (by omega)
    omega)
  by_contra h
  have := one_lt_pow₀ hq h
  omega

end GlobalTheory.CompanionTheory.TameAction

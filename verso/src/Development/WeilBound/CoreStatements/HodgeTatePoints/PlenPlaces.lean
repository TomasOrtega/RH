import Development.WeilBound.CoreStatements.HodgeTatePoints.IsMaximalOfNeBot
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PFiniteBirationalLength

namespace PositivityTheory.HtPt.Plen

open GroundTheory.FunctionField IsLocalRing IsDedekindDomain GroundTheory.Heights₂.Heights

/- English proof (translation)
Establish `hmax : (𝔫.under A).IsMaximal` using `Ideal.IsMaximal.under A 𝔫`. Establish `hu : 𝔫.under A = maximalIdeal A` using `IsLocalRing.eq_maximalIdeal hmax`. Use `haveI : 𝔫.LiesOver (maximalIdeal A) := ⟨hu.symm⟩`. Rewrite using `[Ideal.inertiaDeg_eq_of_isMaximal (maximalIdeal A) 𝔫]`. Use `letI : Field (A ⧸ maximalIdeal A) := Ideal.Quotient.field _`.

Use `letI : Field (B ⧸ 𝔫) := Ideal.Quotient.field _`. Use `haveI : IsScalarTower k (A ⧸ maximalIdeal A) (B ⧸ 𝔫) := by`. Use `IsScalarTower.of_algebraMap_eq (fun x => ?_)` and prove the remaining obligations. Rewrite using `[IsScalarTower.algebraMap_apply k B (B ⧸ 𝔫), IsScalarTower.algebraMap_apply k A B]`. Both sides reduce to the same expression.

Rewrite using `[mul_comm]`. Conclude with `Module.finrank_mul_finrank k (A ⧸ maximalIdeal A) (B ⧸ 𝔫)`.
-/
theorem inertiaDeg_mul (k A B : Type) [Field k] [CommRing A] [IsLocalRing A] [CommRing B]
    [Algebra k A] [Algebra A B] [Algebra k B] [IsScalarTower k A B] [Module.Finite A B]
    (𝔫 : Ideal B) [𝔫.IsMaximal] :
    𝔫.inertiaDeg A * Module.finrank k (ResidueField A) = Module.finrank k (B ⧸ 𝔫) := by
  have hmax : (𝔫.under A).IsMaximal := Ideal.IsMaximal.under A 𝔫
  have hu : 𝔫.under A = maximalIdeal A := IsLocalRing.eq_maximalIdeal hmax
  haveI : 𝔫.LiesOver (maximalIdeal A) := ⟨hu.symm⟩
  rw [Ideal.inertiaDeg_eq_of_isMaximal (maximalIdeal A) 𝔫]
  letI : Field (A ⧸ maximalIdeal A) := Ideal.Quotient.field _
  letI : Field (B ⧸ 𝔫) := Ideal.Quotient.field _
  haveI : IsScalarTower k (A ⧸ maximalIdeal A) (B ⧸ 𝔫) := by
    refine IsScalarTower.of_algebraMap_eq (fun x => ?_)
    rw [IsScalarTower.algebraMap_apply k B (B ⧸ 𝔫), IsScalarTower.algebraMap_apply k A B]
    rfl
  rw [mul_comm]
  exact Module.finrank_mul_finrank k (A ⧸ maximalIdeal A) (B ⧸ 𝔫)

variable {k K : Type} [Field k] [Field K] [Algebra k K] [IsFunctionField k K]

omit [IsFunctionField k K] in
/- English proof (translation)
Establish `hker : RingHom.ker (resHom B v hv) = p`. Use extensionality with `b`. Rewrite using `[RingHom.mem_ker, hp]`. Rewrite using `[Place.deg, ← hker]`. Conclude with `(Ideal.quotientKerAlgEquivOfSurjective hs).toLinearEquiv.finrank_eq.symm`.
-/
theorem deg_eq_of_surjective (B : Type) [CommRing B] [Algebra k B] [Algebra B K]
    [IsScalarTower k B K] (v : Place k K) (hv : ∀ b : B, algebraMap B K b ∈ v.ring) (p : Ideal B)
    (hp : ∀ b, b ∈ p ↔ resHom B v hv b = 0) (hs : Function.Surjective (resHom B v hv)) :
    v.deg = Module.finrank k (B ⧸ p) := by
  have hker : RingHom.ker (resHom B v hv) = p := by
    ext b
    rw [RingHom.mem_ker, hp]
  rw [Place.deg, ← hker]
  exact (Ideal.quotientKerAlgEquivOfSurjective hs).toLinearEquiv.finrank_eq.symm

omit [IsFunctionField k K] in

/- English proof (translation)
Use `haveI : P.asIdeal.IsMaximal := P.isMaximal`. Establish `hv : ∀ b : B, algebraMap B K b ∈ (Place.ofHeightOneSpectrum B hk P).ring` using `Place.algebraMap_mem_ofHeightOneSpectrum B hk P`. Establish `hres : ∀ b : B, resHom B (Place.ofHeightOneSpectrum B hk P) hv b = IsLocalRing.residue _ (algebraMap B (HeightOneSpectrum.valuationSubringAtPrime K P) b)` using `fun b => rfl`. Establish `hp : ∀ b, b ∈ P.asIdeal ↔ resHom B (Place.ofHeightOneSpectrum B hk P) hv b = 0`. Introduce `b`.

Rewrite using `[hres, IsLocalRing.residue_eq_zero_iff, ← Ideal.mem_under, IsLocalization.AtPrime.under_maximalIdeal (HeightOneSpectrum.valuationSubringAtPrime K P) P.asIdeal]`. Establish `hs : Function.Surjective (resHom B (Place.ofHeightOneSpectrum B hk P) hv)`. Introduce `y`. Take `⟨o, rfl⟩` from `IsLocalRing.residue_surjective y`. Take `⟨x, hx⟩` from `(IsLocalization.AtPrime.equivQuotMaximalIdeal P.asIdeal (HeightOneSpectrum.valuationSubringAtPrime K P)).surjective (Ideal.Quotient.mk _ o)`.

Take `⟨b, rfl⟩` from `Ideal.Quotient.mk_surjective x`. Use `⟨b, ?_⟩` and prove the remaining obligations. Rewrite using `[hres]`. Rewrite `hx` using `[IsLocalization.AtPrime.equivQuotMaximalIdeal_apply_mk]`. Conclude with `hx`.

Conclude with `deg_eq_of_surjective B (Place.ofHeightOneSpectrum B hk P) hv P.asIdeal hp hs`.
-/
theorem deg_ofHeightOneSpectrum (B : Type) [CommRing B] [IsDedekindDomain B] [Algebra B K]
    [IsFractionRing B K] [Algebra k B] [IsScalarTower k B K]
    (hk : ∀ c : k, algebraMap k K c ∈ (algebraMap B K).range) (P : HeightOneSpectrum B) :
    (Place.ofHeightOneSpectrum B hk P).deg = Module.finrank k (B ⧸ P.asIdeal) := by
  haveI : P.asIdeal.IsMaximal := P.isMaximal
  have hv : ∀ b : B, algebraMap B K b ∈ (Place.ofHeightOneSpectrum B hk P).ring :=
    Place.algebraMap_mem_ofHeightOneSpectrum B hk P
  have hres : ∀ b : B, resHom B (Place.ofHeightOneSpectrum B hk P) hv b =
      IsLocalRing.residue _ (algebraMap B (HeightOneSpectrum.valuationSubringAtPrime K P) b) :=
    fun b => rfl
  have hp : ∀ b, b ∈ P.asIdeal ↔ resHom B (Place.ofHeightOneSpectrum B hk P) hv b = 0 := by
    intro b
    rw [hres, IsLocalRing.residue_eq_zero_iff, ← Ideal.mem_under,
      IsLocalization.AtPrime.under_maximalIdeal (HeightOneSpectrum.valuationSubringAtPrime K P)
        P.asIdeal]
  have hs : Function.Surjective (resHom B (Place.ofHeightOneSpectrum B hk P) hv) := by
    intro y
    obtain ⟨o, rfl⟩ := IsLocalRing.residue_surjective y
    obtain ⟨x, hx⟩ := (IsLocalization.AtPrime.equivQuotMaximalIdeal P.asIdeal
      (HeightOneSpectrum.valuationSubringAtPrime K P)).surjective (Ideal.Quotient.mk _ o)
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective x
    refine ⟨b, ?_⟩
    rw [hres]
    rw [IsLocalization.AtPrime.equivQuotMaximalIdeal_apply_mk] at hx
    exact hx
  exact deg_eq_of_surjective B (Place.ofHeightOneSpectrum B hk P) hv P.asIdeal hp hs

/- English proof (translation)
Proceed by induction on `n with`. Consider the case `zero`. Establish `: Subsingleton (B ⧸ P ^ 0)`. Rewrite using `[pow_zero, Ideal.one_eq_top]`. Conclude with `Ideal.Quotient.subsingleton_iff.mpr rfl`.

Rewrite using `[Module.length_eq_zero]`. Simplify using the standard rewrite rules. Consider the case `succ n ih`. Choose the witnesses or unpack the hypotheses as in `⟨a, ha, hna⟩ : ∃ a ∈ P ^ n, a ∉ P ^ (n + 1) := by`. Assume the negation of the conclusion as `h`.

Use `push_neg at h`. Conclude with `(Ideal.pow_succ_lt_pow hP n).not_ge h`. Set `φ : (B ⧸ P) →ₗ[B] (B ⧸ P ^ (n + 1))` to `Submodule.mapQ P (P ^ (n + 1)) (LinearMap.mulLeft B a) (by`. Introduce `x hx`. Simplify using `only [Submodule.mem_comap, LinearMap.mulLeft_apply]`.

Rewrite using `[pow_succ]`. Conclude with `Ideal.mul_mem_mul ha hx)`. Set `ψ : (B ⧸ P ^ (n + 1)) →ₗ[B] (B ⧸ P ^ n)` to `Submodule.factor (Ideal.pow_le_pow_right n.le_succ)`. Establish `hφ : Function.Injective φ`. Rewrite using `[← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']`.

Introduce `x hx`. Take `⟨c, rfl⟩` from `Submodule.Quotient.mk_surjective P x`. Establish `h1 : a * c ∈ P ^ (n + 1)`. Use `hx` as an intermediate fact. Simplify using `only [φ, Submodule.mapQ_apply, LinearMap.mulLeft_apply, Submodule.Quotient.mk_eq_zero] at this`.

Conclude with `this`. Rewrite using `[Submodule.Quotient.mk_eq_zero]`. Conclude with `(Ideal.IsPrime.mem_pow_mul P h1).resolve_left hna`. Establish `hψ : Function.Surjective ψ` using `Submodule.factor_surjective _`. Establish `hex : Function.Exact φ ψ`.

Introduce `y`. Take `⟨y, rfl⟩` from `Submodule.Quotient.mk_surjective (P ^ (n + 1)) y`. Prove the components needed by the constructor for the conclusion. Introduce `hy`. Establish `hy' : y ∈ P ^ n`.

Express the relevant statement in the definitionally equal form `(Submodule.Quotient.mk y : B ⧸ P ^ n) = 0 at hy`. Rewrite `hy` using `[Submodule.Quotient.mk_eq_zero]`. Then use the resulting hypothesis. Establish `hsup : y ∈ Ideal.span {a} ⊔ P ^ (n + 1)`. Establish `ha' : Ideal.span {a} ≤ P ^ n` using `(Ideal.span_singleton_le_iff_mem _).mpr ha`. Establish `hna' : ¬ Ideal.span {a} ≤ P ^ (n + 1)` using `fun h => hna ((Ideal.span_singleton_le_iff_mem _).mp h)`.

Establish `hspan0 : Ideal.span {a} ≠ ⊥` using `fun h => hna' (h ▸ bot_le)`. Establish `hirr : Irreducible P` using `((Ideal.prime_iff_isPrime hP).mpr inferInstance).irreducible`. Rewrite using `[sup_comm, Ideal.irreducible_pow_sup hspan0 hirr, Ideal.count_normalizedFactors_eq ha' hna', min_eq_left n.le_succ]`. Conclude with `hy'`. Take `⟨u, hu, z, hz, rfl⟩` from `Submodule.mem_sup.mp hsup`.

Take `⟨c, rfl⟩` from `Ideal.mem_span_singleton'.mp hu`. Use `⟨Submodule.Quotient.mk c, ?_⟩` and prove the remaining obligations. Simplify using `only [φ, Submodule.mapQ_apply, LinearMap.mulLeft_apply]`. Rewrite using `[Submodule.Quotient.eq]`. Establish `: a * c - (c * a + z) = -z` using `by ring`.

Rewrite using `[this]`. Conclude with `neg_mem hz`. Introduce and unpack `⟨x, hx⟩`. Rewrite using `[← hx]`. Take `⟨c, rfl⟩` from `Submodule.Quotient.mk_surjective P x`.

Express the relevant statement in the definitionally equal form `(Submodule.Quotient.mk (a * c) : B ⧸ P ^ n) = 0`. Rewrite using `[Submodule.Quotient.mk_eq_zero]`. Conclude with `Ideal.mul_mem_right c _ ha`. Establish `hlen` using `Module.length_eq_add_of_exact (φ.restrictScalars A) (ψ.restrictScalars A) hφ hψ hex`. Rewrite using `[hlen, ih, GroundTheory.Heights₂.Heights.NumbersDVR.FiniteBirationalLength.length_quot_maximal_eq_inertiaDeg P]`.

Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
private theorem length_quotient_pow_eq_mul_inertiaDeg {A B : Type} [CommRing A] [IsLocalRing A] [CommRing B]
    [IsDedekindDomain B] [Algebra A B] [Module.Finite A B] (P : Ideal B) [P.IsMaximal]
    (hP : P ≠ ⊥) (n : ℕ) :
    Module.length A (B ⧸ P ^ n) = n * ((P.inertiaDeg A : ℕ) : ℕ∞) := by
  induction n with
  | zero =>
    have : Subsingleton (B ⧸ P ^ 0) := by
      rw [pow_zero, Ideal.one_eq_top]
      exact Ideal.Quotient.subsingleton_iff.mpr rfl
    rw [Module.length_eq_zero]
    simp
  | succ n ih =>
    obtain ⟨a, ha, hna⟩ : ∃ a ∈ P ^ n, a ∉ P ^ (n + 1) := by
      by_contra h
      push_neg at h
      exact (Ideal.pow_succ_lt_pow hP n).not_ge h
    let φ : (B ⧸ P) →ₗ[B] (B ⧸ P ^ (n + 1)) :=
      Submodule.mapQ P (P ^ (n + 1)) (LinearMap.mulLeft B a) (by
        intro x hx
        simp only [Submodule.mem_comap, LinearMap.mulLeft_apply]
        rw [pow_succ]
        exact Ideal.mul_mem_mul ha hx)
    let ψ : (B ⧸ P ^ (n + 1)) →ₗ[B] (B ⧸ P ^ n) :=
      Submodule.factor (Ideal.pow_le_pow_right n.le_succ)
    have hφ : Function.Injective φ := by
      rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
      intro x hx
      obtain ⟨c, rfl⟩ := Submodule.Quotient.mk_surjective P x
      have h1 : a * c ∈ P ^ (n + 1) := by
        have := hx
        simp only [φ, Submodule.mapQ_apply, LinearMap.mulLeft_apply,
          Submodule.Quotient.mk_eq_zero] at this
        exact this
      rw [Submodule.Quotient.mk_eq_zero]
      exact (Ideal.IsPrime.mem_pow_mul P h1).resolve_left hna
    have hψ : Function.Surjective ψ := Submodule.factor_surjective _
    have hex : Function.Exact φ ψ := by
      intro y
      obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective (P ^ (n + 1)) y
      constructor
      · intro hy
        have hy' : y ∈ P ^ n := by
          change (Submodule.Quotient.mk y : B ⧸ P ^ n) = 0 at hy
          rwa [Submodule.Quotient.mk_eq_zero] at hy
        have hsup : y ∈ Ideal.span {a} ⊔ P ^ (n + 1) := by
          have ha' : Ideal.span {a} ≤ P ^ n := (Ideal.span_singleton_le_iff_mem _).mpr ha
          have hna' : ¬ Ideal.span {a} ≤ P ^ (n + 1) := fun h =>
            hna ((Ideal.span_singleton_le_iff_mem _).mp h)
          have hspan0 : Ideal.span {a} ≠ ⊥ := fun h => hna' (h ▸ bot_le)
          have hirr : Irreducible P := ((Ideal.prime_iff_isPrime hP).mpr inferInstance).irreducible
          rw [sup_comm, Ideal.irreducible_pow_sup hspan0 hirr, Ideal.count_normalizedFactors_eq ha' hna',
            min_eq_left n.le_succ]
          exact hy'
        obtain ⟨u, hu, z, hz, rfl⟩ := Submodule.mem_sup.mp hsup
        obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.mp hu
        refine ⟨Submodule.Quotient.mk c, ?_⟩
        simp only [φ, Submodule.mapQ_apply, LinearMap.mulLeft_apply]
        rw [Submodule.Quotient.eq]
        have : a * c - (c * a + z) = -z := by ring
        rw [this]
        exact neg_mem hz
      · rintro ⟨x, hx⟩
        rw [← hx]
        obtain ⟨c, rfl⟩ := Submodule.Quotient.mk_surjective P x
        change (Submodule.Quotient.mk (a * c) : B ⧸ P ^ n) = 0
        rw [Submodule.Quotient.mk_eq_zero]
        exact Ideal.mul_mem_right c _ ha
    have hlen := Module.length_eq_add_of_exact (φ.restrictScalars A) (ψ.restrictScalars A) hφ hψ hex
    rw [hlen, ih, GroundTheory.Heights₂.Heights.NumbersDVR.FiniteBirationalLength.length_quot_maximal_eq_inertiaDeg P]
    push_cast
    ring

/- English proof (translation)
Establish `key : ∀ x y : K, v x = v y → w x = w y` using `fun x y hxy => h.val_eq.mp hxy`. Establish `hπ0 : π ≠ 0`. Introduce and unpack `rfl`. Rewrite `hπ` using `[map_zero]`. Conclude with `WithZero.exp_ne_zero hπ.symm`.

Establish `hexp : ∀ (c : ℤ) (a : ℤ), (WithZero.exp c) ^ a = WithZero.exp (a * c)`. Introduce `c a`. Rewrite using `[← WithZero.exp_zsmul, smul_eq_mul]`. Establish `hvπ : ∀ a : ℤ, v (π ^ a) = WithZero.exp (-a)`. Introduce `a`.

Rewrite using `[map_zpow₀, hπ, hexp]`. Put the polynomial expressions in normal form. Establish `hwπ0 : w π ≠ 0` using `(Valuation.ne_zero_iff w).mpr hπ0`. Establish `hwπ : w π = WithZero.exp (WithZero.log (w π))` using `(WithZero.exp_log hwπ0).symm`. Establish `hρ0 : ρ ≠ 0`.

Introduce and unpack `rfl`. Rewrite `hρ` using `[map_zero]`. Conclude with `WithZero.exp_ne_zero hρ.symm`. Establish `hvρ : v ρ = WithZero.exp (WithZero.log (v ρ))` using `(WithZero.exp_log ((Valuation.ne_zero_iff v).mpr hρ0)).symm`. Establish `h1 : w ρ = w (π ^ (-WithZero.log (v ρ)))` using `key _ _ (by rw [hvπ, neg_neg]; exact hvρ)`.

Rewrite `h1` using `[hρ, map_zpow₀, hwπ, hexp, WithZero.exp_inj]`. Establish `hc : WithZero.log (w π) = 1 ∨ WithZero.log (w π) = -1`. Establish `hm : WithZero.log (w π) * WithZero.log (v ρ) = 1` using `by linear_combination h1`. Conclude with `Int.eq_one_or_neg_one_of_mul_eq_one hm`. Establish `hc' : WithZero.log (w π) = -1`.

Break down `hc with hc | hc` into its components or cases. It suffices to derive a contradiction. Establish `hle : v π ≤ v 1`. Rewrite using `[hπ, map_one, ← WithZero.exp_zero, WithZero.exp_le_exp]`. Evaluate the numerical expressions.

Establish `hle'` using `(h π 1).mp hle`. Rewrite `hle'` using `[hwπ, hc, map_one, ← WithZero.exp_zero, WithZero.exp_le_exp]`. Evaluate the numerical expressions using `at hle'`. Conclude with `hc`. Use extensionality with `x`.

Distinguish the cases in `hx : x = 0`. Simplify using `[hx]`. Establish `hvx : v x = WithZero.exp (WithZero.log (v x))` using `(WithZero.exp_log ((Valuation.ne_zero_iff v).mpr hx)).symm`. Establish `h2 : w x = w (π ^ (-WithZero.log (v x)))` using `key _ _ (by rw [hvπ, neg_neg]; exact hvx)`. Rewrite using `[h2, map_zpow₀, hwπ, hexp, hc', hvx, WithZero.log_exp]`.

Put the polynomial expressions in normal form.
-/
private theorem valuation_eq_of_isEquiv_of_uniformizers {K : Type} [Field K]
    (v w : Valuation K (WithZero (Multiplicative ℤ))) (h : v.IsEquiv w)
    (π : K) (hπ : v π = WithZero.exp (-1)) (ρ : K) (hρ : w ρ = WithZero.exp (-1)) :
    v = w := by
  have key : ∀ x y : K, v x = v y → w x = w y := fun x y hxy => h.val_eq.mp hxy
  have hπ0 : π ≠ 0 := by
    rintro rfl
    rw [map_zero] at hπ
    exact WithZero.exp_ne_zero hπ.symm
  have hexp : ∀ (c : ℤ) (a : ℤ), (WithZero.exp c) ^ a = WithZero.exp (a * c) := by
    intro c a
    rw [← WithZero.exp_zsmul, smul_eq_mul]
  have hvπ : ∀ a : ℤ, v (π ^ a) = WithZero.exp (-a) := by
    intro a
    rw [map_zpow₀, hπ, hexp]
    ring_nf
  have hwπ0 : w π ≠ 0 := (Valuation.ne_zero_iff w).mpr hπ0
  have hwπ : w π = WithZero.exp (WithZero.log (w π)) := (WithZero.exp_log hwπ0).symm
  have hρ0 : ρ ≠ 0 := by
    rintro rfl
    rw [map_zero] at hρ
    exact WithZero.exp_ne_zero hρ.symm
  have hvρ : v ρ = WithZero.exp (WithZero.log (v ρ)) :=
    (WithZero.exp_log ((Valuation.ne_zero_iff v).mpr hρ0)).symm
  have h1 : w ρ = w (π ^ (-WithZero.log (v ρ))) := key _ _ (by rw [hvπ, neg_neg]; exact hvρ)
  rw [hρ, map_zpow₀, hwπ, hexp, WithZero.exp_inj] at h1
  have hc : WithZero.log (w π) = 1 ∨ WithZero.log (w π) = -1 := by
    have hm : WithZero.log (w π) * WithZero.log (v ρ) = 1 := by linear_combination h1
    exact Int.eq_one_or_neg_one_of_mul_eq_one hm
  have hc' : WithZero.log (w π) = -1 := by
    rcases hc with hc | hc
    · exfalso
      have hle : v π ≤ v 1 := by
        rw [hπ, map_one, ← WithZero.exp_zero, WithZero.exp_le_exp]
        norm_num
      have hle' := (h π 1).mp hle
      rw [hwπ, hc, map_one, ← WithZero.exp_zero, WithZero.exp_le_exp] at hle'
      norm_num at hle'
    · exact hc
  ext x
  by_cases hx : x = 0
  · simp [hx]
  have hvx : v x = WithZero.exp (WithZero.log (v x)) :=
    (WithZero.exp_log ((Valuation.ne_zero_iff v).mpr hx)).symm
  have h2 : w x = w (π ^ (-WithZero.log (v x))) := key _ _ (by rw [hvπ, neg_neg]; exact hvx)
  rw [h2, map_zpow₀, hwπ, hexp, hc', hvx, WithZero.log_exp]
  ring_nf

/- English proof (translation)
Use extensionality with `x`. Rewrite using `[Valuation.mem_valuationSubring_iff]`. Distinguish the cases in `hx : x = 0`. Simplify using `only [hx, map_zero, zero_le', true_iff]`. Conclude with `v.ring.zero_mem`.

Rewrite using `[← v.ord_nonneg_iff hx, Place.ord]`. Establish `hne : v.valuation x ≠ 0` using `(Valuation.ne_zero_iff _).mpr hx`. Use `conv_lhs => rw [← WithZero.exp_log hne]`. Rewrite using `[← WithZero.exp_zero, WithZero.exp_le_exp]`. Use linear arithmetic over natural numbers and integers.
-/
private theorem place_valuation_valuationSubring_eq_ring {k K : Type} [Field k] [Field K] [Algebra k K]
    [IsFunctionField k K] (v : Place k K) : v.valuation.valuationSubring = v.ring := by
  ext x
  rw [Valuation.mem_valuationSubring_iff]
  by_cases hx : x = 0
  · simp only [hx, map_zero, zero_le', true_iff]
    exact v.ring.zero_mem
  · rw [← v.ord_nonneg_iff hx, Place.ord]
    have hne : v.valuation x ≠ 0 := (Valuation.ne_zero_iff _).mpr hx
    conv_lhs => rw [← WithZero.exp_log hne]
    rw [← WithZero.exp_zero, WithZero.exp_le_exp]
    omega

/- English proof (translation)
Use `set v := Place.ofHeightOneSpectrum B hk P with hv`. Take `⟨π, hπ⟩` from `v.exists_ord_eq_one`. Establish `hπ0 : π ≠ 0`. Introduce and unpack `rfl`. Rewrite `hπ` using `[v.ord_zero]`.

Conclude with `zero_ne_one hπ`. Take `⟨ρ, hρ⟩` from `P.valuation_exists_uniformizer K`. Use `valuation_eq_of_isEquiv_of_uniformizers _ _ ?_ π ?_ ρ hρ` and prove the remaining obligations. Rewrite using `[Valuation.isEquiv_iff_valuationSubring, place_valuation_valuationSubring_eq_ring, ← HeightOneSpectrum.valuationSubringAtPrime_eq_valuationSubring]`. Establish `hne : v.valuation π ≠ 0` using `(Valuation.ne_zero_iff _).mpr hπ0`.

Rewrite using `[← WithZero.exp_log hne, WithZero.exp_inj]`. Rewrite `hπ` using `[Place.ord]`. Use linear arithmetic over natural numbers and integers.
-/
private theorem ofHeightOneSpectrum_valuation_eq {k K B : Type} [Field k] [Field K] [Algebra k K]
    [IsFunctionField k K] [CommRing B] [IsDedekindDomain B] [Algebra B K] [IsFractionRing B K]
    (hk : ∀ c : k, algebraMap k K c ∈ (algebraMap B K).range) (P : HeightOneSpectrum B) :
    (Place.ofHeightOneSpectrum B hk P).valuation = P.valuation K := by
  set v := Place.ofHeightOneSpectrum B hk P with hv
  obtain ⟨π, hπ⟩ := v.exists_ord_eq_one
  have hπ0 : π ≠ 0 := by
    rintro rfl
    rw [v.ord_zero] at hπ
    exact zero_ne_one hπ
  obtain ⟨ρ, hρ⟩ := P.valuation_exists_uniformizer K
  refine valuation_eq_of_isEquiv_of_uniformizers _ _ ?_ π ?_ ρ hρ
  · rw [Valuation.isEquiv_iff_valuationSubring, place_valuation_valuationSubring_eq_ring,
      ← HeightOneSpectrum.valuationSubringAtPrime_eq_valuationSubring]
  · have hne : v.valuation π ≠ 0 := (Valuation.ne_zero_iff _).mpr hπ0
    rw [← WithZero.exp_log hne, WithZero.exp_inj]
    rw [Place.ord] at hπ
    omega

/- English proof (translation)
Rewrite using `[Place.ord, ofHeightOneSpectrum_valuation_eq, HeightOneSpectrum.valuation_of_algebraMap, HeightOneSpectrum.intValuation_if_neg _ hb, WithZero.log_exp, neg_neg]`.
-/
private theorem ofHeightOneSpectrum_ord_eq_count {k K B : Type} [Field k] [Field K] [Algebra k K]
    [IsFunctionField k K] [CommRing B] [IsDedekindDomain B] [Algebra B K] [IsFractionRing B K]
    (hk : ∀ c : k, algebraMap k K c ∈ (algebraMap B K).range) (P : HeightOneSpectrum B)
    (b : B) (hb : b ≠ 0) :
    (Place.ofHeightOneSpectrum B hk P).ord (algebraMap B K b) =
      ((Associates.mk P.asIdeal).count (Associates.mk (Ideal.span {b})).factors : ℤ) := by
  rw [Place.ord, ofHeightOneSpectrum_valuation_eq, HeightOneSpectrum.valuation_of_algebraMap,
    HeightOneSpectrum.intValuation_if_neg _ hb, WithZero.log_exp, neg_neg]

/- English proof (translation)
Set `e : HeightOneSpectrum B → ℕ` to `fun P => (Associates.mk P.asIdeal).count (Associates.mk I).factors`. Establish `hprod : ∏ P, P.asIdeal ^ e P = I`. Establish `h` using `Ideal.finprod_heightOneSpectrum_factorization hI`. Rewrite `h` using `[finprod_eq_prod_of_fintype]`. Conclude with `h`.

Set `φ` to `HeightOneSpectrum.quotientEquivPiOfProdEq I (fun P => P) e (fun _ _ h => h) hprod`. Set `ψ : (B ⧸ I) ≃ₗ[A] (∀ P : HeightOneSpectrum B, B ⧸ P.asIdeal ^ e P)` to `{ φ.toAddEquiv with map_smul' := by`. Introduce `a x`. Take `⟨x, rfl⟩` from `Ideal.Quotient.mk_surjective x`. Use `rfl }`.

Rewrite using `[ψ.length_eq, Module.length_pi_of_fintype]`. Use `push_cast`. Use `Finset.sum_congr rfl (fun P _ => ?_)` and prove the remaining obligations. Use `haveI : P.asIdeal.IsMaximal := P.isMaximal`. Rewrite using `[length_quotient_pow_eq_mul_inertiaDeg P.asIdeal P.ne_bot]`.
-/
private theorem length_quotient_eq_sum_count_mul_inertiaDeg {A B : Type} [CommRing A] [IsLocalRing A] [CommRing B]
    [IsDedekindDomain B] [Algebra A B] [Module.Finite A B] [Fintype (HeightOneSpectrum B)]
    (I : Ideal B) (hI : I ≠ ⊥) :
    Module.length A (B ⧸ I) = ∑ P : HeightOneSpectrum B,
      (((Associates.mk P.asIdeal).count (Associates.mk I).factors * P.asIdeal.inertiaDeg A : ℕ) : ℕ∞) := by
  classical
  let e : HeightOneSpectrum B → ℕ := fun P => (Associates.mk P.asIdeal).count (Associates.mk I).factors
  have hprod : ∏ P, P.asIdeal ^ e P = I := by
    have h := Ideal.finprod_heightOneSpectrum_factorization hI
    rw [finprod_eq_prod_of_fintype] at h
    exact h
  let φ := HeightOneSpectrum.quotientEquivPiOfProdEq I (fun P => P) e (fun _ _ h => h) hprod
  let ψ : (B ⧸ I) ≃ₗ[A] (∀ P : HeightOneSpectrum B, B ⧸ P.asIdeal ^ e P) :=
    { φ.toAddEquiv with
      map_smul' := by
        intro a x
        obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
        rfl }
  rw [ψ.length_eq, Module.length_pi_of_fintype]
  push_cast
  refine Finset.sum_congr rfl (fun P _ => ?_)
  haveI : P.asIdeal.IsMaximal := P.isMaximal
  rw [length_quotient_pow_eq_mul_inertiaDeg P.asIdeal P.ne_bot]

/- English proof (translation)
Use `set g := algebraMap A B f with hg`. Use `set R : Submodule A B := LinearMap.range (Algebra.linearMap A B) with hR`. Use `set fR : Submodule A B := Submodule.span A {g} with hfR`. Establish `hfRR : fR ≤ R`. Rewrite using `[hfR, Submodule.span_le, Set.singleton_subset_iff]`.

Conclude with `⟨f, rfl⟩`. Set `φ1 : (A ⧸ Ideal.span {f}) →ₗ[A] (B ⧸ fR)` to `Submodule.mapQ (Ideal.span {f}) fR (Algebra.linearMap A B) (by`. Introduce `a ha`. Take `⟨c, rfl⟩` from `Ideal.mem_span_singleton'.mp ha`. Simplify using `only [Submodule.mem_comap, Algebra.linearMap_apply]`.

Rewrite using `[Submodule.mem_span_singleton]`. Conclude with `⟨c, by rw [map_mul, Algebra.smul_def]⟩)`. Set `ψ1 : (B ⧸ fR) →ₗ[A] (B ⧸ R)` to `Submodule.factor hfRR`. Establish `h1inj : Function.Injective φ1`. Rewrite using `[← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']`.

Introduce `x hx`. Take `⟨a, rfl⟩` from `Submodule.Quotient.mk_surjective _ x`. Express the relevant statement in the definitionally equal form `(Submodule.Quotient.mk (algebraMap A B a) : B ⧸ fR) = 0 at hx`. Rewrite `hx` using `[Submodule.Quotient.mk_eq_zero, Submodule.mem_span_singleton]`. Take `⟨c, hc⟩` from `hx`.

Rewrite using `[Submodule.Quotient.mk_eq_zero, Ideal.mem_span_singleton']`. Use `⟨c, hAB ?_⟩` and prove the remaining obligations. Rewrite using `[map_mul, ← hc, Algebra.smul_def]`. Establish `h1sur : Function.Surjective ψ1` using `Submodule.factor_surjective hfRR`. Establish `h1ex : Function.Exact φ1 ψ1`.

Introduce `y`. Take `⟨b, rfl⟩` from `Submodule.Quotient.mk_surjective _ y`. Prove the components needed by the constructor for the conclusion. Introduce `hy`. Express the relevant statement in the definitionally equal form `(Submodule.Quotient.mk b : B ⧸ R) = 0 at hy`.

Rewrite `hy` using `[Submodule.Quotient.mk_eq_zero]`. Take `⟨a, rfl⟩` from `hy`. Conclude with `⟨Submodule.Quotient.mk a, rfl⟩`. Introduce and unpack `⟨x, hx⟩`. Rewrite using `[← hx]`.

Take `⟨a, rfl⟩` from `Submodule.Quotient.mk_surjective _ x`. Express the relevant statement in the definitionally equal form `(Submodule.Quotient.mk (algebraMap A B a) : B ⧸ R) = 0`. Rewrite using `[Submodule.Quotient.mk_eq_zero]`. Conclude with `⟨a, rfl⟩`. Set `φ2 : (B ⧸ R) →ₗ[A] (B ⧸ fR)` to `Submodule.mapQ R fR (LinearMap.mulLeft A g) (by`.

Introduce and unpack `_ ⟨a, rfl⟩`. Simplify using `only [Submodule.mem_comap, LinearMap.mulLeft_apply, Algebra.linearMap_apply]`. Rewrite using `[Submodule.mem_span_singleton]`. Conclude with `⟨a, by rw [Algebra.smul_def, mul_comm]⟩)`. Set `ψ2 : (B ⧸ fR) →ₗ[A] (B ⧸ Ideal.span {g})` to `fR.liftQ (Ideal.Quotient.mkₐ A (Ideal.span {g})).toLinearMap (by`.

Rewrite using `[hfR, Submodule.span_le, Set.singleton_subset_iff]`. Simplify using `only [SetLike.mem_coe, LinearMap.mem_ker, AlgHom.toLinearMap_apply, Ideal.Quotient.mkₐ_eq_mk]`. Conclude with `Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self g))`. Establish `h2inj : Function.Injective φ2`. Rewrite using `[← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']`.

Introduce `x hx`. Take `⟨b, rfl⟩` from `Submodule.Quotient.mk_surjective _ x`. Express the relevant statement in the definitionally equal form `(Submodule.Quotient.mk (g * b) : B ⧸ fR) = 0 at hx`. Rewrite `hx` using `[Submodule.Quotient.mk_eq_zero, Submodule.mem_span_singleton]`. Take `⟨c, hc⟩` from `hx`.

Rewrite using `[Submodule.Quotient.mk_eq_zero]`. Use `⟨c, ?_⟩` and prove the remaining obligations. Rewrite `hc` using `[Algebra.smul_def]`. Apply `mul_left_cancel₀ hf` to reduce the goal to its premises. Rewrite using `[Algebra.linearMap_apply, ← hc, mul_comm]`.

Establish `h2sur : Function.Surjective ψ2`. Introduce `y`. Take `⟨b, rfl⟩` from `Ideal.Quotient.mk_surjective y`. Conclude with `⟨Submodule.Quotient.mk b, rfl⟩`. Establish `h2ex : Function.Exact φ2 ψ2`.

Introduce `y`. Take `⟨b, rfl⟩` from `Submodule.Quotient.mk_surjective _ y`. Prove the components needed by the constructor for the conclusion. Introduce `hy`. Express the relevant statement in the definitionally equal form `Ideal.Quotient.mk (Ideal.span {g}) b = 0 at hy`.

Rewrite `hy` using `[Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton']`. Take `⟨x, rfl⟩` from `hy`. Use `⟨Submodule.Quotient.mk x, ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `(Submodule.Quotient.mk (g * x) : B ⧸ fR) = Submodule.Quotient.mk (x * g)`. Rewrite using `[mul_comm]`.

Introduce and unpack `⟨x, hx⟩`. Rewrite using `[← hx]`. Take `⟨b, rfl⟩` from `Submodule.Quotient.mk_surjective _ x`. Express the relevant statement in the definitionally equal form `Ideal.Quotient.mk (Ideal.span {g}) (g * b) = 0`. Rewrite using `[Ideal.Quotient.eq_zero_iff_mem]`.

Conclude with `Ideal.mul_mem_right b _ (Ideal.mem_span_singleton_self g)`. Establish `e1` using `Module.length_eq_add_of_exact φ1 ψ1 h1inj h1sur h1ex`. Establish `e2` using `Module.length_eq_add_of_exact φ2 ψ2 h2inj h2sur h2ex`. Establish `e3 : Module.length A (B ⧸ R) + Module.length A (A ⧸ Ideal.span {f}) = Module.length A (B ⧸ R) + Module.length A (B ⧸ Ideal.span {g})`. Rewrite using `[add_comm, ← e1, e2]`.

Conclude with `WithTop.add_left_cancel hfin e3`.
-/
private theorem length_quotient_span_eq_of_finite_length_coker {A B : Type} [CommRing A] [CommRing B] [IsDomain B]
    [Algebra A B] (hAB : Function.Injective (algebraMap A B)) (f : A)
    (hf : algebraMap A B f ≠ 0)
    (hfin : Module.length A (B ⧸ LinearMap.range (Algebra.linearMap A B)) ≠ ⊤) :
    Module.length A (A ⧸ Ideal.span {f}) =
      Module.length A (B ⧸ Ideal.span {algebraMap A B f}) := by
  set g := algebraMap A B f with hg
  set R : Submodule A B := LinearMap.range (Algebra.linearMap A B) with hR
  set fR : Submodule A B := Submodule.span A {g} with hfR
  have hfRR : fR ≤ R := by
    rw [hfR, Submodule.span_le, Set.singleton_subset_iff]
    exact ⟨f, rfl⟩
  let φ1 : (A ⧸ Ideal.span {f}) →ₗ[A] (B ⧸ fR) :=
    Submodule.mapQ (Ideal.span {f}) fR (Algebra.linearMap A B) (by
      intro a ha
      obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.mp ha
      simp only [Submodule.mem_comap, Algebra.linearMap_apply]
      rw [Submodule.mem_span_singleton]
      exact ⟨c, by rw [map_mul, Algebra.smul_def]⟩)
  let ψ1 : (B ⧸ fR) →ₗ[A] (B ⧸ R) := Submodule.factor hfRR
  have h1inj : Function.Injective φ1 := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro x hx
    obtain ⟨a, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    change (Submodule.Quotient.mk (algebraMap A B a) : B ⧸ fR) = 0 at hx
    rw [Submodule.Quotient.mk_eq_zero, Submodule.mem_span_singleton] at hx
    obtain ⟨c, hc⟩ := hx
    rw [Submodule.Quotient.mk_eq_zero, Ideal.mem_span_singleton']
    refine ⟨c, hAB ?_⟩
    rw [map_mul, ← hc, Algebra.smul_def]
  have h1sur : Function.Surjective ψ1 := Submodule.factor_surjective hfRR
  have h1ex : Function.Exact φ1 ψ1 := by
    intro y
    obtain ⟨b, rfl⟩ := Submodule.Quotient.mk_surjective _ y
    constructor
    · intro hy
      change (Submodule.Quotient.mk b : B ⧸ R) = 0 at hy
      rw [Submodule.Quotient.mk_eq_zero] at hy
      obtain ⟨a, rfl⟩ := hy
      exact ⟨Submodule.Quotient.mk a, rfl⟩
    · rintro ⟨x, hx⟩
      rw [← hx]
      obtain ⟨a, rfl⟩ := Submodule.Quotient.mk_surjective _ x
      change (Submodule.Quotient.mk (algebraMap A B a) : B ⧸ R) = 0
      rw [Submodule.Quotient.mk_eq_zero]
      exact ⟨a, rfl⟩
  let φ2 : (B ⧸ R) →ₗ[A] (B ⧸ fR) :=
    Submodule.mapQ R fR (LinearMap.mulLeft A g) (by
      rintro _ ⟨a, rfl⟩
      simp only [Submodule.mem_comap, LinearMap.mulLeft_apply, Algebra.linearMap_apply]
      rw [Submodule.mem_span_singleton]
      exact ⟨a, by rw [Algebra.smul_def, mul_comm]⟩)
  let ψ2 : (B ⧸ fR) →ₗ[A] (B ⧸ Ideal.span {g}) :=
    fR.liftQ (Ideal.Quotient.mkₐ A (Ideal.span {g})).toLinearMap (by
      rw [hfR, Submodule.span_le, Set.singleton_subset_iff]
      simp only [SetLike.mem_coe, LinearMap.mem_ker, AlgHom.toLinearMap_apply,
        Ideal.Quotient.mkₐ_eq_mk]
      exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self g))
  have h2inj : Function.Injective φ2 := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro x hx
    obtain ⟨b, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    change (Submodule.Quotient.mk (g * b) : B ⧸ fR) = 0 at hx
    rw [Submodule.Quotient.mk_eq_zero, Submodule.mem_span_singleton] at hx
    obtain ⟨c, hc⟩ := hx
    rw [Submodule.Quotient.mk_eq_zero]
    refine ⟨c, ?_⟩
    rw [Algebra.smul_def] at hc
    apply mul_left_cancel₀ hf
    rw [Algebra.linearMap_apply, ← hc, mul_comm]
  have h2sur : Function.Surjective ψ2 := by
    intro y
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective y
    exact ⟨Submodule.Quotient.mk b, rfl⟩
  have h2ex : Function.Exact φ2 ψ2 := by
    intro y
    obtain ⟨b, rfl⟩ := Submodule.Quotient.mk_surjective _ y
    constructor
    · intro hy
      change Ideal.Quotient.mk (Ideal.span {g}) b = 0 at hy
      rw [Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton'] at hy
      obtain ⟨x, rfl⟩ := hy
      refine ⟨Submodule.Quotient.mk x, ?_⟩
      change (Submodule.Quotient.mk (g * x) : B ⧸ fR) = Submodule.Quotient.mk (x * g)
      rw [mul_comm]
    · rintro ⟨x, hx⟩
      rw [← hx]
      obtain ⟨b, rfl⟩ := Submodule.Quotient.mk_surjective _ x
      change Ideal.Quotient.mk (Ideal.span {g}) (g * b) = 0
      rw [Ideal.Quotient.eq_zero_iff_mem]
      exact Ideal.mul_mem_right b _ (Ideal.mem_span_singleton_self g)
  have e1 := Module.length_eq_add_of_exact φ1 ψ1 h1inj h1sur h1ex
  have e2 := Module.length_eq_add_of_exact φ2 ψ2 h2inj h2sur h2ex
  have e3 : Module.length A (B ⧸ R) + Module.length A (A ⧸ Ideal.span {f}) =
      Module.length A (B ⧸ R) + Module.length A (B ⧸ Ideal.span {g}) := by
    rw [add_comm, ← e1, e2]
  exact WithTop.add_left_cancel hfin e3

/- English proof (translation)
Take `⟨p, hp, hpe⟩` from `Algebra.IsIntegral.isIntegral (R := A) b`. Set `ψ : A →+* v.ring` to `(algebraMap A K).codRestrict v.ring hA`. Establish `hint : IsIntegral v.ring (algebraMap B K b)`. Use `⟨p.map ψ, hp.map ψ, ?_⟩` and prove the remaining obligations. Rewrite using `[Polynomial.eval₂_map]`.

Establish `hc : (algebraMap v.ring K).comp ψ = (algebraMap B K).comp (algebraMap A B)`. Use extensionality with `a`. Simplify using `only [RingHom.comp_apply]`. Rewrite using `[← IsScalarTower.algebraMap_apply]`. Both sides reduce to the same expression.

Rewrite using `[hc, ← Polynomial.hom_eval₂, hpe, map_zero]`. Take `⟨y, hy⟩` from `IsIntegrallyClosed.isIntegral_iff.mp hint`. Rewrite using `[← hy]`. Conclude with `y.2`.
-/
private theorem algebraMap_mem_place_ring_of_isIntegral {k K A B : Type} [Field k] [Field K] [Algebra k K]
    [IsFunctionField k K] [CommRing A] [Algebra A K] [CommRing B] [Algebra A B] [Algebra B K]
    [IsScalarTower A B K] [Algebra.IsIntegral A B] (v : Place k K)
    (hA : ∀ a : A, algebraMap A K a ∈ v.ring) (b : B) :
    algebraMap B K b ∈ v.ring := by
  obtain ⟨p, hp, hpe⟩ := Algebra.IsIntegral.isIntegral (R := A) b
  let ψ : A →+* v.ring := (algebraMap A K).codRestrict v.ring hA
  have hint : IsIntegral v.ring (algebraMap B K b) := by
    refine ⟨p.map ψ, hp.map ψ, ?_⟩
    rw [Polynomial.eval₂_map]
    have hc : (algebraMap v.ring K).comp ψ = (algebraMap B K).comp (algebraMap A B) := by
      ext a
      simp only [RingHom.comp_apply]
      rw [← IsScalarTower.algebraMap_apply]
      rfl
    rw [hc, ← Polynomial.hom_eval₂, hpe, map_zero]
  obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.mp hint
  rw [← hy]
  exact y.2

/- English proof (translation)
Establish `hAK : Function.Injective (algebraMap A K)` using `IsFractionRing.injective A K`. Establish `hBK : Function.Injective (algebraMap B K)` using `IsFractionRing.injective B K`. Establish `hAB : Function.Injective (algebraMap A B)`. Introduce `x y h`. Apply `hAK` to reduce the goal to its premises.

Rewrite using `[IsScalarTower.algebraMap_apply A B K x, IsScalarTower.algebraMap_apply A B K y, h]`. Establish `hk : ∀ c : k, algebraMap k K c ∈ (algebraMap B K).range` using `fun c => ⟨algebraMap k B c, (IsScalarTower.algebraMap_apply k B K c).symm⟩`. Use `haveI : Algebra.IsIntegral A B := Algebra.IsIntegral.of_finite A B`. Establish `hg0 : algebraMap A B f ≠ 0` using `fun h => hf (hAB (by rw [h, map_zero]))`. Establish `hm : maximalIdeal A ≠ ⊥` using `fun h => hA ((IsLocalRing.isField_iff_maximalIdeal_eq).mpr h)`.

Take `⟨a0, ha0m, ha0⟩` from `Submodule.exists_mem_ne_zero_of_ne_bot hm`. Establish `hover : ∀ P : HeightOneSpectrum B, P.asIdeal.comap (algebraMap A B) = maximalIdeal A`. Introduce `P`. Use `haveI := P.isMaximal`. Conclude with `IsLocalRing.eq_maximalIdeal (Ideal.IsMaximal.under A P.asIdeal)`.

Establish `hfinH : Finite (HeightOneSpectrum B)`. Establish `h0 : Ideal.span {algebraMap A B a0} ≠ 0`. Rewrite using `[Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]`. Conclude with `fun h => ha0 (hAB (by rw [h, map_zero]))`. Use `Set.finite_univ_iff.mp ((Ideal.finite_factors h0).subset ?_)` and prove the remaining obligations.

Introduce `P _`. Use `show P.asIdeal ∣ Ideal.span {algebraMap A B a0}`. Rewrite using `[Ideal.dvd_iff_le, Ideal.span_singleton_le_iff_mem]`. Establish `h1 : a0 ∈ P.asIdeal.comap (algebraMap A B)`. Rewrite using `[hover P]`.

Conclude with `ha0m`. Conclude with `h1`. Use `haveI : Fintype (HeightOneSpectrum B) := Fintype.ofFinite _`. Establish `hlenfin : ∀ I : Ideal B, I ≠ ⊥ → Module.length A (B ⧸ I) ≠ ⊤`. Introduce `I hI`.

Rewrite using `[length_quotient_eq_sum_count_mul_inertiaDeg I hI, ← Nat.cast_sum]`. Conclude with `ENat.coe_ne_top _`. Establish `hfin : Module.length A (B ⧸ LinearMap.range (Algebra.linearMap A B)) ≠ ⊤`. Take `⟨s, hs⟩` from `Module.Finite.fg_top (R := A) (M := B)`. Take `⟨⟨c, hc⟩, hcint⟩` from `IsLocalization.exist_integer_multiples_of_finset (nonZeroDivisors A) (s.image (algebraMap B K))`.

Establish `hc0 : algebraMap A B c ≠ 0` using `fun h => nonZeroDivisors.ne_zero hc (hAB (by rw [h, map_zero]))`. Establish `hcond : (⊤ : Submodule A B) ≤ (LinearMap.range (Algebra.linearMap A B)).comap (LinearMap.mulLeft A (algebraMap A B c))`. Rewrite using `[← hs, Submodule.span_le]`. Introduce `b hb`. Take `⟨a, ha⟩` from `hcint (algebraMap B K b) (Finset.mem_image_of_mem _ hb)`.

Use `⟨a, hBK ?_⟩` and prove the remaining obligations. Simplify using `only [Algebra.linearMap_apply, LinearMap.mulLeft_apply]`. Rewrite using `[← IsScalarTower.algebraMap_apply, ha]`. Express the relevant statement in the definitionally equal form `c • algebraMap B K b = _`. Rewrite using `[Algebra.smul_def, map_mul, ← IsScalarTower.algebraMap_apply]`.

Establish `hle : (Ideal.span {algebraMap A B c}).restrictScalars A ≤ LinearMap.range (Algebra.linearMap A B)`. Introduce `x hx`. Take `⟨y, rfl⟩` from `Ideal.mem_span_singleton'.mp hx`. Rewrite using `[mul_comm]`. Conclude with `hcond Submodule.mem_top`.

Set `q : (B ⧸ Ideal.span {algebraMap A B c}) →ₗ[A] (B ⧸ LinearMap.range (Algebra.linearMap A B))` to `(Submodule.factor hle).comp (Submodule.Quotient.restrictScalarsEquiv A (Ideal.span {algebraMap A B c})).symm.toLinearMap`. Establish `hq : Function.Surjective q` using `(Submodule.factor_surjective hle).comp (LinearEquiv.surjective _)`. Establish `hspan : Ideal.span {algebraMap A B c} ≠ ⊥`. Rewrite using `[Ne, Ideal.span_singleton_eq_bot]`. Conclude with `hc0`.

Conclude with `ne_top_of_le_ne_top (hlenfin _ hspan) (Module.length_le_of_surjective q hq)`. Establish `hX` using `length_quotient_span_eq_of_finite_length_coker hAB f hg0 hfin`. Establish `hspan : Ideal.span {algebraMap A B f} ≠ ⊥`. Rewrite using `[Ne, Ideal.span_singleton_eq_bot]`. Conclude with `hg0`.

Establish `hY` using `length_quotient_eq_sum_count_mul_inertiaDeg (A := A) (Ideal.span {algebraMap A B f}) hspan`. Rewrite using `[hX, hY, ← Nat.cast_sum, ENat.toNat_coe]`. Use `set φ : HeightOneSpectrum B → Place k K := fun P => Place.ofHeightOneSpectrum B hk P with hφ`. Establish `hφinj : Function.Injective φ`. Establish `key : ∀ (v w : Place k K) (hv : ∀ b : B, algebraMap B K b ∈ v.ring) (hw : ∀ b : B, algebraMap B K b ∈ w.ring), v = w → Place.center B v hv = Place.center B w hw`.

Introduce and unpack `v w hv hw rfl`. Both sides reduce to the same expression. Introduce `P Q h`. Rewrite using `[← Place.center_ofHeightOneSpectrum B hk P, ← Place.center_ofHeightOneSpectrum B hk Q]`. Conclude with `key _ _ _ _ h`.

Establish `hS : {v : Place k K | (∀ a : A, v.valuation (algebraMap A K a) ≤ 1) ∧ ∀ a ∈ maximalIdeal A, v.valuation (algebraMap A K a) < 1} = Set.range φ`. Use extensionality with `v`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨h1, _⟩`. Establish `hA' : ∀ a : A, algebraMap A K a ∈ v.ring`.

Introduce `a`. Rewrite using `[← place_valuation_valuationSubring_eq_ring v]`. Conclude with `h1 a`. Establish `hB' : ∀ b : B, algebraMap B K b ∈ v.ring` using `algebraMap_mem_place_ring_of_isIntegral v hA'`. Conclude with `⟨Place.center B v hB', Place.ofHeightOneSpectrum_center B hk v hB'⟩`.

Introduce and unpack `⟨P, rfl⟩`. Use `⟨fun a => ?_, fun a ha => ?_⟩` and prove the remaining obligations. Simplify using `only [φ]`. Rewrite using `[ofHeightOneSpectrum_valuation_eq, IsScalarTower.algebraMap_apply A B K]`. Conclude with `HeightOneSpectrum.valuation_le_one _ _`.

Simplify using `only [φ]`. Rewrite using `[ofHeightOneSpectrum_valuation_eq, IsScalarTower.algebraMap_apply A B K, HeightOneSpectrum.valuation_lt_one_iff_mem]`. Establish `h2 : a ∈ P.asIdeal.comap (algebraMap A B)`. Rewrite using `[hover P]`. Conclude with `ha`.

Conclude with `h2`. Rewrite using `[hS, finsum_mem_range hφinj, finsum_eq_sum_of_fintype]`. Use `push_cast`. Rewrite using `[Finset.sum_mul]`. Use `Finset.sum_congr rfl (fun P _ => ?_)` and prove the remaining obligations.

Simplify using `only [φ]`. Use `haveI := P.isMaximal`. Rewrite using `[deg_ofHeightOneSpectrum B hk P, IsScalarTower.algebraMap_apply A B K f, ofHeightOneSpectrum_ord_eq_count hk P _ hg0, ← inertiaDeg_mul k A B P.asIdeal]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem length_places (A B : Type) [CommRing A] [IsDomain A] [Algebra k A] [Algebra A K]
    [IsScalarTower k A K] [IsLocalRing A] [IsNoetherianRing A] [IsFractionRing A K]
    [CommRing B] [IsDedekindDomain B] [Algebra A B] [Algebra B K] [IsScalarTower A B K]
    [IsFractionRing B K] [Algebra k B] [IsScalarTower k A B] [IsScalarTower k B K]
    [Module.Finite A B] (hA : ¬ IsField A) (f : A) (hf : f ≠ 0) :
    (((Module.length A (A ⧸ Ideal.span {f})).toNat * Module.finrank k (ResidueField A) : ℕ) : ℤ) =
      ∑ᶠ v ∈ {v : Place k K | (∀ a : A, v.valuation (algebraMap A K a) ≤ 1) ∧
        ∀ a ∈ maximalIdeal A, v.valuation (algebraMap A K a) < 1},
        (v.deg : ℤ) * v.ord (algebraMap A K f) := by
  classical
  have hAK : Function.Injective (algebraMap A K) := IsFractionRing.injective A K
  have hBK : Function.Injective (algebraMap B K) := IsFractionRing.injective B K
  have hAB : Function.Injective (algebraMap A B) := by
    intro x y h
    apply hAK
    rw [IsScalarTower.algebraMap_apply A B K x, IsScalarTower.algebraMap_apply A B K y, h]
  have hk : ∀ c : k, algebraMap k K c ∈ (algebraMap B K).range :=
    fun c => ⟨algebraMap k B c, (IsScalarTower.algebraMap_apply k B K c).symm⟩
  haveI : Algebra.IsIntegral A B := Algebra.IsIntegral.of_finite A B
  have hg0 : algebraMap A B f ≠ 0 := fun h => hf (hAB (by rw [h, map_zero]))
  have hm : maximalIdeal A ≠ ⊥ := fun h => hA ((IsLocalRing.isField_iff_maximalIdeal_eq).mpr h)
  obtain ⟨a0, ha0m, ha0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hm
  have hover : ∀ P : HeightOneSpectrum B,
      P.asIdeal.comap (algebraMap A B) = maximalIdeal A := by
    intro P
    haveI := P.isMaximal
    exact IsLocalRing.eq_maximalIdeal (Ideal.IsMaximal.under A P.asIdeal)
  have hfinH : Finite (HeightOneSpectrum B) := by
    have h0 : Ideal.span {algebraMap A B a0} ≠ 0 := by
      rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
      exact fun h => ha0 (hAB (by rw [h, map_zero]))
    refine Set.finite_univ_iff.mp ((Ideal.finite_factors h0).subset ?_)
    intro P _
    show P.asIdeal ∣ Ideal.span {algebraMap A B a0}
    rw [Ideal.dvd_iff_le, Ideal.span_singleton_le_iff_mem]
    have h1 : a0 ∈ P.asIdeal.comap (algebraMap A B) := by
      rw [hover P]
      exact ha0m
    exact h1
  haveI : Fintype (HeightOneSpectrum B) := Fintype.ofFinite _
  have hlenfin : ∀ I : Ideal B, I ≠ ⊥ → Module.length A (B ⧸ I) ≠ ⊤ := by
    intro I hI
    rw [length_quotient_eq_sum_count_mul_inertiaDeg I hI, ← Nat.cast_sum]
    exact ENat.coe_ne_top _
  have hfin : Module.length A (B ⧸ LinearMap.range (Algebra.linearMap A B)) ≠ ⊤ := by
    obtain ⟨s, hs⟩ := Module.Finite.fg_top (R := A) (M := B)
    obtain ⟨⟨c, hc⟩, hcint⟩ :=
      IsLocalization.exist_integer_multiples_of_finset (nonZeroDivisors A)
        (s.image (algebraMap B K))
    have hc0 : algebraMap A B c ≠ 0 := fun h =>
      nonZeroDivisors.ne_zero hc (hAB (by rw [h, map_zero]))
    have hcond : (⊤ : Submodule A B) ≤ (LinearMap.range (Algebra.linearMap A B)).comap
        (LinearMap.mulLeft A (algebraMap A B c)) := by
      rw [← hs, Submodule.span_le]
      intro b hb
      obtain ⟨a, ha⟩ := hcint (algebraMap B K b) (Finset.mem_image_of_mem _ hb)
      refine ⟨a, hBK ?_⟩
      simp only [Algebra.linearMap_apply, LinearMap.mulLeft_apply]
      rw [← IsScalarTower.algebraMap_apply, ha]
      change c • algebraMap B K b = _
      rw [Algebra.smul_def, map_mul, ← IsScalarTower.algebraMap_apply]
    have hle : (Ideal.span {algebraMap A B c}).restrictScalars A ≤
        LinearMap.range (Algebra.linearMap A B) := by
      intro x hx
      obtain ⟨y, rfl⟩ := Ideal.mem_span_singleton'.mp hx
      rw [mul_comm]
      exact hcond Submodule.mem_top
    let q : (B ⧸ Ideal.span {algebraMap A B c}) →ₗ[A]
        (B ⧸ LinearMap.range (Algebra.linearMap A B)) :=
      (Submodule.factor hle).comp
        (Submodule.Quotient.restrictScalarsEquiv A (Ideal.span {algebraMap A B c})).symm.toLinearMap
    have hq : Function.Surjective q :=
      (Submodule.factor_surjective hle).comp (LinearEquiv.surjective _)
    have hspan : Ideal.span {algebraMap A B c} ≠ ⊥ := by
      rw [Ne, Ideal.span_singleton_eq_bot]
      exact hc0
    exact ne_top_of_le_ne_top (hlenfin _ hspan) (Module.length_le_of_surjective q hq)
  have hX := length_quotient_span_eq_of_finite_length_coker hAB f hg0 hfin
  have hspan : Ideal.span {algebraMap A B f} ≠ ⊥ := by
    rw [Ne, Ideal.span_singleton_eq_bot]
    exact hg0
  have hY := length_quotient_eq_sum_count_mul_inertiaDeg (A := A) (Ideal.span {algebraMap A B f}) hspan
  rw [hX, hY, ← Nat.cast_sum, ENat.toNat_coe]
  set φ : HeightOneSpectrum B → Place k K := fun P => Place.ofHeightOneSpectrum B hk P with hφ
  have hφinj : Function.Injective φ := by
    have key : ∀ (v w : Place k K) (hv : ∀ b : B, algebraMap B K b ∈ v.ring)
        (hw : ∀ b : B, algebraMap B K b ∈ w.ring), v = w →
          Place.center B v hv = Place.center B w hw := by
      rintro v w hv hw rfl
      rfl
    intro P Q h
    rw [← Place.center_ofHeightOneSpectrum B hk P, ← Place.center_ofHeightOneSpectrum B hk Q]
    exact key _ _ _ _ h
  have hS : {v : Place k K | (∀ a : A, v.valuation (algebraMap A K a) ≤ 1) ∧
      ∀ a ∈ maximalIdeal A, v.valuation (algebraMap A K a) < 1} = Set.range φ := by
    ext v
    constructor
    · rintro ⟨h1, _⟩
      have hA' : ∀ a : A, algebraMap A K a ∈ v.ring := by
        intro a
        rw [← place_valuation_valuationSubring_eq_ring v]
        exact h1 a
      have hB' : ∀ b : B, algebraMap B K b ∈ v.ring := algebraMap_mem_place_ring_of_isIntegral v hA'
      exact ⟨Place.center B v hB', Place.ofHeightOneSpectrum_center B hk v hB'⟩
    · rintro ⟨P, rfl⟩
      refine ⟨fun a => ?_, fun a ha => ?_⟩
      · simp only [φ]
        rw [ofHeightOneSpectrum_valuation_eq, IsScalarTower.algebraMap_apply A B K]
        exact HeightOneSpectrum.valuation_le_one _ _
      · simp only [φ]
        rw [ofHeightOneSpectrum_valuation_eq, IsScalarTower.algebraMap_apply A B K,
          HeightOneSpectrum.valuation_lt_one_iff_mem]
        have h2 : a ∈ P.asIdeal.comap (algebraMap A B) := by
          rw [hover P]
          exact ha
        exact h2
  rw [hS, finsum_mem_range hφinj, finsum_eq_sum_of_fintype]
  push_cast
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl (fun P _ => ?_)
  simp only [φ]
  haveI := P.isMaximal
  rw [deg_ofHeightOneSpectrum B hk P, IsScalarTower.algebraMap_apply A B K f,
    ofHeightOneSpectrum_ord_eq_count hk P _ hg0, ← inertiaDeg_mul k A B P.asIdeal]
  push_cast
  ring

/- English proof (translation)
Introduce `k K A _ _ _ _ _ _ _ _ _ _ _ _ _ hA f hf`. Use `haveI : Module.Finite A (integralClosure A K) := finite_closure k K A`. Use `haveI : IsFractionRing (integralClosure A K) K := integralClosure.isFractionRing_of_finite_extension K K`. Use `haveI : IsScalarTower k A (integralClosure A K) := IsScalarTower.of_algebraMap_eq (fun x => Subtype.ext (IsScalarTower.algebraMap_apply k A K x))`. Use `haveI : IsScalarTower k (integralClosure A K) K := IsScalarTower.of_algebraMap_eq (fun x => rfl)`.

Use `haveI : IsNoetherianRing (integralClosure A K) := isNoetherian_of_tower A inferInstance`. Use `haveI : IsDedekindDomain (integralClosure A K) := by`. Rewrite using `[isDedekindDomain_iff (integralClosure A K) K]`. Use `⟨inferInstance, inferInstance, ⟨fun {p} hp0 hp => isMaximal_of_ne_bot (k := k) (K := K) (integralClosure A K) (IsFractionRing.injective (integralClosure A K) K) p hp0 hp⟩, ?_⟩` and prove the remaining obligations. Introduce `x hx`.

Conclude with `⟨⟨x, isIntegral_trans x hx⟩, rfl⟩`. Conclude with `length_places A (integralClosure A K) hA f hf`.
-/
theorem len_places : ∀ (k K A : Type) [Field k] [Field K] [Algebra k K] [GroundTheory.FunctionField.IsFunctionField k K] [CommRing A] [IsDomain A] [Algebra k A] [Algebra A K] [IsScalarTower k A K] [IsLocalRing A] [IsNoetherianRing A] [IsFractionRing A K] [Algebra.EssFiniteType k A], ¬ IsField A → ∀ f : A, f ≠ 0 → (((Module.length A (A ⧸ Ideal.span {f})).toNat * Module.finrank k (IsLocalRing.ResidueField A) : ℕ) : ℤ) = ∑ᶠ v ∈ {v : GroundTheory.FunctionField.Place k K | (∀ a : A, v.valuation (algebraMap A K a) ≤ 1) ∧ ∀ a ∈ IsLocalRing.maximalIdeal A, v.valuation (algebraMap A K a) < 1}, (v.deg : ℤ) * v.ord (algebraMap A K f) := by
  intro k K A _ _ _ _ _ _ _ _ _ _ _ _ _ hA f hf
  haveI : Module.Finite A (integralClosure A K) := finite_closure k K A
  haveI : IsFractionRing (integralClosure A K) K :=
    integralClosure.isFractionRing_of_finite_extension K K
  haveI : IsScalarTower k A (integralClosure A K) :=
    IsScalarTower.of_algebraMap_eq (fun x => Subtype.ext (IsScalarTower.algebraMap_apply k A K x))
  haveI : IsScalarTower k (integralClosure A K) K :=
    IsScalarTower.of_algebraMap_eq (fun x => rfl)
  haveI : IsNoetherianRing (integralClosure A K) := isNoetherian_of_tower A inferInstance
  haveI : IsDedekindDomain (integralClosure A K) := by
    rw [isDedekindDomain_iff (integralClosure A K) K]
    refine ⟨inferInstance, inferInstance, ⟨fun {p} hp0 hp =>
      isMaximal_of_ne_bot (k := k) (K := K) (integralClosure A K)
        (IsFractionRing.injective (integralClosure A K) K) p hp0 hp⟩, ?_⟩
    intro x hx
    exact ⟨⟨x, isIntegral_trans x hx⟩, rfl⟩
  exact length_places A (integralClosure A K) hA f hf

end PositivityTheory.HtPt.Plen

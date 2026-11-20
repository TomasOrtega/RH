import ReciprocityTheory.GaloisValuations.GlobalA

set_option linter.style.haveILetI false

noncomputable section

open NumberField IsDedekindDomain Pointwise
open scoped nonZeroDivisors

namespace ReciprocityTheory.Gal

section den

variable {Ω : Type*} [Field Ω]

/- English proof (translation)
The claim follows from `isIntegral_trans b hb`.
-/
theorem isIntegral_int_of_isIntegral {F : Type*} [Field F] [NumberField F] [Algebra F Ω] {b : Ω} (hb : IsIntegral (𝓞 F) b) : IsIntegral ℤ b :=
  isIntegral_trans b hb

/- English proof (translation)
Establish `h1 : IsIntegral A b` using `hb.tower_top`. Take `⟨y, hy⟩` from `(IsIntegrallyClosed.isIntegral_iff (R := A) (K := Ω)).mp h1`. Rewrite using `[← hy]`. Conclude with `y.2`.
-/
theorem mem_of_isIntegral_int (A : ValuationSubring Ω) {b : Ω} (hb : IsIntegral ℤ b) : b ∈ A := by
  have h1 : IsIntegral A b := hb.tower_top
  obtain ⟨y, hy⟩ := (IsIntegrallyClosed.isIntegral_iff (R := A) (K := Ω)).mp h1
  rw [← hy]
  exact y.2

/- English proof (translation)
Establish `: CharZero Ω` using `charZero_of_injective_algebraMap (algebraMap F Ω).injective`. Establish `hxF : IsIntegral F x` using `Algebra.IsIntegral.isIntegral x`. Establish `hxQ : IsIntegral ℚ x` using `isIntegral_trans x hxF`. Set `E` to `IntermediateField.adjoin ℚ ({x} : Set Ω)`. Establish `: FiniteDimensional ℚ E` using `IntermediateField.adjoin.finiteDimensional hxQ`.

Establish `: NumberField E` using `⟨⟩`. Set `x' : E` to `⟨x, IntermediateField.mem_adjoin_simple_self ℚ x⟩`. Set `M : FractionalIdeal (𝓞 E)⁰ E` to `1 + FractionalIdeal.spanSingleton _ x'`. Establish `h1M : (1 : E) ∈ M`. Establish `hle1 : (1 : FractionalIdeal (𝓞 E)⁰ E) ≤ M`.

Simplify using `only [M, ← FractionalIdeal.sup_eq_add]`. Conclude with `le_sup_left`. Conclude with `hle1 (FractionalIdeal.one_mem_one _)`. Establish `hxM : x' ∈ M`. Establish `hle1 : FractionalIdeal.spanSingleton (𝓞 E)⁰ x' ≤ M`.

Simplify using `only [M, ← FractionalIdeal.sup_eq_add]`. Conclude with `le_sup_right`. Conclude with `hle1 (FractionalIdeal.mem_spanSingleton_self _ _)`. Establish `hM : M ≠ 0`. Introduce `h`.

Rewrite `h1M` using `[h]`. Conclude with `one_ne_zero ((FractionalIdeal.mem_zero_iff _).mp h1M)`. Establish `hMM : M * M⁻¹ = 1` using `mul_inv_cancel₀ hM`. Choose the witnesses or unpack the hypotheses as in `⟨α, hα, β, hβ, e⟩ : ∃ α ∈ M⁻¹, ∃ β ∈ M⁻¹, α + x' * β = 1 := by`. Establish `h1 : (1 : E) ∈ M * M⁻¹` using `by rw [hMM]; exact FractionalIdeal.one_mem_one _`.

Establish `e2 : M * M⁻¹ = M⁻¹ ⊔ FractionalIdeal.spanSingleton _ x' * M⁻¹`. Simplify using `only [M, add_mul, one_mul, FractionalIdeal.sup_eq_add]`. Rewrite `h1` using `[e2, ← FractionalIdeal.mem_coe, FractionalIdeal.coe_sup, Submodule.mem_sup]`. Take `⟨α, hα, z, hz, e⟩` from `h1`. Take `⟨β, hβ, rfl⟩` from `FractionalIdeal.mem_singleton_mul.mp hz`.

Conclude with `⟨α, hα, β, hβ, e⟩`. Establish `hint : ∀ γ ∈ M⁻¹, IsIntegral ℤ (γ : Ω) ∧ IsIntegral ℤ ((γ * x' : E) : Ω)`. Introduce `γ hγ`. Rewrite `hγ` using `[FractionalIdeal.mem_inv_iff hM]`. Establish `key : ∀ z : E, z ∈ (1 : FractionalIdeal (𝓞 E)⁰ E) → IsIntegral ℤ (z : Ω)`.

Introduce `z hz`. Take `⟨z', rfl⟩` from `(FractionalIdeal.mem_one_iff _).mp hz`. Establish `: IsIntegral ℤ (algebraMap (𝓞 E) E z')` using `z'.2`. Conclude with `this.map (IsScalarTower.toAlgHom ℤ E Ω)`. Conclude with `⟨by simpa using key _ (hγ 1 h1M), key _ (hγ x' hxM)⟩`.

Establish `hle : ∀ γ ∈ M⁻¹, A.valuation (γ : Ω) ≤ 1` using `fun γ hγ => (A.valuation_le_one_iff _).mpr (mem_of_isIntegral_int A (hint γ hγ).1)`. Distinguish the cases in `ha : A.valuation (α : Ω) = 1`. Conclude with `⟨α, _, (hint α hα).1, (hint α hα).2, ha, by simp [x']⟩`. Distinguish the cases in `hb : A.valuation (β : Ω) = 1`. Conclude with `⟨β, _, (hint β hβ).1, (hint β hβ).2, hb, by simp [x', mul_comm]⟩`.

It suffices to derive a contradiction. Establish `ha' : A.valuation (α : Ω) < 1` using `lt_of_le_of_ne (hle α hα) ha`. Establish `hb' : A.valuation (β : Ω) < 1` using `lt_of_le_of_ne (hle β hβ) hb`. Establish `e' : (α : Ω) + x * (β : Ω) = 1`. Use `congrArg (fun z : E => (z : Ω)) e` as an intermediate fact.

Simplify `this` using `[x']`. Establish `: A.valuation ((α : Ω) + x * (β : Ω)) < 1`. Use `Valuation.map_add_lt _ ha' ?_` and prove the remaining obligations. Rewrite using `[Valuation.map_mul]`. Combine the equalities or inequalities in the displayed calculation.

Rewrite `this` using `[e', Valuation.map_one]`. Conclude with `lt_irrefl _ this`.
-/
theorem exists_den (F : Type*) [Field F] [NumberField F] [Algebra F Ω] [IsAlgClosure F Ω]
    (A : ValuationSubring Ω) {x : Ω} (hx : A.valuation x ≤ 1) :
    ∃ s t : Ω, IsIntegral ℤ s ∧ IsIntegral ℤ t ∧ A.valuation s = 1 ∧ s * x = t := by
  have : CharZero Ω := charZero_of_injective_algebraMap (algebraMap F Ω).injective
  have hxF : IsIntegral F x := Algebra.IsIntegral.isIntegral x
  have hxQ : IsIntegral ℚ x := isIntegral_trans x hxF
  let E := IntermediateField.adjoin ℚ ({x} : Set Ω)
  have : FiniteDimensional ℚ E := IntermediateField.adjoin.finiteDimensional hxQ
  have : NumberField E := ⟨⟩
  let x' : E := ⟨x, IntermediateField.mem_adjoin_simple_self ℚ x⟩
  let M : FractionalIdeal (𝓞 E)⁰ E := 1 + FractionalIdeal.spanSingleton _ x'
  have h1M : (1 : E) ∈ M := by
    have hle1 : (1 : FractionalIdeal (𝓞 E)⁰ E) ≤ M := by
      simp only [M, ← FractionalIdeal.sup_eq_add]; exact le_sup_left
    exact hle1 (FractionalIdeal.one_mem_one _)
  have hxM : x' ∈ M := by
    have hle1 : FractionalIdeal.spanSingleton (𝓞 E)⁰ x' ≤ M := by
      simp only [M, ← FractionalIdeal.sup_eq_add]; exact le_sup_right
    exact hle1 (FractionalIdeal.mem_spanSingleton_self _ _)
  have hM : M ≠ 0 := by
    intro h
    rw [h] at h1M
    exact one_ne_zero ((FractionalIdeal.mem_zero_iff _).mp h1M)
  have hMM : M * M⁻¹ = 1 := mul_inv_cancel₀ hM
  obtain ⟨α, hα, β, hβ, e⟩ : ∃ α ∈ M⁻¹, ∃ β ∈ M⁻¹, α + x' * β = 1 := by
    have h1 : (1 : E) ∈ M * M⁻¹ := by rw [hMM]; exact FractionalIdeal.one_mem_one _
    have e2 : M * M⁻¹ = M⁻¹ ⊔ FractionalIdeal.spanSingleton _ x' * M⁻¹ := by
      simp only [M, add_mul, one_mul, FractionalIdeal.sup_eq_add]
    rw [e2, ← FractionalIdeal.mem_coe, FractionalIdeal.coe_sup, Submodule.mem_sup] at h1
    obtain ⟨α, hα, z, hz, e⟩ := h1
    obtain ⟨β, hβ, rfl⟩ := FractionalIdeal.mem_singleton_mul.mp hz
    exact ⟨α, hα, β, hβ, e⟩
  have hint : ∀ γ ∈ M⁻¹, IsIntegral ℤ (γ : Ω) ∧ IsIntegral ℤ ((γ * x' : E) : Ω) := by
    intro γ hγ
    rw [FractionalIdeal.mem_inv_iff hM] at hγ
    have key : ∀ z : E, z ∈ (1 : FractionalIdeal (𝓞 E)⁰ E) → IsIntegral ℤ (z : Ω) := by
      intro z hz
      obtain ⟨z', rfl⟩ := (FractionalIdeal.mem_one_iff _).mp hz
      have : IsIntegral ℤ (algebraMap (𝓞 E) E z') := z'.2
      exact this.map (IsScalarTower.toAlgHom ℤ E Ω)
    exact ⟨by simpa using key _ (hγ 1 h1M), key _ (hγ x' hxM)⟩
  have hle : ∀ γ ∈ M⁻¹, A.valuation (γ : Ω) ≤ 1 := fun γ hγ =>
    (A.valuation_le_one_iff _).mpr (mem_of_isIntegral_int A (hint γ hγ).1)
  by_cases ha : A.valuation (α : Ω) = 1
  · exact ⟨α, _, (hint α hα).1, (hint α hα).2, ha, by simp [x']⟩
  by_cases hb : A.valuation (β : Ω) = 1
  · exact ⟨β, _, (hint β hβ).1, (hint β hβ).2, hb, by simp [x', mul_comm]⟩
  exfalso
  have ha' : A.valuation (α : Ω) < 1 := lt_of_le_of_ne (hle α hα) ha
  have hb' : A.valuation (β : Ω) < 1 := lt_of_le_of_ne (hle β hβ) hb
  have e' : (α : Ω) + x * (β : Ω) = 1 := by
    have := congrArg (fun z : E => (z : Ω)) e
    simpa [x'] using this
  have : A.valuation ((α : Ω) + x * (β : Ω)) < 1 := by
    refine Valuation.map_add_lt _ ha' ?_
    rw [Valuation.map_mul]
    calc A.valuation x * A.valuation (β : Ω) ≤ 1 * A.valuation (β : Ω) := mul_le_mul_left hx _
      _ < 1 := by rw [one_mul]; exact hb'
  rw [e', Valuation.map_one] at this
  exact lt_irrefl _ this

/- English proof (translation)
Introduce `x hx`. Establish `hx' : A.valuation x ≤ 1` using `(A.valuation_le_one_iff x).mpr hx`. Take `⟨s, t, hs, ht, hs1, e⟩` from `exists_den F A hx'`. Establish `hs0 : s ≠ 0` using `by rintro rfl; simp at hs1`. Establish `hs1' : A'.valuation s = 1`.

Use `le_antisymm ((A'.valuation_le_one_iff s).mpr (mem_of_isIntegral_int A' hs)) ?_` and prove the remaining obligations. Rewrite using `[← not_lt, ← h s hs, hs1]`. Conclude with `lt_irrefl 1`. Establish `hxt : x = t * s⁻¹` using `by rw [← e]; field_simp`. Rewrite using `[← A'.valuation_le_one_iff, hxt, Valuation.map_mul, map_inv₀, hs1', inv_one, mul_one, A'.valuation_le_one_iff]`.

Conclude with `mem_of_isIntegral_int A' ht`.
-/
theorem le_of_valuation_lt_one_iff (F : Type*) [Field F] [NumberField F] [Algebra F Ω]
    [IsAlgClosure F Ω] {A A' : ValuationSubring Ω}
    (h : ∀ b : Ω, IsIntegral ℤ b → (A.valuation b < 1 ↔ A'.valuation b < 1)) : A ≤ A' := by
  intro x hx
  have hx' : A.valuation x ≤ 1 := (A.valuation_le_one_iff x).mpr hx
  obtain ⟨s, t, hs, ht, hs1, e⟩ := exists_den F A hx'
  have hs0 : s ≠ 0 := by rintro rfl; simp at hs1
  have hs1' : A'.valuation s = 1 := by
    refine le_antisymm ((A'.valuation_le_one_iff s).mpr (mem_of_isIntegral_int A' hs)) ?_
    rw [← not_lt, ← h s hs, hs1]
    exact lt_irrefl 1
  have hxt : x = t * s⁻¹ := by rw [← e]; field_simp
  rw [← A'.valuation_le_one_iff, hxt, Valuation.map_mul, map_inv₀, hs1', inv_one, mul_one,
    A'.valuation_le_one_iff]
  exact mem_of_isIntegral_int A' ht

/- English proof (translation)
The claim follows from `le_antisymm (le_of_valuation_lt_one_iff F h) (le_of_valuation_lt_one_iff F fun b hb => (h b hb).symm)`.
-/
theorem eq_of_valuation_lt_one_iff (F : Type*) [Field F] [NumberField F] [Algebra F Ω]
    [IsAlgClosure F Ω] {A A' : ValuationSubring Ω}
    (h : ∀ b : Ω, IsIntegral ℤ b → (A.valuation b < 1 ↔ A'.valuation b < 1)) : A = A' :=
  le_antisymm (le_of_valuation_lt_one_iff F h)
    (le_of_valuation_lt_one_iff F fun b hb => (h b hb).symm)

end den

section places

variable {F Ω : Type*} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω]

/- English proof (translation)
Rewrite using `[← ValuationSubring.mem_nonunits_iff, ← ValuationSubring.mem_nonunits_iff, ValuationSubring.mem_nonunits_iff_or, ValuationSubring.mem_nonunits_iff_or, ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem, AlgEquiv.smul_def, map_inv₀, map_eq_zero_iff _ (g⁻¹ : Ω ≃ₐ[F] Ω).injective]`.
-/
theorem smul_valuation_lt_one_iff (g : Ω ≃ₐ[F] Ω) (A : ValuationSubring Ω) (y : Ω) :
    (g • A).valuation y < 1 ↔ A.valuation ((g⁻¹ : Ω ≃ₐ[F] Ω) y) < 1 := by
  rw [← ValuationSubring.mem_nonunits_iff, ← ValuationSubring.mem_nonunits_iff,
    ValuationSubring.mem_nonunits_iff_or, ValuationSubring.mem_nonunits_iff_or,
    ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem, AlgEquiv.smul_def, map_inv₀,
    map_eq_zero_iff _ (g⁻¹ : Ω ≃ₐ[F] Ω).injective]

omit [NumberField F] [IsAlgClosure F Ω] in
/- English proof (translation)
Rewrite using `[ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem, AlgEquiv.smul_def]`. Conclude with `hA _ (hb.map ((g⁻¹ : Ω ≃ₐ[F] Ω).toAlgHom.restrictScalars ℤ))`.
-/
theorem smul_le_one_of_isIntegral (g : Ω ≃ₐ[F] Ω) {A : ValuationSubring Ω}
    (hA : ∀ b : Ω, IsIntegral ℤ b → b ∈ A) {b : Ω} (hb : IsIntegral ℤ b) : b ∈ g • A := by
  rw [ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem, AlgEquiv.smul_def]
  exact hA _ (hb.map ((g⁻¹ : Ω ≃ₐ[F] Ω).toAlgHom.restrictScalars ℤ))

variable (F Ω) in

abbrev IntCl := integralClosure (𝓞 F) Ω

/- English proof (translation)
The claim follows from `(A.valuation_le_one_iff _).mpr (mem_of_isIntegral_int A (isIntegral_int_of_isIntegral b.2))`.
-/
theorem valuation_le_one_intCl (A : ValuationSubring Ω) (b : IntCl F Ω) :
    A.valuation (b : Ω) ≤ 1 :=
  (A.valuation_le_one_iff _).mpr (mem_of_isIntegral_int A (isIntegral_int_of_isIntegral b.2))

def primeBelow (A : ValuationSubring Ω) : Ideal (IntCl F Ω) where
  carrier := {b | A.valuation (b : Ω) < 1}
  add_mem' {a b} ha hb := by
    show A.valuation ((a : Ω) + b) < 1
    exact Valuation.map_add_lt _ ha hb
  zero_mem' := by show A.valuation ((0 : IntCl F Ω) : Ω) < 1; simp
  smul_mem' c b hb := by
    show A.valuation ((c : Ω) * b) < 1
    rw [Valuation.map_mul]
    calc A.valuation (c : Ω) * A.valuation (b : Ω) ≤ 1 * A.valuation (b : Ω) :=
          mul_le_mul_left (valuation_le_one_intCl A c) _
      _ < 1 := by rw [one_mul]; exact hb

/- English proof (translation)
Unfold both sides. The equivalence is reflexive.
-/
theorem mem_primeBelow {A : ValuationSubring Ω} {b : IntCl F Ω} :
    b ∈ primeBelow A ↔ A.valuation (b : Ω) < 1 := Iff.rfl

instance isPrime_primeBelow (A : ValuationSubring Ω) : (primeBelow (F := F) A).IsPrime where
  ne_top' h := by
    have : (1 : IntCl F Ω) ∈ primeBelow A := h ▸ Submodule.mem_top
    rw [mem_primeBelow] at this
    simp at this
  mem_or_mem' {a b} hab := by
    rw [mem_primeBelow, mem_primeBelow]
    rw [mem_primeBelow] at hab
    by_contra hn
    simp only [not_or, not_lt] at hn
    have ha : A.valuation (a : Ω) = 1 := le_antisymm (valuation_le_one_intCl A a) hn.1
    have hb : A.valuation (b : Ω) = 1 := le_antisymm (valuation_le_one_intCl A b) hn.2
    have : A.valuation ((a * b : IntCl F Ω) : Ω) = 1 := by
      rw [MulMemClass.coe_mul, Valuation.map_mul, ha, hb, one_mul]
    rw [this] at hab
    exact lt_irrefl _ hab

/- English proof (translation)
Use extensionality with `x`. Rewrite using `[Ideal.under, Ideal.mem_comap, mem_primeBelow, ← hA x]`. Both sides reduce to the same expression.
-/
theorem under_primeBelow {A : ValuationSubring Ω} {v : HeightOneSpectrum (𝓞 F)}
    (hA : ∀ x : 𝓞 F, A.valuation (algebraMap F Ω (x : F)) < 1 ↔ x ∈ v.asIdeal) :
    (primeBelow (F := F) A).under (𝓞 F) = v.asIdeal := by
  ext x
  rw [Ideal.under, Ideal.mem_comap, mem_primeBelow, ← hA x]
  rfl

/- English proof (translation)
Use extensionality with `b`. Rewrite using `[Ideal.mem_pointwise_smul_iff_inv_smul_mem, mem_primeBelow, mem_primeBelow, smul_valuation_lt_one_iff]`. Both sides reduce to the same expression.
-/
theorem primeBelow_smul (g : Ω ≃ₐ[F] Ω) (A : ValuationSubring Ω) :
    primeBelow (F := F) (g • A) = g • primeBelow (F := F) A := by
  ext b
  rw [Ideal.mem_pointwise_smul_iff_inv_smul_mem, mem_primeBelow, mem_primeBelow,
    smul_valuation_lt_one_iff]
  rfl

end places

section profinite

variable {F Ω : Type*} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω]

variable (F Ω) in

/- English proof (translation)
Use `letI : TopologicalSpace (IntCl F Ω) := ⊥`. Use `haveI : DiscreteTopology (IntCl F Ω) := ⟨rfl⟩`. Use `⟨continuous_discrete_rng.mpr fun c => ?_⟩` and prove the remaining obligations. Rewrite using `[isOpen_iff_forall_mem_open]`. Introduce and unpack `⟨g₀, b₀⟩ h`.

Use `⟨{g : Ω ≃ₐ[F] Ω | g (b₀ : Ω) = g₀ (b₀ : Ω)} ×ˢ {b₀}, ?_, (isOpen_setOf_apply (F := F) (b₀ : Ω) (· = g₀ (b₀ : Ω))).prod (isOpen_discrete _), ⟨rfl, rfl⟩⟩` and prove the remaining obligations. Introduce and unpack `⟨g, b⟩ ⟨hg, hb⟩`. Simplify using `only [Set.mem_singleton_iff] at hb`. Substitute `hb` using the available equality. Simplify using `only [Set.mem_preimage, Set.mem_singleton_iff] at h ⊢`.

Rewrite using `[← h]`. Conclude with `Subtype.ext hg`.
-/
theorem continuousSMul_intCl :
    @ContinuousSMul (Ω ≃ₐ[F] Ω) (IntCl F Ω) _ _ ⊥ := by
  letI : TopologicalSpace (IntCl F Ω) := ⊥
  haveI : DiscreteTopology (IntCl F Ω) := ⟨rfl⟩
  refine ⟨continuous_discrete_rng.mpr fun c => ?_⟩
  rw [isOpen_iff_forall_mem_open]
  rintro ⟨g₀, b₀⟩ h
  refine ⟨{g : Ω ≃ₐ[F] Ω | g (b₀ : Ω) = g₀ (b₀ : Ω)} ×ˢ {b₀}, ?_,
    (isOpen_setOf_apply (F := F) (b₀ : Ω) (· = g₀ (b₀ : Ω))).prod (isOpen_discrete _), ⟨rfl, rfl⟩⟩
  rintro ⟨g, b⟩ ⟨hg, hb⟩
  simp only [Set.mem_singleton_iff] at hb
  subst hb
  simp only [Set.mem_preimage, Set.mem_singleton_iff] at h ⊢
  rw [← h]
  exact Subtype.ext hg

variable (F Ω) in

/- English proof (translation)
Use `⟨fun b hb => ?_⟩` and prove the remaining obligations. Establish `hfix : ∀ σ : Ω ≃ₐ[F] Ω, σ (b : Ω) = b` using `fun σ => congrArg Subtype.val (hb σ)`. Establish `hbot` using `(InfiniteGalois.mem_bot_iff_fixed (b : Ω)).mpr hfix`. Take `⟨c, hc⟩` from `IntermediateField.mem_bot.mp hbot`. Establish `hcint : IsIntegral (𝓞 F) c`.

Establish `: IsIntegral (𝓞 F) (algebraMap F Ω c)` using `hc ▸ b.2`. Conclude with `(isIntegral_algHom_iff (IsScalarTower.toAlgHom (𝓞 F) F Ω) (algebraMap F Ω).injective).mp this`. Take `⟨a, ha⟩` from `(IsIntegrallyClosed.isIntegral_iff (R := 𝓞 F) (K := F)).mp hcint`. Use `⟨a, Subtype.ext ?_⟩` and prove the remaining obligations. Rewrite using `[← hc, ← ha]`.

Both sides reduce to the same expression.
-/
theorem isInvariant_intCl : Algebra.IsInvariant (𝓞 F) (IntCl F Ω) (Ω ≃ₐ[F] Ω) := by
  refine ⟨fun b hb => ?_⟩
  have hfix : ∀ σ : Ω ≃ₐ[F] Ω, σ (b : Ω) = b := fun σ => congrArg Subtype.val (hb σ)
  have hbot := (InfiniteGalois.mem_bot_iff_fixed (b : Ω)).mpr hfix
  obtain ⟨c, hc⟩ := IntermediateField.mem_bot.mp hbot
  have hcint : IsIntegral (𝓞 F) c := by
    have : IsIntegral (𝓞 F) (algebraMap F Ω c) := hc ▸ b.2
    exact (isIntegral_algHom_iff (IsScalarTower.toAlgHom (𝓞 F) F Ω)
      (algebraMap F Ω).injective).mp this
  obtain ⟨a, ha⟩ := (IsIntegrallyClosed.isIntegral_iff (R := 𝓞 F) (K := F)).mp hcint
  refine ⟨a, Subtype.ext ?_⟩
  rw [← hc, ← ha]
  rfl

/- English proof (translation)
Use `letI : TopologicalSpace (IntCl F Ω) := ⊥`. Use `haveI : DiscreteTopology (IntCl F Ω) := ⟨rfl⟩`. Use `haveI := continuousSMul_intCl F Ω`. Use `haveI := isInvariant_intCl F Ω`. Take `⟨g, hg⟩` from `Algebra.IsInvariant.exists_smul_of_under_eq_of_profinite (A := 𝓞 F) (G := Ω ≃ₐ[F] Ω) (primeBelow (F := F) A) (primeBelow (F := F) A') (by rw [under_primeBelow hA, under_primeBelow hA'])`.

Use `⟨g, eq_of_valuation_lt_one_iff F fun b hb => ?_⟩` and prove the remaining obligations. Set `b' : IntCl F Ω` to `⟨b, hb.tower_top⟩`. Express the relevant statement in the definitionally equal form `b' ∈ primeBelow (F := F) (g • A) ↔ b' ∈ primeBelow (F := F) A'`. Rewrite using `[primeBelow_smul, hg]`.
-/
theorem exists_smul_eq_of_over {A A' : ValuationSubring Ω} {v : HeightOneSpectrum (𝓞 F)}
    (hA : ∀ x : 𝓞 F, A.valuation (algebraMap F Ω (x : F)) < 1 ↔ x ∈ v.asIdeal)
    (hA' : ∀ x : 𝓞 F, A'.valuation (algebraMap F Ω (x : F)) < 1 ↔ x ∈ v.asIdeal) :
    ∃ g : Ω ≃ₐ[F] Ω, g • A = A' := by
  letI : TopologicalSpace (IntCl F Ω) := ⊥
  haveI : DiscreteTopology (IntCl F Ω) := ⟨rfl⟩
  haveI := continuousSMul_intCl F Ω
  haveI := isInvariant_intCl F Ω
  obtain ⟨g, hg⟩ := Algebra.IsInvariant.exists_smul_of_under_eq_of_profinite (A := 𝓞 F)
    (G := Ω ≃ₐ[F] Ω) (primeBelow (F := F) A) (primeBelow (F := F) A')
    (by rw [under_primeBelow hA, under_primeBelow hA'])
  refine ⟨g, eq_of_valuation_lt_one_iff F fun b hb => ?_⟩
  let b' : IntCl F Ω := ⟨b, hb.tower_top⟩
  change b' ∈ primeBelow (F := F) (g • A) ↔ b' ∈ primeBelow (F := F) A'
  rw [primeBelow_smul, hg]

/- English proof (translation)
Use `letI : TopologicalSpace (IntCl F Ω) := ⊥`. Use `haveI : DiscreteTopology (IntCl F Ω) := ⟨rfl⟩`. Use `haveI := continuousSMul_intCl F Ω`. Use `haveI := isInvariant_intCl F Ω`. Use `set Q := primeBelow (F := F) A with hQ`.

Use `haveI : v.asIdeal.IsMaximal := v.isMaximal`. Use `haveI : Q.LiesOver v.asIdeal := ⟨(under_primeBelow hA).symm⟩`. Use `haveI : Q.IsMaximal := Ideal.isMaximal_of_isIntegral_of_isMaximal_comap (R := 𝓞 F) Q (by rw [show Ideal.comap (algebraMap (𝓞 F) (IntCl F Ω)) Q = v.asIdeal from under_primeBelow hA]; exact v.isMaximal)`. Use `letI : Field (IntCl F Ω ⧸ Q) := Ideal.Quotient.field Q`. Use `letI : Field (𝓞 F ⧸ v.asIdeal) := Ideal.Quotient.field v.asIdeal`.

Use `letI : Fintype (𝓞 F ⧸ v.asIdeal) := Fintype.ofFinite _`. Use `haveI hBi : Algebra.IsIntegral (𝓞 F) (IntCl F Ω) := inferInstance`. Use `haveI : Algebra.IsIntegral (𝓞 F ⧸ v.asIdeal) (IntCl F Ω ⧸ Q) := Ideal.Quotient.algebra_isIntegral_of_liesOver Q v.asIdeal`. Use `haveI : Algebra.IsAlgebraic (𝓞 F ⧸ v.asIdeal) (IntCl F Ω ⧸ Q) := Algebra.IsIntegral.isAlgebraic`. Set `φ : (IntCl F Ω ⧸ Q) ≃ₐ[𝓞 F ⧸ v.asIdeal] (IntCl F Ω ⧸ Q)` to `FiniteField.frobeniusAlgEquivOfAlgebraic (𝓞 F ⧸ v.asIdeal) (IntCl F Ω ⧸ Q)`.

Take `⟨⟨σ, hσQ⟩, hσ⟩` from `Ideal.Quotient.stabilizerHom_surjective_of_profinite (G := Ω ≃ₐ[F] Ω) v.asIdeal Q φ`. Establish `hσQ' : σ • Q = Q` using `hσQ`. Use `set q := Nat.card (𝓞 F ⧸ v.asIdeal) with hq`. Establish `hqc : Fintype.card (𝓞 F ⧸ v.asIdeal) = q` using `Fintype.card_eq_nat_card`. Establish `hcong : ∀ b : IntCl F Ω, A.valuation (σ (b : Ω) - (b : Ω) ^ q) < 1`.

Introduce `b`. Establish `h1 : Ideal.Quotient.mk Q (σ • b) = Ideal.Quotient.mk Q b ^ Fintype.card (𝓞 F ⧸ v.asIdeal)` using `DFunLike.congr_fun hσ (Ideal.Quotient.mk Q b)`. Establish `h2 : σ • b - b ^ q ∈ Q`. Rewrite using `[← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_pow, h1, hqc, sub_self]`. Conclude with `h2`.

Establish `hdec : σ • A = A`. Use `eq_of_valuation_lt_one_iff F fun b hb => ?_` and prove the remaining obligations. Set `b' : IntCl F Ω` to `⟨b, hb.tower_top⟩`. Express the relevant statement in the definitionally equal form `b' ∈ primeBelow (F := F) (σ • A) ↔ b' ∈ Q`. Rewrite using `[primeBelow_smul, hσQ']`.

Use `⟨σ, hdec, fun x hx => ?_⟩` and prove the remaining obligations. Take `⟨s, t, hs, ht, hs1, e⟩` from `exists_den F A hx`. Establish `hcs` using `hcong ⟨s, hs.tower_top⟩`. Establish `hct` using `hcong ⟨t, ht.tower_top⟩`. Establish `hvt : A.valuation t ≤ 1` using `(A.valuation_le_one_iff _).mpr (mem_of_isIntegral_int A ht)`.

Establish `hσs : A.valuation (σ s) = 1`. Use `le_antisymm ((A.valuation_le_one_iff _).mpr (mem_of_isIntegral_int A (hs.map ((σ : Ω ≃ₐ[F] Ω).toAlgHom.restrictScalars ℤ)))) ?_` and prove the remaining obligations. Establish `h3 : ¬ (σ • A).valuation (σ s) < 1`. Rewrite using `[smul_valuation_lt_one_iff]`. Establish `: (σ⁻¹ : Ω ≃ₐ[F] Ω) (σ s) = s` using `by show (σ⁻¹ * σ) s = s`.

Simplify using the standard rewrite rules. Rewrite using `[this, hs1]`. Conclude with `lt_irrefl 1`. Rewrite `h3` using `[hdec]`. Conclude with `not_lt.mp h3`.

Establish `he' : σ s * σ x = σ t` using `by rw [← map_mul, e]`. Establish `key : s ^ q * σ s * (σ x - x ^ q) = s ^ q * (σ t - t ^ q) + t ^ q * (s ^ q - σ s)`. Rewrite using `[← he', ← e]`. Expand and normalize the polynomial expressions, which then agree. Establish `hv : A.valuation (s ^ q * σ s * (σ x - x ^ q)) < 1`.

Rewrite using `[key]`. Apply `Valuation.map_add_lt` to reduce the goal to its premises. Rewrite using `[Valuation.map_mul, Valuation.map_pow, hs1, one_pow, one_mul]`. Conclude with `hct`. Rewrite using `[Valuation.map_mul, Valuation.map_sub_swap]`.

Combine the equalities or inequalities in the displayed calculation. Rewrite `hv` using `[Valuation.map_mul, Valuation.map_mul, Valuation.map_pow, hs1, hσs, one_pow, one_mul, one_mul]`. Conclude with `hv`.
-/
theorem exists_frob_over {A : ValuationSubring Ω} {v : HeightOneSpectrum (𝓞 F)}
    (hA : ∀ x : 𝓞 F, A.valuation (algebraMap F Ω (x : F)) < 1 ↔ x ∈ v.asIdeal) :
    ∃ σ : Ω ≃ₐ[F] Ω, σ • A = A ∧ ∀ x, A.valuation x ≤ 1 →
      A.valuation (σ x - x ^ Nat.card (𝓞 F ⧸ v.asIdeal)) < 1 := by
  letI : TopologicalSpace (IntCl F Ω) := ⊥
  haveI : DiscreteTopology (IntCl F Ω) := ⟨rfl⟩
  haveI := continuousSMul_intCl F Ω
  haveI := isInvariant_intCl F Ω
  set Q := primeBelow (F := F) A with hQ
  haveI : v.asIdeal.IsMaximal := v.isMaximal
  haveI : Q.LiesOver v.asIdeal := ⟨(under_primeBelow hA).symm⟩
  haveI : Q.IsMaximal := Ideal.isMaximal_of_isIntegral_of_isMaximal_comap (R := 𝓞 F) Q
    (by rw [show Ideal.comap (algebraMap (𝓞 F) (IntCl F Ω)) Q = v.asIdeal from
      under_primeBelow hA]; exact v.isMaximal)
  letI : Field (IntCl F Ω ⧸ Q) := Ideal.Quotient.field Q
  letI : Field (𝓞 F ⧸ v.asIdeal) := Ideal.Quotient.field v.asIdeal
  letI : Fintype (𝓞 F ⧸ v.asIdeal) := Fintype.ofFinite _
  haveI hBi : Algebra.IsIntegral (𝓞 F) (IntCl F Ω) := inferInstance
  haveI : Algebra.IsIntegral (𝓞 F ⧸ v.asIdeal) (IntCl F Ω ⧸ Q) :=
    Ideal.Quotient.algebra_isIntegral_of_liesOver Q v.asIdeal
  haveI : Algebra.IsAlgebraic (𝓞 F ⧸ v.asIdeal) (IntCl F Ω ⧸ Q) := Algebra.IsIntegral.isAlgebraic
  let φ : (IntCl F Ω ⧸ Q) ≃ₐ[𝓞 F ⧸ v.asIdeal] (IntCl F Ω ⧸ Q) :=
    FiniteField.frobeniusAlgEquivOfAlgebraic (𝓞 F ⧸ v.asIdeal) (IntCl F Ω ⧸ Q)
  obtain ⟨⟨σ, hσQ⟩, hσ⟩ := Ideal.Quotient.stabilizerHom_surjective_of_profinite
    (G := Ω ≃ₐ[F] Ω) v.asIdeal Q φ
  have hσQ' : σ • Q = Q := hσQ
  set q := Nat.card (𝓞 F ⧸ v.asIdeal) with hq
  have hqc : Fintype.card (𝓞 F ⧸ v.asIdeal) = q := Fintype.card_eq_nat_card
  have hcong : ∀ b : IntCl F Ω, A.valuation (σ (b : Ω) - (b : Ω) ^ q) < 1 := by
    intro b
    have h1 : Ideal.Quotient.mk Q (σ • b) =
        Ideal.Quotient.mk Q b ^ Fintype.card (𝓞 F ⧸ v.asIdeal) :=
      DFunLike.congr_fun hσ (Ideal.Quotient.mk Q b)
    have h2 : σ • b - b ^ q ∈ Q := by
      rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_pow, h1, hqc, sub_self]
    exact h2
  have hdec : σ • A = A := by
    refine eq_of_valuation_lt_one_iff F fun b hb => ?_
    let b' : IntCl F Ω := ⟨b, hb.tower_top⟩
    change b' ∈ primeBelow (F := F) (σ • A) ↔ b' ∈ Q
    rw [primeBelow_smul, hσQ']
  refine ⟨σ, hdec, fun x hx => ?_⟩
  obtain ⟨s, t, hs, ht, hs1, e⟩ := exists_den F A hx
  have hcs := hcong ⟨s, hs.tower_top⟩
  have hct := hcong ⟨t, ht.tower_top⟩
  have hvt : A.valuation t ≤ 1 := (A.valuation_le_one_iff _).mpr (mem_of_isIntegral_int A ht)
  have hσs : A.valuation (σ s) = 1 := by
    refine le_antisymm ((A.valuation_le_one_iff _).mpr (mem_of_isIntegral_int A
      (hs.map ((σ : Ω ≃ₐ[F] Ω).toAlgHom.restrictScalars ℤ)))) ?_
    have h3 : ¬ (σ • A).valuation (σ s) < 1 := by
      rw [smul_valuation_lt_one_iff]
      have : (σ⁻¹ : Ω ≃ₐ[F] Ω) (σ s) = s := by
        show (σ⁻¹ * σ) s = s
        simp
      rw [this, hs1]
      exact lt_irrefl 1
    rw [hdec] at h3
    exact not_lt.mp h3
  have he' : σ s * σ x = σ t := by rw [← map_mul, e]
  have key : s ^ q * σ s * (σ x - x ^ q) = s ^ q * (σ t - t ^ q) + t ^ q * (s ^ q - σ s) := by
    rw [← he', ← e]; ring
  have hv : A.valuation (s ^ q * σ s * (σ x - x ^ q)) < 1 := by
    rw [key]
    apply Valuation.map_add_lt
    · rw [Valuation.map_mul, Valuation.map_pow, hs1, one_pow, one_mul]
      exact hct
    · rw [Valuation.map_mul, Valuation.map_sub_swap]
      calc A.valuation (t ^ q) * A.valuation (σ s - s ^ q) ≤ 1 * A.valuation (σ s - s ^ q) :=
            mul_le_mul_left (by rw [Valuation.map_pow]; exact pow_le_one' hvt q) _
        _ < 1 := by rw [one_mul]; exact hcs
  rw [Valuation.map_mul, Valuation.map_mul, Valuation.map_pow, hs1, hσs, one_pow, one_mul,
    one_mul] at hv
  exact hv

end profinite

end ReciprocityTheory.Gal

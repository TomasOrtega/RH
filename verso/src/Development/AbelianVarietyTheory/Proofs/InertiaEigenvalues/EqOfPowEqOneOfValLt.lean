import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.DataN
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemZpowersOfTameGen
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ValRootEqOne
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.FrobeniusOrbits

namespace GlobalTheory.TameCharDet

open scoped Pointwise

/- English proof (translation)
Use `first`. Consider the case `exact @_root_.GlobalTheory.RootValuationOne.main`. Consider the case `exact _root_.GlobalTheory.RootValuationOne.main`. Consider the case `(apply _root_.GlobalTheory.RootValuationOne.main <;> assumption)`. Consider the case `(intros; apply _root_.GlobalTheory.RootValuationOne.main <;> assumption)`.

Consider the case `(intros; apply @_root_.GlobalTheory.RootValuationOne.main <;> first | assumption | infer_instance)`. Consider the case `(intros; exact _root_.GlobalTheory.RootValuationOne.main ..)`.
-/
theorem eq_of_pow_eq_one_of_val_lt {Ω : Type} [Field Ω] (A : ValuationSubring Ω) (n : ℕ)
    (hn : ¬ A.valuation (n : Ω) < 1) {ξ ξ' : Ω} (h : ξ ^ n = 1) (h' : ξ' ^ n = 1)
    (hlt : A.valuation (ξ - ξ') < 1) : ξ = ξ' := by
  first
  | exact @_root_.GlobalTheory.RootValuationOne.main
  | exact _root_.GlobalTheory.RootValuationOne.main
  | (apply _root_.GlobalTheory.RootValuationOne.main <;> assumption)
  | (intros; apply _root_.GlobalTheory.RootValuationOne.main <;> assumption)
  | (intros; apply @_root_.GlobalTheory.RootValuationOne.main <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.RootValuationOne.main ..)

/- English proof (translation)
Introduce `E Ω _ _ _ _ _ v A hA γ hγ K _ _ _ r hr n hn hnv hI π e hπ he hord σ hσ hσv`. Establish `hn0 : n ≠ 0` using `hn.ne'`. Establish `hnA : ¬ A.valuation (n : Ω) < 1`. Introduce `h`. Apply `hnv` to reduce the goal to its premises.

Rewrite using `[← hA]`. Simplify using `using h`. Use `set ζ := γ π / π with hζ`. Establish `hζn : ζ ^ n = 1` using `by rw [← hord]; exact pow_orderOf_eq_one ζ`. Establish `hγn : r γ ^ n = 1` using `hI γ hγ.1`.

Establish `hred : ∀ {M : Type} [Monoid M] (x : M), x ^ n = 1 → ∀ a : ℕ, x ^ a = x ^ (a % n)`. Introduce `M _ x hx a`. Use `conv_lhs => rw [← Nat.div_add_mod a n, pow_add, pow_mul, hx, one_pow, one_mul]`. Establish `hvζ : A.valuation ζ = 1`. Establish `hp : A.valuation ζ ^ n = 1` using `by rw [← map_pow, hζn, map_one]`.

Break down `lt_trichotomy (A.valuation ζ) 1 with hl | he | hg` into its components or cases. Conclude with `absurd hp (pow_lt_one₀ zero_le' hl hn0).ne`. Conclude with `he`. Conclude with `absurd hp (one_lt_pow₀ hg hn0).ne'`. Establish `hfixζ : ∀ τ ∈ Ine (F` using `E) A, τ ζ = ζ := by`.

Introduce `τ hτ`. Use `eq_of_pow_eq_one_of_val_lt A n hnA ?_ hζn (hτ.2 ζ hvζ.le)` and prove the remaining obligations. Rewrite using `[← map_pow, hζn, map_one]`. Establish `hfixπ : ∀ τ : Formalism.ConjugateSelfDual.G E Ω, (∀ y : Ω, y ≠ 0 → A.valuation (τ y / y - 1) < 1) → τ π = π`. Introduce `τ hτ`.

Establish `h1 : (τ π / π) ^ n = 1`. Rewrite using `[div_pow, ← map_pow, he, AlgEquiv.commutes, div_self]`. Rewrite using `[← he]`. Conclude with `pow_ne_zero _ hπ`. Establish `h2` using `eq_of_pow_eq_one_of_val_lt A n hnA h1 (one_pow n) (hτ π hπ)`.

Rewrite `h2` using `[div_eq_one_iff_eq hπ]`. Then use the resulting hypothesis. Establish `hw : ∀ τ : Formalism.ConjugateSelfDual.G E Ω, (∀ y : Ω, y ≠ 0 → A.valuation (τ y / y - 1) < 1) → r τ = 1`. Introduce `τ hτ`. Assume the negation of the conclusion as `hne`. Establish `hd : orderOf (r τ) ∣ n` using `orderOf_dvd_of_pow_eq_one (hI τ (GlobalTheory.TameGenPowers.wild_mem_Ine hτ))`.

Establish `hne1 : orderOf (r τ) ≠ 1` using `by rwa [Ne, orderOf_eq_one_iff]`. Take `⟨l, hl, k, hk⟩` from `Nat.exists_prime_and_dvd hne1`. Establish `hlv : ((l : ℕ) : 𝓞 E) ∉ v.asIdeal`. Introduce `h`. Apply `hnv` to reduce the goal to its premises.

Take `⟨c, hc⟩` from `hd`. Rewrite using `[hc, hk]`. Use `push_cast`. Conclude with `Ideal.mul_mem_right _ _ (Ideal.mul_mem_right _ _ h)`. Establish `h1 : r (τ ^ k) = 1`.

Use `GlobalTheory.TameGenPowers.eq_one_of_wild_prime E Ω v A hA K r hr l hl hlv _ (GlobalTheory.WildInertiaChar.wild_pow A τ hτ k) ?_` and prove the remaining obligations. Rewrite using `[map_pow, ← pow_mul, mul_comm, ← hk, pow_orderOf_eq_one]`. Rewrite `h1` using `[map_pow]`. Establish `h2` using `orderOf_dvd_of_pow_eq_one h1`. Establish `ho : orderOf (r τ) ≠ 0` using `fun h => hn0 (by simpa [h] using hd)`.

Establish `hk0 : k ≠ 0`. Introduce and unpack `rfl`. Conclude with `ho (by simpa using hk)`. Establish `h3` using `Nat.le_of_dvd (Nat.pos_of_ne_zero hk0) h2`. Rewrite `h3` using `[hk]`.

Use `hl.two_le` as an intermediate fact. Use `Nat.pos_of_ne_zero hk0` as an intermediate fact. Use the polynomial consequences of the given equalities and inequalities. Establish `hint : IsIntegral E π` using `Algebra.IsIntegral.isIntegral π`. Use `haveI : FiniteDimensional E (IntermediateField.adjoin E {π}) := IntermediateField.adjoin.finiteDimensional hint`.

Establish `hHo : IsOpen ((IntermediateField.adjoin E {π}).fixingSubgroup : Set (Formalism.ConjugateSelfDual.G E Ω))` using `IntermediateField.fixingSubgroup_isOpen _`. Establish `hfixH : ∀ τ g : Formalism.ConjugateSelfDual.G E Ω, g ∈ (IntermediateField.adjoin E {π}).fixingSubgroup → (τ * g) π = τ π`. Introduce `τ g hg`. Rewrite using `[AlgEquiv.mul_apply, (IntermediateField.mem_fixingSubgroup_iff _ _).1 hg π (IntermediateField.mem_adjoin_simple_self E π)]`. Establish `hopen : ∀ U : Set (Formalism.ConjugateSelfDual.G E Ω), (∀ τ ∈ U, ∀ g ∈ (IntermediateField.adjoin E {π}).fixingSubgroup, τ * g ∈ U) → IsOpen U`.

Introduce `U hU`. Rewrite using `[isOpen_iff_mem_nhds]`. Introduce `τ hτ`. Rewrite using `[← map_mul_left_nhds_one τ]`. Conclude with `Filter.mem_map.2 (Filter.mem_of_superset (hHo.mem_nhds (one_mem _)) fun g hg => hU τ hτ g hg)`.

Establish `hloc : ∀ c : Ω, IsClosed {τ : Formalism.ConjugateSelfDual.G E Ω | τ π = c}`. Introduce `c`. Rewrite using `[← isOpen_compl_iff]`. Use `hopen _ fun τ hτ g hg => ?_` and prove the remaining obligations. Simplify using `only [Set.mem_compl_iff, Set.mem_setOf_eq] at hτ ⊢`.

Rewrite using `[hfixH τ g hg]` and apply the resulting hypothesis. Set `T : Set (Formalism.ConjugateSelfDual.G E Ω)` to `⋃ a ∈ Finset.range n, {τ | r τ = r γ ^ a ∧ τ π = ζ ^ a * π}`. Establish `hTc : IsClosed T`. Use `isClosed_biUnion_finset fun a _ => ?_` and prove the remaining obligations. Conclude with `(isClosed_singleton.preimage hr).inter (hloc _)`.

Set `P : Formalism.ConjugateSelfDual.G E Ω → Prop` to `fun τ => τ ∈ Ine (F := E) A ∧ ∃ a : ℕ, r τ = r γ ^ a ∧ τ π = ζ ^ a * π`. Establish `hP : ∀ τ ∈ Subgroup.closure (insert γ {σ : Formalism.ConjugateSelfDual.G E Ω | ∀ y : Ω, y ≠ 0 → A.valuation (σ y / y - 1) < 1}), P τ`. Introduce `τ hτ`. Proceed by induction on `hτ using Subgroup.closure_induction with`. Consider the case `mem x hx`.

Break down `hx with rfl | hx` into its components or cases. Conclude with `⟨hγ.1, 1, (pow_one _).symm, by rw [pow_one, hζ, div_mul_cancel₀ _ hπ]⟩`. Conclude with `⟨GlobalTheory.TameGenPowers.wild_mem_Ine hx, 0, by rw [hw x hx, pow_zero], by rw [hfixπ x hx, pow_zero, one_mul]⟩`. Consider the case `one => exact ⟨one_mem _, 0, by rw [map_one, pow_zero], by rw [pow_zero, one_mul]; rfl⟩`. Consider the case `mul x y _ _ ihx ihy`.

Take `⟨hxI, a, ha, haπ⟩` from `ihx`. Take `⟨hyI, b, hb, hbπ⟩` from `ihy`. Use `⟨mul_mem hxI hyI, a + b, by rw [map_mul, ha, hb, pow_add], ?_⟩` and prove the remaining obligations. Rewrite using `[AlgEquiv.mul_apply, hbπ, map_mul, map_pow, hfixζ x hxI, haπ, pow_add]`. Expand and normalize the polynomial expressions, which then agree.

Consider the case `inv x _ ihx`. Take `⟨hxI, a, ha, haπ⟩` from `ihx`. Establish `hiI : x⁻¹ ∈ Ine (F` using `E) A := inv_mem hxI`. Establish `hex : a * (n - 1) + a = a * n`. Rewrite using `[← Nat.mul_succ, Nat.succ_eq_add_one, Nat.sub_add_cancel hn]`.

Use `⟨hiI, a * (n - 1), ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[map_inv, ha]`. Use `symm`. Use `eq_inv_of_mul_eq_one_left ?_` and prove the remaining obligations. Rewrite using `[← pow_add, hex, pow_mul', hγn, one_pow]`.

Establish `hxx : (x⁻¹ : Formalism.ConjugateSelfDual.G E Ω) (x π) = π`. Rewrite using `[← AlgEquiv.mul_apply, inv_mul_cancel]`. Both sides reduce to the same expression. Establish `h1 : π = ζ ^ a * (x⁻¹ : Formalism.ConjugateSelfDual.G E Ω) π`. Establish `h2` using `congrArg (fun y => (x⁻¹ : Formalism.ConjugateSelfDual.G E Ω) y) haπ`.

Rewrite `h2` using `[hxx, map_mul, map_pow, hfixζ _ hiI]`. Conclude with `h2`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[hex, pow_mul', hζn, one_pow, one_mul]`. Use `_ = ζ ^ (a * (n - 1)) * (ζ ^ a * (x⁻¹ : Formalism.ConjugateSelfDual.G E Ω) π) := by ring`.

Use `_ = ζ ^ (a * (n - 1)) * π := by rw [← h1]`. Establish `hST : ((Subgroup.closure (insert γ {σ : Formalism.ConjugateSelfDual.G E Ω | ∀ y : Ω, y ≠ 0 → A.valuation (σ y / y - 1) < 1}) : Subgroup (Formalism.ConjugateSelfDual.G E Ω)) : Set (Formalism.ConjugateSelfDual.G E Ω)) ⊆ T`. Introduce `τ hτ`. Take `⟨-, a, ha, haπ⟩` from `hP τ hτ`. Use `Set.mem_biUnion (x := a % n) (Finset.mem_coe.2 (Finset.mem_range.2 (Nat.mod_lt _ hn))) ?_` and prove the remaining obligations.

Conclude with `⟨by rw [ha, hred _ hγn a], by rw [haπ, hred _ hζn a]⟩`. Establish `hσT : σ ∈ T` using `closure_minimal hST hTc (hγ.2 hσ)`. Choose the witnesses or unpack the hypotheses as in `⟨a, ha, haπ⟩ : ∃ a : ℕ, r σ = r γ ^ a ∧ σ π = ζ ^ a * π := by`. Simplify using `only [T, Set.mem_iUnion] at hσT`. Take `⟨a, -, h⟩` from `hσT`.

Conclude with `⟨a, h⟩`. Establish `hq : σ π / π = ζ ^ a` using `by rw [haπ, mul_div_assoc, div_self hπ, mul_one]`. Rewrite `hσv` using `[hq]`. Establish `hζa : ζ ^ a = ζ`. Use `eq_of_pow_eq_one_of_val_lt A n hnA ?_ hζn hσv` and prove the remaining obligations.

Rewrite using `[← pow_mul, mul_comm, pow_mul, hζn, one_pow]`. Establish `hmod : a ≡ 1 [MOD n]`. Break down `Nat.eq_zero_or_pos a with rfl | ha0` into its components or cases. Establish `h1 : orderOf ζ = 1` using `orderOf_eq_one_iff.2 (by rw [← hζa, pow_zero])`. Rewrite using `[← hord, h1]`.

Conclude with `Nat.modEq_one`. Establish `hζ0 : ζ ≠ 0`. Introduce `h`. Rewrite `hζn` using `[h, zero_pow hn0]`. Conclude with `zero_ne_one hζn`.

Establish `h1 : ζ ^ (a - 1) = 1`. Establish `h3 : ζ ^ (a - 1) * ζ = 1 * ζ`. Rewrite using `[← pow_succ, Nat.sub_add_cancel ha0, hζa, one_mul]`. Conclude with `mul_right_cancel₀ hζ0 h3`. Establish `h2` using `orderOf_dvd_of_pow_eq_one h1`.

Rewrite `h2` using `[hord]`. Conclude with `((Nat.modEq_iff_dvd' ha0).2 h2).symm`. Rewrite using `[ha]`. Use `conv_rhs => rw [← pow_one (r γ)]`. Conclude with `(pow_eq_pow_iff_modEq).2 (hmod.of_dvd (orderOf_dvd_of_pow_eq_one hγn))`.
-/
theorem eq_of_tameChar : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (v : HeightOneSpectrum (𝓞 E)) (A : ValuationSubring Ω), Formalism.ConjugateSelfDual.IsPlaceOver A v → ∀ γ : Formalism.ConjugateSelfDual.G E Ω, TameGenAt A γ → ∀ (K : Type) [Field K] [TopologicalSpace K] [T2Space K] (r : Formalism.ConjugateSelfDual.G E Ω →* Kˣ), Continuous r → ∀ n : ℕ, 0 < n → ((n : ℕ) : 𝓞 E) ∉ v.asIdeal → (∀ σ ∈ Ine (F := E) A, r σ ^ n = 1) → ∀ (π : Ω) (e : E), π ≠ 0 → π ^ n = algebraMap E Ω e → orderOf (γ π / π) = n → ∀ σ ∈ Ine (F := E) A, A.valuation (σ π / π - γ π / π) < 1 → r σ = r γ := by
  intro E Ω _ _ _ _ _ v A hA γ hγ K _ _ _ r hr n hn hnv hI π e hπ he hord σ hσ hσv
  have hn0 : n ≠ 0 := hn.ne'
  have hnA : ¬ A.valuation (n : Ω) < 1 := by
    intro h
    apply hnv
    rw [← hA]
    simpa using h
  set ζ := γ π / π with hζ
  have hζn : ζ ^ n = 1 := by rw [← hord]; exact pow_orderOf_eq_one ζ
  have hγn : r γ ^ n = 1 := hI γ hγ.1
  have hred : ∀ {M : Type} [Monoid M] (x : M), x ^ n = 1 → ∀ a : ℕ, x ^ a = x ^ (a % n) := by
    intro M _ x hx a
    conv_lhs => rw [← Nat.div_add_mod a n, pow_add, pow_mul, hx, one_pow, one_mul]
  have hvζ : A.valuation ζ = 1 := by
    have hp : A.valuation ζ ^ n = 1 := by rw [← map_pow, hζn, map_one]
    rcases lt_trichotomy (A.valuation ζ) 1 with hl | he | hg
    · exact absurd hp (pow_lt_one₀ zero_le' hl hn0).ne
    · exact he
    · exact absurd hp (one_lt_pow₀ hg hn0).ne'

  have hfixζ : ∀ τ ∈ Ine (F := E) A, τ ζ = ζ := by
    intro τ hτ
    refine eq_of_pow_eq_one_of_val_lt A n hnA ?_ hζn (hτ.2 ζ hvζ.le)
    rw [← map_pow, hζn, map_one]

  have hfixπ : ∀ τ : Formalism.ConjugateSelfDual.G E Ω, (∀ y : Ω, y ≠ 0 → A.valuation (τ y / y - 1) < 1) → τ π = π := by
    intro τ hτ
    have h1 : (τ π / π) ^ n = 1 := by
      rw [div_pow, ← map_pow, he, AlgEquiv.commutes, div_self]
      rw [← he]; exact pow_ne_zero _ hπ
    have h2 := eq_of_pow_eq_one_of_val_lt A n hnA h1 (one_pow n) (hτ π hπ)
    rwa [div_eq_one_iff_eq hπ] at h2

  have hw : ∀ τ : Formalism.ConjugateSelfDual.G E Ω, (∀ y : Ω, y ≠ 0 → A.valuation (τ y / y - 1) < 1) → r τ = 1 := by
    intro τ hτ
    by_contra hne
    have hd : orderOf (r τ) ∣ n := orderOf_dvd_of_pow_eq_one (hI τ (GlobalTheory.TameGenPowers.wild_mem_Ine hτ))
    have hne1 : orderOf (r τ) ≠ 1 := by rwa [Ne, orderOf_eq_one_iff]
    obtain ⟨l, hl, k, hk⟩ := Nat.exists_prime_and_dvd hne1
    have hlv : ((l : ℕ) : 𝓞 E) ∉ v.asIdeal := by
      intro h
      apply hnv
      obtain ⟨c, hc⟩ := hd
      rw [hc, hk]
      push_cast
      exact Ideal.mul_mem_right _ _ (Ideal.mul_mem_right _ _ h)
    have h1 : r (τ ^ k) = 1 := by
      refine GlobalTheory.TameGenPowers.eq_one_of_wild_prime E Ω v A hA K r hr l hl hlv _
        (GlobalTheory.WildInertiaChar.wild_pow A τ hτ k) ?_
      rw [map_pow, ← pow_mul, mul_comm, ← hk, pow_orderOf_eq_one]
    rw [map_pow] at h1
    have h2 := orderOf_dvd_of_pow_eq_one h1
    have ho : orderOf (r τ) ≠ 0 := fun h => hn0 (by simpa [h] using hd)
    have hk0 : k ≠ 0 := by
      rintro rfl
      exact ho (by simpa using hk)
    have h3 := Nat.le_of_dvd (Nat.pos_of_ne_zero hk0) h2
    rw [hk] at h3
    have := hl.two_le
    have := Nat.pos_of_ne_zero hk0
    nlinarith

  have hint : IsIntegral E π := Algebra.IsIntegral.isIntegral π
  haveI : FiniteDimensional E (IntermediateField.adjoin E {π}) :=
    IntermediateField.adjoin.finiteDimensional hint
  have hHo : IsOpen ((IntermediateField.adjoin E {π}).fixingSubgroup : Set (Formalism.ConjugateSelfDual.G E Ω)) :=
    IntermediateField.fixingSubgroup_isOpen _
  have hfixH : ∀ τ g : Formalism.ConjugateSelfDual.G E Ω, g ∈ (IntermediateField.adjoin E {π}).fixingSubgroup →
      (τ * g) π = τ π := by
    intro τ g hg
    rw [AlgEquiv.mul_apply, (IntermediateField.mem_fixingSubgroup_iff _ _).1 hg π
      (IntermediateField.mem_adjoin_simple_self E π)]
  have hopen : ∀ U : Set (Formalism.ConjugateSelfDual.G E Ω), (∀ τ ∈ U, ∀ g ∈ (IntermediateField.adjoin E {π}).fixingSubgroup,
      τ * g ∈ U) → IsOpen U := by
    intro U hU
    rw [isOpen_iff_mem_nhds]
    intro τ hτ
    rw [← map_mul_left_nhds_one τ]
    exact Filter.mem_map.2 (Filter.mem_of_superset (hHo.mem_nhds (one_mem _)) fun g hg => hU τ hτ g hg)
  have hloc : ∀ c : Ω, IsClosed {τ : Formalism.ConjugateSelfDual.G E Ω | τ π = c} := by
    intro c
    rw [← isOpen_compl_iff]
    refine hopen _ fun τ hτ g hg => ?_
    simp only [Set.mem_compl_iff, Set.mem_setOf_eq] at hτ ⊢
    rwa [hfixH τ g hg]
  let T : Set (Formalism.ConjugateSelfDual.G E Ω) := ⋃ a ∈ Finset.range n, {τ | r τ = r γ ^ a ∧ τ π = ζ ^ a * π}
  have hTc : IsClosed T := by
    refine isClosed_biUnion_finset fun a _ => ?_
    exact (isClosed_singleton.preimage hr).inter (hloc _)

  let P : Formalism.ConjugateSelfDual.G E Ω → Prop := fun τ =>
    τ ∈ Ine (F := E) A ∧ ∃ a : ℕ, r τ = r γ ^ a ∧ τ π = ζ ^ a * π
  have hP : ∀ τ ∈ Subgroup.closure (insert γ
      {σ : Formalism.ConjugateSelfDual.G E Ω | ∀ y : Ω, y ≠ 0 → A.valuation (σ y / y - 1) < 1}), P τ := by
    intro τ hτ
    induction hτ using Subgroup.closure_induction with
    | mem x hx =>
      rcases hx with rfl | hx
      · exact ⟨hγ.1, 1, (pow_one _).symm, by rw [pow_one, hζ, div_mul_cancel₀ _ hπ]⟩
      · exact ⟨GlobalTheory.TameGenPowers.wild_mem_Ine hx, 0, by rw [hw x hx, pow_zero],
          by rw [hfixπ x hx, pow_zero, one_mul]⟩
    | one => exact ⟨one_mem _, 0, by rw [map_one, pow_zero], by rw [pow_zero, one_mul]; rfl⟩
    | mul x y _ _ ihx ihy =>
      obtain ⟨hxI, a, ha, haπ⟩ := ihx
      obtain ⟨hyI, b, hb, hbπ⟩ := ihy
      refine ⟨mul_mem hxI hyI, a + b, by rw [map_mul, ha, hb, pow_add], ?_⟩
      rw [AlgEquiv.mul_apply, hbπ, map_mul, map_pow, hfixζ x hxI, haπ, pow_add]
      ring
    | inv x _ ihx =>
      obtain ⟨hxI, a, ha, haπ⟩ := ihx
      have hiI : x⁻¹ ∈ Ine (F := E) A := inv_mem hxI
      have hex : a * (n - 1) + a = a * n := by
        rw [← Nat.mul_succ, Nat.succ_eq_add_one, Nat.sub_add_cancel hn]
      refine ⟨hiI, a * (n - 1), ?_, ?_⟩
      · rw [map_inv, ha]
        symm
        refine eq_inv_of_mul_eq_one_left ?_
        rw [← pow_add, hex, pow_mul', hγn, one_pow]
      · have hxx : (x⁻¹ : Formalism.ConjugateSelfDual.G E Ω) (x π) = π := by
          rw [← AlgEquiv.mul_apply, inv_mul_cancel]; rfl
        have h1 : π = ζ ^ a * (x⁻¹ : Formalism.ConjugateSelfDual.G E Ω) π := by
          have h2 := congrArg (fun y => (x⁻¹ : Formalism.ConjugateSelfDual.G E Ω) y) haπ
          rw [hxx, map_mul, map_pow, hfixζ _ hiI] at h2
          exact h2
        calc (x⁻¹ : Formalism.ConjugateSelfDual.G E Ω) π = ζ ^ (a * (n - 1) + a) * (x⁻¹ : Formalism.ConjugateSelfDual.G E Ω) π := by
              rw [hex, pow_mul', hζn, one_pow, one_mul]
          _ = ζ ^ (a * (n - 1)) * (ζ ^ a * (x⁻¹ : Formalism.ConjugateSelfDual.G E Ω) π) := by ring
          _ = ζ ^ (a * (n - 1)) * π := by rw [← h1]
  have hST : ((Subgroup.closure (insert γ
      {σ : Formalism.ConjugateSelfDual.G E Ω | ∀ y : Ω, y ≠ 0 → A.valuation (σ y / y - 1) < 1}) : Subgroup (Formalism.ConjugateSelfDual.G E Ω)) :
        Set (Formalism.ConjugateSelfDual.G E Ω)) ⊆ T := by
    intro τ hτ
    obtain ⟨-, a, ha, haπ⟩ := hP τ hτ
    refine Set.mem_biUnion (x := a % n) (Finset.mem_coe.2 (Finset.mem_range.2 (Nat.mod_lt _ hn))) ?_
    exact ⟨by rw [ha, hred _ hγn a], by rw [haπ, hred _ hζn a]⟩
  have hσT : σ ∈ T := closure_minimal hST hTc (hγ.2 hσ)
  obtain ⟨a, ha, haπ⟩ : ∃ a : ℕ, r σ = r γ ^ a ∧ σ π = ζ ^ a * π := by
    simp only [T, Set.mem_iUnion] at hσT
    obtain ⟨a, -, h⟩ := hσT
    exact ⟨a, h⟩
  have hq : σ π / π = ζ ^ a := by rw [haπ, mul_div_assoc, div_self hπ, mul_one]
  rw [hq] at hσv
  have hζa : ζ ^ a = ζ := by
    refine eq_of_pow_eq_one_of_val_lt A n hnA ?_ hζn hσv
    rw [← pow_mul, mul_comm, pow_mul, hζn, one_pow]
  have hmod : a ≡ 1 [MOD n] := by
    rcases Nat.eq_zero_or_pos a with rfl | ha0
    · have h1 : orderOf ζ = 1 := orderOf_eq_one_iff.2 (by rw [← hζa, pow_zero])
      rw [← hord, h1]; exact Nat.modEq_one
    · have hζ0 : ζ ≠ 0 := by
        intro h; rw [h, zero_pow hn0] at hζn; exact zero_ne_one hζn
      have h1 : ζ ^ (a - 1) = 1 := by
        have h3 : ζ ^ (a - 1) * ζ = 1 * ζ := by
          rw [← pow_succ, Nat.sub_add_cancel ha0, hζa, one_mul]
        exact mul_right_cancel₀ hζ0 h3
      have h2 := orderOf_dvd_of_pow_eq_one h1
      rw [hord] at h2
      exact ((Nat.modEq_iff_dvd' ha0).2 h2).symm
  rw [ha]
  conv_rhs => rw [← pow_one (r γ)]
  exact (pow_eq_pow_iff_modEq).2 (hmod.of_dvd (orderOf_dvd_of_pow_eq_one hγn))

end GlobalTheory.TameCharDet

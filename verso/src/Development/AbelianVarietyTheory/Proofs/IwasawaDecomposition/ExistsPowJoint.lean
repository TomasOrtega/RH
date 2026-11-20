import Mathlib
import Formalism.LocalToGlobal.NormalizedHeckeFactors.RingHomOfBaseOrderToFraction
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemZpowersOfTameGen
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsTameGenAtOfValuationSubring
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EqOfPowEqOneOfValLt
open NumberField IsDedekindDomain

namespace GlobalTheory.TameJoint

/- English proof (translation)
Introduce `E Ω _ _ _ _ _ M _ φ P A L γ π w hA hker hL hγ hw hγL hπ he σ hσ`. Establish `hL0 : L ≠ 0` using `by rintro rfl; exact hL (by simp)`. Establish `hn : 0 < L` using `Nat.pos_of_ne_zero hL0`. Establish `hLA : ¬ A.valuation (L : Ω) < 1`. Introduce `h`.

Apply `hL` to reduce the goal to its premises. Rewrite using `[← hA]`. Simplify using `using h`. Use `set ζ := γ π / π with hζ`. Establish `hζn : ζ ^ L = 1`.

Rewrite using `[hζ, div_pow, ← map_pow, he, AlgEquiv.commutes, div_self]`. Rewrite using `[← he]`. Conclude with `pow_ne_zero _ hπ`. Establish `hred : ∀ {N : Type} [Monoid N] (x : N), x ^ L = 1 → ∀ a : ℕ, x ^ a = x ^ (a % L)`. Introduce `N _ x hx a`.

Use `conv_lhs => rw [← Nat.div_add_mod a L, pow_add, pow_mul, hx, one_pow, one_mul]`. Establish `hvζ : A.valuation ζ = 1`. Establish `hp : A.valuation ζ ^ L = 1` using `by rw [← map_pow, hζn, map_one]`. Break down `lt_trichotomy (A.valuation ζ) 1 with hl | he' | hg` into its components or cases. Conclude with `absurd hp (pow_lt_one₀ zero_le' hl hL0).ne`.

Conclude with `he'`. Conclude with `absurd hp (one_lt_pow₀ hg hL0).ne'`. Establish `hfixζ : ∀ τ ∈ ReciprocityTheory.Gal.Ine (F` using `E) A, τ ζ = ζ := by`. Introduce `τ hτ`. Use `GlobalTheory.TameCharDet.eq_of_pow_eq_one_of_val_lt A L hLA ?_ hζn (hτ.2 ζ hvζ.le)` and prove the remaining obligations.

Rewrite using `[← map_pow, hζn, map_one]`. Establish `hfixπ : ∀ τ : Formalism.ConjugateSelfDual.G E Ω, (∀ y : Ω, y ≠ 0 → A.valuation (τ y / y - 1) < 1) → τ π = π`. Introduce `τ hτ`. Establish `h1 : (τ π / π) ^ L = 1`. Rewrite using `[div_pow, ← map_pow, he, AlgEquiv.commutes, div_self]`.

Rewrite using `[← he]`. Conclude with `pow_ne_zero _ hπ`. Establish `h2` using `GlobalTheory.TameCharDet.eq_of_pow_eq_one_of_val_lt A L hLA h1 (one_pow L) (hτ π hπ)`. Rewrite `h2` using `[div_eq_one_iff_eq hπ]`. Then use the resulting hypothesis. Establish `hopenH : ∀ (H : Subgroup (Formalism.ConjugateSelfDual.G E Ω)), IsOpen (H : Set (Formalism.ConjugateSelfDual.G E Ω)) → ∀ U : Set (Formalism.ConjugateSelfDual.G E Ω), (∀ τ ∈ U, ∀ g ∈ H, τ * g ∈ U) → IsOpen U`.

Introduce `H hH U hU`. Rewrite using `[isOpen_iff_mem_nhds]`. Introduce `τ hτ`. Rewrite using `[← map_mul_left_nhds_one τ]`. Conclude with `Filter.mem_map.2 (Filter.mem_of_superset (hH.mem_nhds (one_mem _)) fun g hg => hU τ hτ g hg)`.

Establish `hint : IsIntegral E π` using `Algebra.IsIntegral.isIntegral π`. Use `haveI : FiniteDimensional E (IntermediateField.adjoin E {π}) := IntermediateField.adjoin.finiteDimensional hint`. Establish `hHo : IsOpen ((IntermediateField.adjoin E {π}).fixingSubgroup : Set (Formalism.ConjugateSelfDual.G E Ω))` using `IntermediateField.fixingSubgroup_isOpen _`. Establish `hloc : ∀ c : Ω, IsClosed {τ : Formalism.ConjugateSelfDual.G E Ω | τ π = c}`. Introduce `c`.

Rewrite using `[← isOpen_compl_iff]`. Use `hopenH _ hHo _ fun τ hτ g hg => ?_` and prove the remaining obligations. Simplify using `only [Set.mem_compl_iff, Set.mem_setOf_eq] at hτ ⊢`. Rewrite using `[AlgEquiv.mul_apply, (IntermediateField.mem_fixingSubgroup_iff _ _).1 hg π (IntermediateField.mem_adjoin_simple_self E π)]` and apply the resulting hypothesis. Establish `hfib : ∀ c : M, IsClosed {τ : Formalism.ConjugateSelfDual.G E Ω | φ τ = c}`.

Introduce `c`. Rewrite using `[← isOpen_compl_iff]`. Use `hopenH _ hker _ fun τ hτ g hg => ?_` and prove the remaining obligations. Simplify using `only [Set.mem_compl_iff, Set.mem_setOf_eq] at hτ ⊢`. Rewrite using `[map_mul, (MonoidHom.mem_ker).1 hg, mul_one]` and apply the resulting hypothesis.

Set `T : Set (Formalism.ConjugateSelfDual.G E Ω)` to `⋃ a ∈ Finset.range L, {τ | φ τ = φ γ ^ a ∧ τ π = ζ ^ a * π}`. Establish `hTc : IsClosed T`. Use `isClosed_biUnion_finset fun a _ => ?_` and prove the remaining obligations. Conclude with `(hfib _).inter (hloc _)`. Set `Q : Formalism.ConjugateSelfDual.G E Ω → Prop` to `fun τ => τ ∈ ReciprocityTheory.Gal.Ine (F := E) A ∧ ∃ a : ℕ, φ τ = φ γ ^ a ∧ τ π = ζ ^ a * π`.

Establish `hQ : ∀ τ ∈ Subgroup.closure (insert γ {σ : Formalism.ConjugateSelfDual.G E Ω | ∀ y : Ω, y ≠ 0 → A.valuation (σ y / y - 1) < 1}), Q τ`. Introduce `τ hτ`. Proceed by induction on `hτ using Subgroup.closure_induction with`. Consider the case `mem x hx`. Break down `hx with rfl | hx` into its components or cases.

Conclude with `⟨hγ.1, 1, (pow_one _).symm, by rw [pow_one, hζ, div_mul_cancel₀ _ hπ]⟩`. Conclude with `⟨GlobalTheory.TameGenPowers.wild_mem_Ine hx, 0, by rw [hw x hx, pow_zero], by rw [hfixπ x hx, pow_zero, one_mul]⟩`. Consider the case `one => exact ⟨one_mem _, 0, by rw [map_one, pow_zero], by rw [pow_zero, one_mul]; rfl⟩`. Consider the case `mul x y _ _ ihx ihy`. Take `⟨hxI, a, ha, haπ⟩` from `ihx`.

Take `⟨hyI, b, hb, hbπ⟩` from `ihy`. Use `⟨mul_mem hxI hyI, a + b, by rw [map_mul, ha, hb, pow_add], ?_⟩` and prove the remaining obligations. Rewrite using `[AlgEquiv.mul_apply, hbπ, map_mul, map_pow, hfixζ x hxI, haπ, pow_add]`. Expand and normalize the polynomial expressions, which then agree. Consider the case `inv x _ ihx`.

Take `⟨hxI, a, ha, haπ⟩` from `ihx`. Establish `hiI : x⁻¹ ∈ ReciprocityTheory.Gal.Ine (F` using `E) A := inv_mem hxI`. Establish `hex : a * (L - 1) + a = a * L`. Rewrite using `[← Nat.mul_succ, Nat.succ_eq_add_one, Nat.sub_add_cancel hn]`. Use `⟨hiI, a * (L - 1), ?_, ?_⟩` and prove the remaining obligations.

Rewrite using `[map_inv, ha]`. Use `symm`. Use `eq_inv_of_mul_eq_one_left ?_` and prove the remaining obligations. Rewrite using `[← pow_add, hex, pow_mul', hγL, one_pow]`. Establish `hxx : (x⁻¹ : Formalism.ConjugateSelfDual.G E Ω) (x π) = π`.

Rewrite using `[← AlgEquiv.mul_apply, inv_mul_cancel]`. Both sides reduce to the same expression. Establish `h1 : π = ζ ^ a * (x⁻¹ : Formalism.ConjugateSelfDual.G E Ω) π`. Establish `h2` using `congrArg (fun y => (x⁻¹ : Formalism.ConjugateSelfDual.G E Ω) y) haπ`. Rewrite `h2` using `[hxx, map_mul, map_pow, hfixζ _ hiI]`.

Conclude with `h2`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[hex, pow_mul', hζn, one_pow, one_mul]`. Use `_ = ζ ^ (a * (L - 1)) * (ζ ^ a * (x⁻¹ : Formalism.ConjugateSelfDual.G E Ω) π) := by ring`. Use `_ = ζ ^ (a * (L - 1)) * π := by rw [← h1]`.

Establish `hST : ((Subgroup.closure (insert γ {σ : Formalism.ConjugateSelfDual.G E Ω | ∀ y : Ω, y ≠ 0 → A.valuation (σ y / y - 1) < 1}) : Subgroup (Formalism.ConjugateSelfDual.G E Ω)) : Set (Formalism.ConjugateSelfDual.G E Ω)) ⊆ T`. Introduce `τ hτ`. Take `⟨-, a, ha, haπ⟩` from `hQ τ hτ`. Use `Set.mem_biUnion (x := a % L) (Finset.mem_coe.2 (Finset.mem_range.2 (Nat.mod_lt _ hn))) ?_` and prove the remaining obligations. Conclude with `⟨by rw [ha, hred _ hγL a], by rw [haπ, hred _ hζn a]⟩`.

Establish `hσT : σ ∈ T` using `closure_minimal hST hTc (hγ.2 hσ)`. Simplify using `only [T, Set.mem_iUnion] at hσT`. Take `⟨a, -, h⟩` from `hσT`. Conclude with `⟨a, h⟩`.
-/
theorem exists_pow_joint : ∀ {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
    {M : Type} [CommGroup M] (φ : Formalism.ConjugateSelfDual.G E Ω →* M) (P : HeightOneSpectrum (𝓞 E)) (A : ValuationSubring Ω) (L : ℕ)
    (γ : Formalism.ConjugateSelfDual.G E Ω) (π : Ω) (w : E),
    Formalism.ConjugateSelfDual.IsPlaceOver A P → IsOpen (φ.ker : Set (Formalism.ConjugateSelfDual.G E Ω)) → ((L : ℕ) : 𝓞 E) ∉ P.asIdeal → Formalism.BasicNotions.TameGenAt A γ →
    (∀ τ : Formalism.ConjugateSelfDual.G E Ω, (∀ y : Ω, y ≠ 0 → A.valuation (τ y / y - 1) < 1) → φ τ = 1) → φ γ ^ L = 1 →
    π ≠ 0 → π ^ L = algebraMap E Ω w →
    ∀ σ ∈ ReciprocityTheory.Gal.Ine (F := E) A, ∃ b : ℕ, φ σ = φ γ ^ b ∧ σ π = (γ π / π) ^ b * π := by
  intro E Ω _ _ _ _ _ M _ φ P A L γ π w hA hker hL hγ hw hγL hπ he σ hσ
  have hL0 : L ≠ 0 := by rintro rfl; exact hL (by simp)
  have hn : 0 < L := Nat.pos_of_ne_zero hL0
  have hLA : ¬ A.valuation (L : Ω) < 1 := by
    intro h
    apply hL
    rw [← hA]
    simpa using h
  set ζ := γ π / π with hζ
  have hζn : ζ ^ L = 1 := by
    rw [hζ, div_pow, ← map_pow, he, AlgEquiv.commutes, div_self]
    rw [← he]; exact pow_ne_zero _ hπ
  have hred : ∀ {N : Type} [Monoid N] (x : N), x ^ L = 1 → ∀ a : ℕ, x ^ a = x ^ (a % L) := by
    intro N _ x hx a
    conv_lhs => rw [← Nat.div_add_mod a L, pow_add, pow_mul, hx, one_pow, one_mul]
  have hvζ : A.valuation ζ = 1 := by
    have hp : A.valuation ζ ^ L = 1 := by rw [← map_pow, hζn, map_one]
    rcases lt_trichotomy (A.valuation ζ) 1 with hl | he' | hg
    · exact absurd hp (pow_lt_one₀ zero_le' hl hL0).ne
    · exact he'
    · exact absurd hp (one_lt_pow₀ hg hL0).ne'

  have hfixζ : ∀ τ ∈ ReciprocityTheory.Gal.Ine (F := E) A, τ ζ = ζ := by
    intro τ hτ
    refine GlobalTheory.TameCharDet.eq_of_pow_eq_one_of_val_lt A L hLA ?_ hζn (hτ.2 ζ hvζ.le)
    rw [← map_pow, hζn, map_one]

  have hfixπ : ∀ τ : Formalism.ConjugateSelfDual.G E Ω, (∀ y : Ω, y ≠ 0 → A.valuation (τ y / y - 1) < 1) → τ π = π := by
    intro τ hτ
    have h1 : (τ π / π) ^ L = 1 := by
      rw [div_pow, ← map_pow, he, AlgEquiv.commutes, div_self]
      rw [← he]; exact pow_ne_zero _ hπ
    have h2 := GlobalTheory.TameCharDet.eq_of_pow_eq_one_of_val_lt A L hLA h1 (one_pow L) (hτ π hπ)
    rwa [div_eq_one_iff_eq hπ] at h2

  have hopenH : ∀ (H : Subgroup (Formalism.ConjugateSelfDual.G E Ω)), IsOpen (H : Set (Formalism.ConjugateSelfDual.G E Ω)) →
      ∀ U : Set (Formalism.ConjugateSelfDual.G E Ω), (∀ τ ∈ U, ∀ g ∈ H, τ * g ∈ U) → IsOpen U := by
    intro H hH U hU
    rw [isOpen_iff_mem_nhds]
    intro τ hτ
    rw [← map_mul_left_nhds_one τ]
    exact Filter.mem_map.2 (Filter.mem_of_superset (hH.mem_nhds (one_mem _)) fun g hg => hU τ hτ g hg)
  have hint : IsIntegral E π := Algebra.IsIntegral.isIntegral π
  haveI : FiniteDimensional E (IntermediateField.adjoin E {π}) :=
    IntermediateField.adjoin.finiteDimensional hint
  have hHo : IsOpen ((IntermediateField.adjoin E {π}).fixingSubgroup : Set (Formalism.ConjugateSelfDual.G E Ω)) :=
    IntermediateField.fixingSubgroup_isOpen _
  have hloc : ∀ c : Ω, IsClosed {τ : Formalism.ConjugateSelfDual.G E Ω | τ π = c} := by
    intro c
    rw [← isOpen_compl_iff]
    refine hopenH _ hHo _ fun τ hτ g hg => ?_
    simp only [Set.mem_compl_iff, Set.mem_setOf_eq] at hτ ⊢
    rwa [AlgEquiv.mul_apply, (IntermediateField.mem_fixingSubgroup_iff _ _).1 hg π
      (IntermediateField.mem_adjoin_simple_self E π)]
  have hfib : ∀ c : M, IsClosed {τ : Formalism.ConjugateSelfDual.G E Ω | φ τ = c} := by
    intro c
    rw [← isOpen_compl_iff]
    refine hopenH _ hker _ fun τ hτ g hg => ?_
    simp only [Set.mem_compl_iff, Set.mem_setOf_eq] at hτ ⊢
    rwa [map_mul, (MonoidHom.mem_ker).1 hg, mul_one]
  let T : Set (Formalism.ConjugateSelfDual.G E Ω) := ⋃ a ∈ Finset.range L, {τ | φ τ = φ γ ^ a ∧ τ π = ζ ^ a * π}
  have hTc : IsClosed T := by
    refine isClosed_biUnion_finset fun a _ => ?_
    exact (hfib _).inter (hloc _)
  let Q : Formalism.ConjugateSelfDual.G E Ω → Prop := fun τ =>
    τ ∈ ReciprocityTheory.Gal.Ine (F := E) A ∧ ∃ a : ℕ, φ τ = φ γ ^ a ∧ τ π = ζ ^ a * π
  have hQ : ∀ τ ∈ Subgroup.closure (insert γ
      {σ : Formalism.ConjugateSelfDual.G E Ω | ∀ y : Ω, y ≠ 0 → A.valuation (σ y / y - 1) < 1}), Q τ := by
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
      have hiI : x⁻¹ ∈ ReciprocityTheory.Gal.Ine (F := E) A := inv_mem hxI
      have hex : a * (L - 1) + a = a * L := by
        rw [← Nat.mul_succ, Nat.succ_eq_add_one, Nat.sub_add_cancel hn]
      refine ⟨hiI, a * (L - 1), ?_, ?_⟩
      · rw [map_inv, ha]
        symm
        refine eq_inv_of_mul_eq_one_left ?_
        rw [← pow_add, hex, pow_mul', hγL, one_pow]
      · have hxx : (x⁻¹ : Formalism.ConjugateSelfDual.G E Ω) (x π) = π := by
          rw [← AlgEquiv.mul_apply, inv_mul_cancel]; rfl
        have h1 : π = ζ ^ a * (x⁻¹ : Formalism.ConjugateSelfDual.G E Ω) π := by
          have h2 := congrArg (fun y => (x⁻¹ : Formalism.ConjugateSelfDual.G E Ω) y) haπ
          rw [hxx, map_mul, map_pow, hfixζ _ hiI] at h2
          exact h2
        calc (x⁻¹ : Formalism.ConjugateSelfDual.G E Ω) π = ζ ^ (a * (L - 1) + a) * (x⁻¹ : Formalism.ConjugateSelfDual.G E Ω) π := by
              rw [hex, pow_mul', hζn, one_pow, one_mul]
          _ = ζ ^ (a * (L - 1)) * (ζ ^ a * (x⁻¹ : Formalism.ConjugateSelfDual.G E Ω) π) := by ring
          _ = ζ ^ (a * (L - 1)) * π := by rw [← h1]
  have hST : ((Subgroup.closure (insert γ
      {σ : Formalism.ConjugateSelfDual.G E Ω | ∀ y : Ω, y ≠ 0 → A.valuation (σ y / y - 1) < 1}) : Subgroup (Formalism.ConjugateSelfDual.G E Ω)) :
        Set (Formalism.ConjugateSelfDual.G E Ω)) ⊆ T := by
    intro τ hτ
    obtain ⟨-, a, ha, haπ⟩ := hQ τ hτ
    refine Set.mem_biUnion (x := a % L) (Finset.mem_coe.2 (Finset.mem_range.2 (Nat.mod_lt _ hn))) ?_
    exact ⟨by rw [ha, hred _ hγL a], by rw [haπ, hred _ hζn a]⟩
  have hσT : σ ∈ T := closure_minimal hST hTc (hγ.2 hσ)
  simp only [T, Set.mem_iUnion] at hσT
  obtain ⟨a, -, h⟩ := hσT
  exact ⟨a, h⟩

end GlobalTheory.TameJoint

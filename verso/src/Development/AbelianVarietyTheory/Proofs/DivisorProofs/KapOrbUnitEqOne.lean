import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnifAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OrbitalIntegralUnitIndicatorEventuallyOneClassStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EventuallyExistsIntegralCharpolySplitPlaceStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIntegralElementCharPolyNonsplitStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsConjSameSeparableCharpolySplitPlaceStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EventuallyUnitaryConjOfSameEllipticCharpolyInertStatement
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.UnitOrbCount

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

/- English proof (translation)
Establish `h : ((g⁻¹ * γ * g : UL n w) : GLw n w) = (g : GLw n w)⁻¹ * (γ : GLw n w) * (g : GLw n w)`. Rewrite using `[Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv]`. Establish `h2 : (g⁻¹ * γ * g).1.val = ((g : GLw n w)⁻¹ : GLw n w).val * γ.1.val * (g : GLw n w).val`. Rewrite using `[← Units.val_mul, ← Units.val_mul]`. Conclude with `congrArg Units.val h`.

Rewrite using `[h2, Matrix.coe_units_inv]`. Conclude with `Matrix.charpoly_units_conj' (g : GLw n w) γ.1.val`.
-/
theorem cp_conj {n : ℕ} {w : Pl E} (g γ : UL n w) :
    (g⁻¹ * γ * g).1.val.charpoly = γ.1.val.charpoly := by
  have h : ((g⁻¹ * γ * g : UL n w) : GLw n w) = (g : GLw n w)⁻¹ * (γ : GLw n w) * (g : GLw n w) := by
    rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv]
  have h2 : (g⁻¹ * γ * g).1.val = ((g : GLw n w)⁻¹ : GLw n w).val * γ.1.val * (g : GLw n w).val := by
    rw [← Units.val_mul, ← Units.val_mul]
    exact congrArg Units.val h
  rw [h2, Matrix.coe_units_inv]
  exact Matrix.charpoly_units_conj' (g : GLw n w) γ.1.val

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `h`. Establish `h'` using `Quot.eqvGen_exact h`. Use `clear h`. Proceed by induction on `h' with`.

Consider the case `rel a b hab => obtain ⟨g, hg⟩ := hab; exact ⟨g, by simpa using hg⟩`. Consider the case `refl a => exact ⟨1, by simp⟩`. Consider the case `symm a b _ ih => obtain ⟨g, hg⟩ := ih; exact ⟨g⁻¹, by rw [hg]; group⟩`. Consider the case `trans a b c _ _ ih1 ih2`. Take `⟨g, hg⟩` from `ih1; obtain ⟨k, hk⟩ := ih2; exact ⟨g * k, by rw [hk, hg]; group⟩`.

Introduce and unpack `⟨g, hg⟩`. Conclude with `Quot.sound ⟨g, by simpa using hg⟩`.
-/
theorem mk_eq_iff {G : Type} [Group G] (x y : G) :
    (Quot.mk _ x : TwCl (MonoidHom.id G)) = Quot.mk _ y ↔ ∃ g : G, y = g⁻¹ * x * g := by
  constructor
  · intro h
    have h' := Quot.eqvGen_exact h
    clear h
    induction h' with
    | rel a b hab => obtain ⟨g, hg⟩ := hab; exact ⟨g, by simpa using hg⟩
    | refl a => exact ⟨1, by simp⟩
    | symm a b _ ih => obtain ⟨g, hg⟩ := ih; exact ⟨g⁻¹, by rw [hg]; group⟩
    | trans a b c _ _ ih1 ih2 =>
      obtain ⟨g, hg⟩ := ih1; obtain ⟨k, hk⟩ := ih2; exact ⟨g * k, by rw [hk, hg]; group⟩
  · rintro ⟨g, hg⟩
    exact Quot.sound ⟨g, by simpa using hg⟩

/- English proof (translation)
Use `⟨{u | u = @Classical.epsilon _ ⟨u⟩ fun u' : Pl E => u'.under (𝓞 (maximalRealSubfield E)) = u.under (𝓞 (maximalRealSubfield E))}, fun w => ?_⟩` and prove the remaining obligations. Use `haveI : Nonempty (Pl E) := ⟨w⟩`. Establish `hspec` using `Classical.epsilon_spec (p := fun u' : Pl E => u'.under (𝓞 (maximalRealSubfield E)) = w.under (𝓞 (maximalRealSubfield E))) ⟨w, rfl⟩`. Use `⟨_, ⟨?_, hspec⟩, ?_⟩` and prove the remaining obligations. Use `show _ = _`.

Simplify using `only [hspec]`. Introduce and unpack `u ⟨hu, hu'⟩`. Rewrite `hu` using `[Set.mem_setOf_eq]`. Rewrite using `[hu]`. Simplify using `only [hu']`.
-/
theorem exists_section : ∃ S : Set (Pl E), IsSection S := by
  refine ⟨{u | u = @Classical.epsilon _ ⟨u⟩ fun u' : Pl E => u'.under (𝓞 (maximalRealSubfield E)) =
      u.under (𝓞 (maximalRealSubfield E))}, fun w => ?_⟩
  haveI : Nonempty (Pl E) := ⟨w⟩
  have hspec := Classical.epsilon_spec (p := fun u' : Pl E => u'.under (𝓞 (maximalRealSubfield E)) =
      w.under (𝓞 (maximalRealSubfield E))) ⟨w, rfl⟩
  refine ⟨_, ⟨?_, hspec⟩, ?_⟩
  · show _ = _
    simp only [hspec]
  · rintro u ⟨hu, hu'⟩
    rw [Set.mem_setOf_eq] at hu
    rw [hu]
    simp only [hu']

/- English proof (translation)
Take `⟨m1, -, s1, r1⟩` from `h1`. Take `⟨m2, -, s2, r2⟩` from `h2`. Use `⟨m1.mul m2, by rw [m1.natDegree_mul m2, hn], s1.mul s2 hc, fun τ z hz => ?_⟩` and prove the remaining obligations. Rewrite `hz` using `[Polynomial.map_mul, Polynomial.roots_mul]`. Break down `Multiset.mem_add.1 hz with h | h` into its components or cases.

Conclude with `r1 τ z h`. Conclude with `r2 τ z h`. Rewrite using `[← Polynomial.map_mul]`. Conclude with `((m1.mul m2).map τ).ne_zero`.
-/
theorem ell_mul {n : ℕ} (p₁ p₂ : E[X]) (h1 : p₁ ∈ Ell E p₁.natDegree) (h2 : p₂ ∈ Ell E p₂.natDegree)
    (hc : IsCoprime p₁ p₂) (hn : p₁.natDegree + p₂.natDegree = n) : p₁ * p₂ ∈ Ell E n := by
  obtain ⟨m1, -, s1, r1⟩ := h1
  obtain ⟨m2, -, s2, r2⟩ := h2
  refine ⟨m1.mul m2, by rw [m1.natDegree_mul m2, hn], s1.mul s2 hc, fun τ z hz => ?_⟩
  rw [Polynomial.map_mul, Polynomial.roots_mul] at hz
  · rcases Multiset.mem_add.1 hz with h | h
    · exact r1 τ z h
    · exact r2 τ z h
  · rw [← Polynomial.map_mul]
    exact ((m1.mul m2).map τ).ne_zero

end GlobalTheory.UnitOrbCount

namespace GlobalTheory.UnitOrbCount

/- English proof (translation)
Introduce `E _ _ _ hU n hn p₁ p₂ h1 h2 hc hd`. Establish `hP` using `ell_mul p₁ p₂ h1 h2 hc hd`. Take `⟨S, hS⟩` from `exists_section (E := E)`. Use `filter_upwards [GlobalTheory.T.orbitalIntegral_unitIndicator_eventually_oneClass E hU n hn S hS _ hP, GlobalTheory.T.eventually_exists_integral_charpoly_split_place E hU n hn _ hP, GlobalTheory.T.exists_integral_element_char_poly_nonsplit E hU n hn _ hP, GlobalTheory.T.eventually …`. Establish `hmap : atPl w (p₁ * p₂) = atPl w p₁ * atPl w p₂` using `Polynomial.map_mul _`.

Rewrite `hA`, `hE1`, `hE2`, `hU2` using `[hmap]`. Choose the witnesses or unpack the hypotheses as in `⟨γ₀, hγ₀K, hγ₀P⟩ : ∃ γ : UL n w, γ ∈ KL n w ∧ γ.1.val.charpoly = atPl w p₁ * atPl w p₂ := by`. Distinguish the cases in `hs : IsSplitAt w`. Conclude with `hE1 hs`. Conclude with `hE2 hs`.

Establish `huniq : ∀ γ γ' : UL n w, γ ∈ KL n w → γ' ∈ KL n w → γ.1.val.charpoly = atPl w p₁ * atPl w p₂ → γ'.1.val.charpoly = atPl w p₁ * atPl w p₂ → ∃ g : UL n w, γ' = g⁻¹ * γ * g`. Introduce `γ γ' hk hk' hp hp'`. Distinguish the cases in `hs : IsSplitAt w`. Use `GlobalTheory.T.exists_conj_same_separable_charpoly_split_place E n _ hP w hs γ γ'` as an intermediate fact. Rewrite `this` using `[hmap]`.

Conclude with `this hp hp'`. Conclude with `hU2 hs γ γ' hk hk' hp hp'`. Establish `key : ∀ γ : UL n w, γ.1.val.charpoly = atPl w p₁ * atPl w p₂ → ((∃ g : UL n w, g⁻¹ * γ * g ∈ KL n w) ↔ (Quot.mk _ γ : TwCl (MonoidHom.id (UL n w))) = Quot.mk _ γ₀)`. Introduce `γ hp`. Rewrite using `[mk_eq_iff]`.

Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨g, hg⟩`. Take `⟨k, hk⟩` from `huniq _ γ₀ hg hγ₀K (by rw [cp_conj, hp]) hγ₀P`. Conclude with `⟨g * k, by rw [hk]; group⟩`. Introduce and unpack `⟨g, hg⟩`.

Conclude with `⟨g, hg ▸ hγ₀K⟩`. Unfold `kapOrb clSum`. Simplify using `only [Set.mem_setOf_eq]`. Take `⟨c₀, hc₀⟩ : ∃ c₀ : TwCl (MonoidHom.id (UL n w)), Quot.mk _ γ₀ = c₀` from `⟨_, rfl⟩`. Rewrite `key` using `[hc₀]`.

Rewrite using `[finsum_eq_single _ c₀]`. Establish `hc : (Quot.mk _ c₀.rep : TwCl (MonoidHom.id (UL n w))) = Quot.mk _ γ₀`. Rewrite using `[hc₀]`. Conclude with `Quot.out_eq _`. Take `⟨g, hg⟩` from `(mk_eq_iff _ _).1 hc`.

Establish `hp : c₀.rep.1.val.charpoly = atPl w p₁ * atPl w p₂`. Rewrite using `[← hγ₀P, hg, cp_conj]`. Establish `hex : ∃ g : UL n w, g⁻¹ * c₀.rep * g ∈ KL n w` using `⟨g, hg ▸ hγ₀K⟩`. Take `⟨hT, -, hQ⟩` from `hA _ hp`. Rewrite using `[if_pos hp, hT, if_pos hex, hQ (atPl w p₁) (dvd_mul_right _ _) hex, mul_one]`.

Introduce `c hne`. Establish `hc : (Quot.mk _ c.rep : TwCl (MonoidHom.id (UL n w))) = c` using `Quot.out_eq c`. Distinguish the cases in `hp : c.rep.1.val.charpoly = atPl w p₁ * atPl w p₂`. Take `⟨hT, -, -⟩` from `hA c.rep hp`. Rewrite using `[if_pos hp, hT, if_neg, mul_zero]`.

Introduce `hex`. Apply `hne` to reduce the goal to its premises. Rewrite using `[← hc]`. Conclude with `(key _ hp).1 hex`. Rewrite using `[if_neg hp]`.
-/
theorem kapOrb_unit_eq_one : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ n : ℕ, 1 ≤ n → ∀ p₁ p₂ : E[X], p₁ ∈ Ell E p₁.natDegree → p₂ ∈ Ell E p₂.natDegree → IsCoprime p₁ p₂ → p₁.natDegree + p₂.natDegree = n → ∀ᶠ w in cofinite, kapOrb n w (atPl w p₁) (atPl w p₂) ((KL n w : Set (UL n w)).indicator 1) = 1 := by
  intro E _ _ _ hU n hn p₁ p₂ h1 h2 hc hd
  have hP := ell_mul p₁ p₂ h1 h2 hc hd
  obtain ⟨S, hS⟩ := exists_section (E := E)
  filter_upwards [GlobalTheory.T.orbitalIntegral_unitIndicator_eventually_oneClass E hU n hn S hS _ hP, GlobalTheory.T.eventually_exists_integral_charpoly_split_place E hU n hn _ hP, GlobalTheory.T.exists_integral_element_char_poly_nonsplit E hU n hn _ hP,
    GlobalTheory.T.eventually_unitary_conj_of_same_elliptic_charpoly_inert E hU n hn _ hP] with w hA hE1 hE2 hU2
  have hmap : atPl w (p₁ * p₂) = atPl w p₁ * atPl w p₂ := Polynomial.map_mul _
  rw [hmap] at hA hE1 hE2 hU2
  obtain ⟨γ₀, hγ₀K, hγ₀P⟩ : ∃ γ : UL n w, γ ∈ KL n w ∧ γ.1.val.charpoly = atPl w p₁ * atPl w p₂ := by
    by_cases hs : IsSplitAt w
    · exact hE1 hs
    · exact hE2 hs
  have huniq : ∀ γ γ' : UL n w, γ ∈ KL n w → γ' ∈ KL n w → γ.1.val.charpoly = atPl w p₁ * atPl w p₂ →
      γ'.1.val.charpoly = atPl w p₁ * atPl w p₂ → ∃ g : UL n w, γ' = g⁻¹ * γ * g := by
    intro γ γ' hk hk' hp hp'
    by_cases hs : IsSplitAt w
    · have := GlobalTheory.T.exists_conj_same_separable_charpoly_split_place E n _ hP w hs γ γ'
      rw [hmap] at this
      exact this hp hp'
    · exact hU2 hs γ γ' hk hk' hp hp'
  have key : ∀ γ : UL n w, γ.1.val.charpoly = atPl w p₁ * atPl w p₂ →
      ((∃ g : UL n w, g⁻¹ * γ * g ∈ KL n w) ↔ (Quot.mk _ γ : TwCl (MonoidHom.id (UL n w))) = Quot.mk _ γ₀) := by
    intro γ hp
    rw [mk_eq_iff]
    constructor
    · rintro ⟨g, hg⟩
      obtain ⟨k, hk⟩ := huniq _ γ₀ hg hγ₀K (by rw [cp_conj, hp]) hγ₀P
      exact ⟨g * k, by rw [hk]; group⟩
    · rintro ⟨g, hg⟩
      exact ⟨g, hg ▸ hγ₀K⟩
  unfold kapOrb clSum
  simp only [Set.mem_setOf_eq]
  obtain ⟨c₀, hc₀⟩ : ∃ c₀ : TwCl (MonoidHom.id (UL n w)), Quot.mk _ γ₀ = c₀ := ⟨_, rfl⟩
  rw [hc₀] at key
  rw [finsum_eq_single _ c₀]
  · have hc : (Quot.mk _ c₀.rep : TwCl (MonoidHom.id (UL n w))) = Quot.mk _ γ₀ := by
      rw [hc₀]; exact Quot.out_eq _
    obtain ⟨g, hg⟩ := (mk_eq_iff _ _).1 hc
    have hp : c₀.rep.1.val.charpoly = atPl w p₁ * atPl w p₂ := by
      rw [← hγ₀P, hg, cp_conj]
    have hex : ∃ g : UL n w, g⁻¹ * c₀.rep * g ∈ KL n w :=
      ⟨g, hg ▸ hγ₀K⟩
    obtain ⟨hT, -, hQ⟩ := hA _ hp
    rw [if_pos hp, hT, if_pos hex, hQ (atPl w p₁) (dvd_mul_right _ _) hex, mul_one]
  · intro c hne
    have hc : (Quot.mk _ c.rep : TwCl (MonoidHom.id (UL n w))) = c := Quot.out_eq c
    by_cases hp : c.rep.1.val.charpoly = atPl w p₁ * atPl w p₂
    · obtain ⟨hT, -, -⟩ := hA c.rep hp
      rw [if_pos hp, hT, if_neg, mul_zero]
      intro hex
      apply hne
      rw [← hc]
      exact (key _ hp).1 hex
    · rw [if_neg hp]

end GlobalTheory.UnitOrbCount

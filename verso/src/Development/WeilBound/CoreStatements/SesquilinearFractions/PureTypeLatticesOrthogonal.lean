import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsTransition
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.PrincipalRootReZeroImSq
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Matrix GlobalTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl
open scoped ComplexOrder

namespace PositivityTheory.Xgf

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

/- English proof (translation)
Establish `h` using `D.alt (x + y)`. Simplify using `only [map_add, LinearMap.add_apply, D.alt x, D.alt y, zero_add, add_zero] at h`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem symplectic_form_skew (D : Datum H) (x y : D.La) : D.EF x y = -D.EF y x := by
  have h := D.alt (x + y)
  simp only [map_add, LinearMap.add_apply, D.alt x, D.alt y, zero_add, add_zero] at h
  linarith

/- English proof (translation)
Introduce `h`. Establish `h0 : H.rt0 = 0` using `by linear_combination h / 2`. Establish `hs` using `H.sqrt_neg_disc_sq`. Rewrite `hs` using `[h0]`. Establish `hd : (H.d : ℂ) ≠ 0` using `by exact_mod_cast H.d_prime.ne_zero`.

Apply `hd` to reduce the goal to its premises. Take the linear combination `hs`.
-/
theorem Host_rt0_ne_neg : H.rt0 ≠ -H.rt0 := by
  intro h
  have h0 : H.rt0 = 0 := by linear_combination h / 2
  have hs := H.sqrt_neg_disc_sq
  rw [h0] at hs
  have hd : (H.d : ℂ) ≠ 0 := by exact_mod_cast H.d_prime.ne_zero
  apply hd
  linear_combination hs

/- English proof (translation)
Introduce `E _ _ _ H D g ty P hP a b ha hb`. Simplify using `only [sgnRt, if_true, Bool.false_eq_true, if_false] at ha hb`. Prove the components needed by the constructor for the conclusion. Unfold `sesq`. Use `Finset.sum_eq_zero fun k _ => ?_` and prove the remaining obligations.

Rewrite using `[GlobalTheory.CM.FamCompare.orth_of_pure hP ((PureType.lat hP H.rt0).smul_mem _ ha) hb]`. Simplify using the standard rewrite rules. Unfold `sesq`. Use `Finset.sum_eq_zero fun k _ => ?_` and prove the remaining obligations. Rewrite using `[symplectic_form_skew D, GlobalTheory.CM.FamCompare.orth_of_pure hP ha ((PureType.lat hP (-H.rt0)).smul_mem _ hb)]`.

Simplify using the standard rewrite rules.
-/
theorem pure_type_lattices_orthogonal : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (P : D.La →+ (Fin g → ℂ)) (hP : IsPeriod D ty P) (a b : D.La), a ∈ PureType.lat hP (sgnRt H true) → b ∈ PureType.lat hP (sgnRt H false) → sesq D a b = 0 ∧ sesq D b a = 0 := by
  intro E _ _ _ H D g ty P hP a b ha hb
  simp only [sgnRt, if_true, Bool.false_eq_true, if_false] at ha hb
  constructor
  · unfold sesq
    refine Finset.sum_eq_zero fun k _ => ?_
    rw [GlobalTheory.CM.FamCompare.orth_of_pure hP ((PureType.lat hP H.rt0).smul_mem _ ha) hb]
    simp
  · unfold sesq
    refine Finset.sum_eq_zero fun k _ => ?_
    rw [symplectic_form_skew D, GlobalTheory.CM.FamCompare.orth_of_pure hP ha ((PureType.lat hP (-H.rt0)).smul_mem _ hb)]
    simp

/- English proof (translation)
Introduce `E _ _ _ H D g ty P hP p q x n hx hn`. Establish `hsplit : ∀ y : D.La, ∃ a ∈ Submodule.span (𝓞 E) (Set.range (x ∘ Sum.inl)), ∃ b ∈ Submodule.span (𝓞 E) (Set.range (x ∘ Sum.inr)), n • y = a + b`. Introduce `y`. Establish `h` using `hn y`. Establish `e : Set.range x = Set.range (x ∘ Sum.inl) ∪ Set.range (x ∘ Sum.inr)`.

Use extensionality with `z`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨(i | j), rfl⟩`. Conclude with `Or.inl ⟨i, rfl⟩`. Conclude with `Or.inr ⟨j, rfl⟩`.

Introduce and unpack `(⟨i, rfl⟩ | ⟨j, rfl⟩)`. Conclude with `⟨_, rfl⟩`. Conclude with `⟨_, rfl⟩`. Rewrite `h` using `[e, Submodule.span_union, Submodule.mem_sup]`. Take `⟨a, ha, b, hb, hab⟩` from `h`.

Conclude with `⟨a, ha, b, hb, hab.symm⟩`. Establish `hlatL : Submodule.span (𝓞 E) (Set.range (x ∘ Sum.inl)) ≤ PureType.lat hP (sgnRt H true)` using `Submodule.span_le.2 (by rintro _ ⟨i, rfl⟩; exact hx.1 i)`. Establish `hlatR : Submodule.span (𝓞 E) (Set.range (x ∘ Sum.inr)) ≤ PureType.lat hP (sgnRt H false)` using `Submodule.span_le.2 (by rintro _ ⟨j, rfl⟩; exact hx.2 j)`. Establish `hboth : ∀ z, z ∈ PureType.lat hP (sgnRt H true) → z ∈ PureType.lat hP (sgnRt H false) → z = 0`. Introduce `z h1 h2`.

Apply `hP.2.1` to reduce the goal to its premises. Rewrite using `[map_zero]`. Use function extensionality and compare the values at `j`. Distinguish the cases in `hj : ty j (H.rt : E) = H.rt0`. Establish `: ty j (H.rt : E) ≠ -H.rt0` using `by rw [hj]; exact Host_rt0_ne_neg`.

Conclude with `h2 j (by simpa [sgnRt] using this)`. Conclude with `h1 j (by simpa [sgnRt] using hj)`. Use `⟨fun y => ?_, fun y hy => ?_, fun y hy => ?_⟩` and prove the remaining obligations. Take `⟨a, ha, b, hb, e⟩` from `hsplit y`. Conclude with `⟨a, hlatL ha, b, hlatR hb, e⟩`.

Take `⟨a, ha, b, hb, e⟩` from `hsplit y`. Establish `hb0 : b = 0` using `hboth b (by`. Establish `: b = n • y - a` using `by rw [e]; abel`. Rewrite using `[this]`. Conclude with `Submodule.sub_mem _ (Submodule.smul_of_tower_mem _ _ hy) (hlatL ha)) (hlatR hb)`.

Rewrite using `[e, hb0, add_zero]`. Conclude with `ha`. Take `⟨a, ha, b, hb, e⟩` from `hsplit y`. Establish `ha0 : a = 0` using `hboth a (hlatL ha) (by`. Establish `: a = n • y - b` using `by rw [e]; abel`.

Rewrite using `[this]`. Conclude with `Submodule.sub_mem _ (Submodule.smul_of_tower_mem _ _ hy) (hlatR hb))`. Rewrite using `[e, ha0, zero_add]`. Conclude with `hb`.
-/
theorem pure_family_decomposition : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (P : D.La →+ (Fin g → ℂ)) (hP : IsPeriod D ty P) (p q : ℕ) (x : Fin p ⊕ Fin q → D.La) (n : ℕ), IsPure hP x → (∀ y : D.La, n • y ∈ Submodule.span (𝓞 E) (Set.range x)) → (∀ y : D.La, ∃ a ∈ PureType.lat hP (sgnRt H true), ∃ b ∈ PureType.lat hP (sgnRt H false), n • y = a + b) ∧ (∀ y ∈ PureType.lat hP (sgnRt H true), n • y ∈ Submodule.span (𝓞 E) (Set.range (x ∘ Sum.inl))) ∧ ∀ y ∈ PureType.lat hP (sgnRt H false), n • y ∈ Submodule.span (𝓞 E) (Set.range (x ∘ Sum.inr)) := by
  intro E _ _ _ H D g ty P hP p q x n hx hn

  have hsplit : ∀ y : D.La, ∃ a ∈ Submodule.span (𝓞 E) (Set.range (x ∘ Sum.inl)),
      ∃ b ∈ Submodule.span (𝓞 E) (Set.range (x ∘ Sum.inr)), n • y = a + b := by
    intro y
    have h := hn y
    have e : Set.range x = Set.range (x ∘ Sum.inl) ∪ Set.range (x ∘ Sum.inr) := by
      ext z; constructor
      · rintro ⟨(i | j), rfl⟩
        · exact Or.inl ⟨i, rfl⟩
        · exact Or.inr ⟨j, rfl⟩
      · rintro (⟨i, rfl⟩ | ⟨j, rfl⟩)
        · exact ⟨_, rfl⟩
        · exact ⟨_, rfl⟩
    rw [e, Submodule.span_union, Submodule.mem_sup] at h
    obtain ⟨a, ha, b, hb, hab⟩ := h
    exact ⟨a, ha, b, hb, hab.symm⟩
  have hlatL : Submodule.span (𝓞 E) (Set.range (x ∘ Sum.inl)) ≤ PureType.lat hP (sgnRt H true) :=
    Submodule.span_le.2 (by rintro _ ⟨i, rfl⟩; exact hx.1 i)
  have hlatR : Submodule.span (𝓞 E) (Set.range (x ∘ Sum.inr)) ≤ PureType.lat hP (sgnRt H false) :=
    Submodule.span_le.2 (by rintro _ ⟨j, rfl⟩; exact hx.2 j)
  have hboth : ∀ z, z ∈ PureType.lat hP (sgnRt H true) → z ∈ PureType.lat hP (sgnRt H false) → z = 0 := by
    intro z h1 h2
    apply hP.2.1
    rw [map_zero]
    funext j
    by_cases hj : ty j (H.rt : E) = H.rt0
    · have : ty j (H.rt : E) ≠ -H.rt0 := by rw [hj]; exact Host_rt0_ne_neg
      exact h2 j (by simpa [sgnRt] using this)
    · exact h1 j (by simpa [sgnRt] using hj)
  refine ⟨fun y => ?_, fun y hy => ?_, fun y hy => ?_⟩
  · obtain ⟨a, ha, b, hb, e⟩ := hsplit y
    exact ⟨a, hlatL ha, b, hlatR hb, e⟩
  · obtain ⟨a, ha, b, hb, e⟩ := hsplit y
    have hb0 : b = 0 := hboth b (by
      have : b = n • y - a := by rw [e]; abel
      rw [this]
      exact Submodule.sub_mem _ (Submodule.smul_of_tower_mem _ _ hy) (hlatL ha)) (hlatR hb)
    rw [e, hb0, add_zero]; exact ha
  · obtain ⟨a, ha, b, hb, e⟩ := hsplit y
    have ha0 : a = 0 := hboth a (hlatL ha) (by
      have : a = n • y - b := by rw [e]; abel
      rw [this]
      exact Submodule.sub_mem _ (Submodule.smul_of_tower_mem _ _ hy) (hlatR hb))
    rw [e, ha0, zero_add]; exact hb

end PositivityTheory.Xgf

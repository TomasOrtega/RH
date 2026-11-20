import Mathlib
import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.IsHermForm
import Formalism.LocalToGlobal.ProjectiveLattices.ThClass

open NumberField IsDedekindDomain GlobalTheory.AdLat GlobalTheory.UnRep ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open scoped TensorProduct Matrix

noncomputable section

namespace GlobalTheory.UnRep.StdInhab

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

/- English proof (translation)
Apply `Subtype.ext` to reduce the goal to its premises. Use `show ((H.bar (H.bar a) : 𝓞 E) : E) = (a : E)`. Rewrite using `[H.bar_eq, H.bar_eq, IsCMField.complexConj_apply_apply]`.
-/
theorem bar_bar (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (a : 𝓞 E) : H.bar (H.bar a) = a := by
  apply Subtype.ext
  show ((H.bar (H.bar a) : 𝓞 E) : E) = (a : E)
  rw [H.bar_eq, H.bar_eq, IsCMField.complexConj_apply_apply]

/- English proof (translation)
Establish `h1 : H.bar H.rt ^ 2 = H.rt ^ 2`. Rewrite using `[← map_pow, H.rt_sq, map_neg, map_natCast]`. Break down `sq_eq_sq_iff_eq_or_eq_neg.1 h1 with e | e` into its components or cases. It suffices to derive a contradiction. Establish `e' : IsCMField.complexConj E (H.rt : E) = H.rt` using `by rw [← H.bar_eq, e]`.

Take `⟨φ⟩ : Nonempty (E →+* ℂ)` from `inferInstance`. Establish `c` using `IsCMField.complexEmbedding_complexConj E φ (H.rt : E)`. Rewrite `c` using `[e']`. Establish `r : φ (H.rt : E) ^ 2 = -(H.d : ℂ)`. Use `congrArg (fun z : 𝓞 E => φ (z : E)) H.rt_sq` as an intermediate fact.

Simplify using `using this`. Take `⟨x, hx⟩` from `Complex.conj_eq_iff_real.1 c.symm`. Rewrite `r` using `[hx]`. Establish `r' : x ^ 2 = -(H.d : ℝ)` using `by exact_mod_cast r`. Establish `: (0 : ℝ) < H.d` using `by exact_mod_cast H.d_prime.pos`.

Use polynomial arithmetic with `[sq_nonneg x]`. Conclude with `e`.
-/
theorem bar_rt (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) : H.bar H.rt = -H.rt := by
  have h1 : H.bar H.rt ^ 2 = H.rt ^ 2 := by
    rw [← map_pow, H.rt_sq, map_neg, map_natCast]
  rcases sq_eq_sq_iff_eq_or_eq_neg.1 h1 with e | e
  · exfalso
    have e' : IsCMField.complexConj E (H.rt : E) = H.rt := by rw [← H.bar_eq, e]
    obtain ⟨φ⟩ : Nonempty (E →+* ℂ) := inferInstance
    have c := IsCMField.complexEmbedding_complexConj E φ (H.rt : E)
    rw [e'] at c
    have r : φ (H.rt : E) ^ 2 = -(H.d : ℂ) := by
      have := congrArg (fun z : 𝓞 E => φ (z : E)) H.rt_sq
      simpa using this
    obtain ⟨x, hx⟩ := Complex.conj_eq_iff_real.1 c.symm
    rw [hx] at r
    have r' : x ^ 2 = -(H.d : ℝ) := by exact_mod_cast r
    have : (0 : ℝ) < H.d := by exact_mod_cast H.d_prime.pos
    nlinarith [sq_nonneg x]
  · exact e

/- English proof (translation)
Establish `h2 : 2 * H.bar H.w0 = 1 + H.bar H.rt`. Use `congrArg H.bar H.two_weight_eq_one_add_root` as an intermediate fact. Simplify `this` using `[map_ofNat]`. Establish `h4 : (2 : 𝓞 E) ≠ 0` using `by norm_num`. Apply `mul_left_cancel₀ h4` to reduce the goal to its premises.

Rewrite using `[h2, bar_rt]`. Take the linear combination `H.two_weight_eq_one_add_root`.
-/
theorem bar_w (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) : H.bar H.w0 = 1 - H.w0 := by
  have h2 : 2 * H.bar H.w0 = 1 + H.bar H.rt := by
    have := congrArg H.bar H.two_weight_eq_one_add_root
    simpa [map_ofNat] using this
  have h4 : (2 : 𝓞 E) ≠ 0 := by norm_num
  apply mul_left_cancel₀ h4
  rw [h2, bar_rt]
  linear_combination H.two_weight_eq_one_add_root

/- English proof (translation)
Take `⟨m, hm⟩ : ∃ m, H.d + 1 = 4 * m` from `⟨(H.d + 1) / 4, by have := H.d_mod; omega⟩`. Use `⟨m, by have := H.d_mod; omega, ?_⟩` and prove the remaining obligations. Establish `hm' : (H.d : 𝓞 E) + 1 = 4 * m` using `by exact_mod_cast hm`. Rewrite using `[bar_w]`. Establish `h4 : (4 : 𝓞 E) ≠ 0` using `by norm_num`.

Apply `mul_left_cancel₀ h4` to reduce the goal to its premises. Take the linear combination `(-(2 * H.w0 + H.rt - 1)) * H.two_weight_eq_one_add_root - H.rt_sq + hm'`.
-/
theorem w_norm (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) :
    ∃ m : ℕ, 2 ≤ m ∧ H.w0 * H.bar H.w0 = (m : 𝓞 E) := by
  obtain ⟨m, hm⟩ : ∃ m, H.d + 1 = 4 * m := ⟨(H.d + 1) / 4, by have := H.d_mod; omega⟩
  refine ⟨m, by have := H.d_mod; omega, ?_⟩
  have hm' : (H.d : 𝓞 E) + 1 = 4 * m := by exact_mod_cast hm
  rw [bar_w]
  have h4 : (4 : 𝓞 E) ≠ 0 := by norm_num
  apply mul_left_cancel₀ h4
  linear_combination (-(2 * H.w0 + H.rt - 1)) * H.two_weight_eq_one_add_root - H.rt_sq + hm'

/- English proof (translation)
Introduce `hu`. Take `⟨m, hm, e⟩` from `w_norm H`. Establish `h1 : IsUnit (m : 𝓞 E)` using `e ▸ hu.mul (hu.map H.bar)`. Establish `h2 : IsUnit (Algebra.norm ℤ (algebraMap ℤ (𝓞 E) (m : ℤ)))`. Apply `IsUnit.map` to reduce the goal to its premises.

Simplify using `using h1`. Rewrite `h2` using `[Algebra.norm_algebraMap]`. Establish `h3 : Module.finrank ℤ (𝓞 E) ≠ 0` using `Module.finrank_pos.ne'`. Rewrite `h2` using `[isUnit_pow_iff h3, Int.isUnit_iff]`. Use linear arithmetic over natural numbers and integers.
-/
theorem w_not_unit (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) : ¬ IsUnit H.w0 := by
  intro hu
  obtain ⟨m, hm, e⟩ := w_norm H
  have h1 : IsUnit (m : 𝓞 E) := e ▸ hu.mul (hu.map H.bar)
  have h2 : IsUnit (Algebra.norm ℤ (algebraMap ℤ (𝓞 E) (m : ℤ))) := by
    apply IsUnit.map
    simpa using h1
  rw [Algebra.norm_algebraMap] at h2
  have h3 : Module.finrank ℤ (𝓞 E) ≠ 0 := Module.finrank_pos.ne'
  rw [isUnit_pow_iff h3, Int.isUnit_iff] at h2
  omega

/- English proof (translation)
Take `⟨m, hm, e⟩` from `w_norm H`. Introduce `h`. Rewrite `e` using `[h, zero_mul]`. Establish `: m = 0` using `by exact_mod_cast e.symm`. Use linear arithmetic over natural numbers and integers.
-/
theorem w_ne_zero (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) : H.w0 ≠ 0 := by
  obtain ⟨m, hm, e⟩ := w_norm H
  intro h
  rw [h, zero_mul] at e
  have : m = 0 := by exact_mod_cast e.symm
  omega

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨a, ha, b, hb, hbP⟩ e`. Apply `hbP` to reduce the goal to its premises. Establish `: b = H.bar a`. Apply `Subtype.ext` to reduce the goal to its premises.

Use `show (b : E) = ((H.bar a : 𝓞 E) : E)`. Rewrite using `[hb, H.bar_eq]`. Rewrite using `[this, ← e]`. Conclude with `Ideal.mem_map_of_mem (H.bar : 𝓞 E →+* 𝓞 E) ha`. Introduce `hne`.

Assume the negation of the conclusion as `hm`. Establish `key : ∀ a ∈ P, H.bar a ∈ P`. Introduce `a ha`. Assume the negation of the conclusion as `hb`. Conclude with `hm ⟨a, ha, H.bar a, H.bar_eq a, hb⟩`.

Apply `hne` to reduce the goal to its premises. Apply `le_antisymm` to reduce the goal to its premises. Rewrite using `[Ideal.map_le_iff_le_comap]`. Introduce `a ha`. Conclude with `key a ha`.

Introduce `a ha`. Rewrite using `[← bar_bar H a]`. Conclude with `Ideal.mem_map_of_mem (H.bar : 𝓞 E →+* 𝓞 E) (key a ha)`.
-/
theorem moved_iff (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (P : Ideal (𝓞 E)) :
    Moved (IsCMField.complexConj E) P ↔ P.map (H.bar : 𝓞 E →+* 𝓞 E) ≠ P := by
  constructor
  · rintro ⟨a, ha, b, hb, hbP⟩ e
    apply hbP
    have : b = H.bar a := by
      apply Subtype.ext
      show (b : E) = ((H.bar a : 𝓞 E) : E)
      rw [hb, H.bar_eq]
    rw [this, ← e]
    exact Ideal.mem_map_of_mem (H.bar : 𝓞 E →+* 𝓞 E) ha
  · intro hne
    by_contra hm
    have key : ∀ a ∈ P, H.bar a ∈ P := by
      intro a ha
      by_contra hb
      exact hm ⟨a, ha, H.bar a, H.bar_eq a, hb⟩
    apply hne
    apply le_antisymm
    · rw [Ideal.map_le_iff_le_comap]
      intro a ha
      exact key a ha
    · intro a ha
      rw [← bar_bar H a]
      exact Ideal.mem_map_of_mem (H.bar : 𝓞 E →+* 𝓞 E) (key a ha)

/- English proof (translation)
Use `⟨w_ne_zero H, fun P hP hw => ?_⟩` and prove the remaining obligations. Establish `h1 : (1 : 𝓞 E) ∉ P` using `(Ideal.ne_top_iff_one P).1 hP.ne_top`. Use `⟨⟨H.w0, hw, H.bar H.w0, H.bar_eq _, fun hb => h1 ?_⟩, by simpa using h1⟩` and prove the remaining obligations. Use `P.add_mem hw hb` as an intermediate fact. Rewrite `this` using `[bar_w, add_sub_cancel]`. Then use the resulting hypothesis.
-/
theorem splitOff_w (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) : SplitOff (IsCMField.complexConj E) 1 H.w0 := by
  refine ⟨w_ne_zero H, fun P hP hw => ?_⟩
  have h1 : (1 : 𝓞 E) ∉ P := (Ideal.ne_top_iff_one P).1 hP.ne_top
  refine ⟨⟨H.w0, hw, H.bar H.w0, H.bar_eq _, fun hb => h1 ?_⟩, by simpa using h1⟩
  have := P.add_mem hw hb
  rwa [bar_w, add_sub_cancel] at this

omit [IsCMField E] in
/- English proof (translation)
Introduce `j _`. Distinguish the cases in `h : j = i`. Substitute `h` using the available equality. Conclude with `Submodule.mem_one.2 ⟨1, by simp⟩`. Conclude with `Submodule.mem_one.2 ⟨0, by simp [h]⟩`.
-/
theorem single_mem (n : ℕ) (i : Fin n) : (Pi.single i (1 : E) : Fin n → E) ∈ stdLat E n := by
  intro j _
  by_cases h : j = i
  · subst h
    exact Submodule.mem_one.2 ⟨1, by simp⟩
  · exact Submodule.mem_one.2 ⟨0, by simp [h]⟩

omit [IsCMField E] in
/- English proof (translation)
Apply `le_antisymm` to reduce the goal to its premises. Introduce `x hx`. Establish `hx' : ∀ i, ∃ r : 𝓞 E, algebraMap (𝓞 E) E r = x i` using `fun i => Submodule.mem_one.1 (hx i trivial)`. Use `choose r hr using hx'`. Establish `: x = ∑ i, r i • (Pi.single i (1 : E) : Fin n → E)`.

Use function extensionality and compare the values at `j`. Simplify using `[Finset.sum_apply, Pi.single_apply, Algebra.smul_def, hr]`. Rewrite using `[this]`. Conclude with `Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)`. Rewrite using `[Submodule.span_le]`.

Introduce and unpack `_ ⟨i, rfl⟩`. Conclude with `single_mem n i`.
-/
theorem stdLat_eq_span (n : ℕ) :
    stdLat E n = Submodule.span (𝓞 E) (Set.range fun i : Fin n => (Pi.single i (1 : E) : Fin n → E)) := by
  apply le_antisymm
  · intro x hx
    have hx' : ∀ i, ∃ r : 𝓞 E, algebraMap (𝓞 E) E r = x i := fun i => Submodule.mem_one.1 (hx i trivial)
    choose r hr using hx'
    have : x = ∑ i, r i • (Pi.single i (1 : E) : Fin n → E) := by
      funext j
      simp [Finset.sum_apply, Pi.single_apply, Algebra.smul_def, hr]
    rw [this]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  · rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    exact single_mem n i

/- English proof (translation)
Unfold `hermE`. Use `Finset.sum_congr rfl fun a _ => ?_` and prove the remaining obligations. Simplify using `[Matrix.one_apply]`.
-/
theorem hermE_one {F : Type} [Field F] [Algebra F E] (c : E ≃ₐ[F] E) {n : ℕ} (x y : Fin n → E) :
    hermE c 1 x y = ∑ a, x a * c (y a) := by
  unfold hermE
  refine Finset.sum_congr rfl fun a _ => ?_
  simp [Matrix.one_apply]

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `h i j`. Use `h (Pi.single j 1) (Pi.single i 1)` as an intermediate fact. Rewrite `this` using `[hermE_one, hermE_one]`. Simplify using `only [Matrix.mulVec_single_one, Matrix.col_apply] at this`.

Simplify using `only [mul_comm (c _)]`. Rewrite using `[this]`. Distinguish the cases in `e : i = j`. Substitute `e` using the available equality. Simplify using `[Pi.single_apply]`.

Simplify using `[Pi.single_apply, e, Ne.symm e]`. Introduce `h x y`. Rewrite using `[hermE_one, hermE_one]`. Simplify using `only [Matrix.mulVec, dotProduct, map_sum, map_mul, Finset.sum_mul, Finset.mul_sum]`. Combine the equalities or inequalities in the displayed calculation.

Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Rewrite using `[Finset.sum_mul]`.

Conclude with `Finset.sum_congr rfl fun a _ => by ring`. Use `_ = _ := by simp [h]`.
-/
theorem isUnE_one_iff {F : Type} [Field F] [Algebra F E] (c : E ≃ₐ[F] E) {n : ℕ} (γ : Matrix (Fin n) (Fin n) E) :
    IsUnE c 1 γ ↔ ∀ i j, ∑ b, c (γ b i) * γ b j = if i = j then 1 else 0 := by
  constructor
  · intro h i j
    have := h (Pi.single j 1) (Pi.single i 1)
    rw [hermE_one, hermE_one] at this
    simp only [Matrix.mulVec_single_one, Matrix.col_apply] at this
    simp only [mul_comm (c _)]
    rw [this]
    by_cases e : i = j
    · subst e; simp [Pi.single_apply]
    · simp [Pi.single_apply, e, Ne.symm e]
  · intro h x y
    rw [hermE_one, hermE_one]
    simp only [Matrix.mulVec, dotProduct, map_sum, map_mul, Finset.sum_mul, Finset.mul_sum]
    calc ∑ a, ∑ i, ∑ j, γ a j * x j * (c (γ a i) * c (y i))
        = ∑ i, ∑ j, (∑ a, c (γ a i) * γ a j) * (x j * c (y i)) := by
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [Finset.sum_mul]
          exact Finset.sum_congr rfl fun a _ => by ring
      _ = _ := by simp [h]

/- English proof (translation)
Introduce `E _ _ _ H n`. Use `⟨⟨IsCMField.complexConj_apply_apply E, IsCMField.complexConj_ne_one E, fun a b => ?_, by simp⟩, Algebra.IsQuadraticExtension.finrank_eq_two _ _, ?_, ?_, splitOff_w H, w_not_unit H, fun P _ => moved_iff H P, isUnE_one_iff _⟩` and prove the remaining obligations. Distinguish the cases in `e : a = b`. Substitute `e` using the available equality. Simplify using the standard rewrite rules.

Simplify using `[Matrix.one_apply, e, Ne.symm e]`. Rewrite using `[stdLat_eq_span]`. Conclude with `Submodule.fg_span (Set.finite_range _)`. Rewrite using `[eq_top_iff, ← (Pi.basisFun E (Fin n)).span_eq]`. Apply `Submodule.span_mono` to reduce the goal to its premises.

Introduce and unpack `_ ⟨i, rfl⟩`. Simplify using `using single_mem (E := E) n i`.
-/
theorem main : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (n : ℕ), IsHermForm (IsCMField.complexConj E) (1 : Matrix (Fin n) (Fin n) E) ∧ Module.finrank (maximalRealSubfield E) E = 2 ∧ (stdLat E n).FG ∧ Submodule.span E (stdLat E n : Set (Fin n → E)) = ⊤ ∧ SplitOff (IsCMField.complexConj E) 1 H.w0 ∧ ¬ IsUnit H.w0 ∧ (∀ P : Ideal (𝓞 E), P.IsPrime → (Moved (IsCMField.complexConj E) P ↔ P.map (H.bar : 𝓞 E →+* 𝓞 E) ≠ P)) ∧ ∀ γ : Matrix (Fin n) (Fin n) E, IsUnE (IsCMField.complexConj E) 1 γ ↔ ∀ i j, ∑ b, (IsCMField.complexConj E) (γ b i) * γ b j = if i = j then 1 else 0 := by
  intro E _ _ _ H n
  refine ⟨⟨IsCMField.complexConj_apply_apply E, IsCMField.complexConj_ne_one E, fun a b => ?_, by simp⟩,
    Algebra.IsQuadraticExtension.finrank_eq_two _ _, ?_, ?_, splitOff_w H, w_not_unit H,
    fun P _ => moved_iff H P, isUnE_one_iff _⟩
  · by_cases e : a = b
    · subst e; simp
    · simp [Matrix.one_apply, e, Ne.symm e]
  · rw [stdLat_eq_span]
    exact Submodule.fg_span (Set.finite_range _)
  · rw [eq_top_iff, ← (Pi.basisFun E (Fin n)).span_eq]
    apply Submodule.span_mono
    rintro _ ⟨i, rfl⟩
    simpa using single_mem (E := E) n i

end GlobalTheory.UnRep.StdInhab

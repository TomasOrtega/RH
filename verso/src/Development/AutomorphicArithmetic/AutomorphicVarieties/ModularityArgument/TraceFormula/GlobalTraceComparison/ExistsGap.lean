import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.StableBlock
import Mathlib.Analysis.CStarAlgebra.GelfandDuality

namespace UpperTheory.V.Z.Tf.GlobalTraceComparison

section Core

variable {X : Type} [TopologicalSpace X] [CompactSpace X] {B : Type} [CommRing B] [StarRing B]
  [Algebra ℂ B] [StarModule ℂ B] (Φ : B →⋆ₐ[ℂ] C(X, ℂ)) (A : StarSubalgebra ℂ B)
  (p : A →⋆ₐ[ℂ] ℂ)

private def Nn (c : A) : Prop :=
  p c = 0 ∧ ∀ χ, (Φ (c : B) χ).im = 0 ∧ 0 ≤ (Φ (c : B) χ).re

/- English proof (translation)
Use `⟨by simp [hc.1, hd.1], fun χ => ?_⟩` and prove the remaining obligations. Establish `h₁` using `hc.2 χ`. Establish `h₂` using `hd.2 χ`. Establish `e : Φ ((c + d : A) : B) χ = Φ (c : B) χ + Φ (d : B) χ` using `by simp`. Rewrite using `[e, Complex.add_im, Complex.add_re]`.

Conclude with `⟨by rw [h₁.1, h₂.1, add_zero], add_nonneg h₁.2 h₂.2⟩`.
-/
private lemma nn_add {c d : A} (hc : Nn Φ A p c) (hd : Nn Φ A p d) : Nn Φ A p (c + d) := by
  refine ⟨by simp [hc.1, hd.1], fun χ => ?_⟩
  have h₁ := hc.2 χ
  have h₂ := hd.2 χ
  have e : Φ ((c + d : A) : B) χ = Φ (c : B) χ + Φ (d : B) χ := by simp
  rw [e, Complex.add_im, Complex.add_re]
  exact ⟨by rw [h₁.1, h₂.1, add_zero], add_nonneg h₁.2 h₂.2⟩

/- English proof (translation)
Establish `e : Φ ((star b * b : A) : B) χ = star (Φ (b : B) χ) * Φ (b : B) χ`. Simplify using `[map_mul, map_star]`. Rewrite using `[e]`. Simplify using `using Complex.conj_mul' (Φ (b : B) χ)`.
-/
private lemma sq_apply (b : A) (χ : X) :
    Φ ((star b * b : A) : B) χ = ((‖Φ (b : B) χ‖ ^ 2 : ℝ) : ℂ) := by
  have e : Φ ((star b * b : A) : B) χ = star (Φ (b : B) χ) * Φ (b : B) χ := by
    simp [map_mul, map_star]
  rw [e]
  simpa using Complex.conj_mul' (Φ (b : B) χ)

/- English proof (translation)
Use `⟨by simp [map_mul, map_star, hb], fun χ => ?_⟩` and prove the remaining obligations. Rewrite using `[sq_apply]`. Conclude with `⟨Complex.ofReal_im _, by rw [Complex.ofReal_re]; positivity⟩`.
-/
private lemma nn_sq {b : A} (hb : p b = 0) : Nn Φ A p (star b * b) := by
  refine ⟨by simp [map_mul, map_star, hb], fun χ => ?_⟩
  rw [sq_apply]
  exact ⟨Complex.ofReal_im _, by rw [Complex.ofReal_re]; positivity⟩

/- English proof (translation)
Use `hK.induction_on (p := fun S => ∃ c : A, Nn Φ A p c ∧ ∃ δ : ℝ, 0 < δ ∧ ∀ χ ∈ S, δ ≤ (Φ (c : B) χ).re) ?_ ?_ ?_ ?_` and prove the remaining obligations. Conclude with `⟨0, ⟨by simp, fun χ => by simp⟩, 1, one_pos, by simp⟩`. Introduce and unpack `S T hST ⟨c, hc, δ, hδ, h⟩`. Conclude with `⟨c, hc, δ, hδ, fun χ hχ => h χ (hST hχ)⟩`. Introduce and unpack `S T ⟨c, hc, δ, hδ, h⟩ ⟨d, hd', ε, hε, h'⟩`.

Use `⟨c + d, nn_add Φ A p hc hd', min δ ε, lt_min hδ hε, ?_⟩` and prove the remaining obligations. Introduce and unpack `χ (hχ | hχ)`. Establish `e : Φ ((c + d : A) : B) χ = Φ (c : B) χ + Φ (d : B) χ` using `by simp`. Rewrite using `[e, Complex.add_re]`. Use `(hd'.2 χ).2` as an intermediate fact.

Use `h χ hχ` as an intermediate fact. Use `min_le_left δ ε` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion. Establish `e : Φ ((c + d : A) : B) χ = Φ (c : B) χ + Φ (d : B) χ` using `by simp`. Rewrite using `[e, Complex.add_re]`.

Use `(hc.2 χ).2` as an intermediate fact. Use `h' χ hχ` as an intermediate fact. Use `min_le_right δ ε` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion. Introduce `χ hχ`.

Take `⟨a, ha⟩` from `hd χ hχ`. Use `set b : A := a - algebraMap ℂ A (p a) with hbdef`. Establish `hb : p b = 0`. Rewrite using `[hbdef, map_sub, AlgHomClass.commutes]`. Simplify using the standard rewrite rules.

Establish `hbχ : Φ (b : B) χ ≠ 0`. Establish `e : Φ (b : B) χ = Φ (a : B) χ - p a`. Simplify using `[hbdef, AlgHomClass.commutes, Algebra.algebraMap_eq_smul_one]`. Rewrite using `[e]`. Conclude with `sub_ne_zero.2 ha`.

Establish `hpos : 0 < ‖Φ (b : B) χ‖ ^ 2 / 2`. Use `norm_pos_iff.2 hbχ` as an intermediate fact. Check the signs of the components of the expression. Establish `hopen : IsOpen {y : X | ‖Φ (b : B) χ‖ ^ 2 / 2 < (Φ ((star b * b : A) : B) y).re}` using `isOpen_lt continuous_const (Complex.continuous_re.comp (map_continuous _))`. Establish `hmem : χ ∈ {y : X | ‖Φ (b : B) χ‖ ^ 2 / 2 < (Φ ((star b * b : A) : B) y).re}`.

Rewrite using `[Set.mem_setOf_eq, sq_apply, Complex.ofReal_re]`. Combine the linear equalities and inequalities to obtain the conclusion. Conclude with `⟨_, mem_nhdsWithin_of_mem_nhds (hopen.mem_nhds hmem), star b * b, nn_sq Φ A p hb, _, hpos, fun y hy => le_of_lt hy⟩`.
-/
private lemma exists_sep {K : Set X} (hK : IsCompact K)
    (hd : ∀ χ ∈ K, ∃ a : A, Φ (a : B) χ ≠ p a) :
    ∃ c : A, Nn Φ A p c ∧ ∃ δ : ℝ, 0 < δ ∧ ∀ χ ∈ K, δ ≤ (Φ (c : B) χ).re := by
  refine hK.induction_on
    (p := fun S => ∃ c : A, Nn Φ A p c ∧ ∃ δ : ℝ, 0 < δ ∧ ∀ χ ∈ S, δ ≤ (Φ (c : B) χ).re)
    ?_ ?_ ?_ ?_
  · exact ⟨0, ⟨by simp, fun χ => by simp⟩, 1, one_pos, by simp⟩
  · rintro S T hST ⟨c, hc, δ, hδ, h⟩
    exact ⟨c, hc, δ, hδ, fun χ hχ => h χ (hST hχ)⟩
  · rintro S T ⟨c, hc, δ, hδ, h⟩ ⟨d, hd', ε, hε, h'⟩
    refine ⟨c + d, nn_add Φ A p hc hd', min δ ε, lt_min hδ hε, ?_⟩
    rintro χ (hχ | hχ)
    · have e : Φ ((c + d : A) : B) χ = Φ (c : B) χ + Φ (d : B) χ := by simp
      rw [e, Complex.add_re]
      have := (hd'.2 χ).2
      have := h χ hχ
      have := min_le_left δ ε
      linarith
    · have e : Φ ((c + d : A) : B) χ = Φ (c : B) χ + Φ (d : B) χ := by simp
      rw [e, Complex.add_re]
      have := (hc.2 χ).2
      have := h' χ hχ
      have := min_le_right δ ε
      linarith
  · intro χ hχ
    obtain ⟨a, ha⟩ := hd χ hχ
    set b : A := a - algebraMap ℂ A (p a) with hbdef
    have hb : p b = 0 := by
      rw [hbdef, map_sub, AlgHomClass.commutes]
      simp
    have hbχ : Φ (b : B) χ ≠ 0 := by
      have e : Φ (b : B) χ = Φ (a : B) χ - p a := by
        simp [hbdef, AlgHomClass.commutes, Algebra.algebraMap_eq_smul_one]
      rw [e]
      exact sub_ne_zero.2 ha
    have hpos : 0 < ‖Φ (b : B) χ‖ ^ 2 / 2 := by
      have := norm_pos_iff.2 hbχ
      positivity
    have hopen : IsOpen {y : X | ‖Φ (b : B) χ‖ ^ 2 / 2 < (Φ ((star b * b : A) : B) y).re} :=
      isOpen_lt continuous_const (Complex.continuous_re.comp (map_continuous _))
    have hmem : χ ∈ {y : X | ‖Φ (b : B) χ‖ ^ 2 / 2 < (Φ ((star b * b : A) : B) y).re} := by
      rw [Set.mem_setOf_eq, sq_apply, Complex.ofReal_re]
      linarith
    exact ⟨_, mem_nhdsWithin_of_mem_nhds (hopen.mem_nhds hmem), star b * b, nn_sq Φ A p hb,
      _, hpos, fun y hy => le_of_lt hy⟩

/- English proof (translation)
Establish `hcl : IsClosed {χ : X | ∀ a : A, Φ (a : B) χ = p a}`. Simplify using `only [Set.setOf_forall]`. Conclude with `isClosed_iInter fun a => isClosed_eq (map_continuous _) continuous_const`. Break down `Set.eq_empty_or_nonempty {χ : X | ∀ a : A, Φ (a : B) χ = p a} with he | hne` into its components or cases. Use `⟨ρ / 2, by positivity, by linarith, fun χ hχ => ?_⟩` and prove the remaining obligations.

Establish `: χ ∈ {χ : X | ∀ a : A, Φ (a : B) χ = p a}` using `hχ`. Rewrite `this` using `[he]`. Conclude with `this.elim`. Take `⟨χ₀, h₀, hmax⟩` from `hcl.isCompact.exists_isMaxOn hne (f := fun χ => ‖Φ x χ‖) (continuous_norm.comp (map_continuous _)).continuousOn`. Establish `h₁` using `h χ₀ h₀`.

Establish `h₂` using `norm_nonneg (Φ x χ₀)`. Use `⟨(‖Φ x χ₀‖ + ρ) / 2, by linarith, by linarith, fun χ hχ => ?_⟩` and prove the remaining obligations. Establish `: ‖Φ x χ‖ ≤ ‖Φ x χ₀‖` using `hmax hχ`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
private lemma exists_gap (x : B) {ρ : ℝ} (hρ : 0 < ρ)
    (h : ∀ χ, (∀ a : A, Φ (a : B) χ = p a) → ‖Φ x χ‖ < ρ) :
    ∃ ρ' : ℝ, 0 < ρ' ∧ ρ' < ρ ∧ ∀ χ, (∀ a : A, Φ (a : B) χ = p a) → ‖Φ x χ‖ < ρ' := by
  have hcl : IsClosed {χ : X | ∀ a : A, Φ (a : B) χ = p a} := by
    simp only [Set.setOf_forall]
    exact isClosed_iInter fun a => isClosed_eq (map_continuous _) continuous_const
  rcases Set.eq_empty_or_nonempty {χ : X | ∀ a : A, Φ (a : B) χ = p a} with he | hne
  · refine ⟨ρ / 2, by positivity, by linarith, fun χ hχ => ?_⟩
    have : χ ∈ {χ : X | ∀ a : A, Φ (a : B) χ = p a} := hχ
    rw [he] at this
    exact this.elim
  · obtain ⟨χ₀, h₀, hmax⟩ := hcl.isCompact.exists_isMaxOn hne
      (f := fun χ => ‖Φ x χ‖) (continuous_norm.comp (map_continuous _)).continuousOn
    have h₁ := h χ₀ h₀
    have h₂ := norm_nonneg (Φ x χ₀)
    refine ⟨(‖Φ x χ₀‖ + ρ) / 2, by linarith, by linarith, fun χ hχ => ?_⟩
    have : ‖Φ x χ‖ ≤ ‖Φ x χ₀‖ := hmax hχ
    linarith

end Core

section Rep

/- English proof (translation)
Set `S : StarSubalgebra ℂ (H →L[ℂ] H)` to `R.range`. Establish `hcomm : ∀ u v : S, u * v = v * u`. Introduce and unpack `⟨_, y, rfl⟩ ⟨_, z, rfl⟩`. Apply `Subtype.ext` to reduce the goal to its premises. Use `show R y * R z = R z * R y`.

Rewrite using `[← map_mul, ← map_mul, mul_comm]`. Set `C` to `S.topologicalClosure`. Establish `hmc : ∀ u v : C, u * v = v * u` using `(S.commRingTopologicalClosure hcomm).mul_comm`. Use `haveI hcl : IsClosed (C : Set (H →L[ℂ] H)) := S.isClosed_topologicalClosure`. Use `letI : CStarAlgebra C := inferInstance`.

Use `letI : CommCStarAlgebra C := { mul_comm := hmc }`. Set `G : C →⋆ₐ[ℂ] C(WeakDual.characterSpace ℂ C, ℂ)` to `(gelfandStarTransform C : _)`. Establish `hmem : ∀ y, R y ∈ C` using `fun y => S.le_topologicalClosure ⟨y, rfl⟩`. Set `ι : B →⋆ₐ[ℂ] C` to `R.codRestrict C hmem`. Use `⟨_, inferInstance, inferInstance, G.comp ι, fun y => ?_⟩` and prove the remaining obligations.

Apply the tactic sequence `exact (gelfandTransform_isometry C).norm_map_of_map_zero (map_zero _) (ι y)`.
-/
private theorem exists_rep {B : Type} [CommRing B] [StarRing B] [Algebra ℂ B] [StarModule ℂ B]
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (R : B →⋆ₐ[ℂ] (H →L[ℂ] H)) :
    ∃ (X : Type) (_ : TopologicalSpace X) (_ : CompactSpace X) (Φ : B →⋆ₐ[ℂ] C(X, ℂ)),
      ∀ y, ‖Φ y‖ = ‖R y‖ := by
  let S : StarSubalgebra ℂ (H →L[ℂ] H) := R.range
  have hcomm : ∀ u v : S, u * v = v * u := by
    rintro ⟨_, y, rfl⟩ ⟨_, z, rfl⟩
    apply Subtype.ext
    show R y * R z = R z * R y
    rw [← map_mul, ← map_mul, mul_comm]
  let C := S.topologicalClosure
  have hmc : ∀ u v : C, u * v = v * u := (S.commRingTopologicalClosure hcomm).mul_comm
  haveI hcl : IsClosed (C : Set (H →L[ℂ] H)) := S.isClosed_topologicalClosure
  letI : CStarAlgebra C := inferInstance
  letI : CommCStarAlgebra C := { mul_comm := hmc }
  let G : C →⋆ₐ[ℂ] C(WeakDual.characterSpace ℂ C, ℂ) := (gelfandStarTransform C : _)
  have hmem : ∀ y, R y ∈ C := fun y => S.le_topologicalClosure ⟨y, rfl⟩
  let ι : B →⋆ₐ[ℂ] C := R.codRestrict C hmem
  refine ⟨_, inferInstance, inferInstance, G.comp ι, fun y => ?_⟩
  exact (gelfandTransform_isometry C).norm_map_of_map_zero (map_zero _) (ι y)

end Rep

section Peak

variable {X : Type} [TopologicalSpace X] [CompactSpace X] {B : Type} [CommRing B] [StarRing B]
  [Algebra ℂ B] [StarModule ℂ B] (Φ : B →⋆ₐ[ℂ] C(X, ℂ)) (A : StarSubalgebra ℂ B)
  (p : A →⋆ₐ[ℂ] ℂ)

/- English proof (translation)
Take `⟨ρ', h0, h1, hg⟩` from `exists_gap Φ A p x hρ h`. Establish `hKc : IsCompact {χ : X | ρ' ≤ ‖Φ x χ‖}` using `(isClosed_le continuous_const (continuous_norm.comp (map_continuous _))).isCompact`. Take `⟨c, hc, δ, hδ, hcK⟩` from `exists_sep Φ A p hKc (fun χ hχ => by`. Assume the negation of the conclusion as `hne`. Use `push_neg at hne`.

Conclude with `absurd (hg χ hne) (not_lt.2 hχ))`. Take `⟨b, hbdef⟩ : ∃ b : A, b = a₀ - 1` from `⟨_, rfl⟩`. Establish `hb : p b = 0` using `by rw [hbdef, map_sub, map_one, ha, sub_self]`. Establish `hbχ : ∀ χ, Φ (b : B) χ = Φ (a₀ : B) χ - 1` using `fun χ => by simp [hbdef]`. Take `⟨d, hddef⟩ : ∃ d : A, d = c + star b * b` from `⟨_, rfl⟩`.

Establish `hd : Nn Φ A p d` using `hddef ▸ nn_add Φ A p hc (nn_sq Φ A p hb)`. Establish `hdχ : ∀ χ, (Φ (d : B) χ).re = (Φ (c : B) χ).re + ‖Φ (b : B) χ‖ ^ 2` using `fun χ => by`. Establish `e : Φ (d : B) χ = Φ (c : B) χ + Φ ((star b * b : A) : B) χ`. Establish `e₀ : ((c + star b * b : A) : B) = (c : B) + ((star b * b : A) : B)` using `rfl`. Rewrite using `[hddef, e₀, map_add, ContinuousMap.add_apply]`.

Rewrite using `[e, Complex.add_re, sq_apply, Complex.ofReal_re]`. Take `⟨ε, hεdef⟩ : ∃ ε : ℝ, ε = (ρ - ρ') / ρ'` from `⟨_, rfl⟩`. Establish `hε : 0 < ε` using `by rw [hεdef]; exact div_pos (sub_pos.2 h1) h0`. Establish `hρε : ρ' * (1 + ε) = ρ` using `by rw [hεdef]; field_simp; ring`. Take `⟨η, hηdef⟩ : ∃ η : ℝ, η = min δ (ε ^ 2)` from `⟨_, rfl⟩`.

Establish `hη : 0 < η` using `by rw [hηdef]; exact lt_min hδ (by positivity)`. Establish `hηδ : η ≤ δ` using `by rw [hηdef]; exact min_le_left _ _`. Establish `hηε : η ≤ ε ^ 2` using `by rw [hηdef]; exact min_le_right _ _`. Take `⟨M, hMdef⟩ : ∃ M : ℝ, M = ‖Φ (d : B)‖ + η + 1` from `⟨_, rfl⟩`. Establish `hdn` using `norm_nonneg (Φ (d : B))`.

Establish `hM : 0 < M` using `by rw [hMdef]; linarith`. Establish `hηM : η < M` using `by rw [hMdef]; linarith`. Establish `ht : ∀ χ, Φ (d : B) χ = (((Φ (d : B) χ).re : ℝ) : ℂ)` using `fun χ => Complex.ext (by simp) (by simp [(hd.2 χ).1])`. Establish `ht0 : ∀ χ, 0 ≤ (Φ (d : B) χ).re` using `fun χ => (hd.2 χ).2`. Establish `htM : ∀ χ, (Φ (d : B) χ).re ≤ M` using `fun χ => by`.

Establish `h₁` using `Complex.re_le_norm (Φ (d : B) χ)`. Establish `h₂` using `ContinuousMap.norm_coe_le_norm (Φ (d : B)) χ`. Rewrite using `[hMdef]`. Combine the linear equalities and inequalities to obtain the conclusion. Take `⟨θ, hθdef⟩ : ∃ θ : ℝ, θ = 1 - η / M` from `⟨_, rfl⟩`.

Establish `hθ1 : θ < 1` using `by rw [hθdef]; have := div_pos hη hM; linarith`. Establish `hθ0 : 0 < θ`. Rewrite using `[hθdef, sub_pos, div_lt_one hM]`. Conclude with `hηM`. Take `⟨L, hLdef⟩ : ∃ L : ℝ, L = ‖Φ x‖ * ‖Φ (a₀ : B)‖ + 1` from `⟨_, rfl⟩`.

Establish `hL : 0 < L` using `by rw [hLdef]; positivity`. Take `⟨n, hn⟩` from `exists_pow_lt_of_lt_one (div_pos hρ hL) hθ1`. Establish `hn' : L * θ ^ n < ρ` using `by rwa [lt_div_iff₀' hL] at hn`. Take `⟨g, hgdef⟩ : ∃ g : A, g = (1 - algebraMap ℂ A ((M : ℂ)⁻¹) * d) ^ n` from `⟨_, rfl⟩`. Use `⟨g, ?_, ?_⟩` and prove the remaining obligations.

Rewrite using `[hgdef, map_pow, map_sub, map_one, map_mul, hd.1, mul_zero, sub_zero, one_pow]`. Establish `hgχ : ∀ χ, Φ (g : B) χ = (((1 - (Φ (d : B) χ).re / M) ^ n : ℝ) : ℂ)` using `fun χ => by`. Establish `e : Φ (g : B) χ = (1 - (M : ℂ)⁻¹ * Φ (d : B) χ) ^ n`. Simplify using `[hgdef, AlgHomClass.commutes, Algebra.algebraMap_eq_smul_one]`. Rewrite using `[e, ht χ]`.

Use `push_cast`. Simplify using `[div_eq_inv_mul]`. Rewrite using `[ContinuousMap.norm_lt_iff _ hρ]`. Introduce `χ`. Establish `e : Φ (x * (g * a₀ : A)) χ = Φ x χ * (Φ (g : B) χ * Φ (a₀ : B) χ)` using `by simp`.

Rewrite using `[e, norm_mul, norm_mul]`. Establish `h1t : 0 ≤ 1 - (Φ (d : B) χ).re / M`. Rewrite using `[sub_nonneg, div_le_one hM]`. Conclude with `htM χ`. Establish `h2t : 1 - (Φ (d : B) χ).re / M ≤ 1`.

Use `div_nonneg (ht0 χ) hM.le` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hgn : ‖Φ (g : B) χ‖ = (1 - (Φ (d : B) χ).re / M) ^ n`. Rewrite using `[hgχ, Complex.norm_real, Real.norm_of_nonneg (pow_nonneg h1t n)]`. Distinguish the cases in `hcase : η ≤ (Φ (d : B) χ).re`.

Establish `hgθ : ‖Φ (g : B) χ‖ ≤ θ ^ n`. Rewrite using `[hgn]`. Use `pow_le_pow_left₀ h1t ?_ n` and prove the remaining obligations. Rewrite using `[hθdef]`. Use `div_le_div_of_nonneg_right hcase hM.le` as an intermediate fact.

Combine the linear equalities and inequalities to obtain the conclusion. Establish `hx` using `ContinuousMap.norm_coe_le_norm (Φ x) χ`. Establish `ha'` using `ContinuousMap.norm_coe_le_norm (Φ (a₀ : B)) χ`. Combine the equalities or inequalities in the displayed calculation. Establish `: 0 ≤ θ ^ n` using `pow_nonneg hθ0.le n`.

Rewrite using `[hLdef]`. Use the polynomial consequences of the given equalities and inequalities. Use `_ < ρ := hn'`. Use `push_neg at hcase`. Establish `hc0` using `(hc.2 χ).2`.

Establish `hdt` using `hdχ χ`. Establish `hxl : ‖Φ x χ‖ < ρ'`. Assume the negation of the conclusion as `hx`. Use `push_neg at hx`. Use `hcK χ hx` as an intermediate fact.

Use `sq_nonneg ‖Φ (b : B) χ‖` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hbl : ‖Φ (b : B) χ‖ ≤ ε`. Assume the negation of the conclusion as `hbe`. Use `push_neg at hbe`.

Establish `: ε ^ 2 < ‖Φ (b : B) χ‖ ^ 2`. Use `hε.le` as an intermediate fact. Use `gcongr`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hal : ‖Φ (a₀ : B) χ‖ ≤ 1 + ε`.

Establish `e' : Φ (a₀ : B) χ = Φ (b : B) χ + 1` using `by rw [hbχ]; ring`. Rewrite using `[e']`. Use `norm_add_le (Φ (b : B) χ) (1 : ℂ)` as an intermediate fact. Rewrite `this` using `[norm_one]`. Combine the linear equalities and inequalities to obtain the conclusion.

Establish `hg1 : ‖Φ (g : B) χ‖ ≤ 1`. Rewrite using `[hgn]`. Conclude with `pow_le_one₀ h1t h2t`. Combine the equalities or inequalities in the displayed calculation.
-/
private theorem core (a₀ : A) (x : B) {ρ : ℝ} (ha : p a₀ = 1) (hρ : 0 < ρ)
    (h : ∀ χ, (∀ a : A, Φ (a : B) χ = p a) → ‖Φ x χ‖ < ρ) :
    ∃ g : A, p g = 1 ∧ ‖Φ (x * (g * a₀ : A))‖ < ρ := by
  obtain ⟨ρ', h0, h1, hg⟩ := exists_gap Φ A p x hρ h
  have hKc : IsCompact {χ : X | ρ' ≤ ‖Φ x χ‖} :=
    (isClosed_le continuous_const (continuous_norm.comp (map_continuous _))).isCompact
  obtain ⟨c, hc, δ, hδ, hcK⟩ := exists_sep Φ A p hKc (fun χ hχ => by
    by_contra hne
    push_neg at hne
    exact absurd (hg χ hne) (not_lt.2 hχ))
  obtain ⟨b, hbdef⟩ : ∃ b : A, b = a₀ - 1 := ⟨_, rfl⟩
  have hb : p b = 0 := by rw [hbdef, map_sub, map_one, ha, sub_self]
  have hbχ : ∀ χ, Φ (b : B) χ = Φ (a₀ : B) χ - 1 := fun χ => by simp [hbdef]
  obtain ⟨d, hddef⟩ : ∃ d : A, d = c + star b * b := ⟨_, rfl⟩
  have hd : Nn Φ A p d := hddef ▸ nn_add Φ A p hc (nn_sq Φ A p hb)
  have hdχ : ∀ χ, (Φ (d : B) χ).re = (Φ (c : B) χ).re + ‖Φ (b : B) χ‖ ^ 2 := fun χ => by
    have e : Φ (d : B) χ = Φ (c : B) χ + Φ ((star b * b : A) : B) χ := by
      have e₀ : ((c + star b * b : A) : B) = (c : B) + ((star b * b : A) : B) := rfl
      rw [hddef, e₀, map_add, ContinuousMap.add_apply]
    rw [e, Complex.add_re, sq_apply, Complex.ofReal_re]
  obtain ⟨ε, hεdef⟩ : ∃ ε : ℝ, ε = (ρ - ρ') / ρ' := ⟨_, rfl⟩
  have hε : 0 < ε := by rw [hεdef]; exact div_pos (sub_pos.2 h1) h0
  have hρε : ρ' * (1 + ε) = ρ := by rw [hεdef]; field_simp; ring
  obtain ⟨η, hηdef⟩ : ∃ η : ℝ, η = min δ (ε ^ 2) := ⟨_, rfl⟩
  have hη : 0 < η := by rw [hηdef]; exact lt_min hδ (by positivity)
  have hηδ : η ≤ δ := by rw [hηdef]; exact min_le_left _ _
  have hηε : η ≤ ε ^ 2 := by rw [hηdef]; exact min_le_right _ _
  obtain ⟨M, hMdef⟩ : ∃ M : ℝ, M = ‖Φ (d : B)‖ + η + 1 := ⟨_, rfl⟩
  have hdn := norm_nonneg (Φ (d : B))
  have hM : 0 < M := by rw [hMdef]; linarith
  have hηM : η < M := by rw [hMdef]; linarith
  have ht : ∀ χ, Φ (d : B) χ = (((Φ (d : B) χ).re : ℝ) : ℂ) := fun χ =>
    Complex.ext (by simp) (by simp [(hd.2 χ).1])
  have ht0 : ∀ χ, 0 ≤ (Φ (d : B) χ).re := fun χ => (hd.2 χ).2
  have htM : ∀ χ, (Φ (d : B) χ).re ≤ M := fun χ => by
    have h₁ := Complex.re_le_norm (Φ (d : B) χ)
    have h₂ := ContinuousMap.norm_coe_le_norm (Φ (d : B)) χ
    rw [hMdef]
    linarith
  obtain ⟨θ, hθdef⟩ : ∃ θ : ℝ, θ = 1 - η / M := ⟨_, rfl⟩
  have hθ1 : θ < 1 := by rw [hθdef]; have := div_pos hη hM; linarith
  have hθ0 : 0 < θ := by
    rw [hθdef, sub_pos, div_lt_one hM]
    exact hηM
  obtain ⟨L, hLdef⟩ : ∃ L : ℝ, L = ‖Φ x‖ * ‖Φ (a₀ : B)‖ + 1 := ⟨_, rfl⟩
  have hL : 0 < L := by rw [hLdef]; positivity
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one (div_pos hρ hL) hθ1
  have hn' : L * θ ^ n < ρ := by rwa [lt_div_iff₀' hL] at hn
  obtain ⟨g, hgdef⟩ : ∃ g : A, g = (1 - algebraMap ℂ A ((M : ℂ)⁻¹) * d) ^ n := ⟨_, rfl⟩
  refine ⟨g, ?_, ?_⟩
  · rw [hgdef, map_pow, map_sub, map_one, map_mul, hd.1, mul_zero, sub_zero, one_pow]
  have hgχ : ∀ χ, Φ (g : B) χ = (((1 - (Φ (d : B) χ).re / M) ^ n : ℝ) : ℂ) := fun χ => by
    have e : Φ (g : B) χ = (1 - (M : ℂ)⁻¹ * Φ (d : B) χ) ^ n := by
      simp [hgdef, AlgHomClass.commutes, Algebra.algebraMap_eq_smul_one]
    rw [e, ht χ]
    push_cast
    simp [div_eq_inv_mul]
  rw [ContinuousMap.norm_lt_iff _ hρ]
  intro χ
  have e : Φ (x * (g * a₀ : A)) χ = Φ x χ * (Φ (g : B) χ * Φ (a₀ : B) χ) := by simp
  rw [e, norm_mul, norm_mul]
  have h1t : 0 ≤ 1 - (Φ (d : B) χ).re / M := by
    rw [sub_nonneg, div_le_one hM]
    exact htM χ
  have h2t : 1 - (Φ (d : B) χ).re / M ≤ 1 := by
    have := div_nonneg (ht0 χ) hM.le
    linarith
  have hgn : ‖Φ (g : B) χ‖ = (1 - (Φ (d : B) χ).re / M) ^ n := by
    rw [hgχ, Complex.norm_real, Real.norm_of_nonneg (pow_nonneg h1t n)]
  by_cases hcase : η ≤ (Φ (d : B) χ).re
  · have hgθ : ‖Φ (g : B) χ‖ ≤ θ ^ n := by
      rw [hgn]
      refine pow_le_pow_left₀ h1t ?_ n
      rw [hθdef]
      have := div_le_div_of_nonneg_right hcase hM.le
      linarith
    have hx := ContinuousMap.norm_coe_le_norm (Φ x) χ
    have ha' := ContinuousMap.norm_coe_le_norm (Φ (a₀ : B)) χ
    calc ‖Φ x χ‖ * (‖Φ (g : B) χ‖ * ‖Φ (a₀ : B) χ‖)
        ≤ ‖Φ x‖ * (θ ^ n * ‖Φ (a₀ : B)‖) := by gcongr
      _ = ‖Φ x‖ * ‖Φ (a₀ : B)‖ * θ ^ n := by ring
      _ ≤ L * θ ^ n := by
          have : 0 ≤ θ ^ n := pow_nonneg hθ0.le n
          rw [hLdef]
          nlinarith
      _ < ρ := hn'
  · push_neg at hcase
    have hc0 := (hc.2 χ).2
    have hdt := hdχ χ
    have hxl : ‖Φ x χ‖ < ρ' := by
      by_contra hx
      push_neg at hx
      have := hcK χ hx
      have := sq_nonneg ‖Φ (b : B) χ‖
      linarith
    have hbl : ‖Φ (b : B) χ‖ ≤ ε := by
      by_contra hbe
      push_neg at hbe
      have : ε ^ 2 < ‖Φ (b : B) χ‖ ^ 2 := by
        have := hε.le
        gcongr
      linarith
    have hal : ‖Φ (a₀ : B) χ‖ ≤ 1 + ε := by
      have e' : Φ (a₀ : B) χ = Φ (b : B) χ + 1 := by rw [hbχ]; ring
      rw [e']
      have := norm_add_le (Φ (b : B) χ) (1 : ℂ)
      rw [norm_one] at this
      linarith
    have hg1 : ‖Φ (g : B) χ‖ ≤ 1 := by
      rw [hgn]
      exact pow_le_one₀ h1t h2t
    calc ‖Φ x χ‖ * (‖Φ (g : B) χ‖ * ‖Φ (a₀ : B) χ‖)
        ≤ ‖Φ x χ‖ * (1 * (1 + ε)) := by gcongr
      _ < ρ' * (1 * (1 + ε)) := mul_lt_mul_of_pos_right hxl (by positivity)
      _ = ρ := by rw [one_mul, hρε]

end Peak

end UpperTheory.V.Z.Tf.GlobalTraceComparison

/- English proof (translation)
Introduce `B _ _ _ _ H _ _ _ R A p a₀ x ρ ha hρ h`. Take `⟨X, _, _, Φ, hΦ⟩` from `UpperTheory.V.Z.Tf.GlobalTraceComparison.exists_rep R`. Take `⟨g, hg, hn⟩` from `UpperTheory.V.Z.Tf.GlobalTraceComparison.core Φ A p a₀ x ha hρ (fun χ hχ => by`. Set `s : B →⋆ₐ[ℂ] ℂ` to `(ContinuousMap.evalStarAlgHom ℂ ℂ χ).comp Φ`. Use `h s (fun y => ?_) hχ` and prove the remaining obligations.

Rewrite using `[← hΦ y]`. Conclude with `ContinuousMap.norm_coe_le_norm (Φ y) χ)`. Conclude with `⟨g, hg, by rw [← hΦ]; exact hn⟩`.
-/
theorem UpperTheory.V.Z.Tf.GlobalTraceComparison.peak :
    UpperTheory.V.Z.Tf.GlobalTraceComparison.Peak := by
  intro B _ _ _ _ H _ _ _ R A p a₀ x ρ ha hρ h
  obtain ⟨X, _, _, Φ, hΦ⟩ := UpperTheory.V.Z.Tf.GlobalTraceComparison.exists_rep R
  obtain ⟨g, hg, hn⟩ := UpperTheory.V.Z.Tf.GlobalTraceComparison.core Φ A p a₀ x ha hρ (fun χ hχ => by
    let s : B →⋆ₐ[ℂ] ℂ := (ContinuousMap.evalStarAlgHom ℂ ℂ χ).comp Φ
    refine h s (fun y => ?_) hχ
    rw [← hΦ y]
    exact ContinuousMap.norm_coe_le_norm (Φ y) χ)
  exact ⟨g, hg, by rw [← hΦ]; exact hn⟩

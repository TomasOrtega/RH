import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.TwoWeightEqOneAddRoot

noncomputable section

namespace GlobalTheory.SemiAbelianTripleChecks

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {S S' : Scheme.{0}}

/- English proof (translation)
The claim follows from `t.act.add a b`.
-/
theorem act_add (t : SAB H S) (a b : 𝓞 E) :
    t.act.act (a + b) = lift (t.act.act a) (t.act.act b) ≫ μ[t.G] := t.act.add a b

/- English proof (translation)
Apply the tactic sequence `have h : (List.finRange 3).filter (· ∈ ({i} : Finset (Fin 3))) = [i] := by fin_cases i <;> decide`. Unfold `psum`. Rewrite using `[h]`. Establish `: padd G (x i) (pzero G T) = x i * 1` using `rfl`. Simplify using `only [List.foldr_cons, List.foldr_nil]`.

Rewrite using `[this, _root_.mul_one]`.
-/
theorem psum_singleton (G : Over S) [GrpObj G] [IsCommMonObj G] {T : Over S} (x : Fin 3 → (T ⟶ G)) (i : Fin 3) :
    psum G x {i} = x i := by
  have h : (List.finRange 3).filter (· ∈ ({i} : Finset (Fin 3))) = [i] := by
    fin_cases i <;> decide
  unfold psum
  rw [h]
  have : padd G (x i) (pzero G T) = x i * 1 := rfl
  simp only [List.foldr_cons, List.foldr_nil]
  rw [this, _root_.mul_one]

/- English proof (translation)
Establish `key : ∀ i : Fin 3, m.F3 ≫ (x3 G i).left = m'.F3 ≫ (x3 G i).left` using `fun i => by`. Establish `h1` using `m.psum_comm {i}`. Establish `h2` using `m'.psum_comm {i}`. Rewrite `h1`, `h2` using `[psum_singleton, psum_singleton]`. Rewrite using `[← h1, ← h2, h]`.

Establish `k0` using `key 0`. Establish `k1` using `key 1`. Establish `k2` using `key 2`. Apply `pullback.hom_ext` to reduce the goal to its premises. Conclude with `k0`.

Apply `pullback.hom_ext` to reduce the goal to its premises. Rewrite using `[Category.assoc, Category.assoc]`. Conclude with `k1`. Rewrite using `[Category.assoc, Category.assoc]`. Conclude with `k2`.
-/
theorem cubeMap_tripleProduct_unique {G' : Over S'} {G : Over S} [GrpObj G'] [IsCommMonObj G'] [GrpObj G] [IsCommMonObj G]
    (m m' : CubeMap G' G) (h : m.F = m'.F) : m.F3 = m'.F3 := by
  have key : ∀ i : Fin 3, m.F3 ≫ (x3 G i).left = m'.F3 ≫ (x3 G i).left := fun i => by
    have h1 := m.psum_comm {i}
    have h2 := m'.psum_comm {i}
    rw [psum_singleton, psum_singleton] at h1 h2
    rw [← h1, ← h2, h]
  have k0 := key 0
  have k1 := key 1
  have k2 := key 2
  apply pullback.hom_ext
  · exact k0
  · apply pullback.hom_ext
    · rw [Category.assoc, Category.assoc]; exact k1
    · rw [Category.assoc, Category.assoc]; exact k2

/- English proof (translation)
Take `⟨⟨F, F3, e, he, hp⟩, c, b, a, l⟩` from `m`. Take `⟨⟨F', F3', e', he', hp'⟩, c', b', a', l'⟩` from `m'`. Establish `h3 : F3 = F3'` using `cubeMap_tripleProduct_unique ⟨F, F3, e, he, hp⟩ ⟨F', F3', e', he', hp'⟩ h`. Establish `h1 : F = F'` using `h`. Establish `h2 : e = e'` using `b.trans b'.symm`.

Substitute `h1 h2 h3` using the available equality. Both sides reduce to the same expression.
-/
theorem sabMap_ext {t' : SAB H S'} {t : SAB H S} {f : S' ⟶ S} (m m' : SABMap t' t f) (h : m.φ = m'.φ) :
    m = m' := by
  obtain ⟨⟨F, F3, e, he, hp⟩, c, b, a, l⟩ := m
  obtain ⟨⟨F', F3', e', he', hp'⟩, c', b', a', l'⟩ := m'
  have h3 : F3 = F3' := cubeMap_tripleProduct_unique ⟨F, F3, e, he, hp⟩ ⟨F', F3', e', he', hp'⟩ h
  have h1 : F = F' := h
  have h2 : e = e' := b.trans b'.symm
  subst h1 h2 h3
  rfl

/- English proof (translation)
Establish `hd : (H.d : 𝓞 E) ≠ 0` using `by exact_mod_cast H.d_prime.ne_zero`. Establish `hsq : (H.bar H.rt) ^ 2 = H.rt ^ 2`. Rewrite using `[← map_pow, H.rt_sq]`. Simplify using the standard rewrite rules. Establish `hne : H.bar H.rt ≠ H.rt`.

Introduce `h`. Establish `h1 : IsCMField.complexConj E (H.rt : E) = (H.rt : E)` using `by rw [← H.bar_eq, h]`. Take `⟨φ⟩ : Nonempty (E →+* ℂ)` from `inferInstance`. Establish `h2` using `IsCMField.complexEmbedding_complexConj E φ (H.rt : E)`. Rewrite `h2` using `[h1]`.

Establish `h3 : ((H.rt : E)) ^ 2 = -(H.d : E)`. Use `congrArg (fun x : 𝓞 E => (x : E)) H.rt_sq` as an intermediate fact. Simplify using `using this`. Establish `h4 : (φ H.rt) ^ 2 = -(H.d : ℂ)` using `by rw [← map_pow, h3]; simp`. Establish `h5 : (φ H.rt).im = 0` using `Complex.conj_eq_iff_im.1 h2.symm`.

Establish `h6` using `congrArg Complex.re h4`. Simplify using `[pow_two, h5] at h6`. Establish `h7 : (0 : ℝ) < H.d` using `by exact_mod_cast H.d_prime.pos`. Use polynomial arithmetic with `[mul_self_nonneg (φ H.rt).re]`. Establish `hb : H.bar H.rt = -H.rt`.

Break down `sq_eq_sq_iff_eq_or_eq_neg.1 hsq with h | h` into its components or cases. Conclude with `absurd h hne`. Conclude with `h`. Establish `h2 : 2 * H.bar H.w0 = 1 - H.rt`. Use `congrArg H.bar H.two_weight_eq_one_add_root` as an intermediate fact.

Rewrite `this` using `[map_mul, map_add, map_one, hb, map_ofNat]`. Rewrite using `[this]`. Expand and normalize the polynomial expressions, which then agree. Establish `h3 : (2 : 𝓞 E) * (H.w0 + H.bar H.w0) = 2 * 1`. Rewrite using `[mul_add, H.two_weight_eq_one_add_root, h2]`.

Expand and normalize the polynomial expressions, which then agree. Conclude with `mul_left_cancel₀ two_ne_zero h3`.
-/
theorem cmHostUnit_add_conj_eq_one (H : Host E) : H.w0 + H.bar H.w0 = 1 := by
  have hd : (H.d : 𝓞 E) ≠ 0 := by exact_mod_cast H.d_prime.ne_zero
  have hsq : (H.bar H.rt) ^ 2 = H.rt ^ 2 := by
    rw [← map_pow, H.rt_sq]; simp
  have hne : H.bar H.rt ≠ H.rt := by
    intro h
    have h1 : IsCMField.complexConj E (H.rt : E) = (H.rt : E) := by rw [← H.bar_eq, h]
    obtain ⟨φ⟩ : Nonempty (E →+* ℂ) := inferInstance
    have h2 := IsCMField.complexEmbedding_complexConj E φ (H.rt : E)
    rw [h1] at h2
    have h3 : ((H.rt : E)) ^ 2 = -(H.d : E) := by
      have := congrArg (fun x : 𝓞 E => (x : E)) H.rt_sq
      simpa using this
    have h4 : (φ H.rt) ^ 2 = -(H.d : ℂ) := by rw [← map_pow, h3]; simp
    have h5 : (φ H.rt).im = 0 := Complex.conj_eq_iff_im.1 h2.symm
    have h6 := congrArg Complex.re h4
    simp [pow_two, h5] at h6
    have h7 : (0 : ℝ) < H.d := by exact_mod_cast H.d_prime.pos
    nlinarith [mul_self_nonneg (φ H.rt).re]
  have hb : H.bar H.rt = -H.rt := by
    rcases sq_eq_sq_iff_eq_or_eq_neg.1 hsq with h | h
    · exact absurd h hne
    · exact h
  have h2 : 2 * H.bar H.w0 = 1 - H.rt := by
    have := congrArg H.bar H.two_weight_eq_one_add_root
    rw [map_mul, map_add, map_one, hb, map_ofNat] at this
    rw [this]; ring
  have h3 : (2 : 𝓞 E) * (H.w0 + H.bar H.w0) = 2 * 1 := by
    rw [mul_add, H.two_weight_eq_one_add_root, h2]; ring
  exact mul_left_cancel₀ two_ne_zero h3

end GlobalTheory.SemiAbelianTripleChecks

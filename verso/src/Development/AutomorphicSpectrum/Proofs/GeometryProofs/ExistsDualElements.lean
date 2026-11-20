import Mathlib
open Filter Topology Metric

namespace GlobalTheory.CompanionTheory.ExpChart.DualElements

/- English proof (translation)
Establish `hspan : Submodule.span ℂ (Set.range w) = ⊤`. Assume the negation of the conclusion as `hne`. Take `⟨f, hf0, hf⟩` from `Submodule.exists_le_ker_of_lt_top _ (lt_top_iff_ne_top.2 hne)`. Apply `hf0` to reduce the goal to its premises. Establish `hfx : ∀ y : Fin g → ℂ, f y = ∑ a, f (fun j => if a = j then 1 else 0) * y a`.

Introduce `y`. Rewrite using `[LinearMap.pi_apply_eq_sum_univ f y]`. Conclude with `Finset.sum_congr rfl fun a _ => by rw [smul_eq_mul, mul_comm]`. Establish `hc` using `h (fun a => f (fun j => if a = j then 1 else 0)) (fun x => by`. Rewrite using `[← hfx]`.

Conclude with `hf (Submodule.subset_span ⟨x, rfl⟩))`. Use `LinearMap.ext fun y => ?_` and prove the remaining obligations. Rewrite using `[hfx y, LinearMap.zero_apply]`. Conclude with `Finset.sum_eq_zero fun a _ => by`. Rewrite using `[show f (fun j => if a = j then 1 else 0) = 0 from congrFun hc a, zero_mul]`.

Take `⟨b, hb, hbs, hli⟩` from `exists_linearIndependent ℂ (Set.range w)`. Set `B` to `Module.Basis.mk hli (by rw [Subtype.range_coe, hbs, hspan])`. Establish `: Fintype b` using `FiniteDimensional.fintypeBasisIndex B`. Establish `hcard : Fintype.card b = g`. Rewrite using `[← Module.finrank_eq_card_basis B]`.

Simplify using the standard rewrite rules. Set `e : Fin g ≃ b` to `(Fintype.equivFinOfCardEq hcard).symm`. Establish `hex : ∀ i, ∃ x, w x = (e i : Fin g → ℂ)` using `fun i => hb (e i).2`. Use `choose a ha using hex`. Use `⟨a, ?_⟩` and prove the remaining obligations.

Establish `hrow : LinearIndependent ℂ (Matrix.of fun i j => w (a i) j).row`. Establish `hEq : (Matrix.of fun i j => w (a i) j).row = Subtype.val ∘ e`. Use extensionality with `i j`. Simplify using `[Matrix.row, ha]`. Rewrite using `[hEq]`.

Conclude with `hli.comp _ e.injective`. Establish `hu` using `Matrix.linearIndependent_rows_iff_isUnit.1 hrow`. Conclude with `((Matrix.isUnit_iff_isUnit_det _).1 hu).ne_zero`.
-/
theorem exists_det_ne_zero {X : Type} {g : ℕ} (w : X → Fin g → ℂ)
    (h : ∀ c : Fin g → ℂ, (∀ x, ∑ a, c a * w x a = 0) → c = 0) :
    ∃ a : Fin g → X, (Matrix.of fun i j => w (a i) j).det ≠ 0 := by
  have hspan : Submodule.span ℂ (Set.range w) = ⊤ := by
    by_contra hne
    obtain ⟨f, hf0, hf⟩ := Submodule.exists_le_ker_of_lt_top _ (lt_top_iff_ne_top.2 hne)
    apply hf0
    have hfx : ∀ y : Fin g → ℂ, f y = ∑ a, f (fun j => if a = j then 1 else 0) * y a := by
      intro y
      rw [LinearMap.pi_apply_eq_sum_univ f y]
      exact Finset.sum_congr rfl fun a _ => by rw [smul_eq_mul, mul_comm]
    have hc := h (fun a => f (fun j => if a = j then 1 else 0)) (fun x => by
      rw [← hfx]
      exact hf (Submodule.subset_span ⟨x, rfl⟩))
    refine LinearMap.ext fun y => ?_
    rw [hfx y, LinearMap.zero_apply]
    exact Finset.sum_eq_zero fun a _ => by
      rw [show f (fun j => if a = j then 1 else 0) = 0 from congrFun hc a, zero_mul]
  obtain ⟨b, hb, hbs, hli⟩ := exists_linearIndependent ℂ (Set.range w)
  let B := Module.Basis.mk hli (by rw [Subtype.range_coe, hbs, hspan])
  have : Fintype b := FiniteDimensional.fintypeBasisIndex B
  have hcard : Fintype.card b = g := by
    rw [← Module.finrank_eq_card_basis B]
    simp
  let e : Fin g ≃ b := (Fintype.equivFinOfCardEq hcard).symm
  have hex : ∀ i, ∃ x, w x = (e i : Fin g → ℂ) := fun i => hb (e i).2
  choose a ha using hex
  refine ⟨a, ?_⟩
  have hrow : LinearIndependent ℂ (Matrix.of fun i j => w (a i) j).row := by
    have hEq : (Matrix.of fun i j => w (a i) j).row = Subtype.val ∘ e := by
      ext i j
      simp [Matrix.row, ha]
    rw [hEq]
    exact hli.comp _ e.injective
  have hu := Matrix.linearIndependent_rows_iff_isUnit.1 hrow
  exact ((Matrix.isUnit_iff_isUnit_det _).1 hu).ne_zero

/- English proof (translation)
Introduce `R A _ _ _ r g E v φ h1 h2 h3 h4`. Set `D : Fin g → A →+ Localization.Away r` to `fun a => AddMonoidHom.mk' (fun x => TrivSqZeroExt.snd (v a x)) (fun x y => by`. Rewrite using `[map_add, TrivSqZeroExt.snd_add])`. Establish `hD : ∀ a x, D a x = TrivSqZeroExt.snd (v a x)` using `fun _ _ => rfl`. Establish `hDmul : ∀ a x y, D a (x * y) = E x * D a y + E y * D a x`.

Introduce `a x y`. Rewrite using `[hD, hD, hD, map_mul, TrivSqZeroExt.snd_mul, h3, h3, smul_eq_mul, op_smul_eq_mul, mul_comm (TrivSqZeroExt.snd (v a x))]`. Establish `hDalg : ∀ a (s : R), D a (algebraMap R A s) = 0` using `fun a s => h2 a s`. Establish `hDs : ∀ a (s : R) x, D a (algebraMap R A s * x) = algebraMap R (Localization.Away r) s * D a x`. Introduce `a s x`.

Rewrite using `[hDmul, hDalg, h1, mul_zero, add_zero]`. Take `⟨a, ha⟩` from `exists_det_ne_zero (X := A) (fun x i => φ (D i x)) h4`. Take `⟨⟨b, hbm⟩, hb⟩` from `IsLocalization.exist_integer_multiples_of_finite (Submonoid.powers r) (fun c => E (a c))`. Establish `hbu : IsUnit (algebraMap R (Localization.Away r) b)` using `IsLocalization.map_units _ (⟨b, hbm⟩ : Submonoid.powers r)`. Establish `hb' : ∀ c, ∃ s, algebraMap R (Localization.Away r) s = algebraMap R (Localization.Away r) b * E (a c)` using `fun c => by`.

Take `⟨s, hs⟩` from `hb c`. Conclude with `⟨s, by rw [hs, Algebra.smul_def]⟩`. Use `choose s hs using hb'`. Set `t' : Fin g → A` to `fun c => algebraMap R A b * a c - algebraMap R A (s c)`. Establish `hEt' : ∀ c, E (t' c) = 0`.

Introduce `c`. Simplify using `only [t', map_sub, map_mul, h1, hs, sub_self]`. Establish `hDt' : ∀ i c, D i (t' c) = algebraMap R (Localization.Away r) b * D i (a c)`. Introduce `i c`. Simplify using `only [t', map_sub, hDs, hDalg, sub_zero]`.

Set `N : Matrix (Fin g) (Fin g) (Localization.Away r)` to `Matrix.of fun c i => D i (t' c)`. Establish `hN : φ N.det ≠ 0`. Establish `hN0 : N = algebraMap R (Localization.Away r) b • Matrix.of (fun c i => D i (a c))`. Use extensionality with `c i`. Simplify using `[N, hDt']`.

Rewrite using `[hN0, Matrix.det_smul, map_mul, map_pow, RingHom.map_det]`. Use `mul_ne_zero (pow_ne_zero _ (hbu.map φ).ne_zero) ?_` and prove the remaining obligations. Establish `hM : φ.mapMatrix (Matrix.of fun c i => D i (a c)) = Matrix.of fun i j => φ (D j (a i))`. Use extensionality with `i j`. Simplify using the standard rewrite rules.

Rewrite using `[hM]`. Conclude with `ha`. Take `⟨⟨b2, hb2m⟩, hb2⟩` from `IsLocalization.exist_integer_multiples_of_finite (Submonoid.powers r) (fun o : Option (Fin g × Fin g) => o.elim N.det (fun p => N.adjugate p.1 p.2))`. Establish `hb2u : IsUnit (algebraMap R (Localization.Away r) b2)` using `IsLocalization.map_units _ (⟨b2, hb2m⟩ : Submonoid.powers r)`. Establish `hρ : ∃ ρ, algebraMap R (Localization.Away r) ρ = algebraMap R (Localization.Away r) b2 * N.det`.

Take `⟨s, hs⟩` from `hb2 none`. Conclude with `⟨s, by rw [hs, Algebra.smul_def]; rfl⟩`. Establish `hn : ∀ c c', ∃ n, algebraMap R (Localization.Away r) n = algebraMap R (Localization.Away r) b2 * N.adjugate c c'` using `fun c c' => by`. Take `⟨s, hs⟩` from `hb2 (some (c, c'))`. Conclude with `⟨s, by rw [hs, Algebra.smul_def]; rfl⟩`.

Take `⟨ρ, hρ⟩` from `hρ`. Use `choose n hn using hn`. Use `⟨ρ, fun c => ∑ c', algebraMap R A (n c c') * t' c', ?_, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[hρ, map_mul]`. Conclude with `mul_ne_zero (hb2u.map φ).ne_zero hN`.

Introduce `c`. Rewrite using `[map_sum]`. Conclude with `Finset.sum_eq_zero fun c' _ => by rw [map_mul, hEt', mul_zero]`. Introduce `i c`. Rewrite using `[← hD, map_sum]`.

Establish `hsum : ∑ c', D i (algebraMap R A (n c c') * t' c') = algebraMap R (Localization.Away r) b2 * (N.adjugate * N) c i`. Rewrite using `[Matrix.mul_apply, Finset.mul_sum]`. Use `Finset.sum_congr rfl fun c' _ => ?_` and prove the remaining obligations. Rewrite using `[hDs, hn, mul_assoc]`. Both sides reduce to the same expression.

Rewrite using `[hsum, Matrix.adjugate_mul, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul]`. Distinguish the cases in `hic : i = c`. Substitute `hic` using the available equality. Simplify using `[hρ]`. Simplify using `[hic, Ne.symm hic]`.
-/
theorem exists_dual_elements :
    ∀ (R A : Type) [CommRing R] [CommRing A] [Algebra R A] (r : R) (g : ℕ)
      (E : A →+* Localization.Away r) (v : Fin g → (A →+* DualNumber (Localization.Away r)))
      (φ : Localization.Away r →+* ℂ),
      (∀ x : R, E (algebraMap R A x) = algebraMap R (Localization.Away r) x) →
      (∀ a (x : R), TrivSqZeroExt.snd (v a (algebraMap R A x)) = 0) →
      (∀ a x, TrivSqZeroExt.fst (v a x) = E x) →
      (∀ c : Fin g → ℂ, (∀ x, ∑ a, c a * φ (TrivSqZeroExt.snd (v a x)) = 0) → c = 0) →
      ∃ (ρ : R) (t : Fin g → A), φ (algebraMap R (Localization.Away r) ρ) ≠ 0 ∧
        (∀ c, E (t c) = 0) ∧
        ∀ a c, TrivSqZeroExt.snd (v a (t c)) =
          if a = c then algebraMap R (Localization.Away r) ρ else 0 := by
  intro R A _ _ _ r g E v φ h1 h2 h3 h4
  let D : Fin g → A →+ Localization.Away r := fun a =>
    AddMonoidHom.mk' (fun x => TrivSqZeroExt.snd (v a x)) (fun x y => by
      rw [map_add, TrivSqZeroExt.snd_add])
  have hD : ∀ a x, D a x = TrivSqZeroExt.snd (v a x) := fun _ _ => rfl
  have hDmul : ∀ a x y, D a (x * y) = E x * D a y + E y * D a x := by
    intro a x y
    rw [hD, hD, hD, map_mul, TrivSqZeroExt.snd_mul, h3, h3, smul_eq_mul, op_smul_eq_mul, mul_comm (TrivSqZeroExt.snd (v a x))]
  have hDalg : ∀ a (s : R), D a (algebraMap R A s) = 0 := fun a s => h2 a s
  have hDs : ∀ a (s : R) x, D a (algebraMap R A s * x) =
      algebraMap R (Localization.Away r) s * D a x := by
    intro a s x
    rw [hDmul, hDalg, h1, mul_zero, add_zero]
  obtain ⟨a, ha⟩ := exists_det_ne_zero (X := A) (fun x i => φ (D i x)) h4
  obtain ⟨⟨b, hbm⟩, hb⟩ := IsLocalization.exist_integer_multiples_of_finite
    (Submonoid.powers r) (fun c => E (a c))
  have hbu : IsUnit (algebraMap R (Localization.Away r) b) :=
    IsLocalization.map_units _ (⟨b, hbm⟩ : Submonoid.powers r)
  have hb' : ∀ c, ∃ s, algebraMap R (Localization.Away r) s =
      algebraMap R (Localization.Away r) b * E (a c) := fun c => by
    obtain ⟨s, hs⟩ := hb c
    exact ⟨s, by rw [hs, Algebra.smul_def]⟩
  choose s hs using hb'
  let t' : Fin g → A := fun c => algebraMap R A b * a c - algebraMap R A (s c)
  have hEt' : ∀ c, E (t' c) = 0 := by
    intro c
    simp only [t', map_sub, map_mul, h1, hs, sub_self]
  have hDt' : ∀ i c, D i (t' c) = algebraMap R (Localization.Away r) b * D i (a c) := by
    intro i c
    simp only [t', map_sub, hDs, hDalg, sub_zero]
  let N : Matrix (Fin g) (Fin g) (Localization.Away r) := Matrix.of fun c i => D i (t' c)
  have hN : φ N.det ≠ 0 := by
    have hN0 : N = algebraMap R (Localization.Away r) b •
        Matrix.of (fun c i => D i (a c)) := by
      ext c i
      simp [N, hDt']
    rw [hN0, Matrix.det_smul, map_mul, map_pow, RingHom.map_det]
    refine mul_ne_zero (pow_ne_zero _ (hbu.map φ).ne_zero) ?_
    have hM : φ.mapMatrix (Matrix.of fun c i => D i (a c)) =
        Matrix.of fun i j => φ (D j (a i)) := by
      ext i j
      simp
    rw [hM]
    exact ha
  obtain ⟨⟨b2, hb2m⟩, hb2⟩ := IsLocalization.exist_integer_multiples_of_finite
    (Submonoid.powers r)
    (fun o : Option (Fin g × Fin g) => o.elim N.det (fun p => N.adjugate p.1 p.2))
  have hb2u : IsUnit (algebraMap R (Localization.Away r) b2) :=
    IsLocalization.map_units _ (⟨b2, hb2m⟩ : Submonoid.powers r)
  have hρ : ∃ ρ, algebraMap R (Localization.Away r) ρ =
      algebraMap R (Localization.Away r) b2 * N.det := by
    obtain ⟨s, hs⟩ := hb2 none
    exact ⟨s, by rw [hs, Algebra.smul_def]; rfl⟩
  have hn : ∀ c c', ∃ n, algebraMap R (Localization.Away r) n =
      algebraMap R (Localization.Away r) b2 * N.adjugate c c' := fun c c' => by
    obtain ⟨s, hs⟩ := hb2 (some (c, c'))
    exact ⟨s, by rw [hs, Algebra.smul_def]; rfl⟩
  obtain ⟨ρ, hρ⟩ := hρ
  choose n hn using hn
  refine ⟨ρ, fun c => ∑ c', algebraMap R A (n c c') * t' c', ?_, ?_, ?_⟩
  · rw [hρ, map_mul]
    exact mul_ne_zero (hb2u.map φ).ne_zero hN
  · intro c
    rw [map_sum]
    exact Finset.sum_eq_zero fun c' _ => by rw [map_mul, hEt', mul_zero]
  · intro i c
    rw [← hD, map_sum]
    have hsum : ∑ c', D i (algebraMap R A (n c c') * t' c') =
        algebraMap R (Localization.Away r) b2 * (N.adjugate * N) c i := by
      rw [Matrix.mul_apply, Finset.mul_sum]
      refine Finset.sum_congr rfl fun c' _ => ?_
      rw [hDs, hn, mul_assoc]
      rfl
    rw [hsum, Matrix.adjugate_mul, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul]
    by_cases hic : i = c
    · subst hic
      simp [hρ]
    · simp [hic, Ne.symm hic]

end GlobalTheory.CompanionTheory.ExpChart.DualElements

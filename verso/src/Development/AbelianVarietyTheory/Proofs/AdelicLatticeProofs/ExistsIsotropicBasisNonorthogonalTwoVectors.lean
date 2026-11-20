import Mathlib
import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.IsHermHyperbolic
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.Hat1
open NumberField IsDedekindDomain Matrix GlobalTheory.UTrans GlobalTheory.AdLat
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.UTrans.IsoBasis

variable {E : Type} [Field E] {n : ℕ}

def hfL (σ : E →+* E) (G : Matrix (Fin n) (Fin n) E) (y : Fin n → E) : (Fin n → E) →ₗ[E] E where
  toFun x := hf σ G x y
  map_add' u v := by simp [hf, add_mul, Finset.sum_add_distrib]
  map_smul' c u := by simp [hf, Finset.mul_sum, mul_assoc]

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem hfL_apply (σ : E →+* E) (G : Matrix (Fin n) (Fin n) E) (y x : Fin n → E) :
    hfL σ G y x = hf σ G x y := rfl

/- English proof (translation)
Simplify using `only [hf, map_sum, map_mul, hG.invol, hG.herm]`. Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_` and prove the remaining obligations. Expand and normalize the polynomial expressions, which then agree.
-/
theorem hf_symm {σ : E →+* E} {G : Matrix (Fin n) (Fin n) E} (hG : IsHerm σ G) (x y : Fin n → E) :
    σ (hf σ G x y) = hf σ G y x := by
  simp only [hf, map_sum, map_mul, hG.invol, hG.herm]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  ring

/- English proof (translation)
Assume the negation of the conclusion as `h`. Use `push_neg at h`. Apply `hy` to reduce the goal to its premises. Establish `h0 : G.mulVec (fun b => σ (y b)) = 0`. Use function extensionality and compare the values at `a`.

Use `h (Pi.single a 1)` as an intermediate fact. Simplify `this` using `[hfL_apply, hf, Pi.single_apply, Matrix.mulVec, dotProduct, ite_mul, Finset.sum_ite_irrel]`. Establish `h1` using `Matrix.eq_zero_of_mulVec_eq_zero hG.det_ne h0`. Use function extensionality and compare the values at `b`. Use `congrFun h1 b` as an intermediate fact.

Simplify using `using this`.
-/
theorem hfL_ne {σ : E →+* E} {G : Matrix (Fin n) (Fin n) E} (hG : IsHerm σ G) {y : Fin n → E}
    (hy : y ≠ 0) : ∃ x, hfL σ G y x ≠ 0 := by
  by_contra h
  push_neg at h
  apply hy
  have h0 : G.mulVec (fun b => σ (y b)) = 0 := by
    funext a
    have := h (Pi.single a 1)
    simpa [hfL_apply, hf, Pi.single_apply, Matrix.mulVec, dotProduct, ite_mul, Finset.sum_ite_irrel] using this
  have h1 := Matrix.eq_zero_of_mulVec_eq_zero hG.det_ne h0
  funext b
  have := congrFun h1 b
  simpa using this

/- English proof (translation)
Simplify using `only [hf, Finset.mul_sum, ← Finset.sum_add_distrib]`. Use `Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Simplify using `only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, map_add, map_mul]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem hf_comb {σ : E →+* E} (G : Matrix (Fin n) (Fin n) E) (a b : E) (u w : Fin n → E) :
    hf σ G (a • u + b • w) (a • u + b • w) =
      a * σ a * hf σ G u u + a * σ b * hf σ G u w + b * σ a * hf σ G w u + b * σ b * hf σ G w w := by
  simp only [hf, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, map_add, map_mul]
  ring

/- English proof (translation)
Take `⟨w, hw0, hw⟩` from `hz`. Take `⟨c, hc⟩` from `hG.ne_id`. Use `set δ := c - σ c with hδ`. Establish `hδ0 : δ ≠ 0` using `sub_ne_zero.2 hc.symm`. Establish `hδσ : σ δ = -δ` using `by simp [hδ, hG.invol]`.

Take `⟨u, hu⟩` from `Module.Dual.exists_forall_ne_zero_of_forall_exists (fun o : Option ι => o.elim (hfL σ G w) f) (by`. Introduce and unpack `(_ | i)`. Conclude with `hfL_ne hG hw0`. Conclude with `hf0 i)`. Establish `huw : hf σ G u w ≠ 0` using `hu none`.

Establish `hui : ∀ i, f i u ≠ 0` using `fun i => hu (some i)`. Use `set a := hf σ G w u with ha`. Establish `hσa : σ a = hf σ G u w` using `hf_symm hG _ _`. Establish `ha0 : a ≠ 0`. Introduce `h`.

Apply `huw` to reduce the goal to its premises. Rewrite using `[← hσa, h, map_zero]`. Establish `huu : σ (hf σ G u u) = hf σ G u u` using `hf_symm hG _ _`. Set `bad : ι → E` to `fun i => (hf σ G u u / 2 - a * f i u / f i w) / δ`. Establish `hfin : (Set.range bad).Finite` using `Set.finite_range bad`.

Choose the witnesses or unpack the hypotheses as in `⟨t, ht⟩ : ∃ t : ℕ, (t : E) ∉ Set.range bad := by`. Assume the negation of the conclusion as `h`. Use `push_neg at h`. Conclude with `(Set.infinite_of_injective_forall_mem (f := fun t : ℕ => (t : E)) Nat.cast_injective h) hfin`. Use `⟨a • u + (-(hf σ G u u) / 2 + δ * t) • w, ?_, fun i => ?_⟩` and prove the remaining obligations.

Rewrite using `[hf_comb, hw, ← ha, ← hσa]`. Simplify using `only [map_add, map_mul, map_div₀, map_neg, huu, hδσ, map_natCast, map_ofNat]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul]`. Distinguish the cases in `h : f i w = 0`.

Simplify using `[h, ha0, hui i]`. Introduce `h'`. Apply `ht` to reduce the goal to its premises. Use `⟨i, ?_⟩` and prove the remaining obligations. Simplify using `only [bad]`.

Clear the denominators using the available nonvanishing facts. Take the linear combination `(-2 : E) * h'`.
-/
theorem exists_isotropic_avoid [CharZero E] {σ : E →+* E} {G : Matrix (Fin n) (Fin n) E}
    (hG : IsHerm σ G) (hz : ∃ z : Fin n → E, z ≠ 0 ∧ hf σ G z z = 0)
    {ι : Type} [Finite ι] (f : ι → (Fin n → E) →ₗ[E] E) (hf0 : ∀ i, ∃ x, f i x ≠ 0) :
    ∃ z, hf σ G z z = 0 ∧ ∀ i, f i z ≠ 0 := by
  obtain ⟨w, hw0, hw⟩ := hz
  obtain ⟨c, hc⟩ := hG.ne_id
  set δ := c - σ c with hδ
  have hδ0 : δ ≠ 0 := sub_ne_zero.2 hc.symm
  have hδσ : σ δ = -δ := by simp [hδ, hG.invol]
  obtain ⟨u, hu⟩ := Module.Dual.exists_forall_ne_zero_of_forall_exists
    (fun o : Option ι => o.elim (hfL σ G w) f) (by
      rintro (_ | i)
      · exact hfL_ne hG hw0
      · exact hf0 i)
  have huw : hf σ G u w ≠ 0 := hu none
  have hui : ∀ i, f i u ≠ 0 := fun i => hu (some i)
  set a := hf σ G w u with ha
  have hσa : σ a = hf σ G u w := hf_symm hG _ _
  have ha0 : a ≠ 0 := by
    intro h; apply huw; rw [← hσa, h, map_zero]
  have huu : σ (hf σ G u u) = hf σ G u u := hf_symm hG _ _
  let bad : ι → E := fun i => (hf σ G u u / 2 - a * f i u / f i w) / δ
  have hfin : (Set.range bad).Finite := Set.finite_range bad
  obtain ⟨t, ht⟩ : ∃ t : ℕ, (t : E) ∉ Set.range bad := by
    by_contra h
    push_neg at h
    exact (Set.infinite_of_injective_forall_mem (f := fun t : ℕ => (t : E)) Nat.cast_injective h) hfin
  refine ⟨a • u + (-(hf σ G u u) / 2 + δ * t) • w, ?_, fun i => ?_⟩
  · rw [hf_comb, hw, ← ha, ← hσa]
    simp only [map_add, map_mul, map_div₀, map_neg, huu, hδσ, map_natCast, map_ofNat]
    ring
  · rw [map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul]
    by_cases h : f i w = 0
    · simp [h, ha0, hui i]
    · intro h'
      apply ht
      refine ⟨i, ?_⟩
      simp only [bad]
      field_simp
      linear_combination (-2 : E) * h'

/- English proof (translation)
Set `S : Set (Fin n → E)` to `{z | hf σ G z z = 0 ∧ hf σ G x z ≠ 0 ∧ hf σ G y z ≠ 0}`. Establish `hspan : Submodule.span E S = ⊤`. Assume the negation of the conclusion as `h`. Take `⟨g, hg0, hg⟩` from `Submodule.exists_le_ker_of_lt_top _ (lt_top_iff_ne_top.2 h)`. Take `⟨z, hz0, hz1⟩` from `exists_isotropic_avoid hG hz ![g, hfL σ G x, hfL σ G y] (by`.

Introduce `i`. Use `fin_cases i`. Assume the negation of the conclusion as `h push_neg at h`. Conclude with `hg0 (LinearMap.ext h)`. Conclude with `hfL_ne hG hx`.

Conclude with `hfL_ne hG hy)`. Establish `hzS : z ∈ S`. Use `⟨hz0, fun h => hz1 1 ?_, fun h => hz1 2 ?_⟩` and prove the remaining obligations. Use `show hf σ G z x = 0`. Rewrite using `[← hf_symm hG, h, map_zero]`.

Use `show hf σ G z y = 0`. Rewrite using `[← hf_symm hG, h, map_zero]`. Conclude with `hz1 0 (hg (Submodule.subset_span hzS))`. Take `⟨v, hvS, -, hv⟩` from `Submodule.exists_fun_fin_finrank_span_eq E S`. Establish `hn : n = Module.finrank E (Submodule.span E S)`.

Rewrite using `[hspan]`. Simplify using the standard rewrite rules. Conclude with `⟨v ∘ Fin.cast hn, hv.comp _ (Fin.cast_injective hn), fun i => hvS _⟩`.
-/
theorem exists_isotropic_basis (E : Type) [Field E] [CharZero E] (n : ℕ) (σ : E →+* E)
    (G : Matrix (Fin n) (Fin n) E) (hG : IsHerm σ G)
    (hz : ∃ z : Fin n → E, z ≠ 0 ∧ hf σ G z z = 0) (x y : Fin n → E) (hx : x ≠ 0) (hy : y ≠ 0) :
    ∃ z : Fin n → Fin n → E, LinearIndependent E z ∧
      ∀ i, hf σ G (z i) (z i) = 0 ∧ hf σ G x (z i) ≠ 0 ∧ hf σ G y (z i) ≠ 0 := by
  let S : Set (Fin n → E) := {z | hf σ G z z = 0 ∧ hf σ G x z ≠ 0 ∧ hf σ G y z ≠ 0}
  have hspan : Submodule.span E S = ⊤ := by
    by_contra h
    obtain ⟨g, hg0, hg⟩ := Submodule.exists_le_ker_of_lt_top _ (lt_top_iff_ne_top.2 h)
    obtain ⟨z, hz0, hz1⟩ := exists_isotropic_avoid hG hz ![g, hfL σ G x, hfL σ G y] (by
      intro i
      fin_cases i
      · by_contra h
        push_neg at h
        exact hg0 (LinearMap.ext h)
      · exact hfL_ne hG hx
      · exact hfL_ne hG hy)
    have hzS : z ∈ S := by
      refine ⟨hz0, fun h => hz1 1 ?_, fun h => hz1 2 ?_⟩
      · show hf σ G z x = 0
        rw [← hf_symm hG, h, map_zero]
      · show hf σ G z y = 0
        rw [← hf_symm hG, h, map_zero]
    exact hz1 0 (hg (Submodule.subset_span hzS))
  obtain ⟨v, hvS, -, hv⟩ := Submodule.exists_fun_fin_finrank_span_eq E S
  have hn : n = Module.finrank E (Submodule.span E S) := by
    rw [hspan]; simp
  exact ⟨v ∘ Fin.cast hn, hv.comp _ (Fin.cast_injective hn), fun i => hvS _⟩

end GlobalTheory.UTrans.IsoBasis

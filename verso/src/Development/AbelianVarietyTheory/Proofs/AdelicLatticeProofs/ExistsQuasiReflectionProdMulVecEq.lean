import Mathlib
import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.IsHermForm

open NumberField IsDedekindDomain GlobalTheory.AdLat GlobalTheory.UnRep
open scoped TensorProduct Matrix

namespace GlobalTheory.UnRep.ReflStep

variable {F E : Type} [Field F] [Field E] [Algebra F E] (c : E ≃ₐ[F] E) {n : ℕ} (G : Matrix (Fin n) (Fin n) E)

/- English proof (translation)
Simplify using `only [hermE, Finset.mul_sum, ← Finset.sum_sub_distrib, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]`. Use `Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_` and prove the remaining obligations. Expand and normalize the polynomial expressions, which then agree.
-/
theorem herm_sub_smul_left (z x w : Fin n → E) (e : E) :
    hermE c G (z - e • x) w = hermE c G z w - e * hermE c G x w := by
  simp only [hermE, Finset.mul_sum, ← Finset.sum_sub_distrib, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  ring

/- English proof (translation)
Simplify using `only [hermE, Finset.mul_sum, ← Finset.sum_sub_distrib, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, map_sub, map_mul]`. Use `Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_` and prove the remaining obligations. Expand and normalize the polynomial expressions, which then agree.
-/
theorem herm_sub_smul_right (z x w : Fin n → E) (e : E) :
    hermE c G w (z - e • x) = hermE c G w z - c e * hermE c G w x := by
  simp only [hermE, Finset.mul_sum, ← Finset.sum_sub_distrib, Pi.sub_apply, Pi.smul_apply, smul_eq_mul,
    map_sub, map_mul]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  ring

/- English proof (translation)
Simplify using `only [hermE, Finset.mul_sum, Pi.smul_apply, smul_eq_mul]`. Use `Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_` and prove the remaining obligations. Expand and normalize the polynomial expressions, which then agree.
-/
theorem herm_smul_left (x w : Fin n → E) (e : E) :
    hermE c G (e • x) w = e * hermE c G x w := by
  simp only [hermE, Finset.mul_sum, Pi.smul_apply, smul_eq_mul]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  ring

/- English proof (translation)
Simplify using `only [hermE, map_sum, map_mul, h.1, h.2.2.1]`. Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_` and prove the remaining obligations. Expand and normalize the polynomial expressions, which then agree.
-/
theorem herm_conj (h : IsHermForm c G) (x y : Fin n → E) : c (hermE c G x y) = hermE c G y x := by
  simp only [hermE, map_sum, map_mul, h.1, h.2.2.1]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  ring

/- English proof (translation)
Establish `hd : (G *ᵥ fun b => c (x b)) ⬝ᵥ v = hermE c G v x`. Simplify using `only [hermE, dotProduct, Matrix.mulVec, Finset.sum_mul]`. Use `Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_` and prove the remaining obligations. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[refl, Matrix.add_mulVec, Matrix.one_mulVec, Matrix.smul_mulVec, Matrix.vecMulVec_mulVec, hd]`.

Use extensionality with `i`. Simplify using `only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, MulOpposite.smul_eq_mul_unop, MulOpposite.unop_op]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem refl_mulVec (x v : Fin n → E) (u : E) :
    refl c G x u *ᵥ v = v + ((u - 1) * hermE c G v x / hermE c G x x) • x := by
  have hd : (G *ᵥ fun b => c (x b)) ⬝ᵥ v = hermE c G v x := by
    simp only [hermE, dotProduct, Matrix.mulVec, Finset.sum_mul]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    ring
  rw [refl, Matrix.add_mulVec, Matrix.one_mulVec, Matrix.smul_mulVec, Matrix.vecMulVec_mulVec, hd]
  ext i
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, MulOpposite.smul_eq_mul_unop, MulOpposite.unop_op]
  ring

/- English proof (translation)
Take `⟨a, ha⟩ : ∃ a, a = hermE c G z (z - e • x)` from `⟨_, rfl⟩`. Establish `hyy : hermE c G (z - e • x) (z - e • x) = a + c a`. Rewrite using `[ha, herm_conj c G h, herm_sub_smul_left c G z x (z - e • x), herm_sub_smul_left c G z x z, herm_sub_smul_right c G z x x, he, hz]`. Take the linear combination `(hermE c G x x) * he2`. Establish `ha0 : a ≠ 0`.

Introduce and unpack `rfl`. Conclude with `hy (by simpa using hyy)`. Establish `hca : c a ≠ 0` using `by simpa using ha0`. Use `⟨-c a / a, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[map_div₀, map_neg, h.1]`.

Clear the denominators using the available nonvanishing facts. Rewrite using `[refl_mulVec, ← ha]`. Establish `: (-c a / a - 1) * a / hermE c G (z - e • x) (z - e • x) = -1`. Rewrite using `[div_eq_iff hy, hyy]`. Clear the denominators using the available nonvanishing facts.

Expand and normalize the polynomial expressions, which then agree. Rewrite using `[this]`. Simplify using the standard rewrite rules.
-/
theorem exists_refl (h : IsHermForm c G) (x z : Fin n → E) (hz : hermE c G z z = hermE c G x x) (e : E)
    (he : c e = e) (he2 : e * e = 1) (hy : hermE c G (z - e • x) (z - e • x) ≠ 0) :
    ∃ u : E, u * c u = 1 ∧ refl c G (z - e • x) u *ᵥ z = e • x := by
  obtain ⟨a, ha⟩ : ∃ a, a = hermE c G z (z - e • x) := ⟨_, rfl⟩
  have hyy : hermE c G (z - e • x) (z - e • x) = a + c a := by
    rw [ha, herm_conj c G h, herm_sub_smul_left c G z x (z - e • x), herm_sub_smul_left c G z x z,
      herm_sub_smul_right c G z x x, he, hz]
    linear_combination (hermE c G x x) * he2
  have ha0 : a ≠ 0 := by
    rintro rfl
    exact hy (by simpa using hyy)
  have hca : c a ≠ 0 := by simpa using ha0
  refine ⟨-c a / a, ?_, ?_⟩
  · rw [map_div₀, map_neg, h.1]
    field_simp
  · rw [refl_mulVec, ← ha]
    have : (-c a / a - 1) * a / hermE c G (z - e • x) (z - e • x) = -1 := by
      rw [div_eq_iff hy, hyy]
      field_simp
      ring
    rw [this]
    simp

end GlobalTheory.UnRep.ReflStep

open GlobalTheory.UnRep.ReflStep in

/- English proof (translation)
Introduce `F E _ _ _ _ _ c n G h x z hx hz`. Establish `hxs : x ∈ Submodule.span E ({x, z} : Set (Fin n → E))` using `Submodule.subset_span (by simp)`. Establish `hzs : z ∈ Submodule.span E ({x, z} : Set (Fin n → E))` using `Submodule.subset_span (by simp)`. Establish `hmem : ∀ e : E, z - e • x ∈ Submodule.span E ({x, z} : Set (Fin n → E))` using `fun e => Submodule.sub_mem _ hzs (Submodule.smul_mem _ _ hxs)`. Distinguish the cases in `h1 : hermE c G (z - (1 : E) • x) (z - (1 : E) • x) = 0`.

Establish `h2 : hermE c G (z - (-1 : E) • x) (z - (-1 : E) • x) ≠ 0`. Introduce `h2`. Rewrite `h1`, `h2` using `[herm_sub_smul_left, herm_sub_smul_right, herm_sub_smul_right]`. Simplify using `only [map_one, map_neg, hz] at h1 h2`. Apply `hx` to reduce the goal to its premises.

Establish `h4 : (4 : E) * hermE c G x x = 0` using `by linear_combination h1 + h2`. Conclude with `(mul_eq_zero.1 h4).resolve_left (by norm_num)`. Take `⟨u, hu, hu'⟩` from `exists_refl c G h x z hz (-1) (by simp) (by simp) h2`. Use `⟨[(x, -1), (z - (-1 : E) • x, u)], ?_, ?_⟩` and prove the remaining obligations. Introduce `p hp`.

Simplify using `only [List.mem_cons, List.not_mem_nil, or_false] at hp`. Break down `hp with rfl | rfl` into its components or cases. Conclude with `⟨hx, by simp, hxs⟩`. Conclude with `⟨h2, hu, hmem _⟩`. Simplify using `only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one]`.

Rewrite using `[← Matrix.mulVec_mulVec, hu', refl_mulVec, herm_smul_left, ← add_smul]`. Establish `: (-1 : E) + (-1 - 1) * (-1 * hermE c G x x) / hermE c G x x = 1`. Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[this, one_smul]`.

Take `⟨u, hu, hu'⟩` from `exists_refl c G h x z hz 1 (by simp) (by simp) h1`. Use `⟨[(z - (1 : E) • x, u)], ?_, ?_⟩` and prove the remaining obligations. Introduce `p hp`. Simplify using `only [List.mem_cons, List.not_mem_nil, or_false] at hp`. Substitute `hp` using the available equality.

Conclude with `⟨h1, hu, hmem _⟩`. Simplify using `only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one]`. Rewrite using `[hu', one_smul]`.
-/
theorem GlobalTheory.UnRep.exists_refl_prod_mulVec_eq : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (c : E ≃ₐ[F] E) (n : ℕ) (G : Matrix (Fin n) (Fin n) E), IsHermForm c G → ∀ x z : Fin n → E, hermE c G x x ≠ 0 → hermE c G z z = hermE c G x x → ∃ l : List ((Fin n → E) × E), (∀ p ∈ l, hermE c G p.1 p.1 ≠ 0 ∧ p.2 * c p.2 = 1 ∧ p.1 ∈ Submodule.span E {x, z}) ∧ (l.map fun p => refl c G p.1 p.2).prod *ᵥ z = x := by
  intro F E _ _ _ _ _ c n G h x z hx hz
  have hxs : x ∈ Submodule.span E ({x, z} : Set (Fin n → E)) := Submodule.subset_span (by simp)
  have hzs : z ∈ Submodule.span E ({x, z} : Set (Fin n → E)) := Submodule.subset_span (by simp)
  have hmem : ∀ e : E, z - e • x ∈ Submodule.span E ({x, z} : Set (Fin n → E)) := fun e =>
    Submodule.sub_mem _ hzs (Submodule.smul_mem _ _ hxs)
  by_cases h1 : hermE c G (z - (1 : E) • x) (z - (1 : E) • x) = 0
  · have h2 : hermE c G (z - (-1 : E) • x) (z - (-1 : E) • x) ≠ 0 := by
      intro h2
      rw [herm_sub_smul_left, herm_sub_smul_right, herm_sub_smul_right] at h1 h2
      simp only [map_one, map_neg, hz] at h1 h2
      apply hx
      have h4 : (4 : E) * hermE c G x x = 0 := by linear_combination h1 + h2
      exact (mul_eq_zero.1 h4).resolve_left (by norm_num)
    obtain ⟨u, hu, hu'⟩ := exists_refl c G h x z hz (-1) (by simp) (by simp) h2
    refine ⟨[(x, -1), (z - (-1 : E) • x, u)], ?_, ?_⟩
    · intro p hp
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl
      · exact ⟨hx, by simp, hxs⟩
      · exact ⟨h2, hu, hmem _⟩
    · simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one]
      rw [← Matrix.mulVec_mulVec, hu', refl_mulVec, herm_smul_left, ← add_smul]
      have : (-1 : E) + (-1 - 1) * (-1 * hermE c G x x) / hermE c G x x = 1 := by
        field_simp
        ring
      rw [this, one_smul]
  · obtain ⟨u, hu, hu'⟩ := exists_refl c G h x z hz 1 (by simp) (by simp) h1
    refine ⟨[(z - (1 : E) • x, u)], ?_, ?_⟩
    · intro p hp
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
      subst hp
      exact ⟨h1, hu, hmem _⟩
    · simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one]
      rw [hu', one_smul]

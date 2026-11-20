import Mathlib
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FiniteAdeleStrongApproximationModNat
open scoped Matrix
open NumberField IsDedekindDomain

namespace GlobalTheory.AdelicMatLat

variable (E : Type) [Field E] [NumberField E]

def intAdeles : Subring (FiniteAdeleRing (𝓞 E) E) where
  carrier := {a | ∀ v, a v ∈ v.adicCompletionIntegers E}
  mul_mem' ha hb v := mul_mem (ha v) (hb v)
  one_mem' v := one_mem (v.adicCompletionIntegers E)
  add_mem' ha hb v := add_mem (ha v) (hb v)
  zero_mem' v := zero_mem (v.adicCompletionIntegers E)
  neg_mem' ha v := neg_mem (ha v)

/- English proof (translation)
Unfold both sides. The equivalence is reflexive.
-/
theorem mem_intAdeles {a : FiniteAdeleRing (𝓞 E) E} :
    a ∈ intAdeles E ↔ ∀ v, a v ∈ v.adicCompletionIntegers E := Iff.rfl

/- English proof (translation)
Rewrite using `[mem_intAdeles, ← GlobalTheory.AdLat.mem_adelicIdeal_one_iff_integral, GlobalTheory.Idele.algebraMap_mem_adelicIdeal (GlobalTheory.AdLat.one_ne_zero_fracIdeal E), FractionalIdeal.mem_one_iff]`.
-/
theorem algebraMap_mem_iff (x : E) :
    algebraMap E (FiniteAdeleRing (𝓞 E) E) x ∈ intAdeles E ↔ ∃ r : 𝓞 E, (r : E) = x := by
  rw [mem_intAdeles, ← GlobalTheory.AdLat.mem_adelicIdeal_one_iff_integral,
    GlobalTheory.Idele.algebraMap_mem_adelicIdeal (GlobalTheory.AdLat.one_ne_zero_fracIdeal E),
    FractionalIdeal.mem_one_iff]

/- English proof (translation)
Take `⟨a, b, hb, rfl⟩` from `IsFractionRing.div_surjective (A := 𝓞 E) x`. Establish `hb0 : b ≠ 0` using `nonZeroDivisors.ne_zero hb`. Take `⟨c, hc⟩` from `Ideal.mem_span_singleton'.1 (Ideal.absNorm_mem (Ideal.span {b}))`. Use `⟨Ideal.absNorm (Ideal.span {b}), Nat.pos_of_ne_zero ?_, c * a, ?_⟩` and prove the remaining obligations. Simplify `hb0` using `[Ideal.absNorm_eq_zero_iff]`.

Establish `h1 : ((Ideal.absNorm (Ideal.span {b}) : ℕ) : E) = algebraMap (𝓞 E) E c * algebraMap (𝓞 E) E b`. Rewrite using `[← map_mul, hc, map_natCast]`. Establish `h2 : algebraMap (𝓞 E) E b ≠ 0`. Simplify using `using hb0`. Rewrite using `[h1]`.

Express the relevant statement in the definitionally equal form `algebraMap (𝓞 E) E (c * a) = _`. Rewrite using `[map_mul]`. Clear the denominators using the available nonvanishing facts.
-/
theorem exists_nat_denom (x : E) : ∃ d : ℕ, 0 < d ∧ ∃ r : 𝓞 E, (r : E) = d * x := by
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := 𝓞 E) x
  have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.1 (Ideal.absNorm_mem (Ideal.span {b}))
  refine ⟨Ideal.absNorm (Ideal.span {b}), Nat.pos_of_ne_zero ?_, c * a, ?_⟩
  · simpa [Ideal.absNorm_eq_zero_iff] using hb0
  · have h1 : ((Ideal.absNorm (Ideal.span {b}) : ℕ) : E) =
        algebraMap (𝓞 E) E c * algebraMap (𝓞 E) E b := by
      rw [← map_mul, hc, map_natCast]
    have h2 : algebraMap (𝓞 E) E b ≠ 0 := by
      simpa using hb0
    rw [h1]
    change algebraMap (𝓞 E) E (c * a) = _
    rw [map_mul]
    field_simp

/- English proof (translation)
Take `⟨x, b, hb, rfl⟩` from `GlobalTheory.AdLat.exists_eq_algebraMap_add_nsmul E 1 one_pos a`. Take `⟨d, hd, r, hr⟩` from `exists_nat_denom E x`. Use `⟨d, hd, ?_⟩` and prove the remaining obligations. Rewrite using `[mul_add, one_smul]`. Use `add_mem ?_ (mul_mem (natCast_mem _ d) hb)` and prove the remaining obligations.

Rewrite using `[← map_natCast (algebraMap E (FiniteAdeleRing (𝓞 E) E)), ← map_mul, algebraMap_mem_iff]`. Conclude with `⟨r, hr⟩`.
-/
theorem exists_nat_mul_mem (a : FiniteAdeleRing (𝓞 E) E) :
    ∃ d : ℕ, 0 < d ∧ (d : FiniteAdeleRing (𝓞 E) E) * a ∈ intAdeles E := by
  obtain ⟨x, b, hb, rfl⟩ := GlobalTheory.AdLat.exists_eq_algebraMap_add_nsmul E 1 one_pos a
  obtain ⟨d, hd, r, hr⟩ := exists_nat_denom E x
  refine ⟨d, hd, ?_⟩
  rw [mul_add, one_smul]
  refine add_mem ?_ (mul_mem (natCast_mem _ d) hb)
  rw [← map_natCast (algebraMap E (FiniteAdeleRing (𝓞 E) E)), ← map_mul, algebraMap_mem_iff]
  exact ⟨r, hr⟩

/- English proof (translation)
Use `choose d hd h using fun i => exists_nat_mul_mem E (a i)`. Use `⟨∏ i, d i, Finset.prod_pos fun i _ => hd i, fun i => ?_⟩` and prove the remaining obligations. Rewrite using `[← Finset.prod_erase_mul _ _ (Finset.mem_univ i), Nat.cast_mul, mul_assoc]`. Conclude with `mul_mem (natCast_mem _ _) (h i)`.
-/
theorem exists_nat_mul_mem_family {ι : Type} [Fintype ι] (a : ι → FiniteAdeleRing (𝓞 E) E) :
    ∃ d : ℕ, 0 < d ∧ ∀ i, (d : FiniteAdeleRing (𝓞 E) E) * a i ∈ intAdeles E := by
  classical
  choose d hd h using fun i => exists_nat_mul_mem E (a i)
  refine ⟨∏ i, d i, Finset.prod_pos fun i _ => hd i, fun i => ?_⟩
  rw [← Finset.prod_erase_mul _ _ (Finset.mem_univ i), Nat.cast_mul, mul_assoc]
  exact mul_mem (natCast_mem _ _) (h i)

variable {E} {n : ℕ}

def lat (β : Matrix (Fin n) (Fin n) (FiniteAdeleRing (𝓞 E) E)) : Submodule (𝓞 E) (Fin n → E) where
  carrier := {x | ∀ j, ∑ k, algebraMap E (FiniteAdeleRing (𝓞 E) E) (x k) * β k j ∈ intAdeles E}
  add_mem' {x y} hx hy j := by
    simpa only [Pi.add_apply, map_add, add_mul, Finset.sum_add_distrib] using add_mem (hx j) (hy j)
  zero_mem' j := by simp
  smul_mem' c x hx j := by
    have h : algebraMap E (FiniteAdeleRing (𝓞 E) E) (c : E) ∈ intAdeles E :=
      (algebraMap_mem_iff E _).2 ⟨c, rfl⟩
    have h2 := mul_mem h (hx j)
    rw [Finset.mul_sum] at h2
    convert h2 using 2 with k
    rw [← mul_assoc, ← map_mul]
    rfl

/- English proof (translation)
Unfold both sides. The equivalence is reflexive.
-/
theorem mem_lat {β : Matrix (Fin n) (Fin n) (FiniteAdeleRing (𝓞 E) E)} {x : Fin n → E} :
    x ∈ lat β ↔
      ∀ j, ∑ k, algebraMap E (FiniteAdeleRing (𝓞 E) E) (x k) * β k j ∈ intAdeles E := Iff.rfl

/- English proof (translation)
Take `⟨d, hd, h⟩` from `exists_nat_mul_mem_family E (fun p : Fin n × Fin n => β p.1 p.2)`. Rewrite using `[eq_top_iff, ← (Pi.basisFun E (Fin n)).span_eq, Submodule.span_le]`. Introduce and unpack `_ ⟨i, rfl⟩`. Establish `hm : (Pi.single i (d : E) : Fin n → E) ∈ lat β`. Introduce `j`.

Rewrite using `[Finset.sum_eq_single i (by intro k _ hk; simp [Pi.single_eq_of_ne hk]) (by simp)]`. Simplify using `using h (i, j)`. Establish `hd' : (d : E) ≠ 0` using `Nat.cast_ne_zero.2 hd.ne'`. Establish `he : Pi.basisFun E (Fin n) i = (d : E)⁻¹ • (Pi.single i (d : E) : Fin n → E)`. Rewrite using `[Pi.basisFun_apply, ← Pi.single_smul, smul_eq_mul, inv_mul_cancel₀ hd']`.

Rewrite using `[he]`. Conclude with `Submodule.smul_mem _ _ (Submodule.subset_span hm)`.
-/
theorem span_lat (β : Matrix (Fin n) (Fin n) (FiniteAdeleRing (𝓞 E) E)) :
    Submodule.span E (lat β : Set (Fin n → E)) = ⊤ := by
  classical
  obtain ⟨d, hd, h⟩ := exists_nat_mul_mem_family E (fun p : Fin n × Fin n => β p.1 p.2)
  rw [eq_top_iff, ← (Pi.basisFun E (Fin n)).span_eq, Submodule.span_le]
  rintro _ ⟨i, rfl⟩
  have hm : (Pi.single i (d : E) : Fin n → E) ∈ lat β := by
    intro j
    rw [Finset.sum_eq_single i (by intro k _ hk; simp [Pi.single_eq_of_ne hk]) (by simp)]
    simpa using h (i, j)
  have hd' : (d : E) ≠ 0 := Nat.cast_ne_zero.2 hd.ne'
  have he : Pi.basisFun E (Fin n) i = (d : E)⁻¹ • (Pi.single i (d : E) : Fin n → E) := by
    rw [Pi.basisFun_apply, ← Pi.single_smul, smul_eq_mul, inv_mul_cancel₀ hd']
  rw [he]
  exact Submodule.smul_mem _ _ (Submodule.subset_span hm)

/- English proof (translation)
Take `⟨d, hd, h⟩` from `exists_nat_mul_mem_family E (fun p : Fin n × Fin n => β⁻¹.1 p.1 p.2)`. Establish `hd' : (d : E) ≠ 0` using `Nat.cast_ne_zero.2 hd.ne'`. Establish `hle : lat β.1 ≤ Submodule.span (𝓞 E) (Set.range fun i : Fin n => (Pi.single i (d : E)⁻¹ : Fin n → E))`. Introduce `x hx`. Establish `h1 : ∀ j, ∃ r : 𝓞 E, (r : E) = d * x j`.

Introduce `j`. Rewrite using `[← algebraMap_mem_iff]`. Establish `h2 : algebraMap E (FiniteAdeleRing (𝓞 E) E) (d * x j) = ∑ l, (∑ k, algebraMap E (FiniteAdeleRing (𝓞 E) E) (x k) * β.1 k l) * ((d : FiniteAdeleRing (𝓞 E) E) * β⁻¹.1 l j)`. Establish `h3 : ((fun k => algebraMap E (FiniteAdeleRing (𝓞 E) E) (x k)) ᵥ* β.1) ᵥ* β⁻¹.1 = fun k => algebraMap E (FiniteAdeleRing (𝓞 E) E) (x k)`. Rewrite using `[Matrix.vecMul_vecMul, Units.mul_inv, Matrix.vecMul_one]`.

Rewrite using `[map_mul, map_natCast, ← congrFun h3 j]`. Simplify using `only [Matrix.vecMul, dotProduct]`. Rewrite using `[Finset.mul_sum]`. Conclude with `Finset.sum_congr rfl fun l _ => mul_left_comm _ _ _`. Rewrite using `[h2]`.

Conclude with `sum_mem fun l _ => mul_mem (hx l) (h (l, j))`. Use `choose r hr using h1`. Establish `h4 : x = ∑ i, r i • (Pi.single i (d : E)⁻¹ : Fin n → E)`. Use extensionality with `j`. Rewrite using `[Finset.sum_apply, Finset.sum_eq_single j (by intro k _ hk; simp [Pi.single_eq_of_ne hk.symm]) (by simp)]`.

Rewrite using `[Pi.smul_apply, Pi.single_eq_same]`. Express the relevant statement in the definitionally equal form `x j = (r j : E) * (d : E)⁻¹`. Rewrite using `[hr]`. Clear the denominators using the available nonvanishing facts. Rewrite using `[h4]`.

Conclude with `sum_mem fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)`. Use `haveI := isNoetherian_span_of_finite (𝓞 E) (Set.finite_range fun i : Fin n => (Pi.single i (d : E)⁻¹ : Fin n → E))`. Conclude with `Submodule.FG.of_le_of_isNoetherian hle`.
-/
theorem fg_lat (β : GL (Fin n) (FiniteAdeleRing (𝓞 E) E)) : (lat β.1).FG := by
  classical
  obtain ⟨d, hd, h⟩ := exists_nat_mul_mem_family E (fun p : Fin n × Fin n => β⁻¹.1 p.1 p.2)
  have hd' : (d : E) ≠ 0 := Nat.cast_ne_zero.2 hd.ne'
  have hle : lat β.1 ≤ Submodule.span (𝓞 E)
      (Set.range fun i : Fin n => (Pi.single i (d : E)⁻¹ : Fin n → E)) := by
    intro x hx
    have h1 : ∀ j, ∃ r : 𝓞 E, (r : E) = d * x j := by
      intro j
      rw [← algebraMap_mem_iff]
      have h2 : algebraMap E (FiniteAdeleRing (𝓞 E) E) (d * x j) =
          ∑ l, (∑ k, algebraMap E (FiniteAdeleRing (𝓞 E) E) (x k) * β.1 k l) *
            ((d : FiniteAdeleRing (𝓞 E) E) * β⁻¹.1 l j) := by
        have h3 : ((fun k => algebraMap E (FiniteAdeleRing (𝓞 E) E) (x k)) ᵥ* β.1) ᵥ* β⁻¹.1 =
            fun k => algebraMap E (FiniteAdeleRing (𝓞 E) E) (x k) := by
          rw [Matrix.vecMul_vecMul, Units.mul_inv, Matrix.vecMul_one]
        rw [map_mul, map_natCast, ← congrFun h3 j]
        simp only [Matrix.vecMul, dotProduct]
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun l _ => mul_left_comm _ _ _
      rw [h2]
      exact sum_mem fun l _ => mul_mem (hx l) (h (l, j))
    choose r hr using h1
    have h4 : x = ∑ i, r i • (Pi.single i (d : E)⁻¹ : Fin n → E) := by
      ext j
      rw [Finset.sum_apply, Finset.sum_eq_single j
        (by intro k _ hk; simp [Pi.single_eq_of_ne hk.symm]) (by simp)]
      rw [Pi.smul_apply, Pi.single_eq_same]
      change x j = (r j : E) * (d : E)⁻¹
      rw [hr]
      field_simp
    rw [h4]
    exact sum_mem fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  haveI := isNoetherian_span_of_finite (𝓞 E)
    (Set.finite_range fun i : Fin n => (Pi.single i (d : E)⁻¹ : Fin n → E))
  exact Submodule.FG.of_le_of_isNoetherian hle

/- English proof (translation)
Assemble the required witnesses or components as `⟨fg_lat β, span_lat β.1⟩`.
-/
theorem isLattice_lat (β : GL (Fin n) (FiniteAdeleRing (𝓞 E) E)) :
    Submodule.IsLattice E (lat β.1) := ⟨fg_lat β, span_lat β.1⟩

/- English proof (translation)
Take `⟨d₁, hd₁, h₁⟩` from `exists_nat_mul_mem_family E (fun p : Fin n × Fin n => β.1 p.1 p.2)`. Take `⟨d₂, hd₂, h₂⟩` from `exists_nat_mul_mem_family E (fun p : Fin n × Fin n => algebraMap E (FiniteAdeleRing (𝓞 E) E) (δ⁻¹.1 p.1 p.2))`. Use `choose x b hb hx using fun k => GlobalTheory.AdLat.exists_eq_algebraMap_add_nsmul E (d₁ * d₂) (Nat.mul_pos hd₁ hd₂) (β⁻¹.1 i k)`. Establish `hxl : x ∈ lat β.1`. Introduce `l`.

Establish `h3 : ∑ k, algebraMap E (FiniteAdeleRing (𝓞 E) E) (x k) * β.1 k l = (β⁻¹.1 * β.1) i l - ∑ k, ((d₂ : FiniteAdeleRing (𝓞 E) E) * b k) * ((d₁ : FiniteAdeleRing (𝓞 E) E) * β.1 k l)`. Rewrite using `[Matrix.mul_apply, ← Finset.sum_sub_distrib]`. Use `Finset.sum_congr rfl fun k _ => ?_` and prove the remaining obligations. Rewrite using `[hx k, nsmul_eq_mul, Nat.cast_mul]`. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[h3, Units.inv_mul]`. Use `sub_mem ?_ (sum_mem fun k _ => mul_mem (mul_mem (natCast_mem _ _) (hb k)) (h₁ (k, l)))` and prove the remaining obligations. Rewrite using `[Matrix.one_apply]`. Use `split_ifs`. Conclude with `one_mem _`.

Conclude with `zero_mem _`. Take `⟨y, hy⟩` from `hδ x hxl`. Establish `h4 : (y j : E) = ∑ k, (M : E) * x k * δ⁻¹.1 k j`. Establish `h5 : ((M : E) • x) ᵥ* δ⁻¹.1 = fun i => (y i : E)`. Rewrite using `[hy, Matrix.vecMul_vecMul, Units.mul_inv, Matrix.vecMul_one]`.

Rewrite using `[← congrFun h5 j]`. Both sides reduce to the same expression. Establish `h6 : (M : FiniteAdeleRing (𝓞 E) E) * (β⁻¹.1 * δ⁻¹.1.map (algebraMap E (FiniteAdeleRing (𝓞 E) E))) i j = algebraMap E (FiniteAdeleRing (𝓞 E) E) (y j : E) + ∑ k, ((M : FiniteAdeleRing (𝓞 E) E) * ((d₁ : FiniteAdeleRing (𝓞 E) E) * b k)) * ((d₂ : FiniteAdeleRing (𝓞 E) E) * algebraMap …`. Rewrite using `[h4, map_sum, Matrix.mul_apply, Finset.mul_sum, ← Finset.sum_add_distrib]`. Use `Finset.sum_congr rfl fun k _ => ?_` and prove the remaining obligations.

Rewrite using `[hx k, nsmul_eq_mul, Nat.cast_mul, Matrix.map_apply, map_mul, map_mul, map_natCast]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[h6]`. Conclude with `add_mem ((algebraMap_mem_iff E _).2 ⟨y j, rfl⟩) (sum_mem fun k _ => mul_mem (mul_mem (natCast_mem _ _) (mul_mem (natCast_mem _ _) (hb k))) (h₂ (k, j)))`.
-/
theorem inv_mul_mem (β : GL (Fin n) (FiniteAdeleRing (𝓞 E) E)) (M : ℕ) (δ : GL (Fin n) E)
    (hδ : ∀ x ∈ lat β.1, ∃ y : Fin n → 𝓞 E, (M : E) • x = (fun i => (y i : E)) ᵥ* δ.1)
    (i j : Fin n) :
    (M : FiniteAdeleRing (𝓞 E) E) *
      (β⁻¹.1 * δ⁻¹.1.map (algebraMap E (FiniteAdeleRing (𝓞 E) E))) i j ∈ intAdeles E := by
  classical
  obtain ⟨d₁, hd₁, h₁⟩ := exists_nat_mul_mem_family E (fun p : Fin n × Fin n => β.1 p.1 p.2)
  obtain ⟨d₂, hd₂, h₂⟩ := exists_nat_mul_mem_family E
    (fun p : Fin n × Fin n => algebraMap E (FiniteAdeleRing (𝓞 E) E) (δ⁻¹.1 p.1 p.2))
  choose x b hb hx using fun k => GlobalTheory.AdLat.exists_eq_algebraMap_add_nsmul E (d₁ * d₂)
    (Nat.mul_pos hd₁ hd₂) (β⁻¹.1 i k)
  have hxl : x ∈ lat β.1 := by
    intro l
    have h3 : ∑ k, algebraMap E (FiniteAdeleRing (𝓞 E) E) (x k) * β.1 k l =
        (β⁻¹.1 * β.1) i l - ∑ k, ((d₂ : FiniteAdeleRing (𝓞 E) E) * b k) *
          ((d₁ : FiniteAdeleRing (𝓞 E) E) * β.1 k l) := by
      rw [Matrix.mul_apply, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [hx k, nsmul_eq_mul, Nat.cast_mul]
      ring
    rw [h3, Units.inv_mul]
    refine sub_mem ?_ (sum_mem fun k _ => mul_mem (mul_mem (natCast_mem _ _) (hb k)) (h₁ (k, l)))
    rw [Matrix.one_apply]
    split_ifs
    · exact one_mem _
    · exact zero_mem _
  obtain ⟨y, hy⟩ := hδ x hxl
  have h4 : (y j : E) = ∑ k, (M : E) * x k * δ⁻¹.1 k j := by
    have h5 : ((M : E) • x) ᵥ* δ⁻¹.1 = fun i => (y i : E) := by
      rw [hy, Matrix.vecMul_vecMul, Units.mul_inv, Matrix.vecMul_one]
    rw [← congrFun h5 j]
    rfl
  have h6 : (M : FiniteAdeleRing (𝓞 E) E) *
      (β⁻¹.1 * δ⁻¹.1.map (algebraMap E (FiniteAdeleRing (𝓞 E) E))) i j =
      algebraMap E (FiniteAdeleRing (𝓞 E) E) (y j : E) +
        ∑ k, ((M : FiniteAdeleRing (𝓞 E) E) * ((d₁ : FiniteAdeleRing (𝓞 E) E) * b k)) *
          ((d₂ : FiniteAdeleRing (𝓞 E) E) *
            algebraMap E (FiniteAdeleRing (𝓞 E) E) (δ⁻¹.1 k j)) := by
    rw [h4, map_sum, Matrix.mul_apply, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [hx k, nsmul_eq_mul, Nat.cast_mul, Matrix.map_apply, map_mul, map_mul, map_natCast]
    ring
  rw [h6]
  exact add_mem ((algebraMap_mem_iff E _).2 ⟨y j, rfl⟩) (sum_mem fun k _ =>
    mul_mem (mul_mem (natCast_mem _ _) (mul_mem (natCast_mem _ _) (hb k))) (h₂ (k, j)))

/- English proof (translation)
Introduce `E _ _ n β`. Use `⟨lat β.1, isLattice_lat β, fun M δ h1 h2 i j v => ⟨?_, inv_mul_mem β M δ h2 i j v⟩⟩` and prove the remaining obligations. Rewrite using `[Matrix.mul_apply]`. Conclude with `h1 i j v`.
-/
theorem exists_lattice_integral : ∀ (E : Type) [Field E] [NumberField E] (n : ℕ) (β : GL (Fin n) (FiniteAdeleRing (𝓞 E) E)), ∃ Λ : Submodule (𝓞 E) (Fin n → E), Submodule.IsLattice E Λ ∧ ∀ (M : ℕ) (δ : GL (Fin n) E), (∀ i, δ.1 i ∈ Λ) → (∀ x ∈ Λ, ∃ y : Fin n → 𝓞 E, (M : E) • x = (fun i => (y i : E)) ᵥ* δ.1) → ∀ (i j : Fin n) (v : HeightOneSpectrum (𝓞 E)), (δ.1.map (algebraMap E (FiniteAdeleRing (𝓞 E) E)) * β.1) i j v ∈ v.adicCompletionIntegers E ∧ ((M : FiniteAdeleRing (𝓞 E) E) * (β⁻¹.1 * δ⁻¹.1.map (algebraMap E (FiniteAdeleRing (𝓞 E) E))) i j) v ∈ v.adicCompletionIntegers E := by
  intro E _ _ n β
  refine ⟨lat β.1, isLattice_lat β, fun M δ h1 h2 i j v => ⟨?_, inv_mul_mem β M δ h2 i j v⟩⟩
  rw [Matrix.mul_apply]
  exact h1 i j v

end GlobalTheory.AdelicMatLat

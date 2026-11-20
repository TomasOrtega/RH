import Mathlib
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.DualRestrictSurjectiveOfIsTorsionFreeQuotient
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Clauses
open ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory

open Module

/- English proof (translation)
Set `w : Fin g ⊕ Fin g → ℤ` to `Sum.elim u 1`. Establish `hw : ∀ j, IsCoprime (w j) (M : ℤ)`. Introduce and unpack `(i | i)`. Conclude with `⟨d i, -t i, by simp only [w, Sum.elim_inl]; linear_combination ht i⟩`. Conclude with `isCoprime_one_left`.

Set `S : (Fin g ⊕ Fin g → ℤ) →ₗ[ℤ] (Fin g ⊕ Fin g → ℤ)` to `{ toFun := fun a j => w j * a j map_add' := fun a c => by funext j; simp [mul_add] map_smul' := fun r a => by funext j; simp; ring }`. Set `L : (Fin g ⊕ Fin g → ℤ) →+ La` to `(b.equivFun.symm.toLinearMap ∘ₗ S).toAddMonoidHom`. Establish `hrepr : ∀ v j, b.repr (b.equivFun.symm v) j = v j` using `fun v j => by`. Rewrite using `[← Basis.equivFun_apply, LinearEquiv.apply_symm_apply]`. Establish `hL : ∀ a j, b.repr (L a) j = w j * a j` using `fun a j => hrepr (S a) j`.

Use `⟨L, fun a => ⟨?_, ?_⟩, fun x => ?_, fun a c => ?_⟩` and prove the remaining obligations. Introduce and unpack `⟨y, hy⟩`. Establish `hdiv : ∀ j, (M : ℤ) ∣ a j`. Introduce `j`. Use `hL a j` as an intermediate fact.

Rewrite `this` using `[hy, map_nsmul]`. Establish `h2 : (M : ℤ) ∣ w j * a j` using `⟨b.repr y j, by rw [← this]; simp⟩`. Conclude with `(hw j).symm.dvd_of_dvd_mul_left h2`. Use `choose c hc using hdiv`. Conclude with `⟨c, funext fun j => by simp [hc j]⟩`.

Introduce and unpack `⟨c, rfl⟩`. Conclude with `⟨L c, map_nsmul L M c⟩`. Use `⟨Sum.elim (fun i => d i * b.repr x (Sum.inl i)) (fun i => b.repr x (Sum.inr i)), b.equivFun.symm (Sum.elim (fun i => -(t i * b.repr x (Sum.inl i))) 0), ?_⟩` and prove the remaining obligations. Apply `b.repr.injective` to reduce the goal to its premises. Use extensionality with `j`.

Rewrite using `[map_add, Finsupp.add_apply, hL, map_nsmul, Finsupp.smul_apply]`. Break down `j with i | i` into its components or cases. Simplify using `only [w, Sum.elim_inl, hrepr, nsmul_eq_mul]`. Take the linear combination `(-(b.repr x (Sum.inl i))) * ht i`. Simplify using `[w, hrepr]`.

Use `⟨∑ i, t i * (a (Sum.inl i) * c (Sum.inr i) - a (Sum.inr i) * c (Sum.inl i)), ?_⟩` and prove the remaining obligations. Rewrite using `[hb.apply_eq_sum hB, omegaStd, Finset.mul_sum, ← Finset.sum_add_distrib]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Simplify using `only [hL, w, Sum.elim_inl, Sum.elim_inr, Pi.one_apply, one_mul]`. Take the linear combination `(a (Sum.inl i) * c (Sum.inr i) - a (Sum.inr i) * c (Sum.inl i)) * ht i`.
-/
theorem exists_lattice_map_of_symplecticBasis {La : Type} [AddCommGroup La] {g : ℕ}
    (EF : LinearMap.BilinForm ℤ La) (hB : EF.IsAlt) (b : Basis (Fin g ⊕ Fin g) ℤ La)
    (d : Fin g → ℤ) (hb : IsSymplecticBasisOfType EF b d) (M : ℕ) (u t : Fin g → ℤ)
    (ht : ∀ i, u i * d i = 1 + (M : ℤ) * t i) :
    ∃ L : (Fin g ⊕ Fin g → ℤ) →+ La,
      (∀ a, (∃ y, L a = M • y) ↔ ∃ c, a = M • c) ∧ (∀ x, ∃ a y, x = L a + M • y) ∧
      ∀ a c, ∃ k : ℤ, EF (L a) (L c) = omegaStd a c + M * k := by
  classical
  let w : Fin g ⊕ Fin g → ℤ := Sum.elim u 1
  have hw : ∀ j, IsCoprime (w j) (M : ℤ) := by
    rintro (i | i)
    · exact ⟨d i, -t i, by simp only [w, Sum.elim_inl]; linear_combination ht i⟩
    · exact isCoprime_one_left
  let S : (Fin g ⊕ Fin g → ℤ) →ₗ[ℤ] (Fin g ⊕ Fin g → ℤ) :=
    { toFun := fun a j => w j * a j
      map_add' := fun a c => by funext j; simp [mul_add]
      map_smul' := fun r a => by funext j; simp; ring }
  let L : (Fin g ⊕ Fin g → ℤ) →+ La := (b.equivFun.symm.toLinearMap ∘ₗ S).toAddMonoidHom
  have hrepr : ∀ v j, b.repr (b.equivFun.symm v) j = v j := fun v j => by
    rw [← Basis.equivFun_apply, LinearEquiv.apply_symm_apply]
  have hL : ∀ a j, b.repr (L a) j = w j * a j := fun a j => hrepr (S a) j
  refine ⟨L, fun a => ⟨?_, ?_⟩, fun x => ?_, fun a c => ?_⟩
  · rintro ⟨y, hy⟩
    have hdiv : ∀ j, (M : ℤ) ∣ a j := by
      intro j
      have := hL a j
      rw [hy, map_nsmul] at this
      have h2 : (M : ℤ) ∣ w j * a j := ⟨b.repr y j, by rw [← this]; simp⟩
      exact (hw j).symm.dvd_of_dvd_mul_left h2
    choose c hc using hdiv
    exact ⟨c, funext fun j => by simp [hc j]⟩
  · rintro ⟨c, rfl⟩
    exact ⟨L c, map_nsmul L M c⟩
  · refine ⟨Sum.elim (fun i => d i * b.repr x (Sum.inl i)) (fun i => b.repr x (Sum.inr i)),
      b.equivFun.symm (Sum.elim (fun i => -(t i * b.repr x (Sum.inl i))) 0), ?_⟩
    apply b.repr.injective
    ext j
    rw [map_add, Finsupp.add_apply, hL, map_nsmul, Finsupp.smul_apply]
    rcases j with i | i
    · simp only [w, Sum.elim_inl, hrepr, nsmul_eq_mul]
      linear_combination (-(b.repr x (Sum.inl i))) * ht i
    · simp [w, hrepr]
  · refine ⟨∑ i, t i * (a (Sum.inl i) * c (Sum.inr i) - a (Sum.inr i) * c (Sum.inl i)), ?_⟩
    rw [hb.apply_eq_sum hB, omegaStd, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [hL, w, Sum.elim_inl, Sum.elim_inr, Pi.one_apply, one_mul]
    linear_combination (a (Sum.inl i) * c (Sum.inr i) - a (Sum.inr i) * c (Sum.inl i)) * ht i

/- English proof (translation)
Introduce `La _ _ _ EF halt hinj e M hperf hcop`. Establish `hB : EF.IsAlt` using `halt`. Take `⟨g, b, d, hb, -, -⟩` from `exists_isSymplecticBasisOfType_pos hB hinj`. Establish `hg : Module.finrank ℤ La / 2 = g`. Rewrite using `[IsSymplecticBasisOfType.finrank_eq b, Fintype.card_fin]`.

Use linear arithmetic over natural numbers and integers. Rewrite using `[hg]`. Establish `hde : ∀ i, d i ∣ (e : ℤ)`. Introduce `i`. Take `⟨x, hx⟩` from `hperf (b.coord (Sum.inr i))`.

Establish `h1` using `hb.apply_right x i`. Rewrite `h1` using `[hx]`. Simplify using `only [LinearMap.smul_apply, Basis.coord_apply, Basis.repr_self, Finsupp.single_eq_same, nsmul_eq_mul, mul_one] at h1`. Conclude with `⟨b.repr x (Sum.inl i), by rw [h1, mul_comm]⟩`. Establish `hc : ∀ i, IsCoprime (M : ℤ) (d i)` using `fun i => (Nat.isCoprime_iff_coprime.2 hcop).of_isCoprime_of_dvd_right (hde i)`.

Use `choose p u hpu using hc`. Conclude with `exists_lattice_map_of_symplecticBasis EF hB b d hb M u (fun i => -p i) (fun i => by linear_combination hpu i)`.
-/
theorem exists_lattice_map_mod_of_perfect : ∀ (La : Type) [AddCommGroup La] [Module.Free ℤ La] [Module.Finite ℤ La] (EF : LinearMap.BilinForm ℤ La),
  (∀ x, EF x x = 0) → Function.Injective EF → ∀ (e M : ℕ), (∀ f : La →ₗ[ℤ] ℤ, ∃ x, EF x = e • f) → M.Coprime e →
  ∃ L : (Fin (Module.finrank ℤ La / 2) ⊕ Fin (Module.finrank ℤ La / 2) → ℤ) →+ La,
    (∀ a, (∃ y, L a = M • y) ↔ ∃ c, a = M • c) ∧ (∀ x, ∃ a y, x = L a + M • y) ∧
    ∀ a c, ∃ k : ℤ, EF (L a) (L c) = omegaStd a c + M * k := by
  intro La _ _ _ EF halt hinj e M hperf hcop
  have hB : EF.IsAlt := halt
  obtain ⟨g, b, d, hb, -, -⟩ := exists_isSymplecticBasisOfType_pos hB hinj
  have hg : Module.finrank ℤ La / 2 = g := by
    rw [IsSymplecticBasisOfType.finrank_eq b, Fintype.card_fin]; omega
  rw [hg]
  have hde : ∀ i, d i ∣ (e : ℤ) := by
    intro i
    obtain ⟨x, hx⟩ := hperf (b.coord (Sum.inr i))
    have h1 := hb.apply_right x i
    rw [hx] at h1
    simp only [LinearMap.smul_apply, Basis.coord_apply, Basis.repr_self, Finsupp.single_eq_same,
      nsmul_eq_mul, mul_one] at h1
    exact ⟨b.repr x (Sum.inl i), by rw [h1, mul_comm]⟩
  have hc : ∀ i, IsCoprime (M : ℤ) (d i) := fun i =>
    (Nat.isCoprime_iff_coprime.2 hcop).of_isCoprime_of_dvd_right (hde i)
  choose p u hpu using hc
  exact exists_lattice_map_of_symplecticBasis EF hB b d hb M u (fun i => -p i)
    (fun i => by linear_combination hpu i)

end GlobalTheory

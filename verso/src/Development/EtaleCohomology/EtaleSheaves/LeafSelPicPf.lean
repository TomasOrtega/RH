import Development.EtaleCohomology.EtaleSheaves.LeafPicCut

noncomputable section
open nonZeroDivisors IsDedekindDomain

namespace LateralTheory.E.LeafSelPicPf
open LateralTheory.E.LeafPicCut

/- English proof (translation)
Establish `hx0 : (x : FractionalIdeal B⁰ (FractionRing B)) ≠ 0` using `x.ne_zero`. Establish `hc : ∀ v : HeightOneSpectrum B, FractionalIdeal.count (FractionRing B) v (x : FractionalIdeal B⁰ (FractionRing B)) = 0`. Introduce `v`. Establish `h1` using `FractionalIdeal.count_pow (FractionRing B) v q (x : FractionalIdeal B⁰ (FractionRing B))`. Rewrite `h1` using `[← Units.val_pow_eq_pow_val, h, Units.val_one, FractionalIdeal.count_one]`.

Establish `hq' : (q : ℤ) ≠ 0` using `by exact_mod_cast hq`. Conclude with `(mul_eq_zero.mp h1.symm).resolve_left hq'`. Use `ext1`. Rewrite using `[← FractionalIdeal.finprod_heightOneSpectrum_factorization' (FractionRing B) hx0]`. Simplify using `[hc]`.
-/
lemma units_torsionFree {B : Type} [CommRing B] [IsDedekindDomain B] {q : ℕ} (hq : q ≠ 0)
    (x : (FractionalIdeal B⁰ (FractionRing B))ˣ) (h : x ^ q = 1) : x = 1 := by
  have hx0 : (x : FractionalIdeal B⁰ (FractionRing B)) ≠ 0 := x.ne_zero
  have hc : ∀ v : HeightOneSpectrum B,
      FractionalIdeal.count (FractionRing B) v (x : FractionalIdeal B⁰ (FractionRing B)) = 0 := by
    intro v
    have h1 := FractionalIdeal.count_pow (FractionRing B) v q (x : FractionalIdeal B⁰ (FractionRing B))
    rw [← Units.val_pow_eq_pow_val, h, Units.val_one, FractionalIdeal.count_one] at h1
    have hq' : (q : ℤ) ≠ 0 := by exact_mod_cast hq
    exact (mul_eq_zero.mp h1.symm).resolve_left hq'
  ext1
  rw [← FractionalIdeal.finprod_heightOneSpectrum_factorization' (FractionRing B) hx0]
  simp [hc]

/- English proof (translation)
Use `revert hc`. Use `ClassGroup.induction (R := B) (FractionRing B) (fun I hc => ?_) c` and prove the remaining obligations. Use `⟨I, ?_⟩` and prove the remaining obligations. Establish `h1 : ClassGroup.mk (FractionRing B) (I ^ q) = ClassGroup.mk (FractionRing B) 1`. Rewrite using `[map_pow, hc, map_one]`.

Take `⟨x, hx⟩` from `ClassGroup.mk_eq_mk.mp h1`. Use `⟨x⁻¹, rfl, ?_⟩` and prove the remaining obligations. Rewrite using `[map_inv, inv_eq_iff_mul_eq_one, mul_comm, hx]`.
-/
lemma exists_rep {B : Type} [CommRing B] [IsDedekindDomain B] (q : ℕ) (c : ClassGroup B) (hc : c ^ q = 1) :
    ∃ (I : (FractionalIdeal B⁰ (FractionRing B))ˣ) (f : (FractionRing B)ˣ),
      ClassGroup.mk (FractionRing B) I = c ∧ toPrincipalIdeal B (FractionRing B) f = I ^ q := by
  revert hc
  refine ClassGroup.induction (R := B) (FractionRing B) (fun I hc => ?_) c
  · refine ⟨I, ?_⟩
    have h1 : ClassGroup.mk (FractionRing B) (I ^ q) = ClassGroup.mk (FractionRing B) 1 := by
      rw [map_pow, hc, map_one]
    obtain ⟨x, hx⟩ := ClassGroup.mk_eq_mk.mp h1
    refine ⟨x⁻¹, rfl, ?_⟩
    rw [map_inv, inv_eq_iff_mul_eq_one, mul_comm, hx]

/- English proof (translation)
Introduce `B _ _ q _ hfin`. Establish `hex` using `fun c : {c : ClassGroup B // c ^ q = 1} => exists_rep q c.1 c.2`. Use `choose I f hI hf using hex`. Establish `hsel : ∀ c, f c ∈ sel B q` using `fun c => by`. Simplify using `only [sel, Subgroup.mem_comap, MonoidHom.mem_range]`.

Conclude with `⟨I c, by rw [hf c]; rfl⟩`. Set `φ : {c : ClassGroup B // c ^ q = 1} → selQ B q` to `fun c => QuotientGroup.mk ⟨f c, hsel c⟩`. Use `Finite.of_injective φ ?_` and prove the remaining obligations. Introduce `c d hcd`. Establish `h1` using `QuotientGroup.eq.mp hcd`.

Rewrite `h1` using `[Subgroup.mem_subgroupOf, MonoidHom.mem_range]`. Take `⟨u, hu⟩` from `h1`. Simplify using `only [powMonoidHom_apply, Subgroup.coe_mul, Subgroup.coe_inv] at hu`. Establish `hx : ((I c)⁻¹ * I d * (toPrincipalIdeal B (FractionRing B) u)⁻¹) ^ q = 1`. Rewrite using `[mul_pow, mul_pow, inv_pow, inv_pow, ← map_pow, hu, ← hf c, ← hf d, map_mul, map_inv]`.

Use `group`. Establish `h2` using `units_torsionFree (NeZero.ne q) _ hx`. Apply `Subtype.ext` to reduce the goal to its premises. Rewrite using `[← hI c, ← hI d]`. Use `ClassGroup.mk_eq_mk.mpr ⟨u, ?_⟩` and prove the remaining obligations.

Rewrite `h2` using `[mul_inv_eq_one, inv_mul_eq_iff_eq_mul]`. Conclude with `h2.symm`.
-/
theorem LeafSelPic_of : LeafSelPic := by
  intro B _ _ q _ hfin
  classical
  have hex := fun c : {c : ClassGroup B // c ^ q = 1} => exists_rep q c.1 c.2
  choose I f hI hf using hex
  have hsel : ∀ c, f c ∈ sel B q := fun c => by
    simp only [sel, Subgroup.mem_comap, MonoidHom.mem_range]
    exact ⟨I c, by rw [hf c]; rfl⟩
  let φ : {c : ClassGroup B // c ^ q = 1} → selQ B q := fun c => QuotientGroup.mk ⟨f c, hsel c⟩
  refine Finite.of_injective φ ?_
  intro c d hcd
  have h1 := QuotientGroup.eq.mp hcd
  rw [Subgroup.mem_subgroupOf, MonoidHom.mem_range] at h1
  obtain ⟨u, hu⟩ := h1
  simp only [powMonoidHom_apply, Subgroup.coe_mul, Subgroup.coe_inv] at hu
  have hx : ((I c)⁻¹ * I d * (toPrincipalIdeal B (FractionRing B) u)⁻¹) ^ q = 1 := by
    rw [mul_pow, mul_pow, inv_pow, inv_pow, ← map_pow, hu, ← hf c, ← hf d, map_mul, map_inv]
    group
  have h2 := units_torsionFree (NeZero.ne q) _ hx
  apply Subtype.ext
  rw [← hI c, ← hI d]
  refine ClassGroup.mk_eq_mk.mpr ⟨u, ?_⟩
  rw [mul_inv_eq_one, inv_mul_eq_iff_eq_mul] at h2
  exact h2.symm

end LateralTheory.E.LeafSelPicPf

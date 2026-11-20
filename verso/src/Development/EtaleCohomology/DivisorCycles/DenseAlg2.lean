import Development.EtaleCohomology.DivisorCycles.CycleCount

open Matrix Polynomial PositivityTheory.AutomorphicGaloisHodgeTate.Div

namespace LateralTheory.DivDb.DenseAlg₂
open LateralTheory.DivDb

variable {C : Type} [Field C]

/- English proof (translation)
The claim follows from `| 0 => by simp | k + 1 => by rw [pow_succ, pow_succ, Matrix.mul_assoc, h, ← Matrix.mul_assoc, pow_intertwine y z T h k, Matrix.mul_assoc]`.
-/
theorem pow_intertwine {N n : ℕ} (y : Mat C N) (z : Mat C n) (T : Matrix (Fin N) (Fin n) C)
    (h : y * T = T * z) : ∀ k : ℕ, y ^ k * T = T * z ^ k
  | 0 => by simp
  | k + 1 => by
    rw [pow_succ, pow_succ, Matrix.mul_assoc, h, ← Matrix.mul_assoc, pow_intertwine y z T h k,
      Matrix.mul_assoc]

/- English proof (translation)
Rewrite using `[aeval_eq_sum_range, aeval_eq_sum_range, Matrix.sum_mul, Matrix.mul_sum]`. Use `Finset.sum_congr rfl fun k _ => ?_` and prove the remaining obligations. Rewrite using `[Matrix.smul_mul, Matrix.mul_smul, pow_intertwine y z T h k]`.
-/
theorem aeval_intertwine {N n : ℕ} (y : Mat C N) (z : Mat C n) (T : Matrix (Fin N) (Fin n) C)
    (h : y * T = T * z) (q : C[X]) : aeval y q * T = T * aeval z q := by
  rw [aeval_eq_sum_range, aeval_eq_sum_range, Matrix.sum_mul, Matrix.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Matrix.smul_mul, Matrix.mul_smul, pow_intertwine y z T h k]

/- English proof (translation)
Establish `hq0 : q ≠ 0` using `hm.ne_zero`. Establish `hnd : ((Finset.univ : Finset (Fin n)).val.map l).Nodup` using `Multiset.Nodup.map hl Finset.univ.nodup`. Establish `hle : (Finset.univ : Finset (Fin n)).val.map l ≤ q.roots` using `(Multiset.le_iff_subset hnd).2 fun a ha => by`. Take `⟨j, -, rfl⟩` from `Multiset.mem_map.1 ha`. Conclude with `(mem_roots hq0).2 (hr j)`.

Establish `hcs : Multiset.card ((Finset.univ : Finset (Fin n)).val.map l) = n` using `by simp`. Establish `heq : (Finset.univ : Finset (Fin n)).val.map l = q.roots` using `Multiset.eq_of_le_of_card_le hle (by rw [hcs, ← hd]; exact card_roots' q)`. Establish `hcard : Multiset.card q.roots = q.natDegree` using `by rw [← heq, hcs, hd]`. Establish `hprod` using `prod_multiset_X_sub_C_of_monic_of_roots_card_eq hm hcard`. Rewrite `hprod` using `[← heq, Multiset.map_map]`.

Establish `e : (∏ j, (X - Polynomial.C (l j))) = q` using `by rw [← hprod, Finset.prod_eq_multiset_prod]; rfl`. Conclude with `e ▸ separable_prod_X_sub_C_iff.2 hl`.
-/
theorem sep_of_roots {n : ℕ} (q : C[X]) (hm : q.Monic) (hd : q.natDegree = n) (l : Fin n → C)
    (hl : Function.Injective l) (hr : ∀ j, q.IsRoot (l j)) : q.Separable := by
  classical
  have hq0 : q ≠ 0 := hm.ne_zero
  have hnd : ((Finset.univ : Finset (Fin n)).val.map l).Nodup := Multiset.Nodup.map hl Finset.univ.nodup
  have hle : (Finset.univ : Finset (Fin n)).val.map l ≤ q.roots := (Multiset.le_iff_subset hnd).2 fun a ha => by
    obtain ⟨j, -, rfl⟩ := Multiset.mem_map.1 ha
    exact (mem_roots hq0).2 (hr j)
  have hcs : Multiset.card ((Finset.univ : Finset (Fin n)).val.map l) = n := by simp
  have heq : (Finset.univ : Finset (Fin n)).val.map l = q.roots :=
    Multiset.eq_of_le_of_card_le hle (by rw [hcs, ← hd]; exact card_roots' q)
  have hcard : Multiset.card q.roots = q.natDegree := by rw [← heq, hcs, hd]
  have hprod := prod_multiset_X_sub_C_of_monic_of_roots_card_eq hm hcard
  rw [← heq, Multiset.map_map] at hprod
  have e : (∏ j, (X - Polynomial.C (l j))) = q := by rw [← hprod, Finset.prod_eq_multiset_prod]; rfl
  exact e ▸ separable_prod_X_sub_C_iff.2 hl

/- English proof (translation)
Establish `h1 : l ∈ spectrum C y` using `Matrix.mem_spectrum_of_isRoot_charpoly hl`. Establish `h2` using `spectrum.subset_polynomial_aeval y q ⟨l, h1, rfl⟩`. Rewrite `h2` using `[hq, spectrum.mem_iff, sub_zero]`. Assume the negation of the conclusion as `hne`. Conclude with `h2 ((IsUnit.mk0 (q.eval l) hne).map (algebraMap C (Mat C N)))`.
-/
theorem isRoot_of_aeval {N : ℕ} (y : Mat C N) (q : C[X]) (hq : aeval y q = 0) (l : C)
    (hl : y.charpoly.IsRoot l) : q.IsRoot l := by
  have h1 : l ∈ spectrum C y := Matrix.mem_spectrum_of_isRoot_charpoly hl
  have h2 := spectrum.subset_polynomial_aeval y q ⟨l, h1, rfl⟩
  rw [hq, spectrum.mem_iff, sub_zero] at h2
  by_contra hne
  exact h2 ((IsUnit.mk0 (q.eval l) hne).map (algebraMap C (Mat C N)))

/- English proof (translation)
Introduce `Γ C _ _ _ N n ρ r A B hSub U g m hm hE`. Take `⟨hBA, hint, hspan⟩` from `hSub`. Establish `hr : ∀ h : Γ, B * (ρ h : Mat C N) * A = (r h : Mat C n)` using `fun h => by`. Rewrite using `[Matrix.mul_assoc, hint h, ← Matrix.mul_assoc, hBA, Matrix.one_mul]`. Establish `hgu : ∀ u : Γ, (ρ g : Mat C N) * (ρ u : Mat C N) = (ρ (g * u) : Mat C N)` using `fun u => by`.

Rewrite using `[map_mul, Units.val_mul]`. Assume the negation of the conclusion as `hno`. Use `push Not at hno`. Take `⟨f, hf⟩` from `hSP C n`. Set `φ : Mat C N →ₗ[C] Mat C n` to `{ toFun := fun x => B * (ρ g : Mat C N) * x * A map_add' := fun x y => by simp [Matrix.mul_add, Matrix.add_mul] map_smul' := fun c x => by simp [Matrix.mul_smul, Matrix.smul_mul] }`.

Take `⟨f', hf', -⟩` from `hCh C N n φ f`. Establish `hz : ¬ (φ m).charpoly.Separable`. Rewrite using `[hf, not_not, ← hf']`. Use `hm f' fun x hx => ?_` and prove the remaining obligations. Take `⟨u, hu, rfl⟩` from `Submonoid.mem_map.1 hx`.

Rewrite using `[hf']`. Establish `hφu : φ (((Units.coeHom (Mat C N)).comp ρ) u) = (r (g * u) : Mat C n)` using `by show B * (ρ g : Mat C N) * (ρ u : Mat C N) * A = _`. Rewrite using `[Matrix.mul_assoc B, hgu, hr]`. Rewrite using `[hφu]`. Assume the negation of the conclusion as `h`.

Conclude with `hno u hu ((hf _).2 h)`. Establish `hyT : ∀ T : Matrix (Fin N) (Fin n) C, (∀ h, (ρ h : Mat C N) * T = T * (r h : Mat C n)) → ((ρ g : Mat C N) * m) * T = T * φ m`. Introduce `T hT`. Set `ψ : Mat C N →ₗ[C] Mat C N` to `{ toFun := fun x => ((ρ g : Mat C N) * x * T - T * (B * (ρ g : Mat C N) * x * A)) * B map_add' := fun x y => by`. Simplify using `only [Matrix.mul_add, Matrix.add_mul, Matrix.sub_mul]`.

Normalize the expressions using the abelian group laws. Use the proof step `map_smul' := fun c x => by`. Simplify using `only [Matrix.mul_smul, Matrix.smul_mul, Matrix.sub_mul, RingHom.id_apply, smul_sub] }`. Establish `hψ : ψ m = 0`. Use extensionality with `i j`.

Take `⟨f2, hf2, -⟩` from `hCh C N N ψ (MvPolynomial.X (i, j))`. Establish `h0 : ev m f2 = 0`. Use `hm f2 fun x hx => ?_` and prove the remaining obligations. Take `⟨u, hu, rfl⟩` from `Submonoid.mem_map.1 hx`. Rewrite using `[hf2]`.

Establish `hψu : ψ (((Units.coeHom (Mat C N)).comp ρ) u) = 0` using `by show (((ρ g : Mat C N) * (ρ u : Mat C N) * T - T * (B * (ρ g : Mat C N) * (ρ u : Mat C N) * A)) * B) = 0`. Rewrite using `[Matrix.mul_assoc B, hgu, hr, hT, sub_self, Matrix.zero_mul]`. Rewrite using `[hψu]`. Simplify using `[ev]`. Rewrite `h0` using `[hf2]`.

Simplify `h0` using `[ev]`. Establish `h2 : ((ρ g : Mat C N) * m * T - T * φ m) * B * A = 0`. Establish `e : ψ m = ((ρ g : Mat C N) * m * T - T * φ m) * B` using `rfl`. Rewrite using `[← e, hψ, Matrix.zero_mul]`. Rewrite `h2` using `[Matrix.mul_assoc, hBA, Matrix.mul_one]`.

Conclude with `sub_eq_zero.1 h2`. Establish `hqy : aeval ((ρ g : Mat C N) * m) (φ m).charpoly = 0`. Apply `hspan` to reduce the goal to its premises. Introduce `T hT`. Rewrite using `[aeval_intertwine _ _ T (hyT T hT), Matrix.aeval_self_charpoly, Matrix.mul_zero]`.

Take `⟨l, hl, hlr⟩` from `hE`. Conclude with `hz (sep_of_roots _ (Matrix.charpoly_monic _) (by simp [Matrix.charpoly_natDegree_eq_dim]) l hl fun j => isRoot_of_aeval _ _ hqy (l j) (hlr j))`.
-/
theorem DenseAlg_of (hCh : Chain) (hSP : SepPoly) : DenseAlg := by
  intro Γ C _ _ _ N n ρ r A B hSub U g m hm hE
  obtain ⟨hBA, hint, hspan⟩ := hSub
  have hr : ∀ h : Γ, B * (ρ h : Mat C N) * A = (r h : Mat C n) := fun h => by
    rw [Matrix.mul_assoc, hint h, ← Matrix.mul_assoc, hBA, Matrix.one_mul]
  have hgu : ∀ u : Γ, (ρ g : Mat C N) * (ρ u : Mat C N) = (ρ (g * u) : Mat C N) := fun u => by
    rw [map_mul, Units.val_mul]
  by_contra hno
  push Not at hno
  obtain ⟨f, hf⟩ := hSP C n
  let φ : Mat C N →ₗ[C] Mat C n :=
    { toFun := fun x => B * (ρ g : Mat C N) * x * A
      map_add' := fun x y => by simp [Matrix.mul_add, Matrix.add_mul]
      map_smul' := fun c x => by simp [Matrix.mul_smul, Matrix.smul_mul] }
  obtain ⟨f', hf', -⟩ := hCh C N n φ f
  have hz : ¬ (φ m).charpoly.Separable := by
    rw [hf, not_not, ← hf']
    refine hm f' fun x hx => ?_
    obtain ⟨u, hu, rfl⟩ := Submonoid.mem_map.1 hx
    rw [hf']
    have hφu : φ (((Units.coeHom (Mat C N)).comp ρ) u) = (r (g * u) : Mat C n) := by
      show B * (ρ g : Mat C N) * (ρ u : Mat C N) * A = _
      rw [Matrix.mul_assoc B, hgu, hr]
    rw [hφu]
    by_contra h
    exact hno u hu ((hf _).2 h)
  have hyT : ∀ T : Matrix (Fin N) (Fin n) C, (∀ h, (ρ h : Mat C N) * T = T * (r h : Mat C n)) →
      ((ρ g : Mat C N) * m) * T = T * φ m := by
    intro T hT
    let ψ : Mat C N →ₗ[C] Mat C N :=
      { toFun := fun x => ((ρ g : Mat C N) * x * T - T * (B * (ρ g : Mat C N) * x * A)) * B
        map_add' := fun x y => by
          simp only [Matrix.mul_add, Matrix.add_mul, Matrix.sub_mul]; abel
        map_smul' := fun c x => by
          simp only [Matrix.mul_smul, Matrix.smul_mul, Matrix.sub_mul, RingHom.id_apply, smul_sub] }
    have hψ : ψ m = 0 := by
      ext i j
      obtain ⟨f2, hf2, -⟩ := hCh C N N ψ (MvPolynomial.X (i, j))
      have h0 : ev m f2 = 0 := by
        refine hm f2 fun x hx => ?_
        obtain ⟨u, hu, rfl⟩ := Submonoid.mem_map.1 hx
        rw [hf2]
        have hψu : ψ (((Units.coeHom (Mat C N)).comp ρ) u) = 0 := by
          show (((ρ g : Mat C N) * (ρ u : Mat C N) * T -
            T * (B * (ρ g : Mat C N) * (ρ u : Mat C N) * A)) * B) = 0
          rw [Matrix.mul_assoc B, hgu, hr, hT, sub_self, Matrix.zero_mul]
        rw [hψu]; simp [ev]
      rw [hf2] at h0
      simpa [ev] using h0
    have h2 : ((ρ g : Mat C N) * m * T - T * φ m) * B * A = 0 := by
      have e : ψ m = ((ρ g : Mat C N) * m * T - T * φ m) * B := rfl
      rw [← e, hψ, Matrix.zero_mul]
    rw [Matrix.mul_assoc, hBA, Matrix.mul_one] at h2
    exact sub_eq_zero.1 h2
  have hqy : aeval ((ρ g : Mat C N) * m) (φ m).charpoly = 0 := by
    apply hspan
    intro T hT
    rw [aeval_intertwine _ _ T (hyT T hT), Matrix.aeval_self_charpoly, Matrix.mul_zero]
  obtain ⟨l, hl, hlr⟩ := hE
  exact hz (sep_of_roots _ (Matrix.charpoly_monic _) (by simp [Matrix.charpoly_natDegree_eq_dim]) l hl
    fun j => isRoot_of_aeval _ _ hqy (l j) (hlr j))

end LateralTheory.DivDb.DenseAlg₂

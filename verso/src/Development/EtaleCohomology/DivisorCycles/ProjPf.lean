import Development.EtaleCohomology.DivisorCycles.CycleCount

open Matrix Polynomial PositivityTheory.AutomorphicGaloisHodgeTate.Div
namespace LateralTheory.DivDb.ProjPf

variable {C : Type} [Field C] {N n : ℕ}

/- English proof (translation)
Establish `h1 : Module.End.HasEigenvalue (Matrix.toLin' X) c` using `(Module.End.hasEigenvalue_iff_isRoot_charpoly _ _).2 (by rw [Matrix.charpoly_toLin']; exact h)`. Rewrite using `[← Matrix.minpoly_toLin']`. Conclude with `Module.End.hasEigenvalue_iff_isRoot.1 h1`.
-/
theorem root_minpoly (X : LateralTheory.DivDb.Mat C N) (c : C) (h : X.charpoly.IsRoot c) :
    (minpoly C X).IsRoot c := by
  have h1 : Module.End.HasEigenvalue (Matrix.toLin' X) c :=
    (Module.End.hasEigenvalue_iff_isRoot_charpoly _ _).2 (by rw [Matrix.charpoly_toLin']; exact h)
  rw [← Matrix.minpoly_toLin']
  exact Module.End.hasEigenvalue_iff_isRoot.1 h1

/- English proof (translation)
Apply `Finset.prod_dvd_of_coprime` to reduce the goal to its premises. Conclude with `fun a _ b _ hab => Polynomial.pairwise_coprime_X_sub_C he hab`. Introduce `k _`. Conclude with `Polynomial.dvd_iff_isRoot.2 (hf k)`.
-/
theorem prod_dvd (e : Fin n → C) (he : Function.Injective e) (f : C[X]) (hf : ∀ k, f.eval (e k) = 0) :
    (∏ k, (X - Polynomial.C (e k))) ∣ f := by
  apply Finset.prod_dvd_of_coprime
  · exact fun a _ b _ hab => Polynomial.pairwise_coprime_X_sub_C he hab
  · intro k _; exact Polynomial.dvd_iff_isRoot.2 (hf k)

/- English proof (translation)
Take `⟨q, hq0, hqd, hq⟩` from `hD`. Establish `hint : IsIntegral C X` using `Matrix.isIntegral X`. Establish `hmon : (minpoly C X).Monic` using `minpoly.monic hint`. Establish `hdvd : (∏ k, (Polynomial.X - Polynomial.C (e k))) ∣ minpoly C X` using `prod_dvd e he _ (fun k => root_minpoly X _ (hr k))`. Establish `hPm : (∏ k, (Polynomial.X - Polynomial.C (e k))).Monic` using `monic_prod_of_monic _ _ (fun k _ => monic_X_sub_C _)`.

Establish `hdeg : (minpoly C X).natDegree ≤ n`. Use `Polynomial.natDegree_le_of_dvd (minpoly.dvd C X hq) hq0` as an intermediate fact. Use linear arithmetic over natural numbers and integers. Apply `Polynomial.eq_of_monic_of_dvd_of_natDegree_le hPm hmon hdvd` to reduce the goal to its premises. Rewrite using `[natDegree_prod_of_monic _ _ (fun k _ => monic_X_sub_C _)]`.

Simplify using `only [natDegree_X_sub_C, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul, mul_one]`. Conclude with `hdeg`.
-/
theorem minpoly_eq (X : LateralTheory.DivDb.Mat C N) (e : Fin n → C) (he : Function.Injective e)
    (hD : LateralTheory.DivDb.Deg n X) (hr : ∀ i, X.charpoly.IsRoot (e i)) :
    minpoly C X = ∏ k, (Polynomial.X - Polynomial.C (e k)) := by
  obtain ⟨q, hq0, hqd, hq⟩ := hD
  have hint : IsIntegral C X := Matrix.isIntegral X
  have hmon : (minpoly C X).Monic := minpoly.monic hint
  have hdvd : (∏ k, (Polynomial.X - Polynomial.C (e k))) ∣ minpoly C X :=
    prod_dvd e he _ (fun k => root_minpoly X _ (hr k))
  have hPm : (∏ k, (Polynomial.X - Polynomial.C (e k))).Monic :=
    monic_prod_of_monic _ _ (fun k _ => monic_X_sub_C _)
  have hdeg : (minpoly C X).natDegree ≤ n := by
    have := Polynomial.natDegree_le_of_dvd (minpoly.dvd C X hq) hq0
    omega
  apply Polynomial.eq_of_monic_of_dvd_of_natDegree_le hPm hmon hdvd
  rw [natDegree_prod_of_monic _ _ (fun k _ => monic_X_sub_C _)]
  simp only [natDegree_X_sub_C, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul, mul_one]
  exact hdeg

/- English proof (translation)
Use `split_ifs with h`. Substitute `h` using the available equality. Conclude with `Lagrange.eval_basis_self he.injOn (Finset.mem_univ _)`. Conclude with `Lagrange.eval_basis_of_ne (Ne.symm h) (Finset.mem_univ _)`.
-/
theorem evb (e : Fin n → C) (he : Function.Injective e) (i k : Fin n) :
    (Lagrange.basis Finset.univ e i).eval (e k) = if k = i then 1 else 0 := by
  split_ifs with h
  · subst h; exact Lagrange.eval_basis_self he.injOn (Finset.mem_univ _)
  · exact Lagrange.eval_basis_of_ne (Ne.symm h) (Finset.mem_univ _)

/- English proof (translation)
Rewrite using `[← minpoly.dvd_iff, minpoly_eq X e he hD hr]`. Conclude with `prod_dvd e he f hf`.
-/
theorem vanish (X : LateralTheory.DivDb.Mat C N) (e : Fin n → C) (he : Function.Injective e)
    (hD : LateralTheory.DivDb.Deg n X) (hr : ∀ i, X.charpoly.IsRoot (e i)) (f : C[X])
    (hf : ∀ k, f.eval (e k) = 0) : aeval X f = 0 := by
  rw [← minpoly.dvd_iff, minpoly_eq X e he hD hr]
  exact prod_dvd e he f hf

end LateralTheory.DivDb.ProjPf

namespace LateralTheory.DivDb
open LateralTheory.DivDb.ProjPf

/- English proof (translation)
Introduce `C _ N n X e he hD hr`. Use `set b : Fin n → C[X] := fun i => Lagrange.basis Finset.univ e i with hb`. Establish `V` using `vanish X e he hD hr`. Use `⟨fun i => aeval X (b i), ⟨⟨⟨fun i => ?_, fun i j hij => ?_⟩, ?_⟩, fun i => ?_⟩, ?_, fun i => ?_⟩` and prove the remaining obligations. Use `show aeval X (b i) * aeval X (b i) = aeval X (b i)`.

Rewrite using `[← sub_eq_zero, ← map_mul, ← map_sub]`. Apply `V` to reduce the goal to its premises. Introduce `k`. Simplify using `only [hb, eval_sub, eval_mul, evb e he]`. Apply the tactic sequence `split_ifs <;> simp`.

Use `show aeval X (b i) * aeval X (b j) = 0`. Rewrite using `[← map_mul]`. Apply `V` to reduce the goal to its premises. Introduce `k`. Simplify using `only [hb, eval_mul, evb e he]`.

Apply the tactic sequence `split_ifs with h1 h2 <;> simp_all`. Use `show ∑ i, aeval X (b i) = 1`. Establish `h : aeval X (∑ i, b i - 1) = 0`. Apply `V` to reduce the goal to its premises. Introduce `k`.

Simplify using `only [hb, eval_sub, eval_finsetSum, evb e he, eval_one]`. Simplify using the standard rewrite rules. Rewrite `h` using `[map_sub, map_one, map_sum, sub_eq_zero]`. Conclude with `h`. Introduce `h0`.

Establish `h1 : minpoly C X ∣ b i` using `(minpoly.dvd_iff).2 h0`. Rewrite `h1` using `[minpoly_eq X e he hD hr]`. Establish `hne : b i ≠ 0` using `Lagrange.basis_ne_zero he.injOn (Finset.mem_univ _)`. Establish `h2` using `Polynomial.natDegree_le_of_dvd h1 hne`. Rewrite `h2` using `[natDegree_prod_of_monic _ _ (fun k _ => monic_X_sub_C _)]`.

Establish `h3 : (b i).natDegree = n - 1`. Simplify using `only [hb]`. Rewrite using `[Lagrange.natDegree_basis he.injOn (Finset.mem_univ _)]`. Simplify using the standard rewrite rules. Simplify using `only [natDegree_X_sub_C, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul, mul_one] at h2`.

Use `i.pos` as an intermediate fact. Use linear arithmetic over natural numbers and integers. Establish `: aeval X (Polynomial.X - ∑ i, Polynomial.C (e i) * b i) = 0`. Apply `V` to reduce the goal to its premises. Introduce `k`.

Simplify using `only [hb, eval_sub, eval_X, eval_finsetSum, eval_mul, eval_C, evb e he]`. Simplify using the standard rewrite rules. Rewrite `this` using `[map_sub, aeval_X, map_sum, sub_eq_zero]`. Use `this.trans (Finset.sum_congr rfl fun i _ => ?_)` and prove the remaining obligations. Rewrite using `[map_mul, aeval_C, Algebra.smul_def]`.

Conclude with `Polynomial.aeval_mem_adjoin_singleton C _`.
-/
theorem Proj_of : Proj := by
  intro C _ N n X e he hD hr
  classical
  set b : Fin n → C[X] := fun i => Lagrange.basis Finset.univ e i with hb
  have V := vanish X e he hD hr
  refine ⟨fun i => aeval X (b i), ⟨⟨⟨fun i => ?_, fun i j hij => ?_⟩, ?_⟩, fun i => ?_⟩, ?_, fun i => ?_⟩
  · show aeval X (b i) * aeval X (b i) = aeval X (b i)
    rw [← sub_eq_zero, ← map_mul, ← map_sub]
    apply V; intro k
    simp only [hb, eval_sub, eval_mul, evb e he]
    split_ifs <;> simp
  · show aeval X (b i) * aeval X (b j) = 0
    rw [← map_mul]
    apply V; intro k
    simp only [hb, eval_mul, evb e he]
    split_ifs with h1 h2 <;> simp_all
  · show ∑ i, aeval X (b i) = 1
    have h : aeval X (∑ i, b i - 1) = 0 := by
      apply V; intro k
      simp only [hb, eval_sub, eval_finsetSum, evb e he, eval_one]
      simp
    rw [map_sub, map_one, map_sum, sub_eq_zero] at h
    exact h
  · intro h0
    have h1 : minpoly C X ∣ b i := (minpoly.dvd_iff).2 h0
    rw [minpoly_eq X e he hD hr] at h1
    have hne : b i ≠ 0 := Lagrange.basis_ne_zero he.injOn (Finset.mem_univ _)
    have h2 := Polynomial.natDegree_le_of_dvd h1 hne
    rw [natDegree_prod_of_monic _ _ (fun k _ => monic_X_sub_C _)] at h2
    have h3 : (b i).natDegree = n - 1 := by
      simp only [hb]
      rw [Lagrange.natDegree_basis he.injOn (Finset.mem_univ _)]
      simp
    simp only [natDegree_X_sub_C, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul,
      mul_one] at h2
    have := i.pos
    omega
  · have : aeval X (Polynomial.X - ∑ i, Polynomial.C (e i) * b i) = 0 := by
      apply V; intro k
      simp only [hb, eval_sub, eval_X, eval_finsetSum, eval_mul, eval_C, evb e he]
      simp
    rw [map_sub, aeval_X, map_sum, sub_eq_zero] at this
    refine this.trans (Finset.sum_congr rfl fun i _ => ?_)
    rw [map_mul, aeval_C, Algebra.smul_def]
  · exact Polynomial.aeval_mem_adjoin_singleton C _

end LateralTheory.DivDb

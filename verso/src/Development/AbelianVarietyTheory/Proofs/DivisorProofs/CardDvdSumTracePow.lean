import Mathlib
import Formalism.FlagUnipotentLattices.MemOfOrthogonalAnisotropic
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.CardFiniteSubgroupGLIntDvd

namespace GlobalTheory.MinkowskiExact

open Polynomial

/- English proof (translation)
Set `σ : H →* Matrix ι ι ℚ` to `(Int.castRingHom ℚ).mapMatrix.toMonoidHom.comp ρ`. Establish `hc : (Fintype.card H : ℚ) ≠ 0` using `by exact_mod_cast Fintype.card_ne_zero`. Establish `h1 : ∀ h, σ h * ∑ g, σ g = ∑ g, σ g`. Introduce `h`. Rewrite using `[Finset.mul_sum]`.

Conclude with `Fintype.sum_equiv (Equiv.mulLeft h) _ _ fun g => (map_mul σ h g).symm`. Establish `h2 : (∑ g, σ g) * ∑ g, σ g = (Fintype.card H : ℚ) • ∑ g, σ g`. Rewrite using `[Finset.sum_mul, Finset.sum_congr rfl fun g _ => h1 g, Finset.sum_const, Finset.card_univ, Nat.cast_smul_eq_nsmul]`. Set `e : Matrix ι ι ℚ` to `(Fintype.card H : ℚ)⁻¹ • ∑ g, σ g`. Establish `he : e * e = e`.

Simplify using `only [e]`. Rewrite using `[smul_mul_smul_comm, h2, smul_smul, mul_assoc, inv_mul_cancel₀ hc, mul_one]`. Establish `hi : IsIdempotentElem (Matrix.toLin' e)`. Express the relevant statement in the definitionally equal form `Matrix.toLin' e ∘ₗ Matrix.toLin' e = Matrix.toLin' e`. Rewrite using `[← Matrix.toLin'_mul, he]`.

Establish `ht` using `(LinearMap.IsIdempotentElem.isProj_range _ hi).trace`. Rewrite `ht` using `[Matrix.trace_toLin'_eq]`. Use `⟨Module.finrank ℚ (LinearMap.range (Matrix.toLin' e)), ?_⟩` and prove the remaining obligations. Establish `h3 : ∀ g, (σ g).trace = ((ρ g).trace : ℚ)`. Introduce `g`.

Simplify using `[σ, Matrix.trace]`. Apply `Int.cast_injective (α := ℚ)` to reduce the goal to its premises. Use `push_cast`. Rewrite using `[← ht]`. Simplify using `only [e]`.

Rewrite using `[Matrix.trace_smul, smul_eq_mul, ← mul_assoc, mul_inv_cancel₀ hc, one_mul, Matrix.trace_sum]`. Conclude with `Finset.sum_congr rfl fun g _ => (h3 g).symm`.
-/
theorem card_dvd_sum_trace {H ι : Type} [Group H] [Fintype H] [Fintype ι] [DecidableEq ι]
    (ρ : H →* Matrix ι ι ℤ) : (Fintype.card H : ℤ) ∣ ∑ g, (ρ g).trace := by
  let σ : H →* Matrix ι ι ℚ := (Int.castRingHom ℚ).mapMatrix.toMonoidHom.comp ρ
  have hc : (Fintype.card H : ℚ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have h1 : ∀ h, σ h * ∑ g, σ g = ∑ g, σ g := by
    intro h
    rw [Finset.mul_sum]
    exact Fintype.sum_equiv (Equiv.mulLeft h) _ _ fun g => (map_mul σ h g).symm
  have h2 : (∑ g, σ g) * ∑ g, σ g = (Fintype.card H : ℚ) • ∑ g, σ g := by
    rw [Finset.sum_mul, Finset.sum_congr rfl fun g _ => h1 g, Finset.sum_const, Finset.card_univ,
      Nat.cast_smul_eq_nsmul]
  let e : Matrix ι ι ℚ := (Fintype.card H : ℚ)⁻¹ • ∑ g, σ g
  have he : e * e = e := by
    simp only [e]
    rw [smul_mul_smul_comm, h2, smul_smul, mul_assoc, inv_mul_cancel₀ hc, mul_one]
  have hi : IsIdempotentElem (Matrix.toLin' e) := by
    change Matrix.toLin' e ∘ₗ Matrix.toLin' e = Matrix.toLin' e
    rw [← Matrix.toLin'_mul, he]
  have ht := (LinearMap.IsIdempotentElem.isProj_range _ hi).trace
  rw [Matrix.trace_toLin'_eq] at ht
  refine ⟨Module.finrank ℚ (LinearMap.range (Matrix.toLin' e)), ?_⟩
  have h3 : ∀ g, (σ g).trace = ((ρ g).trace : ℚ) := by
    intro g
    simp [σ, Matrix.trace]
  apply Int.cast_injective (α := ℚ)
  push_cast
  rw [← ht]
  simp only [e]
  rw [Matrix.trace_smul, smul_eq_mul, ← mul_assoc, mul_inv_cancel₀ hc, one_mul, Matrix.trace_sum]
  exact Finset.sum_congr rfl fun g _ => (h3 g).symm

/- English proof (translation)
Set `τ : H →* Matrix (Fin j → ι) (Fin j → ι) ℤ` to `{ toFun := fun g => Matrix.of fun a b => ∏ i, ρ g (a i) (b i) map_one' := by`. Use extensionality with `a b`. Simplify using `only [map_one, Matrix.of_apply, Matrix.one_apply]`. Rewrite using `[Finset.prod_ite_zero]`. Simplify using `[funext_iff]`.

Use the proof step `map_mul' := fun g h => by`. Use extensionality with `a b`. Simplify using `only [map_mul, Matrix.of_apply, Matrix.mul_apply]`. Rewrite using `[Finset.prod_univ_sum, Fintype.piFinset_univ]`. Conclude with `Finset.sum_congr rfl fun c _ => Finset.prod_mul_distrib }`.

Establish `h` using `card_dvd_sum_trace τ`. Use `h using 2 with g` and compare the differences between its conclusion and the goal. Rewrite using `[Matrix.trace, Fintype.sum_pow]`. Both sides reduce to the same expression.
-/
theorem card_dvd_sum_trace_pow {H ι : Type} [Group H] [Fintype H] [Fintype ι] [DecidableEq ι]
    (ρ : H →* Matrix ι ι ℤ) (j : ℕ) : (Fintype.card H : ℤ) ∣ ∑ g, (ρ g).trace ^ j := by
  let τ : H →* Matrix (Fin j → ι) (Fin j → ι) ℤ :=
    { toFun := fun g => Matrix.of fun a b => ∏ i, ρ g (a i) (b i)
      map_one' := by
        ext a b
        simp only [map_one, Matrix.of_apply, Matrix.one_apply]
        rw [Finset.prod_ite_zero]
        simp [funext_iff]
      map_mul' := fun g h => by
        ext a b
        simp only [map_mul, Matrix.of_apply, Matrix.mul_apply]
        rw [Finset.prod_univ_sum, Fintype.piFinset_univ]
        exact Finset.sum_congr rfl fun c _ => Finset.prod_mul_distrib }
  have h := card_dvd_sum_trace τ
  convert h using 2 with g
  rw [Matrix.trace, Fintype.sum_pow]
  rfl

/- English proof (translation)
Proceed by induction on `f using Polynomial.induction_on' with`. Consider the case `add p q hp hq`. Simplify using `only [eval_add, Finset.sum_add_distrib]`. Conclude with `dvd_add hp hq`. Consider the case `monomial j a`.

Simplify using `only [eval_monomial, ← Finset.mul_sum]`. Conclude with `Dvd.dvd.mul_left (card_dvd_sum_trace_pow ρ j) a`.
-/
theorem card_dvd_sum_eval {H ι : Type} [Group H] [Fintype H] [Fintype ι] [DecidableEq ι]
    (ρ : H →* Matrix ι ι ℤ) (f : ℤ[X]) : (Fintype.card H : ℤ) ∣ ∑ g, f.eval (ρ g).trace := by
  induction f using Polynomial.induction_on' with
  | add p q hp hq =>
    simp only [eval_add, Finset.sum_add_distrib]
    exact dvd_add hp hq
  | monomial j a =>
    simp only [eval_monomial, ← Finset.mul_sum]
    exact Dvd.dvd.mul_left (card_dvd_sum_trace_pow ρ j) a

/- English proof (translation)
Establish `h1 : z ∈ spectrum ℂ A` using `Matrix.mem_spectrum_iff_isRoot_charpoly.2 (isRoot_of_mem_roots hz)`. Use `haveI : Nontrivial (Matrix (Fin n) (Fin n) ℂ) := by`. Assume the negation of the conclusion as `hn`. Rewrite `hn` using `[not_nontrivial_iff_subsingleton]`. Rewrite `h1` using `[spectrum.of_subsingleton]`.

Conclude with `h1`. Establish `h2` using `spectrum.pow_mem_pow A m h1`. Rewrite `h2` using `[h, spectrum.one_eq, Set.mem_singleton_iff]`. Conclude with `Complex.norm_eq_one_of_pow_eq_one h2 hm`.
-/
theorem norm_root {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) {m : ℕ} (hm : m ≠ 0) (h : A ^ m = 1)
    {z : ℂ} (hz : z ∈ A.charpoly.roots) : ‖z‖ = 1 := by
  have h1 : z ∈ spectrum ℂ A :=
    Matrix.mem_spectrum_iff_isRoot_charpoly.2 (isRoot_of_mem_roots hz)
  haveI : Nontrivial (Matrix (Fin n) (Fin n) ℂ) := by
    by_contra hn
    rw [not_nontrivial_iff_subsingleton] at hn
    rw [spectrum.of_subsingleton] at h1
    exact h1
  have h2 := spectrum.pow_mem_pow A m h1
  rw [h, spectrum.one_eq, Set.mem_singleton_iff] at h2
  exact Complex.norm_eq_one_of_pow_eq_one h2 hm

/- English proof (translation)
Rewrite using `[IsAlgClosed.card_roots_eq_natDegree, Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin]`.
-/
theorem card_roots {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) : Multiset.card A.charpoly.roots = n := by
  rw [IsAlgClosed.card_roots_eq_natDegree, Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin]

/- English proof (translation)
Rewrite using `[Matrix.trace_eq_sum_roots_charpoly]`. Use `(norm_multiset_sum_le _).trans ?_` and prove the remaining obligations. Rewrite using `[Multiset.map_congr rfl fun z hz => norm_root A hm h hz]`. Simplify using `[card_roots]`.
-/
theorem norm_trace_le {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) {m : ℕ} (hm : m ≠ 0) (h : A ^ m = 1) :
    ‖A.trace‖ ≤ n := by
  rw [Matrix.trace_eq_sum_roots_charpoly]
  refine (norm_multiset_sum_le _).trans ?_
  rw [Multiset.map_congr rfl fun z hz => norm_root A hm h hz]
  simp [card_roots]

/- English proof (translation)
Break down `Nat.eq_zero_or_pos n with rfl | hn` into its components or cases. Conclude with `Subsingleton.elim _ _`. Rewrite `ht` using `[Matrix.trace_eq_sum_roots_charpoly]`. Establish `hre : ∀ z ∈ A.charpoly.roots, z.re ≤ 1` using `fun z hz => (Complex.re_le_norm z).trans (norm_root A hm h hz).le`. Establish `hs : (A.charpoly.roots.map fun z => 1 - z.re).sum = 0`.

Use `congrArg Complex.re ht` as an intermediate fact. Rewrite using `[Multiset.sum_map_sub]`. Establish `h2` using `map_multiset_sum Complex.reAddGroupHom A.charpoly.roots`. Simplify using `only [Complex.coe_reAddGroupHom] at h2`. Rewrite `this` using `[h2]`.

Simplify using `[card_roots, this]`. Establish `h1 : ∀ z ∈ A.charpoly.roots, z = 1`. Introduce `z hz`. Establish `h0 : 1 - z.re = 0` using `Multiset.all_zero_of_le_zero_le_of_sum_eq_zero (by`. Introduce `x hx`.

Take `⟨w, hw, rfl⟩` from `Multiset.mem_map.1 hx`. Combine the linear relations using `[hre w hw]) hs _ (Multiset.mem_map_of_mem _ hz)`. Establish `h3` using `norm_root A hm h hz`. Establish `h4 : z.re * z.re + z.im * z.im = 1`. Rewrite using `[← Complex.normSq_apply, Complex.normSq_eq_norm_sq, h3]`.

Evaluate the numerical expressions. Establish `h5 : z.re = 1` using `by linarith`. Rewrite `h4` using `[h5]`. Apply `Complex.ext` to reduce the goal to its premises. Simplify using `using h5`.

Simplify using `using h4`. Establish `hch : A.charpoly = (X - C 1) ^ n`. Rewrite using `[(IsAlgClosed.splits A.charpoly).eq_prod_roots_of_monic A.charpoly_monic, Multiset.eq_replicate.2 ⟨card_roots A, h1⟩]`. Simplify using the standard rewrite rules. Establish `hsq : Squarefree (minpoly ℂ A)`.

Establish `hsep : (X ^ m - C 1 : ℂ[X]).Separable` using `separable_X_pow_sub_C 1 (by exact_mod_cast hm) one_ne_zero`. Use `hsep.squarefree.squarefree_of_dvd (minpoly.dvd ℂ A ?_)` and prove the remaining obligations. Simplify using `[h]`. Establish `hd : minpoly ℂ A ∣ X - C 1`. Rewrite using `[← hsq.dvd_pow_iff_dvd hn.ne', ← hch]`.

Conclude with `A.minpoly_dvd_charpoly`. Use `aeval_eq_zero_of_dvd_aeval_eq_zero hd (minpoly.aeval ℂ A)` as an intermediate fact. Simplify `this` using `[sub_eq_zero]`.
-/
theorem eq_one_of_trace {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) {m : ℕ} (hm : m ≠ 0) (h : A ^ m = 1)
    (ht : A.trace = n) : A = 1 := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · exact Subsingleton.elim _ _
  rw [Matrix.trace_eq_sum_roots_charpoly] at ht
  have hre : ∀ z ∈ A.charpoly.roots, z.re ≤ 1 := fun z hz =>
    (Complex.re_le_norm z).trans (norm_root A hm h hz).le
  have hs : (A.charpoly.roots.map fun z => 1 - z.re).sum = 0 := by
    have := congrArg Complex.re ht
    rw [Multiset.sum_map_sub]
    have h2 := map_multiset_sum Complex.reAddGroupHom A.charpoly.roots
    simp only [Complex.coe_reAddGroupHom] at h2
    rw [h2] at this
    simp [card_roots, this]
  have h1 : ∀ z ∈ A.charpoly.roots, z = 1 := by
    intro z hz
    have h0 : 1 - z.re = 0 := Multiset.all_zero_of_le_zero_le_of_sum_eq_zero (by
      intro x hx
      obtain ⟨w, hw, rfl⟩ := Multiset.mem_map.1 hx
      linarith [hre w hw]) hs _ (Multiset.mem_map_of_mem _ hz)
    have h3 := norm_root A hm h hz
    have h4 : z.re * z.re + z.im * z.im = 1 := by
      rw [← Complex.normSq_apply, Complex.normSq_eq_norm_sq, h3]; norm_num
    have h5 : z.re = 1 := by linarith
    rw [h5] at h4
    apply Complex.ext
    · simpa using h5
    · simpa using h4
  have hch : A.charpoly = (X - C 1) ^ n := by
    rw [(IsAlgClosed.splits A.charpoly).eq_prod_roots_of_monic A.charpoly_monic,
      Multiset.eq_replicate.2 ⟨card_roots A, h1⟩]
    simp
  have hsq : Squarefree (minpoly ℂ A) := by
    have hsep : (X ^ m - C 1 : ℂ[X]).Separable :=
      separable_X_pow_sub_C 1 (by exact_mod_cast hm) one_ne_zero
    refine hsep.squarefree.squarefree_of_dvd (minpoly.dvd ℂ A ?_)
    simp [h]
  have hd : minpoly ℂ A ∣ X - C 1 := by
    rw [← hsq.dvd_pow_iff_dvd hn.ne', ← hch]
    exact A.minpoly_dvd_charpoly
  have := aeval_eq_zero_of_dvd_aeval_eq_zero hd (minpoly.aeval ℂ A)
  simpa [sub_eq_zero] using this

/- English proof (translation)
Establish `key : ∀ (k : ℕ) (B : Matrix (Fin n) (Fin n) (ZMod 2)), (B ^ 2 ^ k).trace = B.trace`. Introduce `k B`. Proceed by induction on `k with`. Consider the case `zero => simp`. Consider the case `succ k ih => rw [pow_succ, pow_mul, ZMod.trace_pow_card, ZMod.pow_card, ih]`.

Establish `h1` using `key k ((Int.castRingHom (ZMod 2)).mapMatrix A)`. Rewrite `h1` using `[← map_pow, h, map_one, Matrix.trace_one, Fintype.card_fin]`. Establish `h2 : (((n : ℤ) - A.trace : ℤ) : ZMod 2) = 0`. Use `push_cast`. Rewrite using `[h1]`.

Simplify using `[Matrix.trace]`. Conclude with `(ZMod.intCast_zmod_eq_zero_iff_dvd _ 2).1 h2` after adjusting the coercions.
-/
theorem two_dvd_sub_trace {n : ℕ} (A : Matrix (Fin n) (Fin n) ℤ) {k : ℕ} (h : A ^ 2 ^ k = 1) :
    (2 : ℤ) ∣ n - A.trace := by
  have key : ∀ (k : ℕ) (B : Matrix (Fin n) (Fin n) (ZMod 2)), (B ^ 2 ^ k).trace = B.trace := by
    intro k B
    induction k with
    | zero => simp
    | succ k ih => rw [pow_succ, pow_mul, ZMod.trace_pow_card, ZMod.pow_card, ih]
  have h1 := key k ((Int.castRingHom (ZMod 2)).mapMatrix A)
  rw [← map_pow, h, map_one, Matrix.trace_one, Fintype.card_fin] at h1
  have h2 : (((n : ℤ) - A.trace : ℤ) : ZMod 2) = 0 := by
    push_cast
    rw [h1]
    simp [Matrix.trace]
  exact_mod_cast (ZMod.intCast_zmod_eq_zero_iff_dvd _ 2).1 h2

/- English proof (translation)
Establish `h` using `card_dvd_sum_eval ρ (∏ i ∈ Finset.range n, (X - C ((n : ℤ) - 2 * (i + 1))))`. Rewrite `h` using `[Finset.sum_eq_single (1 : H)]`. Rewrite `h` using `[hk, map_one, Matrix.trace_one, Fintype.card_fin, eval_prod]`. Establish `e : ∏ i ∈ Finset.range n, eval (n : ℤ) (X - C ((n : ℤ) - 2 * (i + 1))) = ((2 ^ n * n.factorial : ℕ) : ℤ)`. Rewrite using `[← Finset.prod_range_add_one_eq_factorial]`.

Use `push_cast`. Rewrite using `[← Finset.card_range n, ← Finset.prod_const, Finset.card_range, ← Finset.prod_mul_distrib]`. Conclude with `Finset.prod_congr rfl fun i _ => by simp`. Rewrite `h` using `[e]`. Conclude with `h` after adjusting the coercions.

Introduce `g _ hg`. Establish `hp : ρ g ^ 2 ^ k = 1` using `by rw [← map_pow, ← hk, pow_card_eq_one, map_one]`. Set `A : Matrix (Fin n) (Fin n) ℂ` to `(Int.castRingHom ℂ).mapMatrix (ρ g)`. Establish `hA : A ^ 2 ^ k = 1` using `by simp only [A]; rw [← map_pow, hp, map_one]`. Establish `hAt : A.trace = ((ρ g).trace : ℂ)` using `by simp [A, Matrix.trace]`.

Establish `h1` using `norm_trace_le A (by positivity) hA`. Rewrite `h1` using `[hAt, Complex.norm_intCast]`. Establish `h1' : |(ρ g).trace| ≤ n` using `by exact_mod_cast h1`. Establish `h2 : (ρ g).trace ≠ n`. Introduce `h2`.

Establish `h3` using `eq_one_of_trace A (by positivity) hA (by rw [hAt, h2]; simp)`. Apply `hg` to reduce the goal to its premises. Apply `hρ` to reduce the goal to its premises. Apply `Matrix.map_injective (f := (Int.castRingHom ℂ : ℤ → ℂ)) Int.cast_injective` to reduce the goal to its premises. Establish `h4 : (ρ g).map (Int.castRingHom ℂ) = 1` using `h3`.

Simplify using `only [h4]`. Conclude with `(Matrix.map_one _ (map_zero _) (map_one _)).symm`. Take `⟨c, hc⟩` from `two_dvd_sub_trace (ρ g) hp`. Take `⟨h5, h6⟩` from `abs_le.1 h1'`. Rewrite using `[eval_prod]`.

Use `Finset.prod_eq_zero (i := (c - 1).toNat) (Finset.mem_range.2 (by omega)) ?_` and prove the remaining obligations. Rewrite using `[eval_sub, eval_X, eval_C]`. Use linear arithmetic over natural numbers and integers. Simplify using the standard rewrite rules.
-/
theorem card_two_group_dvd {H : Type} [Group H] [Fintype H] {n k : ℕ} (ρ : H →* Matrix (Fin n) (Fin n) ℤ)
    (hρ : ∀ g, ρ g = 1 → g = 1) (hk : Fintype.card H = 2 ^ k) : 2 ^ k ∣ 2 ^ n * n.factorial := by
  classical
  have h := card_dvd_sum_eval ρ (∏ i ∈ Finset.range n, (X - C ((n : ℤ) - 2 * (i + 1))))
  rw [Finset.sum_eq_single (1 : H)] at h
  · rw [hk, map_one, Matrix.trace_one, Fintype.card_fin, eval_prod] at h
    have e : ∏ i ∈ Finset.range n, eval (n : ℤ) (X - C ((n : ℤ) - 2 * (i + 1)))
        = ((2 ^ n * n.factorial : ℕ) : ℤ) := by
      rw [← Finset.prod_range_add_one_eq_factorial]
      push_cast
      rw [← Finset.card_range n, ← Finset.prod_const, Finset.card_range, ← Finset.prod_mul_distrib]
      exact Finset.prod_congr rfl fun i _ => by simp
    rw [e] at h
    exact_mod_cast h
  · intro g _ hg
    have hp : ρ g ^ 2 ^ k = 1 := by rw [← map_pow, ← hk, pow_card_eq_one, map_one]
    let A : Matrix (Fin n) (Fin n) ℂ := (Int.castRingHom ℂ).mapMatrix (ρ g)
    have hA : A ^ 2 ^ k = 1 := by simp only [A]; rw [← map_pow, hp, map_one]
    have hAt : A.trace = ((ρ g).trace : ℂ) := by simp [A, Matrix.trace]
    have h1 := norm_trace_le A (by positivity) hA
    rw [hAt, Complex.norm_intCast] at h1
    have h1' : |(ρ g).trace| ≤ n := by exact_mod_cast h1
    have h2 : (ρ g).trace ≠ n := by
      intro h2
      have h3 := eq_one_of_trace A (by positivity) hA (by rw [hAt, h2]; simp)
      apply hg
      apply hρ
      apply Matrix.map_injective (f := (Int.castRingHom ℂ : ℤ → ℂ)) Int.cast_injective
      have h4 : (ρ g).map (Int.castRingHom ℂ) = 1 := h3
      simp only [h4]
      exact (Matrix.map_one _ (map_zero _) (map_one _)).symm
    obtain ⟨c, hc⟩ := two_dvd_sub_trace (ρ g) hp
    obtain ⟨h5, h6⟩ := abs_le.1 h1'
    rw [eval_prod]
    refine Finset.prod_eq_zero (i := (c - 1).toNat) (Finset.mem_range.2 (by omega)) ?_
    rw [eval_sub, eval_X, eval_C]
    omega
  · simp

/- English proof (translation)
Use `haveI := Fact.mk hp`. Establish `hl : Nat.log p (n / (p - 1)) < n + 1` using `Nat.lt_succ_of_le ((Nat.log_le_self _ _).trans (Nat.div_le_self _ _))`. Rewrite using `[padicValNat_factorial hl, Formalism.HermitianLatticeCounting.S6.minkowskiExp, Finset.range_eq_Ico, Finset.sum_eq_sum_Ico_succ_bot (Nat.succ_pos n), pow_zero, one_mul]`. Use `congr 1`. Conclude with `Finset.sum_congr rfl fun i _ => by rw [Nat.div_div_eq_div_mul, mul_comm]`.
-/
theorem exp_eq (n p : ℕ) (hp : p.Prime) :
    n / (p - 1) + padicValNat p (n / (p - 1)).factorial = Formalism.HermitianLatticeCounting.S6.minkowskiExp n p := by
  haveI := Fact.mk hp
  have hl : Nat.log p (n / (p - 1)) < n + 1 :=
    Nat.lt_succ_of_le ((Nat.log_le_self _ _).trans (Nat.div_le_self _ _))
  rw [padicValNat_factorial hl, Formalism.HermitianLatticeCounting.S6.minkowskiExp, Finset.range_eq_Ico,
    Finset.sum_eq_sum_Ico_succ_bot (Nat.succ_pos n), pow_zero, one_mul]
  congr 1
  exact Finset.sum_congr rfl fun i _ => by rw [Nat.div_div_eq_div_mul, mul_comm]

open MinkowskiOrder in

/- English proof (translation)
Introduce `n G hG`. Establish `hc : Nat.card G ≠ 0` using `Nat.card_pos.ne'`. Rewrite using `[Nat.dvd_iff_prime_pow_dvd_dvd]`. Introduce `p k hp hk`. Use `haveI := Fact.mk hp`.

Establish `hle : k ≤ n / (p - 1) + padicValNat p (n / (p - 1)).factorial`. Distinguish the cases in `h2 : p = 2`. Substitute `h2` using the available equality. Take `⟨K, hK⟩` from `Sylow.exists_subgroup_card_pow_prime 2 hk`. Use `haveI := Fintype.ofFinite K`.

Rewrite `hK` using `[Nat.card_eq_fintype_card]`. Establish `h` using `card_two_group_dvd ((Units.coeHom _).comp (G.subtype.comp K.subtype)) (fun g hg => Subtype.ext (Subtype.ext (Units.ext hg))) hK`. Establish `hf` using `Nat.factorial_ne_zero n`. Rewrite `h` using `[padicValNat_dvd_iff_le (by positivity), padicValNat.mul (by positivity) hf, padicValNat.prime_pow]`. Simplify using `using h`.

Take `⟨l, hl, hpl, h⟩` from `exists_prime_gen p hp h2`. Establish `hp2` using `hp.two_le`. Use `le_trans ?_ (sum_odd p l hp h2 hl hpl h n)` and prove the remaining obligations. Rewrite using `[← val_prod n p l hp hl (by omega)]`. Conclude with `(hp.pow_dvd_iff_le_factorization (Finset.prod_ne_zero_iff.mpr fun i _ => Nat.sub_ne_zero_of_lt (Nat.pow_lt_pow_right hl.one_lt i.2))).1 (hk.trans (card_dvd_prod n G l hl (by omega)))`.

Distinguish the cases in `hpn : p < n + 2`. Rewrite `hle` using `[exp_eq n p hp]`. Use `(pow_dvd_pow p hle).trans ?_` and prove the remaining obligations. Conclude with `Finset.dvd_prod_of_mem (fun q => q ^ Formalism.HermitianLatticeCounting.S6.minkowskiExp n q) (Finset.mem_filter.2 ⟨Finset.mem_range.2 hpn, hp⟩)`. Rewrite `hle` using `[Nat.div_eq_of_lt (by omega)]`.

Establish `: k = 0` using `by simpa using hle`. Rewrite using `[this, pow_zero]`. Conclude with `one_dvd _`.
-/
theorem minkowskiBound : Formalism.HermitianLatticeCounting.S6.MinkowskiBound := by
  intro n G hG
  have hc : Nat.card G ≠ 0 := Nat.card_pos.ne'
  rw [Nat.dvd_iff_prime_pow_dvd_dvd]
  intro p k hp hk
  haveI := Fact.mk hp
  have hle : k ≤ n / (p - 1) + padicValNat p (n / (p - 1)).factorial := by
    by_cases h2 : p = 2
    · subst h2
      obtain ⟨K, hK⟩ := Sylow.exists_subgroup_card_pow_prime 2 hk
      haveI := Fintype.ofFinite K
      rw [Nat.card_eq_fintype_card] at hK
      have h := card_two_group_dvd ((Units.coeHom _).comp (G.subtype.comp K.subtype))
        (fun g hg => Subtype.ext (Subtype.ext (Units.ext hg))) hK
      have hf := Nat.factorial_ne_zero n
      rw [padicValNat_dvd_iff_le (by positivity), padicValNat.mul (by positivity) hf,
        padicValNat.prime_pow] at h
      simpa using h
    · obtain ⟨l, hl, hpl, h⟩ := exists_prime_gen p hp h2
      have hp2 := hp.two_le
      refine le_trans ?_ (sum_odd p l hp h2 hl hpl h n)
      rw [← val_prod n p l hp hl (by omega)]
      exact (hp.pow_dvd_iff_le_factorization (Finset.prod_ne_zero_iff.mpr fun i _ =>
        Nat.sub_ne_zero_of_lt (Nat.pow_lt_pow_right hl.one_lt i.2))).1
        (hk.trans (card_dvd_prod n G l hl (by omega)))
  by_cases hpn : p < n + 2
  · rw [exp_eq n p hp] at hle
    refine (pow_dvd_pow p hle).trans ?_
    exact Finset.dvd_prod_of_mem (fun q => q ^ Formalism.HermitianLatticeCounting.S6.minkowskiExp n q)
      (Finset.mem_filter.2 ⟨Finset.mem_range.2 hpn, hp⟩)
  · rw [Nat.div_eq_of_lt (by omega)] at hle
    have : k = 0 := by simpa using hle
    rw [this, pow_zero]
    exact one_dvd _

end GlobalTheory.MinkowskiExact

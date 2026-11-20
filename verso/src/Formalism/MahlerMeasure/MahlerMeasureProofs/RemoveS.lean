import Formalism.MahlerMeasure.TieVars
import Formalism.MahlerMeasure.MahlerMeasureProofs.LevelAct

namespace Formalism.GM.ProjS

open MvPolynomial Finset

variable {k σ : Type} [Field k]

noncomputable def mfac (m : σ →₀ ℕ) : k := m.prod fun _ j => (j.factorial : k)

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem fockK_eq (F G : MvPolynomial σ k) :
    M.fockK F G = ∑ m ∈ F.support, F.coeff m * G.coeff m * mfac m := rfl

/- English proof (translation)
Simplify `h` using `[MvPolynomial.mem_support_iff]`.
-/
private theorem mvPolynomial_coeff_eq_zero_of_not_mem_support {p : MvPolynomial σ k} {m : σ →₀ ℕ} (h : m ∉ p.support) :
    coeff m p = 0 := by
  simpa [MvPolynomial.mem_support_iff] using h

/- English proof (translation)
Rewrite using `[fockK_eq]`. Apply `Finset.sum_subset hs` to reduce the goal to its premises. Introduce `m _ hm`. Rewrite using `[mvPolynomial_coeff_eq_zero_of_not_mem_support hm]`. Simplify using the standard rewrite rules.
-/
theorem fockK_superset (F G : MvPolynomial σ k) (s : Finset (σ →₀ ℕ)) (hs : F.support ⊆ s) :
    M.fockK F G = ∑ m ∈ s, F.coeff m * G.coeff m * mfac m := by
  rw [fockK_eq]
  apply Finset.sum_subset hs
  intro m _ hm
  rw [mvPolynomial_coeff_eq_zero_of_not_mem_support hm]
  simp

/- English proof (translation)
Rewrite using `[fockK_superset F G (F.support ∪ G.support) (fun x hx => Finset.mem_union_left _ hx), fockK_superset G F (F.support ∪ G.support) (fun x hx => Finset.mem_union_right _ hx)]`. Conclude with `Finset.sum_congr rfl (fun m _ => by ring)`.
-/
theorem fockK_symm (F G : MvPolynomial σ k) : M.fockK F G = M.fockK G F := by
  classical
  rw [fockK_superset F G (F.support ∪ G.support) (fun x hx => Finset.mem_union_left _ hx),
    fockK_superset G F (F.support ∪ G.support) (fun x hx => Finset.mem_union_right _ hx)]
  exact Finset.sum_congr rfl (fun m _ => by ring)

/- English proof (translation)
Establish `h1 : (F + F').support ⊆ F.support ∪ F'.support`. Introduce `m hm`. Rewrite using `[Finset.mem_union]`. Assume the negation of the conclusion as `h`. Rewrite `h` using `[not_or]`.

Apply `(MvPolynomial.mem_support_iff.mp hm)` to reduce the goal to its premises. Rewrite using `[MvPolynomial.coeff_add, mvPolynomial_coeff_eq_zero_of_not_mem_support h.1, mvPolynomial_coeff_eq_zero_of_not_mem_support h.2, add_zero]`. Rewrite using `[fockK_superset _ G _ h1, fockK_superset F G (F.support ∪ F'.support) (fun x hx => Finset.mem_union_left _ hx), fockK_superset F' G (F.support ∪ F'.support) (fun x hx => Finset.mem_union_right _ hx), ← Finset.sum_add_distrib]`. Use `Finset.sum_congr rfl (fun m _ => ?_)` and prove the remaining obligations. Rewrite using `[MvPolynomial.coeff_add]`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem fockK_add_left (F F' G : MvPolynomial σ k) :
    M.fockK (F + F') G = M.fockK F G + M.fockK F' G := by
  classical
  have h1 : (F + F').support ⊆ F.support ∪ F'.support := by
    intro m hm
    rw [Finset.mem_union]
    by_contra h
    rw [not_or] at h
    apply (MvPolynomial.mem_support_iff.mp hm)
    rw [MvPolynomial.coeff_add, mvPolynomial_coeff_eq_zero_of_not_mem_support h.1, mvPolynomial_coeff_eq_zero_of_not_mem_support h.2, add_zero]
  rw [fockK_superset _ G _ h1,
    fockK_superset F G (F.support ∪ F'.support) (fun x hx => Finset.mem_union_left _ hx),
    fockK_superset F' G (F.support ∪ F'.support) (fun x hx => Finset.mem_union_right _ hx),
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun m _ => ?_)
  rw [MvPolynomial.coeff_add]
  ring

/- English proof (translation)
Establish `h1 : (c • F).support ⊆ F.support`. Introduce `m hm`. Assume the negation of the conclusion as `h`. Apply `(MvPolynomial.mem_support_iff.mp hm)` to reduce the goal to its premises. Rewrite using `[MvPolynomial.coeff_smul, mvPolynomial_coeff_eq_zero_of_not_mem_support h, smul_zero]`.

Rewrite using `[fockK_superset _ G _ h1, fockK_eq, Finset.mul_sum]`. Use `Finset.sum_congr rfl (fun m _ => ?_)` and prove the remaining obligations. Rewrite using `[MvPolynomial.coeff_smul, smul_eq_mul]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem fockK_smul_left (c : k) (F G : MvPolynomial σ k) :
    M.fockK (c • F) G = c * M.fockK F G := by
  have h1 : (c • F).support ⊆ F.support := by
    intro m hm
    by_contra h
    apply (MvPolynomial.mem_support_iff.mp hm)
    rw [MvPolynomial.coeff_smul, mvPolynomial_coeff_eq_zero_of_not_mem_support h, smul_zero]
  rw [fockK_superset _ G _ h1, fockK_eq, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun m _ => ?_)
  rw [MvPolynomial.coeff_smul, smul_eq_mul]
  ring

/- English proof (translation)
Simplify using `[Formalism.GM.M.fockK]`.
-/
theorem fockK_zero_left (G : MvPolynomial σ k) : M.fockK 0 G = 0 := by
  simp [Formalism.GM.M.fockK]

/- English proof (translation)
Use `Finset.induction_on s (by simp [fockK_zero_left]) ?_` and prove the remaining obligations. Introduce `a s ha ih`. Rewrite using `[Finset.sum_insert ha, Finset.sum_insert ha, fockK_add_left, ih]`.
-/
theorem fockK_sum_left {ι : Type} (s : Finset ι) (f : ι → MvPolynomial σ k) (G : MvPolynomial σ k) :
    M.fockK (∑ i ∈ s, f i) G = ∑ i ∈ s, M.fockK (f i) G := by
  classical
  refine Finset.induction_on s (by simp [fockK_zero_left]) ?_
  intro a s ha ih
  rw [Finset.sum_insert ha, Finset.sum_insert ha, fockK_add_left, ih]

/- English proof (translation)
Rewrite using `[fockK_symm F (G + G'), fockK_add_left, fockK_symm G F, fockK_symm G' F]`.
-/
theorem fockK_add_right (F G G' : MvPolynomial σ k) :
    M.fockK F (G + G') = M.fockK F G + M.fockK F G' := by
  rw [fockK_symm F (G + G'), fockK_add_left, fockK_symm G F, fockK_symm G' F]

/- English proof (translation)
Rewrite using `[fockK_symm F (c • G), fockK_smul_left, fockK_symm G F]`.
-/
theorem fockK_smul_right (c : k) (F G : MvPolynomial σ k) :
    M.fockK F (c • G) = c * M.fockK F G := by
  rw [fockK_symm F (c • G), fockK_smul_left, fockK_symm G F]

/- English proof (translation)
Rewrite using `[fockK_symm F, fockK_sum_left]`. Conclude with `Finset.sum_congr rfl (fun i _ => fockK_symm _ _)`.
-/
theorem fockK_sum_right {ι : Type} (s : Finset ι) (f : ι → MvPolynomial σ k) (F : MvPolynomial σ k) :
    M.fockK F (∑ i ∈ s, f i) = ∑ i ∈ s, M.fockK F (f i) := by
  rw [fockK_symm F, fockK_sum_left]
  exact Finset.sum_congr rfl (fun i _ => fockK_symm _ _)

/- English proof (translation)
Rewrite using `[fockK_symm, fockK_zero_left]`.
-/
theorem fockK_zero_right (F : MvPolynomial σ k) : M.fockK F 0 = 0 := by
  rw [fockK_symm, fockK_zero_left]

/- English proof (translation)
Establish `key : ∀ n : σ →₀ ℕ, n.support ⊆ insert v m.support → (mfac n : k) = ∏ a ∈ insert v m.support, ((n a).factorial : k)`. Introduce `n hn`. Unfold `mfac`. Conclude with `Finsupp.prod_of_support_subset n hn (fun _ j => (j.factorial : k)) (fun _ _ => by simp)`. Establish `hsub : (m + Finsupp.single v 1).support ⊆ insert v m.support`.

Introduce `a ha`. Rewrite `ha` using `[Finsupp.mem_support_iff]`. Rewrite using `[Finset.mem_insert, Finsupp.mem_support_iff]`. Distinguish the cases in `hav : a = v`. Conclude with `Or.inl hav`.

Use `right`. Simplify `ha` using `[Finsupp.single_apply, Ne.symm hav]`. Establish `hv : v ∈ insert v m.support` using `Finset.mem_insert_self v _`. Establish `hrest : ∏ a ∈ (insert v m.support).erase v, (((m + Finsupp.single v 1 : σ →₀ ℕ) a).factorial : k) = ∏ a ∈ (insert v m.support).erase v, ((m a).factorial : k)`. Use `Finset.prod_congr rfl (fun a ha => ?_)` and prove the remaining obligations.

Establish `hav : a ≠ v` using `Finset.ne_of_mem_erase ha`. Simplify using `[Ne.symm hav]`. Rewrite using `[key _ hsub, key m (Finset.subset_insert v m.support), ← Finset.mul_prod_erase (insert v m.support) (fun a => (((m + Finsupp.single v 1 : σ →₀ ℕ) a).factorial : k)) hv, ← Finset.mul_prod_erase (insert v m.support) (fun a => ((m a).factorial : k)) hv, hrest]`. Simplify using `only [Finsupp.coe_add, Pi.add_apply, Finsupp.single_eq_same, Nat.factorial_succ]`. Use `push_cast`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem mfac_add_single (m : σ →₀ ℕ) (v : σ) :
    (mfac (m + Finsupp.single v 1) : k) = mfac m * ((m v : k) + 1) := by
  classical
  have key : ∀ n : σ →₀ ℕ, n.support ⊆ insert v m.support →
      (mfac n : k) = ∏ a ∈ insert v m.support, ((n a).factorial : k) := by
    intro n hn
    unfold mfac
    exact Finsupp.prod_of_support_subset n hn (fun _ j => (j.factorial : k)) (fun _ _ => by simp)
  have hsub : (m + Finsupp.single v 1).support ⊆ insert v m.support := by
    intro a ha
    rw [Finsupp.mem_support_iff] at ha
    rw [Finset.mem_insert, Finsupp.mem_support_iff]
    by_cases hav : a = v
    · exact Or.inl hav
    · right
      simpa [Finsupp.single_apply, Ne.symm hav] using ha
  have hv : v ∈ insert v m.support := Finset.mem_insert_self v _
  have hrest : ∏ a ∈ (insert v m.support).erase v, (((m + Finsupp.single v 1 : σ →₀ ℕ) a).factorial : k)
      = ∏ a ∈ (insert v m.support).erase v, ((m a).factorial : k) := by
    refine Finset.prod_congr rfl (fun a ha => ?_)
    have hav : a ≠ v := Finset.ne_of_mem_erase ha
    simp [Ne.symm hav]
  rw [key _ hsub, key m (Finset.subset_insert v m.support),
    ← Finset.mul_prod_erase (insert v m.support) (fun a => (((m + Finsupp.single v 1 : σ →₀ ℕ) a).factorial : k)) hv,
    ← Finset.mul_prod_erase (insert v m.support) (fun a => ((m a).factorial : k)) hv, hrest]
  simp only [Finsupp.coe_add, Pi.add_apply, Finsupp.single_eq_same, Nat.factorial_succ]
  push_cast
  ring

/- English proof (translation)
Establish `h1` using `Formalism.GM.coeff_X_mul_pderiv' v h (m + Finsupp.single v 1)`. Rewrite `h1` using `[mul_comm (X v), MvPolynomial.coeff_mul_X]`. Rewrite using `[h1]`. Simplify using the standard rewrite rules.
-/
private theorem coeff_pderiv_eq_coeff_add_single_mul' (v : σ) (h : MvPolynomial σ k) (m : σ →₀ ℕ) :
    coeff m (pderiv v h) = coeff (m + Finsupp.single v 1) h * ((m v : k) + 1) := by
  have h1 := Formalism.GM.coeff_X_mul_pderiv' v h (m + Finsupp.single v 1)
  rw [mul_comm (X v), MvPolynomial.coeff_mul_X] at h1
  rw [h1]
  simp

/- English proof (translation)
Rewrite using `[fockK_eq, fockK_eq, mul_comm (X v) g, MvPolynomial.support_mul_X, Finset.sum_map]`. Use `Finset.sum_congr rfl (fun m _ => ?_)` and prove the remaining obligations. Rewrite using `[addRightEmbedding_apply, MvPolynomial.coeff_mul_X, coeff_pderiv_eq_coeff_add_single_mul', mfac_add_single]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem fockK_X_mul (v : σ) (g h : MvPolynomial σ k) :
    M.fockK (X v * g) h = M.fockK g (pderiv v h) := by
  rw [fockK_eq, fockK_eq, mul_comm (X v) g, MvPolynomial.support_mul_X, Finset.sum_map]
  refine Finset.sum_congr rfl (fun m _ => ?_)
  rw [addRightEmbedding_apply, MvPolynomial.coeff_mul_X, coeff_pderiv_eq_coeff_add_single_mul', mfac_add_single]
  ring

/- English proof (translation)
Rewrite using `[MvPolynomial.pderiv_X, Pi.single_apply, if_neg h]`.
-/
private theorem mvPolynomial_pderiv_X_eq_zero_of_ne {i j : σ} (h : j ≠ i) : pderiv i (X j : MvPolynomial σ k) = 0 := by
  classical
  rw [MvPolynomial.pderiv_X, Pi.single_apply, if_neg h]

/- English proof (translation)
Rewrite using `[Derivation.leibniz_pow, mvPolynomial_pderiv_X_eq_zero_of_ne h, smul_zero, smul_zero]`.
-/
private theorem pderiv_X_pow_of_ne {i j : σ} (h : j ≠ i) (z : ℕ) : pderiv i (X j ^ z : MvPolynomial σ k) = 0 := by
  rw [Derivation.leibniz_pow, mvPolynomial_pderiv_X_eq_zero_of_ne h, smul_zero, smul_zero]

/- English proof (translation)
Rewrite using `[MvPolynomial.pderiv_mul, pderiv_X_pow_of_ne h, zero_mul, zero_add]`.
-/
private theorem pderiv_X_pow_mul_of_ne {i j : σ} (h : j ≠ i) (z : ℕ) (g : MvPolynomial σ k) :
    pderiv i (X j ^ z * g) = X j ^ z * pderiv i g := by
  rw [MvPolynomial.pderiv_mul, pderiv_X_pow_of_ne h, zero_mul, zero_add]

/- English proof (translation)
Use `MvPolynomial.induction_on' p ?_ ?_` and prove the remaining obligations. Introduce `s a`. Distinguish the cases in `hij : i = j`. Substitute `hij` using the available equality. Both sides reduce to the same expression.

Simplify using `only [MvPolynomial.pderiv_monomial]`. Establish `h1 : (s - Finsupp.single j 1 : σ →₀ ℕ) i = s i`. Simplify using `[Ne.symm hij]`. Establish `h2 : (s - Finsupp.single i 1 : σ →₀ ℕ) j = s j`. Simplify using `[hij]`.

Rewrite using `[h1, h2, tsub_right_comm]`. Use `congr 1`. Expand and normalize the polynomial expressions, which then agree. Introduce `p q hp hq`. Simplify using `only [map_add, hp, hq]`.
-/
theorem pderiv_comm (i j : σ) (p : MvPolynomial σ k) :
    pderiv i (pderiv j p) = pderiv j (pderiv i p) := by
  classical
  refine MvPolynomial.induction_on' p ?_ ?_
  · intro s a
    by_cases hij : i = j
    · subst hij; rfl
    · simp only [MvPolynomial.pderiv_monomial]
      have h1 : (s - Finsupp.single j 1 : σ →₀ ℕ) i = s i := by
        simp [Ne.symm hij]
      have h2 : (s - Finsupp.single i 1 : σ →₀ ℕ) j = s j := by
        simp [hij]
      rw [h1, h2, tsub_right_comm]
      congr 1
      ring
  · intro p q hp hq
    simp only [map_add, hp, hq]

end Formalism.GM.ProjS

namespace Formalism.GM.ProjS

open MvPolynomial Finset

variable {k σ : Type} [Field k]

noncomputable def eulL {s : ℕ} (t : Fin s → σ) : MvPolynomial σ k →ₗ[k] MvPolynomial σ k :=
  ∑ c, (LinearMap.mulLeft k (X (t c))) ∘ₗ (pderiv (t c)).toLinearMap

/- English proof (translation)
Simplify using `only [eulL, LinearMap.sum_apply]`. Both sides reduce to the same expression.
-/
theorem eulL_apply {s : ℕ} (t : Fin s → σ) (g : MvPolynomial σ k) :
    eulL t g = ∑ c, X (t c) * pderiv (t c) g := by
  simp only [eulL, LinearMap.sum_apply]
  rfl

/- English proof (translation)
Rewrite using `[eulL_apply, MvPolynomial.coeff_sum, Finset.mul_sum]`. Conclude with `Finset.sum_congr rfl (fun c _ => Formalism.GM.coeff_X_mul_pderiv' (t c) g m)`.
-/
theorem coeff_eulL {s : ℕ} (t : Fin s → σ) (g : MvPolynomial σ k) (m : σ →₀ ℕ) :
    coeff m (eulL t g) = coeff m g * ∑ c, (m (t c) : k) := by
  rw [eulL_apply, MvPolynomial.coeff_sum, Finset.mul_sum]
  exact Finset.sum_congr rfl (fun c _ => Formalism.GM.coeff_X_mul_pderiv' (t c) g m)

/- English proof (translation)
Use extensionality with `m`. Rewrite using `[coeff_eulL, MvPolynomial.coeff_smul, smul_eq_mul]`. Distinguish the cases in `hm : m ∈ g.support`. Rewrite using `[← Nat.cast_sum, h m hm]`. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[mvPolynomial_coeff_eq_zero_of_not_mem_support hm]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem eulL_of_support {s : ℕ} (t : Fin s → σ) (a : ℕ) (g : MvPolynomial σ k)
    (h : ∀ m ∈ g.support, ∑ c, m (t c) = a) : eulL t g = (a : k) • g := by
  ext m
  rw [coeff_eulL, MvPolynomial.coeff_smul, smul_eq_mul]
  by_cases hm : m ∈ g.support
  · rw [← Nat.cast_sum, h m hm]; ring
  · rw [mvPolynomial_coeff_eq_zero_of_not_mem_support hm]; ring

/- English proof (translation)
Use extensionality with `m`. Rewrite using `[MvPolynomial.coeff_zero]`. Assume the negation of the conclusion as `hne`. Establish `h1` using `congrArg (coeff m) h`. Rewrite `h1` using `[coeff_eulL, MvPolynomial.coeff_smul, smul_eq_mul, mul_comm ((a : k) - b)]`.

Establish `h2 : (∑ c, (m (t c) : k)) = (a : k) - b` using `mul_left_cancel₀ hne h1`. Establish `h3 : ((∑ c, m (t c) + b : ℕ) : k) = ((a : ℕ) : k)`. Use `push_cast`. Rewrite using `[h2]`. Expand and normalize the polynomial expressions, which then agree.

Establish `h4` using `Nat.cast_injective h3`. Use linear arithmetic over natural numbers and integers.
-/
theorem eq_zero_of_eulL {s : ℕ} (t : Fin s → σ) (a b : ℕ) (hab : a < b) (g : MvPolynomial σ k) [CharZero k]
    (h : eulL t g = ((a : k) - (b : k)) • g) : g = 0 := by
  ext m
  rw [MvPolynomial.coeff_zero]
  by_contra hne
  have h1 := congrArg (coeff m) h
  rw [coeff_eulL, MvPolynomial.coeff_smul, smul_eq_mul, mul_comm ((a : k) - b)] at h1
  have h2 : (∑ c, (m (t c) : k)) = (a : k) - b := mul_left_cancel₀ hne h1
  have h3 : ((∑ c, m (t c) + b : ℕ) : k) = ((a : ℕ) : k) := by
    push_cast
    rw [h2]
    ring
  have h4 := Nat.cast_injective h3
  omega

/- English proof (translation)
Rewrite using `[eulL_apply, eulL_apply, eulL_apply, Finset.sum_mul, Finset.mul_sum, ← Finset.sum_add_distrib]`. Use `Finset.sum_congr rfl (fun c _ => ?_)` and prove the remaining obligations. Rewrite using `[MvPolynomial.pderiv_mul]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem eulL_mul {s : ℕ} (t : Fin s → σ) (f g : MvPolynomial σ k) :
    eulL t (f * g) = eulL t f * g + f * eulL t g := by
  rw [eulL_apply, eulL_apply, eulL_apply, Finset.sum_mul, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun c _ => ?_)
  rw [MvPolynomial.pderiv_mul]
  ring

/- English proof (translation)
Rewrite using `[eulL_apply, eulL_apply, map_sum]`. Use `Finset.sum_congr rfl (fun c _ => ?_)` and prove the remaining obligations. Rewrite using `[MvPolynomial.pderiv_mul, mvPolynomial_pderiv_X_eq_zero_of_ne (hv c), zero_mul, zero_add, pderiv_comm]`.
-/
theorem eulL_pderiv_notMem {s : ℕ} (t : Fin s → σ) (v : σ) (hv : ∀ c, t c ≠ v) (h : MvPolynomial σ k) :
    eulL t (pderiv v h) = pderiv v (eulL t h) := by
  rw [eulL_apply, eulL_apply, map_sum]
  refine Finset.sum_congr rfl (fun c _ => ?_)
  rw [MvPolynomial.pderiv_mul, mvPolynomial_pderiv_X_eq_zero_of_ne (hv c), zero_mul, zero_add, pderiv_comm]

/- English proof (translation)
Establish `key : pderiv (t c0) (eulL t h) = pderiv (t c0) h + eulL t (pderiv (t c0) h)`. Rewrite using `[eulL_apply, eulL_apply, map_sum]`. Establish `hc : ∀ c, pderiv (t c0) (X (t c) * pderiv (t c) h) = (if c = c0 then pderiv (t c) h else 0) + X (t c) * pderiv (t c) (pderiv (t c0) h)`. Introduce `c`. Rewrite using `[MvPolynomial.pderiv_mul, Formalism.GM.pderiv_X_inj ht, pderiv_comm (t c0) (t c)]`.

Apply the tactic sequence `split_ifs <;> simp`. Rewrite using `[Finset.sum_congr rfl (fun c _ => hc c), Finset.sum_add_distrib, Finset.sum_ite_eq', if_pos (Finset.mem_univ _)]`. Rewrite using `[key]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem eulL_pderiv_mem {s : ℕ} (t : Fin s → σ) (ht : Function.Injective t) (c0 : Fin s)
    (h : MvPolynomial σ k) :
    eulL t (pderiv (t c0) h) = pderiv (t c0) (eulL t h) - pderiv (t c0) h := by
  have key : pderiv (t c0) (eulL t h) = pderiv (t c0) h + eulL t (pderiv (t c0) h) := by
    rw [eulL_apply, eulL_apply, map_sum]
    have hc : ∀ c, pderiv (t c0) (X (t c) * pderiv (t c) h) =
        (if c = c0 then pderiv (t c) h else 0) + X (t c) * pderiv (t c) (pderiv (t c0) h) := by
      intro c
      rw [MvPolynomial.pderiv_mul, Formalism.GM.pderiv_X_inj ht, pderiv_comm (t c0) (t c)]
      split_ifs <;> simp
    rw [Finset.sum_congr rfl (fun c _ => hc c), Finset.sum_add_distrib, Finset.sum_ite_eq',
      if_pos (Finset.mem_univ _)]
  rw [key]
  ring

/- English proof (translation)
Break down `hab with ⟨⟨d, hd⟩, hb⟩ | ⟨ha, ⟨d, hd⟩⟩` into its components or cases. Substitute `hd` using the available equality. Rewrite using `[eulL_pderiv_mem t ht d, eulL_pderiv_notMem t b hb]`. Substitute `hd` using the available equality. Rewrite using `[eulL_pderiv_notMem t a ha, eulL_pderiv_mem t ht d, map_sub]`.
-/
theorem eulL_pderiv_pair {s : ℕ} (t : Fin s → σ) (ht : Function.Injective t) (a b : σ)
    (hab : ((∃ d, t d = a) ∧ ∀ d, t d ≠ b) ∨ ((∀ d, t d ≠ a) ∧ ∃ d, t d = b)) (g : MvPolynomial σ k) :
    eulL t (pderiv a (pderiv b g)) = pderiv a (pderiv b (eulL t g)) - pderiv a (pderiv b g) := by
  rcases hab with ⟨⟨d, hd⟩, hb⟩ | ⟨ha, ⟨d, hd⟩⟩
  · subst hd
    rw [eulL_pderiv_mem t ht d, eulL_pderiv_notMem t b hb]
  · subst hd
    rw [eulL_pderiv_notMem t a ha, eulL_pderiv_mem t ht d, map_sub]

/- English proof (translation)
Simplify using `only [Formalism.GM.tieF_apply', map_sum]`. Rewrite using `[← Finset.sum_sub_distrib]`. Conclude with `Finset.sum_congr rfl (fun c _ => eulL_pderiv_pair t ht (w c) (e c) (hmix c) g)`.
-/
theorem eulL_tieF {s r : ℕ} (t : Fin s → σ) (ht : Function.Injective t) (w e : Fin r → σ)
    (hmix : ∀ c, ((∃ d, t d = w c) ∧ ∀ d, t d ≠ e c) ∨ ((∀ d, t d ≠ w c) ∧ ∃ d, t d = e c))
    (g : MvPolynomial σ k) :
    eulL t (tieF w e g) = tieF w e (eulL t g) - tieF w e g := by
  simp only [Formalism.GM.tieF_apply', map_sum]
  rw [← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl (fun c _ => eulL_pderiv_pair t ht (w c) (e c) (hmix c) g)

/- English proof (translation)
Proceed by induction on `l with`. Consider the case `zero => simpa using hg`. Consider the case `succ l ih`. Rewrite using `[pow_succ', Module.End.mul_apply, eulL_tieF t ht w e hmix, ih, map_smul, Nat.cast_succ, sub_add_eq_sub_sub, sub_smul (α - (l : k)) 1, one_smul]`.
-/
theorem eulL_tieF_pow {s r : ℕ} (t : Fin s → σ) (ht : Function.Injective t) (w e : Fin r → σ)
    (hmix : ∀ c, ((∃ d, t d = w c) ∧ ∀ d, t d ≠ e c) ∨ ((∀ d, t d ≠ w c) ∧ ∃ d, t d = e c))
    (g : MvPolynomial σ k) (α : k) (hg : eulL t g = α • g) (l : ℕ) :
    eulL t ((tieF w e ^ l) g) = (α - l) • (tieF w e ^ l) g := by
  induction l with
  | zero => simpa using hg
  | succ l ih =>
    rw [pow_succ', Module.End.mul_apply, eulL_tieF t ht w e hmix, ih, map_smul, Nat.cast_succ,
      sub_add_eq_sub_sub, sub_smul (α - (l : k)) 1, one_smul]

/- English proof (translation)
Simplify using `only [Formalism.GM.tieF_apply', map_sum]`. Use `Finset.sum_congr rfl (fun c _ => ?_)` and prove the remaining obligations. Rewrite using `[pderiv_comm (e c) v, pderiv_comm (w c) v]`.
-/
theorem tieF_pderiv {r : ℕ} (w e : Fin r → σ) (v : σ) (g : MvPolynomial σ k) :
    tieF w e (pderiv v g) = pderiv v (tieF w e g) := by
  simp only [Formalism.GM.tieF_apply', map_sum]
  refine Finset.sum_congr rfl (fun c _ => ?_)
  rw [pderiv_comm (e c) v, pderiv_comm (w c) v]

/- English proof (translation)
Proceed by induction on `l with`. Consider the case `zero => simp`. Consider the case `succ l ih`. Simplify using `only [pow_succ', Module.End.mul_apply]`. Rewrite using `[ih, tieF_pderiv]`.
-/
theorem tieF_pow_pderiv {r : ℕ} (w e : Fin r → σ) (v : σ) (g : MvPolynomial σ k) (l : ℕ) :
    (tieF w e ^ l) (pderiv v g) = pderiv v ((tieF w e ^ l) g) := by
  induction l with
  | zero => simp
  | succ l ih =>
    simp only [pow_succ', Module.End.mul_apply]
    rw [ih, tieF_pderiv]

/- English proof (translation)
Simplify using `only [Formalism.GM.tieF_apply', Finset.mul_sum]`. Use `Finset.sum_congr rfl (fun c _ => ?_)` and prove the remaining obligations. Rewrite using `[pderiv_X_pow_mul_of_ne (hz c).2.symm, pderiv_X_pow_mul_of_ne (hz c).1.symm]`.
-/
theorem tieF_X_pow_mul {r : ℕ} (w e : Fin r → σ) (zv : σ) (hz : ∀ c, w c ≠ zv ∧ e c ≠ zv) (z : ℕ)
    (g : MvPolynomial σ k) : tieF w e (X zv ^ z * g) = X zv ^ z * tieF w e g := by
  simp only [Formalism.GM.tieF_apply', Finset.mul_sum]
  refine Finset.sum_congr rfl (fun c _ => ?_)
  rw [pderiv_X_pow_mul_of_ne (hz c).2.symm, pderiv_X_pow_mul_of_ne (hz c).1.symm]

/- English proof (translation)
Proceed by induction on `l with`. Consider the case `zero => simp`. Consider the case `succ l ih`. Simplify using `only [pow_succ', Module.End.mul_apply]`. Rewrite using `[ih, tieF_X_pow_mul w e zv hz]`.
-/
theorem tieF_pow_X_pow_mul {r : ℕ} (w e : Fin r → σ) (zv : σ) (hz : ∀ c, w c ≠ zv ∧ e c ≠ zv) (z : ℕ)
    (g : MvPolynomial σ k) (l : ℕ) : (tieF w e ^ l) (X zv ^ z * g) = X zv ^ z * (tieF w e ^ l) g := by
  induction l with
  | zero => simp
  | succ l ih =>
    simp only [pow_succ', Module.End.mul_apply]
    rw [ih, tieF_X_pow_mul w e zv hz]

end Formalism.GM.ProjS

namespace Formalism.GM.ProjS

open MvPolynomial Finset

variable {k σ : Type} [Field k]

section
variable {s : ℕ} {w e : Fin s → σ}

/- English proof (translation)
Establish `hR : eulL w (∑ d, X (w d) * X (e d) : MvPolynomial σ k) = ∑ d, X (w d) * X (e d)`. Rewrite using `[eulL_apply]`. Conclude with `Finset.sum_congr rfl (fun c _ => by rw [Formalism.GM.pderiv_w_S hw hwe c])`. Rewrite using `[eulL_mul, hR, hW, mul_smul_comm, add_smul, one_smul]`. Normalize the expressions using the abelian group laws.
-/
theorem eulL_w_S_mul (hw : Function.Injective w) (hwe : ∀ c d, w c ≠ e d)
    (g : MvPolynomial σ k) (α : k) (hW : eulL w g = α • g) :
    eulL w ((∑ d, X (w d) * X (e d)) * g) = (α + 1) • ((∑ d, X (w d) * X (e d)) * g) := by
  have hR : eulL w (∑ d, X (w d) * X (e d) : MvPolynomial σ k) = ∑ d, X (w d) * X (e d) := by
    rw [eulL_apply]
    exact Finset.sum_congr rfl (fun c _ => by rw [Formalism.GM.pderiv_w_S hw hwe c])
  rw [eulL_mul, hR, hW, mul_smul_comm, add_smul, one_smul]
  abel

/- English proof (translation)
Establish `hR : eulL e (∑ d, X (w d) * X (e d) : MvPolynomial σ k) = ∑ d, X (w d) * X (e d)`. Rewrite using `[eulL_apply]`. Conclude with `Finset.sum_congr rfl (fun c _ => by rw [Formalism.GM.pderiv_e_S he hwe c, mul_comm])`. Rewrite using `[eulL_mul, hR, hE, mul_smul_comm, add_smul, one_smul]`. Normalize the expressions using the abelian group laws.
-/
theorem eulL_e_S_mul (he : Function.Injective e) (hwe : ∀ c d, w c ≠ e d)
    (g : MvPolynomial σ k) (β : k) (hE : eulL e g = β • g) :
    eulL e ((∑ d, X (w d) * X (e d)) * g) = (β + 1) • ((∑ d, X (w d) * X (e d)) * g) := by
  have hR : eulL e (∑ d, X (w d) * X (e d) : MvPolynomial σ k) = ∑ d, X (w d) * X (e d) := by
    rw [eulL_apply]
    exact Finset.sum_congr rfl (fun c _ => by rw [Formalism.GM.pderiv_e_S he hwe c, mul_comm])
  rw [eulL_mul, hR, hE, mul_smul_comm, add_smul, one_smul]
  abel

/- English proof (translation)
Proceed by induction on `j with`. Consider the case `zero`. Simplify using `only [pow_zero, Module.End.one_apply, Nat.cast_zero, add_zero]`. Conclude with `⟨hW, hE⟩`. Consider the case `succ j ih`.

Rewrite using `[pow_succ', Module.End.mul_apply, Formalism.GM.tieE_apply', Nat.cast_succ, ← add_assoc, ← add_assoc]`. Conclude with `⟨eulL_w_S_mul hw hwe _ _ ih.1, eulL_e_S_mul he hwe _ _ ih.2⟩`.
-/
theorem eulL_tieE_pow (hw : Function.Injective w) (he : Function.Injective e) (hwe : ∀ c d, w c ≠ e d)
    (g : MvPolynomial σ k) (α β : k) (hW : eulL w g = α • g) (hE : eulL e g = β • g) (j : ℕ) :
    eulL w ((tieE w e ^ j) g) = (α + j) • (tieE w e ^ j) g ∧
    eulL e ((tieE w e ^ j) g) = (β + j) • (tieE w e ^ j) g := by
  induction j with
  | zero =>
    simp only [pow_zero, Module.End.one_apply, Nat.cast_zero, add_zero]
    exact ⟨hW, hE⟩
  | succ j ih =>
    rw [pow_succ', Module.End.mul_apply, Formalism.GM.tieE_apply', Nat.cast_succ, ← add_assoc, ← add_assoc]
    exact ⟨eulL_w_S_mul hw hwe _ _ ih.1, eulL_e_S_mul he hwe _ _ ih.2⟩

/- English proof (translation)
Establish `hc : ∀ c, pderiv (w c) (pderiv (e c) ((∑ d, X (w d) * X (e d)) * g)) = g + X (w c) * pderiv (w c) g + X (e c) * pderiv (e c) g + (∑ d, X (w d) * X (e d)) * pderiv (w c) (pderiv (e c) g)`. Introduce `c`. Rewrite using `[MvPolynomial.pderiv_mul, Formalism.GM.pderiv_e_S he hwe c, map_add, MvPolynomial.pderiv_mul, MvPolynomial.pderiv_mul, MvPolynomial.pderiv_X_self, Formalism.GM.pderiv_w_S hw hwe c]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[Formalism.GM.tieF_apply', Formalism.GM.tieF_apply', Finset.sum_congr rfl (fun c _ => hc c)]`.

Simplify using `only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin, ← Finset.mul_sum]`. Rewrite using `[← eulL_apply w g, ← eulL_apply e g, hW, hE]`. Simplify using `only [MvPolynomial.smul_eq_C_mul, map_add, map_natCast, nsmul_eq_mul]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem F_S_mul_k (hw : Function.Injective w) (he : Function.Injective e) (hwe : ∀ c d, w c ≠ e d)
    (g : MvPolynomial σ k) (α β : k) (hW : eulL w g = α • g) (hE : eulL e g = β • g) :
    tieF w e ((∑ d, X (w d) * X (e d)) * g) =
      (∑ d, X (w d) * X (e d)) * tieF w e g + (α + β + s) • g := by
  have hc : ∀ c, pderiv (w c) (pderiv (e c) ((∑ d, X (w d) * X (e d)) * g)) =
      g + X (w c) * pderiv (w c) g + X (e c) * pderiv (e c) g +
        (∑ d, X (w d) * X (e d)) * pderiv (w c) (pderiv (e c) g) := by
    intro c
    rw [MvPolynomial.pderiv_mul, Formalism.GM.pderiv_e_S he hwe c, map_add, MvPolynomial.pderiv_mul,
      MvPolynomial.pderiv_mul, MvPolynomial.pderiv_X_self, Formalism.GM.pderiv_w_S hw hwe c]
    ring
  rw [Formalism.GM.tieF_apply', Formalism.GM.tieF_apply', Finset.sum_congr rfl (fun c _ => hc c)]
  simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    ← Finset.mul_sum]
  rw [← eulL_apply w g, ← eulL_apply e g, hW, hE]
  simp only [MvPolynomial.smul_eq_C_mul, map_add, map_natCast, nsmul_eq_mul]
  ring

/- English proof (translation)
Proceed by induction on `j with`. Consider the case `zero`. Simplify using `only [zero_add, pow_one, pow_zero, Module.End.one_apply, Formalism.GM.tieE_apply', Nat.cast_zero, one_mul, add_zero]`. Conclude with `F_S_mul_k hw he hwe g α β hW hE`. Consider the case `succ j ih`.

Establish `hr` using `eulL_tieE_pow hw he hwe g α β hW hE (j + 1)`. Establish `e1 : ∀ x : MvPolynomial σ k, (Formalism.GM.tieE w e ^ (j + 1 + 1)) x = (∑ d, X (w d) * X (e d)) * (Formalism.GM.tieE w e ^ (j + 1)) x`. Introduce `x`. Rewrite using `[pow_succ' (Formalism.GM.tieE (k := k) w e) (j + 1), Module.End.mul_apply, Formalism.GM.tieE_apply']`. Establish `e0 : ∀ x : MvPolynomial σ k, (Formalism.GM.tieE w e ^ (j + 1)) x = (∑ d, X (w d) * X (e d)) * (Formalism.GM.tieE w e ^ j) x`.

Introduce `x`. Rewrite using `[pow_succ' (Formalism.GM.tieE (k := k) w e) j, Module.End.mul_apply, Formalism.GM.tieE_apply']`. Establish `hcoef : ((j : k) + 1) * (α + β + s + j) + (α + ((j + 1 : ℕ) : k) + (β + ((j + 1 : ℕ) : k)) + s) = (((j + 1 : ℕ) : k) + 1) * (α + β + s + ((j + 1 : ℕ) : k))`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[e1, e1, F_S_mul_k hw he hwe _ _ _ hr.1 hr.2, ih, mul_add, mul_smul_comm, ← e0, add_assoc, ← add_smul, hcoef]`.
-/
theorem F_E_pow_comm (hw : Function.Injective w) (he : Function.Injective e) (hwe : ∀ c d, w c ≠ e d)
    (g : MvPolynomial σ k) (α β : k) (hW : eulL w g = α • g) (hE : eulL e g = β • g) (j : ℕ) :
    tieF w e ((tieE w e ^ (j + 1)) g) =
      (tieE w e ^ (j + 1)) (tieF w e g) + (((j : k) + 1) * (α + β + s + j)) • (tieE w e ^ j) g := by
  induction j with
  | zero =>
    simp only [zero_add, pow_one, pow_zero, Module.End.one_apply, Formalism.GM.tieE_apply', Nat.cast_zero, one_mul, add_zero]
    exact F_S_mul_k hw he hwe g α β hW hE
  | succ j ih =>
    have hr := eulL_tieE_pow hw he hwe g α β hW hE (j + 1)
    have e1 : ∀ x : MvPolynomial σ k, (Formalism.GM.tieE w e ^ (j + 1 + 1)) x = (∑ d, X (w d) * X (e d)) * (Formalism.GM.tieE w e ^ (j + 1)) x := by
      intro x
      rw [pow_succ' (Formalism.GM.tieE (k := k) w e) (j + 1), Module.End.mul_apply, Formalism.GM.tieE_apply']
    have e0 : ∀ x : MvPolynomial σ k, (Formalism.GM.tieE w e ^ (j + 1)) x = (∑ d, X (w d) * X (e d)) * (Formalism.GM.tieE w e ^ j) x := by
      intro x
      rw [pow_succ' (Formalism.GM.tieE (k := k) w e) j, Module.End.mul_apply, Formalism.GM.tieE_apply']
    have hcoef : ((j : k) + 1) * (α + β + s + j) + (α + ((j + 1 : ℕ) : k) + (β + ((j + 1 : ℕ) : k)) + s) =
        (((j + 1 : ℕ) : k) + 1) * (α + β + s + ((j + 1 : ℕ) : k)) := by
      push_cast
      ring
    rw [e1, e1, F_S_mul_k hw he hwe _ _ _ hr.1 hr.2, ih, mul_add, mul_smul_comm, ← e0,
      add_assoc, ← add_smul, hcoef]

end

/- English proof (translation)
Rewrite using `[Formalism.GM.tieE_apply', Finset.sum_mul, fockK_sum_left, Formalism.GM.tieF_apply', fockK_sum_right]`. Use `Finset.sum_congr rfl (fun c _ => ?_)` and prove the remaining obligations. Rewrite using `[mul_assoc, fockK_X_mul, fockK_X_mul, pderiv_comm]`.
-/
theorem fockK_tieE {r : ℕ} (w e : Fin r → σ) (g h : MvPolynomial σ k) :
    M.fockK (tieE w e g) h = M.fockK g (tieF w e h) := by
  rw [Formalism.GM.tieE_apply', Finset.sum_mul, fockK_sum_left, Formalism.GM.tieF_apply', fockK_sum_right]
  refine Finset.sum_congr rfl (fun c _ => ?_)
  rw [mul_assoc, fockK_X_mul, fockK_X_mul, pderiv_comm]

/- English proof (translation)
Proceed by induction on `l generalizing h with`. Consider the case `zero => simp`. Consider the case `succ l ih`. Rewrite using `[pow_succ' (Formalism.GM.tieE w e) l, Module.End.mul_apply, fockK_tieE, ih, pow_succ (Formalism.GM.tieF w e) l, Module.End.mul_apply]`.
-/
theorem fockK_tieE_pow {r : ℕ} (w e : Fin r → σ) (l : ℕ) (g h : MvPolynomial σ k) :
    M.fockK ((tieE w e ^ l) g) h = M.fockK g ((tieF w e ^ l) h) := by
  induction l generalizing h with
  | zero => simp
  | succ l ih =>
    rw [pow_succ' (Formalism.GM.tieE w e) l, Module.End.mul_apply, fockK_tieE, ih, pow_succ (Formalism.GM.tieF w e) l,
      Module.End.mul_apply]

/- English proof (translation)
Rewrite using `[fockK_symm g, fockK_tieE_pow, fockK_symm h]`.
-/
theorem fockK_tieE_pow_right {r : ℕ} (w e : Fin r → σ) (l : ℕ) (g h : MvPolynomial σ k) :
    M.fockK g ((tieE w e ^ l) h) = M.fockK ((tieF w e ^ l) g) h := by
  rw [fockK_symm g, fockK_tieE_pow, fockK_symm h]

/- English proof (translation)
Proceed by induction on `z generalizing h with`. Consider the case `zero => simp`. Consider the case `succ z ih`. Rewrite using `[pow_succ' (X v : MvPolynomial σ k) z, mul_assoc, fockK_X_mul, ih, pow_succ, Module.End.mul_apply]`. Apply the tactic sequence `try rfl`.
-/
theorem fockK_X_pow_mul (v : σ) (z : ℕ) (a h : MvPolynomial σ k) :
    M.fockK (X v ^ z * a) h = M.fockK a (((pderiv v).toLinearMap ^ z) h) := by
  induction z generalizing h with
  | zero => simp
  | succ z ih =>
    rw [pow_succ' (X v : MvPolynomial σ k) z, mul_assoc, fockK_X_mul, ih, pow_succ, Module.End.mul_apply]
    try rfl

/- English proof (translation)
Rewrite using `[Derivation.leibniz_pow, MvPolynomial.pderiv_X_self, smul_eq_mul, mul_one, nsmul_eq_mul, Nat.add_sub_cancel]`.
-/
private theorem pderiv_X_pow_succ_self (v : σ) (z : ℕ) :
    pderiv v (X v ^ (z + 1) : MvPolynomial σ k) = ((z + 1 : ℕ) : MvPolynomial σ k) * X v ^ z := by
  rw [Derivation.leibniz_pow, MvPolynomial.pderiv_X_self, smul_eq_mul, mul_one, nsmul_eq_mul,
    Nat.add_sub_cancel]

/- English proof (translation)
Proceed by induction on `z with`. Consider the case `zero => simp`. Consider the case `succ z ih`. Establish `h1 : (pderiv v).toLinearMap (X v ^ (z + 1) * b) = ((z + 1 : ℕ) : k) • (X v ^ z * b)` using `by show pderiv v (X v ^ (z + 1) * b) = _`. Rewrite using `[MvPolynomial.pderiv_mul, hb, mul_zero, add_zero, pderiv_X_pow_succ_self, MvPolynomial.smul_eq_C_mul, map_natCast, mul_assoc]`.

Rewrite using `[pow_succ, Module.End.mul_apply, h1, map_smul, ih, smul_smul, Nat.factorial_succ, Nat.cast_mul]`.
-/
theorem pderiv_pow_X_pow_mul (v : σ) (b : MvPolynomial σ k) (hb : pderiv v b = 0) (z : ℕ) :
    ((pderiv v).toLinearMap ^ z) (X v ^ z * b) = (z.factorial : k) • b := by
  induction z with
  | zero => simp
  | succ z ih =>
    have h1 : (pderiv v).toLinearMap (X v ^ (z + 1) * b) = ((z + 1 : ℕ) : k) • (X v ^ z * b) := by
      show pderiv v (X v ^ (z + 1) * b) = _
      rw [MvPolynomial.pderiv_mul, hb, mul_zero, add_zero, pderiv_X_pow_succ_self, MvPolynomial.smul_eq_C_mul,
        map_natCast, mul_assoc]
    rw [pow_succ, Module.End.mul_apply, h1, map_smul, ih, smul_smul, Nat.factorial_succ, Nat.cast_mul]

/- English proof (translation)
Unfold `Formalism.GM.M.tieEh Formalism.GM.tieE`. Rewrite using `[Fin.sum_univ_succ]`. Simplify using `only [Fin.cons_zero, Fin.cons_succ]`.
-/
theorem tieEh_eq {r : ℕ} (w e : Fin r → σ) (zv sv : σ) :
    (M.tieEh w e zv sv : MvPolynomial σ k →ₗ[k] MvPolynomial σ k) =
      tieE (Fin.cons zv w : Fin (r + 1) → σ) (Fin.cons sv e) := by
  unfold Formalism.GM.M.tieEh Formalism.GM.tieE
  rw [Fin.sum_univ_succ]
  simp only [Fin.cons_zero, Fin.cons_succ]

/- English proof (translation)
Unfold `Formalism.GM.M.tieFh Formalism.GM.tieF`. Rewrite using `[Fin.sum_univ_succ]`. Simplify using `only [Fin.cons_zero, Fin.cons_succ]`.
-/
theorem tieFh_eq {r : ℕ} (w e : Fin r → σ) (zv sv : σ) :
    (M.tieFh w e zv sv : MvPolynomial σ k →ₗ[k] MvPolynomial σ k) =
      tieF (Fin.cons zv w : Fin (r + 1) → σ) (Fin.cons sv e) := by
  unfold Formalism.GM.M.tieFh Formalism.GM.tieF
  rw [Fin.sum_univ_succ]
  simp only [Fin.cons_zero, Fin.cons_succ]

end Formalism.GM.ProjS

namespace Formalism.GM.ProjS

open MvPolynomial Finset

variable {k σ : Type} [Field k] {r : ℕ} {w e : Fin r → σ} {zv sv : σ}

/- English proof (translation)
Take `⟨hw, he, hwe, hz, hzs⟩` from `hv`. Introduce `i j hij`. Proceed by induction on `i using Fin.cases with`. Consider the case `zero`. Proceed by induction on `j using Fin.cases with`.

Consider the case `zero => rfl`. Consider the case `succ j`. Simplify using `only [Fin.cons_zero, Fin.cons_succ] at hij`. Conclude with `absurd hij.symm (hz j).1`. Consider the case `succ i`.

Proceed by induction on `j using Fin.cases with`. Consider the case `zero`. Simplify using `only [Fin.cons_zero, Fin.cons_succ] at hij`. Conclude with `absurd hij (hz i).1`. Consider the case `succ j`.

Simplify using `only [Fin.cons_succ] at hij`. Rewrite using `[hw hij]`.
-/
theorem tv_w (hv : M.TieVars w e zv sv) : Function.Injective (Fin.cons zv w : Fin (r + 1) → σ) := by
  obtain ⟨hw, he, hwe, hz, hzs⟩ := hv
  intro i j hij
  induction i using Fin.cases with
  | zero =>
    induction j using Fin.cases with
    | zero => rfl
    | succ j =>
      simp only [Fin.cons_zero, Fin.cons_succ] at hij
      exact absurd hij.symm (hz j).1
  | succ i =>
    induction j using Fin.cases with
    | zero =>
      simp only [Fin.cons_zero, Fin.cons_succ] at hij
      exact absurd hij (hz i).1
    | succ j =>
      simp only [Fin.cons_succ] at hij
      rw [hw hij]

/- English proof (translation)
Take `⟨hw, he, hwe, hz, hzs⟩` from `hv`. Introduce `i j hij`. Proceed by induction on `i using Fin.cases with`. Consider the case `zero`. Proceed by induction on `j using Fin.cases with`.

Consider the case `zero => rfl`. Consider the case `succ j`. Simplify using `only [Fin.cons_zero, Fin.cons_succ] at hij`. Conclude with `absurd hij.symm (hz j).2.2.2`. Consider the case `succ i`.

Proceed by induction on `j using Fin.cases with`. Consider the case `zero`. Simplify using `only [Fin.cons_zero, Fin.cons_succ] at hij`. Conclude with `absurd hij (hz i).2.2.2`. Consider the case `succ j`.

Simplify using `only [Fin.cons_succ] at hij`. Rewrite using `[he hij]`.
-/
theorem tv_e (hv : M.TieVars w e zv sv) : Function.Injective (Fin.cons sv e : Fin (r + 1) → σ) := by
  obtain ⟨hw, he, hwe, hz, hzs⟩ := hv
  intro i j hij
  induction i using Fin.cases with
  | zero =>
    induction j using Fin.cases with
    | zero => rfl
    | succ j =>
      simp only [Fin.cons_zero, Fin.cons_succ] at hij
      exact absurd hij.symm (hz j).2.2.2
  | succ i =>
    induction j using Fin.cases with
    | zero =>
      simp only [Fin.cons_zero, Fin.cons_succ] at hij
      exact absurd hij (hz i).2.2.2
    | succ j =>
      simp only [Fin.cons_succ] at hij
      rw [he hij]

/- English proof (translation)
Take `⟨hw, he, hwe, hz, hzs⟩` from `hv`. Introduce `c d`. Proceed by induction on `c using Fin.cases with`. Consider the case `zero`. Proceed by induction on `d using Fin.cases with`.

Consider the case `zero => simpa using hzs`. Consider the case `succ d => simpa using (hz d).2.2.1.symm`. Consider the case `succ c`. Proceed by induction on `d using Fin.cases with`. Consider the case `zero => simpa using (hz c).2.1`.

Consider the case `succ d => simpa using hwe c d`.
-/
theorem tv_we (hv : M.TieVars w e zv sv) :
    ∀ c d, (Fin.cons zv w : Fin (r + 1) → σ) c ≠ (Fin.cons sv e : Fin (r + 1) → σ) d := by
  obtain ⟨hw, he, hwe, hz, hzs⟩ := hv
  intro c d
  induction c using Fin.cases with
  | zero =>
    induction d using Fin.cases with
    | zero => simpa using hzs
    | succ d => simpa using (hz d).2.2.1.symm
  | succ c =>
    induction d using Fin.cases with
    | zero => simpa using (hz c).2.1
    | succ d => simpa using hwe c d

/- English proof (translation)
Introduce `c` and use `Or.inl ⟨⟨c, rfl⟩, fun d => hv.2.2.1 d c⟩`.
-/
theorem mix_w (hv : M.TieVars w e zv sv) :
    ∀ c, ((∃ d, w d = w c) ∧ ∀ d, w d ≠ e c) ∨ ((∀ d, w d ≠ w c) ∧ ∃ d, w d = e c) := fun c => Or.inl ⟨⟨c, rfl⟩, fun d => hv.2.2.1 d c⟩

/- English proof (translation)
Take `⟨hw, he, hwe, hz, hzs⟩` from `hv`. Introduce `c`. Use `Or.inl ⟨⟨c.succ, by simp⟩, fun d => ?_⟩` and prove the remaining obligations. Proceed by induction on `d using Fin.cases with`. Consider the case `zero => simpa using (hz c).2.2.1.symm`.

Consider the case `succ d => simpa using hwe d c`.
-/
theorem mix_w' (hv : M.TieVars w e zv sv) :
    ∀ c, ((∃ d, (Fin.cons zv w : Fin (r + 1) → σ) d = w c) ∧ ∀ d, (Fin.cons zv w : Fin (r + 1) → σ) d ≠ e c) ∨
      ((∀ d, (Fin.cons zv w : Fin (r + 1) → σ) d ≠ w c) ∧ ∃ d, (Fin.cons zv w : Fin (r + 1) → σ) d = e c) := by
  obtain ⟨hw, he, hwe, hz, hzs⟩ := hv
  intro c
  refine Or.inl ⟨⟨c.succ, by simp⟩, fun d => ?_⟩
  induction d using Fin.cases with
  | zero => simpa using (hz c).2.2.1.symm
  | succ d => simpa using hwe d c

/- English proof (translation)
Take `⟨hw, he, hwe, hz, hzs⟩` from `hv`. Introduce `c`. Use `Or.inr ⟨fun d => ?_, ⟨c.succ, by simp⟩⟩` and prove the remaining obligations. Proceed by induction on `d using Fin.cases with`. Consider the case `zero => simpa using (hz c).2.1.symm`.

Consider the case `succ d => simpa using (hwe c d).symm`.
-/
theorem mix_e' (hv : M.TieVars w e zv sv) :
    ∀ c, ((∃ d, (Fin.cons sv e : Fin (r + 1) → σ) d = w c) ∧ ∀ d, (Fin.cons sv e : Fin (r + 1) → σ) d ≠ e c) ∨
      ((∀ d, (Fin.cons sv e : Fin (r + 1) → σ) d ≠ w c) ∧ ∃ d, (Fin.cons sv e : Fin (r + 1) → σ) d = e c) := by
  obtain ⟨hw, he, hwe, hz, hzs⟩ := hv
  intro c
  refine Or.inr ⟨fun d => ?_, ⟨c.succ, by simp⟩⟩
  induction d using Fin.cases with
  | zero => simpa using (hz c).2.1.symm
  | succ d => simpa using (hwe c d).symm

/- English proof (translation)
Use extensionality with `m`. Rewrite using `[coeff_pderiv_eq_coeff_add_single_mul', MvPolynomial.coeff_zero]`. Establish `h0 : coeff (m + Finsupp.single v 1) y = 0`. Assume the negation of the conclusion as `hne`. Establish `h1` using `h _ (MvPolynomial.mem_support_iff.mpr hne)`.

Simplify using `at h1`. Rewrite using `[h0, zero_mul]`.
-/
theorem pderiv_of_free (v : σ) (y : MvPolynomial σ k) (h : ∀ m ∈ y.support, m v = 0) : pderiv v y = 0 := by
  ext m
  rw [coeff_pderiv_eq_coeff_add_single_mul', MvPolynomial.coeff_zero]
  have h0 : coeff (m + Finsupp.single v 1) y = 0 := by
    by_contra hne
    have h1 := h _ (MvPolynomial.mem_support_iff.mpr hne)
    simp at h1
  rw [h0, zero_mul]

/- English proof (translation)
Apply `eulL_of_support` to reduce the goal to its premises. Introduce `m hm`. Rewrite `hm` using `[MvPolynomial.mem_support_iff, MvPolynomial.coeff_X_pow]`. Use `split_ifs at hm with h`. Rewrite using `[← h]`.

Conclude with `ha`. Conclude with `absurd rfl hm`.
-/
theorem eulL_X_pow {s : ℕ} (t : Fin s → σ) (zv : σ) (z a : ℕ) (ha : ∑ c, (Finsupp.single zv z) (t c) = a) :
    eulL t (X zv ^ z : MvPolynomial σ k) = (a : k) • X zv ^ z := by
  classical
  apply eulL_of_support
  intro m hm
  rw [MvPolynomial.mem_support_iff, MvPolynomial.coeff_X_pow] at hm
  split_ifs at hm with h
  · rw [← h]; exact ha
  · exact absurd rfl hm

section
variable {o n z : ℕ} {y : MvPolynomial σ k}

/- English proof (translation)
Rewrite using `[eulL_mul, eulL_X_pow t x0 d a ha, eulL_of_support t b f hb, smul_mul_assoc, mul_smul_comm, ← add_smul, Nat.cast_add]`.
-/
private theorem eulL_X_pow_mul_eq_smul {q : ℕ} (t : Fin q → σ) (x0 : σ) (d a b : ℕ) (f : MvPolynomial σ k)
    (ha : ∑ c, (Finsupp.single x0 d) (t c) = a) (hb : ∀ m ∈ f.support, ∑ c, m (t c) = b) :
    eulL t (X x0 ^ d * f) = ((a + b : ℕ) : k) • (X x0 ^ d * f) := by
  rw [eulL_mul, eulL_X_pow t x0 d a ha, eulL_of_support t b f hb, smul_mul_assoc,
    mul_smul_comm, ← add_smul, Nat.cast_add]

/- English proof (translation)
Take `⟨hw, he, hwe, hzz, hzs⟩` from `hv`. Establish `n1 : ∀ c, zv ≠ w c` using `fun c => (hzz c).1.symm`. Establish `n2 : ∀ c, zv ≠ e c` using `fun c => (hzz c).2.2.1.symm`. Use `⟨?_, ?_, ?_⟩` and prove the remaining obligations. Establish `h` using `eulL_X_pow_mul_eq_smul (k := k) (Fin.cons zv w : Fin (r + 1) → σ) zv z z o y ?_ ?_`.

Rewrite `h` using `[add_comm z o]`. Then use the resulting hypothesis. Rewrite using `[Fin.sum_univ_succ]`. Simplify using `[n1]`. Introduce `m hm`. Rewrite using `[Fin.sum_univ_succ]`.

Simplify using `[(hz m hm).1, (hy m hm).1]`. Establish `h` using `eulL_X_pow_mul_eq_smul (k := k) (Fin.cons sv e : Fin (r + 1) → σ) zv z 0 n y ?_ ?_`. Rewrite `h` using `[zero_add]`. Then use the resulting hypothesis. Rewrite using `[Fin.sum_univ_succ]`. Simplify using `[n2, hzs]`.

Introduce `m hm`. Rewrite using `[Fin.sum_univ_succ]`. Simplify using `[(hz m hm).2, (hy m hm).2]`. Establish `h` using `eulL_X_pow_mul_eq_smul (k := k) w zv z 0 o y ?_ ?_`. Rewrite `h` using `[zero_add]`. Then use the resulting hypothesis.

Simplify using `[n1]`. Introduce `m hm`. Conclude with `(hy m hm).1`.
-/
theorem eig_u (hv : M.TieVars w e zv sv) (hy : BiHom w e o n y) (hz : M.ZSFree zv sv y) :
    eulL (Fin.cons zv w : Fin (r + 1) → σ) (X zv ^ z * y) = ((o + z : ℕ) : k) • (X zv ^ z * y) ∧
    eulL (Fin.cons sv e : Fin (r + 1) → σ) (X zv ^ z * y) = (n : k) • (X zv ^ z * y) ∧
    eulL w (X zv ^ z * y) = (o : k) • (X zv ^ z * y) := by
  obtain ⟨hw, he, hwe, hzz, hzs⟩ := hv
  have n1 : ∀ c, zv ≠ w c := fun c => (hzz c).1.symm
  have n2 : ∀ c, zv ≠ e c := fun c => (hzz c).2.2.1.symm
  refine ⟨?_, ?_, ?_⟩
  · have h := eulL_X_pow_mul_eq_smul (k := k) (Fin.cons zv w : Fin (r + 1) → σ) zv z z o y ?_ ?_
    · rwa [add_comm z o] at h
    · rw [Fin.sum_univ_succ]
      simp [n1]
    · intro m hm
      rw [Fin.sum_univ_succ]
      simp [(hz m hm).1, (hy m hm).1]
  · have h := eulL_X_pow_mul_eq_smul (k := k) (Fin.cons sv e : Fin (r + 1) → σ) zv z 0 n y ?_ ?_
    · rwa [zero_add] at h
    · rw [Fin.sum_univ_succ]
      simp [n2, hzs]
    · intro m hm
      rw [Fin.sum_univ_succ]
      simp [(hz m hm).2, (hy m hm).2]
  · have h := eulL_X_pow_mul_eq_smul (k := k) w zv z 0 o y ?_ ?_
    · rwa [zero_add] at h
    · simp [n1]
    · intro m hm
      exact (hy m hm).1

/- English proof (translation)
Rewrite using `[pderiv_X_pow_mul_of_ne hv.2.2.2.2 z y, pderiv_of_free sv y (fun m hm => (hz m hm).2), mul_zero]`.
-/
theorem pderiv_sv_u (hv : M.TieVars w e zv sv) (hz : M.ZSFree zv sv y) :
    pderiv sv (X zv ^ z * y) = 0 := by
  rw [pderiv_X_pow_mul_of_ne hv.2.2.2.2 z y, pderiv_of_free sv y (fun m hm => (hz m hm).2), mul_zero]

/- English proof (translation)
Establish `hsplit : ∀ g : MvPolynomial σ k, Formalism.GM.tieF (Fin.cons zv w : Fin (r + 1) → σ) (Fin.cons sv e) g = pderiv zv (pderiv sv g) + Formalism.GM.tieF w e g`. Introduce `g`. Rewrite using `[← tieFh_eq]`. Both sides reduce to the same expression. Rewrite using `[hsplit, ← tieF_pow_pderiv, pderiv_sv_u hv hz, map_zero, map_zero, zero_add, pow_succ' (Formalism.GM.tieF w e) l, Module.End.mul_apply]`.
-/
theorem Fh_v (hv : M.TieVars w e zv sv) (hz : M.ZSFree zv sv y) (l : ℕ) :
    tieF (Fin.cons zv w : Fin (r + 1) → σ) (Fin.cons sv e) ((tieF w e ^ l) (X zv ^ z * y)) =
      (tieF w e ^ (l + 1)) (X zv ^ z * y) := by
  have hsplit : ∀ g : MvPolynomial σ k, Formalism.GM.tieF (Fin.cons zv w : Fin (r + 1) → σ) (Fin.cons sv e) g =
      pderiv zv (pderiv sv g) + Formalism.GM.tieF w e g := by
    intro g
    rw [← tieFh_eq]
    rfl
  rw [hsplit, ← tieF_pow_pderiv, pderiv_sv_u hv hz, map_zero, map_zero, zero_add,
    pow_succ' (Formalism.GM.tieF w e) l, Module.End.mul_apply]

/- English proof (translation)
Proceed by induction on `l with`. Consider the case `zero => simp`. Consider the case `succ l ih`. Rewrite using `[pow_succ' (Formalism.GM.tieF (k := k) (Fin.cons zv w : Fin (r + 1) → σ) (Fin.cons sv e)) l, Module.End.mul_apply, ih, Fh_v hv hz l]`.
-/
theorem Fh_pow_u (hv : M.TieVars w e zv sv) (hz : M.ZSFree zv sv y) (l : ℕ) :
    (tieF (Fin.cons zv w : Fin (r + 1) → σ) (Fin.cons sv e) ^ l) (X zv ^ z * y) =
      (tieF w e ^ l) (X zv ^ z * y) := by
  induction l with
  | zero => simp
  | succ l ih =>
    rw [pow_succ' (Formalism.GM.tieF (k := k) (Fin.cons zv w : Fin (r + 1) → σ) (Fin.cons sv e)) l, Module.End.mul_apply, ih,
      Fh_v hv hz l]

/- English proof (translation)
Establish `h0` using `eig_u (z := z) hv hy hz`. Conclude with `⟨eulL_tieF_pow _ (tv_w hv) w e (mix_w' hv) _ _ h0.1 l, eulL_tieF_pow _ (tv_e hv) w e (mix_e' hv) _ _ h0.2.1 l, eulL_tieF_pow _ hv.1 w e (mix_w hv) _ _ h0.2.2 l⟩`.
-/
theorem eig_v (hv : M.TieVars w e zv sv) (hy : BiHom w e o n y) (hz : M.ZSFree zv sv y) (l : ℕ) :
    eulL (Fin.cons zv w : Fin (r + 1) → σ) ((tieF w e ^ l) (X zv ^ z * y)) =
      (((o + z : ℕ) : k) - l) • (tieF w e ^ l) (X zv ^ z * y) ∧
    eulL (Fin.cons sv e : Fin (r + 1) → σ) ((tieF w e ^ l) (X zv ^ z * y)) =
      ((n : k) - l) • (tieF w e ^ l) (X zv ^ z * y) ∧
    eulL w ((tieF w e ^ l) (X zv ^ z * y)) = ((o : k) - l) • (tieF w e ^ l) (X zv ^ z * y) := by
  have h0 := eig_u (z := z) hv hy hz
  exact ⟨eulL_tieF_pow _ (tv_w hv) w e (mix_w' hv) _ _ h0.1 l,
    eulL_tieF_pow _ (tv_e hv) w e (mix_e' hv) _ _ h0.2.1 l,
    eulL_tieF_pow _ hv.1 w e (mix_w hv) _ _ h0.2.2 l⟩

/- English proof (translation)
The claim follows from `eq_zero_of_eulL w o (o + 1) (Nat.lt_succ_self o) _ (eig_v (z := z) hv hy hz (o + 1)).2.2`.
-/
theorem v_top [CharZero k] (hv : M.TieVars w e zv sv) (hy : BiHom w e o n y) (hz : M.ZSFree zv sv y) :
    (tieF w e ^ (o + 1)) (X zv ^ z * y) = 0 :=
  eq_zero_of_eulL w o (o + 1) (Nat.lt_succ_self o) _
    (eig_v (z := z) hv hy hz (o + 1)).2.2

/- English proof (translation)
Establish `hw'` using `tv_w hv`. Establish `he'` using `tv_e hv`. Establish `hd` using `tv_we hv`. Prove the components needed by the constructor for the conclusion. Rewrite using `[map_sum, Finset.smul_sum]`.

Use `Finset.sum_congr rfl (fun l _ => ?_)` and prove the remaining obligations. Establish `h1` using `eig_v (z := z) hv hy hz l`. Establish `h2` using `(eulL_tieE_pow hw' he' hd _ _ _ h1.1 h1.2.1 l).1`. Rewrite using `[map_smul, h2, sub_add_cancel, smul_comm]`. Rewrite using `[map_sum, Finset.smul_sum]`.

Use `Finset.sum_congr rfl (fun l _ => ?_)` and prove the remaining obligations. Establish `h1` using `eig_v (z := z) hv hy hz l`. Establish `h2` using `(eulL_tieE_pow hw' he' hd _ _ _ h1.1 h1.2.1 l).2`. Rewrite using `[map_smul, h2, sub_add_cancel, smul_comm]`.
-/
theorem eig_P (hv : M.TieVars w e zv sv) (hy : BiHom w e o n y) (hz : M.ZSFree zv sv y) (c : ℕ → k) :
    eulL (Fin.cons zv w : Fin (r + 1) → σ)
      (∑ l ∈ range (o + 1), c l • (tieE (Fin.cons zv w : Fin (r + 1) → σ) (Fin.cons sv e) ^ l)
        ((tieF w e ^ l) (X zv ^ z * y))) =
      ((o + z : ℕ) : k) • (∑ l ∈ range (o + 1), c l • (tieE (Fin.cons zv w : Fin (r + 1) → σ) (Fin.cons sv e) ^ l)
        ((tieF w e ^ l) (X zv ^ z * y))) ∧
    eulL (Fin.cons sv e : Fin (r + 1) → σ)
      (∑ l ∈ range (o + 1), c l • (tieE (Fin.cons zv w : Fin (r + 1) → σ) (Fin.cons sv e) ^ l)
        ((tieF w e ^ l) (X zv ^ z * y))) =
      (n : k) • (∑ l ∈ range (o + 1), c l • (tieE (Fin.cons zv w : Fin (r + 1) → σ) (Fin.cons sv e) ^ l)
        ((tieF w e ^ l) (X zv ^ z * y))) := by
  have hw' := tv_w hv
  have he' := tv_e hv
  have hd := tv_we hv
  constructor
  · rw [map_sum, Finset.smul_sum]
    refine Finset.sum_congr rfl (fun l _ => ?_)
    have h1 := eig_v (z := z) hv hy hz l
    have h2 := (eulL_tieE_pow hw' he' hd _ _ _ h1.1 h1.2.1 l).1
    rw [map_smul, h2, sub_add_cancel, smul_comm]
  · rw [map_sum, Finset.smul_sum]
    refine Finset.sum_congr rfl (fun l _ => ?_)
    have h1 := eig_v (z := z) hv hy hz l
    have h2 := (eulL_tieE_pow hw' he' hd _ _ _ h1.1 h1.2.1 l).2
    rw [map_smul, h2, sub_add_cancel, smul_comm]

end

end Formalism.GM.ProjS

namespace Formalism.GM.ProjS

open MvPolynomial Finset

/- English proof (translation)
Use `set A := o + n + r + z - 1 with hAdef`. Establish `hjA : j + 1 ≤ A` using `by omega`. Establish `hc1 : (A.choose j : k) ≠ 0` using `Nat.cast_ne_zero.mpr (Nat.choose_pos (by omega)).ne'`. Establish `hf1 : (j.factorial : k) ≠ 0` using `Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero j)`. Establish `hch : (A.choose (j + 1) : k) * ((j : k) + 1) = (A.choose j : k) * ((A : k) - j)`.

Establish `h0` using `Nat.choose_succ_right_eq A j`. Establish `h' : ((A.choose (j + 1) * (j + 1) : ℕ) : k) = ((A.choose j * (A - j) : ℕ) : k)` using `by rw [h0]`. Move the coercions through the operations in `[Nat.cast_sub (by omega : j ≤ A)] at h'`. Conclude with `h'`. Establish `hbr : (((o + z : ℕ) : k) - ((j + 1 : ℕ) : k) + ((n : k) - ((j + 1 : ℕ) : k)) + ((r + 1 : ℕ) : k) + j) = (A : k) - j`.

Establish `hA1 : (A : k) + 1 = (o : k) + n + r + z`. Establish `h2 : A + 1 = o + n + r + z` using `by omega`. Conclude with `h2` after adjusting the coercions. Use `push_cast`. Take the linear combination `-hA1`.

Establish `hden : (((j + 1).factorial : k) ^ 2) * (A.choose (j + 1) : k) = (((j : k) + 1) * ((A : k) - j)) * ((j.factorial : k) ^ 2 * (A.choose j : k))`. Rewrite using `[Nat.factorial_succ]`. Use `push_cast`. Take the linear combination `(((j : k) + 1) * (j.factorial : k) ^ 2) * hch`. Establish `hne : ((j : k) + 1) * ((A : k) - j) ≠ 0`.

Use `mul_ne_zero ?_ ?_` and prove the remaining obligations. Conclude with `Nat.succ_ne_zero j` after adjusting the coercions. Use `sub_ne_zero.mpr ?_` and prove the remaining obligations. Conclude with `(show A ≠ j by omega)` after adjusting the coercions. Establish `hD : (j.factorial : k) ^ 2 * (A.choose j : k) ≠ 0` using `mul_ne_zero (pow_ne_zero 2 hf1) hc1`.

Establish `key : ∀ (a E D : k), E ≠ 0 → a / (E * D) * E = a / D`. Introduce `a E D hE`. Rewrite using `[div_mul_eq_mul_div, mul_comm E D, mul_div_mul_right _ _ hE]`. Rewrite using `[hbr, hden, key _ _ _ hne]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem coef_cancel {k : Type} [Field k] [CharZero k] (o n r z j : ℕ) (hr : 1 ≤ r) (hj : j < o) :
    ((-1 : k) ^ j) / (((j.factorial : k) ^ 2) * ((o + n + r + z - 1).choose j : k)) +
      ((-1 : k) ^ (j + 1)) / ((((j + 1).factorial : k) ^ 2) * ((o + n + r + z - 1).choose (j + 1) : k)) *
        (((j : k) + 1) * (((o + z : ℕ) : k) - ((j + 1 : ℕ) : k) + ((n : k) - ((j + 1 : ℕ) : k)) +
          ((r + 1 : ℕ) : k) + j)) = 0 := by
  set A := o + n + r + z - 1 with hAdef
  have hjA : j + 1 ≤ A := by omega
  have hc1 : (A.choose j : k) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.choose_pos (by omega)).ne'
  have hf1 : (j.factorial : k) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero j)
  have hch : (A.choose (j + 1) : k) * ((j : k) + 1) = (A.choose j : k) * ((A : k) - j) := by
    have h0 := Nat.choose_succ_right_eq A j
    have h' : ((A.choose (j + 1) * (j + 1) : ℕ) : k) = ((A.choose j * (A - j) : ℕ) : k) := by rw [h0]
    push_cast [Nat.cast_sub (by omega : j ≤ A)] at h'
    exact h'
  have hbr : (((o + z : ℕ) : k) - ((j + 1 : ℕ) : k) + ((n : k) - ((j + 1 : ℕ) : k)) + ((r + 1 : ℕ) : k) + j) =
      (A : k) - j := by
    have hA1 : (A : k) + 1 = (o : k) + n + r + z := by
      have h2 : A + 1 = o + n + r + z := by omega
      exact_mod_cast h2
    push_cast
    linear_combination -hA1
  have hden : (((j + 1).factorial : k) ^ 2) * (A.choose (j + 1) : k) =
      (((j : k) + 1) * ((A : k) - j)) * ((j.factorial : k) ^ 2 * (A.choose j : k)) := by
    rw [Nat.factorial_succ]
    push_cast
    linear_combination (((j : k) + 1) * (j.factorial : k) ^ 2) * hch
  have hne : ((j : k) + 1) * ((A : k) - j) ≠ 0 := by
    refine mul_ne_zero ?_ ?_
    · exact_mod_cast Nat.succ_ne_zero j
    · refine sub_ne_zero.mpr ?_
      exact_mod_cast (show A ≠ j by omega)
  have hD : (j.factorial : k) ^ 2 * (A.choose j : k) ≠ 0 := mul_ne_zero (pow_ne_zero 2 hf1) hc1
  have key : ∀ (a E D : k), E ≠ 0 → a / (E * D) * E = a / D := by
    intro a E D hE
    rw [div_mul_eq_mul_div, mul_comm E D, mul_div_mul_right _ _ hE]
  rw [hbr, hden, key _ _ _ hne]
  ring

end Formalism.GM.ProjS

namespace Formalism.GM.ProjS

open MvPolynomial Finset

variable {k σ : Type} [Field k] {r : ℕ} {w e : Fin r → σ} {zv sv : σ}

/- English proof (translation)
Unfold `Formalism.GM.M.tieP`. Rewrite using `[tieEh_eq]`.
-/
theorem tieP_eq (o n z : ℕ) (y : MvPolynomial σ k) :
    M.tieP w e zv sv o n z y = ∑ l ∈ range (o + 1),
      (((-1 : k) ^ l) / (((l.factorial : k) ^ 2) * ((o + n + r + z - 1).choose l : k))) •
        (tieE (Fin.cons zv w : Fin (r + 1) → σ) (Fin.cons sv e) ^ l) ((tieF w e ^ l) (X zv ^ z * y)) := by
  unfold Formalism.GM.M.tieP
  rw [tieEh_eq]

/- English proof (translation)
Establish `h1 : ∑ j ∈ range o, c (j + 1) • F (j + 1) + c 0 • F 0 = ∑ j ∈ range o, c j • F j`. Rewrite using `[← Finset.sum_range_succ' (fun j => c j • F j), Finset.sum_range_succ, hF, smul_zero, add_zero]`. Simplify using `only [smul_add, Finset.sum_add_distrib, smul_smul]`. Rewrite using `[add_right_comm, h1, ← Finset.sum_add_distrib]`. Use `Finset.sum_eq_zero (fun j hj => ?_)` and prove the remaining obligations.

Rewrite using `[← add_smul, hc j (Finset.mem_range.mp hj), zero_smul]`.
-/
private theorem sum_range_smul_add_smul_eq_zero_of_recurrence {M : Type} [AddCommGroup M] [Module k M] (c d : ℕ → k) (F : ℕ → M) (o : ℕ)
    (hF : F o = 0) (hc : ∀ j < o, c j + c (j + 1) * d j = 0) :
    ∑ j ∈ range o, c (j + 1) • (F (j + 1) + d j • F j) + c 0 • F 0 = 0 := by
  have h1 : ∑ j ∈ range o, c (j + 1) • F (j + 1) + c 0 • F 0 = ∑ j ∈ range o, c j • F j := by
    rw [← Finset.sum_range_succ' (fun j => c j • F j), Finset.sum_range_succ, hF, smul_zero, add_zero]
  simp only [smul_add, Finset.sum_add_distrib, smul_smul]
  rw [add_right_comm, h1, ← Finset.sum_add_distrib]
  refine Finset.sum_eq_zero (fun j hj => ?_)
  rw [← add_smul, hc j (Finset.mem_range.mp hj), zero_smul]

/- English proof (translation)
Establish `hw'` using `tv_w hv`. Establish `he'` using `tv_e hv`. Establish `hd` using `tv_we hv`. Establish `hT0 : Formalism.GM.tieF (k` using `k) (Fin.cons zv w : Fin (r + 1) → σ) (Fin.cons sv e) ((Formalism.GM.tieE (Fin.cons zv w : Fin (r + 1) → σ) (Fin.cons sv e) ^ 0) ((Formalism.GM.tieF w e ^ 0) (X zv ^ z * y))) = (Formalism.GM.tieE (Fin.cons zv w : Fin (r + 1) → σ) (Fin.cons sv e) ^ 0) ((Formalism.GM.tieF w e ^ (0 + …`. Establish `h0` using `Fh_v (z := z) hv hz 0`.

Simplify using `using h0`. Establish `hTs : ∀ j : ℕ, Formalism.GM.tieF (k` using `k) (Fin.cons zv w : Fin (r + 1) → σ) (Fin.cons sv e) ((Formalism.GM.tieE (Fin.cons zv w : Fin (r + 1) → σ) (Fin.cons sv e) ^ (j + 1)) ((Formalism.GM.tieF w e ^ (j + 1)) (X zv ^ z * y))) = (Formalism.GM.tieE (Fin.cons zv w : Fin (r + 1) → σ) (Fin.cons sv e) ^ (j + 1)) ((Formalism. …`. Introduce `j`. Establish `h1` using `eig_v (z := z) hv hy hz (j + 1)`. Rewrite using `[F_E_pow_comm hw' he' hd _ _ _ h1.1 h1.2.1 j, Fh_v (z := z) hv hz (j + 1)]`.

Establish `hF : (Formalism.GM.tieE (Fin.cons zv w : Fin (r + 1) → σ) (Fin.cons sv e) ^ o) ((Formalism.GM.tieF w e ^ (o + 1)) (X zv ^ z * y)) = 0`. Rewrite using `[v_top hv hy hz, map_zero]`. Rewrite using `[tieP_eq, map_sum, Finset.sum_range_succ']`. Simplify using `only [map_smul, hTs, hT0]`. Conclude with `sum_range_smul_add_smul_eq_zero_of_recurrence (fun l => ((-1 : k) ^ l) / (((l.factorial : k) ^ 2) * ((o + n + r + z - 1).choose l : k))) (fun j => ((j : k) + 1) * (((o + z : ℕ) : k) - ((j + 1 : ℕ) : k) + ((n : k) - ((j + 1 : ℕ) : k)) + ((r + 1 : ℕ) : k) + j)) (fun j => (Formalism …`.
-/
theorem fh_P [CharZero k] (hv : M.TieVars w e zv sv) (hr : 1 ≤ r) {o n z : ℕ} {y : MvPolynomial σ k}
    (hy : BiHom w e o n y) (hz : M.ZSFree zv sv y) :
    tieF (Fin.cons zv w : Fin (r + 1) → σ) (Fin.cons sv e) (M.tieP w e zv sv o n z y) = 0 := by
  have hw' := tv_w hv
  have he' := tv_e hv
  have hd := tv_we hv
  have hT0 : Formalism.GM.tieF (k := k) (Fin.cons zv w : Fin (r + 1) → σ) (Fin.cons sv e)
      ((Formalism.GM.tieE (Fin.cons zv w : Fin (r + 1) → σ) (Fin.cons sv e) ^ 0) ((Formalism.GM.tieF w e ^ 0) (X zv ^ z * y))) =
      (Formalism.GM.tieE (Fin.cons zv w : Fin (r + 1) → σ) (Fin.cons sv e) ^ 0) ((Formalism.GM.tieF w e ^ (0 + 1)) (X zv ^ z * y)) := by
    have h0 := Fh_v (z := z) hv hz 0
    simpa using h0
  have hTs : ∀ j : ℕ, Formalism.GM.tieF (k := k) (Fin.cons zv w : Fin (r + 1) → σ) (Fin.cons sv e)
      ((Formalism.GM.tieE (Fin.cons zv w : Fin (r + 1) → σ) (Fin.cons sv e) ^ (j + 1)) ((Formalism.GM.tieF w e ^ (j + 1)) (X zv ^ z * y))) =
      (Formalism.GM.tieE (Fin.cons zv w : Fin (r + 1) → σ) (Fin.cons sv e) ^ (j + 1)) ((Formalism.GM.tieF w e ^ (j + 1 + 1)) (X zv ^ z * y)) +
      (((j : k) + 1) * (((o + z : ℕ) : k) - ((j + 1 : ℕ) : k) + ((n : k) - ((j + 1 : ℕ) : k)) +
        ((r + 1 : ℕ) : k) + j)) •
        (Formalism.GM.tieE (Fin.cons zv w : Fin (r + 1) → σ) (Fin.cons sv e) ^ j) ((Formalism.GM.tieF w e ^ (j + 1)) (X zv ^ z * y)) := by
    intro j
    have h1 := eig_v (z := z) hv hy hz (j + 1)
    rw [F_E_pow_comm hw' he' hd _ _ _ h1.1 h1.2.1 j, Fh_v (z := z) hv hz (j + 1)]
  have hF : (Formalism.GM.tieE (Fin.cons zv w : Fin (r + 1) → σ) (Fin.cons sv e) ^ o)
      ((Formalism.GM.tieF w e ^ (o + 1)) (X zv ^ z * y)) = 0 := by
    rw [v_top hv hy hz, map_zero]
  rw [tieP_eq, map_sum, Finset.sum_range_succ']
  simp only [map_smul, hTs, hT0]
  exact sum_range_smul_add_smul_eq_zero_of_recurrence
    (fun l => ((-1 : k) ^ l) / (((l.factorial : k) ^ 2) * ((o + n + r + z - 1).choose l : k)))
    (fun j => ((j : k) + 1) * (((o + z : ℕ) : k) - ((j + 1 : ℕ) : k) + ((n : k) - ((j + 1 : ℕ) : k)) +
        ((r + 1 : ℕ) : k) + j))
    (fun j => (Formalism.GM.tieE (Fin.cons zv w : Fin (r + 1) → σ) (Fin.cons sv e) ^ j)
      ((Formalism.GM.tieF w e ^ (j + 1)) (X zv ^ z * y))) o hF
    (fun j hj => coef_cancel o n r z j hr hj)

end Formalism.GM.ProjS

namespace Formalism.GM.ProjS

open MvPolynomial Finset

variable {k σ : Type} [Field k] {r : ℕ} {w e : Fin r → σ} {zv sv : σ}

/- English proof (translation)
Rewrite using `[tieP_eq, fockK_sum_left, Finset.sum_range_succ', Finset.sum_eq_zero, zero_add]`. Simplify using the standard rewrite rules. Introduce `i _`. Rewrite using `[fockK_smul_left, fockK_tieE_pow, pow_succ (Formalism.GM.tieF (k := k) (Fin.cons zv w : Fin (r + 1) → σ) (Fin.cons sv e)) i, Module.End.mul_apply, hQ, map_zero, fockK_zero_right, mul_zero]`.
-/
theorem fockK_P_left (o n z : ℕ) (y Q : MvPolynomial σ k)
    (hQ : tieF (Fin.cons zv w : Fin (r + 1) → σ) (Fin.cons sv e) Q = 0) :
    M.fockK (M.tieP w e zv sv o n z y) Q = M.fockK (X zv ^ z * y) Q := by
  rw [tieP_eq, fockK_sum_left, Finset.sum_range_succ', Finset.sum_eq_zero, zero_add]
  · simp
  · intro i _
    rw [fockK_smul_left, fockK_tieE_pow,
      pow_succ (Formalism.GM.tieF (k := k) (Fin.cons zv w : Fin (r + 1) → σ) (Fin.cons sv e)) i, Module.End.mul_apply, hQ,
      map_zero, fockK_zero_right, mul_zero]

/- English proof (translation)
Proceed by induction on `j with`. Consider the case `zero => simp`. Consider the case `succ j ih`. Rewrite using `[pow_succ' (Formalism.GM.tieE W E) j, Module.End.mul_apply, ih, Formalism.GM.tieE_apply', pow_succ' (∑ d, X (W d) * X (E d) : MvPolynomial σ k) j, mul_assoc]`.
-/
private theorem tieE_pow_apply_eq_sum_X_mul_X_pow_mul {q : ℕ} (W E : Fin q → σ) (j : ℕ) (g : MvPolynomial σ k) :
    (Formalism.GM.tieE W E ^ j) g = (∑ d, X (W d) * X (E d)) ^ j * g := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [pow_succ' (Formalism.GM.tieE W E) j, Module.End.mul_apply, ih, Formalism.GM.tieE_apply',
      pow_succ' (∑ d, X (W d) * X (E d) : MvPolynomial σ k) j, mul_assoc]

/- English proof (translation)
Simplify using `only [Formalism.GM.tiePhi, LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.comp_apply]`.
-/
private theorem tiePhi_eq_sum_range_neg_one_pow_div_tieE_pow_tieF_pow {q : ℕ} (W E : Fin q → σ) (o n z : ℕ) (g : MvPolynomial σ k) :
    Formalism.GM.tiePhi W E o n z g = ∑ l ∈ range (o + 1),
      (((-1 : k) ^ l) / (((l.factorial : k) ^ 2) * ((o + n + q + z - 1).choose l : k))) •
        (Formalism.GM.tieE W E ^ l) ((Formalism.GM.tieF W E ^ l) g) := by
  simp only [Formalism.GM.tiePhi, LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.comp_apply]

/- English proof (translation)
Establish `hzz : ∀ c, w c ≠ zv ∧ e c ≠ zv` using `fun c => ⟨(hv.2.2.2.1 c).1, (hv.2.2.2.1 c).2.2.1⟩`. Rewrite using `[fockK_P_left o n z y _ (fh_P (z := z) hv hr hy' hz')]`. Establish `step1 : Formalism.GM.M.fockK (X zv ^ z * y) (Formalism.GM.M.tieP w e zv sv o n z y') = Formalism.GM.M.fockK (X zv ^ z * y) (Formalism.GM.tiePhi w e o n z (X zv ^ z * y'))`. Rewrite using `[tieP_eq, tiePhi_eq_sum_range_neg_one_pow_div_tieE_pow_tieF_pow, fockK_sum_right, fockK_sum_right]`. Use `Finset.sum_congr rfl (fun l _ => ?_)` and prove the remaining obligations.

Rewrite using `[fockK_smul_right, fockK_smul_right, fockK_tieE_pow_right, fockK_tieE_pow_right, Fh_pow_u hv hz l]`. Establish `hPX : Formalism.GM.tiePhi w e o n z (X zv ^ z * y') = X zv ^ z * Formalism.GM.tiePhi w e o n z y'`. Rewrite using `[tiePhi_eq_sum_range_neg_one_pow_div_tieE_pow_tieF_pow, tiePhi_eq_sum_range_neg_one_pow_div_tieE_pow_tieF_pow, Finset.mul_sum]`. Use `Finset.sum_congr rfl (fun l _ => ?_)` and prove the remaining obligations. Rewrite using `[tieF_pow_X_pow_mul w e zv hzz z y' l, tieE_pow_apply_eq_sum_X_mul_X_pow_mul, tieE_pow_apply_eq_sum_X_mul_X_pow_mul, mul_smul_comm, mul_left_comm]`.

Establish `hRs : pderiv zv (∑ d, X (w d) * X (e d) : MvPolynomial σ k) = 0`. Rewrite using `[map_sum]`. Use `Finset.sum_eq_zero (fun d _ => ?_)` and prove the remaining obligations. Rewrite using `[MvPolynomial.pderiv_mul, mvPolynomial_pderiv_X_eq_zero_of_ne (hzz d).1, mvPolynomial_pderiv_X_eq_zero_of_ne (hzz d).2, zero_mul, mul_zero, add_zero]`. Establish `hPd : pderiv zv (Formalism.GM.tiePhi w e o n z y') = 0`.

Rewrite using `[tiePhi_eq_sum_range_neg_one_pow_div_tieE_pow_tieF_pow, map_sum]`. Use `Finset.sum_eq_zero (fun l _ => ?_)` and prove the remaining obligations. Rewrite using `[Derivation.map_smul, tieE_pow_apply_eq_sum_X_mul_X_pow_mul, MvPolynomial.pderiv_mul, Derivation.leibniz_pow, hRs, smul_zero, smul_zero, zero_mul, zero_add, ← tieF_pow_pderiv, pderiv_of_free zv y' (fun m hm => (hz' m hm).1), map_zero, mul_zero, smul_zero]`. Rewrite using `[step1, hPX, fockK_X_pow_mul, pderiv_pow_X_pow_mul zv _ hPd z, fockK_smul_right]`.
-/
theorem fockForm_augLift_augLift [CharZero k] (hv : M.TieVars w e zv sv) (hr : 1 ≤ r) {o n z : ℕ} {y y' : MvPolynomial σ k}
    (_hy : BiHom w e o n y) (hy' : BiHom w e o n y') (hz : M.ZSFree zv sv y) (hz' : M.ZSFree zv sv y') :
    M.fockK (M.tieP w e zv sv o n z y) (M.tieP w e zv sv o n z y') =
      (z.factorial : k) * M.fockK y (tiePhi w e o n z y') := by
  have hzz : ∀ c, w c ≠ zv ∧ e c ≠ zv := fun c => ⟨(hv.2.2.2.1 c).1, (hv.2.2.2.1 c).2.2.1⟩
  rw [fockK_P_left o n z y _ (fh_P (z := z) hv hr hy' hz')]
  have step1 : Formalism.GM.M.fockK (X zv ^ z * y) (Formalism.GM.M.tieP w e zv sv o n z y') =
      Formalism.GM.M.fockK (X zv ^ z * y) (Formalism.GM.tiePhi w e o n z (X zv ^ z * y')) := by
    rw [tieP_eq, tiePhi_eq_sum_range_neg_one_pow_div_tieE_pow_tieF_pow, fockK_sum_right, fockK_sum_right]
    refine Finset.sum_congr rfl (fun l _ => ?_)
    rw [fockK_smul_right, fockK_smul_right, fockK_tieE_pow_right, fockK_tieE_pow_right,
      Fh_pow_u hv hz l]
  have hPX : Formalism.GM.tiePhi w e o n z (X zv ^ z * y') = X zv ^ z * Formalism.GM.tiePhi w e o n z y' := by
    rw [tiePhi_eq_sum_range_neg_one_pow_div_tieE_pow_tieF_pow, tiePhi_eq_sum_range_neg_one_pow_div_tieE_pow_tieF_pow, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun l _ => ?_)
    rw [tieF_pow_X_pow_mul w e zv hzz z y' l, tieE_pow_apply_eq_sum_X_mul_X_pow_mul, tieE_pow_apply_eq_sum_X_mul_X_pow_mul, mul_smul_comm,
      mul_left_comm]
  have hRs : pderiv zv (∑ d, X (w d) * X (e d) : MvPolynomial σ k) = 0 := by
    rw [map_sum]
    refine Finset.sum_eq_zero (fun d _ => ?_)
    rw [MvPolynomial.pderiv_mul, mvPolynomial_pderiv_X_eq_zero_of_ne (hzz d).1, mvPolynomial_pderiv_X_eq_zero_of_ne (hzz d).2, zero_mul, mul_zero, add_zero]
  have hPd : pderiv zv (Formalism.GM.tiePhi w e o n z y') = 0 := by
    rw [tiePhi_eq_sum_range_neg_one_pow_div_tieE_pow_tieF_pow, map_sum]
    refine Finset.sum_eq_zero (fun l _ => ?_)
    rw [Derivation.map_smul, tieE_pow_apply_eq_sum_X_mul_X_pow_mul, MvPolynomial.pderiv_mul, Derivation.leibniz_pow, hRs, smul_zero,
      smul_zero, zero_mul, zero_add, ← tieF_pow_pderiv,
      pderiv_of_free zv y' (fun m hm => (hz' m hm).1), map_zero, mul_zero, smul_zero]
  rw [step1, hPX, fockK_X_pow_mul, pderiv_pow_X_pow_mul zv _ hPd z, fockK_smul_right]

/- English proof (translation)
Rewrite using `[fockK_tieE_pow, Formalism.GM.F_pow_E_pow hW hE hWE u' a b N0 (by rw [← eulL_apply W u']; exact hWu') (by rw [← eulL_apply E u']; exact hEu') hu' hN i l, fockK_smul_right]`. Use `split_ifs with h`. Substitute `h` using the available equality. Rewrite using `[Nat.sub_self, pow_zero, Module.End.one_apply, Nat.descFactorial_self]`. Take `⟨m, hm⟩ : ∃ m, l - i = m + 1` from `⟨l - i - 1, by omega⟩`.

Rewrite using `[hm, pow_succ' (Formalism.GM.tieE W E) m, Module.End.mul_apply, fockK_symm u, fockK_tieE, hu, fockK_zero_right, mul_zero]`.
-/
private theorem fockK_tieE_pow_tieE_pow_eq_ite {q : ℕ} {W E : Fin q → σ} (hW : Function.Injective W)
    (hE : Function.Injective E) (hWE : ∀ c d, W c ≠ E d) (a b N0 : ℕ) (hN : a + b + q = N0 + 1)
    (u u' : MvPolynomial σ k) (hu' : Formalism.GM.tieF W E u' = 0) (hWu' : eulL W u' = (a : k) • u')
    (hEu' : eulL E u' = (b : k) • u') (hu : Formalism.GM.tieF W E u = 0) (i l : ℕ) (hil : i ≤ l) :
    Formalism.GM.M.fockK ((Formalism.GM.tieE W E ^ i) u) ((Formalism.GM.tieE W E ^ l) u') =
      if i = l then ((i.factorial * (N0 + i).descFactorial i : ℕ) : k) * Formalism.GM.M.fockK u u' else 0 := by
  rw [fockK_tieE_pow, Formalism.GM.F_pow_E_pow hW hE hWE u' a b N0 (by rw [← eulL_apply W u']; exact hWu')
    (by rw [← eulL_apply E u']; exact hEu') hu' hN i l, fockK_smul_right]
  split_ifs with h
  · subst h
    rw [Nat.sub_self, pow_zero, Module.End.one_apply, Nat.descFactorial_self]
  · obtain ⟨m, hm⟩ : ∃ m, l - i = m + 1 := ⟨l - i - 1, by omega⟩
    rw [hm, pow_succ' (Formalism.GM.tieE W E) m, Module.End.mul_apply, fockK_symm u, fockK_tieE, hu,
      fockK_zero_right, mul_zero]

/- English proof (translation)
Establish `hw'` using `tv_w hv`. Establish `he'` using `tv_e hv`. Establish `hd` using `tv_we hv`. Establish `hL` using `fh_P (z := z) hv hr hy hz`. Establish `hL'` using `fh_P (z := z) hv hr hy' hz'`.

Establish `hE : eulL (Fin.cons zv w : Fin (r + 1) → σ) (Formalism.GM.M.tieP w e zv sv o n z y) = ((o + z : ℕ) : k) • Formalism.GM.M.tieP w e zv sv o n z y ∧ eulL (Fin.cons sv e : Fin (r + 1) → σ) (Formalism.GM.M.tieP w e zv sv o n z y) = (n : k) • Formalism.GM.M.tieP w e zv sv o n z y`. Rewrite using `[tieP_eq]`. Conclude with `eig_P (z := z) hv hy hz _`. Establish `hE' : eulL (Fin.cons zv w : Fin (r + 1) → σ) (Formalism.GM.M.tieP w e zv sv o n z y') = ((o + z : ℕ) : k) • Formalism.GM.M.tieP w e zv sv o n z y' ∧ eulL (Fin.cons sv e : Fin (r + 1) → σ) (Formalism.GM.M.tieP w e zv sv o n z y') = (n : k) • Formalism.GM.M.tieP w e zv sv o n z y'`. Rewrite using `[tieP_eq]`.

Conclude with `eig_P (z := z) hv hy' hz' _`. Establish `hN : (o + z) + n + (r + 1) = (o + z + n + r) + 1` using `by omega`. Rewrite using `[tieEh_eq, fockK_smul_left, fockK_smul_right]`. Distinguish the cases in `h : j = j'`. Substitute `j'` using the available equality.

Rewrite using `[fockK_tieE_pow_tieE_pow_eq_ite hw' he' hd (o + z) n (o + z + n + r) hN _ _ hL' hE'.1 hE'.2 hL j j le_rfl, if_pos rfl, if_pos rfl, fockForm_augLift_augLift (z := z) hv hr hy hy' hz hz']`. Establish `h1 : o + n + r + z + 1 + j - 1 = o + z + n + r + j` using `by omega`. Establish `hf : (j.factorial : k) ≠ 0` using `Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero j)`. Establish `e1 : (j.factorial : k)⁻¹ * (j.factorial : k) = 1` using `inv_mul_cancel₀ hf`. Rewrite using `[h1, Nat.descFactorial_eq_factorial_mul_choose]`.

Use `push_cast`. Take the linear combination `(((j.factorial : k)⁻¹ * (j.factorial : k) + 1) * (((o + z + n + r + j).choose j : ℕ) : k) * (z.factorial : k) * Formalism.GM.M.fockK y (Formalism.GM.tiePhi w e o n z y')) * e1`. Rewrite using `[if_neg h]`. Break down `lt_or_gt_of_ne h with hlt | hgt` into its components or cases. Rewrite using `[fockK_tieE_pow_tieE_pow_eq_ite hw' he' hd (o + z) n (o + z + n + r) hN _ _ hL' hE'.1 hE'.2 hL j j' hlt.le, if_neg h, mul_zero, mul_zero]`.

Rewrite using `[fockK_symm, fockK_tieE_pow_tieE_pow_eq_ite hw' he' hd (o + z) n (o + z + n + r) hN _ _ hL hE.1 hE.2 hL' j' j hgt.le, if_neg (Ne.symm h), mul_zero, mul_zero]`.
-/
theorem fockForm_raiseAug_pow_augLift [CharZero k] (hv : M.TieVars w e zv sv) (hr : 1 ≤ r) {o n z : ℕ} {y y' : MvPolynomial σ k}
    (hy : BiHom w e o n y) (hy' : BiHom w e o n y') (hz : M.ZSFree zv sv y) (hz' : M.ZSFree zv sv y')
    (j j' : ℕ) :
    M.fockK ((((j.factorial : k))⁻¹) • ((M.tieEh w e zv sv) ^ j) (M.tieP w e zv sv o n z y))
        ((((j'.factorial : k))⁻¹) • ((M.tieEh w e zv sv) ^ j') (M.tieP w e zv sv o n z y')) =
      if j = j' then (((o + n + r + z + 1 + j - 1).choose j : ℕ) : k) * (z.factorial : k) *
        M.fockK y (tiePhi w e o n z y') else 0 := by
  have hw' := tv_w hv
  have he' := tv_e hv
  have hd := tv_we hv
  have hL := fh_P (z := z) hv hr hy hz
  have hL' := fh_P (z := z) hv hr hy' hz'
  have hE : eulL (Fin.cons zv w : Fin (r + 1) → σ) (Formalism.GM.M.tieP w e zv sv o n z y) =
        ((o + z : ℕ) : k) • Formalism.GM.M.tieP w e zv sv o n z y ∧
      eulL (Fin.cons sv e : Fin (r + 1) → σ) (Formalism.GM.M.tieP w e zv sv o n z y) =
        (n : k) • Formalism.GM.M.tieP w e zv sv o n z y := by
    rw [tieP_eq]
    exact eig_P (z := z) hv hy hz _
  have hE' : eulL (Fin.cons zv w : Fin (r + 1) → σ) (Formalism.GM.M.tieP w e zv sv o n z y') =
        ((o + z : ℕ) : k) • Formalism.GM.M.tieP w e zv sv o n z y' ∧
      eulL (Fin.cons sv e : Fin (r + 1) → σ) (Formalism.GM.M.tieP w e zv sv o n z y') =
        (n : k) • Formalism.GM.M.tieP w e zv sv o n z y' := by
    rw [tieP_eq]
    exact eig_P (z := z) hv hy' hz' _
  have hN : (o + z) + n + (r + 1) = (o + z + n + r) + 1 := by omega
  rw [tieEh_eq, fockK_smul_left, fockK_smul_right]
  by_cases h : j = j'
  · subst j'
    rw [fockK_tieE_pow_tieE_pow_eq_ite hw' he' hd (o + z) n (o + z + n + r) hN _ _ hL' hE'.1 hE'.2 hL j j le_rfl,
      if_pos rfl, if_pos rfl, fockForm_augLift_augLift (z := z) hv hr hy hy' hz hz']
    have h1 : o + n + r + z + 1 + j - 1 = o + z + n + r + j := by omega
    have hf : (j.factorial : k) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero j)
    have e1 : (j.factorial : k)⁻¹ * (j.factorial : k) = 1 := inv_mul_cancel₀ hf
    rw [h1, Nat.descFactorial_eq_factorial_mul_choose]
    push_cast
    linear_combination (((j.factorial : k)⁻¹ * (j.factorial : k) + 1) *
      (((o + z + n + r + j).choose j : ℕ) : k) * (z.factorial : k) *
      Formalism.GM.M.fockK y (Formalism.GM.tiePhi w e o n z y')) * e1
  · rw [if_neg h]
    rcases lt_or_gt_of_ne h with hlt | hgt
    · rw [fockK_tieE_pow_tieE_pow_eq_ite hw' he' hd (o + z) n (o + z + n + r) hN _ _ hL' hE'.1 hE'.2 hL j j' hlt.le,
        if_neg h, mul_zero, mul_zero]
    · rw [fockK_symm, fockK_tieE_pow_tieE_pow_eq_ite hw' he' hd (o + z) n (o + z + n + r) hN _ _ hL hE.1 hE.2 hL'
        j' j hgt.le, if_neg (Ne.symm h), mul_zero, mul_zero]

end Formalism.GM.ProjS

namespace Formalism.GM

end Formalism.GM

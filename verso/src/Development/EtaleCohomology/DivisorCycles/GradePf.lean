import Development.EtaleCohomology.DivisorCycles.CycleCount

open Matrix PositivityTheory.AutomorphicGaloisHodgeTate.Div Polynomial
namespace LateralTheory.DivDb.GradePf

section
variable {C : Type} [Field C] {N n : ℕ}

noncomputable def adX (X : Mat C N) : Module.End C (Mat C N) :=
  LinearMap.mulLeft C X - LinearMap.mulRight C X

/- English proof (translation)
Simplify using `[adX]`.
-/
lemma adX_apply (X Y : Mat C N) : adX X Y = X * Y - Y * X := by
  simp [adX]

/- English proof (translation)
Proceed by induction on `k with`. Consider the case `zero => intro Y hY`. Simplify using `using hY`. Consider the case `succ k ih => intro Y hY`. Rewrite using `[pow_succ', Module.End.mul_apply]`.

Conclude with `hf _ (ih Y hY)`.
-/
lemma pow_mem (f : Module.End C (Mat C N)) (g : Submodule C (Mat C N))
    (hf : ∀ Y ∈ g, f Y ∈ g) (k : ℕ) : ∀ Y ∈ g, (f ^ k) Y ∈ g := by
  induction k with
  | zero => intro Y hY; simpa using hY
  | succ k ih => intro Y hY; rw [pow_succ', Module.End.mul_apply]; exact hf _ (ih Y hY)

/- English proof (translation)
Proceed by induction on `q using Polynomial.induction_on' with`. Consider the case `add p q hp hq`. Introduce `Y hY`. Simplify using `only [map_add, LinearMap.add_apply]`. Conclude with `g.add_mem (hp Y hY) (hq Y hY)`.

Consider the case `monomial k a`. Introduce `Y hY`. Rewrite using `[aeval_monomial, Module.End.mul_apply, Module.algebraMap_end_apply]`. Conclude with `g.smul_mem _ (pow_mem f g hf k Y hY)`.
-/
lemma aeval_mem (f : Module.End C (Mat C N)) (g : Submodule C (Mat C N))
    (hf : ∀ Y ∈ g, f Y ∈ g) (q : C[X]) : ∀ Y ∈ g, aeval f q Y ∈ g := by
  induction q using Polynomial.induction_on' with
  | add p q hp hq =>
    intro Y hY; simp only [map_add, LinearMap.add_apply]; exact g.add_mem (hp Y hY) (hq Y hY)
  | monomial k a =>
    intro Y hY
    rw [aeval_monomial, Module.End.mul_apply, Module.algebraMap_end_apply]
    exact g.smul_mem _ (pow_mem f g hf k Y hY)

/- English proof (translation)
Proceed by induction on `k with`. Consider the case `zero => simp`. Consider the case `succ k ih => rw [pow_succ', Module.End.mul_apply, ih, map_smul, h, smul_smul, pow_succ]`.
-/
lemma pow_eig (f : Module.End C (Mat C N)) (Z : Mat C N) (c : C) (h : f Z = c • Z) (k : ℕ) :
    (f ^ k) Z = c ^ k • Z := by
  induction k with
  | zero => simp
  | succ k ih => rw [pow_succ', Module.End.mul_apply, ih, map_smul, h, smul_smul, pow_succ]

/- English proof (translation)
Proceed by induction on `q using Polynomial.induction_on' with`. Consider the case `add p q hp hq => simp only [map_add, LinearMap.add_apply, hp, hq, eval_add, add_smul]`. Consider the case `monomial k a`. Rewrite using `[aeval_monomial, Module.End.mul_apply, Module.algebraMap_end_apply, pow_eig f Z c h, smul_smul, eval_monomial]`.
-/
lemma aeval_eig (f : Module.End C (Mat C N)) (Z : Mat C N) (c : C) (h : f Z = c • Z) (q : C[X]) :
    aeval f q Z = q.eval c • Z := by
  induction q using Polynomial.induction_on' with
  | add p q hp hq => simp only [map_add, LinearMap.add_apply, hp, hq, eval_add, add_smul]
  | monomial k a =>
    rw [aeval_monomial, Module.End.mul_apply, Module.algebraMap_end_apply, pow_eig f Z c h, smul_smul,
      eval_monomial]

/- English proof (translation)
Establish `inj` using `isLac_inj hL`. Establish `h' : e i + e l = e k + e j` using `by linear_combination h`. Assume the negation of the conclusion as `hne`. Establish `hki : k ≠ i`. Introduce `hk`.

Rewrite `h'` using `[hk]`. Conclude with `hne ⟨hk, inj (by linear_combination h')⟩`. Establish `hlj : l ≠ j`. Introduce `hl`. Rewrite `h'` using `[hl]`.

Conclude with `hne ⟨(inj (by linear_combination h')).symm, hl⟩`. Establish `hkl : k ≠ l`. Introduce `hk; rw [hk] at h; exact hij (inj (by linear_combination h))`. Distinguish the cases in `hil : i = l`. Substitute `hil` using the available equality.

Distinguish the cases in `hkj : k = j`. Substitute `hkj` using the available equality. Conclude with `hki (inj (mul_left_cancel₀ (two_ne_zero (α := C)) (by linear_combination -h')))`. Use `hL {i} {k, j} (by simp) (by simp) (by simp [Finset.disjoint_left]; exact ⟨hki.symm, hij⟩)` as an intermediate fact. Apply `this` to reduce the goal to its premises.

Rewrite using `[Finset.card_pair hkj, Finset.sum_pair hkj]`. Simplify using the standard rewrite rules. Take the linear combination `h'`. Distinguish the cases in `hkj : k = j`. Substitute `hkj` using the available equality.

Use `hL {i, l} {k} (by simp) (by simp) (by simp [Finset.disjoint_left]; exact ⟨hij, hlj⟩)` as an intermediate fact. Apply `this` to reduce the goal to its premises. Rewrite using `[Finset.card_pair hil, Finset.sum_pair hil]`. Simplify using the standard rewrite rules. Take the linear combination `h'`.

Use `hL {i, l} {k, j} (by simp) (by simp) (by simp [Finset.disjoint_left]; exact ⟨⟨hki.symm, hij⟩, hkl.symm, hlj⟩)` as an intermediate fact. Apply `this` to reduce the goal to its premises. Rewrite using `[Finset.card_pair hil, Finset.sum_pair hil, Finset.card_pair hkj, Finset.sum_pair hkj]`. Rewrite using `[h']`.
-/
lemma lac_key [CharZero C] {e : Fin n → C} (hL : IsLac e) {i j k l : Fin n} (hij : i ≠ j)
    (h : e i - e j = e k - e l) : k = i ∧ l = j := by
  have inj := isLac_inj hL
  have h' : e i + e l = e k + e j := by linear_combination h
  by_contra hne
  have hki : k ≠ i := by
    intro hk; rw [hk] at h'
    exact hne ⟨hk, inj (by linear_combination h')⟩
  have hlj : l ≠ j := by
    intro hl; rw [hl] at h'
    exact hne ⟨(inj (by linear_combination h')).symm, hl⟩
  have hkl : k ≠ l := by
    intro hk; rw [hk] at h; exact hij (inj (by linear_combination h))
  by_cases hil : i = l
  · subst hil
    by_cases hkj : k = j
    · subst hkj
      exact hki (inj (mul_left_cancel₀ (two_ne_zero (α := C)) (by linear_combination -h')))
    · have := hL {i} {k, j} (by simp) (by simp)
        (by simp [Finset.disjoint_left]; exact ⟨hki.symm, hij⟩)
      apply this
      rw [Finset.card_pair hkj, Finset.sum_pair hkj]; simp; linear_combination h'
  · by_cases hkj : k = j
    · subst hkj
      have := hL {i, l} {k} (by simp) (by simp)
        (by simp [Finset.disjoint_left]; exact ⟨hij, hlj⟩)
      apply this
      rw [Finset.card_pair hil, Finset.sum_pair hil]; simp; linear_combination h'
    · have := hL {i, l} {k, j} (by simp) (by simp)
        (by simp [Finset.disjoint_left]; exact ⟨⟨hki.symm, hij⟩, hkl.symm, hlj⟩)
      apply this
      rw [Finset.card_pair hil, Finset.sum_pair hil, Finset.card_pair hkj, Finset.sum_pair hkj]
      rw [h']
end

end LateralTheory.DivDb.GradePf

namespace LateralTheory.DivDb
open LateralTheory.DivDb.GradePf

/- English proof (translation)
Introduce `C _ _ N n p e g hS hL hg Y hY i j hij`. Use `set X := ∑ i, e i • p i with hXdef`. Establish `hco` using `hS.1`. Establish `hid : ∀ k, p k * p k = p k` using `fun k => hco.idem k`. Establish `hor : ∀ k l, k ≠ l → p k * p l = 0` using `fun k l h => hco.ortho h`.

Establish `hsum : ∑ k, p k = 1` using `hco.complete`. Establish `hXp : ∀ k, X * p k = e k • p k`. Introduce `k`. Rewrite using `[hXdef, Finset.sum_mul]`. Simplify using `only [smul_mul_assoc]`.

Rewrite using `[Finset.sum_eq_single k]`. Rewrite using `[hid]`. Introduce `b _ hb`. Rewrite using `[hor b k hb, smul_zero]`. Simplify using the standard rewrite rules.

Establish `hpX : ∀ k, p k * X = e k • p k`. Introduce `k`. Rewrite using `[hXdef, Finset.mul_sum]`. Simplify using `only [mul_smul_comm]`. Rewrite using `[Finset.sum_eq_single k]`.

Rewrite using `[hid]`. Introduce `b _ hb`. Rewrite using `[hor k b (Ne.symm hb), smul_zero]`. Simplify using the standard rewrite rules. Establish `hdec : Y = ∑ kl : Fin n × Fin n, p kl.1 * Y * p kl.2`.

Establish `: (∑ k, p k) * Y * (∑ l, p l) = ∑ kl : Fin n × Fin n, p kl.1 * Y * p kl.2`. Rewrite using `[Finset.sum_mul, Finset.sum_mul, Fintype.sum_prod_type]`. Repeatedly rewrite using `[Finset.mul_sum]`. Rewrite using `[← this, hsum, one_mul, mul_one]`. Establish `heig : ∀ kl : Fin n × Fin n, adX X (p kl.1 * Y * p kl.2) = (e kl.1 - e kl.2) • (p kl.1 * Y * p kl.2)`.

Introduce `kl`. Rewrite using `[adX_apply, ← mul_assoc, ← mul_assoc, hXp, mul_assoc (p kl.1 * Y), hpX]`. Simplify using `[sub_smul, smul_mul_assoc, mul_smul_comm]`. Establish `hstab : ∀ Z ∈ g, adX X Z ∈ g` using `fun Z hZ => by rw [adX_apply]; exact hg Z hZ`. Set `q : C[X]` to `∏ kl ∈ (Finset.univ : Finset (Fin n × Fin n)).erase (i, j), (Polynomial.X - Polynomial.C (e kl.1 - e kl.2))`.

Establish `hq : aeval (adX X) q Y = q.eval (e i - e j) • (p i * Y * p j)` using `by conv_lhs => rw [hdec]`. Rewrite using `[map_sum]`. Repeatedly rewrite using `[aeval_eig (adX X) _ _ (heig _)]`. Rewrite using `[Finset.sum_eq_single (i, j)]`. Introduce `b _ hb`.

Establish `: q.eval (e b.1 - e b.2) = 0`. Simplify using `only [q, eval_prod]`. Conclude with `Finset.prod_eq_zero (Finset.mem_erase.mpr ⟨hb, Finset.mem_univ _⟩) (by simp)`. Rewrite using `[this, zero_smul]`. Simplify using the standard rewrite rules.

Establish `hq0 : q.eval (e i - e j) ≠ 0`. Simplify using `only [q, eval_prod]`. Rewrite using `[Finset.prod_ne_zero_iff]`. Introduce `kl hkl`. Simplify using `only [eval_sub, eval_X, eval_C]`.

Introduce `h0`. Use `lac_key hL hij (sub_eq_zero.mp h0)` as an intermediate fact. Conclude with `(Finset.mem_erase.mp hkl).1 (Prod.ext this.1 this.2)`. Establish `hm` using `g.smul_mem (q.eval (e i - e j))⁻¹ (aeval_mem (adX X) g hstab q Y hY)`. Rewrite `hm` using `[hq, smul_smul, inv_mul_cancel₀ hq0, one_smul]`. Then use the resulting hypothesis.
-/
theorem Grade_of : Grade := by
  intro C _ _ N n p e g hS hL hg Y hY i j hij
  set X := ∑ i, e i • p i with hXdef
  have hco := hS.1
  have hid : ∀ k, p k * p k = p k := fun k => hco.idem k
  have hor : ∀ k l, k ≠ l → p k * p l = 0 := fun k l h => hco.ortho h
  have hsum : ∑ k, p k = 1 := hco.complete
  have hXp : ∀ k, X * p k = e k • p k := by
    intro k; rw [hXdef, Finset.sum_mul]; simp only [smul_mul_assoc]
    rw [Finset.sum_eq_single k]
    · rw [hid]
    · intro b _ hb; rw [hor b k hb, smul_zero]
    · simp
  have hpX : ∀ k, p k * X = e k • p k := by
    intro k; rw [hXdef, Finset.mul_sum]; simp only [mul_smul_comm]
    rw [Finset.sum_eq_single k]
    · rw [hid]
    · intro b _ hb; rw [hor k b (Ne.symm hb), smul_zero]
    · simp
  have hdec : Y = ∑ kl : Fin n × Fin n, p kl.1 * Y * p kl.2 := by
    have : (∑ k, p k) * Y * (∑ l, p l) = ∑ kl : Fin n × Fin n, p kl.1 * Y * p kl.2 := by
      rw [Finset.sum_mul, Finset.sum_mul, Fintype.sum_prod_type]; simp_rw [Finset.mul_sum]
    rw [← this, hsum, one_mul, mul_one]
  have heig : ∀ kl : Fin n × Fin n, adX X (p kl.1 * Y * p kl.2) = (e kl.1 - e kl.2) • (p kl.1 * Y * p kl.2) := by
    intro kl
    rw [adX_apply, ← mul_assoc, ← mul_assoc, hXp, mul_assoc (p kl.1 * Y), hpX]
    simp [sub_smul, smul_mul_assoc, mul_smul_comm]
  have hstab : ∀ Z ∈ g, adX X Z ∈ g := fun Z hZ => by rw [adX_apply]; exact hg Z hZ
  let q : C[X] := ∏ kl ∈ (Finset.univ : Finset (Fin n × Fin n)).erase (i, j), (Polynomial.X - Polynomial.C (e kl.1 - e kl.2))
  have hq : aeval (adX X) q Y = q.eval (e i - e j) • (p i * Y * p j) := by
    conv_lhs => rw [hdec]
    rw [map_sum]
    simp_rw [aeval_eig (adX X) _ _ (heig _)]
    rw [Finset.sum_eq_single (i, j)]
    · intro b _ hb
      have : q.eval (e b.1 - e b.2) = 0 := by
        simp only [q, eval_prod]
        exact Finset.prod_eq_zero (Finset.mem_erase.mpr ⟨hb, Finset.mem_univ _⟩) (by simp)
      rw [this, zero_smul]
    · simp
  have hq0 : q.eval (e i - e j) ≠ 0 := by
    simp only [q, eval_prod]
    rw [Finset.prod_ne_zero_iff]
    intro kl hkl
    simp only [eval_sub, eval_X, eval_C]
    intro h0
    have := lac_key hL hij (sub_eq_zero.mp h0)
    exact (Finset.mem_erase.mp hkl).1 (Prod.ext this.1 this.2)
  have hm := g.smul_mem (q.eval (e i - e j))⁻¹ (aeval_mem (adX X) g hstab q Y hY)
  rwa [hq, smul_smul, inv_mul_cancel₀ hq0, one_smul] at hm

end LateralTheory.DivDb

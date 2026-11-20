import Mathlib
import Formalism.GL3MeanSquares.InvariantSeriesBidegreeOneOne

namespace Formalism.HermitianLattices.IntegralLatticeDensity.PD

open Finset Formalism.HermitianLattices.IntegralLatticeDensity

section calculus

variable {M Q : Type} [AddCommGroup M] [AddCommGroup Q] {φ : M → Q}

/- English proof (translation)
Simplify using `only [cob]`. Rewrite using `[add_comm a b]`. Normalize the expressions using the abelian group laws.
-/
theorem cob_symm' (a b : M) : cob φ a b = cob φ b a := by
  simp only [cob]
  rw [add_comm a b]
  abel

/- English proof (translation)
Simplify using `only [cob]`. Normalize the expressions using the abelian group laws.
-/
theorem phi_add' (a b : M) : φ (a + b) = φ a + φ b + cob φ a b := by
  simp only [cob]
  abel

/- English proof (translation)
Rewrite using `[cob_symm', h1, cob_symm' b, cob_symm' b']`.
-/
theorem cob_add_right' (h1 : ∀ a a' b, cob φ (a + a') b = cob φ a b + cob φ a' b) (a b b' : M) :
    cob φ a (b + b') = cob φ a b + cob φ a b' := by
  rw [cob_symm', h1, cob_symm' b, cob_symm' b']

/- English proof (translation)
Establish `h` using `h1 0 0 b`. Rewrite `h` using `[add_zero]`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem cob_zero_left' (h1 : ∀ a a' b, cob φ (a + a') b = cob φ a b + cob φ a' b) (b : M) :
    cob φ 0 b = 0 := by
  have h := h1 0 0 b
  rw [add_zero] at h
  calc cob φ 0 b = (cob φ 0 b + cob φ 0 b) - cob φ 0 b := by abel
    _ = cob φ 0 b - cob φ 0 b := by rw [← h]
    _ = 0 := sub_self _

/- English proof (translation)
Rewrite using `[cob_symm', cob_zero_left' h1]`.
-/
theorem cob_zero_right' (h1 : ∀ a a' b, cob φ (a + a') b = cob φ a b + cob φ a' b) (a : M) :
    cob φ a 0 = 0 := by
  rw [cob_symm', cob_zero_left' h1]

/- English proof (translation)
Establish `h` using `cob_zero_left' h1 (0 : M)`. Simplify using `only [cob, add_zero, sub_self, zero_sub, neg_eq_zero] at h`. Conclude with `h`.
-/
theorem phi_zero' (h1 : ∀ a a' b, cob φ (a + a') b = cob φ a b + cob φ a' b) : φ 0 = 0 := by
  have h := cob_zero_left' h1 (0 : M)
  simp only [cob, add_zero, sub_self, zero_sub, neg_eq_zero] at h
  exact h

/- English proof (translation)
Proceed by induction on `s using Finset.cons_induction with`. Consider the case `empty => rw [Finset.sum_empty, Finset.sum_empty, cob_zero_right' h1]`. Consider the case `cons j s hj ih => rw [Finset.sum_cons, Finset.sum_cons, cob_add_right' h1, ih]`.
-/
theorem cob_sum_right' (h1 : ∀ a a' b, cob φ (a + a') b = cob φ a b + cob φ a' b)
    {J : Type} (a : M) (s : Finset J) (x : J → M) :
    cob φ a (∑ j ∈ s, x j) = ∑ j ∈ s, cob φ a (x j) := by
  induction s using Finset.cons_induction with
  | empty => rw [Finset.sum_empty, Finset.sum_empty, cob_zero_right' h1]
  | cons j s hj ih => rw [Finset.sum_cons, Finset.sum_cons, cob_add_right' h1, ih]

/- English proof (translation)
Proceed by induction on `s using Finset.cons_induction with`. Consider the case `empty => rw [Finset.sum_empty, Finset.sum_empty, cob_zero_left' h1]`. Consider the case `cons j s hj ih => rw [Finset.sum_cons, Finset.sum_cons, h1, ih]`.
-/
theorem cob_sum_left' (h1 : ∀ a a' b, cob φ (a + a') b = cob φ a b + cob φ a' b)
    {J : Type} (b : M) (s : Finset J) (x : J → M) :
    cob φ (∑ j ∈ s, x j) b = ∑ j ∈ s, cob φ (x j) b := by
  induction s using Finset.cons_induction with
  | empty => rw [Finset.sum_empty, Finset.sum_empty, cob_zero_left' h1]
  | cons j s hj ih => rw [Finset.sum_cons, Finset.sum_cons, h1, ih]

variable {O : Type} [CommRing O] [StarRing O] [Module O M]

/- English proof (translation)
Repeatedly rewrite using `[h2, Finset.smul_sum, smul_smul, cob_sum_right' h1]`. Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Rewrite using `[Finset.sum_smul, cob_sum_right' h1]`.
-/
theorem cross' (h1 : ∀ a a' b, cob φ (a + a') b = cob φ a b + cob φ a' b)
    (h2 : ∀ (α : O) a b, cob φ (α • a) b = cob φ a (star α • b))
    {n J : Type} [Fintype n] (c : n → O) (d : n → J → O) (a : M) (s : Finset J) (x : J → M) :
    ∑ i, cob φ (c i • a) (∑ j ∈ s, d i j • x j) =
      ∑ j ∈ s, cob φ a ((∑ i, star (c i) * d i j) • x j) := by
  simp_rw [h2, Finset.smul_sum, smul_smul, cob_sum_right' h1]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.sum_smul, cob_sum_right' h1]

variable {Z : Type} [CommRing Z] [Module Z Q] {nm : O → Z}

/- English proof (translation)
Proceed by induction on `s using Finset.cons_induction with`. Consider the case `empty => simp [phi_zero' h1]`. Consider the case `cons k s hk ih`. Establish `hcross : ∑ i, cob φ (c i k • u k) (∑ j ∈ s, c i j • u j) = 0`. Rewrite using `[cross' h1 h2 (fun i => c i k) c (u k) s u]`.

Use `Finset.sum_eq_zero fun j hj => ?_` and prove the remaining obligations. Establish `hne : k ≠ j`. Introduce and unpack `rfl`. Conclude with `hk hj`. Rewrite using `[hG k j hne, zero_smul, cob_zero_right' h1]`.

Simplify using `only [Finset.sum_cons]`. Simplify using `only [phi_add', Finset.sum_add_distrib, h3]`. Rewrite using `[hcross, ih, ← Finset.sum_smul, add_zero]`.
-/
theorem diag' (h1 : ∀ a a' b, cob φ (a + a') b = cob φ a b + cob φ a' b)
    (h2 : ∀ (α : O) a b, cob φ (α • a) b = cob φ a (star α • b))
    (h3 : ∀ (α : O) u, φ (α • u) = nm α • φ u)
    {n J : Type} [Fintype n] (c : n → J → O)
    (hG : ∀ a j, a ≠ j → ∑ i, star (c i a) * c i j = 0) (u : J → M) (s : Finset J) :
    ∑ i, φ (∑ j ∈ s, c i j • u j) = ∑ j ∈ s, (∑ i, nm (c i j)) • φ (u j) := by
  induction s using Finset.cons_induction with
  | empty => simp [phi_zero' h1]
  | cons k s hk ih =>
    have hcross : ∑ i, cob φ (c i k • u k) (∑ j ∈ s, c i j • u j) = 0 := by
      rw [cross' h1 h2 (fun i => c i k) c (u k) s u]
      refine Finset.sum_eq_zero fun j hj => ?_
      have hne : k ≠ j := by
        rintro rfl
        exact hk hj
      rw [hG k j hne, zero_smul, cob_zero_right' h1]
    simp only [Finset.sum_cons]
    simp only [phi_add', Finset.sum_add_distrib, h3]
    rw [hcross, ih, ← Finset.sum_smul, add_zero]

end calculus

end Formalism.HermitianLattices.IntegralLatticeDensity.PD

namespace Formalism.HermitianLattices.IntegralLatticeDensity

open Finset PD

/- English proof (translation)
Introduce `Z O M Q _ _ _ _ _ _ _ _ φ nm hinj hnm h1 h2 h3 n _ _ δ hδ u`. Establish `hG : ∀ a j, a ≠ j → ∑ i, star (δ i a) * δ i j = 0`. Introduce `a j hne`. Use `congrFun (congrFun hδ a) j` as an intermediate fact. Simplify `this` using `[Matrix.mul_apply, Matrix.one_apply_ne hne]`.

Establish `hN : ∀ j, ∑ i, nm (δ i j) = 1`. Introduce `j`. Apply `hinj` to reduce the goal to its premises. Use `congrFun (congrFun hδ j) j` as an intermediate fact. Simplify using `only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.one_apply_eq] at this`.

Rewrite using `[map_sum, map_one]`. Simplify `this` using `[hnm]`. Rewrite using `[diag' h1 h2 h3 δ hG u Finset.univ]`. Simplify using `[hN]`.
-/
theorem unitary_invariance : UnitaryInvariance := by
  intro Z O M Q _ _ _ _ _ _ _ _ φ nm hinj hnm h1 h2 h3 n _ _ δ hδ u
  have hG : ∀ a j, a ≠ j → ∑ i, star (δ i a) * δ i j = 0 := by
    intro a j hne
    have := congrFun (congrFun hδ a) j
    simpa [Matrix.mul_apply, Matrix.one_apply_ne hne] using this
  have hN : ∀ j, ∑ i, nm (δ i j) = 1 := by
    intro j
    apply hinj
    have := congrFun (congrFun hδ j) j
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.one_apply_eq] at this
    rw [map_sum, map_one]
    simpa [hnm] using this
  rw [diag' h1 h2 h3 δ hG u Finset.univ]
  simp [hN]

/- English proof (translation)
Introduce `Z O M Q _ _ _ _ _ _ _ _ φ nm hinj hnm h1 h2 h3 n ι _ _ _ f f' hff hf'f' hff' t t'`. Establish `hiso : ∀ (g : ι → n → O) (w : ι → M), (∀ e e', ∑ i, star (g e i) * g e' i = 0) → ∑ i, φ (∑ e, g e i • w e) = 0`. Introduce `g w hg`. Establish `hz : ∀ e, ∑ i, nm (g e i) = 0`. Introduce `e`.

Apply `hinj` to reduce the goal to its premises. Rewrite using `[map_sum, map_zero]`. Simplify `hg e e` using `[hnm]`. Rewrite using `[diag' h1 h2 h3 (fun i e => g e i) (fun a j _ => hg a j) w Finset.univ]`. Simplify using `[hz]`.

Establish `hcross : ∑ i, cob φ (∑ e, f e i • t e) (∑ e, f' e i • t' e) = ∑ e, cob φ (t e) (t' e)`. Repeatedly rewrite using `[cob_sum_left' h1]`. Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_congr rfl fun e _ => ?_` and prove the remaining obligations. Rewrite using `[cross' h1 h2 (fun i => f e i) (fun i e' => f' e' i) (t e) Finset.univ t', Finset.sum_eq_single e]`.

Rewrite using `[hff' e e, if_pos rfl, one_smul]`. Introduce `e' _ hne`. Rewrite using `[hff' e e', if_neg (fun h => hne h.symm), zero_smul, cob_zero_right' h1]`. Introduce `h`. Conclude with `absurd (Finset.mem_univ e) h`.

Combine the equalities or inequalities in the displayed calculation. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[Finset.sum_add_distrib, phi_add' (φ := φ)]`. Use `_ = ∑ e, cob φ (t e) (t' e) := by`. Rewrite using `[Finset.sum_add_distrib, Finset.sum_add_distrib, hiso f t hff, hiso f' t' hf'f', hcross, zero_add, zero_add]`.
-/
theorem hyperbolic_plane_split : HyperbolicSplit := by
  intro Z O M Q _ _ _ _ _ _ _ _ φ nm hinj hnm h1 h2 h3 n ι _ _ _ f f' hff hf'f' hff' t t'

  have hiso : ∀ (g : ι → n → O) (w : ι → M), (∀ e e', ∑ i, star (g e i) * g e' i = 0) →
      ∑ i, φ (∑ e, g e i • w e) = 0 := by
    intro g w hg
    have hz : ∀ e, ∑ i, nm (g e i) = 0 := by
      intro e
      apply hinj
      rw [map_sum, map_zero]
      simpa [hnm] using hg e e
    rw [diag' h1 h2 h3 (fun i e => g e i) (fun a j _ => hg a j) w Finset.univ]
    simp [hz]

  have hcross : ∑ i, cob φ (∑ e, f e i • t e) (∑ e, f' e i • t' e) = ∑ e, cob φ (t e) (t' e) := by
    simp_rw [cob_sum_left' h1]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun e _ => ?_
    rw [cross' h1 h2 (fun i => f e i) (fun i e' => f' e' i) (t e) Finset.univ t',
      Finset.sum_eq_single e]
    · rw [hff' e e, if_pos rfl, one_smul]
    · intro e' _ hne
      rw [hff' e e', if_neg (fun h => hne h.symm), zero_smul, cob_zero_right' h1]
    · intro h
      exact absurd (Finset.mem_univ e) h
  calc ∑ i, φ (∑ e, (f e i • t e + f' e i • t' e))
      = ∑ i, (φ (∑ e, f e i • t e) + φ (∑ e, f' e i • t' e) +
          cob φ (∑ e, f e i • t e) (∑ e, f' e i • t' e)) := by
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Finset.sum_add_distrib, phi_add' (φ := φ)]
    _ = ∑ e, cob φ (t e) (t' e) := by
        rw [Finset.sum_add_distrib, Finset.sum_add_distrib, hiso f t hff, hiso f' t' hf'f', hcross,
          zero_add, zero_add]

end Formalism.HermitianLattices.IntegralLatticeDensity

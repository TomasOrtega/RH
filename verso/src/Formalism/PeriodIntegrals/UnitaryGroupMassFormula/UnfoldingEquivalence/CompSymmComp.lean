import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnfoldingEquivalence.Points

open PI.UnfoldEquiv PI.UnfoldEquiv.Loc

noncomputable section

namespace PI.UnfoldEquiv.UnitaryGroupMassFormula

variable {k : Type} [CommRing k]

/- English proof (translation)
Establish `hlt : n + i < n + c` using `by omega`. Establish `hw' : w - PI.UnfoldEquiv.Loc.atN w (n + i) • PI.UnfoldEquiv.Loc.eN k (n + c) (n + i) ∈ PI.UnfoldEquiv.Loc.Ufl k n c i`. Rewrite `hw`, the goal using `[mem_Ufl]`. Introduce `l hl`. Rewrite using `[Pi.sub_apply, Pi.smul_apply, eN_apply, smul_eq_mul]`.

Distinguish the cases in `hl' : l.1 = n + i`. Rewrite using `[if_pos hl', mul_one, PI.UnfoldEquiv.Loc.atN, dif_pos hlt]`. Establish `hle : l = ⟨n + i, hlt⟩` using `Fin.ext hl'`. Rewrite using `[hle, sub_self]`. Rewrite using `[if_neg hl', mul_zero, sub_zero]`.

Conclude with `hw l (by omega)`. Establish `hre : PI.UnfoldEquiv.Loc.atN (r (PI.UnfoldEquiv.Loc.eN k (n + c) (n + i))) (n + i) = 1`. Establish `h1` using `atN_of_mem (hr.2.2 i)`. Establish `h2` using `atN_add (r (PI.UnfoldEquiv.Loc.eN k (n + c) (n + i)) - PI.UnfoldEquiv.Loc.eN k (n + c) (n + i)) (PI.UnfoldEquiv.Loc.eN k (n + c) (n + i)) (n + i)`. Rewrite `h2` using `[sub_add_cancel]`.

Rewrite using `[h2, h1, atN_eN hlt, zero_add]`. Establish `hdec : r w = r (w - PI.UnfoldEquiv.Loc.atN w (n + i) • PI.UnfoldEquiv.Loc.eN k (n + c) (n + i)) + PI.UnfoldEquiv.Loc.atN w (n + i) • r (PI.UnfoldEquiv.Loc.eN k (n + c) (n + i))`. Rewrite using `[map_sub, map_smul, sub_add_cancel]`. Rewrite using `[hdec, atN_add, atN_smul, atN_of_mem (hr.1 i _ hw'), hre, zero_add, mul_one]`.
-/
theorem atN_map {n c i : ℕ} {r : (Fin (n + c) → k) ≃ₗ[k] (Fin (n + c) → k)} (hr : R1cond k n c r) (hi : i < c)
    {w : Fin (n + c) → k} (hw : w ∈ Ufl k n c (i + 1)) : atN (r w) (n + i) = atN w (n + i) := by
  have hlt : n + i < n + c := by omega
  have hw' : w - PI.UnfoldEquiv.Loc.atN w (n + i) • PI.UnfoldEquiv.Loc.eN k (n + c) (n + i) ∈ PI.UnfoldEquiv.Loc.Ufl k n c i := by
    rw [mem_Ufl] at hw ⊢
    intro l hl
    rw [Pi.sub_apply, Pi.smul_apply, eN_apply, smul_eq_mul]
    by_cases hl' : l.1 = n + i
    · rw [if_pos hl', mul_one, PI.UnfoldEquiv.Loc.atN, dif_pos hlt]
      have hle : l = ⟨n + i, hlt⟩ := Fin.ext hl'
      rw [hle, sub_self]
    · rw [if_neg hl', mul_zero, sub_zero]
      exact hw l (by omega)
  have hre : PI.UnfoldEquiv.Loc.atN (r (PI.UnfoldEquiv.Loc.eN k (n + c) (n + i))) (n + i) = 1 := by
    have h1 := atN_of_mem (hr.2.2 i)
    have h2 := atN_add (r (PI.UnfoldEquiv.Loc.eN k (n + c) (n + i)) - PI.UnfoldEquiv.Loc.eN k (n + c) (n + i)) (PI.UnfoldEquiv.Loc.eN k (n + c) (n + i)) (n + i)
    rw [sub_add_cancel] at h2
    rw [h2, h1, atN_eN hlt, zero_add]
  have hdec : r w = r (w - PI.UnfoldEquiv.Loc.atN w (n + i) • PI.UnfoldEquiv.Loc.eN k (n + c) (n + i)) + PI.UnfoldEquiv.Loc.atN w (n + i) • r (PI.UnfoldEquiv.Loc.eN k (n + c) (n + i)) := by
    rw [map_sub, map_smul, sub_add_cancel]
  rw [hdec, atN_add, atN_smul, atN_of_mem (hr.1 i _ hw'), hre, zero_add, mul_one]

/- English proof (translation)
Establish `h` using `atN_smul (0 : k) (0 : Fin N → k) i`. Rewrite `h` using `[zero_smul, zero_mul]`. Then use the resulting hypothesis.
-/
private theorem atN_zero {N : ℕ} (i : ℕ) : PI.UnfoldEquiv.Loc.atN (0 : Fin N → k) i = 0 := by
  have h := atN_smul (0 : k) (0 : Fin N → k) i
  rwa [zero_smul, zero_mul] at h

/- English proof (translation)
Use function extensionality and compare the values at `l`. Establish `hl` using `l.2`. Rewrite using `[eN_apply, Pi.zero_apply, if_neg (by omega)]`.
-/
private theorem eN_eq_zero_of_le {N i : ℕ} (h : N ≤ i) : PI.UnfoldEquiv.Loc.eN k N i = 0 := by
  funext l
  have hl := l.2
  rw [eN_apply, Pi.zero_apply, if_neg (by omega)]

/- English proof (translation)
Establish `key : ∀ i ∈ Finset.range c, PI.UnfoldEquiv.Loc.atN (r (x (PI.UnfoldEquiv.Loc.eN k (n' + (c + 1)) (n' + i + 1)))) (n + i) = PI.UnfoldEquiv.Loc.atN (x (PI.UnfoldEquiv.Loc.eN k (n' + (c + 1)) (n' + i + 1))) (n + i) + PI.UnfoldEquiv.Loc.atN (r (PI.UnfoldEquiv.Loc.eN k (n + c) (n + i …`. Introduce `i hi`. Rewrite `hi` using `[Finset.mem_range]`. Distinguish the cases in `hic : i + 1 < c`. Establish `hu : x (PI.UnfoldEquiv.Loc.eN k (n' + (c + 1)) (n' + i + 1)) - PI.UnfoldEquiv.Loc.eN k (n + c) (n + i + 1) ∈ PI.UnfoldEquiv.Loc.Ufl k n c (i + 1)` using `h.2.2 (i + 1) (by omega) hic`.

Establish `hcoord` using `atN_map hr hi hu`. Establish `hx : x (PI.UnfoldEquiv.Loc.eN k (n' + (c + 1)) (n' + i + 1)) = (x (PI.UnfoldEquiv.Loc.eN k (n' + (c + 1)) (n' + i + 1)) - PI.UnfoldEquiv.Loc.eN k (n + c) (n + i + 1)) + PI.UnfoldEquiv.Loc.eN k (n + c) (n + i + 1)` using `(sub_add_cancel _ _).symm`. Rewrite using `[hx, map_add, atN_add, atN_add, hcoord, atN_eN_ne (by omega : n + i + 1 ≠ n + i), add_zero]`. Establish `hw : x (PI.UnfoldEquiv.Loc.eN k (n' + (c + 1)) (n' + i + 1)) ∈ PI.UnfoldEquiv.Loc.Ufl k n c (i + 1)`. Rewrite using `[mem_Ufl]`.

Introduce `l hl`. It suffices to derive a contradiction. Use `l.2` as an intermediate fact. Use linear arithmetic over natural numbers and integers. Rewrite using `[atN_map hr hi hw, eN_eq_zero_of_le (by omega : n + c ≤ n + i + 1), map_zero, atN_zero, add_zero]`.

Simplify using `only [PI.UnfoldEquiv.Loc.chArg, PI.UnfoldEquiv.Loc.n1Arg, LinearMap.comp_apply, LinearEquiv.coe_coe]`. Rewrite using `[Finset.sum_congr rfl key, Finset.sum_add_distrib]`. Use `congr 1`. Break down `Nat.eq_zero_or_pos c with hc | hc` into its components or cases. Substitute `hc` using the available equality.

Simplify using the standard rewrite rules. Take `⟨m, rfl⟩ : ∃ m, c = m + 1` from `⟨c - 1, by omega⟩`. Rewrite using `[Nat.add_sub_cancel, Finset.sum_range_succ, eN_eq_zero_of_le (by omega : n + (m + 1) ≤ n + m + 1), map_zero, atN_zero, add_zero]`.
-/
theorem chArg_map {n' n c : ℕ} {r : (Fin (n + c) → k) ≃ₗ[k] (Fin (n + c) → k)} (hr : R1cond k n c r)
    {xj : (Fin n' → k) →ₗ[k] (Fin n → k)} {x : (Fin (n' + (c + 1)) → k) →ₗ[k] (Fin (n + c) → k)} (h : Q xj x) :
    chArg (n' := n') (c' := c + 1) (n := n) (c := c) (r.toLinearMap ∘ₗ x) = chArg x + n1Arg r := by
  have key : ∀ i ∈ Finset.range c,
      PI.UnfoldEquiv.Loc.atN (r (x (PI.UnfoldEquiv.Loc.eN k (n' + (c + 1)) (n' + i + 1)))) (n + i) =
        PI.UnfoldEquiv.Loc.atN (x (PI.UnfoldEquiv.Loc.eN k (n' + (c + 1)) (n' + i + 1))) (n + i) + PI.UnfoldEquiv.Loc.atN (r (PI.UnfoldEquiv.Loc.eN k (n + c) (n + i + 1))) (n + i) := by
    intro i hi
    rw [Finset.mem_range] at hi
    by_cases hic : i + 1 < c
    · have hu : x (PI.UnfoldEquiv.Loc.eN k (n' + (c + 1)) (n' + i + 1)) - PI.UnfoldEquiv.Loc.eN k (n + c) (n + i + 1) ∈ PI.UnfoldEquiv.Loc.Ufl k n c (i + 1) :=
        h.2.2 (i + 1) (by omega) hic
      have hcoord := atN_map hr hi hu
      have hx : x (PI.UnfoldEquiv.Loc.eN k (n' + (c + 1)) (n' + i + 1)) =
          (x (PI.UnfoldEquiv.Loc.eN k (n' + (c + 1)) (n' + i + 1)) - PI.UnfoldEquiv.Loc.eN k (n + c) (n + i + 1)) + PI.UnfoldEquiv.Loc.eN k (n + c) (n + i + 1) :=
        (sub_add_cancel _ _).symm
      rw [hx, map_add, atN_add, atN_add, hcoord, atN_eN_ne (by omega : n + i + 1 ≠ n + i), add_zero]
    · have hw : x (PI.UnfoldEquiv.Loc.eN k (n' + (c + 1)) (n' + i + 1)) ∈ PI.UnfoldEquiv.Loc.Ufl k n c (i + 1) := by
        rw [mem_Ufl]
        intro l hl
        exfalso
        have := l.2
        omega
      rw [atN_map hr hi hw, eN_eq_zero_of_le (by omega : n + c ≤ n + i + 1), map_zero,
        atN_zero, add_zero]
  simp only [PI.UnfoldEquiv.Loc.chArg, PI.UnfoldEquiv.Loc.n1Arg, LinearMap.comp_apply, LinearEquiv.coe_coe]
  rw [Finset.sum_congr rfl key, Finset.sum_add_distrib]
  congr 1
  rcases Nat.eq_zero_or_pos c with hc | hc
  · subst hc
    simp
  · obtain ⟨m, rfl⟩ : ∃ m, c = m + 1 := ⟨c - 1, by omega⟩
    rw [Nat.add_sub_cancel, Finset.sum_range_succ, eN_eq_zero_of_le (by omega : n + (m + 1) ≤ n + m + 1), map_zero,
      atN_zero, add_zero]

/- English proof (translation)
Apply `LinearMap.ext` to reduce the goal to its premises. Introduce `v`. Simplify using the standard rewrite rules.
-/
theorem comp_symm_comp {n' n c : ℕ} (r : (Fin (n + c) → k) ≃ₗ[k] (Fin (n + c) → k))
    (y : (Fin (n' + (c + 1)) → k) →ₗ[k] (Fin (n + c) → k)) : r.toLinearMap ∘ₗ (r.symm.toLinearMap ∘ₗ y) = y := by
  apply LinearMap.ext
  intro v
  simp

/- English proof (translation)
Apply `LinearMap.ext` to reduce the goal to its premises. Introduce `v`. Simplify using the standard rewrite rules.
-/
theorem symm_comp_comp {n' n c : ℕ} (r : (Fin (n + c) → k) ≃ₗ[k] (Fin (n + c) → k))
    (y : (Fin (n' + (c + 1)) → k) →ₗ[k] (Fin (n + c) → k)) : r.symm.toLinearMap ∘ₗ (r.toLinearMap ∘ₗ y) = y := by
  apply LinearMap.ext
  intro v
  simp

/- English proof (translation)
Introduce `k₀ K _ _ _ n' n c psi hpsi wt Φ r g hmem hg xj`. Establish `hmem' : PI.UnfoldEquiv.Loc.R1cond k₀ n c r ∧ PI.UnfoldEquiv.Loc.R1cond k₀ n c r⁻¹` using `hmem`. Establish `hr : PI.UnfoldEquiv.Loc.R1cond k₀ n c r` using `hmem'.1`. Establish `hrs : PI.UnfoldEquiv.Loc.R1cond k₀ n c r.symm` using `hmem'.2`. Establish `hgs : ∀ v, r.symm (PI.UnfoldEquiv.Loc.inX k₀ n c v) = PI.UnfoldEquiv.Loc.inX k₀ n c (g.symm v)`.

Introduce `v`. Rewrite using `[LinearEquiv.symm_apply_eq, hg, LinearEquiv.apply_symm_apply]`. Establish `hgg : g.toLinearMap ∘ₗ (g.symm.toLinearMap ∘ₗ xj) = xj`. Apply `LinearMap.ext` to reduce the goal to its premises. Introduce `v`.

Simplify using the standard rewrite rules. Set `F : (PI.UnfoldEquiv.Loc.FC n' (c + 1) n c → k₀) → (PI.UnfoldEquiv.Loc.FC n' (c + 1) n c → k₀)` to `fun t => fe (r.symm.toLinearMap ∘ₗ PI.UnfoldEquiv.Loc.xx1 xj t)`. Set `G : (PI.UnfoldEquiv.Loc.FC n' (c + 1) n c → k₀) → (PI.UnfoldEquiv.Loc.FC n' (c + 1) n c → k₀)` to `fun s => fe (r.toLinearMap ∘ₗ PI.UnfoldEquiv.Loc.xx1 (g.symm.toLinearMap ∘ₗ xj) s)`. Establish `hF : ∀ t, PI.UnfoldEquiv.Loc.xx1 (g.symm.toLinearMap ∘ₗ xj) (F t) = r.symm.toLinearMap ∘ₗ PI.UnfoldEquiv.Loc.xx1 xj t` using `fun t => fillMatrix_extractFree (Q_map hrs hgs (isFillOf_fillMatrix xj t))`. Establish `hG : ∀ s, PI.UnfoldEquiv.Loc.xx1 xj (G s) = r.toLinearMap ∘ₗ PI.UnfoldEquiv.Loc.xx1 (g.symm.toLinearMap ∘ₗ xj) s` using `fun s => by`.

Establish `h1` using `Q_map hr hg (isFillOf_fillMatrix (g.symm.toLinearMap ∘ₗ xj) s)`. Rewrite `h1` using `[hgg]`. Conclude with `fillMatrix_extractFree h1`. Establish `hbij : Function.Bijective F`. Use `Function.bijective_iff_has_inverse.mpr ⟨G, fun t => ?_, fun s => ?_⟩` and prove the remaining obligations.

Use `show fe (r.toLinearMap ∘ₗ PI.UnfoldEquiv.Loc.xx1 (g.symm.toLinearMap ∘ₗ xj) (F t)) = t`. Rewrite using `[hF, comp_symm_comp, extractFree_fillMatrix]`. Use `show fe (r.symm.toLinearMap ∘ₗ PI.UnfoldEquiv.Loc.xx1 xj (G s)) = s`. Rewrite using `[hG, symm_comp_comp, extractFree_fillMatrix]`. Establish `hca : ∀ t : PI.UnfoldEquiv.Loc.FC n' (c + 1) n c → k₀, PI.UnfoldEquiv.Loc.chArg (PI.UnfoldEquiv.Loc.xx1 xj t) = PI.UnfoldEquiv.Loc.chArg (r.symm.toLinearMap ∘ₗ PI.UnfoldEquiv.Loc.xx1 xj t) + PI.UnfoldEquiv.Loc.n1Arg r` using `fun t => by`.

Establish `h2` using `chArg_map hr (Q_map hrs hgs (isFillOf_fillMatrix xj t))`. Rewrite `h2` using `[comp_symm_comp]`. Then use the resulting hypothesis. Simplify using `only [PI.UnfoldEquiv.Loc.E1, Fintype.piFinset_univ]`. Rewrite using `[mul_left_comm (psi _)]`. Use `congr 1`.

Rewrite using `[Finset.mul_sum]`. Use `Fintype.sum_bijective F hbij _ _ (fun t => ?_)` and prove the remaining obligations. Rewrite using `[hF, hca, neg_add, hpsi]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem unfoldEquiv : UnfoldEquiv := by
  intro k₀ K _ _ _ n' n c psi hpsi wt Φ r g hmem hg xj
  have hmem' : PI.UnfoldEquiv.Loc.R1cond k₀ n c r ∧ PI.UnfoldEquiv.Loc.R1cond k₀ n c r⁻¹ := hmem
  have hr : PI.UnfoldEquiv.Loc.R1cond k₀ n c r := hmem'.1
  have hrs : PI.UnfoldEquiv.Loc.R1cond k₀ n c r.symm := hmem'.2
  have hgs : ∀ v, r.symm (PI.UnfoldEquiv.Loc.inX k₀ n c v) = PI.UnfoldEquiv.Loc.inX k₀ n c (g.symm v) := by
    intro v
    rw [LinearEquiv.symm_apply_eq, hg, LinearEquiv.apply_symm_apply]
  have hgg : g.toLinearMap ∘ₗ (g.symm.toLinearMap ∘ₗ xj) = xj := by
    apply LinearMap.ext
    intro v
    simp
  let F : (PI.UnfoldEquiv.Loc.FC n' (c + 1) n c → k₀) → (PI.UnfoldEquiv.Loc.FC n' (c + 1) n c → k₀) :=
    fun t => fe (r.symm.toLinearMap ∘ₗ PI.UnfoldEquiv.Loc.xx1 xj t)
  let G : (PI.UnfoldEquiv.Loc.FC n' (c + 1) n c → k₀) → (PI.UnfoldEquiv.Loc.FC n' (c + 1) n c → k₀) :=
    fun s => fe (r.toLinearMap ∘ₗ PI.UnfoldEquiv.Loc.xx1 (g.symm.toLinearMap ∘ₗ xj) s)
  have hF : ∀ t, PI.UnfoldEquiv.Loc.xx1 (g.symm.toLinearMap ∘ₗ xj) (F t) = r.symm.toLinearMap ∘ₗ PI.UnfoldEquiv.Loc.xx1 xj t := fun t =>
    fillMatrix_extractFree (Q_map hrs hgs (isFillOf_fillMatrix xj t))
  have hG : ∀ s, PI.UnfoldEquiv.Loc.xx1 xj (G s) = r.toLinearMap ∘ₗ PI.UnfoldEquiv.Loc.xx1 (g.symm.toLinearMap ∘ₗ xj) s := fun s => by
    have h1 := Q_map hr hg (isFillOf_fillMatrix (g.symm.toLinearMap ∘ₗ xj) s)
    rw [hgg] at h1
    exact fillMatrix_extractFree h1
  have hbij : Function.Bijective F := by
    refine Function.bijective_iff_has_inverse.mpr ⟨G, fun t => ?_, fun s => ?_⟩
    · show fe (r.toLinearMap ∘ₗ PI.UnfoldEquiv.Loc.xx1 (g.symm.toLinearMap ∘ₗ xj) (F t)) = t
      rw [hF, comp_symm_comp, extractFree_fillMatrix]
    · show fe (r.symm.toLinearMap ∘ₗ PI.UnfoldEquiv.Loc.xx1 xj (G s)) = s
      rw [hG, symm_comp_comp, extractFree_fillMatrix]
  have hca : ∀ t : PI.UnfoldEquiv.Loc.FC n' (c + 1) n c → k₀, PI.UnfoldEquiv.Loc.chArg (PI.UnfoldEquiv.Loc.xx1 xj t) =
      PI.UnfoldEquiv.Loc.chArg (r.symm.toLinearMap ∘ₗ PI.UnfoldEquiv.Loc.xx1 xj t) + PI.UnfoldEquiv.Loc.n1Arg r := fun t => by
    have h2 := chArg_map hr (Q_map hrs hgs (isFillOf_fillMatrix xj t))
    rwa [comp_symm_comp] at h2
  simp only [PI.UnfoldEquiv.Loc.E1, Fintype.piFinset_univ]
  rw [mul_left_comm (psi _)]
  congr 1
  rw [Finset.mul_sum]
  refine Fintype.sum_bijective F hbij _ _ (fun t => ?_)
  rw [hF, hca, neg_add, hpsi]
  ring

end PI.UnfoldEquiv.UnitaryGroupMassFormula

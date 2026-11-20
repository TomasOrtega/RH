import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.WdDefs

open Module

/- English proof (translation)
Introduce `k W ι _ _ _ n T d hT`. Take `⟨b, hb⟩` from `hT`. Establish `hp : ∀ a x, b.coord (Fin.last n) (T a x) = d a (Fin.last n) * b.coord (Fin.last n) x`. Introduce `a x`. Establish `h : (b.coord (Fin.last n)) ∘ₗ (T a) = d a (Fin.last n) • b.coord (Fin.last n)`.

Use `b.ext fun j => ?_` and prove the remaining obligations. Establish `h1` using `(hb a).1 (Fin.last n) j`. Establish `h2` using `(hb a).2 (Fin.last n)`. Rewrite `h1`, `h2` using `[LinearMap.toMatrix_apply]`. Simplify using `only [LinearMap.comp_apply, LinearMap.smul_apply, Basis.coord_apply, Basis.repr_self, smul_eq_mul]`.

Distinguish the cases in `hj : j = Fin.last n`. Substitute `hj` using the available equality. Rewrite using `[h2]`. Simplify using the standard rewrite rules. Rewrite using `[h1 (lt_of_le_of_ne (Fin.le_last j) hj), Finsupp.single_apply, if_neg hj, mul_zero]`.

Simplify using `using LinearMap.congr_fun h x`. Establish `hS : ∀ a, ∀ x ∈ LinearMap.ker (b.coord (Fin.last n)), T a x ∈ LinearMap.ker (b.coord (Fin.last n))`. Introduce `a x hx`. Rewrite `hx`, the goal using `[LinearMap.mem_ker]`. Rewrite using `[hp, hx, mul_zero]`.

Use `⟨LinearMap.ker (b.coord (Fin.last n)), hS, b.coord (Fin.last n), ?_, rfl, hp, ?_⟩` and prove the remaining obligations. Introduce `c`. Conclude with `⟨c • b (Fin.last n), by simp⟩`. Set `v : Fin n → LinearMap.ker (b.coord (Fin.last n))` to `fun i => ⟨b (Fin.castSucc i), by`. Rewrite using `[LinearMap.mem_ker, Basis.coord_apply, Basis.repr_self, Finsupp.single_apply, if_neg (Fin.castSucc_lt_last i).ne]⟩`.

Establish `hv : LinearIndependent k v`. Apply `LinearIndependent.of_comp (LinearMap.ker (b.coord (Fin.last n))).subtype` to reduce the goal to its premises. Conclude with `b.linearIndependent.comp Fin.castSucc (Fin.castSucc_injective n)`. Establish `key : ∀ x : LinearMap.ker (b.coord (Fin.last n)), x = ∑ i, b.repr (x : W) (Fin.castSucc i) • v i`. Introduce `x`.

Apply `Subtype.ext` to reduce the goal to its premises. Establish `hx : b.repr (x : W) (Fin.last n) = 0` using `x.2`. Establish `h` using `b.sum_repr (x : W)`. Rewrite `h` using `[Fin.sum_univ_castSucc, hx, zero_smul, add_zero]`. Rewrite using `[Submodule.coe_sum]`.

Conclude with `h.symm`. Establish `hsp : ⊤ ≤ Submodule.span k (Set.range v)`. Introduce `x _`. Rewrite using `[key x]`. Conclude with `Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)`.

Set `b'` to `Basis.mk hv hsp`. Establish `hb' : ∀ i, b' i = v i` using `fun i => Basis.mk_apply hv hsp i`. Establish `hr : ∀ (x : LinearMap.ker (b.coord (Fin.last n))) i, b'.repr x i = b.repr (x : W) (Fin.castSucc i)`. Introduce `x i`. Establish `h` using `congrFun (b'.repr_sum_self fun i => b.repr (x : W) (Fin.castSucc i)) i`.

Simplify using `only [hb'] at h`. Rewrite `h` using `[← key x]`. Conclude with `h`. Establish `hm : ∀ a i j, LinearMap.toMatrix b' b' ((T a).restrict (hS a)) i j = LinearMap.toMatrix b b (T a) (Fin.castSucc i) (Fin.castSucc j)`. Introduce `a i j`.

Rewrite using `[LinearMap.toMatrix_apply, LinearMap.toMatrix_apply, hr, hb']`. Both sides reduce to the same expression. Use `⟨b', fun a => ⟨fun i j hij => ?_, fun i => ?_⟩⟩` and prove the remaining obligations. Conclude with `(hm a i j).trans ((hb a).1 _ _ (Fin.castSucc_lt_castSucc_iff.2 hij))`. Conclude with `(hm a i i).trans ((hb a).2 _)`.
-/
theorem UpperTheory.weilDeligne_triangular_initial_segment :
    UpperTheory.V.Af.Wd.TriInit := by
  intro k W ι _ _ _ n T d hT
  obtain ⟨b, hb⟩ := hT
  have hp : ∀ a x, b.coord (Fin.last n) (T a x) = d a (Fin.last n) * b.coord (Fin.last n) x := by
    intro a x
    have h : (b.coord (Fin.last n)) ∘ₗ (T a) = d a (Fin.last n) • b.coord (Fin.last n) := by
      refine b.ext fun j => ?_
      have h1 := (hb a).1 (Fin.last n) j
      have h2 := (hb a).2 (Fin.last n)
      rw [LinearMap.toMatrix_apply] at h1 h2
      simp only [LinearMap.comp_apply, LinearMap.smul_apply, Basis.coord_apply, Basis.repr_self, smul_eq_mul]
      by_cases hj : j = Fin.last n
      · subst hj
        rw [h2]; simp
      · rw [h1 (lt_of_le_of_ne (Fin.le_last j) hj), Finsupp.single_apply, if_neg hj, mul_zero]
    simpa using LinearMap.congr_fun h x
  have hS : ∀ a, ∀ x ∈ LinearMap.ker (b.coord (Fin.last n)), T a x ∈ LinearMap.ker (b.coord (Fin.last n)) := by
    intro a x hx
    rw [LinearMap.mem_ker] at hx ⊢
    rw [hp, hx, mul_zero]
  refine ⟨LinearMap.ker (b.coord (Fin.last n)), hS, b.coord (Fin.last n), ?_, rfl, hp, ?_⟩
  · intro c
    exact ⟨c • b (Fin.last n), by simp⟩
  · let v : Fin n → LinearMap.ker (b.coord (Fin.last n)) := fun i =>
      ⟨b (Fin.castSucc i), by
        rw [LinearMap.mem_ker, Basis.coord_apply, Basis.repr_self, Finsupp.single_apply,
          if_neg (Fin.castSucc_lt_last i).ne]⟩
    have hv : LinearIndependent k v := by
      apply LinearIndependent.of_comp (LinearMap.ker (b.coord (Fin.last n))).subtype
      exact b.linearIndependent.comp Fin.castSucc (Fin.castSucc_injective n)
    have key : ∀ x : LinearMap.ker (b.coord (Fin.last n)),
        x = ∑ i, b.repr (x : W) (Fin.castSucc i) • v i := by
      intro x
      apply Subtype.ext
      have hx : b.repr (x : W) (Fin.last n) = 0 := x.2
      have h := b.sum_repr (x : W)
      rw [Fin.sum_univ_castSucc, hx, zero_smul, add_zero] at h
      rw [Submodule.coe_sum]
      exact h.symm
    have hsp : ⊤ ≤ Submodule.span k (Set.range v) := by
      intro x _
      rw [key x]
      exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
    let b' := Basis.mk hv hsp
    have hb' : ∀ i, b' i = v i := fun i => Basis.mk_apply hv hsp i
    have hr : ∀ (x : LinearMap.ker (b.coord (Fin.last n))) i, b'.repr x i = b.repr (x : W) (Fin.castSucc i) := by
      intro x i
      have h := congrFun (b'.repr_sum_self fun i => b.repr (x : W) (Fin.castSucc i)) i
      simp only [hb'] at h
      rw [← key x] at h
      exact h
    have hm : ∀ a i j, LinearMap.toMatrix b' b' ((T a).restrict (hS a)) i j =
        LinearMap.toMatrix b b (T a) (Fin.castSucc i) (Fin.castSucc j) := by
      intro a i j
      rw [LinearMap.toMatrix_apply, LinearMap.toMatrix_apply, hr, hb']
      rfl
    refine ⟨b', fun a => ⟨fun i j hij => ?_, fun i => ?_⟩⟩
    · exact (hm a i j).trans ((hb a).1 _ _ (Fin.castSucc_lt_castSucc_iff.2 hij))
    · exact (hm a i i).trans ((hb a).2 _)

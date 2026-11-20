import Mathlib

namespace GlobalTheory.NotLeSqSup

/- English proof (translation)
Introduce `h`. Establish `key : ∀ j : ℕ, m ≤ m ^ (j + 1) ⊔ I`. Introduce `j`. Proceed by induction on `j with`. Consider the case `zero => simpa using (le_sup_left : m ≤ m ⊔ I)`.

Consider the case `succ j ih`. Combine the equalities or inequalities in the displayed calculation. Use `sup_le ?_ le_sup_right` and prove the remaining obligations. Combine the equalities or inequalities in the displayed calculation. Apply `hI` to reduce the goal to its premises.

Simplify `key n` using `[hn]`.
-/
theorem not_le_sq_sup {A : Type} [CommRing A] {m I : Ideal A} {n : ℕ}
    (hn : m ^ (n + 1) = ⊥) (hI : ¬ m ≤ I) : ¬ m ≤ m ^ 2 ⊔ I := by
  intro h
  have key : ∀ j : ℕ, m ≤ m ^ (j + 1) ⊔ I := by
    intro j
    induction j with
    | zero => simpa using (le_sup_left : m ≤ m ⊔ I)
    | succ j ih =>
      calc m ≤ m ^ 2 ⊔ I := h
        _ ≤ m ^ (j + 1 + 1) ⊔ I := by
          refine sup_le ?_ le_sup_right
          calc m ^ 2 = m * m := pow_two m
            _ ≤ m * (m ^ (j + 1) ⊔ I) := Ideal.mul_mono_right ih
            _ = m * m ^ (j + 1) ⊔ m * I := Ideal.mul_sup _ _ _
            _ ≤ m ^ (j + 1 + 1) ⊔ I :=
              sup_le_sup (le_of_eq (pow_succ' m (j + 1)).symm)
                (Ideal.mul_le.mpr fun r _ s hs => I.mul_mem_left r hs)
  apply hI
  simpa [hn] using key n

/- English proof (translation)
Introduce `k A _ _ _ aug I n hn hIm hmI`. Establish `hx : ¬ RingHom.ker aug ≤ RingHom.ker aug ^ 2 ⊔ I` using `not_le_sq_sup hn hmI`. Take `⟨x, hxm, hxN⟩` from `Set.not_subset.mp hx`. Set `N : Submodule k A` to `(RingHom.ker aug ^ 2 ⊔ I).restrictScalars k`. Establish `hq : N.mkQ x ≠ 0`.

Rewrite using `[Ne, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]`. Conclude with `hxN`. Choose the witnesses or unpack the hypotheses as in `⟨f, hf⟩ : ∃ f : Module.Dual k (A ⧸ N), f (N.mkQ x) ≠ 0 := by`. Assume the negation of the conclusion as `h`. Use `push_neg at h`.

Conclude with `hq ((Module.forall_dual_apply_eq_zero_iff k _).mp h)`. Set `g : A →ₗ[k] k` to `f.comp N.mkQ`. Establish `hgN : ∀ a ∈ RingHom.ker aug ^ 2 ⊔ I, g a = 0`. Introduce `a ha`. Establish `: N.mkQ a = 0`.

Rewrite using `[Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]`. Conclude with `ha`. Simplify using `only [g, LinearMap.comp_apply, this, map_zero]`. Set `D : A →ₗ[k] k` to `g.comp (LinearMap.id - (Algebra.linearMap k A).comp aug.toLinearMap)`. Establish `hD : ∀ a, D a = g (a - algebraMap k A (aug a))` using `fun a => rfl`.

Establish `hsub : ∀ a, a - algebraMap k A (aug a) ∈ RingHom.ker aug`. Introduce `a`. Simplify using `[RingHom.mem_ker]`. Establish `hDmul : ∀ a b, D (a * b) = aug a * D b + aug b * D a`. Introduce `a b`.

Establish `e : a * b - algebraMap k A (aug (a * b)) = (a - algebraMap k A (aug a)) * (b - algebraMap k A (aug b)) + aug a • (b - algebraMap k A (aug b)) + aug b • (a - algebraMap k A (aug a))`. Rewrite using `[map_mul, Algebra.smul_def, Algebra.smul_def, map_mul]`. Expand and normalize the polynomial expressions, which then agree. Establish `h0 : g ((a - algebraMap k A (aug a)) * (b - algebraMap k A (aug b))) = 0` using `hgN _ (Ideal.mem_sup_left (by rw [pow_two]; exact Ideal.mul_mem_mul (hsub a) (hsub b)))`. Rewrite using `[hD, hD, hD, e, map_add, map_add, h0, map_smul, map_smul, smul_eq_mul, smul_eq_mul, zero_add]`.

Set `L : A →ₗ[k] DualNumber k` to `(Algebra.linearMap k (DualNumber k)).comp aug.toLinearMap + (TrivSqZeroExt.inrHom k k).comp D`. Establish `hLfst : ∀ a, (L a).fst = aug a` using `by intro a; simp [L, TrivSqZeroExt.algebraMap_eq_inl]`. Establish `hLsnd : ∀ a, (L a).snd = D a` using `by intro a; simp [L, TrivSqZeroExt.algebraMap_eq_inl]`. Apply the tactic sequence `let φ : A →ₐ[k] DualNumber k := AlgHom.ofLinearMap L (by ext <;> simp [hLfst, hLsnd, hD]) (by intro a b; ext <;> simp [hLfst, hLsnd, hDmul] <;> ring)`. Establish `hφ : ∀ a, φ a = L a` using `fun a => rfl`.

Use `⟨φ, ?_, ?_, x, hxm, ?_⟩` and prove the remaining obligations. Use extensionality with `a`. Simplify using `[hφ, hLfst]`. Introduce `a ha`. Use `ext`.

Simplify using `[hφ, hLfst]`. Conclude with `hIm ha`. Simplify using `only [hφ, hLsnd, TrivSqZeroExt.snd_zero]`. Rewrite using `[hD]`. Establish `: aug a = 0` using `hIm ha`.

Rewrite using `[this, map_zero, sub_zero]`. Conclude with `hgN a (Ideal.mem_sup_right ha)`. Introduce `h0`. Apply `hf` to reduce the goal to its premises. Use `congrArg TrivSqZeroExt.snd h0` as an intermediate fact.

Rewrite `this` using `[hφ, hLsnd, hD, TrivSqZeroExt.snd_zero, (RingHom.mem_ker).mp hxm, map_zero, sub_zero]`. Conclude with `this`.
-/
theorem main : ∀ {k A : Type} [inst : Field k] [inst_1 : CommRing A] [inst_2 : Algebra k A] (aug : A →ₐ[k] k) {I : Ideal A} {n : ℕ}, RingHom.ker aug ^ (n + (1 : ℕ)) = ⊥ → I ≤ RingHom.ker aug → ¬RingHom.ker aug ≤ I → ∃ (φ : A →ₐ[k] DualNumber k), AlgHom.comp (TrivSqZeroExt.fstHom k k k) φ = aug ∧ (∀ a ∈ I, (φ : A → DualNumber k) a = (0 : DualNumber k)) ∧ ∃ a ∈ RingHom.ker aug, (φ : A → DualNumber k) a ≠ (0 : DualNumber k) := by
  intro k A _ _ _ aug I n hn hIm hmI
  have hx : ¬ RingHom.ker aug ≤ RingHom.ker aug ^ 2 ⊔ I := not_le_sq_sup hn hmI
  obtain ⟨x, hxm, hxN⟩ := Set.not_subset.mp hx
  let N : Submodule k A := (RingHom.ker aug ^ 2 ⊔ I).restrictScalars k
  have hq : N.mkQ x ≠ 0 := by
    rw [Ne, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]; exact hxN
  obtain ⟨f, hf⟩ : ∃ f : Module.Dual k (A ⧸ N), f (N.mkQ x) ≠ 0 := by
    by_contra h; push_neg at h
    exact hq ((Module.forall_dual_apply_eq_zero_iff k _).mp h)
  let g : A →ₗ[k] k := f.comp N.mkQ
  have hgN : ∀ a ∈ RingHom.ker aug ^ 2 ⊔ I, g a = 0 := by
    intro a ha
    have : N.mkQ a = 0 := by
      rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]; exact ha
    simp only [g, LinearMap.comp_apply, this, map_zero]
  let D : A →ₗ[k] k := g.comp (LinearMap.id - (Algebra.linearMap k A).comp aug.toLinearMap)
  have hD : ∀ a, D a = g (a - algebraMap k A (aug a)) := fun a => rfl
  have hsub : ∀ a, a - algebraMap k A (aug a) ∈ RingHom.ker aug := by
    intro a; simp [RingHom.mem_ker]
  have hDmul : ∀ a b, D (a * b) = aug a * D b + aug b * D a := by
    intro a b
    have e : a * b - algebraMap k A (aug (a * b)) =
        (a - algebraMap k A (aug a)) * (b - algebraMap k A (aug b))
          + aug a • (b - algebraMap k A (aug b)) + aug b • (a - algebraMap k A (aug a)) := by
      rw [map_mul, Algebra.smul_def, Algebra.smul_def, map_mul]; ring
    have h0 : g ((a - algebraMap k A (aug a)) * (b - algebraMap k A (aug b))) = 0 :=
      hgN _ (Ideal.mem_sup_left (by rw [pow_two]; exact Ideal.mul_mem_mul (hsub a) (hsub b)))
    rw [hD, hD, hD, e, map_add, map_add, h0, map_smul, map_smul, smul_eq_mul, smul_eq_mul, zero_add]
  let L : A →ₗ[k] DualNumber k :=
    (Algebra.linearMap k (DualNumber k)).comp aug.toLinearMap + (TrivSqZeroExt.inrHom k k).comp D
  have hLfst : ∀ a, (L a).fst = aug a := by intro a; simp [L, TrivSqZeroExt.algebraMap_eq_inl]
  have hLsnd : ∀ a, (L a).snd = D a := by intro a; simp [L, TrivSqZeroExt.algebraMap_eq_inl]
  let φ : A →ₐ[k] DualNumber k := AlgHom.ofLinearMap L
    (by ext <;> simp [hLfst, hLsnd, hD])
    (by intro a b; ext <;> simp [hLfst, hLsnd, hDmul] <;> ring)
  have hφ : ∀ a, φ a = L a := fun a => rfl
  refine ⟨φ, ?_, ?_, x, hxm, ?_⟩
  · ext a; simp [hφ, hLfst]
  · intro a ha
    ext
    · simp [hφ, hLfst]; exact hIm ha
    · simp only [hφ, hLsnd, TrivSqZeroExt.snd_zero]
      rw [hD]
      have : aug a = 0 := hIm ha
      rw [this, map_zero, sub_zero]
      exact hgN a (Ideal.mem_sup_right ha)
  · intro h0
    apply hf
    have := congrArg TrivSqZeroExt.snd h0
    rw [hφ, hLsnd, hD, TrivSqZeroExt.snd_zero, (RingHom.mem_ker).mp hxm, map_zero, sub_zero] at this
    exact this

end GlobalTheory.NotLeSqSup

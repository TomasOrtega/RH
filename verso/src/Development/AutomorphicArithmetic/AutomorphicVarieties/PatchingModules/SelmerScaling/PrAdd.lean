import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.SelmerScaling.EpC
open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.AlgebraTools UpperTheory.V.Pa

/- English proof (translation)
Introduce `l _ S`. Establish `h1 : ∀ a, algebraMap S.Bh S.U.AA (S.pr0 a) + (S.pr1 a : S.U.AA) = a`. Introduce `a`. Simplify using `[Ctx.pr1]`. Establish `h2 : ∀ (b : S.Bh) (y : S.U.N), S.pr0 (algebraMap S.Bh S.U.AA b + y) = b ∧ S.pr1 (algebraMap S.Bh S.U.AA b + y) = y`.

Introduce `b y`. Establish `e` using `h1 (algebraMap S.Bh S.U.AA b + y)`. Establish `hm : algebraMap S.Bh S.U.AA (S.pr0 (algebraMap S.Bh S.U.AA b + y) - b) ∈ S.U.N`. Establish `: algebraMap S.Bh S.U.AA (S.pr0 (algebraMap S.Bh S.U.AA b + y) - b) = (y : S.U.AA) - (S.pr1 (algebraMap S.Bh S.U.AA b + y) : S.U.AA)`. Rewrite using `[map_sub]`.

Take the linear combination `e`. Rewrite using `[this]`. Conclude with `S.U.N.sub_mem y.2 (S.pr1 _).2`. Establish `hz : algebraMap S.Bh S.U.AA (S.pr0 (algebraMap S.Bh S.U.AA b + y) - b) = 0` using `Submodule.disjoint_def.1 S.U.compl.disjoint _ (Submodule.mem_one.2 ⟨_, rfl⟩) hm`. Establish `hb : S.pr0 (algebraMap S.Bh S.U.AA b + y) = b` using `sub_eq_zero.1 (S.U.inj (by rw [hz, map_zero]))`.

Use `⟨hb, Subtype.ext ?_⟩` and prove the remaining obligations. Rewrite `e` using `[hb]`. Conclude with `add_left_cancel e`. Establish `key : ∀ (a : S.U.AA) (b : S.Bh) (y : S.U.N), a = algebraMap S.Bh S.U.AA b + y → S.pr0 a = b ∧ S.pr1 a = y`. Introduce and unpack `a b y rfl`.

Conclude with `h2 b y`. Establish `hi : ired S.U.N ≤ maximalIdeal S.Bh`. Use `Ideal.span_le.2 ?_` and prove the remaining obligations. Introduce and unpack `b ⟨x, hx, y, hy, e⟩`. Take `⟨c, hc, e'⟩` from `S.U.mul_mem x hx y hy`.

Establish `: b = c` using `S.U.inj (e.symm.trans e')`. Rewrite using `[this]`. Conclude with `hc`. Use `⟨h1, h2, fun a a' => key _ _ _ ?_, fun b a => key _ _ _ ?_, fun a a' => ?_, hi, ?_⟩` and prove the remaining obligations. Rewrite using `[map_add, Submodule.coe_add]`.

Take the linear combination `- h1 a - h1 a'`. Rewrite using `[map_mul, Submodule.coe_smul, Algebra.smul_def, Algebra.smul_def, ← mul_add, h1]`. Take `⟨c, -, e⟩` from `S.U.mul_mem _ (S.pr1 a).2 _ (S.pr1 a').2`. Use `key (a * a') (S.pr0 a * S.pr0 a' + c) (S.pr0 a • S.pr1 a' + S.pr0 a' • S.pr1 a) (by` as an intermediate fact. Rewrite using `[map_add, map_mul, Submodule.coe_add, Submodule.coe_smul, Submodule.coe_smul, Algebra.smul_def, Algebra.smul_def, ← e]`.

Establish `e1` using `h1 a`. Establish `e2` using `h1 a'`. Take the linear combination `(- a') * e1 - (algebraMap S.Bh S.U.AA (S.pr0 a) + (S.pr1 a : S.U.AA)) * e2)`. Use `⟨?_, this.2⟩` and prove the remaining obligations. Rewrite using `[this.1, add_sub_cancel_left]`.

Conclude with `Ideal.subset_span ⟨_, (S.pr1 a).2, _, (S.pr1 a').2, e⟩`. Use `sup_le (sup_le ?_ (Ideal.pow_le_self two_ne_zero)) hi` and prove the remaining obligations. Conclude with `((IsLocalRing.local_hom_TFAE (algebraMap S.OO S.Bh)).out 0 2).1 (IsCO.isLocalHom (O := S.OO) (R := S.Bh))`.
-/
theorem UpperTheory.V.Pa.prAdd :
    ∀ (l : ℕ) [Fact l.Prime] (S : Ctx l), (∀ a, algebraMap S.Bh S.U.AA (S.pr0 a) + (S.pr1 a : S.U.AA) = a) ∧ (∀ (b : S.Bh) (y : S.U.N), S.pr0 (algebraMap S.Bh S.U.AA b + y) = b ∧ S.pr1 (algebraMap S.Bh S.U.AA b + y) = y) ∧ (∀ a a', S.pr0 (a + a') = S.pr0 a + S.pr0 a' ∧ S.pr1 (a + a') = S.pr1 a + S.pr1 a') ∧ (∀ (b : S.Bh) a, S.pr0 (b • a) = b * S.pr0 a ∧ S.pr1 (b • a) = b • S.pr1 a) ∧ (∀ a a', S.pr0 (a * a') - S.pr0 a * S.pr0 a' ∈ ired S.U.N ∧ S.pr1 (a * a') = S.pr0 a • S.pr1 a' + S.pr0 a' • S.pr1 a) ∧ ired S.U.N ≤ maximalIdeal S.Bh ∧ S.J2 ≤ maximalIdeal S.Bh := by
  intro l _ S
  have h1 : ∀ a, algebraMap S.Bh S.U.AA (S.pr0 a) + (S.pr1 a : S.U.AA) = a := by
    intro a
    simp [Ctx.pr1]
  have h2 : ∀ (b : S.Bh) (y : S.U.N), S.pr0 (algebraMap S.Bh S.U.AA b + y) = b ∧
      S.pr1 (algebraMap S.Bh S.U.AA b + y) = y := by
    intro b y
    have e := h1 (algebraMap S.Bh S.U.AA b + y)
    have hm : algebraMap S.Bh S.U.AA (S.pr0 (algebraMap S.Bh S.U.AA b + y) - b) ∈ S.U.N := by
      have : algebraMap S.Bh S.U.AA (S.pr0 (algebraMap S.Bh S.U.AA b + y) - b) =
          (y : S.U.AA) - (S.pr1 (algebraMap S.Bh S.U.AA b + y) : S.U.AA) := by
        rw [map_sub]; linear_combination e
      rw [this]
      exact S.U.N.sub_mem y.2 (S.pr1 _).2
    have hz : algebraMap S.Bh S.U.AA (S.pr0 (algebraMap S.Bh S.U.AA b + y) - b) = 0 :=
      Submodule.disjoint_def.1 S.U.compl.disjoint _ (Submodule.mem_one.2 ⟨_, rfl⟩) hm
    have hb : S.pr0 (algebraMap S.Bh S.U.AA b + y) = b :=
      sub_eq_zero.1 (S.U.inj (by rw [hz, map_zero]))
    refine ⟨hb, Subtype.ext ?_⟩
    rw [hb] at e
    exact add_left_cancel e
  have key : ∀ (a : S.U.AA) (b : S.Bh) (y : S.U.N), a = algebraMap S.Bh S.U.AA b + y →
      S.pr0 a = b ∧ S.pr1 a = y := by
    rintro a b y rfl
    exact h2 b y
  have hi : ired S.U.N ≤ maximalIdeal S.Bh := by
    refine Ideal.span_le.2 ?_
    rintro b ⟨x, hx, y, hy, e⟩
    obtain ⟨c, hc, e'⟩ := S.U.mul_mem x hx y hy
    have : b = c := S.U.inj (e.symm.trans e')
    rw [this]; exact hc
  refine ⟨h1, h2, fun a a' => key _ _ _ ?_, fun b a => key _ _ _ ?_, fun a a' => ?_, hi, ?_⟩
  · rw [map_add, Submodule.coe_add]
    linear_combination - h1 a - h1 a'
  · rw [map_mul, Submodule.coe_smul, Algebra.smul_def, Algebra.smul_def, ← mul_add, h1]
  · obtain ⟨c, -, e⟩ := S.U.mul_mem _ (S.pr1 a).2 _ (S.pr1 a').2
    have := key (a * a') (S.pr0 a * S.pr0 a' + c) (S.pr0 a • S.pr1 a' + S.pr0 a' • S.pr1 a) (by
      rw [map_add, map_mul, Submodule.coe_add, Submodule.coe_smul, Submodule.coe_smul, Algebra.smul_def,
        Algebra.smul_def, ← e]
      have e1 := h1 a
      have e2 := h1 a'
      linear_combination (- a') * e1 - (algebraMap S.Bh S.U.AA (S.pr0 a) + (S.pr1 a : S.U.AA)) * e2)
    refine ⟨?_, this.2⟩
    rw [this.1, add_sub_cancel_left]
    exact Ideal.subset_span ⟨_, (S.pr1 a).2, _, (S.pr1 a').2, e⟩
  · refine sup_le (sup_le ?_ (Ideal.pow_le_self two_ne_zero)) hi
    exact ((IsLocalRing.local_hom_TFAE (algebraMap S.OO S.Bh)).out 0 2).1 (IsCO.isLocalHom (O := S.OO) (R := S.Bh))

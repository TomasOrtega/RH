import Mathlib
import Formalism.SharpRestriction.Divisibility.SchurIrreducible
import Development.AbelianVarietyTheory.Definitions.Foundations.IsFockIPOfFockData
open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible GlobalTheory.FockAlg MvPolynomial

noncomputable section
namespace GlobalTheory.IrrTensor

section General
variable {V : Type} [AddCommGroup V] [Module ℂ V] {ι : Type} (A : ι → Module.End ℂ V)

/- English proof (translation)
Set `R` to `Algebra.adjoin ℂ (Set.range A)`. Establish `hA : ∀ Z, A Z ∈ R` using `fun Z => Algebra.subset_adjoin ⟨Z, rfl⟩`. Use `haveI : IsSimpleModule R V := by`. Use `(isSimpleModule_iff R V).2 ?_` and prove the remaining obligations. Use `{ toNontrivial := (Submodule.nontrivial_iff R).2 inferInstance, eq_bot_or_eq_top := fun N => ?_ }` and prove the remaining obligations.

Break down `hirr (N.restrictScalars ℂ) (fun Z y hy => N.smul_mem (⟨A Z, hA Z⟩ : R) hy) with h | h` into its components or cases. Use `left`. Conclude with `(Submodule.restrictScalars_eq_bot_iff ℂ R V).1 h`. Use `right`. Conclude with `(Submodule.restrictScalars_eq_top_iff ℂ R V).1 h`.

Set `F : Module.End (Module.End R V) V` to `{ toFun := f map_add' := f.map_add map_smul' := fun g x => by`. Take `⟨c, hc⟩` from `hsch (g.restrictScalars ℂ) (fun Z => LinearMap.ext fun y => g.map_smul (⟨A Z, hA Z⟩ : R) y)`. Establish `hg : ∀ y, g y = c • y` using `fun y => LinearMap.congr_fun hc y`. Use `show f (g x) = g (f x)`. Rewrite using `[hg, hg, map_smul] }`.

Take `⟨r, hr⟩` from `jacobson_density (R := R) F s`. Conclude with `⟨r.1, r.2, fun m hm => hr m hm⟩`.
-/
theorem density [Nontrivial V]
    (hirr : ∀ N : Submodule ℂ V, (∀ Z, ∀ y ∈ N, A Z y ∈ N) → N = ⊥ ∨ N = ⊤)
    (hsch : ∀ T : V →ₗ[ℂ] V, (∀ Z, T ∘ₗ A Z = A Z ∘ₗ T) → ∃ c : ℂ, T = c • LinearMap.id)
    (f : Module.End ℂ V) (s : Finset V) :
    ∃ r ∈ Algebra.adjoin ℂ (Set.range A), ∀ m ∈ s, f m = r m := by
  let R := Algebra.adjoin ℂ (Set.range A)
  have hA : ∀ Z, A Z ∈ R := fun Z => Algebra.subset_adjoin ⟨Z, rfl⟩
  haveI : IsSimpleModule R V := by
    refine (isSimpleModule_iff R V).2 ?_
    refine { toNontrivial := (Submodule.nontrivial_iff R).2 inferInstance, eq_bot_or_eq_top := fun N => ?_ }
    rcases hirr (N.restrictScalars ℂ) (fun Z y hy => N.smul_mem (⟨A Z, hA Z⟩ : R) hy) with h | h
    · left
      exact (Submodule.restrictScalars_eq_bot_iff ℂ R V).1 h
    · right
      exact (Submodule.restrictScalars_eq_top_iff ℂ R V).1 h
  let F : Module.End (Module.End R V) V :=
    { toFun := f
      map_add' := f.map_add
      map_smul' := fun g x => by
        obtain ⟨c, hc⟩ := hsch (g.restrictScalars ℂ) (fun Z => LinearMap.ext fun y =>
          g.map_smul (⟨A Z, hA Z⟩ : R) y)
        have hg : ∀ y, g y = c • y := fun y => LinearMap.congr_fun hc y
        show f (g x) = g (f x)
        rw [hg, hg, map_smul] }
  obtain ⟨r, hr⟩ := jacobson_density (R := R) F s
  exact ⟨r.1, r.2, fun m hm => hr m hm⟩

variable {W : Type} [AddCommGroup W] [Module ℂ W]

end General

variable {p q : ℕ}

/- English proof (translation)
Simplify using `[wtSub, Submodule.mem_iInf, sub_eq_zero]`.
-/
theorem mem_wtSub {V : Type} [AddCommGroup V] [Module ℂ V] {act : Mat p q →ₗ[ℂ] Module.End ℂ V}
    {μ : Ix p q → ℚ} {v : V} : v ∈ wtSub act μ ↔ ∀ a, act (Eab a a) v = ((μ a : ℚ) : ℂ) • v := by
  simp [wtSub, Submodule.mem_iInf, sub_eq_zero]

/- English proof (translation)
Rewrite `hv`, the goal using `[mem_wtSub]`. Introduce `c`. Establish `h` using `LinearMap.congr_fun (hl (Eab c c) (Eab a b)) v`. Establish `e : (Eab c c * Eab a b - Eab a b * Eab c c : Mat p q) = (((if c = a then 1 else 0) - (if c = b then 1 else 0) : ℚ) : ℂ) • Eab a b`. Unfold `Eab`.

Establish `e1 : (Matrix.single c c 1 * Matrix.single a b 1 : Mat p q) = (if c = a then (1 : ℂ) else 0) • Matrix.single a b 1` using `by split_ifs with h`. Substitute `h` using the available equality. Simplify using the standard rewrite rules. Simplify using `[Matrix.single_mul_single_of_ne, h]`. Establish `e2 : (Matrix.single a b 1 * Matrix.single c c 1 : Mat p q) = (if c = b then (1 : ℂ) else 0) • Matrix.single a b 1` using `by split_ifs with h`.

Substitute `h` using the available equality. Simplify using the standard rewrite rules. Simplify using `[Matrix.single_mul_single_of_ne, Ne.symm h]`. Rewrite using `[e1, e2, ← sub_smul]`. Use `congr 1`.

Apply the tactic sequence `split_ifs <;> simp`. Rewrite `h` using `[e, map_smul, LinearMap.smul_apply, LinearMap.sub_apply, Module.End.mul_apply, Module.End.mul_apply, hv c, map_smul, eq_sub_iff_add_eq]`. Rewrite using `[← h, Rat.cast_add, add_smul, add_comm]`.
-/
theorem root_shift {V : Type} [AddCommGroup V] [Module ℂ V] {act : Mat p q →ₗ[ℂ] Module.End ℂ V}
    (hl : IsLieAct act) {μ : Ix p q → ℚ} {v : V} (hv : v ∈ wtSub act μ) (a b : Ix p q) :
    act (Eab a b) v ∈ wtSub act (fun c => μ c + ((if c = a then 1 else 0) - (if c = b then 1 else 0))) := by
  rw [mem_wtSub] at hv ⊢
  intro c
  have h := LinearMap.congr_fun (hl (Eab c c) (Eab a b)) v
  have e : (Eab c c * Eab a b - Eab a b * Eab c c : Mat p q) =
      (((if c = a then 1 else 0) - (if c = b then 1 else 0) : ℚ) : ℂ) • Eab a b := by
    unfold Eab
    have e1 : (Matrix.single c c 1 * Matrix.single a b 1 : Mat p q) =
        (if c = a then (1 : ℂ) else 0) • Matrix.single a b 1 := by
      split_ifs with h
      · subst h; simp
      · simp [Matrix.single_mul_single_of_ne, h]
    have e2 : (Matrix.single a b 1 * Matrix.single c c 1 : Mat p q) =
        (if c = b then (1 : ℂ) else 0) • Matrix.single a b 1 := by
      split_ifs with h
      · subst h; simp
      · simp [Matrix.single_mul_single_of_ne, Ne.symm h]
    rw [e1, e2, ← sub_smul]
    congr 1
    split_ifs <;> simp
  rw [e, map_smul, LinearMap.smul_apply, LinearMap.sub_apply, Module.End.mul_apply,
    Module.End.mul_apply, hv c, map_smul, eq_sub_iff_add_eq] at h
  rw [← h, Rat.cast_add, add_smul, add_comm]

/- English proof (translation)
Choose the witnesses or unpack the hypotheses as in `⟨μ₀, v₀, hv₀, hv₀'⟩ : ∃ μ v, v ∈ wtSub M.act μ ∧ v ≠ 0 := by`. Assume the negation of the conclusion as `h`. Use `push Not at h`. Take `⟨x, hx⟩` from `exists_ne (0 : M.V)`. Establish `: (⨆ μ : Ix p q → ℚ, wtSub M.act μ) = ⊥` using `iSup_eq_bot.2 fun μ => (Submodule.eq_bot_iff _).2 (h μ)`.

Establish `h2` using `M.wts x`. Rewrite `h2` using `[this]`. Conclude with `hx h2`. Take `⟨U, hfd, hU, hK⟩` from `M.kfin v₀`. Set `k : Ix p q → ℚ` to `Sum.elim (fun i => -((i : ℕ) : ℚ)) (fun i => -((i : ℕ) : ℚ))`.

Set `h : (Ix p q → ℚ) → ℚ` to `fun μ => ∑ a, k a * μ a`. Set `H : Mat p q` to `∑ a, ((k a : ℚ) : ℂ) • Eab a a`. Establish `hKE : ∀ a b : Ix p q, sameBlock a b → IsKC (Eab a b)`. Introduce `a b hab c d hcd`. Unfold `Eab`.

Rewrite using `[Matrix.single_apply, if_neg]`. Introduce and unpack `⟨rfl, rfl⟩`. Conclude with `hcd hab`. Establish `hH : ∀ x ∈ U, M.act H x ∈ U`. Introduce `x hx`.

Simplify using `only [H, map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply]`. Apply the tactic sequence `exact U.sum_mem fun a _ => U.smul_mem _ (hK _ (hKE a a (by cases a <;> trivial)) x hx)`. Set `S : Set (Ix p q → ℚ)` to `{μ | ∃ v ∈ U, v ∈ wtSub M.act μ ∧ v ≠ 0}`. Establish `hfin : (h '' S).Finite`. Establish `h1` using `Module.End.finite_hasEigenvalue ((M.act H).restrict hH)`.

Use `(h1.preimage (f := fun x : ℚ => (x : ℂ)) Rat.cast_injective.injOn).subset ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨μ, ⟨v, hvU, hv, hv0⟩, rfl⟩`. Use `Module.End.hasEigenvalue_of_hasEigenvector (x := ⟨v, hvU⟩) ⟨?_, fun e => hv0 (congrArg Subtype.val e)⟩` and prove the remaining obligations. Rewrite using `[Module.End.mem_eigenspace_iff]`. Apply `Subtype.ext` to reduce the goal to its premises.

Use `show M.act H v = ((h μ : ℚ) : ℂ) • v`. Simplify using `only [H, h, map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, mem_wtSub.1 hv, smul_smul, ← Finset.sum_smul]`. Use `push_cast`. Both sides reduce to the same expression. Take `⟨_, ⟨μ, ⟨v, hvU, hv, hv0⟩, rfl⟩, hmax⟩` from `Set.exists_max_image (h '' S) id hfin ⟨_, μ₀, ⟨v₀, hU, hv₀, hv₀'⟩, rfl⟩`.

Use `⟨μ, v, hv0, hv, ?_⟩` and prove the remaining obligations. Simplify using `only [SetLike.mem_coe, Submodule.mem_iInf, LinearMap.mem_ker]`. Introduce `a b hab`. Assume the negation of the conclusion as `hne`. Apply the tactic sequence `have hs : sameBlock a b := by cases a <;> cases b <;> first | trivial | exact hab`.

Establish `hlt : k b < k a`. Apply the tactic sequence `cases a <;> cases b <;> first | exact hab.elim | skip`. Use `all_goals`. Simplify using `only [k, Sum.elim_inl, Sum.elim_inr, neg_lt_neg_iff, Nat.cast_lt]`. Conclude with `hab`.

Use `hmax _ ⟨_, ⟨_, hK _ (hKE a b hs) v hvU, root_shift M.lie hv a b, hne⟩, rfl⟩` as an intermediate fact. Simplify using `only [id, h, mul_add, mul_sub, Finset.sum_add_distrib, Finset.sum_sub_distrib, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true] at this`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem exists_highest (M : GKMod p q) [Nontrivial M.V] : ∃ μ v, IsHW M.act μ v := by
  obtain ⟨μ₀, v₀, hv₀, hv₀'⟩ : ∃ μ v, v ∈ wtSub M.act μ ∧ v ≠ 0 := by
    by_contra h
    push Not at h
    obtain ⟨x, hx⟩ := exists_ne (0 : M.V)
    have : (⨆ μ : Ix p q → ℚ, wtSub M.act μ) = ⊥ :=
      iSup_eq_bot.2 fun μ => (Submodule.eq_bot_iff _).2 (h μ)
    have h2 := M.wts x
    rw [this] at h2
    exact hx h2
  obtain ⟨U, hfd, hU, hK⟩ := M.kfin v₀
  let k : Ix p q → ℚ := Sum.elim (fun i => -((i : ℕ) : ℚ)) (fun i => -((i : ℕ) : ℚ))
  let h : (Ix p q → ℚ) → ℚ := fun μ => ∑ a, k a * μ a
  let H : Mat p q := ∑ a, ((k a : ℚ) : ℂ) • Eab a a
  have hKE : ∀ a b : Ix p q, sameBlock a b → IsKC (Eab a b) := by
    intro a b hab c d hcd
    unfold Eab
    rw [Matrix.single_apply, if_neg]
    rintro ⟨rfl, rfl⟩
    exact hcd hab
  have hH : ∀ x ∈ U, M.act H x ∈ U := by
    intro x hx
    simp only [H, map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply]
    exact U.sum_mem fun a _ => U.smul_mem _ (hK _ (hKE a a (by cases a <;> trivial)) x hx)
  let S : Set (Ix p q → ℚ) := {μ | ∃ v ∈ U, v ∈ wtSub M.act μ ∧ v ≠ 0}
  have hfin : (h '' S).Finite := by
    have h1 := Module.End.finite_hasEigenvalue ((M.act H).restrict hH)
    refine (h1.preimage (f := fun x : ℚ => (x : ℂ)) Rat.cast_injective.injOn).subset ?_
    rintro _ ⟨μ, ⟨v, hvU, hv, hv0⟩, rfl⟩
    refine Module.End.hasEigenvalue_of_hasEigenvector (x := ⟨v, hvU⟩) ⟨?_, fun e => hv0 (congrArg Subtype.val e)⟩
    rw [Module.End.mem_eigenspace_iff]
    apply Subtype.ext
    show M.act H v = ((h μ : ℚ) : ℂ) • v
    simp only [H, h, map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply,
      mem_wtSub.1 hv, smul_smul, ← Finset.sum_smul]
    push_cast
    rfl
  obtain ⟨_, ⟨μ, ⟨v, hvU, hv, hv0⟩, rfl⟩, hmax⟩ :=
    Set.exists_max_image (h '' S) id hfin ⟨_, μ₀, ⟨v₀, hU, hv₀, hv₀'⟩, rfl⟩
  refine ⟨μ, v, hv0, hv, ?_⟩
  simp only [SetLike.mem_coe, Submodule.mem_iInf, LinearMap.mem_ker]
  intro a b hab
  by_contra hne
  have hs : sameBlock a b := by cases a <;> cases b <;> first | trivial | exact hab
  have hlt : k b < k a := by
    cases a <;> cases b <;> first | exact hab.elim | skip
    all_goals
      simp only [k, Sum.elim_inl, Sum.elim_inr, neg_lt_neg_iff, Nat.cast_lt]
      exact hab
  have := hmax _ ⟨_, ⟨_, hK _ (hKE a b hs) v hvU, root_shift M.lie hv a b, hne⟩, rfl⟩
  simp only [id, h, mul_add, mul_sub, Finset.sum_add_distrib, Finset.sum_sub_distrib, mul_ite,
    mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true] at this
  linarith

/- English proof (translation)
Use `haveI := hI.1`. Take `⟨μ, v, hv0, hv⟩` from `exists_highest M`. Establish `hf : ∀ Z x, T (M.act Z x) = M.act Z (T x)` using `fun Z x => LinearMap.congr_fun (hT Z) x`. Establish `hst : ∀ x ∈ hwSub M.act μ, T x ∈ hwSub M.act μ`. Introduce `x hx`.

Simplify using `only [hwSub, wtSub, Submodule.mem_inf, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply] at hx ⊢`. Use `⟨fun c => ?_, fun c d h => ?_⟩` and prove the remaining obligations. Rewrite using `[← hf, ← map_smul, ← map_sub, hx.1 c, map_zero]`. Rewrite using `[← hf, hx.2 c d h, map_zero]`. Use `haveI := hA μ`.

Use `haveI : Nontrivial (hwSub M.act μ) := ⟨⟨⟨v, hv⟩, 0, fun e => hv0 (congrArg Subtype.val e)⟩⟩`. Take `⟨c, hc⟩` from `Module.End.exists_eigenvalue (T.restrict hst)`. Take `⟨x, hx⟩` from `hc.exists_hasEigenvector`. Establish `hx1 : T x = c • (x : M.V)` using `congrArg Subtype.val hx.apply_eq_smul`. Use `⟨c, ?_⟩` and prove the remaining obligations.

Break down `hI.2 (LinearMap.ker (T - c • LinearMap.id)) (fun Z y hy => by` into its components or cases. Simplify using `only [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply, sub_eq_zero] at hy ⊢`. Rewrite using `[hf, hy, map_smul]) with h | h`. Conclude with `absurd (Subtype.ext ((Submodule.eq_bot_iff _).1 h x (by simp [hx1]))) hx.2`. Conclude with `sub_eq_zero.1 (LinearMap.ker_eq_top.1 h)`.
-/
theorem schur (M : GKMod p q) (hI : IrrGK M) (hA : AdmGK M) (T : M.V →ₗ[ℂ] M.V)
    (hT : ∀ Z, T ∘ₗ M.act Z = M.act Z ∘ₗ T) : ∃ c : ℂ, T = c • LinearMap.id := by
  haveI := hI.1
  obtain ⟨μ, v, hv0, hv⟩ := exists_highest M
  have hf : ∀ Z x, T (M.act Z x) = M.act Z (T x) := fun Z x => LinearMap.congr_fun (hT Z) x
  have hst : ∀ x ∈ hwSub M.act μ, T x ∈ hwSub M.act μ := by
    intro x hx
    simp only [hwSub, wtSub, Submodule.mem_inf, Submodule.mem_iInf, LinearMap.mem_ker,
      LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply] at hx ⊢
    refine ⟨fun c => ?_, fun c d h => ?_⟩
    · rw [← hf, ← map_smul, ← map_sub, hx.1 c, map_zero]
    · rw [← hf, hx.2 c d h, map_zero]
  haveI := hA μ
  haveI : Nontrivial (hwSub M.act μ) := ⟨⟨⟨v, hv⟩, 0, fun e => hv0 (congrArg Subtype.val e)⟩⟩
  obtain ⟨c, hc⟩ := Module.End.exists_eigenvalue (T.restrict hst)
  obtain ⟨x, hx⟩ := hc.exists_hasEigenvector
  have hx1 : T x = c • (x : M.V) := congrArg Subtype.val hx.apply_eq_smul
  refine ⟨c, ?_⟩
  rcases hI.2 (LinearMap.ker (T - c • LinearMap.id)) (fun Z y hy => by
    simp only [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply,
      sub_eq_zero] at hy ⊢
    rw [hf, hy, map_smul]) with h | h
  · exact absurd (Subtype.ext ((Submodule.eq_bot_iff _).1 h x (by simp [hx1]))) hx.2
  · exact sub_eq_zero.1 (LinearMap.ker_eq_top.1 h)

end GlobalTheory.IrrTensor

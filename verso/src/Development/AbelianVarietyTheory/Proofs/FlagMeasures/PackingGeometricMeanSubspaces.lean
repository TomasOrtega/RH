import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.PackingGeometricMeanSeparated

open Finset

namespace GlobalTheory

/- English proof (translation)
Introduce `ι _ _ W _ _ _ U N hU α T y la X hla hX hT hsep`. Establish `hcard : 0 < Fintype.card ι` using `Fintype.card_pos`. Establish `hexp : (1 : ℝ) / Fintype.card ι ≠ 0`. Establish `: (0 : ℝ) < Fintype.card ι` using `by exact_mod_cast hcard`. Check the signs of the components of the expression.

Establish `hinj : Set.InjOn y T`. Introduce `t ht t' ht' he`. Assume the negation of the conclusion as `hne`. Establish `h` using `hsep t ht t' ht' hne`. Rewrite `h` using `[he]`.

Simplify using `only [sub_self, norm_zero] at h`. Establish `h0 : (∏ _v : ι, (0 : ℝ)) = 0` using `Finset.prod_eq_zero (Finset.mem_univ (Classical.arbitrary ι)) rfl`. Rewrite `h` using `[h0, Real.zero_rpow hexp]`. Combine the linear equalities and inequalities to obtain the conclusion. Break down `Nat.eq_zero_or_pos N with hN | hN` into its components or cases.

Substitute `hN` using the available equality. Establish `hzero : ∀ t ∈ T, y t = 0`. Introduce `t ht`. Use function extensionality and compare the values at `v`. Establish `hb : U v = ⊥` using `Submodule.finrank_eq_zero.mp (Nat.le_zero.mp (hU v))`.

Establish `hm` using `(hT t ht v).1`. Rewrite `hm` using `[hb, Submodule.mem_bot]`. Conclude with `hm`. Establish `h1 : T.card ≤ 1`. Rewrite using `[Finset.card_le_one]`.

Introduce `a ha b hb`. Conclude with `hinj ha hb (by rw [hzero a ha, hzero b hb])`. Simplify using `only [zero_mul, pow_zero]`. Conclude with `h1` after adjusting the coercions. Establish `key` using `packing_geometric_mean_separated ι (fun v => ↥(U v) × (Fin (N - Module.finrank ℝ (U v)) → ℝ)) N hN (fun v => by`.

Simplify using `only [Module.finrank_prod, Module.finrank_fin_fun]`. Use `hU v` as an intermediate fact. Use the proof step `omega)`. Use `la`. Use the proof step `(↑(T.attach.image (fun t : T => fun v => ((⟨y t v, (hT t t.2 v).1⟩ : U v), (0 : Fin (N - Module.finrank ℝ (U v)) → ℝ)))))`.

Use the proof step `(fun _ => X) hla (fun _ => hX)`. Establish `hnormpt : ∀ (v : ι) (a : U v), ‖((a, (0 : Fin (N - Module.finrank ℝ (U v)) → ℝ)) : ↥(U v) × (Fin (N - Module.finrank ℝ (U v)) → ℝ))‖ = ‖(a : W)‖`. Introduce `v a`. Rewrite using `[Prod.norm_def, norm_zero, max_eq_left (norm_nonneg _)]`. Both sides reduce to the same expression.

Take `⟨-, hbound⟩` from `key (by`. Introduce `s hs s' hs' hne`. Simplify using `only [Finset.coe_image, Set.mem_image, Finset.mem_coe, Finset.mem_attach, true_and] at hs hs'`. Take `⟨a, rfl⟩` from `hs`. Take `⟨b, rfl⟩` from `hs'`.

Establish `hab : (a : α) ≠ b`. Introduce `h`. Apply `hne` to reduce the goal to its premises. Rewrite using `[Subtype.ext h]`. Establish `e : ∀ v, ‖((⟨y a v, (hT a a.2 v).1⟩ : U v), (0 : Fin (N - Module.finrank ℝ (U v)) → ℝ)) - ((⟨y b v, (hT b b.2 v).1⟩ : U v), (0 : Fin (N - Module.finrank ℝ (U v)) → ℝ))‖ = ‖y a v - y b v‖`.

Introduce `v`. Rewrite using `[Prod.mk_sub_mk, sub_zero, hnormpt]`. Both sides reduce to the same expression. Simplify using `only [e]`. Conclude with `hsep a a.2 b b.2 hab)`.

Establish `hset : {s ∈ (↑(T.attach.image (fun t : T => fun v => ((⟨y t v, (hT t t.2 v).1⟩ : U v), (0 : Fin (N - Module.finrank ℝ (U v)) → ℝ)))) : Set (∀ v, ↥(U v) × (Fin (N - Module.finrank ℝ (U v)) → ℝ))) | ∀ v, ‖s v‖ ≤ (fun _ => X) v} = ↑(T.attach.image (fun t : T => fun v => ((⟨y t v, (h …`. Apply `Set.sep_eq_self_iff_mem_true.mpr` to reduce the goal to its premises. Introduce `s hs`. Simplify using `only [Finset.coe_image, Set.mem_image, Finset.mem_coe, Finset.mem_attach, true_and] at hs`. Take `⟨a, rfl⟩` from `hs`.

Introduce `v`. Rewrite using `[hnormpt]`. Conclude with `(hT a a.2 v).2`. Establish `hinj' : Function.Injective (fun t : T => fun v => ((⟨y t v, (hT t t.2 v).1⟩ : U v), (0 : Fin (N - Module.finrank ℝ (U v)) → ℝ)))`. Introduce `a b hab`.

Apply `Subtype.ext` to reduce the goal to its premises. Apply `hinj a.2 b.2` to reduce the goal to its premises. Use function extensionality and compare the values at `v`. Use `congrFun hab v` as an intermediate fact. Simplify using `only [Prod.mk.injEq, Subtype.mk.injEq] at this`.

Conclude with `this.1`. Rewrite `hbound` using `[hset, Set.ncard_coe_finset, Finset.card_image_of_injective _ hinj', Finset.card_attach]`. Establish `hX' : (∏ _v : ι, X) ^ ((1 : ℝ) / Fintype.card ι) = X`. Rewrite using `[Finset.prod_const, Finset.card_univ, one_div]`. Conclude with `Real.pow_rpow_inv_natCast hX.le hcard.ne'`.

Rewrite `hbound` using `[hX']`. Conclude with `hbound`.
-/
theorem packing_geometric_mean_subspaces : ∀ (ι : Type) [Fintype ι] [Nonempty ι] (W : Type) [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W] (U : ι → Submodule ℝ W) (N : ℕ), (∀ v, Module.finrank ℝ (U v) ≤ N) → ∀ (α : Type) (T : Finset α) (y : α → ι → W) (la X : ℝ), 0 < la → 0 < X → (∀ t ∈ T, ∀ v, y t v ∈ U v ∧ ‖y t v‖ ≤ X) → (∀ t ∈ T, ∀ t' ∈ T, t ≠ t' → la ≤ (∏ v, ‖y t v - y t' v‖) ^ ((1 : ℝ) / Fintype.card ι)) → (T.card : ℝ) ≤ (1 + 2 * X / la) ^ (N * Fintype.card ι) := by
  intro ι _ _ W _ _ _ U N hU α T y la X hla hX hT hsep
  classical
  have hcard : 0 < Fintype.card ι := Fintype.card_pos
  have hexp : (1 : ℝ) / Fintype.card ι ≠ 0 := by
    have : (0 : ℝ) < Fintype.card ι := by exact_mod_cast hcard
    positivity

  have hinj : Set.InjOn y T := by
    intro t ht t' ht' he
    by_contra hne
    have h := hsep t ht t' ht' hne
    rw [he] at h
    simp only [sub_self, norm_zero] at h
    have h0 : (∏ _v : ι, (0 : ℝ)) = 0 :=
      Finset.prod_eq_zero (Finset.mem_univ (Classical.arbitrary ι)) rfl
    rw [h0, Real.zero_rpow hexp] at h
    linarith
  rcases Nat.eq_zero_or_pos N with hN | hN
  ·
    subst hN
    have hzero : ∀ t ∈ T, y t = 0 := by
      intro t ht
      funext v
      have hb : U v = ⊥ := Submodule.finrank_eq_zero.mp (Nat.le_zero.mp (hU v))
      have hm := (hT t ht v).1
      rw [hb, Submodule.mem_bot] at hm
      exact hm
    have h1 : T.card ≤ 1 := by
      rw [Finset.card_le_one]
      intro a ha b hb
      exact hinj ha hb (by rw [hzero a ha, hzero b hb])
    simp only [zero_mul, pow_zero]
    exact_mod_cast h1
  ·
    have key := packing_geometric_mean_separated ι
      (fun v => ↥(U v) × (Fin (N - Module.finrank ℝ (U v)) → ℝ)) N hN
      (fun v => by
        simp only [Module.finrank_prod, Module.finrank_fin_fun]
        have := hU v
        omega)
      la
      (↑(T.attach.image (fun t : T => fun v =>
        ((⟨y t v, (hT t t.2 v).1⟩ : U v), (0 : Fin (N - Module.finrank ℝ (U v)) → ℝ)))))
      (fun _ => X) hla (fun _ => hX)
    have hnormpt : ∀ (v : ι) (a : U v),
        ‖((a, (0 : Fin (N - Module.finrank ℝ (U v)) → ℝ)) :
          ↥(U v) × (Fin (N - Module.finrank ℝ (U v)) → ℝ))‖ = ‖(a : W)‖ := by
      intro v a
      rw [Prod.norm_def, norm_zero, max_eq_left (norm_nonneg _)]
      rfl
    obtain ⟨-, hbound⟩ := key (by
      intro s hs s' hs' hne
      simp only [Finset.coe_image, Set.mem_image, Finset.mem_coe, Finset.mem_attach,
        true_and] at hs hs'
      obtain ⟨a, rfl⟩ := hs
      obtain ⟨b, rfl⟩ := hs'
      have hab : (a : α) ≠ b := by
        intro h
        apply hne
        rw [Subtype.ext h]
      have e : ∀ v, ‖((⟨y a v, (hT a a.2 v).1⟩ : U v),
            (0 : Fin (N - Module.finrank ℝ (U v)) → ℝ)) -
          ((⟨y b v, (hT b b.2 v).1⟩ : U v), (0 : Fin (N - Module.finrank ℝ (U v)) → ℝ))‖ =
          ‖y a v - y b v‖ := by
        intro v
        rw [Prod.mk_sub_mk, sub_zero, hnormpt]
        rfl
      simp only [e]
      exact hsep a a.2 b b.2 hab)
    have hset : {s ∈ (↑(T.attach.image (fun t : T => fun v =>
        ((⟨y t v, (hT t t.2 v).1⟩ : U v), (0 : Fin (N - Module.finrank ℝ (U v)) → ℝ)))) :
          Set (∀ v, ↥(U v) × (Fin (N - Module.finrank ℝ (U v)) → ℝ))) |
          ∀ v, ‖s v‖ ≤ (fun _ => X) v} =
        ↑(T.attach.image (fun t : T => fun v =>
          ((⟨y t v, (hT t t.2 v).1⟩ : U v), (0 : Fin (N - Module.finrank ℝ (U v)) → ℝ)))) := by
      apply Set.sep_eq_self_iff_mem_true.mpr
      intro s hs
      simp only [Finset.coe_image, Set.mem_image, Finset.mem_coe, Finset.mem_attach,
        true_and] at hs
      obtain ⟨a, rfl⟩ := hs
      intro v
      rw [hnormpt]
      exact (hT a a.2 v).2
    have hinj' : Function.Injective (fun t : T => fun v =>
        ((⟨y t v, (hT t t.2 v).1⟩ : U v), (0 : Fin (N - Module.finrank ℝ (U v)) → ℝ))) := by
      intro a b hab
      apply Subtype.ext
      apply hinj a.2 b.2
      funext v
      have := congrFun hab v
      simp only [Prod.mk.injEq, Subtype.mk.injEq] at this
      exact this.1
    rw [hset, Set.ncard_coe_finset, Finset.card_image_of_injective _ hinj',
      Finset.card_attach] at hbound
    have hX' : (∏ _v : ι, X) ^ ((1 : ℝ) / Fintype.card ι) = X := by
      rw [Finset.prod_const, Finset.card_univ, one_div]
      exact Real.pow_rpow_inv_natCast hX.le hcard.ne'
    rw [hX'] at hbound
    exact hbound

end GlobalTheory

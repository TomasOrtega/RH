import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.CapelliIdentity.ColAnti
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.CapelliIdentity.ProdOfFnUpdateEq

noncomputable section

open Finset

namespace ReciprocityTheory.ChartRestriction.DS.Lap.Capelli

open ReciprocityTheory.ChartRestriction.DS

section Ring

variable {𝒰 : Type*} [Ring 𝒰] [Algebra ℂ 𝒰] {n : ℕ} (E : Fin n → Fin n → 𝒰)

/- English proof (translation)
Establish `h` using `cminor_comm E hE a b (id : Fin n → Fin n) id x`. Simplify using `only [id, Finset.sum_ite_eq', Finset.mem_univ, if_true] at h`. Distinguish the cases in `hab : a = b`. Substitute `hab` using the available equality. Rewrite `h` using `[show Function.update (id : Fin n → Fin n) a a = id from Function.update_eq_self a id, sub_self]`.

Conclude with `sub_eq_zero.1 h`. Establish `h1 : cminor E (Function.update (id : Fin n → Fin n) b a) id x = 0`. Apply `cminor_rows_not_inj` to reduce the goal to its premises. Introduce `hinj`. Establish `: Function.update (id : Fin n → Fin n) b a b = Function.update (id : Fin n → Fin n) b a a`.

Simplify using `[Function.update_of_ne hab]`. Conclude with `hab (hinj this).symm`. Establish `h2 : cminor E id (Function.update (id : Fin n → Fin n) a b) x = 0`. Apply `cminor_cols_not_inj E hE` to reduce the goal to its premises. Introduce `hinj`.

Establish `: Function.update (id : Fin n → Fin n) a b a = Function.update (id : Fin n → Fin n) a b b`. Simplify using `[Function.update_of_ne (Ne.symm hab)]`. Conclude with `hab (hinj this)`. Rewrite `h` using `[h1, h2, sub_self]`. Conclude with `sub_eq_zero.1 h`.
-/
theorem capelliC_central (hE : GlRelR E) (x : ℂ) (a b : Fin n) : Commute (E a b) (capelliC E x) := by
  have h := cminor_comm E hE a b (id : Fin n → Fin n) id x
  simp only [id, Finset.sum_ite_eq', Finset.mem_univ, if_true] at h
  by_cases hab : a = b
  · subst hab
    rw [show Function.update (id : Fin n → Fin n) a a = id from Function.update_eq_self a id, sub_self] at h
    exact sub_eq_zero.1 h
  · have h1 : cminor E (Function.update (id : Fin n → Fin n) b a) id x = 0 := by
      apply cminor_rows_not_inj
      intro hinj
      have : Function.update (id : Fin n → Fin n) b a b = Function.update (id : Fin n → Fin n) b a a := by
        simp [Function.update_of_ne hab]
      exact hab (hinj this).symm
    have h2 : cminor E id (Function.update (id : Fin n → Fin n) a b) x = 0 := by
      apply cminor_cols_not_inj E hE
      intro hinj
      have : Function.update (id : Fin n → Fin n) a b a = Function.update (id : Fin n → Fin n) a b b := by
        simp [Function.update_of_ne (Ne.symm hab)]
      exact hab (hinj this)
    rw [h1, h2, sub_self] at h
    exact sub_eq_zero.1 h

end Ring

section Module

variable {M : Type*} [AddCommGroup M] [Module ℂ M] {n : ℕ} (E : Fin n → Fin n → Module.End ℂ M)

/- English proof (translation)
Unfold `capEntry`. Apply the tactic sequence `split_ifs <;> simp [Module.algebraMap_end_apply]`.
-/
theorem capEntry_apply_end (x : ℂ) (a b : Fin n) (v : M) :
    capEntry E x a b v = E a b v + if a = b then x • v else 0 := by
  unfold capEntry
  split_ifs <;> simp [Module.algebraMap_end_apply]

/- English proof (translation)
Introduce `p`. Proceed by induction on `p with`. Consider the case `zero`. Introduce `r c _ _ _`. Simplify using the standard rewrite rules.

Consider the case `succ p ih`. Introduce `r c hr hrp hc`. Rewrite using `[List.ofFn_succ', List.prod_concat, Module.End.mul_apply]`. Establish `hcl : (c (Fin.last p) : ℕ) = p` using `by rw [hc]; simp`. Establish `hrl : (r (Fin.last p) : ℕ) ≤ p` using `by have := hrp (Fin.last p); omega`.

Break down `lt_or_eq_of_le hrl with hlt | heq` into its components or cases. Establish `hlt' : r (Fin.last p) < c (Fin.last p)`. Rewrite using `[Fin.lt_iff_val_lt_val, hcl]`. Conclude with `hlt`. Rewrite using `[capEntry_apply_end, hup _ _ hlt', if_neg (ne_of_lt hlt'), add_zero, map_zero]`.

Rewrite using `[if_neg]`. Introduce `hall`. Use `hall (Fin.last p)` as an intermediate fact. Simplify using `only [Fin.val_last] at this`. Use linear arithmetic over natural numbers and integers.

Establish `heq' : r (Fin.last p) = c (Fin.last p)` using `Fin.ext (by rw [heq, hcl])`. Rewrite using `[capEntry_apply_end, if_pos heq', heq', hd, ← add_smul, map_smul]`. Establish `hr' : Function.Injective (fun j : Fin p => r j.castSucc)` using `hr.comp (Fin.castSucc_injective p)`. Establish `hrp' : ∀ j : Fin p, (r j.castSucc : ℕ) < p`. Introduce `j`.

Establish `h1` using `hrp j.castSucc`. Establish `h2 : r j.castSucc ≠ r (Fin.last p)` using `fun h => (Fin.castSucc_lt_last j).ne (hr h)`. Establish `h3 : (r j.castSucc : ℕ) ≠ p` using `fun h => h2 (Fin.ext (by rw [h, heq]))`. Use linear arithmetic over natural numbers and integers. Establish `hc' : ∀ j : Fin p, (c j.castSucc : ℕ) = j` using `fun j => by rw [hc]; simp`.

Establish `key` using `ih (fun j => r j.castSucc) (fun j => c j.castSucc) hr' hrp' hc'`. Simplify using `only [Fin.coe_castSucc] at key ⊢`. Rewrite using `[key]`. Establish `hiff : (∀ j : Fin (p + 1), (r j : ℕ) = j) ↔ (∀ j : Fin p, (r j.castSucc : ℕ) = j)`. Prove the components needed by the constructor for the conclusion.

Introduce `h j`. Simplify using `using h j.castSucc`. Introduce `h j`. Break down `Fin.eq_castSucc_or_eq_last j with ⟨i, rfl⟩ | rfl` into its components or cases. Simplify using `using h i`.

Simplify using `using heq`. Distinguish the cases in `hall : ∀ j : Fin p, (r j.castSucc : ℕ) = j`. Rewrite using `[if_pos hall, if_pos (hiff.2 hall), smul_smul, Fin.prod_univ_castSucc]`. Use `congr 1`. Simplify using `only [Fin.coe_castSucc, Fin.val_last, hcl]`.

Expand and normalize the polynomial expressions, which then agree. Rewrite using `[if_neg hall, if_neg (fun h => hall (hiff.1 h)), smul_zero]`.
-/
theorem prod_ofFn_apply_highestWeight (μ : Fin n → ℂ) (v : M) (x : ℂ) (hup : ∀ a b, a < b → E a b v = 0)
    (hd : ∀ a, E a a v = μ a • v) :
    ∀ (p : ℕ) (r c : Fin p → Fin n), Function.Injective r → (∀ j, (r j : ℕ) < p) →
      (∀ j, (c j : ℕ) = j) →
      (List.ofFn fun j : Fin p => capEntry E (x - ((j : ℕ) : ℂ)) (r j) (c j)).prod v =
        if (∀ j, (r j : ℕ) = j) then (∏ j : Fin p, (x + μ (c j) - ((j : ℕ) : ℂ))) • v else 0 := by
  intro p
  induction p with
  | zero =>
    intro r c _ _ _
    simp
  | succ p ih =>
    intro r c hr hrp hc
    rw [List.ofFn_succ', List.prod_concat, Module.End.mul_apply]
    have hcl : (c (Fin.last p) : ℕ) = p := by rw [hc]; simp
    have hrl : (r (Fin.last p) : ℕ) ≤ p := by have := hrp (Fin.last p); omega
    rcases lt_or_eq_of_le hrl with hlt | heq
    · have hlt' : r (Fin.last p) < c (Fin.last p) := by
        rw [Fin.lt_iff_val_lt_val, hcl]; exact hlt
      rw [capEntry_apply_end, hup _ _ hlt', if_neg (ne_of_lt hlt'), add_zero, map_zero]
      rw [if_neg]
      intro hall
      have := hall (Fin.last p)
      simp only [Fin.val_last] at this
      omega
    · have heq' : r (Fin.last p) = c (Fin.last p) := Fin.ext (by rw [heq, hcl])
      rw [capEntry_apply_end, if_pos heq', heq', hd, ← add_smul, map_smul]
      have hr' : Function.Injective (fun j : Fin p => r j.castSucc) :=
        hr.comp (Fin.castSucc_injective p)
      have hrp' : ∀ j : Fin p, (r j.castSucc : ℕ) < p := by
        intro j
        have h1 := hrp j.castSucc
        have h2 : r j.castSucc ≠ r (Fin.last p) := fun h => (Fin.castSucc_lt_last j).ne (hr h)
        have h3 : (r j.castSucc : ℕ) ≠ p := fun h => h2 (Fin.ext (by rw [h, heq]))
        omega
      have hc' : ∀ j : Fin p, (c j.castSucc : ℕ) = j := fun j => by rw [hc]; simp
      have key := ih (fun j => r j.castSucc) (fun j => c j.castSucc) hr' hrp' hc'
      simp only [Fin.coe_castSucc] at key ⊢
      rw [key]
      have hiff : (∀ j : Fin (p + 1), (r j : ℕ) = j) ↔ (∀ j : Fin p, (r j.castSucc : ℕ) = j) := by
        constructor
        · intro h j; simpa using h j.castSucc
        · intro h j
          rcases Fin.eq_castSucc_or_eq_last j with ⟨i, rfl⟩ | rfl
          · simpa using h i
          · simpa using heq
      by_cases hall : ∀ j : Fin p, (r j.castSucc : ℕ) = j
      · rw [if_pos hall, if_pos (hiff.2 hall), smul_smul, Fin.prod_univ_castSucc]
        congr 1
        simp only [Fin.coe_castSucc, Fin.val_last, hcl]
        ring
      · rw [if_neg hall, if_neg (fun h => hall (hiff.1 h)), smul_zero]

/- English proof (translation)
Unfold `capelliC cminor`. Rewrite using `[LinearMap.sum_apply]`. Rewrite using `[Finset.sum_eq_single (1 : Equiv.Perm (Fin n))]`. Rewrite using `[LinearMap.smul_apply]`. Use `prod_ofFn_apply_highestWeight E μ v x hup hd n (fun j => (1 : Equiv.Perm (Fin n)) j) id (Equiv.injective _) (fun j => by simp) (fun j => rfl)` as an intermediate fact.

Simplify using `only [id] at this ⊢`. Rewrite using `[this, if_pos (fun j => by simp)]`. Simplify using the standard rewrite rules. Introduce `σ _ hσ`. Rewrite using `[LinearMap.smul_apply]`.

Use `prod_ofFn_apply_highestWeight E μ v x hup hd n (fun j => σ j) id (Equiv.injective _) (fun j => (σ j).2) (fun j => rfl)` as an intermediate fact. Simplify using `only [id] at this ⊢`. Rewrite using `[this, if_neg, smul_zero]`. Introduce `hall`. Apply `hσ` to reduce the goal to its premises.

Use extensionality with `j`. Simplify using `using hall j`. Introduce `h`. Conclude with `absurd (Finset.mem_univ _) h`.
-/
theorem capelliC_hw (μ : Fin n → ℂ) (v : M) (x : ℂ) (hup : ∀ a b, a < b → E a b v = 0)
    (hd : ∀ a, E a a v = μ a • v) :
    capelliC E x v = (∏ a : Fin n, (x + μ a - ((a : ℕ) : ℂ))) • v := by
  unfold capelliC cminor
  rw [LinearMap.sum_apply]
  rw [Finset.sum_eq_single (1 : Equiv.Perm (Fin n))]
  · rw [LinearMap.smul_apply]
    have := prod_ofFn_apply_highestWeight E μ v x hup hd n (fun j => (1 : Equiv.Perm (Fin n)) j) id
      (Equiv.injective _) (fun j => by simp) (fun j => rfl)
    simp only [id] at this ⊢
    rw [this, if_pos (fun j => by simp)]
    simp
  · intro σ _ hσ
    rw [LinearMap.smul_apply]
    have := prod_ofFn_apply_highestWeight E μ v x hup hd n (fun j => σ j) id
      (Equiv.injective _) (fun j => (σ j).2) (fun j => rfl)
    simp only [id] at this ⊢
    rw [this, if_neg, smul_zero]
    intro hall
    apply hσ
    ext j
    simpa using hall j
  · intro h; exact absurd (Finset.mem_univ _) h

/- English proof (translation)
Establish `hE' : GlRelR E` using `(isGlRep_iff_glRelR E).1 hE`. Use `set c : ℂ := ∏ a : Fin n, (x + (μ a : ℂ) - ((a : ℕ) : ℂ)) with hc`. Establish `hv' : capelliC E x v = c • v` using `capelliC_hw E (fun a => (μ a : ℂ)) v x hv.2 hv.1`. Set `T : Submodule ℂ M` to `LinearMap.ker (capelliC E x - c • (1 : Module.End ℂ M))`. Establish `hmem : ∀ w, w ∈ T ↔ capelliC E x w = c • w`.

Introduce `w`. Simplify using `only [T, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply, sub_eq_zero]`. Establish `hle : genSub E (Submodule.span ℂ {v}) ≤ T`. Apply `sInf_le` to reduce the goal to its premises. Use `⟨?_, ?_⟩` and prove the remaining obligations.

Rewrite using `[Submodule.span_le, Set.singleton_subset_iff]`. Conclude with `(hmem v).2 hv'`. Introduce `a b w hw`. Rewrite `hw`, the goal using `[hmem]`. Establish `hcomm` using `congrArg (fun f : Module.End ℂ M => f w) (capelliC_central E hE' x a b).eq`.

Simplify using `only [Module.End.mul_apply] at hcomm`. Rewrite using `[← hcomm, hw, map_smul]`. Introduce `y hy`. Conclude with `(hmem y).1 (hle hy)`.
-/
theorem capelliC_genSub (hE : IsGlRep E) (μ : Fin n → ℝ) (v : M) (hv : IsHWVec E μ v) (x : ℂ) :
    ∀ y ∈ genSub E (Submodule.span ℂ {v}),
      capelliC E x y = (∏ a : Fin n, (x + (μ a : ℂ) - ((a : ℕ) : ℂ))) • y := by
  have hE' : GlRelR E := (isGlRep_iff_glRelR E).1 hE
  set c : ℂ := ∏ a : Fin n, (x + (μ a : ℂ) - ((a : ℕ) : ℂ)) with hc
  have hv' : capelliC E x v = c • v :=
    capelliC_hw E (fun a => (μ a : ℂ)) v x hv.2 hv.1
  let T : Submodule ℂ M := LinearMap.ker (capelliC E x - c • (1 : Module.End ℂ M))
  have hmem : ∀ w, w ∈ T ↔ capelliC E x w = c • w := by
    intro w
    simp only [T, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply,
      sub_eq_zero]
  have hle : genSub E (Submodule.span ℂ {v}) ≤ T := by
    apply sInf_le
    refine ⟨?_, ?_⟩
    · rw [Submodule.span_le, Set.singleton_subset_iff]
      exact (hmem v).2 hv'
    · intro a b w hw
      rw [hmem] at hw ⊢
      have hcomm := congrArg (fun f : Module.End ℂ M => f w) (capelliC_central E hE' x a b).eq
      simp only [Module.End.mul_apply] at hcomm
      rw [← hcomm, hw, map_smul]
  intro y hy
  exact (hmem y).1 (hle hy)

end Module

end ReciprocityTheory.ChartRestriction.DS.Lap.Capelli

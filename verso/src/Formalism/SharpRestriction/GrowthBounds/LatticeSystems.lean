import Formalism.SubspaceCounting.ChoiceOfTopsRefined
import Formalism.GradedWeylDivisibility.FinalD
import Formalism.SharpRestriction.GrowthBounds.SelectionLemmas

noncomputable section

open scoped BigOperators

namespace Formalism.MainNotions.G.LatticeSystems

open Formalism.MainNotions.G Formalism.MainNotions.SelectionLemmas Formalism.G0

variable {p : ℕ}

/- English proof (translation)
Use `⟨∅, by simp, by simp, fun x hx => ?_⟩` and prove the remaining obligations. Apply `Submodule.mem_sup_left` to reduce the goal to its premises. Apply `Submodule.subset_span` to reduce the goal to its premises. Simplify using `only [Set.mem_iUnion]`. Use `⟨∅, by simp, x, hx, ?_⟩` and prove the remaining obligations.

Simplify using `[monoN]`.
-/
theorem allLE (G : GAtP p) (VV : Finset (Fin G.P.nV)) (m : ℕ) (Sv : Fin G.P.nV → ℕ)
    (M : Submodule G.O G.Fn) :
    AllButLE (p : G.O) M (prodIdeal G VV m Sv M) 0 (∑ v ∈ VV, Sv v) := by
  refine ⟨∅, by simp, by simp, fun x hx => ?_⟩
  apply Submodule.mem_sup_left
  apply Submodule.subset_span
  simp only [Set.mem_iUnion]
  refine ⟨∅, by simp, x, hx, ?_⟩
  simp [monoN]

/- English proof (translation)
Introduce and unpack `x ⟨⟨-, hx⟩, hx'⟩`. Rewrite `hx`, the goal using `[Submodule.ideal_span_singleton_smul]`. Take `⟨y, hy, rfl⟩` from `(Submodule.mem_smul_pointwise_iff_exists _ _ _).1 hx`. Distinguish the cases in `ha : a = 0`. Substitute `ha` using the available equality.

Simplify using the standard rewrite rules. Conclude with `(Submodule.mem_smul_pointwise_iff_exists _ _ _).2 ⟨y, hM'.2 a y hy ha hx', rfl⟩`.
-/
theorem sat_clause {O X : Type} [CommRing O] [AddCommGroup X] [Module O X] (a : O)
    (N M M' : Submodule O X) (hM' : IsSaturatedIn M' M) :
    (N ⊓ Ideal.span {a} • M) ⊓ M' ≤ Ideal.span {a} • M' := by
  rintro x ⟨⟨-, hx⟩, hx'⟩
  rw [Submodule.ideal_span_singleton_smul] at hx ⊢
  obtain ⟨y, hy, rfl⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).1 hx
  by_cases ha : a = 0
  · subst ha; simp
  · exact (Submodule.mem_smul_pointwise_iff_exists _ _ _).2 ⟨y, hM'.2 a y hy ha hx', rfl⟩

/- English proof (translation)
Rewrite using `[injective_iff_map_eq_zero]`. Introduce `x`. Proceed by induction on `x using Submodule.Quotient.induction_on with`. Consider the case `H x`. Introduce `hx`.

Establish `h2 : (Submodule.Quotient.mk (Submodule.inclusion h x) : ↥M ⧸ Submodule.comap M.subtype Nst) = 0` using `hx`. Rewrite `h2` using `[Submodule.Quotient.mk_eq_zero]`. Rewrite using `[Submodule.Quotient.mk_eq_zero]`. Conclude with `h2`.
-/
theorem inj_clause {O X : Type} [CommRing O] [AddCommGroup X] [Module O X]
    (Nst M M' : Submodule O X) (h : M' ≤ M) :
    Function.Injective (Submodule.mapQ (Submodule.comap M'.subtype Nst) (Submodule.comap M.subtype Nst)
      (Submodule.inclusion h) (fun _ hx => hx)) := by
  rw [injective_iff_map_eq_zero]
  intro x
  induction x using Submodule.Quotient.induction_on with
  | H x =>
    intro hx
    have h2 : (Submodule.Quotient.mk (Submodule.inclusion h x) :
        ↥M ⧸ Submodule.comap M.subtype Nst) = 0 := hx
    rw [Submodule.Quotient.mk_eq_zero] at h2
    rw [Submodule.Quotient.mk_eq_zero]
    exact h2

/- English proof (translation)
Establish `h` using `ManyOrbitsP.fact_esymm_le (VV.val.map κ) (by intro x hx; obtain ⟨v, hv, rfl⟩ := Multiset.mem_map.mp hx; exact hκ v hv) k`. Rewrite `h` using `[Finset.esymm_map_val]`. Establish `hs : (VV.val.map κ).sum = ∑ v ∈ VV, κ v` using `rfl`. Rewrite `h` using `[hs]`. Establish `hf : (0 : ℝ) < k.factorial` using `by exact_mod_cast Nat.factorial_pos k`.

Rewrite using `[le_div_iff₀ hf, mul_pow]`. Unfold `esymmOn`. Establish `hm : (0 : ℝ) ≤ (d : ℝ) * (m : ℝ) ^ k` using `by positivity`. Use polynomial arithmetic with `[mul_le_mul_of_nonneg_left h hm]`.
-/
theorem esymm_clause {ι : Type} (VV : Finset ι) (κ : ι → ℝ) (hκ : ∀ v ∈ VV, 0 ≤ κ v) (m d k : ℕ) :
    (d : ℝ) * (m : ℝ) ^ k * esymmOn VV κ k ≤
      (d : ℝ) * ((m : ℝ) * ∑ v ∈ VV, κ v) ^ k / (k.factorial : ℝ) := by
  have h := ManyOrbitsP.fact_esymm_le (VV.val.map κ)
    (by intro x hx; obtain ⟨v, hv, rfl⟩ := Multiset.mem_map.mp hx; exact hκ v hv) k
  rw [Finset.esymm_map_val] at h
  have hs : (VV.val.map κ).sum = ∑ v ∈ VV, κ v := rfl
  rw [hs] at h
  have hf : (0 : ℝ) < k.factorial := by exact_mod_cast Nat.factorial_pos k
  rw [le_div_iff₀ hf, mul_pow]
  unfold esymmOn
  have hm : (0 : ℝ) ≤ (d : ℝ) * (m : ℝ) ^ k := by positivity
  nlinarith [mul_le_mul_of_nonneg_left h hm]

section Prod

variable (G : GAtP p) (y : Fin G.P.nV → Module.End G.O G.Fn) (hy : ∀ v F, y v F = G.yv v F)

include hy in
/- English proof (translation)
Proceed by induction on `m generalizing x with`. Consider the case `zero => simp`. Consider the case `succ n ih`. Rewrite using `[pow_succ, Module.End.mul_apply, ih, hy, Function.iterate_succ_apply]`.
-/
theorem pr_iter (v : Fin G.P.nV) (m : ℕ) (x : G.Fn) : (y v ^ m) x = (G.yv v)^[m] x := by
  induction m generalizing x with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, Module.End.mul_apply, ih, hy, Function.iterate_succ_apply]

include hy in

/- English proof (translation)
Proceed by induction on `l with`. Consider the case `nil => simp`. Consider the case `cons i l ih`. Rewrite using `[List.map_cons, List.prod_cons, Module.End.mul_apply, ih]`. Consider the cases of `hε : ε i with`.

Consider the case `true`. Simplify using `only [hε, if_true, List.filter_cons, Bool.not_true, Bool.false_eq_true, if_false, List.map_cons, List.foldr_cons, Function.comp_apply]`. Rewrite using `[map_smul, pr_iter G y hy]`. Consider the case `false`. Simplify using `only [hε, Bool.false_eq_true, if_false, List.filter_cons, Bool.not_false, if_true, List.map_cons, List.sum_cons, LinearMap.smul_apply, Module.End.one_apply]`.

Rewrite using `[pow_mul, hπ, smul_smul, pow_add]`.
-/
theorem pr_list {V : ℕ} (e : Fin V → Fin G.P.nV) (m : ℕ) (Sv : Fin G.P.nV → ℕ) (π : G.O) (c : ℕ)
    (hπ : π ^ c = (p : G.O)) (ε : Fin V → Bool) (l : List (Fin V)) (x : G.Fn) :
    ((l.map fun i => if ε i then y (e i) ^ m else (π ^ (c * Sv (e i))) • (1 : Module.End G.O G.Fn)).prod) x =
      ((p : G.O) ^ ((l.filter fun i => !ε i).map fun i => Sv (e i)).sum) •
        (((l.filter fun i => ε i).map e).foldr (fun v f => (G.yv v)^[m] ∘ f) id) x := by
  induction l with
  | nil => simp
  | cons i l ih =>
    rw [List.map_cons, List.prod_cons, Module.End.mul_apply, ih]
    cases hε : ε i with
    | true =>
      simp only [hε, if_true, List.filter_cons, Bool.not_true, Bool.false_eq_true, if_false,
        List.map_cons, List.foldr_cons, Function.comp_apply]
      rw [map_smul, pr_iter G y hy]
    | false =>
      simp only [hε, Bool.false_eq_true, if_false, List.filter_cons, Bool.not_false, if_true,
        List.map_cons, List.sum_cons, LinearMap.smul_apply, Module.End.one_apply]
      rw [pow_mul, hπ, smul_smul, pow_add]

include hy in

/- English proof (translation)
Unfold `prodIdealMap`. Use `iSup_le fun ε => ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨x, hx, rfl⟩`. Unfold `monoOp`. Rewrite using `[pr_list G y hy e m Sv π c hπ ε]`.

Apply `Submodule.subset_span` to reduce the goal to its premises. Simplify using `only [Set.mem_iUnion]`. Use `⟨(Finset.univ.filter fun i => ε i = true).map e, ?_, x, hx, ?_⟩` and prove the remaining obligations. Rewrite using `[Finset.mem_powerset]`. Conclude with `Finset.map_subset_map.2 (Finset.filter_subset _ _)`.

Unfold `monoN`. Establish `hB : Finset.univ.map e \ (Finset.univ.filter fun i => ε i = true).map e = (Finset.univ.filter fun i => ε i = false).map e`. Use extensionality with `v`. Simplify using `only [Finset.mem_sdiff, Finset.mem_map, Finset.mem_univ, true_and, Finset.mem_filter]`. Prove the components needed by the constructor for the conclusion.

Introduce and unpack `⟨⟨i, rfl⟩, h2⟩`. Use `⟨i, ?_, rfl⟩` and prove the remaining obligations. Consider the cases of `hε : ε i with`. Consider the case `true => exact absurd ⟨i, hε, rfl⟩ h2`. Consider the case `false => rfl`.

Introduce and unpack `⟨i, hi, rfl⟩`. Use `⟨⟨i, rfl⟩, ?_⟩` and prove the remaining obligations. Introduce and unpack `⟨j, hj, hji⟩`. Rewrite `hj` using `[e.injective hji, hi]`. Conclude with `absurd hj (by simp)`.

Establish `hsum : ∑ v ∈ Finset.univ.map e \ (Finset.univ.filter fun i => ε i = true).map e, Sv v = (((List.finRange V).filter fun i => !ε i).map fun i => Sv (e i)).sum`. Rewrite using `[hB, Finset.sum_map, ← List.sum_toFinset _ ((List.nodup_finRange V).filter _)]`. Apply `Finset.sum_congr _ (fun _ _ => rfl)` to reduce the goal to its premises. Use extensionality with `i`. Simplify using the standard rewrite rules.

Rewrite using `[hsum]`. Use `congr 1`. Establish `: LeftCommutative (fun (v : Fin G.P.nV) (f : G.Fn → G.Fn) => (G.yv v)^[m] ∘ f)` using `⟨fun u v f => by`. Use function extensionality and compare the values at `z`. Establish `hc : Function.Commute (G.yv u) (G.yv v)` using `fun F => hcomm u v F`.

Conclude with `(hc.iterate_iterate m m) (f z)⟩`. Establish `hperm : (((Finset.univ.filter fun i => ε i = true).map e).sort (· ≤ ·)).Perm (((List.finRange V).filter fun i => ε i).map e)`. Rewrite using `[List.perm_ext_iff_of_nodup (Finset.sort_nodup _ _) (((List.nodup_finRange V).filter _).map e.injective)]`. Introduce `a`. Simplify using the standard rewrite rules.

Conclude with `congrFun (hperm.foldr_eq id) x`.
-/
theorem pr_le {V : ℕ} (e : Fin V ↪ Fin G.P.nV)
    (hcomm : ∀ (u v : Fin G.P.nV) (F : G.Fn), G.yv u (G.yv v F) = G.yv v (G.yv u F))
    (m : ℕ) (Sv : Fin G.P.nV → ℕ) (π : G.O) (c : ℕ) (hπ : π ^ c = (p : G.O)) (M : Submodule G.O G.Fn) :
    prodIdealMap π (fun i => y (e i)) m (fun i => c * Sv (e i)) M ≤
      prodIdeal G (Finset.univ.map e) m Sv M := by
  classical
  unfold prodIdealMap
  refine iSup_le fun ε => ?_
  rintro _ ⟨x, hx, rfl⟩
  unfold monoOp
  rw [pr_list G y hy e m Sv π c hπ ε]
  apply Submodule.subset_span
  simp only [Set.mem_iUnion]
  refine ⟨(Finset.univ.filter fun i => ε i = true).map e, ?_, x, hx, ?_⟩
  · rw [Finset.mem_powerset]
    exact Finset.map_subset_map.2 (Finset.filter_subset _ _)
  · unfold monoN
    have hB : Finset.univ.map e \ (Finset.univ.filter fun i => ε i = true).map e =
        (Finset.univ.filter fun i => ε i = false).map e := by
      ext v
      simp only [Finset.mem_sdiff, Finset.mem_map, Finset.mem_univ, true_and, Finset.mem_filter]
      constructor
      · rintro ⟨⟨i, rfl⟩, h2⟩
        refine ⟨i, ?_, rfl⟩
        cases hε : ε i with
        | true => exact absurd ⟨i, hε, rfl⟩ h2
        | false => rfl
      · rintro ⟨i, hi, rfl⟩
        refine ⟨⟨i, rfl⟩, ?_⟩
        rintro ⟨j, hj, hji⟩
        rw [e.injective hji, hi] at hj
        exact absurd hj (by simp)
    have hsum : ∑ v ∈ Finset.univ.map e \ (Finset.univ.filter fun i => ε i = true).map e, Sv v =
        (((List.finRange V).filter fun i => !ε i).map fun i => Sv (e i)).sum := by
      rw [hB, Finset.sum_map, ← List.sum_toFinset _ ((List.nodup_finRange V).filter _)]
      apply Finset.sum_congr _ (fun _ _ => rfl)
      ext i
      simp
    rw [hsum]
    congr 1
    have : LeftCommutative (fun (v : Fin G.P.nV) (f : G.Fn → G.Fn) => (G.yv v)^[m] ∘ f) :=
      ⟨fun u v f => by
        funext z
        have hc : Function.Commute (G.yv u) (G.yv v) := fun F => hcomm u v F
        exact (hc.iterate_iterate m m) (f z)⟩
    have hperm : (((Finset.univ.filter fun i => ε i = true).map e).sort (· ≤ ·)).Perm
        (((List.finRange V).filter fun i => ε i).map e) := by
      rw [List.perm_ext_iff_of_nodup (Finset.sort_nodup _ _)
        (((List.nodup_finRange V).filter _).map e.injective)]
      intro a
      simp
    exact congrFun (hperm.foldr_eq id) x

end Prod

def extS {V n : ℕ} (e : Fin V ↪ Fin n) (σ : Fin V → Slot) : Fin n → Slot :=
  Function.extend e σ (fun _ => Slot.base)

/- English proof (translation)
Use function extensionality and compare the values at `v`. Distinguish the cases in `h : ∃ j, e j = v`. Take `⟨j, rfl⟩` from `h`. Unfold `extS`. Rewrite using `[e.injective.extend_apply]`.

Distinguish the cases in `hj : j = i`. Substitute `hj` using the available equality. Simplify using the standard rewrite rules. Rewrite using `[Function.update_of_ne hj, Function.update_of_ne (fun h => hj (e.injective h)), e.injective.extend_apply]`. Unfold `extS`.

Rewrite using `[Function.extend_apply' _ _ _ h, Function.update_of_ne (fun hv => h ⟨i, hv.symm⟩), Function.extend_apply' _ _ _ h]`.
-/
theorem extS_update {V n : ℕ} (e : Fin V ↪ Fin n) (σ : Fin V → Slot) (i : Fin V) (s : Slot) :
    extS e (Function.update σ i s) = Function.update (extS e σ) (e i) s := by
  funext v
  by_cases h : ∃ j, e j = v
  · obtain ⟨j, rfl⟩ := h
    unfold extS
    rw [e.injective.extend_apply]
    by_cases hj : j = i
    · subst hj; simp
    · rw [Function.update_of_ne hj, Function.update_of_ne (fun h => hj (e.injective h)),
        e.injective.extend_apply]
  · unfold extS
    rw [Function.extend_apply' _ _ _ h, Function.update_of_ne (fun hv => h ⟨i, hv.symm⟩),
      Function.extend_apply' _ _ _ h]

/- English proof (translation)
Use function extensionality and compare the values at `v`. Distinguish the cases in `h : ∃ j, e j = v`. Take `⟨j, rfl⟩` from `h`. Unfold `extS`. Rewrite using `[e.injective.extend_apply]`.

Unfold `extS`. Rewrite using `[Function.extend_apply' _ _ _ h]`.
-/
theorem extS_base {V n : ℕ} (e : Fin V ↪ Fin n) :
    extS e (fun _ => Slot.base) = fun _ => Slot.base := by
  funext v
  by_cases h : ∃ j, e j = v
  · obtain ⟨j, rfl⟩ := h
    unfold extS
    rw [e.injective.extend_apply]
  · unfold extS
    rw [Function.extend_apply' _ _ _ h]

/- English proof (translation)
Use function extensionality and compare the values at `v`. Distinguish the cases in `h : ∃ j, e j = v`. Take `⟨j, rfl⟩` from `h`. Unfold `extS`. Rewrite using `[e.injective.extend_apply]`.

Simplify using `[vertexLabel]`. Unfold `extS`. Rewrite using `[Function.extend_apply' _ _ _ h]`. Establish `: v ∉ B.map e`. Introduce `hv`.

Take `⟨j, -, hj⟩` from `Finset.mem_map.1 hv`. Conclude with `h ⟨j, hj⟩`. Simplify using `[vertexLabel, this]`.
-/
theorem extS_positionAt {V n : ℕ} (e : Fin V ↪ Fin n) (B : Finset (Fin V)) :
    extS e (vertexLabel B) = vertexLabel (B.map e) := by
  funext v
  by_cases h : ∃ j, e j = v
  · obtain ⟨j, rfl⟩ := h
    unfold extS
    rw [e.injective.extend_apply]
    simp [vertexLabel]
  · unfold extS
    rw [Function.extend_apply' _ _ _ h]
    have : v ∉ B.map e := by
      intro hv
      obtain ⟨j, -, hj⟩ := Finset.mem_map.1 hv
      exact h ⟨j, hj⟩
    simp [vertexLabel, this]

def RestWalk (G : GAtP p) (VV : Finset (Fin G.P.nV)) (t : Fin G.P.nV → ℕ) (Dd : ℕ)
    (κ : Fin G.P.nV → ℝ) : Prop :=
  ∃ L : (Fin G.P.nV → Slot) → Submodule G.O G.Fn,
    L (fun _ => Slot.base) = G.Mna ∧
    (∀ σ, ∀ v ∈ VV, L (Function.update σ v Slot.base) ≤ L (Function.update σ v Slot.ball)) ∧
    (∀ σ, ∀ v ∈ VV, L (Function.update σ v Slot.dual) ≤ L (Function.update σ v Slot.base)) ∧
    (∀ σ, ∀ v ∈ VV, ∀ x ∈ L (Function.update σ v Slot.ball),
      G.P.w ^ t v • x ∈ L (Function.update σ v Slot.base)) ∧
    (∀ σ, ∀ v ∈ VV, ∀ x ∈ L (Function.update σ v Slot.base),
      G.P.w ^ t v • x ∈ L (Function.update σ v Slot.dual)) ∧
    (∀ σ, ∀ v ∈ VV, ∀ x ∈ L (Function.update σ v Slot.ball),
      G.yv v x ∈ L (Function.update σ v Slot.dual)) ∧
    (∀ B : Finset (Fin G.P.nV), B ⊆ VV → B.Nonempty →
      ∃ C : Finset G.Fn, (↑C : Set G.Fn) ⊆ L (vertexLabel B) ∧
        (C.card : ℝ) ≤ (∏ v ∈ B, κ v) * (G.dna : ℝ) ∧
        ∀ x ∈ L (vertexLabel B), (p : G.O) ^ (Dd + 1) • x ∈
          (⨆ v ∈ B, Submodule.span G.O
            (G.yv v '' (L (Function.update (vertexLabel B) v Slot.ball) : Set G.Fn))) ⊔
            Submodule.span G.O (↑C : Set G.Fn))

/- English proof (translation)
Take `⟨L, hL0, h1, h2, h3, h4, h5, h6⟩` from `hR`. Establish `he : ∀ i, e i ∈ Finset.univ.map e` using `fun i => Finset.mem_map_of_mem e (Finset.mem_univ i)`. Establish `h6' : ∀ B : Finset (Fin V), ∃ C : Finset G.Fn, B.Nonempty → ((↑C : Set G.Fn) ⊆ L (vertexLabel (B.map e)) ∧ (C.card : ℝ) ≤ (∏ v ∈ B.map e, κ v) * (G.dna : ℝ) ∧ ∀ x ∈ L (vertexLabel (B.map e)), (p : G.O) ^ (Dd + 1) • x ∈ (⨆ v ∈ B.map e, Submodule.span G.O (G.yv v '' (L (Function.up …`. Introduce `B`. Distinguish the cases in `hB : B.Nonempty`.

Take `⟨C, hC⟩` from `h6 (B.map e) (Finset.map_subset_map.2 (Finset.subset_univ _)) (hB.map)`. Conclude with `⟨C, fun _ => hC⟩`. Conclude with `⟨∅, fun h => absurd h hB⟩`. Use `choose C hC using h6'`. Establish `W` using `(Top.walkSharp V G.P.w (fun σ => L (extS e σ)) (fun i => y (e i)) m β (2 * (Dd + 1)) (2 * S) (fun i => t (e i)) (fun i => t (e i)) (fun i => 2 * t (e i)) (fun i => 2 * Sv (e i)) (fun B => (C B).card) C hm (fun i j => by`.

Apply `LinearMap.ext` to reduce the goal to its premises. Introduce `F`. Simplify using `only [Module.End.mul_apply, hy]`. Conclude with `hcomm _ _ _)`. Use the proof step `(fun σ i => by simp only [extS_update]; exact h1 _ _ (he i))`.

Use the proof step `(fun σ i => by simp only [extS_update]; exact h2 _ _ (he i))`. Use the proof step `(fun σ i => by simp only [extS_update]; exact h3 _ _ (he i))`. Use the proof step `(fun σ i => by simp only [extS_update]; exact h4 _ _ (he i))`. Use the proof step `(fun σ i => by`. Simplify using `only [extS_update]`.

Introduce `x hx`. Rewrite using `[two_mul, pow_add, mul_smul]`. Conclude with `h4 _ _ (he i) _ (h3 _ _ (he i) _ hx))`. Use the proof step `(fun σ i => by`. Simplify using `only [extS_update, hy]`.

Conclude with `h5 _ _ (he i))`. Use the proof step `(fun B hB => by`. Establish `hBn : B.Nonempty`. Rewrite using `[← Finset.card_pos]`. Use linear arithmetic over natural numbers and integers.

Take `⟨c1, c2, c3⟩` from `hC B hBn`. Simplify using `only [extS_update, extS_positionAt]`. Use `⟨c1, le_rfl, fun x hx => ?_⟩` and prove the remaining obligations. Rewrite using `[pow_mul, hw]`. Use `SetLike.le_def.1 (sup_le_sup_right ?_ _) (c3 x hx)` and prove the remaining obligations.

Use `iSup₂_le fun v hv => ?_` and prove the remaining obligations. Take `⟨i, hi, rfl⟩` from `Finset.mem_map.1 hv`. Rewrite using `[Submodule.span_le]`. Introduce and unpack `_ ⟨z, hz, rfl⟩`. Use `Submodule.mem_iSup_of_mem i (Submodule.mem_iSup_of_mem hi ⟨z, hz, hy _ _⟩))` and prove the remaining obligations.

Use the proof step `(fun i => Nat.mul_le_mul_left 2 (hS _ (he i)))).1`. Simplify using `only [extS_base, hL0] at W`. Take `⟨Cc, hCM, hcard, hx⟩` from `W`. Use `⟨Cc, hCM, Nat.le_floor ?_, fun x hxM => ?_⟩` and prove the remaining obligations. Combine the equalities or inequalities in the displayed calculation.

Use `push_cast`. Apply `Finset.sum_le_sum` to reduce the goal to its premises. Introduce `B hB`. Establish `hBn : B.Nonempty`. Rewrite using `[← Finset.card_pos, (Finset.mem_powersetCard.1 hB).2]`.

Use linear arithmetic over natural numbers and integers. Conclude with `mul_le_mul_of_nonneg_left (hC B hBn).2.1 (by positivity)`. Use `_ = (G.dna : ℝ) * (m : ℝ) ^ (β + 1) * esymmOn (Finset.univ.map e) κ (β + 1) := by`. Unfold `esymmOn`. Rewrite using `[Finset.powersetCard_map, Finset.sum_map, Finset.mul_sum]`.

Apply `Finset.sum_congr rfl` to reduce the goal to its premises. Introduce `B _`. Use `show _ = _ * _ * ∏ v ∈ B.map e, κ v`. Expand and normalize the polynomial expressions, which then agree. Establish `hexp : ∑ i, (t (e i) + t (e i) + (m - 1) * (2 * t (e i)) + m * (2 * (Dd + 1))) + β * (2 * S) = 2 * (tau (Finset.univ.map e) m Dd t + β * S)`.

Unfold `tau`. Rewrite using `[Finset.sum_map]`. Take `⟨k, rfl⟩ : ∃ k, m = k + 1` from `⟨m - 1, by omega⟩`. Simplify using `only [Nat.add_sub_cancel]`. Establish `hs : ∑ i, (t (e i) + t (e i) + k * (2 * t (e i)) + (k + 1) * (2 * (Dd + 1))) = 2 * ∑ i, (k + 1) * (t (e i) + Dd + 1)`.

Rewrite using `[Finset.mul_sum]`. Apply `Finset.sum_congr rfl` to reduce the goal to its premises. Introduce `i _`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[hs]`.

Expand and normalize the polynomial expressions, which then agree. Establish `h7` using `hx x hxM`. Rewrite `h7` using `[hexp, pow_mul, hw]`. Conclude with `SetLike.le_def.1 (sup_le_sup_right (pr_le G y hy e hcomm m Sv G.P.w 2 hw G.Mna) _) h7`.
-/
theorem walk_allBut_bound (G : GAtP p) (y : Fin G.P.nV → Module.End G.O G.Fn) (hy : ∀ v F, y v F = G.yv v F)
    (hcomm : ∀ (u v : Fin G.P.nV) (F : G.Fn), G.yv u (G.yv v F) = G.yv v (G.yv u F))
    {V : ℕ} (e : Fin V ↪ Fin G.P.nV) (t Sv : Fin G.P.nV → ℕ) (Dd S m : ℕ) (κ : Fin G.P.nV → ℝ)
    (hw : G.P.w ^ 2 = (p : G.O)) (hm : 1 ≤ m) (hS : ∀ v ∈ Finset.univ.map e, Sv v ≤ S)
    (hR : RestWalk G (Finset.univ.map e) t Dd κ) (β : ℕ) :
    AllButLE (p : G.O) G.Mna (prodIdeal G (Finset.univ.map e) m Sv G.Mna)
      ⌊(G.dna : ℝ) * (m : ℝ) ^ (β + 1) * esymmOn (Finset.univ.map e) κ (β + 1)⌋₊
      (tau (Finset.univ.map e) m Dd t + β * S) := by
  classical
  obtain ⟨L, hL0, h1, h2, h3, h4, h5, h6⟩ := hR
  have he : ∀ i, e i ∈ Finset.univ.map e := fun i => Finset.mem_map_of_mem e (Finset.mem_univ i)
  have h6' : ∀ B : Finset (Fin V), ∃ C : Finset G.Fn, B.Nonempty →
      ((↑C : Set G.Fn) ⊆ L (vertexLabel (B.map e)) ∧
        (C.card : ℝ) ≤ (∏ v ∈ B.map e, κ v) * (G.dna : ℝ) ∧
        ∀ x ∈ L (vertexLabel (B.map e)), (p : G.O) ^ (Dd + 1) • x ∈
          (⨆ v ∈ B.map e, Submodule.span G.O
            (G.yv v '' (L (Function.update (vertexLabel (B.map e)) v Slot.ball) : Set G.Fn))) ⊔
            Submodule.span G.O (↑C : Set G.Fn)) := by
    intro B
    by_cases hB : B.Nonempty
    · obtain ⟨C, hC⟩ := h6 (B.map e) (Finset.map_subset_map.2 (Finset.subset_univ _)) (hB.map)
      exact ⟨C, fun _ => hC⟩
    · exact ⟨∅, fun h => absurd h hB⟩
  choose C hC using h6'
  have W := (Top.walkSharp V G.P.w (fun σ => L (extS e σ)) (fun i => y (e i)) m β (2 * (Dd + 1)) (2 * S)
    (fun i => t (e i)) (fun i => t (e i)) (fun i => 2 * t (e i)) (fun i => 2 * Sv (e i))
    (fun B => (C B).card) C hm
    (fun i j => by
      apply LinearMap.ext
      intro F
      simp only [Module.End.mul_apply, hy]
      exact hcomm _ _ _)
    (fun σ i => by simp only [extS_update]; exact h1 _ _ (he i))
    (fun σ i => by simp only [extS_update]; exact h2 _ _ (he i))
    (fun σ i => by simp only [extS_update]; exact h3 _ _ (he i))
    (fun σ i => by simp only [extS_update]; exact h4 _ _ (he i))
    (fun σ i => by
      simp only [extS_update]
      intro x hx
      rw [two_mul, pow_add, mul_smul]
      exact h4 _ _ (he i) _ (h3 _ _ (he i) _ hx))
    (fun σ i => by
      simp only [extS_update, hy]
      exact h5 _ _ (he i))
    (fun B hB => by
      have hBn : B.Nonempty := by
        rw [← Finset.card_pos]; omega
      obtain ⟨c1, c2, c3⟩ := hC B hBn
      simp only [extS_update, extS_positionAt]
      refine ⟨c1, le_rfl, fun x hx => ?_⟩
      rw [pow_mul, hw]
      refine SetLike.le_def.1 (sup_le_sup_right ?_ _) (c3 x hx)
      refine iSup₂_le fun v hv => ?_
      obtain ⟨i, hi, rfl⟩ := Finset.mem_map.1 hv
      rw [Submodule.span_le]
      rintro _ ⟨z, hz, rfl⟩
      refine Submodule.mem_iSup_of_mem i (Submodule.mem_iSup_of_mem hi ⟨z, hz, hy _ _⟩))
    (fun i => Nat.mul_le_mul_left 2 (hS _ (he i)))).1
  simp only [extS_base, hL0] at W
  obtain ⟨Cc, hCM, hcard, hx⟩ := W
  refine ⟨Cc, hCM, Nat.le_floor ?_, fun x hxM => ?_⟩
  · calc (Cc.card : ℝ)
        ≤ ((∑ B ∈ (Finset.univ : Finset (Fin V)).powersetCard (β + 1),
            m ^ (β + 1) * (C B).card : ℕ) : ℝ) := by exact_mod_cast hcard
      _ ≤ ∑ B ∈ (Finset.univ : Finset (Fin V)).powersetCard (β + 1),
            (m : ℝ) ^ (β + 1) * ((∏ v ∈ B.map e, κ v) * (G.dna : ℝ)) := by
          push_cast
          apply Finset.sum_le_sum
          intro B hB
          have hBn : B.Nonempty := by
            rw [← Finset.card_pos, (Finset.mem_powersetCard.1 hB).2]; omega
          exact mul_le_mul_of_nonneg_left (hC B hBn).2.1 (by positivity)
      _ = (G.dna : ℝ) * (m : ℝ) ^ (β + 1) * esymmOn (Finset.univ.map e) κ (β + 1) := by
          unfold esymmOn
          rw [Finset.powersetCard_map, Finset.sum_map, Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro B _
          show _ = _ * _ * ∏ v ∈ B.map e, κ v
          ring
  · have hexp : ∑ i, (t (e i) + t (e i) + (m - 1) * (2 * t (e i)) + m * (2 * (Dd + 1))) + β * (2 * S) =
        2 * (tau (Finset.univ.map e) m Dd t + β * S) := by
      unfold tau
      rw [Finset.sum_map]
      obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
      simp only [Nat.add_sub_cancel]
      have hs : ∑ i, (t (e i) + t (e i) + k * (2 * t (e i)) + (k + 1) * (2 * (Dd + 1))) =
          2 * ∑ i, (k + 1) * (t (e i) + Dd + 1) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _
        ring
      rw [hs]
      ring
    have h7 := hx x hxM
    rw [hexp, pow_mul, hw] at h7
    exact SetLike.le_def.1 (sup_le_sup_right (pr_le G y hy e hcomm m Sv G.P.w 2 hw G.Mna) _) h7

/- English proof (translation)
Establish `hVV : Finset.univ.map (VV.orderEmbOfFin rfl).toEmbedding = VV` using `Finset.map_orderEmbOfFin_univ VV rfl`. Use `walk_allBut_bound G y hy hcomm (VV.orderEmbOfFin rfl).toEmbedding t Sv Dd S m κ hw hm (by rw [hVV]; exact hS) (by rw [hVV]; exact hR) β` as an intermediate fact. Rewrite `this` using `[hVV]`. Conclude with `this`.
-/
theorem walk_clause (G : GAtP p) (y : Fin G.P.nV → Module.End G.O G.Fn) (hy : ∀ v F, y v F = G.yv v F)
    (hcomm : ∀ (u v : Fin G.P.nV) (F : G.Fn), G.yv u (G.yv v F) = G.yv v (G.yv u F))
    (VV : Finset (Fin G.P.nV)) (t Sv : Fin G.P.nV → ℕ) (Dd S m : ℕ) (κ : Fin G.P.nV → ℝ)
    (hw : G.P.w ^ 2 = (p : G.O)) (hm : 1 ≤ m) (hS : ∀ v ∈ VV, Sv v ≤ S)
    (hR : RestWalk G VV t Dd κ) (β : ℕ) :
    AllButLE (p : G.O) G.Mna (prodIdeal G VV m Sv G.Mna)
      ⌊(G.dna : ℝ) * (m : ℝ) ^ (β + 1) * esymmOn VV κ (β + 1)⌋₊ (tau VV m Dd t + β * S) := by
  have hVV : Finset.univ.map (VV.orderEmbOfFin rfl).toEmbedding = VV := Finset.map_orderEmbOfFin_univ VV rfl
  have := walk_allBut_bound G y hy hcomm (VV.orderEmbOfFin rfl).toEmbedding t Sv Dd S m κ hw hm
    (by rw [hVV]; exact hS) (by rw [hVV]; exact hR) β
  rw [hVV] at this
  exact this

end Formalism.MainNotions.G.LatticeSystems

namespace Formalism.MainNotions.G.LatticeSystems

open Formalism.MainNotions.G

/- English proof (translation)
Take `⟨u, M, hu⟩` from `h`. Use `⟨fun j => ∑ i, algebraMap O Kf (M j i) • y i, ?_⟩` and prove the remaining obligations. Rewrite using `[Fintype.linearIndependent_iff]`. Introduce `c hc k`. Establish `h1` using `congrArg (fun z => ((u (Pi.single k 1) : A) : Module.Dual Kf V) z) hc`.

Simplify using `only [map_sum, map_smul, smul_eq_mul, map_zero] at h1`. Establish `h2 : ∀ j, ∑ i, algebraMap O Kf (M j i) * ((u (Pi.single k 1) : A) : Module.Dual Kf V) (y i) = algebraMap O Kf (π ^ D * (Pi.single k 1 : Fin n → O) j)` using `fun j => hu _ j`. Simplify using `only [h2] at h1`. Establish `h3 : ∑ j, c j * algebraMap O Kf (π ^ D * (Pi.single k 1 : Fin n → O) j) = c k * algebraMap O Kf π ^ D`. Rewrite using `[Finset.sum_eq_single k]`.

Simplify using the standard rewrite rules. Introduce `j _ hj`. Simplify using `[Pi.single_eq_of_ne hj]`. Introduce `hk`. Conclude with `absurd (Finset.mem_univ k) hk`.

Rewrite `h1` using `[h3]`. Conclude with `(mul_eq_zero.mp h1).resolve_right (pow_ne_zero _ hπ)`.
-/
theorem kp_indep {O Kf V : Type*} [CommRing O] [Field Kf] [Algebra O Kf] [AddCommGroup V] [Module Kf V]
    (π : O) (hπ : algebraMap O Kf π ≠ 0) (A : Submodule O (Module.Dual Kf V)) {I : Type*} [Fintype I]
    (y : I → V) (n D : ℕ) (h : GoodRankK π A (fun i G => G (y i)) n D) :
    ∃ x : Fin n → V, LinearIndependent Kf x := by
  classical
  obtain ⟨u, M, hu⟩ := h
  refine ⟨fun j => ∑ i, algebraMap O Kf (M j i) • y i, ?_⟩
  rw [Fintype.linearIndependent_iff]
  intro c hc k
  have h1 := congrArg (fun z => ((u (Pi.single k 1) : A) : Module.Dual Kf V) z) hc
  simp only [map_sum, map_smul, smul_eq_mul, map_zero] at h1
  have h2 : ∀ j, ∑ i, algebraMap O Kf (M j i) * ((u (Pi.single k 1) : A) : Module.Dual Kf V) (y i) =
      algebraMap O Kf (π ^ D * (Pi.single k 1 : Fin n → O) j) := fun j => hu _ j
  simp only [h2] at h1
  have h3 : ∑ j, c j * algebraMap O Kf (π ^ D * (Pi.single k 1 : Fin n → O) j) =
      c k * algebraMap O Kf π ^ D := by
    rw [Finset.sum_eq_single k]
    · simp
    · intro j _ hj
      simp [Pi.single_eq_of_ne hj]
    · intro hk
      exact absurd (Finset.mem_univ k) hk
  rw [h3] at h1
  exact (mul_eq_zero.mp h1).resolve_right (pow_ne_zero _ hπ)

/- English proof (translation)
Establish `hS` using `G.P.setting v`. Establish `h1 : (p : G.P.W v) ≠ 0` using `hS.p_unif.ne_zero`. Establish `hfr` using `hS.frac_alt`. Establish `h2 : algebraMap (G.P.W v) (G.P.Qq v) (p : G.P.W v) ≠ 0`. Introduce `h0`.

Conclude with `h1 ((IsFractionRing.injective (G.P.W v) (G.P.Qq v)) (by rw [h0, map_zero]))`. Establish `h3` using `hS.ι_comp (p : G.P.W v)`. Rewrite `h3` using `[map_natCast (G.P.j v)]`. Rewrite using `[← h3]`. Conclude with `(map_ne_zero (G.P.ι v)).mpr h2`.
-/
theorem kp_p_ne_zero {p : ℕ} (G : GAtP p) (v : Fin G.P.nV) : algebraMap G.O G.Kf (p : G.O) ≠ 0 := by
  have hS := G.P.setting v
  have h1 : (p : G.P.W v) ≠ 0 := hS.p_unif.ne_zero
  have hfr := hS.frac_alt
  have h2 : algebraMap (G.P.W v) (G.P.Qq v) (p : G.P.W v) ≠ 0 := by
    intro h0
    exact h1 ((IsFractionRing.injective (G.P.W v) (G.P.Qq v)) (by rw [h0, map_zero]))
  have h3 := hS.ι_comp (p : G.P.W v)
  rw [map_natCast (G.P.j v)] at h3
  rw [← h3]
  exact (map_ne_zero (G.P.ι v)).mpr h2

/- English proof (translation)
Establish `hp` using `kp_p_ne_zero G v`. Take `⟨-, hL⟩` from `h`. Take `⟨M, e, F, -, -, -, n, hn, hG⟩` from `hL (colSpan (G.P.W v) 1) ⟨1, by simp, rfl⟩`. Distinguish the cases in `hd : dimV G.Kf (G.P.lam0 v) = 0`. Conclude with `Or.inr hd`.

Use `left`. Establish `hfin : Module.Finite G.Kf (Vsp G.Kf (G.P.lam0 v))`. Assume the negation of the conclusion as `hnf`. Conclude with `hd (Module.finrank_of_not_finite hnf)`. Take `⟨x, hx⟩` from `kp_indep (p : G.O) hp _ (fun i => ((p : G.Kf) ^ Ar G.P.r (G.P.lam0 v)) • F i) n Dd hG`.

Establish `hle : n ≤ dimV G.Kf (G.P.lam0 v)`. Establish `h0` using `hx.fintype_card_le_finrank`. Rewrite `h0` using `[Fintype.card_fin]`. Conclude with `h0`. Establish `hpos : (0 : ℝ) < (dimV G.Kf (G.P.lam0 v) : ℝ)` using `by exact_mod_cast Nat.pos_of_ne_zero hd`.

Establish `hle' : (n : ℝ) ≤ (dimV G.Kf (G.P.lam0 v) : ℝ)` using `by exact_mod_cast hle`. Use the polynomial consequences of the given equalities and inequalities.
-/
theorem kappa_nonneg {p : ℕ} (G : GAtP p) (v : Fin G.P.nV) (t Dd cStar : ℕ) (κ : ℝ)
    (h : LPprime (W := G.P.W v) (Qq := G.P.Qq v) (O := G.O) (Kf := G.Kf) p (G.P.n' v) (G.P.ι v) (G.P.σ v)
      G.P.w G.P.r (G.P.lam0 v) t Dd κ cStar) :
    0 ≤ κ ∨ dimV G.Kf (G.P.lam0 v) = 0 := by
  have hp := kp_p_ne_zero G v
  obtain ⟨-, hL⟩ := h
  obtain ⟨M, e, F, -, -, -, n, hn, hG⟩ := hL (colSpan (G.P.W v) 1) ⟨1, by simp, rfl⟩
  by_cases hd : dimV G.Kf (G.P.lam0 v) = 0
  · exact Or.inr hd
  left
  have hfin : Module.Finite G.Kf (Vsp G.Kf (G.P.lam0 v)) := by
    by_contra hnf
    exact hd (Module.finrank_of_not_finite hnf)
  obtain ⟨x, hx⟩ := kp_indep (p : G.O) hp _
    (fun i => ((p : G.Kf) ^ Ar G.P.r (G.P.lam0 v)) • F i) n Dd hG
  have hle : n ≤ dimV G.Kf (G.P.lam0 v) := by
    have h0 := hx.fintype_card_le_finrank
    rw [Fintype.card_fin] at h0
    exact h0
  have hpos : (0 : ℝ) < (dimV G.Kf (G.P.lam0 v) : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hd
  have hle' : (n : ℝ) ≤ (dimV G.Kf (G.P.lam0 v) : ℝ) := by exact_mod_cast hle
  nlinarith

/- English proof (translation)
Use `⟨Finsupp.equivFunOnFinite.symm (fun x : Fin k × Fin k => if x.1 = x.2 then ν x.2 else 0), ?_, ?_⟩` and prove the remaining obligations. Introduce `l j hj a`. Simplify using `only [Finsupp.equivFunOnFinite_symm_apply_apply, zero_add, Finset.sum_ite_eq', Finset.mem_filter, Finset.mem_univ, true_and]`. Distinguish the cases in `h : j ≤ a`. Establish `hl : l < a`.

Rewrite using `[Fin.lt_def]`. Use `Fin.le_def.mp h` as an intermediate fact. Use linear arithmetic over natural numbers and integers. Establish `hlj : l ≤ j`. Rewrite using `[Fin.le_def]`.

Use linear arithmetic over natural numbers and integers. Simplify using `only [h, hl, if_true]`. Conclude with `hν hlj`. Simplify using `[h]`. Introduce `t`.

Simplify using the standard rewrite rules.
-/
theorem kp_ssIdx_nonempty (k : ℕ) (ν : Fin k → ℕ) (hν : Antitone ν) : (Formalism.GradedWeylDivisibility.ssIdx k k ν).Nonempty := by
  classical
  refine ⟨Finsupp.equivFunOnFinite.symm (fun x : Fin k × Fin k => if x.1 = x.2 then ν x.2 else 0), ?_, ?_⟩
  · intro l j hj a
    simp only [Finsupp.equivFunOnFinite_symm_apply_apply, zero_add, Finset.sum_ite_eq', Finset.mem_filter,
      Finset.mem_univ, true_and]
    by_cases h : j ≤ a
    · have hl : l < a := by
        rw [Fin.lt_def]
        have := Fin.le_def.mp h
        omega
      have hlj : l ≤ j := by
        rw [Fin.le_def]
        omega
      simp only [h, hl, if_true]
      exact hν hlj
    · simp [h]
  · intro t
    simp

/- English proof (translation)
Unfold `lamAt`. Use `split_ifs with h`. Conclude with `hdom s`. Introduce `i j hij`. Establish `: lam0 s i.rev ≤ lam0 s j.rev` using `hdom s (Fin.rev_le_rev.mpr hij)`.

Simplify using `using this`.
-/
theorem kp_lamAt_antitone {n' m : ℕ} (lam0 : Fin n' → Fin (m + 1) → ℤ) (hdom : IsDominant lam0) (s : Fin n') :
    Antitone (lamAt lam0 s) := by
  unfold lamAt
  split_ifs with h
  · exact hdom s
  · intro i j hij
    have : lam0 s i.rev ≤ lam0 s j.rev := hdom s (Fin.rev_le_rev.mpr hij)
    simpa using this

/- English proof (translation)
Introduce `i j hij`. Unfold `nuOf`. Conclude with `Int.toNat_le_toNat (by have := h hij; omega)`.
-/
theorem kp_nuOf_antitone {m : ℕ} (lam : Fin (m + 1) → ℤ) (h : Antitone lam) : Antitone (nuOf lam) := by
  intro i j hij
  unfold nuOf
  exact Int.toNat_le_toNat (by have := h hij; omega)

/- English proof (translation)
Establish `hV : Vsp Kf lam0 = Formalism.GradedWeylDivisibility.tensorLat Kf Kf (fun s => Formalism.GradedWeylDivisibility.dualWeyl Kf (m + 1) (m + 1) (nuOf (lamAt lam0 s)))`. Unfold `Vsp`. Use `congr 1`. Use function extensionality and compare the values at `s`. Rewrite using `[if_pos (kp_lamAt_antitone lam0 hdom s)]`.

Establish `hb` using `fun s : Fin n' => Formalism.GradedWeylDivisibility.sSBasis Kf (m + 1) (m + 1) (nuOf (lamAt lam0 s))`. Use `choose b hb1 _ using hb`. Establish `: IsFractionRing Kf Kf` using `IsLocalization.of_le_isUnit (fun x hx => IsUnit.mk0 x (nonZeroDivisors.ne_zero hx))`. Take `⟨hli, hsp⟩` from `Formalism.GradedWeylDivisibility.tensorBasis Kf Kf (Fin n') (m + 1) (m + 1) (fun s => ↥(Formalism.GradedWeylDivisibility.ssIdx (m + 1) (m + 1) (nuOf (lamAt lam0 s)))) (fun s => Formalism.GradedWeylDivisibility.dualWeyl Kf (m + 1) (m + 1) (nuOf (lamAt lam0 s))) b (fun s => (hb1 s) …`. Establish `: ∀ s : Fin n', Fintype ↥(Formalism.GradedWeylDivisibility.ssIdx (m + 1) (m + 1) (nuOf (lamAt lam0 s)))` using `fun s => (Formalism.GradedWeylDivisibility.sSIdxFinite (m + 1) (m + 1) (nuOf (lamAt lam0 s))).fintype`.

Establish `: ∀ s : Fin n', Nonempty ↥(Formalism.GradedWeylDivisibility.ssIdx (m + 1) (m + 1) (nuOf (lamAt lam0 s)))` using `fun s => (kp_ssIdx_nonempty (m + 1) _ (kp_nuOf_antitone _ (kp_lamAt_antitone lam0 hdom s))).to_subtype`. Unfold `dimV`. Rewrite using `[hV, ← hsp, finrank_span_eq_card hli]`. Conclude with `Fintype.card_pos`.
-/
theorem kp_dimV_pos (Kf : Type) [Field Kf] {n' m : ℕ} (lam0 : Fin n' → Fin (m + 1) → ℤ)
    (hdom : IsDominant lam0) : 0 < dimV Kf lam0 := by
  classical
  have hV : Vsp Kf lam0 = Formalism.GradedWeylDivisibility.tensorLat Kf Kf
      (fun s => Formalism.GradedWeylDivisibility.dualWeyl Kf (m + 1) (m + 1) (nuOf (lamAt lam0 s))) := by
    unfold Vsp
    congr 1
    funext s
    rw [if_pos (kp_lamAt_antitone lam0 hdom s)]
  have hb := fun s : Fin n' => Formalism.GradedWeylDivisibility.sSBasis Kf (m + 1) (m + 1) (nuOf (lamAt lam0 s))
  choose b hb1 _ using hb
  have : IsFractionRing Kf Kf :=
    IsLocalization.of_le_isUnit (fun x hx => IsUnit.mk0 x (nonZeroDivisors.ne_zero hx))
  obtain ⟨hli, hsp⟩ := Formalism.GradedWeylDivisibility.tensorBasis Kf Kf (Fin n') (m + 1) (m + 1)
    (fun s => ↥(Formalism.GradedWeylDivisibility.ssIdx (m + 1) (m + 1) (nuOf (lamAt lam0 s))))
    (fun s => Formalism.GradedWeylDivisibility.dualWeyl Kf (m + 1) (m + 1) (nuOf (lamAt lam0 s))) b
    (fun s => (hb1 s).1) (fun s => (hb1 s).2.1)
  have : ∀ s : Fin n', Fintype ↥(Formalism.GradedWeylDivisibility.ssIdx (m + 1) (m + 1) (nuOf (lamAt lam0 s))) :=
    fun s => (Formalism.GradedWeylDivisibility.sSIdxFinite (m + 1) (m + 1) (nuOf (lamAt lam0 s))).fintype
  have : ∀ s : Fin n', Nonempty ↥(Formalism.GradedWeylDivisibility.ssIdx (m + 1) (m + 1) (nuOf (lamAt lam0 s))) :=
    fun s => (kp_ssIdx_nonempty (m + 1) _ (kp_nuOf_antitone _ (kp_lamAt_antitone lam0 hdom s))).to_subtype
  unfold dimV
  rw [hV, ← hsp, finrank_span_eq_card hli]
  exact Fintype.card_pos

/- English proof (translation)
The claim follows from `(kappa_nonneg G v t Dd cStar κ h).resolve_right (kp_dimV_pos G.Kf (G.P.lam0 v) (G.P.dom v)).ne'`.
-/
theorem kappa_nonneg' {p : ℕ} (G : GAtP p) (v : Fin G.P.nV) (t Dd cStar : ℕ) (κ : ℝ)
    (h : LPprime (W := G.P.W v) (Qq := G.P.Qq v) (O := G.O) (Kf := G.Kf) p (G.P.n' v) (G.P.ι v) (G.P.σ v)
      G.P.w G.P.r (G.P.lam0 v) t Dd κ cStar) : 0 ≤ κ :=
  (kappa_nonneg G v t Dd cStar κ h).resolve_right (kp_dimV_pos G.Kf (G.P.lam0 v) (G.P.dom v)).ne'

end Formalism.MainNotions.G.LatticeSystems

namespace Formalism.MainNotions.G.LatticeSystems

open Formalism.MainNotions.G Formalism.MainNotions.SelectionLemmas

/- English proof (translation)
Distinguish the cases in `hL : IsLattice W L`. Take `⟨g, -, hg⟩` from `hL`. Establish `hfg : L.FG`. Rewrite using `[hg]`. Conclude with `Submodule.fg_span (Set.finite_range _)`.

Establish `: Module.Finite W L` using `Module.Finite.iff_fg.mpr hfg`. Use `set I : Ideal W := Ideal.span {(p : W)} with hI`. Establish `: Module.Finite (W ⧸ I) (↥L ⧸ I • (⊤ : Submodule W L))` using `Module.Finite.of_restrictScalars_finite W _ _`. Establish `: Finite (↥L ⧸ I • (⊤ : Submodule W L))` using `Module.finite_of_finite (W ⧸ I)`. Set `f : Submodule W (Fin k → Qq) → Set (↥L ⧸ I • (⊤ : Submodule W L))` to `fun A => ((A.comap L.subtype).map (I • (⊤ : Submodule W L)).mkQ : Set _)`.

Use `Set.Finite.of_finite_image (f := f) (Set.toFinite _) ?_` and prove the remaining obligations. Establish `key : ∀ A : Submodule W (Fin k → Qq), IsEdge p n' r ⟨A, L⟩ → I • (⊤ : Submodule W L) ≤ A.comap L.subtype`. Introduce `A hA`. Rewrite using `[Submodule.smul_le]`. Introduce `a ha x _`.

Take `⟨c, rfl⟩` from `Ideal.mem_span_singleton'.mp ha`. Rewrite using `[mul_smul]`. Apply `Submodule.smul_mem` to reduce the goal to its premises. Use `show (p : W) • (x : Fin k → Qq) ∈ A`. Conclude with `hA.2.2.2.1 x x.2`.

Introduce `A hA B hB hAB`. Establish `h1 : (A.comap L.subtype).map (I • (⊤ : Submodule W L)).mkQ = (B.comap L.subtype).map (I • (⊤ : Submodule W L)).mkQ` using `SetLike.coe_injective hAB`. Establish `h2` using `congrArg (Submodule.comap (I • (⊤ : Submodule W L)).mkQ) h1`. Rewrite `h2` using `[Submodule.comap_map_mkQ, Submodule.comap_map_mkQ, sup_eq_right.mpr (key A hA), sup_eq_right.mpr (key B hB)]`. Establish `h3` using `congrArg (Submodule.map L.subtype) h2`.

Rewrite `h3` using `[Submodule.map_comap_subtype, Submodule.map_comap_subtype, inf_eq_right.mpr hA.2.2.1, inf_eq_right.mpr hB.2.2.1]`. Conclude with `h3`. Use `Set.finite_empty` and compare the differences between its conclusion and the goal. Use extensionality with `A`. Simplify using `only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]`.

Conclude with `fun h => hL h.2.1`.
-/
theorem ef_edges_finite_gen {W Qq : Type} [CommRing W] [Field Qq] [Algebra W Qq] (p n' r k : ℕ)
    (hfin : Finite (W ⧸ Ideal.span {(p : W)})) (L : Submodule W (Fin k → Qq)) :
    {L'' : Submodule W (Fin k → Qq) | IsEdge p n' r ⟨L'', L⟩}.Finite := by
  classical
  by_cases hL : IsLattice W L
  · obtain ⟨g, -, hg⟩ := hL
    have hfg : L.FG := by
      rw [hg]; exact Submodule.fg_span (Set.finite_range _)
    have : Module.Finite W L := Module.Finite.iff_fg.mpr hfg
    set I : Ideal W := Ideal.span {(p : W)} with hI
    have : Module.Finite (W ⧸ I) (↥L ⧸ I • (⊤ : Submodule W L)) :=
      Module.Finite.of_restrictScalars_finite W _ _
    have : Finite (↥L ⧸ I • (⊤ : Submodule W L)) := Module.finite_of_finite (W ⧸ I)
    let f : Submodule W (Fin k → Qq) → Set (↥L ⧸ I • (⊤ : Submodule W L)) :=
      fun A => ((A.comap L.subtype).map (I • (⊤ : Submodule W L)).mkQ : Set _)
    refine Set.Finite.of_finite_image (f := f) (Set.toFinite _) ?_
    have key : ∀ A : Submodule W (Fin k → Qq), IsEdge p n' r ⟨A, L⟩ →
        I • (⊤ : Submodule W L) ≤ A.comap L.subtype := by
      intro A hA
      rw [Submodule.smul_le]
      intro a ha x _
      obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.mp ha
      rw [mul_smul]
      apply Submodule.smul_mem
      show (p : W) • (x : Fin k → Qq) ∈ A
      exact hA.2.2.2.1 x x.2
    intro A hA B hB hAB
    have h1 : (A.comap L.subtype).map (I • (⊤ : Submodule W L)).mkQ =
        (B.comap L.subtype).map (I • (⊤ : Submodule W L)).mkQ := SetLike.coe_injective hAB
    have h2 := congrArg (Submodule.comap (I • (⊤ : Submodule W L)).mkQ) h1
    rw [Submodule.comap_map_mkQ, Submodule.comap_map_mkQ, sup_eq_right.mpr (key A hA),
      sup_eq_right.mpr (key B hB)] at h2
    have h3 := congrArg (Submodule.map L.subtype) h2
    rw [Submodule.map_comap_subtype, Submodule.map_comap_subtype, inf_eq_right.mpr hA.2.2.1,
      inf_eq_right.mpr hB.2.2.1] at h3
    exact h3
  · convert Set.finite_empty
    ext A
    simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
    exact fun h => hL h.2.1

section PlacesLevel

variable {p : ℕ} {O Kf : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field Kf] [Algebra O Kf]
  (P : Places p O Kf)

/- English proof (translation)
Apply `ef_edges_finite_gen` to reduce the goal to its premises. Apply `Nat.finite_of_card_ne_zero` to reduce the goal to its premises. Rewrite using `[(P.setting v).res_card]`. Conclude with `pow_ne_zero _ (P.setting v).prime.ne_zero`.
-/
theorem ef_places_finite (v : Fin P.nV) (L : Submodule (P.W v) (Fin (P.m + 1) → P.Qq v)) :
    {L'' : Submodule (P.W v) (Fin (P.m + 1) → P.Qq v) | IsEdge p (P.n' v) P.r ⟨L'', L⟩}.Finite := by
  apply ef_edges_finite_gen
  apply Nat.finite_of_card_ne_zero
  rw [(P.setting v).res_card]
  exact pow_ne_zero _ (P.setting v).prime.ne_zero

def ef_E (v : Fin P.nV) (L : Submodule (P.W v) (Fin (P.m + 1) → P.Qq v)) :
    Finset (Submodule (P.W v) (Fin (P.m + 1) → P.Qq v)) :=
  (ef_places_finite P v L).toFinset

/- English proof (translation)
Unfold `Level.yv`. Use `congr 1`. Conclude with `finsum_mem_eq_finite_toFinset_sum _ (ef_places_finite P v (L v))`.
-/
theorem ef_yv_eq (v : Fin P.nV) (F : P.Tup → P.Xsp) (L : P.Tup) :
    Level.yv (P := P) v F L =
      ((p : Kf) ^ P.ArV v) • ∑ L'' ∈ ef_E P v (L v), F (Function.update L v L'') := by
  unfold Level.yv
  congr 1
  exact finsum_mem_eq_finite_toFinset_sum _ (ef_places_finite P v (L v))

/- English proof (translation)
Use function extensionality and compare the values at `L`. Rewrite using `[Pi.add_apply, ef_yv_eq, ef_yv_eq, ef_yv_eq, ← smul_add, ← Finset.sum_add_distrib]`. Both sides reduce to the same expression.
-/
theorem ef_yv_add (v : Fin P.nV) (F F' : P.Tup → P.Xsp) :
    Level.yv (P := P) v (F + F') = Level.yv (P := P) v F + Level.yv (P := P) v F' := by
  funext L
  rw [Pi.add_apply, ef_yv_eq, ef_yv_eq, ef_yv_eq, ← smul_add, ← Finset.sum_add_distrib]
  rfl

/- English proof (translation)
Use function extensionality and compare the values at `L`. Rewrite using `[Pi.smul_apply, ef_yv_eq, ef_yv_eq, smul_comm c]`. Use `congr 1`. Rewrite using `[Finset.smul_sum]`. Both sides reduce to the same expression.
-/
theorem ef_yv_smul (v : Fin P.nV) (c : O) (F : P.Tup → P.Xsp) :
    Level.yv (P := P) v (c • F) = c • Level.yv (P := P) v F := by
  funext L
  rw [Pi.smul_apply, ef_yv_eq, ef_yv_eq, smul_comm c]
  congr 1
  rw [Finset.smul_sum]
  rfl

/- English proof (translation)
Distinguish the cases in `huv : u = v`. Substitute `huv` using the available equality. Both sides reduce to the same expression. Use function extensionality and compare the values at `L`. Establish `h1 : ∀ (a b : Fin P.nV), a ≠ b → Level.yv (P` using `P) a (Level.yv (P := P) b F) L = ((p : Kf) ^ P.ArV a) • ((p : Kf) ^ P.ArV b) • ∑ x ∈ ef_E P a (L a), ∑ y ∈ ef_E P b (L b), F (Function.update (Function.update L a x) b y) := by`.

Introduce `a b hab`. Rewrite using `[ef_yv_eq]`. Use `congr 1`. Rewrite using `[Finset.smul_sum]`. Apply `Finset.sum_congr rfl` to reduce the goal to its premises.

Introduce `x _`. Establish `e : Function.update (β` using `fun v => Submodule (P.W v) (Fin (P.m + 1) → P.Qq v)) L a x b = L b := Function.update_of_ne (Ne.symm hab) x L`. Establish `h` using `ef_yv_eq P b F (Function.update (β := fun v => Submodule (P.W v) (Fin (P.m + 1) → P.Qq v)) L a x)`. Rewrite `h` using `[e]`. Conclude with `h`.

Rewrite using `[h1 u v huv, h1 v u (Ne.symm huv), smul_comm, Finset.sum_comm]`. Use `congr 2`. Apply `Finset.sum_congr rfl` to reduce the goal to its premises. Introduce `y _`. Apply `Finset.sum_congr rfl` to reduce the goal to its premises.

Introduce `x _`. Conclude with `congrArg F (Function.update_comm huv x y L)`.
-/
theorem ef_yv_comm (u v : Fin P.nV) (F : P.Tup → P.Xsp) :
    Level.yv (P := P) u (Level.yv (P := P) v F) = Level.yv (P := P) v (Level.yv (P := P) u F) := by
  by_cases huv : u = v
  · subst huv; rfl
  funext L
  have h1 : ∀ (a b : Fin P.nV), a ≠ b → Level.yv (P := P) a (Level.yv (P := P) b F) L =
      ((p : Kf) ^ P.ArV a) • ((p : Kf) ^ P.ArV b) • ∑ x ∈ ef_E P a (L a), ∑ y ∈ ef_E P b (L b),
        F (Function.update (Function.update L a x) b y) := by
    intro a b hab
    rw [ef_yv_eq]
    congr 1
    rw [Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro x _
    have e : Function.update (β := fun v => Submodule (P.W v) (Fin (P.m + 1) → P.Qq v)) L a x b = L b :=
      Function.update_of_ne (Ne.symm hab) x L
    have h := ef_yv_eq P b F
      (Function.update (β := fun v => Submodule (P.W v) (Fin (P.m + 1) → P.Qq v)) L a x)
    rw [e] at h
    exact h
  rw [h1 u v huv, h1 v u (Ne.symm huv), smul_comm, Finset.sum_comm]
  congr 2
  apply Finset.sum_congr rfl
  intro y _
  apply Finset.sum_congr rfl
  intro x _
  exact congrArg F (Function.update_comm huv x y L)

end PlacesLevel

variable {p : ℕ}

/- English proof (translation)
The claim follows from `ef_places_finite G.P v L`.
-/
theorem edges_finite (G : GAtP p) (v : Fin G.P.nV) (L : Submodule (G.P.W v) (Fin (G.P.m + 1) → G.P.Qq v)) :
    {L'' : Submodule (G.P.W v) (Fin (G.P.m + 1) → G.P.Qq v) | IsEdge p (G.P.n' v) G.P.r ⟨L'', L⟩}.Finite :=
  ef_places_finite G.P v L

def yEnd (G : GAtP p) (v : Fin G.P.nV) : Module.End G.O G.Fn where
  toFun := G.yv v
  map_add' F F' := by
    funext i
    exact ef_yv_add G.P v (F i) (F' i)
  map_smul' c F := by
    funext i
    exact ef_yv_smul G.P v c (F i)

/- English proof (translation)
Both sides reduce to the same expression.
-/
@[simp] theorem yEnd_apply (G : GAtP p) (v : Fin G.P.nV) (F : G.Fn) : yEnd G v F = G.yv v F := rfl

/- English proof (translation)
Rewrite using `[Module.End.pow_apply]`. Both sides reduce to the same expression.
-/
theorem yEnd_pow_apply (G : GAtP p) (v : Fin G.P.nV) (m : ℕ) (F : G.Fn) :
    (yEnd G v ^ m) F = (G.yv v)^[m] F := by
  rw [Module.End.pow_apply]
  rfl

/- English proof (translation)
Introduce `u v F` and use `funext fun i => ef_yv_comm G.P u v (F i)`.
-/
theorem exponent_condition_holds (D : Formalism.BasicNotions.D7) (G : GAtP p) : Formalism.MainNotions.SelectionLemmas.adm3 D G :=
  fun u v F => funext fun i => ef_yv_comm G.P u v (F i)

/- English proof (translation)
Apply `LinearMap.ext` to reduce the goal to its premises. Introduce `F`. Conclude with `funext fun i => ef_yv_comm G.P u v (F i)`.
-/
theorem yEnd_commute (G : GAtP p) (u v : Fin G.P.nV) : Commute (yEnd G u) (yEnd G v) := by
  apply LinearMap.ext
  intro F
  exact funext fun i => ef_yv_comm G.P u v (F i)

end Formalism.MainNotions.G.LatticeSystems

namespace Formalism.MainNotions.G.LatticeSystems

open Formalism.G0

/- English proof (translation)
Proceed by induction on `n with`. Consider the case `zero`. Rewrite using `[pow_zero, Ideal.span_singleton_one]`. Establish `: Subsingleton (R ⧸ (⊤ : Ideal R))` using `Submodule.Quotient.subsingleton_iff.mpr rfl`. Simplify using the standard rewrite rules.

Consider the case `succ n ih`. Establish `hUV : Ideal.span {ϖ ^ (n + 1)} ≤ Ideal.span {ϖ ^ n}`. Rewrite using `[Ideal.span_singleton_le_span_singleton]`. Conclude with `pow_dvd_pow _ (Nat.le_succ n)`. Rewrite using `[LengthLayersP.length_quot_eq_add (O := R) (X := R) hUV, ih]`.

Establish `hmap : Submodule.map (Submodule.mkQ (Ideal.span {ϖ ^ (n + 1)})) (Ideal.span {ϖ ^ n}) = Submodule.span R {Submodule.mkQ (Ideal.span {ϖ ^ (n + 1)}) (ϖ ^ n)}` using `by show Submodule.map _ (Submodule.span R {ϖ ^ n}) = _`. Rewrite using `[Submodule.map_span, Set.image_singleton]`. Rewrite using `[hmap]`. Use `set x := Submodule.mkQ (Ideal.span {ϖ ^ (n + 1)}) (ϖ ^ n) with hx`. Establish `hkill : ϖ ^ 1 • x = 0`.

Rewrite using `[hx, ← map_smul, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero, smul_eq_mul, pow_one, ← pow_succ']`. Conclude with `Ideal.mem_span_singleton_self _`. Establish `hle : Module.length R ↥(Submodule.span R {x}) ≤ ((1 : ℕ) : ℕ∞)` using `LengthLayersP.length_span_singleton_le ϖ hϖ 1 x hkill`. Establish `hx0 : x ≠ 0`. Rewrite using `[hx, Submodule.mkQ_apply, Ne, Submodule.Quotient.mk_eq_zero, Ideal.mem_span_singleton, pow_dvd_pow_iff hϖ.ne_zero hϖ.not_isUnit]`.

Use linear arithmetic over natural numbers and integers. Establish `hne : Module.length R ↥(Submodule.span R {x}) ≠ 0`. Rewrite using `[Ne, Module.length_eq_zero_iff, not_subsingleton_iff_nontrivial, Submodule.nontrivial_iff_ne_bot, Ne, Submodule.span_singleton_eq_bot]`. Conclude with `hx0`. Establish `h1 : Module.length R ↥(Submodule.span R {x}) = 1`.

Apply `le_antisymm (by simpa using hle)` to reduce the goal to its premises. Conclude with `Order.one_le_iff_ne_zero.mpr hne`. Rewrite using `[h1]`. Use `push_cast`. Rewrite using `[add_comm]`.
-/
theorem ln_length_pow {R : Type} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] (ϖ : R)
    (hϖ : Irreducible ϖ) (n : ℕ) : Module.length R (R ⧸ Ideal.span {ϖ ^ n}) = n := by
  induction n with
  | zero =>
    rw [pow_zero, Ideal.span_singleton_one]
    have : Subsingleton (R ⧸ (⊤ : Ideal R)) := Submodule.Quotient.subsingleton_iff.mpr rfl
    simp
  | succ n ih =>
    have hUV : Ideal.span {ϖ ^ (n + 1)} ≤ Ideal.span {ϖ ^ n} := by
      rw [Ideal.span_singleton_le_span_singleton]
      exact pow_dvd_pow _ (Nat.le_succ n)
    rw [LengthLayersP.length_quot_eq_add (O := R) (X := R) hUV, ih]
    have hmap : Submodule.map (Submodule.mkQ (Ideal.span {ϖ ^ (n + 1)})) (Ideal.span {ϖ ^ n}) =
        Submodule.span R {Submodule.mkQ (Ideal.span {ϖ ^ (n + 1)}) (ϖ ^ n)} := by
      show Submodule.map _ (Submodule.span R {ϖ ^ n}) = _
      rw [Submodule.map_span, Set.image_singleton]
    rw [hmap]
    set x := Submodule.mkQ (Ideal.span {ϖ ^ (n + 1)}) (ϖ ^ n) with hx
    have hkill : ϖ ^ 1 • x = 0 := by
      rw [hx, ← map_smul, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero, smul_eq_mul, pow_one,
        ← pow_succ']
      exact Ideal.mem_span_singleton_self _
    have hle : Module.length R ↥(Submodule.span R {x}) ≤ ((1 : ℕ) : ℕ∞) :=
      LengthLayersP.length_span_singleton_le ϖ hϖ 1 x hkill
    have hx0 : x ≠ 0 := by
      rw [hx, Submodule.mkQ_apply, Ne, Submodule.Quotient.mk_eq_zero, Ideal.mem_span_singleton,
        pow_dvd_pow_iff hϖ.ne_zero hϖ.not_isUnit]
      omega
    have hne : Module.length R ↥(Submodule.span R {x}) ≠ 0 := by
      rw [Ne, Module.length_eq_zero_iff, not_subsingleton_iff_nontrivial,
        Submodule.nontrivial_iff_ne_bot, Ne, Submodule.span_singleton_eq_bot]
      exact hx0
    have h1 : Module.length R ↥(Submodule.span R {x}) = 1 := by
      apply le_antisymm (by simpa using hle)
      exact Order.one_le_iff_ne_zero.mpr hne
    rw [h1]
    push_cast
    rw [add_comm]

/- English proof (translation)
Establish `: ϖ ^ (e * k) • x = (((u⁻¹ : Rˣ) : R) ^ k) • (a ^ k • x)`. Rewrite using `[smul_smul, ha, mul_pow, ← mul_assoc, ← mul_pow, Units.inv_mul, one_pow, one_mul, pow_mul]`. Rewrite using `[this]`. Conclude with `P.smul_mem _ h`.
-/
theorem ln_conv {R X : Type} [CommRing R] [AddCommGroup X] [Module R X] (u : Rˣ) (ϖ a : R) (e : ℕ)
    (ha : a = ↑u * ϖ ^ e) (k : ℕ) (x : X) (P : Submodule R X) (h : a ^ k • x ∈ P) :
    ϖ ^ (e * k) • x ∈ P := by
  have : ϖ ^ (e * k) • x = (((u⁻¹ : Rˣ) : R) ^ k) • (a ^ k • x) := by
    rw [smul_smul, ha, mul_pow, ← mul_assoc, ← mul_pow, Units.inv_mul, one_pow, one_mul, pow_mul]
  rw [this]
  exact P.smul_mem _ h

/- English proof (translation)
Take `⟨ϖ, hϖ⟩` from `IsDiscreteValuationRing.exists_irreducible R`. Take `⟨e, u, hau⟩` from `IsDiscreteValuationRing.eq_unit_mul_pow_irreducible ha hϖ`. Establish `hlen : Module.length R (R ⧸ Ideal.span {a}) = e`. Rewrite using `[hau, Ideal.span_singleton_mul_left_unit u.isUnit]`. Conclude with `ln_length_pow ϖ hϖ e`.

Establish `hspan : Ideal.span {a ^ τ} = Ideal.span {ϖ ^ (e * τ)}`. Rewrite using `[hau, mul_pow, ← pow_mul, ← Units.val_pow_eq_pow_val, Ideal.span_singleton_mul_left_unit (u ^ τ).isUnit]`. Take `⟨ℓ, hℓ, hb⟩` from `CyclicSpanLengthLemmas.lengthPart2 ϖ hϖ M N d hd (e * τ) (e * S) V s hs0 hs (by`. Introduce `β hβ`. Take `⟨C, hC, hcard, hx⟩` from `h1 β hβ`.

Use `⟨C, hC, hcard, fun x hxM => ?_⟩` and prove the remaining obligations. Use `ln_conv u ϖ a e hau (τ + β * S) x _ (hx x hxM)` as an intermediate fact. Establish `he : e * τ + β * (e * S) = e * (τ + β * S)` using `by ring`. Rewrite using `[he]`. Conclude with `this)`.

Use the proof step `(by`. Take `⟨C, hC, hcard, hx⟩` from `h2`. Use `⟨C, hC, hcard, fun x hxM => ?_⟩` and prove the remaining obligations. Use `ln_conv u ϖ a e hau (V * S) x _ (hx x hxM)` as an intermediate fact. Establish `he : V * (e * S) = e * (V * S)` using `by ring`.

Rewrite using `[he]`. Conclude with `this)`. Use `⟨ℓ, by rw [hspan]; exact hℓ, ?_⟩` and prove the remaining obligations. Rewrite using `[hlen, ENat.toNat_natCast]`. Use `hb.trans (le_of_eq ?_)` and prove the remaining obligations.

Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem lengthFromAllBut {R X : Type} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [AddCommGroup X] [Module R X] (a : R) (ha : a ≠ 0) (M N : Submodule R X)
    [Module.Free R M] [Module.Finite R M] (d : ℕ) (hd : Module.finrank R M = d)
    (τ S V : ℕ) (s : ℝ) (hs0 : 0 ≤ s) (hs : s ≤ 1 / 2)
    (h1 : ∀ β < V, ∃ C : Finset X, (↑C : Set X) ⊆ M ∧ (C.card : ℝ) ≤ d * s ^ (β + 1) ∧
      ∀ x ∈ M, a ^ (τ + β * S) • x ∈ N ⊔ Submodule.span R (↑C : Set X))
    (h2 : Formalism.G0.AllButLE a M N 0 (V * S)) :
    ∃ ℓ : ℕ, Module.length R (↥M ⧸ Submodule.comap M.subtype (N ⊓ (Ideal.span {a ^ τ}) • M)) = ℓ ∧
      (ℓ : ℝ) ≤ ((Module.length R (R ⧸ Ideal.span {a})).toNat : ℝ) * ((d : ℝ) * τ + 2 * S * s * d) := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible R
  obtain ⟨e, u, hau⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible ha hϖ
  have hlen : Module.length R (R ⧸ Ideal.span {a}) = e := by
    rw [hau, Ideal.span_singleton_mul_left_unit u.isUnit]
    exact ln_length_pow ϖ hϖ e
  have hspan : Ideal.span {a ^ τ} = Ideal.span {ϖ ^ (e * τ)} := by
    rw [hau, mul_pow, ← pow_mul, ← Units.val_pow_eq_pow_val,
      Ideal.span_singleton_mul_left_unit (u ^ τ).isUnit]
  obtain ⟨ℓ, hℓ, hb⟩ := CyclicSpanLengthLemmas.lengthPart2 ϖ hϖ M N d hd (e * τ) (e * S) V s hs0 hs
    (by
      intro β hβ
      obtain ⟨C, hC, hcard, hx⟩ := h1 β hβ
      refine ⟨C, hC, hcard, fun x hxM => ?_⟩
      have := ln_conv u ϖ a e hau (τ + β * S) x _ (hx x hxM)
      have he : e * τ + β * (e * S) = e * (τ + β * S) := by ring
      rw [he]
      exact this)
    (by
      obtain ⟨C, hC, hcard, hx⟩ := h2
      refine ⟨C, hC, hcard, fun x hxM => ?_⟩
      have := ln_conv u ϖ a e hau (V * S) x _ (hx x hxM)
      have he : V * (e * S) = e * (V * S) := by ring
      rw [he]
      exact this)
  refine ⟨ℓ, by rw [hspan]; exact hℓ, ?_⟩
  rw [hlen, ENat.toNat_natCast]
  refine hb.trans (le_of_eq ?_)
  push_cast
  ring

end Formalism.MainNotions.G.LatticeSystems

namespace Formalism.MainNotions.G.LatticeSystems

open Formalism.MainNotions.G Formalism.MainNotions.SelectionLemmas Formalism.G0

variable {p : ℕ}

def piLattice₂ (G : GAtP p) (v : Fin G.P.nV) (tv : ℕ) (s : Slot)
    (Lv : Submodule (G.P.W v) (Fin (G.P.m + 1) → G.P.Qq v)) :
    Submodule G.O (MvPolynomial (Fin (G.P.n' v) × (Fin (G.P.m + 1) × Fin (G.P.m + 1))) G.Kf) :=
  match s with
  | Slot.base => Hten G.O (G.P.lam0 v) fun s => extO G.O (G.P.ι v) (G.P.σ v) s.val Lv
  | Slot.ball => ofV (Nsrc p (G.P.n' v) (G.P.ι v) (G.P.σ v) G.P.w G.P.r (G.P.lam0 v) tv Lv)
  | Slot.dual => ofV (predual (Ntgt p (G.P.n' v) (G.P.ι v) (G.P.σ v) G.P.w G.P.r (G.P.lam0 v) tv Lv))

def latSys (G : GAtP p) (t : Fin G.P.nV → ℕ) (σ : Fin G.P.nV → Slot) : Submodule G.O G.Fn :=
  G.funMod (G.P.sys fun v => piLattice₂ G v (t v) (σ v))

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem latSys_base (G : GAtP p) (t : Fin G.P.nV → ℕ) : latSys G t (fun _ => Slot.base) = G.Mna := rfl

def RestLocChain (G : GAtP p) (v : Fin G.P.nV) (tv : ℕ) : Prop :=
  ∀ Lv : Submodule (G.P.W v) (Fin (G.P.m + 1) → G.P.Qq v), IsLattice (G.P.W v) Lv →
    piLattice₂ G v tv Slot.base Lv ≤ piLattice₂ G v tv Slot.ball Lv ∧
    piLattice₂ G v tv Slot.dual Lv ≤ piLattice₂ G v tv Slot.base Lv ∧
    (∀ z ∈ piLattice₂ G v tv Slot.ball Lv, G.P.w ^ tv • z ∈ piLattice₂ G v tv Slot.base Lv) ∧
    (∀ z ∈ piLattice₂ G v tv Slot.base Lv, G.P.w ^ tv • z ∈ piLattice₂ G v tv Slot.dual Lv)

def RestNat (G : GAtP p) (VV : Finset (Fin G.P.nV)) (t : Fin G.P.nV → ℕ) : Prop :=
  ∀ σ, ∀ v ∈ VV, ∀ x ∈ latSys G t (Function.update σ v Slot.ball),
    G.yv v x ∈ latSys G t (Function.update σ v Slot.dual)

def RestJ (G : GAtP p) (VV : Finset (Fin G.P.nV)) (t : Fin G.P.nV → ℕ) (Dd : ℕ)
    (κ : Fin G.P.nV → ℝ) : Prop :=
  ∀ B : Finset (Fin G.P.nV), B ⊆ VV → B.Nonempty →
    ∃ C : Finset G.Fn, (↑C : Set G.Fn) ⊆ latSys G t (vertexLabel B) ∧
      (C.card : ℝ) ≤ (∏ v ∈ B, κ v) * (G.dna : ℝ) ∧
      ∀ x ∈ latSys G t (vertexLabel B), (p : G.O) ^ (Dd + 1) • x ∈
        (⨆ v ∈ B, Submodule.span G.O
          (G.yv v '' (latSys G t (Function.update (vertexLabel B) v Slot.ball) : Set G.Fn))) ⊔
          Submodule.span G.O (↑C : Set G.Fn)

/- English proof (translation)
Unfold `GAtP.funMod at hF ⊢`. Rewrite `hF`, the goal using `[Submodule.mem_pi]`. Introduce `i hi`. Establish `h0` using `hF i hi`. Unfold `Level.funMod at h0 ⊢`.

Rewrite `h0`, the goal using `[Submodule.mem_inf, Submodule.mem_inf]`. Take `⟨⟨hA, hB⟩, hC⟩` from `h0`. Use `⟨⟨?_, Submodule.smul_mem _ c hB⟩, Submodule.smul_mem _ c hC⟩` and prove the remaining obligations. Establish `hA'` using `fun L hL => (Submodule.mem_iInf _).1 ((Submodule.mem_iInf _).1 hA L) hL`. Use `(Submodule.mem_iInf _).2 fun L => (Submodule.mem_iInf _).2 fun hL => ?_` and prove the remaining obligations.

Conclude with `h L hL _ (hA' L hL)`.
-/
theorem ch_funMod_smul (G : GAtP p) (Hv Hv' : G.P.Tup → Submodule G.O G.P.Xsp) (c : G.O)
    (h : ∀ L, G.P.IsLatTup L → ∀ x ∈ Hv L, c • x ∈ Hv' L) (F : G.Fn) (hF : F ∈ G.funMod Hv) :
    c • F ∈ G.funMod Hv' := by
  unfold GAtP.funMod at hF ⊢
  rw [Submodule.mem_pi] at hF ⊢
  intro i hi
  have h0 := hF i hi
  unfold Level.funMod at h0 ⊢
  rw [Submodule.mem_inf, Submodule.mem_inf] at h0 ⊢
  obtain ⟨⟨hA, hB⟩, hC⟩ := h0
  refine ⟨⟨?_, Submodule.smul_mem _ c hB⟩, Submodule.smul_mem _ c hC⟩
  have hA' := fun L hL => (Submodule.mem_iInf _).1 ((Submodule.mem_iInf _).1 hA L) hL
  refine (Submodule.mem_iInf _).2 fun L => (Submodule.mem_iInf _).2 fun hL => ?_
  exact h L hL _ (hA' L hL)

/- English proof (translation)
Unfold `Places.tenV at hX ⊢`. Proceed by induction on `hX using Submodule.span_induction with`. Consider the case `mem X hX`. Take `⟨F, hF, rfl⟩` from `hX`. Apply `Submodule.subset_span` to reduce the goal to its premises.

Use `⟨Function.update F v (c • F v), ?_, ?_⟩` and prove the remaining obligations. Introduce `u`. Distinguish the cases in `huv : u = v`. Substitute `huv` using the available equality. Rewrite using `[Function.update_self]`.

Conclude with `hv _ (hF u)`. Rewrite using `[Function.update_of_ne huv]`. Conclude with `hu u huv (hF u)`. Establish `h1 : (fun u => G.P.vEmb u (Function.update F v (c • F v) u)) = Function.update (fun u => G.P.vEmb u (F u)) v (G.P.vEmb v (c • F v))`. Use function extensionality and compare the values at `u`.

Conclude with `Function.apply_update (fun u => G.P.vEmb u) F v (c • F v) u`. Establish `h2 : ∏ u, G.P.vEmb u (F u) = G.P.vEmb v (F v) * ∏ u ∈ Finset.univ \ {v}, G.P.vEmb u (F u)`. Use `Finset.prod_update_of_mem (Finset.mem_univ v) (fun u => G.P.vEmb u (F u)) (G.P.vEmb v (F v))` as an intermediate fact. Rewrite `this` using `[Function.update_eq_self]`. Conclude with `this`.

Establish `h3 : G.P.vEmb v (c • F v) = c • G.P.vEmb v (F v)` using `(G.P.vEmb v).toLinearMap.map_smul_of_tower c (F v)`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[h2, smul_mul_assoc]`. Use `_ = ∏ u, Function.update (fun u => G.P.vEmb u (F u)) v (G.P.vEmb v (c • F v)) u := by`. Rewrite using `[Finset.prod_update_of_mem (Finset.mem_univ v), h3]`.

Use `_ = ∏ u, G.P.vEmb u (Function.update F v (c • F v) u) := by`. Rewrite using `[← h1]`. Consider the case `zero => rw [smul_zero]`. Conclude with `Submodule.zero_mem _`. Consider the case `add x y _ _ hx hy => rw [smul_add]`.

Conclude with `Submodule.add_mem _ hx hy`. Consider the case `smul a x _ hx => rw [smul_comm]`. Conclude with `Submodule.smul_mem _ a hx`.
-/
theorem ch_tenV_smul (G : GAtP p) (v : Fin G.P.nV) (c : G.O)
    (M M' : ∀ u, Submodule G.O (MvPolynomial (Fin (G.P.n' u) × (Fin (G.P.m + 1) × Fin (G.P.m + 1))) G.Kf))
    (hv : ∀ x ∈ M v, c • x ∈ M' v) (hu : ∀ u, u ≠ v → M u ≤ M' u) (X : G.P.Xsp) (hX : X ∈ G.P.tenV M) :
    c • X ∈ G.P.tenV M' := by
  classical
  unfold Places.tenV at hX ⊢
  induction hX using Submodule.span_induction with
  | mem X hX =>
    obtain ⟨F, hF, rfl⟩ := hX
    apply Submodule.subset_span
    refine ⟨Function.update F v (c • F v), ?_, ?_⟩
    · intro u
      by_cases huv : u = v
      · subst huv
        rw [Function.update_self]
        exact hv _ (hF u)
      · rw [Function.update_of_ne huv]
        exact hu u huv (hF u)
    · have h1 : (fun u => G.P.vEmb u (Function.update F v (c • F v) u)) =
          Function.update (fun u => G.P.vEmb u (F u)) v (G.P.vEmb v (c • F v)) := by
        funext u
        exact Function.apply_update (fun u => G.P.vEmb u) F v (c • F v) u
      have h2 : ∏ u, G.P.vEmb u (F u) =
          G.P.vEmb v (F v) * ∏ u ∈ Finset.univ \ {v}, G.P.vEmb u (F u) := by
        have := Finset.prod_update_of_mem (Finset.mem_univ v) (fun u => G.P.vEmb u (F u))
          (G.P.vEmb v (F v))
        rw [Function.update_eq_self] at this
        exact this
      have h3 : G.P.vEmb v (c • F v) = c • G.P.vEmb v (F v) :=
        (G.P.vEmb v).toLinearMap.map_smul_of_tower c (F v)
      calc c • ∏ u, G.P.vEmb u (F u)
          = (c • G.P.vEmb v (F v)) * ∏ u ∈ Finset.univ \ {v}, G.P.vEmb u (F u) := by
            rw [h2, smul_mul_assoc]
        _ = ∏ u, Function.update (fun u => G.P.vEmb u (F u)) v (G.P.vEmb v (c • F v)) u := by
            rw [Finset.prod_update_of_mem (Finset.mem_univ v), h3]
        _ = ∏ u, G.P.vEmb u (Function.update F v (c • F v) u) := by
            rw [← h1]
  | zero => rw [smul_zero]; exact Submodule.zero_mem _
  | add x y _ _ hx hy => rw [smul_add]; exact Submodule.add_mem _ hx hy
  | smul a x _ hx => rw [smul_comm]; exact Submodule.smul_mem _ a hx

/- English proof (translation)
Use `ch_funMod_smul G _ _ c ?_ x hx` and prove the remaining obligations. Introduce `L hL X hX`. Use `ch_tenV_smul G v c _ _ ?_ ?_ X hX` and prove the remaining obligations. Simplify using `only [Function.update_self]`. Conclude with `hloc (L v) (hL v)`.

Introduce `u hu`. Simplify using `only [Function.update_of_ne hu]`. Conclude with `le_rfl`.
-/
theorem ch_step (G : GAtP p) (t : Fin G.P.nV → ℕ) (σ : Fin G.P.nV → Slot) (v : Fin G.P.nV)
    (s1 s2 : Slot) (c : G.O)
    (hloc : ∀ Lv, IsLattice (G.P.W v) Lv → ∀ z ∈ piLattice₂ G v (t v) s1 Lv, c • z ∈ piLattice₂ G v (t v) s2 Lv)
    (x : G.Fn) (hx : x ∈ latSys G t (Function.update σ v s1)) :
    c • x ∈ latSys G t (Function.update σ v s2) := by
  refine ch_funMod_smul G _ _ c ?_ x hx
  intro L hL X hX
  refine ch_tenV_smul G v c _ _ ?_ ?_ X hX
  · simp only [Function.update_self]
    exact hloc (L v) (hL v)
  · intro u hu
    simp only [Function.update_of_ne hu]
    exact le_rfl

/- English proof (translation)
Use `⟨fun σ v hv x hx => ?_, fun σ v hv x hx => ?_, fun σ v hv x hx => ?_, fun σ v hv x hx => ?_⟩` and prove the remaining obligations. Use `ch_step G t σ v Slot.base Slot.ball 1 (fun Lv hLv z hz => by rw [one_smul]; exact (h v hv Lv hLv).1 hz) x hx` as an intermediate fact. Rewrite `this` using `[one_smul]`. Then use the resulting hypothesis. Use `ch_step G t σ v Slot.dual Slot.base 1 (fun Lv hLv z hz => by rw [one_smul]; exact (h v hv Lv hLv).2.1 hz) x hx` as an intermediate fact. Rewrite `this` using `[one_smul]`. Then use the resulting hypothesis.

Conclude with `ch_step G t σ v Slot.ball Slot.base _ (fun Lv hLv => (h v hv Lv hLv).2.2.1) x hx`. Conclude with `ch_step G t σ v Slot.base Slot.dual _ (fun Lv hLv => (h v hv Lv hLv).2.2.2) x hx`.
-/
theorem ch_chain (G : GAtP p) (VV : Finset (Fin G.P.nV)) (t : Fin G.P.nV → ℕ)
    (h : ∀ v ∈ VV, RestLocChain G v (t v)) :
    (∀ σ, ∀ v ∈ VV, latSys G t (Function.update σ v Slot.base) ≤ latSys G t (Function.update σ v Slot.ball)) ∧
    (∀ σ, ∀ v ∈ VV, latSys G t (Function.update σ v Slot.dual) ≤ latSys G t (Function.update σ v Slot.base)) ∧
    (∀ σ, ∀ v ∈ VV, ∀ x ∈ latSys G t (Function.update σ v Slot.ball),
      G.P.w ^ t v • x ∈ latSys G t (Function.update σ v Slot.base)) ∧
    (∀ σ, ∀ v ∈ VV, ∀ x ∈ latSys G t (Function.update σ v Slot.base),
      G.P.w ^ t v • x ∈ latSys G t (Function.update σ v Slot.dual)) := by
  refine ⟨fun σ v hv x hx => ?_, fun σ v hv x hx => ?_, fun σ v hv x hx => ?_, fun σ v hv x hx => ?_⟩
  · have := ch_step G t σ v Slot.base Slot.ball 1
      (fun Lv hLv z hz => by rw [one_smul]; exact (h v hv Lv hLv).1 hz) x hx
    rwa [one_smul] at this
  · have := ch_step G t σ v Slot.dual Slot.base 1
      (fun Lv hLv z hz => by rw [one_smul]; exact (h v hv Lv hLv).2.1 hz) x hx
    rwa [one_smul] at this
  · exact ch_step G t σ v Slot.ball Slot.base _ (fun Lv hLv => (h v hv Lv hLv).2.2.1) x hx
  · exact ch_step G t σ v Slot.base Slot.dual _ (fun Lv hLv => (h v hv Lv hLv).2.2.2) x hx

/- English proof (translation)
Take `⟨c1, c2, c3, c4⟩` from `ch_chain G VV t h1`. Conclude with `⟨latSys G t, latSys_base G t, c1, c2, c3, c4, h2, h3⟩`.
-/
theorem restWalk_of_concrete (G : GAtP p) (VV : Finset (Fin G.P.nV)) (t : Fin G.P.nV → ℕ) (Dd : ℕ)
    (κ : Fin G.P.nV → ℝ) (h1 : ∀ v ∈ VV, RestLocChain G v (t v)) (h2 : RestNat G VV t)
    (h3 : RestJ G VV t Dd κ) : RestWalk G VV t Dd κ := by
  obtain ⟨c1, c2, c3, c4⟩ := ch_chain G VV t h1
  exact ⟨latSys G t, latSys_base G t, c1, c2, c3, c4, h2, h3⟩

def LocalLatticeChain (G : GAtP p) (v : Fin G.P.nV) (tv : ℕ) : Prop :=
  ∀ Lv : Submodule (G.P.W v) (Fin (G.P.m + 1) → G.P.Qq v), IsLattice (G.P.W v) Lv →
    (∀ z ∈ piLattice₂ G v tv Slot.base Lv, z ∈ Vsp G.Kf (G.P.lam0 v)) ∧
    (∀ e : Edge (G.P.W v) (G.P.Qq v) (G.P.m + 1), IsEdge p (G.P.n' v) G.P.r e → e.src = Lv →
      HL (O := G.O) (G.P.ι v) (G.P.σ v) (G.P.lam0 v) Lv ≤
        Re p (G.P.ι v) (G.P.σ v) G.P.w G.P.r (G.P.lam0 v) e) ∧
    piLattice₂ G v tv Slot.dual Lv ≤ piLattice₂ G v tv Slot.base Lv

/- English proof (translation)
Introduce `h`. Apply `kp_p_ne_zero G v` to reduce the goal to its premises. Rewrite using `[← (G.P.setting v).w_sq, map_pow, h]`. Simplify using the standard rewrite rules.
-/
theorem ch_w_ne_zero (G : GAtP p) (v : Fin G.P.nV) : algebraMap G.O G.Kf G.P.w ≠ 0 := by
  intro h
  apply kp_p_ne_zero G v
  rw [← (G.P.setting v).w_sq, map_pow, h]
  simp

/- English proof (translation)
Rewrite using `[zpow_natCast, ← map_pow, algebraMap_smul]`.
-/
theorem ch_w_smul (G : GAtP p) {X : Type*} [AddCommGroup X] [Module G.Kf X] [Module G.O X]
    [IsScalarTower G.O G.Kf X] (t : ℕ) (x : X) :
    G.P.w ^ t • x = (algebraMap G.O G.Kf G.P.w ^ (t : ℤ)) • x := by
  rw [zpow_natCast, ← map_pow, algebraMap_smul]

/- English proof (translation)
Rewrite using `[smul_smul, ← zpow_add₀ (ch_w_ne_zero G v), add_neg_cancel, zpow_zero, one_smul]`.
-/
theorem ch_cancel (G : GAtP p) (v : Fin G.P.nV) {X : Type*} [AddCommGroup X] [Module G.Kf X] (t : ℕ) (x : X) :
    (algebraMap G.O G.Kf G.P.w ^ (t : ℤ)) • (algebraMap G.O G.Kf G.P.w ^ (-(t : ℤ))) • x = x := by
  rw [smul_smul, ← zpow_add₀ (ch_w_ne_zero G v), add_neg_cancel, zpow_zero, one_smul]

/- English proof (translation)
Rewrite using `[smul_smul, ← zpow_add₀ (ch_w_ne_zero G v), neg_add_cancel, zpow_zero, one_smul]`.
-/
theorem ch_cancel' (G : GAtP p) (v : Fin G.P.nV) {X : Type*} [AddCommGroup X] [Module G.Kf X] (t : ℕ) (x : X) :
    (algebraMap G.O G.Kf G.P.w ^ (-(t : ℤ))) • (algebraMap G.O G.Kf G.P.w ^ (t : ℤ)) • x = x := by
  rw [smul_smul, ← zpow_add₀ (ch_w_ne_zero G v), neg_add_cancel, zpow_zero, one_smul]

/- English proof (translation)
Introduce `Lv hLv`. Take `⟨ha, hb, hc⟩` from `h Lv hLv`. Use `⟨?_, hc, ?_, ?_⟩` and prove the remaining obligations. Introduce `z hz`. Establish `hz' : (⟨z, ha z hz⟩ : Vsp G.Kf (G.P.lam0 v)) ∈ HL (O` using `G.O) (G.P.ι v) (G.P.σ v) (G.P.lam0 v) Lv := hz`.

Use `⟨⟨z, ha z hz⟩, ⟨?_, ?_⟩, rfl⟩` and prove the remaining obligations. Use `⟨G.P.w ^ tv • ⟨z, ha z hz⟩, Submodule.smul_mem _ _ hz', ?_⟩` and prove the remaining obligations. Rewrite using `[ch_w_smul]`. Conclude with `ch_cancel' G v tv _`. Use `(Submodule.mem_iInf _).2 fun e => (Submodule.mem_iInf _).2 fun he => ?_` and prove the remaining obligations.

Conclude with `hb e he.1 he.2 hz'`. Introduce and unpack `_ ⟨n, hn, rfl⟩`. Take `⟨x, hx, rfl⟩` from `hn.1`. Establish `hx' : (x : MvPolynomial (Fin (G.P.n' v) × (Fin (G.P.m + 1) × Fin (G.P.m + 1))) G.Kf) ∈ piLattice₂ G v tv Slot.base Lv` using `hx`. Establish `e1 : G.P.w ^ tv • ((Vsp G.Kf (G.P.lam0 v)).subtype.restrictScalars G.O) (((LinearMap.lsmul G.Kf (Vsp G.Kf (G.P.lam0 v)) (algebraMap G.O G.Kf G.P.w ^ (-(tv : ℤ)))).restrictScalars G.O) x) = (x : MvPolynomial (Fin (G.P.n' v) × (Fin (G.P.m + 1) × Fin (G.P.m + 1))) G.Kf)`.

Rewrite using `[ch_w_smul]`. Conclude with `ch_cancel G v tv _`. Rewrite using `[e1]`. Conclude with `hx'`. Introduce `z hz`.

Establish `hz' : (⟨z, ha z hz⟩ : Vsp G.Kf (G.P.lam0 v)) ∈ HL (O` using `G.O) (G.P.ι v) (G.P.σ v) (G.P.lam0 v) Lv := hz`. Use `⟨G.P.w ^ tv • ⟨z, ha z hz⟩, ?_, rfl⟩` and prove the remaining obligations. Introduce `φ hφ`. Take `⟨ψ, hψ, rfl⟩` from `hφ.1`. Establish `e2 : (((LinearMap.lsmul G.Kf (Module.Dual G.Kf (Vsp G.Kf (G.P.lam0 v))) (algebraMap G.O G.Kf G.P.w ^ (-(tv : ℤ)))).restrictScalars G.O) ψ) (G.P.w ^ tv • (⟨z, ha z hz⟩ : Vsp G.Kf (G.P.lam0 v))) = ψ ⟨z, ha z hz⟩`.

Rewrite using `[ch_w_smul, map_smul]`. Use `show (algebraMap G.O G.Kf G.P.w ^ (tv : ℤ)) • ((algebraMap G.O G.Kf G.P.w ^ (-(tv : ℤ))) • ψ ⟨z, ha z hz⟩) = _`. Conclude with `ch_cancel G v tv _`. Rewrite using `[e2]`. Conclude with `hψ _ hz'`.
-/
theorem ch_locChain (G : GAtP p) (v : Fin G.P.nV) (tv : ℕ) (h : LocalLatticeChain G v tv) :
    RestLocChain G v tv := by
  intro Lv hLv
  obtain ⟨ha, hb, hc⟩ := h Lv hLv
  refine ⟨?_, hc, ?_, ?_⟩
  · intro z hz
    have hz' : (⟨z, ha z hz⟩ : Vsp G.Kf (G.P.lam0 v)) ∈
        HL (O := G.O) (G.P.ι v) (G.P.σ v) (G.P.lam0 v) Lv := hz
    refine ⟨⟨z, ha z hz⟩, ⟨?_, ?_⟩, rfl⟩
    · refine ⟨G.P.w ^ tv • ⟨z, ha z hz⟩, Submodule.smul_mem _ _ hz', ?_⟩
      rw [ch_w_smul]
      exact ch_cancel' G v tv _
    · refine (Submodule.mem_iInf _).2 fun e => (Submodule.mem_iInf _).2 fun he => ?_
      exact hb e he.1 he.2 hz'
  · rintro _ ⟨n, hn, rfl⟩
    obtain ⟨x, hx, rfl⟩ := hn.1
    have hx' : (x : MvPolynomial (Fin (G.P.n' v) × (Fin (G.P.m + 1) × Fin (G.P.m + 1))) G.Kf) ∈
        piLattice₂ G v tv Slot.base Lv := hx
    have e1 : G.P.w ^ tv • ((Vsp G.Kf (G.P.lam0 v)).subtype.restrictScalars G.O)
        (((LinearMap.lsmul G.Kf (Vsp G.Kf (G.P.lam0 v))
          (algebraMap G.O G.Kf G.P.w ^ (-(tv : ℤ)))).restrictScalars G.O) x) =
        (x : MvPolynomial (Fin (G.P.n' v) × (Fin (G.P.m + 1) × Fin (G.P.m + 1))) G.Kf) := by
      rw [ch_w_smul]
      exact ch_cancel G v tv _
    rw [e1]
    exact hx'
  · intro z hz
    have hz' : (⟨z, ha z hz⟩ : Vsp G.Kf (G.P.lam0 v)) ∈
        HL (O := G.O) (G.P.ι v) (G.P.σ v) (G.P.lam0 v) Lv := hz
    refine ⟨G.P.w ^ tv • ⟨z, ha z hz⟩, ?_, rfl⟩
    intro φ hφ
    obtain ⟨ψ, hψ, rfl⟩ := hφ.1
    have e2 : (((LinearMap.lsmul G.Kf (Module.Dual G.Kf (Vsp G.Kf (G.P.lam0 v)))
          (algebraMap G.O G.Kf G.P.w ^ (-(tv : ℤ)))).restrictScalars G.O) ψ)
        (G.P.w ^ tv • (⟨z, ha z hz⟩ : Vsp G.Kf (G.P.lam0 v))) = ψ ⟨z, ha z hz⟩ := by
      rw [ch_w_smul, map_smul]
      show (algebraMap G.O G.Kf G.P.w ^ (tv : ℤ)) • ((algebraMap G.O G.Kf G.P.w ^ (-(tv : ℤ))) • ψ ⟨z, ha z hz⟩) = _
      exact ch_cancel G v tv _
    rw [e2]
    exact hψ _ hz'

/- English proof (translation)
The claim follows from `restWalk_of_concrete G VV t Dd κ (fun v hv => ch_locChain G v (t v) (h1 v hv)) h2 h3`.
-/
theorem restWalk_of_concrete' (G : GAtP p) (VV : Finset (Fin G.P.nV)) (t : Fin G.P.nV → ℕ) (Dd : ℕ)
    (κ : Fin G.P.nV → ℝ) (h1 : ∀ v ∈ VV, LocalLatticeChain G v (t v)) (h2 : RestNat G VV t)
    (h3 : RestJ G VV t Dd κ) : RestWalk G VV t Dd κ :=
  restWalk_of_concrete G VV t Dd κ (fun v hv => ch_locChain G v (t v) (h1 v hv)) h2 h3

def RestLocD (G : GAtP p) (v : Fin G.P.nV) : Prop :=
  ∀ Lv : Submodule (G.P.W v) (Fin (G.P.m + 1) → G.P.Qq v), IsLattice (G.P.W v) Lv →
    (∀ z ∈ Hten G.O (G.P.lam0 v) (fun s => extO G.O (G.P.ι v) (G.P.σ v) s.val Lv), z ∈ Vsp G.Kf (G.P.lam0 v)) ∧
    (∀ e : Edge (G.P.W v) (G.P.Qq v) (G.P.m + 1), IsEdge p (G.P.n' v) G.P.r e → e.src = Lv →
      HL (O := G.O) (G.P.ι v) (G.P.σ v) (G.P.lam0 v) Lv ≤
        Re p (G.P.ι v) (G.P.σ v) G.P.w G.P.r (G.P.lam0 v) e) ∧
    (∀ e : Edge (G.P.W v) (G.P.Qq v) (G.P.m + 1), IsEdge p (G.P.n' v) G.P.r e → e.tgt = Lv →
      Formalism.GradedWeylDivisibility.dualLat G.O G.Kf (HL (O := G.O) (G.P.ι v) (G.P.σ v) (G.P.lam0 v) Lv) ≤
        Re' p (G.P.ι v) (G.P.σ v) G.P.w G.P.r (G.P.lam0 v) e) ∧
    predual (Formalism.GradedWeylDivisibility.dualLat G.O G.Kf (HL (O := G.O) (G.P.ι v) (G.P.σ v) (G.P.lam0 v) Lv)) ≤
      HL (O := G.O) (G.P.ι v) (G.P.σ v) (G.P.lam0 v) Lv

/- English proof (translation)
Introduce `Lv hLv`. Take `⟨ha, hb, hc1, hc2⟩` from `h Lv hLv`. Use `⟨ha, hb, ?_⟩` and prove the remaining obligations. Introduce and unpack `_ ⟨x, hx, rfl⟩`. Establish `hx2 : x ∈ predual (Formalism.GradedWeylDivisibility.dualLat G.O G.Kf (HL (O` using `G.O) (G.P.ι v) (G.P.σ v) (G.P.lam0 v) Lv)) := by`.

Introduce `ψ hψ`. Apply `hx ψ` to reduce the goal to its premises. Use `⟨?_, ?_⟩` and prove the remaining obligations. Use `⟨G.P.w ^ tv • ψ, Submodule.smul_mem _ _ hψ, ?_⟩` and prove the remaining obligations. Rewrite using `[ch_w_smul]`.

Conclude with `ch_cancel' G v tv _`. Use `(Submodule.mem_iInf _).2 fun e => (Submodule.mem_iInf _).2 fun he => ?_` and prove the remaining obligations. Conclude with `hc1 e he.1 he.2 hψ`. Conclude with `hc2 hx2`.
-/
theorem local_lattice_chain_of_local (G : GAtP p) (v : Fin G.P.nV) (tv : ℕ) (h : RestLocD G v) : LocalLatticeChain G v tv := by
  intro Lv hLv
  obtain ⟨ha, hb, hc1, hc2⟩ := h Lv hLv
  refine ⟨ha, hb, ?_⟩
  rintro _ ⟨x, hx, rfl⟩
  have hx2 : x ∈ predual (Formalism.GradedWeylDivisibility.dualLat G.O G.Kf
      (HL (O := G.O) (G.P.ι v) (G.P.σ v) (G.P.lam0 v) Lv)) := by
    intro ψ hψ
    apply hx ψ
    refine ⟨?_, ?_⟩
    · refine ⟨G.P.w ^ tv • ψ, Submodule.smul_mem _ _ hψ, ?_⟩
      rw [ch_w_smul]
      exact ch_cancel' G v tv _
    · refine (Submodule.mem_iInf _).2 fun e => (Submodule.mem_iInf _).2 fun he => ?_
      exact hc1 e he.1 he.2 hψ
  exact hc2 hx2

/- English proof (translation)
The claim follows from `restWalk_of_concrete' G VV t Dd κ (fun v hv => local_lattice_chain_of_local G v (t v) (h1 v hv)) h2 h3`.
-/
theorem restWalk_of_local (G : GAtP p) (VV : Finset (Fin G.P.nV)) (t : Fin G.P.nV → ℕ) (Dd : ℕ)
    (κ : Fin G.P.nV → ℝ) (h1 : ∀ v ∈ VV, RestLocD G v) (h2 : RestNat G VV t)
    (h3 : RestJ G VV t Dd κ) : RestWalk G VV t Dd κ :=
  restWalk_of_concrete' G VV t Dd κ (fun v hv => local_lattice_chain_of_local G v (t v) (h1 v hv)) h2 h3

end Formalism.MainNotions.G.LatticeSystems

namespace Formalism.MainNotions.G.LatticeSystems

open Formalism.MainNotions.G Formalism.MainNotions.SelectionLemmas Formalism.G0

variable {p : ℕ}

/- English proof (translation)
Rewrite using `[← map_pow, (G.P.setting v).w_sq, map_natCast]`.
-/
theorem nt_p_eq (G : GAtP p) (v : Fin G.P.nV) : (p : G.Kf) = algebraMap G.O G.Kf G.P.w ^ 2 := by
  rw [← map_pow, (G.P.setting v).w_sq, map_natCast]

/- English proof (translation)
Establish `ha` using `ch_w_ne_zero G v`. Rewrite using `[nt_p_eq G v, ← zpow_natCast (algebraMap G.O G.Kf G.P.w) 2, ← zpow_mul, ← zpow_add₀ ha, ← zpow_add₀ ha]`. Establish `: -A + (((2 : ℕ) : ℤ) * A + -A) = 0` using `by push_cast; ring`. Rewrite using `[this, zpow_zero]`.
-/
theorem nt_scal (G : GAtP p) (v : Fin G.P.nV) (A : ℤ) :
    algebraMap G.O G.Kf G.P.w ^ (-A) * ((p : G.Kf) ^ A * algebraMap G.O G.Kf G.P.w ^ (-A)) = 1 := by
  have ha := ch_w_ne_zero G v
  rw [nt_p_eq G v, ← zpow_natCast (algebraMap G.O G.Kf G.P.w) 2, ← zpow_mul, ← zpow_add₀ ha, ← zpow_add₀ ha]
  have : -A + (((2 : ℕ) : ℤ) * A + -A) = 0 := by push_cast; ring
  rw [this, zpow_zero]

/- English proof (translation)
Take `⟨n, hn, rfl⟩` from `hz`. Establish `hn2 : n ∈ Re p (G.P.ι v) (G.P.σ v) G.P.w G.P.r (G.P.lam0 v) e` using `(Submodule.mem_iInf _).1 ((Submodule.mem_iInf _).1 hn.2 e) ⟨he, rfl⟩`. Take `⟨x, hx, rfl⟩` from `hn2`. Use `⟨((p : G.Kf) ^ G.P.ArV v) • ((algebraMap G.O G.Kf G.P.w ^ (-Ar G.P.r (G.P.lam0 v))) • x), ?_, rfl⟩` and prove the remaining obligations. Introduce `φ hφ`.

Establish `hφ2 : φ ∈ Re' p (G.P.ι v) (G.P.σ v) G.P.w G.P.r (G.P.lam0 v) e` using `(Submodule.mem_iInf _).1 ((Submodule.mem_iInf _).1 hφ.2 e) ⟨he, rfl⟩`. Take `⟨ψ, hψ, rfl⟩` from `hφ2`. Establish `e2 : ((algebraMap G.O G.Kf G.P.w ^ (-Ar G.P.r (G.P.lam0 v))) • ψ) (((p : G.Kf) ^ G.P.ArV v) • ((algebraMap G.O G.Kf G.P.w ^ (-Ar G.P.r (G.P.lam0 v))) • x)) = ψ x`. Rewrite using `[LinearMap.smul_apply, map_smul, map_smul, smul_smul, smul_smul]`. Unfold `Places.ArV`.

Rewrite using `[mul_assoc, nt_scal G v, one_smul]`. Establish `e3` using `hψ x hx`. Rewrite `e3` using `[← e2]`. Conclude with `e3`.
-/
theorem nt_local (G : GAtP p) (v : Fin G.P.nV) (tv : ℕ) (e : Edge (G.P.W v) (G.P.Qq v) (G.P.m + 1))
    (he : IsEdge p (G.P.n' v) G.P.r e)
    (z : MvPolynomial (Fin (G.P.n' v) × (Fin (G.P.m + 1) × Fin (G.P.m + 1))) G.Kf)
    (hz : z ∈ piLattice₂ G v tv Slot.ball e.src) :
    ((p : G.Kf) ^ G.P.ArV v) • z ∈ piLattice₂ G v tv Slot.dual e.tgt := by
  obtain ⟨n, hn, rfl⟩ := hz
  have hn2 : n ∈ Re p (G.P.ι v) (G.P.σ v) G.P.w G.P.r (G.P.lam0 v) e :=
    (Submodule.mem_iInf _).1 ((Submodule.mem_iInf _).1 hn.2 e) ⟨he, rfl⟩
  obtain ⟨x, hx, rfl⟩ := hn2
  refine ⟨((p : G.Kf) ^ G.P.ArV v) • ((algebraMap G.O G.Kf G.P.w ^ (-Ar G.P.r (G.P.lam0 v))) • x), ?_, rfl⟩
  intro φ hφ
  have hφ2 : φ ∈ Re' p (G.P.ι v) (G.P.σ v) G.P.w G.P.r (G.P.lam0 v) e :=
    (Submodule.mem_iInf _).1 ((Submodule.mem_iInf _).1 hφ.2 e) ⟨he, rfl⟩
  obtain ⟨ψ, hψ, rfl⟩ := hφ2
  have e2 : ((algebraMap G.O G.Kf G.P.w ^ (-Ar G.P.r (G.P.lam0 v))) • ψ)
      (((p : G.Kf) ^ G.P.ArV v) • ((algebraMap G.O G.Kf G.P.w ^ (-Ar G.P.r (G.P.lam0 v))) • x)) = ψ x := by
    rw [LinearMap.smul_apply, map_smul, map_smul, smul_smul, smul_smul]
    unfold Places.ArV
    rw [mul_assoc, nt_scal G v, one_smul]
  have e3 := hψ x hx
  rw [← e2] at e3
  exact e3

/- English proof (translation)
Unfold `Places.tenV at hX ⊢`. Proceed by induction on `hX using Submodule.span_induction with`. Consider the case `mem X hX`. Take `⟨F, hF, rfl⟩` from `hX`. Apply `Submodule.subset_span` to reduce the goal to its premises.

Use `⟨Function.update F v (c • F v), ?_, ?_⟩` and prove the remaining obligations. Introduce `u`. Distinguish the cases in `huv : u = v`. Substitute `huv` using the available equality. Rewrite using `[Function.update_self]`.

Conclude with `hv _ (hF u)`. Rewrite using `[Function.update_of_ne huv]`. Conclude with `hu u huv (hF u)`. Establish `h1 : (fun u => G.P.vEmb u (Function.update F v (c • F v) u)) = Function.update (fun u => G.P.vEmb u (F u)) v (G.P.vEmb v (c • F v))`. Use function extensionality and compare the values at `u`.

Conclude with `Function.apply_update (fun u => G.P.vEmb u) F v (c • F v) u`. Establish `h2 : ∏ u, G.P.vEmb u (F u) = G.P.vEmb v (F v) * ∏ u ∈ Finset.univ \ {v}, G.P.vEmb u (F u)`. Use `Finset.prod_update_of_mem (Finset.mem_univ v) (fun u => G.P.vEmb u (F u)) (G.P.vEmb v (F v))` as an intermediate fact. Rewrite `this` using `[Function.update_eq_self]`. Conclude with `this`.

Establish `h3 : G.P.vEmb v (c • F v) = c • G.P.vEmb v (F v)` using `map_smul (G.P.vEmb v) c (F v)`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[h2, smul_mul_assoc]`. Use `_ = ∏ u, Function.update (fun u => G.P.vEmb u (F u)) v (G.P.vEmb v (c • F v)) u := by`. Rewrite using `[Finset.prod_update_of_mem (Finset.mem_univ v), h3]`.

Use `_ = ∏ u, G.P.vEmb u (Function.update F v (c • F v) u) := by`. Rewrite using `[← h1]`. Consider the case `zero => rw [smul_zero]`. Conclude with `Submodule.zero_mem _`. Consider the case `add x y _ _ hx hy => rw [smul_add]`.

Conclude with `Submodule.add_mem _ hx hy`. Consider the case `smul a x _ hx => rw [smul_comm]`. Conclude with `Submodule.smul_mem _ a hx`.
-/
theorem nt_tenV_smulK (G : GAtP p) (v : Fin G.P.nV) (c : G.Kf)
    (M M' : ∀ u, Submodule G.O (MvPolynomial (Fin (G.P.n' u) × (Fin (G.P.m + 1) × Fin (G.P.m + 1))) G.Kf))
    (hv : ∀ x ∈ M v, c • x ∈ M' v) (hu : ∀ u, u ≠ v → M u ≤ M' u) (X : G.P.Xsp) (hX : X ∈ G.P.tenV M) :
    c • X ∈ G.P.tenV M' := by
  classical
  unfold Places.tenV at hX ⊢
  induction hX using Submodule.span_induction with
  | mem X hX =>
    obtain ⟨F, hF, rfl⟩ := hX
    apply Submodule.subset_span
    refine ⟨Function.update F v (c • F v), ?_, ?_⟩
    · intro u
      by_cases huv : u = v
      · subst huv
        rw [Function.update_self]
        exact hv _ (hF u)
      · rw [Function.update_of_ne huv]
        exact hu u huv (hF u)
    · have h1 : (fun u => G.P.vEmb u (Function.update F v (c • F v) u)) =
          Function.update (fun u => G.P.vEmb u (F u)) v (G.P.vEmb v (c • F v)) := by
        funext u
        exact Function.apply_update (fun u => G.P.vEmb u) F v (c • F v) u
      have h2 : ∏ u, G.P.vEmb u (F u) =
          G.P.vEmb v (F v) * ∏ u ∈ Finset.univ \ {v}, G.P.vEmb u (F u) := by
        have := Finset.prod_update_of_mem (Finset.mem_univ v) (fun u => G.P.vEmb u (F u))
          (G.P.vEmb v (F v))
        rw [Function.update_eq_self] at this
        exact this
      have h3 : G.P.vEmb v (c • F v) = c • G.P.vEmb v (F v) := map_smul (G.P.vEmb v) c (F v)
      calc c • ∏ u, G.P.vEmb u (F u)
          = (c • G.P.vEmb v (F v)) * ∏ u ∈ Finset.univ \ {v}, G.P.vEmb u (F u) := by
            rw [h2, smul_mul_assoc]
        _ = ∏ u, Function.update (fun u => G.P.vEmb u (F u)) v (G.P.vEmb v (c • F v)) u := by
            rw [Finset.prod_update_of_mem (Finset.mem_univ v), h3]
        _ = ∏ u, G.P.vEmb u (Function.update F v (c • F v) u) := by
            rw [← h1]
  | zero => rw [smul_zero]; exact Submodule.zero_mem _
  | add x y _ _ hx hy => rw [smul_add]; exact Submodule.add_mem _ hx hy
  | smul a x _ hx => rw [smul_comm]; exact Submodule.smul_mem _ a hx

def nt_EqSub (G : GAtP p) (i : G.comp) : Submodule G.O (G.P.Tup → G.P.Xsp) :=
  ⨅ (γ : (G.lev i).Γ) (L : G.P.Tup), LinearMap.ker
    (LinearMap.proj (R := G.O) (φ := fun _ : G.P.Tup => G.P.Xsp) ((G.lev i).smul γ L) -
      (((G.lev i).χ γ : G.O) • (((G.lev i).actX γ).restrictScalars G.O)) ∘ₗ
        LinearMap.proj (R := G.O) (φ := fun _ : G.P.Tup => G.P.Xsp) L)

def RestEquiv (G : GAtP p) (v : Fin G.P.nV) : Prop :=
  ∀ (i : G.comp) (F : G.P.Tup → G.P.Xsp), F ∈ nt_EqSub G i → Level.yv (P := G.P) v F ∈ nt_EqSub G i

/- English proof (translation)
Introduce `σ v hv x hx`. Unfold `latSys GAtP.funMod at hx ⊢`. Rewrite `hx`, the goal using `[Submodule.mem_pi]`. Introduce `i hi`. Establish `h0` using `hx i hi`.

Unfold `Level.funMod at h0 ⊢`. Rewrite `h0`, the goal using `[Submodule.mem_inf, Submodule.mem_inf]`. Take `⟨⟨hA, hB⟩, hC⟩` from `h0`. Establish `hA'` using `fun L hL => (Submodule.mem_iInf _).1 ((Submodule.mem_iInf _).1 hA L) hL`. Establish `hB' : ∀ L : G.P.Tup, ¬ G.P.IsLatTup L → x i L = 0` using `fun L hL => (Submodule.mem_iInf _).1 ((Submodule.mem_iInf _).1 hB L) hL`.

Establish `hne : ∀ (L : G.P.Tup) (L'' : Submodule (G.P.W v) (Fin (G.P.m + 1) → G.P.Qq v)) (u : Fin G.P.nV), u ≠ v → Function.update (β` using `fun v => Submodule (G.P.W v) (Fin (G.P.m + 1) → G.P.Qq v)) L v L'' u = L u := fun L L'' u hu => Function.update_of_ne hu L'' L`. Establish `hself : ∀ (L : G.P.Tup) (L'' : Submodule (G.P.W v) (Fin (G.P.m + 1) → G.P.Qq v)), Function.update (β` using `fun v => Submodule (G.P.W v) (Fin (G.P.m + 1) → G.P.Qq v)) L v L'' v = L'' := fun L L'' => Function.update_self v L'' L`. Use `⟨⟨?_, ?_⟩, h v hv i _ hC⟩` and prove the remaining obligations. Use `(Submodule.mem_iInf _).2 fun L => (Submodule.mem_iInf _).2 fun hL => ?_` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `Level.yv (P := G.P) v (x i) L ∈ G.P.sys (fun u => piLattice₂ G u (t u) (Function.update σ v Slot.dual u)) L`.

Rewrite using `[ef_yv_eq, Finset.smul_sum]`. Use `Submodule.sum_mem _ fun L'' hL'' => ?_` and prove the remaining obligations. Establish `hE : IsEdge p (G.P.n' v) G.P.r ⟨L'', L v⟩` using `(Set.Finite.mem_toFinset (ef_places_finite G.P v (L v))).1 hL''`. Establish `hlat : G.P.IsLatTup (Function.update (β` using `fun v => Submodule (G.P.W v) (Fin (G.P.m + 1) → G.P.Qq v)) L v L'') := by`. Introduce `u`.

Distinguish the cases in `huv : u = v`. Substitute `huv` using the available equality. Rewrite using `[hself]`. Conclude with `hE.1`. Rewrite using `[hne L L'' u huv]`.

Conclude with `hL u`. Establish `hval` using `hA' _ hlat`. Use `nt_tenV_smulK G v _ _ _ ?_ ?_ _ hval` and prove the remaining obligations. Introduce `z hz`. Rewrite `hz` using `[hself]`.

Establish `hz2 : z ∈ piLattice₂ G v (t v) (Function.update σ v Slot.ball v) L''` using `hz`. Rewrite `hz2` using `[Function.update_self]`. Use `show _ ∈ piLattice₂ G v (t v) (Function.update σ v Slot.dual v) (L v)`. Rewrite using `[Function.update_self]`. Conclude with `nt_local G v (t v) ⟨L'', L v⟩ hE z hz2`.

Introduce `u hu`. Rewrite using `[hne L L'' u hu]`. Use `show piLattice₂ G u (t u) (Function.update σ v Slot.ball u) (L u) ≤ piLattice₂ G u (t u) (Function.update σ v Slot.dual u) (L u)`. Rewrite using `[Function.update_of_ne hu, Function.update_of_ne hu]`. Use `(Submodule.mem_iInf _).2 fun L => (Submodule.mem_iInf _).2 fun hL => ?_` and prove the remaining obligations.

Express the relevant statement in the definitionally equal form `Level.yv (P := G.P) v (x i) L = 0`. Rewrite using `[ef_yv_eq, Finset.sum_eq_zero, smul_zero]`. Introduce `L'' hL''`. Establish `hE : IsEdge p (G.P.n' v) G.P.r ⟨L'', L v⟩` using `(Set.Finite.mem_toFinset (ef_places_finite G.P v (L v))).1 hL''`. Apply `hB'` to reduce the goal to its premises.

Introduce `hlat`. Apply `hL` to reduce the goal to its premises. Introduce `u`. Distinguish the cases in `huv : u = v`. Substitute `huv` using the available equality.

Conclude with `hE.2.1`. Use `hlat u` as an intermediate fact. Rewrite `this` using `[hne L L'' u huv]`. Conclude with `this`.
-/
theorem nt_nat (G : GAtP p) (VV : Finset (Fin G.P.nV)) (t : Fin G.P.nV → ℕ)
    (h : ∀ v ∈ VV, RestEquiv G v) : RestNat G VV t := by
  classical
  intro σ v hv x hx
  unfold latSys GAtP.funMod at hx ⊢
  rw [Submodule.mem_pi] at hx ⊢
  intro i hi
  have h0 := hx i hi
  unfold Level.funMod at h0 ⊢
  rw [Submodule.mem_inf, Submodule.mem_inf] at h0 ⊢
  obtain ⟨⟨hA, hB⟩, hC⟩ := h0
  have hA' := fun L hL => (Submodule.mem_iInf _).1 ((Submodule.mem_iInf _).1 hA L) hL
  have hB' : ∀ L : G.P.Tup, ¬ G.P.IsLatTup L → x i L = 0 :=
    fun L hL => (Submodule.mem_iInf _).1 ((Submodule.mem_iInf _).1 hB L) hL
  have hne : ∀ (L : G.P.Tup) (L'' : Submodule (G.P.W v) (Fin (G.P.m + 1) → G.P.Qq v)) (u : Fin G.P.nV),
      u ≠ v → Function.update (β := fun v => Submodule (G.P.W v) (Fin (G.P.m + 1) → G.P.Qq v)) L v L'' u = L u :=
    fun L L'' u hu => Function.update_of_ne hu L'' L
  have hself : ∀ (L : G.P.Tup) (L'' : Submodule (G.P.W v) (Fin (G.P.m + 1) → G.P.Qq v)),
      Function.update (β := fun v => Submodule (G.P.W v) (Fin (G.P.m + 1) → G.P.Qq v)) L v L'' v = L'' :=
    fun L L'' => Function.update_self v L'' L
  refine ⟨⟨?_, ?_⟩, h v hv i _ hC⟩
  · refine (Submodule.mem_iInf _).2 fun L => (Submodule.mem_iInf _).2 fun hL => ?_
    change Level.yv (P := G.P) v (x i) L ∈
      G.P.sys (fun u => piLattice₂ G u (t u) (Function.update σ v Slot.dual u)) L
    rw [ef_yv_eq, Finset.smul_sum]
    refine Submodule.sum_mem _ fun L'' hL'' => ?_
    have hE : IsEdge p (G.P.n' v) G.P.r ⟨L'', L v⟩ :=
      (Set.Finite.mem_toFinset (ef_places_finite G.P v (L v))).1 hL''
    have hlat : G.P.IsLatTup
        (Function.update (β := fun v => Submodule (G.P.W v) (Fin (G.P.m + 1) → G.P.Qq v)) L v L'') := by
      intro u
      by_cases huv : u = v
      · subst huv
        rw [hself]
        exact hE.1
      · rw [hne L L'' u huv]
        exact hL u
    have hval := hA' _ hlat
    refine nt_tenV_smulK G v _ _ _ ?_ ?_ _ hval
    · intro z hz
      rw [hself] at hz
      have hz2 : z ∈ piLattice₂ G v (t v) (Function.update σ v Slot.ball v) L'' := hz
      rw [Function.update_self] at hz2
      show _ ∈ piLattice₂ G v (t v) (Function.update σ v Slot.dual v) (L v)
      rw [Function.update_self]
      exact nt_local G v (t v) ⟨L'', L v⟩ hE z hz2
    · intro u hu
      rw [hne L L'' u hu]
      show piLattice₂ G u (t u) (Function.update σ v Slot.ball u) (L u) ≤
        piLattice₂ G u (t u) (Function.update σ v Slot.dual u) (L u)
      rw [Function.update_of_ne hu, Function.update_of_ne hu]
  · refine (Submodule.mem_iInf _).2 fun L => (Submodule.mem_iInf _).2 fun hL => ?_
    change Level.yv (P := G.P) v (x i) L = 0
    rw [ef_yv_eq, Finset.sum_eq_zero, smul_zero]
    intro L'' hL''
    have hE : IsEdge p (G.P.n' v) G.P.r ⟨L'', L v⟩ :=
      (Set.Finite.mem_toFinset (ef_places_finite G.P v (L v))).1 hL''
    apply hB'
    intro hlat
    apply hL
    intro u
    by_cases huv : u = v
    · subst huv
      exact hE.2.1
    · have := hlat u
      rw [hne L L'' u huv] at this
      exact this

section EdgeMap

variable {W Qq : Type} [CommRing W] [Field Qq] [Algebra W Qq] {k : ℕ}

def nt_phi (W : Type) {Qq : Type} [CommRing W] [Field Qq] [Algebra W Qq] {k : ℕ} (g : GL (Fin k) Qq) :
    (Fin k → Qq) →ₗ[W] (Fin k → Qq) :=
  (Matrix.mulVecLin (g : Matrix (Fin k) (Fin k) Qq)).restrictScalars W

/- English proof (translation)
Use `show Matrix.mulVec ((g⁻¹ : GL (Fin k) Qq) : Matrix (Fin k) (Fin k) Qq) (Matrix.mulVec (g : Matrix (Fin k) (Fin k) Qq) x) = x`. Rewrite using `[Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec]`.
-/
theorem nt_phi_inv (g : GL (Fin k) Qq) (x : Fin k → Qq) : nt_phi W g⁻¹ (nt_phi W g x) = x := by
  show Matrix.mulVec ((g⁻¹ : GL (Fin k) Qq) : Matrix (Fin k) (Fin k) Qq)
    (Matrix.mulVec (g : Matrix (Fin k) (Fin k) Qq) x) = x
  rw [Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec]

/- English proof (translation)
Use `show Matrix.mulVec (g : Matrix (Fin k) (Fin k) Qq) (Matrix.mulVec ((g⁻¹ : GL (Fin k) Qq) : Matrix (Fin k) (Fin k) Qq) x) = x`. Rewrite using `[Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mulVec]`.
-/
theorem nt_phi_inv' (g : GL (Fin k) Qq) (x : Fin k → Qq) : nt_phi W g (nt_phi W g⁻¹ x) = x := by
  show Matrix.mulVec (g : Matrix (Fin k) (Fin k) Qq)
    (Matrix.mulVec ((g⁻¹ : GL (Fin k) Qq) : Matrix (Fin k) (Fin k) Qq) x) = x
  rw [Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mulVec]

/- English proof (translation)
Rewrite using `[← Submodule.map_comp]`. Establish `: (nt_phi W g⁻¹) ∘ₗ (nt_phi W g) = LinearMap.id` using `LinearMap.ext fun x => nt_phi_inv g x`. Rewrite using `[this, Submodule.map_id]`.
-/
theorem nt_map_inv (g : GL (Fin k) Qq) (A : Submodule W (Fin k → Qq)) :
    (A.map (nt_phi W g)).map (nt_phi W g⁻¹) = A := by
  rw [← Submodule.map_comp]
  have : (nt_phi W g⁻¹) ∘ₗ (nt_phi W g) = LinearMap.id := LinearMap.ext fun x => nt_phi_inv g x
  rw [this, Submodule.map_id]

/- English proof (translation)
Rewrite using `[← Submodule.map_comp]`. Establish `: (nt_phi W g) ∘ₗ (nt_phi W g⁻¹) = LinearMap.id` using `LinearMap.ext fun x => nt_phi_inv' g x`. Rewrite using `[this, Submodule.map_id]`.
-/
theorem nt_map_inv' (g : GL (Fin k) Qq) (A : Submodule W (Fin k → Qq)) :
    (A.map (nt_phi W g⁻¹)).map (nt_phi W g) = A := by
  rw [← Submodule.map_comp]
  have : (nt_phi W g) ∘ₗ (nt_phi W g⁻¹) = LinearMap.id := LinearMap.ext fun x => nt_phi_inv' g x
  rw [this, Submodule.map_id]

def nt_equivLin (W : Type) {Qq : Type} [CommRing W] [Field Qq] [Algebra W Qq] {k : ℕ} (g : GL (Fin k) Qq) :
    (Fin k → Qq) ≃ₗ[W] (Fin k → Qq) :=
  LinearEquiv.ofLinearMap (nt_phi W g) (nt_phi W g⁻¹) (LinearMap.ext fun x => nt_phi_inv' g x)
    (LinearMap.ext fun x => nt_phi_inv g x)

/- English proof (translation)
Take `⟨h, hdet, rfl⟩` from `hA`. Use `⟨(g : Matrix (Fin k) (Fin k) Qq) * h, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[Matrix.det_mul]`. Conclude with `((Matrix.isUnit_iff_isUnit_det (g : Matrix (Fin k) (Fin k) Qq)).1 (Units.isUnit g)).mul hdet`. Unfold `colSpan`.

Rewrite using `[Submodule.map_span, ← Set.range_comp]`. Use `congr 2`.
-/
theorem nt_lat_map (g : GL (Fin k) Qq) (A : Submodule W (Fin k → Qq)) (hA : IsLattice W A) :
    IsLattice W (A.map (nt_phi W g)) := by
  obtain ⟨h, hdet, rfl⟩ := hA
  refine ⟨(g : Matrix (Fin k) (Fin k) Qq) * h, ?_, ?_⟩
  · rw [Matrix.det_mul]
    exact ((Matrix.isUnit_iff_isUnit_det (g : Matrix (Fin k) (Fin k) Qq)).1 (Units.isUnit g)).mul hdet
  · unfold colSpan
    rw [Submodule.map_span, ← Set.range_comp]
    congr 2

/- English proof (translation)
Take `⟨h1, h2, h3, h4, h5⟩` from `h`. Use `⟨nt_lat_map g A h1, nt_lat_map g B h2, Submodule.map_mono h3, ?_, ?_⟩` and prove the remaining obligations. Introduce and unpack `_ ⟨y, hy, rfl⟩`. Conclude with `⟨(p : W) • y, h4 y hy, map_smul _ _ _⟩`. Rewrite using `[← h5]`.

Establish `hf : (Submodule.comap B.subtype A).map ((nt_equivLin W g).submoduleMap B : ↥B →ₗ[W] _) = Submodule.comap (B.map (nt_equivLin W g : (Fin k → Qq) →ₗ[W] (Fin k → Qq))).subtype (A.map (nt_phi W g))`. Use extensionality with `⟨y, hy⟩`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨⟨x, hxB⟩, hxA, hxy⟩`. Conclude with `⟨x, hxA, congrArg Subtype.val hxy⟩`.

Introduce and unpack `⟨a, ha, hay⟩`. Conclude with `⟨⟨a, h3 ha⟩, ha, Subtype.ext hay⟩`. Conclude with `(Nat.card_congr (Submodule.Quotient.equiv _ _ ((nt_equivLin W g).submoduleMap B) hf).toEquiv).symm`.
-/
theorem nt_edge_map (p n' r : ℕ) (g : GL (Fin k) Qq) (A B : Submodule W (Fin k → Qq))
    (h : IsEdge p n' r ⟨A, B⟩) : IsEdge p n' r ⟨A.map (nt_phi W g), B.map (nt_phi W g)⟩ := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  refine ⟨nt_lat_map g A h1, nt_lat_map g B h2, Submodule.map_mono h3, ?_, ?_⟩
  · rintro _ ⟨y, hy, rfl⟩
    exact ⟨(p : W) • y, h4 y hy, map_smul _ _ _⟩
  · rw [← h5]
    have hf : (Submodule.comap B.subtype A).map ((nt_equivLin W g).submoduleMap B : ↥B →ₗ[W] _) =
        Submodule.comap (B.map (nt_equivLin W g : (Fin k → Qq) →ₗ[W] (Fin k → Qq))).subtype
          (A.map (nt_phi W g)) := by
      ext ⟨y, hy⟩
      constructor
      · rintro ⟨⟨x, hxB⟩, hxA, hxy⟩
        exact ⟨x, hxA, congrArg Subtype.val hxy⟩
      · rintro ⟨a, ha, hay⟩
        exact ⟨⟨a, h3 ha⟩, ha, Subtype.ext hay⟩
    exact (Nat.card_congr (Submodule.Quotient.equiv _ _ ((nt_equivLin W g).submoduleMap B) hf).toEquiv).symm

end EdgeMap

/- English proof (translation)
Use function extensionality and compare the values at `u`. Distinguish the cases in `huv : u = v`. Substitute `huv` using the available equality. Establish `e1 : Function.update (β` using `fun v => Submodule (G.P.W v) (Fin (G.P.m + 1) → G.P.Qq v)) L u A u = A := Function.update_self u A L`. Establish `e2 : Function.update (β` using `fun v => Submodule (G.P.W v) (Fin (G.P.m + 1) → G.P.Qq v)) ((G.lev i).smul γ L) u (A.map (nt_phi (G.P.W u) ((G.lev i).act u γ))) u = A.map (nt_phi (G.P.W u) ((G.lev i).act u γ)) := Function.update_self u _ _`.

Conclude with `(congrArg (fun Z => Submodule.map (nt_phi (G.P.W u) ((G.lev i).act u γ)) Z) e1).trans e2.symm`. Establish `e1 : Function.update (β` using `fun v => Submodule (G.P.W v) (Fin (G.P.m + 1) → G.P.Qq v)) L v A u = L u := Function.update_of_ne huv A L`. Establish `e2 : Function.update (β` using `fun v => Submodule (G.P.W v) (Fin (G.P.m + 1) → G.P.Qq v)) ((G.lev i).smul γ L) v (A.map (nt_phi (G.P.W v) ((G.lev i).act v γ))) u = (G.lev i).smul γ L u := Function.update_of_ne huv _ _`. Conclude with `(congrArg (fun Z => Submodule.map (nt_phi (G.P.W u) ((G.lev i).act u γ)) Z) e1).trans e2.symm`.
-/
theorem nt_smul_update (G : GAtP p) (i : G.comp) (γ : (G.lev i).Γ) (v : Fin G.P.nV) (L : G.P.Tup)
    (A : Submodule (G.P.W v) (Fin (G.P.m + 1) → G.P.Qq v)) :
    (G.lev i).smul γ
      (Function.update (β := fun v => Submodule (G.P.W v) (Fin (G.P.m + 1) → G.P.Qq v)) L v A) =
    Function.update (β := fun v => Submodule (G.P.W v) (Fin (G.P.m + 1) → G.P.Qq v)) ((G.lev i).smul γ L) v
      (A.map (nt_phi (G.P.W v) ((G.lev i).act v γ))) := by
  funext u
  by_cases huv : u = v
  · subst huv
    have e1 : Function.update (β := fun v => Submodule (G.P.W v) (Fin (G.P.m + 1) → G.P.Qq v)) L u A u = A :=
      Function.update_self u A L
    have e2 : Function.update (β := fun v => Submodule (G.P.W v) (Fin (G.P.m + 1) → G.P.Qq v))
        ((G.lev i).smul γ L) u (A.map (nt_phi (G.P.W u) ((G.lev i).act u γ))) u =
        A.map (nt_phi (G.P.W u) ((G.lev i).act u γ)) := Function.update_self u _ _
    exact (congrArg (fun Z => Submodule.map (nt_phi (G.P.W u) ((G.lev i).act u γ)) Z) e1).trans e2.symm
  · have e1 : Function.update (β := fun v => Submodule (G.P.W v) (Fin (G.P.m + 1) → G.P.Qq v)) L v A u = L u :=
      Function.update_of_ne huv A L
    have e2 : Function.update (β := fun v => Submodule (G.P.W v) (Fin (G.P.m + 1) → G.P.Qq v))
        ((G.lev i).smul γ L) v (A.map (nt_phi (G.P.W v) ((G.lev i).act v γ))) u =
        (G.lev i).smul γ L u := Function.update_of_ne huv _ _
    exact (congrArg (fun Z => Submodule.map (nt_phi (G.P.W u) ((G.lev i).act u γ)) Z) e1).trans e2.symm

/- English proof (translation)
Introduce `i F hF`. Establish `hF' : ∀ (γ : (G.lev i).Γ) (L : G.P.Tup), F ((G.lev i).smul γ L) = ((G.lev i).χ γ : G.O) • (G.lev i).actX γ (F L)`. Introduce `γ L`. Establish `h1` using `(Submodule.mem_iInf _).1 ((Submodule.mem_iInf _).1 hF γ) L`. Rewrite `h1` using `[LinearMap.mem_ker]`.

Conclude with `sub_eq_zero.1 h1`. Use `(Submodule.mem_iInf _).2 fun γ => (Submodule.mem_iInf _).2 fun L => ?_` and prove the remaining obligations. Rewrite using `[LinearMap.mem_ker]`. Use `show Level.yv (P := G.P) v F ((G.lev i).smul γ L) - ((G.lev i).χ γ : G.O) • (G.lev i).actX γ (Level.yv (P := G.P) v F L) = 0`. Establish `hsum : ∑ A ∈ ef_E G.P v (L v), ((G.lev i).χ γ : G.O) • (G.lev i).actX γ (F (Function.update (β` using `fun v => Submodule (G.P.W v) (Fin (G.P.m + 1) → G.P.Qq v)) L v A)) = ∑ B ∈ ef_E G.P v ((G.lev i).smul γ L v), F (Function.update (β := fun v => Submodule (G.P.W v) (Fin (G.P.m + 1) → G.P.Qq v)) ((G.lev i).smul γ L) v B) := by`.

Use `Finset.sum_bij (fun (A : Submodule (G.P.W v) (Fin (G.P.m + 1) → G.P.Qq v)) _ => A.map (nt_phi (G.P.W v) ((G.lev i).act v γ))) ?_ ?_ ?_ ?_` and prove the remaining obligations. Introduce `A hA`. Establish `hE : IsEdge p (G.P.n' v) G.P.r ⟨A, L v⟩` using `(Set.Finite.mem_toFinset (ef_places_finite G.P v (L v))).1 hA`. Conclude with `(Set.Finite.mem_toFinset (ef_places_finite G.P v _)).2 (nt_edge_map p (G.P.n' v) G.P.r ((G.lev i).act v γ) A (L v) hE)`. Introduce `A _ A' _ hAA`.

Use `congrArg (fun X => Submodule.map (nt_phi (G.P.W v) ((G.lev i).act v γ)⁻¹) X) hAA` as an intermediate fact. Simplify `this` using `only [nt_map_inv]`. Introduce `B hB`. Establish `hE : IsEdge p (G.P.n' v) G.P.r ⟨B, (L v).map (nt_phi (G.P.W v) ((G.lev i).act v γ))⟩` using `(Set.Finite.mem_toFinset (ef_places_finite G.P v _)).1 hB`. Establish `hE2` using `nt_edge_map p (G.P.n' v) G.P.r ((G.lev i).act v γ)⁻¹ _ _ hE`.

Rewrite `hE2` using `[nt_map_inv]`. Conclude with `⟨B.map (nt_phi (G.P.W v) ((G.lev i).act v γ)⁻¹), (Set.Finite.mem_toFinset (ef_places_finite G.P v (L v))).2 hE2, nt_map_inv' _ _⟩`. Introduce `A _`. Conclude with `(hF' γ _).symm.trans (congrArg F (nt_smul_update G i γ v L A))`. Rewrite using `[sub_eq_zero]`.

Combine the equalities or inequalities in the displayed calculation. Rewrite using `[map_smul, map_sum]`. Simplify using `only [Finset.smul_sum]`. Apply `Finset.sum_congr rfl` to reduce the goal to its premises. Introduce `A _`.

Rewrite using `[smul_comm]`. Use `_ = ((G.lev i).χ γ : G.O) • (G.lev i).actX γ (Level.yv (P := G.P) v F L) := by`. Rewrite using `[ef_yv_eq]`.
-/
theorem nt_equiv (G : GAtP p) (v : Fin G.P.nV) : RestEquiv G v := by
  classical
  intro i F hF
  have hF' : ∀ (γ : (G.lev i).Γ) (L : G.P.Tup),
      F ((G.lev i).smul γ L) = ((G.lev i).χ γ : G.O) • (G.lev i).actX γ (F L) := by
    intro γ L
    have h1 := (Submodule.mem_iInf _).1 ((Submodule.mem_iInf _).1 hF γ) L
    rw [LinearMap.mem_ker] at h1
    exact sub_eq_zero.1 h1
  refine (Submodule.mem_iInf _).2 fun γ => (Submodule.mem_iInf _).2 fun L => ?_
  rw [LinearMap.mem_ker]
  show Level.yv (P := G.P) v F ((G.lev i).smul γ L) -
    ((G.lev i).χ γ : G.O) • (G.lev i).actX γ (Level.yv (P := G.P) v F L) = 0
  have hsum : ∑ A ∈ ef_E G.P v (L v), ((G.lev i).χ γ : G.O) • (G.lev i).actX γ (F (Function.update (β := fun v => Submodule (G.P.W v) (Fin (G.P.m + 1) → G.P.Qq v)) L v A)) =
      ∑ B ∈ ef_E G.P v ((G.lev i).smul γ L v), F (Function.update (β := fun v => Submodule (G.P.W v) (Fin (G.P.m + 1) → G.P.Qq v)) ((G.lev i).smul γ L) v B) := by
    refine Finset.sum_bij (fun (A : Submodule (G.P.W v) (Fin (G.P.m + 1) → G.P.Qq v)) _ =>
      A.map (nt_phi (G.P.W v) ((G.lev i).act v γ))) ?_ ?_ ?_ ?_
    · intro A hA
      have hE : IsEdge p (G.P.n' v) G.P.r ⟨A, L v⟩ :=
        (Set.Finite.mem_toFinset (ef_places_finite G.P v (L v))).1 hA
      exact (Set.Finite.mem_toFinset (ef_places_finite G.P v _)).2
        (nt_edge_map p (G.P.n' v) G.P.r ((G.lev i).act v γ) A (L v) hE)
    · intro A _ A' _ hAA
      have := congrArg (fun X => Submodule.map (nt_phi (G.P.W v) ((G.lev i).act v γ)⁻¹) X) hAA
      simpa only [nt_map_inv] using this
    · intro B hB
      have hE : IsEdge p (G.P.n' v) G.P.r ⟨B, (L v).map (nt_phi (G.P.W v) ((G.lev i).act v γ))⟩ :=
        (Set.Finite.mem_toFinset (ef_places_finite G.P v _)).1 hB
      have hE2 := nt_edge_map p (G.P.n' v) G.P.r ((G.lev i).act v γ)⁻¹ _ _ hE
      rw [nt_map_inv] at hE2
      exact ⟨B.map (nt_phi (G.P.W v) ((G.lev i).act v γ)⁻¹),
        (Set.Finite.mem_toFinset (ef_places_finite G.P v (L v))).2 hE2, nt_map_inv' _ _⟩
    · intro A _
      exact (hF' γ _).symm.trans (congrArg F (nt_smul_update G i γ v L A))
  rw [sub_eq_zero]
  calc Level.yv (P := G.P) v F ((G.lev i).smul γ L)
      = ((p : G.Kf) ^ G.P.ArV v) •
          ∑ B ∈ ef_E G.P v ((G.lev i).smul γ L v), F (Function.update (β := fun v => Submodule (G.P.W v) (Fin (G.P.m + 1) → G.P.Qq v)) ((G.lev i).smul γ L) v B) :=
        ef_yv_eq G.P v F _
    _ = ((p : G.Kf) ^ G.P.ArV v) • ∑ A ∈ ef_E G.P v (L v),
          ((G.lev i).χ γ : G.O) • (G.lev i).actX γ (F (Function.update (β := fun v => Submodule (G.P.W v) (Fin (G.P.m + 1) → G.P.Qq v)) L v A)) :=
        congrArg (fun s => ((p : G.Kf) ^ G.P.ArV v) • s) hsum.symm
    _ = ((G.lev i).χ γ : G.O) • (G.lev i).actX γ (((p : G.Kf) ^ G.P.ArV v) •
          ∑ A ∈ ef_E G.P v (L v), F (Function.update (β := fun v => Submodule (G.P.W v) (Fin (G.P.m + 1) → G.P.Qq v)) L v A)) := by
        rw [map_smul, map_sum]
        simp only [Finset.smul_sum]
        apply Finset.sum_congr rfl
        intro A _
        rw [smul_comm]
    _ = ((G.lev i).χ γ : G.O) • (G.lev i).actX γ (Level.yv (P := G.P) v F L) := by
        rw [ef_yv_eq]

/- English proof (translation)
The claim follows from `nt_nat G VV t fun v _ => nt_equiv G v`.
-/
theorem restNat_proved (G : GAtP p) (VV : Finset (Fin G.P.nV)) (t : Fin G.P.nV → ℕ) : RestNat G VV t :=
  nt_nat G VV t fun v _ => nt_equiv G v

/- English proof (translation)
The claim follows from `restWalk_of_local G VV t Dd κ h1 (restNat_proved G VV t) h3`.
-/
theorem restWalk_of_local_J (G : GAtP p) (VV : Finset (Fin G.P.nV)) (t : Fin G.P.nV → ℕ) (Dd : ℕ)
    (κ : Fin G.P.nV → ℝ) (h1 : ∀ v ∈ VV, RestLocD G v) (h3 : RestJ G VV t Dd κ) : RestWalk G VV t Dd κ :=
  restWalk_of_local G VV t Dd κ h1 (restNat_proved G VV t) h3

end Formalism.MainNotions.G.LatticeSystems

namespace Formalism.MainNotions.G.LatticeSystems

open Formalism.MainNotions.G Formalism.GradedWeylDivisibility MvPolynomial

def la_tw {Qq Kf : Type} [Field Qq] [Field Kf] (ι : Qq →+* Kf) (σ : Qq ≃+* Qq) (s : ℕ) {k : ℕ}
    (g : Matrix (Fin k) (Fin k) Qq) : Matrix (Fin k) (Fin k) Kf :=
  (ι.comp ((σ ^ s : Qq ≃+* Qq) : Qq →+* Qq)).mapMatrix g

/- English proof (translation)
Unfold `la_tw`. Rewrite using `[← RingHom.map_det]`. Conclude with `hg.map _`.
-/
theorem la_tw_det {Qq Kf : Type} [Field Qq] [Field Kf] (ι : Qq →+* Kf) (σ : Qq ≃+* Qq) (s : ℕ) {k : ℕ}
    (g : Matrix (Fin k) (Fin k) Qq) (hg : IsUnit g.det) : IsUnit (la_tw ι σ s g).det := by
  unfold la_tw
  rw [← RingHom.map_det]
  exact hg.map _

/- English proof (translation)
Proceed by induction on `s with`. Consider the case `zero => exact ⟨x, by simp⟩`. Consider the case `succ n ih`. Take `⟨y, hy⟩` from `ih`. Take `⟨z, hz⟩` from `hσ y`.

Use `⟨z, ?_⟩` and prove the remaining obligations. Rewrite using `[pow_succ', RingAut.mul_apply, hy, hz]`.
-/
theorem la_sigma_pow {W Qq : Type} [CommRing W] [Field Qq] [Algebra W Qq] (σ : Qq ≃+* Qq)
    (hσ : ∀ x : W, ∃ y : W, σ (algebraMap W Qq x) = algebraMap W Qq y) (s : ℕ) (x : W) :
    ∃ y : W, (σ ^ s) (algebraMap W Qq x) = algebraMap W Qq y := by
  induction s with
  | zero => exact ⟨x, by simp⟩
  | succ n ih =>
    obtain ⟨y, hy⟩ := ih
    obtain ⟨z, hz⟩ := hσ y
    refine ⟨z, ?_⟩
    rw [pow_succ', RingAut.mul_apply, hy, hz]

/- English proof (translation)
Apply `le_antisymm` to reduce the goal to its premises. Unfold `extO`. Rewrite using `[Submodule.span_le]`. Introduce and unpack `_ ⟨x, hx, rfl⟩`. Express the relevant statement in the definitionally equal form `x ∈ Submodule.span W _ at hx`.

Proceed by induction on `hx using Submodule.span_induction with`. Consider the case `mem x hx`. Take `⟨c, rfl⟩` from `hx`. Conclude with `Submodule.subset_span ⟨c, rfl⟩`. Consider the case `zero`.

Establish `: twistVec ι σ s (0 : Fin k → Qq) = 0` using `by funext i; simp [twistVec]`. Rewrite using `[this]`. Conclude with `Submodule.zero_mem _`. Consider the case `add x y _ _ hx hy`. Establish `: twistVec ι σ s (x + y) = twistVec ι σ s x + twistVec ι σ s y`.

Use function extensionality and compare the values at `i`. Simplify using `[twistVec]`. Rewrite using `[this]`. Conclude with `Submodule.add_mem _ hx hy`. Consider the case `smul a x _ hx`.

Take `⟨a', ha'⟩` from `la_sigma_pow σ hσ s a`. Establish `: twistVec ι σ s (a • x) = (j a') • twistVec ι σ s x`. Use function extensionality and compare the values at `i`. Simplify using `only [twistVec, Pi.smul_apply, Algebra.smul_def, map_mul, ha', hι]`. Rewrite using `[this]`.

Conclude with `Submodule.smul_mem _ _ hx`. Unfold `colSpan`. Rewrite using `[Submodule.span_le]`. Introduce and unpack `_ ⟨c, rfl⟩`. Conclude with `Submodule.subset_span ⟨fun i => g i c, Submodule.subset_span ⟨c, rfl⟩, rfl⟩`.
-/
theorem la_extO {W Qq O Kf : Type} [CommRing W] [Field Qq] [Algebra W Qq] [CommRing O] [Field Kf]
    [Algebra O Kf] (ι : Qq →+* Kf) (σ : Qq ≃+* Qq) (j : W →+* O)
    (hσ : ∀ x : W, ∃ y : W, σ (algebraMap W Qq x) = algebraMap W Qq y)
    (hι : ∀ x : W, ι (algebraMap W Qq x) = algebraMap O Kf (j x)) (s : ℕ) {k : ℕ}
    (g : Matrix (Fin k) (Fin k) Qq) :
    extO O ι σ s (colSpan W g) = colSpan O (la_tw ι σ s g) := by
  apply le_antisymm
  · unfold extO
    rw [Submodule.span_le]
    rintro _ ⟨x, hx, rfl⟩
    change x ∈ Submodule.span W _ at hx
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨c, rfl⟩ := hx
      exact Submodule.subset_span ⟨c, rfl⟩
    | zero =>
      have : twistVec ι σ s (0 : Fin k → Qq) = 0 := by funext i; simp [twistVec]
      rw [this]; exact Submodule.zero_mem _
    | add x y _ _ hx hy =>
      have : twistVec ι σ s (x + y) = twistVec ι σ s x + twistVec ι σ s y := by
        funext i; simp [twistVec]
      rw [this]; exact Submodule.add_mem _ hx hy
    | smul a x _ hx =>
      obtain ⟨a', ha'⟩ := la_sigma_pow σ hσ s a
      have : twistVec ι σ s (a • x) = (j a') • twistVec ι σ s x := by
        funext i
        simp only [twistVec, Pi.smul_apply, Algebra.smul_def, map_mul, ha', hι]
      rw [this]; exact Submodule.smul_mem _ _ hx
  · unfold colSpan
    rw [Submodule.span_le]
    rintro _ ⟨c, rfl⟩
    exact Submodule.subset_span ⟨fun i => g i c, Submodule.subset_span ⟨c, rfl⟩, rfl⟩

/- English proof (translation)
Unfold `H0`. Rewrite using `[if_pos hlam]`. Conclude with `iInf₂_le g ⟨hg, rfl⟩`.
-/
theorem H0_le_twisted_nabla {O Kf : Type} [CommRing O] [Field Kf] [Algebra O Kf] (m : ℕ) (lam : Fin (m + 1) → ℤ)
    (hlam : Antitone lam) (g : Matrix (Fin (m + 1)) (Fin (m + 1)) Kf) (hg : IsUnit g.det) :
    H0 O m lam (colSpan O g) ≤ nablaLTw O Kf m lam g := by
  unfold H0
  rw [if_pos hlam]
  exact iInf₂_le g ⟨hg, rfl⟩

/- English proof (translation)
Take `⟨F', hF', rfl⟩` from `hF`. Conclude with `Submodule.smul_mem _ _ (nablaLLe O Kf (m + 1) (m + 1) _ g hg F' hF')`.
-/
theorem la_nablaLTw_le {O Kf : Type} [CommRing O] [Field Kf] [Algebra O Kf] (m : ℕ) (lam : Fin (m + 1) → ℤ)
    (g : Matrix (Fin (m + 1)) (Fin (m + 1)) Kf) (hg : IsUnit g.det)
    (F : MvPolynomial (Fin (m + 1) × Fin (m + 1)) Kf) (hF : F ∈ nablaLTw O Kf m lam g) :
    F ∈ dualWeyl Kf (m + 1) (m + 1) (nuOf lam) := by
  obtain ⟨F', hF', rfl⟩ := hF
  exact Submodule.smul_mem _ _ (nablaLLe O Kf (m + 1) (m + 1) _ g hg F' hF')

variable {p : ℕ}

/- English proof (translation)
Take `⟨y, hy⟩` from `(G.P.setting v).frob x`. Conclude with `⟨_, hy⟩`.
-/
theorem la_frob (G : GAtP p) (v : Fin G.P.nV) (x : G.P.W v) :
    ∃ y : G.P.W v, G.P.σ v (algebraMap (G.P.W v) (G.P.Qq v) x) = algebraMap (G.P.W v) (G.P.Qq v) y := by
  obtain ⟨y, hy⟩ := (G.P.setting v).frob x
  exact ⟨_, hy⟩

/- English proof (translation)
The claim follows from `la_extO (G.P.ι v) (G.P.σ v) (G.P.j v) (la_frob G v) (G.P.setting v).ι_comp s g`.
-/
theorem la_extO_G (G : GAtP p) (v : Fin G.P.nV) (s : ℕ) (g : Matrix (Fin (G.P.m + 1)) (Fin (G.P.m + 1)) (G.P.Qq v)) :
    extO G.O (G.P.ι v) (G.P.σ v) s (colSpan (G.P.W v) g) = colSpan G.O (la_tw (G.P.ι v) (G.P.σ v) s g) :=
  la_extO (G.P.ι v) (G.P.σ v) (G.P.j v) (la_frob G v) (G.P.setting v).ι_comp s g

/- English proof (translation)
Take `⟨g, hg, rfl⟩` from `hLv`. Establish `hle : Hten G.O (G.P.lam0 v) (fun s => extO G.O (G.P.ι v) (G.P.σ v) s.val (colSpan (G.P.W v) g)) ≤ (Vsp G.Kf (G.P.lam0 v)).restrictScalars G.O`. Unfold `Hten tensorLat`. Rewrite using `[Submodule.span_le]`. Introduce and unpack `_ ⟨F, hF, rfl⟩`.

Apply `Submodule.subset_span` to reduce the goal to its premises. Use `⟨F, fun s => ?_, rfl⟩` and prove the remaining obligations. Establish `hanti` using `kp_lamAt_antitone (G.P.lam0 v) (G.P.dom v) s`. Use `beta_reduce`. Rewrite using `[if_pos hanti]`.

Establish `h1` using `hF s`. Use `beta_reduce at h1`. Rewrite `h1` using `[la_extO_G]`. Conclude with `la_nablaLTw_le _ _ _ (la_tw_det _ _ _ g hg) _ (H0_le_twisted_nabla _ _ hanti _ (la_tw_det _ _ _ g hg) h1)`. Conclude with `fun z hz => hle hz`.
-/
theorem la_H_le_V (G : GAtP p) (v : Fin G.P.nV) (Lv : Submodule (G.P.W v) (Fin (G.P.m + 1) → G.P.Qq v))
    (hLv : IsLattice (G.P.W v) Lv) :
    ∀ z ∈ Hten G.O (G.P.lam0 v) (fun s => extO G.O (G.P.ι v) (G.P.σ v) s.val Lv), z ∈ Vsp G.Kf (G.P.lam0 v) := by
  obtain ⟨g, hg, rfl⟩ := hLv
  have hle : Hten G.O (G.P.lam0 v) (fun s => extO G.O (G.P.ι v) (G.P.σ v) s.val (colSpan (G.P.W v) g)) ≤
      (Vsp G.Kf (G.P.lam0 v)).restrictScalars G.O := by
    unfold Hten tensorLat
    rw [Submodule.span_le]
    rintro _ ⟨F, hF, rfl⟩
    apply Submodule.subset_span
    refine ⟨F, fun s => ?_, rfl⟩
    have hanti := kp_lamAt_antitone (G.P.lam0 v) (G.P.dom v) s
    beta_reduce
    rw [if_pos hanti]
    have h1 := hF s
    beta_reduce at h1
    rw [la_extO_G] at h1
    exact la_nablaLTw_le _ _ _ (la_tw_det _ _ _ g hg) _ (H0_le_twisted_nabla _ _ hanti _ (la_tw_det _ _ _ g hg) h1)
  exact fun z hz => hle hz

/- English proof (translation)
Consider the cases of `nonempty_fintype I`. Introduce `x hx`. Establish `hc : ∀ i, b.coord i ∈ dualLat O Kf (Submodule.span O (Set.range b))`. Introduce `i`. Express the relevant statement in the definitionally equal form `∀ y ∈ Submodule.span O (Set.range b), b.coord i y ∈ Set.range (algebraMap O Kf)`.

Introduce `y hy`. Proceed by induction on `hy using Submodule.span_induction with`. Consider the case `mem y hy`. Take `⟨j, rfl⟩` from `hy`. Distinguish the cases in `h : j = i`.

Substitute `h; exact ⟨1, by simp⟩` using the available equality. Conclude with `⟨0, by simp [h]⟩`. Consider the case `zero => exact ⟨0, by simp⟩`. Consider the case `add y z _ _ hy hz`. Take `⟨a, ha⟩` from `hy`.

Take `⟨c, hc⟩` from `hz`. Conclude with `⟨a + c, by simp [ha, hc]⟩`. Consider the case `smul a y _ hy`. Take `⟨c, hc⟩` from `hy`. Conclude with `⟨a * c, by rw [map_mul, hc, ← Algebra.smul_def, LinearMap.map_smul_of_tower]⟩`.

Rewrite using `[← b.sum_repr x]`. Use `Submodule.sum_mem _ fun i _ => ?_` and prove the remaining obligations. Take `⟨a, ha⟩` from `hx (b.coord i) (hc i)`. Establish `h2 : b.repr x i = algebraMap O Kf a` using `by rw [ha]; rfl`. Rewrite using `[h2, algebraMap_smul]`.

Conclude with `Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)`.
-/
theorem la_refl_basis {O Kf V : Type} [CommRing O] [Field Kf] [Algebra O Kf] [AddCommGroup V] [Module Kf V]
    [Module O V] [IsScalarTower O Kf V] {I : Type} [Finite I] (b : Module.Basis I Kf V) :
    predual (dualLat O Kf (Submodule.span O (Set.range b))) ≤ Submodule.span O (Set.range b) := by
  classical
  cases nonempty_fintype I
  intro x hx
  have hc : ∀ i, b.coord i ∈ dualLat O Kf (Submodule.span O (Set.range b)) := by
    intro i
    change ∀ y ∈ Submodule.span O (Set.range b), b.coord i y ∈ Set.range (algebraMap O Kf)
    intro y hy
    induction hy using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨j, rfl⟩ := hy
      by_cases h : j = i
      · subst h; exact ⟨1, by simp⟩
      · exact ⟨0, by simp [h]⟩
    | zero => exact ⟨0, by simp⟩
    | add y z _ _ hy hz =>
      obtain ⟨a, ha⟩ := hy
      obtain ⟨c, hc⟩ := hz
      exact ⟨a + c, by simp [ha, hc]⟩
    | smul a y _ hy =>
      obtain ⟨c, hc⟩ := hy
      exact ⟨a * c, by rw [map_mul, hc, ← Algebra.smul_def, LinearMap.map_smul_of_tower]⟩
  rw [← b.sum_repr x]
  refine Submodule.sum_mem _ fun i _ => ?_
  obtain ⟨a, ha⟩ := hx (b.coord i) (hc i)
  have h2 : b.repr x i = algebraMap O Kf a := by rw [ha]; rfl
  rw [h2, algebraMap_smul]
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)

/- English proof (translation)
Substitute `hsp` using the available equality. Substitute `hA` using the available equality. Establish `hb : (Submodule.span O (Set.range P)).comap ((Submodule.span Kf (Set.range P)).subtype.restrictScalars O) = Submodule.span O (Set.range (Module.Basis.span hli))`. Establish `h1 : (Submodule.span O (Set.range (Module.Basis.span hli))).map ((Submodule.span Kf (Set.range P)).subtype.restrictScalars O) = Submodule.span O (Set.range P)`. Rewrite using `[Submodule.map_span, ← Set.range_comp]`.

Use `congr 2`. Use function extensionality and compare the values at `i`. Conclude with `congrArg Subtype.val (Module.Basis.span_apply hli i)`. Rewrite using `[← h1, Submodule.comap_map_eq_of_injective]`. Conclude with `Subtype.val_injective`.

Rewrite using `[hb]`. Conclude with `la_refl_basis _`.
-/
theorem la_refl_sub {O Kf X : Type} [CommRing O] [Field Kf] [Algebra O Kf] [AddCommGroup X] [Module Kf X]
    [Module O X] [IsScalarTower O Kf X] {I : Type} [Finite I] (P : I → X) (hli : LinearIndependent Kf P)
    (Vs : Submodule Kf X) (hsp : Submodule.span Kf (Set.range P) = Vs)
    (A : Submodule O X) (hA : Submodule.span O (Set.range P) = A) :
    predual (dualLat O Kf (A.comap (Vs.subtype.restrictScalars O))) ≤
      A.comap (Vs.subtype.restrictScalars O) := by
  subst hsp
  subst hA
  have hb : (Submodule.span O (Set.range P)).comap
      ((Submodule.span Kf (Set.range P)).subtype.restrictScalars O) =
      Submodule.span O (Set.range (Module.Basis.span hli)) := by
    have h1 : (Submodule.span O (Set.range (Module.Basis.span hli))).map
        ((Submodule.span Kf (Set.range P)).subtype.restrictScalars O) = Submodule.span O (Set.range P) := by
      rw [Submodule.map_span, ← Set.range_comp]
      congr 2
      funext i
      exact congrArg Subtype.val (Module.Basis.span_apply hli i)
    rw [← h1, Submodule.comap_map_eq_of_injective]
    exact Subtype.val_injective
  rw [hb]
  exact la_refl_basis _

def H0IndepOfBasis (O Kf : Type) [CommRing O] [Field Kf] [Algebra O Kf] : Prop :=
  ∀ (m : ℕ) (lam : Fin (m + 1) → ℤ) (g h : Matrix (Fin (m + 1)) (Fin (m + 1)) Kf), IsUnit g.det → IsUnit h.det →
    colSpan O g = colSpan O h → nablaLTw O Kf m lam g ≤ nablaLTw O Kf m lam h

/- English proof (translation)
Apply `le_antisymm (H0_le_twisted_nabla m lam hlam g hg)` to reduce the goal to its premises. Unfold `H0`. Rewrite using `[if_pos hlam]`. Conclude with `le_iInf₂ fun h hh => hI m lam g h hg hh.1 hh.2`.
-/
theorem H0_eq_twisted_nabla {O Kf : Type} [CommRing O] [Field Kf] [Algebra O Kf] (hI : H0IndepOfBasis O Kf) (m : ℕ)
    (lam : Fin (m + 1) → ℤ) (hlam : Antitone lam) (g : Matrix (Fin (m + 1)) (Fin (m + 1)) Kf)
    (hg : IsUnit g.det) : H0 O m lam (colSpan O g) = nablaLTw O Kf m lam g := by
  apply le_antisymm (H0_le_twisted_nabla m lam hlam g hg)
  unfold H0
  rw [if_pos hlam]
  exact le_iInf₂ fun h hh => hI m lam g h hg hh.1 hh.2

/- English proof (translation)
Take `⟨b, hb, -⟩` from `sSBasis O (m + 1) (m + 1) (nuOf lam)`. Take `⟨o1, o2⟩` from `nablaLBasis O Kf hinj (m + 1) (m + 1) (nuOf lam) b _ hb g hg`. Take `⟨k1, k2⟩` from `nablaLKBasis O Kf hinj (m + 1) (m + 1) (nuOf lam) b _ hb g hg`. Establish `hc : g.det ^ (-(lam (Fin.last m))) ≠ 0` using `zpow_ne_zero _ hg.ne_zero`. Use `set T : MvPolynomial (Fin (m + 1) × Fin (m + 1)) Kf →ₗ[Kf] MvPolynomial (Fin (m + 1) × Fin (m + 1)) Kf := LinearMap.lsmul Kf _ (g.det ^ (-(lam (Fin.last m)))) with hT`.

Establish `hTinj : Function.Injective T` using `fun x y hxy => smul_right_injective _ hc hxy`. Use `⟨fun i => T (rowAct Kf g⁻¹ (map (algebraMap O Kf) (b i))), ?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Conclude with `o1.map' (T.restrictScalars O) (LinearMap.ker_eq_bot.2 hTinj)`. Establish `: (Set.range fun i => T (rowAct Kf g⁻¹ (map (algebraMap O Kf) (b i)))) = (T.restrictScalars O) '' (Set.range fun i => rowAct Kf g⁻¹ (map (algebraMap O Kf) (b i)))`. Rewrite using `[← Set.range_comp]`.

Both sides reduce to the same expression. Rewrite using `[this, ← Submodule.map_span, o2]`. Both sides reduce to the same expression. Conclude with `k1.map' T (LinearMap.ker_eq_bot.2 hTinj)`. Establish `: (Set.range fun i => T (rowAct Kf g⁻¹ (map (algebraMap O Kf) (b i)))) = T '' (Set.range fun i => rowAct Kf g⁻¹ (map (algebraMap O Kf) (b i)))`.

Rewrite using `[← Set.range_comp]`. Both sides reduce to the same expression. Rewrite using `[this, ← Submodule.map_span, k2]`. Establish `hT2 : T = (g.det ^ (-(lam (Fin.last m)))) • LinearMap.id`. Use extensionality with `x`.

Simplify using `[hT]`. Rewrite using `[hT2, Submodule.map_smul _ _ _ hc, Submodule.map_id]`.
-/
theorem la_basis {O Kf : Type} [CommRing O] [IsDomain O] [Field Kf] [Algebra O Kf]
    (hinj : Function.Injective (algebraMap O Kf)) (m : ℕ) (lam : Fin (m + 1) → ℤ)
    (g : Matrix (Fin (m + 1)) (Fin (m + 1)) Kf) (hg : IsUnit g.det) :
    ∃ B : ↥(ssIdx (m + 1) (m + 1) (nuOf lam)) → MvPolynomial (Fin (m + 1) × Fin (m + 1)) Kf,
      LinearIndependent O B ∧ Submodule.span O (Set.range B) = nablaLTw O Kf m lam g ∧
      LinearIndependent Kf B ∧ Submodule.span Kf (Set.range B) = dualWeyl Kf (m + 1) (m + 1) (nuOf lam) := by
  obtain ⟨b, hb, -⟩ := sSBasis O (m + 1) (m + 1) (nuOf lam)
  obtain ⟨o1, o2⟩ := nablaLBasis O Kf hinj (m + 1) (m + 1) (nuOf lam) b _ hb g hg
  obtain ⟨k1, k2⟩ := nablaLKBasis O Kf hinj (m + 1) (m + 1) (nuOf lam) b _ hb g hg
  have hc : g.det ^ (-(lam (Fin.last m))) ≠ 0 := zpow_ne_zero _ hg.ne_zero
  set T : MvPolynomial (Fin (m + 1) × Fin (m + 1)) Kf →ₗ[Kf] MvPolynomial (Fin (m + 1) × Fin (m + 1)) Kf :=
    LinearMap.lsmul Kf _ (g.det ^ (-(lam (Fin.last m)))) with hT
  have hTinj : Function.Injective T := fun x y hxy => smul_right_injective _ hc hxy
  refine ⟨fun i => T (rowAct Kf g⁻¹ (map (algebraMap O Kf) (b i))), ?_, ?_, ?_, ?_⟩
  · exact o1.map' (T.restrictScalars O) (LinearMap.ker_eq_bot.2 hTinj)
  · have : (Set.range fun i => T (rowAct Kf g⁻¹ (map (algebraMap O Kf) (b i)))) =
        (T.restrictScalars O) '' (Set.range fun i => rowAct Kf g⁻¹ (map (algebraMap O Kf) (b i))) := by
      rw [← Set.range_comp]; rfl
    rw [this, ← Submodule.map_span, o2]
    rfl
  · exact k1.map' T (LinearMap.ker_eq_bot.2 hTinj)
  · have : (Set.range fun i => T (rowAct Kf g⁻¹ (map (algebraMap O Kf) (b i)))) =
        T '' (Set.range fun i => rowAct Kf g⁻¹ (map (algebraMap O Kf) (b i))) := by
      rw [← Set.range_comp]; rfl
    rw [this, ← Submodule.map_span, k2]
    have hT2 : T = (g.det ^ (-(lam (Fin.last m)))) • LinearMap.id := by
      ext x; simp [hT]
    rw [hT2, Submodule.map_smul _ _ _ hc, Submodule.map_id]

/- English proof (translation)
Take `⟨g, hg, rfl⟩` from `hLv`. Use `(G.P.setting v).frac_O` as an intermediate fact. Establish `hinj : Function.Injective (algebraMap G.O G.Kf)` using `IsFractionRing.injective G.O G.Kf`. Establish `hanti` using `kp_lamAt_antitone (G.P.lam0 v) (G.P.dom v)`. Establish `hB` using `fun s : Fin (G.P.n' v) => la_basis hinj G.P.m (lamAt (G.P.lam0 v) s) (la_tw (G.P.ι v) (G.P.σ v) s.val g) (la_tw_det _ _ _ g hg)`.

Use `choose B b1 b2 b3 b4 using hB`. Establish `hV : Vsp G.Kf (G.P.lam0 v) = tensorLat G.Kf G.Kf (fun s => dualWeyl G.Kf (G.P.m + 1) (G.P.m + 1) (nuOf (lamAt (G.P.lam0 v) s)))`. Unfold `Vsp`. Use `congr 1`. Use function extensionality and compare the values at `s`.

Rewrite using `[if_pos (hanti s)]`. Establish `hH : Hten G.O (G.P.lam0 v) (fun s => extO G.O (G.P.ι v) (G.P.σ v) s.val (colSpan (G.P.W v) g)) = tensorLat G.O G.Kf (fun s => nablaLTw G.O G.Kf G.P.m (lamAt (G.P.lam0 v) s) (la_tw (G.P.ι v) (G.P.σ v) s.val g))`. Unfold `Hten`. Use `congr 1`. Use function extensionality and compare the values at `s`.

Use `beta_reduce`. Rewrite using `[la_extO_G, H0_eq_twisted_nabla hI _ _ (hanti s) _ (la_tw_det _ _ _ g hg)]`. Establish `hKK : IsFractionRing G.Kf G.Kf` using `IsLocalization.of_le_isUnit (fun x hx => IsUnit.mk0 x (nonZeroDivisors.ne_zero hx))`. Take `⟨-, oS⟩` from `tensorBasis G.O G.Kf (Fin (G.P.n' v)) (G.P.m + 1) (G.P.m + 1) _ _ B b1 b2`. Take `⟨kL, kS⟩` from `tensorBasis G.Kf G.Kf (Fin (G.P.n' v)) (G.P.m + 1) (G.P.m + 1) _ _ B b3 b4`.

Establish `: ∀ s : Fin (G.P.n' v), Finite ↥(ssIdx (G.P.m + 1) (G.P.m + 1) (nuOf (lamAt (G.P.lam0 v) s)))` using `fun s => (sSIdxFinite (G.P.m + 1) (G.P.m + 1) (nuOf (lamAt (G.P.lam0 v) s))).to_subtype`. Unfold `HL toV`. Conclude with `la_refl_sub _ kL _ (kS.trans hV.symm) _ (oS.trans hH.symm)`.
-/
theorem la_reflexive_of (G : GAtP p) (hI : H0IndepOfBasis G.O G.Kf) (v : Fin G.P.nV)
    (Lv : Submodule (G.P.W v) (Fin (G.P.m + 1) → G.P.Qq v)) (hLv : IsLattice (G.P.W v) Lv) :
    predual (dualLat G.O G.Kf (HL (O := G.O) (G.P.ι v) (G.P.σ v) (G.P.lam0 v) Lv)) ≤
      HL (O := G.O) (G.P.ι v) (G.P.σ v) (G.P.lam0 v) Lv := by
  classical
  obtain ⟨g, hg, rfl⟩ := hLv
  have := (G.P.setting v).frac_O
  have hinj : Function.Injective (algebraMap G.O G.Kf) := IsFractionRing.injective G.O G.Kf
  have hanti := kp_lamAt_antitone (G.P.lam0 v) (G.P.dom v)
  have hB := fun s : Fin (G.P.n' v) => la_basis hinj G.P.m (lamAt (G.P.lam0 v) s)
    (la_tw (G.P.ι v) (G.P.σ v) s.val g) (la_tw_det _ _ _ g hg)
  choose B b1 b2 b3 b4 using hB
  have hV : Vsp G.Kf (G.P.lam0 v) = tensorLat G.Kf G.Kf
      (fun s => dualWeyl G.Kf (G.P.m + 1) (G.P.m + 1) (nuOf (lamAt (G.P.lam0 v) s))) := by
    unfold Vsp
    congr 1
    funext s
    rw [if_pos (hanti s)]
  have hH : Hten G.O (G.P.lam0 v) (fun s => extO G.O (G.P.ι v) (G.P.σ v) s.val (colSpan (G.P.W v) g)) =
      tensorLat G.O G.Kf (fun s => nablaLTw G.O G.Kf G.P.m (lamAt (G.P.lam0 v) s)
        (la_tw (G.P.ι v) (G.P.σ v) s.val g)) := by
    unfold Hten
    congr 1
    funext s
    beta_reduce
    rw [la_extO_G, H0_eq_twisted_nabla hI _ _ (hanti s) _ (la_tw_det _ _ _ g hg)]
  have hKK : IsFractionRing G.Kf G.Kf :=
    IsLocalization.of_le_isUnit (fun x hx => IsUnit.mk0 x (nonZeroDivisors.ne_zero hx))
  obtain ⟨-, oS⟩ := tensorBasis G.O G.Kf (Fin (G.P.n' v)) (G.P.m + 1) (G.P.m + 1) _ _ B b1 b2
  obtain ⟨kL, kS⟩ := tensorBasis G.Kf G.Kf (Fin (G.P.n' v)) (G.P.m + 1) (G.P.m + 1) _ _ B b3 b4
  have : ∀ s : Fin (G.P.n' v), Finite ↥(ssIdx (G.P.m + 1) (G.P.m + 1) (nuOf (lamAt (G.P.lam0 v) s))) :=
    fun s => (sSIdxFinite (G.P.m + 1) (G.P.m + 1) (nuOf (lamAt (G.P.lam0 v) s))).to_subtype
  unfold HL toV
  exact la_refl_sub _ kL _ (kS.trans hV.symm) _ (oS.trans hH.symm)

/- English proof (translation)
Establish `h : (rowAct Kf (n` using `n) (U.map (algebraMap O Kf))).toRingHom.comp (map (algebraMap O Kf)) = (map (algebraMap O Kf)).comp (rowAct O (n := n) U).toRingHom := by`. Apply `MvPolynomial.ringHom_ext` to reduce the goal to its premises. Introduce `a`. Simplify using `[rowAct]`. Introduce `x`.

Simplify using `[rowAct]`. Conclude with `RingHom.congr_fun h f`.
-/
theorem la_rowAct_map {O Kf : Type} [CommRing O] [Field Kf] [Algebra O Kf] {k n : ℕ}
    (U : Matrix (Fin k) (Fin k) O) (f : MvPolynomial (Fin k × Fin n) O) :
    rowAct Kf (U.map (algebraMap O Kf)) (map (algebraMap O Kf) f) = map (algebraMap O Kf) (rowAct O U f) := by
  have h : (rowAct Kf (n := n) (U.map (algebraMap O Kf))).toRingHom.comp (map (algebraMap O Kf)) =
      (map (algebraMap O Kf)).comp (rowAct O (n := n) U).toRingHom := by
    apply MvPolynomial.ringHom_ext
    · intro a
      simp [rowAct]
    · intro x
      simp [rowAct]
  exact RingHom.congr_fun h f

/- English proof (translation)
Establish `h1 : ∀ c : Fin k, ∃ a : Fin k → O, ∑ c', a c' • (fun i => g i c') = fun i => h i c`. Introduce `c`. Establish `: (fun i => h i c) ∈ colSpan O g` using `hle (Submodule.subset_span ⟨c, rfl⟩)`. Conclude with `(Submodule.mem_span_range_iff_exists_fun O).1 this`. Use `choose a ha using h1`.

Use `⟨fun c' c => a c c', ?_⟩` and prove the remaining obligations. Use extensionality with `i c`. Use `congrFun (ha c) i` as an intermediate fact. Rewrite using `[Matrix.mul_apply, ← this, Finset.sum_apply]`. Apply `Finset.sum_congr rfl` to reduce the goal to its premises.

Introduce `c' _`. Use `show a c c' • g i c' = g i c' * algebraMap O Kf (a c c')`. Rewrite using `[Algebra.smul_def, mul_comm]`.
-/
theorem la_factor {O Kf : Type} [CommRing O] [Field Kf] [Algebra O Kf] {k : ℕ}
    (g h : Matrix (Fin k) (Fin k) Kf) (hle : colSpan O h ≤ colSpan O g) :
    ∃ U : Matrix (Fin k) (Fin k) O, h = g * U.map (algebraMap O Kf) := by
  have h1 : ∀ c : Fin k, ∃ a : Fin k → O, ∑ c', a c' • (fun i => g i c') = fun i => h i c := by
    intro c
    have : (fun i => h i c) ∈ colSpan O g := hle (Submodule.subset_span ⟨c, rfl⟩)
    exact (Submodule.mem_span_range_iff_exists_fun O).1 this
  choose a ha using h1
  refine ⟨fun c' c => a c c', ?_⟩
  ext i c
  have := congrFun (ha c) i
  rw [Matrix.mul_apply, ← this, Finset.sum_apply]
  apply Finset.sum_congr rfl
  intro c' _
  show a c c' • g i c' = g i c' * algebraMap O Kf (a c c')
  rw [Algebra.smul_def, mul_comm]

/- English proof (translation)
Introduce `m lam g h hg hh heq`. Take `⟨U, hU⟩` from `la_factor g h heq.ge`. Take `⟨U2, hU2⟩` from `la_factor h g heq.le`. Establish `hUU : U * U2 = 1`. Establish `h1 : g * (U * U2).map (algebraMap O Kf) = g * 1`.

Rewrite using `[Matrix.mul_one, Matrix.map_mul, ← Matrix.mul_assoc, ← hU, ← hU2]`. Establish `hgu : IsUnit g` using `(Matrix.isUnit_iff_isUnit_det g).2 hg`. Establish `h2 : (U * U2).map (algebraMap O Kf) = 1` using `hgu.mul_left_cancel h1`. Apply `Matrix.map_injective hinj` to reduce the goal to its premises. Use `beta_reduce`.

Rewrite using `[h2]`. Simplify using the standard rewrite rules. Establish `hdet : U.det * U2.det = 1` using `by rw [← Matrix.det_mul, hUU, Matrix.det_one]`. Set `u : Oˣ` to `⟨U.det, U2.det, hdet, by rw [mul_comm]; exact hdet⟩`. Establish `hdU : (U.map (algebraMap O Kf)).det = algebraMap O Kf U.det`.

Rewrite using `[RingHom.map_det]`. Both sides reduce to the same expression. Establish `hc : algebraMap O Kf U.det ≠ 0`. Introduce `h0`. Use `congrArg (algebraMap O Kf) hdet` as an intermediate fact.

Rewrite `this` using `[map_mul, h0, zero_mul, map_one]`. Conclude with `zero_ne_one this`. Establish `hz : ∀ e : ℤ, algebraMap O Kf ((u ^ e : Oˣ) : O) = (algebraMap O Kf U.det) ^ e`. Introduce `e`. Establish `h1 : ((Units.map (algebraMap O Kf : O →* Kf) u ^ e : Kfˣ) : Kf) = (algebraMap O Kf U.det) ^ e`.

Rewrite using `[Units.val_zpow_eq_zpow_val]`. Both sides reduce to the same expression. Rewrite using `[← h1, ← map_zpow]`. Both sides reduce to the same expression. Introduce and unpack `_ ⟨F, hF, rfl⟩`.

Establish `hFh : F ∈ nablaL O Kf (m + 1) (m + 1) (fun t => (lam t - lam (Fin.last m)).toNat) h`. Take `⟨f, hf, hfe⟩` from `hF`. Use `⟨rowAct O U f, dualWeylRowStable O _ _ _ U f hf, ?_⟩` and prove the remaining obligations. Establish `h3 : rowAct Kf (n` using `m + 1) h = (rowAct Kf (U.map (algebraMap O Kf))).comp (rowAct Kf g) := by`. Rewrite using `[rowActMul, hU]`.

Express the relevant statement in the definitionally equal form `map (algebraMap O Kf) (rowAct O U f) = rowAct Kf h F`. Rewrite using `[h3, AlgHom.comp_apply, ← la_rowAct_map]`. Use `congr 1`. Use `⟨((u ^ (lam (Fin.last m)) : Oˣ) : O) • F, Submodule.smul_mem _ _ hFh, ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `h.det ^ (-(lam (Fin.last m))) • (((u ^ (lam (Fin.last m)) : Oˣ) : O) • F) = g.det ^ (-(lam (Fin.last m))) • F`.

Rewrite using `[← algebraMap_smul Kf (((u ^ (lam (Fin.last m)) : Oˣ) : O)) F, hz, smul_smul, hU, Matrix.det_mul, hdU, mul_zpow, mul_assoc, ← zpow_add₀ hc, neg_add_cancel, zpow_zero, mul_one]`.
-/
theorem la_indep {O Kf : Type} [CommRing O] [Field Kf] [Algebra O Kf]
    (hinj : Function.Injective (algebraMap O Kf)) : H0IndepOfBasis O Kf := by
  intro m lam g h hg hh heq
  obtain ⟨U, hU⟩ := la_factor g h heq.ge
  obtain ⟨U2, hU2⟩ := la_factor h g heq.le
  have hUU : U * U2 = 1 := by
    have h1 : g * (U * U2).map (algebraMap O Kf) = g * 1 := by
      rw [Matrix.mul_one, Matrix.map_mul, ← Matrix.mul_assoc, ← hU, ← hU2]
    have hgu : IsUnit g := (Matrix.isUnit_iff_isUnit_det g).2 hg
    have h2 : (U * U2).map (algebraMap O Kf) = 1 := hgu.mul_left_cancel h1
    apply Matrix.map_injective hinj
    beta_reduce
    rw [h2]
    simp
  have hdet : U.det * U2.det = 1 := by rw [← Matrix.det_mul, hUU, Matrix.det_one]
  let u : Oˣ := ⟨U.det, U2.det, hdet, by rw [mul_comm]; exact hdet⟩
  have hdU : (U.map (algebraMap O Kf)).det = algebraMap O Kf U.det := by
    rw [RingHom.map_det]; rfl
  have hc : algebraMap O Kf U.det ≠ 0 := by
    intro h0
    have := congrArg (algebraMap O Kf) hdet
    rw [map_mul, h0, zero_mul, map_one] at this
    exact zero_ne_one this
  have hz : ∀ e : ℤ, algebraMap O Kf ((u ^ e : Oˣ) : O) = (algebraMap O Kf U.det) ^ e := by
    intro e
    have h1 : ((Units.map (algebraMap O Kf : O →* Kf) u ^ e : Kfˣ) : Kf) = (algebraMap O Kf U.det) ^ e := by
      rw [Units.val_zpow_eq_zpow_val]; rfl
    rw [← h1, ← map_zpow]
    rfl
  rintro _ ⟨F, hF, rfl⟩
  have hFh : F ∈ nablaL O Kf (m + 1) (m + 1) (fun t => (lam t - lam (Fin.last m)).toNat) h := by
    obtain ⟨f, hf, hfe⟩ := hF
    refine ⟨rowAct O U f, dualWeylRowStable O _ _ _ U f hf, ?_⟩
    have h3 : rowAct Kf (n := m + 1) h = (rowAct Kf (U.map (algebraMap O Kf))).comp (rowAct Kf g) := by
      rw [rowActMul, hU]
    change map (algebraMap O Kf) (rowAct O U f) = rowAct Kf h F
    rw [h3, AlgHom.comp_apply, ← la_rowAct_map]
    congr 1
  refine ⟨((u ^ (lam (Fin.last m)) : Oˣ) : O) • F, Submodule.smul_mem _ _ hFh, ?_⟩
  change h.det ^ (-(lam (Fin.last m))) • (((u ^ (lam (Fin.last m)) : Oˣ) : O) • F) =
    g.det ^ (-(lam (Fin.last m))) • F
  rw [← algebraMap_smul Kf (((u ^ (lam (Fin.last m)) : Oˣ) : O)) F, hz, smul_smul, hU, Matrix.det_mul, hdU,
    mul_zpow, mul_assoc, ← zpow_add₀ hc, neg_add_cancel, zpow_zero, mul_one]

/- English proof (translation)
Use `(G.P.setting v).frac_O` as an intermediate fact. Conclude with `la_reflexive_of G (la_indep (IsFractionRing.injective G.O G.Kf)) v Lv hLv`.
-/
theorem la_reflexive (G : GAtP p) (v : Fin G.P.nV)
    (Lv : Submodule (G.P.W v) (Fin (G.P.m + 1) → G.P.Qq v)) (hLv : IsLattice (G.P.W v) Lv) :
    predual (dualLat G.O G.Kf (HL (O := G.O) (G.P.ι v) (G.P.σ v) (G.P.lam0 v) Lv)) ≤
      HL (O := G.O) (G.P.ι v) (G.P.σ v) (G.P.lam0 v) Lv := by
  have := (G.P.setting v).frac_O
  exact la_reflexive_of G (la_indep (IsFractionRing.injective G.O G.Kf)) v Lv hLv

def RestLocEdge (G : GAtP p) (v : Fin G.P.nV) : Prop :=
  ∀ Lv : Submodule (G.P.W v) (Fin (G.P.m + 1) → G.P.Qq v), IsLattice (G.P.W v) Lv →
    (∀ e : Edge (G.P.W v) (G.P.Qq v) (G.P.m + 1), IsEdge p (G.P.n' v) G.P.r e → e.src = Lv →
      HL (O := G.O) (G.P.ι v) (G.P.σ v) (G.P.lam0 v) Lv ≤
        Re p (G.P.ι v) (G.P.σ v) G.P.w G.P.r (G.P.lam0 v) e) ∧
    (∀ e : Edge (G.P.W v) (G.P.Qq v) (G.P.m + 1), IsEdge p (G.P.n' v) G.P.r e → e.tgt = Lv →
      dualLat G.O G.Kf (HL (O := G.O) (G.P.ι v) (G.P.σ v) (G.P.lam0 v) Lv) ≤
        Re' p (G.P.ι v) (G.P.σ v) G.P.w G.P.r (G.P.lam0 v) e)

/- English proof (translation)
Introduce `Lv hLv` and use `⟨la_H_le_V G v Lv hLv, (h Lv hLv).1, (h Lv hLv).2, la_reflexive G v Lv hLv⟩`.
-/
theorem la_locD_of_edge (G : GAtP p) (v : Fin G.P.nV) (h : RestLocEdge G v) : RestLocD G v :=
  fun Lv hLv => ⟨la_H_le_V G v Lv hLv, (h Lv hLv).1, (h Lv hLv).2, la_reflexive G v Lv hLv⟩

end Formalism.MainNotions.G.LatticeSystems

namespace Formalism.MainNotions.G.LatticeSystems

open Formalism.MainNotions.G Formalism.GradedWeylDivisibility MvPolynomial

/- English proof (translation)
Take `⟨b, hb, h2⟩` from `sSBasis R k n ν`. Use `⟨b, hb, fun m r => ?_⟩` and prove the remaining obligations. Take `⟨hdeg, hlc, K, sz, hsz, I, hshape, -, hbm⟩` from `h2 m`. Establish `hmem : m.1 ∈ (bideterminant R sz hsz I).support`. Rewrite using `[← hbm, MvPolynomial.mem_support_iff]`.

Establish `h3 : (colLex k n).leadingCoeff (b m) = MvPolynomial.coeff ((colLex k n).degree (b m)) (b m)` using `rfl`. Rewrite `h3` using `[hdeg]`. Rewrite using `[← h3, hlc]`. Conclude with `one_ne_zero`. Establish `h4` using `(bidetDominance R k n K sz hsz I m.1 hmem).1 r`.

Rewrite `h4` using `[hshape]`. Conclude with `h4`.
-/
theorem lb_basis (R : Type) [CommRing R] [IsDomain R] (k n : ℕ) (ν : Fin n → ℕ) :
    ∃ b : ssIdx k n ν → MvPolynomial (Fin k × Fin n) R,
      IsWeightBasis R k n ν b (fun m => rowWt m.1) ∧
      ∀ (m : ssIdx k n ν) (r : ℕ),
        (∑ a : Fin k with a.val < r, rowWt m.1 a) ≤ ∑ t : Fin n with t.val < r, ν t := by
  obtain ⟨b, hb, h2⟩ := sSBasis R k n ν
  refine ⟨b, hb, fun m r => ?_⟩
  obtain ⟨hdeg, hlc, K, sz, hsz, I, hshape, -, hbm⟩ := h2 m
  have hmem : m.1 ∈ (bideterminant R sz hsz I).support := by
    rw [← hbm, MvPolynomial.mem_support_iff]
    have h3 : (colLex k n).leadingCoeff (b m) =
        MvPolynomial.coeff ((colLex k n).degree (b m)) (b m) := rfl
    rw [hdeg] at h3
    rw [← h3, hlc]
    exact one_ne_zero
  have h4 := (bidetDominance R k n K sz hsz I m.1 hmem).1 r
  rw [hshape] at h4
  exact h4

/- English proof (translation)
Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty => simp`. Consider the case `insert a s ha ih => rw [Finset.prod_insert ha, Finset.sum_insert ha, zpow_add₀ hc, ih]`.
-/
theorem lb_zpow_sum {K ι : Type*} [Field K] (c : K) (hc : c ≠ 0) (s : Finset ι) (f : ι → ℤ) :
    ∏ i ∈ s, c ^ (f i) = c ^ (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => rw [Finset.prod_insert ha, Finset.sum_insert ha, zpow_add₀ hc, ih]

def lb_D {K : Type*} [Field K] (k r : ℕ) (c : K) : Matrix (Fin k) (Fin k) K :=
  Matrix.diagonal fun a => if a.val < r then c⁻¹ else 1

/- English proof (translation)
Use `set c : Kf := algebraMap O Kf w with hc`. Use `set ν : Fin (m + 1) → ℕ := fun t => (lam t - lam (Fin.last m)).toNat with hν`. Use `set e : ℤ := lam (Fin.last m) with he`. Take `⟨b, hb, hwt⟩` from `lb_basis O (m + 1) (m + 1) ν`. Use `set t : Fin (m + 1) → Kf := fun a => if a.val < r then c⁻¹ else 1 with ht`.

Establish `ht0 : ∀ a, t a ≠ 0`. Introduce `a`. Simplify using `only [ht]`. Use `split_ifs`. Conclude with `inv_ne_zero hw`.

Conclude with `one_ne_zero`. Establish `hB` using `(nablaLBasis O Kf hinj (m + 1) (m + 1) ν b _ hb g hg).2`. Establish `hD` using `(nablaLDiag O Kf hinj (m + 1) (m + 1) ν b _ hb g t hg ht0).2`. Take `⟨F0, hF0, rfl⟩` from `hF`. Establish `hF0' : F0 ∈ nablaL O Kf (m + 1) (m + 1) ν g` using `hF0`.

Rewrite `hF0'` using `[← hB]`. Use `set A : ℤ := ∑ i : Fin (m + 1) with i.val < r, lam i with hA`. Use `set T : MvPolynomial (Fin (m + 1) × Fin (m + 1)) Kf →ₗ[O] MvPolynomial (Fin (m + 1) × Fin (m + 1)) Kf := (LinearMap.lsmul Kf _ (c ^ A * g.det ^ (-e))).restrictScalars O with hT`. Establish `key : Submodule.span O (Set.range fun i => rowAct Kf g⁻¹ (map (algebraMap O Kf) (b i))) ≤ (nablaLTw O Kf m lam (g * lb_D (m + 1) r c)).comap T`. Rewrite using `[Submodule.span_le]`.

Introduce and unpack `_ ⟨i, rfl⟩`. Use `set Fi := rowAct Kf g⁻¹ (map (algebraMap O Kf) (b i)) with hFi`. Use `set π' : ℕ := ∑ a : Fin (m + 1) with a.val < r, rowWt i.1 a with hπ`. Use `set Nν : ℕ := ∑ t : Fin (m + 1) with t.val < r, ν t with hNν`. Establish `hle : π' ≤ Nν` using `hwt i r`.

Use `⟨w ^ (Nν - π') • ((∏ a, t a ^ rowWt i.1 a)⁻¹ • Fi), ?_, ?_⟩` and prove the remaining obligations. Apply `Submodule.smul_mem show _ ∈ nablaL O Kf (m + 1) (m + 1) ν (g * Matrix.diagonal t)` to reduce the goal to its premises. Rewrite using `[← hD]`. Conclude with `Submodule.subset_span ⟨i, rfl⟩`. Use `show (g * lb_D (m + 1) r c).det ^ (-e) • (w ^ (Nν - π') • ((∏ a, t a ^ rowWt i.1 a)⁻¹ • Fi)) = (c ^ A * g.det ^ (-e)) • Fi`.

Rewrite using `[← algebraMap_smul Kf (w ^ (Nν - π')), smul_smul, smul_smul, map_pow, ← hc]`. Use `congr 1`. Use `set ρ : ℕ := (Finset.univ.filter fun a : Fin (m + 1) => a.val < r).card with hρ`. Establish `h1 : (g * lb_D (m + 1) r c).det = g.det * (c⁻¹) ^ ρ`. Rewrite using `[Matrix.det_mul, lb_D, Matrix.det_diagonal, Finset.prod_ite, Finset.prod_const, Finset.prod_const_one, mul_one]`.

Establish `h2 : ∏ a, t a ^ rowWt i.1 a = (c⁻¹) ^ π'`. Rewrite using `[hπ, ← Finset.prod_pow_eq_pow_sum, Finset.prod_filter]`. Apply `Finset.prod_congr rfl` to reduce the goal to its premises. Introduce `a _`. Simplify using `only [ht]`.

Apply the tactic sequence `split_ifs <;> simp`. Establish `h3 : A = (Nν : ℤ) + ρ * e`. Rewrite using `[hA, hNν, hρ]`. Use `push_cast`. Rewrite using `[Finset.card_eq_sum_ones]`.

Use `push_cast`. Rewrite using `[Finset.sum_mul, ← Finset.sum_add_distrib]`. Apply `Finset.sum_congr rfl` to reduce the goal to its premises. Introduce `a _`. Establish `: 0 ≤ lam a - lam (Fin.last m)` using `sub_nonneg.2 (hlam (Fin.le_last a))`.

Simplify using `only [hν, Int.toNat_of_nonneg this, he]`. Expand and normalize the polynomial expressions, which then agree. Establish `h4 : c ^ Nν = c ^ (Nν - π') * c ^ π'`. Rewrite using `[← pow_add, Nat.sub_add_cancel hle]`. Establish `h5 : ((c⁻¹) ^ ρ) ^ (-e) = c ^ ((ρ : ℤ) * e)`.

Rewrite using `[inv_pow, inv_zpow, zpow_neg, inv_inv, ← zpow_natCast c ρ, ← zpow_mul]`. Establish `h6 : ((c⁻¹) ^ π')⁻¹ = c ^ π'` using `by rw [inv_pow, inv_inv]`. Rewrite using `[h1, h2, h3, mul_zpow, h5, h6, zpow_add₀ hw, zpow_natCast, h4]`. Expand and normalize the polynomial expressions, which then agree. Establish `h5` using `key hF0'`.

Establish `h6 : T F0 = c ^ A • (LinearMap.restrictScalars O ((LinearMap.lsmul Kf _) (g.det ^ (-e)))) F0`. Simplify using `only [hT, LinearMap.restrictScalars_apply, LinearMap.lsmul_apply, smul_smul]`. Rewrite using `[← h6]`. Conclude with `h5`.
-/
theorem lb_P (O Kf : Type) [CommRing O] [IsDomain O] [Field Kf] [Algebra O Kf]
    (hinj : Function.Injective (algebraMap O Kf)) (m r : ℕ) (lam : Fin (m + 1) → ℤ) (hlam : Antitone lam)
    (w : O) (hw : algebraMap O Kf w ≠ 0) (g : Matrix (Fin (m + 1)) (Fin (m + 1)) Kf) (hg : IsUnit g.det)
    (F : MvPolynomial (Fin (m + 1) × Fin (m + 1)) Kf) (hF : F ∈ nablaLTw O Kf m lam g) :
    (algebraMap O Kf w ^ (∑ i : Fin (m + 1) with i.val < r, lam i)) • F ∈
      nablaLTw O Kf m lam (g * lb_D (m + 1) r (algebraMap O Kf w)) := by
  classical
  set c : Kf := algebraMap O Kf w with hc
  set ν : Fin (m + 1) → ℕ := fun t => (lam t - lam (Fin.last m)).toNat with hν
  set e : ℤ := lam (Fin.last m) with he
  obtain ⟨b, hb, hwt⟩ := lb_basis O (m + 1) (m + 1) ν
  set t : Fin (m + 1) → Kf := fun a => if a.val < r then c⁻¹ else 1 with ht
  have ht0 : ∀ a, t a ≠ 0 := by
    intro a
    simp only [ht]
    split_ifs
    · exact inv_ne_zero hw
    · exact one_ne_zero
  have hB := (nablaLBasis O Kf hinj (m + 1) (m + 1) ν b _ hb g hg).2
  have hD := (nablaLDiag O Kf hinj (m + 1) (m + 1) ν b _ hb g t hg ht0).2
  obtain ⟨F0, hF0, rfl⟩ := hF
  have hF0' : F0 ∈ nablaL O Kf (m + 1) (m + 1) ν g := hF0
  rw [← hB] at hF0'
  set A : ℤ := ∑ i : Fin (m + 1) with i.val < r, lam i with hA
  set T : MvPolynomial (Fin (m + 1) × Fin (m + 1)) Kf →ₗ[O] MvPolynomial (Fin (m + 1) × Fin (m + 1)) Kf :=
    (LinearMap.lsmul Kf _ (c ^ A * g.det ^ (-e))).restrictScalars O with hT
  have key : Submodule.span O (Set.range fun i => rowAct Kf g⁻¹ (map (algebraMap O Kf) (b i))) ≤
      (nablaLTw O Kf m lam (g * lb_D (m + 1) r c)).comap T := by
    rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    set Fi := rowAct Kf g⁻¹ (map (algebraMap O Kf) (b i)) with hFi
    set π' : ℕ := ∑ a : Fin (m + 1) with a.val < r, rowWt i.1 a with hπ
    set Nν : ℕ := ∑ t : Fin (m + 1) with t.val < r, ν t with hNν
    have hle : π' ≤ Nν := hwt i r
    refine ⟨w ^ (Nν - π') • ((∏ a, t a ^ rowWt i.1 a)⁻¹ • Fi), ?_, ?_⟩
    · apply Submodule.smul_mem
      show _ ∈ nablaL O Kf (m + 1) (m + 1) ν (g * Matrix.diagonal t)
      rw [← hD]
      exact Submodule.subset_span ⟨i, rfl⟩
    · show (g * lb_D (m + 1) r c).det ^ (-e) • (w ^ (Nν - π') • ((∏ a, t a ^ rowWt i.1 a)⁻¹ • Fi)) =
        (c ^ A * g.det ^ (-e)) • Fi
      rw [← algebraMap_smul Kf (w ^ (Nν - π')), smul_smul, smul_smul, map_pow, ← hc]
      congr 1
      set ρ : ℕ := (Finset.univ.filter fun a : Fin (m + 1) => a.val < r).card with hρ
      have h1 : (g * lb_D (m + 1) r c).det = g.det * (c⁻¹) ^ ρ := by
        rw [Matrix.det_mul, lb_D, Matrix.det_diagonal, Finset.prod_ite, Finset.prod_const,
          Finset.prod_const_one, mul_one]
      have h2 : ∏ a, t a ^ rowWt i.1 a = (c⁻¹) ^ π' := by
        rw [hπ, ← Finset.prod_pow_eq_pow_sum, Finset.prod_filter]
        apply Finset.prod_congr rfl
        intro a _
        simp only [ht]
        split_ifs <;> simp
      have h3 : A = (Nν : ℤ) + ρ * e := by
        rw [hA, hNν, hρ]
        push_cast
        rw [Finset.card_eq_sum_ones]
        push_cast
        rw [Finset.sum_mul, ← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro a _
        have : 0 ≤ lam a - lam (Fin.last m) := sub_nonneg.2 (hlam (Fin.le_last a))
        simp only [hν, Int.toNat_of_nonneg this, he]
        ring
      have h4 : c ^ Nν = c ^ (Nν - π') * c ^ π' := by
        rw [← pow_add, Nat.sub_add_cancel hle]
      have h5 : ((c⁻¹) ^ ρ) ^ (-e) = c ^ ((ρ : ℤ) * e) := by
        rw [inv_pow, inv_zpow, zpow_neg, inv_inv, ← zpow_natCast c ρ, ← zpow_mul]
      have h6 : ((c⁻¹) ^ π')⁻¹ = c ^ π' := by rw [inv_pow, inv_inv]
      rw [h1, h2, h3, mul_zpow, h5, h6, zpow_add₀ hw, zpow_natCast, h4]
      ring
  have h5 := key hF0'
  have h6 : T F0 = c ^ A • (LinearMap.restrictScalars O ((LinearMap.lsmul Kf _) (g.det ^ (-e)))) F0 := by
    simp only [hT, LinearMap.restrictScalars_apply, LinearMap.lsmul_apply, smul_smul]
  rw [← h6]
  exact h5

/- English proof (translation)
Establish `key : tensorLat O Kf M ≤ (tensorLat O Kf M').comap ((LinearMap.lsmul Kf (MvPolynomial (S × (Fin k × Fin n)) Kf) (∏ s, c s)).restrictScalars O)`. Unfold `tensorLat`. Rewrite using `[Submodule.span_le]`. Introduce and unpack `_ ⟨F, hF, rfl⟩`. Apply `Submodule.subset_span` to reduce the goal to its premises.

Use `⟨fun s => c s • F s, fun s => h s _ (hF s), ?_⟩` and prove the remaining obligations. Simplify using `only [LinearMap.restrictScalars_apply, LinearMap.lsmul_apply, map_smul]`. Rewrite using `[Finset.prod_smul]`. Conclude with `fun P hP => key hP`.
-/
theorem lb_tensor (O Kf : Type) [CommRing O] [Field Kf] [Algebra O Kf] {S : Type} [Fintype S] {k n : ℕ}
    (M M' : S → Submodule O (MvPolynomial (Fin k × Fin n) Kf)) (c : S → Kf)
    (h : ∀ s, ∀ F ∈ M s, c s • F ∈ M' s) :
    ∀ P ∈ tensorLat O Kf M, (∏ s, c s) • P ∈ tensorLat O Kf M' := by
  have key : tensorLat O Kf M ≤ (tensorLat O Kf M').comap
      ((LinearMap.lsmul Kf (MvPolynomial (S × (Fin k × Fin n)) Kf) (∏ s, c s)).restrictScalars O) := by
    unfold tensorLat
    rw [Submodule.span_le]
    rintro _ ⟨F, hF, rfl⟩
    apply Submodule.subset_span
    refine ⟨fun s => c s • F s, fun s => h s _ (hF s), ?_⟩
    simp only [LinearMap.restrictScalars_apply, LinearMap.lsmul_apply, map_smul]
    rw [Finset.prod_smul]
  exact fun P hP => key hP

/- English proof (translation)
Establish `hcol : ∀ (g h : Matrix (Fin (m + 1)) (Fin (m + 1)) Kf), colSpan O g = colSpan O h → ∃ U : Matrix (Fin (m + 1)) (Fin (m + 1)) O, h = g * U.map (algebraMap O Kf)`. Introduce `g h hs`. Establish `h1 : ∀ j, ∃ c : Fin (m + 1) → O, ∑ i, c i • (fun a => g a i) = fun a => h a j`. Introduce `j`. Establish `hm : (fun a => h a j) ∈ colSpan O g`.

Rewrite using `[hs]`. Conclude with `Submodule.subset_span ⟨j, rfl⟩`. Conclude with `(Submodule.mem_span_range_iff_exists_fun O).1 hm`. Use `choose c hc using h1`. Use `⟨fun i j => c j i, ?_⟩` and prove the remaining obligations.

Use extensionality with `a j`. Establish `h2` using `congrFun (hc j) a`. Rewrite using `[Matrix.mul_apply, ← h2, Finset.sum_apply]`. Apply `Finset.sum_congr rfl` to reduce the goal to its premises. Introduce `i _`.

Use `show c j i • g a i = g a i * algebraMap O Kf (c j i)`. Rewrite using `[Algebra.smul_def, mul_comm]`. Take `⟨U, hU⟩` from `hcol g h hs`. Take `⟨U', hU'⟩` from `hcol h g hs.symm`. Establish `hdU : ∀ V : Matrix (Fin (m + 1)) (Fin (m + 1)) O, (V.map (algebraMap O Kf)).det = algebraMap O Kf V.det` using `fun V => (RingHom.map_det (algebraMap O Kf) V).symm`.

Establish `hdet : U.det * U'.det = 1`. Apply `hinj` to reduce the goal to its premises. Establish `h1 : g.det * (algebraMap O Kf U.det * algebraMap O Kf U'.det) = g.det * 1` using `by conv_rhs => rw [mul_one, hU', hU, Matrix.det_mul, Matrix.det_mul, hdU, hdU]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[map_mul, map_one]`.

Conclude with `mul_left_cancel₀ hg.ne_zero h1`. Set `u : Oˣ` to `⟨U.det, U'.det, hdet, by rw [mul_comm]; exact hdet⟩`. Use `set e : ℤ := lam (Fin.last m) with he`. Establish `hz : algebraMap O Kf ((u ^ e : Oˣ) : O) = (algebraMap O Kf U.det) ^ e`. Combine the equalities or inequalities in the displayed calculation.

Introduce `F hF`. Rewrite using `[nablaLTwMem O Kf m lam h hh]`. Rewrite `hF` using `[nablaLTwMem O Kf m lam g hg]`. Take `⟨f, hf, hfe⟩` from `hF`. Use `⟨((u ^ e : Oˣ) : O) • rowAct O U f, Submodule.smul_mem _ _ (dualWeylRowStable O _ _ _ U f hf), ?_⟩` and prove the remaining obligations.

Establish `hmap : ∀ f : MvPolynomial (Fin (m + 1) × Fin (m + 1)) O, (mapAlgHom (Algebra.ofId O Kf)).toLinearMap f = map (algebraMap O Kf) f` using `fun f => rfl`. Rewrite `hfe` using `[hmap]`. Rewrite using `[map_smul, hmap, ldtwist_map_rowAct, hfe, map_smul, ← algebraMap_smul Kf ((u ^ e : Oˣ) : O), hz, smul_smul]`. Establish `h4 : rowAct Kf (U.map (algebraMap O Kf)) (rowAct Kf g F) = rowAct Kf h F`. Establish `h5` using `rowActMul Kf (m + 1) (m + 1) (U.map (algebraMap O Kf)) g`.

Rewrite using `[hU, ← h5]`. Both sides reduce to the same expression. Rewrite using `[h4, hU, Matrix.det_mul, hdU, mul_zpow, mul_comm]`.
-/
theorem lb_indep (O Kf : Type) [CommRing O] [IsDomain O] [Field Kf] [Algebra O Kf]
    (hinj : Function.Injective (algebraMap O Kf)) (m : ℕ) (lam : Fin (m + 1) → ℤ)
    (g h : Matrix (Fin (m + 1)) (Fin (m + 1)) Kf) (hg : IsUnit g.det) (hh : IsUnit h.det)
    (hs : colSpan O g = colSpan O h) : nablaLTw O Kf m lam g ≤ nablaLTw O Kf m lam h := by
  classical
  have hcol : ∀ (g h : Matrix (Fin (m + 1)) (Fin (m + 1)) Kf), colSpan O g = colSpan O h →
      ∃ U : Matrix (Fin (m + 1)) (Fin (m + 1)) O, h = g * U.map (algebraMap O Kf) := by
    intro g h hs
    have h1 : ∀ j, ∃ c : Fin (m + 1) → O, ∑ i, c i • (fun a => g a i) = fun a => h a j := by
      intro j
      have hm : (fun a => h a j) ∈ colSpan O g := by
        rw [hs]; exact Submodule.subset_span ⟨j, rfl⟩
      exact (Submodule.mem_span_range_iff_exists_fun O).1 hm
    choose c hc using h1
    refine ⟨fun i j => c j i, ?_⟩
    ext a j
    have h2 := congrFun (hc j) a
    rw [Matrix.mul_apply, ← h2, Finset.sum_apply]
    apply Finset.sum_congr rfl
    intro i _
    show c j i • g a i = g a i * algebraMap O Kf (c j i)
    rw [Algebra.smul_def, mul_comm]
  obtain ⟨U, hU⟩ := hcol g h hs
  obtain ⟨U', hU'⟩ := hcol h g hs.symm
  have hdU : ∀ V : Matrix (Fin (m + 1)) (Fin (m + 1)) O,
      (V.map (algebraMap O Kf)).det = algebraMap O Kf V.det :=
    fun V => (RingHom.map_det (algebraMap O Kf) V).symm
  have hdet : U.det * U'.det = 1 := by
    apply hinj
    have h1 : g.det * (algebraMap O Kf U.det * algebraMap O Kf U'.det) = g.det * 1 := by
      conv_rhs => rw [mul_one, hU', hU, Matrix.det_mul, Matrix.det_mul, hdU, hdU]
      ring
    rw [map_mul, map_one]
    exact mul_left_cancel₀ hg.ne_zero h1
  let u : Oˣ := ⟨U.det, U'.det, hdet, by rw [mul_comm]; exact hdet⟩
  set e : ℤ := lam (Fin.last m) with he
  have hz : algebraMap O Kf ((u ^ e : Oˣ) : O) = (algebraMap O Kf U.det) ^ e := by
    calc algebraMap O Kf ((u ^ e : Oˣ) : O)
        = ((Units.map (algebraMap O Kf : O →* Kf) (u ^ e) : Kfˣ) : Kf) := rfl
      _ = (((Units.map (algebraMap O Kf : O →* Kf) u) ^ e : Kfˣ) : Kf) := by rw [map_zpow]
      _ = ((Units.map (algebraMap O Kf : O →* Kf) u : Kfˣ) : Kf) ^ e := Units.val_zpow_eq_zpow_val _ _
      _ = (algebraMap O Kf U.det) ^ e := rfl
  intro F hF
  rw [nablaLTwMem O Kf m lam h hh]
  rw [nablaLTwMem O Kf m lam g hg] at hF
  obtain ⟨f, hf, hfe⟩ := hF
  refine ⟨((u ^ e : Oˣ) : O) • rowAct O U f,
    Submodule.smul_mem _ _ (dualWeylRowStable O _ _ _ U f hf), ?_⟩
  have hmap : ∀ f : MvPolynomial (Fin (m + 1) × Fin (m + 1)) O,
      (mapAlgHom (Algebra.ofId O Kf)).toLinearMap f = map (algebraMap O Kf) f := fun f => rfl
  rw [hmap] at hfe
  rw [map_smul, hmap, ldtwist_map_rowAct, hfe, map_smul, ← algebraMap_smul Kf ((u ^ e : Oˣ) : O), hz,
    smul_smul]
  have h4 : rowAct Kf (U.map (algebraMap O Kf)) (rowAct Kf g F) = rowAct Kf h F := by
    have h5 := rowActMul Kf (m + 1) (m + 1) (U.map (algebraMap O Kf)) g
    rw [hU, ← h5]
    rfl
  rw [h4, hU, Matrix.det_mul, hdU, mul_zpow, mul_comm]

/- English proof (translation)
Rewrite using `[lb_D, Matrix.det_diagonal, isUnit_iff_ne_zero, Finset.prod_ne_zero_iff]`. Introduce `a _`. Use `split_ifs`. Conclude with `inv_ne_zero hc`. Conclude with `one_ne_zero`.
-/
theorem lb_D_det {K : Type*} [Field K] (k r : ℕ) (c : K) (hc : c ≠ 0) : IsUnit (lb_D k r c).det := by
  rw [lb_D, Matrix.det_diagonal, isUnit_iff_ne_zero, Finset.prod_ne_zero_iff]
  intro a _
  split_ifs
  · exact inv_ne_zero hc
  · exact one_ne_zero

/- English proof (translation)
Establish `hgD : IsUnit (g * lb_D (m + 1) r (algebraMap O Kf w)).det`. Rewrite using `[Matrix.det_mul]`. Conclude with `hg.mul (lb_D_det _ _ _ hw)`. Unfold `H0 at hF ⊢`. Rewrite `hF`, the goal using `[if_pos hlam]`.

Establish `h1 : F ∈ nablaLTw O Kf m lam g` using `(iInf₂_le g ⟨hg, rfl⟩ : _ ≤ nablaLTw O Kf m lam g) hF`. Establish `h2` using `lb_P O Kf hinj m r lam hlam w hw g hg F h1`. Conclude with `(le_iInf₂ fun h hh => lb_indep O Kf hinj m lam _ h hgD hh.1 hh.2 : nablaLTw O Kf m lam (g * lb_D (m + 1) r (algebraMap O Kf w)) ≤ _) h2`.
-/
theorem lb_pos (O Kf : Type) [CommRing O] [IsDomain O] [Field Kf] [Algebra O Kf]
    (hinj : Function.Injective (algebraMap O Kf)) (m r : ℕ) (lam : Fin (m + 1) → ℤ) (hlam : Antitone lam)
    (w : O) (hw : algebraMap O Kf w ≠ 0) (g : Matrix (Fin (m + 1)) (Fin (m + 1)) Kf) (hg : IsUnit g.det)
    (F : MvPolynomial (Fin (m + 1) × Fin (m + 1)) Kf) (hF : F ∈ H0 O m lam (colSpan O g)) :
    (algebraMap O Kf w ^ (∑ i : Fin (m + 1) with i.val < r, lam i)) • F ∈
      H0 O m lam (colSpan O (g * lb_D (m + 1) r (algebraMap O Kf w))) := by
  have hgD : IsUnit (g * lb_D (m + 1) r (algebraMap O Kf w)).det := by
    rw [Matrix.det_mul]; exact hg.mul (lb_D_det _ _ _ hw)
  unfold H0 at hF ⊢
  rw [if_pos hlam] at hF ⊢
  have h1 : F ∈ nablaLTw O Kf m lam g := (iInf₂_le g ⟨hg, rfl⟩ : _ ≤ nablaLTw O Kf m lam g) hF
  have h2 := lb_P O Kf hinj m r lam hlam w hw g hg F h1
  exact (le_iInf₂ fun h hh => lb_indep O Kf hinj m lam _ h hgD hh.1 hh.2 :
    nablaLTw O Kf m lam (g * lb_D (m + 1) r (algebraMap O Kf w)) ≤ _) h2

variable {p : ℕ}

def RestEdgeLat (G : GAtP p) (v : Fin G.P.nV) : Prop :=
  ∀ e : Edge (G.P.W v) (G.P.Qq v) (G.P.m + 1), IsEdge p (G.P.n' v) G.P.r e →
    ∃ gs : ℕ → Matrix (Fin (G.P.m + 1)) (Fin (G.P.m + 1)) G.Kf, (∀ s, IsUnit (gs s).det) ∧
      (∀ s, extO G.O (G.P.ι v) (G.P.σ v) s e.src = colSpan G.O (gs s)) ∧
      (∀ s, LeAt p (G.P.ι v) (G.P.σ v) G.P.w s e =
        colSpan G.O (gs s * lb_D (G.P.m + 1) G.P.r (algebraMap G.O G.Kf G.P.w))) ∧
      (∀ s, extO G.O (G.P.ι v) (G.P.σ v) s e.tgt =
        colSpan G.O (gs s * lb_D (G.P.m + 1) G.P.r (algebraMap G.O G.Kf G.P.w) *
          lb_D (G.P.m + 1) G.P.r (algebraMap G.O G.Kf G.P.w)))

/- English proof (translation)
The claim follows from `haveI := (G.P.setting v).frac_O IsFractionRing.injective G.O G.Kf`.
-/
theorem lb_inj (G : GAtP p) (v : Fin G.P.nV) : Function.Injective (algebraMap G.O G.Kf) :=
  haveI := (G.P.setting v).frac_O
  IsFractionRing.injective G.O G.Kf

/- English proof (translation)
Take `⟨gs, hgs, h1, h2, h3⟩` from `hE e he`. Establish `hw` using `ch_w_ne_zero G v`. Establish `hA : ∏ s : Fin (G.P.n' v), algebraMap G.O G.Kf G.P.w ^ (∑ i : Fin (G.P.m + 1) with i.val < G.P.r, lamAt (G.P.lam0 v) s i) = algebraMap G.O G.Kf G.P.w ^ Ar G.P.r (G.P.lam0 v)` using `lb_zpow_sum _ hw _ _`. Establish `hgD : ∀ s, IsUnit (gs s * lb_D (G.P.m + 1) G.P.r (algebraMap G.O G.Kf G.P.w)).det`. Introduce `s`.

Rewrite using `[Matrix.det_mul]`. Conclude with `(hgs s).mul (lb_D_det _ _ _ hw)`. Prove the components needed by the constructor for the conclusion. Introduce `P hP`. Rewrite using `[← hA]`.

Use `lb_tensor G.O G.Kf _ _ _ (fun s F hF => ?_) P hP` and prove the remaining obligations. Use `beta_reduce at hF ⊢`. Rewrite `hF` using `[h1]`. Rewrite using `[h2]`. Conclude with `lb_pos G.O G.Kf (lb_inj G v) G.P.m G.P.r _ (kp_lamAt_antitone _ (G.P.dom v) s) G.P.w hw _ (hgs _) F hF`.

Introduce `P hP`. Rewrite using `[← hA]`. Use `lb_tensor G.O G.Kf _ _ _ (fun s F hF => ?_) P hP` and prove the remaining obligations. Use `beta_reduce at hF ⊢`. Rewrite `hF` using `[h2]`.

Rewrite using `[h3]`. Conclude with `lb_pos G.O G.Kf (lb_inj G v) G.P.m G.P.r _ (kp_lamAt_antitone _ (G.P.dom v) s) G.P.w hw _ (hgD _) F hF`.
-/
theorem lb_steps (G : GAtP p) (v : Fin G.P.nV) (hE : RestEdgeLat G v)
    (e : Edge (G.P.W v) (G.P.Qq v) (G.P.m + 1)) (he : IsEdge p (G.P.n' v) G.P.r e) :
    (∀ P ∈ Hten G.O (G.P.lam0 v) (fun s => extO G.O (G.P.ι v) (G.P.σ v) s.val e.src),
      (algebraMap G.O G.Kf G.P.w ^ Ar G.P.r (G.P.lam0 v)) • P ∈
        Hten G.O (G.P.lam0 v) (fun s => LeAt p (G.P.ι v) (G.P.σ v) G.P.w s.val e)) ∧
    (∀ P ∈ Hten G.O (G.P.lam0 v) (fun s => LeAt p (G.P.ι v) (G.P.σ v) G.P.w s.val e),
      (algebraMap G.O G.Kf G.P.w ^ Ar G.P.r (G.P.lam0 v)) • P ∈
        Hten G.O (G.P.lam0 v) (fun s => extO G.O (G.P.ι v) (G.P.σ v) s.val e.tgt)) := by
  obtain ⟨gs, hgs, h1, h2, h3⟩ := hE e he
  have hw := ch_w_ne_zero G v
  have hA : ∏ s : Fin (G.P.n' v), algebraMap G.O G.Kf G.P.w ^
      (∑ i : Fin (G.P.m + 1) with i.val < G.P.r, lamAt (G.P.lam0 v) s i) =
      algebraMap G.O G.Kf G.P.w ^ Ar G.P.r (G.P.lam0 v) := lb_zpow_sum _ hw _ _
  have hgD : ∀ s, IsUnit (gs s * lb_D (G.P.m + 1) G.P.r (algebraMap G.O G.Kf G.P.w)).det := by
    intro s
    rw [Matrix.det_mul]; exact (hgs s).mul (lb_D_det _ _ _ hw)
  constructor
  · intro P hP
    rw [← hA]
    refine lb_tensor G.O G.Kf _ _ _ (fun s F hF => ?_) P hP
    beta_reduce at hF ⊢
    rw [h1] at hF
    rw [h2]
    exact lb_pos G.O G.Kf (lb_inj G v) G.P.m G.P.r _ (kp_lamAt_antitone _ (G.P.dom v) s) G.P.w hw _ (hgs _) F hF
  · intro P hP
    rw [← hA]
    refine lb_tensor G.O G.Kf _ _ _ (fun s F hF => ?_) P hP
    beta_reduce at hF ⊢
    rw [h2] at hF
    rw [h3]
    exact lb_pos G.O G.Kf (lb_inj G v) G.P.m G.P.r _ (kp_lamAt_antitone _ (G.P.dom v) s) G.P.w hw _ (hgD _) F hF

/- English proof (translation)
Introduce `x hx`. Establish `hw` using `ch_w_ne_zero G v`. Use `⟨(algebraMap G.O G.Kf G.P.w ^ Ar G.P.r (G.P.lam0 v)) • x, (lb_steps G v hE e he).1 _ hx, ?_⟩` and prove the remaining obligations. Use `show (algebraMap G.O G.Kf G.P.w ^ (-Ar G.P.r (G.P.lam0 v))) • (algebraMap G.O G.Kf G.P.w ^ Ar G.P.r (G.P.lam0 v)) • x = x`. Rewrite using `[smul_smul, ← zpow_add₀ hw, neg_add_cancel, zpow_zero, one_smul]`.
-/
theorem lb_H_le_Re (G : GAtP p) (v : Fin G.P.nV) (hE : RestEdgeLat G v)
    (e : Edge (G.P.W v) (G.P.Qq v) (G.P.m + 1)) (he : IsEdge p (G.P.n' v) G.P.r e) :
    HL (O := G.O) (G.P.ι v) (G.P.σ v) (G.P.lam0 v) e.src ≤
      Re p (G.P.ι v) (G.P.σ v) G.P.w G.P.r (G.P.lam0 v) e := by
  intro x hx
  have hw := ch_w_ne_zero G v
  refine ⟨(algebraMap G.O G.Kf G.P.w ^ Ar G.P.r (G.P.lam0 v)) • x, (lb_steps G v hE e he).1 _ hx, ?_⟩
  show (algebraMap G.O G.Kf G.P.w ^ (-Ar G.P.r (G.P.lam0 v))) •
    (algebraMap G.O G.Kf G.P.w ^ Ar G.P.r (G.P.lam0 v)) • x = x
  rw [smul_smul, ← zpow_add₀ hw, neg_add_cancel, zpow_zero, one_smul]

/- English proof (translation)
Introduce `φ hφ`. Establish `hw` using `ch_w_ne_zero G v`. Use `⟨(algebraMap G.O G.Kf G.P.w ^ Ar G.P.r (G.P.lam0 v)) • φ, ?_, ?_⟩` and prove the remaining obligations. Introduce `z hz`. Establish `h1` using `hφ ((algebraMap G.O G.Kf G.P.w ^ Ar G.P.r (G.P.lam0 v)) • z) ((lb_steps G v hE e he).2 _ hz)`.

Rewrite `h1` using `[map_smul]`. Conclude with `h1`. Use `show (algebraMap G.O G.Kf G.P.w ^ (-Ar G.P.r (G.P.lam0 v))) • (algebraMap G.O G.Kf G.P.w ^ Ar G.P.r (G.P.lam0 v)) • φ = φ`. Rewrite using `[smul_smul, ← zpow_add₀ hw, neg_add_cancel, zpow_zero, one_smul]`.
-/
theorem lb_Hdual_le_Re' (G : GAtP p) (v : Fin G.P.nV) (hE : RestEdgeLat G v)
    (e : Edge (G.P.W v) (G.P.Qq v) (G.P.m + 1)) (he : IsEdge p (G.P.n' v) G.P.r e) :
    dualLat G.O G.Kf (HL (O := G.O) (G.P.ι v) (G.P.σ v) (G.P.lam0 v) e.tgt) ≤
      Re' p (G.P.ι v) (G.P.σ v) G.P.w G.P.r (G.P.lam0 v) e := by
  intro φ hφ
  have hw := ch_w_ne_zero G v
  refine ⟨(algebraMap G.O G.Kf G.P.w ^ Ar G.P.r (G.P.lam0 v)) • φ, ?_, ?_⟩
  · intro z hz
    have h1 := hφ ((algebraMap G.O G.Kf G.P.w ^ Ar G.P.r (G.P.lam0 v)) • z) ((lb_steps G v hE e he).2 _ hz)
    rw [map_smul] at h1
    exact h1
  · show (algebraMap G.O G.Kf G.P.w ^ (-Ar G.P.r (G.P.lam0 v))) •
      (algebraMap G.O G.Kf G.P.w ^ Ar G.P.r (G.P.lam0 v)) • φ = φ
    rw [smul_smul, ← zpow_add₀ hw, neg_add_cancel, zpow_zero, one_smul]

/- English proof (translation)
Establish `key : colSpan O (M * Matrix.diagonal d) ≤ (colSpan O M).comap (a • (LinearMap.id : (Fin k → Kf) →ₗ[O] (Fin k → Kf)))`. Unfold `colSpan`. Rewrite using `[Submodule.span_le]`. Introduce and unpack `_ ⟨j, rfl⟩`. Establish `h1 : a • (fun i => (M * Matrix.diagonal d) i j) = o j • (fun i => M i j)`.

Use function extensionality and compare the values at `i`. Simplify using `only [Pi.smul_apply, Matrix.mul_diagonal, Algebra.smul_def]`. Rewrite using `[← h j]`. Expand and normalize the polynomial expressions, which then agree. Use `show a • (fun i => (M * Matrix.diagonal d) i j) ∈ Submodule.span O (Set.range fun c : Fin k => fun i => M i c)`.

Rewrite using `[h1]`. Conclude with `Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)`. Conclude with `fun x hx => key hx`.
-/
theorem lb_col {O Kf : Type} [CommRing O] [Field Kf] [Algebra O Kf] {k : ℕ} (M : Matrix (Fin k) (Fin k) Kf)
    (d : Fin k → Kf) (o : Fin k → O) (a : O) (h : ∀ j, algebraMap O Kf a * d j = algebraMap O Kf (o j)) :
    ∀ x ∈ colSpan O (M * Matrix.diagonal d), a • x ∈ colSpan O M := by
  have key : colSpan O (M * Matrix.diagonal d) ≤
      (colSpan O M).comap (a • (LinearMap.id : (Fin k → Kf) →ₗ[O] (Fin k → Kf))) := by
    unfold colSpan
    rw [Submodule.span_le]
    rintro _ ⟨j, rfl⟩
    have h1 : a • (fun i => (M * Matrix.diagonal d) i j) = o j • (fun i => M i j) := by
      funext i
      simp only [Pi.smul_apply, Matrix.mul_diagonal, Algebra.smul_def]
      rw [← h j]; ring
    show a • (fun i => (M * Matrix.diagonal d) i j) ∈
      Submodule.span O (Set.range fun c : Fin k => fun i => M i c)
    rw [h1]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)
  exact fun x hx => key hx

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem lb_tw_apply {Qq Kf : Type} [Field Qq] [Field Kf] (ι : Qq →+* Kf) (σ : Qq ≃+* Qq) (s : ℕ) {k : ℕ}
    (g : Matrix (Fin k) (Fin k) Qq) (i j : Fin k) : la_tw ι σ s g i j = ι ((σ ^ s) (g i j)) := rfl

/- English proof (translation)
Use `show G.P.ι v ((G.P.σ v ^ s) ((p : G.P.W v) • x i)) = _`. Rewrite using `[Algebra.smul_def, map_natCast, map_mul, map_mul, map_natCast, map_natCast]`.
-/
theorem lb_tw_p (G : GAtP p) (v : Fin G.P.nV) (s : ℕ) (x : Fin (G.P.m + 1) → G.P.Qq v) (i : Fin (G.P.m + 1)) :
    twistVec (G.P.ι v) (G.P.σ v) s ((p : G.P.W v) • x) i = (p : G.Kf) * G.P.ι v ((G.P.σ v ^ s) (x i)) := by
  show G.P.ι v ((G.P.σ v ^ s) ((p : G.P.W v) • x i)) = _
  rw [Algebra.smul_def, map_natCast, map_mul, map_mul, map_natCast, map_natCast]

def RestEdgeBasis (G : GAtP p) (v : Fin G.P.nV) : Prop :=
  ∀ e : Edge (G.P.W v) (G.P.Qq v) (G.P.m + 1), IsEdge p (G.P.n' v) G.P.r e →
    ∃ g : Matrix (Fin (G.P.m + 1)) (Fin (G.P.m + 1)) (G.P.Qq v), IsEdgeBasis p G.P.r e g

/- English proof (translation)
Introduce `e he`. Take `⟨g, hg, hsrc, htgt⟩` from `hB e he`. Unfold `lb_D`. Use `set c : G.Kf := algebraMap G.O G.Kf G.P.w with hc`. Establish `hw : c ≠ 0` using `ch_w_ne_zero G v`.

Establish `hpK : (p : G.Kf) = c ^ 2` using `nt_p_eq G v`. Establish `hpK0 : (p : G.Kf) ≠ 0` using `by rw [hpK]; exact pow_ne_zero _ hw`. Establish `hpQ0 : (p : G.P.Qq v) ≠ 0`. Introduce `h0`. Apply `hpK0` to reduce the goal to its premises.

Use `congrArg (G.P.ι v) h0` as an intermediate fact. Simplify using `using this`. Use `set dK : Fin (G.P.m + 1) → G.Kf := fun a => if a.val < G.P.r then c⁻¹ else 1 with hdK`. Use `set dQ : Fin (G.P.m + 1) → G.P.Qq v := fun a => if a.val < G.P.r then ((p : G.P.Qq v))⁻¹ else 1 with hdQ`. Establish `hDD : ∀ s, la_tw (G.P.ι v) (G.P.σ v) s (g * Matrix.diagonal dQ) = la_tw (G.P.ι v) (G.P.σ v) s g * Matrix.diagonal dK * Matrix.diagonal dK`.

Introduce `s`. Use extensionality with `i j`. Rewrite using `[Matrix.mul_assoc, Matrix.diagonal_mul_diagonal, Matrix.mul_diagonal, lb_tw_apply, lb_tw_apply, Matrix.mul_diagonal, map_mul, map_mul]`. Use `congr 1`. Simplify using `only [hdQ, hdK]`.

Use `split_ifs`. Rewrite using `[map_inv₀, map_inv₀, map_natCast, map_natCast, hpK, pow_two, mul_inv]`. Simplify using the standard rewrite rules. Establish `e1 : ∀ s, extO G.O (G.P.ι v) (G.P.σ v) s e.src = colSpan G.O (la_tw (G.P.ι v) (G.P.σ v) s g)` using `fun s => by rw [hsrc]; exact la_extO_G G v s g`. Establish `e3 : ∀ s, extO G.O (G.P.ι v) (G.P.σ v) s e.tgt = colSpan G.O (la_tw (G.P.ι v) (G.P.σ v) s g * Matrix.diagonal dK * Matrix.diagonal dK)` using `fun s => by rw [htgt, la_extO_G, hDD]`.

Use `⟨fun s => la_tw (G.P.ι v) (G.P.σ v) s g, fun s => la_tw_det _ _ s g hg, e1, ?_, e3⟩` and prove the remaining obligations. Introduce `s`. Use `set gK := la_tw (G.P.ι v) (G.P.σ v) s g with hgK`. Apply `le_antisymm` to reduce the goal to its premises. Unfold `LeAt`.

Use `sup_le ?_ ?_` and prove the remaining obligations. Rewrite using `[e1]`. Introduce `x hx`. Establish `h1 : gK = gK * Matrix.diagonal dK * Matrix.diagonal (fun a : Fin (G.P.m + 1) => if a.val < G.P.r then c else 1)`. Rewrite using `[Matrix.mul_assoc, Matrix.diagonal_mul_diagonal]`.

Establish `h2 : (fun a : Fin (G.P.m + 1) => dK a * (if a.val < G.P.r then c else 1)) = fun _ => 1`. Use function extensionality and compare the values at `a`. Simplify using `only [hdK]`. Use `split_ifs`. Conclude with `inv_mul_cancel₀ hw`.

Simplify using the standard rewrite rules. Rewrite using `[h2, Matrix.diagonal_one, Matrix.mul_one]`. Establish `hx' : x ∈ colSpan G.O gK` using `hx`. Rewrite `hx'` using `[h1]`. Apply the tactic sequence `have h3 := lb_col (gK * Matrix.diagonal dK) _ (fun a : Fin (G.P.m + 1) => if a.val < G.P.r then G.P.w else 1) 1 (by intro j; split_ifs <;> simp [hc]) x hx'`.

Rewrite `h3` using `[one_smul]`. Conclude with `h3`. Rewrite using `[Submodule.span_le]`. Introduce and unpack `_ ⟨x, hx, rfl⟩`. Establish `h1 : c⁻¹ • twistVec (G.P.ι v) (G.P.σ v) s ((p : G.P.W v) • x) = G.P.w • twistVec (G.P.ι v) (G.P.σ v) s x`.

Use function extensionality and compare the values at `i`. Rewrite using `[Pi.smul_apply, Pi.smul_apply, lb_tw_p, smul_eq_mul, Algebra.smul_def, ← hc, hpK]`. Use `show c⁻¹ * (c ^ 2 * _) = c * (G.P.ι v) ((G.P.σ v ^ s) (x i))`. Clear the denominators using the available nonvanishing facts. Establish `h2 : twistVec (G.P.ι v) (G.P.σ v) s x ∈ colSpan G.O (gK * Matrix.diagonal dK * Matrix.diagonal dK)`.

Rewrite using `[← e3]`. Conclude with `Submodule.subset_span ⟨x, hx, rfl⟩`. Use `show c⁻¹ • twistVec (G.P.ι v) (G.P.σ v) s ((p : G.P.W v) • x) ∈ _`. Rewrite using `[h1]`. Conclude with `lb_col (gK * Matrix.diagonal dK) dK (fun a : Fin (G.P.m + 1) => if a.val < G.P.r then 1 else G.P.w) G.P.w (by`.

Introduce `j`. Simplify using `only [hdK]`. Use `split_ifs`. Rewrite using `[← hc, mul_inv_cancel₀ hw, map_one]`. Rewrite using `[mul_one]) _ h2`.

Unfold `colSpan`. Rewrite using `[Submodule.span_le]`. Introduce and unpack `_ ⟨j, rfl⟩`. Unfold `LeAt`. Distinguish the cases in `hj : j.val < G.P.r`.

Apply `Submodule.mem_sup_right` to reduce the goal to its premises. Apply `Submodule.subset_span` to reduce the goal to its premises. Use `⟨fun i => (g * Matrix.diagonal dQ) i j, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[htgt]`. Conclude with `Submodule.subset_span ⟨j, rfl⟩`.

Use function extensionality and compare the values at `i show c⁻¹ • twistVec (G.P.ι v) (G.P.σ v) s ((p : G.P.W v) • fun i => (g * Matrix.diagonal dQ) i j) i = (gK * Matrix.diagonal dK) i j`. Rewrite using `[lb_tw_p, Matrix.mul_diagonal, Matrix.mul_diagonal, smul_eq_mul, hgK, lb_tw_apply]`. Simplify using `only [hdQ, hdK, hj, if_true, map_mul, map_inv₀, map_natCast]`. Clear the denominators using the available nonvanishing facts. Apply `Submodule.mem_sup_left` to reduce the goal to its premises.

Apply `Submodule.subset_span` to reduce the goal to its premises. Use `⟨fun i => g i j, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[hsrc]`. Conclude with `Submodule.subset_span ⟨j, rfl⟩`. Use function extensionality and compare the values at `i`.

Simplify using `only [twistVec, Matrix.mul_diagonal, hdK, hj, if_false, mul_one, lb_tw_apply]`.
-/
theorem lb_edgeLat_of_basis (G : GAtP p) (v : Fin G.P.nV) (hB : RestEdgeBasis G v) : RestEdgeLat G v := by
  intro e he
  obtain ⟨g, hg, hsrc, htgt⟩ := hB e he
  unfold lb_D
  set c : G.Kf := algebraMap G.O G.Kf G.P.w with hc
  have hw : c ≠ 0 := ch_w_ne_zero G v
  have hpK : (p : G.Kf) = c ^ 2 := nt_p_eq G v
  have hpK0 : (p : G.Kf) ≠ 0 := by rw [hpK]; exact pow_ne_zero _ hw
  have hpQ0 : (p : G.P.Qq v) ≠ 0 := by
    intro h0
    apply hpK0
    have := congrArg (G.P.ι v) h0
    simpa using this
  set dK : Fin (G.P.m + 1) → G.Kf := fun a => if a.val < G.P.r then c⁻¹ else 1 with hdK
  set dQ : Fin (G.P.m + 1) → G.P.Qq v := fun a => if a.val < G.P.r then ((p : G.P.Qq v))⁻¹ else 1 with hdQ
  have hDD : ∀ s, la_tw (G.P.ι v) (G.P.σ v) s (g * Matrix.diagonal dQ) =
      la_tw (G.P.ι v) (G.P.σ v) s g * Matrix.diagonal dK * Matrix.diagonal dK := by
    intro s
    ext i j
    rw [Matrix.mul_assoc, Matrix.diagonal_mul_diagonal, Matrix.mul_diagonal, lb_tw_apply, lb_tw_apply,
      Matrix.mul_diagonal, map_mul, map_mul]
    congr 1
    simp only [hdQ, hdK]
    split_ifs
    · rw [map_inv₀, map_inv₀, map_natCast, map_natCast, hpK, pow_two, mul_inv]
    · simp
  have e1 : ∀ s, extO G.O (G.P.ι v) (G.P.σ v) s e.src = colSpan G.O (la_tw (G.P.ι v) (G.P.σ v) s g) :=
    fun s => by rw [hsrc]; exact la_extO_G G v s g
  have e3 : ∀ s, extO G.O (G.P.ι v) (G.P.σ v) s e.tgt =
      colSpan G.O (la_tw (G.P.ι v) (G.P.σ v) s g * Matrix.diagonal dK * Matrix.diagonal dK) :=
    fun s => by rw [htgt, la_extO_G, hDD]
  refine ⟨fun s => la_tw (G.P.ι v) (G.P.σ v) s g, fun s => la_tw_det _ _ s g hg, e1, ?_, e3⟩
  intro s
  set gK := la_tw (G.P.ι v) (G.P.σ v) s g with hgK
  apply le_antisymm
  · unfold LeAt
    refine sup_le ?_ ?_
    · rw [e1]
      intro x hx
      have h1 : gK = gK * Matrix.diagonal dK *
          Matrix.diagonal (fun a : Fin (G.P.m + 1) => if a.val < G.P.r then c else 1) := by
        rw [Matrix.mul_assoc, Matrix.diagonal_mul_diagonal]
        have h2 : (fun a : Fin (G.P.m + 1) => dK a * (if a.val < G.P.r then c else 1)) = fun _ => 1 := by
          funext a
          simp only [hdK]
          split_ifs
          · exact inv_mul_cancel₀ hw
          · simp
        rw [h2, Matrix.diagonal_one, Matrix.mul_one]
      have hx' : x ∈ colSpan G.O gK := hx
      rw [h1] at hx'
      have h3 := lb_col (gK * Matrix.diagonal dK) _
        (fun a : Fin (G.P.m + 1) => if a.val < G.P.r then G.P.w else 1) 1
        (by intro j; split_ifs <;> simp [hc]) x hx'
      rw [one_smul] at h3
      exact h3
    · rw [Submodule.span_le]
      rintro _ ⟨x, hx, rfl⟩
      have h1 : c⁻¹ • twistVec (G.P.ι v) (G.P.σ v) s ((p : G.P.W v) • x) =
          G.P.w • twistVec (G.P.ι v) (G.P.σ v) s x := by
        funext i
        rw [Pi.smul_apply, Pi.smul_apply, lb_tw_p, smul_eq_mul, Algebra.smul_def, ← hc, hpK]
        show c⁻¹ * (c ^ 2 * _) = c * (G.P.ι v) ((G.P.σ v ^ s) (x i))
        field_simp
      have h2 : twistVec (G.P.ι v) (G.P.σ v) s x ∈
          colSpan G.O (gK * Matrix.diagonal dK * Matrix.diagonal dK) := by
        rw [← e3]; exact Submodule.subset_span ⟨x, hx, rfl⟩
      show c⁻¹ • twistVec (G.P.ι v) (G.P.σ v) s ((p : G.P.W v) • x) ∈ _
      rw [h1]
      exact lb_col (gK * Matrix.diagonal dK) dK
        (fun a : Fin (G.P.m + 1) => if a.val < G.P.r then 1 else G.P.w) G.P.w
        (by
          intro j
          simp only [hdK]
          split_ifs
          · rw [← hc, mul_inv_cancel₀ hw, map_one]
          · rw [mul_one]) _ h2
  · unfold colSpan
    rw [Submodule.span_le]
    rintro _ ⟨j, rfl⟩
    unfold LeAt
    by_cases hj : j.val < G.P.r
    · apply Submodule.mem_sup_right
      apply Submodule.subset_span
      refine ⟨fun i => (g * Matrix.diagonal dQ) i j, ?_, ?_⟩
      · rw [htgt]; exact Submodule.subset_span ⟨j, rfl⟩
      · funext i
        show c⁻¹ • twistVec (G.P.ι v) (G.P.σ v) s
          ((p : G.P.W v) • fun i => (g * Matrix.diagonal dQ) i j) i = (gK * Matrix.diagonal dK) i j
        rw [lb_tw_p, Matrix.mul_diagonal, Matrix.mul_diagonal, smul_eq_mul, hgK, lb_tw_apply]
        simp only [hdQ, hdK, hj, if_true, map_mul, map_inv₀, map_natCast]
        field_simp
    · apply Submodule.mem_sup_left
      apply Submodule.subset_span
      refine ⟨fun i => g i j, ?_, ?_⟩
      · rw [hsrc]; exact Submodule.subset_span ⟨j, rfl⟩
      · funext i
        simp only [twistVec, Matrix.mul_diagonal, hdK, hj, if_false, mul_one, lb_tw_apply]

/- English proof (translation)
Introduce `Lv hLv` and use `⟨la_H_le_V G v Lv hLv, fun e he hs => hs ▸ lb_H_le_Re G v (lb_edgeLat_of_basis G v hB) e he, fun e he ht => ht ▸ lb_Hdual_le_Re' G v (lb_edgeLat_of_basis G v hB) e he, la_reflexive G v Lv hLv⟩`.
-/
theorem restLocD_of_edgeBasis (G : GAtP p) (v : Fin G.P.nV) (hB : RestEdgeBasis G v) : RestLocD G v :=
  fun Lv hLv => ⟨la_H_le_V G v Lv hLv,
    fun e he hs => hs ▸ lb_H_le_Re G v (lb_edgeLat_of_basis G v hB) e he,
    fun e he ht => ht ▸ lb_Hdual_le_Re' G v (lb_edgeLat_of_basis G v hB) e he,
    la_reflexive G v Lv hLv⟩

end Formalism.MainNotions.G.LatticeSystems

namespace Formalism.MainNotions.G.LatticeSystems

open Formalism.MainNotions.G

/- English proof (translation)
Establish `hli0 : LinearIndependent W (fun j : Fin k => (p : W) • Pi.basisFun W (Fin k) j)`. Rewrite using `[Fintype.linearIndependent_iff]`. Introduce `c hc i`. Establish `h1` using `congrFun hc i`. Simplify using `only [Finset.sum_apply, Pi.smul_apply, Pi.basisFun_apply, Pi.single_apply, smul_eq_mul, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true, Pi.zero_apply] at h1`.

Conclude with `(mul_eq_zero.1 h1).resolve_right hp0`. Establish `hrank : Module.finrank W N = Module.finrank W (Fin k → W)`. Apply `le_antisymm (Submodule.finrank_le N)` to reduce the goal to its premises. Establish `hli : LinearIndependent W (fun j : Fin k => (⟨(p : W) • Pi.basisFun W (Fin k) j, hpN _⟩ : N))` using `LinearIndependent.of_comp N.subtype hli0`. Establish `h3` using `hli.fintype_card_le_finrank`.

Simplify using `using h3`. Take `⟨bT, hbT⟩ : ∃ bT, bT = Submodule.smithNormalFormTopBasis (Pi.basisFun W (Fin k)) hrank` from `⟨_, rfl⟩`. Take `⟨bB, hbB⟩ : ∃ bB, bB = Submodule.smithNormalFormBotBasis (Pi.basisFun W (Fin k)) hrank` from `⟨_, rfl⟩`. Take `⟨a, ha⟩ : ∃ a, a = Submodule.smithNormalFormCoeffs (Pi.basisFun W (Fin k)) hrank` from `⟨_, rfl⟩`. Establish `hsnf : ∀ i, (bB i : Fin k → W) = a i • bT i`.

Introduce `i`. Rewrite using `[hbB, ha, hbT]`. Conclude with `Submodule.smithNormalFormBotBasis_def (Pi.basisFun W (Fin k)) hrank i`. Use `⟨bT, a, ?_, ?_, ?_⟩` and prove the remaining obligations. Establish `h3` using `congrArg (Submodule.map N.subtype) bB.span_eq`.

Rewrite `h3` using `[Submodule.map_span, Submodule.map_top, Submodule.range_subtype, ← Set.range_comp]`. Rewrite using `[← h3]`. Use `congr 2`. Use function extensionality and compare the values at `i`. Conclude with `hsnf i`.

Introduce `i`. Establish `hmem` using `hpN (bT i)`. Establish `h1 : (p : W) • bT i = ∑ j, (bB.repr ⟨_, hmem⟩ j) • (a j • bT j)`. Establish `h2` using `congrArg N.subtype (bB.sum_repr ⟨_, hmem⟩)`. Simplify using `only [map_sum, map_smul, Submodule.subtype_apply, hsnf] at h2`.

Conclude with `h2.symm`. Establish `h3` using `congrArg (fun z => bT.repr z i) h1`. Simplify using `only [map_smul, map_sum, Module.Basis.repr_self, Finsupp.smul_apply, Finsupp.single_apply, Finsupp.coe_finsetSum, Finset.sum_apply, smul_eq_mul, if_true, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ] at h3`. Conclude with `⟨bB.repr ⟨_, hmem⟩ i, h3.trans (mul_comm _ _)⟩`. Rewrite using `[Nat.card_congr (Submodule.quotientEquivPiSpan N (Pi.basisFun W (Fin k)) hrank).toEquiv, Nat.card_pi, ha]`.
-/
theorem smith_normal_form_card {W : Type} [CommRing W] [IsDomain W] [IsPrincipalIdealRing W] (p k : ℕ) (hp0 : (p : W) ≠ 0)
    (N : Submodule W (Fin k → W)) (hpN : ∀ x, (p : W) • x ∈ N) :
    ∃ (bT : Module.Basis (Fin k) W (Fin k → W)) (a : Fin k → W),
      N = Submodule.span W (Set.range fun i => a i • bT i) ∧ (∀ i, a i ∣ (p : W)) ∧
      Nat.card ((Fin k → W) ⧸ N) = ∏ i, Nat.card (W ⧸ Ideal.span {a i}) := by
  classical
  have hli0 : LinearIndependent W (fun j : Fin k => (p : W) • Pi.basisFun W (Fin k) j) := by
    rw [Fintype.linearIndependent_iff]
    intro c hc i
    have h1 := congrFun hc i
    simp only [Finset.sum_apply, Pi.smul_apply, Pi.basisFun_apply, Pi.single_apply, smul_eq_mul, mul_ite,
      mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true, Pi.zero_apply] at h1
    exact (mul_eq_zero.1 h1).resolve_right hp0
  have hrank : Module.finrank W N = Module.finrank W (Fin k → W) := by
    apply le_antisymm (Submodule.finrank_le N)
    have hli : LinearIndependent W
        (fun j : Fin k => (⟨(p : W) • Pi.basisFun W (Fin k) j, hpN _⟩ : N)) :=
      LinearIndependent.of_comp N.subtype hli0
    have h3 := hli.fintype_card_le_finrank
    simpa using h3
  obtain ⟨bT, hbT⟩ : ∃ bT, bT = Submodule.smithNormalFormTopBasis (Pi.basisFun W (Fin k)) hrank := ⟨_, rfl⟩
  obtain ⟨bB, hbB⟩ : ∃ bB, bB = Submodule.smithNormalFormBotBasis (Pi.basisFun W (Fin k)) hrank := ⟨_, rfl⟩
  obtain ⟨a, ha⟩ : ∃ a, a = Submodule.smithNormalFormCoeffs (Pi.basisFun W (Fin k)) hrank := ⟨_, rfl⟩
  have hsnf : ∀ i, (bB i : Fin k → W) = a i • bT i := by
    intro i
    rw [hbB, ha, hbT]
    exact Submodule.smithNormalFormBotBasis_def (Pi.basisFun W (Fin k)) hrank i
  refine ⟨bT, a, ?_, ?_, ?_⟩
  · have h3 := congrArg (Submodule.map N.subtype) bB.span_eq
    rw [Submodule.map_span, Submodule.map_top, Submodule.range_subtype, ← Set.range_comp] at h3
    rw [← h3]
    congr 2
    funext i
    exact hsnf i
  · intro i
    have hmem := hpN (bT i)
    have h1 : (p : W) • bT i = ∑ j, (bB.repr ⟨_, hmem⟩ j) • (a j • bT j) := by
      have h2 := congrArg N.subtype (bB.sum_repr ⟨_, hmem⟩)
      simp only [map_sum, map_smul, Submodule.subtype_apply, hsnf] at h2
      exact h2.symm
    have h3 := congrArg (fun z => bT.repr z i) h1
    simp only [map_smul, map_sum, Module.Basis.repr_self, Finsupp.smul_apply, Finsupp.single_apply,
      Finsupp.coe_finsetSum, Finset.sum_apply, smul_eq_mul, if_true, mul_ite, mul_one, mul_zero,
      Finset.sum_ite_eq', Finset.mem_univ] at h3
    exact ⟨bB.repr ⟨_, hmem⟩ i, h3.trans (mul_comm _ _)⟩
  · rw [Nat.card_congr (Submodule.quotientEquivPiSpan N (Pi.basisFun W (Fin k)) hrank).toEquiv, Nat.card_pi, ha]

/- English proof (translation)
Take `⟨-, ⟨gL, hgL, hL⟩, hle, hpL, -⟩` from `he`. Take `⟨φ, hφ⟩ : ∃ φ : (Fin k → W) →ₗ[W] (Fin k → Qq), φ = Fintype.linearCombination W (fun (c : Fin k) (i : Fin k) => gL i c)` from `⟨_, rfl⟩`. Establish `hφr : LinearMap.range φ = e.tgt`. Rewrite using `[hL, hφ]`. Conclude with `Fintype.range_linearCombination W _`.

Establish `hφi : Function.Injective φ`. Rewrite using `[injective_iff_map_eq_zero]`. Introduce `x hx`. Establish `h1 : gL.mulVec (fun c => algebraMap W Qq (x c)) = 0`. Use function extensionality and compare the values at `i`.

Establish `h0` using `congrFun hx i`. Rewrite `h0` using `[hφ]`. Simplify using `only [Fintype.linearCombination_apply, Finset.sum_apply, Pi.smul_apply, Pi.zero_apply] at h0`. Simplify using `only [Matrix.mulVec, dotProduct, Pi.zero_apply]`. Rewrite using `[← h0]`.

Apply `Finset.sum_congr rfl` to reduce the goal to its premises. Introduce `c _`. Rewrite using `[Algebra.smul_def, mul_comm]`. Establish `h2` using `Matrix.eq_zero_of_mulVec_eq_zero hgL.ne_zero h1`. Use function extensionality and compare the values at `c`.

Conclude with `(IsFractionRing.injective W Qq) (by simpa using congrFun h2 c)`. Take `⟨N, hN⟩ : ∃ N : Submodule W (Fin k → W), N = e.src.comap φ` from `⟨_, rfl⟩`. Establish `hpN : ∀ x, (p : W) • x ∈ N` using `fun x => by`. Rewrite using `[hN, Submodule.mem_comap, map_smul]`. Conclude with `hpL _ (hφr ▸ LinearMap.mem_range_self φ x)`.

Take `⟨bT, a, hNs, hdiv, hcd⟩` from `smith_normal_form_card p k hp0 N hpN`. Use `⟨fun i => φ (bT i), a, ?_, ?_, hdiv, ?_⟩` and prove the remaining obligations. Rewrite using `[← hφr, LinearMap.range_eq_map, ← bT.span_eq, Submodule.map_span, ← Set.range_comp]`. Both sides reduce to the same expression. Establish `h1 : e.src = N.map φ`.

Rewrite using `[hN, Submodule.map_comap_eq, hφr]`. Conclude with `(inf_eq_right.2 hle).symm`. Rewrite using `[h1, hNs, Submodule.map_span, ← Set.range_comp]`. Use `congr 2`. Use function extensionality and compare the values at `i`.

Simplify using `only [Function.comp_apply, map_smul]`. Take `⟨φ', hφ'⟩ : ∃ φ' : (Fin k → W) ≃ₗ[W] e.tgt, ∀ x, ((φ' x : e.tgt) : Fin k → Qq) = φ x` from `⟨(LinearEquiv.ofInjective φ hφi).trans (LinearEquiv.ofEq _ _ hφr), fun x => rfl⟩`. Establish `hmap : N.map (φ' : (Fin k → W) →ₗ[W] e.tgt) = Submodule.comap e.tgt.subtype e.src`. Use extensionality with `y`. Prove the components needed by the constructor for the conclusion.

Introduce and unpack `⟨x, hx, rfl⟩`. Rewrite `hx` using `[hN]`. Use `show ((φ' x : e.tgt) : Fin k → Qq) ∈ e.src`. Rewrite using `[hφ']`. Conclude with `hx`.

Introduce `hy`. Use `⟨φ'.symm y, ?_, by simp⟩` and prove the remaining obligations. Rewrite using `[hN]`. Use `show φ (φ'.symm y) ∈ e.src`. Rewrite using `[← hφ', LinearEquiv.apply_symm_apply]`.

Conclude with `hy`. Rewrite using `[← Nat.card_congr (Submodule.Quotient.equiv N _ φ' hmap).toEquiv, hcd]`.
-/
theorem lc_snf {W Qq : Type} [CommRing W] [IsDomain W] [IsPrincipalIdealRing W] [Field Qq] [Algebra W Qq]
    [IsFractionRing W Qq] (p n' r k : ℕ) (hp0 : (p : W) ≠ 0) (e : Edge W Qq k) (he : IsEdge p n' r e) :
    ∃ (b' : Fin k → (Fin k → Qq)) (a : Fin k → W),
      e.tgt = Submodule.span W (Set.range b') ∧
      e.src = Submodule.span W (Set.range fun i => a i • b' i) ∧
      (∀ i, a i ∣ (p : W)) ∧
      Nat.card (↥e.tgt ⧸ Submodule.comap e.tgt.subtype e.src) = ∏ i, Nat.card (W ⧸ Ideal.span {a i}) := by
  classical
  obtain ⟨-, ⟨gL, hgL, hL⟩, hle, hpL, -⟩ := he
  obtain ⟨φ, hφ⟩ : ∃ φ : (Fin k → W) →ₗ[W] (Fin k → Qq),
      φ = Fintype.linearCombination W (fun (c : Fin k) (i : Fin k) => gL i c) := ⟨_, rfl⟩
  have hφr : LinearMap.range φ = e.tgt := by
    rw [hL, hφ]; exact Fintype.range_linearCombination W _
  have hφi : Function.Injective φ := by
    rw [injective_iff_map_eq_zero]
    intro x hx
    have h1 : gL.mulVec (fun c => algebraMap W Qq (x c)) = 0 := by
      funext i
      have h0 := congrFun hx i
      rw [hφ] at h0
      simp only [Fintype.linearCombination_apply, Finset.sum_apply, Pi.smul_apply, Pi.zero_apply] at h0
      simp only [Matrix.mulVec, dotProduct, Pi.zero_apply]
      rw [← h0]
      apply Finset.sum_congr rfl
      intro c _
      rw [Algebra.smul_def, mul_comm]
    have h2 := Matrix.eq_zero_of_mulVec_eq_zero hgL.ne_zero h1
    funext c
    exact (IsFractionRing.injective W Qq) (by simpa using congrFun h2 c)
  obtain ⟨N, hN⟩ : ∃ N : Submodule W (Fin k → W), N = e.src.comap φ := ⟨_, rfl⟩
  have hpN : ∀ x, (p : W) • x ∈ N := fun x => by
    rw [hN, Submodule.mem_comap, map_smul]
    exact hpL _ (hφr ▸ LinearMap.mem_range_self φ x)
  obtain ⟨bT, a, hNs, hdiv, hcd⟩ := smith_normal_form_card p k hp0 N hpN
  refine ⟨fun i => φ (bT i), a, ?_, ?_, hdiv, ?_⟩
  · rw [← hφr, LinearMap.range_eq_map, ← bT.span_eq, Submodule.map_span, ← Set.range_comp]
    rfl
  · have h1 : e.src = N.map φ := by
      rw [hN, Submodule.map_comap_eq, hφr]
      exact (inf_eq_right.2 hle).symm
    rw [h1, hNs, Submodule.map_span, ← Set.range_comp]
    congr 2
    funext i
    simp only [Function.comp_apply, map_smul]
  · obtain ⟨φ', hφ'⟩ : ∃ φ' : (Fin k → W) ≃ₗ[W] e.tgt, ∀ x, ((φ' x : e.tgt) : Fin k → Qq) = φ x :=
      ⟨(LinearEquiv.ofInjective φ hφi).trans (LinearEquiv.ofEq _ _ hφr), fun x => rfl⟩
    have hmap : N.map (φ' : (Fin k → W) →ₗ[W] e.tgt) = Submodule.comap e.tgt.subtype e.src := by
      ext y
      constructor
      · rintro ⟨x, hx, rfl⟩
        rw [hN] at hx
        show ((φ' x : e.tgt) : Fin k → Qq) ∈ e.src
        rw [hφ']
        exact hx
      · intro hy
        refine ⟨φ'.symm y, ?_, by simp⟩
        rw [hN]
        show φ (φ'.symm y) ∈ e.src
        rw [← hφ', LinearEquiv.apply_symm_apply]
        exact hy
    rw [← Nat.card_congr (Submodule.Quotient.equiv N _ φ' hmap).toEquiv, hcd]

/- English proof (translation)
Take `⟨b', a, hT, hS, hdiv, hc⟩` from `lc_snf p n' r k hp.ne_zero e he`. Establish `hcard2` using `he.2.2.2.2`. Establish `hfac : ∀ i, Nat.card (W ⧸ Ideal.span {a i}) = if IsUnit (a i) then 1 else p ^ n'`. Introduce `i`. Use `split_ifs with hu`.

Rewrite using `[Ideal.span_singleton_eq_top.2 hu]`. Establish `: Subsingleton (W ⧸ (⊤ : Ideal W))` using `Ideal.Quotient.subsingleton_iff.2 rfl`. Conclude with `Nat.card_of_subsingleton 0`. Take `⟨x, hx⟩` from `hdiv i`. Establish `hxu` using `(hp.isUnit_or_isUnit hx).resolve_left hu`.

Establish `hass : Associated (a i) (p : W)` using `⟨hxu.unit, by rw [hx]; rfl⟩`. Rewrite using `[Ideal.span_singleton_eq_span_singleton.2 hass]`. Conclude with `hcard`. Establish `hs : (Finset.univ.filter fun i => ¬ IsUnit (a i)).card = r`. Establish `h1 : p ^ (n' * r) = (p ^ n') ^ (Finset.univ.filter fun i => ¬ IsUnit (a i)).card`.

Rewrite using `[← hcard2, hc]`. Simplify using `only [hfac]`. Rewrite using `[Finset.prod_ite]`. Simplify using the standard rewrite rules. Rewrite `h1` using `[← pow_mul]`.

Establish `h3` using `Nat.pow_right_injective hp2 h1`. Conclude with `(Nat.eq_of_mul_eq_mul_left hn h3).symm`. Establish `hrk : r ≤ k`. Rewrite using `[← hs]`. Conclude with `(Finset.card_le_univ _).trans (by simp)`.

Establish `hcardEq : Fintype.card {c : Fin k // c.val < r} = Fintype.card {i : Fin k // ¬ IsUnit (a i)}`. Rewrite using `[Fintype.card_subtype, Fintype.card_subtype, hs]`. Establish `h1 : (Finset.univ.filter fun c : Fin k => c.val < r) = Finset.univ.map (Fin.castLEEmb hrk)`. Use extensionality with `c`. Simplify using `only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_map]`.

Prove the components needed by the constructor for the conclusion. Introduce `h`. Conclude with `⟨⟨c.val, h⟩, Fin.ext rfl⟩`. Introduce and unpack `⟨d, rfl⟩`. Conclude with `d.isLt`.

Rewrite using `[h1, Finset.card_map, Finset.card_univ, Fintype.card_fin]`. Set `σ : Equiv.Perm (Fin k)` to `(Fintype.equivOfCardEq hcardEq).extendSubtype`. Establish `hσ1 : ∀ c : Fin k, c.val < r → ¬ IsUnit (a (σ c))`. Introduce `c hc`. Establish `h1` using `Equiv.extendSubtype_mem (Fintype.equivOfCardEq hcardEq) c hc`.

Conclude with `h1`. Establish `hσ2 : ∀ c : Fin k, ¬ c.val < r → IsUnit (a (σ c))`. Introduce `c hc`. Establish `h1` using `Equiv.extendSubtype_not_mem (Fintype.equivOfCardEq hcardEq) c hc`. Conclude with `not_not.1 h1`.

Set `g : Matrix (Fin k) (Fin k) Qq` to `fun i c => (a (σ c) • b' (σ c)) i`. Set `d : Fin k → Qq` to `fun c => if c.val < r then ((p : Qq))⁻¹ else 1`. Establish `hSg : e.src = colSpan W g`. Rewrite using `[hS]`. Unfold `colSpan`.

Use `congr 1`. Use extensionality with `x`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨i, rfl⟩`. Conclude with `⟨σ.symm i, by funext j; simp [g]⟩`.

Introduce and unpack `⟨c, rfl⟩`. Conclude with `⟨σ c, rfl⟩`. Establish `hpQ0 : (p : Qq) ≠ 0`. Rewrite using `[← map_natCast (algebraMap W Qq)]`. Conclude with `fun h => hp.ne_zero ((IsFractionRing.injective W Qq) (by rw [h, map_zero]))`.

Apply the tactic sequence `have hentry : ∀ i c, (g * Matrix.diagonal d) i c = g i c * d c := fun i c => Matrix.mul_diagonal d g i c`. Establish `hu : ∀ c, ∃ u : Wˣ, (fun i => (g * Matrix.diagonal d) i c) = (u : W) • b' (σ c)`. Introduce `c`. Distinguish the cases in `hc : c.val < r`. Take `⟨x, hx⟩` from `hdiv (σ c)`.

Establish `hxu` using `(hp.isUnit_or_isUnit hx).resolve_left (hσ1 c hc)`. Use `⟨hxu.unit⁻¹, ?_⟩` and prove the remaining obligations. Use function extensionality and compare the values at `i`. Rewrite using `[hentry]`. Use `show (a (σ c) • b' (σ c)) i * (if c.val < r then ((p : Qq))⁻¹ else 1) = _`.

Rewrite using `[if_pos hc]`. Simplify using `only [Pi.smul_apply, Algebra.smul_def]`. Establish `hpQ : (p : Qq) = algebraMap W Qq (a (σ c)) * algebraMap W Qq x`. Rewrite using `[← map_mul, ← hx, map_natCast]`. Establish `hx1 : algebraMap W Qq x * algebraMap W Qq ((hxu.unit⁻¹ : Wˣ) : W) = 1`.

Rewrite using `[← map_mul, IsUnit.mul_val_inv, map_one]`. Establish `hA : algebraMap W Qq (a (σ c)) ≠ 0` using `fun h => hpQ0 (by rw [hpQ, h, zero_mul])`. Establish `hX : algebraMap W Qq x ≠ 0` using `fun h => hpQ0 (by rw [hpQ, h, mul_zero])`. Rewrite using `[eq_inv_of_mul_eq_one_right hx1, hpQ, mul_inv]`. Clear the denominators using the available nonvanishing facts.

Use `⟨(hσ2 c hc).unit, ?_⟩` and prove the remaining obligations. Use function extensionality and compare the values at `i`. Rewrite using `[hentry]`. Use `show (a (σ c) • b' (σ c)) i * (if c.val < r then ((p : Qq))⁻¹ else 1) = _`. Rewrite using `[if_neg hc, mul_one]`.

Both sides reduce to the same expression. Establish `hTg : e.tgt = colSpan W (g * Matrix.diagonal d)`. Rewrite using `[hT]`. Unfold `colSpan`. Apply `le_antisymm` to reduce the goal to its premises.

Rewrite using `[Submodule.span_le]`. Introduce and unpack `_ ⟨i, rfl⟩`. Take `⟨u, hu'⟩` from `hu (σ.symm i)`. Establish `h1 : b' i = ((u⁻¹ : Wˣ) : W) • (fun j => (g * Matrix.diagonal d) j (σ.symm i))`. Rewrite using `[hu', smul_smul]`.

Simplify using the standard rewrite rules. Rewrite using `[h1]`. Conclude with `Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, rfl⟩)`. Rewrite using `[Submodule.span_le]`. Introduce and unpack `_ ⟨c, rfl⟩`.

Take `⟨u, hu'⟩` from `hu c`. Use `show (fun i => (g * Matrix.diagonal d) i c) ∈ Submodule.span W (Set.range b')`. Rewrite using `[hu']`. Conclude with `Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, rfl⟩)`. Take `⟨hS0, hS0det, hS0eq⟩` from `he.1`.

Take `⟨U, hU⟩` from `la_factor g hS0 (by rw [← hS0eq, ← hSg])`. Establish `hdet : IsUnit g.det`. Establish `h1 : hS0.det = g.det * (U.map (algebraMap W Qq)).det` using `by rw [hU, Matrix.det_mul]`. Rewrite `hS0det` using `[h1]`. Conclude with `isUnit_of_mul_isUnit_left hS0det`.

Conclude with `⟨g, hdet, hSg, hTg⟩`.
-/
theorem lc_main {W Qq : Type} [CommRing W] [IsDomain W] [IsPrincipalIdealRing W] [Field Qq] [Algebra W Qq]
    [IsFractionRing W Qq] (p n' r k : ℕ) (hp : Irreducible (p : W))
    (hcard : Nat.card (W ⧸ Ideal.span {(p : W)}) = p ^ n') (hp2 : 2 ≤ p) (hn : 0 < n')
    (e : Edge W Qq k) (he : IsEdge p n' r e) :
    ∃ g : Matrix (Fin k) (Fin k) Qq, IsEdgeBasis p r e g := by
  classical
  obtain ⟨b', a, hT, hS, hdiv, hc⟩ := lc_snf p n' r k hp.ne_zero e he
  have hcard2 := he.2.2.2.2
  have hfac : ∀ i, Nat.card (W ⧸ Ideal.span {a i}) = if IsUnit (a i) then 1 else p ^ n' := by
    intro i
    split_ifs with hu
    · rw [Ideal.span_singleton_eq_top.2 hu]
      have : Subsingleton (W ⧸ (⊤ : Ideal W)) := Ideal.Quotient.subsingleton_iff.2 rfl
      exact Nat.card_of_subsingleton 0
    · obtain ⟨x, hx⟩ := hdiv i
      have hxu := (hp.isUnit_or_isUnit hx).resolve_left hu
      have hass : Associated (a i) (p : W) := ⟨hxu.unit, by rw [hx]; rfl⟩
      rw [Ideal.span_singleton_eq_span_singleton.2 hass]
      exact hcard
  have hs : (Finset.univ.filter fun i => ¬ IsUnit (a i)).card = r := by
    have h1 : p ^ (n' * r) = (p ^ n') ^ (Finset.univ.filter fun i => ¬ IsUnit (a i)).card := by
      rw [← hcard2, hc]
      simp only [hfac]
      rw [Finset.prod_ite]
      simp
    rw [← pow_mul] at h1
    have h3 := Nat.pow_right_injective hp2 h1
    exact (Nat.eq_of_mul_eq_mul_left hn h3).symm
  have hrk : r ≤ k := by
    rw [← hs]
    exact (Finset.card_le_univ _).trans (by simp)
  have hcardEq : Fintype.card {c : Fin k // c.val < r} = Fintype.card {i : Fin k // ¬ IsUnit (a i)} := by
    rw [Fintype.card_subtype, Fintype.card_subtype, hs]
    have h1 : (Finset.univ.filter fun c : Fin k => c.val < r) = Finset.univ.map (Fin.castLEEmb hrk) := by
      ext c
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_map]
      constructor
      · intro h
        exact ⟨⟨c.val, h⟩, Fin.ext rfl⟩
      · rintro ⟨d, rfl⟩
        exact d.isLt
    rw [h1, Finset.card_map, Finset.card_univ, Fintype.card_fin]
  let σ : Equiv.Perm (Fin k) := (Fintype.equivOfCardEq hcardEq).extendSubtype
  have hσ1 : ∀ c : Fin k, c.val < r → ¬ IsUnit (a (σ c)) := by
    intro c hc
    have h1 := Equiv.extendSubtype_mem (Fintype.equivOfCardEq hcardEq) c hc
    exact h1
  have hσ2 : ∀ c : Fin k, ¬ c.val < r → IsUnit (a (σ c)) := by
    intro c hc
    have h1 := Equiv.extendSubtype_not_mem (Fintype.equivOfCardEq hcardEq) c hc
    exact not_not.1 h1
  let g : Matrix (Fin k) (Fin k) Qq := fun i c => (a (σ c) • b' (σ c)) i
  let d : Fin k → Qq := fun c => if c.val < r then ((p : Qq))⁻¹ else 1
  have hSg : e.src = colSpan W g := by
    rw [hS]
    unfold colSpan
    congr 1
    ext x
    constructor
    · rintro ⟨i, rfl⟩
      exact ⟨σ.symm i, by funext j; simp [g]⟩
    · rintro ⟨c, rfl⟩
      exact ⟨σ c, rfl⟩
  have hpQ0 : (p : Qq) ≠ 0 := by
    rw [← map_natCast (algebraMap W Qq)]
    exact fun h => hp.ne_zero ((IsFractionRing.injective W Qq) (by rw [h, map_zero]))
  have hentry : ∀ i c, (g * Matrix.diagonal d) i c = g i c * d c := fun i c => Matrix.mul_diagonal d g i c
  have hu : ∀ c, ∃ u : Wˣ, (fun i => (g * Matrix.diagonal d) i c) = (u : W) • b' (σ c) := by
    intro c
    by_cases hc : c.val < r
    · obtain ⟨x, hx⟩ := hdiv (σ c)
      have hxu := (hp.isUnit_or_isUnit hx).resolve_left (hσ1 c hc)
      refine ⟨hxu.unit⁻¹, ?_⟩
      funext i
      rw [hentry]
      show (a (σ c) • b' (σ c)) i * (if c.val < r then ((p : Qq))⁻¹ else 1) = _
      rw [if_pos hc]
      simp only [Pi.smul_apply, Algebra.smul_def]
      have hpQ : (p : Qq) = algebraMap W Qq (a (σ c)) * algebraMap W Qq x := by
        rw [← map_mul, ← hx, map_natCast]
      have hx1 : algebraMap W Qq x * algebraMap W Qq ((hxu.unit⁻¹ : Wˣ) : W) = 1 := by
        rw [← map_mul, IsUnit.mul_val_inv, map_one]
      have hA : algebraMap W Qq (a (σ c)) ≠ 0 := fun h => hpQ0 (by rw [hpQ, h, zero_mul])
      have hX : algebraMap W Qq x ≠ 0 := fun h => hpQ0 (by rw [hpQ, h, mul_zero])
      rw [eq_inv_of_mul_eq_one_right hx1, hpQ, mul_inv]
      field_simp
    · refine ⟨(hσ2 c hc).unit, ?_⟩
      funext i
      rw [hentry]
      show (a (σ c) • b' (σ c)) i * (if c.val < r then ((p : Qq))⁻¹ else 1) = _
      rw [if_neg hc, mul_one]
      rfl
  have hTg : e.tgt = colSpan W (g * Matrix.diagonal d) := by
    rw [hT]
    unfold colSpan
    apply le_antisymm
    · rw [Submodule.span_le]
      rintro _ ⟨i, rfl⟩
      obtain ⟨u, hu'⟩ := hu (σ.symm i)
      have h1 : b' i = ((u⁻¹ : Wˣ) : W) • (fun j => (g * Matrix.diagonal d) j (σ.symm i)) := by
        rw [hu', smul_smul]
        simp
      rw [h1]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, rfl⟩)
    · rw [Submodule.span_le]
      rintro _ ⟨c, rfl⟩
      obtain ⟨u, hu'⟩ := hu c
      show (fun i => (g * Matrix.diagonal d) i c) ∈ Submodule.span W (Set.range b')
      rw [hu']
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, rfl⟩)
  obtain ⟨hS0, hS0det, hS0eq⟩ := he.1
  obtain ⟨U, hU⟩ := la_factor g hS0 (by rw [← hS0eq, ← hSg])
  have hdet : IsUnit g.det := by
    have h1 : hS0.det = g.det * (U.map (algebraMap W Qq)).det := by rw [hU, Matrix.det_mul]
    rw [h1] at hS0det
    exact isUnit_of_mul_isUnit_left hS0det
  exact ⟨g, hdet, hSg, hTg⟩

/- English proof (translation)
Introduce `e he`. Establish `hS` using `G.P.setting v`. Use `hS.frac_alt` as an intermediate fact. Conclude with `lc_main p (G.P.n' v) G.P.r (G.P.m + 1) hS.p_unif hS.res_card (by have := hS.five_le; omega) (by have := hS.two_le; omega) e he`.
-/
theorem restEdgeBasis {p : ℕ} (G : GAtP p) (v : Fin G.P.nV) : RestEdgeBasis G v := by
  intro e he
  have hS := G.P.setting v
  have := hS.frac_alt
  exact lc_main p (G.P.n' v) G.P.r (G.P.m + 1) hS.p_unif hS.res_card (by have := hS.five_le; omega)
    (by have := hS.two_le; omega) e he

end Formalism.MainNotions.G.LatticeSystems

namespace Formalism.MainNotions.G.LatticeSystems

open Formalism.MainNotions.G Formalism.GradedWeylDivisibility MvPolynomial

variable {p : ℕ}

/- English proof (translation)
The claim follows from `have := (G.P.setting v).frac_O IsFractionRing.injective G.O G.Kf`.
-/
theorem fn_inj (G : GAtP p) (v : Fin G.P.nV) : Function.Injective (algebraMap G.O G.Kf) :=
  have := (G.P.setting v).frac_O
  IsFractionRing.injective G.O G.Kf

/- English proof (translation)
Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty`. Simplify using `only [Finset.prod_empty]`. Rewrite using `[Submodule.one_eq_span]`. Conclude with `Submodule.fg_span_singleton _`.

Consider the case `insert a s ha ih`. Rewrite using `[Finset.prod_insert ha]`. Conclude with `(h a (Finset.mem_insert_self _ _)).mul (ih fun i hi => h i (Finset.mem_insert_of_mem hi))`.
-/
theorem fn_prod_fg {R A ι : Type*} [CommSemiring R] [CommSemiring A] [Algebra R A] (s : Finset ι)
    (N : ι → Submodule R A) (h : ∀ i ∈ s, (N i).FG) : (∏ i ∈ s, N i).FG := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.prod_empty]
    rw [Submodule.one_eq_span]
    exact Submodule.fg_span_singleton _
  | insert a s ha ih =>
    rw [Finset.prod_insert ha]
    exact (h a (Finset.mem_insert_self _ _)).mul (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

/- English proof (translation)
Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty`. Simplify using `only [Finset.prod_empty]`. Conclude with `Submodule.one_le.1 le_rfl`. Consider the case `insert b s hb ih`.

Rewrite using `[Finset.prod_insert hb, Finset.prod_insert hb]`. Conclude with `Submodule.mul_mem_mul (h b (Finset.mem_insert_self _ _)) (ih fun i hi => h i (Finset.mem_insert_of_mem hi))`.
-/
theorem fn_prod_mem {R A ι : Type*} [CommSemiring R] [CommSemiring A] [Algebra R A] (s : Finset ι)
    (N : ι → Submodule R A) (a : ι → A) (h : ∀ i ∈ s, a i ∈ N i) : ∏ i ∈ s, a i ∈ ∏ i ∈ s, N i := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.prod_empty]
    exact Submodule.one_le.1 le_rfl
  | insert b s hb ih =>
    rw [Finset.prod_insert hb, Finset.prod_insert hb]
    exact Submodule.mul_mem_mul (h b (Finset.mem_insert_self _ _))
      (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

/- English proof (translation)
Take `⟨g, hg, rfl⟩` from `hLv`. Rewrite using `[la_extO_G]`. Establish `hg'` using `la_tw_det (G.P.ι v) (G.P.σ v) s.val g hg`. Take `⟨B, -, hB, -, -⟩` from `la_basis (fn_inj G v) G.P.m (lamAt (G.P.lam0 v) s) _ hg'`. Use `⟨nablaLTw G.O G.Kf G.P.m (lamAt (G.P.lam0 v) s) (la_tw (G.P.ι v) (G.P.σ v) s.val g), ?_, ?_⟩` and prove the remaining obligations.

Rewrite using `[← hB]`. Establish `: Finite ↥(ssIdx (G.P.m + 1) (G.P.m + 1) (nuOf (lamAt (G.P.lam0 v) s)))` using `(sSIdxFinite _ _ _).to_subtype`. Conclude with `Submodule.fg_span (Set.finite_range B)`. Unfold `H0 split_ifs with h`. Conclude with `iInf₂_le _ ⟨hg', rfl⟩`.

Conclude with `bot_le`.
-/
theorem H0_le_finitely_generated (G : GAtP p) (v : Fin G.P.nV) (s : Fin (G.P.n' v))
    (Lv : Submodule (G.P.W v) (Fin (G.P.m + 1) → G.P.Qq v)) (hLv : IsLattice (G.P.W v) Lv) :
    ∃ N : Submodule G.O (MvPolynomial (Fin (G.P.m + 1) × Fin (G.P.m + 1)) G.Kf), N.FG ∧
      H0 G.O G.P.m (lamAt (G.P.lam0 v) s) (extO G.O (G.P.ι v) (G.P.σ v) s.val Lv) ≤ N := by
  obtain ⟨g, hg, rfl⟩ := hLv
  rw [la_extO_G]
  have hg' := la_tw_det (G.P.ι v) (G.P.σ v) s.val g hg
  obtain ⟨B, -, hB, -, -⟩ := la_basis (fn_inj G v) G.P.m (lamAt (G.P.lam0 v) s) _ hg'
  refine ⟨nablaLTw G.O G.Kf G.P.m (lamAt (G.P.lam0 v) s) (la_tw (G.P.ι v) (G.P.σ v) s.val g), ?_, ?_⟩
  · rw [← hB]
    have : Finite ↥(ssIdx (G.P.m + 1) (G.P.m + 1) (nuOf (lamAt (G.P.lam0 v) s))) :=
      (sSIdxFinite _ _ _).to_subtype
    exact Submodule.fg_span (Set.finite_range B)
  · unfold H0
    split_ifs with h
    · exact iInf₂_le _ ⟨hg', rfl⟩
    · exact bot_le

/- English proof (translation)
Use `choose N hN1 hN2 using fun s => H0_le_finitely_generated G v s Lv hLv`. Use `⟨∏ s, (N s).map ((blockEmb G.Kf s).toLinearMap.restrictScalars G.O), fn_prod_fg _ _ (fun s _ => (hN1 s).map _), ?_⟩` and prove the remaining obligations. Unfold `Hten tensorLat`. Rewrite using `[Submodule.span_le]`. Introduce and unpack `_ ⟨F, hF, rfl⟩`.

Conclude with `fn_prod_mem _ _ _ (fun s _ => ⟨F s, hN2 s (hF s), rfl⟩)`.
-/
theorem fn_Hten_fg (G : GAtP p) (v : Fin G.P.nV)
    (Lv : Submodule (G.P.W v) (Fin (G.P.m + 1) → G.P.Qq v)) (hLv : IsLattice (G.P.W v) Lv) :
    ∃ N : Submodule G.O (MvPolynomial (Fin (G.P.n' v) × (Fin (G.P.m + 1) × Fin (G.P.m + 1))) G.Kf), N.FG ∧
      Hten G.O (G.P.lam0 v) (fun s => extO G.O (G.P.ι v) (G.P.σ v) s.val Lv) ≤ N := by
  choose N hN1 hN2 using fun s => H0_le_finitely_generated G v s Lv hLv
  refine ⟨∏ s, (N s).map ((blockEmb G.Kf s).toLinearMap.restrictScalars G.O),
    fn_prod_fg _ _ (fun s _ => (hN1 s).map _), ?_⟩
  unfold Hten tensorLat
  rw [Submodule.span_le]
  rintro _ ⟨F, hF, rfl⟩
  exact fn_prod_mem _ _ _ (fun s _ => ⟨F s, hN2 s (hF s), rfl⟩)

/- English proof (translation)
Use `choose N hN1 hN2 using fun v => fn_Hten_fg G v (L v) (hL v)`. Use `⟨∏ v, (N v).map ((G.P.vEmb v).toLinearMap.restrictScalars G.O), fn_prod_fg _ _ (fun v _ => (hN1 v).map _), ?_⟩` and prove the remaining obligations. Unfold `Places.Htup Places.tenV`. Rewrite using `[Submodule.span_le]`. Introduce and unpack `_ ⟨F, hF, rfl⟩`.

Conclude with `fn_prod_mem _ _ _ (fun v _ => ⟨F v, hN2 v (hF v), rfl⟩)`.
-/
theorem fn_Htup_fg (G : GAtP p) (L : G.P.Tup) (hL : G.P.IsLatTup L) :
    ∃ N : Submodule G.O G.P.Xsp, N.FG ∧ G.P.Htup L ≤ N := by
  choose N hN1 hN2 using fun v => fn_Hten_fg G v (L v) (hL v)
  refine ⟨∏ v, (N v).map ((G.P.vEmb v).toLinearMap.restrictScalars G.O),
    fn_prod_fg _ _ (fun v _ => (hN1 v).map _), ?_⟩
  unfold Places.Htup Places.tenV
  rw [Submodule.span_le]
  rintro _ ⟨F, hF, rfl⟩
  exact fn_prod_mem _ _ _ (fun v _ => ⟨F v, hN2 v (hF v), rfl⟩)

def RestHfin (G : GAtP p) : Prop :=
  ∀ L, G.P.IsLatTup L → ∃ S : Finset G.P.Xsp, G.P.Htup L ≤ Submodule.span G.O (↑S : Set G.P.Xsp)

/- English proof (translation)
Introduce `L hL`. Take `⟨N, ⟨S, hS⟩, hle⟩` from `fn_Htup_fg G L hL`. Conclude with `⟨S, hS ▸ hle⟩`.
-/
theorem restHfin (G : GAtP p) : RestHfin G := by
  intro L hL
  obtain ⟨N, ⟨S, hS⟩, hle⟩ := fn_Htup_fg G L hL
  exact ⟨S, hS ▸ hle⟩

/- English proof (translation)
Establish `h : F i ∈ (G.lev i).funMod G.P.Htup` using `hF i (Set.mem_univ i)`. Unfold `Level.funMod at h`. Simplify using `only [Submodule.mem_inf, Submodule.mem_iInf, Submodule.mem_comap, LinearMap.mem_ker, LinearMap.proj_apply, LinearMap.sub_apply, LinearMap.comp_apply, LinearMap.smul_apply, LinearMap.restrictScalars_apply, sub_eq_zero] at h`. Conclude with `⟨h.1.1, h.1.2, fun γ L => h.2 γ L⟩`.
-/
theorem fn_mem (G : GAtP p) {F : G.Fn} (hF : F ∈ G.Mna) (i : G.comp) :
    (∀ L, G.P.IsLatTup L → F i L ∈ G.P.Htup L) ∧ (∀ L, ¬ G.P.IsLatTup L → F i L = 0) ∧
      ∀ (γ : (G.lev i).Γ) (L : G.P.Tup),
        F i ((G.lev i).smul γ L) = ((G.lev i).χ γ : G.O) • (G.lev i).actX γ (F i L) := by
  have h : F i ∈ (G.lev i).funMod G.P.Htup := hF i (Set.mem_univ i)
  unfold Level.funMod at h
  simp only [Submodule.mem_inf, Submodule.mem_iInf, Submodule.mem_comap, LinearMap.mem_ker,
    LinearMap.proj_apply, LinearMap.sub_apply, LinearMap.comp_apply, LinearMap.smul_apply,
    LinearMap.restrictScalars_apply, sub_eq_zero] at h
  exact ⟨h.1.1, h.1.2, fun γ L => h.2 γ L⟩

/- English proof (translation)
Use `choose R hR1 hR2 using h2`. Establish `hS : ∀ x : (Σ i : G.comp, ↥(R i)), ∃ S : Finset G.P.Xsp, G.P.Htup x.2.1 ≤ Submodule.span G.O (↑S : Set G.P.Xsp)` using `fun x => hH _ (hR1 x.1 _ x.2.2)`. Use `choose S hS using hS`. Set `f : ↥G.Mna →ₗ[G.O] (∀ x : (Σ i : G.comp, ↥(R i)), ↥(Submodule.span G.O (↑(S x) : Set G.P.Xsp)))` to `LinearMap.pi fun x => LinearMap.codRestrict _ ((LinearMap.proj x.2.1) ∘ₗ (LinearMap.proj x.1) ∘ₗ G.Mna.subtype) (fun F => hS x ((fn_mem G F.2 x.1).1 _ (hR1 x.1 _ x.2.2)))`. Establish `: ∀ x : (Σ i : G.comp, ↥(R i)), IsNoetherian G.O ↥(Submodule.span G.O (↑(S x) : Set G.P.Xsp))` using `fun x => isNoetherian_of_fg_of_noetherian _ (Submodule.fg_span (Finset.finite_toSet _))`.

Apply `Module.Finite.of_injective f` to reduce the goal to its premises. Rewrite using `[injective_iff_map_eq_zero]`. Introduce `F hF0`. Apply `Subtype.ext` to reduce the goal to its premises. Use function extensionality and compare the values at `i L`.

Use `show F.1 i L = 0`. Distinguish the cases in `hL : G.P.IsLatTup L`. Take `⟨L₀, hL₀, γ, rfl⟩` from `hR2 i L hL`. Establish `h0 : F.1 i L₀ = 0` using `congrArg Subtype.val (congrFun hF0 ⟨i, ⟨L₀, hL₀⟩⟩)`. Rewrite using `[(fn_mem G F.2 i).2.2 γ L₀, h0, map_zero, smul_zero]`.

Conclude with `(fn_mem G F.2 i).2.1 L hL`.
-/
theorem mna_finite_of (G : GAtP p) (hH : RestHfin G) (h2 : G.FinClasses) : Module.Finite G.O G.Mna := by
  classical
  choose R hR1 hR2 using h2
  have hS : ∀ x : (Σ i : G.comp, ↥(R i)), ∃ S : Finset G.P.Xsp,
      G.P.Htup x.2.1 ≤ Submodule.span G.O (↑S : Set G.P.Xsp) := fun x => hH _ (hR1 x.1 _ x.2.2)
  choose S hS using hS
  let f : ↥G.Mna →ₗ[G.O] (∀ x : (Σ i : G.comp, ↥(R i)), ↥(Submodule.span G.O (↑(S x) : Set G.P.Xsp))) :=
    LinearMap.pi fun x => LinearMap.codRestrict _
      ((LinearMap.proj x.2.1) ∘ₗ (LinearMap.proj x.1) ∘ₗ G.Mna.subtype)
      (fun F => hS x ((fn_mem G F.2 x.1).1 _ (hR1 x.1 _ x.2.2)))
  have : ∀ x : (Σ i : G.comp, ↥(R i)), IsNoetherian G.O ↥(Submodule.span G.O (↑(S x) : Set G.P.Xsp)) :=
    fun x => isNoetherian_of_fg_of_noetherian _ (Submodule.fg_span (Finset.finite_toSet _))
  apply Module.Finite.of_injective f
  rw [injective_iff_map_eq_zero]
  intro F hF0
  apply Subtype.ext
  funext i L
  show F.1 i L = 0
  by_cases hL : G.P.IsLatTup L
  · obtain ⟨L₀, hL₀, γ, rfl⟩ := hR2 i L hL
    have h0 : F.1 i L₀ = 0 := congrArg Subtype.val (congrFun hF0 ⟨i, ⟨L₀, hL₀⟩⟩)
    rw [(fn_mem G F.2 i).2.2 γ L₀, h0, map_zero, smul_zero]
  · exact (fn_mem G F.2 i).2.1 L hL

/- English proof (translation)
The claim follows from `mna_finite_of G (restHfin G) h2`.
-/
theorem mna_finite (G : GAtP p) (h2 : G.FinClasses) : Module.Finite G.O G.Mna :=
  mna_finite_of G (restHfin G) h2

/- English proof (translation)
Establish `ha : algebraMap G.O G.Kf c ≠ 0` using `fun h0 => hc (fn_inj G v (by rw [h0, map_zero]))`. Use function extensionality and compare the values at `i L`. Establish `h1 : c • F i L = 0` using `congrFun (congrFun h i) L`. Rewrite `h1` using `[← algebraMap_smul G.Kf c (F i L)]`. Establish `h2` using `inv_smul_smul₀ ha (F i L)`.

Rewrite `h2` using `[h1, smul_zero]`. Conclude with `h2.symm`.
-/
theorem fn_torsion (G : GAtP p) (v : Fin G.P.nV) (c : G.O) (hc : c ≠ 0) (F : G.Fn) (h : c • F = 0) : F = 0 := by
  have ha : algebraMap G.O G.Kf c ≠ 0 := fun h0 => hc (fn_inj G v (by rw [h0, map_zero]))
  funext i L
  have h1 : c • F i L = 0 := congrFun (congrFun h i) L
  rw [← algebraMap_smul G.Kf c (F i L)] at h1
  have h2 := inv_smul_smul₀ ha (F i L)
  rw [h1, smul_zero] at h2
  exact h2.symm

/- English proof (translation)
Establish `: Module.IsTorsionFree G.O ↥G.Mna` using `⟨fun c hc x y hxy => by`. Establish `h0 : c • (x - y) = 0`. Rewrite using `[smul_sub]`. Conclude with `sub_eq_zero.2 hxy`. Establish `h1 : x - y = 0` using `Subtype.ext (fn_torsion G v c hc.ne_zero (x - y).1 (congrArg Subtype.val h0))`.

Conclude with `sub_eq_zero.1 h1⟩`. Conclude with `Module.free_of_finite_type_torsion_free'`.
-/
theorem mna_free (G : GAtP p) (v : Fin G.P.nV) [Module.Finite G.O G.Mna] : Module.Free G.O G.Mna := by
  have : Module.IsTorsionFree G.O ↥G.Mna := ⟨fun c hc x y hxy => by
    have h0 : c • (x - y) = 0 := by
      rw [smul_sub]
      exact sub_eq_zero.2 hxy
    have h1 : x - y = 0 := Subtype.ext (fn_torsion G v c hc.ne_zero (x - y).1 (congrArg Subtype.val h0))
    exact sub_eq_zero.1 h1⟩
  exact Module.free_of_finite_type_torsion_free'

end Formalism.MainNotions.G.LatticeSystems

namespace Formalism.MainNotions.G.LatticeSystems

open Formalism.MainNotions.G Formalism.MainNotions.SelectionLemmas Formalism.G0

variable {p : ℕ}

def RemainingCountingStatement (G : GAtP p) : Prop :=
  G.TrivStab → G.FinClasses →
  ∀ (VV : Finset (Fin G.P.nV)) (t : Fin G.P.nV → ℕ) (Dd cStar : ℕ) (κ : Fin G.P.nV → ℝ), VV.Nonempty →
    (∀ v ∈ VV, LPprime (W := G.P.W v) (Qq := G.P.Qq v) (O := G.O) (Kf := G.Kf) p (G.P.n' v) (G.P.ι v) (G.P.σ v)
      G.P.w G.P.r (G.P.lam0 v) (t v) Dd (κ v) cStar) →
    RestWalk G VV t Dd κ

/- English proof (translation)
The claim follows from `Finset.sum_nonneg fun _ hB => Finset.prod_nonneg fun v hv => hκ v ((Finset.mem_powersetCard.1 hB).1 hv)`.
-/
theorem esymmOn_nonneg {ι : Type} (VV : Finset ι) (κ : ι → ℝ) (hκ : ∀ v ∈ VV, 0 ≤ κ v) (k : ℕ) :
    0 ≤ esymmOn VV κ k :=
  Finset.sum_nonneg fun _ hB => Finset.prod_nonneg fun v hv => hκ v ((Finset.mem_powersetCard.1 hB).1 hv)

/- English proof (translation)
Introduce `VV t Sv Dd cStar S m κ hm hS hLP M d N τ`. Establish `hthm : ∀ β : ℕ, AllButLE (p : G.O) M N ⌊(d : ℝ) * (m : ℝ) ^ (β + 1) * esymmOn VV κ (β + 1)⌋₊ (τ + β * S)`. Introduce `β`. Break down `VV.eq_empty_or_nonempty with hE | ⟨v0, hv0⟩` into its components or cases. Use `ManyOrbitsP.allBut_mono (allLE G VV m Sv M) (Nat.zero_le _) ?_` and prove the remaining obligations.

Rewrite using `[hE]`. Simplify using the standard rewrite rules. Conclude with `walk_clause G (yEnd G) (fun _ _ => rfl) (exponent_condition_holds D G) VV t Sv Dd S m κ (G.P.setting v0).w_sq hm hS (hR hA.1 hA.2.1 VV t Dd cStar κ ⟨v0, hv0⟩ hLP) β`. Use `⟨⟨hthm, allLE G VV m Sv M⟩, fun hSig => ?_⟩` and prove the remaining obligations. Introduce `Sig Nst`.

Establish `hκ : ∀ v ∈ VV, 0 ≤ κ v` using `fun v hv => kappa_nonneg' G v (t v) Dd cStar (κ v) (hLP v hv)`. Establish `hs0 : 0 ≤ Sig` using `mul_nonneg (Nat.cast_nonneg m) (Finset.sum_nonneg hκ)`. Use `⟨fun β => esymm_clause VV κ hκ m d (β + 1), ?_, fun M' hM' => ⟨sat_clause _ N M M' hM', inj_clause Nst M M' hM'.1, fun Y _ _ K Z hZ => (Submodule.map_mono (inf_le_left.trans inf_le_left)).trans hZ⟩⟩` and prove the remaining obligations. Break down `VV.eq_empty_or_nonempty with hE | ⟨v0, hv0⟩` into its components or cases. Establish `hτ : τ = 0` using `by simp [τ, tau, hE]`.

Establish `htop : Submodule.comap M.subtype Nst = ⊤`. Rewrite using `[eq_top_iff]`. Introduce and unpack `⟨x, hx⟩ -`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Apply `Submodule.subset_span` to reduce the goal to its premises.

Simplify using `only [Set.mem_iUnion]`. Conclude with `⟨∅, by simp, x, hx, by simp [monoN, hE]⟩`. Use `show x ∈ Ideal.span {(p : G.O) ^ τ} • M`. Rewrite using `[hτ, pow_zero, Ideal.span_singleton_one, Submodule.top_smul]`. Conclude with `hx`.

Use `⟨0, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[htop]`. Simplify using the standard rewrite rules. Establish `: (0 : ℝ) ≤ (d : ℝ) * τ + 2 * S * Sig * d` using `by positivity`. Simplify using `using mul_nonneg (Nat.cast_nonneg _) this`.

Establish `hp0 : (p : G.O) ≠ 0`. Introduce `h0`. Conclude with `kp_p_ne_zero G v0 (by rw [h0, map_zero])`. Establish `hfr : Module.Free G.O G.Mna` using `hfree v0`. Use `lengthFromAllBut (p : G.O) hp0 M N d rfl τ S VV.card Sig hs0 hSig ?_ ?_` and prove the remaining obligations.

Introduce `β _`. Take `⟨C, hCM, hcard, hx⟩` from `hthm β`. Use `⟨C, hCM, ?_, hx⟩` and prove the remaining obligations. Establish `h0 : (0 : ℝ) ≤ (d : ℝ) * (m : ℝ) ^ (β + 1) * esymmOn VV κ (β + 1)` using `mul_nonneg (by positivity) (esymmOn_nonneg VV κ hκ _)`. Establish `hf : (1 : ℝ) ≤ (β + 1).factorial`.

Conclude with `Nat.one_le_iff_ne_zero.mpr (Nat.factorial_ne_zero _)` after adjusting the coercions. Establish `hpw : 0 ≤ (d : ℝ) * Sig ^ (β + 1)` using `by positivity`. Combine the equalities or inequalities in the displayed calculation. Conclude with `hcard` after adjusting the coercions. Use `_ ≤ (d : ℝ) * (m : ℝ) ^ (β + 1) * esymmOn VV κ (β + 1) := Nat.floor_le h0`.

Use `_ ≤ (d : ℝ) * Sig ^ (β + 1) / ((β + 1).factorial : ℝ) := esymm_clause VV κ hκ m d (β + 1)`. Use `_ ≤ (d : ℝ) * Sig ^ (β + 1) := div_le_self hpw hf`. Use `ManyOrbitsP.allBut_mono (allLE G VV m Sv M) le_rfl ?_` and prove the remaining obligations. Combine the equalities or inequalities in the displayed calculation.
-/
theorem counting_statement_of_block_form (D : Formalism.BasicNotions.D7) (G : GAtP p) (hA : admitted D G) (hR : RemainingCountingStatement G)
    (hfin : Module.Finite G.O G.Mna) (hfree : Fin G.P.nV → Module.Free G.O G.Mna) : Conclusion1 D G := by
  intro VV t Sv Dd cStar S m κ hm hS hLP M d N τ
  have hthm : ∀ β : ℕ, AllButLE (p : G.O) M N
      ⌊(d : ℝ) * (m : ℝ) ^ (β + 1) * esymmOn VV κ (β + 1)⌋₊ (τ + β * S) := by
    intro β
    rcases VV.eq_empty_or_nonempty with hE | ⟨v0, hv0⟩
    · refine ManyOrbitsP.allBut_mono (allLE G VV m Sv M) (Nat.zero_le _) ?_
      rw [hE]; simp
    · exact walk_clause G (yEnd G) (fun _ _ => rfl) (exponent_condition_holds D G) VV t Sv Dd S m κ
        (G.P.setting v0).w_sq hm hS (hR hA.1 hA.2.1 VV t Dd cStar κ ⟨v0, hv0⟩ hLP) β
  refine ⟨⟨hthm, allLE G VV m Sv M⟩, fun hSig => ?_⟩
  intro Sig Nst
  have hκ : ∀ v ∈ VV, 0 ≤ κ v := fun v hv => kappa_nonneg' G v (t v) Dd cStar (κ v) (hLP v hv)
  have hs0 : 0 ≤ Sig := mul_nonneg (Nat.cast_nonneg m) (Finset.sum_nonneg hκ)
  refine ⟨fun β => esymm_clause VV κ hκ m d (β + 1), ?_, fun M' hM' =>
    ⟨sat_clause _ N M M' hM', inj_clause Nst M M' hM'.1, fun Y _ _ K Z hZ =>
      (Submodule.map_mono (inf_le_left.trans inf_le_left)).trans hZ⟩⟩
  rcases VV.eq_empty_or_nonempty with hE | ⟨v0, hv0⟩
  · have hτ : τ = 0 := by simp [τ, tau, hE]
    have htop : Submodule.comap M.subtype Nst = ⊤ := by
      rw [eq_top_iff]
      rintro ⟨x, hx⟩ -
      refine ⟨?_, ?_⟩
      · apply Submodule.subset_span
        simp only [Set.mem_iUnion]
        exact ⟨∅, by simp, x, hx, by simp [monoN, hE]⟩
      · show x ∈ Ideal.span {(p : G.O) ^ τ} • M
        rw [hτ, pow_zero, Ideal.span_singleton_one, Submodule.top_smul]
        exact hx
    refine ⟨0, ?_, ?_⟩
    · rw [htop]
      simp
    · have : (0 : ℝ) ≤ (d : ℝ) * τ + 2 * S * Sig * d := by positivity
      simpa using mul_nonneg (Nat.cast_nonneg _) this
  · have hp0 : (p : G.O) ≠ 0 := by
      intro h0
      exact kp_p_ne_zero G v0 (by rw [h0, map_zero])
    have hfr : Module.Free G.O G.Mna := hfree v0
    refine lengthFromAllBut (p : G.O) hp0 M N d rfl τ S VV.card Sig hs0 hSig ?_ ?_
    · intro β _
      obtain ⟨C, hCM, hcard, hx⟩ := hthm β
      refine ⟨C, hCM, ?_, hx⟩
      have h0 : (0 : ℝ) ≤ (d : ℝ) * (m : ℝ) ^ (β + 1) * esymmOn VV κ (β + 1) :=
        mul_nonneg (by positivity) (esymmOn_nonneg VV κ hκ _)
      have hf : (1 : ℝ) ≤ (β + 1).factorial := by
        exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Nat.factorial_ne_zero _)
      have hpw : 0 ≤ (d : ℝ) * Sig ^ (β + 1) := by positivity
      calc (C.card : ℝ) ≤ (⌊(d : ℝ) * (m : ℝ) ^ (β + 1) * esymmOn VV κ (β + 1)⌋₊ : ℝ) := by
            exact_mod_cast hcard
        _ ≤ (d : ℝ) * (m : ℝ) ^ (β + 1) * esymmOn VV κ (β + 1) := Nat.floor_le h0
        _ ≤ (d : ℝ) * Sig ^ (β + 1) / ((β + 1).factorial : ℝ) := esymm_clause VV κ hκ m d (β + 1)
        _ ≤ (d : ℝ) * Sig ^ (β + 1) := div_le_self hpw hf
    · refine ManyOrbitsP.allBut_mono (allLE G VV m Sv M) le_rfl ?_
      calc ∑ v ∈ VV, Sv v ≤ ∑ _v ∈ VV, S := Finset.sum_le_sum hS
        _ = VV.card * S := by simp

def RestJAll (G : GAtP p) : Prop :=
  G.TrivStab → G.FinClasses →
  ∀ (VV : Finset (Fin G.P.nV)) (t : Fin G.P.nV → ℕ) (Dd cStar : ℕ) (κ : Fin G.P.nV → ℝ), VV.Nonempty →
    (∀ v ∈ VV, LPprime (W := G.P.W v) (Qq := G.P.Qq v) (O := G.O) (Kf := G.Kf) p (G.P.n' v) (G.P.ι v) (G.P.σ v)
      G.P.w G.P.r (G.P.lam0 v) (t v) Dd (κ v) cStar) →
    RestJ G VV t Dd κ

/- English proof (translation)
Introduce `h1 h2 VV t Dd cStar κ hne hLP` and use `restWalk_of_local_J G VV t Dd κ (fun v _ => hD v) (hJ h1 h2 VV t Dd cStar κ hne hLP)`.
-/
theorem open_part_of_local_and_lemma_J (G : GAtP p) (hD : ∀ v, RestLocD G v) (hJ : RestJAll G) : RemainingCountingStatement G :=
  fun h1 h2 VV t Dd cStar κ hne hLP =>
    restWalk_of_local_J G VV t Dd κ (fun v _ => hD v) (hJ h1 h2 VV t Dd cStar κ hne hLP)

/- English proof (translation)
The claim follows from `open_part_of_local_and_lemma_J G (fun v => la_locD_of_edge G v (hE v)) hJ`.
-/
theorem open_part_of_edge_inclusions (G : GAtP p) (hE : ∀ v, RestLocEdge G v) (hJ : RestJAll G) : RemainingCountingStatement G :=
  open_part_of_local_and_lemma_J G (fun v => la_locD_of_edge G v (hE v)) hJ

/- English proof (translation)
The claim follows from `have hfin : Module.Finite G.O G.Mna := mna_finite G hA.2.1 counting_statement_of_block_form D G hA hR hfin (fun v => mna_free G v)`.
-/
theorem instance_of_open_part (D : Formalism.BasicNotions.D7) (G : GAtP p) (hA : admitted D G) (hR : RemainingCountingStatement G) : Conclusion1 D G :=
  have hfin : Module.Finite G.O G.Mna := mna_finite G hA.2.1
  counting_statement_of_block_form D G hA hR hfin (fun v => mna_free G v)

/- English proof (translation)
The claim follows from `instance_of_open_part D G hA (open_part_of_edge_inclusions G hE hJ)`.
-/
theorem instance_of_edges_and_lemma_J (D : Formalism.BasicNotions.D7) (G : GAtP p) (hA : admitted D G) (hE : ∀ v, RestLocEdge G v)
    (hJ : RestJAll G) : Conclusion1 D G :=
  instance_of_open_part D G hA (open_part_of_edge_inclusions G hE hJ)

/- English proof (translation)
The claim follows from `instance_of_open_part D G hA (open_part_of_local_and_lemma_J G (fun v => restLocD_of_edgeBasis G v (hB v)) hJ)`.
-/
theorem instance_of_edge_bases_and_lemma_J (D : Formalism.BasicNotions.D7) (G : GAtP p) (hA : admitted D G) (hB : ∀ v, RestEdgeBasis G v)
    (hJ : RestJAll G) : Conclusion1 D G :=
  instance_of_open_part D G hA (open_part_of_local_and_lemma_J G (fun v => restLocD_of_edgeBasis G v (hB v)) hJ)

/- English proof (translation)
The claim follows from `restLocD_of_edgeBasis G v (restEdgeBasis G v)`.
-/
theorem restLocD (G : GAtP p) (v : Fin G.P.nV) : RestLocD G v :=
  restLocD_of_edgeBasis G v (restEdgeBasis G v)

/- English proof (translation)
The claim follows from `open_part_of_local_and_lemma_J G (restLocD G) hJ`.
-/
theorem open_part_of_lemma_J (G : GAtP p) (hJ : RestJAll G) : RemainingCountingStatement G := open_part_of_local_and_lemma_J G (restLocD G) hJ

/- English proof (translation)
The claim follows from `instance_of_open_part D G hA (open_part_of_lemma_J G hJ)`.
-/
theorem instance_of_lemma_J (D : Formalism.BasicNotions.D7) (G : GAtP p) (hA : admitted D G) (hJ : RestJAll G) : Conclusion1 D G :=
  instance_of_open_part D G hA (open_part_of_lemma_J G hJ)

end Formalism.MainNotions.G.LatticeSystems

namespace Formalism.MainNotions.G.LatticeSystems

open Formalism.MainNotions.G Formalism.MainNotions.SelectionLemmas Formalism.G0

variable {p : ℕ}

abbrev Pol (G : GAtP p) (v : Fin G.P.nV) : Type :=
  MvPolynomial (Fin (G.P.n' v) × (Fin (G.P.m + 1) × Fin (G.P.m + 1))) G.Kf

abbrev Lat (G : GAtP p) (v : Fin G.P.nV) : Type := Submodule (G.P.W v) (Fin (G.P.m + 1) → G.P.Qq v)

def upd (G : GAtP p) (L : G.P.Tup) (v : Fin G.P.nV) (A : Lat G v) : G.P.Tup :=
  Function.update (β := fun v => Lat G v) L v A

def sysOf (G : GAtP p) (t : Fin G.P.nV → ℕ) (σ : Fin G.P.nV → Slot) : G.P.Tup → Submodule G.O G.P.Xsp :=
  G.P.sys fun v => piLattice₂ G v (t v) (σ v)

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem latSys_eq (G : GAtP p) (t : Fin G.P.nV → ℕ) (σ : Fin G.P.nV → Slot) :
    latSys G t σ = G.funMod (sysOf G t σ) := rfl

def EquivSys (G : GAtP p) (Hv : G.P.Tup → Submodule G.O G.P.Xsp) : Prop :=
  ∀ (i : G.comp) (γ : (G.lev i).Γ) (L : G.P.Tup), G.P.IsLatTup L → ∀ ξ ∈ Hv L,
    ((G.lev i).χ γ : G.O) • (G.lev i).actX γ ξ ∈ Hv ((G.lev i).smul γ L)

def JEquiv (G : GAtP p) : Prop := ∀ t σ, EquivSys G (sysOf G t σ)

def delta (G : GAtP p) (i : G.comp) (L0 : G.P.Tup) (ξ : G.P.Xsp) : G.Fn := by
  classical
  exact fun i' L => if h : ∃ γ : (G.lev i).Γ, L = (G.lev i).smul γ L0 then
    (if i' = i then ((G.lev i).χ h.choose : G.O) • (G.lev i).actX h.choose ξ else 0) else 0

def sc {X : Type} [AddCommGroup X] (G : GAtP p) [Module G.O X] (c : G.O) (M : Submodule G.O X) : Submodule G.O X :=
  M.map (LinearMap.lsmul G.O X c)

def MBof (G : GAtP p) (t : Fin G.P.nV → ℕ) (B : Finset (Fin G.P.nV)) : Submodule G.O G.Fn := latSys G t (vertexLabel B)

def JBof (G : GAtP p) (t : Fin G.P.nV → ℕ) (B : Finset (Fin G.P.nV)) : Submodule G.O G.Fn :=
  ⨆ v ∈ B, Submodule.span G.O (G.yv v '' (latSys G t (Function.update (vertexLabel B) v Slot.ball) : Set G.Fn))

def IsReps (G : GAtP p) (reps : Finset (G.comp × G.P.Tup)) : Prop :=
  (∀ r ∈ reps, G.P.IsLatTup r.2) ∧
  (∀ r ∈ reps, ∀ r' ∈ reps, r.1 = r'.1 → (∃ γ : (G.lev r.1).Γ, r'.2 = (G.lev r.1).smul γ r.2) → r = r') ∧
  (∀ (i : G.comp) (L : G.P.Tup), G.P.IsLatTup L →
    ∃ r ∈ reps, r.1 = i ∧ ∃ γ : (G.lev r.1).Γ, L = (G.lev r.1).smul γ r.2)

def JDelta (G : GAtP p) : Prop :=
  (∀ i L0 ξ η, delta G i L0 (ξ + η) = delta G i L0 ξ + delta G i L0 η) ∧
  (∀ i L0 (c : G.O) ξ, delta G i L0 (c • ξ) = c • delta G i L0 ξ) ∧
  (∀ (Hv : G.P.Tup → Submodule G.O G.P.Xsp), EquivSys G Hv → ∀ i L0, G.P.IsLatTup L0 → ∀ ξ ∈ Hv L0,
    delta G i L0 ξ ∈ G.funMod Hv) ∧
  (∀ i L0 (γ : (G.lev i).Γ) ξ, G.P.IsLatTup L0 →
    delta G i L0 ξ i ((G.lev i).smul γ L0) = ((G.lev i).χ γ : G.O) • (G.lev i).actX γ ξ) ∧
  (∀ i L0 ξ, G.P.IsLatTup L0 → delta G i L0 ξ i L0 = ξ) ∧
  (∀ i L0 ξ i' L, (i' ≠ i ∨ ¬ ∃ γ : (G.lev i).Γ, L = (G.lev i).smul γ L0) → delta G i L0 ξ i' L = 0) ∧
  (∃ reps, IsReps G reps) ∧
  (∀ reps, IsReps G reps → ∀ (Hv : G.P.Tup → Submodule G.O G.P.Xsp) (F : G.Fn), F ∈ G.funMod Hv →
    F = ∑ r ∈ reps, delta G r.1 r.2 (F r.1 r.2))

def JStep1 (G : GAtP p) (t : Fin G.P.nV → ℕ) (B : Finset (Fin G.P.nV)) (E : ℕ) : Prop :=
  ∀ v ∈ B, ∀ (i : G.comp) (L : G.P.Tup), G.P.IsLatTup L → ∀ L'' : Lat G v,
    IsEdge p (G.P.n' v) G.P.r ⟨L'', L v⟩ → ∀ ξ : G.P.Xsp,
    ξ ∈ sysOf G t (Function.update (vertexLabel B) v Slot.ball) (upd G L v L'') →
    (∀ L' : Lat G v, IsEdge p (G.P.n' v) G.P.r ⟨L'', L'⟩ → L' ≠ L v →
      ((p : G.Kf) ^ G.P.ArV v) • ξ ∈ sc G ((p : G.O) ^ E) (sysOf G t (vertexLabel B) (upd G L v L'))) →
    delta G i L (((p : G.Kf) ^ G.P.ArV v) • ξ) ∈ JBof G t B ⊔ sc G ((p : G.O) ^ E) (MBof G t B)

def JSmith (G : GAtP p) (v : Fin G.P.nV) (tv Dd cStar : ℕ) (κ : ℝ) : Prop :=
  ∀ Lv : Lat G v, IsLattice (G.P.W v) Lv →
    ∃ (K : ℕ) (src : Fin K → Lat G v) (F : Fin K → Pol G v)
      (b : Fin (dimV G.Kf (G.P.lam0 v)) → Pol G v) (bad : Finset (Fin (dimV G.Kf (G.P.lam0 v)))),
      (∀ k, IsEdge p (G.P.n' v) G.P.r ⟨src k, Lv⟩) ∧
      (∀ k, F k ∈ piLattice₂ G v tv Slot.ball (src k)) ∧
      (∀ k (L' : Lat G v), IsEdge p (G.P.n' v) G.P.r ⟨src k, L'⟩ → L' ≠ Lv →
        ((p : G.Kf) ^ G.P.ArV v) • F k ∈ sc G (G.P.w ^ cStar) (piLattice₂ G v tv Slot.dual L')) ∧
      piLattice₂ G v tv Slot.dual Lv = Submodule.span G.O (Set.range b) ∧
      (bad.card : ℝ) ≤ κ * (dimV G.Kf (G.P.lam0 v) : ℝ) ∧
      ∀ a, a ∉ bad → (p : G.O) ^ Dd • b a ∈
        Submodule.span G.O (Set.range fun k => ((p : G.Kf) ^ G.P.ArV v) • F k)

def JBase (G : GAtP p) (v : Fin G.P.nV) : Prop :=
  ∀ (tv : ℕ) (Lv : Lat G v), IsLattice (G.P.W v) Lv →
    ∃ b : Fin (dimV G.Kf (G.P.lam0 v)) → Pol G v,
      piLattice₂ G v tv Slot.base Lv = Submodule.span G.O (Set.range b)

def JLocal (G : GAtP p) (t : Fin G.P.nV → ℕ) (B : Finset (Fin G.P.nV)) (Dd : ℕ) (κ : Fin G.P.nV → ℝ) : Prop :=
  ∀ (i : G.comp) (L : G.P.Tup), G.P.IsLatTup L →
    ∃ C : Finset G.P.Xsp, (↑C : Set G.P.Xsp) ⊆ sysOf G t (vertexLabel B) L ∧
      (C.card : ℝ) ≤ (∏ v ∈ B, κ v) * ((∏ v, dimV G.Kf (G.P.lam0 v) : ℕ) : ℝ) ∧
      ∀ ξ ∈ sysOf G t (vertexLabel B) L, ∃ g c, (p : G.O) ^ Dd • ξ = g + c ∧
        delta G i L g ∈ JBof G t B ⊔ sc G ((p : G.O) ^ (Dd + 1)) (MBof G t B) ∧
        c ∈ Submodule.span G.O (↑C : Set G.P.Xsp)

def JRank (G : GAtP p) : Prop :=
  ∀ reps, IsReps G reps → reps.card * ∏ v, dimV G.Kf (G.P.lam0 v) ≤ G.dna

end Formalism.MainNotions.G.LatticeSystems

namespace Formalism.MainNotions.G.LatticeSystems

open Formalism.MainNotions.G Formalism.MainNotions.SelectionLemmas Formalism.G0 MvPolynomial

section Act

variable {p : ℕ} {O Kf : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field Kf] [Algebra O Kf]
  (P : Places p O Kf)

def jd_f (v : Fin P.nV) (s : Fin (P.n' v)) : P.Qq v →+* Kf :=
  (P.ι v).comp ((P.σ v ^ s.val : P.Qq v ≃+* P.Qq v) : P.Qq v →+* P.Qq v)

/- English proof (translation)
Use extensionality with `a b`. Both sides reduce to the same expression.
-/
theorem jd_gPos (v : Fin P.nV) (s : Fin (P.n' v)) (A : Matrix (Fin (P.m + 1)) (Fin (P.m + 1)) (P.Qq v)) :
    P.gPos v s A = (jd_f P v s).mapMatrix A := by
  ext a b
  rfl

/- English proof (translation)
Simplify using `only [jd_gPos, map_mul]`.
-/
theorem jd_gPos_mul (v : Fin P.nV) (s : Fin (P.n' v)) (A B : Matrix (Fin (P.m + 1)) (Fin (P.m + 1)) (P.Qq v)) :
    P.gPos v s (A * B) = P.gPos v s A * P.gPos v s B := by
  simp only [jd_gPos, map_mul]

/- English proof (translation)
Simplify using `only [jd_gPos, map_one]`.
-/
theorem jd_gPos_one (v : Fin P.nV) (s : Fin (P.n' v)) : P.gPos v s 1 = 1 := by
  simp only [jd_gPos, map_one]

/- English proof (translation)
Apply `MvPolynomial.algHom_ext` to reduce the goal to its premises. Introduce `x`. Unfold `Places.subst`. Rewrite using `[aeval_X, Finset.sum_eq_single x.2.2.1]`. Simplify using the standard rewrite rules.

Introduce `b _ hb`. Simplify using `[Matrix.one_apply_ne' hb]`. Simplify using the standard rewrite rules.
-/
theorem jd_subst_one : P.subst (fun _ _ => 1) = AlgHom.id Kf P.Xsp := by
  apply MvPolynomial.algHom_ext
  intro x
  unfold Places.subst
  rw [aeval_X, Finset.sum_eq_single x.2.2.1]
  · simp
  · intro b _ hb
    simp [Matrix.one_apply_ne' hb]
  · simp

/- English proof (translation)
Apply `MvPolynomial.algHom_ext` to reduce the goal to its premises. Introduce `x`. Unfold `Places.subst`. Simplify using `only [AlgHom.comp_apply, aeval_X, map_sum, map_mul, algHom_C, Matrix.mul_apply, Finset.sum_mul, Finset.mul_sum]`. Rewrite using `[Finset.sum_comm]`.

Apply `Finset.sum_congr rfl` to reduce the goal to its premises. Introduce `c _`. Apply `Finset.sum_congr rfl` to reduce the goal to its premises. Introduce `b _`. Rewrite using `[MvPolynomial.algebraMap_eq]`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem jd_subst_comp (M N : ∀ v, Fin (P.n' v) → Matrix (Fin (P.m + 1)) (Fin (P.m + 1)) Kf) :
    (P.subst M).comp (P.subst N) = P.subst (fun v s => N v s * M v s) := by
  apply MvPolynomial.algHom_ext
  intro x
  unfold Places.subst
  simp only [AlgHom.comp_apply, aeval_X, map_sum, map_mul, algHom_C, Matrix.mul_apply, Finset.sum_mul,
    Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro c _
  apply Finset.sum_congr rfl
  intro b _
  rw [MvPolynomial.algebraMap_eq]
  ring

/- English proof (translation)
Unfold `Places.natAct`. Simplify using `only [Units.val_one, inv_one, jd_gPos_one, Matrix.det_one, one_zpow, Finset.prod_const_one, one_smul, jd_subst_one]`. Both sides reduce to the same expression.
-/
theorem jd_natAct_one : P.natAct (fun _ => 1) = LinearMap.id := by
  unfold Places.natAct
  simp only [Units.val_one, inv_one, jd_gPos_one, Matrix.det_one, one_zpow, Finset.prod_const_one, one_smul,
    jd_subst_one]
  rfl

/- English proof (translation)
Unfold `Places.natAct`. Apply `LinearMap.ext` to reduce the goal to its premises. Introduce `F`. Simplify using `only [LinearMap.smul_apply, LinearMap.comp_apply, AlgHom.toLinearMap_apply, map_smul, smul_smul]`. Establish `h1 : (P.subst fun v s => P.gPos v s ((A v)⁻¹ : GL (Fin (P.m + 1)) (P.Qq v))) ((P.subst fun v s => P.gPos v s ((B v)⁻¹ : GL (Fin (P.m + 1)) (P.Qq v))) F) = (P.subst fun v s => P.gPos v s ((A v * B v)⁻¹ : GL (Fin (P.m + 1)) (P.Qq v))) F`.

Rewrite using `[← AlgHom.comp_apply, jd_subst_comp]`. Use `congr 2`. Use function extensionality and compare the values at `v s`. Rewrite using `[← jd_gPos_mul, mul_inv_rev, Units.val_mul]`. Rewrite using `[h1]`.

Use `congr 1`. Rewrite using `[← Finset.prod_mul_distrib]`. Apply `Finset.prod_congr rfl` to reduce the goal to its premises. Introduce `v _`. Rewrite using `[← Finset.prod_mul_distrib]`.

Apply `Finset.prod_congr rfl` to reduce the goal to its premises. Introduce `s _`. Rewrite using `[Units.val_mul, jd_gPos_mul, Matrix.det_mul, mul_zpow, mul_comm]`.
-/
theorem jd_natAct_mul (A B : ∀ v, GL (Fin (P.m + 1)) (P.Qq v)) :
    P.natAct (fun v => A v * B v) = P.natAct A ∘ₗ P.natAct B := by
  unfold Places.natAct
  apply LinearMap.ext
  intro F
  simp only [LinearMap.smul_apply, LinearMap.comp_apply, AlgHom.toLinearMap_apply, map_smul, smul_smul]
  have h1 : (P.subst fun v s => P.gPos v s ((A v)⁻¹ : GL (Fin (P.m + 1)) (P.Qq v)))
      ((P.subst fun v s => P.gPos v s ((B v)⁻¹ : GL (Fin (P.m + 1)) (P.Qq v))) F) =
      (P.subst fun v s => P.gPos v s ((A v * B v)⁻¹ : GL (Fin (P.m + 1)) (P.Qq v))) F := by
    rw [← AlgHom.comp_apply, jd_subst_comp]
    congr 2
    funext v s
    rw [← jd_gPos_mul, mul_inv_rev, Units.val_mul]
  rw [h1]
  congr 1
  rw [← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro v _
  rw [← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro s _
  rw [Units.val_mul, jd_gPos_mul, Matrix.det_mul, mul_zpow, mul_comm]

variable {P} (C : Level P)

/- English proof (translation)
Use function extensionality and compare the values at `v`. Unfold `Level.smul`. Use extensionality with `x`. Simplify using the standard rewrite rules.
-/
theorem jd_smul_one (L : P.Tup) : C.smul 1 L = L := by
  funext v
  unfold Level.smul
  ext x
  simp

/- English proof (translation)
Use function extensionality and compare the values at `v`. Unfold `Level.smul`. Use extensionality with `x`. Simplify using `only [Submodule.mem_map, LinearMap.restrictScalars_apply, Matrix.mulVecLin_apply, map_mul, Units.val_mul]`. Prove the components needed by the constructor for the conclusion.

Introduce and unpack `⟨y, hy, rfl⟩`. Conclude with `⟨_, ⟨y, hy, rfl⟩, by rw [Matrix.mulVec_mulVec]⟩`. Introduce and unpack `⟨_, ⟨y, hy, rfl⟩, rfl⟩`. Conclude with `⟨y, hy, by rw [Matrix.mulVec_mulVec]⟩`.
-/
theorem jd_smul_mul (γ γ' : C.Γ) (L : P.Tup) : C.smul (γ * γ') L = C.smul γ (C.smul γ' L) := by
  funext v
  unfold Level.smul
  ext x
  simp only [Submodule.mem_map, LinearMap.restrictScalars_apply, Matrix.mulVecLin_apply, map_mul, Units.val_mul]
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨_, ⟨y, hy, rfl⟩, by rw [Matrix.mulVec_mulVec]⟩
  · rintro ⟨_, ⟨y, hy, rfl⟩, rfl⟩
    exact ⟨y, hy, by rw [Matrix.mulVec_mulVec]⟩

/- English proof (translation)
Unfold `Level.actX`. Simplify using `only [map_one]`. Conclude with `jd_natAct_one P`.
-/
theorem jd_actX_one : C.actX 1 = LinearMap.id := by
  unfold Level.actX
  simp only [map_one]
  exact jd_natAct_one P

/- English proof (translation)
Unfold `Level.actX`. Simplify using `only [map_mul]`. Conclude with `jd_natAct_mul P _ _`.
-/
theorem jd_actX_mul (γ γ' : C.Γ) : C.actX (γ * γ') = C.actX γ ∘ₗ C.actX γ' := by
  unfold Level.actX
  simp only [map_mul]
  exact jd_natAct_mul P _ _

/- English proof (translation)
Introduce `v` and use `nt_lat_map (W := P.W v) (C.act v γ) (L v) (hL v)`.
-/
theorem jd_lat (γ : C.Γ) (L : P.Tup) (hL : P.IsLatTup L) : P.IsLatTup (C.smul γ L) :=
  fun v => nt_lat_map (W := P.W v) (C.act v γ) (L v) (hL v)

end Act

variable {p : ℕ}

/- English proof (translation)
Use function extensionality and compare the values at `i' L`. Simplify using `only [delta, Pi.add_apply]`. Apply the tactic sequence `split_ifs <;> simp [smul_add]`.
-/
theorem jd_add (G : GAtP p) (i : G.comp) (L0 : G.P.Tup) (ξ η : G.P.Xsp) :
    delta G i L0 (ξ + η) = delta G i L0 ξ + delta G i L0 η := by
  funext i' L
  simp only [delta, Pi.add_apply]
  split_ifs <;> simp [smul_add]

/- English proof (translation)
Use function extensionality and compare the values at `i' L`. Simplify using `only [delta, Pi.smul_apply]`. Use `split_ifs`. Rewrite using `[LinearMap.map_smul_of_tower, smul_comm]`. Simplify using the standard rewrite rules.

Simplify using the standard rewrite rules.
-/
theorem jd_smul (G : GAtP p) (i : G.comp) (L0 : G.P.Tup) (c : G.O) (ξ : G.P.Xsp) :
    delta G i L0 (c • ξ) = c • delta G i L0 ξ := by
  funext i' L
  simp only [delta, Pi.smul_apply]
  split_ifs
  · rw [LinearMap.map_smul_of_tower, smul_comm]
  · simp
  · simp

/- English proof (translation)
Simplify using `only [delta]`. Break down `h with h | h` into its components or cases. Apply the tactic sequence `split_ifs <;> rfl`. Rewrite using `[dif_neg h]`.
-/
theorem jd_zero (G : GAtP p) (i : G.comp) (L0 : G.P.Tup) (ξ : G.P.Xsp) (i' : G.comp) (L : G.P.Tup)
    (h : i' ≠ i ∨ ¬ ∃ γ : (G.lev i).Γ, L = (G.lev i).smul γ L0) : delta G i L0 ξ i' L = 0 := by
  simp only [delta]
  rcases h with h | h
  · split_ifs <;> rfl
  · rw [dif_neg h]

/- English proof (translation)
Establish `h2 : (G.lev i).smul (γ'⁻¹ * γ) L0 = L0`. Rewrite using `[jd_smul_mul, h, ← jd_smul_mul, inv_mul_cancel, jd_smul_one]`. Conclude with `(inv_mul_eq_one.1 (h1 i _ L0 hL0 h2)).symm`.
-/
theorem jd_uniq (G : GAtP p) (h1 : G.TrivStab) (i : G.comp) (L0 : G.P.Tup) (hL0 : G.P.IsLatTup L0)
    (γ γ' : (G.lev i).Γ) (h : (G.lev i).smul γ L0 = (G.lev i).smul γ' L0) : γ = γ' := by
  have h2 : (G.lev i).smul (γ'⁻¹ * γ) L0 = L0 := by
    rw [jd_smul_mul, h, ← jd_smul_mul, inv_mul_cancel, jd_smul_one]
  exact (inv_mul_eq_one.1 (h1 i _ L0 hL0 h2)).symm

/- English proof (translation)
Establish `hex : ∃ γ' : (G.lev i).Γ, (G.lev i).smul γ L0 = (G.lev i).smul γ' L0` using `⟨γ, rfl⟩`. Establish `hc : hex.choose = γ` using `(jd_uniq G h1 i L0 hL0 _ _ hex.choose_spec).symm`. Simplify using `only [delta]`. Rewrite using `[dif_pos hex, if_pos trivial, hc]`.
-/
theorem jd_apply (G : GAtP p) (h1 : G.TrivStab) (i : G.comp) (L0 : G.P.Tup) (γ : (G.lev i).Γ) (ξ : G.P.Xsp)
    (hL0 : G.P.IsLatTup L0) :
    delta G i L0 ξ i ((G.lev i).smul γ L0) = ((G.lev i).χ γ : G.O) • (G.lev i).actX γ ξ := by
  have hex : ∃ γ' : (G.lev i).Γ, (G.lev i).smul γ L0 = (G.lev i).smul γ' L0 := ⟨γ, rfl⟩
  have hc : hex.choose = γ := (jd_uniq G h1 i L0 hL0 _ _ hex.choose_spec).symm
  simp only [delta]
  rw [dif_pos hex, if_pos trivial, hc]

/- English proof (translation)
Establish `h` using `jd_apply G h1 i L0 1 ξ hL0`. Rewrite `h` using `[jd_smul_one, map_one, jd_actX_one]`. Simplify using `using h`.
-/
theorem jd_self (G : GAtP p) (h1 : G.TrivStab) (i : G.comp) (L0 : G.P.Tup) (ξ : G.P.Xsp)
    (hL0 : G.P.IsLatTup L0) : delta G i L0 ξ i L0 = ξ := by
  have h := jd_apply G h1 i L0 1 ξ hL0
  rw [jd_smul_one, map_one, jd_actX_one] at h
  simpa using h

/- English proof (translation)
Unfold `GAtP.funMod`. Rewrite using `[Submodule.mem_pi]`. Prove the components needed by the constructor for the conclusion. Introduce `hF i`. Establish `h : F i ∈ (G.lev i).funMod Hv` using `hF i (Set.mem_univ i)`.

Unfold `Level.funMod at h`. Simplify using `only [Submodule.mem_inf, Submodule.mem_iInf, Submodule.mem_comap, LinearMap.mem_ker, LinearMap.proj_apply, LinearMap.sub_apply, LinearMap.comp_apply, LinearMap.smul_apply, LinearMap.restrictScalars_apply, sub_eq_zero] at h`. Conclude with `⟨h.1.1, h.1.2, fun γ L => h.2 γ L⟩`. Introduce `hF i _`. Unfold `Level.funMod`.

Simplify using `only [Submodule.mem_inf, Submodule.mem_iInf, Submodule.mem_comap, LinearMap.mem_ker, LinearMap.proj_apply, LinearMap.sub_apply, LinearMap.comp_apply, LinearMap.smul_apply, LinearMap.restrictScalars_apply, sub_eq_zero]`. Conclude with `⟨⟨(hF i).1, (hF i).2.1⟩, fun γ L => (hF i).2.2 γ L⟩`.
-/
theorem jd_fmem (G : GAtP p) (Hv : G.P.Tup → Submodule G.O G.P.Xsp) (F : G.Fn) :
    F ∈ G.funMod Hv ↔ ∀ i : G.comp,
      (∀ L, G.P.IsLatTup L → F i L ∈ Hv L) ∧ (∀ L, ¬ G.P.IsLatTup L → F i L = 0) ∧
      ∀ (γ : (G.lev i).Γ) (L : G.P.Tup),
        F i ((G.lev i).smul γ L) = ((G.lev i).χ γ : G.O) • (G.lev i).actX γ (F i L) := by
  unfold GAtP.funMod
  rw [Submodule.mem_pi]
  constructor
  · intro hF i
    have h : F i ∈ (G.lev i).funMod Hv := hF i (Set.mem_univ i)
    unfold Level.funMod at h
    simp only [Submodule.mem_inf, Submodule.mem_iInf, Submodule.mem_comap, LinearMap.mem_ker,
      LinearMap.proj_apply, LinearMap.sub_apply, LinearMap.comp_apply, LinearMap.smul_apply,
      LinearMap.restrictScalars_apply, sub_eq_zero] at h
    exact ⟨h.1.1, h.1.2, fun γ L => h.2 γ L⟩
  · intro hF i _
    unfold Level.funMod
    simp only [Submodule.mem_inf, Submodule.mem_iInf, Submodule.mem_comap, LinearMap.mem_ker,
      LinearMap.proj_apply, LinearMap.sub_apply, LinearMap.comp_apply, LinearMap.smul_apply,
      LinearMap.restrictScalars_apply, sub_eq_zero]
    exact ⟨⟨(hF i).1, (hF i).2.1⟩, fun γ L => (hF i).2.2 γ L⟩

/- English proof (translation)
Rewrite using `[jd_fmem]`. Introduce `i'`. Distinguish the cases in `hi : i' = i`. Substitute `hi` using the available equality. Use `⟨fun L _ => ?_, fun L hL => ?_, fun γ L => ?_⟩` and prove the remaining obligations.

Distinguish the cases in `hex : ∃ γ : (G.lev i').Γ, L = (G.lev i').smul γ L0`. Take `⟨γ, rfl⟩` from `hex`. Rewrite using `[jd_apply G h1 i' L0 γ ξ hL0]`. Conclude with `hE i' γ L0 hL0 ξ hξ`. Rewrite using `[jd_zero G i' L0 ξ i' L (Or.inr hex)]`.

Conclude with `Submodule.zero_mem _`. Apply `jd_zero G i' L0 ξ i' L (Or.inr ?_)` to reduce the goal to its premises. Introduce and unpack `⟨γ, rfl⟩`. Conclude with `hL (jd_lat (G.lev i') γ L0 hL0)`. Distinguish the cases in `hex : ∃ γ0 : (G.lev i').Γ, L = (G.lev i').smul γ0 L0`.

Take `⟨γ0, rfl⟩` from `hex`. Rewrite using `[← jd_smul_mul, jd_apply G h1 i' L0 _ ξ hL0, jd_apply G h1 i' L0 _ ξ hL0, map_mul, Units.val_mul, jd_actX_mul, LinearMap.comp_apply, LinearMap.map_smul_of_tower, smul_smul]`. Rewrite using `[jd_zero G i' L0 ξ i' L (Or.inr hex), map_zero, smul_zero]`. Apply `jd_zero G i' L0 ξ i' _ (Or.inr ?_)` to reduce the goal to its premises. Introduce and unpack `⟨γ1, h⟩`.

Apply `hex` to reduce the goal to its premises. Use `⟨γ⁻¹ * γ1, ?_⟩` and prove the remaining obligations. Rewrite using `[jd_smul_mul, ← h, ← jd_smul_mul, inv_mul_cancel, jd_smul_one]`. Establish `hz : ∀ L, delta G i L0 ξ i' L = 0` using `fun L => jd_zero G i L0 ξ i' L (Or.inl hi)`. Use `⟨fun L _ => ?_, fun L _ => hz L, fun γ L => ?_⟩` and prove the remaining obligations.

Rewrite using `[hz L]`. Conclude with `Submodule.zero_mem _`. Rewrite using `[hz, hz, map_zero, smul_zero]`.
-/
theorem jd_mem (G : GAtP p) (h1 : G.TrivStab) (Hv : G.P.Tup → Submodule G.O G.P.Xsp) (hE : EquivSys G Hv)
    (i : G.comp) (L0 : G.P.Tup) (hL0 : G.P.IsLatTup L0) (ξ : G.P.Xsp) (hξ : ξ ∈ Hv L0) :
    delta G i L0 ξ ∈ G.funMod Hv := by
  rw [jd_fmem]
  intro i'
  by_cases hi : i' = i
  · subst hi
    refine ⟨fun L _ => ?_, fun L hL => ?_, fun γ L => ?_⟩
    · by_cases hex : ∃ γ : (G.lev i').Γ, L = (G.lev i').smul γ L0
      · obtain ⟨γ, rfl⟩ := hex
        rw [jd_apply G h1 i' L0 γ ξ hL0]
        exact hE i' γ L0 hL0 ξ hξ
      · rw [jd_zero G i' L0 ξ i' L (Or.inr hex)]
        exact Submodule.zero_mem _
    · apply jd_zero G i' L0 ξ i' L (Or.inr ?_)
      rintro ⟨γ, rfl⟩
      exact hL (jd_lat (G.lev i') γ L0 hL0)
    · by_cases hex : ∃ γ0 : (G.lev i').Γ, L = (G.lev i').smul γ0 L0
      · obtain ⟨γ0, rfl⟩ := hex
        rw [← jd_smul_mul, jd_apply G h1 i' L0 _ ξ hL0, jd_apply G h1 i' L0 _ ξ hL0, map_mul, Units.val_mul,
          jd_actX_mul, LinearMap.comp_apply, LinearMap.map_smul_of_tower, smul_smul]
      · rw [jd_zero G i' L0 ξ i' L (Or.inr hex), map_zero, smul_zero]
        apply jd_zero G i' L0 ξ i' _ (Or.inr ?_)
        rintro ⟨γ1, h⟩
        apply hex
        refine ⟨γ⁻¹ * γ1, ?_⟩
        rw [jd_smul_mul, ← h, ← jd_smul_mul, inv_mul_cancel, jd_smul_one]
  · have hz : ∀ L, delta G i L0 ξ i' L = 0 := fun L => jd_zero G i L0 ξ i' L (Or.inl hi)
    refine ⟨fun L _ => ?_, fun L _ => hz L, fun γ L => ?_⟩
    · rw [hz L]; exact Submodule.zero_mem _
    · rw [hz, hz, map_zero, smul_zero]

end Formalism.MainNotions.G.LatticeSystems

namespace Formalism.MainNotions.G.LatticeSystems

open Formalism.MainNotions.G Formalism.MainNotions.SelectionLemmas Formalism.G0

variable {p : ℕ}

def jd_Orb (G : GAtP p) (i : G.comp) (L L' : G.P.Tup) : Prop := ∃ γ : (G.lev i).Γ, L' = (G.lev i).smul γ L

/- English proof (translation)
Assemble the required witnesses or components as `⟨1, (jd_smul_one _ L).symm⟩`.
-/
theorem jd_Orb_refl (G : GAtP p) (i : G.comp) (L : G.P.Tup) : jd_Orb G i L L := ⟨1, (jd_smul_one _ L).symm⟩

/- English proof (translation)
Take `⟨γ, rfl⟩` from `h`. Conclude with `⟨γ⁻¹, by rw [← jd_smul_mul, inv_mul_cancel, jd_smul_one]⟩`.
-/
theorem jd_Orb_symm (G : GAtP p) (i : G.comp) {L L' : G.P.Tup} (h : jd_Orb G i L L') : jd_Orb G i L' L := by
  obtain ⟨γ, rfl⟩ := h
  exact ⟨γ⁻¹, by rw [← jd_smul_mul, inv_mul_cancel, jd_smul_one]⟩

/- English proof (translation)
Take `⟨γ, rfl⟩` from `h`. Take `⟨γ', rfl⟩` from `h'`. Conclude with `⟨γ' * γ, by rw [jd_smul_mul]⟩`.
-/
theorem jd_Orb_trans (G : GAtP p) (i : G.comp) {L L' L'' : G.P.Tup} (h : jd_Orb G i L L')
    (h' : jd_Orb G i L' L'') : jd_Orb G i L L'' := by
  obtain ⟨γ, rfl⟩ := h
  obtain ⟨γ', rfl⟩ := h'
  exact ⟨γ' * γ, by rw [jd_smul_mul]⟩

/- English proof (translation)
Use `choose R hRlat hRcov using h2`. Establish `: Nonempty G.P.Tup` using `⟨fun _ => ⊥⟩`. Set `S : ∀ i : G.comp, G.P.Tup → Finset G.P.Tup` to `fun i L => (R i).filter fun L' => jd_Orb G i L L'`. Set `c : ∀ i : G.comp, G.P.Tup → G.P.Tup` to `fun i L => Classical.epsilon fun x => x ∈ S i L`. Establish `hc : ∀ i L, L ∈ R i → c i L ∈ S i L` using `fun i L hL => Classical.epsilon_spec (p := fun x => x ∈ S i L) ⟨L, Finset.mem_filter.2 ⟨hL, jd_Orb_refl G i L⟩⟩`.

Establish `hS : ∀ i L L', jd_Orb G i L L' → S i L = S i L'`. Introduce `i L L' h`. Use extensionality with `x`. Simplify using `only [S, Finset.mem_filter]`. Conclude with `⟨fun hx => ⟨hx.1, jd_Orb_trans G i (jd_Orb_symm G i h) hx.2⟩, fun hx => ⟨hx.1, jd_Orb_trans G i h hx.2⟩⟩`.

Use `⟨Finset.univ.biUnion fun i => (R i).image fun L => (i, c i L), ?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `r hr`. Take `⟨i, -, hr⟩` from `Finset.mem_biUnion.1 hr`. Take `⟨L, hL, rfl⟩` from `Finset.mem_image.1 hr`. Conclude with `hRlat i _ (Finset.mem_filter.1 (hc i L hL)).1`.

Introduce `r hr r' hr' h11 horb`. Take `⟨i, -, hr⟩` from `Finset.mem_biUnion.1 hr`. Take `⟨L, hL, rfl⟩` from `Finset.mem_image.1 hr`. Take `⟨i', -, hr'⟩` from `Finset.mem_biUnion.1 hr'`. Take `⟨L', hL', rfl⟩` from `Finset.mem_image.1 hr'`.

Establish `hii : i = i'` using `h11`. Substitute `hii` using the available equality. Establish `o1 : jd_Orb G i L (c i L)` using `(Finset.mem_filter.1 (hc i L hL)).2`. Establish `o2 : jd_Orb G i L' (c i L')` using `(Finset.mem_filter.1 (hc i L' hL')).2`. Establish `o3 : jd_Orb G i (c i L) (c i L')` using `horb`.

Establish `o4 : jd_Orb G i L L'` using `jd_Orb_trans G i (jd_Orb_trans G i o1 o3) (jd_Orb_symm G i o2)`. Establish `: c i L = c i L'` using `by show Classical.epsilon (fun x => x ∈ S i L) = Classical.epsilon (fun x => x ∈ S i L')`. Rewrite using `[hS i L L' o4]`. Rewrite using `[this]`. Introduce `i L hL`.

Take `⟨L0, hL0, hγ⟩` from `hRcov i L hL`. Use `⟨(i, c i L0), Finset.mem_biUnion.2 ⟨i, Finset.mem_univ i, Finset.mem_image.2 ⟨L0, hL0, rfl⟩⟩, rfl, ?_⟩` and prove the remaining obligations. Establish `o1 : jd_Orb G i L0 (c i L0)` using `(Finset.mem_filter.1 (hc i L0 hL0)).2`. Conclude with `jd_Orb_trans G i (jd_Orb_symm G i o1) hγ`.
-/
theorem jd_reps (G : GAtP p) (h2 : G.FinClasses) : ∃ reps, IsReps G reps := by
  classical
  choose R hRlat hRcov using h2
  have : Nonempty G.P.Tup := ⟨fun _ => ⊥⟩

  let S : ∀ i : G.comp, G.P.Tup → Finset G.P.Tup := fun i L => (R i).filter fun L' => jd_Orb G i L L'
  let c : ∀ i : G.comp, G.P.Tup → G.P.Tup := fun i L => Classical.epsilon fun x => x ∈ S i L
  have hc : ∀ i L, L ∈ R i → c i L ∈ S i L := fun i L hL =>
    Classical.epsilon_spec (p := fun x => x ∈ S i L) ⟨L, Finset.mem_filter.2 ⟨hL, jd_Orb_refl G i L⟩⟩
  have hS : ∀ i L L', jd_Orb G i L L' → S i L = S i L' := by
    intro i L L' h
    ext x
    simp only [S, Finset.mem_filter]
    exact ⟨fun hx => ⟨hx.1, jd_Orb_trans G i (jd_Orb_symm G i h) hx.2⟩,
      fun hx => ⟨hx.1, jd_Orb_trans G i h hx.2⟩⟩
  refine ⟨Finset.univ.biUnion fun i => (R i).image fun L => (i, c i L), ?_, ?_, ?_⟩
  · intro r hr
    obtain ⟨i, -, hr⟩ := Finset.mem_biUnion.1 hr
    obtain ⟨L, hL, rfl⟩ := Finset.mem_image.1 hr
    exact hRlat i _ (Finset.mem_filter.1 (hc i L hL)).1
  · intro r hr r' hr' h11 horb
    obtain ⟨i, -, hr⟩ := Finset.mem_biUnion.1 hr
    obtain ⟨L, hL, rfl⟩ := Finset.mem_image.1 hr
    obtain ⟨i', -, hr'⟩ := Finset.mem_biUnion.1 hr'
    obtain ⟨L', hL', rfl⟩ := Finset.mem_image.1 hr'
    have hii : i = i' := h11
    subst hii
    have o1 : jd_Orb G i L (c i L) := (Finset.mem_filter.1 (hc i L hL)).2
    have o2 : jd_Orb G i L' (c i L') := (Finset.mem_filter.1 (hc i L' hL')).2
    have o3 : jd_Orb G i (c i L) (c i L') := horb
    have o4 : jd_Orb G i L L' := jd_Orb_trans G i (jd_Orb_trans G i o1 o3) (jd_Orb_symm G i o2)
    have : c i L = c i L' := by
      show Classical.epsilon (fun x => x ∈ S i L) = Classical.epsilon (fun x => x ∈ S i L')
      rw [hS i L L' o4]
    rw [this]
  · intro i L hL
    obtain ⟨L0, hL0, hγ⟩ := hRcov i L hL
    refine ⟨(i, c i L0), Finset.mem_biUnion.2 ⟨i, Finset.mem_univ i, Finset.mem_image.2 ⟨L0, hL0, rfl⟩⟩, rfl, ?_⟩
    have o1 : jd_Orb G i L0 (c i L0) := (Finset.mem_filter.1 (hc i L0 hL0)).2
    exact jd_Orb_trans G i (jd_Orb_symm G i o1) hγ

/- English proof (translation)
Take `⟨hlat, hirr, hcov⟩` from `hR`. Rewrite `hF` using `[jd_fmem]`. Use function extensionality and compare the values at `i L`. Rewrite using `[Finset.sum_apply, Finset.sum_apply]`. Distinguish the cases in `hL : G.P.IsLatTup L`.

Take `⟨r0, hr0, rfl, γ, rfl⟩` from `hcov i L hL`. Rewrite using `[Finset.sum_eq_single r0]`. Rewrite using `[jd_apply G h1 r0.1 r0.2 γ _ (hlat r0 hr0)]`. Conclude with `(hF r0.1).2.2 γ r0.2`. Introduce `r hr hne`.

Distinguish the cases in `h11 : r0.1 = r.1`. Apply `jd_zero right` to reduce the goal to its premises. Introduce `hex`. Apply `hne` to reduce the goal to its premises. Apply `hirr r hr r0 hr0 h11.symm` to reduce the goal to its premises.

Take `⟨γ1, hγ1⟩` from `hex`. Take `⟨i0, a0⟩` from `r0`. Take `⟨i1, a1⟩` from `r`. Simplify using `only at h11`. Substitute `h11` using the available equality.

Conclude with `jd_Orb_trans G i0 ⟨γ1, hγ1⟩ (jd_Orb_symm G i0 ⟨γ, rfl⟩)`. Conclude with `jd_zero G _ _ _ _ _ (Or.inl h11)`. Introduce `h`. Conclude with `absurd hr0 h`. Rewrite using `[(hF i).2.1 L hL]`.

Use `symm`. Apply `Finset.sum_eq_zero` to reduce the goal to its premises. Introduce `r hr`. Distinguish the cases in `h11 : i = r.1`. Apply `jd_zero right` to reduce the goal to its premises.

Introduce and unpack `⟨γ, rfl⟩`. Conclude with `hL (jd_lat _ γ r.2 (hlat r hr))`. Conclude with `jd_zero G _ _ _ _ _ (Or.inl h11)`.
-/
theorem jd_decomp (G : GAtP p) (h1 : G.TrivStab) (reps : Finset (G.comp × G.P.Tup)) (hR : IsReps G reps)
    (Hv : G.P.Tup → Submodule G.O G.P.Xsp) (F : G.Fn) (hF : F ∈ G.funMod Hv) :
    F = ∑ r ∈ reps, delta G r.1 r.2 (F r.1 r.2) := by
  classical
  obtain ⟨hlat, hirr, hcov⟩ := hR
  rw [jd_fmem] at hF
  funext i L
  rw [Finset.sum_apply, Finset.sum_apply]
  by_cases hL : G.P.IsLatTup L
  · obtain ⟨r0, hr0, rfl, γ, rfl⟩ := hcov i L hL
    rw [Finset.sum_eq_single r0]
    · rw [jd_apply G h1 r0.1 r0.2 γ _ (hlat r0 hr0)]
      exact (hF r0.1).2.2 γ r0.2
    · intro r hr hne
      by_cases h11 : r0.1 = r.1
      · apply jd_zero
        right
        intro hex
        apply hne
        apply hirr r hr r0 hr0 h11.symm
        obtain ⟨γ1, hγ1⟩ := hex

        obtain ⟨i0, a0⟩ := r0
        obtain ⟨i1, a1⟩ := r
        simp only at h11
        subst h11
        exact jd_Orb_trans G i0 ⟨γ1, hγ1⟩ (jd_Orb_symm G i0 ⟨γ, rfl⟩)
      · exact jd_zero G _ _ _ _ _ (Or.inl h11)
    · intro h
      exact absurd hr0 h
  · rw [(hF i).2.1 L hL]
    symm
    apply Finset.sum_eq_zero
    intro r hr
    by_cases h11 : i = r.1
    · apply jd_zero
      right
      rintro ⟨γ, rfl⟩
      exact hL (jd_lat _ γ r.2 (hlat r hr))
    · exact jd_zero G _ _ _ _ _ (Or.inl h11)

/- English proof (translation)
Assemble the required witnesses or components as `⟨jd_add G, jd_smul G, fun Hv hE i L0 hL0 ξ hξ => jd_mem G h1 Hv hE i L0 hL0 ξ hξ, fun i L0 γ ξ hL0 => jd_apply G h1 i L0 γ ξ hL0, fun i L0 ξ hL0 => jd_self G h1 i L0 ξ hL0, fun i L0 ξ i' L h => jd_zero G i L0 ξ i' L h, jd_reps G h2, fun reps hR Hv F hF => jd_decomp G h1 reps hR H …`.
-/
theorem jDelta (G : GAtP p) (h1 : G.TrivStab) (h2 : G.FinClasses) : JDelta G :=
  ⟨jd_add G, jd_smul G, fun Hv hE i L0 hL0 ξ hξ => jd_mem G h1 Hv hE i L0 hL0 ξ hξ,
    fun i L0 γ ξ hL0 => jd_apply G h1 i L0 γ ξ hL0, fun i L0 ξ hL0 => jd_self G h1 i L0 ξ hL0,
    fun i L0 ξ i' L h => jd_zero G i L0 ξ i' L h, jd_reps G h2,
    fun reps hR Hv F hF => jd_decomp G h1 reps hR Hv F hF⟩

end Formalism.MainNotions.G.LatticeSystems

namespace Formalism.MainNotions.G.LatticeSystems

open Formalism.MainNotions.G Formalism.GradedWeylDivisibility MvPolynomial Formalism.G0

def je_rho (Kf : Type) [Field Kf] {n' m : ℕ} (lam0 : Fin n' → Fin (m + 1) → ℤ)
    (g : Fin n' → Matrix (Fin (m + 1)) (Fin (m + 1)) Kf) :
    MvPolynomial (Fin n' × (Fin (m + 1) × Fin (m + 1))) Kf →ₗ[Kf]
      MvPolynomial (Fin n' × (Fin (m + 1) × Fin (m + 1))) Kf :=
  (∏ s, (g s).det ^ (-(lamAt lam0 s (Fin.last m)))) • (blockAct Kf (fun s => (g s)⁻¹)).toLinearMap

/- English proof (translation)
Simplify using `only [Algebra.smul_def, Finset.prod_mul_distrib, map_prod]`.
-/
theorem je_prod_smul {ι K A : Type*} [Fintype ι] [CommSemiring K] [CommSemiring A] [Algebra K A]
    (c : ι → K) (x : ι → A) : (∏ i, c i) • ∏ i, x i = ∏ i, c i • x i := by
  simp only [Algebra.smul_def, Finset.prod_mul_distrib, map_prod]

/- English proof (translation)
Unfold `colSpan`. Rewrite using `[Submodule.map_span, ← Set.range_comp]`. Use `congr 2`.
-/
theorem je_colSpan_mul {O Kf : Type} [CommRing O] [Field Kf] [Algebra O Kf] {k : ℕ}
    (g h : Matrix (Fin k) (Fin k) Kf) :
    (colSpan O h).map ((Matrix.mulVecLin g).restrictScalars O) = colSpan O (g * h) := by
  unfold colSpan
  rw [Submodule.map_span, ← Set.range_comp]
  congr 2

/- English proof (translation)
Establish `hgh : IsUnit (g * h).det` using `by rw [Matrix.det_mul]; exact hg.mul hh`. Rewrite `hF` using `[H0_eq_twisted_nabla hI m lam hlam h hh]`. Rewrite using `[H0_eq_twisted_nabla hI m lam hlam (g * h) hgh]`. Rewrite `hF` using `[nablaLTwMem O Kf m lam h hh]`. Rewrite using `[nablaLTwMem O Kf m lam (g * h) hgh]`.

Establish `e1 : rowAct Kf (g * h) (rowAct Kf g⁻¹ F) = rowAct Kf h F`. Establish `h1` using `rowActMul Kf (m + 1) (m + 1) (g * h) g⁻¹`. Establish `h2 : g⁻¹ * (g * h) = h`. Rewrite using `[← Matrix.mul_assoc, Matrix.nonsing_inv_mul g hg, Matrix.one_mul]`. Rewrite `h1` using `[h2]`.

Conclude with `congrArg (fun f => f F) h1`. Rewrite using `[map_smul, e1, smul_smul, Matrix.det_mul]`. Establish `e2 : (g.det * h.det) ^ (lam (Fin.last m)) * g.det ^ (-(lam (Fin.last m))) = h.det ^ (lam (Fin.last m))`. Rewrite using `[mul_zpow, mul_comm (g.det ^ _), mul_assoc, ← zpow_add₀ hg.ne_zero]`. Simplify using the standard rewrite rules.

Rewrite using `[e2]`. Conclude with `hF`.
-/
theorem H0_row_action_mem {O Kf : Type} [CommRing O] [Field Kf] [Algebra O Kf] (hI : H0IndepOfBasis O Kf) (m : ℕ)
    (lam : Fin (m + 1) → ℤ) (hlam : Antitone lam) (g h : Matrix (Fin (m + 1)) (Fin (m + 1)) Kf)
    (hg : IsUnit g.det) (hh : IsUnit h.det) (F : MvPolynomial (Fin (m + 1) × Fin (m + 1)) Kf)
    (hF : F ∈ H0 O m lam (colSpan O h)) :
    (g.det ^ (-(lam (Fin.last m)))) • rowAct Kf g⁻¹ F ∈ H0 O m lam (colSpan O (g * h)) := by
  have hgh : IsUnit (g * h).det := by rw [Matrix.det_mul]; exact hg.mul hh
  rw [H0_eq_twisted_nabla hI m lam hlam h hh] at hF
  rw [H0_eq_twisted_nabla hI m lam hlam (g * h) hgh]
  rw [nablaLTwMem O Kf m lam h hh] at hF
  rw [nablaLTwMem O Kf m lam (g * h) hgh]
  have e1 : rowAct Kf (g * h) (rowAct Kf g⁻¹ F) = rowAct Kf h F := by
    have h1 := rowActMul Kf (m + 1) (m + 1) (g * h) g⁻¹
    have h2 : g⁻¹ * (g * h) = h := by
      rw [← Matrix.mul_assoc, Matrix.nonsing_inv_mul g hg, Matrix.one_mul]
    rw [h2] at h1
    exact congrArg (fun f => f F) h1
  rw [map_smul, e1, smul_smul, Matrix.det_mul]
  have e2 : (g.det * h.det) ^ (lam (Fin.last m)) * g.det ^ (-(lam (Fin.last m))) =
      h.det ^ (lam (Fin.last m)) := by
    rw [mul_zpow, mul_comm (g.det ^ _), mul_assoc, ← zpow_add₀ hg.ne_zero]
    simp
  rw [e2]
  exact hF

/- English proof (translation)
Unfold `Hten tensorLat at hz ⊢`. Proceed by induction on `hz using Submodule.span_induction with`. Consider the case `mem x hx`. Take `⟨F, hF, rfl⟩` from `hx`. Apply `Submodule.subset_span` to reduce the goal to its premises.

Use `⟨fun s => ((g s).det ^ (-(lamAt lam0 s (Fin.last m)))) • rowAct Kf (g s)⁻¹ (F s), fun s => H0_row_action_mem hI m _ (hdom s) (g s) (h s) (hg s) (hh s) (F s) (hF s), ?_⟩` and prove the remaining obligations. Unfold `je_rho`. Rewrite using `[LinearMap.smul_apply, AlgHom.toLinearMap_apply, map_prod]`. Simplify using `only [(blockActTensor Kf Kf (Fin n') (m + 1) (m + 1) (fun s => (g s)⁻¹)).1, map_smul]`. Conclude with `je_prod_smul _ _`.

Consider the case `zero => rw [map_zero]`. Conclude with `Submodule.zero_mem _`. Consider the case `add x y _ _ hx hy => rw [map_add]`. Conclude with `Submodule.add_mem _ hx hy`. Consider the case `smul a x _ hx => rw [LinearMap.map_smul_of_tower]`.

Conclude with `Submodule.smul_mem _ a hx`.
-/
theorem je_Hten {O Kf : Type} [CommRing O] [Field Kf] [Algebra O Kf] (hI : H0IndepOfBasis O Kf) {n' m : ℕ}
    (lam0 : Fin n' → Fin (m + 1) → ℤ) (hdom : ∀ s, Antitone (lamAt lam0 s))
    (g h : Fin n' → Matrix (Fin (m + 1)) (Fin (m + 1)) Kf) (hg : ∀ s, IsUnit (g s).det)
    (hh : ∀ s, IsUnit (h s).det) (z : MvPolynomial (Fin n' × (Fin (m + 1) × Fin (m + 1))) Kf)
    (hz : z ∈ Hten O lam0 (fun s => colSpan O (h s))) :
    je_rho Kf lam0 g z ∈ Hten O lam0 (fun s => colSpan O (g s * h s)) := by
  unfold Hten tensorLat at hz ⊢
  induction hz using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨F, hF, rfl⟩ := hx
    apply Submodule.subset_span
    refine ⟨fun s => ((g s).det ^ (-(lamAt lam0 s (Fin.last m)))) • rowAct Kf (g s)⁻¹ (F s),
      fun s => H0_row_action_mem hI m _ (hdom s) (g s) (h s) (hg s) (hh s) (F s) (hF s), ?_⟩
    unfold je_rho
    rw [LinearMap.smul_apply, AlgHom.toLinearMap_apply, map_prod]
    simp only [(blockActTensor Kf Kf (Fin n') (m + 1) (m + 1) (fun s => (g s)⁻¹)).1, map_smul]
    exact je_prod_smul _ _
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add x y _ _ hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy
  | smul a x _ hx => rw [LinearMap.map_smul_of_tower]; exact Submodule.smul_mem _ a hx

/- English proof (translation)
Use `choose h hh hΛh using hΛ`. Establish `e1 : Λ = fun s => colSpan O (h s)` using `funext hΛh`. Establish `e2 : Λ' = fun s => colSpan O (g s * h s)`. Use function extensionality and compare the values at `s`. Rewrite using `[hΛ' s, hΛh s, je_colSpan_mul]`.

Rewrite using `[e2]`. Rewrite `hz` using `[e1]`. Conclude with `je_Hten hI lam0 hdom g h hg hh z hz`.
-/
theorem je_Hten' {O Kf : Type} [CommRing O] [Field Kf] [Algebra O Kf] (hI : H0IndepOfBasis O Kf) {n' m : ℕ}
    (lam0 : Fin n' → Fin (m + 1) → ℤ) (hdom : ∀ s, Antitone (lamAt lam0 s))
    (g : Fin n' → Matrix (Fin (m + 1)) (Fin (m + 1)) Kf) (hg : ∀ s, IsUnit (g s).det)
    (Λ Λ' : Fin n' → Submodule O (Fin (m + 1) → Kf)) (hΛ : ∀ s, IsLattice O (Λ s))
    (hΛ' : ∀ s, Λ' s = (Λ s).map ((Matrix.mulVecLin (g s)).restrictScalars O))
    (z : MvPolynomial (Fin n' × (Fin (m + 1) × Fin (m + 1))) Kf) (hz : z ∈ Hten O lam0 Λ) :
    je_rho Kf lam0 g z ∈ Hten O lam0 Λ' := by
  choose h hh hΛh using hΛ
  have e1 : Λ = fun s => colSpan O (h s) := funext hΛh
  have e2 : Λ' = fun s => colSpan O (g s * h s) := by
    funext s
    rw [hΛ' s, hΛh s, je_colSpan_mul]
  rw [e2]
  rw [e1] at hz
  exact je_Hten hI lam0 hdom g h hg hh z hz

/- English proof (translation)
Unfold `je_rho`. Rewrite using `[LinearMap.smul_apply]`. Apply `Submodule.smul_mem` to reduce the goal to its premises. Unfold `Vsp at hz ⊢`. Use `(blockActTensor Kf Kf (Fin n') (m + 1) (m + 1) (fun s => (g s)⁻¹)).2 _ _ (fun s F hF => ?_) z hz` and prove the remaining obligations.

Use `split_ifs at hF ⊢ with hs`. Conclude with `dualWeylRowStable Kf _ _ _ _ F hF`. Rewrite using `[(Submodule.mem_bot Kf).1 hF, map_zero]`. Conclude with `Submodule.zero_mem _`.
-/
theorem je_V (Kf : Type) [Field Kf] {n' m : ℕ} (lam0 : Fin n' → Fin (m + 1) → ℤ)
    (g : Fin n' → Matrix (Fin (m + 1)) (Fin (m + 1)) Kf)
    (z : MvPolynomial (Fin n' × (Fin (m + 1) × Fin (m + 1))) Kf) (hz : z ∈ Vsp Kf lam0) :
    je_rho Kf lam0 g z ∈ Vsp Kf lam0 := by
  unfold je_rho
  rw [LinearMap.smul_apply]
  apply Submodule.smul_mem
  unfold Vsp at hz ⊢
  refine (blockActTensor Kf Kf (Fin n') (m + 1) (m + 1) (fun s => (g s)⁻¹)).2 _ _ (fun s F hF => ?_) z hz
  split_ifs at hF ⊢ with hs
  · exact dualWeylRowStable Kf _ _ _ _ F hF
  · rw [(Submodule.mem_bot Kf).1 hF, map_zero]
    exact Submodule.zero_mem _

variable {p : ℕ}

def je_g (G : GAtP p) (v : Fin G.P.nV) (A : GL (Fin (G.P.m + 1)) (G.P.Qq v)) :
    Fin (G.P.n' v) → Matrix (Fin (G.P.m + 1)) (Fin (G.P.m + 1)) G.Kf :=
  fun s => G.P.gPos v s (A : Matrix (Fin (G.P.m + 1)) (Fin (G.P.m + 1)) (G.P.Qq v))

def je_loc (G : GAtP p) (v : Fin G.P.nV) (A : GL (Fin (G.P.m + 1)) (G.P.Qq v)) : Pol G v →ₗ[G.Kf] Pol G v :=
  je_rho G.Kf (G.P.lam0 v) (je_g G v A)

/- English proof (translation)
The claim follows from `la_tw_det (G.P.ι v) (G.P.σ v) s.val _ ((Matrix.isUnit_iff_isUnit_det _).1 A.isUnit)`.
-/
theorem je_g_det (G : GAtP p) (v : Fin G.P.nV) (A : GL (Fin (G.P.m + 1)) (G.P.Qq v)) (s : Fin (G.P.n' v)) :
    IsUnit (je_g G v A s).det :=
  la_tw_det (G.P.ι v) (G.P.σ v) s.val _ ((Matrix.isUnit_iff_isUnit_det _).1 A.isUnit)

/- English proof (translation)
Use function extensionality and compare the values at `i`. Simplify using `[twistVec, nt_phi, Matrix.mulVec, dotProduct, je_g, Places.gPos, map_sum, map_mul]`.
-/
theorem je_twist (G : GAtP p) (v : Fin G.P.nV) (A : GL (Fin (G.P.m + 1)) (G.P.Qq v)) (s : Fin (G.P.n' v))
    (x : Fin (G.P.m + 1) → G.P.Qq v) :
    twistVec (G.P.ι v) (G.P.σ v) s.val (nt_phi (G.P.W v) A x) =
      (je_g G v A s).mulVec (twistVec (G.P.ι v) (G.P.σ v) s.val x) := by
  funext i
  simp [twistVec, nt_phi, Matrix.mulVec, dotProduct, je_g, Places.gPos, map_sum, map_mul]

/- English proof (translation)
Unfold `extO`. Rewrite using `[Submodule.map_span, Submodule.map_coe, Set.image_image, Set.image_image]`. Use `congr 1`. Apply `Set.image_congr` to reduce the goal to its premises. Introduce `x _`.

Conclude with `je_twist G v A s x`.
-/
theorem je_extO (G : GAtP p) (v : Fin G.P.nV) (A : GL (Fin (G.P.m + 1)) (G.P.Qq v)) (s : Fin (G.P.n' v))
    (Lv : Lat G v) :
    extO G.O (G.P.ι v) (G.P.σ v) s.val (Lv.map (nt_phi (G.P.W v) A)) =
      (extO G.O (G.P.ι v) (G.P.σ v) s.val Lv).map ((Matrix.mulVecLin (je_g G v A s)).restrictScalars G.O) := by
  unfold extO
  rw [Submodule.map_span, Submodule.map_coe, Set.image_image, Set.image_image]
  congr 1
  apply Set.image_congr
  intro x _
  exact je_twist G v A s x

/- English proof (translation)
Unfold `LeAt`. Rewrite using `[Submodule.map_sup, je_extO]`. Use `congr 1`. Rewrite using `[Submodule.map_span, Submodule.map_coe, Set.image_image, Set.image_image]`. Use `congr 1`.

Apply `Set.image_congr` to reduce the goal to its premises. Introduce `x _`. Use `show (algebraMap G.O G.Kf G.P.w)⁻¹ • twistVec (G.P.ι v) (G.P.σ v) s.val ((p : G.P.W v) • nt_phi (G.P.W v) A x) = (je_g G v A s).mulVec ((algebraMap G.O G.Kf G.P.w)⁻¹ • twistVec (G.P.ι v) (G.P.σ v) s.val ((p : G.P.W v) • x))`. Rewrite using `[← map_smul, je_twist, Matrix.mulVec_smul]`.
-/
theorem je_LeAt (G : GAtP p) (v : Fin G.P.nV) (A : GL (Fin (G.P.m + 1)) (G.P.Qq v)) (s : Fin (G.P.n' v))
    (S T : Lat G v) :
    LeAt p (G.P.ι v) (G.P.σ v) G.P.w s.val (⟨S.map (nt_phi (G.P.W v) A), T.map (nt_phi (G.P.W v) A)⟩ :
        Edge (G.P.W v) (G.P.Qq v) (G.P.m + 1)) =
      (LeAt p (G.P.ι v) (G.P.σ v) G.P.w s.val (⟨S, T⟩ : Edge (G.P.W v) (G.P.Qq v) (G.P.m + 1))).map
        ((Matrix.mulVecLin (je_g G v A s)).restrictScalars G.O) := by
  unfold LeAt
  rw [Submodule.map_sup, je_extO]
  congr 1
  rw [Submodule.map_span, Submodule.map_coe, Set.image_image, Set.image_image]
  congr 1
  apply Set.image_congr
  intro x _
  show (algebraMap G.O G.Kf G.P.w)⁻¹ • twistVec (G.P.ι v) (G.P.σ v) s.val ((p : G.P.W v) • nt_phi (G.P.W v) A x) =
    (je_g G v A s).mulVec ((algebraMap G.O G.Kf G.P.w)⁻¹ • twistVec (G.P.ι v) (G.P.σ v) s.val ((p : G.P.W v) • x))
  rw [← map_smul, je_twist, Matrix.mulVec_smul]

/- English proof (translation)
Take `⟨g, hg, rfl⟩` from `hLv`. Conclude with `⟨_, la_tw_det (G.P.ι v) (G.P.σ v) s g hg, la_extO_G G v s g⟩`.
-/
theorem je_extO_lat (G : GAtP p) (v : Fin G.P.nV) (s : ℕ) (Lv : Lat G v) (hLv : IsLattice (G.P.W v) Lv) :
    IsLattice G.O (extO G.O (G.P.ι v) (G.P.σ v) s Lv) := by
  obtain ⟨g, hg, rfl⟩ := hLv
  exact ⟨_, la_tw_det (G.P.ι v) (G.P.σ v) s g hg, la_extO_G G v s g⟩

/- English proof (translation)
Take `⟨gs, h1, -, h3, -⟩` from `lb_edgeLat_of_basis G v (restEdgeBasis G v) e he`. Use `⟨_, ?_, h3 s⟩` and prove the remaining obligations. Rewrite using `[Matrix.det_mul]`. Conclude with `(h1 s).mul (lb_D_det _ _ _ (ch_w_ne_zero G v))`.
-/
theorem je_LeAt_lat (G : GAtP p) (v : Fin G.P.nV) (s : ℕ) (e : Edge (G.P.W v) (G.P.Qq v) (G.P.m + 1))
    (he : IsEdge p (G.P.n' v) G.P.r e) : IsLattice G.O (LeAt p (G.P.ι v) (G.P.σ v) G.P.w s e) := by
  obtain ⟨gs, h1, -, h3, -⟩ := lb_edgeLat_of_basis G v (restEdgeBasis G v) e he
  refine ⟨_, ?_, h3 s⟩
  rw [Matrix.det_mul]
  exact (h1 s).mul (lb_D_det _ _ _ (ch_w_ne_zero G v))

/- English proof (translation)
The claim follows from `kp_lamAt_antitone (G.P.lam0 v) (G.P.dom v) s`.
-/
theorem je_dom (G : GAtP p) (v : Fin G.P.nV) (s : Fin (G.P.n' v)) : Antitone (lamAt (G.P.lam0 v) s) :=
  kp_lamAt_antitone (G.P.lam0 v) (G.P.dom v) s

/- English proof (translation)
The claim follows from `je_Hten' (la_indep (lb_inj G v)) (G.P.lam0 v) (je_dom G v) (je_g G v A) (je_g_det G v A) _ _ (fun s => je_extO_lat G v s.val Lv hLv) (fun s => je_extO G v A s Lv) z hz`.
-/
theorem je_H_ext (G : GAtP p) (v : Fin G.P.nV) (A : GL (Fin (G.P.m + 1)) (G.P.Qq v)) (Lv : Lat G v)
    (hLv : IsLattice (G.P.W v) Lv) (z : Pol G v)
    (hz : z ∈ Hten G.O (G.P.lam0 v) fun s => extO G.O (G.P.ι v) (G.P.σ v) s.val Lv) :
    je_loc G v A z ∈ Hten G.O (G.P.lam0 v) fun s =>
      extO G.O (G.P.ι v) (G.P.σ v) s.val (Lv.map (nt_phi (G.P.W v) A)) :=
  je_Hten' (la_indep (lb_inj G v)) (G.P.lam0 v) (je_dom G v) (je_g G v A) (je_g_det G v A) _ _
    (fun s => je_extO_lat G v s.val Lv hLv) (fun s => je_extO G v A s Lv) z hz

/- English proof (translation)
The claim follows from `je_Hten' (la_indep (lb_inj G v)) (G.P.lam0 v) (je_dom G v) (je_g G v A) (je_g_det G v A) _ _ (fun s => je_LeAt_lat G v s.val _ he) (fun s => je_LeAt G v A s S T) z hz`.
-/
theorem je_H_Le (G : GAtP p) (v : Fin G.P.nV) (A : GL (Fin (G.P.m + 1)) (G.P.Qq v)) (S T : Lat G v)
    (he : IsEdge p (G.P.n' v) G.P.r (⟨S, T⟩ : Edge (G.P.W v) (G.P.Qq v) (G.P.m + 1))) (z : Pol G v)
    (hz : z ∈ Hten G.O (G.P.lam0 v) fun s => LeAt p (G.P.ι v) (G.P.σ v) G.P.w s.val
      (⟨S, T⟩ : Edge (G.P.W v) (G.P.Qq v) (G.P.m + 1))) :
    je_loc G v A z ∈ Hten G.O (G.P.lam0 v) fun s => LeAt p (G.P.ι v) (G.P.σ v) G.P.w s.val
      (⟨S.map (nt_phi (G.P.W v) A), T.map (nt_phi (G.P.W v) A)⟩ : Edge (G.P.W v) (G.P.Qq v) (G.P.m + 1)) :=
  je_Hten' (la_indep (lb_inj G v)) (G.P.lam0 v) (je_dom G v) (je_g G v A) (je_g_det G v A) _ _
    (fun s => je_LeAt_lat G v s.val _ he) (fun s => je_LeAt G v A s S T) z hz

def je_locV (G : GAtP p) (v : Fin G.P.nV) (A : GL (Fin (G.P.m + 1)) (G.P.Qq v)) :
    Vsp G.Kf (G.P.lam0 v) →ₗ[G.Kf] Vsp G.Kf (G.P.lam0 v) :=
  (je_loc G v A).restrict fun z hz => je_V G.Kf (G.P.lam0 v) (je_g G v A) z hz

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem je_locV_coe (G : GAtP p) (v : Fin G.P.nV) (A : GL (Fin (G.P.m + 1)) (G.P.Qq v))
    (x : Vsp G.Kf (G.P.lam0 v)) : ((je_locV G v A x : Vsp G.Kf (G.P.lam0 v)) : Pol G v) = je_loc G v A x := rfl

/- English proof (translation)
The claim follows from `je_H_ext G v A Lv hLv x hx`.
-/
theorem je_HL (G : GAtP p) (v : Fin G.P.nV) (A : GL (Fin (G.P.m + 1)) (G.P.Qq v)) (Lv : Lat G v)
    (hLv : IsLattice (G.P.W v) Lv) (x : Vsp G.Kf (G.P.lam0 v))
    (hx : x ∈ HL (O := G.O) (G.P.ι v) (G.P.σ v) (G.P.lam0 v) Lv) :
    je_locV G v A x ∈ HL (O := G.O) (G.P.ι v) (G.P.σ v) (G.P.lam0 v) (Lv.map (nt_phi (G.P.W v) A)) :=
  je_H_ext G v A Lv hLv x hx

/- English proof (translation)
The claim follows from `je_H_Le G v A S T he x hx`.
-/
theorem je_HLe (G : GAtP p) (v : Fin G.P.nV) (A : GL (Fin (G.P.m + 1)) (G.P.Qq v)) (S T : Lat G v)
    (he : IsEdge p (G.P.n' v) G.P.r (⟨S, T⟩ : Edge (G.P.W v) (G.P.Qq v) (G.P.m + 1)))
    (x : Vsp G.Kf (G.P.lam0 v))
    (hx : x ∈ HLe (O := G.O) p (G.P.ι v) (G.P.σ v) G.P.w (G.P.lam0 v)
      (⟨S, T⟩ : Edge (G.P.W v) (G.P.Qq v) (G.P.m + 1))) :
    je_locV G v A x ∈ HLe (O := G.O) p (G.P.ι v) (G.P.σ v) G.P.w (G.P.lam0 v)
      (⟨S.map (nt_phi (G.P.W v) A), T.map (nt_phi (G.P.W v) A)⟩ : Edge (G.P.W v) (G.P.Qq v) (G.P.m + 1)) :=
  je_H_Le G v A S T he x hx

/- English proof (translation)
Take `⟨y, hy, rfl⟩` from `hx`. Conclude with `⟨f y, h y hy, (map_smul f c y).symm⟩`.
-/
theorem je_scale {O Kf X Y : Type*} [CommRing O] [Field Kf] [Algebra O Kf] [AddCommGroup X] [Module Kf X]
    [Module O X] [IsScalarTower O Kf X] [AddCommGroup Y] [Module Kf Y] [Module O Y] [IsScalarTower O Kf Y]
    (c : Kf) (M : Submodule O X) (M' : Submodule O Y) (f : X →ₗ[Kf] Y) (h : ∀ y ∈ M, f y ∈ M') (x : X)
    (hx : x ∈ scale c M) : f x ∈ scale c M' := by
  obtain ⟨y, hy, rfl⟩ := hx
  exact ⟨f y, h y hy, (map_smul f c y).symm⟩

/- English proof (translation)
Consider the cases of `s with`. Consider the case `base => exact je_H_ext G v A Lv hLv z hz`. Consider the case `ball`. Take `⟨x, hx, rfl⟩` from `hz`. Use `⟨je_locV G v A x, ?_, rfl⟩` and prove the remaining obligations.

Take `⟨h1, h2⟩` from `hx`. Use `⟨je_scale _ _ _ (je_locV G v A) (fun y hy => je_HL G v A Lv hLv y hy) x h1, ?_⟩` and prove the remaining obligations. Use `(Submodule.mem_iInf _).2 fun e' => (Submodule.mem_iInf _).2 ?_` and prove the remaining obligations. Introduce and unpack `⟨he', hs'⟩`. Establish `he : IsEdge p (G.P.n' v) G.P.r (⟨e'.src.map (nt_phi (G.P.W v) A⁻¹), e'.tgt.map (nt_phi (G.P.W v) A⁻¹)⟩ : Edge (G.P.W v) (G.P.Qq v) (G.P.m + 1))` using `nt_edge_map p _ _ A⁻¹ e'.src e'.tgt he'`.

Establish `hsrc : e'.src.map (nt_phi (G.P.W v) A⁻¹) = Lv` using `by rw [hs']; exact nt_map_inv A Lv`. Establish `hx2` using `(Submodule.mem_iInf _).1 ((Submodule.mem_iInf _).1 h2 _) ⟨he, hsrc⟩`. Unfold `Re at hx2 ⊢`. Establish `h3` using `je_scale _ _ _ (je_locV G v A) (fun y hy => je_HLe G v A _ _ he y hy) x hx2`. Rewrite `h3` using `[nt_map_inv', nt_map_inv']`.

Conclude with `h3`. Consider the case `dual`. Take `⟨x, hx, rfl⟩` from `hz`. Use `⟨je_locV G v A x, ?_, rfl⟩` and prove the remaining obligations. Introduce `φ hφ`.

Take `⟨h1, h2⟩` from `hφ`. Use `hx ((je_locV G v A).dualMap φ) ⟨?_, ?_⟩` and prove the remaining obligations. Use `je_scale _ _ _ (je_locV G v A).dualMap (fun ψ hψ => ?_) φ h1` and prove the remaining obligations. Introduce `y hy`. Conclude with `hψ _ (je_HL G v A Lv hLv y hy)`.

Use `(Submodule.mem_iInf _).2 fun e => (Submodule.mem_iInf _).2 ?_` and prove the remaining obligations. Introduce and unpack `⟨he, ht⟩`. Establish `he' : IsEdge p (G.P.n' v) G.P.r (⟨e.src.map (nt_phi (G.P.W v) A), e.tgt.map (nt_phi (G.P.W v) A)⟩ : Edge (G.P.W v) (G.P.Qq v) (G.P.m + 1))` using `nt_edge_map p _ _ A e.src e.tgt he`. Establish `htg : e.tgt.map (nt_phi (G.P.W v) A) = Lv.map (nt_phi (G.P.W v) A)` using `by rw [ht]`. Establish `hφ2` using `(Submodule.mem_iInf _).1 ((Submodule.mem_iInf _).1 h2 _) ⟨he', htg⟩`.

Unfold `Re' at hφ2 ⊢`. Use `je_scale _ _ _ (je_locV G v A).dualMap (fun ψ hψ => ?_) φ hφ2` and prove the remaining obligations. Introduce `y hy`. Conclude with `hψ _ (je_HLe G v A e.src e.tgt he y hy)`.
-/
theorem mapsTo_je_loc (G : GAtP p) (v : Fin G.P.nV) (tv : ℕ) (s : Slot) (A : GL (Fin (G.P.m + 1)) (G.P.Qq v))
    (Lv : Lat G v) (hLv : IsLattice (G.P.W v) Lv) (z : Pol G v) (hz : z ∈ piLattice₂ G v tv s Lv) :
    je_loc G v A z ∈ piLattice₂ G v tv s (Lv.map (nt_phi (G.P.W v) A)) := by
  cases s with
  | base => exact je_H_ext G v A Lv hLv z hz
  | ball =>
    obtain ⟨x, hx, rfl⟩ := hz
    refine ⟨je_locV G v A x, ?_, rfl⟩
    obtain ⟨h1, h2⟩ := hx
    refine ⟨je_scale _ _ _ (je_locV G v A) (fun y hy => je_HL G v A Lv hLv y hy) x h1, ?_⟩
    refine (Submodule.mem_iInf _).2 fun e' => (Submodule.mem_iInf _).2 ?_
    rintro ⟨he', hs'⟩
    have he : IsEdge p (G.P.n' v) G.P.r (⟨e'.src.map (nt_phi (G.P.W v) A⁻¹), e'.tgt.map (nt_phi (G.P.W v) A⁻¹)⟩ :
        Edge (G.P.W v) (G.P.Qq v) (G.P.m + 1)) := nt_edge_map p _ _ A⁻¹ e'.src e'.tgt he'
    have hsrc : e'.src.map (nt_phi (G.P.W v) A⁻¹) = Lv := by rw [hs']; exact nt_map_inv A Lv
    have hx2 := (Submodule.mem_iInf _).1 ((Submodule.mem_iInf _).1 h2 _) ⟨he, hsrc⟩
    unfold Re at hx2 ⊢
    have h3 := je_scale _ _ _ (je_locV G v A) (fun y hy => je_HLe G v A _ _ he y hy) x hx2
    rw [nt_map_inv', nt_map_inv'] at h3
    exact h3
  | dual =>
    obtain ⟨x, hx, rfl⟩ := hz
    refine ⟨je_locV G v A x, ?_, rfl⟩
    intro φ hφ
    obtain ⟨h1, h2⟩ := hφ
    refine hx ((je_locV G v A).dualMap φ) ⟨?_, ?_⟩
    · refine je_scale _ _ _ (je_locV G v A).dualMap (fun ψ hψ => ?_) φ h1
      intro y hy
      exact hψ _ (je_HL G v A Lv hLv y hy)
    · refine (Submodule.mem_iInf _).2 fun e => (Submodule.mem_iInf _).2 ?_
      rintro ⟨he, ht⟩
      have he' : IsEdge p (G.P.n' v) G.P.r (⟨e.src.map (nt_phi (G.P.W v) A), e.tgt.map (nt_phi (G.P.W v) A)⟩ :
          Edge (G.P.W v) (G.P.Qq v) (G.P.m + 1)) := nt_edge_map p _ _ A e.src e.tgt he
      have htg : e.tgt.map (nt_phi (G.P.W v) A) = Lv.map (nt_phi (G.P.W v) A) := by rw [ht]
      have hφ2 := (Submodule.mem_iInf _).1 ((Submodule.mem_iInf _).1 h2 _) ⟨he', htg⟩
      unfold Re' at hφ2 ⊢
      refine je_scale _ _ _ (je_locV G v A).dualMap (fun ψ hψ => ?_) φ hφ2
      intro y hy
      exact hψ _ (je_HLe G v A e.src e.tgt he y hy)

/- English proof (translation)
Establish `h : (G.P.subst Gm).comp (G.P.vEmb v) = (G.P.vEmb v).comp (blockAct G.Kf (Gm v))`. Apply `MvPolynomial.algHom_ext` to reduce the goal to its premises. Introduce `x`. Simplify using `[Places.subst, Places.vEmb, blockAct, map_sum]`. Conclude with `congrArg (fun f => f F) h`.
-/
theorem je_subst_vEmb (G : GAtP p)
    (Gm : ∀ v, Fin (G.P.n' v) → Matrix (Fin (G.P.m + 1)) (Fin (G.P.m + 1)) G.Kf) (v : Fin G.P.nV) (F : Pol G v) :
    G.P.subst Gm (G.P.vEmb v F) = G.P.vEmb v (blockAct G.Kf (Gm v) F) := by
  have h : (G.P.subst Gm).comp (G.P.vEmb v) = (G.P.vEmb v).comp (blockAct G.Kf (Gm v)) := by
    apply MvPolynomial.algHom_ext
    intro x
    simp [Places.subst, Places.vEmb, blockAct, map_sum]
  exact congrArg (fun f => f F) h

/- English proof (translation)
Use `symm`. Apply `Matrix.inv_eq_left_inv` to reduce the goal to its premises. Establish `h1 : ((A⁻¹ : GL (Fin (G.P.m + 1)) (G.P.Qq v)) : Matrix (Fin (G.P.m + 1)) (Fin (G.P.m + 1)) (G.P.Qq v)) * (A : Matrix (Fin (G.P.m + 1)) (Fin (G.P.m + 1)) (G.P.Qq v)) = 1`. Rewrite using `[← Units.val_mul]`. Simplify using the standard rewrite rules.

Use extensionality with `a b`. Establish `h2 : (G.P.gPos v s ((A⁻¹ : GL (Fin (G.P.m + 1)) (G.P.Qq v)) : Matrix (Fin (G.P.m + 1)) (Fin (G.P.m + 1)) (G.P.Qq v)) * je_g G v A s) a b = G.P.ι v ((G.P.σ v ^ s.val) ((((A⁻¹ : GL (Fin (G.P.m + 1)) (G.P.Qq v)) : Matrix (Fin (G.P.m + 1)) (Fin (G.P.m + 1)) (G.P.Qq v)) * (A : Matrix …`. Simplify using `only [Places.gPos, je_g, Matrix.mul_apply, map_sum, map_mul]`. Rewrite using `[h2, h1]`. Distinguish the cases in `hab : a = b`.

Substitute `hab` using the available equality. Simplify using the standard rewrite rules. Simplify using `[hab]`.
-/
theorem je_gPos_inv (G : GAtP p) (v : Fin G.P.nV) (A : GL (Fin (G.P.m + 1)) (G.P.Qq v)) (s : Fin (G.P.n' v)) :
    G.P.gPos v s ((A⁻¹ : GL (Fin (G.P.m + 1)) (G.P.Qq v)) : Matrix (Fin (G.P.m + 1)) (Fin (G.P.m + 1)) (G.P.Qq v)) =
      (je_g G v A s)⁻¹ := by
  symm
  apply Matrix.inv_eq_left_inv
  have h1 : ((A⁻¹ : GL (Fin (G.P.m + 1)) (G.P.Qq v)) : Matrix (Fin (G.P.m + 1)) (Fin (G.P.m + 1)) (G.P.Qq v)) *
      (A : Matrix (Fin (G.P.m + 1)) (Fin (G.P.m + 1)) (G.P.Qq v)) = 1 := by
    rw [← Units.val_mul]; simp
  ext a b
  have h2 : (G.P.gPos v s ((A⁻¹ : GL (Fin (G.P.m + 1)) (G.P.Qq v)) :
      Matrix (Fin (G.P.m + 1)) (Fin (G.P.m + 1)) (G.P.Qq v)) * je_g G v A s) a b =
      G.P.ι v ((G.P.σ v ^ s.val) ((((A⁻¹ : GL (Fin (G.P.m + 1)) (G.P.Qq v)) :
        Matrix (Fin (G.P.m + 1)) (Fin (G.P.m + 1)) (G.P.Qq v)) *
        (A : Matrix (Fin (G.P.m + 1)) (Fin (G.P.m + 1)) (G.P.Qq v))) a b)) := by
    simp only [Places.gPos, je_g, Matrix.mul_apply, map_sum, map_mul]
  rw [h2, h1]
  by_cases hab : a = b
  · subst hab; simp
  · simp [hab]

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem je_loc_apply (G : GAtP p) (v : Fin G.P.nV) (A : GL (Fin (G.P.m + 1)) (G.P.Qq v)) (z : Pol G v) :
    je_loc G v A z = (∏ s, (je_g G v A s).det ^ (-(lamAt (G.P.lam0 v) s (Fin.last G.P.m)))) •
      blockAct G.Kf (fun s => (je_g G v A s)⁻¹) z := rfl

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem je_natAct_apply (G : GAtP p) (A : ∀ v, GL (Fin (G.P.m + 1)) (G.P.Qq v)) (x : G.P.Xsp) :
    G.P.natAct A x = (∏ v, ∏ s, (je_g G v (A v) s).det ^ (-(lamAt (G.P.lam0 v) s (Fin.last G.P.m)))) •
      G.P.subst (fun v s => G.P.gPos v s ((A v)⁻¹ : GL (Fin (G.P.m + 1)) (G.P.Qq v))) x := rfl

/- English proof (translation)
Establish `step1 : G.P.subst (fun v s => G.P.gPos v s ((A v)⁻¹ : GL (Fin (G.P.m + 1)) (G.P.Qq v))) (∏ v, G.P.vEmb v (F v)) = ∏ v, G.P.vEmb v (blockAct G.Kf (fun s => (je_g G v (A v) s)⁻¹) (F v))`. Rewrite using `[map_prod]`. Apply `Finset.prod_congr rfl` to reduce the goal to its premises. Introduce `v _`. Rewrite using `[je_subst_vEmb]`.

Establish `e : (fun s => G.P.gPos v s ((A v)⁻¹ : GL (Fin (G.P.m + 1)) (G.P.Qq v))) = fun s => (je_g G v (A v) s)⁻¹` using `funext fun s => je_gPos_inv G v (A v) s`. Rewrite using `[e]`. Rewrite using `[je_natAct_apply, step1, je_prod_smul]`. Apply `Finset.prod_congr rfl` to reduce the goal to its premises. Introduce `v _`.

Rewrite using `[je_loc_apply, map_smul]`.
-/
theorem je_natAct_prod (G : GAtP p) (A : ∀ v, GL (Fin (G.P.m + 1)) (G.P.Qq v)) (F : ∀ v, Pol G v) :
    G.P.natAct A (∏ v, G.P.vEmb v (F v)) = ∏ v, G.P.vEmb v (je_loc G v (A v) (F v)) := by
  have step1 : G.P.subst (fun v s => G.P.gPos v s ((A v)⁻¹ : GL (Fin (G.P.m + 1)) (G.P.Qq v)))
      (∏ v, G.P.vEmb v (F v)) =
      ∏ v, G.P.vEmb v (blockAct G.Kf (fun s => (je_g G v (A v) s)⁻¹) (F v)) := by
    rw [map_prod]
    apply Finset.prod_congr rfl
    intro v _
    rw [je_subst_vEmb]
    have e : (fun s => G.P.gPos v s ((A v)⁻¹ : GL (Fin (G.P.m + 1)) (G.P.Qq v))) =
        fun s => (je_g G v (A v) s)⁻¹ := funext fun s => je_gPos_inv G v (A v) s
    rw [e]
  rw [je_natAct_apply, step1, je_prod_smul]
  apply Finset.prod_congr rfl
  intro v _
  rw [je_loc_apply, map_smul]

/- English proof (translation)
Introduce `t σ i γ L hL ξ hξ`. Unfold `sysOf Places.sys Places.tenV at hξ ⊢`. Proceed by induction on `hξ using Submodule.span_induction with`. Consider the case `mem x hx`. Take `⟨F, hF, rfl⟩` from `hx`.

Apply `Submodule.smul_mem` to reduce the goal to its premises. Apply `Submodule.subset_span` to reduce the goal to its premises. Conclude with `⟨fun v => je_loc G v ((G.lev i).act v γ) (F v), fun v => mapsTo_je_loc G v (t v) (σ v) _ (L v) (hL v) (F v) (hF v), je_natAct_prod G _ F⟩`. Consider the case `zero => rw [map_zero, smul_zero]`. Conclude with `Submodule.zero_mem _`.

Consider the case `add x y _ _ hx hy => rw [map_add, smul_add]`. Conclude with `Submodule.add_mem _ hx hy`. Consider the case `smul a x _ hx => rw [LinearMap.map_smul_of_tower, smul_comm]`. Conclude with `Submodule.smul_mem _ a hx`.
-/
theorem jEquiv (G : GAtP p) : JEquiv G := by
  intro t σ i γ L hL ξ hξ
  unfold sysOf Places.sys Places.tenV at hξ ⊢
  induction hξ using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨F, hF, rfl⟩ := hx
    apply Submodule.smul_mem
    apply Submodule.subset_span
    exact ⟨fun v => je_loc G v ((G.lev i).act v γ) (F v),
      fun v => mapsTo_je_loc G v (t v) (σ v) _ (L v) (hL v) (F v) (hF v), je_natAct_prod G _ F⟩
  | zero => rw [map_zero, smul_zero]; exact Submodule.zero_mem _
  | add x y _ _ hx hy => rw [map_add, smul_add]; exact Submodule.add_mem _ hx hy
  | smul a x _ hx => rw [LinearMap.map_smul_of_tower, smul_comm]; exact Submodule.smul_mem _ a hx

end Formalism.MainNotions.G.LatticeSystems

namespace Formalism.MainNotions.G.LatticeSystems

open Formalism.MainNotions.G Formalism.MainNotions.SelectionLemmas Formalism.G0

variable {p : ℕ}

/- English proof (translation)
Establish `key : ∀ i : G.comp, F i ∈ (G.lev i).funMod Hv ↔ ((∀ L, G.P.IsLatTup L → F i L ∈ Hv L) ∧ (∀ L, ¬ G.P.IsLatTup L → F i L = 0) ∧ ∀ (γ : (G.lev i).Γ) (L : G.P.Tup), F i ((G.lev i).smul γ L) = ((G.lev i).χ γ : G.O) • (G.lev i).actX γ (F i L))`. Introduce `i`. Unfold `Level.funMod`. Simplify using `only [Submodule.mem_inf, Submodule.mem_iInf, Submodule.mem_comap, LinearMap.mem_ker, LinearMap.proj_apply, LinearMap.sub_apply, LinearMap.comp_apply, LinearMap.smul_apply, LinearMap.restrictScalars_apply, sub_eq_zero]`. Conclude with `and_assoc`.

Unfold `GAtP.funMod`. Rewrite using `[Submodule.mem_pi]`. Prove the components needed by the constructor for the conclusion. Introduce `h i`. Conclude with `(key i).1 (h i (Set.mem_univ i))`.

Introduce `h i _`. Conclude with `(key i).2 (h i)`.
-/
theorem js_mem (G : GAtP p) (Hv : G.P.Tup → Submodule G.O G.P.Xsp) (F : G.Fn) :
    F ∈ G.funMod Hv ↔ ∀ i : G.comp, (∀ L, G.P.IsLatTup L → F i L ∈ Hv L) ∧
      (∀ L, ¬ G.P.IsLatTup L → F i L = 0) ∧
      ∀ (γ : (G.lev i).Γ) (L : G.P.Tup),
        F i ((G.lev i).smul γ L) = ((G.lev i).χ γ : G.O) • (G.lev i).actX γ (F i L) := by
  have key : ∀ i : G.comp, F i ∈ (G.lev i).funMod Hv ↔ ((∀ L, G.P.IsLatTup L → F i L ∈ Hv L) ∧
      (∀ L, ¬ G.P.IsLatTup L → F i L = 0) ∧
      ∀ (γ : (G.lev i).Γ) (L : G.P.Tup),
        F i ((G.lev i).smul γ L) = ((G.lev i).χ γ : G.O) • (G.lev i).actX γ (F i L)) := by
    intro i
    unfold Level.funMod
    simp only [Submodule.mem_inf, Submodule.mem_iInf, Submodule.mem_comap, LinearMap.mem_ker,
      LinearMap.proj_apply, LinearMap.sub_apply, LinearMap.comp_apply, LinearMap.smul_apply,
      LinearMap.restrictScalars_apply, sub_eq_zero]
    exact and_assoc
  unfold GAtP.funMod
  rw [Submodule.mem_pi]
  constructor
  · intro h i
    exact (key i).1 (h i (Set.mem_univ i))
  · intro h i _
    exact (key i).2 (h i)

/- English proof (translation)
Establish `hp : (p : G.Kf) ≠ 0`. Use `kp_p_ne_zero G v0` as an intermediate fact. Rewrite `this` using `[map_natCast]`. Then use the resulting hypothesis. Establish `hq : ∀ x : G.P.Xsp, (p : G.O) ^ E • ((((p : G.Kf) ^ E)⁻¹) • x) = x`. Introduce `x`.

Rewrite using `[← algebraMap_smul G.Kf ((p : G.O) ^ E) ((((p : G.Kf) ^ E)⁻¹) • x), smul_smul, map_pow, map_natCast, mul_inv_cancel₀ (pow_ne_zero _ hp), one_smul]`. Establish `hq' : ∀ x : G.P.Xsp, (((p : G.Kf) ^ E)⁻¹) • ((p : G.O) ^ E • x) = x`. Introduce `x`. Rewrite using `[smul_comm, hq]`. Use `⟨fun i L => (((p : G.Kf) ^ E)⁻¹) • W i L, ?_, ?_⟩` and prove the remaining obligations.

Rewrite using `[SetLike.mem_coe, js_mem]`. Introduce `i`. Take `⟨_, b, c⟩` from `(js_mem G T W).1 hW i`. Use `⟨fun L hL => ?_, fun L hL => ?_, fun γ L => ?_⟩` and prove the remaining obligations. Take `⟨z, hz, hzW⟩` from `hpt i L hL`.

Establish `hzW' : (p : G.O) ^ E • z = W i L` using `hzW`. Use `show (((p : G.Kf) ^ E)⁻¹) • W i L ∈ T L`. Rewrite using `[← hzW', hq']`. Conclude with `hz`. Use `show (((p : G.Kf) ^ E)⁻¹) • W i L = 0`.

Rewrite using `[b L hL, smul_zero]`. Use `show (((p : G.Kf) ^ E)⁻¹) • W i ((G.lev i).smul γ L) = ((G.lev i).χ γ : G.O) • (G.lev i).actX γ ((((p : G.Kf) ^ E)⁻¹) • W i L)`. Rewrite using `[c γ L, map_smul, smul_comm]`. Use function extensionality and compare the values at `i L`. Conclude with `hq (W i L)`.
-/
theorem js_div (G : GAtP p) (v0 : Fin G.P.nV) (T : G.P.Tup → Submodule G.O G.P.Xsp) (E : ℕ) (W : G.Fn)
    (hW : W ∈ G.funMod T)
    (hpt : ∀ i L, G.P.IsLatTup L → W i L ∈ sc G ((p : G.O) ^ E) (T L)) :
    W ∈ sc G ((p : G.O) ^ E) (G.funMod T) := by
  have hp : (p : G.Kf) ≠ 0 := by
    have := kp_p_ne_zero G v0
    rwa [map_natCast] at this
  have hq : ∀ x : G.P.Xsp, (p : G.O) ^ E • ((((p : G.Kf) ^ E)⁻¹) • x) = x := by
    intro x
    rw [← algebraMap_smul G.Kf ((p : G.O) ^ E) ((((p : G.Kf) ^ E)⁻¹) • x), smul_smul, map_pow, map_natCast,
      mul_inv_cancel₀ (pow_ne_zero _ hp), one_smul]
  have hq' : ∀ x : G.P.Xsp, (((p : G.Kf) ^ E)⁻¹) • ((p : G.O) ^ E • x) = x := by
    intro x
    rw [smul_comm, hq]
  refine ⟨fun i L => (((p : G.Kf) ^ E)⁻¹) • W i L, ?_, ?_⟩
  · rw [SetLike.mem_coe, js_mem]
    intro i
    obtain ⟨_, b, c⟩ := (js_mem G T W).1 hW i
    refine ⟨fun L hL => ?_, fun L hL => ?_, fun γ L => ?_⟩
    · obtain ⟨z, hz, hzW⟩ := hpt i L hL
      have hzW' : (p : G.O) ^ E • z = W i L := hzW
      show (((p : G.Kf) ^ E)⁻¹) • W i L ∈ T L
      rw [← hzW', hq']
      exact hz
    · show (((p : G.Kf) ^ E)⁻¹) • W i L = 0
      rw [b L hL, smul_zero]
    · show (((p : G.Kf) ^ E)⁻¹) • W i ((G.lev i).smul γ L) =
        ((G.lev i).χ γ : G.O) • (G.lev i).actX γ ((((p : G.Kf) ^ E)⁻¹) • W i L)
      rw [c γ L, map_smul, smul_comm]
  · funext i L
    exact hq (W i L)

/- English proof (translation)
Use function extensionality and compare the values at `u`. Use `show (L u).map (nt_phi (G.P.W u) ((G.lev i).act u (a * b))) = ((L u).map (nt_phi (G.P.W u) ((G.lev i).act u b))).map (nt_phi (G.P.W u) ((G.lev i).act u a))`. Rewrite using `[← Submodule.map_comp]`. Use `congr 1`. Apply `LinearMap.ext` to reduce the goal to its premises.

Introduce `x`. Simplify using `[nt_phi, map_mul, Matrix.mulVec_mulVec]`.
-/
theorem js_smul_mul (G : GAtP p) (i : G.comp) (a b : (G.lev i).Γ) (L : G.P.Tup) :
    (G.lev i).smul (a * b) L = (G.lev i).smul a ((G.lev i).smul b L) := by
  funext u
  show (L u).map (nt_phi (G.P.W u) ((G.lev i).act u (a * b))) =
    ((L u).map (nt_phi (G.P.W u) ((G.lev i).act u b))).map (nt_phi (G.P.W u) ((G.lev i).act u a))
  rw [← Submodule.map_comp]
  congr 1
  apply LinearMap.ext
  intro x
  simp [nt_phi, map_mul, Matrix.mulVec_mulVec]

/- English proof (translation)
Use function extensionality and compare the values at `u`. Use `show (L u).map (nt_phi (G.P.W u) ((G.lev i).act u 1)) = L u`. Establish `: nt_phi (G.P.W u) ((G.lev i).act u 1) = LinearMap.id`. Apply `LinearMap.ext` to reduce the goal to its premises. Introduce `x`.

Simplify using `[nt_phi]`. Rewrite using `[this, Submodule.map_id]`.
-/
theorem js_smul_one (G : GAtP p) (i : G.comp) (L : G.P.Tup) : (G.lev i).smul 1 L = L := by
  funext u
  show (L u).map (nt_phi (G.P.W u) ((G.lev i).act u 1)) = L u
  have : nt_phi (G.P.W u) ((G.lev i).act u 1) = LinearMap.id := by
    apply LinearMap.ext
    intro x
    simp [nt_phi]
  rw [this, Submodule.map_id]

/- English proof (translation)
Establish `h2 : (G.lev i).smul (b⁻¹ * a) L = L`. Rewrite using `[js_smul_mul, h, ← js_smul_mul, inv_mul_cancel, js_smul_one]`. Use `h1 i _ L hL h2` as an intermediate fact. Conclude with `(inv_mul_eq_one.1 this).symm`.
-/
theorem js_free (G : GAtP p) (h1 : G.TrivStab) (i : G.comp) (a b : (G.lev i).Γ) (L : G.P.Tup)
    (hL : G.P.IsLatTup L) (h : (G.lev i).smul a L = (G.lev i).smul b L) : a = b := by
  have h2 : (G.lev i).smul (b⁻¹ * a) L = L := by
    rw [js_smul_mul, h, ← js_smul_mul, inv_mul_cancel, js_smul_one]
  have := h1 i _ L hL h2
  exact (inv_mul_eq_one.1 this).symm

/- English proof (translation)
The claim follows from `Function.update_self v A L`.
-/
theorem js_upd_self (G : GAtP p) (L : G.P.Tup) (v : Fin G.P.nV) (A : Lat G v) : upd G L v A v = A :=
  Function.update_self v A L

/- English proof (translation)
The claim follows from `Function.update_of_ne hu A L`.
-/
theorem js_upd_ne (G : GAtP p) (L : G.P.Tup) (v : Fin G.P.nV) (A : Lat G v) (u : Fin G.P.nV) (hu : u ≠ v) :
    upd G L v A u = L u :=
  Function.update_of_ne hu A L

/- English proof (translation)
The claim follows from `Function.update_eq_self v L`.
-/
theorem js_upd_eq (G : GAtP p) (L : G.P.Tup) (v : Fin G.P.nV) : upd G L v (L v) = L :=
  Function.update_eq_self v L

/- English proof (translation)
The claim follows from `nt_smul_update G i γ v L A`.
-/
theorem js_smul_upd (G : GAtP p) (i : G.comp) (γ : (G.lev i).Γ) (v : Fin G.P.nV) (L : G.P.Tup) (A : Lat G v) :
    (G.lev i).smul γ (upd G L v A) =
      upd G ((G.lev i).smul γ L) v (A.map (nt_phi (G.P.W v) ((G.lev i).act v γ))) :=
  nt_smul_update G i γ v L A

/- English proof (translation)
Introduce `u`. Distinguish the cases in `huv : u = v`. Substitute `huv` using the available equality. Rewrite using `[js_upd_self]`. Conclude with `hA`.

Rewrite using `[js_upd_ne G L v A u huv]`. Conclude with `hL u`.
-/
theorem js_upd_lat (G : GAtP p) (L : G.P.Tup) (hL : G.P.IsLatTup L) (v : Fin G.P.nV) (A : Lat G v)
    (hA : IsLattice (G.P.W v) A) : G.P.IsLatTup (upd G L v A) := by
  intro u
  by_cases huv : u = v
  · subst huv
    rw [js_upd_self]
    exact hA
  · rw [js_upd_ne G L v A u huv]
    exact hL u

/- English proof (translation)
Establish `hs : vertexLabel B v = Slot.dual` using `by simp [vertexLabel, hv]`. Use `nt_tenV_smulK G v _ _ _ ?_ ?_ _ h` and prove the remaining obligations. Introduce `z hz`. Establish `hz2 : z ∈ piLattice₂ G v (t v) (Function.update (vertexLabel B) v Slot.ball v) (upd G L v L'' v)` using `hz`. Rewrite `hz2` using `[Function.update_self, js_upd_self]`.

Use `show _ ∈ piLattice₂ G v (t v) (vertexLabel B v) (L v)`. Rewrite using `[hs]`. Conclude with `nt_local G v (t v) ⟨L'', L v⟩ hE z hz2`. Introduce `u hu show piLattice₂ G u (t u) (Function.update (vertexLabel B) v Slot.ball u) (upd G L v L'' u) ≤ piLattice₂ G u (t u) (vertexLabel B u) (L u)`. Rewrite using `[Function.update_of_ne hu, js_upd_ne G L v L'' u hu]`.
-/
theorem js_val (G : GAtP p) (t : Fin G.P.nV → ℕ) (B : Finset (Fin G.P.nV)) (v : Fin G.P.nV) (hv : v ∈ B)
    (L : G.P.Tup) (L'' : Lat G v) (hE : IsEdge p (G.P.n' v) G.P.r ⟨L'', L v⟩) (ξ : G.P.Xsp)
    (h : ξ ∈ sysOf G t (Function.update (vertexLabel B) v Slot.ball) (upd G L v L'')) :
    ((p : G.Kf) ^ G.P.ArV v) • ξ ∈ sysOf G t (vertexLabel B) L := by
  have hs : vertexLabel B v = Slot.dual := by simp [vertexLabel, hv]
  refine nt_tenV_smulK G v _ _ _ ?_ ?_ _ h
  · intro z hz
    have hz2 : z ∈ piLattice₂ G v (t v) (Function.update (vertexLabel B) v Slot.ball v) (upd G L v L'' v) := hz
    rw [Function.update_self, js_upd_self] at hz2
    show _ ∈ piLattice₂ G v (t v) (vertexLabel B v) (L v)
    rw [hs]
    exact nt_local G v (t v) ⟨L'', L v⟩ hE z hz2
  · intro u hu
    show piLattice₂ G u (t u) (Function.update (vertexLabel B) v Slot.ball u) (upd G L v L'' u) ≤
      piLattice₂ G u (t u) (vertexLabel B u) (L u)
    rw [Function.update_of_ne hu, js_upd_ne G L v L'' u hu]

/- English proof (translation)
Take `⟨_, _, dMem, dApp, _, dZero, _, _⟩` from `hD`. Introduce `v hv i L hL L'' hedge ξ hξ h2`. Establish `hs : vertexLabel B v = Slot.dual` using `by simp [vertexLabel, hv]`. Establish `hposition : Function.update (vertexLabel B) v Slot.dual = vertexLabel B`. Rewrite using `[← hs]`.

Conclude with `Function.update_eq_self v _`. Establish `hlatx : G.P.IsLatTup (upd G L v L'')` using `js_upd_lat G L hL v L'' hedge.1`. Establish `hF : delta G i (upd G L v L'') ξ ∈ latSys G t (Function.update (vertexLabel B) v Slot.ball)` using `dMem _ (hE t _) i _ hlatx ξ hξ`. Establish `hyJ : G.yv v (delta G i (upd G L v L'') ξ) ∈ JBof G t B` using `Submodule.mem_iSup_of_mem v (Submodule.mem_iSup_of_mem hv (Submodule.subset_span ⟨_, hF, rfl⟩))`. Establish `hyM : G.yv v (delta G i (upd G L v L'') ξ) ∈ MBof G t B`.

Use `restNat_proved G B t (vertexLabel B) v hv _ hF` as an intermediate fact. Rewrite `this` using `[hposition]`. Then use the resulting hypothesis. Establish `hdM : delta G i L (((p : G.Kf) ^ G.P.ArV v) • ξ) ∈ MBof G t B` using `dMem _ (hE t _) i L hL _ (js_val G t B v hv L L'' hedge ξ hξ)`. Establish `hpt : ∀ i' L1, G.P.IsLatTup L1 → (delta G i L (((p : G.Kf) ^ G.P.ArV v) • ξ) - G.yv v (delta G i (upd G L v L'') ξ)) i' L1 ∈ sc G ((p : G.O) ^ E) (sysOf G t (vertexLabel B) L1)`. Introduce `i' L1 hL1`.

Establish `hy : G.yv v (delta G i (upd G L v L'') ξ) i' L1 = ((p : G.Kf) ^ G.P.ArV v) • ∑ A ∈ ef_E G.P v (L1 v), delta G i (upd G L v L'') ξ i' (upd G L1 v A)` using `ef_yv_eq G.P v (delta G i (upd G L v L'') ξ i') L1`. Use `show delta G i L (((p : G.Kf) ^ G.P.ArV v) • ξ) i' L1 - G.yv v (delta G i (upd G L v L'') ξ) i' L1 ∈ _`. Rewrite using `[hy]`. Distinguish the cases in `hi : i' = i`. Substitute `hi` using the available equality.

Establish `key : ∀ A ∈ ef_E G.P v (L1 v), (∀ γ : (G.lev i').Γ, L1 = (G.lev i').smul γ L → A ≠ L''.map (nt_phi (G.P.W v) ((G.lev i').act v γ))) → ((p : G.Kf) ^ G.P.ArV v) • delta G i' (upd G L v L'') ξ i' (upd G L1 v A) ∈ sc G ((p : G.O) ^ E) (sysOf G t (vertexLabel B) L1)`. Introduce `A hA hne`. Establish `hEA : IsEdge p (G.P.n' v) G.P.r ⟨A, L1 v⟩` using `(Set.Finite.mem_toFinset (ef_places_finite G.P v (L1 v))).1 hA`. Distinguish the cases in `hγ : ∃ γ : (G.lev i').Γ, upd G L1 v A = (G.lev i').smul γ (upd G L v L'')`. Take `⟨γ, hγ⟩` from `hγ`.

Establish `hx` using `hγ.trans (js_smul_upd G i' γ v L L'')`. Establish `hAeq : A = L''.map (nt_phi (G.P.W v) ((G.lev i').act v γ))`. Use `congrFun hx v` as an intermediate fact. Rewrite `this` using `[js_upd_self, js_upd_self]`. Then use the resulting hypothesis. Establish `hother : ∀ u, u ≠ v → L1 u = (G.lev i').smul γ L u`.

Introduce `u hu`. Use `congrFun hx u` as an intermediate fact. Rewrite `this` using `[js_upd_ne _ _ _ _ u hu, js_upd_ne _ _ _ _ u hu]`. Then use the resulting hypothesis. Establish `hE' : IsEdge p (G.P.n' v) G.P.r ⟨L'', (L1 v).map (nt_phi (G.P.W v) ((G.lev i').act v γ)⁻¹)⟩`. Use `nt_edge_map p (G.P.n' v) G.P.r ((G.lev i').act v γ)⁻¹ A (L1 v) hEA` as an intermediate fact.

Rewrite `this` using `[hAeq, nt_map_inv]`. Conclude with `this`. Establish `hL1' : (G.lev i').smul γ (upd G L v ((L1 v).map (nt_phi (G.P.W v) ((G.lev i').act v γ)⁻¹))) = L1`. Rewrite using `[js_smul_upd, nt_map_inv']`. Use function extensionality and compare the values at `u`.

Distinguish the cases in `huv : u = v`. Substitute `huv` using the available equality. Conclude with `js_upd_self _ _ _ _`. Rewrite using `[js_upd_ne _ _ _ _ u huv]`. Conclude with `(hother u huv).symm`.

Distinguish the cases in `hL' : (L1 v).map (nt_phi (G.P.W v) ((G.lev i').act v γ)⁻¹) = L v`. It suffices to derive a contradiction. Apply `hne γ _ hAeq` to reduce the goal to its premises. Rewrite `hL1'` using `[hL', js_upd_eq]`. Conclude with `hL1'.symm`.

Take `⟨η, hη, hηe⟩` from `h2 _ hE' hL'`. Establish `hηe' : (p : G.O) ^ E • η = ((p : G.Kf) ^ G.P.ArV v) • ξ` using `hηe`. Establish `h3` using `hE t (vertexLabel B) i' γ _ (js_upd_lat G L hL v _ hE'.2.1) η hη`. Rewrite `h3` using `[hL1']`. Use `⟨_, h3, ?_⟩` and prove the remaining obligations.

Use `show (p : G.O) ^ E • (((G.lev i').χ γ : G.O) • (G.lev i').actX γ η) = _`. Rewrite using `[hγ, dApp i' _ γ ξ hlatx]`. Establish `e3 : (G.lev i').actX γ (((p : G.Kf) ^ G.P.ArV v) • ξ) = ((p : G.Kf) ^ G.P.ArV v) • (G.lev i').actX γ ξ` using `map_smul _ _ _`. Establish `e4 : (G.lev i').actX γ ((p : G.O) ^ E • η) = (p : G.O) ^ E • (G.lev i').actX γ η` using `LinearMap.map_smul_of_tower _ _ _`. Combine the equalities or inequalities in the displayed calculation.

Rewrite using `[← e4, hηe']`. Use `_ = ((G.lev i').χ γ : G.O) • (((p : G.Kf) ^ G.P.ArV v) • (G.lev i').actX γ ξ) := by rw [e3]`. Use `_ = ((p : G.Kf) ^ G.P.ArV v) • (((G.lev i').χ γ : G.O) • (G.lev i').actX γ ξ) := smul_comm _ _ _`. Rewrite using `[dZero i' _ ξ i' _ (Or.inr hγ), smul_zero]`. Conclude with `Submodule.zero_mem _`.

Distinguish the cases in `horb : ∃ γ0 : (G.lev i').Γ, L1 = (G.lev i').smul γ0 L`. Take `⟨γ0, h0⟩` from `horb`. Establish `hA0 : L''.map (nt_phi (G.P.W v) ((G.lev i').act v γ0)) ∈ ef_E G.P v (L1 v)`. Use `(Set.Finite.mem_toFinset (ef_places_finite G.P v (L1 v))).2 ?_` and prove the remaining obligations. Use `nt_edge_map p (G.P.n' v) G.P.r ((G.lev i').act v γ0) L'' (L v) hedge` as an intermediate fact.

Rewrite using `[h0]`. Conclude with `this`. Establish `e1 : delta G i' L (((p : G.Kf) ^ G.P.ArV v) • ξ) i' L1 = ((p : G.Kf) ^ G.P.ArV v) • delta G i' (upd G L v L'') ξ i' (upd G L1 v (L''.map (nt_phi (G.P.W v) ((G.lev i').act v γ0))))`. Establish `e2 : upd G L1 v (L''.map (nt_phi (G.P.W v) ((G.lev i').act v γ0))) = (G.lev i').smul γ0 (upd G L v L'')`. Rewrite using `[js_smul_upd, h0]`.

Rewrite using `[e2, dApp i' _ γ0 ξ hlatx, h0, dApp i' L γ0 _ hL, map_smul, smul_comm]`. Rewrite using `[← Finset.add_sum_erase _ _ hA0, smul_add, ← sub_sub, e1, sub_self, zero_sub, Finset.smul_sum]`. Use `Submodule.neg_mem _ (Submodule.sum_mem _ fun A hA => ?_)` and prove the remaining obligations. Use `key A (Finset.mem_of_mem_erase hA) fun γ hγ hAeq => ?_` and prove the remaining obligations. Establish `hγ0 : γ = γ0` using `js_free G h1 i' γ γ0 L hL (hγ.symm.trans h0)`.

Rewrite `hAeq` using `[hγ0]`. Conclude with `(Finset.ne_of_mem_erase hA) hAeq`. Rewrite using `[dZero i' L _ i' L1 (Or.inr horb), zero_sub, Finset.smul_sum]`. Conclude with `Submodule.neg_mem _ (Submodule.sum_mem _ fun A hA => key A hA fun γ hγ => absurd ⟨γ, hγ⟩ horb)`. Rewrite using `[dZero i L _ i' L1 (Or.inl hi), zero_sub, Finset.smul_sum]`.

Use `Submodule.neg_mem _ (Submodule.sum_mem _ fun A _ => ?_)` and prove the remaining obligations. Rewrite using `[dZero i _ ξ i' _ (Or.inl hi), smul_zero]`. Conclude with `Submodule.zero_mem _`. Establish `hW` using `js_div G v (sysOf G t (vertexLabel B)) E _ (Submodule.sub_mem _ hdM hyM) hpt`. Establish `hsplit : delta G i L (((p : G.Kf) ^ G.P.ArV v) • ξ) = G.yv v (delta G i (upd G L v L'') ξ) + (delta G i L (((p : G.Kf) ^ G.P.ArV v) • ξ) - G.yv v (delta G i (upd G L v L'') ξ))`.

Normalize the expressions using the abelian group laws. Rewrite using `[hsplit]`. Conclude with `Submodule.add_mem_sup hyJ hW`.
-/
theorem jStep1 (G : GAtP p) (h1 : G.TrivStab) (hE : JEquiv G) (hD : JDelta G)
    (t : Fin G.P.nV → ℕ) (B : Finset (Fin G.P.nV)) (E : ℕ) : JStep1 G t B E := by
  classical
  obtain ⟨_, _, dMem, dApp, _, dZero, _, _⟩ := hD
  intro v hv i L hL L'' hedge ξ hξ h2
  have hs : vertexLabel B v = Slot.dual := by simp [vertexLabel, hv]
  have hposition : Function.update (vertexLabel B) v Slot.dual = vertexLabel B := by
    rw [← hs]; exact Function.update_eq_self v _
  have hlatx : G.P.IsLatTup (upd G L v L'') := js_upd_lat G L hL v L'' hedge.1
  have hF : delta G i (upd G L v L'') ξ ∈ latSys G t (Function.update (vertexLabel B) v Slot.ball) :=
    dMem _ (hE t _) i _ hlatx ξ hξ
  have hyJ : G.yv v (delta G i (upd G L v L'') ξ) ∈ JBof G t B :=
    Submodule.mem_iSup_of_mem v (Submodule.mem_iSup_of_mem hv (Submodule.subset_span ⟨_, hF, rfl⟩))
  have hyM : G.yv v (delta G i (upd G L v L'') ξ) ∈ MBof G t B := by
    have := restNat_proved G B t (vertexLabel B) v hv _ hF
    rwa [hposition] at this
  have hdM : delta G i L (((p : G.Kf) ^ G.P.ArV v) • ξ) ∈ MBof G t B :=
    dMem _ (hE t _) i L hL _ (js_val G t B v hv L L'' hedge ξ hξ)
  have hpt : ∀ i' L1, G.P.IsLatTup L1 →
      (delta G i L (((p : G.Kf) ^ G.P.ArV v) • ξ) - G.yv v (delta G i (upd G L v L'') ξ)) i' L1 ∈
        sc G ((p : G.O) ^ E) (sysOf G t (vertexLabel B) L1) := by
    intro i' L1 hL1
    have hy : G.yv v (delta G i (upd G L v L'') ξ) i' L1 = ((p : G.Kf) ^ G.P.ArV v) •
        ∑ A ∈ ef_E G.P v (L1 v), delta G i (upd G L v L'') ξ i' (upd G L1 v A) :=
      ef_yv_eq G.P v (delta G i (upd G L v L'') ξ i') L1
    show delta G i L (((p : G.Kf) ^ G.P.ArV v) • ξ) i' L1 -
      G.yv v (delta G i (upd G L v L'') ξ) i' L1 ∈ _
    rw [hy]
    by_cases hi : i' = i
    · subst hi
      have key : ∀ A ∈ ef_E G.P v (L1 v),
          (∀ γ : (G.lev i').Γ, L1 = (G.lev i').smul γ L →
            A ≠ L''.map (nt_phi (G.P.W v) ((G.lev i').act v γ))) →
          ((p : G.Kf) ^ G.P.ArV v) • delta G i' (upd G L v L'') ξ i' (upd G L1 v A) ∈
            sc G ((p : G.O) ^ E) (sysOf G t (vertexLabel B) L1) := by
        intro A hA hne
        have hEA : IsEdge p (G.P.n' v) G.P.r ⟨A, L1 v⟩ :=
          (Set.Finite.mem_toFinset (ef_places_finite G.P v (L1 v))).1 hA
        by_cases hγ : ∃ γ : (G.lev i').Γ, upd G L1 v A = (G.lev i').smul γ (upd G L v L'')
        · obtain ⟨γ, hγ⟩ := hγ
          have hx := hγ.trans (js_smul_upd G i' γ v L L'')
          have hAeq : A = L''.map (nt_phi (G.P.W v) ((G.lev i').act v γ)) := by
            have := congrFun hx v
            rwa [js_upd_self, js_upd_self] at this
          have hother : ∀ u, u ≠ v → L1 u = (G.lev i').smul γ L u := by
            intro u hu
            have := congrFun hx u
            rwa [js_upd_ne _ _ _ _ u hu, js_upd_ne _ _ _ _ u hu] at this
          have hE' : IsEdge p (G.P.n' v) G.P.r
              ⟨L'', (L1 v).map (nt_phi (G.P.W v) ((G.lev i').act v γ)⁻¹)⟩ := by
            have := nt_edge_map p (G.P.n' v) G.P.r ((G.lev i').act v γ)⁻¹ A (L1 v) hEA
            rw [hAeq, nt_map_inv] at this
            exact this
          have hL1' : (G.lev i').smul γ
              (upd G L v ((L1 v).map (nt_phi (G.P.W v) ((G.lev i').act v γ)⁻¹))) = L1 := by
            rw [js_smul_upd, nt_map_inv']
            funext u
            by_cases huv : u = v
            · subst huv
              exact js_upd_self _ _ _ _
            · rw [js_upd_ne _ _ _ _ u huv]
              exact (hother u huv).symm
          by_cases hL' : (L1 v).map (nt_phi (G.P.W v) ((G.lev i').act v γ)⁻¹) = L v
          · exfalso
            apply hne γ _ hAeq
            rw [hL', js_upd_eq] at hL1'
            exact hL1'.symm
          · obtain ⟨η, hη, hηe⟩ := h2 _ hE' hL'
            have hηe' : (p : G.O) ^ E • η = ((p : G.Kf) ^ G.P.ArV v) • ξ := hηe
            have h3 := hE t (vertexLabel B) i' γ _ (js_upd_lat G L hL v _ hE'.2.1) η hη
            rw [hL1'] at h3
            refine ⟨_, h3, ?_⟩
            show (p : G.O) ^ E • (((G.lev i').χ γ : G.O) • (G.lev i').actX γ η) = _
            rw [hγ, dApp i' _ γ ξ hlatx]
            have e3 : (G.lev i').actX γ (((p : G.Kf) ^ G.P.ArV v) • ξ) =
                ((p : G.Kf) ^ G.P.ArV v) • (G.lev i').actX γ ξ := map_smul _ _ _
            have e4 : (G.lev i').actX γ ((p : G.O) ^ E • η) = (p : G.O) ^ E • (G.lev i').actX γ η :=
              LinearMap.map_smul_of_tower _ _ _
            calc (p : G.O) ^ E • (((G.lev i').χ γ : G.O) • (G.lev i').actX γ η)
                = ((G.lev i').χ γ : G.O) • ((p : G.O) ^ E • (G.lev i').actX γ η) := smul_comm _ _ _
              _ = ((G.lev i').χ γ : G.O) • (G.lev i').actX γ (((p : G.Kf) ^ G.P.ArV v) • ξ) := by
                  rw [← e4, hηe']
              _ = ((G.lev i').χ γ : G.O) • (((p : G.Kf) ^ G.P.ArV v) • (G.lev i').actX γ ξ) := by rw [e3]
              _ = ((p : G.Kf) ^ G.P.ArV v) • (((G.lev i').χ γ : G.O) • (G.lev i').actX γ ξ) :=
                  smul_comm _ _ _
        · rw [dZero i' _ ξ i' _ (Or.inr hγ), smul_zero]
          exact Submodule.zero_mem _
      by_cases horb : ∃ γ0 : (G.lev i').Γ, L1 = (G.lev i').smul γ0 L
      · obtain ⟨γ0, h0⟩ := horb
        have hA0 : L''.map (nt_phi (G.P.W v) ((G.lev i').act v γ0)) ∈ ef_E G.P v (L1 v) := by
          refine (Set.Finite.mem_toFinset (ef_places_finite G.P v (L1 v))).2 ?_
          have := nt_edge_map p (G.P.n' v) G.P.r ((G.lev i').act v γ0) L'' (L v) hedge
          rw [h0]
          exact this
        have e1 : delta G i' L (((p : G.Kf) ^ G.P.ArV v) • ξ) i' L1 = ((p : G.Kf) ^ G.P.ArV v) •
            delta G i' (upd G L v L'') ξ i'
              (upd G L1 v (L''.map (nt_phi (G.P.W v) ((G.lev i').act v γ0)))) := by
          have e2 : upd G L1 v (L''.map (nt_phi (G.P.W v) ((G.lev i').act v γ0))) =
              (G.lev i').smul γ0 (upd G L v L'') := by
            rw [js_smul_upd, h0]
          rw [e2, dApp i' _ γ0 ξ hlatx, h0, dApp i' L γ0 _ hL, map_smul, smul_comm]
        rw [← Finset.add_sum_erase _ _ hA0, smul_add, ← sub_sub, e1, sub_self, zero_sub, Finset.smul_sum]
        refine Submodule.neg_mem _ (Submodule.sum_mem _ fun A hA => ?_)
        refine key A (Finset.mem_of_mem_erase hA) fun γ hγ hAeq => ?_
        have hγ0 : γ = γ0 := js_free G h1 i' γ γ0 L hL (hγ.symm.trans h0)
        rw [hγ0] at hAeq
        exact (Finset.ne_of_mem_erase hA) hAeq
      · rw [dZero i' L _ i' L1 (Or.inr horb), zero_sub, Finset.smul_sum]
        exact Submodule.neg_mem _ (Submodule.sum_mem _ fun A hA =>
          key A hA fun γ hγ => absurd ⟨γ, hγ⟩ horb)
    · rw [dZero i L _ i' L1 (Or.inl hi), zero_sub, Finset.smul_sum]
      refine Submodule.neg_mem _ (Submodule.sum_mem _ fun A _ => ?_)
      rw [dZero i _ ξ i' _ (Or.inl hi), smul_zero]
      exact Submodule.zero_mem _
  have hW := js_div G v (sysOf G t (vertexLabel B)) E _ (Submodule.sub_mem _ hdM hyM) hpt
  have hsplit : delta G i L (((p : G.Kf) ^ G.P.ArV v) • ξ) =
      G.yv v (delta G i (upd G L v L'') ξ) +
        (delta G i L (((p : G.Kf) ^ G.P.ArV v) • ξ) - G.yv v (delta G i (upd G L v L'') ξ)) := by
    abel
  rw [hsplit]
  exact Submodule.add_mem_sup hyJ hW

end Formalism.MainNotions.G.LatticeSystems

namespace Formalism.MainNotions.G.LatticeSystems

open Formalism.MainNotions.G Formalism.MainNotions.SelectionLemmas Formalism.G0 Formalism.GradedWeylDivisibility

/- English proof (translation)
Establish `hm : ∀ i, ∃ μ α : O, a i = α + q * μ ∧ μ ∈ IsLocalRing.maximalIdeal O ∧ (¬ a i ∣ q → α = 0)`. Introduce `i`. Distinguish the cases in `hd : a i ∣ q`. Conclude with `⟨0, a i, by simp, Ideal.zero_mem _, fun h => absurd hd h⟩`. Break down `ValuationRing.dvd_total (a i) q with h1 | h1` into its components or cases.

Conclude with `absurd h1 hd`. Take `⟨m, hm⟩` from `h1`. Use `⟨m, 0, by rw [hm, zero_add], ?_, fun _ => rfl⟩` and prove the remaining obligations. Rewrite using `[IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]`. Introduce `hu`.

Take `⟨w, rfl⟩` from `hu`. Conclude with `hd ⟨((w⁻¹ : Oˣ) : O), by rw [hm, mul_assoc, Units.mul_inv, mul_one]⟩`. Use `choose μ α h1 h2 h3 using hm`. Set `Y : Matrix (Fin n) (Fin n) O` to `fun j k => ∑ i, cc j i * μ i * X i k`. Establish `hZ : ∀ j k, ∑ i, cc j i * α i * X i k = q * ((1 - Y) j k)`.

Introduce `j k`. Establish `e1 : ∑ i, cc j i * a i * X i k = ∑ i, cc j i * α i * X i k + q * Y j k` using `by show _ = _ + q * ∑ i, cc j i * μ i * X i k`. Rewrite using `[Finset.mul_sum, ← Finset.sum_add_distrib]`. Apply `Finset.sum_congr rfl` to reduce the goal to its premises. Introduce `i _`.

Rewrite using `[h1 i]`. Expand and normalize the polynomial expressions, which then agree. Establish `e2` using `h j k`. Rewrite `e2` using `[e1]`. Rewrite using `[Matrix.sub_apply, Matrix.one_apply, mul_sub]`.

Apply the tactic sequence `have e3 : q * (if j = k then (1 : O) else 0) = if j = k then q else 0 := by split_ifs <;> simp`. Rewrite using `[e3, ← e2]`. Expand and normalize the polynomial expressions, which then agree. Establish `hY : ∀ j k, Y j k ∈ IsLocalRing.maximalIdeal O`. Introduce `j k`.

Use `Ideal.sum_mem _ fun i _ => ?_` and prove the remaining obligations. Conclude with `Ideal.mul_mem_right _ _ (Ideal.mul_mem_left _ _ (h2 i))`. Establish `hdet : (1 - Y).det ≠ 0`. Introduce `h0`. Establish `e1 : (IsLocalRing.residue O) (1 - Y).det = ((IsLocalRing.residue O).mapMatrix (1 - Y)).det` using `RingHom.map_det _ _`.

Establish `e2 : (IsLocalRing.residue O).mapMatrix (1 - Y) = 1`. Use extensionality with `j k`. Establish `: (IsLocalRing.residue O) (Y j k) = 0` using `(IsLocalRing.residue_eq_zero_iff _).2 (hY j k)`. Simplify using `only [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.sub_apply, map_sub, this, sub_zero, Matrix.one_apply]`. Apply the tactic sequence `split_ifs <;> simp`.

Rewrite `e1` using `[e2, Matrix.det_one, h0, map_zero]`. Conclude with `zero_ne_one e1`. Set `ψ : (Fin n → O) →ₗ[O] ({i : Fin nS // a i ∣ q} → O)` to `(Matrix.of fun (i : {i : Fin nS // a i ∣ q}) (k : Fin n) => X i.1 k).mulVecLin`. Establish `hψ : Function.Injective ψ`. Rewrite using `[injective_iff_map_eq_zero]`.

Introduce `x hx`. Establish `hx' : ∀ i : Fin nS, a i ∣ q → ∑ k, X i k * x k = 0`. Introduce `i hi`. Use `congrFun hx ⟨i, hi⟩` as an intermediate fact. Simplify `this` using `[ψ, Matrix.mulVec, dotProduct]`.

Apply `Matrix.eq_zero_of_mulVec_eq_zero hdet` to reduce the goal to its premises. Use function extensionality and compare the values at `j`. Establish `e1 : q * ((1 - Y).mulVec x j) = 0` using `by show q * ∑ k, (1 - Y) j k * x k = 0`. Rewrite using `[Finset.mul_sum]`. Establish `: ∀ k, q * ((1 - Y) j k * x k) = ∑ i, cc j i * α i * (X i k * x k)`.

Introduce `k`. Rewrite using `[← mul_assoc, ← hZ, Finset.sum_mul]`. Apply `Finset.sum_congr rfl` to reduce the goal to its premises. Introduce `i _`. Expand and normalize the polynomial expressions, which then agree.

Simplify using `only [this]`. Rewrite using `[Finset.sum_comm]`. Apply `Finset.sum_eq_zero` to reduce the goal to its premises. Introduce `i _`. Rewrite using `[← Finset.mul_sum]`.

Distinguish the cases in `hi : a i ∣ q`. Rewrite using `[hx' i hi, mul_zero]`. Rewrite using `[h3 i hi, mul_zero, zero_mul]`. Conclude with `(mul_eq_zero.1 e1).resolve_left hq`. Use `LinearMap.finrank_le_finrank_of_injective hψ` as an intermediate fact.

Rewrite using `[Nat.card_eq_fintype_card]`. Simplify using `using this`.
-/
theorem jm_count {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {n nS : ℕ} (q : O) (hq : q ≠ 0)
    (a : Fin nS → O) (cc : Fin n → Fin nS → O) (X : Fin nS → Fin n → O)
    (h : ∀ j k, ∑ i, cc j i * a i * X i k = if j = k then q else 0) :
    n ≤ Nat.card {i : Fin nS // a i ∣ q} := by
  classical
  have hm : ∀ i, ∃ μ α : O, a i = α + q * μ ∧ μ ∈ IsLocalRing.maximalIdeal O ∧ (¬ a i ∣ q → α = 0) := by
    intro i
    by_cases hd : a i ∣ q
    · exact ⟨0, a i, by simp, Ideal.zero_mem _, fun h => absurd hd h⟩
    · rcases ValuationRing.dvd_total (a i) q with h1 | h1
      · exact absurd h1 hd
      · obtain ⟨m, hm⟩ := h1
        refine ⟨m, 0, by rw [hm, zero_add], ?_, fun _ => rfl⟩
        rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
        intro hu
        obtain ⟨w, rfl⟩ := hu
        exact hd ⟨((w⁻¹ : Oˣ) : O), by rw [hm, mul_assoc, Units.mul_inv, mul_one]⟩
  choose μ α h1 h2 h3 using hm
  let Y : Matrix (Fin n) (Fin n) O := fun j k => ∑ i, cc j i * μ i * X i k
  have hZ : ∀ j k, ∑ i, cc j i * α i * X i k = q * ((1 - Y) j k) := by
    intro j k
    have e1 : ∑ i, cc j i * a i * X i k = ∑ i, cc j i * α i * X i k + q * Y j k := by
      show _ = _ + q * ∑ i, cc j i * μ i * X i k
      rw [Finset.mul_sum, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro i _
      rw [h1 i]; ring
    have e2 := h j k
    rw [e1] at e2
    rw [Matrix.sub_apply, Matrix.one_apply, mul_sub]
    have e3 : q * (if j = k then (1 : O) else 0) = if j = k then q else 0 := by
      split_ifs <;> simp
    rw [e3, ← e2]; ring
  have hY : ∀ j k, Y j k ∈ IsLocalRing.maximalIdeal O := by
    intro j k
    refine Ideal.sum_mem _ fun i _ => ?_
    exact Ideal.mul_mem_right _ _ (Ideal.mul_mem_left _ _ (h2 i))
  have hdet : (1 - Y).det ≠ 0 := by
    intro h0
    have e1 : (IsLocalRing.residue O) (1 - Y).det = ((IsLocalRing.residue O).mapMatrix (1 - Y)).det :=
      RingHom.map_det _ _
    have e2 : (IsLocalRing.residue O).mapMatrix (1 - Y) = 1 := by
      ext j k
      have : (IsLocalRing.residue O) (Y j k) = 0 := (IsLocalRing.residue_eq_zero_iff _).2 (hY j k)
      simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.sub_apply, map_sub, this, sub_zero,
        Matrix.one_apply]
      split_ifs <;> simp
    rw [e2, Matrix.det_one, h0, map_zero] at e1
    exact zero_ne_one e1
  let ψ : (Fin n → O) →ₗ[O] ({i : Fin nS // a i ∣ q} → O) :=
    (Matrix.of fun (i : {i : Fin nS // a i ∣ q}) (k : Fin n) => X i.1 k).mulVecLin
  have hψ : Function.Injective ψ := by
    rw [injective_iff_map_eq_zero]
    intro x hx
    have hx' : ∀ i : Fin nS, a i ∣ q → ∑ k, X i k * x k = 0 := by
      intro i hi
      have := congrFun hx ⟨i, hi⟩
      simpa [ψ, Matrix.mulVec, dotProduct] using this
    apply Matrix.eq_zero_of_mulVec_eq_zero hdet
    funext j
    have e1 : q * ((1 - Y).mulVec x j) = 0 := by
      show q * ∑ k, (1 - Y) j k * x k = 0
      rw [Finset.mul_sum]
      have : ∀ k, q * ((1 - Y) j k * x k) = ∑ i, cc j i * α i * (X i k * x k) := by
        intro k
        rw [← mul_assoc, ← hZ, Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro i _; ring
      simp only [this]
      rw [Finset.sum_comm]
      apply Finset.sum_eq_zero
      intro i _
      rw [← Finset.mul_sum]
      by_cases hi : a i ∣ q
      · rw [hx' i hi, mul_zero]
      · rw [h3 i hi, mul_zero, zero_mul]
    exact (mul_eq_zero.1 e1).resolve_left hq
  have := LinearMap.finrank_le_finrank_of_injective hψ
  rw [Nat.card_eq_fintype_card]
  simpa using this

section Core

variable {O Kf V : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field Kf] [Algebra O Kf]
  [IsFractionRing O Kf] [AddCommGroup V] [Module Kf V] [Module O V] [IsScalarTower O Kf V]

include Kf in
omit [IsDiscreteValuationRing O] in
/- English proof (translation)
Establish `ha : algebraMap O Kf c ≠ 0` using `fun h0 => hc (IsFractionRing.injective O Kf (by rw [h0, map_zero]))`. Rewrite `h` using `[← algebraMap_smul Kf c x]`. Conclude with `(smul_eq_zero.1 h).resolve_left ha`.
-/
theorem jm_tors (c : O) (hc : c ≠ 0) (x : V) (h : c • x = 0) : x = 0 := by
  have ha : algebraMap O Kf c ≠ 0 := fun h0 => hc (IsFractionRing.injective O Kf (by rw [h0, map_zero]))
  rw [← algebraMap_smul Kf c x] at h
  exact (smul_eq_zero.1 h).resolve_left ha

/- English proof (translation)
Consider the cases of `nonempty_fintype I`. Establish `hli : LinearIndependent O b0` using `(LinearIndependent.iff_fractionRing O Kf).2 b0.linearIndependent`. Set `bH : Module.Basis I O (Submodule.span O (Set.range b0))` to `Module.Basis.span hli`. Establish `f1 : Module.Finite O (Submodule.span O (Set.range b0))` using `Module.Finite.of_basis bH`. Establish `hfH : Module.finrank O (Submodule.span O (Set.range b0)) = Module.finrank Kf V`.

Rewrite using `[Module.finrank_eq_card_basis bH, Module.finrank_eq_card_basis b0]`. Establish `f2 : Module.Finite O P` using `Module.Finite.of_injective (Submodule.inclusion hPH) (Submodule.inclusion_injective hPH)`. Establish `f3 : Module.IsTorsionFree O ↥P` using `⟨fun a ha x y hxy => by`. Establish `h0 : a • (x - y) = 0`. Rewrite using `[smul_sub]`.

Conclude with `sub_eq_zero.2 hxy`. Establish `h1 : x - y = 0` using `Subtype.ext (jm_tors (Kf := Kf) a ha.ne_zero (x - y).1 (congrArg Subtype.val h0))`. Conclude with `sub_eq_zero.1 h1⟩`. Establish `f4 : Module.Free O P` using `Module.free_of_finite_type_torsion_free'`. Establish `h1 : Module.finrank O P ≤ Module.finrank O (Submodule.span O (Set.range b0))` using `LinearMap.finrank_le_finrank_of_injective (Submodule.inclusion_injective hPH)`.

Set `φ : (Submodule.span O (Set.range b0)) →ₗ[O] P` to `LinearMap.codRestrict P ((c • LinearMap.id) ∘ₗ (Submodule.span O (Set.range b0)).subtype) (fun x => hHP x x.2)`. Establish `h2 : Module.finrank O (Submodule.span O (Set.range b0)) ≤ Module.finrank O P`. Use `LinearMap.finrank_le_finrank_of_injective (f := φ) ?_` and prove the remaining obligations. Rewrite using `[injective_iff_map_eq_zero]`. Introduce `x hx`.

Establish `: c • (x : V) = 0` using `congrArg Subtype.val hx`. Conclude with `Subtype.ext (jm_tors (Kf := Kf) c hc _ this)`. Conclude with `⟨Module.finBasisOfFinrankEq O P (by omega)⟩`.
-/
theorem jm_basis {I : Type} [Finite I] (b0 : Module.Basis I Kf V) (c : O) (hc : c ≠ 0) (P : Submodule O V)
    (hPH : P ≤ Submodule.span O (Set.range b0)) (hHP : ∀ x ∈ Submodule.span O (Set.range b0), c • x ∈ P) :
    Nonempty (Module.Basis (Fin (Module.finrank Kf V)) O P) := by
  classical
  cases nonempty_fintype I
  have hli : LinearIndependent O b0 := (LinearIndependent.iff_fractionRing O Kf).2 b0.linearIndependent
  let bH : Module.Basis I O (Submodule.span O (Set.range b0)) := Module.Basis.span hli
  have f1 : Module.Finite O (Submodule.span O (Set.range b0)) := Module.Finite.of_basis bH
  have hfH : Module.finrank O (Submodule.span O (Set.range b0)) = Module.finrank Kf V := by
    rw [Module.finrank_eq_card_basis bH, Module.finrank_eq_card_basis b0]
  have f2 : Module.Finite O P :=
    Module.Finite.of_injective (Submodule.inclusion hPH) (Submodule.inclusion_injective hPH)
  have f3 : Module.IsTorsionFree O ↥P := ⟨fun a ha x y hxy => by
    have h0 : a • (x - y) = 0 := by
      rw [smul_sub]
      exact sub_eq_zero.2 hxy
    have h1 : x - y = 0 :=
      Subtype.ext (jm_tors (Kf := Kf) a ha.ne_zero (x - y).1 (congrArg Subtype.val h0))
    exact sub_eq_zero.1 h1⟩
  have f4 : Module.Free O P := Module.free_of_finite_type_torsion_free'
  have h1 : Module.finrank O P ≤ Module.finrank O (Submodule.span O (Set.range b0)) :=
    LinearMap.finrank_le_finrank_of_injective (Submodule.inclusion_injective hPH)
  let φ : (Submodule.span O (Set.range b0)) →ₗ[O] P :=
    LinearMap.codRestrict P ((c • LinearMap.id) ∘ₗ (Submodule.span O (Set.range b0)).subtype)
      (fun x => hHP x x.2)
  have h2 : Module.finrank O (Submodule.span O (Set.range b0)) ≤ Module.finrank O P := by
    refine LinearMap.finrank_le_finrank_of_injective (f := φ) ?_
    rw [injective_iff_map_eq_zero]
    intro x hx
    have : c • (x : V) = 0 := congrArg Subtype.val hx
    exact Subtype.ext (jm_tors (Kf := Kf) c hc _ this)
  exact ⟨Module.finBasisOfFinrankEq O P (by omega)⟩

/- English proof (translation)
Take `⟨bP⟩` from `jm_basis b0 c hc P hPH hHP`. Set `fP : Fin K → P` to `fun k => ⟨f k, hf k⟩`. Take `⟨nS, snf⟩` from `Submodule.smithNormalForm bP (Submodule.span O (Set.range fP))`. Establish `hmapS : (Submodule.span O (Set.range fP)).map P.subtype = Submodule.span O (Set.range f)`. Rewrite using `[Submodule.map_span, ← Set.range_comp]`.

Both sides reduce to the same expression. Establish `hFj : ∀ j : Fin n, ∑ i, M j i • fP i ∈ Submodule.span O (Set.range fP)` using `fun j => Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)`. Set `cc : Fin n → Fin nS → O` to `fun j i => snf.bN.repr ⟨∑ i, M j i • fP i, hFj j⟩ i`. Establish `hcc : ∀ j, ∑ i, M j i • f i = ∑ i, cc j i • (snf.a i • ((snf.bM (snf.f i) : P) : V))`. Introduce `j`.

Establish `e1` using `snf.bN.sum_repr ⟨∑ i, M j i • fP i, hFj j⟩`. Establish `e2` using `congrArg (fun z : (Submodule.span O (Set.range fP)) => ((z : P) : V)) e1`. Simplify using `only [AddSubmonoidClass.coe_finsetSum, SetLike.val_smul, snf.snf] at e2`. Rewrite using `[← e2]`. Establish `hX : ∀ (i : Fin nS) (k : Fin n), ∃ z : O, algebraMap O Kf z = (u (Pi.single k 1) : Module.Dual Kf V) ((snf.bM (snf.f i) : P) : V)` using `fun i k => hpair _ (u (Pi.single k 1)).2 _ (snf.bM (snf.f i)).2`.

Use `choose X hXe using hX`. Establish `hid : ∀ j k, ∑ i, cc j i * snf.a i * X i k = if j = k then q else 0`. Introduce `j k`. Apply `IsFractionRing.injective O Kf` to reduce the goal to its premises. Establish `e1` using `hu (Pi.single k 1) j`.

Establish `e2 : ∑ i, algebraMap O Kf (M j i) * (u (Pi.single k 1) : Module.Dual Kf V) (f i) = (u (Pi.single k 1) : Module.Dual Kf V) (∑ i, M j i • f i)`. Rewrite using `[map_sum]`. Apply `Finset.sum_congr rfl` to reduce the goal to its premises. Introduce `i _`. Rewrite using `[LinearMap.map_smul_of_tower, Algebra.smul_def]`.

Rewrite `e1` using `[e2, hcc, map_sum]`. Rewrite using `[map_sum]`. Establish `e3 : algebraMap O Kf (q * (Pi.single k (1 : O) : Fin n → O) j) = algebraMap O Kf (if j = k then q else 0)`. Use `congr 1`. Distinguish the cases in `hjk : j = k`.

Substitute `hjk` using the available equality. Simplify using the standard rewrite rules. Simplify using `[hjk]`. Rewrite using `[← e3, ← e1]`. Apply `Finset.sum_congr rfl` to reduce the goal to its premises.

Introduce `i _`. Rewrite using `[LinearMap.map_smul_of_tower, LinearMap.map_smul_of_tower, Algebra.smul_def, Algebra.smul_def, ← hXe, map_mul, map_mul, mul_assoc]`. Establish `hcount` using `jm_count q hq snf.a cc X hid`. Rewrite `hcount` using `[Nat.card_eq_fintype_card, Fintype.card_subtype]`. Use `⟨fun a => ((snf.bM a : P) : V), ((Finset.univ.filter fun i => snf.a i ∣ q).map snf.f)ᶜ, ?_, ?_, ?_⟩` and prove the remaining obligations.

Establish `e1 : (⊤ : Submodule O P).map P.subtype = P`. Rewrite using `[Submodule.map_top, Submodule.range_subtype]`. Rewrite `e1` using `[← snf.bM.span_eq, Submodule.map_span, ← Set.range_comp]`. Conclude with `e1.symm`. Rewrite using `[Finset.card_compl, Finset.card_map, Fintype.card_fin]`.

Establish `: (Finset.univ.filter fun i => snf.a i ∣ q).card ≤ Module.finrank Kf V`. Use `Finset.card_le_univ ((Finset.univ.filter fun i => snf.a i ∣ q).map snf.f)` as an intermediate fact. Rewrite `this` using `[Finset.card_map, Fintype.card_fin]`. Then use the resulting hypothesis. Use linear arithmetic over natural numbers and integers. Introduce `a ha`.

Rewrite `ha` using `[Finset.mem_compl, not_not, Finset.mem_map]`. Take `⟨i, hi, rfl⟩` from `ha`. Take `⟨r, hr⟩` from `(Finset.mem_filter.1 hi).2`. Rewrite using `[← hmapS]`. Use `⟨r • (snf.bN i : P), Submodule.smul_mem _ _ (snf.bN i).2, ?_⟩` and prove the remaining obligations.

Rewrite using `[snf.snf, smul_smul, mul_comm r, ← hr]`. Both sides reduce to the same expression.
-/
theorem jm_core {I : Type} [Finite I] (b0 : Module.Basis I Kf V) (c : O) (hc : c ≠ 0) (P : Submodule O V)
    (hPH : P ≤ Submodule.span O (Set.range b0)) (hHP : ∀ x ∈ Submodule.span O (Set.range b0), c • x ∈ P)
    (N' : Submodule O (Module.Dual Kf V))
    (hpair : ∀ φ ∈ N', ∀ x ∈ P, φ x ∈ Set.range (algebraMap O Kf))
    {K n : ℕ} (f : Fin K → V) (hf : ∀ k, f k ∈ P) (q : O) (hq : q ≠ 0)
    (u : (Fin n → O) →ₗ[O] N') (M : Matrix (Fin n) (Fin K) O)
    (hu : ∀ (x : Fin n → O) (j : Fin n),
      ∑ i, algebraMap O Kf (M j i) * (u x : Module.Dual Kf V) (f i) = algebraMap O Kf (q * x j)) :
    ∃ (b : Fin (Module.finrank Kf V) → V) (bad : Finset (Fin (Module.finrank Kf V))),
      P = Submodule.span O (Set.range b) ∧ bad.card + n ≤ Module.finrank Kf V ∧
      ∀ a, a ∉ bad → q • b a ∈ Submodule.span O (Set.range f) := by
  classical
  obtain ⟨bP⟩ := jm_basis b0 c hc P hPH hHP
  let fP : Fin K → P := fun k => ⟨f k, hf k⟩
  obtain ⟨nS, snf⟩ := Submodule.smithNormalForm bP (Submodule.span O (Set.range fP))
  have hmapS : (Submodule.span O (Set.range fP)).map P.subtype = Submodule.span O (Set.range f) := by
    rw [Submodule.map_span, ← Set.range_comp]
    rfl

  have hFj : ∀ j : Fin n, ∑ i, M j i • fP i ∈ Submodule.span O (Set.range fP) := fun j =>
    Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  let cc : Fin n → Fin nS → O := fun j i => snf.bN.repr ⟨∑ i, M j i • fP i, hFj j⟩ i
  have hcc : ∀ j, ∑ i, M j i • f i = ∑ i, cc j i • (snf.a i • ((snf.bM (snf.f i) : P) : V)) := by
    intro j
    have e1 := snf.bN.sum_repr ⟨∑ i, M j i • fP i, hFj j⟩
    have e2 := congrArg (fun z : (Submodule.span O (Set.range fP)) => ((z : P) : V)) e1
    simp only [AddSubmonoidClass.coe_finsetSum, SetLike.val_smul, snf.snf] at e2
    rw [← e2]
  have hX : ∀ (i : Fin nS) (k : Fin n), ∃ z : O, algebraMap O Kf z =
      (u (Pi.single k 1) : Module.Dual Kf V) ((snf.bM (snf.f i) : P) : V) := fun i k =>
    hpair _ (u (Pi.single k 1)).2 _ (snf.bM (snf.f i)).2
  choose X hXe using hX
  have hid : ∀ j k, ∑ i, cc j i * snf.a i * X i k = if j = k then q else 0 := by
    intro j k
    apply IsFractionRing.injective O Kf
    have e1 := hu (Pi.single k 1) j
    have e2 : ∑ i, algebraMap O Kf (M j i) * (u (Pi.single k 1) : Module.Dual Kf V) (f i) =
        (u (Pi.single k 1) : Module.Dual Kf V) (∑ i, M j i • f i) := by
      rw [map_sum]
      apply Finset.sum_congr rfl
      intro i _
      rw [LinearMap.map_smul_of_tower, Algebra.smul_def]
    rw [e2, hcc, map_sum] at e1
    rw [map_sum]
    have e3 : algebraMap O Kf (q * (Pi.single k (1 : O) : Fin n → O) j) =
        algebraMap O Kf (if j = k then q else 0) := by
      congr 1
      by_cases hjk : j = k
      · subst hjk; simp
      · simp [hjk]
    rw [← e3, ← e1]
    apply Finset.sum_congr rfl
    intro i _
    rw [LinearMap.map_smul_of_tower, LinearMap.map_smul_of_tower, Algebra.smul_def, Algebra.smul_def, ← hXe,
      map_mul, map_mul, mul_assoc]
  have hcount := jm_count q hq snf.a cc X hid
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype] at hcount
  refine ⟨fun a => ((snf.bM a : P) : V), ((Finset.univ.filter fun i => snf.a i ∣ q).map snf.f)ᶜ, ?_, ?_, ?_⟩
  · have e1 : (⊤ : Submodule O P).map P.subtype = P := by
      rw [Submodule.map_top, Submodule.range_subtype]
    rw [← snf.bM.span_eq, Submodule.map_span, ← Set.range_comp] at e1
    exact e1.symm
  · rw [Finset.card_compl, Finset.card_map, Fintype.card_fin]
    have : (Finset.univ.filter fun i => snf.a i ∣ q).card ≤ Module.finrank Kf V := by
      have := Finset.card_le_univ ((Finset.univ.filter fun i => snf.a i ∣ q).map snf.f)
      rwa [Finset.card_map, Fintype.card_fin] at this
    omega
  · intro a ha
    rw [Finset.mem_compl, not_not, Finset.mem_map] at ha
    obtain ⟨i, hi, rfl⟩ := ha
    obtain ⟨r, hr⟩ := (Finset.mem_filter.1 hi).2
    rw [← hmapS]
    refine ⟨r • (snf.bN i : P), Submodule.smul_mem _ _ (snf.bN i).2, ?_⟩
    rw [snf.snf, smul_smul, mul_comm r, ← hr]
    rfl

end Core

variable {p : ℕ}

/- English proof (translation)
Substitute `hsp` using the available equality. Substitute `hA` using the available equality. Use `⟨Module.Basis.span hli, ?_⟩` and prove the remaining obligations. Establish `h1 : (Submodule.span O (Set.range (Module.Basis.span hli))).map ((Submodule.span Kf (Set.range Pf)).subtype.restrictScalars O) = Submodule.span O (Set.range Pf)`. Rewrite using `[Submodule.map_span, ← Set.range_comp]`.

Use `congr 2`. Use function extensionality and compare the values at `i`. Conclude with `congrArg Subtype.val (Module.Basis.span_apply hli i)`. Rewrite using `[← h1, Submodule.comap_map_eq_of_injective]`. Conclude with `Subtype.val_injective`.
-/
theorem jm_sub_basis {O Kf X : Type} [CommRing O] [Field Kf] [Algebra O Kf] [AddCommGroup X] [Module Kf X]
    [Module O X] [IsScalarTower O Kf X] {I : Type} (Pf : I → X) (hli : LinearIndependent Kf Pf)
    (Vs : Submodule Kf X) (hsp : Submodule.span Kf (Set.range Pf) = Vs)
    (A : Submodule O X) (hA : Submodule.span O (Set.range Pf) = A) :
    ∃ b0 : Module.Basis I Kf Vs,
      A.comap (Vs.subtype.restrictScalars O) = Submodule.span O (Set.range b0) := by
  subst hsp
  subst hA
  refine ⟨Module.Basis.span hli, ?_⟩
  have h1 : (Submodule.span O (Set.range (Module.Basis.span hli))).map
      ((Submodule.span Kf (Set.range Pf)).subtype.restrictScalars O) = Submodule.span O (Set.range Pf) := by
    rw [Submodule.map_span, ← Set.range_comp]
    congr 2
    funext i
    exact congrArg Subtype.val (Module.Basis.span_apply hli i)
  rw [← h1, Submodule.comap_map_eq_of_injective]
  exact Subtype.val_injective

/- English proof (translation)
Take `⟨g, hg, rfl⟩` from `hLv`. Use `(G.P.setting v).frac_O` as an intermediate fact. Establish `hinj : Function.Injective (algebraMap G.O G.Kf)` using `IsFractionRing.injective G.O G.Kf`. Establish `hI : H0IndepOfBasis G.O G.Kf` using `la_indep hinj`. Establish `hanti` using `kp_lamAt_antitone (G.P.lam0 v) (G.P.dom v)`.

Establish `hB` using `fun s : Fin (G.P.n' v) => la_basis hinj G.P.m (lamAt (G.P.lam0 v) s) (la_tw (G.P.ι v) (G.P.σ v) s.val g) (la_tw_det _ _ _ g hg)`. Use `choose B b1 b2 b3 b4 using hB`. Establish `hV : Vsp G.Kf (G.P.lam0 v) = tensorLat G.Kf G.Kf (fun s => dualWeyl G.Kf (G.P.m + 1) (G.P.m + 1) (nuOf (lamAt (G.P.lam0 v) s)))`. Unfold `Vsp`. Use `congr 1`.

Use function extensionality and compare the values at `s`. Rewrite using `[if_pos (hanti s)]`. Establish `hH : Hten G.O (G.P.lam0 v) (fun s => extO G.O (G.P.ι v) (G.P.σ v) s.val (colSpan (G.P.W v) g)) = tensorLat G.O G.Kf (fun s => nablaLTw G.O G.Kf G.P.m (lamAt (G.P.lam0 v) s) (la_tw (G.P.ι v) (G.P.σ v) s.val g))`. Unfold `Hten`. Use `congr 1`.

Use function extensionality and compare the values at `s`. Use `beta_reduce`. Rewrite using `[la_extO_G, H0_eq_twisted_nabla hI _ _ (hanti s) _ (la_tw_det _ _ _ g hg)]`. Establish `hKK : IsFractionRing G.Kf G.Kf` using `IsLocalization.of_le_isUnit (fun x hx => IsUnit.mk0 x (nonZeroDivisors.ne_zero hx))`. Take `⟨-, oS⟩` from `tensorBasis G.O G.Kf (Fin (G.P.n' v)) (G.P.m + 1) (G.P.m + 1) _ _ B b1 b2`.

Take `⟨kL, kS⟩` from `tensorBasis G.Kf G.Kf (Fin (G.P.n' v)) (G.P.m + 1) (G.P.m + 1) _ _ B b3 b4`. Establish `: ∀ s : Fin (G.P.n' v), Finite ↥(ssIdx (G.P.m + 1) (G.P.m + 1) (nuOf (lamAt (G.P.lam0 v) s)))` using `fun s => (sSIdxFinite (G.P.m + 1) (G.P.m + 1) (nuOf (lamAt (G.P.lam0 v) s))).to_subtype`. Unfold `HL toV`. Take `⟨b0, hb0⟩` from `jm_sub_basis (O := G.O) _ kL _ (kS.trans hV.symm) _ (oS.trans hH.symm)`. Conclude with `⟨_, inferInstance, b0, hb0⟩`.
-/
theorem jm_HL_basis (G : GAtP p) (v : Fin G.P.nV) (Lv : Lat G v) (hLv : IsLattice (G.P.W v) Lv) :
    ∃ (I : Type) (_ : Finite I) (b0 : Module.Basis I G.Kf (Vsp G.Kf (G.P.lam0 v))),
      HL (O := G.O) (G.P.ι v) (G.P.σ v) (G.P.lam0 v) Lv = Submodule.span G.O (Set.range b0) := by
  classical
  obtain ⟨g, hg, rfl⟩ := hLv
  have := (G.P.setting v).frac_O
  have hinj : Function.Injective (algebraMap G.O G.Kf) := IsFractionRing.injective G.O G.Kf
  have hI : H0IndepOfBasis G.O G.Kf := la_indep hinj
  have hanti := kp_lamAt_antitone (G.P.lam0 v) (G.P.dom v)
  have hB := fun s : Fin (G.P.n' v) => la_basis hinj G.P.m (lamAt (G.P.lam0 v) s)
    (la_tw (G.P.ι v) (G.P.σ v) s.val g) (la_tw_det _ _ _ g hg)
  choose B b1 b2 b3 b4 using hB
  have hV : Vsp G.Kf (G.P.lam0 v) = tensorLat G.Kf G.Kf
      (fun s => dualWeyl G.Kf (G.P.m + 1) (G.P.m + 1) (nuOf (lamAt (G.P.lam0 v) s))) := by
    unfold Vsp
    congr 1
    funext s
    rw [if_pos (hanti s)]
  have hH : Hten G.O (G.P.lam0 v) (fun s => extO G.O (G.P.ι v) (G.P.σ v) s.val (colSpan (G.P.W v) g)) =
      tensorLat G.O G.Kf (fun s => nablaLTw G.O G.Kf G.P.m (lamAt (G.P.lam0 v) s)
        (la_tw (G.P.ι v) (G.P.σ v) s.val g)) := by
    unfold Hten
    congr 1
    funext s
    beta_reduce
    rw [la_extO_G, H0_eq_twisted_nabla hI _ _ (hanti s) _ (la_tw_det _ _ _ g hg)]
  have hKK : IsFractionRing G.Kf G.Kf :=
    IsLocalization.of_le_isUnit (fun x hx => IsUnit.mk0 x (nonZeroDivisors.ne_zero hx))
  obtain ⟨-, oS⟩ := tensorBasis G.O G.Kf (Fin (G.P.n' v)) (G.P.m + 1) (G.P.m + 1) _ _ B b1 b2
  obtain ⟨kL, kS⟩ := tensorBasis G.Kf G.Kf (Fin (G.P.n' v)) (G.P.m + 1) (G.P.m + 1) _ _ B b3 b4
  have : ∀ s : Fin (G.P.n' v), Finite ↥(ssIdx (G.P.m + 1) (G.P.m + 1) (nuOf (lamAt (G.P.lam0 v) s))) :=
    fun s => (sSIdxFinite (G.P.m + 1) (G.P.m + 1) (nuOf (lamAt (G.P.lam0 v) s))).to_subtype
  unfold HL toV
  obtain ⟨b0, hb0⟩ := jm_sub_basis (O := G.O) _ kL _ (kS.trans hV.symm) _ (oS.trans hH.symm)
  exact ⟨_, inferInstance, b0, hb0⟩

/- English proof (translation)
Take `⟨x, hx, rfl⟩` from `hy`. Introduce `φ hφ`. Establish `hφ2 : φ ∈ Re' p (G.P.ι v) (G.P.σ v) G.P.w G.P.r (G.P.lam0 v) e` using `(Submodule.mem_iInf _).1 ((Submodule.mem_iInf _).1 hφ.2 e) ⟨he, rfl⟩`. Take `⟨ψ, hψ, rfl⟩` from `hφ2`. Establish `e2 : ((algebraMap G.O G.Kf G.P.w ^ (-Ar G.P.r (G.P.lam0 v))) • ψ) (((p : G.Kf) ^ G.P.ArV v) • ((algebraMap G.O G.Kf G.P.w ^ (-Ar G.P.r (G.P.lam0 v))) • x)) = ψ x`.

Rewrite using `[LinearMap.smul_apply, map_smul, map_smul, smul_smul, smul_smul]`. Unfold `Places.ArV`. Rewrite using `[mul_assoc, nt_scal G v, one_smul]`. Establish `e3` using `hψ x hx`. Rewrite `e3` using `[← e2]`.

Conclude with `e3`.
-/
theorem jm_Re (G : GAtP p) (v : Fin G.P.nV) (tv : ℕ) (e : Edge (G.P.W v) (G.P.Qq v) (G.P.m + 1))
    (he : IsEdge p (G.P.n' v) G.P.r e) (y : Vsp G.Kf (G.P.lam0 v))
    (hy : y ∈ Re (O := G.O) p (G.P.ι v) (G.P.σ v) G.P.w G.P.r (G.P.lam0 v) e) :
    ((p : G.Kf) ^ G.P.ArV v) • y ∈
      predual (Ntgt (O := G.O) p (G.P.n' v) (G.P.ι v) (G.P.σ v) G.P.w G.P.r (G.P.lam0 v) tv e.tgt) := by
  obtain ⟨x, hx, rfl⟩ := hy
  intro φ hφ
  have hφ2 : φ ∈ Re' p (G.P.ι v) (G.P.σ v) G.P.w G.P.r (G.P.lam0 v) e :=
    (Submodule.mem_iInf _).1 ((Submodule.mem_iInf _).1 hφ.2 e) ⟨he, rfl⟩
  obtain ⟨ψ, hψ, rfl⟩ := hφ2
  have e2 : ((algebraMap G.O G.Kf G.P.w ^ (-Ar G.P.r (G.P.lam0 v))) • ψ)
      (((p : G.Kf) ^ G.P.ArV v) • ((algebraMap G.O G.Kf G.P.w ^ (-Ar G.P.r (G.P.lam0 v))) • x)) = ψ x := by
    rw [LinearMap.smul_apply, map_smul, map_smul, smul_smul, smul_smul]
    unfold Places.ArV
    rw [mul_assoc, nt_scal G v, one_smul]
  have e3 := hψ x hx
  rw [← e2] at e3
  exact e3

/- English proof (translation)
Introduce `Lv hLv`. Take `⟨K, e, F, he, hFN, hFo, n, hn, u, M, hu⟩` from `h.2 Lv hLv`. Use `(G.P.setting v).frac_O` as an intermediate fact. Take `⟨I, hI, b0, hb0⟩` from `jm_HL_basis G v Lv hLv`. Take `⟨-, c2, -, c4⟩` from `ch_locChain G v tv (local_lattice_chain_of_local G v tv (restLocD G v)) Lv hLv`.

Establish `hPH : predual (Ntgt (O` using `G.O) p (G.P.n' v) (G.P.ι v) (G.P.σ v) G.P.w G.P.r (G.P.lam0 v) tv Lv) ≤ Submodule.span G.O (Set.range b0) := by`. Rewrite using `[← hb0]`. Introduce `x hx`. Conclude with `c2 ⟨x, hx, rfl⟩`. Establish `hHP : ∀ x ∈ Submodule.span G.O (Set.range b0), G.P.w ^ tv • x ∈ predual (Ntgt (O` using `G.O) p (G.P.n' v) (G.P.ι v) (G.P.σ v) G.P.w G.P.r (G.P.lam0 v) tv Lv) := by`.

Rewrite using `[← hb0]`. Introduce `x hx`. Take `⟨y, hy, hyx⟩` from `c4 _ hx`. Establish `: y = G.P.w ^ tv • x` using `Subtype.ext hyx`. Rewrite using `[← this]`.

Conclude with `hy`. Establish `hf : ∀ k, ((p : G.Kf) ^ G.P.ArV v) • F k ∈ predual (Ntgt (O` using `G.O) p (G.P.n' v) (G.P.ι v) (G.P.σ v) G.P.w G.P.r (G.P.lam0 v) tv Lv) := by`. Introduce `k`. Establish `h1 : F k ∈ Re (O` using `G.O) p (G.P.ι v) (G.P.σ v) G.P.w G.P.r (G.P.lam0 v) (e k) := (Submodule.mem_iInf _).1 ((Submodule.mem_iInf _).1 (hFN k).2 (e k)) ⟨(he k).1, rfl⟩`. Establish `h2` using `jm_Re G v tv (e k) (he k).1 (F k) h1`.

Rewrite `h2` using `[(he k).2]`. Then use the resulting hypothesis. Establish `hw : G.P.w ^ tv ≠ 0`. Apply `pow_ne_zero` to reduce the goal to its premises. Introduce `h0`. Conclude with `ch_w_ne_zero G v (by rw [h0, map_zero])`.

Establish `hq : (p : G.O) ^ Dd ≠ 0`. Apply `pow_ne_zero` to reduce the goal to its premises. Introduce `h0`. Conclude with `kp_p_ne_zero G v (by rw [h0, map_zero])`. Take `⟨b, bad, hb1, hb2, hb3⟩` from `jm_core b0 (G.P.w ^ tv) hw _ hPH hHP (Ntgt (O := G.O) p (G.P.n' v) (G.P.ι v) (G.P.σ v) G.P.w G.P.r (G.P.lam0 v) tv Lv) (fun φ hφ x hx => hx φ hφ) (fun k => ((p : G.Kf) ^ G.P.ArV v) • F k) hf ((p : G.O) ^ Dd) hq u M hu`.

Use `⟨K, fun k => (e k).src, fun k => (F k : Pol G v), fun a => (b a : Pol G v), bad, ?_, ?_, ?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `k`. Use `(he k).1` as an intermediate fact. Rewrite using `[← (he k).2]`. Conclude with `this`.

Introduce `k`. Conclude with `⟨F k, hFN k, rfl⟩`. Introduce `k L' hE' hne`. Establish `h3` using `hFo k ⟨(e k).src, L'⟩ hE' rfl (by`. Introduce `h0`.

Apply `hne` to reduce the goal to its premises. Rewrite using `[← (he k).2, ← h0])`. Take `⟨y, hy, hyF⟩` from `h3`. Use `⟨((((p : G.Kf) ^ G.P.ArV v) • y : Vsp G.Kf (G.P.lam0 v)) : Pol G v), ⟨_, jm_Re G v tv ⟨(e k).src, L'⟩ hE' y hy, rfl⟩, ?_⟩` and prove the remaining obligations. Establish `hyF' : (F k : Pol G v) = (algebraMap G.O G.Kf G.P.w ^ (cStar : ℤ)) • (y : Pol G v)`.

Rewrite using `[← hyF]`. Both sides reduce to the same expression. Use `show G.P.w ^ cStar • (((p : G.Kf) ^ G.P.ArV v) • (y : Pol G v)) = ((p : G.Kf) ^ G.P.ArV v) • (F k : Pol G v)`. Rewrite using `[hyF', ← algebraMap_smul G.Kf (G.P.w ^ cStar), map_pow, zpow_natCast, smul_comm]`. Use `show ofV _ = _`.

Unfold `ofV`. Rewrite using `[hb1, Submodule.map_span, ← Set.range_comp]`. Both sides reduce to the same expression. Establish `h0 : Finset.card (α` using `Fin (dimV G.Kf (G.P.lam0 v))) bad + n ≤ dimV G.Kf (G.P.lam0 v) := hb2`. Establish `h1 : ((Finset.card (α` using `Fin (dimV G.Kf (G.P.lam0 v))) bad : ℕ) : ℝ) + n ≤ (dimV G.Kf (G.P.lam0 v) : ℝ) := by`.

Conclude with `h0` after adjusting the coercions. Combine the linear equalities and inequalities to obtain the conclusion. Introduce `a ha`. Establish `h1` using `Submodule.mem_map_of_mem (f := (Vsp G.Kf (G.P.lam0 v)).subtype.restrictScalars G.O) (hb3 a ha)`. Rewrite `h1` using `[Submodule.map_span, ← Set.range_comp]`.

Conclude with `h1`.
-/
theorem jSmith (G : GAtP p) (v : Fin G.P.nV) (tv Dd cStar : ℕ) (κ : ℝ)
    (h : LPprime (W := G.P.W v) (Qq := G.P.Qq v) (O := G.O) (Kf := G.Kf) p (G.P.n' v) (G.P.ι v) (G.P.σ v)
      G.P.w G.P.r (G.P.lam0 v) tv Dd κ cStar) : JSmith G v tv Dd cStar κ := by
  intro Lv hLv
  obtain ⟨K, e, F, he, hFN, hFo, n, hn, u, M, hu⟩ := h.2 Lv hLv
  have := (G.P.setting v).frac_O
  obtain ⟨I, hI, b0, hb0⟩ := jm_HL_basis G v Lv hLv
  obtain ⟨-, c2, -, c4⟩ := ch_locChain G v tv (local_lattice_chain_of_local G v tv (restLocD G v)) Lv hLv
  have hPH : predual (Ntgt (O := G.O) p (G.P.n' v) (G.P.ι v) (G.P.σ v) G.P.w G.P.r (G.P.lam0 v) tv Lv) ≤
      Submodule.span G.O (Set.range b0) := by
    rw [← hb0]
    intro x hx
    exact c2 ⟨x, hx, rfl⟩
  have hHP : ∀ x ∈ Submodule.span G.O (Set.range b0), G.P.w ^ tv • x ∈
      predual (Ntgt (O := G.O) p (G.P.n' v) (G.P.ι v) (G.P.σ v) G.P.w G.P.r (G.P.lam0 v) tv Lv) := by
    rw [← hb0]
    intro x hx
    obtain ⟨y, hy, hyx⟩ := c4 _ hx
    have : y = G.P.w ^ tv • x := Subtype.ext hyx
    rw [← this]
    exact hy
  have hf : ∀ k, ((p : G.Kf) ^ G.P.ArV v) • F k ∈
      predual (Ntgt (O := G.O) p (G.P.n' v) (G.P.ι v) (G.P.σ v) G.P.w G.P.r (G.P.lam0 v) tv Lv) := by
    intro k
    have h1 : F k ∈ Re (O := G.O) p (G.P.ι v) (G.P.σ v) G.P.w G.P.r (G.P.lam0 v) (e k) :=
      (Submodule.mem_iInf _).1 ((Submodule.mem_iInf _).1 (hFN k).2 (e k)) ⟨(he k).1, rfl⟩
    have h2 := jm_Re G v tv (e k) (he k).1 (F k) h1
    rwa [(he k).2] at h2
  have hw : G.P.w ^ tv ≠ 0 := by
    apply pow_ne_zero
    intro h0
    exact ch_w_ne_zero G v (by rw [h0, map_zero])
  have hq : (p : G.O) ^ Dd ≠ 0 := by
    apply pow_ne_zero
    intro h0
    exact kp_p_ne_zero G v (by rw [h0, map_zero])
  obtain ⟨b, bad, hb1, hb2, hb3⟩ := jm_core b0 (G.P.w ^ tv) hw _ hPH hHP
    (Ntgt (O := G.O) p (G.P.n' v) (G.P.ι v) (G.P.σ v) G.P.w G.P.r (G.P.lam0 v) tv Lv)
    (fun φ hφ x hx => hx φ hφ) (fun k => ((p : G.Kf) ^ G.P.ArV v) • F k) hf ((p : G.O) ^ Dd) hq u M hu
  refine ⟨K, fun k => (e k).src, fun k => (F k : Pol G v), fun a => (b a : Pol G v), bad, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro k
    have := (he k).1
    rw [← (he k).2]
    exact this
  · intro k
    exact ⟨F k, hFN k, rfl⟩
  · intro k L' hE' hne
    have h3 := hFo k ⟨(e k).src, L'⟩ hE' rfl (by
      intro h0
      apply hne
      rw [← (he k).2, ← h0])
    obtain ⟨y, hy, hyF⟩ := h3
    refine ⟨((((p : G.Kf) ^ G.P.ArV v) • y : Vsp G.Kf (G.P.lam0 v)) : Pol G v),
      ⟨_, jm_Re G v tv ⟨(e k).src, L'⟩ hE' y hy, rfl⟩, ?_⟩
    have hyF' : (F k : Pol G v) = (algebraMap G.O G.Kf G.P.w ^ (cStar : ℤ)) • (y : Pol G v) := by
      rw [← hyF]; rfl
    show G.P.w ^ cStar • (((p : G.Kf) ^ G.P.ArV v) • (y : Pol G v)) = ((p : G.Kf) ^ G.P.ArV v) • (F k : Pol G v)
    rw [hyF', ← algebraMap_smul G.Kf (G.P.w ^ cStar), map_pow, zpow_natCast, smul_comm]
  · show ofV _ = _
    unfold ofV
    rw [hb1, Submodule.map_span, ← Set.range_comp]
    rfl
  · have h0 : Finset.card (α := Fin (dimV G.Kf (G.P.lam0 v))) bad + n ≤ dimV G.Kf (G.P.lam0 v) := hb2
    have h1 : ((Finset.card (α := Fin (dimV G.Kf (G.P.lam0 v))) bad : ℕ) : ℝ) + n ≤
        (dimV G.Kf (G.P.lam0 v) : ℝ) := by
      exact_mod_cast h0
    linarith
  · intro a ha
    have h1 := Submodule.mem_map_of_mem (f := (Vsp G.Kf (G.P.lam0 v)).subtype.restrictScalars G.O) (hb3 a ha)
    rw [Submodule.map_span, ← Set.range_comp] at h1
    exact h1

end Formalism.MainNotions.G.LatticeSystems

namespace Formalism.MainNotions.G.LatticeSystems

open Formalism.MainNotions.G Formalism.MainNotions.SelectionLemmas Formalism.G0

open Pointwise

variable {p : ℕ}

/- English proof (translation)
Establish `h1 : (fun u => G.P.vEmb u (Function.update f v y u)) = Function.update (fun u => G.P.vEmb u (f u)) v (G.P.vEmb v y)`. Use function extensionality and compare the values at `u`. Conclude with `Function.apply_update (fun u => G.P.vEmb u) f v y u`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem jl_prod_upd (G : GAtP p) (v : Fin G.P.nV) (f : ∀ u, Pol G u) (y : Pol G v) :
    ∏ u, G.P.vEmb u (Function.update f v y u) =
      G.P.vEmb v y * ∏ u ∈ Finset.univ \ {v}, G.P.vEmb u (f u) := by
  have h1 : (fun u => G.P.vEmb u (Function.update f v y u)) =
      Function.update (fun u => G.P.vEmb u (f u)) v (G.P.vEmb v y) := by
    funext u
    exact Function.apply_update (fun u => G.P.vEmb u) f v y u
  calc ∏ u, G.P.vEmb u (Function.update f v y u)
      = ∏ u, Function.update (fun u => G.P.vEmb u (f u)) v (G.P.vEmb v y) u := by rw [← h1]
    _ = _ := Finset.prod_update_of_mem (Finset.mem_univ v) _ _

/- English proof (translation)
Use `jl_prod_upd G v f (f v)` as an intermediate fact. Rewrite `this` using `[Function.update_eq_self]`. Conclude with `this`.
-/
theorem jl_prod_self (G : GAtP p) (v : Fin G.P.nV) (f : ∀ u, Pol G u) :
    ∏ u, G.P.vEmb u (f u) = G.P.vEmb v (f v) * ∏ u ∈ Finset.univ \ {v}, G.P.vEmb u (f u) := by
  have := jl_prod_upd G v f (f v)
  rw [Function.update_eq_self] at this
  exact this

/- English proof (translation)
The claim follows from `(G.P.vEmb v).toLinearMap.map_smul_of_tower c y`.
-/
theorem jl_emb_smul (G : GAtP p) (v : Fin G.P.nV) (c : G.O) (y : Pol G v) :
    G.P.vEmb v (c • y) = c • G.P.vEmb v y :=
  (G.P.vEmb v).toLinearMap.map_smul_of_tower c y

/- English proof (translation)
Unfold `Places.tenV`. Apply `Submodule.subset_span` to reduce the goal to its premises. Use `⟨Function.update f v y, ?_, (jl_prod_upd G v f y).symm⟩` and prove the remaining obligations. Introduce `u`. Distinguish the cases in `h : u = v`.

Substitute `h` using the available equality. Rewrite using `[Function.update_self]`. Conclude with `hy`. Rewrite using `[Function.update_of_ne h]`. Conclude with `hf u h`.
-/
theorem jl_mem_tenV (G : GAtP p) (v : Fin G.P.nV) (M : ∀ u, Submodule G.O (Pol G u)) (f : ∀ u, Pol G u)
    (y : Pol G v) (hy : y ∈ M v) (hf : ∀ u, u ≠ v → f u ∈ M u) :
    G.P.vEmb v y * ∏ u ∈ Finset.univ \ {v}, G.P.vEmb u (f u) ∈ G.P.tenV M := by
  unfold Places.tenV
  apply Submodule.subset_span
  refine ⟨Function.update f v y, ?_, (jl_prod_upd G v f y).symm⟩
  intro u
  by_cases h : u = v
  · subst h
    rw [Function.update_self]
    exact hy
  · rw [Function.update_of_ne h]
    exact hf u h

/- English proof (translation)
The claim follows from `Function.update_self (β := fun v => Lat G v) v A L`.
-/
theorem jl_upd_self (G : GAtP p) (L : G.P.Tup) (v : Fin G.P.nV) (A : Lat G v) : upd G L v A v = A :=
  Function.update_self (β := fun v => Lat G v) v A L

/- English proof (translation)
The claim follows from `Function.update_of_ne (β := fun v => Lat G v) h A L`.
-/
theorem jl_upd_ne (G : GAtP p) (L : G.P.Tup) (v : Fin G.P.nV) (A : Lat G v) (u : Fin G.P.nV) (h : u ≠ v) :
    upd G L v A u = L u :=
  Function.update_of_ne (β := fun v => Lat G v) h A L

/- English proof (translation)
Use `hD.2.1 i L 0 0` as an intermediate fact. Rewrite `this` using `[zero_smul, zero_smul]`. Conclude with `this`.
-/
theorem jl_delta_zero (G : GAtP p) (hD : JDelta G) (i : G.comp) (L : G.P.Tup) : delta G i L 0 = 0 := by
  have := hD.2.1 i L 0 0
  rw [zero_smul, zero_smul] at this
  exact this

/- English proof (translation)
Establish `dadd` using `hD.1`. Establish `dsmul` using `hD.2.1`. Proceed by induction on `hz using Submodule.span_induction with`. Consider the case `mem z hz`. Take `⟨k, rfl⟩` from `hz`.

Establish `e1 : G.P.vEmb v (((p : G.Kf) ^ G.P.ArV v) • F k) * ∏ u ∈ Finset.univ \ {v}, G.P.vEmb u (f u) = ((p : G.Kf) ^ G.P.ArV v) • (G.P.vEmb v (F k) * ∏ u ∈ Finset.univ \ {v}, G.P.vEmb u (f u))`. Rewrite using `[map_smul, smul_mul_assoc]`. Rewrite using `[e1]`. Use `hS1 v hv i L hL (src k) (h1 k) _ ?_ ?_` and prove the remaining obligations. Use `jl_mem_tenV G v (fun u => piLattice₂ G u (t u) (Function.update (vertexLabel B) v Slot.ball u) (upd G L v (src k) u)) f (F k) ?_ ?_` and prove the remaining obligations.

Simplify using `only [Function.update_self, jl_upd_self]`. Conclude with `h2 k`. Introduce `u hu`. Simplify using `only [Function.update_of_ne hu, jl_upd_ne G L v _ u hu]`. Conclude with `hf u hu`.

Introduce `L' he hne`. Take `⟨y, hy, hyE⟩` from `h3 k L' he hne`. Establish `hyE' : G.P.w ^ cStar • y = ((p : G.Kf) ^ G.P.ArV v) • F k` using `hyE`. Use `⟨G.P.w ^ (cStar - 2 * (Dd + 1)) • (G.P.vEmb v y * ∏ u ∈ Finset.univ \ {v}, G.P.vEmb u (f u)), ?_, ?_⟩` and prove the remaining obligations. Apply `Submodule.smul_mem` to reduce the goal to its premises.

Use `jl_mem_tenV G v (fun u => piLattice₂ G u (t u) (vertexLabel B u) (upd G L v L' u)) f y ?_ ?_` and prove the remaining obligations. Establish `hs : vertexLabel B v = Slot.dual` using `by simp [vertexLabel, hv]`. Simplify using `only [jl_upd_self, hs]`. Conclude with `hy`. Introduce `u hu`.

Simplify using `only [jl_upd_ne G L v _ u hu]`. Conclude with `hf u hu`. Use `show (p : G.O) ^ (Dd + 1) • (G.P.w ^ (cStar - 2 * (Dd + 1)) • (G.P.vEmb v y * ∏ u ∈ Finset.univ \ {v}, G.P.vEmb u (f u))) = _`. Rewrite using `[← e1, ← hyE', jl_emb_smul, smul_mul_assoc, smul_smul, ← (G.P.setting v).w_sq, ← pow_mul, ← pow_add]`. Use `congr 2`.

Use linear arithmetic over natural numbers and integers. Consider the case `zero`. Rewrite using `[map_zero, zero_mul, jl_delta_zero G hD]`. Conclude with `Submodule.zero_mem _`. Consider the case `add x y _ _ hx hy`.

Rewrite using `[map_add, add_mul, dadd]`. Conclude with `Submodule.add_mem _ hx hy`. Consider the case `smul c x _ hx`. Rewrite using `[jl_emb_smul, smul_mul_assoc, dsmul]`. Conclude with `Submodule.smul_mem _ c hx`.
-/
theorem jl_good (G : GAtP p) (t : Fin G.P.nV → ℕ) (B : Finset (Fin G.P.nV)) (Dd cStar : ℕ)
    (hc : 4 * (Dd + 1) ≤ cStar) (hD : JDelta G) (hS1 : JStep1 G t B (Dd + 1)) (v : Fin G.P.nV) (hv : v ∈ B)
    (i : G.comp) (L : G.P.Tup) (hL : G.P.IsLatTup L) (K : ℕ) (src : Fin K → Lat G v) (F : Fin K → Pol G v)
    (h1 : ∀ k, IsEdge p (G.P.n' v) G.P.r ⟨src k, L v⟩)
    (h2 : ∀ k, F k ∈ piLattice₂ G v (t v) Slot.ball (src k))
    (h3 : ∀ k (L' : Lat G v), IsEdge p (G.P.n' v) G.P.r ⟨src k, L'⟩ → L' ≠ L v →
      ((p : G.Kf) ^ G.P.ArV v) • F k ∈ sc G (G.P.w ^ cStar) (piLattice₂ G v (t v) Slot.dual L'))
    (f : ∀ u, Pol G u) (hf : ∀ u, u ≠ v → f u ∈ piLattice₂ G u (t u) (vertexLabel B u) (L u))
    (z : Pol G v) (hz : z ∈ Submodule.span G.O (Set.range fun k => ((p : G.Kf) ^ G.P.ArV v) • F k)) :
    delta G i L (G.P.vEmb v z * ∏ u ∈ Finset.univ \ {v}, G.P.vEmb u (f u)) ∈
      JBof G t B ⊔ sc G ((p : G.O) ^ (Dd + 1)) (MBof G t B) := by
  have dadd := hD.1
  have dsmul := hD.2.1
  induction hz using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨k, rfl⟩ := hz
    have e1 : G.P.vEmb v (((p : G.Kf) ^ G.P.ArV v) • F k) * ∏ u ∈ Finset.univ \ {v}, G.P.vEmb u (f u) =
        ((p : G.Kf) ^ G.P.ArV v) • (G.P.vEmb v (F k) * ∏ u ∈ Finset.univ \ {v}, G.P.vEmb u (f u)) := by
      rw [map_smul, smul_mul_assoc]
    rw [e1]
    refine hS1 v hv i L hL (src k) (h1 k) _ ?_ ?_
    · refine jl_mem_tenV G v (fun u => piLattice₂ G u (t u) (Function.update (vertexLabel B) v Slot.ball u)
        (upd G L v (src k) u)) f (F k) ?_ ?_
      · simp only [Function.update_self, jl_upd_self]
        exact h2 k
      · intro u hu
        simp only [Function.update_of_ne hu, jl_upd_ne G L v _ u hu]
        exact hf u hu
    · intro L' he hne
      obtain ⟨y, hy, hyE⟩ := h3 k L' he hne
      have hyE' : G.P.w ^ cStar • y = ((p : G.Kf) ^ G.P.ArV v) • F k := hyE
      refine ⟨G.P.w ^ (cStar - 2 * (Dd + 1)) •
        (G.P.vEmb v y * ∏ u ∈ Finset.univ \ {v}, G.P.vEmb u (f u)), ?_, ?_⟩
      · apply Submodule.smul_mem
        refine jl_mem_tenV G v (fun u => piLattice₂ G u (t u) (vertexLabel B u) (upd G L v L' u)) f y ?_ ?_
        · have hs : vertexLabel B v = Slot.dual := by simp [vertexLabel, hv]
          simp only [jl_upd_self, hs]
          exact hy
        · intro u hu
          simp only [jl_upd_ne G L v _ u hu]
          exact hf u hu
      · show (p : G.O) ^ (Dd + 1) • (G.P.w ^ (cStar - 2 * (Dd + 1)) •
          (G.P.vEmb v y * ∏ u ∈ Finset.univ \ {v}, G.P.vEmb u (f u))) = _
        rw [← e1, ← hyE', jl_emb_smul, smul_mul_assoc, smul_smul, ← (G.P.setting v).w_sq, ← pow_mul,
          ← pow_add]
        congr 2
        omega
  | zero =>
    rw [map_zero, zero_mul, jl_delta_zero G hD]
    exact Submodule.zero_mem _
  | add x y _ _ hx hy =>
    rw [map_add, add_mul, dadd]
    exact Submodule.add_mem _ hx hy
  | smul c x _ hx =>
    rw [jl_emb_smul, smul_mul_assoc, dsmul]
    exact Submodule.smul_mem _ c hx

/- English proof (translation)
Unfold `Places.tenV`. Rewrite using `[Submodule.span_le]`. Introduce and unpack `_ ⟨F, hF, rfl⟩`. Establish `h1 : ∏ v, G.P.vEmb v (F v) ∈ ∏ v, Submodule.span G.O (Set.range fun a => G.P.vEmb v (β v a))`. Use `fn_prod_mem _ _ _ (fun v _ => ?_)` and prove the remaining obligations.

Establish `h2 : (Submodule.span G.O (Set.range (β v))).map ((G.P.vEmb v).toLinearMap.restrictScalars G.O) = Submodule.span G.O (Set.range fun a => G.P.vEmb v (β v a))`. Rewrite using `[Submodule.map_span, ← Set.range_comp]`. Both sides reduce to the same expression. Rewrite using `[← h2]`. Conclude with `⟨F v, hF v, rfl⟩`.

Rewrite `h1` using `[Submodule.prod_span]`. Use `(Submodule.span_le.2 ?_) h1` and prove the remaining obligations. Introduce `X hX`. Rewrite `hX` using `[Set.mem_finsetProd]`. Take `⟨g, hg, rfl⟩` from `hX`.

Use `choose a ha using fun v => hg (Finset.mem_univ v)`. Establish `h3 : ∏ v, g v = ∏ v, G.P.vEmb v (β v (a v))` using `Finset.prod_congr rfl (fun v _ => (ha v).symm)`. Rewrite using `[h3]`. Conclude with `h a`.
-/
theorem jl_span (G : GAtP p) (d : Fin G.P.nV → ℕ) (β : ∀ v, Fin (d v) → Pol G v) (S : Submodule G.O G.P.Xsp)
    (h : ∀ a : ∀ v, Fin (d v), ∏ v, G.P.vEmb v (β v (a v)) ∈ S) :
    G.P.tenV (fun v => Submodule.span G.O (Set.range (β v))) ≤ S := by
  unfold Places.tenV
  rw [Submodule.span_le]
  rintro _ ⟨F, hF, rfl⟩
  have h1 : ∏ v, G.P.vEmb v (F v) ∈
      ∏ v, Submodule.span G.O (Set.range fun a => G.P.vEmb v (β v a)) := by
    refine fn_prod_mem _ _ _ (fun v _ => ?_)
    have h2 : (Submodule.span G.O (Set.range (β v))).map ((G.P.vEmb v).toLinearMap.restrictScalars G.O) =
        Submodule.span G.O (Set.range fun a => G.P.vEmb v (β v a)) := by
      rw [Submodule.map_span, ← Set.range_comp]
      rfl
    rw [← h2]
    exact ⟨F v, hF v, rfl⟩
  rw [Submodule.prod_span] at h1
  refine (Submodule.span_le.2 ?_) h1
  intro X hX
  rw [Set.mem_finsetProd] at hX
  obtain ⟨g, hg, rfl⟩ := hX
  choose a ha using fun v => hg (Finset.mem_univ v)
  have h3 : ∏ v, g v = ∏ v, G.P.vEmb v (β v (a v)) := Finset.prod_congr rfl (fun v _ => (ha v).symm)
  rw [h3]
  exact h a

def jl_Q (G : GAtP p) (hD : JDelta G) (i : G.comp) (L : G.P.Tup) (c₀ : G.O) (T : Submodule G.O G.Fn)
    (Cs : Submodule G.O G.P.Xsp) : Submodule G.O G.P.Xsp where
  carrier := {ξ | ∃ g c, c₀ • ξ = g + c ∧ delta G i L g ∈ T ∧ c ∈ Cs}
  add_mem' := by
    rintro x y ⟨g, c, e, hg, hc⟩ ⟨g', c', e', hg', hc'⟩
    refine ⟨g + g', c + c', ?_, ?_, Cs.add_mem hc hc'⟩
    · rw [smul_add, e, e']; abel
    · rw [hD.1]; exact T.add_mem hg hg'
  zero_mem' := ⟨0, 0, by simp, by rw [jl_delta_zero G hD]; exact T.zero_mem, Cs.zero_mem⟩
  smul_mem' := by
    rintro a x ⟨g, c, e, hg, hc⟩
    refine ⟨a • g, a • c, ?_, ?_, Cs.smul_mem a hc⟩
    · rw [smul_comm, e, smul_add]
    · rw [hD.2.1]; exact T.smul_mem a hg

/- English proof (translation)
Introduce `i L hL`. Establish `key : ∀ v, ∃ (β : Fin (dimV G.Kf (G.P.lam0 v)) → Pol G v) (bad : Finset (Fin (dimV G.Kf (G.P.lam0 v)))), piLattice₂ G v (t v) (vertexLabel B v) (L v) = Submodule.span G.O (Set.range β) ∧ (v ∈ B → (bad.card : ℝ) ≤ κ v * (dimV G.Kf (G.P.lam0 v) : ℝ) ∧ ∀ a, a ∉ bad → ∀ f : ∀ u, Pol …`. Introduce `v`. Distinguish the cases in `hv : v ∈ B`. Take `⟨K, src, F, b, bad, e1, e2, e3, e4, e5, e6⟩` from `hSm v hv (L v) (hL v)`.

Use `⟨b, bad, ?_, fun _ => ⟨e5, fun a ha f hf => jl_good G t B Dd cStar hc hD hS1 v hv i L hL K src F e1 e2 e3 f hf _ (e6 a ha)⟩⟩` and prove the remaining obligations. Establish `hs : vertexLabel B v = Slot.dual` using `by simp [vertexLabel, hv]`. Rewrite using `[hs]`. Conclude with `e4`. Take `⟨b, hb⟩` from `hBase v (t v) (L v) (hL v)`.

Use `⟨b, ∅, ?_, fun h => absurd h hv⟩` and prove the remaining obligations. Establish `hs : vertexLabel B v = Slot.base` using `by simp [vertexLabel, hv]`. Rewrite using `[hs]`. Conclude with `hb`. Use `choose β bad hβ hbad using key`.

Establish `hmemβ : ∀ (a : ∀ v, Fin (dimV G.Kf (G.P.lam0 v))) (u : Fin G.P.nV), β u (a u) ∈ piLattice₂ G u (t u) (vertexLabel B u) (L u)`. Introduce `a u`. Rewrite using `[hβ u]`. Conclude with `Submodule.subset_span ⟨a u, rfl⟩`. Set `idx : Finset (∀ v, Fin (dimV G.Kf (G.P.lam0 v)))` to `Fintype.piFinset fun v => if v ∈ B then bad v else Finset.univ`.

Set `prodOf : (∀ v, Fin (dimV G.Kf (G.P.lam0 v))) → G.P.Xsp` to `fun a => ∏ v, G.P.vEmb v (β v (a v))`. Use `⟨idx.image prodOf, ?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `X hX`. Take `⟨a, -, rfl⟩` from `Finset.mem_image.1 (Finset.mem_coe.1 hX)`. Establish `h0 : prodOf a ∈ G.P.tenV (fun v => piLattice₂ G v (t v) (vertexLabel B v) (L v))` using `Submodule.subset_span ⟨fun v => β v (a v), fun v => hmemβ a v, rfl⟩`.

Conclude with `h0`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[Fintype.card_piFinset]`. Use `push_cast`. Both sides reduce to the same expression.

Use `_ ≤ ∏ v, ((if v ∈ B then κ v else 1) * (dimV G.Kf (G.P.lam0 v) : ℝ)) := by`. Use `Finset.prod_le_prod (fun v _ => Nat.cast_nonneg _) (fun v _ => ?_)` and prove the remaining obligations. Distinguish the cases in `hv : v ∈ B`. Simplify using `only [hv, if_true]`. Conclude with `(hbad v hv).1`.

Simplify using `[hv]`. Use `_ = (∏ v ∈ B, κ v) * ((∏ v, dimV G.Kf (G.P.lam0 v) : ℕ) : ℝ) := by`. Rewrite using `[Finset.prod_mul_distrib, Finset.prod_ite_mem, Finset.univ_inter]`. Use `push_cast`. Both sides reduce to the same expression.

Establish `hle : G.P.tenV (fun v => Submodule.span G.O (Set.range (β v))) ≤ jl_Q G hD i L ((p : G.O) ^ Dd) (JBof G t B ⊔ sc G ((p : G.O) ^ (Dd + 1)) (MBof G t B)) (Submodule.span G.O (↑(idx.image prodOf) : Set G.P.Xsp))`. Use `jl_span G _ β _ (fun a => ?_)` and prove the remaining obligations. Distinguish the cases in `hall : ∀ v ∈ B, a v ∈ bad v`. Establish `ha : a ∈ idx`. Rewrite using `[Fintype.mem_piFinset]`.

Introduce `v`. Distinguish the cases in `hv : v ∈ B`. Simplify using `only [hv, if_true]`. Conclude with `hall v hv`. Simplify using `[hv]`.

Use `⟨0, (p : G.O) ^ Dd • prodOf a, by simp [prodOf], ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[jl_delta_zero G hD]`. Conclude with `Submodule.zero_mem _`. Conclude with `Submodule.smul_mem _ _ (Submodule.subset_span (Finset.mem_coe.2 (Finset.mem_image_of_mem prodOf ha)))`. Use `push Not at hall`.

Take `⟨v, hv, hav⟩` from `hall`. Use `⟨(p : G.O) ^ Dd • prodOf a, 0, by simp [prodOf], ?_, Submodule.zero_mem _⟩` and prove the remaining obligations. Establish `e : (p : G.O) ^ Dd • prodOf a = G.P.vEmb v ((p : G.O) ^ Dd • β v (a v)) * ∏ u ∈ Finset.univ \ {v}, G.P.vEmb u (β u (a u))`. Rewrite using `[jl_emb_smul, smul_mul_assoc]`. Use `congr 1`.

Conclude with `jl_prod_self G v (fun u => β u (a u))`. Rewrite using `[e]`. Conclude with `(hbad v hv).2 (a v) hav (fun u => β u (a u)) (fun u _ => hmemβ a u)`. Establish `heq : (fun v => piLattice₂ G v (t v) (vertexLabel B v) (L v)) = fun v => Submodule.span G.O (Set.range (β v))` using `funext hβ`. Introduce `ξ hξ`.

Establish `hξ' : ξ ∈ G.P.tenV (fun v => piLattice₂ G v (t v) (vertexLabel B v) (L v))` using `hξ`. Rewrite `hξ'` using `[heq]`. Conclude with `hle hξ'`.
-/
theorem jLocal (G : GAtP p) (t : Fin G.P.nV → ℕ) (B : Finset (Fin G.P.nV)) (Dd cStar : ℕ)
    (κ : Fin G.P.nV → ℝ) (_hB : B.Nonempty) (hc : 4 * (Dd + 1) ≤ cStar) (hD : JDelta G)
    (hS1 : JStep1 G t B (Dd + 1)) (hSm : ∀ v ∈ B, JSmith G v (t v) Dd cStar (κ v))
    (hBase : ∀ v, JBase G v) : JLocal G t B Dd κ := by
  classical
  intro i L hL
  have key : ∀ v, ∃ (β : Fin (dimV G.Kf (G.P.lam0 v)) → Pol G v)
      (bad : Finset (Fin (dimV G.Kf (G.P.lam0 v)))),
      piLattice₂ G v (t v) (vertexLabel B v) (L v) = Submodule.span G.O (Set.range β) ∧
      (v ∈ B → (bad.card : ℝ) ≤ κ v * (dimV G.Kf (G.P.lam0 v) : ℝ) ∧
        ∀ a, a ∉ bad → ∀ f : ∀ u, Pol G u,
          (∀ u, u ≠ v → f u ∈ piLattice₂ G u (t u) (vertexLabel B u) (L u)) →
          delta G i L (G.P.vEmb v ((p : G.O) ^ Dd • β a) * ∏ u ∈ Finset.univ \ {v}, G.P.vEmb u (f u)) ∈
            JBof G t B ⊔ sc G ((p : G.O) ^ (Dd + 1)) (MBof G t B)) := by
    intro v
    by_cases hv : v ∈ B
    · obtain ⟨K, src, F, b, bad, e1, e2, e3, e4, e5, e6⟩ := hSm v hv (L v) (hL v)
      refine ⟨b, bad, ?_, fun _ => ⟨e5, fun a ha f hf =>
        jl_good G t B Dd cStar hc hD hS1 v hv i L hL K src F e1 e2 e3 f hf _ (e6 a ha)⟩⟩
      have hs : vertexLabel B v = Slot.dual := by simp [vertexLabel, hv]
      rw [hs]
      exact e4
    · obtain ⟨b, hb⟩ := hBase v (t v) (L v) (hL v)
      refine ⟨b, ∅, ?_, fun h => absurd h hv⟩
      have hs : vertexLabel B v = Slot.base := by simp [vertexLabel, hv]
      rw [hs]
      exact hb
  choose β bad hβ hbad using key
  have hmemβ : ∀ (a : ∀ v, Fin (dimV G.Kf (G.P.lam0 v))) (u : Fin G.P.nV),
      β u (a u) ∈ piLattice₂ G u (t u) (vertexLabel B u) (L u) := by
    intro a u
    rw [hβ u]
    exact Submodule.subset_span ⟨a u, rfl⟩
  let idx : Finset (∀ v, Fin (dimV G.Kf (G.P.lam0 v))) :=
    Fintype.piFinset fun v => if v ∈ B then bad v else Finset.univ
  let prodOf : (∀ v, Fin (dimV G.Kf (G.P.lam0 v))) → G.P.Xsp := fun a => ∏ v, G.P.vEmb v (β v (a v))
  refine ⟨idx.image prodOf, ?_, ?_, ?_⟩
  · intro X hX
    obtain ⟨a, -, rfl⟩ := Finset.mem_image.1 (Finset.mem_coe.1 hX)
    have h0 : prodOf a ∈ G.P.tenV (fun v => piLattice₂ G v (t v) (vertexLabel B v) (L v)) :=
      Submodule.subset_span ⟨fun v => β v (a v), fun v => hmemβ a v, rfl⟩
    exact h0
  · calc ((idx.image prodOf).card : ℝ) ≤ (idx.card : ℝ) := by exact_mod_cast Finset.card_image_le
      _ = ∏ v, (((if v ∈ B then bad v else Finset.univ).card : ℕ) : ℝ) := by
          rw [Fintype.card_piFinset]
          push_cast
          rfl
      _ ≤ ∏ v, ((if v ∈ B then κ v else 1) * (dimV G.Kf (G.P.lam0 v) : ℝ)) := by
          refine Finset.prod_le_prod (fun v _ => Nat.cast_nonneg _) (fun v _ => ?_)
          by_cases hv : v ∈ B
          · simp only [hv, if_true]
            exact (hbad v hv).1
          · simp [hv]
      _ = (∏ v ∈ B, κ v) * ((∏ v, dimV G.Kf (G.P.lam0 v) : ℕ) : ℝ) := by
          rw [Finset.prod_mul_distrib, Finset.prod_ite_mem, Finset.univ_inter]
          push_cast
          rfl
  · have hle : G.P.tenV (fun v => Submodule.span G.O (Set.range (β v))) ≤
        jl_Q G hD i L ((p : G.O) ^ Dd) (JBof G t B ⊔ sc G ((p : G.O) ^ (Dd + 1)) (MBof G t B))
          (Submodule.span G.O (↑(idx.image prodOf) : Set G.P.Xsp)) := by
      refine jl_span G _ β _ (fun a => ?_)
      by_cases hall : ∀ v ∈ B, a v ∈ bad v
      · have ha : a ∈ idx := by
          rw [Fintype.mem_piFinset]
          intro v
          by_cases hv : v ∈ B
          · simp only [hv, if_true]
            exact hall v hv
          · simp [hv]
        refine ⟨0, (p : G.O) ^ Dd • prodOf a, by simp [prodOf], ?_, ?_⟩
        · rw [jl_delta_zero G hD]
          exact Submodule.zero_mem _
        · exact Submodule.smul_mem _ _ (Submodule.subset_span
            (Finset.mem_coe.2 (Finset.mem_image_of_mem prodOf ha)))
      · push Not at hall
        obtain ⟨v, hv, hav⟩ := hall
        refine ⟨(p : G.O) ^ Dd • prodOf a, 0, by simp [prodOf], ?_, Submodule.zero_mem _⟩
        have e : (p : G.O) ^ Dd • prodOf a =
            G.P.vEmb v ((p : G.O) ^ Dd • β v (a v)) *
              ∏ u ∈ Finset.univ \ {v}, G.P.vEmb u (β u (a u)) := by
          rw [jl_emb_smul, smul_mul_assoc]
          congr 1
          exact jl_prod_self G v (fun u => β u (a u))
        rw [e]
        exact (hbad v hv).2 (a v) hav (fun u => β u (a u)) (fun u _ => hmemβ a u)
    have heq : (fun v => piLattice₂ G v (t v) (vertexLabel B v) (L v)) =
        fun v => Submodule.span G.O (Set.range (β v)) := funext hβ
    intro ξ hξ
    have hξ' : ξ ∈ G.P.tenV (fun v => piLattice₂ G v (t v) (vertexLabel B v) (L v)) := hξ
    rw [heq] at hξ'
    exact hle hξ'

end Formalism.MainNotions.G.LatticeSystems

namespace Formalism.MainNotions.G.LatticeSystems

open Formalism.MainNotions.G Formalism.GradedWeylDivisibility MvPolynomial Formalism.G0

variable {p : ℕ}

abbrev jr_I (G : GAtP p) (v : Fin G.P.nV) (s : Fin (G.P.n' v)) : Type :=
  ↥(ssIdx (G.P.m + 1) (G.P.m + 1) (nuOf (lamAt (G.P.lam0 v) s)))

instance jr_fin (G : GAtP p) (v : Fin G.P.nV) (s : Fin (G.P.n' v)) : Finite (jr_I G v s) :=
  (sSIdxFinite (G.P.m + 1) (G.P.m + 1) (nuOf (lamAt (G.P.lam0 v) s))).to_subtype

/- English proof (translation)
The claim follows from `IsLocalization.of_le_isUnit (fun x hx => IsUnit.mk0 x (nonZeroDivisors.ne_zero hx))`.
-/
theorem jr_KK (K : Type) [Field K] : IsFractionRing K K :=
  IsLocalization.of_le_isUnit (fun x hx => IsUnit.mk0 x (nonZeroDivisors.ne_zero hx))

/- English proof (translation)
Unfold `Vsp`. Use `congr 1`. Use function extensionality and compare the values at `s`. Rewrite using `[if_pos (kp_lamAt_antitone (G.P.lam0 v) (G.P.dom v) s)]`.
-/
theorem jr_Vsp (G : GAtP p) (v : Fin G.P.nV) : Vsp G.Kf (G.P.lam0 v) = tensorLat G.Kf G.Kf
    (fun s => dualWeyl G.Kf (G.P.m + 1) (G.P.m + 1) (nuOf (lamAt (G.P.lam0 v) s))) := by
  unfold Vsp
  congr 1
  funext s
  rw [if_pos (kp_lamAt_antitone (G.P.lam0 v) (G.P.dom v) s)]

/- English proof (translation)
Take `⟨g, hg, rfl⟩` from `hLv`. Use `(G.P.setting v).frac_O` as an intermediate fact. Establish `hinj : Function.Injective (algebraMap G.O G.Kf)` using `IsFractionRing.injective G.O G.Kf`. Establish `hanti` using `kp_lamAt_antitone (G.P.lam0 v) (G.P.dom v)`. Establish `hB` using `fun s : Fin (G.P.n' v) => la_basis hinj G.P.m (lamAt (G.P.lam0 v) s) (la_tw (G.P.ι v) (G.P.σ v) s.val g) (la_tw_det _ _ _ g hg)`.

Use `choose B b1 b2 b3 b4 using hB`. Establish `hH : Hten G.O (G.P.lam0 v) (fun s => extO G.O (G.P.ι v) (G.P.σ v) s.val (colSpan (G.P.W v) g)) = tensorLat G.O G.Kf (fun s => nablaLTw G.O G.Kf G.P.m (lamAt (G.P.lam0 v) s) (la_tw (G.P.ι v) (G.P.σ v) s.val g))`. Unfold `Hten`. Use `congr 1`. Use function extensionality and compare the values at `s`.

Use `beta_reduce`. Rewrite using `[la_extO_G, H0_eq_twisted_nabla (la_indep hinj) _ _ (hanti s) _ (la_tw_det _ _ _ g hg)]`. Take `⟨-, oS⟩` from `tensorBasis G.O G.Kf (Fin (G.P.n' v)) (G.P.m + 1) (G.P.m + 1) _ _ B b1 b2`. Conclude with `⟨B, b3, b4, oS.trans hH.symm⟩`.
-/
theorem jr_loc (G : GAtP p) (v : Fin G.P.nV) (Lv : Lat G v) (hLv : IsLattice (G.P.W v) Lv) :
    ∃ B : ∀ s : Fin (G.P.n' v), jr_I G v s → MvPolynomial (Fin (G.P.m + 1) × Fin (G.P.m + 1)) G.Kf,
      (∀ s, LinearIndependent G.Kf (B s)) ∧
      (∀ s, Submodule.span G.Kf (Set.range (B s)) =
        dualWeyl G.Kf (G.P.m + 1) (G.P.m + 1) (nuOf (lamAt (G.P.lam0 v) s))) ∧
      Submodule.span G.O (Set.range fun i : (∀ s, jr_I G v s) => ∏ s, blockEmb G.Kf s (B s (i s))) =
        Hten G.O (G.P.lam0 v) (fun s => extO G.O (G.P.ι v) (G.P.σ v) s.val Lv) := by
  classical
  obtain ⟨g, hg, rfl⟩ := hLv
  have := (G.P.setting v).frac_O
  have hinj : Function.Injective (algebraMap G.O G.Kf) := IsFractionRing.injective G.O G.Kf
  have hanti := kp_lamAt_antitone (G.P.lam0 v) (G.P.dom v)
  have hB := fun s : Fin (G.P.n' v) => la_basis hinj G.P.m (lamAt (G.P.lam0 v) s)
    (la_tw (G.P.ι v) (G.P.σ v) s.val g) (la_tw_det _ _ _ g hg)
  choose B b1 b2 b3 b4 using hB
  have hH : Hten G.O (G.P.lam0 v) (fun s => extO G.O (G.P.ι v) (G.P.σ v) s.val (colSpan (G.P.W v) g)) =
      tensorLat G.O G.Kf (fun s => nablaLTw G.O G.Kf G.P.m (lamAt (G.P.lam0 v) s)
        (la_tw (G.P.ι v) (G.P.σ v) s.val g)) := by
    unfold Hten
    congr 1
    funext s
    beta_reduce
    rw [la_extO_G, H0_eq_twisted_nabla (la_indep hinj) _ _ (hanti s) _ (la_tw_det _ _ _ g hg)]
  obtain ⟨-, oS⟩ := tensorBasis G.O G.Kf (Fin (G.P.n' v)) (G.P.m + 1) (G.P.m + 1) _ _ B b1 b2
  exact ⟨B, b3, b4, oS.trans hH.symm⟩

/- English proof (translation)
Establish `hb` using `fun s : Fin (G.P.n' v) => sSBasis G.Kf (G.P.m + 1) (G.P.m + 1) (nuOf (lamAt (G.P.lam0 v) s))`. Use `choose b hb1 _ using hb`. Use `jr_KK G.Kf` as an intermediate fact. Take `⟨hli, hsp⟩` from `tensorBasis G.Kf G.Kf (Fin (G.P.n' v)) (G.P.m + 1) (G.P.m + 1) (fun s => jr_I G v s) (fun s => dualWeyl G.Kf (G.P.m + 1) (G.P.m + 1) (nuOf (lamAt (G.P.lam0 v) s))) b (fun s => (hb1 s).1) (fun s => (hb1 s).2.1)`. Establish `: Fintype (∀ s, jr_I G v s)` using `Fintype.ofFinite _`.

Unfold `dimV`. Rewrite using `[jr_Vsp, ← hsp, finrank_span_eq_card hli, Nat.card_eq_fintype_card]`.
-/
theorem jr_dim (G : GAtP p) (v : Fin G.P.nV) :
    Nat.card (∀ s, jr_I G v s) = dimV G.Kf (G.P.lam0 v) := by
  classical
  have hb := fun s : Fin (G.P.n' v) => sSBasis G.Kf (G.P.m + 1) (G.P.m + 1) (nuOf (lamAt (G.P.lam0 v) s))
  choose b hb1 _ using hb
  have := jr_KK G.Kf
  obtain ⟨hli, hsp⟩ := tensorBasis G.Kf G.Kf (Fin (G.P.n' v)) (G.P.m + 1) (G.P.m + 1)
    (fun s => jr_I G v s)
    (fun s => dualWeyl G.Kf (G.P.m + 1) (G.P.m + 1) (nuOf (lamAt (G.P.lam0 v) s))) b
    (fun s => (hb1 s).1) (fun s => (hb1 s).2.1)
  have : Fintype (∀ s, jr_I G v s) := Fintype.ofFinite _
  unfold dimV
  rw [jr_Vsp, ← hsp, finrank_span_eq_card hli, Nat.card_eq_fintype_card]

/- English proof (translation)
Introduce `tv Lv hLv`. Take `⟨B, -, -, hB⟩` from `jr_loc G v Lv hLv`. Set `e` to `Finite.equivFinOfCardEq (jr_dim G v)`. Use `⟨fun a => ∏ s, blockEmb G.Kf s (B s (e.symm a s)), ?_⟩` and prove the remaining obligations. Establish `hr : (Set.range fun a => ∏ s, blockEmb G.Kf s (B s (e.symm a s))) = Set.range fun i : (∀ s, jr_I G v s) => ∏ s, blockEmb G.Kf s (B s (i s))` using `e.symm.surjective.range_comp (fun i : (∀ s, jr_I G v s) => ∏ s, blockEmb G.Kf s (B s (i s)))`.

Rewrite using `[hr, hB]`. Both sides reduce to the same expression.
-/
theorem jBase (G : GAtP p) (v : Fin G.P.nV) : JBase G v := by
  intro tv Lv hLv
  obtain ⟨B, -, -, hB⟩ := jr_loc G v Lv hLv
  let e := Finite.equivFinOfCardEq (jr_dim G v)
  refine ⟨fun a => ∏ s, blockEmb G.Kf s (B s (e.symm a s)), ?_⟩
  have hr : (Set.range fun a => ∏ s, blockEmb G.Kf s (B s (e.symm a s))) =
      Set.range fun i : (∀ s, jr_I G v s) => ∏ s, blockEmb G.Kf s (B s (i s)) :=
    e.symm.surjective.range_comp (fun i : (∀ s, jr_I G v s) => ∏ s, blockEmb G.Kf s (B s (i s)))
  rw [hr, hB]
  rfl

abbrev jr_S (G : GAtP p) : Type := Σ v : Fin G.P.nV, Fin (G.P.n' v)

abbrev jr_J (G : GAtP p) : Type := ∀ x : jr_S G, jr_I G x.1 x.2

/- English proof (translation)
Rewrite using `[Nat.card_pi, Fintype.prod_sigma]`. Apply `Finset.prod_congr rfl` to reduce the goal to its premises. Introduce `v _`. Rewrite using `[← jr_dim, Nat.card_pi]`.
-/
theorem jr_card (G : GAtP p) : Nat.card (jr_J G) = ∏ v, dimV G.Kf (G.P.lam0 v) := by
  rw [Nat.card_pi, Fintype.prod_sigma]
  apply Finset.prod_congr rfl
  intro v _
  rw [← jr_dim, Nat.card_pi]

def jr_psi (G : GAtP p) : jr_S G × (Fin (G.P.m + 1) × Fin (G.P.m + 1)) →
    (Σ v : Fin G.P.nV, Fin (G.P.n' v) × (Fin (G.P.m + 1) × Fin (G.P.m + 1))) :=
  fun y => ⟨y.1.1, (y.1.2, y.2)⟩

/- English proof (translation)
Introduce and unpack `⟨⟨v, s⟩, x⟩ ⟨⟨v', s'⟩, x'⟩ h`. Simplify using `only [jr_psi, Sigma.mk.injEq] at h`. Take `⟨rfl, h2⟩` from `h`. Simplify using `only [heq_eq_eq, Prod.mk.injEq] at h2`. Take `⟨rfl, rfl⟩` from `h2`.

Both sides reduce to the same expression.
-/
theorem jr_psi_inj (G : GAtP p) : Function.Injective (jr_psi G) := by
  rintro ⟨⟨v, s⟩, x⟩ ⟨⟨v', s'⟩, x'⟩ h
  simp only [jr_psi, Sigma.mk.injEq] at h
  obtain ⟨rfl, h2⟩ := h
  simp only [heq_eq_eq, Prod.mk.injEq] at h2
  obtain ⟨rfl, rfl⟩ := h2
  rfl

/- English proof (translation)
Establish `hB` using `fun v => jr_loc G v (L v) (hL v)`. Use `choose B b3 b4 bH using hB`. Use `jr_KK G.Kf` as an intermediate fact. Take `⟨hli, -⟩` from `tensorBasis G.Kf G.Kf (jr_S G) (G.P.m + 1) (G.P.m + 1) (fun x => jr_I G x.1 x.2) (fun x => dualWeyl G.Kf (G.P.m + 1) (G.P.m + 1) (nuOf (lamAt (G.P.lam0 x.1) x.2))) (fun x => B x.1 x.2) (fun x => b3 x.1 x.2) (fun x => b4 x.1 x.2)`. Establish `hli2` using `hli.map' (rename (jr_psi G) : _ →ₐ[G.Kf] G.P.Xsp).toLinearMap (LinearMap.ker_eq_bot.2 (rename_injective _ (jr_psi_inj G)))`.

Establish `hfO` using `(G.P.setting v0).frac_O`. Establish `hinj : Function.Injective (algebraMap G.O G.Kf)` using `IsFractionRing.injective G.O G.Kf`. Establish `hli3 : LinearIndependent G.O _` using `hli2.restrict_scalars (by intro a b hab; apply hinj; simpa [Algebra.smul_def] using hab)`. Use `⟨_, hli3, fun i => ?_⟩` and prove the remaining obligations. Apply `Submodule.subset_span` to reduce the goal to its premises.

Use `⟨fun v => ∏ s, blockEmb G.Kf s (B v s (i ⟨v, s⟩)), fun v => ?_, ?_⟩` and prove the remaining obligations. Establish `hm : (∏ s, blockEmb G.Kf s (B v s (i ⟨v, s⟩))) ∈ Submodule.span G.O (Set.range fun j : (∀ s, jr_I G v s) => ∏ s, blockEmb G.Kf s (B v s (j s)))` using `Submodule.subset_span ⟨fun s => i ⟨v, s⟩, rfl⟩`. Conclude with `(bH v).le hm`. Simplify using `only [Function.comp_apply, AlgHom.toLinearMap_apply, map_prod]`. Rewrite using `[Fintype.prod_sigma]`.

Apply `Finset.prod_congr rfl` to reduce the goal to its premises. Introduce `v _`. Apply `Finset.prod_congr rfl` to reduce the goal to its premises. Introduce `s _`. Unfold `blockEmb Places.vEmb`.

Rewrite using `[rename_rename, rename_rename]`. Both sides reduce to the same expression.
-/
theorem jr_tuple (G : GAtP p) (v0 : Fin G.P.nV) (L : G.P.Tup) (hL : G.P.IsLatTup L) :
    ∃ Q : jr_J G → G.P.Xsp, LinearIndependent G.O Q ∧ ∀ i, Q i ∈ G.P.Htup L := by
  classical
  have hB := fun v => jr_loc G v (L v) (hL v)
  choose B b3 b4 bH using hB
  have := jr_KK G.Kf
  obtain ⟨hli, -⟩ := tensorBasis G.Kf G.Kf (jr_S G) (G.P.m + 1) (G.P.m + 1)
    (fun x => jr_I G x.1 x.2)
    (fun x => dualWeyl G.Kf (G.P.m + 1) (G.P.m + 1) (nuOf (lamAt (G.P.lam0 x.1) x.2)))
    (fun x => B x.1 x.2) (fun x => b3 x.1 x.2) (fun x => b4 x.1 x.2)
  have hli2 := hli.map' (rename (jr_psi G) : _ →ₐ[G.Kf] G.P.Xsp).toLinearMap
    (LinearMap.ker_eq_bot.2 (rename_injective _ (jr_psi_inj G)))
  have hfO := (G.P.setting v0).frac_O
  have hinj : Function.Injective (algebraMap G.O G.Kf) := IsFractionRing.injective G.O G.Kf
  have hli3 : LinearIndependent G.O _ := hli2.restrict_scalars
    (by intro a b hab; apply hinj; simpa [Algebra.smul_def] using hab)
  refine ⟨_, hli3, fun i => ?_⟩
  apply Submodule.subset_span
  refine ⟨fun v => ∏ s, blockEmb G.Kf s (B v s (i ⟨v, s⟩)), fun v => ?_, ?_⟩
  · have hm : (∏ s, blockEmb G.Kf s (B v s (i ⟨v, s⟩))) ∈ Submodule.span G.O
        (Set.range fun j : (∀ s, jr_I G v s) => ∏ s, blockEmb G.Kf s (B v s (j s))) :=
      Submodule.subset_span ⟨fun s => i ⟨v, s⟩, rfl⟩
    exact (bH v).le hm
  · simp only [Function.comp_apply, AlgHom.toLinearMap_apply, map_prod]
    rw [Fintype.prod_sigma]
    apply Finset.prod_congr rfl
    intro v _
    apply Finset.prod_congr rfl
    intro s _
    unfold blockEmb Places.vEmb
    rw [rename_rename, rename_rename]
    rfl

/- English proof (translation)
Introduce `reps hreps`. Take `⟨-, -, d_mem, -, d_self, d_zero, -, -⟩` from `hD`. Take `⟨r1, r2, -⟩` from `hreps`. Establish `hQ : ∀ r : ↥reps, ∃ Q : jr_J G → G.P.Xsp, LinearIndependent G.O Q ∧ ∀ i, Q i ∈ G.P.Htup r.1.2` using `fun r => jr_tuple G v0 _ (r1 r.1 r.2)`. Use `choose Q q1 q2 using hQ`.

Establish `hfin` using `mna_finite G h2`. Establish `: Fintype (jr_J G)` using `Fintype.ofFinite _`. Set `Z : ↥reps × jr_J G → G.Fn` to `fun x => delta G x.1.1.1 x.1.1.2 (Q x.1 x.2)`. Establish `hEb : EquivSys G G.P.Htup` using `hE (fun _ => 0) (fun _ => Slot.base)`. Establish `hZ : ∀ x, Z x ∈ G.Mna` using `fun x => d_mem G.P.Htup hEb _ _ (r1 _ x.1.2) _ (q2 _ _)`.

Establish `hval : ∀ (r r0 : ↥reps) (j : jr_J G), Z (r, j) r0.1.1 r0.1.2 = if r = r0 then Q r0 j else 0`. Introduce `r r0 j`. Distinguish the cases in `h : r = r0`. Substitute `h` using the available equality. Rewrite using `[if_pos rfl]`.

Conclude with `d_self _ _ _ (r1 _ r.2)`. Rewrite using `[if_neg h]`. Apply `d_zero` to reduce the goal to its premises. Assume the negation of the conclusion as `hc`. Establish `hc1` using `not_not.1 (not_or.1 hc).1`.

Establish `hc2` using `not_not.1 (not_or.1 hc).2`. Conclude with `h (Subtype.ext (r2 r.1 r.2 r0.1 r0.2 hc1.symm hc2))`. Establish `hli : LinearIndependent G.O Z`. Rewrite using `[Fintype.linearIndependent_iff]`. Introduce `c hc x0`.

Establish `hev` using `congrFun (congrFun hc x0.1.1.1) x0.1.1.2`. Rewrite `hev` using `[Fintype.sum_prod_type]`. Simplify using `only [Finset.sum_apply, Pi.smul_apply, hval, Pi.zero_apply] at hev`. Rewrite `hev` using `[Finset.sum_eq_single x0.1]`. Simplify using `only [if_true] at hev`.

Conclude with `Fintype.linearIndependent_iff.1 (q1 x0.1) (fun j => c (x0.1, j)) hev x0.2`. Introduce `r _ hr`. Simplify using `[hr]`. Introduce `h`. Conclude with `absurd (Finset.mem_univ _) h`.

Establish `hli' : LinearIndependent G.O (fun x => (⟨Z x, hZ x⟩ : ↥G.Mna))` using `LinearIndependent.of_comp G.Mna.subtype hli`. Establish `hc` using `hli'.fintype_card_le_finrank`. Rewrite `hc` using `[Fintype.card_prod, Fintype.card_coe, ← Nat.card_eq_fintype_card, jr_card]`. Conclude with `hc`.
-/
theorem jRank (G : GAtP p) (v0 : Fin G.P.nV) (h2 : G.FinClasses) (hE : JEquiv G) (hD : JDelta G) : JRank G := by
  classical
  intro reps hreps
  obtain ⟨-, -, d_mem, -, d_self, d_zero, -, -⟩ := hD
  obtain ⟨r1, r2, -⟩ := hreps
  have hQ : ∀ r : ↥reps, ∃ Q : jr_J G → G.P.Xsp, LinearIndependent G.O Q ∧ ∀ i, Q i ∈ G.P.Htup r.1.2 :=
    fun r => jr_tuple G v0 _ (r1 r.1 r.2)
  choose Q q1 q2 using hQ
  have hfin := mna_finite G h2
  have : Fintype (jr_J G) := Fintype.ofFinite _
  let Z : ↥reps × jr_J G → G.Fn := fun x => delta G x.1.1.1 x.1.1.2 (Q x.1 x.2)
  have hEb : EquivSys G G.P.Htup := hE (fun _ => 0) (fun _ => Slot.base)
  have hZ : ∀ x, Z x ∈ G.Mna := fun x => d_mem G.P.Htup hEb _ _ (r1 _ x.1.2) _ (q2 _ _)
  have hval : ∀ (r r0 : ↥reps) (j : jr_J G), Z (r, j) r0.1.1 r0.1.2 = if r = r0 then Q r0 j else 0 := by
    intro r r0 j
    by_cases h : r = r0
    · subst h
      rw [if_pos rfl]
      exact d_self _ _ _ (r1 _ r.2)
    · rw [if_neg h]
      apply d_zero
      by_contra hc
      have hc1 := not_not.1 (not_or.1 hc).1
      have hc2 := not_not.1 (not_or.1 hc).2
      exact h (Subtype.ext (r2 r.1 r.2 r0.1 r0.2 hc1.symm hc2))
  have hli : LinearIndependent G.O Z := by
    rw [Fintype.linearIndependent_iff]
    intro c hc x0
    have hev := congrFun (congrFun hc x0.1.1.1) x0.1.1.2
    rw [Fintype.sum_prod_type] at hev
    simp only [Finset.sum_apply, Pi.smul_apply, hval, Pi.zero_apply] at hev
    rw [Finset.sum_eq_single x0.1] at hev
    · simp only [if_true] at hev
      exact Fintype.linearIndependent_iff.1 (q1 x0.1) (fun j => c (x0.1, j)) hev x0.2
    · intro r _ hr
      simp [hr]
    · intro h
      exact absurd (Finset.mem_univ _) h
  have hli' : LinearIndependent G.O (fun x => (⟨Z x, hZ x⟩ : ↥G.Mna)) :=
    LinearIndependent.of_comp G.Mna.subtype hli
  have hc := hli'.fintype_card_le_finrank
  rw [Fintype.card_prod, Fintype.card_coe, ← Nat.card_eq_fintype_card, jr_card] at hc
  exact hc

end Formalism.MainNotions.G.LatticeSystems

namespace Formalism.MainNotions.G.LatticeSystems

open Formalism.MainNotions.G Formalism.MainNotions.SelectionLemmas Formalism.G0

variable {p : ℕ}

/- English proof (translation)
Establish `h1` using `(hF i (Set.mem_univ i)).1.1`. Establish `h2` using `(Submodule.mem_iInf _).1 ((Submodule.mem_iInf _).1 h1 L) hL`. Conclude with `h2`.
-/
theorem ja_val (G : GAtP p) (Hv : G.P.Tup → Submodule G.O G.P.Xsp) {F : G.Fn} (hF : F ∈ G.funMod Hv)
    (i : G.comp) (L : G.P.Tup) (hL : G.P.IsLatTup L) : F i L ∈ Hv L := by
  have h1 := (hF i (Set.mem_univ i)).1.1
  have h2 := (Submodule.mem_iInf _).1 ((Submodule.mem_iInf _).1 h1 L) hL
  exact h2

/- English proof (translation)
Establish `hS` using `G.P.setting v`. Set `_ : Algebra (G.P.W v) G.O` to `(G.P.j v).toAlgebra`. Establish `hfin : Module.Finite (G.P.W v) G.O` using `hS.finite`. Establish `hint : Algebra.IsIntegral (G.P.W v) G.O` using `Algebra.IsIntegral.of_finite _ _`. Establish `hinj : Function.Injective (algebraMap (G.P.W v) G.O)`.

Introduce `a b hab`. Establish `h1 : algebraMap G.O G.Kf (G.P.j v a) = algebraMap G.O G.Kf (G.P.j v b)` using `congrArg _ hab`. Rewrite `h1` using `[← hS.ι_comp, ← hS.ι_comp]`. Use `hS.frac_alt` as an intermediate fact. Conclude with `IsFractionRing.injective (G.P.W v) (G.P.Qq v) ((G.P.ι v).injective h1)`.

Take `⟨Q, hQ, hQc⟩` from `Ideal.exists_ideal_over_maximal_of_isIntegral (S := G.O) (IsLocalRing.maximalIdeal (G.P.W v)) (by rw [(RingHom.injective_iff_ker_eq_bot _).1 hinj]; exact bot_le)`. Introduce `hu`. Establish `hp : (p : G.P.W v) ∈ IsLocalRing.maximalIdeal (G.P.W v)`. Rewrite using `[IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]`. Conclude with `hS.p_unif.not_isUnit`.

Rewrite `hp` using `[← hQc, Ideal.mem_comap, map_natCast]`. Conclude with `hQ.ne_top (Ideal.eq_top_of_isUnit_mem _ hp hu)`.
-/
theorem ja_p_nonunit (G : GAtP p) (v : Fin G.P.nV) : ¬ IsUnit (p : G.O) := by
  have hS := G.P.setting v
  let _ : Algebra (G.P.W v) G.O := (G.P.j v).toAlgebra
  have hfin : Module.Finite (G.P.W v) G.O := hS.finite
  have hint : Algebra.IsIntegral (G.P.W v) G.O := Algebra.IsIntegral.of_finite _ _
  have hinj : Function.Injective (algebraMap (G.P.W v) G.O) := by
    intro a b hab
    have h1 : algebraMap G.O G.Kf (G.P.j v a) = algebraMap G.O G.Kf (G.P.j v b) := congrArg _ hab
    rw [← hS.ι_comp, ← hS.ι_comp] at h1
    have := hS.frac_alt
    exact IsFractionRing.injective (G.P.W v) (G.P.Qq v) ((G.P.ι v).injective h1)
  obtain ⟨Q, hQ, hQc⟩ := Ideal.exists_ideal_over_maximal_of_isIntegral (S := G.O)
    (IsLocalRing.maximalIdeal (G.P.W v))
    (by rw [(RingHom.injective_iff_ker_eq_bot _).1 hinj]; exact bot_le)
  intro hu
  have hp : (p : G.P.W v) ∈ IsLocalRing.maximalIdeal (G.P.W v) := by
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    exact hS.p_unif.not_isUnit
  rw [← hQc, Ideal.mem_comap, map_natCast] at hp
  exact hQ.ne_top (Ideal.eq_top_of_isUnit_mem _ hp hu)

/- English proof (translation)
Establish `c2` using `(ch_chain G Finset.univ t (fun v _ => ch_locChain G v (t v) (local_lattice_chain_of_local G v (t v) (restLocD G v)))).2.1`. Unfold `MBof`. Proceed by induction on `B using Finset.induction_on with`. Consider the case `empty`. Establish `: vertexLabel (∅ : Finset (Fin G.P.nV)) = fun _ => Slot.base`.

Use function extensionality and compare the values at `v`. Simplify using `[vertexLabel]`. Rewrite using `[this]`. Conclude with `le_of_eq (latSys_base G t)`. Consider the case `insert v B hv ih`.

Establish `e1 : vertexLabel (insert v B) = Function.update (vertexLabel B) v Slot.dual`. Use function extensionality and compare the values at `u`. Distinguish the cases in `hu : u = v`. Substitute `hu` using the available equality. Simplify using `[vertexLabel]`.

Simplify using `[vertexLabel, hu]`. Establish `e2 : Function.update (vertexLabel B) v Slot.base = vertexLabel B`. Use function extensionality and compare the values at `u`. Distinguish the cases in `hu : u = v`. Substitute `hu` using the available equality.

Simplify using `[vertexLabel, hv]`. Simplify using `[Function.update_of_ne hu]`. Rewrite using `[e1]`. Use `(c2 (vertexLabel B) v (Finset.mem_univ v)).trans ?_` and prove the remaining obligations. Rewrite using `[e2]`.

Conclude with `ih`.
-/
theorem ja_MB_le (G : GAtP p) (t : Fin G.P.nV → ℕ) (B : Finset (Fin G.P.nV)) : MBof G t B ≤ G.Mna := by
  classical
  have c2 := (ch_chain G Finset.univ t
    (fun v _ => ch_locChain G v (t v) (local_lattice_chain_of_local G v (t v) (restLocD G v)))).2.1
  unfold MBof
  induction B using Finset.induction_on with
  | empty =>
    have : vertexLabel (∅ : Finset (Fin G.P.nV)) = fun _ => Slot.base := by
      funext v; simp [vertexLabel]
    rw [this]
    exact le_of_eq (latSys_base G t)
  | insert v B hv ih =>
    have e1 : vertexLabel (insert v B) = Function.update (vertexLabel B) v Slot.dual := by
      funext u
      by_cases hu : u = v
      · subst hu; simp [vertexLabel]
      · simp [vertexLabel, hu]
    have e2 : Function.update (vertexLabel B) v Slot.base = vertexLabel B := by
      funext u
      by_cases hu : u = v
      · subst hu; simp [vertexLabel, hv]
      · simp [Function.update_of_ne hu]
    rw [e1]
    refine (c2 (vertexLabel B) v (Finset.mem_univ v)).trans ?_
    rw [e2]
    exact ih

/- English proof (translation)
Take `⟨dadd, dsmul, dmem, -, -, -, ⟨reps, hreps⟩, ddec⟩` from `hD`. Establish `hL' : ∀ r : G.comp × G.P.Tup, ∃ C : Finset G.P.Xsp, G.P.IsLatTup r.2 → ((↑C : Set G.P.Xsp) ⊆ sysOf G t (vertexLabel B) r.2 ∧ (C.card : ℝ) ≤ (∏ v ∈ B, κ v) * ((∏ v, dimV G.Kf (G.P.lam0 v) : ℕ) : ℝ) ∧ ∀ ξ ∈ sysOf G t (vertexLabel B) r.2, ∃ g c, (p : G.O) ^ Dd • ξ = g + c ∧ delta G …`. Introduce `r`. Distinguish the cases in `h : G.P.IsLatTup r.2`. Take `⟨C, hC⟩` from `hL r.1 r.2 h`.

Conclude with `⟨C, fun _ => hC⟩`. Conclude with `⟨∅, fun h' => absurd h' h⟩`. Use `choose Cr hCr using hL'`. Set `dl : ∀ r : G.comp × G.P.Tup, G.P.Xsp →ₗ[G.O] G.Fn` to `fun r => { toFun := delta G r.1 r.2, map_add' := dadd r.1 r.2, map_smul' := dsmul r.1 r.2 }`. Use `set C : Finset G.Fn := reps.biUnion fun r => (Cr r).image (delta G r.1 r.2) with hCdef`.

Establish `hCM : (↑C : Set G.Fn) ⊆ latSys G t (vertexLabel B)`. Introduce `z hz`. Rewrite `hz` using `[hCdef, Finset.mem_coe, Finset.mem_biUnion]`. Take `⟨r, hr, hz⟩` from `hz`. Take `⟨c, hc, rfl⟩` from `Finset.mem_image.1 hz`.

Conclude with `dmem (sysOf G t (vertexLabel B)) (hE t _) r.1 r.2 (hreps.1 r hr) c ((hCr r (hreps.1 r hr)).1 hc)`. Establish `hprod : 0 ≤ ∏ v ∈ B, κ v` using `Finset.prod_nonneg hκ`. Establish `hcard : (C.card : ℝ) ≤ (∏ v ∈ B, κ v) * (G.dna : ℝ)`. Establish `h1 : C.card ≤ ∑ r ∈ reps, (Cr r).card` using `Finset.card_biUnion_le.trans (Finset.sum_le_sum fun r _ => Finset.card_image_le)`. Combine the equalities or inequalities in the displayed calculation.

Rewrite using `[Finset.sum_const, nsmul_eq_mul]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Use `_ ≤ (∏ v ∈ B, κ v) * (G.dna : ℝ) := mul_le_mul_of_nonneg_left (by exact_mod_cast hR reps hreps) hprod`. Use `⟨C, hCM, hcard, ?_⟩` and prove the remaining obligations.

Use `set T : Submodule G.O G.Fn := JBof G t B ⊔ Submodule.span G.O (↑C : Set G.Fn) with hT`. Establish `key : ∀ x ∈ MBof G t B, (p : G.O) ^ Dd • x ∈ T ⊔ sc G ((p : G.O) ^ (Dd + 1)) (MBof G t B)`. Introduce `x hx`. Establish `hdec` using `ddec reps hreps (sysOf G t (vertexLabel B)) x hx`. Rewrite using `[hdec, Finset.smul_sum]`.

Use `Submodule.sum_mem _ fun r hr => ?_` and prove the remaining obligations. Take `⟨g, c, hgc, hg, hc⟩` from `(hCr r (hreps.1 r hr)).2.2 (x r.1 r.2) (ja_val G _ hx r.1 r.2 (hreps.1 r hr))`. Rewrite using `[← dsmul, hgc, dadd]`. Use `Submodule.add_mem _ ?_ ?_` and prove the remaining obligations. Conclude with `(sup_le_sup_right le_sup_left _ : JBof G t B ⊔ _ ≤ T ⊔ _) hg`.

Apply `Submodule.mem_sup_left` to reduce the goal to its premises. Apply `Submodule.mem_sup_right` to reduce the goal to its premises. Establish `h3 : dl r c ∈ (Submodule.span G.O (↑(Cr r) : Set G.P.Xsp)).map (dl r)` using `Submodule.mem_map_of_mem hc`. Rewrite `h3` using `[Submodule.map_span]`. Use `Submodule.span_mono ?_ h3` and prove the remaining obligations.

Introduce and unpack `_ ⟨c', hc', rfl⟩`. Rewrite using `[hCdef, Finset.mem_coe, Finset.mem_biUnion]`. Conclude with `⟨r, hr, Finset.mem_image_of_mem _ hc'⟩`. Establish `hfin : Module.Finite G.O G.Mna` using `mna_finite G h2`. Establish `hMBfg : (MBof G t B).FG` using `(isNoetherian_submodule.mp (isNoetherian_of_fg_of_noetherian _ (Module.Finite.iff_fg.mp hfin))) _ (ja_MB_le G t B)`.

Establish `hNfg : (sc G ((p : G.O) ^ Dd) (MBof G t B)).FG` using `hMBfg.map _`. Establish `hjac : Ideal.span {(p : G.O)} ≤ Ideal.jacobson ⊥`. Rewrite using `[IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top, Ideal.span_singleton_le_iff_mem, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]`. Conclude with `ja_p_nonunit G v0`. Establish `hle : sc G ((p : G.O) ^ Dd) (MBof G t B) ≤ T ⊔ Ideal.span {(p : G.O)} • sc G ((p : G.O) ^ Dd) (MBof G t B)`.

Introduce and unpack `_ ⟨x, hx, rfl⟩`. Use `(sup_le_sup_left ?_ T : T ⊔ sc G ((p : G.O) ^ (Dd + 1)) (MBof G t B) ≤ _) (key x hx)` and prove the remaining obligations. Introduce and unpack `_ ⟨y, hy, rfl⟩`. Establish `: (LinearMap.lsmul G.O G.Fn ((p : G.O) ^ (Dd + 1))) y = (p : G.O) • ((p : G.O) ^ Dd • y)`. Simplify using `only [LinearMap.lsmul_apply]`.

Rewrite using `[smul_smul, pow_succ']`. Rewrite using `[this]`. Conclude with `Submodule.smul_mem_smul (Ideal.mem_span_singleton_self _) ⟨y, hy, rfl⟩`. Establish `hN` using `Submodule.le_of_le_smul_of_le_jacobson_bot hNfg hjac hle`. Introduce `x hx`.

Establish `h5 : (p : G.O) ^ Dd • x ∈ T` using `hN ⟨x, hx, rfl⟩`. Rewrite using `[pow_succ', mul_smul]`. Conclude with `T.smul_mem _ h5`.
-/
theorem ja_restJ (G : GAtP p) (t : Fin G.P.nV → ℕ) (B : Finset (Fin G.P.nV)) (Dd : ℕ)
    (κ : Fin G.P.nV → ℝ) (v0 : Fin G.P.nV) (h2 : G.FinClasses) (hE : JEquiv G) (hD : JDelta G)
    (hL : JLocal G t B Dd κ) (hR : JRank G) (hκ : ∀ v ∈ B, 0 ≤ κ v) :
    ∃ C : Finset G.Fn, (↑C : Set G.Fn) ⊆ latSys G t (vertexLabel B) ∧
      (C.card : ℝ) ≤ (∏ v ∈ B, κ v) * (G.dna : ℝ) ∧
      ∀ x ∈ latSys G t (vertexLabel B), (p : G.O) ^ (Dd + 1) • x ∈
        (⨆ v ∈ B, Submodule.span G.O
          (G.yv v '' (latSys G t (Function.update (vertexLabel B) v Slot.ball) : Set G.Fn))) ⊔
          Submodule.span G.O (↑C : Set G.Fn) := by
  classical
  obtain ⟨dadd, dsmul, dmem, -, -, -, ⟨reps, hreps⟩, ddec⟩ := hD
  have hL' : ∀ r : G.comp × G.P.Tup, ∃ C : Finset G.P.Xsp, G.P.IsLatTup r.2 →
      ((↑C : Set G.P.Xsp) ⊆ sysOf G t (vertexLabel B) r.2 ∧
      (C.card : ℝ) ≤ (∏ v ∈ B, κ v) * ((∏ v, dimV G.Kf (G.P.lam0 v) : ℕ) : ℝ) ∧
      ∀ ξ ∈ sysOf G t (vertexLabel B) r.2, ∃ g c, (p : G.O) ^ Dd • ξ = g + c ∧
        delta G r.1 r.2 g ∈ JBof G t B ⊔ sc G ((p : G.O) ^ (Dd + 1)) (MBof G t B) ∧
        c ∈ Submodule.span G.O (↑C : Set G.P.Xsp)) := by
    intro r
    by_cases h : G.P.IsLatTup r.2
    · obtain ⟨C, hC⟩ := hL r.1 r.2 h
      exact ⟨C, fun _ => hC⟩
    · exact ⟨∅, fun h' => absurd h' h⟩
  choose Cr hCr using hL'
  let dl : ∀ r : G.comp × G.P.Tup, G.P.Xsp →ₗ[G.O] G.Fn := fun r =>
    { toFun := delta G r.1 r.2, map_add' := dadd r.1 r.2, map_smul' := dsmul r.1 r.2 }
  set C : Finset G.Fn := reps.biUnion fun r => (Cr r).image (delta G r.1 r.2) with hCdef
  have hCM : (↑C : Set G.Fn) ⊆ latSys G t (vertexLabel B) := by
    intro z hz
    rw [hCdef, Finset.mem_coe, Finset.mem_biUnion] at hz
    obtain ⟨r, hr, hz⟩ := hz
    obtain ⟨c, hc, rfl⟩ := Finset.mem_image.1 hz
    exact dmem (sysOf G t (vertexLabel B)) (hE t _) r.1 r.2 (hreps.1 r hr) c ((hCr r (hreps.1 r hr)).1 hc)
  have hprod : 0 ≤ ∏ v ∈ B, κ v := Finset.prod_nonneg hκ
  have hcard : (C.card : ℝ) ≤ (∏ v ∈ B, κ v) * (G.dna : ℝ) := by
    have h1 : C.card ≤ ∑ r ∈ reps, (Cr r).card :=
      Finset.card_biUnion_le.trans (Finset.sum_le_sum fun r _ => Finset.card_image_le)
    calc (C.card : ℝ) ≤ ((∑ r ∈ reps, (Cr r).card : ℕ) : ℝ) := by exact_mod_cast h1
      _ = ∑ r ∈ reps, ((Cr r).card : ℝ) := by push_cast; rfl
      _ ≤ ∑ _r ∈ reps, (∏ v ∈ B, κ v) * ((∏ v, dimV G.Kf (G.P.lam0 v) : ℕ) : ℝ) :=
          Finset.sum_le_sum fun r hr => (hCr r (hreps.1 r hr)).2.1
      _ = (∏ v ∈ B, κ v) * ((reps.card * ∏ v, dimV G.Kf (G.P.lam0 v) : ℕ) : ℝ) := by
          rw [Finset.sum_const, nsmul_eq_mul]; push_cast; ring
      _ ≤ (∏ v ∈ B, κ v) * (G.dna : ℝ) :=
          mul_le_mul_of_nonneg_left (by exact_mod_cast hR reps hreps) hprod
  refine ⟨C, hCM, hcard, ?_⟩
  set T : Submodule G.O G.Fn := JBof G t B ⊔ Submodule.span G.O (↑C : Set G.Fn) with hT
  have key : ∀ x ∈ MBof G t B, (p : G.O) ^ Dd • x ∈ T ⊔ sc G ((p : G.O) ^ (Dd + 1)) (MBof G t B) := by
    intro x hx
    have hdec := ddec reps hreps (sysOf G t (vertexLabel B)) x hx
    rw [hdec, Finset.smul_sum]
    refine Submodule.sum_mem _ fun r hr => ?_
    obtain ⟨g, c, hgc, hg, hc⟩ := (hCr r (hreps.1 r hr)).2.2 (x r.1 r.2)
      (ja_val G _ hx r.1 r.2 (hreps.1 r hr))
    rw [← dsmul, hgc, dadd]
    refine Submodule.add_mem _ ?_ ?_
    · exact (sup_le_sup_right le_sup_left _ : JBof G t B ⊔ _ ≤ T ⊔ _) hg
    · apply Submodule.mem_sup_left
      apply Submodule.mem_sup_right
      have h3 : dl r c ∈ (Submodule.span G.O (↑(Cr r) : Set G.P.Xsp)).map (dl r) :=
        Submodule.mem_map_of_mem hc
      rw [Submodule.map_span] at h3
      refine Submodule.span_mono ?_ h3
      rintro _ ⟨c', hc', rfl⟩
      rw [hCdef, Finset.mem_coe, Finset.mem_biUnion]
      exact ⟨r, hr, Finset.mem_image_of_mem _ hc'⟩
  have hfin : Module.Finite G.O G.Mna := mna_finite G h2
  have hMBfg : (MBof G t B).FG :=
    (isNoetherian_submodule.mp (isNoetherian_of_fg_of_noetherian _ (Module.Finite.iff_fg.mp hfin)))
      _ (ja_MB_le G t B)
  have hNfg : (sc G ((p : G.O) ^ Dd) (MBof G t B)).FG := hMBfg.map _
  have hjac : Ideal.span {(p : G.O)} ≤ Ideal.jacobson ⊥ := by
    rw [IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top, Ideal.span_singleton_le_iff_mem,
      IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    exact ja_p_nonunit G v0
  have hle : sc G ((p : G.O) ^ Dd) (MBof G t B) ≤
      T ⊔ Ideal.span {(p : G.O)} • sc G ((p : G.O) ^ Dd) (MBof G t B) := by
    rintro _ ⟨x, hx, rfl⟩
    refine (sup_le_sup_left ?_ T : T ⊔ sc G ((p : G.O) ^ (Dd + 1)) (MBof G t B) ≤ _) (key x hx)
    rintro _ ⟨y, hy, rfl⟩
    have : (LinearMap.lsmul G.O G.Fn ((p : G.O) ^ (Dd + 1))) y = (p : G.O) • ((p : G.O) ^ Dd • y) := by
      simp only [LinearMap.lsmul_apply]
      rw [smul_smul, pow_succ']
    rw [this]
    exact Submodule.smul_mem_smul (Ideal.mem_span_singleton_self _) ⟨y, hy, rfl⟩
  have hN := Submodule.le_of_le_smul_of_le_jacobson_bot hNfg hjac hle
  intro x hx
  have h5 : (p : G.O) ^ Dd • x ∈ T := hN ⟨x, hx, rfl⟩
  rw [pow_succ', mul_smul]
  exact T.smul_mem _ h5

/- English proof (translation)
Introduce `h1 h2 VV t Dd cStar κ _ hLP B hB hBn`. Take `⟨v0, hv0⟩` from `hBn`. Conclude with `ja_restJ G t B Dd κ v0 h2 hE (hD h1 h2) (hL t B Dd cStar κ ⟨v0, hv0⟩ (hD h1 h2) h1 (fun v hv => hLP v (hB hv))) (hR v0 h2 (hD h1 h2)) (fun v hv => kappa_nonneg' G v (t v) Dd cStar (κ v) (hLP v (hB hv)))`.
-/
theorem restJAll_of (G : GAtP p) (hE : JEquiv G) (hD : G.TrivStab → G.FinClasses → JDelta G)
    (hR : Fin G.P.nV → G.FinClasses → JDelta G → JRank G)
    (hL : ∀ (t : Fin G.P.nV → ℕ) (B : Finset (Fin G.P.nV)) (Dd cStar : ℕ) (κ : Fin G.P.nV → ℝ), B.Nonempty →
      JDelta G → G.TrivStab →
      (∀ v ∈ B, LPprime (W := G.P.W v) (Qq := G.P.Qq v) (O := G.O) (Kf := G.Kf) p (G.P.n' v) (G.P.ι v) (G.P.σ v)
        G.P.w G.P.r (G.P.lam0 v) (t v) Dd (κ v) cStar) → JLocal G t B Dd κ) : RestJAll G := by
  intro h1 h2 VV t Dd cStar κ _ hLP B hB hBn
  obtain ⟨v0, hv0⟩ := hBn
  exact ja_restJ G t B Dd κ v0 h2 hE (hD h1 h2)
    (hL t B Dd cStar κ ⟨v0, hv0⟩ (hD h1 h2) h1 (fun v hv => hLP v (hB hv))) (hR v0 h2 (hD h1 h2))
    (fun v hv => kappa_nonneg' G v (t v) Dd cStar (κ v) (hLP v (hB hv)))

end Formalism.MainNotions.G.LatticeSystems

namespace Formalism.MainNotions.G.LatticeSystems

open Formalism.MainNotions.G Formalism.MainNotions.SelectionLemmas Formalism.G0

variable {p : ℕ}

/- English proof (translation)
The claim follows from `restJAll_of G (jEquiv G) (jDelta G) (fun v0 h2 hD => jRank G v0 h2 (jEquiv G) hD) (fun t B Dd cStar κ hB hD h1 hLP => jLocal G t B Dd cStar κ hB (hLP hB.choose hB.choose_spec).1 hD (jStep1 G h1 (jEquiv G) hD t B (Dd + 1)) (fun v hv => jSmith G v (t v) Dd cStar (κ v) (hLP v hv)) ( …`.
-/
theorem restJAll (G : GAtP p) : RestJAll G :=
  restJAll_of G (jEquiv G) (jDelta G) (fun v0 h2 hD => jRank G v0 h2 (jEquiv G) hD)
    (fun t B Dd cStar κ hB hD h1 hLP =>
      jLocal G t B Dd cStar κ hB (hLP hB.choose hB.choose_spec).1 hD
        (jStep1 G h1 (jEquiv G) hD t B (Dd + 1))
        (fun v hv => jSmith G v (t v) Dd cStar (κ v) (hLP v hv)) (jBase G))

/- English proof (translation)
The claim follows from `instance_of_lemma_J D G hA (restJAll G)`.
-/
theorem theta_kernel_expansion (D : Formalism.BasicNotions.D7) (G : GAtP p) (hA : admitted D G) : Conclusion1 D G :=
  instance_of_lemma_J D G hA (restJAll G)

end Formalism.MainNotions.G.LatticeSystems

namespace Formalism.MainNotions.G.LatticeSystems

open Formalism.MainNotions.G Formalism.MainNotions.SelectionLemmas

/- English proof (translation)
Introduce `p G hA` and use `instance_of_open_part D G hA (h p G)`.
-/
theorem stmt1Loc_of_rest1 (D : Formalism.BasicNotions.D7) (h : ∀ (p : ℕ) (G : GAtP p), RemainingCountingStatement G) : RationalPlaneProblemLocal D :=
  fun p G hA => instance_of_open_part D G hA (h p G)

/- English proof (translation)
Introduce `u w hh hA` and use `instance_of_open_part D _ hA (h u w hh)`.
-/
theorem problem_of_open_part_everywhere (D : Formalism.BasicNotions.D7)
    (h : ∀ (u : D.what₂.Word) (w : D.what₂.places.Pl)
      (hh : Formalism.BasicNotions.GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)), RemainingCountingStatement (D.gat u w hh)) : IntegralityFromMetric D :=
  fun u w hh hA => instance_of_open_part D _ hA (h u w hh)

/- English proof (translation)
Assemble the required witnesses or components as `⟨fun h => ⟨h.1, h.2.1⟩, fun h => ⟨h.1, h.2, exponent_condition_holds D G⟩⟩`.
-/
theorem admissibleModule_iff_lattice_quotients (D : Formalism.BasicNotions.D7) {p : ℕ} (G : GAtP p) : admitted D G ↔ adm1 D G ∧ adm2 D G :=
  ⟨fun h => ⟨h.1, h.2.1⟩, fun h => ⟨h.1, h.2, exponent_condition_holds D G⟩⟩

/- English proof (translation)
Introduce `p G hA` and use `instance_of_lemma_J D G hA (h p G)`.
-/
theorem stmt1Loc_of_J (D : Formalism.BasicNotions.D7) (h : ∀ (p : ℕ) (G : GAtP p), RestJAll G) : RationalPlaneProblemLocal D :=
  fun p G hA => instance_of_lemma_J D G hA (h p G)

/- English proof (translation)
Introduce `u w hh hA` and use `instance_of_lemma_J D _ hA (h u w hh)`.
-/
theorem problem_of_lemma_J_everywhere (D : Formalism.BasicNotions.D7)
    (h : ∀ (u : D.what₂.Word) (w : D.what₂.places.Pl)
      (hh : Formalism.BasicNotions.GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)), RestJAll (D.gat u w hh)) : IntegralityFromMetric D :=
  fun u w hh hA => instance_of_lemma_J D _ hA (h u w hh)

/- English proof (translation)
Introduce `_ G hA` and use `theta_kernel_expansion D G hA`.
-/
theorem stmt1Loc_proved (D : Formalism.BasicNotions.D7) : RationalPlaneProblemLocal D := fun _ G hA => theta_kernel_expansion D G hA

/- English proof (translation)
Introduce `_ _ _ hA` and use `theta_kernel_expansion D _ hA`.
-/
theorem problem_holds (D : Formalism.BasicNotions.D7) : IntegralityFromMetric D := fun _ _ _ hA => theta_kernel_expansion D _ hA

/- English proof (translation)
Introduce `_ _` and use `problem_holds _`.
-/
theorem problem_holds_family {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps) : FamilyGlobalDerivation Fm := fun _ _ => problem_holds _

end Formalism.MainNotions.G.LatticeSystems

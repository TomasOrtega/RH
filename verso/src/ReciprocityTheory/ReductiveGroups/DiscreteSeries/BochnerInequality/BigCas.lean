import ReciprocityTheory.ReductiveGroups.DiscreteSeries.BochnerInequality.BigRep
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.BochnerInequality.BigCasA

noncomputable section

open Finset

namespace ReciprocityTheory.ChartRestriction.DS

variable {n : ℕ}

section BigCas

variable {M : Type*} [NormedAddCommGroup M] [InnerProductSpace ℂ M] {ε : Fin n → Bool}
  {E : Fin n → Fin n → Module.End ℂ M} {V : Submodule ℂ M}

/- English proof (translation)
Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty => simp`. Consider the case `insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, PiLp.add_apply, ih]`.
-/
theorem bcas_sum_apply {k : ℕ} {ι : Type*} (s : Finset ι) (G : ι → Big n k M)
    (κ : Fin k → Fin n × Fin n) : (∑ i ∈ s, G i) κ = ∑ i ∈ s, G i κ := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, PiLp.add_apply, ih]

/- English proof (translation)
Establish `hc : ∀ (a b c d : Fin n) (i : Fin k), mAct E k a b * factorAd (M` using `M) k i c d = factorAd k i c d * mAct E k a b := by`. Introduce `a b c d i`. Use `LinearMap.ext fun F => PiLp.ext fun κ => ?_` and prove the remaining obligations. Simplify using `only [Module.End.mul_apply, mAct_apply, factorAd_apply]`. Apply the tactic sequence `split_ifs <;> simp`.

Establish `hswap : ∀ g : Fin n → Fin n → Module.End ℂ (Big n k M), ∑ a, ∑ b ∈ univ.filter (fun b => ε b = ε a), g b a = ∑ a, ∑ b ∈ univ.filter (fun b => ε b = ε a), g a b`. Introduce `g`. Simplify using `only [Finset.sum_filter]`. Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_` and prove the remaining obligations.

Break down `eq_or_ne (ε a) (ε b) with h | h` into its components or cases. Simplify using `[h]`. Simplify using `[h, h.symm]`. Establish `hX : ∑ a, ∑ b ∈ univ.filter (fun b => ε b = ε a), mAct E k a b * ∑ i, factorAd (M` using `M) k i b a = ∑ a, ∑ b ∈ univ.filter (fun b => ε b = ε a), (∑ i, factorAd (M := M) k i a b) * mAct E k b a := by`. Establish `h1` using `hswap (fun a b => (∑ i, factorAd (M := M) k i a b) * mAct E k b a)`.

Rewrite using `[← h1]`. Simplify using `only [Finset.mul_sum, Finset.sum_mul, hc]`. Establish `hY : ∑ a, ∑ b ∈ univ.filter (fun b => ε b = ε a), (∑ i, factorAd (M` using `M) k i a b) * mAct E k b a = ∑ i, ∑ a, ∑ b ∈ univ.filter (fun b => ε b = ε a), factorAd k i a b * mAct E k b a := by`. Simplify using `only [Finset.sum_mul]`. Use `conv_rhs => rw [Finset.sum_comm]`.

Use `Finset.sum_congr rfl fun a _ => ?_` and prove the remaining obligations. Conclude with `Finset.sum_comm`. Unfold `factorCasimir crossOp bAct casimirK`. Simplify using `only [add_mul, mul_add, Finset.sum_add_distrib]`. Rewrite using `[hX, hY, two_smul]`.

Normalize the expressions using the abelian group laws.
-/
theorem casimirK_bAct (k : ℕ) :
    casimirK ε (bAct E k) = factorCasimir ε k + casimirK ε (mAct E k) + 2 • ∑ i, crossOp ε E k i := by
  have hc : ∀ (a b c d : Fin n) (i : Fin k),
      mAct E k a b * factorAd (M := M) k i c d = factorAd k i c d * mAct E k a b := by
    intro a b c d i
    refine LinearMap.ext fun F => PiLp.ext fun κ => ?_
    simp only [Module.End.mul_apply, mAct_apply, factorAd_apply]
    split_ifs <;> simp
  have hswap : ∀ g : Fin n → Fin n → Module.End ℂ (Big n k M),
      ∑ a, ∑ b ∈ univ.filter (fun b => ε b = ε a), g b a =
        ∑ a, ∑ b ∈ univ.filter (fun b => ε b = ε a), g a b := by
    intro g
    simp only [Finset.sum_filter]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    rcases eq_or_ne (ε a) (ε b) with h | h
    · simp [h]
    · simp [h, h.symm]
  have hX : ∑ a, ∑ b ∈ univ.filter (fun b => ε b = ε a),
        mAct E k a b * ∑ i, factorAd (M := M) k i b a =
      ∑ a, ∑ b ∈ univ.filter (fun b => ε b = ε a),
        (∑ i, factorAd (M := M) k i a b) * mAct E k b a := by
    have h1 := hswap (fun a b => (∑ i, factorAd (M := M) k i a b) * mAct E k b a)
    rw [← h1]
    simp only [Finset.mul_sum, Finset.sum_mul, hc]
  have hY : ∑ a, ∑ b ∈ univ.filter (fun b => ε b = ε a),
        (∑ i, factorAd (M := M) k i a b) * mAct E k b a =
      ∑ i, ∑ a, ∑ b ∈ univ.filter (fun b => ε b = ε a), factorAd k i a b * mAct E k b a := by
    simp only [Finset.sum_mul]
    conv_rhs => rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ => ?_
    exact Finset.sum_comm
  unfold factorCasimir crossOp bAct casimirK
  simp only [add_mul, mul_add, Finset.sum_add_distrib]
  rw [hX, hY, two_smul]
  abel

/- English proof (translation)
Unfold `casimirK`. Simplify using `only [LinearMap.sum_apply, bcas_sum_apply, Module.End.mul_apply, mAct_apply]`.
-/
theorem casimirK_mAct_apply (k : ℕ) (F : Big n k M) (κ : Fin k → Fin n × Fin n) :
    casimirK ε (mAct E k) F κ = casimirK ε E (F κ) := by
  unfold casimirK
  simp only [LinearMap.sum_apply, bcas_sum_apply, Module.End.mul_apply, mAct_apply]

/- English proof (translation)
Establish `hz : ∀ x y : Fin n, ε x = ε y → F (fun _ => (x, y)) = 0`. Introduce `x y hxy`. Unfold `ncV at hF`. Establish `h` using `(Submodule.mem_iInf _).1 hF (fun _ => (x, y))`. Rewrite `h` using `[Submodule.mem_comap]`.

Establish `hc : ¬ ∀ j : Fin 1, ε ((fun _ : Fin 1 => (x, y)) j).1 ≠ ε ((fun _ : Fin 1 => (x, y)) j).2` using `fun hall => hall 0 hxy`. Rewrite `h` using `[if_neg hc, Submodule.mem_bot]`. Conclude with `h`. Establish `hupd : ∀ (κ : Fin 1 → Fin n × Fin n) (v : Fin n × Fin n), Function.update κ 0 v = fun _ => v`. Introduce `κ v`.

Use function extensionality and compare the values at `i`. Rewrite using `[Subsingleton.elim i 0, Function.update_self]`. Establish `hbool : ∀ x y w : Bool, x ≠ y → (y = w ↔ ¬ w = x)` using `by decide`. Use `PiLp.ext fun κ => ?_` and prove the remaining obligations. Take `⟨⟨p, q⟩, rfl⟩ : ∃ v, κ = fun _ => v` from `⟨κ 0, funext fun i => by rw [Subsingleton.elim i 0]⟩`.

Unfold `factorCasimir casimirK`. Simplify using `only [LinearMap.sum_apply, bcas_sum_apply, Module.End.mul_apply, Fin.sum_univ_one, factorAd_apply, hupd]`. Rewrite using `[PiLp.smul_apply]`. Distinguish the cases in `hpq : ε p = ε q`. Rewrite using `[hz p q hpq, smul_zero]`.

Use `Finset.sum_eq_zero fun a _ => Finset.sum_eq_zero fun b _ => ?_` and prove the remaining obligations. Distinguish the cases in `h1 : p = a`. Substitute `h1` using the available equality. Distinguish the cases in `h2 : q = b`. Substitute `h2` using the available equality.

Simplify using `[hz _ _ hpq, fun x => hz x x rfl]`. Simplify using `[h2, hz _ _ hpq, fun x => hz x x rfl]`. Distinguish the cases in `h2 : q = b`. Substitute `h2` using the available equality. Simplify using `[h1, hz _ _ hpq, fun x => hz x x rfl]`.

Simplify using `[h1, h2, fun x => hz x x rfl]`. Establish `hpq' : p ≠ q` using `fun h => hpq (h ▸ rfl) trans ∑ a, ∑ b ∈ univ.filter (fun b => ε b = ε a), ((if p = a then F (fun _ => (p, q)) else 0) + (if q = b then F (fun _ => (p, q)) else 0))`. Use `Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_` and prove the remaining obligations. Distinguish the cases in `h1 : p = a`. Substitute `h1` using the available equality.

Distinguish the cases in `h2 : q = b`. Substitute `h2` using the available equality. Simplify using `[hpq', Ne.symm hpq']`. Simplify using `[h2, hpq', Ne.symm hpq']`. Distinguish the cases in `h2 : q = b`.

Substitute `h2` using the available equality. Simplify using `[h1, hpq', Ne.symm hpq']`. Simplify using `[h1, h2]`. Simplify using `only [Finset.sum_add_distrib]`. Establish `h1 : ∑ a, ∑ b ∈ univ.filter (fun b => ε b = ε a), (if p = a then F (fun _ => (p, q)) else 0) = (univ.filter fun b => ε b = ε p).card • F (fun _ => (p, q))`.

Rewrite using `[Finset.sum_eq_single p (fun a _ ha => by simp [Ne.symm ha]) (by simp)]`. Simplify using the standard rewrite rules. Establish `h2 : ∑ a, ∑ b ∈ univ.filter (fun b => ε b = ε a), (if q = b then F (fun _ => (p, q)) else 0) = (univ.filter fun a => ε q = ε a).card • F (fun _ => (p, q))`. Simplify using `only [Finset.sum_ite_eq, Finset.mem_filter, Finset.mem_univ, true_and]`. Rewrite using `[← Finset.sum_filter, Finset.sum_const]`.

Establish `hcard : (univ.filter fun b => ε b = ε p).card + (univ.filter fun a => ε q = ε a).card = n`. Establish `hf : (univ.filter fun a => ε q = ε a) = univ.filter fun a => ¬ (ε a = ε p)` using `Finset.filter_congr fun a _ => hbool _ _ _ hpq`. Rewrite using `[hf]`. Use `first`. Consider the case `rw [Finset.filter_card_add_filter_neg_card_eq_card, Finset.card_univ, Fintype.card_fin]`.

Consider the case `rw [Finset.card_filter_add_card_filter_not, Finset.card_univ, Fintype.card_fin]`. Consider the case `rw [← Finset.card_union_of_disjoint (Finset.disjoint_filter_filter_neg _ _ _), Finset.filter_union_filter_neg_eq, Finset.card_univ, Fintype.card_fin]`. Consider the case `rw [← Finset.card_union_eq_card_add_card.2 (Finset.disjoint_filter_filter_neg _ _ _), Finset.filter_union_filter_neg_eq, Finset.card_univ, Fintype.card_fin]`. Rewrite using `[h1, h2, ← add_smul, hcard, Nat.cast_smul_eq_nsmul]`.
-/
theorem factorCasimir_ncV_one {F : Big n 1 M} (hF : F ∈ ncV ε V 1) :
    factorCasimir ε 1 F = (n : ℂ) • F := by
  classical
  have hz : ∀ x y : Fin n, ε x = ε y → F (fun _ => (x, y)) = 0 := by
    intro x y hxy
    unfold ncV at hF
    have h := (Submodule.mem_iInf _).1 hF (fun _ => (x, y))
    rw [Submodule.mem_comap] at h
    have hc : ¬ ∀ j : Fin 1, ε ((fun _ : Fin 1 => (x, y)) j).1 ≠ ε ((fun _ : Fin 1 => (x, y)) j).2 :=
      fun hall => hall 0 hxy
    rw [if_neg hc, Submodule.mem_bot] at h
    exact h
  have hupd : ∀ (κ : Fin 1 → Fin n × Fin n) (v : Fin n × Fin n),
      Function.update κ 0 v = fun _ => v := by
    intro κ v
    funext i
    rw [Subsingleton.elim i 0, Function.update_self]
  have hbool : ∀ x y w : Bool, x ≠ y → (y = w ↔ ¬ w = x) := by decide
  refine PiLp.ext fun κ => ?_
  obtain ⟨⟨p, q⟩, rfl⟩ : ∃ v, κ = fun _ => v :=
    ⟨κ 0, funext fun i => by rw [Subsingleton.elim i 0]⟩
  unfold factorCasimir casimirK
  simp only [LinearMap.sum_apply, bcas_sum_apply, Module.End.mul_apply, Fin.sum_univ_one,
    factorAd_apply, hupd]
  rw [PiLp.smul_apply]
  by_cases hpq : ε p = ε q
  · rw [hz p q hpq, smul_zero]
    refine Finset.sum_eq_zero fun a _ => Finset.sum_eq_zero fun b _ => ?_
    by_cases h1 : p = a
    · subst h1
      by_cases h2 : q = b
      · subst h2
        simp [hz _ _ hpq, fun x => hz x x rfl]
      · simp [h2, hz _ _ hpq, fun x => hz x x rfl]
    · by_cases h2 : q = b
      · subst h2
        simp [h1, hz _ _ hpq, fun x => hz x x rfl]
      · simp [h1, h2, fun x => hz x x rfl]
  · have hpq' : p ≠ q := fun h => hpq (h ▸ rfl)
    trans ∑ a, ∑ b ∈ univ.filter (fun b => ε b = ε a),
      ((if p = a then F (fun _ => (p, q)) else 0) + (if q = b then F (fun _ => (p, q)) else 0))
    · refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
      by_cases h1 : p = a
      · subst h1
        by_cases h2 : q = b
        · subst h2
          simp [hpq', Ne.symm hpq']
        · simp [h2, hpq', Ne.symm hpq']
      · by_cases h2 : q = b
        · subst h2
          simp [h1, hpq', Ne.symm hpq']
        · simp [h1, h2]
    · simp only [Finset.sum_add_distrib]
      have h1 : ∑ a, ∑ b ∈ univ.filter (fun b => ε b = ε a),
          (if p = a then F (fun _ => (p, q)) else 0) =
          (univ.filter fun b => ε b = ε p).card • F (fun _ => (p, q)) := by
        rw [Finset.sum_eq_single p (fun a _ ha => by simp [Ne.symm ha]) (by simp)]
        simp
      have h2 : ∑ a, ∑ b ∈ univ.filter (fun b => ε b = ε a),
          (if q = b then F (fun _ => (p, q)) else 0) =
          (univ.filter fun a => ε q = ε a).card • F (fun _ => (p, q)) := by
        simp only [Finset.sum_ite_eq, Finset.mem_filter, Finset.mem_univ, true_and]
        rw [← Finset.sum_filter, Finset.sum_const]
      have hcard : (univ.filter fun b => ε b = ε p).card + (univ.filter fun a => ε q = ε a).card
          = n := by
        have hf : (univ.filter fun a => ε q = ε a) = univ.filter fun a => ¬ (ε a = ε p) :=
          Finset.filter_congr fun a _ => hbool _ _ _ hpq
        rw [hf]
        first
          | rw [Finset.filter_card_add_filter_neg_card_eq_card, Finset.card_univ, Fintype.card_fin]
          | rw [Finset.card_filter_add_card_filter_not, Finset.card_univ, Fintype.card_fin]
          | rw [← Finset.card_union_of_disjoint (Finset.disjoint_filter_filter_neg _ _ _),
              Finset.filter_union_filter_neg_eq, Finset.card_univ, Fintype.card_fin]
          | rw [← Finset.card_union_eq_card_add_card.2 (Finset.disjoint_filter_filter_neg _ _ _),
              Finset.filter_union_filter_neg_eq, Finset.card_univ, Fintype.card_fin]
      rw [h1, h2, ← add_smul, hcard, Nat.cast_smul_eq_nsmul]

/- English proof (translation)
Establish `hadj : ∀ (a b : Fin n) (X Y : Big n k M), inner ℂ ((∑ i, factorAd (M` using `M) k i a b) X) Y = inner ℂ X ((∑ i, factorAd (M := M) k i b a) Y) := by`. Introduce `a b X Y`. Simplify using `only [LinearMap.sum_apply, sum_inner, inner_sum, factorAd_adjoint]`. Unfold `factorCasimir casimirK`. Use `beta_reduce`.

Rewrite using `[LinearMap.sum_apply, sum_inner, map_sum]`. Use `Finset.sum_nonneg fun a _ => ?_` and prove the remaining obligations. Rewrite using `[LinearMap.sum_apply, sum_inner, map_sum]`. Use `Finset.sum_nonneg fun b _ => ?_` and prove the remaining obligations. Rewrite using `[Module.End.mul_apply, hadj]`.

Conclude with `inner_self_nonneg`.
-/
theorem factorCasimir_nonneg (k : ℕ) (F : Big n k M) :
    0 ≤ RCLike.re (inner ℂ (factorCasimir (M := M) ε k F) F) := by
  have hadj : ∀ (a b : Fin n) (X Y : Big n k M),
      inner ℂ ((∑ i, factorAd (M := M) k i a b) X) Y =
        inner ℂ X ((∑ i, factorAd (M := M) k i b a) Y) := by
    intro a b X Y
    simp only [LinearMap.sum_apply, sum_inner, inner_sum, factorAd_adjoint]
  unfold factorCasimir casimirK
  beta_reduce
  rw [LinearMap.sum_apply, sum_inner, map_sum]
  refine Finset.sum_nonneg fun a _ => ?_
  rw [LinearMap.sum_apply, sum_inner, map_sum]
  refine Finset.sum_nonneg fun b _ => ?_
  rw [Module.End.mul_apply, hadj]
  exact inner_self_nonneg

/- English proof (translation)
Establish `hU' : ∀ (a b : Fin n) (x y : M), inner ℂ (E a b x) y = adjSign ε a b * inner ℂ x (E b a y)` using `hU`. Establish `hm : ∀ (a b : Fin n) (X Y : Big n k M), inner ℂ (mAct E k a b X) Y = adjSign ε a b * inner ℂ X (mAct E k b a Y)`. Introduce `a b X Y`. Simplify using `only [PiLp.inner_apply, mAct_apply, hU', Finset.mul_sum]`. Establish `hc : ∀ (a b c d : Fin n), mAct E k a b * factorAd (M` using `M) k i c d = factorAd k i c d * mAct E k a b := by`.

Introduce `a b c d`. Use `LinearMap.ext fun F => PiLp.ext fun κ => ?_` and prove the remaining obligations. Simplify using `only [Module.End.mul_apply, mAct_apply, factorAd_apply]`. Apply the tactic sequence `split_ifs <;> simp`. Establish `hswap : ∀ g : Fin n → Fin n → ℂ, ∑ a, ∑ b ∈ univ.filter (fun b => ε b = ε a), g b a = ∑ a, ∑ b ∈ univ.filter (fun b => ε b = ε a), g a b`.

Introduce `g`. Simplify using `only [Finset.sum_filter]`. Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_` and prove the remaining obligations. Break down `eq_or_ne (ε a) (ε b) with h | h` into its components or cases.

Simplify using `[h]`. Simplify using `[h, h.symm]`. Unfold `crossOp`. Simplify using `only [LinearMap.sum_apply, sum_inner, inner_sum, Module.End.mul_apply]`. Establish `h1` using `hswap (fun a b => inner ℂ F (factorAd k i a b (mAct E k b a G)))`.

Rewrite using `[← h1]`. Use `Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b hb => ?_` and prove the remaining obligations. Establish `hab : ε b = ε a` using `(Finset.mem_filter.1 hb).2`. Rewrite using `[factorAd_adjoint, hm, show adjSign ε b a = 1 by simp [adjSign, hab], one_mul]`. Use `congr 1`.

Conclude with `LinearMap.congr_fun (hc a b b a) G`.
-/
theorem crossOp_symm (hU : IsInfUnitary ε E) (k : ℕ) (i : Fin k) (F G : Big n k M) :
    inner ℂ (crossOp ε E k i F) G = inner ℂ F (crossOp ε E k i G) := by
  have hU' : ∀ (a b : Fin n) (x y : M),
      inner ℂ (E a b x) y = adjSign ε a b * inner ℂ x (E b a y) := hU
  have hm : ∀ (a b : Fin n) (X Y : Big n k M),
      inner ℂ (mAct E k a b X) Y = adjSign ε a b * inner ℂ X (mAct E k b a Y) := by
    intro a b X Y
    simp only [PiLp.inner_apply, mAct_apply, hU', Finset.mul_sum]
  have hc : ∀ (a b c d : Fin n),
      mAct E k a b * factorAd (M := M) k i c d = factorAd k i c d * mAct E k a b := by
    intro a b c d
    refine LinearMap.ext fun F => PiLp.ext fun κ => ?_
    simp only [Module.End.mul_apply, mAct_apply, factorAd_apply]
    split_ifs <;> simp
  have hswap : ∀ g : Fin n → Fin n → ℂ,
      ∑ a, ∑ b ∈ univ.filter (fun b => ε b = ε a), g b a =
        ∑ a, ∑ b ∈ univ.filter (fun b => ε b = ε a), g a b := by
    intro g
    simp only [Finset.sum_filter]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    rcases eq_or_ne (ε a) (ε b) with h | h
    · simp [h]
    · simp [h, h.symm]
  unfold crossOp
  simp only [LinearMap.sum_apply, sum_inner, inner_sum, Module.End.mul_apply]
  have h1 := hswap (fun a b => inner ℂ F (factorAd k i a b (mAct E k b a G)))
  rw [← h1]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b hb => ?_
  have hab : ε b = ε a := (Finset.mem_filter.1 hb).2
  rw [factorAd_adjoint, hm, show adjSign ε b a = 1 by simp [adjSign, hab], one_mul]
  congr 1
  exact LinearMap.congr_fun (hc a b b a) G

/- English proof (translation)
Establish `hmrel : ∀ a b c d : Fin n, mAct E k a b * mAct E k c d - mAct E k c d * mAct E k a b = (if b = c then mAct E k a d else 0) - (if d = a then mAct E k c b else 0)`. Introduce `a b c d`. Use `LinearMap.ext fun F => PiLp.ext fun κ => ?_` and prove the remaining obligations. Establish `h` using `LinearMap.congr_fun (hE a b c d) (F κ)`. Simplify using `only [LinearMap.sub_apply, Module.End.mul_apply] at h`.

Simplify using `only [LinearMap.sub_apply, Module.End.mul_apply, PiLp.sub_apply, mAct_apply]`. Rewrite using `[h]`. Apply the tactic sequence `split_ifs <;> simp [mAct_apply]`. Establish `hterm : ∀ c d : Fin n, (mAct E k a b + factorAd k i a b) * (factorAd k i c d * mAct E k d c) - (factorAd k i c d * mAct E k d c) * (mAct E k a b + factorAd k i a b) = factorAd k i c d * (mAct E k a b * mAct E k d c - mAct E k d c * mAct E k a b) + (factorAd k i a b * factorAd k i …`. Introduce `c d`.

Establish `h1` using `mAct_factorAd_comm (E := E) k i a b c d`. Establish `h2` using `mAct_factorAd_comm (E := E) k i d c a b`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[h1, h2]`. Use `noncomm_ring`.

Establish `key : ∑ c, ∑ d ∈ univ.filter (fun d => ε d = ε c), (factorAd k i c d * ((if b = d then mAct E k a c else 0) - (if c = a then mAct E k d b else 0)) + ((if b = c then factorAd k i a d else 0) - (if d = a then factorAd k i c b else 0)) * mAct E k d c) = 0`. Simplify using `[mul_sub, sub_mul, mul_ite, ite_mul, Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.sum_ite_irrel, hab]`. Establish `hmain : (mAct E k a b + factorAd k i a b) * crossOp ε E k i - crossOp ε E k i * (mAct E k a b + factorAd k i a b) = 0`. Unfold `crossOp`. Rewrite using `[Finset.mul_sum, Finset.sum_mul, ← Finset.sum_sub_distrib]`.

Rewrite using `[← key]`. Use `Finset.sum_congr rfl fun c _ => ?_` and prove the remaining obligations. Rewrite using `[Finset.mul_sum, Finset.sum_mul, ← Finset.sum_sub_distrib]`. Use `Finset.sum_congr rfl fun d _ => ?_` and prove the remaining obligations. Rewrite using `[hterm, hmrel, factorAd_commutator]`.

Establish `hother : ∀ j ∈ univ.erase i, factorAd (M` using `M) k j a b * crossOp ε E k i = crossOp ε E k i * factorAd k j a b := by`. Introduce `j hj`. Establish `hji : j ≠ i` using `Finset.ne_of_mem_erase hj`. Unfold `crossOp`. Rewrite using `[Finset.mul_sum, Finset.sum_mul]`.

Use `Finset.sum_congr rfl fun c _ => ?_` and prove the remaining obligations. Rewrite using `[Finset.mul_sum, Finset.sum_mul]`. Use `Finset.sum_congr rfl fun d _ => ?_` and prove the remaining obligations. Rewrite using `[← mul_assoc, factorAd_comm_of_ne k hji, mul_assoc, ← mAct_factorAd_comm (E := E) k j d c a b, ← mul_assoc]`. Establish `hsum : (∑ j ∈ univ.erase i, factorAd (M` using `M) k j a b) * crossOp ε E k i = crossOp ε E k i * ∑ j ∈ univ.erase i, factorAd k j a b := by`.

Rewrite using `[Finset.sum_mul, Finset.mul_sum]`. Conclude with `Finset.sum_congr rfl hother`. Establish `hsplit : bAct E k a b = (mAct E k a b + factorAd k i a b) + ∑ j ∈ univ.erase i, factorAd (M` using `M) k j a b := by`. Unfold `bAct`. Rewrite using `[← Finset.add_sum_erase _ _ (Finset.mem_univ i)]`.

Normalize the expressions using the abelian group laws. Rewrite using `[hsplit, mul_add, add_mul, ← hsum]`. Establish `h` using `sub_eq_zero.1 hmain`. Rewrite using `[h]`.
-/
theorem crossOp_comm (hE : IsGlRep E) (k : ℕ) (i : Fin k) {a b : Fin n} (hab : ε a = ε b) :
    crossOp ε E k i * bAct E k a b = bAct E k a b * crossOp ε E k i := by
  classical
  have hmrel : ∀ a b c d : Fin n, mAct E k a b * mAct E k c d - mAct E k c d * mAct E k a b =
      (if b = c then mAct E k a d else 0) - (if d = a then mAct E k c b else 0) := by
    intro a b c d
    refine LinearMap.ext fun F => PiLp.ext fun κ => ?_
    have h := LinearMap.congr_fun (hE a b c d) (F κ)
    simp only [LinearMap.sub_apply, Module.End.mul_apply] at h
    simp only [LinearMap.sub_apply, Module.End.mul_apply, PiLp.sub_apply, mAct_apply]
    rw [h]
    split_ifs <;> simp [mAct_apply]
  have hterm : ∀ c d : Fin n,
      (mAct E k a b + factorAd k i a b) * (factorAd k i c d * mAct E k d c) -
        (factorAd k i c d * mAct E k d c) * (mAct E k a b + factorAd k i a b) =
      factorAd k i c d * (mAct E k a b * mAct E k d c - mAct E k d c * mAct E k a b) +
        (factorAd k i a b * factorAd k i c d - factorAd k i c d * factorAd k i a b) * mAct E k d c := by
    intro c d
    have h1 := mAct_factorAd_comm (E := E) k i a b c d
    have h2 := mAct_factorAd_comm (E := E) k i d c a b
    calc _ = mAct E k a b * factorAd k i c d * mAct E k d c +
          factorAd k i a b * factorAd k i c d * mAct E k d c -
          factorAd k i c d * mAct E k d c * mAct E k a b -
          factorAd k i c d * (mAct E k d c * factorAd k i a b) := by noncomm_ring
      _ = _ := by
        rw [h1, h2]
        noncomm_ring
  have key : ∑ c, ∑ d ∈ univ.filter (fun d => ε d = ε c),
      (factorAd k i c d * ((if b = d then mAct E k a c else 0) - (if c = a then mAct E k d b else 0)) +
        ((if b = c then factorAd k i a d else 0) - (if d = a then factorAd k i c b else 0)) *
          mAct E k d c) = 0 := by
    simp [mul_sub, sub_mul, mul_ite, ite_mul, Finset.sum_add_distrib, Finset.sum_sub_distrib,
      Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.sum_ite_irrel, hab]
  have hmain : (mAct E k a b + factorAd k i a b) * crossOp ε E k i -
      crossOp ε E k i * (mAct E k a b + factorAd k i a b) = 0 := by
    unfold crossOp
    rw [Finset.mul_sum, Finset.sum_mul, ← Finset.sum_sub_distrib]
    rw [← key]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [Finset.mul_sum, Finset.sum_mul, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun d _ => ?_
    rw [hterm, hmrel, factorAd_commutator]
  have hother : ∀ j ∈ univ.erase i,
      factorAd (M := M) k j a b * crossOp ε E k i = crossOp ε E k i * factorAd k j a b := by
    intro j hj
    have hji : j ≠ i := Finset.ne_of_mem_erase hj
    unfold crossOp
    rw [Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun d _ => ?_
    rw [← mul_assoc, factorAd_comm_of_ne k hji, mul_assoc, ← mAct_factorAd_comm (E := E) k j d c a b,
      ← mul_assoc]
  have hsum : (∑ j ∈ univ.erase i, factorAd (M := M) k j a b) * crossOp ε E k i =
      crossOp ε E k i * ∑ j ∈ univ.erase i, factorAd k j a b := by
    rw [Finset.sum_mul, Finset.mul_sum]
    exact Finset.sum_congr rfl hother
  have hsplit : bAct E k a b =
      (mAct E k a b + factorAd k i a b) + ∑ j ∈ univ.erase i, factorAd (M := M) k j a b := by
    unfold bAct
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i)]
    abel
  rw [hsplit, mul_add, add_mul, ← hsum]
  have h := sub_eq_zero.1 hmain
  rw [h]

/- English proof (translation)
Establish `hmem : ∀ G : Big n k M, G ∈ ncV ε V k ↔ ∀ κ, G κ ∈ (if ∀ j, ε (κ j).1 ≠ ε (κ j).2 then V else ⊥)`. Introduce `G`. Unfold `ncV`. Simplify using `only [Submodule.mem_iInf, Submodule.mem_comap]`. Conclude with `Iff.rfl`.

Rewrite `hF`, the goal using `[hmem]`. Introduce `κ`. Establish `hc : ∀ p : Fin n × Fin n, ε p.1 = ε (κ i).1 → ε p.2 = ε (κ i).2 → ((∀ j, ε ((Function.update κ i p) j).1 ≠ ε ((Function.update κ i p) j).2) ↔ ∀ j, ε (κ j).1 ≠ ε (κ j).2)`. Introduce `p h1 h2`. Use `forall_congr' fun j => ?_` and prove the remaining obligations.

Distinguish the cases in `hj : j = i`. Substitute `hj` using the available equality. Simplify using `[Function.update_apply, h1, h2]`. Simplify using `[Function.update_apply, hj]`. Establish `hval : (crossOp ε E k i F) κ = ∑ a, ∑ b ∈ univ.filter (fun b => ε b = ε a), ((if (κ i).1 = a then E b a (F (Function.update κ i (b, (κ i).2))) else 0) - (if (κ i).2 = b then E b a (F (Function.update κ i ((κ i).1, a))) else 0))`.

Unfold `crossOp`. Simplify using `only [LinearMap.sum_apply, bcas_sum_apply, Module.End.mul_apply, factorAd_apply, mAct_apply]`. Rewrite using `[hval]`. Use `Submodule.sum_mem _ fun a _ => Submodule.sum_mem _ fun b hb => ?_` and prove the remaining obligations. Establish `hab : ε b = ε a` using `(Finset.mem_filter.1 hb).2`.

Establish `hT : ∀ v ∈ (if (∀ j, ε (κ j).1 ≠ ε (κ j).2) then V else (⊥ : Submodule ℂ M)), E b a v ∈ (if (∀ j, ε (κ j).1 ≠ ε (κ j).2) then V else (⊥ : Submodule ℂ M))`. Introduce `v hv`. Use `split_ifs at hv ⊢ with hcκ`. Conclude with `hV b a hab v hv`. Rewrite `hv`, the goal using `[Submodule.mem_bot]`.

Rewrite using `[hv, map_zero]`. Use `Submodule.sub_mem _ ?_ ?_` and prove the remaining obligations. Distinguish the cases in `h1 : (κ i).1 = a`. Rewrite using `[if_pos h1]`. Use `hT _ ?_` and prove the remaining obligations.

Establish `hFκ` using `hF (Function.update κ i (b, (κ i).2))`. Rewrite `hFκ` using `[if_congr (hc (b, (κ i).2) (by show ε b = ε (κ i).1; rw [hab, h1]) rfl) rfl rfl]`. Then use the resulting hypothesis. Rewrite using `[if_neg h1]`. Conclude with `Submodule.zero_mem _`. Distinguish the cases in `h2 : (κ i).2 = b`.

Rewrite using `[if_pos h2]`. Use `hT _ ?_` and prove the remaining obligations. Establish `hFκ` using `hF (Function.update κ i ((κ i).1, a))`. Rewrite `hFκ` using `[if_congr (hc ((κ i).1, a) rfl (by show ε a = ε (κ i).2; rw [h2, hab])) rfl rfl]`. Then use the resulting hypothesis. Rewrite using `[if_neg h2]`.

Conclude with `Submodule.zero_mem _`.
-/
theorem crossOp_mem_ncV (hV : IsKStableSub ε E V) (k : ℕ) (i : Fin k) {F : Big n k M}
    (hF : F ∈ ncV ε V k) : crossOp ε E k i F ∈ ncV ε V k := by
  classical
  have hmem : ∀ G : Big n k M, G ∈ ncV ε V k ↔
      ∀ κ, G κ ∈ (if ∀ j, ε (κ j).1 ≠ ε (κ j).2 then V else ⊥) := by
    intro G
    unfold ncV
    simp only [Submodule.mem_iInf, Submodule.mem_comap]
    exact Iff.rfl
  rw [hmem] at hF ⊢
  intro κ
  have hc : ∀ p : Fin n × Fin n, ε p.1 = ε (κ i).1 → ε p.2 = ε (κ i).2 →
      ((∀ j, ε ((Function.update κ i p) j).1 ≠ ε ((Function.update κ i p) j).2) ↔
        ∀ j, ε (κ j).1 ≠ ε (κ j).2) := by
    intro p h1 h2
    refine forall_congr' fun j => ?_
    by_cases hj : j = i
    · subst hj
      simp [Function.update_apply, h1, h2]
    · simp [Function.update_apply, hj]
  have hval : (crossOp ε E k i F) κ = ∑ a, ∑ b ∈ univ.filter (fun b => ε b = ε a),
      ((if (κ i).1 = a then E b a (F (Function.update κ i (b, (κ i).2))) else 0) -
        (if (κ i).2 = b then E b a (F (Function.update κ i ((κ i).1, a))) else 0)) := by
    unfold crossOp
    simp only [LinearMap.sum_apply, bcas_sum_apply, Module.End.mul_apply, factorAd_apply,
      mAct_apply]
  rw [hval]
  refine Submodule.sum_mem _ fun a _ => Submodule.sum_mem _ fun b hb => ?_
  have hab : ε b = ε a := (Finset.mem_filter.1 hb).2
  have hT : ∀ v ∈ (if (∀ j, ε (κ j).1 ≠ ε (κ j).2) then V else (⊥ : Submodule ℂ M)),
      E b a v ∈ (if (∀ j, ε (κ j).1 ≠ ε (κ j).2) then V else (⊥ : Submodule ℂ M)) := by
    intro v hv
    split_ifs at hv ⊢ with hcκ
    · exact hV b a hab v hv
    · rw [Submodule.mem_bot] at hv ⊢
      rw [hv, map_zero]
  refine Submodule.sub_mem _ ?_ ?_
  · by_cases h1 : (κ i).1 = a
    · rw [if_pos h1]
      refine hT _ ?_
      have hFκ := hF (Function.update κ i (b, (κ i).2))
      rwa [if_congr (hc (b, (κ i).2) (by show ε b = ε (κ i).1; rw [hab, h1]) rfl) rfl rfl]
        at hFκ
    · rw [if_neg h1]
      exact Submodule.zero_mem _
  · by_cases h2 : (κ i).2 = b
    · rw [if_pos h2]
      refine hT _ ?_
      have hFκ := hF (Function.update κ i ((κ i).1, a))
      rwa [if_congr (hc ((κ i).1, a) rfl (by show ε a = ε (κ i).2; rw [h2, hab])) rfl rfl]
        at hFκ
    · rw [if_neg h2]
      exact Submodule.zero_mem _

end BigCas

end ReciprocityTheory.ChartRestriction.DS

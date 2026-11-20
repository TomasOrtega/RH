import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.InstAddCommGroupTwo
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsLocallyConstantOrbit

noncomputable section

open GlobalTheory GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.SmGL.Exponents GlobalTheory.IwahoriInj ValuativeRel

namespace GlobalTheory.JacInj

section Abstract

variable {G V W : Type} [Group G] [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
  {π₁ : Representation ℂ G V} {π : Representation ℂ G W}

/- English proof (translation)
Establish `h` using `LinearMap.congr_fun (f.isIntertwining' g) v`. Simplify using `using h`.
-/
theorem map_apply' (f : π₁.IntertwiningMap π) (g : G) (v : V) : f (π₁ g v) = π g (f v) := by
  have h := LinearMap.congr_fun (f.isIntertwining' g) v
  simpa using h

/- English proof (translation)
Establish `hle : twKer π₁ H 1 ≤ (twKer π H 1).comap f.toLinearMap`. Use `Submodule.span_le.2 ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨h, w, rfl⟩`. Simplify using `only [SetLike.mem_coe, Submodule.mem_comap, map_sub, map_smul]`. Use `Submodule.subset_span ⟨h, f w, ?_⟩` and prove the remaining obligations.

Simplify using `[map_apply']`. Conclude with `hle hv`.
-/
theorem map_mem_twKer (f : π₁.IntertwiningMap π) {H : Subgroup G} {v : V} (hv : v ∈ twKer π₁ H 1) :
    f v ∈ twKer π H 1 := by
  have hle : twKer π₁ H 1 ≤ (twKer π H 1).comap f.toLinearMap := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨h, w, rfl⟩
    simp only [SetLike.mem_coe, Submodule.mem_comap, map_sub, map_smul]
    refine Submodule.subset_span ⟨h, f w, ?_⟩
    simp [map_apply']
  exact hle hv

variable [TopologicalSpace G] [IsTopologicalGroup G]

/- English proof (translation)
Establish `h₁ : IsSmooth π₁`. Introduce `w`. Establish `hset : {g : G | π₁ g w = w} = {g : G | π g (f w) = f w}`. Use extensionality with `g`. Simplify using `only [Set.mem_ofPred_eq, ← map_apply' f g w]`.

Conclude with `hf.eq_iff.symm`. Rewrite using `[hset]`. Conclude with `hπ (f w)`. Take `⟨U, -, hU, hUv⟩` from `GlobalTheory.LocGL.exists_normal_fix h₁ hH v`. Use `letI : Fintype (H ⧸ U) := U.fintypeQuotientOfFiniteIndex`.

Establish `hUf : ∀ u ∈ U, π (u : H) (f v) = f v` using `fun u hu => by rw [← map_apply', hUv u hu]`. Rewrite using `[← GlobalTheory.LocGL.idem_eq_zero_iff h₁ hH]`. Apply `hf` to reduce the goal to its premises. Rewrite using `[map_zero, GlobalTheory.LocGL.idem_eq_cosetSum h₁ hH U hUv, map_smul, map_sum]`. Simplify using `only [map_apply']`.

Rewrite using `[← GlobalTheory.LocGL.idem_eq_cosetSum hπ hH U hUf]`. Conclude with `(GlobalTheory.LocGL.idem_eq_zero_iff hπ hH).2 hv`.
-/
theorem mem_twKer_of_map (f : π₁.IntertwiningMap π) (hπ : IsSmooth π) (hf : Function.Injective f)
    {H : Subgroup G} (hH : IsCompact (H : Set G)) {v : V} (hv : f v ∈ twKer π H 1) :
    v ∈ twKer π₁ H 1 := by
  have h₁ : IsSmooth π₁ := by
    intro w
    have hset : {g : G | π₁ g w = w} = {g : G | π g (f w) = f w} := by
      ext g
      simp only [Set.mem_ofPred_eq, ← map_apply' f g w]
      exact hf.eq_iff.symm
    rw [hset]
    exact hπ (f w)
  obtain ⟨U, -, hU, hUv⟩ := GlobalTheory.LocGL.exists_normal_fix h₁ hH v
  letI : Fintype (H ⧸ U) := U.fintypeQuotientOfFiniteIndex
  have hUf : ∀ u ∈ U, π (u : H) (f v) = f v := fun u hu => by rw [← map_apply', hUv u hu]
  rw [← GlobalTheory.LocGL.idem_eq_zero_iff h₁ hH]
  apply hf
  rw [map_zero, GlobalTheory.LocGL.idem_eq_cosetSum h₁ hH U hUv, map_smul, map_sum]
  simp only [map_apply']
  rw [← GlobalTheory.LocGL.idem_eq_cosetSum hπ hH U hUf]
  exact (GlobalTheory.LocGL.idem_eq_zero_iff hπ hH).2 hv

end Abstract

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {α n : Type} {m : α → Type} [Fintype α] [LinearOrder α] [∀ a, Fintype (m a)]
  [∀ a, DecidableEq (m a)] [Fintype n] [DecidableEq n]

def wt (e : (Σ a, m a) ≃ n) (M : ℕ) (i j : n) : ℤ :=
  M * (((Finset.univ.filter (· < blk e i)).card : ℤ) - (Finset.univ.filter (· < blk e j)).card)

/- English proof (translation)
Unfold `GlobalTheory.IwahoriInj.Conc`. Use `⟨fun i => by simp [wt], fun i j l => le_of_eq ?_⟩` and prove the remaining obligations. Simplify using `only [wt]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem conc_wt (e : (Σ a, m a) ≃ n) (M : ℕ) : Conc (wt e M) := by
  unfold GlobalTheory.IwahoriInj.Conc
  refine ⟨fun i => by simp [wt], fun i j l => le_of_eq ?_⟩
  simp only [wt]
  ring

/- English proof (translation)
Take `⟨hP, hD⟩` from `mem_unipRad.1 hg`. Rewrite `hP` using `[mem_parab]`. Establish `hmono : ∀ a b : ℤ, a ≤ b → uniformizer k ^ b ≤ uniformizer k ^ a`. Introduce `a b hab`. Conclude with `zpow_le_zpow_right_of_le_one₀ uniformizer_pos uniformizer_lt_one.le hab`.

Break down `lt_trichotomy (blk e i) (blk e j) with h | h | h` into its components or cases. Take `⟨N, hN⟩` from `MulArchimedean.arch (valuation k ((g : Matrix n n k) i j)) ((one_lt_inv₀ uniformizer_pos).2 uniformizer_lt_one)`. Establish `hss : Finset.univ.filter (· < blk e i) ⊂ Finset.univ.filter (· < blk e j)`. Use `(Finset.ssubset_iff_of_subset (fun x hx => ?_)).2 ⟨blk e i, ?_, ?_⟩` and prove the remaining obligations. Simplify using `only [Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢`.

Conclude with `hx.trans h`. Simplify using `[h]`. Simplify using the standard rewrite rules. Establish `hlt` using `Finset.card_lt_card hss`. Use `filter_upwards [Filter.eventually_ge_atTop N] with M hM`.

Establish `hM' : (N : ℤ) ≤ M` using `by exact_mod_cast hM`. Establish `hd : ((Finset.univ.filter (· < blk e i)).card : ℤ) - (Finset.univ.filter (· < blk e j)).card ≤ -1` using `by omega`. Establish `hw : wt e M i j ≤ -(N : ℤ)`. Simplify using `only [wt]`. Use the polynomial consequences of the given equalities and inequalities.

Use `hN.trans (le_trans (le_of_eq ?_) (hmono _ _ hw))` and prove the remaining obligations. Rewrite using `[zpow_neg, zpow_natCast, inv_pow]`. Use `Filter.Eventually.of_forall fun M => ?_` and prove the remaining obligations. Establish `hw : wt e M i j = 0` using `by simp [wt, h]`. Rewrite using `[hw, zpow_zero]`.

Take `⟨⟨a, i'⟩, rfl⟩` from `e.surjective i`. Take `⟨⟨b, j'⟩, rfl⟩` from `e.surjective j`. Simplify using `only [blk_apply] at h`. Consider the cases of `h`. Rewrite using `[hD _ i' j', Matrix.one_apply]`.

Apply the tactic sequence `split_ifs <;> simp`. Conclude with `Filter.Eventually.of_forall fun M => by`. Rewrite using `[hP i j h, map_zero]`. Conclude with `zero_le'`.
-/
private theorem eventually_valuation_le_uniformizer_pow_of_mem_unipRad (e : (Σ a, m a) ≃ n) {g : GL n k} (hg : g ∈ unipRad k e) (i j : n) :
    ∀ᶠ M : ℕ in Filter.atTop, valuation k ((g : Matrix n n k) i j) ≤ uniformizer k ^ wt e M i j := by
  obtain ⟨hP, hD⟩ := mem_unipRad.1 hg
  rw [mem_parab] at hP
  have hmono : ∀ a b : ℤ, a ≤ b → uniformizer k ^ b ≤ uniformizer k ^ a := by
    intro a b hab
    exact zpow_le_zpow_right_of_le_one₀ uniformizer_pos uniformizer_lt_one.le hab
  rcases lt_trichotomy (blk e i) (blk e j) with h | h | h
  ·
    obtain ⟨N, hN⟩ := MulArchimedean.arch (valuation k ((g : Matrix n n k) i j))
      ((one_lt_inv₀ uniformizer_pos).2 uniformizer_lt_one)
    have hss : Finset.univ.filter (· < blk e i) ⊂ Finset.univ.filter (· < blk e j) := by
      refine (Finset.ssubset_iff_of_subset (fun x hx => ?_)).2 ⟨blk e i, ?_, ?_⟩
      · simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
        exact hx.trans h
      · simp [h]
      · simp
    have hlt := Finset.card_lt_card hss
    filter_upwards [Filter.eventually_ge_atTop N] with M hM
    have hM' : (N : ℤ) ≤ M := by exact_mod_cast hM
    have hd : ((Finset.univ.filter (· < blk e i)).card : ℤ) -
        (Finset.univ.filter (· < blk e j)).card ≤ -1 := by omega
    have hw : wt e M i j ≤ -(N : ℤ) := by
      simp only [wt]
      nlinarith
    refine hN.trans (le_trans (le_of_eq ?_) (hmono _ _ hw))
    rw [zpow_neg, zpow_natCast, inv_pow]
  ·
    refine Filter.Eventually.of_forall fun M => ?_
    have hw : wt e M i j = 0 := by simp [wt, h]
    rw [hw, zpow_zero]
    obtain ⟨⟨a, i'⟩, rfl⟩ := e.surjective i
    obtain ⟨⟨b, j'⟩, rfl⟩ := e.surjective j
    simp only [blk_apply] at h
    cases h
    rw [hD _ i' j', Matrix.one_apply]
    split_ifs <;> simp
  ·
    exact Filter.Eventually.of_forall fun M => by
      rw [hP i j h, map_zero]
      exact zero_le'

/- English proof (translation)
Unfold `GlobalTheory.IwahoriInj.grp`. Simplify using `only [Subgroup.mem_mk, Submonoid.mem_mk, Subsemigroup.mem_mk, Set.mem_ofPred_eq]`. Unfold `GlobalTheory.IwahoriInj.Deep`. Establish `hu' : u⁻¹ ∈ unipRad k e` using `inv_mem hu`. Conclude with `(Filter.eventually_all.2 fun i => Filter.eventually_all.2 fun j => eventually_valuation_le_uniformizer_pow_of_mem_unipRad e hu i j).and (Filter.eventually_all.2 fun i => Filter.eventually_all.2 fun j => eventually_valuation_le_uniformizer_pow_of_mem_unipRad e hu' i j)`.
-/
theorem eventually_mem_grp (e : (Σ a, m a) ≃ n) {u : GL n k} (hu : u ∈ unipRad k e) :
    ∀ᶠ M : ℕ in Filter.atTop, u ∈ grp k (conc_wt e M) := by
  unfold GlobalTheory.IwahoriInj.grp
  simp only [Subgroup.mem_mk, Submonoid.mem_mk, Subsemigroup.mem_mk, Set.mem_ofPred_eq]
  unfold GlobalTheory.IwahoriInj.Deep
  have hu' : u⁻¹ ∈ unipRad k e := inv_mem hu
  exact (Filter.eventually_all.2 fun i => Filter.eventually_all.2 fun j => eventually_valuation_le_uniformizer_pow_of_mem_unipRad e hu i j).and
    (Filter.eventually_all.2 fun i => Filter.eventually_all.2 fun j => eventually_valuation_le_uniformizer_pow_of_mem_unipRad e hu' i j)

/- English proof (translation)
Apply `IsTopologicalAddGroup.t2Space_of_zero_sep` to reduce the goal to its premises. Introduce `x hx`. Use `⟨{y | valuation k y < valuation k x}, ?_, fun h => lt_irrefl (valuation k x) (by simpa using h)⟩` and prove the remaining obligations. Rewrite using `[IsValuativeTopology.mem_nhds_zero_iff]`. Conclude with `⟨Units.mk0 _ ((valuation k).ne_zero_iff.2 hx), fun y hy => by simpa using hy⟩`.
-/
private theorem t2Space_localField : T2Space k := by
  apply IsTopologicalAddGroup.t2Space_of_zero_sep
  intro x hx
  refine ⟨{y | valuation k y < valuation k x}, ?_, fun h => lt_irrefl (valuation k x) (by simpa using h)⟩
  rw [IsValuativeTopology.mem_nhds_zero_iff]
  exact ⟨Units.mk0 _ ((valuation k).ne_zero_iff.2 hx), fun y hy => by simpa using hy⟩

/- English proof (translation)
Establish `: T2Space k` using `t2Space_localField`. Establish `hv : Continuous fun g : GL n k => (g : Matrix n n k)` using `Units.continuous_val`. Establish `hc : ∀ i j, Continuous fun g : GL n k => (g : Matrix n n k) i j` using `fun i j => hv.matrix_elem i j`. Establish `hset : (unipRad k e : Set (GL n k)) = {g : GL n k | ∀ i j, blk e j < blk e i → (g : Matrix n n k) i j = 0} ∩ {g : GL n k | ∀ a (i j : m a), (g : Matrix n n k) (e ⟨a, i⟩) (e ⟨a, j⟩) = (1 : Matrix (m a) (m a) k) i j}`. Use extensionality with `g`.

Simplify using `only [SetLike.mem_coe, mem_unipRad, mem_parab, Set.mem_inter_iff, Set.mem_ofPred_eq]`. Rewrite using `[hset]`. Use `IsClosed.inter ?_ ?_` and prove the remaining obligations. Simplify using `only [Set.ofPred_forall]`. Conclude with `isClosed_iInter fun i => isClosed_iInter fun j => isClosed_iInter fun _ => isClosed_eq (hc i j) continuous_const`.

Simplify using `only [Set.ofPred_forall]`. Conclude with `isClosed_iInter fun a => isClosed_iInter fun i => isClosed_iInter fun j => isClosed_eq (hc _ _) continuous_const`.
-/
theorem isClosed_unipRad (e : (Σ a, m a) ≃ n) : IsClosed (unipRad k e : Set (GL n k)) := by
  have : T2Space k := t2Space_localField
  have hv : Continuous fun g : GL n k => (g : Matrix n n k) := Units.continuous_val
  have hc : ∀ i j, Continuous fun g : GL n k => (g : Matrix n n k) i j := fun i j => hv.matrix_elem i j
  have hset : (unipRad k e : Set (GL n k)) =
      {g : GL n k | ∀ i j, blk e j < blk e i → (g : Matrix n n k) i j = 0} ∩
        {g : GL n k | ∀ a (i j : m a), (g : Matrix n n k) (e ⟨a, i⟩) (e ⟨a, j⟩) = (1 : Matrix (m a) (m a) k) i j} := by
    ext g
    simp only [SetLike.mem_coe, mem_unipRad, mem_parab, Set.mem_inter_iff, Set.mem_ofPred_eq]
  rw [hset]
  refine IsClosed.inter ?_ ?_
  · simp only [Set.ofPred_forall]
    exact isClosed_iInter fun i => isClosed_iInter fun j => isClosed_iInter fun _ =>
      isClosed_eq (hc i j) continuous_const
  · simp only [Set.ofPred_forall]
    exact isClosed_iInter fun a => isClosed_iInter fun i => isClosed_iInter fun j =>
      isClosed_eq (hc _ _) continuous_const

variable {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]

/- English proof (translation)
Proceed by induction on `hv using Submodule.span_induction with`. Consider the case `mem x hx`. Take `⟨u, w, rfl⟩` from `hx`. Use `filter_upwards [eventually_mem_grp e u.2] with M hM`. Conclude with `Submodule.subset_span ⟨⟨u, hM, u.2⟩, w, rfl⟩`.

Consider the case `zero => exact Filter.Eventually.of_forall fun _ => Submodule.zero_mem _`. Consider the case `add x y _ _ hx hy => filter_upwards [hx, hy] with M h₁ h₂`. Conclude with `Submodule.add_mem _ h₁ h₂`. Consider the case `smul c x _ hx => filter_upwards [hx] with M h`. Conclude with `Submodule.smul_mem _ c h`.
-/
theorem eventually_mem_twKer_inf (e : (Σ a, m a) ≃ n) {π : Representation ℂ (GL n k) V} {v : V}
    (hv : v ∈ twKer π (unipRad k e) 1) :
    ∀ᶠ M : ℕ in Filter.atTop, v ∈ twKer π (grp k (conc_wt e M) ⊓ unipRad k e) 1 := by
  induction hv using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨u, w, rfl⟩ := hx
    filter_upwards [eventually_mem_grp e u.2] with M hM
    exact Submodule.subset_span ⟨⟨u, hM, u.2⟩, w, rfl⟩
  | zero => exact Filter.Eventually.of_forall fun _ => Submodule.zero_mem _
  | add x y _ _ hx hy =>
    filter_upwards [hx, hy] with M h₁ h₂
    exact Submodule.add_mem _ h₁ h₂
  | smul c x _ hx =>
    filter_upwards [hx] with M h
    exact Submodule.smul_mem _ c h

/- English proof (translation)
Use `Submodule.span_mono ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨h, w, rfl⟩`. Conclude with `⟨⟨h, hHK h.2⟩, w, rfl⟩`.
-/
private theorem twKer_one_mono' {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V]
    {ρ : Representation ℂ G V} {H K : Subgroup G} (hHK : H ≤ K) : twKer ρ H 1 ≤ twKer ρ K 1 := by
  refine Submodule.span_mono ?_
  rintro _ ⟨h, w, rfl⟩
  exact ⟨⟨h, hHK h.2⟩, w, rfl⟩

/- English proof (translation)
Introduce `x y hxy`. Take `⟨v, rfl⟩` from `Submodule.Quotient.mk_surjective _ x`. Take `⟨w, rfl⟩` from `Submodule.Quotient.mk_surjective _ y`. Establish `hmk : ∀ u : V, jacMap e f (Submodule.Quotient.mk u) = Submodule.Quotient.mk (f u)` using `fun _ => rfl`. Rewrite `hxy` using `[hmk, hmk, Submodule.Quotient.eq, ← map_sub]`.

Rewrite using `[Submodule.Quotient.eq]`. Take `⟨M, hM⟩` from `(eventually_mem_twKer_inf e hxy).exists`. Establish `hcpt : IsCompact ((grp k (conc_wt e M) ⊓ unipRad k e : Subgroup (GL n k)) : Set (GL n k))`. Rewrite using `[Subgroup.coe_inf]`. Conclude with `(isCompact_grp (conc_wt e M)).inter_right (isClosed_unipRad e)`.

Conclude with `twKer_one_mono' inf_le_right (mem_twKer_of_map f hπ hf hcpt hM)`.
-/
theorem jacMap_injective (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (α n : Type) (m : α → Type) [Fintype α] [LinearOrder α]
    [∀ a, Fintype (m a)] [∀ a, DecidableEq (m a)] [Fintype n] [DecidableEq n] (e : (Σ a, m a) ≃ n)
    (V : Type) [AddCommGroup V] [Module ℂ V] (W : Type) [AddCommGroup W] [Module ℂ W]
    (π₁ : Representation ℂ (GL n k) V) (π : Representation ℂ (GL n k) W)
    (f : π₁.IntertwiningMap π) (hπ : IsSmooth π) (hf : Function.Injective f) :
    Function.Injective (jacMap e f) := by
  intro x y hxy
  obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  obtain ⟨w, rfl⟩ := Submodule.Quotient.mk_surjective _ y
  have hmk : ∀ u : V, jacMap e f (Submodule.Quotient.mk u) = Submodule.Quotient.mk (f u) :=
    fun _ => rfl
  rw [hmk, hmk, Submodule.Quotient.eq, ← map_sub] at hxy
  rw [Submodule.Quotient.eq]
  obtain ⟨M, hM⟩ := (eventually_mem_twKer_inf e hxy).exists
  have hcpt : IsCompact ((grp k (conc_wt e M) ⊓ unipRad k e : Subgroup (GL n k)) : Set (GL n k)) := by
    rw [Subgroup.coe_inf]
    exact (isCompact_grp (conc_wt e M)).inter_right (isClosed_unipRad e)
  exact twKer_one_mono' inf_le_right (mem_twKer_of_map f hπ hf hcpt hM)

end GlobalTheory.JacInj

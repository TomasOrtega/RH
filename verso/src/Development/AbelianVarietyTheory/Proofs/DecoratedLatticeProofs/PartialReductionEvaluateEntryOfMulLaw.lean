import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ChLApply
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.AddCharConductorAndHaarIntegersExist
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData
open scoped Topology

noncomputable section
namespace GlobalTheory.PartRedEval
open GlobalTheory.PartRed

section Alg
variable {k : Type} [Field k] {R Q : Type} [DecidableEq R] [DecidableEq Q]

/- English proof (translation)
Simplify using `[fillAt, hE, hI]`.
-/
theorem fillAt_apply_of_notMem (β : Matrix R Q k) {E I : Finset (R × Q)} {e : R × Q} (hE : e ∉ E) (hI : e ∉ I)
    (x : Matrix R Q k) (y : I → k) : fillAt β E I x y e.1 e.2 = x e.1 e.2 := by
  simp [fillAt, hE, hI]

/- English proof (translation)
Use extensionality with `r q`. Distinguish the cases in `h : e = (r, q)`. Substitute `h` using the available equality. Simplify using `[fillAt, hE, hI]`. Establish `h0 : Matrix.single e.1 e.2 u r q = 0` using `Matrix.single_apply_of_ne _ _ _ _ _ (fun h' => h (Prod.ext h'.1 h'.2))`.

Simplify using `[fillAt, h0]`.
-/
theorem fillAt_add_single (β : Matrix R Q k) {E I : Finset (R × Q)} {e : R × Q} (hE : e ∉ E) (hI : e ∉ I)
    (x : Matrix R Q k) (u : k) (y : I → k) :
    fillAt β E I (x + Matrix.single e.1 e.2 u) y = fillAt β E I x y + Matrix.single e.1 e.2 u := by
  ext r q
  by_cases h : e = (r, q)
  · subst h
    simp [fillAt, hE, hI]
  · have h0 : Matrix.single e.1 e.2 u r q = 0 :=
      Matrix.single_apply_of_ne _ _ _ _ _ (fun h' => h (Prod.ext h'.1 h'.2))
    simp [fillAt, h0]

/- English proof (translation)
Use extensionality with `r q`. Distinguish the cases in `h : e = (r, q)`. Substitute `h` using the available equality. Simplify using `[fillAt, hE, hI]`. Establish `h0 : Matrix.single e.1 e.2 (β e.1 e.2 - x e.1 e.2) r q = 0` using `Matrix.single_apply_of_ne _ _ _ _ _ (fun h' => h (Prod.ext h'.1 h'.2))`.

Establish `h1 : (r, q) ≠ e` using `fun h' => h h'.symm`. Simplify using `[fillAt, h0, h1]`.
-/
theorem fillAt_insert (β : Matrix R Q k) {E I : Finset (R × Q)} {e : R × Q} (hE : e ∉ E) (hI : e ∉ I)
    (x : Matrix R Q k) (y : I → k) :
    fillAt β (insert e E) I x y = fillAt β E I (x + Matrix.single e.1 e.2 (β e.1 e.2 - x e.1 e.2)) y := by
  ext r q
  by_cases h : e = (r, q)
  · subst h
    simp [fillAt, hE, hI]
  · have h0 : Matrix.single e.1 e.2 (β e.1 e.2 - x e.1 e.2) r q = 0 :=
      Matrix.single_apply_of_ne _ _ _ _ _ (fun h' => h (Prod.ext h'.1 h'.2))
    have h1 : (r, q) ≠ e := fun h' => h h'.symm
    simp [fillAt, h0, h1]

end Alg

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {R Q : Type} [Fintype R] [Fintype Q] [DecidableEq R] [DecidableEq Q]

/- English proof (translation)
Establish `h : (w : Matrix R Q k → k) = fun m => ∑ i, ∑ j, m i j * w (Matrix.single i j 1)`. Use function extensionality and compare the values at `m`. Use `conv_lhs => rw [Matrix.matrix_eq_sum_single m]`. Simplify using `only [map_sum]`. Use `Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations.

Rewrite using `[← smul_eq_mul, ← map_smul, Matrix.smul_single, smul_eq_mul, mul_one]`. Rewrite using `[h]`. Conclude with `continuous_finset_sum _ fun i _ => continuous_finset_sum _ fun j _ => (continuous_id.matrix_elem i j).mul continuous_const`.
-/
theorem continuous_form (w : Matrix R Q k →ₗ[k] k) : Continuous w := by
  have h : (w : Matrix R Q k → k) = fun m => ∑ i, ∑ j, m i j * w (Matrix.single i j 1) := by
    funext m
    conv_lhs => rw [Matrix.matrix_eq_sum_single m]
    simp only [map_sum]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [← smul_eq_mul, ← map_smul, Matrix.smul_single, smul_eq_mul, mul_one]
  rw [h]
  exact continuous_finset_sum _ fun i _ => continuous_finset_sum _ fun j _ =>
    (continuous_id.matrix_elem i j).mul continuous_const

omit [Fintype R] [Fintype Q] in

/- English proof (translation)
Establish `hc : Continuous fun t : k => (Matrix.single e.1 e.2 t : Matrix R Q k)`. Use `continuous_matrix fun i j => ?_` and prove the remaining obligations. Simplify using `only [Matrix.single, Matrix.of_apply]`. Use `split_ifs`. Conclude with `continuous_id`.

Conclude with `continuous_const`. Establish `h1 : ∀ᶠ t in 𝓝 (0 : k), ∀ x ∈ tsupport f, f (x + Matrix.single e.1 e.2 t) = f x`. Use `IsCompact.eventually_forall_of_forall_eventually hf.2 fun x _ => ?_` and prove the remaining obligations. Establish `h2 : IsLocallyConstant fun q : k × Matrix R Q k => (f (q.2 + Matrix.single e.1 e.2 q.1), f q.2)` using `(hf.1.comp_continuous (continuous_snd.add (hc.comp continuous_fst))).prodMk (hf.1.comp_continuous continuous_snd)`. Use `filter_upwards [h2.eventually_eq (0, x)] with q hq`.

Simplify using `only [Prod.mk.injEq, Matrix.single_zero, add_zero] at hq`. Rewrite using `[hq.1, hq.2]`. Take `⟨s, hs⟩` from `exists_cball_subset h1`. Use `⟨s, fun t ht x => ?_⟩` and prove the remaining obligations. Distinguish the cases in `hx : x ∈ tsupport f`.

Conclude with `hs ht x hx`. Distinguish the cases in `hx' : x + Matrix.single e.1 e.2 t ∈ tsupport f`. Use `hs (neg_mem_cball ht) _ hx'` as an intermediate fact. Rewrite using `[← this, add_assoc, ← Matrix.single_add, add_neg_cancel, Matrix.single_zero, add_zero]`. Rewrite using `[image_eq_zero_of_notMem_tsupport hx, image_eq_zero_of_notMem_tsupport hx']`.
-/
theorem exists_cball_single {f : Matrix R Q k → ℂ} (hf : f ∈ SB (Matrix R Q k)) (e : R × Q) :
    ∃ s : kˣ, ∀ t ∈ cball s, ∀ x, f (x + Matrix.single e.1 e.2 t) = f x := by
  have hc : Continuous fun t : k => (Matrix.single e.1 e.2 t : Matrix R Q k) := by
    refine continuous_matrix fun i j => ?_
    simp only [Matrix.single, Matrix.of_apply]
    split_ifs
    · exact continuous_id
    · exact continuous_const
  have h1 : ∀ᶠ t in 𝓝 (0 : k), ∀ x ∈ tsupport f, f (x + Matrix.single e.1 e.2 t) = f x := by
    refine IsCompact.eventually_forall_of_forall_eventually hf.2 fun x _ => ?_
    have h2 : IsLocallyConstant fun q : k × Matrix R Q k => (f (q.2 + Matrix.single e.1 e.2 q.1), f q.2) :=
      (hf.1.comp_continuous (continuous_snd.add (hc.comp continuous_fst))).prodMk
        (hf.1.comp_continuous continuous_snd)
    filter_upwards [h2.eventually_eq (0, x)] with q hq
    simp only [Prod.mk.injEq, Matrix.single_zero, add_zero] at hq
    rw [hq.1, hq.2]
  obtain ⟨s, hs⟩ := exists_cball_subset h1
  refine ⟨s, fun t ht x => ?_⟩
  by_cases hx : x ∈ tsupport f
  · exact hs ht x hx
  by_cases hx' : x + Matrix.single e.1 e.2 t ∈ tsupport f
  · have := hs (neg_mem_cball ht) _ hx'
    rw [← this, add_assoc, ← Matrix.single_add, add_neg_cancel, Matrix.single_zero, add_zero]
  · rw [image_eq_zero_of_notMem_tsupport hx, image_eq_zero_of_notMem_tsupport hx']

def ballGrp (s : kˣ) : AddSubgroup k where
  carrier := cball s
  add_mem' := add_mem_cball
  zero_mem' := by simp [cball]
  neg_mem' := neg_mem_cball

/- English proof (translation)
Use `(IsLocallyConstant.iff_eventually_eq _).mpr fun x => ?_` and prove the remaining obligations. Establish `: (fun z => -x + z) ⁻¹' cball s ∈ 𝓝 x` using `((isOpen_cball s).preimage (by fun_prop)).mem_nhds (by simp [cball])`. Use `filter_upwards [this] with z hz`. Conclude with `(QuotientAddGroup.eq.mpr hz).symm`.
-/
theorem isLocallyConstant_mk (s : kˣ) : IsLocallyConstant (QuotientAddGroup.mk : k → k ⧸ ballGrp s) := by
  refine (IsLocallyConstant.iff_eventually_eq _).mpr fun x => ?_
  have : (fun z => -x + z) ⁻¹' cball s ∈ 𝓝 x :=
    ((isOpen_cball s).preimage (by fun_prop)).mem_nhds (by simp [cball])
  filter_upwards [this] with z hz
  exact (QuotientAddGroup.eq.mpr hz).symm

/- English proof (translation)
Take `⟨t, ht, hne⟩` from `h.exists_ne_one (c * s⁻¹) (x := d) (by`. Rewrite using `[show c * (c * s⁻¹)⁻¹ = s by rw [_root_.mul_inv_rev, inv_inv, mul_comm s, mul_inv_cancel_left]])` and apply the resulting hypothesis. Use `⟨t, hne, fun u hu => h.eq_one ?_⟩` and prove the remaining obligations. Establish `h1 : valuation k t ≤ valuation k ((c * s⁻¹ : kˣ) : k)` using `ht`. Establish `h2 : valuation k u ≤ valuation k (s : k)` using `hu`.

Use `show valuation k (t * u) ≤ valuation k (c : k)`. Establish `h3 : (c : k) = ((c * s⁻¹ : kˣ) : k) * s` using `by simp`. Rewrite using `[h3, map_mul, map_mul]`. Conclude with `mul_le_mul' h1 h2`.
-/
theorem exists_sep {ψ : AddChar k Circle} {c : kˣ} (h : HasConductor ψ c) (s : kˣ) {d : k} (hd : d ∉ cball s) :
    ∃ b : k, ψ (b * d) ≠ 1 ∧ ∀ u ∈ cball s, ψ (b * u) = 1 := by
  obtain ⟨t, ht, hne⟩ := h.exists_ne_one (c * s⁻¹) (x := d) (by
    rwa [show c * (c * s⁻¹)⁻¹ = s by rw [_root_.mul_inv_rev, inv_inv, mul_comm s, mul_inv_cancel_left]])
  refine ⟨t, hne, fun u hu => h.eq_one ?_⟩
  have h1 : valuation k t ≤ valuation k ((c * s⁻¹ : kˣ) : k) := ht
  have h2 : valuation k u ≤ valuation k (s : k) := hu
  show valuation k (t * u) ≤ valuation k (c : k)
  have h3 : (c : k) = ((c * s⁻¹ : kˣ) : k) * s := by simp
  rw [h3, map_mul, map_mul]
  exact mul_le_mul' h1 h2

variable [MeasurableSpace k] [BorelSpace k]

/- English proof (translation)
Use `haveI := secondCountable k`. Use `haveI := t2Space k`. Establish `hf : Continuous (fillAt β E I x)`. Use `continuous_matrix fun r q => ?_` and prove the remaining obligations. Simplify using `only [fillAt, Matrix.of_apply]`.

Use `split_ifs`. Conclude with `continuous_apply _`. Conclude with `continuous_const`. Conclude with `continuous_const`. Establish `hp : Continuous fun (m : Matrix R Q k) (i : I) => m i.1.1 i.1.2` using `continuous_pi fun i => continuous_id.matrix_elem _ _`.

Establish `h1 : HasCompactSupport fun y : I → k => Φ (fillAt β E I x y)`. Use `HasCompactSupport.intro (IsCompact.image hΦ.2 hp) fun y hy => ?_` and prove the remaining obligations. Use `image_eq_zero_of_notMem_tsupport fun h => hy ⟨_, h, ?_⟩` and prove the remaining obligations. Use function extensionality and compare the values at `i`. Simplify using `[fillAt]`.

Use `Continuous.integrable_of_hasCompactSupport ?_ h1.mul_right` and prove the remaining obligations. Conclude with `(hΦ.1.continuous.comp hf).mul (continuous_subtype_val.comp (hψ.comp ((continuous_form w).comp hf).neg))`.
-/
theorem integrable_red {ψ : AddChar k Circle} (hψ : Continuous ψ) (ν : Measure k) [ν.IsAddHaarMeasure]
    (w : Matrix R Q k →ₗ[k] k) (β : Matrix R Q k) (E I : Finset (R × Q)) {Φ : Matrix R Q k → ℂ}
    (hΦ : Φ ∈ SB (Matrix R Q k)) (x : Matrix R Q k) :
    Integrable (fun y : I → k => Φ (fillAt β E I x y) * (ψ (-w (fillAt β E I x y)) : ℂ))
      (Measure.pi fun _ => ν) := by
  haveI := secondCountable k
  haveI := t2Space k
  have hf : Continuous (fillAt β E I x) := by
    refine continuous_matrix fun r q => ?_
    simp only [fillAt, Matrix.of_apply]
    split_ifs
    · exact continuous_apply _
    · exact continuous_const
    · exact continuous_const
  have hp : Continuous fun (m : Matrix R Q k) (i : I) => m i.1.1 i.1.2 :=
    continuous_pi fun i => continuous_id.matrix_elem _ _
  have h1 : HasCompactSupport fun y : I → k => Φ (fillAt β E I x y) := by
    refine HasCompactSupport.intro (IsCompact.image hΦ.2 hp) fun y hy => ?_
    refine image_eq_zero_of_notMem_tsupport fun h => hy ⟨_, h, ?_⟩
    funext i
    simp [fillAt]
  refine Continuous.integrable_of_hasCompactSupport ?_ h1.mul_right
  exact (hΦ.1.continuous.comp hf).mul
    (continuous_subtype_val.comp (hψ.comp ((continuous_form w).comp hf).neg))

/- English proof (translation)
Introduce `k _ _ _ _ _ _ ψ ν hψ hψ1 hν R Q _ _ _ _ M _ _ L w β E I e hI hK hL`. Distinguish the cases in `hE : e ∈ E`. Rewrite using `[Finset.insert_eq_of_mem hE]` and apply the resulting hypothesis. Introduce `Φ hΦ`. Take `⟨c, hc⟩` from `(conductor_exists k).1 ψ hψ hψ1`.

Take `⟨s₁, hs₁⟩` from `exists_cball_single Φ.2 e`. Establish `hn : (fun u : k => u * w (Matrix.single e.1 e.2 1)) ⁻¹' cball c ∈ 𝓝 (0 : k)` using `((isOpen_cball c).preimage (by fun_prop)).mem_nhds (by simp [cball])`. Take `⟨s, hs⟩` from `exists_cball_subset (Filter.inter_mem (cball_mem_nhds s₁) hn)`. Establish `hinv : ∀ u ∈ cball s, ∀ x, red ψ ν w β E I Φ.1 (x + Matrix.single e.1 e.2 u) = red ψ ν w β E I Φ.1 x`. Introduce `u hu x`.

Unfold `red`. Use `congr 1`. Use function extensionality and compare the values at `y`. Establish `h1 : w (Matrix.single e.1 e.2 u) = u * w (Matrix.single e.1 e.2 1)`. Rewrite using `[← smul_eq_mul, ← map_smul, Matrix.smul_single, smul_eq_mul, mul_one]`.

Rewrite using `[fillAt_add_single β hE hI, hs₁ u (hs hu).1, map_add, neg_add, AddChar.map_add_eq_mul, h1, hc.eq_one (neg_mem_cball (hs hu).2), mul_one]`. Set `p : Matrix R Q k → k ⧸ ballGrp s` to `fun x => QuotientAddGroup.mk (x e.1 e.2)`. Establish `hp : IsLocallyConstant p` using `(isLocallyConstant_mk s).comp_continuous (continuous_id.matrix_elem _ _)`. Set `P : k ⧸ ballGrp s → SB (Matrix R Q k)` to `fun q => ⟨fun x => (if p x = q then 1 else 0) * Φ.1 x, (hp.comp fun a => if a = q then (1 : ℂ) else 0).mul Φ.2.1, Φ.2.2.mul_left⟩`. Establish `hred : ∀ q x, red ψ ν w β E I (P q).1 x = (if p x = q then 1 else 0) * red ψ ν w β E I Φ.1 x`.

Introduce `q x`. Unfold `red`. Rewrite using `[← integral_const_mul]`. Use `congr 1`. Use function extensionality and compare the values at `y`.

Simplify using `only [P, p, fillAt_apply_of_notMem β hE hI, mul_assoc]`. Establish `hP : ∀ q, L (P q) = 0`. Introduce `q`. Proceed by induction on `q using QuotientAddGroup.induction_on with | H a => ?_`. Distinguish the cases in `ha : a - β e.1 e.2 ∈ cball s`.

Use `hK _ (funext fun x => ?_)` and prove the remaining obligations. Rewrite using `[hred]`. Use `split_ifs with hx`. Establish `h1 : -x e.1 e.2 + a ∈ cball s` using `QuotientAddGroup.eq.mp hx`. Establish `h2 : β e.1 e.2 - x e.1 e.2 ∈ cball s`.

Use `add_mem_cball h1 (neg_mem_cball ha)` as an intermediate fact. Use `this using 1` and compare the differences between its conclusion and the goal. Expand and normalize the polynomial expressions, which then agree. Establish `h3` using `congrFun hΦ x`. Rewrite using `[← hinv _ h2, one_mul]`.

Simplify `h3` using `only [red, fillAt_insert β hE hI]`. Simplify using the standard rewrite rules. Take `⟨b, hb, hb'⟩` from `exists_sep hc s ha`. Take `⟨Φ', h1, h2⟩` from `hL b (P a)`. Use `set z : ℂ := (ψ (b * (a - β e.1 e.2)) : ℂ) with hz`.

Establish `h3 : L (Φ' - z • P a) = 0`. Use `hK _ (funext fun x => ?_)` and prove the remaining obligations. Establish `h4 : red ψ ν w β E I (Φ' - z • P a).1 x = red ψ ν w β E I Φ'.1 x - z * red ψ ν w β E I (P a).1 x`. Unfold `red`. Rewrite using `[← integral_const_mul, ← integral_sub (integrable_red hψ ν w β E I Φ'.2 x) ((integrable_red hψ ν w β E I (P a).2 x).const_mul z)]`.

Use `congr 1`. Use function extensionality and compare the values at `y`. Simplify using `only [Submodule.coe_sub, Submodule.coe_smul, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[h4, h2, hred]`.

Use `split_ifs with hx`. Establish `h5 : -a + x e.1 e.2 ∈ cball s` using `QuotientAddGroup.eq.mp hx.symm`. Establish `h6 : b * (x e.1 e.2 - β e.1 e.2) = b * (a - β e.1 e.2) + b * (-a + x e.1 e.2)` using `by ring`. Rewrite using `[h6, AddChar.map_add_eq_mul, hb' _ h5, mul_one, hz]`. Simplify using the standard rewrite rules.

Simplify using the standard rewrite rules. Rewrite `h3` using `[map_sub, map_smul, h1]`. Establish `h7 : (1 - z) ≠ 0` using `fun h => hb (Circle.ext (by rw [← hz, Circle.coe_one]; exact (sub_eq_zero.mp h).symm))`. Establish `h8 : (1 - z) • L (P a) = 0` using `by rw [sub_smul, one_smul, h3]`. Conclude with `(smul_eq_zero.mp h8).resolve_left h7`.

Establish `hfin : (p '' tsupport Φ.1).Finite`. Use `letI : TopologicalSpace (k ⧸ ballGrp s) := ⊥`. Use `haveI : DiscreteTopology (k ⧸ ballGrp s) := ⟨rfl⟩`. Conclude with `(IsCompact.image Φ.2.2 hp.continuous).finite_of_discrete`. Establish `hsum : Φ = ∑ q ∈ hfin.toFinset, P q`.

Use `Subtype.ext (funext fun x => ?_)` and prove the remaining obligations. Simplify using `only [Submodule.coe_sum, Finset.sum_apply, P, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Set.Finite.mem_toFinset]`. Use `split_ifs with hx`. Both sides reduce to the same expression. Conclude with `image_eq_zero_of_notMem_tsupport fun h => hx ⟨x, h, rfl⟩`.

Rewrite using `[hsum, map_sum]`. Conclude with `Finset.sum_eq_zero fun q _ => hP q`.
-/
theorem kills_insert_of_evalLaw : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (ψ : AddChar k Circle) (ν : Measure k), Continuous ψ → ψ ≠ 1 → ν.IsAddHaarMeasure → ∀ (R Q : Type) [Fintype R] [Fintype Q] [DecidableEq R] [DecidableEq Q] (M : Type) [AddCommGroup M] [Module ℂ M] (L : SB (Matrix R Q k) →ₗ[ℂ] M) (w : Matrix R Q k →ₗ[k] k) (β : Matrix R Q k) (E I : Finset (R × Q)) (e : R × Q), e ∉ I → GlobalTheory.PartRed.Kills L ψ ν w β E I → GlobalTheory.PartRed.EvalLaw L ψ ν w β E I e → GlobalTheory.PartRed.Kills L ψ ν w β (insert e E) I := by
  intro k _ _ _ _ _ _ ψ ν hψ hψ1 hν R Q _ _ _ _ M _ _ L w β E I e hI hK hL
  classical
  by_cases hE : e ∈ E
  · rwa [Finset.insert_eq_of_mem hE]
  intro Φ hΦ
  obtain ⟨c, hc⟩ := (conductor_exists k).1 ψ hψ hψ1
  obtain ⟨s₁, hs₁⟩ := exists_cball_single Φ.2 e
  have hn : (fun u : k => u * w (Matrix.single e.1 e.2 1)) ⁻¹' cball c ∈ 𝓝 (0 : k) :=
    ((isOpen_cball c).preimage (by fun_prop)).mem_nhds (by simp [cball])
  obtain ⟨s, hs⟩ := exists_cball_subset (Filter.inter_mem (cball_mem_nhds s₁) hn)

  have hinv : ∀ u ∈ cball s, ∀ x, red ψ ν w β E I Φ.1 (x + Matrix.single e.1 e.2 u) = red ψ ν w β E I Φ.1 x := by
    intro u hu x
    unfold red
    congr 1
    funext y
    have h1 : w (Matrix.single e.1 e.2 u) = u * w (Matrix.single e.1 e.2 1) := by
      rw [← smul_eq_mul, ← map_smul, Matrix.smul_single, smul_eq_mul, mul_one]
    rw [fillAt_add_single β hE hI, hs₁ u (hs hu).1, map_add, neg_add, AddChar.map_add_eq_mul, h1,
      hc.eq_one (neg_mem_cball (hs hu).2), mul_one]
  let p : Matrix R Q k → k ⧸ ballGrp s := fun x => QuotientAddGroup.mk (x e.1 e.2)
  have hp : IsLocallyConstant p := (isLocallyConstant_mk s).comp_continuous (continuous_id.matrix_elem _ _)
  let P : k ⧸ ballGrp s → SB (Matrix R Q k) := fun q =>
    ⟨fun x => (if p x = q then 1 else 0) * Φ.1 x,
      (hp.comp fun a => if a = q then (1 : ℂ) else 0).mul Φ.2.1, Φ.2.2.mul_left⟩
  have hred : ∀ q x, red ψ ν w β E I (P q).1 x = (if p x = q then 1 else 0) * red ψ ν w β E I Φ.1 x := by
    intro q x
    unfold red
    rw [← integral_const_mul]
    congr 1
    funext y
    simp only [P, p, fillAt_apply_of_notMem β hE hI, mul_assoc]
  have hP : ∀ q, L (P q) = 0 := by
    intro q
    induction q using QuotientAddGroup.induction_on with | H a => ?_
    by_cases ha : a - β e.1 e.2 ∈ cball s
    · refine hK _ (funext fun x => ?_)
      rw [hred]
      split_ifs with hx
      · have h1 : -x e.1 e.2 + a ∈ cball s := QuotientAddGroup.eq.mp hx
        have h2 : β e.1 e.2 - x e.1 e.2 ∈ cball s := by
          have := add_mem_cball h1 (neg_mem_cball ha)
          convert this using 1
          ring
        have h3 := congrFun hΦ x
        rw [← hinv _ h2, one_mul]
        simpa only [red, fillAt_insert β hE hI] using h3
      · simp
    · obtain ⟨b, hb, hb'⟩ := exists_sep hc s ha
      obtain ⟨Φ', h1, h2⟩ := hL b (P a)
      set z : ℂ := (ψ (b * (a - β e.1 e.2)) : ℂ) with hz
      have h3 : L (Φ' - z • P a) = 0 := by
        refine hK _ (funext fun x => ?_)
        have h4 : red ψ ν w β E I (Φ' - z • P a).1 x =
            red ψ ν w β E I Φ'.1 x - z * red ψ ν w β E I (P a).1 x := by
          unfold red
          rw [← integral_const_mul, ← integral_sub (integrable_red hψ ν w β E I Φ'.2 x)
            ((integrable_red hψ ν w β E I (P a).2 x).const_mul z)]
          congr 1
          funext y
          simp only [Submodule.coe_sub, Submodule.coe_smul, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
          ring
        rw [h4, h2, hred]
        split_ifs with hx
        · have h5 : -a + x e.1 e.2 ∈ cball s := QuotientAddGroup.eq.mp hx.symm
          have h6 : b * (x e.1 e.2 - β e.1 e.2) = b * (a - β e.1 e.2) + b * (-a + x e.1 e.2) := by ring
          rw [h6, AddChar.map_add_eq_mul, hb' _ h5, mul_one, hz]
          simp
        · simp
      rw [map_sub, map_smul, h1] at h3
      have h7 : (1 - z) ≠ 0 := fun h => hb (Circle.ext (by rw [← hz, Circle.coe_one]; exact (sub_eq_zero.mp h).symm))
      have h8 : (1 - z) • L (P a) = 0 := by rw [sub_smul, one_smul, h3]
      exact (smul_eq_zero.mp h8).resolve_left h7
  have hfin : (p '' tsupport Φ.1).Finite := by
    letI : TopologicalSpace (k ⧸ ballGrp s) := ⊥
    haveI : DiscreteTopology (k ⧸ ballGrp s) := ⟨rfl⟩
    exact (IsCompact.image Φ.2.2 hp.continuous).finite_of_discrete
  have hsum : Φ = ∑ q ∈ hfin.toFinset, P q := by
    refine Subtype.ext (funext fun x => ?_)
    simp only [Submodule.coe_sum, Finset.sum_apply, P, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq,
      Set.Finite.mem_toFinset]
    split_ifs with hx
    · rfl
    · exact image_eq_zero_of_notMem_tsupport fun h => hx ⟨x, h, rfl⟩
  rw [hsum, map_sum]
  exact Finset.sum_eq_zero fun q _ => hP q

end GlobalTheory.PartRedEval

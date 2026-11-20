import Development.AutomorphicArithmetic.Foundations.Convolution.TwistedLocalOrbits.HoweSpace

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel Matrix GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets UpperTheory.ConvolutionTheory.Loc

namespace UpperTheory.ConvolutionTheory.Loc

variable {E : Type} [Field E] [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E]

/- English proof (translation)
Use `haveI : MulArchimedean (ValueGroupWithZero E) := isRankLeOne_iff_mulArchimedean.1 inferInstance`. Establish `hK : IsCompact (Set.pi Set.univ fun _ : ι => {x : E | valuation E x ≤ r})` using `isCompact_univ_pi fun _ => IsNonarchimedeanLocalField.isCompact_closedBall E r`. Establish `hin : ∀ m : ℕ, ∀ j, valuation E (F^[m] 0 j) ≤ r`. Introduce `m`. Proceed by induction on `m with`.

Consider the case `zero => intro j`. Simplify using the standard rewrite rules. Consider the case `succ m ih => rw [Function.iterate_succ_apply']`. Conclude with `hS _ ih`. Establish `hd : ∀ m : ℕ, ∀ j, valuation E (F^[m + 1] 0 j - F^[m] 0 j) ≤ c ^ m * r`.

Introduce `m`. Proceed by induction on `m with`. Consider the case `zero => intro j`. Simplify using `using hin 1 j`. Consider the case `succ m ih`.

Introduce `j`. Use `hF _ _ (hin (m + 1)) (hin m) _ ih j` as an intermediate fact. Rewrite `this` using `[← Function.iterate_succ_apply' F (m + 1), ← Function.iterate_succ_apply' F m]`. Rewrite using `[pow_succ', mul_assoc]` and apply the resulting hypothesis. Take `⟨p, hp, hcl⟩` from `hK.exists_mapClusterPt_of_frequently (l := Filter.atTop) (f := fun m : ℕ => F^[m] 0) (Filter.Frequently.of_forall fun m j _ => hin m j)`.

Establish `hp' : ∀ j, valuation E (p j) ≤ r` using `fun j => hp j trivial`. Use `⟨p, hp', funext fun j => ?_⟩` and prove the remaining obligations. Assume the negation of the conclusion as `hne`. Establish `hd0 : valuation E (F p j - p j) ≠ 0` using `by simpa [sub_eq_zero] using hne`. Use `set d := valuation E (F p j - p j) with hdd`.

Establish `hN : {u : ι → E | ∀ l, valuation E (u l - p l) < d} ∈ nhds p`. Rewrite using `[Set.setOf_forall]`. Use `Filter.iInter_mem.2 fun l => ?_` and prove the remaining obligations. Conclude with `(continuous_apply l).continuousAt.preimage_mem_nhds ((IsValuativeTopology.hasBasis_nhds (p l)).mem_of_mem (i := Units.mk0 d hd0) trivial)`. Establish `hev : ∀ᶠ m : ℕ in Filter.atTop, c ^ m * r < d`.

Distinguish the cases in `hr : r = 0`. Conclude with `Filter.Eventually.of_forall fun m => by simpa [hr] using zero_lt_iff.2 hd0`. Take `⟨m₀, hm₀⟩` from `exists_pow_lt₀ hc (Units.mk0 (d / r) (div_ne_zero hd0 hr))`. Use `Filter.eventually_atTop.2 ⟨m₀, fun m hm => ?_⟩` and prove the remaining obligations. Establish `h1 : c ^ m < d / r` using `(pow_le_pow_right_of_le_one' hc.le hm).trans_lt hm₀`.

Conclude with `(lt_div_iff₀ (zero_lt_iff.2 hr)).1 h1`. Take `⟨m, hm1, hm2⟩` from `((mapClusterPt_iff_frequently.1 hcl _ hN).and_eventually hev).exists`. Establish `h1` using `hF _ _ (hin m) hp' d (fun l => (hm1 l).le) j`. Rewrite `h1` using `[← Function.iterate_succ_apply' F m]`. Establish `h2 : valuation E (F^[m + 1] 0 j - F p j) < d` using `h1.trans_lt (by simpa using mul_lt_mul_of_pos_right hc (zero_lt_iff.2 hd0))`.

Establish `h3` using `(hd m j).trans_lt hm2`. Establish `e : F p j - p j = ((F^[m + 1] 0 j - F^[m] 0 j) + (F^[m] 0 j - p j)) - (F^[m + 1] 0 j - F p j)` using `by ring`. Establish `: valuation E (F p j - p j) < d`. Rewrite using `[e]`. Conclude with `Valuation.map_sub_lt _ (Valuation.map_add_lt _ h3 (hm1 j)) h2`.

Conclude with `lt_irrefl _ this`.
-/
private theorem fixB {ι : Type} [Fintype ι] (r c : ValueGroupWithZero E) (hc : c < 1) (F : (ι → E) → (ι → E))
    (hS : ∀ u, (∀ j, valuation E (u j) ≤ r) → ∀ j, valuation E (F u j) ≤ r)
    (hF : ∀ u u', (∀ j, valuation E (u j) ≤ r) → (∀ j, valuation E (u' j) ≤ r) → ∀ ρ,
      (∀ j, valuation E (u j - u' j) ≤ ρ) → ∀ j, valuation E (F u j - F u' j) ≤ c * ρ) :
    ∃ u, (∀ j, valuation E (u j) ≤ r) ∧ F u = u := by
  haveI : MulArchimedean (ValueGroupWithZero E) := isRankLeOne_iff_mulArchimedean.1 inferInstance
  have hK : IsCompact (Set.pi Set.univ fun _ : ι => {x : E | valuation E x ≤ r}) :=
    isCompact_univ_pi fun _ => IsNonarchimedeanLocalField.isCompact_closedBall E r
  have hin : ∀ m : ℕ, ∀ j, valuation E (F^[m] 0 j) ≤ r := by
    intro m
    induction m with
    | zero => intro j; simp
    | succ m ih => rw [Function.iterate_succ_apply']; exact hS _ ih
  have hd : ∀ m : ℕ, ∀ j, valuation E (F^[m + 1] 0 j - F^[m] 0 j) ≤ c ^ m * r := by
    intro m
    induction m with
    | zero => intro j; simpa using hin 1 j
    | succ m ih =>
      intro j
      have := hF _ _ (hin (m + 1)) (hin m) _ ih j
      rw [← Function.iterate_succ_apply' F (m + 1), ← Function.iterate_succ_apply' F m] at this
      rwa [pow_succ', mul_assoc]
  obtain ⟨p, hp, hcl⟩ := hK.exists_mapClusterPt_of_frequently (l := Filter.atTop) (f := fun m : ℕ => F^[m] 0)
    (Filter.Frequently.of_forall fun m j _ => hin m j)
  have hp' : ∀ j, valuation E (p j) ≤ r := fun j => hp j trivial
  refine ⟨p, hp', funext fun j => ?_⟩
  by_contra hne
  have hd0 : valuation E (F p j - p j) ≠ 0 := by simpa [sub_eq_zero] using hne
  set d := valuation E (F p j - p j) with hdd
  have hN : {u : ι → E | ∀ l, valuation E (u l - p l) < d} ∈ nhds p := by
    rw [Set.setOf_forall]
    refine Filter.iInter_mem.2 fun l => ?_
    exact (continuous_apply l).continuousAt.preimage_mem_nhds
      ((IsValuativeTopology.hasBasis_nhds (p l)).mem_of_mem (i := Units.mk0 d hd0) trivial)
  have hev : ∀ᶠ m : ℕ in Filter.atTop, c ^ m * r < d := by
    by_cases hr : r = 0
    · exact Filter.Eventually.of_forall fun m => by simpa [hr] using zero_lt_iff.2 hd0
    · obtain ⟨m₀, hm₀⟩ := exists_pow_lt₀ hc (Units.mk0 (d / r) (div_ne_zero hd0 hr))
      refine Filter.eventually_atTop.2 ⟨m₀, fun m hm => ?_⟩
      have h1 : c ^ m < d / r := (pow_le_pow_right_of_le_one' hc.le hm).trans_lt hm₀
      exact (lt_div_iff₀ (zero_lt_iff.2 hr)).1 h1
  obtain ⟨m, hm1, hm2⟩ := ((mapClusterPt_iff_frequently.1 hcl _ hN).and_eventually hev).exists
  have h1 := hF _ _ (hin m) hp' d (fun l => (hm1 l).le) j
  rw [← Function.iterate_succ_apply' F m] at h1
  have h2 : valuation E (F^[m + 1] 0 j - F p j) < d :=
    h1.trans_lt (by simpa using mul_lt_mul_of_pos_right hc (zero_lt_iff.2 hd0))
  have h3 := (hd m j).trans_lt hm2
  have e : F p j - p j = ((F^[m + 1] 0 j - F^[m] 0 j) + (F^[m] 0 j - p j)) - (F^[m + 1] 0 j - F p j) := by ring
  have : valuation E (F p j - p j) < d := by
    rw [e]
    exact Valuation.map_sub_lt _ (Valuation.map_add_lt _ h3 (hm1 j)) h2
  exact lt_irrefl _ this

omit [TopologicalSpace E] [IsNonarchimedeanLocalField E] in

/- English proof (translation)
Take `⟨i₀, -, hi₀⟩` from `Finset.exists_max_image Finset.univ (fun l => valuation E (y l)) ⟨i, Finset.mem_univ i⟩`. Use `(hi₀ i (Finset.mem_univ i)).trans ?_` and prove the remaining obligations. Assume the negation of the conclusion as `hlt`. Use `push Not at hlt`. Establish `h0 : 0 < valuation E (y i₀)` using `zero_le.trans_lt hlt`.

Establish `e : y i₀ = (M *ᵥ y) i₀ - ∑ l, (M i₀ l - (1 : Matrix (Fin n) (Fin n) E) i₀ l) * y l`. Simplify using `[sub_mul, Finset.sum_sub_distrib, mulVec, dotProduct, one_apply]`. Establish `h2 : valuation E (∑ l, (M i₀ l - (1 : Matrix (Fin n) (Fin n) E) i₀ l) * y l) ≤ r * valuation E (y i₀)` using `Valuation.map_sum_le _ fun l _ => by`. Rewrite using `[map_mul]`. Conclude with `mul_le_mul' (hM _ _) (hi₀ l (Finset.mem_univ l))`.

Establish `: valuation E (y i₀) < valuation E (y i₀)` using `by conv_lhs => rw [e]`. Conclude with `Valuation.map_sub_lt _ ((h i₀).trans_lt hlt) (h2.trans_lt (by simpa using mul_lt_mul_of_pos_right hr h0))`. Conclude with `lt_irrefl _ this`.
-/
private theorem boundB {n : ℕ} {r : ValueGroupWithZero E} (hr : r < 1) (M : Matrix (Fin n) (Fin n) E)
    (hM : ∀ i j, valuation E (M i j - (1 : Matrix (Fin n) (Fin n) E) i j) ≤ r) (y : Fin n → E)
    (ρ : ValueGroupWithZero E) (h : ∀ i, valuation E ((M *ᵥ y) i) ≤ ρ) (i : Fin n) : valuation E (y i) ≤ ρ := by
  obtain ⟨i₀, -, hi₀⟩ := Finset.exists_max_image Finset.univ (fun l => valuation E (y l)) ⟨i, Finset.mem_univ i⟩
  refine (hi₀ i (Finset.mem_univ i)).trans ?_
  by_contra hlt
  push Not at hlt
  have h0 : 0 < valuation E (y i₀) := zero_le.trans_lt hlt
  have e : y i₀ = (M *ᵥ y) i₀ - ∑ l, (M i₀ l - (1 : Matrix (Fin n) (Fin n) E) i₀ l) * y l := by
    simp [sub_mul, Finset.sum_sub_distrib, mulVec, dotProduct, one_apply]
  have h2 : valuation E (∑ l, (M i₀ l - (1 : Matrix (Fin n) (Fin n) E) i₀ l) * y l) ≤ r * valuation E (y i₀) :=
    Valuation.map_sum_le _ fun l _ => by
      rw [map_mul]; exact mul_le_mul' (hM _ _) (hi₀ l (Finset.mem_univ l))
  have : valuation E (y i₀) < valuation E (y i₀) := by
    conv_lhs => rw [e]
    exact Valuation.map_sub_lt _ ((h i₀).trans_lt hlt)
      (h2.trans_lt (by simpa using mul_lt_mul_of_pos_right hr h0))
  exact lt_irrefl _ this

/- English proof (translation)
Introduce `i j`. Use `boundB hr (a : Matrix (Fin n) (Fin n) E) ha (fun l => ((a⁻¹ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) l j - (1 : Matrix (Fin n) (Fin n) E) l j) r (fun l => ?_) i` and prove the remaining obligations. Establish `e : (a : Matrix (Fin n) (Fin n) E) * (((a⁻¹ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) - 1) = 1 - a`. Rewrite using `[mul_sub, ← Units.val_mul, mul_inv_cancel, mul_one, Units.val_one]`. Establish `e2` using `congrFun (congrFun e l) j`.

Use `ha l j` as an intermediate fact. Rewrite `this` using `[← Valuation.map_neg, neg_sub, ← Matrix.sub_apply, ← e2]`. Conclude with `this`.
-/
private theorem ball_invB {n : ℕ} {r : ValueGroupWithZero E} (hr : r < 1) {a : GL (Fin n) E} (ha : a ∈ ball n r) :
    a⁻¹ ∈ ball n r := by
  intro i j
  refine boundB hr (a : Matrix (Fin n) (Fin n) E) ha
    (fun l => ((a⁻¹ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) l j - (1 : Matrix (Fin n) (Fin n) E) l j) r
    (fun l => ?_) i
  have e : (a : Matrix (Fin n) (Fin n) E) * (((a⁻¹ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) - 1) = 1 - a := by
    rw [mul_sub, ← Units.val_mul, mul_inv_cancel, mul_one, Units.val_one]
  have e2 := congrFun (congrFun e l) j
  have := ha l j
  rw [← Valuation.map_neg, neg_sub, ← Matrix.sub_apply, ← e2] at this
  exact this

/- English proof (translation)
Introduce `i j`. Establish `e : ((a * b : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) - 1 = ((a : Matrix (Fin n) (Fin n) E) - 1) * ((b : Matrix (Fin n) (Fin n) E) - 1) + ((a : Matrix (Fin n) (Fin n) E) - 1) + ((b : Matrix (Fin n) (Fin n) E) - 1)`. Rewrite using `[Units.val_mul]`. Use `noncomm_ring`. Rewrite using `[← Matrix.sub_apply, e, Matrix.add_apply, Matrix.add_apply, Matrix.mul_apply]`.

Use `Valuation.map_add_le _ (Valuation.map_add_le _ (Valuation.map_sum_le _ fun l _ => ?_) (ha i j)) (hb i j)` and prove the remaining obligations. Rewrite using `[map_mul]`. Conclude with `(mul_le_mul' (ha i l) ((hb l j).trans hr.le)).trans (mul_one r).le`.
-/
private theorem ball_mulB {n : ℕ} {r : ValueGroupWithZero E} (hr : r < 1) {a b : GL (Fin n) E} (ha : a ∈ ball n r)
    (hb : b ∈ ball n r) : a * b ∈ ball n r := by
  intro i j
  have e : ((a * b : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) - 1 =
      ((a : Matrix (Fin n) (Fin n) E) - 1) * ((b : Matrix (Fin n) (Fin n) E) - 1) +
        ((a : Matrix (Fin n) (Fin n) E) - 1) + ((b : Matrix (Fin n) (Fin n) E) - 1) := by
    rw [Units.val_mul]; noncomm_ring
  rw [← Matrix.sub_apply, e, Matrix.add_apply, Matrix.add_apply, Matrix.mul_apply]
  refine Valuation.map_add_le _ (Valuation.map_add_le _ (Valuation.map_sum_le _ fun l _ => ?_) (ha i j)) (hb i j)
  rw [map_mul]
  exact (mul_le_mul' (ha i l) ((hb l j).trans hr.le)).trans (mul_one r).le

/- English proof (translation)
Introduce `i j`. Use `ha i j` as an intermediate fact. Rewrite `this` using `[← hσ, map_sub]`. Establish `e : σ ((1 : Matrix (Fin n) (Fin n) E) i j) = (1 : Matrix (Fin n) (Fin n) E) i j`. Simplify using `[one_apply, apply_ite σ]`.

Rewrite `this` using `[e]`. Conclude with `this`.
-/
private theorem ball_sgB {n : ℕ} {r : ValueGroupWithZero E} {σ : E ≃+* E} (hσ : Isom σ) {a : GL (Fin n) E}
    (ha : a ∈ ball n r) : sg σ a ∈ ball n r := by
  intro i j
  have := ha i j
  rw [← hσ, map_sub] at this
  have e : σ ((1 : Matrix (Fin n) (Fin n) E) i j) = (1 : Matrix (Fin n) (Fin n) E) i j := by
    simp [one_apply, apply_ite σ]
  rw [e] at this
  exact this

/- English proof (translation)
Establish `hσ' : ∀ x, valuation E (σ.symm x) = valuation E x` using `fun x => by rw [← hσ, RingEquiv.apply_symm_apply]`. Establish `hr1 : r ≤ 1` using `hr.trans hc.le`. Set `w : (Fin n → E) → Fin n → E` to `fun u j => ∑ l, (e l + β l * u l) * m l j`. Establish `hw : ∀ u, (∀ j, valuation E (u j) ≤ r) → ∀ j, valuation E (w u j) ≤ r` using `fun u hu j => Valuation.map_sum_le _ fun l _ => by`. Rewrite using `[map_mul]`.

Use `(mul_le_mul' (Valuation.map_add_le _ (he l) ?_) (hm l j)).trans (one_mul r).le` and prove the remaining obligations. Rewrite using `[map_mul]`. Conclude with `mul_le_one' (hβ1 l) ((hu l).trans hr1)`. Establish `hw' : ∀ u u' : Fin n → E, ∀ ρ, (∀ j, valuation E (u j - u' j) ≤ ρ) → ∀ j, valuation E (w u j - w u' j) ≤ c * ρ` using `fun u u' ρ h j => by`. Rewrite using `[← Finset.sum_sub_distrib]`.

Use `Valuation.map_sum_le _ fun l _ => ?_` and prove the remaining obligations. Rewrite using `[show (e l + β l * u l) * m l j - (e l + β l * u' l) * m l j = β l * (m l j * (u l - u' l)) by ring, map_mul, map_mul]`. Conclude with `(mul_le_mul' (hβ1 l) (mul_le_mul' ((hm l j).trans hr) (h l))).trans (one_mul _).le`. Establish `key : ∀ (x x' y y' : E) (ρ : ValueGroupWithZero E), valuation E x ≤ c → valuation E y' ≤ 1 → valuation E (x - x') ≤ c * ρ → valuation E (y - y') ≤ ρ → valuation E (x * σ y - x' * σ y') ≤ c * ρ`. Introduce `x x' y y' ρ h1 h2 h3 h4`.

Rewrite using `[show x * σ y - x' * σ y' = x * σ (y - y') + (x - x') * σ y' by rw [map_sub]; ring]`. Use `Valuation.map_add_le _ ?_ ?_` and prove the remaining obligations. Rewrite using `[map_mul, hσ]`. Conclude with `mul_le_mul' h1 h4`. Rewrite using `[map_mul, hσ]`.

Conclude with `(mul_le_mul' h3 h2).trans (mul_one _).le`. Take `⟨u, hu, hfix⟩` from `fixB r c hc (fun u j => if P j then σ.symm (β j * u j + w u j - w u i * σ (u j)) else σ (α j * u j) + w u i * σ (α j * u j) - w u j) (by`. Introduce `u hu j`. Use `split_ifs with h`. Rewrite using `[hσ']`.

Use `Valuation.map_sub_le _ (Valuation.map_add_le _ ?_ (hw u hu j)) ?_` and prove the remaining obligations. Rewrite using `[map_mul]`. Conclude with `(mul_le_mul' (hβ1 j) (hu j)).trans (one_mul _).le`. Rewrite using `[map_mul, hσ]`. Conclude with `(mul_le_mul' ((hw u hu i).trans hr1) (hu j)).trans (one_mul _).le`.

Establish `h1 : valuation E (σ (α j * u j)) ≤ r`. Rewrite using `[hσ, map_mul]`. Conclude with `(mul_le_mul' ((hα j h).trans hc.le) (hu j)).trans (one_mul _).le`. Use `Valuation.map_sub_le _ (Valuation.map_add_le _ h1 ?_) (hw u hu j)` and prove the remaining obligations. Rewrite using `[map_mul]`.

Conclude with `(mul_le_mul' ((hw u hu i).trans hr1) h1).trans (one_mul _).le)`. Use the proof step `(by`. Introduce `u u' hu hu' ρ hρ j`. Use `split_ifs with h`. Rewrite using `[← map_sub, hσ', show β j * u j + w u j - w u i * σ (u j) - (β j * u' j + w u' j - w u' i * σ (u' j)) = β j * (u j - u' j) + (w u j - w u' j) - (w u i * σ (u j) - w u' i * σ (u' j)) by ring]`.

Use `Valuation.map_sub_le _ (Valuation.map_add_le _ ?_ (hw' u u' ρ hρ j)) ?_` and prove the remaining obligations. Rewrite using `[map_mul]`. Conclude with `mul_le_mul' (hβ j h) (hρ j)`. Conclude with `key _ _ _ _ _ ((hw u hu i).trans hr) ((hu' j).trans hr1) (hw' u u' ρ hρ i) (hρ j)`. Rewrite using `[show σ (α j * u j) + w u i * σ (α j * u j) - w u j - (σ (α j * u' j) + w u' i * σ (α j * u' j) - w u' j) = σ (α j * (u j - u' j)) + (w u i * σ (α j * u j) - w u' i * σ (α j * u' j)) - (w u j - w u' j) by`.

Rewrite using `[mul_sub, map_sub]`. Use the proof step `ring]`. Establish `ha1 : valuation E (α j) ≤ 1` using `(hα j h).trans hc.le`. Use `Valuation.map_sub_le _ (Valuation.map_add_le _ ?_ ?_) (hw' u u' ρ hρ j)` and prove the remaining obligations. Rewrite using `[hσ, map_mul]`.

Conclude with `mul_le_mul' (hα j h) (hρ j)`. Use `key _ _ _ _ _ ((hw u hu i).trans hr) ?_ (hw' u u' ρ hρ i) ?_` and prove the remaining obligations. Rewrite using `[map_mul]`. Conclude with `mul_le_one' ha1 ((hu' j).trans hr1)`. Rewrite using `[← mul_sub, map_mul]`.

Conclude with `(mul_le_mul' ha1 (hρ j)).trans (one_mul _).le)`. Use `⟨u, w u, hu, hw u hu, fun _ => rfl, fun j h => ?_, fun j h => ?_⟩` and prove the remaining obligations. Use `congrFun hfix j` as an intermediate fact. Simplify using `only [if_pos h] at this`. Conclude with `(σ.symm_apply_eq.1 this).symm`.

Use `congrFun hfix j` as an intermediate fact. Simplify using `only [if_neg h] at this`. Conclude with `this.symm`.
-/
private theorem gridInteriorVertexDecompTransport {n : ℕ} {σ : E ≃+* E} (hσ : Isom σ) {r c : ValueGroupWithZero E} (hc : c < 1) (hr : r ≤ c)
    (m : Matrix (Fin n) (Fin n) E) (hm : ∀ i j, valuation E (m i j) ≤ r) (e α β : Fin n → E)
    (he : ∀ j, valuation E (e j) ≤ 1) (i : Fin n) (P : Fin n → Prop) [DecidablePred P]
    (hα : ∀ j, ¬ P j → valuation E (α j) ≤ c) (hβ : ∀ j, P j → valuation E (β j) ≤ c)
    (hβ1 : ∀ j, valuation E (β j) ≤ 1) :
    ∃ u w : Fin n → E, (∀ j, valuation E (u j) ≤ r) ∧ (∀ j, valuation E (w j) ≤ r) ∧
      (∀ j, w j = ∑ l, (e l + β l * u l) * m l j) ∧
      (∀ j, P j → σ (u j) = β j * u j + w j - w i * σ (u j)) ∧
      (∀ j, ¬ P j → u j = σ (α j * u j) + w i * σ (α j * u j) - w j) := by
  have hσ' : ∀ x, valuation E (σ.symm x) = valuation E x := fun x => by rw [← hσ, RingEquiv.apply_symm_apply]
  have hr1 : r ≤ 1 := hr.trans hc.le
  let w : (Fin n → E) → Fin n → E := fun u j => ∑ l, (e l + β l * u l) * m l j
  have hw : ∀ u, (∀ j, valuation E (u j) ≤ r) → ∀ j, valuation E (w u j) ≤ r := fun u hu j =>
    Valuation.map_sum_le _ fun l _ => by
      rw [map_mul]
      refine (mul_le_mul' (Valuation.map_add_le _ (he l) ?_) (hm l j)).trans (one_mul r).le
      rw [map_mul]
      exact mul_le_one' (hβ1 l) ((hu l).trans hr1)
  have hw' : ∀ u u' : Fin n → E, ∀ ρ, (∀ j, valuation E (u j - u' j) ≤ ρ) →
      ∀ j, valuation E (w u j - w u' j) ≤ c * ρ := fun u u' ρ h j => by
    rw [← Finset.sum_sub_distrib]
    refine Valuation.map_sum_le _ fun l _ => ?_
    rw [show (e l + β l * u l) * m l j - (e l + β l * u' l) * m l j = β l * (m l j * (u l - u' l)) by ring,
      map_mul, map_mul]
    exact (mul_le_mul' (hβ1 l) (mul_le_mul' ((hm l j).trans hr) (h l))).trans (one_mul _).le
  have key : ∀ (x x' y y' : E) (ρ : ValueGroupWithZero E), valuation E x ≤ c → valuation E y' ≤ 1 →
      valuation E (x - x') ≤ c * ρ → valuation E (y - y') ≤ ρ → valuation E (x * σ y - x' * σ y') ≤ c * ρ := by
    intro x x' y y' ρ h1 h2 h3 h4
    rw [show x * σ y - x' * σ y' = x * σ (y - y') + (x - x') * σ y' by rw [map_sub]; ring]
    refine Valuation.map_add_le _ ?_ ?_
    · rw [map_mul, hσ]; exact mul_le_mul' h1 h4
    · rw [map_mul, hσ]; exact (mul_le_mul' h3 h2).trans (mul_one _).le
  obtain ⟨u, hu, hfix⟩ := fixB r c hc
    (fun u j => if P j then σ.symm (β j * u j + w u j - w u i * σ (u j))
      else σ (α j * u j) + w u i * σ (α j * u j) - w u j)
    (by
      intro u hu j
      split_ifs with h
      · rw [hσ']
        refine Valuation.map_sub_le _ (Valuation.map_add_le _ ?_ (hw u hu j)) ?_
        · rw [map_mul]; exact (mul_le_mul' (hβ1 j) (hu j)).trans (one_mul _).le
        · rw [map_mul, hσ]; exact (mul_le_mul' ((hw u hu i).trans hr1) (hu j)).trans (one_mul _).le
      · have h1 : valuation E (σ (α j * u j)) ≤ r := by
          rw [hσ, map_mul]; exact (mul_le_mul' ((hα j h).trans hc.le) (hu j)).trans (one_mul _).le
        refine Valuation.map_sub_le _ (Valuation.map_add_le _ h1 ?_) (hw u hu j)
        rw [map_mul]; exact (mul_le_mul' ((hw u hu i).trans hr1) h1).trans (one_mul _).le)
    (by
      intro u u' hu hu' ρ hρ j
      split_ifs with h
      · rw [← map_sub, hσ', show β j * u j + w u j - w u i * σ (u j) - (β j * u' j + w u' j - w u' i * σ (u' j)) =
          β j * (u j - u' j) + (w u j - w u' j) - (w u i * σ (u j) - w u' i * σ (u' j)) by ring]
        refine Valuation.map_sub_le _ (Valuation.map_add_le _ ?_ (hw' u u' ρ hρ j)) ?_
        · rw [map_mul]; exact mul_le_mul' (hβ j h) (hρ j)
        · exact key _ _ _ _ _ ((hw u hu i).trans hr) ((hu' j).trans hr1) (hw' u u' ρ hρ i) (hρ j)
      · rw [show σ (α j * u j) + w u i * σ (α j * u j) - w u j - (σ (α j * u' j) + w u' i * σ (α j * u' j) - w u' j) =
          σ (α j * (u j - u' j)) + (w u i * σ (α j * u j) - w u' i * σ (α j * u' j)) - (w u j - w u' j) by
            rw [mul_sub, map_sub]; ring]
        have ha1 : valuation E (α j) ≤ 1 := (hα j h).trans hc.le
        refine Valuation.map_sub_le _ (Valuation.map_add_le _ ?_ ?_) (hw' u u' ρ hρ j)
        · rw [hσ, map_mul]; exact mul_le_mul' (hα j h) (hρ j)
        · refine key _ _ _ _ _ ((hw u hu i).trans hr) ?_ (hw' u u' ρ hρ i) ?_
          · rw [map_mul]; exact mul_le_one' ha1 ((hu' j).trans hr1)
          · rw [← mul_sub, map_mul]; exact (mul_le_mul' ha1 (hρ j)).trans (one_mul _).le)
  refine ⟨u, w u, hu, hw u hu, fun _ => rfl, fun j h => ?_, fun j h => ?_⟩
  · have := congrFun hfix j
    simp only [if_pos h] at this
    exact (σ.symm_apply_eq.1 this).symm
  · have := congrFun hfix j
    simp only [if_neg h] at this
    exact this.symm

/- English proof (translation)
Set `α : Fin n → E` to `fun j => if j < i then 1 else if j = i then 0 else (t i : E) / t j`. Set `β : Fin n → E` to `fun j => if j < i then (t j : E) / t i else if j = i then 0 else 1`. Establish `hq : ∀ p q, p < q → valuation E ((t p : E) / t q) ≤ uniformizer E` using `fun p q h => by`. Rewrite using `[le_uniformizer_iff, map_div₀, div_lt_one₀ (zero_lt_iff.2 (by simp))]`. Conclude with `ht p q h`.

Establish `hα : ∀ j, ¬ j < i → valuation E (α j) ≤ uniformizer E` using `fun j h => by`. Simplify using `only [α, if_neg h]`. Use `split_ifs with h'`. Simplify using the standard rewrite rules. Conclude with `hq _ _ (by omega)`.

Establish `hβ : ∀ j, j < i → valuation E (β j) ≤ uniformizer E` using `fun j h => by`. Simplify using `only [β, if_pos h]`. Conclude with `hq _ _ h`. Establish `hα1 : ∀ j, valuation E (α j) ≤ 1` using `fun j => by`. Distinguish the cases in `h : j < i`.

Simplify using `[α, h]`. Conclude with `(hα j h).trans uniformizer_lt_one.le`. Establish `hβ1 : ∀ j, valuation E (β j) ≤ 1` using `fun j => by`. Distinguish the cases in `h : j < i`. Conclude with `(hβ j h).trans uniformizer_lt_one.le`.

Apply the tactic sequence `simp only [β, if_neg h] split_ifs <;> simp`. Establish `hαβ : ∀ j, α j * t j = t i * β j` using `fun j => by`. Simplify using `only [α, β]`. Apply the tactic sequence `split_ifs <;> field_simp`. Simplify using the standard rewrite rules.

Apply the tactic sequence `obtain ⟨u, w, hu, hw, hw', h1, h2⟩ := gridInteriorVertexDecompTransport hσ uniformizer_lt_one (le_uniformizer_iff.2 hr) (b - 1) hb (fun j => (1 : Matrix (Fin n) (Fin n) E) i j) α β (fun j => by rw [one_apply]; split_ifs <;> simp) i (· < i) hα hβ hβ1`. Use `⟨fun j => (1 : Matrix (Fin n) (Fin n) E) i j + α j * u j, 1 + w i, fun j => ?_, by simpa using hw i, fun j => ?_⟩` and prove the remaining obligations. Rewrite using `[add_sub_cancel_left, map_mul]`. Conclude with `(mul_le_mul' (hα1 j) (hu j)).trans (one_mul _).le`. Establish `e1 : ∀ l, ((1 : Matrix (Fin n) (Fin n) E) i l + α l * u l) * (t l : E) = t i * ((1 : Matrix (Fin n) (Fin n) E) i l + β l * u l)` using `fun l => by`.

Establish `: (1 : Matrix (Fin n) (Fin n) E) i l * (t l : E) = t i * (1 : Matrix (Fin n) (Fin n) E) i l`. Distinguish the cases in `h : i = l`. Substitute `h` using the available equality. Simplify using the standard rewrite rules. Simplify using `[one_apply_ne h]`.

Take the linear combination `this + u l * hαβ l`. Establish `e2 : ∑ l, ((1 : Matrix (Fin n) (Fin n) E) i l + β l * u l) * b l j = (1 : Matrix (Fin n) (Fin n) E) i j + β j * u j + w j`. Rewrite using `[hw' j]`. Simplify using `only [Matrix.sub_apply, mul_sub, Finset.sum_sub_distrib, one_apply (i := _) (j := j), mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]`. Expand and normalize the polynomial expressions, which then agree.

Simplify using `only [e1, mul_assoc]`. Rewrite using `[← Finset.mul_sum, e2]`. Use `congr 1`. Break down `lt_trichotomy j i with h | h | h` into its components or cases. Use `h1 j h` as an intermediate fact.

Establish `ea : α j = 1` using `by simp [α, h]`. Rewrite using `[one_apply_ne h.ne', ea, one_mul, zero_add, zero_add]`. Take the linear combination `-this`. Substitute `h` using the available equality. Simplify using `[α, β]`.

Use `h2 j h.not_gt` as an intermediate fact. Establish `eb : β j = 1` using `by simp [β, h.not_gt, h.ne']`. Rewrite using `[one_apply_ne h.ne, eb, one_mul, zero_add, zero_add]`. Take the linear combination `this`.
-/
private theorem rowB {n : ℕ} {σ : E ≃+* E} (hσ : Isom σ) {t : Fin n → Eˣ} (ht : Strict t)
    {r : ValueGroupWithZero E} (hr : r < 1) (b : Matrix (Fin n) (Fin n) E)
    (hb : ∀ i j, valuation E (b i j - (1 : Matrix (Fin n) (Fin n) E) i j) ≤ r) (i : Fin n) :
    ∃ (x : Fin n → E) (s : E), (∀ j, valuation E (x j - (1 : Matrix (Fin n) (Fin n) E) i j) ≤ r) ∧
      valuation E (s - 1) ≤ r ∧ ∀ j, ∑ l, x l * (t l : E) * b l j = (t i : E) * s * σ (x j) := by
  let α : Fin n → E := fun j => if j < i then 1 else if j = i then 0 else (t i : E) / t j
  let β : Fin n → E := fun j => if j < i then (t j : E) / t i else if j = i then 0 else 1
  have hq : ∀ p q, p < q → valuation E ((t p : E) / t q) ≤ uniformizer E := fun p q h => by
    rw [le_uniformizer_iff, map_div₀, div_lt_one₀ (zero_lt_iff.2 (by simp))]
    exact ht p q h
  have hα : ∀ j, ¬ j < i → valuation E (α j) ≤ uniformizer E := fun j h => by
    simp only [α, if_neg h]
    split_ifs with h'
    · simp
    · exact hq _ _ (by omega)
  have hβ : ∀ j, j < i → valuation E (β j) ≤ uniformizer E := fun j h => by
    simp only [β, if_pos h]
    exact hq _ _ h
  have hα1 : ∀ j, valuation E (α j) ≤ 1 := fun j => by
    by_cases h : j < i
    · simp [α, h]
    · exact (hα j h).trans uniformizer_lt_one.le
  have hβ1 : ∀ j, valuation E (β j) ≤ 1 := fun j => by
    by_cases h : j < i
    · exact (hβ j h).trans uniformizer_lt_one.le
    · simp only [β, if_neg h]
      split_ifs <;> simp
  have hαβ : ∀ j, α j * t j = t i * β j := fun j => by
    simp only [α, β]
    split_ifs <;> field_simp
    simp
  obtain ⟨u, w, hu, hw, hw', h1, h2⟩ := gridInteriorVertexDecompTransport hσ uniformizer_lt_one (le_uniformizer_iff.2 hr) (b - 1) hb
    (fun j => (1 : Matrix (Fin n) (Fin n) E) i j) α β
    (fun j => by rw [one_apply]; split_ifs <;> simp) i (· < i) hα hβ hβ1
  refine ⟨fun j => (1 : Matrix (Fin n) (Fin n) E) i j + α j * u j, 1 + w i, fun j => ?_, by simpa using hw i,
    fun j => ?_⟩
  · rw [add_sub_cancel_left, map_mul]
    exact (mul_le_mul' (hα1 j) (hu j)).trans (one_mul _).le
  · have e1 : ∀ l, ((1 : Matrix (Fin n) (Fin n) E) i l + α l * u l) * (t l : E) =
        t i * ((1 : Matrix (Fin n) (Fin n) E) i l + β l * u l) := fun l => by
      have : (1 : Matrix (Fin n) (Fin n) E) i l * (t l : E) = t i * (1 : Matrix (Fin n) (Fin n) E) i l := by
        by_cases h : i = l
        · subst h; simp
        · simp [one_apply_ne h]
      linear_combination this + u l * hαβ l
    have e2 : ∑ l, ((1 : Matrix (Fin n) (Fin n) E) i l + β l * u l) * b l j =
        (1 : Matrix (Fin n) (Fin n) E) i j + β j * u j + w j := by
      rw [hw' j]
      simp only [Matrix.sub_apply, mul_sub, Finset.sum_sub_distrib, one_apply (i := _) (j := j), mul_ite, mul_one,
        mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
      ring
    simp only [e1, mul_assoc]
    rw [← Finset.mul_sum, e2]
    congr 1
    rcases lt_trichotomy j i with h | h | h
    · have := h1 j h
      have ea : α j = 1 := by simp [α, h]
      rw [one_apply_ne h.ne', ea, one_mul, zero_add, zero_add]
      linear_combination -this
    · subst h
      simp [α, β]
    · have := h2 j h.not_gt
      have eb : β j = 1 := by simp [β, h.not_gt, h.ne']
      rw [one_apply_ne h.ne, eb, one_mul, zero_add, zero_add]
      linear_combination this

end UpperTheory.ConvolutionTheory.Loc

/- English proof (translation)
Introduce `E _ _ _ _ n σ hσ t ht r hr a ha b hb`. Establish `hb' : b * sg σ a ∈ ball n r` using `ball_mulB hr hb (ball_sgB hσ ha)`. Use `choose x s hx hs h using rowB hσ ht hr _ hb'`. Establish `hdet : (Matrix.of x).det ≠ 0`. Introduce `h0`.

Take `⟨y, hy, hy0⟩` from `Matrix.exists_mulVec_eq_zero_iff.2 h0`. Use `hy (funext fun i => ?_)` and prove the remaining obligations. Simplify using `using boundB hr (Matrix.of x) hx y 0 (fun l => by simp [hy0]) i`. Establish `hs0 : ∀ i, s i ≠ 0` using `fun i h0 => by`. Use `(hs i).trans_lt hr` as an intermediate fact.

Simplify using `[h0] at this`. Set `k : GL (Fin n) E` to `GeneralLinearGroup.mkOfDetNeZero _ hdet`. Establish `hk : k ∈ ball n r` using `hx`. Establish `e : k * diagT E (Fin n) t * (b * sg σ a) = diagT E (Fin n) (t * fun i => Units.mk0 (s i) (hs0 i)) * sg σ k`. Use extensionality with `i j`.

Rewrite using `[Units.val_mul, Units.val_mul, Units.val_mul _ (sg σ k), val_diagT, val_diagT, diagonal_mul, Matrix.mul_apply]`. Simplify using `only [mul_diagonal]`. Conclude with `h i j`. Use `⟨k * a⁻¹, ball_mulB hr hk (ball_invB hr ha), fun i => Units.mk0 (s i) (hs0 i), hs, ?_⟩` and prove the remaining obligations. Rewrite using `[map_mul (sg σ), map_inv (sg σ), mul_assoc (k * a⁻¹)⁻¹, ← mul_assoc _ (sg σ k), ← e]`.

Use `group`.
-/
theorem UpperTheory.ConvolutionTheory.Loc.contractB :
    ∀ (E : Type) [Field E] [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E] (n : ℕ) (σ : E ≃+* E), Isom σ → ∀ t : Fin n → Eˣ, Strict t → ∀ r : ValueGroupWithZero E, r < 1 →
      ∀ a ∈ ball n r, ∀ b ∈ ball n r, ∃ k ∈ ball n r, ∃ s : Fin n → Eˣ, (∀ i, valuation E ((s i : E) - 1) ≤ r) ∧
        a * diagT E (Fin n) t * b = k⁻¹ * diagT E (Fin n) (t * s) * sg σ k := by
  intro E _ _ _ _ n σ hσ t ht r hr a ha b hb
  have hb' : b * sg σ a ∈ ball n r := ball_mulB hr hb (ball_sgB hσ ha)
  choose x s hx hs h using rowB hσ ht hr _ hb'
  have hdet : (Matrix.of x).det ≠ 0 := by
    intro h0
    obtain ⟨y, hy, hy0⟩ := Matrix.exists_mulVec_eq_zero_iff.2 h0
    refine hy (funext fun i => ?_)
    simpa using boundB hr (Matrix.of x) hx y 0 (fun l => by simp [hy0]) i
  have hs0 : ∀ i, s i ≠ 0 := fun i h0 => by
    have := (hs i).trans_lt hr
    simp [h0] at this
  let k : GL (Fin n) E := GeneralLinearGroup.mkOfDetNeZero _ hdet
  have hk : k ∈ ball n r := hx
  have e : k * diagT E (Fin n) t * (b * sg σ a) =
      diagT E (Fin n) (t * fun i => Units.mk0 (s i) (hs0 i)) * sg σ k := by
    ext i j
    rw [Units.val_mul, Units.val_mul, Units.val_mul _ (sg σ k), val_diagT, val_diagT, diagonal_mul, Matrix.mul_apply]
    simp only [mul_diagonal]
    exact h i j
  refine ⟨k * a⁻¹, ball_mulB hr hk (ball_invB hr ha), fun i => Units.mk0 (s i) (hs0 i), hs, ?_⟩
  rw [map_mul (sg σ), map_inv (sg σ), mul_assoc (k * a⁻¹)⁻¹, ← mul_assoc _ (sg σ k), ← e]
  group

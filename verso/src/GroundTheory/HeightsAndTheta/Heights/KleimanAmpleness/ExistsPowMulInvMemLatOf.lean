import Mathlib
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.ImportsRestMore
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.ChartRingOverOneBlockEqChartRing
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.MemSpanOfMemIdealMod
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.AssemblyBase
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

open ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH (chartRingOver secOver)

noncomputable section

namespace PullSecsModel

section Loc

variable {S : Type} [CommRing S] {Ω : Type} [Field Ω] [Algebra S Ω]

/- English proof (translation)
Assemble the required witnesses or components as `⟨⟨r, hr⟩, 1, one_not_mem_of_prime hP, by simp⟩`.
-/
theorem self_mem_fracSub (A : Subalgebra S Ω) (P : Ideal A) [hP : P.IsPrime] {r : Ω} (hr : r ∈ A) :
    r ∈ fracSub A P :=
  ⟨⟨r, hr⟩, 1, one_not_mem_of_prime hP, by simp⟩

/- English proof (translation)
Assume the negation of the conclusion as `ha`. Establish `hJ : mulMemIdeal A a ≠ ⊤`. Introduce `hJ`. Apply `ha` to reduce the goal to its premises. Establish `h1 : (1 : A) ∈ mulMemIdeal A a` using `hJ ▸ Submodule.mem_top`.

Express the relevant statement in the definitionally equal form `((1 : A) : Ω) * a ∈ A at h1`. Rewrite `h1` using `[OneMemClass.coe_one, one_mul]`. Then use the resulting hypothesis. Take `⟨P, hP, hJP⟩` from `Ideal.exists_le_maximal _ hJ`. Use `hP.isPrime` as an intermediate fact. Take `⟨u, v, hv, huv⟩ : ∃ u v : A, v ∉ P ∧ a = (u : Ω) / v` from `h P`.

Apply `hv (hJP _)` to reduce the goal to its premises. Express the relevant statement in the definitionally equal form `(v : Ω) * a ∈ A`. Rewrite using `[huv, mul_div_cancel₀ _ (coe_ne_zero_of_not_mem hv)]`. Conclude with `u.2`.
-/
theorem mem_of_forall_fracSub (A : Subalgebra S Ω) (a : Ω)
    (h : ∀ (P : Ideal A) [P.IsPrime], a ∈ fracSub A P) : a ∈ A := by
  by_contra ha
  have hJ : mulMemIdeal A a ≠ ⊤ := by
    intro hJ
    apply ha
    have h1 : (1 : A) ∈ mulMemIdeal A a := hJ ▸ Submodule.mem_top
    change ((1 : A) : Ω) * a ∈ A at h1
    rwa [OneMemClass.coe_one, one_mul] at h1
  obtain ⟨P, hP, hJP⟩ := Ideal.exists_le_maximal _ hJ
  have := hP.isPrime
  obtain ⟨u, v, hv, huv⟩ : ∃ u v : A, v ∉ P ∧ a = (u : Ω) / v := h P
  apply hv (hJP _)
  change (v : Ω) * a ∈ A
  rw [huv, mul_div_cancel₀ _ (coe_ne_zero_of_not_mem hv)]
  exact u.2

/- English proof (translation)
Take `⟨a, b, hb, rfl⟩` from `mem_locIn.mp hu`. Conclude with `⟨Subalgebra.inclusion hAB a, Subalgebra.inclusion hAB b, hb, rfl⟩`.
-/
theorem locIn_comap_le_fracSub {A B : Subalgebra S Ω} (hAB : A ≤ B) (P : Ideal B) [P.IsPrime] (u : Ω)
    (hu : u ∈ IndefiniteRowSideFullHecke.Kleiman2.locIn A (P.comap (Subalgebra.inclusion hAB))) : u ∈ fracSub B P := by
  obtain ⟨a, b, hb, rfl⟩ := mem_locIn.mp hu
  exact ⟨Subalgebra.inclusion hAB a, Subalgebra.inclusion hAB b, hb, rfl⟩

end Loc

section Join

variable {S : Type} [CommRing S] {Ω : Type} [Field Ω] [Algebra S Ω]
  {K₁ : Type} [Fintype K₁] {ι₁ : K₁ → Type} [∀ k, Fintype (ι₁ k)]
  {K₀ : Type} [Fintype K₀] [DecidableEq K₀] {ι₀ : K₀ → Type} [∀ k, Fintype (ι₀ k)]
  {y₁ : (Σ k, ι₁ k) → Ω} {y₀ : (Σ k, ι₀ k) → Ω} {k₀ : K₀} {N N' : ℕ} {e : ι₀ k₀ ≃ Fin (N + 1)}
  {x' : Fin (N' + 1) → Ω}

variable (S y₁ y₀) in

abbrev joinRing (c₁ : ∀ k, ι₁ k) (c₀ : ∀ k, ι₀ k) : Subalgebra S Ω :=
  chartRingOver S (IndefiniteRowSideFullHecke.Kleiman2.joinVec y₁ y₀) (IndefiniteRowSideFullHecke.Kleiman2.joinChart c₁ c₀)

omit [Fintype K₁] [∀ k, Fintype (ι₁ k)] [Fintype K₀] [DecidableEq K₀] [∀ k, Fintype (ι₀ k)] in
/- English proof (translation)
The claim follows from `Algebra.adjoin_le (by rintro _ ⟨⟨k, a⟩, rfl⟩; exact Algebra.subset_adjoin ⟨⟨Sum.inl k, a⟩, rfl⟩)`.
-/
theorem chartRingOver_le_join₁ (c₁ : ∀ k, ι₁ k) (c₀ : ∀ k, ι₀ k) :
    chartRingOver S y₁ c₁ ≤ joinRing S y₁ y₀ c₁ c₀ :=
  Algebra.adjoin_le (by rintro _ ⟨⟨k, a⟩, rfl⟩; exact Algebra.subset_adjoin ⟨⟨Sum.inl k, a⟩, rfl⟩)

omit [Fintype K₁] [∀ k, Fintype (ι₁ k)] [Fintype K₀] [DecidableEq K₀] [∀ k, Fintype (ι₀ k)] in
/- English proof (translation)
The claim follows from `Algebra.adjoin_le (by rintro _ ⟨⟨k, a⟩, rfl⟩; exact Algebra.subset_adjoin ⟨⟨Sum.inr k, a⟩, rfl⟩)`.
-/
theorem chartRingOver_le_join₀ (c₁ : ∀ k, ι₁ k) (c₀ : ∀ k, ι₀ k) :
    chartRingOver S y₀ c₀ ≤ joinRing S y₁ y₀ c₁ c₀ :=
  Algebra.adjoin_le (by rintro _ ⟨⟨k, a⟩, rfl⟩; exact Algebra.subset_adjoin ⟨⟨Sum.inr k, a⟩, rfl⟩)

omit [Fintype K₁] [∀ k, Fintype (ι₁ k)] [Fintype K₀] [DecidableEq K₀] [∀ k, Fintype (ι₀ k)] in

/- English proof (translation)
Use `Algebra.adjoin_le ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨⟨k | k, a⟩, rfl⟩`. Conclude with `h₁ (Algebra.subset_adjoin ⟨⟨k, a⟩, rfl⟩)`. Conclude with `h₀ (Algebra.subset_adjoin ⟨⟨k, a⟩, rfl⟩)`.
-/
theorem joinRing_le (c₁ : ∀ k, ι₁ k) (c₀ : ∀ k, ι₀ k) (T : Subalgebra S Ω) (h₁ : chartRingOver S y₁ c₁ ≤ T)
    (h₀ : chartRingOver S y₀ c₀ ≤ T) : joinRing S y₁ y₀ c₁ c₀ ≤ T := by
  refine Algebra.adjoin_le ?_
  rintro _ ⟨⟨k | k, a⟩, rfl⟩
  · exact h₁ (Algebra.subset_adjoin ⟨⟨k, a⟩, rfl⟩)
  · exact h₀ (Algebra.subset_adjoin ⟨⟨k, a⟩, rfl⟩)

omit [∀ k, Fintype (ι₁ k)] [DecidableEq K₀] [∀ k, Fintype (ι₀ k)] in

/- English proof (translation)
Rewrite using `[Fintype.prod_sum_type]`. Simplify using `[IndefiniteRowSideFullHecke.Kleiman2.pullDeg, genInv, IndefiniteRowSideFullHecke.Kleiman2.joinVec, IndefiniteRowSideFullHecke.Kleiman2.joinChart]`.
-/
theorem prod_pullDeg (c₁ : ∀ k, ι₁ k) (c₀ : ∀ k, ι₀ k) (β : K₀ → ℤ) :
    ∏ k, IndefiniteRowSideFullHecke.Kleiman2.joinVec y₁ y₀ ⟨k, IndefiniteRowSideFullHecke.Kleiman2.joinChart c₁ c₀ k⟩ ^ (-IndefiniteRowSideFullHecke.Kleiman2.pullDeg β k) =
      genInv y₀ β c₀ := by
  rw [Fintype.prod_sum_type]
  simp [IndefiniteRowSideFullHecke.Kleiman2.pullDeg, genInv, IndefiniteRowSideFullHecke.Kleiman2.joinVec, IndefiniteRowSideFullHecke.Kleiman2.joinChart]

omit [∀ k, Fintype (ι₁ k)] [DecidableEq K₀] [∀ k, Fintype (ι₀ k)] in

/- English proof (translation)
Simplify using `only [secOver, Submodule.mem_iInf, Submodule.mem_comap, LinearMap.mulRight_apply, Subalgebra.mem_toSubmodule]`. Prove the components needed by the constructor for the conclusion. Introduce `h c₁ c₀ h₁ h₀`. Use `h (IndefiniteRowSideFullHecke.Kleiman2.joinChart c₁ c₀) (by rintro (k | k); exacts [h₁ k, h₀ k])` as an intermediate fact. Rewrite `this` using `[prod_pullDeg]`. Then use the resulting hypothesis.

Introduce `h c hc`. Apply the tactic sequence `obtain ⟨c₁, c₀, rfl⟩ : ∃ (c₁ : ∀ k, ι₁ k) (c₀ : ∀ k, ι₀ k), c = IndefiniteRowSideFullHecke.Kleiman2.joinChart c₁ c₀ := ⟨fun k => c (Sum.inl k), fun k => c (Sum.inr k), by funext k; rcases k with k | k <;> rfl⟩`. Rewrite using `[prod_pullDeg]`. Conclude with `h c₁ c₀ (fun k => hc (Sum.inl k)) (fun k => hc (Sum.inr k))`.
-/
theorem mem_secOver_join_iff (β : K₀ → ℤ) (t : Ω) :
    t ∈ secOver S (IndefiniteRowSideFullHecke.Kleiman2.joinVec y₁ y₀) (IndefiniteRowSideFullHecke.Kleiman2.pullDeg β) ↔
      ∀ (c₁ : ∀ k, ι₁ k) (c₀ : ∀ k, ι₀ k), (∀ k, y₁ ⟨k, c₁ k⟩ ≠ 0) → (∀ k, y₀ ⟨k, c₀ k⟩ ≠ 0) →
        t * genInv y₀ β c₀ ∈ joinRing S y₁ y₀ c₁ c₀ := by
  simp only [secOver, Submodule.mem_iInf, Submodule.mem_comap, LinearMap.mulRight_apply,
    Subalgebra.mem_toSubmodule]
  constructor
  · intro h c₁ c₀ h₁ h₀
    have := h (IndefiniteRowSideFullHecke.Kleiman2.joinChart c₁ c₀) (by rintro (k | k); exacts [h₁ k, h₀ k])
    rwa [prod_pullDeg] at this
  · intro h c hc
    obtain ⟨c₁, c₀, rfl⟩ : ∃ (c₁ : ∀ k, ι₁ k) (c₀ : ∀ k, ι₀ k), c = IndefiniteRowSideFullHecke.Kleiman2.joinChart c₁ c₀ :=
      ⟨fun k => c (Sum.inl k), fun k => c (Sum.inr k), by funext k; rcases k with k | k <;> rfl⟩
    rw [prod_pullDeg]
    exact h c₁ c₀ (fun k => hc (Sum.inl k)) (fun k => hc (Sum.inr k))

omit [Fintype K₁] [∀ k, Fintype (ι₁ k)] in
/- English proof (translation)
Rewrite using `[baseVec_apply, Equiv.symm_apply_apply]`.
-/
theorem baseVec_e (c₀ : ∀ k, ι₀ k) : baseVec y₀ k₀ e (e (c₀ k₀)) = y₀ ⟨k₀, c₀ k₀⟩ := by
  rw [baseVec_apply, Equiv.symm_apply_apply]

omit [Fintype K₁] [∀ k, Fintype (ι₁ k)] in

/- English proof (translation)
Use `mem_of_forall_fracSub _ b fun P _ => ?_` and prove the remaining obligations. Establish `hle₁` using `chartRingOver_le_join₁ (S := S) (y₁ := y₁) (y₀ := y₀) c₁ c₀`. Establish `hz : IndefiniteRowSideFullHecke.Kleiman2.locIn _ (P.comap (Subalgebra.inclusion hle₁)) ∈ IndefiniteRowSideFullHecke.Kleiman2.modelPts S (IndefiniteRowSideFullHecke.Kleiman2.oneBlock x')`. Rewrite using `[← hsame]`. Conclude with `⟨c₁, h₁, _, inferInstance, rfl⟩`.

Take `⟨c', hc', p', hp', hz'⟩` from `hz`. Establish `hT : ∀ u ∈ IndefiniteRowSideFullHecke.Kleiman2.locIn (chartRingOver S (IndefiniteRowSideFullHecke.Kleiman2.oneBlock x') c') p', u ∈ fracSub (joinRing S y₁ y₀ c₁ c₀) P`. Introduce `u hu`. Rewrite `hu` using `[← hz']`. Conclude with `locIn_comap_le_fracSub hle₁ P u hu`.

Establish `hi' : x' (c' ()) ≠ 0` using `hc' ()`. Establish `hi : baseVec y₀ k₀ e (e (c₀ k₀)) ≠ 0` using `by rw [baseVec_e]; exact h₀ k₀`. Establish `hpair : pairRing S x' (baseVec y₀ k₀ e) (c' ()) (e (c₀ k₀)) ≤ fracSub (joinRing S y₁ y₀ c₁ c₀) P`. Use `Algebra.adjoin_le ?_` and prove the remaining obligations. Introduce and unpack `_ (⟨a, rfl⟩ | ⟨a, rfl⟩)`.

Use `hp'` as an intermediate fact. Conclude with `hT _ (subset_locIn _ p' (Algebra.subset_adjoin ⟨⟨(), a⟩, rfl⟩))`. Use `self_mem_fracSub _ P ?_` and prove the remaining obligations. Establish `: baseVec y₀ k₀ e a / baseVec y₀ k₀ e (e (c₀ k₀)) = y₀ ⟨k₀, e.symm a⟩ / y₀ ⟨k₀, c₀ k₀⟩`. Rewrite using `[baseVec_e, baseVec_apply]`.

Use `show baseVec y₀ k₀ e a / baseVec y₀ k₀ e (e (c₀ k₀)) ∈ _`. Rewrite using `[this]`. Conclude with `chartRingOver_le_join₀ c₁ c₀ (div_mem_chartRingOver c₀ k₀ _)`. Conclude with `hpair (mem_pairRing_of_mem_domRing hi' hi hb)`.
-/
theorem domRing_le_join (hsame : IndefiniteRowSideFullHecke.Kleiman2.SameModel S y₁ (IndefiniteRowSideFullHecke.Kleiman2.oneBlock x'))
    (c₁ : ∀ k, ι₁ k) (c₀ : ∀ k, ι₀ k) (h₁ : ∀ k, y₁ ⟨k, c₁ k⟩ ≠ 0) (h₀ : ∀ k, y₀ ⟨k, c₀ k⟩ ≠ 0) {b : Ω}
    (hb : b ∈ Kleiman.domRing S (baseVec y₀ k₀ e) x' (e (c₀ k₀))) : b ∈ joinRing S y₁ y₀ c₁ c₀ := by
  refine mem_of_forall_fracSub _ b fun P _ => ?_
  have hle₁ := chartRingOver_le_join₁ (S := S) (y₁ := y₁) (y₀ := y₀) c₁ c₀
  have hz : IndefiniteRowSideFullHecke.Kleiman2.locIn _ (P.comap (Subalgebra.inclusion hle₁)) ∈
      IndefiniteRowSideFullHecke.Kleiman2.modelPts S (IndefiniteRowSideFullHecke.Kleiman2.oneBlock x') := by
    rw [← hsame]
    exact ⟨c₁, h₁, _, inferInstance, rfl⟩
  obtain ⟨c', hc', p', hp', hz'⟩ := hz
  have hT : ∀ u ∈ IndefiniteRowSideFullHecke.Kleiman2.locIn (chartRingOver S (IndefiniteRowSideFullHecke.Kleiman2.oneBlock x') c') p',
      u ∈ fracSub (joinRing S y₁ y₀ c₁ c₀) P := by
    intro u hu
    rw [← hz'] at hu
    exact locIn_comap_le_fracSub hle₁ P u hu
  have hi' : x' (c' ()) ≠ 0 := hc' ()
  have hi : baseVec y₀ k₀ e (e (c₀ k₀)) ≠ 0 := by rw [baseVec_e]; exact h₀ k₀
  have hpair : pairRing S x' (baseVec y₀ k₀ e) (c' ()) (e (c₀ k₀)) ≤ fracSub (joinRing S y₁ y₀ c₁ c₀) P := by
    refine Algebra.adjoin_le ?_
    rintro _ (⟨a, rfl⟩ | ⟨a, rfl⟩)
    · have := hp'
      exact hT _ (subset_locIn _ p' (Algebra.subset_adjoin ⟨⟨(), a⟩, rfl⟩))
    · refine self_mem_fracSub _ P ?_
      have : baseVec y₀ k₀ e a / baseVec y₀ k₀ e (e (c₀ k₀)) = y₀ ⟨k₀, e.symm a⟩ / y₀ ⟨k₀, c₀ k₀⟩ := by
        rw [baseVec_e, baseVec_apply]
      show baseVec y₀ k₀ e a / baseVec y₀ k₀ e (e (c₀ k₀)) ∈ _
      rw [this]
      exact chartRingOver_le_join₀ c₁ c₀ (div_mem_chartRingOver c₀ k₀ _)
  exact hpair (mem_pairRing_of_mem_domRing hi' hi hb)

omit [Fintype K₁] [∀ k, Fintype (ι₁ k)] in

/- English proof (translation)
Establish `hM : ∀ d' : ∀ k, ι₀ k, ∃ M : ℕ, (∀ k, y₀ ⟨k, d' k⟩ ≠ 0) → (f : Ω) ^ M * ((genInv y₀ β d)⁻¹ * genInv y₀ β d') ∈ overRing (S` using `S) y₀ k₀ e d' i := by`. Introduce `d'`. Distinguish the cases in `hd' : ∀ k, y₀ ⟨k, d' k⟩ ≠ 0`. Establish `hfB : (f : Ω) ∈ overRing (S` using `S) y₀ k₀ e d' i := chartRing_le_overRing d' i f.2`. Establish `hdP : chartRingOver S y₀ d ≤ powMulMem _ (f : Ω) hfB` using `hdle.trans (powMulMem_mono (chartRing_le_overRing d' i) f.2)`.

Establish `hd'P : chartRingOver S y₀ d' ≤ powMulMem _ (f : Ω) hfB` using `(chartRingOver_le_overRing d' i).trans (le_powMulMem _ hfB)`. Establish `hratio : (genInv y₀ β d)⁻¹ * genInv y₀ β d' = ∏ k, (y₀ ⟨k, d k⟩ / y₀ ⟨k, d' k⟩) ^ β k`. Rewrite using `[inv_mul_eq_div]`. Simplify using `only [genInv]`. Rewrite using `[← Finset.prod_div_distrib]`.

Use `Finset.prod_congr rfl fun k _ => ?_` and prove the remaining obligations. Rewrite using `[zpow_neg, zpow_neg, inv_div_inv, div_zpow]`. Establish `hrP : (genInv y₀ β d)⁻¹ * genInv y₀ β d' ∈ powMulMem _ (f : Ω) hfB`. Rewrite using `[hratio]`. Use `Subalgebra.prod_mem _ fun k _ => zpow_mem_of_inv_mem _ ?_ ?_ _` and prove the remaining obligations.

Conclude with `hd'P (div_mem_chartRingOver d' k _)`. Rewrite using `[inv_div]`. Conclude with `hdP (div_mem_chartRingOver d k _)`. Take `⟨M, hM⟩` from `hrP`. Conclude with `⟨M, fun _ => hM⟩`.

Conclude with `⟨0, fun h => absurd h hd'⟩`. Use `choose M hM using hM`. Use `⟨∑ d', M d', fun d' hd' => ?_⟩` and prove the remaining obligations. Rewrite using `[mul_assoc]`. Conclude with `pow_mul_mem_of_le _ (chartRing_le_overRing d' i f.2) (Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ d')) (hM d' hd')`.
-/
theorem exists_pow_mul_inv_mem_latOf (β : K₀ → ℤ) (i : Fin (N + 1))
    (f : ReciprocityTheory.ChartRestriction.G.Geo.chartRing S (baseVec y₀ k₀ e) i) {d : ∀ k, ι₀ k}
    (hdle : chartRingOver S y₀ d ≤ powMulMem _ (f : Ω) f.2) :
    ∃ n : ℕ, (f : Ω) ^ n * (genInv y₀ β d)⁻¹ ∈ latOf (S := S) y₀ k₀ e β i := by
  have hM : ∀ d' : ∀ k, ι₀ k, ∃ M : ℕ, (∀ k, y₀ ⟨k, d' k⟩ ≠ 0) →
      (f : Ω) ^ M * ((genInv y₀ β d)⁻¹ * genInv y₀ β d') ∈ overRing (S := S) y₀ k₀ e d' i := by
    intro d'
    by_cases hd' : ∀ k, y₀ ⟨k, d' k⟩ ≠ 0
    · have hfB : (f : Ω) ∈ overRing (S := S) y₀ k₀ e d' i := chartRing_le_overRing d' i f.2
      have hdP : chartRingOver S y₀ d ≤ powMulMem _ (f : Ω) hfB :=
        hdle.trans (powMulMem_mono (chartRing_le_overRing d' i) f.2)
      have hd'P : chartRingOver S y₀ d' ≤ powMulMem _ (f : Ω) hfB :=
        (chartRingOver_le_overRing d' i).trans (le_powMulMem _ hfB)
      have hratio : (genInv y₀ β d)⁻¹ * genInv y₀ β d' = ∏ k, (y₀ ⟨k, d k⟩ / y₀ ⟨k, d' k⟩) ^ β k := by
        rw [inv_mul_eq_div]
        simp only [genInv]
        rw [← Finset.prod_div_distrib]
        refine Finset.prod_congr rfl fun k _ => ?_
        rw [zpow_neg, zpow_neg, inv_div_inv, div_zpow]
      have hrP : (genInv y₀ β d)⁻¹ * genInv y₀ β d' ∈ powMulMem _ (f : Ω) hfB := by
        rw [hratio]
        refine Subalgebra.prod_mem _ fun k _ => zpow_mem_of_inv_mem _ ?_ ?_ _
        · exact hd'P (div_mem_chartRingOver d' k _)
        · rw [inv_div]; exact hdP (div_mem_chartRingOver d k _)
      obtain ⟨M, hM⟩ := hrP
      exact ⟨M, fun _ => hM⟩
    · exact ⟨0, fun h => absurd h hd'⟩
  choose M hM using hM
  refine ⟨∑ d', M d', fun d' hd' => ?_⟩
  rw [mul_assoc]
  exact pow_mul_mem_of_le _ (chartRing_le_overRing d' i f.2)
    (Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ d')) (hM d' hd')

omit [Fintype K₁] [∀ k, Fintype (ι₁ k)] in

/- English proof (translation)
Use extensionality with `t`. Rewrite using `[mem_secs_iff]`. Simplify using `only [secOver, Submodule.mem_iInf, Submodule.mem_comap, LinearMap.mulRight_apply, Subalgebra.mem_toSubmodule]`. Prove the components needed by the constructor for the conclusion. Introduce `h d hd`.

Establish `hi : baseVec y₀ k₀ e (e (d k₀)) ≠ 0` using `by rw [baseVec_e]; exact hd k₀`. Establish `h1` using `(mem_twist_single hy β c hi t).mp (h _ hi) d hd`. Rewrite `h1` using `[overRing_self]`. Conclude with `h1`. Introduce `h i hi`.

Conclude with `(mem_twist_single hy β c hi t).mpr fun d hd => chartRingOver_le_overRing d i (h d hd)`.
-/
theorem secs_bundleOfDeg (hy : IndefiniteRowSideFullHecke.Kleiman2.IsModelWithBase S y₀ k₀) (β : K₀ → ℤ) (c : ℤ) :
    ((TranslateEq.ofSecond (bundleOfDeg (e := e) hy β)).twist (Kleiman.twistSys S (baseVec y₀ k₀ e) c)).secs =
      secOver S y₀ (β + c • IndefiniteRowSideFullHecke.Kleiman2.baseDeg k₀) := by
  ext t
  rw [mem_secs_iff]
  simp only [secOver, Submodule.mem_iInf, Submodule.mem_comap, LinearMap.mulRight_apply,
    Subalgebra.mem_toSubmodule]
  constructor
  · intro h d hd
    have hi : baseVec y₀ k₀ e (e (d k₀)) ≠ 0 := by rw [baseVec_e]; exact hd k₀
    have h1 := (mem_twist_single hy β c hi t).mp (h _ hi) d hd
    rw [overRing_self] at h1
    exact h1
  · intro h i hi
    exact (mem_twist_single hy β c hi t).mpr fun d hd => chartRingOver_le_overRing d i (h d hd)

omit [Fintype K₁] [∀ k, Fintype (ι₁ k)] in

/- English proof (translation)
Take `⟨c₁, h₁⟩` from `Kleiman.Generated.full S Ω N (baseVec y₀ k₀ e) Q`. Take `⟨c₂, h₂⟩` from `Kleiman.Generated.full S Ω N (baseVec y₀ k₀ e) (TranslateEq.ofSecond (bundleOfDeg (e := e) hy β))`. Establish `heq : (Q.twist (Kleiman.twistSys S (baseVec y₀ k₀ e) (max c₁ c₂))).sub (Kleiman.singleChart hi) = ((TranslateEq.ofSecond (bundleOfDeg (e` using `e) hy β)).twist (Kleiman.twistSys S (baseVec y₀ k₀ e) (max c₁ c₂))).sub (Kleiman.singleChart hi) := by`. Rewrite using `[← h₁ _ (le_max_left _ _), ← h₂ _ (le_max_right _ _), hQ, secs_bundleOfDeg]`. Establish `hiI : i ∈ (Kleiman.singleChart hi).1` using `Finset.mem_singleton_self i`.

Establish `hxc : baseVec y₀ k₀ e i ^ (max c₁ c₂) ≠ 0` using `zpow_ne_zero _ hi`. Express the relevant statement in the definitionally equal form `l ∈ Q.sub (Kleiman.singleChart hi) ↔ l ∈ (bundleOfDeg (e := e) hy β).lat i`. Rewrite using `[← ofSecond_sub_single (bundleOfDeg (e := e) hy β) hi l]`. Prove the components needed by the constructor for the conclusion. Introduce `hl`.

Establish `h1` using `(TranslateEq.mem_twist_twistSys_iff Q.toSubSystem (max c₁ c₂) _ hiI _).mpr ⟨l, hl, rfl⟩`. Rewrite `h1` using `[heq]`. Take `⟨u, hu, hul⟩` from `(TranslateEq.mem_twist_twistSys_iff _ (max c₁ c₂) _ hiI _).mp h1`. Rewrite `hul` using `[smul_eq_mul, smul_eq_mul, mul_right_inj' hxc]`. Rewrite using `[hul]` and apply the resulting hypothesis.

Introduce `hl`. Establish `h1` using `(TranslateEq.mem_twist_twistSys_iff (TranslateEq.ofSecond (bundleOfDeg (e := e) hy β)).toSubSystem (max c₁ c₂) _ hiI _).mpr ⟨l, hl, rfl⟩`. Rewrite `h1` using `[← heq]`. Take `⟨u, hu, hul⟩` from `(TranslateEq.mem_twist_twistSys_iff _ (max c₁ c₂) _ hiI _).mp h1`. Rewrite `hul` using `[smul_eq_mul, smul_eq_mul, mul_right_inj' hxc]`.

Rewrite using `[hul]` and apply the resulting hypothesis.
-/
theorem mem_sub_iff_latOf [IsNoetherianRing S] (hy : IndefiniteRowSideFullHecke.Kleiman2.IsModelWithBase S y₀ k₀) (β : K₀ → ℤ)
    (Q : Kleiman.LineBundle S (baseVec y₀ k₀ e))
    (hQ : ∀ c : ℤ, (Q.twist (Kleiman.twistSys S (baseVec y₀ k₀ e) c)).secs =
      secOver S y₀ (β + c • IndefiniteRowSideFullHecke.Kleiman2.baseDeg k₀))
    {i : Fin (N + 1)} (hi : baseVec y₀ k₀ e i ≠ 0) (l : Ω) :
    l ∈ Q.sub (Kleiman.singleChart hi) ↔ l ∈ latOf (S := S) y₀ k₀ e β i := by
  obtain ⟨c₁, h₁⟩ := Kleiman.Generated.full S Ω N (baseVec y₀ k₀ e) Q
  obtain ⟨c₂, h₂⟩ := Kleiman.Generated.full S Ω N (baseVec y₀ k₀ e) (TranslateEq.ofSecond (bundleOfDeg (e := e) hy β))
  have heq : (Q.twist (Kleiman.twistSys S (baseVec y₀ k₀ e) (max c₁ c₂))).sub (Kleiman.singleChart hi) =
      ((TranslateEq.ofSecond (bundleOfDeg (e := e) hy β)).twist
        (Kleiman.twistSys S (baseVec y₀ k₀ e) (max c₁ c₂))).sub (Kleiman.singleChart hi) := by
    rw [← h₁ _ (le_max_left _ _), ← h₂ _ (le_max_right _ _), hQ, secs_bundleOfDeg]
  have hiI : i ∈ (Kleiman.singleChart hi).1 := Finset.mem_singleton_self i
  have hxc : baseVec y₀ k₀ e i ^ (max c₁ c₂) ≠ 0 := zpow_ne_zero _ hi
  change l ∈ Q.sub (Kleiman.singleChart hi) ↔ l ∈ (bundleOfDeg (e := e) hy β).lat i
  rw [← ofSecond_sub_single (bundleOfDeg (e := e) hy β) hi l]
  constructor
  · intro hl
    have h1 := (TranslateEq.mem_twist_twistSys_iff Q.toSubSystem (max c₁ c₂) _ hiI _).mpr ⟨l, hl, rfl⟩
    rw [heq] at h1
    obtain ⟨u, hu, hul⟩ := (TranslateEq.mem_twist_twistSys_iff _ (max c₁ c₂) _ hiI _).mp h1
    rw [smul_eq_mul, smul_eq_mul, mul_right_inj' hxc] at hul
    rwa [hul]
  · intro hl
    have h1 := (TranslateEq.mem_twist_twistSys_iff (TranslateEq.ofSecond (bundleOfDeg (e := e) hy β)).toSubSystem
      (max c₁ c₂) _ hiI _).mpr ⟨l, hl, rfl⟩
    rw [← heq] at h1
    obtain ⟨u, hu, hul⟩ := (TranslateEq.mem_twist_twistSys_iff _ (max c₁ c₂) _ hiI _).mp h1
    rw [smul_eq_mul, smul_eq_mul, mul_right_inj' hxc] at hul
    rwa [hul]

omit [Fintype K₁] [∀ k, Fintype (ι₁ k)] [Fintype K₀] [DecidableEq K₀] [∀ k, Fintype (ι₀ k)] in

/- English proof (translation)
Establish `hC' : chartRingOver S (IndefiniteRowSideFullHecke.Kleiman2.oneBlock x') (fun _ => i') ≤ pairRing S x' (baseVec y₀ k₀ e) i' i` using `Algebra.adjoin_le (by rintro _ ⟨⟨⟨⟩, a⟩, rfl⟩; exact Algebra.subset_adjoin (Or.inl ⟨a, rfl⟩))`. Establish `hz : IndefiniteRowSideFullHecke.Kleiman2.locIn _ (P.comap (Subalgebra.inclusion hC')) ∈ IndefiniteRowSideFullHecke.Kleiman2.modelPts S y₁`. Rewrite using `[hsame]`. Conclude with `⟨fun _ => i', fun _ => hi', _, inferInstance, rfl⟩`. Take `⟨c₁, hc₁, p₁, hp₁, hz₁⟩` from `hz`.

Use `⟨c₁, hc₁, fun r hr => ?_⟩` and prove the remaining obligations. Use `hp₁` as an intermediate fact. Establish `hr'` using `subset_locIn _ p₁ hr`. Rewrite `hr'` using `[← hz₁]`. Conclude with `locIn_comap_le_fracSub hC' P r hr'`.
-/
theorem exists_chart₁ (hsame : IndefiniteRowSideFullHecke.Kleiman2.SameModel S y₁ (IndefiniteRowSideFullHecke.Kleiman2.oneBlock x')) {i' : Fin (N' + 1)}
    (hi' : x' i' ≠ 0) (i : Fin (N + 1)) (P : Ideal (pairRing S x' (baseVec y₀ k₀ e) i' i)) [P.IsPrime] :
    ∃ c₁ : ∀ k, ι₁ k, (∀ k, y₁ ⟨k, c₁ k⟩ ≠ 0) ∧
      chartRingOver S y₁ c₁ ≤ fracSub (pairRing S x' (baseVec y₀ k₀ e) i' i) P := by
  have hC' : chartRingOver S (IndefiniteRowSideFullHecke.Kleiman2.oneBlock x') (fun _ => i') ≤ pairRing S x' (baseVec y₀ k₀ e) i' i :=
    Algebra.adjoin_le (by rintro _ ⟨⟨⟨⟩, a⟩, rfl⟩; exact Algebra.subset_adjoin (Or.inl ⟨a, rfl⟩))
  have hz : IndefiniteRowSideFullHecke.Kleiman2.locIn _ (P.comap (Subalgebra.inclusion hC')) ∈ IndefiniteRowSideFullHecke.Kleiman2.modelPts S y₁ := by
    rw [hsame]
    exact ⟨fun _ => i', fun _ => hi', _, inferInstance, rfl⟩
  obtain ⟨c₁, hc₁, p₁, hp₁, hz₁⟩ := hz
  refine ⟨c₁, hc₁, fun r hr => ?_⟩
  have := hp₁
  have hr' := subset_locIn _ p₁ hr
  rw [← hz₁] at hr'
  exact locIn_comap_le_fracSub hC' P r hr'

omit [Fintype K₁] [∀ k, Fintype (ι₁ k)] in

/- English proof (translation)
Establish `hGD : ReciprocityTheory.ChartRestriction.G.Geo.chartRing S (baseVec y₀ k₀ e) i ≤ pairRing S x' (baseVec y₀ k₀ e) i' i` using `(TranslateEq.chartRing.equiv S _ hi).le.trans (chartRing_le_pairRing i' hi)`. Take `⟨f, hf, d, hd, hdle⟩` from `exists_basic hy hi (P.comap (Subalgebra.inclusion hGD))`. Establish `hf0 : (f : Ω) ≠ 0` using `coe_ne_zero_of_not_mem hf`. Establish `hfP : ∀ M : ℕ, Subalgebra.inclusion hGD (f ^ M) ∉ P`. Introduce `M hM`.

Rewrite `hM` using `[map_pow]`. Conclude with `hf (Ideal.mem_comap.mpr (Ideal.IsPrime.mem_of_pow_mem inferInstance M hM))`. Use `⟨f, hf0, d, hd, hdle, fun r hr => ?_, fun n => ?_⟩` and prove the remaining obligations. Take `⟨M, hM⟩` from `hdle hr`. Use `⟨Subalgebra.inclusion hGD ⟨_, hM⟩, Subalgebra.inclusion hGD (f ^ M), hfP M, ?_⟩` and prove the remaining obligations.

Rewrite using `[Subalgebra.coe_inclusion, Subalgebra.coe_inclusion, SubmonoidClass.coe_pow]`. Conclude with `(mul_div_cancel_left₀ r (pow_ne_zero M hf0)).symm`. Use `⟨1, Subalgebra.inclusion hGD (f ^ n), hfP n, ?_⟩` and prove the remaining obligations. Rewrite using `[OneMemClass.coe_one, Subalgebra.coe_inclusion, SubmonoidClass.coe_pow, one_div]`.
-/
theorem exists_chart₀ (hy : IndefiniteRowSideFullHecke.Kleiman2.IsModelWithBase S y₀ k₀) (i' : Fin (N' + 1)) {i : Fin (N + 1)}
    (hi : baseVec y₀ k₀ e i ≠ 0) (P : Ideal (pairRing S x' (baseVec y₀ k₀ e) i' i)) [P.IsPrime] :
    ∃ f : ReciprocityTheory.ChartRestriction.G.Geo.chartRing S (baseVec y₀ k₀ e) i, (f : Ω) ≠ 0 ∧ ∃ d : ∀ k, ι₀ k, (∀ k, y₀ ⟨k, d k⟩ ≠ 0) ∧
      chartRingOver S y₀ d ≤ powMulMem _ (f : Ω) f.2 ∧
      chartRingOver S y₀ d ≤ fracSub (pairRing S x' (baseVec y₀ k₀ e) i' i) P ∧
      ∀ n : ℕ, ((f : Ω) ^ n)⁻¹ ∈ fracSub (pairRing S x' (baseVec y₀ k₀ e) i' i) P := by
  have hGD : ReciprocityTheory.ChartRestriction.G.Geo.chartRing S (baseVec y₀ k₀ e) i ≤ pairRing S x' (baseVec y₀ k₀ e) i' i :=
    (TranslateEq.chartRing.equiv S _ hi).le.trans (chartRing_le_pairRing i' hi)
  obtain ⟨f, hf, d, hd, hdle⟩ := exists_basic hy hi (P.comap (Subalgebra.inclusion hGD))
  have hf0 : (f : Ω) ≠ 0 := coe_ne_zero_of_not_mem hf
  have hfP : ∀ M : ℕ, Subalgebra.inclusion hGD (f ^ M) ∉ P := by
    intro M hM
    rw [map_pow] at hM
    exact hf (Ideal.mem_comap.mpr (Ideal.IsPrime.mem_of_pow_mem inferInstance M hM))
  refine ⟨f, hf0, d, hd, hdle, fun r hr => ?_, fun n => ?_⟩
  · obtain ⟨M, hM⟩ := hdle hr
    refine ⟨Subalgebra.inclusion hGD ⟨_, hM⟩, Subalgebra.inclusion hGD (f ^ M), hfP M, ?_⟩
    rw [Subalgebra.coe_inclusion, Subalgebra.coe_inclusion, SubmonoidClass.coe_pow]
    exact (mul_div_cancel_left₀ r (pow_ne_zero M hf0)).symm
  · refine ⟨1, Subalgebra.inclusion hGD (f ^ n), hfP n, ?_⟩
    rw [OneMemClass.coe_one, Subalgebra.coe_inclusion, SubmonoidClass.coe_pow, one_div]

/- English proof (translation)
Rewrite using `[mem_secOver_join_iff]`. Introduce `c₁ c₀ h₁ h₀`. Establish `hi : baseVec y₀ k₀ e (e (c₀ k₀)) ≠ 0` using `by rw [baseVec_e]; exact h₀ k₀`. Simplify using `only [Kleiman.pullSecs, Submodule.mem_iInf] at ht`. Establish `ht'` using `ht _ hi`.

Use `clear ht`. Proceed by induction on `ht' using Submodule.span_induction with`. Consider the case `mem z hz`. Take `⟨b, hb, l, hl, rfl⟩` from `hz`. Establish `hl'` using `(mem_latOf β _ l).mp ((mem_sub_iff_latOf hy β Q hQ hi l).mp hl) c₀ h₀`.

Rewrite `hl'` using `[overRing_self]`. Rewrite using `[mul_assoc]`. Conclude with `Subalgebra.mul_mem _ (domRing_le_join hsame c₁ c₀ h₁ h₀ hb) (chartRingOver_le_join₀ c₁ c₀ hl')`. Consider the case `zero => rw [zero_mul]`. Conclude with `Subalgebra.zero_mem _`.

Consider the case `add u v _ _ hu hv => rw [add_mul]`. Conclude with `Subalgebra.add_mem _ hu hv`. Consider the case `smul r u _ hu`. Rewrite using `[Algebra.smul_def, mul_assoc]`. Conclude with `Subalgebra.mul_mem _ (Subalgebra.algebraMap_mem _ r) hu`.
-/
theorem mem_secOver_of_mem_pullSecs [IsNoetherianRing S] (hy : IndefiniteRowSideFullHecke.Kleiman2.IsModelWithBase S y₀ k₀)
    (hsame : IndefiniteRowSideFullHecke.Kleiman2.SameModel S y₁ (IndefiniteRowSideFullHecke.Kleiman2.oneBlock x')) (β : K₀ → ℤ)
    (Q : Kleiman.LineBundle S (baseVec y₀ k₀ e))
    (hQ : ∀ c : ℤ, (Q.twist (Kleiman.twistSys S (baseVec y₀ k₀ e) c)).secs =
      secOver S y₀ (β + c • IndefiniteRowSideFullHecke.Kleiman2.baseDeg k₀))
    (t : Ω) (ht : t ∈ Kleiman.pullSecs x' Q.toSubSystem) :
    t ∈ secOver S (IndefiniteRowSideFullHecke.Kleiman2.joinVec y₁ y₀) (IndefiniteRowSideFullHecke.Kleiman2.pullDeg β) := by
  rw [mem_secOver_join_iff]
  intro c₁ c₀ h₁ h₀
  have hi : baseVec y₀ k₀ e (e (c₀ k₀)) ≠ 0 := by rw [baseVec_e]; exact h₀ k₀
  simp only [Kleiman.pullSecs, Submodule.mem_iInf] at ht
  have ht' := ht _ hi
  clear ht
  induction ht' using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨b, hb, l, hl, rfl⟩ := hz
    have hl' := (mem_latOf β _ l).mp ((mem_sub_iff_latOf hy β Q hQ hi l).mp hl) c₀ h₀
    rw [overRing_self] at hl'
    rw [mul_assoc]
    exact Subalgebra.mul_mem _ (domRing_le_join hsame c₁ c₀ h₁ h₀ hb) (chartRingOver_le_join₀ c₁ c₀ hl')
  | zero => rw [zero_mul]; exact Subalgebra.zero_mem _
  | add u v _ _ hu hv => rw [add_mul]; exact Subalgebra.add_mem _ hu hv
  | smul r u _ hu =>
    rw [Algebra.smul_def, mul_assoc]
    exact Subalgebra.mul_mem _ (Subalgebra.algebraMap_mem _ r) hu

/- English proof (translation)
Rewrite `ht` using `[mem_secOver_join_iff]`. Simplify using `only [Kleiman.pullSecs, Submodule.mem_iInf]`. Introduce `i hi`. Take `⟨m, g, hgQ⟩` from `Submodule.fg_iff_exists_fin_generating_family.mp (Q.fg (Kleiman.singleChart hi))`. Take `⟨Q', hQ'⟩` from `Q.invertible (Kleiman.singleChart hi)`.

Establish `hlw : ∀ l ∈ Q.sub (Kleiman.singleChart hi), ∀ w ∈ Q', l * w ∈ Kleiman.chartRing S (baseVec y₀ k₀ e) (Kleiman.singleChart hi)`. Introduce `l hl w hw`. Establish `h` using `Submodule.mul_mem_mul hl hw`. Rewrite `h` using `[hQ', Submodule.mem_one]`. Take `⟨r, hr⟩` from `h`.

Rewrite using `[← hr]`. Conclude with `r.2`. Establish `hg : ∀ b, g b ∈ Q.sub (Kleiman.singleChart hi)` using `fun b => by`. Rewrite using `[← hgQ]`. Conclude with `Submodule.subset_span ⟨b, rfl⟩`.

Rewrite `hQ'` using `[← hgQ]`. Take `⟨w, hwQ, -, hsum⟩` from `exists_sum_eq_one g Q' hQ'`. Establish `htw : ∀ b, t * w b ∈ Kleiman.domRing S (baseVec y₀ k₀ e) x' i`. Introduce `b`. Use `mem_domRing_of_forall fun i' hi' => ?_` and prove the remaining obligations.

Use `mem_of_forall_fracSub _ _ fun P _ => ?_` and prove the remaining obligations. Take `⟨c₁, hc₁, h1⟩` from `exists_chart₁ (y₀ := y₀) (e := e) hsame hi' i P`. Take `⟨f, hf0, d, hd, hdle, h0, hinv⟩` from `exists_chart₀ (x' := x') hy i' hi P`. Take `⟨n, hn⟩` from `exists_pow_mul_inv_mem_latOf (S := S) (y₀ := y₀) β i f hdle`. Establish `hlwb` using `chartRing_le_pairRing (x' := x') i' hi (hlw _ ((mem_sub_iff_latOf hy β Q hQ hi _).mpr hn) (w b) (hwQ b))`.

Establish `htd` using `joinRing_le c₁ d _ h1 h0 (ht c₁ d hc₁ hd)`. Establish `hG` using `genInv_ne_zero β hd`. Establish `e1 : t * w b = t * genInv y₀ β d * ((f : Ω) ^ n * (genInv y₀ β d)⁻¹ * w b) * ((f : Ω) ^ n)⁻¹`. Clear the denominators using the available nonvanishing facts. Rewrite using `[e1]`.

Conclude with `mul_mem (mul_mem htd (self_mem_fracSub _ P hlwb)) (hinv n)`. Establish `e : t = ∑ b, t * w b * g b`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[Finset.mul_sum]; exact Finset.sum_congr rfl fun b _ => by ring`. Rewrite using `[e]`.

Conclude with `Submodule.sum_mem _ fun b _ => Submodule.subset_span ⟨t * w b, htw b, g b, hg b, rfl⟩`.
-/
theorem mem_pullSecs_of_mem_secOver [IsNoetherianRing S] (hy : IndefiniteRowSideFullHecke.Kleiman2.IsModelWithBase S y₀ k₀)
    (hsame : IndefiniteRowSideFullHecke.Kleiman2.SameModel S y₁ (IndefiniteRowSideFullHecke.Kleiman2.oneBlock x')) (β : K₀ → ℤ)
    (Q : Kleiman.LineBundle S (baseVec y₀ k₀ e))
    (hQ : ∀ c : ℤ, (Q.twist (Kleiman.twistSys S (baseVec y₀ k₀ e) c)).secs =
      secOver S y₀ (β + c • IndefiniteRowSideFullHecke.Kleiman2.baseDeg k₀))
    (t : Ω) (ht : t ∈ secOver S (IndefiniteRowSideFullHecke.Kleiman2.joinVec y₁ y₀) (IndefiniteRowSideFullHecke.Kleiman2.pullDeg β)) :
    t ∈ Kleiman.pullSecs x' Q.toSubSystem := by
  rw [mem_secOver_join_iff] at ht
  simp only [Kleiman.pullSecs, Submodule.mem_iInf]
  intro i hi
  obtain ⟨m, g, hgQ⟩ := Submodule.fg_iff_exists_fin_generating_family.mp (Q.fg (Kleiman.singleChart hi))
  obtain ⟨Q', hQ'⟩ := Q.invertible (Kleiman.singleChart hi)
  have hlw : ∀ l ∈ Q.sub (Kleiman.singleChart hi), ∀ w ∈ Q',
      l * w ∈ Kleiman.chartRing S (baseVec y₀ k₀ e) (Kleiman.singleChart hi) := by
    intro l hl w hw
    have h := Submodule.mul_mem_mul hl hw
    rw [hQ', Submodule.mem_one] at h
    obtain ⟨r, hr⟩ := h
    rw [← hr]
    exact r.2
  have hg : ∀ b, g b ∈ Q.sub (Kleiman.singleChart hi) := fun b => by
    rw [← hgQ]; exact Submodule.subset_span ⟨b, rfl⟩
  rw [← hgQ] at hQ'
  obtain ⟨w, hwQ, -, hsum⟩ := exists_sum_eq_one g Q' hQ'
  have htw : ∀ b, t * w b ∈ Kleiman.domRing S (baseVec y₀ k₀ e) x' i := by
    intro b
    refine mem_domRing_of_forall fun i' hi' => ?_
    refine mem_of_forall_fracSub _ _ fun P _ => ?_
    obtain ⟨c₁, hc₁, h1⟩ := exists_chart₁ (y₀ := y₀) (e := e) hsame hi' i P
    obtain ⟨f, hf0, d, hd, hdle, h0, hinv⟩ := exists_chart₀ (x' := x') hy i' hi P
    obtain ⟨n, hn⟩ := exists_pow_mul_inv_mem_latOf (S := S) (y₀ := y₀) β i f hdle
    have hlwb := chartRing_le_pairRing (x' := x') i' hi
      (hlw _ ((mem_sub_iff_latOf hy β Q hQ hi _).mpr hn) (w b) (hwQ b))
    have htd := joinRing_le c₁ d _ h1 h0 (ht c₁ d hc₁ hd)
    have hG := genInv_ne_zero β hd
    have e1 : t * w b =
        t * genInv y₀ β d * ((f : Ω) ^ n * (genInv y₀ β d)⁻¹ * w b) * ((f : Ω) ^ n)⁻¹ := by
      field_simp
    rw [e1]
    exact mul_mem (mul_mem htd (self_mem_fracSub _ P hlwb)) (hinv n)
  have e : t = ∑ b, t * w b * g b := by
    calc t = t * ∑ b, g b * w b := by rw [hsum, mul_one]
      _ = ∑ b, t * w b * g b := by
        rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun b _ => by ring
  rw [e]
  exact Submodule.sum_mem _ fun b _ => Submodule.subset_span ⟨t * w b, htw b, g b, hg b, rfl⟩

end Join

end PullSecsModel

/- English proof (translation)
Introduce `S _ K₁ _ ι₁ _ K₀ _ _ ι₀ _ Ω _ _ y₁ y₀ k₀ N N' e x x' hx hS _ hy _ hsame Q β hQ`. Substitute `hx` using the available equality. Use extensionality with `t`. Conclude with `⟨PullSecsModel.mem_secOver_of_mem_pullSecs hy hsame β Q hQ t, PullSecsModel.mem_pullSecs_of_mem_secOver hy hsame β Q hQ t⟩`.
-/
theorem PullSecsModel.full : PullSecsModel.Statement := by
  intro S _ K₁ _ ι₁ _ K₀ _ _ ι₀ _ Ω _ _ y₁ y₀ k₀ N N' e x x' hx hS _ hy _ hsame Q β hQ
  subst hx
  ext t
  exact ⟨PullSecsModel.mem_secOver_of_mem_pullSecs hy hsame β Q hQ t,
    PullSecsModel.mem_pullSecs_of_mem_secOver hy hsame β Q hQ t⟩

end

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

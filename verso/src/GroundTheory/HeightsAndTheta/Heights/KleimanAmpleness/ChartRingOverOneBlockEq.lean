import Mathlib
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.ImportsBisRest
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.ZpowMemSubringOfInvMem
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

open MvPolynomial
open ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH (chartRingOver secOver)

noncomputable section

namespace BaseTwistSecs

variable {S : Type} [CommRing S] {Ω : Type} [Field Ω] [Algebra S Ω]

/- English proof (translation)
Set `I : Ideal B` to `{ carrier := {a | (a : Ω) * u ∈ B} add_mem' := fun {a b} ha hb => by show ((a : Ω) + b) * u ∈ B`. Rewrite using `[add_mul]`. Conclude with `B.add_mem ha hb`. Use the proof step `zero_mem' := by show (0 : Ω) * u ∈ B; rw [zero_mul]; exact B.zero_mem`. Use the proof step `smul_mem' := fun c a ha => by show ((c : Ω) * a) * u ∈ B`.

Rewrite using `[mul_assoc]`. Conclude with `B.mul_mem c.2 ha }`. Distinguish the cases in `hI : I = ⊤`. Establish `h1 : (1 : B) ∈ I` using `hI ▸ Submodule.mem_top`. Establish `h2 : ((1 : B) : Ω) * u ∈ B` using `h1`.

Simplify using `using h2`. Take `⟨p, hp, hIp⟩` from `Ideal.exists_le_maximal I hI`. Use `hp.isPrime` as an intermediate fact. Take `⟨a, b, hb, hu⟩` from `mem_locIn.mp (h p hp)`. Establish `hb0 : (b : Ω) ≠ 0` using `coe_ne_zero_of_not_mem hb`.

Use `absurd (hIp ?_) hb` and prove the remaining obligations. Use `show (b : Ω) * u ∈ B`. Rewrite using `[hu, mul_div_cancel₀ _ hb0]`. Conclude with `a.2`.
-/
theorem mem_of_forall_mem_locIn (B : Subalgebra S Ω) {u : Ω}
    (h : ∀ p : Ideal B, p.IsMaximal → u ∈ IndefiniteRowSideFullHecke.Kleiman2.locIn B p) : u ∈ B := by
  let I : Ideal B :=
    { carrier := {a | (a : Ω) * u ∈ B}
      add_mem' := fun {a b} ha hb => by
        show ((a : Ω) + b) * u ∈ B
        rw [add_mul]; exact B.add_mem ha hb
      zero_mem' := by show (0 : Ω) * u ∈ B; rw [zero_mul]; exact B.zero_mem
      smul_mem' := fun c a ha => by
        show ((c : Ω) * a) * u ∈ B
        rw [mul_assoc]; exact B.mul_mem c.2 ha }
  by_cases hI : I = ⊤
  · have h1 : (1 : B) ∈ I := hI ▸ Submodule.mem_top
    have h2 : ((1 : B) : Ω) * u ∈ B := h1
    simpa using h2
  · obtain ⟨p, hp, hIp⟩ := Ideal.exists_le_maximal I hI
    have := hp.isPrime
    obtain ⟨a, b, hb, hu⟩ := mem_locIn.mp (h p hp)
    have hb0 : (b : Ω) ≠ 0 := coe_ne_zero_of_not_mem hb
    refine absurd (hIp ?_) hb
    show (b : Ω) * u ∈ B
    rw [hu, mul_div_cancel₀ _ hb0]
    exact a.2

/- English proof (translation)
Unfold `chartRingOver`. Use `congr 1`. Use extensionality with `z`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨⟨⟨⟩, a⟩, rfl⟩`.

Conclude with `⟨a, rfl⟩`. Introduce and unpack `⟨a, rfl⟩`. Conclude with `⟨⟨(), a⟩, rfl⟩`.
-/
theorem chartRingOver_oneBlock_eq {κ : Type} (x : κ → Ω) (c : Unit → κ) :
    chartRingOver S (IndefiniteRowSideFullHecke.Kleiman2.oneBlock x) c = Algebra.adjoin S (Set.range fun i => x i / x (c ())) := by
  unfold chartRingOver
  congr 1
  ext z
  constructor
  · rintro ⟨⟨⟨⟩, a⟩, rfl⟩
    exact ⟨a, rfl⟩
  · rintro ⟨a, rfl⟩
    exact ⟨⟨(), a⟩, rfl⟩

/- English proof (translation)
Unfold `secOver`. Simplify using `only [Submodule.mem_iInf, Submodule.mem_comap, LinearMap.mulRight_apply, Finset.univ_unique, Finset.prod_singleton, Subalgebra.mem_toSubmodule, chartRingOver_oneBlock_eq]`. Prove the components needed by the constructor for the conclusion. Introduce `h j hj`. Conclude with `h (fun _ => j) (fun _ => hj)`.

Introduce `h c hc`. Conclude with `h (c ()) (hc ())`.
-/
theorem mem_secOver_oneBlock {κ : Type} (x : κ → Ω) (n : ℤ) (t : Ω) :
    t ∈ secOver S (IndefiniteRowSideFullHecke.Kleiman2.oneBlock x) (fun _ => n) ↔
      ∀ j, x j ≠ 0 → t * x j ^ (-n) ∈ Algebra.adjoin S (Set.range fun i => x i / x j) := by
  unfold secOver
  simp only [Submodule.mem_iInf, Submodule.mem_comap, LinearMap.mulRight_apply, Finset.univ_unique,
    Finset.prod_singleton, Subalgebra.mem_toSubmodule, chartRingOver_oneBlock_eq]
  constructor
  · intro h j hj
    exact h (fun _ => j) (fun _ => hj)
  · intro h c hc
    exact h (c ()) (hc ())

/- English proof (translation)
Use extensionality with `t`. Rewrite using `[mem_secOver_oneBlock, mem_secOver_oneBlock]`. Establish `hr : ∀ j', Set.range (fun i' => x (σ i') / x (σ j')) = Set.range (fun i => x i / x (σ j'))` using `fun j' => σ.surjective.range_comp (fun i => x i / x (σ j'))`. Simplify using `only [Function.comp_apply]`. Prove the components needed by the constructor for the conclusion.

Introduce `h j hj`. Take `⟨j', rfl⟩` from `σ.surjective j`. Use `h j' hj` as an intermediate fact. Rewrite `this` using `[hr]`. Then use the resulting hypothesis. Introduce `h j' hj'`.

Rewrite using `[hr]`. Conclude with `h (σ j') hj'`.
-/
theorem secOver_oneBlock_comp {κ κ' : Type} (σ : κ' ≃ κ) (x : κ → Ω) (n : ℤ) :
    secOver S (IndefiniteRowSideFullHecke.Kleiman2.oneBlock (x ∘ σ)) (fun _ => n) = secOver S (IndefiniteRowSideFullHecke.Kleiman2.oneBlock x) (fun _ => n) := by
  ext t
  rw [mem_secOver_oneBlock, mem_secOver_oneBlock]
  have hr : ∀ j', Set.range (fun i' => x (σ i') / x (σ j')) = Set.range (fun i => x i / x (σ j')) :=
    fun j' => σ.surjective.range_comp (fun i => x i / x (σ j'))
  simp only [Function.comp_apply]
  constructor
  · intro h j hj
    obtain ⟨j', rfl⟩ := σ.surjective j
    have := h j' hj
    rwa [hr] at this
  · intro h j' hj'
    rw [hr]
    exact h (σ j') hj'

/- English proof (translation)
Use extensionality with `t`. Rewrite using `[mem_secOver_oneBlock]`. Prove the components needed by the constructor for the conclusion. Introduce `ht j hj`. Establish `htj : t ∈ Kleiman.twistMod S x n (Kleiman.singleChart hj)`.

Use `(Submodule.mem_iInf _).mp ht (Kleiman.singleChart hj)` as an intermediate fact. Conclude with `this`. Rewrite `htj` using `[Kleiman.twistMod_eq_span n _ (Finset.mem_singleton_self j), Submodule.mem_span_singleton]`. Take `⟨a, rfl⟩` from `htj`. Establish `hA` using `(chartRingOver_oneBlock x (S := S) (fun _ => j) hj).symm.trans (chartRingOver_oneBlock_eq x (fun _ => j))`.

Rewrite using `[← hA, Kleiman.chartRing_smul_def, zpow_neg, mul_assoc, mul_inv_cancel₀ (zpow_ne_zero n hj), mul_one]`. Conclude with `a.2`. Introduce `h`. Use `(Submodule.mem_iInf _).mpr fun I => ?_` and prove the remaining obligations. Take `⟨j, hjI⟩` from `I.2.1`.

Establish `hj : x j ≠ 0` using `(Kleiman.mem_support x).mp (I.2.2 hjI)`. Establish `hA` using `(chartRingOver_oneBlock x (S := S) (fun _ => j) hj).symm.trans (chartRingOver_oneBlock_eq x (fun _ => j))`. Establish `hmem : t * x j ^ (-n) ∈ Kleiman.chartRing S x I` using `Kleiman.chartRing_mono (Finset.singleton_subset_iff.mpr hjI) (hA ▸ h j hj)`. Express the relevant statement in the definitionally equal form `t ∈ Kleiman.twistMod S x n I`. Rewrite using `[Kleiman.twistMod_eq_span n I hjI, Submodule.mem_span_singleton]`.

Use `⟨⟨_, hmem⟩, ?_⟩` and prove the remaining obligations. Rewrite using `[Kleiman.chartRing_smul_def]`. Use `show t * x j ^ (-n) * x j ^ n = t`. Rewrite using `[zpow_neg]`. Conclude with `inv_mul_cancel_right₀ (zpow_ne_zero n hj) t`.
-/
theorem twistSys_secs_eq_secOver {N : ℕ} (x : Fin (N + 1) → Ω) (n : ℤ) :
    (Kleiman.twistSys S x n).secs = secOver S (IndefiniteRowSideFullHecke.Kleiman2.oneBlock x) (fun _ => n) := by
  ext t
  rw [mem_secOver_oneBlock]
  constructor
  · intro ht j hj
    have htj : t ∈ Kleiman.twistMod S x n (Kleiman.singleChart hj) := by
      have := (Submodule.mem_iInf _).mp ht (Kleiman.singleChart hj)
      exact this
    rw [Kleiman.twistMod_eq_span n _ (Finset.mem_singleton_self j), Submodule.mem_span_singleton] at htj
    obtain ⟨a, rfl⟩ := htj
    have hA := (chartRingOver_oneBlock x (S := S) (fun _ => j) hj).symm.trans (chartRingOver_oneBlock_eq x (fun _ => j))
    rw [← hA, Kleiman.chartRing_smul_def, zpow_neg, mul_assoc, mul_inv_cancel₀ (zpow_ne_zero n hj), mul_one]
    exact a.2
  · intro h
    refine (Submodule.mem_iInf _).mpr fun I => ?_
    obtain ⟨j, hjI⟩ := I.2.1
    have hj : x j ≠ 0 := (Kleiman.mem_support x).mp (I.2.2 hjI)
    have hA := (chartRingOver_oneBlock x (S := S) (fun _ => j) hj).symm.trans (chartRingOver_oneBlock_eq x (fun _ => j))
    have hmem : t * x j ^ (-n) ∈ Kleiman.chartRing S x I :=
      Kleiman.chartRing_mono (Finset.singleton_subset_iff.mpr hjI) (hA ▸ h j hj)
    change t ∈ Kleiman.twistMod S x n I
    rw [Kleiman.twistMod_eq_span n I hjI, Submodule.mem_span_singleton]
    refine ⟨⟨_, hmem⟩, ?_⟩
    rw [Kleiman.chartRing_smul_def]
    show t * x j ^ (-n) * x j ^ n = t
    rw [zpow_neg]
    exact inv_mul_cancel_right₀ (zpow_ne_zero n hj) t

variable {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type}

/- English proof (translation)
Use `set x' := IndefiniteRowSideFullHecke.Kleiman2.blockVec y k₀ with hx'`. Establish `hmem : ∀ t, t ∈ secOver S y (m • IndefiniteRowSideFullHecke.Kleiman2.baseDeg k₀) ↔ ∀ c : ∀ k, ι k, (∀ k, y ⟨k, c k⟩ ≠ 0) → t * y ⟨k₀, c k₀⟩ ^ (-m) ∈ chartRingOver S y c`. Introduce `t`. Simplify using `only [secOver, Submodule.mem_iInf, Submodule.mem_comap, LinearMap.mulRight_apply, Subalgebra.mem_toSubmodule, prod_baseDeg]`. Use extensionality with `t`.

Rewrite using `[hmem, mem_secOver_oneBlock]`. Prove the components needed by the constructor for the conclusion. Introduce `ht j hj`. Apply `mem_of_forall_mem_locIn` to reduce the goal to its premises. Introduce `p hp`.

Establish `hpp` using `hp.isPrime`. Establish `hz : IndefiniteRowSideFullHecke.Kleiman2.locIn _ p ∈ IndefiniteRowSideFullHecke.Kleiman2.modelPts S (IndefiniteRowSideFullHecke.Kleiman2.oneBlock x')`. Use `⟨fun _ => j, fun _ => hj, ?_⟩` and prove the remaining obligations. Rewrite using `[chartRingOver_oneBlock_eq]`. Conclude with `⟨p, hp.isPrime, rfl⟩`.

Rewrite `hz` using `[← hy.2]`. Take `⟨c, hc, q, hq, hzq⟩` from `hz`. Establish `hA : ∀ a ∈ chartRingOver S y c, a ∈ IndefiniteRowSideFullHecke.Kleiman2.locIn _ p` using `fun a ha => by`. Rewrite using `[hzq, mem_locIn]`. Conclude with `⟨⟨a, ha⟩, 1, fun h => one_not_mem_of_prime hq h, by simp⟩`.

Establish `hB : ∀ a ∈ Algebra.adjoin S (Set.range fun i => x' i / x' j), a ∈ IndefiniteRowSideFullHecke.Kleiman2.locIn _ p` using `fun a ha => mem_locIn.mpr ⟨⟨a, ha⟩, 1, fun h => one_not_mem_of_prime hpp h, by simp⟩`. Establish `hyc : y ⟨k₀, c k₀⟩ ≠ 0` using `hc k₀`. Establish `hr : y ⟨k₀, c k₀⟩ / x' j ∈ IndefiniteRowSideFullHecke.Kleiman2.locIn _ p` using `hB _ (Algebra.subset_adjoin ⟨c k₀, rfl⟩)`. Establish `hr' : (y ⟨k₀, c k₀⟩ / x' j)⁻¹ ∈ IndefiniteRowSideFullHecke.Kleiman2.locIn _ p`. Rewrite using `[inv_div]`.

Conclude with `hA _ (Algebra.subset_adjoin ⟨⟨k₀, j⟩, rfl⟩)`. Establish `e : t * x' j ^ (-m) = t * y ⟨k₀, c k₀⟩ ^ (-m) * (y ⟨k₀, c k₀⟩ / x' j) ^ m`. Rewrite using `[div_zpow, zpow_neg, zpow_neg]`. Clear the denominators using the available nonvanishing facts. Rewrite using `[e]`.

Conclude with `Subring.mul_mem _ (hA _ (ht c hc)) (zpow_mem_subring_of_inv_mem _ hr hr' m)`. Introduce `ht c hc`. Establish `hle : Algebra.adjoin S (Set.range fun i => x' i / x' (c k₀)) ≤ chartRingOver S y c`. Rewrite using `[Algebra.adjoin_le_iff]`. Introduce and unpack `_ ⟨i, rfl⟩`.

Conclude with `Algebra.subset_adjoin ⟨⟨k₀, i⟩, rfl⟩`. Conclude with `hle (ht (c k₀) (hc k₀))`.
-/
theorem secOver_baseDeg_eq (y : (Σ k, ι k) → Ω) (k₀ : K) (hy : IndefiniteRowSideFullHecke.Kleiman2.IsModelWithBase S y k₀) (m : ℤ) :
    secOver S y (m • IndefiniteRowSideFullHecke.Kleiman2.baseDeg k₀) =
      secOver S (IndefiniteRowSideFullHecke.Kleiman2.oneBlock (IndefiniteRowSideFullHecke.Kleiman2.blockVec y k₀)) (fun _ => m) := by
  set x' := IndefiniteRowSideFullHecke.Kleiman2.blockVec y k₀ with hx'
  have hmem : ∀ t, t ∈ secOver S y (m • IndefiniteRowSideFullHecke.Kleiman2.baseDeg k₀) ↔
      ∀ c : ∀ k, ι k, (∀ k, y ⟨k, c k⟩ ≠ 0) → t * y ⟨k₀, c k₀⟩ ^ (-m) ∈ chartRingOver S y c := by
    intro t
    simp only [secOver, Submodule.mem_iInf, Submodule.mem_comap, LinearMap.mulRight_apply,
      Subalgebra.mem_toSubmodule, prod_baseDeg]
  ext t
  rw [hmem, mem_secOver_oneBlock]
  constructor
  · intro ht j hj
    apply mem_of_forall_mem_locIn
    intro p hp
    have hpp := hp.isPrime
    have hz : IndefiniteRowSideFullHecke.Kleiman2.locIn _ p ∈ IndefiniteRowSideFullHecke.Kleiman2.modelPts S (IndefiniteRowSideFullHecke.Kleiman2.oneBlock x') := by
      refine ⟨fun _ => j, fun _ => hj, ?_⟩
      rw [chartRingOver_oneBlock_eq]
      exact ⟨p, hp.isPrime, rfl⟩
    rw [← hy.2] at hz
    obtain ⟨c, hc, q, hq, hzq⟩ := hz
    have hA : ∀ a ∈ chartRingOver S y c, a ∈ IndefiniteRowSideFullHecke.Kleiman2.locIn _ p := fun a ha => by
      rw [hzq, mem_locIn]
      exact ⟨⟨a, ha⟩, 1, fun h => one_not_mem_of_prime hq h, by simp⟩
    have hB : ∀ a ∈ Algebra.adjoin S (Set.range fun i => x' i / x' j), a ∈ IndefiniteRowSideFullHecke.Kleiman2.locIn _ p :=
      fun a ha => mem_locIn.mpr ⟨⟨a, ha⟩, 1, fun h => one_not_mem_of_prime hpp h, by simp⟩
    have hyc : y ⟨k₀, c k₀⟩ ≠ 0 := hc k₀
    have hr : y ⟨k₀, c k₀⟩ / x' j ∈ IndefiniteRowSideFullHecke.Kleiman2.locIn _ p := hB _ (Algebra.subset_adjoin ⟨c k₀, rfl⟩)
    have hr' : (y ⟨k₀, c k₀⟩ / x' j)⁻¹ ∈ IndefiniteRowSideFullHecke.Kleiman2.locIn _ p := by
      rw [inv_div]
      exact hA _ (Algebra.subset_adjoin ⟨⟨k₀, j⟩, rfl⟩)
    have e : t * x' j ^ (-m) = t * y ⟨k₀, c k₀⟩ ^ (-m) * (y ⟨k₀, c k₀⟩ / x' j) ^ m := by
      rw [div_zpow, zpow_neg, zpow_neg]
      field_simp
    rw [e]
    exact Subring.mul_mem _ (hA _ (ht c hc)) (zpow_mem_subring_of_inv_mem _ hr hr' m)
  · intro ht c hc
    have hle : Algebra.adjoin S (Set.range fun i => x' i / x' (c k₀)) ≤ chartRingOver S y c := by
      rw [Algebra.adjoin_le_iff]
      rintro _ ⟨i, rfl⟩
      exact Algebra.subset_adjoin ⟨⟨k₀, i⟩, rfl⟩
    exact hle (ht (c k₀) (hc k₀))

/- English proof (translation)
Introduce `S _ K _ _ ι _ Ω _ _ y k₀ N e x hx hy c`. Rewrite using `[twistSys_secs_eq_secOver, secOver_baseDeg_eq y k₀ hy, hx, secOver_oneBlock_comp]`.
-/
theorem full : BaseTwistSecs.Statement := by
  intro S _ K _ _ ι _ Ω _ _ y k₀ N e x hx hy c
  rw [twistSys_secs_eq_secOver, secOver_baseDeg_eq y k₀ hy, hx, secOver_oneBlock_comp]

end BaseTwistSecs

end

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WEMulNUMulTD

noncomputable section

open ValuativeRel

namespace GlobalTheory.PrinTwo.BallCover

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

def ballGrp (r : kˣ) : AddSubgroup k where
  carrier := {z | valuation k z ≤ valuation k (r : k)}
  zero_mem' := by simp
  add_mem' := fun {a b} ha hb =>
    show valuation k (a + b) ≤ valuation k (r : k) from (valuation k).map_add_le ha hb
  neg_mem' := fun {a} ha =>
    show valuation k (-a) ≤ valuation k (r : k) by rw [Valuation.map_neg]; exact ha

/- English proof (translation)
Unfold both sides. The equivalence is reflexive.
-/
theorem mem_ballGrp (r : kˣ) (z : k) : z ∈ ballGrp r ↔ valuation k z ≤ valuation k (r : k) :=
  Iff.rfl

/- English proof (translation)
Rewrite using `[isOpen_iff_mem_nhds]`. Introduce `x hx`. Rewrite using `[IsValuativeTopology.mem_nhds_iff']`. Use `⟨Units.mk0 γ hγ, fun y hy => ?_⟩` and prove the remaining obligations. Simplify using `only [Set.mem_setOf_eq, Units.val_mk0] at hx hy ⊢`.

Establish `h` using `(valuation k).map_add (y - x) x`. Rewrite `h` using `[sub_add_cancel]`. Conclude with `h.trans (max_le hy.le hx)`.
-/
theorem isOpen_le (γ : ValueGroupWithZero k) (hγ : γ ≠ 0) :
    IsOpen {x : k | valuation k x ≤ γ} := by
  rw [isOpen_iff_mem_nhds]
  intro x hx
  rw [IsValuativeTopology.mem_nhds_iff']
  refine ⟨Units.mk0 γ hγ, fun y hy => ?_⟩
  simp only [Set.mem_setOf_eq, Units.val_mk0] at hx hy ⊢
  have h := (valuation k).map_add (y - x) x
  rw [sub_add_cancel] at h
  exact h.trans (max_le hy.le hx)

/- English proof (translation)
Rewrite using `[QuotientAddGroup.eq, mem_ballGrp]`. Simplify using `only [ball, Set.mem_setOf_eq]`. Rewrite using `[show -(x - c) + t = -(x - (c + t)) by ring, Valuation.map_neg]`.
-/
theorem mem_ball_add_iff (r : kˣ) (c t x : k) :
    x ∈ ball (c + t) r ↔ (QuotientAddGroup.mk (x - c) : k ⧸ ballGrp r) = QuotientAddGroup.mk t := by
  rw [QuotientAddGroup.eq, mem_ballGrp]
  simp only [ball, Set.mem_setOf_eq]
  rw [show -(x - c) + t = -(x - (c + t)) by ring, Valuation.map_neg]

/- English proof (translation)
Establish `hcov : {x : k | valuation k x ≤ γ} ⊆ ⋃ c ∈ {x : k | valuation k x ≤ γ}, ball c r`. Introduce `x hx`. Simplify using `only [Set.mem_iUnion]`. Conclude with `⟨x, hx, by simp [ball]⟩`. Establish `hopen : ∀ c ∈ {x : k | valuation k x ≤ γ}, IsOpen (ball c r)`.

Introduce `c _`. Establish `h0 : valuation k (r : k) ≠ 0` using `by simp`. Conclude with `(isOpen_le _ h0).preimage (continuous_sub_right c)`. Take `⟨t, -, ht, hBt⟩` from `(IsNonarchimedeanLocalField.isCompact_closedBall k γ).elim_finite_subcover_image hopen hcov`. Use `(ht.image (QuotientAddGroup.mk : k → k ⧸ ballGrp r)).subset ?_` and prove the remaining obligations.

Introduce and unpack `_ ⟨x, hx, rfl⟩`. Use `hBt hx` as an intermediate fact. Simplify using `only [Set.mem_iUnion] at this`. Take `⟨c, hc, hxc⟩` from `this`. Use `⟨c, hc, QuotientAddGroup.eq.2 ?_⟩` and prove the remaining obligations.

Rewrite using `[mem_ballGrp, show -c + x = x - c by ring]`. Conclude with `hxc`.
-/
theorem finite_image (r : kˣ) (γ : ValueGroupWithZero k) :
    ((QuotientAddGroup.mk : k → k ⧸ ballGrp r) '' {x | valuation k x ≤ γ}).Finite := by
  have hcov : {x : k | valuation k x ≤ γ} ⊆
      ⋃ c ∈ {x : k | valuation k x ≤ γ}, ball c r := by
    intro x hx
    simp only [Set.mem_iUnion]
    exact ⟨x, hx, by simp [ball]⟩
  have hopen : ∀ c ∈ {x : k | valuation k x ≤ γ}, IsOpen (ball c r) := by
    intro c _
    have h0 : valuation k (r : k) ≠ 0 := by simp
    exact (isOpen_le _ h0).preimage (continuous_sub_right c)
  obtain ⟨t, -, ht, hBt⟩ :=
    (IsNonarchimedeanLocalField.isCompact_closedBall k γ).elim_finite_subcover_image hopen hcov
  refine (ht.image (QuotientAddGroup.mk : k → k ⧸ ballGrp r)).subset ?_
  rintro _ ⟨x, hx, rfl⟩
  have := hBt hx
  simp only [Set.mem_iUnion] at this
  obtain ⟨c, hc, hxc⟩ := this
  refine ⟨c, hc, QuotientAddGroup.eq.2 ?_⟩
  rw [mem_ballGrp, show -c + x = x - c by ring]
  exact hxc

/- English proof (translation)
Introduce `k _ _ _ _ s S hsS`. Establish `hfin` using `finite_image s (valuation k (S : k))`. Set `F` to `hfin.toFinset`. Establish `hmemF : ∀ q : k ⧸ ballGrp s, q ∈ F ↔ ∃ x, valuation k x ≤ valuation k (S : k) ∧ (QuotientAddGroup.mk x : k ⧸ ballGrp s) = q`. Introduce `q`.

Simplify using `[F]`. Establish `hout : ∀ q : k ⧸ ballGrp s, (QuotientAddGroup.mk (Quotient.out q) : k ⧸ ballGrp s) = q` using `fun q => QuotientAddGroup.out_eq' q`. Establish `hG : ∀ y : k, (QuotientAddGroup.mk y : k ⧸ ballGrp s) ∈ F ↔ valuation k y ≤ valuation k (S : k)`. Introduce `y`. Rewrite using `[hmemF]`.

Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨z, hz, hzy⟩`. Establish `h1 : -z + y ∈ ballGrp s` using `QuotientAddGroup.eq.1 hzy`. Rewrite `h1` using `[mem_ballGrp]`. Establish `h2` using `(valuation k).map_add_le hz (h1.trans hsS)`.

Rewrite `h2` using `[show z + (-z + y) = y by ring]`. Then use the resulting hypothesis. Introduce `hy`. Conclude with `⟨y, hy, rfl⟩`. Use `⟨F.image (fun q => Quotient.out q), ?_, ?_, ?_⟩` and prove the remaining obligations. Conclude with `Finset.Nonempty.image ⟨_, (hG 0).2 (by simp)⟩ _`.

Introduce `t ht`. Take `⟨q, hq, rfl⟩` from `Finset.mem_image.1 ht`. Conclude with `(hG _).1 (by rw [hout]; exact hq)`. Introduce `c x`. Rewrite using `[Finset.sum_image (fun a ha b hb h => by`.

Establish `h'` using `congrArg (QuotientAddGroup.mk : k → k ⧸ ballGrp s) h`. Simplify `h')]` using `only [hout]`. Establish `hterm : ∀ q : k ⧸ ballGrp s, (GlobalTheory.PrinTwo.ball (c + Quotient.out q) s).indicator (1 : k → ℂ) x = if (QuotientAddGroup.mk (x - c) : k ⧸ ballGrp s) = q then 1 else 0`. Introduce `q`. Rewrite using `[Set.indicator_apply, Pi.one_apply]`.

Conclude with `if_congr ((mem_ball_add_iff s c _ x).trans (by rw [hout])) rfl rfl`. Use `Eq.trans ?_ (Finset.sum_congr rfl (fun q _ => (hterm q).symm))` and prove the remaining obligations. Rewrite using `[Finset.sum_ite_eq, Set.indicator_apply, Pi.one_apply]`. Conclude with `if_congr (hG (x - c)).symm rfl rfl`.
-/
theorem indicator_ball_eq_sum :
    ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
      (s S : kˣ), ValuativeRel.valuation k (s : k) ≤ ValuativeRel.valuation k (S : k) →
      ∃ T : Finset k, T.Nonempty ∧ (∀ t ∈ T, ValuativeRel.valuation k t ≤ ValuativeRel.valuation k (S : k)) ∧
        ∀ c x : k, (GlobalTheory.PrinTwo.ball c S).indicator (1 : k → ℂ) x =
          ∑ t ∈ T, (GlobalTheory.PrinTwo.ball (c + t) s).indicator 1 x := by
  intro k _ _ _ _ s S hsS
  classical
  have hfin := finite_image s (valuation k (S : k))
  let F := hfin.toFinset
  have hmemF : ∀ q : k ⧸ ballGrp s, q ∈ F ↔
      ∃ x, valuation k x ≤ valuation k (S : k) ∧ (QuotientAddGroup.mk x : k ⧸ ballGrp s) = q := by
    intro q; simp [F]
  have hout : ∀ q : k ⧸ ballGrp s, (QuotientAddGroup.mk (Quotient.out q) : k ⧸ ballGrp s) = q :=
    fun q => QuotientAddGroup.out_eq' q
  have hG : ∀ y : k, (QuotientAddGroup.mk y : k ⧸ ballGrp s) ∈ F ↔
      valuation k y ≤ valuation k (S : k) := by
    intro y
    rw [hmemF]
    constructor
    · rintro ⟨z, hz, hzy⟩
      have h1 : -z + y ∈ ballGrp s := QuotientAddGroup.eq.1 hzy
      rw [mem_ballGrp] at h1
      have h2 := (valuation k).map_add_le hz (h1.trans hsS)
      rwa [show z + (-z + y) = y by ring] at h2
    · intro hy
      exact ⟨y, hy, rfl⟩
  refine ⟨F.image (fun q => Quotient.out q), ?_, ?_, ?_⟩
  · exact Finset.Nonempty.image ⟨_, (hG 0).2 (by simp)⟩ _
  · intro t ht
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.1 ht
    exact (hG _).1 (by rw [hout]; exact hq)
  · intro c x
    rw [Finset.sum_image (fun a ha b hb h => by
      have h' := congrArg (QuotientAddGroup.mk : k → k ⧸ ballGrp s) h
      simpa only [hout] using h')]
    have hterm : ∀ q : k ⧸ ballGrp s,
        (GlobalTheory.PrinTwo.ball (c + Quotient.out q) s).indicator (1 : k → ℂ) x =
          if (QuotientAddGroup.mk (x - c) : k ⧸ ballGrp s) = q then 1 else 0 := by
      intro q
      rw [Set.indicator_apply, Pi.one_apply]
      exact if_congr ((mem_ball_add_iff s c _ x).trans (by rw [hout])) rfl rfl
    refine Eq.trans ?_ (Finset.sum_congr rfl (fun q _ => (hterm q).symm))
    rw [Finset.sum_ite_eq, Set.indicator_apply, Pi.one_apply]
    exact if_congr (hG (x - c)).symm rfl rfl

end GlobalTheory.PrinTwo.BallCover

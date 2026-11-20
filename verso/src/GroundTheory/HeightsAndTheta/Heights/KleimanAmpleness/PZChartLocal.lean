import Mathlib
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.ZChartLocalSt
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.ZChartSmulSt
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PAmpleAffineGen
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

noncomputable section

universe u v w

namespace ZChartLocal

open AmpleAffineGen AmpleTwistLocal

variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N : ℕ} {x : Fin (N + 1) → Ω}
  {E : Type v} [AddCommGroup E] [Module Ω E] [Module S E] [IsScalarTower S Ω E]

omit [Module S E] [IsScalarTower S Ω E] in

/- English proof (translation)
Express the relevant statement in the definitionally equal form `y ∈ Submodule.span _ _ at hy`. Use `Submodule.span_induction (p := fun y _ => w • y ∈ (F.twist (H.pow (c + d))).sub I) ?_ ?_ ?_ ?_ hy` and prove the remaining obligations. Introduce and unpack `_ ⟨q, hq, z, hz, rfl⟩`. Conclude with `Submodule.subset_span ⟨q * w, mul_mem_pow H I hq d hw, z, hz, by rw [smul_smul, mul_comm]⟩`. Rewrite using `[smul_zero]`.

Conclude with `Submodule.zero_mem _`. Introduce `a b _ _ ha hb`. Rewrite using `[smul_add]`. Conclude with `Submodule.add_mem _ ha hb`. Introduce `a z _ hz`.

Establish `e : w • (a • z) = a • (w • z)`. Express the relevant statement in the definitionally equal form `w • ((a : Ω) • z) = (a : Ω) • (w • z)`. Rewrite using `[smul_smul, smul_smul, mul_comm]`. Rewrite using `[e]`. Conclude with `Submodule.smul_mem _ a hz`.
-/
theorem smul_mem_twist_pow (F : SubSystem S x E) (H : SubSystem S x Ω) (I : Chart x) {c d : ℕ}
    {y : E} {w : Ω} (hy : y ∈ (F.twist (H.pow c)).sub I) (hw : w ∈ (H.pow d).sub I) :
    w • y ∈ (F.twist (H.pow (c + d))).sub I := by
  change y ∈ Submodule.span _ _ at hy
  refine Submodule.span_induction
    (p := fun y _ => w • y ∈ (F.twist (H.pow (c + d))).sub I) ?_ ?_ ?_ ?_ hy
  · rintro _ ⟨q, hq, z, hz, rfl⟩
    exact Submodule.subset_span ⟨q * w, mul_mem_pow H I hq d hw, z, hz, by rw [smul_smul, mul_comm]⟩
  · rw [smul_zero]; exact Submodule.zero_mem _
  · intro a b _ _ ha hb; rw [smul_add]; exact Submodule.add_mem _ ha hb
  · intro a z _ hz
    have e : w • (a • z) = a • (w • z) := by
      change w • ((a : Ω) • z) = (a : Ω) • (w • z)
      rw [smul_smul, smul_smul, mul_comm]
    rw [e]
    exact Submodule.smul_mem _ a hz

/- English proof (translation)
Proceed by induction on `T using Finset.induction_on with`. Consider the case `empty => rw [Finset.prod_empty, Finset.card_empty]`. Conclude with `one_mem_twistMod_zero I`. Consider the case `insert a T ha ih`. Rewrite using `[Finset.prod_insert ha, Finset.card_insert_of_notMem ha, mul_comm]`.

Establish `h1 : h a ∈ (H.pow 1).sub I`. Rewrite using `[SubSystem.pow_sub, pow_one]`. Conclude with `(Submodule.mem_iInf _).mp (hh a) I`. Conclude with `mul_mem_pow H I ih 1 h1`.
-/
theorem prod_mem_pow (H : SubSystem S x Ω) (I : Chart x) {r : ℕ} {h : Fin (r + 1) → Ω}
    (hh : ∀ l, h l ∈ H.secs) (T : Finset (Fin (r + 1))) : ∏ l ∈ T, h l ∈ (H.pow T.card).sub I := by
  classical
  induction T using Finset.induction_on with
  | empty => rw [Finset.prod_empty, Finset.card_empty]; exact one_mem_twistMod_zero I
  | insert a T ha ih =>
    rw [Finset.prod_insert ha, Finset.card_insert_of_notMem ha, mul_comm]
    have h1 : h a ∈ (H.pow 1).sub I := by
      rw [SubSystem.pow_sub, pow_one]; exact (Submodule.mem_iInf _).mp (hh a) I
    exact mul_mem_pow H I ih 1 h1

omit [Module S E] [IsScalarTower S Ω E] in

/- English proof (translation)
The claim follows from `Submodule.smul_mem (F.sub I) (⟨_, pow_mem (chartRatio_mem I K) k⟩ : chartRing S x I) hy`.
-/
theorem ratio_pow_smul_mem (F : SubSystem S x E) (I K : Chart x) (k : ℕ) {y : E} (hy : y ∈ F.sub I) :
    chartRatio I K ^ k • y ∈ F.sub I :=
  Submodule.smul_mem (F.sub I) (⟨_, pow_mem (chartRatio_mem I K) k⟩ : chartRing S x I) hy

omit [Module S E] [IsScalarTower S Ω E] in

/- English proof (translation)
Take `⟨a, ha, hay⟩` from `(G.mem_iff I (unionChart I K) (subset_unionChart_left I K) y).mp hy`. Take `⟨w, hw⟩` from `ha.exists_left_inv`. Take `⟨D, hD⟩` from `exists_pow_mul_mem I K w.2`. Use `⟨D, ?_⟩` and prove the remaining obligations. Establish `hw' : (w : Ω) * (a : Ω) = 1` using `congrArg Subtype.val hw`.

Establish `e : chartRatio I K ^ D • y = (⟨_, hD⟩ : chartRing S x I) • ((a : Ω) • y)`. Express the relevant statement in the definitionally equal form `_ = (chartRatio I K ^ D * (w : Ω)) • ((a : Ω) • y)`. Rewrite using `[smul_smul, mul_assoc, hw', mul_one]`. Rewrite using `[e]`. Conclude with `Submodule.smul_mem _ _ hay`.
-/
theorem loc_subFamily (G : SubFamily S x E) (I K : Chart x) {y : E}
    (hy : y ∈ G.sub (unionChart I K)) : ∃ c : ℕ, chartRatio I K ^ c • y ∈ G.sub I := by
  obtain ⟨a, ha, hay⟩ := (G.mem_iff I (unionChart I K) (subset_unionChart_left I K) y).mp hy
  obtain ⟨w, hw⟩ := ha.exists_left_inv
  obtain ⟨D, hD⟩ := exists_pow_mul_mem I K w.2
  refine ⟨D, ?_⟩
  have hw' : (w : Ω) * (a : Ω) = 1 := congrArg Subtype.val hw
  have e : chartRatio I K ^ D • y = (⟨_, hD⟩ : chartRing S x I) • ((a : Ω) • y) := by
    change _ = (chartRatio I K ^ D * (w : Ω)) • ((a : Ω) • y)
    rw [smul_smul, mul_assoc, hw', mul_one]
  rw [e]
  exact Submodule.smul_mem _ _ hay

omit [Module S E] [IsScalarTower S Ω E] in

/- English proof (translation)
Express the relevant statement in the definitionally equal form `y ∈ Submodule.span _ _ at hy`. Use `Submodule.span_induction (p := fun y _ => ∃ c : ℕ, chartRatio I K ^ c • y ∈ (G.toSubSystem.twist (H.toSubSystem.pow q)).sub I) ?_ ?_ ?_ ?_ hy` and prove the remaining obligations. Introduce and unpack `_ ⟨p, hp, z, hz, rfl⟩`. Take `⟨D₁, h₁⟩` from `exists_pow_mul_mem_of_eq (H.powBundle q) (LineBundle.powBundle_toSubSystem H q) I K hp`. Take `⟨D₂, h₂⟩` from `loc_subFamily G I K hz`.

Use `⟨D₁ + D₂, Submodule.subset_span ⟨_, h₁, _, h₂, ?_⟩⟩` and prove the remaining obligations. Rewrite using `[smul_smul, smul_smul, pow_add]`. Use `congr 1`. Expand and normalize the polynomial expressions, which then agree. Conclude with `⟨0, by rw [smul_zero]; exact Submodule.zero_mem _⟩`.

Introduce and unpack `y₁ y₂ - - ⟨c₁, h₁⟩ ⟨c₂, h₂⟩`. Use `⟨c₁ + c₂, ?_⟩` and prove the remaining obligations. Establish `e : chartRatio I K ^ (c₁ + c₂) • (y₁ + y₂) = chartRatio I K ^ c₂ • (chartRatio I K ^ c₁ • y₁) + chartRatio I K ^ c₁ • (chartRatio I K ^ c₂ • y₂)`. Rewrite using `[smul_add, smul_smul, smul_smul, ← pow_add, ← pow_add, Nat.add_comm c₂ c₁]`. Rewrite using `[e]`.

Conclude with `Submodule.add_mem _ (ratio_pow_smul_mem _ I K c₂ h₁) (ratio_pow_smul_mem _ I K c₁ h₂)`. Introduce and unpack `a y - ⟨c, hc⟩`. Take `⟨D, hD⟩` from `exists_pow_mul_mem I K a.2`. Use `⟨D + c, ?_⟩` and prove the remaining obligations. Establish `e : chartRatio I K ^ (D + c) • (a • y) = (⟨_, hD⟩ : chartRing S x I) • (chartRatio I K ^ c • y)`.

Express the relevant statement in the definitionally equal form `chartRatio I K ^ (D + c) • ((a : Ω) • y) = (chartRatio I K ^ D * (a : Ω)) • (chartRatio I K ^ c • y)`. Rewrite using `[smul_smul, smul_smul, pow_add]`. Use `congr 1`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e]`.

Conclude with `Submodule.smul_mem _ _ hc`.
-/
theorem loc_twist (G : SubFamily S x E) (H : LineBundle S x) (I K : Chart x) (q : ℕ) {y : E}
    (hy : y ∈ (G.toSubSystem.twist (H.toSubSystem.pow q)).sub (unionChart I K)) :
    ∃ c : ℕ, chartRatio I K ^ c • y ∈ (G.toSubSystem.twist (H.toSubSystem.pow q)).sub I := by
  change y ∈ Submodule.span _ _ at hy
  refine Submodule.span_induction (p := fun y _ => ∃ c : ℕ,
    chartRatio I K ^ c • y ∈ (G.toSubSystem.twist (H.toSubSystem.pow q)).sub I) ?_ ?_ ?_ ?_ hy
  · rintro _ ⟨p, hp, z, hz, rfl⟩
    obtain ⟨D₁, h₁⟩ := exists_pow_mul_mem_of_eq (H.powBundle q)
      (LineBundle.powBundle_toSubSystem H q) I K hp
    obtain ⟨D₂, h₂⟩ := loc_subFamily G I K hz
    refine ⟨D₁ + D₂, Submodule.subset_span ⟨_, h₁, _, h₂, ?_⟩⟩
    rw [smul_smul, smul_smul, pow_add]
    congr 1
    ring
  · exact ⟨0, by rw [smul_zero]; exact Submodule.zero_mem _⟩
  · rintro y₁ y₂ - - ⟨c₁, h₁⟩ ⟨c₂, h₂⟩
    refine ⟨c₁ + c₂, ?_⟩
    have e : chartRatio I K ^ (c₁ + c₂) • (y₁ + y₂) =
        chartRatio I K ^ c₂ • (chartRatio I K ^ c₁ • y₁) + chartRatio I K ^ c₁ • (chartRatio I K ^ c₂ • y₂) := by
      rw [smul_add, smul_smul, smul_smul, ← pow_add, ← pow_add, Nat.add_comm c₂ c₁]
    rw [e]
    exact Submodule.add_mem _ (ratio_pow_smul_mem _ I K c₂ h₁) (ratio_pow_smul_mem _ I K c₁ h₂)
  · rintro a y - ⟨c, hc⟩
    obtain ⟨D, hD⟩ := exists_pow_mul_mem I K a.2
    refine ⟨D + c, ?_⟩
    have e : chartRatio I K ^ (D + c) • (a • y) = (⟨_, hD⟩ : chartRing S x I) • (chartRatio I K ^ c • y) := by
      change chartRatio I K ^ (D + c) • ((a : Ω) • y) = (chartRatio I K ^ D * (a : Ω)) • (chartRatio I K ^ c • y)
      rw [smul_smul, smul_smul, pow_add]
      congr 1
      ring
    rw [e]
    exact Submodule.smul_mem _ _ hc

end ZChartLocal

open AmpleAffineGen AmpleTwistLocal ZChartLocal in

/- English proof (translation)
Introduce `S _ Ω _ _ N x E _ _ _ _ G H r h hh J j hj b hb K hK j₀ hj₀ I I' hI' z hz`. Establish `hbpow : ∀ (k : ℕ) {y : E}, y ∈ secsOnZChart G.toSubSystem H.toSubSystem h I J → b ^ k • y ∈ secsOnZChart G.toSubSystem H.toSubSystem h I J`. Introduce `k`. Proceed by induction on `k with`. Consider the case `zero => intro y hy`.

Rewrite using `[pow_zero, one_smul]` and apply the resulting hypothesis. Consider the case `succ k ih`. Introduce `y hy`. Rewrite using `[pow_succ', mul_smul]`. Conclude with `hSmul S Ω N x E G.toSubSystem H.toSubSystem r h hh J j hj I b hb _ (ih hy)`.

Establish `hIU : I'.1 ⊆ (unionChart I K).1`. Rewrite using `[hI']`. Conclude with `Finset.insert_subset (Finset.mem_union_right _ hj₀) Finset.subset_union_left`. Establish `hzU : z ∈ secsOnZChart G.toSubSystem H.toSubSystem h (unionChart I K) J`. Use `Submodule.span_mono ?_ hz` and prove the remaining obligations.

Introduce and unpack `y ⟨n, hn⟩`. Conclude with `⟨n, (G.toSubSystem.twist (H.toSubSystem.pow _)).mono I' _ hIU _ hn⟩`. Take `⟨e, n, hn⟩` from `hK I`. Establish `hR` using `prod_mem_pow H.toSubSystem I hh (J.1.erase j)`. Establish `hJ : xProd J = h j * ∏ l ∈ J.1.erase j, h l` using `(Finset.mul_prod_erase J.1 h hj).symm`.

Establish `hcard : (J.1.erase j).card + 1 = J.1.card` using `Finset.card_erase_add_one hj`. Generalize the expression as in `∏ l ∈ J.1.erase j, h l = R at hR hJ`. Establish `hu` using `mul_mem_pow H.toSubSystem I hn _ (pow_mem_pow H.toSubSystem I hR n)`. Generalize the expression as in `hud : b ^ e * (xProd I ^ K.1.card / xProd K ^ I.1.card) * h j ^ n * R ^ n = u at hu`. Establish `huv : u * chartRatio I K = b ^ e * xProd J ^ n`.

Establish `h1` using `chartRatio_mul_chartRatio I K`. Rewrite `h1` using `[chartRatio, chartRatio]`. Rewrite using `[← hud, hJ, chartRatio]`. Take the linear combination `(b ^ e * (h j * R) ^ n) * h1`. Express the relevant statement in the definitionally equal form `z ∈ Submodule.span S _ at hzU`.

Use `Submodule.span_induction (p := fun z _ => ∃ e : ℕ, b ^ e • z ∈ secsOnZChart G.toSubSystem H.toSubSystem h I J) ?_ ?_ ?_ ?_ hzU` and prove the remaining obligations. Introduce and unpack `y ⟨m, hm⟩`. Take `⟨c, hc⟩` from `loc_twist G H I K _ hm`. Use `⟨e * c, Submodule.subset_span ⟨m + n * c, ?_⟩⟩` and prove the remaining obligations. Establish `h2` using `smul_mem_twist_pow G.toSubSystem H.toSubSystem I hc (pow_mem_pow H.toSubSystem I hu c)`.

Establish `e1 : xProd J ^ (m + n * c) • b ^ (e * c) • y = u ^ c • chartRatio I K ^ c • xProd J ^ m • y`. Rewrite using `[smul_smul, smul_smul, smul_smul, ← mul_pow, huv]`. Use `congr 1`. Expand and normalize the polynomial expressions, which then agree. Establish `e2 : J.1.card * m + (1 * n + (J.1.erase j).card * n) * c = J.1.card * (m + n * c)`.

Rewrite using `[← hcard]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e1, ← e2]`. Conclude with `h2`. Conclude with `⟨0, by rw [smul_zero]; exact Submodule.zero_mem _⟩`.

Introduce and unpack `y₁ y₂ - - ⟨e₁, h₁⟩ ⟨e₂, h₂⟩`. Use `⟨e₁ + e₂, ?_⟩` and prove the remaining obligations. Establish `e3 : b ^ (e₁ + e₂) • (y₁ + y₂) = b ^ e₂ • (b ^ e₁ • y₁) + b ^ e₁ • (b ^ e₂ • y₂)`. Rewrite using `[smul_add, smul_smul, smul_smul, ← pow_add, ← pow_add, Nat.add_comm e₂ e₁]`. Rewrite using `[e3]`.

Conclude with `Submodule.add_mem _ (hbpow _ h₁) (hbpow _ h₂)`. Introduce and unpack `s y - ⟨e', h'⟩`. Conclude with `⟨e', by rw [smul_comm]; exact Submodule.smul_mem _ s h'⟩`.
-/
theorem ZChartLocal.proof (hSmul : ZChartSmul.Statement.{u, v, w}) : ZChartLocal.Statement.{u, v, w} := by
  intro S _ Ω _ _ N x E _ _ _ _ G H r h hh J j hj b hb K hK j₀ hj₀ I I' hI' z hz
  classical
  have hbpow : ∀ (k : ℕ) {y : E}, y ∈ secsOnZChart G.toSubSystem H.toSubSystem h I J →
      b ^ k • y ∈ secsOnZChart G.toSubSystem H.toSubSystem h I J := by
    intro k
    induction k with
    | zero => intro y hy; rwa [pow_zero, one_smul]
    | succ k ih =>
      intro y hy
      rw [pow_succ', mul_smul]
      exact hSmul S Ω N x E G.toSubSystem H.toSubSystem r h hh J j hj I b hb _ (ih hy)
  have hIU : I'.1 ⊆ (unionChart I K).1 := by
    rw [hI']; exact Finset.insert_subset (Finset.mem_union_right _ hj₀) Finset.subset_union_left
  have hzU : z ∈ secsOnZChart G.toSubSystem H.toSubSystem h (unionChart I K) J := by
    refine Submodule.span_mono ?_ hz
    rintro y ⟨n, hn⟩
    exact ⟨n, (G.toSubSystem.twist (H.toSubSystem.pow _)).mono I' _ hIU _ hn⟩
  obtain ⟨e, n, hn⟩ := hK I
  have hR := prod_mem_pow H.toSubSystem I hh (J.1.erase j)
  have hJ : xProd J = h j * ∏ l ∈ J.1.erase j, h l := (Finset.mul_prod_erase J.1 h hj).symm
  have hcard : (J.1.erase j).card + 1 = J.1.card := Finset.card_erase_add_one hj
  generalize ∏ l ∈ J.1.erase j, h l = R at hR hJ
  have hu := mul_mem_pow H.toSubSystem I hn _ (pow_mem_pow H.toSubSystem I hR n)
  generalize hud : b ^ e * (xProd I ^ K.1.card / xProd K ^ I.1.card) * h j ^ n * R ^ n = u at hu
  have huv : u * chartRatio I K = b ^ e * xProd J ^ n := by
    have h1 := chartRatio_mul_chartRatio I K
    rw [chartRatio, chartRatio] at h1
    rw [← hud, hJ, chartRatio]
    linear_combination (b ^ e * (h j * R) ^ n) * h1
  change z ∈ Submodule.span S _ at hzU
  refine Submodule.span_induction (p := fun z _ =>
    ∃ e : ℕ, b ^ e • z ∈ secsOnZChart G.toSubSystem H.toSubSystem h I J) ?_ ?_ ?_ ?_ hzU
  · rintro y ⟨m, hm⟩
    obtain ⟨c, hc⟩ := loc_twist G H I K _ hm
    refine ⟨e * c, Submodule.subset_span ⟨m + n * c, ?_⟩⟩
    have h2 := smul_mem_twist_pow G.toSubSystem H.toSubSystem I hc (pow_mem_pow H.toSubSystem I hu c)
    have e1 : xProd J ^ (m + n * c) • b ^ (e * c) • y = u ^ c • chartRatio I K ^ c • xProd J ^ m • y := by
      rw [smul_smul, smul_smul, smul_smul, ← mul_pow, huv]
      congr 1
      ring
    have e2 : J.1.card * m + (1 * n + (J.1.erase j).card * n) * c = J.1.card * (m + n * c) := by
      rw [← hcard]; ring
    rw [e1, ← e2]
    exact h2
  · exact ⟨0, by rw [smul_zero]; exact Submodule.zero_mem _⟩
  · rintro y₁ y₂ - - ⟨e₁, h₁⟩ ⟨e₂, h₂⟩
    refine ⟨e₁ + e₂, ?_⟩
    have e3 : b ^ (e₁ + e₂) • (y₁ + y₂) = b ^ e₂ • (b ^ e₁ • y₁) + b ^ e₁ • (b ^ e₂ • y₂) := by
      rw [smul_add, smul_smul, smul_smul, ← pow_add, ← pow_add, Nat.add_comm e₂ e₁]
    rw [e3]
    exact Submodule.add_mem _ (hbpow _ h₁) (hbpow _ h₂)
  · rintro s y - ⟨e', h'⟩
    exact ⟨e', by rw [smul_comm]; exact Submodule.smul_mem _ s h'⟩

end

end GroundTheory.Heights₂.Heights.Kleiman

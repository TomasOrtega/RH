import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.NormalFormDualOrthogonalLast
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.IsNormalFormStabilizerMeasure
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.IsFundOne
open NumberField MeasureTheory Matrix Formalism.HermitianLatticeCounting.S6 GlobalTheory.HermLat GlobalTheory.DegCnt Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp GlobalTheory.DegVol
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.CovolIdx

/- English proof (translation)
Rewrite using `[← ENNReal.tsum_prod]`. Set `e : (H ⧸ C.subgroupOf H) × C → H` to `fun p => p.1.out * ⟨p.2, hC p.2.2⟩`. Establish `hmk : ∀ p, (QuotientGroup.mk (e p) : H ⧸ C.subgroupOf H) = p.1`. Introduce `p`. Establish `: (QuotientGroup.mk (e p) : H ⧸ C.subgroupOf H) = QuotientGroup.mk p.1.out`.

Use `symm`. Rewrite using `[QuotientGroup.eq]`. Simplify using `[e, Subgroup.mem_subgroupOf]`. Rewrite using `[this, QuotientGroup.out_eq']`. Establish `he : Function.Bijective e`.

Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨q, c⟩ ⟨q', c'⟩ h`. Establish `h1 : q = q'`. Use `hmk (q, c)` as an intermediate fact. Rewrite `this` using `[h, hmk]`.

Conclude with `this.symm`. Substitute `h1` using the available equality. Establish `h2` using `mul_left_cancel h`. Establish `h3 : c = c'` using `Subtype.ext (congrArg Subtype.val h2 :)`. Rewrite using `[h3]`.

Introduce `h`. Establish `hm : ((QuotientGroup.mk h : H ⧸ C.subgroupOf H).out)⁻¹ * h ∈ C.subgroupOf H`. Rewrite using `[← QuotientGroup.eq, QuotientGroup.out_eq']`. Use `⟨(QuotientGroup.mk h, ⟨_, Subgroup.mem_subgroupOf.1 hm⟩), ?_⟩` and prove the remaining obligations. Apply `Subtype.ext` to reduce the goal to its premises.

Simplify using `[e]`. Conclude with `((Equiv.ofBijective e he).tsum_eq (fun h : H => f h)).symm`.
-/
theorem tsum_cosets {G : Type} [Group G] (C H : Subgroup G) (hC : C ≤ H) (f : G → ℝ≥0∞) :
    ∑' h : H, f h = ∑' q : H ⧸ C.subgroupOf H, ∑' c : C, f ((q.out : H) * (c : G)) := by
  rw [← ENNReal.tsum_prod]
  let e : (H ⧸ C.subgroupOf H) × C → H := fun p => p.1.out * ⟨p.2, hC p.2.2⟩
  have hmk : ∀ p, (QuotientGroup.mk (e p) : H ⧸ C.subgroupOf H) = p.1 := by
    intro p
    have : (QuotientGroup.mk (e p) : H ⧸ C.subgroupOf H) = QuotientGroup.mk p.1.out := by
      symm
      rw [QuotientGroup.eq]
      simp [e, Subgroup.mem_subgroupOf]
    rw [this, QuotientGroup.out_eq']
  have he : Function.Bijective e := by
    constructor
    · rintro ⟨q, c⟩ ⟨q', c'⟩ h
      have h1 : q = q' := by
        have := hmk (q, c)
        rw [h, hmk] at this
        exact this.symm
      subst h1
      have h2 := mul_left_cancel h
      have h3 : c = c' := Subtype.ext (congrArg Subtype.val h2 :)
      rw [h3]
    · intro h
      have hm : ((QuotientGroup.mk h : H ⧸ C.subgroupOf H).out)⁻¹ * h ∈ C.subgroupOf H := by
        rw [← QuotientGroup.eq, QuotientGroup.out_eq']
      refine ⟨(QuotientGroup.mk h, ⟨_, Subgroup.mem_subgroupOf.1 hm⟩), ?_⟩
      apply Subtype.ext
      simp [e]
  exact ((Equiv.ofBijective e he).tsum_eq (fun h : H => f h)).symm

/- English proof (translation)
Rewrite using `[← measure_iUnion₀]`. Apply `measure_congr` to reduce the goal to its premises. Establish `: ∀ᵐ x ∂μ, x ∈ R` using `hR`. Use `filter_upwards [this] with x hx`. Take `⟨s, hs, -⟩` from `h x hx`.

Apply `propext` to reduce the goal to its premises. Prove the components needed by the constructor for the conclusion. Introduce `hxS`. Conclude with `Set.mem_iUnion.2 ⟨⟨s, hs.1⟩, hs.2, hxS⟩`. Introduce `hxS`.

Take `⟨a, ha⟩` from `Set.mem_iUnion.1 hxS`. Conclude with `ha.2`. Introduce `a b hab`. Use `measure_mono_null ?_ hR` and prove the remaining obligations. Introduce and unpack `x ⟨ha, hb⟩ hx`.

Conclude with `hab (Subtype.ext ((h x hx).unique ⟨a.2, ha.1⟩ ⟨b.2, hb.1⟩))`. Introduce `a`. Conclude with `((hm a hΩ).inter hS).nullMeasurableSet`.
-/
theorem measure_eq_tsum_inter {G α : Type} [Group G] [MulAction G α] [MeasurableSpace α]
    (μ : Measure α) (R : Set α) (A : Subgroup G) [Countable A] (Ω S : Set α)
    (hm : ∀ s : G, Measurable fun x : α => s • x) (hR : μ Rᶜ = 0)
    (hΩ : MeasurableSet Ω) (hS : MeasurableSet S) (h : ∀ x ∈ R, ∃! s, s ∈ A ∧ s • x ∈ Ω) :
    μ S = ∑' a : A, μ ((fun x => (a : G) • x) ⁻¹' Ω ∩ S) := by
  rw [← measure_iUnion₀]
  · apply measure_congr
    have : ∀ᵐ x ∂μ, x ∈ R := hR
    filter_upwards [this] with x hx
    obtain ⟨s, hs, -⟩ := h x hx
    apply propext
    constructor
    · intro hxS
      exact Set.mem_iUnion.2 ⟨⟨s, hs.1⟩, hs.2, hxS⟩
    · intro hxS
      obtain ⟨a, ha⟩ := Set.mem_iUnion.1 hxS
      exact ha.2
  · intro a b hab
    refine measure_mono_null ?_ hR
    rintro x ⟨ha, hb⟩ hx
    exact hab (Subtype.ext ((h x hx).unique ⟨a.2, ha.1⟩ ⟨b.2, hb.1⟩))
  · intro a
    exact ((hm a hΩ).inter hS).nullMeasurableSet

/- English proof (translation)
Introduce `G α _ _ _ μ R A B Ω K hm cA cB hR hinv hAB hBA hΩ hK fA fB`. Establish `hpre : ∀ s ∈ A ⊔ B, ∀ S, MeasurableSet S → μ ((fun x => s • x) ⁻¹' S) = μ S`. Introduce `s hs S hS`. Rewrite using `[← Measure.map_apply (hm s) hS, (hinv s hs).2]`. Set `F : G → G → ℝ≥0∞` to `fun a b => μ ((fun x => a • x) ⁻¹' Ω ∩ (fun x => b • x) ⁻¹' K)`.

Establish `hF : ∀ a b c : G, c ∈ A ⊓ B → F (a * c) b = F a (b * c⁻¹)`. Introduce `a b c hc`. Use `Eq.trans ?_ (hpre c (Subgroup.mem_sup_left hc.1) _ ((hm a hΩ).inter (hm (b * c⁻¹) hK)))` and prove the remaining obligations. Simplify using `only [F]`. Use `congr 1`.

Use extensionality with `x`. Simplify using `[mul_smul]`. Establish `h1 : ∀ b ∈ B, μ K = ∑' a : A, F a b`. Introduce `b hb`. Rewrite using `[← hpre b (Subgroup.mem_sup_right hb) K hK]`.

Conclude with `measure_eq_tsum_inter μ R A Ω _ hm hR hΩ (hm b hK) fA`. Establish `h2 : ∀ a ∈ A, μ Ω = ∑' b : B, F a b`. Introduce `a ha`. Rewrite using `[← hpre a (Subgroup.mem_sup_left ha) Ω hΩ, measure_eq_tsum_inter μ R B K _ hm hR hK (hm a hΩ) fB]`. Simplify using `only [F, Set.inter_comm]`.

Establish `key : ∑' _q : B ⧸ (A ⊓ B).subgroupOf B, μ K = ∑' _p : A ⧸ (A ⊓ B).subgroupOf A, μ Ω`. Establish `e1 : ∀ q : B ⧸ (A ⊓ B).subgroupOf B, μ K = ∑' p : A ⧸ (A ⊓ B).subgroupOf A, ∑' c : (A ⊓ B : Subgroup G), F (p.out : A) ((q.out : B) * (c : G))`. Introduce `q`. Rewrite using `[h1 _ q.out.2, tsum_cosets (A ⊓ B) A inf_le_left (fun a => F a (q.out : B))]`. Use `tsum_congr fun p => ?_` and prove the remaining obligations.

Rewrite using `[← (Equiv.inv (A ⊓ B : Subgroup G)).tsum_eq]`. Use `tsum_congr fun c => ?_` and prove the remaining obligations. Rewrite using `[hF _ _ _ (Subtype.property _)]`. Simplify using the standard rewrite rules. Establish `e2 : ∀ p : A ⧸ (A ⊓ B).subgroupOf A, μ Ω = ∑' q : B ⧸ (A ⊓ B).subgroupOf B, ∑' c : (A ⊓ B : Subgroup G), F (p.out : A) ((q.out : B) * (c : G))`.

Introduce `p`. Rewrite using `[h2 _ p.out.2, tsum_cosets (A ⊓ B) B inf_le_right (fun b => F (p.out : A) b)]`. Rewrite using `[tsum_congr e1, tsum_congr e2, ENNReal.tsum_comm]`. Rewrite `key` using `[Subgroup.inf_subgroupOf_right, Subgroup.inf_subgroupOf_left, ENNReal.tsum_const, ENNReal.tsum_const]`. Establish `fq : Finite (B ⧸ A.subgroupOf B)` using `Subgroup.fintypeOfIndexNeZero hAB |>.finite`.

Establish `fp : Finite (A ⧸ B.subgroupOf A)` using `Subgroup.fintypeOfIndexNeZero hBA |>.finite`. Establish `key' : (A.relIndex B : ℝ≥0∞) * μ K = (B.relIndex A : ℝ≥0∞) * μ Ω`. Simplify `key` using `[ENat.card_eq_coe_natCard, Subgroup.relIndex, Subgroup.index]`. Establish `hv : ENNReal.ofReal (GlobalTheory.HL.invVol A B) = (A.relIndex B : ℝ≥0∞)⁻¹ * (B.relIndex A : ℝ≥0∞)`. Unfold `GlobalTheory.HL.invVol`.

Rewrite using `[ENNReal.ofReal_div_of_pos (by exact_mod_cast Nat.pos_of_ne_zero hAB), ENNReal.ofReal_natCast, ENNReal.ofReal_natCast, div_eq_mul_inv, mul_comm]`. Rewrite using `[hv, mul_assoc, ← key', ← mul_assoc, ENNReal.inv_mul_cancel (by exact_mod_cast hAB) (ENNReal.natCast_ne_top _), one_mul]`.
-/
theorem measure_eq_invVol_mul : ∀ (G α : Type) [Group G] [MulAction G α] [MeasurableSpace α] (μ : Measure α) (R : Set α) (A B : Subgroup G) (Ω K : Set α), (∀ s : G, Measurable fun x : α => s • x) → Countable A → Countable B → μ Rᶜ = 0 → (∀ s ∈ A ⊔ B, (∀ x ∈ R, s • x ∈ R) ∧ μ.map (fun x => s • x) = μ) → A.relIndex B ≠ 0 → B.relIndex A ≠ 0 → MeasurableSet Ω → MeasurableSet K → (∀ x ∈ R, ∃! s, s ∈ A ∧ s • x ∈ Ω) → (∀ x ∈ R, ∃! s, s ∈ B ∧ s • x ∈ K) → μ K = ENNReal.ofReal (GlobalTheory.HL.invVol A B) * μ Ω := by
  intro G α _ _ _ μ R A B Ω K hm cA cB hR hinv hAB hBA hΩ hK fA fB
  have hpre : ∀ s ∈ A ⊔ B, ∀ S, MeasurableSet S → μ ((fun x => s • x) ⁻¹' S) = μ S := by
    intro s hs S hS
    rw [← Measure.map_apply (hm s) hS, (hinv s hs).2]
  let F : G → G → ℝ≥0∞ := fun a b => μ ((fun x => a • x) ⁻¹' Ω ∩ (fun x => b • x) ⁻¹' K)
  have hF : ∀ a b c : G, c ∈ A ⊓ B → F (a * c) b = F a (b * c⁻¹) := by
    intro a b c hc
    refine Eq.trans ?_ (hpre c (Subgroup.mem_sup_left hc.1) _ ((hm a hΩ).inter (hm (b * c⁻¹) hK)))
    simp only [F]
    congr 1
    ext x
    simp [mul_smul]
  have h1 : ∀ b ∈ B, μ K = ∑' a : A, F a b := by
    intro b hb
    rw [← hpre b (Subgroup.mem_sup_right hb) K hK]
    exact measure_eq_tsum_inter μ R A Ω _ hm hR hΩ (hm b hK) fA
  have h2 : ∀ a ∈ A, μ Ω = ∑' b : B, F a b := by
    intro a ha
    rw [← hpre a (Subgroup.mem_sup_left ha) Ω hΩ,
      measure_eq_tsum_inter μ R B K _ hm hR hK (hm a hΩ) fB]
    simp only [F, Set.inter_comm]
  have key : ∑' _q : B ⧸ (A ⊓ B).subgroupOf B, μ K = ∑' _p : A ⧸ (A ⊓ B).subgroupOf A, μ Ω := by
    have e1 : ∀ q : B ⧸ (A ⊓ B).subgroupOf B, μ K =
        ∑' p : A ⧸ (A ⊓ B).subgroupOf A, ∑' c : (A ⊓ B : Subgroup G),
          F (p.out : A) ((q.out : B) * (c : G)) := by
      intro q
      rw [h1 _ q.out.2, tsum_cosets (A ⊓ B) A inf_le_left (fun a => F a (q.out : B))]
      refine tsum_congr fun p => ?_
      rw [← (Equiv.inv (A ⊓ B : Subgroup G)).tsum_eq]
      refine tsum_congr fun c => ?_
      rw [hF _ _ _ (Subtype.property _)]
      simp
    have e2 : ∀ p : A ⧸ (A ⊓ B).subgroupOf A, μ Ω =
        ∑' q : B ⧸ (A ⊓ B).subgroupOf B, ∑' c : (A ⊓ B : Subgroup G),
          F (p.out : A) ((q.out : B) * (c : G)) := by
      intro p
      rw [h2 _ p.out.2, tsum_cosets (A ⊓ B) B inf_le_right (fun b => F (p.out : A) b)]
    rw [tsum_congr e1, tsum_congr e2, ENNReal.tsum_comm]
  rw [Subgroup.inf_subgroupOf_right, Subgroup.inf_subgroupOf_left, ENNReal.tsum_const, ENNReal.tsum_const] at key
  have fq : Finite (B ⧸ A.subgroupOf B) := Subgroup.fintypeOfIndexNeZero hAB |>.finite
  have fp : Finite (A ⧸ B.subgroupOf A) := Subgroup.fintypeOfIndexNeZero hBA |>.finite
  have key' : (A.relIndex B : ℝ≥0∞) * μ K = (B.relIndex A : ℝ≥0∞) * μ Ω := by
    simpa [ENat.card_eq_coe_natCard, Subgroup.relIndex, Subgroup.index] using key
  have hv : ENNReal.ofReal (GlobalTheory.HL.invVol A B) = (A.relIndex B : ℝ≥0∞)⁻¹ * (B.relIndex A : ℝ≥0∞) := by
    unfold GlobalTheory.HL.invVol
    rw [ENNReal.ofReal_div_of_pos (by exact_mod_cast Nat.pos_of_ne_zero hAB), ENNReal.ofReal_natCast,
      ENNReal.ofReal_natCast, div_eq_mul_inv, mul_comm]
  rw [hv, mul_assoc, ← key', ← mul_assoc,
    ENNReal.inv_mul_cancel (by exact_mod_cast hAB) (ENNReal.natCast_ne_top _), one_mul]

end GlobalTheory.CovolIdx

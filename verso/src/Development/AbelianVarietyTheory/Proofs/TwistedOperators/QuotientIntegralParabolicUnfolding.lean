import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.SimpleSum
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsMulLeftInvariantVolGL
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnipotentRadicalBasic
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RootExchangeUnipotentHaarAndModulusStatement
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx

noncomputable section
namespace GlobalTheory.QuotInt

section Abstract
variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/- English proof (translation)
Assemble the required witnesses or components as `⟨hF.1.comp_continuous (continuous_mul_const h), hF.2.comp_homeomorph (Homeomorph.mulRight h)⟩`.
-/
theorem sb_right {F : G → ℂ} (hF : F ∈ SB G) (h : G) : (fun g => F (g * h)) ∈ SB G :=
  ⟨hF.1.comp_continuous (continuous_mul_const h), hF.2.comp_homeomorph (Homeomorph.mulRight h)⟩

/- English proof (translation)
Set `K : Subgroup G` to `{ carrier := {x | ∀ g, F (g * x) = F g} one_mem' := by intro g; simp mul_mem' := by`. Introduce `a b ha hb g`. Rewrite using `[← mul_assoc, hb, ha]`. Use the proof step `inv_mem' := by`. Introduce `a ha g`.

Use `ha (g * a⁻¹)` as an intermediate fact. Simplify using `using this.symm }`. Use `⟨K, ?_, fun g x hx => hx g⟩` and prove the remaining obligations. Establish `h1 : ∀ᶠ x in nhds (1 : G), ∀ g ∈ tsupport F, F (g * x) = F g`. Apply `IsCompact.eventually_forall_of_forall_eventually hF.2` to reduce the goal to its premises.

Introduce `g _`. Establish `a1 : IsLocallyConstant (fun z : G × G => F (z.2 * z.1))` using `hF.1.comp_continuous (by fun_prop)`. Establish `a2 : IsLocallyConstant (fun z : G × G => F z.2)` using `hF.1.comp_continuous (by fun_prop)`. Use `filter_upwards [a1.eventually_eq (1, g), a2.eventually_eq (1, g)] with z hz1 hz2`. Simplify using `only [hz1, hz2, mul_one]`.

Establish `h2 : ∀ᶠ x in nhds (1 : G), ∀ g ∈ tsupport F, F (g * x⁻¹) = F g`. Establish `: Filter.Tendsto (fun x : G => x⁻¹) (nhds 1) (nhds 1)`. Simplify using `using (continuous_inv (G := G)).tendsto 1`. Conclude with `this.eventually h1`. Apply `Subgroup.isOpen_of_mem_nhds K (g := 1)` to reduce the goal to its premises.

Use `filter_upwards [h1, h2] with x hx1 hx2`. Introduce `g`. Distinguish the cases in `hg : g ∈ tsupport F`. Conclude with `hx1 g hg`. Distinguish the cases in `hg' : g * x ∈ tsupport F`.

Simplify using `using (hx2 _ hg').symm`. Rewrite using `[image_eq_zero_of_notMem_tsupport hg, image_eq_zero_of_notMem_tsupport hg']`.
-/
theorem exists_open_stab {F : G → ℂ} (hF : F ∈ SB G) :
    ∃ K : Subgroup G, IsOpen (K : Set G) ∧ ∀ g, ∀ x ∈ K, F (g * x) = F g := by
  let K : Subgroup G :=
    { carrier := {x | ∀ g, F (g * x) = F g}
      one_mem' := by intro g; simp
      mul_mem' := by
        intro a b ha hb g
        rw [← mul_assoc, hb, ha]
      inv_mem' := by
        intro a ha g
        have := ha (g * a⁻¹)
        simpa using this.symm }
  refine ⟨K, ?_, fun g x hx => hx g⟩
  have h1 : ∀ᶠ x in nhds (1 : G), ∀ g ∈ tsupport F, F (g * x) = F g := by
    apply IsCompact.eventually_forall_of_forall_eventually hF.2
    intro g _
    have a1 : IsLocallyConstant (fun z : G × G => F (z.2 * z.1)) :=
      hF.1.comp_continuous (by fun_prop)
    have a2 : IsLocallyConstant (fun z : G × G => F z.2) :=
      hF.1.comp_continuous (by fun_prop)
    filter_upwards [a1.eventually_eq (1, g), a2.eventually_eq (1, g)] with z hz1 hz2
    simp only [hz1, hz2, mul_one]
  have h2 : ∀ᶠ x in nhds (1 : G), ∀ g ∈ tsupport F, F (g * x⁻¹) = F g := by
    have : Filter.Tendsto (fun x : G => x⁻¹) (nhds 1) (nhds 1) := by
      simpa using (continuous_inv (G := G)).tendsto 1
    exact this.eventually h1
  apply Subgroup.isOpen_of_mem_nhds K (g := 1)
  filter_upwards [h1, h2] with x hx1 hx2
  intro g
  by_cases hg : g ∈ tsupport F
  · exact hx1 g hg
  · by_cases hg' : g * x ∈ tsupport F
    · simpa using (hx2 _ hg').symm
    · rw [image_eq_zero_of_notMem_tsupport hg, image_eq_zero_of_notMem_tsupport hg']

/- English proof (translation)
Use `haveI := QuotientGroup.discreteTopology hKo`. Use `⟨(IsLocallyConstant.of_discrete a).comp_continuous QuotientGroup.continuous_mk, ?_⟩` and prove the remaining obligations. Establish `hc : IsCompact (⋃ q ∈ S, (fun x => q.out * x) '' (K : Set G))` using `S.isCompact_biUnion fun q _ => hKc.image (by fun_prop)`. Use `HasCompactSupport.intro hc fun g hg => ha _ fun hq => hg ?_` and prove the remaining obligations. Simplify using `only [Set.mem_iUnion]`.

Use `⟨_, hq, ((g : G ⧸ K).out)⁻¹ * g, ?_, by simp⟩` and prove the remaining obligations. Conclude with `QuotientGroup.eq.1 (by simp)`.
-/
theorem sb_of_quot (K : Subgroup G) (hKo : IsOpen (K : Set G)) (hKc : IsCompact (K : Set G))
    (S : Finset (G ⧸ K)) (a : G ⧸ K → ℂ) (ha : ∀ q, q ∉ S → a q = 0) :
    (fun g : G => a (g : G ⧸ K)) ∈ SB G := by
  haveI := QuotientGroup.discreteTopology hKo
  refine ⟨(IsLocallyConstant.of_discrete a).comp_continuous QuotientGroup.continuous_mk, ?_⟩
  have hc : IsCompact (⋃ q ∈ S, (fun x => q.out * x) '' (K : Set G)) :=
    S.isCompact_biUnion fun q _ => hKc.image (by fun_prop)
  refine HasCompactSupport.intro hc fun g hg => ha _ fun hq => hg ?_
  simp only [Set.mem_iUnion]
  refine ⟨_, hq, ((g : G ⧸ K).out)⁻¹ * g, ?_, by simp⟩
  exact QuotientGroup.eq.1 (by simp)

/- English proof (translation)
Use `haveI := QuotientGroup.discreteTopology hKo`. Use `(hC.image (QuotientGroup.continuous_mk (N := K))).finite_of_discrete` as an intermediate fact. Conclude with `⟨this.toFinset, fun g hg => by simpa using ⟨g, hg, rfl⟩⟩`.
-/
theorem finite_quot (K : Subgroup G) (hKo : IsOpen (K : Set G)) {C : Set G} (hC : IsCompact C) :
    ∃ S : Finset (G ⧸ K), ∀ g ∈ C, (g : G ⧸ K) ∈ S := by
  haveI := QuotientGroup.discreteTopology hKo
  have := (hC.image (QuotientGroup.continuous_mk (N := K))).finite_of_discrete
  exact ⟨this.toFinset, fun g hg => by simpa using ⟨g, hg, rfl⟩⟩

/- English proof (translation)
Take `⟨K₁, hK₁, hinv⟩` from `exists_open_stab hF`. Use `set K : Subgroup G := K₀ ⊓ K₁ with hK`. Establish `ho : IsOpen (K : Set G)` using `hKo.inter hK₁`. Establish `hc : IsCompact (K : Set G)` using `hKc.inter_right (K₁.isClosed_of_isOpen hK₁)`. Take `⟨S, hS⟩` from `finite_quot K ho hF.2`.

Set `ind : G ⧸ K → G → ℂ` to `fun q g => if (g : G ⧸ K) = q then 1 else 0`. Establish `hind : ∀ q, ind q ∈ SB G` using `fun q => sb_of_quot K ho hc {q} (fun x => if x = q then 1 else 0) (by intro x hx; simpa using hx)`. Establish `hout : ∀ g : G, F (g : G ⧸ K).out = F g`. Introduce `g`. Establish `: g⁻¹ * (g : G ⧸ K).out ∈ K` using `QuotientGroup.eq.1 (by simp)`.

Simplify using `using hinv g _ this.2`. Establish `hdec : ∀ g, F g = ∑ q ∈ S, F q.out * ind q g`. Introduce `g`. Simplify using `only [ind, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq]`. Use `split_ifs with h`.

Conclude with `(hout g).symm`. Conclude with `image_eq_zero_of_notMem_tsupport fun hg => h (hS g hg)`. Establish `hz : Λ (fun _ => 0) = 0` using `by simpa using hsmul 0 0`. Establish `hsum : ∀ (T : Finset (G ⧸ K)) (h : G), Λ (fun g => ∑ q ∈ T, F q.out * ind q (g * h)) = ∑ q ∈ T, F q.out * Λ (fun g => ind q (g * h))`. Introduce `T h`.

Proceed by induction on `T using Finset.induction_on with`. Consider the case `empty => simpa using hz`. Consider the case `insert a T ha ih`. Simplify using `only [Finset.sum_insert ha]`. Rewrite using `[← ih, ← hsmul, ← hadd]`.

Both sides reduce to the same expression. Conclude with `(SB G).smul_mem (F a.out) (sb_right (hind a) h)`. Use `(SB G).sum_mem (t := T) fun q _ => (SB G).smul_mem (F q.out) (sb_right (hind q) h)` as an intermediate fact. Use `this using 1` and compare the differences between its conclusion and the goal. Use extensionality with `g`.

Simplify using the standard rewrite rules. Establish `hshift : ∀ (r : G) (q : G ⧸ K) (g : G), ind (r • q) g = ind q (r⁻¹ * g)`. Introduce `r q g`. Establish `: ((r⁻¹ * g : G) : G ⧸ K) = r⁻¹ • (g : G ⧸ K)` using `rfl`. Simplify using `only [ind, this, inv_smul_eq_iff]`.

Establish `htot : ∑ q ∈ S, F q.out = 0`. Apply `Finset.sum_cancels_of_partition_cancels (MulAction.orbitRel R (G ⧸ K))` to reduce the goal to its premises. Introduce `x _`. Establish `hc0 : Λ (fun g => ind x (g * x.out)) ≠ 0`. Use `hpos _ (sb_right (hind x) _) (fun g => ?_) ⟨1, R.one_mem, by simp [ind]⟩` and prove the remaining obligations.

Apply the tactic sequence `simp only [ind]; split_ifs <;> simp`. Use `h0 x.out` as an intermediate fact. Simplify using `only [hdec (_ * x.out)] at this`. Rewrite `this` using `[hsum]`. Apply `mul_right_cancel₀ hc0` to reduce the goal to its premises.

Rewrite using `[zero_mul, ← this, Finset.sum_mul, Finset.sum_filter]`. Use `Finset.sum_congr rfl fun q _ => ?_` and prove the remaining obligations. Use `split_ifs with hq`. Take `⟨r, rfl⟩` from `hq`. Use `congr 1`.

Rewrite using `[← hleft r⁻¹ (R.inv_mem r.2)]`. Use `congr 1`. Use extensionality with `g`. Express the relevant statement in the definitionally equal form `_ = ind ((r : G) • x) _`. Rewrite using `[hshift, mul_assoc]`.

Rewrite using `[hcongr (fun g => ind q (g * x.out)) (fun _ => 0), hz, mul_zero]`. Introduce `r hr`. Simplify using `only [ind, ite_eq_right_iff]`. Introduce `h`. Use `absurd ⟨⟨r, hr⟩, ?_⟩ hq` and prove the remaining obligations.

Rewrite using `[← h]`. Express the relevant statement in the definitionally equal form `r • x = r • ((x.out : G) : G ⧸ K)`. Simplify using the standard rewrite rules. Establish `hint : ∀ q, ∫ g, ind q g ∂μ = ∫ g, ind ((1 : G) : G ⧸ K) g ∂μ`. Introduce `q`.

Establish `: q = q.out • ((1 : G) : G ⧸ K)`. Express the relevant statement in the definitionally equal form `q = ((q.out * 1 : G) : G ⧸ K)`. Simplify using the standard rewrite rules. Rewrite using `[this]`. Simplify using `only [hshift]`.

Conclude with `integral_mul_left_eq_self _ _`. Rewrite using `[show (fun g => F g) = fun g => ∑ q ∈ S, F q.out * ind q g from funext hdec, integral_finset_sum]`. Simplify using `only [integral_const_mul, hint]`. Rewrite using `[← Finset.sum_mul, htot, zero_mul]`. Introduce `q _`.

Conclude with `((hind q).1.continuous.integrable_of_hasCompactSupport (hind q).2).const_mul _`.
-/
theorem integral_eq_zero_of_avg [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsMulLeftInvariant]
    [IsFiniteMeasureOnCompacts μ]
    (K₀ : Subgroup G) (hKo : IsOpen (K₀ : Set G)) (hKc : IsCompact (K₀ : Set G))
    (R : Subgroup G) (Λ : (G → ℂ) → ℂ)
    (hadd : ∀ φ ∈ SB G, ∀ ψ ∈ SB G, Λ (φ + ψ) = Λ φ + Λ ψ)
    (hsmul : ∀ (a : ℂ) φ, Λ (fun g => a * φ g) = a * Λ φ)
    (hcongr : ∀ φ ψ, (∀ r ∈ R, φ r = ψ r) → Λ φ = Λ ψ)
    (hleft : ∀ r ∈ R, ∀ φ, Λ (fun g => φ (r * g)) = Λ φ)
    (hpos : ∀ φ ∈ SB G, (∀ g, φ g = 0 ∨ φ g = 1) → (∃ r ∈ R, φ r = 1) → Λ φ ≠ 0)
    {F : G → ℂ} (hF : F ∈ SB G) (h0 : ∀ h, Λ (fun g => F (g * h)) = 0) : ∫ g, F g ∂μ = 0 := by
  classical
  obtain ⟨K₁, hK₁, hinv⟩ := exists_open_stab hF
  set K : Subgroup G := K₀ ⊓ K₁ with hK
  have ho : IsOpen (K : Set G) := hKo.inter hK₁
  have hc : IsCompact (K : Set G) := hKc.inter_right (K₁.isClosed_of_isOpen hK₁)
  obtain ⟨S, hS⟩ := finite_quot K ho hF.2
  let ind : G ⧸ K → G → ℂ := fun q g => if (g : G ⧸ K) = q then 1 else 0
  have hind : ∀ q, ind q ∈ SB G := fun q =>
    sb_of_quot K ho hc {q} (fun x => if x = q then 1 else 0) (by intro x hx; simpa using hx)
  have hout : ∀ g : G, F (g : G ⧸ K).out = F g := by
    intro g
    have : g⁻¹ * (g : G ⧸ K).out ∈ K := QuotientGroup.eq.1 (by simp)
    simpa using hinv g _ this.2
  have hdec : ∀ g, F g = ∑ q ∈ S, F q.out * ind q g := by
    intro g
    simp only [ind, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq]
    split_ifs with h
    · exact (hout g).symm
    · exact image_eq_zero_of_notMem_tsupport fun hg => h (hS g hg)
  have hz : Λ (fun _ => 0) = 0 := by simpa using hsmul 0 0
  have hsum : ∀ (T : Finset (G ⧸ K)) (h : G), Λ (fun g => ∑ q ∈ T, F q.out * ind q (g * h)) =
      ∑ q ∈ T, F q.out * Λ (fun g => ind q (g * h)) := by
    intro T h
    induction T using Finset.induction_on with
    | empty => simpa using hz
    | insert a T ha ih =>
      simp only [Finset.sum_insert ha]
      rw [← ih, ← hsmul, ← hadd]
      · rfl
      · exact (SB G).smul_mem (F a.out) (sb_right (hind a) h)
      · have := (SB G).sum_mem (t := T) fun q _ => (SB G).smul_mem (F q.out) (sb_right (hind q) h)
        convert this using 1
        ext g; simp
  have hshift : ∀ (r : G) (q : G ⧸ K) (g : G), ind (r • q) g = ind q (r⁻¹ * g) := by
    intro r q g
    have : ((r⁻¹ * g : G) : G ⧸ K) = r⁻¹ • (g : G ⧸ K) := rfl
    simp only [ind, this, inv_smul_eq_iff]
  have htot : ∑ q ∈ S, F q.out = 0 := by
    apply Finset.sum_cancels_of_partition_cancels (MulAction.orbitRel R (G ⧸ K))
    intro x _
    have hc0 : Λ (fun g => ind x (g * x.out)) ≠ 0 := by
      refine hpos _ (sb_right (hind x) _) (fun g => ?_) ⟨1, R.one_mem, by simp [ind]⟩
      simp only [ind]; split_ifs <;> simp
    have := h0 x.out
    simp only [hdec (_ * x.out)] at this
    rw [hsum] at this
    apply mul_right_cancel₀ hc0
    rw [zero_mul, ← this, Finset.sum_mul, Finset.sum_filter]
    refine Finset.sum_congr rfl fun q _ => ?_
    split_ifs with hq
    · obtain ⟨r, rfl⟩ := hq
      congr 1
      rw [← hleft r⁻¹ (R.inv_mem r.2)]
      congr 1; ext g
      change _ = ind ((r : G) • x) _
      rw [hshift, mul_assoc]
    · rw [hcongr (fun g => ind q (g * x.out)) (fun _ => 0), hz, mul_zero]
      intro r hr
      simp only [ind, ite_eq_right_iff]
      intro h
      refine absurd ⟨⟨r, hr⟩, ?_⟩ hq
      rw [← h]
      change r • x = r • ((x.out : G) : G ⧸ K)
      simp
  have hint : ∀ q, ∫ g, ind q g ∂μ = ∫ g, ind ((1 : G) : G ⧸ K) g ∂μ := by
    intro q
    have : q = q.out • ((1 : G) : G ⧸ K) := by
      change q = ((q.out * 1 : G) : G ⧸ K)
      simp
    rw [this]
    simp only [hshift]
    exact integral_mul_left_eq_self _ _
  rw [show (fun g => F g) = fun g => ∑ q ∈ S, F q.out * ind q g from funext hdec, integral_finset_sum]
  · simp only [integral_const_mul, hint]
    rw [← Finset.sum_mul, htot, zero_mul]
  · intro q _
    exact ((hind q).1.continuous.integrable_of_hasCompactSupport (hind q).2).const_mul _

/- English proof (translation)
Take `⟨S, hS⟩` from `finite_quot K ho hΩ`. Set `Φ : G → ℂ` to `fun g => if (g : G ⧸ K) ∈ S then 1 else 0`. Establish `hΦ : Φ ∈ SB G` using `sb_of_quot K ho hc S (fun x => if x ∈ S then 1 else 0) (by intro x hx; simpa using hx)`. Set `A : G → ℂ` to `fun h => Λ (fun g => Φ (g * h))`. Establish `hA : IsLocallyConstant A`.

Rewrite using `[IsLocallyConstant.iff_eventually_eq]`. Introduce `h`. Establish `: IsOpen ((fun y => h⁻¹ * y) ⁻¹' (K : Set G))` using `ho.preimage (by fun_prop)`. Use `filter_upwards [this.mem_nhds (x := h) (by simp [K.one_mem])] with y hy`. Simplify using `only [A, Φ]`.

Use `congr 1`. Use extensionality with `g`. Establish `: ((g * y : G) : G ⧸ K) = ((g * h : G) : G ⧸ K)` using `by symm; rw [QuotientGroup.eq]; simpa [mul_assoc] using hy`. Rewrite using `[this]`. Use `⟨fun g => (f g / A g) * Φ g, ⟨(hf.div hA).mul hΦ.1, hΦ.2.mul_left⟩, fun h => ?_⟩` and prove the remaining obligations.

Rewrite using `[hcongr _ (fun g => (f h / A h) * Φ (g * h)), hsmul]`. Distinguish the cases in `h0 : f h = 0`. Simplify using `[h0]`. Take `⟨r, hr, w, hw, rfl⟩` from `hs h h0`. Establish `: A (r * w) ≠ 0`.

Use `hpos _ (sb_right hΦ _) (fun g => ?_) ⟨r⁻¹, R.inv_mem hr, by simp [Φ, hS w hw]⟩` and prove the remaining obligations. Apply the tactic sequence `simp only [Φ]; split_ifs <;> simp`. Conclude with `(div_mul_cancel₀ _ this).symm`. Introduce `r hr`. Take `⟨d, hd, h1, h2⟩` from `hright r hr`.

Establish `: A (r * h) = d * A h`. Simplify using `only [A]`. Rewrite using `[← h1]`. Simplify using `only [mul_assoc]`. Simplify using `only [this, h2, mul_div_mul_left _ _ hd]`.
-/
theorem exists_avg (K : Subgroup G) (ho : IsOpen (K : Set G)) (hc : IsCompact (K : Set G))
    (R : Subgroup G) (Λ : (G → ℂ) → ℂ)
    (hsmul : ∀ (a : ℂ) φ, Λ (fun g => a * φ g) = a * Λ φ)
    (hcongr : ∀ φ ψ, (∀ r ∈ R, φ r = ψ r) → Λ φ = Λ ψ)
    (hpos : ∀ φ ∈ SB G, (∀ g, φ g = 0 ∨ φ g = 1) → (∃ r ∈ R, φ r = 1) → Λ φ ≠ 0)
    {f : G → ℂ} (hf : IsLocallyConstant f) {Ω : Set G} (hΩ : IsCompact Ω)
    (hs : ∀ h, f h ≠ 0 → ∃ r ∈ R, ∃ w ∈ Ω, h = r * w)
    (hright : ∀ r ∈ R, ∃ d : ℂ, d ≠ 0 ∧ (∀ φ, Λ (fun g => φ (g * r)) = d * Λ φ) ∧ ∀ h, f (r * h) = d * f h) :
    ∃ F ∈ SB G, ∀ h, f h = Λ (fun g => F (g * h)) := by
  classical
  obtain ⟨S, hS⟩ := finite_quot K ho hΩ
  let Φ : G → ℂ := fun g => if (g : G ⧸ K) ∈ S then 1 else 0
  have hΦ : Φ ∈ SB G := sb_of_quot K ho hc S (fun x => if x ∈ S then 1 else 0) (by intro x hx; simpa using hx)
  let A : G → ℂ := fun h => Λ (fun g => Φ (g * h))
  have hA : IsLocallyConstant A := by
    rw [IsLocallyConstant.iff_eventually_eq]
    intro h
    have : IsOpen ((fun y => h⁻¹ * y) ⁻¹' (K : Set G)) := ho.preimage (by fun_prop)
    filter_upwards [this.mem_nhds (x := h) (by simp [K.one_mem])] with y hy
    simp only [A, Φ]
    congr 1; ext g
    have : ((g * y : G) : G ⧸ K) = ((g * h : G) : G ⧸ K) := by
      symm; rw [QuotientGroup.eq]; simpa [mul_assoc] using hy
    rw [this]
  refine ⟨fun g => (f g / A g) * Φ g, ⟨(hf.div hA).mul hΦ.1, hΦ.2.mul_left⟩, fun h => ?_⟩
  rw [hcongr _ (fun g => (f h / A h) * Φ (g * h)), hsmul]
  · by_cases h0 : f h = 0
    · simp [h0]
    · obtain ⟨r, hr, w, hw, rfl⟩ := hs h h0
      have : A (r * w) ≠ 0 := by
        refine hpos _ (sb_right hΦ _) (fun g => ?_) ⟨r⁻¹, R.inv_mem hr, by simp [Φ, hS w hw]⟩
        simp only [Φ]; split_ifs <;> simp
      exact (div_mul_cancel₀ _ this).symm
  · intro r hr
    obtain ⟨d, hd, h1, h2⟩ := hright r hr
    have : A (r * h) = d * A h := by
      simp only [A]
      rw [← h1]; simp only [mul_assoc]
    simp only [this, h2, mul_div_mul_left _ _ hd]

end Abstract

section Concrete
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {n : Type} [Fintype n] [DecidableEq n] {c p : ℕ}

/- English proof (translation)
Apply `Continuous.units_map` to reduce the goal to its premises. Conclude with `Continuous.matrix_fromBlocks continuous_id continuous_const continuous_const continuous_const`.
-/
theorem continuous_embX : Continuous (embX (k := k) (n := n) c) := by
  apply Continuous.units_map
  exact Continuous.matrix_fromBlocks continuous_id continuous_const continuous_const continuous_const

omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
/- English proof (translation)
Use `((GlobalTheory.RootEx.Radical.unipotent_radical_basic k n c p).1 u).1 hu` as an intermediate fact. Use extensionality with `i j`. Establish `h` using `this (Sum.inl i) (Sum.inl j) (le_refl _)`. Simplify using `only [toBlocks₁₁, of_apply, h, Matrix.one_apply, Sum.inl.injEq]`.
-/
theorem block_of_mem {u : GL (n ⊕ Fin c) k} (hu : u ∈ N k n c p) : u.val.toBlocks₁₁ = 1 := by
  have := ((GlobalTheory.RootEx.Radical.unipotent_radical_basic k n c p).1 u).1 hu
  ext i j
  have h := this (Sum.inl i) (Sum.inl j) (le_refl _)
  simp only [toBlocks₁₁, of_apply, h, Matrix.one_apply, Sum.inl.injEq]

omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
/- English proof (translation)
Establish `h` using `block_of_mem hu`. Express the relevant statement in the definitionally equal form `(fromBlocks x.val 0 0 1 * u.val).toBlocks₁₁ = _`. Rewrite using `[← fromBlocks_toBlocks u.val, fromBlocks_multiply, h]`. Simplify using the standard rewrite rules.
-/
theorem block_left (x : GL n k) {u : GL (n ⊕ Fin c) k} (hu : u ∈ N k n c p) :
    (embX c x * u).val.toBlocks₁₁ = x.val := by
  have h := block_of_mem hu
  change (fromBlocks x.val 0 0 1 * u.val).toBlocks₁₁ = _
  rw [← fromBlocks_toBlocks u.val, fromBlocks_multiply, h]
  simp

omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
/- English proof (translation)
Establish `h` using `block_of_mem hu`. Express the relevant statement in the definitionally equal form `(u.val * fromBlocks x.val 0 0 1).toBlocks₁₁ = _`. Rewrite using `[← fromBlocks_toBlocks u.val, fromBlocks_multiply, h]`. Simplify using the standard rewrite rules.
-/
theorem block_right (x : GL n k) {u : GL (n ⊕ Fin c) k} (hu : u ∈ N k n c p) :
    (u * embX c x).val.toBlocks₁₁ = x.val := by
  have h := block_of_mem hu
  change (u.val * fromBlocks x.val 0 0 1).toBlocks₁₁ = _
  rw [← fromBlocks_toBlocks u.val, fromBlocks_multiply, h]
  simp

/- English proof (translation)
Establish `hb : Continuous (fun g : GL (n ⊕ Fin c) k => g.val.toBlocks₁₁)`. Use `continuous_matrix fun i j => ?_` and prove the remaining obligations. Conclude with `(Units.continuous_val.matrix_elem (Sum.inl i) (Sum.inl j))`. Use `haveI : T2Space k := by`. Use `letI := IsTopologicalAddGroup.rightUniformSpace k`.

Use `haveI := isUniformAddGroup_of_addCommGroup (G := k)`. Use `infer_instance`. Establish `h1` using `hC.image hb`. Establish `h2` using `hC.image (MulOpposite.continuous_op.comp (hb.comp continuous_inv))`. Establish `h3` using `(Units.isClosedEmbedding_embedProduct (α := Matrix n n k)).isCompact_preimage (h1.prod h2)`.

Establish `h4` using `(h3.prod hC).image (f := fun z => (embX c z.1)⁻¹ * z.2) ((continuous_embX.comp continuous_fst).inv.mul continuous_snd)`. Establish `h5` using `hN.isClosedEmbedding_subtypeVal.isCompact_preimage h4`. Use `⟨_, h3.prod h5, fun z hz => ?_⟩` and prove the remaining obligations. Establish `hz1 : z.1 ∈ Units.embedProduct (Matrix n n k) ⁻¹' (((fun g : GL (n ⊕ Fin c) k => g.val.toBlocks₁₁) '' C) ×ˢ ((MulOpposite.op ∘ (fun g : GL (n ⊕ Fin c) k => g.val.toBlocks₁₁) ∘ fun a => a⁻¹) '' C))` using `⟨⟨_, hz, block_left z.1 z.2.2⟩, ⟨_, hz, by`. Simplify using `only [Function.comp, _root_.mul_inv_rev, ← map_inv]`.

Rewrite using `[block_right _ ((N k n c p).inv_mem z.2.2)]`. Use the proof step `rfl⟩⟩`. Conclude with `⟨hz1, ⟨(z.1, _), ⟨hz1, hz⟩, by simp⟩⟩`.
-/
theorem compact_preimage (hN : IsClosed (N k n c p : Set (GL (n ⊕ Fin c) k))) {C : Set (GL (n ⊕ Fin c) k)}
    (hC : IsCompact C) : ∃ D : Set (GL n k × N k n c p), IsCompact D ∧
      ∀ z : GL n k × N k n c p, embX c z.1 * (z.2 : GL (n ⊕ Fin c) k) ∈ C → z ∈ D := by
  have hb : Continuous (fun g : GL (n ⊕ Fin c) k => g.val.toBlocks₁₁) := by
    refine continuous_matrix fun i j => ?_
    exact (Units.continuous_val.matrix_elem (Sum.inl i) (Sum.inl j))
  haveI : T2Space k := by
    letI := IsTopologicalAddGroup.rightUniformSpace k
    haveI := isUniformAddGroup_of_addCommGroup (G := k)
    infer_instance
  have h1 := hC.image hb
  have h2 := hC.image (MulOpposite.continuous_op.comp (hb.comp continuous_inv))
  have h3 := (Units.isClosedEmbedding_embedProduct (α := Matrix n n k)).isCompact_preimage (h1.prod h2)
  have h4 := (h3.prod hC).image (f := fun z => (embX c z.1)⁻¹ * z.2)
    ((continuous_embX.comp continuous_fst).inv.mul continuous_snd)
  have h5 := hN.isClosedEmbedding_subtypeVal.isCompact_preimage h4
  refine ⟨_, h3.prod h5, fun z hz => ?_⟩
  have hz1 : z.1 ∈ Units.embedProduct (Matrix n n k) ⁻¹'
      (((fun g : GL (n ⊕ Fin c) k => g.val.toBlocks₁₁) '' C) ×ˢ
        ((MulOpposite.op ∘ (fun g : GL (n ⊕ Fin c) k => g.val.toBlocks₁₁) ∘ fun a => a⁻¹) '' C)) :=
    ⟨⟨_, hz, block_left z.1 z.2.2⟩, ⟨_, hz, by
      simp only [Function.comp, _root_.mul_inv_rev, ← map_inv]
      rw [block_right _ ((N k n c p).inv_mem z.2.2)]
      rfl⟩⟩
  exact ⟨hz1, ⟨(z.1, _), ⟨hz1, hz⟩, by simp⟩⟩

end Concrete

/- English proof (translation)
Introduce `k _ _ _ _ _ _ n _ _ c p hp hpc ν _ μX _ μG _ f`. Take `⟨bX, lX, sX, -, -, -, hXH, hXR⟩` from `GlobalTheory.SplitWeil.volGL_haar k n ν`. Take `⟨bG, lG, sG, hKc, hKo, -⟩` from `GlobalTheory.SplitWeil.volGL_haar k (n ⊕ Fin c) ν`. Take `⟨hN, -, hH, hRi, hconj⟩` from `GlobalTheory.T.rootExchangeUnipotent_haar_and_modulus k n c p hp hpc ν`. Take `⟨-, -, -, hnorm, hdec, -⟩` from `GlobalTheory.RootEx.Radical.unipotent_radical_basic k n c p`.

Use `haveI : LocallyCompactSpace (N k n c p) := hN.isClosedEmbedding_subtypeVal.locallyCompactSpace`. Use `haveI : SecondCountableTopology (N k n c p) := TopologicalSpace.Subtype.secondCountableTopology _`. Use `haveI : SigmaFinite (volN ν n c p) := Measure.IsHaarMeasure.sigmaFinite _`. Use `haveI : μX.IsMulRightInvariant := by`. Rewrite using `[Measure.isMulLeftInvariant_eq_smul μX (volGL ν n)]`.

Use `infer_instance`. Set `Λ : (GL (n ⊕ Fin c) k → ℂ) → ℂ` to `fun φ => ∫ g, (∫ u : N k n c p, φ (embX c g * (u : GL (n ⊕ Fin c) k)) ∂(volN ν n c p)) ∂μX`. Establish `hm : Continuous (fun z : GL n k × N k n c p => embX c z.1 * (z.2 : GL (n ⊕ Fin c) k))` using `(continuous_embX.comp continuous_fst).mul (continuous_subtype_val.comp continuous_snd)`. Establish `hsupp : ∀ φ ∈ SB (GL (n ⊕ Fin c) k), HasCompactSupport (fun z : GL n k × N k n c p => φ (embX c z.1 * (z.2 : GL (n ⊕ Fin c) k)))`. Introduce `φ hφ`.

Take `⟨D, hD, h⟩` from `compact_preimage hN hφ.2`. Conclude with `HasCompactSupport.intro hD fun z hz => image_eq_zero_of_notMem_tsupport fun h' => hz (h z h')`. Establish `hint : ∀ φ ∈ SB (GL (n ⊕ Fin c) k), Integrable (fun z : GL n k × N k n c p => φ (embX c z.1 * (z.2 : GL (n ⊕ Fin c) k))) (μX.prod (volN ν n c p))` using `fun φ hφ => (hφ.1.continuous.comp hm).integrable_of_hasCompactSupport (hsupp φ hφ)`. Establish `hprod : ∀ φ ∈ SB (GL (n ⊕ Fin c) k), Λ φ = ∫ z : GL n k × N k n c p, φ (embX c z.1 * (z.2 : GL (n ⊕ Fin c) k)) ∂(μX.prod (volN ν n c p))` using `fun φ hφ => (integral_prod _ (hint φ hφ)).symm`. Establish `hadd : ∀ φ ∈ SB _, ∀ ψ ∈ SB _, Λ (φ + ψ) = Λ φ + Λ ψ`.

Introduce `φ hφ ψ hψ`. Rewrite using `[hprod _ hφ, hprod _ hψ, hprod _ (add_mem hφ hψ), ← integral_add (hint φ hφ) (hint ψ hψ)]`. Both sides reduce to the same expression. Establish `hsmul : ∀ (a : ℂ) φ, Λ (fun g => a * φ g) = a * Λ φ`. Introduce `a φ`.

Simplify using `only [Λ, integral_const_mul]`. Establish `hmem : ∀ (g : GL n k) (u : N k n c p), embX c g * (u : GL (n ⊕ Fin c) k) ∈ R k n c p` using `fun g u => mul_mem (Subgroup.mem_sup_left ⟨g, rfl⟩) (Subgroup.mem_sup_right u.2)`. Establish `hcongr : ∀ φ ψ, (∀ r ∈ R k n c p, φ r = ψ r) → Λ φ = Λ ψ`. Introduce `φ ψ h`. Simplify using `only [Λ, fun g u => h _ (hmem g u)]`.

Establish `hleft : ∀ r ∈ R k n c p, ∀ φ, Λ (fun g => φ (r * g)) = Λ φ`. Introduce `r hr φ`. Take `⟨⟨x, u₀⟩, rfl, -⟩` from `hdec r hr`. Simplify using `only [Λ]`. Rewrite using `[← integral_mul_left_eq_self (fun g => ∫ u : N k n c p, φ (embX c g * (u : GL (n ⊕ Fin c) k)) ∂(volN ν n c p)) x]`.

Use `congr 1`. Use extensionality with `g`. Rewrite using `[← integral_mul_left_eq_self (fun u : N k n c p => φ (embX c (x * g) * (u : GL (n ⊕ Fin c) k))) ⟨_, (hnorm g⁻¹ _ u₀.2).1⟩]`. Use `congr 1`. Use extensionality with `u`.

Simplify using `[mul_assoc]`. Establish `hpos : ∀ φ ∈ SB _, (∀ g, φ g = 0 ∨ φ g = 1) → (∃ r ∈ R k n c p, φ r = 1) → Λ φ ≠ 0`. Introduce and unpack `φ hφ h01 ⟨r, hr, h1⟩`. Take `⟨z₀, rfl, -⟩` from `hdec r hr`. Rewrite using `[hprod _ hφ]`.

Use `set V : Set (GL n k × N k n c p) := {z | φ (embX c z.1 * (z.2 : GL (n ⊕ Fin c) k)) = 1} with hV`. Establish `hVo : IsOpen V` using `(hφ.1.comp_continuous hm).isOpen_fiber 1`. Establish `hVs : V ⊆ tsupport (fun z : GL n k × N k n c p => φ (embX c z.1 * (z.2 : GL (n ⊕ Fin c) k)))`. Introduce `z hz`. Apply `subset_tsupport` to reduce the goal to its premises.

Rewrite using `[Function.mem_support, show φ _ = 1 from hz]`. Conclude with `one_ne_zero`. Establish `hfin : (μX.prod (volN ν n c p)) V ≠ ⊤` using `((measure_mono hVs).trans_lt (IsCompact.measure_lt_top (hsupp φ hφ))).ne`. Establish `hne : (μX.prod (volN ν n c p)) V ≠ 0` using `hVo.measure_ne_zero _ ⟨z₀, h1⟩`. Establish `: (fun z : GL n k × N k n c p => φ (embX c z.1 * (z.2 : GL (n ⊕ Fin c) k))) = V.indicator (fun _ => (1 : ℂ))`.

Use extensionality with `z`. Distinguish the cases in `hz : z ∈ V`. Rewrite using `[Set.indicator_of_mem hz]`. Conclude with `hz`. Rewrite using `[Set.indicator_of_notMem hz]`.

Conclude with `(h01 _).resolve_right hz`. Rewrite using `[this, integral_indicator_const _ hVo.measurableSet]`. Simplify using `[Measure.real, ENNReal.toReal_eq_zero_iff, hfin, hne]`. Use `⟨?_, fun hf ⟨Ω, hΩ, hs⟩ hequiv => ?_⟩` and prove the remaining obligations. Introduce and unpack `z z' ⟨F, hF, hF1, rfl⟩ ⟨F', hF', hF1', rfl⟩`.

Establish `h` using `integral_eq_zero_of_avg μG _ hKo hKc _ Λ hadd hsmul hcongr hleft hpos (sub_mem hF hF') (by`. Introduce `h`. Use `hadd _ (sb_right (sub_mem hF hF') h) _ (sb_right hF' h)` as an intermediate fact. Rewrite `this` using `[show ((fun g => (F - F') (g * h)) + fun g => F' (g * h)) = fun g => F (g * h) by ext; simp]`. Establish `e1 : Λ (fun g => F (g * h)) = f h` using `(hF1 h).symm`.

Establish `e2 : Λ (fun g => F' (g * h)) = f h` using `(hF1' h).symm`. Rewrite `this` using `[e1, e2]`. Simplify using `using this)`. Simplify using `only [Pi.sub_apply] at h`. Rewrite `h` using `[integral_sub (hF.1.continuous.integrable_of_hasCompactSupport hF.2) (hF'.1.continuous.integrable_of_hasCompactSupport hF'.2), sub_eq_zero]`. Then use the resulting hypothesis.

Take `⟨F, hF, h⟩` from `exists_avg _ hKo hKc _ Λ hsmul hcongr hpos hf hΩ hs (by`. Introduce `r hr`. Take `⟨⟨x, u₀⟩, rfl, -⟩` from `hdec r hr`. Establish `hpos' : ∀ y, 0 < nabs k y` using `fun y => by`. Simplify using `only [nabs]`.

Conclude with `distribHaarChar_pos` after adjusting the coercions. Use `⟨_, ?_, fun φ => ?_, hequiv x u₀ u₀.2⟩` and prove the remaining obligations. Conclude with `Complex.ofReal_ne_zero.2 (Real.rpow_pos_of_pos (hpos' _) _).ne'`. Simplify using `only [Λ]`. Rewrite using `[← integral_mul_right_eq_self (fun g => ∫ u : N k n c p, φ (embX c g * (u : GL (n ⊕ Fin c) k)) ∂(volN ν n c p)) x, ← integral_const_mul]`.

Use `congr 1`. Use extensionality with `g`. Establish `h1` using `hconj x⁻¹ (fun y => φ (embX c g * embX c x * y * u₀))`. Establish `h2` using `integral_mul_right_eq_self (μ := volN ν n c p) (fun u : N k n c p => φ (embX c (g * x) * (u : GL (n ⊕ Fin c) k))) u₀`. Establish `h3 : nabs k (Matrix.GeneralLinearGroup.det x⁻¹) = (nabs k (Matrix.GeneralLinearGroup.det x))⁻¹`.

Simplify using `[nabs]`. Rewrite `h1` using `[h3, Real.inv_rpow (hpos' _).le, ← Real.rpow_neg (hpos' _).le, neg_neg, Complex.real_smul]`. Rewrite using `[← h2]`. Simplify `h1)` using `[mul_assoc]`. Conclude with `⟨_, F, hF, h, rfl⟩`.
-/
theorem quotInt_unique_exists : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (n : Type) [Fintype n] [DecidableEq n] (c p : ℕ) (_ : 1 ≤ p) (_ : p ≤ c) (ν : Measure k) [ν.IsAddHaarMeasure] (μX : Measure (GL n k)) [μX.IsHaarMeasure] (μG : Measure (GL (n ⊕ Fin c) k)) [μG.IsHaarMeasure] (f : GL (n ⊕ Fin c) k → ℂ), (∀ z z', IsQuotInt ν μX μG p f z → IsQuotInt ν μX μG p f z' → z = z') ∧ (IsLocallyConstant f → (∃ Ω, IsCompact Ω ∧ ∀ h, f h ≠ 0 → ∃ r ∈ R k n c p, ∃ w ∈ Ω, h = r * w) → (∀ (x : GL n k), ∀ u ∈ N k n c p, ∀ h, f (embX c x * u * h) = ((nabs k (Matrix.GeneralLinearGroup.det x) ^ ((c : ℝ) + 1 - 2 * p) : ℝ) : ℂ) * f h) → ∃ z, IsQuotInt ν μX μG p f z) := by
  intro k _ _ _ _ _ _ n _ _ c p hp hpc ν _ μX _ μG _ f
  classical
  obtain ⟨bX, lX, sX, -, -, -, hXH, hXR⟩ := GlobalTheory.SplitWeil.volGL_haar k n ν
  obtain ⟨bG, lG, sG, hKc, hKo, -⟩ := GlobalTheory.SplitWeil.volGL_haar k (n ⊕ Fin c) ν
  obtain ⟨hN, -, hH, hRi, hconj⟩ := GlobalTheory.T.rootExchangeUnipotent_haar_and_modulus k n c p hp hpc ν
  obtain ⟨-, -, -, hnorm, hdec, -⟩ := GlobalTheory.RootEx.Radical.unipotent_radical_basic k n c p
  haveI : LocallyCompactSpace (N k n c p) := hN.isClosedEmbedding_subtypeVal.locallyCompactSpace
  haveI : SecondCountableTopology (N k n c p) :=
    TopologicalSpace.Subtype.secondCountableTopology _
  haveI : SigmaFinite (volN ν n c p) := Measure.IsHaarMeasure.sigmaFinite _
  haveI : μX.IsMulRightInvariant := by
    rw [Measure.isMulLeftInvariant_eq_smul μX (volGL ν n)]
    infer_instance
  let Λ : (GL (n ⊕ Fin c) k → ℂ) → ℂ := fun φ =>
    ∫ g, (∫ u : N k n c p, φ (embX c g * (u : GL (n ⊕ Fin c) k)) ∂(volN ν n c p)) ∂μX
  have hm : Continuous (fun z : GL n k × N k n c p => embX c z.1 * (z.2 : GL (n ⊕ Fin c) k)) :=
    (continuous_embX.comp continuous_fst).mul (continuous_subtype_val.comp continuous_snd)
  have hsupp : ∀ φ ∈ SB (GL (n ⊕ Fin c) k),
      HasCompactSupport (fun z : GL n k × N k n c p => φ (embX c z.1 * (z.2 : GL (n ⊕ Fin c) k))) := by
    intro φ hφ
    obtain ⟨D, hD, h⟩ := compact_preimage hN hφ.2
    exact HasCompactSupport.intro hD fun z hz => image_eq_zero_of_notMem_tsupport fun h' => hz (h z h')
  have hint : ∀ φ ∈ SB (GL (n ⊕ Fin c) k), Integrable
      (fun z : GL n k × N k n c p => φ (embX c z.1 * (z.2 : GL (n ⊕ Fin c) k))) (μX.prod (volN ν n c p)) :=
    fun φ hφ => (hφ.1.continuous.comp hm).integrable_of_hasCompactSupport (hsupp φ hφ)
  have hprod : ∀ φ ∈ SB (GL (n ⊕ Fin c) k), Λ φ =
      ∫ z : GL n k × N k n c p, φ (embX c z.1 * (z.2 : GL (n ⊕ Fin c) k)) ∂(μX.prod (volN ν n c p)) :=
    fun φ hφ => (integral_prod _ (hint φ hφ)).symm
  have hadd : ∀ φ ∈ SB _, ∀ ψ ∈ SB _, Λ (φ + ψ) = Λ φ + Λ ψ := by
    intro φ hφ ψ hψ
    rw [hprod _ hφ, hprod _ hψ, hprod _ (add_mem hφ hψ), ← integral_add (hint φ hφ) (hint ψ hψ)]
    rfl
  have hsmul : ∀ (a : ℂ) φ, Λ (fun g => a * φ g) = a * Λ φ := by
    intro a φ
    simp only [Λ, integral_const_mul]
  have hmem : ∀ (g : GL n k) (u : N k n c p), embX c g * (u : GL (n ⊕ Fin c) k) ∈ R k n c p :=
    fun g u => mul_mem (Subgroup.mem_sup_left ⟨g, rfl⟩) (Subgroup.mem_sup_right u.2)
  have hcongr : ∀ φ ψ, (∀ r ∈ R k n c p, φ r = ψ r) → Λ φ = Λ ψ := by
    intro φ ψ h
    simp only [Λ, fun g u => h _ (hmem g u)]
  have hleft : ∀ r ∈ R k n c p, ∀ φ, Λ (fun g => φ (r * g)) = Λ φ := by
    intro r hr φ
    obtain ⟨⟨x, u₀⟩, rfl, -⟩ := hdec r hr
    simp only [Λ]
    rw [← integral_mul_left_eq_self
      (fun g => ∫ u : N k n c p, φ (embX c g * (u : GL (n ⊕ Fin c) k)) ∂(volN ν n c p)) x]
    congr 1; ext g
    rw [← integral_mul_left_eq_self (fun u : N k n c p => φ (embX c (x * g) * (u : GL (n ⊕ Fin c) k)))
      ⟨_, (hnorm g⁻¹ _ u₀.2).1⟩]
    congr 1; ext u
    simp [mul_assoc]
  have hpos : ∀ φ ∈ SB _, (∀ g, φ g = 0 ∨ φ g = 1) → (∃ r ∈ R k n c p, φ r = 1) → Λ φ ≠ 0 := by
    rintro φ hφ h01 ⟨r, hr, h1⟩
    obtain ⟨z₀, rfl, -⟩ := hdec r hr
    rw [hprod _ hφ]
    set V : Set (GL n k × N k n c p) := {z | φ (embX c z.1 * (z.2 : GL (n ⊕ Fin c) k)) = 1} with hV
    have hVo : IsOpen V := (hφ.1.comp_continuous hm).isOpen_fiber 1
    have hVs : V ⊆ tsupport (fun z : GL n k × N k n c p => φ (embX c z.1 * (z.2 : GL (n ⊕ Fin c) k))) := by
      intro z hz
      apply subset_tsupport
      rw [Function.mem_support, show φ _ = 1 from hz]
      exact one_ne_zero
    have hfin : (μX.prod (volN ν n c p)) V ≠ ⊤ :=
      ((measure_mono hVs).trans_lt (IsCompact.measure_lt_top (hsupp φ hφ))).ne
    have hne : (μX.prod (volN ν n c p)) V ≠ 0 := hVo.measure_ne_zero _ ⟨z₀, h1⟩
    have : (fun z : GL n k × N k n c p => φ (embX c z.1 * (z.2 : GL (n ⊕ Fin c) k))) =
        V.indicator (fun _ => (1 : ℂ)) := by
      ext z
      by_cases hz : z ∈ V
      · rw [Set.indicator_of_mem hz]; exact hz
      · rw [Set.indicator_of_notMem hz]; exact (h01 _).resolve_right hz
    rw [this, integral_indicator_const _ hVo.measurableSet]
    simp [Measure.real, ENNReal.toReal_eq_zero_iff, hfin, hne]
  refine ⟨?_, fun hf ⟨Ω, hΩ, hs⟩ hequiv => ?_⟩
  · rintro z z' ⟨F, hF, hF1, rfl⟩ ⟨F', hF', hF1', rfl⟩
    have h := integral_eq_zero_of_avg μG _ hKo hKc _ Λ hadd hsmul hcongr hleft hpos (sub_mem hF hF') (by
      intro h
      have := hadd _ (sb_right (sub_mem hF hF') h) _ (sb_right hF' h)
      rw [show ((fun g => (F - F') (g * h)) + fun g => F' (g * h)) = fun g => F (g * h) by ext; simp] at this
      have e1 : Λ (fun g => F (g * h)) = f h := (hF1 h).symm
      have e2 : Λ (fun g => F' (g * h)) = f h := (hF1' h).symm
      rw [e1, e2] at this
      simpa using this)
    simp only [Pi.sub_apply] at h
    rwa [integral_sub (hF.1.continuous.integrable_of_hasCompactSupport hF.2)
      (hF'.1.continuous.integrable_of_hasCompactSupport hF'.2), sub_eq_zero] at h
  · obtain ⟨F, hF, h⟩ := exists_avg _ hKo hKc _ Λ hsmul hcongr hpos hf hΩ hs (by
      intro r hr
      obtain ⟨⟨x, u₀⟩, rfl, -⟩ := hdec r hr
      have hpos' : ∀ y, 0 < nabs k y := fun y => by
        simp only [nabs]; exact_mod_cast distribHaarChar_pos
      refine ⟨_, ?_, fun φ => ?_, hequiv x u₀ u₀.2⟩
      · exact Complex.ofReal_ne_zero.2 (Real.rpow_pos_of_pos (hpos' _) _).ne'
      · simp only [Λ]
        rw [← integral_mul_right_eq_self
          (fun g => ∫ u : N k n c p, φ (embX c g * (u : GL (n ⊕ Fin c) k)) ∂(volN ν n c p)) x,
          ← integral_const_mul]
        congr 1; ext g
        have h1 := hconj x⁻¹ (fun y => φ (embX c g * embX c x * y * u₀))
        have h2 := integral_mul_right_eq_self (μ := volN ν n c p)
          (fun u : N k n c p => φ (embX c (g * x) * (u : GL (n ⊕ Fin c) k))) u₀
        have h3 : nabs k (Matrix.GeneralLinearGroup.det x⁻¹) = (nabs k (Matrix.GeneralLinearGroup.det x))⁻¹ := by
          simp [nabs]
        rw [h3, Real.inv_rpow (hpos' _).le, ← Real.rpow_neg (hpos' _).le, neg_neg, Complex.real_smul] at h1
        rw [← h2]
        simpa [mul_assoc] using h1)
    exact ⟨_, F, hF, h, rfl⟩

end GlobalTheory.QuotInt

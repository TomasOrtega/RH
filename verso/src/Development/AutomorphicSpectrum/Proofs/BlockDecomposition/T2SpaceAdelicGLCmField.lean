import Mathlib
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.IsotropicMahlerBounds.OnlyIsotropic
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.QuotientVanishing.QuotVanish
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsNormalisedThetaSub
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.LcscAdelicUnitaryGroup
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqZeroOfAdelicFourierSeparatingCharsVanish
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FiniteTwConjOfIsTest
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LintegralTsumEnormNeTop
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.OnlyStableSubspaces

noncomputable section
open NumberField IsDedekindDomain Matrix MeasureTheory
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.Tf.Loc PositivityTheory.Rg.BcB
open scoped Pointwise ENNReal

namespace GlobalTheory.CompanionTheory.UnfoldCut

section Group

variable {D G : Type} [Group D] [Group G]

/- English proof (translation)
Simplify using `only [twConj, map_mul]`. Use `group`.
-/
theorem twConj_mul' (θ : Monoid.End G) (a b δ : G) :
    twConj θ (a * b) δ = twConj θ b (twConj θ a δ) := by
  simp only [twConj, map_mul]; group

/- English proof (translation)
Simplify using `[twConj, hθ]`.
-/
theorem twConj_map' (ι : D →* G) (θD : Monoid.End D) (θ : Monoid.End G)
    (hθ : ∀ d, θ (ι d) = ι (θD d)) (g δ : D) :
    twConj θ (ι g) (ι δ) = ι (twConj θD g δ) := by
  simp [twConj, hθ]

/- English proof (translation)
Assemble the required witnesses or components as `⟨1, by simp [twConj]⟩ symm := by rintro a b ⟨g, rfl⟩ exact ⟨g⁻¹, by simp only [twConj, map_inv]; group⟩ trans := by rintro a b c ⟨g, rfl⟩ ⟨h, rfl⟩ exact ⟨g * h, (twConj_mul' θ g h a).symm⟩`.
-/
theorem twConjugate_equivalence (θ : Monoid.End D) : Equivalence (TwConjugate θ) where
  refl δ := ⟨1, by simp [twConj]⟩
  symm := by
    rintro a b ⟨g, rfl⟩
    exact ⟨g⁻¹, by simp only [twConj, map_inv]; group⟩
  trans := by
    rintro a b c ⟨g, rfl⟩ ⟨h, rfl⟩
    exact ⟨g * h, (twConj_mul' θ g h a).symm⟩

/- English proof (translation)
The claim follows from `(twConjugate_equivalence θ).quot_mk_eq_iff a b`.
-/
theorem cl_eq_iff (θ : Monoid.End D) (a b : D) :
    Quot.mk (TwConjugate θ) a = Quot.mk (TwConjugate θ) b ↔ TwConjugate θ a b :=
  (twConjugate_equivalence θ).quot_mk_eq_iff a b

/- English proof (translation)
Establish `hρ : ∀ q : ι.range ⧸ ((twCent θD δ).map ι).subgroupOf ι.range, ∃ ρ : D, ι ρ = ((q.out : ι.range) : G)⁻¹` using `fun q => by`. Take `⟨r, hr⟩` from `(q.out : ι.range).2`. Conclude with `⟨r⁻¹, by rw [map_inv, hr]⟩`. Use `choose ρ hρ using hρ`. Set `b : (ι.range ⧸ ((twCent θD δ).map ι).subgroupOf ι.range) → {d : D // TwConjugate θD δ d}` to `fun q => ⟨twConj θD (ρ q) δ, ρ q, rfl⟩`.

Establish `hb : Function.Bijective b`. Prove the components needed by the constructor for the conclusion. Introduce `q q' h`. Establish `h1 : twConj θD (ρ q) δ = twConj θD (ρ q') δ` using `congrArg Subtype.val h`. Establish `h2 : ρ q * (ρ q')⁻¹ ∈ twCent θD δ`.

Express the relevant statement in the definitionally equal form `twConj θD (ρ q * (ρ q')⁻¹) δ = δ`. Rewrite using `[twConj_mul', h1, ← twConj_mul']`. Simplify using `[twConj]`. Rewrite using `[← QuotientGroup.out_eq' q, ← QuotientGroup.out_eq' q', QuotientGroup.eq]`. Rewrite using `[Subgroup.mem_subgroupOf]`.

Use `⟨_, h2, ?_⟩` and prove the remaining obligations. Simplify using `only [map_mul, map_inv, hρ, inv_inv, Subgroup.coe_mul, InvMemClass.coe_inv]`. Introduce and unpack `⟨d, g, rfl⟩`. Set `γ : ι.range` to `⟨ι g⁻¹, g⁻¹, rfl⟩`. Set `q : ι.range ⧸ ((twCent θD δ).map ι).subgroupOf ι.range` to `QuotientGroup.mk γ`.

Use `⟨q, Subtype.ext ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `twConj θD (ρ q) δ = twConj θD g δ`. Establish `h1 : γ⁻¹ * q.out ∈ ((twCent θD δ).map ι).subgroupOf ι.range`. Rewrite using `[← QuotientGroup.eq]`. Conclude with `(QuotientGroup.out_eq' q).symm`.

Rewrite `h1` using `[Subgroup.mem_subgroupOf]`. Take `⟨t, ht, hte⟩` from `h1`. Establish `h2 : ρ q = t⁻¹ * g`. Apply `hι` to reduce the goal to its premises. Rewrite using `[hρ q, map_mul, map_inv, hte]`.

Simplify using `[γ]`. Rewrite using `[h2, twConj_mul']`. Use `congr 1`. Use `(twCent θD δ).inv_mem ht` as an intermediate fact. Conclude with `this`.

Use `⟨Equiv.ofBijective b hb, fun q => ⟨ρ q, hρ q, rfl⟩⟩` and prove the remaining obligations.
-/
theorem exists_class_equiv (ι : D →* G) (hι : Function.Injective ι) (θD : Monoid.End D) (δ : D) :
    ∃ e : (ι.range ⧸ ((twCent θD δ).map ι).subgroupOf ι.range) ≃ {d : D // TwConjugate θD δ d},
      ∀ q, ∃ ρ : D, ι ρ = ((q.out : ι.range) : G)⁻¹ ∧ (e q : D) = twConj θD ρ δ := by
  classical
  have hρ : ∀ q : ι.range ⧸ ((twCent θD δ).map ι).subgroupOf ι.range,
      ∃ ρ : D, ι ρ = ((q.out : ι.range) : G)⁻¹ := fun q => by
    obtain ⟨r, hr⟩ := (q.out : ι.range).2
    exact ⟨r⁻¹, by rw [map_inv, hr]⟩
  choose ρ hρ using hρ
  let b : (ι.range ⧸ ((twCent θD δ).map ι).subgroupOf ι.range) → {d : D // TwConjugate θD δ d} :=
    fun q => ⟨twConj θD (ρ q) δ, ρ q, rfl⟩
  have hb : Function.Bijective b := by
    constructor
    · intro q q' h
      have h1 : twConj θD (ρ q) δ = twConj θD (ρ q') δ := congrArg Subtype.val h
      have h2 : ρ q * (ρ q')⁻¹ ∈ twCent θD δ := by
        change twConj θD (ρ q * (ρ q')⁻¹) δ = δ
        rw [twConj_mul', h1, ← twConj_mul']
        simp [twConj]
      rw [← QuotientGroup.out_eq' q, ← QuotientGroup.out_eq' q', QuotientGroup.eq]
      rw [Subgroup.mem_subgroupOf]
      refine ⟨_, h2, ?_⟩
      simp only [map_mul, map_inv, hρ, inv_inv, Subgroup.coe_mul, InvMemClass.coe_inv]
    · rintro ⟨d, g, rfl⟩
      let γ : ι.range := ⟨ι g⁻¹, g⁻¹, rfl⟩
      let q : ι.range ⧸ ((twCent θD δ).map ι).subgroupOf ι.range := QuotientGroup.mk γ
      refine ⟨q, Subtype.ext ?_⟩
      change twConj θD (ρ q) δ = twConj θD g δ
      have h1 : γ⁻¹ * q.out ∈ ((twCent θD δ).map ι).subgroupOf ι.range := by
        rw [← QuotientGroup.eq]
        exact (QuotientGroup.out_eq' q).symm
      rw [Subgroup.mem_subgroupOf] at h1
      obtain ⟨t, ht, hte⟩ := h1
      have h2 : ρ q = t⁻¹ * g := by
        apply hι
        rw [hρ q, map_mul, map_inv, hte]
        simp [γ]
      rw [h2, twConj_mul']
      congr 1
      have := (twCent θD δ).inv_mem ht
      exact this
  refine ⟨Equiv.ofBijective b hb, fun q => ⟨ρ q, hρ q, rfl⟩⟩

end Group

section Measure

variable {D G : Type} [Group D] [Group G]

def hh (S : Set G) (θ : Monoid.End G) (ι : D →* G) (φ : G → ℂ) (x : G) (d : D) : ℂ :=
  S.indicator (1 : G → ℂ) x * φ (twConj θ x (ι d))

/- English proof (translation)
Establish `h1 : S.indicator (1 : G → ℂ) (ι g * x) = S.indicator (1 : G → ℂ) x`. Distinguish the cases in `hx : x ∈ S`. Rewrite using `[Set.indicator_of_mem hx, Set.indicator_of_mem ((hSinv g x).2 hx)]`. Both sides reduce to the same expression. Rewrite using `[Set.indicator_of_notMem hx, Set.indicator_of_notMem (fun h => hx ((hSinv g x).1 h))]`.

Rewrite using `[hh, hh, h1, twConj_mul', twConj_map' ι θD θ hθ]`.
-/
theorem hh_shift {S : Set G} {θ : Monoid.End G} {ι : D →* G} {θD : Monoid.End D}
    (hθ : ∀ d, θ (ι d) = ι (θD d)) (hSinv : ∀ g x, ι g * x ∈ S ↔ x ∈ S) (φ : G → ℂ)
    (g : D) (x : G) (d : D) :
    hh S θ ι φ (ι g * x) d = hh S θ ι φ x (twConj θD g d) := by
  have h1 : S.indicator (1 : G → ℂ) (ι g * x) = S.indicator (1 : G → ℂ) x := by
    by_cases hx : x ∈ S
    · rw [Set.indicator_of_mem hx, Set.indicator_of_mem ((hSinv g x).2 hx)]; rfl
    · rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem (fun h => hx ((hSinv g x).1 h))]
  rw [hh, hh, h1, twConj_mul', twConj_map' ι θD θ hθ]

def twEquiv (θD : Monoid.End D) (g : D) : D ≃ D where
  toFun := twConj θD g
  invFun := twConj θD g⁻¹
  left_inv d := by rw [← twConj_mul']; simp [twConj]
  right_inv d := by rw [← twConj_mul']; simp [twConj]

/- English proof (translation)
Simplify using `[hh, Set.indicator_of_notMem hx]`.
-/
theorem hh_of_notMem {S : Set G} {θ : Monoid.End G} {ι : D →* G} {φ : G → ℂ} {x : G} (hx : x ∉ S)
    (d : D) : hh S θ ι φ x d = 0 := by
  simp [hh, Set.indicator_of_notMem hx]

/- English proof (translation)
Rewrite using `[← ofReal_norm]`. Use `ENNReal.ofReal_le_ofReal ?_` and prove the remaining obligations. Distinguish the cases in `hx : x ∈ S`. Simplify `hM _` using `[hh, Set.indicator_of_mem hx]`. Rewrite using `[hh_of_notMem hx]`.

Simplify using `using (norm_nonneg _).trans (hM 1)`.
-/
theorem enorm_hh_le {S : Set G} {θ : Monoid.End G} {ι : D →* G} {φ : G → ℂ} {M : ℝ}
    (hM : ∀ g, ‖φ g‖ ≤ M) (x : G) (d : D) : ‖hh S θ ι φ x d‖ₑ ≤ ENNReal.ofReal M := by
  rw [← ofReal_norm]
  refine ENNReal.ofReal_le_ofReal ?_
  by_cases hx : x ∈ S
  · simpa [hh, Set.indicator_of_mem hx] using hM _
  · rw [hh_of_notMem hx]; simpa using (norm_nonneg _).trans (hM 1)

/- English proof (translation)
Take `⟨a, ⟨g, rfl⟩, c, hc, rfl⟩` from `Set.mem_mul.1 (hSC hx)`. Conclude with `⟨g, c, hc, rfl⟩`.
-/
theorem exists_of_mem {S C : Set G} {ι : D →* G} (hSC : S ⊆ (ι.range : Set G) * C) {x : G}
    (hx : x ∈ S) : ∃ g : D, ∃ c ∈ C, x = ι g * c := by
  obtain ⟨a, ⟨g, rfl⟩, c, hc, rfl⟩ := Set.mem_mul.1 (hSC hx)
  exact ⟨g, c, hc, rfl⟩

/- English proof (translation)
Use `haveI : Countable ι.range := (Set.countable_range ι).to_subtype`. Rewrite using `[hF.measure_eq_tsum C]`. Use `le_trans (measure_mono ?_) (measure_iUnion_le _)` and prove the remaining obligations. Introduce and unpack `x ⟨hx, hxF⟩`. Take `⟨a, ha, c, hc, rfl⟩` from `Set.mem_mul.1 (hSC hx)`.

Conclude with `Set.mem_iUnion.2 ⟨⟨a, ha⟩, ⟨c, hc, rfl⟩, hxF⟩`.
-/
theorem measure_inter_le [MeasurableSpace G] [MeasurableMul G] [Countable D] {ι : D →* G}
    {μ : Measure G} [μ.IsMulLeftInvariant] {F S C : Set G}
    (hF : IsFundamentalDomain ι.range F μ) (hSC : S ⊆ (ι.range : Set G) * C) :
    μ (S ∩ F) ≤ μ C := by
  haveI : Countable ι.range := (Set.countable_range ι).to_subtype
  rw [hF.measure_eq_tsum C]
  refine le_trans (measure_mono ?_) (measure_iUnion_le _)
  rintro x ⟨hx, hxF⟩
  obtain ⟨a, ha, c, hc, rfl⟩ := Set.mem_mul.1 (hSC hx)
  exact Set.mem_iUnion.2 ⟨⟨a, ha⟩, ⟨c, hc, rfl⟩, hxF⟩

end Measure

section Main

variable {D G : Type} [Group D] [Countable D] [Group G] [MeasurableSpace G] [MeasurableMul G]

/- English proof (translation)
Use `set h := hh S θ ι φ with hdef`. Use `set P : Finset D := hfin.toFinset with hP`. Set `cl : D → Quot (TwConjugate θD)` to `Quot.mk _`. Set `T : Finset (Quot (TwConjugate θD))` to `P.image cl`. Establish `hmemP : ∀ c ∈ C, ∀ d, h c d ≠ 0 → d ∈ P` using `fun c hc d hd => by`.

Use `hfin.mem_toFinset.2 ⟨c, hc, fun h0 => hd ?_⟩` and prove the remaining obligations. Simplify using `[hdef, hh, h0]`. Establish `hshift : ∀ g x d, h (ι g * x) d = h x (twConj θD g d)` using `fun g x d => hh_shift hθ hSinv φ g x d`. Establish `hsupp : ∀ x, (Function.support (h x)).Finite` using `fun x => by`. Distinguish the cases in `hx : x ∈ S`.

Take `⟨g, c, hc, rfl⟩` from `exists_of_mem hSC hx`. Use `(P.finite_toSet.preimage (twEquiv θD g).injective.injOn).subset fun d hd => ?_` and prove the remaining obligations. Use `hmemP c hc _ ?_` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `h c (twConj θD g d) ≠ 0`. Rewrite using `[← hshift]`.

Conclude with `hd`. Establish `: Function.support (h x) = ∅`. Use extensionality with `d`. Simplify using `[hdef, hh_of_notMem hx]`. Rewrite using `[this]`.

Conclude with `Set.finite_empty`. Use `set B : ℝ≥0∞ := P.card * ENNReal.ofReal M with hB`. Establish `hbd : ∀ x, ∑' d, ‖h x d‖ₑ ≤ S.indicator (fun _ => B) x` using `fun x => by`. Distinguish the cases in `hx : x ∈ S`. Rewrite using `[Set.indicator_of_mem hx]`.

Take `⟨g, c, hc, rfl⟩` from `exists_of_mem hSC hx`. Establish `e1 : ∑' d, ‖h (ι g * c) d‖ₑ = ∑' d, ‖h c d‖ₑ`. Repeatedly rewrite using `[hshift]`. Conclude with `(twEquiv θD g).tsum_eq fun d => ‖h c d‖ₑ`. Rewrite using `[e1, tsum_eq_sum (s := P) fun d hd => by`.

Rewrite using `[enorm_eq_zero]`. Assume the negation of the conclusion as `h0`. Conclude with `hd (hmemP c hc d h0)]`. Use `(Finset.sum_le_card_nsmul _ _ _ fun d _ => enorm_hh_le hM c d).trans ?_` and prove the remaining obligations. Simplify using `[hB]`.

Simplify using `[hdef, hh_of_notMem hx, Set.indicator_of_notMem hx]`. Establish `hBfin : B ≠ ∞` using `ENNReal.mul_ne_top (ENNReal.natCast_ne_top _) ENNReal.ofReal_ne_top`. Establish `hA : ∫⁻ x in F, ∑' d, ‖h x d‖ₑ ∂μ < ∞`. Use `lt_of_le_of_lt (lintegral_mono hbd) ?_` and prove the remaining obligations. Rewrite using `[lintegral_indicator hS, setLIntegral_const, Measure.restrict_apply hS]`.

Conclude with `ENNReal.mul_lt_top hBfin.lt_top ((measure_inter_le hF hSC).trans_lt hC.lt_top)`. Establish `hzero : ∀ c ∉ T, ∀ d, cl d = c → ∀ x, h x d = 0` using `fun c hc d hd x => by`. Distinguish the cases in `hx : x ∈ S`. Take `⟨g, c', hc', rfl⟩` from `exists_of_mem hSC hx`. Assume the negation of the conclusion as `h0`.

Rewrite `h0` using `[hshift]`. Use `hc (Finset.mem_image.2 ⟨_, hmemP c' hc' _ h0, ?_⟩)` and prove the remaining obligations. Rewrite using `[← hd]`. Conclude with `((cl_eq_iff θD d _).2 ⟨g, rfl⟩).symm`. Conclude with `hh_of_notMem hx d`.

Set `gc : Quot (TwConjugate θD) → G → ℂ` to `fun c x => ∑' d : {d : D // cl d = c}, h x d`. Establish `hmeas : ∀ d, Measurable fun x => h x d` using `fun d => (measurable_one.indicator hS).mul (hφm d)`. Establish `hint : ∀ c, IntegrableOn (gc c) F μ` using `fun c => by`. Use `⟨AEStronglyMeasurable.tsum fun d => (hmeas d).aestronglyMeasurable, ?_⟩` and prove the remaining obligations. Use `lt_of_le_of_lt (lintegral_mono fun x => ?_) hA` and prove the remaining obligations.

Conclude with `enorm_tsum_le_tsum_enorm.trans (ENNReal.tsum_comp_le_tsum_of_injective Subtype.val_injective fun d => ‖h x d‖ₑ)`. Establish `hclass : ∀ c, Tm (Quot.out c) = ∫ x in F, gc c x ∂μ` using `fun c => by`. Take `⟨e, he⟩` from `exists_class_equiv ι hι θD (Quot.out c)`. Set `e'` to `e.trans (Equiv.subtypeEquivRight (p := TwConjugate θD (Quot.out c)) (q := fun d => cl d = c) fun d => by`. Rewrite using `[← cl_eq_iff θD]`.

Express the relevant statement in the definitionally equal form `cl (Quot.out c) = cl d ↔ _`. Establish `: cl (Quot.out c) = c` using `Quot.out_eq c`. Rewrite using `[this, eq_comm])`. Establish `hq : ∀ x q, h (((q.out : ι.range) : G)⁻¹ * x) (Quot.out c) = h x (e' q : D)` using `fun x q => by`. Take `⟨ρ, hρ, hρe⟩` from `he q`.

Rewrite using `[← hρ, hshift, ← hρe]`. Both sides reduce to the same expression. Establish `h1 : ∀ x, ∑' q : ι.range ⧸ ((twCent θD (Quot.out c)).map ι).subgroupOf ι.range, ‖h (((q.out : ι.range) : G)⁻¹ * x) (Quot.out c)‖ₑ = ∑' d : {d : D // cl d = c}, ‖h x d‖ₑ` using `fun x => by`. Repeatedly rewrite using `[hq]`. Conclude with `e'.tsum_eq fun d => ‖h x d‖ₑ`.

Establish `h2 : ∀ x, ∑' q : ι.range ⧸ ((twCent θD (Quot.out c)).map ι).subgroupOf ι.range, h (((q.out : ι.range) : G)⁻¹ * x) (Quot.out c) = gc c x` using `fun x => by`. Repeatedly rewrite using `[hq]`. Conclude with `e'.tsum_eq fun d => h x d`. Establish `h3` using `habs (Quot.out c) (by`. Repeatedly rewrite using `[h1]`.

Use `(lt_of_le_of_lt (lintegral_mono fun x => ?_) hA).ne` and prove the remaining obligations. Conclude with `ENNReal.tsum_comp_le_tsum_of_injective Subtype.val_injective fun d => ‖h x d‖ₑ)`. Rewrite using `[h3]`. Repeatedly rewrite using `[h2]`. Establish `hpt : ∀ x, S.indicator (1 : G → ℂ) x * ∑ᶠ d, φ (twConj θ x (ι d)) = ∑ c ∈ T, gc c x` using `fun x => by`.

Establish `e0 : S.indicator (1 : G → ℂ) x * ∑ᶠ d, φ (twConj θ x (ι d)) = ∑ᶠ d, h x d`. Distinguish the cases in `hx : x ∈ S`. Simplify using `[hdef, hh, Set.indicator_of_mem hx]`. Simplify using `[hdef, hh, Set.indicator_of_notMem hx]`. Establish `hs : Summable (h x)` using `summable_of_finite_support (hsupp x)`.

Establish `hs' : Summable fun p => h x (Equiv.sigmaFiberEquiv cl p)` using `(Equiv.sigmaFiberEquiv cl).summable_iff.2 hs`. Establish `e1 : ∑' d, h x d = ∑' p, h x (Equiv.sigmaFiberEquiv cl p)` using `((Equiv.sigmaFiberEquiv cl).tsum_eq (h x)).symm`. Establish `e00 : ∑' d, h x d = ∑ᶠ d, h x d` using `tsum_eq_finsum (hsupp x)`. Rewrite using `[e0, ← e00, e1, Summable.tsum_sigma' (f := fun p => h x (Equiv.sigmaFiberEquiv cl p)) (fun c => hs'.sigma_factor c) hs']`. Establish `e2 : ∑' c, gc c x = ∑ c ∈ T, gc c x` using `tsum_eq_sum fun c hc => (tsum_congr fun d : {d : D // cl d = c} => hzero c hc d.1 d.2 x).trans tsum_zero`.

Conclude with `e2`. Use `⟨T.finite_toSet.subset fun c hc => ?_, ?_⟩` and prove the remaining obligations. Assume the negation of the conclusion as `hcT`. Conclude with `hc (hT0 _ fun x => hzero c hcT _ (Quot.out_eq c) x)`. Repeatedly rewrite using `[hpt]`.

Rewrite using `[integral_finset_sum T fun c _ => hint c, finsum_eq_sum_of_support_subset (s := T)]`. Conclude with `Finset.sum_congr rfl fun c _ => (hclass c).symm`. Introduce `c hc`. Assume the negation of the conclusion as `hcT`. Conclude with `hc (hT0 _ fun x => hzero c hcT _ (Quot.out_eq c) x)`.
-/
theorem abstract_unfold
    (ι : D →* G) (hι : Function.Injective ι) (θD : Monoid.End D) (θ : Monoid.End G)
    (hθ : ∀ d, θ (ι d) = ι (θD d)) (μ : Measure G) [μ.IsMulLeftInvariant]
    {F : Set G} (hF : IsFundamentalDomain ι.range F μ)
    {S C : Set G} (hS : MeasurableSet S) (hSinv : ∀ g x, ι g * x ∈ S ↔ x ∈ S)
    (hC : μ C ≠ ∞) (hSC : S ⊆ (ι.range : Set G) * C)
    (φ : G → ℂ) (M : ℝ) (hM : ∀ g, ‖φ g‖ ≤ M)
    (hφm : ∀ d : D, Measurable fun x => φ (twConj θ x (ι d)))
    (hfin : {d : D | ∃ x ∈ C, φ (twConj θ x (ι d)) ≠ 0}.Finite)
    (Tm : D → ℂ)
    (hT0 : ∀ δ, (∀ x, hh S θ ι φ x δ = 0) → Tm δ = 0)
    (habs : ∀ δ : D,
      ∫⁻ x in F, ∑' q : ι.range ⧸ ((twCent θD δ).map ι).subgroupOf ι.range,
        ‖hh S θ ι φ (((q.out : ι.range) : G)⁻¹ * x) δ‖ₑ ∂μ ≠ ∞ →
      Tm δ = ∫ x in F, ∑' q : ι.range ⧸ ((twCent θD δ).map ι).subgroupOf ι.range,
        hh S θ ι φ (((q.out : ι.range) : G)⁻¹ * x) δ ∂μ) :
    (Function.support fun c : Quot (TwConjugate θD) => Tm (Quot.out c)).Finite ∧
      ∫ x in F, S.indicator (1 : G → ℂ) x * ∑ᶠ d, φ (twConj θ x (ι d)) ∂μ =
        ∑ᶠ c : Quot (TwConjugate θD), Tm (Quot.out c) := by
  classical
  set h := hh S θ ι φ with hdef
  set P : Finset D := hfin.toFinset with hP
  let cl : D → Quot (TwConjugate θD) := Quot.mk _
  let T : Finset (Quot (TwConjugate θD)) := P.image cl
  have hmemP : ∀ c ∈ C, ∀ d, h c d ≠ 0 → d ∈ P := fun c hc d hd => by
    refine hfin.mem_toFinset.2 ⟨c, hc, fun h0 => hd ?_⟩
    simp [hdef, hh, h0]
  have hshift : ∀ g x d, h (ι g * x) d = h x (twConj θD g d) := fun g x d =>
    hh_shift hθ hSinv φ g x d

  have hsupp : ∀ x, (Function.support (h x)).Finite := fun x => by
    by_cases hx : x ∈ S
    · obtain ⟨g, c, hc, rfl⟩ := exists_of_mem hSC hx
      refine (P.finite_toSet.preimage (twEquiv θD g).injective.injOn).subset fun d hd => ?_
      refine hmemP c hc _ ?_
      change h c (twConj θD g d) ≠ 0
      rw [← hshift]
      exact hd
    · have : Function.support (h x) = ∅ := by
        ext d; simp [hdef, hh_of_notMem hx]
      rw [this]; exact Set.finite_empty

  set B : ℝ≥0∞ := P.card * ENNReal.ofReal M with hB
  have hbd : ∀ x, ∑' d, ‖h x d‖ₑ ≤ S.indicator (fun _ => B) x := fun x => by
    by_cases hx : x ∈ S
    · rw [Set.indicator_of_mem hx]
      obtain ⟨g, c, hc, rfl⟩ := exists_of_mem hSC hx
      have e1 : ∑' d, ‖h (ι g * c) d‖ₑ = ∑' d, ‖h c d‖ₑ := by
        simp_rw [hshift]
        exact (twEquiv θD g).tsum_eq fun d => ‖h c d‖ₑ
      rw [e1, tsum_eq_sum (s := P) fun d hd => by
        rw [enorm_eq_zero]; by_contra h0; exact hd (hmemP c hc d h0)]
      refine (Finset.sum_le_card_nsmul _ _ _ fun d _ => enorm_hh_le hM c d).trans ?_
      simp [hB]
    · simp [hdef, hh_of_notMem hx, Set.indicator_of_notMem hx]
  have hBfin : B ≠ ∞ := ENNReal.mul_ne_top (ENNReal.natCast_ne_top _) ENNReal.ofReal_ne_top
  have hA : ∫⁻ x in F, ∑' d, ‖h x d‖ₑ ∂μ < ∞ := by
    refine lt_of_le_of_lt (lintegral_mono hbd) ?_
    rw [lintegral_indicator hS, setLIntegral_const, Measure.restrict_apply hS]
    exact ENNReal.mul_lt_top hBfin.lt_top ((measure_inter_le hF hSC).trans_lt hC.lt_top)

  have hzero : ∀ c ∉ T, ∀ d, cl d = c → ∀ x, h x d = 0 := fun c hc d hd x => by
    by_cases hx : x ∈ S
    · obtain ⟨g, c', hc', rfl⟩ := exists_of_mem hSC hx
      by_contra h0
      rw [hshift] at h0
      refine hc (Finset.mem_image.2 ⟨_, hmemP c' hc' _ h0, ?_⟩)
      rw [← hd]
      exact ((cl_eq_iff θD d _).2 ⟨g, rfl⟩).symm
    · exact hh_of_notMem hx d
  let gc : Quot (TwConjugate θD) → G → ℂ := fun c x => ∑' d : {d : D // cl d = c}, h x d
  have hmeas : ∀ d, Measurable fun x => h x d := fun d =>
    (measurable_one.indicator hS).mul (hφm d)
  have hint : ∀ c, IntegrableOn (gc c) F μ := fun c => by
    refine ⟨AEStronglyMeasurable.tsum fun d => (hmeas d).aestronglyMeasurable, ?_⟩
    refine lt_of_le_of_lt (lintegral_mono fun x => ?_) hA
    exact enorm_tsum_le_tsum_enorm.trans
      (ENNReal.tsum_comp_le_tsum_of_injective Subtype.val_injective fun d => ‖h x d‖ₑ)
  have hclass : ∀ c, Tm (Quot.out c) = ∫ x in F, gc c x ∂μ := fun c => by
    obtain ⟨e, he⟩ := exists_class_equiv ι hι θD (Quot.out c)
    let e' := e.trans (Equiv.subtypeEquivRight (p := TwConjugate θD (Quot.out c))
      (q := fun d => cl d = c) fun d => by
        rw [← cl_eq_iff θD]
        change cl (Quot.out c) = cl d ↔ _
        have : cl (Quot.out c) = c := Quot.out_eq c
        rw [this, eq_comm])
    have hq : ∀ x q, h (((q.out : ι.range) : G)⁻¹ * x) (Quot.out c) = h x (e' q : D) := fun x q => by
      obtain ⟨ρ, hρ, hρe⟩ := he q
      rw [← hρ, hshift, ← hρe]
      rfl
    have h1 : ∀ x, ∑' q : ι.range ⧸ ((twCent θD (Quot.out c)).map ι).subgroupOf ι.range,
        ‖h (((q.out : ι.range) : G)⁻¹ * x) (Quot.out c)‖ₑ = ∑' d : {d : D // cl d = c}, ‖h x d‖ₑ :=
      fun x => by
        simp_rw [hq]
        exact e'.tsum_eq fun d => ‖h x d‖ₑ
    have h2 : ∀ x, ∑' q : ι.range ⧸ ((twCent θD (Quot.out c)).map ι).subgroupOf ι.range,
        h (((q.out : ι.range) : G)⁻¹ * x) (Quot.out c) = gc c x := fun x => by
      simp_rw [hq]
      exact e'.tsum_eq fun d => h x d
    have h3 := habs (Quot.out c) (by
      simp_rw [h1]
      refine (lt_of_le_of_lt (lintegral_mono fun x => ?_) hA).ne
      exact ENNReal.tsum_comp_le_tsum_of_injective Subtype.val_injective fun d => ‖h x d‖ₑ)
    rw [h3]
    simp_rw [h2]
  have hpt : ∀ x, S.indicator (1 : G → ℂ) x * ∑ᶠ d, φ (twConj θ x (ι d)) = ∑ c ∈ T, gc c x := fun x => by
    have e0 : S.indicator (1 : G → ℂ) x * ∑ᶠ d, φ (twConj θ x (ι d)) = ∑ᶠ d, h x d := by
      by_cases hx : x ∈ S
      · simp [hdef, hh, Set.indicator_of_mem hx]
      · simp [hdef, hh, Set.indicator_of_notMem hx]
    have hs : Summable (h x) := summable_of_finite_support (hsupp x)
    have hs' : Summable fun p => h x (Equiv.sigmaFiberEquiv cl p) :=
      (Equiv.sigmaFiberEquiv cl).summable_iff.2 hs
    have e1 : ∑' d, h x d = ∑' p, h x (Equiv.sigmaFiberEquiv cl p) :=
      ((Equiv.sigmaFiberEquiv cl).tsum_eq (h x)).symm
    have e00 : ∑' d, h x d = ∑ᶠ d, h x d := tsum_eq_finsum (hsupp x)
    rw [e0, ← e00, e1,
      Summable.tsum_sigma' (f := fun p => h x (Equiv.sigmaFiberEquiv cl p))
        (fun c => hs'.sigma_factor c) hs']
    have e2 : ∑' c, gc c x = ∑ c ∈ T, gc c x := tsum_eq_sum fun c hc =>
      (tsum_congr fun d : {d : D // cl d = c} => hzero c hc d.1 d.2 x).trans tsum_zero
    exact e2
  refine ⟨T.finite_toSet.subset fun c hc => ?_, ?_⟩
  · by_contra hcT
    exact hc (hT0 _ fun x => hzero c hcT _ (Quot.out_eq c) x)
  · simp_rw [hpt]
    rw [integral_finset_sum T fun c _ => hint c, finsum_eq_sum_of_support_subset (s := T)]
    · exact Finset.sum_congr rfl fun c _ => (hclass c).symm
    · intro c hc
      by_contra hcT
      exact hc (hT0 _ fun x => hzero c hcT _ (Quot.out_eq c) x)

end Main

section Top

variable {E : Type} [Field E] [NumberField E] {n : ℕ}

/- English proof (translation)
Use `haveI := GlobalTheory.AdelicFourierUniq.secondCountable_inf E`. Use `haveI := GlobalTheory.AdelicUnitaryTop.secondCountable_finiteAdele E`. Use `haveI : SecondCountableTopology (Ad E) := inferInstanceAs (SecondCountableTopology (InfiniteAdeleRing E × FiniteAdeleRing (𝓞 E) E))`. Use `haveI : SecondCountableTopology (Matrix (Fin n) (Fin n) (Ad E)) := inferInstanceAs (SecondCountableTopology (Fin n → Fin n → Ad E))`. Use `haveI : SecondCountableTopology (Matrix (Fin n) (Fin n) (Ad E))ᵐᵒᵖ := MulOpposite.opHomeomorph.symm.isEmbedding.secondCountableTopology`.

Conclude with `Units.isEmbedding_embedProduct.secondCountableTopology`.
-/
theorem secondCountable_GA : SecondCountableTopology (GA E n) := by
  haveI := GlobalTheory.AdelicFourierUniq.secondCountable_inf E
  haveI := GlobalTheory.AdelicUnitaryTop.secondCountable_finiteAdele E
  haveI : SecondCountableTopology (Ad E) :=
    inferInstanceAs (SecondCountableTopology (InfiniteAdeleRing E × FiniteAdeleRing (𝓞 E) E))
  haveI : SecondCountableTopology (Matrix (Fin n) (Fin n) (Ad E)) :=
    inferInstanceAs (SecondCountableTopology (Fin n → Fin n → Ad E))
  haveI : SecondCountableTopology (Matrix (Fin n) (Fin n) (Ad E))ᵐᵒᵖ :=
    MulOpposite.opHomeomorph.symm.isEmbedding.secondCountableTopology
  exact Units.isEmbedding_embedProduct.secondCountableTopology

/- English proof (translation)
The claim follows from `GroundTheory.Automorphic.AdelicGLn.locallyCompactSpace E n`.
-/
theorem locallyCompact_GA : LocallyCompactSpace (GA E n) :=
  GroundTheory.Automorphic.AdelicGLn.locallyCompactSpace E n

/- English proof (translation)
Use `haveI := GlobalTheory.AdelicFourierUniq.t2Space_infiniteAdeleRing_of_numberField E`. Use `haveI := GlobalTheory.AdelicUnitaryTop.t2Space_finiteAdeleRing_of_numberField E`. Use `haveI : T2Space (Ad E) := inferInstanceAs (T2Space (InfiniteAdeleRing E × FiniteAdeleRing (𝓞 E) E))`. Use `haveI : T2Space (Matrix (Fin n) (Fin n) (Ad E)) := inferInstanceAs (T2Space (Fin n → Fin n → Ad E))`. Use `haveI : T2Space (Matrix (Fin n) (Fin n) (Ad E))ᵐᵒᵖ := MulOpposite.opHomeomorph.symm.isEmbedding.t2Space`.

Conclude with `Units.isEmbedding_embedProduct.t2Space`.
-/
theorem t2Space_adelicGL_cmField : T2Space (GA E n) := by
  haveI := GlobalTheory.AdelicFourierUniq.t2Space_infiniteAdeleRing_of_numberField E
  haveI := GlobalTheory.AdelicUnitaryTop.t2Space_finiteAdeleRing_of_numberField E
  haveI : T2Space (Ad E) :=
    inferInstanceAs (T2Space (InfiniteAdeleRing E × FiniteAdeleRing (𝓞 E) E))
  haveI : T2Space (Matrix (Fin n) (Fin n) (Ad E)) :=
    inferInstanceAs (T2Space (Fin n → Fin n → Ad E))
  haveI : T2Space (Matrix (Fin n) (Fin n) (Ad E))ᵐᵒᵖ :=
    MulOpposite.opHomeomorph.symm.isEmbedding.t2Space
  exact Units.isEmbedding_embedProduct.t2Space

/- English proof (translation)
Use `haveI : Countable E := (Module.finBasis ℚ E).equivFun.injective.countable`. Use `haveI : Countable (Matrix (Fin n) (Fin n) E) := inferInstanceAs (Countable (Fin n → Fin n → E))`. Conclude with `Units.val_injective.countable`.
-/
theorem countable_GL : Countable (GL (Fin n) E) := by
  haveI : Countable E := (Module.finBasis ℚ E).equivFun.injective.countable
  haveI : Countable (Matrix (Fin n) (Fin n) E) := inferInstanceAs (Countable (Fin n → Fin n → E))
  exact Units.val_injective.countable

end Top

/- English proof (translation)
Introduce `E _ _ _ n _ _ μ _ F τ φ hF hφ`. Use `haveI := secondCountable_GA (E := E) (n := n)`. Use `haveI := locallyCompact_GA (E := E) (n := n)`. Use `haveI := t2Space_adelicGL_cmField (E := E) (n := n)`. Use `haveI := countable_GL (E := E) (n := n)`.

Use `haveI : Countable (ratGL E n).range := (Set.countable_range (ratGL E n)).to_subtype`. Take `⟨hcl, hinv, C, hCc, hSC⟩` from `hM E n τ`. Take `⟨M, hMb⟩` from `hφ.supp.exists_bound_of_continuous hφ.cont`. Establish `hθ : ∀ d, thetaA E n (ratGL E n d) = ratGL E n (thetaE E n d)` using `fun d => (GlobalTheory.CompanionTheory.OnlyStab.ratGL_thetaE d).symm`. Establish `hcont : ∀ d, Continuous fun x => φ (twConj (thetaA E n) x (ratGL E n d))` using `fun d => hφ.cont.comp ((continuous_inv.mul continuous_const).mul GlobalTheory.CompanionTheory.KerTwFin.continuous_thetaA)`.

Establish `hHm : ∀ δ, Measurable fun x => hh (cutSet E n τ) (thetaA E n) (ratGL E n) φ x δ` using `fun δ => (measurable_one.indicator hcl.measurableSet).mul (hcont δ).measurable`. Establish `hinvH : ∀ δ, ∀ h ∈ ratCent δ, ∀ x, hh (cutSet E n τ) (thetaA E n) (ratGL E n) φ (h * x) δ = hh (cutSet E n τ) (thetaA E n) (ratGL E n) φ x δ`. Introduce and unpack `δ _ ⟨t, ht, rfl⟩ x`. Rewrite using `[hh_shift hθ hinv φ t x δ]`. Establish `: twConj (thetaE E n) t δ = δ` using `ht`.

Rewrite using `[this]`. Use `abstract_unfold (ratGL E n) GlobalTheory.CompanionTheory.KerTwFin.injective_ratGL (thetaE E n) (thetaA E n) hθ μ hF hcl.measurableSet hinv hCc.measure_lt_top.ne hSC φ M hMb (fun d => (hcont d).measurable) (GlobalTheory.CompanionTheory.KerTwFin.finite_twConj_of_isTest hφ hCc) (fun …` and prove the remaining obligations. Introduce `δ h0`. Establish `: (fun x => chiT τ x * φ (twConj (thetaA E n) x (ratGL E n δ))) = fun _ => 0` using `funext h0`. Simplify using `only [cutTerm, this]`.

Simplify using `[quotIntegral]`. Introduce `δ hfin haveI : DiscreteTopology (ratCent δ) := DiscreteTopology.of_subset (s := ((ratGL E n).range : Set (GA E n))) GlobalTheory.CompanionTheory.KerTwFin.discreteTopology_range (fun _ ⟨t, _, e⟩ => ⟨t, e⟩)`. Conclude with `GlobalTheory.CompanionTheory.QuotUnfold.quotIntegral_unfold (Γ := (ratGL E n).range) (Γ₀ := ratCent δ) (fun _ ⟨t, _, e⟩ => ⟨t, e⟩) hF (hHm δ) (hinvH δ) hfin`.
-/
theorem unfold_of_mahler (hM : Mahler) : Unfold := by
  intro E _ _ _ n _ _ μ _ F τ φ hF hφ
  haveI := secondCountable_GA (E := E) (n := n)
  haveI := locallyCompact_GA (E := E) (n := n)
  haveI := t2Space_adelicGL_cmField (E := E) (n := n)
  haveI := countable_GL (E := E) (n := n)
  haveI : Countable (ratGL E n).range := (Set.countable_range (ratGL E n)).to_subtype
  obtain ⟨hcl, hinv, C, hCc, hSC⟩ := hM E n τ
  obtain ⟨M, hMb⟩ := hφ.supp.exists_bound_of_continuous hφ.cont
  have hθ : ∀ d, thetaA E n (ratGL E n d) = ratGL E n (thetaE E n d) := fun d =>
    (GlobalTheory.CompanionTheory.OnlyStab.ratGL_thetaE d).symm
  have hcont : ∀ d, Continuous fun x => φ (twConj (thetaA E n) x (ratGL E n d)) := fun d =>
    hφ.cont.comp ((continuous_inv.mul continuous_const).mul GlobalTheory.CompanionTheory.KerTwFin.continuous_thetaA)
  have hHm : ∀ δ, Measurable fun x => hh (cutSet E n τ) (thetaA E n) (ratGL E n) φ x δ := fun δ =>
    (measurable_one.indicator hcl.measurableSet).mul (hcont δ).measurable
  have hinvH : ∀ δ, ∀ h ∈ ratCent δ, ∀ x,
      hh (cutSet E n τ) (thetaA E n) (ratGL E n) φ (h * x) δ =
        hh (cutSet E n τ) (thetaA E n) (ratGL E n) φ x δ := by
    rintro δ _ ⟨t, ht, rfl⟩ x
    rw [hh_shift hθ hinv φ t x δ]
    have : twConj (thetaE E n) t δ = δ := ht
    rw [this]
  refine abstract_unfold (ratGL E n) GlobalTheory.CompanionTheory.KerTwFin.injective_ratGL (thetaE E n) (thetaA E n) hθ μ hF
    hcl.measurableSet hinv hCc.measure_lt_top.ne hSC φ M hMb (fun d => (hcont d).measurable)
    (GlobalTheory.CompanionTheory.KerTwFin.finite_twConj_of_isTest hφ hCc) (fun δ => cutTerm μ τ φ δ) ?_ ?_
  · intro δ h0
    have : (fun x => chiT τ x * φ (twConj (thetaA E n) x (ratGL E n δ))) = fun _ => 0 := funext h0
    simp only [cutTerm, this]
    simp [quotIntegral]
  · intro δ hfin
    haveI : DiscreteTopology (ratCent δ) :=
      DiscreteTopology.of_subset (s := ((ratGL E n).range : Set (GA E n)))
        GlobalTheory.CompanionTheory.KerTwFin.discreteTopology_range (fun _ ⟨t, _, e⟩ => ⟨t, e⟩)
    exact GlobalTheory.CompanionTheory.QuotUnfold.quotIntegral_unfold (Γ := (ratGL E n).range) (Γ₀ := ratCent δ)
      (fun _ ⟨t, _, e⟩ => ⟨t, e⟩) hF (hHm δ) (hinvH δ) hfin

/- English proof (translation)
Introduce `_ hM _` and use `unfold_of_mahler hM`.
-/
theorem unfold_of_absUnfold_mahler_kerFin : PositivityTheory.Rg.BcB.D4.AbsUnfold → Mahler → PositivityTheory.Rg.BcB.D4.KerFin → Unfold :=
  fun _ hM _ => unfold_of_mahler hM

end GlobalTheory.CompanionTheory.UnfoldCut

end

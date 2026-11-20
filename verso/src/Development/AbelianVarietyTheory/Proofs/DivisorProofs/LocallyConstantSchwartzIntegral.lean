import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Definitions.Divisors.IsCompactIsOpenUnitsAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConeFinIntEq
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

namespace GlobalTheory.ConeBump

/- English proof (translation)
Rewrite using `[IsLocallyConstant.iff_eventually_eq]`. Introduce `p₀`. Establish `hh : IsLocallyConstant (fun x : P × Q => (Function.uncurry f x, f p₀ x.2))` using `hlc.prodMk (hlc.comp_continuous (continuous_const.prodMk continuous_snd))`. Establish `hn : IsOpen {x : P × Q | f x.1 x.2 = f p₀ x.2}` using `hh {z : Z × Z | z.1 = z.2}`. Take `⟨u, v, hu, hv, hpu, hCv, huv⟩` from `generalized_tube_lemma isCompact_singleton hC hn (by`.

Introduce and unpack `⟨p, q⟩ ⟨hp, -⟩`. Rewrite `hp` using `[Set.mem_singleton_iff]`. Substitute `hp` using the available equality. Use the proof step `rfl)`. Use `filter_upwards [hu.mem_nhds (hpu rfl)] with p hp`.

Use function extensionality and compare the values at `q`. Distinguish the cases in `hq : q ∈ C`. Conclude with `huv (Set.mk_mem_prod hp (hCv hq))`. Rewrite using `[hsupp p q hq, hsupp p₀ q hq]`.
-/
theorem isLocallyConstant_curry_of_compact_supp {P Q Z : Type} [TopologicalSpace P]
    [TopologicalSpace Q] [Zero Z] (f : P → Q → Z) (C : Set Q) (hC : IsCompact C)
    (hlc : IsLocallyConstant (Function.uncurry f)) (hsupp : ∀ p q, q ∉ C → f p q = 0) :
    IsLocallyConstant f := by
  rw [IsLocallyConstant.iff_eventually_eq]
  intro p₀
  have hh : IsLocallyConstant (fun x : P × Q => (Function.uncurry f x, f p₀ x.2)) :=
    hlc.prodMk (hlc.comp_continuous (continuous_const.prodMk continuous_snd))
  have hn : IsOpen {x : P × Q | f x.1 x.2 = f p₀ x.2} :=
    hh {z : Z × Z | z.1 = z.2}
  obtain ⟨u, v, hu, hv, hpu, hCv, huv⟩ :=
    generalized_tube_lemma isCompact_singleton hC hn (by
      rintro ⟨p, q⟩ ⟨hp, -⟩
      rw [Set.mem_singleton_iff] at hp
      subst hp
      rfl)
  filter_upwards [hu.mem_nhds (hpu rfl)] with p hp
  funext q
  by_cases hq : q ∈ C
  · exact huv (Set.mk_mem_prod hp (hCv hq))
  · rw [hsupp p q hq, hsupp p₀ q hq]

/- English proof (translation)
Introduce `P Q Y _ _ _ _ _ _ _ _ _ μP _ μQ _ f g C hC hlc hSB hsupp hg L hadd hsmul`. Establish `hfin : (Set.range (Function.uncurry f) \ {0}).Finite`. Establish `hK : IsCompact (Set.univ ×ˢ C : Set (P × Q))` using `isCompact_univ.prod hC`. Use `haveI := isCompact_iff_compactSpace.mp hK`. Establish `h1` using `(hlc.comp_continuous (continuous_subtype_val : Continuous (Subtype.val : (Set.univ ×ˢ C : Set (P × Q)) → P × Q))).range_finite`.

Use `h1.subset ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨⟨⟨p, q⟩, rfl⟩, hne⟩`. Establish `hq : q ∈ C`. Assume the negation of the conclusion as `hq`. Conclude with `hne (hsupp p q hq)`.

Conclude with `⟨⟨(p, q), ⟨Set.mem_univ _, hq⟩⟩, rfl⟩`. Use `set S := hfin.toFinset with hSdef`. Establish `hmemS : ∀ p q, f p q ≠ 0 → f p q ∈ S`. Introduce `p q h`. Rewrite using `[Set.Finite.mem_toFinset]`.

Conclude with `⟨⟨(p, q), rfl⟩, h⟩`. Establish `hS0 : ∀ s ∈ S, s ≠ 0` using `fun s hs => ((Set.Finite.mem_toFinset _).1 hs).2`. Establish `hSSB : ∀ s ∈ S, s ∈ SB Y`. Introduce `s hs`. Take `⟨⟨⟨p, q⟩, rfl⟩, -⟩` from `(Set.Finite.mem_toFinset _).1 hs`.

Conclude with `hSB p q`. Set `χ : (Y → ℂ) → P → Q → ℂ` to `fun s p q => if f p q = s then 1 else 0`. Establish `hdec : ∀ φ : (Y → ℂ) → ℂ, φ 0 = 0 → ∀ p q, φ (f p q) = ∑ s ∈ S, χ s p q * φ s`. Introduce `φ h0 p q`. Simplify using `only [χ, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq]`.

Distinguish the cases in `h : f p q = 0`. Rewrite using `[h, h0]`. Simplify using the standard rewrite rules. Rewrite using `[if_pos (hmemS p q h)]`. Establish `hlcP` using `isLocallyConstant_curry_of_compact_supp f C hC hlc hsupp`.

Establish `hχlc : ∀ s, IsLocallyConstant (Function.uncurry (χ s))` using `fun s => hlc.comp (fun v => if v = s then (1 : ℂ) else 0)`. Establish `hsuppχ : ∀ s ∈ S, ∀ p q, q ∉ C → χ s p q = 0`. Introduce `s hs p q hq`. Simplify using `[χ, hsupp p q hq, (hS0 s hs).symm]`. Establish `hint_in : ∀ s ∈ S, ∀ p, Integrable (fun q => χ s p q * g q) μQ`.

Introduce `s hs p`. Apply `Continuous.integrable_of_hasCompactSupport` to reduce the goal to its premises. Conclude with `((hχlc s).comp_continuous (continuous_const.prodMk continuous_id)).continuous.mul hg`. Conclude with `HasCompactSupport.intro hC (fun q hq => by simp [hsuppχ s hs p q hq])`. Set `G : (Y → ℂ) → P → ℂ` to `fun s p => ∫ q, χ s p q * g q ∂μQ`.

Establish `hGlc : ∀ s, IsLocallyConstant (G s)` using `fun s => hlcP.comp (fun h : Q → Y → ℂ => ∫ q, (if h q = s then (1 : ℂ) else 0) * g q ∂μQ)`. Establish `hint_out : ∀ s, Integrable (G s) μP` using `fun s => (hGlc s).continuous.integrable_of_hasCompactSupport (isCompact_univ.of_isClosed_subset (isClosed_tsupport _) (Set.subset_univ _))`. Set `a : (Y → ℂ) → ℂ` to `fun s => ∫ p, G s p ∂μP`. Establish `hkey : ∀ φ : (Y → ℂ) → ℂ, φ 0 = 0 → ∫ p, ∫ q, φ (f p q) * g q ∂μQ ∂μP = ∑ s ∈ S, a s * φ s`. Introduce `φ h0`.

Establish `e1 : ∀ p, ∫ q, φ (f p q) * g q ∂μQ = ∑ s ∈ S, G s p * φ s`. Introduce `p`. Establish `: (fun q => φ (f p q) * g q) = fun q => ∑ s ∈ S, χ s p q * g q * φ s`. Use function extensionality and compare the values at `q`. Rewrite using `[hdec φ h0 p q, Finset.sum_mul]`.

Conclude with `Finset.sum_congr rfl fun s _ => by ring`. Rewrite using `[this, integral_finset_sum _ (fun s hs => (hint_in s hs p).mul_const _)]`. Conclude with `Finset.sum_congr rfl fun s _ => integral_mul_const _ _`. Rewrite using `[integral_congr_ae (ae_of_all _ e1), integral_finset_sum _ (fun s _ => (hint_out s).mul_const _)]`. Conclude with `Finset.sum_congr rfl fun s _ => integral_mul_const _ _`.

Establish `hL0 : L 0 = 0`. Use `hsmul 0 0 (Submodule.zero_mem _)` as an intermediate fact. Simplify using `using this`. Establish `hfun : (fun y => ∫ p, ∫ q, f p q y * g q ∂μQ ∂μP) = ∑ s ∈ S, a s • s`. Use function extensionality and compare the values at `y`.

Use `hkey (fun h => h y) rfl` as an intermediate fact. Rewrite using `[this, Finset.sum_apply]`. Both sides reduce to the same expression. Establish `hLsum : ∀ T ⊆ S, L (∑ s ∈ T, a s • s) = ∑ s ∈ T, a s * L s`. Introduce `T`.

Proceed by induction on `T using Finset.induction_on with`. Consider the case `empty => intro _`. Simplify using `using hL0`. Consider the case `insert x T hx ih`. Introduce `hT`.

Establish `hxS : x ∈ S` using `hT (Finset.mem_insert_self _ _)`. Establish `hTS : T ⊆ S` using `fun t ht => hT (Finset.mem_insert_of_mem ht)`. Rewrite using `[Finset.sum_insert hx, Finset.sum_insert hx, hadd _ (Submodule.smul_mem _ _ (hSSB x hxS)) _ (Submodule.sum_mem _ fun t ht => Submodule.smul_mem _ _ (hSSB t (hTS ht))), hsmul _ _ (hSSB x hxS), ih hTS]`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Rewrite using `[hfun]`.

Conclude with `Submodule.sum_mem _ fun s hs => Submodule.smul_mem _ _ (hSSB s hs)`. Rewrite using `[hfun, hLsum S subset_rfl, hkey L hL0]`.
-/
theorem integ_mem_SB_and_map : ∀ {P Q Y : Type} [TopologicalSpace P] [CompactSpace P] [MeasurableSpace P] [OpensMeasurableSpace P]
    [TopologicalSpace Q] [T2Space Q] [MeasurableSpace Q] [OpensMeasurableSpace Q] [TopologicalSpace Y]
    (μP : Measure P) [IsFiniteMeasure μP] (μQ : Measure Q) [IsFiniteMeasureOnCompacts μQ] (f : P → Q → Y → ℂ)
    (g : Q → ℂ) (C : Set Q), IsCompact C → IsLocallyConstant (Function.uncurry f) → (∀ p q, f p q ∈ SB Y) →
    (∀ p q, q ∉ C → f p q = 0) → Continuous g → ∀ L : (Y → ℂ) → ℂ,
    (∀ a ∈ SB Y, ∀ a' ∈ SB Y, L (a + a') = L a + L a') → (∀ (c : ℂ), ∀ a ∈ SB Y, L (c • a) = c * L a) →
    (fun y => ∫ p, ∫ q, f p q y * g q ∂μQ ∂μP) ∈ SB Y ∧
      L (fun y => ∫ p, ∫ q, f p q y * g q ∂μQ ∂μP) = ∫ p, ∫ q, L (f p q) * g q ∂μQ ∂μP := by
  intro P Q Y _ _ _ _ _ _ _ _ _ μP _ μQ _ f g C hC hlc hSB hsupp hg L hadd hsmul
  classical
  have hfin : (Set.range (Function.uncurry f) \ {0}).Finite := by
    have hK : IsCompact (Set.univ ×ˢ C : Set (P × Q)) := isCompact_univ.prod hC
    haveI := isCompact_iff_compactSpace.mp hK
    have h1 := (hlc.comp_continuous (continuous_subtype_val :
      Continuous (Subtype.val : (Set.univ ×ˢ C : Set (P × Q)) → P × Q))).range_finite
    refine h1.subset ?_
    rintro _ ⟨⟨⟨p, q⟩, rfl⟩, hne⟩
    have hq : q ∈ C := by
      by_contra hq
      exact hne (hsupp p q hq)
    exact ⟨⟨(p, q), ⟨Set.mem_univ _, hq⟩⟩, rfl⟩
  set S := hfin.toFinset with hSdef
  have hmemS : ∀ p q, f p q ≠ 0 → f p q ∈ S := by
    intro p q h
    rw [Set.Finite.mem_toFinset]
    exact ⟨⟨(p, q), rfl⟩, h⟩
  have hS0 : ∀ s ∈ S, s ≠ 0 := fun s hs => ((Set.Finite.mem_toFinset _).1 hs).2
  have hSSB : ∀ s ∈ S, s ∈ SB Y := by
    intro s hs
    obtain ⟨⟨⟨p, q⟩, rfl⟩, -⟩ := (Set.Finite.mem_toFinset _).1 hs
    exact hSB p q
  let χ : (Y → ℂ) → P → Q → ℂ := fun s p q => if f p q = s then 1 else 0
  have hdec : ∀ φ : (Y → ℂ) → ℂ, φ 0 = 0 → ∀ p q, φ (f p q) = ∑ s ∈ S, χ s p q * φ s := by
    intro φ h0 p q
    simp only [χ, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq]
    by_cases h : f p q = 0
    · rw [h, h0]
      simp
    · rw [if_pos (hmemS p q h)]
  have hlcP := isLocallyConstant_curry_of_compact_supp f C hC hlc hsupp
  have hχlc : ∀ s, IsLocallyConstant (Function.uncurry (χ s)) := fun s =>
    hlc.comp (fun v => if v = s then (1 : ℂ) else 0)
  have hsuppχ : ∀ s ∈ S, ∀ p q, q ∉ C → χ s p q = 0 := by
    intro s hs p q hq
    simp [χ, hsupp p q hq, (hS0 s hs).symm]
  have hint_in : ∀ s ∈ S, ∀ p, Integrable (fun q => χ s p q * g q) μQ := by
    intro s hs p
    apply Continuous.integrable_of_hasCompactSupport
    · exact ((hχlc s).comp_continuous (continuous_const.prodMk continuous_id)).continuous.mul hg
    · exact HasCompactSupport.intro hC (fun q hq => by simp [hsuppχ s hs p q hq])
  let G : (Y → ℂ) → P → ℂ := fun s p => ∫ q, χ s p q * g q ∂μQ
  have hGlc : ∀ s, IsLocallyConstant (G s) := fun s =>
    hlcP.comp (fun h : Q → Y → ℂ => ∫ q, (if h q = s then (1 : ℂ) else 0) * g q ∂μQ)
  have hint_out : ∀ s, Integrable (G s) μP := fun s =>
    (hGlc s).continuous.integrable_of_hasCompactSupport
      (isCompact_univ.of_isClosed_subset (isClosed_tsupport _) (Set.subset_univ _))
  let a : (Y → ℂ) → ℂ := fun s => ∫ p, G s p ∂μP
  have hkey : ∀ φ : (Y → ℂ) → ℂ, φ 0 = 0 →
      ∫ p, ∫ q, φ (f p q) * g q ∂μQ ∂μP = ∑ s ∈ S, a s * φ s := by
    intro φ h0
    have e1 : ∀ p, ∫ q, φ (f p q) * g q ∂μQ = ∑ s ∈ S, G s p * φ s := by
      intro p
      have : (fun q => φ (f p q) * g q) = fun q => ∑ s ∈ S, χ s p q * g q * φ s := by
        funext q
        rw [hdec φ h0 p q, Finset.sum_mul]
        exact Finset.sum_congr rfl fun s _ => by ring
      rw [this, integral_finset_sum _ (fun s hs => (hint_in s hs p).mul_const _)]
      exact Finset.sum_congr rfl fun s _ => integral_mul_const _ _
    rw [integral_congr_ae (ae_of_all _ e1),
      integral_finset_sum _ (fun s _ => (hint_out s).mul_const _)]
    exact Finset.sum_congr rfl fun s _ => integral_mul_const _ _
  have hL0 : L 0 = 0 := by
    have := hsmul 0 0 (Submodule.zero_mem _)
    simpa using this
  have hfun : (fun y => ∫ p, ∫ q, f p q y * g q ∂μQ ∂μP) = ∑ s ∈ S, a s • s := by
    funext y
    have := hkey (fun h => h y) rfl
    rw [this, Finset.sum_apply]
    rfl
  have hLsum : ∀ T ⊆ S, L (∑ s ∈ T, a s • s) = ∑ s ∈ T, a s * L s := by
    intro T
    induction T using Finset.induction_on with
    | empty => intro _; simpa using hL0
    | insert x T hx ih =>
      intro hT
      have hxS : x ∈ S := hT (Finset.mem_insert_self _ _)
      have hTS : T ⊆ S := fun t ht => hT (Finset.mem_insert_of_mem ht)
      rw [Finset.sum_insert hx, Finset.sum_insert hx,
        hadd _ (Submodule.smul_mem _ _ (hSSB x hxS))
          _ (Submodule.sum_mem _ fun t ht => Submodule.smul_mem _ _ (hSSB t (hTS ht))),
        hsmul _ _ (hSSB x hxS), ih hTS]
  refine ⟨?_, ?_⟩
  · rw [hfun]
    exact Submodule.sum_mem _ fun s hs => Submodule.smul_mem _ _ (hSSB s hs)
  · rw [hfun, hLsum S subset_rfl, hkey L hL0]

end GlobalTheory.ConeBump

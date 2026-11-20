import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ChartGen
import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.MaxMass
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.SiegelMassRatioOfLI
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.AlphaDiscriminantHolds
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.JordanSplittingExists
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.DiscEquiv
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MaximalHermitianLatticeLocalStructureDiscriminan
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.NormRepCountExtP
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.ExistsLatticeOfFibLocNeZeroGood
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.IsUnimodularAtIffVd
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.ExistsLocalData
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.MemSmulOfMemSmulLocF
open NumberField GlobalTheory.Mass Formalism.HermitianLatticesTheory Formalism.HermitianLattices.Ext.L3 Formalism.L2.SG.Pf.Cnt
open scoped Classical

noncomputable section
namespace GlobalTheory.MaxLatExpo

/- English proof (translation)
Introduce `K F V _ _ _ _ _ _ _ _ _ _ _ hK hF h hs hd M hM P hPb b a hJ`. Establish `hP : P.IsMaximal` using `hPb.1`. Establish `hp : (P.comap (algebraMap (𝓞 F) (𝓞 K))).IsMaximal` using `Ideal.isMaximal_comap_of_isIntegral_of_isMaximal P`. Establish `hpp` using `hp.isPrime`. Establish `hl : ∀ L : Submodule (𝓞 K) V, locF (P.comap (algebraMap (𝓞 F) (𝓞 K))) L = loc (K` using `K) P L := fun L => locF_eq_loc hK hF hP L`.

Take `⟨-, -, -, hloc⟩` from `GlobalTheory.MaxLatStruct.main K V h hK hs (UnimodularLocalization.nondegenerate hd) M hM`. Take `⟨hconj, -, -, x, hxM, ⟨a0, ha0x, ha0P, ha0P2⟩, hstr⟩` from `hloc P hPb`. Establish `hext : extP K (P.comap (algebraMap (𝓞 F) (𝓞 K))) = P` using `ThirdPropositionSlot.map_comap_eq_of_inert hK hF hP hconj`. Take `⟨hbX, hspan, horth, hdiag, ha⟩` from `hJ`. Establish `hL : IsLatIn (⊤ : Submodule K V) M` using `⟨hM.1.1.fg, hM.1.1.span_eq_top⟩`.

Establish `hdI : dualIn h ⊤ M = dual h M`. Use extensionality with `z`. Simplify using `[dualIn]`. Use `set p := P.comap (algebraMap (𝓞 F) (𝓞 K)) with hpdef`. Use `set S := HU.SP K p with hSdef`.

Establish `hB : ∀ z, z ∈ locF p M ↔ ∀ i, h (b i) z / algebraMap (𝓞 K) K (algebraMap (𝓞 F) (𝓞 K) (a i)) ∈ S` using `fun z => by`. Conclude with `(Formalism.L2.SG.Pf.G2.mem_B_iff hbX hspan horth hdiag ha hpp hL z).trans ⟨fun h => h.2, fun h => ⟨Submodule.mem_top, h⟩⟩`. Establish `hA : ∀ z, z ∈ locF p (dual h M) ↔ ∀ i, h (b i) z ∈ S` using `fun z => by`. Rewrite using `[← hdI]`. Conclude with `(Formalism.L2.SG.Pf.G2.mem_locF_dualIn_iff hbX hspan horth hdiag ha hF hp hL z).trans ⟨fun h => h.2, fun h => ⟨Submodule.mem_top, h⟩⟩`.

Establish `hR : ∀ c, c ∈ locR (K` using `K) P → c ∈ S := fun c hc => HU.mem_SP_iff_locF.2 (by rw [locF_eq_loc hK hF hP (1 : Submodule (𝓞 K) K)]; exact hc)`. Choose the witnesses or unpack the hypotheses as in `⟨a0', ha0'⟩ : a0 ∈ Set.range (algebraMap (𝓞 F) (𝓞 K)) := by`. Use `(conjO_eq_iff_mem_range hF a0).1 (RingOfIntegers.ext ?_)` and prove the remaining obligations. Rewrite using `[conjO_coe]`. Express the relevant statement in the definitionally equal form `star ((a0 : K)) = (a0 : K)`.

Rewrite using `[ha0x]`. Conclude with `hs.eq x x`. Establish `ha0ne : a0' ≠ 0`. Introduce and unpack `rfl`. Apply `ha0P2` to reduce the goal to its premises.

Rewrite using `[← ha0', map_zero]`. Conclude with `Submodule.zero_mem _`. Establish `hv0 : vF p a0' = 1`. Establish `h1` using `localValuationFiltration.mem_pow_vF hp ha0ne`. Establish `h2` using `localValuationFiltration.notMem_pow_vF hp ha0ne`.

Establish `hin : a0' ∈ p` using `by rw [hpdef, Ideal.mem_comap, ha0']; exact ha0P`. Break down `Nat.lt_or_ge (vF p a0') 2 with hlt | hge` into its components or cases. Use `interval_cases hv : vF p a0'`. Rewrite `h2` using `[zero_add, pow_one]`. Conclude with `absurd hin h2`.

Both sides reduce to the same expression. It suffices to derive a contradiction. Apply `ha0P2` to reduce the goal to its premises. Use `localizedQuotients.ι_mem_pow (K := K) (Ideal.pow_le_pow_right hge h1)` as an intermediate fact. Rewrite `this` using `[hext, ha0']`. Then use the resulting hypothesis.

Establish `hd0 : h x x = algebraMap (𝓞 K) K (algebraMap (𝓞 F) (𝓞 K) a0')` using `by rw [ha0', ← ha0x]`. Establish `hdne : h x x ≠ 0` using `by rw [hd0]; exact Formalism.L2.SG.Pf.G2.jK_ι_ne_zero ha0ne`. Establish `hα : ∀ i, algebraMap (𝓞 K) K (algebraMap (𝓞 F) (𝓞 K) (a i)) ≠ 0` using `fun i => Formalism.L2.SG.Pf.G2.jK_ι_ne_zero (ha i)`. Establish `hy : ∀ k i, h (b k) ((algebraMap (𝓞 K) K (algebraMap (𝓞 F) (𝓞 K) (a i)))⁻¹ • b i) = if k = i then 1 else 0`. Introduce `k i`.

Rewrite using `[LinearMap.map_smul, smul_eq_mul]`. Use `split_ifs with hki`. Substitute `hki` using the available equality. Rewrite using `[hdiag]`. Conclude with `inv_mul_cancel₀ (hα k)`.

Rewrite using `[horth k i hki, mul_zero]`. Establish `hyA : ∀ i, (algebraMap (𝓞 K) K (algebraMap (𝓞 F) (𝓞 K) (a i)))⁻¹ • b i ∈ loc (K` using `K) P (dual h M) := by`. Introduce `i`. Rewrite using `[← hl, hA]`. Introduce `k`.

Rewrite using `[hy]`. Use `split_ifs`. Conclude with `S.one_mem`. Conclude with `S.zero_mem`. Use `choose c hc hcM using fun i => hstr _ (hyA i)`.

Establish `hcS : ∀ i, c i ∈ S` using `fun i => hR _ (hc i)`. Establish `hE : ∀ i k, ((if k = i then (1 : K) else 0) - c i * (h x x)⁻¹ * h (b k) x) / algebraMap (𝓞 K) K (algebraMap (𝓞 F) (𝓞 K) (a k)) ∈ S`. Introduce `i k`. Establish `h1` using `hcM i`. Rewrite `h1` using `[← hl]`.

Use `(hB _).1 h1 k` as an intermediate fact. Rewrite `this` using `[map_sub, hy, LinearMap.map_smul, smul_eq_mul]`. Then use the resulting hypothesis. Establish `hξ : ∀ k, h (b k) x / algebraMap (𝓞 K) K (algebraMap (𝓞 F) (𝓞 K) (a k)) ∈ S` using `(hB x).1 (LocF.le_locF p M hxM)`. Establish `hdS : h x x ∈ S` using `by rw [hd0]; exact HU.jK_mem_SP _`. Establish `hle1 : ∀ i, vF p (a i) ≤ 1`.

Introduce `i`. Assume the negation of the conclusion as `hgt`. Use `push_neg at hgt`. Establish `h1 : h x x / algebraMap (𝓞 K) K (algebraMap (𝓞 F) (𝓞 K) (a i)) ∈ S`. Establish `e : h x x / algebraMap (𝓞 K) K (algebraMap (𝓞 F) (𝓞 K) (a i)) = h x x * (((if i = i then (1 : K) else 0) - c i * (h x x)⁻¹ * h (b i) x) / algebraMap (𝓞 K) K (algebraMap (𝓞 F) (𝓞 K) (a i))) + c i * (h (b i) x / algebraMap (𝓞 K) K (algebraMap (𝓞 F) (𝓞 K) (a i)))`.

Rewrite using `[if_pos rfl]`. Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e]`. Conclude with `S.add_mem (S.mul_mem hdS (hE i i)) (S.mul_mem (hcS i) (hξ i))`.

Establish `h1' : algebraMap (𝓞 K) K a0 / algebraMap (𝓞 K) K (algebraMap (𝓞 F) (𝓞 K) (a i)) ∈ S`. Rewrite using `[show algebraMap (𝓞 K) K a0 = h x x from ha0x]`. Conclude with `h1`. Establish `h2` using `(Formalism.L2.SG.Pf.G2.div_mem_SP_iff hp (ha i) a0).1 h1'`. Rewrite `h2` using `[hext]`.

Conclude with `ha0P2 (Ideal.pow_le_pow_right hgt h2)`. Establish `huniq : ∀ i j, i ≠ j → vF p (a j) = 1 → 1 ≤ vF p (a i) → False`. Introduce `i j hij hj hi`. Establish `hci : c i / algebraMap (𝓞 K) K (algebraMap (𝓞 F) (𝓞 K) (a j)) ∈ S`. Establish `e : c i / algebraMap (𝓞 K) K (algebraMap (𝓞 F) (𝓞 K) (a j)) = c i * (((if j = j then (1 : K) else 0) - c j * (h x x)⁻¹ * h (b j) x) / algebraMap (𝓞 K) K (algebraMap (𝓞 F) (𝓞 K) (a j))) - c j * (((if j = i then (1 : K) else 0) - c i * (h x x)⁻¹ * h (b j) x) / algebraMap (𝓞 K) K (a …`.

Rewrite using `[if_pos rfl, if_neg (fun e => hij e.symm)]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e]`. Conclude with `S.sub_mem (S.mul_mem (hcS i) (hE j j)) (S.mul_mem (hcS j) (hE i j))`. Take `⟨t, ht, w, hw⟩` from `HU.mem_SP.1 (hcS i)`.

Establish `hw1 : algebraMap (𝓞 K) K w / algebraMap (𝓞 K) K (algebraMap (𝓞 F) (𝓞 K) (a j)) ∈ S`. Rewrite using `[hw, mul_div_assoc]`. Conclude with `S.mul_mem (HU.jK_mem_SP _) hci`. Establish `hwP : w ∈ P`. Use `(Formalism.L2.SG.Pf.G2.div_mem_SP_iff hp (ha j) w).1 hw1` as an intermediate fact.

Rewrite `this` using `[hj, pow_one, hext]`. Then use the resulting hypothesis. Establish `hw2 : algebraMap (𝓞 K) K w / algebraMap (𝓞 K) K (algebraMap (𝓞 F) (𝓞 K) a0') ∈ S` using `(Formalism.L2.SG.Pf.G2.div_mem_SP_iff hp ha0ne w).2 (by rw [hv0, pow_one, hext]; exact hwP)`. Establish `htne : algebraMap (𝓞 K) K (algebraMap (𝓞 F) (𝓞 K) t) ≠ 0` using `Formalism.L2.SG.Pf.G2.jK_ι_ne_zero (Formalism.L2.SG.Pf.G2.ne_zero_of_notMem ht)`. Establish `htinv : (algebraMap (𝓞 K) K (algebraMap (𝓞 F) (𝓞 K) t))⁻¹ ∈ S` using `HU.mem_SP.2 ⟨t, ht, 1, by rw [map_one, mul_inv_cancel₀ htne]⟩`. Establish `hcd : c i * (h x x)⁻¹ ∈ S`.

Establish `e : c i * (h x x)⁻¹ = (algebraMap (𝓞 K) K (algebraMap (𝓞 F) (𝓞 K) t))⁻¹ * (algebraMap (𝓞 K) K w / algebraMap (𝓞 K) K (algebraMap (𝓞 F) (𝓞 K) a0'))`. Rewrite using `[hw, ← hd0]`. Clear the denominators using the available nonvanishing facts. Rewrite using `[e]`. Conclude with `S.mul_mem htinv hw2`.

Establish `h1 : algebraMap (𝓞 K) K 1 / algebraMap (𝓞 K) K (algebraMap (𝓞 F) (𝓞 K) (a i)) ∈ S`. Establish `e : algebraMap (𝓞 K) K 1 / algebraMap (𝓞 K) K (algebraMap (𝓞 F) (𝓞 K) (a i)) = ((if i = i then (1 : K) else 0) - c i * (h x x)⁻¹ * h (b i) x) / algebraMap (𝓞 K) K (algebraMap (𝓞 F) (𝓞 K) (a i)) + (c i * (h x x)⁻¹) * (h (b i) x / algebraMap (𝓞 K) K (algebraMap (𝓞 F) (𝓞 K) (a i)))`. Rewrite using `[if_pos rfl, map_one]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e]`.

Conclude with `S.add_mem (hE i i) (S.mul_mem hcd (hξ i))`. Establish `h2` using `(Formalism.L2.SG.Pf.G2.div_mem_SP_iff hp (ha i) 1).1 h1`. Rewrite `h2` using `[hext]`. Conclude with `hP.ne_top ((Ideal.eq_top_iff_one P).2 (Ideal.pow_le_self (by omega) h2))`. Establish `hex : ∃ i, vF p (a i) ≠ 0`.

Assume the negation of the conclusion as `hcon`. Use `push_neg at hcon`. Apply `hPb.2` to reduce the goal to its premises. Establish `hinv : ∀ i, algebraMap (𝓞 K) K 1 / algebraMap (𝓞 K) K (algebraMap (𝓞 F) (𝓞 K) (a i)) ∈ S` using `fun i => (Formalism.L2.SG.Pf.G2.div_mem_SP_iff hp (ha i) 1).2 (by rw [hcon i, pow_zero, Ideal.one_eq_top]; exact Submodule.mem_top)`. Establish `heq : loc (K` using `K) P (dual h M) = loc (K := K) P M := by`.

Rewrite using `[← hl, ← hl]`. Use extensionality with `z`. Rewrite using `[hA, hB]`. Prove the components needed by the constructor for the conclusion. Introduce `hz i`.

Establish `e : h (b i) z / algebraMap (𝓞 K) K (algebraMap (𝓞 F) (𝓞 K) (a i)) = h (b i) z * (algebraMap (𝓞 K) K 1 / algebraMap (𝓞 K) K (algebraMap (𝓞 F) (𝓞 K) (a i)))`. Rewrite using `[map_one]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e]`. Conclude with `S.mul_mem (hz i) (hinv i)`.

Introduce `hz i`. Establish `e : h (b i) z = algebraMap (𝓞 K) K (algebraMap (𝓞 F) (𝓞 K) (a i)) * (h (b i) z / algebraMap (𝓞 K) K (algebraMap (𝓞 F) (𝓞 K) (a i)))`. Clear denominators, using `[hα i]` for the nonvanishing conditions. Rewrite using `[e]`. Conclude with `S.mul_mem (HU.jK_mem_SP _) (hz i)`.

Take `⟨σ, hσ⟩` from `GlobalTheory.MaxLatStruct.star_int (K := K)`. Establish `hinj` using `IsFractionRing.injective (𝓞 K) K`. Establish `hstar : ∀ r : 𝓞 K, star (algebraMap (𝓞 K) K r) ∈ Set.range (algebraMap (𝓞 K) K)` using `fun r => ⟨σ r, hσ r⟩`. Unfold `IsUnimodularAt`. Rewrite using `[locDual_dualAt_loc h hinj hstar, ← le_antisymm (locDual_loc_dual_le h P M) (locDual_dualAt_le h hstar P M hM.1.1.fg)]`.

Conclude with `heq`. Take `⟨i, hi⟩` from `hex`. Establish `hi1 : vF p (a i) = 1` using `le_antisymm (hle1 i) (Nat.one_le_iff_ne_zero.2 hi)`. Use `⟨i, hi1, fun j hji => ?_⟩` and prove the remaining obligations. Assume the negation of the conclusion as `hj`.

Conclude with `huniq j i hji hi1 (Nat.one_le_iff_ne_zero.2 hj)`.
-/
theorem main : ∀ (K F V : Type) [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V], IsCMUnram K → IsFixF K F → ∀ h : V →ₗ⋆[K] V →ₗ[K] K, h.IsSymm → IsTotPosDef h → ∀ M : Submodule (𝓞 K) V, IsMaxLat h M → ∀ P ∈ badP h M, ∀ (b : Fin (Module.finrank K (⊤ : Submodule K V)) → V) (a : Fin (Module.finrank K (⊤ : Submodule K V)) → 𝓞 F), IsJordanIn h ⊤ M (P.comap (algebraMap (𝓞 F) (𝓞 K))) b a → ∃ i, vF (P.comap (algebraMap (𝓞 F) (𝓞 K))) (a i) = 1 ∧ ∀ j, j ≠ i → vF (P.comap (algebraMap (𝓞 F) (𝓞 K))) (a j) = 0 := by
  intro K F V _ _ _ _ _ _ _ _ _ _ _ hK hF h hs hd M hM P hPb b a hJ
  have hP : P.IsMaximal := hPb.1
  have hp : (P.comap (algebraMap (𝓞 F) (𝓞 K))).IsMaximal :=
    Ideal.isMaximal_comap_of_isIntegral_of_isMaximal P
  have hpp := hp.isPrime
  have hl : ∀ L : Submodule (𝓞 K) V, locF (P.comap (algebraMap (𝓞 F) (𝓞 K))) L = loc (K := K) P L :=
    fun L => locF_eq_loc hK hF hP L
  obtain ⟨-, -, -, hloc⟩ := GlobalTheory.MaxLatStruct.main K V h hK hs (UnimodularLocalization.nondegenerate hd) M hM
  obtain ⟨hconj, -, -, x, hxM, ⟨a0, ha0x, ha0P, ha0P2⟩, hstr⟩ := hloc P hPb
  have hext : extP K (P.comap (algebraMap (𝓞 F) (𝓞 K))) = P := ThirdPropositionSlot.map_comap_eq_of_inert hK hF hP hconj
  obtain ⟨hbX, hspan, horth, hdiag, ha⟩ := hJ
  have hL : IsLatIn (⊤ : Submodule K V) M := ⟨hM.1.1.fg, hM.1.1.span_eq_top⟩
  have hdI : dualIn h ⊤ M = dual h M := by
    ext z; simp [dualIn]
  set p := P.comap (algebraMap (𝓞 F) (𝓞 K)) with hpdef
  set S := HU.SP K p with hSdef
  have hB : ∀ z, z ∈ locF p M ↔ ∀ i, h (b i) z / algebraMap (𝓞 K) K (algebraMap (𝓞 F) (𝓞 K) (a i)) ∈ S := fun z => by
    exact (Formalism.L2.SG.Pf.G2.mem_B_iff hbX hspan horth hdiag ha hpp hL z).trans ⟨fun h => h.2, fun h => ⟨Submodule.mem_top, h⟩⟩
  have hA : ∀ z, z ∈ locF p (dual h M) ↔ ∀ i, h (b i) z ∈ S := fun z => by
    rw [← hdI]; exact (Formalism.L2.SG.Pf.G2.mem_locF_dualIn_iff hbX hspan horth hdiag ha hF hp hL z).trans ⟨fun h => h.2, fun h => ⟨Submodule.mem_top, h⟩⟩
  have hR : ∀ c, c ∈ locR (K := K) P → c ∈ S := fun c hc => HU.mem_SP_iff_locF.2 (by rw [locF_eq_loc hK hF hP (1 : Submodule (𝓞 K) K)]; exact hc)

  obtain ⟨a0', ha0'⟩ : a0 ∈ Set.range (algebraMap (𝓞 F) (𝓞 K)) := by
    refine (conjO_eq_iff_mem_range hF a0).1 (RingOfIntegers.ext ?_)
    rw [conjO_coe]
    change star ((a0 : K)) = (a0 : K)
    rw [ha0x]; exact hs.eq x x
  have ha0ne : a0' ≠ 0 := by
    rintro rfl
    apply ha0P2
    rw [← ha0', map_zero]; exact Submodule.zero_mem _
  have hv0 : vF p a0' = 1 := by
    have h1 := localValuationFiltration.mem_pow_vF hp ha0ne
    have h2 := localValuationFiltration.notMem_pow_vF hp ha0ne
    have hin : a0' ∈ p := by rw [hpdef, Ideal.mem_comap, ha0']; exact ha0P
    rcases Nat.lt_or_ge (vF p a0') 2 with hlt | hge
    · interval_cases hv : vF p a0'
      · rw [zero_add, pow_one] at h2; exact absurd hin h2
      · rfl
    · exfalso
      apply ha0P2
      have := localizedQuotients.ι_mem_pow (K := K) (Ideal.pow_le_pow_right hge h1)
      rwa [hext, ha0'] at this
  have hd0 : h x x = algebraMap (𝓞 K) K (algebraMap (𝓞 F) (𝓞 K) a0') := by rw [ha0', ← ha0x]
  have hdne : h x x ≠ 0 := by rw [hd0]; exact Formalism.L2.SG.Pf.G2.jK_ι_ne_zero ha0ne
  have hα : ∀ i, algebraMap (𝓞 K) K (algebraMap (𝓞 F) (𝓞 K) (a i)) ≠ 0 := fun i => Formalism.L2.SG.Pf.G2.jK_ι_ne_zero (ha i)
  have hy : ∀ k i, h (b k) ((algebraMap (𝓞 K) K (algebraMap (𝓞 F) (𝓞 K) (a i)))⁻¹ • b i) = if k = i then 1 else 0 := by
    intro k i
    rw [LinearMap.map_smul, smul_eq_mul]
    split_ifs with hki
    · subst hki; rw [hdiag]; exact inv_mul_cancel₀ (hα k)
    · rw [horth k i hki, mul_zero]
  have hyA : ∀ i, (algebraMap (𝓞 K) K (algebraMap (𝓞 F) (𝓞 K) (a i)))⁻¹ • b i ∈ loc (K := K) P (dual h M) := by
    intro i
    rw [← hl, hA]
    intro k
    rw [hy]
    split_ifs
    · exact S.one_mem
    · exact S.zero_mem
  choose c hc hcM using fun i => hstr _ (hyA i)
  have hcS : ∀ i, c i ∈ S := fun i => hR _ (hc i)
  have hE : ∀ i k, ((if k = i then (1 : K) else 0) - c i * (h x x)⁻¹ * h (b k) x) / algebraMap (𝓞 K) K (algebraMap (𝓞 F) (𝓞 K) (a k)) ∈ S := by
    intro i k
    have h1 := hcM i
    rw [← hl] at h1
    have := (hB _).1 h1 k
    rwa [map_sub, hy, LinearMap.map_smul, smul_eq_mul] at this
  have hξ : ∀ k, h (b k) x / algebraMap (𝓞 K) K (algebraMap (𝓞 F) (𝓞 K) (a k)) ∈ S :=
    (hB x).1 (LocF.le_locF p M hxM)
  have hdS : h x x ∈ S := by rw [hd0]; exact HU.jK_mem_SP _

  have hle1 : ∀ i, vF p (a i) ≤ 1 := by
    intro i
    by_contra hgt
    push_neg at hgt
    have h1 : h x x / algebraMap (𝓞 K) K (algebraMap (𝓞 F) (𝓞 K) (a i)) ∈ S := by
      have e : h x x / algebraMap (𝓞 K) K (algebraMap (𝓞 F) (𝓞 K) (a i)) =
          h x x * (((if i = i then (1 : K) else 0) - c i * (h x x)⁻¹ * h (b i) x) / algebraMap (𝓞 K) K (algebraMap (𝓞 F) (𝓞 K) (a i))) + c i * (h (b i) x / algebraMap (𝓞 K) K (algebraMap (𝓞 F) (𝓞 K) (a i))) := by
        rw [if_pos rfl]; field_simp; ring
      rw [e]
      exact S.add_mem (S.mul_mem hdS (hE i i)) (S.mul_mem (hcS i) (hξ i))
    have h1' : algebraMap (𝓞 K) K a0 / algebraMap (𝓞 K) K (algebraMap (𝓞 F) (𝓞 K) (a i)) ∈ S := by
      rw [show algebraMap (𝓞 K) K a0 = h x x from ha0x]; exact h1
    have h2 := (Formalism.L2.SG.Pf.G2.div_mem_SP_iff hp (ha i) a0).1 h1'
    rw [hext] at h2
    exact ha0P2 (Ideal.pow_le_pow_right hgt h2)
  have huniq : ∀ i j, i ≠ j → vF p (a j) = 1 → 1 ≤ vF p (a i) → False := by
    intro i j hij hj hi
    have hci : c i / algebraMap (𝓞 K) K (algebraMap (𝓞 F) (𝓞 K) (a j)) ∈ S := by
      have e : c i / algebraMap (𝓞 K) K (algebraMap (𝓞 F) (𝓞 K) (a j)) = c i * (((if j = j then (1 : K) else 0) - c j * (h x x)⁻¹ * h (b j) x) / algebraMap (𝓞 K) K (algebraMap (𝓞 F) (𝓞 K) (a j)))
          - c j * (((if j = i then (1 : K) else 0) - c i * (h x x)⁻¹ * h (b j) x) / algebraMap (𝓞 K) K (algebraMap (𝓞 F) (𝓞 K) (a j))) := by
        rw [if_pos rfl, if_neg (fun e => hij e.symm)]; ring
      rw [e]
      exact S.sub_mem (S.mul_mem (hcS i) (hE j j)) (S.mul_mem (hcS j) (hE i j))
    obtain ⟨t, ht, w, hw⟩ := HU.mem_SP.1 (hcS i)
    have hw1 : algebraMap (𝓞 K) K w / algebraMap (𝓞 K) K (algebraMap (𝓞 F) (𝓞 K) (a j)) ∈ S := by
      rw [hw, mul_div_assoc]; exact S.mul_mem (HU.jK_mem_SP _) hci
    have hwP : w ∈ P := by
      have := (Formalism.L2.SG.Pf.G2.div_mem_SP_iff hp (ha j) w).1 hw1
      rwa [hj, pow_one, hext] at this
    have hw2 : algebraMap (𝓞 K) K w / algebraMap (𝓞 K) K (algebraMap (𝓞 F) (𝓞 K) a0') ∈ S :=
      (Formalism.L2.SG.Pf.G2.div_mem_SP_iff hp ha0ne w).2 (by rw [hv0, pow_one, hext]; exact hwP)
    have htne : algebraMap (𝓞 K) K (algebraMap (𝓞 F) (𝓞 K) t) ≠ 0 := Formalism.L2.SG.Pf.G2.jK_ι_ne_zero (Formalism.L2.SG.Pf.G2.ne_zero_of_notMem ht)
    have htinv : (algebraMap (𝓞 K) K (algebraMap (𝓞 F) (𝓞 K) t))⁻¹ ∈ S := HU.mem_SP.2 ⟨t, ht, 1, by rw [map_one, mul_inv_cancel₀ htne]⟩
    have hcd : c i * (h x x)⁻¹ ∈ S := by
      have e : c i * (h x x)⁻¹ = (algebraMap (𝓞 K) K (algebraMap (𝓞 F) (𝓞 K) t))⁻¹ * (algebraMap (𝓞 K) K w / algebraMap (𝓞 K) K (algebraMap (𝓞 F) (𝓞 K) a0')) := by
        rw [hw, ← hd0]; field_simp
      rw [e]; exact S.mul_mem htinv hw2
    have h1 : algebraMap (𝓞 K) K 1 / algebraMap (𝓞 K) K (algebraMap (𝓞 F) (𝓞 K) (a i)) ∈ S := by
      have e : algebraMap (𝓞 K) K 1 / algebraMap (𝓞 K) K (algebraMap (𝓞 F) (𝓞 K) (a i)) = ((if i = i then (1 : K) else 0) - c i * (h x x)⁻¹ * h (b i) x) / algebraMap (𝓞 K) K (algebraMap (𝓞 F) (𝓞 K) (a i))
          + (c i * (h x x)⁻¹) * (h (b i) x / algebraMap (𝓞 K) K (algebraMap (𝓞 F) (𝓞 K) (a i))) := by
        rw [if_pos rfl, map_one]; ring
      rw [e]; exact S.add_mem (hE i i) (S.mul_mem hcd (hξ i))
    have h2 := (Formalism.L2.SG.Pf.G2.div_mem_SP_iff hp (ha i) 1).1 h1
    rw [hext] at h2
    exact hP.ne_top ((Ideal.eq_top_iff_one P).2 (Ideal.pow_le_self (by omega) h2))
  have hex : ∃ i, vF p (a i) ≠ 0 := by
    by_contra hcon
    push_neg at hcon
    apply hPb.2
    have hinv : ∀ i, algebraMap (𝓞 K) K 1 / algebraMap (𝓞 K) K (algebraMap (𝓞 F) (𝓞 K) (a i)) ∈ S := fun i =>
      (Formalism.L2.SG.Pf.G2.div_mem_SP_iff hp (ha i) 1).2 (by rw [hcon i, pow_zero, Ideal.one_eq_top]; exact Submodule.mem_top)
    have heq : loc (K := K) P (dual h M) = loc (K := K) P M := by
      rw [← hl, ← hl]
      ext z
      rw [hA, hB]
      constructor
      · intro hz i
        have e : h (b i) z / algebraMap (𝓞 K) K (algebraMap (𝓞 F) (𝓞 K) (a i)) = h (b i) z * (algebraMap (𝓞 K) K 1 / algebraMap (𝓞 K) K (algebraMap (𝓞 F) (𝓞 K) (a i))) := by
          rw [map_one]; ring
        rw [e]; exact S.mul_mem (hz i) (hinv i)
      · intro hz i
        have e : h (b i) z = algebraMap (𝓞 K) K (algebraMap (𝓞 F) (𝓞 K) (a i)) * (h (b i) z / algebraMap (𝓞 K) K (algebraMap (𝓞 F) (𝓞 K) (a i))) := by
          field_simp [hα i]
        rw [e]; exact S.mul_mem (HU.jK_mem_SP _) (hz i)
    obtain ⟨σ, hσ⟩ := GlobalTheory.MaxLatStruct.star_int (K := K)
    have hinj := IsFractionRing.injective (𝓞 K) K
    have hstar : ∀ r : 𝓞 K, star (algebraMap (𝓞 K) K r) ∈ Set.range (algebraMap (𝓞 K) K) :=
      fun r => ⟨σ r, hσ r⟩
    unfold IsUnimodularAt
    rw [locDual_dualAt_loc h hinj hstar, ← le_antisymm (locDual_loc_dual_le h P M)
      (locDual_dualAt_le h hstar P M hM.1.1.fg)]
    exact heq
  obtain ⟨i, hi⟩ := hex
  have hi1 : vF p (a i) = 1 := le_antisymm (hle1 i) (Nat.one_le_iff_ne_zero.2 hi)
  refine ⟨i, hi1, fun j hji => ?_⟩
  by_contra hj
  exact huniq j i hji hi1 (Nat.one_le_iff_ne_zero.2 hj)

end GlobalTheory.MaxLatExpo

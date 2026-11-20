import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousAtPlace

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped GlobalTheory.VacAny
open Filter Topology

namespace GlobalTheory.SchrBox

/- English proof (translation)
Establish `hop : ∀ y : X, IsOpen {x | x - y ∈ B}` using `fun y => hB.preimage (continuous_id.sub continuous_const)`. Establish `key` using `(hK.diff (hop x₀)).induction_on (p := fun T => ∃ g ∈ Algebra.adjoin ℂ (Set.range χ), (∀ x, x - x₀ ∈ B → g x = 1) ∧ ∀ x ∈ T, g x = 0) ⟨1, one_mem _, fun _ _ => rfl, fun _ h => h.elim⟩ (fun s t hst ⟨g, hg, h1, h2⟩ => ⟨g, hg, h1, fun x hx => h2 x (hst hx)⟩) (fun s t hs ht => by`. Take `⟨g, hg, h1, h2⟩` from `hs`. Take `⟨g', hg', h1', h2'⟩` from `ht`. Use `⟨g * g', mul_mem hg hg', fun x hx => by simp [h1 x hx, h1' x hx], fun x hx => ?_⟩` and prove the remaining obligations.

Break down `hx with hx | hx` into its components or cases. Simplify using `[h2 x hx]`. Simplify using `[h2' x hx])`. Use the proof step `(fun y hy => by`. Take `⟨i, hi, hiB⟩` from `hsep (y - x₀) hy.2`.

Establish `hne : 1 - χ i (y - x₀) ≠ 0` using `sub_ne_zero.2 hi.symm`. Establish `hx0 : ∀ x, χ i (-x₀) * χ i x = χ i (x - x₀)` using `fun x => by`. Rewrite using `[← hχ]`. Use `congr 1`. Normalize the expressions using the abelian group laws.

Use `⟨{x | x - y ∈ B}, mem_nhdsWithin_of_mem_nhds ((hop y).mem_nhds (by simpa using h0)), (1 - χ i (y - x₀))⁻¹ • (χ i (-x₀) • χ i - χ i (y - x₀) • 1), ?_, fun x hx => ?_, fun x hx => ?_⟩` and prove the remaining obligations. Conclude with `Subalgebra.smul_mem _ (sub_mem (Subalgebra.smul_mem _ (Algebra.subset_adjoin (Set.mem_range_self i)) _) (Subalgebra.smul_mem _ (one_mem _) _)) _`. Simplify using `only [Pi.smul_apply, Pi.sub_apply, smul_eq_mul, Pi.one_apply, mul_one, hx0, hiB _ hx]`. Conclude with `inv_mul_cancel₀ hne`. Establish `: χ i (x - x₀) = χ i (y - x₀)`.

Rewrite using `[show x - x₀ = (x - y) + (y - x₀) by abel, hχ, hiB _ hx, one_mul]`. Simplify using `only [Pi.smul_apply, Pi.sub_apply, smul_eq_mul, Pi.one_apply, mul_one, hx0, this, sub_self, mul_zero])`. Take `⟨g, hg, h1, h2⟩` from `key`. Conclude with `⟨g, hg, h1, fun x hx hx' => h2 x ⟨hx, hx'⟩⟩`.
-/
theorem exists_cut {X ι : Type} [AddCommGroup X] [TopologicalSpace X] [IsTopologicalAddGroup X] (χ : ι → X → ℂ)
    (hχ : ∀ i x y, χ i (x + y) = χ i x * χ i y) {B : Set X} (hB : IsOpen B) (h0 : (0 : X) ∈ B)
    (hsep : ∀ z, z ∉ B → ∃ i, χ i z ≠ 1 ∧ ∀ u ∈ B, χ i u = 1) {K : Set X} (hK : IsCompact K) (x₀ : X) :
    ∃ g ∈ Algebra.adjoin ℂ (Set.range χ), (∀ x, x - x₀ ∈ B → g x = 1) ∧ ∀ x ∈ K, x - x₀ ∉ B → g x = 0 := by
  have hop : ∀ y : X, IsOpen {x | x - y ∈ B} := fun y => hB.preimage (continuous_id.sub continuous_const)
  have key := (hK.diff (hop x₀)).induction_on
    (p := fun T => ∃ g ∈ Algebra.adjoin ℂ (Set.range χ), (∀ x, x - x₀ ∈ B → g x = 1) ∧ ∀ x ∈ T, g x = 0)
    ⟨1, one_mem _, fun _ _ => rfl, fun _ h => h.elim⟩
    (fun s t hst ⟨g, hg, h1, h2⟩ => ⟨g, hg, h1, fun x hx => h2 x (hst hx)⟩)
    (fun s t hs ht => by
      obtain ⟨g, hg, h1, h2⟩ := hs
      obtain ⟨g', hg', h1', h2'⟩ := ht
      refine ⟨g * g', mul_mem hg hg', fun x hx => by simp [h1 x hx, h1' x hx], fun x hx => ?_⟩
      rcases hx with hx | hx
      · simp [h2 x hx]
      · simp [h2' x hx])
    (fun y hy => by
      obtain ⟨i, hi, hiB⟩ := hsep (y - x₀) hy.2
      have hne : 1 - χ i (y - x₀) ≠ 0 := sub_ne_zero.2 hi.symm
      have hx0 : ∀ x, χ i (-x₀) * χ i x = χ i (x - x₀) := fun x => by
        rw [← hχ]; congr 1; abel
      refine ⟨{x | x - y ∈ B}, mem_nhdsWithin_of_mem_nhds ((hop y).mem_nhds (by simpa using h0)),
        (1 - χ i (y - x₀))⁻¹ • (χ i (-x₀) • χ i - χ i (y - x₀) • 1), ?_, fun x hx => ?_, fun x hx => ?_⟩
      · exact Subalgebra.smul_mem _ (sub_mem (Subalgebra.smul_mem _ (Algebra.subset_adjoin (Set.mem_range_self i)) _)
          (Subalgebra.smul_mem _ (one_mem _) _)) _
      · simp only [Pi.smul_apply, Pi.sub_apply, smul_eq_mul, Pi.one_apply, mul_one, hx0, hiB _ hx]
        exact inv_mul_cancel₀ hne
      · have : χ i (x - x₀) = χ i (y - x₀) := by
          rw [show x - x₀ = (x - y) + (y - x₀) by abel, hχ, hiB _ hx, one_mul]
        simp only [Pi.smul_apply, Pi.sub_apply, smul_eq_mul, Pi.one_apply, mul_one, hx0, this, sub_self, mul_zero])
  obtain ⟨g, hg, h1, h2⟩ := key
  exact ⟨g, hg, h1, fun x hx hx' => h2 x ⟨hx, hx'⟩⟩

/- English proof (translation)
Establish `key : ∀ f ∈ Submodule.span ℂ (Set.range fun i => χ i * s), g * f ∈ Submodule.span ℂ (Set.range fun i => χ i * s)`. Proceed by induction on `hg using Algebra.adjoin_induction with`. Consider the case `mem x hx`. Take `⟨i, rfl⟩` from `hx`. Introduce `f hf`.

Proceed by induction on `hf using Submodule.span_induction with`. Consider the case `mem y hy`. Take `⟨j, rfl⟩` from `hy`. Conclude with `Submodule.subset_span ⟨i + j, by simp only [hχ, mul_assoc]⟩`. Consider the case `zero => simp`.

Consider the case `add a b _ _ ha hb => rw [mul_add]`. Conclude with `add_mem ha hb`. Consider the case `smul c a _ ha => rw [mul_smul_comm]`. Conclude with `Submodule.smul_mem _ _ ha`. Consider the case `algebraMap r => intro f hf`.

Rewrite using `[← Algebra.smul_def]`. Conclude with `Submodule.smul_mem _ _ hf`. Consider the case `add a b _ _ ha hb => intro f hf`. Rewrite using `[add_mul]`. Conclude with `add_mem (ha f hf) (hb f hf)`.

Consider the case `mul a b _ _ ha hb => intro f hf`. Rewrite using `[mul_assoc]`. Conclude with `ha _ (hb f hf)`. Conclude with `key s (Submodule.subset_span ⟨0, by simp [h0]⟩)`.
-/
theorem adjoin_mul_mem {X ι : Type} [AddCommGroup ι] (χ : ι → X → ℂ) (h0 : χ 0 = 1) (hχ : ∀ i j, χ (i + j) = χ i * χ j)
    (s : X → ℂ) {g : X → ℂ} (hg : g ∈ Algebra.adjoin ℂ (Set.range χ)) :
    g * s ∈ Submodule.span ℂ (Set.range fun i => χ i * s) := by
  have key : ∀ f ∈ Submodule.span ℂ (Set.range fun i => χ i * s),
      g * f ∈ Submodule.span ℂ (Set.range fun i => χ i * s) := by
    induction hg using Algebra.adjoin_induction with
    | mem x hx =>
      obtain ⟨i, rfl⟩ := hx
      intro f hf
      induction hf using Submodule.span_induction with
      | mem y hy =>
        obtain ⟨j, rfl⟩ := hy
        exact Submodule.subset_span ⟨i + j, by simp only [hχ, mul_assoc]⟩
      | zero => simp
      | add a b _ _ ha hb => rw [mul_add]; exact add_mem ha hb
      | smul c a _ ha => rw [mul_smul_comm]; exact Submodule.smul_mem _ _ ha
    | algebraMap r => intro f hf; rw [← Algebra.smul_def]; exact Submodule.smul_mem _ _ hf
    | add a b _ _ ha hb => intro f hf; rw [add_mul]; exact add_mem (ha f hf) (hb f hf)
    | mul a b _ _ ha hb => intro f hf; rw [mul_assoc]; exact ha _ (hb f hf)
  exact key s (Submodule.subset_span ⟨0, by simp [h0]⟩)

variable {F : Type} [Field F] [NumberField F] {v : Pl F}

/- English proof (translation)
Take `⟨c, hc⟩` from `HeightOneSpectrum.valuedAdicCompletion_surjective F v (WithZero.exp n)`. Establish `hc0 : c ≠ 0`. Introduce and unpack `rfl`. Rewrite `hc` using `[map_zero]`. Conclude with `WithZero.exp_ne_zero hc.symm`.

Establish `: {y : Fv F v | Valued.v y ≤ WithZero.exp n} = {y | Valued.v.restrict y ≤ Valued.v.restrict c}`. Use extensionality with `y`. Simplify using `only [Set.mem_ofPred_eq, Valuation.restrict_le_iff, hc]`. Rewrite using `[this]`. Conclude with `Valued.isOpen_closedBall _ (by simp [hc0])`.
-/
theorem isOpen_ball (n : ℤ) : IsOpen {y : Fv F v | Valued.v y ≤ WithZero.exp n} := by
  obtain ⟨c, hc⟩ := HeightOneSpectrum.valuedAdicCompletion_surjective F v (WithZero.exp n)
  have hc0 : c ≠ 0 := by
    rintro rfl
    rw [map_zero] at hc
    exact WithZero.exp_ne_zero hc.symm
  have : {y : Fv F v | Valued.v y ≤ WithZero.exp n} = {y | Valued.v.restrict y ≤ Valued.v.restrict c} := by
    ext y
    simp only [Set.mem_ofPred_eq, Valuation.restrict_le_iff, hc]
  rw [this]
  exact Valued.isOpen_closedBall _ (by simp [hc0])

/- English proof (translation)
Take `⟨γ, hγ⟩` from `Valued.mem_nhds.1 hU`. Establish `hne : MonoidWithZeroHom.ValueGroup₀.embedding γ.1 ≠ 0` using `by simp`. Use `⟨(WithZero.log (MonoidWithZeroHom.ValueGroup₀.embedding γ.1)).natAbs + 1, fun N hN y hy => hγ ?_⟩` and prove the remaining obligations. Simplify using `only [Set.mem_ofPred_eq, Valuation.restrict_lt_iff_lt_embedding]`. Use `hy.trans_lt ?_` and prove the remaining obligations.

Use `conv_rhs => rw [← WithZero.exp_log hne]`. Rewrite using `[WithZero.exp_lt_exp]`. Use linear arithmetic over natural numbers and integers.
-/
theorem exists_ball_subset {U : Set (Fv F v)} {x : Fv F v} (hU : U ∈ 𝓝 x) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ y, Valued.v (y - x) ≤ WithZero.exp (-(N : ℤ)) → y ∈ U := by
  obtain ⟨γ, hγ⟩ := Valued.mem_nhds.1 hU
  have hne : MonoidWithZeroHom.ValueGroup₀.embedding γ.1 ≠ 0 := by simp
  refine ⟨(WithZero.log (MonoidWithZeroHom.ValueGroup₀.embedding γ.1)).natAbs + 1, fun N hN y hy => hγ ?_⟩
  simp only [Set.mem_ofPred_eq, Valuation.restrict_lt_iff_lt_embedding]
  refine hy.trans_lt ?_
  conv_rhs => rw [← WithZero.exp_log hne]
  rw [WithZero.exp_lt_exp]
  omega

/- English proof (translation)
Take `⟨c, hc⟩` from `HeightOneSpectrum.valuedAdicCompletion_surjective F v (WithZero.exp n)`. Establish `hmem : ∀ u : Fv F v, u / c ∈ v.adicCompletionIntegers F ↔ Valued.v u ≤ WithZero.exp n` using `fun u => by`. Rewrite using `[HeightOneSpectrum.mem_adicCompletionIntegers, map_div₀, hc, div_le_one₀ WithZero.exp_pos]`. Establish `h1` using `mt (hψ (z / c)).1 (mt (hmem z).1 hz)`. Use `push Not at h1`.

Take `⟨y, hy, hy1⟩` from `h1`. Use `⟨y / c, by rwa [show z * (y / c) = z / c * y by ring], fun u hu => ?_⟩` and prove the remaining obligations. Rewrite using `[show u * (y / c) = u / c * y by ring]`. Conclude with `(hψ _).2 ((hmem u).2 hu) y hy`.
-/
theorem exists_sep {ψ : AddChar (Fv F v) ℂ}
    (hψ : ∀ x : Fv F v, (∀ y ∈ v.adicCompletionIntegers F, ψ (x * y) = 1) ↔ x ∈ v.adicCompletionIntegers F)
    (n : ℤ) {z : Fv F v} (hz : ¬ Valued.v z ≤ WithZero.exp n) :
    ∃ t, ψ (z * t) ≠ 1 ∧ ∀ u, Valued.v u ≤ WithZero.exp n → ψ (u * t) = 1 := by
  obtain ⟨c, hc⟩ := HeightOneSpectrum.valuedAdicCompletion_surjective F v (WithZero.exp n)
  have hmem : ∀ u : Fv F v, u / c ∈ v.adicCompletionIntegers F ↔ Valued.v u ≤ WithZero.exp n := fun u => by
    rw [HeightOneSpectrum.mem_adicCompletionIntegers, map_div₀, hc, div_le_one₀ WithZero.exp_pos]
  have h1 := mt (hψ (z / c)).1 (mt (hmem z).1 hz)
  push Not at h1
  obtain ⟨y, hy, hy1⟩ := h1
  refine ⟨y / c, by rwa [show z * (y / c) = z / c * y by ring], fun u hu => ?_⟩
  rw [show u * (y / c) = u / c * y by ring]
  exact (hψ _).2 ((hmem u).2 hu) y hy

/- English proof (translation)
Introduce `F _ _ v ψ hψ κ _ s hs hs0`. Take `⟨x₀, hx₀⟩` from `Function.ne_iff.1 hs0`. Establish `hx₀ : s x₀ ≠ 0` using `hx₀`. Establish `hU : {x | s x = s x₀} ∈ 𝓝 x₀` using `(hs.1.isOpen_fiber (s x₀)).mem_nhds rfl`. Rewrite `hU` using `[nhds_pi, Filter.mem_pi']`.

Take `⟨I, t, ht, htU⟩` from `hU`. Use `choose M hM using fun i => exists_ball_subset (ht i)`. Use `⟨x₀, Finset.univ.sup M, fun N hN => ?_⟩` and prove the remaining obligations. Establish `hconst : ∀ x : κ → Fv F v, (∀ i, Valued.v (x i - x₀ i) ≤ WithZero.exp (-(N : ℤ))) → s x = s x₀` using `fun x hx => htU fun i _ => hM i N ((Finset.le_sup (f := M) (Finset.mem_univ i)).trans hN) _ (hx i)`. Set `χ : (κ → Fv F v) → (κ → Fv F v) → ℂ` to `fun b x => ψ (x ⬝ᵥ b)`.

Establish `hB : IsOpen {x : κ → Fv F v | ∀ i, Valued.v (x i) ≤ WithZero.exp (-(N : ℤ))}`. Rewrite using `[Set.ofPred_forall]`. Conclude with `isOpen_iInter_of_finite fun i => (isOpen_ball (v := v) (-(N : ℤ))).preimage (continuous_apply (A := fun _ : κ => Fv F v) i)`. Take `⟨g, hg, h1, h2⟩` from `exists_cut χ (fun b x y => by simp only [χ, add_dotProduct, AddChar.map_add_eq_mul]) hB (by simp) (fun z hz => by`. Simplify using `only [Set.mem_ofPred_eq, not_forall] at hz`.

Take `⟨i, hi⟩` from `hz`. Take `⟨t, ht1, ht2⟩` from `exists_sep hψ _ hi`. Conclude with `⟨Pi.single i t, by simpa only [χ, dotProduct_single] using ht1, fun u hu => by simpa only [χ, dotProduct_single] using ht2 _ (hu i)⟩) hs.2 x₀`. Establish `hm` using `adjoin_mul_mem χ (by ext x; simp [χ]) (fun i j => by ext x; simp only [χ, dotProduct_add, AddChar.map_add_eq_mul, Pi.mul_apply]) s hg`. Establish `hle : Submodule.span ℂ (Set.range fun b => χ b * s) ≤ Submodule.span ℂ (Set.range fun w : (κ → Fv F v) × (κ → Fv F v) => schr ψ w s)`.

Use `Submodule.span_mono ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨b, rfl⟩`. Conclude with `⟨(0, b), by ext x; simp [schr, χ]⟩`. Use `Submodule.smul_mem _ (s x₀)⁻¹ (hle hm)` as an intermediate fact. Use `this using 1` and compare the differences between its conclusion and the goal.

Use extensionality with `x`. Distinguish the cases in `hx : ∀ i, Valued.v (x i - x₀ i) ≤ WithZero.exp (-(N : ℤ))`. Rewrite using `[Set.indicator_of_mem (by exact hx)]`. Simplify using `[h1 x hx, hconst x hx, hx₀]`. Rewrite using `[Set.indicator_of_notMem (by exact hx)]`.

Distinguish the cases in `hxs : x ∈ tsupport s`. Simplify using `[h2 x hxs hx]`. Simplify using `[image_eq_zero_of_notMem_tsupport hxs]`.
-/
theorem indicator_box_mem_span : ∀ (F : Type) [Field F] [NumberField F] (v : Pl F) (ψ : AddChar (Fv F v) ℂ), (∀ x : Fv F v, (∀ y ∈ v.adicCompletionIntegers F, ψ (x * y) = 1) ↔ x ∈ v.adicCompletionIntegers F) → ∀ (κ : Type) [Fintype κ] (s : (κ → Fv F v) → ℂ), s ∈ SB (κ → Fv F v) → s ≠ 0 → ∃ (x₀ : κ → Fv F v) (N₀ : ℕ), ∀ N ≥ N₀, Set.indicator {x : κ → Fv F v | ∀ i, Valued.v (x i - x₀ i) ≤ WithZero.exp (-(N : ℤ))} (1 : (κ → Fv F v) → ℂ) ∈ Submodule.span ℂ (Set.range fun w : (κ → Fv F v) × (κ → Fv F v) => schr ψ w s) := by
  intro F _ _ v ψ hψ κ _ s hs hs0
  classical
  obtain ⟨x₀, hx₀⟩ := Function.ne_iff.1 hs0
  have hx₀ : s x₀ ≠ 0 := hx₀
  have hU : {x | s x = s x₀} ∈ 𝓝 x₀ := (hs.1.isOpen_fiber (s x₀)).mem_nhds rfl
  rw [nhds_pi, Filter.mem_pi'] at hU
  obtain ⟨I, t, ht, htU⟩ := hU
  choose M hM using fun i => exists_ball_subset (ht i)
  refine ⟨x₀, Finset.univ.sup M, fun N hN => ?_⟩
  have hconst : ∀ x : κ → Fv F v, (∀ i, Valued.v (x i - x₀ i) ≤ WithZero.exp (-(N : ℤ))) → s x = s x₀ :=
    fun x hx => htU fun i _ => hM i N ((Finset.le_sup (f := M) (Finset.mem_univ i)).trans hN) _ (hx i)
  let χ : (κ → Fv F v) → (κ → Fv F v) → ℂ := fun b x => ψ (x ⬝ᵥ b)
  have hB : IsOpen {x : κ → Fv F v | ∀ i, Valued.v (x i) ≤ WithZero.exp (-(N : ℤ))} := by
    rw [Set.ofPred_forall]
    exact isOpen_iInter_of_finite fun i => (isOpen_ball (v := v) (-(N : ℤ))).preimage (continuous_apply (A := fun _ : κ => Fv F v) i)
  obtain ⟨g, hg, h1, h2⟩ := exists_cut χ (fun b x y => by simp only [χ, add_dotProduct, AddChar.map_add_eq_mul]) hB
    (by simp) (fun z hz => by
      simp only [Set.mem_ofPred_eq, not_forall] at hz
      obtain ⟨i, hi⟩ := hz
      obtain ⟨t, ht1, ht2⟩ := exists_sep hψ _ hi
      exact ⟨Pi.single i t, by simpa only [χ, dotProduct_single] using ht1,
        fun u hu => by simpa only [χ, dotProduct_single] using ht2 _ (hu i)⟩) hs.2 x₀
  have hm := adjoin_mul_mem χ (by ext x; simp [χ])
    (fun i j => by ext x; simp only [χ, dotProduct_add, AddChar.map_add_eq_mul, Pi.mul_apply]) s hg
  have hle : Submodule.span ℂ (Set.range fun b => χ b * s) ≤
      Submodule.span ℂ (Set.range fun w : (κ → Fv F v) × (κ → Fv F v) => schr ψ w s) := by
    refine Submodule.span_mono ?_
    rintro _ ⟨b, rfl⟩
    exact ⟨(0, b), by ext x; simp [schr, χ]⟩
  have := Submodule.smul_mem _ (s x₀)⁻¹ (hle hm)
  convert this using 1
  ext x
  by_cases hx : ∀ i, Valued.v (x i - x₀ i) ≤ WithZero.exp (-(N : ℤ))
  · rw [Set.indicator_of_mem (by exact hx)]
    simp [h1 x hx, hconst x hx, hx₀]
  · rw [Set.indicator_of_notMem (by exact hx)]
    by_cases hxs : x ∈ tsupport s
    · simp [h2 x hxs hx]
    · simp [image_eq_zero_of_notMem_tsupport hxs]

end GlobalTheory.SchrBox

import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ShearGL
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CompactSetFiniteCosetRepresentatives

open Matrix MeasureTheory GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.BZSeg GlobalTheory.BZMir GlobalTheory.SplitWeil GlobalTheory.CompanionTheory.MirFourier GlobalTheory.CompanionTheory.BZOnto.PerpSmall ValuativeRel Zc
open scoped Topology
open GlobalTheory.CompanionTheory.MirPair

noncomputable section

namespace GlobalTheory.CompanionTheory.MirPair.AvgBox

/- English proof (translation)
Use `set A : E → Set E := fun s => (fun x => -s + x) ⁻¹' (D : Set E) with hA`. Establish `hAm : ∀ s, MeasurableSet (A s)` using `fun s => (measurable_const_add (-s)) hD`. Establish `hmem : ∀ s x, x ∈ A s ↔ x - s ∈ D`. Introduce `s x`. Simplify using `only [hA, Set.mem_preimage, SetLike.mem_coe, neg_add_eq_sub]`.

Establish `hAM : ∀ s ∈ S, ∀ x ∈ A s, x ∈ M`. Introduce `s hs x hx`. Use `M.add_mem (hDM ((hmem s x).1 hx)) (hSM s hs)` as an intermediate fact. Simplify using `using this`. Establish `hU : (M : Set E) = ⋃ s ∈ S, A s`.

Use extensionality with `x`. Simplify using `only [Set.mem_iUnion, SetLike.mem_coe, exists_prop]`. Prove the components needed by the constructor for the conclusion. Introduce `hx`. Take `⟨s, ⟨hs, hxs⟩, -⟩` from `hS x hx`.

Conclude with `⟨s, hs, (hmem s x).2 hxs⟩`. Introduce and unpack `⟨s, hs, hx⟩`. Conclude with `hAM s hs x hx`. Establish `hdisj : Set.Pairwise (S : Set E) (Function.onFun Disjoint A)`. Introduce `s hs s' hs' hne`.

Use `Set.disjoint_left.2 fun x hx hx' => hne ?_` and prove the remaining obligations. Conclude with `(hS x (hAM s hs x hx)).unique ⟨hs, (hmem s x).1 hx⟩ ⟨hs', (hmem s' x).1 hx'⟩`. Establish `hconst : ∀ s, Set.EqOn (fun _ => f s) f (A s)`. Introduce `s x hx`. Use `hf s (x - s) ((hmem s x).1 hx)` as an intermediate fact.

Simplify using `using this.symm`. Establish `hvol : ∀ s, μ (A s) = μ (D : Set E)` using `fun s => measure_preimage_add μ (-s) _`. Rewrite using `[hU, integral_biUnion_finset S (fun s _ => hAm s) hdisj ?_]`. Rewrite using `[Finset.mul_sum]`. Use `Finset.sum_congr rfl fun s _ => ?_` and prove the remaining obligations.

Rewrite using `[← setIntegral_congr_fun (hAm s) (hconst s), setIntegral_const]`. Simplify using `[Measure.real, hvol]`. Introduce `s _`. Use `IntegrableOn.congr_fun ?_ (hconst s) (hAm s)` and prove the remaining obligations. Conclude with `integrableOn_const (by rw [hvol]; exact hfin)`.
-/
theorem setIntegral_eq_sum_reps {E : Type} [AddCommGroup E] [MeasurableSpace E] [MeasurableAdd E]
    (μ : Measure E) [μ.IsAddLeftInvariant] (D M : AddSubgroup E) (hD : MeasurableSet (D : Set E))
    (hfin : μ (D : Set E) ≠ ⊤) (hDM : D ≤ M) (S : Finset E) (hSM : ∀ s ∈ S, s ∈ M)
    (hS : ∀ x ∈ M, ∃! s, s ∈ S ∧ x - s ∈ D) (f : E → ℂ) (hf : ∀ x, ∀ d ∈ D, f (x + d) = f x) :
    ∫ x in (M : Set E), f x ∂μ = ((μ.real (D : Set E) : ℝ) : ℂ) * ∑ s ∈ S, f s := by
  classical
  set A : E → Set E := fun s => (fun x => -s + x) ⁻¹' (D : Set E) with hA
  have hAm : ∀ s, MeasurableSet (A s) := fun s => (measurable_const_add (-s)) hD
  have hmem : ∀ s x, x ∈ A s ↔ x - s ∈ D := by
    intro s x
    simp only [hA, Set.mem_preimage, SetLike.mem_coe, neg_add_eq_sub]
  have hAM : ∀ s ∈ S, ∀ x ∈ A s, x ∈ M := by
    intro s hs x hx
    have := M.add_mem (hDM ((hmem s x).1 hx)) (hSM s hs)
    simpa using this
  have hU : (M : Set E) = ⋃ s ∈ S, A s := by
    ext x
    simp only [Set.mem_iUnion, SetLike.mem_coe, exists_prop]
    constructor
    · intro hx
      obtain ⟨s, ⟨hs, hxs⟩, -⟩ := hS x hx
      exact ⟨s, hs, (hmem s x).2 hxs⟩
    · rintro ⟨s, hs, hx⟩
      exact hAM s hs x hx
  have hdisj : Set.Pairwise (S : Set E) (Function.onFun Disjoint A) := by
    intro s hs s' hs' hne
    refine Set.disjoint_left.2 fun x hx hx' => hne ?_
    exact (hS x (hAM s hs x hx)).unique ⟨hs, (hmem s x).1 hx⟩ ⟨hs', (hmem s' x).1 hx'⟩
  have hconst : ∀ s, Set.EqOn (fun _ => f s) f (A s) := by
    intro s x hx
    have := hf s (x - s) ((hmem s x).1 hx)
    simpa using this.symm
  have hvol : ∀ s, μ (A s) = μ (D : Set E) := fun s => measure_preimage_add μ (-s) _
  rw [hU, integral_biUnion_finset S (fun s _ => hAm s) hdisj ?_]
  · rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [← setIntegral_congr_fun (hAm s) (hconst s), setIntegral_const]
    simp [Measure.real, hvol]
  · intro s _
    refine IntegrableOn.congr_fun ?_ (hconst s) (hAm s)
    exact integrableOn_const (by rw [hvol]; exact hfin)

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

/- English proof (translation)
Simplify using `only [uM, ofAdd_add, map_mul]`.
-/
theorem uM_add (n : ℕ) (x y : Fin n → k) : uM n (x + y) = uM n x * uM n y := by
  simp only [uM, ofAdd_add, map_mul]

/- English proof (translation)
The claim follows from `(continuous_unipIn n).comp continuous_ofAdd`.
-/
theorem continuous_uM (n : ℕ) : Continuous (uM (k := k) n) :=
  (continuous_unipIn n).comp continuous_ofAdd

section Rep

variable {n : ℕ} {V V' : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup V'] [Module ℂ V']

/- English proof (translation)
Set `x : MirUin k (n + 1)` to `⟨uM (n + 1) y, Subgroup.mem_subgroupOf.2 ⟨Multiplicative.ofAdd y, rfl⟩⟩`. Establish `hx` using `mirChar_eq k ψ n x (Multiplicative.ofAdd y) rfl`. Use `Submodule.subset_span ⟨x, v, ?_⟩` and prove the remaining obligations. Rewrite using `[hx]`. Both sides reduce to the same expression.
-/
theorem sub_smul_mem_twKer (ψ : AddChar k Circle) (T : Representation ℂ (Mir k (n + 1)) V)
    (y : Fin (n + 1) → k) (v : V) :
    T (uM (n + 1) y) v - ((ψ (y (Fin.last n)) : Circle) : ℂ) • v ∈
      twKer T (MirUin k (n + 1)) (mirChar k ψ n) := by
  let x : MirUin k (n + 1) := ⟨uM (n + 1) y, Subgroup.mem_subgroupOf.2 ⟨Multiplicative.ofAdd y, rfl⟩⟩
  have hx := mirChar_eq k ψ n x (Multiplicative.ofAdd y) rfl
  refine Submodule.subset_span ⟨x, v, ?_⟩
  rw [hx]
  rfl

/- English proof (translation)
Rewrite using `[wt, ← Circle.coe_mul, ← AddChar.map_add_eq_mul]`. Simplify using the standard rewrite rules.
-/
theorem wt_mul_psi (ψ : AddChar k Circle) (y : Fin (n + 1) → k) :
    wt ψ n y * ((ψ (y (Fin.last n)) : Circle) : ℂ) = 1 := by
  rw [wt, ← Circle.coe_mul, ← AddChar.map_add_eq_mul]
  simp

/- English proof (translation)
Establish `h : (∑ s ∈ S, wt ψ n s • T (uM (n + 1) s) v) - (S.card : ℂ) • v = ∑ s ∈ S, wt ψ n s • (T (uM (n + 1) s) v - ((ψ (s (Fin.last n)) : Circle) : ℂ) • v)`. Simplify using `only [smul_sub, smul_smul, wt_mul_psi, one_smul, Finset.sum_sub_distrib, Finset.sum_const, Nat.cast_smul_eq_nsmul]`. Rewrite using `[h]`. Conclude with `Submodule.sum_mem _ fun s _ => Submodule.smul_mem _ _ (sub_smul_mem_twKer ψ T s v)`.
-/
theorem avg_sub_mem_twKer (ψ : AddChar k Circle) (T : Representation ℂ (Mir k (n + 1)) V)
    (S : Finset (Fin (n + 1) → k)) (v : V) :
    (∑ s ∈ S, wt ψ n s • T (uM (n + 1) s) v) - (S.card : ℂ) • v ∈
      twKer T (MirUin k (n + 1)) (mirChar k ψ n) := by
  have h : (∑ s ∈ S, wt ψ n s • T (uM (n + 1) s) v) - (S.card : ℂ) • v =
      ∑ s ∈ S, wt ψ n s • (T (uM (n + 1) s) v - ((ψ (s (Fin.last n)) : Circle) : ℂ) • v) := by
    simp only [smul_sub, smul_smul, wt_mul_psi, one_smul, Finset.sum_sub_distrib, Finset.sum_const,
      Nat.cast_smul_eq_nsmul]
  rw [h]
  exact Submodule.sum_mem _ fun s _ => Submodule.smul_mem _ _ (sub_smul_mem_twKer ψ T s v)

/- English proof (translation)
Establish `h1 : wt ψ n (x + d) = wt ψ n x`. Simplify using `only [wt, Pi.add_apply, neg_add, AddChar.map_add_eq_mul, AddChar.map_neg_eq_inv, hψ, inv_one, mul_one]`. Establish `h2 : coef T B v v' (x + d) = coef T B v v' x`. Simplify using `only [coef, uM_add, map_mul, Module.End.mul_apply, hd]`. Rewrite using `[h1, h2]`.
-/
theorem integrand_add (ψ : AddChar k Circle) (T : Representation ℂ (Mir k (n + 1)) V) (B : V →ₗ[ℂ] V' →ₗ[ℂ] ℂ)
    (v : V) (v' : V') (x d : Fin (n + 1) → k) (hd : T (uM (n + 1) d) v = v)
    (hψ : ψ (d (Fin.last n)) = 1) :
    wt ψ n (x + d) * coef T B v v' (x + d) = wt ψ n x * coef T B v v' x := by
  have h1 : wt ψ n (x + d) = wt ψ n x := by
    simp only [wt, Pi.add_apply, neg_add, AddChar.map_add_eq_mul, AddChar.map_neg_eq_inv, hψ, inv_one, mul_one]
  have h2 : coef T B v v' (x + d) = coef T B v v' x := by
    simp only [coef, uM_add, map_mul, Module.End.mul_apply, hd]
  rw [h1, h2]

end Rep

/- English proof (translation)
Introduce `k _ _ _ _ _ _ ν _ ψ n V V' _ _ _ _ T B hψ hT hB v hv`. Use `haveI : SecondCountableTopology k := GlobalTheory.SplitWeil.secondCountable k`. Use `haveI : SigmaFinite ν := sigmaFinite_of_locallyFinite`. Use `haveI : (piHaar ν (n + 1)).IsAddHaarMeasure := by`. Unfold `piHaar`.

Use `infer_instance`. Take `⟨r, hr⟩` from `exists_cball_addChar_eq_one ψ hψ`. Establish `hΩ₁ : {y : Fin (n + 1) → k | T (uM (n + 1) y) v = v} ∈ 𝓝 (0 : Fin (n + 1) → k)`. Use `((hT v).preimage (continuous_uM (n + 1))).mem_nhds ?_` and prove the remaining obligations. Simplify using `[uM]`.

Establish `hΩ₂ : {y : Fin (n + 1) → k | y (Fin.last n) ∈ cball r} ∈ 𝓝 (0 : Fin (n + 1) → k)`. Establish `h0 : cball r ∈ 𝓝 ((0 : Fin (n + 1) → k) (Fin.last n))` using `by simpa using cball_mem_nhds r`. Conclude with `(continuous_apply (Fin.last n)).continuousAt h0`. Take `⟨t₀, ht₀⟩` from `exists_box_subset (Filter.inter_mem hΩ₁ hΩ₂)`. Use `⟨t₀, fun t ht => ?_⟩` and prove the remaining obligations.

Establish `hDM : box (n + 1) t₀ ≤ box (n + 1) t` using `fun x hx j => show valuation k (x j) ≤ valuation k (t : k) from le_trans (show valuation k (x j) ≤ valuation k (t₀ : k) from hx j) ht`. Establish `hDo : IsOpen (box (n + 1) t₀ : Set (Fin (n + 1) → k))` using `AddSubgroup.isOpen_of_mem_nhds _ (g := 0) (box_mem_nhds (n + 1) t₀)`. Take `⟨S, hSM, hS⟩` from `GlobalTheory.CompanionTheory.OpenSubgroupCosets.exists_finset_unique_coset_reps (box (n + 1) t₀) hDo (box (n + 1) t : Set (Fin (n + 1) → k)) (isCompact_box (n + 1) t)`. Establish `hfin : piHaar ν (n + 1) (box (n + 1) t₀ : Set (Fin (n + 1) → k)) ≠ ⊤` using `(isCompact_box (n + 1) t₀).measure_lt_top.ne`. Establish `hpos : piHaar ν (n + 1) (box (n + 1) t₀ : Set (Fin (n + 1) → k)) ≠ 0` using `hDo.measure_ne_zero _ ⟨0, (box (n + 1) t₀).zero_mem⟩`.

Establish `hvol : ((piHaar ν (n + 1)).real (box (n + 1) t₀ : Set (Fin (n + 1) → k)) : ℝ) ≠ 0` using `(ENNReal.toReal_pos hpos hfin).ne'`. Establish `hcard : (S.card : ℂ) ≠ 0`. Take `⟨s, ⟨hs, -⟩, -⟩` from `hS 0 (box (n + 1) t).zero_mem`. Conclude with `Nat.cast_ne_zero.2 (Finset.card_ne_zero_of_mem hs)`. Use `set v₁ : V := ∑ s ∈ S, wt ψ n s • T (uM (n + 1) s) v with hv₁`.

Establish `hv₁0 : v₁ ≠ 0`. Introduce `h0`. Establish `h` using `avg_sub_mem_twKer ψ T S v`. Rewrite `h` using `[← hv₁, h0, zero_sub, neg_mem_iff]`. Conclude with `hv ((Submodule.smul_mem_iff _ hcard).1 h)`.

Take `⟨v', hv'⟩` from `hB v₁ hv₁0`. Use `⟨v', ?_⟩` and prove the remaining obligations. Establish `hJ : JJ ν ψ T B (box (n + 1) t : Set (Fin (n + 1) → k)) v v' = (((piHaar ν (n + 1)).real (box (n + 1) t₀ : Set (Fin (n + 1) → k)) : ℝ) : ℂ) * B v₁ v'`. Rewrite using `[JJ, setIntegral_eq_sum_reps (piHaar ν (n + 1)) (box (n + 1) t₀) (box (n + 1) t) hDo.measurableSet hfin hDM S hSM hS _ fun x d hd => integrand_add ψ T B v v' x d (ht₀ hd).1 (hr _ (ht₀ hd).2)]`. Simplify using `only [hv₁, map_sum, LinearMap.sum_apply, map_smul, LinearMap.smul_apply, smul_eq_mul, coef]`.

Rewrite using `[hJ]`. Conclude with `mul_ne_zero (Complex.ofReal_ne_zero.2 hvol) hv'`.
-/
theorem exists_JJ_ne_zero : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (ν : Measure k) [ν.IsAddHaarMeasure] (ψ : AddChar k Circle) {n : ℕ} {V V' : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup V'] [Module ℂ V'] (T : Representation ℂ (Mir k (n + 1)) V) (B : V →ₗ[ℂ] V' →ₗ[ℂ] ℂ), Continuous ψ → IsSmooth T → (∀ v, v ≠ 0 → ∃ v', B v v' ≠ 0) → ∀ v : V, v ∉ twKer T (MirUin k (n + 1)) (mirChar k ψ n) → ∃ t₀ : kˣ, ∀ t : kˣ, valuation k (t₀ : k) ≤ valuation k (t : k) → ∃ v', JJ ν ψ T B (box (n + 1) t : Set (Fin (n + 1) → k)) v v' ≠ 0 := by
  intro k _ _ _ _ _ _ ν _ ψ n V V' _ _ _ _ T B hψ hT hB v hv
  haveI : SecondCountableTopology k := GlobalTheory.SplitWeil.secondCountable k
  haveI : SigmaFinite ν := sigmaFinite_of_locallyFinite
  haveI : (piHaar ν (n + 1)).IsAddHaarMeasure := by
    unfold piHaar
    infer_instance
  obtain ⟨r, hr⟩ := exists_cball_addChar_eq_one ψ hψ
  have hΩ₁ : {y : Fin (n + 1) → k | T (uM (n + 1) y) v = v} ∈ 𝓝 (0 : Fin (n + 1) → k) := by
    refine ((hT v).preimage (continuous_uM (n + 1))).mem_nhds ?_
    simp [uM]
  have hΩ₂ : {y : Fin (n + 1) → k | y (Fin.last n) ∈ cball r} ∈ 𝓝 (0 : Fin (n + 1) → k) := by
    have h0 : cball r ∈ 𝓝 ((0 : Fin (n + 1) → k) (Fin.last n)) := by simpa using cball_mem_nhds r
    exact (continuous_apply (Fin.last n)).continuousAt h0
  obtain ⟨t₀, ht₀⟩ := exists_box_subset (Filter.inter_mem hΩ₁ hΩ₂)
  refine ⟨t₀, fun t ht => ?_⟩
  have hDM : box (n + 1) t₀ ≤ box (n + 1) t := fun x hx j =>
    show valuation k (x j) ≤ valuation k (t : k) from
      le_trans (show valuation k (x j) ≤ valuation k (t₀ : k) from hx j) ht
  have hDo : IsOpen (box (n + 1) t₀ : Set (Fin (n + 1) → k)) :=
    AddSubgroup.isOpen_of_mem_nhds _ (g := 0) (box_mem_nhds (n + 1) t₀)
  obtain ⟨S, hSM, hS⟩ := GlobalTheory.CompanionTheory.OpenSubgroupCosets.exists_finset_unique_coset_reps
    (box (n + 1) t₀) hDo (box (n + 1) t : Set (Fin (n + 1) → k)) (isCompact_box (n + 1) t)
  have hfin : piHaar ν (n + 1) (box (n + 1) t₀ : Set (Fin (n + 1) → k)) ≠ ⊤ :=
    (isCompact_box (n + 1) t₀).measure_lt_top.ne
  have hpos : piHaar ν (n + 1) (box (n + 1) t₀ : Set (Fin (n + 1) → k)) ≠ 0 :=
    hDo.measure_ne_zero _ ⟨0, (box (n + 1) t₀).zero_mem⟩
  have hvol : ((piHaar ν (n + 1)).real (box (n + 1) t₀ : Set (Fin (n + 1) → k)) : ℝ) ≠ 0 :=
    (ENNReal.toReal_pos hpos hfin).ne'
  have hcard : (S.card : ℂ) ≠ 0 := by
    obtain ⟨s, ⟨hs, -⟩, -⟩ := hS 0 (box (n + 1) t).zero_mem
    exact Nat.cast_ne_zero.2 (Finset.card_ne_zero_of_mem hs)
  set v₁ : V := ∑ s ∈ S, wt ψ n s • T (uM (n + 1) s) v with hv₁
  have hv₁0 : v₁ ≠ 0 := by
    intro h0
    have h := avg_sub_mem_twKer ψ T S v
    rw [← hv₁, h0, zero_sub, neg_mem_iff] at h
    exact hv ((Submodule.smul_mem_iff _ hcard).1 h)
  obtain ⟨v', hv'⟩ := hB v₁ hv₁0
  refine ⟨v', ?_⟩
  have hJ : JJ ν ψ T B (box (n + 1) t : Set (Fin (n + 1) → k)) v v' =
      (((piHaar ν (n + 1)).real (box (n + 1) t₀ : Set (Fin (n + 1) → k)) : ℝ) : ℂ) * B v₁ v' := by
    rw [JJ, setIntegral_eq_sum_reps (piHaar ν (n + 1)) (box (n + 1) t₀) (box (n + 1) t) hDo.measurableSet hfin hDM S
      hSM hS _ fun x d hd => integrand_add ψ T B v v' x d (ht₀ hd).1 (hr _ (ht₀ hd).2)]
    simp only [hv₁, map_sum, LinearMap.sum_apply, map_smul, LinearMap.smul_apply, smul_eq_mul, coef]
  rw [hJ]
  exact mul_ne_zero (Complex.ofReal_ne_zero.2 hvol) hv'

end GlobalTheory.CompanionTheory.MirPair.AvgBox

end

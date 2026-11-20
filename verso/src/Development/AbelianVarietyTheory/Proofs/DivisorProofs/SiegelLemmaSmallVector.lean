import Mathlib
import ReciprocityTheory.GeometryOfNumbers.LatticeCovolumes.ArakelovDegreeEqDegreeOfFamily
import ReciprocityTheory.SemistableReduction.SemiDegCA
open NumberField ReciprocityTheory.GeometryOfNumbersTheory
open scoped ComplexOrder

namespace GlobalTheory.SlopeStep

/- English proof (translation)
Use `set M := h.gram σ v with hM`. Use `set c : Fin (n + 1) → ℂ := fun a => M.adjugate a (Fin.last n) with hc`. Establish `hMc : ∀ a, ∑ b, M a b * c b = if a = Fin.last n then M.det else 0`. Introduce `a`. Use `congrFun (congrFun (Matrix.mul_adjugate M) a) (Fin.last n)` as an intermediate fact.

Rewrite `this` using `[Matrix.mul_apply]`. Rewrite using `[this]`. Simplify using `[Matrix.one_apply]`. Establish `hclast : c (Fin.last n) = (h.gram σ (fun a : Fin n => v a.castSucc)).det`. Rewrite using `[hc]`.

Simplify using `only`. Rewrite using `[Matrix.adjugate_fin_succ_eq_det_submatrix]`. Simplify using `[Fin.succAbove_last]`. Both sides reduce to the same expression. Use `set D := (h.gram σ (fun a : Fin n => v a.castSucc)).det with hDdef`.

Establish `hG : 0 < D` using `(h.posDef σ n (fun a : Fin n => v a.castSucc) (hli.comp _ (Fin.castSucc_injective n))).det_pos`. Rewrite `hG` using `[Complex.pos_iff]`. Establish `hq : (∑ a, ∑ b, starRingEnd ℂ (c a) * c b * h.form σ (v a) (v b)) = starRingEnd ℂ (c (Fin.last n)) * M.det`. Establish `: ∀ a, ∑ b, starRingEnd ℂ (c a) * c b * h.form σ (v a) (v b) = starRingEnd ℂ (c a) * (if a = Fin.last n then M.det else 0)`. Introduce `a`.

Rewrite using `[← hMc a, Finset.mul_sum]`. Use `Finset.sum_congr rfl fun b _ => ?_` and prove the remaining obligations. Simplify using `[hM, HermFam.gram]`. Expand and normalize the polynomial expressions, which then agree. Repeatedly rewrite using `[this]`.

Simplify using the standard rewrite rules. Establish `hl : ∑ a, c a * φ a = c (Fin.last n) * φ (Fin.last n)`. Rewrite using `[Fin.sum_univ_castSucc]`. Simplify using `[hφ]`. Establish `key` using `hB c`.

Rewrite `key` using `[hl, hq, hclast]`. Establish `hn : ‖D * φ (Fin.last n)‖ ^ 2 = D.re ^ 2 * ‖φ (Fin.last n)‖ ^ 2`. Rewrite using `[norm_mul, mul_pow, Complex.sq_norm, Complex.normSq_apply, ← hG.2]`. Expand and normalize the polynomial expressions, which then agree. Establish `hr : (starRingEnd ℂ D * M.det).re = D.re * M.det.re`.

Simplify using `[Complex.mul_re, ← hG.2]`. Rewrite `key` using `[hn, hr]`. Establish `hpos` using `hG.1`. Use polynomial arithmetic with `[key, hpos]`.
-/
theorem gram_last_bound {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    (h : HermFam K V) (σ : K →+* ℂ) {n : ℕ} (v : Fin (n + 1) → V)
    (hli : LinearIndependent K v) (φ : Fin (n + 1) → ℂ) (hφ : ∀ a : Fin n, φ a.castSucc = 0)
    (B : ℝ)
    (hB : ∀ c : Fin (n + 1) → ℂ, ‖∑ a, c a * φ a‖ ^ 2 ≤
      B ^ 2 * (∑ a, ∑ b, starRingEnd ℂ (c a) * c b * h.form σ (v a) (v b)).re) :
    ‖φ (Fin.last n)‖ ^ 2 * (h.gram σ (fun a : Fin n => v a.castSucc)).det.re ≤
      B ^ 2 * (h.gram σ v).det.re := by
  set M := h.gram σ v with hM
  set c : Fin (n + 1) → ℂ := fun a => M.adjugate a (Fin.last n) with hc
  have hMc : ∀ a, ∑ b, M a b * c b = if a = Fin.last n then M.det else 0 := by
    intro a
    have := congrFun (congrFun (Matrix.mul_adjugate M) a) (Fin.last n)
    rw [Matrix.mul_apply] at this
    rw [this]
    simp [Matrix.one_apply]
  have hclast : c (Fin.last n) = (h.gram σ (fun a : Fin n => v a.castSucc)).det := by
    rw [hc]
    simp only
    rw [Matrix.adjugate_fin_succ_eq_det_submatrix]
    simp [Fin.succAbove_last]
    rfl
  set D := (h.gram σ (fun a : Fin n => v a.castSucc)).det with hDdef
  have hG : 0 < D := (h.posDef σ n (fun a : Fin n => v a.castSucc)
    (hli.comp _ (Fin.castSucc_injective n))).det_pos
  rw [Complex.pos_iff] at hG
  have hq : (∑ a, ∑ b, starRingEnd ℂ (c a) * c b * h.form σ (v a) (v b)) =
      starRingEnd ℂ (c (Fin.last n)) * M.det := by
    have : ∀ a, ∑ b, starRingEnd ℂ (c a) * c b * h.form σ (v a) (v b) =
        starRingEnd ℂ (c a) * (if a = Fin.last n then M.det else 0) := by
      intro a
      rw [← hMc a, Finset.mul_sum]
      refine Finset.sum_congr rfl fun b _ => ?_
      simp [hM, HermFam.gram]
      ring
    simp_rw [this]
    simp
  have hl : ∑ a, c a * φ a = c (Fin.last n) * φ (Fin.last n) := by
    rw [Fin.sum_univ_castSucc]
    simp [hφ]
  have key := hB c
  rw [hl, hq, hclast] at key
  have hn : ‖D * φ (Fin.last n)‖ ^ 2 = D.re ^ 2 * ‖φ (Fin.last n)‖ ^ 2 := by
    rw [norm_mul, mul_pow, Complex.sq_norm, Complex.normSq_apply, ← hG.2]
    ring
  have hr : (starRingEnd ℂ D * M.det).re = D.re * M.det.re := by
    simp [Complex.mul_re, ← hG.2]
  rw [hn, hr] at key
  have hpos := hG.1
  nlinarith [key, hpos]

/- English proof (translation)
Introduce `K _ _ r hE E V f u B hfg _hspan huE huV hfu hBpos hB`. Use `set EV := E ⊓ V.restrictScalars (𝓞 K) with hEV`. Use `set EW := E ⊓ (V ⊓ LinearMap.ker f).restrictScalars (𝓞 K) with hEW`. Establish `hnoeth : IsNoetherian (𝓞 K) E` using `isNoetherian_of_fg_of_noetherian E hfg`. Establish `hsubfg : ∀ N : Submodule (𝓞 K) (Fin r → K), N ≤ E → N.FG`.

Introduce `N hN`. Establish `h1 : (N.comap E.subtype).FG` using `IsNoetherian.noetherian _`. Establish `h2` using `h1.map E.subtype`. Rewrite `h2` using `[Submodule.map_comap_eq, Submodule.range_subtype, inf_of_le_right hN]`. Then use the resulting hypothesis. Establish `hEVfg : EV.FG` using `hsubfg EV inf_le_left`.

Establish `hEWfg : EW.FG` using `hsubfg EW inf_le_left`. Establish `hWV : EW ≤ EV` using `fun x hx => ⟨hx.1, hx.2.1⟩`. Take `⟨n, w, hw⟩ : ∃ n : ℕ, ∃ w : Fin n → Fin r → K, IsFrame K EW w` from `⟨_, exists_isFrame EW hEWfg⟩`. Use `set v : Fin (n + 1) → Fin r → K := Fin.snoc w u with hvdef`. Establish `hv_cs : ∀ a : Fin n, v a.castSucc = w a` using `fun a => by simp [hvdef]`.

Establish `hv_last : v (Fin.last n) = u` using `by simp [hvdef]`. Establish `hfw : ∀ a, f (w a) = 0` using `fun a => (hw.1 a).2.2`. Establish `hfspan : ∀ x ∈ Submodule.span K (Set.range w), f x = 0`. Introduce `x hx`. Establish `: Submodule.span K (Set.range w) ≤ LinearMap.ker f` using `Submodule.span_le.mpr (by rintro _ ⟨a, rfl⟩; exact hfw a)`.

Conclude with `this hx`. Establish `hvV : ∀ a, v a ∈ V`. Introduce `a`. Proceed by induction on `a using Fin.lastCases with`. Consider the case `last => rw [hv_last]`.

Conclude with `huV`. Consider the case `cast a => rw [hv_cs]`. Conclude with `(hw.1 a).2.1`. Establish `hvli : LinearIndependent K v`. Rewrite using `[hvdef, linearIndependent_fin_snoc]`.

Conclude with `⟨hw.2.1, fun hu => hfu (hfspan u hu)⟩`. Establish `hvfr : IsFrame K EV v`. Use `⟨?_, hvli, ?_⟩` and prove the remaining obligations. Introduce `a`. Proceed by induction on `a using Fin.lastCases with`.

Consider the case `last => rw [hv_last]`. Conclude with `⟨huE, huV⟩`. Consider the case `cast a => rw [hv_cs]`. Conclude with `hWV (hw.1 a)`. Introduce `x hx`.

Take `⟨a, b, hb, hab⟩` from `IsFractionRing.div_surjective (A := 𝓞 K) (f x / f u)`. Establish `hb0 : (algebraMap (𝓞 K) K b) ≠ 0`. Rewrite using `[ne_eq, map_eq_zero_iff _ (FaithfulSMul.algebraMap_injective (𝓞 K) K)]`. Conclude with `nonZeroDivisors.ne_zero hb`. Use `set z := b • x - a • u with hz`.

Establish `hzK : z = (algebraMap (𝓞 K) K b) • x - (algebraMap (𝓞 K) K a) • u`. Rewrite using `[hz, algebraMap_smul, algebraMap_smul]`. Establish `hzEW : z ∈ EW`. Use `⟨E.sub_mem (E.smul_mem b hx.1) (E.smul_mem a huE), ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[hzK]`.

Conclude with `V.sub_mem (V.smul_mem _ hx.2) (V.smul_mem _ huV)`. Use `show f z = 0`. Rewrite using `[hzK, map_sub, map_smul, map_smul, smul_eq_mul, smul_eq_mul]`. Establish `: algebraMap (𝓞 K) K a = f x / f u * algebraMap (𝓞 K) K b`. Rewrite using `[← hab]`.

Clear the denominators using the available nonvanishing facts. Rewrite using `[this]`. Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree. Establish `hspW : Submodule.span K (Set.range w) ≤ Submodule.span K (Set.range v)` using `Submodule.span_mono (by rintro _ ⟨a, rfl⟩; exact ⟨a.castSucc, hv_cs a⟩)`.

Establish `hzs : z ∈ Submodule.span K (Set.range v)` using `hspW (hw.2.2 hzEW)`. Establish `hus : u ∈ Submodule.span K (Set.range v)` using `Submodule.subset_span ⟨Fin.last n, hv_last⟩`. Establish `hx' : x = (algebraMap (𝓞 K) K b)⁻¹ • (z + (algebraMap (𝓞 K) K a) • u)`. Rewrite using `[hzK, sub_add_cancel, smul_smul, inv_mul_cancel₀ hb0, one_smul]`. Rewrite using `[SetLike.mem_coe, hx']`.

Conclude with `Submodule.smul_mem _ _ (Submodule.add_mem _ hzs (Submodule.smul_mem _ _ hus))`. Establish `hle : Submodule.span (𝓞 K) (Set.range v) ≤ EV` using `Submodule.span_le.mpr (by rintro _ ⟨a, rfl⟩; exact hvfr.1 a)`. Establish `hfcomb : ∀ c : Fin (n + 1) → 𝓞 K, f (∑ i, c i • v i) = c (Fin.last n) • f u`. Introduce `c`. Rewrite using `[map_sum]`.

Repeatedly rewrite using `[LinearMap.map_smul_of_tower]`. Rewrite using `[Fin.sum_univ_castSucc]`. Simplify using `[hv_cs, hfw, hv_last]`. Establish `hidx : (Submodule.span (𝓞 K) (Set.range v)).toAddSubgroup.relIndex EV.toAddSubgroup = (Submodule.span (𝓞 K) {f u}).toAddSubgroup.relIndex (EV.map (f.restrictScalars (𝓞 K))).toAddSubgroup * (Submodule.span (𝓞 K) (Set.range w)).toAddSubgroup.relIndex EW.toAddSubgroup`. Rewrite using `[ReciprocityTheory.MultiplicativeHeights.SemiDegIdx.relIndex_eq_map_mul_ker (f.restrictScalars (𝓞 K)).toAddMonoidHom (Submodule.toAddSubgroup_mono hle)]`.

Use `congr 1`. Use `congr 1`. Use extensionality with `y`. Simplify using `only [AddSubgroup.mem_map, Submodule.mem_toAddSubgroup]`. Prove the components needed by the constructor for the conclusion.

Introduce and unpack `⟨x, hx, rfl⟩`. Take `⟨c, rfl⟩` from `(Submodule.mem_span_range_iff_exists_fun (𝓞 K)).mp hx`. Rewrite using `[Submodule.mem_span_singleton]`. Conclude with `⟨c (Fin.last n), by simpa using (hfcomb c).symm⟩`. Introduce `hy`.

Take `⟨a, rfl⟩` from `Submodule.mem_span_singleton.mp hy`. Use `⟨a • u, Submodule.smul_mem _ _ (Submodule.subset_span ⟨Fin.last n, hv_last⟩), ?_⟩` and prove the remaining obligations. Simplify using the standard rewrite rules. Use `congr 1`. Use extensionality with `x`.

Simplify using `only [AddSubgroup.mem_inf, Submodule.mem_toAddSubgroup, AddMonoidHom.mem_ker]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨hx, hfx⟩`. Take `⟨c, rfl⟩` from `(Submodule.mem_span_range_iff_exists_fun (𝓞 K)).mp hx`. Establish `h0 : c (Fin.last n) • f u = 0` using `by rw [← hfcomb c]; simpa using hfx`.

Establish `hc0 : c (Fin.last n) = 0`. Rewrite `h0` using `[← algebraMap_smul K, smul_eq_mul, mul_eq_zero]`. Break down `h0 with h0 | h0` into its components or cases. Conclude with `(map_eq_zero_iff _ (FaithfulSMul.algebraMap_injective (𝓞 K) K)).mp h0`. Conclude with `absurd h0 hfu`.

Rewrite using `[Fin.sum_univ_castSucc, hc0, zero_smul, add_zero]`. Conclude with `Submodule.sum_mem _ fun a _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨a, (hv_cs a).symm⟩)`. Introduce `hx`. Use `⟨Submodule.span_mono (by rintro _ ⟨a, rfl⟩; exact ⟨a.castSucc, hv_cs a⟩) hx, ?_⟩` and prove the remaining obligations. Use `hfspan _ (Submodule.span_le_restrictScalars (𝓞 K) K _ hx)` as an intermediate fact.

Simplify using `using this`. Use extensionality with `x`. Simplify using `[hEV, hEW, and_assoc]`. Establish `hne` using `hvfr.relIndex_ne_zero hEVfg`. Rewrite `hne` using `[hidx]`.

Take `⟨hne1, hne2⟩` from `mul_ne_zero_iff.mp hne`. Establish `hs : ∀ σ : K →+* ℂ, Real.log ‖σ (f u)‖ + (1 / 2) * Real.log (hE.gram σ w).det.re ≤ Real.log (B σ) + (1 / 2) * Real.log (hE.gram σ v).det.re`. Introduce `σ`. Establish `key` using `gram_last_bound hE σ v hvli (fun a => σ (f (v a))) (by intro a; simp [hv_cs, hfw]) (B σ) (fun c => hB σ (n + 1) v c hvV)`. Establish `hw' : (fun a : Fin n => v a.castSucc) = w` using `funext hv_cs`.

Simplify using `only [hv_last, hw'] at key`. Establish `h1 : 0 < ‖σ (f u)‖` using `norm_pos_iff.mpr ((map_ne_zero σ).mpr hfu)`. Establish `h2` using `hE.ds_gram_det_re_pos σ hw.2.1`. Establish `h3` using `hE.ds_gram_det_re_pos σ hvli`. Establish `h4` using `hBpos σ`.

Establish `hl` using `Real.log_le_log (by positivity) key`. Rewrite `hl` using `[Real.log_mul (by positivity) h2.ne', Real.log_mul (by positivity) h3.ne', Real.log_pow, Real.log_pow]`. Move the coercions through the operations in `at hl`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hsum` using `Finset.sum_le_sum (fun σ (_ : σ ∈ (Finset.univ : Finset (K →+* ℂ))) => hs σ)`.

Rewrite `hsum` using `[Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]`. Establish `hd : (0 : ℝ) < Module.finrank ℚ K` using `Nat.cast_pos.mpr Module.finrank_pos`. Rewrite using `[arakelovDegree_eq_degreeOfFamily hE hEVfg hvfr, arakelovDegree_eq_degreeOfFamily hE hEWfg hw]`. Unfold `degreeOfFamily`. Rewrite using `[hidx, Nat.cast_mul, Real.log_mul (by exact_mod_cast hne1) (by exact_mod_cast hne2), div_sub_div_same, div_le_div_iff_of_pos_right hd]`.

Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem slope_step : ∀ (K : Type) [Field K] [NumberField K] (r : ℕ) (hE : HermFam K (Fin r → K)) (E : Submodule (𝓞 K) (Fin r → K)) (V : Submodule K (Fin r → K)) (f : (Fin r → K) →ₗ[K] K) (u : Fin r → K) (B : (K →+* ℂ) → ℝ), E.FG → Submodule.span K (E : Set (Fin r → K)) = ⊤ → u ∈ E → u ∈ V → f u ≠ 0 → (∀ σ, 0 < B σ) → (∀ (σ : K →+* ℂ) (q : ℕ) (v : Fin q → Fin r → K) (c : Fin q → ℂ), (∀ a, v a ∈ V) → ‖∑ a, c a * σ (f (v a))‖ ^ 2 ≤ B σ ^ 2 * (∑ a, ∑ b, starRingEnd ℂ (c a) * c b * hE.form σ (v a) (v b)).re) → deg hE (E ⊓ V.restrictScalars (𝓞 K)) - deg hE (E ⊓ (V ⊓ LinearMap.ker f).restrictScalars (𝓞 K)) ≤ (Real.log ((Submodule.span (𝓞 K) {f u}).toAddSubgroup.relIndex ((E ⊓ V.restrictScalars (𝓞 K)).map (f.restrictScalars (𝓞 K))).toAddSubgroup : ℝ) - ∑ σ : K →+* ℂ, Real.log ‖σ (f u)‖ + ∑ σ : K →+* ℂ, Real.log (B σ)) / Module.finrank ℚ K := by
  intro K _ _ r hE E V f u B hfg _hspan huE huV hfu hBpos hB
  set EV := E ⊓ V.restrictScalars (𝓞 K) with hEV
  set EW := E ⊓ (V ⊓ LinearMap.ker f).restrictScalars (𝓞 K) with hEW
  have hnoeth : IsNoetherian (𝓞 K) E := isNoetherian_of_fg_of_noetherian E hfg
  have hsubfg : ∀ N : Submodule (𝓞 K) (Fin r → K), N ≤ E → N.FG := by
    intro N hN
    have h1 : (N.comap E.subtype).FG := IsNoetherian.noetherian _
    have h2 := h1.map E.subtype
    rwa [Submodule.map_comap_eq, Submodule.range_subtype, inf_of_le_right hN] at h2
  have hEVfg : EV.FG := hsubfg EV inf_le_left
  have hEWfg : EW.FG := hsubfg EW inf_le_left
  have hWV : EW ≤ EV := fun x hx => ⟨hx.1, hx.2.1⟩
  obtain ⟨n, w, hw⟩ : ∃ n : ℕ, ∃ w : Fin n → Fin r → K, IsFrame K EW w :=
    ⟨_, exists_isFrame EW hEWfg⟩
  set v : Fin (n + 1) → Fin r → K := Fin.snoc w u with hvdef
  have hv_cs : ∀ a : Fin n, v a.castSucc = w a := fun a => by simp [hvdef]
  have hv_last : v (Fin.last n) = u := by simp [hvdef]
  have hfw : ∀ a, f (w a) = 0 := fun a => (hw.1 a).2.2
  have hfspan : ∀ x ∈ Submodule.span K (Set.range w), f x = 0 := by
    intro x hx
    have : Submodule.span K (Set.range w) ≤ LinearMap.ker f :=
      Submodule.span_le.mpr (by rintro _ ⟨a, rfl⟩; exact hfw a)
    exact this hx
  have hvV : ∀ a, v a ∈ V := by
    intro a
    induction a using Fin.lastCases with
    | last => rw [hv_last]; exact huV
    | cast a => rw [hv_cs]; exact (hw.1 a).2.1
  have hvli : LinearIndependent K v := by
    rw [hvdef, linearIndependent_fin_snoc]
    exact ⟨hw.2.1, fun hu => hfu (hfspan u hu)⟩
  have hvfr : IsFrame K EV v := by
    refine ⟨?_, hvli, ?_⟩
    · intro a
      induction a using Fin.lastCases with
      | last => rw [hv_last]; exact ⟨huE, huV⟩
      | cast a => rw [hv_cs]; exact hWV (hw.1 a)
    · intro x hx
      obtain ⟨a, b, hb, hab⟩ := IsFractionRing.div_surjective (A := 𝓞 K) (f x / f u)
      have hb0 : (algebraMap (𝓞 K) K b) ≠ 0 := by
        rw [ne_eq, map_eq_zero_iff _ (FaithfulSMul.algebraMap_injective (𝓞 K) K)]
        exact nonZeroDivisors.ne_zero hb
      set z := b • x - a • u with hz
      have hzK : z = (algebraMap (𝓞 K) K b) • x - (algebraMap (𝓞 K) K a) • u := by
        rw [hz, algebraMap_smul, algebraMap_smul]
      have hzEW : z ∈ EW := by
        refine ⟨E.sub_mem (E.smul_mem b hx.1) (E.smul_mem a huE), ?_, ?_⟩
        · rw [hzK]; exact V.sub_mem (V.smul_mem _ hx.2) (V.smul_mem _ huV)
        · show f z = 0
          rw [hzK, map_sub, map_smul, map_smul, smul_eq_mul, smul_eq_mul]
          have : algebraMap (𝓞 K) K a = f x / f u * algebraMap (𝓞 K) K b := by
            rw [← hab]; field_simp
          rw [this]; field_simp; ring
      have hspW : Submodule.span K (Set.range w) ≤ Submodule.span K (Set.range v) :=
        Submodule.span_mono (by rintro _ ⟨a, rfl⟩; exact ⟨a.castSucc, hv_cs a⟩)
      have hzs : z ∈ Submodule.span K (Set.range v) := hspW (hw.2.2 hzEW)
      have hus : u ∈ Submodule.span K (Set.range v) := Submodule.subset_span ⟨Fin.last n, hv_last⟩
      have hx' : x = (algebraMap (𝓞 K) K b)⁻¹ • (z + (algebraMap (𝓞 K) K a) • u) := by
        rw [hzK, sub_add_cancel, smul_smul, inv_mul_cancel₀ hb0, one_smul]
      rw [SetLike.mem_coe, hx']
      exact Submodule.smul_mem _ _ (Submodule.add_mem _ hzs (Submodule.smul_mem _ _ hus))
  have hle : Submodule.span (𝓞 K) (Set.range v) ≤ EV :=
    Submodule.span_le.mpr (by rintro _ ⟨a, rfl⟩; exact hvfr.1 a)
  have hfcomb : ∀ c : Fin (n + 1) → 𝓞 K, f (∑ i, c i • v i) = c (Fin.last n) • f u := by
    intro c
    rw [map_sum]
    simp_rw [LinearMap.map_smul_of_tower]
    rw [Fin.sum_univ_castSucc]
    simp [hv_cs, hfw, hv_last]
  have hidx : (Submodule.span (𝓞 K) (Set.range v)).toAddSubgroup.relIndex EV.toAddSubgroup =
      (Submodule.span (𝓞 K) {f u}).toAddSubgroup.relIndex
        (EV.map (f.restrictScalars (𝓞 K))).toAddSubgroup *
      (Submodule.span (𝓞 K) (Set.range w)).toAddSubgroup.relIndex EW.toAddSubgroup := by
    rw [ReciprocityTheory.MultiplicativeHeights.SemiDegIdx.relIndex_eq_map_mul_ker (f.restrictScalars (𝓞 K)).toAddMonoidHom
      (Submodule.toAddSubgroup_mono hle)]
    congr 1
    · congr 1
      · ext y
        simp only [AddSubgroup.mem_map, Submodule.mem_toAddSubgroup]
        constructor
        · rintro ⟨x, hx, rfl⟩
          obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun (𝓞 K)).mp hx
          rw [Submodule.mem_span_singleton]
          exact ⟨c (Fin.last n), by simpa using (hfcomb c).symm⟩
        · intro hy
          obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hy
          refine ⟨a • u, Submodule.smul_mem _ _ (Submodule.subset_span ⟨Fin.last n, hv_last⟩), ?_⟩
          simp
    · congr 1
      · ext x
        simp only [AddSubgroup.mem_inf, Submodule.mem_toAddSubgroup, AddMonoidHom.mem_ker]
        constructor
        · rintro ⟨hx, hfx⟩
          obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun (𝓞 K)).mp hx
          have h0 : c (Fin.last n) • f u = 0 := by rw [← hfcomb c]; simpa using hfx
          have hc0 : c (Fin.last n) = 0 := by
            rw [← algebraMap_smul K, smul_eq_mul, mul_eq_zero] at h0
            rcases h0 with h0 | h0
            · exact (map_eq_zero_iff _ (FaithfulSMul.algebraMap_injective (𝓞 K) K)).mp h0
            · exact absurd h0 hfu
          rw [Fin.sum_univ_castSucc, hc0, zero_smul, add_zero]
          exact Submodule.sum_mem _ fun a _ => Submodule.smul_mem _ _
            (Submodule.subset_span ⟨a, (hv_cs a).symm⟩)
        · intro hx
          refine ⟨Submodule.span_mono (by rintro _ ⟨a, rfl⟩; exact ⟨a.castSucc, hv_cs a⟩) hx, ?_⟩
          have := hfspan _ (Submodule.span_le_restrictScalars (𝓞 K) K _ hx)
          simpa using this
      · ext x
        simp [hEV, hEW, and_assoc]
  have hne := hvfr.relIndex_ne_zero hEVfg
  rw [hidx] at hne
  obtain ⟨hne1, hne2⟩ := mul_ne_zero_iff.mp hne
  have hs : ∀ σ : K →+* ℂ, Real.log ‖σ (f u)‖ + (1 / 2) * Real.log (hE.gram σ w).det.re ≤
      Real.log (B σ) + (1 / 2) * Real.log (hE.gram σ v).det.re := by
    intro σ
    have key := gram_last_bound hE σ v hvli (fun a => σ (f (v a))) (by intro a; simp [hv_cs, hfw])
      (B σ) (fun c => hB σ (n + 1) v c hvV)
    have hw' : (fun a : Fin n => v a.castSucc) = w := funext hv_cs
    simp only [hv_last, hw'] at key
    have h1 : 0 < ‖σ (f u)‖ := norm_pos_iff.mpr ((map_ne_zero σ).mpr hfu)
    have h2 := hE.ds_gram_det_re_pos σ hw.2.1
    have h3 := hE.ds_gram_det_re_pos σ hvli
    have h4 := hBpos σ
    have hl := Real.log_le_log (by positivity) key
    rw [Real.log_mul (by positivity) h2.ne', Real.log_mul (by positivity) h3.ne',
      Real.log_pow, Real.log_pow] at hl
    push_cast at hl
    linarith
  have hsum := Finset.sum_le_sum (fun σ (_ : σ ∈ (Finset.univ : Finset (K →+* ℂ))) => hs σ)
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum] at hsum
  have hd : (0 : ℝ) < Module.finrank ℚ K := Nat.cast_pos.mpr Module.finrank_pos
  rw [arakelovDegree_eq_degreeOfFamily hE hEVfg hvfr, arakelovDegree_eq_degreeOfFamily hE hEWfg hw]
  unfold degreeOfFamily
  rw [hidx, Nat.cast_mul, Real.log_mul (by exact_mod_cast hne1) (by exact_mod_cast hne2),
    div_sub_div_same, div_le_div_iff_of_pos_right hd]
  linarith

end GlobalTheory.SlopeStep

import ReciprocityTheory.SemistableReduction.LatSemiSt
import Lemmata.GeneralBFactSecond.Imports

namespace ReciprocityTheory.MultiplicativeHeights

open Matrix NumberField Module

/- English proof (translation)
Apply the tactic sequence `first | exact Bl.general_b_fact_second.goal1 .. | (apply Bl.general_b_fact_second.goal1 <;> assumption) | (intros; apply Bl.general_b_fact_second.goal1 <;> assumption)`.
-/
theorem sc_scale {K : Type} [Field K] [NumberField K] {r : ℕ} (L : Submodule (𝓞 K) (Fin r → K))
    (hL : Submodule.span K (L : Set (Fin r → K)) = ⊤) (x : Fin r → K) :
    ∃ d : 𝓞 K, d ≠ 0 ∧ d • x ∈ L := by
  first | exact Bl.general_b_fact_second.goal1 .. | (apply Bl.general_b_fact_second.goal1 <;> assumption) | (intros; apply Bl.general_b_fact_second.goal1 <;> assumption)

/- English proof (translation)
Use `hv.units_smul (fun i => Units.mk0 (a i) (ha i))` as an intermediate fact. Use `this using 1` and compare the differences between its conclusion and the goal. Use function extensionality and compare the values at `i`. Simplify using `[Units.smul_def]`.
-/
theorem sc_li_scale {K V ι : Type*} [Field K] [AddCommGroup V] [Module K V] {v : ι → V}
    (hv : LinearIndependent K v) (a : ι → K) (ha : ∀ i, a i ≠ 0) :
    LinearIndependent K (fun i => a i • v i) := by
  have := hv.units_smul (fun i => Units.mk0 (a i) (ha i))
  convert this using 1
  funext i
  simp [Units.smul_def]

/- English proof (translation)
Use `set b0 := Module.finBasis K (LinearMap.ker N.mulVecLin)`. Use `choose d hd0 hdL using fun i => sc_scale L hL (b0 i : Fin r → K)`. Establish `hinj` using `FaithfulSMul.algebraMap_injective (𝓞 K) K`. Establish `ha : ∀ i, algebraMap (𝓞 K) K (d i) ≠ 0` using `fun i h => hd0 i (hinj (by rw [h, map_zero]))`. Use `⟨fun i => algebraMap (𝓞 K) K (d i) • (b0 i : Fin r → K), fun i => ?_, fun i => ?_, ?_, ?_⟩` and prove the remaining obligations.

Use `show algebraMap (𝓞 K) K (d i) • (b0 i : Fin r → K) ∈ L`. Rewrite using `[algebraMap_smul]`. Conclude with `hdL i`. Establish `h` using `(b0 i).2`. Rewrite `h` using `[LinearMap.mem_ker, Matrix.mulVecLin_apply]`.

Rewrite using `[mulVec_smul, h, smul_zero]`. Conclude with `sc_li_scale (b0.linearIndependent.map' _ (Submodule.ker_subtype _)) _ ha`. Introduce `y hy`. Establish `hy' : y ∈ LinearMap.ker N.mulVecLin`. Rewrite using `[LinearMap.mem_ker, Matrix.mulVecLin_apply]`.

Conclude with `hy`. Establish `hsum` using `b0.sum_repr ⟨y, hy'⟩`. Establish `hsum' : y = ∑ i, b0.repr ⟨y, hy'⟩ i • (b0 i : Fin r → K)`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[hsum]`.

Use `_ = _ := by rw [Submodule.coe_sum]; simp only [Submodule.coe_smul]`. Rewrite using `[hsum']`. Use `Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ ?_` and prove the remaining obligations. Establish `hb : (b0 i : Fin r → K) = (algebraMap (𝓞 K) K (d i))⁻¹ • (algebraMap (𝓞 K) K (d i) • (b0 i : Fin r → K))`. Rewrite using `[inv_smul_smul₀ (ha i)]`.

Rewrite using `[hb]`. Conclude with `Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)`.
-/
theorem sc_kerfam {K : Type} [Field K] [NumberField K] {r : ℕ} (L : Submodule (𝓞 K) (Fin r → K))
    (hL : Submodule.span K (L : Set (Fin r → K)) = ⊤) (N : Matrix (Fin r) (Fin r) K) :
    ∃ b : Fin (finrank K (LinearMap.ker N.mulVecLin)) → Fin r → K,
      (∀ i, b i ∈ L) ∧ (∀ i, N *ᵥ b i = 0) ∧ LinearIndependent K b ∧
      ∀ y, N *ᵥ y = 0 → y ∈ Submodule.span K (Set.range b) := by
  set b0 := Module.finBasis K (LinearMap.ker N.mulVecLin)
  choose d hd0 hdL using fun i => sc_scale L hL (b0 i : Fin r → K)
  have hinj := FaithfulSMul.algebraMap_injective (𝓞 K) K
  have ha : ∀ i, algebraMap (𝓞 K) K (d i) ≠ 0 := fun i h =>
    hd0 i (hinj (by rw [h, map_zero]))
  refine ⟨fun i => algebraMap (𝓞 K) K (d i) • (b0 i : Fin r → K), fun i => ?_, fun i => ?_, ?_, ?_⟩
  · show algebraMap (𝓞 K) K (d i) • (b0 i : Fin r → K) ∈ L
    rw [algebraMap_smul]; exact hdL i
  · have h := (b0 i).2
    rw [LinearMap.mem_ker, Matrix.mulVecLin_apply] at h
    rw [mulVec_smul, h, smul_zero]
  · exact sc_li_scale (b0.linearIndependent.map' _ (Submodule.ker_subtype _)) _ ha
  · intro y hy
    have hy' : y ∈ LinearMap.ker N.mulVecLin := by
      rw [LinearMap.mem_ker, Matrix.mulVecLin_apply]; exact hy
    have hsum := b0.sum_repr ⟨y, hy'⟩
    have hsum' : y = ∑ i, b0.repr ⟨y, hy'⟩ i • (b0 i : Fin r → K) := by
      calc y = ((⟨y, hy'⟩ : LinearMap.ker N.mulVecLin) : Fin r → K) := rfl
        _ = ((∑ i, b0.repr ⟨y, hy'⟩ i • b0 i : LinearMap.ker N.mulVecLin) : Fin r → K) := by
          rw [hsum]
        _ = _ := by rw [Submodule.coe_sum]; simp only [Submodule.coe_smul]
    rw [hsum']
    refine Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ ?_
    have hb : (b0 i : Fin r → K) =
        (algebraMap (𝓞 K) K (d i))⁻¹ • (algebraMap (𝓞 K) K (d i) • (b0 i : Fin r → K)) := by
      rw [inv_smul_smul₀ (ha i)]
    rw [hb]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)

/- English proof (translation)
Use `set e := Module.finBasis K (LinearMap.range N.mulVecLin)`. Establish `hex : ∀ j, ∃ y, N *ᵥ y = (e j : Fin r → K)`. Introduce `j`. Take `⟨y, hy⟩` from `LinearMap.mem_range.mp (e j).2`. Conclude with `⟨y, by rw [← Matrix.mulVecLin_apply]; exact hy⟩`.

Use `choose y hy using hex`. Use `choose d hd0 hdL using fun j => sc_scale L hL (y j)`. Establish `hinj` using `FaithfulSMul.algebraMap_injective (𝓞 K) K`. Establish `ha : ∀ j, algebraMap (𝓞 K) K (d j) ≠ 0` using `fun j h => hd0 j (hinj (by rw [h, map_zero]))`. Use `⟨fun j => algebraMap (𝓞 K) K (d j) • y j, fun j => ?_, ?_⟩` and prove the remaining obligations.

Use `show algebraMap (𝓞 K) K (d j) • y j ∈ L`. Rewrite using `[algebraMap_smul]`. Conclude with `hdL j`. Use `sc_li_scale (e.linearIndependent.map' _ (Submodule.ker_subtype _)) _ ha` as an intermediate fact. Establish `heq : (fun j => N *ᵥ (algebraMap (𝓞 K) K (d j) • y j)) = fun j => algebraMap (𝓞 K) K (d j) • ((LinearMap.range N.mulVecLin).subtype ∘ e) j`.

Use function extensionality and compare the values at `j`. Simplify using `[mulVec_smul, hy]`. Rewrite using `[heq]`. Conclude with `this`.
-/
theorem sc_imfam {K : Type} [Field K] [NumberField K] {r : ℕ} (L : Submodule (𝓞 K) (Fin r → K))
    (hL : Submodule.span K (L : Set (Fin r → K)) = ⊤) (N : Matrix (Fin r) (Fin r) K) :
    ∃ c : Fin (finrank K (LinearMap.range N.mulVecLin)) → Fin r → K,
      (∀ j, c j ∈ L) ∧ LinearIndependent K (fun j => N *ᵥ c j) := by
  set e := Module.finBasis K (LinearMap.range N.mulVecLin)
  have hex : ∀ j, ∃ y, N *ᵥ y = (e j : Fin r → K) := by
    intro j
    obtain ⟨y, hy⟩ := LinearMap.mem_range.mp (e j).2
    exact ⟨y, by rw [← Matrix.mulVecLin_apply]; exact hy⟩
  choose y hy using hex
  choose d hd0 hdL using fun j => sc_scale L hL (y j)
  have hinj := FaithfulSMul.algebraMap_injective (𝓞 K) K
  have ha : ∀ j, algebraMap (𝓞 K) K (d j) ≠ 0 := fun j h =>
    hd0 j (hinj (by rw [h, map_zero]))
  refine ⟨fun j => algebraMap (𝓞 K) K (d j) • y j, fun j => ?_, ?_⟩
  · show algebraMap (𝓞 K) K (d j) • y j ∈ L
    rw [algebraMap_smul]; exact hdL j
  · have := sc_li_scale (e.linearIndependent.map' _ (Submodule.ker_subtype _)) _ ha
    have heq : (fun j => N *ᵥ (algebraMap (𝓞 K) K (d j) • y j)) = fun j =>
        algebraMap (𝓞 K) K (d j) • ((LinearMap.range N.mulVecLin).subtype ∘ e) j := by
      funext j; simp [mulVec_smul, hy]
    rw [heq]; exact this

/- English proof (translation)
Rewrite using `[Fintype.linearIndependent_iff]`. Introduce `g hg`. Rewrite `hg` using `[Fin.sum_univ_add]`. Simplify using `only [Fin.append_left, Fin.append_right] at hg`. Establish `h1 : ∑ j, g (Fin.natAdd k j) • (N *ᵥ c j) = 0`.

Use `congrArg N.mulVecLin hg` as an intermediate fact. Simplify `this` using `[map_add, map_sum, map_smul, Matrix.mulVecLin_apply, hbN]`. Establish `hc0` using `Fintype.linearIndependent_iff.mp hc _ h1`. Establish `hb0 : ∀ i, g (Fin.castAdd m i) = 0`. Apply `Fintype.linearIndependent_iff.mp hb` to reduce the goal to its premises.

Simplify `hg` using `[hc0]`. Introduce `i`. Conclude with `Fin.addCases (fun i => hb0 i) (fun j => hc0 j) i`.
-/
theorem sc_append_li {K : Type} [Field K] [NumberField K] {r k m : ℕ}
    (N : Matrix (Fin r) (Fin r) K) (b : Fin k → Fin r → K) (c : Fin m → Fin r → K)
    (hbN : ∀ i, N *ᵥ b i = 0) (hb : LinearIndependent K b)
    (hc : LinearIndependent K (fun j => N *ᵥ c j)) : LinearIndependent K (Fin.append b c) := by
  rw [Fintype.linearIndependent_iff]
  intro g hg
  rw [Fin.sum_univ_add] at hg
  simp only [Fin.append_left, Fin.append_right] at hg
  have h1 : ∑ j, g (Fin.natAdd k j) • (N *ᵥ c j) = 0 := by
    have := congrArg N.mulVecLin hg
    simpa [map_add, map_sum, map_smul, Matrix.mulVecLin_apply, hbN] using this
  have hc0 := Fintype.linearIndependent_iff.mp hc _ h1
  have hb0 : ∀ i, g (Fin.castAdd m i) = 0 := by
    apply Fintype.linearIndependent_iff.mp hb
    simpa [hc0] using hg
  intro i
  exact Fin.addCases (fun i => hb0 i) (fun j => hc0 j) i

/- English proof (translation)
Use `Nat.pos_of_ne_zero fun h0 => hN ?_` and prove the remaining obligations. Rewrite `h0` using `[Submodule.finrank_eq_zero, LinearMap.range_eq_bot]`. Use `LinearMap.toMatrix'_toLin' N` as an intermediate fact. Rewrite `this` using `[Matrix.toLin'_apply', h0, map_zero]`. Conclude with `this.symm`.
-/
theorem sc_rank_pos {K : Type} [Field K] [NumberField K] {r : ℕ}
    (N : Matrix (Fin r) (Fin r) K) (hN : N ≠ 0) : 0 < finrank K (LinearMap.range N.mulVecLin) := by
  refine Nat.pos_of_ne_zero fun h0 => hN ?_
  rw [Submodule.finrank_eq_zero, LinearMap.range_eq_bot] at h0
  have := LinearMap.toMatrix'_toLin' N
  rw [Matrix.toLin'_apply', h0, map_zero] at this
  exact this.symm

/- English proof (translation)
Use `set f := N.mulVecLin.restrictScalars (𝓞 K) with hf`. Establish `hfx : ∀ x, f x = N *ᵥ x` using `fun x => rfl`. Establish `hspanb : Submodule.span K (Set.range b) ≤ LinearMap.ker N.mulVecLin`. Rewrite using `[Submodule.span_le]`. Introduce and unpack `_ ⟨i, rfl⟩`.

Simplify using `[hbN i]`. Establish `hspanc : Submodule.span (𝓞 K) (Set.range c) ≤ (Submodule.span (𝓞 K) (Set.range fun j => N *ᵥ c j)).comap f`. Rewrite using `[Submodule.span_le]`. Introduce and unpack `_ ⟨j, rfl⟩`. Conclude with `Submodule.subset_span ⟨j, (hfx (c j)).symm⟩`.

Rewrite using `[Submodule.map_toAddSubgroup, ← AddSubgroup.relIndex_comap, ← AddSubgroup.inf_relIndex_right (AddSubgroup.comap _ _), ← AddSubgroup.inf_relIndex_right (Submodule.toAddSubgroup _)]`. Use `congr 1`. Use extensionality with `x`. Simplify using `only [AddSubgroup.mem_inf, AddSubgroup.mem_comap, Submodule.mem_toAddSubgroup, AddMonoidHom.coe_coe]`. Prove the components needed by the constructor for the conclusion.

Introduce and unpack `⟨hx, hxL⟩`. Use `⟨?_, hxL⟩` and prove the remaining obligations. Take `⟨a, ha⟩` from `Submodule.mem_span_range_iff_exists_fun (𝓞 K) |>.mp hx`. Use `set z := ∑ j, a j • c j with hz`. Establish `hzc : z ∈ Submodule.span (𝓞 K) (Set.range c)` using `Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)`.

Establish `hzL : z ∈ L` using `Submodule.sum_mem _ fun j _ => L.smul_mem _ (hcL j)`. Establish `hfz : f (x - z) = 0`. Rewrite using `[map_sub, hz, map_sum]`. Simplify using `only [map_smul]`. Simplify using `only [hfx] at ha ⊢`.

Rewrite using `[ha, sub_self]`. Establish `hsat : x - z ∈ satSub L b`. Use `⟨L.sub_mem hxL hzL, ?_⟩` and prove the remaining obligations. Conclude with `hker _ (by rw [← hfx]; exact hfz)`. Conclude with `Submodule.mem_sup.mpr ⟨x - z, hsat, z, hzc, sub_add_cancel x z⟩`.

Introduce and unpack `⟨hx, hxL⟩`. Use `⟨?_, hxL⟩` and prove the remaining obligations. Take `⟨y, hy, z, hz, rfl⟩` from `Submodule.mem_sup.mp hx`. Establish `hy0 : f y = 0`. Establish `h` using `hspanb hy.2`.

Rewrite `h` using `[LinearMap.mem_ker]`. Conclude with `h`. Rewrite using `[map_add, hy0, zero_add]`. Conclude with `hspanc hz`.
-/
theorem sc_index {K : Type} [Field K] [NumberField K] {r k m : ℕ}
    (L : Submodule (𝓞 K) (Fin r → K)) (N : Matrix (Fin r) (Fin r) K)
    (b : Fin k → Fin r → K) (c : Fin m → Fin r → K) (hcL : ∀ j, c j ∈ L)
    (hbN : ∀ i, N *ᵥ b i = 0) (hker : ∀ y, N *ᵥ y = 0 → y ∈ Submodule.span K (Set.range b)) :
    (Submodule.span (𝓞 K) (Set.range fun j => N *ᵥ c j)).toAddSubgroup.relIndex
        (L.map (N.mulVecLin.restrictScalars (𝓞 K))).toAddSubgroup =
      (satSub L b ⊔ Submodule.span (𝓞 K) (Set.range c)).toAddSubgroup.relIndex L.toAddSubgroup := by
  set f := N.mulVecLin.restrictScalars (𝓞 K) with hf
  have hfx : ∀ x, f x = N *ᵥ x := fun x => rfl
  have hspanb : Submodule.span K (Set.range b) ≤ LinearMap.ker N.mulVecLin := by
    rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    simp [hbN i]
  have hspanc : Submodule.span (𝓞 K) (Set.range c) ≤
      (Submodule.span (𝓞 K) (Set.range fun j => N *ᵥ c j)).comap f := by
    rw [Submodule.span_le]
    rintro _ ⟨j, rfl⟩
    exact Submodule.subset_span ⟨j, (hfx (c j)).symm⟩
  rw [Submodule.map_toAddSubgroup, ← AddSubgroup.relIndex_comap,
    ← AddSubgroup.inf_relIndex_right (AddSubgroup.comap _ _),
    ← AddSubgroup.inf_relIndex_right (Submodule.toAddSubgroup _)]
  congr 1
  ext x
  simp only [AddSubgroup.mem_inf, AddSubgroup.mem_comap, Submodule.mem_toAddSubgroup,
    AddMonoidHom.coe_coe]
  constructor
  · rintro ⟨hx, hxL⟩
    refine ⟨?_, hxL⟩
    obtain ⟨a, ha⟩ := Submodule.mem_span_range_iff_exists_fun (𝓞 K) |>.mp hx
    set z := ∑ j, a j • c j with hz
    have hzc : z ∈ Submodule.span (𝓞 K) (Set.range c) :=
      Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)
    have hzL : z ∈ L := Submodule.sum_mem _ fun j _ => L.smul_mem _ (hcL j)
    have hfz : f (x - z) = 0 := by
      rw [map_sub, hz, map_sum]
      simp only [map_smul]
      simp only [hfx] at ha ⊢
      rw [ha, sub_self]
    have hsat : x - z ∈ satSub L b := by
      refine ⟨L.sub_mem hxL hzL, ?_⟩
      exact hker _ (by rw [← hfx]; exact hfz)
    exact Submodule.mem_sup.mpr ⟨x - z, hsat, z, hzc, sub_add_cancel x z⟩
  · rintro ⟨hx, hxL⟩
    refine ⟨?_, hxL⟩
    obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.mp hx
    have hy0 : f y = 0 := by
      have h := hspanb hy.2
      rw [LinearMap.mem_ker] at h
      exact h
    rw [map_add, hy0, zero_add]
    exact hspanc hz

end ReciprocityTheory.MultiplicativeHeights

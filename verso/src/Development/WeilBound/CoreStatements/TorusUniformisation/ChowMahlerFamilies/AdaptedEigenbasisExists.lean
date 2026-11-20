import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.LinearIndependentEigProj
open AlgebraicGeometry CategoryTheory Limits NumberField GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Flat

namespace PositivityTheory.Xgn.AdaptedEigenbasis

variable {E : Type} [Field E] [NumberField E] {K W : Type} [Field K] [AddCommGroup W] [Module K W]

/- English proof (translation)
Take `⟨g, hg⟩` from `(Fintype.linearCombination K w).exists_leftInverse_of_injective (LinearMap.ker_eq_bot'.2 fun c hc => funext (Fintype.linearIndependent_iff.1 hw c hc))`. Use `⟨fun j => LinearMap.proj j ∘ₗ g, fun j j' => ?_⟩` and prove the remaining obligations. Establish `h` using `LinearMap.congr_fun hg (Pi.single j' 1)`. Simplify using `only [LinearMap.comp_apply, Fintype.linearCombination_apply_single, one_smul, LinearMap.id_apply] at h`. Simplify using `[h, Pi.single_apply]`.
-/
theorem exists_dual {q : ℕ} {w : Fin q → W} (hw : LinearIndependent K w) :
    ∃ f : Fin q → Module.Dual K W, ∀ j j', f j (w j') = if j = j' then 1 else 0 := by
  obtain ⟨g, hg⟩ := (Fintype.linearCombination K w).exists_leftInverse_of_injective
    (LinearMap.ker_eq_bot'.2 fun c hc => funext (Fintype.linearIndependent_iff.1 hw c hc))
  refine ⟨fun j => LinearMap.proj j ∘ₗ g, fun j j' => ?_⟩
  have h := LinearMap.congr_fun hg (Pi.single j' 1)
  simp only [LinearMap.comp_apply, Fintype.linearCombination_apply_single, one_smul, LinearMap.id_apply] at h
  simp [h, Pi.single_apply]

/- English proof (translation)
Simplify using `only [HT.eigProj, LinearMap.sum_apply, LinearMap.smul_apply, map_sum, map_smul, h, smul_eq_mul, ← mul_assoc]`. Rewrite using `[← Finset.sum_mul]`. Establish `: ∑ k, τ (HT.dualInt E k) * τ ((RingOfIntegers.basis E k : 𝓞 E) : E) = 1`. Rewrite using `[← map_one τ, ← HT.LatBasic.sum_dualInt_mul, map_sum]`. Simplify using the standard rewrite rules.

Rewrite using `[this, one_mul]`.
-/
theorem form_eigProj {ρ : 𝓞 E →+* Module.End K W} {τ : E →+* K} {φ : Module.Dual K W}
    (h : ∀ (b : 𝓞 E) x, φ (ρ b x) = τ (b : E) * φ x) (x : W) : φ (HT.eigProj ρ τ x) = φ x := by
  simp only [HT.eigProj, LinearMap.sum_apply, LinearMap.smul_apply, map_sum, map_smul, h, smul_eq_mul,
    ← mul_assoc]
  rw [← Finset.sum_mul]
  have : ∑ k, τ (HT.dualInt E k) * τ ((RingOfIntegers.basis E k : 𝓞 E) : E) = 1 := by
    rw [← map_one τ, ← HT.LatBasic.sum_dualInt_mul, map_sum]
    simp
  rw [this, one_mul]

/- English proof (translation)
Simplify using `only [HT.eigProj, LinearMap.sum_apply, LinearMap.smul_apply, Prod.fst_sum, Prod.smul_fst, h]`.
-/
theorem eigProj_fst {ρ : 𝓞 E →+* Module.End K W} {ρH : 𝓞 E →+* Module.End K (W × Module.Dual K W)}
    (h : ∀ a y, (ρH a y).1 = ρ a y.1) (σ : E →+* K) (y : W × Module.Dual K W) :
    (HT.eigProj ρH σ y).1 = HT.eigProj ρ σ y.1 := by
  simp only [HT.eigProj, LinearMap.sum_apply, LinearMap.smul_apply, Prod.fst_sum, Prod.smul_fst, h]

omit [NumberField E] in

/- English proof (translation)
Rewrite using `[HT.LatBasic.mem_eigSp]`. Prove the components needed by the constructor for the conclusion. Introduce `H b x`. Establish `h1` using `H (bar b)`. Rewrite `h1` using `[h, hb]`.

Rewrite using `[hσ]`. Conclude with `LinearMap.congr_fun (congrArg Prod.snd h1) x`. Introduce `H a`. Rewrite using `[h]`. Use `Prod.ext (by simp) (LinearMap.ext fun x => ?_)` and prove the remaining obligations.

Establish `h1` using `H (bar a) x`. Rewrite `h1` using `[hσ, hb]`. Conclude with `h1`.
-/
theorem inr_mem_iff {ρ : 𝓞 E →+* Module.End K W} {ρH : 𝓞 E →+* Module.End K (W × Module.Dual K W)}
    {bar : 𝓞 E ≃+* 𝓞 E} {σ σ' : E →+* K} (h : ∀ a φ, ρH a (0, φ) = (0, φ ∘ₗ ρ (bar a)))
    (hσ : ∀ a : 𝓞 E, σ' (a : E) = σ (bar a : 𝓞 E)) (hb : ∀ a, bar (bar a) = a) (φ : Module.Dual K W) :
    ((0, φ) : W × Module.Dual K W) ∈ HT.eigSp ρH σ ↔ ∀ (b : 𝓞 E) x, φ (ρ b x) = σ' (b : E) * φ x := by
  rw [HT.LatBasic.mem_eigSp]
  constructor
  · intro H b x
    have h1 := H (bar b)
    rw [h, hb] at h1
    rw [hσ]
    exact LinearMap.congr_fun (congrArg Prod.snd h1) x
  · intro H a
    rw [h]
    refine Prod.ext (by simp) (LinearMap.ext fun x => ?_)
    have h1 := H (bar a) x
    rw [hσ, hb] at h1
    exact h1

end PositivityTheory.Xgn.AdaptedEigenbasis

open PositivityTheory.Xgn.AdaptedEigenbasis in
/- English proof (translation)
Introduce `E _ _ K W _ _ _ _ _ ρ ρH bar σ σ' p q v w h1 h2 hσ hb hv hvs hw hws`. Take `⟨f, hf⟩` from `exists_dual hw`. Establish `hvm : ∀ i, v i ∈ HT.eigSp ρ σ` using `fun i => hvs ▸ Submodule.subset_span ⟨i, rfl⟩`. Establish `hwm : ∀ j, w j ∈ HT.eigSp ρ σ'` using `fun j => hws ▸ Submodule.subset_span ⟨j, rfl⟩`. Use `set φ : Fin q → Module.Dual K W := fun j => f j ∘ₗ HT.eigProj ρ σ' with hφ`.

Establish `hφw : ∀ j j', φ j (w j') = if j = j' then 1 else 0` using `fun j j' => by`. Simplify using `only [hφ, LinearMap.comp_apply, HT.LatBasic.eigProj_of_mem (hwm j'), hf]`. Establish `hφe : ∀ j (b : 𝓞 E) x, φ j (ρ b x) = σ' (b : E) * φ j x` using `fun j b x => by`. Simplify using `only [hφ, LinearMap.comp_apply, HodgeDeterminantLattice.eigProj_act, map_smul, smul_eq_mul]`. Use `set l : Fin p → W × Module.Dual K W := fun i => HT.eigProj ρH σ (v i, 0) with hl`.

Establish `hl1 : ∀ i, (l i).1 = v i` using `fun i => by`. Simplify using `only [hl, eigProj_fst h1, HT.LatBasic.eigProj_of_mem (hvm i)]`. Establish `hlm : ∀ i, l i ∈ HT.eigSp ρH σ` using `fun i => HT.LatBasic.eigProj_mem _ _ _`. Establish `hum : ∀ i, Fin.addCases (motive` using `fun _ => W × Module.Dual K W) l (fun j => (0, φ j)) i ∈ HT.eigSp ρH σ := fun i => by`. Use `Fin.addCases (fun i => ?_) (fun j => ?_) i` and prove the remaining obligations.

Simplify `hlm i` using `only [Fin.addCases_left]`. Simplify `(inr_mem_iff h2 hσ hb _).2 (hφe j)` using `only [Fin.addCases_right]`. Use `⟨Fin.addCases (motive := fun _ => W × Module.Dual K W) l (fun j => (0, φ j)), ⟨hum, fun i => by simp only [Fin.addCases_left, hl1], fun j => by simp only [Fin.addCases_right, hφw, implies_true, and_self]⟩, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[Fintype.linearIndependent_iff]`. Introduce `c hc`.

Rewrite `hc` using `[Fin.sum_univ_add]`. Simplify using `only [Fin.addCases_left, Fin.addCases_right] at hc`. Establish `hc1 : ∀ i, c (Fin.castAdd q i) = 0`. Use `Fintype.linearIndependent_iff.1 hv _ ?_` and prove the remaining obligations. Use `congrArg Prod.fst hc` as an intermediate fact.

Simplify `this` using `[Prod.fst_sum, hl1]`. Introduce `i`. Use `Fin.addCases hc1 (fun j => ?_) i` and prove the remaining obligations. Use `LinearMap.congr_fun (congrArg Prod.snd hc) (w j)` as an intermediate fact. Simplify `this` using `[Prod.snd_sum, hc1, hφw]`.

Apply `le_antisymm` to reduce the goal to its premises. Rewrite using `[Submodule.span_le]`. Introduce and unpack `_ ⟨i, rfl⟩`. Conclude with `hum i`. Introduce `y hy`.

Establish `hy1 : y.1 ∈ Submodule.span K (Set.range v)`. Rewrite using `[hvs, HT.LatBasic.mem_eigSp]`. Introduce `a`. Rewrite using `[← h1, HT.LatBasic.mem_eigSp.1 hy a, Prod.smul_fst]`. Take `⟨c, hc⟩` from `(Submodule.mem_span_range_iff_exists_fun K).1 hy1`.

Use `set z := y - ∑ i, c i • l i with hz`. Establish `hzm : z ∈ HT.eigSp ρH σ` using `sub_mem hy (Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (hlm i))`. Establish `hz1 : z = (0, z.2)` using `Prod.ext (by simp [hz, Prod.fst_sum, hl1, hc]) rfl`. Rewrite `hzm` using `[hz1, inr_mem_iff h2 hσ hb]`. Establish `hz2 : z.2 = ∑ j, z.2 (w j) • φ j`.

Use `LinearMap.ext fun x => ?_` and prove the remaining obligations. Establish `hx : HT.eigProj ρ σ' x ∈ Submodule.span K (Set.range w)` using `hws ▸ HT.LatBasic.eigProj_mem _ _ _`. Take `⟨d, hd⟩` from `(Submodule.mem_span_range_iff_exists_fun K).1 hx`. Establish `hd' : ∀ j, φ j x = d j` using `fun j => by`. Rewrite using `[← form_eigProj (hφe j) x, ← hd]`.

Simplify using `[hφw]`. Rewrite using `[← form_eigProj hzm x, ← hd]`. Simplify using `[hd', mul_comm]`. Establish `e : y = ∑ i, c i • l i + ∑ j, z.2 (w j) • ((0, φ j) : W × Module.Dual K W)`. Rewrite using `[← sub_eq_iff_eq_add', ← hz]`.

Use `Prod.ext ?_ ?_` and prove the remaining obligations. Rewrite using `[hz1]`. Simplify using `[Prod.fst_sum]`. Rewrite using `[Prod.snd_sum]`. Conclude with `hz2`.

Rewrite using `[e]`. Use `add_mem (Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨Fin.castAdd q i, by simp only [Fin.addCases_left]⟩)) (Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨Fin.natAdd p j, by simp only [Fin.addCases_right]⟩))` and prove the remaining obligations.
-/
theorem PositivityTheory.Xgn.adapted_eigenbasis_exists : ∀ (E : Type) [Field E] [NumberField E] (K W : Type) [Field K] [CharZero K] [AddCommGroup W] [Module K W] [FiniteDimensional K W] (ρ : 𝓞 E →+* Module.End K W) (ρH : 𝓞 E →+* Module.End K (W × Module.Dual K W)) (bar : 𝓞 E ≃+* 𝓞 E) (σ σ' : E →+* K) (p q : ℕ) (v : Fin p → W) (w : Fin q → W), (∀ a y, (ρH a y).1 = ρ a y.1) → (∀ a φ, ρH a (0, φ) = (0, φ ∘ₗ ρ (bar a))) → (∀ a : 𝓞 E, σ' (a : E) = σ (bar a : 𝓞 E)) → (∀ a, bar (bar a) = a) → LinearIndependent K v → Submodule.span K (Set.range v) = HT.eigSp ρ σ → LinearIndependent K w → Submodule.span K (Set.range w) = HT.eigSp ρ σ' → ∃ u, IsAdapted ρH σ v w u ∧ LinearIndependent K u ∧ Submodule.span K (Set.range u) = HT.eigSp ρH σ := by
  intro E _ _ K W _ _ _ _ _ ρ ρH bar σ σ' p q v w h1 h2 hσ hb hv hvs hw hws
  obtain ⟨f, hf⟩ := exists_dual hw
  have hvm : ∀ i, v i ∈ HT.eigSp ρ σ := fun i => hvs ▸ Submodule.subset_span ⟨i, rfl⟩
  have hwm : ∀ j, w j ∈ HT.eigSp ρ σ' := fun j => hws ▸ Submodule.subset_span ⟨j, rfl⟩
  set φ : Fin q → Module.Dual K W := fun j => f j ∘ₗ HT.eigProj ρ σ' with hφ
  have hφw : ∀ j j', φ j (w j') = if j = j' then 1 else 0 := fun j j' => by
    simp only [hφ, LinearMap.comp_apply, HT.LatBasic.eigProj_of_mem (hwm j'), hf]
  have hφe : ∀ j (b : 𝓞 E) x, φ j (ρ b x) = σ' (b : E) * φ j x := fun j b x => by
    simp only [hφ, LinearMap.comp_apply, HodgeDeterminantLattice.eigProj_act, map_smul, smul_eq_mul]
  set l : Fin p → W × Module.Dual K W := fun i => HT.eigProj ρH σ (v i, 0) with hl
  have hl1 : ∀ i, (l i).1 = v i := fun i => by
    simp only [hl, eigProj_fst h1, HT.LatBasic.eigProj_of_mem (hvm i)]
  have hlm : ∀ i, l i ∈ HT.eigSp ρH σ := fun i => HT.LatBasic.eigProj_mem _ _ _
  have hum : ∀ i, Fin.addCases (motive := fun _ => W × Module.Dual K W) l (fun j => (0, φ j)) i ∈
      HT.eigSp ρH σ := fun i => by
    refine Fin.addCases (fun i => ?_) (fun j => ?_) i
    · simpa only [Fin.addCases_left] using hlm i
    · simpa only [Fin.addCases_right] using (inr_mem_iff h2 hσ hb _).2 (hφe j)
  refine ⟨Fin.addCases (motive := fun _ => W × Module.Dual K W) l (fun j => (0, φ j)),
    ⟨hum, fun i => by simp only [Fin.addCases_left, hl1],
      fun j => by simp only [Fin.addCases_right, hφw, implies_true, and_self]⟩, ?_, ?_⟩
  · rw [Fintype.linearIndependent_iff]
    intro c hc
    rw [Fin.sum_univ_add] at hc
    simp only [Fin.addCases_left, Fin.addCases_right] at hc
    have hc1 : ∀ i, c (Fin.castAdd q i) = 0 := by
      refine Fintype.linearIndependent_iff.1 hv _ ?_
      have := congrArg Prod.fst hc
      simpa [Prod.fst_sum, hl1] using this
    intro i
    refine Fin.addCases hc1 (fun j => ?_) i
    have := LinearMap.congr_fun (congrArg Prod.snd hc) (w j)
    simpa [Prod.snd_sum, hc1, hφw] using this
  · apply le_antisymm
    · rw [Submodule.span_le]
      rintro _ ⟨i, rfl⟩
      exact hum i
    · intro y hy
      have hy1 : y.1 ∈ Submodule.span K (Set.range v) := by
        rw [hvs, HT.LatBasic.mem_eigSp]
        intro a
        rw [← h1, HT.LatBasic.mem_eigSp.1 hy a, Prod.smul_fst]
      obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun K).1 hy1
      set z := y - ∑ i, c i • l i with hz
      have hzm : z ∈ HT.eigSp ρH σ :=
        sub_mem hy (Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (hlm i))
      have hz1 : z = (0, z.2) := Prod.ext (by simp [hz, Prod.fst_sum, hl1, hc]) rfl
      rw [hz1, inr_mem_iff h2 hσ hb] at hzm
      have hz2 : z.2 = ∑ j, z.2 (w j) • φ j := by
        refine LinearMap.ext fun x => ?_
        have hx : HT.eigProj ρ σ' x ∈ Submodule.span K (Set.range w) := hws ▸ HT.LatBasic.eigProj_mem _ _ _
        obtain ⟨d, hd⟩ := (Submodule.mem_span_range_iff_exists_fun K).1 hx
        have hd' : ∀ j, φ j x = d j := fun j => by
          rw [← form_eigProj (hφe j) x, ← hd]
          simp [hφw]
        rw [← form_eigProj hzm x, ← hd]
        simp [hd', mul_comm]
      have e : y = ∑ i, c i • l i + ∑ j, z.2 (w j) • ((0, φ j) : W × Module.Dual K W) := by
        rw [← sub_eq_iff_eq_add', ← hz]
        refine Prod.ext ?_ ?_
        · rw [hz1]
          simp [Prod.fst_sum]
        · rw [Prod.snd_sum]
          exact hz2
      rw [e]
      refine add_mem (Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span
        ⟨Fin.castAdd q i, by simp only [Fin.addCases_left]⟩)) (Submodule.sum_mem _ fun j _ =>
        Submodule.smul_mem _ _ (Submodule.subset_span ⟨Fin.natAdd p j, by simp only [Fin.addCases_right]⟩))

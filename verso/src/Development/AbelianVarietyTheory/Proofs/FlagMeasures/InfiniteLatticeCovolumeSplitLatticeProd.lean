import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.IsLatMeasurableConst
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.CovolEqOfAedisjoint
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.TranslatedLatticeAtInfinityFullCovolumeDual

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.FlagBase GlobalTheory.OrbitTerm
open GlobalTheory.LatFacts Module

noncomputable section

namespace GlobalTheory.CovProd

variable (E : Type) [Field E] [NumberField E] (k : ℕ)

def splitVec : (VecInf E 1 × VecInf E k) ≃ₗ[ℝ] VecInf E (k + 1) where
  toFun p w := Fin.cons (p.1 w 0) (p.2 w)
  invFun x := (fun w _ => x w 0, fun w => Fin.tail (x w))
  map_add' p q := by
    funext w a
    refine Fin.cases ?_ (fun a => ?_) a <;> simp
  map_smul' c p := by
    funext w a
    refine Fin.cases ?_ (fun a => ?_) a <;> simp
  left_inv p := by
    refine Prod.ext ?_ ?_
    · funext w a
      rw [Subsingleton.elim a 0]
      simp
    · funext w
      simp
  right_inv x := by
    funext w
    simp

/- English proof (translation)
Rewrite using `[← ZSpan.map_fundamentalDomain, LinearEquiv.image_eq_preimage_symm, Set.mem_preimage, ZSpan.mem_fundamentalDomain, ZSpan.mem_fundamentalDomain, ZSpan.mem_fundamentalDomain, Sum.forall]`. Simplify using `only [Basis.prod_repr_inl, Basis.prod_repr_inr]`.
-/
theorem mem_fd_prod {ι κ : Type} [Fintype ι] [Fintype κ] (b : Basis ι ℝ (VecInf E 1)) (c : Basis κ ℝ (VecInf E k))
    (x : VecInf E (k + 1)) :
    x ∈ ZSpan.fundamentalDomain ((b.prod c).map (splitVec E k)) ↔
      ((splitVec E k).symm x).1 ∈ ZSpan.fundamentalDomain b ∧
        ((splitVec E k).symm x).2 ∈ ZSpan.fundamentalDomain c := by
  rw [← ZSpan.map_fundamentalDomain, LinearEquiv.image_eq_preimage_symm, Set.mem_preimage,
    ZSpan.mem_fundamentalDomain, ZSpan.mem_fundamentalDomain, ZSpan.mem_fundamentalDomain, Sum.forall]
  simp only [Basis.prod_repr_inl, Basis.prod_repr_inr]

/- English proof (translation)
Establish `h1 : MeasurePreserving (fun (x : InfinitePlace E → Fin (k + 1) → ℂ) w => MeasurableEquiv.piFinSuccAbove (fun _ : Fin (k + 1) => ℂ) 0 (x w)) (Measure.pi fun _ => Measure.pi fun _ => (volume : Measure ℂ)) (Measure.pi fun _ => (volume : Measure ℂ).prod (Measure.pi fun _ : Fin k => ( …` using `measurePreserving_pi _ _ fun _ => measurePreserving_piFinSuccAbove (fun _ => volume) 0`. Establish `h2` using `measurePreserving_arrowProdEquivProdArrow ℂ (Fin k → ℂ) (InfinitePlace E) (fun _ => (volume : Measure ℂ)) (fun _ => Measure.pi fun _ : Fin k => (volume : Measure ℂ))`. Establish `h3 : MeasurePreserving (fun (y : InfinitePlace E → ℂ) w => (MeasurableEquiv.funUnique (Fin 1) ℂ).symm (y w)) (Measure.pi fun _ => (volume : Measure ℂ)) (Measure.pi fun _ => Measure.pi fun _ : Fin 1 => (volume : Measure ℂ))` using `measurePreserving_pi _ _ fun _ => MeasurePreserving.symm _ (measurePreserving_funUnique (volume : Measure ℂ) (Fin 1))`. Establish `h4` using `(h3.prod (MeasurePreserving.id (Measure.pi fun _ : InfinitePlace E => Measure.pi fun _ : Fin k => (volume : Measure ℂ)))).comp (h2.comp h1)`. Use `h4 using 1` and compare the differences between its conclusion and the goal.

Apply the tactic sequence `all_goals rfl`.
-/
private theorem measurePreserving_splitVec_symm :
    MeasurePreserving (fun x : VecInf E (k + 1) => (splitVec E k).symm x) volume volume := by
  have h1 : MeasurePreserving
      (fun (x : InfinitePlace E → Fin (k + 1) → ℂ) w =>
        MeasurableEquiv.piFinSuccAbove (fun _ : Fin (k + 1) => ℂ) 0 (x w))
      (Measure.pi fun _ => Measure.pi fun _ => (volume : Measure ℂ))
      (Measure.pi fun _ => (volume : Measure ℂ).prod (Measure.pi fun _ : Fin k => (volume : Measure ℂ))) :=
    measurePreserving_pi _ _ fun _ => measurePreserving_piFinSuccAbove (fun _ => volume) 0
  have h2 := measurePreserving_arrowProdEquivProdArrow ℂ (Fin k → ℂ) (InfinitePlace E)
    (fun _ => (volume : Measure ℂ)) (fun _ => Measure.pi fun _ : Fin k => (volume : Measure ℂ))
  have h3 : MeasurePreserving
      (fun (y : InfinitePlace E → ℂ) w => (MeasurableEquiv.funUnique (Fin 1) ℂ).symm (y w))
      (Measure.pi fun _ => (volume : Measure ℂ))
      (Measure.pi fun _ => Measure.pi fun _ : Fin 1 => (volume : Measure ℂ)) :=
    measurePreserving_pi _ _ fun _ =>
      MeasurePreserving.symm _ (measurePreserving_funUnique (volume : Measure ℂ) (Fin 1))
  have h4 := (h3.prod (MeasurePreserving.id
    (Measure.pi fun _ : InfinitePlace E => Measure.pi fun _ : Fin k => (volume : Measure ℂ)))).comp (h2.comp h1)
  convert h4 using 1
  all_goals rfl

/- English proof (translation)
Rewrite using `[covAt_span, covAt_span, covAt_span]`. Establish `hs : ZSpan.fundamentalDomain ((b.prod c).map (splitVec E k)) = (fun x => (splitVec E k).symm x) ⁻¹' (ZSpan.fundamentalDomain b ×ˢ ZSpan.fundamentalDomain c)`. Use extensionality with `x`. Rewrite using `[mem_fd_prod]`. Both sides reduce to the same expression.

Establish `hm : MeasurableSet (ZSpan.fundamentalDomain b ×ˢ ZSpan.fundamentalDomain c)` using `(ZSpan.fundamentalDomain_measurableSet b).prod (ZSpan.fundamentalDomain_measurableSet c)`. Rewrite using `[hs, measureReal_def, (measurePreserving_splitVec_symm E k).measure_preimage hm.nullMeasurableSet, Measure.volume_eq_prod, Measure.prod_prod, ENNReal.toReal_mul, measureReal_def, measureReal_def]`.
-/
theorem covAt_prod (b : Basis (Idx E 1) ℝ (VecInf E 1)) (c : Basis (Idx E k) ℝ (VecInf E k)) :
    covAt E (k + 1) (Submodule.span ℤ (Set.range ((b.prod c).map (splitVec E k)))) =
      covAt E 1 (Submodule.span ℤ (Set.range b)) * covAt E k (Submodule.span ℤ (Set.range c)) := by
  rw [covAt_span, covAt_span, covAt_span]
  have hs : ZSpan.fundamentalDomain ((b.prod c).map (splitVec E k)) =
      (fun x => (splitVec E k).symm x) ⁻¹' (ZSpan.fundamentalDomain b ×ˢ ZSpan.fundamentalDomain c) := by
    ext x
    rw [mem_fd_prod]
    rfl
  have hm : MeasurableSet (ZSpan.fundamentalDomain b ×ˢ ZSpan.fundamentalDomain c) :=
    (ZSpan.fundamentalDomain_measurableSet b).prod (ZSpan.fundamentalDomain_measurableSet c)
  rw [hs, measureReal_def, (measurePreserving_splitVec_symm E k).measure_preimage hm.nullMeasurableSet,
    Measure.volume_eq_prod, Measure.prod_prod, ENNReal.toReal_mul, measureReal_def, measureReal_def]

/- English proof (translation)
Simplify using `only [latAt, of_oneInf, inv_one, one_mulVec]`. Both sides reduce to the same expression.
-/
theorem latAt_oneInf (j : ℕ) (Λ : Submodule (𝓞 E) (Fin j → E)) :
    latAt E j Λ (oneInf E j) = Submodule.span ℤ (emb E j '' (Λ : Set (Fin j → E))) := by
  simp only [latAt, of_oneInf, inv_one, one_mulVec]
  rfl

/- English proof (translation)
Apply `le_antisymm` to reduce the goal to its premises. Rewrite using `[Submodule.span_le]`. Introduce and unpack `_ ⟨i, rfl⟩`. Break down `i with i | i` into its components or cases. Use `Submodule.mem_prod.2 ⟨?_, ?_⟩` and prove the remaining obligations.

Rewrite using `[Basis.prod_apply_inl_fst]`. Conclude with `Submodule.subset_span ⟨i, rfl⟩`. Rewrite using `[Basis.prod_apply_inl_snd]`. Conclude with `zero_mem _`. Use `Submodule.mem_prod.2 ⟨?_, ?_⟩` and prove the remaining obligations.

Rewrite using `[Basis.prod_apply_inr_fst]`. Conclude with `zero_mem _`. Rewrite using `[Basis.prod_apply_inr_snd]`. Conclude with `Submodule.subset_span ⟨i, rfl⟩`. Introduce and unpack `⟨x, y⟩ hxy`.

Rewrite `hxy` using `[Submodule.mem_prod]`. Establish `hx : Submodule.span ℤ (Set.range b) ≤ (Submodule.span ℤ (Set.range (b.prod c))).comap (LinearMap.inl ℤ M N)`. Rewrite using `[Submodule.span_le]`. Introduce and unpack `_ ⟨i, rfl⟩`. Use `Submodule.subset_span ⟨Sum.inl i, ?_⟩` and prove the remaining obligations.

Conclude with `Prod.ext (Basis.prod_apply_inl_fst b c i) (Basis.prod_apply_inl_snd b c i)`. Establish `hy : Submodule.span ℤ (Set.range c) ≤ (Submodule.span ℤ (Set.range (b.prod c))).comap (LinearMap.inr ℤ M N)`. Rewrite using `[Submodule.span_le]`. Introduce and unpack `_ ⟨i, rfl⟩`. Use `Submodule.subset_span ⟨Sum.inr i, ?_⟩` and prove the remaining obligations.

Conclude with `Prod.ext (Basis.prod_apply_inr_fst b c i) (Basis.prod_apply_inr_snd b c i)`. Establish `h` using `add_mem (Submodule.mem_comap.1 (hx hxy.1)) (Submodule.mem_comap.1 (hy hxy.2))`. Simplify using `using h`.
-/
theorem span_prod {M N : Type} [AddCommGroup M] [AddCommGroup N] [Module ℝ M] [Module ℝ N] {ι κ : Type}
    (b : Basis ι ℝ M) (c : Basis κ ℝ N) :
    Submodule.span ℤ (Set.range (b.prod c)) =
      (Submodule.span ℤ (Set.range b)).prod (Submodule.span ℤ (Set.range c)) := by
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    rcases i with i | i
    · refine Submodule.mem_prod.2 ⟨?_, ?_⟩
      · rw [Basis.prod_apply_inl_fst]
        exact Submodule.subset_span ⟨i, rfl⟩
      · rw [Basis.prod_apply_inl_snd]
        exact zero_mem _
    · refine Submodule.mem_prod.2 ⟨?_, ?_⟩
      · rw [Basis.prod_apply_inr_fst]
        exact zero_mem _
      · rw [Basis.prod_apply_inr_snd]
        exact Submodule.subset_span ⟨i, rfl⟩
  · rintro ⟨x, y⟩ hxy
    rw [Submodule.mem_prod] at hxy
    have hx : Submodule.span ℤ (Set.range b) ≤
        (Submodule.span ℤ (Set.range (b.prod c))).comap (LinearMap.inl ℤ M N) := by
      rw [Submodule.span_le]
      rintro _ ⟨i, rfl⟩
      refine Submodule.subset_span ⟨Sum.inl i, ?_⟩
      exact Prod.ext (Basis.prod_apply_inl_fst b c i) (Basis.prod_apply_inl_snd b c i)
    have hy : Submodule.span ℤ (Set.range c) ≤
        (Submodule.span ℤ (Set.range (b.prod c))).comap (LinearMap.inr ℤ M N) := by
      rw [Submodule.span_le]
      rintro _ ⟨i, rfl⟩
      refine Submodule.subset_span ⟨Sum.inr i, ?_⟩
      exact Prod.ext (Basis.prod_apply_inr_fst b c i) (Basis.prod_apply_inr_snd b c i)
    have h := add_mem (Submodule.mem_comap.1 (hx hxy.1)) (Submodule.mem_comap.1 (hy hxy.2))
    simpa using h

/- English proof (translation)
Introduce `E _ _ hE k Λ Λ₀ Λ' h₀ h' hΛ`. Rewrite using `[latAt_oneInf, latAt_oneInf, latAt_oneInf]`. Take `⟨b, hb⟩` from `exists_basis E 1 Λ₀ h₀`. Take `⟨c, hc⟩` from `exists_basis E k Λ' h'`. Use `set s : (VecInf E 1 × VecInf E k) →ₗ[ℤ] VecInf E (k + 1) := (splitVec E k).toLinearMap.restrictScalars ℤ with hs`.

Establish `hsv : ∀ p, s p = splitVec E k p` using `fun p => rfl`. Establish `hemb : ∀ y : Fin (k + 1) → E, emb E (k + 1) y = s (emb E 1 (fun _ => y 0), emb E k (Fin.tail y))`. Introduce `y`. Rewrite using `[hsv]`. Use function extensionality and compare the values at `w a`.

Use `Fin.cases ?_ (fun a => ?_) a` and prove the remaining obligations. Both sides reduce to the same expression. Simplify using `[splitVec, emb, Fin.tail]`. Establish `key : Submodule.span ℤ (emb E (k + 1) '' (Λ : Set (Fin (k + 1) → E))) = Submodule.span ℤ (Set.range ((b.prod c).map (splitVec E k)))`. Establish `hr : Set.range ((b.prod c).map (splitVec E k)) = s '' Set.range (b.prod c)`.

Rewrite using `[Basis.coe_map, Set.range_comp]`. Both sides reduce to the same expression. Rewrite using `[hr, Submodule.span_image, span_prod, ← hb, ← hc]`. Apply `le_antisymm` to reduce the goal to its premises. Rewrite using `[Submodule.span_le]`.

Introduce and unpack `_ ⟨y, hy, rfl⟩`. Establish `hy'` using `(hΛ y).1 hy`. Use `Submodule.mem_map.2 ⟨(emb E 1 (fun _ => y 0), emb E k (Fin.tail y)), Submodule.mem_prod.2 ⟨Submodule.subset_span ⟨_, hy'.1, rfl⟩, Submodule.subset_span ⟨_, hy'.2, rfl⟩⟩, (hemb y).symm⟩` and prove the remaining obligations. Rewrite using `[Submodule.map_le_iff_le_comap]`. Introduce and unpack `⟨u, v⟩ huv`.

Rewrite `huv` using `[Submodule.mem_prod]`. Establish `hu : Submodule.span ℤ (emb E 1 '' (Λ₀ : Set (Fin 1 → E))) ≤ (Submodule.span ℤ (emb E (k + 1) '' (Λ : Set (Fin (k + 1) → E)))).comap (s.comp (LinearMap.inl ℤ _ _))`. Rewrite using `[Submodule.span_le]`. Introduce and unpack `_ ⟨z, hz, rfl⟩`. Establish `hz0 : (fun _ : Fin 1 => z 0) = z`.

Use function extensionality and compare the values at `i`. Rewrite using `[Subsingleton.elim i 0]`. Establish `hmem : (Fin.cons (z 0) (0 : Fin k → E) : Fin (k + 1) → E) ∈ Λ`. Use `(hΛ _).2 ⟨?_, ?_⟩` and prove the remaining obligations. Simplify `hz0 ▸ hz` using `only [Fin.cons_zero]`.

Simplify `zero_mem Λ'` using `only [Fin.tail_cons]`. Use `Submodule.subset_span ⟨_, hmem, ?_⟩` and prove the remaining obligations. Rewrite using `[hemb, Fin.tail_cons, map_zero]`. Simplify using `only [Fin.cons_zero, hz0, LinearMap.comp_apply, LinearMap.inl_apply]`. Establish `hv : Submodule.span ℤ (emb E k '' (Λ' : Set (Fin k → E))) ≤ (Submodule.span ℤ (emb E (k + 1) '' (Λ : Set (Fin (k + 1) → E)))).comap (s.comp (LinearMap.inr ℤ _ _))`.

Rewrite using `[Submodule.span_le]`. Introduce and unpack `_ ⟨z, hz, rfl⟩`. Establish `hmem : (Fin.cons 0 z : Fin (k + 1) → E) ∈ Λ`. Use `(hΛ _).2 ⟨?_, ?_⟩` and prove the remaining obligations. Use `zero_mem Λ₀ using 1` and compare the differences between its conclusion and the goal.

Use function extensionality and compare the values at `i`. Simplify using the standard rewrite rules. Rewrite using `[Fin.tail_cons]`. Conclude with `hz`. Use `Submodule.subset_span ⟨_, hmem, ?_⟩` and prove the remaining obligations.

Rewrite using `[hemb, Fin.tail_cons]`. Simplify using `only [Fin.cons_zero, LinearMap.comp_apply, LinearMap.inr_apply]`. Use `congr 2`. Conclude with `map_zero (emb E 1)`. Establish `h` using `add_mem (Submodule.mem_comap.1 (hu huv.1)) (Submodule.mem_comap.1 (hv huv.2))`.

Rewrite using `[Submodule.mem_comap]`. Simplify `h` using `[← map_add]`. Rewrite using `[key, hb, hc]`. Conclude with `covAt_prod E k b c`.
-/
theorem covAt_latAt_prod : ∀ (E : Type) [Field E] [NumberField E], IsTotallyComplex E → ∀ (k : ℕ) (Λ : Submodule (𝓞 E) (Fin (k + 1) → E)) (Λ₀ : Submodule (𝓞 E) (Fin 1 → E)) (Λ' : Submodule (𝓞 E) (Fin k → E)), Submodule.IsLattice E Λ₀ → Submodule.IsLattice E Λ' → (∀ y, y ∈ Λ ↔ (fun _ => y 0) ∈ Λ₀ ∧ Fin.tail y ∈ Λ') → covAt E (k + 1) (latAt E (k + 1) Λ (oneInf E (k + 1))) = covAt E 1 (latAt E 1 Λ₀ (oneInf E 1)) * covAt E k (latAt E k Λ' (oneInf E k)) := by
  intro E _ _ hE k Λ Λ₀ Λ' h₀ h' hΛ
  rw [latAt_oneInf, latAt_oneInf, latAt_oneInf]
  obtain ⟨b, hb⟩ := exists_basis E 1 Λ₀ h₀
  obtain ⟨c, hc⟩ := exists_basis E k Λ' h'

  set s : (VecInf E 1 × VecInf E k) →ₗ[ℤ] VecInf E (k + 1) :=
    (splitVec E k).toLinearMap.restrictScalars ℤ with hs
  have hsv : ∀ p, s p = splitVec E k p := fun p => rfl

  have hemb : ∀ y : Fin (k + 1) → E,
      emb E (k + 1) y = s (emb E 1 (fun _ => y 0), emb E k (Fin.tail y)) := by
    intro y
    rw [hsv]
    funext w a
    refine Fin.cases ?_ (fun a => ?_) a
    · rfl
    · simp [splitVec, emb, Fin.tail]
  have key : Submodule.span ℤ (emb E (k + 1) '' (Λ : Set (Fin (k + 1) → E))) =
      Submodule.span ℤ (Set.range ((b.prod c).map (splitVec E k))) := by
    have hr : Set.range ((b.prod c).map (splitVec E k)) = s '' Set.range (b.prod c) := by
      rw [Basis.coe_map, Set.range_comp]
      rfl
    rw [hr, Submodule.span_image, span_prod, ← hb, ← hc]
    apply le_antisymm
    · rw [Submodule.span_le]
      rintro _ ⟨y, hy, rfl⟩
      have hy' := (hΛ y).1 hy
      refine Submodule.mem_map.2 ⟨(emb E 1 (fun _ => y 0), emb E k (Fin.tail y)),
        Submodule.mem_prod.2 ⟨Submodule.subset_span ⟨_, hy'.1, rfl⟩,
          Submodule.subset_span ⟨_, hy'.2, rfl⟩⟩, (hemb y).symm⟩
    · rw [Submodule.map_le_iff_le_comap]
      rintro ⟨u, v⟩ huv
      rw [Submodule.mem_prod] at huv
      have hu : Submodule.span ℤ (emb E 1 '' (Λ₀ : Set (Fin 1 → E))) ≤
          (Submodule.span ℤ (emb E (k + 1) '' (Λ : Set (Fin (k + 1) → E)))).comap
            (s.comp (LinearMap.inl ℤ _ _)) := by
        rw [Submodule.span_le]
        rintro _ ⟨z, hz, rfl⟩
        have hz0 : (fun _ : Fin 1 => z 0) = z := by
          funext i
          rw [Subsingleton.elim i 0]
        have hmem : (Fin.cons (z 0) (0 : Fin k → E) : Fin (k + 1) → E) ∈ Λ := by
          refine (hΛ _).2 ⟨?_, ?_⟩
          · simpa only [Fin.cons_zero] using hz0 ▸ hz
          · simpa only [Fin.tail_cons] using zero_mem Λ'
        refine Submodule.subset_span ⟨_, hmem, ?_⟩
        rw [hemb, Fin.tail_cons, map_zero]
        simp only [Fin.cons_zero, hz0, LinearMap.comp_apply, LinearMap.inl_apply]
      have hv : Submodule.span ℤ (emb E k '' (Λ' : Set (Fin k → E))) ≤
          (Submodule.span ℤ (emb E (k + 1) '' (Λ : Set (Fin (k + 1) → E)))).comap
            (s.comp (LinearMap.inr ℤ _ _)) := by
        rw [Submodule.span_le]
        rintro _ ⟨z, hz, rfl⟩
        have hmem : (Fin.cons 0 z : Fin (k + 1) → E) ∈ Λ := by
          refine (hΛ _).2 ⟨?_, ?_⟩
          · convert zero_mem Λ₀ using 1
            funext i
            simp
          · rw [Fin.tail_cons]
            exact hz
        refine Submodule.subset_span ⟨_, hmem, ?_⟩
        rw [hemb, Fin.tail_cons]
        simp only [Fin.cons_zero, LinearMap.comp_apply, LinearMap.inr_apply]
        congr 2
        exact map_zero (emb E 1)
      have h := add_mem (Submodule.mem_comap.1 (hu huv.1)) (Submodule.mem_comap.1 (hv huv.2))
      rw [Submodule.mem_comap]
      simpa [← map_add] using h
  rw [key, hb, hc]
  exact covAt_prod E k b c

end GlobalTheory.CovProd

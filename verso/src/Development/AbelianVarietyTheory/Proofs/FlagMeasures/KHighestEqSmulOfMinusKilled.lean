import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ActSingleNeZero
import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.EigenfunctionFiniteCoefficients
import Formalism.RealPlaceAnalysis.RealPlaceTaylor.FirstSlotSliceSlotMixedCasimirZero
import Formalism.RealPlaceAnalysis.RealPlaceTaylor.IsCompactInvariantOrthogonalInf
import Formalism.RealPlaceAnalysis.FinalF
import Formalism.RealPlaceAnalysis.QuotientSettingHolds
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.SymmetricKMapEqZeroOfVminusSlices

open MeasureTheory Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec GlobalTheory.DSId GlobalTheory.Jet
open scoped InnerProductSpace ComplexOrder

noncomputable section

namespace GlobalTheory.Jet

/- English proof (translation)
Use `haveI : FiniteDimensional ℂ (kSpan ε E u) := hfd`. Use `haveI hWfd : FiniteDimensional ℂ (arrV0 ε E u (j + 1)) := by`. Set `φ : arrV0 ε E u (j + 1) →ₗ[ℂ] ((Fin (j + 1) → Fin n × Fin n) → kSpan ε E u)` to `LinearMap.pi fun α => LinearMap.codRestrict (kSpan ε E u) ((LinearMap.proj (R := ℂ) (φ := fun _ : Fin (j + 1) → Fin n × Fin n => V) α ∘ₗ arrOf V n (j + 1)) ∘ₗ (arrV0 ε E u (j + 1)).subtype) (fun F => admissibleArrays_apply_mem F.2 α)`. Use `Module.Finite.of_injective φ ?_` and prove the remaining obligations. Introduce `F G h`.

Apply `Subtype.ext` to reduce the goal to its premises. Apply `indexArray_ext` to reduce the goal to its premises. Introduce `α`. Establish `h'` using `congrArg (fun f => ((f α : kSpan ε E u) : V)) h`. Simplify `h'` using `[φ, arrOf]`.

Use `haveI : CompleteSpace (arrV0 ε E u (j + 1)) := FiniteDimensional.complete ℂ _`. Set `f : arrV0 ε E u (j + 1) →L[ℂ] ℂ` to `LinearMap.toContinuousLinearMap (T ∘ₗ (arrV0 ε E u (j + 1)).subtype)`. Set `G0 : arrV0 ε E u (j + 1)` to `(InnerProductSpace.toDual ℂ (arrV0 ε E u (j + 1))).symm f`. Establish `hGW : (G0 : Arr V n (j + 1)) ∈ arrV0 ε E u (j + 1)` using `G0.2`. Establish `hG : ∀ F ∈ arrV0 ε E u (j + 1), T F = ⟪(G0 : Arr V n (j + 1)), F⟫_ℂ`.

Introduce `F hF`. Establish `h1` using `InnerProductSpace.toDual_symm_apply (𝕜 := ℂ) (E := arrV0 ε E u (j + 1)) (x := ⟨F, hF⟩) (y := f)`. Rewrite `h1` using `[Submodule.coe_inner]`. Rewrite using `[h1]`. Both sides reduce to the same expression.

Use `set G : Arr V n (j + 1) := (G0 : Arr V n (j + 1)) with hGdef`. Establish `hinv : ∀ (s : Equiv.Perm (Fin (j + 1))) (H : Arr V n (j + 1)), permArr V n s (permArr V n s⁻¹ H) = H`. Introduce `s H`. Apply `indexArray_ext` to reduce the goal to its premises. Introduce `α`.

Simplify using `[permutePositions_apply]`. Establish `hsym : G ∈ symSub V n (j + 1)`. Rewrite using `[mem_symmetricArrays]`. Introduce `s`. Establish `hD : permArr V n s G - G ∈ arrV0 ε E u (j + 1)` using `Submodule.sub_mem _ (permute_mem_highest_jets hGW s) hGW`.

Establish `horth : ∀ F ∈ arrV0 ε E u (j + 1), ⟪permArr V n s G - G, F⟫_ℂ = 0`. Introduce `F hF`. Rewrite using `[inner_sub_left, sub_eq_zero]`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[hinv]`.

Use `_ = ⟪G, permArr V n s⁻¹ F⟫_ℂ := inner_permutePositions s _ _`. Use `_ = T (permArr V n s⁻¹ F) := (hG _ (permute_mem_highest_jets hF _)).symm`. Use `_ = T F := hTs F hF s⁻¹`. Use `_ = ⟪G, F⟫_ℂ := hG F hF`. Conclude with `sub_eq_zero.mp (inner_self_eq_zero.mp (horth _ hD))`.

Take `⟨hpm, hsup⟩` from `typesSplit V n ε E (LamOf ε lam) u hE hU hu hfd`. Establish `hVm : Vminus ε E (LamOf ε lam) u ≤ arrV0 ε E u 1` using `isotypicPart_le ε (arrE E 1) _ _ (admissibleArrays_invariant ε E u 1)`. Establish `hslice : ∀ α', sliceLin V n α' G ∈ Vplus ε E (LamOf ε lam) u`. Introduce `α'`. Distinguish the cases in `hα : ∀ i, ε (α' i).1 ≠ ε (α' i).2`.

Establish `hP : sliceLin V n α' G ∈ arrV0 ε E u 1` using `slice_mem_highest_jets hGW α'`. Establish `hperp : ∀ m ∈ Vminus ε E (LamOf ε lam) u, ⟪sliceLin V n α' G, m⟫_ℂ = 0`. Introduce `m hm`. Establish `hins : sliceIns α' m ∈ arrV0 ε E u (j + 1)` using `sliceIns_mem hα (hVm hm)`. Establish `hT0 : T (sliceIns α' m) = 0`.

Apply `hTm _ hins` to reduce the goal to its premises. Introduce `β'`. Rewrite using `[slice_sliceIns]`. Use `split_ifs`. Conclude with `hm`.

Conclude with `zero_mem _`. Rewrite `hT0` using `[hG _ hins, inner_eq_sum_firstPositionSlice]`. Establish `hterm : ∀ β' : Fin j → Fin n × Fin n, ⟪sliceLin V n β' G, sliceLin V n β' (sliceIns α' m)⟫_ℂ = if β' = α' then ⟪sliceLin V n α' G, m⟫_ℂ else 0`. Introduce `β'`. Rewrite using `[slice_sliceIns]`.

Use `split_ifs with h`. Rewrite using `[h]`. Conclude with `inner_zero_right _`. Simplify `hT0` using `only [hterm, Finset.sum_ite_eq', Finset.mem_univ, if_true]`. Rewrite `hP` using `[← hsup]`.

Take `⟨p, hp, m, hm, hpmE⟩` from `Submodule.mem_sup.mp hP`. Establish `hmm : ⟪m, m⟫_ℂ = 0`. Establish `h1` using `hperp m hm`. Rewrite `h1` using `[← hpmE, inner_add_left, hpm p hp m hm, zero_add]`. Conclude with `h1`.

Rewrite `hmm` using `[inner_self_eq_zero]`. Rewrite using `[← hpmE, hmm, add_zero]`. Conclude with `hp`. Rewrite using `[slice_eq_zero_of_compact hGW α' hα]`. Conclude with `zero_mem _`.

Establish `hN : G ∈ Nset ε E (LamOf ε lam) u j`. Simplify using `only [Formalism.REAL.Nset, Submodule.mem_inf, Submodule.mem_iInf, Submodule.mem_comap]`. Conclude with `⟨⟨hGW, hsym⟩, hslice⟩`. Establish `hCW : CasK ε (arrE E (j + 1)) G ∈ arrV0 ε E u (j + 1)`. Rewrite using `[compactCasimir_apply]`.

Use `Submodule.sum_mem _ (fun a _ => Submodule.sum_mem _ (fun b _ => ?_))` and prove the remaining obligations. Use `split_ifs with h`. Conclude with `admissibleArrays_invariant ε E u (j + 1) a b h _ (admissibleArrays_invariant ε E u (j + 1) b a h.symm G hGW)`. Conclude with `zero_mem _`. Establish `hc` using `hTc G hGW`.

Rewrite `hc` using `[hG _ (Submodule.sub_mem _ hCW (Submodule.smul_mem _ _ hGW)), inner_sub_right, inner_smul_right, sub_eq_zero]`. Establish `hre : (⟪G, CasK ε (arrE E (j + 1)) G⟫_ℂ).re = ckv ε (LamOf ε lam) * ‖G‖ ^ 2`. Rewrite using `[hc, Complex.re_ofReal_mul, re_inner_self_indexArray]`. Establish `hpos` using `nPos V n ε E lam g u j hE hU hu hfd hgap G hN`. Rewrite `hpos` using `[hre]`.

Establish `hgn : 0 < g - 2 * (n : ℝ)` using `by linarith`. Establish `hk : 0 < 2 * ((j : ℝ) + 1) * (g - 2 * (n : ℝ))` using `by positivity`. Establish `hsq : ‖G‖ ^ 2 ≤ 0` using `by nlinarith [sq_nonneg ‖G‖]`. Establish `hG0 : G = 0`. Establish `: ‖G‖ = 0` using `by nlinarith [norm_nonneg G]`.

Conclude with `norm_eq_zero.mp this`. Introduce `F hF`. Rewrite using `[hG F hF, hG0, inner_zero_left]`.
-/
theorem form_eq_zero_of_casK (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] (n : ℕ) (ε : Fin n → Bool)
    (E : Fin n → Fin n → Module.End ℂ V) (lam : Fin n → ℝ) (g : ℝ) (u : V) (j : ℕ) (hE : GlRel E)
    (hU : IsUnitary ε E) (hu : KHighest ε E (LamOf ε lam) u) (hfd : FiniteDimensional ℂ (kSpan ε E u))
    (hgap : ∀ a b : Fin n, a < b → ε a ≠ ε b → g ≤ lam a - lam b) (hg : 2 * (n : ℝ) < g)
    (T : Arr V n (j + 1) →ₗ[ℂ] ℂ)
    (hTc : ∀ F ∈ arrV0 ε E u (j + 1),
      T (CasK ε (arrE E (j + 1)) F - ((ckv ε (LamOf ε lam) : ℝ) : ℂ) • F) = 0)
    (hTs : ∀ F ∈ arrV0 ε E u (j + 1), ∀ s : Equiv.Perm (Fin (j + 1)), T (permArr V n s F) = T F)
    (hTm : ∀ F ∈ arrV0 ε E u (j + 1), (∀ α', sliceLin V n α' F ∈ Vminus ε E (LamOf ε lam) u) → T F = 0) :
    ∀ F ∈ arrV0 ε E u (j + 1), T F = 0 := by
  haveI : FiniteDimensional ℂ (kSpan ε E u) := hfd
  haveI hWfd : FiniteDimensional ℂ (arrV0 ε E u (j + 1)) := by
    let φ : arrV0 ε E u (j + 1) →ₗ[ℂ] ((Fin (j + 1) → Fin n × Fin n) → kSpan ε E u) :=
      LinearMap.pi fun α => LinearMap.codRestrict (kSpan ε E u)
        ((LinearMap.proj (R := ℂ) (φ := fun _ : Fin (j + 1) → Fin n × Fin n => V) α ∘ₗ
          arrOf V n (j + 1)) ∘ₗ (arrV0 ε E u (j + 1)).subtype)
        (fun F => admissibleArrays_apply_mem F.2 α)
    refine Module.Finite.of_injective φ ?_
    intro F G h
    apply Subtype.ext
    apply indexArray_ext
    intro α
    have h' := congrArg (fun f => ((f α : kSpan ε E u) : V)) h
    simpa [φ, arrOf] using h'
  haveI : CompleteSpace (arrV0 ε E u (j + 1)) := FiniteDimensional.complete ℂ _
  let f : arrV0 ε E u (j + 1) →L[ℂ] ℂ := LinearMap.toContinuousLinearMap (T ∘ₗ (arrV0 ε E u (j + 1)).subtype)
  let G0 : arrV0 ε E u (j + 1) := (InnerProductSpace.toDual ℂ (arrV0 ε E u (j + 1))).symm f
  have hGW : (G0 : Arr V n (j + 1)) ∈ arrV0 ε E u (j + 1) := G0.2
  have hG : ∀ F ∈ arrV0 ε E u (j + 1), T F = ⟪(G0 : Arr V n (j + 1)), F⟫_ℂ := by
    intro F hF
    have h1 := InnerProductSpace.toDual_symm_apply (𝕜 := ℂ) (E := arrV0 ε E u (j + 1)) (x := ⟨F, hF⟩) (y := f)
    rw [Submodule.coe_inner] at h1
    rw [h1]
    rfl
  set G : Arr V n (j + 1) := (G0 : Arr V n (j + 1)) with hGdef

  have hinv : ∀ (s : Equiv.Perm (Fin (j + 1))) (H : Arr V n (j + 1)),
      permArr V n s (permArr V n s⁻¹ H) = H := by
    intro s H
    apply indexArray_ext
    intro α
    simp [permutePositions_apply]
  have hsym : G ∈ symSub V n (j + 1) := by
    rw [mem_symmetricArrays]
    intro s
    have hD : permArr V n s G - G ∈ arrV0 ε E u (j + 1) :=
      Submodule.sub_mem _ (permute_mem_highest_jets hGW s) hGW
    have horth : ∀ F ∈ arrV0 ε E u (j + 1), ⟪permArr V n s G - G, F⟫_ℂ = 0 := by
      intro F hF
      rw [inner_sub_left, sub_eq_zero]
      calc ⟪permArr V n s G, F⟫_ℂ = ⟪permArr V n s G, permArr V n s (permArr V n s⁻¹ F)⟫_ℂ := by
            rw [hinv]
        _ = ⟪G, permArr V n s⁻¹ F⟫_ℂ := inner_permutePositions s _ _
        _ = T (permArr V n s⁻¹ F) := (hG _ (permute_mem_highest_jets hF _)).symm
        _ = T F := hTs F hF s⁻¹
        _ = ⟪G, F⟫_ℂ := hG F hF
    exact sub_eq_zero.mp (inner_self_eq_zero.mp (horth _ hD))

  obtain ⟨hpm, hsup⟩ := typesSplit V n ε E (LamOf ε lam) u hE hU hu hfd
  have hVm : Vminus ε E (LamOf ε lam) u ≤ arrV0 ε E u 1 :=
    isotypicPart_le ε (arrE E 1) _ _ (admissibleArrays_invariant ε E u 1)
  have hslice : ∀ α', sliceLin V n α' G ∈ Vplus ε E (LamOf ε lam) u := by
    intro α'
    by_cases hα : ∀ i, ε (α' i).1 ≠ ε (α' i).2
    · have hP : sliceLin V n α' G ∈ arrV0 ε E u 1 := slice_mem_highest_jets hGW α'
      have hperp : ∀ m ∈ Vminus ε E (LamOf ε lam) u, ⟪sliceLin V n α' G, m⟫_ℂ = 0 := by
        intro m hm
        have hins : sliceIns α' m ∈ arrV0 ε E u (j + 1) := sliceIns_mem hα (hVm hm)
        have hT0 : T (sliceIns α' m) = 0 := by
          apply hTm _ hins
          intro β'
          rw [slice_sliceIns]
          split_ifs
          · exact hm
          · exact zero_mem _
        rw [hG _ hins, inner_eq_sum_firstPositionSlice] at hT0
        have hterm : ∀ β' : Fin j → Fin n × Fin n,
            ⟪sliceLin V n β' G, sliceLin V n β' (sliceIns α' m)⟫_ℂ =
              if β' = α' then ⟪sliceLin V n α' G, m⟫_ℂ else 0 := by
          intro β'
          rw [slice_sliceIns]
          split_ifs with h
          · rw [h]
          · exact inner_zero_right _
        simpa only [hterm, Finset.sum_ite_eq', Finset.mem_univ, if_true] using hT0
      rw [← hsup] at hP
      obtain ⟨p, hp, m, hm, hpmE⟩ := Submodule.mem_sup.mp hP
      have hmm : ⟪m, m⟫_ℂ = 0 := by
        have h1 := hperp m hm
        rw [← hpmE, inner_add_left, hpm p hp m hm, zero_add] at h1
        exact h1
      rw [inner_self_eq_zero] at hmm
      rw [← hpmE, hmm, add_zero]
      exact hp
    · rw [slice_eq_zero_of_compact hGW α' hα]
      exact zero_mem _
  have hN : G ∈ Nset ε E (LamOf ε lam) u j := by
    simp only [Formalism.REAL.Nset, Submodule.mem_inf, Submodule.mem_iInf, Submodule.mem_comap]
    exact ⟨⟨hGW, hsym⟩, hslice⟩

  have hCW : CasK ε (arrE E (j + 1)) G ∈ arrV0 ε E u (j + 1) := by
    rw [compactCasimir_apply]
    refine Submodule.sum_mem _ (fun a _ => Submodule.sum_mem _ (fun b _ => ?_))
    split_ifs with h
    · exact admissibleArrays_invariant ε E u (j + 1) a b h _ (admissibleArrays_invariant ε E u (j + 1) b a h.symm G hGW)
    · exact zero_mem _
  have hc := hTc G hGW
  rw [hG _ (Submodule.sub_mem _ hCW (Submodule.smul_mem _ _ hGW)), inner_sub_right,
    inner_smul_right, sub_eq_zero] at hc
  have hre : (⟪G, CasK ε (arrE E (j + 1)) G⟫_ℂ).re = ckv ε (LamOf ε lam) * ‖G‖ ^ 2 := by
    rw [hc, Complex.re_ofReal_mul, re_inner_self_indexArray]
  have hpos := nPos V n ε E lam g u j hE hU hu hfd hgap G hN
  rw [hre] at hpos
  have hgn : 0 < g - 2 * (n : ℝ) := by linarith
  have hk : 0 < 2 * ((j : ℝ) + 1) * (g - 2 * (n : ℝ)) := by positivity
  have hsq : ‖G‖ ^ 2 ≤ 0 := by nlinarith [sq_nonneg ‖G‖]
  have hG0 : G = 0 := by
    have : ‖G‖ = 0 := by nlinarith [norm_nonneg G]
    exact norm_eq_zero.mp this
  intro F hF
  rw [hG F hF, hG0, inner_zero_left]

/- English proof (translation)
Proceed by induction on `w with`. Consider the case `nil => simp [ew]`. Consider the case `cons q w ih => simp only [List.cons_append, ew, ih, mul_assoc]`.
-/
private theorem ew_append_singleton {V : Type} [AddCommGroup V] [Module ℂ V] {n : ℕ}
    (E : Fin n → Fin n → Module.End ℂ V) (w : List (Fin n × Fin n)) (p : Fin n × Fin n) :
    ew E (w ++ [p]) = ew E w * E p.1 p.2 := by
  induction w with
  | nil => simp [ew]
  | cons q w ih => simp only [List.cons_append, ew, ih, mul_assoc]

/- English proof (translation)
Establish `hθ : ∀ H : Arr V n (j + 1), thetaA E (j + 1) H = ∑ α : Fin (j + 1) → Fin n × Fin n, ew E (List.ofFn α).reverse (H α)`. Introduce `H`. Simplify using `[thetaA, arrOf]`. Rewrite using `[hθ, sum_fin_cons]`. Use `Finset.sum_congr rfl (fun α' _ => ?_)` and prove the remaining obligations.

Establish `hterm : ∀ β : Fin 1 → Fin n × Fin n, ew E (List.ofFn (Fin.cons (β 0) α' : Fin (j + 1) → Fin n × Fin n)).reverse (F (Fin.cons (β 0) α')) = ew E (List.ofFn α').reverse (E (β 0).1 (β 0).2 (F (Fin.cons (β 0) α')))`. Introduce `β`. Rewrite using `[List.ofFn_succ]`. Simplify using `only [Fin.cons_zero, Fin.cons_succ, List.reverse_cons, ew_append_singleton, Module.End.mul_apply]`. Simplify using `only [hterm]`.

Rewrite using `[← map_sum]`. Use `congr 1`. Establish `hat : ∀ a b, at1 (sliceLin V n α' F) a b = F (Fin.cons (a, b) α')`. Introduce `a b`. Rewrite using `[at1, ← firstPositionSlice_apply α' F (fun _ => (a, b))]`.

Both sides reduce to the same expression. Simplify using `only [hat]`. Rewrite using `[← Fintype.sum_prod_type']`. Conclude with `Fintype.sum_equiv (Equiv.funUnique (Fin 1) (Fin n × Fin n)) _ _ (fun β => rfl)`.
-/
theorem thetaA_eq_sum_slice {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] {n j : ℕ}
    (E : Fin n → Fin n → Module.End ℂ V) (F : Arr V n (j + 1)) :
    thetaA E (j + 1) F = ∑ α' : Fin j → Fin n × Fin n, ew E (List.ofFn α').reverse
      (∑ a, ∑ b, E a b (at1 (sliceLin V n α' F) a b)) := by
  have hθ : ∀ H : Arr V n (j + 1), thetaA E (j + 1) H =
      ∑ α : Fin (j + 1) → Fin n × Fin n, ew E (List.ofFn α).reverse (H α) := by
    intro H
    simp [thetaA, arrOf]
  rw [hθ, sum_fin_cons]
  refine Finset.sum_congr rfl (fun α' _ => ?_)
  have hterm : ∀ β : Fin 1 → Fin n × Fin n,
      ew E (List.ofFn (Fin.cons (β 0) α' : Fin (j + 1) → Fin n × Fin n)).reverse
          (F (Fin.cons (β 0) α')) =
        ew E (List.ofFn α').reverse (E (β 0).1 (β 0).2 (F (Fin.cons (β 0) α'))) := by
    intro β
    rw [List.ofFn_succ]
    simp only [Fin.cons_zero, Fin.cons_succ, List.reverse_cons, ew_append_singleton, Module.End.mul_apply]
  simp only [hterm]
  rw [← map_sum]
  congr 1
  have hat : ∀ a b, at1 (sliceLin V n α' F) a b = F (Fin.cons (a, b) α') := by
    intro a b
    rw [at1, ← firstPositionSlice_apply α' F (fun _ => (a, b))]
    rfl
  simp only [hat]
  rw [← Fintype.sum_prod_type']
  exact Fintype.sum_equiv (Equiv.funUnique (Fin 1) (Fin n × Fin n)) _ _ (fun β => rfl)

/- English proof (translation)
Establish `harr : ∀ (c d : Fin n) (H : Arr V n j), thetaA E j (arrE E j c d H) = E c d (thetaA E j H)` using `((arrModule V n ε E j).1 hE).2`. Rewrite using `[compactCasimir_apply, compactCasimir_apply, map_sum]`. Use `Finset.sum_congr rfl (fun a _ => ?_)` and prove the remaining obligations. Rewrite using `[map_sum]`. Use `Finset.sum_congr rfl (fun b _ => ?_)` and prove the remaining obligations.

Use `split_ifs with h`. Rewrite using `[harr, harr]`. Conclude with `map_zero _`.
-/
theorem thetaA_casK {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] {n j : ℕ} (ε : Fin n → Bool)
    (E : Fin n → Fin n → Module.End ℂ V) (hE : GlRel E) (F : Arr V n j) :
    thetaA E j (CasK ε (arrE E j) F) = CasK ε E (thetaA E j F) := by
  have harr : ∀ (c d : Fin n) (H : Arr V n j), thetaA E j (arrE E j c d H) = E c d (thetaA E j H) :=
    ((arrModule V n ε E j).1 hE).2
  rw [compactCasimir_apply, compactCasimir_apply, map_sum]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  rw [map_sum]
  refine Finset.sum_congr rfl (fun b _ => ?_)
  split_ifs with h
  · rw [harr, harr]
  · exact map_zero _

/- English proof (translation)
Rewrite using `[compactCasimir_apply, compactCasimir_apply, inner_sum, sum_inner]`. Use `Finset.sum_congr rfl (fun a _ => ?_)` and prove the remaining obligations. Rewrite using `[inner_sum, sum_inner]`. Use `Finset.sum_congr rfl (fun b _ => ?_)` and prove the remaining obligations. Use `split_ifs with h`.

Rewrite using `[← hU b a h.symm x (E b a y), hU a b h (E b a x) y]`. Rewrite using `[inner_zero_right, inner_zero_left]`.
-/
theorem inner_casK_symm {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] {n : ℕ} (ε : Fin n → Bool)
    (E : Fin n → Fin n → Module.End ℂ V) (hU : KUnit ε E) (x y : V) :
    ⟪x, CasK ε E y⟫_ℂ = ⟪CasK ε E x, y⟫_ℂ := by
  rw [compactCasimir_apply, compactCasimir_apply, inner_sum, sum_inner]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  rw [inner_sum, sum_inner]
  refine Finset.sum_congr rfl (fun b _ => ?_)
  split_ifs with h
  · rw [← hU b a h.symm x (E b a y), hU a b h (E b a x) y]
  · rw [inner_zero_right, inner_zero_left]

/- English proof (translation)
Introduce `V _ _ n ε E lam g u hE hU hu hfd hgap hg hmin x hx hxk`. Establish `hKU : KUnit ε E` using `isUnitary_kUnit ε E hU`. Establish `hKR : KRel ε E` using `glRel_kRel ε E hE`. Take `⟨hP0, -, -, -, hPcyc, hPex, -⟩` from `pfilFacts V n ε E u hE`. Take `⟨-, hTonto, hTsym⟩` from `thetaFil V n ε E u hE`.

Use `set c : ℂ := ⟪u, x⟫_ℂ / ⟪u, u⟫_ℂ with hcdef`. Use `set z : V := x - c • u with hzdef`. Establish `huz : ⟪u, z⟫_ℂ = 0`. Distinguish the cases in `h0 : u = 0`. Rewrite using `[h0, inner_zero_left]`.

Establish `hne : ⟪u, u⟫_ℂ ≠ 0` using `inner_self_ne_zero.mpr h0`. Rewrite using `[hzdef, inner_sub_right, inner_smul_right, hcdef, div_mul_cancel₀ _ hne, sub_self]`. Establish `hzK : KHighest ε E (LamOf ε lam) z`. Use `⟨fun a => ?_, fun a b h1 h2 => ?_⟩` and prove the remaining obligations. Rewrite using `[hzdef, map_sub, map_smul, hxk.1 a, hu.1 a, smul_sub, smul_comm c]`.

Rewrite using `[hzdef, map_sub, map_smul, hxk.2 a b h1 h2, hu.2 a b h1 h2, smul_zero, sub_zero]`. Establish `memO : ∀ y : V, y ∈ (ℂ ∙ z)ᗮ ↔ ⟪z, y⟫_ℂ = 0` using `fun y => Submodule.mem_orthogonal_singleton_iff_inner_right`. Establish `base : pfil ε E u 0 ≤ (ℂ ∙ z)ᗮ`. Rewrite using `[hP0, (kLow V n ε E (LamOf ε lam) u hKR hu).1, lowSpan]`. Use `Submodule.span_le.mpr ?_` and prove the remaining obligations.

Introduce and unpack `y ⟨w, hw, rfl⟩`. Rewrite using `[SetLike.mem_coe, memO]`. Consider the cases of `w with`. Consider the case `nil`. Rewrite using `[ew, Module.End.one_apply]`.

Conclude with `inner_eq_zero_symm.mp huz`. Consider the case `cons p w`. Take `⟨h1, h2⟩` from `hw p (List.mem_cons_self ..)`. Rewrite using `[ew, Module.End.mul_apply, ← hKU p.2 p.1 h1.symm, hzK.2 p.2 p.1 h2 h1.symm, inner_zero_left]`. Establish `step : ∀ j, pfil ε E u j ≤ (ℂ ∙ z)ᗮ → pfil ε E u (j + 1) ≤ (ℂ ∙ z)ᗮ`.

Introduce `j ih`. Establish `hT : ∀ F ∈ arrV0 ε E u (j + 1), ⟪z, thetaA E (j + 1) F⟫_ℂ = 0`. Establish `key` using `form_eq_zero_of_casK V n ε E lam g u j hE hU hu hfd hgap hg ((innerₛₗ ℂ z).comp (thetaA E (j + 1))) (by`. Introduce `F hF`. Rewrite using `[LinearMap.comp_apply, innerₛₗ_apply_apply, map_sub, map_smul, thetaA_casK ε E hE, inner_sub_right, inner_smul_right, inner_casK_symm ε E hKU, kCasSpan V n ε E (LamOf ε lam) z hKR hzK z (mem_compactSpan_self ε E z), inner_smul_left, Complex.conj_ofReal, sub_self])`.

Use the proof step `(by`. Introduce `F hF s`. Rewrite using `[LinearMap.comp_apply, LinearMap.comp_apply, innerₛₗ_apply_apply, innerₛₗ_apply_apply]`. Establish `h3` using `(memO _).mp (ih (hTsym j F hF s))`. Rewrite `h3` using `[inner_sub_right, sub_eq_zero]`.

Conclude with `h3)`. Use the proof step `(by`. Introduce `F hF hsl`. Rewrite using `[LinearMap.comp_apply, innerₛₗ_apply_apply, thetaA_eq_sum_slice, Finset.sum_eq_zero, inner_zero_right]`. Introduce `α' _`.

Rewrite using `[hmin _ (hsl α'), map_zero])`. Introduce `F hF`. Simplify using `using key F hF`. Introduce `y hy`. Take `⟨y1, hy1, y2, hy2, rfl⟩` from `Submodule.mem_sup.mp (hTonto j hy)`.

Take `⟨F, hF, rfl⟩` from `Submodule.mem_map.mp hy1`. Rewrite using `[memO, inner_add_right, hT F hF, (memO _).mp (ih hy2), add_zero]`. Establish `hall : ∀ j, pfil ε E u j ≤ (ℂ ∙ z)ᗮ`. Introduce `j`. Proceed by induction on `j with`.

Consider the case `zero => exact base`. Consider the case `succ j ih => exact step j ih`. Establish `hucyc : u ∈ cyc E u` using `hPcyc 0 (by rw [hP0]; exact mem_compactSpan_self ε E u)`. Establish `hzc : z ∈ cyc E u` using `(cyc E u).sub_mem hx ((cyc E u).smul_mem c hucyc)`. Take `⟨j, hj⟩` from `hPex z hzc`.

Establish `hzz : ⟪z, z⟫_ℂ = 0` using `(memO z).mp (hall j hj)`. Establish `hz0 : z = 0` using `inner_self_eq_zero.mp hzz`. Conclude with `⟨c, sub_eq_zero.mp hz0⟩`.
-/
theorem kHighest_eq_smul_of_minus_killed : ∀ (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] (n : ℕ) (ε : Fin n → Bool) (E : Fin n → Fin n → Module.End ℂ V) (lam : Fin n → ℝ) (g : ℝ) (u : V), GlRel E → IsUnitary ε E → KHighest ε E (LamOf ε lam) u → FiniteDimensional ℂ (kSpan ε E u) → (∀ a b : Fin n, a < b → ε a ≠ ε b → g ≤ lam a - lam b) → 2 * (n : ℝ) < g → (∀ G ∈ Vminus ε E (LamOf ε lam) u, ∑ a, ∑ b, E a b (at1 G a b) = 0) → ∀ x ∈ cyc E u, KHighest ε E (LamOf ε lam) x → ∃ c : ℂ, x = c • u := by
  intro V _ _ n ε E lam g u hE hU hu hfd hgap hg hmin x hx hxk
  have hKU : KUnit ε E := isUnitary_kUnit ε E hU
  have hKR : KRel ε E := glRel_kRel ε E hE
  obtain ⟨hP0, -, -, -, hPcyc, hPex, -⟩ := pfilFacts V n ε E u hE
  obtain ⟨-, hTonto, hTsym⟩ := thetaFil V n ε E u hE
  set c : ℂ := ⟪u, x⟫_ℂ / ⟪u, u⟫_ℂ with hcdef
  set z : V := x - c • u with hzdef
  have huz : ⟪u, z⟫_ℂ = 0 := by
    by_cases h0 : u = 0
    · rw [h0, inner_zero_left]
    have hne : ⟪u, u⟫_ℂ ≠ 0 := inner_self_ne_zero.mpr h0
    rw [hzdef, inner_sub_right, inner_smul_right, hcdef, div_mul_cancel₀ _ hne, sub_self]
  have hzK : KHighest ε E (LamOf ε lam) z := by
    refine ⟨fun a => ?_, fun a b h1 h2 => ?_⟩
    · rw [hzdef, map_sub, map_smul, hxk.1 a, hu.1 a, smul_sub, smul_comm c]
    · rw [hzdef, map_sub, map_smul, hxk.2 a b h1 h2, hu.2 a b h1 h2, smul_zero, sub_zero]
  have memO : ∀ y : V, y ∈ (ℂ ∙ z)ᗮ ↔ ⟪z, y⟫_ℂ = 0 :=
    fun y => Submodule.mem_orthogonal_singleton_iff_inner_right
  have base : pfil ε E u 0 ≤ (ℂ ∙ z)ᗮ := by
    rw [hP0, (kLow V n ε E (LamOf ε lam) u hKR hu).1, lowSpan]
    refine Submodule.span_le.mpr ?_
    rintro y ⟨w, hw, rfl⟩
    rw [SetLike.mem_coe, memO]
    cases w with
    | nil =>
      rw [ew, Module.End.one_apply]
      exact inner_eq_zero_symm.mp huz
    | cons p w =>
      obtain ⟨h1, h2⟩ := hw p (List.mem_cons_self ..)
      rw [ew, Module.End.mul_apply, ← hKU p.2 p.1 h1.symm, hzK.2 p.2 p.1 h2 h1.symm, inner_zero_left]
  have step : ∀ j, pfil ε E u j ≤ (ℂ ∙ z)ᗮ → pfil ε E u (j + 1) ≤ (ℂ ∙ z)ᗮ := by
    intro j ih
    have hT : ∀ F ∈ arrV0 ε E u (j + 1), ⟪z, thetaA E (j + 1) F⟫_ℂ = 0 := by
      have key := form_eq_zero_of_casK V n ε E lam g u j hE hU hu hfd hgap hg
        ((innerₛₗ ℂ z).comp (thetaA E (j + 1)))
        (by
          intro F hF
          rw [LinearMap.comp_apply, innerₛₗ_apply_apply, map_sub, map_smul, thetaA_casK ε E hE,
            inner_sub_right, inner_smul_right, inner_casK_symm ε E hKU,
            kCasSpan V n ε E (LamOf ε lam) z hKR hzK z (mem_compactSpan_self ε E z),
            inner_smul_left, Complex.conj_ofReal, sub_self])
        (by
          intro F hF s
          rw [LinearMap.comp_apply, LinearMap.comp_apply, innerₛₗ_apply_apply, innerₛₗ_apply_apply]
          have h3 := (memO _).mp (ih (hTsym j F hF s))
          rw [inner_sub_right, sub_eq_zero] at h3
          exact h3)
        (by
          intro F hF hsl
          rw [LinearMap.comp_apply, innerₛₗ_apply_apply, thetaA_eq_sum_slice, Finset.sum_eq_zero, inner_zero_right]
          intro α' _
          rw [hmin _ (hsl α'), map_zero])
      intro F hF
      simpa using key F hF
    intro y hy
    obtain ⟨y1, hy1, y2, hy2, rfl⟩ := Submodule.mem_sup.mp (hTonto j hy)
    obtain ⟨F, hF, rfl⟩ := Submodule.mem_map.mp hy1
    rw [memO, inner_add_right, hT F hF, (memO _).mp (ih hy2), add_zero]
  have hall : ∀ j, pfil ε E u j ≤ (ℂ ∙ z)ᗮ := by
    intro j
    induction j with
    | zero => exact base
    | succ j ih => exact step j ih
  have hucyc : u ∈ cyc E u := hPcyc 0 (by rw [hP0]; exact mem_compactSpan_self ε E u)
  have hzc : z ∈ cyc E u := (cyc E u).sub_mem hx ((cyc E u).smul_mem c hucyc)
  obtain ⟨j, hj⟩ := hPex z hzc
  have hzz : ⟪z, z⟫_ℂ = 0 := (memO z).mp (hall j hj)
  have hz0 : z = 0 := inner_self_eq_zero.mp hzz
  exact ⟨c, sub_eq_zero.mp hz0⟩

end GlobalTheory.Jet

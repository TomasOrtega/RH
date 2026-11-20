import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsStableGauss
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NonemptyMeasAndReps
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.QuadraticWeilUnipotentTorusPreserveTest
open GlobalTheory.JR GlobalTheory.JR.WeilQuad Matrix MeasureTheory Filter Topology

noncomputable section

namespace GlobalTheory.JR.WeilQuad.GaussStable

variable {F E : Type} [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E]

/- English proof (translation)
Take `⟨-, hinj, hN, htr, -⟩` from `GlobalTheory.JR.Et.quadratic_structure F E A`. Apply `hinj` to reduce the goal to its premises. Rewrite using `[map_add, map_add, hN, hN, hN, htr, star_add, star_mul, star_star]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem NL_add [Unram F E] (A : Et F E) (y m : A.L) :
    A.NL (y + m) = A.NL y + Algebra.trace A.K A.L (star m * y) + A.NL m := by
  obtain ⟨-, hinj, hN, htr, -⟩ := GlobalTheory.JR.Et.quadratic_structure F E A
  apply hinj
  rw [map_add, map_add, hN, hN, hN, htr, star_add, star_mul, star_star]
  ring

/- English proof (translation)
Take `⟨-, hinj, hN, -, -⟩` from `GlobalTheory.JR.Et.quadratic_structure F E A`. Apply `hinj` to reduce the goal to its premises. Rewrite using `[hN, zero_mul, map_zero]`.
-/
theorem NL_zero [Unram F E] (A : Et F E) : A.NL 0 = 0 := by
  obtain ⟨-, hinj, hN, -, -⟩ := GlobalTheory.JR.Et.quadratic_structure F E A
  apply hinj
  rw [hN, zero_mul, map_zero]

/- English proof (translation)
Use `U.charZero` as an intermediate fact. Use `EtMeas.finite_L A` as an intermediate fact. Take `⟨-, hinj, -, htr, hnd⟩` from `GlobalTheory.JR.Et.quadratic_structure F E A`. Establish `hs : (EtMeas.formL A v).IsSymm` using `⟨fun y y' => by`. Rewrite using `[EtMeas.formL_apply, EtMeas.formL_apply]`.

Use `congr 2`. Apply `hinj` to reduce the goal to its premises. Rewrite using `[htr, htr]`. Simplify using `[add_comm, mul_comm]⟩`. Establish `hl : ∀ y', (∀ y, EtMeas.formL A v y' y = 0) → y' = 0` using `fun y' h => hnd y' fun y => by`.

Establish `h1 : (v : A.K) * Algebra.trace A.K A.L (star y' * y) = 0` using `EtMeas.eq_zero_of_trace F A.K _ fun k => by`. Use `h (k • y)` as an intermediate fact. Rewrite `this` using `[EtMeas.formL_apply, mul_smul_comm, map_smul, smul_eq_mul]`. Rewrite using `[← this]`. Use `congr 1`.

Expand and normalize the polynomial expressions, which then agree. Simplify using `using h1`. Conclude with `⟨hs, ⟨hl, fun y h => hl y fun y' => by rw [hs.eq]; exact h y'⟩⟩`.
-/
theorem formL_symm_nondeg [U : Unram F E] (A : Et F E) (v : A.Kˣ) :
    (EtMeas.formL A v).IsSymm ∧ (EtMeas.formL A v).Nondegenerate := by
  have := U.charZero
  have := EtMeas.finite_L A
  obtain ⟨-, hinj, -, htr, hnd⟩ := GlobalTheory.JR.Et.quadratic_structure F E A
  have hs : (EtMeas.formL A v).IsSymm := ⟨fun y y' => by
    rw [EtMeas.formL_apply, EtMeas.formL_apply]
    congr 2
    apply hinj
    rw [htr, htr]; simp [add_comm, mul_comm]⟩
  have hl : ∀ y', (∀ y, EtMeas.formL A v y' y = 0) → y' = 0 := fun y' h => hnd y' fun y => by
    have h1 : (v : A.K) * Algebra.trace A.K A.L (star y' * y) = 0 := EtMeas.eq_zero_of_trace F A.K _ fun k => by
      have := h (k • y)
      rw [EtMeas.formL_apply, mul_smul_comm, map_smul, smul_eq_mul] at this
      rw [← this]; congr 1; ring
    simpa using h1
  exact ⟨hs, ⟨hl, fun y h => hl y fun y' => by rw [hs.eq]; exact h y'⟩⟩

open Classical in

/- English proof (translation)
Use `split_ifs with h`. Rewrite using `[show (M : Set V).indicator χ = (M : Set V).indicator (fun _ => (1 : ℂ)) from Set.indicator_congr (fun m hm => h m hm), integral_indicator_const _ hMo.measurableSet]`. Simplify using the standard rewrite rules. Use `push Not at h`. Take `⟨m0, hm0, h1⟩` from `h`.

Use `AbsInv.integral_eq_zero_of_translate μ _ m0 (χ m0) h1 fun m => ?_` and prove the remaining obligations. Distinguish the cases in `hm : m ∈ M`. Rewrite using `[Set.indicator_of_mem (by exact M.add_mem hm hm0), Set.indicator_of_mem (by exact hm), hχ, mul_comm]`. Establish `h2 : m + m0 ∉ M` using `fun h' => hm (by simpa using M.sub_mem h' hm0)`. Rewrite using `[Set.indicator_of_notMem (by exact h2), Set.indicator_of_notMem (by exact hm), mul_zero]`.
-/
theorem integral_indicator_char {V : Type} [AddCommGroup V] [TopologicalSpace V] [IsTopologicalAddGroup V]
    [MeasurableSpace V] [BorelSpace V] (μ : Measure V) [μ.IsAddHaarMeasure] (M : AddSubgroup V)
    (hMo : IsOpen (M : Set V)) (χ : V → ℂ) (hχ : ∀ a b, χ (a + b) = χ a * χ b) :
    ∫ m, (M : Set V).indicator χ m ∂μ = if ∀ m ∈ M, χ m = 1 then (μ.real (M : Set V) : ℂ) else 0 := by
  classical
  split_ifs with h
  · rw [show (M : Set V).indicator χ = (M : Set V).indicator (fun _ => (1 : ℂ)) from
      Set.indicator_congr (fun m hm => h m hm), integral_indicator_const _ hMo.measurableSet]
    simp
  · push Not at h
    obtain ⟨m0, hm0, h1⟩ := h
    refine AbsInv.integral_eq_zero_of_translate μ _ m0 (χ m0) h1 fun m => ?_
    by_cases hm : m ∈ M
    · rw [Set.indicator_of_mem (by exact M.add_mem hm hm0), Set.indicator_of_mem (by exact hm), hχ, mul_comm]
    · have h2 : m + m0 ∉ M := fun h' => hm (by simpa using M.sub_mem h' hm0)
      rw [Set.indicator_of_notMem (by exact h2), Set.indicator_of_notMem (by exact hm), mul_zero]

end GlobalTheory.JR.WeilQuad.GaussStable

open GlobalTheory.JR.WeilQuad.GaussStable in

/- English proof (translation)
Introduce `F E _ _ _ _ hU A ψ x μ ω h u`. Take `⟨-, -, hψ, hsd, -⟩` from `h`. Use `haveI := hsd.1`. Use `haveI : IsUltrametricDist F := hU.ultraF`. Use `haveI : LocallyCompactSpace F := hU.lcF`.

Use `haveI := EtMeas.finite_L A`. Use `haveI : IsTopologicalAddGroup A.L := IsModuleTopology.topologicalAddGroup F A.L`. Use `set β := EtMeas.formL A ((u * x : A.Kˣ) : A.K) with hβ`. Use `set f : A.L → ℂ := fun y => A.psiK ψ ((u : A.K) * x * A.NL y) with hf`. Establish `htr : Continuous (Algebra.trace F A.K)` using `IsModuleTopology.continuous_of_linearMap _`.

Establish `hin : Continuous fun y : A.L => Algebra.trace F A.K ((u : A.K) * x * A.NL y)` using `htr.comp (continuous_const.mul (GlobalTheory.JR.EtMeas.continuous_NL A))`. Establish `hflc : IsLocallyConstant f` using `(isLocallyConstant_of_stdChar hψ).comp_continuous hin`. Establish `hfc : Continuous f` using `hflc.continuous`. Establish `hkey : ∀ y m, f (y + m) = f y * ψ (β m y) * f m`. Introduce `y m`.

Simplify using `only [hf, hβ, EtMeas.formL_apply, Units.val_mul, NL_add A, Et.psiK, mul_add, map_add, AddChar.map_add_eq_mul]`. Establish `hf0 : f 0 = 1` using `by simp [hf, NL_zero A, Et.psiK]`. Take `⟨-, hsmall⟩` from `GlobalTheory.JR.exists_small_dual_lattices F ψ hψ A.L β (formL_symm_nondeg A (u * x)).1 (formL_symm_nondeg A (u * x)).2`. Take `⟨M, N, hMU, hMo, hMc, hNo, hNc, hN, -⟩` from `hsmall {y | f y = 1} ((hflc.isOpen_fiber 1).mem_nhds hf0)`. Establish `hfM : ∀ m ∈ M, f m = 1` using `fun m hm => hMU hm`.

Establish `hMpos : μ.real (M : Set A.L) ≠ 0` using `(ENNReal.toReal_pos (hMo.measure_pos μ ⟨0, M.zero_mem⟩).ne' hMc.measure_lt_top.ne).ne'`. Use `⟨∫ y in (N : Set A.L), f y ∂μ, M ⊔ N, AddSubgroup.isOpen_mono le_sup_left hMo, ?_, ?_⟩` and prove the remaining obligations. Use `(hMc.add hNc).of_isClosed_subset (AddSubgroup.isClosed_of_isOpen _ (AddSubgroup.isOpen_mono le_sup_left hMo)) ?_` and prove the remaining obligations. Introduce `z hz`. Take `⟨a, ha, b, hb, rfl⟩` from `AddSubgroup.mem_sup.1 hz`.

Conclude with `Set.add_mem_add ha hb`. Introduce `Λ hΛo hΛc hle`. Establish `hMΛ : M ≤ Λ` using `le_sup_left.trans hle`. Establish `hNΛ : N ≤ Λ` using `le_sup_right.trans hle`. Use `set iM : A.L → ℂ := (M : Set A.L).indicator (fun _ => 1) with hiM`.

Use `set iΛ : A.L → ℂ := (Λ : Set A.L).indicator (fun _ => 1) with hiΛ`. Establish `hiMc : Continuous iM` using `IsClopen.continuous_indicator ⟨AddSubgroup.isClosed_of_isOpen _ hMo, hMo⟩ continuous_const`. Establish `hiΛc : Continuous iΛ` using `IsClopen.continuous_indicator ⟨AddSubgroup.isClosed_of_isOpen _ hΛo, hΛo⟩ continuous_const`. Set `g : A.L → A.L → ℂ` to `fun m y => iM m * (iΛ y * f (y + m))`. Establish `hgc : Continuous (Function.uncurry g)` using `(hiMc.comp continuous_fst).mul ((hiΛc.comp continuous_snd).mul (hfc.comp (continuous_snd.add continuous_fst)))`.

Establish `hgs : HasCompactSupport (Function.uncurry g)`. Use `HasCompactSupport.intro (hMc.prod hΛc) ?_` and prove the remaining obligations. Introduce and unpack `⟨m, y⟩ hp`. Simplify using `only [Set.mem_prod, not_and_or] at hp`. Break down `hp with hp | hp` into its components or cases.

Establish `: iM m = 0` using `by rw [hiM, Set.indicator_of_notMem hp]`. Simplify using `[Function.uncurry, g, this]`. Establish `: iΛ y = 0` using `by rw [hiΛ, Set.indicator_of_notMem hp]`. Simplify using `[Function.uncurry, g, this]`. Establish `hswap` using `integral_integral_swap_of_hasCompactSupport hgc hgs (μ := μ) (ν := μ)`.

Establish `hA : ∀ m, ∫ y, g m y ∂μ = iM m * ∫ y in (Λ : Set A.L), f y ∂μ`. Introduce `m`. Distinguish the cases in `hm : m ∈ M`. Establish `e : ∀ y, iΛ y * f (y + m) = (Λ : Set A.L).indicator f (y + m)`. Introduce `y`.

Distinguish the cases in `hy : y ∈ Λ`. Rewrite using `[hiΛ, Set.indicator_of_mem (by exact hy), Set.indicator_of_mem (by exact Λ.add_mem hy (hMΛ hm)), one_mul]`. Establish `h2 : y + m ∉ Λ` using `fun h' => hy (by simpa using Λ.sub_mem h' (hMΛ hm))`. Rewrite using `[hiΛ, Set.indicator_of_notMem (by exact hy), Set.indicator_of_notMem (by exact h2), zero_mul]`. Simplify using `only [g]`.

Rewrite using `[integral_const_mul]`. Use `congr 1`. Repeatedly rewrite using `[e]`. Rewrite using `[integral_add_right_eq_self (μ := μ) ((Λ : Set A.L).indicator f) m, integral_indicator hΛo.measurableSet]`. Establish `h1 : iM m = 0` using `by rw [hiM, Set.indicator_of_notMem (by exact hm)]`.

Simplify using `[g, h1]`. Establish `hB : ∀ y, ∫ m, g m y ∂μ = (N : Set A.L).indicator (fun y => (μ.real (M : Set A.L) : ℂ) * f y) y`. Introduce `y`. Establish `e : ∀ m, g m y = iΛ y * f y * (M : Set A.L).indicator (fun m => ψ (β m y)) m`. Introduce `m`.

Distinguish the cases in `hm : m ∈ M`. Establish `h1 : iM m = 1` using `by rw [hiM, Set.indicator_of_mem (by exact hm)]`. Establish `h2 : (M : Set A.L).indicator (fun m => ψ (β m y)) m = ψ (β m y)` using `Set.indicator_of_mem (by exact hm) _`. Simplify using `only [g]`. Rewrite using `[h1, h2, hkey, hfM m hm]`.

Expand and normalize the polynomial expressions, which then agree. Establish `h1 : iM m = 0` using `by rw [hiM, Set.indicator_of_notMem (by exact hm)]`. Establish `h2 : (M : Set A.L).indicator (fun m => ψ (β m y)) m = 0` using `Set.indicator_of_notMem (by exact hm) _`. Simplify using `only [g]`. Rewrite using `[h1, h2]`.

Expand and normalize the polynomial expressions, which then agree. Repeatedly rewrite using `[e]`. Rewrite using `[integral_const_mul, integral_indicator_char μ M hMo (fun m => ψ (β m y)) (fun a b => by simp [map_add, AddChar.map_add_eq_mul])]`. Distinguish the cases in `hy : y ∈ N`. Rewrite using `[if_pos ((hN y).1 hy), Set.indicator_of_mem (by exact hy), hiΛ, Set.indicator_of_mem (by exact hNΛ hy)]`.

Expand and normalize the polynomial expressions, which then agree. Rewrite using `[if_neg (fun h' => hy ((hN y).2 h')), Set.indicator_of_notMem (by exact hy), mul_zero]`. Establish `h1 : ∫ m, ∫ y, g m y ∂μ ∂μ = (μ.real (M : Set A.L) : ℂ) * ∫ y in (Λ : Set A.L), f y ∂μ`. Repeatedly rewrite using `[hA]`. Rewrite using `[integral_mul_const, hiM, integral_indicator_const _ hMo.measurableSet]`.

Simplify using the standard rewrite rules. Establish `h2 : ∫ y, ∫ m, g m y ∂μ ∂μ = (μ.real (M : Set A.L) : ℂ) * ∫ y in (N : Set A.L), f y ∂μ`. Repeatedly rewrite using `[hB]`. Rewrite using `[integral_indicator hNo.measurableSet, integral_const_mul]`. Establish `hmain` using `h1.symm.trans (hswap.trans h2)`.

Unfold `gaussInt`. Conclude with `mul_left_cancel₀ (Complex.ofReal_ne_zero.2 hMpos) hmain`.
-/
theorem GlobalTheory.JR.WeilQuad.exists_stableGauss : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E]
    [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E) (ψ : AddChar F ℂ) (x : A.Kˣ) (μ : Measure A.L)
    (ω : A.K → ℂ), Hyp A ψ x μ ω → ∀ u : A.Kˣ, ∃ G, IsStableGauss A ψ x μ u G := by
  intro F E _ _ _ _ hU A ψ x μ ω h u
  classical
  obtain ⟨-, -, hψ, hsd, -⟩ := h
  haveI := hsd.1
  haveI : IsUltrametricDist F := hU.ultraF
  haveI : LocallyCompactSpace F := hU.lcF
  haveI := EtMeas.finite_L A
  haveI : IsTopologicalAddGroup A.L := IsModuleTopology.topologicalAddGroup F A.L
  set β := EtMeas.formL A ((u * x : A.Kˣ) : A.K) with hβ
  set f : A.L → ℂ := fun y => A.psiK ψ ((u : A.K) * x * A.NL y) with hf
  have htr : Continuous (Algebra.trace F A.K) := IsModuleTopology.continuous_of_linearMap _
  have hin : Continuous fun y : A.L => Algebra.trace F A.K ((u : A.K) * x * A.NL y) :=
    htr.comp (continuous_const.mul (GlobalTheory.JR.EtMeas.continuous_NL A))
  have hflc : IsLocallyConstant f := (isLocallyConstant_of_stdChar hψ).comp_continuous hin
  have hfc : Continuous f := hflc.continuous
  have hkey : ∀ y m, f (y + m) = f y * ψ (β m y) * f m := by
    intro y m
    simp only [hf, hβ, EtMeas.formL_apply, Units.val_mul, NL_add A, Et.psiK, mul_add, map_add,
      AddChar.map_add_eq_mul]
  have hf0 : f 0 = 1 := by simp [hf, NL_zero A, Et.psiK]
  obtain ⟨-, hsmall⟩ := GlobalTheory.JR.exists_small_dual_lattices F ψ hψ A.L β
    (formL_symm_nondeg A (u * x)).1 (formL_symm_nondeg A (u * x)).2
  obtain ⟨M, N, hMU, hMo, hMc, hNo, hNc, hN, -⟩ :=
    hsmall {y | f y = 1} ((hflc.isOpen_fiber 1).mem_nhds hf0)
  have hfM : ∀ m ∈ M, f m = 1 := fun m hm => hMU hm
  have hMpos : μ.real (M : Set A.L) ≠ 0 :=
    (ENNReal.toReal_pos (hMo.measure_pos μ ⟨0, M.zero_mem⟩).ne' hMc.measure_lt_top.ne).ne'
  refine ⟨∫ y in (N : Set A.L), f y ∂μ, M ⊔ N, AddSubgroup.isOpen_mono le_sup_left hMo, ?_, ?_⟩
  · refine (hMc.add hNc).of_isClosed_subset
      (AddSubgroup.isClosed_of_isOpen _ (AddSubgroup.isOpen_mono le_sup_left hMo)) ?_
    intro z hz
    obtain ⟨a, ha, b, hb, rfl⟩ := AddSubgroup.mem_sup.1 hz
    exact Set.add_mem_add ha hb
  intro Λ hΛo hΛc hle
  have hMΛ : M ≤ Λ := le_sup_left.trans hle
  have hNΛ : N ≤ Λ := le_sup_right.trans hle
  set iM : A.L → ℂ := (M : Set A.L).indicator (fun _ => 1) with hiM
  set iΛ : A.L → ℂ := (Λ : Set A.L).indicator (fun _ => 1) with hiΛ
  have hiMc : Continuous iM :=
    IsClopen.continuous_indicator ⟨AddSubgroup.isClosed_of_isOpen _ hMo, hMo⟩ continuous_const
  have hiΛc : Continuous iΛ :=
    IsClopen.continuous_indicator ⟨AddSubgroup.isClosed_of_isOpen _ hΛo, hΛo⟩ continuous_const
  let g : A.L → A.L → ℂ := fun m y => iM m * (iΛ y * f (y + m))
  have hgc : Continuous (Function.uncurry g) :=
    (hiMc.comp continuous_fst).mul ((hiΛc.comp continuous_snd).mul (hfc.comp (continuous_snd.add continuous_fst)))
  have hgs : HasCompactSupport (Function.uncurry g) := by
    refine HasCompactSupport.intro (hMc.prod hΛc) ?_
    rintro ⟨m, y⟩ hp
    simp only [Set.mem_prod, not_and_or] at hp
    rcases hp with hp | hp
    · have : iM m = 0 := by rw [hiM, Set.indicator_of_notMem hp]
      simp [Function.uncurry, g, this]
    · have : iΛ y = 0 := by rw [hiΛ, Set.indicator_of_notMem hp]
      simp [Function.uncurry, g, this]
  have hswap := integral_integral_swap_of_hasCompactSupport hgc hgs (μ := μ) (ν := μ)
  have hA : ∀ m, ∫ y, g m y ∂μ = iM m * ∫ y in (Λ : Set A.L), f y ∂μ := by
    intro m
    by_cases hm : m ∈ M
    · have e : ∀ y, iΛ y * f (y + m) = (Λ : Set A.L).indicator f (y + m) := by
        intro y
        by_cases hy : y ∈ Λ
        · rw [hiΛ, Set.indicator_of_mem (by exact hy), Set.indicator_of_mem (by exact Λ.add_mem hy (hMΛ hm)), one_mul]
        · have h2 : y + m ∉ Λ := fun h' => hy (by simpa using Λ.sub_mem h' (hMΛ hm))
          rw [hiΛ, Set.indicator_of_notMem (by exact hy), Set.indicator_of_notMem (by exact h2), zero_mul]
      simp only [g]
      rw [integral_const_mul]
      congr 1
      simp_rw [e]
      rw [integral_add_right_eq_self (μ := μ) ((Λ : Set A.L).indicator f) m,
        integral_indicator hΛo.measurableSet]
    · have h1 : iM m = 0 := by rw [hiM, Set.indicator_of_notMem (by exact hm)]
      simp [g, h1]
  have hB : ∀ y, ∫ m, g m y ∂μ = (N : Set A.L).indicator (fun y => (μ.real (M : Set A.L) : ℂ) * f y) y := by
    intro y
    have e : ∀ m, g m y = iΛ y * f y * (M : Set A.L).indicator (fun m => ψ (β m y)) m := by
      intro m
      by_cases hm : m ∈ M
      · have h1 : iM m = 1 := by rw [hiM, Set.indicator_of_mem (by exact hm)]
        have h2 : (M : Set A.L).indicator (fun m => ψ (β m y)) m = ψ (β m y) :=
          Set.indicator_of_mem (by exact hm) _
        simp only [g]
        rw [h1, h2, hkey, hfM m hm]; ring
      · have h1 : iM m = 0 := by rw [hiM, Set.indicator_of_notMem (by exact hm)]
        have h2 : (M : Set A.L).indicator (fun m => ψ (β m y)) m = 0 :=
          Set.indicator_of_notMem (by exact hm) _
        simp only [g]
        rw [h1, h2]; ring
    simp_rw [e]
    rw [integral_const_mul, integral_indicator_char μ M hMo (fun m => ψ (β m y))
      (fun a b => by simp [map_add, AddChar.map_add_eq_mul])]
    by_cases hy : y ∈ N
    · rw [if_pos ((hN y).1 hy), Set.indicator_of_mem (by exact hy), hiΛ, Set.indicator_of_mem (by exact hNΛ hy)]
      ring
    · rw [if_neg (fun h' => hy ((hN y).2 h')), Set.indicator_of_notMem (by exact hy), mul_zero]
  have h1 : ∫ m, ∫ y, g m y ∂μ ∂μ = (μ.real (M : Set A.L) : ℂ) * ∫ y in (Λ : Set A.L), f y ∂μ := by
    simp_rw [hA]
    rw [integral_mul_const, hiM, integral_indicator_const _ hMo.measurableSet]
    simp
  have h2 : ∫ y, ∫ m, g m y ∂μ ∂μ = (μ.real (M : Set A.L) : ℂ) * ∫ y in (N : Set A.L), f y ∂μ := by
    simp_rw [hB]
    rw [integral_indicator hNo.measurableSet, integral_const_mul]
  have hmain := h1.symm.trans (hswap.trans h2)
  unfold gaussInt
  exact mul_left_cancel₀ (Complex.ofReal_ne_zero.2 hMpos) hmain

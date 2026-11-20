import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsRapidInf
import GroundTheory.AutomorphicForms.MultiplicityOne.Equivariance
import GroundTheory.GlobalFields.TateThesis.AdelicCharLocal

noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory

namespace GlobalTheory.JSW.WhitModel

open GlobalTheory.CuspRep GroundTheory.Automorphic GroundTheory.Automorphic.FourierWhittaker

variable {E : Type} [Field E] [NumberField E] {a : ℕ}

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨h0, h1⟩`. Use `⟨fun p => (u : Matrix (Fin a) (Fin a) (Ad E)) p.1.1 p.1.2, Units.ext ?_⟩` and prove the remaining obligations. Use `Matrix.ext fun i j => ?_` and prove the remaining obligations. Rewrite using `[coe_uGL, uMat_apply]`.

Use `split_ifs with h h'`. Substitute `h` using the available equality. Conclude with `h1 i`. Both sides reduce to the same expression. Conclude with `h0 i j (lt_of_le_of_ne (not_lt.1 h') (Ne.symm h))`.

Introduce and unpack `⟨X, rfl⟩`. Use `⟨fun i j h => ?_, fun i => ?_⟩` and prove the remaining obligations. Rewrite using `[coe_uGL, uMat_apply, if_neg (ne_of_gt h), dif_neg (not_lt.2 h.le)]`. Rewrite using `[coe_uGL, uMat_apply, if_pos rfl]`.
-/
theorem mem_NA_iff (u : GA E a) : u ∈ NA E a ↔ ∃ X : Pos a → Ad E, u = uGL X := by
  constructor
  · rintro ⟨h0, h1⟩
    refine ⟨fun p => (u : Matrix (Fin a) (Fin a) (Ad E)) p.1.1 p.1.2, Units.ext ?_⟩
    refine Matrix.ext fun i j => ?_
    rw [coe_uGL, uMat_apply]
    split_ifs with h h'
    · subst h; exact h1 i
    · rfl
    · exact h0 i j (lt_of_le_of_ne (not_lt.1 h') (Ne.symm h))
  · rintro ⟨X, rfl⟩
    refine ⟨fun i j h => ?_, fun i => ?_⟩
    · rw [coe_uGL, uMat_apply, if_neg (ne_of_gt h), dif_neg (not_lt.2 h.le)]
    · rw [coe_uGL, uMat_apply, if_pos rfl]

/- English proof (translation)
Unfold `GlobalTheory.Whittaker.superDiag supSum`. Use `(Finset.sum_sigma' _ _ _).trans ?_` and prove the remaining obligations. Use `symm`. Use `Finset.sum_bij (fun p _ => ⟨p.1.1, p.1.2⟩) ?_ ?_ ?_ ?_` and prove the remaining obligations. Introduce `p hp`.

Simplify using `only [Finset.mem_filter, Finset.mem_univ, true_and] at hp`. Simplify using `[hp.1]`. Introduce `p _ q _ h`. Simplify using `only [Sigma.mk.injEq, heq_eq_eq] at h`. Conclude with `Subtype.ext (Prod.ext h.1 h.2)`.

Introduce and unpack `⟨i, j⟩ h`. Simplify using `only [Finset.mem_sigma, Finset.mem_filter, Finset.mem_univ, true_and] at h`. Conclude with `⟨⟨(i, j), by rw [Fin.lt_def]; simp only; omega⟩, by simp [h], rfl⟩`. Introduce `p _`. Simplify using `only [coe_uGL, uMat_apply]`.

Rewrite using `[if_neg (ne_of_lt p.2), dif_pos p.2]`.
-/
theorem superDiag_uGL (X : Pos a → Ad E) : GlobalTheory.Whittaker.superDiag (uGL X) = supSum 0 X := by
  classical
  unfold GlobalTheory.Whittaker.superDiag supSum
  refine (Finset.sum_sigma' _ _ _).trans ?_
  symm
  refine Finset.sum_bij (fun p _ => ⟨p.1.1, p.1.2⟩) ?_ ?_ ?_ ?_
  · intro p hp
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp
    simp [hp.1]
  · intro p _ q _ h
    simp only [Sigma.mk.injEq, heq_eq_eq] at h
    exact Subtype.ext (Prod.ext h.1 h.2)
  · rintro ⟨i, j⟩ h
    simp only [Finset.mem_sigma, Finset.mem_filter, Finset.mem_univ, true_and] at h
    exact ⟨⟨(i, j), by rw [Fin.lt_def]; simp only; omega⟩, by simp [h], rfl⟩
  · intro p _
    simp only [coe_uGL, uMat_apply]
    rw [if_neg (ne_of_lt p.2), dif_pos p.2]

/- English proof (translation)
Take `⟨X, rfl⟩` from `(mem_NA_iff u).1 hu`. Rewrite using `[psiN, superDiag_uGL]`. Conclude with `MultiplicityOne.whittaker_uGL_mul hc hl X g`.
-/
theorem whit_mul {F : GA E a → ℂ} (hc : Continuous F) (hl : AutomorphicForm.IsLeftInvariant F) {u : GA E a}
    (hu : u ∈ NA E a) (g : GA E a) : whit F (u * g) = psiN u * whit F g := by
  obtain ⟨X, rfl⟩ := (mem_NA_iff u).1 hu
  rw [psiN, superDiag_uGL]
  exact MultiplicityOne.whittaker_uGL_mul hc hl X g

/- English proof (translation)
Rewrite using `[whit, whittaker_eq_partialCoeff hc one_pos, partialCoeff_self]`.
-/
theorem whit_rank_one {F : GA E 1 → ℂ} (hc : Continuous F) (g : GA E 1) : whit F g = F g := by
  rw [whit, whittaker_eq_partialCoeff hc one_pos, partialCoeff_self]

/- English proof (translation)
Assume the negation of the conclusion as `h`. Use `push Not at h`. Use `GroundTheory.Global.adelicChar_ne_one (K := E) (AddChar.ext _ _ fun x => ?_)` and prove the remaining obligations. Establish `h1` using `h (uGL fun _ => x) ((mem_NA_iff _).2 ⟨_, rfl⟩)`. Establish `h2 : GlobalTheory.Whittaker.superDiag (uGL (n` using `2) fun _ => x) = x := by`.

Simplify using `[GlobalTheory.Whittaker.superDiag, Finset.sum_filter, uMat_apply]`. Rewrite `h1` using `[psiN, h2]`. Conclude with `Subtype.ext h1`.
-/
theorem exists_psiN_ne_one : ∃ u ∈ NA E 2, psiN u ≠ 1 := by
  by_contra h
  push Not at h
  refine GroundTheory.Global.adelicChar_ne_one (K := E) (AddChar.ext _ _ fun x => ?_)
  have h1 := h (uGL fun _ => x) ((mem_NA_iff _).2 ⟨_, rfl⟩)
  have h2 : GlobalTheory.Whittaker.superDiag (uGL (n := 2) fun _ => x) = x := by
    simp [GlobalTheory.Whittaker.superDiag, Finset.sum_filter, uMat_apply]
  rw [psiN, h2] at h1
  exact Subtype.ext h1

/- English proof (translation)
Take `⟨u, hu, h⟩` from `exists_psiN_ne_one (E := E)`. Establish `h1` using `whit_mul (F := fun _ : GA E 2 => (1 : ℂ)) continuous_const (fun _ _ => rfl) hu 1`. Establish `h2 : whit (fun _ : GA E 2 => (1 : ℂ)) (u * 1) = whit (fun _ : GA E 2 => (1 : ℂ)) 1` using `rfl`. Rewrite `h1` using `[h2]`. Assume the negation of the conclusion as `h0`.

Conclude with `h ((mul_eq_right₀ h0).1 h1.symm)`.
-/
theorem whit_const_two : whit (fun _ : GA E 2 => (1 : ℂ)) 1 = 0 := by
  obtain ⟨u, hu, h⟩ := exists_psiN_ne_one (E := E)
  have h1 := whit_mul (F := fun _ : GA E 2 => (1 : ℂ)) continuous_const (fun _ _ => rfl) hu 1
  have h2 : whit (fun _ : GA E 2 => (1 : ℂ)) (u * 1) = whit (fun _ : GA E 2 => (1 : ℂ)) 1 := rfl
  rw [h2] at h1
  by_contra h0
  exact h ((mul_eq_right₀ h0).1 h1.symm)

/- English proof (translation)
Rewrite using `[psiLoc, GroundTheory.Global.localAdelicChar_apply]`. Use `congr 2`.
-/
theorem psiLoc_eq (w : HeightOneSpectrum (𝓞 E)) (x : w.adicCompletion E) :
    psiLoc w x = (GroundTheory.Global.localAdelicChar E w x : ℂ) := by
  classical
  rw [psiLoc, GroundTheory.Global.localAdelicChar_apply]
  congr 2

/- English proof (translation)
Simplify using `[diagPow]`.
-/
theorem diagPow_val {K : Type} [CommRing K] {n : ℕ} (ϖ : Kˣ) (l : Fin n → ℕ) :
    (diagPow ϖ l : Matrix (Fin n) (Fin n) K) = Matrix.diagonal fun i => (ϖ : K) ^ l i := by
  simp [diagPow]

/- English proof (translation)
The claim follows from `Units.ext (by rw [diagPow_val]; simp)`.
-/
theorem diagPow_zero {K : Type} [CommRing K] {n : ℕ} (ϖ : Kˣ) : diagPow ϖ (0 : Fin n → ℕ) = 1 :=
  Units.ext (by rw [diagPow_val]; simp)

/- English proof (translation)
Establish `hc : ∀ g : GA E a, GeneralLinearGroup.map ((pLoc E w).comp (pFin E)) g = GeneralLinearGroup.map (pLoc E w) (GeneralLinearGroup.map (pFin E) g)` using `fun _ => rfl`. Establish `key : ∀ L : List (HeightOneSpectrum (𝓞 E)), L.Nodup → GeneralLinearGroup.map ((pLoc E w).comp (pFin E)) (L.map fun v => finGL E a (locGL E a v (diagPow (ϖ v) (l v)))).prod = if w ∈ L then diagPow (ϖ w) (l w) else 1`. Introduce `L hL`. Proceed by induction on `L with`. Consider the case `nil => simp`.

Consider the case `cons v L ih`. Rewrite `hL` using `[List.nodup_cons]`. Rewrite using `[List.map_cons, List.prod_cons, map_mul, ih hL.2, hc, pFin_finGL]`. Distinguish the cases in `h : w = v`. Substitute `h` using the available equality.

Rewrite using `[pLoc_locGL, if_neg hL.1, if_pos List.mem_cons_self, mul_one]`. Rewrite using `[pLoc_locGL_of_ne h, one_mul]`. Simplify using `[h]`. Rewrite using `[tl, key _ (Finset.nodup_toList _)]`. Use `split_ifs with h`.

Both sides reduce to the same expression. Rewrite `h` using `[Finset.mem_toList, Finsupp.notMem_support_iff]`. Rewrite using `[h, diagPow_zero]`.
-/
theorem tl_comp (ϖ : ∀ w : HeightOneSpectrum (𝓞 E), (w.adicCompletion E)ˣ) (l : HeightOneSpectrum (𝓞 E) →₀ (Fin a → ℕ))
    (w : HeightOneSpectrum (𝓞 E)) :
    GeneralLinearGroup.map ((pLoc E w).comp (pFin E)) (tl ϖ l) = diagPow (ϖ w) (l w) := by
  classical
  have hc : ∀ g : GA E a, GeneralLinearGroup.map ((pLoc E w).comp (pFin E)) g =
      GeneralLinearGroup.map (pLoc E w) (GeneralLinearGroup.map (pFin E) g) := fun _ => rfl
  have key : ∀ L : List (HeightOneSpectrum (𝓞 E)), L.Nodup →
      GeneralLinearGroup.map ((pLoc E w).comp (pFin E))
        (L.map fun v => finGL E a (locGL E a v (diagPow (ϖ v) (l v)))).prod =
        if w ∈ L then diagPow (ϖ w) (l w) else 1 := by
    intro L hL
    induction L with
    | nil => simp
    | cons v L ih =>
      rw [List.nodup_cons] at hL
      rw [List.map_cons, List.prod_cons, map_mul, ih hL.2, hc, pFin_finGL]
      by_cases h : w = v
      · subst h; rw [pLoc_locGL, if_neg hL.1, if_pos List.mem_cons_self, mul_one]
      · rw [pLoc_locGL_of_ne h, one_mul]; simp [h]
  rw [tl, key _ (Finset.nodup_toList _)]
  split_ifs with h
  · rfl
  · rw [Finset.mem_toList, Finsupp.notMem_support_iff] at h
    rw [h, diagPow_zero]

/- English proof (translation)
Establish `hc : ∀ v, ∀ g : GA E a, GeneralLinearGroup.map ((pLoc E v).comp (pFin E)) g = GeneralLinearGroup.map (pLoc E v) (GeneralLinearGroup.map (pFin E) g)` using `fun _ _ => rfl`. Prove the components needed by the constructor for the conclusion. Introduce `h`. Distinguish the cases in `hw : w ∈ S`. Conclude with `Or.inl hw`.

Use `h w hw` as an intermediate fact. Rewrite `this` using `[hc, pFin_finGL, pLoc_locGL]`. Conclude with `Or.inr this`. Introduce and unpack `(h | rfl) v hv`. Rewrite using `[hc, pFin_finGL, pLoc_locGL_of_ne (fun e : v = w => hv (by rw [e]; exact h))]`.

Simplify using the standard rewrite rules.
-/
theorem loc_mem_supS (S : Finset (HeightOneSpectrum (𝓞 E))) (w : HeightOneSpectrum (𝓞 E))
    (g : GL (Fin a) (w.adicCompletion E)) : finGL E a (locGL E a w g) ∈ supS E a S ↔ w ∈ S ∨ g = 1 := by
  have hc : ∀ v, ∀ g : GA E a, GeneralLinearGroup.map ((pLoc E v).comp (pFin E)) g =
      GeneralLinearGroup.map (pLoc E v) (GeneralLinearGroup.map (pFin E) g) := fun _ _ => rfl
  constructor
  · intro h
    by_cases hw : w ∈ S
    · exact Or.inl hw
    · have := h w hw
      rw [hc, pFin_finGL, pLoc_locGL] at this
      exact Or.inr this
  · rintro (h | rfl) v hv
    · rw [hc, pFin_finGL, pLoc_locGL_of_ne (fun e : v = w => hv (by rw [e]; exact h))]
    · simp

/- English proof (translation)
Introduce and unpack `u ⟨⟨h0, h1⟩, hS⟩`. Use `⟨hS, fun j => ?_⟩` and prove the remaining obligations. Use `split_ifs with h`. Substitute `h` using the available equality. Conclude with `h1 _`.

Conclude with `h0 _ _ (lt_of_le_of_ne (Fin.le_last j) h)`.
-/
theorem NA_inter_supS_subset (S : Finset (HeightOneSpectrum (𝓞 E))) (m : ℕ) :
    NA E (m + 1) ∩ supS E (m + 1) S ⊆ mirS E S m := by
  rintro u ⟨⟨h0, h1⟩, hS⟩
  refine ⟨hS, fun j => ?_⟩
  split_ifs with h
  · subst h; exact h1 _
  · exact h0 _ _ (lt_of_le_of_ne (Fin.le_last j) h)

/- English proof (translation)
Assemble the required witnesses or components as `⟨measurable_const, measurable_const, fun _ => integrable_const _⟩`.
-/
theorem isRapidInf_dirac (c : ℂ) (y : GL (Fin a) (Cinf E)) :
    IsRapidInf (Measure.dirac ()) (fun _ => c) (fun _ : Unit => y) :=
  ⟨measurable_const, measurable_const, fun _ => integrable_const _⟩

/- English proof (translation)
Introduce and unpack `⟨-, -, h⟩`. Use `h 0` as an intermediate fact. Simplify using `[integrable_const_iff] at this`. Conclude with `(measure_ne_top (volume : Measure ℝ) Set.univ) Real.volume_univ`.
-/
theorem not_isRapidInf_const : ¬ IsRapidInf (volume : Measure ℝ) (fun _ => 1) (fun _ => (1 : GL (Fin a) (Cinf E))) := by
  rintro ⟨-, -, h⟩
  have := h 0
  simp [integrable_const_iff] at this
  exact (measure_ne_top (volume : Measure ℝ) Set.univ) Real.volume_univ

variable [IsTotallyComplex E]

/- English proof (translation)
Introduce `v _`. Express the relevant statement in the definitionally equal form `GeneralLinearGroup.map (pLoc E v) (GeneralLinearGroup.map (pFin E) (infGL E a y)) = 1`. Rewrite using `[pFin_infGL]`. Conclude with `map_one _`.
-/
theorem inf_mem_supS (S : Finset (HeightOneSpectrum (𝓞 E))) (y : GL (Fin a) (Cinf E)) : infGL E a y ∈ supS E a S := by
  intro v _
  change GeneralLinearGroup.map (pLoc E v) (GeneralLinearGroup.map (pFin E) (infGL E a y)) = 1
  rw [pFin_infGL]; exact map_one _

/- English proof (translation)
Apply `le_antisymm` to reduce the goal to its premises. Use `sInf_le ⟨fun φ hφ => ?_, fun F hF h => ?_, fun F hF X _ ν _ k γ _ => ?_⟩` and prove the remaining obligations. Take `⟨c, rfl⟩` from `Submodule.mem_span_singleton.1 hφ`. Conclude with `Submodule.mem_span_singleton.2 ⟨c, rfl⟩`. Take `⟨c, rfl⟩` from `Submodule.mem_span_singleton.1 hF`.

Conclude with `Submodule.mem_span_singleton.2 ⟨c, rfl⟩`. Take `⟨c, rfl⟩` from `Submodule.mem_span_singleton.1 hF`. Conclude with `Submodule.mem_span_singleton.2 ⟨∫ x, k x * c ∂ν, by funext g; simp⟩`. Use `le_sInf fun S hS => Submodule.span_le.2 ?_` and prove the remaining obligations. Introduce and unpack `_ rfl`.

Conclude with `hS.1 (oneFn E a) (Submodule.mem_span_singleton_self _)`.
-/
theorem mspanR_triv (ha : a ≤ 1) : mspanR (CuspSub.triv E ha) = Submodule.span ℂ {fun _ => 1} := by
  apply le_antisymm
  · refine sInf_le ⟨fun φ hφ => ?_, fun F hF h => ?_, fun F hF X _ ν _ k γ _ => ?_⟩
    · obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hφ
      exact Submodule.mem_span_singleton.2 ⟨c, rfl⟩
    · obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hF
      exact Submodule.mem_span_singleton.2 ⟨c, rfl⟩
    · obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hF
      exact Submodule.mem_span_singleton.2 ⟨∫ x, k x * c ∂ν, by funext g; simp⟩
  · refine le_sInf fun S hS => Submodule.span_le.2 ?_
    rintro _ rfl
    exact hS.1 (oneFn E a) (Submodule.mem_span_singleton_self _)

end GlobalTheory.JSW.WhitModel

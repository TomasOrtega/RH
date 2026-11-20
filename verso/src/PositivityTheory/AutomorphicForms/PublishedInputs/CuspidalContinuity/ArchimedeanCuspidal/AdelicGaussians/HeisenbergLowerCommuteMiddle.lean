import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.AdelicGaussians.UpperRightUnipotentInvariance

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix Filter Topology
open GroundTheory.Global GroundTheory.LocalField GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.FourierWhittaker (vecDomain vecMeasure pair)
open scoped NumberField.AdeleRing

namespace Ad3.GA.unipotentTranslateContinuity

local notation "𝔞" => algebraMap ℚ 𝔸[ℚ]

/- English proof (translation)
Rewrite using `[AddChar.map_add_eq_mul, Circle.coe_mul]`.
-/
theorem psi_add (a b : 𝔸[ℚ]) :
    (adelicChar ℚ (a + b) : ℂ) = (adelicChar ℚ a : ℂ) * (adelicChar ℚ b : ℂ) := by
  rw [AddChar.map_add_eq_mul, Circle.coe_mul]

/- English proof (translation)
Rewrite using `[adelicChar_algebraMap, Circle.coe_one]`.
-/
theorem psi_rat (q : ℚ) : (adelicChar ℚ (𝔞 q) : ℂ) = 1 := by
  rw [adelicChar_algebraMap, Circle.coe_one]

/- English proof (translation)
Rewrite using `[AddChar.map_zero_eq_one, Circle.coe_one]`.
-/
theorem psi_zero : (adelicChar ℚ 0 : ℂ) = 1 := by
  rw [AddChar.map_zero_eq_one, Circle.coe_one]

/- English proof (translation)
The claim follows from `Circle.norm_coe _`.
-/
theorem norm_psi (a : 𝔸[ℚ]) : ‖(adelicChar ℚ a : ℂ)‖ = 1 := Circle.norm_coe _

/- English proof (translation)
Assume the negation of the conclusion as `h`. Use `push Not at h`. Use `adelicChar_ne_one (K := ℚ) (DFunLike.ext _ _ fun b => ?_)` and prove the remaining obligations. Rewrite using `[AddChar.one_apply]`. Use `ext`.

Simplify using `using h b`.
-/
theorem exists_psi_ne_one : ∃ b : 𝔸[ℚ], (adelicChar ℚ b : ℂ) ≠ 1 := by
  by_contra h
  push Not at h
  refine adelicChar_ne_one (K := ℚ) (DFunLike.ext _ _ fun b => ?_)
  rw [AddChar.one_apply]
  ext
  simpa using h b

/- English proof (translation)
Combine the equalities or inequalities in the displayed calculation. Rewrite using `[psi_add]`. Expand and normalize the polynomial expressions, which then agree. Use `_ = w * (adelicChar ℚ (C + D) : ℂ) := by rw [e]`. Use `_ = _ := by rw [psi_add]; ring`.
-/
theorem psi_comb {A B C D : 𝔸[ℚ]} (e : A + B = C + D) (w : ℂ) :
    (adelicChar ℚ A : ℂ) * w * (adelicChar ℚ B : ℂ) =
      (adelicChar ℚ C : ℂ) * (w * (adelicChar ℚ D : ℂ)) := by
  calc (adelicChar ℚ A : ℂ) * w * (adelicChar ℚ B : ℂ) = w * (adelicChar ℚ (A + B) : ℂ) := by
        rw [psi_add]; ring
    _ = w * (adelicChar ℚ (C + D) : ℂ) := by rw [e]
    _ = _ := by rw [psi_add]; ring

def splitAt {ι : Type*} [DecidableEq ι] (i : ι) : ι ≃ {j // j ≠ i} ⊕ Unit where
  toFun j := if h : j = i then Sum.inr () else Sum.inl ⟨j, h⟩
  invFun := Sum.elim Subtype.val fun _ => i
  left_inv j := by
    by_cases h : j = i
    · subst h; simp
    · simp [h]
  right_inv p := by
    rcases p with ⟨j, hj⟩ | ⟨⟩
    · simp [hj]
    · simp

/- English proof (translation)
Rewrite using `[FourierWhittaker.setIntegral_vecDomain_sum (splitAt i) hc]`. Use `integral_eq_zero_of_ae (ae_of_all _ fun x => ?_)` and prove the remaining obligations. Set `G : (Unit → 𝔸[ℚ]) → ℂ` to `fun y => F fun j => Sum.elim x y (splitAt i j)`. Use `show ∫ y in vecDomain ℚ Unit, G y ∂vecMeasure ℚ Unit = 0`. Establish `hvec : ∀ (y a : Unit → 𝔸[ℚ]), (fun j => Sum.elim x (y + a) (splitAt i j)) = (fun j => Sum.elim x y (splitAt i j)) + Pi.single i (a ())`.

Introduce `y a`. Use function extensionality and compare the values at `j`. Distinguish the cases in `h : j = i`. Substitute `h` using the available equality. Simplify using `[splitAt]`.

Simplify using `[splitAt, h]`. Establish `hG : ∀ y a, G (y + a) = (adelicChar ℚ (𝔞 r * a ()) : ℂ) * G y`. Introduce `y a`. Simplify using `only [G, hvec, hF]`. Establish `hper : ∀ ξ ∈ FourierWhittaker.vecLattice ℚ Unit, ∀ y, G (ξ + y) = G y`.

Introduce `ξ hξ y`. Take `⟨η, rfl⟩` from `FourierWhittaker.mem_vecLattice.1 hξ`. Rewrite using `[add_comm, hG]`. Use `show (adelicChar ℚ (𝔞 r * 𝔞 (η ())) : ℂ) * G y = G y`. Rewrite using `[← map_mul, psi_rat, one_mul]`.

Take `⟨b, hb⟩` from `exists_psi_ne_one`. Establish `h1` using `FourierWhittaker.setIntegral_comp_add (fun _ => 𝔞 r⁻¹ * b) hper`. Establish `hrb : 𝔞 r * (𝔞 r⁻¹ * b) = b`. Rewrite using `[← mul_assoc, ← map_mul, mul_inv_cancel₀ hr, map_one, one_mul]`. Simplify using `only [hG, hrb] at h1`.

Rewrite `h1` using `[integral_const_mul]`. Establish `h2 : ((adelicChar ℚ b : ℂ) - 1) * ∫ y in vecDomain ℚ Unit, G y ∂vecMeasure ℚ Unit = 0`. Rewrite using `[sub_mul, one_mul, h1, sub_self]`. Conclude with `(mul_eq_zero.1 h2).resolve_left (sub_ne_zero.2 hb)`.
-/
theorem setIntegral_eq_zero_of_shift {ι : Type*} [Fintype ι] [DecidableEq ι]
    {F : (ι → 𝔸[ℚ]) → ℂ} (hc : Continuous F) (i : ι) {r : ℚ} (hr : r ≠ 0)
    (hF : ∀ y s, F (y + Pi.single i s) = (adelicChar ℚ (𝔞 r * s) : ℂ) * F y) :
    ∫ y in vecDomain ℚ ι, F y ∂vecMeasure ℚ ι = 0 := by
  rw [FourierWhittaker.setIntegral_vecDomain_sum (splitAt i) hc]
  refine integral_eq_zero_of_ae (ae_of_all _ fun x => ?_)
  let G : (Unit → 𝔸[ℚ]) → ℂ := fun y => F fun j => Sum.elim x y (splitAt i j)
  show ∫ y in vecDomain ℚ Unit, G y ∂vecMeasure ℚ Unit = 0
  have hvec : ∀ (y a : Unit → 𝔸[ℚ]), (fun j => Sum.elim x (y + a) (splitAt i j)) =
      (fun j => Sum.elim x y (splitAt i j)) + Pi.single i (a ()) := by
    intro y a
    funext j
    by_cases h : j = i
    · subst h; simp [splitAt]
    · simp [splitAt, h]
  have hG : ∀ y a, G (y + a) = (adelicChar ℚ (𝔞 r * a ()) : ℂ) * G y := by
    intro y a
    simp only [G, hvec, hF]
  have hper : ∀ ξ ∈ FourierWhittaker.vecLattice ℚ Unit, ∀ y, G (ξ + y) = G y := by
    intro ξ hξ y
    obtain ⟨η, rfl⟩ := FourierWhittaker.mem_vecLattice.1 hξ
    rw [add_comm, hG]
    show (adelicChar ℚ (𝔞 r * 𝔞 (η ())) : ℂ) * G y = G y
    rw [← map_mul, psi_rat, one_mul]
  obtain ⟨b, hb⟩ := exists_psi_ne_one
  have h1 := FourierWhittaker.setIntegral_comp_add (fun _ => 𝔞 r⁻¹ * b) hper
  have hrb : 𝔞 r * (𝔞 r⁻¹ * b) = b := by
    rw [← mul_assoc, ← map_mul, mul_inv_cancel₀ hr, map_one, one_mul]
  simp only [hG, hrb] at h1
  rw [integral_const_mul] at h1
  have h2 : ((adelicChar ℚ b : ℂ) - 1) * ∫ y in vecDomain ℚ Unit, G y ∂vecMeasure ℚ Unit = 0 := by
    rw [sub_mul, one_mul, h1, sub_self]
  exact (mul_eq_zero.1 h2).resolve_left (sub_ne_zero.2 hb)

/- English proof (translation)
Establish `key : ∀ y, F y = F 0`. Introduce `y`. Establish `: ∀ S : Finset ι, F (∑ i ∈ S, Pi.single i (y i)) = F 0`. Introduce `S`. Use `Finset.induction_on S (by simp) ?_` and prove the remaining obligations.

Introduce `a S ha ih`. Rewrite using `[Finset.sum_insert ha, add_comm, hF, ih]`. Rewrite using `[← this Finset.univ, Finset.univ_sum_single]`. Rewrite using `[setIntegral_congr_fun FourierWhittaker.measurableSet_vecDomain (fun y _ => key y), setIntegral_const, measureReal_def, FourierWhittaker.vecMeasure_vecDomain, ENNReal.toReal_one, one_smul]`.
-/
theorem setIntegral_eq_of_shift {ι : Type*} [Fintype ι] [DecidableEq ι] {F : (ι → 𝔸[ℚ]) → ℂ}
    (hF : ∀ y i s, F (y + Pi.single i s) = F y) :
    ∫ y in vecDomain ℚ ι, F y ∂vecMeasure ℚ ι = F 0 := by
  have key : ∀ y, F y = F 0 := by
    intro y
    have : ∀ S : Finset ι, F (∑ i ∈ S, Pi.single i (y i)) = F 0 := by
      intro S
      refine Finset.induction_on S (by simp) ?_
      intro a S ha ih
      rw [Finset.sum_insert ha, add_comm, hF, ih]
    rw [← this Finset.univ, Finset.univ_sum_single]
  rw [setIntegral_congr_fun FourierWhittaker.measurableSet_vecDomain (fun y _ => key y),
    setIntegral_const, measureReal_def, FourierWhittaker.vecMeasure_vecDomain, ENNReal.toReal_one,
    one_smul]

/- English proof (translation)
Establish `: IsFiniteMeasure ((vecMeasure ℚ ι).restrict (vecDomain ℚ ι))` using `⟨by`. Rewrite using `[Measure.restrict_apply_univ, FourierWhittaker.vecMeasure_vecDomain]`. Conclude with `ENNReal.one_lt_top⟩`. Establish `hint : ∀ q, Integrable (F q) ((vecMeasure ℚ ι).restrict (vecDomain ℚ ι))` using `fun q => Integrable.mono' (integrable_const (b q)) (hc q).aestronglyMeasurable ((ae_restrict_iff' FourierWhittaker.measurableSet_vecDomain).2 (ae_of_all _ (hle q)))`. Establish `hnorm : ∀ q, ∫ y in vecDomain ℚ ι, ‖F q y‖ ∂vecMeasure ℚ ι ≤ b q`.

Introduce `q`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[setIntegral_const, measureReal_def, FourierWhittaker.vecMeasure_vecDomain, ENNReal.toReal_one, one_smul]`. Conclude with `(integral_tsum_of_summable_integral_norm hint (Summable.of_nonneg_of_le (fun q => integral_nonneg fun _ => norm_nonneg _) hnorm hb)).symm`.
-/
theorem setIntegral_tsum_of_le {ι : Type*} [Fintype ι] {α : Type*} [Countable α]
    (F : α → (ι → 𝔸[ℚ]) → ℂ) (hc : ∀ q, Continuous (F q)) (b : α → ℝ) (hb : Summable b)
    (hle : ∀ q, ∀ y ∈ vecDomain ℚ ι, ‖F q y‖ ≤ b q) :
    ∫ y in vecDomain ℚ ι, ∑' q, F q y ∂vecMeasure ℚ ι =
      ∑' q, ∫ y in vecDomain ℚ ι, F q y ∂vecMeasure ℚ ι := by
  have : IsFiniteMeasure ((vecMeasure ℚ ι).restrict (vecDomain ℚ ι)) := ⟨by
    rw [Measure.restrict_apply_univ, FourierWhittaker.vecMeasure_vecDomain]; exact ENNReal.one_lt_top⟩
  have hint : ∀ q, Integrable (F q) ((vecMeasure ℚ ι).restrict (vecDomain ℚ ι)) := fun q =>
    Integrable.mono' (integrable_const (b q)) (hc q).aestronglyMeasurable
      ((ae_restrict_iff' FourierWhittaker.measurableSet_vecDomain).2 (ae_of_all _ (hle q)))
  have hnorm : ∀ q, ∫ y in vecDomain ℚ ι, ‖F q y‖ ∂vecMeasure ℚ ι ≤ b q := by
    intro q
    calc ∫ y in vecDomain ℚ ι, ‖F q y‖ ∂vecMeasure ℚ ι
        ≤ ∫ _ in vecDomain ℚ ι, b q ∂vecMeasure ℚ ι :=
          setIntegral_mono_on (hint q).norm (integrable_const _)
            FourierWhittaker.measurableSet_vecDomain (hle q)
      _ = b q := by
          rw [setIntegral_const, measureReal_def, FourierWhittaker.vecMeasure_vecDomain,
            ENNReal.toReal_one, one_smul]
  exact (integral_tsum_of_summable_integral_norm hint
    (Summable.of_nonneg_of_le (fun q => integral_nonneg fun _ => norm_nonneg _) hnorm hb)).symm

instance countable_GL2 : Countable (GL (Fin 2) ℚ) := by
  have : Countable (Matrix (Fin 2) (Fin 2) ℚ) := inferInstanceAs (Countable (Fin 2 → Fin 2 → ℚ))
  exact Function.Injective.countable (f := fun g : GL (Fin 2) ℚ => (g : Matrix (Fin 2) (Fin 2) ℚ))
    fun a b h => Units.ext h

instance countable_NQ : Countable NQ := Quotient.countable

/- English proof (translation)
Use `Units.continuous_iff.2 ⟨?_, ?_⟩` and prove the remaining obligations. Use `show Continuous fun x => (!![1, a x, b x; 0, 1, c x; 0, 0, 1] : Matrix (Fin 3) (Fin 3) 𝔸[ℚ])`. Use `continuous_matrix fun i j => ?_` and prove the remaining obligations. Apply the tactic sequence `fin_cases i <;> fin_cases j <;> simp <;> fun_prop`. Use `show Continuous fun x => (!![1, -a x, a x * c x - b x; 0, 1, -c x; 0, 0, 1] : Matrix (Fin 3) (Fin 3) 𝔸[ℚ])`.

Use `continuous_matrix fun i j => ?_` and prove the remaining obligations. Apply the tactic sequence `fin_cases i <;> fin_cases j <;> simp <;> fun_prop`.
-/
theorem continuous_uni {X : Type*} [TopologicalSpace X] {a b c : X → 𝔸[ℚ]} (ha : Continuous a)
    (hb : Continuous b) (hc : Continuous c) : Continuous fun x => (uni (a x) (b x) (c x) : G3) := by
  refine Units.continuous_iff.2 ⟨?_, ?_⟩
  · show Continuous fun x => (!![1, a x, b x; 0, 1, c x; 0, 0, 1] : Matrix (Fin 3) (Fin 3) 𝔸[ℚ])
    refine continuous_matrix fun i j => ?_
    fin_cases i <;> fin_cases j <;> simp <;> fun_prop
  · show Continuous fun x =>
      (!![1, -a x, a x * c x - b x; 0, 1, -c x; 0, 0, 1] : Matrix (Fin 3) (Fin 3) 𝔸[ℚ])
    refine continuous_matrix fun i j => ?_
    fin_cases i <;> fin_cases j <;> simp <;> fun_prop

/- English proof (translation)
Use `Units.continuous_iff.2 ⟨?_, ?_⟩` and prove the remaining obligations. Use `show Continuous fun x => (!![1, 0, 0; a x, 1, 0; 0, 0, 1] : Matrix (Fin 3) (Fin 3) 𝔸[ℚ])`. Use `continuous_matrix fun i j => ?_` and prove the remaining obligations. Apply the tactic sequence `fin_cases i <;> fin_cases j <;> simp <;> fun_prop`. Use `show Continuous fun x => (!![1, 0, 0; -a x, 1, 0; 0, 0, 1] : Matrix (Fin 3) (Fin 3) 𝔸[ℚ])`.

Use `continuous_matrix fun i j => ?_` and prove the remaining obligations. Apply the tactic sequence `fin_cases i <;> fin_cases j <;> simp <;> fun_prop`.
-/
theorem continuous_lowM {X : Type*} [TopologicalSpace X] {a : X → 𝔸[ℚ]} (ha : Continuous a) :
    Continuous fun x => lowM (a x) := by
  refine Units.continuous_iff.2 ⟨?_, ?_⟩
  · show Continuous fun x => (!![1, 0, 0; a x, 1, 0; 0, 0, 1] : Matrix (Fin 3) (Fin 3) 𝔸[ℚ])
    refine continuous_matrix fun i j => ?_
    fin_cases i <;> fin_cases j <;> simp <;> fun_prop
  · show Continuous fun x => (!![1, 0, 0; -a x, 1, 0; 0, 0, 1] : Matrix (Fin 3) (Fin 3) 𝔸[ℚ])
    refine continuous_matrix fun i j => ?_
    fin_cases i <;> fin_cases j <;> simp <;> fun_prop

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem val_uni (x y z : 𝔸[ℚ]) :
    ((uni x y z : G3) : Matrix (Fin 3) (Fin 3) 𝔸[ℚ]) = !![1, x, y; 0, 1, z; 0, 0, 1] := rfl

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem val_lowM (c : 𝔸[ℚ]) :
    ((lowM c : G3) : Matrix (Fin 3) (Fin 3) 𝔸[ℚ]) = !![1, 0, 0; c, 1, 0; 0, 0, 1] := rfl

/- English proof (translation)
Use extensionality with `i j`. Apply the tactic sequence `fin_cases i <;> fin_cases j <;> simp [e1, b1M]`.
-/
theorem diagonal_embed_GL2_matrix (γ : GL (Fin 2) ℚ) :
    ((dia (e1 γ) : G3) : Matrix (Fin 3) (Fin 3) 𝔸[ℚ]) =
      !![𝔞 (γ.val 0 0), 𝔞 (γ.val 0 1), 0; 𝔞 (γ.val 1 0), 𝔞 (γ.val 1 1), 0; 0, 0, 1] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [e1, b1M]

/- English proof (translation)
Use extensionality with `i j`. Apply the tactic sequence `fin_cases i <;> fin_cases j <;> simp [e2, b2M, sw, Matrix.mul_apply, Fin.sum_univ_three]`.
-/
theorem val_dia_e2sw (γ : GL (Fin 2) ℚ) :
    ((dia (e2 γ * sw) : G3) : Matrix (Fin 3) (Fin 3) 𝔸[ℚ]) =
      !![0, 1, 0; 𝔞 (γ.val 0 0), 0, 𝔞 (γ.val 0 1); 𝔞 (γ.val 1 0), 0, 𝔞 (γ.val 1 1)] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [e2, b2M, sw, Matrix.mul_apply, Fin.sum_univ_three]

/- English proof (translation)
Apply `Units.ext` to reduce the goal to its premises. Rewrite using `[val_lowM]`. Use extensionality with `i j`. Apply the tactic sequence `fin_cases i <;> fin_cases j <;> simp`.
-/
theorem lowM_zero : lowM (0 : 𝔸[ℚ]) = 1 := by
  apply Units.ext
  rw [val_lowM]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

/- English proof (translation)
Apply `Units.ext` to reduce the goal to its premises. Rewrite using `[val_uni]`. Use extensionality with `i j`. Apply the tactic sequence `fin_cases i <;> fin_cases j <;> simp`.
-/
theorem uni_zero : (uni 0 0 0 : G3) = 1 := by
  apply Units.ext
  rw [val_uni]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

/- English proof (translation)
Use `congrArg (fun X : Matrix (Fin 2) (Fin 2) ℚ => 𝔞 (X i j)) (Units.inv_mul γ)` as an intermediate fact. Simplify using `only [Matrix.mul_apply, Fin.sum_univ_two, map_add, map_mul, Matrix.one_apply] at this`. Rewrite using `[this]`. Apply the tactic sequence `split_ifs <;> simp`.
-/
theorem inv_rel (γ : GL (Fin 2) ℚ) (i j : Fin 2) :
    𝔞 ((γ⁻¹).val i 0) * 𝔞 (γ.val 0 j) + 𝔞 ((γ⁻¹).val i 1) * 𝔞 (γ.val 1 j) =
      if i = j then 1 else 0 := by
  have := congrArg (fun X : Matrix (Fin 2) (Fin 2) ℚ => 𝔞 (X i j)) (Units.inv_mul γ)
  simp only [Matrix.mul_apply, Fin.sum_univ_two, map_add, map_mul, Matrix.one_apply] at this
  rw [this]
  split_ifs <;> simp

/- English proof (translation)
Apply `Units.ext` to reduce the goal to its premises. Simplify using `only [Units.val_mul, val_lowM, val_uni]`. Use extensionality with `i j`. Apply the tactic sequence `fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three] <;> ring`.
-/
theorem heisenberg_lower_commute_corner (c x t s : 𝔸[ℚ]) :
    lowM c * uni 0 x (t + s) = uni 0 0 s * (lowM c * uni 0 x t) := by
  apply Units.ext
  simp only [Units.val_mul, val_lowM, val_uni]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three] <;> ring

/- English proof (translation)
Apply `Units.ext` to reduce the goal to its premises. Simplify using `only [Units.val_mul, val_lowM, val_uni]`. Use extensionality with `i j`. Apply the tactic sequence `fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three] <;> ring`.
-/
theorem heisenberg_lower_commute_middle (c x t s : 𝔸[ℚ]) :
    lowM c * uni 0 (x + s) t = uni 0 s (c * s) * (lowM c * uni 0 x t) := by
  apply Units.ext
  simp only [Units.val_mul, val_lowM, val_uni]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three] <;> ring

/- English proof (translation)
Apply `Units.ext` to reduce the goal to its premises. Simplify using `only [Units.val_mul, val_lowM, val_uni]`. Use extensionality with `i j`. Apply the tactic sequence `fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three] <;> ring`.
-/
theorem hH_c (c x t s : 𝔸[ℚ]) :
    lowM (c + s) * uni 0 x t = lowM s * (lowM c * uni 0 x t) := by
  apply Units.ext
  simp only [Units.val_mul, val_lowM, val_uni]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three] <;> ring

/- English proof (translation)
Apply `Units.ext` to reduce the goal to its premises. Simplify using `only [Units.val_mul, val_uni]`. Use extensionality with `i j`. Apply the tactic sequence `fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three] <;> ring`.
-/
theorem hY_a (a b s : 𝔸[ℚ]) : uni 0 (a + s) b = uni 0 s 0 * uni 0 a b := by
  apply Units.ext
  simp only [Units.val_mul, val_uni]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three] <;> ring

/- English proof (translation)
Apply `Units.ext` to reduce the goal to its premises. Simplify using `only [Units.val_mul, val_uni]`. Use extensionality with `i j`. Apply the tactic sequence `fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three] <;> ring`.
-/
theorem hY_b (a b s : 𝔸[ℚ]) : uni 0 a (b + s) = uni 0 0 s * uni 0 a b := by
  apply Units.ext
  simp only [Units.val_mul, val_uni]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three] <;> ring

/- English proof (translation)
Apply `Units.ext` to reduce the goal to its premises. Simplify using `only [Units.val_mul, diagonal_embed_GL2_matrix, val_uni]`. Use extensionality with `i j`. Apply the tactic sequence `fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three] <;> ring`.
-/
theorem GL2_embed_commute_corner (γ : GL (Fin 2) ℚ) (s : 𝔸[ℚ]) :
    dia (e1 γ) * uni 0 0 s = uni 0 (𝔞 (γ.val 0 1) * s) (𝔞 (γ.val 1 1) * s) * dia (e1 γ) := by
  apply Units.ext
  simp only [Units.val_mul, diagonal_embed_GL2_matrix, val_uni]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three] <;> ring

/- English proof (translation)
Apply `Units.ext` to reduce the goal to its premises. Simplify using `only [Units.val_mul, diagonal_embed_GL2_matrix, val_uni]`. Use extensionality with `i j`. Apply the tactic sequence `fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three] <;> ring`.
-/
theorem GL2_embed_commute_middle (γ : GL (Fin 2) ℚ) (s w : 𝔸[ℚ]) :
    dia (e1 γ) * uni 0 s w = uni 0 (𝔞 (γ.val 0 0) * s + 𝔞 (γ.val 0 1) * w)
      (𝔞 (γ.val 1 0) * s + 𝔞 (γ.val 1 1) * w) * dia (e1 γ) := by
  apply Units.ext
  simp only [Units.val_mul, diagonal_embed_GL2_matrix, val_uni]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three] <;> ring

/- English proof (translation)
Establish `h` using `congrArg Matrix.det (Units.mul_inv γ)`. Rewrite `h` using `[Matrix.det_mul, Matrix.det_one, Matrix.det_fin_two]`. Introduce `h0`. Rewrite `h` using `[h0, zero_mul]`. Conclude with `zero_ne_one h`.
-/
theorem det_ne_zero2 (γ : GL (Fin 2) ℚ) : γ.val 0 0 * γ.val 1 1 - γ.val 0 1 * γ.val 1 0 ≠ 0 := by
  have h := congrArg Matrix.det (Units.mul_inv γ)
  rw [Matrix.det_mul, Matrix.det_one, Matrix.det_fin_two] at h
  intro h0
  rw [h0, zero_mul] at h
  exact zero_ne_one h

/- English proof (translation)
Establish `h10 : γ.val 1 0 ≠ 0`. Introduce `h`. Use `det_ne_zero2 γ` as an intermediate fact. Rewrite `this` using `[h, h11]`. Simplify using `at this`.

Establish `hq : 𝔞 (γ.val 0 1 / γ.val 1 0) * 𝔞 (γ.val 1 0) = 𝔞 (γ.val 0 1)`. Rewrite using `[← map_mul, div_mul_cancel₀ _ h10]`. Generalize the expression as in `𝔞 (γ.val 0 1 / γ.val 1 0) = A at hq ⊢`. Apply `Units.ext` to reduce the goal to its premises. Simplify using `only [Units.val_mul, diagonal_embed_GL2_matrix, val_uni, val_lowM]`.

Use extensionality with `i j`. Apply the tactic sequence `fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three, h11] <;> first | linear_combination s * hq | linear_combination -s * hq | ring1`.
-/
theorem dU_c (γ : GL (Fin 2) ℚ) (h11 : γ.val 1 1 = 0) (s : 𝔸[ℚ]) :
    dia (e1 γ) * lowM s = uni (𝔞 (γ.val 0 1 / γ.val 1 0) * s) 0 0 * dia (e1 γ) := by
  have h10 : γ.val 1 0 ≠ 0 := by
    intro h; have := det_ne_zero2 γ; rw [h, h11] at this; simp at this
  have hq : 𝔞 (γ.val 0 1 / γ.val 1 0) * 𝔞 (γ.val 1 0) = 𝔞 (γ.val 0 1) := by
    rw [← map_mul, div_mul_cancel₀ _ h10]
  generalize 𝔞 (γ.val 0 1 / γ.val 1 0) = A at hq ⊢
  apply Units.ext
  simp only [Units.val_mul, diagonal_embed_GL2_matrix, val_uni, val_lowM]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three, h11] <;>
    first | linear_combination s * hq | linear_combination -s * hq | ring1

/- English proof (translation)
Establish `r0` using `inv_rel γ 1 0`. Establish `r1` using `inv_rel γ 1 1`. Simplify using `only [Fin.isValue, one_ne_zero, if_false, if_true] at r0 r1`. Generalize the expression as in `((γ⁻¹ : GL (Fin 2) ℚ) : Matrix (Fin 2) (Fin 2) ℚ) = N at r0 r1 ⊢`. Apply `Units.ext` to reduce the goal to its premises.

Simplify using `only [Units.val_mul, val_dia_e2sw, val_uni]`. Use extensionality with `i j`. Apply the tactic sequence `fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three] <;> first | linear_combination s * r0 | linear_combination -s * r0 |`. Take the linear combination `s * r1 | linear_combination -s * r1 | ring1`.
-/
theorem GL2_swap_embed_commute_corner (γ : GL (Fin 2) ℚ) (s : 𝔸[ℚ]) :
    dia (e2 γ * sw) * uni 0 0 s =
      uni (𝔞 ((γ⁻¹).val 1 0) * s) (𝔞 ((γ⁻¹).val 1 1) * s) 0 * dia (e2 γ * sw) := by
  have r0 := inv_rel γ 1 0
  have r1 := inv_rel γ 1 1
  simp only [Fin.isValue, one_ne_zero, if_false, if_true] at r0 r1
  generalize ((γ⁻¹ : GL (Fin 2) ℚ) : Matrix (Fin 2) (Fin 2) ℚ) = N at r0 r1 ⊢
  apply Units.ext
  simp only [Units.val_mul, val_dia_e2sw, val_uni]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three] <;>
    first | linear_combination s * r0 | linear_combination -s * r0 |
      linear_combination s * r1 | linear_combination -s * r1 | ring1

/- English proof (translation)
Establish `r0` using `inv_rel γ 0 0`. Establish `r1` using `inv_rel γ 0 1`. Simplify using `only [Fin.isValue, zero_ne_one, if_false, if_true] at r0 r1`. Generalize the expression as in `((γ⁻¹ : GL (Fin 2) ℚ) : Matrix (Fin 2) (Fin 2) ℚ) = N at r0 r1 ⊢`. Apply `Units.ext` to reduce the goal to its premises.

Simplify using `only [Units.val_mul, val_dia_e2sw, val_uni, val_lowM]`. Use extensionality with `i j`. Apply the tactic sequence `fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three] <;> first | linear_combination s * r0 | linear_combination -s * r0 |`. Take the linear combination `s * r1 | linear_combination -s * r1 | ring1`.
-/
theorem dV_c (γ : GL (Fin 2) ℚ) (s : 𝔸[ℚ]) :
    dia (e2 γ * sw) * lowM s =
      uni (𝔞 ((γ⁻¹).val 0 0) * s) (𝔞 ((γ⁻¹).val 0 1) * s) 0 * dia (e2 γ * sw) := by
  have r0 := inv_rel γ 0 0
  have r1 := inv_rel γ 0 1
  simp only [Fin.isValue, zero_ne_one, if_false, if_true] at r0 r1
  generalize ((γ⁻¹ : GL (Fin 2) ℚ) : Matrix (Fin 2) (Fin 2) ℚ) = N at r0 r1 ⊢
  apply Units.ext
  simp only [Units.val_mul, val_dia_e2sw, val_uni, val_lowM]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three] <;>
    first | linear_combination s * r0 | linear_combination -s * r0 |
      linear_combination s * r1 | linear_combination -s * r1 | ring1

/- English proof (translation)
Establish `h11 : γ.val 1 1 ≠ 0`. Introduce `h`. Use `det_ne_zero2 γ` as an intermediate fact. Rewrite `this` using `[h, h10]`. Simplify using `at this`.

Establish `q1 : 𝔞 (γ.val 1 1)⁻¹ * 𝔞 (γ.val 1 1) = 1`. Rewrite using `[← map_mul, inv_mul_cancel₀ h11, map_one]`. Establish `q2 : 𝔞 (γ.val 0 0 / γ.val 1 1) * 𝔞 (γ.val 1 1) = 𝔞 (γ.val 0 0)`. Rewrite using `[← map_mul, div_mul_cancel₀ _ h11]`. Generalize the expression as in `𝔞 (γ.val 1 1)⁻¹ = A1 at q1 ⊢`.

Generalize the expression as in `𝔞 (γ.val 0 0 / γ.val 1 1) = A2 at q2 ⊢`. Apply `Units.ext` to reduce the goal to its premises. Simplify using `only [Units.val_mul, val_dia_e2sw, val_uni]`. Use extensionality with `i j`. Apply the tactic sequence `fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three, h10] <;> first | linear_combination w * q1 | linear_combination -w * q1 |`.

Take the linear combination `s * q2 | linear_combination -s * q2 | ring1`.
-/
theorem GL2_swap_embed_commute_middle (γ : GL (Fin 2) ℚ) (h10 : γ.val 1 0 = 0) (s w : 𝔸[ℚ]) :
    dia (e2 γ * sw) * uni 0 s w =
      uni 0 (𝔞 (γ.val 1 1)⁻¹ * w) (𝔞 (γ.val 0 0 / γ.val 1 1) * s) * dia (e2 γ * sw) := by
  have h11 : γ.val 1 1 ≠ 0 := by
    intro h; have := det_ne_zero2 γ; rw [h, h10] at this; simp at this
  have q1 : 𝔞 (γ.val 1 1)⁻¹ * 𝔞 (γ.val 1 1) = 1 := by
    rw [← map_mul, inv_mul_cancel₀ h11, map_one]
  have q2 : 𝔞 (γ.val 0 0 / γ.val 1 1) * 𝔞 (γ.val 1 1) = 𝔞 (γ.val 0 0) := by
    rw [← map_mul, div_mul_cancel₀ _ h11]
  generalize 𝔞 (γ.val 1 1)⁻¹ = A1 at q1 ⊢
  generalize 𝔞 (γ.val 0 0 / γ.val 1 1) = A2 at q2 ⊢
  apply Units.ext
  simp only [Units.val_mul, val_dia_e2sw, val_uni]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three, h10] <;>
    first | linear_combination w * q1 | linear_combination -w * q1 |
      linear_combination s * q2 | linear_combination -s * q2 | ring1

end Ad3.GA.unipotentTranslateContinuity

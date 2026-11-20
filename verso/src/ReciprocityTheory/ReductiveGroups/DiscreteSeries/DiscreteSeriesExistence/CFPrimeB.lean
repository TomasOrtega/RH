import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.CFPrimeA
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.BochnerInequality.LayerWeight

noncomputable section

open Finset

namespace ReciprocityTheory.ChartRestriction.DS

variable {n : ℕ} {M : Type*} [AddCommGroup M] [Module ℂ M]

def tcoef (φ : Module.Dual ℂ (Fock n)) : TensorProduct ℂ M (Fock n) →ₗ[ℂ] M :=
  (TensorProduct.rid ℂ M).toLinearMap ∘ₗ TensorProduct.map LinearMap.id φ

/- English proof (translation)
Simplify using `[tcoef]`.
-/
theorem tcoef_tmul (φ : Module.Dual ℂ (Fock n)) (m : M) (f : Fock n) : tcoef φ (m ⊗ₜ f) = φ f • m := by
  simp [tcoef]

/- English proof (translation)
Proceed by induction on `y using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `tmul m f => simp [tcoef_tmul]`. Consider the case `add x y hx hy => simp only [map_add, hx, hy]`.
-/
theorem tcoef_map_left {M' : Type*} [AddCommGroup M'] [Module ℂ M'] (φ : Module.Dual ℂ (Fock n))
    (T : M' →ₗ[ℂ] M) (y : TensorProduct ℂ M' (Fock n)) :
    tcoef φ (TensorProduct.map T LinearMap.id y) = T (tcoef φ y) := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul m f => simp [tcoef_tmul]
  | add x y hx hy => simp only [map_add, hx, hy]

/- English proof (translation)
Proceed by induction on `y using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `tmul m f => simp [tcoef_tmul]`. Consider the case `add x y hx hy => simp only [map_add, hx, hy]`.
-/
theorem tcoef_lTensor (φ : Module.Dual ℂ (Fock n)) (S : Module.End ℂ (Fock n))
    (y : TensorProduct ℂ M (Fock n)) : tcoef φ (LinearMap.lTensor M S y) = tcoef (φ ∘ₗ S) y := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul m f => simp [tcoef_tmul]
  | add x y hx hy => simp only [map_add, hx, hy]

/- English proof (translation)
Proceed by induction on `y using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `tmul m f => simp [tcoef_tmul, smul_smul]`. Consider the case `add x y hx hy => simp only [map_add, hx, hy, smul_add]`.
-/
theorem tcoef_smul (c : ℂ) (φ : Module.Dual ℂ (Fock n)) (y : TensorProduct ℂ M (Fock n)) :
    tcoef (c • φ) y = c • tcoef φ y := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul m f => simp [tcoef_tmul, smul_smul]
  | add x y hx hy => simp only [map_add, hx, hy, smul_add]

/- English proof (translation)
Proceed by induction on `y using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `tmul m f`. Simplify using `only [tcoef_tmul, Module.Basis.coord_apply, TensorProduct.smul_tmul]`. Rewrite using `[← TensorProduct.tmul_sum, (fockBasis n).sum_repr]`.

Consider the case `add x y hx hy`. Simplify using `only [map_add, TensorProduct.add_tmul, Finset.sum_add_distrib]`. Rewrite using `[← hx, ← hy]`.
-/
theorem tcoef_expand (y : TensorProduct ℂ M (Fock n)) :
    y = ∑ s, tcoef ((fockBasis n).coord s) y ⊗ₜ fockBasis n s := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul m f =>
    simp only [tcoef_tmul, Module.Basis.coord_apply, TensorProduct.smul_tmul]
    rw [← TensorProduct.tmul_sum, (fockBasis n).sum_repr]
  | add x y hx hy =>
    simp only [map_add, TensorProduct.add_tmul, Finset.sum_add_distrib]
    rw [← hx, ← hy]

/- English proof (translation)
Take `⟨z, rfl⟩` from `hy`. Rewrite using `[tcoef_map_left]`. Conclude with `(tcoef φ z).2`.
-/
theorem tcoef_mem {L : Submodule ℂ M} {y : TensorProduct ℂ M (Fock n)}
    (hy : y ∈ LinearMap.range (TensorProduct.map L.subtype (LinearMap.id : Fock n →ₗ[ℂ] Fock n)))
    (φ : Module.Dual ℂ (Fock n)) : tcoef φ y ∈ L := by
  obtain ⟨z, rfl⟩ := hy
  rw [tcoef_map_left]
  exact (tcoef φ z).2

/- English proof (translation)
Simplify using `[dot, sub_mul, Finset.sum_sub_distrib]`.
-/
theorem dot_sub_left (u v w : Fin n → ℝ) : dot (u - v) w = dot u w - dot v w := by
  simp [dot, sub_mul, Finset.sum_sub_distrib]

/- English proof (translation)
Simplify using `[dot, root, sub_mul, Finset.sum_sub_distrib, Pi.single_apply]`.
-/
theorem dot_root_left (a b : Fin n) (w : Fin n → ℝ) : dot (root a b) w = w a - w b := by
  simp [dot, root, sub_mul, Finset.sum_sub_distrib, Pi.single_apply]

/- English proof (translation)
Use `(fockBasis n).ext fun t => ?_` and prove the remaining obligations. Simplify using `only [LinearMap.comp_apply, fockBasis_wt, map_smul, LinearMap.smul_apply, Module.Basis.coord_apply, Module.Basis.repr_self, Finsupp.single_apply]`. Use `split_ifs with h`. Substitute `h` using the available equality. Both sides reduce to the same expression.

Simplify using the standard rewrite rules.
-/
theorem coord_comp_sg (ε : Fin n → Bool) (s : Finset (Fin (n * n))) (c : Fin n) :
    (fockBasis n).coord s ∘ₗ sgE ε cpFock cmFock c c = ((fockWt ε s c : ℝ) : ℂ) • (fockBasis n).coord s := by
  classical
  refine (fockBasis n).ext fun t => ?_
  simp only [LinearMap.comp_apply, fockBasis_wt, map_smul, LinearMap.smul_apply, Module.Basis.coord_apply,
    Module.Basis.repr_self, Finsupp.single_apply]
  split_ifs with h
  · subst h
    rfl
  · simp

/- English proof (translation)
Use function extensionality and compare the values at `c`. Establish `h1 : ((fockBasis n).coord s ∘ₗ sgE ε cpFock cmFock c c) f = ((ν c : ℝ) : ℂ) * (fockBasis n).coord s f`. Rewrite using `[LinearMap.comp_apply, hf c, map_smul, smul_eq_mul]`. Rewrite `h1` using `[coord_comp_sg, LinearMap.smul_apply, smul_eq_mul]`. Establish `h2` using `mul_right_cancel₀ hs h1`.

Conclude with `h2.symm` after adjusting the coercions.
-/
theorem coord_wt_eq (ε : Fin n → Bool) {ν : Fin n → ℝ} {f : Fock n}
    (hf : ∀ c, sgE ε cpFock cmFock c c f = ((ν c : ℝ) : ℂ) • f) {s : Finset (Fin (n * n))}
    (hs : (fockBasis n).coord s f ≠ 0) : ν = fockWt ε s := by
  funext c
  have h1 : ((fockBasis n).coord s ∘ₗ sgE ε cpFock cmFock c c) f =
      ((ν c : ℝ) : ℂ) * (fockBasis n).coord s f := by
    rw [LinearMap.comp_apply, hf c, map_smul, smul_eq_mul]
  rw [coord_comp_sg, LinearMap.smul_apply, smul_eq_mul] at h1
  have h2 := mul_right_cancel₀ hs h1
  exact_mod_cast h2.symm

/- English proof (translation)
Establish `hcomm` using `sgE_comm isCAR_fock ε c c a b rfl hε`. Establish `key : sgE ε cpFock cmFock c c * sgE ε cpFock cmFock a b - sgE ε cpFock cmFock a b * sgE ε cpFock cmFock c c = ((root a b c : ℝ) : ℂ) • sgE ε cpFock cmFock a b`. Rewrite using `[hcomm]`. Distinguish the cases in `hca : c = a`. Substitute `hca` using the available equality.

Establish `hbc : b ≠ c` using `fun h => hab h.symm`. Simplify using `[root, Pi.single_apply, hbc, hab]`. Distinguish the cases in `hbc : b = c`. Substitute `hbc` using the available equality. Simplify using `[root, Pi.single_apply, hca, Ne.symm hca]`.

Simplify using `[root, Pi.single_apply, hca, Ne.symm hca, hbc, Ne.symm hbc]`. Establish `h1 : sgE ε cpFock cmFock c c (sgE ε cpFock cmFock a b f) - sgE ε cpFock cmFock a b (sgE ε cpFock cmFock c c f) = ((root a b c : ℝ) : ℂ) • sgE ε cpFock cmFock a b f`. Establish `h2` using `congrArg (fun T : Module.End ℂ (Fock n) => T f) key`. Simplify using `using h2`. Rewrite `h1` using `[hf c, map_smul, sub_eq_iff_eq_add]`.

Rewrite using `[h1, Pi.add_apply, Complex.ofReal_add, add_smul]`. Normalize the expressions using the abelian group laws.
-/
theorem sg_raise_wt (ε : Fin n → Bool) {a b : Fin n} (hab : a ≠ b) (hε : ε a = ε b) {ν : Fin n → ℝ}
    {f : Fock n} (hf : ∀ c, sgE ε cpFock cmFock c c f = ((ν c : ℝ) : ℂ) • f) (c : Fin n) :
    sgE ε cpFock cmFock c c (sgE ε cpFock cmFock a b f) =
      (((ν + root a b) c : ℝ) : ℂ) • sgE ε cpFock cmFock a b f := by
  classical
  have hcomm := sgE_comm isCAR_fock ε c c a b rfl hε
  have key : sgE ε cpFock cmFock c c * sgE ε cpFock cmFock a b -
      sgE ε cpFock cmFock a b * sgE ε cpFock cmFock c c =
        ((root a b c : ℝ) : ℂ) • sgE ε cpFock cmFock a b := by
    rw [hcomm]
    by_cases hca : c = a
    · subst hca
      have hbc : b ≠ c := fun h => hab h.symm
      simp [root, Pi.single_apply, hbc, hab]
    · by_cases hbc : b = c
      · subst hbc
        simp [root, Pi.single_apply, hca, Ne.symm hca]
      · simp [root, Pi.single_apply, hca, Ne.symm hca, hbc, Ne.symm hbc]
  have h1 : sgE ε cpFock cmFock c c (sgE ε cpFock cmFock a b f) -
      sgE ε cpFock cmFock a b (sgE ε cpFock cmFock c c f) =
        ((root a b c : ℝ) : ℂ) • sgE ε cpFock cmFock a b f := by
    have h2 := congrArg (fun T : Module.End ℂ (Fock n) => T f) key
    simpa using h2
  rw [hf c, map_smul, sub_eq_iff_eq_add] at h1
  rw [h1, Pi.add_apply, Complex.ofReal_add, add_smul]
  abel

/- English proof (translation)
Establish `hne : ∃ s, tcoef ((fockBasis n).coord s) y ≠ 0`. Assume the negation of the conclusion as `hcon`. Use `push_neg at hcon`. Apply `hy0` to reduce the goal to its premises. Rewrite using `[tcoef_expand y]`.

Simplify using `[hcon]`. Take `⟨s, hs, hmin⟩` from `Finset.exists_min_image (Finset.univ.filter fun t => tcoef ((fockBasis n).coord t) y ≠ 0) (fun t => dot (fockWt ε t) lam) (by obtain ⟨t, ht⟩ := hne; exact ⟨t, by simpa using ht⟩)`. Simplify using `only [Finset.mem_filter, Finset.mem_univ, true_and] at hs hmin`. Establish `hbasis : ∀ (t : Finset (Fin (n * n))) (c : Fin n), sgE ε cpFock cmFock c c (fockBasis n t) = ((fockWt ε t c : ℝ) : ℂ) • fockBasis n t`. Introduce `t c`.

Apply `(fockBasis n).ext_elem` to reduce the goal to its premises. Introduce `u`. Establish `h` using `LinearMap.congr_fun (coord_comp_sg ε u c) (fockBasis n t)`. Simplify using `only [LinearMap.comp_apply, Module.Basis.coord_apply, LinearMap.smul_apply, smul_eq_mul] at h`. Rewrite using `[h, map_smul, Finsupp.smul_apply, smul_eq_mul, Module.Basis.repr_self, Finsupp.single_apply]`.

Apply the tactic sequence `split_ifs with htu <;> simp [htu]`. Establish `htc : ∀ (φ : Module.Dual ℂ (Fock n)), tcoef φ y = ∑ t, φ (fockBasis n t) • tcoef ((fockBasis n).coord t) y`. Introduce `φ`. Use `conv_lhs => rw [tcoef_expand y]`. Simplify using `[map_sum, tcoef_tmul]`.

Use `⟨s, hs, ?_⟩` and prove the remaining obligations. Unfold `IsKHWVec`. Use `⟨fun a => ?_, fun a b hab heq => ?_⟩` and prove the remaining obligations. Establish `h1` using `congrArg (tcoef ((fockBasis n).coord s)) (hy.1 a)`. Simplify using `only [LinearMap.add_apply, map_add, tcoef_map_left, tcoef_lTensor, coord_comp_sg, tcoef_smul, map_smul] at h1`.

Rewrite using `[Pi.sub_apply, Complex.ofReal_sub, sub_smul, ← h1]`. Normalize the expressions using the abelian group laws. Establish `h1` using `congrArg (tcoef ((fockBasis n).coord s)) (hy.2 a b hab heq)`. Simplify using `only [LinearMap.add_apply, map_add, tcoef_map_left, tcoef_lTensor, map_zero] at h1`. Establish `h2 : tcoef ((fockBasis n).coord s ∘ₗ sgE ε cpFock cmFock a b) y = 0`.

Rewrite using `[htc]`. Use `Finset.sum_eq_zero fun t _ => ?_` and prove the remaining obligations. Distinguish the cases in `hyt : tcoef ((fockBasis n).coord t) y = 0`. Rewrite using `[hyt, smul_zero]`. Establish `hco : ((fockBasis n).coord s ∘ₗ sgE ε cpFock cmFock a b) (fockBasis n t) = 0`.

Assume the negation of the conclusion as `hne'`. Establish `hw` using `coord_wt_eq ε (fun c => sg_raise_wt ε (ne_of_lt hab) heq (hbasis t) c) hne'`. Establish `hft : fockWt ε t = fockWt ε s - root a b` using `eq_sub_of_add_eq hw`. Establish `hlt : dot (fockWt ε t) lam < dot (fockWt ε s) lam`. Rewrite using `[hft, dot_sub_left, dot_root_left]`.

Use `hlam hab` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion. Conclude with `absurd (hmin t hyt) (not_le.2 hlt)`. Rewrite using `[hco, zero_smul]`. Rewrite `h1` using `[h2, add_zero]`.

Conclude with `h1`.
-/
theorem khw_extract (ε : Fin n → Bool) {lam : Fin n → ℝ} (hlam : StrictAnti lam)
    {E : Fin n → Fin n → Module.End ℂ M} {μ : Fin n → ℝ} {y : TensorProduct ℂ M (Fock n)}
    (hy : IsKHWVec ε (fun a b => TensorProduct.map (E a b) LinearMap.id +
      LinearMap.lTensor M (sgE ε cpFock cmFock a b)) μ y) (hy0 : y ≠ 0) :
    ∃ s, tcoef ((fockBasis n).coord s) y ≠ 0 ∧
      IsKHWVec ε E (μ - fockWt ε s) (tcoef ((fockBasis n).coord s) y) := by
  classical
  have hne : ∃ s, tcoef ((fockBasis n).coord s) y ≠ 0 := by
    by_contra hcon
    push_neg at hcon
    apply hy0
    rw [tcoef_expand y]
    simp [hcon]
  obtain ⟨s, hs, hmin⟩ := Finset.exists_min_image
    (Finset.univ.filter fun t => tcoef ((fockBasis n).coord t) y ≠ 0)
    (fun t => dot (fockWt ε t) lam)
    (by obtain ⟨t, ht⟩ := hne; exact ⟨t, by simpa using ht⟩)
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hs hmin
  have hbasis : ∀ (t : Finset (Fin (n * n))) (c : Fin n),
      sgE ε cpFock cmFock c c (fockBasis n t) = ((fockWt ε t c : ℝ) : ℂ) • fockBasis n t := by
    intro t c
    apply (fockBasis n).ext_elem
    intro u
    have h := LinearMap.congr_fun (coord_comp_sg ε u c) (fockBasis n t)
    simp only [LinearMap.comp_apply, Module.Basis.coord_apply, LinearMap.smul_apply,
      smul_eq_mul] at h
    rw [h, map_smul, Finsupp.smul_apply, smul_eq_mul, Module.Basis.repr_self, Finsupp.single_apply]
    split_ifs with htu <;> simp [htu]
  have htc : ∀ (φ : Module.Dual ℂ (Fock n)),
      tcoef φ y = ∑ t, φ (fockBasis n t) • tcoef ((fockBasis n).coord t) y := by
    intro φ
    conv_lhs => rw [tcoef_expand y]
    simp [map_sum, tcoef_tmul]
  refine ⟨s, hs, ?_⟩
  unfold IsKHWVec
  refine ⟨fun a => ?_, fun a b hab heq => ?_⟩
  · have h1 := congrArg (tcoef ((fockBasis n).coord s)) (hy.1 a)
    simp only [LinearMap.add_apply, map_add, tcoef_map_left, tcoef_lTensor, coord_comp_sg,
      tcoef_smul, map_smul] at h1
    rw [Pi.sub_apply, Complex.ofReal_sub, sub_smul, ← h1]
    abel
  · have h1 := congrArg (tcoef ((fockBasis n).coord s)) (hy.2 a b hab heq)
    simp only [LinearMap.add_apply, map_add, tcoef_map_left, tcoef_lTensor, map_zero] at h1
    have h2 : tcoef ((fockBasis n).coord s ∘ₗ sgE ε cpFock cmFock a b) y = 0 := by
      rw [htc]
      refine Finset.sum_eq_zero fun t _ => ?_
      by_cases hyt : tcoef ((fockBasis n).coord t) y = 0
      · rw [hyt, smul_zero]
      · have hco : ((fockBasis n).coord s ∘ₗ sgE ε cpFock cmFock a b) (fockBasis n t) = 0 := by
          by_contra hne'
          have hw := coord_wt_eq ε (fun c => sg_raise_wt ε (ne_of_lt hab) heq (hbasis t) c) hne'
          have hft : fockWt ε t = fockWt ε s - root a b := eq_sub_of_add_eq hw
          have hlt : dot (fockWt ε t) lam < dot (fockWt ε s) lam := by
            rw [hft, dot_sub_left, dot_root_left]
            have := hlam hab
            linarith
          exact absurd (hmin t hyt) (not_le.2 hlt)
        rw [hco, zero_smul]
    rw [h2, add_zero] at h1
    exact h1

def zPlus (ε : Fin n → Bool) (E : Fin n → Fin n → Module.End ℂ M) : Module.End ℂ M :=
  ∑ c ∈ plusIdx ε, E c c

/- English proof (translation)
Establish `key : ∀ c, E c c * E a b = E a b * E c c + ((if c = a then (1 : ℂ) else 0) - (if b = c then (1 : ℂ) else 0)) • E a b`. Introduce `c`. Rewrite using `[← sub_eq_iff_eq_add', hE c c a b]`. Apply the tactic sequence `rcases eq_or_ne c a with rfl | h1 <;> rcases eq_or_ne b c with rfl | h2 <;> simp [*, sub_smul]`. Unfold `zPlus`.

Rewrite using `[Finset.sum_mul, Finset.sum_congr rfl (fun c _ => key c), Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.sum_smul]`. Use `congr 2`. Simplify using `[Finset.sum_sub_distrib, plusIdx]`.
-/
theorem zPlus_comm {ε : Fin n → Bool} {E : Fin n → Fin n → Module.End ℂ M} (hE : IsGlRep E) (a b : Fin n) :
    zPlus ε E * E a b = E a b * zPlus ε E +
      ((if ε a = true then (1 : ℂ) else 0) - (if ε b = true then (1 : ℂ) else 0)) • E a b := by
  have key : ∀ c, E c c * E a b = E a b * E c c +
      ((if c = a then (1 : ℂ) else 0) - (if b = c then (1 : ℂ) else 0)) • E a b := by
    intro c
    rw [← sub_eq_iff_eq_add', hE c c a b]
    rcases eq_or_ne c a with rfl | h1 <;> rcases eq_or_ne b c with rfl | h2 <;> simp [*, sub_smul]
  unfold zPlus
  rw [Finset.sum_mul, Finset.sum_congr rfl (fun c _ => key c), Finset.sum_add_distrib,
    ← Finset.mul_sum, ← Finset.sum_smul]
  congr 2
  simp [Finset.sum_sub_distrib, plusIdx]

/- English proof (translation)
Unfold `zPlus`. Rewrite using `[LinearMap.sum_apply, Finset.sum_smul]`. Conclude with `Finset.sum_congr rfl fun c _ => hw.1 c`.
-/
theorem zPlus_khw {ε : Fin n → Bool} {E : Fin n → Fin n → Module.End ℂ M} {ν : Fin n → ℝ} {w : M}
    (hw : IsKHWVec ε E ν w) : zPlus ε E w = (∑ c ∈ plusIdx ε, ((ν c : ℝ) : ℂ)) • w := by
  unfold zPlus
  rw [LinearMap.sum_apply, Finset.sum_smul]
  exact Finset.sum_congr rfl fun c _ => hw.1 c

/- English proof (translation)
Take `⟨_, hst, hirr, w, hwV, hw0, hw⟩` from `hV`. Establish `hS'st : IsKStableSub ε E (V ⊓ LinearMap.ker (zPlus ε E - (∑ c ∈ plusIdx ε, ((Λ c : ℝ) : ℂ)) • 1))`. Introduce `a b hab v hv`. Rewrite `hv`, the goal using `[Submodule.mem_inf, LinearMap.mem_ker]`. Use `⟨hst a b hab v hv.1, ?_⟩` and prove the remaining obligations.

Establish `hz` using `hv.2`. Rewrite `hz` using `[LinearMap.sub_apply, sub_eq_zero, LinearMap.smul_apply, Module.End.one_apply]`. Establish `hc` using `LinearMap.congr_fun (zPlus_comm (ε := ε) hE a b) v`. Simplify using `only [Module.End.mul_apply, LinearMap.add_apply, LinearMap.smul_apply, hz, hab, sub_self, zero_smul, add_zero] at hc`. Rewrite using `[LinearMap.sub_apply, sub_eq_zero, LinearMap.smul_apply, Module.End.one_apply, hc, map_smul]`.

Break down `hirr _ inf_le_left hS'st with h0 | hV'` into its components or cases. It suffices to derive a contradiction. Apply `hw0` to reduce the goal to its premises. Establish `hwS : w ∈ V ⊓ LinearMap.ker (zPlus ε E - (∑ c ∈ plusIdx ε, ((Λ c : ℝ) : ℂ)) • 1)`. Rewrite using `[Submodule.mem_inf, LinearMap.mem_ker]`.

Use `⟨hwV, ?_⟩` and prove the remaining obligations. Rewrite using `[LinearMap.sub_apply, sub_eq_zero, LinearMap.smul_apply, Module.End.one_apply]`. Conclude with `zPlus_khw hw`. Rewrite `hwS` using `[h0]`. Conclude with `(Submodule.mem_bot ℂ).1 hwS`.

Introduce `v hv`. Rewrite `hv` using `[← hV', Submodule.mem_inf, LinearMap.mem_ker, LinearMap.sub_apply, sub_eq_zero, LinearMap.smul_apply, Module.End.one_apply]`. Conclude with `hv.2`.
-/
theorem zPlus_V {ε : Fin n → Bool} {E : Fin n → Fin n → Module.End ℂ M} (hE : IsGlRep E) {Λ : Fin n → ℝ}
    {V : Submodule ℂ M} (hV : IsKIrrHW ε E Λ V) :
    ∀ v ∈ V, zPlus ε E v = (∑ c ∈ plusIdx ε, ((Λ c : ℝ) : ℂ)) • v := by
  obtain ⟨_, hst, hirr, w, hwV, hw0, hw⟩ := hV
  have hS'st : IsKStableSub ε E
      (V ⊓ LinearMap.ker (zPlus ε E - (∑ c ∈ plusIdx ε, ((Λ c : ℝ) : ℂ)) • 1)) := by
    intro a b hab v hv
    rw [Submodule.mem_inf, LinearMap.mem_ker] at hv ⊢
    refine ⟨hst a b hab v hv.1, ?_⟩
    have hz := hv.2
    rw [LinearMap.sub_apply, sub_eq_zero, LinearMap.smul_apply, Module.End.one_apply] at hz
    have hc := LinearMap.congr_fun (zPlus_comm (ε := ε) hE a b) v
    simp only [Module.End.mul_apply, LinearMap.add_apply, LinearMap.smul_apply, hz, hab, sub_self,
      zero_smul, add_zero] at hc
    rw [LinearMap.sub_apply, sub_eq_zero, LinearMap.smul_apply, Module.End.one_apply, hc, map_smul]
  rcases hirr _ inf_le_left hS'st with h0 | hV'
  · exfalso
    apply hw0
    have hwS : w ∈ V ⊓ LinearMap.ker (zPlus ε E - (∑ c ∈ plusIdx ε, ((Λ c : ℝ) : ℂ)) • 1) := by
      rw [Submodule.mem_inf, LinearMap.mem_ker]
      refine ⟨hwV, ?_⟩
      rw [LinearMap.sub_apply, sub_eq_zero, LinearMap.smul_apply, Module.End.one_apply]
      exact zPlus_khw hw
    rw [h0] at hwS
    exact (Submodule.mem_bot ℂ).1 hwS
  · intro v hv
    rw [← hV', Submodule.mem_inf, LinearMap.mem_ker, LinearMap.sub_apply, sub_eq_zero,
      LinearMap.smul_apply, Module.End.one_apply] at hv
    exact hv.2

/- English proof (translation)
Use `show E a b v ∈ layer ε E V 0 ⊔ ⨆ (a : Fin n) (b : Fin n) (_ : ε a ≠ ε b), (layer ε E V 0).map (E a b)`. Use `Submodule.mem_sup_right ?_` and prove the remaining obligations. Use `Submodule.mem_iSup_of_mem a (Submodule.mem_iSup_of_mem b (Submodule.mem_iSup_of_mem h ?_))` and prove the remaining obligations. Conclude with `Submodule.mem_map_of_mem hv`.
-/
theorem mem_layer_one {ε : Fin n → Bool} {E : Fin n → Fin n → Module.End ℂ M} {V : Submodule ℂ M}
    {v : M} (hv : v ∈ V) {a b : Fin n} (h : ε a ≠ ε b) : E a b v ∈ layer ε E V 1 := by
  show E a b v ∈ layer ε E V 0 ⊔
    ⨆ (a : Fin n) (b : Fin n) (_ : ε a ≠ ε b), (layer ε E V 0).map (E a b)
  refine Submodule.mem_sup_right ?_
  refine Submodule.mem_iSup_of_mem a (Submodule.mem_iSup_of_mem b (Submodule.mem_iSup_of_mem h ?_))
  exact Submodule.mem_map_of_mem hv

/- English proof (translation)
Establish `hex : ∃ s, tcoef ((fockBasis n).coord s) x ≠ 0`. Assume the negation of the conclusion as `hcon`. Use `push_neg at hcon`. Apply `hx0` to reduce the goal to its premises. Rewrite using `[tcoef_expand x]`.

Simplify using `[hcon]`. Take `⟨s, hs⟩` from `hex`. Use `⟨_, tcoef_mem hx _, hs, ?_⟩` and prove the remaining obligations. Rewrite using `[← tcoef_map_left, hTx, map_zero]`.
-/
theorem tens_ker_nontrivial (T : Module.End ℂ M) {V : Submodule ℂ M} {x : TensorProduct ℂ M (Fock n)}
    (hx : x ∈ LinearMap.range (TensorProduct.map V.subtype (LinearMap.id : Fock n →ₗ[ℂ] Fock n)))
    (hx0 : x ≠ 0) (hTx : TensorProduct.map T LinearMap.id x = 0) : ∃ v ∈ V, v ≠ 0 ∧ T v = 0 := by
  have hex : ∃ s, tcoef ((fockBasis n).coord s) x ≠ 0 := by
    by_contra hcon
    push_neg at hcon
    apply hx0
    rw [tcoef_expand x]
    simp [hcon]
  obtain ⟨s, hs⟩ := hex
  refine ⟨_, tcoef_mem hx _, hs, ?_⟩
  rw [← tcoef_map_left, hTx, map_zero]

section Vanish

variable {M : Type*} [NormedAddCommGroup M] [InnerProductSpace ℂ M]

/- English proof (translation)
Assume the negation of the conclusion as `hy0`. Take `⟨s, hw0, hwK⟩` from `khw_extract ε hmono hK hy0`. Establish `hwL` using `tcoef_mem hy ((fockBasis n).coord s)`. Establish `hw1` using `(Submodule.mem_inf.mp hwL).1`. Establish `hwz : zPlus ε E (tcoef ((fockBasis n).coord s) y) = t • tcoef ((fockBasis n).coord s) y`.

Establish `h` using `(Submodule.mem_inf.mp hwL).2`. Rewrite `h` using `[LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply, sub_eq_zero]`. Then use the resulting hypothesis. Establish `hsum : (∑ c ∈ plusIdx ε, (((lam - rhoC ε + rhoHol ε - fockWt ε s) c : ℝ) : ℂ)) = t`. Establish `h2` using `zPlus_khw hwK`. Rewrite `h2` using `[hwz]`.

Conclude with `(smul_left_injective ℂ hw0 h2).symm`. Take `⟨j, hj, hnc⟩` from `khw_layer_weight hE hU hV 1 hw1 hw0 hwK`. Break down `Nat.le_one_iff_eq_zero_or_eq_one.mp hj with rfl | rfl` into its components or cases. Take `⟨γ, -, hγ⟩` from `hnc`. Simplify using `only [Finset.univ_eq_empty, Finset.sum_empty] at hγ`.

Establish `hν : ∀ c, (lam - rhoC ε + rhoHol ε - fockWt ε s) c = lowK ε lam c` using `fun c => by`. Use `congrFun hγ c` as an intermediate fact. Simplify using `only [Pi.sub_apply, Pi.zero_apply] at this`. Simplify using `only [Pi.sub_apply]`. Combine the linear equalities and inequalities to obtain the conclusion.

Apply `ht` to reduce the goal to its premises. Rewrite using `[← hsum]`. Conclude with `Finset.sum_congr rfl fun c _ => by rw [hν c]`. Take `⟨γ, hγε, hγ⟩` from `hnc`. Rewrite `hγ` using `[Fin.sum_univ_one]`.

Establish `hab : ε (γ 0).1 ≠ ε (γ 0).2` using `hγε 0`. Establish `hne : (γ 0).1 ≠ (γ 0).2` using `fun h => hab (by rw [h])`. Break down `lt_or_gt_of_ne hne with hlt | hlt` into its components or cases. Establish `hw' : fockWt ε s = (rhoHol ε - rhoN ε) - root (γ 0).1 (γ 0).2`. Use function extensionality and compare the values at `c`.

Use `congrFun hγ c` as an intermediate fact. Simplify using `only [Pi.sub_apply, Pi.add_apply, lowK, root] at this ⊢`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `h1` using `fockWt_dot_ge ε hmono s`. Rewrite `h1` using `[hw']`.

Simplify using `only [dot_sub_left, dot_root_left] at h1`. Combine the linear relations using `[hmono hlt]`. Apply `hw0` to reduce the goal to its premises. Use `hNo (γ 0).2 (γ 0).1 hlt hab.symm _ hw1 ?_` and prove the remaining obligations. Establish `: lam - rhoC ε + rhoHol ε - fockWt ε s = lowK ε lam - root (γ 0).2 (γ 0).1`.

Use function extensionality and compare the values at `c`. Use `congrFun hγ c` as an intermediate fact. Simplify using `only [Pi.sub_apply, Pi.add_apply, lowK, root] at this ⊢`. Combine the linear equalities and inequalities to obtain the conclusion. Rewrite `hwK` using `[this]`. Then use the resulting hypothesis.
-/
theorem tens_khw_vanish {ε : Fin n → Bool} {lam : Fin n → ℝ} (hmono : StrictAnti lam)
    {E : Fin n → Fin n → Module.End ℂ M} (hE : IsGlRep E) (hU : IsInfUnitary ε E) {V : Submodule ℂ M}
    (hV : IsKIrrHW ε E (lowK ε lam) V)
    (hNo : ∀ a b : Fin n, a < b → ε a ≠ ε b → ∀ w ∈ layer ε E V 1,
      IsKHWVec ε E (lowK ε lam - root a b) w → w = 0)
    {t : ℂ} (ht : t ≠ ∑ c ∈ plusIdx ε, ((lowK ε lam c : ℝ) : ℂ)) {y : TensorProduct ℂ M (Fock n)}
    (hy : y ∈ LinearMap.range (TensorProduct.map (layer ε E V 1 ⊓ LinearMap.ker (zPlus ε E - t • 1)).subtype
      (LinearMap.id : Fock n →ₗ[ℂ] Fock n)))
    (hK : IsKHWVec ε (fun a b => (TensorProduct.map (E a b) LinearMap.id +
      LinearMap.lTensor M (sgE ε cpFock cmFock a b) : Module.End ℂ (TensorProduct ℂ M (Fock n))))
      (lam - rhoC ε + rhoHol ε) y) : y = 0 := by
  by_contra hy0
  obtain ⟨s, hw0, hwK⟩ := khw_extract ε hmono hK hy0
  have hwL := tcoef_mem hy ((fockBasis n).coord s)
  have hw1 := (Submodule.mem_inf.mp hwL).1
  have hwz : zPlus ε E (tcoef ((fockBasis n).coord s) y) = t • tcoef ((fockBasis n).coord s) y := by
    have h := (Submodule.mem_inf.mp hwL).2
    rwa [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply, sub_eq_zero] at h
  have hsum : (∑ c ∈ plusIdx ε, (((lam - rhoC ε + rhoHol ε - fockWt ε s) c : ℝ) : ℂ)) = t := by
    have h2 := zPlus_khw hwK
    rw [hwz] at h2
    exact (smul_left_injective ℂ hw0 h2).symm
  obtain ⟨j, hj, hnc⟩ := khw_layer_weight hE hU hV 1 hw1 hw0 hwK
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hj with rfl | rfl
  · obtain ⟨γ, -, hγ⟩ := hnc
    simp only [Finset.univ_eq_empty, Finset.sum_empty] at hγ
    have hν : ∀ c, (lam - rhoC ε + rhoHol ε - fockWt ε s) c = lowK ε lam c := fun c => by
      have := congrFun hγ c
      simp only [Pi.sub_apply, Pi.zero_apply] at this
      simp only [Pi.sub_apply]
      linarith
    apply ht
    rw [← hsum]
    exact Finset.sum_congr rfl fun c _ => by rw [hν c]
  · obtain ⟨γ, hγε, hγ⟩ := hnc
    rw [Fin.sum_univ_one] at hγ
    have hab : ε (γ 0).1 ≠ ε (γ 0).2 := hγε 0
    have hne : (γ 0).1 ≠ (γ 0).2 := fun h => hab (by rw [h])
    rcases lt_or_gt_of_ne hne with hlt | hlt
    · have hw' : fockWt ε s = (rhoHol ε - rhoN ε) - root (γ 0).1 (γ 0).2 := by
        funext c
        have := congrFun hγ c
        simp only [Pi.sub_apply, Pi.add_apply, lowK, root] at this ⊢
        linarith
      have h1 := fockWt_dot_ge ε hmono s
      rw [hw'] at h1
      simp only [dot_sub_left, dot_root_left] at h1
      linarith [hmono hlt]
    · apply hw0
      refine hNo (γ 0).2 (γ 0).1 hlt hab.symm _ hw1 ?_
      have : lam - rhoC ε + rhoHol ε - fockWt ε s = lowK ε lam - root (γ 0).2 (γ 0).1 := by
        funext c
        have := congrFun hγ c
        simp only [Pi.sub_apply, Pi.add_apply, lowK, root] at this ⊢
        linarith
      rwa [this] at hwK

end Vanish

end ReciprocityTheory.ChartRestriction.DS

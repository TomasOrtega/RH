import Mathlib
open MeasureTheory Filter Topology
open scoped SchwartzMap ContDiff

noncomputable section

namespace GlobalTheory.LatticePartition

def bump (t : ℝ) : ℝ := Real.smoothTransition (t + 1) - Real.smoothTransition t

/- English proof (translation)
The claim follows from `(Real.smoothTransition.contDiff.comp (contDiff_id.add contDiff_const)).sub Real.smoothTransition.contDiff`.
-/
theorem bump_contDiff : ContDiff ℝ ∞ bump :=
  (Real.smoothTransition.contDiff.comp (contDiff_id.add contDiff_const)).sub
    Real.smoothTransition.contDiff

/- English proof (translation)
Unfold `bump`. Break down `le_abs'.1 h with h | h` into its components or cases. Rewrite using `[Real.smoothTransition.zero_of_nonpos (by linarith), Real.smoothTransition.zero_of_nonpos (by linarith)]`. Simplify using the standard rewrite rules. Rewrite using `[Real.smoothTransition.one_of_one_le (by linarith), Real.smoothTransition.one_of_one_le h]`.

Simplify using the standard rewrite rules.
-/
theorem bump_eq_zero {t : ℝ} (h : 1 ≤ |t|) : bump t = 0 := by
  unfold bump
  rcases le_abs'.1 h with h | h
  · rw [Real.smoothTransition.zero_of_nonpos (by linarith),
      Real.smoothTransition.zero_of_nonpos (by linarith)]
    simp
  · rw [Real.smoothTransition.one_of_one_le (by linarith),
      Real.smoothTransition.one_of_one_le h]
    simp

/- English proof (translation)
Apply `bump_eq_zero` to reduce the goal to its premises. Simplify using `only [Finset.mem_insert, Finset.mem_singleton, not_or] at hk`. Establish `h1` using `Int.floor_le y`. Establish `h2` using `Int.lt_floor_add_one y`. Establish `: k ≤ ⌊y⌋ - 2 ∨ ⌊y⌋ + 2 ≤ k` using `by omega`.

Break down `this with h | h` into its components or cases. Establish `h' : (k : ℝ) ≤ (⌊y⌋ : ℝ) - 2` using `by exact_mod_cast h`. Rewrite using `[le_abs']`. Use `right`. Combine the linear equalities and inequalities to obtain the conclusion.

Establish `h' : (⌊y⌋ : ℝ) + 2 ≤ (k : ℝ)` using `by exact_mod_cast h`. Rewrite using `[le_abs']`. Use `left`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem bump_local (y : ℝ) (k : ℤ) (hk : k ∉ ({⌊y⌋ - 1, ⌊y⌋, ⌊y⌋ + 1} : Finset ℤ)) :
    bump (y - k) = 0 := by
  apply bump_eq_zero
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hk
  have h1 := Int.floor_le y
  have h2 := Int.lt_floor_add_one y
  have : k ≤ ⌊y⌋ - 2 ∨ ⌊y⌋ + 2 ≤ k := by omega
  rcases this with h | h
  · have h' : (k : ℝ) ≤ (⌊y⌋ : ℝ) - 2 := by exact_mod_cast h
    rw [le_abs']; right; linarith
  · have h' : (⌊y⌋ : ℝ) + 2 ≤ (k : ℝ) := by exact_mod_cast h
    rw [le_abs']; left; linarith

/- English proof (translation)
Rewrite using `[Finset.sum_insert (by simp; omega), Finset.sum_insert (by simp), Finset.sum_singleton]`. Establish `h1` using `Int.floor_le y`. Establish `h2` using `Int.lt_floor_add_one y`. Establish `e1 : y - ((⌊y⌋ - 1 : ℤ) : ℝ) = y - (⌊y⌋ : ℝ) + 1` using `by push_cast; ring`. Establish `e2 : y - ((⌊y⌋ + 1 : ℤ) : ℝ) + 1 = y - (⌊y⌋ : ℝ)` using `by push_cast; ring`.

Establish `ha : Real.smoothTransition (y - (⌊y⌋ : ℝ) + 1 + 1) = 1` using `Real.smoothTransition.one_of_one_le (by linarith)`. Establish `hb : Real.smoothTransition (y - ((⌊y⌋ + 1 : ℤ) : ℝ)) = 0` using `Real.smoothTransition.zero_of_nonpos (by push_cast; linarith)`. Unfold `bump`. Rewrite using `[e1, e2, ha, hb]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem bump_sum (y : ℝ) : ∑ k ∈ ({⌊y⌋ - 1, ⌊y⌋, ⌊y⌋ + 1} : Finset ℤ), bump (y - k) = 1 := by
  rw [Finset.sum_insert (by simp; omega), Finset.sum_insert (by simp), Finset.sum_singleton]
  have h1 := Int.floor_le y
  have h2 := Int.lt_floor_add_one y
  have e1 : y - ((⌊y⌋ - 1 : ℤ) : ℝ) = y - (⌊y⌋ : ℝ) + 1 := by push_cast; ring
  have e2 : y - ((⌊y⌋ + 1 : ℤ) : ℝ) + 1 = y - (⌊y⌋ : ℝ) := by push_cast; ring
  have ha : Real.smoothTransition (y - (⌊y⌋ : ℝ) + 1 + 1) = 1 :=
    Real.smoothTransition.one_of_one_le (by linarith)
  have hb : Real.smoothTransition (y - ((⌊y⌋ + 1 : ℤ) : ℝ)) = 0 :=
    Real.smoothTransition.zero_of_nonpos (by push_cast; linarith)
  unfold bump
  rw [e1, e2, ha, hb]
  ring

/- English proof (translation)
Use `Summable.of_norm_bounded_eventually (ZLattice.summable_norm_pow_inv L _ (Nat.lt_succ_self _)) ?_` and prove the remaining obligations. Use `(Set.finite_singleton (0 : L)).subset fun z hz => ?_` and prove the remaining obligations. Assume the negation of the conclusion as `h0`. Apply `hz` to reduce the goal to its premises. Establish `hz0 : 0 < ‖z‖` using `norm_pos_iff.2 h0`.

Use `show ‖((1 + ‖z‖) ^ (Module.finrank ℤ L + 1))⁻¹‖ ≤ ‖z‖⁻¹ ^ (Module.finrank ℤ L + 1)`. Rewrite using `[norm_inv, norm_pow, Real.norm_of_nonneg (by positivity), inv_pow]`. Conclude with `inv_anti₀ (pow_pos hz0 _) (pow_le_pow_left₀ hz0.le (by linarith) _)`.
-/
theorem summable_lattice {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (L : Submodule ℤ E) [DiscreteTopology L] :
    Summable fun z : L => ((1 + ‖z‖) ^ (Module.finrank ℤ L + 1))⁻¹ := by
  refine Summable.of_norm_bounded_eventually (ZLattice.summable_norm_pow_inv L _ (Nat.lt_succ_self _)) ?_
  refine (Set.finite_singleton (0 : L)).subset fun z hz => ?_
  by_contra h0
  apply hz
  have hz0 : 0 < ‖z‖ := norm_pos_iff.2 h0
  show ‖((1 + ‖z‖) ^ (Module.finrank ℤ L + 1))⁻¹‖ ≤ ‖z‖⁻¹ ^ (Module.finrank ℤ L + 1)
  rw [norm_inv, norm_pow, Real.norm_of_nonneg (by positivity), inv_pow]
  exact inv_anti₀ (pow_pos hz0 _) (pow_le_pow_left₀ hz0.le (by linarith) _)

section
variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] {n : ℕ}

def bumpProd (e : V ≃L[ℝ] (Fin n → ℝ)) (x : V) : ℝ := ∏ i, bump (e x i)

def latPt (e : V ≃L[ℝ] (Fin n → ℝ)) (j : Fin n → ℤ) : V := e.symm (fun i => (j i : ℝ))

/- English proof (translation)
Unfold `bumpProd`. Use `contDiff_prod fun i _ => bump_contDiff.comp ?_` and prove the remaining obligations. Conclude with `(contDiff_apply ℝ ℝ i).comp e.contDiff`.
-/
theorem bumpProd_contDiff (e : V ≃L[ℝ] (Fin n → ℝ)) : ContDiff ℝ ∞ (bumpProd e) := by
  unfold bumpProd
  refine contDiff_prod fun i _ => bump_contDiff.comp ?_
  exact (contDiff_apply ℝ ℝ i).comp e.contDiff

/- English proof (translation)
Establish `hK : IsCompact (Set.univ.pi fun _ : Fin n => Set.Icc (-1 : ℝ) 1)` using `isCompact_univ_pi fun _ => isCompact_Icc`. Use `HasCompactSupport.intro (hK.image e.symm.continuous) ?_` and prove the remaining obligations. Introduce `x hx`. Establish `: ∃ i, 1 ≤ |e x i|`. Assume the negation of the conclusion as `h`.

Simplify using `only [not_exists, not_le] at h`. Conclude with `hx ⟨e x, Set.mem_univ_pi.2 fun i => ⟨(abs_lt.1 (h i)).1.le, (abs_lt.1 (h i)).2.le⟩, e.symm_apply_apply x⟩`. Take `⟨i, hi⟩` from `this`. Conclude with `Finset.prod_eq_zero (Finset.mem_univ i) (bump_eq_zero hi)`.
-/
theorem bumpProd_compact (e : V ≃L[ℝ] (Fin n → ℝ)) : HasCompactSupport (bumpProd e) := by
  have hK : IsCompact (Set.univ.pi fun _ : Fin n => Set.Icc (-1 : ℝ) 1) :=
    isCompact_univ_pi fun _ => isCompact_Icc
  refine HasCompactSupport.intro (hK.image e.symm.continuous) ?_
  intro x hx
  have : ∃ i, 1 ≤ |e x i| := by
    by_contra h
    simp only [not_exists, not_le] at h
    exact hx ⟨e x, Set.mem_univ_pi.2 fun i => ⟨(abs_lt.1 (h i)).1.le, (abs_lt.1 (h i)).2.le⟩,
      e.symm_apply_apply x⟩
  obtain ⟨i, hi⟩ := this
  exact Finset.prod_eq_zero (Finset.mem_univ i) (bump_eq_zero hi)

/- English proof (translation)
Simplify using `[bumpProd, latPt, map_sub]`.
-/
theorem bumpProd_sub (e : V ≃L[ℝ] (Fin n → ℝ)) (x : V) (j : Fin n → ℤ) :
    bumpProd e (x - latPt e j) = ∏ i, bump (e x i - j i) := by
  simp [bumpProd, latPt, map_sub]

/- English proof (translation)
Simplify using `only [bumpProd_sub]`. Generalize the expression as in `e x = y`. Establish `hsum : ∑ j ∈ Fintype.piFinset (fun i => ({⌊y i⌋ - 1, ⌊y i⌋, ⌊y i⌋ + 1} : Finset ℤ)), ∏ i, bump (y i - j i) = 1`. Rewrite using `[← Finset.prod_univ_sum (t := fun i => ({⌊y i⌋ - 1, ⌊y i⌋, ⌊y i⌋ + 1} : Finset ℤ)) (f := fun i k => bump (y i - k))]`. Conclude with `Finset.prod_eq_one fun i _ => bump_sum (y i)`.

Establish `h` using `hasSum_sum_of_ne_finset_zero (L := SummationFilter.unconditional _) (f := fun j : Fin n → ℤ => ∏ i, bump (y i - j i)) (s := Fintype.piFinset (fun i => ({⌊y i⌋ - 1, ⌊y i⌋, ⌊y i⌋ + 1} : Finset ℤ))) (by`. Introduce `j hj`. Rewrite `hj` using `[Fintype.mem_piFinset, not_forall]`. Take `⟨i, hi⟩` from `hj`. Conclude with `Finset.prod_eq_zero (Finset.mem_univ i) (bump_local _ _ hi))`.

Rewrite `h` using `[hsum]`. Then use the resulting hypothesis.
-/
theorem hasSum_bumpProd (e : V ≃L[ℝ] (Fin n → ℝ)) (x : V) :
    HasSum (fun j : Fin n → ℤ => bumpProd e (x - latPt e j)) 1 := by
  simp only [bumpProd_sub]
  generalize e x = y
  have hsum : ∑ j ∈ Fintype.piFinset (fun i => ({⌊y i⌋ - 1, ⌊y i⌋, ⌊y i⌋ + 1} : Finset ℤ)),
      ∏ i, bump (y i - j i) = 1 := by
    rw [← Finset.prod_univ_sum (t := fun i => ({⌊y i⌋ - 1, ⌊y i⌋, ⌊y i⌋ + 1} : Finset ℤ))
      (f := fun i k => bump (y i - k))]
    exact Finset.prod_eq_one fun i _ => bump_sum (y i)
  have h := hasSum_sum_of_ne_finset_zero (L := SummationFilter.unconditional _)
    (f := fun j : Fin n → ℤ => ∏ i, bump (y i - j i))
    (s := Fintype.piFinset (fun i => ({⌊y i⌋ - 1, ⌊y i⌋, ⌊y i⌋ + 1} : Finset ℤ))) (by
      intro j hj
      rw [Fintype.mem_piFinset, not_forall] at hj
      obtain ⟨i, hi⟩ := hj
      exact Finset.prod_eq_zero (Finset.mem_univ i) (bump_local _ _ hi))
  rwa [hsum] at h

/- English proof (translation)
Establish `hmem : ∀ j, latPt b.equivFunL j ∈ Submodule.span ℤ (Set.range b)` using `fun j => by`. Establish `: latPt b.equivFunL j = ∑ i, (j i : ℝ) • b i` using `b.equivFun_symm_apply _`. Rewrite using `[this]`. Use `Submodule.sum_mem _ fun i _ => ?_` and prove the remaining obligations. Rewrite using `[Int.cast_smul_eq_zsmul]`.

Conclude with `Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)`. Establish `hinj : Function.Injective fun j : Fin n → ℤ => (⟨latPt b.equivFunL j, hmem j⟩ : Submodule.span ℤ (Set.range b))`. Introduce `j k hjk`. Establish `h1 : latPt b.equivFunL j = latPt b.equivFunL k` using `congrArg Subtype.val hjk`. Establish `h2 : (fun i => (j i : ℝ)) = fun i => (k i : ℝ)` using `b.equivFunL.symm.injective h1`.

Use function extensionality and compare the values at `i`. Conclude with `congrFun h2 i` after adjusting the coercions. Establish `h` using `(summable_lattice (Submodule.span ℤ (Set.range b))).comp_injective hinj`. Use `⟨Module.finrank ℤ (Submodule.span ℤ (Set.range b)) + 1, h.congr fun j => ?_⟩` and prove the remaining obligations. Simplify using `only [Function.comp_apply, Submodule.coe_norm]`.
-/
theorem summable_latPt [FiniteDimensional ℝ V] (b : Module.Basis (Fin n) ℝ V) :
    ∃ M : ℕ, Summable (fun j : Fin n → ℤ => ((1 + ‖latPt b.equivFunL j‖) ^ M)⁻¹) := by
  have hmem : ∀ j, latPt b.equivFunL j ∈ Submodule.span ℤ (Set.range b) := fun j => by
    have : latPt b.equivFunL j = ∑ i, (j i : ℝ) • b i := b.equivFun_symm_apply _
    rw [this]
    refine Submodule.sum_mem _ fun i _ => ?_
    rw [Int.cast_smul_eq_zsmul]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  have hinj : Function.Injective fun j : Fin n → ℤ =>
      (⟨latPt b.equivFunL j, hmem j⟩ : Submodule.span ℤ (Set.range b)) := by
    intro j k hjk
    have h1 : latPt b.equivFunL j = latPt b.equivFunL k := congrArg Subtype.val hjk
    have h2 : (fun i => (j i : ℝ)) = fun i => (k i : ℝ) := b.equivFunL.symm.injective h1
    funext i
    exact_mod_cast congrFun h2 i
  have h := (summable_lattice (Submodule.span ℤ (Set.range b))).comp_injective hinj
  refine ⟨Module.finrank ℤ (Submodule.span ℤ (Set.range b)) + 1, h.congr fun j => ?_⟩
  simp only [Function.comp_apply, Submodule.coe_norm]

/- English proof (translation)
Establish `ht` using `hS.tendsto_cofinite_zero`. Establish `hR : (0 : ℝ) ≤ max R 0` using `le_max_right _ _`. Establish `hε : (0 : ℝ) < ((1 + max R 0) ^ M)⁻¹` using `by positivity`. Establish `h3` using `ht (Iio_mem_nhds hε)`. Rewrite `h3` using `[Filter.mem_map, Filter.mem_cofinite]`.

Use `h3.subset fun j hj => ?_` and prove the remaining obligations. Simplify using `only [Set.mem_setOf_eq] at hj`. Simplify using `only [Set.mem_compl_iff, Set.mem_preimage, Set.mem_Iio, not_lt]`. Establish `hj' : a j ≤ max R 0` using `le_trans hj (le_max_left _ _)`. Establish `h0` using `ha j`.

Conclude with `inv_anti₀ (by positivity) (pow_le_pow_left₀ (by linarith) (by linarith) _)`.
-/
theorem finite_of_summable {ι : Type} (a : ι → ℝ) (ha : ∀ j, 0 ≤ a j) (M : ℕ)
    (hS : Summable (fun j => ((1 + a j) ^ M)⁻¹)) (R : ℝ) : {j | a j ≤ R}.Finite := by
  have ht := hS.tendsto_cofinite_zero
  have hR : (0 : ℝ) ≤ max R 0 := le_max_right _ _
  have hε : (0 : ℝ) < ((1 + max R 0) ^ M)⁻¹ := by positivity
  have h3 := ht (Iio_mem_nhds hε)
  rw [Filter.mem_map, Filter.mem_cofinite] at h3
  refine h3.subset fun j hj => ?_
  simp only [Set.mem_setOf_eq] at hj
  simp only [Set.mem_compl_iff, Set.mem_preimage, Set.mem_Iio, not_lt]
  have hj' : a j ≤ max R 0 := le_trans hj (le_max_left _ _)
  have h0 := ha j
  exact inv_anti₀ (by positivity) (pow_le_pow_left₀ (by linarith) (by linarith) _)

end

/- English proof (translation)
Introduce `V _ _ _`. Take `⟨M, hS⟩` from `summable_latPt (Module.finBasis ℝ V)`. Generalize the expression as in `(Module.finBasis ℝ V).equivFunL = e at hS`. Establish `hc : HasCompactSupport (fun x => ((bumpProd e x : ℝ) : ℂ))` using `(bumpProd_compact e).comp_left (g := Complex.ofReal) Complex.ofReal_zero`. Establish `hd : ContDiff ℝ ∞ (fun x => ((bumpProd e x : ℝ) : ℂ))` using `Complex.ofRealCLM.contDiff.comp (bumpProd_contDiff e)`.

Take `⟨ψ, hψ⟩ : ∃ ψ : SchwartzMap V ℂ, (ψ : V → ℂ) = fun x => ((bumpProd e x : ℝ) : ℂ)` from `⟨hc.toSchwartzMap hd, rfl⟩`. Use `⟨ψ, hψ ▸ hc, ?_, latPt e, ?_, ?_, M, hS⟩` and prove the remaining obligations. Introduce `x`. Rewrite using `[hψ]`. Conclude with `Complex.conj_ofReal _`.

Introduce `x`. Rewrite using `[hψ]`. Establish `h` using `Complex.hasSum_ofReal.2 (hasSum_bumpProd e x)`. Rewrite `h` using `[Complex.ofReal_one]`. Then use the resulting hypothesis. Conclude with `finite_of_summable (fun j => ‖latPt e j‖) (fun _ => norm_nonneg _) M hS`.
-/
theorem exists_lattice_partition :
    ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V],
    ∃ ψ : SchwartzMap V ℂ, HasCompactSupport (ψ : V → ℂ) ∧ (∀ x, starRingEnd ℂ (ψ x) = ψ x) ∧
      ∃ v : (Fin (Module.finrank ℝ V) → ℤ) → V, (∀ x, HasSum (fun j => ψ (x - v j)) 1) ∧
        (∀ R : ℝ, {j | ‖v j‖ ≤ R}.Finite) ∧ ∃ M : ℕ, Summable (fun j => ((1 + ‖v j‖) ^ M)⁻¹) := by
  intro V _ _ _
  obtain ⟨M, hS⟩ := summable_latPt (Module.finBasis ℝ V)
  generalize (Module.finBasis ℝ V).equivFunL = e at hS
  have hc : HasCompactSupport (fun x => ((bumpProd e x : ℝ) : ℂ)) :=
    (bumpProd_compact e).comp_left (g := Complex.ofReal) Complex.ofReal_zero
  have hd : ContDiff ℝ ∞ (fun x => ((bumpProd e x : ℝ) : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp (bumpProd_contDiff e)
  obtain ⟨ψ, hψ⟩ : ∃ ψ : SchwartzMap V ℂ, (ψ : V → ℂ) = fun x => ((bumpProd e x : ℝ) : ℂ) :=
    ⟨hc.toSchwartzMap hd, rfl⟩
  refine ⟨ψ, hψ ▸ hc, ?_, latPt e, ?_, ?_, M, hS⟩
  · intro x
    rw [hψ]
    exact Complex.conj_ofReal _
  · intro x
    rw [hψ]
    have h := Complex.hasSum_ofReal.2 (hasSum_bumpProd e x)
    rwa [Complex.ofReal_one] at h
  · exact finite_of_summable (fun j => ‖latPt e j‖) (fun _ => norm_nonneg _) M hS

end GlobalTheory.LatticePartition

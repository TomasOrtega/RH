import Formalism.PieriBlockIdeals.StatementLP

namespace Formalism.CohomologicalDescent.LP

open Formalism.CohomologicalDescent.Symmetrization Formalism.CohomologicalDescent.BinaryFormsExample

/- English proof (translation)
Distinguish the cases in `hx : x = 0`. Simplify using `[hx]`. Conclude with `(h.pos x hx).le`.
-/
theorem lpa_nonneg {K N : Type*} [Field K] [LinearOrder K] [AddCommGroup N] [Module K N] {q : ℕ}
    {T : Fin q → Fin q → Module.End K N} {B : LinearMap.BilinForm K N} (h : FormMod T B) (x : N) : 0 ≤ B x x := by
  by_cases hx : x = 0
  · simp [hx]
  · exact (h.pos x hx).le

/- English proof (translation)
Introduce `K N q _ _ _ _ _ T B hU v μ hv0 hv a b hab`. Take `⟨hr, hd⟩` from `hv`. Establish `h2` using `LinearMap.congr_fun (hU.gl a b b a) v`. Rewrite `h2` using `[if_pos rfl, if_pos rfl]`. Simplify using `only [LinearMap.sub_apply, Module.End.mul_apply, hr a b hab, map_zero, sub_zero, hd a, hd b] at h2`.

Establish `hnn` using `lpa_nonneg hU (T b a v)`. Rewrite `hnn` using `[hU.adj b a v (T b a v), h2, map_sub, map_smul, map_smul, smul_eq_mul, smul_eq_mul, ← sub_mul]`. Establish `hpos` using `hU.pos v hv0`. Assume the negation of the conclusion as `hlt`. Use `push Not at hlt`.

Establish `hneg : (μ a - μ b) * B v v < 0` using `mul_neg_of_neg_of_pos (sub_neg.mpr hlt) hpos`. Conclude with `(not_le.mpr hneg) hnn`.
-/
theorem highestWeightDominant_holds : HWDominant := by
  intro K N q _ _ _ _ _ T B hU v μ hv0 hv a b hab
  obtain ⟨hr, hd⟩ := hv
  have h2 := LinearMap.congr_fun (hU.gl a b b a) v
  rw [if_pos rfl, if_pos rfl] at h2
  simp only [LinearMap.sub_apply, Module.End.mul_apply, hr a b hab, map_zero, sub_zero, hd a, hd b] at h2
  have hnn := lpa_nonneg hU (T b a v)
  rw [hU.adj b a v (T b a v), h2, map_sub, map_smul, map_smul, smul_eq_mul, smul_eq_mul, ← sub_mul] at hnn
  have hpos := hU.pos v hv0
  by_contra hlt
  push Not at hlt
  have hneg : (μ a - μ b) * B v v < 0 := mul_neg_of_neg_of_pos (sub_neg.mpr hlt) hpos
  exact (not_le.mpr hneg) hnn

/- English proof (translation)
Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty => exact ⟨C, le_rfl, hne, hC, 0, by simp⟩`. Consider the case `insert i s hi ih`. Take `⟨C', hC'C, hC'ne, hC'st, μ, hμ⟩` from `ih`. Establish `key : C' ⊓ ⨆ c, (f i).genEigenspace c 1 = ⨆ c, C' ⊓ (f i).genEigenspace c 1` using `Submodule.inf_iSup_genEigenspace (p := C') (f := f i) (fun x hx => hC'st i x hx) 1`.

Establish `htop : (⨆ c, (f i).genEigenspace c 1) = ⊤` using `hdiag i`. Rewrite `key` using `[htop, inf_top_eq]`. Establish `hex : ∃ c, C' ⊓ (f i).genEigenspace c 1 ≠ ⊥`. Assume the negation of the conclusion as `h`. Use `push Not at h`.

Apply `hC'ne` to reduce the goal to its premises. Rewrite using `[key]`. Conclude with `iSup_eq_bot.mpr h`. Take `⟨c, hc⟩` from `hex`. Use `⟨C' ⊓ (f i).genEigenspace c 1, inf_le_left.trans hC'C, hc, ?_, Function.update μ i c, ?_⟩` and prove the remaining obligations.

Introduce `j x hx`. Take `⟨hx1, hx2⟩` from `Submodule.mem_inf.mp hx`. Conclude with `Submodule.mem_inf.mpr ⟨hC'st j x hx1, Module.End.mapsTo_genEigenspace_of_comm (hcomm i j) c 1 hx2⟩`. Introduce `j hj x hx`. Take `⟨hx1, hx2⟩` from `Submodule.mem_inf.mp hx`.

Break down `Finset.mem_insert.mp hj with hji | hjs` into its components or cases. Rewrite using `[hji, Function.update_self]`. Conclude with `Module.End.mem_genEigenspace_one.mp hx2`. Establish `hji : j ≠ i` using `fun h => hi (h ▸ hjs)`. Rewrite using `[Function.update_of_ne hji]`.

Conclude with `hμ j hjs x hx1`.
-/
theorem lpa_joint {K N ι : Type*} [Field K] [AddCommGroup N] [Module K N] [FiniteDimensional K N]
    (f : ι → Module.End K N) (hcomm : ∀ i j, Commute (f i) (f j))
    (hdiag : ∀ i, ⨆ μ : K, Module.End.eigenspace (f i) μ = ⊤) (s : Finset ι) (C : Submodule K N)
    (hC : ∀ i, ∀ x ∈ C, f i x ∈ C) (hne : C ≠ ⊥) :
    ∃ C' : Submodule K N, C' ≤ C ∧ C' ≠ ⊥ ∧ (∀ i, ∀ x ∈ C', f i x ∈ C') ∧ ∃ μ : ι → K, ∀ i ∈ s, ∀ x ∈ C', f i x = μ i • x := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨C, le_rfl, hne, hC, 0, by simp⟩
  | insert i s hi ih =>
    obtain ⟨C', hC'C, hC'ne, hC'st, μ, hμ⟩ := ih
    have key : C' ⊓ ⨆ c, (f i).genEigenspace c 1 = ⨆ c, C' ⊓ (f i).genEigenspace c 1 :=
      Submodule.inf_iSup_genEigenspace (p := C') (f := f i) (fun x hx => hC'st i x hx) 1
    have htop : (⨆ c, (f i).genEigenspace c 1) = ⊤ := hdiag i
    rw [htop, inf_top_eq] at key
    have hex : ∃ c, C' ⊓ (f i).genEigenspace c 1 ≠ ⊥ := by
      by_contra h
      push Not at h
      apply hC'ne
      rw [key]
      exact iSup_eq_bot.mpr h
    obtain ⟨c, hc⟩ := hex
    refine ⟨C' ⊓ (f i).genEigenspace c 1, inf_le_left.trans hC'C, hc, ?_, Function.update μ i c, ?_⟩
    · intro j x hx
      obtain ⟨hx1, hx2⟩ := Submodule.mem_inf.mp hx
      exact Submodule.mem_inf.mpr
        ⟨hC'st j x hx1, Module.End.mapsTo_genEigenspace_of_comm (hcomm i j) c 1 hx2⟩
    · intro j hj x hx
      obtain ⟨hx1, hx2⟩ := Submodule.mem_inf.mp hx
      rcases Finset.mem_insert.mp hj with hji | hjs
      · rw [hji, Function.update_self]
        exact Module.End.mem_genEigenspace_one.mp hx2
      · have hji : j ≠ i := fun h => hi (h ▸ hjs)
        rw [Function.update_of_ne hji]
        exact hμ j hjs x hx1

/- English proof (translation)
Establish `hs : ∀ d : Fin q, ∑ c : Fin q, -((c : ℕ) : K) * (Pi.single d (1 : K) : Fin q → K) c = -((d : ℕ) : K)`. Introduce `d`. Rewrite using `[Finset.sum_eq_single d]`. Simplify using the standard rewrite rules. Introduce `c _ hcd`.

Rewrite using `[Pi.single_eq_of_ne hcd, mul_zero]`. Introduce `h`. Conclude with `absurd (Finset.mem_univ d) h`. Simplify using `only [Pi.add_apply, Pi.sub_apply, mul_add, mul_sub, Finset.sum_add_distrib, Finset.sum_sub_distrib, hs]`. Expand and normalize the polynomial expressions, which then agree.
-/
private theorem weighted_sum_add_single_sub_single {K : Type*} [Field K] {q : ℕ} (μ : Fin q → K) (a b : Fin q) :
    ∑ c : Fin q, -((c : ℕ) : K) * (μ + Pi.single a (1 : K) - Pi.single b (1 : K) : Fin q → K) c =
      ∑ c : Fin q, -((c : ℕ) : K) * μ c + ((b : ℕ) : K) - ((a : ℕ) : K) := by
  have hs : ∀ d : Fin q, ∑ c : Fin q, -((c : ℕ) : K) * (Pi.single d (1 : K) : Fin q → K) c = -((d : ℕ) : K) := by
    intro d
    rw [Finset.sum_eq_single d]
    · simp
    · intro c _ hcd
      rw [Pi.single_eq_of_ne hcd, mul_zero]
    · intro h
      exact absurd (Finset.mem_univ d) h
  simp only [Pi.add_apply, Pi.sub_apply, mul_add, mul_sub, Finset.sum_add_distrib, Finset.sum_sub_distrib, hs]
  ring

/- English proof (translation)
Introduce `K N q _ _ _ _ _ _ T hT hdiag C hC hne`. Establish `hcomm : ∀ a b, Commute (T a a) (T b b)`. Introduce `a b`. Distinguish the cases in `hab : a = b`. Substitute `hab` using the available equality.

Conclude with `Commute.refl _`. Establish `h` using `hT a a b b`. Rewrite `h` using `[if_neg hab, if_neg (Ne.symm hab), sub_zero]`. Conclude with `sub_eq_zero.mp h`. Take `⟨C', hC'C, hC'ne, _, μ0, hμ0⟩` from `lpa_joint (fun a => T a a) (fun a b => hcomm a b) hdiag Finset.univ C (fun a x hx => hC a a x hx) hne`.

Take `⟨x0, hx0C', hx00⟩` from `Submodule.exists_mem_ne_zero_of_ne_bot hC'ne`. Take `⟨W, hW⟩ : ∃ W : Set (Fin q → K), ∀ ν, ν ∈ W ↔ ∃ v ∈ C, v ≠ 0 ∧ ∀ c, T c c v = ν c • v` from `⟨{ν | ∃ v ∈ C, v ≠ 0 ∧ ∀ c, T c c v = ν c • v}, fun ν => Iff.rfl⟩`. Establish `hW0 : μ0 ∈ W` using `(hW μ0).mpr ⟨x0, hC'C hx0C', hx00, fun c => hμ0 c (Finset.mem_univ c) x0 hx0C'⟩`. Establish `hfin : (Set.univ.pi fun c : Fin q => {z : K | (T c c).HasEigenvalue z}).Finite` using `Set.Finite.pi fun c => Module.End.finite_hasEigenvalue (T c c)`. Establish `hWfin : W.Finite`.

Use `hfin.subset ?_` and prove the remaining obligations. Introduce `ν hν`. Take `⟨v, -, hv0, hv⟩` from `(hW ν).mp hν`. Rewrite using `[Set.mem_univ_pi]`. Introduce `c`.

Conclude with `Module.End.hasEigenvalue_of_hasEigenvector (Module.End.hasEigenvector_iff.mpr ⟨Module.End.mem_eigenspace_iff.mpr (hv c), hv0⟩)`. Take `⟨μ, hμW, hmax⟩` from `Set.exists_max_image W (fun ν => ∑ c : Fin q, -((c : ℕ) : K) * ν c) hWfin ⟨μ0, hW0⟩`. Take `⟨v, hvC, hv0, hvw⟩` from `(hW μ).mp hμW`. Use `⟨v, hvC, hv0, μ, And.intro ?_ hvw⟩` and prove the remaining obligations. Introduce `a b hab`.

Assume the negation of the conclusion as `hw`. Establish `hba : b ≠ a` using `hab.ne'`. Establish `hwt : ∀ c, T c c (T a b v) = (μ + Pi.single a (1 : K) - Pi.single b (1 : K) : Fin q → K) c • T a b v`. Introduce `c`. Establish `h2` using `LinearMap.congr_fun (hT c c a b) v`.

Simplify using `only [LinearMap.sub_apply, Module.End.mul_apply, hvw c, map_smul] at h2`. Establish `h3` using `sub_eq_iff_eq_add.mp h2`. Distinguish the cases in `hca : c = a`. Rewrite `h3`, the goal using `[hca]`. Rewrite `h3` using `[if_pos rfl, if_neg hba, LinearMap.zero_apply, sub_zero]`.

Rewrite using `[h3]`. Simplify using `only [Pi.add_apply, Pi.sub_apply, Pi.single_eq_same, Pi.single_eq_of_ne hab.ne, sub_zero]`. Use `module`. Distinguish the cases in `hcb : c = b`. Rewrite `h3`, the goal using `[hcb]`.

Rewrite `h3` using `[if_neg hba, if_pos rfl, LinearMap.zero_apply, zero_sub]`. Rewrite using `[h3]`. Simplify using `only [Pi.add_apply, Pi.sub_apply, Pi.single_eq_same, Pi.single_eq_of_ne hba, add_zero]`. Use `module`. Rewrite `h3` using `[if_neg hca, if_neg (fun h => hcb h.symm), LinearMap.zero_apply, sub_zero, zero_add]`.

Rewrite using `[h3]`. Simplify using `only [Pi.add_apply, Pi.sub_apply, Pi.single_eq_of_ne hca, Pi.single_eq_of_ne hcb, add_zero, sub_zero]`. Establish `hνW : (μ + Pi.single a (1 : K) - Pi.single b (1 : K) : Fin q → K) ∈ W` using `(hW _).mpr ⟨T a b v, hC a b v hvC, hw, hwt⟩`. Establish `hle : ∑ c : Fin q, -((c : ℕ) : K) * (μ + Pi.single a (1 : K) - Pi.single b (1 : K) : Fin q → K) c ≤ ∑ c : Fin q, -((c : ℕ) : K) * μ c` using `hmax _ hνW`. Rewrite `hle` using `[weighted_sum_add_single_sub_single]`.

Establish `hlt : ((a : ℕ) : K) < ((b : ℕ) : K)`. Conclude with `Nat.cast_lt.mpr hab`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem existsHighestWeight_holds : ExistsHW := by
  intro K N q _ _ _ _ _ _ T hT hdiag C hC hne
  classical
  have hcomm : ∀ a b, Commute (T a a) (T b b) := by
    intro a b
    by_cases hab : a = b
    · subst hab
      exact Commute.refl _
    · have h := hT a a b b
      rw [if_neg hab, if_neg (Ne.symm hab), sub_zero] at h
      exact sub_eq_zero.mp h
  obtain ⟨C', hC'C, hC'ne, _, μ0, hμ0⟩ :=
    lpa_joint (fun a => T a a) (fun a b => hcomm a b) hdiag Finset.univ C
      (fun a x hx => hC a a x hx) hne
  obtain ⟨x0, hx0C', hx00⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hC'ne
  obtain ⟨W, hW⟩ : ∃ W : Set (Fin q → K), ∀ ν, ν ∈ W ↔ ∃ v ∈ C, v ≠ 0 ∧ ∀ c, T c c v = ν c • v :=
    ⟨{ν | ∃ v ∈ C, v ≠ 0 ∧ ∀ c, T c c v = ν c • v}, fun ν => Iff.rfl⟩
  have hW0 : μ0 ∈ W := (hW μ0).mpr ⟨x0, hC'C hx0C', hx00, fun c => hμ0 c (Finset.mem_univ c) x0 hx0C'⟩
  have hfin : (Set.univ.pi fun c : Fin q => {z : K | (T c c).HasEigenvalue z}).Finite :=
    Set.Finite.pi fun c => Module.End.finite_hasEigenvalue (T c c)
  have hWfin : W.Finite := by
    refine hfin.subset ?_
    intro ν hν
    obtain ⟨v, -, hv0, hv⟩ := (hW ν).mp hν
    rw [Set.mem_univ_pi]
    intro c
    exact Module.End.hasEigenvalue_of_hasEigenvector
      (Module.End.hasEigenvector_iff.mpr ⟨Module.End.mem_eigenspace_iff.mpr (hv c), hv0⟩)
  obtain ⟨μ, hμW, hmax⟩ :=
    Set.exists_max_image W (fun ν => ∑ c : Fin q, -((c : ℕ) : K) * ν c) hWfin ⟨μ0, hW0⟩
  obtain ⟨v, hvC, hv0, hvw⟩ := (hW μ).mp hμW
  refine ⟨v, hvC, hv0, μ, And.intro ?_ hvw⟩
  intro a b hab
  by_contra hw
  have hba : b ≠ a := hab.ne'
  have hwt : ∀ c, T c c (T a b v) = (μ + Pi.single a (1 : K) - Pi.single b (1 : K) : Fin q → K) c • T a b v := by
    intro c
    have h2 := LinearMap.congr_fun (hT c c a b) v
    simp only [LinearMap.sub_apply, Module.End.mul_apply, hvw c, map_smul] at h2
    have h3 := sub_eq_iff_eq_add.mp h2
    by_cases hca : c = a
    · rw [hca] at h3 ⊢
      rw [if_pos rfl, if_neg hba, LinearMap.zero_apply, sub_zero] at h3
      rw [h3]
      simp only [Pi.add_apply, Pi.sub_apply, Pi.single_eq_same, Pi.single_eq_of_ne hab.ne, sub_zero]
      module
    · by_cases hcb : c = b
      · rw [hcb] at h3 ⊢
        rw [if_neg hba, if_pos rfl, LinearMap.zero_apply, zero_sub] at h3
        rw [h3]
        simp only [Pi.add_apply, Pi.sub_apply, Pi.single_eq_same, Pi.single_eq_of_ne hba, add_zero]
        module
      · rw [if_neg hca, if_neg (fun h => hcb h.symm), LinearMap.zero_apply, sub_zero, zero_add] at h3
        rw [h3]
        simp only [Pi.add_apply, Pi.sub_apply, Pi.single_eq_of_ne hca, Pi.single_eq_of_ne hcb,
          add_zero, sub_zero]
  have hνW : (μ + Pi.single a (1 : K) - Pi.single b (1 : K) : Fin q → K) ∈ W := (hW _).mpr ⟨T a b v, hC a b v hvC, hw, hwt⟩
  have hle : ∑ c : Fin q, -((c : ℕ) : K) * (μ + Pi.single a (1 : K) - Pi.single b (1 : K) : Fin q → K) c ≤
      ∑ c : Fin q, -((c : ℕ) : K) * μ c := hmax _ hνW
  rw [weighted_sum_add_single_sub_single] at hle
  have hlt : ((a : ℕ) : K) < ((b : ℕ) : K) := by
    exact Nat.cast_lt.mpr hab
  linarith

/- English proof (translation)
Introduce `K N q _ _ _ _ _ _ T B hU S S' hS hS' hhw`. Establish `hrefl : B.IsRefl`. Introduce `x y h`. Conclude with `(hU.symm y x).trans h`. Establish `hRst : Stab T (S ⊓ S')` using `fun a b x hx => Submodule.mem_inf.mpr ⟨hS a b x (Submodule.mem_inf.mp hx).1, hS' a b x (Submodule.mem_inf.mp hx).2⟩`.

Establish `hUst : Stab T (S ⊓ B.orthogonal (S ⊓ S'))`. Introduce `a b x hx`. Take `⟨hxS, hxO⟩` from `Submodule.mem_inf.mp hx`. Use `Submodule.mem_inf.mpr ⟨hS a b x hxS, ?_⟩` and prove the remaining obligations. Rewrite using `[LinearMap.BilinForm.mem_orthogonal_iff]`.

Introduce `n hn`. Rewrite using `[hU.symm, hU.adj, hU.symm]`. Conclude with `(LinearMap.BilinForm.mem_orthogonal_iff.mp hxO) _ (hRst b a n hn)`. Establish `hUbot : S ⊓ B.orthogonal (S ⊓ S') = ⊥`. Assume the negation of the conclusion as `hne`.

Take `⟨v, hvU, hv0, μ, hμ⟩` from `existsHighestWeight_holds K N q T hU.gl hU.diag _ hUst hne`. Take `⟨hvS, hvO⟩` from `Submodule.mem_inf.mp hvU`. Establish `hvS'` using `hhw v hvS μ hμ`. Establish `hvv` using `(LinearMap.BilinForm.mem_orthogonal_iff.mp hvO) v (Submodule.mem_inf.mpr ⟨hvS, hvS'⟩)`. Conclude with `(hU.pos v hv0).ne' hvv`.

Establish `hcompl : IsCompl (S ⊓ S') (B.orthogonal (S ⊓ S'))` using `(LinearMap.BilinForm.isCompl_orthogonal_iff_disjoint hrefl).mpr (Submodule.disjoint_def.mpr fun x hxR hxO => Classical.byContradiction fun h => (hU.pos x h).ne' ((LinearMap.BilinForm.mem_orthogonal_iff.mp hxO) x hxR))`. Introduce `x hxS`. Establish `hx : x ∈ (S ⊓ S') ⊔ B.orthogonal (S ⊓ S')`. Rewrite using `[hcompl.sup_eq_top]`. Conclude with `Submodule.mem_top`.

Take `⟨y, hyR, z, hzO, hyz⟩` from `Submodule.mem_sup.mp hx`. Establish `hzS : z ∈ S`. Establish `hz : z = x - y`. Rewrite using `[← hyz]`. Normalize the expressions using the abelian group laws.

Rewrite using `[hz]`. Conclude with `S.sub_mem hxS (Submodule.mem_inf.mp hyR).1`. Establish `hz0 : z = 0`. Establish `hzU : z ∈ S ⊓ B.orthogonal (S ⊓ S')` using `Submodule.mem_inf.mpr ⟨hzS, hzO⟩`. Rewrite `hzU` using `[hUbot]`.

Conclude with `(Submodule.mem_bot K).mp hzU`. Rewrite using `[← hyz, hz0, add_zero]`. Conclude with `(Submodule.mem_inf.mp hyR).2`.
-/
theorem completeReducibility_holds : CompleteRed := by
  intro K N q _ _ _ _ _ _ T B hU S S' hS hS' hhw
  classical
  have hrefl : B.IsRefl := by
    intro x y h
    exact (hU.symm y x).trans h
  have hRst : Stab T (S ⊓ S') := fun a b x hx =>
    Submodule.mem_inf.mpr ⟨hS a b x (Submodule.mem_inf.mp hx).1, hS' a b x (Submodule.mem_inf.mp hx).2⟩
  have hUst : Stab T (S ⊓ B.orthogonal (S ⊓ S')) := by
    intro a b x hx
    obtain ⟨hxS, hxO⟩ := Submodule.mem_inf.mp hx
    refine Submodule.mem_inf.mpr ⟨hS a b x hxS, ?_⟩
    rw [LinearMap.BilinForm.mem_orthogonal_iff]
    intro n hn
    rw [hU.symm, hU.adj, hU.symm]
    exact (LinearMap.BilinForm.mem_orthogonal_iff.mp hxO) _ (hRst b a n hn)
  have hUbot : S ⊓ B.orthogonal (S ⊓ S') = ⊥ := by
    by_contra hne
    obtain ⟨v, hvU, hv0, μ, hμ⟩ := existsHighestWeight_holds K N q T hU.gl hU.diag _ hUst hne
    obtain ⟨hvS, hvO⟩ := Submodule.mem_inf.mp hvU
    have hvS' := hhw v hvS μ hμ
    have hvv := (LinearMap.BilinForm.mem_orthogonal_iff.mp hvO) v (Submodule.mem_inf.mpr ⟨hvS, hvS'⟩)
    exact (hU.pos v hv0).ne' hvv
  have hcompl : IsCompl (S ⊓ S') (B.orthogonal (S ⊓ S')) :=
    (LinearMap.BilinForm.isCompl_orthogonal_iff_disjoint hrefl).mpr
      (Submodule.disjoint_def.mpr fun x hxR hxO =>
        Classical.byContradiction fun h =>
          (hU.pos x h).ne' ((LinearMap.BilinForm.mem_orthogonal_iff.mp hxO) x hxR))
  intro x hxS
  have hx : x ∈ (S ⊓ S') ⊔ B.orthogonal (S ⊓ S') := by
    rw [hcompl.sup_eq_top]
    exact Submodule.mem_top
  obtain ⟨y, hyR, z, hzO, hyz⟩ := Submodule.mem_sup.mp hx
  have hzS : z ∈ S := by
    have hz : z = x - y := by
      rw [← hyz]
      abel
    rw [hz]
    exact S.sub_mem hxS (Submodule.mem_inf.mp hyR).1
  have hz0 : z = 0 := by
    have hzU : z ∈ S ⊓ B.orthogonal (S ⊓ S') := Submodule.mem_inf.mpr ⟨hzS, hzO⟩
    rw [hUbot] at hzU
    exact (Submodule.mem_bot K).mp hzU
  rw [← hyz, hz0, add_zero]
  exact (Submodule.mem_inf.mp hyR).2

end Formalism.CohomologicalDescent.LP

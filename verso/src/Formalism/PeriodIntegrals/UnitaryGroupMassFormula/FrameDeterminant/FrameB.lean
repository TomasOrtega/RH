import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.FrameDeterminant.FrameA

noncomputable section

open NumberField

namespace PI.FlagFrameDeterminants

open Formalism.MainNotions.S Formalism.MainNotions.S.Lat PI.IsoDetDefs

section Gen

variable {E : Type} [Field E] [NumberField E] [StarRing E] {S : Formalism.BasicNotions.HSpace E} {r : ℕ} {T : E}

/- English proof (translation)
Proceed by induction on `hv using Submodule.span_induction with`. Consider the case `mem y hy`. Take `⟨a, x, hx, rfl⟩` from `hy`. Use `⟨Pi.single a x, fun b => ?_, ?_⟩` and prove the remaining obligations. Distinguish the cases in `hb : b = a`.

Substitute `hb` using the available equality. Simplify using `using hx`. Simplify using `[hb, (𝔞 b).zero_mem]`. Simplify using `[Pi.single_apply, ite_smul]`. Consider the case `zero => exact ⟨0, fun a => (𝔞 a).zero_mem, by simp⟩`.

Consider the case `add y y' _ _ hy hy'`. Take `⟨c, hc, rfl⟩` from `hy`. Take `⟨c', hc', rfl⟩` from `hy'`. Conclude with `⟨c + c', fun a => Submodule.add_mem (𝔞 a : Submodule (𝓞 E) E) (hc a) (hc' a), by simp [add_smul, Finset.sum_add_distrib]⟩`. Consider the case `smul o y _ hy`.

Take `⟨c, hc, rfl⟩` from `hy`. Use `⟨fun a => (o : E) * c a, fun a => ?_, ?_⟩` and prove the remaining obligations. Use `Submodule.smul_mem (𝔞 a : Submodule (𝓞 E) E) o (hc a)` as an intermediate fact. Simplify `this` using `[Algebra.smul_def]`. Rewrite using `[Finset.smul_sum]`.

Use `Finset.sum_congr rfl fun a _ => ?_` and prove the remaining obligations. Rewrite using `[← algebraMap_smul E o (c a • e a), smul_smul]`.
-/
theorem mem_frameSpan {ι : Type} [Fintype ι] (𝔞 : ι → FractionalIdeal (nonZeroDivisors (𝓞 E)) E)
    (e : ι → S.V) {v : S.V}
    (hv : v ∈ Submodule.span (𝓞 E) {y | ∃ (a : ι) (x : E), x ∈ 𝔞 a ∧ y = x • e a}) :
    ∃ c : ι → E, (∀ a, c a ∈ 𝔞 a) ∧ v = ∑ a, c a • e a := by
  classical
  induction hv using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨a, x, hx, rfl⟩ := hy
    refine ⟨Pi.single a x, fun b => ?_, ?_⟩
    · by_cases hb : b = a
      · subst hb; simpa using hx
      · simp [hb, (𝔞 b).zero_mem]
    · simp [Pi.single_apply, ite_smul]
  | zero => exact ⟨0, fun a => (𝔞 a).zero_mem, by simp⟩
  | add y y' _ _ hy hy' =>
    obtain ⟨c, hc, rfl⟩ := hy
    obtain ⟨c', hc', rfl⟩ := hy'
    exact ⟨c + c', fun a => Submodule.add_mem (𝔞 a : Submodule (𝓞 E) E) (hc a) (hc' a),
      by simp [add_smul, Finset.sum_add_distrib]⟩
  | smul o y _ hy =>
    obtain ⟨c, hc, rfl⟩ := hy
    refine ⟨fun a => (o : E) * c a, fun a => ?_, ?_⟩
    · have := Submodule.smul_mem (𝔞 a : Submodule (𝓞 E) E) o (hc a)
      simpa [Algebra.smul_def] using this
    · rw [Finset.smul_sum]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [← algebraMap_smul E o (c a • e a), smul_smul]

/- English proof (translation)
Use `Submodule.sum_mem _ fun a _ => ?_` and prove the remaining obligations. Use `(le_iSup (fun a => ((𝔞 a : Submodule (𝓞 E) E)).map ((LinearMap.toSpanSingleton E S.V (e a)).restrictScalars (𝓞 E))) a) ?_` and prove the remaining obligations. Conclude with `⟨c a, hc a, rfl⟩`.
-/
theorem mem_pseudoSpan_of {n : ℕ} (𝔞 : Fin n → FractionalIdeal (nonZeroDivisors (𝓞 E)) E)
    (e : Fin n → S.V) (c : Fin n → E) (hc : ∀ a, c a ∈ 𝔞 a) : ∑ a, c a • e a ∈ pseudoSpan 𝔞 e := by
  refine Submodule.sum_mem _ fun a _ => ?_
  refine (le_iSup (fun a => ((𝔞 a : Submodule (𝓞 E) E)).map
    ((LinearMap.toSpanSingleton E S.V (e a)).restrictScalars (𝓞 E))) a) ?_
  exact ⟨c a, hc a, rfl⟩

/- English proof (translation)
The claim follows from `Submodule.span_mono (Set.image_subset_range _ _)`.
-/
theorem partial_flag_le_total (F : FlagG S r T) (j : ℕ) : F.Xa j ≤ F.X :=
  Submodule.span_mono (Set.image_subset_range _ _)

/- English proof (translation)
The claim follows from `Submodule.subset_span ⟨a, ha, rfl⟩`.
-/
theorem e_mem_xa (F : FlagG S r T) {j : ℕ} (a : Fin r) (ha : a.val < j) : F.e a ∈ F.Xa j :=
  Submodule.subset_span ⟨a, ha, rfl⟩

/- English proof (translation)
Apply `le_antisymm` to reduce the goal to its premises. Introduce `v hv`. Establish `hvX : v ∈ Λ ⊓ toO S F.X` using `⟨hv.1, partial_flag_le_total F j hv.2⟩`. Rewrite `hvX` using `[hX]`. Take `⟨c, hc, rfl⟩` from `mem_frameSpan 𝔞 F.e hvX`.

Take `⟨k, rfl⟩` from `Nat.exists_eq_add_of_le hj`. Rewrite `hv`, the goal using `[Fin.sum_univ_add]`. Establish `h1 : ∑ i : Fin j, c (Fin.castAdd k i) • F.e (Fin.castAdd k i) ∈ F.Xa j` using `Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (e_mem_xa F _ (by simp))`. Establish `h2 : ∑ i : Fin k, c (Fin.natAdd j i) • F.e (Fin.natAdd j i) ∈ Submodule.span E (F.e '' {a | j ≤ a.val})` using `Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, by simp, rfl⟩)`. Establish `h3 : ∑ i : Fin k, c (Fin.natAdd j i) • F.e (Fin.natAdd j i) ∈ F.Xa j`.

Use `(F.Xa j).sub_mem hv.2 h1` as an intermediate fact. Simplify using `using this`. Establish `hdis` using `F.e_indep.disjoint_span_image (s := {a : Fin (j + k) | a.val < j}) (t := {a | j ≤ a.val}) (Set.disjoint_left.mpr fun a ha hb => by simp at ha hb; omega)`. Establish `h0 : ∑ i : Fin k, c (Fin.natAdd j i) • F.e (Fin.natAdd j i) = 0` using `(Submodule.disjoint_def.mp hdis) _ h3 h2`. Rewrite using `[h0, add_zero]`.

Use `mem_pseudoSpan_of (fun a : Fin j => 𝔞 (Fin.castLE hj a)) (fun a => F.e (Fin.castLE hj a)) (fun a => c (Fin.castLE hj a)) (fun a => hc _)` as an intermediate fact. Apply the tactic sequence `convert this using 3 <;> rfl`. Use `iSup_le fun a => ?_` and prove the remaining obligations. Introduce and unpack `v ⟨x, hx, rfl⟩`. Establish `hm : x • F.e (Fin.castLE hj a) ∈ Λ ⊓ toO S F.X`.

Rewrite using `[hX]`. Conclude with `Submodule.subset_span ⟨_, x, hx, rfl⟩`. Conclude with `⟨hm.1, Submodule.smul_mem _ _ (e_mem_xa F _ (by simp))⟩`.
-/
theorem inf_xa_eq (F : FlagG S r T) (Λ : Submodule (𝓞 E) S.V)
    (𝔞 : Fin r → FractionalIdeal (nonZeroDivisors (𝓞 E)) E)
    (hX : Λ ⊓ toO S F.X = Submodule.span (𝓞 E) {y | ∃ (a : Fin r) (x : E), x ∈ 𝔞 a ∧ y = x • F.e a})
    {j : ℕ} (hj : j ≤ r) :
    Λ ⊓ toO S (F.Xa j) = pseudoSpan (fun a : Fin j => 𝔞 (Fin.castLE hj a)) (fun a => F.e (Fin.castLE hj a)) := by
  classical
  apply le_antisymm
  · intro v hv
    have hvX : v ∈ Λ ⊓ toO S F.X := ⟨hv.1, partial_flag_le_total F j hv.2⟩
    rw [hX] at hvX
    obtain ⟨c, hc, rfl⟩ := mem_frameSpan 𝔞 F.e hvX
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hj
    rw [Fin.sum_univ_add] at hv ⊢
    have h1 : ∑ i : Fin j, c (Fin.castAdd k i) • F.e (Fin.castAdd k i) ∈ F.Xa j :=
      Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (e_mem_xa F _ (by simp))
    have h2 : ∑ i : Fin k, c (Fin.natAdd j i) • F.e (Fin.natAdd j i) ∈
        Submodule.span E (F.e '' {a | j ≤ a.val}) :=
      Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, by simp, rfl⟩)
    have h3 : ∑ i : Fin k, c (Fin.natAdd j i) • F.e (Fin.natAdd j i) ∈ F.Xa j := by
      have := (F.Xa j).sub_mem hv.2 h1
      simpa using this
    have hdis := F.e_indep.disjoint_span_image (s := {a : Fin (j + k) | a.val < j}) (t := {a | j ≤ a.val})
      (Set.disjoint_left.mpr fun a ha hb => by simp at ha hb; omega)
    have h0 : ∑ i : Fin k, c (Fin.natAdd j i) • F.e (Fin.natAdd j i) = 0 :=
      (Submodule.disjoint_def.mp hdis) _ h3 h2
    rw [h0, add_zero]
    have := mem_pseudoSpan_of (fun a : Fin j => 𝔞 (Fin.castLE hj a)) (fun a => F.e (Fin.castLE hj a))
      (fun a => c (Fin.castLE hj a)) (fun a => hc _)
    convert this using 3 <;> rfl
  · refine iSup_le fun a => ?_
    rintro v ⟨x, hx, rfl⟩
    have hm : x • F.e (Fin.castLE hj a) ∈ Λ ⊓ toO S F.X := by
      rw [hX]; exact Submodule.subset_span ⟨_, x, hx, rfl⟩
    exact ⟨hm.1, Submodule.smul_mem _ _ (e_mem_xa F _ (by simp))⟩

end Gen

end PI.FlagFrameDeterminants

import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.IrreducibleDistinctUnitary
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.GenericDetPowMulHw
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.NonemptyDirectSumEquivOfFinrankLe
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.IsSemisimpleRepresentationTprodOfIsIrreducibleAl
import Formalism.GradedWeylDivisibility.DualWeylDominanceOf
import Formalism.GradedWeylDivisibility.FinalB

open MvPolynomial Formalism.BasicNotions Formalism.GradedWeylDivisibility GlobalTheory.Branching GlobalTheory.GLDuality
open Formalism.REAL (fockF)
open scoped DirectSum TensorProduct Kronecker Matrix

namespace GlobalTheory.GLDuality.HighestLine

/- English proof (translation)
Simplify using `only [Finsupp.weight_apply]`. Rewrite using `[Finsupp.sum_mapDomain_index (h := fun (x : Fin r × Fin n) (c : ℕ) => c • colW r n x) (fun _ => zero_smul _ _) (fun _ _ _ => add_smul _ _ _)]`. Rewrite using `[Finsupp.sum, Finsupp.sum, Finset.sum_apply, Finset.sum_apply]`. Use `Finset.sum_congr rfl fun x _ => ?_` and prove the remaining obligations. Simplify using `[colW, Pi.single_apply, Fin.castLE_inj]`.
-/
theorem weight_mapDomain {r m n : ℕ} (h : m ≤ n) (u : Fin r × Fin m →₀ ℕ) (i : Fin m) :
    Finsupp.weight (colW r n) (Finsupp.mapDomain (Prod.map id (Fin.castLE h)) u) (Fin.castLE h i) =
      Finsupp.weight (colW r m) u i := by
  classical
  simp only [Finsupp.weight_apply]
  rw [Finsupp.sum_mapDomain_index (h := fun (x : Fin r × Fin n) (c : ℕ) => c • colW r n x)
    (fun _ => zero_smul _ _) (fun _ _ _ => add_smul _ _ _)]
  rw [Finsupp.sum, Finsupp.sum, Finset.sum_apply, Finset.sum_apply]
  refine Finset.sum_congr rfl fun x _ => ?_
  simp [colW, Pi.single_apply, Fin.castLE_inj]

/- English proof (translation)
Rewrite using `[Finsupp.weight_apply, Finsupp.sum, Finset.sum_apply]`. Distinguish the cases in `hx : u x = 0`. Rewrite using `[hx]`. Conclude with `Nat.zero_le _`. Use `le_trans ?_ (Finset.single_le_sum (f := fun y => (u y • colW r n y) x.2) (fun y _ => Nat.zero_le _) (Finsupp.mem_support_iff.mpr hx))` and prove the remaining obligations.

Simplify using `[colW]`.
-/
theorem le_weight {r n : ℕ} (u : Fin r × Fin n →₀ ℕ) (x : Fin r × Fin n) :
    u x ≤ Finsupp.weight (colW r n) u x.2 := by
  classical
  rw [Finsupp.weight_apply, Finsupp.sum, Finset.sum_apply]
  by_cases hx : u x = 0
  · rw [hx]; exact Nat.zero_le _
  · refine le_trans ?_ (Finset.single_le_sum (f := fun y => (u y • colW r n y) x.2)
      (fun y _ => Nat.zero_le _) (Finsupp.mem_support_iff.mpr hx))
    simp [colW]

/- English proof (translation)
Establish `key : (colAdd ℂ (Fin.castLE h l) (Fin.castLE h j) c).comp (rename (Prod.map id (Fin.castLE h))) = (rename (Prod.map id (Fin.castLE h))).comp (colAdd ℂ (r` using `r) l j c) := by`. Apply `MvPolynomial.algHom_ext` to reduce the goal to its premises. Introduce and unpack `⟨a, s⟩`. Simplify using `only [AlgHom.comp_apply, rename_X, colAdd, aeval_X, Prod.map_apply, id_eq, Fin.castLE_inj]`. Apply the tactic sequence `split_ifs <;> simp [rename_X]`.

Conclude with `DFunLike.congr_fun key f`.
-/
theorem colAdd_rename {r m n : ℕ} (h : m ≤ n) (l j : Fin m) (c : ℂ) (f : MvPolynomial (Fin r × Fin m) ℂ) :
    colAdd ℂ (Fin.castLE h l) (Fin.castLE h j) c (rename (Prod.map id (Fin.castLE h)) f) =
      rename (Prod.map id (Fin.castLE h)) (colAdd ℂ l j c f) := by
  have key : (colAdd ℂ (Fin.castLE h l) (Fin.castLE h j) c).comp (rename (Prod.map id (Fin.castLE h))) =
      (rename (Prod.map id (Fin.castLE h))).comp (colAdd ℂ (r := r) l j c) := by
    apply MvPolynomial.algHom_ext
    rintro ⟨a, s⟩
    simp only [AlgHom.comp_apply, rename_X, colAdd, aeval_X, Prod.map_apply, id_eq, Fin.castLE_inj]
    split_ifs <;> simp [rename_X]
  exact DFunLike.congr_fun key f

/- English proof (translation)
Establish `key : (rowGen ℂ (n` using `n) a b).comp (rename (Prod.map id (Fin.castLE h))) = (Polynomial.mapAlgHom (rename (Prod.map id (Fin.castLE h)))).comp (rowGen ℂ (n := m) a b) := by`. Apply `MvPolynomial.algHom_ext` to reduce the goal to its premises. Introduce and unpack `⟨x, s⟩`. Simplify using `only [AlgHom.comp_apply, rename_X, rowGen, aeval_X, Prod.map_apply, id_eq]`. Apply the tactic sequence `split_ifs <;> simp [rename_X, Polynomial.coe_mapAlgHom]`.

Establish `hf` using `DFunLike.congr_fun key f`. Simplify using `only [AlgHom.comp_apply] at hf`. Simplify using `only [rowDiv]`. Rewrite using `[hf]`. Simplify using `[Polynomial.coe_mapAlgHom, Polynomial.coeff_map]`.
-/
theorem rowDiv_rename {r m n : ℕ} (h : m ≤ n) (a b : Fin r) (k : ℕ) (f : MvPolynomial (Fin r × Fin m) ℂ) :
    rowDiv ℂ a b k (rename (Prod.map id (Fin.castLE h)) f) =
      rename (Prod.map id (Fin.castLE h)) (rowDiv ℂ a b k f) := by
  have key : (rowGen ℂ (n := n) a b).comp (rename (Prod.map id (Fin.castLE h))) =
      (Polynomial.mapAlgHom (rename (Prod.map id (Fin.castLE h)))).comp (rowGen ℂ (n := m) a b) := by
    apply MvPolynomial.algHom_ext
    rintro ⟨x, s⟩
    simp only [AlgHom.comp_apply, rename_X, rowGen, aeval_X, Prod.map_apply, id_eq]
    split_ifs <;> simp [rename_X, Polynomial.coe_mapAlgHom]
  have hf := DFunLike.congr_fun key f
  simp only [AlgHom.comp_apply] at hf
  simp only [rowDiv]
  rw [hf]
  simp [Polynomial.coe_mapAlgHom, Polynomial.coeff_map]

/- English proof (translation)
Establish `hφi : Function.Injective (Prod.map id (Fin.castLE h) : Fin r × Fin r → Fin r × Fin n)` using `Function.Injective.prodMap Function.injective_id (Fin.castLE_injective h)`. Establish `hpt` using `(dualWeylPoint ℂ r n ν f).1 hf`. Establish `hvars : (f.vars : Set (Fin r × Fin n)) ⊆ Set.range (Prod.map id (Fin.castLE h) : Fin r × Fin r → Fin r × Fin n)`. Introduce `x hx`. Rewrite `hx` using `[Finset.mem_coe, MvPolynomial.mem_vars]`.

Take `⟨u, hu, hxu⟩` from `hx`. Establish `hwu : Finsupp.weight (colW r n) u = ν` using `hpt.1 (MvPolynomial.mem_support_iff.mp hu)`. Establish `hx2 : x.2.val < r`. Assume the negation of the conclusion as `hlt`. Establish `h1` using `le_weight u x`.

Rewrite `h1` using `[hwu, h0 x.2 (not_lt.mp hlt)]`. Conclude with `(Finsupp.mem_support_iff.mp hxu) (Nat.le_zero.mp h1)`. Conclude with `⟨(x.1, ⟨x.2.val, hx2⟩), Prod.ext rfl (Fin.ext rfl)⟩`. Take `⟨g, rfl⟩` from `exists_rename_eq_of_vars_subset_range f _ hφi hvars`. Establish `hgw : IsWeightedHomogeneous (colW r r) g (fun i => ν (Fin.castLE h i))`.

Introduce `u hu`. Establish `hu' : coeff (Finsupp.mapDomain (Prod.map id (Fin.castLE h)) u) (rename (Prod.map id (Fin.castLE h)) g) ≠ 0`. Rewrite using `[coeff_rename_mapDomain _ hφi]` and apply the resulting hypothesis. Establish `hwu` using `hpt.1 hu'`. Use function extensionality and compare the values at `i`.

Rewrite using `[← weight_mapDomain h u i, hwu]`. Establish `hgc : ∀ l j : Fin r, l < j → ∀ c : ℂ, colAdd ℂ l j c g = g`. Introduce `l j hlj c`. Apply `rename_injective _ hφi` to reduce the goal to its premises. Rewrite using `[← colAdd_rename h]`.

Conclude with `hpt.2 _ _ (show Fin.castLE h l < Fin.castLE h j from hlj) c`. Establish `hg : g ∈ dualWeyl ℂ r r (fun i => ν (Fin.castLE h i))` using `(dualWeylPoint ℂ r r _ g).2 ⟨hgw, hgc⟩`. Establish `hgk : ∀ a b : Fin r, a < b → ∀ k : ℕ, 1 ≤ k → rowDiv ℂ a b k g = 0`. Introduce `a b hab k hk1`. Apply `rename_injective _ hφi` to reduce the goal to its premises.

Rewrite using `[← rowDiv_rename h, map_zero]`. Conclude with `hk a b hab k hk1`. Establish `hant : Antitone (fun i : Fin r => ν (Fin.castLE h i))` using `fun i j hij => hν (show Fin.castLE h i ≤ Fin.castLE h j from hij)`. Take `⟨c, hc⟩` from `hwLine ℂ r r le_rfl _ hant g hg hgk`. Conclude with `⟨c, by rw [hc, map_smul]⟩`.
-/
theorem wide {r n : ℕ} (h : r ≤ n) (ν : Fin n → ℕ) (hν : Antitone ν) (h0 : ∀ s : Fin n, r ≤ s.val → ν s = 0)
    (f : MvPolynomial (Fin r × Fin n) ℂ) (hf : f ∈ dualWeyl ℂ r n ν)
    (hk : ∀ a b : Fin r, a < b → ∀ k : ℕ, 1 ≤ k → rowDiv ℂ a b k f = 0) :
    ∃ c : ℂ, f = c • rename (Prod.map id (Fin.castLE h)) (hw ℂ le_rfl fun i => ν (Fin.castLE h i)) := by
  classical
  have hφi : Function.Injective (Prod.map id (Fin.castLE h) : Fin r × Fin r → Fin r × Fin n) :=
    Function.Injective.prodMap Function.injective_id (Fin.castLE_injective h)
  have hpt := (dualWeylPoint ℂ r n ν f).1 hf
  have hvars : (f.vars : Set (Fin r × Fin n)) ⊆
      Set.range (Prod.map id (Fin.castLE h) : Fin r × Fin r → Fin r × Fin n) := by
    intro x hx
    rw [Finset.mem_coe, MvPolynomial.mem_vars] at hx
    obtain ⟨u, hu, hxu⟩ := hx
    have hwu : Finsupp.weight (colW r n) u = ν := hpt.1 (MvPolynomial.mem_support_iff.mp hu)
    have hx2 : x.2.val < r := by
      by_contra hlt
      have h1 := le_weight u x
      rw [hwu, h0 x.2 (not_lt.mp hlt)] at h1
      exact (Finsupp.mem_support_iff.mp hxu) (Nat.le_zero.mp h1)
    exact ⟨(x.1, ⟨x.2.val, hx2⟩), Prod.ext rfl (Fin.ext rfl)⟩
  obtain ⟨g, rfl⟩ := exists_rename_eq_of_vars_subset_range f _ hφi hvars
  have hgw : IsWeightedHomogeneous (colW r r) g (fun i => ν (Fin.castLE h i)) := by
    intro u hu
    have hu' : coeff (Finsupp.mapDomain (Prod.map id (Fin.castLE h)) u)
        (rename (Prod.map id (Fin.castLE h)) g) ≠ 0 := by
      rwa [coeff_rename_mapDomain _ hφi]
    have hwu := hpt.1 hu'
    funext i
    rw [← weight_mapDomain h u i, hwu]
  have hgc : ∀ l j : Fin r, l < j → ∀ c : ℂ, colAdd ℂ l j c g = g := by
    intro l j hlj c
    apply rename_injective _ hφi
    rw [← colAdd_rename h]
    exact hpt.2 _ _ (show Fin.castLE h l < Fin.castLE h j from hlj) c
  have hg : g ∈ dualWeyl ℂ r r (fun i => ν (Fin.castLE h i)) :=
    (dualWeylPoint ℂ r r _ g).2 ⟨hgw, hgc⟩
  have hgk : ∀ a b : Fin r, a < b → ∀ k : ℕ, 1 ≤ k → rowDiv ℂ a b k g = 0 := by
    intro a b hab k hk1
    apply rename_injective _ hφi
    rw [← rowDiv_rename h, map_zero]
    exact hk a b hab k hk1
  have hant : Antitone (fun i : Fin r => ν (Fin.castLE h i)) := fun i j hij =>
    hν (show Fin.castLE h i ≤ Fin.castLE h j from hij)
  obtain ⟨c, hc⟩ := hwLine ℂ r r le_rfl _ hant g hg hgk
  exact ⟨c, by rw [hc, map_smul]⟩

/- English proof (translation)
Introduce `r n ν v hv hkv hv0`. Establish `hant : Antitone ν`. Introduce `i j hij`. Assume the negation of the conclusion as `hlt`. Use `push_neg at hlt`.

Establish `hij' : i < j` using `lt_of_le_of_ne hij (by rintro rfl; exact lt_irrefl _ hlt)`. Establish `hbot` using `dualWeylNonDom ℂ r n ν ⟨i, j, hij', hlt⟩`. Rewrite `hv` using `[hbot]`. Conclude with `hv0 ((Submodule.mem_bot ℂ).mp hv)`. Establish `h0 : ∀ s : Fin n, r ≤ s.val → ν s = 0`.

Introduce `s hs`. Assume the negation of the conclusion as `hne`. Conclude with `hv0 (hwLineTall ℂ r n ν ⟨s, hs, Nat.pos_of_ne_zero hne⟩ v hv hkv)`. Establish `hline : ∃ H : MvPolynomial (Fin r × Fin n) ℂ, ∀ w ∈ dualWeyl ℂ r n ν, (∀ a b : Fin r, a < b → ∀ k : ℕ, 1 ≤ k → rowDiv ℂ a b k w = 0) → ∃ c : ℂ, w = c • H`. Break down `le_total n r with hnr | hrn` into its components or cases.

Conclude with `⟨hw ℂ hnr ν, fun w hw' hk => hwLine ℂ r n hnr ν hant w hw' hk⟩`. Conclude with `⟨_, fun w hw' hk => wide hrn ν hant h0 w hw' hk⟩`. Take `⟨H, hH⟩` from `hline`. Use `⟨⟨⟨fun i => ν (Fin.castLE (min_le_left n r) i), fun i j hij => hant (show Fin.castLE (min_le_left n r) i ≤ Fin.castLE (min_le_left n r) j from hij)⟩, ?_⟩, ?_⟩` and prove the remaining obligations. Use function extensionality and compare the values at `s`.

Simplify using `only [rowNu]`. Use `split_ifs with hs`. Conclude with `congrArg ν (Fin.ext rfl)`. Establish `hsn` using `s.isLt`. Conclude with `h0 s (by omega)`.

Introduce `w hw' hkw`. Take `⟨c₀, hc₀⟩` from `hH v hv hkv`. Take `⟨c₁, hc₁⟩` from `hH w hw' hkw`. Establish `hc0 : c₀ ≠ 0`. Introduce and unpack `rfl`.

Conclude with `hv0 (by rw [hc₀, zero_smul])`. Use `⟨c₁ / c₀, ?_⟩` and prove the remaining obligations. Rewrite using `[hc₁, hc₀, smul_smul, div_mul_cancel₀ _ hc0]`.
-/
theorem highest_line : ∀ (r n : ℕ) (ν : Fin n → ℕ) (v : MvPolynomial (Fin r × Fin n) ℂ), v ∈ dualWeyl ℂ r n ν → (∀ a b : Fin r, a < b → ∀ k : ℕ, 1 ≤ k → rowDiv ℂ a b k v = 0) → v ≠ 0 → (∃ a : Part (min n r), ν = rowNu (r := n) a.1) ∧ ∀ w ∈ dualWeyl ℂ r n ν, (∀ a b : Fin r, a < b → ∀ k : ℕ, 1 ≤ k → rowDiv ℂ a b k w = 0) → ∃ c : ℂ, w = c • v := by
  intro r n ν v hv hkv hv0
  have hant : Antitone ν := by
    intro i j hij
    by_contra hlt
    push_neg at hlt
    have hij' : i < j := lt_of_le_of_ne hij (by rintro rfl; exact lt_irrefl _ hlt)
    have hbot := dualWeylNonDom ℂ r n ν ⟨i, j, hij', hlt⟩
    rw [hbot] at hv
    exact hv0 ((Submodule.mem_bot ℂ).mp hv)
  have h0 : ∀ s : Fin n, r ≤ s.val → ν s = 0 := by
    intro s hs
    by_contra hne
    exact hv0 (hwLineTall ℂ r n ν ⟨s, hs, Nat.pos_of_ne_zero hne⟩ v hv hkv)
  have hline : ∃ H : MvPolynomial (Fin r × Fin n) ℂ, ∀ w ∈ dualWeyl ℂ r n ν,
      (∀ a b : Fin r, a < b → ∀ k : ℕ, 1 ≤ k → rowDiv ℂ a b k w = 0) → ∃ c : ℂ, w = c • H := by
    rcases le_total n r with hnr | hrn
    · exact ⟨hw ℂ hnr ν, fun w hw' hk => hwLine ℂ r n hnr ν hant w hw' hk⟩
    · exact ⟨_, fun w hw' hk => wide hrn ν hant h0 w hw' hk⟩
  obtain ⟨H, hH⟩ := hline
  refine ⟨⟨⟨fun i => ν (Fin.castLE (min_le_left n r) i), fun i j hij =>
    hant (show Fin.castLE (min_le_left n r) i ≤ Fin.castLE (min_le_left n r) j from hij)⟩, ?_⟩, ?_⟩
  · funext s
    simp only [rowNu]
    split_ifs with hs
    · exact congrArg ν (Fin.ext rfl)
    · have hsn := s.isLt
      exact h0 s (by omega)
  · intro w hw' hkw
    obtain ⟨c₀, hc₀⟩ := hH v hv hkv
    obtain ⟨c₁, hc₁⟩ := hH w hw' hkw
    have hc0 : c₀ ≠ 0 := by
      rintro rfl
      exact hv0 (by rw [hc₀, zero_smul])
    refine ⟨c₁ / c₀, ?_⟩
    rw [hc₁, hc₀, smul_smul, div_mul_cancel₀ _ hc0]

end GlobalTheory.GLDuality.HighestLine

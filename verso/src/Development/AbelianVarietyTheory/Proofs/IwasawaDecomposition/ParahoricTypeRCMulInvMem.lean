import Mathlib
import Formalism.LocalToGlobal.Divisibility.QLocTied
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.HostPins
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIsUnrM
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIsNrm
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsAddHaarCompletionIntegralMatricesVolOne
import Development.AbelianVarietyTheory.Definitions.Divisors.T2SpaceGeneralLinearGroup

open MeasureTheory Matrix NumberField IsDedekindDomain Formalism.BasicNotions Formalism.DoubleCosetMeasures Formalism.L2.Host Formalism.L2.DIV Formalism.L2.DIV.QLoc GlobalTheory.Mem.HD

namespace GlobalTheory.ParGroup

variable {F : Type} [Field F] (O : Subring F) (ϖ : F)

def InW (x : F) : Prop := ∃ o ∈ O, x = ϖ * o

/- English proof (translation)
Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty => exact ⟨0, O.zero_mem, by simp⟩`. Consider the case `@insert a s ha ih`. Rewrite using `[Finset.sum_insert ha]`. Take `⟨o₁, ho₁, e₁⟩` from `h a (Finset.mem_insert_self a s)`.

Take `⟨o₂, ho₂, e₂⟩` from `ih (fun i hi => h i (Finset.mem_insert_of_mem hi))`. Conclude with `⟨o₁ + o₂, O.add_mem ho₁ ho₂, by rw [e₁, e₂, mul_add]⟩`.
-/
theorem inW_sum {ι : Type} (s : Finset ι) (f : ι → F) (h : ∀ i ∈ s, InW O ϖ (f i)) :
    InW O ϖ (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨0, O.zero_mem, by simp⟩
  | @insert a s ha ih =>
    rw [Finset.sum_insert ha]
    obtain ⟨o₁, ho₁, e₁⟩ := h a (Finset.mem_insert_self a s)
    obtain ⟨o₂, ho₂, e₂⟩ := ih (fun i hi => h i (Finset.mem_insert_of_mem hi))
    exact ⟨o₁ + o₂, O.add_mem ho₁ ho₂, by rw [e₁, e₂, mul_add]⟩

/- English proof (translation)
Take `⟨o, ho, rfl⟩` from `hx`. Conclude with `⟨o * a, O.mul_mem ho ha, by ring⟩`.
-/
theorem inW_mul_right {x a : F} (hx : InW O ϖ x) (ha : a ∈ O) : InW O ϖ (x * a) := by
  obtain ⟨o, ho, rfl⟩ := hx
  exact ⟨o * a, O.mul_mem ho ha, by ring⟩

/- English proof (translation)
Take `⟨o, ho, rfl⟩` from `hx`. Conclude with `⟨a * o, O.mul_mem ha ho, by ring⟩`.
-/
theorem inW_mul_left {x a : F} (ha : a ∈ O) (hx : InW O ϖ x) : InW O ϖ (a * x) := by
  obtain ⟨o, ho, rfl⟩ := hx
  exact ⟨a * o, O.mul_mem ha ho, by ring⟩

/- English proof (translation)
Take `⟨hkG, hkW⟩` from `hk`. Take `⟨hkG', hkW'⟩` from `hk'`. Use `⟨(GLint O (r + c)).mul_mem hkG hkG', ?_⟩` and prove the remaining obligations. Establish `hI : IsInt O (k : Matrix (Fin (r + c)) (Fin (r + c)) F)` using `hkG.1`. Establish `hI' : IsInt O (k' : Matrix (Fin (r + c)) (Fin (r + c)) F)` using `hkG'.1`.

Introduce `i j`. Use `show InW O ϖ _`. Simplify using `only [bDA, Matrix.submatrix_apply, Units.val_mul, Matrix.mul_apply]`. Apply `inW_sum` to reduce the goal to its premises. Introduce `l _`.

Use `Fin.addCases (fun l => ?_) (fun l => ?_) l` and prove the remaining obligations. Conclude with `inW_mul_right O ϖ (hkW i l) (hI' _ _)`. Conclude with `inW_mul_left O ϖ (hI _ _) (hkW' l j)`.
-/
theorem mul_mem_parJ {r c : ℕ} {k k' : GL (Fin (r + c)) F} (hk : k ∈ parJ O ϖ r c)
    (hk' : k' ∈ parJ O ϖ r c) : k * k' ∈ parJ O ϖ r c := by
  obtain ⟨hkG, hkW⟩ := hk
  obtain ⟨hkG', hkW'⟩ := hk'
  refine ⟨(GLint O (r + c)).mul_mem hkG hkG', ?_⟩
  have hI : IsInt O (k : Matrix (Fin (r + c)) (Fin (r + c)) F) := hkG.1
  have hI' : IsInt O (k' : Matrix (Fin (r + c)) (Fin (r + c)) F) := hkG'.1
  intro i j
  show InW O ϖ _
  simp only [bDA, Matrix.submatrix_apply, Units.val_mul, Matrix.mul_apply]
  apply inW_sum
  intro l _
  refine Fin.addCases (fun l => ?_) (fun l => ?_) l
  · exact inW_mul_right O ϖ (hkW i l) (hI' _ _)
  · exact inW_mul_left O ϖ (hI _ _) (hkW' l j)
/- English proof (translation)
Set `D : Matrix (Fin c) (Fin c) R` to `K.submatrix (Fin.natAdd r) (Fin.natAdd r)`. Set `T : Matrix (Fin c) (Fin c) R` to `N.submatrix (Fin.natAdd r) (Fin.natAdd r)`. Set `S : Matrix (Fin c) (Fin r) R` to `N.submatrix (Fin.natAdd r) (Fin.castAdd c)`. Establish `key : ∀ a b, (K * N) (Fin.natAdd r a) b = ∑ l : Fin c, K (Fin.natAdd r a) (Fin.natAdd r l) * N (Fin.natAdd r l) b`. Introduce `a b`.

Rewrite using `[Matrix.mul_apply, Fin.sum_univ_add]`. Simplify using `[hK]`. Establish `hDT : D * T = 1`. Use extensionality with `a b`. Establish `h` using `key a (Fin.natAdd r b)`.

Rewrite `h` using `[hKN]`. Simplify using `only [D, T, Matrix.mul_apply, Matrix.submatrix_apply]`. Rewrite using `[← h]`. Distinguish the cases in `hab : a = b`. Substitute `hab` using the available equality.

Simplify using the standard rewrite rules. Establish `hne : Fin.natAdd r a ≠ Fin.natAdd r b`. Introduce `e`. Apply `hab` to reduce the goal to its premises. Use `ext`.

Use `congrArg Fin.val e` as an intermediate fact. Simplify using `at this`. Use linear arithmetic over natural numbers and integers. Rewrite using `[Matrix.one_apply_ne hne, Matrix.one_apply_ne hab]`. Establish `hDS : D * S = 0`.

Use extensionality with `a b`. Establish `h` using `key a (Fin.castAdd c b)`. Rewrite `h` using `[hKN]`. Establish `hne : Fin.natAdd r a ≠ Fin.castAdd c b`. Introduce `e`.

Use `congrArg Fin.val e` as an intermediate fact. Establish `hb` using `b.isLt`. Simplify using `at this`. Use linear arithmetic over natural numbers and integers. Rewrite `h` using `[Matrix.one_apply_ne hne]`.

Simplify using `only [D, S, Matrix.mul_apply, Matrix.submatrix_apply, Matrix.zero_apply]`. Conclude with `h.symm`. Establish `hTD : T * D = 1` using `by first`. Consider the case `exact mul_eq_one_comm.mp hDT`. Consider the case `rw [← Matrix.inv_eq_right_inv hDT]`.

Conclude with `Matrix.nonsing_inv_mul D (Matrix.isUnit_det_of_right_inverse hDT)`. Establish `hS : S = 0`. Combine the equalities or inequalities in the displayed calculation. Conclude with `congrFun (congrFun hS i) j`.
-/
private theorem lower_block_eq_zero_of_mul_eq_one {R : Type} [CommRing R] {r c : ℕ}
    (K N : Matrix (Fin (r + c)) (Fin (r + c)) R) (hKN : K * N = 1)
    (hK : ∀ i j, K (Fin.natAdd r i) (Fin.castAdd c j) = 0) (i : Fin c) (j : Fin r) :
    N (Fin.natAdd r i) (Fin.castAdd c j) = 0 := by
  let D : Matrix (Fin c) (Fin c) R := K.submatrix (Fin.natAdd r) (Fin.natAdd r)
  let T : Matrix (Fin c) (Fin c) R := N.submatrix (Fin.natAdd r) (Fin.natAdd r)
  let S : Matrix (Fin c) (Fin r) R := N.submatrix (Fin.natAdd r) (Fin.castAdd c)
  have key : ∀ a b, (K * N) (Fin.natAdd r a) b =
      ∑ l : Fin c, K (Fin.natAdd r a) (Fin.natAdd r l) * N (Fin.natAdd r l) b := by
    intro a b
    rw [Matrix.mul_apply, Fin.sum_univ_add]
    simp [hK]
  have hDT : D * T = 1 := by
    ext a b
    have h := key a (Fin.natAdd r b)
    rw [hKN] at h
    simp only [D, T, Matrix.mul_apply, Matrix.submatrix_apply]
    rw [← h]
    by_cases hab : a = b
    · subst hab
      simp
    · have hne : Fin.natAdd r a ≠ Fin.natAdd r b := by
        intro e
        apply hab
        ext
        have := congrArg Fin.val e
        simp at this
        omega
      rw [Matrix.one_apply_ne hne, Matrix.one_apply_ne hab]
  have hDS : D * S = 0 := by
    ext a b
    have h := key a (Fin.castAdd c b)
    rw [hKN] at h
    have hne : Fin.natAdd r a ≠ Fin.castAdd c b := by
      intro e
      have := congrArg Fin.val e
      have hb := b.isLt
      simp at this
      omega
    rw [Matrix.one_apply_ne hne] at h
    simp only [D, S, Matrix.mul_apply, Matrix.submatrix_apply, Matrix.zero_apply]
    exact h.symm
  have hTD : T * D = 1 := by
    first
    | exact mul_eq_one_comm.mp hDT
    | rw [← Matrix.inv_eq_right_inv hDT]
      exact Matrix.nonsing_inv_mul D (Matrix.isUnit_det_of_right_inverse hDT)
  have hS : S = 0 := by
    calc S = (T * D) * S := by rw [hTD, Matrix.one_mul]
      _ = T * (D * S) := Matrix.mul_assoc _ _ _
      _ = 0 := by rw [hDS, Matrix.mul_zero]
  exact congrFun (congrFun hS i) j

/- English proof (translation)
Take `⟨hkG, hkW⟩` from `hk`. Use `⟨(GLint O (r + c)).inv_mem hkG, ?_⟩` and prove the remaining obligations. Establish `hI : IsInt O (k : Matrix (Fin (r + c)) (Fin (r + c)) F)` using `hkG.1`. Establish `hJ : IsInt O ((k⁻¹ : GL (Fin (r + c)) F) : Matrix (Fin (r + c)) (Fin (r + c)) F)` using `hkG.2`. Set `KO : Matrix (Fin (r + c)) (Fin (r + c)) O` to `fun a b => ⟨(k : Matrix (Fin (r + c)) (Fin (r + c)) F) a b, hI a b⟩`.

Set `NO : Matrix (Fin (r + c)) (Fin (r + c)) O` to `fun a b => ⟨((k⁻¹ : GL (Fin (r + c)) F) : Matrix (Fin (r + c)) (Fin (r + c)) F) a b, hJ a b⟩`. Establish `hKN : KO * NO = 1`. Apply `Matrix.map_injective (f := O.subtype) Subtype.val_injective` to reduce the goal to its premises. Simplify using `only`. Rewrite using `[Matrix.map_mul, Matrix.map_one _ (map_zero _) (map_one _)]`.

Establish `e1 : KO.map O.subtype = (k : Matrix (Fin (r + c)) (Fin (r + c)) F)` using `by ext; rfl`. Establish `e2 : NO.map O.subtype = ((k⁻¹ : GL (Fin (r + c)) F) : Matrix (Fin (r + c)) (Fin (r + c)) F)` using `by ext; rfl`. Rewrite using `[e1, e2, ← Units.val_mul, mul_inv_cancel, Units.val_one]`. Set `π` to `Ideal.Quotient.mk (Ideal.span {(⟨ϖ, hϖ⟩ : O)})`. Establish `hKNb : KO.map π * NO.map π = 1`.

Rewrite using `[← Matrix.map_mul, hKN, Matrix.map_one _ (map_zero _) (map_one _)]`. Establish `hK0 : ∀ i j, KO.map π (Fin.natAdd r i) (Fin.castAdd c j) = 0`. Introduce `i j`. Take `⟨o, ho, e⟩` from `hkW i j`. Rewrite using `[Matrix.map_apply, Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton']`.

Use `⟨⟨o, ho⟩, Subtype.ext ?_⟩` and prove the remaining obligations. Simplify using `only [bDA, Matrix.submatrix_apply] at e`. Simplify using `only [KO, Subring.coe_mul, e]`. Expand and normalize the polynomial expressions, which then agree. Introduce `i j`.

Establish `h0` using `lower_block_eq_zero_of_mul_eq_one (KO.map π) (NO.map π) hKNb hK0 i j`. Rewrite `h0` using `[Matrix.map_apply, Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton']`. Take `⟨⟨o, ho⟩, e⟩` from `h0`. Use `⟨o, ho, ?_⟩` and prove the remaining obligations. Establish `e'` using `congrArg Subtype.val e`.

Simplify using `only [NO, Subring.coe_mul] at e'`. Simplify using `only [bDA, Matrix.submatrix_apply]`. Rewrite using `[← e']`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem inv_mem_parJ {r c : ℕ} {k : GL (Fin (r + c)) F} (hϖ : ϖ ∈ O) (hk : k ∈ parJ O ϖ r c) :
    k⁻¹ ∈ parJ O ϖ r c := by
  obtain ⟨hkG, hkW⟩ := hk
  refine ⟨(GLint O (r + c)).inv_mem hkG, ?_⟩
  have hI : IsInt O (k : Matrix (Fin (r + c)) (Fin (r + c)) F) := hkG.1
  have hJ : IsInt O ((k⁻¹ : GL (Fin (r + c)) F) : Matrix (Fin (r + c)) (Fin (r + c)) F) := hkG.2
  let KO : Matrix (Fin (r + c)) (Fin (r + c)) O := fun a b => ⟨(k : Matrix (Fin (r + c)) (Fin (r + c)) F) a b, hI a b⟩
  let NO : Matrix (Fin (r + c)) (Fin (r + c)) O :=
    fun a b => ⟨((k⁻¹ : GL (Fin (r + c)) F) : Matrix (Fin (r + c)) (Fin (r + c)) F) a b, hJ a b⟩
  have hKN : KO * NO = 1 := by
    apply Matrix.map_injective (f := O.subtype) Subtype.val_injective
    dsimp only
    rw [Matrix.map_mul, Matrix.map_one _ (map_zero _) (map_one _)]
    have e1 : KO.map O.subtype = (k : Matrix (Fin (r + c)) (Fin (r + c)) F) := by ext; rfl
    have e2 : NO.map O.subtype = ((k⁻¹ : GL (Fin (r + c)) F) : Matrix (Fin (r + c)) (Fin (r + c)) F) := by ext; rfl
    rw [e1, e2, ← Units.val_mul, mul_inv_cancel, Units.val_one]
  let π := Ideal.Quotient.mk (Ideal.span {(⟨ϖ, hϖ⟩ : O)})
  have hKNb : KO.map π * NO.map π = 1 := by
    rw [← Matrix.map_mul, hKN, Matrix.map_one _ (map_zero _) (map_one _)]
  have hK0 : ∀ i j, KO.map π (Fin.natAdd r i) (Fin.castAdd c j) = 0 := by
    intro i j
    obtain ⟨o, ho, e⟩ := hkW i j
    rw [Matrix.map_apply, Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton']
    refine ⟨⟨o, ho⟩, Subtype.ext ?_⟩
    simp only [bDA, Matrix.submatrix_apply] at e
    simp only [KO, Subring.coe_mul, e]
    ring
  intro i j
  have h0 := lower_block_eq_zero_of_mul_eq_one (KO.map π) (NO.map π) hKNb hK0 i j
  rw [Matrix.map_apply, Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton'] at h0
  obtain ⟨⟨o, ho⟩, e⟩ := h0
  refine ⟨o, ho, ?_⟩
  have e' := congrArg Subtype.val e
  simp only [NO, Subring.coe_mul] at e'
  simp only [bDA, Matrix.submatrix_apply]
  rw [← e']
  ring

/- English proof (translation)
Introduce `F _ O ϖ hϖ r c k k' hk hk'`. Conclude with `⟨mul_mem_parJ O ϖ hk hk', inv_mem_parJ O ϖ hϖ hk⟩`.
-/
theorem parJ_mul_inv : ∀ (F : Type) [Field F] (O : Subring F) (ϖ : F), ϖ ∈ O → ∀ (r c : ℕ) (k k' : GL (Fin (r + c)) F),
    k ∈ parJ O ϖ r c → k' ∈ parJ O ϖ r c → k * k' ∈ parJ O ϖ r c ∧ k⁻¹ ∈ parJ O ϖ r c := by
  intro F _ O ϖ hϖ r c k k' hk hk'
  exact ⟨mul_mem_parJ O ϖ hk hk', inv_mem_parJ O ϖ hϖ hk⟩

end GlobalTheory.ParGroup

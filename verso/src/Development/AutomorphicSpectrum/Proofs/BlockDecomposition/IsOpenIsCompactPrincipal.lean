import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PadicIsNonarchimedeanLocalField

open ValuativeRel Matrix
open scoped Topology

namespace GlobalTheory.CompanionTheory.PrincipalCongruence

variable {k : Type*} [Field k] [ValuativeRel k]

/- English proof (translation)
Assume the negation of the conclusion as `h`. Use `push_neg at h`. Take `⟨i₁, j₁, h₁⟩` from `h`. Use `haveI : Nonempty (n × n) := ⟨(i₁, j₁)⟩`. Take `⟨⟨i₀, j₀⟩, hm⟩` from `Finite.exists_max (fun p : n × n => valuation k (B p.1 p.2 - (1 : Matrix n n k) p.1 p.2))`.

Establish `hm' : ∀ l j, valuation k (B l j - (1 : Matrix n n k) l j) ≤ valuation k (B i₀ j₀ - (1 : Matrix n n k) i₀ j₀)` using `fun l j => hm (l, j)`. Establish `hM : valuation k t < valuation k (B i₀ j₀ - (1 : Matrix n n k) i₀ j₀)` using `h₁.trans_le (hm' i₁ j₁)`. Establish `hM0 : 0 < valuation k (B i₀ j₀ - (1 : Matrix n n k) i₀ j₀)` using `lt_of_le_of_lt zero_le' hM`. Establish `hmat : (A - 1) * (B - 1) = -(A - 1) - (B - 1)`. Simplify using `only [sub_mul, mul_sub, hAB, one_mul, mul_one]`.

Normalize the expressions using the abelian group laws. Establish `key : B i₀ j₀ - (1 : Matrix n n k) i₀ j₀ = -(A i₀ j₀ - (1 : Matrix n n k) i₀ j₀) - ∑ l, (A i₀ l - (1 : Matrix n n k) i₀ l) * (B l j₀ - (1 : Matrix n n k) l j₀)`. Use `congrFun (congrFun hmat i₀) j₀` as an intermediate fact. Simplify using `only [Matrix.mul_apply, Matrix.sub_apply, Matrix.neg_apply] at this`. Rewrite using `[this]`.

Expand and normalize the polynomial expressions, which then agree. Establish `hsum : valuation k (∑ l, (A i₀ l - (1 : Matrix n n k) i₀ l) * (B l j₀ - (1 : Matrix n n k) l j₀)) ≤ valuation k t * valuation k (B i₀ j₀ - (1 : Matrix n n k) i₀ j₀)`. Use `Valuation.map_sum_le _ fun l _ => ?_` and prove the remaining obligations. Rewrite using `[map_mul]`. Conclude with `mul_le_mul' (hA i₀ l) (hm' l j₀)`.

Establish `hlt : valuation k t * valuation k (B i₀ j₀ - (1 : Matrix n n k) i₀ j₀) < valuation k (B i₀ j₀ - (1 : Matrix n n k) i₀ j₀)` using `mul_lt_of_lt_one_left hM0 ht`. Establish `hle` using `Valuation.map_sub (valuation k) (-(A i₀ j₀ - (1 : Matrix n n k) i₀ j₀)) (∑ l, (A i₀ l - (1 : Matrix n n k) i₀ l) * (B l j₀ - (1 : Matrix n n k) l j₀))`. Rewrite `hle` using `[← key, Valuation.map_neg]`. Break down `le_max_iff.mp hle with h | h` into its components or cases. Conclude with `absurd ((h.trans (hA i₀ j₀))) (not_le.mpr hM)`.

Conclude with `absurd (h.trans hsum) (not_le.mpr hlt)`.
-/
theorem inv_congr {n : Type*} [Fintype n] [DecidableEq n] (A B : Matrix n n k)
    (hAB : A * B = 1) {t : k} (ht : valuation k t < 1)
    (hA : ∀ i j, valuation k (A i j - (1 : Matrix n n k) i j) ≤ valuation k t) :
    ∀ i j, valuation k (B i j - (1 : Matrix n n k) i j) ≤ valuation k t := by
  by_contra h
  push_neg at h
  obtain ⟨i₁, j₁, h₁⟩ := h
  haveI : Nonempty (n × n) := ⟨(i₁, j₁)⟩
  obtain ⟨⟨i₀, j₀⟩, hm⟩ := Finite.exists_max
    (fun p : n × n => valuation k (B p.1 p.2 - (1 : Matrix n n k) p.1 p.2))
  have hm' : ∀ l j, valuation k (B l j - (1 : Matrix n n k) l j) ≤
      valuation k (B i₀ j₀ - (1 : Matrix n n k) i₀ j₀) := fun l j => hm (l, j)
  have hM : valuation k t < valuation k (B i₀ j₀ - (1 : Matrix n n k) i₀ j₀) :=
    h₁.trans_le (hm' i₁ j₁)
  have hM0 : 0 < valuation k (B i₀ j₀ - (1 : Matrix n n k) i₀ j₀) :=
    lt_of_le_of_lt zero_le' hM
  have hmat : (A - 1) * (B - 1) = -(A - 1) - (B - 1) := by
    simp only [sub_mul, mul_sub, hAB, one_mul, mul_one]
    abel
  have key : B i₀ j₀ - (1 : Matrix n n k) i₀ j₀ = -(A i₀ j₀ - (1 : Matrix n n k) i₀ j₀) -
      ∑ l, (A i₀ l - (1 : Matrix n n k) i₀ l) * (B l j₀ - (1 : Matrix n n k) l j₀) := by
    have := congrFun (congrFun hmat i₀) j₀
    simp only [Matrix.mul_apply, Matrix.sub_apply, Matrix.neg_apply] at this
    rw [this]
    ring
  have hsum : valuation k (∑ l, (A i₀ l - (1 : Matrix n n k) i₀ l) *
      (B l j₀ - (1 : Matrix n n k) l j₀)) ≤
      valuation k t * valuation k (B i₀ j₀ - (1 : Matrix n n k) i₀ j₀) := by
    refine Valuation.map_sum_le _ fun l _ => ?_
    rw [map_mul]
    exact mul_le_mul' (hA i₀ l) (hm' l j₀)
  have hlt : valuation k t * valuation k (B i₀ j₀ - (1 : Matrix n n k) i₀ j₀) <
      valuation k (B i₀ j₀ - (1 : Matrix n n k) i₀ j₀) :=
    mul_lt_of_lt_one_left hM0 ht
  have hle := Valuation.map_sub (valuation k) (-(A i₀ j₀ - (1 : Matrix n n k) i₀ j₀))
    (∑ l, (A i₀ l - (1 : Matrix n n k) i₀ l) * (B l j₀ - (1 : Matrix n n k) l j₀))
  rw [← key, Valuation.map_neg] at hle
  rcases le_max_iff.mp hle with h | h
  · exact absurd ((h.trans (hA i₀ j₀))) (not_le.mpr hM)
  · exact absurd (h.trans hsum) (not_le.mpr hlt)

variable [TopologicalSpace k] [IsNonarchimedeanLocalField k]

def congSet (n : Type*) [DecidableEq n] (t : k) : Set (Matrix n n k) :=
  {A | ∀ i j, valuation k (A i j - (1 : Matrix n n k) i j) ≤ valuation k t}

/- English proof (translation)
Establish `h : congSet n t = ⋂ i, ⋂ j, (fun A : Matrix n n k => A i j - (1 : Matrix n n k) i j) ⁻¹' GlobalTheory.SplitWeil.cball (Units.mk0 t ht)`. Use extensionality with `A`. Simplify using `[congSet, GlobalTheory.SplitWeil.cball]`. Rewrite using `[h]`. Use `isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j => ?_` and prove the remaining obligations.

Conclude with `(GlobalTheory.SplitWeil.isOpen_cball _).preimage ((continuous_id.matrix_elem i j).sub continuous_const)`.
-/
theorem isOpen_congSet (n : Type*) [Fintype n] [DecidableEq n] {t : k} (ht : t ≠ 0) :
    IsOpen (congSet n t) := by
  have h : congSet n t = ⋂ i, ⋂ j, (fun A : Matrix n n k => A i j - (1 : Matrix n n k) i j) ⁻¹'
      GlobalTheory.SplitWeil.cball (Units.mk0 t ht) := by
    ext A
    simp [congSet, GlobalTheory.SplitWeil.cball]
  rw [h]
  refine isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j => ?_
  exact (GlobalTheory.SplitWeil.isOpen_cball _).preimage
    ((continuous_id.matrix_elem i j).sub continuous_const)

/- English proof (translation)
Establish `h : congSet n t = Set.pi Set.univ fun i => Set.pi Set.univ fun j => (fun x : k => x + (1 : Matrix n n k) i j) '' GlobalTheory.SplitWeil.cball (Units.mk0 t ht)`. Use extensionality with `A`. Prove the components needed by the constructor for the conclusion. Introduce `hA i _ j _`. Conclude with `⟨A i j - (1 : Matrix n n k) i j, hA i j, by simp⟩`.

Introduce `hA i j`. Take `⟨x, hx, hxA⟩` from `hA i (Set.mem_univ _) j (Set.mem_univ _)`. Establish `hx' : A i j - (1 : Matrix n n k) i j = x`. Rewrite using `[← hxA]`. Simplify using the standard rewrite rules.

Rewrite using `[hx']`. Conclude with `hx`. Rewrite using `[h]`. Conclude with `isCompact_univ_pi fun i => isCompact_univ_pi fun j => (GlobalTheory.SplitWeil.isCompact_cball _).image (continuous_id.add continuous_const)`.
-/
theorem isCompact_congSet (n : Type*) [Fintype n] [DecidableEq n] {t : k} (ht : t ≠ 0) :
    IsCompact (congSet n t) := by
  have h : congSet n t = Set.pi Set.univ fun i => Set.pi Set.univ fun j =>
      (fun x : k => x + (1 : Matrix n n k) i j) '' GlobalTheory.SplitWeil.cball (Units.mk0 t ht) := by
    ext A
    constructor
    · intro hA i _ j _
      exact ⟨A i j - (1 : Matrix n n k) i j, hA i j, by simp⟩
    · intro hA i j
      obtain ⟨x, hx, hxA⟩ := hA i (Set.mem_univ _) j (Set.mem_univ _)
      have hx' : A i j - (1 : Matrix n n k) i j = x := by
        rw [← hxA]
        simp
      rw [hx']
      exact hx
  rw [h]
  exact isCompact_univ_pi fun i => isCompact_univ_pi fun j =>
    (GlobalTheory.SplitWeil.isCompact_cball _).image (continuous_id.add continuous_const)

def congGL (n : Type*) [Fintype n] [DecidableEq n] (t : k) : Set (GL n k) :=
  {g | (g : Matrix n n k) ∈ congSet n t}

/- English proof (translation)
The claim follows from `(isOpen_congSet n ht).preimage Units.continuous_val`.
-/
theorem isOpen_congGL (n : Type*) [Fintype n] [DecidableEq n] {t : k} (ht : t ≠ 0) :
    IsOpen (congGL n t) :=
  (isOpen_congSet n ht).preimage Units.continuous_val

/- English proof (translation)
Use `haveI := GlobalTheory.SplitWeil.t2Space k`. Rewrite using `[Units.isEmbedding_embedProduct.isCompact_iff]`. Establish `hc : IsCompact ((congSet n t ×ˢ (MulOpposite.op '' congSet n t)) ∩ {p : Matrix n n k × (Matrix n n k)ᵐᵒᵖ | p.1 * p.2.unop = 1 ∧ p.2.unop * p.1 = 1})`. Use `((isCompact_congSet n ht).prod ((isCompact_congSet n ht).image MulOpposite.continuous_op)).inter_right ?_` and prove the remaining obligations. Establish `hu : Continuous fun p : Matrix n n k × (Matrix n n k)ᵐᵒᵖ => p.2.unop` using `MulOpposite.continuous_unop.comp continuous_snd`.

Conclude with `(isClosed_eq (continuous_fst.matrix_mul hu) continuous_const).inter (isClosed_eq (hu.matrix_mul continuous_fst) continuous_const)`. Use `hc using 1` and compare the differences between its conclusion and the goal. Use extensionality with `⟨A, B⟩`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨g, hg, hgp⟩`.

Simplify using `only [Units.embedProduct_apply, Prod.mk.injEq] at hgp`. Take `⟨rfl, rfl⟩` from `hgp`. Use `⟨⟨hg, _, inv_congr (g : Matrix n n k) _ g.mul_inv ht1 hg, rfl⟩, ?_⟩` and prove the remaining obligations. Conclude with `⟨g.mul_inv, g.inv_mul⟩`. Introduce and unpack `⟨⟨hA, -⟩, h₁, h₂⟩`.

Use `⟨⟨A, B.unop, h₁, h₂⟩, hA, ?_⟩` and prove the remaining obligations. Simplify using `[Units.embedProduct_apply]`.
-/
theorem isCompact_congGL (n : Type*) [Fintype n] [DecidableEq n] {t : k} (ht : t ≠ 0)
    (ht1 : valuation k t < 1) : IsCompact (congGL n t) := by
  haveI := GlobalTheory.SplitWeil.t2Space k
  rw [Units.isEmbedding_embedProduct.isCompact_iff]
  have hc : IsCompact ((congSet n t ×ˢ (MulOpposite.op '' congSet n t)) ∩
      {p : Matrix n n k × (Matrix n n k)ᵐᵒᵖ |
        p.1 * p.2.unop = 1 ∧ p.2.unop * p.1 = 1}) := by
    refine ((isCompact_congSet n ht).prod
      ((isCompact_congSet n ht).image MulOpposite.continuous_op)).inter_right ?_
    have hu : Continuous fun p : Matrix n n k × (Matrix n n k)ᵐᵒᵖ => p.2.unop :=
      MulOpposite.continuous_unop.comp continuous_snd
    exact (isClosed_eq (continuous_fst.matrix_mul hu) continuous_const).inter
      (isClosed_eq (hu.matrix_mul continuous_fst) continuous_const)
  convert hc using 1
  ext ⟨A, B⟩
  constructor
  · rintro ⟨g, hg, hgp⟩
    simp only [Units.embedProduct_apply, Prod.mk.injEq] at hgp
    obtain ⟨rfl, rfl⟩ := hgp
    refine ⟨⟨hg, _, inv_congr (g : Matrix n n k) _ g.mul_inv ht1 hg, rfl⟩, ?_⟩
    exact ⟨g.mul_inv, g.inv_mul⟩
  · rintro ⟨⟨hA, -⟩, h₁, h₂⟩
    refine ⟨⟨A, B.unop, h₁, h₂⟩, hA, ?_⟩
    simp [Units.embedProduct_apply]

/- English proof (translation)
Introduce `_ _ _ _ _ N _ ht ht1` and use `⟨isOpen_congGL (Fin N) ht, isCompact_congGL (Fin N) ht ht1⟩`.
-/
theorem isOpen_isCompact_principal : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (N : ℕ) (t : k), t ≠ 0 → ValuativeRel.valuation k (t) < 1 →
    IsOpen {g : GL (Fin N) k | ∀ i j, ValuativeRel.valuation k
      ((g : Matrix (Fin N) (Fin N) k) i j - (1 : Matrix (Fin N) (Fin N) k) i j) ≤
        ValuativeRel.valuation k (t)} ∧
    IsCompact {g : GL (Fin N) k | ∀ i j, ValuativeRel.valuation k
      ((g : Matrix (Fin N) (Fin N) k) i j - (1 : Matrix (Fin N) (Fin N) k) i j) ≤
        ValuativeRel.valuation k (t)} :=
  fun _ _ _ _ _ N _ ht ht1 => ⟨isOpen_congGL (Fin N) ht, isCompact_congGL (Fin N) ht ht1⟩

end GlobalTheory.CompanionTheory.PrincipalCongruence

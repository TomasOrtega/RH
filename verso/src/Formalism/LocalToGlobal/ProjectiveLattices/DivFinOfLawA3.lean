import Formalism.LocalToGlobal.ProjectiveLattices.CompHt

noncomputable section

namespace Formalism.L2.Pj

open AlgebraicGeometry CategoryTheory NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.T0

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l} [Fintype (Comp Xo c)]

section Fin

variable (d : Data c.F (Comp Xo c) (fun Z => Om Z) (WTZ E) (fun Z => AC Z))

def DivFin : Prop := ∀ (Z : Comp Xo c) (r : Om Z), r ≠ 0 → {v | d.admitted Z v ∧ v r ≠ 0}.Finite

def FrShFin (δ : ∀ Z : Comp Xo c, AddValuation (Om Z) (WithTop ℤ) → Ix Dw → ℤ) : Prop :=
  ∀ Z : Comp Xo c, {v | d.admitted Z v ∧ δ Z v ≠ 0}.Finite

/- English proof (translation)
Introduce `Z G f hf hf0`. Take `⟨a, rfl⟩` from `Submodule.mem_span_singleton.mp hf`. Establish `ha : a ≠ 0`. Introduce and unpack `rfl`. Conclude with `hf0 (zero_smul _ _)`.

Establish `hcoeff : (a • (AddMonoidAlgebra.single G (1 : Om Z))).coeff G = a` using `by first`. Consider the case `simp`. Consider the case `simp [AddMonoidAlgebra.smul_single']`. Consider the case `(rw [AddMonoidAlgebra.smul_single', mul_one]; rfl)`. Use `((hD Z a ha).union (hF Z)).subset ?_` and prove the remaining obligations.

Introduce and unpack `v ⟨hadm, hne⟩`. Rewrite `hne` using `[hord]`. Unfold `ordC at hne`. Rewrite `hne` using `[hcoeff]`. Distinguish the cases in `hv : v a = 0`.

Use `Or.inr ⟨hadm, fun hδ => hne ?_⟩` and prove the remaining obligations. Rewrite using `[hv, hδ]`. Establish `hz : frW (0 : Ix Dw → ℤ) G = 0`. Unfold `frW`. Simplify using the standard rewrite rules.

Rewrite using `[hz]`. Both sides reduce to the same expression. Conclude with `Or.inl ⟨hadm, hv⟩`.
-/
theorem lawA3'_of (δ : ∀ Z : Comp Xo c, AddValuation (Om Z) (WithTop ℤ) → Ix Dw → ℤ)
    (hord : ∀ Z v, d.ord Z v = ordC (δ Z v) v) (hD : DivFin d) (hF : FrShFin d δ) : LawA3' d := by
  intro Z G f hf hf0
  obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hf
  have ha : a ≠ 0 := by
    rintro rfl
    exact hf0 (zero_smul _ _)
  have hcoeff : (a • (AddMonoidAlgebra.single G (1 : Om Z))).coeff G = a := by
    first
      | simp
      | simp [AddMonoidAlgebra.smul_single']
      | (rw [AddMonoidAlgebra.smul_single', mul_one]; rfl)
  refine ((hD Z a ha).union (hF Z)).subset ?_
  rintro v ⟨hadm, hne⟩
  rw [hord] at hne
  unfold ordC at hne
  rw [hcoeff] at hne
  by_cases hv : v a = 0
  · refine Or.inr ⟨hadm, fun hδ => hne ?_⟩
    rw [hv, hδ]
    have hz : frW (0 : Ix Dw → ℤ) G = 0 := by
      unfold frW
      simp
    rw [hz]
    rfl
  · exact Or.inl ⟨hadm, hv⟩

/- English proof (translation)
Introduce `Z r hr`. Establish `hmem : AddMonoidAlgebra.single (0 : WTZ E) r ∈ AG Z 0`. Use `Submodule.mem_span_singleton.mpr ⟨r, ?_⟩` and prove the remaining obligations. Use `first`. Consider the case `simp [AddMonoidAlgebra.smul_single']`.

Consider the case `(rw [AddMonoidAlgebra.smul_single', mul_one])`. Establish `hne0 : AddMonoidAlgebra.single (0 : WTZ E) r ≠ 0` using `by first`. Consider the case `simpa using hr`. Consider the case `exact Finsupp.single_ne_zero.mpr hr`. Use `(h Z hmem hne0).subset ?_` and prove the remaining obligations.

Introduce and unpack `v ⟨hadm, hv⟩`. Use `⟨hadm, ?_⟩` and prove the remaining obligations. Rewrite using `[hord]`. Unfold `ordC`. Establish `hc : (AddMonoidAlgebra.single (0 : WTZ E) r).coeff 0 = r` using `by first`.

Consider the case `simp`. Consider the case `rfl`. Establish `hf0 : frW (δ Z v) (0 : WTZ E) = 0`. Unfold `frW`. Use `Finset.sum_eq_zero (fun i _ => ?_)` and prove the remaining obligations.

Apply the tactic sequence `cases i <;> simp [exZ]`. Rewrite using `[hc, hf0, add_zero]`. Take `⟨n, hn⟩` from `WithTop.ne_top_iff_exists.mp ((AddValuation.top_iff v).not.mpr hr)`. Rewrite using `[← hn, WithTop.untopD_coe]`. Introduce and unpack `rfl`.

Conclude with `hv (by rw [← hn]; rfl)`.
-/
theorem divFin_of_lawA3' (δ : ∀ Z : Comp Xo c, AddValuation (Om Z) (WithTop ℤ) → Ix Dw → ℤ)
    (hord : ∀ Z v, d.ord Z v = ordC (δ Z v) v) (h : LawA3' d) : DivFin d := by
  intro Z r hr
  have hmem : AddMonoidAlgebra.single (0 : WTZ E) r ∈ AG Z 0 := by
    refine Submodule.mem_span_singleton.mpr ⟨r, ?_⟩
    first
      | simp [AddMonoidAlgebra.smul_single']
      | (rw [AddMonoidAlgebra.smul_single', mul_one])
  have hne0 : AddMonoidAlgebra.single (0 : WTZ E) r ≠ 0 := by
    first
      | simpa using hr
      | exact Finsupp.single_ne_zero.mpr hr
  refine (h Z hmem hne0).subset ?_
  rintro v ⟨hadm, hv⟩
  refine ⟨hadm, ?_⟩
  rw [hord]
  unfold ordC
  have hc : (AddMonoidAlgebra.single (0 : WTZ E) r).coeff 0 = r := by
    first
      | simp
      | rfl
  have hf0 : frW (δ Z v) (0 : WTZ E) = 0 := by
    unfold frW
    refine Finset.sum_eq_zero (fun i _ => ?_)
    cases i <;> simp [exZ]
  rw [hc, hf0, add_zero]
  obtain ⟨n, hn⟩ := WithTop.ne_top_iff_exists.mp ((AddValuation.top_iff v).not.mpr hr)
  rw [← hn, WithTop.untopD_coe]
  rintro rfl
  exact hv (by rw [← hn]; rfl)

end Fin

section Data

variable (h : GenFrEx Xo c)
    (δ : ∀ Z : Comp Xo c, AddValuation (Om Z) (WithTop ℤ) → Ix Dw → ℤ)
    (fn : ∀ σ : c.F →+* ℂ, FrPt Xo c (CAt σ) → Ix Dw → ℝ)
    (yP : ∀ Z : Comp Xo c, ∀ P : Om Z →+* ℂ, FrPt Xo c (CAt (sgOf P)))
    (Dd N T i g0 : ℕ) (cc : ℝ) (uL uF uka ude uet uta1 uta2 : WtR E)
    (wR : Fin (N + 1) → Rul Xo c) (jc : Comp Xo c → Fin (N + 1))
    (np : ℕ) (thpR : Fin np → Rul Xo c) (n0 : ℕ) (th0R : Fin n0 → Rul Xo c) (uF0 : WtR E)
    (nk : ℕ) (thkR : Fin nk → Rul Xo c) (MR : Set (Rul Xo c)) (etR ta1R ta2R : Rul Xo c)
    (nu : IsDedekindDomain.HeightOneSpectrum (𝓞 c.F) → ℝ)
    (ip : (c.F →+* ℂ) → (∀ Z : Comp Xo c, AC Z) → (∀ Z : Comp Xo c, AC Z) → ℂ)
    (wsize : WTZ E → ℝ) (DF PN PQ tableDegreeThreeBase PP0' Pd Gc PI4 Pet tableLineDegreeFive tableLineDegreeTwo Prw PO f r : ℝ)

/- English proof (translation)
The claim follows from `lawA3'_of _ δ (fun _ _ => rfl) hD hF`.
-/
theorem lawA3'_dataOf
    (hD : DivFin (dataOf h δ fn yP Dd N T i g0 cc uL uF uka ude uet uta1 uta2 wR jc np thpR n0 th0R uF0 nk thkR MR
      etR ta1R ta2R nu ip wsize DF PN PQ tableDegreeThreeBase PP0' Pd Gc PI4 Pet tableLineDegreeFive tableLineDegreeTwo Prw PO f r))
    (hF : FrShFin (dataOf h δ fn yP Dd N T i g0 cc uL uF uka ude uet uta1 uta2 wR jc np thpR n0 th0R uF0 nk thkR MR
      etR ta1R ta2R nu ip wsize DF PN PQ tableDegreeThreeBase PP0' Pd Gc PI4 Pet tableLineDegreeFive tableLineDegreeTwo Prw PO f r) δ) :
    LawA3' (dataOf h δ fn yP Dd N T i g0 cc uL uF uka ude uet uta1 uta2 wR jc np thpR n0 th0R uF0 nk thkR MR
      etR ta1R ta2R nu ip wsize DF PN PQ tableDegreeThreeBase PP0' Pd Gc PI4 Pet tableLineDegreeFive tableLineDegreeTwo Prw PO f r) :=
  lawA3'_of _ δ (fun _ _ => rfl) hD hF

end Data

end Formalism.L2.Pj

import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.NormOneAtOne
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AdelicPointComponentsAtPlacesLatticesVacua
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FractionalIdealCompletionLocallyPrincipal
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SelfDualLatticeRationalLineTraceFractionalIdealStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.Core.Mi
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (latV Moves MonoAt OrthAt PrimAt idAt intAt grpAt colMul Lat SplitPt GoodBF GluedCore IsSumFrame)
open GlobalTheory.SeeSaw (idV dI FI)
open ValuativeRel
open GlobalTheory.Core.Mi.LatMatch

noncomputable section

namespace GlobalTheory.Core.Mi.LatMatch.FlagDown

variable {D : D7}

/- English proof (translation)
Introduce `h`. Establish `h1` using `congrFun (congrFun d.e'e j) j`. Rewrite `h1` using `[Matrix.mul_apply, Matrix.one_apply_eq]`. Establish `: ∀ k, d.e k j = 0` using `fun k => congrFun h k`. Simplify using `[this] at h1`.
-/
theorem col_ne_zero {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) (j : Fin ρ) : (fun k => d.e k j) ≠ 0 := by
  intro h
  have h1 := congrFun (congrFun d.e'e j) j
  rw [Matrix.mul_apply, Matrix.one_apply_eq] at h1
  have : ∀ k, d.e k j = 0 := fun k => congrFun h k
  simp [this] at h1

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem colMul_eq {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) (j : Fin ρ) (a : AE D) :
    colMul d.jX j a = a • ratV (fun k => d.e k j) := rfl

/- English proof (translation)
Choose the witnesses or unpack the hypotheses as in `⟨k, hk⟩ : ∃ k, d.e k j ≠ 0 := by`. Assume the negation of the conclusion as `hc`. Use `push_neg at hc`. Conclude with `col_ne_zero d j (funext hc)`. Establish `h1 : a * incA D (d.e k j) ∈ idAt D P` using `GlobalTheory.FinPlLoc.latV_idAt h k`.

Establish `h2` using `(idAt D P).mul_mem_right (incA D (d.e k j)⁻¹) h1`. Rewrite `h2` using `[mul_assoc, ← map_mul, mul_inv_cancel₀ hk, map_one, mul_one]`. Then use the resulting hypothesis.
-/
theorem mem_idAt_of_colMul {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) (j : Fin ρ) {L : Lat S}
    {P : GlobalTheory.FinPl.Pl D → Prop} {a : AE D} (h : colMul d.jX j a ∈ latV S L P) : a ∈ idAt D P := by
  obtain ⟨k, hk⟩ : ∃ k, d.e k j ≠ 0 := by
    by_contra hc
    push_neg at hc
    exact col_ne_zero d j (funext hc)
  have h1 : a * incA D (d.e k j) ∈ idAt D P := GlobalTheory.FinPlLoc.latV_idAt h k
  have h2 := (idAt D P).mul_mem_right (incA D (d.e k j)⁻¹) h1
  rwa [mul_assoc, ← map_mul, mul_inv_cancel₀ hk, map_one, mul_one] at h2

/- English proof (translation)
Take `⟨𝔞, h𝔞, -, hv⟩` from `GlobalTheory.T.selfDualLattice_rationalLineTrace_fractionalIdeal D S L _ hL (col_ne_zero d j)`. Take `⟨x, hx, hx'⟩` from `GlobalTheory.IdVGen.idV_gen D v 𝔞 h𝔞`. Use `⟨x, hx, fun a ha => ?_⟩` and prove the remaining obligations. Rewrite using `[colMul_eq, hv v a ha, hx']`. Conclude with `⟨fun h => h.1, fun h => ⟨h, ha⟩⟩`.
-/
theorem line_gen {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) (j : Fin ρ) (L : Lat S) (hL : IsSelfDualC S L)
    (v : GlobalTheory.FinPl.Pl D) : ∃ x : D.host.E, x ≠ 0 ∧ ∀ a ∈ idAt D (· = v),
      (colMul d.jX j a ∈ latV S L (· = v) ↔ incA D x⁻¹ * a ∈ intAt D (· = v)) := by
  obtain ⟨𝔞, h𝔞, -, hv⟩ := GlobalTheory.T.selfDualLattice_rationalLineTrace_fractionalIdeal D S L _ hL (col_ne_zero d j)
  obtain ⟨x, hx, hx'⟩ := GlobalTheory.IdVGen.idV_gen D v 𝔞 h𝔞
  refine ⟨x, hx, fun a ha => ?_⟩
  rw [colMul_eq, hv v a ha, hx']
  exact ⟨fun h => h.1, fun h => ⟨h, ha⟩⟩

/- English proof (translation)
Take `⟨ε, -, -, hε, hεid, -⟩` from `GlobalTheory.FinPlLoc.part_idem (D := D) (· = v)`. Introduce `t ht`. Establish `hs : incA D x⁻¹ * t ∈ idAt D (· = v)` using `(idAt D _).mul_mem_left _ ht`. Establish `ha0 : incA D x * ε ∈ idAt D (· = v)` using `(idAt D _).mul_mem_left _ hε.1`. Establish `ha0' : incA D x⁻¹ * (incA D x * ε) ∈ intAt D (· = v)`.

Rewrite using `[← mul_assoc, ← map_mul, inv_mul_cancel₀ hx, map_one, one_mul]` and apply the resulting hypothesis. Establish `key : incA D x⁻¹ * t * (incA D x * ε) = t`. Combine the equalities or inequalities in the displayed calculation. Use `_ = t := by rw [← map_mul, inv_mul_cancel₀ hx, map_one, one_mul]; exact (hεid t).1 ht`. Establish `red : ∀ R : AE D → Prop, (∀ o ∈ intAt D (· = v), ∀ t, R t → R (o * t)) → R t → ∀ a ∈ idAt D (· = v), incA D x⁻¹ * a ∈ intAt D (· = v) → R (incA D x⁻¹ * t * a)`.

Introduce `R hR hRt a _ ha`. Use `hR _ ha t hRt` as an intermediate fact. Rewrite `this` using `[show incA D x⁻¹ * a * t = incA D x⁻¹ * t * a by ring]`. Then use the resulting hypothesis. Prove the components needed by the constructor for the conclusion. Introduce `hPt`.

Use `(h _ hs).1 (red P hP hPt) _ ha0 ha0'` as an intermediate fact. Rewrite `this` using `[key]`. Then use the resulting hypothesis. Introduce `hQt`. Use `(h _ hs).2 (red Q hQ hQt) _ ha0 ha0'` as an intermediate fact. Rewrite `this` using `[key]`. Then use the resulting hypothesis.
-/
theorem cancel {v : GlobalTheory.FinPl.Pl D} (x : D.host.E) (hx : x ≠ 0) (P Q : AE D → Prop)
    (hP : ∀ o ∈ intAt D (· = v), ∀ t, P t → P (o * t)) (hQ : ∀ o ∈ intAt D (· = v), ∀ t, Q t → Q (o * t))
    (h : ∀ s ∈ idAt D (· = v),
      (∀ a ∈ idAt D (· = v), incA D x⁻¹ * a ∈ intAt D (· = v) → P (s * a)) ↔
        (∀ a ∈ idAt D (· = v), incA D x⁻¹ * a ∈ intAt D (· = v) → Q (s * a))) :
    ∀ t ∈ idAt D (· = v), P t ↔ Q t := by
  obtain ⟨ε, -, -, hε, hεid, -⟩ := GlobalTheory.FinPlLoc.part_idem (D := D) (· = v)
  intro t ht
  have hs : incA D x⁻¹ * t ∈ idAt D (· = v) := (idAt D _).mul_mem_left _ ht
  have ha0 : incA D x * ε ∈ idAt D (· = v) := (idAt D _).mul_mem_left _ hε.1
  have ha0' : incA D x⁻¹ * (incA D x * ε) ∈ intAt D (· = v) := by
    rwa [← mul_assoc, ← map_mul, inv_mul_cancel₀ hx, map_one, one_mul]
  have key : incA D x⁻¹ * t * (incA D x * ε) = t := by
    calc _ = (incA D x⁻¹ * incA D x) * (ε * t) := by ring
    _ = t := by rw [← map_mul, inv_mul_cancel₀ hx, map_one, one_mul]; exact (hεid t).1 ht
  have red : ∀ R : AE D → Prop, (∀ o ∈ intAt D (· = v), ∀ t, R t → R (o * t)) → R t →
      ∀ a ∈ idAt D (· = v), incA D x⁻¹ * a ∈ intAt D (· = v) → R (incA D x⁻¹ * t * a) := by
    intro R hR hRt a _ ha
    have := hR _ ha t hRt
    rwa [show incA D x⁻¹ * a * t = incA D x⁻¹ * t * a by ring] at this
  constructor
  · intro hPt
    have := (h _ hs).1 (red P hP hPt) _ ha0 ha0'
    rwa [key] at this
  · intro hQt
    have := (h _ hs).2 (red Q hQ hQt) _ ha0 ha0'
    rwa [key] at this

end GlobalTheory.Core.Mi.LatMatch.FlagDown

open GlobalTheory.Core.Mi.LatMatch.FlagDown in

/- English proof (translation)
Introduce `D ψ S S₀ ρ d L L' v c hsd hP hP' hc i j hij hj`. Take `⟨x, hx, hA⟩` from `line_gen d j L hsd v`. Use `cancel x hx (fun t => colMul d.jX i t ∈ latV S L (· = v)) (fun t => colMul d.jX i (c * t) ∈ latV S L' (· = v)) ?_ ?_ ?_` and prove the remaining obligations. Introduce `o ho t ht`. Establish `e : colMul d.jX i (o * t) = o • colMul d.jX i t`.

Use function extensionality and compare the values at `k`. Simplify using `only [colMul, Pi.smul_apply, smul_eq_mul]`. Expand and normalize the polynomial expressions, which then agree. Use `show colMul d.jX i (o * t) ∈ latV S L (· = v)`. Rewrite using `[e]`.

Conclude with `GlobalTheory.FinPlLoc.smul_latV v ho ht`. Introduce `o ho t ht`. Establish `e : colMul d.jX i (c * (o * t)) = o • colMul d.jX i (c * t)`. Use function extensionality and compare the values at `k`. Simplify using `only [colMul, Pi.smul_apply, smul_eq_mul]`.

Expand and normalize the polynomial expressions, which then agree. Use `show colMul d.jX i (c * (o * t)) ∈ latV S L' (· = v)`. Rewrite using `[e]`. Conclude with `GlobalTheory.FinPlLoc.smul_latV v ho ht`. Introduce `s hs`.

Establish `e1` using `hP i j hij s hs`. Establish `e2` using `hP' i j hij s hs`. Establish `l1 : (∀ a ∈ idAt D (· = v), incA D x⁻¹ * a ∈ intAt D (· = v) → colMul d.jX i (s * a) ∈ latV S L (· = v)) ↔ (∀ a : AE D, colMul d.jX j a ∈ latV S L (· = v) → colMul d.jX i (s * a) ∈ latV S L (· = v))`. Prove the components needed by the constructor for the conclusion. Introduce `H a ha`.

Establish `hid` using `mem_idAt_of_colMul d j ha`. Conclude with `H a hid ((hA a hid).1 ha)`. Introduce `H a ha hx'`. Conclude with `H a ((hA a ha).2 hx')`. Establish `l2 : (∀ a ∈ idAt D (· = v), incA D x⁻¹ * a ∈ intAt D (· = v) → colMul d.jX i (c * (s * a)) ∈ latV S L' (· = v)) ↔ (∀ a' : AE D, colMul d.jX j a' ∈ latV S L' (· = v) → colMul d.jX i (s * a') ∈ latV S L' (· = v))`.

Prove the components needed by the constructor for the conclusion. Introduce `H a' ha'`. Establish `ha'id` using `mem_idAt_of_colMul d j ha'`. Establish `hb : cA D c * a' ∈ idAt D (· = v)` using `(idAt D _).mul_mem_left _ ha'id`. Establish `hcb : c * (cA D c * a') = a'` using `by rw [← mul_assoc, hc.1, one_mul]`.

Establish `hj'` using `(hj _ hb).2 (by rw [hcb]; exact ha')`. Use `H _ hb ((hA _ hb).1 hj')` as an intermediate fact. Rewrite `this` using `[show c * (s * (cA D c * a')) = s * (c * (cA D c * a')) by ring, hcb]`. Then use the resulting hypothesis. Introduce `H a ha hx'`. Establish `hj'` using `(hj a ha).1 ((hA a ha).2 hx')`.

Use `H _ hj'` as an intermediate fact. Rewrite `this` using `[show s * (c * a) = c * (s * a) by ring]`. Then use the resulting hypothesis. Conclude with `l1.trans (e1.trans e2.symm) |>.trans l2.symm`.
-/
theorem GlobalTheory.Core.Mi.LatMatch.match_down_flag : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S S₀ : HSp D) (ρ : ℕ) (d : HypDec S S₀ ρ) (L L' : Lat S) (v : GlobalTheory.FinPl.Pl D) (c : AE D), IsSelfDualC S L → PrimAt ψ d L v → PrimAt ψ d L' v → NormOneAt v c → ∀ i j : Fin ρ, j.1 = i.1 + 1 → (∀ a ∈ idAt D (· = v), (colMul d.jX j a ∈ latV S L (· = v) ↔ colMul d.jX j (c * a) ∈ latV S L' (· = v))) → ∀ a ∈ idAt D (· = v), (colMul d.jX i a ∈ latV S L (· = v) ↔ colMul d.jX i (c * a) ∈ latV S L' (· = v)) := by
  intro D ψ S S₀ ρ d L L' v c hsd hP hP' hc i j hij hj
  obtain ⟨x, hx, hA⟩ := line_gen d j L hsd v
  refine cancel x hx (fun t => colMul d.jX i t ∈ latV S L (· = v))
    (fun t => colMul d.jX i (c * t) ∈ latV S L' (· = v)) ?_ ?_ ?_
  · intro o ho t ht
    have e : colMul d.jX i (o * t) = o • colMul d.jX i t := by
      funext k; simp only [colMul, Pi.smul_apply, smul_eq_mul]; ring
    show colMul d.jX i (o * t) ∈ latV S L (· = v)
    rw [e]; exact GlobalTheory.FinPlLoc.smul_latV v ho ht
  · intro o ho t ht
    have e : colMul d.jX i (c * (o * t)) = o • colMul d.jX i (c * t) := by
      funext k; simp only [colMul, Pi.smul_apply, smul_eq_mul]; ring
    show colMul d.jX i (c * (o * t)) ∈ latV S L' (· = v)
    rw [e]; exact GlobalTheory.FinPlLoc.smul_latV v ho ht
  · intro s hs
    have e1 := hP i j hij s hs
    have e2 := hP' i j hij s hs
    have l1 : (∀ a ∈ idAt D (· = v), incA D x⁻¹ * a ∈ intAt D (· = v) → colMul d.jX i (s * a) ∈ latV S L (· = v)) ↔
        (∀ a : AE D, colMul d.jX j a ∈ latV S L (· = v) → colMul d.jX i (s * a) ∈ latV S L (· = v)) := by
      constructor
      · intro H a ha
        have hid := mem_idAt_of_colMul d j ha
        exact H a hid ((hA a hid).1 ha)
      · intro H a ha hx'
        exact H a ((hA a ha).2 hx')
    have l2 : (∀ a ∈ idAt D (· = v), incA D x⁻¹ * a ∈ intAt D (· = v) →
        colMul d.jX i (c * (s * a)) ∈ latV S L' (· = v)) ↔
        (∀ a' : AE D, colMul d.jX j a' ∈ latV S L' (· = v) → colMul d.jX i (s * a') ∈ latV S L' (· = v)) := by
      constructor
      · intro H a' ha'
        have ha'id := mem_idAt_of_colMul d j ha'
        have hb : cA D c * a' ∈ idAt D (· = v) := (idAt D _).mul_mem_left _ ha'id
        have hcb : c * (cA D c * a') = a' := by rw [← mul_assoc, hc.1, one_mul]
        have hj' := (hj _ hb).2 (by rw [hcb]; exact ha')
        have := H _ hb ((hA _ hb).1 hj')
        rwa [show c * (s * (cA D c * a')) = s * (c * (cA D c * a')) by ring, hcb] at this
      · intro H a ha hx'
        have hj' := (hj a ha).1 ((hA a ha).2 hx')
        have := H _ hj'
        rwa [show s * (c * a) = c * (s * a) by ring] at this
    exact l1.trans (e1.trans e2.symm) |>.trans l2.symm

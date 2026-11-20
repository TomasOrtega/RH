import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TotalEqOfNonneg
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EqOfIsometricTrivShift
import Development.AbelianVarietyTheory.Definitions.Divisors.DiagValExtTraceNonneg
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.QuotStages

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CxPts GlobalTheory.VB GlobalTheory.HermFrame GlobalTheory.CurveDens GlobalTheory.Cartier
open GlobalTheory.Twist (resM app_resM)
open GlobalTheory.VBExt (AdaptedChart)
open scoped ComplexOrder

namespace GlobalTheory.MetStage

/- English proof (translation)
Use extensionality with `a b`. Conclude with `h.form_frame c hc _ _`.
-/
theorem gram_chart {k : Type} [CommRing k] {X : Scheme.{0}} {p : X ⟶ Sp k} {σ : k →+* ℂ}
    {E : X.Modules} {r : ℕ} (h : Met p σ E r) (c : Chart E r) {y : CxPts p σ}
    (hc : y ∈ ptsIn p σ c.U) {ι : Type} (φ : ι → Fin r) :
    h.gram (fun a => c.e (φ a)) y = (h.G c y).submatrix φ φ := by
  ext a b; exact h.form_frame c hc _ _

/- English proof (translation)
Introduce `k _ X p σ A M B L Q V f g u q₀ q₁ q₂ w₀ w₁ w₂ hS₀ hS₁ hS₂ l m w₃ hS₃ n hA hM hL hQ hV hg h hfg hsq hm hl`. Establish `key : ∀ y : CxPts p σ, ∃ (U : X.Opens) (e : Fin n → Γ(A, U)) (t : Fin 1 → Γ(M, U)) (t₁ : Fin 1 → Γ(B, U)), y ∈ ptsIn p σ U ∧ IsFrame e ∧ IsFrame (fun k => q₀.app U (t k)) ∧ IsFrame (fun k => q₁.app U (t₁ k))`. Introduce `y`. Take `⟨a, ha⟩` from `Met.exists_adapted hS₀ hA hL y`. Take `⟨b, hb⟩` from `Met.exists_adapted hS₁ hM hQ y`.

Use `⟨a.U ⊓ b.U, fun i => resM A inf_le_left (a.e i), fun i => resM M inf_le_left (a.t i), fun i => resM B inf_le_right (b.t i), mem_ptsIn_inf.2 ⟨ha, hb⟩, a.he.res inf_le_left, ?_, ?_⟩` and prove the remaining obligations. Simplify using `only [app_resM]`. Conclude with `a.ht.res inf_le_left`. Simplify using `only [app_resM]`. Conclude with `b.ht.res inf_le_right`.

Establish `QS` using `GlobalTheory.QuotStage.quotStages`. Use `⟨Met.ext_of_exists fun y => ?_, Met.ext_of_exists fun y => ?_⟩` and prove the remaining obligations. Use `all_goals`. Take `⟨U, e, t, t₁, hy, he, ht, ht₁⟩` from `key y`. Establish `hgf : ∀ i, g.app U (f.app U (e i)) = u.app U (e i)` using `fun i => congr(($(hfg)).app U (e i))`.

Establish `hsq' : ∀ x : Γ(M, U), l.app U (q₀.app U x) = q₂.app U (g.app U x)` using `fun x => congr(($(hsq)).app U x)`. Establish `hm' : ∀ x : Γ(B, U), m.app U (q₂.app U x) = q₁.app U x` using `fun x => congr(($(hm)).app U x)`. Set `a₀ : AdaptedChart (ShortComplex.mk f q₀ w₀) n 1` to `⟨U, e, t, he, ht⟩`. Set `a₃ : AdaptedChart (ShortComplex.mk l m w₃) 1 1` to `⟨U, fun i => q₀.app U (t i), fun i => q₂.app U (t₁ i), ht, by show IsFrame fun k => m.app U (q₂.app U (t₁ k))`. Simplify using `only [hm']`.

Conclude with `ht₁⟩`. Set `t₂ : Fin (1 + 1) → Γ(B, U)` to `Sum.elim (fun i => g.app U (t i)) t₁ ∘ finSumFinEquiv.symm`. Establish `ht₂ : (fun k => q₂.app U (t₂ k)) = a₃.frame ∘ finSumFinEquiv.symm`. Use function extensionality and compare the values at `j`. Use `show q₂.app U (Sum.elim (fun i => g.app U (t i)) t₁ (finSumFinEquiv.symm j)) = a₃.frame (finSumFinEquiv.symm j)`.

Break down `finSumFinEquiv.symm j with i | i` into its components or cases. Use `exacts [(hsq' _).symm, rfl]`. Set `a₂ : AdaptedChart (ShortComplex.mk u q₂ w₂) n (1 + 1)` to `⟨U, e, t₂, he, by show IsFrame fun k => q₂.app U (t₂ k)`. Rewrite using `[ht₂]`. Conclude with `(a₃.mid hS₃).isFrame⟩`.

Set `T : Fin n ⊕ (Fin 1 ⊕ Fin 1) → Γ(B, U)` to `Sum.elim (fun i => u.app U (e i)) (Sum.elim (fun i => g.app U (t i)) t₁)`. Establish `h₂T : a₂.frame = T ∘ Sum.map id finSumFinEquiv.symm`. Apply the tactic sequence `funext j; rcases j with i | i <;> rfl`. Establish `hK : (h.gram T y).PosDef`. Use `(Met.posDef_gram_frame h hS₂ a₂ hy).submatrix (Equiv.sumCongr (Equiv.refl (Fin n)) finSumFinEquiv).injective` as an intermediate fact.

Rewrite `this` using `[h₂T]`. Use `this using 1` and compare the differences between its conclusion and the goal. Use extensionality with `i j`. Apply the tactic sequence `rcases i with i | i <;> rcases j with j | j <;> simp [Met.gram]`. Establish `hQ₂ : (Met.quot (S` using `ShortComplex.mk u q₂ w₂) (r := n) (s := 1 + 1) h hS₂ hA hV).G a₂.quot y = (quotGram (h.gram T y)).submatrix finSumFinEquiv.symm finSumFinEquiv.symm := by`.

Rewrite using `[Met.quot_G h hS₂ hA hV a₂ hy, h₂T]`. Use `(QS (Fin n) (Fin 1 ⊕ Fin 1) (Fin 1)).2 (Fin n) (Fin (1 + 1)) (Equiv.refl _) finSumFinEquiv.symm (h.gram T y)` as an intermediate fact. Simplify using `only [Equiv.coe_refl] at this`. Conclude with `this`. Establish `h₃ : a₃.frame = fun j => a₂.quot.e (finSumFinEquiv j)`.

Use function extensionality and compare the values at `j`. Conclude with `((congrFun ht₂ (finSumFinEquiv j)).trans (congrArg a₃.frame (finSumFinEquiv.symm_apply_apply j))).symm`. Establish `hG₃ : (Met.quot (S` using `ShortComplex.mk u q₂ w₂) (r := n) (s := 1 + 1) h hS₂ hA hV).gram a₃.frame y = quotGram (h.gram T y) := by`. Rewrite using `[h₃]`. Use `(gram_chart _ a₂.quot hy finSumFinEquiv).trans ?_` and prove the remaining obligations.

Rewrite using `[hQ₂]`. Use extensionality with `i j`. Simplify using `only [submatrix_apply, Equiv.symm_apply_apply]`. Take `⟨e₁, e₂⟩` from `(QS (Fin n) (Fin 1) (Fin 1)).1 _ hK`. Use `⟨a₀.quot, hy, ?_⟩` and prove the remaining obligations.

Establish `hR : (h.restrict hg hM).gram a₀.frame y = (h.gram T y).submatrix (Sum.map id Sum.inl) (Sum.map id Sum.inl)`. Establish `hT : ∀ i, g.app U (a₀.frame i) = T (Sum.map id Sum.inl i)`. Introduce and unpack `(i | i)`. Use `exacts [hgf i, rfl]`. Use extensionality with `i j`.

Conclude with `(h.form_restrict hg hM _ _ hy).trans (congrArg₂ (h.form · · y) (hT i) (hT j))`. Rewrite using `[Met.quot_G (S := ShortComplex.mk f q₀ w₀) (h.restrict hg hM) hS₀ hA hL a₀ hy, hR, ← e₁, ← hG₃]`. Both sides reduce to the same expression. Set `a₁ : AdaptedChart (ShortComplex.mk g q₁ w₁) (n + 1) 1` to `⟨U, (a₀.mid hS₀).e, t₁, (a₀.mid hS₀).isFrame, ht₁⟩`. Establish `hc : a₃.quot = a₁.quot`.

Establish `: (fun i => m.app U (q₂.app U (t₁ i))) = fun i => q₁.app U (t₁ i)`. Use function extensionality and compare the values at `fun i => hm' _`. Conclude with `(Chart.mk.injEq ..).mpr ⟨rfl, heq_of_eq this⟩`. Establish `hR : h.gram a₁.frame y = ((h.gram T y).submatrix (Equiv.sumAssoc _ _ _) (Equiv.sumAssoc _ _ _)).submatrix (Sum.map finSumFinEquiv.symm id) (Sum.map finSumFinEquiv.symm id)`. Establish `hT : ∀ i, a₁.frame i = T (Equiv.sumAssoc _ _ _ (Sum.map finSumFinEquiv.symm id i))`.

Introduce and unpack `(i | i)`. Use `show g.app U (a₀.frame (finSumFinEquiv.symm i)) = T (Equiv.sumAssoc _ _ _ (Sum.inl (finSumFinEquiv.symm i)))`. Break down `finSumFinEquiv.symm i with i | i` into its components or cases. Use `exacts [hgf i, rfl]`. Both sides reduce to the same expression.

Use extensionality with `i j`. Conclude with `congrArg₂ (h.form · · y) (hT i) (hT j)`. Use `⟨a₁.quot, hy, ?_⟩` and prove the remaining obligations. Rewrite using `[Met.quot_G (S := ShortComplex.mk g q₁ w₁) h hS₁ hM hQ a₁ hy, hR, (QS (Fin n ⊕ Fin 1) (Fin 1) (Fin 1)).2, submatrix_id_id, ← e₂, ← hG₃, ← hc]`. Conclude with `Met.quot_G (S := ShortComplex.mk l m w₃) _ hS₃ hL hQ a₃ hy`.
-/
theorem metStages : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) (p : X ⟶ Sp k) (σ : k →+* ℂ) (A M B L Q V : X.Modules) (f : A ⟶ M) (g : M ⟶ B) (u : A ⟶ B) (q₀ : M ⟶ L) (q₁ : B ⟶ Q) (q₂ : B ⟶ V) (w₀ : f ≫ q₀ = 0) (w₁ : g ≫ q₁ = 0) (w₂ : u ≫ q₂ = 0) (hS₀ : (ShortComplex.mk f q₀ w₀).ShortExact) (hS₁ : (ShortComplex.mk g q₁ w₁).ShortExact) (hS₂ : (ShortComplex.mk u q₂ w₂).ShortExact) (l : L ⟶ V) (m : V ⟶ Q) (w₃ : l ≫ m = 0) (hS₃ : (ShortComplex.mk l m w₃).ShortExact) (n : ℕ) (hA : IsVB A n) (hM : IsVB M (n + 1)) (hL : IsVB L 1) (hQ : IsVB Q 1) (hV : IsVB V (1 + 1)) (hg : IsSubbundle g) (h : Met p σ B (n + 1 + 1)), f ≫ g = u → q₀ ≫ l = g ≫ q₂ → q₂ ≫ m = q₁ → ∀ hl : IsSubbundle l, (Met.quot (S := ShortComplex.mk u q₂ w₂) (r := n) (s := 1 + 1) h hS₂ hA hV).restrict hl hL = Met.quot (S := ShortComplex.mk f q₀ w₀) (h.restrict hg hM) hS₀ hA hL ∧ Met.quot (S := ShortComplex.mk l m w₃) (Met.quot (S := ShortComplex.mk u q₂ w₂) (r := n) (s := 1 + 1) h hS₂ hA hV) hS₃ hL hQ = Met.quot (S := ShortComplex.mk g q₁ w₁) h hS₁ hM hQ := by
  intro k _ X p σ A M B L Q V f g u q₀ q₁ q₂ w₀ w₁ w₂ hS₀ hS₁ hS₂ l m w₃ hS₃ n hA hM hL hQ hV hg h hfg hsq hm hl
  have key : ∀ y : CxPts p σ, ∃ (U : X.Opens) (e : Fin n → Γ(A, U)) (t : Fin 1 → Γ(M, U))
      (t₁ : Fin 1 → Γ(B, U)), y ∈ ptsIn p σ U ∧ IsFrame e ∧ IsFrame (fun k => q₀.app U (t k)) ∧
        IsFrame (fun k => q₁.app U (t₁ k)) := by
    intro y
    obtain ⟨a, ha⟩ := Met.exists_adapted hS₀ hA hL y
    obtain ⟨b, hb⟩ := Met.exists_adapted hS₁ hM hQ y
    refine ⟨a.U ⊓ b.U, fun i => resM A inf_le_left (a.e i), fun i => resM M inf_le_left (a.t i),
      fun i => resM B inf_le_right (b.t i), mem_ptsIn_inf.2 ⟨ha, hb⟩, a.he.res inf_le_left, ?_, ?_⟩
    · simp only [app_resM]; exact a.ht.res inf_le_left
    · simp only [app_resM]; exact b.ht.res inf_le_right
  have QS := GlobalTheory.QuotStage.quotStages
  refine ⟨Met.ext_of_exists fun y => ?_, Met.ext_of_exists fun y => ?_⟩
  all_goals
    obtain ⟨U, e, t, t₁, hy, he, ht, ht₁⟩ := key y
    have hgf : ∀ i, g.app U (f.app U (e i)) = u.app U (e i) := fun i => congr(($(hfg)).app U (e i))
    have hsq' : ∀ x : Γ(M, U), l.app U (q₀.app U x) = q₂.app U (g.app U x) :=
      fun x => congr(($(hsq)).app U x)
    have hm' : ∀ x : Γ(B, U), m.app U (q₂.app U x) = q₁.app U x := fun x => congr(($(hm)).app U x)
    let a₀ : AdaptedChart (ShortComplex.mk f q₀ w₀) n 1 := ⟨U, e, t, he, ht⟩
    let a₃ : AdaptedChart (ShortComplex.mk l m w₃) 1 1 := ⟨U, fun i => q₀.app U (t i),
      fun i => q₂.app U (t₁ i), ht, by
        show IsFrame fun k => m.app U (q₂.app U (t₁ k))
        simp only [hm']; exact ht₁⟩
    let t₂ : Fin (1 + 1) → Γ(B, U) := Sum.elim (fun i => g.app U (t i)) t₁ ∘ finSumFinEquiv.symm
    have ht₂ : (fun k => q₂.app U (t₂ k)) = a₃.frame ∘ finSumFinEquiv.symm := by
      funext j
      show q₂.app U (Sum.elim (fun i => g.app U (t i)) t₁ (finSumFinEquiv.symm j)) =
        a₃.frame (finSumFinEquiv.symm j)
      rcases finSumFinEquiv.symm j with i | i
      exacts [(hsq' _).symm, rfl]
    let a₂ : AdaptedChart (ShortComplex.mk u q₂ w₂) n (1 + 1) := ⟨U, e, t₂, he, by
        show IsFrame fun k => q₂.app U (t₂ k)
        rw [ht₂]; exact (a₃.mid hS₃).isFrame⟩
    let T : Fin n ⊕ (Fin 1 ⊕ Fin 1) → Γ(B, U) :=
      Sum.elim (fun i => u.app U (e i)) (Sum.elim (fun i => g.app U (t i)) t₁)
    have h₂T : a₂.frame = T ∘ Sum.map id finSumFinEquiv.symm := by
      funext j; rcases j with i | i <;> rfl
    have hK : (h.gram T y).PosDef := by
      have := (Met.posDef_gram_frame h hS₂ a₂ hy).submatrix
        (Equiv.sumCongr (Equiv.refl (Fin n)) finSumFinEquiv).injective
      rw [h₂T] at this
      convert this using 1
      ext i j
      rcases i with i | i <;> rcases j with j | j <;> simp [Met.gram]
    have hQ₂ : (Met.quot (S := ShortComplex.mk u q₂ w₂) (r := n) (s := 1 + 1) h hS₂ hA hV).G a₂.quot y =
        (quotGram (h.gram T y)).submatrix finSumFinEquiv.symm finSumFinEquiv.symm := by
      rw [Met.quot_G h hS₂ hA hV a₂ hy, h₂T]
      have := (QS (Fin n) (Fin 1 ⊕ Fin 1) (Fin 1)).2 (Fin n) (Fin (1 + 1)) (Equiv.refl _)
        finSumFinEquiv.symm (h.gram T y)
      simp only [Equiv.coe_refl] at this
      exact this
    have h₃ : a₃.frame = fun j => a₂.quot.e (finSumFinEquiv j) := by
      funext j
      exact ((congrFun ht₂ (finSumFinEquiv j)).trans
        (congrArg a₃.frame (finSumFinEquiv.symm_apply_apply j))).symm
    have hG₃ : (Met.quot (S := ShortComplex.mk u q₂ w₂) (r := n) (s := 1 + 1) h hS₂ hA hV).gram
        a₃.frame y = quotGram (h.gram T y) := by
      rw [h₃]
      refine (gram_chart _ a₂.quot hy finSumFinEquiv).trans ?_
      rw [hQ₂]
      ext i j
      simp only [submatrix_apply, Equiv.symm_apply_apply]
    obtain ⟨e₁, e₂⟩ := (QS (Fin n) (Fin 1) (Fin 1)).1 _ hK
  · refine ⟨a₀.quot, hy, ?_⟩
    have hR : (h.restrict hg hM).gram a₀.frame y =
        (h.gram T y).submatrix (Sum.map id Sum.inl) (Sum.map id Sum.inl) := by
      have hT : ∀ i, g.app U (a₀.frame i) = T (Sum.map id Sum.inl i) := by
        rintro (i | i)
        exacts [hgf i, rfl]
      ext i j
      exact (h.form_restrict hg hM _ _ hy).trans (congrArg₂ (h.form · · y) (hT i) (hT j))
    rw [Met.quot_G (S := ShortComplex.mk f q₀ w₀) (h.restrict hg hM) hS₀ hA hL a₀ hy, hR, ← e₁,
      ← hG₃]
    rfl
  · let a₁ : AdaptedChart (ShortComplex.mk g q₁ w₁) (n + 1) 1 :=
      ⟨U, (a₀.mid hS₀).e, t₁, (a₀.mid hS₀).isFrame, ht₁⟩
    have hc : a₃.quot = a₁.quot := by
      have : (fun i => m.app U (q₂.app U (t₁ i))) = fun i => q₁.app U (t₁ i) :=
        funext fun i => hm' _
      exact (Chart.mk.injEq ..).mpr ⟨rfl, heq_of_eq this⟩
    have hR : h.gram a₁.frame y = ((h.gram T y).submatrix (Equiv.sumAssoc _ _ _)
        (Equiv.sumAssoc _ _ _)).submatrix (Sum.map finSumFinEquiv.symm id)
        (Sum.map finSumFinEquiv.symm id) := by
      have hT : ∀ i, a₁.frame i = T (Equiv.sumAssoc _ _ _ (Sum.map finSumFinEquiv.symm id i)) := by
        rintro (i | i)
        · show g.app U (a₀.frame (finSumFinEquiv.symm i)) =
            T (Equiv.sumAssoc _ _ _ (Sum.inl (finSumFinEquiv.symm i)))
          rcases finSumFinEquiv.symm i with i | i
          exacts [hgf i, rfl]
        · rfl
      ext i j
      exact congrArg₂ (h.form · · y) (hT i) (hT j)
    refine ⟨a₁.quot, hy, ?_⟩
    rw [Met.quot_G (S := ShortComplex.mk g q₁ w₁) h hS₁ hM hQ a₁ hy, hR,
      (QS (Fin n ⊕ Fin 1) (Fin 1) (Fin 1)).2, submatrix_id_id, ← e₂, ← hG₃, ← hc]
    exact Met.quot_G (S := ShortComplex.mk l m w₃) _ hS₃ hL hQ a₃ hy

end GlobalTheory.MetStage

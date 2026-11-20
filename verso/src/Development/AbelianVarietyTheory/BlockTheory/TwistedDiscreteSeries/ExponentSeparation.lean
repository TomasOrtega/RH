import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsSubquotientDetRepParInd
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsCellOfIsSubquotient

noncomputable section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL ValuativeRel

namespace GlobalTheory.IndefiniteRowSideFullHecke.ExponentSeparationTwistedDiscreteSeries

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

def strictCone (ϖ : kˣ) (r : ℕ) : Set (Fin r → kˣ) :=
  {t | ∃ a : Fin r → ℤ, StrictAnti a ∧ t = fun i => ϖ ^ a i}

open Classical in

def IsExp {r : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin r) k) V)
    (E : Multiset ((Fin r → kˣ) →* ℂˣ)) : Prop :=
  ∀ χ, expMult π χ = (E.count χ : ℕ∞)

def charSum {r : ℕ} (E : Multiset ((Fin r → kˣ) →* ℂˣ)) (t : Fin r → kˣ) : ℂ :=
  (E.map fun χ => (χ t : ℂ)).sum

def ExponentsSeparate : Prop :=
  ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (ϖ : kˣ), valuation k (ϖ : k) = uniformizer k →
    ∀ (r n : ℕ) (V : Fin n → Type) [∀ i, AddCommGroup (V i)] [∀ i, Module ℂ (V i)]
      (π : ∀ i, Representation ℂ (GL (Fin r) k) (V i)),
      (∀ i, (π i).IsIrreducible) → (∀ i, IsAdmissible (π i)) →
      (∀ i j, i ≠ j → IsEmpty ((π i).Equiv (π j))) →
      (∀ i, fixed (π i) (iwahori k (Fin r)) ≠ ⊥) →
      ∀ (E : Fin n → Multiset ((Fin r → kˣ) →* ℂˣ)), (∀ i, IsExp (π i) (E i)) →
        ∀ c : Fin n → ℂ, (∀ t ∈ strictCone ϖ r, ∑ i, c i * charSum (E i) t = 0) → ∀ i, c i = 0

def ExponentsExist : Prop :=
  ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (r : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin r) k) V),
    IsAdmissible π → FiniteDimensional ℂ (fixed (jacBU π) (torusO k (Fin r))) ∧ ∃ E, IsExp π E

/- English proof (translation)
Use `Multiset.ext.2 fun χ => ?_` and prove the remaining obligations. Use `(h χ).symm.trans (h' χ)` as an intermediate fact. Use `Nat.cast_injective (R := ℕ∞) this` and compare the differences between its conclusion and the goal.
-/
theorem IsExp.unique {r : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]
    {π : Representation ℂ (GL (Fin r) k) V} {E E' : Multiset ((Fin r → kˣ) →* ℂˣ)}
    (h : IsExp π E) (h' : IsExp π E') : E = E' := by
  classical
  refine Multiset.ext.2 fun χ => ?_
  have := (h χ).symm.trans (h' χ)
  convert Nat.cast_injective (R := ℕ∞) this

/- English proof (translation)
Establish `h0 : expMult π χ ≠ 0`. Rewrite using `[h χ]`. Establish `: Multiset.count χ E ≠ 0` using `Multiset.count_ne_zero.2 hχ`. Introduce `h1`. Apply `this` to reduce the goal to its premises.

Use `Nat.cast_eq_zero.1 h1` and compare the differences between its conclusion and the goal. Establish `h1` using `Model.scalar_of_isSubquotient (g := t) (c := 1) (JHMult.jhMult_ne_zero_iff.1 h0) (fun v => Subtype.ext (by`. Establish `h2 : jacBU π t v.1 = _` using `v.2 ⟨t, ht⟩`. Use `show jacBU π t v.1 = _`. Simplify using `using h2)) 1`.

Use `ext`. Simplify using `using h1`.
-/
theorem IsExp.unramified {r : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]
    {π : Representation ℂ (GL (Fin r) k) V} {E : Multiset ((Fin r → kˣ) →* ℂˣ)}
    (h : IsExp π E) {χ : (Fin r → kˣ) →* ℂˣ} (hχ : χ ∈ E) {t : Fin r → kˣ}
    (ht : t ∈ torusO k (Fin r)) : χ t = 1 := by
  classical
  have h0 : expMult π χ ≠ 0 := by
    rw [h χ]
    have : Multiset.count χ E ≠ 0 := Multiset.count_ne_zero.2 hχ
    intro h1
    apply this
    convert Nat.cast_eq_zero.1 h1
  have h1 := Model.scalar_of_isSubquotient (g := t) (c := 1) (JHMult.jhMult_ne_zero_iff.1 h0)
    (fun v => Subtype.ext (by
      have h2 : jacBU π t v.1 = _ := v.2 ⟨t, ht⟩
      show jacBU π t v.1 = _
      simpa using h2)) 1
  ext
  simpa using h1

omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in

/- English proof (translation)
Assemble the required witnesses or components as `⟨fun i => -((i : ℕ) : ℤ), fun i j h => by have : (i : ℕ) < j := h; simp only; omega, rfl⟩`.
-/
example (ϖ : kˣ) (r : ℕ) : (fun i : Fin r => ϖ ^ (-((i : ℕ) : ℤ))) ∈ strictCone ϖ r :=
  ⟨fun i => -((i : ℕ) : ℤ), fun i j h => by have : (i : ℕ) < j := h; simp only; omega, rfl⟩

/- English proof (translation)
Take `⟨v, hv, h0⟩` from `(Submodule.ne_bot_iff _).1 (isSpherical_detRep (n := Fin r) h)`. Conclude with `(Submodule.ne_bot_iff _).2 ⟨v, fun g => by simpa using hv ⟨g.1, iwahori_le_KO k _ g.2⟩, h0⟩`.
-/
theorem fixed_detRep_ne_bot {r : ℕ} {χ : kˣ →* ℂˣ} (h : IsUnram χ) :
    fixed (detRep (Fin r) χ) (iwahori k (Fin r)) ≠ ⊥ := by
  obtain ⟨v, hv, h0⟩ := (Submodule.ne_bot_iff _).1 (isSpherical_detRep (n := Fin r) h)
  exact (Submodule.ne_bot_iff _).2 ⟨v, fun g => by simpa using hv ⟨g.1, iwahori_le_KO k _ g.2⟩, h0⟩

/- English proof (translation)
Assemble the required witnesses or components as `⟨(isSmooth_ofChar_iff _).2 (isSmoothChar_of_isUnram h).detChar, fun _ _ _ => inferInstance⟩`.
-/
theorem isAdmissible_detRep {r : ℕ} {χ : kˣ →* ℂˣ} (h : IsUnram χ) :
    IsAdmissible (detRep (Fin r) χ) :=
  ⟨(isSmooth_ofChar_iff _).2 (isSmoothChar_of_isUnram h).detChar, fun _ _ _ => inferInstance⟩

/- English proof (translation)
Establish `hb : twKer (detRep (Fin r) χ) (unipB k (Fin r)) 1 = ⊥` using `twKer_detRep _ χ`. Establish `hact : ∀ (t : Fin r → kˣ) (x : Jacquet (detRep (Fin r) χ) (unipB k (Fin r))), jacBU (detRep (Fin r) χ) t x = (torusChar (fun _ => χ) t : ℂ) • x`. Introduce `t x`. Take `⟨v, rfl⟩` from `Submodule.Quotient.mk_surjective _ x`. Establish `hd : Matrix.GeneralLinearGroup.det (diagT k (Fin r) t) = ∏ i, t i` using `by ext; simp [val_diagT]`.

Rewrite using `[jacBU_mk, ← Submodule.Quotient.mk_smul]`. Simplify using `[detRep, hd]`. Establish `ht : fixed (jacBU (detRep (Fin r) χ)) (torusO k (Fin r)) = ⊤`. Use `eq_top_iff.2 fun x _ t => ?_` and prove the remaining obligations. Establish `: torusChar (fun _ : Fin r => χ) t.1 = 1`.

Rewrite using `[torusChar_apply]`. Conclude with `Finset.prod_eq_one fun i _ => h _ (t.2 i)`. Rewrite using `[hact, this]`. Both sides reduce to the same expression. Establish `φ : (jacBUFixed (detRep (Fin r) χ)).Equiv (ofChar (torusChar fun _ : Fin r => χ))`.

Use `.mk ((LinearEquiv.ofTop _ ht).trans (Submodule.quotEquivOfEqBot _ hb)) fun t => ?_` and prove the remaining obligations. Use `LinearMap.ext fun x => ?_` and prove the remaining obligations. Establish `: jacBUFixed (detRep (Fin r) χ) t x = (torusChar (fun _ => χ) t : ℂ) • x` using `Subtype.ext (hact t x.1)`. Simplify using `only [LinearMap.comp_apply]`. Rewrite using `[this, map_smul, ofChar_apply, smul_eq_mul]`.

Introduce `ψ`. Rewrite using `[expMult, jhMult_congr_right _ φ]`. Distinguish the cases in `hψ : ψ = torusChar fun _ : Fin r => χ`. Rewrite using `[hψ, jhMult_self (isIrreducible_ofChar _)]`. Simplify using the standard rewrite rules.

Rewrite using `[Model.jhMult_ofChar_ne hψ]`. Simplify using `[hψ]`.
-/
theorem isExp_detRep {r : ℕ} {χ : kˣ →* ℂˣ} (h : IsUnram χ) :
    IsExp (detRep (Fin r) χ) {torusChar fun _ => χ} := by
  classical
  have hb : twKer (detRep (Fin r) χ) (unipB k (Fin r)) 1 = ⊥ := twKer_detRep _ χ
  have hact : ∀ (t : Fin r → kˣ) (x : Jacquet (detRep (Fin r) χ) (unipB k (Fin r))),
      jacBU (detRep (Fin r) χ) t x = (torusChar (fun _ => χ) t : ℂ) • x := by
    intro t x
    obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    have hd : Matrix.GeneralLinearGroup.det (diagT k (Fin r) t) = ∏ i, t i := by
      ext; simp [val_diagT]
    rw [jacBU_mk, ← Submodule.Quotient.mk_smul]
    simp [detRep, hd]
  have ht : fixed (jacBU (detRep (Fin r) χ)) (torusO k (Fin r)) = ⊤ := by
    refine eq_top_iff.2 fun x _ t => ?_
    have : torusChar (fun _ : Fin r => χ) t.1 = 1 := by
      rw [torusChar_apply]
      exact Finset.prod_eq_one fun i _ => h _ (t.2 i)
    rw [hact, this]
    rfl
  have φ : (jacBUFixed (detRep (Fin r) χ)).Equiv (ofChar (torusChar fun _ : Fin r => χ)) := by
    refine .mk ((LinearEquiv.ofTop _ ht).trans (Submodule.quotEquivOfEqBot _ hb)) fun t => ?_
    refine LinearMap.ext fun x => ?_
    have : jacBUFixed (detRep (Fin r) χ) t x = (torusChar (fun _ => χ) t : ℂ) • x :=
      Subtype.ext (hact t x.1)
    simp only [LinearMap.comp_apply]
    rw [this, map_smul, ofChar_apply, smul_eq_mul]
  intro ψ
  rw [expMult, jhMult_congr_right _ φ]
  by_cases hψ : ψ = torusChar fun _ : Fin r => χ
  · rw [hψ, jhMult_self (isIrreducible_ofChar _)]
    simp
  · rw [Model.jhMult_ofChar_ne hψ]
    simp [hψ]

end GlobalTheory.IndefiniteRowSideFullHecke.ExponentSeparationTwistedDiscreteSeries

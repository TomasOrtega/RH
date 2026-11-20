import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.EntryAgree
import Formalism.LocalToGlobal.Columns.ChainTw
open NumberField IsDedekindDomain MeasureTheory ValuativeRel Matrix Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.TwBridge GlobalTheory.SymBridge

noncomputable section
namespace GlobalTheory.TwBridge.TopPhi

/- English proof (translation)
Introduce `X Pr R Ch sel S₀ mu cst σ₀ P k _ _ _ _ ι s W _ _ ν hA hPhi e' e he' he y`. Establish `hm : R.m = s + 2` using `hA.steps`. Establish `hlast : (e (Sum.inr ())).val = R.N R.m - 1` using `he (Sum.inr ())`. Establish `hc : cOf R (s + 1) = 0` using `by unfold cOf; omega`. Set `E1' : XIx (Fin R.k) (Fin R.t) (s + 1) ⊕ Fin 0 ≃ Fin (R.N (s + 1) + cOf R (s + 1))` to `(Equiv.sumEmpty _ _).trans (e'.trans (finCongr (by omega)))`.

Establish `hbd : ∀ z, (e (Sum.inl z)).val < R.N R.m - 1 + 0` using `fun z => by`. Establish `h1` using `(e (Sum.inl z)).isLt`. Establish `h2 : e (Sum.inl z) ≠ e (Sum.inr ())` using `e.injective.ne (by simp)`. Establish `h3 : (e (Sum.inl z)).val ≠ R.N R.m - 1` using `fun h => h2 (Fin.ext (h.trans hlast.symm))`. Use linear arithmetic over natural numbers and integers.

Set `f1 : Ix (Fin R.k ⊕ Fin (s + 1)) (Fin R.t) (s + 2) → Fin (R.N R.m - 1 + 0)` to `fun z => ⟨(e (Sum.inl z)).val, hbd z⟩`. Establish `hf1 : Function.Bijective f1`. Use `(Fintype.bijective_iff_injective_and_card _).2 ⟨fun z z' h => ?_, ?_⟩` and prove the remaining obligations. Establish `h'` using `Fin.val_eq_of_eq h`. Establish `: e (Sum.inl z) = e (Sum.inl z')` using `Fin.ext h'`.

Conclude with `Sum.inl_injective (e.injective this)`. Use `Fintype.card_congr e` as an intermediate fact. Simplify using `only [Fintype.card_sum, Fintype.card_prod, Fintype.card_unit, Fintype.card_fin] at this ⊢`. Use linear arithmetic over natural numbers and integers. Set `E1` to `Equiv.ofBijective f1 hf1`.

Establish `hE1' : IsOrdY E1'`. Introduce and unpack `(a | a)`. Conclude with `he' a`. Conclude with `a.elim0`. Establish `hE1 : IsOrd zPos E1` using `fun z => he (Sum.inl z)`.

Establish `hmat : fromCols (toLoc ι e e' y).toRows₁ 0 = toLoc ι E1 E1' (prXp X.E R ∘ₗ y ∘ₗ LinearMap.funLeft X.E X.E (Fin.castAdd (cOf R (s + 1))))`. Use extensionality with `z c`. Break down `c with c | c` into its components or cases. Simplify using `only [fromCols_apply_inl, toRows₁_apply, toLoc, LinearMap.comp_apply, prXp, LinearMap.funLeft_apply]`. Establish `hs : LinearMap.funLeft X.E X.E (Fin.castAdd (cOf R (s + 1))) (Pi.single (E1' (Sum.inl c)) 1) = Pi.single (e' c) 1`.

Use function extensionality and compare the values at `i`. Simplify using `[E1', Pi.single_apply, Fin.ext_iff]`. Rewrite using `[hs]`. Both sides reduce to the same expression. Conclude with `c.elim0`.

Rewrite using `[hmat]`. Conclude with `hPhi.2 E1' E1 hE1' hE1 _`.
-/
theorem topPhi : ∀ (X : Fields) (Pr : Primes X) (R : Ranks) (Ch : Chars X Pr R.m) (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) (S₀ : Set ℕ) (mu : Tup X.F X.E X.K S₀) (cst : LocCst X (rowSG Pr sel mu)) (σ₀ : X.K →+* ℂ) (P : rowSG Pr sel mu) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ι : X.E →+* k) (s : ℕ) (W : TwData k) [MeasurableSpace k] [BorelSpace k] (ν : Measure k), AtTwist (R := R) sel mu cst σ₀ P ι s W → PhiAgree Ch sel mu cst σ₀ P ι s W →
  ∀ (e' : XIx (Fin R.k) (Fin R.t) (s + 1) ≃ Fin (R.N (s + 1))) (e : Ix (Fin R.k ⊕ Fin (s + 1)) (Fin R.t) (s + 2) ⊕ Unit ≃ Fin (R.N R.m)),
    IsOrd xPos e' → IsOrd (Sum.elim zPos fun _ => R.N R.m - 1) e → ∀ (y : HomE X.E (R.N (s + 1)) (R.N R.m)),
      (W.T s R).PhiTop (fromCols (toLoc ι e e' y).toRows₁ 0) =
        σ₀ (PhiTop Ch mu cst.sharp s P.1 (prXp X.E R ∘ₗ y ∘ₗ LinearMap.funLeft X.E X.E (Fin.castAdd (cOf R (s + 1))))) := by
  classical
  intro X Pr R Ch sel S₀ mu cst σ₀ P k _ _ _ _ ι s W _ _ ν hA hPhi e' e he' he y
  have hm : R.m = s + 2 := hA.steps
  have hlast : (e (Sum.inr ())).val = R.N R.m - 1 := he (Sum.inr ())
  have hc : cOf R (s + 1) = 0 := by unfold cOf; omega
  let E1' : XIx (Fin R.k) (Fin R.t) (s + 1) ⊕ Fin 0 ≃ Fin (R.N (s + 1) + cOf R (s + 1)) :=
    (Equiv.sumEmpty _ _).trans (e'.trans (finCongr (by omega)))
  have hbd : ∀ z, (e (Sum.inl z)).val < R.N R.m - 1 + 0 := fun z => by
    have h1 := (e (Sum.inl z)).isLt
    have h2 : e (Sum.inl z) ≠ e (Sum.inr ()) := e.injective.ne (by simp)
    have h3 : (e (Sum.inl z)).val ≠ R.N R.m - 1 := fun h => h2 (Fin.ext (h.trans hlast.symm))
    omega
  let f1 : Ix (Fin R.k ⊕ Fin (s + 1)) (Fin R.t) (s + 2) → Fin (R.N R.m - 1 + 0) :=
    fun z => ⟨(e (Sum.inl z)).val, hbd z⟩
  have hf1 : Function.Bijective f1 := by
    refine (Fintype.bijective_iff_injective_and_card _).2 ⟨fun z z' h => ?_, ?_⟩
    · have h' := Fin.val_eq_of_eq h
      have : e (Sum.inl z) = e (Sum.inl z') := Fin.ext h'
      exact Sum.inl_injective (e.injective this)
    · have := Fintype.card_congr e
      simp only [Fintype.card_sum, Fintype.card_prod, Fintype.card_unit, Fintype.card_fin] at this ⊢
      omega
  let E1 := Equiv.ofBijective f1 hf1
  have hE1' : IsOrdY E1' := by
    rintro (a | a)
    · exact he' a
    · exact a.elim0
  have hE1 : IsOrd zPos E1 := fun z => he (Sum.inl z)
  have hmat : fromCols (toLoc ι e e' y).toRows₁ 0 =
      toLoc ι E1 E1' (prXp X.E R ∘ₗ y ∘ₗ LinearMap.funLeft X.E X.E (Fin.castAdd (cOf R (s + 1)))) := by
    ext z c
    rcases c with c | c
    · simp only [fromCols_apply_inl, toRows₁_apply, toLoc, LinearMap.comp_apply, prXp, LinearMap.funLeft_apply]
      have hs : LinearMap.funLeft X.E X.E (Fin.castAdd (cOf R (s + 1))) (Pi.single (E1' (Sum.inl c)) 1) =
          Pi.single (e' c) 1 := by
        funext i
        simp [E1', Pi.single_apply, Fin.ext_iff]
      rw [hs]
      rfl
    · exact c.elim0
  rw [hmat]
  exact hPhi.2 E1' E1 hE1' hE1 _

end GlobalTheory.TwBridge.TopPhi

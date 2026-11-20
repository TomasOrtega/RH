import Development.WeilBound.CoreStatements.PublishedTheorems.CasselmanWallach.SmoothSeminormAndSobolevBounds
import CompanionTheory.HarishChandraModules.KFiniteAnalyticVectors.AnalyticIntertwiners.HarishChandraModulesIndefiniteUnitaryGroup
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.AnalyticVectors.Unitary

noncomputable section

open Matrix Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.SmoothGlob GlobalTheory.TypeSum
open scoped InnerProductSpace

namespace PositivityTheory.CW.KFiniteInclusion

variable {n : ℕ} {ε : Fin n → Bool} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  {σ : Mx n → (H →L[ℂ] H)}

def incl (hK : ∀ v : H, IsKFin ε σ v → v ∈ ReciprocityTheory.ChartRestriction.DS.smD ε σ) :
    kfin ε σ →ₗ[ℂ] ReciprocityTheory.ChartRestriction.DS.smD ε σ where
  toFun v := ⟨v, hK v v.2⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem incl_val (hK : ∀ v : H, IsKFin ε σ v → v ∈ ReciprocityTheory.ChartRestriction.DS.smD ε σ) (v : kfin ε σ) :
    ((incl hK v : ReciprocityTheory.ChartRestriction.DS.smD ε σ) : H) = v := rfl

/- English proof (translation)
Establish `h'` using `congrArg Subtype.val h`. Conclude with `Subtype.ext h'`.
-/
theorem incl_inj (hK : ∀ v : H, IsKFin ε σ v → v ∈ ReciprocityTheory.ChartRestriction.DS.smD ε σ) {v w : kfin ε σ}
    (h : incl hK v = incl hK w) : v = w := by
  have h' := congrArg Subtype.val h
  exact Subtype.ext h'

def Eop (hK : ∀ v : H, IsKFin ε σ v → v ∈ ReciprocityTheory.ChartRestriction.DS.smD ε σ)
    (h2 : ∀ a b, ∀ v ∈ CompanionTheory.D.gk.HC.KF ε σ, ReciprocityTheory.ChartRestriction.DS.smE ε σ a b v ∈ CompanionTheory.D.gk.HC.KF ε σ)
    (a b : Fin n) : Module.End ℂ (kfin ε σ) where
  toFun v := ⟨(ReciprocityTheory.ChartRestriction.DS.smE ε σ a b (incl hK v) : H), h2 a b (incl hK v) v.2⟩
  map_add' x y := Subtype.ext (by simp only [map_add, Submodule.coe_add])
  map_smul' c x := Subtype.ext (by simp only [map_smul, Submodule.coe_smul, RingHom.id_apply])

variable (hK : ∀ v : H, IsKFin ε σ v → v ∈ ReciprocityTheory.ChartRestriction.DS.smD ε σ)
    (h2 : ∀ a b, ∀ v ∈ CompanionTheory.D.gk.HC.KF ε σ, ReciprocityTheory.ChartRestriction.DS.smE ε σ a b v ∈ CompanionTheory.D.gk.HC.KF ε σ)

/- English proof (translation)
The claim follows from `Subtype.ext rfl`.
-/
theorem incl_E (a b : Fin n) (v : kfin ε σ) :
    incl hK (Eop hK h2 a b v) = ReciprocityTheory.ChartRestriction.DS.smE ε σ a b (incl hK v) := Subtype.ext rfl

/- English proof (translation)
Simplify using `only [ReciprocityTheory.ChartRestriction.DS.actM, LinearMap.sum_apply, LinearMap.smul_apply, map_sum, map_smul, incl_E]`.
-/
theorem incl_actM (X : Mx n) (v : kfin ε σ) :
    incl hK (ReciprocityTheory.ChartRestriction.DS.actM (Eop hK h2) X v) = ReciprocityTheory.ChartRestriction.DS.actM (ReciprocityTheory.ChartRestriction.DS.smE ε σ) X (incl hK v) := by
  simp only [ReciprocityTheory.ChartRestriction.DS.actM, LinearMap.sum_apply, LinearMap.smul_apply, map_sum, map_smul, incl_E]

end PositivityTheory.CW.KFiniteInclusion

namespace PositivityTheory.CW

open KFiniteInclusion

/- English proof (translation)
Introduce `n ε H _ _ _ σ hσ hirr`. Take `⟨hK, h2⟩` from `CompanionTheory.D.gk.HC.K_finite_smooth_vectors n ε H σ hσ hirr`. Establish `hD` using `ReciprocityTheory.ChartRestriction.DS.isDerivedOn_smE hσ`. Establish `hun` using `ReciprocityTheory.ChartRestriction.DS.isInfUnitary_of_isDerivedOn hσ hD`. Use `⟨Eop hK h2, ?_, ?_, ?_, ?_⟩` and prove the remaining obligations.

Introduce `X hX v`. Establish `h` using `ReciprocityTheory.ChartRestriction.DS.dS_eq_actM hD (X := X) hX (incl hK v)`. Establish `e1 : ((ReciprocityTheory.ChartRestriction.DS.actM (Eop hK h2) X v : kfin ε σ) : H) = ((ReciprocityTheory.ChartRestriction.DS.actM (ReciprocityTheory.ChartRestriction.DS.smE ε σ) X (incl hK v) : ReciprocityTheory.ChartRestriction.DS.smD ε σ) : H)`. Rewrite using `[← incl_actM hK h2 X v]`. Both sides reduce to the same expression.

Rewrite using `[e1, ← h]`. Simplify using `only [ReciprocityTheory.ChartRestriction.DS.dS, dRep, Complex.coe_smul, incl_val]`. Introduce `a b c d`. Use `LinearMap.ext fun v => incl_inj hK ?_` and prove the remaining obligations. Establish `h` using `LinearMap.congr_fun (hD.glRep a b c d) (incl hK v)`.

Simplify using `only [LinearMap.sub_apply, Module.End.mul_apply, map_sub, incl_E] at h ⊢`. Rewrite using `[h]`. Apply the tactic sequence `split_ifs <;> simp [incl_E]`. Introduce `a b x y`. Establish `h` using `hun a b (incl hK x) (incl hK y)`.

Rewrite `h` using `[Submodule.coe_inner, Submodule.coe_inner]`. Rewrite using `[Submodule.coe_inner, Submodule.coe_inner]`. Conclude with `h`. Introduce `N hN set M := N.map (incl hK) with hM`. Establish `hMK : (M : Set (ReciprocityTheory.ChartRestriction.DS.smD ε σ)) ⊆ CompanionTheory.D.gk.HC.KF ε σ`.

Introduce and unpack `_ ⟨w, -, rfl⟩`. Conclude with `w.2`. Establish `hMst : ∀ a b, ∀ v ∈ M, ReciprocityTheory.ChartRestriction.DS.smE ε σ a b v ∈ M`. Introduce and unpack `a b _ ⟨w, hw, rfl⟩`. Conclude with `⟨Eop hK h2 a b w, hN a b w hw, incl_E hK h2 a b w⟩`.

Break down `CompanionTheory.D.gk.HC.uIrr n ε H σ hσ hirr M hMK hMst with h | h` into its components or cases. Use `left`. Use `eq_bot_iff.2 fun x hx => ?_` and prove the remaining obligations. Establish `: incl hK x ∈ M` using `⟨x, hx, rfl⟩`. Rewrite `this` using `[h, Submodule.mem_bot]`.

Rewrite using `[Submodule.mem_bot]`. Conclude with `incl_inj hK (this.trans (map_zero _).symm)`. Use `right`. Use `eq_top_iff.2 fun x _ => ?_` and prove the remaining obligations. Establish `: incl hK x ∈ (M : Set (ReciprocityTheory.ChartRestriction.DS.smD ε σ))` using `by rw [h]; exact x.2`.

Take `⟨w, hw, e⟩` from `this`. Rewrite using `[← incl_inj hK e]` and apply the resulting hypothesis.
-/
theorem c1 : C1 := by
  intro n ε H _ _ _ σ hσ hirr
  obtain ⟨hK, h2⟩ := CompanionTheory.D.gk.HC.K_finite_smooth_vectors n ε H σ hσ hirr
  have hD := ReciprocityTheory.ChartRestriction.DS.isDerivedOn_smE hσ
  have hun := ReciprocityTheory.ChartRestriction.DS.isInfUnitary_of_isDerivedOn hσ hD
  refine ⟨Eop hK h2, ?_, ?_, ?_, ?_⟩
  · intro X hX v
    have h := ReciprocityTheory.ChartRestriction.DS.dS_eq_actM hD (X := X) hX (incl hK v)
    have e1 : ((ReciprocityTheory.ChartRestriction.DS.actM (Eop hK h2) X v : kfin ε σ) : H) =
        ((ReciprocityTheory.ChartRestriction.DS.actM (ReciprocityTheory.ChartRestriction.DS.smE ε σ) X (incl hK v) : ReciprocityTheory.ChartRestriction.DS.smD ε σ) : H) := by
      rw [← incl_actM hK h2 X v]
      rfl
    rw [e1, ← h]
    simp only [ReciprocityTheory.ChartRestriction.DS.dS, dRep, Complex.coe_smul, incl_val]
  · intro a b c d
    refine LinearMap.ext fun v => incl_inj hK ?_
    have h := LinearMap.congr_fun (hD.glRep a b c d) (incl hK v)
    simp only [LinearMap.sub_apply, Module.End.mul_apply, map_sub, incl_E] at h ⊢
    rw [h]
    split_ifs <;> simp [incl_E]
  · intro a b x y
    have h := hun a b (incl hK x) (incl hK y)
    rw [Submodule.coe_inner, Submodule.coe_inner] at h
    rw [Submodule.coe_inner, Submodule.coe_inner]
    exact h
  · intro N hN
    set M := N.map (incl hK) with hM
    have hMK : (M : Set (ReciprocityTheory.ChartRestriction.DS.smD ε σ)) ⊆ CompanionTheory.D.gk.HC.KF ε σ := by
      rintro _ ⟨w, -, rfl⟩
      exact w.2
    have hMst : ∀ a b, ∀ v ∈ M, ReciprocityTheory.ChartRestriction.DS.smE ε σ a b v ∈ M := by
      rintro a b _ ⟨w, hw, rfl⟩
      exact ⟨Eop hK h2 a b w, hN a b w hw, incl_E hK h2 a b w⟩
    rcases CompanionTheory.D.gk.HC.uIrr n ε H σ hσ hirr M hMK hMst with h | h
    · left
      refine eq_bot_iff.2 fun x hx => ?_
      have : incl hK x ∈ M := ⟨x, hx, rfl⟩
      rw [h, Submodule.mem_bot] at this
      rw [Submodule.mem_bot]
      exact incl_inj hK (this.trans (map_zero _).symm)
    · right
      refine eq_top_iff.2 fun x _ => ?_
      have : incl hK x ∈ (M : Set (ReciprocityTheory.ChartRestriction.DS.smD ε σ)) := by rw [h]; exact x.2
      obtain ⟨w, hw, e⟩ := this
      rwa [← incl_inj hK e]

end PositivityTheory.CW

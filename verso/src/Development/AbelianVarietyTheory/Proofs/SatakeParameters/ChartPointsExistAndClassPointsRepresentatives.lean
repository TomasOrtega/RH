import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.UnderTie
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ChartPointLeftTranslateRationalUnitaryStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ChartBasePointRightTranslateByChartLevelStatement

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.Ker Formalism.L2.DIV GlobalTheory.TwU GlobalTheory.TwV Formalism.UG Formalism.L2.PairingIndexBounds.F Formalism.MainNotions.G.KAat Formalism.L2.Forms Formalism.MainNotions.G

noncomputable section

namespace GlobalTheory.TwV

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Cls

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : G.Inst D L} {Gl : G.LatInst D} {Kc : G.Consts} {Y : DivX D} {cX : ExtraC}
  {ex : Extra D L hT Gi Gl Kc Y cX} {t : KerEntTied ex} {u : D.what₂.Word} {μ : D.what₂.Tup} {St : ChainCharts D u μ}
  {A : AdData t u μ St} {dtU : Formalism.L2.Herm.unitaryOneFiniteAdeles D.sp.cm →* D.Dt} {a : 𝓞 D.host.E}

/- English proof (translation)
Rewrite using `[← H.N_eq i hi c]`. Conclude with `H.lat i hi c`. Use `frame := fun P => H.frame i hi c P`. Use `fnl := by`. Introduce `P v h hv`.

Conclude with `Classical.epsilon_spec (H.fnl i hi ((St i hi).chOf c) P v h hv) c rfl`.
-/
theorem isPtAd_cls (H : AdTie A dtU a) (i : ℕ) (hi : i ≤ D.R.m) (c : (D.chTw u μ).cls i) :
    IsPtAd A a i hi ((St i hi).chOf c) ((St i hi).y c) (A.pt i hi c) where
  lat := by
    rw [← H.N_eq i hi c]
    exact H.lat i hi c
  frame := fun P => H.frame i hi c P
  fnl := by
    intro P v h hv
    exact Classical.epsilon_spec (H.fnl i hi ((St i hi).chOf c) P v h hv) c rfl

/- English proof (translation)
Take `⟨⟨c, rfl⟩, hc⟩` from `((St i hi).K β).y_bij.2 (Quotient.mk'' x)`. Take `⟨g, hg, k, hk, e⟩` from `(DoubleCoset.eq _ _ _ _).1 hc`. Rewrite `hg`, `hk` using `[Subgroup.mem_subgroupOf]`. Take `⟨γ, hγ, hγg⟩` from `Subgroup.mem_map.1 hg`. Use `⟨c, rfl, γ, hγ, ⟨k.1, hk⟩, ?_⟩` and prove the remaining obligations.

Establish `e1` using `congrArg Subtype.val e`. Simplify using `only [Subgroup.coe_mul] at e1`. Rewrite using `[e1, ← hγg]`. Both sides reduce to the same expression.
-/
theorem exists_cls_eq (i : ℕ) (hi : i ≤ D.R.m) (β : (St i hi).Ch) (x : UA D i hi) :
    ∃ c : (D.chTw u μ).cls i, (St i hi).chOf c = β ∧ ∃ γ ∈ UJ (sigD D : D.host.E →+* D.host.E) (gramN D i hi),
      ∃ κ : ((St i hi).K β).lev.U, x.1 = ratA D.host.F γ * ((St i hi).y c).1 * κ.1 := by
  obtain ⟨⟨c, rfl⟩, hc⟩ := ((St i hi).K β).y_bij.2 (Quotient.mk'' x)
  obtain ⟨g, hg, k, hk, e⟩ := (DoubleCoset.eq _ _ _ _).1 hc
  rw [Subgroup.mem_subgroupOf] at hg hk
  obtain ⟨γ, hγ, hγg⟩ := Subgroup.mem_map.1 hg
  refine ⟨c, rfl, γ, hγ, ⟨k.1, hk⟩, ?_⟩
  have e1 := congrArg Subtype.val e
  simp only [Subgroup.coe_mul] at e1
  rw [e1, ← hγg]
  rfl

end Cls

/- English proof (translation)
Introduce `D L hT Gi Gl Kc Y cX ex t u μ St A dtU a hPin hTie`. Establish `hcls : ∀ i hi c, IsPtAd A a i hi ((St i hi).chOf c) ((St i hi).y c) (A.pt i hi c)` using `fun i hi c => isPtAd_cls hTie i hi c`. Use `⟨fun i hi β x => ?_, hcls⟩` and prove the remaining obligations. Take `⟨c, hcβ, γ, hγ, κ, hx⟩` from `exists_cls_eq (St := St) i hi β x`. Substitute `hcβ` using the available equality.

Set `k : UA D i hi` to `⟨κ.1, (((St i hi).K ((St i hi).chOf c)).lev.U_eq κ.1).1 κ.2 |>.1⟩`. Set `x₁ : UA D i hi` to `x * k⁻¹`. Establish `hx₁ : x₁.1 = ratA D.host.F γ * ((St i hi).y c).1` using `by show x.1 * (κ.1)⁻¹ = _`. Rewrite using `[hx, mul_inv_cancel_right]`. Take `⟨p₁, hp₁⟩` from `hR A dtU a hPin hTie i hi _ ((St i hi).y c) x₁ (A.pt i hi c) γ hγ hx₁ (hcls i hi c)`.

Establish `hxk : x.1 = x₁.1 * κ.1` using `by show x.1 = x.1 * (κ.1)⁻¹ * κ.1`. Rewrite using `[inv_mul_cancel_right]`. Conclude with `hL A dtU a hPin hTie i hi _ x₁ x p₁ κ hxk hp₁`.
-/
theorem ptEx_of_tie (hR : UnderTie (fun {D L hT Gi Gl Kc Y cX ex t u μ St} A dtU a => ∀ (i : ℕ) (hi : i ≤ D.R.m) (β : (St i hi).Ch) (x x' : UA D i hi) p, ∀ γ ∈ Formalism.UG.UJ (Formalism.L2.Forms.sigD D : D.host.E →+* D.host.E) (Formalism.L2.Forms.gramN D i hi), x'.1 = ratA D.host.F γ * x.1 → IsPtAd A a i hi β x p → ∃ p', IsPtAd A a i hi β x' p')) (hL : UnderTie (fun {D L hT Gi Gl Kc Y cX ex t u μ St} A dtU a => ∀ (i : ℕ) (hi : i ≤ D.R.m) (β : (St i hi).Ch) (x x' : UA D i hi) p (κ : ((St i hi).K β).lev.U), x'.1 = x.1 * κ.1 → IsPtAd A a i hi β x p → ∃ p', IsPtAd A a i hi β x' p')) : UnderTie (fun {D L hT Gi Gl Kc Y cX ex t u μ St} A dtU a => PtEx A a ∧ ∀ i hi c, IsPtAd A a i hi ((St i hi).chOf c) ((St i hi).y c) (A.pt i hi c)) := by
  intro D L hT Gi Gl Kc Y cX ex t u μ St A dtU a hPin hTie
  have hcls : ∀ i hi c, IsPtAd A a i hi ((St i hi).chOf c) ((St i hi).y c) (A.pt i hi c) :=
    fun i hi c => isPtAd_cls hTie i hi c
  refine ⟨fun i hi β x => ?_, hcls⟩
  obtain ⟨c, hcβ, γ, hγ, κ, hx⟩ := exists_cls_eq (St := St) i hi β x
  subst hcβ

  let k : UA D i hi := ⟨κ.1, (((St i hi).K ((St i hi).chOf c)).lev.U_eq κ.1).1 κ.2 |>.1⟩

  let x₁ : UA D i hi := x * k⁻¹
  have hx₁ : x₁.1 = ratA D.host.F γ * ((St i hi).y c).1 := by
    show x.1 * (κ.1)⁻¹ = _
    rw [hx, mul_inv_cancel_right]
  obtain ⟨p₁, hp₁⟩ := hR A dtU a hPin hTie i hi _ ((St i hi).y c) x₁ (A.pt i hi c) γ hγ hx₁ (hcls i hi c)
  have hxk : x.1 = x₁.1 * κ.1 := by
    show x.1 = x.1 * (κ.1)⁻¹ * κ.1
    rw [inv_mul_cancel_right]
  exact hL A dtU a hPin hTie i hi _ x₁ x p₁ κ hxk hp₁

/- English proof (translation)
The claim follows from `ptEx_of_tie GlobalTheory.T.chartPoint_leftTranslate_rationalUnitary GlobalTheory.T.chartBasePoint_rightTranslate_by_chartLevel`.
-/
theorem ptEx_isPtAd : UnderTie (fun {D L hT Gi Gl Kc Y cX ex t u μ St} A dtU a => PtEx A a ∧ ∀ i hi c, IsPtAd A a i hi ((St i hi).chOf c) ((St i hi).y c) (A.pt i hi c)) :=
  ptEx_of_tie GlobalTheory.T.chartPoint_leftTranslate_rationalUnitary GlobalTheory.T.chartBasePoint_rightTranslate_by_chartLevel

end GlobalTheory.TwV

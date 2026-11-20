import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutEX2
import Formalism.HermitianCurvature.HermitianCurvatureProofs.PBGLet

noncomputable section

open Matrix MeasureTheory Filter Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt
open scoped ContDiff

namespace Formalism.FourierDecayAlt.P.CutEXUw

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

section gloc

variable {k r : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]

def LocOpG (T : (B.Mat k r → E) → (B.Mat k r → E)) : Prop :=
  ∀ O : Set (B.Mat k r), IsOpen O → ∀ f₁ f₂ : B.Mat k r → E, (∀ x ∈ O, x ∈ B.GV k r → f₁ x = f₂ x) →
    ∀ x ∈ O, x ∈ B.GV k r → T f₁ x = T f₂ x

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. A detailed English derivation is pending.
-/
theorem locOpG_top (u : ℂ) (a b : Fin (2 * r + k + 1)) :
    LocOpG (k := k) (r := r) (E := E) (Formalism.QuantumDeterminants.Top (EabH (Hpk k r)) u a b) := by
  intro O hO f₁ f₂ h x hx hxG
  exact PBG.top_congr' O hO u a b h x hx hxG

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem locOpG_foldr : ∀ (L : List ((B.Mat k r → E) → (B.Mat k r → E))), (∀ T ∈ L, LocOpG T) →
    LocOpG (fun f => L.foldr (fun T h => T h) f)
  | [], _ => fun _ _ _ _ h => h
  | T :: L, hL => by
    intro O hO f₁ f₂ h x hx hxG
    simp only [List.foldr_cons]
    exact hL T List.mem_cons_self O hO _ _
      (locOpG_foldr L (fun T' hT' => hL T' (List.mem_cons_of_mem _ hT')) O hO f₁ f₂ h) x hx hxG

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Simplify using the standard rewrite rules. Reduce the conclusion to the remaining proof obligations. Reduce the equality to equality of the corresponding arguments. Reduce the conclusion to the remaining proof obligations.

Extract witnesses or component facts from the available result. A detailed English derivation is pending.
-/
theorem locOpG_qminorOp {t : ℕ} (a b : Fin t → Fin (2 * r + k + 1)) (u : ℂ) :
    LocOpG (k := k) (r := r) (E := E) (qminorOp (EabH (Hpk k r)) a b u) := by
  intro O hO f₁ f₂ h x hx hxG
  simp only [qminorOp, Finset.sum_apply, Pi.smul_apply]
  refine Finset.sum_congr rfl fun σ _ => ?_
  congr 1
  refine locOpG_foldr _ (fun T hT => ?_) O hO f₁ f₂ h x hx hxG
  obtain ⟨i, rfl⟩ := List.mem_ofFn.1 hT
  exact locOpG_top _ _ _

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Simplify using the standard rewrite rules. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression.

A detailed English derivation is pending.
-/
theorem locOpG_AAop (m : ℕ) (hm : m ≤ r) (u : ℂ) : LocOpG (k := k) (r := r) (E := E) (C3.AAop k r m hm u) := by
  intro O hO f₁ f₂ h x hx hxG
  simp only [C3.AAop]
  refine Finset.sum_congr rfl fun c _ => ?_
  split_ifs
  · rw [locOpG_qminorOp _ _ _ O hO f₁ f₂ h x hx hxG]
  · rfl

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Simplify using the standard rewrite rules. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression.

A detailed English derivation is pending.
-/
theorem locOpG_AAvop (m : ℕ) (hm : m ≤ r) (ell : ℂ) :
    LocOpG (k := k) (r := r) (E := E) (C3.AAvop k r m hm ell) := by
  intro O hO f₁ f₂ h x hx hxG
  simp only [C3.AAvop]
  refine Finset.sum_congr rfl fun c _ => ?_
  split_ifs
  · rw [locOpG_qminorOp _ _ _ O hO f₁ f₂ h x hx hxG]
  · rfl

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Simplify using the standard rewrite rules. Both sides reduce to the same expression. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities.

A detailed English derivation is pending.
-/
theorem locOpG_vLet (z z' : Fin (2 * r + k + 1) → ℂ) (j : ℕ) (hj : j ≤ r) (l : C.Letter) (e : Fin 2) :
    LocOpG (k := k) (r := r) (E := E) (D.vLet k r z z' j hj l e) := by
  intro O hO f₁ f₂ h x hx hxG
  simp only [D.vLet]
  split_ifs
  · rfl
  · rw [locOpG_AAop _ _ _ O hO f₁ f₂ h x hx hxG]
  · rw [locOpG_AAvop _ _ _ O hO f₁ f₂ h x hx hxG]

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem uwG_congrG (z z' : Fin (2 * r + k + 1) → ℂ) (j : ℕ) (hj : j ≤ r) {O : Set (B.Mat k r)} (hO : IsOpen O)
    {f₁ f₂ : B.Mat k r → E} (h : ∀ x ∈ O, x ∈ B.GV k r → f₁ x = f₂ x) :
    ∀ (w : List C.Letter) (e : Wd.Ix (Fin w.length)), ∀ x ∈ O, x ∈ B.GV k r →
      D.uwG k r z z' f₁ j hj w e x = D.uwG k r z z' f₂ j hj w e x
  | [], _ => h
  | l :: w, e => by
    intro x hx hxG
    simp only [D.uwG]
    exact locOpG_vLet z z' j hj l _ O hO _ _ (uwG_congrG z z' j hj hO h w _) x hx hxG

/- English proof (translation)
Apply function extensionality and compare values at an arbitrary argument. Simplify using the standard rewrite rules. A detailed English derivation is pending.
-/
theorem top_zero (u : ℂ) (a b : Fin (2 * r + k + 1)) :
    Formalism.QuantumDeterminants.Top (EabH (Hpk k r)) u a b (fun _ : B.Mat k r => (0 : E)) = fun _ => 0 := by
  funext g
  simp only [Formalism.QuantumDeterminants.Top, smul_zero, ite_self, zero_add]
  exact PBG.eabH_zero a b g

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem foldr_zero : ∀ (L : List ((B.Mat k r → E) → (B.Mat k r → E))),
    (∀ T ∈ L, T (fun _ => 0) = fun _ => 0) → L.foldr (fun T h => T h) (fun _ => (0 : E)) = fun _ => 0
  | [], _ => rfl
  | T :: L, hL => by
    simp only [List.foldr_cons]
    rw [foldr_zero L (fun T' hT' => hL T' (List.mem_cons_of_mem _ hT'))]
    exact hL T List.mem_cons_self

/- English proof (translation)
Replace the relevant objects with their definitions. Reduce the claim to the hypotheses of an applicable result. Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities. Apply function extensionality and compare values at an arbitrary argument.

Simplify using the standard rewrite rules.
-/
theorem qminorOp_zero {t : ℕ} (a b : Fin t → Fin (2 * r + k + 1)) (u : ℂ) :
    qminorOp (EabH (Hpk k r)) a b u (fun _ : B.Mat k r => (0 : E)) = fun _ => 0 := by
  unfold qminorOp
  apply Finset.sum_eq_zero
  intro σ _
  rw [foldr_zero _ (fun T hT => by obtain ⟨i, rfl⟩ := List.mem_ofFn.1 hT; exact top_zero _ _ _)]
  funext g
  simp

/- English proof (translation)
Apply function extensionality and compare values at an arbitrary argument. Simplify using the standard rewrite rules. Reduce the claim to the hypotheses of an applicable result. Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities.

Simplify using the standard rewrite rules. Both sides reduce to the same expression. A detailed English derivation is pending.
-/
theorem AAop_zero (m : ℕ) (hm : m ≤ r) (u : ℂ) : C3.AAop k r m hm u (fun _ : B.Mat k r => (0 : E)) = fun _ => 0 := by
  funext g
  simp only [C3.AAop]
  apply Finset.sum_eq_zero
  intro c _
  split_ifs
  · rw [qminorOp_zero]; simp
  · rfl

/- English proof (translation)
Apply function extensionality and compare values at an arbitrary argument. Simplify using the standard rewrite rules. Reduce the claim to the hypotheses of an applicable result. Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities.

Simplify using the standard rewrite rules. Both sides reduce to the same expression. A detailed English derivation is pending.
-/
theorem AAvop_zero (m : ℕ) (hm : m ≤ r) (ell : ℂ) :
    C3.AAvop k r m hm ell (fun _ : B.Mat k r => (0 : E)) = fun _ => 0 := by
  funext g
  simp only [C3.AAvop]
  apply Finset.sum_eq_zero
  intro c _
  split_ifs
  · rw [qminorOp_zero]; simp
  · rfl

/- English proof (translation)
Apply function extensionality and compare values at an arbitrary argument. Simplify using the standard rewrite rules. Both sides reduce to the same expression. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules.

Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. A detailed English derivation is pending.
-/
theorem vLet_zero (z z' : Fin (2 * r + k + 1) → ℂ) (j : ℕ) (hj : j ≤ r) (l : C.Letter) (e : Fin 2) :
    D.vLet k r z z' j hj l e (fun _ : B.Mat k r => (0 : E)) = fun _ => 0 := by
  funext g
  simp only [D.vLet]
  split_ifs
  · rfl
  · rw [AAop_zero]; simp
  · rw [AAvop_zero]; simp

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem uwG_zero (z z' : Fin (2 * r + k + 1) → ℂ) (j : ℕ) (hj : j ≤ r) :
    ∀ (w : List C.Letter) (e : Wd.Ix (Fin w.length)),
      D.uwG k r z z' (fun _ : B.Mat k r => (0 : E)) j hj w e = fun _ => 0
  | [], _ => rfl
  | l :: w, e => by
    simp only [D.uwG]
    rw [uwG_zero z z' j hj w _]
    exact vLet_zero z z' j hj l _

end gloc

/- English proof (translation)
Replace the relevant objects with their definitions. A detailed English derivation is pending.
-/
theorem continuous_gN {k r : ℕ} : Continuous (fun g : B.Mat k r => B.gN g) := by
  unfold B.gN
  fun_prop

/- English proof (translation)
Extract witnesses or component facts from the available result. Introduce a local definition for the expression. Establish an intermediate fact. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses.

Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Assume the negation of the conclusion and derive a contradiction. Rewrite the conclusion using the stated equalities. Establish an intermediate fact.

Fix the arbitrary inputs or assume the hypotheses. Assume the negation of the conclusion and derive a contradiction. Establish an intermediate fact. Establish an intermediate fact. Fix the arbitrary inputs and assume any hypotheses. A detailed English derivation is pending.

Reduce the conclusion to the remaining proof obligations. Fix the arbitrary inputs or assume the hypotheses. Consider separately whether the proposition holds or fails. Establish an intermediate fact. Supply the required witnesses or components.

Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses.

A detailed English derivation is pending.
-/
theorem topCls_uwG {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] (Bs : B.RealPlaceData k r Wp Wq) (F : B.Mat k r → (Wq →L[ℂ] Wp))
    (hF : CutEX.TopCls Bs F) (w : List C.Letter) (e : Wd.Ix (Fin w.length)) :
    CutEX.TopCls Bs (D.uwG k r Bs.z Bs.z' F r le_rfl w e) := by
  obtain ⟨⟨hsm, ⟨R, hR⟩, ⟨ε, hε, hεG⟩⟩, ⟨K, hK, h0K, hDK⟩⟩ := hF
  let S : Set (B.Mat k r) := {x | x ∈ B.GV k r ∧ F x ≠ 0}
  have hDc : Continuous (fun x : B.Mat k r => Dmin k r Bs.z Bs.z' x ⟨r, by omega⟩) :=
    (Formalism.FourierDecayAlt.P.JCx1.contDiff_Dmin Bs.z Bs.z' _).continuous
  have hvan : ∀ x ∈ (closure S)ᶜ, x ∈ B.GV k r → D.uwG k r Bs.z Bs.z' F r le_rfl w e x = 0 := by
    intro x hx hxG
    have hz : ∀ y ∈ (closure S)ᶜ, y ∈ B.GV k r → F y = (fun _ => (0 : Wq →L[ℂ] Wp)) y := by
      intro y hy hyG
      by_contra hne
      exact hy (subset_closure ⟨hyG, hne⟩)
    rw [uwG_congrG Bs.z Bs.z' r le_rfl isClosed_closure.isOpen_compl hz w e x hx hxG, uwG_zero]
  have hcl : ∀ x, x ∈ B.GV k r → D.uwG k r Bs.z Bs.z' F r le_rfl w e x ≠ 0 → x ∈ closure S := by
    intro x hxG hne
    by_contra hx
    exact hne (hvan x hx hxG)
  have hDcl : ∀ x ∈ closure S, Dmin k r Bs.z Bs.z' x ⟨r, by omega⟩ ∈ K := by
    have hsub : S ⊆ (fun x => Dmin k r Bs.z Bs.z' x ⟨r, by omega⟩) ⁻¹' K := fun x hx => hDK x hx.1 hx.2
    exact fun x hx => closure_minimal hsub (hK.isClosed.preimage hDc) hx
  refine ⟨⟨?_, ⟨R, ?_⟩, ⟨ε, hε, ?_⟩⟩, ⟨K, hK, h0K, ?_⟩⟩
  · intro g₀ hg₀
    by_cases hD : Dmin k r Bs.z Bs.z' g₀ ⟨r, by omega⟩ = 0
    · have hg₀S : g₀ ∈ (closure S)ᶜ := fun h => h0K (hD ▸ hDcl g₀ h)
      exact ⟨(closure S)ᶜ, fun _ => 0, isClosed_closure.isOpen_compl, hg₀S, contDiffOn_const,
        fun x hx hxG => hvan x hx hxG⟩
    · exact PBG.uwG_mem Bs.z Bs.z' r le_rfl hsm w e g₀ hD hg₀
  · intro g hg hne
    have hsub : S ⊆ {x | B.gN x ≤ R} := fun x hx => hR x hx.1 hx.2
    exact closure_minimal hsub (isClosed_le continuous_gN continuous_const) (hcl g hg hne)
  · intro g hg hne
    have hsub : S ⊆ {x | ε ≤ Gf k r Bs.z Bs.z' x} := fun x hx => hεG x hx.1 hx.2
    exact closure_minimal hsub (isClosed_le continuous_const (Formalism.FourierDecayAlt.P.Ux8.cont_Gf _ _ _ _)) (hcl g hg hne)
  · intro g hg hne
    exact hDcl g (hcl g hg hne)

end Formalism.FourierDecayAlt.P.CutEXUw

namespace Formalism.FourierDecayAlt.P

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. A detailed English derivation is pending.
-/
theorem unipotent_weight_top : CutEX.UwTop := by
  intro Wp Wq _ _ _ _ _ _ P p F hF w e
  exact CutEXUw.topCls_uwG p.T.base F hF w e

end Formalism.FourierDecayAlt.P

import Mathlib
import Development.AbelianVarietyTheory.Definitions.PlaceAdaptation.AdaptStd
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.FormalGroupPointsOfIntegralChartSpecStatement

set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.PtTie
open ReciprocityTheory.ChartRestriction.G.TB (dAct dLin)
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.PlaceInt
namespace GlobalTheory.PlaceInt.FormKer

/- English proof (translation)
Apply function extensionality and compare values at an arbitrary argument. By extensionality, compare the relevant components. Extract witnesses or component facts from the available result. Simplify using the standard rewrite rules.
-/
lemma cpt_const {V : Type} [CommRing V] {d : ℕ} (x : Pt V 0 d) :
    (cpt (fun i => MvPowerSeries.constantCoeff (x i)) : Pt V 0 d) = x := by
  funext i
  ext m

  obtain rfl : m = 0 := Subsingleton.elim _ _
  simp [cpt]

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Proceed by induction. Treat this case separately. Simplify to obtain the desired conclusion from the available facts. Treat this case separately.

Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
lemma rel_prod {M P : Type*} [Monoid M] (R : M → P → Prop) (z : P) (s : P → P → P) (h1 : R 1 z)
    (hm : ∀ a a' x x', R a x → R a' x' → R (a * a') (s x x')) :
    ∀ (n : ℕ) (f : Fin n → M) (g : Fin n → P), (∀ j, R (f j) (g j)) →
      R (List.ofFn f).prod ((List.ofFn g).foldr s z) := by
  intro n
  induction n with
  | zero => intro f g _; simpa using h1
  | succ n ih =>
    intro f g hfg
    rw [List.ofFn_succ, List.ofFn_succ, List.prod_cons, List.foldr_cons]
    exact hm _ _ _ _ (hfg 0) (ih _ _ fun j => hfg j.succ)

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Establish an intermediate fact. Apply function extensionality and compare values at an arbitrary argument. Simplify using the standard rewrite rules.

Establish an intermediate fact. Assume the hypotheses and unpack their components. Supply the required witnesses or components. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses.

Establish an intermediate fact. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Apply function extensionality and compare values at an arbitrary argument. Establish an intermediate fact.

Simplify to obtain the desired conclusion from the available facts. Simplify using the standard rewrite rules. Prove the components needed by the constructor for the conclusion. Fix the arbitrary inputs or assume the hypotheses. Reduce the conclusion to the remaining proof obligations.

Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression. Assume the hypotheses and unpack their components.

Extract witnesses or component facts from the available result. Establish an intermediate fact. Substitute using the available equality. A detailed English derivation is pending.
-/
theorem kills_iff_mem_kerM : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) [StarRing (𝓞 E)], (∀ a : 𝓞 E, star a = H.bar a) → ∀ (T : CDVR) (io : c.F →+* T.Fr) (y : IntFr Xo c T io) (C : IntegralChartA3 Xo c T io y), ∀ B : FB T.V (chD C.ch) (𝓞 E), IsBT C B → ∀ (n : ℕ) (mu : Matrix (Fin n) (Fin n) (𝓞 E)) (a : Fin n → (ptO Xo (xOf y) ⟶ Xo.univ.t.G)) (α : Fin n → Fin (chD C.ch) → T.V), (∀ b, FormPt C (a b) (α b)) → (Kills Xo mu a ↔ α ∈ kerM B mu) := by
  intro E _ _ _ H Dw l Xo c _ hstar T io y C B hB n mu a α hα
  obtain ⟨h1, hinj, hmul, hact, -⟩ := GlobalTheory.T.formal_group_points_of_integral_chart_spec E H Dw l Xo c hstar T io y C B hB

  have h0 : (0 : Pt T.V 0 (chD C.ch)) = cpt 0 := by
    funext k
    simp [cpt]
  have hstep : ∀ (g g' : ptO Xo (xOf y) ⟶ Xo.univ.t.G) (x x' : Pt T.V 0 (chD C.ch)),
      (∃ δ, x = cpt δ ∧ FormPt C g δ) → (∃ δ, x' = cpt δ ∧ FormPt C g' δ) →
        ∃ δ, addV B.G.F x x' = cpt δ ∧ FormPt C (g * g') δ := by
    rintro g g' x x' ⟨al, rfl, hg⟩ ⟨al', rfl, hg'⟩
    exact ⟨_, (cpt_const _).symm, hmul g g' al al' _ hg hg' (cpt_const _)⟩
  have key : ∀ i, ∃ δ : Fin (chD C.ch) → T.V,
      matV B (m := 0) mu (fun j => cpt (α j)) i = cpt δ ∧
        FormPt C (List.ofFn fun j => a j ≫ Xo.univ.t.act.act (mu i j)).prod δ := by
    intro i
    have hrow : ∀ j, ∃ δ, compV (B.A.act (mu i j)) (cpt (α j)) = cpt δ ∧
        FormPt C (a j ≫ Xo.univ.t.act.act (mu i j)) δ := fun j =>
      ⟨_, (cpt_const _).symm, hact (a j) (α j) _ (mu i j) (hα j) (cpt_const _)⟩
    exact rel_prod (fun g x => ∃ δ, x = cpt δ ∧ FormPt C g δ) 0 (addV B.G.F) ⟨0, h0, h1⟩
      hstep n (fun j => a j ≫ Xo.univ.t.act.act (mu i j))
      (fun j => compV (B.A.act (mu i j)) (cpt (α j))) hrow
  have hcpt : ∀ δ : Fin (chD C.ch) → T.V, cpt (n := 0) δ = 0 → δ = 0 := by
    intro δ h
    funext k
    have := congrArg MvPowerSeries.constantCoeff (congrFun h k)
    simpa [cpt] using this
  simp only [Kills, kerM, Set.mem_ofPred_eq]
  constructor
  · intro hk
    refine ⟨fun b => (hα b).1, funext fun i => ?_⟩
    obtain ⟨δ, hm, hF⟩ := key i
    obtain rfl : δ = 0 := (hinj _ 1 δ 0 hF h1).mp (hk i)
    rw [hm, ← h0]
    rfl
  · rintro ⟨-, hz⟩ i
    obtain ⟨δ, hm, hF⟩ := key i
    have hδ : δ = 0 := hcpt δ (by rw [← hm]; exact congrFun hz i)
    subst hδ
    exact (hinj _ 1 0 0 hF h1).mpr rfl

end GlobalTheory.PlaceInt.FormKer

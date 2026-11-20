import Mathlib
import Development.AbelianVarietyTheory.Definitions.ThetaValues.ThConst
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ThExprUniqOfChartIndep2
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.CorrOfJetsOfAnalyticFrameProductsStatement
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.JetReadingLinearSubstitutionPointsStatement

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.AnVal.Sym

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.AnVal
open scoped ContDiff
attribute [local instance] Over.cartesianMonoidalCategory

/- English proof (translation)
Establish `hc : ContDiffAt ℂ ω (fun v : Fin g → ℂ => v k) 0` using `(contDiff_apply ℂ ℂ k).contDiffAt`. Use `TCPf.eq_of_cc _ _ fun l => ?_` and prove the remaining obligations. Break down `List.eq_nil_or_concat l with rfl | ⟨l', q, rfl⟩` into its components or cases. Simplify using `only [List.foldr_nil, constantCoeff_tay, MvPowerSeries.constantCoeff_X] show lD _ 0 (Multiset.toList 0) = 0`. Rewrite using `[Multiset.toList_zero]`.

Conclude with `iteratedFDeriv_zero_apply _`. Rewrite using `[List.concat_eq_append, List.foldr_append, List.foldr_append]`. Use `congr 2`. Take `⟨a, j⟩` from `q`. Take `rfl : a = 0` from `Subsingleton.elim _ _`.

Simplify using `only [List.foldr_cons, List.foldr_nil]`. Rewrite using `[TM.pderiv_tay hc]`. Establish `: (fun y : Fin g → ℂ => fderiv ℂ (fun v : Fin g → ℂ => v k) y (Pi.single j 1)) = fun _ => (Pi.single j (1 : ℂ) : Fin g → ℂ) k`. Use function extensionality and compare the values at `y`. Rewrite using `[(hasFDerivAt_apply (𝕜 := ℂ) k y).fderiv]`.

Both sides reduce to the same expression. Rewrite using `[this, TM.tay_const, MvPowerSeries.pderiv_X]`. Distinguish the cases in `h : k = j`. Substitute `h` using the available equality. Simplify using the standard rewrite rules.

Simplify using `[h, Pi.single_apply]`.
-/
theorem tay_coord {g : ℕ} (k : Fin g) :
    tay (fun v : Fin g → ℂ => v k) 0 = MvPowerSeries.X ((0 : Fin 1), k) := by
  have hc : ContDiffAt ℂ ω (fun v : Fin g → ℂ => v k) 0 := (contDiff_apply ℂ ℂ k).contDiffAt
  refine TCPf.eq_of_cc _ _ fun l => ?_
  rcases List.eq_nil_or_concat l with rfl | ⟨l', q, rfl⟩
  · simp only [List.foldr_nil, constantCoeff_tay, MvPowerSeries.constantCoeff_X]
    show lD _ 0 (Multiset.toList 0) = 0
    rw [Multiset.toList_zero]
    exact iteratedFDeriv_zero_apply _
  · rw [List.concat_eq_append, List.foldr_append, List.foldr_append]
    congr 2
    obtain ⟨a, j⟩ := q
    obtain rfl : a = 0 := Subsingleton.elim _ _
    simp only [List.foldr_cons, List.foldr_nil]
    rw [TM.pderiv_tay hc]
    have : (fun y : Fin g → ℂ => fderiv ℂ (fun v : Fin g → ℂ => v k) y (Pi.single j 1)) =
        fun _ => (Pi.single j (1 : ℂ) : Fin g → ℂ) k := by
      funext y
      rw [(hasFDerivAt_apply (𝕜 := ℂ) k y).fderiv]
      rfl
    rw [this, TM.tay_const, MvPowerSeries.pderiv_X]
    by_cases h : k = j
    · subst h; simp
    · simp [h, Pi.single_apply]

/- English proof (translation)
Rewrite using `[← MvPolynomial.coe_X, psJet, FBIdJet.psTrunc_eq, FBIdJet.mk_trunc_coe]`.
-/
theorem psJet_X {κ : Type} [Fintype κ] [DecidableEq κ] (m : ℕ) (s : κ) :
    psJet m (MvPowerSeries.X s : MvPowerSeries κ ℂ) = Ideal.Quotient.mk _ (MvPolynomial.X s) := by
  rw [← MvPolynomial.coe_X, psJet, FBIdJet.psTrunc_eq, FBIdJet.mk_trunc_coe]

/- English proof (translation)
Unfold `jetN jetOf`. Use `show renN n g m (psJet m (tay (fun v : Fin (n * g) → ℂ => v (finProdFinEquiv (i, j))) 0)) = _`. Rewrite using `[tay_coord, psJet_X]`. Use `show Ideal.Quotient.mk _ (MvPolynomial.aeval _ _) = _`. Rewrite using `[MvPolynomial.aeval_X, Equiv.symm_apply_apply]`.
-/
theorem jetN_coord {n g : ℕ} (m : ℕ) (i : Fin n) (j : Fin g) :
    jetN m (fun w : Fin n → Fin g → ℂ => w i j) = Ideal.Quotient.mk _ (MvPolynomial.X (i, j)) := by
  unfold jetN jetOf
  show renN n g m (psJet m (tay (fun v : Fin (n * g) → ℂ => v (finProdFinEquiv (i, j))) 0)) = _
  rw [tay_coord, psJet_X]
  show Ideal.Quotient.mk _ (MvPolynomial.aeval _ _) = _
  rw [MvPolynomial.aeval_X, Equiv.symm_apply_apply]

def swapL (g : ℕ) : (Fin 2 → Fin g → ℂ) →ₗ[ℂ] (Fin 2 → Fin g → ℂ) :=
  LinearMap.pi fun i => LinearMap.proj (Equiv.swap (0 : Fin 2) 1 i)

def swapI : ULift.{0} (Finset (Fin 2)) ≃ ULift.{0} (Finset (Fin 2)) :=
  Equiv.ulift.trans ((Equiv.finsetCongr (Equiv.swap (0 : Fin 2) 1)).trans Equiv.ulift.symm)

/- English proof (translation)
Use `LinearMap.ext fun w => ?_` and prove the remaining obligations. Simplify using `[psumL, swapL, swapI, Equiv.finsetCongr_apply]`.
-/
theorem psumL_swap (g : ℕ) (I : ULift.{0} (Finset (Fin 2))) :
    psumL 2 g I ∘ₗ swapL g = psumL 2 g (swapI I) := by
  refine LinearMap.ext fun w => ?_
  simp [psumL, swapL, swapI, Equiv.finsetCongr_apply]

/- English proof (translation)
Simplify using `[cε, swapI, Equiv.finsetCongr_apply]`.
-/
theorem cε_swap (I : ULift.{0} (Finset (Fin 2))) : cε 2 (swapI I) = cε 2 I := by
  simp [cε, swapI, Equiv.finsetCongr_apply]

/- English proof (translation)
Take `⟨_, rfl⟩` from `h`. Take `⟨_, rfl⟩` from `h'`. Both sides reduce to the same expression.
-/
theorem jetMap_unique {S : Scheme.{0}} {A : Over S} [GrpObj A] {L : RigLB A} {x0 : Sp ℂ ⟶ S} {g : ℕ}
    (Φ : AnFr A L x0 g) {n m : ℕ} {ψ ψ' : Sp (Jet ℂ (Fin n × Fin g) m) ⟶ A.left}
    {Λ : (Fin n → Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ)} (h : Φ.JetMap m ψ Λ) (h' : Φ.JetMap m ψ' Λ) : ψ = ψ' := by
  obtain ⟨_, rfl⟩ := h
  obtain ⟨_, rfl⟩ := h'
  rfl

/- English proof (translation)
Introduce `E _ _ _ H Dw l Xo c _ _ y g ty el Φ hI e he m`. Use `⟨1, ?_, ?_⟩` and prove the remaining obligations. Use `show (1 : Jet ℂ (Fin 2 × Fin g) m) = psJet m 1`. Rewrite using `[← MvPolynomial.coe_one, psJet, FBIdJet.psTrunc_eq, FBIdJet.mk_trunc_coe, map_one]`. Establish `hR` using `(he m).2`.

Establish `hS` using `GlobalTheory.T.jetReading_linearSubstitution_points _ Xo.univ.t.G Xo.univ.t.PP y.x g Φ.toAnFr 2 2 m (swapL g) (fun p : Fin 2 × Fin g => (![fun j => MvPolynomial.X ((1 : Fin 2), j), fun j => MvPolynomial.X ((0 : Fin 2), j)] : Fin 2 → Fin g → MvPolynomial (Fin 2 × Fin g) ℂ) p.1 p.2 …`. Introduce and unpack `⟨i, j⟩`. Rewrite using `[psJet_X]`. Use `Eq.trans ?_ (jetN_coord m (Equiv.swap (0 : Fin 2) 1 i) j).symm` and prove the remaining obligations. Use `show Ideal.Quotient.mk _ (MvPolynomial.aeval _ _) = _`.

Apply the tactic sequence `fin_cases i <;> simp) _ _ _ _ _ hR`. Establish `hC` using `GlobalTheory.T.corr_of_jets_of_analytic_frame_products _ Xo.univ.t.G Xo.univ.t.PP y.x g Φ.toAnFr hI 2 m _ _ _ _ _ _ _ _ _ _ hR hS (by`. Introduce `ψ`. Use `(Fintype.sum_equiv swapI _ _ fun I => ?_).symm` and prove the remaining obligations. Establish `h1` using `hS.1 I`.

Use `beta_reduce at h1 ⊢`. Rewrite `h1` using `[psumL_swap]`. Rewrite using `[jetMap_unique _ h1 (hR.1 (swapI I)), cε_swap])`. Introduce `j j' h1 h2 h3`. Use `(hC j j' h1 h2 h3).trans ?_` and prove the remaining obligations.

Use `congr 1`. Use `show _ = res le_top (unitΓ (1 : (Jet ℂ (Fin 2 × Fin g) m)ˣ)⁻¹) * _`. Rewrite using `[inv_one, unitΓ, map_one]`. Establish `: ∀ (X : Scheme.{0}) (U : X.Opens), res (le_top : U ≤ ⊤) (1 : Γ(X, ⊤)ˣ) = 1` using `fun X U => map_one _`. Rewrite using `[this]`.

Conclude with `(_root_.one_mul _).symm`.
-/
theorem sy_trivial : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) [Algebra c.F ℂ] [StarRing (𝓞 E)] (y : FrPt Xo c ℂ) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (el : Fin g ≃ Lt1 Dw) (Φ : AnPt y g ty el), Φ.toAnFr.Imm → ∀ e : ∀ m, FrTy y g Φ.jx m, Φ.IsAnE e → ∀ m, ∃ u : (Jet ℂ (Fin 2 × Fin g) m)ˣ, (u : Jet ℂ (Fin 2 × Fin g) m) = psJet m (anFB ty).sy ∧ LB.Gen.Corr Xo.univ.t.PP.L _ _ _ _ (e m) (scaleGen _ _ (unitΓ u⁻¹) (pe y g Φ.jx e m ![fun j => MvPolynomial.X ((1 : Fin 2), j), fun j => MvPolynomial.X ((0 : Fin 2), j)])) := by
  intro E _ _ _ H Dw l Xo c _ _ y g ty el Φ hI e he m
  refine ⟨1, ?_, ?_⟩
  · show (1 : Jet ℂ (Fin 2 × Fin g) m) = psJet m 1
    rw [← MvPolynomial.coe_one, psJet, FBIdJet.psTrunc_eq, FBIdJet.mk_trunc_coe, map_one]
  have hR := (he m).2
  have hS := GlobalTheory.T.jetReading_linearSubstitution_points _ Xo.univ.t.G Xo.univ.t.PP y.x g Φ.toAnFr 2 2 m (swapL g)
    (fun p : Fin 2 × Fin g => (![fun j => MvPolynomial.X ((1 : Fin 2), j), fun j => MvPolynomial.X ((0 : Fin 2), j)] :
      Fin 2 → Fin g → MvPolynomial (Fin 2 × Fin g) ℂ) p.1 p.2) (by
      rintro ⟨i, j⟩
      rw [psJet_X]
      refine Eq.trans ?_ (jetN_coord m (Equiv.swap (0 : Fin 2) 1 i) j).symm
      show Ideal.Quotient.mk _ (MvPolynomial.aeval _ _) = _
      fin_cases i <;> simp) _ _ _ _ _ hR
  have hC := GlobalTheory.T.corr_of_jets_of_analytic_frame_products _ Xo.univ.t.G Xo.univ.t.PP y.x g Φ.toAnFr hI 2 m _ _ _ _ _ _ _ _ _ _ hR hS (by
    intro ψ
    refine (Fintype.sum_equiv swapI _ _ fun I => ?_).symm
    have h1 := hS.1 I
    beta_reduce at h1 ⊢
    rw [psumL_swap] at h1
    rw [jetMap_unique _ h1 (hR.1 (swapI I)), cε_swap])
  intro j j' h1 h2 h3
  refine (hC j j' h1 h2 h3).trans ?_
  congr 1
  show _ = res le_top (unitΓ (1 : (Jet ℂ (Fin 2 × Fin g) m)ˣ)⁻¹) * _
  rw [inv_one, unitΓ, map_one]
  have : ∀ (X : Scheme.{0}) (U : X.Opens), res (le_top : U ≤ ⊤) (1 : Γ(X, ⊤)ˣ) = 1 := fun X U => map_one _
  rw [this]
  exact (_root_.one_mul _).symm

end GlobalTheory.AnVal.Sym

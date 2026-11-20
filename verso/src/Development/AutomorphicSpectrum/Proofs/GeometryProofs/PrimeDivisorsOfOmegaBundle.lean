import Mathlib
import Development.AutomorphicSpectrum.Statements.GeometryStatements.CmpPair
import Development.AutomorphicSpectrum.Statements.GeometryStatements.CmpSt
import Development.AutomorphicSpectrum.Statements.GeometryStatements.PadicIntegersHenselianFiniteResidue
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.SplitComps
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.Proportional
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.RootFundamentalWeightDuality
open MvPolynomial AlgebraicGeometry CategoryTheory NumberField Filter Topology ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cmp
open ReciprocityTheory.ChartRestriction.G.AI.I1 (IsBlockMap pullDeg)
open ReciprocityTheory.ChartRestriction.G.AI.I4 (IsPullHerm imageZ blockFnField)

namespace GlobalTheory.CompanionTheory.Ar.TieOfOrigin

/- English proof (translation)
Rewrite using `[Fintype.sum_prod_type, Finset.sum_eq_single a.1]`. Rewrite using `[← Finset.sum_neg_distrib, ← Finset.sum_subset (Finset.subset_univ (Finset.Iic a.2))]`. Use `Finset.sum_congr rfl fun k hk => ?_` and prove the remaining obligations. Simplify using `[fundOnRoot, Finset.mem_Iic.mp hk]`. Introduce `k _ hk`.

Establish `hk' : ¬ k ≤ a.2` using `fun h => hk (Finset.mem_Iic.mpr h)`. Simplify using `[fundOnRoot, hk']`. Introduce `τ _ hτ`. Simplify using `[fundOnRoot, hτ]`. Simplify using the standard rewrite rules.
-/
theorem sum_fundOnRoot {Ψ : Type} [Fintype Ψ] [DecidableEq Ψ] {N : ℕ} {G : Type} [AddCommGroup G]
    (f : Ψ × Fin N → G) (a : Ψ × Fin N) :
    ∑ r, fundOnRoot a r • f r = -∑ k ∈ Finset.Iic a.2, f (a.1, k) := by
  rw [Fintype.sum_prod_type, Finset.sum_eq_single a.1]
  · rw [← Finset.sum_neg_distrib, ← Finset.sum_subset (Finset.subset_univ (Finset.Iic a.2))]
    · refine Finset.sum_congr rfl fun k hk => ?_
      simp [fundOnRoot, Finset.mem_Iic.mp hk]
    · intro k _ hk
      have hk' : ¬ k ≤ a.2 := fun h => hk (Finset.mem_Iic.mpr h)
      simp [fundOnRoot, hk']
  · intro τ _ hτ
    simp [fundOnRoot, hτ]
  · simp

/- English proof (translation)
Use `show Real.log (∏ j, (ℓ j).h z ^ n j) = _`. Rewrite using `[Real.log_prod fun j _ => (zpow_pos ((ℓ j).pos z hz) _).ne']`. Simplify using `[Real.log_zpow]`.
-/
theorem log_combLine {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {J : Type} [Fintype J]
    (ℓ : J → HermLine ι) (n : J → ℤ) (z : (Σ k, ι k) → ℂ) (hz : ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) :
    Real.log ((Top.combLine ℓ n).h z) = ∑ j, n j • Real.log ((ℓ j).h z) := by
  show Real.log (∏ j, (ℓ j).h z ^ n j) = _
  rw [Real.log_prod fun j _ => (zpow_pos ((ℓ j).pos z hz) _).ne']
  simp [Real.log_zpow]

/- English proof (translation)
Establish `h1 : ∀ a, g a = ∑ r', fundOnRoot a r' • f r'` using `fun a => by rw [h, sum_fundOnRoot]`. Simplify using `only [h1, Finset.smul_sum, smul_smul]`. Rewrite using `[Finset.sum_comm]`. Simplify using `only [← Finset.sum_smul, (rootOnFund_mul_fundOnRoot_inverse Ψ N r _).1]`. Simplify using the standard rewrite rules.
-/
theorem sum_rootOnFund {Ψ : Type} [Fintype Ψ] [DecidableEq Ψ] {N : ℕ} (f g : Ψ × Fin N → ℝ)
    (h : ∀ a, g a = -∑ k ∈ Finset.Iic a.2, f (a.1, k)) (r : Ψ × Fin N) :
    ∑ a, rootOnFund r a • g a = f r := by
  have h1 : ∀ a, g a = ∑ r', fundOnRoot a r' • f r' := fun a => by rw [h, sum_fundOnRoot]
  simp only [h1, Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  simp only [← Finset.sum_smul, (rootOnFund_mul_fundOnRoot_inverse Ψ N r _).1]
  simp

end GlobalTheory.CompanionTheory.Ar.TieOfOrigin

open GlobalTheory.CompanionTheory.Ar.TieOfOrigin in
/- English proof (translation)
Introduce `E _ _ _ H D l Xo c O _ β Y S RM Sys Fx Or hvb hdiscr halg`. Use `⟨{ A := Or.𝔐, Fl := Or.Fl, e := Or.e, roots := Or.lines, sing := Or.sing, sing_deg := Or.sing_deg hodge := Or.hodge, Sy := Sys.comap some, Re := Or.Re.comap some, alg := halg ref_deg := ?_, sing_eq := ?_, line_eq := ?_, δ_eq := Or.δ_eq, discr := hdiscr ht_vb := fun p hp s => (hvb …` and prove the remaining obligations. Introduce and unpack `⟨τ, i⟩`. Use `(Or.fund_deg τ i).trans ?_` and prove the remaining obligations. Use `Eq.trans ?_ (@sum_fundOnRoot _ _ (_) _ _ _ (fun r => (Or.sing r).a) (τ, i)).symm` and prove the remaining obligations.

Simplify using `only [Or.sing_deg]`. Introduce and unpack `⟨τ, i⟩ x hx`. Establish `hz` using `(Or.Re.R.mem x x (Or.Re.R.mem_U x)).1`. Use `(log_combLine _ _ _ hz).trans ?_` and prove the remaining obligations. Use `(@sum_fundOnRoot _ _ (_) _ _ _ (fun r => Real.log ((Or.sing r).h (Or.Re.R.lift x x))) (τ, i)).trans ?_` and prove the remaining obligations.

Conclude with `(Or.fund_sing τ i x hx).symm`. Establish `h0 : 0 < Sys.t₀` using `(Sys.reg none).1 filter_upwards [Ioc_mem_nhdsGT h0] with t ht r z hz`. Use `Real.log_injOn_pos ((RM.x t r).pos z hz.1) (HermLine.pos _ z hz.1) ?_` and prove the remaining obligations. Use `Eq.trans ?_ (log_combLine _ _ _ hz.1).symm` and prove the remaining obligations. Conclude with `(@sum_rootOnFund _ _ (_) _ (fun r => Real.log ((RM.x t r).h z)) (fun a => Real.log ((Or.Re.line (some a) t).h z)) (fun a => Or.fund_reg a.1 a.2 t ht.1 ht.2 z hz) r).symm`.
-/
theorem GlobalTheory.CompanionTheory.Ar.hodgeTie_of_rootOrigin : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (S : Finset ℕ) (RM : Top.RootModel (CMType H) (D.p + D.q)) (Sys : PB.AnSys (Top.dimFl (CMType H) (D.p + D.q)) (Option (RootIx D))) (Fx : FixedData Y Sys) (Or : RootOrigin Y S RM Fx), Or.𝔐.OmVB → (∀ p : ℕ, p.Prime → (p : ℤ) ∣ NumberField.discr E → p ∈ S) → AlgOver (Or.Re.comap some) → ∃ T : HodgeTie Y S (Module.finrank ℚ c.F) RM, T.A = Or.𝔐 := by
  intro E _ _ _ H D l Xo c O _ β Y S RM Sys Fx Or hvb hdiscr halg
  refine ⟨{ A := Or.𝔐, Fl := Or.Fl, e := Or.e, roots := Or.lines, sing := Or.sing, sing_deg := Or.sing_deg
            hodge := Or.hodge, Sy := Sys.comap some, Re := Or.Re.comap some, alg := halg
            ref_deg := ?_, sing_eq := ?_, line_eq := ?_, δ_eq := Or.δ_eq, discr := hdiscr
            ht_vb := fun p hp s => (hvb p hp).2 s }, rfl⟩
  · rintro ⟨τ, i⟩
    refine (Or.fund_deg τ i).trans ?_
    refine Eq.trans ?_ (@sum_fundOnRoot _ _ (_) _ _ _ (fun r => (Or.sing r).a) (τ, i)).symm
    simp only [Or.sing_deg]
  · rintro ⟨τ, i⟩ x hx
    have hz := (Or.Re.R.mem x x (Or.Re.R.mem_U x)).1
    refine (log_combLine _ _ _ hz).trans ?_
    refine (@sum_fundOnRoot _ _ (_) _ _ _ (fun r => Real.log ((Or.sing r).h (Or.Re.R.lift x x))) (τ, i)).trans ?_
    exact (Or.fund_sing τ i x hx).symm
  · have h0 : 0 < Sys.t₀ := (Sys.reg none).1
    filter_upwards [Ioc_mem_nhdsGT h0] with t ht r z hz
    refine Real.log_injOn_pos ((RM.x t r).pos z hz.1) (HermLine.pos _ z hz.1) ?_
    refine Eq.trans ?_ (log_combLine _ _ _ hz.1).symm
    exact (@sum_rootOnFund _ _ (_) _ (fun r => Real.log ((RM.x t r).h z))
      (fun a => Real.log ((Or.Re.line (some a) t).h z))
      (fun a => Or.fund_reg a.1 a.2 t ht.1 ht.2 z hz) r).symm

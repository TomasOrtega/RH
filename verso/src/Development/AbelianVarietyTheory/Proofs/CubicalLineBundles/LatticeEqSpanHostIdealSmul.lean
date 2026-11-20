import Mathlib
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsRankOneCuspLatticeDataOfPrincipal
import Development.AbelianVarietyTheory.Definitions.CMLattices.IntegralOf
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.CmLieStatementsIffLibrary
import Formalism.LocalToGlobal.ProjectiveLattices.RosatiLatticeNorms.CmFrameOfEq
import Formalism.LocalToGlobal.ProjectiveLattices.HostInt
import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.FactPrincipalDatum

open CategoryTheory NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.MainNotions Formalism.BasicNotions Formalism.L2.LamCM
open GlobalTheory

namespace GlobalTheory

/- English proof (translation)
Establish `hA : 𝔄 ≠ 0`. Introduce and unpack `rfl`. Simplify using `at hone`. Use `le_antisymm (fun x hx => ?_) hle` and prove the remaining obligations. Establish `h1 : x ∈ traceFormDual X.ξ0 X.Gm ((𝔄 : Submodule (𝓞 E) E) • X.L')` using `fun y hy => X.EF_int x hx y (hle hy)`.

Rewrite `h1` using `[traceFormDual_eq X.ξ0_ne, hermDual_smul hA, hermDual_eq_self_iff.2 ⟨X.L'_int, X.L'_dual⟩, ← fractionalIdeal_mul_smul, ← mul_inv]`. Establish `h2 : 𝔄 = (FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 E)) X.ξ0 * (differentIdeal ℤ (𝓞 E) : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) * conjFrac 𝔄)⁻¹`. Use `eq_inv_of_mul_eq_one_left ?_` and prove the remaining obligations. Rewrite using `[← hone]`. Expand and normalize the polynomial expressions, which then agree.

Rewrite `h1` using `[← h2]`. Then use the resulting hypothesis.
-/
theorem dataX_lattice_eq_smul_of_le {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}
    (X : DataX E r) (𝔄 : FractionalIdeal (nonZeroDivisors (𝓞 E)) E)
    (hone : FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 E)) X.ξ0 * 𝔄 * conjFrac 𝔄 *
      (differentIdeal ℤ (𝓞 E) : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) = 1)
    (hle : (𝔄 : Submodule (𝓞 E) E) • X.L' ≤ X.Λ) :
    X.Λ = (𝔄 : Submodule (𝓞 E) E) • X.L' := by
  have hA : 𝔄 ≠ 0 := by
    rintro rfl
    simp at hone
  refine le_antisymm (fun x hx => ?_) hle
  have h1 : x ∈ traceFormDual X.ξ0 X.Gm ((𝔄 : Submodule (𝓞 E) E) • X.L') :=
    fun y hy => X.EF_int x hx y (hle hy)
  rw [traceFormDual_eq X.ξ0_ne, hermDual_smul hA, hermDual_eq_self_iff.2 ⟨X.L'_int, X.L'_dual⟩,
    ← fractionalIdeal_mul_smul, ← mul_inv] at h1
  have h2 : 𝔄 = (FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 E)) X.ξ0 *
      (differentIdeal ℤ (𝓞 E) : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) * conjFrac 𝔄)⁻¹ := by
    refine eq_inv_of_mul_eq_one_left ?_
    rw [← hone]; ring
  rwa [← h2] at h1

/- English proof (translation)
Introduce `D T h j hj k Xx hX hle`. Establish `hξ` using `GlobalTheory.eq_or_eq_neg_of_purelyImaginary_of_norm_eq _ D.host.xi0 ((T.U j T.σ₀).X k).ξ0 D.host.φ₀ (GlobalTheory.LatticeData.flagDomainConj_hostXi_eq_neg D) ((T.U j T.σ₀).X k).ξ0_im (h.xiAbs j hj _ T.good_σ₀ k _).symm`. Establish `hb : D.host.AAbar = conjFrac D.host.AA`. Use extensionality with `a`. Rewrite using `[mem_conjFrac, GlobalTheory.LatticeData.cc_eq_conj]`.

Conclude with `⟨conj_mem_AA D, fun ha => by simpa only [conj_conj] using conj_mem_AAbar D ha⟩`. Establish `hone : FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 D.host.E)) Xx.ξ0 * D.host.AA * conjFrac D.host.AA * (differentIdeal ℤ (𝓞 D.host.E) : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) = 1`. Establish `h1` using `Formalism.IndefR.Fin.factPrincipalDatum D.R D.host`. Rewrite using `[show Xx.ξ0 = ((T.U j T.σ₀).X k).ξ0 from congrArg _ hX, ← hb]`. Break down `hξ with e | e` into its components or cases.

Rewrite using `[e]`. Conclude with `h1`. Rewrite using `[e, show -D.host.xi0 = (-1 : (𝓞 D.host.E)ˣ) • D.host.xi0 by simp, ← (FractionalIdeal.spanSingleton_eq_spanSingleton.2 ⟨-1, rfl⟩)]`. Conclude with `h1`. Rewrite using `[← fractionalIdeal_smul_eq_span]`.

Conclude with `dataX_lattice_eq_smul_of_le Xx _ hone (Submodule.smul_le.2 hle)`.
-/
theorem lattice_eq_span_hostIdeal_smul : ∀ (D : D7) (T : Core D) (h : LawsCore T) (j : ℕ), InR D j → ∀ (k : (T.U j T.σ₀).Comp) (Xx : DataX D.host.E D.R.r), Xx.toData = (T.U j T.σ₀).X k → (∀ a ∈ D.host.AA, ∀ v ∈ Xx.L', a • v ∈ Xx.Λ) → Xx.Λ = Submodule.span (𝓞 D.host.E) {v | ∃ a ∈ D.host.AA, ∃ u ∈ Xx.L', v = a • u} := by
  intro D T h j hj k Xx hX hle
  have hξ := GlobalTheory.eq_or_eq_neg_of_purelyImaginary_of_norm_eq _ D.host.xi0 ((T.U j T.σ₀).X k).ξ0 D.host.φ₀
    (GlobalTheory.LatticeData.flagDomainConj_hostXi_eq_neg D) ((T.U j T.σ₀).X k).ξ0_im (h.xiAbs j hj _ T.good_σ₀ k _).symm
  have hb : D.host.AAbar = conjFrac D.host.AA := by
    ext a
    rw [mem_conjFrac, GlobalTheory.LatticeData.cc_eq_conj]
    exact ⟨conj_mem_AA D, fun ha => by simpa only [conj_conj] using conj_mem_AAbar D ha⟩
  have hone : FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 D.host.E)) Xx.ξ0 * D.host.AA *
      conjFrac D.host.AA *
      (differentIdeal ℤ (𝓞 D.host.E) : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) = 1 := by
    have h1 := Formalism.IndefR.Fin.factPrincipalDatum D.R D.host
    rw [show Xx.ξ0 = ((T.U j T.σ₀).X k).ξ0 from congrArg _ hX, ← hb]
    rcases hξ with e | e
    · rw [e]; exact h1
    · rw [e, show -D.host.xi0 = (-1 : (𝓞 D.host.E)ˣ) • D.host.xi0 by simp,
        ← (FractionalIdeal.spanSingleton_eq_spanSingleton.2 ⟨-1, rfl⟩)]
      exact h1
  rw [← fractionalIdeal_smul_eq_span]
  exact dataX_lattice_eq_smul_of_le Xx _ hone (Submodule.smul_le.2 hle)

end GlobalTheory

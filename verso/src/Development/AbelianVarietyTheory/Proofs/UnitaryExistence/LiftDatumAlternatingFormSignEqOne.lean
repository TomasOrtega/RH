import Mathlib
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.CoeSelfDualLatticeInFrameCoordinatesEq
import Formalism.LocalToGlobal.ProjectiveLattices.ParCanon
import Formalism.LocalToGlobal.ProjectiveLattices.ExistsParameterConditions
import Formalism.LocalToGlobal.ProjectiveLattices.ValSetAlgSubset
import Formalism.LocalToGlobal.ProjectiveLattices.IntAll
import Formalism.LocalToGlobal.ProjectiveLattices.AllTest
import Formalism.LocalToGlobal.ProjectiveLattices.VolProofs
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.NegIndexTransposeOfHasSignature

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj
open scoped TensorProduct Matrix Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Member

namespace GlobalTheory.Member

/- English proof (translation)
Establish `h1` using `xi0_embedding_im_pos D D.host.φ₀ ((mem_cm_type_iff D _).2 rfl)`. Establish `hφ : D.host.φ₀ D.host.sqrtMinusD = Complex.I * (Real.sqrt D.host.d : ℂ)` using `D.host.φ₀_mem`. Establish `hpos : 0 < (D.host.φ₀ D.host.sqrtMinusD).im`. Rewrite using `[hφ]`. Establish `hd : (0 : ℝ) < D.host.d` using `by exact_mod_cast d_pos D`.

Simplify using `using hd`. Rewrite `h1` using `[if_pos hpos, Int.cast_one, _root_.one_mul]`. Rewrite using `[map_neg, Complex.neg_im]`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem neg_baseElement_im_neg_baseEmbedding (D : D7) : (D.host.φ₀ (-D.host.xi0)).im < 0 := by
  have h1 := xi0_embedding_im_pos D D.host.φ₀ ((mem_cm_type_iff D _).2 rfl)
  have hφ : D.host.φ₀ D.host.sqrtMinusD = Complex.I * (Real.sqrt D.host.d : ℂ) := D.host.φ₀_mem
  have hpos : 0 < (D.host.φ₀ D.host.sqrtMinusD).im := by
    rw [hφ]
    have hd : (0 : ℝ) < D.host.d := by exact_mod_cast d_pos D
    simpa using hd
  rw [if_pos hpos, Int.cast_one, _root_.one_mul] at h1
  rw [map_neg, Complex.neg_im]
  linarith

/- English proof (translation)
Introduce `D H Dw j hj hrt hrt0 hp _ φ ε hinj hspan0 hEF`. Establish `hr` using `D.sp.W_rank j hj.1 hj.2`. Set `f` to `((D.sp.W j).frame.equivFun.restrictScalars (𝓞 D.host.E)).toLinearMap`. Establish `hio : Function.Injective (f ∘ₗ φ)` using `(D.sp.W j).frame.equivFun.injective.comp hinj`. Establish `hdet` using `(GlobalTheory.RecDict.posIndex_gmW (D.sp.W j) (D.sp.W_sig j) hr D.host.φ₀).2`.

Establish `hherm` using `GlobalTheory.RecDict.cc_gmW (D.sp.W j) hr`. Establish `hspan : Submodule.span D.host.E (Set.range (f ∘ₗ φ)) = ⊤`. Establish `: Set.range (f ∘ₗ φ) = (D.sp.W j).frame.equivFun.toLinearMap '' Set.range φ`. Rewrite using `[← Set.range_comp]`. Both sides reduce to the same expression.

Rewrite using `[this, Submodule.span_image, hspan0, Submodule.map_top, LinearEquiv.range]`. Break down `Int.units_eq_one_or ε with h | h` into its components or cases. Conclude with `h`. It suffices to derive a contradiction. Substitute `h` using the available equality.

Set `c : (Fin (D.sp.W j).rank → D.host.E) ≃ₗ[D.host.E] (Fin D.R.r → D.host.E)` to `LinearEquiv.funCongrLeft D.host.E D.host.E (finCongr hr.symm)`. Set `ψ : Dw.La →ₗ[𝓞 D.host.E] (Fin D.R.r → D.host.E)` to `(c.restrictScalars (𝓞 D.host.E)).toLinearMap ∘ₗ f ∘ₗ φ`. Establish `hψ : ∀ x, ψ x = (D.sp.W j).frame.equivFun (φ x) ∘ Fin.cast hr.symm` using `fun _ => rfl`. Establish `hτ : D.host.φ₀ (H.rt : D.host.E) = H.rt0` using `by rw [hrt, hrt0]`. Establish `hξ : cc (-D.host.xi0) = -(-D.host.xi0)`.

Rewrite using `[cc, map_neg, conj_xi0_alt]`. Establish `hsp : Submodule.span D.host.E (Set.range ψ) = ⊤`. Establish `: Set.range ψ = c.toLinearMap '' Set.range (f ∘ₗ φ)`. Rewrite using `[← Set.range_comp]`. Both sides reduce to the same expression.

Rewrite using `[this, Submodule.span_image, hspan, Submodule.map_top, LinearEquiv.range]`. Take `⟨P, hP, hPg⟩` from `(GlobalTheory.HermSign.signature_of_model D.host.E H Dw D.R.r (-D.host.xi0) _ ψ hξ ⟨c.injective.comp hio, hsp, hherm, hdet, fun x y => by`. Rewrite using `[hEF, hψ, hψ, neg_mul, map_neg, GlobalTheory.RecDict.trace_herm_gmW]`. Use the proof step `simp⟩ D.host.φ₀ hτ).2 (neg_baseElement_im_neg_baseEmbedding D)`. Establish `hm` using `D.R.m_add_three_le_k`.

Establish `h1` using `hj.1`. Establish `h2` using `hj.2`. Establish `hle : Dw.p ≤ D.R.r`. Rewrite using `[hp]`. Simplify using `only [Ranks.sigW, Ranks.r]`.

Use linear arithmetic over natural numbers and integers. Establish `h3` using `(GlobalTheory.Inertia.gram_eq_sgn_iff D.host.φ₀ hherm hdet _).1 ⟨hle, P, hP, hPg⟩`. Rewrite `h3` using `[(GlobalTheory.RecDict.posIndex_gmW (D.sp.W j) (D.sp.W_sig j) hr D.host.φ₀).1, D.sp.W_sigval j hj.1 hj.2, hp]`. Simplify using `only [Ranks.sigW] at h3`. Use linear arithmetic over natural numbers and integers.
-/
theorem sign_eq_one : ∀ (D : D7) (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E) (Dw : Datum H) (j : ℕ), InR D j → (H.rt : D.host.E) = D.host.sqrtMinusD → H.rt0 = D.host.φ₀ D.host.sqrtMinusD → Dw.p = (D.R.sigW j).1 → Dw.q = (D.R.sigW j).2 → ∀ (φ : Dw.La →ₗ[𝓞 D.host.E] (D.sp.W j).V) (ε : ℤˣ), Function.Injective φ → Submodule.span D.host.E (Set.range φ) = ⊤ → (∀ x y, ((Dw.EF x y : ℤ) : ℚ) = ((ε : ℤ) : ℚ) * Algebra.trace ℚ D.host.E (D.host.xi0 * (D.sp.W j).hT (φ x) (φ y))) → ε = 1 := by
  intro D H Dw j hj hrt hrt0 hp _ φ ε hinj hspan0 hEF
  have hr := D.sp.W_rank j hj.1 hj.2
  let f := ((D.sp.W j).frame.equivFun.restrictScalars (𝓞 D.host.E)).toLinearMap
  have hio : Function.Injective (f ∘ₗ φ) := (D.sp.W j).frame.equivFun.injective.comp hinj
  have hdet := (GlobalTheory.RecDict.posIndex_gmW (D.sp.W j) (D.sp.W_sig j) hr D.host.φ₀).2
  have hherm := GlobalTheory.RecDict.cc_gmW (D.sp.W j) hr
  have hspan : Submodule.span D.host.E (Set.range (f ∘ₗ φ)) = ⊤ := by
    have : Set.range (f ∘ₗ φ) = (D.sp.W j).frame.equivFun.toLinearMap '' Set.range φ := by
      rw [← Set.range_comp]
      rfl
    rw [this, Submodule.span_image, hspan0, Submodule.map_top, LinearEquiv.range]
  rcases Int.units_eq_one_or ε with h | h
  · exact h
  exfalso
  subst h
  let c : (Fin (D.sp.W j).rank → D.host.E) ≃ₗ[D.host.E] (Fin D.R.r → D.host.E) :=
    LinearEquiv.funCongrLeft D.host.E D.host.E (finCongr hr.symm)
  let ψ : Dw.La →ₗ[𝓞 D.host.E] (Fin D.R.r → D.host.E) :=
    (c.restrictScalars (𝓞 D.host.E)).toLinearMap ∘ₗ f ∘ₗ φ
  have hψ : ∀ x, ψ x = (D.sp.W j).frame.equivFun (φ x) ∘ Fin.cast hr.symm := fun _ => rfl
  have hτ : D.host.φ₀ (H.rt : D.host.E) = H.rt0 := by rw [hrt, hrt0]
  have hξ : cc (-D.host.xi0) = -(-D.host.xi0) := by
    rw [cc, map_neg, conj_xi0_alt]
  have hsp : Submodule.span D.host.E (Set.range ψ) = ⊤ := by
    have : Set.range ψ = c.toLinearMap '' Set.range (f ∘ₗ φ) := by
      rw [← Set.range_comp]
      rfl
    rw [this, Submodule.span_image, hspan, Submodule.map_top, LinearEquiv.range]
  obtain ⟨P, hP, hPg⟩ := (GlobalTheory.HermSign.signature_of_model D.host.E H Dw D.R.r (-D.host.xi0)
    _ ψ hξ ⟨c.injective.comp hio, hsp, hherm, hdet, fun x y => by
      rw [hEF, hψ, hψ, neg_mul, map_neg, GlobalTheory.RecDict.trace_herm_gmW]
      simp⟩ D.host.φ₀ hτ).2 (neg_baseElement_im_neg_baseEmbedding D)
  have hm := D.R.m_add_three_le_k
  have h1 := hj.1
  have h2 := hj.2
  have hle : Dw.p ≤ D.R.r := by
    rw [hp]
    simp only [Ranks.sigW, Ranks.r]
    omega
  have h3 := (GlobalTheory.Inertia.gram_eq_sgn_iff D.host.φ₀ hherm hdet _).1 ⟨hle, P, hP, hPg⟩
  rw [(GlobalTheory.RecDict.posIndex_gmW (D.sp.W j) (D.sp.W_sig j) hr D.host.φ₀).1, D.sp.W_sigval j hj.1 hj.2, hp] at h3
  simp only [Ranks.sigW] at h3
  omega

end GlobalTheory.Member

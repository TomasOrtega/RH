import Mathlib
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.FormPlus
import Formalism.LocalToGlobal.ProjectiveLattices.ThShort
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ComponentAttainedAtBaseFrame
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.NegIndexTransposeOfHasSignature
open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Semi
open scoped TensorProduct
open GlobalTheory.ShortMove

namespace GlobalTheory.ShortMove

open GlobalTheory.RecDict

attribute [local instance] Formalism.BasicNotions.Host.cmStar

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Introduce a local definition for the expression. Extract witnesses or component facts from the available result. Rewrite the indicated hypotheses using the stated equalities.

Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact.

Rewrite the indicated hypotheses using the stated equalities. Establish an intermediate fact. Establish an intermediate fact. Reduce the claim to the hypotheses of an applicable result. Take a linear combination of the given relations to obtain the conclusion.

Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression. Extract witnesses or component facts from the available result.

Extract witnesses or component facts from the available result. Supply the required witnesses or components. Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. Assume the hypotheses and unpack their components.

Extract witnesses or component facts from the available result. Supply the required witnesses or components. Assume the hypotheses and unpack their components. Supply the required witnesses or components. Extract witnesses or component facts from the available result.

Supply the required witnesses or components. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Use the resulting assumption. Extract witnesses or component facts from the available result. Establish an intermediate fact.

Rewrite the conclusion using the stated equalities. By extensionality, compare the relevant components. Simplify using the standard rewrite rules. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities.

Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem exists_adelic_of_isometry : ∀ (D : D7) (V : HSp D) (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E) (Dw : Datum H) (io : Dw.La →ₗ[𝓞 D.host.E] (Fin V.rank → D.host.E)), LatEmb V io → FormPlus V io → ∀ s : Sim Dw, (∀ n, s.ν n = 1) → ∃ κ : GA D V, latGHat V κ = latGHat V 1 ∧ ∀ N : ℕ, 0 < N → ∀ a, ∃ w ∈ latGHat V 1, (finHom V κ).1.mulVec (finVec V (io a)) = finVec V (io (s.f N a)) + N • w := by
  intro D V H Dw io hio hEF s hν
  obtain ⟨hinj, hrange⟩ := hio
  let c : D.host.E ≃ₐ[D.host.F] D.host.E :=
    AlgEquiv.ofAlgHom D.sp.cm.sig D.sp.cm.sig (AlgHom.ext fun x => star_star x) (AlgHom.ext fun x => star_star x)
  obtain ⟨hfg, hsp, hlat⟩ := comp_latG D V
  rw [← hrange] at hfg hsp hlat
  have hξ : D.host.xi0 ≠ 0 := by
    have h1 : (Ideal.absNorm D.host.ccK : D.host.E) ≠ 0 := by
      exact_mod_cast (Ideal.absNorm_eq_zero_iff.not.2 D.host.ccK_ne_bot)
    have h2 : D.host.sqrtMinusD ≠ 0 := by
      intro h
      have := D.host.sqrtMinusD_sq
      rw [h] at this
      have hd : (D.host.d : D.host.E) ≠ 0 := by
        have := D.host.qd_big.2
        exact_mod_cast (by omega : D.host.d ≠ 0)
      apply hd
      linear_combination this
    exact div_ne_zero (by norm_num) (mul_ne_zero h1 h2)
  have hA : ∀ x y, ((Dw.EF x y : ℤ) : ℚ) = Algebra.trace ℚ D.host.E (D.host.xi0 *
      ∑ a, ∑ b, io x a * (-V.gram.transpose) a b * c (io y b)) := by
    intro x y
    rw [hEF, ← trace_herm_gmW V rfl, LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]
    rfl
  obtain ⟨gf, hg1, hg2, hg3⟩ := comp_adelic_of_tower D.host.F D.host.E V.rank c (-V.gram.transpose)
    D.host.xi0 hξ Dw.La Dw.La (fun x y => Dw.EF x y) (fun x y => Dw.EF x y) io hinj
    (LinearMap.range io) (LinearEquiv.ofInjective io hinj) hfg hsp hfg hsp hA hA s.f
    (fun n m hn hm a => by
      obtain ⟨e, he⟩ := s.tower n m hn hm a
      exact ⟨e, by rw [← he, add_sub_cancel]⟩)
    (fun n hn => by
      obtain ⟨g, hg⟩ := s.inv n hn
      refine ⟨fun a => ⟨?_, ?_⟩, fun a' => ?_⟩
      · rintro ⟨e, he⟩
        obtain ⟨b, hb⟩ := (hg a).1
        exact ⟨g e - b, by rw [smul_sub, ← hb, he, map_nsmul, sub_sub_cancel]⟩
      · rintro ⟨e, he⟩
        exact ⟨s.f n e, by rw [he, map_nsmul]⟩
      · obtain ⟨b, hb⟩ := (hg a').2
        exact ⟨g a', -b, by rw [smul_neg, ← hb, neg_sub, add_sub_cancel]⟩)
    (fun n hn a a' => by
      have := s.mult n hn a a'
      rwa [hν, one_mul] at this)
  obtain ⟨u, -, hug⟩ := (GlobalTheory.T.adelicUnitary_exists_with_prescribed_parts D V).1 gf (comp_mem_HR _ _ _ c _ (fun _ => rfl) _ gf hg3)
  have h1 : (latGHat V 1 : Set (Fin V.rank → AdLat.RA D.host.F D.host.E)) =
      AdLat.hat D.host.F (LinearMap.range io : Set (Fin V.rank → D.host.E)) := by
    rw [(hlat 1).2, map_one, Units.val_one]
    ext z
    simp
  refine ⟨u, SetLike.coe_injective ?_, fun N hN a => ?_⟩
  · rw [(hlat u).2, hug, hg1, h1]
  · obtain ⟨w, hw, hgw⟩ := hg2 N hN a
    refine ⟨w, ?_, ?_⟩
    · rw [← SetLike.mem_coe, h1]
      exact hw
    · rw [hug]
      exact hgw

end GlobalTheory.ShortMove

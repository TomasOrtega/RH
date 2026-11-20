import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SuperDiagEqSdM
open NumberField IsDedekindDomain GlobalTheory.CuspRep Matrix MeasureTheory GlobalTheory.WhitBump
open scoped ContDiff

namespace GlobalTheory.WhitBump

/- English proof (translation)
Introduce `E _ _ _ n u _ hk`. Establish `hent` using `((GroundTheory.Automorphic.AdelicGLn.mem_integralFiniteGL_iff E n).1 hk).1`. Establish `hs : GlobalTheory.Whittaker.superDiag u ∈ GroundTheory.Global.integralFiniteAdeles (𝓞 E) E`. Unfold `GlobalTheory.Whittaker.superDiag`. Conclude with `Subring.sum_mem _ fun i _ => Subring.sum_mem _ fun j _ => hent i j`.

Establish `hd : sFin E (GlobalTheory.Whittaker.superDiag u) ∈ GroundTheory.Global.invDifferentAdeles E` using `GroundTheory.Global.mem_invDifferentAdeles.mpr (GroundTheory.Global.mem_finiteInvDifferent_of_mem_integralFiniteAdeles hs)`. Unfold `psiFin`. Rewrite using `[GroundTheory.Global.adelicChar_of_mem_invDifferentAdeles hd]`. Establish `h0 : (sFin E (GlobalTheory.Whittaker.superDiag u)).1 = 0` using `rfl`. Rewrite using `[h0, map_zero, neg_zero, AddChar.map_zero_eq_one]`.

Simplify using the standard rewrite rules.
-/
theorem psiFin_superDiag_eq_one_of_integral : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (n : ℕ)
    (u : GL (Fin n) (Af E)), u ∈ GlobalTheory.SmGL.unipB (Af E) (Fin n) →
    u ∈ GroundTheory.Automorphic.AdelicGLn.integralFiniteGL E n → psiFin (GlobalTheory.Whittaker.superDiag u) = 1 := by
  intro E _ _ _ n u _ hk
  have hent := ((GroundTheory.Automorphic.AdelicGLn.mem_integralFiniteGL_iff E n).1 hk).1
  have hs : GlobalTheory.Whittaker.superDiag u ∈ GroundTheory.Global.integralFiniteAdeles (𝓞 E) E := by
    unfold GlobalTheory.Whittaker.superDiag
    exact Subring.sum_mem _ fun i _ => Subring.sum_mem _ fun j _ => hent i j
  have hd : sFin E (GlobalTheory.Whittaker.superDiag u) ∈ GroundTheory.Global.invDifferentAdeles E :=
    GroundTheory.Global.mem_invDifferentAdeles.mpr
      (GroundTheory.Global.mem_finiteInvDifferent_of_mem_integralFiniteAdeles hs)
  unfold psiFin
  rw [GroundTheory.Global.adelicChar_of_mem_invDifferentAdeles hd]
  have h0 : (sFin E (GlobalTheory.Whittaker.superDiag u)).1 = 0 := rfl
  rw [h0, map_zero, neg_zero, AddChar.map_zero_eq_one]
  simp

end GlobalTheory.WhitBump

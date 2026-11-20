import Formalism.SharpRestriction.GlobalSchurBounds.JointsL
import Formalism.LocalRingCardinality.DataErr
import Formalism.LocalToGlobal.HermitianColumns.ClsNonempty

noncomputable section

namespace Formalism.L2.GlobalTheoryTheory

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory Formalism.FrobeniusOrbits NumberField

/- English proof (translation)
Establish `hg : H.galE (H.sigmaOf (g : R.GG)) = g` using `(H.gal).apply_symm_apply _`. Establish `hb : H.sigmaOf (g : R.GG) (H.sqd) = H.sqd` using `(H.toHostAx.galE_mem_Psi_iff _).1 (by rw [hg]; exact g.2)`. Proceed by induction on `hx using IntermediateField.adjoin_induction with`. Consider the case `mem y hy => rw [Set.mem_singleton_iff.1 hy]`. Conclude with `hb`.

Consider the case `algebraMap r => exact AlgEquiv.commutes _ r`. Consider the case `add y z _ _ hy hz => rw [map_add, hy, hz]`. Consider the case `inv y _ hy => rw [map_inv₀, hy]`. Consider the case `mul y z _ _ hy hz => rw [map_mul, hy, hz]`.
-/
theorem sigma_fix_K {R : Ranks} (H : Host R) (g : R.Psi) {x : H.E} (hx : x ∈ H.K) :
    H.sigmaOf (g : R.GG) x = x := by
  have hg : H.galE (H.sigmaOf (g : R.GG)) = g :=
    (H.gal).apply_symm_apply _
  have hb : H.sigmaOf (g : R.GG) (H.sqd) = H.sqd :=
    (H.toHostAx.galE_mem_Psi_iff _).1 (by rw [hg]; exact g.2)
  induction hx using IntermediateField.adjoin_induction with
  | mem y hy => rw [Set.mem_singleton_iff.1 hy]; exact hb
  | algebraMap r => exact AlgEquiv.commutes _ r
  | add y z _ _ hy hz => rw [map_add, hy, hz]
  | inv y _ hy => rw [map_inv₀, hy]
  | mul y z _ _ hy hz => rw [map_mul, hy, hz]

/- English proof (translation)
Unfold `tauLL`. Rewrite using `[sigma_fix_K D.host (D.eTau τ) hx]`.
-/
theorem tauLL_of_K (D : D7) (τ : D.what₂.Tau) {x : D.host.E} (hx : x ∈ D.host.K) : tauLL D τ x = D.embE x := by
  unfold tauLL
  rw [sigma_fix_K D.host (D.eTau τ) hx]

def AdmBRest (D : D7) (u : D.what₂.Word) (π : 𝓞 D.host.E) : Prop :=
  letI := D.host.cmStar
  ∀ i, i ≤ D.R.m →
    ∃ (co : (D.sp.X i).V ≃ₗ[D.host.E] (Fin (D.R.N i) → D.host.E)) (L0 : SDLat D.host.E (D.R.N i)),
      (∀ x y, stdH D.host.E (D.R.N i) (co x) (co y) = (D.sp.X i).hT x y) ∧
      (∀ y, co y ∈ L0.1 ↔ y ∈ (D.sp.X i).L0) ∧
      ∀ c : (D.mem u).C.cls i, ∃ Ln : SDLat D.host.E (D.R.N i),
        (∀ y, co y ∈ Ln.1 ↔ ∃ a ∈ D.clsLat u i c, ∃ b ∈ Formalism.HermitianLatticesTheory.dual (D.sp.X i).hT (D.clsLat u i c),
          y = a + D.host.conj (π : D.host.E) • b) ∧
        (QuotientGroup.mk (D.detCls u i c) : D.Dt ⧸ D.UO) = D.relDet (D.R.N i) L0 Ln

/- English proof (translation)
Use `⟨X.piT u, X.piT_K u, X.piT_norm u, fun w hw => ?_, h⟩` and prove the remaining obligations. Rewrite using `[hs u w hw]`. Prove the components needed by the constructor for the conclusion. Introduce `h1`. Use `h1 (D.eTau.symm 1)` as an intermediate fact.

Rewrite `this` using `[tauLL_of_K D _ (X.piT_K u)]`. Then use the resulting hypothesis. Introduce `h1 τ`. Rewrite using `[tauLL_of_K D _ (X.piT_K u)]` and apply the resulting hypothesis.
-/
theorem base_lattice_convention_of_flags {D : D7} (X : ErrX D) (hs : SeenDef D X) (u : D.what₂.Word)
    (h : AdmBRest D u (X.piT u)) : product_first_zeroth_parts.admB D u := by
  refine ⟨X.piT u, X.piT_K u, X.piT_norm u, fun w hw => ?_, h⟩
  rw [hs u w hw]
  constructor
  · intro h1
    have := h1 (D.eTau.symm 1)
    rwa [tauLL_of_K D _ (X.piT_K u)] at this
  · intro h1 τ
    rwa [tauLL_of_K D _ (X.piT_K u)]

end Formalism.L2.GlobalTheoryTheory

end

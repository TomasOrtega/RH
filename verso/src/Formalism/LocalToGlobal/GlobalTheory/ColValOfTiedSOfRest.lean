import Formalism.LocalToGlobal.GlobalTheory.ClassesLevelZeroNonempty

noncomputable section

open NumberField Matrix

namespace Formalism.L2.GlobalTheoryTheory.ColValS

open Formalism.BasicNotions Formalism.MainNotions.GlobalTheoryTheory.Inhab

attribute [local instance] Formalism.BasicNotions.Host.cmStar

/- English proof (translation)
Use `conv_lhs => rw [← b.sum_repr y]`. Simplify using `only [map_sum, LinearMap.map_smulₛₗ, LinearMap.sum_apply, LinearMap.smul_apply, map_smul, hb, smul_eq_mul, starRingEnd_apply]`. Simplify using `[mul_ite, Finset.sum_ite_eq]`. Conclude with `Finset.sum_congr rfl fun _ _ => mul_comm _ _`.
-/
theorem hT_self_of_on {E : Type} [Field E] [NumberField E] [StarRing E] (S : HSpace E)
    (b : Module.Basis (Fin S.rank) E S.V) (hb : ∀ a a', S.hT (b a) (b a') = if a = a' then 1 else 0) (y : S.V) :
    S.hT y y = ∑ a, star (b.repr y a) * b.repr y a := by
  conv_lhs => rw [← b.sum_repr y]
  simp only [map_sum, LinearMap.map_smulₛₗ, LinearMap.sum_apply, LinearMap.smul_apply, map_smul, hb,
    smul_eq_mul, starRingEnd_apply]
  simp [mul_ite, Finset.sum_ite_eq]
  exact Finset.sum_congr rfl fun _ _ => mul_comm _ _

/- English proof (translation)
Take `⟨b, hb, -⟩` from `h`. Introduce `σ`. Use `⟨(b.toMatrix (D.sp.X 0).frame).map σ, ?_, ?_⟩` and prove the remaining obligations. Use `haveI := b.invertibleToMatrix (D.sp.X 0).frame`. Establish `hu : IsUnit (σ (b.toMatrix (D.sp.X 0).frame).det)` using `(Matrix.isUnit_det_of_invertible _).map σ`.

Rewrite `hu` using `[RingHom.map_det, RingHom.mapMatrix_apply]`. Then use the resulting hypothesis. Introduce `y`. Establish `hrepr : ∀ i, ((b.toMatrix (D.sp.X 0).frame).map σ *ᵥ fun j => σ ((D.sp.X 0).frame.repr y j)) i = σ (b.repr y i)`. Introduce `i`. Rewrite using `[← (D.sp.X 0).frame.toMatrix_mulVec_repr b y, RingHom.map_mulVec]`.

Both sides reduce to the same expression. Simplify using `only [hrepr]`. Rewrite using `[hT_self_of_on (D.sp.X 0) b hb y, map_sum, Complex.re_sum]`. Use `Finset.sum_congr rfl fun a _ => ?_` and prove the remaining obligations. Rewrite using `[map_mul, host_emb_star, Complex.conj_mul', ← Complex.ofReal_pow, Complex.ofReal_re]`.
-/
theorem posFrame_of_std (D : D7) (h : Formalism.L2.Herm.IsStd (D.sp.X 0)) : PosFrame D := by
  obtain ⟨b, hb, -⟩ := h
  intro σ
  refine ⟨(b.toMatrix (D.sp.X 0).frame).map σ, ?_, ?_⟩
  · haveI := b.invertibleToMatrix (D.sp.X 0).frame
    have hu : IsUnit (σ (b.toMatrix (D.sp.X 0).frame).det) :=
      (Matrix.isUnit_det_of_invertible _).map σ
    rwa [RingHom.map_det, RingHom.mapMatrix_apply] at hu
  · intro y
    have hrepr : ∀ i, ((b.toMatrix (D.sp.X 0).frame).map σ *ᵥ
        fun j => σ ((D.sp.X 0).frame.repr y j)) i = σ (b.repr y i) := by
      intro i
      rw [← (D.sp.X 0).frame.toMatrix_mulVec_repr b y, RingHom.map_mulVec]
      rfl
    simp only [hrepr]
    rw [hT_self_of_on (D.sp.X 0) b hb y, map_sum, Complex.re_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [map_mul, host_emb_star, Complex.conj_mul', ← Complex.ofReal_pow, Complex.ofReal_re]

/- English proof (translation)
The claim follows from `ColBase_exists D u (posFrame_of_std D (F.herm.std.1 0 (Nat.zero_le _))) rho`.
-/
theorem colBase_of_sym {D : D7} (F : Formalism.L2.Forms.ColsTiedSym D) (u : D.what₂.Word)
    (rho : D.what₂.Tau → (D.host.E →+* D.what₂.LL)) : ∃ B : ColBase D u, B.rho = rho :=
  ColBase_exists D u (posFrame_of_std D (F.herm.std.1 0 (Nat.zero_le _))) rho

/- English proof (translation)
Use `colValOfTiedS_of_rest fun D F ha u => ?_` and prove the remaining obligations. Take `⟨rho, hr⟩` from `h D F ha u`. Take `⟨B, hB⟩` from `colBase_of_sym F u rho`. Conclude with `⟨B, hr B hB⟩`.
-/
theorem colValOfTiedS_of_rest'
    (h : ∀ D : D7, Formalism.L2.Forms.ColsTiedSym D → Formalism.MainNotions.flipTwoThree.adm3 D → ∀ u : D.what₂.Word,
      ∃ rho : D.what₂.Tau → (D.host.E →+* D.what₂.LL), ∀ B : ColBase D u, B.rho = rho → ColRest B) :
    Formalism.MainNotions.RT.ColumnValuationFromTwistCompatibility := by
  refine colValOfTiedS_of_rest fun D F ha u => ?_
  obtain ⟨rho, hr⟩ := h D F ha u
  obtain ⟨B, hB⟩ := colBase_of_sym F u rho
  exact ⟨B, hr B hB⟩

end Formalism.L2.GlobalTheoryTheory.ColValS

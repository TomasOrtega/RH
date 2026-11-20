import Mathlib
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.StepTwoFiltSt
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.QuotTransSt
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.StepTwoPieceSt
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial

noncomputable section

universe u v w

/- English proof (translation)
Establish `h2 : Subsingleton (Cech.Cochain G i)`. Unfold `Cech.Cochain`. Use `infer_instance`. Unfold `Cech.H`. Use `Submodule.Quotient.subsingleton_iff.mpr (eq_top_iff.mpr fun z _ => ?_)` and prove the remaining obligations.

Establish `hz : z = 0` using `Subtype.ext (h2.elim _ _)`. Rewrite using `[hz]`. Conclude with `Submodule.zero_mem _`.
-/
theorem Cech.H_subsingleton {n : ℕ} {U : Finset (Fin n)} {R : Type u} [CommRing R] {G : Cell U → Type v}
    [∀ I, AddCommGroup (G I)] [∀ I, Module R (G I)] (ρ : ∀ I J : Cell U, I.1 ⊆ J.1 → G I →ₗ[R] G J)
    (h : ∀ I, Subsingleton (G I)) (i : ℕ) : Subsingleton (Cech.H G ρ i) := by
  have h2 : Subsingleton (Cech.Cochain G i) := by
    unfold Cech.Cochain; infer_instance
  unfold Cech.H
  refine Submodule.Quotient.subsingleton_iff.mpr (eq_top_iff.mpr fun z _ => ?_)
  have hz : z = 0 := Subtype.ext (h2.elim _ _)
  rw [hz]
  exact Submodule.zero_mem _

section Helpers

variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N : ℕ}
  {x : Fin (N + 1) → Ω} {E : Type v} [AddCommGroup E] [Module Ω E] [Module S E]
  [IsScalarTower S Ω E]

omit [IsScalarTower S Ω E] in

/- English proof (translation)
Use `Submodule.span_mono ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨q, hq, y, hy, rfl⟩`. Use `⟨q, hq, y, ?_, rfl⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `y ∈ M'.tilde 0 I`. Express the relevant statement in the definitionally equal form `y ∈ M.tilde 0 I at hy`.

Use `Submodule.span_mono ?_ hy` and prove the remaining obligations. Introduce and unpack `_ ⟨m, s, a, e, hs, hse, hm, hae, rfl⟩`. Conclude with `⟨m, s, a, e, hs, hse, h a hm, hae, rfl⟩`.
-/
theorem tildeSys_twist_mono {M M' : FinGradedSub (S := S) (x := x) E} (h : ∀ c, M.piece c ≤ M'.piece c)
    (Q : SubSystem S x Ω) (I : Chart x) :
    ((M.tildeSys 0).twist Q).sub I ≤ ((M'.tildeSys 0).twist Q).sub I := by
  refine Submodule.span_mono ?_
  rintro _ ⟨q, hq, y, hy, rfl⟩
  refine ⟨q, hq, y, ?_, rfl⟩
  change y ∈ M'.tilde 0 I
  change y ∈ M.tilde 0 I at hy
  refine Submodule.span_mono ?_ hy
  rintro _ ⟨m, s, a, e, hs, hse, hm, hae, rfl⟩
  exact ⟨m, s, a, e, hs, hse, h a hm, hae, rfl⟩

/- English proof (translation)
Establish `h1 : ∀ I, Subsingleton (F.sub I ⧸ SubSystem.quotSub F F I)` using `fun I => Submodule.Quotient.subsingleton_iff.mpr (eq_top_iff.mpr fun y _ => y.2)`. Unfold `SubSystem.quotH`. Conclude with `Cech.H_subsingleton _ h1 i`.
-/
theorem quotH_self_subsingleton (F : SubSystem S x E) (i : ℕ) :
    Subsingleton (SubSystem.quotH F F i) := by
  have h1 : ∀ I, Subsingleton (F.sub I ⧸ SubSystem.quotSub F F I) := fun I =>
    Submodule.Quotient.subsingleton_iff.mpr (eq_top_iff.mpr fun y _ => y.2)
  unfold SubSystem.quotH
  exact Cech.H_subsingleton _ h1 i

end Helpers

/- English proof (translation)
Introduce `S _ _ Ω _ _ N x E _ _ _ _ M₁ M₂ h21 J hJ`. Take `⟨n, Nf, g, deg, pr, h0, hlast, hk⟩` from `hF S Ω N x E M₁ M₂ h21 J hJ`. Use `⟨n, pr, fun i => -deg i, fun i => ⟨(hk i).1, (hk i).2.1, (hk i).2.2.1, (hk i).2.2.2.1⟩, ?_⟩` and prove the remaining obligations. Introduce `Q c hQ`. Establish `key : ∀ (m : ℕ) (hm : m < n + 1), (∀ a, (Nf 0).piece a ≤ (Nf ⟨m, hm⟩).piece a) ∧ Subsingleton (SubSystem.quotH (((Nf ⟨m, hm⟩).tildeSys 0).twist (Q.twist (twistSys S x c))) (((Nf 0).tildeSys 0).twist (Q.twist (twistSys S x c))) 1)`.

Introduce `m`. Proceed by induction on `m with`. Consider the case `zero => intro _`. Conclude with `⟨fun _ => le_rfl, quotH_self_subsingleton _ 1⟩`. Consider the case `succ m ih`.

Introduce `hm`. Take `⟨ih1, ih2⟩` from `ih (by omega)`. Take `⟨hpr, hhom, hprx, -, hg, hsup, hann⟩` from `hk ⟨m, by omega⟩`. Establish `hstep` using `hP S Ω N x E _ _ (g ⟨m, by omega⟩) (deg ⟨m, by omega⟩) (pr ⟨m, by omega⟩) hpr hhom hprx hg hsup hann Q c (fun hrel => by rw [sub_eq_add_neg]; exact hQ ⟨m, by omega⟩ hrel)`. Establish `hle : ∀ a, (Nf ⟨m, by omega⟩).piece a ≤ (Nf ⟨m + 1, hm⟩).piece a` using `fun a => by`.

Rewrite using `[show (⟨m + 1, hm⟩ : Fin (n + 1)) = Fin.succ ⟨m, by omega⟩ from rfl, hsup a]`. Conclude with `le_sup_left`. Conclude with `⟨fun a => (ih1 a).trans (hle a), hT S Ω N x E _ _ _ (tildeSys_twist_mono ih1 _) (tildeSys_twist_mono hle _) ih2 hstep⟩`. Take `⟨-, h⟩` from `key n (Nat.lt_succ_self n)`. Rewrite `h` using `[show (⟨n, Nat.lt_succ_self n⟩ : Fin (n + 1)) = Fin.last n from rfl, hlast, h0]`.

Conclude with `h`.
-/
theorem StepTwo.Reduce.proof (hF : StepTwo.Filt.Statement.{u, v, w}) (hT : QuotTrans.Statement.{u, v, w})
    (hP : StepTwo.Piece.Statement.{u, v, w}) : StepTwo.Reduce.Statement.{u, v, w} := by
  intro S _ _ Ω _ _ N x E _ _ _ _ M₁ M₂ h21 J hJ
  obtain ⟨n, Nf, g, deg, pr, h0, hlast, hk⟩ := hF S Ω N x E M₁ M₂ h21 J hJ
  refine ⟨n, pr, fun i => -deg i, fun i => ⟨(hk i).1, (hk i).2.1, (hk i).2.2.1, (hk i).2.2.2.1⟩, ?_⟩
  intro Q c hQ
  have key : ∀ (m : ℕ) (hm : m < n + 1), (∀ a, (Nf 0).piece a ≤ (Nf ⟨m, hm⟩).piece a) ∧
      Subsingleton (SubSystem.quotH (((Nf ⟨m, hm⟩).tildeSys 0).twist (Q.twist (twistSys S x c)))
        (((Nf 0).tildeSys 0).twist (Q.twist (twistSys S x c))) 1) := by
    intro m
    induction m with
    | zero => intro _; exact ⟨fun _ => le_rfl, quotH_self_subsingleton _ 1⟩
    | succ m ih =>
      intro hm
      obtain ⟨ih1, ih2⟩ := ih (by omega)
      obtain ⟨hpr, hhom, hprx, -, hg, hsup, hann⟩ := hk ⟨m, by omega⟩
      have hstep := hP S Ω N x E _ _ (g ⟨m, by omega⟩) (deg ⟨m, by omega⟩) (pr ⟨m, by omega⟩) hpr hhom
        hprx hg hsup hann Q c (fun hrel => by rw [sub_eq_add_neg]; exact hQ ⟨m, by omega⟩ hrel)
      have hle : ∀ a, (Nf ⟨m, by omega⟩).piece a ≤ (Nf ⟨m + 1, hm⟩).piece a := fun a => by
        rw [show (⟨m + 1, hm⟩ : Fin (n + 1)) = Fin.succ ⟨m, by omega⟩ from rfl, hsup a]
        exact le_sup_left
      exact ⟨fun a => (ih1 a).trans (hle a), hT S Ω N x E _ _ _ (tildeSys_twist_mono ih1 _)
        (tildeSys_twist_mono hle _) ih2 hstep⟩
  obtain ⟨-, h⟩ := key n (Nat.lt_succ_self n)
  rw [show (⟨n, Nat.lt_succ_self n⟩ : Fin (n + 1)) = Fin.last n from rfl, hlast, h0] at h
  exact h

end

end GroundTheory.Heights₂.Heights.Kleiman

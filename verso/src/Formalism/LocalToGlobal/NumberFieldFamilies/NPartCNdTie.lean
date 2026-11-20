import Formalism.LocalToGlobal.NumberFieldFamilies.GamCSpec

noncomputable section

open Formalism.BasicNotions NumberField IsDedekindDomain Module Module.End Formalism.ConjugateSelfDual ReciprocityTheory.Gal

namespace Formalism.L2.Fam.NPC

set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 400000

section Gen

variable {R : Ranks} {H : Host R} {what₂ : Rows.Data R} (B : LocBase0 H what₂)

def bjC (hI : OsInt B) (i : LocT B) (g : (what₂.MjLat (jOf B i)).gen) : BjC B hI i :=
  (bjRel B hI i).mkQ (Pi.basisFun (OOf B i) _ g)

/- English proof (translation)
Establish `e : ∑ g, c g • Pi.basisFun (OOf B i) _ g = c`. Simplify using `using (Pi.basisFun (OOf B i) ((what₂.MjLat (jOf B i)).gen)).sum_repr c`. Simplify using `only [bjC, ← map_smul, ← map_sum, e]`. Both sides reduce to the same expression.
-/
theorem bjC_sum (hI : OsInt B) (i : LocT B) (c : (what₂.MjLat (jOf B i)).gen → OOf B i) :
    ∑ g, c g • bjC B hI i g = Submodule.Quotient.mk c := by
  have e : ∑ g, c g • Pi.basisFun (OOf B i) _ g = c := by
    simpa using (Pi.basisFun (OOf B i) ((what₂.MjLat (jOf B i)).gen)).sum_repr c
  simp only [bjC, ← map_smul, ← map_sum, e]
  rfl

/- English proof (translation)
Rewrite using `[eq_top_iff]`. Introduce and unpack `x -`. Proceed by induction on `x using Submodule.Quotient.induction_on with`. Consider the case `H c`. Rewrite using `[← bjC_sum]`.

Conclude with `Submodule.sum_mem _ (fun g _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨g, rfl⟩))`.
-/
theorem bjC_span (hI : OsInt B) (i : LocT B) :
    Submodule.span (OOf B i) (Set.range (bjC B hI i)) = ⊤ := by
  rw [eq_top_iff]
  rintro x -
  induction x using Submodule.Quotient.induction_on with
  | H c =>
    rw [← bjC_sum]
    exact Submodule.sum_mem _ (fun g _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨g, rfl⟩))

/- English proof (translation)
Rewrite using `[bjC_sum, Submodule.Quotient.mk_eq_zero]`. Both sides reduce to the same expression.
-/
theorem bjC_rel (hI : OsInt B) (i : LocT B) (c : (what₂.MjLat (jOf B i)).gen → OOf B i) :
    ∑ g, c g • bjC B hI i g = 0 ↔
      c ∈ Submodule.span (OOf B i) ((fun r => (sOfC B hI i) ∘ r) '' Formalism.L2.latRel (what₂.MjLat (jOf B i))) := by
  rw [bjC_sum, Submodule.Quotient.mk_eq_zero]
  rfl

def idealAt {j : ℕ} {w : what₂.places.Pl} (p : ℕ × what₂.places.Pl) (hp : p = (j, w))
    (I : Ideal (heckeAlg0 B p.1 p.2)) : Ideal (heckeAlg0 B j w) := by
  subst hp; exact I

def mxC (j : ℕ) (w : what₂.places.Pl) (i : LocT B) : Ideal (heckeAlg0 B j w) := by
  classical
  exact if h : i.1 = (j, w) then idealAt B i.1 h i.2.1 else ⊥

/- English proof (translation)
Unfold `mxC`. Conclude with `(dif_pos (rfl : i.1 = (jOf B i, wOf B i))).trans rfl`.
-/
theorem mxC_self (i : LocT B) : mxC B (jOf B i) (wOf B i) i = i.2.1 := by
  unfold mxC
  exact (dif_pos (rfl : i.1 = (jOf B i, wOf B i))).trans rfl

/- English proof (translation)
Rewrite using `[mxC_self]`. Conclude with `i.2.2.1`.
-/
theorem mxC_max (i : LocT B) : (mxC B (jOf B i) (wOf B i) i).IsMaximal := by
  rw [mxC_self]; exact i.2.2.1

/- English proof (translation)
Introduce and unpack `⟨⟨j1, w1⟩, I1⟩ h1 ⟨⟨j2, w2⟩, I2⟩ h2 he`. Establish `h1'` using `(locsC_mem B hF j w _).1 (Finset.mem_coe.1 h1)`. Establish `h2'` using `(locsC_mem B hF j w _).1 (Finset.mem_coe.1 h2)`. Simplify using `only [jOf, wOf] at h1' h2'`. Take `⟨rfl, rfl⟩` from `h1'`.

Take `⟨rfl, rfl⟩` from `h2'`. Establish `e1` using `mxC_self B ⟨(_, _), I1⟩`. Establish `e2` using `mxC_self B ⟨(_, _), I2⟩`. Simplify using `only [jOf, wOf] at e1 e2 he`. Rewrite `he` using `[e1, e2]`.

Conclude with `Sigma.ext rfl (heq_of_eq (Subtype.ext he))`.
-/
theorem mxC_inj (hF : LocsFin B) (j : ℕ) (w : what₂.places.Pl) : Set.InjOn (mxC B j w) (locsC B hF j w) := by
  rintro ⟨⟨j1, w1⟩, I1⟩ h1 ⟨⟨j2, w2⟩, I2⟩ h2 he
  have h1' := (locsC_mem B hF j w _).1 (Finset.mem_coe.1 h1)
  have h2' := (locsC_mem B hF j w _).1 (Finset.mem_coe.1 h2)
  simp only [jOf, wOf] at h1' h2'
  obtain ⟨rfl, rfl⟩ := h1'
  obtain ⟨rfl, rfl⟩ := h2'
  have e1 := mxC_self B ⟨(_, _), I1⟩
  have e2 := mxC_self B ⟨(_, _), I2⟩
  simp only [jOf, wOf] at e1 e2 he
  rw [e1, e2] at he
  exact Sigma.ext rfl (heq_of_eq (Subtype.ext he))

/- English proof (translation)
Assemble the required witnesses or components as `⟨⟨(j, w), ⟨I, hI, h1, h2, hw⟩⟩, (locsC_mem B hF j w _).2 ⟨rfl, rfl⟩, mxC_self B ⟨(j, w), ⟨I, hI, h1, h2, hw⟩⟩⟩`.
-/
theorem mxC_all (hF : LocsFin B) (j : ℕ) (w : what₂.places.Pl) (h1 : 1 ≤ j) (h2 : j ≤ R.m) (hw : what₂.muAt w ≠ what₂.mu0)
    (I : Ideal (heckeAlg0 B j w)) (hI : I.IsMaximal) : ∃ i ∈ locsC B hF j w, mxC B j w i = I :=
  ⟨⟨(j, w), ⟨I, hI, h1, h2, hw⟩⟩, (locsC_mem B hF j w _).2 ⟨rfl, rfl⟩, mxC_self B ⟨(j, w), ⟨I, hI, h1, h2, hw⟩⟩⟩

def PsiC (hC : PartCompl B) (hL : MtLoc B hC) (i : LocT B) :
    TensorProduct (OOf B i) (FractionRing (OOf B i)) (MtSub B hC i) →ₗ[FractionRing (OOf B i)] B.V (jOf B i) (wOf B i) :=
  (partOf B i).subtype.comp (mtEquiv B hC hL i).toLinearMap

/- English proof (translation)
The claim follows from `(Submodule.injective_subtype _).comp (mtEquiv B hC hL i).injective`.
-/
theorem PsiC_inj (hC : PartCompl B) (hL : MtLoc B hC) (i : LocT B) : Function.Injective (PsiC B hC hL i) :=
  (Submodule.injective_subtype _).comp (mtEquiv B hC hL i).injective

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `hy`. Conclude with `⟨(mtEquiv B hC hL i).symm ⟨y, hy⟩, by simp [PsiC]⟩`. Introduce and unpack `⟨z, rfl⟩`. Conclude with `((mtEquiv B hC hL i) z).2`.
-/
theorem PsiC_range (hC : PartCompl B) (hL : MtLoc B hC) (i : LocT B) (y : B.V (jOf B i) (wOf B i)) :
    y ∈ NCov.part (hAlg B i) i.2.1 ↔ ∃ z, PsiC B hC hL i z = y := by
  constructor
  · intro hy
    exact ⟨(mtEquiv B hC hL i).symm ⟨y, hy⟩, by simp [PsiC]⟩
  · rintro ⟨z, rfl⟩
    exact ((mtEquiv B hC hL i) z).2

/- English proof (translation)
Establish `e : PsiC B hC hL i (prMtC B hC hL i x) = (projOf B hC i (B.iV (jOf B i) (wOf B i) x) : B.V (jOf B i) (wOf B i))`. Simplify using `[PsiC, prMtC]`. Rewrite using `[e]`. Use `show _ ∈ offOf B i`. Rewrite using `[← Submodule.linearProjOfIsCompl_ker (hC i), LinearMap.mem_ker, map_sub]`.

Simplify using `only [projOf, Submodule.linearProjOfIsCompl_apply_left]`. Conclude with `sub_eq_zero.2 rfl`.
-/
theorem PsiC_pr (hC : PartCompl B) (hL : MtLoc B hC) (i : LocT B) (x : what₂.MtL (what₂.muTw (wOf B i)) (jOf B i)) :
    PsiC B hC hL i (prMtC B hC hL i x) - B.iV (jOf B i) (wOf B i) x ∈ NCov.off (hAlg B i) i.2.1 := by
  have e : PsiC B hC hL i (prMtC B hC hL i x) = (projOf B hC i (B.iV (jOf B i) (wOf B i) x) : B.V (jOf B i) (wOf B i)) := by
    simp [PsiC, prMtC]
  rw [e]
  show _ ∈ offOf B i
  rw [← Submodule.linearProjOfIsCompl_ker (hC i), LinearMap.mem_ker, map_sub]
  simp only [projOf, Submodule.linearProjOfIsCompl_apply_left]
  exact sub_eq_zero.2 rfl

/- English proof (translation)
Simplify using `[hTOf, hTfun, dif_pos hvk]`.
-/
theorem ptX_val (i : LocT B) (v : HeightOneSpectrum (𝓞 H.E)) (k : ℕ) (hvk : GenAt0 H (lOf B i) (B.Qw (wOf B i)) v k)
    (x : XOf B i) : (hTOf B i v k : XOf B i → OOf B i) x = x.1 ⟨B.hK (jOf B i) (wOf B i) v k, Algebra.subset_adjoin ⟨v, k, hvk, rfl⟩⟩ := by
  simp [hTOf, hTfun, dif_pos hvk]

end Gen

end Formalism.L2.Fam.NPC

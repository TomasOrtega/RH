import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.AutomorphicRepresentations.EvalBasis
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaCellCovers.KernelDiagonalIntegrableHolds
import Development.DiscreteGroups.PiInvariants.CompactSupportTwists.PiInvTop
import Development.DiscreteGroups.PiInvariants.CompactSupportTwists.PiVecExHolds
import Development.DiscreteGroups.PiInvariants.CompactSupportTwists.PiSeenA

open UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi DiscreteGroups.T1.G

noncomputable section

open NumberField MeasureTheory GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.Desc

attribute [local instance] PositivityTheory.Rg.BcB.E.borelH

namespace UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi

section SlopeTestRemainingChoices

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ} {D : Dom E n 0} {ι : Type}

/- English proof (translation)
Both sides reduce to the same expression.
-/
private lemma vecM_apply (v : Lp ℂ 2 D.ν) (c : ι → ℂ) (l : ι) : vecM v c l = c l • v := rfl

/- English proof (translation)
Use `ext1 l`. Simplify using `[vecM_apply]`.
-/
private lemma vecM_zero (c : ι → ℂ) : vecM (0 : Lp ℂ 2 D.ν) c = 0 := by
  ext1 l
  simp [vecM_apply]

/- English proof (translation)
Use `ext1 l`. Simplify using `[vecM_apply, smul_add]`.
-/
private lemma vecM_add (a b : Lp ℂ 2 D.ν) (c : ι → ℂ) : vecM (a + b) c = vecM a c + vecM b c := by
  ext1 l
  simp [vecM_apply, smul_add]

/- English proof (translation)
Use `ext1 l`. Simplify using `[vecM_apply, smul_sub]`.
-/
private lemma vecM_sub (a b : Lp ℂ 2 D.ν) (c : ι → ℂ) : vecM (a - b) c = vecM a c - vecM b c := by
  ext1 l
  simp [vecM_apply, smul_sub]

/- English proof (translation)
Use `ext1 l`. Simplify using `[vecM_apply, smul_comm r]`.
-/
private lemma vecM_smul (r : ℂ) (a : Lp ℂ 2 D.ν) (c : ι → ℂ) : vecM (r • a) c = r • vecM a c := by
  ext1 l
  simp [vecM_apply, smul_comm r]

/- English proof (translation)
Use `ext1 l`. Simplify using `[vecM_apply]`.
-/
private lemma vecM_unit (f : Hs (ι := Unit) D) : vecM (f ()) (fun _ : Unit => 1) = f := by
  ext1 l
  simp [vecM_apply]

/- English proof (translation)
The claim follows from `(PiLp.continuous_toLp 2 _).comp (continuous_pi fun l => (continuous_const_smul (c l)).comp (PiLp.continuous_apply 2 _ ()))`.
-/
private lemma continuous_vecM [Fintype ι] (c : ι → ℂ) :
    Continuous fun f : Hs (ι := Unit) D => (vecM (f ()) c : Hs (ι := ι) D) :=
  (PiLp.continuous_toLp 2 _).comp
    (continuous_pi fun l => (continuous_const_smul (c l)).comp (PiLp.continuous_apply 2 _ ()))

/- English proof (translation)
Introduce `l`. Take `⟨ψ, hψ, u, hu, hc, he⟩` from `hf ()`. Use `⟨c l • ψ, π.V.smul_mem _ hψ, u, hu, hc, ?_⟩` and prove the remaining obligations. Establish `h1` using `Lp.coeFn_smul (c l) (f ())`. Use `filter_upwards [h1, he] with x h1 h2`.

Rewrite using `[vecM_apply, h1, Pi.smul_apply, h2]`. Simplify using `[mul_assoc]`.
-/
private lemma isPiVec_vecM (π : CuspSub E n) {f : Hs (ι := Unit) D} (hf : IsPiVec D π f) (c : ι → ℂ) :
    IsPiVec D π (vecM (f ()) c : Hs (ι := ι) D) := by
  intro l
  obtain ⟨ψ, hψ, u, hu, hc, he⟩ := hf ()
  refine ⟨c l • ψ, π.V.smul_mem _ hψ, u, hu, hc, ?_⟩
  have h1 := Lp.coeFn_smul (c l) (f ())
  filter_upwards [h1, he] with x h1 h2
  rw [vecM_apply, h1, Pi.smul_apply, h2]
  simp [mul_assoc]

/- English proof (translation)
Introduce `_`. Take `⟨ψ, hψ, u, hu, hc, he⟩` from `hg l`. Use `⟨ψ, hψ, u, hu, hc, ?_⟩` and prove the remaining obligations. Simplify `he` using `[vecM_apply]`.
-/
private lemma isPiVec_comp (π : CuspSub E n) {g : Hs (ι := ι) D} (hg : IsPiVec D π g) (l : ι) :
    IsPiVec D π (vecM (g l) (fun _ : Unit => 1) : Hs (ι := Unit) D) := by
  intro _
  obtain ⟨ψ, hψ, u, hu, hc, he⟩ := hg l
  refine ⟨ψ, hψ, u, hu, hc, ?_⟩
  simpa [vecM_apply] using he

/- English proof (translation)
Establish `hspan : ∀ f ∈ Submodule.span ℂ {f : Hs (ι` using `Unit) D | IsPiVec D π f}, (vecM (f ()) c : Hs (ι := ι) D) ∈ Submodule.span ℂ {f : Hs (ι := ι) D | IsPiVec D π f} := by`. Introduce `f hf`. Proceed by induction on `hf using Submodule.span_induction with`. Consider the case `mem x hx => exact Submodule.subset_span (isPiVec_vecM π hx c)`. Consider the case `zero => simpa [vecM_zero] using Submodule.zero_mem _`.

Consider the case `add x y _ _ hx hy`. Establish `: (x + y) () = x () + y ()` using `rfl`. Rewrite using `[this, vecM_add]`. Conclude with `Submodule.add_mem _ hx hy`. Consider the case `smul r x _ hx`.

Establish `: (r • x) () = r • x ()` using `rfl`. Rewrite using `[this, vecM_smul]`. Conclude with `Submodule.smul_mem _ _ hx`. Establish `hf' : f ∈ closure (Submodule.span ℂ {f : Hs (ι` using `Unit) D | IsPiVec D π f} : Set (Hs (ι := Unit) D)) := hf`. Establish `: (vecM (f ()) c : Hs (ι` using `ι) D) ∈ closure (Submodule.span ℂ {f : Hs (ι := ι) D | IsPiVec D π f} : Set (Hs (ι := ι) D)) := map_mem_closure (f := fun f : Hs (ι := Unit) D => (vecM (f ()) c : Hs (ι := ι) D)) (continuous_vecM c) hf' hspan`.

Conclude with `this`.
-/
private lemma vecM_mem [Fintype ι] (π : CuspSub E n) (c : ι → ℂ) {f : Hs (ι := Unit) D}
    (hf : f ∈ piSp D π Unit) : (vecM (f ()) c : Hs (ι := ι) D) ∈ piSp D π ι := by
  have hspan : ∀ f ∈ Submodule.span ℂ {f : Hs (ι := Unit) D | IsPiVec D π f},
      (vecM (f ()) c : Hs (ι := ι) D) ∈ Submodule.span ℂ {f : Hs (ι := ι) D | IsPiVec D π f} := by
    intro f hf
    induction hf using Submodule.span_induction with
    | mem x hx => exact Submodule.subset_span (isPiVec_vecM π hx c)
    | zero => simpa [vecM_zero] using Submodule.zero_mem _
    | add x y _ _ hx hy =>
      have : (x + y) () = x () + y () := rfl
      rw [this, vecM_add]
      exact Submodule.add_mem _ hx hy
    | smul r x _ hx =>
      have : (r • x) () = r • x () := rfl
      rw [this, vecM_smul]
      exact Submodule.smul_mem _ _ hx
  have hf' : f ∈ closure (Submodule.span ℂ {f : Hs (ι := Unit) D | IsPiVec D π f} : Set (Hs (ι := Unit) D)) := hf
  have : (vecM (f ()) c : Hs (ι := ι) D) ∈
      closure (Submodule.span ℂ {f : Hs (ι := ι) D | IsPiVec D π f} : Set (Hs (ι := ι) D)) :=
    map_mem_closure (f := fun f : Hs (ι := Unit) D => (vecM (f ()) c : Hs (ι := ι) D))
      (continuous_vecM c) hf' hspan
  exact this

/- English proof (translation)
Rewrite using `[piSp, Submodule.orthogonal_closure, Submodule.mem_orthogonal]`. Introduce `g hg`. Proceed by induction on `hg using Submodule.span_induction with`. Consider the case `mem g hg`. Rewrite using `[PiLp.inner_apply]`.

Use `Finset.sum_eq_zero fun l _ => ?_` and prove the remaining obligations. Establish `h` using `(Submodule.mem_orthogonal _ _).1 hw _ (Submodule.le_topologicalClosure _ (Submodule.subset_span (isPiVec_comp π hg l)))`. Rewrite `h` using `[PiLp.inner_apply]`. Simplify using `only [vecM_apply, one_smul, Finset.univ_unique, Finset.sum_singleton] at h`. Rewrite using `[vecM_apply, inner_smul_right, h, mul_zero]`.

Consider the case `zero => simp`. Consider the case `add x y _ _ hx hy => rw [inner_add_left, hx, hy, add_zero]`. Consider the case `smul r x _ hx => rw [inner_smul_left, hx, mul_zero]`.
-/
private lemma vecM_orth [Fintype ι] (π : CuspSub E n) (c : ι → ℂ) {w : Lp ℂ 2 D.ν}
    (hw : (vecM w fun _ : Unit => 1 : Hs (ι := Unit) D) ∈ (piSp D π Unit)ᗮ) :
    (vecM w c : Hs (ι := ι) D) ∈ (piSp D π ι)ᗮ := by
  rw [piSp, Submodule.orthogonal_closure, Submodule.mem_orthogonal]
  intro g hg
  induction hg using Submodule.span_induction with
  | mem g hg =>
    rw [PiLp.inner_apply]
    refine Finset.sum_eq_zero fun l _ => ?_
    have h := (Submodule.mem_orthogonal _ _).1 hw _
      (Submodule.le_topologicalClosure _ (Submodule.subset_span (isPiVec_comp π hg l)))
    rw [PiLp.inner_apply] at h
    simp only [vecM_apply, one_smul, Finset.univ_unique, Finset.sum_singleton] at h
    rw [vecM_apply, inner_smul_right, h, mul_zero]
  | zero => simp
  | add x y _ _ hx hy => rw [inner_add_left, hx, hy, add_zero]
  | smul r x _ hx => rw [inner_smul_left, hx, mul_zero]

end SlopeTestRemainingChoices

end UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi

/- English proof (translation)
Introduce `E _ _ _ n D π ι _ v c`. Use `show _ = vecM ((piSp D π Unit).starProjection (vecM v fun _ : Unit => 1) ()) c`. Establish `hmem` using `(piSp D π Unit).starProjection_apply_mem (vecM v fun _ : Unit => 1)`. Establish `horth` using `(piSp D π Unit).sub_starProjection_mem_orthogonal (vecM v fun _ : Unit => 1)`. Use `Submodule.eq_starProjection_of_mem_orthogonal (vecM_mem π c hmem) ?_` and prove the remaining obligations.

Rewrite using `[← vecM_sub]`. Use `vecM_orth π c ?_` and prove the remaining obligations. Rewrite using `[vecM_sub, vecM_unit]`. Conclude with `horth`.
-/
theorem UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi.pDiag_pf :
    PDiag := by
  intro E _ _ _ n D π ι _ v c
  show _ = vecM ((piSp D π Unit).starProjection (vecM v fun _ : Unit => 1) ()) c
  have hmem := (piSp D π Unit).starProjection_apply_mem (vecM v fun _ : Unit => 1)
  have horth := (piSp D π Unit).sub_starProjection_mem_orthogonal (vecM v fun _ : Unit => 1)
  refine Submodule.eq_starProjection_of_mem_orthogonal (vecM_mem π c hmem) ?_
  rw [← vecM_sub]
  refine vecM_orth π c ?_
  rw [vecM_sub, vecM_unit]
  exact horth

end

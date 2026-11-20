import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.IsolateSpec

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC UpperTheory.Gal.TranscendenceTraces

/- English proof (translation)
Introduce `hcrit Z S p w hloc`. Apply `hcrit p w` to reduce the goal to its premises. Introduce `B φ hφ b`. Take `⟨A, hAo, ⟨a, ha⟩, hA⟩` from `hloc (B.u b)`. Choose the witnesses or unpack the hypotheses as in `⟨W, f1, f2, hW, hf1, c0, hc0⟩ : ∃ (W : Scheme) (f1 : W ⟶ B.U) (f2 : W ⟶ A.U), IsPullback f1 f2 B.u A.u ∧ IsOpenImmersion f1 ∧ ∃ c0, f1 c0 = b := by`.

Take `⟨c0, hc0, -⟩` from `Scheme.Pullback.exists_preimage_pullback (f := B.u) (g := A.u) b a ha.symm`. Conclude with `⟨_, _, _, IsPullback.of_hasPullback B.u A.u, inferInstance, c0, hc0⟩`. Take `⟨V', q1, q2, hq⟩ : ∃ (V' : Scheme) (q1 : V' ⟶ A.V) (q2 : V' ⟶ W), IsPullback q1 q2 A.r f2` from `⟨_, _, _, IsPullback.of_hasPullback A.r f2⟩`. Establish `hcomm : (q1 ≫ A.v) ≫ p = (q2 ≫ f1) ≫ B.u`. Simplify using `only [Category.assoc]`.

Rewrite using `[A.pb.w, ← Category.assoc, hq.w, Category.assoc, hW.w]`. Take `⟨g, hg1, hg2⟩ : ∃ g : V' ⟶ B.V, g ≫ B.v = q1 ≫ A.v ∧ g ≫ B.r = q2 ≫ f1` from `⟨B.pb.lift _ _ hcomm, B.pb.lift_fst _ _ _, B.pb.lift_snd _ _ _⟩`. Establish `hsq : IsPullback g q2 B.r f1`. Use `IsPullback.of_right ?_ hg2 B.pb` and prove the remaining obligations. Rewrite using `[hg1, hW.w]`.

Conclude with `hq.paste_horiz A.pb`. Take `⟨ψ, hψ, hψs⟩` from `hA ⟨W, V', f2, q1, q2, hq⟩ (fun y => φ (g y)) (hφ.comp_continuous g.continuous)`. Use `⟨f1 '' {y | ψ y = ψ c0}, ψ c0, f1.isOpenEmbedding.isOpenMap _ (hψ.isOpen_fiber _), ⟨c0, rfl, hc0⟩, ?_⟩` and prove the remaining obligations. Introduce and unpack `Ω _ _ x ⟨y, hy, hyx⟩`. Establish `hr : Set.range x ⊆ Set.range f1`.

Introduce and unpack `_ ⟨t, rfl⟩`. Conclude with `⟨y, hyx.trans (pt_eq x t).symm⟩`. Establish `hx' : IsOpenImmersion.lift f1 x hr ≫ f1 = x` using `IsOpenImmersion.lift_fac _ _ _`. Establish `hpt : pt (IsOpenImmersion.lift f1 x hr) = y`. Apply `f1.isOpenEmbedding.injective` to reduce the goal to its premises.

Rewrite using `[← pt_comp, hx', hyx]`. Establish `hs` using `hψs Ω (IsOpenImmersion.lift f1 x hr)`. Rewrite `hs` using `[hpt, show ψ y = ψ c0 from hy]`. Rewrite using `[hs]`. Use `symm`.

Establish `hb` using `fib_bijOn hsq (IsOpenImmersion.lift f1 x hr)`. Rewrite `hb` using `[hx']`. Use `finsum_mem_eq_of_bijOn (fun z => z ≫ g) hb ?_` and prove the remaining obligations. Introduce `z _`. Simplify using `only [Wt.comap, pt_comp, Category.assoc, hg1]`.
-/
theorem UpperTheory.Gal.TranscendenceTraces.wtLocal_of :
    WtCrit → WtLocal := by
  intro hcrit Z S p w hloc
  apply hcrit p w
  intro B φ hφ b
  obtain ⟨A, hAo, ⟨a, ha⟩, hA⟩ := hloc (B.u b)
  obtain ⟨W, f1, f2, hW, hf1, c0, hc0⟩ : ∃ (W : Scheme) (f1 : W ⟶ B.U) (f2 : W ⟶ A.U),
      IsPullback f1 f2 B.u A.u ∧ IsOpenImmersion f1 ∧ ∃ c0, f1 c0 = b := by
    obtain ⟨c0, hc0, -⟩ :=
      Scheme.Pullback.exists_preimage_pullback (f := B.u) (g := A.u) b a ha.symm
    exact ⟨_, _, _, IsPullback.of_hasPullback B.u A.u, inferInstance, c0, hc0⟩
  obtain ⟨V', q1, q2, hq⟩ : ∃ (V' : Scheme) (q1 : V' ⟶ A.V) (q2 : V' ⟶ W),
      IsPullback q1 q2 A.r f2 :=
    ⟨_, _, _, IsPullback.of_hasPullback A.r f2⟩
  have hcomm : (q1 ≫ A.v) ≫ p = (q2 ≫ f1) ≫ B.u := by
    simp only [Category.assoc]
    rw [A.pb.w, ← Category.assoc, hq.w, Category.assoc, hW.w]
  obtain ⟨g, hg1, hg2⟩ : ∃ g : V' ⟶ B.V, g ≫ B.v = q1 ≫ A.v ∧ g ≫ B.r = q2 ≫ f1 :=
    ⟨B.pb.lift _ _ hcomm, B.pb.lift_fst _ _ _, B.pb.lift_snd _ _ _⟩
  have hsq : IsPullback g q2 B.r f1 := by
    refine IsPullback.of_right ?_ hg2 B.pb
    rw [hg1, hW.w]
    exact hq.paste_horiz A.pb
  obtain ⟨ψ, hψ, hψs⟩ :=
    hA ⟨W, V', f2, q1, q2, hq⟩ (fun y => φ (g y)) (hφ.comp_continuous g.continuous)
  refine ⟨f1 '' {y | ψ y = ψ c0}, ψ c0, f1.isOpenEmbedding.isOpenMap _ (hψ.isOpen_fiber _),
    ⟨c0, rfl, hc0⟩, ?_⟩
  rintro Ω _ _ x ⟨y, hy, hyx⟩
  have hr : Set.range x ⊆ Set.range f1 := by
    rintro _ ⟨t, rfl⟩
    exact ⟨y, hyx.trans (pt_eq x t).symm⟩
  have hx' : IsOpenImmersion.lift f1 x hr ≫ f1 = x := IsOpenImmersion.lift_fac _ _ _
  have hpt : pt (IsOpenImmersion.lift f1 x hr) = y := by
    apply f1.isOpenEmbedding.injective
    rw [← pt_comp, hx', hyx]
  have hs := hψs Ω (IsOpenImmersion.lift f1 x hr)
  rw [hpt, show ψ y = ψ c0 from hy] at hs
  rw [hs]
  symm
  have hb := fib_bijOn hsq (IsOpenImmersion.lift f1 x hr)
  rw [hx'] at hb
  refine finsum_mem_eq_of_bijOn (fun z => z ≫ g) hb ?_
  intro z _
  simp only [Wt.comap, pt_comp, Category.assoc, hg1]

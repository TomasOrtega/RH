import Mathlib

open IsLocalRing

/- English proof (translation)
Introduce `A K M W _ _ _ _ _ _ Y0 Y _ e he hYY0 hiff χ sp hadd hsmul hli f`. Establish `hsp0 : sp 0 = 0`. Simplify using `using hadd 0 Y0.zero_mem 0 Y0.zero_mem`. Establish `hsum : ∀ {ι : Type} (s : Finset ι) (g : ι → M), (∀ i, g i ∈ Y0) → sp (∑ i ∈ s, g i) = ∑ i ∈ s, sp (g i)`. Introduce `ι s g hg`.

Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty => simp [hsp0]`. Consider the case `@insert a s ha ih`. Rewrite using `[Finset.sum_insert ha, Finset.sum_insert ha, hadd _ (hg a) _ (Y0.sum_mem (fun i _ => hg i)), ih]`. Prove the components needed by the constructor for the conclusion.

Introduce `h0`. Set `b` to `Module.Free.chooseBasis A Y0`. Set `y0 : Y0` to `⟨f, hYY0 f.2⟩`. Establish `hey : e y0 = y0` using `(hiff y0).1 f.2`. Establish `hy0 : y0 = ∑ i ∈ (b.repr y0).support, b.repr y0 i • b i` using `by conv_lhs => rw [← b.linearCombination_repr y0]`.

Rewrite using `[Finsupp.linearCombination_apply]`. Both sides reduce to the same expression. Establish `hf : (f : M) = ∑ i ∈ (b.repr y0).support, b.repr y0 i • ((b i : Y0) : M)`. Establish `h` using `congrArg (fun z : Y0 => (z : M)) hy0`. Rewrite using `[show (f : M) = (y0 : M) from rfl]`.

Use `h.trans ?_` and prove the remaining obligations. Rewrite using `[Submodule.coe_sum]`. Simplify using `only [Submodule.coe_smul]`. Establish `hspf : sp (f : M) = ∑ i ∈ (b.repr y0).support, χ (b.repr y0 i) • sp ((b i : Y0) : M)`. Rewrite using `[hf, hsum _ _ (fun i => Y0.smul_mem _ (b i).2)]`.

Conclude with `Finset.sum_congr rfl (fun i _ => hsmul _ (b i).2 _)`. Rewrite `hspf` using `[h0]`. Establish `hc : ∀ i ∈ (b.repr y0).support, χ (b.repr y0 i) = 0` using `linearIndependent_iff'.1 (hli _ b) _ (fun i => χ (b.repr y0 i)) hspf.symm`. Establish `hz : ∀ i, ((e (b i) : Y0) : M) ∈ Y` using `fun i => (hiff (e (b i))).2 (by rw [← Module.End.mul_apply, he.eq])`. Establish `hfY : f = ∑ i ∈ (b.repr y0).support, b.repr y0 i • (⟨_, hz i⟩ : Y)`.

Apply `Subtype.ext` to reduce the goal to its premises. Rewrite using `[Submodule.coe_sum]`. Simplify using `only [Submodule.coe_smul]`. Establish `h1 : (f : M) = ((e y0 : Y0) : M)` using `by rw [hey]`. Rewrite using `[h1]`.

Use `conv_lhs => rw [hy0]`. Rewrite using `[map_sum, Submodule.coe_sum]`. Simplify using `only [map_smul, Submodule.coe_smul]`. Rewrite using `[hfY]`. Use `Submodule.sum_mem _ (fun i hi => ?_)` and prove the remaining obligations.

Conclude with `Submodule.smul_mem_smul ((RingHom.mem_ker).2 (hc i hi)) Submodule.mem_top`. Introduce `hf`. Use `Submodule.smul_induction_on (p := fun g : Y => sp (g : M) = 0) hf ?_ ?_` and prove the remaining obligations. Introduce `r hr y _ show sp ((r • y : Y) : M) = 0`. Rewrite using `[Submodule.coe_smul, hsmul _ (hYY0 y.2) r, (RingHom.mem_ker).1 hr, zero_smul]`.

Introduce `y z hy hz`. Establish `hy' : sp (y : M) = 0` using `hy`. Establish `hz' : sp (z : M) = 0` using `hz`. Use `show sp ((y + z : Y) : M) = 0`. Rewrite using `[Submodule.coe_add, hadd _ (hYY0 y.2) _ (hYY0 z.2), hy', hz', add_zero]`.
-/
theorem UpperTheory.V.Th.AnnihilatorQuotientFinite.kerSp :
    ∀ {A K M W : Type} [CommRing A] [Field K] [AddCommGroup M] [Module A M] [AddCommGroup W] [Module K W] (Y0 Y : Submodule A M) [Module.Free A Y0] (e : Module.End A Y0), IsIdempotentElem e → Y ≤ Y0 → (∀ y : Y0, (y : M) ∈ Y ↔ e y = y) → ∀ (χ : A →+* K) (sp : M → W), (∀ f ∈ Y0, ∀ f' ∈ Y0, sp (f + f') = sp f + sp f') → (∀ f ∈ Y0, ∀ b : A, sp (b • f) = χ b • sp f) → (∀ (κ : Type) (b : Module.Basis κ A Y0), LinearIndependent K fun i => sp (b i)) → ∀ f : Y, sp f = 0 ↔ f ∈ (RingHom.ker χ • ⊤ : Submodule A Y) := by
  intro A K M W _ _ _ _ _ _ Y0 Y _ e he hYY0 hiff χ sp hadd hsmul hli f
  classical
  have hsp0 : sp 0 = 0 := by
    simpa using hadd 0 Y0.zero_mem 0 Y0.zero_mem
  have hsum : ∀ {ι : Type} (s : Finset ι) (g : ι → M), (∀ i, g i ∈ Y0) →
      sp (∑ i ∈ s, g i) = ∑ i ∈ s, sp (g i) := by
    intro ι s g hg
    induction s using Finset.induction_on with
    | empty => simp [hsp0]
    | @insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha,
        hadd _ (hg a) _ (Y0.sum_mem (fun i _ => hg i)), ih]
  constructor
  · intro h0
    let b := Module.Free.chooseBasis A Y0
    let y0 : Y0 := ⟨f, hYY0 f.2⟩
    have hey : e y0 = y0 := (hiff y0).1 f.2
    have hy0 : y0 = ∑ i ∈ (b.repr y0).support, b.repr y0 i • b i := by
      conv_lhs => rw [← b.linearCombination_repr y0]
      rw [Finsupp.linearCombination_apply]
      rfl
    have hf : (f : M) = ∑ i ∈ (b.repr y0).support, b.repr y0 i • ((b i : Y0) : M) := by
      have h := congrArg (fun z : Y0 => (z : M)) hy0
      rw [show (f : M) = (y0 : M) from rfl]
      refine h.trans ?_
      rw [Submodule.coe_sum]
      simp only [Submodule.coe_smul]
    have hspf : sp (f : M) = ∑ i ∈ (b.repr y0).support, χ (b.repr y0 i) • sp ((b i : Y0) : M) := by
      rw [hf, hsum _ _ (fun i => Y0.smul_mem _ (b i).2)]
      exact Finset.sum_congr rfl (fun i _ => hsmul _ (b i).2 _)
    rw [h0] at hspf
    have hc : ∀ i ∈ (b.repr y0).support, χ (b.repr y0 i) = 0 :=
      linearIndependent_iff'.1 (hli _ b) _ (fun i => χ (b.repr y0 i)) hspf.symm
    have hz : ∀ i, ((e (b i) : Y0) : M) ∈ Y := fun i =>
      (hiff (e (b i))).2 (by rw [← Module.End.mul_apply, he.eq])
    have hfY : f = ∑ i ∈ (b.repr y0).support, b.repr y0 i • (⟨_, hz i⟩ : Y) := by
      apply Subtype.ext
      rw [Submodule.coe_sum]
      simp only [Submodule.coe_smul]
      have h1 : (f : M) = ((e y0 : Y0) : M) := by rw [hey]
      rw [h1]
      conv_lhs => rw [hy0]
      rw [map_sum, Submodule.coe_sum]
      simp only [map_smul, Submodule.coe_smul]
    rw [hfY]
    refine Submodule.sum_mem _ (fun i hi => ?_)
    exact Submodule.smul_mem_smul ((RingHom.mem_ker).2 (hc i hi)) Submodule.mem_top
  · intro hf
    refine Submodule.smul_induction_on (p := fun g : Y => sp (g : M) = 0) hf ?_ ?_
    · intro r hr y _
      show sp ((r • y : Y) : M) = 0
      rw [Submodule.coe_smul, hsmul _ (hYY0 y.2) r, (RingHom.mem_ker).1 hr, zero_smul]
    · intro y z hy hz
      have hy' : sp (y : M) = 0 := hy
      have hz' : sp (z : M) = 0 := hz
      show sp ((y + z : Y) : M) = 0
      rw [Submodule.coe_add, hadd _ (hYY0 y.2) _ (hYY0 z.2), hy', hz', add_zero]

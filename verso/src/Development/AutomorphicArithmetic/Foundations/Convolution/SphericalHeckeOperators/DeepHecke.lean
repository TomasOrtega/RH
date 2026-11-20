import Development.AutomorphicArithmetic.Foundations.Convolution.SphericalHeckeOperators.SymSum
import Development.AutomorphicArithmetic.Foundations.Convolution.TwistedLocalOrbits.Match
import Development.AutomorphicArithmetic.Foundations.Convolution.SphericalHeckeOperators.DeepAbs
import Development.AutomorphicArithmetic.Foundations.Convolution.SphericalHeckeOperators.ThMatch
import Development.AutomorphicArithmetic.Foundations.Convolution.SphericalHeckeOperators.SigInv
import Development.AutomorphicArithmetic.Foundations.Convolution.SphericalHeckeOperators.DefBridge
import Development.AutomorphicArithmetic.Foundations.Convolution.SphericalHeckeOperators.UnrQ
import Development.AutomorphicArithmetic.Foundations.Convolution.SphericalHeckeOperators.DcoShape
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.OrbitalIntegrals.QuotFubiniHolds

open MeasureTheory GroundTheory.Automorphic GroundTheory.Automorphic.Spherical GroundTheory.Automorphic.GLnLocal GroundTheory.Automorphic.Iwasawa UpperTheory.ConvolutionTheory.H

/- English proof (translation)
Introduce `x hx y hy c`. Establish `hcx` using `Submodule.smul_mem (locallyConstantCompactSupport G ℂ ℂ) c hx`. Rewrite using `[ha _ _ hcx.1.continuous hcx.2 hy.1.continuous hy.2, hs]`.
-/
private theorem lin_of {G : Type} [TopologicalSpace G] [Group G] [IsTopologicalGroup G] (Λ : (G → ℂ) → ℂ)
    (hs : ∀ (c : ℂ) (φ : G → ℂ), Λ (c • φ) = c * Λ φ)
    (ha : ∀ φ ψ : G → ℂ, Continuous φ → HasCompactSupport φ → Continuous ψ → HasCompactSupport ψ →
      Λ (φ + ψ) = Λ φ + Λ ψ) :
    ∀ x ∈ locallyConstantCompactSupport G ℂ ℂ, ∀ y ∈ locallyConstantCompactSupport G ℂ ℂ, ∀ c : ℂ,
      Λ (c • x + y) = c * Λ x + Λ y := by
  intro x hx y hy c
  have hcx := Submodule.smul_mem (locallyConstantCompactSupport G ℂ ℂ) c hx
  rw [ha _ _ hcx.1.continuous hcx.2 hy.1.continuous hy.2, hs]

/- English proof (translation)
Take `⟨i1, i2, i3, -⟩` from `UpperTheory.V.Z.Tf.Orb.gLTop F n`. Establish `key : ∀ x ∈ comm μ, Continuous x ∧ HasCompactSupport x ∧ Λ x = 0`. Introduce `x hx`. Proceed by induction on `hx using Submodule.span_induction with`. Consider the case `mem x hx`.

Take `⟨a, b, ha', hb, rfl⟩` from `hx`. Establish `ham : a ∈ locallyConstantCompactSupport (GL (Fin n) F) ℂ ℂ`. Break down `ha' with rfl | ⟨l, hl, rfl⟩` into its components or cases. Conclude with `indicator_mem_locallyConstantCompactSupport (GLnLocal.isCompact_integralGL F n) (GLnLocal.isOpen_integralGL F n) (1 : ℂ)`. Conclude with `(UpperTheory.ConvolutionTheory.H.dcoShape F n l hl).2.2.1`.

Take `⟨c1, c2⟩ : Continuous (groupConv μ a b) ∧ HasCompactSupport (groupConv μ a b)` from `UpperTheory.V.Z.Tf.Orb.convTest _ μ inferInstance a b ham.1.continuous ham.2 hb.1.continuous hb.2`. Take `⟨d1, d2⟩ : Continuous (groupConv μ b a) ∧ HasCompactSupport (groupConv μ b a)` from `UpperTheory.V.Z.Tf.Orb.convTest _ μ inferInstance b a hb.1.continuous hb.2 ham.1.continuous ham.2`. Establish `e : groupConv μ a b - groupConv μ b a = groupConv μ a b + (-1 : ℂ) • groupConv μ b a`. Rewrite using `[neg_one_smul, sub_eq_add_neg]`. Establish `hneg : Continuous ((-1 : ℂ) • groupConv μ b a)` using `d1.const_smul _`.

Establish `hnegc : HasCompactSupport ((-1 : ℂ) • groupConv μ b a)` using `HasCompactSupport.mono d2 (Function.support_const_smul_subset _ _)`. Use `⟨?_, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[e]`. Conclude with `Continuous.add c1 hneg`. Rewrite using `[e]`.

Conclude with `HasCompactSupport.add c2 hnegc`. Rewrite using `[e, ha _ _ c1 c2 hneg hnegc, hs, hc a b ha' ham hb]`. Expand and normalize the polynomial expressions, which then agree. Consider the case `zero`. Use `⟨continuous_const, HasCompactSupport.zero, ?_⟩` and prove the remaining obligations.

Use `hs 0 0` as an intermediate fact. Simplify using `using this`. Consider the case `add x y _ _ hx hy`. Conclude with `⟨hx.1.add hy.1, hx.2.1.add hy.2.1, by rw [ha _ _ hx.1 hx.2.1 hy.1 hy.2.1, hx.2.2, hy.2.2, add_zero]⟩`. Consider the case `smul c x _ hx`.

Conclude with `⟨hx.1.const_smul c, HasCompactSupport.mono hx.2.1 (Function.support_const_smul_subset _ _), by rw [hs, hx.2.2, mul_zero]⟩`. Conclude with `fun x hx => (key x hx).2.2`.
-/
private theorem comm_zero {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] {n : ℕ}
    [MeasurableSpace (GL (Fin n) F)] [BorelSpace (GL (Fin n) F)] (μ : Measure (GL (Fin n) F)) [μ.IsHaarMeasure]
    (Λ : (GL (Fin n) F → ℂ) → ℂ)
    (hs : ∀ (c : ℂ) (φ : GL (Fin n) F → ℂ), Λ (c • φ) = c * Λ φ)
    (ha : ∀ φ ψ : GL (Fin n) F → ℂ, Continuous φ → HasCompactSupport φ → Continuous ψ → HasCompactSupport ψ →
      Λ (φ + ψ) = Λ φ + Λ ψ)
    (hc : ∀ a b : GL (Fin n) F → ℂ, (a = oneK F n ∨ ∃ l, Antitone l ∧ a = uFn F l) →
      a ∈ locallyConstantCompactSupport (GL (Fin n) F) ℂ ℂ → b ∈ locallyConstantCompactSupport (GL (Fin n) F) ℂ ℂ →
      Λ (groupConv μ a b) = Λ (groupConv μ b a)) :
    ∀ x ∈ comm μ, Λ x = 0 := by
  obtain ⟨i1, i2, i3, -⟩ := UpperTheory.V.Z.Tf.Orb.gLTop F n
  have key : ∀ x ∈ comm μ, Continuous x ∧ HasCompactSupport x ∧ Λ x = 0 := by
    intro x hx
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨a, b, ha', hb, rfl⟩ := hx
      have ham : a ∈ locallyConstantCompactSupport (GL (Fin n) F) ℂ ℂ := by
        rcases ha' with rfl | ⟨l, hl, rfl⟩
        · exact indicator_mem_locallyConstantCompactSupport (GLnLocal.isCompact_integralGL F n)
            (GLnLocal.isOpen_integralGL F n) (1 : ℂ)
        · exact (UpperTheory.ConvolutionTheory.H.dcoShape F n l hl).2.2.1
      obtain ⟨c1, c2⟩ : Continuous (groupConv μ a b) ∧ HasCompactSupport (groupConv μ a b) :=
        UpperTheory.V.Z.Tf.Orb.convTest _ μ inferInstance a b ham.1.continuous ham.2 hb.1.continuous hb.2
      obtain ⟨d1, d2⟩ : Continuous (groupConv μ b a) ∧ HasCompactSupport (groupConv μ b a) :=
        UpperTheory.V.Z.Tf.Orb.convTest _ μ inferInstance b a hb.1.continuous hb.2 ham.1.continuous ham.2
      have e : groupConv μ a b - groupConv μ b a = groupConv μ a b + (-1 : ℂ) • groupConv μ b a := by
        rw [neg_one_smul, sub_eq_add_neg]
      have hneg : Continuous ((-1 : ℂ) • groupConv μ b a) := d1.const_smul _
      have hnegc : HasCompactSupport ((-1 : ℂ) • groupConv μ b a) :=
        HasCompactSupport.mono d2 (Function.support_const_smul_subset _ _)
      refine ⟨?_, ?_, ?_⟩
      · rw [e]; exact Continuous.add c1 hneg
      · rw [e]; exact HasCompactSupport.add c2 hnegc
      · rw [e, ha _ _ c1 c2 hneg hnegc, hs, hc a b ha' ham hb]
        ring
    | zero =>
      refine ⟨continuous_const, HasCompactSupport.zero, ?_⟩
      have := hs 0 0
      simpa using this
    | add x y _ _ hx hy =>
      exact ⟨hx.1.add hy.1, hx.2.1.add hy.2.1, by rw [ha _ _ hx.1 hx.2.1 hy.1 hy.2.1, hx.2.2, hy.2.2, add_zero]⟩
    | smul c x _ hx =>
      exact ⟨hx.1.const_smul c, HasCompactSupport.mono hx.2.1 (Function.support_const_smul_subset _ _),
        by rw [hs, hx.2.2, mul_zero]⟩
  exact fun x hx => (key x hx).2.2

/- English proof (translation)
Unfold `PositivityTheory.Rg.Tf.Loc.IsTwRegSemisimple at hr`. Unfold `PositivityTheory.Rg.Tf.Loc.IsRegSemisimple`. Rewrite `hr` using `[hN, Units.val_mul, Units.val_mul, Matrix.coe_units_inv, Matrix.charpoly_units_conj]`. Establish `h : ((PositivityTheory.Rg.Tf.Loc.incl γ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) = ((γ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k).map (algebraMap k E)` using `rfl`. Rewrite `hr` using `[h, Matrix.charpoly_map]`.

Conclude with `(Polynomial.separable_map _).1 hr`.
-/
private theorem reg_of_norm {k E : Type} [Field k] [Field E] [Algebra k E] {n : ℕ} (σ : E ≃ₐ[k] E)
    {δ x : GL (Fin n) E} {γ : GL (Fin n) k} (hr : PositivityTheory.Rg.Tf.Loc.IsTwRegSemisimple σ δ)
    (hN : PositivityTheory.Rg.Tf.Loc.normGL σ δ = x * PositivityTheory.Rg.Tf.Loc.incl γ * x⁻¹) :
    PositivityTheory.Rg.Tf.Loc.IsRegSemisimple γ := by
  unfold PositivityTheory.Rg.Tf.Loc.IsTwRegSemisimple at hr
  unfold PositivityTheory.Rg.Tf.Loc.IsRegSemisimple
  rw [hN, Units.val_mul, Units.val_mul, Matrix.coe_units_inv, Matrix.charpoly_units_conj] at hr
  have h : ((PositivityTheory.Rg.Tf.Loc.incl γ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) =
      ((γ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k).map (algebraMap k E) := rfl
  rw [h, Matrix.charpoly_map] at hr
  exact (Polynomial.separable_map _).1 hr

/- English proof (translation)
Introduce `k E _ _ _ _ _ _ _ _ _ _ _ _ _ hu σ hσ n _ _ _ _ μE μk hE hk h1 h2 P hP z`. Take `⟨hq, -⟩` from `UpperTheory.ConvolutionTheory.H.unrQ k E hu`. Rewrite `h1` using `[(UpperTheory.ConvolutionTheory.H.defBridge E n).1]`. Rewrite `h2` using `[(UpperTheory.ConvolutionTheory.H.defBridge k n).1]`. Establish `hq' : (qF E : ℂ) = (qF k : ℂ) ^ Module.finrank k E` using `by rw [hq]; push_cast; rfl`.

Take `⟨g, hg1, hg2, hg3, hg4⟩` from `UpperTheory.ConvolutionTheory.H.deepAbs k E n (Module.finrank k E) Module.finrank_pos hq' μE μk h1 h2 P hP z`. Establish `hcE : ∀ (δ : GL (Fin n) E) (μδ : Measure (PositivityTheory.Rg.Tf.Loc.twCent (PositivityTheory.Rg.Tf.Loc.sigmaGL σ) δ)), PositivityTheory.Rg.Tf.Loc.IsTwRegSemisimple σ δ → μδ.IsHaarMeasure → ∀ x ∈ comm μE, PositivityTheory.Rg.Tf.Loc.twOrbIntegralC (PositivityTheory.Rg.Tf.Loc.sigma …`. Introduce `δ μδ hr hm`. Take `⟨ls, la⟩` from `UpperTheory.V.Z.Tf.Orb.twOrbLin_holds k E σ hσ n μE inferInstance δ hr μδ hm`. Establish `tc` using `UpperTheory.V.Z.Tf.Orb.twOrbComm_holds k E σ hσ n μE inferInstance δ hr μδ hm`.

Use `comm_zero μE _ ls la fun a b ha' ham hb => ?_` and prove the remaining obligations. Use `tc a b ham.1.continuous ham.2 hb.1.continuous hb.2 fun x => ?_` and prove the remaining obligations. Break down `ha' with rfl | ⟨l, hl, rfl⟩` into its components or cases. Conclude with `(UpperTheory.ConvolutionTheory.H.sigInv k E σ n x).1`. Conclude with `(UpperTheory.ConvolutionTheory.H.sigInv k E σ n x).2 l`.

Establish `hck : ∀ (γ : GL (Fin n) k) (μγ : Measure (Subgroup.centralizer {γ})), PositivityTheory.Rg.Tf.Loc.IsRegSemisimple γ → μγ.IsHaarMeasure → ∀ x ∈ comm μk, PositivityTheory.Rg.Tf.Loc.orbIntegralC μk γ μγ x = 0`. Introduce `γ μγ hr hm`. Take `⟨ls, la⟩` from `UpperTheory.V.Z.Tf.Orb.orbLin_holds k n μk inferInstance γ hr μγ hm`. Establish `oc` using `UpperTheory.V.Z.Tf.Orb.orbComm_holds k n μk inferInstance γ hr μγ hm`. Conclude with `comm_zero μk _ ls la fun a b _ ham hb => oc a b ham.1.continuous ham.2 hb.1.continuous hb.2`.

Establish `hlk : ∀ (γ : GL (Fin n) k) (μγ : Measure (Subgroup.centralizer {γ})), PositivityTheory.Rg.Tf.Loc.IsRegSemisimple γ → μγ.IsHaarMeasure → ∀ x ∈ locallyConstantCompactSupport (GL (Fin n) k) ℂ ℂ, ∀ y ∈ locallyConstantCompactSupport (GL (Fin n) k) ℂ ℂ, ∀ c : ℂ, PositivityTheory.Rg.Tf. …`. Introduce `γ μγ hr hm`. Take `⟨ls, la⟩` from `UpperTheory.V.Z.Tf.Orb.orbLin_holds k n μk inferInstance γ hr μγ hm`. Conclude with `lin_of _ ls la`. Use `⟨g, hg1, hg2, hg3, fun p hp h f hh hf => ⟨?_, ?_⟩⟩` and prove the remaining obligations.

Introduce `δ γ x μδ μγ hr hN hδ hγ hm`. Establish `hrγ` using `reg_of_norm σ hr hN`. Take `⟨ls, la⟩` from `UpperTheory.V.Z.Tf.Orb.twOrbLin_holds k E σ hσ n μE inferInstance δ hr μδ hδ`. Conclude with `hg4 p hp h f hh hf (PositivityTheory.Rg.Tf.Loc.twOrbIntegralC (PositivityTheory.Rg.Tf.Loc.sigmaGL σ) μE δ μδ) (PositivityTheory.Rg.Tf.Loc.orbIntegralC μk γ μγ) (lin_of _ ls la) (hcE δ μδ hr hδ) (hlk γ μγ hrγ hγ) (hck γ μγ hrγ hγ) fun a ha => (UpperTheory.ConvolutionTheory.H.thMat …`. Introduce `γ μγ hr hnot hγ`.

Conclude with `(hg4 p hp h f hh hf (fun _ => 0) (PositivityTheory.Rg.Tf.Loc.orbIntegralC μk γ μγ) (fun _ _ _ _ _ => by simp) (fun _ _ => rfl) (hlk γ μγ hr hγ) (hck γ μγ hr hγ) fun a ha => ((UpperTheory.ConvolutionTheory.H.thMatch k E hu σ hσ n μE μk a ha).2 γ μγ hr hnot hγ).symm).symm`.
-/
theorem UpperTheory.ConvolutionTheory.H.deepHecke :
    ∀ (k E : Type) [Field k] [CharZero k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
      [Field E] [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E]
      [Algebra k E] [ValuativeExtension k E] [FiniteDimensional k E] [IsGalois k E], PositivityTheory.Rg.Tf.Loc.IsUnramifiedLoc k E →
      ∀ σ : E ≃ₐ[k] E, (∀ τ : E ≃ₐ[k] E, τ ∈ Subgroup.zpowers σ) →
      ∀ (n : ℕ) [MeasurableSpace (GL (Fin n) E)] [BorelSpace (GL (Fin n) E)] [MeasurableSpace (GL (Fin n) k)] [BorelSpace (GL (Fin n) k)]
        (μE : Measure (GL (Fin n) E)) (μk : Measure (GL (Fin n) k)) [μE.IsHaarMeasure] [μk.IsHaarMeasure],
      μE (PositivityTheory.Rg.Tf.Loc.unitGL (n := Fin n) E : Set (GL (Fin n) E)) = 1 → μk (PositivityTheory.Rg.Tf.Loc.unitGL (n := Fin n) k : Set (GL (Fin n) k)) = 1 →
      ∀ P : Finset (LaurentRing n), (∀ p ∈ P, p ∈ symmetricLaurent n) → ∀ z : Fin n → ℂˣ,
      ∃ g ∈ symmetricLaurent n, g ∈ (polyEmb n).range ∧ evalAt z g ≠ 0 ∧ ∀ p ∈ Submodule.span ℂ (P : Set (LaurentRing n)),
        ∀ (h : SphericalHecke μE (F := E) (n := n)) (f : SphericalHecke μk (F := k) (n := n)),
          satakeTransform μE h = g * p → satakeTransform μk f = bc (Module.finrank k E) (g * p) →
          UpperTheory.ConvolutionTheory.Loc.Match σ μE μk (fun x => (h : HeckeAlgebra μE) x) fun x => (f : HeckeAlgebra μk) x := by
  intro k E _ _ _ _ _ _ _ _ _ _ _ _ _ hu σ hσ n _ _ _ _ μE μk hE hk h1 h2 P hP z
  obtain ⟨hq, -⟩ := UpperTheory.ConvolutionTheory.H.unrQ k E hu
  rw [(UpperTheory.ConvolutionTheory.H.defBridge E n).1] at h1
  rw [(UpperTheory.ConvolutionTheory.H.defBridge k n).1] at h2
  have hq' : (qF E : ℂ) = (qF k : ℂ) ^ Module.finrank k E := by rw [hq]; push_cast; rfl
  obtain ⟨g, hg1, hg2, hg3, hg4⟩ := UpperTheory.ConvolutionTheory.H.deepAbs k E n (Module.finrank k E) Module.finrank_pos hq' μE μk h1 h2 P hP z
  have hcE : ∀ (δ : GL (Fin n) E) (μδ : Measure (PositivityTheory.Rg.Tf.Loc.twCent (PositivityTheory.Rg.Tf.Loc.sigmaGL σ) δ)),
      PositivityTheory.Rg.Tf.Loc.IsTwRegSemisimple σ δ → μδ.IsHaarMeasure →
      ∀ x ∈ comm μE, PositivityTheory.Rg.Tf.Loc.twOrbIntegralC (PositivityTheory.Rg.Tf.Loc.sigmaGL σ) μE δ μδ x = 0 := by
    intro δ μδ hr hm
    obtain ⟨ls, la⟩ := UpperTheory.V.Z.Tf.Orb.twOrbLin_holds k E σ hσ n μE inferInstance δ hr μδ hm
    have tc := UpperTheory.V.Z.Tf.Orb.twOrbComm_holds k E σ hσ n μE inferInstance δ hr μδ hm
    refine comm_zero μE _ ls la fun a b ha' ham hb => ?_
    refine tc a b ham.1.continuous ham.2 hb.1.continuous hb.2 fun x => ?_
    rcases ha' with rfl | ⟨l, hl, rfl⟩
    · exact (UpperTheory.ConvolutionTheory.H.sigInv k E σ n x).1
    · exact (UpperTheory.ConvolutionTheory.H.sigInv k E σ n x).2 l
  have hck : ∀ (γ : GL (Fin n) k) (μγ : Measure (Subgroup.centralizer {γ})),
      PositivityTheory.Rg.Tf.Loc.IsRegSemisimple γ → μγ.IsHaarMeasure →
      ∀ x ∈ comm μk, PositivityTheory.Rg.Tf.Loc.orbIntegralC μk γ μγ x = 0 := by
    intro γ μγ hr hm
    obtain ⟨ls, la⟩ := UpperTheory.V.Z.Tf.Orb.orbLin_holds k n μk inferInstance γ hr μγ hm
    have oc := UpperTheory.V.Z.Tf.Orb.orbComm_holds k n μk inferInstance γ hr μγ hm
    exact comm_zero μk _ ls la fun a b _ ham hb => oc a b ham.1.continuous ham.2 hb.1.continuous hb.2
  have hlk : ∀ (γ : GL (Fin n) k) (μγ : Measure (Subgroup.centralizer {γ})),
      PositivityTheory.Rg.Tf.Loc.IsRegSemisimple γ → μγ.IsHaarMeasure →
      ∀ x ∈ locallyConstantCompactSupport (GL (Fin n) k) ℂ ℂ, ∀ y ∈ locallyConstantCompactSupport (GL (Fin n) k) ℂ ℂ, ∀ c : ℂ,
        PositivityTheory.Rg.Tf.Loc.orbIntegralC μk γ μγ (c • x + y) =
          c * PositivityTheory.Rg.Tf.Loc.orbIntegralC μk γ μγ x + PositivityTheory.Rg.Tf.Loc.orbIntegralC μk γ μγ y := by
    intro γ μγ hr hm
    obtain ⟨ls, la⟩ := UpperTheory.V.Z.Tf.Orb.orbLin_holds k n μk inferInstance γ hr μγ hm
    exact lin_of _ ls la
  refine ⟨g, hg1, hg2, hg3, fun p hp h f hh hf => ⟨?_, ?_⟩⟩
  · intro δ γ x μδ μγ hr hN hδ hγ hm
    have hrγ := reg_of_norm σ hr hN
    obtain ⟨ls, la⟩ := UpperTheory.V.Z.Tf.Orb.twOrbLin_holds k E σ hσ n μE inferInstance δ hr μδ hδ
    exact hg4 p hp h f hh hf (PositivityTheory.Rg.Tf.Loc.twOrbIntegralC (PositivityTheory.Rg.Tf.Loc.sigmaGL σ) μE δ μδ)
      (PositivityTheory.Rg.Tf.Loc.orbIntegralC μk γ μγ) (lin_of _ ls la) (hcE δ μδ hr hδ) (hlk γ μγ hrγ hγ) (hck γ μγ hrγ hγ)
      fun a ha => (UpperTheory.ConvolutionTheory.H.thMatch k E hu σ hσ n μE μk a ha).1 δ γ x μδ μγ hr hN hδ hγ hm
  · intro γ μγ hr hnot hγ
    exact (hg4 p hp h f hh hf (fun _ => 0) (PositivityTheory.Rg.Tf.Loc.orbIntegralC μk γ μγ)
      (fun _ _ _ _ _ => by simp) (fun _ _ => rfl) (hlk γ μγ hr hγ) (hck γ μγ hr hγ)
      fun a ha => ((UpperTheory.ConvolutionTheory.H.thMatch k E hu σ hσ n μE μk a ha).2 γ μγ hr hnot hγ).symm).symm

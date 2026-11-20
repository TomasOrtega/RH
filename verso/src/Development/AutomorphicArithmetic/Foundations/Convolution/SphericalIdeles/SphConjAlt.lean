import Mathlib
import Development.AutomorphicArithmetic.Foundations.Convolution.SphericalIdeles.SphConj
import Development.AutomorphicArithmetic.Foundations.Convolution.TraceSplitting.Places
import Development.AutomorphicArithmetic.Foundations.Convolution.IntegrableConvolution.TwistPerm
import Development.AutomorphicArithmetic.Foundations.Convolution.IntegrableConvolution.FinSplit
import Development.AutomorphicArithmetic.Foundations.Convolution.IntegrableConvolution.SplitLoc
import Development.AutomorphicArithmetic.Foundations.Convolution.CentreSplitting.TwUnitary

open MeasureTheory NumberField IsDedekindDomain
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.CuspidalSpectrum GroundTheory.Global GroundTheory.Global.SemiLocal
open PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Geo UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C UpperTheory.ConvolutionTheory.L1

namespace UpperTheory.ConvolutionTheory.Sph

open scoped Fin.NatCast Fin.CommRing in
/- English proof (translation)
Establish `key : ∀ (t : ℕ) (i : Fin (m + 1)), P (i + (t : Fin (m + 1))) → P i`. Introduce `t`. Proceed by induction on `t with`. Consider the case `zero => intro i hi`. Simplify using `using hi`.

Consider the case `succ t ih`. Introduce `i hi`. Use `ih i (h _ ?_)` and prove the remaining obligations. Rewrite `hi` using `[Nat.cast_succ, ← add_assoc]`. Conclude with `hi`.

Use `key (j - k).val k ?_` and prove the remaining obligations. Rewrite using `[Fin.cast_val_eq_self]`. Simplify using `using hj`.
-/
private theorem round_cycle {m : ℕ} {P : Fin (m + 1) → Prop} (h : ∀ i, P (i + 1) → P i) (j k : Fin (m + 1)) (hj : P j) :
    P k := by
  have key : ∀ (t : ℕ) (i : Fin (m + 1)), P (i + (t : Fin (m + 1))) → P i := by
    intro t
    induction t with
    | zero => intro i hi; simpa using hi
    | succ t ih =>
      intro i hi
      refine ih i (h _ ?_)
      rw [Nat.cast_succ, ← add_assoc] at hi
      exact hi
  refine key (j - k).val k ?_
  rw [Fin.cast_val_eq_self]
  simpa using hj

/- English proof (translation)
Simplify using `only [fixL, fixF, Submodule.mem_iInf, LinearMap.mem_eqLocus, ContinuousLinearMap.coe_coe, LinearMap.id_apply]`. Prove the components needed by the constructor for the conclusion. Introduce `h g hg`. Conclude with `h _ ⟨g, hg, rfl⟩`. Introduce and unpack `h _ ⟨g, hg, rfl⟩`.

Conclude with `h g hg`.
-/
private theorem mem_fixL {K : Type} [Field K] [NumberField K] {n : ℕ} {μ : Measure (normOneGL K n)} [μ.IsHaarMeasure]
    {w : Pl K} {J : Subgroup (GL (Fin n) (w.adicCompletion K))} {f : LL μ} :
    f ∈ fixL μ w J ↔ ∀ g ∈ J, rhoL μ w g f = f := by
  simp only [fixL, fixF, Submodule.mem_iInf, LinearMap.mem_eqLocus, ContinuousLinearMap.coe_coe, LinearMap.id_apply]
  constructor
  · intro h g hg
    exact h _ ⟨g, hg, rfl⟩
  · rintro h _ ⟨g, hg, rfl⟩
    exact h g hg

/- English proof (translation)
Take `⟨x, hx, hx0⟩` from `(Submodule.ne_bot_iff _).1 h`. Take `⟨hxV, hxf⟩` from `Submodule.mem_inf.1 hx`. Establish `hxf'` using `mem_fixL.1 hxf`. Use `(Submodule.ne_bot_iff _).2 ⟨θ.U x, Submodule.mem_inf.2 ⟨?_, mem_fixL.2 fun k hk => ?_⟩, fun h0 => hx0 ?_⟩` and prove the remaining obligations. Rewrite using `[← hV]`.

Conclude with `Submodule.mem_map_of_mem hxV`. Take `⟨⟨ε, hε⟩, hint, -⟩` from `splitLoc F E p (e i) (hs _) n`. Take `⟨-, hint', -⟩` from `splitLoc F E p (e (i + 1)) (hs _) n`. Choose the witnesses or unpack the hypotheses as in `⟨g, rfl⟩ : ∃ g, mapGL n (completionMap p (e i).1) g = k := by`. Take `⟨g, hg⟩` from `ε.surjective k`.

Conclude with `⟨g, (hε g).symm.trans hg⟩`. Establish `hg` using `(hint g).1 hk`. Establish `h2` using `(twistPerm F E σ hσ m n μ θ hθ).2.1 p D e he i g x`. Rewrite `h2` using `[hxf' _ ((hint' g).2 hg)]`. Conclude with `h2.symm`.

Use `(Dp.twUnitary E n μ θ).1 x` as an intermediate fact. Rewrite `this` using `[h0, norm_zero]`. Conclude with `norm_eq_zero.1 this.symm`.
-/
private theorem fix_step {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsGalois F E]
    {σ : E ≃ₐ[F] E} (hσ : ∀ τ, τ ∈ Subgroup.zpowers σ) {m n : ℕ} {μ : Measure (normOneGL E n)} [μ.IsHaarMeasure]
    {θ : Twist μ} (hθ : IsGalTwist σ θ) (p : Pl F) (hs : GM.Split E p) (D : Split (incFin E p) (galFin σ p) m)
    (e : Fin (m + 1) ≃ PlacesOver E p)
    (he : ∀ (b : CompletionsOver E p) i, completionMap p (e i).1 (D.e b i) = b (e i))
    {V : Submodule ℂ (LL μ)} (hV : V.map (θ.U : LL μ →ₗ[ℂ] LL μ) = V) (i : Fin (m + 1))
    (h : V ⊓ fixL μ (e (i + 1)).1 (GLnLocal.integralGL ((e (i + 1)).1.adicCompletion E) n) ≠ ⊥) :
    V ⊓ fixL μ (e i).1 (GLnLocal.integralGL ((e i).1.adicCompletion E) n) ≠ ⊥ := by
  obtain ⟨x, hx, hx0⟩ := (Submodule.ne_bot_iff _).1 h
  obtain ⟨hxV, hxf⟩ := Submodule.mem_inf.1 hx
  have hxf' := mem_fixL.1 hxf
  refine (Submodule.ne_bot_iff _).2 ⟨θ.U x, Submodule.mem_inf.2 ⟨?_, mem_fixL.2 fun k hk => ?_⟩, fun h0 => hx0 ?_⟩
  · rw [← hV]
    exact Submodule.mem_map_of_mem hxV
  · obtain ⟨⟨ε, hε⟩, hint, -⟩ := splitLoc F E p (e i) (hs _) n
    obtain ⟨-, hint', -⟩ := splitLoc F E p (e (i + 1)) (hs _) n
    obtain ⟨g, rfl⟩ : ∃ g, mapGL n (completionMap p (e i).1) g = k := by
      obtain ⟨g, hg⟩ := ε.surjective k
      exact ⟨g, (hε g).symm.trans hg⟩
    have hg := (hint g).1 hk
    have h2 := (twistPerm F E σ hσ m n μ θ hθ).2.1 p D e he i g x
    rw [hxf' _ ((hint' g).2 hg)] at h2
    exact h2.symm
  · have := (Dp.twUnitary E n μ θ).1 x
    rw [h0, norm_zero] at this
    exact norm_eq_zero.1 this.symm

end UpperTheory.ConvolutionTheory.Sph

/- English proof (translation)
Introduce `F E _ _ _ _ _ _ _ _ σ hσ hp n hn μ _ θ hθ V hV w w' hww h`. Set `u : PlacesOver E (w.under (𝓞 F))` to `⟨w, inferInstance⟩`. Establish `hl : w'.asIdeal.LiesOver (w.under (𝓞 F)).asIdeal`. Rewrite using `[hww]`. Use `infer_instance`.

Set `u' : PlacesOver E (w.under (𝓞 F))` to `⟨w', hl⟩`. Distinguish the cases in `hs : GM.Split E (w.under (𝓞 F))`. Take `⟨m, hm⟩ : ∃ m, Module.finrank F E = m + 1` from `⟨Module.finrank F E - 1, by have := hp.pos; omega⟩`. Take `⟨D, e, -, he⟩` from `finSplit F E σ hσ m hm _ u hs`. Establish `hstep` using `fun i => fix_step hσ hθ _ hs D e he hV i`.

Set `Q : PlacesOver E (w.under (𝓞 F)) → Prop` to `fun a => V ⊓ fixL μ a.1 (GLnLocal.integralGL (a.1.adicCompletion E) n) ≠ ⊥`. Take `⟨j, hj⟩` from `e.surjective u`. Take `⟨k, hk⟩` from `e.surjective u'`. Establish `hQ : Q (e k)` using `round_cycle (P := fun i => Q (e i)) hstep j k (by`. Express the relevant statement in the definitionally equal form `Q (e j)`.

Rewrite using `[hj]`. Conclude with `h)`. Rewrite `hQ` using `[hk]`. Conclude with `hQ`. Use `(T.places F E hp).2.2.2.1 _ hs u u'` as an intermediate fact.

Establish `hw : w' = w` using `congrArg Subtype.val this`. Substitute `hw` using the available equality. Conclude with `h`.
-/
theorem UpperTheory.ConvolutionTheory.Sph.sphConj :
    UpperTheory.ConvolutionTheory.Sph.SphConj := by
  intro F E _ _ _ _ _ _ _ _ σ hσ hp n hn μ _ θ hθ V hV w w' hww h
  let u : PlacesOver E (w.under (𝓞 F)) := ⟨w, inferInstance⟩
  have hl : w'.asIdeal.LiesOver (w.under (𝓞 F)).asIdeal := by
    rw [hww]
    infer_instance
  let u' : PlacesOver E (w.under (𝓞 F)) := ⟨w', hl⟩
  by_cases hs : GM.Split E (w.under (𝓞 F))
  · obtain ⟨m, hm⟩ : ∃ m, Module.finrank F E = m + 1 := ⟨Module.finrank F E - 1, by have := hp.pos; omega⟩
    obtain ⟨D, e, -, he⟩ := finSplit F E σ hσ m hm _ u hs
    have hstep := fun i => fix_step hσ hθ _ hs D e he hV i
    let Q : PlacesOver E (w.under (𝓞 F)) → Prop := fun a =>
      V ⊓ fixL μ a.1 (GLnLocal.integralGL (a.1.adicCompletion E) n) ≠ ⊥
    obtain ⟨j, hj⟩ := e.surjective u
    obtain ⟨k, hk⟩ := e.surjective u'
    have hQ : Q (e k) := round_cycle (P := fun i => Q (e i)) hstep j k (by
      change Q (e j)
      rw [hj]
      exact h)
    rw [hk] at hQ
    exact hQ
  · have := (T.places F E hp).2.2.2.1 _ hs u u'
    have hw : w' = w := congrArg Subtype.val this
    subst hw
    exact h

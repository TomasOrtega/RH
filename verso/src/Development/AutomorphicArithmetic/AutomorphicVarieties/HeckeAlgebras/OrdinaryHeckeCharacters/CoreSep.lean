import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.CoefficientRepTrivialOnUnramified
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.GalUnitary
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.SpecIntIff
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.PartAct0
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.HiComm
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Polynomial ValuativeRel IsLocalRing GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil UpperTheory.V UpperTheory.V.Hi
open UpperTheory.V.HV (Coef)
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

/- English proof (translation)
Set `s : Y →ₛₗ[φ] N` to `{ toFun := fun f => sp f map_add' := fun f f' => hadd _ f.2 _ f'.2 map_smul' := fun r f => hsmul _ f.2 r }`. Establish `h1 : s g = ∑ j ∈ (b.repr g).support, φ (b.repr g j) • sp (b j)` using `by conv_lhs => rw [← b.linearCombination_repr g, Finsupp.linearCombination_apply, Finsupp.sum, map_sum]`. Conclude with `Finset.sum_congr rfl fun j _ => s.map_smulₛₗ _ _`. Distinguish the cases in `hi : i ∈ (b.repr g).support`. Conclude with `linearIndependent_iff'.1 hind _ (fun j => φ (b.repr g j)) (h1.symm.trans hg) i hi`.

Rewrite using `[Finsupp.notMem_support_iff.1 hi, map_zero]`.
-/
private theorem coreSep_coord {A M N κ : Type} [CommRing A] [AddCommGroup M] [Module A M] [AddCommGroup N] [Module ℂ N]
    (Y : Submodule A M) (φ : A →+* ℂ) (sp : M → N) (hadd : ∀ f ∈ Y, ∀ f' ∈ Y, sp (f + f') = sp f + sp f')
    (hsmul : ∀ f ∈ Y, ∀ b : A, sp (b • f) = φ b • sp f) (b : Module.Basis κ A Y)
    (hind : LinearIndependent ℂ fun i => sp (b i)) (g : Y) (hg : sp g = 0) (i : κ) : φ (b.repr g i) = 0 := by
  classical
  let s : Y →ₛₗ[φ] N :=
    { toFun := fun f => sp f
      map_add' := fun f f' => hadd _ f.2 _ f'.2
      map_smul' := fun r f => hsmul _ f.2 r }
  have h1 : s g = ∑ j ∈ (b.repr g).support, φ (b.repr g j) • sp (b j) := by
    conv_lhs => rw [← b.linearCombination_repr g, Finsupp.linearCombination_apply, Finsupp.sum, map_sum]
    exact Finset.sum_congr rfl fun j _ => s.map_smulₛₗ _ _
  by_cases hi : i ∈ (b.repr g).support
  · exact linearIndependent_iff'.1 hind _ (fun j => φ (b.repr g j)) (h1.symm.trans hg) i hi
  · rw [Finsupp.notMem_support_iff.1 hi, map_zero]

/- English proof (translation)
Establish `hle : E ≤ (LinearMap.ker T).map E.subtype` using `by conv_lhs => rw [hE]`. Conclude with `iSup_le fun j G hG => ⟨⟨G, hG.2⟩, h j ⟨G, hG.2⟩ hG.1, rfl⟩`. Take `⟨G, hG, hGF⟩` from `hle F.2`. Establish `: G = F` using `Subtype.ext hGF`. Conclude with `this ▸ hG`.
-/
private theorem coreSep_kill {N J : Type*} [AddCommGroup N] [Module ℂ N] (E : Submodule ℂ N) (Y : J → Submodule ℂ N)
    (hE : E = ⨆ j, Y j ⊓ E) (T : Module.End ℂ E) (h : ∀ j, ∀ F : E, (F : N) ∈ Y j → T F = 0) (F : E) : T F = 0 := by
  have hle : E ≤ (LinearMap.ker T).map E.subtype := by
    conv_lhs => rw [hE]
    exact iSup_le fun j G hG => ⟨⟨G, hG.2⟩, h j ⟨G, hG.2⟩ hG.1, rfl⟩
  obtain ⟨G, hG, hGF⟩ := hle F.2
  have : G = F := Subtype.ext hGF
  exact this ▸ hG

/- English proof (translation)
Introduce `hLit L Ω _ _ _ _ _ l _ n c H hAx A _ _ _ θ hθ ι P hP a K _ lam hlam hD t ht`. Take `⟨-, -, hfree, -⟩` from `hiComm L Ω l n c H hAx A θ hθ K`. Set `b` to `Module.Free.chooseBasis A (H.X.Ord (H.τA A) θ (H.lev K))`. Use `Subtype.ext (LinearMap.ext fun f => ?_)` and prove the remaining obligations. Set `g : H.X.Ord (H.τA A) θ (H.lev K)` to `⟨((t : Module.End A (H.MK θ a K)) f : H.MK θ a K), ((t : Module.End A (H.MK θ a K)) f).2.1⟩`.

Establish `hg : g = 0`. Use `b.repr.injective (Finsupp.ext fun i => ?_)` and prove the remaining obligations. Rewrite using `[map_zero, Finsupp.zero_apply]`. Use `hD _ fun x hx => ?_` and prove the remaining obligations. Take `⟨d, ξ, c0, sp, hsp⟩` from `spec L Ω l n c H hAx A θ hθ ι x lam hx.2.1`.

Take `⟨h1, act, h2, -, -, -, h3⟩` from `partAct0 hLit L Ω l n c H hAx A θ hθ ι P hP x lam d ξ c0 sp hsp hlam a K _ rfl`. Establish `hE` using `h1.resolve_right (not_not.2 hx)`. Establish `h0` using `coreSep_kill _ _ hE (act t) (fun Y F hF => by`. Distinguish the cases in `hb : Y.1.Y ⊓ Submodule.span ℂ (sp '' H.MK θ a K) = ⊥`. Establish `: F = 0` using `Subtype.ext ((Submodule.eq_bot_iff _).1 hb _ ⟨hF, F.2⟩)`.

Rewrite using `[this, map_zero]`. Take `⟨y, hy, hact⟩` from `h3 hx Y.1 hb`. Rewrite using `[hact t F hF, ht y (hy ▸ hx), map_zero, zero_smul])`. Use the proof step `⟨sp f, Submodule.subset_span ⟨f, f.2, rfl⟩⟩`. Establish `h4` using `h2 t f ⟨sp f, Submodule.subset_span ⟨f, f.2, rfl⟩⟩ rfl`.

Rewrite `h4` using `[h0]`. Establish `h5` using `coreSep_coord _ (ι.toRingHom.comp x.toRingHom) sp (hsp.add K) (hsp.smul K) b (hsp.indep K _ b) g h4.symm i`. Conclude with `ι.injective (h5.trans (map_zero ι).symm)`. Conclude with `Subtype.ext (congrArg (fun z : H.X.Ord (H.τA A) θ (H.lev K) => (z : H.X.Fn A H.m)) hg)`.
-/
theorem UpperTheory.V.Hi.coreSep :
    GlobalTheory.Mem.LiteralAutomorphy.LitN → ∀ (L Ω : Type) [Field L] [NumberField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] (l : ℕ) [Fact l.Prime] (n : ℕ) (c : Coef l) (H : HSet L Ω l n c), H.Ax →
    ∀ (A : Type) [CommRing A] [Algebra c.O A] [Alg.IsCO c.O A] (θ : H.X.I.T →* Aˣ), H.IsWt θ →
    ∀ (ι : Qbar l ≃+* ℂ) (P : Wt L l n → (H.Gq →* GL (Fin n) (Qbar l)) → Prop), H.Aut ι P →
    ∀ (a : H.Op → c.O) (K : H.Lev) [Fact (CommOn (H.MK θ a K) (H.op A))], ∀ lam ∈ H.admitted, H.DenseWt θ lam → ∀ t : H.TK θ a K, (∀ x : H.TK θ a K →ₐ[c.O] Qbar l, H.Good θ (x.toRingHom.comp (algebraMap A _)) lam → x t = 0) → t = 0 := by
  intro hLit L Ω _ _ _ _ _ l _ n c H hAx A _ _ _ θ hθ ι P hP a K _ lam hlam hD t ht
  obtain ⟨-, -, hfree, -⟩ := hiComm L Ω l n c H hAx A θ hθ K
  let b := Module.Free.chooseBasis A (H.X.Ord (H.τA A) θ (H.lev K))
  refine Subtype.ext (LinearMap.ext fun f => ?_)
  let g : H.X.Ord (H.τA A) θ (H.lev K) :=
    ⟨((t : Module.End A (H.MK θ a K)) f : H.MK θ a K), ((t : Module.End A (H.MK θ a K)) f).2.1⟩
  have hg : g = 0 := by
    refine b.repr.injective (Finsupp.ext fun i => ?_)
    rw [map_zero, Finsupp.zero_apply]
    refine hD _ fun x hx => ?_
    obtain ⟨d, ξ, c0, sp, hsp⟩ := spec L Ω l n c H hAx A θ hθ ι x lam hx.2.1
    obtain ⟨h1, act, h2, -, -, -, h3⟩ := partAct0 hLit L Ω l n c H hAx A θ hθ ι P hP x lam d ξ c0 sp hsp hlam a K _ rfl
    have hE := h1.resolve_right (not_not.2 hx)
    have h0 := coreSep_kill _ _ hE (act t) (fun Y F hF => by
      by_cases hb : Y.1.Y ⊓ Submodule.span ℂ (sp '' H.MK θ a K) = ⊥
      · have : F = 0 := Subtype.ext ((Submodule.eq_bot_iff _).1 hb _ ⟨hF, F.2⟩)
        rw [this, map_zero]
      · obtain ⟨y, hy, hact⟩ := h3 hx Y.1 hb
        rw [hact t F hF, ht y (hy ▸ hx), map_zero, zero_smul])
      ⟨sp f, Submodule.subset_span ⟨f, f.2, rfl⟩⟩
    have h4 := h2 t f ⟨sp f, Submodule.subset_span ⟨f, f.2, rfl⟩⟩ rfl
    rw [h0] at h4
    have h5 := coreSep_coord _ (ι.toRingHom.comp x.toRingHom) sp (hsp.add K) (hsp.smul K) b (hsp.indep K _ b) g h4.symm i
    exact ι.injective (h5.trans (map_zero ι).symm)
  exact Subtype.ext (congrArg (fun z : H.X.Ord (H.τA A) θ (H.lev K) => (z : H.X.Fn A H.m)) hg)

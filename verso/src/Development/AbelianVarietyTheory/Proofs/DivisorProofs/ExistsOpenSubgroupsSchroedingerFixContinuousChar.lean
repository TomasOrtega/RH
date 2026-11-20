import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsTransportF
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsContOnOfLocal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TransportedWeilDatumCMPreservesSchwartzHeisenberStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSubgroupAddCharDotProductTrivialOnCompactStatement
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped Classical

noncomputable section

namespace GlobalTheory.SchrFixFin

variable {F : Type} [Field F] [NumberField F]

/- English proof (translation)
Rewrite `hU` using `[hf.nhds_eq_comap, map_zero, Filter.mem_comap]`. Take `⟨t, ht, hsub⟩` from `hU`. Take `⟨V, hV⟩` from `NonarchimedeanAddGroup.is_nonarchimedean t ht`. Conclude with `⟨V.comap f hf.continuous, fun x hx => hsub (hV hx)⟩`.
-/
theorem nonarch_of_inducing {G S : Type} [AddGroup G] [TopologicalSpace G] [NonarchimedeanAddGroup G]
    [AddGroup S] [TopologicalSpace S] [IsTopologicalAddGroup S] (f : S →+ G) (hf : Topology.IsInducing f) :
    NonarchimedeanAddGroup S where
  is_nonarchimedean U hU := by
    rw [hf.nhds_eq_comap, map_zero, Filter.mem_comap] at hU
    obtain ⟨t, ht, hsub⟩ := hU
    obtain ⟨V, hV⟩ := NonarchimedeanAddGroup.is_nonarchimedean t ht
    exact ⟨V.comap f hf.continuous, fun x hx => hsub (hV hx)⟩

/- English proof (translation)
Rewrite `hU` using `[nhds_pi, Filter.mem_pi]`. Take `⟨I, hI, t, ht, hs⟩` from `hU`. Use `choose K hK using fun i => NonarchimedeanAddGroup.is_nonarchimedean (G := G i) (t i) (ht i)`. Conclude with `⟨⟨AddSubgroup.pi I fun i => (K i : AddSubgroup (G i)), isOpen_set_pi hI fun i _ => (K i).isOpen⟩, fun x hx => hs fun i hi => hK i (hx i hi)⟩`.
-/
theorem nonarch_pi' {ι : Type} {G : ι → Type} [∀ i, AddGroup (G i)] [∀ i, TopologicalSpace (G i)]
    [∀ i, NonarchimedeanAddGroup (G i)] : NonarchimedeanAddGroup (∀ i, G i) where
  is_nonarchimedean U hU := by
    rw [nhds_pi, Filter.mem_pi] at hU
    obtain ⟨I, hI, t, ht, hs⟩ := hU
    choose K hK using fun i => NonarchimedeanAddGroup.is_nonarchimedean (G := G i) (t i) (ht i)
    exact ⟨⟨AddSubgroup.pi I fun i => (K i : AddSubgroup (G i)), isOpen_set_pi hI fun i _ => (K i).isOpen⟩,
      fun x hx => hs fun i hi => hK i (hx i hi)⟩

variable (F) in

/- English proof (translation)
Use `haveI : ∀ v : HeightOneSpectrum (𝓞 F), NonarchimedeanAddGroup (v.adicCompletionIntegers F) := fun v => nonarch_of_inducing (v.adicCompletionIntegers F).subtype.toAddMonoidHom Topology.IsInducing.subtypeVal`. Use `haveI := nonarch_pi' (G := fun v : HeightOneSpectrum (𝓞 F) => v.adicCompletionIntegers F)`. Set `f : (∀ v : HeightOneSpectrum (𝓞 F), v.adicCompletionIntegers F) →+ FiniteAdeleRing (𝓞 F) F` to `{ toFun := RestrictedProduct.structureMap (fun v : HeightOneSpectrum (𝓞 F) => v.adicCompletion F) (fun v => (v.adicCompletionIntegers F : Set (v.adicCompletion F))) Filter.cofinite map_zero' := rfl map_add' := fun _ _ => rfl }`. Conclude with `NonarchimedeanAddGroup.nonarchimedean_of_emb f (RestrictedProduct.isOpenEmbedding_structureMap (fun v => Valued.isOpen_integer _))`.
-/
theorem nonarch_finAdeles : NonarchimedeanAddGroup (FiniteAdeleRing (𝓞 F) F) := by
  haveI : ∀ v : HeightOneSpectrum (𝓞 F), NonarchimedeanAddGroup (v.adicCompletionIntegers F) := fun v =>
    nonarch_of_inducing (v.adicCompletionIntegers F).subtype.toAddMonoidHom Topology.IsInducing.subtypeVal
  haveI := nonarch_pi' (G := fun v : HeightOneSpectrum (𝓞 F) => v.adicCompletionIntegers F)
  let f : (∀ v : HeightOneSpectrum (𝓞 F), v.adicCompletionIntegers F) →+ FiniteAdeleRing (𝓞 F) F :=
    { toFun := RestrictedProduct.structureMap (fun v : HeightOneSpectrum (𝓞 F) => v.adicCompletion F)
        (fun v => (v.adicCompletionIntegers F : Set (v.adicCompletion F))) Filter.cofinite
      map_zero' := rfl
      map_add' := fun _ _ => rfl }
  exact NonarchimedeanAddGroup.nonarchimedean_of_emb f
    (RestrictedProduct.isOpenEmbedding_structureMap (fun v => Valued.isOpen_integer _))

def transFix {M : Type} [AddCommGroup M] (Φ : M → ℂ) : AddSubgroup M where
  carrier := {u | ∀ x, Φ (x + u) = Φ x}
  zero_mem' := fun x => by rw [add_zero]
  add_mem' := fun {a b} ha hb x => by rw [← add_assoc, hb, ha]
  neg_mem' := fun {a} ha x => by
    have := ha (x + -a)
    rw [neg_add_cancel_right] at this
    exact this.symm

/- English proof (translation)
Establish `h : ∀ᶠ u in nhds (0 : M), ∀ x ∈ tsupport Φ, Φ (x + u) = Φ x ∧ Φ (x - u) = Φ x`. Apply `h2.isCompact.eventually_forall_of_forall_eventually` to reduce the goal to its premises. Introduce `x _`. Establish `a1` using `(h1.comp_continuous (show Continuous fun z : M × M => z.2 + z.1 by fun_prop)).eventually_eq (0, x)`. Establish `a2` using `(h1.comp_continuous (show Continuous fun z : M × M => z.2 - z.1 by fun_prop)).eventually_eq (0, x)`.

Establish `a3` using `(h1.comp_continuous (show Continuous fun z : M × M => z.2 by fun_prop)).eventually_eq (0, x)`. Use `filter_upwards [a1, a2, a3] with z b1 b2 b3`. Simplify using `only [Function.comp, add_zero, sub_zero] at b1 b2 b3`. Conclude with `⟨b1.trans b3.symm, b2.trans b3.symm⟩`. Establish `key : ∀ᶠ u in nhds (0 : M), ∀ x, Φ (x + u) = Φ x` using `by filter_upwards [h] with u hu x`.

Distinguish the cases in `hx : x ∈ tsupport Φ`. Conclude with `(hu x hx).1`. Distinguish the cases in `hx' : x + u ∈ tsupport Φ`. Use `(hu _ hx').2` as an intermediate fact. Rewrite `this` using `[add_sub_cancel_right]`.

Conclude with `this.symm`. Rewrite using `[image_eq_zero_of_notMem_tsupport hx, image_eq_zero_of_notMem_tsupport hx']`. Conclude with `AddSubgroup.isOpen_of_mem_nhds _ key`.
-/
theorem isOpen_transFix {M : Type} [AddCommGroup M] [TopologicalSpace M] [IsTopologicalAddGroup M] {Φ : M → ℂ}
    (h1 : IsLocallyConstant Φ) (h2 : HasCompactSupport Φ) : IsOpen (transFix Φ : Set M) := by
  have h : ∀ᶠ u in nhds (0 : M), ∀ x ∈ tsupport Φ, Φ (x + u) = Φ x ∧ Φ (x - u) = Φ x := by
    apply h2.isCompact.eventually_forall_of_forall_eventually
    intro x _
    have a1 := (h1.comp_continuous (show Continuous fun z : M × M => z.2 + z.1 by fun_prop)).eventually_eq (0, x)
    have a2 := (h1.comp_continuous (show Continuous fun z : M × M => z.2 - z.1 by fun_prop)).eventually_eq (0, x)
    have a3 := (h1.comp_continuous (show Continuous fun z : M × M => z.2 by fun_prop)).eventually_eq (0, x)
    filter_upwards [a1, a2, a3] with z b1 b2 b3
    simp only [Function.comp, add_zero, sub_zero] at b1 b2 b3
    exact ⟨b1.trans b3.symm, b2.trans b3.symm⟩
  have key : ∀ᶠ u in nhds (0 : M), ∀ x, Φ (x + u) = Φ x := by
    filter_upwards [h] with u hu x
    by_cases hx : x ∈ tsupport Φ
    · exact (hu x hx).1
    · by_cases hx' : x + u ∈ tsupport Φ
      · have := (hu _ hx').2
        rw [add_sub_cancel_right] at this
        exact this.symm
      · rw [image_eq_zero_of_notMem_tsupport hx, image_eq_zero_of_notMem_tsupport hx']
  exact AddSubgroup.isOpen_of_mem_nhds _ key

/- English proof (translation)
Use `Prod.ext ?_ rfl` and prove the remaining obligations. Use `show (InfiniteAdeleRing.ringEquiv_mixedSpace F).symm 0 = 0`. Conclude with `map_zero _`.
-/
theorem adeleJoin_zero {κ : Type} (y : κ → FiniteAdeleRing (𝓞 F) F) (i : κ) :
    GlobalTheory.WeilCont.adeleJoin F 0 y i = ((0 : InfiniteAdeleRing F), y i) := by
  refine Prod.ext ?_ rfl
  show (InfiniteAdeleRing.ringEquiv_mixedSpace F).symm 0 = 0
  exact map_zero _

/- English proof (translation)
Set `p1 : AdeleRing (𝓞 F) F →+* InfiniteAdeleRing F` to `RingHom.fst _ _`. Set `p2 : AdeleRing (𝓞 F) F →+* FiniteAdeleRing (𝓞 F) F` to `RingHom.snd _ _`. Establish `e1 : ∀ s : AdeleRing (𝓞 F) F, s.1 = p1 s` using `fun _ => rfl`. Establish `e2 : ∀ s : AdeleRing (𝓞 F) F, s.2 = p2 s` using `fun _ => rfl`. Use `Prod.ext ?_ ?_` and prove the remaining obligations.

Rewrite using `[e1, dotProduct, map_sum]`. Use `Finset.sum_eq_zero fun i _ => ?_` and prove the remaining obligations. Rewrite using `[map_mul, adeleJoin_zero]`. Conclude with `mul_zero _`. Rewrite using `[e2, dotProduct, map_sum]`.

Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[map_mul, adeleJoin_zero]`. Both sides reduce to the same expression.
-/
theorem dot_adeleJoin_zero {κ : Type} [Fintype κ] (v : κ → AdeleRing (𝓞 F) F) (y : κ → FiniteAdeleRing (𝓞 F) F) :
    v ⬝ᵥ GlobalTheory.WeilCont.adeleJoin F 0 y = ((0 : InfiniteAdeleRing F), (fun i => (v i).2) ⬝ᵥ y) := by
  let p1 : AdeleRing (𝓞 F) F →+* InfiniteAdeleRing F := RingHom.fst _ _
  let p2 : AdeleRing (𝓞 F) F →+* FiniteAdeleRing (𝓞 F) F := RingHom.snd _ _
  have e1 : ∀ s : AdeleRing (𝓞 F) F, s.1 = p1 s := fun _ => rfl
  have e2 : ∀ s : AdeleRing (𝓞 F) F, s.2 = p2 s := fun _ => rfl
  refine Prod.ext ?_ ?_
  · rw [e1, dotProduct, map_sum]
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [map_mul, adeleJoin_zero]
    exact mul_zero _
  · rw [e2, dotProduct, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_mul, adeleJoin_zero]
    rfl

/- English proof (translation)
Use `haveI := nonarch_finAdeles F`. Set `χ : AddChar (FiniteAdeleRing (𝓞 F) F) ℂ` to `ψ.compAddMonoidHom (AddMonoidHom.inr (InfiniteAdeleRing F) (FiniteAdeleRing (𝓞 F) F))`. Establish `hχ : Continuous χ` using `hψ.comp (continuous_const.prodMk continuous_id)`. Take `⟨H, hH⟩` from `GlobalTheory.T.exists_subgroup_addChar_dotProduct_trivial_on_compact χ hχ κ (tsupport g) hg.2.isCompact`. Set `c : FiniteAdeleRing (𝓞 F) F` to `(⅟(2 : AdeleRing (𝓞 F) F)).2`.

Use `⟨transFix g ⊓ (H : AddSubgroup (κ → FiniteAdeleRing (𝓞 F) F)).comap (DistribSMul.toAddMonoidHom (κ → FiniteAdeleRing (𝓞 F) F) c), H, ?_, H.isOpen, ?_⟩` and prove the remaining obligations. Rewrite using `[AddSubgroup.coe_inf]`. Conclude with `(isOpen_transFix hg.1 hg.2).inter (H.isOpen.preimage (continuous_const_smul c))`. Introduce and unpack `x ⟨hx1, hx2⟩ y hy`. Use function extensionality and compare the values at `z`.

Establish `hf : (fun i => InfiniteAdeleRing.ringEquiv_mixedSpace F ((z + GlobalTheory.WeilCont.adeleJoin F 0 x) i).1) = fun i => InfiniteAdeleRing.ringEquiv_mixedSpace F (z i).1`. Use function extensionality and compare the values at `i`. Rewrite using `[Pi.add_apply, adeleJoin_zero]`. Conclude with `congrArg _ (add_zero (z i).1)`. Establish `hgz : (fun i => ((z + GlobalTheory.WeilCont.adeleJoin F 0 x) i).2) = (fun i => (z i).2) + x`.

Use function extensionality and compare the values at `i`. Rewrite using `[Pi.add_apply, adeleJoin_zero]`. Both sides reduce to the same expression. Establish `hz : pureA F f g (z + GlobalTheory.WeilCont.adeleJoin F 0 x) = pureA F f g z`. Simplify using `only [pureA]`.

Rewrite using `[hf, hgz, hx1]`. Simplify using `only [schr]`. Rewrite using `[hz]`. Distinguish the cases in `hg0 : g (fun i => (z i).2) = 0`. Simplify using `only [pureA, hg0, mul_zero]`.

Establish `hzc : (fun i => (z i).2) ∈ tsupport g` using `subset_tsupport _ hg0`. Establish `harg : z ⬝ᵥ GlobalTheory.WeilCont.adeleJoin F 0 y + ⅟(2 : AdeleRing (𝓞 F) F) * (GlobalTheory.WeilCont.adeleJoin F 0 x ⬝ᵥ GlobalTheory.WeilCont.adeleJoin F 0 y) = ((0 : InfiniteAdeleRing F), (fun i => (z i).2) ⬝ᵥ y + (c • x) ⬝ᵥ y)`. Rewrite using `[dot_adeleJoin_zero, dot_adeleJoin_zero, smul_dotProduct]`. Use `Prod.ext ?_ ?_` and prove the remaining obligations. Use `show (0 : InfiniteAdeleRing F) + (⅟(2 : AdeleRing (𝓞 F) F)).1 * 0 = 0`.

Rewrite using `[mul_zero, add_zero]`. Use `show (fun i => (z i).2) ⬝ᵥ y + c * ((fun i => (GlobalTheory.WeilCont.adeleJoin F 0 x i).2) ⬝ᵥ y) = _`. Both sides reduce to the same expression. Rewrite using `[harg]`. Establish `h1 : ψ ((0 : InfiniteAdeleRing F), (fun i => (z i).2) ⬝ᵥ y + (c • x) ⬝ᵥ y) = 1` using `hH _ hzc (c • x) hx2 y hy`.

Rewrite using `[h1, one_mul]`.
-/
theorem exists_fix_pure (ψ : AddChar (AdeleRing (𝓞 F) F) ℂ) (hψ : Continuous ψ) (κ : Type) [Fintype κ]
    (f : SchwartzMap (κ → mixedEmbedding.mixedSpace F) ℂ) (g : (κ → FiniteAdeleRing (𝓞 F) F) → ℂ)
    (hg : g ∈ SB (κ → FiniteAdeleRing (𝓞 F) F)) :
    ∃ L₁ L₂ : AddSubgroup (κ → FiniteAdeleRing (𝓞 F) F),
      IsOpen (L₁ : Set (κ → FiniteAdeleRing (𝓞 F) F)) ∧ IsOpen (L₂ : Set (κ → FiniteAdeleRing (𝓞 F) F)) ∧
      ∀ x ∈ L₁, ∀ y ∈ L₂, schr ψ (GlobalTheory.WeilCont.adeleJoin F 0 x, GlobalTheory.WeilCont.adeleJoin F 0 y) (pureA F f g) =
        pureA F f g := by
  haveI := nonarch_finAdeles F
  let χ : AddChar (FiniteAdeleRing (𝓞 F) F) ℂ :=
    ψ.compAddMonoidHom (AddMonoidHom.inr (InfiniteAdeleRing F) (FiniteAdeleRing (𝓞 F) F))
  have hχ : Continuous χ := hψ.comp (continuous_const.prodMk continuous_id)
  obtain ⟨H, hH⟩ := GlobalTheory.T.exists_subgroup_addChar_dotProduct_trivial_on_compact χ hχ κ (tsupport g) hg.2.isCompact
  let c : FiniteAdeleRing (𝓞 F) F := (⅟(2 : AdeleRing (𝓞 F) F)).2
  refine ⟨transFix g ⊓ (H : AddSubgroup (κ → FiniteAdeleRing (𝓞 F) F)).comap
    (DistribSMul.toAddMonoidHom (κ → FiniteAdeleRing (𝓞 F) F) c), H, ?_, H.isOpen, ?_⟩
  · rw [AddSubgroup.coe_inf]
    exact (isOpen_transFix hg.1 hg.2).inter (H.isOpen.preimage (continuous_const_smul c))
  rintro x ⟨hx1, hx2⟩ y hy
  funext z
  have hf : (fun i => InfiniteAdeleRing.ringEquiv_mixedSpace F ((z + GlobalTheory.WeilCont.adeleJoin F 0 x) i).1) =
      fun i => InfiniteAdeleRing.ringEquiv_mixedSpace F (z i).1 := by
    funext i
    rw [Pi.add_apply, adeleJoin_zero]
    exact congrArg _ (add_zero (z i).1)
  have hgz : (fun i => ((z + GlobalTheory.WeilCont.adeleJoin F 0 x) i).2) = (fun i => (z i).2) + x := by
    funext i
    rw [Pi.add_apply, adeleJoin_zero]
    rfl
  have hz : pureA F f g (z + GlobalTheory.WeilCont.adeleJoin F 0 x) = pureA F f g z := by
    simp only [pureA]
    rw [hf, hgz, hx1]
  simp only [schr]
  rw [hz]
  by_cases hg0 : g (fun i => (z i).2) = 0
  · simp only [pureA, hg0, mul_zero]
  have hzc : (fun i => (z i).2) ∈ tsupport g := subset_tsupport _ hg0
  have harg : z ⬝ᵥ GlobalTheory.WeilCont.adeleJoin F 0 y + ⅟(2 : AdeleRing (𝓞 F) F) *
      (GlobalTheory.WeilCont.adeleJoin F 0 x ⬝ᵥ GlobalTheory.WeilCont.adeleJoin F 0 y) =
      ((0 : InfiniteAdeleRing F), (fun i => (z i).2) ⬝ᵥ y + (c • x) ⬝ᵥ y) := by
    rw [dot_adeleJoin_zero, dot_adeleJoin_zero, smul_dotProduct]
    refine Prod.ext ?_ ?_
    · show (0 : InfiniteAdeleRing F) + (⅟(2 : AdeleRing (𝓞 F) F)).1 * 0 = 0
      rw [mul_zero, add_zero]
    · show (fun i => (z i).2) ⬝ᵥ y + c * ((fun i => (GlobalTheory.WeilCont.adeleJoin F 0 x i).2) ⬝ᵥ y) = _
      rfl
  rw [harg]
  have h1 : ψ ((0 : InfiniteAdeleRing F), (fun i => (z i).2) ⬝ᵥ y + (c • x) ⬝ᵥ y) = 1 :=
    hH _ hzc (c • x) hx2 y hy
  rw [h1, one_mul]

/- English proof (translation)
Introduce `F _ _ ψ hψ κ _ Φ hΦ`. Proceed by induction on `hΦ using Submodule.span_induction with`. Consider the case `mem Φ h`. Take `⟨f, g, hg, rfl⟩` from `h`. Conclude with `exists_fix_pure ψ hψ κ f g hg`.

Consider the case `zero`. Use `⟨⊤, ⊤, isOpen_univ, isOpen_univ, fun x _ y _ => ?_⟩` and prove the remaining obligations. Use function extensionality and compare the values at `z`. Simplify using `[schr]`. Consider the case `add Φ Ψ _ _ h1 h2`.

Take `⟨L₁, L₂, o₁, o₂, h⟩` from `h1`. Take `⟨M₁, M₂, p₁, p₂, h'⟩` from `h2`. Use `⟨L₁ ⊓ M₁, L₂ ⊓ M₂, by rw [AddSubgroup.coe_inf]; exact o₁.inter p₁, by rw [AddSubgroup.coe_inf]; exact o₂.inter p₂, fun x hx y hy => ?_⟩` and prove the remaining obligations. Establish `e1` using `h x hx.1 y hy.1`. Establish `e2` using `h' x hx.2 y hy.2`.

Use function extensionality and compare the values at `z`. Establish `a1` using `congrFun e1 z`. Establish `a2` using `congrFun e2 z`. Simplify using `only [schr, Pi.add_apply] at a1 a2 ⊢`. Rewrite using `[mul_add, a1, a2]`.

Consider the case `smul a Φ _ h`. Take `⟨L₁, L₂, o₁, o₂, h⟩` from `h`. Use `⟨L₁, L₂, o₁, o₂, fun x hx y hy => ?_⟩` and prove the remaining obligations. Use function extensionality and compare the values at `z`. Establish `a1` using `congrFun (h x hx y hy) z`.

Simplify using `only [schr, Pi.smul_apply, smul_eq_mul] at a1 ⊢`. Rewrite using `[mul_left_comm, a1]`.
-/
theorem exists_fix : ∀ (F : Type) [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ), Continuous ψ →
    ∀ (κ : Type) [Fintype κ], ∀ Φ ∈ schA F κ,
      ∃ L₁ L₂ : AddSubgroup (κ → FiniteAdeleRing (𝓞 F) F),
        IsOpen (L₁ : Set (κ → FiniteAdeleRing (𝓞 F) F)) ∧ IsOpen (L₂ : Set (κ → FiniteAdeleRing (𝓞 F) F)) ∧
        ∀ x ∈ L₁, ∀ y ∈ L₂, schr ψ (GlobalTheory.WeilCont.adeleJoin F 0 x, GlobalTheory.WeilCont.adeleJoin F 0 y) Φ = Φ := by
  intro F _ _ ψ hψ κ _ Φ hΦ
  induction hΦ using Submodule.span_induction with
  | mem Φ h =>
    obtain ⟨f, g, hg, rfl⟩ := h
    exact exists_fix_pure ψ hψ κ f g hg
  | zero =>
    refine ⟨⊤, ⊤, isOpen_univ, isOpen_univ, fun x _ y _ => ?_⟩
    funext z
    simp [schr]
  | add Φ Ψ _ _ h1 h2 =>
    obtain ⟨L₁, L₂, o₁, o₂, h⟩ := h1
    obtain ⟨M₁, M₂, p₁, p₂, h'⟩ := h2
    refine ⟨L₁ ⊓ M₁, L₂ ⊓ M₂, by rw [AddSubgroup.coe_inf]; exact o₁.inter p₁,
      by rw [AddSubgroup.coe_inf]; exact o₂.inter p₂, fun x hx y hy => ?_⟩
    have e1 := h x hx.1 y hy.1
    have e2 := h' x hx.2 y hy.2
    funext z
    have a1 := congrFun e1 z
    have a2 := congrFun e2 z
    simp only [schr, Pi.add_apply] at a1 a2 ⊢
    rw [mul_add, a1, a2]
  | smul a Φ _ h =>
    obtain ⟨L₁, L₂, o₁, o₂, h⟩ := h
    refine ⟨L₁, L₂, o₁, o₂, fun x hx y hy => ?_⟩
    funext z
    have a1 := congrFun (h x hx y hy) z
    simp only [schr, Pi.smul_apply, smul_eq_mul] at a1 ⊢
    rw [mul_left_comm, a1]

end GlobalTheory.SchrFixFin

end

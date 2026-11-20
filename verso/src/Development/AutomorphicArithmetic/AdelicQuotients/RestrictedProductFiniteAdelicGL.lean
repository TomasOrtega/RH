import Development.AutomorphicArithmetic.Foundations.Convolution.LocalGroupAnalysis.SelmerRankBoundLaurent
import GroundTheory.AutomorphicForms.ReductionFinite

open NumberField IsDedekindDomain Topology Filter
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction
open PositivityTheory.Rg.Tf.Geo UpperTheory.ConvolutionTheory.G UpperTheory.ConvolutionTheory.T4
open scoped NumberField.AdeleRing RestrictedProduct

namespace UpperTheory.OpenSubgroupProjection

variable (K : Type) [Field K] [NumberField K] (n : ℕ)

private abbrev RF : Type :=
  Πʳ v : Pl K, [GL (Fin n) (v.adicCompletion K), KF K n v]

/- English proof (translation)
Apply `Units.ext` to reduce the goal to its premises. Use extensionality with `a b`. Both sides reduce to the same expression.
-/
private theorem fst_eq (g : GA K n) : (AdelicGLn.prodEquiv K n g).1 = pI K n g := by
  apply Units.ext; ext a b; rfl

/- English proof (translation)
The claim follows from `GLnLocal.isOpen_integralGL _ n`.
-/
private theorem opn (v : Pl K) : IsOpen (KF K n v : Set (GL (Fin n) (v.adicCompletion K))) :=
  GLnLocal.isOpen_integralGL _ n

/- English proof (translation)
The claim follows from `GLnLocal.isCompact_integralGL _ n`.
-/
private theorem cpt (v : Pl K) : IsCompact (KF K n v : Set (GL (Fin n) (v.adicCompletion K))) :=
  GLnLocal.isCompact_integralGL _ n

private noncomputable def phi : GA K n ≃ₜ GL (Fin n) (InfiniteAdeleRing K) × RF K n :=
  (AdelicGLn.prodEquiv K n).toHomeomorph.trans
    (Homeomorph.prodCongr (Homeomorph.refl _) (AdelicGLn.finiteRestrictedEquiv K n).toHomeomorph)

/- English proof (translation)
The claim follows from `fst_eq K n g`.
-/
private theorem phi_fst (g : GA K n) : (phi K n g).1 = pI K n g := fst_eq K n g

/- English proof (translation)
Both sides reduce to the same expression.
-/
private theorem phi_snd (g : GA K n) (v : Pl K) : (phi K n g).2 v = pF K n v g := rfl

/- English proof (translation)
Set `A : Set (Pl K)` to `{v | C v ⊆ (KF K n v : Set (GL (Fin n) (v.adicCompletion K)))}`. Establish `hle : (cofinite : Filter (Pl K)) ≤ 𝓟 A` using `le_principal_iff.2 hK`. Establish `hemb : IsEmbedding (DFunLike.coe : (Πʳ v : Pl K, [GL (Fin n) (v.adicCompletion K), KF K n v]_[𝓟 A]) → ∀ v : Pl K, GL (Fin n) (v.adicCompletion K))` using `RestrictedProduct.isEmbedding_coe_of_principal`. Establish `hT : IsCompact (Set.pi Set.univ C)` using `isCompact_univ_pi hC`. Establish `hsub : Set.pi Set.univ C ⊆ Set.range (DFunLike.coe : (Πʳ v : Pl K, [GL (Fin n) (v.adicCompletion K), KF K n v]_[𝓟 A]) → ∀ v : Pl K, GL (Fin n) (v.adicCompletion K))` using `fun x hx => ⟨⟨x, eventually_principal.2 fun v hv => hv (hx v trivial)⟩, rfl⟩`.

Establish `h1` using `(hemb.isInducing.isCompact_preimage_iff hsub).2 hT`. Establish `h2` using `h1.image (RestrictedProduct.continuous_inclusion hle)`. Use `h2 using 1` and compare the differences between its conclusion and the goal. Use extensionality with `x`. Prove the components needed by the constructor for the conclusion.

Introduce `hx`. Conclude with `⟨⟨x, eventually_principal.2 fun v hv => hv (hx v)⟩, fun v _ => hx v, rfl⟩`. Introduce and unpack `⟨y, hy, rfl⟩ v`. Conclude with `hy v trivial`.
-/
private theorem compact_box (C : ∀ v : Pl K, Set (GL (Fin n) (v.adicCompletion K)))
    (hC : ∀ v, IsCompact (C v))
    (hK : ∀ᶠ v in cofinite, C v ⊆ (KF K n v : Set (GL (Fin n) (v.adicCompletion K)))) :
    IsCompact {x : RF K n | ∀ v, x v ∈ C v} := by
  let A : Set (Pl K) := {v | C v ⊆ (KF K n v : Set (GL (Fin n) (v.adicCompletion K)))}
  have hle : (cofinite : Filter (Pl K)) ≤ 𝓟 A := le_principal_iff.2 hK
  have hemb : IsEmbedding (DFunLike.coe : (Πʳ v : Pl K, [GL (Fin n) (v.adicCompletion K), KF K n v]_[𝓟 A]) →
      ∀ v : Pl K, GL (Fin n) (v.adicCompletion K)) := RestrictedProduct.isEmbedding_coe_of_principal
  have hT : IsCompact (Set.pi Set.univ C) := isCompact_univ_pi hC
  have hsub : Set.pi Set.univ C ⊆ Set.range (DFunLike.coe :
      (Πʳ v : Pl K, [GL (Fin n) (v.adicCompletion K), KF K n v]_[𝓟 A]) →
      ∀ v : Pl K, GL (Fin n) (v.adicCompletion K)) := fun x hx =>
    ⟨⟨x, eventually_principal.2 fun v hv => hv (hx v trivial)⟩, rfl⟩
  have h1 := (hemb.isInducing.isCompact_preimage_iff hsub).2 hT
  have h2 := h1.image (RestrictedProduct.continuous_inclusion hle)
  convert h2 using 1
  ext x
  constructor
  · intro hx
    exact ⟨⟨x, eventually_principal.2 fun v hv => hv (hx v)⟩, fun v _ => hx v, rfl⟩
  · rintro ⟨y, hy, rfl⟩ v
    exact hy v trivial

/- English proof (translation)
Establish `h0 : IsOpen (US (pF K n) (KF K n) ∅ : Set (GA K n))`. Establish `: (US (pF K n) (KF K n) ∅ : Set (GA K n)) = (fun g => (AdelicGLn.prodEquiv K n g).2) ⁻¹' (AdelicGLn.integralFiniteGL K n : Set (AdelicGLn.FiniteAdelicGL K n))`. Use extensionality with `g`. Simplify using `only [Set.mem_preimage, SetLike.mem_coe, AdelicGLn.mem_integralFiniteGL_iff_forall, mem_US]`. Conclude with `⟨fun h v => h v (Finset.notMem_empty v), fun h v _ => h v⟩`.

Rewrite using `[this]`. Conclude with `(AdelicGLn.isOpen_integralFiniteGL K n).preimage (continuous_snd.comp (AdelicGLn.prodEquiv K n).continuous)`. Conclude with `Subgroup.isOpen_mono (H₁ := US (pF K n) (KF K n) ∅) (H₂ := US (pF K n) (KF K n) S) (fun g hg v _ => hg v (Finset.notMem_empty v)) h0`.
-/
private theorem opnU (S : Finset (Pl K)) :
    IsOpen (US (pF K n) (KF K n) S : Set (GA K n)) := by
  have h0 : IsOpen (US (pF K n) (KF K n) ∅ : Set (GA K n)) := by
    have : (US (pF K n) (KF K n) ∅ : Set (GA K n)) =
        (fun g => (AdelicGLn.prodEquiv K n g).2) ⁻¹'
          (AdelicGLn.integralFiniteGL K n : Set (AdelicGLn.FiniteAdelicGL K n)) := by
      ext g
      simp only [Set.mem_preimage, SetLike.mem_coe, AdelicGLn.mem_integralFiniteGL_iff_forall, mem_US]
      exact ⟨fun h v => h v (Finset.notMem_empty v), fun h v _ => h v⟩
    rw [this]
    exact (AdelicGLn.isOpen_integralFiniteGL K n).preimage
      (continuous_snd.comp (AdelicGLn.prodEquiv K n).continuous)
  exact Subgroup.isOpen_mono (H₁ := US (pF K n) (KF K n) ∅) (H₂ := US (pF K n) (KF K n) S)
    (fun g hg v _ => hg v (Finset.notMem_empty v)) h0

end UpperTheory.OpenSubgroupProjection

open UpperTheory.OpenSubgroupProjection in
/- English proof (translation)
Introduce `K _ _ n`. Use `{ cq := ?_ cp := fun v => continuous_finAt v opn := opn K n cpt := cpt K n ae := fun g => AdelicGLn.eventually_mem_integralGL K n g opnU := opnU K n` and prove the remaining obligations. Use extensionality with `:= ?_`. Use `surj := ?_`. Use `prop := ?_ }`.

Establish `: (pI K n : GA K n → _) = fun g => (AdelicGLn.prodEquiv K n g).1`. Use function extensionality and compare the values at `fun g => (fst_eq K n g).symm`. Rewrite using `[this]`. Conclude with `continuous_fst.comp (AdelicGLn.prodEquiv K n).continuous`. Introduce `g g' h1 h2`.

Apply `(phi K n).injective` to reduce the goal to its premises. Use `Prod.ext ?_ (Subtype.ext (funext fun v => ?_))` and prove the remaining obligations. Rewrite using `[phi_fst, phi_fst, h1]`. Conclude with `h2 v`. Introduce `gi gv h`.

Use `⟨(phi K n).symm (gi, ⟨gv, h⟩), ?_, fun v => ?_⟩` and prove the remaining obligations. Rewrite using `[← phi_fst, Homeomorph.apply_symm_apply]`. Rewrite using `[← phi_snd, Homeomorph.apply_symm_apply]`. Both sides reduce to the same expression. Introduce `Ci C hCi hC hK`.

Establish `h` using `(hCi.prod (compact_box K n C hC hK))`. Establish `h2` using `(phi K n).isCompact_preimage.2 h`. Use `h2 using 1` and compare the differences between its conclusion and the goal. Use extensionality with `g`. Simplify using `only [Set.mem_setOf_eq, Set.mem_preimage, Set.mem_prod, phi_fst, phi_snd]`.
-/
theorem UpperTheory.restrictedProduct_finite_adelicGL :
    RPF := by
  intro K _ _ n
  refine
    { cq := ?_
      cp := fun v => continuous_finAt v
      opn := opn K n
      cpt := cpt K n
      ae := fun g => AdelicGLn.eventually_mem_integralGL K n g
      opnU := opnU K n
      ext := ?_
      surj := ?_
      prop := ?_ }
  · have : (pI K n : GA K n → _) = fun g => (AdelicGLn.prodEquiv K n g).1 :=
      funext fun g => (fst_eq K n g).symm
    rw [this]
    exact continuous_fst.comp (AdelicGLn.prodEquiv K n).continuous
  · intro g g' h1 h2
    apply (phi K n).injective
    refine Prod.ext ?_ (Subtype.ext (funext fun v => ?_))
    · rw [phi_fst, phi_fst, h1]
    · exact h2 v
  · intro gi gv h
    refine ⟨(phi K n).symm (gi, ⟨gv, h⟩), ?_, fun v => ?_⟩
    · rw [← phi_fst, Homeomorph.apply_symm_apply]
    · rw [← phi_snd, Homeomorph.apply_symm_apply]
      rfl
  · intro Ci C hCi hC hK
    have h := (hCi.prod (compact_box K n C hC hK))
    have h2 := (phi K n).isCompact_preimage.2 h
    convert h2 using 1
    ext g
    simp only [Set.mem_setOf_eq, Set.mem_preimage, Set.mem_prod, phi_fst, phi_snd]

import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilRepresentationPreservesSchwartz
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAdmittedFormEqAdelicThetaDistribution

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped Classical

noncomputable section

namespace GlobalTheory.ThetaSchrCont

open GlobalTheory.HeisSchA GlobalTheory.Published.Metaplectic
open scoped Matrix

variable {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ]

def finSlice (Φ : (κ → AdeleRing (𝓞 F) F) → ℂ) (y : κ → mixedEmbedding.mixedSpace F) :
    (κ → FiniteAdeleRing (𝓞 F) F) → ℂ :=
  fun w => Φ fun i => ((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (y i), w i)

/- English proof (translation)
Proceed by induction on `hΦ using Submodule.span_induction with`. Consider the case `mem x hx`. Take `⟨f, g, hg, rfl⟩` from `hx`. Establish `: finSlice (pureA F f g) y = f y • g`. Use function extensionality and compare the values at `w`.

Simplify using `only [finSlice, pureA, RingEquiv.apply_symm_apply, Pi.smul_apply, smul_eq_mul]`. Rewrite using `[this]`. Conclude with `Submodule.smul_mem _ _ hg`. Consider the case `zero => exact (SB _).zero_mem`. Consider the case `add x x' _ _ hx hx' => exact (SB _).add_mem hx hx'`.

Consider the case `smul a x _ hx => exact (SB _).smul_mem a hx`.
-/
theorem finSlice_mem {Φ : (κ → AdeleRing (𝓞 F) F) → ℂ} (hΦ : Φ ∈ schA F κ) (y : κ → mixedEmbedding.mixedSpace F) :
    finSlice Φ y ∈ SB (κ → FiniteAdeleRing (𝓞 F) F) := by
  induction hΦ using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨f, g, hg, rfl⟩ := hx
    have : finSlice (pureA F f g) y = f y • g := by
      funext w
      simp only [finSlice, pureA, RingEquiv.apply_symm_apply, Pi.smul_apply, smul_eq_mul]
    rw [this]
    exact Submodule.smul_mem _ _ hg
  | zero => exact (SB _).zero_mem
  | add x x' _ _ hx hx' => exact (SB _).add_mem hx hx'
  | smul a x _ hx => exact (SB _).smul_mem a hx

/- English proof (translation)
Choose the witnesses or unpack the hypotheses as in `⟨y, hy⟩ : ∃ y, f y ≠ 0 := by`. Assume the negation of the conclusion as `h`. Use `push_neg at h`. Conclude with `hf (SchwartzMap.ext h)`. Set `e` to `InfiniteAdeleRing.ringEquiv_mixedSpace F`.

Use `⟨(f y)⁻¹ • finSlice (tens (evI F) (⇑f) r) y, Submodule.smul_mem _ _ (finSlice_mem hr.2 y), fun x => ?_⟩` and prove the remaining obligations. Set `z : κ → AF F` to `fun i => mk (e.symm (y i) - (x i).1) 0`. Establish `hz : At (evI F) z`. Introduce `u hu`. Use function extensionality and compare the values at `i`.

Conclude with `at_mk _ u hu`. Establish `hxz : x + z = fun i => (e.symm (y i), (x i).2)`. Use function extensionality and compare the values at `i`. Use `Prod.ext ?_ ?_` and prove the remaining obligations. Use `show (x i).1 + (e.symm (y i) - (x i).1) = e.symm (y i)`.

Normalize the expressions using the abelian group laws. Use `show (x i).2 + 0 = (x i).2`. Conclude with `add_zero _`. Establish `h1` using `hr.1 x z hz`. Rewrite `h1` using `[hxz]`.

Establish `h2 : (fun i => evI F ((e.symm (y i), (x i).2) : AF F)) = y`. Use function extensionality and compare the values at `i`. Conclude with `e.apply_symm_apply (y i)`. Simplify using `only [Pi.smul_apply, smul_eq_mul, finSlice, tens]`. Rewrite using `[h2, ← h1]`.

Clear the denominators using the available nonvanishing facts. Both sides reduce to the same expression.
-/
theorem exists_fin_of_rest {f : SInf F κ} {r : (κ → AF F) → ℂ} (hr : Rest (evI F) (⇑f) r) (hf : f ≠ 0) :
    ∃ G ∈ SB (κ → FiniteAdeleRing (𝓞 F) F), ∀ x : κ → AF F, r x = G fun i => (x i).2 := by
  obtain ⟨y, hy⟩ : ∃ y, f y ≠ 0 := by
    by_contra h
    push_neg at h
    exact hf (SchwartzMap.ext h)
  let e := InfiniteAdeleRing.ringEquiv_mixedSpace F
  refine ⟨(f y)⁻¹ • finSlice (tens (evI F) (⇑f) r) y, Submodule.smul_mem _ _ (finSlice_mem hr.2 y), fun x => ?_⟩
  let z : κ → AF F := fun i => mk (e.symm (y i) - (x i).1) 0
  have hz : At (evI F) z := by
    intro u hu
    funext i
    exact at_mk _ u hu
  have hxz : x + z = fun i => (e.symm (y i), (x i).2) := by
    funext i
    refine Prod.ext ?_ ?_
    · show (x i).1 + (e.symm (y i) - (x i).1) = e.symm (y i)
      abel
    · show (x i).2 + 0 = (x i).2
      exact add_zero _
  have h1 := hr.1 x z hz
  rw [hxz] at h1
  have h2 : (fun i => evI F ((e.symm (y i), (x i).2) : AF F)) = y := by
    funext i
    exact e.apply_symm_apply (y i)
  simp only [Pi.smul_apply, smul_eq_mul, finSlice, tens]
  rw [h2, ← h1]
  field_simp
  rfl

/- English proof (translation)
Use function extensionality and compare the values at `x`. Simplify using `only [tens, pureA, hG]`. Both sides reduce to the same expression.
-/
theorem tens_eq_pureA (g : SInf F κ) {r : (κ → AF F) → ℂ} {G : (κ → FiniteAdeleRing (𝓞 F) F) → ℂ}
    (hG : ∀ x : κ → AF F, r x = G fun i => (x i).2) : tens (evI F) (⇑g) r = pureA F g G := by
  funext x
  simp only [tens, pureA, hG]
  rfl

/- English proof (translation)
Introduce `q h`. Set `c : κ → mixedEmbedding.mixedSpace F` to `fun i => q (w.2 i)`. Set `t : κ → mixedEmbedding.mixedSpace F` to `fun i => q (w.1 i)`. Set `k : ℝ` to `Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (q h)`. Set `d : κ → FiniteAdeleRing (𝓞 F) F` to `fun i => p2 (w.2 i)`.

Set `s : κ → FiniteAdeleRing (𝓞 F) F` to `fun i => p2 (w.1 i)`. Use function extensionality and compare the values at `x`. Set `y : κ → mixedEmbedding.mixedSpace F` to `fun i => q (x i)`. Set `z : κ → FiniteAdeleRing (𝓞 F) F` to `fun i => p2 (x i)`. Establish `h1 : (fun i => q ((x + w.1) i)) = y + t` using `funext fun i => map_add q (x i) (w.1 i)`.

Establish `h2 : (fun i => p2 ((x + w.1) i)) = z + s` using `funext fun i => map_add p2 (x i) (w.1 i)`. Establish `h3 : ψ (x ⬝ᵥ w.2 + h) = eChar ((-trL c) y + -k) * finChar ψ (z ⬝ᵥ d + p2 h)`. Rewrite using `[map_eq_mul ψ, hψ.2.2 _ (at_mk _)]`. Use `congr 1`. Establish `e1 : evI F (mk (p1 (x ⬝ᵥ w.2 + h)) 0) = y ⬝ᵥ c + q h`.

Express the relevant statement in the definitionally equal form `q (x ⬝ᵥ w.2 + h) = _`. Rewrite using `[map_add, RingHom.map_dotProduct]`. Both sides reduce to the same expression. Rewrite using `[e1, map_add, eChar_apply, ContinuousLinearMap.neg_apply, trL_apply]`. Use `congr 1`.

Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[map_add, RingHom.map_dotProduct]`. Both sides reduce to the same expression. Express the relevant statement in the definitionally equal form `ψ (x ⬝ᵥ w.2 + h) * (f (fun i => q ((x + w.1) i)) * g (fun i => p2 ((x + w.1) i))) = archS f c t k y * (finChar ψ (z ⬝ᵥ d + p2 h) * g (z + s))`.

Rewrite using `[h1, h2, h3, archS_apply]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem schr_pureA_eq [Invertible (2 : AdeleRing (𝓞 F) F)] (ψ : AddChar (AdeleRing (𝓞 F) F) ℂ) (hψ : IsStd ψ)
    (w : (κ → AdeleRing (𝓞 F) F) × (κ → AdeleRing (𝓞 F) F)) (f : SchwartzMap (κ → mixedEmbedding.mixedSpace F) ℂ)
    (g : (κ → FiniteAdeleRing (𝓞 F) F) → ℂ) :
    let q : AdeleRing (𝓞 F) F →+* mixedEmbedding.mixedSpace F := (InfiniteAdeleRing.ringEquiv_mixedSpace F).toRingHom.comp p1
    let h : AdeleRing (𝓞 F) F := ⅟(2 : AdeleRing (𝓞 F) F) * (w.1 ⬝ᵥ w.2)
    schr ψ w (pureA F f g) = pureA F (archS f (fun i => q (w.2 i)) (fun i => q (w.1 i))
      (Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (q h)))
      (finS ψ g (fun i => p2 (w.2 i)) (fun i => p2 (w.1 i)) (p2 h)) := by
  intro q h
  let c : κ → mixedEmbedding.mixedSpace F := fun i => q (w.2 i)
  let t : κ → mixedEmbedding.mixedSpace F := fun i => q (w.1 i)
  let k : ℝ := Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (q h)
  let d : κ → FiniteAdeleRing (𝓞 F) F := fun i => p2 (w.2 i)
  let s : κ → FiniteAdeleRing (𝓞 F) F := fun i => p2 (w.1 i)
  funext x
  let y : κ → mixedEmbedding.mixedSpace F := fun i => q (x i)
  let z : κ → FiniteAdeleRing (𝓞 F) F := fun i => p2 (x i)
  have h1 : (fun i => q ((x + w.1) i)) = y + t := funext fun i => map_add q (x i) (w.1 i)
  have h2 : (fun i => p2 ((x + w.1) i)) = z + s := funext fun i => map_add p2 (x i) (w.1 i)
  have h3 : ψ (x ⬝ᵥ w.2 + h) = eChar ((-trL c) y + -k) * finChar ψ (z ⬝ᵥ d + p2 h) := by
    rw [map_eq_mul ψ, hψ.2.2 _ (at_mk _)]
    congr 1
    · have e1 : evI F (mk (p1 (x ⬝ᵥ w.2 + h)) 0) = y ⬝ᵥ c + q h := by
        change q (x ⬝ᵥ w.2 + h) = _
        rw [map_add, RingHom.map_dotProduct]
        rfl
      rw [e1, map_add, eChar_apply, ContinuousLinearMap.neg_apply, trL_apply]
      congr 1
      push_cast
      ring
    · rw [map_add, RingHom.map_dotProduct]
      rfl
  change ψ (x ⬝ᵥ w.2 + h) * (f (fun i => q ((x + w.1) i)) * g (fun i => p2 ((x + w.1) i))) =
    archS f c t k y * (finChar ψ (z ⬝ᵥ d + p2 h) * g (z + s))
  rw [h1, h2, h3, archS_apply]
  ring

/- English proof (translation)
Introduce `F E _ _ _ _ _ σ n d X W M ψ hψ u f r hr hf`. Take `⟨G, hG, hrG⟩` from `exists_fin_of_rest hr hf`. Use `set w := M.co.e u with hw`. Set `q : AdeleRing (𝓞 F) F →+* mixedEmbedding.mixedSpace F` to `(InfiniteAdeleRing.ringEquiv_mixedSpace F).toRingHom.comp p1`. Set `h : AdeleRing (𝓞 F) F` to `⅟(2 : AdeleRing (𝓞 F) F) * (w.1 ⬝ᵥ w.2)`.

Set `c : Fin n × Fin d → mixedEmbedding.mixedSpace F` to `fun i => q (w.2 i)`. Set `t : Fin n × Fin d → mixedEmbedding.mixedSpace F` to `fun i => q (w.1 i)`. Set `k : ℝ` to `Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (q h)`. Set `G'` to `finS ψ G (fun i => p2 (w.2 i)) (fun i => p2 (w.1 i)) (p2 h)`. Establish `hG' : G' ∈ SB (Fin n × Fin d → FiniteAdeleRing (𝓞 F) F)` using `finS_mem ψ hψ.1 hG _ _ _`.

Take `⟨l, hl, hleq⟩` from `GlobalTheory.ThetaAdmitted.exists_admitted_form_eq_adelicThetaDistribution_alt F (Fin n × Fin d)`. Take `⟨T₀, hT₀⟩` from `hl G' hG'`. Set `A : SInf F (Fin n × Fin d) →L[ℂ] SInf F (Fin n × Fin d)` to `(SchwartzMap.smulLeftCLM ℂ (fun y : Fin n × Fin d → mixedEmbedding.mixedSpace F => eChar ((-trL c) y + -k))).comp (SchwartzMap.compSubConstCLM ℂ (-t))`. Use `⟨T₀.comp A, fun g => ?_⟩` and prove the remaining obligations. Establish `hΦ : M.co.rho ψ u (tens (evI F) (⇑g) r) = pureA F (A g) G'`.

Rewrite using `[tens_eq_pureA g hrG]`. Conclude with `schr_pureA_eq ψ hψ w g G`. Rewrite using `[hΦ]`. Establish `hmem : pureA F (A g) G' ∈ schA F (Fin n × Fin d)` using `Submodule.subset_span ⟨A g, G', hG', rfl⟩`. Use `hasSum_thetaSum F hmem using 1` and compare the differences between its conclusion and the goal.

Rewrite using `[ContinuousLinearMap.comp_apply, ← hT₀, hleq _ hmem]`.
-/
theorem exists_clm_hasSum : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
    {n d : ℕ} {X : Spc F E n} {W : Spc F E d} (M : Model σ X W) (ψ : AddChar (AF F) ℂ), IsStd ψ →
    ∀ (u : Matrix (Fin n) (Fin d) (AE F E)) (f : SInf F (Fin n × Fin d)) (r : (Fin n × Fin d → AF F) → ℂ),
    Rest (evI F) (⇑f) r → f ≠ 0 → ∃ T : SInf F (Fin n × Fin d) →L[ℂ] ℂ, ∀ g : SInf F (Fin n × Fin d),
      HasSum (fun ξ : Fin n × Fin d → F => M.co.rho ψ u (tens (evI F) (⇑g) r) (fun i => algebraMap F (AF F) (ξ i))) (T g) := by
  intro F E _ _ _ _ _ σ n d X W M ψ hψ u f r hr hf
  obtain ⟨G, hG, hrG⟩ := exists_fin_of_rest hr hf
  set w := M.co.e u with hw
  let q : AdeleRing (𝓞 F) F →+* mixedEmbedding.mixedSpace F :=
    (InfiniteAdeleRing.ringEquiv_mixedSpace F).toRingHom.comp p1
  let h : AdeleRing (𝓞 F) F := ⅟(2 : AdeleRing (𝓞 F) F) * (w.1 ⬝ᵥ w.2)
  let c : Fin n × Fin d → mixedEmbedding.mixedSpace F := fun i => q (w.2 i)
  let t : Fin n × Fin d → mixedEmbedding.mixedSpace F := fun i => q (w.1 i)
  let k : ℝ := Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (q h)
  let G' := finS ψ G (fun i => p2 (w.2 i)) (fun i => p2 (w.1 i)) (p2 h)
  have hG' : G' ∈ SB (Fin n × Fin d → FiniteAdeleRing (𝓞 F) F) := finS_mem ψ hψ.1 hG _ _ _
  obtain ⟨l, hl, hleq⟩ := GlobalTheory.ThetaAdmitted.exists_admitted_form_eq_adelicThetaDistribution_alt F (Fin n × Fin d)
  obtain ⟨T₀, hT₀⟩ := hl G' hG'
  let A : SInf F (Fin n × Fin d) →L[ℂ] SInf F (Fin n × Fin d) :=
    (SchwartzMap.smulLeftCLM ℂ (fun y : Fin n × Fin d → mixedEmbedding.mixedSpace F => eChar ((-trL c) y + -k))).comp
      (SchwartzMap.compSubConstCLM ℂ (-t))
  refine ⟨T₀.comp A, fun g => ?_⟩
  have hΦ : M.co.rho ψ u (tens (evI F) (⇑g) r) = pureA F (A g) G' := by
    rw [tens_eq_pureA g hrG]
    exact schr_pureA_eq ψ hψ w g G
  rw [hΦ]
  have hmem : pureA F (A g) G' ∈ schA F (Fin n × Fin d) := Submodule.subset_span ⟨A g, G', hG', rfl⟩
  convert hasSum_thetaSum F hmem using 1
  rw [ContinuousLinearMap.comp_apply, ← hT₀, hleq _ hmem]

end GlobalTheory.ThetaSchrCont

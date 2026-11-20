import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

open scoped RestrictedProduct

noncomputable section

namespace GlobalTheory.RestAnyFactor

variable {F : Type} [Field F] [NumberField F]

/- English proof (translation)
Unfold `singleV`. Conclude with `RestrictedProduct.single_eq_same (fun w : HeightOneSpectrum (𝓞 F) => w.adicCompletionIntegers F) v t`.
-/
theorem singleV_self (v : Pl F) (t : Fv F v) : (singleV F v t) v = t := by
  classical
  unfold singleV
  exact RestrictedProduct.single_eq_same (fun w : HeightOneSpectrum (𝓞 F) => w.adicCompletionIntegers F) v t

/- English proof (translation)
Unfold `singleV`. Conclude with `RestrictedProduct.single_eq_of_ne (fun w : HeightOneSpectrum (𝓞 F) => w.adicCompletionIntegers F) t h`.
-/
theorem singleV_ne {v w : Pl F} (h : w ≠ v) (t : Fv F v) : (singleV F v t) w = 0 := by
  classical
  unfold singleV
  exact RestrictedProduct.single_eq_of_ne (fun w : HeightOneSpectrum (𝓞 F) => w.adicCompletionIntegers F) t h

/- English proof (translation)
The claim follows from `singleV_self v t`.
-/
theorem evalV_singleV (v : Pl F) (t : Fv F v) : evalV F v (singleV F v t) = t := singleV_self v t

/- English proof (translation)
Use `RestrictedProduct.ext _ _ fun w => ?_` and prove the remaining obligations. Use `show (singleV F v (s + t)) w = (singleV F v s) w + (singleV F v t) w`. Distinguish the cases in `h : w = v`. Substitute `h` using the available equality. Rewrite using `[singleV_self, singleV_self, singleV_self]`.

Rewrite using `[singleV_ne h, singleV_ne h, singleV_ne h, add_zero]`.
-/
theorem singleV_add (v : Pl F) (s t : Fv F v) : singleV F v (s + t) = singleV F v s + singleV F v t := by
  refine RestrictedProduct.ext _ _ fun w => ?_
  show (singleV F v (s + t)) w = (singleV F v s) w + (singleV F v t) w
  by_cases h : w = v
  · subst h; rw [singleV_self, singleV_self, singleV_self]
  · rw [singleV_ne h, singleV_ne h, singleV_ne h, add_zero]

/- English proof (translation)
Use `RestrictedProduct.ext _ _ fun w => ?_` and prove the remaining obligations. Use `show (singleV F v 0) w = 0`. Distinguish the cases in `h : w = v`. Substitute `h` using the available equality. Rewrite using `[singleV_self]`.

Rewrite using `[singleV_ne h]`.
-/
theorem singleV_zero (v : Pl F) : singleV F v 0 = 0 := by
  refine RestrictedProduct.ext _ _ fun w => ?_
  show (singleV F v 0) w = 0
  by_cases h : w = v
  · subst h; rw [singleV_self]
  · rw [singleV_ne h]

open Classical in
/- English proof (translation)
Establish `hS : Filter.cofinite ≤ Filter.principal ({v}ᶜ : Set (HeightOneSpectrum (𝓞 F)))` using `Filter.le_principal_iff.2 (Set.finite_singleton v).compl_mem_cofinite`. Set `f : v.adicCompletion F → Πʳ w : HeightOneSpectrum (𝓞 F), [w.adicCompletion F, w.adicCompletionIntegers F]_[Filter.principal ({v}ᶜ : Set _)]` to `fun x => ⟨Pi.single (M := fun w : HeightOneSpectrum (𝓞 F) => w.adicCompletion F) v x, by`. Introduce `w hw`. Establish `hw' : w ≠ v` using `hw`. Simplify using `only [Set.mem_ofPred_eq, Pi.single_eq_of_ne hw', SetLike.mem_coe]`.

Conclude with `zero_mem _⟩`. Establish `hf : Continuous f` using `RestrictedProduct.continuous_rng_of_principal.2 (continuous_single v)`. Conclude with `(RestrictedProduct.continuous_inclusion hS).comp hf`.
-/
theorem continuous_singleV (v : Pl F) : Continuous (singleV F v) := by
  have hS : Filter.cofinite ≤ Filter.principal ({v}ᶜ : Set (HeightOneSpectrum (𝓞 F))) :=
    Filter.le_principal_iff.2 (Set.finite_singleton v).compl_mem_cofinite
  let f : v.adicCompletion F → Πʳ w : HeightOneSpectrum (𝓞 F),
      [w.adicCompletion F, w.adicCompletionIntegers F]_[Filter.principal ({v}ᶜ : Set _)] :=
    fun x => ⟨Pi.single (M := fun w : HeightOneSpectrum (𝓞 F) => w.adicCompletion F) v x, by
      intro w hw
      have hw' : w ≠ v := hw
      simp only [Set.mem_ofPred_eq, Pi.single_eq_of_ne hw', SetLike.mem_coe]
      exact zero_mem _⟩
  have hf : Continuous f := RestrictedProduct.continuous_rng_of_principal.2 (continuous_single v)
  exact (RestrictedProduct.continuous_inclusion hS).comp hf

/- English proof (translation)
The claim follows from `RestrictedProduct.continuous_eval (R := fun w : HeightOneSpectrum (𝓞 F) => w.adicCompletion F) (A := fun w : HeightOneSpectrum (𝓞 F) => (w.adicCompletionIntegers F : Set (w.adicCompletion F))) v`.
-/
theorem continuous_evalV' (v : Pl F) : Continuous (evalV F v) :=
  RestrictedProduct.continuous_eval (R := fun w : HeightOneSpectrum (𝓞 F) => w.adicCompletion F)
    (A := fun w : HeightOneSpectrum (𝓞 F) => (w.adicCompletionIntegers F : Set (w.adicCompletion F))) v

/- English proof (translation)
Both sides reduce to the same expression.
-/
example (v : Pl F) (a : AF F) : evFin F v a = evalV F v a.2 := rfl

/- English proof (translation)
Take `⟨hψl, hψc⟩` from `hψ`. Take `⟨hgl, hgc⟩` from `hg`. Establish `hP : Continuous fun y : κ → Af F => fun i => evalV F v (y i)` using `continuous_pi fun i => (continuous_evalV' v).comp (continuous_apply i)`. Establish `hQ : Continuous fun y : κ → Af F => fun i => y i + singleV F v (y₀ i - evalV F v (y i))` using `continuous_pi fun i => (continuous_apply i).add ((continuous_singleV v).comp (continuous_const.sub ((continuous_evalV' v).comp (continuous_apply i))))`. Use `⟨?_, ?_⟩` and prove the remaining obligations.

Conclude with `IsLocallyConstant.comp₂ (IsLocallyConstant.comp₂ (IsLocallyConstant.const c) (hψl.comp_continuous hP) (· * ·)) (hgl.comp_continuous hQ) (· * ·)`. Set `R : (κ → Fv F v) × (κ → Af F) → κ → Af F` to `fun p i => p.2 i + singleV F v (p.1 i - evalV F v (p.2 i))`. Establish `hR : Continuous R` using `continuous_pi fun i => ((continuous_apply i).comp continuous_snd).add ((continuous_singleV v).comp (((continuous_apply i).comp continuous_fst).sub ((continuous_evalV' v).comp ((continuous_apply i).comp continuous_snd))))`. Establish `hK : IsCompact (R '' (tsupport ψ ×ˢ tsupport g))` using `(hψc.isCompact.prod hgc.isCompact).image hR`. Set `S : Set (κ → Af F)` to `(fun y => ((fun i => evalV F v (y i)), fun i => y i + singleV F v (y₀ i - evalV F v (y i)))) ⁻¹' (tsupport ψ ×ˢ tsupport g)`.

Establish `hS : IsClosed S` using `((isClosed_tsupport ψ).prod (isClosed_tsupport g)).preimage (hP.prodMk hQ)`. Use `hK.of_isClosed_subset (isClosed_tsupport _) ?_` and prove the remaining obligations. Use `(closure_minimal (fun y hy => ?_) hS).trans fun y hy => ⟨_, hy, ?_⟩` and prove the remaining obligations. Use `⟨subset_tsupport _ fun h => hy ?_, subset_tsupport _ fun h => hy ?_⟩` and prove the remaining obligations. Simplify using `only [h, mul_zero, zero_mul]`.

Simplify using `only [h, mul_zero]`. Use function extensionality and compare the values at `i`. Simplify using `only [R]`. Rewrite using `[add_assoc, ← singleV_add, map_add, evalV_singleV]`. Establish `e : y₀ i - evalV F v (y i) + (evalV F v (y i) - (evalV F v (y i) + (y₀ i - evalV F v (y i)))) = 0` using `by ring`.

Rewrite using `[e, singleV_zero, add_zero]`.
-/
theorem sb_shift (v : Pl F) {κ : Type} [Fintype κ] (y₀ : κ → Fv F v) (c : ℂ) {ψ : (κ → Fv F v) → ℂ}
    {g : (κ → Af F) → ℂ} (hψ : ψ ∈ SB (κ → Fv F v)) (hg : g ∈ SB (κ → Af F)) :
    (fun y : κ → Af F => c * ψ (fun i => evalV F v (y i)) *
      g (fun i => y i + singleV F v (y₀ i - evalV F v (y i)))) ∈ SB (κ → Af F) := by
  obtain ⟨hψl, hψc⟩ := hψ
  obtain ⟨hgl, hgc⟩ := hg
  have hP : Continuous fun y : κ → Af F => fun i => evalV F v (y i) :=
    continuous_pi fun i => (continuous_evalV' v).comp (continuous_apply i)
  have hQ : Continuous fun y : κ → Af F => fun i => y i + singleV F v (y₀ i - evalV F v (y i)) :=
    continuous_pi fun i => (continuous_apply i).add
      ((continuous_singleV v).comp (continuous_const.sub ((continuous_evalV' v).comp (continuous_apply i))))
  refine ⟨?_, ?_⟩
  · exact IsLocallyConstant.comp₂ (IsLocallyConstant.comp₂ (IsLocallyConstant.const c)
      (hψl.comp_continuous hP) (· * ·)) (hgl.comp_continuous hQ) (· * ·)
  · let R : (κ → Fv F v) × (κ → Af F) → κ → Af F := fun p i => p.2 i + singleV F v (p.1 i - evalV F v (p.2 i))
    have hR : Continuous R := continuous_pi fun i =>
      ((continuous_apply i).comp continuous_snd).add ((continuous_singleV v).comp
        (((continuous_apply i).comp continuous_fst).sub
          ((continuous_evalV' v).comp ((continuous_apply i).comp continuous_snd))))
    have hK : IsCompact (R '' (tsupport ψ ×ˢ tsupport g)) := (hψc.isCompact.prod hgc.isCompact).image hR
    let S : Set (κ → Af F) := (fun y => ((fun i => evalV F v (y i)), fun i => y i + singleV F v (y₀ i - evalV F v (y i)))) ⁻¹'
      (tsupport ψ ×ˢ tsupport g)
    have hS : IsClosed S := ((isClosed_tsupport ψ).prod (isClosed_tsupport g)).preimage (hP.prodMk hQ)
    refine hK.of_isClosed_subset (isClosed_tsupport _) ?_
    refine (closure_minimal (fun y hy => ?_) hS).trans fun y hy => ⟨_, hy, ?_⟩
    · refine ⟨subset_tsupport _ fun h => hy ?_, subset_tsupport _ fun h => hy ?_⟩
      · simp only [h, mul_zero, zero_mul]
      · simp only [h, mul_zero]
    · funext i
      simp only [R]
      rw [add_assoc, ← singleV_add, map_add, evalV_singleV]
      have e : y₀ i - evalV F v (y i) + (evalV F v (y i) - (evalV F v (y i) + (y₀ i - evalV F v (y i)))) = 0 := by ring
      rw [e, singleV_zero, add_zero]

/- English proof (translation)
Introduce `F _ _ v κ _ φ ψ r _ hne hR hψ`. Take `⟨hinv, hmem⟩` from `hR`. Use `⟨hinv, ?_⟩` and prove the remaining obligations. Take `⟨y₀, hy₀⟩ : ∃ y₀, φ y₀ ≠ 0` from `by by_contra! h`. Conclude with `hne (funext h)`.

Set `c : ℂ` to `(φ y₀)⁻¹`. Set `zf : (κ → Af F) → κ → Af F` to `fun y i => singleV F v (y₀ i - evalV F v (y i))`. Set `z : (κ → AF F) → κ → AF F` to `fun x i => ((0, zf (fun j => (x j).2) i) : AF F)`. Establish `hev : ∀ x : κ → AF F, (fun i => evFin F v ((x + z x) i)) = y₀` using `fun x => by`. Use function extensionality and compare the values at `i`.

Use `show evalV F v ((x i).2 + singleV F v (y₀ i - evalV F v ((x i).2))) = y₀ i`. Rewrite using `[map_add, evalV_singleV, add_sub_cancel]`. Establish `hAt : ∀ x, At (evFin F v) (z x)` using `fun x u hu => by`. Use function extensionality and compare the values at `i`. Use `Prod.ext (mul_zero _) ?_` and prove the remaining obligations.

Use `show u.2 * singleV F v _ = 0`. Use `RestrictedProduct.ext _ _ fun w => ?_` and prove the remaining obligations. Use `show u.2 w * (singleV F v _) w = 0`. Distinguish the cases in `h : w = v`. Substitute `h` using the available equality.

Establish `: u.2 w = 0` using `hu`. Rewrite using `[this, zero_mul]`. Rewrite using `[singleV_ne h, mul_zero]`. Set `T : ((κ → AF F) → ℂ) →ₗ[ℂ] ((κ → AF F) → ℂ)` to `{ toFun := fun Φ x => c * ψ (fun i => evFin F v (x i)) * Φ (x + z x) map_add' := fun _ _ => funext fun _ => by simp only [Pi.add_apply]; ring map_smul' := fun _ _ => funext fun _ => by simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]; ring }`. Establish `hT : tens (evFin F v) ψ r = T (tens (evFin F v) φ r)`.

Use function extensionality and compare the values at `x`. Use `show ψ _ * r x = c * ψ _ * (φ (fun i => evFin F v ((x + z x) i)) * r (x + z x))`. Rewrite using `[hinv x (z x) (hAt x), hev x]`. Establish `hc : c * φ y₀ = 1` using `inv_mul_cancel₀ hy₀`. Take the linear combination `(-(ψ (fun i => evFin F v (x i)) * r x)) * hc`.

Rewrite using `[hT]`. Establish `key : schA F κ ≤ (schA F κ).comap T`. Use `Submodule.span_le.2 ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨f, g, hg, rfl⟩`. Use `show T (pureA F f g) ∈ schA F κ`.

Use `Submodule.subset_span ⟨f, fun y => c * ψ (fun i => evalV F v (y i)) * g (fun i => y i + zf y i), sb_shift v y₀ c hψ hg, ?_⟩` and prove the remaining obligations. Use function extensionality and compare the values at `x`. Use `show c * ψ _ * (f _ * g _) = f _ * (c * ψ _ * g _)`. Establish `e1 : (fun i => (InfiniteAdeleRing.ringEquiv_mixedSpace F) ((x + z x) i).1) = fun i => (InfiniteAdeleRing.ringEquiv_mixedSpace F) (x i).1`. Use function extensionality and compare the values at `i`.

Use `show (InfiniteAdeleRing.ringEquiv_mixedSpace F) ((x i).1 + 0) = _`. Rewrite using `[add_zero]`. Rewrite using `[e1]`. Use `show c * ψ _ * (f _ * g (fun i => (x i).2 + zf (fun j => (x j).2) i)) = _`. Establish `e2 : (fun i => evFin F v (x i)) = fun i => evalV F v (x i).2` using `rfl`.

Rewrite using `[e2]`. Expand and normalize the polynomial expressions, which then agree. Conclude with `key hmem`.
-/
theorem rest_of_rest : ∀ (F : Type) [Field F] [NumberField F] (v : Pl F) (κ : Type) [Fintype κ] (φ ψ : (κ → Fv F v) → ℂ)
    (r : (κ → AF F) → ℂ), φ ∈ SB (κ → Fv F v) → φ ≠ 0 → Rest (evFin F v) φ r → ψ ∈ SB (κ → Fv F v) →
    Rest (evFin F v) ψ r := by
  intro F _ _ v κ _ φ ψ r _ hne hR hψ
  obtain ⟨hinv, hmem⟩ := hR
  refine ⟨hinv, ?_⟩
  obtain ⟨y₀, hy₀⟩ : ∃ y₀, φ y₀ ≠ 0 := by
    by_contra! h
    exact hne (funext h)
  let c : ℂ := (φ y₀)⁻¹
  let zf : (κ → Af F) → κ → Af F := fun y i => singleV F v (y₀ i - evalV F v (y i))
  let z : (κ → AF F) → κ → AF F := fun x i => ((0, zf (fun j => (x j).2) i) : AF F)
  have hev : ∀ x : κ → AF F, (fun i => evFin F v ((x + z x) i)) = y₀ := fun x => by
    funext i
    show evalV F v ((x i).2 + singleV F v (y₀ i - evalV F v ((x i).2))) = y₀ i
    rw [map_add, evalV_singleV, add_sub_cancel]
  have hAt : ∀ x, At (evFin F v) (z x) := fun x u hu => by
    funext i
    refine Prod.ext (mul_zero _) ?_
    show u.2 * singleV F v _ = 0
    refine RestrictedProduct.ext _ _ fun w => ?_
    show u.2 w * (singleV F v _) w = 0
    by_cases h : w = v
    · subst h
      have : u.2 w = 0 := hu
      rw [this, zero_mul]
    · rw [singleV_ne h, mul_zero]
  let T : ((κ → AF F) → ℂ) →ₗ[ℂ] ((κ → AF F) → ℂ) :=
    { toFun := fun Φ x => c * ψ (fun i => evFin F v (x i)) * Φ (x + z x)
      map_add' := fun _ _ => funext fun _ => by simp only [Pi.add_apply]; ring
      map_smul' := fun _ _ => funext fun _ => by simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]; ring }
  have hT : tens (evFin F v) ψ r = T (tens (evFin F v) φ r) := by
    funext x
    show ψ _ * r x = c * ψ _ * (φ (fun i => evFin F v ((x + z x) i)) * r (x + z x))
    rw [hinv x (z x) (hAt x), hev x]
    have hc : c * φ y₀ = 1 := inv_mul_cancel₀ hy₀
    linear_combination (-(ψ (fun i => evFin F v (x i)) * r x)) * hc
  rw [hT]
  have key : schA F κ ≤ (schA F κ).comap T := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨f, g, hg, rfl⟩
    show T (pureA F f g) ∈ schA F κ
    refine Submodule.subset_span ⟨f, fun y => c * ψ (fun i => evalV F v (y i)) * g (fun i => y i + zf y i),
      sb_shift v y₀ c hψ hg, ?_⟩
    funext x
    show c * ψ _ * (f _ * g _) = f _ * (c * ψ _ * g _)
    have e1 : (fun i => (InfiniteAdeleRing.ringEquiv_mixedSpace F) ((x + z x) i).1) =
        fun i => (InfiniteAdeleRing.ringEquiv_mixedSpace F) (x i).1 := by
      funext i
      show (InfiniteAdeleRing.ringEquiv_mixedSpace F) ((x i).1 + 0) = _
      rw [add_zero]
    rw [e1]
    show c * ψ _ * (f _ * g (fun i => (x i).2 + zf (fun j => (x j).2) i)) = _
    have e2 : (fun i => evFin F v (x i)) = fun i => evalV F v (x i).2 := rfl
    rw [e2]
    ring
  exact key hmem

end GlobalTheory.RestAnyFactor

import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CharacterInvariantAdelicFormEqMulEvalZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicStoneVonNeumannLagrangianUniqueness
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzVanishingDecompositionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TranslationInvariantFunctionalLinearZeroStatement

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped Matrix TensorProduct

noncomputable section

namespace GlobalTheory.SvNLinear

/- English proof (translation)
The claim follows from `GlobalTheory.T.modulation_invariant_functional_kills_linear_multiple`.
-/
theorem kills_linear_mul : ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    (T : SchwartzMap V ℂ →ₗ[ℂ] ℂ),
    (∀ (L : V →L[ℝ] ℝ) (f f' : SchwartzMap V ℂ), (∀ x, f' x = Complex.exp (Complex.I * (L x : ℂ)) * f x) → T f' = T f) →
    ∀ (L : V →L[ℝ] ℝ) (h g : SchwartzMap V ℂ), (∀ x, g x = (L x : ℂ) * h x) → T g = 0 := GlobalTheory.T.modulation_invariant_functional_kills_linear_multiple

/- English proof (translation)
Take `⟨f₀, hf₀⟩` from `GlobalTheory.CharInvForm.exists_schwartz_one V`. Use `⟨T f₀, fun f => ?_⟩` and prove the remaining obligations. Establish `h0 : (f - f 0 • f₀) 0 = 0` using `by simp [hf₀]`. Take `⟨n, L, h, g, hg, hsum⟩` from `GlobalTheory.T.schwartz_vanishing_decomposition V _ h0`. Establish `e : f - f 0 • f₀ = ∑ i, g i`.

Use extensionality with `x`. Rewrite using `[hsum x, SchwartzMap.sum_apply]`. Establish `: T (f - f 0 • f₀) = 0`. Rewrite using `[e, map_sum]`. Conclude with `Finset.sum_eq_zero fun i _ => kills_linear_mul V T hT (L i) (h i) (g i) (hg i)`.

Rewrite `this` using `[map_sub, map_smul, sub_eq_zero]`. Rewrite using `[this, smul_eq_mul, mul_comm]`.
-/
theorem arch (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    (T : SchwartzMap V ℂ →ₗ[ℂ] ℂ)
    (hT : ∀ (L : V →L[ℝ] ℝ) (f f' : SchwartzMap V ℂ),
      (∀ x, f' x = Complex.exp (Complex.I * (L x : ℂ)) * f x) → T f' = T f) :
    ∃ a : ℂ, ∀ f : SchwartzMap V ℂ, T f = a * f 0 := by
  obtain ⟨f₀, hf₀⟩ := GlobalTheory.CharInvForm.exists_schwartz_one V
  refine ⟨T f₀, fun f => ?_⟩
  have h0 : (f - f 0 • f₀) 0 = 0 := by simp [hf₀]
  obtain ⟨n, L, h, g, hg, hsum⟩ := GlobalTheory.T.schwartz_vanishing_decomposition V _ h0
  have e : f - f 0 • f₀ = ∑ i, g i := by
    ext x
    rw [hsum x, SchwartzMap.sum_apply]
  have : T (f - f 0 • f₀) = 0 := by
    rw [e, map_sum]
    exact Finset.sum_eq_zero fun i _ => kills_linear_mul V T hT (L i) (h i) (g i) (hg i)
  rw [map_sub, map_smul, sub_eq_zero] at this
  rw [this, smul_eq_mul, mul_comm]

open scoped Classical

open GlobalTheory.CharInvForm in

/- English proof (translation)
Introduce `F _ _ ψ hψ κ _ l hinv`. Establish `harch : ∀ g ∈ SB (κ → Af F), ∃ α : ℂ, ∀ f : SchwartzMap (κ → mixedEmbedding.mixedSpace F) ℂ, l (pureA F f g) = α * f 0`. Introduce `g hg`. Set `T : SchwartzMap (κ → mixedEmbedding.mixedSpace F) ℂ →ₗ[ℂ] ℂ` to `{ toFun := fun f => l (pureA F f g) map_add' := fun f f' => by`. Rewrite using `[← map_add]`.

Use `congr 1`. Use function extensionality and compare the values at `x`. Simplify using `only [pureA, SchwartzMap.add_apply, Pi.add_apply]`. Expand and normalize the polynomial expressions, which then agree. Use the proof step `map_smul' := fun s f => by`.

Rewrite using `[RingHom.id_apply, ← map_smul]`. Use `congr 1`. Use function extensionality and compare the values at `x`. Simplify using `only [pureA, SchwartzMap.smul_apply, Pi.smul_apply, smul_eq_mul]`. Use `ring }`.

Take `⟨α, hα⟩` from `arch _ T (by`. Introduce `L f f' hff'`. Take `⟨Y, hY⟩` from `GlobalTheory.TraceDual.exists_trace_rep F κ L`. Use `show l (pureA F f' g) = l (pureA F f g)`. Rewrite using `[← hinv (fun i => pairA F ((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (Y i)) 0) (pureA F f g) (mem_schA f hg)]`.

Use `congr 1`. Use function extensionality and compare the values at `x`. Simplify using `only [pureA, hff', psi_dot_inf hψ, hY]`. Use the proof step `ring)`. Conclude with `⟨α, hα⟩`.

Take `⟨f₀, hf₀⟩` from `exists_schwartz_one (κ → mixedEmbedding.mixedSpace F)`. Set `a : ((κ → Af F) → ℂ) →ₗ[ℂ] ℂ` to `{ toFun := fun g => l (pureA F f₀ g) map_add' := fun g g' => by`. Rewrite using `[← map_add]`. Use `congr 1`. Use function extensionality and compare the values at `x`.

Simplify using `only [pureA, Pi.add_apply]`. Expand and normalize the polynomial expressions, which then agree. Use the proof step `map_smul' := fun s g => by`. Rewrite using `[RingHom.id_apply, ← map_smul]`. Use `congr 1`.

Use function extensionality and compare the values at `x`. Simplify using `only [pureA, Pi.smul_apply, smul_eq_mul]`. Use `ring }`. Take `⟨c, hc⟩` from `GlobalTheory.CharForm.exists_eq_mul_apply_zero (κ → Af F) {χ | ∃ y : κ → Af F, χ = fun x => ψ (pairA F 0 (x ⬝ᵥ y))} (by`. Introduce `N hN`.

Take `⟨U, hUo, hUc, hUN, hsep⟩` from `GlobalTheory.FinSepChar.finite_chars_separate F ψ hψ κ N hN`. Use `⟨U, hUo, hUc, hUN, fun x₀ hx₀ => ?_⟩` and prove the remaining obligations. Take `⟨y, hyU, hy⟩` from `hsep x₀ hx₀`. Use `⟨_, ⟨y, rfl⟩, fun u hu => ?_, hy⟩` and prove the remaining obligations. Use `show ψ (pairA F 0 ((x₀ + u) ⬝ᵥ y)) = ψ (pairA F 0 (x₀ ⬝ᵥ y))`.

Rewrite using `[add_dotProduct, pairA_zero_add, AddChar.map_add_eq_mul, hyU u hu, mul_one])`. Use `a`. Use the proof step `(by`. Introduce and unpack `χ ⟨y, rfl⟩ g hg`. Use `show l (pureA F f₀ _) = l (pureA F f₀ g)`.

Rewrite using `[← hinv (fun i => pairA F 0 (y i)) (pureA F f₀ g) (mem_schA f₀ hg)]`. Use `congr 1`. Use function extensionality and compare the values at `x`. Simplify using `only [pureA, dot_pairA_fin]`. Use the proof step `ring)`.

Use `⟨c, fun φ hφ => ?_⟩` and prove the remaining obligations. Proceed by induction on `hφ using Submodule.span_induction with`. Consider the case `mem Φ hΦ`. Take `⟨f, g, hg, rfl⟩` from `hΦ`. Take `⟨α, hα⟩` from `harch g hg`.

Establish `hαc : α = c * g 0`. Establish `e1` using `hα f₀`. Rewrite `e1` using `[hf₀, mul_one]`. Rewrite using `[← e1]`. Conclude with `hc g hg`.

Rewrite using `[hα f, hαc, pureA_zero]`. Expand and normalize the polynomial expressions, which then agree. Consider the case `zero => simp`. Consider the case `add φ φ' _ _ h h' => rw [map_add, h, h', Pi.add_apply, mul_add]`. Consider the case `smul s φ _ h => rw [map_smul, h, Pi.smul_apply, smul_eq_mul, smul_eq_mul]`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem charInv : ∀ (F : Type) [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ), IsStd ψ → ∀ (κ : Type) [Fintype κ]
    (l : ((κ → AF F) → ℂ) →ₗ[ℂ] ℂ),
    (∀ (y : κ → AF F), ∀ φ ∈ schA F κ, l (fun x => ψ (x ⬝ᵥ y) * φ x) = l φ) →
    ∃ c : ℂ, ∀ φ ∈ schA F κ, l φ = c * φ 0 := by
  intro F _ _ ψ hψ κ _ l hinv

  have harch : ∀ g ∈ SB (κ → Af F), ∃ α : ℂ,
      ∀ f : SchwartzMap (κ → mixedEmbedding.mixedSpace F) ℂ, l (pureA F f g) = α * f 0 := by
    intro g hg
    let T : SchwartzMap (κ → mixedEmbedding.mixedSpace F) ℂ →ₗ[ℂ] ℂ :=
      { toFun := fun f => l (pureA F f g)
        map_add' := fun f f' => by
          rw [← map_add]
          congr 1
          funext x
          simp only [pureA, SchwartzMap.add_apply, Pi.add_apply]
          ring
        map_smul' := fun s f => by
          rw [RingHom.id_apply, ← map_smul]
          congr 1
          funext x
          simp only [pureA, SchwartzMap.smul_apply, Pi.smul_apply, smul_eq_mul]
          ring }
    obtain ⟨α, hα⟩ := arch _ T (by
      intro L f f' hff'
      obtain ⟨Y, hY⟩ := GlobalTheory.TraceDual.exists_trace_rep F κ L
      show l (pureA F f' g) = l (pureA F f g)
      rw [← hinv (fun i => pairA F ((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (Y i)) 0)
        (pureA F f g) (mem_schA f hg)]
      congr 1
      funext x
      simp only [pureA, hff', psi_dot_inf hψ, hY]
      ring)
    exact ⟨α, hα⟩

  obtain ⟨f₀, hf₀⟩ := exists_schwartz_one (κ → mixedEmbedding.mixedSpace F)
  let a : ((κ → Af F) → ℂ) →ₗ[ℂ] ℂ :=
    { toFun := fun g => l (pureA F f₀ g)
      map_add' := fun g g' => by
        rw [← map_add]
        congr 1
        funext x
        simp only [pureA, Pi.add_apply]
        ring
      map_smul' := fun s g => by
        rw [RingHom.id_apply, ← map_smul]
        congr 1
        funext x
        simp only [pureA, Pi.smul_apply, smul_eq_mul]
        ring }
  obtain ⟨c, hc⟩ := GlobalTheory.CharForm.exists_eq_mul_apply_zero (κ → Af F) {χ | ∃ y : κ → Af F, χ = fun x => ψ (pairA F 0 (x ⬝ᵥ y))}
    (by
      intro N hN
      obtain ⟨U, hUo, hUc, hUN, hsep⟩ := GlobalTheory.FinSepChar.finite_chars_separate F ψ hψ κ N hN
      refine ⟨U, hUo, hUc, hUN, fun x₀ hx₀ => ?_⟩
      obtain ⟨y, hyU, hy⟩ := hsep x₀ hx₀
      refine ⟨_, ⟨y, rfl⟩, fun u hu => ?_, hy⟩
      show ψ (pairA F 0 ((x₀ + u) ⬝ᵥ y)) = ψ (pairA F 0 (x₀ ⬝ᵥ y))
      rw [add_dotProduct, pairA_zero_add, AddChar.map_add_eq_mul, hyU u hu, mul_one])
    a
    (by
      rintro χ ⟨y, rfl⟩ g hg
      show l (pureA F f₀ _) = l (pureA F f₀ g)
      rw [← hinv (fun i => pairA F 0 (y i)) (pureA F f₀ g) (mem_schA f₀ hg)]
      congr 1
      funext x
      simp only [pureA, dot_pairA_fin]
      ring)
  refine ⟨c, fun φ hφ => ?_⟩
  induction hφ using Submodule.span_induction with
  | mem Φ hΦ =>
    obtain ⟨f, g, hg, rfl⟩ := hΦ
    obtain ⟨α, hα⟩ := harch g hg
    have hαc : α = c * g 0 := by
      have e1 := hα f₀
      rw [hf₀, mul_one] at e1
      rw [← e1]
      exact hc g hg
    rw [hα f, hαc, pureA_zero]
    ring
  | zero => simp
  | add φ φ' _ _ h h' => rw [map_add, h, h', Pi.add_apply, mul_add]
  | smul s φ _ h => rw [map_smul, h, Pi.smul_apply, smul_eq_mul, smul_eq_mul]; ring

/- English proof (translation)
Introduce `g _`. Use `⟨g (fun i => (x i).2) • ((BoundedContinuousFunction.evalCLM ℂ (fun i => InfiniteAdeleRing.ringEquiv_mixedSpace F (x i).1)).comp (SchwartzMap.toBoundedContinuousFunctionCLM ℂ _ ℂ)), fun f => ?_⟩` and prove the remaining obligations. Simplify using `only [LinearMap.proj_apply, pureA, ContinuousLinearMap.smul_apply, ContinuousLinearMap.comp_apply, BoundedContinuousFunction.evalCLM_apply, SchwartzMap.toBoundedContinuousFunctionCLM_apply, SchwartzMap.toBoundedContinuousFunction_apply, smul_eq_mul]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem eval_mem_adm {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ] (x : κ → AF F) :
    (LinearMap.proj x : ((κ → AF F) → ℂ) →ₗ[ℂ] ℂ) ∈ (adeleClass F).adm κ := by
  intro g _
  refine ⟨g (fun i => (x i).2) • ((BoundedContinuousFunction.evalCLM ℂ
    (fun i => InfiniteAdeleRing.ringEquiv_mixedSpace F (x i).1)).comp
    (SchwartzMap.toBoundedContinuousFunctionCLM ℂ _ ℂ)), fun f => ?_⟩
  simp only [LinearMap.proj_apply, pureA, ContinuousLinearMap.smul_apply, ContinuousLinearMap.comp_apply,
    BoundedContinuousFunction.evalCLM_apply, SchwartzMap.toBoundedContinuousFunctionCLM_apply,
    SchwartzMap.toBoundedContinuousFunction_apply, smul_eq_mul]
  ring

end GlobalTheory.SvNLinear

namespace GlobalTheory.SvNLinear

open GlobalTheory.AdelicSvN

/- English proof (translation)
Introduce `_ F _ _ ψ hψ κ _ L hL hdim l₁ l₂ hi₁ hi₂ ⟨φ₀, hφ₀, hne⟩`. Take `⟨g, hg, hgL⟩` from `GlobalTheory.T.exists_symplecticBlockGenerators_lagrangian_normal_form F κ L hL hdim`. Take `⟨S, hS, hSs, hSa, hSi⟩` from `realised_of_mem_closure ψ hψ hg`. Establish `hlin : ∀ (a b : ℂ), ∀ φ ∈ schA F κ, ∀ φ' ∈ schA F κ, S (a • φ + b • φ') = a • S φ + b • S φ'`. Introduce `a b φ hφ φ' hφ'`.

Use function extensionality and compare the values at `x`. Take `⟨l', _, e⟩` from `hSa _ (eval_mem_adm x)`. Establish `hm : a • φ + b • φ' ∈ schA F κ` using `add_mem (Submodule.smul_mem _ a hφ) (Submodule.smul_mem _ b hφ')`. Establish `e1` using `e _ hm`. Establish `e2` using `e φ hφ`.

Establish `e3` using `e φ' hφ'`. Simplify using `only [LinearMap.proj_apply] at e1 e2 e3`. Rewrite using `[← e1, map_add, map_smul, map_smul, e2, e3]`. Both sides reduce to the same expression. Establish `key : ∀ l : ((κ → AF F) → ℂ) →ₗ[ℂ] ℂ, (∀ (t : AF F), ∀ w ∈ L, ∀ φ ∈ schA F κ, l (schr ψ (t • ((fun i => algebraMap F (AF F) (w.1 i)), (fun i => algebraMap F (AF F) (w.2 i)))) φ) = l φ) → ∃ c : ℂ, ∀ φ ∈ schA F κ, l (S φ) = c * φ 0`.

Introduce `l hi`. Set `f : schA F κ →ₗ[ℂ] ℂ` to `{ toFun := fun φ => l (S φ.1) map_add' := fun φ φ' => by`. Use `hlin 1 1 φ.1 φ.2 φ'.1 φ'.2` as an intermediate fact. Simplify using `only [one_smul] at this`. Simplify using `only [Submodule.coe_add, this, map_add]`.

Use the proof step `map_smul' := fun s φ => by`. Use `hlin s 0 φ.1 φ.2 0 (Submodule.zero_mem _)` as an intermediate fact. Simplify using `only [zero_smul, add_zero] at this`. Simplify using `only [Submodule.coe_smul, this, map_smul, RingHom.id_apply, smul_eq_mul] }`. Take `⟨l', hl'⟩` from `LinearMap.exists_extend f`.

Establish `e : ∀ φ (hφ : φ ∈ schA F κ), l' φ = l (S φ)` using `fun φ hφ => LinearMap.congr_fun hl' ⟨φ, hφ⟩`. Take `⟨c, hc⟩` from `charInv F ψ hψ κ l' (fun y φ hφ => by`. Establish `hm : (fun x => ψ (x ⬝ᵥ y) * φ x) = schr ψ (0, y) φ` using `by funext x; simp [schr]`. Rewrite using `[hm, e _ (GlobalTheory.HeisSchA.schr_mem_schA ψ hψ _ φ hφ), e φ hφ, hSi _ φ hφ, act_zero_eq_sum]`. Conclude with `inv_sum ψ hψ L hL l hi Finset.univ y _ (fun j => hgL _) _ (hS φ hφ))`.

Conclude with `⟨c, fun φ hφ => (e φ hφ).symm.trans (hc φ hφ)⟩`. Take `⟨c₁, h₁⟩` from `key l₁ hi₁`. Take `⟨c₂, h₂⟩` from `key l₂ hi₂`. Take `⟨ψ₀, hψ₀, rfl⟩` from `hSs φ₀ hφ₀`. Establish `hc₂ : c₂ ≠ 0` using `fun h => hne (by rw [h₂ ψ₀ hψ₀, h, zero_mul])`.

Use `⟨c₁ / c₂, fun φ hφ => ?_⟩` and prove the remaining obligations. Take `⟨φ', hφ', rfl⟩` from `hSs φ hφ`. Rewrite using `[h₁ φ' hφ', h₂ φ' hφ']`. Clear the denominators using the available nonvanishing facts.
-/
theorem main : GlobalTheory.FunPr.Hypotheses₂ → ∀ (F : Type) [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ), IsStd ψ → ∀ (κ : Type) [Fintype κ]
    (L : Submodule F ((κ → F) × (κ → F))), (∀ a ∈ L, ∀ b ∈ L, a.1 ⬝ᵥ b.2 = b.1 ⬝ᵥ a.2) →
    Module.finrank F L = Fintype.card κ → ∀ (l₁ l₂ : ((κ → AF F) → ℂ) →ₗ[ℂ] ℂ),
    (∀ (t : AF F), ∀ w ∈ L, ∀ φ ∈ schA F κ,
      l₁ (schr ψ (t • ((fun i => algebraMap F (AF F) (w.1 i)), (fun i => algebraMap F (AF F) (w.2 i)))) φ) = l₁ φ) →
    (∀ (t : AF F), ∀ w ∈ L, ∀ φ ∈ schA F κ,
      l₂ (schr ψ (t • ((fun i => algebraMap F (AF F) (w.1 i)), (fun i => algebraMap F (AF F) (w.2 i)))) φ) = l₂ φ) →
    (∃ φ ∈ schA F κ, l₂ φ ≠ 0) → ∃ c : ℂ, ∀ φ ∈ schA F κ, l₁ φ = c * l₂ φ := by
  intro _ F _ _ ψ hψ κ _ L hL hdim l₁ l₂ hi₁ hi₂ ⟨φ₀, hφ₀, hne⟩
  classical
  obtain ⟨g, hg, hgL⟩ := GlobalTheory.T.exists_symplecticBlockGenerators_lagrangian_normal_form F κ L hL hdim
  obtain ⟨S, hS, hSs, hSa, hSi⟩ := realised_of_mem_closure ψ hψ hg

  have hlin : ∀ (a b : ℂ), ∀ φ ∈ schA F κ, ∀ φ' ∈ schA F κ, S (a • φ + b • φ') = a • S φ + b • S φ' := by
    intro a b φ hφ φ' hφ'
    funext x
    obtain ⟨l', _, e⟩ := hSa _ (eval_mem_adm x)
    have hm : a • φ + b • φ' ∈ schA F κ := add_mem (Submodule.smul_mem _ a hφ) (Submodule.smul_mem _ b hφ')
    have e1 := e _ hm
    have e2 := e φ hφ
    have e3 := e φ' hφ'
    simp only [LinearMap.proj_apply] at e1 e2 e3
    rw [← e1, map_add, map_smul, map_smul, e2, e3]
    rfl
  have key : ∀ l : ((κ → AF F) → ℂ) →ₗ[ℂ] ℂ, (∀ (t : AF F), ∀ w ∈ L, ∀ φ ∈ schA F κ,
      l (schr ψ (t • ((fun i => algebraMap F (AF F) (w.1 i)), (fun i => algebraMap F (AF F) (w.2 i)))) φ) = l φ) →
      ∃ c : ℂ, ∀ φ ∈ schA F κ, l (S φ) = c * φ 0 := by
    intro l hi
    let f : schA F κ →ₗ[ℂ] ℂ :=
      { toFun := fun φ => l (S φ.1)
        map_add' := fun φ φ' => by
          have := hlin 1 1 φ.1 φ.2 φ'.1 φ'.2
          simp only [one_smul] at this
          simp only [Submodule.coe_add, this, map_add]
        map_smul' := fun s φ => by
          have := hlin s 0 φ.1 φ.2 0 (Submodule.zero_mem _)
          simp only [zero_smul, add_zero] at this
          simp only [Submodule.coe_smul, this, map_smul, RingHom.id_apply, smul_eq_mul] }
    obtain ⟨l', hl'⟩ := LinearMap.exists_extend f
    have e : ∀ φ (hφ : φ ∈ schA F κ), l' φ = l (S φ) := fun φ hφ => LinearMap.congr_fun hl' ⟨φ, hφ⟩
    obtain ⟨c, hc⟩ := charInv F ψ hψ κ l' (fun y φ hφ => by
      have hm : (fun x => ψ (x ⬝ᵥ y) * φ x) = schr ψ (0, y) φ := by funext x; simp [schr]
      rw [hm, e _ (GlobalTheory.HeisSchA.schr_mem_schA ψ hψ _ φ hφ), e φ hφ, hSi _ φ hφ, act_zero_eq_sum]
      exact inv_sum ψ hψ L hL l hi Finset.univ y _ (fun j => hgL _) _ (hS φ hφ))
    exact ⟨c, fun φ hφ => (e φ hφ).symm.trans (hc φ hφ)⟩
  obtain ⟨c₁, h₁⟩ := key l₁ hi₁
  obtain ⟨c₂, h₂⟩ := key l₂ hi₂
  obtain ⟨ψ₀, hψ₀, rfl⟩ := hSs φ₀ hφ₀
  have hc₂ : c₂ ≠ 0 := fun h => hne (by rw [h₂ ψ₀ hψ₀, h, zero_mul])
  refine ⟨c₁ / c₂, fun φ hφ => ?_⟩
  obtain ⟨φ', hφ', rfl⟩ := hSs φ hφ
  rw [h₁ φ' hφ', h₂ φ' hφ']
  field_simp

end GlobalTheory.SvNLinear

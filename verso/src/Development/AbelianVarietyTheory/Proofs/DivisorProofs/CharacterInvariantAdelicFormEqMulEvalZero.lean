import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormIteratedFDerivRemCompLe
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzVanishingDecomposition
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TraceFormMapSurjective
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEqMulApplyZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCompactOpenSeparating
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped Matrix TensorProduct

namespace GlobalTheory.CharInvForm

/- English proof (translation)
Take `⟨f, -, hc, hs, -, h1⟩` from `exists_contDiff_tsupport_subset (x := (0 : V)) (s := Set.univ) (n := ⊤) Filter.univ_mem`. Establish `hc' : HasCompactSupport (fun x => (f x : ℂ))` using `hc.comp_left Complex.ofReal_zero`. Establish `hs' : ContDiff ℝ (↑(⊤ : ℕ∞)) (fun x => (f x : ℂ))` using `Complex.ofRealCLM.contDiff.comp hs`. Conclude with `⟨hc'.toSchwartzMap hs', by simp [h1]⟩`.
-/
theorem exists_schwartz_one (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] :
    ∃ f₀ : SchwartzMap V ℂ, f₀ 0 = 1 := by
  obtain ⟨f, -, hc, hs, -, h1⟩ :=
    exists_contDiff_tsupport_subset (x := (0 : V)) (s := Set.univ) (n := ⊤) Filter.univ_mem
  have hc' : HasCompactSupport (fun x => (f x : ℂ)) := hc.comp_left Complex.ofReal_zero
  have hs' : ContDiff ℝ (↑(⊤ : ℕ∞)) (fun x => (f x : ℂ)) := Complex.ofRealCLM.contDiff.comp hs
  exact ⟨hc'.toSchwartzMap hs', by simp [h1]⟩

/- English proof (translation)
Take `⟨f₀, hf₀⟩` from `exists_schwartz_one V`. Use `⟨T f₀, fun f => ?_⟩` and prove the remaining obligations. Establish `h0 : (f - f 0 • f₀) 0 = 0` using `by simp [hf₀]`. Take `⟨n, L, h, g, hg, hsum⟩` from `GlobalTheory.SchwartzDiv.hadamard V _ h0`. Establish `e : f - f 0 • f₀ = ∑ i, g i`.

Use extensionality with `x`. Rewrite using `[hsum x, SchwartzMap.sum_apply]`. Establish `: T (f - f 0 • f₀) = 0`. Rewrite using `[e, map_sum]`. Conclude with `Finset.sum_eq_zero fun i _ => GlobalTheory.CharFormDeriv.charForm_kills_linear_mul V T hT (L i) (h i) (g i) (hg i)`.

Rewrite `this` using `[map_sub, map_smul, sub_eq_zero]`. Rewrite using `[this, smul_eq_mul, mul_comm]`.
-/
theorem arch (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    (T : SchwartzMap V ℂ →L[ℂ] ℂ)
    (hT : ∀ (L : V →L[ℝ] ℝ) (f f' : SchwartzMap V ℂ),
      (∀ x, f' x = Complex.exp (Complex.I * (L x : ℂ)) * f x) → T f' = T f) :
    ∃ a : ℂ, ∀ f : SchwartzMap V ℂ, T f = a * f 0 := by
  obtain ⟨f₀, hf₀⟩ := exists_schwartz_one V
  refine ⟨T f₀, fun f => ?_⟩
  have h0 : (f - f 0 • f₀) 0 = 0 := by simp [hf₀]
  obtain ⟨n, L, h, g, hg, hsum⟩ := GlobalTheory.SchwartzDiv.hadamard V _ h0
  have e : f - f 0 • f₀ = ∑ i, g i := by
    ext x
    rw [hsum x, SchwartzMap.sum_apply]
  have : T (f - f 0 • f₀) = 0 := by
    rw [e, map_sum]
    exact Finset.sum_eq_zero fun i _ => GlobalTheory.CharFormDeriv.charForm_kills_linear_mul V T hT (L i) (h i) (g i) (hg i)
  rw [map_sub, map_smul, sub_eq_zero] at this
  rw [this, smul_eq_mul, mul_comm]

end GlobalTheory.CharInvForm

namespace GlobalTheory.CharInvForm

open scoped Classical

variable {F : Type} [Field F] [NumberField F]

/- English proof (translation)
The claim follows from `Prod.ext (zero_add (0 : Ainf F)).symm rfl`.
-/
theorem pairA_zero_add (a b : Af F) : pairA F 0 (a + b) = pairA F 0 a + pairA F 0 b :=
  Prod.ext (zero_add (0 : Ainf F)).symm rfl

/- English proof (translation)
Establish `h1 : (RingHom.fst (Ainf F) (Af F)) (x ⬝ᵥ fun i => pairA F 0 (y i)) = 0`. Simplify using `only [dotProduct, map_sum, map_mul]`. Conclude with `Finset.sum_eq_zero fun i _ => by show (RingHom.fst (Ainf F) (Af F)) (x i) * 0 = 0`. Conclude with `mul_zero _`. Establish `h2 : (RingHom.snd (Ainf F) (Af F)) (x ⬝ᵥ fun i => pairA F 0 (y i)) = (fun i => (x i).2) ⬝ᵥ y`.

Simplify using `only [dotProduct, map_sum, map_mul]`. Both sides reduce to the same expression. Conclude with `Prod.ext h1 h2`.
-/
theorem dot_pairA_fin {κ : Type} [Fintype κ] (x : κ → AF F) (y : κ → Af F) :
    (x ⬝ᵥ fun i => pairA F 0 (y i)) = pairA F 0 ((fun i => (x i).2) ⬝ᵥ y) := by
  have h1 : (RingHom.fst (Ainf F) (Af F)) (x ⬝ᵥ fun i => pairA F 0 (y i)) = 0 := by
    simp only [dotProduct, map_sum, map_mul]
    exact Finset.sum_eq_zero fun i _ => by
      show (RingHom.fst (Ainf F) (Af F)) (x i) * 0 = 0
      exact mul_zero _
  have h2 : (RingHom.snd (Ainf F) (Af F)) (x ⬝ᵥ fun i => pairA F 0 (y i)) = (fun i => (x i).2) ⬝ᵥ y := by
    simp only [dotProduct, map_sum, map_mul]
    rfl
  exact Prod.ext h1 h2

/- English proof (translation)
Establish `h1 : (RingHom.fst (Ainf F) (Af F)) (x ⬝ᵥ fun i => pairA F (y i) 0) = ∑ i, (x i).1 * y i`. Simplify using `only [dotProduct, map_sum, map_mul]`. Both sides reduce to the same expression. Establish `h2 : (RingHom.snd (Ainf F) (Af F)) (x ⬝ᵥ fun i => pairA F (y i) 0) = 0`. Simplify using `only [dotProduct, map_sum, map_mul]`.

Conclude with `Finset.sum_eq_zero fun i _ => by show (RingHom.snd (Ainf F) (Af F)) (x i) * 0 = 0`. Conclude with `mul_zero _`. Conclude with `Prod.ext h1 h2`.
-/
theorem dot_pairA_inf {κ : Type} [Fintype κ] (x : κ → AF F) (y : κ → Ainf F) :
    (x ⬝ᵥ fun i => pairA F (y i) 0) = pairA F (∑ i, (x i).1 * y i) 0 := by
  have h1 : (RingHom.fst (Ainf F) (Af F)) (x ⬝ᵥ fun i => pairA F (y i) 0) = ∑ i, (x i).1 * y i := by
    simp only [dotProduct, map_sum, map_mul]
    rfl
  have h2 : (RingHom.snd (Ainf F) (Af F)) (x ⬝ᵥ fun i => pairA F (y i) 0) = 0 := by
    simp only [dotProduct, map_sum, map_mul]
    exact Finset.sum_eq_zero fun i _ => by
      show (RingHom.snd (Ainf F) (Af F)) (x i) * 0 = 0
      exact mul_zero _
  exact Prod.ext h1 h2

/- English proof (translation)
The claim follows from `Submodule.subset_span ⟨f, g, hg, rfl⟩`.
-/
theorem mem_schA {κ : Type} [Fintype κ] (f : SchwartzMap (κ → mixedEmbedding.mixedSpace F) ℂ)
    {g : (κ → Af F) → ℂ} (hg : g ∈ SB (κ → Af F)) : pureA F f g ∈ schA F κ :=
  Submodule.subset_span ⟨f, g, hg, rfl⟩

/- English proof (translation)
Simplify using `only [pureA]`. Use `congr 2`. Use function extensionality and compare the values at `i`. Conclude with `map_zero (InfiniteAdeleRing.ringEquiv_mixedSpace F)`.
-/
theorem pureA_zero {κ : Type} (f : (κ → mixedEmbedding.mixedSpace F) → ℂ) (g : (κ → Af F) → ℂ) :
    pureA F f g 0 = f 0 * g 0 := by
  simp only [pureA]
  congr 2
  · funext i
    exact map_zero (InfiniteAdeleRing.ringEquiv_mixedSpace F)

end GlobalTheory.CharInvForm

namespace GlobalTheory.CharInvForm

open scoped Classical

/- English proof (translation)
Establish `hat : At (evI F) (pairA F (∑ i, (x i).1 * (InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (Y i)) 0)`. Introduce `u hu`. Establish `h1 : u.1 = 0` using `(InfiniteAdeleRing.ringEquiv_mixedSpace F).injective (by rw [map_zero]; exact hu)`. Use `show (u.1 * _, u.2 * 0) = ((0 : Ainf F), (0 : Af F))`. Rewrite using `[h1, zero_mul, mul_zero]`.

Rewrite using `[dot_pairA_inf, hψ.2.2 _ hat]`. Use `show Complex.exp (_ * ((Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (InfiniteAdeleRing.ringEquiv_mixedSpace F (∑ i, (x i).1 * (InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (Y i))) : ℝ) : ℂ)) = _`. Rewrite using `[map_sum, map_sum]`. Simplify using `only [map_mul, RingEquiv.apply_symm_apply]`. Use `congr 1`.

Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem psi_dot_inf {F : Type} [Field F] [NumberField F] {ψ : AddChar (AF F) ℂ} (hψ : IsStd ψ) {κ : Type} [Fintype κ]
    (x : κ → AF F) (Y : κ → mixedEmbedding.mixedSpace F) :
    ψ (x ⬝ᵥ fun i => pairA F ((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (Y i)) 0) =
      Complex.exp (Complex.I * ((-(2 * Real.pi) * ∑ i, Algebra.trace ℝ (mixedEmbedding.mixedSpace F)
        ((fun i => InfiniteAdeleRing.ringEquiv_mixedSpace F (x i).1) i * Y i) : ℝ) : ℂ)) := by
  have hat : At (evI F) (pairA F (∑ i, (x i).1 * (InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (Y i)) 0) := by
    intro u hu
    have h1 : u.1 = 0 := (InfiniteAdeleRing.ringEquiv_mixedSpace F).injective (by rw [map_zero]; exact hu)
    show (u.1 * _, u.2 * 0) = ((0 : Ainf F), (0 : Af F))
    rw [h1, zero_mul, mul_zero]
  rw [dot_pairA_inf, hψ.2.2 _ hat]
  show Complex.exp (_ * ((Algebra.trace ℝ (mixedEmbedding.mixedSpace F)
    (InfiniteAdeleRing.ringEquiv_mixedSpace F (∑ i, (x i).1 * (InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (Y i))) : ℝ) : ℂ)) = _
  rw [map_sum, map_sum]
  simp only [map_mul, RingEquiv.apply_symm_apply]
  congr 1
  push_cast
  ring

/- English proof (translation)
Introduce `F _ _ ψ hψ κ _ l hl hinv`. Establish `harch : ∀ g ∈ SB (κ → Af F), ∃ α : ℂ, ∀ f : SchwartzMap (κ → mixedEmbedding.mixedSpace F) ℂ, l (pureA F f g) = α * f 0`. Introduce `g hg`. Take `⟨T, hT⟩` from `hl g hg`. Take `⟨α, hα⟩` from `arch _ T (by`.

Introduce `L f f' hff'`. Take `⟨Y, hY⟩` from `GlobalTheory.TraceDual.exists_trace_rep F κ L`. Rewrite using `[← hT, ← hT, ← hinv (fun i => pairA F ((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (Y i)) 0) (pureA F f g) (mem_schA f hg)]`. Use `congr 1`. Use function extensionality and compare the values at `x`.

Simplify using `only [pureA, hff', psi_dot_inf hψ, hY]`. Use the proof step `ring)`. Conclude with `⟨α, fun f => (hT f).trans (hα f)⟩`. Take `⟨f₀, hf₀⟩` from `exists_schwartz_one (κ → mixedEmbedding.mixedSpace F)`. Set `a : ((κ → Af F) → ℂ) →ₗ[ℂ] ℂ` to `{ toFun := fun g => l (pureA F f₀ g) map_add' := fun g g' => by`.

Rewrite using `[← map_add]`. Use `congr 1`. Use function extensionality and compare the values at `x`. Simplify using `only [pureA, Pi.add_apply]`. Expand and normalize the polynomial expressions, which then agree.

Use the proof step `map_smul' := fun s g => by`. Rewrite using `[RingHom.id_apply, ← map_smul]`. Use `congr 1`. Use function extensionality and compare the values at `x`. Simplify using `only [pureA, Pi.smul_apply, smul_eq_mul]`.

Use `ring }`. Take `⟨c, hc⟩` from `GlobalTheory.CharForm.exists_eq_mul_apply_zero (κ → Af F) {χ | ∃ y : κ → Af F, χ = fun x => ψ (pairA F 0 (x ⬝ᵥ y))} (by`. Introduce `N hN`. Take `⟨U, hUo, hUc, hUN, hsep⟩` from `GlobalTheory.FinSepChar.finite_chars_separate F ψ hψ κ N hN`. Use `⟨U, hUo, hUc, hUN, fun x₀ hx₀ => ?_⟩` and prove the remaining obligations.

Take `⟨y, hyU, hy⟩` from `hsep x₀ hx₀`. Use `⟨_, ⟨y, rfl⟩, fun u hu => ?_, hy⟩` and prove the remaining obligations. Use `show ψ (pairA F 0 ((x₀ + u) ⬝ᵥ y)) = ψ (pairA F 0 (x₀ ⬝ᵥ y))`. Rewrite using `[add_dotProduct, pairA_zero_add, AddChar.map_add_eq_mul, hyU u hu, mul_one])`. Use `a`.

Use the proof step `(by`. Introduce and unpack `χ ⟨y, rfl⟩ g hg`. Use `show l (pureA F f₀ _) = l (pureA F f₀ g)`. Rewrite using `[← hinv (fun i => pairA F 0 (y i)) (pureA F f₀ g) (mem_schA f₀ hg)]`. Use `congr 1`.

Use function extensionality and compare the values at `x`. Simplify using `only [pureA, dot_pairA_fin]`. Use the proof step `ring)`. Use `⟨c, fun φ hφ => ?_⟩` and prove the remaining obligations. Proceed by induction on `hφ using Submodule.span_induction with`.

Consider the case `mem Φ hΦ`. Take `⟨f, g, hg, rfl⟩` from `hΦ`. Take `⟨α, hα⟩` from `harch g hg`. Establish `hαc : α = c * g 0`. Establish `e1` using `hα f₀`.

Rewrite `e1` using `[hf₀, mul_one]`. Rewrite using `[← e1]`. Conclude with `hc g hg`. Rewrite using `[hα f, hαc, pureA_zero]`. Expand and normalize the polynomial expressions, which then agree.

Consider the case `zero => simp`. Consider the case `add φ φ' _ _ h h' => rw [map_add, h, h', Pi.add_apply, mul_add]`. Consider the case `smul s φ _ h => rw [map_smul, h, Pi.smul_apply, smul_eq_mul, smul_eq_mul]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem main : ∀ (F : Type) [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ), IsStd ψ → ∀ (κ : Type) [Fintype κ]
    (l : ((κ → AF F) → ℂ) →ₗ[ℂ] ℂ), l ∈ (adeleClass F).adm κ →
    (∀ (y : κ → AF F), ∀ φ ∈ schA F κ, l (fun x => ψ (x ⬝ᵥ y) * φ x) = l φ) →
    ∃ c : ℂ, ∀ φ ∈ schA F κ, l φ = c * φ 0 := by
  intro F _ _ ψ hψ κ _ l hl hinv

  have harch : ∀ g ∈ SB (κ → Af F), ∃ α : ℂ,
      ∀ f : SchwartzMap (κ → mixedEmbedding.mixedSpace F) ℂ, l (pureA F f g) = α * f 0 := by
    intro g hg
    obtain ⟨T, hT⟩ := hl g hg
    obtain ⟨α, hα⟩ := arch _ T (by
      intro L f f' hff'
      obtain ⟨Y, hY⟩ := GlobalTheory.TraceDual.exists_trace_rep F κ L
      rw [← hT, ← hT, ← hinv (fun i => pairA F ((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (Y i)) 0)
        (pureA F f g) (mem_schA f hg)]
      congr 1
      funext x
      simp only [pureA, hff', psi_dot_inf hψ, hY]
      ring)
    exact ⟨α, fun f => (hT f).trans (hα f)⟩

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

end GlobalTheory.CharInvForm

/- English proof (translation)
The claim follows from `GlobalTheory.CharInvForm.main`.
-/
example : ∀ (F : Type) [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ), IsStd ψ → ∀ (κ : Type) [Fintype κ] (l : ((κ → AF F) → ℂ) →ₗ[ℂ] ℂ), l ∈ (adeleClass F).adm κ → (∀ (y : κ → AF F), ∀ φ ∈ schA F κ, l (fun x => ψ (x ⬝ᵥ y) * φ x) = l φ) → ∃ c : ℂ, ∀ φ ∈ schA F κ, l φ = c * φ 0 := GlobalTheory.CharInvForm.main

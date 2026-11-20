import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DarbouxCoordinatesInsertZero
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.PlaneEv

noncomputable section

namespace GlobalTheory.ThK.PlaneEv.Clo

open scoped Classical

variable {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ]

def trL (b : κ → mixedEmbedding.mixedSpace F) : (κ → mixedEmbedding.mixedSpace F) →L[ℝ] ℝ :=
  LinearMap.toContinuousLinearMap
    ((Algebra.trace ℝ (mixedEmbedding.mixedSpace F)) ∘ₗ
      ∑ i, (LinearMap.mulRight ℝ (b i)) ∘ₗ LinearMap.proj i)

/- English proof (translation)
Simplify using `[trL]`.
-/
theorem trL_apply (b x : κ → mixedEmbedding.mixedSpace F) :
    trL b x = Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (∑ i, x i * b i) := by
  simp [trL]

/- English proof (translation)
Use function extensionality and compare the values at `x`. Simplify using `[dH, trL_apply]`.
-/
theorem dH_eq (a b : κ → mixedEmbedding.mixedSpace F) (f : (κ → mixedEmbedding.mixedSpace F) → ℂ) :
    dH a b f = fun x => fderiv ℝ f x a - 2 * Real.pi * Complex.I * ((trL b x : ℝ) : ℂ) * f x := by
  funext x; simp [dH, trL_apply]

/- English proof (translation)
Rewrite using `[dH_eq]`.
-/
theorem dH_apply' (a b : κ → mixedEmbedding.mixedSpace F) (f : (κ → mixedEmbedding.mixedSpace F) → ℂ) (x) :
    dH a b f x = fderiv ℝ f x a - 2 * Real.pi * Complex.I * ((trL b x : ℝ) : ℂ) * f x := by
  rw [dH_eq]

/- English proof (translation)
Establish `hff : HasFDerivAt (fderiv ℝ f) (fderiv ℝ (fderiv ℝ f) x) x` using `((hf.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num) x).hasFDerivAt`. Establish `h1 : HasFDerivAt (fun y => fderiv ℝ f y a') ((fderiv ℝ (fderiv ℝ f) x).flip a') x`. Simplify using `using hff.clm_apply (hasFDerivAt_const a' x)`. Establish `h2 : HasFDerivAt (fun y => ((trL b' y : ℝ) : ℂ)) (Complex.ofRealCLM.comp (trL b')) x` using `(Complex.ofRealCLM.comp (trL b')).hasFDerivAt`. Establish `h3 : HasFDerivAt f (fderiv ℝ f x) x` using `(hf.differentiable (by norm_num) x).hasFDerivAt`.

Establish `h4` using `h1.sub ((h2.const_mul (2 * Real.pi * Complex.I : ℂ)).mul h3)`. Establish `h5 : HasFDerivAt (fun y => fderiv ℝ f y a' - 2 * Real.pi * Complex.I * ((trL b' y : ℝ) : ℂ) * f y) _ x` using `h4`. Rewrite using `[dH_eq, h5.fderiv]`. Simplify using the standard rewrite rules. Expand and normalize the polynomial expressions, which then agree.
-/
theorem fderiv_dH_apply (f : (κ → mixedEmbedding.mixedSpace F) → ℂ) (hf : ContDiff ℝ 2 f)
    (a' b' a x : κ → mixedEmbedding.mixedSpace F) :
    fderiv ℝ (dH a' b' f) x a = fderiv ℝ (fderiv ℝ f) x a a'
      - 2 * Real.pi * Complex.I * ((trL b' a : ℝ) : ℂ) * f x
      - 2 * Real.pi * Complex.I * ((trL b' x : ℝ) : ℂ) * fderiv ℝ f x a := by
  have hff : HasFDerivAt (fderiv ℝ f) (fderiv ℝ (fderiv ℝ f) x) x :=
    ((hf.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num) x).hasFDerivAt
  have h1 : HasFDerivAt (fun y => fderiv ℝ f y a') ((fderiv ℝ (fderiv ℝ f) x).flip a') x := by
    simpa using hff.clm_apply (hasFDerivAt_const a' x)
  have h2 : HasFDerivAt (fun y => ((trL b' y : ℝ) : ℂ)) (Complex.ofRealCLM.comp (trL b')) x :=
    (Complex.ofRealCLM.comp (trL b')).hasFDerivAt
  have h3 : HasFDerivAt f (fderiv ℝ f x) x := (hf.differentiable (by norm_num) x).hasFDerivAt
  have h4 := h1.sub ((h2.const_mul (2 * Real.pi * Complex.I : ℂ)).mul h3)
  have h5 : HasFDerivAt (fun y => fderiv ℝ f y a' - 2 * Real.pi * Complex.I * ((trL b' y : ℝ) : ℂ) * f y) _ x := h4
  rw [dH_eq, h5.fderiv]
  simp
  ring

/- English proof (translation)
Establish `hs` using `(hf.contDiffAt (x := x)).isSymmSndFDerivAt (by simp [minSmoothness_of_isRCLikeNormedField])`. Establish `e1` using `fderiv_dH_apply f hf a' b' a x`. Establish `e2` using `fderiv_dH_apply f hf a b a' x`. Rewrite using `[dH_apply' a b (dH a' b' f), dH_apply' a' b' (dH a b f), e1, e2, dH_apply' a' b' f, dH_apply' a b f, hs a a']`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem dH_comm (f : (κ → mixedEmbedding.mixedSpace F) → ℂ) (hf : ContDiff ℝ 2 f)
    (a b a' b' x : κ → mixedEmbedding.mixedSpace F) :
    dH a b (dH a' b' f) x - dH a' b' (dH a b f) x =
      -(2 * Real.pi * Complex.I * (((trL b' a : ℝ) : ℂ) - ((trL b a' : ℝ) : ℂ))) * f x := by
  have hs := (hf.contDiffAt (x := x)).isSymmSndFDerivAt (by simp [minSmoothness_of_isRCLikeNormedField])
  have e1 := fderiv_dH_apply f hf a' b' a x
  have e2 := fderiv_dH_apply f hf a b a' x
  rw [dH_apply' a b (dH a' b' f), dH_apply' a' b' (dH a b f), e1, e2, dH_apply' a' b' f, dH_apply' a b f, hs a a']
  ring

/- English proof (translation)
Simplify using `only [trL_apply, Pi.add_apply, mul_add, Finset.sum_add_distrib, map_add]`.
-/
theorem trL_add (b b' x : κ → mixedEmbedding.mixedSpace F) : trL (b + b') x = trL b x + trL b' x := by
  simp only [trL_apply, Pi.add_apply, mul_add, Finset.sum_add_distrib, map_add]

/- English proof (translation)
Simplify using `[trL_apply]`.
-/
theorem trL_zero (x : κ → mixedEmbedding.mixedSpace F) : trL 0 x = 0 := by
  simp [trL_apply]

def Dop (hD : HasDH F κ) (a b : κ → mixedEmbedding.mixedSpace F) : SInf F κ →ₗ[ℂ] SInf F κ where
  toFun f := Classical.choose (hD a b f)
  map_add' f g := by
    ext x
    rw [SchwartzMap.add_apply, congrFun (Classical.choose_spec (hD a b (f + g))) x,
      congrFun (Classical.choose_spec (hD a b f)) x, congrFun (Classical.choose_spec (hD a b g)) x,
      dH_apply', dH_apply', dH_apply']
    have h := (f.differentiableAt (x := x)).hasFDerivAt.add (g.differentiableAt (x := x)).hasFDerivAt
    have h' : HasFDerivAt (⇑(f + g)) (fderiv ℝ f x + fderiv ℝ g x) x := h
    rw [h'.fderiv]
    simp only [ContinuousLinearMap.add_apply, SchwartzMap.add_apply]
    ring
  map_smul' c f := by
    ext x
    rw [SchwartzMap.smul_apply, congrFun (Classical.choose_spec (hD a b (c • f))) x,
      congrFun (Classical.choose_spec (hD a b f)) x, dH_apply', dH_apply']
    have h := (f.differentiableAt (x := x)).hasFDerivAt.const_smul c
    have h' : HasFDerivAt (⇑(c • f)) (c • fderiv ℝ f x) x := h
    rw [h'.fderiv]
    simp only [ContinuousLinearMap.smul_apply, SchwartzMap.smul_apply, smul_eq_mul, RingHom.id_apply]
    ring

/- English proof (translation)
The claim follows from `Classical.choose_spec (hD a b f)`.
-/
theorem coe_Dop (hD : HasDH F κ) (a b : κ → mixedEmbedding.mixedSpace F) (f : SInf F κ) :
    ⇑(Dop hD a b f) = dH a b ⇑f :=
  Classical.choose_spec (hD a b f)

/- English proof (translation)
The claim follows from `DFunLike.coe_injective (by rw [h, coe_Dop])`.
-/
theorem Dop_eq_of (hD : HasDH F κ) (a b : κ → mixedEmbedding.mixedSpace F) (f f₁ : SInf F κ)
    (h : ⇑f₁ = dH a b ⇑f) : f₁ = Dop hD a b f :=
  DFunLike.coe_injective (by rw [h, coe_Dop])

/- English proof (translation)
Use extensionality with `f x`. Simplify using `only [LinearMap.sub_apply, Module.End.mul_apply, Module.algebraMap_end_apply, SchwartzMap.sub_apply, SchwartzMap.smul_apply, smul_eq_mul]`. Rewrite using `[coe_Dop, coe_Dop, coe_Dop, coe_Dop]`. Conclude with `dH_comm _ (f.smooth 2) a b a' b' x`.
-/
theorem Dop_comm (hD : HasDH F κ) (a b a' b' : κ → mixedEmbedding.mixedSpace F) :
    Dop hD a b * Dop hD a' b' - Dop hD a' b' * Dop hD a b =
      algebraMap ℂ (Module.End ℂ (SInf F κ))
        (-(2 * Real.pi * Complex.I * (((trL b' a : ℝ) : ℂ) - ((trL b a' : ℝ) : ℂ)))) := by
  ext f x
  simp only [LinearMap.sub_apply, Module.End.mul_apply, Module.algebraMap_end_apply, SchwartzMap.sub_apply,
    SchwartzMap.smul_apply, smul_eq_mul]
  rw [coe_Dop, coe_Dop, coe_Dop, coe_Dop]
  exact dH_comm _ (f.smooth 2) a b a' b' x

/- English proof (translation)
Use extensionality with `f x`. Simplify using `only [LinearMap.add_apply, SchwartzMap.add_apply]`. Rewrite using `[coe_Dop, coe_Dop, coe_Dop, dH_apply', dH_apply', dH_apply', map_add, trL_add]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem Dop_add (hD : HasDH F κ) (a b a' b' : κ → mixedEmbedding.mixedSpace F) :
    Dop hD (a + a') (b + b') = Dop hD a b + Dop hD a' b' := by
  ext f x
  simp only [LinearMap.add_apply, SchwartzMap.add_apply]
  rw [coe_Dop, coe_Dop, coe_Dop, dH_apply', dH_apply', dH_apply', map_add, trL_add]
  push_cast
  ring

section Plane

variable {n d d₁ : ℕ} (hd : d = d₁ + 2)

/- English proof (translation)
Rewrite using `[trL_apply]`. Establish `: (∑ i, ins0 hd a₁ i * β i) = ins0 hd a₁ ⬝ᵥ β` using `rfl`. Rewrite using `[this, ins0_dotProduct]`. Establish `h0 : (fun p => β ((idx hd).symm (Sum.inl p))) = 0` using `funext hβ`. Rewrite using `[h0, dotProduct_zero, map_zero]`.
-/
theorem trL_ins0_of_isPl (β : Fin n × Fin d → mixedEmbedding.mixedSpace F) (hβ : IsPl hd β)
    (a₁ : Fin n × Fin d₁ → mixedEmbedding.mixedSpace F) : trL β (ins0 hd a₁) = 0 := by
  rw [trL_apply]
  have : (∑ i, ins0 hd a₁ i * β i) = ins0 hd a₁ ⬝ᵥ β := rfl
  rw [this, ins0_dotProduct]
  have h0 : (fun p => β ((idx hd).symm (Sum.inl p))) = 0 := funext hβ
  rw [h0, dotProduct_zero, map_zero]

/- English proof (translation)
Rewrite using `[trL_apply]`. Establish `: (∑ i, γ i * ins0 hd b₁ i) = ins0 hd b₁ ⬝ᵥ γ` using `by rw [dotProduct_comm]; rfl`. Rewrite using `[this, ins0_dotProduct]`. Establish `h0 : (fun p => γ ((idx hd).symm (Sum.inl p))) = 0` using `funext hγ`. Rewrite using `[h0, dotProduct_zero, map_zero]`.
-/
theorem trL_of_isPl_ins0 (γ : Fin n × Fin d → mixedEmbedding.mixedSpace F) (hγ : IsPl hd γ)
    (b₁ : Fin n × Fin d₁ → mixedEmbedding.mixedSpace F) : trL (ins0 hd b₁) γ = 0 := by
  rw [trL_apply]
  have : (∑ i, γ i * ins0 hd b₁ i) = ins0 hd b₁ ⬝ᵥ γ := by rw [dotProduct_comm]; rfl
  rw [this, ins0_dotProduct]
  have h0 : (fun p => γ ((idx hd).symm (Sum.inl p))) = 0 := funext hγ
  rw [h0, dotProduct_zero, map_zero]

/- English proof (translation)
Introduce `p`. Simplify using the standard rewrite rules.
-/
theorem isPl_sub_ins0 (a : Fin n × Fin d → mixedEmbedding.mixedSpace F) :
    IsPl hd (a - ins0 hd fun p => a ((idx hd).symm (Sum.inl p))) := by
  intro p
  simp

variable (hD : HasDH F (Fin n × Fin d))

def Ealg : Subalgebra ℂ (Module.End ℂ (SInf F (Fin n × Fin d))) :=
  Algebra.adjoin ℂ {T | ∃ a₁ b₁ : Fin n × Fin d₁ → mixedEmbedding.mixedSpace F, T = Dop hD (ins0 hd a₁) (ins0 hd b₁)}

def Balg : Subalgebra ℂ (Module.End ℂ (SInf F (Fin n × Fin d))) :=
  Algebra.adjoin ℂ {T | ∃ β : Fin n × Fin d → mixedEmbedding.mixedSpace F, IsPl hd β ∧ T = Dop hD 0 β}

/- English proof (translation)
Rewrite `h` using `[map_zero]`. Conclude with `sub_eq_zero.1 h`.
-/
theorem comm_of_zero {X Y : Module.End ℂ (SInf F (Fin n × Fin d))}
    (h : X * Y - Y * X = algebraMap ℂ _ 0) : X * Y = Y * X := by
  rw [map_zero] at h; exact sub_eq_zero.1 h

/- English proof (translation)
Introduce `S hS`. Establish `: Ealg hd hD ≤ Subalgebra.centralizer ℂ {T}`. Use `Algebra.adjoin_le ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨a₁, b₁, rfl⟩`. Rewrite using `[SetLike.mem_coe, Subalgebra.mem_centralizer_iff]`.

Introduce and unpack `_ rfl`. Conclude with `hT a₁ b₁`. Conclude with `((Subalgebra.mem_centralizer_iff ℂ).1 (this hS) T rfl)`.
-/
theorem mem_centralizer_E (T : Module.End ℂ (SInf F (Fin n × Fin d)))
    (hT : ∀ a₁ b₁ : Fin n × Fin d₁ → mixedEmbedding.mixedSpace F,
      T * Dop hD (ins0 hd a₁) (ins0 hd b₁) = Dop hD (ins0 hd a₁) (ins0 hd b₁) * T) :
    ∀ S ∈ Ealg hd hD, T * S = S * T := by
  intro S hS
  have : Ealg hd hD ≤ Subalgebra.centralizer ℂ {T} := by
    refine Algebra.adjoin_le ?_
    rintro _ ⟨a₁, b₁, rfl⟩
    rw [SetLike.mem_coe, Subalgebra.mem_centralizer_iff]
    rintro _ rfl
    exact hT a₁ b₁
  exact ((Subalgebra.mem_centralizer_iff ℂ).1 (this hS) T rfl)

/- English proof (translation)
The claim follows from `mem_centralizer_E hd hD _ fun a₁ b₁ => comm_of_zero (by rw [Dop_comm]; simp [trL_ins0_of_isPl hd β hβ, trL_zero])`.
-/
theorem B_comm_E (β : Fin n × Fin d → mixedEmbedding.mixedSpace F) (hβ : IsPl hd β) :
    ∀ S ∈ Ealg hd hD, Dop hD 0 β * S = S * Dop hD 0 β :=
  mem_centralizer_E hd hD _ fun a₁ b₁ => comm_of_zero (by
    rw [Dop_comm]; simp [trL_ins0_of_isPl hd β hβ, trL_zero])

/- English proof (translation)
The claim follows from `mem_centralizer_E hd hD _ fun a₁ b₁ => comm_of_zero (by rw [Dop_comm]; simp [trL_of_isPl_ins0 hd γ hγ, trL_zero])`.
-/
theorem C_comm_E (γ : Fin n × Fin d → mixedEmbedding.mixedSpace F) (hγ : IsPl hd γ) :
    ∀ S ∈ Ealg hd hD, Dop hD γ 0 * S = S * Dop hD γ 0 :=
  mem_centralizer_E hd hD _ fun a₁ b₁ => comm_of_zero (by
    rw [Dop_comm]; simp [trL_of_isPl_ins0 hd γ hγ, trL_zero])

/- English proof (translation)
Introduce `T hT`. Establish `: Balg hd hD ≤ Subalgebra.centralizer ℂ (Ealg hd hD : Set _)`. Use `Algebra.adjoin_le ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨β, hβ, rfl⟩`. Rewrite using `[SetLike.mem_coe, Subalgebra.mem_centralizer_iff]`.

Introduce `S hS`. Conclude with `(B_comm_E hd hD β hβ S hS).symm`. Introduce `S hS`. Conclude with `((Subalgebra.mem_centralizer_iff ℂ).1 (this hT) S hS).symm`.
-/
theorem B_comm_E' : ∀ T ∈ Balg hd hD, ∀ S ∈ Ealg hd hD, T * S = S * T := by
  intro T hT
  have : Balg hd hD ≤ Subalgebra.centralizer ℂ (Ealg hd hD : Set _) := by
    refine Algebra.adjoin_le ?_
    rintro _ ⟨β, hβ, rfl⟩
    rw [SetLike.mem_coe, Subalgebra.mem_centralizer_iff]
    intro S hS
    exact (B_comm_E hd hD β hβ S hS).symm
  intro S hS
  exact ((Subalgebra.mem_centralizer_iff ℂ).1 (this hT) S hS).symm

/- English proof (translation)
Introduce `T hT`. Proceed by induction on `hT using Algebra.adjoin_induction with`. Consider the case `mem x hx`. Take `⟨β, hβ, rfl⟩` from `hx`. Rewrite using `[Dop_comm]`.

Conclude with `Subalgebra.algebraMap_mem _ _`. Consider the case `algebraMap r`. Rewrite using `[Algebra.commutes, sub_self]`. Conclude with `zero_mem _`. Consider the case `add x y hx hy ihx ihy`.

Establish `: Dop hD γ 0 * (x + y) - (x + y) * Dop hD γ 0 = (Dop hD γ 0 * x - x * Dop hD γ 0) + (Dop hD γ 0 * y - y * Dop hD γ 0)` using `by noncomm_ring`. Rewrite using `[this]`. Conclude with `add_mem ihx ihy`. Consider the case `mul x y hx hy ihx ihy`. Establish `: Dop hD γ 0 * (x * y) - (x * y) * Dop hD γ 0 = (Dop hD γ 0 * x - x * Dop hD γ 0) * y + x * (Dop hD γ 0 * y - y * Dop hD γ 0)` using `by noncomm_ring`.

Rewrite using `[this]`. Conclude with `add_mem (mul_mem ihx hy) (mul_mem hx ihy)`.
-/
theorem C_bracket_B (γ : Fin n × Fin d → mixedEmbedding.mixedSpace F) :
    ∀ T ∈ Balg hd hD, Dop hD γ 0 * T - T * Dop hD γ 0 ∈ Balg hd hD := by
  intro T hT
  induction hT using Algebra.adjoin_induction with
  | mem x hx =>
    obtain ⟨β, hβ, rfl⟩ := hx
    rw [Dop_comm]
    exact Subalgebra.algebraMap_mem _ _
  | algebraMap r =>
    rw [Algebra.commutes, sub_self]
    exact zero_mem _
  | add x y hx hy ihx ihy =>
    have : Dop hD γ 0 * (x + y) - (x + y) * Dop hD γ 0 =
        (Dop hD γ 0 * x - x * Dop hD γ 0) + (Dop hD γ 0 * y - y * Dop hD γ 0) := by noncomm_ring
    rw [this]; exact add_mem ihx ihy
  | mul x y hx hy ihx ihy =>
    have : Dop hD γ 0 * (x * y) - (x * y) * Dop hD γ 0 =
        (Dop hD γ 0 * x - x * Dop hD γ 0) * y + x * (Dop hD γ 0 * y - y * Dop hD γ 0) := by noncomm_ring
    rw [this]; exact add_mem (mul_mem ihx hy) (mul_mem hx ihy)

/- English proof (translation)
Use extensionality with `x`. Rewrite using `[ei_apply, coe_Dop, dH_apply', trL_ins0_of_isPl hd β hβ]`. Simplify using the standard rewrite rules.
-/
theorem ei_B (β : Fin n × Fin d → mixedEmbedding.mixedSpace F) (hβ : IsPl hd β) (g : SInf F (Fin n × Fin d)) :
    ei F hd (Dop hD 0 β g) = 0 := by
  ext x
  rw [ei_apply, coe_Dop, dH_apply', trL_ins0_of_isPl hd β hβ]
  simp

/- English proof (translation)
Establish `hcomp : ⇑(ei F hd g) = ⇑g ∘ ⇑(insertZerosCLM F hd)` using `rfl`. Use function extensionality and compare the values at `x`. Rewrite using `[ei_apply, coe_Dop, hcomp]`. Simplify using `only [dH]`. Establish `hf : DifferentiableAt ℝ (⇑g) (insertZerosCLM F hd x)` using `g.differentiableAt`.

Rewrite using `[fderiv_comp x hf (insertZerosCLM F hd).differentiableAt, ContinuousLinearMap.fderiv]`. Establish `hs : (∑ i, ins0 hd x i * ins0 hd b₁ i) = ∑ i, x i * b₁ i` using `ins0_dotProduct_ins0 hd x b₁`. Rewrite using `[hs]`. Both sides reduce to the same expression.
-/
theorem ei_E (a₁ b₁ : Fin n × Fin d₁ → mixedEmbedding.mixedSpace F) (g : SInf F (Fin n × Fin d)) :
    ⇑(ei F hd (Dop hD (ins0 hd a₁) (ins0 hd b₁) g)) = dH a₁ b₁ ⇑(ei F hd g) := by
  have hcomp : ⇑(ei F hd g) = ⇑g ∘ ⇑(insertZerosCLM F hd) := rfl
  funext x
  rw [ei_apply, coe_Dop, hcomp]
  simp only [dH]
  have hf : DifferentiableAt ℝ (⇑g) (insertZerosCLM F hd x) := g.differentiableAt
  rw [fderiv_comp x hf (insertZerosCLM F hd).differentiableAt, ContinuousLinearMap.fderiv]
  have hs : (∑ i, ins0 hd x i * ins0 hd b₁ i) = ∑ i, x i * b₁ i :=
    ins0_dotProduct_ins0 hd x b₁
  rw [hs]
  rfl

/- English proof (translation)
Introduce `T hT`. Proceed by induction on `hT using Algebra.adjoin_induction with`. Consider the case `mem x hx`. Take `⟨β, hβ, rfl⟩` from `hx`. Conclude with `⟨0, fun g => by rw [ei_B hd hD β hβ, zero_smul]⟩`.

Consider the case `algebraMap r`. Conclude with `⟨r, fun g => by rw [Module.algebraMap_end_apply, map_smul]⟩`. Consider the case `add x y hx hy ihx ihy`. Take `⟨c₁, h₁⟩` from `ihx`. Take `⟨c₂, h₂⟩` from `ihy`.

Conclude with `⟨c₁ + c₂, fun g => by rw [LinearMap.add_apply, map_add, h₁, h₂, add_smul]⟩`. Consider the case `mul x y hx hy ihx ihy`. Take `⟨c₁, h₁⟩` from `ihx`. Take `⟨c₂, h₂⟩` from `ihy`. Conclude with `⟨c₁ * c₂, fun g => by rw [Module.End.mul_apply, h₁, h₂, smul_smul]⟩`.
-/
theorem ei_Balg : ∀ T ∈ Balg hd hD, ∃ c : ℂ, ∀ g, ei F hd (T g) = c • ei F hd g := by
  intro T hT
  induction hT using Algebra.adjoin_induction with
  | mem x hx =>
    obtain ⟨β, hβ, rfl⟩ := hx
    exact ⟨0, fun g => by rw [ei_B hd hD β hβ, zero_smul]⟩
  | algebraMap r =>
    exact ⟨r, fun g => by rw [Module.algebraMap_end_apply, map_smul]⟩
  | add x y hx hy ihx ihy =>
    obtain ⟨c₁, h₁⟩ := ihx
    obtain ⟨c₂, h₂⟩ := ihy
    exact ⟨c₁ + c₂, fun g => by rw [LinearMap.add_apply, map_add, h₁, h₂, add_smul]⟩
  | mul x y hx hy ihx ihy =>
    obtain ⟨c₁, h₁⟩ := ihx
    obtain ⟨c₂, h₂⟩ := ihy
    exact ⟨c₁ * c₂, fun g => by rw [Module.End.mul_apply, h₁, h₂, smul_smul]⟩

/- English proof (translation)
Introduce `S hS`. Proceed by induction on `hS using Algebra.adjoin_induction with`. Consider the case `mem x hx`. Take `⟨a₁, b₁, rfl⟩` from `hx`. Conclude with `fun g hg => hP a₁ b₁ _ hg _ (ei_E hd hD a₁ b₁ g)`.

Consider the case `algebraMap r`. Introduce `g hg`. Rewrite using `[Module.algebraMap_end_apply, map_smul]`. Conclude with `P₁.smul_mem r hg`. Consider the case `add x y hx hy ihx ihy`.

Introduce `g hg`. Rewrite using `[LinearMap.add_apply, map_add]`. Conclude with `add_mem (ihx g hg) (ihy g hg)`. Consider the case `mul x y hx hy ihx ihy`. Introduce `g hg`.

Rewrite using `[Module.End.mul_apply]`. Conclude with `ihx _ (ihy g hg)`.
-/
theorem ei_Ealg (P₁ : Submodule ℂ (SInf F (Fin n × Fin d₁)))
    (hP : ∀ (a b : Fin n × Fin d₁ → mixedEmbedding.mixedSpace F), ∀ g ∈ P₁, ∀ g₁ : SInf F (Fin n × Fin d₁),
      ⇑g₁ = dH a b ⇑g → g₁ ∈ P₁) :
    ∀ S ∈ Ealg hd hD, ∀ g, ei F hd g ∈ P₁ → ei F hd (S g) ∈ P₁ := by
  intro S hS
  induction hS using Algebra.adjoin_induction with
  | mem x hx =>
    obtain ⟨a₁, b₁, rfl⟩ := hx
    exact fun g hg => hP a₁ b₁ _ hg _ (ei_E hd hD a₁ b₁ g)
  | algebraMap r =>
    intro g hg
    rw [Module.algebraMap_end_apply, map_smul]
    exact P₁.smul_mem r hg
  | add x y hx hy ihx ihy =>
    intro g hg
    rw [LinearMap.add_apply, map_add]
    exact add_mem (ihx g hg) (ihy g hg)
  | mul x y hx hy ihx ihy =>
    intro g hg
    rw [Module.End.mul_apply]
    exact ihx _ (ihy g hg)

end Plane

/- English proof (translation)
Introduce `F _ _ n d d₁ hd P₁ G hD hP hG`. Set `S : Set (SInf F (Fin n × Fin d))` to `{g | ∃ f₀ ∈ G, ∃ E ∈ Ealg hd hD, ∃ T ∈ Balg hd hD, g = E (T f₀)}`. Use `⟨Submodule.span ℂ S, ?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `f₀ hf₀`. Conclude with `Submodule.subset_span ⟨f₀, hf₀, 1, one_mem _, 1, one_mem _, by simp⟩`.

Introduce `a b f hf f₁ hf₁`. Rewrite using `[Dop_eq_of hD a b f f₁ hf₁]`. It suffices to establish `key : Submodule.span ℂ S ≤ (Submodule.span ℂ S).comap (Dop hD a b) from key hf`. Use `Submodule.span_le.2 ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨f₀, hf₀, E, hE, T, hT, rfl⟩`.

Rewrite using `[SetLike.mem_coe, Submodule.mem_comap]`. Use `set a₁ : Fin n × Fin d₁ → mixedEmbedding.mixedSpace F := fun p => a ((idx hd).symm (Sum.inl p))`. Use `set b₁ : Fin n × Fin d₁ → mixedEmbedding.mixedSpace F := fun p => b ((idx hd).symm (Sum.inl p))`. Establish `hγ : IsPl hd (a - ins0 hd a₁)` using `isPl_sub_ins0 hd a`. Establish `hβ : IsPl hd (b - ins0 hd b₁)` using `isPl_sub_ins0 hd b`.

Establish `hdec : Dop hD a b = Dop hD (ins0 hd a₁) (ins0 hd b₁) + (Dop hD (a - ins0 hd a₁) 0 + Dop hD 0 (b - ins0 hd b₁))`. Rewrite using `[← Dop_add hD (a - ins0 hd a₁) 0 0 (b - ins0 hd b₁), add_zero, zero_add, ← Dop_add, add_sub_cancel, add_sub_cancel]`. Rewrite using `[hdec, LinearMap.add_apply, LinearMap.add_apply]`. Use `add_mem ?_ (add_mem ?_ ?_)` and prove the remaining obligations. Use `Submodule.subset_span ⟨f₀, hf₀, Dop hD (ins0 hd a₁) (ins0 hd b₁) * E, mul_mem (Algebra.subset_adjoin ⟨a₁, b₁, rfl⟩) hE, T, hT, rfl⟩` and prove the remaining obligations.

Take `⟨β', hβ', c, hc⟩` from `(hG f₀ hf₀).2 _ hγ`. Establish `hC0 : Dop hD (a - ins0 hd a₁) 0 f₀ = c • Dop hD 0 β' f₀`. Use extensionality with `x`. Rewrite using `[SchwartzMap.smul_apply, coe_Dop, coe_Dop, smul_eq_mul]`. Conclude with `hc x`.

Establish `hcomm` using `congrArg (fun X : Module.End ℂ _ => X (T f₀)) (C_comm_E hd hD _ hγ E hE)`. Simplify using `only [Module.End.mul_apply] at hcomm`. Rewrite using `[hcomm]`. Establish `hT' : c • (T * Dop hD 0 β') + (Dop hD (a - ins0 hd a₁) 0 * T - T * Dop hD (a - ins0 hd a₁) 0) ∈ Balg hd hD` using `add_mem (Subalgebra.smul_mem _ (mul_mem hT (Algebra.subset_adjoin ⟨β', hβ', rfl⟩)) c) (C_bracket_B hd hD _ T hT)`. Use `Submodule.subset_span ⟨f₀, hf₀, E, hE, _, hT', ?_⟩` and prove the remaining obligations.

Use `congr 1`. Simplify using `only [LinearMap.add_apply, LinearMap.smul_apply, Module.End.mul_apply, LinearMap.sub_apply, hC0, map_smul]`. Normalize the expressions using the abelian group laws. Establish `hcomm` using `congrArg (fun X : Module.End ℂ _ => X (T f₀)) (B_comm_E hd hD _ hβ E hE)`. Simplify using `only [Module.End.mul_apply] at hcomm`.

Rewrite using `[hcomm]`. Conclude with `Submodule.subset_span ⟨f₀, hf₀, E, hE, Dop hD 0 (b - ins0 hd b₁) * T, mul_mem (Algebra.subset_adjoin ⟨_, hβ, rfl⟩) hT, rfl⟩`. Introduce `f hf`. It suffices to establish `key : Submodule.span ℂ S ≤ P₁.comap (ei F hd).toLinearMap from key hf`. Use `Submodule.span_le.2 ?_` and prove the remaining obligations.

Introduce and unpack `_ ⟨f₀, hf₀, E, hE, T, hT, rfl⟩`. Rewrite using `[SetLike.mem_coe, Submodule.mem_comap, ContinuousLinearMap.coe_coe]`. Establish `hcomm` using `congrArg (fun X : Module.End ℂ _ => X f₀) (B_comm_E' hd hD T hT E hE)`. Simplify using `only [Module.End.mul_apply] at hcomm`. Rewrite using `[← hcomm]`.

Take `⟨c, hc⟩` from `ei_Balg hd hD T hT`. Rewrite using `[hc]`. Conclude with `P₁.smul_mem c (ei_Ealg hd hD P₁ hP E hE f₀ (hG f₀ hf₀).1)`.
-/
theorem exists_dH_stable_ei_mem : ∀ (F : Type) [Field F] [NumberField F] (n d d₁ : ℕ) (hd : d = d₁ + 2) (P₁ : Submodule ℂ (SInf F (Fin n × Fin d₁)))
    (G : Set (SInf F (Fin n × Fin d))), HasDH F (Fin n × Fin d) →
    (∀ (a b : Fin n × Fin d₁ → mixedEmbedding.mixedSpace F), ∀ g ∈ P₁, ∀ g₁ : SInf F (Fin n × Fin d₁), ⇑g₁ = dH a b ⇑g → g₁ ∈ P₁) →
    (∀ f₀ ∈ G, ei F hd f₀ ∈ P₁ ∧ ∀ γ : Fin n × Fin d → mixedEmbedding.mixedSpace F, IsPl hd γ →
      ∃ β : Fin n × Fin d → mixedEmbedding.mixedSpace F, IsPl hd β ∧ ∃ c : ℂ, ∀ x, dH γ 0 ⇑f₀ x = c * dH 0 β ⇑f₀ x) →
    ∃ Q : Submodule ℂ (SInf F (Fin n × Fin d)), G ⊆ Q ∧
      (∀ (a b : Fin n × Fin d → mixedEmbedding.mixedSpace F), ∀ f ∈ Q, ∀ f₁ : SInf F (Fin n × Fin d), ⇑f₁ = dH a b ⇑f → f₁ ∈ Q) ∧
      ∀ f ∈ Q, ei F hd f ∈ P₁ := by
  intro F _ _ n d d₁ hd P₁ G hD hP hG
  let S : Set (SInf F (Fin n × Fin d)) :=
    {g | ∃ f₀ ∈ G, ∃ E ∈ Ealg hd hD, ∃ T ∈ Balg hd hD, g = E (T f₀)}
  refine ⟨Submodule.span ℂ S, ?_, ?_, ?_⟩
  · intro f₀ hf₀
    exact Submodule.subset_span ⟨f₀, hf₀, 1, one_mem _, 1, one_mem _, by simp⟩
  · intro a b f hf f₁ hf₁
    rw [Dop_eq_of hD a b f f₁ hf₁]
    suffices key : Submodule.span ℂ S ≤ (Submodule.span ℂ S).comap (Dop hD a b) from key hf
    refine Submodule.span_le.2 ?_
    rintro _ ⟨f₀, hf₀, E, hE, T, hT, rfl⟩
    rw [SetLike.mem_coe, Submodule.mem_comap]
    set a₁ : Fin n × Fin d₁ → mixedEmbedding.mixedSpace F := fun p => a ((idx hd).symm (Sum.inl p))
    set b₁ : Fin n × Fin d₁ → mixedEmbedding.mixedSpace F := fun p => b ((idx hd).symm (Sum.inl p))
    have hγ : IsPl hd (a - ins0 hd a₁) := isPl_sub_ins0 hd a
    have hβ : IsPl hd (b - ins0 hd b₁) := isPl_sub_ins0 hd b
    have hdec : Dop hD a b = Dop hD (ins0 hd a₁) (ins0 hd b₁) +
        (Dop hD (a - ins0 hd a₁) 0 + Dop hD 0 (b - ins0 hd b₁)) := by
      rw [← Dop_add hD (a - ins0 hd a₁) 0 0 (b - ins0 hd b₁), add_zero, zero_add, ← Dop_add,
        add_sub_cancel, add_sub_cancel]
    rw [hdec, LinearMap.add_apply, LinearMap.add_apply]
    refine add_mem ?_ (add_mem ?_ ?_)
    · refine Submodule.subset_span ⟨f₀, hf₀, Dop hD (ins0 hd a₁) (ins0 hd b₁) * E,
        mul_mem (Algebra.subset_adjoin ⟨a₁, b₁, rfl⟩) hE, T, hT, rfl⟩
    · obtain ⟨β', hβ', c, hc⟩ := (hG f₀ hf₀).2 _ hγ
      have hC0 : Dop hD (a - ins0 hd a₁) 0 f₀ = c • Dop hD 0 β' f₀ := by
        ext x
        rw [SchwartzMap.smul_apply, coe_Dop, coe_Dop, smul_eq_mul]
        exact hc x
      have hcomm := congrArg (fun X : Module.End ℂ _ => X (T f₀)) (C_comm_E hd hD _ hγ E hE)
      simp only [Module.End.mul_apply] at hcomm
      rw [hcomm]
      have hT' : c • (T * Dop hD 0 β') + (Dop hD (a - ins0 hd a₁) 0 * T - T * Dop hD (a - ins0 hd a₁) 0) ∈
          Balg hd hD :=
        add_mem (Subalgebra.smul_mem _ (mul_mem hT (Algebra.subset_adjoin ⟨β', hβ', rfl⟩)) c)
          (C_bracket_B hd hD _ T hT)
      refine Submodule.subset_span ⟨f₀, hf₀, E, hE, _, hT', ?_⟩
      congr 1
      simp only [LinearMap.add_apply, LinearMap.smul_apply, Module.End.mul_apply, LinearMap.sub_apply, hC0,
        map_smul]
      abel
    · have hcomm := congrArg (fun X : Module.End ℂ _ => X (T f₀)) (B_comm_E hd hD _ hβ E hE)
      simp only [Module.End.mul_apply] at hcomm
      rw [hcomm]
      exact Submodule.subset_span ⟨f₀, hf₀, E, hE, Dop hD 0 (b - ins0 hd b₁) * T,
        mul_mem (Algebra.subset_adjoin ⟨_, hβ, rfl⟩) hT, rfl⟩
  · intro f hf
    suffices key : Submodule.span ℂ S ≤ P₁.comap (ei F hd).toLinearMap from key hf
    refine Submodule.span_le.2 ?_
    rintro _ ⟨f₀, hf₀, E, hE, T, hT, rfl⟩
    rw [SetLike.mem_coe, Submodule.mem_comap, ContinuousLinearMap.coe_coe]
    have hcomm := congrArg (fun X : Module.End ℂ _ => X f₀) (B_comm_E' hd hD T hT E hE)
    simp only [Module.End.mul_apply] at hcomm
    rw [← hcomm]
    obtain ⟨c, hc⟩ := ei_Balg hd hD T hT
    rw [hc]
    exact P₁.smul_mem c (ei_Ealg hd hD P₁ hP E hE f₀ (hG f₀ hf₀).1)

end GlobalTheory.ThK.PlaneEv.Clo

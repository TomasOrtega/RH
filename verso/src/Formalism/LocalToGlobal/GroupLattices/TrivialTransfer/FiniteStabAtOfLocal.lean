import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.AdelstabL
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Afsplit

noncomputable section

open Matrix TensorProduct NumberField IsDedekindDomain Formalism.UG Formalism.UG.P

namespace Formalism.L2.G.Triv

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

local notation "𝔸" => FiniteAdeleRing (𝓞 F) F
local notation "𝒜" => E ⊗[F] FiniteAdeleRing (𝓞 F) F
local notation "𝒮" => tensInt (F := F) (FiniteAdeleRing (𝓞 F) F) (intOE E) (intAd F)

abbrev SV (E : Type) [Field E] [NumberField E] [Algebra F E] (v : HeightOneSpectrum (𝓞 F)) :
    Subring (E ⊗[F] v.adicCompletion F) :=
  tensInt (F := F) (v.adicCompletion F) (intOE E) (v.adicCompletionIntegers F).toSubring

section Trace

/- English proof (translation)
Proceed by induction on `z using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `tmul e a`. Simplify using `[adelstabT, Algebra.TensorProduct.tmul_mul_tmul, mul_smul_comm]`. Consider the case `add x y hx hy => rw [mul_add, map_add, map_add, hx, hy, mul_add]`.
-/
theorem T_mul (c : 𝔸) (z : 𝒜) : adelstabT F E (((1 : E) ⊗ₜ[F] c) * z) = c * adelstabT F E z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul e a =>
    simp [adelstabT, Algebra.TensorProduct.tmul_mul_tmul, mul_smul_comm]
  | add x y hx hy => rw [mul_add, map_add, map_add, hx, hy, mul_add]

/- English proof (translation)
Introduce `v`. Establish `h1` using `adelstabT_mem (afsplit_IE_int v _ (hz v))`. Rewrite `h1` using `[afsplit_decomp, afsplitEps, Algebra.TensorProduct.one_def, afsplitIE_tmul, T_mul]`. Establish `h2` using `h1 v`. Rewrite `h2` using `[afsplit_mul_apply, afsplitI_self, one_mul]`.

Conclude with `h2`.
-/
theorem T_int (z : 𝒜) (hz : ∀ v, prV (E := E) v z ∈ SV E v) : adelstabT F E z ∈ intAd F := by
  intro v
  have h1 := adelstabT_mem (afsplit_IE_int v _ (hz v))
  rw [afsplit_decomp, afsplitEps, Algebra.TensorProduct.one_def, afsplitIE_tmul, T_mul] at h1
  have h2 := h1 v
  rw [afsplit_mul_apply, afsplitI_self, one_mul] at h2
  exact h2

/- English proof (translation)
Proceed by induction on `z using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `tmul e a`. Establish `he` using `((Algebra.traceForm F E).dualBasis (traceForm_nondegenerate F E) β).sum_repr e`. Simplify using `only [LinearMap.BilinForm.dualBasis_repr_apply, Algebra.traceForm_apply] at he`.

Use `conv_lhs => rw [← he]`. Rewrite using `[TensorProduct.sum_tmul]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[Algebra.TensorProduct.tmul_mul_tmul, one_mul, TensorProduct.smul_tmul, mul_comm e (β i)]`. Simplify using `[adelstabT]`.

Consider the case `add x y hx hy => conv_lhs => rw [hx, hy]`. Rewrite using `[← Finset.sum_add_distrib]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[mul_add, map_add, TensorProduct.tmul_add]`.
-/
theorem expand {ι : Type} [Fintype ι] [DecidableEq ι] (β : Module.Basis ι F E) (z : 𝒜) :
    z = ∑ i, ((Algebra.traceForm F E).dualBasis (traceForm_nondegenerate F E) β i) ⊗ₜ[F]
      adelstabT F E ((β i ⊗ₜ[F] (1 : 𝔸)) * z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul e a =>
    have he := ((Algebra.traceForm F E).dualBasis (traceForm_nondegenerate F E) β).sum_repr e
    simp only [LinearMap.BilinForm.dualBasis_repr_apply, Algebra.traceForm_apply] at he
    conv_lhs => rw [← he]
    rw [TensorProduct.sum_tmul]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul, TensorProduct.smul_tmul, mul_comm e (β i)]
    simp [adelstabT]
  | add x y hx hy =>
    conv_lhs => rw [hx, hy]
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [mul_add, map_add, TensorProduct.tmul_add]

/- English proof (translation)
Set `β₀` to `Module.finBasis F E`. Take `⟨m₁, hm₁, hi₁⟩` from `adelstabL_den (fun i => β₀ i)`. Establish `hu : ∀ _ : Fin (Module.finrank F E), IsUnit ((m₁ : ℤ) : F)` using `fun _ => (Int.cast_ne_zero.2 hm₁).isUnit`. Set `β` to `β₀.isUnitSMul hu`. Establish `hβ : ∀ i, IsIntegral ℤ (β i)`.

Introduce `i`. Establish `: β i = (m₁ : E) * β₀ i`. Rewrite using `[Module.Basis.isUnitSMul_apply, Algebra.smul_def, map_intCast]`. Rewrite using `[this]`. Conclude with `hi₁ i`.

Take `⟨m₂, hm₂, hi₂⟩` from `adelstabL_den (fun i => (Algebra.traceForm F E).dualBasis (traceForm_nondegenerate F E) β i)`. Use `⟨m₂, hm₂, fun z hz => ?_⟩` and prove the remaining obligations. Rewrite using `[expand β z, Finset.mul_sum]`. Use `sum_mem fun i _ => ?_` and prove the remaining obligations. Establish `ht : adelstabT F E ((β i ⊗ₜ[F] (1 : 𝔸)) * z) ∈ intAd F`.

Use `T_int _ fun v => ?_` and prove the remaining obligations. Rewrite using `[map_mul]`. Use `mul_mem ?_ (hz v)` and prove the remaining obligations. Conclude with `Subring.subset_closure (Or.inl ⟨⟨β i, ⟨⟨β i, hβ i⟩, rfl⟩⟩, rfl⟩)`. Establish `h1 : inclE (F` using `F) 𝔸 (m₂ : E) * ((Algebra.traceForm F E).dualBasis (traceForm_nondegenerate F E) β i ⊗ₜ[F] adelstabT F E ((β i ⊗ₜ[F] (1 : 𝔸)) * z)) = algebraMap (𝓞 E) E ⟨_, hi₂ i⟩ ⊗ₜ[F] adelstabT F E ((β i ⊗ₜ[F] (1 : 𝔸)) * z) := by show ((m₂ : E) ⊗ₜ[F] (1 : 𝔸)) * _ = _`.

Rewrite using `[Algebra.TensorProduct.tmul_mul_tmul, one_mul]`. Both sides reduce to the same expression. Rewrite using `[h1]`. Conclude with `levelaf_tmul_mem _ ht`.
-/
theorem exists_den : ∃ d : ℤ, d ≠ 0 ∧ ∀ z : 𝒜, (∀ v, prV (E := E) v z ∈ SV E v) →
    inclE (F := F) 𝔸 (d : E) * z ∈ 𝒮 := by
  classical
  let β₀ := Module.finBasis F E
  obtain ⟨m₁, hm₁, hi₁⟩ := adelstabL_den (fun i => β₀ i)
  have hu : ∀ _ : Fin (Module.finrank F E), IsUnit ((m₁ : ℤ) : F) := fun _ => (Int.cast_ne_zero.2 hm₁).isUnit
  let β := β₀.isUnitSMul hu
  have hβ : ∀ i, IsIntegral ℤ (β i) := by
    intro i
    have : β i = (m₁ : E) * β₀ i := by
      rw [Module.Basis.isUnitSMul_apply, Algebra.smul_def, map_intCast]
    rw [this]; exact hi₁ i
  obtain ⟨m₂, hm₂, hi₂⟩ := adelstabL_den (fun i => (Algebra.traceForm F E).dualBasis (traceForm_nondegenerate F E) β i)
  refine ⟨m₂, hm₂, fun z hz => ?_⟩
  rw [expand β z, Finset.mul_sum]
  refine sum_mem fun i _ => ?_
  have ht : adelstabT F E ((β i ⊗ₜ[F] (1 : 𝔸)) * z) ∈ intAd F := by
    refine T_int _ fun v => ?_
    rw [map_mul]
    refine mul_mem ?_ (hz v)
    exact Subring.subset_closure (Or.inl ⟨⟨β i, ⟨⟨β i, hβ i⟩, rfl⟩⟩, rfl⟩)
  have h1 : inclE (F := F) 𝔸 (m₂ : E) * ((Algebra.traceForm F E).dualBasis (traceForm_nondegenerate F E) β i ⊗ₜ[F]
      adelstabT F E ((β i ⊗ₜ[F] (1 : 𝔸)) * z)) =
      algebraMap (𝓞 E) E ⟨_, hi₂ i⟩ ⊗ₜ[F] adelstabT F E ((β i ⊗ₜ[F] (1 : 𝔸)) * z) := by
    show ((m₂ : E) ⊗ₜ[F] (1 : 𝔸)) * _ = _
    rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul]
    rfl
  rw [h1]
  exact levelaf_tmul_mem _ ht

end Trace

section Lattice

variable {n : Type} [Fintype n] [DecidableEq n]

omit [Fintype n] [DecidableEq n] [NumberField F] [Algebra F E] in
/- English proof (translation)
Use `Fintype.ofFinite n` as an intermediate fact. Take `⟨s, hs⟩ : Λ.FG` from `Module.Finite.iff_fg.mp hfin`. Take `⟨m, hm0, hm⟩` from `adelstabL_den (fun p : s × n => (p.1 : n → E) p.2)`. Use `⟨m, hm0, ?_⟩` and prove the remaining obligations. Introduce `x hx`.

Rewrite `hx` using `[← hs]`. Proceed by induction on `hx using Submodule.span_induction with`. Consider the case `mem x hx => intro k`. Conclude with `hm (⟨x, hx⟩, k)`. Consider the case `zero => intro k`.

Simplify using `[isIntegral_zero]`. Consider the case `add x y _ _ hx hy => intro k`. Simplify `(hx k).add (hy k)` using `[mul_add]`. Consider the case `smul r x _ hx`. Introduce `k`.

Establish `: (m : E) * (r • x) k = algebraMap (𝓞 E) E r * ((m : E) * x k)`. Simplify using `[Algebra.smul_def]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[this]`. Conclude with `(RingOfIntegers.isIntegral_coe r).mul (hx k)`.
-/
theorem den_upper (Λ : Submodule (𝓞 E) (n → E)) [Finite n] (hfin : Module.Finite (𝓞 E) Λ) :
    ∃ m : ℤ, m ≠ 0 ∧ ∀ x ∈ Λ, ∀ k, IsIntegral ℤ ((m : E) * x k) := by
  classical
  have := Fintype.ofFinite n
  obtain ⟨s, hs⟩ : Λ.FG := Module.Finite.iff_fg.mp hfin
  obtain ⟨m, hm0, hm⟩ := adelstabL_den (fun p : s × n => (p.1 : n → E) p.2)
  refine ⟨m, hm0, ?_⟩
  intro x hx
  rw [← hs] at hx
  induction hx using Submodule.span_induction with
  | mem x hx => intro k; exact hm (⟨x, hx⟩, k)
  | zero => intro k; simp [isIntegral_zero]
  | add x y _ _ hx hy => intro k; simpa [mul_add] using (hx k).add (hy k)
  | smul r x _ hx =>
    intro k
    have : (m : E) * (r • x) k = algebraMap (𝓞 E) E r * ((m : E) * x k) := by
      simp [Algebra.smul_def]; ring
    rw [this]
    exact (RingOfIntegers.isIntegral_coe r).mul (hx k)

omit [NumberField F] [Algebra F E] in
/- English proof (translation)
Establish `hk : ∀ k : n, ∃ N : ℕ, ∃ f : Fin N → E, ∃ w : Fin N → Λ, ∑ j, f j • (w j : n → E) = Pi.single k 1`. Introduce `k`. Establish `: (Pi.single k 1 : n → E) ∈ Submodule.span E (Λ : Set (n → E))`. Rewrite using `[hspan]`. Conclude with `Submodule.mem_top`.

Take `⟨N, f, w, h⟩` from `Submodule.mem_span_set'.1 this`. Conclude with `⟨N, f, fun j => ⟨w j, (w j).2⟩, h⟩`. Use `choose N f w hw using hk`. Take `⟨m, hm0, hm⟩` from `adelstabL_den (fun p : Σ k : n, Fin (N k) => f p.1 p.2)`. Use `⟨m, hm0, fun k => ?_⟩` and prove the remaining obligations.

Establish `: (Pi.single k (m : E) : n → E) = ∑ j, (⟨(m : E) * f k j, hm ⟨k, j⟩⟩ : 𝓞 E) • (w k j : n → E)`. Establish `h1 : (Pi.single k (m : E) : n → E) = (m : E) • (Pi.single k 1 : n → E)`. Rewrite using `[← Pi.single_smul', smul_eq_mul, mul_one]`. Rewrite using `[h1, ← hw k, Finset.smul_sum]`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations.

Rewrite using `[← algebraMap_smul E, smul_smul]`. Both sides reduce to the same expression. Rewrite using `[this]`. Conclude with `sum_mem fun j _ => Λ.smul_mem _ (w k j).2`.
-/
theorem den_lower (Λ : Submodule (𝓞 E) (n → E)) (hspan : Submodule.span E (Λ : Set (n → E)) = ⊤) :
    ∃ m : ℤ, m ≠ 0 ∧ ∀ k, (Pi.single k (m : E) : n → E) ∈ Λ := by
  classical
  have hk : ∀ k : n, ∃ N : ℕ, ∃ f : Fin N → E, ∃ w : Fin N → Λ,
      ∑ j, f j • (w j : n → E) = Pi.single k 1 := by
    intro k
    have : (Pi.single k 1 : n → E) ∈ Submodule.span E (Λ : Set (n → E)) := by
      rw [hspan]; exact Submodule.mem_top
    obtain ⟨N, f, w, h⟩ := Submodule.mem_span_set'.1 this
    exact ⟨N, f, fun j => ⟨w j, (w j).2⟩, h⟩
  choose N f w hw using hk
  obtain ⟨m, hm0, hm⟩ := adelstabL_den (fun p : Σ k : n, Fin (N k) => f p.1 p.2)
  refine ⟨m, hm0, fun k => ?_⟩
  have : (Pi.single k (m : E) : n → E) =
      ∑ j, (⟨(m : E) * f k j, hm ⟨k, j⟩⟩ : 𝓞 E) • (w k j : n → E) := by
    have h1 : (Pi.single k (m : E) : n → E) = (m : E) • (Pi.single k 1 : n → E) := by
      rw [← Pi.single_smul', smul_eq_mul, mul_one]
    rw [h1, ← hw k, Finset.smul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← algebraMap_smul E, smul_smul]
    rfl
  rw [this]
  exact sum_mem fun j _ => Λ.smul_mem _ (w k j).2

/- English proof (translation)
Apply `Subring.subset_closure` to reduce the goal to its premises. Use `left`. Conclude with `⟨⟨e, ⟨⟨e, he⟩, rfl⟩⟩, rfl⟩`.
-/
theorem incl_int (v : HeightOneSpectrum (𝓞 F)) (e : E) (he : IsIntegral ℤ e) :
    inclE (F := F) (v.adicCompletion F) e ∈ SV E v := by
  apply Subring.subset_closure
  left
  exact ⟨⟨e, ⟨⟨e, he⟩, rfl⟩⟩, rfl⟩

/- English proof (translation)
Proceed by induction on `hy using Submodule.span_induction with`. Consider the case `mem y hy'`. Take `⟨x, hx, rfl⟩` from `hy'`. Rewrite using `[← map_mul]`. Conclude with `incl_int v _ (hm x hx i)`.

Consider the case `zero => simp`. Consider the case `add a b _ _ ha hb`. Simplify using `only [Pi.add_apply, mul_add]`. Conclude with `add_mem ha hb`. Consider the case `smul s a _ ha`.

Simplify using `only [Pi.smul_apply, Subring.smul_def, smul_eq_mul]`. Rewrite using `[mul_left_comm]`. Conclude with `mul_mem s.2 ha`.
-/
theorem loc_upper (Λ : Submodule (𝓞 E) (n → E)) (m : ℤ) (hm : ∀ x ∈ Λ, ∀ k, IsIntegral ℤ ((m : E) * x k))
    (v : HeightOneSpectrum (𝓞 F)) (y : n → E ⊗[F] v.adicCompletion F)
    (hy : y ∈ latS (F := F) (v.adicCompletion F) (SV E v) Λ) (i : n) :
    inclE (F := F) (v.adicCompletion F) (m : E) * y i ∈ SV E v := by
  induction hy using Submodule.span_induction with
  | mem y hy' =>
    obtain ⟨x, hx, rfl⟩ := hy'
    rw [← map_mul]
    exact incl_int v _ (hm x hx i)
  | zero => simp
  | add a b _ _ ha hb =>
    simp only [Pi.add_apply, mul_add]
    exact add_mem ha hb
  | smul s a _ ha =>
    simp only [Pi.smul_apply, Subring.smul_def, smul_eq_mul]
    rw [mul_left_comm]
    exact mul_mem s.2 ha

/- English proof (translation)
Establish `key : (fun i => inclE (F` using `F) (v.adicCompletion F) (m : E) * y i) = ∑ k, (⟨y k, hy k⟩ : SV E v) • (fun i => inclE (F := F) (v.adicCompletion F) ((Pi.single k (m : E) : n → E) i)) := by`. Use extensionality with `i`. Rewrite using `[Finset.sum_apply, Finset.sum_eq_single i]`. Use `show _ = y i * inclE (F := F) (v.adicCompletion F) ((Pi.single i (m : E) : n → E) i)`. Rewrite using `[Pi.single_eq_same, mul_comm]`.

Introduce `k _ hk show y k * inclE (F := F) (v.adicCompletion F) ((Pi.single k (m : E) : n → E) i) = 0`. Rewrite using `[Pi.single_eq_of_ne (Ne.symm hk), map_zero, mul_zero]`. Introduce `h`. Conclude with `absurd (Finset.mem_univ i) h`. Rewrite using `[key]`.

Conclude with `Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, hm k, rfl⟩)`.
-/
theorem loc_lower (Λ : Submodule (𝓞 E) (n → E)) (m : ℤ) (hm : ∀ k, (Pi.single k (m : E) : n → E) ∈ Λ)
    (v : HeightOneSpectrum (𝓞 F)) (y : n → E ⊗[F] v.adicCompletion F) (hy : ∀ i, y i ∈ SV E v) :
    (fun i => inclE (F := F) (v.adicCompletion F) (m : E) * y i) ∈ latS (F := F) (v.adicCompletion F) (SV E v) Λ := by
  have key : (fun i => inclE (F := F) (v.adicCompletion F) (m : E) * y i) =
      ∑ k, (⟨y k, hy k⟩ : SV E v) • (fun i => inclE (F := F) (v.adicCompletion F) ((Pi.single k (m : E) : n → E) i)) := by
    ext i
    rw [Finset.sum_apply, Finset.sum_eq_single i]
    · show _ = y i * inclE (F := F) (v.adicCompletion F) ((Pi.single i (m : E) : n → E) i)
      rw [Pi.single_eq_same, mul_comm]
    · intro k _ hk
      show y k * inclE (F := F) (v.adicCompletion F) ((Pi.single k (m : E) : n → E) i) = 0
      rw [Pi.single_eq_of_ne (Ne.symm hk), map_zero, mul_zero]
    · intro h
      exact absurd (Finset.mem_univ i) h
  rw [key]
  exact Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, hm k, rfl⟩)

def latLoc (F : Type) [Field F] [NumberField F] [Algebra F E] (Λ : Submodule (𝓞 E) (n → E)) :
    Submodule (tensInt (F := F) (FiniteAdeleRing (𝓞 F) F) (intOE E) (intAd F)) (n → E ⊗[F] FiniteAdeleRing (𝓞 F) F) where
  carrier := {x | ∀ v : HeightOneSpectrum (𝓞 F),
    (fun i => prV (E := E) v (x i)) ∈ latS (F := F) (v.adicCompletion F) (SV E v) Λ}
  add_mem' := by
    intro a b ha hb v
    have : (fun i => prV (E := E) v ((a + b) i)) = (fun i => prV (E := E) v (a i)) + fun i => prV (E := E) v (b i) := by
      ext i; simp
    rw [this]; exact add_mem (ha v) (hb v)
  zero_mem' := by
    intro v
    have : (fun i => prV (E := E) v ((0 : n → E ⊗[F] FiniteAdeleRing (𝓞 F) F) i)) = 0 := by ext i; simp
    rw [this]; exact zero_mem _
  smul_mem' := by
    intro s a ha v
    have : (fun i => prV (E := E) v ((s • a) i)) =
        (⟨prV (E := E) v s, afsplit_prV_int v _ s.2⟩ : SV E v) • fun i => prV (E := E) v (a i) := by
      ext i
      show prV (E := E) v ((s : E ⊗[F] FiniteAdeleRing (𝓞 F) F) * a i) = prV (E := E) v s * prV (E := E) v (a i)
      rw [map_mul]
    rw [this]; exact Submodule.smul_mem _ _ (ha v)

/- English proof (translation)
Simplify using `only [levelafC, inclE, map_intCast]`. Rewrite using `[← Algebra.TensorProduct.includeRight_apply, map_intCast]`.
-/
theorem levelafC_int (m : ℤ) : levelafC E (m : 𝓞 F) = inclE (F := F) 𝔸 (m : E) := by
  simp only [levelafC, inclE, map_intCast]
  rw [← Algebra.TensorProduct.includeRight_apply, map_intCast]

/- English proof (translation)
Take `⟨m₁, hm₁, h₁⟩` from `den_lower Λ hspan`. Take `⟨m₂, hm₂, h₂⟩` from `den_upper Λ hfin`. Take `⟨d, hd, h₃⟩` from `exists_den (F := F) (E := E)`. Use `adelstab_core σ J hτ hH hdet hdef (latLoc F Λ) U ?_ (m₁ : 𝓞 F) ((d * m₂ : ℤ) : 𝓞 F) (Int.cast_ne_zero.2 hm₁) (Int.cast_ne_zero.2 (mul_ne_zero hd hm₂)) ?_ ?_ g` and prove the remaining obligations. Introduce `x hx y`.

Establish `key : ∀ v : HeightOneSpectrum (𝓞 F), (fun i => prV (E` using `E) v (((x : Matrix n n 𝒜) *ᵥ y) i)) = ((bc (prV (E := E) v) x : GL n (E ⊗[F] v.adicCompletion F)) : Matrix n n (E ⊗[F] v.adicCompletion F)) *ᵥ fun i => prV (E := E) v (y i) := by`. Introduce `v`. Use extensionality with `i`. Conclude with `RingHom.map_mulVec (prV (E := E) v) (x : Matrix n n 𝒜) y i`. Prove the components needed by the constructor for the conclusion.

Introduce `hy v`. Rewrite using `[key v]`. Conclude with `(hU x hx v _).1 (hy v)`. Introduce `hy v`. Use `hy v` as an intermediate fact.

Rewrite `this` using `[key v]`. Conclude with `(hU x hx v _).2 this`. Introduce `w hw v`. Establish `: (fun i => prV (E` using `E) v (levelafC E (m₁ : 𝓞 F) * w i)) = fun i => inclE (F := F) (v.adicCompletion F) (m₁ : E) * prV (E := E) v (w i) := by`. Use extensionality with `i`.

Rewrite using `[levelafC_int, map_mul, afsplit_prV_inclE]`. Rewrite using `[this]`. Conclude with `loc_lower Λ m₁ h₁ v _ fun i => afsplit_prV_int v _ (hw i)`. Introduce `w hw i`. Rewrite using `[levelafC_int, Int.cast_mul, map_mul, mul_assoc]`.

Use `h₃ _ fun v => ?_` and prove the remaining obligations. Rewrite using `[map_mul, afsplit_prV_inclE]`. Conclude with `loc_upper Λ m₂ h₂ v _ (hw v) i`.
-/
theorem finite_stabAt_of_local (σ : E →ₐ[F] E) (J : Matrix n n E)
    (hτ : ∀ τ : E →+* ℂ, τ.comp (σ : E →+* E) = (starRingEnd ℂ).comp τ)
    (hH : IsHerm (σ : E →+* E) J) (hdet : IsUnit J.det) (hdef : IsTotDef σ J)
    (Λ : Submodule (𝓞 E) (n → E)) (hfin : Module.Finite (𝓞 E) Λ) (hspan : Submodule.span E (Λ : Set (n → E)) = ⊤)
    (U : Subgroup (GL n 𝒜))
    (hU : ∀ x ∈ U, ∀ v : HeightOneSpectrum (𝓞 F),
      bc (prV (E := E) v) x ∈ stabGL (latS (F := F) (v.adicCompletion F) (SV E v) Λ))
    (g : UPts σ J 𝔸) :
    Finite (stabAt ((ratPts σ J 𝔸).subgroupOf (UPts σ J 𝔸)) (U.subgroupOf (UPts σ J 𝔸)) g) := by
  obtain ⟨m₁, hm₁, h₁⟩ := den_lower Λ hspan
  obtain ⟨m₂, hm₂, h₂⟩ := den_upper Λ hfin
  obtain ⟨d, hd, h₃⟩ := exists_den (F := F) (E := E)
  refine adelstab_core σ J hτ hH hdet hdef (latLoc F Λ) U ?_ (m₁ : 𝓞 F) ((d * m₂ : ℤ) : 𝓞 F) (Int.cast_ne_zero.2 hm₁)
    (Int.cast_ne_zero.2 (mul_ne_zero hd hm₂)) ?_ ?_ g
  · intro x hx y
    have key : ∀ v : HeightOneSpectrum (𝓞 F), (fun i => prV (E := E) v (((x : Matrix n n 𝒜) *ᵥ y) i)) =
        ((bc (prV (E := E) v) x : GL n (E ⊗[F] v.adicCompletion F)) : Matrix n n (E ⊗[F] v.adicCompletion F)) *ᵥ
          fun i => prV (E := E) v (y i) := by
      intro v
      ext i
      exact RingHom.map_mulVec (prV (E := E) v) (x : Matrix n n 𝒜) y i
    constructor
    · intro hy v
      rw [key v]
      exact (hU x hx v _).1 (hy v)
    · intro hy v
      have := hy v
      rw [key v] at this
      exact (hU x hx v _).2 this
  · intro w hw v
    have : (fun i => prV (E := E) v (levelafC E (m₁ : 𝓞 F) * w i)) =
        fun i => inclE (F := F) (v.adicCompletion F) (m₁ : E) * prV (E := E) v (w i) := by
      ext i
      rw [levelafC_int, map_mul, afsplit_prV_inclE]
    rw [this]
    exact loc_lower Λ m₁ h₁ v _ fun i => afsplit_prV_int v _ (hw i)
  · intro w hw i
    rw [levelafC_int, Int.cast_mul, map_mul, mul_assoc]
    refine h₃ _ fun v => ?_
    rw [map_mul, afsplit_prV_inclE]
    exact loc_upper Λ m₂ h₂ v _ (hw v) i

end Lattice

end Formalism.L2.G.Triv

end

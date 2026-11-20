import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RankPosOfLeaves

noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.DiscSpec GlobalTheory.CompanionTheory.CTFin PositivityTheory.Rg.Rs
open PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.SpectralAccumulation

namespace GlobalTheory.CompanionTheory.EGlue.OneStepProof

open GlobalTheory.CompanionTheory.EGlue

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {N : ℕ}

/- English proof (translation)
Introduce `φ hφ`. Use `(Submodule.mem_sInf).2 ?_` and prove the remaining obligations. Introduce and unpack `U ⟨hS, -⟩`. Conclude with `hS hφ`.
-/
theorem subset_hull (S : Set (Sm E N)) : S ⊆ (hull S : Submodule ℂ (Sm E N)) := by
  intro φ hφ
  refine (Submodule.mem_sInf).2 ?_
  rintro U ⟨hS, -⟩
  exact hS hφ

/- English proof (translation)
The claim follows from `sInf_le ⟨hS, hU⟩`.
-/
theorem hull_le {S : Set (Sm E N)} {U : Submodule ℂ (Sm E N)} (hS : S ⊆ U) (hU : IsStable U) : hull S ≤ U :=
  sInf_le ⟨hS, hU⟩

/- English proof (translation)
Introduce `h`. Establish `h1 : φ ∈ (hull S : Submodule ℂ (Sm E N))` using `subset_hull S hφ`. Rewrite `h1` using `[h]`. Conclude with `h0 ((Submodule.mem_bot ℂ).1 h1)`.
-/
theorem hull_ne_bot {S : Set (Sm E N)} {φ : Sm E N} (hφ : φ ∈ S) (h0 : φ ≠ 0) : hull S ≠ ⊥ := by
  intro h
  have h1 : φ ∈ (hull S : Submodule ℂ (Sm E N)) := subset_hull S hφ
  rw [h] at h1
  exact h0 ((Submodule.mem_bot ℂ).1 h1)

/- English proof (translation)
Assume the negation of the conclusion as `hcon`. Establish `hz : ∀ φ ∈ S, T φ = 0`. Introduce `φ hφ`. Assume the negation of the conclusion as `h`. Conclude with `hcon ⟨φ, hφ, h⟩`.

Establish `hK : IsStable (hull S ⊓ LinearMap.ker T)`. Introduce `o χ hχ`. Use `Submodule.mem_inf.2 ⟨hst o χ hχ.1, ?_⟩` and prove the remaining obligations. Establish `h0 : T χ = 0` using `LinearMap.mem_ker.1 hχ.2`. Rewrite using `[LinearMap.mem_ker, he o χ hχ.1, h0, map_zero]`.

Establish `hS : S ⊆ (hull S ⊓ LinearMap.ker T : Submodule ℂ (Sm E N))` using `fun φ hφ => Submodule.mem_inf.2 ⟨subset_hull S hφ, LinearMap.mem_ker.2 (hz φ hφ)⟩`. Conclude with `hT (LinearMap.mem_ker.1 (Submodule.mem_inf.1 (hull_le hS hK hψ)).2)`.
-/
theorem exists_ne_of_hull {S : Set (Sm E N)} (hst : IsStable (hull S)) (T : Sm E N →ₗ[ℂ] Sm E N)
    (he : ∀ o, ∀ χ ∈ hull S, T (act o χ) = act o (T χ)) {ψ : Sm E N} (hψ : ψ ∈ hull S) (hT : T ψ ≠ 0) :
    ∃ φ ∈ S, T φ ≠ 0 := by
  by_contra hcon
  have hz : ∀ φ ∈ S, T φ = 0 := by
    intro φ hφ
    by_contra h
    exact hcon ⟨φ, hφ, h⟩
  have hK : IsStable (hull S ⊓ LinearMap.ker T) := by
    intro o χ hχ
    refine Submodule.mem_inf.2 ⟨hst o χ hχ.1, ?_⟩
    have h0 : T χ = 0 := LinearMap.mem_ker.1 hχ.2
    rw [LinearMap.mem_ker, he o χ hχ.1, h0, map_zero]
  have hS : S ⊆ (hull S ⊓ LinearMap.ker T : Submodule ℂ (Sm E N)) := fun φ hφ =>
    Submodule.mem_inf.2 ⟨subset_hull S hφ, LinearMap.mem_ker.2 (hz φ hφ)⟩
  exact hT (LinearMap.mem_ker.1 (Submodule.mem_inf.1 (hull_le hS hK hψ)).2)

/- English proof (translation)
Introduce and unpack `rfl`. Conclude with `h rfl`.
-/
theorem sm_ne_zero {φ : Sm E N} {x : GA E N} (h : φ.1 x ≠ 0) : φ ≠ 0 := by
  rintro rfl
  exact h rfl

/- English proof (translation)
Introduce `hSl hRe hFD hST hP₁ hP₂ hHG hCE`. Introduce `E _ _ _ a b ι _ K₁ K₂ W₁ W₂ Θ₁ Θ₂ Ω₁ Ω₂ f m₁ m₂ hW₁ hW₂ hF₁ hF₂ hf hT hs₁ hs₂ hA₁ hA₂ hN₁ hN₂ hC₁ hC₂ hI₁ hI₂ hD₁ hD₂ hP`. Take `⟨fd₁, fd₂⟩` from `hFD E a b ι _ _ f hP`. Establish `ty₁ : ∀ φ ∈ slices₁ f, TypeB K₁ W₁ φ`. Introduce and unpack `φ ⟨i, m, h⟩`.

Conclude with `(hST E a b K₁ K₂ W₁ W₂ (f i) (hT i)).1 φ m h`. Establish `ty₂ : ∀ φ ∈ slices₂ f, TypeB K₂ W₂ φ`. Introduce and unpack `φ ⟨i, m, h⟩`. Conclude with `(hST E a b K₁ K₂ W₁ W₂ (f i) (hT i)).2 φ m h`. Take `⟨st₁, fg₁⟩` from `hHG E a K₁ W₁ _ ty₁ fd₁`.

Take `⟨st₂, fg₂⟩` from `hHG E b K₂ W₂ _ ty₂ fd₂`. Establish `hU₁ : hull (slices₁ f) ≠ ⊥`. Take `⟨i, hi⟩` from `Function.ne_iff.1 hf`. Take `⟨x, hx⟩` from `Function.ne_iff.1 hi`. Take `⟨φ, hφ⟩` from `hs₁ i x.2`.

Use `hull_ne_bot (φ := φ) ⟨i, x.2, hφ⟩ (sm_ne_zero (x := x.1) ?_)` and prove the remaining obligations. Rewrite using `[hφ]`. Conclude with `hx`. Take `⟨t₁, T₁, r₁, g₁, l₁, e₁, i₁, ψ, hψ, hTψ⟩` from `hF₁ _ st₁ hA₁ fg₁ hN₁ hC₁ (fun τ => ⟨m₁ τ, hI₁ τ, hD₁ τ⟩) hU₁`. Take `⟨φ, ⟨i₀, y, hφ⟩, hTφ⟩` from `exists_ne_of_hull st₁ T₁ e₁ hψ hTψ`.

Take `⟨G₁ne, G₁p, G₁t, G₁h⟩` from `hP₁ E a b ι K₁ K₂ W₁ W₂ _ t₁.space _ T₁ f hW₁ hW₂ st₁ e₁ i₁ hP hT ⟨i₀, y, φ, hφ, hTφ⟩`. Establish `hsl : ∀ i m, sl₂ (ap₁ T₁ (f i)) m ∈ hull (slices₂ f) ∧ (sl₂ (ap₁ T₁ (f i)) m).1 = fun x => ap₁ T₁ (f i) (m, x)` using `fun i m => (hSl E a b _ _ _ (G₁p i)).2 m`. Establish `hss : slices₂ (fun i => ap₁ T₁ (f i)) ⊆ (hull (slices₂ f) : Submodule ℂ (Sm E b))`. Introduce and unpack `χ ⟨i, m, h⟩`. Establish `hχ : χ = sl₂ (ap₁ T₁ (f i)) m` using `Subtype.ext (h.trans (hsl i m).2.symm)`.

Rewrite using `[hχ]`. Conclude with `(hsl i m).1`. Establish `hle : hull (slices₂ fun i => ap₁ T₁ (f i)) ≤ hull (slices₂ f)` using `hull_le hss st₂`. Establish `ty₂' : ∀ χ ∈ slices₂ (fun i => ap₁ T₁ (f i)), TypeB K₂ W₂ χ`. Introduce and unpack `χ ⟨i, m, h⟩`.

Conclude with `(hST E a b K₁ K₂ W₁ W₂ _ (G₁t i)).2 χ m h`. Take `⟨st₂', fg₂'⟩` from `hHG E b K₂ W₂ _ ty₂' (hFD E a b ι _ _ _ G₁p).2`. Establish `G₁p' : ∀ i, ap₁ T₁ (f i) ∈ pairSpace t₁.space (hull (slices₂ fun i => ap₁ T₁ (f i)))` using `fun i => hRe E a b _ _ _ _ (G₁p i) fun m χ h => subset_hull _ ⟨i, m, h⟩`. Establish `hU₂ : hull (slices₂ fun i => ap₁ T₁ (f i)) ≠ ⊥`. Take `⟨i, hi⟩` from `Function.ne_iff.1 G₁ne`.

Take `⟨x, hx⟩` from `Function.ne_iff.1 hi`. Use `hull_ne_bot (φ := sl₂ (ap₁ T₁ (f i)) x.1) ⟨i, x.1, (hsl i x.1).2⟩ (sm_ne_zero (x := x.2) ?_)` and prove the remaining obligations. Rewrite using `[(hsl i x.1).2]`. Conclude with `hx`. Take `⟨t₂, T₂, r₂, g₂, l₂, e₂, i₂, ψ', hψ', hTψ'⟩` from `hF₂ _ st₂' (fun χ hχ => hA₂ χ (hle hχ)) fg₂' (fun χ hχ => hN₂ χ (hle hχ)) (by`.

Take `⟨z, hz, h⟩` from `hC₂`. Conclude with `⟨z, hz, fun χ hχ => h χ (hle hχ)⟩)`. Use the proof step `(fun τ => ⟨m₂ τ, ⟨(hI₂ τ).1, fun u χ hχ => (hI₂ τ).2 u χ (hle hχ)⟩, hD₂ τ⟩) hU₂`. Take `⟨χ, ⟨i₃, y₃, hχ⟩, hTχ⟩` from `exists_ne_of_hull st₂' T₂ e₂ hψ' hTψ'`. Take `⟨Gne, Gp, Gt, Gh⟩` from `hP₂ E a b ι K₁ K₂ W₁ W₂ _ _ t₂.space T₂ (fun i => ap₁ T₁ (f i)) hW₁ hW₂ st₂' e₂ i₂ G₁p' G₁t ⟨i₃, y₃, χ, hχ, hTχ⟩`.

Conclude with `⟨t₁, t₂, fun i => ap₂ T₂ (ap₁ T₁ (f i)), T₁ ψ, T₂ ψ', r₁, r₂, g₁, g₂, l₁, l₂, Gne, Gp, Gt, fun h c e => Gh h c (G₁h h c e), i₁ ψ hψ, hTψ, hCE E a _ T₁ ψ m₁ st₁ e₁ hψ (fun τ u => (hI₁ τ).2 u ψ hψ), i₂ ψ' hψ', hTψ', hCE E b _ T₂ ψ' m₂ st₂' e₂ hψ' (fun τ u => (hI₂ τ).2 u ψ' (hle hψ' …`.
-/
theorem oneStep_of_parts : PairSlices → PairRestrict → PairFD → SliceType → PairStep₁ → PairStep₂ → HullGen → CapEquiv →
    OneStep := by
  intro hSl hRe hFD hST hP₁ hP₂ hHG hCE
  intro E _ _ _ a b ι _ K₁ K₂ W₁ W₂ Θ₁ Θ₂ Ω₁ Ω₂ f m₁ m₂ hW₁ hW₂ hF₁ hF₂ hf hT hs₁ hs₂ hA₁ hA₂ hN₁ hN₂ hC₁ hC₂ hI₁ hI₂
    hD₁ hD₂ hP
  obtain ⟨fd₁, fd₂⟩ := hFD E a b ι _ _ f hP
  have ty₁ : ∀ φ ∈ slices₁ f, TypeB K₁ W₁ φ := by
    rintro φ ⟨i, m, h⟩
    exact (hST E a b K₁ K₂ W₁ W₂ (f i) (hT i)).1 φ m h
  have ty₂ : ∀ φ ∈ slices₂ f, TypeB K₂ W₂ φ := by
    rintro φ ⟨i, m, h⟩
    exact (hST E a b K₁ K₂ W₁ W₂ (f i) (hT i)).2 φ m h
  obtain ⟨st₁, fg₁⟩ := hHG E a K₁ W₁ _ ty₁ fd₁
  obtain ⟨st₂, fg₂⟩ := hHG E b K₂ W₂ _ ty₂ fd₂

  have hU₁ : hull (slices₁ f) ≠ ⊥ := by
    obtain ⟨i, hi⟩ := Function.ne_iff.1 hf
    obtain ⟨x, hx⟩ := Function.ne_iff.1 hi
    obtain ⟨φ, hφ⟩ := hs₁ i x.2
    refine hull_ne_bot (φ := φ) ⟨i, x.2, hφ⟩ (sm_ne_zero (x := x.1) ?_)
    rw [hφ]
    exact hx
  obtain ⟨t₁, T₁, r₁, g₁, l₁, e₁, i₁, ψ, hψ, hTψ⟩ :=
    hF₁ _ st₁ hA₁ fg₁ hN₁ hC₁ (fun τ => ⟨m₁ τ, hI₁ τ, hD₁ τ⟩) hU₁
  obtain ⟨φ, ⟨i₀, y, hφ⟩, hTφ⟩ := exists_ne_of_hull st₁ T₁ e₁ hψ hTψ
  obtain ⟨G₁ne, G₁p, G₁t, G₁h⟩ := hP₁ E a b ι K₁ K₂ W₁ W₂ _ t₁.space _ T₁ f hW₁ hW₂ st₁ e₁ i₁ hP hT
    ⟨i₀, y, φ, hφ, hTφ⟩

  have hsl : ∀ i m, sl₂ (ap₁ T₁ (f i)) m ∈ hull (slices₂ f) ∧
      (sl₂ (ap₁ T₁ (f i)) m).1 = fun x => ap₁ T₁ (f i) (m, x) :=
    fun i m => (hSl E a b _ _ _ (G₁p i)).2 m
  have hss : slices₂ (fun i => ap₁ T₁ (f i)) ⊆ (hull (slices₂ f) : Submodule ℂ (Sm E b)) := by
    rintro χ ⟨i, m, h⟩
    have hχ : χ = sl₂ (ap₁ T₁ (f i)) m := Subtype.ext (h.trans (hsl i m).2.symm)
    rw [hχ]
    exact (hsl i m).1
  have hle : hull (slices₂ fun i => ap₁ T₁ (f i)) ≤ hull (slices₂ f) := hull_le hss st₂
  have ty₂' : ∀ χ ∈ slices₂ (fun i => ap₁ T₁ (f i)), TypeB K₂ W₂ χ := by
    rintro χ ⟨i, m, h⟩
    exact (hST E a b K₁ K₂ W₁ W₂ _ (G₁t i)).2 χ m h
  obtain ⟨st₂', fg₂'⟩ := hHG E b K₂ W₂ _ ty₂' (hFD E a b ι _ _ _ G₁p).2
  have G₁p' : ∀ i, ap₁ T₁ (f i) ∈ pairSpace t₁.space (hull (slices₂ fun i => ap₁ T₁ (f i))) := fun i =>
    hRe E a b _ _ _ _ (G₁p i) fun m χ h => subset_hull _ ⟨i, m, h⟩
  have hU₂ : hull (slices₂ fun i => ap₁ T₁ (f i)) ≠ ⊥ := by
    obtain ⟨i, hi⟩ := Function.ne_iff.1 G₁ne
    obtain ⟨x, hx⟩ := Function.ne_iff.1 hi
    refine hull_ne_bot (φ := sl₂ (ap₁ T₁ (f i)) x.1) ⟨i, x.1, (hsl i x.1).2⟩ (sm_ne_zero (x := x.2) ?_)
    rw [(hsl i x.1).2]
    exact hx

  obtain ⟨t₂, T₂, r₂, g₂, l₂, e₂, i₂, ψ', hψ', hTψ'⟩ :=
    hF₂ _ st₂' (fun χ hχ => hA₂ χ (hle hχ)) fg₂' (fun χ hχ => hN₂ χ (hle hχ))
      (by
        obtain ⟨z, hz, h⟩ := hC₂
        exact ⟨z, hz, fun χ hχ => h χ (hle hχ)⟩)
      (fun τ => ⟨m₂ τ, ⟨(hI₂ τ).1, fun u χ hχ => (hI₂ τ).2 u χ (hle hχ)⟩, hD₂ τ⟩) hU₂
  obtain ⟨χ, ⟨i₃, y₃, hχ⟩, hTχ⟩ := exists_ne_of_hull st₂' T₂ e₂ hψ' hTψ'
  obtain ⟨Gne, Gp, Gt, Gh⟩ := hP₂ E a b ι K₁ K₂ W₁ W₂ _ _ t₂.space T₂ (fun i => ap₁ T₁ (f i)) hW₁ hW₂ st₂' e₂ i₂ G₁p' G₁t
    ⟨i₃, y₃, χ, hχ, hTχ⟩
  exact ⟨t₁, t₂, fun i => ap₂ T₂ (ap₁ T₁ (f i)), T₁ ψ, T₂ ψ', r₁, r₂, g₁, g₂, l₁, l₂, Gne, Gp, Gt,
    fun h c e => Gh h c (G₁h h c e), i₁ ψ hψ, hTψ,
    hCE E a _ T₁ ψ m₁ st₁ e₁ hψ (fun τ u => (hI₁ τ).2 u ψ hψ),
    i₂ ψ' hψ', hTψ',
    hCE E b _ T₂ ψ' m₂ st₂' e₂ hψ' (fun τ u => (hI₂ τ).2 u ψ' (hle hψ'))⟩

end GlobalTheory.CompanionTheory.EGlue.OneStepProof

end

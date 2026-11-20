import Formalism.SharpRestriction.LevelLetterCocycles.FrameInvPoly
import Formalism.SharpRestriction.LevelLetterCocycles.LocalizationQuotientSeparatedDvd

noncomputable section

open Classical TensorProduct

namespace Formalism.MainNotions.UnusedSlot80.LevC

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.WachCoordinates.Br

section Gen

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR}
    {LL : Type} [Field LL] [Algebra Qp LL]
    {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]

/- English proof (translation)
Assemble the required witnesses or components as `⟨x ⊗ₜ[Qp] (⟨y, hy⟩ : ↥((PD.Fil a).restrictScalars Qp)), by simp [TensorProduct.AlgebraTensorModule.map_tmul]⟩`.
-/
theorem tmul_mem_filV (x : V) {y : BdR} {a : ℤ} (hy : y ∈ PD.Fil a) :
    x ⊗ₜ[Qp] y ∈ FilV PD (LL := LL) (V := V) a :=
  ⟨x ⊗ₜ[Qp] (⟨y, hy⟩ : ↥((PD.Fil a).restrictScalars Qp)), by
    simp [TensorProduct.AlgebraTensorModule.map_tmul]⟩

/- English proof (translation)
Proceed by induction on `z using TensorProduct.induction_on with`. Consider the case `zero => exact ⟨0, Submodule.zero_mem _⟩`. Consider the case `tmul x y`. Take `⟨a, ha⟩` from `PD.Fil_exh y`. Conclude with `⟨a, tmul_mem_filV x ha⟩`.

Consider the case `add x y hx hy`. Take `⟨a, ha⟩` from `hx`. Take `⟨b, hb⟩` from `hy`. Conclude with `⟨min a b, Submodule.add_mem _ (Formalism.MainNotions.UnusedSlot80.LevR.filV_anti (min_le_left a b) ha) (Formalism.MainNotions.UnusedSlot80.LevR.filV_anti (min_le_right a b) hb)⟩`.
-/
theorem filV_exh (z : V ⊗[Qp] BdR) : ∃ a, z ∈ FilV PD (LL := LL) (V := V) a := by
  induction z using TensorProduct.induction_on with
  | zero => exact ⟨0, Submodule.zero_mem _⟩
  | tmul x y =>
    obtain ⟨a, ha⟩ := PD.Fil_exh y
    exact ⟨a, tmul_mem_filV x ha⟩
  | add x y hx hy =>
    obtain ⟨a, ha⟩ := hx
    obtain ⟨b, hb⟩ := hy
    exact ⟨min a b, Submodule.add_mem _ (Formalism.MainNotions.UnusedSlot80.LevR.filV_anti (min_le_left a b) ha)
      (Formalism.MainNotions.UnusedSlot80.LevR.filV_anti (min_le_right a b) hb)⟩

/- English proof (translation)
Establish `hfree : Module.Free Qp V` using `Module.Free.of_divisionRing Qp V`. Set `𝔟` to `Module.Free.chooseBasis Qp V`. Set `E` to `TensorProduct.equivFinsuppOfBasisLeft (N := BdR) 𝔟`. Establish `hcoord : ∀ a, ∀ w ∈ FilV PD (LL` using `LL) (V := V) a, ∀ i, E w i ∈ PD.Fil a := by`. Introduce `a w hw i`.

Take `⟨u, rfl⟩` from `hw`. Proceed by induction on `u using TensorProduct.induction_on with`. Consider the case `zero => simp [(PD.Fil a).zero_mem]`. Consider the case `tmul x y`. Simplify using `only [TensorProduct.AlgebraTensorModule.map_tmul, LinearMap.id_apply, Submodule.coe_subtype]`.

Rewrite using `[TensorProduct.equivFinsuppOfBasisLeft_apply_tmul]`. Simplify using `only [Finsupp.mapRange_apply]`. Establish `: (𝔟.repr x i) • (y : BdR) = algebraMap Qp K (𝔟.repr x i) • (y : BdR)`. Rewrite using `[algebraMap_smul]`. Rewrite using `[this]`.

Conclude with `(PD.Fil a).smul_mem _ y.2`. Consider the case `add u₁ u₂ h₁ h₂`. Rewrite using `[map_add, map_add, Finsupp.add_apply]`. Conclude with `(PD.Fil a).add_mem h₁ h₂`. Establish `hE : E z = 0`.

Use extensionality with `i`. Conclude with `PD.Fil_sep _ fun a => hcoord a z (h a) i`. Conclude with `E.injective (by rw [hE, map_zero])`.
-/
theorem filV_sep (z : V ⊗[Qp] BdR) (h : ∀ a, z ∈ FilV PD (LL := LL) (V := V) a) : z = 0 := by
  have hfree : Module.Free Qp V := Module.Free.of_divisionRing Qp V
  let 𝔟 := Module.Free.chooseBasis Qp V
  let E := TensorProduct.equivFinsuppOfBasisLeft (N := BdR) 𝔟
  have hcoord : ∀ a, ∀ w ∈ FilV PD (LL := LL) (V := V) a, ∀ i, E w i ∈ PD.Fil a := by
    intro a w hw i
    obtain ⟨u, rfl⟩ := hw
    induction u using TensorProduct.induction_on with
    | zero => simp [(PD.Fil a).zero_mem]
    | tmul x y =>
      simp only [TensorProduct.AlgebraTensorModule.map_tmul, LinearMap.id_apply, Submodule.coe_subtype]
      rw [TensorProduct.equivFinsuppOfBasisLeft_apply_tmul]
      simp only [Finsupp.mapRange_apply]
      have : (𝔟.repr x i) • (y : BdR) = algebraMap Qp K (𝔟.repr x i) • (y : BdR) := by
        rw [algebraMap_smul]
      rw [this]
      exact (PD.Fil a).smul_mem _ y.2
    | add u₁ u₂ h₁ h₂ =>
      rw [map_add, map_add, Finsupp.add_apply]
      exact (PD.Fil a).add_mem h₁ h₂
  have hE : E z = 0 := by
    ext i
    exact PD.Fil_sep _ fun a => hcoord a z (h a) i
  exact E.injective (by rw [hE, map_zero])

end Gen

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR}
    {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL] [CommRing O] [Algebra O LL]
    {v : AddValuation LL (WithTop ℚ)} {n : ℕ} (W : LocWach PD LL O v n)

open Formalism.MainNotions.ArcLiftingSetup

/- English proof (translation)
Establish `hι : ιV PD (LL` using `LL) (V := T.V) x ∈ DdRE PD T.ρ τ := Formalism.MainNotions.UnusedSlot80.LevR.ιDi_le W T c τ hover hsurj ⟨x, hxD, rfl⟩`. Establish `h1 : ιV PD (LL` using `LL) (V := T.V) x ∈ FildR PD T.ρ τ a := ⟨hι, hx.2⟩`. Establish `heq : FildR PD T.ρ τ (a + 1) = FildR PD T.ρ τ a`. Assume the negation of the conclusion as `hne`. Conclude with `hna hne`.

Rewrite `h1` using `[← heq]`. Conclude with `⟨hx.1, h1.2⟩`.
-/
theorem fil_step (T : LocLat G Qp LL O) (c : ZMod n) (τ : K →ₐ[Qp] LL)
    (hover : ∀ x : K₀, τ (algebraMap K₀ K x) = W.emb c x) (hsurj : Function.Surjective (algebraMap K₀ K))
    (a : ℤ) (hna : ¬ IsJumpV PD T.ρ τ a) {x : T.V ⊗[Qp] B} (hxD : x ∈ DcrisL PD T.ρ (W.emb c))
    (hx : x ∈ FilCris PD T.ρ a) : x ∈ FilCris PD T.ρ (a + 1) := by
  have hι : ιV PD (LL := LL) (V := T.V) x ∈ DdRE PD T.ρ τ :=
    Formalism.MainNotions.UnusedSlot80.LevR.ιDi_le W T c τ hover hsurj ⟨x, hxD, rfl⟩
  have h1 : ιV PD (LL := LL) (V := T.V) x ∈ FildR PD T.ρ τ a := ⟨hι, hx.2⟩
  have heq : FildR PD T.ρ τ (a + 1) = FildR PD T.ρ τ a := by
    by_contra hne; exact hna hne
  rw [← heq] at h1
  exact ⟨hx.1, h1.2⟩

/- English proof (translation)
Take `⟨u₀, hu₀⟩` from `filV_exh (PD := PD) (LL := LL) (ιV PD (LL := LL) (V := T.V) x)`. Establish `hx0 : x ∈ FilCris PD T.ρ u₀` using `⟨hxD.1, hu₀⟩`. Distinguish the cases in `hle : -(H : ℤ) ≤ u₀`. Conclude with `Formalism.MainNotions.UnusedSlot80.LevR.filCris_anti T.ρ hle hx0`. Establish `key : ∀ k : ℕ, u₀ + k ≤ -(H : ℤ) → x ∈ FilCris PD T.ρ (u₀ + k)`.

Introduce `k`. Proceed by induction on `k with`. Consider the case `zero => intro _`. Simplify using `using hx0`. Consider the case `succ k ih`.

Introduce `hk`. Use `fil_step W T c τ hover hsurj (u₀ + k) (fun hj => by have := hJ _ hj; push_cast at hk; omega) hxD (ih (by push_cast at hk; omega))` as an intermediate fact. Use `push_cast`. Rewrite using `[← add_assoc]` and apply the resulting hypothesis. Use `key (-(H : ℤ) - u₀).toNat (by omega)` as an intermediate fact.

Rewrite `this` using `[show u₀ + ((-(H : ℤ) - u₀).toNat : ℤ) = -(H : ℤ) by omega]`. Then use the resulting hypothesis.
-/
theorem fil_low (T : LocLat G Qp LL O) (c : ZMod n) (τ : K →ₐ[Qp] LL)
    (hover : ∀ x : K₀, τ (algebraMap K₀ K x) = W.emb c x) (hsurj : Function.Surjective (algebraMap K₀ K))
    (H : ℕ) (hJ : ∀ a, IsJumpV PD T.ρ τ a → -(H : ℤ) ≤ a) {x : T.V ⊗[Qp] B}
    (hxD : x ∈ DcrisL PD T.ρ (W.emb c)) : x ∈ FilCris PD T.ρ (-(H : ℤ)) := by
  obtain ⟨u₀, hu₀⟩ := filV_exh (PD := PD) (LL := LL) (ιV PD (LL := LL) (V := T.V) x)
  have hx0 : x ∈ FilCris PD T.ρ u₀ := ⟨hxD.1, hu₀⟩
  by_cases hle : -(H : ℤ) ≤ u₀
  · exact Formalism.MainNotions.UnusedSlot80.LevR.filCris_anti T.ρ hle hx0
  · have key : ∀ k : ℕ, u₀ + k ≤ -(H : ℤ) → x ∈ FilCris PD T.ρ (u₀ + k) := by
      intro k
      induction k with
      | zero => intro _; simpa using hx0
      | succ k ih =>
        intro hk
        have := fil_step W T c τ hover hsurj (u₀ + k) (fun hj => by have := hJ _ hj; push_cast at hk; omega)
          hxD (ih (by push_cast at hk; omega))
        push_cast; rwa [← add_assoc]
    have := key (-(H : ℤ) - u₀).toNat (by omega)
    rwa [show u₀ + ((-(H : ℤ) - u₀).toNat : ℤ) = -(H : ℤ) by omega] at this

/- English proof (translation)
Establish `key : ∀ k : ℕ, x ∈ FilCris PD T.ρ (u + k)`. Introduce `k`. Proceed by induction on `k with`. Consider the case `zero => simpa using hx`. Consider the case `succ k ih`.

Use `fil_step W T c τ hover hsurj (u + k) (fun hj => by have := hJ _ hj; omega) hxD ih` as an intermediate fact. Use `push_cast`. Rewrite using `[← add_assoc]` and apply the resulting hypothesis. Establish `hall : ∀ a, ιV PD (LL` using `LL) (V := T.V) x ∈ FilV PD (LL := LL) (V := T.V) a := by`. Introduce `a`.

Distinguish the cases in `ha : a ≤ u`. Conclude with `Formalism.MainNotions.UnusedSlot80.LevR.filV_anti ha hx.2`. Use `(key (a - u).toNat).2` as an intermediate fact. Rewrite `this` using `[show u + ((a - u).toNat : ℤ) = a by omega]`. Then use the resulting hypothesis. Establish `h0` using `filV_sep (PD := PD) _ hall`.

Conclude with `Formalism.MainNotions.UnusedSlot80.LevR.ιV_inj (by rw [h0, map_zero])`.
-/
theorem fil_high (T : LocLat G Qp LL O) (c : ZMod n) (τ : K →ₐ[Qp] LL)
    (hover : ∀ x : K₀, τ (algebraMap K₀ K x) = W.emb c x) (hsurj : Function.Surjective (algebraMap K₀ K))
    (H : ℕ) (hJ : ∀ a, IsJumpV PD T.ρ τ a → a ≤ (H : ℤ)) (u : ℤ) (hu : (H : ℤ) < u) {x : T.V ⊗[Qp] B}
    (hxD : x ∈ DcrisL PD T.ρ (W.emb c)) (hx : x ∈ FilCris PD T.ρ u) : x = 0 := by
  have key : ∀ k : ℕ, x ∈ FilCris PD T.ρ (u + k) := by
    intro k
    induction k with
    | zero => simpa using hx
    | succ k ih =>
      have := fil_step W T c τ hover hsurj (u + k) (fun hj => by have := hJ _ hj; omega) hxD ih
      push_cast; rwa [← add_assoc]
  have hall : ∀ a, ιV PD (LL := LL) (V := T.V) x ∈ FilV PD (LL := LL) (V := T.V) a := by
    intro a
    by_cases ha : a ≤ u
    · exact Formalism.MainNotions.UnusedSlot80.LevR.filV_anti ha hx.2
    · have := (key (a - u).toNat).2
      rwa [show u + ((a - u).toNat : ℤ) = a by omega] at this
  have h0 := filV_sep (PD := PD) _ hall
  exact Formalism.MainNotions.UnusedSlot80.LevR.ιV_inj (by rw [h0, map_zero])

end Formalism.MainNotions.UnusedSlot80.LevC

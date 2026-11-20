import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.JordanExists
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.LocFSubspace
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.IsUnimodularAtIffVd
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.ApplyMemSmulOfMemAutSub
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.IsLatticeOfFibReps

open NumberField Module

noncomputable section

namespace Formalism.L2.SG.Pf.G8

open Formalism.HermitianLattices.Ext.L3 Formalism.L2.SG.Pf.Cnt

variable {K F V : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F]
  [Algebra F K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V]
  [IsScalarTower (𝓞 K) K V]

def fibS (h : V →ₗ⋆[K] V →ₗ[K] K) (U : Submodule K V) (𝔭 : Ideal (𝓞 F)) (M T : Submodule (𝓞 K) V) :
    Set (Submodule (𝓞 K) V) :=
  {Λ | (∃ Λ₀ : Submodule (𝓞 K) V, Submodule.IsLattice K Λ₀ ∧ locF 𝔭 Λ₀ = Λ) ∧
    dualF h 𝔭 Λ = Λ ∧
    Λ ⊓ U.restrictScalars (𝓞 K) = locF 𝔭 M ∧
    Λ ⊓ (orthK h U).restrictScalars (𝓞 K) = locF 𝔭 T}

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem fibP_eq (h : V →ₗ⋆[K] V →ₗ[K] K) (U : Submodule K V) (𝔭 : Ideal (𝓞 F)) (M T : Submodule (𝓞 K) V) :
    fibP h U 𝔭 M T = Nat.card (fibS h U 𝔭 M T) := rfl

/- English proof (translation)
Use `⟨hA.1.sup hB.1, ?_⟩` and prove the remaining obligations. Rewrite using `[eq_top_iff, ← hc.sup_eq_top, ← hA.2, ← hB.2]`. Conclude with `sup_le (Submodule.span_mono (SetLike.coe_subset_coe.mpr le_sup_left)) (Submodule.span_mono (SetLike.coe_subset_coe.mpr le_sup_right))`.
-/
theorem isLattice_sup {X Y : Submodule K V} (hc : IsCompl X Y) {A B : Submodule (𝓞 K) V}
    (hA : IsLatIn X A) (hB : IsLatIn Y B) : Submodule.IsLattice K (A ⊔ B) := by
  refine ⟨hA.1.sup hB.1, ?_⟩
  rw [eq_top_iff, ← hc.sup_eq_top, ← hA.2, ← hB.2]
  exact sup_le (Submodule.span_mono (SetLike.coe_subset_coe.mpr le_sup_left))
    (Submodule.span_mono (SetLike.coe_subset_coe.mpr le_sup_right))

/- English proof (translation)
Take `⟨n, hn, hnA⟩` from `LocF.exists_zsmul_le hA hB`. Take `⟨m, hm, hmB⟩` from `LocF.exists_zsmul_le hB hA`. Establish `hc : ((n * m : ℤ) : 𝓞 F) ≠ 0`. Conclude with `mul_ne_zero hn hm` after adjusting the coercions. Take `⟨s, hs⟩` from `(LocalFactorEquality.finite_vF_ne_zero hc).exists_finset`.

Use `⟨s, fun 𝔭 h𝔭 => ?_⟩` and prove the remaining obligations. Establish `hv : vF 𝔭.1 ((n * m : ℤ) : 𝓞 F) = 0`. Assume the negation of the conclusion as `hne`. Conclude with `h𝔭 ((hs 𝔭).2 hne)`. Establish `hnm` using `LocalizedFibreSets.notMem_of_vF_zero 𝔭.2 hc hv`.

Establish `hp` using `𝔭.2.isPrime`. Establish `hn' : ((n : ℤ) : 𝓞 F) ∉ 𝔭.1` using `fun h1 => hnm (by rw [Int.cast_mul]; exact 𝔭.1.mul_mem_right _ h1)`. Establish `hm' : ((m : ℤ) : 𝓞 F) ∉ 𝔭.1` using `fun h1 => hnm (by rw [Int.cast_mul]; exact 𝔭.1.mul_mem_left _ h1)`. Establish `key : ∀ {A B : Submodule (𝓞 K) V} (k : ℤ), ((k : ℤ) : 𝓞 F) ∉ 𝔭.1 → (∀ x ∈ A, k • x ∈ B) → locF 𝔭.1 A ≤ locF 𝔭.1 B`. Introduce `A B k hk hkA x hx`.

Take `⟨t, ht, htx⟩` from `(LocF.mem_locF_iff hp A x).1 hx`. Use `(LocF.mem_locF_iff hp B x).2 ⟨(k : 𝓞 F) * t, fun h1 => (hp.mem_or_mem h1).elim hk ht, ?_⟩` and prove the remaining obligations. Rewrite using `[map_mul, mul_smul, LocF.algebraMap_intCast_smul]`. Conclude with `hkA _ htx`. Conclude with `le_antisymm (key n hn' hnA) (key m hm' hmB)`.
-/
theorem exists_locF_eq {A B : Submodule (𝓞 K) V} (hA : Submodule.IsLattice K A)
    (hB : Submodule.IsLattice K B) :
    ∃ s : Finset {𝔭 : Ideal (𝓞 F) // 𝔭.IsMaximal}, ∀ 𝔭 ∉ s, locF 𝔭.1 A = locF 𝔭.1 B := by
  obtain ⟨n, hn, hnA⟩ := LocF.exists_zsmul_le hA hB
  obtain ⟨m, hm, hmB⟩ := LocF.exists_zsmul_le hB hA
  have hc : ((n * m : ℤ) : 𝓞 F) ≠ 0 := by
    exact_mod_cast mul_ne_zero hn hm
  obtain ⟨s, hs⟩ := (LocalFactorEquality.finite_vF_ne_zero hc).exists_finset
  refine ⟨s, fun 𝔭 h𝔭 => ?_⟩
  have hv : vF 𝔭.1 ((n * m : ℤ) : 𝓞 F) = 0 := by
    by_contra hne
    exact h𝔭 ((hs 𝔭).2 hne)
  have hnm := LocalizedFibreSets.notMem_of_vF_zero 𝔭.2 hc hv
  have hp := 𝔭.2.isPrime
  have hn' : ((n : ℤ) : 𝓞 F) ∉ 𝔭.1 := fun h1 => hnm (by rw [Int.cast_mul]; exact 𝔭.1.mul_mem_right _ h1)
  have hm' : ((m : ℤ) : 𝓞 F) ∉ 𝔭.1 := fun h1 => hnm (by rw [Int.cast_mul]; exact 𝔭.1.mul_mem_left _ h1)
  have key : ∀ {A B : Submodule (𝓞 K) V} (k : ℤ), ((k : ℤ) : 𝓞 F) ∉ 𝔭.1 → (∀ x ∈ A, k • x ∈ B) →
      locF 𝔭.1 A ≤ locF 𝔭.1 B := by
    intro A B k hk hkA x hx
    obtain ⟨t, ht, htx⟩ := (LocF.mem_locF_iff hp A x).1 hx
    refine (LocF.mem_locF_iff hp B x).2 ⟨(k : 𝓞 F) * t, fun h1 => (hp.mem_or_mem h1).elim hk ht, ?_⟩
    rw [map_mul, mul_smul, LocF.algebraMap_intCast_smul]
    exact hkA _ htx
  exact le_antisymm (key n hn' hnA) (key m hm' hmB)

/- English proof (translation)
Unfold both sides. The equivalence is reflexive.
-/
private lemma mem_locF_lemma {W : Type} [AddCommGroup W] [Module (𝓞 K) W] (𝔭 : Ideal (𝓞 F))
    (L : Submodule (𝓞 K) W) (x : W) :
    x ∈ locF 𝔭 L ↔ ∃ s ∈ Submonoid.closure
      {s : 𝓞 K | ∃ t : 𝓞 F, t ∉ 𝔭 ∧ algebraMap (𝓞 F) (𝓞 K) t = s}, s • x ∈ L := Iff.rfl

/- English proof (translation)
Proceed by induction on `hs using Submonoid.closure_induction with`. Consider the case `mem x hx`. Take `⟨t, ht, rfl⟩` from `hx`. Establish `ht0 : t ≠ 0` using `fun h0 => ht (h0 ▸ 𝔭.zero_mem)`. Establish `e : algebraMap (𝓞 K) K (algebraMap (𝓞 F) (𝓞 K) t) = algebraMap F K (t : F)` using `rfl`.

Rewrite using `[e]`. Conclude with `(map_ne_zero _).mpr (by simpa using ht0)`. Consider the case `one => simp`. Consider the case `mul x y _ _ hx hy => rw [map_mul]`. Conclude with `mul_ne_zero hx hy`.
-/
private lemma algebraMap_ne_zero_of_mem_closure_prime_compl {𝔭 : Ideal (𝓞 F)} {s : 𝓞 K}
    (hs : s ∈ Submonoid.closure {s : 𝓞 K | ∃ t : 𝓞 F, t ∉ 𝔭 ∧ algebraMap (𝓞 F) (𝓞 K) t = s}) :
    algebraMap (𝓞 K) K s ≠ 0 := by
  induction hs using Submonoid.closure_induction with
  | mem x hx =>
    obtain ⟨t, ht, rfl⟩ := hx
    have ht0 : t ≠ 0 := fun h0 => ht (h0 ▸ 𝔭.zero_mem)
    have e : algebraMap (𝓞 K) K (algebraMap (𝓞 F) (𝓞 K) t) = algebraMap F K (t : F) := rfl
    rw [e]
    exact (map_ne_zero _).mpr (by simpa using ht0)
  | one => simp
  | mul x y _ _ hx hy => rw [map_mul]; exact mul_ne_zero hx hy

/- English proof (translation)
Apply `le_antisymm` to reduce the goal to its premises. Introduce and unpack `x ⟨hx1, hx2⟩`. Take `⟨s, hs, hsx⟩` from `(mem_locF_lemma 𝔭 _ x).mp hx1`. Take `⟨a, ha, b, hb, hab⟩` from `Submodule.mem_sup.mp hsx`. Establish `hxX : x ∈ X` using `hx2`.

Establish `hsX : s • x ∈ X`. Rewrite using `[← algebraMap_smul K s x]`. Conclude with `X.smul_mem _ hxX`. Establish `hbX : b ∈ X`. Establish `: b = s • x - a` using `by rw [← hab]; abel`.

Rewrite using `[this]`. Conclude with `X.sub_mem hsX (hA a ha)`. Establish `hb0 : b = 0`. Use `hc.inf_eq_bot` as an intermediate fact. Establish `hmem : b ∈ X ⊓ Y` using `⟨hbX, hB b hb⟩`.

Rewrite `hmem` using `[this]`. Conclude with `(Submodule.mem_bot K).mp hmem`. Use `(mem_locF_lemma 𝔭 _ x).mpr ⟨s, hs, ?_⟩` and prove the remaining obligations. Rewrite using `[← hab, hb0, add_zero]`. Conclude with `ha`.

Introduce `x hx`. Take `⟨s, hs, hsx⟩` from `(mem_locF_lemma 𝔭 _ x).mp hx`. Use `⟨(mem_locF_lemma 𝔭 _ x).mpr ⟨s, hs, Submodule.mem_sup_left hsx⟩, ?_⟩` and prove the remaining obligations. Establish `hs0 : algebraMap (𝓞 K) K s ≠ 0` using `algebraMap_ne_zero_of_mem_closure_prime_compl hs`. Establish `e : x = (algebraMap (𝓞 K) K s)⁻¹ • (s • x)`.

Rewrite using `[← algebraMap_smul K s x, smul_smul, inv_mul_cancel₀ hs0, one_smul]`. Use `show x ∈ X`. Rewrite using `[e]`. Conclude with `X.smul_mem _ (hA _ hsx)`.
-/
theorem locF_sup_inf {X Y : Submodule K V} (hc : IsCompl X Y) {A B : Submodule (𝓞 K) V}
    (hA : ∀ x ∈ A, x ∈ X) (hB : ∀ x ∈ B, x ∈ Y) {𝔭 : Ideal (𝓞 F)} (hp : 𝔭.IsPrime) :
    locF 𝔭 (A ⊔ B) ⊓ X.restrictScalars (𝓞 K) = locF 𝔭 A := by
  apply le_antisymm
  · rintro x ⟨hx1, hx2⟩
    obtain ⟨s, hs, hsx⟩ := (mem_locF_lemma 𝔭 _ x).mp hx1
    obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.mp hsx
    have hxX : x ∈ X := hx2
    have hsX : s • x ∈ X := by
      rw [← algebraMap_smul K s x]; exact X.smul_mem _ hxX
    have hbX : b ∈ X := by
      have : b = s • x - a := by rw [← hab]; abel
      rw [this]; exact X.sub_mem hsX (hA a ha)
    have hb0 : b = 0 := by
      have := hc.inf_eq_bot
      have hmem : b ∈ X ⊓ Y := ⟨hbX, hB b hb⟩
      rw [this] at hmem
      exact (Submodule.mem_bot K).mp hmem
    refine (mem_locF_lemma 𝔭 _ x).mpr ⟨s, hs, ?_⟩
    rw [← hab, hb0, add_zero]; exact ha
  · intro x hx
    obtain ⟨s, hs, hsx⟩ := (mem_locF_lemma 𝔭 _ x).mp hx
    refine ⟨(mem_locF_lemma 𝔭 _ x).mpr ⟨s, hs, Submodule.mem_sup_left hsx⟩, ?_⟩
    have hs0 : algebraMap (𝓞 K) K s ≠ 0 := algebraMap_ne_zero_of_mem_closure_prime_compl hs
    have e : x = (algebraMap (𝓞 K) K s)⁻¹ • (s • x) := by
      rw [← algebraMap_smul K s x, smul_smul, inv_mul_cancel₀ hs0, one_smul]
    show x ∈ X
    rw [e]
    exact X.smul_mem _ (hA _ hsx)

/- English proof (translation)
Introduce `x hx`. Establish `hx' : ∀ y ∈ B, h y x ∈ locF 𝔭 (1 : Submodule (𝓞 K) K)` using `hx`. Express the relevant statement in the definitionally equal form `∀ y ∈ A, h y x ∈ locF 𝔭 (1 : Submodule (𝓞 K) K)`. Conclude with `fun y hy => hx' y (hAB hy)`.
-/
theorem dualF_anti (h : V →ₗ⋆[K] V →ₗ[K] K) (𝔭 : Ideal (𝓞 F)) {A B : Submodule (𝓞 K) V} (hAB : A ≤ B) :
    dualF h 𝔭 B ≤ dualF h 𝔭 A := by
  intro x hx
  have hx' : ∀ y ∈ B, h y x ∈ locF 𝔭 (1 : Submodule (𝓞 K) K) := hx
  change ∀ y ∈ A, h y x ∈ locF 𝔭 (1 : Submodule (𝓞 K) K)
  exact fun y hy => hx' y (hAB hy)

end Formalism.L2.SG.Pf.G8

import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.RedSurjective
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KerEqRangeOfRangeEqKer
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrobKerIdealLeAugIdeal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OmegaLevelBijectiveOfPowEqZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DUnitMemRangeOfMemKerIdeal
open CategoryTheory TensorProduct Coalgebra Bialgebra GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Dieu

noncomputable section

namespace GlobalTheory.PDivGroup

/- English proof (translation)
Rewrite using `[← LinearMap.comp_apply, ← cotMap_comp]`. Take `⟨b, rfl⟩` from `AugCot.d_surjective _ x`. Rewrite using `[cotMap_d]`. Establish `h'` using `(kerIdeal_le_ker_iff g (π : A →ₐ[k] C)).1 h b`. Express the relevant statement in the definitionally equal form `dUnit k ((π : A →ₐ[k] C) (g b)) = 0`.

Rewrite using `[h']`. Conclude with `AugCot.d_algebraMap _ _`.
-/
theorem cotMap_comp_eq_zero_of_kerIdeal_le {k A B C : Type} [Field k] [CommRing A] [CommRing B]
    [CommRing C] [Bialgebra k A] [Bialgebra k B] [Bialgebra k C] (g : B →ₐc[k] A)
    (π : A →ₐc[k] C) (h : kerIdeal g ≤ RingHom.ker π) (x : Cot k B) :
    cotMap π (cotMap g x) = 0 := by
  rw [← LinearMap.comp_apply, ← cotMap_comp]
  obtain ⟨b, rfl⟩ := AugCot.d_surjective _ x
  rw [cotMap_d]
  have h' := (kerIdeal_le_ker_iff g (π : A →ₐ[k] C)).1 h b
  change dUnit k ((π : A →ₐ[k] C) (g b)) = 0
  rw [h']
  exact AugCot.d_algebraMap _ _

/- English proof (translation)
Introduce `p _ k _ _ G H q C _ _ _ _ π hπ`. Establish `hp : (p : k) = 0` using `CharP.cast_eq_zero k p`. Establish `part1 : kerIdeal (q.app 1) ≤ RingHom.ker π → ∀ w ∈ LinearMap.range (omegaMap G H q), cotMap π (w.1 1) = 0`. Introduce and unpack `h w ⟨v, rfl⟩`. Conclude with `cotMap_comp_eq_zero_of_kerIdeal_le (q.app 1) π h (v.1 1)`.

Use `⟨part1, fun h1 h2 => ?_, fun H' f hf => ?_⟩` and prove the remaining obligations. Set `Φ : G.omega →ₗ[k] Cot k C` to `cotMap π ∘ₗ G.omegaLevel 1`. Establish `hΦ : Function.Surjective Φ` using `(cotMap_surjective hπ).comp (G.omegaLevel_one_bijective hp).2`. Establish `hker : LinearMap.ker Φ = LinearMap.range (omegaMap G H q)`. Use extensionality with `w`.

Rewrite using `[LinearMap.mem_ker]`. Prove the components needed by the constructor for the conclusion. Introduce `hw`. Establish `hw' : AugCot.map (π : G.A 1 →ₐ[k] C) (BialgHomClass.counitAlgHom_comp π) (w.1 1) = 0` using `hw`. Take `⟨x, hx⟩` from `(AugCot.exact_kerMap_map (π : G.A 1 →ₐ[k] C) (BialgHomClass.counitAlgHom_comp π) hπ (w.1 1)).1 hw'`.

Establish `hx2 : dUnit k (x : G.A 1) = w.1 1`. Rewrite using `[← hx]`. Conclude with `(AugCot.kerMap_apply _ _ x).symm`. Establish `hxm : (x : G.A 1) ∈ kerIdeal (q.app 1) ⊔ augIdeal k (G.A 1) ^ 2` using `h1 x.2`. Take `⟨y, hy, z, hz, hyz⟩` from `Submodule.mem_sup.1 hxm`.

Establish `hz0 : dUnit k z = 0`. Establish `hzI : z ∈ augIdeal k (G.A 1)` using `Ideal.pow_le_self two_ne_zero hz`. Establish `hεz : counitAlgHom k (G.A 1) z = 0` using `hzI`. Rewrite using `[dUnit, AugCot.d_eq_zero_iff, hεz, map_zero, sub_zero]`. Conclude with `hz`.

Take `⟨u, hu⟩` from `dUnit_mem_range_of_mem_kerIdeal (q.app 1) hy`. Take `⟨v, rfl⟩` from `(H.omegaLevel_one_bijective hp).2 u`. Use `⟨v, (G.omegaLevel_one_bijective hp).1 ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `cotMap (q.app 1) (H.omegaLevel 1 v) = w.1 1`. Rewrite using `[hu, ← hx2, ← hyz]`.

Express the relevant statement in the definitionally equal form `dUnit k y = dUnit k (y + z)`. Rewrite using `[show dUnit k (y + z) = dUnit k y + dUnit k z from map_add _ y z, hz0, add_zero]`. Introduce `hw`. Conclude with `part1 h2 w hw`. Rewrite using `[← hker]`.

Conclude with `(Φ.quotKerEquivOfSurjective hΦ).finrank_eq`. Rewrite using `[cotMap_comp]`. Use `LinearMap.ext fun u => ?_` and prove the remaining obligations. Take `⟨v, rfl⟩` from `(H'.omegaLevel_one_bijective hp).2 u`. Conclude with `hf _ ⟨v, rfl⟩`.
-/
theorem cot_kernel_eq_coker_omegaMap : ∀ (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [CharP k p] (G H : PDivGroup p k) (q : G ⟶ H) (C : Type) [CommRing C] [HopfAlgebra k C] [IsCocomm k C] [Module.Finite k C] (π : G.A 1 →ₐc[k] C), Function.Surjective π → (kerIdeal (q.app 1) ≤ RingHom.ker π → ∀ w ∈ LinearMap.range (omegaMap G H q), cotMap π (w.1 1) = 0) ∧ (RingHom.ker π ≤ kerIdeal (q.app 1) ⊔ augIdeal k (G.A 1) ^ 2 → kerIdeal (q.app 1) ≤ RingHom.ker π → Module.finrank k (G.omega ⧸ LinearMap.range (omegaMap G H q)) = Module.finrank k (Cot k C)) ∧ ∀ (H' : PDivGroup p k) (f : G ⟶ H'), (∀ w ∈ LinearMap.range (omegaMap G H' f), cotMap π (w.1 1) = 0) → cotMap (π.comp (f.app 1)) = 0 := by
  intro p _ k _ _ G H q C _ _ _ _ π hπ
  have hp : (p : k) = 0 := CharP.cast_eq_zero k p
  have part1 : kerIdeal (q.app 1) ≤ RingHom.ker π →
      ∀ w ∈ LinearMap.range (omegaMap G H q), cotMap π (w.1 1) = 0 := by
    rintro h w ⟨v, rfl⟩
    exact cotMap_comp_eq_zero_of_kerIdeal_le (q.app 1) π h (v.1 1)
  refine ⟨part1, fun h1 h2 => ?_, fun H' f hf => ?_⟩
  ·
    let Φ : G.omega →ₗ[k] Cot k C := cotMap π ∘ₗ G.omegaLevel 1
    have hΦ : Function.Surjective Φ :=
      (cotMap_surjective hπ).comp (G.omegaLevel_one_bijective hp).2
    have hker : LinearMap.ker Φ = LinearMap.range (omegaMap G H q) := by
      ext w
      rw [LinearMap.mem_ker]
      constructor
      · intro hw
        have hw' : AugCot.map (π : G.A 1 →ₐ[k] C) (BialgHomClass.counitAlgHom_comp π) (w.1 1) = 0 :=
          hw
        obtain ⟨x, hx⟩ := (AugCot.exact_kerMap_map (π : G.A 1 →ₐ[k] C)
          (BialgHomClass.counitAlgHom_comp π) hπ (w.1 1)).1 hw'
        have hx2 : dUnit k (x : G.A 1) = w.1 1 := by
          rw [← hx]; exact (AugCot.kerMap_apply _ _ x).symm
        have hxm : (x : G.A 1) ∈ kerIdeal (q.app 1) ⊔ augIdeal k (G.A 1) ^ 2 := h1 x.2
        obtain ⟨y, hy, z, hz, hyz⟩ := Submodule.mem_sup.1 hxm
        have hz0 : dUnit k z = 0 := by
          have hzI : z ∈ augIdeal k (G.A 1) := Ideal.pow_le_self two_ne_zero hz
          have hεz : counitAlgHom k (G.A 1) z = 0 := hzI
          rw [dUnit, AugCot.d_eq_zero_iff, hεz, map_zero, sub_zero]
          exact hz
        obtain ⟨u, hu⟩ := dUnit_mem_range_of_mem_kerIdeal (q.app 1) hy
        obtain ⟨v, rfl⟩ := (H.omegaLevel_one_bijective hp).2 u
        refine ⟨v, (G.omegaLevel_one_bijective hp).1 ?_⟩
        change cotMap (q.app 1) (H.omegaLevel 1 v) = w.1 1
        rw [hu, ← hx2, ← hyz]
        change dUnit k y = dUnit k (y + z)
        rw [show dUnit k (y + z) = dUnit k y + dUnit k z from map_add _ y z, hz0, add_zero]
      · intro hw
        exact part1 h2 w hw
    rw [← hker]
    exact (Φ.quotKerEquivOfSurjective hΦ).finrank_eq
  · rw [cotMap_comp]
    refine LinearMap.ext fun u => ?_
    obtain ⟨v, rfl⟩ := (H'.omegaLevel_one_bijective hp).2 u
    exact hf _ ⟨v, rfl⟩

end GlobalTheory.PDivGroup

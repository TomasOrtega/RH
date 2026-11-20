import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RestrictHomApply
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.LocalLanglandsGL
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.WeilDeligne GlobalTheory.WeilDeligne.PrimDecomp GlobalTheory.LocLanglands

namespace GlobalTheory.WeilDeligne.PrimDecomp.SubStab

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}
variable {V : Type} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]

/- English proof (translation)
Proceed by induction on `j with`. Consider the case `zero => simp`. Consider the case `succ j ih`. Rewrite using `[pow_succ', Module.End.mul_apply, a.comm_apply, ih, map_smul, smul_smul, Module.End.mul_apply, pow_succ']`.
-/
theorem rho_pow_N_apply (a : WDRep h V) (σ : Weil h) (j : ℕ) (v : V) :
    a.ρ σ ((a.N ^ j) v) = (((normV w : ℕ) : ℂ) ^ deg σ) ^ j • (a.N ^ j) (a.ρ σ v) := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [pow_succ', Module.End.mul_apply, a.comm_apply, ih, map_smul, smul_smul,
      Module.End.mul_apply, pow_succ']

/- English proof (translation)
Establish `h1` using `rho_pow_N_apply a σ⁻¹ j (a.ρ σ v)`. Establish `h2 : a.ρ σ⁻¹ (a.ρ σ v) = v`. Rewrite using `[← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]`. Rewrite `h1` using `[h2, hv, smul_zero]`. Establish `h3 : a.ρ σ (a.ρ σ⁻¹ ((a.N ^ j) (a.ρ σ v))) = (a.N ^ j) (a.ρ σ v)`.

Rewrite using `[← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]`. Rewrite using `[← h3, h1, map_zero]`.
-/
theorem rho_mem_ker_pow (a : WDRep h V) (σ : Weil h) (j : ℕ) (v : V) (hv : (a.N ^ j) v = 0) :
    (a.N ^ j) (a.ρ σ v) = 0 := by
  have h1 := rho_pow_N_apply a σ⁻¹ j (a.ρ σ v)
  have h2 : a.ρ σ⁻¹ (a.ρ σ v) = v := by
    rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]
  rw [h2, hv, smul_zero] at h1
  have h3 : a.ρ σ (a.ρ σ⁻¹ ((a.N ^ j) (a.ρ σ v))) = (a.N ^ j) (a.ρ σ v) := by
    rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]
  rw [← h3, h1, map_zero]

/- English proof (translation)
Proceed by induction on `j with`. Consider the case `zero => simpa using hv`. Consider the case `succ j ih`. Establish `e : k + 2 * ((j + 1 : ℕ) : ℤ) = (k + 2 * (j : ℤ)) + 2` using `by push_cast; ring`. Rewrite using `[e, pow_succ', Module.End.mul_apply]`.

Conclude with `hN _ _ ih`.
-/
theorem pow_N_mem_wtSpace (a : WDRep h V)
    (hN : ∀ (k : ℤ), ∀ v ∈ wtSpace a k, a.N v ∈ wtSpace a (k + 2)) (j : ℕ) (k : ℤ) (v : V)
    (hv : v ∈ wtSpace a k) : (a.N ^ j) v ∈ wtSpace a (k + 2 * (j : ℤ)) := by
  induction j with
  | zero => simpa using hv
  | succ j ih =>
    have e : k + 2 * ((j + 1 : ℕ) : ℤ) = (k + 2 * (j : ℤ)) + 2 := by push_cast; ring
    rw [e, pow_succ', Module.End.mul_apply]
    exact hN _ _ ih

/- English proof (translation)
Introduce `E Ω _ _ _ _ _ A w h V _ _ _ a m hρ hN htop`. Use `⟨⟨fun σ => ?_, ?_⟩, ⟨fun σ => ?_, ?_⟩⟩` and prove the remaining obligations. Use `show strand a.N (wtSpace a (-(m : ℤ))) m ≤ (strand a.N (wtSpace a (-(m : ℤ))) m).comap (a.ρ σ)`. Use `iSup_le fun j => ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨s, hs, rfl⟩`.

Rewrite using `[Submodule.mem_comap]`. Rewrite using `[rho_pow_N_apply]`. Use `Submodule.smul_mem _ _ (Submodule.mem_iSup_of_mem j ⟨a.ρ σ s, hρ _ σ s hs, rfl⟩)` and prove the remaining obligations. Use `show strand a.N (wtSpace a (-(m : ℤ))) m ≤ (strand a.N (wtSpace a (-(m : ℤ))) m).comap a.N`. Use `iSup_le fun j => ?_` and prove the remaining obligations.

Introduce and unpack `_ ⟨s, hs, rfl⟩`. Rewrite using `[Submodule.mem_comap]`. Rewrite using `[← Module.End.mul_apply, ← pow_succ']`. Distinguish the cases in `hj : (j : ℕ) < m`. Conclude with `Submodule.mem_iSup_of_mem (⟨(j : ℕ) + 1, by omega⟩ : Fin (m + 1)) ⟨s, hs, rfl⟩`.

Establish `hjm : (j : ℕ) = m` using `by have := j.isLt; omega`. Establish `hmem` using `pow_N_mem_wtSpace a hN ((j : ℕ) + 1) _ s hs`. Rewrite `hmem` using `[htop _ (by push_cast; omega), Submodule.mem_bot]`. Rewrite using `[hmem]`. Conclude with `Submodule.zero_mem _`.

Use `show lowPart (wtSpace a) a.N m ≤ (lowPart (wtSpace a) a.N m).comap (a.ρ σ)`. Use `iSup_le fun k => ?_` and prove the remaining obligations. Introduce and unpack `v ⟨hv1, hv2⟩`. Conclude with `Submodule.mem_iSup_of_mem k ⟨hρ k σ v hv1, rho_mem_ker_pow a σ _ v hv2⟩`. Use `show lowPart (wtSpace a) a.N m ≤ (lowPart (wtSpace a) a.N m).comap a.N`.

Use `iSup_le fun k => ?_` and prove the remaining obligations. Introduce and unpack `v ⟨hv1, hv2⟩`. Use `Submodule.mem_iSup_of_mem (k + 2) ⟨hN k v hv1, ?_⟩` and prove the remaining obligations. Use `show (a.N ^ (((m : ℤ) - (k + 2) + 1) / 2).toNat) (a.N v) = 0`. Establish `hv2' : (a.N ^ (((m : ℤ) - k + 1) / 2).toNat) v = 0` using `hv2`.

Establish `hle : (((m : ℤ) - k + 1) / 2).toNat ≤ (((m : ℤ) - (k + 2) + 1) / 2).toNat + 1` using `by omega`. Rewrite using `[← Module.End.mul_apply, ← pow_succ, ← Nat.sub_add_cancel hle, pow_add, Module.End.mul_apply, hv2', map_zero]`.
-/
theorem strand_and_lowPart_stable : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E)) (h : IsPlaceOver A w) (V : Type) [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V] (a : WDRep h V) (m : ℕ), (∀ (k : ℤ) (σ : Weil h), ∀ v ∈ wtSpace a k, a.ρ σ v ∈ wtSpace a k) → (∀ (k : ℤ), ∀ v ∈ wtSpace a k, a.N v ∈ wtSpace a (k + 2)) → (∀ k : ℤ, (m : ℤ) < k → wtSpace a k = ⊥) → IsSubWD a (strand a.N (wtSpace a (-(m : ℤ))) m) ∧ IsSubWD a (lowPart (wtSpace a) a.N m) := by
  intro E Ω _ _ _ _ _ A w h V _ _ _ a m hρ hN htop
  refine ⟨⟨fun σ => ?_, ?_⟩, ⟨fun σ => ?_, ?_⟩⟩
  ·
    show strand a.N (wtSpace a (-(m : ℤ))) m ≤ (strand a.N (wtSpace a (-(m : ℤ))) m).comap (a.ρ σ)
    refine iSup_le fun j => ?_
    rintro _ ⟨s, hs, rfl⟩
    rw [Submodule.mem_comap]
    rw [rho_pow_N_apply]
    refine Submodule.smul_mem _ _ (Submodule.mem_iSup_of_mem j ⟨a.ρ σ s, hρ _ σ s hs, rfl⟩)
  ·
    show strand a.N (wtSpace a (-(m : ℤ))) m ≤ (strand a.N (wtSpace a (-(m : ℤ))) m).comap a.N
    refine iSup_le fun j => ?_
    rintro _ ⟨s, hs, rfl⟩
    rw [Submodule.mem_comap]
    rw [← Module.End.mul_apply, ← pow_succ']
    by_cases hj : (j : ℕ) < m
    · exact Submodule.mem_iSup_of_mem (⟨(j : ℕ) + 1, by omega⟩ : Fin (m + 1)) ⟨s, hs, rfl⟩
    · have hjm : (j : ℕ) = m := by have := j.isLt; omega
      have hmem := pow_N_mem_wtSpace a hN ((j : ℕ) + 1) _ s hs
      rw [htop _ (by push_cast; omega), Submodule.mem_bot] at hmem
      rw [hmem]
      exact Submodule.zero_mem _
  ·
    show lowPart (wtSpace a) a.N m ≤ (lowPart (wtSpace a) a.N m).comap (a.ρ σ)
    refine iSup_le fun k => ?_
    rintro v ⟨hv1, hv2⟩
    exact Submodule.mem_iSup_of_mem k ⟨hρ k σ v hv1, rho_mem_ker_pow a σ _ v hv2⟩
  ·
    show lowPart (wtSpace a) a.N m ≤ (lowPart (wtSpace a) a.N m).comap a.N
    refine iSup_le fun k => ?_
    rintro v ⟨hv1, hv2⟩
    refine Submodule.mem_iSup_of_mem (k + 2) ⟨hN k v hv1, ?_⟩
    show (a.N ^ (((m : ℤ) - (k + 2) + 1) / 2).toNat) (a.N v) = 0
    have hv2' : (a.N ^ (((m : ℤ) - k + 1) / 2).toNat) v = 0 := hv2
    have hle : (((m : ℤ) - k + 1) / 2).toNat ≤ (((m : ℤ) - (k + 2) + 1) / 2).toNat + 1 := by omega
    rw [← Module.End.mul_apply, ← pow_succ, ← Nat.sub_add_cancel hle, pow_add,
      Module.End.mul_apply, hv2', map_zero]

end GlobalTheory.WeilDeligne.PrimDecomp.SubStab

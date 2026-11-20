import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IotaScalarOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CharmatrixBlockDiagonal
open GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.SandwichMaps GlobalTheory.DetInv Matrix TensorProduct

namespace GlobalTheory.RepModule

def Rep {R Λ n : Type} [CommRing R] [Ring Λ] [Algebra R Λ] [Fintype n] [DecidableEq n]
    (_ρ : Λ →ₐ[R] Matrix n n R) : Type := n → R

variable {R Λ n : Type} [CommRing R] [Ring Λ] [Algebra R Λ] [Fintype n] [DecidableEq n]
  (ρ : Λ →ₐ[R] Matrix n n R)

instance : AddCommGroup (Rep ρ) := inferInstanceAs (AddCommGroup (n → R))
instance : Module R (Rep ρ) := inferInstanceAs (Module R (n → R))
instance : Module.Free R (Rep ρ) := inferInstanceAs (Module.Free R (n → R))
instance : Module.Finite R (Rep ρ) := inferInstanceAs (Module.Finite R (n → R))

instance : Module Λ (Rep ρ) where
  smul a v := (ρ a *ᵥ (v : n → R) : n → R)
  one_smul v := by
    change ρ 1 *ᵥ _ = _
    rw [map_one]; exact one_mulVec _
  mul_smul a b v := by
    change ρ (a * b) *ᵥ _ = ρ a *ᵥ (ρ b *ᵥ _)
    rw [map_mul]; symm; apply mulVec_mulVec
  smul_zero a := by change ρ a *ᵥ _ = _; apply mulVec_zero
  smul_add a v w := by change ρ a *ᵥ _ = ρ a *ᵥ _ + ρ a *ᵥ _; apply mulVec_add
  add_smul a b v := by
    change ρ (a + b) *ᵥ _ = ρ a *ᵥ _ + ρ b *ᵥ _
    rw [map_add]; apply add_mulVec
  zero_smul v := by
    change ρ 0 *ᵥ _ = _
    rw [map_zero]; apply zero_mulVec

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem smul_def (a : Λ) (v : Rep ρ) : a • v = (ρ a *ᵥ (v : n → R) : n → R) := rfl

instance : IsScalarTower R Λ (Rep ρ) where
  smul_assoc c a v := by
    change ρ (c • a) *ᵥ _ = c • (ρ a *ᵥ _)
    rw [map_smul]; apply smul_mulVec

def toFun : Rep ρ ≃ₗ[R] (n → R) := LinearEquiv.refl R (n → R)

end GlobalTheory.RepModule

open GlobalTheory.RepModule in

/- English proof (translation)
Introduce `p _ Λ _ _ _ _ _ _ h d b ρ`. Use `haveI : Module.Finite Λ (Rep ρ) := Module.Finite.of_restrictScalars_finite ℤ_[p] Λ (Rep ρ)`. Use `haveI : NoZeroSMulDivisors Λ (Rep ρ) := by`. Use `⟨fun {a v} hav => ?_⟩` and prove the remaining obligations. Assume the negation of the conclusion as `hne`.

Use `push_neg at hne`. Take `⟨ha, hv⟩` from `hne`. Establish `hI` using `Ideal.comap_ne_bot_of_integral_mem (R := ℤ_[p]) ha (Ideal.mem_span_singleton_self a) (Algebra.IsIntegral.isIntegral a)`. Take `⟨r, hr, hr0⟩` from `Submodule.exists_mem_ne_zero_of_ne_bot hI`. Rewrite `hr` using `[Ideal.mem_comap, Ideal.mem_span_singleton']`.

Take `⟨c, hc⟩` from `hr`. Establish `h1 : r • v = 0`. Rewrite using `[← algebraMap_smul Λ r v, ← hc, mul_smul, hav, smul_zero]`. Establish `h2 : (r • (v : Fin h → ℤ_[p])) = 0` using `h1`. Conclude with `hv (smul_eq_zero.mp h2 |>.resolve_left hr0)`.

Use `haveI : Module.Free Λ (Rep ρ) := Module.free_of_finite_type_torsion_free'`. Set `N` to `Module.finrank Λ (Rep ρ)`. Set `y : Module.Basis (Fin N) Λ (Rep ρ)` to `Module.finBasis Λ (Rep ρ)`. Set `c` to `b.smulTower y`. Use `⟨N, fun i => (y i : Fin h → ℤ_[p]), ?_, ?_, ?_⟩` and prove the remaining obligations.

Establish `h1` using `Module.finrank_eq_card_basis c`. Establish `h2 : Module.finrank ℤ_[p] (Rep ρ) = h`. Rewrite using `[(toFun ρ).finrank_eq]`. Simplify using the standard rewrite rules. Rewrite `h1` using `[h2]`.

Simplify using `[Fintype.card_prod, Fintype.card_fin] at h1`. Rewrite using `[h1, mul_comm]`. Establish `hs` using `(c.map (toFun ρ)).span_eq`. Rewrite using `[← hs]`. Use `congr 1`.

Use extensionality with `x`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨⟨i, j⟩, rfl⟩`. Conclude with `⟨(j, i), by rw [Module.Basis.map_apply, Module.Basis.smulTower_apply]; rfl⟩`. Introduce and unpack `⟨⟨j, i⟩, rfl⟩`.

Conclude with `⟨(i, j), by rw [Module.Basis.map_apply, Module.Basis.smulTower_apply]; rfl⟩`. Introduce `a`. Rewrite using `[← GlobalTheory.FibreCharpoly.charpoly_lsmul_eq_pow ℤ_[p] Λ (Rep ρ) y a, ← LinearEquiv.charpoly_conj (toFun ρ), ← LinearMap.charpoly_toMatrix _ (Pi.basisFun ℤ_[p] (Fin h))]`. Use `congr 1`. Use extensionality with `i j`.

Rewrite using `[LinearMap.toMatrix_eq_toMatrix', LinearMap.toMatrix'_apply]`. Use `symm`. Express the relevant statement in the definitionally equal form `(ρ a *ᵥ (Pi.single j 1 : Fin h → ℤ_[p])) i = _`. Simplify using `[mulVec_single]`.
-/
theorem GlobalTheory.DetInv.rep_free_charpoly : ∀ (p : ℕ) [Fact p.Prime] (Λ : Type) [CommRing Λ] [IsDomain Λ]
    [IsDiscreteValuationRing Λ] [Algebra ℤ_[p] Λ] [Module.Free ℤ_[p] Λ] [Module.Finite ℤ_[p] Λ]
    (h d : ℕ) (b : Module.Basis (Fin d) ℤ_[p] Λ) (ρ : Λ →ₐ[ℤ_[p]] Matrix (Fin h) (Fin h) ℤ_[p]),
    ∃ (N : ℕ) (y : Fin N → Fin h → ℤ_[p]), h = N * d ∧
      Submodule.span ℤ_[p] (Set.range fun ij : Fin N × Fin d => ρ (b ij.2) *ᵥ y ij.1) = ⊤ ∧
      ∀ a : Λ, (ρ a).charpoly = (LinearMap.mulLeft ℤ_[p] a).charpoly ^ N := by
  intro p _ Λ _ _ _ _ _ _ h d b ρ
  classical
  haveI : Module.Finite Λ (Rep ρ) := Module.Finite.of_restrictScalars_finite ℤ_[p] Λ (Rep ρ)
  haveI : NoZeroSMulDivisors Λ (Rep ρ) := by
    refine ⟨fun {a v} hav => ?_⟩
    by_contra hne
    push_neg at hne
    obtain ⟨ha, hv⟩ := hne
    have hI := Ideal.comap_ne_bot_of_integral_mem (R := ℤ_[p]) ha (Ideal.mem_span_singleton_self a)
      (Algebra.IsIntegral.isIntegral a)
    obtain ⟨r, hr, hr0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hI
    rw [Ideal.mem_comap, Ideal.mem_span_singleton'] at hr
    obtain ⟨c, hc⟩ := hr
    have h1 : r • v = 0 := by
      rw [← algebraMap_smul Λ r v, ← hc, mul_smul, hav, smul_zero]
    have h2 : (r • (v : Fin h → ℤ_[p])) = 0 := h1
    exact hv (smul_eq_zero.mp h2 |>.resolve_left hr0)
  haveI : Module.Free Λ (Rep ρ) := Module.free_of_finite_type_torsion_free'
  let N := Module.finrank Λ (Rep ρ)
  let y : Module.Basis (Fin N) Λ (Rep ρ) := Module.finBasis Λ (Rep ρ)
  let c := b.smulTower y
  refine ⟨N, fun i => (y i : Fin h → ℤ_[p]), ?_, ?_, ?_⟩
  · have h1 := Module.finrank_eq_card_basis c
    have h2 : Module.finrank ℤ_[p] (Rep ρ) = h := by
      rw [(toFun ρ).finrank_eq]; simp
    rw [h2] at h1
    simp [Fintype.card_prod, Fintype.card_fin] at h1
    rw [h1, mul_comm]
  · have hs := (c.map (toFun ρ)).span_eq
    rw [← hs]
    congr 1
    ext x
    constructor
    · rintro ⟨⟨i, j⟩, rfl⟩
      exact ⟨(j, i), by rw [Module.Basis.map_apply, Module.Basis.smulTower_apply]; rfl⟩
    · rintro ⟨⟨j, i⟩, rfl⟩
      exact ⟨(i, j), by rw [Module.Basis.map_apply, Module.Basis.smulTower_apply]; rfl⟩
  · intro a
    rw [← GlobalTheory.FibreCharpoly.charpoly_lsmul_eq_pow ℤ_[p] Λ (Rep ρ) y a,
      ← LinearEquiv.charpoly_conj (toFun ρ), ← LinearMap.charpoly_toMatrix _ (Pi.basisFun ℤ_[p] (Fin h))]
    congr 1
    ext i j
    rw [LinearMap.toMatrix_eq_toMatrix', LinearMap.toMatrix'_apply]
    symm
    change (ρ a *ᵥ (Pi.single j 1 : Fin h → ℤ_[p])) i = _
    simp [mulVec_single]

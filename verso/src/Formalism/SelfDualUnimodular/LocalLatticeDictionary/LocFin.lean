import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.LatDictZAbs
import Lemmata.Denominators.Denom

noncomputable section

open NumberField

namespace Formalism.L2.SG.Pf.LatDictZ.Z0.LF

open ReciprocityTheory.ChartRestriction.L3 ReciprocityTheory.ChartRestriction.L3.WA

variable {E : Type} [Field E] [NumberField E] [StarRing E] {n : ℕ}

/- English proof (translation)
Establish `hQi : IsIntegral ℚ e` using `Algebra.IsIntegral.isIntegral (R := ℚ) e`. Choose the witnesses or unpack the hypotheses as in `⟨y, hy0, hint⟩ : ∃ y : ℤ, y ≠ 0 ∧ IsIntegral ℤ ((y : E) * e) := by`. Establish `hZ : IsAlgebraic ℤ e` using `(IsFractionRing.isAlgebraic_iff ℤ ℚ E).mpr hQi.isAlgebraic`. Take `⟨y, hy0, hi⟩` from `hZ.exists_integral_multiple`. Conclude with `⟨y, hy0, by simpa [zsmul_eq_mul] using hi⟩`.

Establish `hint' : IsIntegral ℤ ((y.natAbs : E) * e)`. Break down `Int.natAbs_eq y with h | h` into its components or cases. Rewrite `hint` using `[h]`. Rewrite `hint` using `[Int.cast_natCast]`. Then use the resulting hypothesis. Rewrite `hint` using `[h]`.

Establish `h2` using `hint.neg`. Move the coercions through the operations in `at h2`. Simplify using `using h2`. Use `⟨y.natAbs, Int.natAbs_pos.mpr hy0, ?_⟩` and prove the remaining obligations. Conclude with `⟨IsIntegralClosure.mk' (𝓞 E) ((y.natAbs : E) * e) hint', (IsIntegralClosure.algebraMap_mk' (𝓞 E) _ hint').symm⟩`.
-/
theorem nat_denom (e : E) : ∃ m : ℕ, 0 < m ∧ ∃ r : 𝓞 E, (m : E) * e = algebraMap (𝓞 E) E r := by
  have hQi : IsIntegral ℚ e := Algebra.IsIntegral.isIntegral (R := ℚ) e
  obtain ⟨y, hy0, hint⟩ : ∃ y : ℤ, y ≠ 0 ∧ IsIntegral ℤ ((y : E) * e) := by
    have hZ : IsAlgebraic ℤ e := (IsFractionRing.isAlgebraic_iff ℤ ℚ E).mpr hQi.isAlgebraic
    obtain ⟨y, hy0, hi⟩ := hZ.exists_integral_multiple
    exact ⟨y, hy0, by simpa [zsmul_eq_mul] using hi⟩
  have hint' : IsIntegral ℤ ((y.natAbs : E) * e) := by
    rcases Int.natAbs_eq y with h | h
    · rw [h] at hint
      rwa [Int.cast_natCast] at hint
    · rw [h] at hint
      have h2 := hint.neg
      push_cast at h2
      simpa using h2
  refine ⟨y.natAbs, Int.natAbs_pos.mpr hy0, ?_⟩
  exact ⟨IsIntegralClosure.mk' (𝓞 E) ((y.natAbs : E) * e) hint',
    (IsIntegralClosure.algebraMap_mk' (𝓞 E) _ hint').symm⟩

/- English proof (translation)
Apply the tactic sequence `first | exact Bl.DenominatorsAlt.goal1 .. | (apply Bl.DenominatorsAlt.goal1 <;> assumption) | (intros; apply Bl.DenominatorsAlt.goal1 <;> assumption)`.
-/
theorem vec_denom (M : Submodule (𝓞 E) (Fin n → E)) (hsp : Submodule.span E (M : Set (Fin n → E)) = ⊤)
    (v : Fin n → E) : ∃ m : ℕ, 0 < m ∧ (m : 𝓞 E) • v ∈ M := by
  first | exact Bl.DenominatorsAlt.goal1 .. | (apply Bl.DenominatorsAlt.goal1 <;> assumption) | (intros; apply Bl.DenominatorsAlt.goal1 <;> assumption)

/- English proof (translation)
Take `⟨S, hS⟩` from `hL`. Use `choose f hf0 hfM using fun v : Fin n → E => vec_denom M hsp v`. Use `⟨∏ s ∈ S, f s, Finset.prod_pos (fun i _ => hf0 i), ?_⟩` and prove the remaining obligations. Introduce `x hx`. Rewrite `hx` using `[← hS]`.

Establish `hle : Submodule.span (𝓞 E) (S : Set (Fin n → E)) ≤ M.comap (((∏ s ∈ S, f s : ℕ) : 𝓞 E) • LinearMap.id)`. Rewrite using `[Submodule.span_le]`. Introduce `s hs`. Rewrite using `[SetLike.mem_coe, Submodule.mem_comap, LinearMap.smul_apply, LinearMap.id_apply]`. Take `⟨k, hk⟩` from `Finset.dvd_prod_of_mem f (Finset.mem_coe.mp hs)`.

Rewrite using `[hk, Nat.cast_mul, mul_comm, mul_smul]`. Conclude with `M.smul_mem _ (hfM s)`. Establish `h2` using `hle hx`. Rewrite `h2` using `[Submodule.mem_comap, LinearMap.smul_apply, LinearMap.id_apply]`. Then use the resulting hypothesis.
-/
theorem lat_denom (L M : Submodule (𝓞 E) (Fin n → E)) (hL : L.FG)
    (hsp : Submodule.span E (M : Set (Fin n → E)) = ⊤) :
    ∃ N : ℕ, 0 < N ∧ ∀ x ∈ L, (N : 𝓞 E) • x ∈ M := by
  classical
  obtain ⟨S, hS⟩ := hL
  choose f hf0 hfM using fun v : Fin n → E => vec_denom M hsp v
  refine ⟨∏ s ∈ S, f s, Finset.prod_pos (fun i _ => hf0 i), ?_⟩
  intro x hx
  rw [← hS] at hx
  have hle : Submodule.span (𝓞 E) (S : Set (Fin n → E)) ≤
      M.comap (((∏ s ∈ S, f s : ℕ) : 𝓞 E) • LinearMap.id) := by
    rw [Submodule.span_le]
    intro s hs
    rw [SetLike.mem_coe, Submodule.mem_comap, LinearMap.smul_apply, LinearMap.id_apply]
    obtain ⟨k, hk⟩ := Finset.dvd_prod_of_mem f (Finset.mem_coe.mp hs)
    rw [hk, Nat.cast_mul, mul_comm, mul_smul]
    exact M.smul_mem _ (hfM s)
  have h2 := hle hx
  rwa [Submodule.mem_comap, LinearMap.smul_apply, LinearMap.id_apply] at h2

/- English proof (translation)
Introduce and unpack `x ⟨t, ht, htx⟩`. Establish `hNh : (N : 𝓞 E) ∈ Formalism.HermitianLatticesTheory.hcompl (K` using `E) p := by`. Rewrite using `[mem_hcompl_iff hp, mem_conjIdeal_iff, map_natCast]`. Conclude with `⟨hNp, hNp⟩`. Use `⟨(N : 𝓞 E) * t, mul_mem hNh ht, ?_⟩` and prove the remaining obligations.

Rewrite using `[mul_smul]`. Conclude with `hN _ htx`.
-/
theorem loc_le_of_denom {L M : Submodule (𝓞 E) (Fin n → E)} {N : ℕ} (hN : ∀ x ∈ L, (N : 𝓞 E) • x ∈ M)
    {p : Ideal (𝓞 E)} (hp : p.IsPrime) (hNp : (N : 𝓞 E) ∉ p) :
    Formalism.HermitianLatticesTheory.loc (K := E) p L ≤ Formalism.HermitianLatticesTheory.loc (K := E) p M := by
  rintro x ⟨t, ht, htx⟩
  have hNh : (N : 𝓞 E) ∈ Formalism.HermitianLatticesTheory.hcompl (K := E) p := by
    rw [mem_hcompl_iff hp, mem_conjIdeal_iff, map_natCast]
    exact ⟨hNp, hNp⟩
  refine ⟨(N : 𝓞 E) * t, mul_mem hNh ht, ?_⟩
  rw [mul_smul]; exact hN _ htx

/- English proof (translation)
Introduce `E _ _ _ n L M hLfg hMfg hLsp hMsp`. Take `⟨N₁, hN₁, h1⟩` from `lat_denom L M hLfg hMsp`. Take `⟨N₂, hN₂, h2⟩` from `lat_denom M L hMfg hLsp`. Establish `h0 : ((N₁ * N₂ : ℕ) : 𝓞 E) ≠ 0`. Rewrite using `[Nat.cast_ne_zero]`.

Conclude with `(Nat.mul_pos hN₁ hN₂).ne'`. Use `(Ring.HasFiniteQuotients.finite_setOfPred_mem _ h0).subset ?_` and prove the remaining obligations. Introduce and unpack `p ⟨hp, hne⟩`. Assume the negation of the conclusion as `hNp`. Apply `hne` to reduce the goal to its premises.

Establish `hp'` using `hp.isPrime`. Simplify using `only [Set.mem_setOf_eq, Nat.cast_mul] at hNp`. Establish `n1 : (N₁ : 𝓞 E) ∉ p` using `fun h => hNp (p.mul_mem_right _ h)`. Establish `n2 : (N₂ : 𝓞 E) ∉ p` using `fun h => hNp (p.mul_mem_left _ h)`. Conclude with `le_antisymm (loc_le_of_denom h2 hp' n2) (loc_le_of_denom h1 hp' n1)`.
-/
theorem lattice_locally_finite : LocFinite := by
  intro E _ _ _ n L M hLfg hMfg hLsp hMsp
  obtain ⟨N₁, hN₁, h1⟩ := lat_denom L M hLfg hMsp
  obtain ⟨N₂, hN₂, h2⟩ := lat_denom M L hMfg hLsp
  have h0 : ((N₁ * N₂ : ℕ) : 𝓞 E) ≠ 0 := by
    rw [Nat.cast_ne_zero]; exact (Nat.mul_pos hN₁ hN₂).ne'
  refine (Ring.HasFiniteQuotients.finite_setOfPred_mem _ h0).subset ?_
  rintro p ⟨hp, hne⟩
  by_contra hNp
  apply hne
  have hp' := hp.isPrime
  simp only [Set.mem_setOf_eq, Nat.cast_mul] at hNp
  have n1 : (N₁ : 𝓞 E) ∉ p := fun h => hNp (p.mul_mem_right _ h)
  have n2 : (N₂ : 𝓞 E) ∉ p := fun h => hNp (p.mul_mem_left _ h)
  exact le_antisymm (loc_le_of_denom h2 hp' n2) (loc_le_of_denom h1 hp' n1)

end Formalism.L2.SG.Pf.LatDictZ.Z0.LF

import Mathlib
import Formalism.PeriodIntegrals.KerIso

noncomputable section
open scoped BigOperators
open NumberField

namespace PI.KerIso.DetOrdW

open IsDedekindDomain

variable {K : Type} [Field K] [NumberField K]

/- English proof (translation)
Establish `hcast : ((s : ℕ) : K) = algebraMap (𝓞 K) K (s : 𝓞 K)` using `by simp`. Rewrite using `[hcast, IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap, IsDedekindDomain.HeightOneSpectrum.intValuation_eq_one_iff]`. Introduce `hs𝔭`. Take `⟨a, b, hab⟩` from `Nat.isCoprime_iff_coprime.2 hs`. Establish `h1 : (1 : 𝓞 K) ∈ 𝔭.asIdeal`.

Establish `e` using `congrArg (Int.cast : ℤ → 𝓞 K) hab`. Move the coercions through the operations in `at e`. Rewrite using `[← e]`. Conclude with `Ideal.add_mem _ (Ideal.mul_mem_left _ _ hs𝔭) (Ideal.mul_mem_left _ _ hp)`. Conclude with `𝔭.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 h1)`.
-/
theorem val_natCast_eq_one (𝔭 : HeightOneSpectrum (𝓞 K)) {p s : ℕ}
    (hp : ((p : ℕ) : 𝓞 K) ∈ 𝔭.asIdeal) (hs : Nat.Coprime s p) :
    𝔭.valuation K (s : K) = 1 := by
  have hcast : ((s : ℕ) : K) = algebraMap (𝓞 K) K (s : 𝓞 K) := by simp
  rw [hcast, IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap,
    IsDedekindDomain.HeightOneSpectrum.intValuation_eq_one_iff]
  intro hs𝔭
  obtain ⟨a, b, hab⟩ := Nat.isCoprime_iff_coprime.2 hs
  have h1 : (1 : 𝓞 K) ∈ 𝔭.asIdeal := by
    have e := congrArg (Int.cast : ℤ → 𝓞 K) hab
    push_cast at e
    rw [← e]
    exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ hs𝔭) (Ideal.mul_mem_left _ _ hp)
  exact 𝔭.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 h1)

/- English proof (translation)
Take `⟨r, hr⟩` from `hx`. Establish `h : 𝔭.valuation K (algebraMap (𝓞 K) K r) ≤ 1` using `𝔭.valuation_le_one (K := K) r`. Rewrite `h` using `[hr, map_mul, val_natCast_eq_one 𝔭 hp hs, one_mul]`. Conclude with `h`.
-/
theorem val_le_one_of_den (𝔭 : HeightOneSpectrum (𝓞 K)) {p s : ℕ}
    (hp : ((p : ℕ) : 𝓞 K) ∈ 𝔭.asIdeal) (hs : Nat.Coprime s p) {x : K}
    (hx : (s : K) * x ∈ (algebraMap (𝓞 K) K).range) : 𝔭.valuation K x ≤ 1 := by
  obtain ⟨r, hr⟩ := hx
  have h : 𝔭.valuation K (algebraMap (𝓞 K) K r) ≤ 1 := 𝔭.valuation_le_one (K := K) r
  rw [hr, map_mul, val_natCast_eq_one 𝔭 hp hs, one_mul] at h
  exact h

/- English proof (translation)
Use `set M := LinearMap.toMatrix' u with hM`. Establish `hsingle : ∀ j : ι, ∀ w, (Pi.single j (1 : K) : ι → K) w ∈ (algebraMap (𝓞 K) K).range`. Introduce `j w`. Rewrite using `[Pi.single_apply]`. Use `split_ifs`.

Conclude with `one_mem _`. Conclude with `zero_mem _`. Use `choose s hs hsi using fun j => hu (Pi.single j 1) (hsingle j)`. Establish `hent : ∀ i j, M i j * (s j : K) ∈ (algebraMap (𝓞 K) K).range`. Introduce `i j`.

Rewrite using `[hM, LinearMap.toMatrix'_apply, mul_comm]`. Conclude with `hsi j i`. Use `choose N hN using fun i j => hent i j`. Establish `hdet : LinearMap.det u * ((∏ j, s j : ℕ) : K) = algebraMap (𝓞 K) K (Matrix.of N).det`. Rewrite using `[RingHom.map_det, ← LinearMap.det_toMatrix', ← hM, Nat.cast_prod, ← Matrix.det_diagonal, ← Matrix.det_mul]`.

Use `congr 1`. Use extensionality with `i j`. Simplify using `[Matrix.mul_diagonal, hN]`. Apply `val_le_one_of_den 𝔭 hp (Nat.Coprime.prod_left fun j _ => hs j)` to reduce the goal to its premises. Rewrite using `[mul_comm, hdet]`.

Conclude with `RingHom.mem_range_self _ _`.
-/
theorem val_det_le_one (𝔭 : HeightOneSpectrum (𝓞 K)) {p : ℕ}
    (hp : ((p : ℕ) : 𝓞 K) ∈ 𝔭.asIdeal) {ι : Type} [Fintype ι] [DecidableEq ι]
    (u : (ι → K) →ₗ[K] (ι → K))
    (hu : ∀ v : ι → K, (∀ w, v w ∈ (algebraMap (𝓞 K) K).range) →
      ∃ s : ℕ, Nat.Coprime s p ∧ ∀ w, (s : K) * u v w ∈ (algebraMap (𝓞 K) K).range) :
    𝔭.valuation K (LinearMap.det u) ≤ 1 := by
  set M := LinearMap.toMatrix' u with hM
  have hsingle : ∀ j : ι, ∀ w, (Pi.single j (1 : K) : ι → K) w ∈ (algebraMap (𝓞 K) K).range := by
    intro j w
    rw [Pi.single_apply]
    split_ifs
    · exact one_mem _
    · exact zero_mem _
  choose s hs hsi using fun j => hu (Pi.single j 1) (hsingle j)
  have hent : ∀ i j, M i j * (s j : K) ∈ (algebraMap (𝓞 K) K).range := by
    intro i j
    rw [hM, LinearMap.toMatrix'_apply, mul_comm]
    exact hsi j i
  choose N hN using fun i j => hent i j
  have hdet : LinearMap.det u * ((∏ j, s j : ℕ) : K) = algebraMap (𝓞 K) K (Matrix.of N).det := by
    rw [RingHom.map_det, ← LinearMap.det_toMatrix', ← hM, Nat.cast_prod, ← Matrix.det_diagonal, ← Matrix.det_mul]
    congr 1
    ext i j
    simp [Matrix.mul_diagonal, hN]
  apply val_le_one_of_den 𝔭 hp (Nat.Coprime.prod_left fun j _ => hs j)
  rw [mul_comm, hdet]
  exact RingHom.mem_range_self _ _

variable {E : Type} [Field E] [Algebra K E] {n : Type} [Fintype n]

/- English proof (translation)
Take `⟨-, hgB⟩` from `hg`. Take `⟨hgA', -⟩` from `hg'`. Take `⟨s₁, hs₁, h₁⟩` from `hgB v hv`. Take `⟨s₂, hs₂, h₂⟩` from `hgA' ((s₁ : K) • g.symm v) (fun a => by`. Simplify `h₁ a)` using `[Pi.smul_apply, Algebra.smul_def]`.

Use `⟨s₂ * s₁, Nat.Coprime.mul hs₂ hs₁, fun w => ?_⟩` and prove the remaining obligations. Establish `h` using `h₂ w`. Rewrite `h` using `[map_smul, Pi.smul_apply, smul_eq_mul]`. Rewrite using `[Nat.cast_mul, mul_assoc]`. Conclude with `h`.
-/
theorem comp_integral {M : Set E} {p : ℕ} {g g' : (Fin 4 → E) ≃ₗ[K] (Fin 4 × n → K)}
    (hg : AtP M g p) (hg' : AtP M g' p) (v : Fin 4 × n → K)
    (hv : ∀ w, v w ∈ (algebraMap (𝓞 K) K).range) :
    ∃ s : ℕ, Nat.Coprime s p ∧ ∀ w, (s : K) * g' (g.symm v) w ∈ (algebraMap (𝓞 K) K).range := by
  obtain ⟨-, hgB⟩ := hg
  obtain ⟨hgA', -⟩ := hg'
  obtain ⟨s₁, hs₁, h₁⟩ := hgB v hv
  obtain ⟨s₂, hs₂, h₂⟩ := hgA' ((s₁ : K) • g.symm v) (fun a => by
    simpa [Pi.smul_apply, Algebra.smul_def] using h₁ a)
  refine ⟨s₂ * s₁, Nat.Coprime.mul hs₂ hs₁, fun w => ?_⟩
  have h := h₂ w
  rw [map_smul, Pi.smul_apply, smul_eq_mul] at h
  rw [Nat.cast_mul, mul_assoc]
  exact h

/- English proof (translation)
Introduce `K E _ _ _ _ n _ M p 𝔭 g g' g₀ hp hp𝔭 hg hg'`. Set `u : (Fin 4 × n → K) →ₗ[K] (Fin 4 × n → K)` to `((g.symm.trans g' : (Fin 4 × n → K) ≃ₗ[K] (Fin 4 × n → K)) : (Fin 4 × n → K) →ₗ[K] (Fin 4 × n → K))`. Set `u' : (Fin 4 × n → K) →ₗ[K] (Fin 4 × n → K)` to `((g'.symm.trans g : (Fin 4 × n → K) ≃ₗ[K] (Fin 4 × n → K)) : (Fin 4 × n → K) →ₗ[K] (Fin 4 × n → K))`. Establish `h1 : 𝔭.valuation K (LinearMap.det u) ≤ 1` using `val_det_le_one 𝔭 hp𝔭 u (fun v hv => comp_integral hg hg' v hv)`. Establish `h2 : 𝔭.valuation K (LinearMap.det u') ≤ 1` using `val_det_le_one 𝔭 hp𝔭 u' (fun v hv => comp_integral hg' hg v hv)`.

Establish `hprod : LinearMap.det u' * LinearMap.det u = 1`. Rewrite using `[← LinearMap.det_comp]`. Establish `hid : u' ∘ₗ u = LinearMap.id` using `LinearMap.ext fun x => by simp [u, u']`. Rewrite using `[hid, LinearMap.det_id]`. Establish `hv1 : 𝔭.valuation K (LinearMap.det u) = 1`.

Use `le_antisymm h1 ?_` and prove the remaining obligations. Assume the negation of the conclusion as `hlt`. Use `push_neg at hlt`. Establish `h3 : 𝔭.valuation K (LinearMap.det u) * 𝔭.valuation K (LinearMap.det u') ≤ 𝔭.valuation K (LinearMap.det u)` using `mul_le_of_le_one_right' h2`. Rewrite `h3` using `[mul_comm, ← map_mul, hprod, map_one]`.

Conclude with `absurd h3 (not_le.2 hlt)`. Establish `hrel : detRel g' g₀ = LinearMap.det u * detRel g g₀`. Unfold `detRel`. Rewrite using `[← LinearMap.det_comp]`. Use `congr 1`.

Conclude with `LinearMap.ext fun x => by simp [u]`. Unfold `ordK`. Rewrite using `[hrel, map_mul, hv1, one_mul]`.
-/
theorem detOrdIndep : DetOrdIndep := by
  intro K E _ _ _ _ n _ M p 𝔭 g g' g₀ hp hp𝔭 hg hg'
  classical
  let u : (Fin 4 × n → K) →ₗ[K] (Fin 4 × n → K) :=
    ((g.symm.trans g' : (Fin 4 × n → K) ≃ₗ[K] (Fin 4 × n → K)) : (Fin 4 × n → K) →ₗ[K] (Fin 4 × n → K))
  let u' : (Fin 4 × n → K) →ₗ[K] (Fin 4 × n → K) :=
    ((g'.symm.trans g : (Fin 4 × n → K) ≃ₗ[K] (Fin 4 × n → K)) : (Fin 4 × n → K) →ₗ[K] (Fin 4 × n → K))
  have h1 : 𝔭.valuation K (LinearMap.det u) ≤ 1 :=
    val_det_le_one 𝔭 hp𝔭 u (fun v hv => comp_integral hg hg' v hv)
  have h2 : 𝔭.valuation K (LinearMap.det u') ≤ 1 :=
    val_det_le_one 𝔭 hp𝔭 u' (fun v hv => comp_integral hg' hg v hv)
  have hprod : LinearMap.det u' * LinearMap.det u = 1 := by
    rw [← LinearMap.det_comp]
    have hid : u' ∘ₗ u = LinearMap.id := LinearMap.ext fun x => by simp [u, u']
    rw [hid, LinearMap.det_id]
  have hv1 : 𝔭.valuation K (LinearMap.det u) = 1 := by
    refine le_antisymm h1 ?_
    by_contra hlt
    push_neg at hlt
    have h3 : 𝔭.valuation K (LinearMap.det u) * 𝔭.valuation K (LinearMap.det u') ≤ 𝔭.valuation K (LinearMap.det u) :=
      mul_le_of_le_one_right' h2
    rw [mul_comm, ← map_mul, hprod, map_one] at h3
    exact absurd h3 (not_le.2 hlt)
  have hrel : detRel g' g₀ = LinearMap.det u * detRel g g₀ := by
    unfold detRel
    rw [← LinearMap.det_comp]
    congr 1
    exact LinearMap.ext fun x => by simp [u]
  unfold ordK
  rw [hrel, map_mul, hv1, one_mul]

end PI.KerIso.DetOrdW

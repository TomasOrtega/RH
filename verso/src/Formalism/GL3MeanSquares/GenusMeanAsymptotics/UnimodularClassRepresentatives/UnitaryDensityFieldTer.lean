import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.UnitaryDensityFieldBis

open NumberField Module

noncomputable section

namespace Formalism.HermitianLattices.Ext.L3.unitaryAbsoluteValueBounds

variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]

local notation "ι" => algebraMap (𝓞 F) (𝓞 K)

variable {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V]
  [IsScalarTower (𝓞 K) K V]

/- English proof (translation)
Use `Submodule.smul_induction_on hx (fun r hr m _ => ?_) (fun x y hx hy => ?_)` and prove the remaining obligations. Take `⟨o, ho⟩` from `Submodule.mem_one.mp (hLi (w : V) w.2 (m : V) m.2)`. Use `⟨r * o, Ideal.mul_mem_right _ _ hr, ?_⟩` and prove the remaining obligations. Rewrite using `[Submodule.coe_smul, ← algebraMap_smul K r (m : V), map_smul, smul_eq_mul, map_mul, ho]`. Take `⟨u, hu, hu'⟩` from `hx`.

Take `⟨v, hv, hv'⟩` from `hy`. Conclude with `⟨u + v, Ideal.add_mem _ hu hv, by rw [Submodule.coe_add, map_add, hu', hv', map_add]⟩`.
-/
private theorem exists_mem_ideal_form_eq_of_mem_ideal_smul {h : V →ₗ⋆[K] V →ₗ[K] K} {L : Submodule (𝓞 K) V}
    (hLi : Formalism.HermitianLatticesTheory.IsIntegralLat h L) (I : Ideal (𝓞 K)) (w x : ↥L)
    (hx : x ∈ (I • ⊤ : Submodule (𝓞 K) ↥L)) :
    ∃ y ∈ I, h (w : V) (x : V) = algebraMap (𝓞 K) K y := by
  refine Submodule.smul_induction_on hx (fun r hr m _ => ?_) (fun x y hx hy => ?_)
  · obtain ⟨o, ho⟩ := Submodule.mem_one.mp (hLi (w : V) w.2 (m : V) m.2)
    refine ⟨r * o, Ideal.mul_mem_right _ _ hr, ?_⟩
    rw [Submodule.coe_smul, ← algebraMap_smul K r (m : V), map_smul, smul_eq_mul, map_mul, ho]
  · obtain ⟨u, hu, hu'⟩ := hx
    obtain ⟨v, hv, hv'⟩ := hy
    exact ⟨u + v, Ideal.add_mem _ hu hv, by rw [Submodule.coe_add, map_add, hu', hv', map_add]⟩

/- English proof (translation)
Use `Submodule.smul_induction_on hx (fun r hr m _ => ?_) (fun x y hx hy => ?_)` and prove the remaining obligations. Take `⟨o, ho⟩` from `Submodule.mem_one.mp (hLi (m : V) m.2 (w : V) w.2)`. Use `⟨conjO K r * o, Ideal.mul_mem_right _ _ (idealPowerSpanBounds.conjO_mem_pow hF 𝔭 k r hr), ?_⟩` and prove the remaining obligations. Rewrite using `[Submodule.coe_smul, ← algebraMap_smul K r (m : V), LinearMap.map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul, map_mul, ho]`. Apply the tactic sequence `congr 1 <;> simp [conjO]`.

Take `⟨u, hu, hu'⟩` from `hx`. Take `⟨v, hv, hv'⟩` from `hy`. Conclude with `⟨u + v, Ideal.add_mem _ hu hv, by`. Rewrite using `[Submodule.coe_add, map_add, LinearMap.add_apply, hu', hv', map_add]⟩`.
-/
private theorem exists_mem_extP_pow_form_eq_of_mem_extP_pow_smul (hF : IsFixF K F) {h : V →ₗ⋆[K] V →ₗ[K] K} {L : Submodule (𝓞 K) V}
    (hLi : Formalism.HermitianLatticesTheory.IsIntegralLat h L) (𝔭 : Ideal (𝓞 F)) (k : ℕ) (w x : ↥L)
    (hx : x ∈ ((extP K 𝔭) ^ k • ⊤ : Submodule (𝓞 K) ↥L)) :
    ∃ y ∈ extP K 𝔭 ^ k, h (x : V) (w : V) = algebraMap (𝓞 K) K y := by
  refine Submodule.smul_induction_on hx (fun r hr m _ => ?_) (fun x y hx hy => ?_)
  · obtain ⟨o, ho⟩ := Submodule.mem_one.mp (hLi (m : V) m.2 (w : V) w.2)
    refine ⟨conjO K r * o, Ideal.mul_mem_right _ _ (idealPowerSpanBounds.conjO_mem_pow hF 𝔭 k r hr), ?_⟩
    rw [Submodule.coe_smul, ← algebraMap_smul K r (m : V), LinearMap.map_smulₛₗ, LinearMap.smul_apply,
      smul_eq_mul, map_mul, ho]
    congr 1 <;> simp [conjO]
  · obtain ⟨u, hu, hu'⟩ := hx
    obtain ⟨v, hv, hv'⟩ := hy
    exact ⟨u + v, Ideal.add_mem _ hu hv, by
      rw [Submodule.coe_add, map_add, LinearMap.add_apply, hu', hv', map_add]⟩

/- English proof (translation)
Establish `hint : ∀ y : ↥L, ∃ o : 𝓞 K, h (y : V) (y : V) = algebraMap (𝓞 K) K o` using `fun y =>`. Set `⟨o, ho⟩` to `Submodule.mem_one.mp (hLi (y : V) y.2 (y : V) y.2)`. Use the proof step `⟨o, ho.symm⟩`. Establish `hn : ∀ m : 𝓞 F, algebraMap F K (m : F) = algebraMap (𝓞 K) K (ι m)` using `fun m => rfl`. Take `⟨o₀, ho₀⟩` from `hint y₀`.

Establish `ho₀' : o₀ = ι n₀` using `IsFractionRing.injective (𝓞 K) K (by rw [← ho₀, h₀, hn])`. Establish `hcong : ∀ y : ↥L, (Submodule.Quotient.mk y : ↥L ⧸ ((extP K 𝔭) ^ k • ⊤ : Submodule (𝓞 K) ↥L)) = Submodule.Quotient.mk y₀ → ∀ o : 𝓞 K, h (y : V) (y : V) = algebraMap (𝓞 K) K o → Ideal.Quotient.mk (extP K 𝔭 ^ k) o = Ideal.Quotient.mk (extP K 𝔭 ^ k) o₀`. Introduce `y hy o ho`. Rewrite `hy` using `[Submodule.Quotient.eq]`. Take `⟨u1, hu1, he1⟩` from `exists_mem_ideal_form_eq_of_mem_ideal_smul hLi (extP K 𝔭 ^ k) y₀ (y - y₀) hy`.

Take `⟨u2, hu2, he2⟩` from `exists_mem_extP_pow_form_eq_of_mem_extP_pow_smul hF hLi 𝔭 k y₀ (y - y₀) hy`. Take `⟨u3, hu3, he3⟩` from `exists_mem_ideal_form_eq_of_mem_ideal_smul hLi (extP K 𝔭 ^ k) (y - y₀) (y - y₀) hy`. Establish `hyx : y = y₀ + (y - y₀)` using `by abel`. Establish `hsum : o = o₀ + u1 + u2 + u3`. Apply `IsFractionRing.injective (𝓞 K) K` to reduce the goal to its premises.

Rewrite using `[← ho, hyx]`. Simplify using `only [Submodule.coe_add, map_add, LinearMap.add_apply]`. Rewrite using `[he1, he2, he3, ← ho₀]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[Ideal.Quotient.eq, hsum, show o₀ + u1 + u2 + u3 - o₀ = u1 + u2 + u3 by ring]`.

Conclude with `Ideal.add_mem _ (Ideal.add_mem _ hu1 hu2) hu3`. Establish `key : ∀ o : 𝓞 K, Ideal.Quotient.mk (extP K 𝔭 ^ k) o = Ideal.Quotient.mk (extP K 𝔭 ^ k) o₀ → (CongrP 𝔭 k (algebraMap (𝓞 K) K o) (algebraMap F K (n : F)) ↔ n₀ - n ∈ 𝔭 ^ k)`. Introduce `o hoo`. Rewrite using `[hn, integralBasisSpans.congrP_int h𝔭, hoo, ho₀', Ideal.Quotient.eq, ← map_sub, ← MeanB.comap_extP_pow (K := K) 𝔭 k, Ideal.mem_comap]`. Prove the components needed by the constructor for the conclusion.

Introduce and unpack `⟨y, hy, hc⟩`. Take `⟨o, ho⟩` from `hint y`. Rewrite `hc` using `[ho]`. Conclude with `(key o (hcong y hy o ho)).mp hc`. Introduce `hmem`.

Use `⟨y₀, rfl, ?_⟩` and prove the remaining obligations. Rewrite using `[ho₀]`. Conclude with `(key o₀ rfl).mpr hmem`.
-/
theorem nk_iff (hF : IsFixF K F) {h : V →ₗ⋆[K] V →ₗ[K] K} (hs : h.IsSymm) {L : Submodule (𝓞 K) V}
    (hLi : Formalism.HermitianLatticesTheory.IsIntegralLat h L) {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) (k : ℕ) (n : 𝓞 F)
    (y₀ : ↥L) (n₀ : 𝓞 F) (h₀ : h (y₀ : V) (y₀ : V) = algebraMap F K (n₀ : F)) :
    (∃ y : ↥L, (Submodule.Quotient.mk y : ↥L ⧸ ((extP K 𝔭) ^ k • ⊤ : Submodule (𝓞 K) ↥L)) =
        Submodule.Quotient.mk y₀ ∧ CongrP 𝔭 k (h (y : V) (y : V)) (algebraMap F K (n : F))) ↔
      n₀ - n ∈ 𝔭 ^ k := by
  have hint : ∀ y : ↥L, ∃ o : 𝓞 K, h (y : V) (y : V) = algebraMap (𝓞 K) K o := fun y =>
    let ⟨o, ho⟩ := Submodule.mem_one.mp (hLi (y : V) y.2 (y : V) y.2)
    ⟨o, ho.symm⟩
  have hn : ∀ m : 𝓞 F, algebraMap F K (m : F) = algebraMap (𝓞 K) K (ι m) := fun m => rfl
  obtain ⟨o₀, ho₀⟩ := hint y₀
  have ho₀' : o₀ = ι n₀ := IsFractionRing.injective (𝓞 K) K (by rw [← ho₀, h₀, hn])
  have hcong : ∀ y : ↥L, (Submodule.Quotient.mk y : ↥L ⧸ ((extP K 𝔭) ^ k • ⊤ : Submodule (𝓞 K) ↥L)) =
      Submodule.Quotient.mk y₀ → ∀ o : 𝓞 K, h (y : V) (y : V) = algebraMap (𝓞 K) K o →
      Ideal.Quotient.mk (extP K 𝔭 ^ k) o = Ideal.Quotient.mk (extP K 𝔭 ^ k) o₀ := by
    intro y hy o ho
    rw [Submodule.Quotient.eq] at hy
    obtain ⟨u1, hu1, he1⟩ := exists_mem_ideal_form_eq_of_mem_ideal_smul hLi (extP K 𝔭 ^ k) y₀ (y - y₀) hy
    obtain ⟨u2, hu2, he2⟩ := exists_mem_extP_pow_form_eq_of_mem_extP_pow_smul hF hLi 𝔭 k y₀ (y - y₀) hy
    obtain ⟨u3, hu3, he3⟩ := exists_mem_ideal_form_eq_of_mem_ideal_smul hLi (extP K 𝔭 ^ k) (y - y₀) (y - y₀) hy
    have hyx : y = y₀ + (y - y₀) := by abel
    have hsum : o = o₀ + u1 + u2 + u3 := by
      apply IsFractionRing.injective (𝓞 K) K
      rw [← ho, hyx]
      simp only [Submodule.coe_add, map_add, LinearMap.add_apply]
      rw [he1, he2, he3, ← ho₀]
      ring
    rw [Ideal.Quotient.eq, hsum, show o₀ + u1 + u2 + u3 - o₀ = u1 + u2 + u3 by ring]
    exact Ideal.add_mem _ (Ideal.add_mem _ hu1 hu2) hu3
  have key : ∀ o : 𝓞 K, Ideal.Quotient.mk (extP K 𝔭 ^ k) o = Ideal.Quotient.mk (extP K 𝔭 ^ k) o₀ →
      (CongrP 𝔭 k (algebraMap (𝓞 K) K o) (algebraMap F K (n : F)) ↔ n₀ - n ∈ 𝔭 ^ k) := by
    intro o hoo
    rw [hn, integralBasisSpans.congrP_int h𝔭, hoo, ho₀', Ideal.Quotient.eq, ← map_sub,
      ← MeanB.comap_extP_pow (K := K) 𝔭 k, Ideal.mem_comap]
  constructor
  · rintro ⟨y, hy, hc⟩
    obtain ⟨o, ho⟩ := hint y
    rw [ho] at hc
    exact (key o (hcong y hy o ho)).mp hc
  · intro hmem
    refine ⟨y₀, rfl, ?_⟩
    rw [ho₀]
    exact (key o₀ rfl).mpr hmem

section Frame

variable {h : V →ₗ⋆[K] V →ₗ[K] K} {L : Submodule (𝓞 K) V} {m : ℕ} (z : Fin m → ↥L) (g : Fin m → 𝓞 K)

def lin (a : Fin m → 𝓞 K) : ↥L := ∑ i, a i • z i

/- English proof (translation)
Simplify using `only [lin, ← Finset.sum_sub_distrib, Pi.sub_apply, sub_smul]`.
-/
theorem lin_sub (a b : Fin m → 𝓞 K) : lin z a - lin z b = lin z (a - b) := by
  simp only [lin, ← Finset.sum_sub_distrib, Pi.sub_apply, sub_smul]

/- English proof (translation)
Simplify using `[lin]`.
-/
theorem coe_lin (a : Fin m → 𝓞 K) : ((lin z a : ↥L) : V) = ∑ i, a i • (z i : V) := by
  simp [lin]

variable {z g}

/- English proof (translation)
Rewrite using `[coe_lin, map_sum, Finset.sum_eq_single j]`. Rewrite using `[← algebraMap_smul K (c j) (z j : V), map_smul, hzg, smul_eq_mul, map_mul]`. Introduce `i _ hij`. Rewrite using `[← algebraMap_smul K (c i) (z i : V), map_smul, hzo j i (Ne.symm hij), smul_zero]`. Simplify using the standard rewrite rules.
-/
theorem form_right (hzo : ∀ i j, i ≠ j → h (z i : V) (z j : V) = 0)
    (hzg : ∀ i, h (z i : V) (z i : V) = algebraMap (𝓞 K) K (g i)) (j : Fin m) (c : Fin m → 𝓞 K) :
    h (z j : V) (lin z c : V) = algebraMap (𝓞 K) K (c j * g j) := by
  rw [coe_lin, map_sum, Finset.sum_eq_single j]
  · rw [← algebraMap_smul K (c j) (z j : V), map_smul, hzg, smul_eq_mul, map_mul]
  · intro i _ hij
    rw [← algebraMap_smul K (c i) (z i : V), map_smul, hzo j i (Ne.symm hij), smul_zero]
  · simp

/- English proof (translation)
Use `nth_rewrite 1 [coe_lin]`. Rewrite using `[map_sum, LinearMap.sum_apply, map_sum]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[← algebraMap_smul K (c i) (z i : V), LinearMap.map_smulₛₗ, LinearMap.smul_apply, form_right hzo hzg, smul_eq_mul, map_mul, map_mul, map_mul, ← mul_assoc]`. Apply the tactic sequence `congr 2 <;> simp [conjO]`.
-/
theorem form_lin (hzo : ∀ i j, i ≠ j → h (z i : V) (z j : V) = 0)
    (hzg : ∀ i, h (z i : V) (z i : V) = algebraMap (𝓞 K) K (g i)) (c : Fin m → 𝓞 K) :
    h (lin z c : V) (lin z c : V) = algebraMap (𝓞 K) K (∑ i, conjO K (c i) * c i * g i) := by
  nth_rewrite 1 [coe_lin]
  rw [map_sum, LinearMap.sum_apply, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← algebraMap_smul K (c i) (z i : V), LinearMap.map_smulₛₗ, LinearMap.smul_apply,
    form_right hzo hzg, smul_eq_mul, map_mul, map_mul, map_mul, ← mul_assoc]
  congr 2 <;> simp [conjO]

/- English proof (translation)
Rewrite using `[Submodule.Quotient.eq, lin_sub]`. Prove the components needed by the constructor for the conclusion. Introduce `hmem i`. Establish `key : ∀ x : ↥L, x ∈ ((extP K 𝔭) ^ k • ⊤ : Submodule (𝓞 K) ↥L) → ∃ y ∈ extP K 𝔭 ^ k, h (z i : V) (x : V) = algebraMap (𝓞 K) K y`. Introduce `x hx`.

Use `Submodule.smul_induction_on hx (fun r hr m _ => ?_) (fun x y hx hy => ?_)` and prove the remaining obligations. Take `⟨o, ho⟩` from `Submodule.mem_one.mp (hLi (z i : V) (z i).2 (m : V) m.2)`. Use `⟨r * o, Ideal.mul_mem_right _ _ hr, ?_⟩` and prove the remaining obligations. Rewrite using `[Submodule.coe_smul, ← algebraMap_smul K r (m : V), map_smul, smul_eq_mul, map_mul, ho]`. Take `⟨u, hu, hu'⟩` from `hx`.

Take `⟨w, hw, hw'⟩` from `hy`. Conclude with `⟨u + w, Ideal.add_mem _ hu hw, by rw [Submodule.coe_add, map_add, hu', hw', map_add]⟩`. Take `⟨y, hy, hyeq⟩` from `key _ hmem`. Rewrite `hyeq` using `[form_right hzo hzg]`. Establish `h1 : (a - b) i * g i ∈ extP K 𝔭 ^ k`.

Rewrite using `[IsFractionRing.injective (𝓞 K) K hyeq]`. Conclude with `hy`. Establish `h2 : (a - b) i * (g i - 1) ∈ extP K 𝔭 ^ k` using `Ideal.mul_mem_left _ _ (hg1 i)`. Establish `h3 : a i - b i = (a - b) i * g i - (a - b) i * (g i - 1)`. Simplify using `only [Pi.sub_apply]`.

Expand and normalize the polynomial expressions, which then agree. Rewrite using `[h3]`. Conclude with `Ideal.sub_mem _ h1 h2`. Introduce `hab`. Conclude with `Submodule.sum_mem _ fun i _ => Submodule.smul_mem_smul (hab i) Submodule.mem_top`.
-/
theorem mk_lin_eq_iff (hLi : Formalism.HermitianLatticesTheory.IsIntegralLat h L) (𝔭 : Ideal (𝓞 F)) (k : ℕ)
    (hzo : ∀ i j, i ≠ j → h (z i : V) (z j : V) = 0)
    (hzg : ∀ i, h (z i : V) (z i : V) = algebraMap (𝓞 K) K (g i))
    (hg1 : ∀ i, g i - 1 ∈ extP K 𝔭 ^ k) (a b : Fin m → 𝓞 K) :
    (Submodule.Quotient.mk (lin z a) : ↥L ⧸ ((extP K 𝔭) ^ k • ⊤ : Submodule (𝓞 K) ↥L)) =
      Submodule.Quotient.mk (lin z b) ↔ ∀ i, a i - b i ∈ extP K 𝔭 ^ k := by
  rw [Submodule.Quotient.eq, lin_sub]
  constructor
  · intro hmem i
    have key : ∀ x : ↥L, x ∈ ((extP K 𝔭) ^ k • ⊤ : Submodule (𝓞 K) ↥L) →
        ∃ y ∈ extP K 𝔭 ^ k, h (z i : V) (x : V) = algebraMap (𝓞 K) K y := by
      intro x hx
      refine Submodule.smul_induction_on hx (fun r hr m _ => ?_) (fun x y hx hy => ?_)
      · obtain ⟨o, ho⟩ := Submodule.mem_one.mp (hLi (z i : V) (z i).2 (m : V) m.2)
        refine ⟨r * o, Ideal.mul_mem_right _ _ hr, ?_⟩
        rw [Submodule.coe_smul, ← algebraMap_smul K r (m : V), map_smul, smul_eq_mul, map_mul, ho]
      · obtain ⟨u, hu, hu'⟩ := hx
        obtain ⟨w, hw, hw'⟩ := hy
        exact ⟨u + w, Ideal.add_mem _ hu hw, by rw [Submodule.coe_add, map_add, hu', hw', map_add]⟩
    obtain ⟨y, hy, hyeq⟩ := key _ hmem
    rw [form_right hzo hzg] at hyeq
    have h1 : (a - b) i * g i ∈ extP K 𝔭 ^ k := by
      rw [IsFractionRing.injective (𝓞 K) K hyeq]
      exact hy
    have h2 : (a - b) i * (g i - 1) ∈ extP K 𝔭 ^ k := Ideal.mul_mem_left _ _ (hg1 i)
    have h3 : a i - b i = (a - b) i * g i - (a - b) i * (g i - 1) := by
      simp only [Pi.sub_apply]
      ring
    rw [h3]
    exact Ideal.sub_mem _ h1 h2
  · intro hab
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem_smul (hab i) Submodule.mem_top

end Frame

/- English proof (translation)
Rewrite `hy` using `[Submodule.Quotient.eq]`. Take `⟨u1, hu1, he1⟩` from `exists_mem_ideal_form_eq_of_mem_ideal_smul hLi (extP K 𝔭 ^ k) y₀ (y - y₀) hy`. Take `⟨u2, hu2, he2⟩` from `exists_mem_extP_pow_form_eq_of_mem_extP_pow_smul hF hLi 𝔭 k y₀ (y - y₀) hy`. Take `⟨u3, hu3, he3⟩` from `exists_mem_ideal_form_eq_of_mem_ideal_smul hLi (extP K 𝔭 ^ k) (y - y₀) (y - y₀) hy`. Establish `hyx : y = y₀ + (y - y₀)` using `by abel`.

Establish `hsum : o = o₀ + u1 + u2 + u3`. Apply `IsFractionRing.injective (𝓞 K) K` to reduce the goal to its premises. Rewrite using `[← ho, hyx]`. Simplify using `only [Submodule.coe_add, map_add, LinearMap.add_apply]`. Rewrite using `[he1, he2, he3, ← ho₀]`.

Expand and normalize the polynomial expressions, which then agree. Rewrite using `[Ideal.Quotient.eq, hsum, show o₀ + u1 + u2 + u3 - o₀ = u1 + u2 + u3 by ring]`. Conclude with `Ideal.add_mem _ (Ideal.add_mem _ hu1 hu2) hu3`.
-/
private theorem quotient_norm_congr_of_quotient_eq (hF : IsFixF K F) {h : V →ₗ⋆[K] V →ₗ[K] K} {L : Submodule (𝓞 K) V}
    (hLi : Formalism.HermitianLatticesTheory.IsIntegralLat h L) (𝔭 : Ideal (𝓞 F)) (k : ℕ) (y y₀ : ↥L)
    (hy : (Submodule.Quotient.mk y : ↥L ⧸ ((extP K 𝔭) ^ k • ⊤ : Submodule (𝓞 K) ↥L)) =
      Submodule.Quotient.mk y₀)
    (o o₀ : 𝓞 K) (ho : h (y : V) (y : V) = algebraMap (𝓞 K) K o)
    (ho₀ : h (y₀ : V) (y₀ : V) = algebraMap (𝓞 K) K o₀) :
    Ideal.Quotient.mk (extP K 𝔭 ^ k) o = Ideal.Quotient.mk (extP K 𝔭 ^ k) o₀ := by
  rw [Submodule.Quotient.eq] at hy
  obtain ⟨u1, hu1, he1⟩ := exists_mem_ideal_form_eq_of_mem_ideal_smul hLi (extP K 𝔭 ^ k) y₀ (y - y₀) hy
  obtain ⟨u2, hu2, he2⟩ := exists_mem_extP_pow_form_eq_of_mem_extP_pow_smul hF hLi 𝔭 k y₀ (y - y₀) hy
  obtain ⟨u3, hu3, he3⟩ := exists_mem_ideal_form_eq_of_mem_ideal_smul hLi (extP K 𝔭 ^ k) (y - y₀) (y - y₀) hy
  have hyx : y = y₀ + (y - y₀) := by abel
  have hsum : o = o₀ + u1 + u2 + u3 := by
    apply IsFractionRing.injective (𝓞 K) K
    rw [← ho, hyx]
    simp only [Submodule.coe_add, map_add, LinearMap.add_apply]
    rw [he1, he2, he3, ← ho₀]
    ring
  rw [Ideal.Quotient.eq, hsum, show o₀ + u1 + u2 + u3 - o₀ = u1 + u2 + u3 by ring]
  exact Ideal.add_mem _ (Ideal.add_mem _ hu1 hu2) hu3

/- English proof (translation)
Take `⟨z, g, hzo, hzg, hg1⟩` from `exists_frame hK hF hs hd hL hLi h𝔭 hv hk`. Establish `hint : ∀ y : ↥L, ∃ o : 𝓞 K, h (y : V) (y : V) = algebraMap (𝓞 K) K o` using `fun y =>`. Set `⟨o, ho⟩` to `Submodule.mem_one.mp (hLi (y : V) y.2 (y : V) y.2)`. Use the proof step `⟨o, ho.symm⟩`. Establish `hn : algebraMap F K (n : F) = algebraMap (𝓞 K) K (ι n)` using `rfl`.

Set `lift : (Fin (finrank K V) → AQ K 𝔭 k) → Fin (finrank K V) → 𝓞 K` to `fun x i => (Ideal.Quotient.mk_surjective (x i)).choose`. Establish `hlift : ∀ x i, Ideal.Quotient.mk (extP K 𝔭 ^ k) (lift x i) = x i` using `fun x i => (Ideal.Quotient.mk_surjective (x i)).choose_spec`. Set `Φ : (Fin (finrank K V) → AQ K 𝔭 k) → ↥L ⧸ ((extP K 𝔭) ^ k • ⊤ : Submodule (𝓞 K) ↥L)` to `fun x => Submodule.Quotient.mk (lin z (lift x))`. Establish `hinj : Function.Injective Φ`. Introduce `x x' hxx`.

Establish `hd` using `(mk_lin_eq_iff hLi 𝔭 k hzo hzg hg1 (lift x) (lift x')).mp hxx`. Use function extensionality and compare the values at `i`. Rewrite using `[← hlift x i, ← hlift x' i, Ideal.Quotient.eq]`. Conclude with `hd i`. Use `haveI : Fact (IsFixF K F) := ⟨hF⟩`.

Use `haveI : Finite (Fin (finrank K V) → AQ K 𝔭 k) := vectorCountBounds.finite_vec h𝔭 k`. Establish `hcard : Nat.card (↥L ⧸ ((extP K 𝔭) ^ k • ⊤ : Submodule (𝓞 K) ↥L)) = Nat.card (Fin (finrank K V) → AQ K 𝔭 k)`. Rewrite using `[MeanB.card_quot_extP hK hF hL h𝔭 k, vectorCountBounds.card_vec hK h𝔭 k, Fintype.card_fin]`. Put the polynomial expressions in normal form. Use `haveI : Finite (↥L ⧸ ((extP K 𝔭) ^ k • ⊤ : Submodule (𝓞 K) ↥L)) := Nat.finite_of_card_ne_zero (by rw [hcard]; exact Nat.card_pos.ne')`.

Establish `hbij : Function.Bijective Φ` using `hinj.bijective_of_nat_card_le hcard.le`. Establish `hsum : ∀ x, Ideal.Quotient.mk (extP K 𝔭 ^ k) (∑ i, conjO K (lift x i) * lift x i * g i) = ∑ i, sg hF 𝔭 k (x i) * x i`. Introduce `x`. Rewrite using `[map_sum]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations.

Establish `hg : Ideal.Quotient.mk (extP K 𝔭 ^ k) (g i) = 1`. Rewrite using `[← map_one (Ideal.Quotient.mk (extP K 𝔭 ^ k)), Ideal.Quotient.eq]`. Conclude with `hg1 i`. Rewrite using `[map_mul, map_mul, hg, mul_one]`. Use `conv_rhs => rw [← hlift x i]`.

Unfold `sg`. Rewrite using `[NormLifting.conjQ_mk]`. Unfold `nkCount cnt`. Use `(Nat.card_congr ((Equiv.ofBijective Φ hbij).subtypeEquiv (fun x => ?_))).symm` and prove the remaining obligations. Use `show _ ↔ ∃ y : ↥L, Submodule.Quotient.mk y = Φ x ∧ _`.

Prove the components needed by the constructor for the conclusion. Introduce `hx`. Use `⟨lin z (lift x), rfl, ?_⟩` and prove the remaining obligations. Rewrite using `[form_lin hzo hzg, hn, integralBasisSpans.congrP_int h𝔭, hsum x, hx]`. Introduce and unpack `⟨y, hy, hc⟩`.

Take `⟨o, ho⟩` from `hint y`. Establish `hcg` using `quotient_norm_congr_of_quotient_eq hF hLi 𝔭 k y (lin z (lift x)) hy o _ ho (form_lin hzo hzg (lift x))`. Rewrite `hc` using `[ho, hn, integralBasisSpans.congrP_int h𝔭, hcg, hsum x]`. Conclude with `hc`.
-/
theorem nkCount_eq_cnt (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F)
    {h : V →ₗ⋆[K] V →ₗ[K] K} (hs : h.IsSymm) (hd : IsTotPosDef h) {L : Submodule (𝓞 K) V}
    (hL : Submodule.IsLattice K L) (hLi : Formalism.HermitianLatticesTheory.IsIntegralLat h L) {𝔭 : Ideal (𝓞 F)}
    (h𝔭 : 𝔭.IsMaximal) (hv : vd h L 𝔭 = 0) {k : ℕ} (hk : 1 ≤ k) (n : 𝓞 F) :
    nkCount h L 𝔭 k n = cnt hF 𝔭 k (finrank K V) (ι n) := by
  obtain ⟨z, g, hzo, hzg, hg1⟩ := exists_frame hK hF hs hd hL hLi h𝔭 hv hk
  have hint : ∀ y : ↥L, ∃ o : 𝓞 K, h (y : V) (y : V) = algebraMap (𝓞 K) K o := fun y =>
    let ⟨o, ho⟩ := Submodule.mem_one.mp (hLi (y : V) y.2 (y : V) y.2)
    ⟨o, ho.symm⟩
  have hn : algebraMap F K (n : F) = algebraMap (𝓞 K) K (ι n) := rfl
  let lift : (Fin (finrank K V) → AQ K 𝔭 k) → Fin (finrank K V) → 𝓞 K :=
    fun x i => (Ideal.Quotient.mk_surjective (x i)).choose
  have hlift : ∀ x i, Ideal.Quotient.mk (extP K 𝔭 ^ k) (lift x i) = x i :=
    fun x i => (Ideal.Quotient.mk_surjective (x i)).choose_spec
  let Φ : (Fin (finrank K V) → AQ K 𝔭 k) → ↥L ⧸ ((extP K 𝔭) ^ k • ⊤ : Submodule (𝓞 K) ↥L) :=
    fun x => Submodule.Quotient.mk (lin z (lift x))
  have hinj : Function.Injective Φ := by
    intro x x' hxx
    have hd := (mk_lin_eq_iff hLi 𝔭 k hzo hzg hg1 (lift x) (lift x')).mp hxx
    funext i
    rw [← hlift x i, ← hlift x' i, Ideal.Quotient.eq]
    exact hd i
  haveI : Fact (IsFixF K F) := ⟨hF⟩
  haveI : Finite (Fin (finrank K V) → AQ K 𝔭 k) := vectorCountBounds.finite_vec h𝔭 k
  have hcard : Nat.card (↥L ⧸ ((extP K 𝔭) ^ k • ⊤ : Submodule (𝓞 K) ↥L)) =
      Nat.card (Fin (finrank K V) → AQ K 𝔭 k) := by
    rw [MeanB.card_quot_extP hK hF hL h𝔭 k, vectorCountBounds.card_vec hK h𝔭 k, Fintype.card_fin]
    ring_nf
  haveI : Finite (↥L ⧸ ((extP K 𝔭) ^ k • ⊤ : Submodule (𝓞 K) ↥L)) :=
    Nat.finite_of_card_ne_zero (by rw [hcard]; exact Nat.card_pos.ne')
  have hbij : Function.Bijective Φ := hinj.bijective_of_nat_card_le hcard.le
  have hsum : ∀ x, Ideal.Quotient.mk (extP K 𝔭 ^ k) (∑ i, conjO K (lift x i) * lift x i * g i) =
      ∑ i, sg hF 𝔭 k (x i) * x i := by
    intro x
    rw [map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    have hg : Ideal.Quotient.mk (extP K 𝔭 ^ k) (g i) = 1 := by
      rw [← map_one (Ideal.Quotient.mk (extP K 𝔭 ^ k)), Ideal.Quotient.eq]
      exact hg1 i
    rw [map_mul, map_mul, hg, mul_one]
    conv_rhs => rw [← hlift x i]
    unfold sg
    rw [NormLifting.conjQ_mk]
  unfold nkCount cnt
  refine (Nat.card_congr ((Equiv.ofBijective Φ hbij).subtypeEquiv (fun x => ?_))).symm
  show _ ↔ ∃ y : ↥L, Submodule.Quotient.mk y = Φ x ∧ _
  constructor
  · intro hx
    refine ⟨lin z (lift x), rfl, ?_⟩
    rw [form_lin hzo hzg, hn, integralBasisSpans.congrP_int h𝔭, hsum x, hx]
  · rintro ⟨y, hy, hc⟩
    obtain ⟨o, ho⟩ := hint y
    have hcg := quotient_norm_congr_of_quotient_eq hF hLi 𝔭 k y (lin z (lift x)) hy o _ ho (form_lin hzo hzg (lift x))
    rw [ho, hn, integralBasisSpans.congrP_int h𝔭, hcg, hsum x] at hc
    exact hc

end Formalism.HermitianLattices.Ext.L3.unitaryAbsoluteValueBounds

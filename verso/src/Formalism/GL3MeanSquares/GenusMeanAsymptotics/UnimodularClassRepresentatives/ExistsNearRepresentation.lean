import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.CongrPIffInI
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.ExistsSmulMem

open NumberField Module

noncomputable section

namespace Formalism.HermitianLattices.Ext.L3.Cell

open LocalSpans idealPowerSpanBounds localizedQuotients WCA

variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
variable {V : Type} [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]

local notation "ι" => algebraMap (𝓞 F) (𝓞 K)
local notation "κ" => algebraMap (𝓞 K) K

variable {𝔭 : Ideal (𝓞 F)} {A : Submodule (𝓞 K) V}

/- English proof (translation)
The claim follows from `hs.eq w w`.
-/
theorem form_self_star {h : V →ₗ⋆[K] V →ₗ[K] K} (hs : h.IsSymm) (w : V) : star (h w w) = h w w :=
  hs.eq w w

/- English proof (translation)
Use `set w := x - b with hw`. Establish `hx : x = w + b` using `by rw [hw]; abel`. Establish `e1 : star (h b w) = h w b` using `hs.eq b w`. Establish `e2 : star (h w b) = h b w` using `hs.eq w b`. Establish `e3 : star (h w w) = h w w` using `hs.eq w w`.

Use `set d := h w w with hdd`. Prove the components needed by the constructor for the conclusion. Simplify using `only [map_sub, LinearMap.sub_apply, LinearMap.map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul, starRingEnd_apply, RingHom.id_apply, star_mul', star_add, star_inv₀, e1, e2, e3, ← hdd]`. Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree.

Establish `e4 : h x x - h b b = d + (h b w + h w b)`. Rewrite using `[hx]`. Simplify using `only [map_add, LinearMap.add_apply, ← hdd]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e4]`.

Establish `e5 : d⁻¹ * (d + (h b w + h w b)) = 1 + (h b w + h w b) * d⁻¹`. Clear the denominators using the available nonvanishing facts. Rewrite using `[e5, add_smul, one_smul]`. Use `conv_lhs => rw [hx]`. Normalize the expressions using the abelian group laws.
-/
theorem exact_step {h : V →ₗ⋆[K] V →ₗ[K] K} (hs : h.IsSymm) {b x : V}
    (hd : h (x - b) (x - b) ≠ 0) :
    h (b - ((h b (x - b) + h (x - b) b) * (h (x - b) (x - b))⁻¹) • (x - b))
        (b - ((h b (x - b) + h (x - b) b) * (h (x - b) (x - b))⁻¹) • (x - b)) = h b b ∧
      (b - ((h b (x - b) + h (x - b) b) * (h (x - b) (x - b))⁻¹) • (x - b)) - x =
        -(((h (x - b) (x - b))⁻¹ * (h x x - h b b)) • (x - b)) := by
  set w := x - b with hw
  have hx : x = w + b := by rw [hw]; abel
  have e1 : star (h b w) = h w b := hs.eq b w
  have e2 : star (h w b) = h b w := hs.eq w b
  have e3 : star (h w w) = h w w := hs.eq w w
  set d := h w w with hdd
  constructor
  · simp only [map_sub, LinearMap.sub_apply, LinearMap.map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul,
      starRingEnd_apply, RingHom.id_apply, star_mul', star_add, star_inv₀, e1, e2, e3, ← hdd]
    field_simp
    ring
  · have e4 : h x x - h b b = d + (h b w + h w b) := by
      rw [hx]
      simp only [map_add, LinearMap.add_apply, ← hdd]
      ring
    rw [e4]
    have e5 : d⁻¹ * (d + (h b w + h w b)) = 1 + (h b w + h w b) * d⁻¹ := by
      field_simp
    rw [e5, add_smul, one_smul]
    conv_lhs => rw [hx]
    abel

/- English proof (translation)
Establish `hp` using `h𝔭.isPrime`. Establish `hd : h (x - b) (x - b) ≠ 0`. Introduce `h0`. Apply `hD` to reduce the goal to its premises. Rewrite using `[h0, mul_zero]`.

Conclude with `InI.zero hp _`. Establish `hs0 : κ (ι s) ≠ 0`. Introduce `h0`. Apply `hD` to reduce the goal to its premises. Rewrite using `[map_mul, map_mul, h0, zero_mul, zero_mul]`.

Conclude with `InI.zero hp _`. Take `⟨h1, h2⟩` from `exact_step hs hd`. Use `set y := b - ((h b (x - b) + h (x - b) b) * (h (x - b) (x - b))⁻¹) • (x - b) with hy`. Use `set w := x - b with hw`. Establish `hsw : InL 𝔭 A 0 (ι s • w)`.

Rewrite using `[hw, smul_sub]`. Use `InL.sub hp ?_ ((inL_zero_iff hp).2 (le_locF 𝔭 A hsb))` and prove the remaining obligations. Rewrite using `[← algebraMap_smul K (ι s)]`. Use `InL.smul hp (InI.int hp (ι s)) hx` as an intermediate fact. Rewrite `this` using `[zero_add]`. Then use the resulting hypothesis.

Establish `hDe : h (ι s • w) (ι s • w) = κ (ι (s * s)) * h w w` using `form_smul hF h s s w w`. Establish `hD0 : InI 𝔭 0 (κ (ι (s * s)) * h w w)`. Rewrite using `[← hDe]`. Conclude with `InL.form hp hF hA hsw hsw`. Establish `hDs : star (κ (ι (s * s)) * h w w) = κ (ι (s * s)) * h w w`.

Rewrite using `[← hDe]`. Conclude with `hs.eq _ _`. Establish `h3 : InI 𝔭 (v + k) (κ (ι s) * (h x x - κ (ι n)))`. Use `InI.mul hp (InI.int hp (ι s)) hε` as an intermediate fact. Rewrite `this` using `[zero_add]`. Then use the resulting hypothesis.

Establish `h4` using `InI.divK h𝔭 hF hDs hD0 hD h3`. Establish `h5` using `InL.smul hp h4 hsw`. Rewrite `h5` using `[add_zero]`. Establish `h6 : InL 𝔭 A k (y - x)`. Rewrite using `[h2, hb]`.

Apply `InL.neg` to reduce the goal to its premises. Establish `: ((h w w)⁻¹ * (h x x - κ (ι n))) • w = ((κ (ι (s * s)) * h w w)⁻¹ * (κ (ι s) * (h x x - κ (ι n)))) • ι s • w`. Rewrite using `[← algebraMap_smul K (ι s), smul_smul]`. Use `congr 1`. Rewrite using `[map_mul, map_mul]`.

Clear the denominators using the available nonvanishing facts. Rewrite using `[this]`. Conclude with `h5`. Use `⟨y, ?_, h1.trans hb, h6⟩` and prove the remaining obligations. Establish `: y = x + (y - x)` using `by abel`.

Rewrite using `[this]`. Conclude with `hx.add hp (h6.mono (Nat.zero_le _))`.
-/
theorem exists_near_representation (h𝔭 : 𝔭.IsMaximal) (hF : IsFixF K F) {h : V →ₗ⋆[K] V →ₗ[K] K} (hs : h.IsSymm)
    (hA : Formalism.HermitianLatticesTheory.IsIntegralLat h A) {n s : 𝓞 F} {b : V}
    (hb : h b b = κ (ι n)) (hsb : ι s • b ∈ A) {v k : ℕ} {x : V} (hx : InL 𝔭 A 0 x)
    (hε : InI 𝔭 (v + k) (h x x - κ (ι n)))
    (hD : ¬ InI 𝔭 (v + 1) (κ (ι (s * s)) * h (x - b) (x - b))) :
    ∃ y, InL 𝔭 A 0 y ∧ h y y = κ (ι n) ∧ InL 𝔭 A k (y - x) := by
  have hp := h𝔭.isPrime
  have hd : h (x - b) (x - b) ≠ 0 := by
    intro h0
    apply hD
    rw [h0, mul_zero]
    exact InI.zero hp _
  have hs0 : κ (ι s) ≠ 0 := by
    intro h0
    apply hD
    rw [map_mul, map_mul, h0, zero_mul, zero_mul]
    exact InI.zero hp _
  obtain ⟨h1, h2⟩ := exact_step hs hd
  set y := b - ((h b (x - b) + h (x - b) b) * (h (x - b) (x - b))⁻¹) • (x - b) with hy
  set w := x - b with hw
  have hsw : InL 𝔭 A 0 (ι s • w) := by
    rw [hw, smul_sub]
    refine InL.sub hp ?_ ((inL_zero_iff hp).2 (le_locF 𝔭 A hsb))
    rw [← algebraMap_smul K (ι s)]
    have := InL.smul hp (InI.int hp (ι s)) hx
    rwa [zero_add] at this
  have hDe : h (ι s • w) (ι s • w) = κ (ι (s * s)) * h w w := form_smul hF h s s w w
  have hD0 : InI 𝔭 0 (κ (ι (s * s)) * h w w) := by
    rw [← hDe]
    exact InL.form hp hF hA hsw hsw
  have hDs : star (κ (ι (s * s)) * h w w) = κ (ι (s * s)) * h w w := by
    rw [← hDe]; exact hs.eq _ _
  have h3 : InI 𝔭 (v + k) (κ (ι s) * (h x x - κ (ι n))) := by
    have := InI.mul hp (InI.int hp (ι s)) hε
    rwa [zero_add] at this
  have h4 := InI.divK h𝔭 hF hDs hD0 hD h3
  have h5 := InL.smul hp h4 hsw
  rw [add_zero] at h5
  have h6 : InL 𝔭 A k (y - x) := by
    rw [h2, hb]
    apply InL.neg
    have : ((h w w)⁻¹ * (h x x - κ (ι n))) • w =
        ((κ (ι (s * s)) * h w w)⁻¹ * (κ (ι s) * (h x x - κ (ι n)))) • ι s • w := by
      rw [← algebraMap_smul K (ι s), smul_smul]
      congr 1
      rw [map_mul, map_mul]
      field_simp
    rw [this]
    exact h5
  refine ⟨y, ?_, h1.trans hb, h6⟩
  have : y = x + (y - x) := by abel
  rw [this]
  exact hx.add hp (h6.mono (Nat.zero_le _))

/- English proof (translation)
Take `⟨r, hr, hrv⟩` from `StabilizerLattices.exists_smul_mem hΛ v`. Take `⟨s, hs⟩` from `(conjO_eq_iff_mem_range hF (conjO K r * r)).1 (by`. Rewrite using `[map_mul, conjO_conjO, mul_comm])`. Use `⟨s, ?_, ?_⟩` and prove the remaining obligations. Introduce and unpack `rfl`.

Rewrite `hs` using `[map_zero]`. Break down `mul_eq_zero.1 hs.symm with h0 | h0` into its components or cases. Apply `hr` to reduce the goal to its premises. Rewrite using `[← conjO_conjO r, h0, map_zero]`. Conclude with `hr h0`.

Rewrite using `[hs, mul_smul]`. Conclude with `Λ.smul_mem _ hrv`.
-/
theorem exists_F_smul_mem (hF : IsFixF K F) {Λ : Submodule (𝓞 K) V} (hΛ : Submodule.IsLattice K Λ)
    (v : V) : ∃ s : 𝓞 F, s ≠ 0 ∧ ι s • v ∈ Λ := by
  obtain ⟨r, hr, hrv⟩ := StabilizerLattices.exists_smul_mem hΛ v
  obtain ⟨s, hs⟩ := (conjO_eq_iff_mem_range hF (conjO K r * r)).1 (by
    rw [map_mul, conjO_conjO, mul_comm])
  refine ⟨s, ?_, ?_⟩
  · rintro rfl
    rw [map_zero] at hs
    rcases mul_eq_zero.1 hs.symm with h0 | h0
    · apply hr
      rw [← conjO_conjO r, h0, map_zero]
    · exact hr h0
  · rw [hs, mul_smul]
    exact Λ.smul_mem _ hrv

/- English proof (translation)
Establish `hp` using `h𝔭.isPrime`. Take `⟨b, hb⟩` from `hrep`. Take `⟨s, hs0, hsb⟩` from `exists_F_smul_mem hF hL b`. Establish `hN : 4 * (s * s * n) ≠ 0` using `mul_ne_zero (by norm_num) (mul_ne_zero (mul_ne_zero hs0 hs0) hn)`. Use `⟨vF 𝔭 (4 * (s * s * n)), fun k hk x hx hε => ?_⟩` and prove the remaining obligations.

Use `set v := vF 𝔭 (4 * (s * s * n)) with hv`. Distinguish the cases in `h1 : InI 𝔭 (v + 1) (κ (ι (s * s)) * h (x - b) (x - b))`. Distinguish the cases in `h2 : InI 𝔭 (v + 1) (κ (ι (s * s)) * h (x - -b) (x - -b))`. It suffices to derive a contradiction. Apply `localValuationFiltration.notMem_pow_vF h𝔭 hN` to reduce the goal to its premises.

Rewrite using `[← hv, ← inI_ι (K := K) h𝔭]`. Establish `h3 : InI 𝔭 (v + 1) (κ (ι (2 * (s * s))) * (h x x - κ (ι n)))`. Use `InI.mul hp (InI.int hp (ι (2 * (s * s)))) (hε.mono (by omega : v + 1 ≤ v + k))` as an intermediate fact. Rewrite `this` using `[zero_add]`. Then use the resulting hypothesis. Establish `e : κ (ι (4 * (s * s * n))) = κ (ι (s * s)) * h (x - b) (x - b) + κ (ι (s * s)) * h (x - -b) (x - -b) - κ (ι (2 * (s * s))) * (h x x - κ (ι n))`.

Simplify using `only [map_sub, map_neg, LinearMap.sub_apply, LinearMap.neg_apply, hb, map_mul, map_ofNat]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e]`. Conclude with `(h1.add hp h2).sub hp h3`. Conclude with `exists_near_representation h𝔭 hF hs hA (b := -b) (by simpa using hb) (by rw [smul_neg]; exact A.neg_mem hsb) hx hε h2`.

Conclude with `exists_near_representation h𝔭 hF hs hA hb hsb hx hε h1`.
-/
theorem exists_near (h𝔭 : 𝔭.IsMaximal) (hF : IsFixF K F) {h : V →ₗ⋆[K] V →ₗ[K] K} (hs : h.IsSymm)
    (hL : Submodule.IsLattice K A) (hA : Formalism.HermitianLatticesTheory.IsIntegralLat h A) {n : 𝓞 F} (hn : n ≠ 0)
    (hrep : ∃ b : V, h b b = κ (ι n)) :
    ∃ v : ℕ, ∀ k : ℕ, 1 ≤ k → ∀ x, InL 𝔭 A 0 x → InI 𝔭 (v + k) (h x x - κ (ι n)) →
      ∃ y, InL 𝔭 A 0 y ∧ h y y = κ (ι n) ∧ InL 𝔭 A k (y - x) := by
  have hp := h𝔭.isPrime
  obtain ⟨b, hb⟩ := hrep
  obtain ⟨s, hs0, hsb⟩ := exists_F_smul_mem hF hL b
  have hN : 4 * (s * s * n) ≠ 0 :=
    mul_ne_zero (by norm_num) (mul_ne_zero (mul_ne_zero hs0 hs0) hn)
  refine ⟨vF 𝔭 (4 * (s * s * n)), fun k hk x hx hε => ?_⟩
  set v := vF 𝔭 (4 * (s * s * n)) with hv
  by_cases h1 : InI 𝔭 (v + 1) (κ (ι (s * s)) * h (x - b) (x - b))
  · by_cases h2 : InI 𝔭 (v + 1) (κ (ι (s * s)) * h (x - -b) (x - -b))
    · exfalso
      apply localValuationFiltration.notMem_pow_vF h𝔭 hN
      rw [← hv, ← inI_ι (K := K) h𝔭]
      have h3 : InI 𝔭 (v + 1) (κ (ι (2 * (s * s))) * (h x x - κ (ι n))) := by
        have := InI.mul hp (InI.int hp (ι (2 * (s * s)))) (hε.mono (by omega : v + 1 ≤ v + k))
        rwa [zero_add] at this
      have e : κ (ι (4 * (s * s * n))) = κ (ι (s * s)) * h (x - b) (x - b) +
          κ (ι (s * s)) * h (x - -b) (x - -b) - κ (ι (2 * (s * s))) * (h x x - κ (ι n)) := by
        simp only [map_sub, map_neg, LinearMap.sub_apply, LinearMap.neg_apply, hb, map_mul, map_ofNat]
        ring
      rw [e]
      exact (h1.add hp h2).sub hp h3
    · exact exists_near_representation h𝔭 hF hs hA (b := -b) (by simpa using hb)
        (by rw [smul_neg]; exact A.neg_mem hsb) hx hε h2
  · exact exists_near_representation h𝔭 hF hs hA hb hsb hx hε h1

end Formalism.HermitianLattices.Ext.L3.Cell

import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.CoeCmbSingle

open NumberField Module Matrix

noncomputable section

namespace Formalism.HermitianLattices.Ext.L3.HU

open LocalSpans idealPowerSpanBounds localizedQuotients integralBasisSpans

variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
variable {V : Type} [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
variable {κ : Type} [Fintype κ] [DecidableEq κ]

local notation "ι" => algebraMap (𝓞 F) (𝓞 K)
local notation "jK" => algebraMap (𝓞 K) K

/- English proof (translation)
Conclude with `⟨1, fun h1 => ‹𝔭.IsPrime›.ne_top ((Ideal.eq_top_iff_one _).2 h1), 0, Submodule.zero_mem _, by simp⟩`.
-/
theorem InP.zero {𝔭 : Ideal (𝓞 F)} [𝔭.IsPrime] (k : ℕ) : InP 𝔭 k (0 : K) := by
  exact ⟨1, fun h1 => ‹𝔭.IsPrime›.ne_top ((Ideal.eq_top_iff_one _).2 h1), 0, Submodule.zero_mem _, by simp⟩

/- English proof (translation)
Take `⟨s, hs, y, hy, hya⟩` from `ha`. Take `⟨t, ht, z, hz, hzb⟩` from `hb`. Use `⟨s * t, fun hst => (‹𝔭.IsPrime›.mem_or_mem hst).elim hs ht, ι t * y + ι s * z, Ideal.add_mem _ (Ideal.mul_mem_left _ _ hy) (Ideal.mul_mem_left _ _ hz), ?_⟩` and prove the remaining obligations. Simplify using `only [map_add, map_mul]`. Take the linear combination `(jK (ι t)) * hya + (jK (ι s)) * hzb`.
-/
private theorem inP_add {𝔭 : Ideal (𝓞 F)} [𝔭.IsPrime] {k : ℕ} {a b : K} (ha : InP 𝔭 k a)
    (hb : InP 𝔭 k b) : InP 𝔭 k (a + b) := by
  obtain ⟨s, hs, y, hy, hya⟩ := ha
  obtain ⟨t, ht, z, hz, hzb⟩ := hb
  refine ⟨s * t, fun hst => (‹𝔭.IsPrime›.mem_or_mem hst).elim hs ht, ι t * y + ι s * z,
    Ideal.add_mem _ (Ideal.mul_mem_left _ _ hy) (Ideal.mul_mem_left _ _ hz), ?_⟩
  simp only [map_add, map_mul]
  linear_combination (jK (ι t)) * hya + (jK (ι s)) * hzb

/- English proof (translation)
Conclude with `Finset.sum_induction f (InP 𝔭 k) (fun a b ha hb => inP_add ha hb) (InP.zero k) hf`.
-/
theorem InP.sum {𝔭 : Ideal (𝓞 F)} [𝔭.IsPrime] {k : ℕ} {α : Type*} (s : Finset α) (f : α → K)
    (hf : ∀ i ∈ s, InP 𝔭 k (f i)) : InP 𝔭 k (∑ i ∈ s, f i) := by
  exact Finset.sum_induction f (InP 𝔭 k) (fun a b ha hb => inP_add ha hb) (InP.zero k) hf

/- English proof (translation)
Take `⟨s, hs, y, hy, hya⟩` from `ha`. Take `⟨t, ht, z, hz, hzb⟩` from `hb`. Use `⟨s * t, fun hst => (‹𝔭.IsPrime›.mem_or_mem hst).elim hs ht, ι t * y - ι s * z, Ideal.sub_mem _ (Ideal.mul_mem_left _ _ hy) (Ideal.mul_mem_left _ _ hz), ?_⟩` and prove the remaining obligations. Simplify using `only [map_sub, map_mul]`. Take the linear combination `(jK (ι t)) * hya - (jK (ι s)) * hzb`.
-/
theorem InP.sub {𝔭 : Ideal (𝓞 F)} [𝔭.IsPrime] {k : ℕ} {a b : K} (ha : InP 𝔭 k a) (hb : InP 𝔭 k b) :
    InP 𝔭 k (a - b) := by
  obtain ⟨s, hs, y, hy, hya⟩ := ha
  obtain ⟨t, ht, z, hz, hzb⟩ := hb
  refine ⟨s * t, fun hst => (‹𝔭.IsPrime›.mem_or_mem hst).elim hs ht, ι t * y - ι s * z,
    Ideal.sub_mem _ (Ideal.mul_mem_left _ _ hy) (Ideal.mul_mem_left _ _ hz), ?_⟩
  simp only [map_sub, map_mul]
  linear_combination (jK (ι t)) * hya - (jK (ι s)) * hzb

/- English proof (translation)
Establish `key : ∀ s ∈ Submonoid.closure {s : 𝓞 K | ∃ t : 𝓞 F, t ∉ 𝔭 ∧ algebraMap (𝓞 F) (𝓞 K) t = s}, ∃ t : 𝓞 F, t ∉ 𝔭 ∧ ι t = s`. Introduce `s hs`. Proceed by induction on `hs using Submonoid.closure_induction with`. Consider the case `mem x hx => exact hx`. Consider the case `one => exact ⟨1, fun h1 => ‹𝔭.IsPrime›.ne_top ((Ideal.eq_top_iff_one _).2 h1), map_one _⟩`.

Consider the case `mul x x' _ _ hx hx'`. Take `⟨a, ha, rfl⟩` from `hx`. Take `⟨a', ha', rfl⟩` from `hx'`. Conclude with `⟨a * a', fun h1 => (‹𝔭.IsPrime›.mem_or_mem h1).elim ha ha', map_mul _ _ _⟩`. Establish `hc : ∀ w : spanO b, ∃ c : κ → 𝓞 K, cmb b c = w`.

Introduce `w`. Unfold `cmb`. Conclude with `(Basis.equivFun _).symm.surjective w`. Establish `coords : ∀ u ∈ locF 𝔭 (spanO b), ∃ t : 𝓞 F, t ∉ 𝔭 ∧ ∃ c : κ → 𝓞 K, (cmb b c : V) = ι t • u`. Introduce `u hu`.

Establish `hu' : ∃ s ∈ Submonoid.closure {s : 𝓞 K | ∃ t : 𝓞 F, t ∉ 𝔭 ∧ algebraMap (𝓞 F) (𝓞 K) t = s}, s • u ∈ spanO b` using `hu`. Take `⟨s, hs, hsu⟩` from `hu'`. Take `⟨t, ht, rfl⟩` from `key s hs`. Take `⟨c, hcw⟩` from `hc ⟨ι t • u, hsu⟩`. Conclude with `⟨t, ht, c, congrArg Subtype.val hcw⟩`.

Establish `hfix : ∀ t : 𝓞 F, star (jK (ι t)) = jK (ι t)` using `fun t => (hF _).2 ⟨(t : F), rfl⟩`. Establish `hst : ∀ r : 𝓞 K, jK (star r) = star (jK r)` using `fun r => rfl`. Establish `hl : ∀ (r : 𝓞 K) (v w : V), h (r • v) w = star (jK r) * h v w` using `fun r v w => by`. Rewrite using `[← algebraMap_smul K r v, LinearMap.map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul, starRingEnd_apply]`. Establish `hr : ∀ (r : 𝓞 K) (v w : V), h v (r • w) = jK r * h v w` using `fun r v w => by`.

Rewrite using `[← algebraMap_smul K r w, map_smul, smul_eq_mul]`. Establish `scale : ∀ {m j : ℕ} {c : K} {p : 𝓞 K}, InP 𝔭 m c → p ∈ extP K 𝔭 ^ j → InP 𝔭 (m + j) (jK p * c)`. Introduce `m j c p hc0 hp`. Take `⟨t, ht, z, hz, hzc⟩` from `hc0`. Use `⟨t, ht, z * p, ?_, ?_⟩` and prove the remaining obligations.

Rewrite using `[pow_add]`. Conclude with `Ideal.mul_mem_mul hz hp`. Rewrite using `[map_mul, hzc]`. Expand and normalize the polynomial expressions, which then agree. Establish `mulI : ∀ {m : ℕ} {c : K} (r : 𝓞 K), InP 𝔭 m c → InP 𝔭 m (jK r * c)`.

Introduce `m c r hc0`. Take `⟨t, ht, z, hz, hzc⟩` from `hc0`. Conclude with `⟨t, ht, r * z, Ideal.mul_mem_left _ r hz, by rw [map_mul, hzc]; ring⟩`. Establish `base : ∀ u ∈ locF 𝔭 (spanO b), ∀ v ∈ locF 𝔭 (spanO b), InP 𝔭 0 (h u v)`. Introduce `u hu v hv`.

Take `⟨t, ht, c, hcu⟩` from `coords u hu`. Take `⟨t', ht', c', hcv⟩` from `coords v hv`. Establish `e : h (cmb b c : V) (cmb b c' : V) = jK (∑ i, ∑ j, star (c i) * (c' j * H i j))`. Rewrite using `[coe_cmb, coe_cmb]`. Establish `h1 : ∀ w : V, h (∑ i, c i • b i) w = ∑ i, star (jK (c i)) * h (b i) w`.

Introduce `w`. Rewrite using `[map_sum, LinearMap.sum_apply]`. Conclude with `Finset.sum_congr rfl fun i _ => hl _ _ _`. Rewrite using `[h1]`. Simplify using `only [map_sum, map_mul, hst, hr, ← hH, Finset.mul_sum]`.

Rewrite `e` using `[hcu, hcv, hl, hr, hfix]`. Use `⟨t * t', fun h1 => (‹𝔭.IsPrime›.mem_or_mem h1).elim ht ht', ∑ i, ∑ j, star (c i) * (c' j * H i j), ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[pow_zero, Ideal.one_eq_top]`. Conclude with `Submodule.mem_top`. Rewrite using `[← e]`.

Simplify using `only [map_mul]`. Expand and normalize the polynomial expressions, which then agree. Establish `step1 : ∀ u ∈ locF 𝔭 (spanO b), ∀ {m : ℕ} {w : V}, w ∈ (extP K 𝔭 ^ m • locF 𝔭 (spanO b) : Submodule (𝓞 K) V) → InP 𝔭 m (h u w)`. Introduce `u hu m w hw`. Use `Submodule.smul_induction_on (p := fun w => InP 𝔭 m (h u w)) hw (fun p hp v hv => ?_) (fun w₁ w₂ h₁ h₂ => ?_)` and prove the remaining obligations.

Rewrite using `[hr]`. Establish `h3` using `scale (base u hu v hv) hp`. Rewrite `h3` using `[zero_add]`. Then use the resulting hypothesis. Rewrite using `[map_add]`. Conclude with `inP_add h₁ h₂`.

Establish `hstar : ∀ {j m : ℕ} {c : K}, InP 𝔭 m c → ∀ p ∈ extP K 𝔭 ^ j, InP 𝔭 (j + m) (star (jK p) * c)`. Introduce `j m c hc0 p hp`. Establish `hp' : p ∈ Submodule.span (𝓞 K) (ι '' ((𝔭 ^ j : Ideal (𝓞 F)) : Set (𝓞 F)))`. Unfold `extP at hp`. Rewrite `hp` using `[← Ideal.map_pow]`.

Conclude with `hp`. Use `clear hp`. Proceed by induction on `hp' using Submodule.span_induction with`. Consider the case `mem x hx`. Take `⟨t, ht, rfl⟩` from `hx`.

Rewrite using `[hfix, add_comm]`. Use `scale hc0 ?_` and prove the remaining obligations. Unfold `extP`. Rewrite using `[← Ideal.map_pow]`. Conclude with `Ideal.mem_map_of_mem _ ht`.

Consider the case `zero => simpa using InP.zero (𝔭 := 𝔭) (K := K) (j + m)`. Consider the case `add x y _ _ hx hy`. Rewrite using `[map_add, star_add, add_mul]`. Conclude with `inP_add hx hy`. Consider the case `smul r x _ hx`.

Rewrite using `[smul_eq_mul, map_mul, star_mul', mul_assoc, ← hst]`. Conclude with `mulI _ hx`. Use `Submodule.smul_induction_on (p := fun w => InP 𝔭 (k + l) (h w y)) hx (fun p hp u hu => ?_) (fun w₁ w₂ h₁ h₂ => ?_)` and prove the remaining obligations. Rewrite using `[hl]`. Conclude with `hstar (step1 u hu hy) p hp`.

Rewrite using `[map_add, LinearMap.add_apply]`. Conclude with `inP_add h₁ h₂`.
-/
theorem form_inP (hF : IsFixF K F) {h : V →ₗ⋆[K] V →ₗ[K] K} (b : Basis κ K V) {H : Matrix κ κ (𝓞 K)}
    (hH : ∀ i j, jK (H i j) = h (b i) (b j)) {𝔭 : Ideal (𝓞 F)} [𝔭.IsPrime] {k l : ℕ} {x y : V}
    (hx : x ∈ (extP K 𝔭 ^ k • locF 𝔭 (spanO b) : Submodule (𝓞 K) V))
    (hy : y ∈ (extP K 𝔭 ^ l • locF 𝔭 (spanO b) : Submodule (𝓞 K) V)) : InP 𝔭 (k + l) (h x y) := by
  have key : ∀ s ∈ Submonoid.closure {s : 𝓞 K | ∃ t : 𝓞 F, t ∉ 𝔭 ∧ algebraMap (𝓞 F) (𝓞 K) t = s},
      ∃ t : 𝓞 F, t ∉ 𝔭 ∧ ι t = s := by
    intro s hs
    induction hs using Submonoid.closure_induction with
    | mem x hx => exact hx
    | one => exact ⟨1, fun h1 => ‹𝔭.IsPrime›.ne_top ((Ideal.eq_top_iff_one _).2 h1), map_one _⟩
    | mul x x' _ _ hx hx' =>
      obtain ⟨a, ha, rfl⟩ := hx
      obtain ⟨a', ha', rfl⟩ := hx'
      exact ⟨a * a', fun h1 => (‹𝔭.IsPrime›.mem_or_mem h1).elim ha ha', map_mul _ _ _⟩
  have hc : ∀ w : spanO b, ∃ c : κ → 𝓞 K, cmb b c = w := by
    intro w
    unfold cmb
    exact (Basis.equivFun _).symm.surjective w
  have coords : ∀ u ∈ locF 𝔭 (spanO b),
      ∃ t : 𝓞 F, t ∉ 𝔭 ∧ ∃ c : κ → 𝓞 K, (cmb b c : V) = ι t • u := by
    intro u hu
    have hu' : ∃ s ∈ Submonoid.closure {s : 𝓞 K | ∃ t : 𝓞 F, t ∉ 𝔭 ∧ algebraMap (𝓞 F) (𝓞 K) t = s},
        s • u ∈ spanO b := hu
    obtain ⟨s, hs, hsu⟩ := hu'
    obtain ⟨t, ht, rfl⟩ := key s hs
    obtain ⟨c, hcw⟩ := hc ⟨ι t • u, hsu⟩
    exact ⟨t, ht, c, congrArg Subtype.val hcw⟩
  have hfix : ∀ t : 𝓞 F, star (jK (ι t)) = jK (ι t) := fun t => (hF _).2 ⟨(t : F), rfl⟩
  have hst : ∀ r : 𝓞 K, jK (star r) = star (jK r) := fun r => rfl
  have hl : ∀ (r : 𝓞 K) (v w : V), h (r • v) w = star (jK r) * h v w := fun r v w => by
    rw [← algebraMap_smul K r v, LinearMap.map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul,
      starRingEnd_apply]
  have hr : ∀ (r : 𝓞 K) (v w : V), h v (r • w) = jK r * h v w := fun r v w => by
    rw [← algebraMap_smul K r w, map_smul, smul_eq_mul]
  have scale : ∀ {m j : ℕ} {c : K} {p : 𝓞 K}, InP 𝔭 m c → p ∈ extP K 𝔭 ^ j →
      InP 𝔭 (m + j) (jK p * c) := by
    intro m j c p hc0 hp
    obtain ⟨t, ht, z, hz, hzc⟩ := hc0
    refine ⟨t, ht, z * p, ?_, ?_⟩
    · rw [pow_add]
      exact Ideal.mul_mem_mul hz hp
    · rw [map_mul, hzc]
      ring
  have mulI : ∀ {m : ℕ} {c : K} (r : 𝓞 K), InP 𝔭 m c → InP 𝔭 m (jK r * c) := by
    intro m c r hc0
    obtain ⟨t, ht, z, hz, hzc⟩ := hc0
    exact ⟨t, ht, r * z, Ideal.mul_mem_left _ r hz, by rw [map_mul, hzc]; ring⟩
  have base : ∀ u ∈ locF 𝔭 (spanO b), ∀ v ∈ locF 𝔭 (spanO b), InP 𝔭 0 (h u v) := by
    intro u hu v hv
    obtain ⟨t, ht, c, hcu⟩ := coords u hu
    obtain ⟨t', ht', c', hcv⟩ := coords v hv
    have e : h (cmb b c : V) (cmb b c' : V) = jK (∑ i, ∑ j, star (c i) * (c' j * H i j)) := by
      rw [coe_cmb, coe_cmb]
      have h1 : ∀ w : V, h (∑ i, c i • b i) w = ∑ i, star (jK (c i)) * h (b i) w := by
        intro w
        rw [map_sum, LinearMap.sum_apply]
        exact Finset.sum_congr rfl fun i _ => hl _ _ _
      rw [h1]
      simp only [map_sum, map_mul, hst, hr, ← hH, Finset.mul_sum]
    rw [hcu, hcv, hl, hr, hfix] at e
    refine ⟨t * t', fun h1 => (‹𝔭.IsPrime›.mem_or_mem h1).elim ht ht', ∑ i, ∑ j, star (c i) * (c' j * H i j), ?_, ?_⟩
    · rw [pow_zero, Ideal.one_eq_top]
      exact Submodule.mem_top
    · rw [← e]
      simp only [map_mul]
      ring
  have step1 : ∀ u ∈ locF 𝔭 (spanO b), ∀ {m : ℕ} {w : V},
      w ∈ (extP K 𝔭 ^ m • locF 𝔭 (spanO b) : Submodule (𝓞 K) V) → InP 𝔭 m (h u w) := by
    intro u hu m w hw
    refine Submodule.smul_induction_on (p := fun w => InP 𝔭 m (h u w)) hw
      (fun p hp v hv => ?_) (fun w₁ w₂ h₁ h₂ => ?_)
    · rw [hr]
      have h3 := scale (base u hu v hv) hp
      rwa [zero_add] at h3
    · rw [map_add]
      exact inP_add h₁ h₂
  have hstar : ∀ {j m : ℕ} {c : K}, InP 𝔭 m c → ∀ p ∈ extP K 𝔭 ^ j,
      InP 𝔭 (j + m) (star (jK p) * c) := by
    intro j m c hc0 p hp
    have hp' : p ∈ Submodule.span (𝓞 K) (ι '' ((𝔭 ^ j : Ideal (𝓞 F)) : Set (𝓞 F))) := by
      unfold extP at hp
      rw [← Ideal.map_pow] at hp
      exact hp
    clear hp
    induction hp' using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨t, ht, rfl⟩ := hx
      rw [hfix, add_comm]
      refine scale hc0 ?_
      unfold extP
      rw [← Ideal.map_pow]
      exact Ideal.mem_map_of_mem _ ht
    | zero => simpa using InP.zero (𝔭 := 𝔭) (K := K) (j + m)
    | add x y _ _ hx hy =>
      rw [map_add, star_add, add_mul]
      exact inP_add hx hy
    | smul r x _ hx =>
      rw [smul_eq_mul, map_mul, star_mul', mul_assoc, ← hst]
      exact mulI _ hx
  refine Submodule.smul_induction_on (p := fun w => InP 𝔭 (k + l) (h w y)) hx
    (fun p hp u hu => ?_) (fun w₁ w₂ h₁ h₂ => ?_)
  · rw [hl]
    exact hstar (step1 u hu hy) p hp
  · rw [map_add, LinearMap.add_apply]
    exact inP_add h₁ h₂

/- English proof (translation)
Rewrite using `[pow_zero, Ideal.one_eq_top, Submodule.top_smul]`. Conclude with `hx`.
-/
theorem mem_smul_zero {𝔭 : Ideal (𝓞 F)} {A : Submodule (𝓞 K) V} {x : V} (hx : x ∈ A) :
    x ∈ (extP K 𝔭 ^ 0 • A : Submodule (𝓞 K) V) := by
  rw [pow_zero, Ideal.one_eq_top, Submodule.top_smul]
  exact hx

/- English proof (translation)
Establish `e : h x y - h x₁ y₁ = h (x - x₁) y + h x₁ (y - y₁)`. Simplify using `only [map_sub, LinearMap.sub_apply]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e]`. Establish `h1` using `form_inP hF b hH hxx (mem_smul_zero hy)`.

Establish `h2` using `form_inP hF b hH (mem_smul_zero hx₁) hyy`. Rewrite `h2` using `[zero_add]`. Conclude with `inP_add h1 h2`.
-/
theorem form_congr (hF : IsFixF K F) {h : V →ₗ⋆[K] V →ₗ[K] K} (b : Basis κ K V) {H : Matrix κ κ (𝓞 K)}
    (hH : ∀ i j, jK (H i j) = h (b i) (b j)) {𝔭 : Ideal (𝓞 F)} [𝔭.IsPrime] {k : ℕ} {x x₁ y y₁ : V}
    (hx₁ : x₁ ∈ locF 𝔭 (spanO b)) (hy : y ∈ locF 𝔭 (spanO b))
    (hxx : x - x₁ ∈ (extP K 𝔭 ^ k • locF 𝔭 (spanO b) : Submodule (𝓞 K) V))
    (hyy : y - y₁ ∈ (extP K 𝔭 ^ k • locF 𝔭 (spanO b) : Submodule (𝓞 K) V)) :
    InP 𝔭 k (h x y - h x₁ y₁) := by
  have e : h x y - h x₁ y₁ = h (x - x₁) y + h x₁ (y - y₁) := by
    simp only [map_sub, LinearMap.sub_apply]; ring
  rw [e]
  have h1 := form_inP hF b hH hxx (mem_smul_zero hy)
  have h2 := form_inP hF b hH (mem_smul_zero hx₁) hyy
  rw [zero_add] at h2
  exact inP_add h1 h2

/- English proof (translation)
Establish `hst : ∀ r : 𝓞 K, jK (star r) = star (jK r)` using `fun r => rfl`. Establish `hl : ∀ (r : 𝓞 K) (v w : V), h (r • v) w = star (jK r) * h v w` using `fun r v w => by`. Rewrite using `[← algebraMap_smul K r v, LinearMap.map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul, starRingEnd_apply]`. Establish `hr : ∀ (r : 𝓞 K) (v w : V), h v (r • w) = jK r * h v w` using `fun r v w => by`. Rewrite using `[← algebraMap_smul K r w, map_smul, smul_eq_mul]`.

Establish `expand : h (∑ i, c i • b i) (∑ j, c' j • b j) = ∑ i, ∑ j, star (jK (c i)) * (jK (c' j) * h (b i) (b j))`. Establish `h1 : ∀ w : V, h (∑ i, c i • b i) w = ∑ i, star (jK (c i)) * h (b i) w`. Introduce `w`. Rewrite using `[map_sum, LinearMap.sum_apply]`. Conclude with `Finset.sum_congr rfl fun i _ => hl _ _ _`.

Rewrite using `[h1]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[map_sum, Finset.mul_sum]`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Rewrite using `[hr]`.

Establish `rhs : jK (star c ⬝ᵥ (H *ᵥ c')) = ∑ i, ∑ j, star (jK (c i)) * (jK (H i j) * jK (c' j))`. Simplify using `only [dotProduct, Matrix.mulVec, Pi.star_apply, map_sum, map_mul, hst, Finset.mul_sum]`. Rewrite using `[coe_cmb, coe_cmb, expand, rhs]`. Use `Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Rewrite using `[← hH]`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem form_cmb {h : V →ₗ⋆[K] V →ₗ[K] K} (b : Basis κ K V) {H : Matrix κ κ (𝓞 K)}
    (hH : ∀ i j, jK (H i j) = h (b i) (b j)) (c c' : κ → 𝓞 K) :
    h (cmb b c : V) (cmb b c' : V) = jK (star c ⬝ᵥ (H *ᵥ c')) := by
  have hst : ∀ r : 𝓞 K, jK (star r) = star (jK r) := fun r => rfl
  have hl : ∀ (r : 𝓞 K) (v w : V), h (r • v) w = star (jK r) * h v w := fun r v w => by
    rw [← algebraMap_smul K r v, LinearMap.map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul,
      starRingEnd_apply]
  have hr : ∀ (r : 𝓞 K) (v w : V), h v (r • w) = jK r * h v w := fun r v w => by
    rw [← algebraMap_smul K r w, map_smul, smul_eq_mul]
  have expand : h (∑ i, c i • b i) (∑ j, c' j • b j) =
      ∑ i, ∑ j, star (jK (c i)) * (jK (c' j) * h (b i) (b j)) := by
    have h1 : ∀ w : V, h (∑ i, c i • b i) w = ∑ i, star (jK (c i)) * h (b i) w := by
      intro w
      rw [map_sum, LinearMap.sum_apply]
      exact Finset.sum_congr rfl fun i _ => hl _ _ _
    rw [h1]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hr]
  have rhs : jK (star c ⬝ᵥ (H *ᵥ c')) = ∑ i, ∑ j, star (jK (c i)) * (jK (H i j) * jK (c' j)) := by
    simp only [dotProduct, Matrix.mulVec, Pi.star_apply, map_sum, map_mul, hst, Finset.mul_sum]
  rw [coe_cmb, coe_cmb, expand, rhs]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [← hH]
  ring

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨t, ht, z, hz, hzt⟩`. Establish `e1 : z = ι t * a`. Apply `IsFractionRing.injective (𝓞 K) K` to reduce the goal to its premises. Rewrite using `[hzt, map_mul]`.

Take `⟨y, i, hi, hyi⟩` from `h𝔭.exists_inv ht`. Take `⟨q, hq⟩` from `sub_dvd_pow_sub_pow (1 : 𝓞 F) i k`. Establish `e0 : (1 : 𝓞 F) - i = y * t` using `by linear_combination -hyi`. Rewrite `hq` using `[e0, one_pow]`. Establish `e2 : (1 : 𝓞 F) = i ^ k + y * t * q` using `by linear_combination hq`.

Establish `h1` using `congrArg ι e2`. Simplify using `only [map_one, map_add, map_mul] at h1`. Establish `e3 : a = ι (i ^ k) * a + ι y * ι q * (ι t * a)` using `by linear_combination a * h1`. Rewrite using `[e3]`. Use `Ideal.add_mem _ (Ideal.mul_mem_right _ _ ?_) (Ideal.mul_mem_left _ _ (by rw [← e1]; exact hz))` and prove the remaining obligations.

Rewrite using `[map_pow]`. Conclude with `Ideal.pow_mem_pow (Ideal.mem_map_of_mem _ hi) k`. Introduce `ha`. Conclude with `⟨1, fun h1 => h𝔭.ne_top ((Ideal.eq_top_iff_one _).2 h1), a, ha, by simp⟩`.
-/
theorem inP_jK_iff {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) (k : ℕ) (a : 𝓞 K) :
    InP 𝔭 k (jK a) ↔ a ∈ extP K 𝔭 ^ k := by
  constructor
  · rintro ⟨t, ht, z, hz, hzt⟩
    have e1 : z = ι t * a := by
      apply IsFractionRing.injective (𝓞 K) K
      rw [hzt, map_mul]
    obtain ⟨y, i, hi, hyi⟩ := h𝔭.exists_inv ht
    obtain ⟨q, hq⟩ := sub_dvd_pow_sub_pow (1 : 𝓞 F) i k
    have e0 : (1 : 𝓞 F) - i = y * t := by linear_combination -hyi
    rw [e0, one_pow] at hq
    have e2 : (1 : 𝓞 F) = i ^ k + y * t * q := by linear_combination hq
    have h1 := congrArg ι e2
    simp only [map_one, map_add, map_mul] at h1
    have e3 : a = ι (i ^ k) * a + ι y * ι q * (ι t * a) := by linear_combination a * h1
    rw [e3]
    refine Ideal.add_mem _ (Ideal.mul_mem_right _ _ ?_) (Ideal.mul_mem_left _ _ (by rw [← e1]; exact hz))
    rw [map_pow]
    exact Ideal.pow_mem_pow (Ideal.mem_map_of_mem _ hi) k
  · intro ha
    exact ⟨1, fun h1 => h𝔭.ne_top ((Ideal.eq_top_iff_one _).2 h1), a, ha, by simp⟩

/- English proof (translation)
The claim follows from `Submodule.smul_mono_left (Ideal.pow_le_pow_right hjk)`.
-/
theorem smul_mono_pow {𝔭 : Ideal (𝓞 F)} {A : Submodule (𝓞 K) V} {j k : ℕ} (hjk : j ≤ k) :
    (extP K 𝔭 ^ k • A : Submodule (𝓞 K) V) ≤ extP K 𝔭 ^ j • A := Submodule.smul_mono_left (Ideal.pow_le_pow_right hjk)

/- English proof (translation)
Establish `hg' : Formalism.HermitianLatticesTheory.gmap g A = A` using `hg.2`. Rewrite using `[← hg']`. Conclude with `Submodule.mem_map_of_mem hx`.
-/
theorem aut_mem {h : V →ₗ⋆[K] V →ₗ[K] K} {A : Submodule (𝓞 K) V} {g : V ≃ₗ[K] V} (hg : g ∈ autSub h A)
    {x : V} (hx : x ∈ A) : g x ∈ A := by
  have hg' : Formalism.HermitianLatticesTheory.gmap g A = A := hg.2
  rw [← hg']
  exact Submodule.mem_map_of_mem hx

/- English proof (translation)
Establish `hs : ∀ (r : 𝓞 K) (v : V), g (r • v) = r • g v` using `fun r v => by`. Rewrite using `[← algebraMap_smul K r v, map_smul, algebraMap_smul]`. Use `Submodule.smul_induction_on (p := fun w => g w ∈ J • A) hx (fun r hr a ha => ?_) (fun u w hu hw => ?_)` and prove the remaining obligations. Simplify using `only [hs]`. Conclude with `Submodule.smul_mem_smul hr (aut_mem hg ha)`.

Simplify using `only [map_add]`. Conclude with `Submodule.add_mem _ hu hw`.
-/
theorem aut_mem_smul {h : V →ₗ⋆[K] V →ₗ[K] K} {A : Submodule (𝓞 K) V} {g : V ≃ₗ[K] V}
    (hg : g ∈ autSub h A) (J : Ideal (𝓞 K)) {x : V} (hx : x ∈ J • A) : g x ∈ J • A := by
  have hs : ∀ (r : 𝓞 K) (v : V), g (r • v) = r • g v := fun r v => by
    rw [← algebraMap_smul K r v, map_smul, algebraMap_smul]
  refine Submodule.smul_induction_on (p := fun w => g w ∈ J • A) hx (fun r hr a ha => ?_)
    (fun u w hu hw => ?_)
  · simp only [hs]
    exact Submodule.smul_mem_smul hr (aut_mem hg ha)
  · simp only [map_add]
    exact Submodule.add_mem _ hu hw

/- English proof (translation)
Establish `hs : ∀ (r : 𝓞 K) (v : V), g (r • v) = r • g v` using `fun r v => by`. Rewrite using `[← algebraMap_smul K r v, map_smul, algebraMap_smul]`. Establish `e : ∑ l, (Y *ᵥ c) l • b l = ∑ i, c i • ∑ l, Y l i • b l`. Simplify using `only [Matrix.mulVec, dotProduct, Finset.sum_smul, Finset.smul_sum, smul_smul]`. Rewrite using `[Finset.sum_comm]`.

Use `Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun l _ => ?_` and prove the remaining obligations. Rewrite using `[mul_comm]`. Rewrite using `[coe_cmb, coe_cmb, map_sum, e]`. Simplify using `only [hs]`. Rewrite using `[← Finset.sum_sub_distrib]`.

Use `Submodule.sum_mem _ fun i _ => ?_` and prove the remaining obligations. Rewrite using `[← smul_sub]`. Conclude with `Submodule.smul_mem _ (c i) (hgY i)`.
-/
theorem aut_cmb {𝔭 : Ideal (𝓞 F)} (b : Basis κ K V) {g : V ≃ₗ[K] V} {Y : Matrix κ κ (𝓞 K)} {j : ℕ}
    (hgY : ∀ i, g (b i) - ∑ l, Y l i • b l ∈ (extP K 𝔭 ^ j • locF 𝔭 (spanO b) : Submodule (𝓞 K) V))
    (c : κ → 𝓞 K) :
    g (cmb b c : V) - (cmb b (Y *ᵥ c) : V) ∈ (extP K 𝔭 ^ j • locF 𝔭 (spanO b) : Submodule (𝓞 K) V) := by
  have hs : ∀ (r : 𝓞 K) (v : V), g (r • v) = r • g v := fun r v => by
    rw [← algebraMap_smul K r v, map_smul, algebraMap_smul]
  have e : ∑ l, (Y *ᵥ c) l • b l = ∑ i, c i • ∑ l, Y l i • b l := by
    simp only [Matrix.mulVec, dotProduct, Finset.sum_smul, Finset.smul_sum, smul_smul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun l _ => ?_
    rw [mul_comm]
  rw [coe_cmb, coe_cmb, map_sum, e]
  simp only [hs]
  rw [← Finset.sum_sub_distrib]
  refine Submodule.sum_mem _ fun i _ => ?_
  rw [← smul_sub]
  exact Submodule.smul_mem _ (c i) (hgY i)

/- English proof (translation)
Establish `key : ∀ s ∈ Submonoid.closure {s : 𝓞 K | ∃ t : 𝓞 F, t ∉ 𝔭 ∧ algebraMap (𝓞 F) (𝓞 K) t = s}, ∃ t : 𝓞 F, t ∉ 𝔭 ∧ ι t = s`. Introduce `s hs`. Proceed by induction on `hs using Submonoid.closure_induction with`. Consider the case `mem x hx => exact hx`. Consider the case `one => exact ⟨1, fun h1 => h𝔭.ne_top ((Ideal.eq_top_iff_one _).2 h1), map_one _⟩`.

Consider the case `mul x x' _ _ hx hx'`. Take `⟨a, ha, rfl⟩` from `hx`. Take `⟨a', ha', rfl⟩` from `hx'`. Conclude with `⟨a * a', fun h1 => (‹𝔭.IsPrime›.mem_or_mem h1).elim ha ha', map_mul _ _ _⟩`. Establish `surj : ∀ z : QA 𝔭 b k, ∃ w : spanO b, Submodule.Quotient.mk (inA 𝔭 b w) = z`.

Introduce `z`. Take `⟨y, rfl⟩` from `Submodule.Quotient.mk_surjective _ z`. Establish `hy : ∃ s ∈ Submonoid.closure {s : 𝓞 K | ∃ t : 𝓞 F, t ∉ 𝔭 ∧ algebraMap (𝓞 F) (𝓞 K) t = s}, s • (y : V) ∈ spanO b` using `y.2`. Take `⟨s, hs, hsy⟩` from `hy`. Take `⟨t, ht, rfl⟩` from `key s hs`.

Take `⟨y', i, hi, hyi⟩` from `h𝔭.exists_inv ht`. Take `⟨q, hq⟩` from `sub_dvd_pow_sub_pow (1 : 𝓞 F) i k`. Establish `e0 : (1 : 𝓞 F) - i = y' * t` using `by linear_combination -hyi`. Rewrite `hq` using `[e0, one_pow]`. Establish `hc : ι (y' * q) * ι t = 1 - ι (i ^ k)`.

Establish `h2` using `congrArg ι hq`. Simplify using `only [map_sub, map_one, map_mul, map_pow] at h2 ⊢`. Take the linear combination `-h2`. Establish `hmem : ι (i ^ k) ∈ extP K 𝔭 ^ k`. Rewrite using `[map_pow]`.

Conclude with `Ideal.pow_mem_pow (Ideal.mem_map_of_mem _ hi) k`. Use `⟨⟨ι (y' * q) • (ι t • (y : V)), Submodule.smul_mem _ _ hsy⟩, ?_⟩` and prove the remaining obligations. Rewrite using `[Submodule.Quotient.eq]`. Establish `e4 : inA 𝔭 b ⟨ι (y' * q) • (ι t • (y : V)), Submodule.smul_mem _ _ hsy⟩ - y = (-ι (i ^ k)) • y`. Apply `Subtype.ext` to reduce the goal to its premises.

Use `show ι (y' * q) • (ι t • (y : V)) - (y : V) = (-ι (i ^ k)) • (y : V)`. Rewrite using `[smul_smul, hc, sub_smul, one_smul, neg_smul]`. Normalize the expressions using the abelian group laws. Rewrite using `[e4]`. Conclude with `Submodule.smul_mem_smul (Submodule.neg_mem _ hmem) Submodule.mem_top`.

Establish `hc : ∀ w : spanO b, ∃ c : κ → 𝓞 K, cmb b c = w`. Introduce `w`. Unfold `cmb`. Conclude with `(Basis.equivFun _).symm.surjective w`. Use `choose w hw using surj`.

Use `choose c hc' using hc`. Use `⟨Matrix.of fun l i => c (w (X (Submodule.Quotient.mk (inA 𝔭 b (cmb b (Pi.single i 1)))))) l, fun i => ?_⟩` and prove the remaining obligations. Establish `e : (cmb b fun l => Matrix.of (fun l i => c (w (X (Submodule.Quotient.mk (inA 𝔭 b (cmb b (Pi.single i 1)))))) l) l i) = w (X (Submodule.Quotient.mk (inA 𝔭 b (cmb b (Pi.single i 1)))))`. Simplify using `only [Matrix.of_apply]`. Conclude with `hc' _`.

Rewrite using `[e, hw]`.
-/
theorem exists_matrix_of_end {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) [𝔭.IsPrime] (b : Basis κ K V) (k : ℕ)
    (X : Module.End (𝓞 K) (QA 𝔭 b k)) : ∃ Y : Matrix κ κ (𝓞 K),
      ∀ i, X (Submodule.Quotient.mk (inA 𝔭 b (cmb b (Pi.single i 1)))) =
        Submodule.Quotient.mk (inA 𝔭 b (cmb b fun l => Y l i)) := by
  have key : ∀ s ∈ Submonoid.closure {s : 𝓞 K | ∃ t : 𝓞 F, t ∉ 𝔭 ∧ algebraMap (𝓞 F) (𝓞 K) t = s},
      ∃ t : 𝓞 F, t ∉ 𝔭 ∧ ι t = s := by
    intro s hs
    induction hs using Submonoid.closure_induction with
    | mem x hx => exact hx
    | one => exact ⟨1, fun h1 => h𝔭.ne_top ((Ideal.eq_top_iff_one _).2 h1), map_one _⟩
    | mul x x' _ _ hx hx' =>
      obtain ⟨a, ha, rfl⟩ := hx
      obtain ⟨a', ha', rfl⟩ := hx'
      exact ⟨a * a', fun h1 => (‹𝔭.IsPrime›.mem_or_mem h1).elim ha ha', map_mul _ _ _⟩
  have surj : ∀ z : QA 𝔭 b k, ∃ w : spanO b, Submodule.Quotient.mk (inA 𝔭 b w) = z := by
    intro z
    obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ z
    have hy : ∃ s ∈ Submonoid.closure {s : 𝓞 K | ∃ t : 𝓞 F, t ∉ 𝔭 ∧ algebraMap (𝓞 F) (𝓞 K) t = s},
        s • (y : V) ∈ spanO b := y.2
    obtain ⟨s, hs, hsy⟩ := hy
    obtain ⟨t, ht, rfl⟩ := key s hs
    obtain ⟨y', i, hi, hyi⟩ := h𝔭.exists_inv ht
    obtain ⟨q, hq⟩ := sub_dvd_pow_sub_pow (1 : 𝓞 F) i k
    have e0 : (1 : 𝓞 F) - i = y' * t := by linear_combination -hyi
    rw [e0, one_pow] at hq
    have hc : ι (y' * q) * ι t = 1 - ι (i ^ k) := by
      have h2 := congrArg ι hq
      simp only [map_sub, map_one, map_mul, map_pow] at h2 ⊢
      linear_combination -h2
    have hmem : ι (i ^ k) ∈ extP K 𝔭 ^ k := by
      rw [map_pow]
      exact Ideal.pow_mem_pow (Ideal.mem_map_of_mem _ hi) k
    refine ⟨⟨ι (y' * q) • (ι t • (y : V)), Submodule.smul_mem _ _ hsy⟩, ?_⟩
    rw [Submodule.Quotient.eq]
    have e4 : inA 𝔭 b ⟨ι (y' * q) • (ι t • (y : V)), Submodule.smul_mem _ _ hsy⟩ - y =
        (-ι (i ^ k)) • y := by
      apply Subtype.ext
      show ι (y' * q) • (ι t • (y : V)) - (y : V) = (-ι (i ^ k)) • (y : V)
      rw [smul_smul, hc, sub_smul, one_smul, neg_smul]
      abel
    rw [e4]
    exact Submodule.smul_mem_smul (Submodule.neg_mem _ hmem) Submodule.mem_top
  have hc : ∀ w : spanO b, ∃ c : κ → 𝓞 K, cmb b c = w := by
    intro w
    unfold cmb
    exact (Basis.equivFun _).symm.surjective w
  choose w hw using surj
  choose c hc' using hc
  refine ⟨Matrix.of fun l i => c (w (X (Submodule.Quotient.mk (inA 𝔭 b (cmb b (Pi.single i 1)))))) l,
    fun i => ?_⟩
  have e : (cmb b fun l => Matrix.of (fun l i =>
      c (w (X (Submodule.Quotient.mk (inA 𝔭 b (cmb b (Pi.single i 1)))))) l) l i) =
      w (X (Submodule.Quotient.mk (inA 𝔭 b (cmb b (Pi.single i 1))))) := by
    simp only [Matrix.of_apply]
    exact hc' _
  rw [e, hw]

/- English proof (translation)
Use `h𝔭.isPrime` as an intermediate fact. Take `⟨Y, hXY⟩` from `exists_matrix_of_end h𝔭 b k X`. Establish `hY : ∀ i j, (Yᴴ * H * Y - H) i j ∈ extP K 𝔭 ^ k`. Introduce `i j`. Establish `h1` using `hX _ _ _ _ (hXY i).symm (hXY j).symm`.

Rewrite `h1` using `[congrP_iff_inP, coe_inA, coe_inA, coe_inA, coe_inA, form_cmb b hH, form_cmb b hH, ← form_col, form_single, ← map_sub, inP_jK_iff h𝔭]`. Conclude with `h1`. Take `⟨g, hg, hgY⟩` from `exists_isom_matrix hK hF hs hd b hH h𝔭 he hk Y hY`. Use `⟨g, hg, fun x x' hxx' => ?_⟩` and prove the remaining obligations. Take `⟨c, hc⟩` from `exists_cmb h𝔭 b k (Submodule.Quotient.mk x)`.

Rewrite `hxx'` using `[hc, end_apply_cmb b k X Y hXY c, mk_eq_iff]`. Rewrite `hc` using `[mk_eq_iff]`. Establish `e1 : g (x : V) - x' = g ((x : V) - (inA 𝔭 b (cmb b c) : V)) + (g (cmb b c : V) - (cmb b (Y *ᵥ c) : V)) - ((x' : V) - (inA 𝔭 b (cmb b (Y *ᵥ c)) : V))`. Rewrite using `[map_sub, coe_inA, coe_inA]`. Normalize the expressions using the abelian group laws.

Rewrite using `[e1]`. Conclude with `sub_mem (add_mem (smul_mono_pow (Nat.sub_le k e) (aut_mem_smul hg _ hc)) (aut_cmb b hgY c)) (smul_mono_pow (Nat.sub_le k e) hxx')`.
-/
theorem exists_isom_lift_basis (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F) {h : V →ₗ⋆[K] V →ₗ[K] K}
    (hs : h.IsSymm) (hd : ∀ x, h x x = 0 → x = 0) (b : Basis κ K V) {H : Matrix κ κ (𝓞 K)}
    (hH : ∀ i j, jK (H i j) = h (b i) (b j)) {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) {e k : ℕ}
    (he : IsE h (locF 𝔭 (spanO b)) 𝔭 e) (hk : e + 1 ≤ k) (X : Module.End (𝓞 K) (QA 𝔭 b k))
    (hX : ∀ x y x' y' : ↥(locF 𝔭 (spanO b)), Submodule.Quotient.mk x' = X (Submodule.Quotient.mk x) →
      Submodule.Quotient.mk y' = X (Submodule.Quotient.mk y) →
      CongrP 𝔭 k (h (x' : V) (y' : V)) (h (x : V) (y : V))) :
    ∃ g ∈ autSub h (locF 𝔭 (spanO b)), ∀ x x' : ↥(locF 𝔭 (spanO b)),
      Submodule.Quotient.mk x' = X (Submodule.Quotient.mk x) →
      g x - x' ∈ ((extP K 𝔭) ^ (k - e) • (locF 𝔭 (spanO b)) : Submodule (𝓞 K) V) := by
  have := h𝔭.isPrime
  obtain ⟨Y, hXY⟩ := exists_matrix_of_end h𝔭 b k X
  have hY : ∀ i j, (Yᴴ * H * Y - H) i j ∈ extP K 𝔭 ^ k := by
    intro i j
    have h1 := hX _ _ _ _ (hXY i).symm (hXY j).symm
    rw [congrP_iff_inP, coe_inA, coe_inA, coe_inA, coe_inA, form_cmb b hH, form_cmb b hH, ← form_col,
      form_single, ← map_sub, inP_jK_iff h𝔭] at h1
    exact h1
  obtain ⟨g, hg, hgY⟩ := exists_isom_matrix hK hF hs hd b hH h𝔭 he hk Y hY
  refine ⟨g, hg, fun x x' hxx' => ?_⟩
  obtain ⟨c, hc⟩ := exists_cmb h𝔭 b k (Submodule.Quotient.mk x)
  rw [hc, end_apply_cmb b k X Y hXY c, mk_eq_iff] at hxx'
  rw [mk_eq_iff] at hc
  have e1 : g (x : V) - x' = g ((x : V) - (inA 𝔭 b (cmb b c) : V)) +
      (g (cmb b c : V) - (cmb b (Y *ᵥ c) : V)) - ((x' : V) - (inA 𝔭 b (cmb b (Y *ᵥ c)) : V)) := by
    rw [map_sub, coe_inA, coe_inA]
    abel
  rw [e1]
  exact sub_mem (add_mem (smul_mono_pow (Nat.sub_le k e) (aut_mem_smul hg _ hc)) (aut_cmb b hgY c))
    (smul_mono_pow (Nat.sub_le k e) hxx')

end Formalism.HermitianLattices.Ext.L3.HU

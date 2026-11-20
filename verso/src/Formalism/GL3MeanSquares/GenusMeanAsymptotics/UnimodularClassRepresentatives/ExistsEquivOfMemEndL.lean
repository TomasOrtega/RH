import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.ExistsMulDvdUnif
import Formalism.HermitianLattices.HermitianLatticesProofs.DualLattice

open NumberField Module

noncomputable section

namespace Formalism.HermitianLattices.Ext.L3.D2

variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
variable {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V]
  [IsScalarTower (𝓞 K) K V]

local notation "ι" => algebraMap (𝓞 F) (𝓞 K)

/- English proof (translation)
Rewrite using `[← algebraMap_smul K (ι (π ^ r)) w]`. Use `congr 1`. Rewrite using `[map_pow, map_pow]`. Both sides reduce to the same expression.
-/
theorem ι_pow_smul (π : 𝓞 F) (r : ℕ) (w : V) :
    ι (π ^ r) • w = algebraMap F K (π : F) ^ r • w := by
  rw [← algebraMap_smul K (ι (π ^ r)) w]
  congr 1
  rw [map_pow, map_pow]
  rfl

/- English proof (translation)
Use `h𝔭.isPrime` as an intermediate fact. Take `⟨n, hn, hnw⟩` from `Formalism.HermitianLatticesTheory.traceReal_mult A₀ hA₀ w`. Establish `hc : ((n : ℤ) : 𝓞 F) ≠ 0` using `by exact_mod_cast hn`. Take `⟨r, u, hu, hdvd⟩` from `exists_mul_dvd h𝔭 hc`. Take `⟨v, hv⟩` from `hdvd (π ^ r) (Ideal.pow_mem_pow hπ r)`.

Use `⟨r, (LocalSpans.mem_locF 𝔭 _ _).2 ⟨u, hu, ?_⟩⟩` and prove the remaining obligations. Establish `: ι u • (algebraMap F K (π : F) ^ r • w) = ι v • (n • w)`. Rewrite using `[← LocF.algebraMap_intCast_smul (K := K) (F := F) n w, smul_smul, ← map_mul, mul_comm v, ← hv, map_mul, mul_smul, ι_pow_smul]`. Rewrite using `[this]`. Conclude with `A₀.smul_mem _ hnw`.
-/
theorem exists_pow_smul_mem {A₀ : Submodule (𝓞 K) V} (hA₀ : Submodule.IsLattice K A₀)
    {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) {π : 𝓞 F} (hπ : π ∈ 𝔭) (w : V) :
    ∃ n : ℕ, algebraMap F K (π : F) ^ n • w ∈ locF 𝔭 A₀ := by
  have := h𝔭.isPrime
  obtain ⟨n, hn, hnw⟩ := Formalism.HermitianLatticesTheory.traceReal_mult A₀ hA₀ w
  have hc : ((n : ℤ) : 𝓞 F) ≠ 0 := by exact_mod_cast hn
  obtain ⟨r, u, hu, hdvd⟩ := exists_mul_dvd h𝔭 hc
  obtain ⟨v, hv⟩ := hdvd (π ^ r) (Ideal.pow_mem_pow hπ r)
  refine ⟨r, (LocalSpans.mem_locF 𝔭 _ _).2 ⟨u, hu, ?_⟩⟩
  have : ι u • (algebraMap F K (π : F) ^ r • w) = ι v • (n • w) := by
    rw [← LocF.algebraMap_intCast_smul (K := K) (F := F) n w, smul_smul, ← map_mul, mul_comm v, ← hv, map_mul,
      mul_smul, ι_pow_smul]
  rw [this]
  exact A₀.smul_mem _ hnw

/- English proof (translation)
Use `h𝔭.isPrime` as an intermediate fact. Take `⟨n, hn, hnx⟩` from `LocF.exists_zsmul_le hA₀ hB₀`. Establish `hc : ((n : ℤ) : 𝓞 F) ≠ 0` using `by exact_mod_cast hn`. Take `⟨r, u, hu, hdvd⟩` from `exists_mul_dvd h𝔭 hc`. Take `⟨π, hπ, hπ'⟩` from `exists_unif h𝔭`.

Take `⟨v, hv⟩` from `hdvd (π ^ r) (Ideal.pow_mem_pow hπ r)`. Use `⟨r, fun x hx => ?_⟩` and prove the remaining obligations. Take `⟨y, hy, rfl⟩` from `(mem_smul_iff_unif h𝔭 hπ hπ' A₀).1 hx`. Take `⟨t, ht, hty⟩` from `(LocalSpans.mem_locF 𝔭 A₀ y).1 hy`. Use `(LocalSpans.mem_locF 𝔭 _ _).2 ⟨u * t, fun h => (h𝔭.isPrime.mem_or_mem h).elim hu ht, ?_⟩` and prove the remaining obligations.

Establish `: ι (u * t) • (algebraMap F K (π : F) ^ r • y) = ι v • (n • (ι t • y))`. Rewrite using `[← LocF.algebraMap_intCast_smul (K := K) (F := F) n, ← ι_pow_smul, smul_smul, smul_smul, smul_smul, ← map_mul, ← map_mul, ← map_mul]`. Use `congr 2`. Take the linear combination `t * hv`. Rewrite using `[this]`.

Conclude with `B₀.smul_mem _ (hnx _ hty)`.
-/
theorem exists_smul_le {A₀ B₀ : Submodule (𝓞 K) V} (hA₀ : Submodule.IsLattice K A₀)
    (hB₀ : Submodule.IsLattice K B₀) {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) :
    ∃ r : ℕ, extP K 𝔭 ^ r • locF 𝔭 A₀ ≤ locF 𝔭 B₀ := by
  have := h𝔭.isPrime
  obtain ⟨n, hn, hnx⟩ := LocF.exists_zsmul_le hA₀ hB₀
  have hc : ((n : ℤ) : 𝓞 F) ≠ 0 := by exact_mod_cast hn
  obtain ⟨r, u, hu, hdvd⟩ := exists_mul_dvd h𝔭 hc
  obtain ⟨π, hπ, hπ'⟩ := exists_unif h𝔭
  obtain ⟨v, hv⟩ := hdvd (π ^ r) (Ideal.pow_mem_pow hπ r)
  refine ⟨r, fun x hx => ?_⟩
  obtain ⟨y, hy, rfl⟩ := (mem_smul_iff_unif h𝔭 hπ hπ' A₀).1 hx
  obtain ⟨t, ht, hty⟩ := (LocalSpans.mem_locF 𝔭 A₀ y).1 hy
  refine (LocalSpans.mem_locF 𝔭 _ _).2 ⟨u * t, fun h => (h𝔭.isPrime.mem_or_mem h).elim hu ht, ?_⟩
  have : ι (u * t) • (algebraMap F K (π : F) ^ r • y) = ι v • (n • (ι t • y)) := by
    rw [← LocF.algebraMap_intCast_smul (K := K) (F := F) n, ← ι_pow_smul, smul_smul, smul_smul, smul_smul,
      ← map_mul, ← map_mul, ← map_mul]
    congr 2
    linear_combination t * hv
  rw [this]
  exact B₀.smul_mem _ (hnx _ hty)

/- English proof (translation)
Use `h𝔭.isPrime` as an intermediate fact. Establish `h0 : v ∈ locF 𝔭 A₀` using `by simpa [pow_zero_smul] using hv 0`. Take `⟨t, ht, htv⟩` from `(LocalSpans.mem_locF 𝔭 A₀ v).1 h0`. Establish `h1 : ∀ j : ℕ, ι t • v ∈ extP K 𝔭 ^ j • A₀` using `fun j => localizedQuotients.mem_smul_of_mem_smul_locF h𝔭 A₀ j htv (Submodule.smul_mem _ _ (hv j))`. Establish `: Module.Finite (𝓞 K) ↥A₀` using `Module.Finite.iff_fg.2 hA₀.fg`.

Establish `h2 : (⟨ι t • v, htv⟩ : ↥A₀) ∈ (⨅ i : ℕ, extP K 𝔭 ^ i • ⊤ : Submodule (𝓞 K) ↥A₀)`. Rewrite using `[Submodule.mem_iInf]`. Introduce `j`. Rewrite using `[Submodule.mem_smul_top_iff]`. Conclude with `h1 j`.

Take `⟨r, hr⟩` from `(Ideal.mem_iInf_smul_pow_eq_bot_iff (extP K 𝔭) _).1 h2`. Establish `hr' : (r : 𝓞 K) • (ι t • v) = ι t • v` using `congrArg Subtype.val hr`. Establish `hr1 : (r : 𝓞 K) ≠ 1`. Introduce `e`. Establish `h3 : (1 : 𝓞 K) ∈ extP K 𝔭 ^ 1` using `by rw [pow_one, ← e]; exact r.2`.

Establish `h4 : (1 : 𝓞 F) ∈ 𝔭 ^ 1` using `(idealPowerSpanBounds.mem_pow_iff (K := K) 𝔭 1 1).1 (by simpa using h3)`. Conclude with `h𝔭.ne_top ((Ideal.eq_top_iff_one _).2 (by simpa using h4))`. Establish `h5 : (algebraMap (𝓞 K) K ((r : 𝓞 K) - 1) * algebraMap F K (t : F)) • v = 0`. Rewrite using `[mul_smul, ← MeanB.algebraMap_comp, algebraMap_smul, algebraMap_smul, sub_smul, hr', one_smul, sub_self]`. Break down `smul_eq_zero.1 h5 with h6 | h6` into its components or cases.

Break down `mul_eq_zero.1 h6 with h7 | h7` into its components or cases. Conclude with `absurd (sub_eq_zero.1 ((map_eq_zero_iff _ (FaithfulSMul.algebraMap_injective (𝓞 K) K)).1 h7)) hr1`. Conclude with `absurd h7 (notMem_ne_zero ht)`. Conclude with `h6`.
-/
theorem eq_zero_of_forall_mem {A₀ : Submodule (𝓞 K) V} (hA₀ : Submodule.IsLattice K A₀)
    {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) {v : V} (hv : ∀ j : ℕ, v ∈ extP K 𝔭 ^ j • locF 𝔭 A₀) :
    v = 0 := by
  have := h𝔭.isPrime
  have h0 : v ∈ locF 𝔭 A₀ := by simpa [pow_zero_smul] using hv 0
  obtain ⟨t, ht, htv⟩ := (LocalSpans.mem_locF 𝔭 A₀ v).1 h0
  have h1 : ∀ j : ℕ, ι t • v ∈ extP K 𝔭 ^ j • A₀ := fun j =>
    localizedQuotients.mem_smul_of_mem_smul_locF h𝔭 A₀ j htv (Submodule.smul_mem _ _ (hv j))
  have : Module.Finite (𝓞 K) ↥A₀ := Module.Finite.iff_fg.2 hA₀.fg
  have h2 : (⟨ι t • v, htv⟩ : ↥A₀) ∈ (⨅ i : ℕ, extP K 𝔭 ^ i • ⊤ : Submodule (𝓞 K) ↥A₀) := by
    rw [Submodule.mem_iInf]
    intro j
    rw [Submodule.mem_smul_top_iff]
    exact h1 j
  obtain ⟨r, hr⟩ := (Ideal.mem_iInf_smul_pow_eq_bot_iff (extP K 𝔭) _).1 h2
  have hr' : (r : 𝓞 K) • (ι t • v) = ι t • v := congrArg Subtype.val hr
  have hr1 : (r : 𝓞 K) ≠ 1 := by
    intro e
    have h3 : (1 : 𝓞 K) ∈ extP K 𝔭 ^ 1 := by rw [pow_one, ← e]; exact r.2
    have h4 : (1 : 𝓞 F) ∈ 𝔭 ^ 1 := (idealPowerSpanBounds.mem_pow_iff (K := K) 𝔭 1 1).1 (by simpa using h3)
    exact h𝔭.ne_top ((Ideal.eq_top_iff_one _).2 (by simpa using h4))
  have h5 : (algebraMap (𝓞 K) K ((r : 𝓞 K) - 1) * algebraMap F K (t : F)) • v = 0 := by
    rw [mul_smul, ← MeanB.algebraMap_comp, algebraMap_smul, algebraMap_smul, sub_smul, hr', one_smul,
      sub_self]
  rcases smul_eq_zero.1 h5 with h6 | h6
  · rcases mul_eq_zero.1 h6 with h7 | h7
    · exact absurd (sub_eq_zero.1 ((map_eq_zero_iff _ (FaithfulSMul.algebraMap_injective (𝓞 K) K)).1 h7)) hr1
    · exact absurd h7 (notMem_ne_zero ht)
  · exact h6

/- English proof (translation)
Use `⟨1, Submonoid.one_mem _, ?_⟩` and prove the remaining obligations. Rewrite using `[one_smul]`. Use `⟨ι (π ^ k), by simp, ?_⟩` and prove the remaining obligations. Use `show algebraMap (𝓞 K) K (ι (π ^ k)) = _`. Rewrite using `[map_pow, map_pow]`.

Both sides reduce to the same expression.
-/
theorem unif_pow_mem_pK_zero {𝔭 : Ideal (𝓞 F)} {π : 𝓞 F} (hπ : π ∈ 𝔭) (k : ℕ) :
    algebraMap F K (π : F) ^ k ∈ pK K 𝔭 0 := by
  refine ⟨1, Submonoid.one_mem _, ?_⟩
  rw [one_smul]
  refine ⟨ι (π ^ k), by simp, ?_⟩
  show algebraMap (𝓞 K) K (ι (π ^ k)) = _
  rw [map_pow, map_pow]
  rfl

/- English proof (translation)
Take `⟨π, hπ, hπ'⟩` from `exists_unif h𝔭`. Establish `hπ0` using `unif_ne_zero (K := K) hπ'`. Use `set p : K := algebraMap F K (π : F) with hp`. Establish `key : ∀ w : V, w + D w ∈ locF 𝔭 A₀ → w ∈ locF 𝔭 A₀`. Introduce `w hw`.

Take `⟨n, hn⟩` from `exists_pow_smul_mem hA₀ h𝔭 hπ w`. Proceed by induction on `n with`. Consider the case `zero => simpa using hn`. Consider the case `succ n ih`. Apply `ih` to reduce the goal to its premises.

Establish `h1 : D (p ^ (n + 1) • w) ∈ extP K 𝔭 ^ 1 • locF 𝔭 A₀`. Rewrite using `[pow_one]`. Conclude with `hD _ hn`. Establish `h2 : p ^ (n + 1) • (w + D w) ∈ extP K 𝔭 ^ 1 • locF 𝔭 A₀` using `(mem_smul_iff_unif h𝔭 hπ hπ' A₀).2 ⟨p ^ n • (w + D w), smul_mem_locF h𝔭 A₀ (unif_pow_mem_pK_zero hπ n) hw, by rw [smul_smul, pow_one, pow_succ']⟩`. Establish `h3 : p ^ (n + 1) • w ∈ extP K 𝔭 ^ 1 • locF 𝔭 A₀`.

Use `sub_mem h2 h1` as an intermediate fact. Rewrite `this` using `[map_smul, smul_add, add_sub_cancel_right]`. Then use the resulting hypothesis. Take `⟨y, hy, e⟩` from `(mem_smul_iff_unif h𝔭 hπ hπ' A₀).1 h3`. Establish `: p ^ n • w = y`. Apply `smul_right_injective V hπ0` to reduce the goal to its premises.

Use `show p • p ^ n • w = p • y`. Rewrite using `[smul_smul, ← pow_succ', e, pow_one]`. Rewrite using `[this]` and apply the resulting hypothesis. Take `⟨y, hy, e⟩` from `(mem_smul_iff_unif h𝔭 hπ hπ' A₀).1 hw`. Use `(mem_smul_iff_unif h𝔭 hπ hπ' A₀).2 ⟨(p ^ j)⁻¹ • w, key _ ?_, ?_⟩` and prove the remaining obligations.

Rewrite using `[map_smul, ← smul_add, e, smul_smul, inv_mul_cancel₀ (pow_ne_zero j hπ0), one_smul]`. Conclude with `hy`. Rewrite using `[smul_smul, mul_inv_cancel₀ (pow_ne_zero j hπ0), one_smul]`.
-/
theorem mem_of_add_mem {A₀ : Submodule (𝓞 K) V} (hA₀ : Submodule.IsLattice K A₀)
    {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) {D : V →ₗ[K] V}
    (hD : D ∈ endL (locF 𝔭 A₀) (extP K 𝔭 • locF 𝔭 A₀)) (j : ℕ) {w : V}
    (hw : w + D w ∈ extP K 𝔭 ^ j • locF 𝔭 A₀) : w ∈ extP K 𝔭 ^ j • locF 𝔭 A₀ := by
  obtain ⟨π, hπ, hπ'⟩ := exists_unif h𝔭
  have hπ0 := unif_ne_zero (K := K) hπ'
  set p : K := algebraMap F K (π : F) with hp
  have key : ∀ w : V, w + D w ∈ locF 𝔭 A₀ → w ∈ locF 𝔭 A₀ := by
    intro w hw
    obtain ⟨n, hn⟩ := exists_pow_smul_mem hA₀ h𝔭 hπ w
    induction n with
    | zero => simpa using hn
    | succ n ih =>
      apply ih
      have h1 : D (p ^ (n + 1) • w) ∈ extP K 𝔭 ^ 1 • locF 𝔭 A₀ := by
        rw [pow_one]; exact hD _ hn
      have h2 : p ^ (n + 1) • (w + D w) ∈ extP K 𝔭 ^ 1 • locF 𝔭 A₀ :=
        (mem_smul_iff_unif h𝔭 hπ hπ' A₀).2 ⟨p ^ n • (w + D w),
          smul_mem_locF h𝔭 A₀ (unif_pow_mem_pK_zero hπ n) hw, by rw [smul_smul, pow_one, pow_succ']⟩
      have h3 : p ^ (n + 1) • w ∈ extP K 𝔭 ^ 1 • locF 𝔭 A₀ := by
        have := sub_mem h2 h1
        rwa [map_smul, smul_add, add_sub_cancel_right] at this
      obtain ⟨y, hy, e⟩ := (mem_smul_iff_unif h𝔭 hπ hπ' A₀).1 h3
      have : p ^ n • w = y := by
        apply smul_right_injective V hπ0
        show p • p ^ n • w = p • y
        rw [smul_smul, ← pow_succ', e, pow_one]
      rwa [this]
  obtain ⟨y, hy, e⟩ := (mem_smul_iff_unif h𝔭 hπ hπ' A₀).1 hw
  refine (mem_smul_iff_unif h𝔭 hπ hπ' A₀).2 ⟨(p ^ j)⁻¹ • w, key _ ?_, ?_⟩
  · rw [map_smul, ← smul_add, e, smul_smul, inv_mul_cancel₀ (pow_ne_zero j hπ0), one_smul]
    exact hy
  · rw [smul_smul, mul_inv_cancel₀ (pow_ne_zero j hπ0), one_smul]

/- English proof (translation)
Establish `hinj : Function.Injective (LinearMap.id + D : V →ₗ[K] V)`. Rewrite using `[← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']`. Introduce `w hw`. Establish `hw' : w + D w = 0` using `hw`. Conclude with `eq_zero_of_forall_mem hA₀ h𝔭 fun j => mem_of_add_mem hA₀ h𝔭 hD j (by rw [hw']; exact zero_mem _)`.

Use `⟨LinearEquiv.ofInjectiveEndo _ hinj, fun x => ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[LinearEquiv.coe_ofInjectiveEndo]`. Both sides reduce to the same expression. Establish `hX : ∀ x, LinearEquiv.ofInjectiveEndo _ hinj x = x + D x` using `fun x => by`. Rewrite using `[LinearEquiv.coe_ofInjectiveEndo]`.

Both sides reduce to the same expression. Rewrite using `[mem_glSub]`. Apply `le_antisymm` to reduce the goal to its premises. Introduce and unpack `_ ⟨x, hx, rfl⟩ show LinearEquiv.ofInjectiveEndo _ hinj x ∈ _`. Rewrite using `[hX]`.

Conclude with `add_mem hx (Submodule.smul_le_right (hD x hx))`. Introduce `y hy`. Use `⟨(LinearEquiv.ofInjectiveEndo _ hinj).symm y, ?_, LinearEquiv.apply_symm_apply _ y⟩` and prove the remaining obligations. Establish `h1` using `hX ((LinearEquiv.ofInjectiveEndo _ hinj).symm y)`. Rewrite `h1` using `[LinearEquiv.apply_symm_apply]`.

Use `mem_of_add_mem hA₀ h𝔭 hD 0 (w := (LinearEquiv.ofInjectiveEndo _ hinj).symm y) (by rw [← h1, pow_zero_smul]; exact hy)` as an intermediate fact. Rewrite `this` using `[pow_zero_smul]`. Then use the resulting hypothesis.
-/
theorem exists_equiv_of_mem_endL {A₀ : Submodule (𝓞 K) V} (hA₀ : Submodule.IsLattice K A₀)
    {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) {D : V →ₗ[K] V}
    (hD : D ∈ endL (locF 𝔭 A₀) (extP K 𝔭 • locF 𝔭 A₀)) :
    ∃ X : V ≃ₗ[K] V, (∀ x, X x = x + D x) ∧ X ∈ glSub (locF 𝔭 A₀) := by
  have hinj : Function.Injective (LinearMap.id + D : V →ₗ[K] V) := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro w hw
    have hw' : w + D w = 0 := hw
    exact eq_zero_of_forall_mem hA₀ h𝔭 fun j =>
      mem_of_add_mem hA₀ h𝔭 hD j (by rw [hw']; exact zero_mem _)
  refine ⟨LinearEquiv.ofInjectiveEndo _ hinj, fun x => ?_, ?_⟩
  · rw [LinearEquiv.coe_ofInjectiveEndo]; rfl
  · have hX : ∀ x, LinearEquiv.ofInjectiveEndo _ hinj x = x + D x := fun x => by
      rw [LinearEquiv.coe_ofInjectiveEndo]; rfl
    rw [mem_glSub]
    apply le_antisymm
    · rintro _ ⟨x, hx, rfl⟩
      show LinearEquiv.ofInjectiveEndo _ hinj x ∈ _
      rw [hX]
      exact add_mem hx (Submodule.smul_le_right (hD x hx))
    · intro y hy
      refine ⟨(LinearEquiv.ofInjectiveEndo _ hinj).symm y, ?_, LinearEquiv.apply_symm_apply _ y⟩
      have h1 := hX ((LinearEquiv.ofInjectiveEndo _ hinj).symm y)
      rw [LinearEquiv.apply_symm_apply] at h1
      have := mem_of_add_mem hA₀ h𝔭 hD 0 (w := (LinearEquiv.ofInjectiveEndo _ hinj).symm y)
        (by rw [← h1, pow_zero_smul]; exact hy)
      rwa [pow_zero_smul] at this

/- English proof (translation)
Take `⟨Y, hY, hY'⟩` from `exists_equiv_of_mem_endL hA₀ h𝔭 (D := (X : V →ₗ[K] V) - LinearMap.id) (fun x hx => hX x hx)`. Establish `: X = Y`. Use extensionality with `x`. Rewrite using `[hY]`. Simplify using the standard rewrite rules.

Rewrite using `[this]` and apply the resulting hypothesis.
-/
theorem mem_glSub_of_sub_mem {A₀ : Submodule (𝓞 K) V} (hA₀ : Submodule.IsLattice K A₀)
    {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) {X : V ≃ₗ[K] V}
    (hX : ∀ x ∈ locF 𝔭 A₀, X x - x ∈ extP K 𝔭 • locF 𝔭 A₀) : X ∈ glSub (locF 𝔭 A₀) := by
  obtain ⟨Y, hY, hY'⟩ := exists_equiv_of_mem_endL hA₀ h𝔭
    (D := (X : V →ₗ[K] V) - LinearMap.id) (fun x hx => hX x hx)
  have : X = Y := by
    ext x
    rw [hY]
    simp
  rwa [this]

end Formalism.HermitianLattices.Ext.L3.D2

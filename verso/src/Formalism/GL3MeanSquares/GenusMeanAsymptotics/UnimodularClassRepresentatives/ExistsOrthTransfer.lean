import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.ExistsIsomScale

noncomputable section

namespace Formalism.HermitianLattices.Ext.L3.U0

open WA Module

variable {K V : Type*} [Field K] [StarRing K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V]

variable {S : Subring K} {π : K} {h : V →ₗ⋆[K] V →ₗ[K] K}

/- English proof (translation)
Unfold `cutW`. Apply `Submodule.finrank_lt_finrank_of_lt` to reduce the goal to its premises. Use `lt_of_le_of_ne inf_le_left fun heq => hxx ?_` and prove the remaining obligations. Establish `hmem : x ∈ W ⊓ LinearMap.ker (h x)`. Rewrite using `[heq]`.

Conclude with `hx`. Conclude with `LinearMap.mem_ker.mp (Submodule.mem_inf.mp hmem).2`.
-/
theorem finrank_cutW_lt {W : Submodule K V} {x : V} (hx : x ∈ W) (hxx : h x x ≠ 0) :
    finrank K (cutW h W x) < finrank K W := by
  unfold cutW
  apply Submodule.finrank_lt_finrank_of_lt
  refine lt_of_le_of_ne inf_le_left fun heq => hxx ?_
  have hmem : x ∈ W ⊓ LinearMap.ker (h x) := by
    rw [heq]
    exact hx
  exact LinearMap.mem_ker.mp (Submodule.mem_inf.mp hmem).2

/- English proof (translation)
Proceed by induction on `n with`. Consider the case `zero`. Introduce `W₁ W₂ M N φ hn hM hN hφ hW`. Establish `hbot : W₁ = ⊥` using `Submodule.finrank_eq_zero.mp (Nat.le_zero.mp hn)`. Use `⟨φ, hφ, fun _ _ => rfl, fun v => ⟨fun hv => ?_, fun hv => ?_⟩⟩` and prove the remaining obligations.

Establish `: v = 0`. Use `hM.le v hv` as an intermediate fact. Rewrite `this` using `[hbot, Submodule.mem_bot]`. Then use the resulting hypothesis. Rewrite using `[this, map_zero]`. Conclude with `N.zero_mem`.

Establish `: v = 0`. Use `(hW v).mpr (hN.le _ hv)` as an intermediate fact. Rewrite `this` using `[hbot, Submodule.mem_bot]`. Then use the resulting hypothesis. Rewrite using `[this]`. Conclude with `M.zero_mem`.

Consider the case `succ n ih`. Introduce `W₁ W₂ M N φ hn hM hN hφ hW`. Distinguish the cases in `hbot : W₁ = ⊥`. Conclude with `ih W₁ W₂ M N φ (by rw [hbot]; simp) hM hN hφ hW`. Take `⟨ξ, hξ, hξ0⟩` from `Submodule.exists_mem_ne_zero_of_ne_bot hbot`.

Establish `hφ' : ∀ a b, h (φ a) (φ b) = h a b` using `hφ`. Take `⟨x, hx, hu⟩` from `hM.exists_unit_norm hS hπ hs hd hξ hξ0`. Take `⟨X, hX, hXu⟩` from `hN.exists_norm hS hπ hs hd ((hW x).mp (hM.le x hx)) hu (hφ' x x)`. Take `⟨φ', hφ'i, hφ'x, hφ'W, hφ'fix⟩` from `exists_prep hs hd hφ hW (hM.le x hx) (hN.le X hX) hXu.symm`. Take `⟨g, hg, hgfix, hgM⟩` from `ih _ _ _ _ φ' (by have := finrank_cutW_lt (h := h) (hM.le x hx) hu.1; omega) (hM.cut hx hu) (hN.cut hX (by rw [hXu]; exact hu)) hφ'i hφ'W`.

Establish `hgx : g x = X`. Rewrite using `[hgfix x fun w hw => symm_zero hs (mem_cutW.mp hw).2, hφ'x]`. Use `⟨g, hg, fun v hv => ?_, mem_iff_of_cut hM.toIsLatIn hN.toIsLatIn hx hX hu hg hgx hgM⟩` and prove the remaining obligations. Rewrite using `[hgfix v fun w hw => hv w (mem_cutW.mp hw).1, hφ'fix v hv]`.
-/
theorem sd_main (hS : IsHermSemilocal S) (hπ : IsUnif S π) (hs : h.IsSymm)
    (hd : ∀ x, h x x = 0 → x = 0) (n : ℕ) :
    ∀ (W₁ W₂ : Submodule K V) (M N : AddSubgroup V) (φ : V ≃ₗ[K] V), finrank K W₁ ≤ n →
      IsSD S h W₁ M → IsSD S h W₂ N → φ ∈ Formalism.HermitianLatticesTheory.isom h → (∀ v, v ∈ W₁ ↔ φ v ∈ W₂) →
      ∃ g ∈ Formalism.HermitianLatticesTheory.isom h, (∀ v, (∀ w ∈ W₁, h w v = 0) → g v = φ v) ∧ ∀ v, v ∈ M ↔ g v ∈ N := by
  induction n with
  | zero =>
    intro W₁ W₂ M N φ hn hM hN hφ hW
    have hbot : W₁ = ⊥ := Submodule.finrank_eq_zero.mp (Nat.le_zero.mp hn)
    refine ⟨φ, hφ, fun _ _ => rfl, fun v => ⟨fun hv => ?_, fun hv => ?_⟩⟩
    · have : v = 0 := by
        have := hM.le v hv
        rwa [hbot, Submodule.mem_bot] at this
      rw [this, map_zero]
      exact N.zero_mem
    · have : v = 0 := by
        have := (hW v).mpr (hN.le _ hv)
        rwa [hbot, Submodule.mem_bot] at this
      rw [this]
      exact M.zero_mem
  | succ n ih =>
    intro W₁ W₂ M N φ hn hM hN hφ hW
    by_cases hbot : W₁ = ⊥
    · exact ih W₁ W₂ M N φ (by rw [hbot]; simp) hM hN hφ hW
    obtain ⟨ξ, hξ, hξ0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hbot
    have hφ' : ∀ a b, h (φ a) (φ b) = h a b := hφ
    obtain ⟨x, hx, hu⟩ := hM.exists_unit_norm hS hπ hs hd hξ hξ0
    obtain ⟨X, hX, hXu⟩ := hN.exists_norm hS hπ hs hd ((hW x).mp (hM.le x hx)) hu (hφ' x x)
    obtain ⟨φ', hφ'i, hφ'x, hφ'W, hφ'fix⟩ := exists_prep hs hd hφ hW (hM.le x hx) (hN.le X hX)
      hXu.symm
    obtain ⟨g, hg, hgfix, hgM⟩ := ih _ _ _ _ φ'
      (by have := finrank_cutW_lt (h := h) (hM.le x hx) hu.1; omega)
      (hM.cut hx hu) (hN.cut hX (by rw [hXu]; exact hu)) hφ'i hφ'W
    have hgx : g x = X := by
      rw [hgfix x fun w hw => symm_zero hs (mem_cutW.mp hw).2, hφ'x]
    refine ⟨g, hg, fun v hv => ?_, mem_iff_of_cut hM.toIsLatIn hN.toIsLatIn hx hX hu hg hgx hgM⟩
    rw [hgfix v fun w hw => hv w (mem_cutW.mp hw).1, hφ'fix v hv]

/- English proof (translation)
Establish `ha : ψ z₁ ∈ W₂` using `hW z₁ hz₁`. Establish `hb : ψ ξ ∈ W₂` using `hW ξ hξ`. Establish `haa : h (ψ z₁) (ψ z₁) ≠ 0`. Rewrite using `[hψ]`. Conclude with `fun h0 => hz₁0 (hd z₁ h0)`.

Establish `hb0 : ψ ξ ≠ 0` using `fun h0 => hξ0 (ψ.injective (h0.trans (map_zero ψ).symm))`. Establish `hab : h (ψ z₁) (ψ ξ) = 0`. Rewrite using `[hψ]`. Conclude with `hzξ`. Distinguish the cases in `h0 : h z₂ (ψ z₁) = 0`.

Conclude with `⟨ψ z₁, ha, fun ha0 => haa (by simp [ha0]), h0⟩`. Use `⟨(h z₂ (ψ ξ)) • ψ z₁ - (h z₂ (ψ z₁)) • ψ ξ, W₂.sub_mem (W₂.smul_mem _ ha) (W₂.smul_mem _ hb), ?_, ?_⟩` and prove the remaining obligations. Introduce `heq`. Establish `hc` using `congrArg (h (ψ z₁)) heq`. Simplify using `only [map_sub, map_smul, smul_eq_mul, hab, mul_zero, sub_zero, map_zero] at hc`.

Break down `mul_eq_zero.mp hc with hb' | hb'` into its components or cases. Rewrite `heq` using `[hb', zero_smul, zero_sub, neg_eq_zero, smul_eq_zero]`. Conclude with `heq.elim h0 hb0`. Conclude with `haa hb'`. Simplify using `only [map_sub, map_smul, smul_eq_mul]`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem exists_orth_transfer (hd : ∀ x, h x x = 0 → x = 0) {W₁ W₂ : Submodule K V}
    {ψ : V ≃ₗ[K] V} (hψ : ∀ a b, h (ψ a) (ψ b) = h a b) (hW : ∀ v ∈ W₁, ψ v ∈ W₂) {z₁ z₂ ξ : V}
    (hz₁ : z₁ ∈ W₁) (hz₁0 : z₁ ≠ 0) (hz₂ : z₂ ∈ W₂) (hz₂0 : z₂ ≠ 0) (hξ : ξ ∈ W₁) (hξ0 : ξ ≠ 0)
    (hzξ : h z₁ ξ = 0) : ∃ η ∈ W₂, η ≠ 0 ∧ h z₂ η = 0 := by
  have ha : ψ z₁ ∈ W₂ := hW z₁ hz₁
  have hb : ψ ξ ∈ W₂ := hW ξ hξ
  have haa : h (ψ z₁) (ψ z₁) ≠ 0 := by
    rw [hψ]
    exact fun h0 => hz₁0 (hd z₁ h0)
  have hb0 : ψ ξ ≠ 0 := fun h0 => hξ0 (ψ.injective (h0.trans (map_zero ψ).symm))
  have hab : h (ψ z₁) (ψ ξ) = 0 := by
    rw [hψ]
    exact hzξ
  by_cases h0 : h z₂ (ψ z₁) = 0
  · exact ⟨ψ z₁, ha, fun ha0 => haa (by simp [ha0]), h0⟩
  · refine ⟨(h z₂ (ψ ξ)) • ψ z₁ - (h z₂ (ψ z₁)) • ψ ξ,
      W₂.sub_mem (W₂.smul_mem _ ha) (W₂.smul_mem _ hb), ?_, ?_⟩
    · intro heq
      have hc := congrArg (h (ψ z₁)) heq
      simp only [map_sub, map_smul, smul_eq_mul, hab, mul_zero, sub_zero, map_zero] at hc
      rcases mul_eq_zero.mp hc with hb' | hb'
      · rw [hb', zero_smul, zero_sub, neg_eq_zero, smul_eq_zero] at heq
        exact heq.elim h0 hb0
      · exact haa hb'
    · simp only [map_sub, map_smul, smul_eq_mul]
      ring

/- English proof (translation)
Introduce `hz`. Conclude with `hM.z_norm_ne (by simp [hz])`.
-/
theorem IsASD.z_ne {W : Submodule K V} {M : AddSubgroup V} {z : V} (hM : IsASD S π h W M z) :
    z ≠ 0 := by
  intro hz
  exact hM.z_norm_ne (by simp [hz])

/- English proof (translation)
Establish `hζ` using `hM.z_norm_ne`. Establish `h1 : ∀ v ∈ W, v = (h z v * (h z z)⁻¹) • z`. Introduce `v hv`. Assume the negation of the conclusion as `hne`. Apply `hline` to reduce the goal to its premises.

Use `⟨v - (h z v * (h z z)⁻¹) • z, W.sub_mem hv (W.smul_mem _ (hM.le z hM.z_mem)), sub_ne_zero.mpr hne, ?_⟩` and prove the remaining obligations. Simplify using `only [map_sub, map_smul, smul_eq_mul]`. Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree. Use `⟨h1, fun v => ⟨fun hv => ?_, ?_⟩⟩` and prove the remaining obligations.

Conclude with `⟨_, mul_inv_mem_of_dv hπ (hM.z_rad v hv) hM.z_norm, h1 v (hM.le v hv)⟩`. Introduce and unpack `⟨c, hc, rfl⟩`. Conclude with `hM.smul_mem c hc z hM.z_mem`.
-/
theorem IsASD.mem_iff_of_line (hπ : IsUnif S π) {W : Submodule K V} {M : AddSubgroup V} {z : V}
    (hM : IsASD S π h W M z) (hline : ¬ ∃ ξ ∈ W, ξ ≠ 0 ∧ h z ξ = 0) :
    (∀ v ∈ W, v = (h z v * (h z z)⁻¹) • z) ∧ ∀ v, v ∈ M ↔ ∃ c ∈ S, v = c • z := by
  have hζ := hM.z_norm_ne
  have h1 : ∀ v ∈ W, v = (h z v * (h z z)⁻¹) • z := by
    intro v hv
    by_contra hne
    apply hline
    refine ⟨v - (h z v * (h z z)⁻¹) • z, W.sub_mem hv (W.smul_mem _ (hM.le z hM.z_mem)),
      sub_ne_zero.mpr hne, ?_⟩
    simp only [map_sub, map_smul, smul_eq_mul]
    field_simp
    ring
  refine ⟨h1, fun v => ⟨fun hv => ?_, ?_⟩⟩
  · exact ⟨_, mul_inv_mem_of_dv hπ (hM.z_rad v hv) hM.z_norm, h1 v (hM.le v hv)⟩
  · rintro ⟨c, hc, rfl⟩
    exact hM.smul_mem c hc z hM.z_mem

/- English proof (translation)
Establish `hφ' : ∀ a b, h (φ a) (φ b) = h a b` using `hφ`. Take `⟨-, hMl⟩` from `hM.mem_iff_of_line hπ h1`. Take `⟨hW₂l, hNl⟩` from `hN.mem_iff_of_line hπ h2`. Establish `hζ₂` using `hN.z_norm_ne`. Take `⟨l, hl⟩ : ∃ l : K, φ z₁ = l • z₂` from `⟨_, hW₂l _ ((hW z₁).mp (hM.le _ hM.z_mem))⟩`.

Establish `hnorm : h z₁ z₁ = star l * l * h z₂ z₂`. Rewrite using `[← hφ', hl]`. Simplify using `only [map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul, starRingEnd_apply, RingHom.id_apply]`. Expand and normalize the polynomial expressions, which then agree. Establish `hNl' : IsUnitIn S (star l * l)`.

Establish `e : star l * l = h z₁ z₁ * π⁻¹ * (h z₂ z₂ * π⁻¹)⁻¹`. Rewrite using `[hnorm]`. Use `hπ.ne` as an intermediate fact. Clear the denominators using the available nonvanishing facts. Rewrite using `[e]`.

Conclude with `unit_mul hM.z_norm (unit_inv hN.z_norm)`. Take `⟨b, hb, hlb⟩` from `exists_norm_one_mul_mem hS hNl'.2.1`. Establish `hlbu : IsUnitIn S (l * b)`. Apply `isUnitIn_of_mul (hS.star_mem _ hlb) hlb` to reduce the goal to its premises. Establish `e : star (l * b) * (l * b) = star l * l`.

Rewrite using `[star_mul']`. Take the linear combination `(star l * l) * hb`. Rewrite using `[e]`. Conclude with `hNl'`. Take `⟨ψ, hψ, hψz, hψfix⟩` from `exists_isom_scale hs hζ₂ hb`.

Establish `hgz : ψ (φ z₁) = (l * b) • z₂` using `by rw [hl, map_smul, hψz, smul_smul]`. Use `⟨ψ * φ, mul_mem hψ hφ, fun v hv => ?_, fun v => ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `ψ (φ v) = φ v`. Apply `hψfix` to reduce the goal to its premises. Establish `h3 : φ.symm z₂ ∈ W₁` using `by rw [hW, φ.apply_symm_apply]; exact hN.le _ hN.z_mem`.

Use `hv _ h3` as an intermediate fact. Rewrite `this` using `[← hφ', φ.apply_symm_apply]`. Then use the resulting hypothesis. Express the relevant statement in the definitionally equal form `v ∈ M ↔ ψ (φ v) ∈ N`. Rewrite using `[hMl, hNl]`. Prove the components needed by the constructor for the conclusion.

Introduce and unpack `⟨c, hc, rfl⟩`. Conclude with `⟨c * (l * b), S.mul_mem hc hlb, by rw [map_smul, map_smul, hgz, smul_smul]⟩`. Introduce and unpack `⟨c, hc, hv⟩`. Use `⟨c * (l * b)⁻¹, S.mul_mem hc hlbu.2.2, ?_⟩` and prove the remaining obligations. Apply `φ.injective` to reduce the goal to its premises.

Apply `ψ.injective` to reduce the goal to its premises. Rewrite using `[hv, map_smul, map_smul, hgz, smul_smul, mul_assoc, inv_mul_cancel₀ hlbu.1, mul_one]`.
-/
theorem asd_base (hS : IsHermSemilocal S) (hπ : IsUnif S π) (hs : h.IsSymm)
    {W₁ W₂ : Submodule K V} {M N : AddSubgroup V} {z₁ z₂ : V} {φ : V ≃ₗ[K] V}
    (hM : IsASD S π h W₁ M z₁) (hN : IsASD S π h W₂ N z₂) (hφ : φ ∈ Formalism.HermitianLatticesTheory.isom h)
    (hW : ∀ v, v ∈ W₁ ↔ φ v ∈ W₂) (h1 : ¬ ∃ ξ ∈ W₁, ξ ≠ 0 ∧ h z₁ ξ = 0)
    (h2 : ¬ ∃ ξ ∈ W₂, ξ ≠ 0 ∧ h z₂ ξ = 0) :
    ∃ g ∈ Formalism.HermitianLatticesTheory.isom h, (∀ v, (∀ w ∈ W₁, h w v = 0) → g v = φ v) ∧ ∀ v, v ∈ M ↔ g v ∈ N := by
  have hφ' : ∀ a b, h (φ a) (φ b) = h a b := hφ
  obtain ⟨-, hMl⟩ := hM.mem_iff_of_line hπ h1
  obtain ⟨hW₂l, hNl⟩ := hN.mem_iff_of_line hπ h2
  have hζ₂ := hN.z_norm_ne
  obtain ⟨l, hl⟩ : ∃ l : K, φ z₁ = l • z₂ := ⟨_, hW₂l _ ((hW z₁).mp (hM.le _ hM.z_mem))⟩
  have hnorm : h z₁ z₁ = star l * l * h z₂ z₂ := by
    rw [← hφ', hl]
    simp only [map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul, starRingEnd_apply, RingHom.id_apply]
    ring
  have hNl' : IsUnitIn S (star l * l) := by
    have e : star l * l = h z₁ z₁ * π⁻¹ * (h z₂ z₂ * π⁻¹)⁻¹ := by
      rw [hnorm]
      have := hπ.ne
      field_simp
    rw [e]
    exact unit_mul hM.z_norm (unit_inv hN.z_norm)
  obtain ⟨b, hb, hlb⟩ := exists_norm_one_mul_mem hS hNl'.2.1
  have hlbu : IsUnitIn S (l * b) := by
    apply isUnitIn_of_mul (hS.star_mem _ hlb) hlb
    have e : star (l * b) * (l * b) = star l * l := by
      rw [star_mul']
      linear_combination (star l * l) * hb
    rw [e]
    exact hNl'
  obtain ⟨ψ, hψ, hψz, hψfix⟩ := exists_isom_scale hs hζ₂ hb
  have hgz : ψ (φ z₁) = (l * b) • z₂ := by rw [hl, map_smul, hψz, smul_smul]
  refine ⟨ψ * φ, mul_mem hψ hφ, fun v hv => ?_, fun v => ?_⟩
  · change ψ (φ v) = φ v
    apply hψfix
    have h3 : φ.symm z₂ ∈ W₁ := by rw [hW, φ.apply_symm_apply]; exact hN.le _ hN.z_mem
    have := hv _ h3
    rwa [← hφ', φ.apply_symm_apply] at this
  · change v ∈ M ↔ ψ (φ v) ∈ N
    rw [hMl, hNl]
    constructor
    · rintro ⟨c, hc, rfl⟩
      exact ⟨c * (l * b), S.mul_mem hc hlb, by rw [map_smul, map_smul, hgz, smul_smul]⟩
    · rintro ⟨c, hc, hv⟩
      refine ⟨c * (l * b)⁻¹, S.mul_mem hc hlbu.2.2, ?_⟩
      apply φ.injective
      apply ψ.injective
      rw [hv, map_smul, map_smul, hgz, smul_smul, mul_assoc, inv_mul_cancel₀ hlbu.1, mul_one]

/- English proof (translation)
Proceed by induction on `n with`. Consider the case `zero`. Introduce `W₁ W₂ M N z₁ z₂ φ hn hM hN hφ hW`. It suffices to derive a contradiction. Establish `hbot : W₁ = ⊥` using `Submodule.finrank_eq_zero.mp (Nat.le_zero.mp hn)`.

Use `hM.le _ hM.z_mem` as an intermediate fact. Rewrite `this` using `[hbot, Submodule.mem_bot]`. Conclude with `hM.z_ne this`. Consider the case `succ n ih`. Introduce `W₁ W₂ M N z₁ z₂ φ hn hM hN hφ hW`.

Establish `hφ' : ∀ a b, h (φ a) (φ b) = h a b` using `hφ`. Distinguish the cases in `h1 : ∃ ξ ∈ W₁, ξ ≠ 0 ∧ h z₁ ξ = 0`. Take `⟨ξ, hξ, hξ0, hzξ⟩` from `h1`. Take `⟨η, hη, hη0, hzη⟩` from `exists_orth_transfer hd hφ' (fun v hv => (hW v).mp hv) (hM.le _ hM.z_mem) hM.z_ne (hN.le _ hN.z_mem) hN.z_ne hξ hξ0 hzξ`. Take `⟨x, hx, hu⟩` from `hM.exists_unit_norm hS hπ hs hd hξ hξ0 hzξ`.

Take `⟨w₀, hw₀, hw₀u⟩` from `hN.exists_unit_norm hS hπ hs hd hη hη0 hzη`. Take `⟨X, hX, hXu⟩` from `hN.exists_norm hS hπ hs hd ((hW x).mp (hM.le x hx)) hu (hφ' x x) hw₀ hw₀u`. Take `⟨φ', hφ'i, hφ'x, hφ'W, hφ'fix⟩` from `exists_prep hs hd hφ hW (hM.le x hx) (hN.le X hX) hXu.symm`. Take `⟨g, hg, hgfix, hgM⟩` from `ih _ _ _ _ _ _ φ' (by have := finrank_cutW_lt (h := h) (hM.le x hx) hu.1; omega) (hM.cut hS hπ hs hx hu) (hN.cut hS hπ hs hX (by rw [hXu]; exact hu)) hφ'i hφ'W`. Establish `hgx : g x = X`.

Rewrite using `[hgfix x fun w hw => symm_zero hs (mem_cutW.mp hw).2, hφ'x]`. Use `⟨g, hg, fun v hv => ?_, mem_iff_of_cut hM.toIsLatIn hN.toIsLatIn hx hX hu hg hgx hgM⟩` and prove the remaining obligations. Rewrite using `[hgfix v fun w hw => hv w (mem_cutW.mp hw).1, hφ'fix v hv]`. Use `asd_base hS hπ hs hM hN hφ hW h1 ?_` and prove the remaining obligations. Introduce and unpack `⟨η, hη, hη0, hzη⟩`.

Apply `h1` to reduce the goal to its premises. Establish `hsym : ∀ a b, h (φ.symm a) (φ.symm b) = h a b`. Introduce `a b`. Rewrite using `[← hφ', φ.apply_symm_apply, φ.apply_symm_apply]`. Conclude with `exists_orth_transfer hd hsym (fun v hv => by rw [hW, φ.apply_symm_apply]; exact hv) (hN.le _ hN.z_mem) hN.z_ne (hM.le _ hM.z_mem) hM.z_ne hη hη0 hzη`.
-/
theorem asd_main (hS : IsHermSemilocal S) (hπ : IsUnif S π) (hs : h.IsSymm)
    (hd : ∀ x, h x x = 0 → x = 0) (n : ℕ) :
    ∀ (W₁ W₂ : Submodule K V) (M N : AddSubgroup V) (z₁ z₂ : V) (φ : V ≃ₗ[K] V),
      finrank K W₁ ≤ n → IsASD S π h W₁ M z₁ → IsASD S π h W₂ N z₂ → φ ∈ Formalism.HermitianLatticesTheory.isom h →
      (∀ v, v ∈ W₁ ↔ φ v ∈ W₂) →
      ∃ g ∈ Formalism.HermitianLatticesTheory.isom h, (∀ v, (∀ w ∈ W₁, h w v = 0) → g v = φ v) ∧ ∀ v, v ∈ M ↔ g v ∈ N := by
  induction n with
  | zero =>
    intro W₁ W₂ M N z₁ z₂ φ hn hM hN hφ hW
    exfalso
    have hbot : W₁ = ⊥ := Submodule.finrank_eq_zero.mp (Nat.le_zero.mp hn)
    have := hM.le _ hM.z_mem
    rw [hbot, Submodule.mem_bot] at this
    exact hM.z_ne this
  | succ n ih =>
    intro W₁ W₂ M N z₁ z₂ φ hn hM hN hφ hW
    have hφ' : ∀ a b, h (φ a) (φ b) = h a b := hφ
    by_cases h1 : ∃ ξ ∈ W₁, ξ ≠ 0 ∧ h z₁ ξ = 0
    · obtain ⟨ξ, hξ, hξ0, hzξ⟩ := h1
      obtain ⟨η, hη, hη0, hzη⟩ := exists_orth_transfer hd hφ' (fun v hv => (hW v).mp hv)
        (hM.le _ hM.z_mem) hM.z_ne (hN.le _ hN.z_mem) hN.z_ne hξ hξ0 hzξ
      obtain ⟨x, hx, hu⟩ := hM.exists_unit_norm hS hπ hs hd hξ hξ0 hzξ
      obtain ⟨w₀, hw₀, hw₀u⟩ := hN.exists_unit_norm hS hπ hs hd hη hη0 hzη
      obtain ⟨X, hX, hXu⟩ := hN.exists_norm hS hπ hs hd ((hW x).mp (hM.le x hx)) hu (hφ' x x)
        hw₀ hw₀u
      obtain ⟨φ', hφ'i, hφ'x, hφ'W, hφ'fix⟩ := exists_prep hs hd hφ hW (hM.le x hx) (hN.le X hX)
        hXu.symm
      obtain ⟨g, hg, hgfix, hgM⟩ := ih _ _ _ _ _ _ φ'
        (by have := finrank_cutW_lt (h := h) (hM.le x hx) hu.1; omega)
        (hM.cut hS hπ hs hx hu) (hN.cut hS hπ hs hX (by rw [hXu]; exact hu)) hφ'i hφ'W
      have hgx : g x = X := by
        rw [hgfix x fun w hw => symm_zero hs (mem_cutW.mp hw).2, hφ'x]
      refine ⟨g, hg, fun v hv => ?_, mem_iff_of_cut hM.toIsLatIn hN.toIsLatIn hx hX hu hg hgx hgM⟩
      rw [hgfix v fun w hw => hv w (mem_cutW.mp hw).1, hφ'fix v hv]
    · refine asd_base hS hπ hs hM hN hφ hW h1 ?_
      rintro ⟨η, hη, hη0, hzη⟩
      apply h1
      have hsym : ∀ a b, h (φ.symm a) (φ.symm b) = h a b := by
        intro a b
        rw [← hφ', φ.apply_symm_apply, φ.apply_symm_apply]
      exact exists_orth_transfer hd hsym
        (fun v hv => by rw [hW, φ.apply_symm_apply]; exact hv)
        (hN.le _ hN.z_mem) hN.z_ne (hM.le _ hM.z_mem) hM.z_ne hη hη0 hzη

end Formalism.HermitianLattices.Ext.L3.U0

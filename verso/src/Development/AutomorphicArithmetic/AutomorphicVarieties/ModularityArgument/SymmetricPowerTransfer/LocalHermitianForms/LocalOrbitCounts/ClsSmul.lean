import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.LocalHermitianForms.LatticeFrames.OmegaStar
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.LocalHermitianForms.LocalOrbitCounts.LeftMulMatrixEmbeddingDetEqNorm
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.LocalHermitianForms.LocalOrbitCounts.NonsqMul
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.LocalHermitianForms.LocalOrbitCounts.HsLaw

open QuadraticAlgebra UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Loc UpperTheory.V.Z.Sym.Loc.CP

section

variable {O K : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field K] [Algebra O K] {Δ τ : K}

omit [IsDomain O] [IsDiscreteValuationRing O] in
/- English proof (translation)
Use `⟨?_, eq_top_iff.2 fun b _ => ?_⟩` and prove the remaining obligations. Take `⟨s, rfl⟩` from `h.fg`. Use `⟨s.image ((z : Etau K τ) * ·), ?_⟩` and prove the remaining obligations. Rewrite using `[Finset.coe_image]`. Conclude with `(congrArg SetLike.coe (Submodule.span_image (LinearMap.mulLeft O (z : Etau K τ)))).symm`.

Use `Submodule.span_image (s := Λ) (LinearMap.mulLeft K (z : Etau K τ))` as an intermediate fact. Rewrite `this` using `[h.span]`. Conclude with `this.ge ⟨((z⁻¹ : (Etau K τ)ˣ) : Etau K τ) * b, trivial, by simp⟩`.
-/
private theorem lat_mul {Λ : Set (Etau K τ)} (h : IsLat O τ Λ) (z : (Etau K τ)ˣ) : IsLat O τ (((z : Etau K τ) * ·) '' Λ) := by
  classical
  refine ⟨?_, eq_top_iff.2 fun b _ => ?_⟩
  · obtain ⟨s, rfl⟩ := h.fg
    refine ⟨s.image ((z : Etau K τ) * ·), ?_⟩
    rw [Finset.coe_image]
    exact (congrArg SetLike.coe (Submodule.span_image (LinearMap.mulLeft O (z : Etau K τ)))).symm
  · have := Submodule.span_image (s := Λ) (LinearMap.mulLeft K (z : Etau K τ))
    rw [h.span] at this
    exact this.ge ⟨((z⁻¹ : (Etau K τ)ˣ) : Etau K τ) * b, trivial, by simp⟩

/- English proof (translation)
Use extensionality with `S`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨s, rfl⟩`. Conclude with `⟨s * k, by simp [← Set.image_comp, Function.comp_def, smul_smul]⟩`. Introduce and unpack `⟨s, rfl⟩`.

Conclude with `⟨s * k⁻¹, by simp [← Set.image_comp, Function.comp_def, smul_smul]⟩`.
-/
private theorem cls_smul (k : Kˣ) (Λ : Set (Etau K τ)) : cls τ (((k : K) • ·) '' Λ) = cls τ Λ := by
  ext S
  constructor
  · rintro ⟨s, rfl⟩
    exact ⟨s * k, by simp [← Set.image_comp, Function.comp_def, smul_smul]⟩
  · rintro ⟨s, rfl⟩
    exact ⟨s * k⁻¹, by simp [← Set.image_comp, Function.comp_def, smul_smul]⟩

/- English proof (translation)
The claim follows from `(h ▸ (⟨1, by simp⟩ : Λ ∈ cls τ Λ) : Λ ∈ cls τ Λ')`.
-/
private theorem of_cls {Λ Λ' : Set (Etau K τ)} (h : cls τ Λ = cls τ Λ') : ∃ k : Kˣ, Λ = ((k : K) • ·) '' Λ' :=
  (h ▸ (⟨1, by simp⟩ : Λ ∈ cls τ Λ) : Λ ∈ cls τ Λ')

/- English proof (translation)
Use extensionality with `S`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨_, ⟨s, rfl⟩, rfl⟩`. Conclude with `⟨s, by simp [← Set.image_comp, Function.comp_def]⟩`. Introduce and unpack `⟨s, rfl⟩`.

Conclude with `⟨_, ⟨s, rfl⟩, by simp [← Set.image_comp, Function.comp_def]⟩`.
-/
private theorem cls_mul (z : (Etau K τ)ˣ) (Λ : Set (Etau K τ)) :
    (fun S => ((z : Etau K τ) * ·) '' S) '' cls τ Λ = cls τ (((z : Etau K τ) * ·) '' Λ) := by
  ext S
  constructor
  · rintro ⟨_, ⟨s, rfl⟩, rfl⟩
    exact ⟨s, by simp [← Set.image_comp, Function.comp_def]⟩
  · rintro ⟨s, rfl⟩
    exact ⟨_, ⟨s, rfl⟩, by simp [← Set.image_comp, Function.comp_def]⟩

/- English proof (translation)
Take `⟨y₁, y₂, hg, h⟩` from `lat_basis L hD hΛ`. Take `⟨a, b, e1⟩` from `(h _).1 (hx _ ((h y₁).2 ⟨1, 0, by simp⟩))`. Take `⟨c, d, e2⟩` from `(h _).1 (hx _ ((h y₂).2 ⟨0, 1, by simp⟩))`. Use `⟨a * d - b * c, mul_right_cancel₀ hg ?_⟩` and prove the remaining obligations. Establish `e3 : (x * y₂ * star (x * y₁)).im = QuadraticAlgebra.norm x * (y₂ * star y₁).im` using `by simp [QuadraticAlgebra.norm_def]; ring`.

Rewrite using `[← e3, e1, e2]`. Simplify using `[-algebraMap_smul]`. Expand and normalize the polynomial expressions, which then agree.
-/
private theorem norm_int (L : IsLoc O Δ) (hD : τ ^ 2 - 4 ≠ 0) {Λ : Set (Etau K τ)} (hΛ : IsLat O τ Λ) {x : Etau K τ} (hx : ∀ y ∈ Λ, x * y ∈ Λ) :
    QuadraticAlgebra.norm x ∈ (algebraMap O K).range := by
  obtain ⟨y₁, y₂, hg, h⟩ := lat_basis L hD hΛ
  obtain ⟨a, b, e1⟩ := (h _).1 (hx _ ((h y₁).2 ⟨1, 0, by simp⟩))
  obtain ⟨c, d, e2⟩ := (h _).1 (hx _ ((h y₂).2 ⟨0, 1, by simp⟩))
  refine ⟨a * d - b * c, mul_right_cancel₀ hg ?_⟩
  have e3 : (x * y₂ * star (x * y₁)).im = QuadraticAlgebra.norm x * (y₂ * star y₁).im := by simp [QuadraticAlgebra.norm_def]; ring
  rw [← e3, e1, e2]
  simp [-algebraMap_smul]; ring

/- English proof (translation)
Use `haveI := L.frac`. Establish `r1 : algebraMap O K r ≠ 0` using `(h1.map _).ne_zero`. Establish `n0 : 2 + τ ≠ 0` using `hr ▸ pow_ne_zero 2 r1`. Establish `hi : ((z⁻¹ : (Etau K τ)ˣ) : Etau K τ) = (2 + τ)⁻¹ • (1 + star ω)`. Use `Units.inv_eq_of_mul_eq_one_right ?_` and prove the remaining obligations.

Rewrite using `[hz]`. Apply the tactic sequence `ext <;> simp [QuadraticAlgebra.re_one, QuadraticAlgebra.im_one] <;> field_simp <;> ring`. Establish `hq : quo z = ω`. Rewrite using `[quo, hi, hz]`. Apply the tactic sequence `ext <;> simp [QuadraticAlgebra.re_one, QuadraticAlgebra.im_one] <;> field_simp <;> ring`.

Establish `e` using `unimodular_image_mul_unit (s := s) (β := β) z Λ`. Rewrite `e` using `[hq]`. Express the relevant statement in the definitionally equal form `_ = Mu ω '' _ at e`. Take `⟨u, hu'⟩` from `hΛ.fg`. Take `⟨i, hi1⟩` from `h1.exists_right_inv`.

Establish `hi2 : algebraMap O K r * algebraMap O K i = 1` using `by rw [← map_mul, hi1, map_one]`. Establish `hi3 : (2 + τ)⁻¹ = algebraMap O K (i ^ 2)` using `inv_eq_of_mul_eq_one_right (by rw [← hr, map_pow, ← mul_pow, hi2, one_pow])`. Rewrite using `[← e]`. Prove the components needed by the constructor for the conclusion. Introduce `H`.

Take `⟨k, hk⟩` from `lattice_homothety_of_eq_unimodular L hD hs hu hΛ (lat_mul hΛ z) H.symm`. Establish `h2` using `norm_int L hD hΛ (x := (k : K) • ((z⁻¹ : (Etau K τ)ˣ) : Etau K τ)) fun y hy => by`. Take `⟨x, hx, e'⟩ : (k : K) • y ∈ ((z : Etau K τ) * ·) '' Λ` from `hk ▸ ⟨y, hy, rfl⟩`. Rewrite using `[smul_mul_assoc, ← mul_smul_comm, ← e']`. Simplify using `using hx`.

Take `⟨n, hn⟩` from `h2`. Establish `h3 : (k : K) ^ 2 = algebraMap O K (n * r ^ 2)`. Rewrite using `[map_mul, map_pow, hr, hn, hi]`. Simplify using `[QuadraticAlgebra.norm_def, QuadraticAlgebra.re_one, QuadraticAlgebra.im_one]`. Clear the denominators using the available nonvanishing facts.

Expand and normalize the polynomial expressions, which then agree. Take `⟨k₀, hk₀⟩` from `IsIntegrallyClosed.algebraMap_eq_of_integral (R := O) (IsIntegral.of_pow (x := (k : K)) (n := 2) (by norm_num) (h3 ▸ isIntegral_algebraMap))`. Introduce `y hy`. Take `⟨x, hx, e'⟩ : (z : Etau K τ) * y ∈ ((k : K) • ·) '' Λ` from `hk ▸ ⟨y, hy, rfl⟩`. Establish `: ω * y = k₀ • x - y`.

Rewrite using `[← algebraMap_smul K, hk₀]`. Simplify using `only at e'`. Rewrite using `[e', hz]`. Expand and normalize the polynomial expressions, which then agree. Rewrite `*` using `[this, hu']`.

Conclude with `sub_mem (Submodule.smul_mem _ _ hx) hy`. Introduce `H`. Use `congr 1`. Rewrite `H`, the goal using `[hu']`. Use extensionality with `y`.

Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨x, hx, rfl⟩`. Simplify using `only [hz, add_mul, one_mul]`. Conclude with `add_mem hx (H x hx)`. Introduce `hy`.

Use `⟨((z⁻¹ : (Etau K τ)ˣ) : Etau K τ) * y, ?_, by simp⟩` and prove the remaining obligations. Establish `: ((z⁻¹ : (Etau K τ)ˣ) : Etau K τ) * y = (i ^ 2) • ((r ^ 2 - 1) • y - ω * y)`. Rewrite using `[hi, hi3, ← algebraMap_smul K (i ^ 2), ← algebraMap_smul K (r ^ 2 - 1), map_sub, map_pow _ r, hr, map_one, smul_mul_assoc]`. Use `congr 1`. Apply the tactic sequence `rw [show (star ω : Etau K τ) = algebraMap K _ τ - ω by ext <;> simp, Algebra.smul_def]`.

Simplify using `only [map_sub, map_add, map_one, map_ofNat]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[this]`. Conclude with `Submodule.smul_mem _ _ (sub_mem (Submodule.smul_mem _ _ hy) (H y hy))`.
-/
private theorem stab_iff (L : IsLoc O Δ) (hD : τ ^ 2 - 4 ≠ 0) {s : K} {β : Etau K τ} (hs : s ≠ 0) (hu : IsUnit β) {r : O} (h1 : IsUnit r)
    (hr : algebraMap O K r ^ 2 = 2 + τ) {z : (Etau K τ)ˣ} (hz : (z : Etau K τ) = 1 + ω) {Λ : Set (Etau K τ)} (hΛ : IsLat O τ Λ) :
    Mu ω '' S0 s β Λ = S0 s β Λ ↔ ∀ y ∈ Λ, ω * y ∈ Λ := by
  haveI := L.frac
  have r1 : algebraMap O K r ≠ 0 := (h1.map _).ne_zero
  have n0 : 2 + τ ≠ 0 := hr ▸ pow_ne_zero 2 r1
  have hi : ((z⁻¹ : (Etau K τ)ˣ) : Etau K τ) = (2 + τ)⁻¹ • (1 + star ω) := by
    refine Units.inv_eq_of_mul_eq_one_right ?_
    rw [hz]
    ext <;> simp [QuadraticAlgebra.re_one, QuadraticAlgebra.im_one] <;> field_simp <;> ring
  have hq : quo z = ω := by
    rw [quo, hi, hz]
    ext <;> simp [QuadraticAlgebra.re_one, QuadraticAlgebra.im_one] <;> field_simp <;> ring
  have e := unimodular_image_mul_unit (s := s) (β := β) z Λ
  rw [hq] at e
  change _ = Mu ω '' _ at e
  obtain ⟨u, hu'⟩ := hΛ.fg
  obtain ⟨i, hi1⟩ := h1.exists_right_inv
  have hi2 : algebraMap O K r * algebraMap O K i = 1 := by rw [← map_mul, hi1, map_one]
  have hi3 : (2 + τ)⁻¹ = algebraMap O K (i ^ 2) := inv_eq_of_mul_eq_one_right (by rw [← hr, map_pow, ← mul_pow, hi2, one_pow])
  rw [← e]
  constructor
  · intro H
    obtain ⟨k, hk⟩ := lattice_homothety_of_eq_unimodular L hD hs hu hΛ (lat_mul hΛ z) H.symm
    have h2 := norm_int L hD hΛ (x := (k : K) • ((z⁻¹ : (Etau K τ)ˣ) : Etau K τ)) fun y hy => by
      obtain ⟨x, hx, e'⟩ : (k : K) • y ∈ ((z : Etau K τ) * ·) '' Λ := hk ▸ ⟨y, hy, rfl⟩
      rw [smul_mul_assoc, ← mul_smul_comm, ← e']
      simpa using hx
    obtain ⟨n, hn⟩ := h2
    have h3 : (k : K) ^ 2 = algebraMap O K (n * r ^ 2) := by
      rw [map_mul, map_pow, hr, hn, hi]
      simp [QuadraticAlgebra.norm_def, QuadraticAlgebra.re_one, QuadraticAlgebra.im_one]
      field_simp
      ring
    obtain ⟨k₀, hk₀⟩ := IsIntegrallyClosed.algebraMap_eq_of_integral (R := O) (IsIntegral.of_pow (x := (k : K)) (n := 2) (by norm_num)
      (h3 ▸ isIntegral_algebraMap))
    intro y hy
    obtain ⟨x, hx, e'⟩ : (z : Etau K τ) * y ∈ ((k : K) • ·) '' Λ := hk ▸ ⟨y, hy, rfl⟩
    have : ω * y = k₀ • x - y := by
      rw [← algebraMap_smul K, hk₀]
      simp only at e'
      rw [e', hz]; ring
    rw [this, hu'] at *
    exact sub_mem (Submodule.smul_mem _ _ hx) hy
  · intro H
    congr 1
    rw [hu'] at H ⊢
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      simp only [hz, add_mul, one_mul]
      exact add_mem hx (H x hx)
    · intro hy
      refine ⟨((z⁻¹ : (Etau K τ)ˣ) : Etau K τ) * y, ?_, by simp⟩
      have : ((z⁻¹ : (Etau K τ)ˣ) : Etau K τ) * y = (i ^ 2) • ((r ^ 2 - 1) • y - ω * y) := by
        rw [hi, hi3, ← algebraMap_smul K (i ^ 2), ← algebraMap_smul K (r ^ 2 - 1), map_sub, map_pow _ r, hr, map_one, smul_mul_assoc]
        congr 1
        rw [show (star ω : Etau K τ) = algebraMap K _ τ - ω by ext <;> simp, Algebra.smul_def]
        simp only [map_sub, map_add, map_one, map_ofNat]
        ring
      rw [this]
      exact Submodule.smul_mem _ _ (sub_mem (Submodule.smul_mem _ _ hy) (H y hy))

end

/- English proof (translation)
Introduce `O K _ _ _ _ _ Δ τ L hD r hr2 hr c hc j χ hj hχ a ha z hz t`. Use `haveI := L.frac`. Establish `h2 : (2 : K) ≠ 0`. Use `(L.two.map (algebraMap O K)).ne_zero` as an intermediate fact. Rewrite `this` using `[map_ofNat]`. Then use the resulting hypothesis.

Establish `h1 : IsUnit r`. Assume the negation of the conclusion as `h'`. Establish `: r - (r - 2) ∈ IsLocalRing.maximalIdeal O` using `sub_mem h' hr2`. Rewrite `this` using `[sub_sub_cancel]`. Conclude with `this L.two`.

Establish `h1' : IsUnit (2 + r)`. Assume the negation of the conclusion as `h'`. Establish `: (2 + r) - (r - 2) ∈ IsLocalRing.maximalIdeal O` using `sub_mem h' hr2`. Rewrite `this` using `[show (2 + r) - (r - 2) = 2 * 2 by ring]`. Conclude with `this (L.two.mul L.two)`.

Establish `r1 : algebraMap O K r ≠ 0` using `(h1.map _).ne_zero`. Establish `n0 : 2 + τ ≠ 0` using `hr ▸ pow_ne_zero 2 r1`. Establish `m0 : 2 - τ ≠ 0` using `fun h => hD (by linear_combination (-(2 + τ)) * h)`. Take `⟨ε₁, s₁, hs₁, e₁⟩` from `L.even`. Establish `hσ : Δ * s₁⁻¹ ^ 2 = algebraMap O K ε₁` using `by rw [e₁]; field_simp`.

Establish `hσ0 : s₁⁻¹ ≠ 0` using `inv_ne_zero hs₁`. Establish `hd : dLam (algebraMap K (Lsq K Δ) (algebraMap O K r)) z = ofE Δ ((algebraMap O K r)⁻¹ • (1 + ω))`. Establish `hi : ((z⁻¹ : (Etau K τ)ˣ) : Etau K τ) = (2 + τ)⁻¹ • (1 + star ω)`. Use `Units.inv_eq_of_mul_eq_one_right ?_` and prove the remaining obligations. Rewrite using `[hz]`.

Apply the tactic sequence `ext <;> simp [QuadraticAlgebra.re_one, QuadraticAlgebra.im_one] <;> field_simp <;> ring`. Rewrite using `[dLam, hi, ← hr]`. Generalize the expression as in `algebraMap O K r = R at r1`. Apply the tactic sequence `ext <;> simp [ofE, QuadraticAlgebra.re_one, QuadraticAlgebra.im_one] <;> field_simp <;> ring`. Take `⟨ε₀, s₀, hs₀, e₀⟩` from `hc`.

Establish `hε₀ : algebraMap O K ε₀ ≠ 0` using `(ε₀.isUnit.map _).ne_zero`. Establish `hc0 : c ≠ 0` using `fun h => mul_ne_zero hε₀ (pow_ne_zero 2 hs₀) (by rw [← e₀, h, zero_mul])`. Apply the tactic sequence `have hq : ∀ x : K, hs (τ ^ 2 - 4) x * hs (τ ^ 2 - 4) x = 1 := fun x => by unfold hs; split_ifs <;> norm_num`. Establish `hm` using `hsMul O K Δ L _ (-2 * c) t hD (mul_ne_zero (neg_ne_zero.2 h2) hc0) t.ne_zero`. Rewrite using `[hd]`.

Use `split_ifs with H`. Rewrite `hm` using `[H, hq]`. Choose the witnesses or unpack the hypotheses as in `⟨p, q, hpq⟩ : ∃ p q : K, p ^ 2 - (τ ^ 2 - 4) * q ^ 2 = -2 * c * t := by`. Assume the negation of the conclusion as `hn`. Rewrite `hm` using `[hs, if_neg hn]`.

Evaluate the numerical expressions using `at hm`. Set `ε : Oˣ` to `-ε₀`. Set `s : K` to `s₀ / (algebraMap O K r * (2 - τ))`. Establish `hs' : s ≠ 0` using `div_ne_zero hs₀ (mul_ne_zero r1 m0)`. Establish `hc' : c = (τ ^ 2 - 4) * algebraMap O K ε * s ^ 2`.

Establish `h5 : s ^ 2 * ((2 + τ) * (2 - τ) ^ 2) = s₀ ^ 2`. Rewrite using `[← hr, ← mul_pow, ← mul_pow, div_mul_cancel₀ _ (mul_ne_zero r1 m0)]`. Use `mul_right_cancel₀ (mul_ne_zero n0 (pow_ne_zero 2 m0)) ?_` and prove the remaining obligations. Simplify using `only [ε, Units.val_neg, map_neg]`. Take the linear combination `(2 + τ) * (2 - τ) * e₀ + (τ ^ 2 - 4) * algebraMap O K ε₀ * h5`.

Set `β : Etau K τ` to `c⁻¹ • ((ω - star ω) * ⟨p - τ * q, 2 * q⟩)`. Establish `hN : QuadraticAlgebra.norm β * c = 2 * t * (τ ^ 2 - 4)`. Simplify using `[β, QuadraticAlgebra.norm_def]`. Clear the denominators using the available nonvanishing facts. Take the linear combination `(-(τ ^ 2 - 4)) * hpq`.

Establish `hβ : QuadraticAlgebra.norm β * algebraMap O K ε * s ^ 2 = 2 * t` using `mul_right_cancel₀ hD (by rw [← hN]; nth_rewrite 1 [hc']; ring)`. Establish `hu : IsUnit β` using `QuadraticAlgebra.isUnit_iff_norm_isUnit.2 (IsUnit.mk0 _ fun h => mul_ne_zero h2 t.ne_zero (by rw [← hβ, h]; ring))`. Establish `ga : gOrb O j χ a = vcount O τ ω`. Rewrite using `[gLat O K Δ τ L hD j χ hj hχ a 1 1 (by simp [ha, QuadraticAlgebra.norm_def]), ha]; simp`. Rewrite using `[ga]`.

Use `letI := torAct (K := K) Δ τ`. Use `letI := mulAct τ`. Establish `kX : ∀ Λ, IsLat O τ Λ → ((∃ S, IsLat O τ S ∧ (∀ y ∈ S, ω * y ∈ S) ∧ cls τ Λ = cls τ S) ↔ ∀ y ∈ Λ, ω * y ∈ Λ)` using `fun Λ hΛ => by`. Use `⟨?_, fun h => ⟨Λ, hΛ, h, rfl⟩⟩` and prove the remaining obligations. Introduce and unpack `⟨S, -, hS, e⟩`.

Take `⟨k, rfl⟩` from `of_cls e`. Introduce and unpack `_ ⟨y, hy, rfl⟩`. Conclude with `⟨_, hS y hy, (mul_smul_comm _ _ _).symm⟩`. Establish `kT : ∀ Λ, IsLat O τ Λ → (IsFix O c (ofE Δ ((algebraMap O K r)⁻¹ • (1 + ω))) ((t : K) • (1 : EL Δ τ)) (up Δ s₁⁻¹ (S0 s β Λ)) ↔ ∀ y ∈ Λ, ω * y ∈ Λ)` using `fun Λ hΛ => by`. Rewrite using `[← stab_iff L hD hs' hu h1 hr hz hΛ]`.

Use `⟨fun h => ?_, fix_up L hσ h1 h1' hr (isUnimodular_cliffordLatticeStabilizer L hD hs' hu hc' hβ hΛ)⟩` and prove the remaining obligations. Take `⟨S, -, h3, h4⟩` from `fix_down L hσ h1 h1' hr h`. Rewrite using `[up_inj hσ0 h4]` and apply the resulting hypothesis. Establish `inv : ∀ (w : (Etau K τ)ˣ) (X : Set (Set (Etau K τ))), (∃ S, IsLat O τ S ∧ (∀ y ∈ S, ω * y ∈ S) ∧ X = cls τ S) → ∃ S, IsLat O τ S ∧ (∀ y ∈ S, ω * y ∈ S) ∧ w • X = cls τ S`. Introduce and unpack `w _ ⟨S, a1, a2, rfl⟩`.

Use `⟨_, lat_mul a1 w, ?_, cls_mul w S⟩` and prove the remaining obligations. Introduce and unpack `_ ⟨y, hy, rfl⟩`. Conclude with `⟨_, a2 y hy, mul_left_comm _ _ _⟩`. Use `wTrans _ _ _ _ _ _ (fun T X => ∃ Λ, IsLat O τ Λ ∧ T = up Δ s₁⁻¹ (S0 s β Λ) ∧ X = cls τ Λ) (fun w S => if_congr (isFix_tor _ _ _ _ _) rfl rfl) (fun w X => if_congr ⟨fun h => ?_, inv w X⟩ rfl rfl) ?_ ?_ (fun T hT => ?_) fun X hX => ?_` and prove the remaining obligations. Simplify using `using inv w⁻¹ _ h`.

Introduce and unpack `w _ _ ⟨Λ, hΛ, rfl, rfl⟩`. Conclude with `⟨_, lat_mul hΛ w, (tor_up _ w _).trans (by rw [unimodular_image_mul_unit]; rfl), cls_mul w Λ⟩`. Introduce and unpack `_ _ ⟨Λ, hΛ, rfl, rfl⟩`. Conclude with `if_congr ((kT Λ hΛ).trans (kX Λ hΛ).symm) rfl rfl`. Take `⟨S, a1, -, rfl⟩` from `fix_down L hσ h1 h1' hr (by by_contra h; exact hT (if_neg h))`.

Take `⟨Λ, hΛ, rfl⟩` from `exists_lat L hc' hβ a1`. Use `⟨_, ⟨Λ, hΛ, rfl, rfl⟩, ?_⟩` and prove the remaining obligations. Introduce and unpack `_ ⟨Λ', hΛ', e, rfl⟩`. Take `⟨k, rfl⟩` from `lattice_homothety_of_eq_unimodular L hD hs' hu hΛ hΛ' (up_inj hσ0 e)`. Conclude with `cls_smul k Λ`.

Take `⟨Λ, hΛ, -, rfl⟩ : ∃ S, IsLat O τ S ∧ (∀ y ∈ S, ω * y ∈ S) ∧ X = cls τ S` from `by by_contra h; exact hX (if_neg h)`. Use `⟨_, ⟨Λ, hΛ, rfl, rfl⟩, ?_⟩` and prove the remaining obligations. Introduce and unpack `_ ⟨Λ', hΛ', rfl, e⟩`. Take `⟨k, rfl⟩` from `of_cls e`. Rewrite using `[unimodular_image_smul_eq]`.

Use `finsum_eq_zero_of_forall_eq_zero fun o => mul_eq_zero_of_right _ (if_neg fun h => H ?_)` and prove the remaining obligations. Take `⟨S, a1, -, -⟩` from `fix_down L hσ h1 h1' hr h`. Break down `a1.iso L t.ne_zero with h3 | h3` into its components or cases. Rewrite using `[(hsLaw O K Δ L).2.2.2 _ _ hD h3, (hsLaw O K Δ L).2.2.2 _ _ hD h3]`. Rewrite `hm` using `[hs, if_pos h3]`.

Take the linear combination `(-hs (τ ^ 2 - 4) (-2 * c)) * hm - hs (τ ^ 2 - 4) (t : K) * hq (-2 * c)`.
-/
theorem UpperTheory.V.Z.Sym.Loc.caseP :
    UpperTheory.V.Z.Sym.Loc.CaseP := by
  intro O K _ _ _ _ _ Δ τ L hD r hr2 hr c hc j χ hj hχ a ha z hz t
  classical
  haveI := L.frac
  have h2 : (2 : K) ≠ 0 := by
    have := (L.two.map (algebraMap O K)).ne_zero
    rwa [map_ofNat] at this
  have h1 : IsUnit r := by
    by_contra h'
    have : r - (r - 2) ∈ IsLocalRing.maximalIdeal O := sub_mem h' hr2
    rw [sub_sub_cancel] at this
    exact this L.two
  have h1' : IsUnit (2 + r) := by
    by_contra h'
    have : (2 + r) - (r - 2) ∈ IsLocalRing.maximalIdeal O := sub_mem h' hr2
    rw [show (2 + r) - (r - 2) = 2 * 2 by ring] at this
    exact this (L.two.mul L.two)
  have r1 : algebraMap O K r ≠ 0 := (h1.map _).ne_zero
  have n0 : 2 + τ ≠ 0 := hr ▸ pow_ne_zero 2 r1
  have m0 : 2 - τ ≠ 0 := fun h => hD (by linear_combination (-(2 + τ)) * h)
  obtain ⟨ε₁, s₁, hs₁, e₁⟩ := L.even
  have hσ : Δ * s₁⁻¹ ^ 2 = algebraMap O K ε₁ := by rw [e₁]; field_simp
  have hσ0 : s₁⁻¹ ≠ 0 := inv_ne_zero hs₁
  have hd : dLam (algebraMap K (Lsq K Δ) (algebraMap O K r)) z = ofE Δ ((algebraMap O K r)⁻¹ • (1 + ω)) := by
    have hi : ((z⁻¹ : (Etau K τ)ˣ) : Etau K τ) = (2 + τ)⁻¹ • (1 + star ω) := by
      refine Units.inv_eq_of_mul_eq_one_right ?_
      rw [hz]
      ext <;> simp [QuadraticAlgebra.re_one, QuadraticAlgebra.im_one] <;> field_simp <;> ring
    rw [dLam, hi, ← hr]
    generalize algebraMap O K r = R at r1
    ext <;> simp [ofE, QuadraticAlgebra.re_one, QuadraticAlgebra.im_one] <;> field_simp <;> ring
  obtain ⟨ε₀, s₀, hs₀, e₀⟩ := hc
  have hε₀ : algebraMap O K ε₀ ≠ 0 := (ε₀.isUnit.map _).ne_zero
  have hc0 : c ≠ 0 := fun h => mul_ne_zero hε₀ (pow_ne_zero 2 hs₀) (by rw [← e₀, h, zero_mul])
  have hq : ∀ x : K, hs (τ ^ 2 - 4) x * hs (τ ^ 2 - 4) x = 1 := fun x => by unfold hs; split_ifs <;> norm_num
  have hm := hsMul O K Δ L _ (-2 * c) t hD (mul_ne_zero (neg_ne_zero.2 h2) hc0) t.ne_zero
  rw [hd]
  split_ifs with H
  · rw [H, hq] at hm
    obtain ⟨p, q, hpq⟩ : ∃ p q : K, p ^ 2 - (τ ^ 2 - 4) * q ^ 2 = -2 * c * t := by
      by_contra hn
      rw [hs, if_neg hn] at hm
      norm_num at hm
    let ε : Oˣ := -ε₀
    let s : K := s₀ / (algebraMap O K r * (2 - τ))
    have hs' : s ≠ 0 := div_ne_zero hs₀ (mul_ne_zero r1 m0)
    have hc' : c = (τ ^ 2 - 4) * algebraMap O K ε * s ^ 2 := by
      have h5 : s ^ 2 * ((2 + τ) * (2 - τ) ^ 2) = s₀ ^ 2 := by
        rw [← hr, ← mul_pow, ← mul_pow, div_mul_cancel₀ _ (mul_ne_zero r1 m0)]
      refine mul_right_cancel₀ (mul_ne_zero n0 (pow_ne_zero 2 m0)) ?_
      simp only [ε, Units.val_neg, map_neg]
      linear_combination (2 + τ) * (2 - τ) * e₀ + (τ ^ 2 - 4) * algebraMap O K ε₀ * h5
    let β : Etau K τ := c⁻¹ • ((ω - star ω) * ⟨p - τ * q, 2 * q⟩)
    have hN : QuadraticAlgebra.norm β * c = 2 * t * (τ ^ 2 - 4) := by
      simp [β, QuadraticAlgebra.norm_def]
      field_simp
      linear_combination (-(τ ^ 2 - 4)) * hpq
    have hβ : QuadraticAlgebra.norm β * algebraMap O K ε * s ^ 2 = 2 * t := mul_right_cancel₀ hD (by rw [← hN]; nth_rewrite 1 [hc']; ring)
    have hu : IsUnit β := QuadraticAlgebra.isUnit_iff_norm_isUnit.2 (IsUnit.mk0 _ fun h => mul_ne_zero h2 t.ne_zero (by rw [← hβ, h]; ring))
    have ga : gOrb O j χ a = vcount O τ ω := by
      rw [gLat O K Δ τ L hD j χ hj hχ a 1 1 (by simp [ha, QuadraticAlgebra.norm_def]), ha]; simp
    rw [ga]
    letI := torAct (K := K) Δ τ
    letI := mulAct τ
    have kX : ∀ Λ, IsLat O τ Λ → ((∃ S, IsLat O τ S ∧ (∀ y ∈ S, ω * y ∈ S) ∧ cls τ Λ = cls τ S) ↔ ∀ y ∈ Λ, ω * y ∈ Λ) := fun Λ hΛ => by
      refine ⟨?_, fun h => ⟨Λ, hΛ, h, rfl⟩⟩
      rintro ⟨S, -, hS, e⟩
      obtain ⟨k, rfl⟩ := of_cls e
      rintro _ ⟨y, hy, rfl⟩
      exact ⟨_, hS y hy, (mul_smul_comm _ _ _).symm⟩
    have kT : ∀ Λ, IsLat O τ Λ → (IsFix O c (ofE Δ ((algebraMap O K r)⁻¹ • (1 + ω))) ((t : K) • (1 : EL Δ τ)) (up Δ s₁⁻¹ (S0 s β Λ)) ↔
        ∀ y ∈ Λ, ω * y ∈ Λ) := fun Λ hΛ => by
      rw [← stab_iff L hD hs' hu h1 hr hz hΛ]
      refine ⟨fun h => ?_, fix_up L hσ h1 h1' hr (isUnimodular_cliffordLatticeStabilizer L hD hs' hu hc' hβ hΛ)⟩
      obtain ⟨S, -, h3, h4⟩ := fix_down L hσ h1 h1' hr h
      rwa [up_inj hσ0 h4]
    have inv : ∀ (w : (Etau K τ)ˣ) (X : Set (Set (Etau K τ))), (∃ S, IsLat O τ S ∧ (∀ y ∈ S, ω * y ∈ S) ∧ X = cls τ S) →
        ∃ S, IsLat O τ S ∧ (∀ y ∈ S, ω * y ∈ S) ∧ w • X = cls τ S := by
      rintro w _ ⟨S, a1, a2, rfl⟩
      refine ⟨_, lat_mul a1 w, ?_, cls_mul w S⟩
      rintro _ ⟨y, hy, rfl⟩
      exact ⟨_, a2 y hy, mul_left_comm _ _ _⟩
    refine wTrans _ _ _ _ _ _ (fun T X => ∃ Λ, IsLat O τ Λ ∧ T = up Δ s₁⁻¹ (S0 s β Λ) ∧ X = cls τ Λ)
      (fun w S => if_congr (isFix_tor _ _ _ _ _) rfl rfl) (fun w X => if_congr ⟨fun h => ?_, inv w X⟩ rfl rfl) ?_ ?_ (fun T hT => ?_) fun X hX => ?_
    · simpa using inv w⁻¹ _ h
    · rintro w _ _ ⟨Λ, hΛ, rfl, rfl⟩
      exact ⟨_, lat_mul hΛ w, (tor_up _ w _).trans (by rw [unimodular_image_mul_unit]; rfl), cls_mul w Λ⟩
    · rintro _ _ ⟨Λ, hΛ, rfl, rfl⟩
      exact if_congr ((kT Λ hΛ).trans (kX Λ hΛ).symm) rfl rfl
    · obtain ⟨S, a1, -, rfl⟩ := fix_down L hσ h1 h1' hr (by by_contra h; exact hT (if_neg h))
      obtain ⟨Λ, hΛ, rfl⟩ := exists_lat L hc' hβ a1
      refine ⟨_, ⟨Λ, hΛ, rfl, rfl⟩, ?_⟩
      rintro _ ⟨Λ', hΛ', e, rfl⟩
      obtain ⟨k, rfl⟩ := lattice_homothety_of_eq_unimodular L hD hs' hu hΛ hΛ' (up_inj hσ0 e)
      exact cls_smul k Λ
    · obtain ⟨Λ, hΛ, -, rfl⟩ : ∃ S, IsLat O τ S ∧ (∀ y ∈ S, ω * y ∈ S) ∧ X = cls τ S := by by_contra h; exact hX (if_neg h)
      refine ⟨_, ⟨Λ, hΛ, rfl, rfl⟩, ?_⟩
      rintro _ ⟨Λ', hΛ', rfl, e⟩
      obtain ⟨k, rfl⟩ := of_cls e
      rw [unimodular_image_smul_eq]
  · refine finsum_eq_zero_of_forall_eq_zero fun o => mul_eq_zero_of_right _ (if_neg fun h => H ?_)
    obtain ⟨S, a1, -, -⟩ := fix_down L hσ h1 h1' hr h
    rcases a1.iso L t.ne_zero with h3 | h3
    · rw [(hsLaw O K Δ L).2.2.2 _ _ hD h3, (hsLaw O K Δ L).2.2.2 _ _ hD h3]
    · rw [hs, if_pos h3] at hm
      linear_combination (-hs (τ ^ 2 - 4) (-2 * c)) * hm - hs (τ ^ 2 - 4) (t : K) * hq (-2 * c)

import Formalism.LocalToGlobal.PairingIndexBounds.HalvesRecursion.BoundedHalfModels.EqOffBound

noncomputable section

namespace Formalism.L2.PairingIndexBounds.Rec

open IsDedekindDomain

section Gen

variable {R : Type} [CommRing R] [IsDedekindDomain R] {K : Type} [Field K] [Algebra R K] [IsFractionRing R K]
  {m n : Type}

/- English proof (translation)
The claim follows from `(algebraMap_smul K r X).symm`.
-/
theorem gh_rsmul (r : R) (X : Matrix m n K) : r • X = algebraMap R K r • X := (algebraMap_smul K r X).symm

/- English proof (translation)
Simplify using `[sMod]`.
-/
theorem gh_mem_sMod_iff (k : K) (Y : Submodule R (Matrix m n K)) (y : Matrix m n K) :
    y ∈ sMod k Y ↔ ∃ z ∈ Y, k • z = y := by
  simp [sMod]

/- English proof (translation)
Use `Submodule.smul_induction_on hy (fun r hr z hz => ?_) (fun x y hx hy => ?_)` and prove the remaining obligations. Rewrite using `[map_smul]`. Conclude with `Submodule.smul_mem_smul hr (h z hz)`. Rewrite using `[map_add]`. Conclude with `add_mem hx hy`.
-/
theorem gh_map_mem {M : Type} [AddCommGroup M] [Module R M] (I : Ideal R) {Y Z : Submodule R M}
    (f : M →ₗ[R] M) (h : ∀ z ∈ Y, f z ∈ Z) {y : M} (hy : y ∈ I • Y) : f y ∈ I • Z := by
  refine Submodule.smul_induction_on hy (fun r hr z hz => ?_) (fun x y hx hy => ?_)
  · rw [map_smul]; exact Submodule.smul_mem_smul hr (h z hz)
  · rw [map_add]; exact add_mem hx hy

/- English proof (translation)
Use `gh_map_mem I (LinearMap.lsmul R M c) (fun z hz => by simpa using h z hz) hy` as an intermediate fact. Simplify using `using this`.
-/
theorem gh_smul_mem {M : Type} [AddCommGroup M] [Module R M] (I : Ideal R) {Y Z : Submodule R M}
    (c : R) (h : ∀ z ∈ Y, c • z ∈ Z) {y : M} (hy : y ∈ I • Y) : c • y ∈ I • Z := by
  have := gh_map_mem I (LinearMap.lsmul R M c) (fun z hz => by simpa using h z hz) hy
  simpa using this

/- English proof (translation)
Take `⟨p, q, hpq⟩` from `h`. Establish `: w = p • (s • w) + q • (B • w)` using `by rw [smul_smul, smul_smul, ← add_smul, hpq, one_smul]`. Rewrite using `[this]`. Conclude with `add_mem (N.smul_mem p hs) (N.smul_mem q hB)`.
-/
theorem gh_local_global {M : Type} [AddCommGroup M] [Module R M] (N : Submodule R M) {s B : R}
    (h : IsCoprime s B) {w : M} (hs : s • w ∈ N) (hB : B • w ∈ N) : w ∈ N := by
  obtain ⟨p, q, hpq⟩ := h
  have : w = p • (s • w) + q • (B • w) := by rw [smul_smul, smul_smul, ← add_smul, hpq, one_smul]
  rw [this]; exact add_mem (N.smul_mem p hs) (N.smul_mem q hB)

/- English proof (translation)
Use `(gh_mem_sMod_iff k Y _).2 ⟨r • z, hz, ?_⟩` and prove the remaining obligations. Rewrite using `[gh_rsmul r z, gh_rsmul c z, smul_smul, hk]`.
-/
theorem gh_mem_sMod_of {k : K} {Y : Submodule R (Matrix m n K)} {r c : R} {z : Matrix m n K}
    (hz : r • z ∈ Y) (hk : k * algebraMap R K r = algebraMap R K c) : c • z ∈ sMod k Y := by
  refine (gh_mem_sMod_iff k Y _).2 ⟨r • z, hz, ?_⟩
  rw [gh_rsmul r z, gh_rsmul c z, smul_smul, hk]

/- English proof (translation)
Introduce `w hw`. Take `⟨z, hz, rfl⟩` from `(gh_mem_sMod_iff k Y w).1 hw`. Rewrite using `[gh_rsmul c, smul_smul, hk, ← gh_rsmul]`. Conclude with `h z hz`.
-/
theorem gh_smul_sMod_mem {k : K} {Y Z : Submodule R (Matrix m n K)} {r c : R}
    (h : ∀ z ∈ Y, r • z ∈ Z) (hk : algebraMap R K c * k = algebraMap R K r) :
    ∀ w ∈ sMod k Y, c • w ∈ Z := by
  intro w hw
  obtain ⟨z, hz, rfl⟩ := (gh_mem_sMod_iff k Y w).1 hw
  rw [gh_rsmul c, smul_smul, hk, ← gh_rsmul]
  exact h z hz

/- English proof (translation)
Introduce `_ hw` and use `gh_smul_mem I c (fun z hz => gh_mem_sMod_of (h z hz) hk) hw`.
-/
theorem gh_toHalf (I : Ideal R) {k : K} {Y Z : Submodule R (Matrix m n K)} {r c : R}
    (h : ∀ z ∈ Y, r • z ∈ Z) (hk : k * algebraMap R K r = algebraMap R K c) :
    ∀ w ∈ I • Y, c • w ∈ I • sMod k Z :=
  fun _ hw => gh_smul_mem I c (fun z hz => gh_mem_sMod_of (h z hz) hk) hw

/- English proof (translation)
Introduce `_ hw` and use `gh_smul_mem I c (gh_smul_sMod_mem h hk) hw`.
-/
theorem gh_fromHalf (I : Ideal R) {k : K} {Y Z : Submodule R (Matrix m n K)} {r c : R}
    (h : ∀ z ∈ Z, r • z ∈ Y) (hk : algebraMap R K c * k = algebraMap R K r) :
    ∀ w ∈ I • sMod k Z, c • w ∈ I • Y :=
  fun _ hw => gh_smul_mem I c (gh_smul_sMod_mem h hk) hw

/- English proof (translation)
Rewrite using `[div_pow, mul_pow, div_mul_eq_mul_div, div_eq_iff (pow_ne_zero e hP)]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem div_pow_mul_prod_pow_left {P Q X : K} (hP : P ≠ 0) (e : ℕ) : (Q / P) ^ e * (X * (P * Q) ^ e) = X * (Q ^ e * Q ^ e) := by
  rw [div_pow, mul_pow, div_mul_eq_mul_div, div_eq_iff (pow_ne_zero e hP)]; ring

/- English proof (translation)
Rewrite using `[← inv_pow, inv_div, div_pow, mul_pow, div_mul_eq_mul_div, div_eq_iff (pow_ne_zero e hQ)]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem inv_div_pow_mul_prod_pow_right {P Q X : K} (hQ : Q ≠ 0) (e : ℕ) :
    ((Q / P) ^ e)⁻¹ * (X * (P * Q) ^ e) = X * (P ^ e * P ^ e) := by
  rw [← inv_pow, inv_div, div_pow, mul_pow, div_mul_eq_mul_div, div_eq_iff (pow_ne_zero e hQ)]; ring

/- English proof (translation)
Rewrite using `[div_pow, mul_pow, mul_div_assoc', div_eq_iff (pow_ne_zero e hP)]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem sq_pow_mul_div_pow_eq_prod_pow {P Q X : K} (hP : P ≠ 0) (e : ℕ) : X * (P ^ e * P ^ e) * (Q / P) ^ e = X * (P * Q) ^ e := by
  rw [div_pow, mul_pow, mul_div_assoc', div_eq_iff (pow_ne_zero e hP)]; ring

/- English proof (translation)
Rewrite using `[← inv_pow, inv_div, div_pow, mul_pow, mul_div_assoc', div_eq_iff (pow_ne_zero e hQ)]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem sq_pow_mul_inv_div_pow_eq_prod_pow {P Q X : K} (hQ : Q ≠ 0) (e : ℕ) :
    X * (Q ^ e * Q ^ e) * ((Q / P) ^ e)⁻¹ = X * (P * Q) ^ e := by
  rw [← inv_pow, inv_div, div_pow, mul_pow, mul_div_assoc', div_eq_iff (pow_ne_zero e hQ)]; ring

/- English proof (translation)
Rewrite using `[div_pow, mul_pow, mul_div_assoc', div_eq_iff (pow_ne_zero e hP)]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem pow_mul_pow_mul_div_pow_eq {P Q : K} (hP : P ≠ 0) (e : ℕ) : P ^ e * P ^ e * (Q / P) ^ e = (P * Q) ^ e := by
  rw [div_pow, mul_pow, mul_div_assoc', div_eq_iff (pow_ne_zero e hP)]; ring

/- English proof (translation)
Use extensionality with `i j`. Simplify using `[matI]`.
-/
theorem gh_matI_add (v : HeightOneSpectrum R) (y z : Matrix m n K) : matI v (y + z) = matI v y + matI v z := by
  ext i j; simp [matI]

/- English proof (translation)
Use extensionality with `i j`. Simplify using `[matI]`.
-/
theorem gh_matI_sub (v : HeightOneSpectrum R) (y z : Matrix m n K) : matI v (y - z) = matI v y - matI v z := by
  ext i j; simp [matI]

/- English proof (translation)
Use extensionality with `i j`. Simplify using `[matI]`.
-/
theorem gh_matI_zero (v : HeightOneSpectrum R) : matI v (0 : Matrix m n K) = 0 := by
  ext i j; simp [matI]

/- English proof (translation)
Rewrite using `[hatY, AddSubgroup.topologicalClosure_coe, AddSubgroup.coe_map]`. Both sides reduce to the same expression.
-/
theorem gh_hatY_coe (v : HeightOneSpectrum R) (Y : Submodule R (Matrix m n K)) :
    (hatY v Y : Set (Matrix m n (v.adicCompletion K))) = closure (matI v '' (Y : Set (Matrix m n K))) := by
  rw [hatY, AddSubgroup.topologicalClosure_coe, AddSubgroup.coe_map]
  rfl

/- English proof (translation)
Introduce `A`. Rewrite using `[SetLike.mem_coe, Submodule.mem_inf]`. Prove the components needed by the constructor for the conclusion. Use `Y₁.smul_mem d₂ (h₁ A)` as an intermediate fact. Rewrite `this` using `[gh_rsmul, smul_smul, ← map_mul, mul_comm d₂]`.

Conclude with `this`. Use `Y₂.smul_mem d₁ (h₂ A)` as an intermediate fact. Rewrite `this` using `[gh_rsmul, smul_smul, ← map_mul]`. Conclude with `this`.
-/
theorem gh_lowB_inf {Y₁ Y₂ : Submodule R (Matrix m n K)} {d₁ d₂ : R} (h₁ : LowB d₁ (Y₁ : Set (Matrix m n K)))
    (h₂ : LowB d₂ (Y₂ : Set (Matrix m n K))) :
    LowB (d₁ * d₂) ((Y₁ ⊓ Y₂ : Submodule R (Matrix m n K)) : Set (Matrix m n K)) := by
  intro A
  rw [SetLike.mem_coe, Submodule.mem_inf]
  constructor
  · have := Y₁.smul_mem d₂ (h₁ A)
    rw [gh_rsmul, smul_smul, ← map_mul, mul_comm d₂] at this; exact this
  · have := Y₂.smul_mem d₁ (h₂ A)
    rw [gh_rsmul, smul_smul, ← map_mul] at this; exact this

/- English proof (translation)
Establish `hγ : algebraMap R K γ ≠ 0` using `(map_ne_zero_iff _ (IsFractionRing.injective R K)).2 hγ0`. Use `Submodule.smul_induction_on hw (fun c hc z hz => ?_) (fun w₁ w₂ h₁ h₂ => ?_)` and prove the remaining obligations. Take `⟨o, ho⟩` from `hto c hc`. Use `⟨t, ht, ?_⟩` and prove the remaining obligations. Establish `h'` using `congrArg (algebraMap R K) ho`.

Rewrite `h'` using `[map_mul, map_mul]`. Establish `: t • ((algebraMap R K γ)⁻¹ • (c • z)) = o • z`. Rewrite using `[gh_rsmul t, gh_rsmul c, gh_rsmul o, smul_smul, smul_smul]`. Use `congr 1`. Rewrite using `[mul_right_comm, h', mul_comm (algebraMap R K γ), mul_assoc, mul_inv_cancel₀ hγ, mul_one]`.

Rewrite using `[this]`. Conclude with `Y.smul_mem o hz`. Take `⟨s₁, hs₁, h₁⟩` from `h₁`. Take `⟨s₂, hs₂, h₂⟩` from `h₂`. Use `⟨s₁ * s₂, fun h => (v.isPrime.mem_or_mem h).elim hs₁ hs₂, ?_⟩` and prove the remaining obligations.

Establish `e1 : (s₁ * s₂) • ((algebraMap R K γ)⁻¹ • w₁) = s₂ • (s₁ • ((algebraMap R K γ)⁻¹ • w₁))`. Rewrite using `[mul_comm, mul_smul]`. Establish `e2 : (s₁ * s₂) • ((algebraMap R K γ)⁻¹ • w₂) = s₁ • (s₂ • ((algebraMap R K γ)⁻¹ • w₂))`. Rewrite using `[mul_smul]`. Rewrite using `[smul_add, smul_add, e1, e2]`.

Conclude with `add_mem (Y.smul_mem _ h₁) (Y.smul_mem _ h₂)`.
-/
theorem gh_read_fwd (I : Ideal R) {γ t : R} (v : HeightOneSpectrum R) (hγ0 : γ ≠ 0) (ht : t ∉ v.asIdeal)
    (hto : ∀ c ∈ I, ∃ o : R, t * c = γ * o) (Y : Submodule R (Matrix m n K)) {w : Matrix m n K}
    (hw : w ∈ I • Y) : ∃ s : R, s ∉ v.asIdeal ∧ s • ((algebraMap R K γ)⁻¹ • w) ∈ Y := by
  have hγ : algebraMap R K γ ≠ 0 := (map_ne_zero_iff _ (IsFractionRing.injective R K)).2 hγ0
  refine Submodule.smul_induction_on hw (fun c hc z hz => ?_) (fun w₁ w₂ h₁ h₂ => ?_)
  · obtain ⟨o, ho⟩ := hto c hc
    refine ⟨t, ht, ?_⟩
    have h' := congrArg (algebraMap R K) ho
    rw [map_mul, map_mul] at h'
    have : t • ((algebraMap R K γ)⁻¹ • (c • z)) = o • z := by
      rw [gh_rsmul t, gh_rsmul c, gh_rsmul o, smul_smul, smul_smul]
      congr 1
      rw [mul_right_comm, h', mul_comm (algebraMap R K γ), mul_assoc, mul_inv_cancel₀ hγ, mul_one]
    rw [this]; exact Y.smul_mem o hz
  · obtain ⟨s₁, hs₁, h₁⟩ := h₁
    obtain ⟨s₂, hs₂, h₂⟩ := h₂
    refine ⟨s₁ * s₂, fun h => (v.isPrime.mem_or_mem h).elim hs₁ hs₂, ?_⟩
    have e1 : (s₁ * s₂) • ((algebraMap R K γ)⁻¹ • w₁) = s₂ • (s₁ • ((algebraMap R K γ)⁻¹ • w₁)) := by
      rw [mul_comm, mul_smul]
    have e2 : (s₁ * s₂) • ((algebraMap R K γ)⁻¹ • w₂) = s₁ • (s₂ • ((algebraMap R K γ)⁻¹ • w₂)) := by
      rw [mul_smul]
    rw [smul_add, smul_add, e1, e2]
    exact add_mem (Y.smul_mem _ h₁) (Y.smul_mem _ h₂)

/- English proof (translation)
Establish `hγ : algebraMap R K γ ≠ 0` using `(map_ne_zero_iff _ (IsFractionRing.injective R K)).2 hγ0`. Use `gh_local_global _ (hcopB s hs) ?_ hB` and prove the remaining obligations. Establish `: s • w = γ • (s • ((algebraMap R K γ)⁻¹ • w))`. Rewrite using `[gh_rsmul γ, smul_comm (algebraMap R K γ) s, smul_smul, mul_inv_cancel₀ hγ, one_smul]`. Rewrite using `[this]`.

Conclude with `Submodule.smul_mem_smul hγI h`.
-/
theorem gh_read_bwd (I : Ideal R) {γ B : R} (v : HeightOneSpectrum R) (hγ0 : γ ≠ 0) (hγI : γ ∈ I)
    (hcopB : ∀ s : R, s ∉ v.asIdeal → IsCoprime s B) (Y : Submodule R (Matrix m n K)) {w : Matrix m n K}
    (hB : B • w ∈ I • Y) {s : R} (hs : s ∉ v.asIdeal) (h : s • ((algebraMap R K γ)⁻¹ • w) ∈ Y) :
    w ∈ I • Y := by
  have hγ : algebraMap R K γ ≠ 0 := (map_ne_zero_iff _ (IsFractionRing.injective R K)).2 hγ0
  refine gh_local_global _ (hcopB s hs) ?_ hB
  have : s • w = γ • (s • ((algebraMap R K γ)⁻¹ • w)) := by
    rw [gh_rsmul γ, smul_comm (algebraMap R K γ) s, smul_smul, mul_inv_cancel₀ hγ, one_smul]
  rw [this]; exact Submodule.smul_mem_smul hγI h

variable [Fintype m] [Fintype n]

/- English proof (translation)
Rewrite using `[← SetLike.mem_coe (x := matI v _), gh_hatY_coe, hC R K v m n Y d hd hl]`. Prove the components needed by the constructor for the conclusion. Conclude with `gh_read_fwd I v hγ0 ht hto Y`. Introduce and unpack `⟨s, hs, h⟩`. Conclude with `gh_read_bwd I v hγ0 hγI hcopB Y hB hs h`.
-/
theorem gh_read_iff (hC : ClosChar) (I : Ideal R) {γ t B : R} (v : HeightOneSpectrum R) (hγ0 : γ ≠ 0)
    (hγI : γ ∈ I) (ht : t ∉ v.asIdeal) (hto : ∀ c ∈ I, ∃ o : R, t * c = γ * o)
    (hcopB : ∀ s : R, s ∉ v.asIdeal → IsCoprime s B) (Y : Submodule R (Matrix m n K)) {d : R} (hd : d ≠ 0)
    (hl : LowB d (Y : Set (Matrix m n K))) {w : Matrix m n K} (hB : B • w ∈ I • Y) :
    w ∈ I • Y ↔ matI v ((algebraMap R K γ)⁻¹ • w) ∈ hatY v Y := by
  rw [← SetLike.mem_coe (x := matI v _), gh_hatY_coe, hC R K v m n Y d hd hl]
  constructor
  · exact gh_read_fwd I v hγ0 ht hto Y
  · rintro ⟨s, hs, h⟩
    exact gh_read_bwd I v hγ0 hγI hcopB Y hB hs h

/- English proof (translation)
Establish `hP : algebraMap R K π ≠ 0` using `(map_ne_zero_iff _ (IsFractionRing.injective R K)).2 hπ0`. Establish `hγ : algebraMap R K γ ≠ 0` using `(map_ne_zero_iff _ (IsFractionRing.injective R K)).2 hγ0`. Establish `hcopB : ∀ s : R, s ∉ v.asIdeal → IsCoprime s (π ^ e * π ^ e)` using `fun s hs =>`. Establish `h` using `(hcop s hs).pow_right (n := e)`. Use the proof step `h.mul_right h`.

Establish `hB : ∀ Y : Submodule R (Matrix m n K), (∀ z ∈ Y₀, (π * πb) ^ e • z ∈ Y) → ∀ w ∈ I • sMod u Y₀, (π ^ e * π ^ e) • w ∈ I • Y` using `fun Y hY => gh_fromHalf I hY (by rw [hu]; simp only [map_mul, map_pow]; exact pow_mul_pow_mul_div_pow_eq hP e)`. Establish `hE : ∀ w ∈ I • Y₁, (x * (πb ^ e * πb ^ e)) • w ∈ I • sMod u Y₀` using `gh_toHalf I (r := x * (π * πb) ^ e) (fun z hz => by rw [mul_smul]; exact Y₀.smul_mem x (h10 z hz)) (by rw [hu]; simp only [map_mul, map_pow]; exact div_pow_mul_prod_pow_left hP e)`. Establish `hmem : ∀ w ∈ I • Y₁ ⊓ I • sMod u Y₀, matI v ((algebraMap R K γ)⁻¹ • w) ∈ hatY v Y₁` using `fun w hw => (gh_read_iff hC I v hγ0 hγI ht hto hcopB Y₁ hd₁ hl₁ (hB Y₁ h01 w (Submodule.mem_inf.1 hw).2)).1 (Submodule.mem_inf.1 hw).1`. Set `φ : (I • Y₁ ⊓ I • sMod u Y₀).toAddSubgroup →+ hatY v Y₁` to `{ toFun := fun w => ⟨matI v ((algebraMap R K γ)⁻¹ • (w : Matrix m n K)), hmem w w.2⟩ map_zero' := by ext1; simp [gh_matI_zero] map_add' := fun w₁ w₂ => by ext1; simp [smul_add, gh_matI_add] }`. Set `ψ` to `(QuotientAddGroup.mk' ((hatY v Y₂).addSubgroupOf (hatY v Y₁))).comp φ`.

Establish `hker : ψ.ker = (I • Y₂ ⊓ I • sMod u Y₀).toAddSubgroup.addSubgroupOf (I • Y₁ ⊓ I • sMod u Y₀).toAddSubgroup`. Use extensionality with `w`. Establish `hwA : (w : Matrix m n K) ∈ I • sMod u Y₀` using `(Submodule.mem_inf.1 w.2).2`. Rewrite using `[AddMonoidHom.mem_ker, AddMonoidHom.comp_apply, QuotientAddGroup.mk'_apply, QuotientAddGroup.eq_zero_iff, AddSubgroup.mem_addSubgroupOf, AddSubgroup.mem_addSubgroupOf, Submodule.mem_toAddSubgroup, Submodule.mem_inf, gh_read_iff hC I v hγ0 hγI ht hto hcopB Y₂ hd₂ hl₂ (hB Y₂ h02 w …`. Conclude with `⟨fun h => ⟨h, hwA⟩, fun h => h.1⟩`.

Establish `hsurj : Function.Surjective ψ`. Introduce `q`. Take `⟨z, rfl⟩` from `QuotientAddGroup.mk_surjective q`. Establish `hz : (z : Matrix m n (v.adicCompletion K)) ∈ closure (matI v '' (Y₁ : Set (Matrix m n K)))`. Rewrite using `[← gh_hatY_coe]`.

Conclude with `z.2`. Take `⟨A, hA1, hAz⟩` from `hA R K v m n Y₁ (Y₁ ⊓ Y₂) (d₁ * d₂) (mul_ne_zero hd₁ hd₂) (gh_lowB_inf hl₁ hl₂) _ hz`. Establish `hγA : γ • A ∈ I • Y₁` using `Submodule.smul_mem_smul hγI hA1`. Establish `hw : (x * (πb ^ e * πb ^ e)) • (γ • A) ∈ I • Y₁ ⊓ I • sMod u Y₀` using `Submodule.mem_inf.2 ⟨Submodule.smul_mem _ _ hγA, hE _ hγA⟩`. Use `⟨⟨_, hw⟩, ?_⟩` and prove the remaining obligations.

Rewrite using `[AddMonoidHom.comp_apply, QuotientAddGroup.mk'_apply, QuotientAddGroup.eq, AddSubgroup.mem_addSubgroupOf]`. Use `show -(matI v ((algebraMap R K γ)⁻¹ • ((x * (πb ^ e * πb ^ e)) • (γ • A)))) + (z : Matrix m n (v.adicCompletion K)) ∈ hatY v Y₂`. Establish `k1 : (algebraMap R K γ)⁻¹ • ((x * (πb ^ e * πb ^ e)) • (γ • A)) = (x * (πb ^ e * πb ^ e)) • A`. Rewrite using `[gh_rsmul γ A, smul_comm (x * (πb ^ e * πb ^ e)) (algebraMap R K γ) A, smul_smul, inv_mul_cancel₀ hγ, one_smul]`. Establish `hcf : (x * (πb ^ e * πb ^ e)) • A + (y * (π ^ e * π ^ e)) • A = A`.

Rewrite using `[← add_smul, hxy, one_smul]`. Establish `hA' : matI v A = matI v ((x * (πb ^ e * πb ^ e)) • A) + matI v ((y * (π ^ e * π ^ e)) • A)`. Rewrite using `[← gh_matI_add, hcf]`. Establish `k2 : -(matI v ((x * (πb ^ e * πb ^ e)) • A)) + (z : Matrix m n (v.adicCompletion K)) = ((z : Matrix m n (v.adicCompletion K)) - matI v A) + matI v ((y * (π ^ e * π ^ e)) • A)`. Rewrite using `[hA']`.

Normalize the expressions using the abelian group laws. Rewrite using `[k1, k2]`. Use `add_mem ?_ ?_` and prove the remaining obligations. Rewrite using `[← SetLike.mem_coe, gh_hatY_coe]`. Conclude with `closure_mono (Set.image_mono (SetLike.coe_subset_coe.2 inf_le_right)) hAz`.

Rewrite using `[← SetLike.mem_coe, gh_hatY_coe, hC R K v m n Y₂ d₂ hd₂ hl₂]`. Use `⟨πb ^ e * πb ^ e, fun h => (v.isPrime.mem_or_mem h).elim (fun h' => hπb (v.isPrime.mem_of_pow_mem _ h')) (fun h' => hπb (v.isPrime.mem_of_pow_mem _ h')), ?_⟩` and prove the remaining obligations. Establish `: (πb ^ e * πb ^ e) • ((y * (π ^ e * π ^ e)) • A) = y • ((π * πb) ^ e • ((π * πb) ^ e • A))`. Simplify using `only [smul_smul]`. Use `congr 1`.

Expand and normalize the polynomial expressions, which then agree. Rewrite using `[this]`. Conclude with `Y₂.smul_mem y (h02 _ (h10 A hA1))`. Rewrite using `[AddSubgroup.relIndex, AddSubgroup.relIndex, AddSubgroup.index_eq_card, AddSubgroup.index_eq_card]`. Conclude with `Nat.card_congr ((QuotientAddGroup.quotientAddEquivOfEq hker.symm).trans (QuotientAddGroup.quotientKerEquivOfSurjective ψ hsurj)).toEquiv`.
-/
theorem gh_relIndex (hC : ClosChar) (hA : ApproxLow) (v : HeightOneSpectrum R) (I : Ideal R)
    {γ t π πb x y : R} {e : ℕ} {u : K} (hu : u = (algebraMap R K πb / algebraMap R K π) ^ e)
    (hγ0 : γ ≠ 0) (hγI : γ ∈ I) (ht : t ∉ v.asIdeal) (hto : ∀ c ∈ I, ∃ o : R, t * c = γ * o)
    (hπ0 : π ≠ 0) (hπb : πb ∉ v.asIdeal) (hcop : ∀ s : R, s ∉ v.asIdeal → IsCoprime s π)
    (hxy : x * (πb ^ e * πb ^ e) + y * (π ^ e * π ^ e) = 1)
    (Y₀ Y₁ Y₂ : Submodule R (Matrix m n K)) {d₁ d₂ : R} (hd₁ : d₁ ≠ 0) (hd₂ : d₂ ≠ 0)
    (hl₁ : LowB d₁ (Y₁ : Set (Matrix m n K))) (hl₂ : LowB d₂ (Y₂ : Set (Matrix m n K)))
    (h01 : ∀ z ∈ Y₀, (π * πb) ^ e • z ∈ Y₁) (h10 : ∀ z ∈ Y₁, (π * πb) ^ e • z ∈ Y₀)
    (h02 : ∀ z ∈ Y₀, (π * πb) ^ e • z ∈ Y₂) :
    (I • Y₂ ⊓ I • sMod u Y₀).toAddSubgroup.relIndex (I • Y₁ ⊓ I • sMod u Y₀).toAddSubgroup =
      (hatY v Y₂).relIndex (hatY v Y₁) := by
  have hP : algebraMap R K π ≠ 0 := (map_ne_zero_iff _ (IsFractionRing.injective R K)).2 hπ0
  have hγ : algebraMap R K γ ≠ 0 := (map_ne_zero_iff _ (IsFractionRing.injective R K)).2 hγ0
  have hcopB : ∀ s : R, s ∉ v.asIdeal → IsCoprime s (π ^ e * π ^ e) := fun s hs =>
    have h := (hcop s hs).pow_right (n := e); h.mul_right h
  have hB : ∀ Y : Submodule R (Matrix m n K), (∀ z ∈ Y₀, (π * πb) ^ e • z ∈ Y) →
      ∀ w ∈ I • sMod u Y₀, (π ^ e * π ^ e) • w ∈ I • Y := fun Y hY =>
    gh_fromHalf I hY (by rw [hu]; simp only [map_mul, map_pow]; exact pow_mul_pow_mul_div_pow_eq hP e)
  have hE : ∀ w ∈ I • Y₁, (x * (πb ^ e * πb ^ e)) • w ∈ I • sMod u Y₀ :=
    gh_toHalf I (r := x * (π * πb) ^ e) (fun z hz => by rw [mul_smul]; exact Y₀.smul_mem x (h10 z hz))
      (by rw [hu]; simp only [map_mul, map_pow]; exact div_pow_mul_prod_pow_left hP e)
  have hmem : ∀ w ∈ I • Y₁ ⊓ I • sMod u Y₀, matI v ((algebraMap R K γ)⁻¹ • w) ∈ hatY v Y₁ := fun w hw =>
    (gh_read_iff hC I v hγ0 hγI ht hto hcopB Y₁ hd₁ hl₁
      (hB Y₁ h01 w (Submodule.mem_inf.1 hw).2)).1 (Submodule.mem_inf.1 hw).1
  let φ : (I • Y₁ ⊓ I • sMod u Y₀).toAddSubgroup →+ hatY v Y₁ :=
    { toFun := fun w => ⟨matI v ((algebraMap R K γ)⁻¹ • (w : Matrix m n K)), hmem w w.2⟩
      map_zero' := by ext1; simp [gh_matI_zero]
      map_add' := fun w₁ w₂ => by ext1; simp [smul_add, gh_matI_add] }
  let ψ := (QuotientAddGroup.mk' ((hatY v Y₂).addSubgroupOf (hatY v Y₁))).comp φ
  have hker : ψ.ker = (I • Y₂ ⊓ I • sMod u Y₀).toAddSubgroup.addSubgroupOf
      (I • Y₁ ⊓ I • sMod u Y₀).toAddSubgroup := by
    ext w
    have hwA : (w : Matrix m n K) ∈ I • sMod u Y₀ := (Submodule.mem_inf.1 w.2).2
    rw [AddMonoidHom.mem_ker, AddMonoidHom.comp_apply, QuotientAddGroup.mk'_apply, QuotientAddGroup.eq_zero_iff,
      AddSubgroup.mem_addSubgroupOf, AddSubgroup.mem_addSubgroupOf, Submodule.mem_toAddSubgroup,
      Submodule.mem_inf, gh_read_iff hC I v hγ0 hγI ht hto hcopB Y₂ hd₂ hl₂ (hB Y₂ h02 w hwA)]
    exact ⟨fun h => ⟨h, hwA⟩, fun h => h.1⟩
  have hsurj : Function.Surjective ψ := by
    intro q
    obtain ⟨z, rfl⟩ := QuotientAddGroup.mk_surjective q
    have hz : (z : Matrix m n (v.adicCompletion K)) ∈ closure (matI v '' (Y₁ : Set (Matrix m n K))) := by
      rw [← gh_hatY_coe]; exact z.2
    obtain ⟨A, hA1, hAz⟩ := hA R K v m n Y₁ (Y₁ ⊓ Y₂) (d₁ * d₂) (mul_ne_zero hd₁ hd₂) (gh_lowB_inf hl₁ hl₂) _ hz
    have hγA : γ • A ∈ I • Y₁ := Submodule.smul_mem_smul hγI hA1
    have hw : (x * (πb ^ e * πb ^ e)) • (γ • A) ∈ I • Y₁ ⊓ I • sMod u Y₀ :=
      Submodule.mem_inf.2 ⟨Submodule.smul_mem _ _ hγA, hE _ hγA⟩
    refine ⟨⟨_, hw⟩, ?_⟩
    rw [AddMonoidHom.comp_apply, QuotientAddGroup.mk'_apply, QuotientAddGroup.eq, AddSubgroup.mem_addSubgroupOf]
    show -(matI v ((algebraMap R K γ)⁻¹ • ((x * (πb ^ e * πb ^ e)) • (γ • A)))) +
      (z : Matrix m n (v.adicCompletion K)) ∈ hatY v Y₂
    have k1 : (algebraMap R K γ)⁻¹ • ((x * (πb ^ e * πb ^ e)) • (γ • A)) = (x * (πb ^ e * πb ^ e)) • A := by
      rw [gh_rsmul γ A, smul_comm (x * (πb ^ e * πb ^ e)) (algebraMap R K γ) A, smul_smul,
        inv_mul_cancel₀ hγ, one_smul]
    have hcf : (x * (πb ^ e * πb ^ e)) • A + (y * (π ^ e * π ^ e)) • A = A := by
      rw [← add_smul, hxy, one_smul]
    have hA' : matI v A = matI v ((x * (πb ^ e * πb ^ e)) • A) + matI v ((y * (π ^ e * π ^ e)) • A) := by
      rw [← gh_matI_add, hcf]
    have k2 : -(matI v ((x * (πb ^ e * πb ^ e)) • A)) + (z : Matrix m n (v.adicCompletion K)) =
        ((z : Matrix m n (v.adicCompletion K)) - matI v A) + matI v ((y * (π ^ e * π ^ e)) • A) := by
      rw [hA']; abel
    rw [k1, k2]
    refine add_mem ?_ ?_
    · rw [← SetLike.mem_coe, gh_hatY_coe]
      exact closure_mono (Set.image_mono (SetLike.coe_subset_coe.2 inf_le_right)) hAz
    · rw [← SetLike.mem_coe, gh_hatY_coe, hC R K v m n Y₂ d₂ hd₂ hl₂]
      refine ⟨πb ^ e * πb ^ e, fun h => (v.isPrime.mem_or_mem h).elim
        (fun h' => hπb (v.isPrime.mem_of_pow_mem _ h')) (fun h' => hπb (v.isPrime.mem_of_pow_mem _ h')), ?_⟩
      have : (πb ^ e * πb ^ e) • ((y * (π ^ e * π ^ e)) • A) = y • ((π * πb) ^ e • ((π * πb) ^ e • A)) := by
        simp only [smul_smul]
        congr 1
        ring
      rw [this]
      exact Y₂.smul_mem y (h02 _ (h10 A hA1))
  rw [AddSubgroup.relIndex, AddSubgroup.relIndex, AddSubgroup.index_eq_card, AddSubgroup.index_eq_card]
  exact Nat.card_congr ((QuotientAddGroup.quotientAddEquivOfEq hker.symm).trans
    (QuotientAddGroup.quotientKerEquivOfSurjective ψ hsurj)).toEquiv

end Gen

/- English proof (translation)
Introduce `R _ _ K _ _ _ v m n _ _ I γ t π πb n₀ ι Y₀ Y hγ0 hγI ht hto hπ0 hπv hπb hcop hl0 hli h0i hi0 i`. Take `⟨d₀, hd₀, hl₀⟩` from `hl0`. Take `⟨d₁, hd₁, hl₁⟩` from `hli i`. Establish `hP : algebraMap R K π ≠ 0` using `(map_ne_zero_iff _ (IsFractionRing.injective R K)).2 hπ0`. Establish `hQ : algebraMap R K πb ≠ 0` using `(map_ne_zero_iff _ (IsFractionRing.injective R K)).2 (fun h => hπb (h ▸ v.asIdeal.zero_mem))`.

Establish `hcopB : ∀ s : R, s ∉ v.asIdeal → IsCoprime s (π ^ n₀ * π ^ n₀)` using `fun s hs =>`. Establish `h` using `(hcop s hs).pow_right (n := n₀)`. Use the proof step `h.mul_right h`. Choose the witnesses or unpack the hypotheses as in `⟨x, y, hxy⟩ : IsCoprime (πb ^ n₀ * πb ^ n₀) (π ^ n₀ * π ^ n₀) := by`. Establish `h` using `(hcop πb hπb).pow (m := n₀) (n := n₀)`.

Establish `h'` using `h.mul_left h`. Conclude with `h'.mul_right h'`. Establish `h00 : ∀ z ∈ Y₀, (π * πb) ^ n₀ • z ∈ Y₀` using `fun z hz => Y₀.smul_mem _ hz`. Introduce `u MA MB`. Use `⟨?_, ?_, ?_, ?_, ?_⟩` and prove the remaining obligations.

Introduce `w hw`. Use `⟨(x * (πb ^ n₀ * πb ^ n₀)) • w, Submodule.mem_inf.2 ⟨Submodule.smul_mem _ _ hw, ?_⟩, (y * (π ^ n₀ * π ^ n₀)) • w, Submodule.mem_inf.2 ⟨Submodule.smul_mem _ _ hw, ?_⟩, ?_⟩` and prove the remaining obligations. Conclude with `gh_toHalf I (r := x * (π * πb) ^ n₀) (fun z hz => by rw [mul_smul]; exact Y₀.smul_mem x (hi0 i z hz)) (by simp only [u, map_mul, map_pow]; exact div_pow_mul_prod_pow_left hP n₀) w hw`. Conclude with `gh_toHalf I (r := y * (π * πb) ^ n₀) (fun z hz => by rw [mul_smul]; exact Y₀.smul_mem y (hi0 i z hz)) (by simp only [u, map_mul, map_pow]; exact inv_div_pow_mul_prod_pow_right hQ n₀) w hw`. Rewrite using `[← add_smul, hxy, one_smul]`.

Introduce `a ha b hb hab`. Establish `hfa : (y * (π ^ n₀ * π ^ n₀)) • a ∈ I • Y i` using `gh_fromHalf I (r := y * (π * πb) ^ n₀) (fun z hz => by rw [mul_smul]; exact (Y i).smul_mem y (h0i i z hz)) (by simp only [u, map_mul, map_pow]; exact sq_pow_mul_div_pow_eq_prod_pow hP n₀) a ha`. Establish `heb : (x * (πb ^ n₀ * πb ^ n₀)) • b ∈ I • Y i` using `gh_fromHalf I (r := x * (π * πb) ^ n₀) (fun z hz => by rw [mul_smul]; exact (Y i).smul_mem x (h0i i z hz)) (by simp only [u, map_mul, map_pow]; exact sq_pow_mul_inv_div_pow_eq_prod_pow hQ n₀) b hb`. Establish `h1 : (x * (πb ^ n₀ * πb ^ n₀)) • (a + b) + (y * (π ^ n₀ * π ^ n₀)) • a - (x * (πb ^ n₀ * πb ^ n₀)) • b = (x * (πb ^ n₀ * πb ^ n₀) + y * (π ^ n₀ * π ^ n₀)) • a`. Rewrite using `[smul_add, add_smul]`.

Normalize the expressions using the abelian group laws. Rewrite `h1` using `[hxy, one_smul]`. Rewrite using `[← h1]`. Conclude with `sub_mem (add_mem (Submodule.smul_mem _ _ hab) hfa) heb`. Introduce `a ha`.

Conclude with `gh_read_iff hC I v hγ0 hγI ht hto hcopB (Y i) hd₁ hl₁ (gh_fromHalf I (r := (π * πb) ^ n₀) (h0i i) (by simp only [u, map_mul, map_pow]; exact pow_mul_pow_mul_div_pow_eq hP n₀) a ha)`. Conclude with `gh_relIndex hC hA v I rfl hγ0 hγI ht hto hπ0 hπb hcop hxy Y₀ (Y i) Y₀ hd₁ hd₀ hl₁ hl₀ (h0i i) (hi0 i) h00`. Conclude with `gh_relIndex hC hA v I rfl hγ0 hγI ht hto hπ0 hπb hcop hxy Y₀ Y₀ (Y i) hd₀ hd₁ hl₀ hl₁ h00 h00 (h0i i)`.
-/
theorem genHalves_of (hC : ClosChar) (hA : ApproxLow) : GenHalves := by
  intro R _ _ K _ _ _ v m n _ _ I γ t π πb n₀ ι Y₀ Y hγ0 hγI ht hto hπ0 hπv hπb hcop hl0 hli h0i hi0 i
  obtain ⟨d₀, hd₀, hl₀⟩ := hl0
  obtain ⟨d₁, hd₁, hl₁⟩ := hli i
  have hP : algebraMap R K π ≠ 0 := (map_ne_zero_iff _ (IsFractionRing.injective R K)).2 hπ0
  have hQ : algebraMap R K πb ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective R K)).2 (fun h => hπb (h ▸ v.asIdeal.zero_mem))
  have hcopB : ∀ s : R, s ∉ v.asIdeal → IsCoprime s (π ^ n₀ * π ^ n₀) := fun s hs =>
    have h := (hcop s hs).pow_right (n := n₀); h.mul_right h
  obtain ⟨x, y, hxy⟩ : IsCoprime (πb ^ n₀ * πb ^ n₀) (π ^ n₀ * π ^ n₀) := by
    have h := (hcop πb hπb).pow (m := n₀) (n := n₀)
    have h' := h.mul_left h
    exact h'.mul_right h'
  have h00 : ∀ z ∈ Y₀, (π * πb) ^ n₀ • z ∈ Y₀ := fun z hz => Y₀.smul_mem _ hz
  intro u MA MB
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro w hw
    refine ⟨(x * (πb ^ n₀ * πb ^ n₀)) • w, Submodule.mem_inf.2 ⟨Submodule.smul_mem _ _ hw, ?_⟩,
      (y * (π ^ n₀ * π ^ n₀)) • w, Submodule.mem_inf.2 ⟨Submodule.smul_mem _ _ hw, ?_⟩, ?_⟩
    · exact gh_toHalf I (r := x * (π * πb) ^ n₀)
        (fun z hz => by rw [mul_smul]; exact Y₀.smul_mem x (hi0 i z hz))
        (by simp only [u, map_mul, map_pow]; exact div_pow_mul_prod_pow_left hP n₀) w hw
    · exact gh_toHalf I (r := y * (π * πb) ^ n₀)
        (fun z hz => by rw [mul_smul]; exact Y₀.smul_mem y (hi0 i z hz))
        (by simp only [u, map_mul, map_pow]; exact inv_div_pow_mul_prod_pow_right hQ n₀) w hw
    · rw [← add_smul, hxy, one_smul]
  · intro a ha b hb hab
    have hfa : (y * (π ^ n₀ * π ^ n₀)) • a ∈ I • Y i :=
      gh_fromHalf I (r := y * (π * πb) ^ n₀)
        (fun z hz => by rw [mul_smul]; exact (Y i).smul_mem y (h0i i z hz))
        (by simp only [u, map_mul, map_pow]; exact sq_pow_mul_div_pow_eq_prod_pow hP n₀) a ha
    have heb : (x * (πb ^ n₀ * πb ^ n₀)) • b ∈ I • Y i :=
      gh_fromHalf I (r := x * (π * πb) ^ n₀)
        (fun z hz => by rw [mul_smul]; exact (Y i).smul_mem x (h0i i z hz))
        (by simp only [u, map_mul, map_pow]; exact sq_pow_mul_inv_div_pow_eq_prod_pow hQ n₀) b hb
    have h1 : (x * (πb ^ n₀ * πb ^ n₀)) • (a + b) + (y * (π ^ n₀ * π ^ n₀)) • a -
        (x * (πb ^ n₀ * πb ^ n₀)) • b = (x * (πb ^ n₀ * πb ^ n₀) + y * (π ^ n₀ * π ^ n₀)) • a := by
      rw [smul_add, add_smul]; abel
    rw [hxy, one_smul] at h1
    rw [← h1]
    exact sub_mem (add_mem (Submodule.smul_mem _ _ hab) hfa) heb
  · intro a ha
    exact gh_read_iff hC I v hγ0 hγI ht hto hcopB (Y i) hd₁ hl₁
      (gh_fromHalf I (r := (π * πb) ^ n₀) (h0i i)
        (by simp only [u, map_mul, map_pow]; exact pow_mul_pow_mul_div_pow_eq hP n₀) a ha)
  · exact gh_relIndex hC hA v I rfl hγ0 hγI ht hto hπ0 hπb hcop hxy Y₀ (Y i) Y₀ hd₁ hd₀ hl₁ hl₀
      (h0i i) (hi0 i) h00
  · exact gh_relIndex hC hA v I rfl hγ0 hγI ht hto hπ0 hπb hcop hxy Y₀ Y₀ (Y i) hd₀ hd₁ hl₀ hl₁
      h00 h00 (h0i i)

end Formalism.L2.PairingIndexBounds.Rec

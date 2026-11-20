import Mathlib
import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.IsHermForm

noncomputable section

namespace GlobalTheory.UnRepCheck

open NumberField IsDedekindDomain GlobalTheory.AdLat GlobalTheory.UnRep
open scoped TensorProduct Matrix

variable {F E : Type} [Field F] [Field E] [Algebra F E] [NumberField F]

/- English proof (translation)
Simplify using `only [hermA, fm, dotProduct, Matrix.mulVec, Matrix.map_apply, Finset.mul_sum, Function.comp, mul_assoc]`.
-/
theorem hermA_eq (c : E ≃ₐ[F] E) {n : ℕ} (G : Matrix (Fin n) (Fin n) E) (x y : Fin n → RA F E) :
    hermA c G x y = x ⬝ᵥ (fm F G *ᵥ (sg (FiniteAdeleRing (𝓞 F) F) c ∘ y)) := by
  simp only [hermA, fm, dotProduct, Matrix.mulVec, Matrix.map_apply, Finset.mul_sum, Function.comp, mul_assoc]

/- English proof (translation)
Simplify using `only [hermA_eq, smul_dotProduct, smul_eq_mul]`.
-/
theorem hermA_smul_left (c : E ≃ₐ[F] E) {n : ℕ} (G : Matrix (Fin n) (Fin n) E) (a : RA F E)
    (x y : Fin n → RA F E) : hermA c G (a • x) y = a * hermA c G x y := by
  simp only [hermA_eq, smul_dotProduct, smul_eq_mul]

/- English proof (translation)
Establish `key : ∀ x y, hermA c G (g *ᵥ x) (g *ᵥ y) = x ⬝ᵥ ((gᵀ * fm F G * g.map (sg (FiniteAdeleRing (𝓞 F) F) c)) *ᵥ (sg (FiniteAdeleRing (𝓞 F) F) c ∘ y))`. Introduce `x y`. Establish `h1 : sg (FiniteAdeleRing (𝓞 F) F) c ∘ (g *ᵥ y) = g.map (sg (FiniteAdeleRing (𝓞 F) F) c) *ᵥ (sg (FiniteAdeleRing (𝓞 F) F) c ∘ y)`. Use function extensionality and compare the values at `i`. Simplify using `[Matrix.mulVec, dotProduct]`.

Rewrite using `[hermA_eq, h1, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec x gᵀ, Matrix.vecMul_transpose]`. Prove the components needed by the constructor for the conclusion. Introduce `h`. Use extensionality with `i j : 2`. Use `h (Pi.single i 1) (Pi.single j 1)` as an intermediate fact.

Rewrite `this` using `[key, hermA_eq]`. Establish `h2 : sg (FiniteAdeleRing (𝓞 F) F) c ∘ (Pi.single j 1 : Fin n → RA F E) = Pi.single j 1`. Use function extensionality and compare the values at `k`. Distinguish the cases in `hk : k = j`. Substitute `hk` using the available equality.

Simplify using the standard rewrite rules. Simplify using `[Pi.single_eq_of_ne hk]`. Rewrite `this` using `[h2]`. Simplify using `using this`. Introduce `h x y`.

Rewrite using `[key, h, hermA_eq]`.
-/
theorem isUnA_iff (c : E ≃ₐ[F] E) {n : ℕ} (G : Matrix (Fin n) (Fin n) E) (g : Matrix (Fin n) (Fin n) (RA F E)) :
    IsUnA c G g ↔ gᵀ * fm F G * g.map (sg (FiniteAdeleRing (𝓞 F) F) c) = fm F G := by
  have key : ∀ x y, hermA c G (g *ᵥ x) (g *ᵥ y) =
      x ⬝ᵥ ((gᵀ * fm F G * g.map (sg (FiniteAdeleRing (𝓞 F) F) c)) *ᵥ (sg (FiniteAdeleRing (𝓞 F) F) c ∘ y)) := by
    intro x y
    have h1 : sg (FiniteAdeleRing (𝓞 F) F) c ∘ (g *ᵥ y) =
        g.map (sg (FiniteAdeleRing (𝓞 F) F) c) *ᵥ (sg (FiniteAdeleRing (𝓞 F) F) c ∘ y) := by
      funext i; simp [Matrix.mulVec, dotProduct]
    rw [hermA_eq, h1, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec x gᵀ,
      Matrix.vecMul_transpose]
  constructor
  · intro h
    ext i j : 2
    have := h (Pi.single i 1) (Pi.single j 1)
    rw [key, hermA_eq] at this
    have h2 : sg (FiniteAdeleRing (𝓞 F) F) c ∘ (Pi.single j 1 : Fin n → RA F E) = Pi.single j 1 := by
      funext k; by_cases hk : k = j
      · subst hk; simp
      · simp [Pi.single_eq_of_ne hk]
    rw [h2] at this
    simpa using this
  · intro h x y
    rw [key, h, hermA_eq]

/- English proof (translation)
Establish `h1` using `congrArg Matrix.det ((isUnA_iff c G g).1 h)`. Establish `hu : IsUnit (fm F G).det`. Establish `: (fm F G).det = (Algebra.TensorProduct.includeRight : E →ₐ[F] RA F E) G.det` using `(AlgHom.map_det (Algebra.TensorProduct.includeRight : E →ₐ[F] RA F E) G).symm`. Rewrite using `[this]`. Conclude with `(IsUnit.mk0 _ hG).map _`.

Establish `h2 : (g.map (sg (FiniteAdeleRing (𝓞 F) F) c)).det = sg (FiniteAdeleRing (𝓞 F) F) c g.det` using `(AlgHom.map_det (sg (FiniteAdeleRing (𝓞 F) F) c) g).symm`. Rewrite `h1` using `[Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, h2]`. Apply `hu.mul_left_cancel` to reduce the goal to its premises. Take the linear combination `h1`.
-/
theorem det_norm_one (c : E ≃ₐ[F] E) {n : ℕ} {G : Matrix (Fin n) (Fin n) E} (hG : G.det ≠ 0)
    {g : Matrix (Fin n) (Fin n) (RA F E)} (h : IsUnA c G g) :
    g.det * sg (FiniteAdeleRing (𝓞 F) F) c g.det = 1 := by
  have h1 := congrArg Matrix.det ((isUnA_iff c G g).1 h)
  have hu : IsUnit (fm F G).det := by
    have : (fm F G).det = (Algebra.TensorProduct.includeRight : E →ₐ[F] RA F E) G.det :=
      (AlgHom.map_det (Algebra.TensorProduct.includeRight : E →ₐ[F] RA F E) G).symm
    rw [this]; exact (IsUnit.mk0 _ hG).map _
  have h2 : (g.map (sg (FiniteAdeleRing (𝓞 F) F) c)).det = sg (FiniteAdeleRing (𝓞 F) F) c g.det :=
    (AlgHom.map_det (sg (FiniteAdeleRing (𝓞 F) F) c) g).symm
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, h2] at h1
  apply hu.mul_left_cancel
  linear_combination h1

/- English proof (translation)
Introduce `x y`. Simplify using `[hermA]`.
-/
theorem isUnA_zero (c : E ≃ₐ[F] E) {n : ℕ} (g : Matrix (Fin n) (Fin n) (RA F E)) : IsUnA c 0 g := by
  intro x y; simp [hermA]

/- English proof (translation)
Assemble the required witnesses or components as `⟨0, by simp, fun _ _ => ⟨0, zero_mem _, by simp⟩⟩`.
-/
theorem congAtA_level_one {n : ℕ} (L : Submodule (𝓞 E) (Fin n → E)) (D : ℕ) (k : Matrix (Fin n) (Fin n) (RA F E)) :
    CongAtA F L 1 D k := ⟨0, by simp, fun _ _ => ⟨0, zero_mem _, by simp⟩⟩

/- English proof (translation)
Take `⟨t, ht, h⟩` from `h`. Introduce `z hz`. Take `⟨w, -, hw⟩` from `h z hz`. Establish `ht0 : (t : F) ≠ 0`. Establish `: t ≠ 0` using `by rintro rfl; exact hN (by simpa using ht)`.

Conclude with `this` after adjusting the coercions. Rewrite `hw` using `[zero_smul, ← Nat.cast_smul_eq_nsmul F]`. Conclude with `sub_eq_zero.1 ((smul_eq_zero_iff_right ht0).1 hw)`.
-/
theorem congAtA_mod_zero {n N : ℕ} (hN : N ≠ 1) (L : Submodule (𝓞 E) (Fin n → E))
    {k : Matrix (Fin n) (Fin n) (RA F E)} (h : CongAtA F L N 0 k) :
    ∀ z ∈ hat F (L : Set (Fin n → E)), k *ᵥ z = z := by
  obtain ⟨t, ht, h⟩ := h
  intro z hz
  obtain ⟨w, -, hw⟩ := h z hz
  have ht0 : (t : F) ≠ 0 := by
    have : t ≠ 0 := by rintro rfl; exact hN (by simpa using ht)
    exact_mod_cast this
  rw [zero_smul, ← Nat.cast_smul_eq_nsmul F] at hw
  exact sub_eq_zero.1 ((smul_eq_zero_iff_right ht0).1 hw)

/- English proof (translation)
Use `⟨1, by simp, fun z hz => ⟨0, zero_mem _, ?_⟩⟩` and prove the remaining obligations. Establish `: hat F ((⊥ : Submodule (𝓞 E) (Fin n → E)) : Set (Fin n → E)) ≤ ⊥`. Rewrite using `[hat, AddSubgroup.closure_le]`. Introduce and unpack `_ ⟨a, -, x, hx, rfl⟩`. Establish `: x = 0` using `by simpa using hx`.

Substitute `this` using the available equality. Use function extensionality and compare the values at `i`. Simplify using the standard rewrite rules. Establish `hz0 : z = 0` using `this hz`. Simplify using `[hz0]`.
-/
theorem congAtA_bot {n N D : ℕ} (k : Matrix (Fin n) (Fin n) (RA F E)) :
    CongAtA F (⊥ : Submodule (𝓞 E) (Fin n → E)) N D k := by
  refine ⟨1, by simp, fun z hz => ⟨0, zero_mem _, ?_⟩⟩
  have : hat F ((⊥ : Submodule (𝓞 E) (Fin n → E)) : Set (Fin n → E)) ≤ ⊥ := by
    rw [hat, AddSubgroup.closure_le]
    rintro _ ⟨a, -, x, hx, rfl⟩
    have : x = 0 := by simpa using hx
    subst this; funext i; simp
  have hz0 : z = 0 := this hz
  simp [hz0]

/- English proof (translation)
Take `⟨t, ht, h⟩` from `h`. Take `⟨t', ht', h'⟩` from `h'`. Use `⟨t * t', Nat.Coprime.mul_left ht ht', fun z hz => ?_⟩` and prove the remaining obligations. Take `⟨w', hw', e'⟩` from `h' z hz`. Take `⟨w, hw, e⟩` from `h z hz`.

Take `⟨u, hu, eu⟩` from `h w' hw'`. Use `⟨D • u + t • w' + t' • w, add_mem (add_mem (nsmul_mem hu _) (nsmul_mem hw' _)) (nsmul_mem hw _), ?_⟩` and prove the remaining obligations. Establish `e2 : t' • (k *ᵥ (k' *ᵥ z) - k *ᵥ z) = D • (k *ᵥ w')`. Rewrite using `[← Matrix.mulVec_sub, ← Matrix.mulVec_smul, e', Matrix.mulVec_smul]`. Rewrite using `[← Matrix.mulVec_mulVec]`.

Take the linear combination `(exp := 1) t • e2 + t' • e + D • eu`.
-/
theorem congAtA_mul {n N D : ℕ} {L : Submodule (𝓞 E) (Fin n → E)} {k k' : Matrix (Fin n) (Fin n) (RA F E)}
    (h : CongAtA F L N D k) (h' : CongAtA F L N D k') : CongAtA F L N D (k * k') := by
  obtain ⟨t, ht, h⟩ := h
  obtain ⟨t', ht', h'⟩ := h'
  refine ⟨t * t', Nat.Coprime.mul_left ht ht', fun z hz => ?_⟩
  obtain ⟨w', hw', e'⟩ := h' z hz
  obtain ⟨w, hw, e⟩ := h z hz
  obtain ⟨u, hu, eu⟩ := h w' hw'
  refine ⟨D • u + t • w' + t' • w, add_mem (add_mem (nsmul_mem hu _) (nsmul_mem hw' _)) (nsmul_mem hw _), ?_⟩
  have e2 : t' • (k *ᵥ (k' *ᵥ z) - k *ᵥ z) = D • (k *ᵥ w') := by
    rw [← Matrix.mulVec_sub, ← Matrix.mulVec_smul, e', Matrix.mulVec_smul]
  rw [← Matrix.mulVec_mulVec]
  linear_combination (exp := 1) t • e2 + t' • e + D • eu

/- English proof (translation)
Take `⟨e, -, -, he, h1⟩` from `hh`. Establish `: e = 0`. Use extensionality with `v : 1`. Assume the negation of the conclusion as `hv`. Conclude with `(he v hv).2 (by simp)`.

Rewrite `h1` using `[this]`. Conclude with `sub_eq_zero.1 (by simpa using h1.symm)`.
-/
theorem suppSplit_zero (c : E ≃ₐ[F] E) {n : ℕ} {h : Matrix (Fin n) (Fin n) (RA F E)} (hh : SuppSplit c 0 h) :
    h = 1 := by
  obtain ⟨e, -, -, he, h1⟩ := hh
  have : e = 0 := by
    ext v : 1
    by_contra hv
    exact (he v hv).2 (by simp)
  rw [this] at h1
  exact sub_eq_zero.1 (by simpa using h1.symm)

/- English proof (translation)
Take `⟨e, -, -, he, h1⟩` from `hh`. Establish `: a * e = 0`. Use extensionality with `v : 1`. Express the relevant statement in the definitionally equal form `a v * e v = 0`. Distinguish the cases in `hv : e v = 0`.

Simplify using `[hv]`. Simplify using `[ha v (he v hv).1 (he v hv).2]`. Rewrite using `[← h1, smul_smul, Algebra.TensorProduct.tmul_mul_tmul, this]`. Simplify using the standard rewrite rules.
-/
theorem suppSplit_kill (c : E ≃ₐ[F] E) {n N : ℕ} {h : Matrix (Fin n) (Fin n) (RA F E)} (hh : SuppSplit c N h)
    (a : FiniteAdeleRing (𝓞 F) F) (ha : ∀ v, SplitPl c v → (N : 𝓞 F) ∉ v.asIdeal → a v = 0) :
    (a ⊗ₜ[F] (1 : E)) • (h - 1) = 0 := by
  obtain ⟨e, -, -, he, h1⟩ := hh
  have : a * e = 0 := by
    ext v : 1
    change a v * e v = 0
    by_cases hv : e v = 0
    · simp [hv]
    · simp [ha v (he v hv).1 (he v hv).2]
  rw [← h1, smul_smul, Algebra.TensorProduct.tmul_mul_tmul, this]
  simp

/- English proof (translation)
Take `⟨e, ee, fe, he, h1⟩` from `hh`. Take `⟨e', ee', fe', he', h1'⟩` from `hh'`. Establish `hv : ∀ v, (e + e' - e * e') v ≠ 0 → e v ≠ 0 ∨ e' v ≠ 0`. Introduce `v hv`. Assume the negation of the conclusion as `hc`.

Use `push Not at hc`. Apply `hv` to reduce the goal to its premises. Express the relevant statement in the definitionally equal form `e v + e' v - e v * e' v = 0`. Simplify using `[hc.1, hc.2]`. Use `⟨e + e' - e * e', by linear_combination (1 - 2 * e' + e' * e') * ee + (1 - e) * ee', (fe.union fe').subset fun v h => hv v h, fun v h => (hv v h).elim (he v) (he' v), ?_⟩` and prove the remaining obligations.

Establish `a1 : ((e + e' - e * e') ⊗ₜ[F] (1 : E) : RA F E) • (h - 1) = h - 1`. Rewrite using `[← h1, smul_smul, Algebra.TensorProduct.tmul_mul_tmul, one_mul]`. Use `congr 2`. Take the linear combination `(1 - e') * ee`. Establish `a2 : ((e + e' - e * e') ⊗ₜ[F] (1 : E) : RA F E) • (h' - 1) = h' - 1`.

Rewrite using `[← h1', smul_smul, Algebra.TensorProduct.tmul_mul_tmul, one_mul]`. Use `congr 2`. Take the linear combination `(1 - e) * ee'`. Establish `: h * h' - 1 = (h - 1) * h' + (h' - 1)` using `by noncomm_ring`. Rewrite using `[this, smul_add, ← smul_mul_assoc, a1, a2]`.
-/
theorem suppSplit_mul (c : E ≃ₐ[F] E) {n N : ℕ} {h h' : Matrix (Fin n) (Fin n) (RA F E)} (hh : SuppSplit c N h)
    (hh' : SuppSplit c N h') : SuppSplit c N (h * h') := by
  obtain ⟨e, ee, fe, he, h1⟩ := hh
  obtain ⟨e', ee', fe', he', h1'⟩ := hh'
  have hv : ∀ v, (e + e' - e * e') v ≠ 0 → e v ≠ 0 ∨ e' v ≠ 0 := by
    intro v hv
    by_contra hc
    push Not at hc
    apply hv
    change e v + e' v - e v * e' v = 0
    simp [hc.1, hc.2]
  refine ⟨e + e' - e * e', by linear_combination (1 - 2 * e' + e' * e') * ee + (1 - e) * ee',
    (fe.union fe').subset fun v h => hv v h, fun v h => (hv v h).elim (he v) (he' v), ?_⟩
  have a1 : ((e + e' - e * e') ⊗ₜ[F] (1 : E) : RA F E) • (h - 1) = h - 1 := by
    rw [← h1, smul_smul, Algebra.TensorProduct.tmul_mul_tmul, one_mul]
    congr 2; linear_combination (1 - e') * ee
  have a2 : ((e + e' - e * e') ⊗ₜ[F] (1 : E) : RA F E) • (h' - 1) = h' - 1 := by
    rw [← h1', smul_smul, Algebra.TensorProduct.tmul_mul_tmul, one_mul]
    congr 2; linear_combination (1 - e) * ee'
  have : h * h' - 1 = (h - 1) * h' + (h' - 1) := by noncomm_ring
  rw [this, smul_add, ← smul_mul_assoc, a1, a2]

/- English proof (translation)
Take `⟨e, ee, fe, he, h1⟩` from `hh`. Use `⟨e, ee, fe, he, ?_⟩` and prove the remaining obligations. Establish `: (h⁻¹).1 - 1 = -((h.1 - 1) * (h⁻¹).1)` using `by rw [sub_mul, h.mul_inv, one_mul, neg_sub]`. Rewrite using `[this, smul_neg, ← smul_mul_assoc, h1]`.
-/
theorem suppSplit_inv (c : E ≃ₐ[F] E) {n N : ℕ} {h : GL (Fin n) (RA F E)} (hh : SuppSplit c N h.1) :
    SuppSplit c N (h⁻¹).1 := by
  obtain ⟨e, ee, fe, he, h1⟩ := hh
  refine ⟨e, ee, fe, he, ?_⟩
  have : (h⁻¹).1 - 1 = -((h.1 - 1) * (h⁻¹).1) := by rw [sub_mul, h.mul_inv, one_mul, neg_sub]
  rw [this, smul_neg, ← smul_mul_assoc, h1]

/- English proof (translation)
Take `⟨P, hP, hv, a, ha, b, hb, hbP⟩` from `h`. Use `⟨P, P.comap (RingOfIntegers.mapRingHom (c : E →+* E)), hP, Ideal.comap_isPrime _ _, fun he => hbP ?_, hv, ?_⟩` and prove the remaining obligations. Establish `h1 : a ∈ P.comap (RingOfIntegers.mapRingHom (c : E →+* E))` using `he ▸ ha`. Establish `: RingOfIntegers.mapRingHom (c : E →+* E) a = b` using `RingOfIntegers.ext hb.symm`. Rewrite `h1` using `[Ideal.mem_comap, this]`. Then use the resulting hypothesis.

Rewrite using `[← hv, Ideal.comap_comap]`. Use `congr 1`. Use extensionality with `x`. Conclude with `c.commutes (x : F)`.
-/
theorem two_primes_of_splitPl (c : E ≃ₐ[F] E) {v : HeightOneSpectrum (𝓞 F)} (h : SplitPl c v) :
    ∃ P Q : Ideal (𝓞 E), P.IsPrime ∧ Q.IsPrime ∧ P ≠ Q ∧ P.comap (algebraMap (𝓞 F) (𝓞 E)) = v.asIdeal ∧
      Q.comap (algebraMap (𝓞 F) (𝓞 E)) = v.asIdeal := by
  obtain ⟨P, hP, hv, a, ha, b, hb, hbP⟩ := h
  refine ⟨P, P.comap (RingOfIntegers.mapRingHom (c : E →+* E)), hP, Ideal.comap_isPrime _ _, fun he => hbP ?_, hv, ?_⟩
  · have h1 : a ∈ P.comap (RingOfIntegers.mapRingHom (c : E →+* E)) := he ▸ ha
    have : RingOfIntegers.mapRingHom (c : E →+* E) a = b := RingOfIntegers.ext hb.symm
    rwa [Ideal.mem_comap, this] at h1
  · rw [← hv, Ideal.comap_comap]
    congr 1
    ext x
    exact c.commutes (x : F)

/- English proof (translation)
Use `haveI : Algebra.IsQuadraticExtension F E := ⟨h2⟩`. Use `haveI : IsGalois F E := inferInstance`. Use `haveI : P.LiesOver v.asIdeal := ⟨h1.symm⟩`. Use `haveI : Q.LiesOver v.asIdeal := ⟨h1'.symm⟩`. Take `⟨σ, hσ⟩` from `Ideal.exists_smul_eq_of_isGaloisGroup v.asIdeal P Q (E ≃ₐ[F] E)`.

Establish `hcard : Nat.card (E ≃ₐ[F] E) = 2` using `by rw [IsGalois.card_aut_eq_finrank, h2]`. Establish `hσc : σ = 1 ∨ σ = c`. Assume the negation of the conclusion as `hh`. Use `push Not at hh`. Take `⟨y, -, hy⟩` from `(Nat.card_eq_two_iff' (1 : E ≃ₐ[F] E)).1 hcard`.

Conclude with `hh.2 ((hy σ hh.1).trans (hy c hc).symm)`. Break down `hσc with rfl | rfl` into its components or cases. Conclude with `(hne (by simpa using hσ)).elim`. Use `⟨P, hP, h1, ?_⟩` and prove the remaining obligations. Assume the negation of the conclusion as `hm`.

Establish `hle : Q ≤ P`. Rewrite using `[← hσ]`. Introduce `b hb`. Assume the negation of the conclusion as `hb'`. Conclude with `hm ⟨σ⁻¹ • b, Ideal.mem_pointwise_smul_iff_inv_smul_mem.1 hb, b, (congrArg (fun x : 𝓞 E => (x : E)) (smul_inv_smul σ b)).symm, hb'⟩`.

Establish `hQ0 : Q ≠ ⊥`. Introduce and unpack `rfl`. Conclude with `v.ne_bot (by rw [← h1']; exact Ideal.comap_bot_of_injective _ (FaithfulSMul.algebraMap_injective _ _))`. Conclude with `hne ((hQ.isMaximal hQ0).eq_of_le hP.ne_top hle).symm`.
-/
theorem splitPl_of_two_primes [NumberField E] (c : E ≃ₐ[F] E) (hc : c ≠ 1) (h2 : Module.finrank F E = 2)
    {v : HeightOneSpectrum (𝓞 F)} {P Q : Ideal (𝓞 E)} (hP : P.IsPrime) (hQ : Q.IsPrime) (hne : P ≠ Q)
    (h1 : P.comap (algebraMap (𝓞 F) (𝓞 E)) = v.asIdeal) (h1' : Q.comap (algebraMap (𝓞 F) (𝓞 E)) = v.asIdeal) :
    SplitPl c v := by
  haveI : Algebra.IsQuadraticExtension F E := ⟨h2⟩
  haveI : IsGalois F E := inferInstance
  haveI : P.LiesOver v.asIdeal := ⟨h1.symm⟩
  haveI : Q.LiesOver v.asIdeal := ⟨h1'.symm⟩
  obtain ⟨σ, hσ⟩ := Ideal.exists_smul_eq_of_isGaloisGroup v.asIdeal P Q (E ≃ₐ[F] E)
  have hcard : Nat.card (E ≃ₐ[F] E) = 2 := by rw [IsGalois.card_aut_eq_finrank, h2]
  have hσc : σ = 1 ∨ σ = c := by
    by_contra hh
    push Not at hh
    obtain ⟨y, -, hy⟩ := (Nat.card_eq_two_iff' (1 : E ≃ₐ[F] E)).1 hcard
    exact hh.2 ((hy σ hh.1).trans (hy c hc).symm)
  rcases hσc with rfl | rfl
  · exact (hne (by simpa using hσ)).elim
  · refine ⟨P, hP, h1, ?_⟩
    by_contra hm
    have hle : Q ≤ P := by
      rw [← hσ]
      intro b hb
      by_contra hb'
      exact hm ⟨σ⁻¹ • b, Ideal.mem_pointwise_smul_iff_inv_smul_mem.1 hb, b,
        (congrArg (fun x : 𝓞 E => (x : E)) (smul_inv_smul σ b)).symm, hb'⟩
    have hQ0 : Q ≠ ⊥ := by
      rintro rfl
      exact v.ne_bot (by rw [← h1']; exact Ideal.comap_bot_of_injective _ (FaithfulSMul.algebraMap_injective _ _))
    exact hne ((hQ.isMaximal hQ0).eq_of_le hP.ne_top hle).symm

end GlobalTheory.UnRepCheck

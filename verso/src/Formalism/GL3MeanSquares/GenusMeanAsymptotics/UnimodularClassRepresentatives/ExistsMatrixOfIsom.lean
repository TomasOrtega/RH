import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.EquivFunEquivOfMatrixSymm
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.ExistsUnitaryNear
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.FiniteRepSetOfOrtho

open NumberField Module Matrix

noncomputable section

namespace Formalism.HermitianLattices.Ext.L3.HU

open LocalSpans idealPowerSpanBounds localizedQuotients integralBasisSpans

variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
variable {V : Type} [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
variable {κ : Type} [Fintype κ] [DecidableEq κ]

local notation "ι" => algebraMap (𝓞 F) (𝓞 K)
local notation "jK" => algebraMap (𝓞 K) K

def IsE (h : V →ₗ⋆[K] V →ₗ[K] K) (A : Submodule (𝓞 K) V) (𝔭 : Ideal (𝓞 F)) (e : ℕ) : Prop :=
  ∀ x : V, (∀ y ∈ A, h y x ∈ locF 𝔭 (1 : Submodule (𝓞 K) K)) →
    ∀ t ∈ 𝔭 ^ e, algebraMap (𝓞 F) (𝓞 K) t • x ∈ A

/- English proof (translation)
Introduce `h0`. Take `⟨v, hv, hv0⟩` from `Matrix.exists_mulVec_eq_zero_iff.2 h0`. Apply `hv` to reduce the goal to its premises. Establish `h1` using `form_repr h b (b.equivFun.symm v) (b.equivFun.symm v)`. Rewrite `h1` using `[LinearEquiv.apply_symm_apply, hv0, dotProduct_zero]`.

Establish `h2` using `hd _ h1`. Rewrite using `[← b.equivFun.apply_symm_apply v, h2, map_zero]`.
-/
theorem gramK_det_ne_zero {h : V →ₗ⋆[K] V →ₗ[K] K} (hd : ∀ x, h x x = 0 → x = 0) (b : Basis κ K V) :
    (gramK h b).det ≠ 0 := by
  intro h0
  obtain ⟨v, hv, hv0⟩ := Matrix.exists_mulVec_eq_zero_iff.2 h0
  apply hv
  have h1 := form_repr h b (b.equivFun.symm v) (b.equivFun.symm v)
  rw [LinearEquiv.apply_symm_apply, hv0, dotProduct_zero] at h1
  have h2 := hd _ h1
  rw [← b.equivFun.apply_symm_apply v, h2, map_zero]

/- English proof (translation)
Establish `hdet : IsUnit (gramK h b).det` using `isUnit_iff_ne_zero.2 (gramK_det_ne_zero hd b)`. Use `⟨jK (ι π₀) ^ e • (gramK h b)⁻¹, ?_, by rw [Matrix.mul_smul, Matrix.mul_nonsing_inv _ hdet]⟩` and prove the remaining obligations. Introduce `i j`. Establish `h1 : ∀ y ∈ locF 𝔭 (spanO b), h y (b.equivFun.symm fun i => (gramK h b)⁻¹ i j) ∈ locF 𝔭 (1 : Submodule (𝓞 K) K)`. Introduce `y hy`.

Rewrite using `[form_repr h b, LinearEquiv.apply_symm_apply]`. Establish `h2 : (gramK h b *ᵥ fun i => (gramK h b)⁻¹ i j) = Pi.single j 1`. Use function extensionality and compare the values at `l`. Establish `: (gramK h b *ᵥ fun i => (gramK h b)⁻¹ i j) l = (gramK h b * (gramK h b)⁻¹) l j` using `rfl`. Rewrite using `[this, Matrix.mul_nonsing_inv _ hdet, Matrix.one_apply, Pi.single_apply]`.

Rewrite using `[h2, dotProduct_single_one, ← mem_SP_iff_locF]`. Conclude with `InP.conj hF ((mem_locF_iff_repr b y).1 hy j)`. Establish `h3` using `(mem_locF_iff_repr b _).1 (he _ h1 (π₀ ^ e) (Ideal.pow_mem_pow hπ e)) i`. Rewrite `h3` using `[← algebraMap_smul K, map_smul, LinearEquiv.apply_symm_apply, Pi.smul_apply, smul_eq_mul, map_pow, map_pow]`. Conclude with `h3`.
-/
theorem exists_E (hF : IsFixF K F) {h : V →ₗ⋆[K] V →ₗ[K] K} (hd : ∀ x, h x x = 0 → x = 0) (b : Basis κ K V)
    {𝔭 : Ideal (𝓞 F)} [𝔭.IsPrime] {e : ℕ} (he : IsE h (locF 𝔭 (spanO b)) 𝔭 e) {π₀ : 𝓞 F} (hπ : π₀ ∈ 𝔭) :
    ∃ E : Matrix κ κ K, Ent (SP K 𝔭) E ∧ gramK h b * E = jK (ι π₀) ^ e • (1 : Matrix κ κ K) := by
  have hdet : IsUnit (gramK h b).det := isUnit_iff_ne_zero.2 (gramK_det_ne_zero hd b)
  refine ⟨jK (ι π₀) ^ e • (gramK h b)⁻¹, ?_, by rw [Matrix.mul_smul, Matrix.mul_nonsing_inv _ hdet]⟩
  intro i j
  have h1 : ∀ y ∈ locF 𝔭 (spanO b), h y (b.equivFun.symm fun i => (gramK h b)⁻¹ i j) ∈
      locF 𝔭 (1 : Submodule (𝓞 K) K) := by
    intro y hy
    rw [form_repr h b, LinearEquiv.apply_symm_apply]
    have h2 : (gramK h b *ᵥ fun i => (gramK h b)⁻¹ i j) = Pi.single j 1 := by
      funext l
      have : (gramK h b *ᵥ fun i => (gramK h b)⁻¹ i j) l = (gramK h b * (gramK h b)⁻¹) l j := rfl
      rw [this, Matrix.mul_nonsing_inv _ hdet, Matrix.one_apply, Pi.single_apply]
    rw [h2, dotProduct_single_one, ← mem_SP_iff_locF]
    exact InP.conj hF ((mem_locF_iff_repr b y).1 hy j)
  have h3 := (mem_locF_iff_repr b _).1 (he _ h1 (π₀ ^ e) (Ideal.pow_mem_pow hπ e)) i
  rw [← algebraMap_smul K, map_smul, LinearEquiv.apply_symm_apply, Pi.smul_apply, smul_eq_mul, map_pow,
    map_pow] at h3
  exact h3

/- English proof (translation)
Use extensionality with `i j`. Conclude with `(hH i j).symm`.
-/
theorem gramK_eq_map {h : V →ₗ⋆[K] V →ₗ[K] K} {b : Basis κ K V} {H : Matrix κ κ (𝓞 K)}
    (hH : ∀ i j, jK (H i j) = h (b i) (b j)) : gramK h b = H.map jK := by
  ext i j
  exact (hH i j).symm

/- English proof (translation)
Rewrite using `[Matrix.map_mul, Matrix.map_mul, conjTranspose_map jK (fun _ => rfl)]`.
-/
theorem map_form (H Y : Matrix κ κ (𝓞 K)) :
    (Y.map jK)ᴴ * H.map jK * Y.map jK = (Yᴴ * H * Y).map jK := by
  rw [Matrix.map_mul, Matrix.map_mul, conjTranspose_map jK (fun _ => rfl)]

/- English proof (translation)
Use `choose Z hZ hZ' using fun i j => (mem_noncompactPart_iff hu k _).1 (inP_jK (hY i j))`. Use `⟨Matrix.of Z, hZ, ?_⟩` and prove the remaining obligations. Rewrite using `[map_form]`. Use extensionality with `i j`. Use `hZ' i j` as an intermediate fact.

Rewrite `this` using `[Matrix.sub_apply, map_sub]`. Rewrite using `[Matrix.add_apply, Matrix.smul_apply, Matrix.map_apply, Matrix.map_apply, Matrix.of_apply, smul_eq_mul, ← this]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem exists_Z {𝔭 : Ideal (𝓞 F)} [𝔭.IsPrime] {π₀ s₀ : 𝓞 F} (hu : IsUnif0 𝔭 π₀ s₀)
    {H Y : Matrix κ κ (𝓞 K)} {k : ℕ} (hY : ∀ i j, (Yᴴ * H * Y - H) i j ∈ extP K 𝔭 ^ k) :
    ∃ Z : Matrix κ κ K, Ent (SP K 𝔭) Z ∧
      (Y.map jK)ᴴ * H.map jK * Y.map jK = H.map jK + jK (ι π₀) ^ k • Z := by
  choose Z hZ hZ' using fun i j => (mem_noncompactPart_iff hu k _).1 (inP_jK (hY i j))
  refine ⟨Matrix.of Z, hZ, ?_⟩
  rw [map_form]
  ext i j
  have := hZ' i j
  rw [Matrix.sub_apply, map_sub] at this
  rw [Matrix.add_apply, Matrix.smul_apply, Matrix.map_apply, Matrix.map_apply, Matrix.of_apply, smul_eq_mul,
    ← this]
  ring

/- English proof (translation)
Introduce `_ _` and use `jK_mem_SP _`.
-/
theorem ent_map {𝔭 : Ideal (𝓞 F)} [𝔭.IsPrime] (Y : Matrix κ κ (𝓞 K)) : Ent (SP K 𝔭) (Y.map jK) :=
  fun _ _ => jK_mem_SP _

/- English proof (translation)
Establish `: ∑ l, c l • b l = ∑ l, jK (c l) • b l` using `Finset.sum_congr rfl fun l _ => (algebraMap_smul K _ _).symm`. Rewrite using `[this, ← Basis.equivFun_symm_apply, LinearEquiv.apply_symm_apply]`.
-/
theorem equivFun_sum_smul (b : Basis κ K V) (c : κ → 𝓞 K) :
    b.equivFun (∑ l, c l • b l) = fun l => jK (c l) := by
  have : ∑ l, c l • b l = ∑ l, jK (c l) • b l :=
    Finset.sum_congr rfl fun l _ => (algebraMap_smul K _ _).symm
  rw [this, ← Basis.equivFun_symm_apply, LinearEquiv.apply_symm_apply]

/- English proof (translation)
Use `h𝔭.isPrime` as an intermediate fact. Take `⟨π₀, s₀, hu⟩` from `exists_isUnif0 h𝔭`. Take `⟨E, hE, hHE⟩` from `exists_E hF hd b he hu.mem`. Take `⟨Z, hZ, hXZ⟩` from `exists_Z hu hY`. Establish `hg` using `gramK_eq_map hH`.

Rewrite `hHE` using `[hg]`. Establish `hHh : (H.map jK)ᴴ = H.map jK` using `by rw [← hg]; exact gramK_conjTranspose hs b`. Take `⟨G, G', D, hG, hG', hD, hGG, hU, hGX⟩` from `exists_unitary_near (isLocUnif hK hF h𝔭 hu) hHh (ent_map H) hE hHE hk (ent_map Y) hZ hXZ`. Use `⟨equivOfMatrix b G G' hGG, ⟨equivOfMatrix_mem_isom h b G G' hGG (by rw [hg]; exact hU), gmap_equivOfMatrix b G G' hGG hG hG'⟩, fun i => ?_⟩` and prove the remaining obligations. Rewrite using `[mem_smul_locF_iff_repr]`.

Introduce `l`. Establish `hb1 : b.equivFun (b i) = Pi.single i 1`. Use function extensionality and compare the values at `j`. Rewrite using `[Basis.equivFun_self, Pi.single_apply]`. Simplify using `only [eq_comm]`.

Rewrite using `[map_sub, equivFun_equivOfMatrix, equivFun_sum_smul, hb1, mulVec_single_one, Pi.sub_apply]`. Use `show InP 𝔭 (k - e) (G l i - jK (Y l i))`. Rewrite using `[hGX, mem_noncompactPart_iff hu]`. Use `⟨D l i, hD l i, ?_⟩` and prove the remaining obligations. Simplify using the standard rewrite rules.
-/
theorem exists_isom_matrix (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F) {h : V →ₗ⋆[K] V →ₗ[K] K}
    (hs : h.IsSymm) (hd : ∀ x, h x x = 0 → x = 0) (b : Basis κ K V) {H : Matrix κ κ (𝓞 K)}
    (hH : ∀ i j, jK (H i j) = h (b i) (b j)) {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) {e k : ℕ}
    (he : IsE h (locF 𝔭 (spanO b)) 𝔭 e) (hk : e + 1 ≤ k) (Y : Matrix κ κ (𝓞 K))
    (hY : ∀ i j, (Yᴴ * H * Y - H) i j ∈ extP K 𝔭 ^ k) :
    ∃ g ∈ autSub h (locF 𝔭 (spanO b)), ∀ i, g (b i) - ∑ l, Y l i • b l ∈
      (extP K 𝔭 ^ (k - e) • locF 𝔭 (spanO b) : Submodule (𝓞 K) V) := by
  have := h𝔭.isPrime
  obtain ⟨π₀, s₀, hu⟩ := exists_isUnif0 h𝔭
  obtain ⟨E, hE, hHE⟩ := exists_E hF hd b he hu.mem
  obtain ⟨Z, hZ, hXZ⟩ := exists_Z hu hY
  have hg := gramK_eq_map hH
  rw [hg] at hHE
  have hHh : (H.map jK)ᴴ = H.map jK := by rw [← hg]; exact gramK_conjTranspose hs b
  obtain ⟨G, G', D, hG, hG', hD, hGG, hU, hGX⟩ := exists_unitary_near (isLocUnif hK hF h𝔭 hu) hHh
    (ent_map H) hE hHE hk (ent_map Y) hZ hXZ
  refine ⟨equivOfMatrix b G G' hGG, ⟨equivOfMatrix_mem_isom h b G G' hGG (by rw [hg]; exact hU),
    gmap_equivOfMatrix b G G' hGG hG hG'⟩, fun i => ?_⟩
  rw [mem_smul_locF_iff_repr]
  intro l
  have hb1 : b.equivFun (b i) = Pi.single i 1 := by
    funext j
    rw [Basis.equivFun_self, Pi.single_apply]
    simp only [eq_comm]
  rw [map_sub, equivFun_equivOfMatrix, equivFun_sum_smul, hb1, mulVec_single_one, Pi.sub_apply]
  show InP 𝔭 (k - e) (G l i - jK (Y l i))
  rw [hGX, mem_noncompactPart_iff hu]
  refine ⟨D l i, hD l i, ?_⟩
  simp

/- English proof (translation)
Use `h𝔭.isPrime` as an intermediate fact. Take `⟨π₀, s₀, hu⟩` from `exists_isUnif0 h𝔭`. Take `⟨E, hE, hHE⟩` from `exists_E hF hd b he hu.mem`. Take `⟨Z, hZ, hXZ⟩` from `exists_Z hu hY`. Establish `hg` using `gramK_eq_map hH`.

Rewrite `hHE` using `[hg]`. Establish `hHh : (H.map jK)ᴴ = H.map jK` using `by rw [← hg]; exact gramK_conjTranspose hs b`. Take `⟨h0, h1⟩` from `det_unit (isLocUnif hK hF h𝔭 hu) hHh (ent_map H) hE hHE hk (ent_map Y) hZ hXZ`. Establish `hdet : (Y.map jK).det = jK Y.det`. Use `RingHom.map_det jK Y` as an intermediate fact.

Rewrite `this` using `[RingHom.mapMatrix_apply]`. Conclude with `this.symm`. Rewrite `h0`, `h1` using `[hdet]`. Take `⟨t, ht, z, e1⟩` from `mem_SP.1 h1`. Establish `e2 : z * Y.det = ι t`.

Apply `jK_inj` to reduce the goal to its premises. Rewrite using `[map_mul, e1]`. Clear the denominators using the available nonvanishing facts. Take `⟨u, hu'⟩` from `MeanA.exists_mul_sub_one_mem_pow h𝔭 ht N`. Apply `IsUnit.of_mul_eq_one (Ideal.Quotient.mk _ (ι u * z))` to reduce the goal to its premises.

Rewrite using `[← map_mul, ← map_one (Ideal.Quotient.mk (extP K 𝔭 ^ N)), Ideal.Quotient.eq]`. Establish `: Y.det * (ι u * z) - 1 = ι (u * t - 1)`. Rewrite using `[map_sub, map_mul, map_one, ← e2]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[this]`.

Conclude with `ι_mem_pow hu'`.
-/
theorem isUnit_det_mk (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F) {h : V →ₗ⋆[K] V →ₗ[K] K}
    (hs : h.IsSymm) (hd : ∀ x, h x x = 0 → x = 0) (b : Basis κ K V) {H : Matrix κ κ (𝓞 K)}
    (hH : ∀ i j, jK (H i j) = h (b i) (b j)) {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) {e k : ℕ}
    (he : IsE h (locF 𝔭 (spanO b)) 𝔭 e) (hk : e + 1 ≤ k) (Y : Matrix κ κ (𝓞 K))
    (hY : ∀ i j, (Yᴴ * H * Y - H) i j ∈ extP K 𝔭 ^ k) (N : ℕ) :
    IsUnit (Ideal.Quotient.mk (extP K 𝔭 ^ N) Y.det) := by
  have := h𝔭.isPrime
  obtain ⟨π₀, s₀, hu⟩ := exists_isUnif0 h𝔭
  obtain ⟨E, hE, hHE⟩ := exists_E hF hd b he hu.mem
  obtain ⟨Z, hZ, hXZ⟩ := exists_Z hu hY
  have hg := gramK_eq_map hH
  rw [hg] at hHE
  have hHh : (H.map jK)ᴴ = H.map jK := by rw [← hg]; exact gramK_conjTranspose hs b
  obtain ⟨h0, h1⟩ := det_unit (isLocUnif hK hF h𝔭 hu) hHh (ent_map H) hE hHE hk (ent_map Y) hZ hXZ
  have hdet : (Y.map jK).det = jK Y.det := by
    have := RingHom.map_det jK Y
    rw [RingHom.mapMatrix_apply] at this
    exact this.symm
  rw [hdet] at h0 h1
  obtain ⟨t, ht, z, e1⟩ := mem_SP.1 h1
  have e2 : z * Y.det = ι t := by
    apply jK_inj
    rw [map_mul, e1]
    field_simp
  obtain ⟨u, hu'⟩ := MeanA.exists_mul_sub_one_mem_pow h𝔭 ht N
  apply IsUnit.of_mul_eq_one (Ideal.Quotient.mk _ (ι u * z))
  rw [← map_mul, ← map_one (Ideal.Quotient.mk (extP K 𝔭 ^ N)), Ideal.Quotient.eq]
  have : Y.det * (ι u * z) - 1 = ι (u * t - 1) := by
    rw [map_sub, map_mul, map_one, ← e2]
    ring
  rw [this]
  exact ι_mem_pow hu'

/- English proof (translation)
Use `form_mulVec Y H (Pi.single i 1) (Pi.single j 1)` as an intermediate fact. Rewrite `this` using `[form_single, mulVec_single_one, mulVec_single_one]`. Conclude with `this.symm`.
-/
theorem form_col (H Y : Matrix κ κ (𝓞 K)) (i j : κ) :
    (Yᴴ * H * Y) i j = star (fun l => Y l i) ⬝ᵥ (H *ᵥ fun l => Y l j) := by
  have := form_mulVec Y H (Pi.single i 1) (Pi.single j 1)
  rw [form_single, mulVec_single_one, mulVec_single_one] at this
  exact this.symm

/- English proof (translation)
Use `h𝔭.isPrime` as an intermediate fact. Establish `hgb : ∀ i, g (b i) ∈ locF 𝔭 (spanO b)`. Introduce `i`. Establish `h1 : g (b i) ∈ Formalism.HermitianLatticesTheory.gmap g (locF 𝔭 (spanO b))` using `⟨b i, le_locF 𝔭 _ (Submodule.subset_span ⟨i, rfl⟩), rfl⟩`. Rewrite `h1` using `[hg.2]`. Then use the resulting hypothesis.

Use `choose c hc hcL using fun i => exists_approx h𝔭 (spanO b) N (hgb i)`. Establish `hsum : ∀ i, ∑ l, crd b ⟨_, hcL i⟩ l • b l = ι (c i) • g (b i)`. Introduce `i`. Use `coe_eq_sum b ⟨_, hcL i⟩` as an intermediate fact. Conclude with `(Finset.sum_congr rfl fun l _ => (algebraMap_smul K _ _).symm).trans this.symm`.

Use `⟨Matrix.of fun l i => crd b ⟨_, hcL i⟩ l, fun i j => ?_, fun i => ?_⟩` and prove the remaining obligations. Establish `h1` using `form_eq h b hH ⟨_, hcL i⟩ ⟨_, hcL j⟩`. Establish `h2 : h (ι (c i) • g (b i)) (ι (c j) • g (b j)) = jK (ι (c i * c j) * H i j)`. Rewrite using `[form_smul hF, hg.1, ← hH, ← map_mul]`. Establish `h3 : (ι (c i * c j) * H i j) = ((Matrix.of fun l i => crd b ⟨_, hcL i⟩ l)ᴴ * H * (Matrix.of fun l i => crd b ⟨_, hcL i⟩ l)) i j`.

Rewrite using `[form_col]`. Conclude with `jK_inj (h2.symm.trans h1)`. Rewrite using `[Matrix.sub_apply, ← h3]`. Establish `h4 : ι (c i * c j) * H i j - H i j = ι (c i * c j - 1) * H i j`. Rewrite using `[map_sub, map_one]`.

Expand and normalize the polynomial expressions, which then agree. Rewrite using `[h4]`. Apply `Ideal.mul_mem_right` to reduce the goal to its premises. Apply `ι_mem_pow` to reduce the goal to its premises. Establish `: c i * c j - 1 = (c i - 1) * c j + (c j - 1)` using `by ring`.

Rewrite using `[this]`. Conclude with `add_mem (Ideal.mul_mem_right _ _ (hc i)) (hc j)`. Establish `h1 : ∑ l, (Matrix.of fun l i => crd b ⟨_, hcL i⟩ l) l i • b l = ι (c i) • g (b i)` using `hsum i`. Rewrite using `[h1]`. Establish `h2 : g (b i) - ι (c i) • g (b i) = ι (-(c i - 1)) • g (b i)`.

Rewrite using `[map_neg, map_sub, map_one, neg_smul, sub_smul, one_smul]`. Normalize the expressions using the abelian group laws. Rewrite using `[h2]`. Conclude with `Submodule.smul_mem_smul (ι_mem_pow (neg_mem (hc i))) (hgb i)`.
-/
theorem exists_matrix_of_isom (hF : IsFixF K F) {h : V →ₗ⋆[K] V →ₗ[K] K} (b : Basis κ K V)
    {H : Matrix κ κ (𝓞 K)} (hH : ∀ i j, jK (H i j) = h (b i) (b j)) {𝔭 : Ideal (𝓞 F)}
    (h𝔭 : 𝔭.IsMaximal) {g : V ≃ₗ[K] V} (hg : g ∈ autSub h (locF 𝔭 (spanO b))) (N : ℕ) :
    ∃ Y : Matrix κ κ (𝓞 K), (∀ i j, (Yᴴ * H * Y - H) i j ∈ extP K 𝔭 ^ N) ∧
      ∀ i, g (b i) - ∑ l, Y l i • b l ∈ (extP K 𝔭 ^ N • locF 𝔭 (spanO b) : Submodule (𝓞 K) V) := by
  have := h𝔭.isPrime
  have hgb : ∀ i, g (b i) ∈ locF 𝔭 (spanO b) := by
    intro i
    have h1 : g (b i) ∈ Formalism.HermitianLatticesTheory.gmap g (locF 𝔭 (spanO b)) :=
      ⟨b i, le_locF 𝔭 _ (Submodule.subset_span ⟨i, rfl⟩), rfl⟩
    rwa [hg.2] at h1
  choose c hc hcL using fun i => exists_approx h𝔭 (spanO b) N (hgb i)
  have hsum : ∀ i, ∑ l, crd b ⟨_, hcL i⟩ l • b l = ι (c i) • g (b i) := by
    intro i
    have := coe_eq_sum b ⟨_, hcL i⟩
    exact (Finset.sum_congr rfl fun l _ => (algebraMap_smul K _ _).symm).trans this.symm
  refine ⟨Matrix.of fun l i => crd b ⟨_, hcL i⟩ l, fun i j => ?_, fun i => ?_⟩
  · have h1 := form_eq h b hH ⟨_, hcL i⟩ ⟨_, hcL j⟩
    have h2 : h (ι (c i) • g (b i)) (ι (c j) • g (b j)) = jK (ι (c i * c j) * H i j) := by
      rw [form_smul hF, hg.1, ← hH, ← map_mul]
    have h3 : (ι (c i * c j) * H i j) = ((Matrix.of fun l i => crd b ⟨_, hcL i⟩ l)ᴴ * H *
        (Matrix.of fun l i => crd b ⟨_, hcL i⟩ l)) i j := by
      rw [form_col]
      exact jK_inj (h2.symm.trans h1)
    rw [Matrix.sub_apply, ← h3]
    have h4 : ι (c i * c j) * H i j - H i j = ι (c i * c j - 1) * H i j := by
      rw [map_sub, map_one]; ring
    rw [h4]
    apply Ideal.mul_mem_right
    apply ι_mem_pow
    have : c i * c j - 1 = (c i - 1) * c j + (c j - 1) := by ring
    rw [this]
    exact add_mem (Ideal.mul_mem_right _ _ (hc i)) (hc j)
  · have h1 : ∑ l, (Matrix.of fun l i => crd b ⟨_, hcL i⟩ l) l i • b l = ι (c i) • g (b i) := hsum i
    rw [h1]
    have h2 : g (b i) - ι (c i) • g (b i) = ι (-(c i - 1)) • g (b i) := by
      rw [map_neg, map_sub, map_one, neg_smul, sub_smul, one_smul]; abel
    rw [h2]
    exact Submodule.smul_mem_smul (ι_mem_pow (neg_mem (hc i))) (hgb i)

end Formalism.HermitianLattices.Ext.L3.HU

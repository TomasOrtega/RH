import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.ConjTransposeMapMk
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.CardUnitaryReduction

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
Introduce `x hx t ht` and use `he x hx t (Ideal.pow_le_pow_right hec ht)`.
-/
theorem IsE.mono {h : V →ₗ⋆[K] V →ₗ[K] K} {A : Submodule (𝓞 K) V} {𝔭 : Ideal (𝓞 F)} {e c : ℕ}
    (he : IsE h A 𝔭 e) (hec : e ≤ c) : IsE h A 𝔭 c :=
  fun x hx t ht => he x hx t (Ideal.pow_le_pow_right hec ht)

/- English proof (translation)
Rewrite using `[localizedQuotients.akCount_locF hFF.out h _ 𝔭 h𝔭, akCount_free h b hH h𝔭]`.
-/
theorem akCount_basis [hFF : Fact (IsFixF K F)] (h : V →ₗ⋆[K] V →ₗ[K] K) (b : Basis κ K V)
    {H : Matrix κ κ (𝓞 K)} (hH : ∀ i j, jK (H i j) = h (b i) (b j)) {𝔭 : Ideal (𝓞 F)}
    (h𝔭 : 𝔭.IsMaximal) (k : ℕ) :
    akCount h (locF 𝔭 (spanO b)) 𝔭 k = Nat.card {X : Matrix κ κ (𝓞 K ⧸ extP K 𝔭 ^ k) //
      Xᴴ * Hq H 𝔭 k * X = Hq H 𝔭 k} := by
  rw [localizedQuotients.akCount_locF hFF.out h _ 𝔭 h𝔭, akCount_free h b hH h𝔭]

/- English proof (translation)
Use extensionality with `i l`. Both sides reduce to the same expression.
-/
theorem map_factor_map_mk (𝔭 : Ideal (𝓞 F)) {j k : ℕ} (hjk : j ≤ k) (Y : Matrix κ κ (𝓞 K)) :
    (Y.map (Ideal.Quotient.mk (extP K 𝔭 ^ k))).map
      (Ideal.Quotient.factor (Ideal.pow_le_pow_right hjk)) = Y.map (Ideal.Quotient.mk (extP K 𝔭 ^ j)) := by
  ext i l
  rfl

/- English proof (translation)
Use `h𝔭.isPrime` as an intermediate fact. Establish `hF : IsFixF K F` using `hFF.out`. Unfold `redCount`. Use `Nat.card_congr ((eL h𝔭 b j).subtypeEquiv fun X => ?_)` and prove the remaining obligations. Prove the components needed by the constructor for the conclusion.

Introduce and unpack `⟨g, hg, hgX⟩`. Take `⟨Y, hY1, hY2⟩` from `exists_matrix_of_isom hF b hH h𝔭 hg (j + c)`. Use `⟨Y.map (Ideal.Quotient.mk _), (mk_form_iff 𝔭 _ H Y).2 hY1, ?_⟩` and prove the remaining obligations. Rewrite using `[map_factor_map_mk 𝔭 (Nat.le_add_right j c), eq_comm, eL_eq_iff]`. Introduce `i`.

Take `⟨y, hy1, hy2⟩` from `hgX (inA 𝔭 b (cmb b (Pi.single i 1)))`. Rewrite using `[hy2, mk_eq_iff, hy1, coe_inA, coe_cmb_single, coe_inA, coe_cmb]`. Conclude with `smul_mono_pow (Nat.le_add_right j c) (hY2 i)`. Introduce and unpack `⟨X', hX', hmap⟩`. Take `⟨Y, rfl⟩` from `exists_map_mk 𝔭 _ X'`.

Rewrite `hmap` using `[map_factor_map_mk 𝔭 (Nat.le_add_right j c), eq_comm, eL_eq_iff]`. Take `⟨g, hg, hgY⟩` from `exists_isom_matrix hK hF hs hd b hH h𝔭 he (by omega : c + 1 ≤ j + c) Y ((mk_form_iff 𝔭 _ H Y).1 hX')`. Rewrite `hgY` using `[Nat.add_sub_cancel]`. Use `⟨g, hg, fun x => ⟨⟨g x, aut_mem hg x.2⟩, rfl, ?_⟩⟩` and prove the remaining obligations. Take `⟨c₀, hc⟩` from `exists_cmb h𝔭 b j (Submodule.Quotient.mk x)`.

Rewrite using `[hc, end_apply_cmb b j X Y hmap c₀, mk_eq_iff]`. Rewrite `hc` using `[mk_eq_iff]`. Establish `e1 : (inA 𝔭 b (cmb b (Y *ᵥ c₀)) : V) - g (x : V) = -(g ((x : V) - (inA 𝔭 b (cmb b c₀) : V)) + (g (cmb b c₀ : V) - (cmb b (Y *ᵥ c₀) : V)))`. Rewrite using `[map_sub, coe_inA, coe_inA]`. Normalize the expressions using the abelian group laws.

Use `show (inA 𝔭 b (cmb b (Y *ᵥ c₀)) : V) - g (x : V) ∈ _`. Rewrite using `[e1]`. Conclude with `neg_mem (add_mem (aut_mem_smul hg _ hc) (aut_cmb b hgY c₀))`.
-/
theorem redCount_basis [hFF : Fact (IsFixF K F)] (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) {h : V →ₗ⋆[K] V →ₗ[K] K}
    (hs : h.IsSymm) (hd : ∀ x, h x x = 0 → x = 0) (b : Basis κ K V) {H : Matrix κ κ (𝓞 K)}
    (hH : ∀ i j, jK (H i j) = h (b i) (b j)) {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) {c j : ℕ}
    (he : IsE h (locF 𝔭 (spanO b)) 𝔭 c) (hj : 1 ≤ j) :
    redCount h (locF 𝔭 (spanO b)) 𝔭 j = Nat.card {X' : Matrix κ κ (𝓞 K ⧸ extP K 𝔭 ^ j) //
      ∃ X : Matrix κ κ (𝓞 K ⧸ extP K 𝔭 ^ (j + c)), Xᴴ * Hq H 𝔭 (j + c) * X = Hq H 𝔭 (j + c) ∧
        X.map (Ideal.Quotient.factor (Ideal.pow_le_pow_right (Nat.le_add_right j c))) = X'} := by
  have := h𝔭.isPrime
  have hF : IsFixF K F := hFF.out
  unfold redCount
  refine Nat.card_congr ((eL h𝔭 b j).subtypeEquiv fun X => ?_)
  constructor
  · rintro ⟨g, hg, hgX⟩
    obtain ⟨Y, hY1, hY2⟩ := exists_matrix_of_isom hF b hH h𝔭 hg (j + c)
    refine ⟨Y.map (Ideal.Quotient.mk _), (mk_form_iff 𝔭 _ H Y).2 hY1, ?_⟩
    rw [map_factor_map_mk 𝔭 (Nat.le_add_right j c), eq_comm, eL_eq_iff]
    intro i
    obtain ⟨y, hy1, hy2⟩ := hgX (inA 𝔭 b (cmb b (Pi.single i 1)))
    rw [hy2, mk_eq_iff, hy1, coe_inA, coe_cmb_single, coe_inA, coe_cmb]
    exact smul_mono_pow (Nat.le_add_right j c) (hY2 i)
  · rintro ⟨X', hX', hmap⟩
    obtain ⟨Y, rfl⟩ := exists_map_mk 𝔭 _ X'
    rw [map_factor_map_mk 𝔭 (Nat.le_add_right j c), eq_comm, eL_eq_iff] at hmap
    obtain ⟨g, hg, hgY⟩ := exists_isom_matrix hK hF hs hd b hH h𝔭 he (by omega : c + 1 ≤ j + c) Y
      ((mk_form_iff 𝔭 _ H Y).1 hX')
    rw [Nat.add_sub_cancel] at hgY
    refine ⟨g, hg, fun x => ⟨⟨g x, aut_mem hg x.2⟩, rfl, ?_⟩⟩
    obtain ⟨c₀, hc⟩ := exists_cmb h𝔭 b j (Submodule.Quotient.mk x)
    rw [hc, end_apply_cmb b j X Y hmap c₀, mk_eq_iff]
    rw [mk_eq_iff] at hc
    have e1 : (inA 𝔭 b (cmb b (Y *ᵥ c₀)) : V) - g (x : V) =
        -(g ((x : V) - (inA 𝔭 b (cmb b c₀) : V)) + (g (cmb b c₀ : V) - (cmb b (Y *ᵥ c₀) : V))) := by
      rw [map_sub, coe_inA, coe_inA]
      abel
    show (inA 𝔭 b (cmb b (Y *ᵥ c₀)) : V) - g (x : V) ∈ _
    rw [e1]
    exact neg_mem (add_mem (aut_mem_smul hg _ hc) (aut_cmb b hgY c₀))

/- English proof (translation)
Take `⟨Y, rfl⟩` from `exists_map_mk 𝔭 _ X`. Establish `h1` using `isUnit_det_mk hK hFF.out hs hd b hH h𝔭 he hk Y ((mk_form_iff 𝔭 _ H Y).1 hX) k`. Establish `h2` using `RingHom.map_det (Ideal.Quotient.mk (extP K 𝔭 ^ k)) Y`. Rewrite `h2` using `[RingHom.mapMatrix_apply]`. Rewrite `h1` using `[h2]`. Then use the resulting hypothesis.
-/
theorem isUnit_det_of_form [hFF : Fact (IsFixF K F)] (hK : Formalism.HermitianLatticesTheory.IsCMUnram K)
    {h : V →ₗ⋆[K] V →ₗ[K] K} (hs : h.IsSymm) (hd : ∀ x, h x x = 0 → x = 0) (b : Basis κ K V)
    {H : Matrix κ κ (𝓞 K)} (hH : ∀ i j, jK (H i j) = h (b i) (b j)) {𝔭 : Ideal (𝓞 F)}
    (h𝔭 : 𝔭.IsMaximal) {e k : ℕ} (he : IsE h (locF 𝔭 (spanO b)) 𝔭 e) (hk : e + 1 ≤ k)
    (X : Matrix κ κ (𝓞 K ⧸ extP K 𝔭 ^ k)) (hX : Xᴴ * Hq H 𝔭 k * X = Hq H 𝔭 k) : IsUnit X.det := by
  obtain ⟨Y, rfl⟩ := exists_map_mk 𝔭 _ X
  have h1 := isUnit_det_mk hK hFF.out hs hd b hH h𝔭 he hk Y ((mk_form_iff 𝔭 _ H Y).1 hX) k
  have h2 := RingHom.map_det (Ideal.Quotient.mk (extP K 𝔭 ^ k)) Y
  rw [RingHom.mapMatrix_apply] at h2
  rwa [h2] at h1

/- English proof (translation)
Use `Matrix.ext fun i j => ?_` and prove the remaining obligations. Apply `jK_inj` to reduce the goal to its premises. Establish `: jK (Hᴴ i j) = star (jK (H j i))` using `rfl`. Rewrite using `[this, hH, hH]`. Conclude with `hs.eq (b j) (b i)`.
-/
theorem conjTranspose_eq_of_symm {h : V →ₗ⋆[K] V →ₗ[K] K} (hs : h.IsSymm) (b : Basis κ K V)
    {H : Matrix κ κ (𝓞 K)} (hH : ∀ i j, jK (H i j) = h (b i) (b j)) : Hᴴ = H := by
  refine Matrix.ext fun i j => ?_
  apply jK_inj
  have : jK (Hᴴ i j) = star (jK (H j i)) := rfl
  rw [this, hH, hH]
  exact hs.eq (b j) (b i)

/- English proof (translation)
Rewrite using `[akCount_basis h b hH h𝔭, redCount_basis hK hs hd b hH h𝔭 he hj, sigmaCount_basis h b hH h𝔭]`. Conclude with `card_cell h𝔭 (conjTranspose_eq_of_symm hs b hH) hcj (isUnit_det_of_form hK hs hd b hH h𝔭 he (by omega))`.
-/
theorem akCount_eq_mul_basis [hFF : Fact (IsFixF K F)] (hK : Formalism.HermitianLatticesTheory.IsCMUnram K)
    {h : V →ₗ⋆[K] V →ₗ[K] K} (hs : h.IsSymm) (hd : ∀ x, h x x = 0 → x = 0) (b : Basis κ K V)
    {H : Matrix κ κ (𝓞 K)} (hH : ∀ i j, jK (H i j) = h (b i) (b j)) {𝔭 : Ideal (𝓞 F)}
    (h𝔭 : 𝔭.IsMaximal) {c j : ℕ} (he : IsE h (locF 𝔭 (spanO b)) 𝔭 c) (hcj : c ≤ j) (hj : 1 ≤ j) :
    akCount h (locF 𝔭 (spanO b)) 𝔭 (j + c) =
      redCount h (locF 𝔭 (spanO b)) 𝔭 j * sigmaCount h (locF 𝔭 (spanO b)) 𝔭 c := by
  rw [akCount_basis h b hH h𝔭, redCount_basis hK hs hd b hH h𝔭 he hj, sigmaCount_basis h b hH h𝔭]
  exact card_cell h𝔭 (conjTranspose_eq_of_symm hs b hH) hcj
    (isUnit_det_of_form hK hs hd b hH h𝔭 he (by omega))

/- English proof (translation)
Proceed by induction on `e with`. Consider the case `zero`. Rewrite using `[pow_zero, zero_add, pow_one]`. Conclude with `fun h => h𝔭.ne_top ((Ideal.eq_top_iff_one _).2 h)`. Consider the case `succ e ih`.

Use `mul_notMem h𝔭.isPrime (ne_bot h𝔭) ih hπ` as an intermediate fact. Rewrite `this` using `[← pow_succ]`. Then use the resulting hypothesis.
-/
theorem pow_notMem {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) {π₀ : 𝓞 F} (hπ : π₀ ∉ 𝔭 ^ 2) (e : ℕ) :
    π₀ ^ e ∉ 𝔭 ^ (e + 1) := by
  induction e with
  | zero =>
    rw [pow_zero, zero_add, pow_one]
    exact fun h => h𝔭.ne_top ((Ideal.eq_top_iff_one _).2 h)
  | succ e ih =>
    have := mul_notMem h𝔭.isPrime (ne_bot h𝔭) ih hπ
    rwa [← pow_succ] at this

/- English proof (translation)
Use `choose t ht z hz using fun a => mem_SP.1 (hf a)`. Use `⟨∏ a, t a, ?_, fun a => ⟨ι (∏ a' ∈ Finset.univ.erase a, t a') * z a, ?_⟩⟩` and prove the remaining obligations. Introduce `hmem`. Take `⟨a, -, ha⟩` from `(Ideal.IsPrime.prod_mem_iff).1 hmem`. Conclude with `ht a ha`.

Rewrite using `[← Finset.mul_prod_erase _ _ (Finset.mem_univ a), map_mul, hz, map_mul ι, map_mul jK]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem exists_common_den {𝔭 : Ideal (𝓞 F)} [hp : 𝔭.IsPrime] {α : Type*} [Fintype α] (f : α → K)
    (hf : ∀ a, f a ∈ SP K 𝔭) : ∃ t : 𝓞 F, t ∉ 𝔭 ∧ ∀ a, ∃ z : 𝓞 K, jK z = jK (ι t) * f a := by
  classical
  choose t ht z hz using fun a => mem_SP.1 (hf a)
  refine ⟨∏ a, t a, ?_, fun a => ⟨ι (∏ a' ∈ Finset.univ.erase a, t a') * z a, ?_⟩⟩
  · intro hmem
    obtain ⟨a, -, ha⟩ := (Ideal.IsPrime.prod_mem_iff).1 hmem
    exact ht a ha
  · rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ a), map_mul, hz, map_mul ι, map_mul jK]
    ring

/- English proof (translation)
Use `h𝔭.isPrime` as an intermediate fact. Take `⟨π₀, s₀, hu⟩` from `exists_isUnif0 h𝔭`. Take `⟨E, hE, hHE⟩` from `exists_E hF hd b he hu.mem`. Take `⟨t, ht, hz⟩` from `exists_common_den (fun p : κ × κ => E p.1 p.2) (fun p => hE p.1 p.2)`. Use `choose z hz using hz`.

Use `⟨Matrix.of fun i j => z (i, j), t * π₀ ^ e, ?_, ?_⟩` and prove the remaining obligations. Use `mul_notMem h𝔭.isPrime (ne_bot h𝔭) (i := 0) (by rwa [zero_add, pow_one]) (pow_notMem h𝔭 hu.notMem e)` as an intermediate fact. Rewrite `this` using `[zero_add]`. Then use the resulting hypothesis. Establish `h1 : (Matrix.of fun i j => z (i, j)).map jK = jK (ι t) • E`. Use extensionality with `i j`.

Conclude with `hz (i, j)`. Establish `h2 : (H * Matrix.of fun i j => z (i, j)).map jK = (ι (t * π₀ ^ e) • (1 : Matrix κ κ (𝓞 K))).map jK`. Rewrite using `[Matrix.map_mul, h1, ← gramK_eq_map hH, Matrix.mul_smul, hHE, smul_smul]`. Use extensionality with `i j`. Distinguish the cases in `hij : i = j`.

Substitute `hij` using the available equality. Simplify using the standard rewrite rules. Simplify using `[hij]`. Conclude with `Matrix.ext fun i j => jK_inj (congrFun (congrFun h2 i) j)`.
-/
theorem exists_E₀ (hF : IsFixF K F) {h : V →ₗ⋆[K] V →ₗ[K] K} (hd : ∀ x, h x x = 0 → x = 0)
    (b : Basis κ K V) {H : Matrix κ κ (𝓞 K)} (hH : ∀ i j, jK (H i j) = h (b i) (b j))
    {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) {e : ℕ} (he : IsE h (locF 𝔭 (spanO b)) 𝔭 e) :
    ∃ (E₀ : Matrix κ κ (𝓞 K)) (d : 𝓞 F), d ∉ 𝔭 ^ (e + 1) ∧ H * E₀ = ι d • (1 : Matrix κ κ (𝓞 K)) := by
  have := h𝔭.isPrime
  obtain ⟨π₀, s₀, hu⟩ := exists_isUnif0 h𝔭
  obtain ⟨E, hE, hHE⟩ := exists_E hF hd b he hu.mem
  obtain ⟨t, ht, hz⟩ := exists_common_den (fun p : κ × κ => E p.1 p.2) (fun p => hE p.1 p.2)
  choose z hz using hz
  refine ⟨Matrix.of fun i j => z (i, j), t * π₀ ^ e, ?_, ?_⟩
  · have := mul_notMem h𝔭.isPrime (ne_bot h𝔭) (i := 0) (by rwa [zero_add, pow_one]) (pow_notMem h𝔭 hu.notMem e)
    rwa [zero_add] at this
  · have h1 : (Matrix.of fun i j => z (i, j)).map jK = jK (ι t) • E := by
      ext i j
      exact hz (i, j)
    have h2 : (H * Matrix.of fun i j => z (i, j)).map jK = (ι (t * π₀ ^ e) • (1 : Matrix κ κ (𝓞 K))).map jK := by
      rw [Matrix.map_mul, h1, ← gramK_eq_map hH, Matrix.mul_smul, hHE, smul_smul]
      ext i j
      by_cases hij : i = j
      · subst hij
        simp
      · simp [hij]
    exact Matrix.ext fun i j => jK_inj (congrFun (congrFun h2 i) j)

/- English proof (translation)
Take `⟨E₀, d, hd1, hHE⟩` from `exists_E₀ hFF.out hd b hH h𝔭 he`. Rewrite using `[sigmaCount_basis h b hH h𝔭, sigmaCount_basis h b hH h𝔭]`. Conclude with `card_sigma_succ hK h𝔭 (conjTranspose_eq_of_symm hs b hH) hd1 hHE hj`.
-/
theorem sigmaCount_succ_basis [hFF : Fact (IsFixF K F)] (hK : Formalism.HermitianLatticesTheory.IsCMUnram K)
    {h : V →ₗ⋆[K] V →ₗ[K] K} (hs : h.IsSymm) (hd : ∀ x, h x x = 0 → x = 0) (b : Basis κ K V)
    {H : Matrix κ κ (𝓞 K)} (hH : ∀ i j, jK (H i j) = h (b i) (b j)) {𝔭 : Ideal (𝓞 F)}
    (h𝔭 : 𝔭.IsMaximal) {e j : ℕ} (he : IsE h (locF 𝔭 (spanO b)) 𝔭 e) (hj : e ≤ j) :
    sigmaCount h (locF 𝔭 (spanO b)) 𝔭 (j + 1) =
      Ideal.absNorm 𝔭 ^ (Fintype.card κ ^ 2) * sigmaCount h (locF 𝔭 (spanO b)) 𝔭 j := by
  obtain ⟨E₀, d, hd1, hHE⟩ := exists_E₀ hFF.out hd b hH h𝔭 he
  rw [sigmaCount_basis h b hH h𝔭, sigmaCount_basis h b hH h𝔭]
  exact card_sigma_succ hK h𝔭 (conjTranspose_eq_of_symm hs b hH) hd1 hHE hj

end Formalism.HermitianLattices.Ext.L3.HU

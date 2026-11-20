import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.Rationality.QuotSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.Rationality.QuotShiftPfH

namespace ReciprocityTheory.ChartRestriction.G.FreeQuotientRank

open IsDedekindDomain QuotShiftPfH

/- English proof (translation)
Unfold `ordAt`. Rewrite using `[map_mul, WithZero.log_mul ((v.valuation F).ne_zero_iff.mpr hx) ((v.valuation F).ne_zero_iff.mpr hy)]`. Expand and normalize the polynomial expressions, which then agree.
-/
private theorem ordAt_mul_rationality {R F : Type} [CommRing R] [IsDedekindDomain R] [Field F]
    [Algebra R F] [IsFractionRing R F] (v : HeightOneSpectrum R) {x y : F} (hx : x ≠ 0)
    (hy : y ≠ 0) : ordAt v (x * y) = ordAt v x + ordAt v y := by
  unfold ordAt
  rw [map_mul, WithZero.log_mul ((v.valuation F).ne_zero_iff.mpr hx)
    ((v.valuation F).ne_zero_iff.mpr hy)]
  ring

/- English proof (translation)
Unfold `ordAt`. Rewrite using `[map_zpow₀, WithZero.log_zpow, smul_eq_mul]`. Expand and normalize the polynomial expressions, which then agree.
-/
private theorem ordAt_zpow {R F : Type} [CommRing R] [IsDedekindDomain R] [Field F]
    [Algebra R F] [IsFractionRing R F] (v : HeightOneSpectrum R) (x : F) (k : ℤ) :
    ordAt v (x ^ k) = k * ordAt v x := by
  unfold ordAt
  rw [map_zpow₀, WithZero.log_zpow, smul_eq_mul]
  ring

/- English proof (translation)
Proceed by induction on `S using Finset.induction_on with`. Consider the case `empty`. Simplify using `only [Finset.prod_empty, Finset.sum_empty]`. Unfold `ordAt`. Rewrite using `[map_one]`.

Both sides reduce to the same expression. Consider the case `insert a S ha ih`. Rewrite using `[Finset.prod_insert ha, Finset.sum_insert ha, ordAt_mul_rationality v (hf a) (Finset.prod_ne_zero_iff.mpr fun i _ => hf i), ih]`.
-/
private theorem ordAt_prod_rationality {R F : Type} [CommRing R] [IsDedekindDomain R] [Field F]
    [Algebra R F] [IsFractionRing R F] (v : HeightOneSpectrum R) {ι : Type} (S : Finset ι)
    (f : ι → F) (hf : ∀ i, f i ≠ 0) : ordAt v (∏ i ∈ S, f i) = ∑ i ∈ S, ordAt v (f i) := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    simp only [Finset.prod_empty, Finset.sum_empty]
    unfold ordAt
    rw [map_one]
    rfl
  | insert a S ha ih =>
    rw [Finset.prod_insert ha, Finset.sum_insert ha,
      ordAt_mul_rationality v (hf a) (Finset.prod_ne_zero_iff.mpr fun i _ => hf i), ih]

/- English proof (translation)
Take `⟨ϖ, hϖ⟩` from `IsDiscreteValuationRing.exists_irreducible (Rv F v)`. Use `set π : F := (ϖ : F) with hπdef`. Establish `hπ0 : π ≠ 0` using `fun h => hϖ.ne_zero (Subtype.ext h)`. Establish `hπ1 : ordAt v π = 1`. Establish `h1` using `(addVal_eq_ord v ϖ hπ0).symm.trans (IsDiscreteValuationRing.addVal_uniformizer hϖ)`.

Establish `h2 : (ordAt v π).toNat = 1` using `by exact_mod_cast h1`. Establish `h3` using `ord_nonneg v ϖ hπ0`. Use linear arithmetic over natural numbers and integers. Establish `hne : ∀ i, ∃ q, c i q ≠ 0`. Introduce `i`.

Assume the negation of the conclusion as `h`. Use `push_neg at h`. Conclude with `hdet (Matrix.det_eq_zero_of_row_eq_zero i fun j => by simp [h])`. Establish `hex : ∀ i, ∃ μ : ℤ, (∃ q, c i q ≠ 0 ∧ ordAt v (c i q) = μ) ∧ ∀ q, c i q ≠ 0 → μ ≤ ordAt v (c i q)`. Introduce `i`.

Take `⟨lb, ⟨q, hq, rfl⟩, hlb⟩` from `Int.exists_least_of_bdd (P := fun z => ∃ q, c i q ≠ 0 ∧ ordAt v (c i q) = z) ⟨⌈-β - s i⌉, by`. Introduce and unpack `z ⟨q, hq, rfl⟩`. Use `Int.ceil_le.mpr ?_` and prove the remaining obligations. Use `hc i q hq` as an intermediate fact. Use the proof step `linarith⟩`.

Use the proof step `(by obtain ⟨q, hq⟩ := hne i; exact ⟨_, q, hq, rfl⟩)`. Conclude with `⟨_, ⟨q, hq, rfl⟩, fun q' hq' => hlb _ ⟨q', hq', rfl⟩⟩`. Use `choose μ hμ1 hμ2 using hex`. Establish `hμβ : ∀ i, -(μ i : ℝ) ≤ β + s i`. Introduce `i`.

Take `⟨q, hq, hqμ⟩` from `hμ1 i`. Use `hc i q hq` as an intermediate fact. Rewrite `this` using `[hqμ]`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hmem : ∀ i q, π ^ (-μ i) * c i q ∈ Rv F v`.

Introduce `i q`. Distinguish the cases in `hq : c i q = 0`. Rewrite using `[hq, mul_zero]`. Conclude with `(Rv F v).zero_mem`. Use `(mem_Rv_iff_ord v (mul_ne_zero (zpow_ne_zero _ hπ0) hq)).mpr ?_` and prove the remaining obligations.

Rewrite using `[ordAt_mul_rationality v (zpow_ne_zero _ hπ0) hq, ordAt_zpow, hπ1]`. Use `hμ2 i q hq` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion. Set `c' : Fin ρ → (Q →ₗ[Rv F v] Rv F v)` to `fun i => { toFun := fun q => ⟨π ^ (-μ i) * c i q, hmem i q⟩ map_add' := fun a b => by ext; simp [mul_add] map_smul' := fun r q => by`. Use `ext`.

Simplify using `only [LinearMap.map_smul, RingHom.id_apply, Subring.coe_mul, Subring.smul_def, smul_eq_mul]`. Use `ring }`. Establish `hmap : ((Matrix.of fun i j => c' i (th j)).map (Rv F v).subtype) = Matrix.diagonal (fun i => π ^ (-μ i)) * Matrix.of fun i j => c i (th j)`. Use extensionality with `i j`. Simplify using `[Matrix.diagonal_mul, c']`.

Establish `hdetF : (((Matrix.of fun i j => c' i (th j)).det : Rv F v) : F) = (∏ i, π ^ (-μ i)) * (Matrix.of fun i j => c i (th j)).det`. Use `RingHom.map_det (Rv F v).subtype (Matrix.of fun i j => c' i (th j))` as an intermediate fact. Simplify using `only [RingHom.mapMatrix_apply] at this`. Rewrite using `[show (((Matrix.of fun i j => c' i (th j)).det : Rv F v) : F) = (Rv F v).subtype (Matrix.of fun i j => c' i (th j)).det from rfl, this, hmap, Matrix.det_mul, Matrix.det_diagonal]`. Establish `hP0 : (∏ i, π ^ (-μ i)) ≠ 0` using `Finset.prod_ne_zero_iff.mpr fun i _ => zpow_ne_zero _ hπ0`.

Establish `hdF0 : (((Matrix.of fun i j => c' i (th j)).det : Rv F v) : F) ≠ 0`. Rewrite using `[hdetF]`. Conclude with `mul_ne_zero hP0 hdet`. Establish `hdet' : (Matrix.of fun i j => c' i (th j)).det ≠ 0` using `fun h => hdF0 (by rw [h]; rfl)`. Establish `hlen` using `hL (Rv F v) Q ρ hb c' th hdet'`.

Rewrite `hlen` using `[addVal_eq_ord v _ hdF0]`. Establish `hord : ordAt v (((Matrix.of fun i j => c' i (th j)).det : Rv F v) : F) = ∑ i, -μ i + ordAt v (Matrix.of fun i j => c i (th j)).det`. Rewrite using `[hdetF, ordAt_mul_rationality v hP0 hdet, ordAt_prod_rationality v _ _ fun i => zpow_ne_zero _ hπ0]`. Use `congr 1`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations.

Rewrite using `[ordAt_zpow, hπ1, mul_one]`. Establish `hnn` using `ord_nonneg v _ hdF0`. Establish `htop : Module.length (Rv F v) (Q ⧸ Submodule.span (Rv F v) (Set.range th)) ≠ ⊤` using `ne_top_of_le_ne_top (ENat.coe_ne_top _) hlen`. Use `⟨(Module.length (Rv F v) (Q ⧸ Submodule.span (Rv F v) (Set.range th))).toNat, (ENat.coe_toNat htop).symm, ?_⟩` and prove the remaining obligations. Establish `hle : (Module.length (Rv F v) (Q ⧸ Submodule.span (Rv F v) (Set.range th))).toNat ≤ (ordAt v (((Matrix.of fun i j => c' i (th j)).det : Rv F v) : F)).toNat`.

Rewrite `hlen` using `[← ENat.coe_toNat htop]`. Conclude with `hlen` after adjusting the coercions. Establish `hle' : ((Module.length (Rv F v) (Q ⧸ Submodule.span (Rv F v) (Set.range th))).toNat : ℝ) ≤ (ordAt v (((Matrix.of fun i j => c' i (th j)).det : Rv F v) : F) : ℝ)`. Establish `: ((Module.length (Rv F v) (Q ⧸ Submodule.span (Rv F v) (Set.range th))).toNat : ℤ) ≤ ordAt v (((Matrix.of fun i j => c' i (th j)).det : Rv F v) : F)` using `by omega`. Conclude with `this` after adjusting the coercions.

Rewrite `hle'` using `[hord]`. Move the coercions through the operations in `at hle'`. Establish `hsum : ∑ i, (-(μ i : ℝ)) ≤ ∑ i, (β + s i)` using `Finset.sum_le_sum fun i _ => hμβ i`. Rewrite `hsum` using `[Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem exists_length_quotient_span_le (hL : QuotLocalStatement) {R F : Type} [CommRing R] [IsDedekindDomain R]
    [Field F] [Algebra R F] [IsFractionRing R F] (v : HeightOneSpectrum R) (Q : Type)
    [AddCommGroup Q] [Module (Rv F v) Q] (ρ : ℕ) (hb : Nonempty (Module.Basis (Fin ρ) (Rv F v) Q))
    (c : Fin ρ → (Q →ₗ[Rv F v] F)) (s : Fin ρ → ℝ) (β : ℝ) (th : Fin ρ → Q)
    (hc : ∀ i q, c i q ≠ 0 → -β ≤ (ordAt v (c i q) : ℝ) + s i)
    (hdet : (Matrix.of fun i j => c i (th j)).det ≠ 0) :
    ∃ n : ℕ, Module.length (Rv F v) (Q ⧸ Submodule.span (Rv F v) (Set.range th)) = n ∧
      (n : ℝ) ≤ (ordAt v (Matrix.of fun i j => c i (th j)).det : ℝ) + ∑ i, s i + ρ * β := by
  classical

  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible (Rv F v)
  set π : F := (ϖ : F) with hπdef
  have hπ0 : π ≠ 0 := fun h => hϖ.ne_zero (Subtype.ext h)
  have hπ1 : ordAt v π = 1 := by
    have h1 := (addVal_eq_ord v ϖ hπ0).symm.trans (IsDiscreteValuationRing.addVal_uniformizer hϖ)
    have h2 : (ordAt v π).toNat = 1 := by exact_mod_cast h1
    have h3 := ord_nonneg v ϖ hπ0
    omega

  have hne : ∀ i, ∃ q, c i q ≠ 0 := by
    intro i
    by_contra h
    push_neg at h
    exact hdet (Matrix.det_eq_zero_of_row_eq_zero i fun j => by simp [h])

  have hex : ∀ i, ∃ μ : ℤ, (∃ q, c i q ≠ 0 ∧ ordAt v (c i q) = μ) ∧
      ∀ q, c i q ≠ 0 → μ ≤ ordAt v (c i q) := by
    intro i
    obtain ⟨lb, ⟨q, hq, rfl⟩, hlb⟩ := Int.exists_least_of_bdd
      (P := fun z => ∃ q, c i q ≠ 0 ∧ ordAt v (c i q) = z)
      ⟨⌈-β - s i⌉, by
        rintro z ⟨q, hq, rfl⟩
        refine Int.ceil_le.mpr ?_
        have := hc i q hq
        linarith⟩
      (by obtain ⟨q, hq⟩ := hne i; exact ⟨_, q, hq, rfl⟩)
    exact ⟨_, ⟨q, hq, rfl⟩, fun q' hq' => hlb _ ⟨q', hq', rfl⟩⟩
  choose μ hμ1 hμ2 using hex
  have hμβ : ∀ i, -(μ i : ℝ) ≤ β + s i := by
    intro i
    obtain ⟨q, hq, hqμ⟩ := hμ1 i
    have := hc i q hq
    rw [hqμ] at this
    linarith

  have hmem : ∀ i q, π ^ (-μ i) * c i q ∈ Rv F v := by
    intro i q
    by_cases hq : c i q = 0
    · rw [hq, mul_zero]; exact (Rv F v).zero_mem
    · refine (mem_Rv_iff_ord v (mul_ne_zero (zpow_ne_zero _ hπ0) hq)).mpr ?_
      rw [ordAt_mul_rationality v (zpow_ne_zero _ hπ0) hq, ordAt_zpow, hπ1]
      have := hμ2 i q hq
      linarith
  let c' : Fin ρ → (Q →ₗ[Rv F v] Rv F v) := fun i =>
    { toFun := fun q => ⟨π ^ (-μ i) * c i q, hmem i q⟩
      map_add' := fun a b => by ext; simp [mul_add]
      map_smul' := fun r q => by
        ext
        simp only [LinearMap.map_smul, RingHom.id_apply, Subring.coe_mul, Subring.smul_def,
          smul_eq_mul]
        ring }
  have hmap : ((Matrix.of fun i j => c' i (th j)).map (Rv F v).subtype) =
      Matrix.diagonal (fun i => π ^ (-μ i)) * Matrix.of fun i j => c i (th j) := by
    ext i j
    simp [Matrix.diagonal_mul, c']
  have hdetF : (((Matrix.of fun i j => c' i (th j)).det : Rv F v) : F) =
      (∏ i, π ^ (-μ i)) * (Matrix.of fun i j => c i (th j)).det := by
    have := RingHom.map_det (Rv F v).subtype (Matrix.of fun i j => c' i (th j))
    simp only [RingHom.mapMatrix_apply] at this
    rw [show (((Matrix.of fun i j => c' i (th j)).det : Rv F v) : F) =
      (Rv F v).subtype (Matrix.of fun i j => c' i (th j)).det from rfl, this, hmap,
      Matrix.det_mul, Matrix.det_diagonal]
  have hP0 : (∏ i, π ^ (-μ i)) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun i _ => zpow_ne_zero _ hπ0
  have hdF0 : (((Matrix.of fun i j => c' i (th j)).det : Rv F v) : F) ≠ 0 := by
    rw [hdetF]; exact mul_ne_zero hP0 hdet
  have hdet' : (Matrix.of fun i j => c' i (th j)).det ≠ 0 := fun h => hdF0 (by rw [h]; rfl)
  have hlen := hL (Rv F v) Q ρ hb c' th hdet'
  rw [addVal_eq_ord v _ hdF0] at hlen
  have hord : ordAt v (((Matrix.of fun i j => c' i (th j)).det : Rv F v) : F) =
      ∑ i, -μ i + ordAt v (Matrix.of fun i j => c i (th j)).det := by
    rw [hdetF, ordAt_mul_rationality v hP0 hdet, ordAt_prod_rationality v _ _ fun i => zpow_ne_zero _ hπ0]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [ordAt_zpow, hπ1, mul_one]
  have hnn := ord_nonneg v _ hdF0
  have htop : Module.length (Rv F v) (Q ⧸ Submodule.span (Rv F v) (Set.range th)) ≠ ⊤ :=
    ne_top_of_le_ne_top (ENat.coe_ne_top _) hlen
  refine ⟨(Module.length (Rv F v) (Q ⧸ Submodule.span (Rv F v) (Set.range th))).toNat,
    (ENat.coe_toNat htop).symm, ?_⟩
  have hle : (Module.length (Rv F v) (Q ⧸ Submodule.span (Rv F v) (Set.range th))).toNat ≤
      (ordAt v (((Matrix.of fun i j => c' i (th j)).det : Rv F v) : F)).toNat := by
    rw [← ENat.coe_toNat htop] at hlen
    exact_mod_cast hlen
  have hle' : ((Module.length (Rv F v) (Q ⧸ Submodule.span (Rv F v) (Set.range th))).toNat : ℝ) ≤
      (ordAt v (((Matrix.of fun i j => c' i (th j)).det : Rv F v) : F) : ℝ) := by
    have : ((Module.length (Rv F v) (Q ⧸ Submodule.span (Rv F v) (Set.range th))).toNat : ℤ) ≤
        ordAt v (((Matrix.of fun i j => c' i (th j)).det : Rv F v) : F) := by omega
    exact_mod_cast this
  rw [hord] at hle'
  push_cast at hle'
  have hsum : ∑ i, (-(μ i : ℝ)) ≤ ∑ i, (β + s i) := Finset.sum_le_sum fun i _ => hμβ i
  rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul] at hsum
  linarith

end ReciprocityTheory.ChartRestriction.G.FreeQuotientRank

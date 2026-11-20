import Formalism.SharpRestriction.CuspSpanNormBounds.BridgeLemVC

noncomputable section

namespace Formalism.MainNotions.BridgeLemVN

open NumberField Formalism.HermitianLatticesTheory Formalism.ThetaLiftIndependence Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.RankOne Formalism.MainNotions.BridgeLemVR
  Formalism.MainNotions.BridgeLemVC

variable {K : Type} [Field K] [NumberField K] [StarRing K]

/- English proof (translation)
Introduce `a`. Prove the components needed by the constructor for the conclusion. Introduce `h`. Conclude with `⟨⟨a, (mem_cmF_iff K a).2 h⟩, rfl⟩`. Introduce and unpack `⟨x, rfl⟩`.

Conclude with `star_coe_cmF K x`.
-/
theorem fixF (K : Type) [Field K] [NumberField K] [StarRing K] :
    ∀ a : K, star a = a ↔ a ∈ Set.range (algebraMap (cmF K) K) := by
  intro a
  constructor
  · intro h
    exact ⟨⟨a, (mem_cmF_iff K a).2 h⟩, rfl⟩
  · rintro ⟨x, rfl⟩
    exact star_coe_cmF K x

/- English proof (translation)
Rewrite using `[Formalism.HermitianLatticeCounting.Final.LocalIntegralStructure.unitsSquareIndex (cmF K) (isReal_cmF hK), (discrTower K (cmF K) hK (fixF K)).2.1]`.
-/
theorem card_quot (hK : IsCMUnram K) :
    Nat.card ((𝓞 (cmF K))ˣ ⧸ (powMonoidHom 2 : (𝓞 (cmF K))ˣ →* (𝓞 (cmF K))ˣ).range) = 2 ^ fDeg K := by
  rw [Formalism.HermitianLatticeCounting.Final.LocalIntegralStructure.unitsSquareIndex (cmF K) (isReal_cmF hK),
    (discrTower K (cmF K) hK (fixF K)).2.1]

/- English proof (translation)
Rewrite using `[Submodule.span_mul_span, Set.singleton_mul_singleton]`.
-/
theorem span_mul_span1 (x y : K) :
    Submodule.span (𝓞 K) {x} * Submodule.span (𝓞 K) {y} = Submodule.span (𝓞 K) {x * y} := by
  rw [Submodule.span_mul_span, Set.singleton_mul_singleton]

/- English proof (translation)
The claim follows from `eq_inv_of_mul_eq_one_left (by rw [← map_mul, inv_mul_cancel, map_one])`.
-/
theorem iota_inv (x : (𝓞 (cmF K))ˣ) : iota K x⁻¹ = (iota K x)⁻¹ :=
  eq_inv_of_mul_eq_one_left (by rw [← map_mul, inv_mul_cancel, map_one])

/- English proof (translation)
Introduce `h0`. Use `congrArg (iota K) (mul_inv_cancel x)` as an intermediate fact. Rewrite `this` using `[map_mul, h0, zero_mul, map_one]`. Conclude with `zero_ne_one this`.
-/
theorem iota_ne_zero (x : (𝓞 (cmF K))ˣ) : iota K x ≠ 0 := by
  intro h0
  have := congrArg (iota K) (mul_inv_cancel x)
  rw [map_mul, h0, zero_mul, map_one] at this
  exact zero_ne_one this

/- English proof (translation)
The claim follows from `star_coe_cmF K _`.
-/
theorem star_iota (x : (𝓞 (cmF K))ˣ) : star (iota K x) = iota K x := star_coe_cmF K _

/- English proof (translation)
Establish `hlat : ∀ M : s, Submodule.IsLattice K (M : Submodule (𝓞 K) K)` using `fun M => (hs.1 M M.2).1`. Set `cl : s → ClassGroup (𝓞 K)` to `fun M => ClassGroup.mk K (fracU (hlat M))`. Set `base : s → s` to `fun M => Classical.choose (⟨M, rfl⟩ : ∃ B : s, cl B = cl M)`. Establish `hbase : ∀ M, cl (base M) = cl M` using `fun M => Classical.choose_spec (⟨M, rfl⟩ : ∃ B : s, cl B = cl M)`. Establish `gen : ∀ (γ γ' : ClassGroup (𝓞 K)) (hγ : ∃ B : s, cl B = γ) (hγ' : ∃ B : s, cl B = γ'), γ = γ' → Classical.choose hγ = Classical.choose hγ'`.

Introduce `γ γ' hγ hγ' e`. Substitute `e` using the available equality. Both sides reduce to the same expression. Establish `hbase_eq : ∀ M M', cl M = cl M' → base M = base M'` using `fun M M' e => gen _ _ _ _ e`. Establish `hex : ∀ M : s, ∃ a : K, a ≠ 0 ∧ (M : Submodule (𝓞 K) K) = Submodule.span (𝓞 K) {a} * ((base M : s) : Submodule (𝓞 K) K)` using `fun M => exists_eq_span_mul (hlat M) (hlat (base M)) (hbase M).symm`.

Use `choose a ha0 haM using hex`. Establish `hu : ∀ M : s, ∃ t : (𝓞 (cmF K))ˣ, iota K t = a M * star (a M)`. Introduce `M`. Take `⟨i1, i2⟩` from `norm_unit h h1 (hs.1 M M.2) (hs.1 _ (base M).2) (haM M)`. Conclude with `exists_unitF (mul_ne_zero (ha0 M) (star_ne_zero.2 (ha0 M))) i1 i2 (by rw [star_mul', star_star, mul_comm])`.

Use `choose t ht using hu`. Set `Q` to `(𝓞 (cmF K))ˣ ⧸ (powMonoidHom 2 : (𝓞 (cmF K))ˣ →* (𝓞 (cmF K))ˣ).range`. Set `Ψ : s → ClassGroup (𝓞 K) × Q` to `fun M => (cl M, ((t M : (𝓞 (cmF K))ˣ) : Q))`. Establish `hinj : Function.Injective Ψ`. Introduce `M M' e`.

Establish `ecl : cl M = cl M'` using `congrArg Prod.fst e`. Establish `eB : base M = base M'` using `hbase_eq M M' ecl`. Establish `eq : ((t M : (𝓞 (cmF K))ˣ) : Q) = ((t M' : (𝓞 (cmF K))ˣ) : Q)` using `congrArg Prod.snd e`. Rewrite `eq` using `[QuotientGroup.eq]`. Take `⟨v, hv⟩` from `eq`.

Use `set ν : K := iota K v with hνdef`. Establish `hν0 : ν ≠ 0` using `iota_ne_zero v`. Establish `hνs : star ν = ν` using `star_iota v`. Establish `hv' : ν ^ 2 = (iota K (t M))⁻¹ * iota K (t M')`. Rewrite using `[hνdef, ← map_pow, ← iota_inv, ← map_mul, ← hv, powMonoidHom_apply]`.

Establish `hu0 : a M * star (a M) ≠ 0` using `mul_ne_zero (ha0 M) (star_ne_zero.2 (ha0 M))`. Establish `key : a M' * star (a M') = a M * star (a M) * ν ^ 2`. Rewrite using `[← ht M, ← ht M', hv', mul_inv_cancel_left₀ (iota_ne_zero _)]`. Use `set b : K := a M' * (a M * ν)⁻¹ with hbdef`. Establish `hb0 : b ≠ 0` using `mul_ne_zero (ha0 M') (inv_ne_zero (mul_ne_zero (ha0 M) hν0))`.

Establish `hb : star b * b = 1`. Establish `e : star b * b = (a M' * star (a M')) * (a M * star (a M) * ν ^ 2)⁻¹`. Rewrite using `[hbdef, star_mul', star_inv₀, star_mul', hνs]`. Establish `hsa : star (a M) ≠ 0` using `star_ne_zero.2 (ha0 M)`. Clear the denominators using the available nonvanishing facts.

Rewrite using `[e, key, mul_inv_cancel₀ (mul_ne_zero hu0 (pow_ne_zero 2 hν0))]`. Set `g : K ≃ₗ[K] K` to `LinearEquiv.smulOfNeZero K K b hb0`. Establish `hg : g ∈ isom h`. Use `(mem_isom_iff h1 g).2 ?_` and prove the remaining obligations. Use `show star (b • (1 : K)) * (b • (1 : K)) = 1`.

Rewrite using `[smul_eq_mul, mul_one]`. Conclude with `hb`. Take `⟨w, hw⟩` from `exists_unitK v`. Establish `hwinv : algebraMap (𝓞 K) K ((w⁻¹ : (𝓞 K)ˣ) : 𝓞 K) = ν⁻¹`. Rewrite using `[hνdef, ← hw]`.

Conclude with `eq_inv_of_mul_eq_one_left (by rw [← map_mul, Units.inv_mul, map_one])`. Establish `hgM : gmap g (M : Submodule (𝓞 K) K) = M'`. Rewrite using `[gmap_smul, haM M, haM M', ← eB, ← mul_assoc, span_mul_span1]`. Establish `e : b * a M = a M' * ν⁻¹`. Rewrite using `[hbdef]`.

Clear the denominators using the available nonvanishing facts. Conclude with `mul_div_cancel_right₀ _ (ha0 M)`. Rewrite using `[e, ← span_mul_span1, mul_assoc, ← hwinv, span_unit_mul]`. Establish `hU` using `hs.2 M' (hs.1 M' M'.2)`. Conclude with `Subtype.ext (hU.unique ⟨M.2, g, hg, hgM⟩ ⟨M'.2, 1, (isom h).one_mem, gmap_one _⟩)`.

Establish `hQ : Nat.card Q = 2 ^ fDeg K` using `card_quot hK`. Establish `: Finite Q` using `Nat.finite_of_card_ne_zero (by rw [hQ]; positivity)`. Establish `hc` using `Nat.card_le_card_of_injective Ψ hinj`. Rewrite `hc` using `[Nat.card_prod, hQ, Nat.card_eq_fintype_card (α := ClassGroup (𝓞 K)), Nat.card_eq_fintype_card, Fintype.card_coe]`. Conclude with `hc`.
-/
theorem card_classReps_le (hK : IsCMUnram K) (h : K →ₗ⋆[K] K →ₗ[K] K) (h1 : h 1 1 ≠ 0)
    (s : Finset (Submodule (𝓞 K) K)) (hs : IsClassReps h (1 : Submodule (𝓞 K) K) s) :
    s.card ≤ classNumber K * 2 ^ fDeg K := by
  classical
  have hlat : ∀ M : s, Submodule.IsLattice K (M : Submodule (𝓞 K) K) := fun M => (hs.1 M M.2).1
  let cl : s → ClassGroup (𝓞 K) := fun M => ClassGroup.mk K (fracU (hlat M))
  let base : s → s := fun M => Classical.choose (⟨M, rfl⟩ : ∃ B : s, cl B = cl M)
  have hbase : ∀ M, cl (base M) = cl M := fun M =>
    Classical.choose_spec (⟨M, rfl⟩ : ∃ B : s, cl B = cl M)
  have gen : ∀ (γ γ' : ClassGroup (𝓞 K)) (hγ : ∃ B : s, cl B = γ) (hγ' : ∃ B : s, cl B = γ'),
      γ = γ' → Classical.choose hγ = Classical.choose hγ' := by
    intro γ γ' hγ hγ' e
    subst e
    rfl
  have hbase_eq : ∀ M M', cl M = cl M' → base M = base M' := fun M M' e => gen _ _ _ _ e
  have hex : ∀ M : s, ∃ a : K, a ≠ 0 ∧
      (M : Submodule (𝓞 K) K) = Submodule.span (𝓞 K) {a} * ((base M : s) : Submodule (𝓞 K) K) :=
    fun M => exists_eq_span_mul (hlat M) (hlat (base M)) (hbase M).symm
  choose a ha0 haM using hex
  have hu : ∀ M : s, ∃ t : (𝓞 (cmF K))ˣ, iota K t = a M * star (a M) := by
    intro M
    obtain ⟨i1, i2⟩ := norm_unit h h1 (hs.1 M M.2) (hs.1 _ (base M).2) (haM M)
    exact exists_unitF (mul_ne_zero (ha0 M) (star_ne_zero.2 (ha0 M))) i1 i2
      (by rw [star_mul', star_star, mul_comm])
  choose t ht using hu
  let Q := (𝓞 (cmF K))ˣ ⧸ (powMonoidHom 2 : (𝓞 (cmF K))ˣ →* (𝓞 (cmF K))ˣ).range
  let Ψ : s → ClassGroup (𝓞 K) × Q := fun M => (cl M, ((t M : (𝓞 (cmF K))ˣ) : Q))
  have hinj : Function.Injective Ψ := by
    intro M M' e
    have ecl : cl M = cl M' := congrArg Prod.fst e
    have eB : base M = base M' := hbase_eq M M' ecl
    have eq : ((t M : (𝓞 (cmF K))ˣ) : Q) = ((t M' : (𝓞 (cmF K))ˣ) : Q) := congrArg Prod.snd e
    rw [QuotientGroup.eq] at eq
    obtain ⟨v, hv⟩ := eq
    set ν : K := iota K v with hνdef
    have hν0 : ν ≠ 0 := iota_ne_zero v
    have hνs : star ν = ν := star_iota v
    have hv' : ν ^ 2 = (iota K (t M))⁻¹ * iota K (t M') := by
      rw [hνdef, ← map_pow, ← iota_inv, ← map_mul, ← hv, powMonoidHom_apply]
    have hu0 : a M * star (a M) ≠ 0 := mul_ne_zero (ha0 M) (star_ne_zero.2 (ha0 M))
    have key : a M' * star (a M') = a M * star (a M) * ν ^ 2 := by
      rw [← ht M, ← ht M', hv', mul_inv_cancel_left₀ (iota_ne_zero _)]
    set b : K := a M' * (a M * ν)⁻¹ with hbdef
    have hb0 : b ≠ 0 := mul_ne_zero (ha0 M') (inv_ne_zero (mul_ne_zero (ha0 M) hν0))
    have hb : star b * b = 1 := by
      have e : star b * b = (a M' * star (a M')) * (a M * star (a M) * ν ^ 2)⁻¹ := by
        rw [hbdef, star_mul', star_inv₀, star_mul', hνs]
        have hsa : star (a M) ≠ 0 := star_ne_zero.2 (ha0 M)
        field_simp
      rw [e, key, mul_inv_cancel₀ (mul_ne_zero hu0 (pow_ne_zero 2 hν0))]
    let g : K ≃ₗ[K] K := LinearEquiv.smulOfNeZero K K b hb0
    have hg : g ∈ isom h := by
      refine (mem_isom_iff h1 g).2 ?_
      show star (b • (1 : K)) * (b • (1 : K)) = 1
      rw [smul_eq_mul, mul_one]
      exact hb
    obtain ⟨w, hw⟩ := exists_unitK v
    have hwinv : algebraMap (𝓞 K) K ((w⁻¹ : (𝓞 K)ˣ) : 𝓞 K) = ν⁻¹ := by
      rw [hνdef, ← hw]
      exact eq_inv_of_mul_eq_one_left (by rw [← map_mul, Units.inv_mul, map_one])
    have hgM : gmap g (M : Submodule (𝓞 K) K) = M' := by
      rw [gmap_smul, haM M, haM M', ← eB, ← mul_assoc, span_mul_span1]
      have e : b * a M = a M' * ν⁻¹ := by
        rw [hbdef]
        field_simp
        exact mul_div_cancel_right₀ _ (ha0 M)
      rw [e, ← span_mul_span1, mul_assoc, ← hwinv, span_unit_mul]
    have hU := hs.2 M' (hs.1 M' M'.2)
    exact Subtype.ext (hU.unique ⟨M.2, g, hg, hgM⟩ ⟨M'.2, 1, (isom h).one_mem, gmap_one _⟩)
  have hQ : Nat.card Q = 2 ^ fDeg K := card_quot hK
  have : Finite Q := Nat.finite_of_card_ne_zero (by rw [hQ]; positivity)
  have hc := Nat.card_le_card_of_injective Ψ hinj
  rw [Nat.card_prod, hQ, Nat.card_eq_fintype_card (α := ClassGroup (𝓞 K)), Nat.card_eq_fintype_card,
    Fintype.card_coe] at hc
  exact hc

/- English proof (translation)
Unfold `mass`. Use `split_ifs with hex`. Use `le_trans ?_ (Nat.cast_le.2 (card_classReps_le hK h h1 _ hex.choose_spec))` and prove the remaining obligations. Combine the equalities or inequalities in the displayed calculation. Use `Finset.sum_le_sum fun M _ => ?_` and prove the remaining obligations.

Break down `Nat.eq_zero_or_pos (Nat.card (autL h M)) with h0 | hpos` into its components or cases. Rewrite using `[h0]`. Simplify using the standard rewrite rules. Conclude with `inv_le_one_of_one_le₀ (by exact_mod_cast hpos)`. Use `_ = (hex.choose.card : ℝ) := by simp`.

Check the signs of the components of the expression.
-/
theorem mass_le (hK : IsCMUnram K) (h : K →ₗ⋆[K] K →ₗ[K] K) (h1 : h 1 1 ≠ 0) :
    mass h (1 : Submodule (𝓞 K) K) ≤ ((classNumber K * 2 ^ fDeg K : ℕ) : ℝ) := by
  unfold mass
  split_ifs with hex
  · refine le_trans ?_ (Nat.cast_le.2 (card_classReps_le hK h h1 _ hex.choose_spec))
    calc ∑ M ∈ hex.choose, ((Nat.card (autL h M) : ℕ) : ℝ)⁻¹ ≤ ∑ _M ∈ hex.choose, (1 : ℝ) := by
          refine Finset.sum_le_sum fun M _ => ?_
          rcases Nat.eq_zero_or_pos (Nat.card (autL h M)) with h0 | hpos
          · rw [h0]; simp
          · exact inv_le_one_of_one_le₀ (by exact_mod_cast hpos)
      _ = (hex.choose.card : ℝ) := by simp
  · positivity

/- English proof (translation)
Assemble the required witnesses or components as `⟨⟨{1}, by rw [Finset.coe_singleton, ← Submodule.one_eq_span]⟩, span_eq_top_of_ne_zero (Submodule.mem_one.2 ⟨1, map_one _⟩) one_ne_zero⟩`.
-/
theorem isLattice_one : Submodule.IsLattice K (1 : Submodule (𝓞 K) K) :=
  ⟨⟨{1}, by rw [Finset.coe_singleton, ← Submodule.one_eq_span]⟩,
    span_eq_top_of_ne_zero (Submodule.mem_one.2 ⟨1, map_one _⟩) one_ne_zero⟩

/- English proof (translation)
Establish `hs` using `stdForm_isSymm K 1`. Establish `ho` using `stdLat_isOrtho K 1`. Use `finiteDimensional_of_ortho ho` as an intermediate fact. Take `⟨h', A, hn, hA, hex, e⟩` from `exists_model hs (isTotPosDef_of_ortho hK hs ho) (finrank_of_ortho ho) (isLattice_of_ortho ho)`. Rewrite using `[← e, ← mass_eq_of_lattices hn hn hA isLattice_one hex]`.

Conclude with `mass_le hK h' hn`.
-/
theorem mass_std_one_le (hK : IsCMUnram K) :
    mass (stdForm K 1) (stdLat K 1) ≤ ((classNumber K * 2 ^ fDeg K : ℕ) : ℝ) := by
  have hs := stdForm_isSymm K 1
  have ho := stdLat_isOrtho K 1
  have := finiteDimensional_of_ortho ho
  obtain ⟨h', A, hn, hA, hex, e⟩ := exists_model hs (isTotPosDef_of_ortho hK hs ho) (finrank_of_ortho ho)
    (isLattice_of_ortho ho)
  rw [← e, ← mass_eq_of_lattices hn hn hA isLattice_one hex]
  exact mass_le hK h' hn

end Formalism.MainNotions.BridgeLemVN

end

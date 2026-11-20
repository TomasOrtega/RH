import Mathlib
import ReciprocityTheory.ClassFieldTheory.LocalClassField.RecDefs
import ReciprocityTheory.ClassFieldTheory.LocalClassField.GalBasic

namespace ReciprocityTheory.DiscreteGroups.LocalClassField

open _root_.Neutral.B1 ReciprocityTheory.Coh Function

variable {p : ℕ} [Fact p.Prime] {K L : IntermediateField ℚ_[p] (PadicAlgCl p)}

/- English proof (translation)
Unfold `normHom`. Rewrite using `[finsum_eq_sum_of_fintype, AddMonoidHom.finsetSum_apply]`. Both sides reduce to the same expression.
-/
theorem normHom_apply [Fintype (GK p K ⧸ subG p K L)] (y : KbarMult p) :
    normHom p K L y = ∑ c : GK p K ⧸ subG p K L, kbarRep p K c.out y := by
  unfold normHom
  rw [finsum_eq_sum_of_fintype, AddMonoidHom.finsetSum_apply]
  rfl

/- English proof (translation)
Rewrite using `[map_mul]`. Both sides reduce to the same expression.
-/
theorem kbarRep_mul (σ τ : GK p K) (y : KbarMult p) :
    kbarRep p K (σ * τ) y = kbarRep p K σ (kbarRep p K τ y) := by
  rw [map_mul]; rfl

/- English proof (translation)
Use `⟨Additive.ofMul (-1 : (PadicAlgCl p)ˣ), fun h0 => ?_⟩` and prove the remaining obligations. Establish `h1 : ((-1 : (PadicAlgCl p)ˣ) : PadicAlgCl p) = ((1 : (PadicAlgCl p)ˣ) : PadicAlgCl p)` using `congrArg (fun u : (PadicAlgCl p)ˣ => (u : PadicAlgCl p)) h0`. Rewrite `h1` using `[Units.val_neg, Units.val_one]`. Evaluate the numerical expressions using `at h1`.
-/
theorem exists_ne_zero_KbarMult : ∃ x : KbarMult p, x ≠ 0 := by
  refine ⟨Additive.ofMul (-1 : (PadicAlgCl p)ˣ), fun h0 => ?_⟩
  have h1 : ((-1 : (PadicAlgCl p)ˣ) : PadicAlgCl p) = ((1 : (PadicAlgCl p)ˣ) : PadicAlgCl p) :=
    congrArg (fun u : (PadicAlgCl p)ˣ => (u : PadicAlgCl p)) h0
  rw [Units.val_neg, Units.val_one] at h1
  norm_num at h1

/- English proof (translation)
Unfold `normHom`. Apply `finsum_of_infinite_support` to reduce the goal to its premises. Establish `hs : Function.support (fun c : GK p K ⧸ subG p K L => (kbarRep p K c.out).toAddMonoidHom) = Set.univ`. Use extensionality with `c`. Simplify using `only [mem_support, Set.mem_univ, iff_true]`.

Introduce `h0`. Take `⟨x, hx⟩` from `exists_ne_zero_KbarMult (p := p)`. Apply `hx` to reduce the goal to its premises. Establish `h1 : kbarRep p K c.out x = 0` using `DFunLike.congr_fun h0 x`. Establish `h2 : kbarRep p K (c.out⁻¹ * c.out) x = 0` using `by rw [kbarRep_mul, h1, map_zero]`.

Rewrite `h2` using `[inv_mul_cancel, map_one]`. Conclude with `h2`. Rewrite using `[hs]`. Conclude with `Set.infinite_univ`.
-/
theorem normHom_of_infinite [Infinite (GK p K ⧸ subG p K L)] : normHom p K L = 0 := by
  unfold normHom
  apply finsum_of_infinite_support
  have hs : Function.support (fun c : GK p K ⧸ subG p K L => (kbarRep p K c.out).toAddMonoidHom) =
      Set.univ := by
    ext c
    simp only [mem_support, Set.mem_univ, iff_true]
    intro h0
    obtain ⟨x, hx⟩ := exists_ne_zero_KbarMult (p := p)
    apply hx
    have h1 : kbarRep p K c.out x = 0 := DFunLike.congr_fun h0 x
    have h2 : kbarRep p K (c.out⁻¹ * c.out) x = 0 := by rw [kbarRep_mul, h1, map_zero]
    rw [inv_mul_cancel, map_one] at h2
    exact h2
  rw [hs]
  exact Set.infinite_univ

/- English proof (translation)
Establish `h1 : σ⁻¹ * (QuotientGroup.mk σ : GK p K ⧸ subG p K L).out ∈ subG p K L` using `QuotientGroup.eq.1 (QuotientGroup.out_eq' _).symm`. Establish `h2 : kbarRep p K (σ⁻¹ * (QuotientGroup.mk σ : GK p K ⧸ subG p K L).out) y = y` using `Units.ext (h1 _ hy)`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[mul_inv_cancel_left]`. Use `_ = kbarRep p K σ y := by rw [kbarRep_mul, h2]`.
-/
theorem kbarRep_out (y : KbarMult p) (hy : y ∈ multOf p L) (σ : GK p K) :
    kbarRep p K (QuotientGroup.mk σ : GK p K ⧸ subG p K L).out y = kbarRep p K σ y := by
  have h1 : σ⁻¹ * (QuotientGroup.mk σ : GK p K ⧸ subG p K L).out ∈ subG p K L :=
    QuotientGroup.eq.1 (QuotientGroup.out_eq' _).symm
  have h2 : kbarRep p K (σ⁻¹ * (QuotientGroup.mk σ : GK p K ⧸ subG p K L).out) y = y :=
    Units.ext (h1 _ hy)
  calc kbarRep p K (QuotientGroup.mk σ : GK p K ⧸ subG p K L).out y
      = kbarRep p K (σ * (σ⁻¹ * (QuotientGroup.mk σ : GK p K ⧸ subG p K L).out)) y := by
        rw [mul_inv_cancel_left]
    _ = kbarRep p K σ y := by rw [kbarRep_mul, h2]

/- English proof (translation)
Use `finite_GalLK (p := p) (K := K) hL` as an intermediate fact. Use `Fintype.ofFinite (GK p K ⧸ subG p K L)` as an intermediate fact. Rewrite using `[mem_multOf_iff_fixed (le_refl K)]`. Introduce `σ _`. Rewrite using `[normHom_apply, map_sum]`.

Use `Fintype.sum_equiv (MulAction.toPerm σ) _ _ fun c => ?_` and prove the remaining obligations. Proceed by induction on `c using QuotientGroup.induction_on with`. Consider the case `H τ => show _ = kbarRep p K (QuotientGroup.mk (σ * τ) : GK p K ⧸ subG p K L).out y`. Rewrite using `[kbarRep_out y hy, kbarRep_out y hy, kbarRep_mul]`.
-/
theorem normHom_mem_multiplicative_group (hL : FiniteDimensional ℚ_[p] L) (y : KbarMult p) (hy : y ∈ multOf p L) :
    normHom p K L y ∈ multOf p K := by
  have := finite_GalLK (p := p) (K := K) hL
  have := Fintype.ofFinite (GK p K ⧸ subG p K L)
  rw [mem_multOf_iff_fixed (le_refl K)]
  intro σ _
  rw [normHom_apply, map_sum]
  refine Fintype.sum_equiv (MulAction.toPerm σ) _ _ fun c => ?_
  induction c using QuotientGroup.induction_on with
  | H τ =>
    show _ = kbarRep p K (QuotientGroup.mk (σ * τ) : GK p K ⧸ subG p K L).out y
    rw [kbarRep_out y hy, kbarRep_out y hy, kbarRep_mul]

/- English proof (translation)
Use `(normHom_apply (K := K) (L := L) (y.1 : KbarMult p)).trans ?_` and prove the remaining obligations. Establish `h1 : (∑ g, (layer p K L).rho g y).1 = ∑ g, ((layer p K L).rho g y).1` using `map_sum (Submodule.subtype _) _ _`. Use `Eq.trans ?_ h1.symm` and prove the remaining obligations. Use `Finset.sum_congr rfl fun g _ => ?_` and prove the remaining obligations. Use `conv_rhs => rw [← QuotientGroup.out_eq' g]`.

Both sides reduce to the same expression.
-/
theorem normHom_layer_eq_trace_sum [(subG p K L).Normal] [Fintype (GalLK p K L)] (y : (layer p K L).V) :
    normHom p K L y.1 = (∑ g, (layer p K L).rho g y).1 := by
  refine (normHom_apply (K := K) (L := L) (y.1 : KbarMult p)).trans ?_
  have h1 : (∑ g, (layer p K L).rho g y).1 = ∑ g, ((layer p K L).rho g y).1 :=
    map_sum (Submodule.subtype _) _ _
  refine Eq.trans ?_ h1.symm
  refine Finset.sum_congr rfl fun g _ => ?_
  conv_rhs => rw [← QuotientGroup.out_eq' g]
  rfl

/- English proof (translation)
Break down `finite_or_infinite (GK p K ⧸ subG p K L) with hf | hi` into its components or cases. Use `Fintype.ofFinite (GK p K ⧸ subG p K L)` as an intermediate fact. Rewrite using `[normHom_apply]`. Establish `h1 : ∀ c : GK p K ⧸ subG p K L, kbarRep p K c.out x = x` using `fun c => Units.ext (c.out.commutes ⟨_, hx⟩)`. Simplify using `only [h1]`.

Rewrite using `[Finset.sum_const, Finset.card_univ, ← Nat.card_eq_fintype_card]`. Both sides reduce to the same expression. Rewrite using `[normHom_of_infinite]`. Establish `h0 : degLK p K L = 0` using `Subgroup.index_eq_zero_iff_infinite.2 hi`. Rewrite using `[h0, zero_smul]`.

Both sides reduce to the same expression.
-/
theorem normHom_of_mem_base (x : KbarMult p) (hx : x ∈ multOf p K) :
    normHom p K L x = degLK p K L • x := by
  rcases finite_or_infinite (GK p K ⧸ subG p K L) with hf | hi
  · have := Fintype.ofFinite (GK p K ⧸ subG p K L)
    rw [normHom_apply]
    have h1 : ∀ c : GK p K ⧸ subG p K L, kbarRep p K c.out x = x :=
      fun c => Units.ext (c.out.commutes ⟨_, hx⟩)
    simp only [h1]
    rw [Finset.sum_const, Finset.card_univ, ← Nat.card_eq_fintype_card]
    rfl
  · rw [normHom_of_infinite]
    have h0 : degLK p K L = 0 := Subgroup.index_eq_zero_iff_infinite.2 hi
    rw [h0, zero_smul]
    rfl

/- English proof (translation)
Establish `h1` using `finiteIndex_subG (p := p) (K := K) hL'`. Establish `h2 : (subG p K L).FiniteIndex` using `Subgroup.finiteIndex_of_le (subG_anti h')`. Conclude with `Subgroup.finite_quotient_of_finiteIndex`.
-/
theorem finite_quot_of_le {L' : IntermediateField ℚ_[p] (PadicAlgCl p)} (hL' : FiniteDimensional ℚ_[p] L')
    (h' : L ≤ L') : Finite (GK p K ⧸ subG p K L) := by
  have h1 := finiteIndex_subG (p := p) (K := K) hL'
  have h2 : (subG p K L).FiniteIndex := Subgroup.finiteIndex_of_le (subG_anti h')
  exact Subgroup.finite_quotient_of_finiteIndex

/- English proof (translation)
Establish `hres : ∀ τ : GK p L, resGK h τ ∈ subG p K L` using `fun τ => by`. Rewrite using `[← range_resGK h]`. Conclude with `⟨τ, rfl⟩`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨c, d⟩ ⟨c', d'⟩ hcd`.

Establish `h1 : (c.out * resGK h d.out)⁻¹ * (c'.out * resGK h d'.out) ∈ subG p K L'` using `QuotientGroup.eq.1 hcd`. Establish `h2 : c.out⁻¹ * c'.out ∈ subG p K L`. Establish `h3` using `(subG p K L).mul_mem ((subG p K L).mul_mem (hres d.out) (subG_anti h' h1)) ((subG p K L).inv_mem (hres d'.out))`. Establish `h4 : resGK h d.out * ((c.out * resGK h d.out)⁻¹ * (c'.out * resGK h d'.out)) * (resGK h d'.out)⁻¹ = c.out⁻¹ * c'.out` using `by group`. Rewrite `h3` using `[h4]`. Then use the resulting hypothesis.

Establish `hc : c = c'`. Rewrite using `[← QuotientGroup.out_eq' c, ← QuotientGroup.out_eq' c']`. Conclude with `QuotientGroup.eq.2 h2`. Substitute `hc` using the available equality. Establish `h5 : resGK h (d.out⁻¹ * d'.out) ∈ subG p K L'`.

Establish `h6 : (c.out * resGK h d.out)⁻¹ * (c.out * resGK h d'.out) = resGK h (d.out⁻¹ * d'.out)`. Rewrite using `[map_mul, map_inv]`. Use `group`. Rewrite `h1` using `[h6]`. Then use the resulting hypothesis. Establish `hd : d = d'`.

Rewrite using `[← QuotientGroup.out_eq' d, ← QuotientGroup.out_eq' d']`. Conclude with `QuotientGroup.eq.2 h5`. Rewrite using `[hd]`. Introduce `e`. Proceed by induction on `e using QuotientGroup.induction_on with`.

Consider the case `H σ`. Establish `h1 : (QuotientGroup.mk σ : GK p K ⧸ subG p K L).out⁻¹ * σ ∈ subG p K L` using `QuotientGroup.eq.1 (QuotientGroup.out_eq' _)`. Establish `h1' : (QuotientGroup.mk σ : GK p K ⧸ subG p K L).out⁻¹ * σ ∈ (resGK h).range`. Rewrite using `[range_resGK h]`. Conclude with `h1`.

Take `⟨τ, hτ⟩` from `h1'`. Use `⟨(QuotientGroup.mk σ, QuotientGroup.mk τ), ?_⟩` and prove the remaining obligations. Establish `h2 : (QuotientGroup.mk τ : GK p L ⧸ subG p L L').out⁻¹ * τ ∈ subG p L L'` using `QuotientGroup.eq.1 (QuotientGroup.out_eq' _)`. Apply `QuotientGroup.eq.2` to reduce the goal to its premises. Establish `h3 : ((QuotientGroup.mk σ : GK p K ⧸ subG p K L).out * resGK h (QuotientGroup.mk τ : GK p L ⧸ subG p L L').out)⁻¹ * σ = resGK h ((QuotientGroup.mk τ : GK p L ⧸ subG p L L').out⁻¹ * τ)`.

Rewrite using `[map_mul, map_inv, hτ, mul_inv_rev, mul_assoc]`. Rewrite using `[h3]`. Conclude with `h2`.
-/
theorem tower_bijective {L' : IntermediateField ℚ_[p] (PadicAlgCl p)} (h : K ≤ L) (h' : L ≤ L') :
    Bijective (fun x : (GK p K ⧸ subG p K L) × (GK p L ⧸ subG p L L') =>
      (QuotientGroup.mk (x.1.out * resGK h x.2.out) : GK p K ⧸ subG p K L')) := by
  have hres : ∀ τ : GK p L, resGK h τ ∈ subG p K L := fun τ => by
    rw [← range_resGK h]; exact ⟨τ, rfl⟩
  constructor
  · rintro ⟨c, d⟩ ⟨c', d'⟩ hcd
    have h1 : (c.out * resGK h d.out)⁻¹ * (c'.out * resGK h d'.out) ∈ subG p K L' :=
      QuotientGroup.eq.1 hcd
    have h2 : c.out⁻¹ * c'.out ∈ subG p K L := by
      have h3 := (subG p K L).mul_mem ((subG p K L).mul_mem (hres d.out) (subG_anti h' h1))
        ((subG p K L).inv_mem (hres d'.out))
      have h4 : resGK h d.out * ((c.out * resGK h d.out)⁻¹ * (c'.out * resGK h d'.out)) *
          (resGK h d'.out)⁻¹ = c.out⁻¹ * c'.out := by group
      rwa [h4] at h3
    have hc : c = c' := by
      rw [← QuotientGroup.out_eq' c, ← QuotientGroup.out_eq' c']
      exact QuotientGroup.eq.2 h2
    subst hc
    have h5 : resGK h (d.out⁻¹ * d'.out) ∈ subG p K L' := by
      have h6 : (c.out * resGK h d.out)⁻¹ * (c.out * resGK h d'.out) = resGK h (d.out⁻¹ * d'.out) := by
        rw [map_mul, map_inv]; group
      rwa [h6] at h1
    have hd : d = d' := by
      rw [← QuotientGroup.out_eq' d, ← QuotientGroup.out_eq' d']
      exact QuotientGroup.eq.2 h5
    rw [hd]
  · intro e
    induction e using QuotientGroup.induction_on with
    | H σ =>
      have h1 : (QuotientGroup.mk σ : GK p K ⧸ subG p K L).out⁻¹ * σ ∈ subG p K L :=
        QuotientGroup.eq.1 (QuotientGroup.out_eq' _)
      have h1' : (QuotientGroup.mk σ : GK p K ⧸ subG p K L).out⁻¹ * σ ∈ (resGK h).range := by
        rw [range_resGK h]; exact h1
      obtain ⟨τ, hτ⟩ := h1'
      refine ⟨(QuotientGroup.mk σ, QuotientGroup.mk τ), ?_⟩
      have h2 : (QuotientGroup.mk τ : GK p L ⧸ subG p L L').out⁻¹ * τ ∈ subG p L L' :=
        QuotientGroup.eq.1 (QuotientGroup.out_eq' _)
      apply QuotientGroup.eq.2
      have h3 : ((QuotientGroup.mk σ : GK p K ⧸ subG p K L).out *
          resGK h (QuotientGroup.mk τ : GK p L ⧸ subG p L L').out)⁻¹ * σ =
          resGK h ((QuotientGroup.mk τ : GK p L ⧸ subG p L L').out⁻¹ * τ) := by
        rw [map_mul, map_inv, hτ, mul_inv_rev, mul_assoc]
      rw [h3]
      exact h2

/- English proof (translation)
Use `finite_quot_of_le (p := p) (K := K) hL' h'` as an intermediate fact. Use `finite_quot_of_le (p := p) (K := K) hL' (le_refl L')` as an intermediate fact. Use `finite_quot_of_le (p := p) (K := L) hL' (le_refl L')` as an intermediate fact. Use `Fintype.ofFinite (GK p K ⧸ subG p K L)` as an intermediate fact. Use `Fintype.ofFinite (GK p K ⧸ subG p K L')` as an intermediate fact.

Use `Fintype.ofFinite (GK p L ⧸ subG p L L')` as an intermediate fact. Rewrite using `[normHom_apply, normHom_apply, normHom_apply]`. Simplify using `only [map_sum]`. Rewrite using `[← Fintype.sum_prod_type']`. Use `Fintype.sum_bijective _ (tower_bijective h h') _ _ fun x => ?_` and prove the remaining obligations.

Rewrite using `[kbarRep_out y hy, kbarRep_mul]`. Both sides reduce to the same expression.
-/
theorem normHom_comp_normHom_of_le {L' : IntermediateField ℚ_[p] (PadicAlgCl p)} (hL' : FiniteDimensional ℚ_[p] L')
    (h : K ≤ L) (h' : L ≤ L') (y : KbarMult p) (hy : y ∈ multOf p L') :
    normHom p K L (normHom p L L' y) = normHom p K L' y := by
  have := finite_quot_of_le (p := p) (K := K) hL' h'
  have := finite_quot_of_le (p := p) (K := K) hL' (le_refl L')
  have := finite_quot_of_le (p := p) (K := L) hL' (le_refl L')
  have := Fintype.ofFinite (GK p K ⧸ subG p K L)
  have := Fintype.ofFinite (GK p K ⧸ subG p K L')
  have := Fintype.ofFinite (GK p L ⧸ subG p L L')
  rw [normHom_apply, normHom_apply, normHom_apply]
  simp only [map_sum]
  rw [← Fintype.sum_prod_type']
  refine Fintype.sum_bijective _ (tower_bijective h h') _ _ fun x => ?_
  rw [kbarRep_out y hy, kbarRep_mul]
  rfl

/- English proof (translation)
Set `F : KbarMult p →+ Additive (PadicAlgCl p)` to `{ toFun := fun x => Additive.ofMul ((Additive.toMul x : (PadicAlgCl p)ˣ) : PadicAlgCl p) map_zero' := rfl map_add' := fun _ _ => rfl }`. Establish `h2` using `congrArg Additive.toMul (map_sum F f s)`. Rewrite `h2` using `[toMul_sum]`. Conclude with `h2`.
-/
theorem coe_sum_KbarMult {ι : Type*} (s : Finset ι) (f : ι → KbarMult p) :
    ((Additive.toMul (∑ c ∈ s, f c) : (PadicAlgCl p)ˣ) : PadicAlgCl p) =
      ∏ c ∈ s, ((Additive.toMul (f c) : (PadicAlgCl p)ˣ) : PadicAlgCl p) := by
  let F : KbarMult p →+ Additive (PadicAlgCl p) :=
    { toFun := fun x => Additive.ofMul ((Additive.toMul x : (PadicAlgCl p)ˣ) : PadicAlgCl p)
      map_zero' := rfl
      map_add' := fun _ _ => rfl }
  have h2 := congrArg Additive.toMul (map_sum F f s)
  rw [toMul_sum] at h2
  exact h2

/- English proof (translation)
Use `finite_GalLK (p := p) (K := K) hL` as an intermediate fact. Use `Fintype.ofFinite (GK p K ⧸ subG p K L)` as an intermediate fact. Establish `hfin : FiniteDimensional K (IntermediateField.extendScalars h)`. Apply `Module.finite_of_finrank_pos` to reduce the goal to its premises. Rewrite using `[← degLK_eq_finrank h]`.

Conclude with `degLK_pos hL`. Establish `hbij : Bijective (fun c : GK p K ⧸ subG p K L => ((c.out : PadicAlgCl p ≃ₐ[K] PadicAlgCl p) : PadicAlgCl p →ₐ[K] PadicAlgCl p).comp (IntermediateField.extendScalars h).val)`. Apply `Function.Injective.bijective_of_nat_card_le` to reduce the goal to its premises. Introduce `c c' hcc`. Rewrite using `[← QuotientGroup.out_eq' c, ← QuotientGroup.out_eq' c']`.

Apply `QuotientGroup.eq.2` to reduce the goal to its premises. Introduce `x hx`. Establish `h1 : c.out x = c'.out x` using `DFunLike.congr_fun hcc (⟨x, hx⟩ : IntermediateField.extendScalars h)`. Use `show c.out⁻¹ (c'.out x) = x`. Rewrite using `[← h1]`.

Conclude with `c.out.symm_apply_apply x`. Rewrite using `[Nat.card_eq_fintype_card, AlgHom.card, ← degLK_eq_finrank h]`. Conclude with `le_of_eq rfl`. Establish `h1` using `Algebra.norm_eq_prod_embeddings K (PadicAlgCl p) (⟨((Additive.toMul y : (PadicAlgCl p)ˣ) : PadicAlgCl p), hy⟩ : IntermediateField.extendScalars h)`. Use `Eq.trans ?_ h1.symm` and prove the remaining obligations.

Rewrite using `[normHom_apply]`. Use `(coe_sum_KbarMult _ _).trans ?_` and prove the remaining obligations. Conclude with `Fintype.prod_bijective _ hbij _ _ fun c => rfl`.
-/
theorem normHom_eq_algebra_norm (hL : FiniteDimensional ℚ_[p] L) (h : K ≤ L) (y : KbarMult p)
    (hy : y ∈ multOf p L) :
    ((Additive.toMul (normHom p K L y) : (PadicAlgCl p)ˣ) : PadicAlgCl p) =
      ((Algebra.norm K (⟨((Additive.toMul y : (PadicAlgCl p)ˣ) : PadicAlgCl p), hy⟩ :
        IntermediateField.extendScalars h) : K) : PadicAlgCl p) := by
  have := finite_GalLK (p := p) (K := K) hL
  have := Fintype.ofFinite (GK p K ⧸ subG p K L)
  have hfin : FiniteDimensional K (IntermediateField.extendScalars h) := by
    apply Module.finite_of_finrank_pos
    rw [← degLK_eq_finrank h]
    exact degLK_pos hL
  have hbij : Bijective (fun c : GK p K ⧸ subG p K L =>
      ((c.out : PadicAlgCl p ≃ₐ[K] PadicAlgCl p) : PadicAlgCl p →ₐ[K] PadicAlgCl p).comp
        (IntermediateField.extendScalars h).val) := by
    apply Function.Injective.bijective_of_nat_card_le
    · intro c c' hcc
      rw [← QuotientGroup.out_eq' c, ← QuotientGroup.out_eq' c']
      apply QuotientGroup.eq.2
      intro x hx
      have h1 : c.out x = c'.out x := DFunLike.congr_fun hcc (⟨x, hx⟩ : IntermediateField.extendScalars h)
      show c.out⁻¹ (c'.out x) = x
      rw [← h1]
      exact c.out.symm_apply_apply x
    · rw [Nat.card_eq_fintype_card, AlgHom.card, ← degLK_eq_finrank h]
      exact le_of_eq rfl
  have h1 := Algebra.norm_eq_prod_embeddings K (PadicAlgCl p)
    (⟨((Additive.toMul y : (PadicAlgCl p)ˣ) : PadicAlgCl p), hy⟩ : IntermediateField.extendScalars h)
  refine Eq.trans ?_ h1.symm
  rw [normHom_apply]
  refine (coe_sum_KbarMult _ _).trans ?_
  exact Fintype.prod_bijective _ hbij _ _ fun c => rfl

/- English proof (translation)
Introduce `x hx`. Rewrite `hx`, the goal using `[mem_normGrp_iff]`. Take `⟨y, hy, hxy⟩` from `hx`. Conclude with `⟨normHom p L L' y, normHom_mem_multiplicative_group hL' y hy, by rw [normHom_comp_normHom_of_le hL' h h' y hy, hxy]⟩`.
-/
theorem normGroup_antitone {L' : IntermediateField ℚ_[p] (PadicAlgCl p)} (hL' : FiniteDimensional ℚ_[p] L')
    (h : K ≤ L) (h' : L ≤ L') : normGrp p K L' ≤ normGrp p K L := by
  intro x hx
  rw [mem_normGrp_iff] at hx ⊢
  obtain ⟨y, hy, hxy⟩ := hx
  exact ⟨normHom p L L' y, normHom_mem_multiplicative_group hL' y hy, by rw [normHom_comp_normHom_of_le hL' h h' y hy, hxy]⟩

/- English proof (translation)
Rewrite using `[mem_normGrp_iff]`. Use `⟨ofK p K (Additive.ofMul x), h (ofK_mem p K _), ?_⟩` and prove the remaining obligations. Rewrite using `[normHom_of_mem_base _ (ofK_mem p K _), ofMul_pow, map_nsmul]`.
-/
theorem pow_degree_mem_normGroup (h : K ≤ L) (x : Kˣ) : x ^ degLK p K L ∈ normGrp p K L := by
  rw [mem_normGrp_iff]
  refine ⟨ofK p K (Additive.ofMul x), h (ofK_mem p K _), ?_⟩
  rw [normHom_of_mem_base _ (ofK_mem p K _), ofMul_pow, map_nsmul]

/- English proof (translation)
Rewrite using `[eq_top_iff]`. Introduce `x _`. Establish `h1 : degLK p K K = 1`. Establish `h2 : subG p K K = ⊤` using `eq_top_iff.2 fun σ _ x hx => σ.commutes ⟨x, hx⟩`. Use `show (subG p K K).index = 1`.

Rewrite using `[h2, Subgroup.index_top]`. Establish `h3` using `pow_degree_mem_normGroup (le_refl K) x`. Rewrite `h3` using `[h1, pow_one]`. Then use the resulting hypothesis.
-/
theorem normGroup_self_eq_top : normGrp p K K = ⊤ := by
  rw [eq_top_iff]
  intro x _
  have h1 : degLK p K K = 1 := by
    have h2 : subG p K K = ⊤ := eq_top_iff.2 fun σ _ x hx => σ.commutes ⟨x, hx⟩
    show (subG p K K).index = 1
    rw [h2, Subgroup.index_top]
  have h3 := pow_degree_mem_normGroup (le_refl K) x
  rwa [h1, pow_one] at h3

end ReciprocityTheory.DiscreteGroups.LocalClassField

import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.TorusAtData
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.FundamentalDomainPointBound
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.ModerateCoefficientPositivity
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.QuadraticCoefficientForms
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.LemmaNA
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.PointwiseNormSqPullbackTensorEqProd
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExistsNeZeroOnCoset

open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.I2
open scoped TensorProduct nonZeroDivisors

namespace GlobalTheory.TupleSumPos

/- English proof (translation)
Establish `: Module.FinitePresentation O M` using `Module.finitePresentation_of_projective O M`. Establish `key : ∀ (K : Type) [Field K] [Algebra O K], Module.finrank K (K ⊗[O] M) = Module.rankAtStalk M (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum O)` using `fun K _ _ => by`. Establish `h` using `Module.rankAtStalk_baseChange (R := O) (M := M) (S := K) ⟨⊥, Ideal.isPrime_bot⟩`. Rewrite `h` using `[Module.rankAtStalk_eq_finrank_of_free]`. Conclude with `h.trans ((Module.isLocallyConstant_rankAtStalk (R := O) (M := M)).apply_eq_of_preconnectedSpace _ _)`.

Rewrite using `[key k, ← key (FractionRing O), (TensorProduct.isBaseChange O M (FractionRing O)).finrank_eq]`.
-/
theorem finrank_fibre (O M k : Type) [CommRing O] [IsDomain O] [AddCommGroup M] [Module O M]
    [Module.Finite O M] [Module.Projective O M] [Field k] [Algebra O k] :
    Module.finrank k (k ⊗[O] M) = Module.finrank O M := by
  have : Module.FinitePresentation O M := Module.finitePresentation_of_projective O M
  have key : ∀ (K : Type) [Field K] [Algebra O K], Module.finrank K (K ⊗[O] M) =
      Module.rankAtStalk M (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum O) := fun K _ _ => by
    have h := Module.rankAtStalk_baseChange (R := O) (M := M) (S := K) ⟨⊥, Ideal.isPrime_bot⟩
    rw [Module.rankAtStalk_eq_finrank_of_free] at h
    exact h.trans ((Module.isLocallyConstant_rankAtStalk (R := O) (M := M)).apply_eq_of_preconnectedSpace _ _)
  rw [key k, ← key (FractionRing O), (TensorProduct.isBaseChange O M (FractionRing O)).finrank_eq]

/- English proof (translation)
Use `set I : Ideal O := Ideal.span {m} with hI`. Establish `: Finite (Ideal (O ⧸ I))` using `Finite.of_injective _ SetLike.coe_injective`. Establish `: Finite (MaximalSpectrum (O ⧸ I))` using `Finite.of_injective (fun P => P.asIdeal) fun _ _ h => MaximalSpectrum.ext h`. Take `⟨B⟩` from `Module.nonempty_basis_of_flat_of_finrank_eq (O ⧸ I) ((O ⧸ I) ⊗[O] M) r fun P => by`. Set `` to `P.isMaximal`.

Set `` to `Ideal.Quotient.field P.asIdeal`. Rewrite using `[(TensorProduct.AlgebraTensorModule.cancelBaseChange O (O ⧸ I) ((O ⧸ I) ⧸ P.1) ((O ⧸ I) ⧸ P.1) M).finrank_eq, finrank_fibre, hr]`. Establish `hs : Function.Surjective (TensorProduct.mk O (O ⧸ I) M 1)` using `TensorProduct.mk_surjective O M (O ⧸ I) Ideal.Quotient.mk_surjective`. Establish `hk : ∀ x : M, TensorProduct.mk O (O ⧸ I) M 1 x = 0 ↔ ∃ y, x = m • y` using `fun x => by`. Rewrite using `[← (TensorProduct.quotTensorEquivQuotSMul M I).map_eq_zero_iff, TensorProduct.mk_apply, TensorProduct.quotTensorEquivQuotSMul_mk_one_tmul, Submodule.Quotient.mk_eq_zero, hI, Submodule.ideal_span_singleton_smul, Submodule.mem_smul_pointwise_iff_exists]`.

Conclude with `⟨fun ⟨y, _, h⟩ => ⟨y, h.symm⟩, fun ⟨y, h⟩ => ⟨y, trivial, h.symm⟩⟩`. Use `choose e he using fun k => hs (B k)`. Establish `hc : ∀ c : Fin r → O, TensorProduct.mk O (O ⧸ I) M 1 (∑ k, c k • e k) = ∑ k, Ideal.Quotient.mk I (c k) • B k` using `fun c => by`. Rewrite using `[map_sum]`. Use `Finset.sum_congr rfl fun k _ => ?_` and prove the remaining obligations.

Rewrite using `[map_smul, he, ← Ideal.Quotient.algebraMap_eq, algebraMap_smul]`. Use `⟨e, fun x => ?_⟩` and prove the remaining obligations. Use `choose c hc' using fun k => Ideal.Quotient.mk_surjective (B.repr (TensorProduct.mk O (O ⧸ I) M 1 x) k)`. Take `⟨y, hy⟩` from `(hk (x - ∑ k, c k • e k)).1 (by`. Rewrite using `[map_sub, hc]`.

Simplify using `only [hc']`. Rewrite using `[B.sum_repr, sub_self])`. Conclude with `⟨c, y, by rw [← hy]; abel⟩`.
-/
theorem exists_generators_mod (O M : Type) [CommRing O] [IsDomain O] [AddCommGroup M] [Module O M]
    [Module.Finite O M] [Module.Projective O M] (m : O) [Finite (O ⧸ Ideal.span {m})] (r : ℕ)
    (hr : Module.finrank O M = r) :
    ∃ e : Fin r → M, ∀ x : M, ∃ (c : Fin r → O) (y : M), x = ∑ k, c k • e k + m • y := by
  set I : Ideal O := Ideal.span {m} with hI
  have : Finite (Ideal (O ⧸ I)) := Finite.of_injective _ SetLike.coe_injective
  have : Finite (MaximalSpectrum (O ⧸ I)) :=
    Finite.of_injective (fun P => P.asIdeal) fun _ _ h => MaximalSpectrum.ext h
  obtain ⟨B⟩ := Module.nonempty_basis_of_flat_of_finrank_eq (O ⧸ I) ((O ⧸ I) ⊗[O] M) r fun P => by
    let := P.isMaximal
    let := Ideal.Quotient.field P.asIdeal
    rw [(TensorProduct.AlgebraTensorModule.cancelBaseChange O (O ⧸ I) ((O ⧸ I) ⧸ P.1) ((O ⧸ I) ⧸ P.1) M).finrank_eq,
      finrank_fibre, hr]
  have hs : Function.Surjective (TensorProduct.mk O (O ⧸ I) M 1) :=
    TensorProduct.mk_surjective O M (O ⧸ I) Ideal.Quotient.mk_surjective
  have hk : ∀ x : M, TensorProduct.mk O (O ⧸ I) M 1 x = 0 ↔ ∃ y, x = m • y := fun x => by
    rw [← (TensorProduct.quotTensorEquivQuotSMul M I).map_eq_zero_iff, TensorProduct.mk_apply,
      TensorProduct.quotTensorEquivQuotSMul_mk_one_tmul, Submodule.Quotient.mk_eq_zero, hI,
      Submodule.ideal_span_singleton_smul, Submodule.mem_smul_pointwise_iff_exists]
    exact ⟨fun ⟨y, _, h⟩ => ⟨y, h.symm⟩, fun ⟨y, h⟩ => ⟨y, trivial, h.symm⟩⟩
  choose e he using fun k => hs (B k)
  have hc : ∀ c : Fin r → O, TensorProduct.mk O (O ⧸ I) M 1 (∑ k, c k • e k) =
      ∑ k, Ideal.Quotient.mk I (c k) • B k := fun c => by
    rw [map_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [map_smul, he, ← Ideal.Quotient.algebraMap_eq, algebraMap_smul]
  refine ⟨e, fun x => ?_⟩
  choose c hc' using fun k => Ideal.Quotient.mk_surjective (B.repr (TensorProduct.mk O (O ⧸ I) M 1 x) k)
  obtain ⟨y, hy⟩ := (hk (x - ∑ k, c k • e k)).1 (by
    rw [map_sub, hc]
    simp only [hc']
    rw [B.sum_repr, sub_self])
  exact ⟨c, y, by rw [← hy]; abel⟩

variable {E : Type} [Field E] [NumberField E]

/- English proof (translation)
Establish `: IsLocalizedModule (𝓞 E)⁰ Λ.subtype` using `{ map_units := fun s => by`. Use `isLocalizedModule_id (𝓞 E)⁰ (Fin n → E) E` as an intermediate fact. Conclude with `IsLocalizedModule.map_units (S := (𝓞 E)⁰) (LinearMap.id : (Fin n → E) →ₗ[𝓞 E] _) s`. Use `surj := fun y => by`. Establish `hy : y ∈ Submodule.span E (Λ : Set (Fin n → E))` using `h ▸ Submodule.mem_top`.

Take `⟨t, ht⟩` from `multiple_mem_span_of_mem_localization_span (𝓞 E)⁰ E _ y hy`. Rewrite `ht` using `[Submodule.span_eq]`. Conclude with `⟨(⟨_, ht⟩, t), rfl⟩`. Use `exists_of_eq := fun h => ⟨1, by simpa using h⟩ }`. Establish `: Module.Finite (𝓞 E) Λ` using `Module.Finite.iff_fg.mpr hfg`.

Establish `: Module.FinitePresentation (𝓞 E) Λ` using `Module.finitePresentation_of_finite _ _`. Establish `: Module.Projective (𝓞 E) Λ` using `Module.Flat.projective_of_finitePresentation`. Establish `: Finite (𝓞 E ⧸ Ideal.span {(5 : 𝓞 E)})` using `Ideal.finiteQuotientOfFreeOfNeBot _ (by simp)`. Use `exists_generators_mod (𝓞 E) Λ 5 n ?_` and prove the remaining obligations. Rewrite using `[← IsLocalizedModule.finrank_eq (𝓞 E)⁰ Λ.subtype le_rfl, ← IsLocalization.finrank_eq E (𝓞 E)⁰ le_rfl]`.

Simplify using the standard rewrite rules.
-/
theorem exists_generators_lattice {n : ℕ} (Λ : Submodule (𝓞 E) (Fin n → E)) (hfg : Λ.FG)
    (h : Submodule.span E (Λ : Set (Fin n → E)) = ⊤) :
    ∃ e : Fin n → Λ, ∀ x : Λ, ∃ (c : Fin n → 𝓞 E) (y : Λ), x = ∑ k, c k • e k + (5 : 𝓞 E) • y := by
  have : IsLocalizedModule (𝓞 E)⁰ Λ.subtype :=
    { map_units := fun s => by
        have := isLocalizedModule_id (𝓞 E)⁰ (Fin n → E) E
        exact IsLocalizedModule.map_units (S := (𝓞 E)⁰) (LinearMap.id : (Fin n → E) →ₗ[𝓞 E] _) s
      surj := fun y => by
        have hy : y ∈ Submodule.span E (Λ : Set (Fin n → E)) := h ▸ Submodule.mem_top
        obtain ⟨t, ht⟩ := multiple_mem_span_of_mem_localization_span (𝓞 E)⁰ E _ y hy
        rw [Submodule.span_eq] at ht
        exact ⟨(⟨_, ht⟩, t), rfl⟩
      exists_of_eq := fun h => ⟨1, by simpa using h⟩ }
  have : Module.Finite (𝓞 E) Λ := Module.Finite.iff_fg.mpr hfg
  have : Module.FinitePresentation (𝓞 E) Λ := Module.finitePresentation_of_finite _ _
  have : Module.Projective (𝓞 E) Λ := Module.Flat.projective_of_finitePresentation
  have : Finite (𝓞 E ⧸ Ideal.span {(5 : 𝓞 E)}) :=
    Ideal.finiteQuotientOfFreeOfNeBot _ (by simp)
  refine exists_generators_mod (𝓞 E) Λ 5 n ?_
  rw [← IsLocalizedModule.finrank_eq (𝓞 E)⁰ Λ.subtype le_rfl,
    ← IsLocalization.finrank_eq E (𝓞 E)⁰ le_rfl]
  simp

/- English proof (translation)
Use extensionality with `i`. Simplify using `[act, mul_add]`.
-/
theorem act_add_vec {dim : (E →+* ℂ) → ℕ} (α : 𝓞 E) (v w : Vsp dim) :
    act α (v + w) = act α v + act α w := by
  ext i; simp [act, mul_add]

/- English proof (translation)
Use extensionality with `i`. Simplify using `[act]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem act_smul_vec {dim : (E →+* ℂ) → ℕ} (α : 𝓞 E) (c : ℂ) (v : Vsp dim) :
    act α (c • v) = c • act α v := by
  ext i; simp [act]; ring

/- English proof (translation)
Use `T.L.nsmul_mem hy 5` as an intermediate fact. Rewrite `this` using `[← Nat.cast_smul_eq_nsmul ℂ, Nat.cast_ofNat]`. Then use the resulting hypothesis.
-/
theorem five_smul_mem (T : PT E) {y : Vsp T.dim} (hy : y ∈ T.L) : (5 : ℂ) • y ∈ T.L := by
  have := T.L.nsmul_mem hy 5
  rwa [← Nat.cast_smul_eq_nsmul ℂ, Nat.cast_ofNat] at this

/- English proof (translation)
Establish `hb` using `(ZSpan.fundamentalDomain_isBounded T.b).smul₀ ((5 : ℂ) ^ 2)`. Establish `hf` using `ZSpan.setFinite_inter T.b hb`. Use `Set.Finite.of_finite_image (f := fun v => ((5 : ℂ) ^ 2) • v) (hf.subset ?_) ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨v, ⟨h1, h2⟩, rfl⟩`. Conclude with `⟨Set.smul_mem_smul_set h1, h2⟩`.

Conclude with `(smul_right_injective _ (by norm_num)).injOn`.
-/
theorem finite_torsion (T : PT E) :
    {v : Vsp T.dim | v ∈ ZSpan.fundamentalDomain T.b ∧ ((5 : ℂ) ^ 2) • v ∈ T.L}.Finite := by
  have hb := (ZSpan.fundamentalDomain_isBounded T.b).smul₀ ((5 : ℂ) ^ 2)
  have hf := ZSpan.setFinite_inter T.b hb
  refine Set.Finite.of_finite_image (f := fun v => ((5 : ℂ) ^ 2) • v) (hf.subset ?_) ?_
  · rintro _ ⟨v, ⟨h1, h2⟩, rfl⟩
    exact ⟨Set.smul_mem_smul_set h1, h2⟩
  · exact (smul_right_injective _ (by norm_num)).injOn

variable [IsCMField E]

/- English proof (translation)
Take `⟨τ⟩ : Nonempty X.Ψ` from `Fintype.card_pos_iff.1 (QuadraticCoefficientForms.card_Psi_pos X)`. Establish `hr : A.T.r = r`. Establish `h1` using `A.T.dim_conj τ.1`. Rewrite `h1` using `[A.dim_pos, A.dim_neg]`. Use `X.p0_le` as an intermediate fact.

Use linear arithmetic over natural numbers and integers. Rewrite using `[hr]`. Take `⟨e, he⟩` from `exists_generators_lattice X.Λ X.Λ_fg X.Λ_span`. Use `⟨fun j => A.φ (e j), fun j => (A.lat _).2 ⟨_, (e j).2, rfl⟩, fun v hv => ?_⟩` and prove the remaining obligations. Take `⟨u, hu, rfl⟩` from `(A.lat v).1 hv`.

Take `⟨c, y, h⟩` from `he ⟨u, hu⟩`. Use `⟨c, A.φ y, (A.lat _).2 ⟨_, y.2, rfl⟩, ?_⟩` and prove the remaining obligations. Establish `h2 : u = ∑ k, (c k : E) • (e k : Fin r → E) + 5 • (y : Fin r → E)`. Use `congrArg Subtype.val h` as an intermediate fact. Simplify using `only [Submodule.coe_add, Submodule.coe_sum, Submodule.coe_smul] at this`.

Rewrite using `[this, ← Nat.cast_smul_eq_nsmul (𝓞 E), Nat.cast_ofNat]`. Both sides reduce to the same expression. Rewrite using `[h2, map_add, map_sum, map_nsmul, ← Nat.cast_smul_eq_nsmul ℂ, Nat.cast_ofNat]`. Simplify using `only [A.act_eq]`.
-/
theorem exists_generators_period {r : ℕ} {X : Data E r} {x : Frame X.Ψ r} (A : TorusAt X x) :
    ∃ e : Fin A.T.r → Vsp A.T.dim, (∀ j, e j ∈ A.T.L) ∧ ∀ v ∈ A.T.L,
      ∃ c : Fin A.T.r → 𝓞 E, ∃ y ∈ A.T.L, v = ∑ j, act (c j) (e j) + (5 : ℂ) • y := by
  obtain ⟨τ⟩ : Nonempty X.Ψ := Fintype.card_pos_iff.1 (QuadraticCoefficientForms.card_Psi_pos X)
  have hr : A.T.r = r := by
    have h1 := A.T.dim_conj τ.1
    rw [A.dim_pos, A.dim_neg] at h1
    have := X.p0_le
    omega
  rw [hr]
  obtain ⟨e, he⟩ := exists_generators_lattice X.Λ X.Λ_fg X.Λ_span
  refine ⟨fun j => A.φ (e j), fun j => (A.lat _).2 ⟨_, (e j).2, rfl⟩, fun v hv => ?_⟩
  obtain ⟨u, hu, rfl⟩ := (A.lat v).1 hv
  obtain ⟨c, y, h⟩ := he ⟨u, hu⟩
  refine ⟨c, A.φ y, (A.lat _).2 ⟨_, y.2, rfl⟩, ?_⟩
  have h2 : u = ∑ k, (c k : E) • (e k : Fin r → E) + 5 • (y : Fin r → E) := by
    have := congrArg Subtype.val h
    simp only [Submodule.coe_add, Submodule.coe_sum, Submodule.coe_smul] at this
    rw [this, ← Nat.cast_smul_eq_nsmul (𝓞 E), Nat.cast_ofNat]
    rfl
  rw [h2, map_add, map_sum, map_nsmul, ← Nat.cast_smul_eq_nsmul ℂ, Nat.cast_ofNat]
  simp only [A.act_eq]

/- English proof (translation)
Introduce `E _ _ _ r X x A`. Use `set S := {a : Fin A.T.r → Vsp A.T.dim | (∀ j, a j ∈ ZSpan.fundamentalDomain A.T.b) ∧ (∀ j, ((5 : ℂ) ^ 2) • a j ∈ A.T.L) ∧ ∀ x ∈ A.T.L, ∃ c : Fin A.T.r → 𝓞 E, ∃ y ∈ A.T.L, x = ∑ j, act (c j) (((5 : ℂ) ^ 2) • a j) + (5 : ℂ) • y} with hS`. Establish `hfin : S.Finite` using `(Set.Finite.pi' fun _ : Fin A.T.r => finite_torsion A.T).subset fun a ha j => ⟨ha.1 j, ha.2.1 j⟩`. Establish `hl : 0 < A.T.l2 1 A.s` using `GlobalTheory.ThetaBound.l2_pos_of_mem_sec_of_ne_zero A.T le_rfl A.s_mem A.s_ne`. Rewrite using `[finsum_mem_eq_finite_toFinset_sum _ hfin]`.

Take `⟨e, heL, he⟩` from `exists_generators_period A`. Use `choose y hyL hy using fun j => GlobalTheory.TorsionCoset.exists_ne_zero_on_coset E A.T A.s A.s_mem A.s_ne 5 (by norm_num) (((5 : ℂ) ^ 2)⁻¹ • e j)`. Simplify using `only [Nat.cast_ofNat] at hy`. Use `set w : Fin A.T.r → Vsp A.T.dim := fun j => ((5 : ℂ) ^ 2)⁻¹ • e j + (5 : ℂ)⁻¹ • y j with hw`. Use `set z : Fin A.T.r → Vsp A.T.dim := fun j => y j - (5 : ℂ) • (ZSpan.floor A.T.b (w j) : Vsp A.T.dim) with hz`.

Establish `hzL : ∀ j, z j ∈ A.T.L` using `fun j => A.T.L.sub_mem (hyL j) (five_smul_mem A.T (ZSpan.floor A.T.b (w j)).2)`. Establish `h25 : ∀ j, ((5 : ℂ) ^ 2) • ZSpan.fract A.T.b (w j) = e j + (5 : ℂ) • z j` using `fun j => by`. Rewrite using `[ZSpan.fract_apply]`. Simplify using `only [hz]`. Generalize the expression as in `(ZSpan.floor A.T.b (w j) : Vsp A.T.dim) = f`.

Simplify using `only [hw]`. Apply the tactic sequence `match_scalars <;> norm_num`. Use `Finset.sum_pos' (fun a _ => Finset.prod_nonneg fun b _ => div_nonneg ?_ hl.le) ⟨fun j => ZSpan.fract A.T.b (w j), hfin.mem_toFinset.2 ⟨fun j => ?_, fun j => ?_, fun v hv => ?_⟩, Finset.prod_pos fun j _ => div_pos ?_ hl⟩` and prove the remaining obligations. Unfold `PT.ptN2`. Check the signs of the components of the expression.

Conclude with `ZSpan.fract_mem_fundamentalDomain _ _`. Rewrite using `[h25]`. Conclude with `A.T.L.add_mem (heL j) (five_smul_mem A.T (hzL j))`. Take `⟨c, u, hu, h⟩` from `he v hv`. Use `⟨c, u - ∑ j, act (c j) (z j), A.T.L.sub_mem hu (A.T.L.sum_mem fun j _ => A.T.stable _ _ (hzL j)), ?_⟩` and prove the remaining obligations.

Simplify using `only [h25, act_add_vec, act_smul_vec, Finset.sum_add_distrib, ← Finset.smul_sum, smul_sub]`. Rewrite using `[h]`. Normalize the expressions using the abelian group laws. Establish `hp` using `pointwiseNormSq_add_period A.T A.s_mem (γ := fun _ => (ZSpan.floor A.T.b (w j) : Vsp A.T.dim)) (fun _ => (ZSpan.floor A.T.b (w j)).2) (fun _ => ZSpan.fract A.T.b (w j))`. Establish `e1 : ((fun _ : Fin 1 => ZSpan.fract A.T.b (w j)) + fun _ => (ZSpan.floor A.T.b (w j) : Vsp A.T.dim)) = fun _ => w j`.

Use function extensionality and compare the values at `k`. Simplify using `[ZSpan.fract_apply]`. Rewrite using `[← hp, e1]`. Unfold `PT.ptN2`. Conclude with `mul_pos (pow_pos (norm_pos_iff.2 (hy j)) 2) (Real.exp_pos _)`.
-/
theorem tuple_sum_pos : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : DataX E r) (x : Frame X.Ψ r) (A : TorusAt X.toData x), 0 < ∑ᶠ (a : Fin A.T.r → Vsp A.T.dim) (_ : a ∈ {a : Fin A.T.r → Vsp A.T.dim | (∀ j, a j ∈ ZSpan.fundamentalDomain A.T.b) ∧ (∀ j, ((5 : ℂ) ^ 2) • a j ∈ A.T.L) ∧ ∀ x ∈ A.T.L, ∃ c : Fin A.T.r → 𝓞 E, ∃ y ∈ A.T.L, x = ∑ j, act (c j) (((5 : ℂ) ^ 2) • a j) + (5 : ℂ) • y}), ∏ b, A.T.ptN2 1 A.s (fun _ => a b) / A.T.l2 1 A.s := by
  intro E _ _ _ r X x A
  set S := {a : Fin A.T.r → Vsp A.T.dim | (∀ j, a j ∈ ZSpan.fundamentalDomain A.T.b) ∧ (∀ j, ((5 : ℂ) ^ 2) • a j ∈ A.T.L) ∧ ∀ x ∈ A.T.L, ∃ c : Fin A.T.r → 𝓞 E, ∃ y ∈ A.T.L, x = ∑ j, act (c j) (((5 : ℂ) ^ 2) • a j) + (5 : ℂ) • y} with hS
  have hfin : S.Finite :=
    (Set.Finite.pi' fun _ : Fin A.T.r => finite_torsion A.T).subset fun a ha j => ⟨ha.1 j, ha.2.1 j⟩
  have hl : 0 < A.T.l2 1 A.s := GlobalTheory.ThetaBound.l2_pos_of_mem_sec_of_ne_zero A.T le_rfl A.s_mem A.s_ne
  rw [finsum_mem_eq_finite_toFinset_sum _ hfin]
  obtain ⟨e, heL, he⟩ := exists_generators_period A
  choose y hyL hy using fun j =>
    GlobalTheory.TorsionCoset.exists_ne_zero_on_coset E A.T A.s A.s_mem A.s_ne 5 (by norm_num) (((5 : ℂ) ^ 2)⁻¹ • e j)
  simp only [Nat.cast_ofNat] at hy
  set w : Fin A.T.r → Vsp A.T.dim := fun j => ((5 : ℂ) ^ 2)⁻¹ • e j + (5 : ℂ)⁻¹ • y j with hw
  set z : Fin A.T.r → Vsp A.T.dim := fun j =>
    y j - (5 : ℂ) • (ZSpan.floor A.T.b (w j) : Vsp A.T.dim) with hz
  have hzL : ∀ j, z j ∈ A.T.L := fun j =>
    A.T.L.sub_mem (hyL j) (five_smul_mem A.T (ZSpan.floor A.T.b (w j)).2)
  have h25 : ∀ j, ((5 : ℂ) ^ 2) • ZSpan.fract A.T.b (w j) = e j + (5 : ℂ) • z j := fun j => by
    rw [ZSpan.fract_apply]
    simp only [hz]
    generalize (ZSpan.floor A.T.b (w j) : Vsp A.T.dim) = f
    simp only [hw]
    match_scalars <;> norm_num
  refine Finset.sum_pos' (fun a _ => Finset.prod_nonneg fun b _ => div_nonneg ?_ hl.le)
    ⟨fun j => ZSpan.fract A.T.b (w j), hfin.mem_toFinset.2 ⟨fun j => ?_, fun j => ?_, fun v hv => ?_⟩,
      Finset.prod_pos fun j _ => div_pos ?_ hl⟩
  · unfold PT.ptN2; positivity
  · exact ZSpan.fract_mem_fundamentalDomain _ _
  · rw [h25]; exact A.T.L.add_mem (heL j) (five_smul_mem A.T (hzL j))
  · obtain ⟨c, u, hu, h⟩ := he v hv
    refine ⟨c, u - ∑ j, act (c j) (z j),
      A.T.L.sub_mem hu (A.T.L.sum_mem fun j _ => A.T.stable _ _ (hzL j)), ?_⟩
    simp only [h25, act_add_vec, act_smul_vec, Finset.sum_add_distrib, ← Finset.smul_sum, smul_sub]
    rw [h]; abel
  · have hp := pointwiseNormSq_add_period A.T A.s_mem
      (γ := fun _ => (ZSpan.floor A.T.b (w j) : Vsp A.T.dim))
      (fun _ => (ZSpan.floor A.T.b (w j)).2) (fun _ => ZSpan.fract A.T.b (w j))
    have e1 : ((fun _ : Fin 1 => ZSpan.fract A.T.b (w j)) +
        fun _ => (ZSpan.floor A.T.b (w j) : Vsp A.T.dim)) = fun _ => w j := by
      funext k; simp [ZSpan.fract_apply]
    rw [← hp, e1]
    unfold PT.ptN2
    exact mul_pos (pow_pos (norm_pos_iff.2 (hy j)) 2) (Real.exp_pos _)

end GlobalTheory.TupleSumPos

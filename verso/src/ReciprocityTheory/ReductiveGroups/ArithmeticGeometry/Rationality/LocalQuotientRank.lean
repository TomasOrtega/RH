import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.Rationality.QCoreH
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.Rationality.FreeQuotPf

namespace ReciprocityTheory.ChartRestriction.G.FreeQuotientRank.LocalQuotientRank

open NumberField Module
open scoped TensorProduct

section
variable {R F X : Type} [CommRing R] [IsDomain R] [Field F] [Algebra R F]
    [IsFractionRing R F] [AddCommGroup X] [Module F X] [Module R X] [IsScalarTower R F X]

/- English proof (translation)
Establish `: Module.Finite R M₁` using `Module.Finite.iff_fg.mpr hM₁`. Establish `ne : ∀ r : R, r ≠ 0 → algebraMap R F r ≠ 0` using `fun r hr => (map_ne_zero_iff _ (IsFractionRing.injective R F)).mpr hr`. Establish `hspan : Submodule.span F ((M₁ ⊓ N.restrictScalars R : Submodule R X) : Set X) = Submodule.span F (M₁ : Set X) ⊓ N`. Apply `le_antisymm` to reduce the goal to its premises. Rewrite using `[Submodule.span_le]`.

Introduce `x hx`. Take `⟨hx1, hx2⟩` from `Submodule.mem_inf.mp hx`. Conclude with `Submodule.mem_inf.mpr ⟨Submodule.subset_span hx1, hx2⟩`. Introduce `x hx`. Take `⟨hx1, hx2⟩` from `Submodule.mem_inf.mp hx`.

Take `⟨d, hd, hd'⟩` from `freeQuot_exists_smul_mem M₁ hx1`. Establish `hN : d • x ∈ N`. Rewrite using `[← algebraMap_smul F d x]`. Conclude with `N.smul_mem _ hx2`. Establish `hmem : d • x ∈ Submodule.span F ((M₁ ⊓ N.restrictScalars R : Submodule R X) : Set X)` using `Submodule.subset_span (Submodule.mem_inf.mpr ⟨hd', hN⟩)`.

Rewrite `hmem` using `[← algebraMap_smul F d x]`. Establish `h2` using `Submodule.smul_mem _ (algebraMap R F d)⁻¹ hmem`. Rewrite `h2` using `[smul_smul, inv_mul_cancel₀ (ne d hd), one_smul]`. Then use the resulting hypothesis. Establish `hrn` using `Submodule.finrank_quotient_add_finrank ((N.restrictScalars R).comap M₁.subtype)`. Establish `hM : finrank R M₁ = finrank F (Submodule.span F (M₁ : Set X))` using `congrArg Cardinal.toNat (freeQuot_rank_span M₁)`.

Establish `hP : finrank R ((N.restrictScalars R).comap M₁.subtype) = finrank F ↥(Submodule.span F (M₁ : Set X) ⊓ N)`. Rewrite using `[(Submodule.equivMapOfInjective M₁.subtype M₁.injective_subtype ((N.restrictScalars R).comap M₁.subtype)).finrank_eq, Submodule.map_comap_subtype, ← hspan]`. Conclude with `congrArg Cardinal.toNat (freeQuot_rank_span _)`. Rewrite using `[← hP, ← hM]`. Conclude with `hrn`.
-/
theorem rank_quot (M₁ : Submodule R X) (hM₁ : M₁.FG) (N : Submodule F X) :
    Module.finrank R (M₁ ⧸ (N.restrictScalars R).comap M₁.subtype) +
        Module.finrank F ↥(Submodule.span F (M₁ : Set X) ⊓ N) =
      Module.finrank F ↥(Submodule.span F (M₁ : Set X)) := by
  have : Module.Finite R M₁ := Module.Finite.iff_fg.mpr hM₁
  have ne : ∀ r : R, r ≠ 0 → algebraMap R F r ≠ 0 := fun r hr =>
    (map_ne_zero_iff _ (IsFractionRing.injective R F)).mpr hr
  have hspan : Submodule.span F ((M₁ ⊓ N.restrictScalars R : Submodule R X) : Set X) =
      Submodule.span F (M₁ : Set X) ⊓ N := by
    apply le_antisymm
    · rw [Submodule.span_le]
      intro x hx
      obtain ⟨hx1, hx2⟩ := Submodule.mem_inf.mp hx
      exact Submodule.mem_inf.mpr ⟨Submodule.subset_span hx1, hx2⟩
    · intro x hx
      obtain ⟨hx1, hx2⟩ := Submodule.mem_inf.mp hx
      obtain ⟨d, hd, hd'⟩ := freeQuot_exists_smul_mem M₁ hx1
      have hN : d • x ∈ N := by
        rw [← algebraMap_smul F d x]
        exact N.smul_mem _ hx2
      have hmem : d • x ∈ Submodule.span F
          ((M₁ ⊓ N.restrictScalars R : Submodule R X) : Set X) :=
        Submodule.subset_span (Submodule.mem_inf.mpr ⟨hd', hN⟩)
      rw [← algebraMap_smul F d x] at hmem
      have h2 := Submodule.smul_mem _ (algebraMap R F d)⁻¹ hmem
      rwa [smul_smul, inv_mul_cancel₀ (ne d hd), one_smul] at h2
  have hrn := Submodule.finrank_quotient_add_finrank ((N.restrictScalars R).comap M₁.subtype)
  have hM : finrank R M₁ = finrank F (Submodule.span F (M₁ : Set X)) :=
    congrArg Cardinal.toNat (freeQuot_rank_span M₁)
  have hP : finrank R ((N.restrictScalars R).comap M₁.subtype) =
      finrank F ↥(Submodule.span F (M₁ : Set X) ⊓ N) := by
    rw [(Submodule.equivMapOfInjective M₁.subtype M₁.injective_subtype
      ((N.restrictScalars R).comap M₁.subtype)).finrank_eq, Submodule.map_comap_subtype, ← hspan]
    exact congrArg Cardinal.toNat (freeQuot_rank_span _)
  rw [← hP, ← hM]
  exact hrn

end

section
variable {K K₁ V : Type} [Field K] [NumberField K] [Field K₁] [NumberField K₁] [Algebra K K₁]
    [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V]
    [IsScalarTower (𝓞 K) K V]

/- English proof (translation)
Establish `h` using `rank_quot (F := K) M hM W`. Rewrite `h` using `[hspan, top_inf_eq, finrank_top]`. Conclude with `h`.
-/
theorem rank_QuotMW (M : Submodule (𝓞 K) V) (hM : M.FG)
    (hspan : Submodule.span K (M : Set V) = ⊤) (W : Submodule K V) :
    Module.finrank (𝓞 K) (QuotMW M W) + Module.finrank K W = Module.finrank K V := by
  have h := rank_quot (F := K) M hM W
  rw [hspan, top_inf_eq, finrank_top] at h
  exact h

/- English proof (translation)
Rewrite using `[eq_top_iff]`. Introduce and unpack `t -`. Proceed by induction on `t using TensorProduct.induction_on with`. Consider the case `zero => exact Submodule.zero_mem _`. Consider the case `tmul a v`.

Establish `: a ⊗ₜ[K] v = a • ((1 : K₁) ⊗ₜ[K] v)`. Rewrite using `[TensorProduct.smul_tmul', smul_eq_mul, mul_one]`. Rewrite using `[this]`. Conclude with `Submodule.smul_mem _ _ (Submodule.subset_span ⟨v, rfl⟩)`. Consider the case `add x y hx hy => exact Submodule.add_mem _ hx hy`.
-/
theorem span_tmul_one : Submodule.span K₁ (Set.range fun v : V => (1 : K₁) ⊗ₜ[K] v) = ⊤ := by
  rw [eq_top_iff]
  rintro t -
  induction t using TensorProduct.induction_on with
  | zero => exact Submodule.zero_mem _
  | tmul a v =>
    have : a ⊗ₜ[K] v = a • ((1 : K₁) ⊗ₜ[K] v) := by
      rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    rw [this]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨v, rfl⟩)
  | add x y hx hy => exact Submodule.add_mem _ hx hy

/- English proof (translation)
Proceed by induction on `hy using Submodule.span_induction with`. Consider the case `mem y hy => obtain ⟨j, rfl⟩ := hy`. Conclude with `Submodule.subset_span ⟨j, rfl⟩`. Consider the case `zero => rw [TensorProduct.tmul_zero]`. Conclude with `Submodule.zero_mem _`.

Consider the case `add a b _ _ ha hb => rw [TensorProduct.tmul_add]`. Conclude with `Submodule.add_mem _ ha hb`. Consider the case `smul r a _ ha`. Rewrite using `[TensorProduct.tmul_smul, ← algebraMap_smul K₁ r]`. Conclude with `Submodule.smul_mem _ _ ha`.
-/
theorem tmul_mem_span {ι : Type*} (g : ι → V) {y : V} (hy : y ∈ Submodule.span K (Set.range g)) :
    (1 : K₁) ⊗ₜ[K] y ∈ Submodule.span K₁ (Set.range fun j => (1 : K₁) ⊗ₜ[K] g j) := by
  induction hy using Submodule.span_induction with
  | mem y hy => obtain ⟨j, rfl⟩ := hy; exact Submodule.subset_span ⟨j, rfl⟩
  | zero => rw [TensorProduct.tmul_zero]; exact Submodule.zero_mem _
  | add a b _ _ ha hb => rw [TensorProduct.tmul_add]; exact Submodule.add_mem _ ha hb
  | smul r a _ ha =>
    rw [TensorProduct.tmul_smul, ← algebraMap_smul K₁ r]
    exact Submodule.smul_mem _ _ ha

/- English proof (translation)
Establish `hρ` using `rank_QuotMW M hM hspan W`. Use `set P := Submodule.span K₁ ((fun a : V => (1 : K₁) ⊗ₜ[K] a) '' (W : Set V)) with hPdef`. Set `e : Fin (finrank (𝓞 K) (QuotMW M W)) → K₁ ⊗[K] V` to `fun j => (1 : K₁) ⊗ₜ[K] ((θ j : M) : V)`. Establish `hP : finrank K₁ P ≤ finrank K W`. Set `B` to `Module.finBasis K W`.

Establish `hle : P ≤ Submodule.span K₁ (Set.range fun k => (1 : K₁) ⊗ₜ[K] ((B k : W) : V))`. Rewrite using `[hPdef, Submodule.span_le]`. Introduce and unpack `_ ⟨a, ha, rfl⟩`. Apply `tmul_mem_span` to reduce the goal to its premises. Establish `h1 : (⟨a, ha⟩ : W) ∈ Submodule.span K (Set.range B)`.

Rewrite using `[B.span_eq]`. Discharge the goal by the elementary cases of `trivial`. Establish `h2` using `Submodule.apply_mem_span_image_of_mem_span W.subtype h1`. Rewrite `h2` using `[← Set.range_comp]`. Conclude with `h2`.

Combine the equalities or inequalities in the displayed calculation. Establish `htop : Submodule.span K₁ (Set.range e) ⊔ P = ⊤`. Rewrite using `[eq_top_iff, ← span_tmul_one (K := K) (K₁ := K₁) (V := V), Submodule.span_le]`. Introduce and unpack `_ ⟨v, rfl⟩`. Establish `hv : v ∈ Submodule.span K (Set.range fun j => ((θ j : M) : V)) ⊔ W`.

Rewrite using `[hθ]`. Discharge the goal by the elementary cases of `trivial`. Take `⟨y, hy, z, hz, rfl⟩` from `Submodule.mem_sup.mp hv`. Use `show (1 : K₁) ⊗ₜ[K] (y + z) ∈ _`. Rewrite using `[TensorProduct.tmul_add]`.

Conclude with `Submodule.add_mem_sup (tmul_mem_span _ hy) (Submodule.subset_span ⟨z, hz, rfl⟩)`. Establish `hU : finrank K₁ (K₁ ⊗[K] V) = finrank K V` using `Module.finrank_baseChange`. Establish `hQ` using `Submodule.finrank_quotient_add_finrank P`. Set `f : Fin (finrank (𝓞 K) (QuotMW M W)) → (K₁ ⊗[K] V) ⧸ P` to `fun j => P.mkQ (e j)`. Establish `hfspan : ⊤ ≤ Submodule.span K₁ (Set.range f)`.

Establish `h1 : Set.range f = P.mkQ '' Set.range e` using `Set.range_comp _ _`. Rewrite using `[h1, Submodule.span_image, top_le_iff, Submodule.map_mkQ_eq_top, sup_comm]`. Conclude with `htop`. Establish `hle : finrank K₁ ((K₁ ⊗[K] V) ⧸ P) ≤ finrank (𝓞 K) (QuotMW M W)`. Establish `h1 : finrank K₁ (Submodule.span K₁ (Set.range f)) ≤ Fintype.card (Fin (finrank (𝓞 K) (QuotMW M W)))` using `finrank_range_le_card f`.

Rewrite `h1` using `[top_le_iff.mp hfspan, finrank_top, Fintype.card_fin]`. Conclude with `h1`. Use linear arithmetic over natural numbers and integers.
-/
theorem quot_finrank (M : Submodule (𝓞 K) V) (hM : M.FG)
    (hspan : Submodule.span K (M : Set V) = ⊤) (W : Submodule K V)
    (θ : Fin (finrank (𝓞 K) (QuotMW M W)) → M)
    (hθ : Submodule.span K (Set.range fun j => ((θ j : M) : V)) ⊔ W = ⊤) :
    finrank K₁ ((K₁ ⊗[K] V) ⧸
      Submodule.span K₁ ((fun a : V => (1 : K₁) ⊗ₜ[K] a) '' (W : Set V))) =
      finrank (𝓞 K) (QuotMW M W) := by
  have hρ := rank_QuotMW M hM hspan W
  set P := Submodule.span K₁ ((fun a : V => (1 : K₁) ⊗ₜ[K] a) '' (W : Set V)) with hPdef
  let e : Fin (finrank (𝓞 K) (QuotMW M W)) → K₁ ⊗[K] V :=
    fun j => (1 : K₁) ⊗ₜ[K] ((θ j : M) : V)
  have hP : finrank K₁ P ≤ finrank K W := by
    let B := Module.finBasis K W
    have hle : P ≤ Submodule.span K₁ (Set.range fun k => (1 : K₁) ⊗ₜ[K] ((B k : W) : V)) := by
      rw [hPdef, Submodule.span_le]
      rintro _ ⟨a, ha, rfl⟩
      apply tmul_mem_span
      have h1 : (⟨a, ha⟩ : W) ∈ Submodule.span K (Set.range B) := by
        rw [B.span_eq]; trivial
      have h2 := Submodule.apply_mem_span_image_of_mem_span W.subtype h1
      rw [← Set.range_comp] at h2
      exact h2
    calc finrank K₁ P ≤ _ := Submodule.finrank_mono hle
      _ ≤ Fintype.card (Fin (finrank K W)) := finrank_range_le_card _
      _ = finrank K W := Fintype.card_fin _
  have htop : Submodule.span K₁ (Set.range e) ⊔ P = ⊤ := by
    rw [eq_top_iff, ← span_tmul_one (K := K) (K₁ := K₁) (V := V), Submodule.span_le]
    rintro _ ⟨v, rfl⟩
    have hv : v ∈ Submodule.span K (Set.range fun j => ((θ j : M) : V)) ⊔ W := by
      rw [hθ]; trivial
    obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.mp hv
    show (1 : K₁) ⊗ₜ[K] (y + z) ∈ _
    rw [TensorProduct.tmul_add]
    exact Submodule.add_mem_sup (tmul_mem_span _ hy) (Submodule.subset_span ⟨z, hz, rfl⟩)
  have hU : finrank K₁ (K₁ ⊗[K] V) = finrank K V := Module.finrank_baseChange
  have hQ := Submodule.finrank_quotient_add_finrank P
  let f : Fin (finrank (𝓞 K) (QuotMW M W)) → (K₁ ⊗[K] V) ⧸ P := fun j => P.mkQ (e j)
  have hfspan : ⊤ ≤ Submodule.span K₁ (Set.range f) := by
    have h1 : Set.range f = P.mkQ '' Set.range e := Set.range_comp _ _
    rw [h1, Submodule.span_image, top_le_iff, Submodule.map_mkQ_eq_top, sup_comm]
    exact htop
  have hle : finrank K₁ ((K₁ ⊗[K] V) ⧸ P) ≤ finrank (𝓞 K) (QuotMW M W) := by
    have h1 : finrank K₁ (Submodule.span K₁ (Set.range f)) ≤
        Fintype.card (Fin (finrank (𝓞 K) (QuotMW M W))) := finrank_range_le_card f
    rw [top_le_iff.mp hfspan, finrank_top, Fintype.card_fin] at h1
    exact h1
  omega

/- English proof (translation)
Establish `hq` using `quot_finrank (K₁ := K₁) M hM hspan W θ hθ`. Use `set P := Submodule.span K₁ ((fun a : V => (1 : K₁) ⊗ₜ[K] a) '' (W : Set V)) with hPdef`. Set `e : Fin (finrank (𝓞 K) (QuotMW M W)) → K₁ ⊗[K] V` to `fun j => (1 : K₁) ⊗ₜ[K] ((θ j : M) : V)`. Establish `htop : Submodule.span K₁ (Set.range e) ⊔ P = ⊤`. Rewrite using `[eq_top_iff, ← span_tmul_one (K := K) (K₁ := K₁) (V := V), Submodule.span_le]`.

Introduce and unpack `_ ⟨v, rfl⟩`. Establish `hv : v ∈ Submodule.span K (Set.range fun j => ((θ j : M) : V)) ⊔ W`. Rewrite using `[hθ]`. Discharge the goal by the elementary cases of `trivial`. Take `⟨y, hy, z, hz, rfl⟩` from `Submodule.mem_sup.mp hv`.

Use `show (1 : K₁) ⊗ₜ[K] (y + z) ∈ _`. Rewrite using `[TensorProduct.tmul_add]`. Conclude with `Submodule.add_mem_sup (tmul_mem_span _ hy) (Submodule.subset_span ⟨z, hz, rfl⟩)`. Set `f : Fin (finrank (𝓞 K) (QuotMW M W)) → (K₁ ⊗[K] V) ⧸ P` to `fun j => P.mkQ (e j)`. Establish `hfspan : ⊤ ≤ Submodule.span K₁ (Set.range f)`.

Establish `h1 : Set.range f = P.mkQ '' Set.range e` using `Set.range_comp _ _`. Rewrite using `[h1, Submodule.span_image, top_le_iff, Submodule.map_mkQ_eq_top, sup_comm]`. Conclude with `htop`. Establish `hli : LinearIndependent K₁ f` using `linearIndependent_of_top_le_span_of_card_eq_finrank hfspan (by rw [Fintype.card_fin, hq])`. Introduce `hdet`.

Take `⟨a, ha0, ha⟩` from `Matrix.exists_mulVec_eq_zero_iff.mpr hdet`. Establish `hx : ∑ j, a j • e j ∈ P`. Rewrite using `[← hc]`. Introduce `i`. Establish `h1` using `congrFun ha i`.

Simplify using `only [Matrix.mulVec, dotProduct, Matrix.of_apply, Pi.zero_apply] at h1`. Rewrite using `[map_sum]`. Simplify using `only [map_smul, smul_eq_mul]`. Combine the equalities or inequalities in the displayed calculation. Establish `h2 : ∑ j, a j • f j = 0`.

Simplify using `only [f, ← map_smul, ← map_sum]`. Conclude with `(Submodule.Quotient.mk_eq_zero P).mpr hx`. Conclude with `ha0 (funext (Fintype.linearIndependent_iff.mp hli a h2))`.
-/
theorem detCT_ne_zero (M : Submodule (𝓞 K) V) (hM : M.FG)
    (hspan : Submodule.span K (M : Set V) = ⊤) (W : Submodule K V)
    (θ : Fin (finrank (𝓞 K) (QuotMW M W)) → M)
    (hθ : Submodule.span K (Set.range fun j => ((θ j : M) : V)) ⊔ W = ⊤)
    (c : Fin (finrank (𝓞 K) (QuotMW M W)) → Module.Dual K₁ (K₁ ⊗[K] V))
    (hc : ∀ x : K₁ ⊗[K] V, (∀ i, c i x = 0) ↔
      x ∈ Submodule.span K₁ ((fun a : V => (1 : K₁) ⊗ₜ[K] a) '' (W : Set V))) :
    detCT c θ ≠ 0 := by
  have hq := quot_finrank (K₁ := K₁) M hM hspan W θ hθ
  set P := Submodule.span K₁ ((fun a : V => (1 : K₁) ⊗ₜ[K] a) '' (W : Set V)) with hPdef
  let e : Fin (finrank (𝓞 K) (QuotMW M W)) → K₁ ⊗[K] V :=
    fun j => (1 : K₁) ⊗ₜ[K] ((θ j : M) : V)
  have htop : Submodule.span K₁ (Set.range e) ⊔ P = ⊤ := by
    rw [eq_top_iff, ← span_tmul_one (K := K) (K₁ := K₁) (V := V), Submodule.span_le]
    rintro _ ⟨v, rfl⟩
    have hv : v ∈ Submodule.span K (Set.range fun j => ((θ j : M) : V)) ⊔ W := by
      rw [hθ]; trivial
    obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.mp hv
    show (1 : K₁) ⊗ₜ[K] (y + z) ∈ _
    rw [TensorProduct.tmul_add]
    exact Submodule.add_mem_sup (tmul_mem_span _ hy) (Submodule.subset_span ⟨z, hz, rfl⟩)
  let f : Fin (finrank (𝓞 K) (QuotMW M W)) → (K₁ ⊗[K] V) ⧸ P := fun j => P.mkQ (e j)
  have hfspan : ⊤ ≤ Submodule.span K₁ (Set.range f) := by
    have h1 : Set.range f = P.mkQ '' Set.range e := Set.range_comp _ _
    rw [h1, Submodule.span_image, top_le_iff, Submodule.map_mkQ_eq_top, sup_comm]
    exact htop
  have hli : LinearIndependent K₁ f :=
    linearIndependent_of_top_le_span_of_card_eq_finrank hfspan (by rw [Fintype.card_fin, hq])
  intro hdet
  obtain ⟨a, ha0, ha⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdet
  have hx : ∑ j, a j • e j ∈ P := by
    rw [← hc]
    intro i
    have h1 := congrFun ha i
    simp only [Matrix.mulVec, dotProduct, Matrix.of_apply, Pi.zero_apply] at h1
    rw [map_sum]
    simp only [map_smul, smul_eq_mul]
    calc _ = ∑ j, c i (e j) * a j := Finset.sum_congr rfl fun j _ => mul_comm _ _
      _ = 0 := h1
  have h2 : ∑ j, a j • f j = 0 := by
    simp only [f, ← map_smul, ← map_sum]
    exact (Submodule.Quotient.mk_eq_zero P).mpr hx
  exact ha0 (funext (Fintype.linearIndependent_iff.mp hli a h2))

end

end ReciprocityTheory.ChartRestriction.G.FreeQuotientRank.LocalQuotientRank

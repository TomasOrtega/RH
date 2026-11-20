import Mathlib

namespace ReciprocityTheory.Coh.TorsionRankLength

universe u

open Module Submodule Function
open scoped Pointwise TensorProduct

section General

variable {R : Type u} [CommRing R] {M : Type u} [AddCommGroup M] [Module R M]

abbrev K (M : Type u) [AddCommGroup M] [Module R M] (r : R) : Submodule R M :=
  LinearMap.ker (r • LinearMap.id : M →ₗ[R] M)

/- English proof (translation)
Simplify using `[K]`.
-/
theorem mem_K {r : R} {x : M} : x ∈ K M r ↔ r • x = 0 := by
  simp [K]

/- English proof (translation)
Use extensionality with `x`. Rewrite using `[Submodule.mem_smul_pointwise_iff_exists, LinearMap.mem_range]`. Simplify using the standard rewrite rules.
-/
theorem smul_top_eq_range (r : R) :
    (r • ⊤ : Submodule R M) = LinearMap.range (r • LinearMap.id : M →ₗ[R] M) := by
  ext x
  rw [Submodule.mem_smul_pointwise_iff_exists, LinearMap.mem_range]
  simp

/- English proof (translation)
The claim follows from `Module.length_eq_add_of_exact N.subtype N.mkQ N.injective_subtype N.mkQ_surjective (LinearMap.exact_subtype_mkQ N)`.
-/
theorem len_sub_add_quot (N : Submodule R M) :
    Module.length R M = Module.length R N + Module.length R (M ⧸ N) :=
  Module.length_eq_add_of_exact N.subtype N.mkQ N.injective_subtype N.mkQ_surjective
    (LinearMap.exact_subtype_mkQ N)

/- English proof (translation)
Use `set φ : M →ₗ[R] M := r • LinearMap.id with hφ`. Establish `h1 : Module.length R M = Module.length R (K M r) + Module.length R (LinearMap.range φ)` using `Module.length_eq_add_of_exact (K M r).subtype φ.rangeRestrict (Submodule.injective_subtype _) φ.surjective_rangeRestrict (LinearMap.exact_iff.2 (by rw [LinearMap.ker_rangeRestrict, Submodule.range_subtype]))`. Establish `h2 : Module.length R M = Module.length R (r • ⊤ : Submodule R M) + Module.length R (QuotSMulTop r M)` using `len_sub_add_quot (r • ⊤ : Submodule R M)`. Establish `h3 : Module.length R (r • ⊤ : Submodule R M) = Module.length R (LinearMap.range φ)` using `(LinearEquiv.ofEq _ _ (smul_top_eq_range r)).length_eq`. Establish `hMt : Module.length R M ≠ ⊤` using `Module.length_ne_top_iff.2 hM`.

Establish `hL : Module.length R (LinearMap.range φ) ≠ ⊤` using `fun h => hMt (by rw [h1, h, add_top])`. Rewrite `h2` using `[h3]`. Rewrite `h2` using `[h1, add_comm (Module.length R (LinearMap.range φ))]`. Conclude with `WithTop.add_right_cancel hL h2`.
-/
theorem len_K_eq_len_quot (hM : IsFiniteLength R M) (r : R) :
    Module.length R (K M r) = Module.length R (QuotSMulTop r M) := by
  set φ : M →ₗ[R] M := r • LinearMap.id with hφ
  have h1 : Module.length R M = Module.length R (K M r) + Module.length R (LinearMap.range φ) :=
    Module.length_eq_add_of_exact (K M r).subtype φ.rangeRestrict (Submodule.injective_subtype _)
      φ.surjective_rangeRestrict
      (LinearMap.exact_iff.2 (by rw [LinearMap.ker_rangeRestrict, Submodule.range_subtype]))
  have h2 : Module.length R M = Module.length R (r • ⊤ : Submodule R M) + Module.length R (QuotSMulTop r M) :=
    len_sub_add_quot (r • ⊤ : Submodule R M)
  have h3 : Module.length R (r • ⊤ : Submodule R M) = Module.length R (LinearMap.range φ) :=
    (LinearEquiv.ofEq _ _ (smul_top_eq_range r)).length_eq
  have hMt : Module.length R M ≠ ⊤ := Module.length_ne_top_iff.2 hM
  have hL : Module.length R (LinearMap.range φ) ≠ ⊤ := fun h => hMt (by rw [h1, h, add_top])
  rw [h3] at h2
  rw [h1, add_comm (Module.length R (LinearMap.range φ))] at h2
  exact WithTop.add_right_cancel hL h2

end General

section DVR

variable {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]

/- English proof (translation)
Establish `hmax : (Ideal.span {t} : Ideal R).IsMaximal` using `PrincipalIdealRing.isMaximal_of_irreducible ht`. Establish `h1 : Module.length R (R ⧸ Ideal.span {t}) = 1`. Rewrite using `[Module.length_eq_one_iff]`. Conclude with `isSimpleModule_iff_isCoatom.2 (Ideal.isMaximal_def.1 hmax)`. Establish `ht0 : t ≠ 0` using `ht.ne_zero`.

Proceed by induction on `k with`. Consider the case `zero => haveI : Subsingleton (R ⧸ Ideal.span {t ^ 0}) := Ideal.Quotient.subsingleton_iff.2 (by rw [pow_zero, Ideal.span_singleton_one])`. Rewrite using `[Nat.cast_zero]`. Conclude with `Module.length_eq_zero_iff.2 this`. Consider the case `succ k ih`.

Establish `hle : Ideal.span {t} ≤ Submodule.comap (LinearMap.mulLeft R (t ^ k)) (Ideal.span {t ^ (k + 1)})`. Introduce `x hx`. Take `⟨y, rfl⟩` from `Ideal.mem_span_singleton'.1 hx`. Simplify using `only [Submodule.mem_comap, LinearMap.mulLeft_apply]`. Rewrite using `[Ideal.mem_span_singleton']`.

Conclude with `⟨y, by ring⟩`. Set `f` to `Submodule.mapQ (Ideal.span {t}) (Ideal.span {t ^ (k + 1)}) (LinearMap.mulLeft R (t ^ k)) hle`. Establish `hfac : Ideal.span {t ^ (k + 1)} ≤ Ideal.span {t ^ k}`. Rewrite using `[Ideal.span_singleton_le_span_singleton]`. Conclude with `⟨t, by ring⟩`.

Set `g` to `(Ideal.Quotient.factorₐ R hfac).toLinearMap`. Establish `hf : Function.Injective f`. Rewrite using `[← LinearMap.ker_eq_bot, eq_bot_iff]`. Introduce `x hx`. Take `⟨x, rfl⟩` from `Submodule.Quotient.mk_surjective _ x`.

Rewrite `hx` using `[LinearMap.mem_ker]`. Simplify using `only [f, Submodule.mapQ_apply, LinearMap.mulLeft_apply, Submodule.Quotient.mk_eq_zero] at hx`. Rewrite using `[Submodule.mem_bot, Submodule.Quotient.mk_eq_zero]`. Take `⟨y, hy⟩` from `Ideal.mem_span_singleton'.1 hx`. Rewrite using `[Ideal.mem_span_singleton']`.

Use `⟨y, ?_⟩` and prove the remaining obligations. Establish `: t ^ k * (y * t) = t ^ k * x` using `by rw [← hy]; ring`. Conclude with `mul_left_cancel₀ (pow_ne_zero _ ht0) this`. Establish `hg : Function.Surjective g`. Introduce `y`.

Take `⟨z, rfl⟩` from `Ideal.Quotient.mk_surjective y`. Conclude with `⟨Ideal.Quotient.mk _ z, rfl⟩`. Establish `hex : Function.Exact f g`. Introduce `y`. Take `⟨z, rfl⟩` from `Ideal.Quotient.mk_surjective y`.

Prove the components needed by the constructor for the conclusion. Introduce `hz`. Establish `hz' : z ∈ Ideal.span {t ^ k}`. Rewrite using `[← Ideal.Quotient.eq_zero_iff_mem]`. Conclude with `hz`.

Take `⟨w, rfl⟩` from `Ideal.mem_span_singleton'.1 hz'`. Conclude with `⟨Submodule.Quotient.mk w, by`. Simplify using `only [f, Submodule.mapQ_apply, LinearMap.mulLeft_apply]`. Use `congr 1`. Use the proof step `ring⟩`.

Introduce and unpack `⟨x, hx⟩`. Take `⟨x, rfl⟩` from `Submodule.Quotient.mk_surjective _ x`. Rewrite using `[← hx]`. Simplify using `only [f, g, Submodule.mapQ_apply, LinearMap.mulLeft_apply, AlgHom.toLinearMap_apply]`. Use `show Ideal.Quotient.factor hfac (Ideal.Quotient.mk _ (t ^ k * x)) = 0`.

Rewrite using `[Ideal.Quotient.factor_mk, Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton']`. Conclude with `⟨x, by ring⟩`. Rewrite using `[Module.length_eq_add_of_exact f g hf hg hex, h1, ih]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem len_quot_pow {t : R} (ht : Irreducible t) (k : ℕ) :
    Module.length R (R ⧸ Ideal.span {t ^ k}) = k := by
  have hmax : (Ideal.span {t} : Ideal R).IsMaximal := PrincipalIdealRing.isMaximal_of_irreducible ht
  have h1 : Module.length R (R ⧸ Ideal.span {t}) = 1 := by
    rw [Module.length_eq_one_iff]
    exact isSimpleModule_iff_isCoatom.2 (Ideal.isMaximal_def.1 hmax)
  have ht0 : t ≠ 0 := ht.ne_zero
  induction k with
  | zero =>
    haveI : Subsingleton (R ⧸ Ideal.span {t ^ 0}) :=
      Ideal.Quotient.subsingleton_iff.2 (by rw [pow_zero, Ideal.span_singleton_one])
    rw [Nat.cast_zero]
    exact Module.length_eq_zero_iff.2 this
  | succ k ih =>
    have hle : Ideal.span {t} ≤ Submodule.comap (LinearMap.mulLeft R (t ^ k)) (Ideal.span {t ^ (k + 1)}) := by
      intro x hx
      obtain ⟨y, rfl⟩ := Ideal.mem_span_singleton'.1 hx
      simp only [Submodule.mem_comap, LinearMap.mulLeft_apply]
      rw [Ideal.mem_span_singleton']
      exact ⟨y, by ring⟩
    let f := Submodule.mapQ (Ideal.span {t}) (Ideal.span {t ^ (k + 1)}) (LinearMap.mulLeft R (t ^ k)) hle
    have hfac : Ideal.span {t ^ (k + 1)} ≤ Ideal.span {t ^ k} := by
      rw [Ideal.span_singleton_le_span_singleton]
      exact ⟨t, by ring⟩
    let g := (Ideal.Quotient.factorₐ R hfac).toLinearMap
    have hf : Function.Injective f := by
      rw [← LinearMap.ker_eq_bot, eq_bot_iff]
      intro x hx
      obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ x
      rw [LinearMap.mem_ker] at hx
      simp only [f, Submodule.mapQ_apply, LinearMap.mulLeft_apply, Submodule.Quotient.mk_eq_zero] at hx
      rw [Submodule.mem_bot, Submodule.Quotient.mk_eq_zero]
      obtain ⟨y, hy⟩ := Ideal.mem_span_singleton'.1 hx
      rw [Ideal.mem_span_singleton']
      refine ⟨y, ?_⟩
      have : t ^ k * (y * t) = t ^ k * x := by rw [← hy]; ring
      exact mul_left_cancel₀ (pow_ne_zero _ ht0) this
    have hg : Function.Surjective g := by
      intro y
      obtain ⟨z, rfl⟩ := Ideal.Quotient.mk_surjective y
      exact ⟨Ideal.Quotient.mk _ z, rfl⟩
    have hex : Function.Exact f g := by
      intro y
      obtain ⟨z, rfl⟩ := Ideal.Quotient.mk_surjective y
      constructor
      · intro hz
        have hz' : z ∈ Ideal.span {t ^ k} := by
          rw [← Ideal.Quotient.eq_zero_iff_mem]
          exact hz
        obtain ⟨w, rfl⟩ := Ideal.mem_span_singleton'.1 hz'
        exact ⟨Submodule.Quotient.mk w, by
          simp only [f, Submodule.mapQ_apply, LinearMap.mulLeft_apply]
          congr 1
          ring⟩
      · rintro ⟨x, hx⟩
        obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ x
        rw [← hx]
        simp only [f, g, Submodule.mapQ_apply, LinearMap.mulLeft_apply, AlgHom.toLinearMap_apply]
        show Ideal.Quotient.factor hfac (Ideal.Quotient.mk _ (t ^ k * x)) = 0
        rw [Ideal.Quotient.factor_mk, Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton']
        exact ⟨x, by ring⟩
    rw [Module.length_eq_add_of_exact f g hf hg hex, h1, ih]
    push_cast
    ring

variable (H : Type u) [AddCommGroup H] [Module R H] [Module.Finite R H]

/- English proof (translation)
Take `⟨ι, _, p, hp, e, ⟨f⟩⟩` from `Module.equiv_directSum_of_isTorsion (R := R) (M := torsion R H) (torsion_isTorsion)`. Rewrite using `[← Module.length_ne_top_iff, f.length_eq, (DirectSum.linearEquivFunOnFintype R ι (fun i => R ⧸ R ∙ p i ^ e i)).length_eq, Module.length_pi_of_fintype]`. Establish `: ∀ i, Module.length R (R ⧸ R ∙ p i ^ e i) = e i` using `fun i => len_quot_pow (hp i) (e i)`. Simplify using `only [this]`. Conclude with `(ENat.sum_lt_top.mpr fun i _ => ENat.natCast_lt_top _).ne`.
-/
theorem torsion_finLen : IsFiniteLength R (torsion R H) := by
  obtain ⟨ι, _, p, hp, e, ⟨f⟩⟩ :=
    Module.equiv_directSum_of_isTorsion (R := R) (M := torsion R H) (torsion_isTorsion)
  rw [← Module.length_ne_top_iff, f.length_eq,
    (DirectSum.linearEquivFunOnFintype R ι (fun i => R ⧸ R ∙ p i ^ e i)).length_eq,
    Module.length_pi_of_fintype]
  have : ∀ i, Module.length R (R ⧸ R ∙ p i ^ e i) = e i := fun i => len_quot_pow (hp i) (e i)
  simp only [this]
  exact (ENat.sum_lt_top.mpr fun i _ => ENat.natCast_lt_top _).ne

/- English proof (translation)
Rewrite using `[Module.finrank_eq_zero_iff]`. Introduce `x`. Take `⟨a, ha⟩` from `(Submodule.mem_torsion_iff (x : H)).1 x.2`. Conclude with `⟨a, nonZeroDivisors.ne_zero a.2, Subtype.ext ha⟩`.
-/
theorem finrank_torsion_eq_zero : Module.finrank R (torsion R H) = 0 := by
  rw [Module.finrank_eq_zero_iff]
  intro x
  obtain ⟨a, ha⟩ := (Submodule.mem_torsion_iff (x : H)).1 x.2
  exact ⟨a, nonZeroDivisors.ne_zero a.2, Subtype.ext ha⟩

/- English proof (translation)
Take `⟨n, b⟩` from `Module.basisOfFiniteTypeTorsionFree' (R := R) (M := H ⧸ torsion R H)`. Take `⟨f, hf⟩` from `Module.projective_lifting_property (torsion R H).mkQ LinearMap.id (torsion R H).mkQ_surjective`. Establish `e : (torsion R H × (H ⧸ torsion R H)) ≃ₗ[R] H` using `lequivProdOfRightSplitExact (torsion R H).injective_subtype (by rw [Submodule.range_subtype, Submodule.ker_mkQ]) hf`. Establish `hrank : Module.finrank R H = n`. Establish `h` using `Submodule.finrank_quotient_add_finrank (torsion R H)`.

Rewrite `h` using `[finrank_torsion_eq_zero, add_zero, Module.finrank_eq_card_basis b, Fintype.card_fin]`. Conclude with `h.symm`. Establish `e2 : QuotSMulTop r H ≃ₗ[R] ((R ⧸ Ideal.span {r}) ⊗[R] torsion R H) × ((R ⧸ Ideal.span {r}) ⊗[R] (H ⧸ torsion R H))` using `(QuotSMulTop.congr r e.symm).trans ((QuotSMulTop.equivQuotTensor r _).trans (TensorProduct.prodRight R R _ _ _))`. Establish `e3 : ((R ⧸ Ideal.span {r}) ⊗[R] (H ⧸ torsion R H)) ≃ₗ[R] (Fin n →₀ (R ⧸ Ideal.span {r}))` using `(LinearEquiv.lTensor _ b.repr).trans (TensorProduct.finsuppScalarRight R R _ _)`. Rewrite using `[e2.length_eq, Module.length_prod, ← (QuotSMulTop.equivQuotTensor r _).length_eq, e3.length_eq, Module.length_finsupp, hrank]`.

Simplify using the standard rewrite rules.
-/
theorem len_quot_split (r : R) :
    Module.length R (QuotSMulTop r H) = Module.length R (QuotSMulTop r (torsion R H)) +
      Module.finrank R H * Module.length R (R ⧸ Ideal.span {r}) := by
  obtain ⟨n, b⟩ := Module.basisOfFiniteTypeTorsionFree' (R := R) (M := H ⧸ torsion R H)
  obtain ⟨f, hf⟩ := Module.projective_lifting_property (torsion R H).mkQ LinearMap.id
    (torsion R H).mkQ_surjective
  have e : (torsion R H × (H ⧸ torsion R H)) ≃ₗ[R] H :=
    lequivProdOfRightSplitExact (torsion R H).injective_subtype
      (by rw [Submodule.range_subtype, Submodule.ker_mkQ]) hf
  have hrank : Module.finrank R H = n := by
    have h := Submodule.finrank_quotient_add_finrank (torsion R H)
    rw [finrank_torsion_eq_zero, add_zero, Module.finrank_eq_card_basis b, Fintype.card_fin] at h
    exact h.symm
  have e2 : QuotSMulTop r H ≃ₗ[R]
      ((R ⧸ Ideal.span {r}) ⊗[R] torsion R H) × ((R ⧸ Ideal.span {r}) ⊗[R] (H ⧸ torsion R H)) :=
    (QuotSMulTop.congr r e.symm).trans ((QuotSMulTop.equivQuotTensor r _).trans
      (TensorProduct.prodRight R R _ _ _))
  have e3 : ((R ⧸ Ideal.span {r}) ⊗[R] (H ⧸ torsion R H)) ≃ₗ[R] (Fin n →₀ (R ⧸ Ideal.span {r})) :=
    (LinearEquiv.lTensor _ b.repr).trans (TensorProduct.finsuppScalarRight R R _ _)
  rw [e2.length_eq, Module.length_prod, ← (QuotSMulTop.equivQuotTensor r _).length_eq,
    e3.length_eq, Module.length_finsupp, hrank]
  simp

/- English proof (translation)
Establish `hmem : ∀ y : H, r • y = 0 → y ∈ torsion R H` using `fun y hy => (Submodule.mem_torsion_iff y).2 ⟨⟨r, mem_nonZeroDivisors_of_ne_zero hr⟩, hy⟩`. Set `f : K (torsion R H) r →ₗ[R] K H r` to `{ toFun := fun x => ⟨((x : torsion R H) : H), by`. Establish `h1` using `mem_K.1 x.2`. Rewrite using `[mem_K]`. Simplify using `using congrArg Subtype.val h1⟩`.

Use the proof step `map_add' := fun x y => rfl`. Use the proof step `map_smul' := fun c x => rfl }`. Establish `hf : Function.Bijective f`. Prove the components needed by the constructor for the conclusion. Introduce `x y hxy`.

Apply `Subtype.ext` to reduce the goal to its premises. Apply `Subtype.ext` to reduce the goal to its premises. Conclude with `congrArg (fun z : K H r => (z : H)) hxy`. Introduce `y`. Use `⟨⟨⟨y, hmem y (mem_K.1 y.2)⟩, ?_⟩, rfl⟩` and prove the remaining obligations.

Rewrite using `[mem_K]`. Apply `Subtype.ext` to reduce the goal to its premises. Conclude with `mem_K.1 y.2`. Conclude with `((LinearEquiv.ofBijective f hf).length_eq).symm`.
-/
theorem len_K_torsion {r : R} (hr : r ≠ 0) :
    Module.length R (K H r) = Module.length R (K (torsion R H) r) := by
  have hmem : ∀ y : H, r • y = 0 → y ∈ torsion R H := fun y hy =>
    (Submodule.mem_torsion_iff y).2 ⟨⟨r, mem_nonZeroDivisors_of_ne_zero hr⟩, hy⟩
  let f : K (torsion R H) r →ₗ[R] K H r :=
    { toFun := fun x => ⟨((x : torsion R H) : H), by
        have h1 := mem_K.1 x.2
        rw [mem_K]
        simpa using congrArg Subtype.val h1⟩
      map_add' := fun x y => rfl
      map_smul' := fun c x => rfl }
  have hf : Function.Bijective f := by
    constructor
    · intro x y hxy
      apply Subtype.ext
      apply Subtype.ext
      exact congrArg (fun z : K H r => (z : H)) hxy
    · intro y
      refine ⟨⟨⟨y, hmem y (mem_K.1 y.2)⟩, ?_⟩, rfl⟩
      rw [mem_K]
      apply Subtype.ext
      exact mem_K.1 y.2
  exact ((LinearEquiv.ofBijective f hf).length_eq).symm

end DVR

section Main

variable {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]

/- English proof (translation)
Establish `htm : t ^ m ≠ 0` using `pow_ne_zero _ ht.ne_zero`. Establish `hT` using `torsion_finLen (R := R) H`. Establish `hK` using `len_K_torsion (R := R) H htm`. Establish `hQ` using `len_K_eq_len_quot hT (t ^ m)`. Establish `hS` using `len_quot_split (R := R) H (t ^ m)`.

Establish `hP` using `len_quot_pow ht m`. Use `⟨?_, ?_, Module.length_ne_top_iff.2 hT⟩` and prove the remaining obligations. Rewrite using `[hS, ← hQ, ← hK, hP]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[hK]`. Establish `h` using `len_sub_add_quot (K (torsion R H) (t ^ m))`. Rewrite using `[h]`. Conclude with `le_self_add`.
-/
theorem len_quot_eq (H : Type u) [AddCommGroup H] [Module R H] [Module.Finite R H] {t : R}
    (ht : Irreducible t) (m : ℕ) :
    Module.length R (QuotSMulTop (t ^ m) H) =
        ((m * Module.finrank R H : ℕ) : ℕ∞) + Module.length R (K H (t ^ m)) ∧
      Module.length R (K H (t ^ m)) ≤ Module.length R (torsion R H) ∧
      Module.length R (torsion R H) ≠ ⊤ := by
  have htm : t ^ m ≠ 0 := pow_ne_zero _ ht.ne_zero
  have hT := torsion_finLen (R := R) H
  have hK := len_K_torsion (R := R) H htm
  have hQ := len_K_eq_len_quot hT (t ^ m)
  have hS := len_quot_split (R := R) H (t ^ m)
  have hP := len_quot_pow ht m
  refine ⟨?_, ?_, Module.length_ne_top_iff.2 hT⟩
  · rw [hS, ← hQ, ← hK, hP]
    push_cast
    ring
  · rw [hK]
    have h := len_sub_add_quot (K (torsion R H) (t ^ m))
    rw [h]
    exact le_self_add

end Main

end ReciprocityTheory.Coh.TorsionRankLength

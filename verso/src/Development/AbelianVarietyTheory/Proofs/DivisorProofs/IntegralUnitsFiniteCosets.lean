import Mathlib
import Formalism.LocalToGlobal.Divisibility.Tuples
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FiniteAdeleStrongApproximationModNat
open NumberField IsDedekindDomain Formalism.L2.DIV Formalism.UG
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.CongNIndex

variable (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

def embO : 𝓞 E →+* RInt F E :=
  RingHom.codRestrict
    ((Algebra.TensorProduct.includeLeft : E →ₐ[F] AfE F E).toRingHom.comp (algebraMap (𝓞 E) E))
    (RInt F E) fun o => Subring.subset_closure (Set.mem_union_left _ ⟨⟨_, RingHom.mem_range.2 ⟨o, rfl⟩⟩, rfl⟩)

def redO (N : ℕ) : 𝓞 E →+* RInt F E ⧸ Ideal.span {(N : RInt F E)} :=
  (Ideal.Quotient.mk _).comp (embO F E)

/- English proof (translation)
The claim follows from `Subring.subset_closure (Set.mem_union_right _ ⟨⟨a, ha⟩, rfl⟩)`.
-/
theorem one_tmul_mem {a : FiniteAdeleRing (𝓞 F) F} (ha : a ∈ intAd F) :
    (1 : E) ⊗ₜ[F] a ∈ RInt F E :=
  Subring.subset_closure (Set.mem_union_right _ ⟨⟨a, ha⟩, rfl⟩)

/- English proof (translation)
Set `T : Subring (RInt F E)` to `(redO F E N).range.comap (Ideal.Quotient.mk _)`. Establish `hN0 : Ideal.Quotient.mk (Ideal.span {(N : RInt F E)}) (N : RInt F E) = 0` using `Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.subset_span rfl)`. Establish `key : RInt F E ≤ T.map (RInt F E).subtype`. Use `Subring.closure_le.2 ?_` and prove the remaining obligations. Introduce and unpack `_ (⟨⟨x, o, rfl⟩, rfl⟩ | ⟨⟨y, hy⟩, rfl⟩)`.

Conclude with `⟨embO F E o, ⟨o, rfl⟩, rfl⟩`. Take `⟨x, a, ha, e⟩` from `(GlobalTheory.AdLat.strong_approximation_mod_nat F N hN).2 y hy`. Use `⟨embO F E (algebraMap (𝓞 F) (𝓞 E) x) + (N : RInt F E) * ⟨_, one_tmul_mem F E (a := a) ha⟩, ⟨algebraMap (𝓞 F) (𝓞 E) x, ?_⟩, ?_⟩` and prove the remaining obligations. Use `show redO F E N _ = Ideal.Quotient.mk _ _`. Rewrite using `[map_add, map_mul, hN0, zero_mul, add_zero]`.

Both sides reduce to the same expression. Use `show ((algebraMap F E (x : F)) ⊗ₜ[F] (1 : FiniteAdeleRing (𝓞 F) F)) + (N : AfE F E) * ((1 : E) ⊗ₜ[F] a) = (1 : E) ⊗ₜ[F] y`. Rewrite using `[e, TensorProduct.tmul_add, Algebra.algebraMap_eq_smul_one (A := FiniteAdeleRing (𝓞 F) F), TensorProduct.tmul_smul, TensorProduct.smul_tmul', ← Algebra.algebraMap_eq_smul_one, TensorProduct.tmul_smul, nsmul_eq_mul]`. Take `⟨w, hw, e⟩` from `key z.2`. Establish `: w = z` using `Subtype.ext e`.

Substitute `this` using the available equality. Conclude with `hw`.
-/
theorem mk_mem_range (N : ℕ) (hN : 0 < N) (z : RInt F E) :
    Ideal.Quotient.mk (Ideal.span {(N : RInt F E)}) z ∈ (redO F E N).range := by
  let T : Subring (RInt F E) := (redO F E N).range.comap (Ideal.Quotient.mk _)
  have hN0 : Ideal.Quotient.mk (Ideal.span {(N : RInt F E)}) (N : RInt F E) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.subset_span rfl)
  have key : RInt F E ≤ T.map (RInt F E).subtype := by
    refine Subring.closure_le.2 ?_
    rintro _ (⟨⟨x, o, rfl⟩, rfl⟩ | ⟨⟨y, hy⟩, rfl⟩)
    · exact ⟨embO F E o, ⟨o, rfl⟩, rfl⟩
    · obtain ⟨x, a, ha, e⟩ := (GlobalTheory.AdLat.strong_approximation_mod_nat F N hN).2 y hy
      refine ⟨embO F E (algebraMap (𝓞 F) (𝓞 E) x) + (N : RInt F E) * ⟨_, one_tmul_mem F E (a := a) ha⟩,
        ⟨algebraMap (𝓞 F) (𝓞 E) x, ?_⟩, ?_⟩
      · show redO F E N _ = Ideal.Quotient.mk _ _
        rw [map_add, map_mul, hN0, zero_mul, add_zero]
        rfl
      · show ((algebraMap F E (x : F)) ⊗ₜ[F] (1 : FiniteAdeleRing (𝓞 F) F)) + (N : AfE F E) * ((1 : E) ⊗ₜ[F] a) = (1 : E) ⊗ₜ[F] y
        rw [e, TensorProduct.tmul_add, Algebra.algebraMap_eq_smul_one (A := FiniteAdeleRing (𝓞 F) F),
          TensorProduct.tmul_smul, TensorProduct.smul_tmul', ← Algebra.algebraMap_eq_smul_one,
          TensorProduct.tmul_smul, nsmul_eq_mul]
  obtain ⟨w, hw, e⟩ := key z.2
  have : w = z := Subtype.ext e
  subst this
  exact hw

/- English proof (translation)
Use `haveI : Finite (𝓞 E ⧸ Ideal.span {(N : 𝓞 E)}) := by`. Apply `Ideal.finiteQuotientOfFreeOfNeBot` to reduce the goal to its premises. Simplify using `[Ideal.span_singleton_eq_bot]`. Use linear arithmetic over natural numbers and integers. Establish `hN0 : Ideal.Quotient.mk (Ideal.span {(N : RInt F E)}) (N : RInt F E) = 0` using `Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.subset_span rfl)`.

Set `φ : 𝓞 E ⧸ Ideal.span {(N : 𝓞 E)} →+* RInt F E ⧸ Ideal.span {(N : RInt F E)}` to `Ideal.Quotient.lift _ (redO F E N) fun a ha => by`. Take `⟨c, rfl⟩` from `Ideal.mem_span_singleton'.1 ha`. Rewrite using `[map_mul, map_natCast, ← map_natCast (Ideal.Quotient.mk (Ideal.span {(N : RInt F E)})), hN0, mul_zero]`. Use `Finite.of_surjective φ fun q => ?_` and prove the remaining obligations. Take `⟨z, rfl⟩` from `Ideal.Quotient.mk_surjective q`.

Take `⟨o, ho⟩` from `mk_mem_range F E N hN z`. Conclude with `⟨Ideal.Quotient.mk _ o, ho⟩`.
-/
theorem finite_quot (N : ℕ) (hN : 0 < N) : Finite (RInt F E ⧸ Ideal.span {(N : RInt F E)}) := by
  haveI : Finite (𝓞 E ⧸ Ideal.span {(N : 𝓞 E)}) := by
    apply Ideal.finiteQuotientOfFreeOfNeBot
    simp [Ideal.span_singleton_eq_bot]; omega
  have hN0 : Ideal.Quotient.mk (Ideal.span {(N : RInt F E)}) (N : RInt F E) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.subset_span rfl)
  let φ : 𝓞 E ⧸ Ideal.span {(N : 𝓞 E)} →+* RInt F E ⧸ Ideal.span {(N : RInt F E)} :=
    Ideal.Quotient.lift _ (redO F E N) fun a ha => by
      obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.1 ha
      rw [map_mul, map_natCast, ← map_natCast (Ideal.Quotient.mk (Ideal.span {(N : RInt F E)})), hN0, mul_zero]
  refine Finite.of_surjective φ fun q => ?_
  obtain ⟨z, rfl⟩ := Ideal.Quotient.mk_surjective q
  obtain ⟨o, ho⟩ := mk_mem_range F E N hN z
  exact ⟨Ideal.Quotient.mk _ o, ho⟩

def toU : intU F E ≃* (RInt F E)ˣ := Submonoid.unitsEquivUnitsType (RInt F E).toSubmonoid

/- English proof (translation)
Use `haveI := finite_quot F E N hN`. Set `I` to `Ideal.span {(N : RInt F E)}`. Set `f : (AfE F E)ˣ → (RInt F E ⧸ I)ˣ` to `fun k => if h : k ∈ intU F E then Units.map (Ideal.Quotient.mk I).toMonoidHom (toU F E ⟨k, h⟩) else 1`. Set `g : (RInt F E ⧸ I)ˣ → (AfE F E)ˣ` to `fun q => if h : ∃ k ∈ intU F E, f k = q then h.choose else 1`. Use `⟨(Set.finite_range g).toFinset, fun k hk => ?_⟩` and prove the remaining obligations.

Establish `hex : ∃ k' ∈ intU F E, f k' = f k` using `⟨k, hk, rfl⟩`. Establish `hg : g (f k) = hex.choose` using `dif_pos hex`. Take `⟨hs, hfs⟩` from `hex.choose_spec`. Use `⟨g (f k), (Set.finite_range g).mem_toFinset.2 ⟨_, rfl⟩, ?_⟩` and prove the remaining obligations. Rewrite using `[hg]`.

Use `set s := hex.choose`. Use `⟨(toU F E ⟨s, hs⟩)⁻¹ * toU F E ⟨k, hk⟩, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[SetLike.mem_coe, MonoidHom.mem_ker, map_mul, map_inv, inv_mul_eq_one]`. Establish `h1 : f s = _` using `dif_pos hs`. Establish `h2 : f k = _` using `dif_pos hk`.

Rewrite using `[← h1, ← h2, hfs]`. Use `ext`. Simplify using `only [map_mul, map_inv, Units.val_mul]`. Both sides reduce to the same expression.
-/
theorem exists_finset (N : ℕ) (hN : 0 < N) :
    ∃ S : Finset (AfE F E)ˣ, ∀ k ∈ intU F E, ∃ s ∈ S, s⁻¹ * k ∈ congN F E N := by
  classical
  haveI := finite_quot F E N hN
  let I := Ideal.span {(N : RInt F E)}
  let f : (AfE F E)ˣ → (RInt F E ⧸ I)ˣ := fun k =>
    if h : k ∈ intU F E then Units.map (Ideal.Quotient.mk I).toMonoidHom (toU F E ⟨k, h⟩) else 1
  let g : (RInt F E ⧸ I)ˣ → (AfE F E)ˣ := fun q =>
    if h : ∃ k ∈ intU F E, f k = q then h.choose else 1
  refine ⟨(Set.finite_range g).toFinset, fun k hk => ?_⟩
  have hex : ∃ k' ∈ intU F E, f k' = f k := ⟨k, hk, rfl⟩
  have hg : g (f k) = hex.choose := dif_pos hex
  obtain ⟨hs, hfs⟩ := hex.choose_spec
  refine ⟨g (f k), (Set.finite_range g).mem_toFinset.2 ⟨_, rfl⟩, ?_⟩
  rw [hg]
  set s := hex.choose
  refine ⟨(toU F E ⟨s, hs⟩)⁻¹ * toU F E ⟨k, hk⟩, ?_, ?_⟩
  · rw [SetLike.mem_coe, MonoidHom.mem_ker, map_mul, map_inv, inv_mul_eq_one]
    have h1 : f s = _ := dif_pos hs
    have h2 : f k = _ := dif_pos hk
    rw [← h1, ← h2, hfs]
  · ext
    simp only [map_mul, map_inv, Units.val_mul]
    rfl

end GlobalTheory.CongNIndex

/- English proof (translation)
Introduce `L _ _ N hN` and use `GlobalTheory.CongNIndex.exists_finset ℚ L N hN`.
-/
theorem GlobalTheory.congN_finite_index : ∀ (L : Type) [Field L] [NumberField L] (N : ℕ), 0 < N →
    ∃ S : Finset (AfE ℚ L)ˣ, ∀ k ∈ intU ℚ L, ∃ s ∈ S, s⁻¹ * k ∈ congN ℚ L N :=
  fun L _ _ N hN => GlobalTheory.CongNIndex.exists_finset ℚ L N hN

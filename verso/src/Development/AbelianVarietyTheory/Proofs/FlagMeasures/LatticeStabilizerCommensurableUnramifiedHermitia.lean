import Mathlib
import Formalism.SharpRestriction.CuspSpanNormBounds.FractionFieldToGenericStalkAlgebraMapEq
import Development.AbelianVarietyTheory.Definitions.Foundations.IsHermND
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ComplementReferenceCompactSubgroup
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.HermLat
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsPrincipalIdealRingOfHenselian
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ImportsBisFurther

open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.LatComm

/- English proof (translation)
Establish `hfg : (⊤ : Submodule R Λ).FG` using `(Submodule.fg_top Λ).2 hΛ`. Establish `hf : Finite (Λ ⧸ (Ideal.span {c}) • (⊤ : Submodule R Λ))` using `Submodule.finite_quotient_smul _ hfg`. Establish `hs : Finite (Submodule R (Λ ⧸ (Ideal.span {c}) • (⊤ : Submodule R Λ)))` using `Finite.of_injective _ SetLike.coe_injective`. Establish `key : ∀ M : Submodule R V, (M ≤ Λ ∧ ∀ v ∈ Λ, c • v ∈ M) → (((M.comap Λ.subtype).map ((Ideal.span {c}) • (⊤ : Submodule R Λ)).mkQ).comap ((Ideal.span {c}) • (⊤ : Submodule R Λ)).mkQ).map Λ.subtype = M`. Introduce `M hM`.

Establish `h1 : (Ideal.span {c}) • (⊤ : Submodule R Λ) ≤ M.comap Λ.subtype`. Rewrite using `[Submodule.smul_le]`. Introduce `r hr v _`. Take `⟨s, rfl⟩` from `Ideal.mem_span_singleton'.1 hr`. Rewrite using `[mul_smul]`.

Conclude with `Submodule.smul_mem _ _ (hM.2 v v.2)`. Rewrite using `[Submodule.comap_map_mkQ, sup_eq_right.2 h1, Submodule.map_comap_subtype, inf_eq_right.2 hM.1]`. Use `Set.Finite.of_finite_image (f := fun M : Submodule R V => (M.comap Λ.subtype).map ((Ideal.span {c}) • (⊤ : Submodule R Λ)).mkQ) (Set.toFinite _) ?_` and prove the remaining obligations. Introduce `M hM N hN h`. Rewrite using `[← key M hM, ← key N hN]`.

Simplify using `only at h`. Rewrite using `[h]`.
-/
theorem finite_between {R V : Type} [CommRing R] [AddCommGroup V] [Module R V] (c : R)
    [Finite (R ⧸ Ideal.span {c})] (Λ : Submodule R V) (hΛ : Λ.FG) :
    {M : Submodule R V | M ≤ Λ ∧ ∀ v ∈ Λ, c • v ∈ M}.Finite := by
  have hfg : (⊤ : Submodule R Λ).FG := (Submodule.fg_top Λ).2 hΛ
  have hf : Finite (Λ ⧸ (Ideal.span {c}) • (⊤ : Submodule R Λ)) :=
    Submodule.finite_quotient_smul _ hfg
  have hs : Finite (Submodule R (Λ ⧸ (Ideal.span {c}) • (⊤ : Submodule R Λ))) :=
    Finite.of_injective _ SetLike.coe_injective
  have key : ∀ M : Submodule R V, (M ≤ Λ ∧ ∀ v ∈ Λ, c • v ∈ M) →
      (((M.comap Λ.subtype).map ((Ideal.span {c}) • (⊤ : Submodule R Λ)).mkQ).comap
        ((Ideal.span {c}) • (⊤ : Submodule R Λ)).mkQ).map Λ.subtype = M := by
    intro M hM
    have h1 : (Ideal.span {c}) • (⊤ : Submodule R Λ) ≤ M.comap Λ.subtype := by
      rw [Submodule.smul_le]
      intro r hr v _
      obtain ⟨s, rfl⟩ := Ideal.mem_span_singleton'.1 hr
      rw [mul_smul]
      exact Submodule.smul_mem _ _ (hM.2 v v.2)
    rw [Submodule.comap_map_mkQ, sup_eq_right.2 h1, Submodule.map_comap_subtype,
      inf_eq_right.2 hM.1]
  refine Set.Finite.of_finite_image (f := fun M : Submodule R V =>
    (M.comap Λ.subtype).map ((Ideal.span {c}) • (⊤ : Submodule R Λ)).mkQ) (Set.toFinite _) ?_
  intro M hM N hN h
  rw [← key M hM, ← key N hN]
  simp only at h
  rw [h]

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]

/- English proof (translation)
Use `first`. Consider the case `exact @_root_.GlobalTheory.PowMulMemOrder.main`. Consider the case `exact _root_.GlobalTheory.PowMulMemOrder.main`. Consider the case `(apply _root_.GlobalTheory.PowMulMemOrder.main <;> assumption)`. Consider the case `(intros; apply _root_.GlobalTheory.PowMulMemOrder.main <;> assumption)`.

Consider the case `(intros; apply @_root_.GlobalTheory.PowMulMemOrder.main <;> first | assumption | infer_instance)`. Consider the case `(intros; exact _root_.GlobalTheory.PowMulMemOrder.main ..)`.
-/
theorem exists_pow_smul_mem (L : LocE F E) {ϖ : 𝒪[F]} (hϖ : Irreducible ϖ) (p : L.O)
    (hp : (p : E) = algebraMap F E (ϖ : F)) {n : ℕ}
    {Λ : Submodule L.O (Fin n → E)} (hΛ : IsLat L Λ) (v : Fin n → E) :
    ∃ j : ℕ, p ^ j • v ∈ Λ := by
  first
  | exact @_root_.GlobalTheory.PowMulMemOrder.main
  | exact _root_.GlobalTheory.PowMulMemOrder.main
  | (apply _root_.GlobalTheory.PowMulMemOrder.main <;> assumption)
  | (intros; apply _root_.GlobalTheory.PowMulMemOrder.main <;> assumption)
  | (intros; apply @_root_.GlobalTheory.PowMulMemOrder.main <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.PowMulMemOrder.main ..)

/- English proof (translation)
Take `⟨s, rfl⟩` from `hΛ'`. Use `choose f hf using exists_pow_smul_mem L hϖ p hp hΛ`. Use `⟨s.sup f, fun v hv => ?_⟩` and prove the remaining obligations. Establish `: Submodule.span L.O (s : Set (Fin n → E)) ≤ Λ.comap (LinearMap.lsmul L.O (Fin n → E) (p ^ s.sup f))`. Rewrite using `[Submodule.span_le]`.

Introduce `x hx`. Take `⟨k, hk⟩` from `Nat.exists_eq_add_of_le' (Finset.le_sup (f := f) hx)`. Use `show p ^ s.sup f • x ∈ Λ`. Rewrite using `[hk, pow_add, mul_smul]`. Conclude with `Λ.smul_mem _ (hf x)`.

Conclude with `this hv`.
-/
theorem exists_pow_smul_le (L : LocE F E) {ϖ : 𝒪[F]} (hϖ : Irreducible ϖ) (p : L.O)
    (hp : (p : E) = algebraMap F E (ϖ : F)) {n : ℕ}
    {Λ Λ' : Submodule L.O (Fin n → E)} (hΛ : IsLat L Λ) (hΛ' : Λ'.FG) :
    ∃ j : ℕ, ∀ v ∈ Λ', p ^ j • v ∈ Λ := by
  obtain ⟨s, rfl⟩ := hΛ'
  choose f hf using exists_pow_smul_mem L hϖ p hp hΛ
  refine ⟨s.sup f, fun v hv => ?_⟩
  have : Submodule.span L.O (s : Set (Fin n → E)) ≤
      Λ.comap (LinearMap.lsmul L.O (Fin n → E) (p ^ s.sup f)) := by
    rw [Submodule.span_le]
    intro x hx
    obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le' (Finset.le_sup (f := f) hx)
    show p ^ s.sup f • x ∈ Λ
    rw [hk, pow_add, mul_smul]
    exact Λ.smul_mem _ (hf x)
  exact this hv

/- English proof (translation)
Introduce `F _ _ _ _ _ E _ _ _ L n Λ Λ' hΛ hΛ' H`. Use `⟨?_, fun g => ⟨⟨?_, ?_⟩, ?_⟩⟩` and prove the remaining obligations. Take `⟨ϖ, hϖ⟩` from `IsDiscreteValuationRing.exists_irreducible 𝒪[F]`. Take `⟨-, -, -, -, hO, hcard, hq, -⟩` from `GlobalTheory.UnramOrder.order_facts L ϖ hϖ`. Set `p : L.O` to `⟨algebraMap F E (ϖ : F), (hO _).2 ϖ.2⟩`.

Establish `hp : (p : E) = algebraMap F E (ϖ : F)` using `rfl`. Take `⟨a, ha⟩` from `exists_pow_smul_le L hϖ p hp hΛ hΛ'.1`. Take `⟨b, hb⟩` from `exists_pow_smul_le L hϖ p hp hΛ' hΛ.1`. Establish `hfin : Finite (L.O ⧸ Ideal.span {p ^ (a + b)})`. Establish `h1` using `hcard (a + b)`.

Establish `h2 : {y : L.O | (y : E) = algebraMap F E ((ϖ : F) ^ (a + b))} = {p ^ (a + b)}`. Use extensionality with `y`. Simplify using `only [Set.mem_setOf_eq, Set.mem_singleton_iff, Subtype.ext_iff, SubmonoidClass.coe_pow, hp, map_pow]`. Rewrite `h1` using `[h2]`. Apply `Nat.finite_of_card_ne_zero` to reduce the goal to its premises.

Rewrite using `[h1]`. Conclude with `pow_ne_zero _ (by omega)`. Establish `hF` using `finite_between (p ^ (a + b)) Λ hΛ.1`. Establish `hu : IsUnit ((p ^ a : L.O) : E)`. Rewrite using `[SubmonoidClass.coe_pow, hp]`.

Conclude with `((IsUnit.mk0 _ (fun h => hϖ.ne_zero (Subtype.ext h))).map (algebraMap F E)).pow a`. Establish `hinj : Function.Injective (LinearMap.lsmul L.O (Fin n → E) (p ^ a))`. Introduce `x y h`. Conclude with `hu.smul_left_cancel.1 h`. Establish `hcomm : ∀ (g : (Fin n → E) ≃ₗ[E] (Fin n → E)) (r : L.O) (v : Fin n → E), g • (r • v) = r • (g • v)` using `fun g r v => map_smul g (r : E) v`.

Establish `heq : (H ⊓ stabL L Λ').subgroupOf (H ⊓ stabL L Λ) = MulAction.stabilizer (H ⊓ stabL L Λ :) Λ'`. Use extensionality with `g`. Simplify using `only [Subgroup.mem_subgroupOf, Subgroup.mem_inf, MulAction.mem_stabilizer_iff]`. Conclude with `⟨fun h => h.2, fun h => ⟨g.2.1, h⟩⟩`. Rewrite using `[Subgroup.relIndex, heq, MulAction.index_stabilizer]`.

Use `Set.ncard_ne_zero_of_mem (MulAction.mem_orbit_self Λ') ?_` and prove the remaining obligations. Use `Set.Finite.of_finite_image (f := fun M => Submodule.map (LinearMap.lsmul L.O (Fin n → E) (p ^ a)) M) (hF.subset ?_) (Submodule.map_injective_of_injective hinj).injOn` and prove the remaining obligations. Introduce and unpack `_ ⟨_, ⟨g, rfl⟩, rfl⟩`. Establish `hg : g.1 • Λ = Λ` using `g.2.2`. Use `⟨?_, fun v hv => ?_⟩` and prove the remaining obligations.

Introduce and unpack `_ ⟨w, hw, rfl⟩`. Take `⟨x, hx, rfl⟩` from `(Submodule.mem_smul_pointwise_iff_exists w g.1 Λ').1 hw`. Use `show p ^ a • (g.1 • x) ∈ Λ`. Rewrite using `[← hcomm]`. Conclude with `hg.le (Submodule.smul_mem_pointwise_smul _ _ _ (ha x hx))`.

Rewrite `hv` using `[← hg]`. Take `⟨x, hx, rfl⟩` from `(Submodule.mem_smul_pointwise_iff_exists v g.1 Λ).1 hv`. Use `⟨g.1 • (p ^ b • x), Submodule.smul_mem_pointwise_smul _ g.1 _ (hb x hx), ?_⟩` and prove the remaining obligations. Rewrite using `[LinearMap.lsmul_apply, hcomm, pow_add, mul_smul]`. Conclude with `hΛ.1.map _`.

Rewrite using `[eq_top_iff]`. Introduce `v _`. Establish `hv : g.symm v ∈ Submodule.span E (Λ : Set (Fin n → E))` using `by rw [hΛ.2]; trivial`. Establish `h2` using `Submodule.apply_mem_span_image_of_mem_span (g : (Fin n → E) →ₗ[E] (Fin n → E)) hv`. Simplify using `only [LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply] at h2`.

Use `Submodule.span_mono ?_ h2` and prove the remaining obligations. Introduce and unpack `_ ⟨x, hx, rfl⟩`. Conclude with `Submodule.smul_mem_pointwise_smul _ g _ hx`. Conclude with `MulAction.stabilizer_smul_eq_stabilizer_map_conj g Λ`.
-/
theorem stab_commensurable : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ {n : ℕ} (Λ Λ' : Submodule L.O (Fin n → E)), IsLat L Λ → IsLat L Λ' → ∀ H : Subgroup ((Fin n → E) ≃ₗ[E] (Fin n → E)), (H ⊓ stabL L Λ').relIndex (H ⊓ stabL L Λ) ≠ 0 ∧ ∀ g : ((Fin n → E) ≃ₗ[E] (Fin n → E)), IsLat L (g • Λ) ∧ stabL L (g • Λ) = MulAut.conj g • stabL L Λ := by
  intro F _ _ _ _ _ E _ _ _ L n Λ Λ' hΛ hΛ' H
  refine ⟨?_, fun g => ⟨⟨?_, ?_⟩, ?_⟩⟩
  · obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[F]
    obtain ⟨-, -, -, -, hO, hcard, hq, -⟩ := GlobalTheory.UnramOrder.order_facts L ϖ hϖ
    let p : L.O := ⟨algebraMap F E (ϖ : F), (hO _).2 ϖ.2⟩
    have hp : (p : E) = algebraMap F E (ϖ : F) := rfl
    obtain ⟨a, ha⟩ := exists_pow_smul_le L hϖ p hp hΛ hΛ'.1
    obtain ⟨b, hb⟩ := exists_pow_smul_le L hϖ p hp hΛ' hΛ.1
    have hfin : Finite (L.O ⧸ Ideal.span {p ^ (a + b)}) := by
      have h1 := hcard (a + b)
      have h2 : {y : L.O | (y : E) = algebraMap F E ((ϖ : F) ^ (a + b))} = {p ^ (a + b)} := by
        ext y
        simp only [Set.mem_setOf_eq, Set.mem_singleton_iff, Subtype.ext_iff,
          SubmonoidClass.coe_pow, hp, map_pow]
      rw [h2] at h1
      apply Nat.finite_of_card_ne_zero
      rw [h1]
      exact pow_ne_zero _ (by omega)
    have hF := finite_between (p ^ (a + b)) Λ hΛ.1
    have hu : IsUnit ((p ^ a : L.O) : E) := by
      rw [SubmonoidClass.coe_pow, hp]
      exact ((IsUnit.mk0 _ (fun h => hϖ.ne_zero (Subtype.ext h))).map (algebraMap F E)).pow a
    have hinj : Function.Injective (LinearMap.lsmul L.O (Fin n → E) (p ^ a)) := by
      intro x y h
      exact hu.smul_left_cancel.1 h
    have hcomm : ∀ (g : (Fin n → E) ≃ₗ[E] (Fin n → E)) (r : L.O) (v : Fin n → E),
        g • (r • v) = r • (g • v) := fun g r v => map_smul g (r : E) v
    have heq : (H ⊓ stabL L Λ').subgroupOf (H ⊓ stabL L Λ) =
        MulAction.stabilizer (H ⊓ stabL L Λ :) Λ' := by
      ext g
      simp only [Subgroup.mem_subgroupOf, Subgroup.mem_inf, MulAction.mem_stabilizer_iff]
      exact ⟨fun h => h.2, fun h => ⟨g.2.1, h⟩⟩
    rw [Subgroup.relIndex, heq, MulAction.index_stabilizer]
    refine Set.ncard_ne_zero_of_mem (MulAction.mem_orbit_self Λ') ?_
    refine Set.Finite.of_finite_image
      (f := fun M => Submodule.map (LinearMap.lsmul L.O (Fin n → E) (p ^ a)) M) (hF.subset ?_)
      (Submodule.map_injective_of_injective hinj).injOn
    rintro _ ⟨_, ⟨g, rfl⟩, rfl⟩
    have hg : g.1 • Λ = Λ := g.2.2
    refine ⟨?_, fun v hv => ?_⟩
    · rintro _ ⟨w, hw, rfl⟩
      obtain ⟨x, hx, rfl⟩ := (Submodule.mem_smul_pointwise_iff_exists w g.1 Λ').1 hw
      show p ^ a • (g.1 • x) ∈ Λ
      rw [← hcomm]
      exact hg.le (Submodule.smul_mem_pointwise_smul _ _ _ (ha x hx))
    · rw [← hg] at hv
      obtain ⟨x, hx, rfl⟩ := (Submodule.mem_smul_pointwise_iff_exists v g.1 Λ).1 hv
      refine ⟨g.1 • (p ^ b • x), Submodule.smul_mem_pointwise_smul _ g.1 _ (hb x hx), ?_⟩
      rw [LinearMap.lsmul_apply, hcomm, pow_add, mul_smul]
  · exact hΛ.1.map _
  · rw [eq_top_iff]
    intro v _
    have hv : g.symm v ∈ Submodule.span E (Λ : Set (Fin n → E)) := by rw [hΛ.2]; trivial
    have h2 := Submodule.apply_mem_span_image_of_mem_span (g : (Fin n → E) →ₗ[E] (Fin n → E)) hv
    simp only [LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply] at h2
    refine Submodule.span_mono ?_ h2
    rintro _ ⟨x, hx, rfl⟩
    exact Submodule.smul_mem_pointwise_smul _ g _ hx
  · exact MulAction.stabilizer_smul_eq_stabilizer_map_conj g Λ

end GlobalTheory.LatComm

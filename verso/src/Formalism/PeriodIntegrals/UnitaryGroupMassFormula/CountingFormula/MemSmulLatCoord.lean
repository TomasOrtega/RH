import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CountingFormula.DensGS
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CountingFormula.DensGSDvr

noncomputable section

namespace PI.UnitaryGroupMassFormula.CntFormula

open NumberField Formalism.MainNotions.S
open Classical ValuativeRel

section Coord

variable {F E : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [CommRing E] [Algebra F E]
  [TopologicalSpace E] [MeasurableSpace E] {M : Loc.Model F E}
  {V : Type} [AddCommGroup V] [Module E V]

def InP (ϖ : 𝒪[F]) (u : F) : Prop := ∃ o : 𝒪[F], u = (ϖ : F) * o

/- English proof (translation)
Use `first`. Consider the case `(rw [e.commutes]; rfl)`. Consider the case `simp [e.commutes]`.
-/
theorem e_alg (e : E ≃ₐ[F] F × F) (c : F) : e (algebraMap F E c) = (c, c) := by
  first
  | (rw [e.commutes]; rfl)
  | simp [e.commutes]

/- English proof (translation)
Rewrite using `[hπ, e_alg]`.
-/
theorem pi_smulF (e : E ≃ₐ[F] F × F) {n : ℕ} (π : V ≃+ (Fin n → F) × (Fin n → F))
    (hπ : ∀ (a : E) (x : V), π (a • x) = ((e a).1 • (π x).1, (e a).2 • (π x).2)) (c : F) (x : V) :
    π (algebraMap F E c • x) = (c • (π x).1, c • (π x).2) := by
  rw [hπ, e_alg]

/- English proof (translation)
Unfold `Loc.HermSp.smulLat`. Prove the components needed by the constructor for the conclusion. Introduce `hx`. Proceed by induction on `hx using Submodule.span_induction with`. Consider the case `mem z hz`.

Take `⟨y, hy, rfl⟩` from `hz`. Conclude with `⟨y, hy, rfl⟩`. Consider the case `zero => exact ⟨0, Λ.zero_mem, (smul_zero c).symm⟩`. Consider the case `add z w _ _ hz hw`. Take `⟨y, hy, rfl⟩` from `hz`.

Take `⟨y', hy', rfl⟩` from `hw`. Conclude with `⟨y + y', Λ.add_mem hy hy', (smul_add c y y').symm⟩`. Consider the case `smul a z _ hz`. Take `⟨y, hy, rfl⟩` from `hz`. Use `⟨a • y, Λ.smul_mem a hy, ?_⟩` and prove the remaining obligations.

Use `first`. Consider the case `exact smul_comm a c y`. Consider the case `exact (smul_comm c a y).symm`. Consider the case `(show ((a : E)) • c • y = c • ((a : E) • y); exact smul_comm _ _ _)`. Introduce and unpack `⟨y, hy, rfl⟩`.

Conclude with `Submodule.subset_span ⟨y, hy, rfl⟩`.
-/
theorem mem_smulLat_iff' (H : Loc.HermSp M V) (Λ : Submodule M.L.O V) (c : E) (x : V) :
    x ∈ H.smulLat c Λ ↔ ∃ y ∈ Λ, x = c • y := by
  unfold Loc.HermSp.smulLat
  constructor
  · intro hx
    induction hx using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨y, hy, rfl⟩ := hz
      exact ⟨y, hy, rfl⟩
    | zero => exact ⟨0, Λ.zero_mem, (smul_zero c).symm⟩
    | add z w _ _ hz hw =>
      obtain ⟨y, hy, rfl⟩ := hz
      obtain ⟨y', hy', rfl⟩ := hw
      exact ⟨y + y', Λ.add_mem hy hy', (smul_add c y y').symm⟩
    | smul a z _ hz =>
      obtain ⟨y, hy, rfl⟩ := hz
      refine ⟨a • y, Λ.smul_mem a hy, ?_⟩
      first
      | exact smul_comm a c y
      | exact (smul_comm c a y).symm
      | (show ((a : E)) • c • y = c • ((a : E) • y); exact smul_comm _ _ _)
  · rintro ⟨y, hy, rfl⟩
    exact Submodule.subset_span ⟨y, hy, rfl⟩

/- English proof (translation)
Rewrite using `[mem_smulLat_iff']`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨y, hy, rfl⟩`. Rewrite using `[pi_smulF e π hπa]`. Take `⟨h1, h2⟩` from `(hπL y).1 hy`.

Conclude with `⟨fun k => ⟨⟨_, h1 k⟩, by simp [Pi.smul_apply, smul_eq_mul]⟩, fun k => ⟨⟨_, h2 k⟩, by simp [Pi.smul_apply, smul_eq_mul]⟩⟩`. Introduce and unpack `⟨h1, h2⟩ choose o1 ho1 using h1 choose o2 ho2 using h2`. Use `⟨π.symm ((fun k => (o1 k : F)), (fun k => (o2 k : F))), ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[hπL, AddEquiv.apply_symm_apply]`. Conclude with `⟨fun k => (o1 k).2, fun k => (o2 k).2⟩`.

Apply `π.injective` to reduce the goal to its premises. Rewrite using `[pi_smulF e π hπa, AddEquiv.apply_symm_apply]`. Apply the tactic sequence `ext k <;> simp [ho1, ho2, Pi.smul_apply, smul_eq_mul]`.
-/
theorem mem_smulLat_coord (e : E ≃ₐ[F] F × F) (H : Loc.HermSp M V) (Λ : Submodule M.L.O V) {n : ℕ}
    (π : V ≃+ (Fin n → F) × (Fin n → F))
    (hπa : ∀ (a : E) (x : V), π (a • x) = ((e a).1 • (π x).1, (e a).2 • (π x).2))
    (hπL : ∀ x : V, x ∈ Λ ↔ (∀ k, (π x).1 k ∈ 𝒪[F]) ∧ ∀ k, (π x).2 k ∈ 𝒪[F]) (ϖ : 𝒪[F]) (x : V) :
    x ∈ H.smulLat (algebraMap F E ϖ) Λ ↔ (∀ k, InP ϖ ((π x).1 k)) ∧ ∀ k, InP ϖ ((π x).2 k) := by
  rw [mem_smulLat_iff']
  constructor
  · rintro ⟨y, hy, rfl⟩
    rw [pi_smulF e π hπa]
    obtain ⟨h1, h2⟩ := (hπL y).1 hy
    exact ⟨fun k => ⟨⟨_, h1 k⟩, by simp [Pi.smul_apply, smul_eq_mul]⟩,
      fun k => ⟨⟨_, h2 k⟩, by simp [Pi.smul_apply, smul_eq_mul]⟩⟩
  · rintro ⟨h1, h2⟩
    choose o1 ho1 using h1
    choose o2 ho2 using h2
    refine ⟨π.symm ((fun k => (o1 k : F)), (fun k => (o2 k : F))), ?_, ?_⟩
    · rw [hπL, AddEquiv.apply_symm_apply]
      exact ⟨fun k => (o1 k).2, fun k => (o2 k).2⟩
    · apply π.injective
      rw [pi_smulF e π hπa, AddEquiv.apply_symm_apply]
      ext k <;> simp [ho1, ho2, Pi.smul_apply, smul_eq_mul]

/- English proof (translation)
Establish `key : ∀ d : 𝒪[F], InP ϖ (d : F) ↔ ϖ ∣ d`. Introduce `d`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨o, ho⟩`. Conclude with `⟨o, Subtype.ext (by simp [ho])⟩`.

Introduce and unpack `⟨o, rfl⟩`. Conclude with `⟨o, by simp⟩`. Establish `e1 : resF F u = IsLocalRing.residue 𝒪[F] ⟨u, hu⟩` using `by first`. Consider the case `simp [resF, hu]`. Consider the case `(unfold resF; rw [dif_pos hu])`.

Establish `e2 : resF F w = IsLocalRing.residue 𝒪[F] ⟨w, hw⟩` using `by first`. Consider the case `simp [resF, hw]`. Consider the case `(unfold resF; rw [dif_pos hw])`. Establish `hs : (u - w : F) = ((⟨u, hu⟩ - ⟨w, hw⟩ : 𝒪[F]) : F)` using `rfl`. Establish `hm : IsLocalRing.maximalIdeal 𝒪[F] = Ideal.span {ϖ}` using `by first`.

Consider the case `exact hϖ.maximalIdeal_eq`. Consider the case `exact (IsDiscreteValuationRing.irreducible_iff_uniformizer _).1 hϖ`. Rewrite using `[e1, e2, hs, key, ← sub_eq_zero, ← map_sub, IsLocalRing.residue_eq_zero_iff, hm, Ideal.mem_span_singleton]`.
-/
theorem inP_sub_iff [IsDiscreteValuationRing 𝒪[F]] {ϖ : 𝒪[F]} (hϖ : Irreducible ϖ) {u w : F}
    (hu : u ∈ 𝒪[F]) (hw : w ∈ 𝒪[F]) : InP ϖ (u - w) ↔ resF F u = resF F w := by
  have key : ∀ d : 𝒪[F], InP ϖ (d : F) ↔ ϖ ∣ d := by
    intro d
    constructor
    · rintro ⟨o, ho⟩
      exact ⟨o, Subtype.ext (by simp [ho])⟩
    · rintro ⟨o, rfl⟩
      exact ⟨o, by simp⟩
  have e1 : resF F u = IsLocalRing.residue 𝒪[F] ⟨u, hu⟩ := by
    first
    | simp [resF, hu]
    | (unfold resF; rw [dif_pos hu])
  have e2 : resF F w = IsLocalRing.residue 𝒪[F] ⟨w, hw⟩ := by
    first
    | simp [resF, hw]
    | (unfold resF; rw [dif_pos hw])
  have hs : (u - w : F) = ((⟨u, hu⟩ - ⟨w, hw⟩ : 𝒪[F]) : F) := rfl
  have hm : IsLocalRing.maximalIdeal 𝒪[F] = Ideal.span {ϖ} := by
    first
    | exact hϖ.maximalIdeal_eq
    | exact (IsDiscreteValuationRing.irreducible_iff_uniformizer _).1 hϖ
  rw [e1, e2, hs, key, ← sub_eq_zero, ← map_sub, IsLocalRing.residue_eq_zero_iff, hm, Ideal.mem_span_singleton]

/- English proof (translation)
Rewrite using `[Submodule.Quotient.eq, mem_smulLat_coord e H Λ π hπa hπL ϖ]`. Take `⟨hx1, hx2⟩` from `(hπL x).1 hx`. Take `⟨hy1, hy2⟩` from `(hπL y).1 hy`. Simplify using `only [map_sub, Prod.fst_sub, Prod.snd_sub, Pi.sub_apply]`. Conclude with `and_congr (forall_congr' fun k => inP_sub_iff hϖ (hx1 k) (hy1 k)) (forall_congr' fun k => inP_sub_iff hϖ (hx2 k) (hy2 k))`.
-/
theorem mk_eq_iff [IsDiscreteValuationRing 𝒪[F]] (e : E ≃ₐ[F] F × F) (H : Loc.HermSp M V)
    (Λ : Submodule M.L.O V) {n : ℕ} (π : V ≃+ (Fin n → F) × (Fin n → F))
    (hπa : ∀ (a : E) (x : V), π (a • x) = ((e a).1 • (π x).1, (e a).2 • (π x).2))
    (hπL : ∀ x : V, x ∈ Λ ↔ (∀ k, (π x).1 k ∈ 𝒪[F]) ∧ ∀ k, (π x).2 k ∈ 𝒪[F]) {ϖ : 𝒪[F]} (hϖ : Irreducible ϖ)
    {x y : V} (hx : x ∈ Λ) (hy : y ∈ Λ) :
    Submodule.Quotient.mk (p := H.smulLat (algebraMap F E ϖ) Λ) x =
        Submodule.Quotient.mk (p := H.smulLat (algebraMap F E ϖ) Λ) y ↔
      (∀ k, resF F ((π x).1 k) = resF F ((π y).1 k)) ∧ ∀ k, resF F ((π x).2 k) = resF F ((π y).2 k) := by
  rw [Submodule.Quotient.eq, mem_smulLat_coord e H Λ π hπa hπL ϖ]
  obtain ⟨hx1, hx2⟩ := (hπL x).1 hx
  obtain ⟨hy1, hy2⟩ := (hπL y).1 hy
  simp only [map_sub, Prod.fst_sub, Prod.snd_sub, Pi.sub_apply]
  exact and_congr (forall_congr' fun k => inP_sub_iff hϖ (hx1 k) (hy1 k))
    (forall_congr' fun k => inP_sub_iff hϖ (hx2 k) (hy2 k))

/- English proof (translation)
Rewrite using `[Submodule.mem_span_singleton]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨a, rfl⟩`. Establish `ha` using `(hO a).1 a.2`. Apply the tactic sequence `refine ⟨⟨⟨(e a).1, ha.1⟩, ?_⟩, ⟨⟨(e a).2, ha.2⟩, ?_⟩⟩ <;>`.

Simplify using `[Subring.smul_def, Submonoid.smul_def, Subalgebra.smul_def, map_mul, e_alg, mul_comm]`. Introduce and unpack `⟨⟨o1, h1⟩, ⟨o2, h2⟩⟩`. Establish `hmem : e.symm ((o1 : F), (o2 : F)) ∈ M.L.O`. Rewrite using `[hO, AlgEquiv.apply_symm_apply]`. Conclude with `⟨o1.2, o2.2⟩`.

Use `⟨⟨_, hmem⟩, ?_⟩` and prove the remaining obligations. Apply `e.injective` to reduce the goal to its premises. Apply the tactic sequence `ext <;> simp [Subring.smul_def, Submonoid.smul_def, Subalgebra.smul_def, map_mul, e_alg, h1, h2, mul_comm]`.
-/
theorem mem_span_irr_iff (e : E ≃ₐ[F] F × F)
    (hO : ∀ x : E, x ∈ M.L.O ↔ (e x).1 ∈ 𝒪[F] ∧ (e x).2 ∈ 𝒪[F]) (ϖ : 𝒪[F]) (z : E) :
    z ∈ Submodule.span M.L.O {algebraMap F E (ϖ : F)} ↔ InP ϖ (e z).1 ∧ InP ϖ (e z).2 := by
  rw [Submodule.mem_span_singleton]
  constructor
  · rintro ⟨a, rfl⟩
    have ha := (hO a).1 a.2
    refine ⟨⟨⟨(e a).1, ha.1⟩, ?_⟩, ⟨⟨(e a).2, ha.2⟩, ?_⟩⟩ <;>
      simp [Subring.smul_def, Submonoid.smul_def, Subalgebra.smul_def, map_mul, e_alg, mul_comm]
  · rintro ⟨⟨o1, h1⟩, ⟨o2, h2⟩⟩
    have hmem : e.symm ((o1 : F), (o2 : F)) ∈ M.L.O := by
      rw [hO, AlgEquiv.apply_symm_apply]
      exact ⟨o1.2, o2.2⟩
    refine ⟨⟨_, hmem⟩, ?_⟩
    apply e.injective
    ext <;> simp [Subring.smul_def, Submonoid.smul_def, Subalgebra.smul_def, map_mul, e_alg, h1, h2, mul_comm]

/- English proof (translation)
Establish `hc : ∀ (a : F) (ha : a ∈ 𝒪[F]), resF F a = IsLocalRing.residue 𝒪[F] ⟨a, ha⟩`. Introduce `a ha`. Use `first`. Consider the case `simp [resF, ha]`. Consider the case `(unfold resF; rw [dif_pos ha])`.

Establish `hsum : (∑ k, ∑ l, x k * (Ph k l : F) * y l) = ((∑ k, ∑ l, (⟨x k, hx k⟩ : 𝒪[F]) * Ph k l * (⟨y l, hy l⟩ : 𝒪[F]) : 𝒪[F]) : F)` using `by first`. Consider the case `(push_cast; rfl)`. Consider the case `(simp only [AddSubmonoidClass.coe_finset_sum, MulMemClass.coe_mul]; rfl)`. Consider the case `(simp only [AddSubmonoidClass.coe_finset_sum, MulMemClass.coe_mul])`. Consider the case `(push_cast; simp)`.

Consider the case `simp`. Establish `hxk : ∀ k, resF F (x k) = IsLocalRing.residue 𝒪[F] ⟨x k, hx k⟩` using `fun k => hc _ (hx k)`. Establish `hyl : ∀ l, resF F (y l) = IsLocalRing.residue 𝒪[F] ⟨y l, hy l⟩` using `fun l => hc _ (hy l)`. Establish `hc' : ∀ z : 𝒪[F], resF F (z : F) = IsLocalRing.residue 𝒪[F] z` using `fun z => hc z z.2`. Rewrite using `[hsum, hc']`.

Simplify using `only [map_sum, map_mul, hxk, hyl]`.
-/
theorem resF_bil {n : ℕ} (x y : Fin n → F) (hx : ∀ k, x k ∈ 𝒪[F]) (hy : ∀ k, y k ∈ 𝒪[F])
    (Ph : Matrix (Fin n) (Fin n) 𝒪[F]) :
    resF F (∑ k, ∑ l, x k * (Ph k l : F) * y l) =
      ∑ k, ∑ l, resF F (x k) * IsLocalRing.residue 𝒪[F] (Ph k l) * resF F (y l) := by
  have hc : ∀ (a : F) (ha : a ∈ 𝒪[F]), resF F a = IsLocalRing.residue 𝒪[F] ⟨a, ha⟩ := by
    intro a ha
    first
    | simp [resF, ha]
    | (unfold resF; rw [dif_pos ha])
  have hsum : (∑ k, ∑ l, x k * (Ph k l : F) * y l) =
      ((∑ k, ∑ l, (⟨x k, hx k⟩ : 𝒪[F]) * Ph k l * (⟨y l, hy l⟩ : 𝒪[F]) : 𝒪[F]) : F) := by
    first
    | (push_cast; rfl)
    | (simp only [AddSubmonoidClass.coe_finset_sum, MulMemClass.coe_mul]; rfl)
    | (simp only [AddSubmonoidClass.coe_finset_sum, MulMemClass.coe_mul])
    | (push_cast; simp)
    | simp
  have hxk : ∀ k, resF F (x k) = IsLocalRing.residue 𝒪[F] ⟨x k, hx k⟩ := fun k => hc _ (hx k)
  have hyl : ∀ l, resF F (y l) = IsLocalRing.residue 𝒪[F] ⟨y l, hy l⟩ := fun l => hc _ (hy l)
  have hc' : ∀ z : 𝒪[F], resF F (z : F) = IsLocalRing.residue 𝒪[F] z := fun z => hc z z.2
  rw [hsum, hc']
  simp only [map_sum, map_mul, hxk, hyl]

/- English proof (translation)
Conclude with `sum_mem fun k _ => sum_mem fun l _ => mul_mem (mul_mem (hx k) (Ph k l).2) (hy l)`.
-/
theorem bil_mem {n : ℕ} (x y : Fin n → F) (hx : ∀ k, x k ∈ 𝒪[F]) (hy : ∀ k, y k ∈ 𝒪[F])
    (Ph : Matrix (Fin n) (Fin n) 𝒪[F]) : (∑ k, ∑ l, x k * (Ph k l : F) * y l) ∈ 𝒪[F] := by
  exact sum_mem fun k _ => sum_mem fun l _ => mul_mem (mul_mem (hx k) (Ph k l).2) (hy l)

end Coord

end PI.UnitaryGroupMassFormula.CntFormula

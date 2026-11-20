import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.ResidualSpectrumByClass
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.CuspidalMultiplicityOne
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.T2SpaceAdelicGeneralLinearGroupNumberField
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.CuspDiscreteDecompositionGL
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsSpanFormsNeBot

open NumberField IsDedekindDomain MeasureTheory Formalism.L2.Host GlobalTheory.AutomorphicL2Unitary GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.DiscSpec GlobalTheory.CuspRep.CuspidalL2GL GlobalTheory.Published

noncomputable section

namespace GlobalTheory.LevelTypeProj

/- English proof (translation)
Establish `hbot : (Submodule.span ℂ (Set.range ev)).dualCoannihilator = ⊥`. Rewrite using `[eq_bot_iff]`. Introduce `v hv`. Rewrite `hv` using `[Submodule.mem_dualCoannihilator]`. Conclude with `(Submodule.mem_bot ℂ).2 (hev v fun x => hv (ev x) (Submodule.subset_span ⟨x, rfl⟩))`.

Rewrite using `[← Subspace.dualCoannihilator_dualAnnihilator_eq (W := Submodule.span ℂ (Set.range ev)), hbot, Submodule.dualAnnihilator_bot]`.
-/
theorem span_eval_eq_top {X M : Type*} [AddCommGroup M] [Module ℂ M] [FiniteDimensional ℂ M]
    (ev : X → Module.Dual ℂ M) (hev : ∀ v, (∀ x, ev x v = 0) → v = 0) :
    Submodule.span ℂ (Set.range ev) = ⊤ := by
  have hbot : (Submodule.span ℂ (Set.range ev)).dualCoannihilator = ⊥ := by
    rw [eq_bot_iff]
    intro v hv
    rw [Submodule.mem_dualCoannihilator] at hv
    exact (Submodule.mem_bot ℂ).2 (hev v fun x => hv (ev x) (Submodule.subset_span ⟨x, rfl⟩))
  rw [← Subspace.dualCoannihilator_dualAnnihilator_eq (W := Submodule.span ℂ (Set.range ev)), hbot,
    Submodule.dualAnnihilator_bot]

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {N : ℕ}

/- English proof (translation)
Simplify using `only [finRep, cptRep, MonoidHom.comp_apply]`. Rewrite using `[← Module.End.mul_apply, ← map_mul, ← infGL_comm, map_mul, Module.End.mul_apply]`.
-/
theorem finRep_cptRep (l : GL (Fin N) (Af E)) (k : Kinf E N) (φ : Sm E N) :
    finRep E N l (cptRep E N k φ) = cptRep E N k (finRep E N l φ) := by
  simp only [finRep, cptRep, MonoidHom.comp_apply]
  rw [← Module.End.mul_apply, ← map_mul, ← infGL_comm, map_mul, Module.End.mul_apply]

def orbitSpan (L : Subgroup (GL (Fin N) (Af E))) (ψ : Sm E N) : Submodule ℂ (Sm E N) :=
  Submodule.span ℂ {v | ∃ l ∈ L, ∃ k, v = finRep E N l (cptRep E N k ψ)}

/- English proof (translation)
The claim follows from `Submodule.subset_span ⟨1, L.one_mem, 1, by rw [map_one, map_one, Module.End.one_apply, Module.End.one_apply]⟩`.
-/
theorem mem_orbitSpan_self (L : Subgroup (GL (Fin N) (Af E))) (ψ : Sm E N) : ψ ∈ orbitSpan L ψ :=
  Submodule.subset_span ⟨1, L.one_mem, 1, by rw [map_one, map_one, Module.End.one_apply, Module.End.one_apply]⟩

/- English proof (translation)
The claim follows from `Submodule.span_le.2 (by rintro _ ⟨l, -, k, rfl⟩; exact hJ (.fin l) _ (hJ (.cpt k) _ hψ))`.
-/
theorem orbitSpan_le {J : Submodule ℂ (Sm E N)} (hJ : IsStable J) (L : Subgroup (GL (Fin N) (Af E)))
    {ψ : Sm E N} (hψ : ψ ∈ J) : orbitSpan L ψ ≤ J :=
  Submodule.span_le.2 (by rintro _ ⟨l, -, k, rfl⟩; exact hJ (.fin l) _ (hJ (.cpt k) _ hψ))

/- English proof (translation)
Proceed by induction on `hv using Submodule.span_induction with`. Consider the case `mem x hx`. Take `⟨l, hl, k, rfl⟩` from `hx`. Apply `Submodule.subset_span` to reduce the goal to its premises. Use `⟨l' * l, L.mul_mem hl' hl, k, ?_⟩` and prove the remaining obligations.

Rewrite using `[map_mul (finRep E N), Module.End.mul_apply]`. Consider the case `zero => rw [map_zero]`. Conclude with `zero_mem _`. Consider the case `add x y _ _ hx hy => rw [map_add]`. Conclude with `add_mem hx hy`.

Consider the case `smul c x _ hx => rw [map_smul]`. Conclude with `Submodule.smul_mem _ c hx`.
-/
theorem finRep_mem_orbitSpan {L : Subgroup (GL (Fin N) (Af E))} {ψ : Sm E N} {l' : GL (Fin N) (Af E)}
    (hl' : l' ∈ L) {v : Sm E N} (hv : v ∈ orbitSpan L ψ) : finRep E N l' v ∈ orbitSpan L ψ := by
  induction hv using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨l, hl, k, rfl⟩ := hx
    apply Submodule.subset_span
    refine ⟨l' * l, L.mul_mem hl' hl, k, ?_⟩
    rw [map_mul (finRep E N), Module.End.mul_apply]
  | zero => rw [map_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
  | smul c x _ hx => rw [map_smul]; exact Submodule.smul_mem _ c hx

/- English proof (translation)
Proceed by induction on `hv using Submodule.span_induction with`. Consider the case `mem x hx`. Take `⟨l, hl, k, rfl⟩` from `hx`. Apply `Submodule.subset_span` to reduce the goal to its premises. Use `⟨l, hl, k' * k, ?_⟩` and prove the remaining obligations.

Rewrite using `[map_mul (cptRep E N), Module.End.mul_apply, finRep_cptRep l k' (cptRep E N k ψ)]`. Consider the case `zero => rw [map_zero]`. Conclude with `zero_mem _`. Consider the case `add x y _ _ hx hy => rw [map_add]`. Conclude with `add_mem hx hy`.

Consider the case `smul c x _ hx => rw [map_smul]`. Conclude with `Submodule.smul_mem _ c hx`.
-/
theorem cptRep_mem_orbitSpan {L : Subgroup (GL (Fin N) (Af E))} {ψ : Sm E N} (k' : Kinf E N)
    {v : Sm E N} (hv : v ∈ orbitSpan L ψ) : cptRep E N k' v ∈ orbitSpan L ψ := by
  induction hv using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨l, hl, k, rfl⟩ := hx
    apply Submodule.subset_span
    refine ⟨l, hl, k' * k, ?_⟩
    rw [map_mul (cptRep E N), Module.End.mul_apply, finRep_cptRep l k' (cptRep E N k ψ)]
  | zero => rw [map_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
  | smul c x _ hx => rw [map_smul]; exact Submodule.smul_mem _ c hx

/- English proof (translation)
Take `⟨t, ht⟩` from `hL.elim_finite_subcover (fun l : GL (Fin N) (Af E) => {m | finRep E N (l⁻¹ * m) ψ = ψ}) (fun l => hψ.level.preimage (continuous_mul_left l⁻¹)) (fun m _ => Set.mem_iUnion.2 ⟨m, by simp only [Set.mem_setOf_eq, inv_mul_cancel, map_one]; rfl⟩)`. Use `hψ.kfin` as an intermediate fact. Use `Submodule.finiteDimensional_of_le (S₂ := t.sup fun l => (Submodule.span ℂ (Set.range fun k => cptRep E N k ψ)).map (finRep E N l)) (Submodule.span_le.2 ?_)` and prove the remaining obligations. Introduce and unpack `_ ⟨m, hm, k, rfl⟩`. Take `⟨l, hl, hlm⟩` from `Set.mem_iUnion₂.1 (ht hm)`.

Establish `e : finRep E N m ψ = finRep E N l ψ`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[← Module.End.mul_apply, ← map_mul, mul_inv_cancel_left]`. Use `_ = finRep E N l ψ := by rw [show finRep E N (l⁻¹ * m) ψ = ψ from hlm]`. Use `Finset.le_sup (f := fun l => (Submodule.span ℂ (Set.range fun k => cptRep E N k ψ)).map (finRep E N l)) hl ?_` and prove the remaining obligations.

Use `⟨cptRep E N k ψ, Submodule.subset_span ⟨k, rfl⟩, ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `finRep E N l (cptRep E N k ψ) = finRep E N m (cptRep E N k ψ)`. Rewrite using `[finRep_cptRep, finRep_cptRep, e]`.
-/
theorem orbitSpan_finiteDimensional (L : Subgroup (GL (Fin N) (Af E))) (hL : IsCompact (L : Set (GL (Fin N) (Af E))))
    (ψ : Sm E N) (hψ : IsAutForm ψ) : FiniteDimensional ℂ (orbitSpan L ψ) := by
  classical
  obtain ⟨t, ht⟩ := hL.elim_finite_subcover (fun l : GL (Fin N) (Af E) => {m | finRep E N (l⁻¹ * m) ψ = ψ})
    (fun l => hψ.level.preimage (continuous_mul_left l⁻¹))
    (fun m _ => Set.mem_iUnion.2 ⟨m, by simp only [Set.mem_setOf_eq, inv_mul_cancel, map_one]; rfl⟩)
  have := hψ.kfin
  refine Submodule.finiteDimensional_of_le
    (S₂ := t.sup fun l => (Submodule.span ℂ (Set.range fun k => cptRep E N k ψ)).map (finRep E N l))
    (Submodule.span_le.2 ?_)
  rintro _ ⟨m, hm, k, rfl⟩
  obtain ⟨l, hl, hlm⟩ := Set.mem_iUnion₂.1 (ht hm)
  have e : finRep E N m ψ = finRep E N l ψ := by
    calc finRep E N m ψ = finRep E N l (finRep E N (l⁻¹ * m) ψ) := by
          rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel_left]
      _ = finRep E N l ψ := by rw [show finRep E N (l⁻¹ * m) ψ = ψ from hlm]
  refine Finset.le_sup (f := fun l => (Submodule.span ℂ (Set.range fun k => cptRep E N k ψ)).map (finRep E N l)) hl ?_
  refine ⟨cptRep E N k ψ, Submodule.subset_span ⟨k, rfl⟩, ?_⟩
  change finRep E N l (cptRep E N k ψ) = finRep E N m (cptRep E N k ψ)
  rw [finRep_cptRep, finRep_cptRep, e]

def typePart (L : Subgroup (GL (Fin N) (Af E))) {U : Type} [AddCommGroup U] [Module ℂ U]
    (ρ : Representation ℂ (Kinf E N) U) : Submodule ℂ (Sm E N) where
  carrier := {φ | (∀ k ∈ L, finRep E N k φ = φ) ∧
    ∀ g : GA E N, (fun k : Kinf E N => (cptRep E N k φ).1 g) ∈ AutFin.coeffSpan ρ}
  add_mem' := fun hx hy => ⟨fun k hk => by rw [map_add, hx.1 k hk, hy.1 k hk],
    fun g => add_mem (hx.2 g) (hy.2 g)⟩
  zero_mem' := ⟨fun _ _ => map_zero _, fun _ => by
    simp only [map_zero, ZeroMemClass.coe_zero, Pi.zero_apply]
    exact zero_mem _⟩
  smul_mem' := fun c _ hx => ⟨fun k hk => by rw [map_smul, hx.1 k hk],
    fun g => Submodule.smul_mem _ c (hx.2 g)⟩

/- English proof (translation)
Use `haveI : FiniteDimensional ℂ (S.comap W.subtype) := (Submodule.comapSubtypeEquivOfLe hSW).symm.finiteDimensional`. Set `e` to `Submodule.equivMapOfInjective (toL2ₗ μ W h) hF (S.comap W.subtype)`. Use `haveI : FiniteDimensional ℂ ((S.comap W.subtype).map (toL2ₗ μ W h)) := e.finiteDimensional`. Establish `e1 : ∀ z, toL2ₗ μ W h ((e.symm z : S.comap W.subtype) : W) = (z : L2 (latticeGL E N) μ)` using `fun z => by`. Use `Submodule.coe_equivMapOfInjective_apply (toL2ₗ μ W h) hF (S.comap W.subtype) (e.symm z)` as an intermediate fact.

Rewrite `this` using `[LinearEquiv.apply_symm_apply]`. Conclude with `this.symm`. Use `⟨(S.comap W.subtype).subtype ∘ₗ e.symm.toLinearMap ∘ₗ ((S.comap W.subtype).map (toL2ₗ μ W h)).orthogonalProjectionOnto.toLinearMap ∘ₗ toL2ₗ μ W h, fun x => (e.symm _).2, fun x y hy => ?_⟩` and prove the remaining obligations. Simplify using `only [LinearMap.comp_apply, LinearEquiv.coe_coe, Submodule.subtype_apply, ContinuousLinearMap.coe_coe]`. Rewrite using `[e1]`.

Conclude with `Submodule.starProjection_inner_eq_zero _ _ ⟨y, hy, rfl⟩`.
-/
theorem exists_proj {μ : Measure (GA E N)} [μ.IsHaarMeasure] {W : Submodule ℂ (Sm E N)}
    (h : ∀ φ ∈ W, MemL2Quotient (latticeGL E N) μ φ.1) (hF : Function.Injective (toL2ₗ μ W h))
    (S : Submodule ℂ (Sm E N)) (hSW : S ≤ W) [FiniteDimensional ℂ S] :
    ∃ p : W →ₗ[ℂ] W, (∀ x, (p x).1 ∈ S) ∧
      ∀ x y : W, y.1 ∈ S → inner ℂ (toL2ₗ μ W h x - toL2ₗ μ W h (p x)) (toL2ₗ μ W h y) = 0 := by
  haveI : FiniteDimensional ℂ (S.comap W.subtype) :=
    (Submodule.comapSubtypeEquivOfLe hSW).symm.finiteDimensional
  let e := Submodule.equivMapOfInjective (toL2ₗ μ W h) hF (S.comap W.subtype)
  haveI : FiniteDimensional ℂ ((S.comap W.subtype).map (toL2ₗ μ W h)) := e.finiteDimensional
  have e1 : ∀ z, toL2ₗ μ W h ((e.symm z : S.comap W.subtype) : W) = (z : L2 (latticeGL E N) μ) := fun z => by
    have := Submodule.coe_equivMapOfInjective_apply (toL2ₗ μ W h) hF (S.comap W.subtype) (e.symm z)
    rw [LinearEquiv.apply_symm_apply] at this
    exact this.symm
  refine ⟨(S.comap W.subtype).subtype ∘ₗ e.symm.toLinearMap ∘ₗ
    ((S.comap W.subtype).map (toL2ₗ μ W h)).orthogonalProjectionOnto.toLinearMap ∘ₗ toL2ₗ μ W h,
    fun x => (e.symm _).2, fun x y hy => ?_⟩
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, Submodule.subtype_apply, ContinuousLinearMap.coe_coe]
  rw [e1]
  exact Submodule.starProjection_inner_eq_zero _ _ ⟨y, hy, rfl⟩

/- English proof (translation)
Establish `hm : (b - a).1 ∈ S` using `S.sub_mem hb ha`. Establish `key : toL2ₗ μ W h (b - a) = (toL2ₗ μ W h x - toL2ₗ μ W h a) - (toL2ₗ μ W h x - toL2ₗ μ W h b)`. Rewrite using `[map_sub]`. Normalize the expressions using the abelian group laws. Establish `h0 : inner ℂ (toL2ₗ μ W h (b - a)) (toL2ₗ μ W h (b - a)) = 0`.

Combine the equalities or inequalities in the displayed calculation. Rewrite using `[← key]`. Use `_ = 0 := by rw [inner_sub_left, hxa _ hm, hxb _ hm, sub_zero]`. Conclude with `(sub_eq_zero.1 (hF ((inner_self_eq_zero.1 h0).trans (map_zero _).symm))).symm`.
-/
theorem proj_unique {μ : Measure (GA E N)} [μ.IsHaarMeasure] {W : Submodule ℂ (Sm E N)}
    (h : ∀ φ ∈ W, MemL2Quotient (latticeGL E N) μ φ.1) (hF : Function.Injective (toL2ₗ μ W h))
    {S : Submodule ℂ (Sm E N)} {x a b : W} (ha : a.1 ∈ S) (hb : b.1 ∈ S)
    (hxa : ∀ y : W, y.1 ∈ S → inner ℂ (toL2ₗ μ W h x - toL2ₗ μ W h a) (toL2ₗ μ W h y) = 0)
    (hxb : ∀ y : W, y.1 ∈ S → inner ℂ (toL2ₗ μ W h x - toL2ₗ μ W h b) (toL2ₗ μ W h y) = 0) : a = b := by
  have hm : (b - a).1 ∈ S := S.sub_mem hb ha
  have key : toL2ₗ μ W h (b - a) = (toL2ₗ μ W h x - toL2ₗ μ W h a) - (toL2ₗ μ W h x - toL2ₗ μ W h b) := by
    rw [map_sub]; abel
  have h0 : inner ℂ (toL2ₗ μ W h (b - a)) (toL2ₗ μ W h (b - a)) = 0 := by
    calc inner ℂ (toL2ₗ μ W h (b - a)) (toL2ₗ μ W h (b - a))
        = inner ℂ ((toL2ₗ μ W h x - toL2ₗ μ W h a) - (toL2ₗ μ W h x - toL2ₗ μ W h b)) (toL2ₗ μ W h (b - a)) := by
          rw [← key]
      _ = 0 := by rw [inner_sub_left, hxa _ hm, hxb _ hm, sub_zero]
  exact (sub_eq_zero.1 (hF ((inner_self_eq_zero.1 h0).trans (map_zero _).symm))).symm

/- English proof (translation)
Use `proj_unique h hF (hpS _) (hgS _ (hpS x)) (hp _) fun y hy => ?_` and prove the remaining obligations. Establish `hy' : rt E N g⁻¹ y.1 ∈ W` using `hSW (hgS' _ hy)`. Establish `ey : y = ⟨rt E N g (rt E N g⁻¹ y.1), hgW _ hy'⟩` using `Subtype.ext (by show y.1 = rt E N g (rt E N g⁻¹ y.1)`. Rewrite using `[← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply])`. Rewrite using `[ey, ← R_toL2ₗ h x (hgW _ x.2), ← R_toL2ₗ h (p x) (hgW _ (p x).2), ← R_toL2ₗ h ⟨_, hy'⟩ (hgW _ hy'), ← map_sub]`.

Set `Ui : L2 (latticeGL E N) μ →ₗᵢ[ℂ] L2 (latticeGL E N) μ` to `⟨(R (latticeGL E N) μ g).toLinearMap, norm_R g⟩`. Express the relevant statement in the definitionally equal form `inner ℂ (Ui _) (Ui _) = 0`. Rewrite using `[Ui.inner_map_map]`. Conclude with `hp x ⟨_, hy'⟩ (hgS' _ hy)`.
-/
theorem proj_rt {μ : Measure (GA E N)} [μ.IsHaarMeasure] [μ.IsMulRightInvariant] {W : Submodule ℂ (Sm E N)}
    (h : ∀ φ ∈ W, MemL2Quotient (latticeGL E N) μ φ.1) (hF : Function.Injective (toL2ₗ μ W h))
    {S : Submodule ℂ (Sm E N)} (hSW : S ≤ W) (p : W →ₗ[ℂ] W) (hpS : ∀ x, (p x).1 ∈ S)
    (hp : ∀ x y : W, y.1 ∈ S → inner ℂ (toL2ₗ μ W h x - toL2ₗ μ W h (p x)) (toL2ₗ μ W h y) = 0)
    (g : GA E N) (hgW : ∀ x ∈ W, rt E N g x ∈ W) (hgS : ∀ x ∈ S, rt E N g x ∈ S)
    (hgS' : ∀ x ∈ S, rt E N g⁻¹ x ∈ S) (x : W) :
    p ⟨rt E N g x.1, hgW _ x.2⟩ = ⟨rt E N g (p x).1, hgW _ (p x).2⟩ := by
  refine proj_unique h hF (hpS _) (hgS _ (hpS x)) (hp _) fun y hy => ?_
  have hy' : rt E N g⁻¹ y.1 ∈ W := hSW (hgS' _ hy)
  have ey : y = ⟨rt E N g (rt E N g⁻¹ y.1), hgW _ hy'⟩ := Subtype.ext (by
    show y.1 = rt E N g (rt E N g⁻¹ y.1)
    rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply])
  rw [ey, ← R_toL2ₗ h x (hgW _ x.2), ← R_toL2ₗ h (p x) (hgW _ (p x).2), ← R_toL2ₗ h ⟨_, hy'⟩ (hgW _ hy'),
    ← map_sub]
  let Ui : L2 (latticeGL E N) μ →ₗᵢ[ℂ] L2 (latticeGL E N) μ := ⟨(R (latticeGL E N) μ g).toLinearMap, norm_R g⟩
  change inner ℂ (Ui _) (Ui _) = 0
  rw [Ui.inner_map_map]
  exact hp x ⟨_, hy'⟩ (hgS' _ hy)

/- English proof (translation)
Introduce `E _ _ _ N μ _ _ W J h hW hA hJ hJW L _ hLc U _ _ _ ρ _ ψ hψ`. Establish `hF` using `toL2ₗ_injective h fun φ hφ => ContAut.continuous_of_isOpen_stab E N φ (hA φ hφ).level`. Establish `hSJ : orbitSpan L ψ.1 ≤ J` using `orbitSpan_le hJ L hψ`. Establish `hSW` using `hSJ.trans hJW`. Use `haveI := orbitSpan_finiteDimensional L hLc ψ.1 (hA _ ψ.2)`.

Use `haveI : FiniteDimensional ℂ (orbitSpan L ψ.1 ⊓ typePart L ρ : Submodule ℂ (Sm E N)) := Submodule.finiteDimensional_of_le inf_le_left`. Take `⟨p, hpS, hp⟩` from `exists_proj h hF (orbitSpan L ψ.1) hSW`. Take `⟨q, hqQ, hq⟩` from `exists_proj h hF (orbitSpan L ψ.1 ⊓ typePart L ρ) (inf_le_left.trans hSW)`. Use `⟨q ψ, hSJ (hqQ ψ).1, (hqQ ψ).2.1, (hqQ ψ).2.2, fun φ hφL hφK => ?_⟩` and prove the remaining obligations. Establish `hpT : (p φ).1 ∈ typePart L ρ`.

Use `⟨fun k hk => ?_, fun g => ?_⟩` and prove the remaining obligations. Establish `hc` using `proj_rt h hF hSW p hpS hp (finGL E N k) (fun x hx => hW (.fin k) x hx) (fun x hx => finRep_mem_orbitSpan hk hx) (fun x hx => by rw [← map_inv]; exact finRep_mem_orbitSpan (L.inv_mem hk) hx) φ`. Conclude with `(congrArg Subtype.val hc).symm.trans (congrArg (fun x => (p x).1) (Subtype.ext (hφL k hk)))`. Establish `hcomm : ∀ k : Kinf E N, cptRep E N k (p φ).1 = (p ⟨cptRep E N k φ.1, hW (.cpt k) _ φ.2⟩).1` using `fun k => (congrArg Subtype.val (proj_rt h hF hSW p hpS hp (infGL E N (Unitary.toUnits k)) (fun x hx => hW (.cpt k) x hx) (fun x hx => cptRep_mem_orbitSpan k hx) (fun x hx => by rw [← map_inv, ← map_inv]; exact cptRep_mem_orbitSpan k⁻¹ hx) φ)).symm`. Use `(hA φ φ.2).kfin` as an intermediate fact.

Establish `hVW : Submodule.span ℂ (Set.range fun k => cptRep E N k φ.1) ≤ W` using `Submodule.span_le.2 (by rintro _ ⟨k, rfl⟩; exact hW (.cpt k) _ φ.2)`. Set `V` to `Submodule.span ℂ (Set.range fun k => cptRep E N k φ.1)`. Set `Λ : Module.Dual ℂ V →ₗ[ℂ] (Kinf E N → ℂ)` to `{ toFun := fun ℓ k => ℓ ⟨cptRep E N k φ.1, Submodule.subset_span ⟨k, rfl⟩⟩ map_add' := fun _ _ => rfl map_smul' := fun _ _ => rfl }`. Set `ev : GA E N → Module.Dual ℂ V` to `fun x => (LinearMap.proj x).comp ((Sm E N).subtype.comp V.subtype)`. Establish `htop` using `span_eval_eq_top ev fun v hv => Subtype.ext (Subtype.ext (funext hv))`.

Establish `hle : Submodule.span ℂ (Set.range ev) ≤ (AutFin.coeffSpan ρ).comap Λ` using `Submodule.span_le.2 (by rintro _ ⟨x, rfl⟩; exact hφK x)`. Set `ℓ : Module.Dual ℂ V` to `(LinearMap.proj g).comp ((Sm E N).subtype.comp (W.subtype.comp (p.comp (Submodule.inclusion hVW))))`. Establish `hℓ : Λ ℓ ∈ AutFin.coeffSpan ρ` using `hle (htop ▸ Submodule.mem_top)`. Use `hℓ using 1` and compare the differences between its conclusion and the goal. Use function extensionality and compare the values at `k`.

Rewrite using `[hcomm k]`. Both sides reduce to the same expression. Establish `hψS : ψ.1 ∈ orbitSpan L ψ.1` using `mem_orbitSpan_self L ψ.1`. Establish `hr : (ψ - q ψ).1 ∈ orbitSpan L ψ.1` using `(orbitSpan L ψ.1).sub_mem hψS (hqQ ψ).1`. Establish `h1 : inner ℂ (toL2ₗ μ W h φ) (toL2ₗ μ W h (ψ - q ψ)) = inner ℂ (toL2ₗ μ W h (p φ)) (toL2ₗ μ W h (ψ - q ψ))`.

Use `hp φ (ψ - q ψ) hr` as an intermediate fact. Rewrite `this` using `[inner_sub_left, sub_eq_zero]`. Then use the resulting hypothesis. Establish `h2 : inner ℂ (toL2ₗ μ W h (p φ)) (toL2ₗ μ W h (ψ - q ψ)) = 0`. Use `hq ψ (p φ) ⟨hpS φ, hpT⟩` as an intermediate fact. Rewrite using `[map_sub, ← inner_conj_symm, this, map_zero]`.

Rewrite using `[← sub_eq_zero, ← inner_sub_right, ← map_sub, h1, h2]`.
-/
theorem exists_levelType_part : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (N : ℕ) (μ : Measure (GA E N)) [μ.IsHaarMeasure] [μ.IsMulRightInvariant] (W J : Submodule ℂ (Sm E N)) (h : ∀ φ ∈ W, MemL2Quotient (latticeGL E N) μ φ.1), IsStable W → (∀ φ ∈ W, IsAutForm φ) → IsStable J → J ≤ W → ∀ (L : Subgroup (GL (Fin N) (Af E))), IsOpen (L : Set (GL (Fin N) (Af E))) → IsCompact (L : Set (GL (Fin N) (Af E))) → ∀ (U : Type) [AddCommGroup U] [Module ℂ U] [FiniteDimensional ℂ U] (ρ : Representation ℂ (Kinf E N) U), AutFin.IsContRep ρ → ∀ ψ : W, ψ.1 ∈ J → ∃ ψ' : W, ψ'.1 ∈ J ∧ (∀ k ∈ L, finRep E N k ψ'.1 = ψ'.1) ∧ (∀ g : GA E N, (fun k : Kinf E N => (cptRep E N k ψ'.1).1 g) ∈ AutFin.coeffSpan ρ) ∧ ∀ φ : W, (∀ k ∈ L, finRep E N k φ.1 = φ.1) → (∀ g : GA E N, (fun k : Kinf E N => (cptRep E N k φ.1).1 g) ∈ AutFin.coeffSpan ρ) → inner ℂ (toL2ₗ μ W h φ) (toL2ₗ μ W h ψ) = inner ℂ (toL2ₗ μ W h φ) (toL2ₗ μ W h ψ') := by
  intro E _ _ _ N μ _ _ W J h hW hA hJ hJW L _ hLc U _ _ _ ρ _ ψ hψ
  have hF := toL2ₗ_injective h fun φ hφ => ContAut.continuous_of_isOpen_stab E N φ (hA φ hφ).level
  have hSJ : orbitSpan L ψ.1 ≤ J := orbitSpan_le hJ L hψ
  have hSW := hSJ.trans hJW
  haveI := orbitSpan_finiteDimensional L hLc ψ.1 (hA _ ψ.2)
  haveI : FiniteDimensional ℂ (orbitSpan L ψ.1 ⊓ typePart L ρ : Submodule ℂ (Sm E N)) :=
    Submodule.finiteDimensional_of_le inf_le_left
  obtain ⟨p, hpS, hp⟩ := exists_proj h hF (orbitSpan L ψ.1) hSW
  obtain ⟨q, hqQ, hq⟩ := exists_proj h hF (orbitSpan L ψ.1 ⊓ typePart L ρ) (inf_le_left.trans hSW)
  refine ⟨q ψ, hSJ (hqQ ψ).1, (hqQ ψ).2.1, (hqQ ψ).2.2, fun φ hφL hφK => ?_⟩
  have hpT : (p φ).1 ∈ typePart L ρ := by
    refine ⟨fun k hk => ?_, fun g => ?_⟩
    · have hc := proj_rt h hF hSW p hpS hp (finGL E N k) (fun x hx => hW (.fin k) x hx)
        (fun x hx => finRep_mem_orbitSpan hk hx)
        (fun x hx => by rw [← map_inv]; exact finRep_mem_orbitSpan (L.inv_mem hk) hx) φ
      exact (congrArg Subtype.val hc).symm.trans (congrArg (fun x => (p x).1) (Subtype.ext (hφL k hk)))
    · have hcomm : ∀ k : Kinf E N, cptRep E N k (p φ).1 = (p ⟨cptRep E N k φ.1, hW (.cpt k) _ φ.2⟩).1 := fun k =>
        (congrArg Subtype.val (proj_rt h hF hSW p hpS hp (infGL E N (Unitary.toUnits k))
          (fun x hx => hW (.cpt k) x hx) (fun x hx => cptRep_mem_orbitSpan k hx)
          (fun x hx => by rw [← map_inv, ← map_inv]; exact cptRep_mem_orbitSpan k⁻¹ hx) φ)).symm
      have := (hA φ φ.2).kfin
      have hVW : Submodule.span ℂ (Set.range fun k => cptRep E N k φ.1) ≤ W :=
        Submodule.span_le.2 (by rintro _ ⟨k, rfl⟩; exact hW (.cpt k) _ φ.2)
      let V := Submodule.span ℂ (Set.range fun k => cptRep E N k φ.1)
      let Λ : Module.Dual ℂ V →ₗ[ℂ] (Kinf E N → ℂ) :=
        { toFun := fun ℓ k => ℓ ⟨cptRep E N k φ.1, Submodule.subset_span ⟨k, rfl⟩⟩
          map_add' := fun _ _ => rfl
          map_smul' := fun _ _ => rfl }
      let ev : GA E N → Module.Dual ℂ V := fun x => (LinearMap.proj x).comp ((Sm E N).subtype.comp V.subtype)
      have htop := span_eval_eq_top ev fun v hv => Subtype.ext (Subtype.ext (funext hv))
      have hle : Submodule.span ℂ (Set.range ev) ≤ (AutFin.coeffSpan ρ).comap Λ :=
        Submodule.span_le.2 (by rintro _ ⟨x, rfl⟩; exact hφK x)
      let ℓ : Module.Dual ℂ V :=
        (LinearMap.proj g).comp ((Sm E N).subtype.comp (W.subtype.comp (p.comp (Submodule.inclusion hVW))))
      have hℓ : Λ ℓ ∈ AutFin.coeffSpan ρ := hle (htop ▸ Submodule.mem_top)
      convert hℓ using 1
      funext k
      rw [hcomm k]
      rfl
  have hψS : ψ.1 ∈ orbitSpan L ψ.1 := mem_orbitSpan_self L ψ.1
  have hr : (ψ - q ψ).1 ∈ orbitSpan L ψ.1 := (orbitSpan L ψ.1).sub_mem hψS (hqQ ψ).1
  have h1 : inner ℂ (toL2ₗ μ W h φ) (toL2ₗ μ W h (ψ - q ψ)) =
      inner ℂ (toL2ₗ μ W h (p φ)) (toL2ₗ μ W h (ψ - q ψ)) := by
    have := hp φ (ψ - q ψ) hr
    rwa [inner_sub_left, sub_eq_zero] at this
  have h2 : inner ℂ (toL2ₗ μ W h (p φ)) (toL2ₗ μ W h (ψ - q ψ)) = 0 := by
    have := hq ψ (p φ) ⟨hpS φ, hpT⟩
    rw [map_sub, ← inner_conj_symm, this, map_zero]
  rw [← sub_eq_zero, ← inner_sub_right, ← map_sub, h1, h2]

end GlobalTheory.LevelTypeProj

end

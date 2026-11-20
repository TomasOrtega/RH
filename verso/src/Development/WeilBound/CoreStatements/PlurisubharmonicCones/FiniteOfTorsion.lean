import Mathlib
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.IsEigFrames
import Development.WeilBound.CoreStatements.PlurisubharmonicCones.EmbEquivSymmApply

open NumberField Matrix GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexConjugate ComplexOrder

noncomputable section

namespace LevelTowerAlt

section Index

variable {E : Type} [Field E] [NumberField E] {M N : Type} [AddCommGroup M] [Module (𝓞 E) M] [AddCommGroup N]
  [Module (𝓞 E) N]

/- English proof (translation)
Use `haveI : Module.Free ℤ M := Module.Free.trans (S := 𝓞 E)`. Use `haveI : Module.Finite ℤ M := Module.Finite.trans (𝓞 E) M`. Use `set g : M →ₗ[ℤ] M := f.restrictScalars ℤ with hg`. Establish `hdet : LinearMap.det g = Algebra.norm ℤ (LinearMap.det f)` using `LinearMap.det_restrictScalars`. Establish `hgi : Function.Injective g` using `hf`.

Set `N : Submodule ℤ M` to `LinearMap.range g`. Set `e : M ≃ₗ[ℤ] N` to `LinearEquiv.ofInjective g hgi`. Establish `key` using `Submodule.natAbs_det_equiv N e.toAddEquiv`. Establish `hcomp : N.subtype ∘ₗ AddMonoidHom.toIntLinearMap (e.toAddEquiv : M →+ N) = g`. Use extensionality with `x`.

Both sides reduce to the same expression. Rewrite `key` using `[hcomp, hdet]`. Rewrite using `[key]`. Both sides reduce to the same expression.
-/
theorem index_range [Module.Free (𝓞 E) M] [Module.Finite (𝓞 E) M] (f : M →ₗ[𝓞 E] M) (hf : Function.Injective f) :
    (LinearMap.range f).toAddSubgroup.index = (Algebra.norm ℤ (LinearMap.det f)).natAbs := by
  classical
  haveI : Module.Free ℤ M := Module.Free.trans (S := 𝓞 E)
  haveI : Module.Finite ℤ M := Module.Finite.trans (𝓞 E) M
  set g : M →ₗ[ℤ] M := f.restrictScalars ℤ with hg
  have hdet : LinearMap.det g = Algebra.norm ℤ (LinearMap.det f) := LinearMap.det_restrictScalars
  have hgi : Function.Injective g := hf
  let N : Submodule ℤ M := LinearMap.range g
  let e : M ≃ₗ[ℤ] N := LinearEquiv.ofInjective g hgi
  have key := Submodule.natAbs_det_equiv N e.toAddEquiv
  have hcomp : N.subtype ∘ₗ AddMonoidHom.toIntLinearMap (e.toAddEquiv : M →+ N) = g := by
    ext x
    rfl
  rw [hcomp, hdet] at key
  rw [key]
  rfl

/- English proof (translation)
Establish `e : ∀ S : Submodule R A, (S.map φ).toAddSubgroup = S.toAddSubgroup.map φ.toAddMonoidHom`. Introduce `S`. Use extensionality with `y`. Simplify using the standard rewrite rules. Rewrite using `[e, e]`.

Conclude with `AddSubgroup.relIndex_map_map_of_injective (f := φ.toAddMonoidHom) J.toAddSubgroup K.toAddSubgroup hφ`.
-/
theorem relIndex_map {R A B : Type} [Ring R] [AddCommGroup A] [Module R A] [AddCommGroup B] [Module R B]
    (φ : A →ₗ[R] B) (hφ : Function.Injective φ) (J K : Submodule R A) :
    (J.map φ).toAddSubgroup.relIndex (K.map φ).toAddSubgroup = J.toAddSubgroup.relIndex K.toAddSubgroup := by
  have e : ∀ S : Submodule R A, (S.map φ).toAddSubgroup = S.toAddSubgroup.map φ.toAddMonoidHom := by
    intro S
    ext y
    simp
  rw [e, e]
  exact AddSubgroup.relIndex_map_map_of_injective (f := φ.toAddMonoidHom) J.toAddSubgroup K.toAddSubgroup hφ

/- English proof (translation)
Establish `hne : (Ideal.span {a}).comap (algebraMap ℤ (𝓞 E)) ≠ ⊥` using `Ideal.comap_ne_bot_of_integral_mem ha (Ideal.mem_span_singleton_self a) (Algebra.IsIntegral.isIntegral a)`. Take `⟨n, hn, hn0⟩` from `Submodule.exists_mem_ne_zero_of_ne_bot hne`. Rewrite `hn` using `[Ideal.mem_comap, Ideal.mem_span_singleton']`. Take `⟨b, hb⟩` from `hn`. Conclude with `⟨n, hn0, b, by simpa using hb.symm⟩`.
-/
private theorem exists_int_eq_mul_of_ne_zero' {E : Type} [Field E] [NumberField E] {a : 𝓞 E} (ha : a ≠ 0) :
    ∃ n : ℤ, n ≠ 0 ∧ ∃ b : 𝓞 E, (n : 𝓞 E) = b * a := by
  have hne : (Ideal.span {a}).comap (algebraMap ℤ (𝓞 E)) ≠ ⊥ :=
    Ideal.comap_ne_bot_of_integral_mem ha (Ideal.mem_span_singleton_self a)
      (Algebra.IsIntegral.isIntegral a)
  obtain ⟨n, hn, hn0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  rw [Ideal.mem_comap, Ideal.mem_span_singleton'] at hn
  obtain ⟨b, hb⟩ := hn
  exact ⟨n, hn0, b, by simpa using hb.symm⟩

/- English proof (translation)
Use `haveI : Module.Finite ℤ M := Module.Finite.trans (𝓞 E) M`. Apply `Module.finite_of_fg_torsion` to reduce the goal to its premises. Introduce `x`. Take `⟨⟨a, ha⟩, hax⟩` from `@h x`. Establish `ha0 : a ≠ 0` using `nonZeroDivisors.ne_zero ha`.

Take `⟨n, hn, b, hb⟩` from `exists_int_eq_mul_of_ne_zero' ha0`. Use `⟨⟨n, mem_nonZeroDivisors_of_ne_zero hn⟩, ?_⟩` and prove the remaining obligations. Use `show n • x = 0`. Rewrite using `[← Int.cast_smul_eq_zsmul (𝓞 E), hb, mul_smul]`. Rewrite `hax` using `[Submonoid.smul_def]`.

Simplify using `[hax]`.
-/
theorem finite_of_torsion [Module.Finite (𝓞 E) M] (h : Module.IsTorsion (𝓞 E) M) : Finite M := by
  haveI : Module.Finite ℤ M := Module.Finite.trans (𝓞 E) M
  apply Module.finite_of_fg_torsion
  intro x
  obtain ⟨⟨a, ha⟩, hax⟩ := @h x
  have ha0 : a ≠ 0 := nonZeroDivisors.ne_zero ha
  obtain ⟨n, hn, b, hb⟩ := exists_int_eq_mul_of_ne_zero' ha0
  refine ⟨⟨n, mem_nonZeroDivisors_of_ne_zero hn⟩, ?_⟩
  show n • x = 0
  rw [← Int.cast_smul_eq_zsmul (𝓞 E), hb, mul_smul]
  rw [Submonoid.smul_def] at hax
  simp [hax]

/- English proof (translation)
Establish `h1` using `J.finrank_quotient_add_finrank`. Establish `h2 : Module.finrank (𝓞 E) (M ⧸ J) = 0` using `by omega`. Establish `h3 : Finite (M ⧸ J)` using `finite_of_torsion (Module.finrank_eq_zero_iff_isTorsion.1 h2)`. Establish `: Finite (M ⧸ J.toAddSubgroup)` using `h3`. Conclude with `AddSubgroup.index_ne_zero_of_finite`.
-/
theorem index_ne_zero [Module.Finite (𝓞 E) M] (J : Submodule (𝓞 E) M)
    (h : Module.finrank (𝓞 E) J = Module.finrank (𝓞 E) M) : J.toAddSubgroup.index ≠ 0 := by
  have h1 := J.finrank_quotient_add_finrank
  have h2 : Module.finrank (𝓞 E) (M ⧸ J) = 0 := by omega
  have h3 : Finite (M ⧸ J) := finite_of_torsion (Module.finrank_eq_zero_iff_isTorsion.1 h2)
  have : Finite (M ⧸ J.toAddSubgroup) := h3
  exact AddSubgroup.index_ne_zero_of_finite

/- English proof (translation)
Take `⟨n, hn, b, hb⟩` from `exists_int_eq_mul_of_ne_zero' ha`. Establish `h1 : n • x = 0`. Rewrite using `[← Int.cast_smul_eq_zsmul (𝓞 E), hb, mul_smul, hx, smul_zero]`. Break down `smul_eq_zero.1 h1 with h | h` into its components or cases. Conclude with `absurd h hn`.

Conclude with `h`.
-/
theorem eq_zero_of_smul [Module.Free ℤ M] {a : 𝓞 E} (ha : a ≠ 0) {x : M} (hx : a • x = 0) : x = 0 := by
  obtain ⟨n, hn, b, hb⟩ := exists_int_eq_mul_of_ne_zero' ha
  have h1 : n • x = 0 := by
    rw [← Int.cast_smul_eq_zsmul (𝓞 E), hb, mul_smul, hx, smul_zero]
  rcases smul_eq_zero.1 h1 with h | h
  · exact absurd h hn
  · exact h

/- English proof (translation)
Establish `hmap : (Submodule.span R (Set.range v)).map I.subtype = Submodule.span R (Set.range fun a => (v a : N))`. Rewrite using `[Submodule.map_span, ← Set.range_comp]`. Both sides reduce to the same expression. Rewrite using `[← hmap, Submodule.mem_map]`. Prove the components needed by the constructor for the conclusion.

Introduce `h`. Conclude with `⟨z, h, rfl⟩`. Introduce and unpack `⟨y, hy, hyz⟩`. Rewrite using `[← Subtype.ext hyz]` and apply the resulting hypothesis.
-/
private theorem mem_span_range_subtype_iff {R N : Type} [CommRing R] [AddCommGroup N] [Module R N] {I : Submodule R N}
    {r : ℕ} (v : Fin r → I) (z : I) :
    z ∈ Submodule.span R (Set.range v) ↔ (z : N) ∈ Submodule.span R (Set.range fun a => (v a : N)) := by
  have hmap : (Submodule.span R (Set.range v)).map I.subtype =
      Submodule.span R (Set.range fun a => (v a : N)) := by
    rw [Submodule.map_span, ← Set.range_comp]
    rfl
  rw [← hmap, Submodule.mem_map]
  constructor
  · intro h
    exact ⟨z, h, rfl⟩
  · rintro ⟨y, hy, hyz⟩
    rwa [← Subtype.ext hyz]

/- English proof (translation)
Rewrite using `[AddSubgroup.relIndex]`. Use `congr 1`. Use extensionality with `z`. Simplify using `only [AddSubgroup.mem_addSubgroupOf, Submodule.mem_toAddSubgroup]`. Conclude with `(mem_span_range_subtype_iff v z).symm`.
-/
private theorem relIndex_span_coe_eq_index_span {R N : Type} [CommRing R] [AddCommGroup N] [Module R N] {I : Submodule R N}
    {r : ℕ} (v : Fin r → I) :
    (Submodule.span R (Set.range fun a => (v a : N))).toAddSubgroup.relIndex I.toAddSubgroup =
      (Submodule.span R (Set.range v)).toAddSubgroup.index := by
  rw [AddSubgroup.relIndex]
  congr 1
  ext z
  simp only [AddSubgroup.mem_addSubgroupOf, Submodule.mem_toAddSubgroup]
  exact (mem_span_range_subtype_iff v z).symm

/- English proof (translation)
Use `haveI : Module.Finite (𝓞 E) M := Module.Finite.of_restrictScalars_finite ℤ (𝓞 E) M`. Use `haveI : IsNoetherian (𝓞 E) M := isNoetherian_of_isNoetherianRing_of_finite (𝓞 E) M`. Take `⟨u, hu⟩` from `exists_linearIndependent_of_le_finrank (R := 𝓞 E) (M := I) (le_refl (Module.finrank (𝓞 E) I))`. Take `⟨x, hxI, hx0⟩` from `Submodule.exists_mem_ne_zero_of_ne_bot hI`. Use `⟨Module.finrank (𝓞 E) I, fun a => (u a : M), ?_, fun a => (u a).2, hu.map' I.subtype I.ker_subtype, ?_⟩` and prove the remaining obligations.

Establish `hl : LinearIndependent (𝓞 E) (fun _ : Fin 1 => (⟨x, hxI⟩ : I))`. Rewrite using `[Fintype.linearIndependent_iff]`. Introduce `c hc i`. Establish `hc0 : c 0 • x = 0` using `by simpa using congrArg Subtype.val hc`. Establish `hi : i = 0` using `Subsingleton.elim _ _`.

Substitute `hi` using the available equality. Assume the negation of the conclusion as `hne`. Conclude with `hx0 (eq_zero_of_smul hne hc0)`. Simplify using `using hl.fintype_card_le_finrank`. Rewrite using `[relIndex_span_coe_eq_index_span u]`.

Apply `index_ne_zero (E := E) (M := I)` to reduce the goal to its premises. Rewrite using `[finrank_span_eq_card hu]`. Simplify using the standard rewrite rules.
-/
theorem exists_family [Module.Free ℤ M] [Module.Finite ℤ M] {I : Submodule (𝓞 E) M} (hI : I ≠ ⊥) :
    ∃ r v, IsNzFamily I r v := by
  haveI : Module.Finite (𝓞 E) M := Module.Finite.of_restrictScalars_finite ℤ (𝓞 E) M
  haveI : IsNoetherian (𝓞 E) M := isNoetherian_of_isNoetherianRing_of_finite (𝓞 E) M
  obtain ⟨u, hu⟩ := exists_linearIndependent_of_le_finrank (R := 𝓞 E) (M := I)
    (le_refl (Module.finrank (𝓞 E) I))
  obtain ⟨x, hxI, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hI
  refine ⟨Module.finrank (𝓞 E) I, fun a => (u a : M), ?_, fun a => (u a).2,
    hu.map' I.subtype I.ker_subtype, ?_⟩
  · have hl : LinearIndependent (𝓞 E) (fun _ : Fin 1 => (⟨x, hxI⟩ : I)) := by
      rw [Fintype.linearIndependent_iff]
      intro c hc i
      have hc0 : c 0 • x = 0 := by simpa using congrArg Subtype.val hc
      have hi : i = 0 := Subsingleton.elim _ _
      subst hi
      by_contra hne
      exact hx0 (eq_zero_of_smul hne hc0)
    simpa using hl.fintype_card_le_finrank
  · rw [relIndex_span_coe_eq_index_span u]
    apply index_ne_zero (E := E) (M := I)
    rw [finrank_span_eq_card hu]
    simp

omit [NumberField E] in
/- English proof (translation)
Rewrite using `[Nat.cast_smul_eq_nsmul]`. Conclude with `AddSubgroup.nsmul_relIndex_mem (Submodule.span (𝓞 E) (Set.range v)).toAddSubgroup (K := I.toAddSubgroup) hx`.
-/
theorem family_nsmul {I : Submodule (𝓞 E) M} {r : ℕ} {v : Fin r → M} {x : M} (hx : x ∈ I) :
    (((Submodule.span (𝓞 E) (Set.range v)).toAddSubgroup.relIndex I.toAddSubgroup : ℕ) : 𝓞 E) • x ∈
      Submodule.span (𝓞 E) (Set.range v) := by
  rw [Nat.cast_smul_eq_nsmul]
  exact AddSubgroup.nsmul_relIndex_mem (Submodule.span (𝓞 E) (Set.range v)).toAddSubgroup (K := I.toAddSubgroup) hx

/- English proof (translation)
Take `⟨h1, hmem, hli, hidx⟩` from `hv`. Set `v' : Fin r → I` to `fun a => ⟨v a, hmem a⟩`. Establish `hli' : LinearIndependent (𝓞 E) v'` using `LinearIndependent.of_comp I.subtype hli`. Use `set N := (Submodule.span (𝓞 E) (Set.range v)).toAddSubgroup.relIndex I.toAddSubgroup with hN`. Establish `htor : Module.rank (𝓞 E) (I ⧸ Submodule.span (𝓞 E) (Set.range v')) = 0`.

Rewrite using `[rank_eq_zero_iff]`. Introduce `q`. Take `⟨y, rfl⟩` from `Submodule.Quotient.mk_surjective _ q`. Use `⟨((N : ℕ) : 𝓞 E), by exact_mod_cast hidx, ?_⟩` and prove the remaining obligations. Rewrite using `[← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero, mem_span_range_subtype_iff v']`.

Conclude with `family_nsmul y.2`. Establish `hsum` using `rank_quotient_add_rank_of_isDomain (Submodule.span (𝓞 E) (Set.range v'))`. Rewrite `hsum` using `[htor, zero_add, rank_span hli']`. Rewrite using `[Module.finrank, ← hsum, Cardinal.mk_range_eq v' hli'.injective]`. Simplify using the standard rewrite rules.
-/
theorem family_rank [Module.Free ℤ M] [Module.Finite ℤ M] {I : Submodule (𝓞 E) M} {r : ℕ} {v : Fin r → M}
    (hv : IsNzFamily I r v) : r = Module.finrank (𝓞 E) I := by
  obtain ⟨h1, hmem, hli, hidx⟩ := hv
  let v' : Fin r → I := fun a => ⟨v a, hmem a⟩
  have hli' : LinearIndependent (𝓞 E) v' := LinearIndependent.of_comp I.subtype hli
  set N := (Submodule.span (𝓞 E) (Set.range v)).toAddSubgroup.relIndex I.toAddSubgroup with hN
  have htor : Module.rank (𝓞 E) (I ⧸ Submodule.span (𝓞 E) (Set.range v')) = 0 := by
    rw [rank_eq_zero_iff]
    intro q
    obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ q
    refine ⟨((N : ℕ) : 𝓞 E), by exact_mod_cast hidx, ?_⟩
    rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero, mem_span_range_subtype_iff v']
    exact family_nsmul y.2
  have hsum := rank_quotient_add_rank_of_isDomain (Submodule.span (𝓞 E) (Set.range v'))
  rw [htor, zero_add, rank_span hli'] at hsum
  rw [Module.finrank, ← hsum, Cardinal.mk_range_eq v' hli'.injective]
  simp

/- English proof (translation)
Use `set V := Submodule.span (𝓞 E) (Set.range v) with hV`. Set `bV : Module.Basis (Fin r) (𝓞 E) V` to `Module.Basis.span hv`. Use `haveI : Module.Free (𝓞 E) V := Module.Free.of_basis bV`. Use `haveI : Module.Finite (𝓞 E) V := Module.Finite.of_basis bV`. Set `f : V →ₗ[𝓞 E] V` to `Matrix.toLin bV bV A`.

Establish `hfb : ∀ b, ((f (bV b) : V) : M) = w b`. Introduce `b`. Simplify using `only [f, Matrix.toLin_self, Submodule.coe_sum, Submodule.coe_smul, hA b]`. Use `Finset.sum_congr rfl fun a _ => ?_` and prove the remaining obligations. Rewrite using `[Module.Basis.span_apply]`.

Establish `hw' : LinearIndependent (𝓞 E) (fun b => f (bV b))`. Apply `LinearIndependent.of_comp V.subtype` to reduce the goal to its premises. Use `hw using 1` and compare the differences between its conclusion and the goal. Use function extensionality and compare the values at `b`. Conclude with `hfb b`.

Establish `hfeq : f = (Finsupp.linearCombination (𝓞 E) (fun b => f (bV b))) ∘ₗ bV.repr.toLinearMap`. Apply `bV.ext` to reduce the goal to its premises. Introduce `b`. Simplify using the standard rewrite rules. Establish `hinj : Function.Injective f`.

Rewrite using `[hfeq]`. Rewrite using `[LinearMap.coe_comp]`. Conclude with `Function.Injective.comp hw' bV.repr.injective`. Establish `hdet : LinearMap.det f = A.det` using `LinearMap.det_toLin bV A`. Establish `hrange : (LinearMap.range f).map V.subtype = Submodule.span (𝓞 E) (Set.range w)`.

Establish `hfw : (fun b => ((f (bV b) : V) : M)) = w` using `funext hfb`. Rewrite using `[LinearMap.range_eq_map, ← bV.span_eq, Submodule.map_span, Submodule.map_span, ← Set.range_comp, ← Set.range_comp, ← hfw]`. Both sides reduce to the same expression. Use `⟨?_, ?_⟩` and prove the remaining obligations. Introduce `h0`.

Take `⟨c, hc0, hc⟩` from `Matrix.exists_mulVec_eq_zero_iff.mpr h0`. Apply `hc0` to reduce the goal to its premises. Establish `hr : ⇑(bV.repr (bV.equivFun.symm c)) = c`. Rewrite using `[← Module.Basis.equivFun_apply, LinearEquiv.apply_symm_apply]`. Establish `h1 : f (bV.equivFun.symm c) = 0`.

Simplify using `only [f]`. Rewrite using `[Matrix.toLin_apply, hr, hc]`. Simplify using the standard rewrite rules. Establish `h2` using `congrArg bV.equivFun (hinj (h1.trans (map_zero f).symm))`. Rewrite `h2` using `[LinearEquiv.apply_symm_apply, map_zero]`. Then use the resulting hypothesis.

Establish `hm` using `relIndex_map V.subtype V.injective_subtype (LinearMap.range f) ⊤`. Rewrite `hm` using `[hrange, Submodule.map_subtype_top]`. Rewrite using `[hm, Submodule.top_toAddSubgroup, AddSubgroup.relIndex_top_right, index_range f hinj, hdet]`.
-/
theorem relIndex_matrix {r : ℕ} {v w : Fin r → M} (hv : LinearIndependent (𝓞 E) v)
    (hw : LinearIndependent (𝓞 E) w) (A : Matrix (Fin r) (Fin r) (𝓞 E)) (hA : ∀ b, w b = ∑ a, A a b • v a) :
    A.det ≠ 0 ∧ (Submodule.span (𝓞 E) (Set.range w)).toAddSubgroup.relIndex
      (Submodule.span (𝓞 E) (Set.range v)).toAddSubgroup = (Algebra.norm ℤ A.det).natAbs := by
  classical
  set V := Submodule.span (𝓞 E) (Set.range v) with hV
  let bV : Module.Basis (Fin r) (𝓞 E) V := Module.Basis.span hv
  haveI : Module.Free (𝓞 E) V := Module.Free.of_basis bV
  haveI : Module.Finite (𝓞 E) V := Module.Finite.of_basis bV
  let f : V →ₗ[𝓞 E] V := Matrix.toLin bV bV A
  have hfb : ∀ b, ((f (bV b) : V) : M) = w b := by
    intro b
    simp only [f, Matrix.toLin_self, Submodule.coe_sum, Submodule.coe_smul, hA b]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Module.Basis.span_apply]
  have hw' : LinearIndependent (𝓞 E) (fun b => f (bV b)) := by
    apply LinearIndependent.of_comp V.subtype
    convert hw using 1
    funext b
    exact hfb b
  have hfeq : f = (Finsupp.linearCombination (𝓞 E) (fun b => f (bV b))) ∘ₗ bV.repr.toLinearMap := by
    apply bV.ext
    intro b
    simp
  have hinj : Function.Injective f := by
    rw [hfeq]
    rw [LinearMap.coe_comp]
    exact Function.Injective.comp hw' bV.repr.injective
  have hdet : LinearMap.det f = A.det := LinearMap.det_toLin bV A
  have hrange : (LinearMap.range f).map V.subtype = Submodule.span (𝓞 E) (Set.range w) := by
    have hfw : (fun b => ((f (bV b) : V) : M)) = w := funext hfb
    rw [LinearMap.range_eq_map, ← bV.span_eq, Submodule.map_span, Submodule.map_span, ← Set.range_comp,
      ← Set.range_comp, ← hfw]
    rfl
  refine ⟨?_, ?_⟩
  · intro h0
    obtain ⟨c, hc0, hc⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr h0
    apply hc0
    have hr : ⇑(bV.repr (bV.equivFun.symm c)) = c := by
      rw [← Module.Basis.equivFun_apply, LinearEquiv.apply_symm_apply]
    have h1 : f (bV.equivFun.symm c) = 0 := by
      simp only [f]
      rw [Matrix.toLin_apply, hr, hc]
      simp
    have h2 := congrArg bV.equivFun (hinj (h1.trans (map_zero f).symm))
    rwa [LinearEquiv.apply_symm_apply, map_zero] at h2
  · have hm := relIndex_map V.subtype V.injective_subtype (LinearMap.range f) ⊤
    rw [hrange, Submodule.map_subtype_top] at hm
    rw [hm, Submodule.top_toAddSubgroup, AddSubgroup.relIndex_top_right, index_range f hinj, hdet]

/- English proof (translation)
Rewrite using `[injective_iff_map_eq_zero]`. Introduce `a ha`. Establish `hker : RingHom.ker s = ⊥`. Apply `Ideal.eq_bot_of_comap_eq_bot (R := ℤ)` to reduce the goal to its premises. Rewrite using `[eq_bot_iff]`.

Introduce `n hn`. Rewrite `hn` using `[Ideal.mem_comap, RingHom.mem_ker, algebraMap_int_eq, eq_intCast, map_intCast]`. Rewrite using `[Ideal.mem_bot]`. Conclude with `hn` after adjusting the coercions. Establish `: a ∈ RingHom.ker s` using `ha`.

Rewrite `this` using `[hker]`. Conclude with `this`.
-/
private theorem ringOfIntegers_ringHom_complex_injective {E : Type} [Field E] [NumberField E] (s : 𝓞 E →+* ℂ) :
    Function.Injective s := by
  rw [injective_iff_map_eq_zero]
  intro a ha
  have hker : RingHom.ker s = ⊥ := by
    apply Ideal.eq_bot_of_comap_eq_bot (R := ℤ)
    rw [eq_bot_iff]
    intro n hn
    rw [Ideal.mem_comap, RingHom.mem_ker, algebraMap_int_eq, eq_intCast, map_intCast] at hn
    rw [Ideal.mem_bot]
    exact_mod_cast hn
  have : a ∈ RingHom.ker s := ha
  rw [hker] at this
  exact this

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `σ₁ σ₂ h`. Apply `AlgHom.coe_ringHom_injective` to reduce the goal to its premises. Conclude with `IsLocalization.ringHom_ext (nonZeroDivisors (𝓞 E)) h`. Introduce `s`.

Use `⟨(IsFractionRing.lift (ringOfIntegers_ringHom_complex_injective s)).toRatAlgHom, ?_⟩` and prove the remaining obligations. Apply `RingHom.ext` to reduce the goal to its premises. Introduce `a`. Rewrite using `[RingHom.comp_apply]`. Conclude with `IsFractionRing.lift_algebraMap (ringOfIntegers_ringHom_complex_injective s) a`.
-/
private theorem bijective_algHom_comp_algebraMap {E : Type} [Field E] [NumberField E] :
    Function.Bijective fun σ : E →ₐ[ℚ] ℂ => (σ : E →+* ℂ).comp (algebraMap (𝓞 E) E) := by
  constructor
  · intro σ₁ σ₂ h
    apply AlgHom.coe_ringHom_injective
    exact IsLocalization.ringHom_ext (nonZeroDivisors (𝓞 E)) h
  · intro s
    refine ⟨(IsFractionRing.lift (ringOfIntegers_ringHom_complex_injective s)).toRatAlgHom, ?_⟩
    apply RingHom.ext
    intro a
    rw [RingHom.comp_apply]
    exact IsFractionRing.lift_algebraMap (ringOfIntegers_ringHom_complex_injective s) a

/- English proof (translation)
Establish `h1 : ((Algebra.norm ℤ d : ℤ) : ℂ) = algebraMap ℚ ℂ (Algebra.norm ℚ (d : E))`. Rewrite using `[← Algebra.coe_norm_int]`. Simplify using the standard rewrite rules. Rewrite using `[h1, Algebra.norm_eq_prod_embeddings ℚ ℂ]`. Conclude with `Fintype.prod_bijective _ bijective_algHom_comp_algebraMap _ _ (fun σ => rfl)`.
-/
theorem norm_eq_prod (d : 𝓞 E) : ((Algebra.norm ℤ d : ℤ) : ℂ) = ∏ s : 𝓞 E →+* ℂ, s d := by
  have h1 : ((Algebra.norm ℤ d : ℤ) : ℂ) = algebraMap ℚ ℂ (Algebra.norm ℚ (d : E)) := by
    rw [← Algebra.coe_norm_int]
    simp
  rw [h1, Algebra.norm_eq_prod_embeddings ℚ ℂ]
  exact Fintype.prod_bijective _ bijective_algHom_comp_algebraMap _ _ (fun σ => rfl)

end Index

section Riem

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {g : ℕ} {Λ : Type} [AddCommGroup Λ] [Module (𝓞 E) Λ]
  {Ψ : Type} [Fintype Ψ] (R : RiemLat E g Λ)

/- English proof (translation)
Use extensionality with `x`. Simplify using the standard rewrite rules.
-/
private theorem starRingEnd_comp_starRingEnd_comp {A : Type} [Ring A] (f : A →+* ℂ) :
    (starRingEnd ℂ).comp ((starRingEnd ℂ).comp f) = f := by
  ext x
  simp

omit [Fintype Ψ] in
/- English proof (translation)
Take `⟨hinj, hiff⟩` from `hσ`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `(a | a) (b | b) h`. Simplify using `only [Sum.elim_inl] at h`. Rewrite using `[hinj h]`.

Simplify using `only [Sum.elim_inl, Sum.elim_inr] at h`. Conclude with `absurd ⟨a, h⟩ ((hiff (σ b)).1 ⟨b, rfl⟩)`. Simplify using `only [Sum.elim_inl, Sum.elim_inr] at h`. Conclude with `absurd ⟨b, h.symm⟩ ((hiff (σ a)).1 ⟨a, rfl⟩)`. Simplify using `only [Sum.elim_inr] at h`.

Establish `h'` using `congrArg (fun f => (starRingEnd ℂ).comp f) h`. Simplify using `only [starRingEnd_comp_starRingEnd_comp] at h'`. Rewrite using `[hinj h']`. Introduce `s`. Distinguish the cases in `hs : ∃ τ, σ τ = s`.

Take `⟨τ, hτ⟩` from `hs`. Conclude with `⟨Sum.inl τ, hτ⟩`. Establish `h2 : ∃ τ, σ τ = (starRingEnd ℂ).comp s`. Assume the negation of the conclusion as `hn`. Conclude with `hs ((hiff s).2 hn)`.

Take `⟨τ, hτ⟩` from `h2`. Use `⟨Sum.inr τ, ?_⟩` and prove the remaining obligations. Simplify using `only [Sum.elim_inr, hτ, starRingEnd_comp_starRingEnd_comp]`.
-/
theorem cm_bij {σ : Ψ → (𝓞 E →+* ℂ)} (hσ : IsCMFam σ) :
    Function.Bijective (Sum.elim σ fun τ => (starRingEnd ℂ).comp (σ τ)) := by
  obtain ⟨hinj, hiff⟩ := hσ
  constructor
  · rintro (a | a) (b | b) h
    · simp only [Sum.elim_inl] at h
      rw [hinj h]
    · simp only [Sum.elim_inl, Sum.elim_inr] at h
      exact absurd ⟨a, h⟩ ((hiff (σ b)).1 ⟨b, rfl⟩)
    · simp only [Sum.elim_inl, Sum.elim_inr] at h
      exact absurd ⟨b, h.symm⟩ ((hiff (σ a)).1 ⟨a, rfl⟩)
    · simp only [Sum.elim_inr] at h
      have h' := congrArg (fun f => (starRingEnd ℂ).comp f) h
      simp only [starRingEnd_comp_starRingEnd_comp] at h'
      rw [hinj h']
  · intro s
    by_cases hs : ∃ τ, σ τ = s
    · obtain ⟨τ, hτ⟩ := hs
      exact ⟨Sum.inl τ, hτ⟩
    · have h2 : ∃ τ, σ τ = (starRingEnd ℂ).comp s := by
        by_contra hn
        exact hs ((hiff s).2 hn)
      obtain ⟨τ, hτ⟩ := h2
      refine ⟨Sum.inr τ, ?_⟩
      simp only [Sum.elim_inr, hτ, starRingEnd_comp_starRingEnd_comp]

/- English proof (translation)
Establish `h` using `norm_eq_prod d`. Rewrite `h` using `[← Fintype.prod_bijective _ (cm_bij hσ) (fun x => Sum.elim σ (fun τ => (starRingEnd ℂ).comp (σ τ)) x d) _ (fun _ => rfl), Fintype.prod_sum_type]`. Simplify using `only [Sum.elim_inl, Sum.elim_inr, RingHom.comp_apply] at h`. Rewrite `h` using `[← Finset.prod_mul_distrib]`. Simplify using `only [Complex.mul_conj] at h`.

Rewrite `h` using `[← Complex.ofReal_prod, ← Complex.ofReal_intCast]`. Establish `hR : ((Algebra.norm ℤ d : ℤ) : ℝ) = ∏ τ, Complex.normSq (σ τ d)` using `Complex.ofReal_injective h`. Establish `hnn : (0 : ℝ) ≤ ∏ τ, Complex.normSq (σ τ d)` using `Finset.prod_nonneg fun τ _ => Complex.normSq_nonneg _`. Rewrite using `[Nat.cast_natAbs, Int.cast_abs, hR, abs_of_nonneg hnn]`.
-/
theorem prod_normSq {σ : Ψ → (𝓞 E →+* ℂ)} (hσ : IsCMFam σ) (d : 𝓞 E) :
    ∏ τ, Complex.normSq (σ τ d) = ((Algebra.norm ℤ d).natAbs : ℝ) := by
  have h := norm_eq_prod d
  rw [← Fintype.prod_bijective _ (cm_bij hσ) (fun x => Sum.elim σ (fun τ => (starRingEnd ℂ).comp (σ τ)) x d) _
    (fun _ => rfl), Fintype.prod_sum_type] at h
  simp only [Sum.elim_inl, Sum.elim_inr, RingHom.comp_apply] at h
  rw [← Finset.prod_mul_distrib] at h
  simp only [Complex.mul_conj] at h
  rw [← Complex.ofReal_prod, ← Complex.ofReal_intCast] at h
  have hR : ((Algebra.norm ℤ d : ℤ) : ℝ) = ∏ τ, Complex.normSq (σ τ d) := Complex.ofReal_injective h
  have hnn : (0 : ℝ) ≤ ∏ τ, Complex.normSq (σ τ d) :=
    Finset.prod_nonneg fun τ _ => Complex.normSq_nonneg _
  rw [Nat.cast_natAbs, Int.cast_abs, hR, abs_of_nonneg hnn]

/- English proof (translation)
Use extensionality with `a b`. Simplify using `[RiemLat.gram, RiemLat.ip, Matrix.mul_apply, dotProduct, mulVec, Finset.mul_sum, Finset.sum_mul, mul_assoc]`. Rewrite using `[Finset.sum_comm]`.
-/
private theorem gram_eq_transpose_of_mul_Hm {r : ℕ} (u : Fin r → Fin g → ℂ) :
    R.gram u = (Matrix.of u * R.Hm * (Matrix.of u)ᴴ)ᵀ := by
  ext a b
  simp [RiemLat.gram, RiemLat.ip, Matrix.mul_apply, dotProduct, mulVec, Finset.mul_sum, Finset.sum_mul, mul_assoc]
  rw [Finset.sum_comm]

/- English proof (translation)
Establish `hU : Matrix.of u' = Aᵀ * Matrix.of u`. Use extensionality with `b i`. Simplify using `[h, Matrix.mul_apply, Finset.sum_apply]`. Rewrite using `[gram_eq_transpose_of_mul_Hm, gram_eq_transpose_of_mul_Hm, hU, Matrix.det_transpose, Matrix.det_transpose, Matrix.conjTranspose_mul, show Aᵀ * Matrix.of u * R.Hm * ((Matrix.of u)ᴴ * Aᵀᴴ) = Aᵀ * (Matrix.of u * R.Hm * (Matrix.of u)ᴴ) * Aᵀᴴ by simp only [Matrix.mul_assoc], Matrix.de …`. Establish `hc : A.det * (Matrix.of u * R.Hm * (Matrix.of u)ᴴ).det * star A.det = (Complex.normSq A.det : ℂ) * (Matrix.of u * R.Hm * (Matrix.of u)ᴴ).det`.

Rewrite using `[Complex.normSq_eq_conj_mul_self, Complex.star_def]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[hc, Complex.re_ofReal_mul]`.
-/
theorem gram_matrix {r : ℕ} (u u' : Fin r → Fin g → ℂ) (A : Matrix (Fin r) (Fin r) ℂ)
    (h : ∀ b, u' b = ∑ a, A a b • u a) : (R.gram u').det.re = Complex.normSq A.det * (R.gram u).det.re := by
  have hU : Matrix.of u' = Aᵀ * Matrix.of u := by
    ext b i
    simp [h, Matrix.mul_apply, Finset.sum_apply]
  rw [gram_eq_transpose_of_mul_Hm, gram_eq_transpose_of_mul_Hm, hU, Matrix.det_transpose, Matrix.det_transpose, Matrix.conjTranspose_mul,
    show Aᵀ * Matrix.of u * R.Hm * ((Matrix.of u)ᴴ * Aᵀᴴ) =
      Aᵀ * (Matrix.of u * R.Hm * (Matrix.of u)ᴴ) * Aᵀᴴ by simp only [Matrix.mul_assoc],
    Matrix.det_mul, Matrix.det_mul, Matrix.det_conjTranspose, Matrix.det_transpose]
  have hc : A.det * (Matrix.of u * R.Hm * (Matrix.of u)ᴴ).det * star A.det =
      (Complex.normSq A.det : ℂ) * (Matrix.of u * R.Hm * (Matrix.of u)ᴴ).det := by
    rw [Complex.normSq_eq_conj_mul_self, Complex.star_def]
    ring
  rw [hc, Complex.re_ofReal_mul]

/- English proof (translation)
Establish `hHm : R.Hm.PosDef`. Use `Matrix.posDef_iff_dotProduct_mulVec.2 ⟨R.herm, fun x hx => ?_⟩` and prove the remaining obligations. Establish `h1` using `R.pos (star x) (by simpa using hx)`. Rewrite `h1` using `[star_star]`. Establish `h2` using `R.herm.im_star_dotProduct_mulVec_self x`.

Conclude with `Complex.pos_iff.2 ⟨h1, by rw [eq_comm]; simpa using h2⟩`. Establish `hB : Function.Injective ((Matrix.of u)ᴴ).mulVec`. Introduce `y z hyz`. Establish `hk : (Matrix.of u)ᴴ *ᵥ (y - z) = 0` using `by rw [Matrix.mulVec_sub, hyz, sub_self]`. Establish `hsum : ∑ a, star ((y - z) a) • u a = 0`.

Use function extensionality and compare the values at `i`. Establish `hi` using `congrArg star (congrFun hk i)`. Simplify `hi` using `[Matrix.mulVec, dotProduct, Matrix.conjTranspose_apply, star_sum, mul_comm]`. Establish `h0` using `Fintype.linearIndependent_iff.1 hu _ hsum`. Establish `ht : y - z = 0` using `funext fun a => star_eq_zero.1 (h0 a)`.

Conclude with `sub_eq_zero.1 ht`. Establish `hM` using `hHm.conjTranspose_mul_mul_same hB`. Rewrite `hM` using `[Matrix.conjTranspose_conjTranspose]`. Rewrite using `[gram_eq_transpose_of_mul_Hm, Matrix.det_transpose]`. Conclude with `(Complex.pos_iff.1 hM.det_pos).1`.
-/
theorem gram_det_pos {r : ℕ} {u : Fin r → Fin g → ℂ} (hu : LinearIndependent ℂ u) : 0 < (R.gram u).det.re := by
  have hHm : R.Hm.PosDef := by
    refine Matrix.posDef_iff_dotProduct_mulVec.2 ⟨R.herm, fun x hx => ?_⟩
    have h1 := R.pos (star x) (by simpa using hx)
    rw [star_star] at h1
    have h2 := R.herm.im_star_dotProduct_mulVec_self x
    exact Complex.pos_iff.2 ⟨h1, by rw [eq_comm]; simpa using h2⟩
  have hB : Function.Injective ((Matrix.of u)ᴴ).mulVec := by
    intro y z hyz
    have hk : (Matrix.of u)ᴴ *ᵥ (y - z) = 0 := by rw [Matrix.mulVec_sub, hyz, sub_self]
    have hsum : ∑ a, star ((y - z) a) • u a = 0 := by
      funext i
      have hi := congrArg star (congrFun hk i)
      simpa [Matrix.mulVec, dotProduct, Matrix.conjTranspose_apply, star_sum, mul_comm] using hi
    have h0 := Fintype.linearIndependent_iff.1 hu _ hsum
    have ht : y - z = 0 := funext fun a => star_eq_zero.1 (h0 a)
    exact sub_eq_zero.1 ht
  have hM := hHm.conjTranspose_mul_mul_same hB
  rw [Matrix.conjTranspose_conjTranspose] at hM
  rw [gram_eq_transpose_of_mul_Hm, Matrix.det_transpose]
  exact (Complex.pos_iff.1 hM.det_pos).1

/- English proof (translation)
Take `⟨_, hvI, hvli, _⟩` from `hv`. Establish `hex : ∀ b, ∃ c : Fin r → 𝓞 E, ∑ a, c a • v a = w b` using `fun b => (Submodule.mem_span_range_iff_exists_fun (𝓞 E)).1 (hle b)`. Use `choose c hc using hex`. Set `A : Matrix (Fin r) (Fin r) (𝓞 E)` to `Matrix.of fun a b => c b a`. Establish `hAw : ∀ b, w b = ∑ a, A a b • v a` using `fun b => (hc b).symm`.

Take `⟨hdet, hidx⟩` from `relIndex_matrix hvli hw A hAw`. Establish `hwv : Submodule.span (𝓞 E) (Set.range w) ≤ Submodule.span (𝓞 E) (Set.range v)` using `Submodule.span_le.2 (by rintro _ ⟨b, rfl⟩; exact hle b)`. Establish `hvle : Submodule.span (𝓞 E) (Set.range v) ≤ I` using `Submodule.span_le.2 (by rintro _ ⟨a, rfl⟩; exact hvI a)`. Establish `hmul` using `AddSubgroup.relIndex_mul_relIndex (Submodule.span (𝓞 E) (Set.range w)).toAddSubgroup (Submodule.span (𝓞 E) (Set.range v)).toAddSubgroup I.toAddSubgroup hwv hvle`. Establish `hnum : ∀ τ, (R.gram fun b => eigComp R.B (σ τ) (R.P (w b))).det.re = Complex.normSq (σ τ A.det) * (R.gram fun a => eigComp R.B (σ τ) (R.P (v a))).det.re`.

Introduce `τ`. Rewrite using `[RingHom.map_det, RingHom.mapMatrix_apply]`. Apply `gram_matrix` to reduce the goal to its premises. Introduce `b`. Simplify using `only [eigComp_eq, hAw b, map_sum, R.act, proj_act, Matrix.map_apply]`.

Establish `hN : ((Algebra.norm ℤ A.det).natAbs : ℝ) ≠ 0`. Conclude with `Int.natAbs_ne_zero.2 (Algebra.norm_ne_zero_iff.2 hdet)` after adjusting the coercions. Unfold `RiemLat.nzOf`. Rewrite using `[Finset.prod_congr rfl (fun τ _ => hnum τ), Finset.prod_mul_distrib, prod_normSq hσ, ← hmul, hidx]`. Use `push_cast`.

Rewrite using `[mul_div_mul_left _ _ hN]`.
-/
theorem nzOf_of_le {σ : Ψ → (𝓞 E →+* ℂ)} (hσ : IsCMFam σ) {I : Submodule (𝓞 E) Λ} {r : ℕ} {v w : Fin r → Λ}
    (hv : IsNzFamily I r v) (hw : LinearIndependent (𝓞 E) w)
    (hle : ∀ b, w b ∈ Submodule.span (𝓞 E) (Set.range v)) : R.nzOf σ I w = R.nzOf σ I v := by
  classical
  obtain ⟨_, hvI, hvli, _⟩ := hv
  have hex : ∀ b, ∃ c : Fin r → 𝓞 E, ∑ a, c a • v a = w b := fun b =>
    (Submodule.mem_span_range_iff_exists_fun (𝓞 E)).1 (hle b)
  choose c hc using hex
  let A : Matrix (Fin r) (Fin r) (𝓞 E) := Matrix.of fun a b => c b a
  have hAw : ∀ b, w b = ∑ a, A a b • v a := fun b => (hc b).symm
  obtain ⟨hdet, hidx⟩ := relIndex_matrix hvli hw A hAw
  have hwv : Submodule.span (𝓞 E) (Set.range w) ≤ Submodule.span (𝓞 E) (Set.range v) :=
    Submodule.span_le.2 (by rintro _ ⟨b, rfl⟩; exact hle b)
  have hvle : Submodule.span (𝓞 E) (Set.range v) ≤ I :=
    Submodule.span_le.2 (by rintro _ ⟨a, rfl⟩; exact hvI a)
  have hmul := AddSubgroup.relIndex_mul_relIndex
    (Submodule.span (𝓞 E) (Set.range w)).toAddSubgroup (Submodule.span (𝓞 E) (Set.range v)).toAddSubgroup
    I.toAddSubgroup hwv hvle
  have hnum : ∀ τ, (R.gram fun b => eigComp R.B (σ τ) (R.P (w b))).det.re =
      Complex.normSq (σ τ A.det) * (R.gram fun a => eigComp R.B (σ τ) (R.P (v a))).det.re := by
    intro τ
    rw [RingHom.map_det, RingHom.mapMatrix_apply]
    apply gram_matrix
    intro b
    simp only [eigComp_eq, hAw b, map_sum, R.act, proj_act, Matrix.map_apply]
  have hN : ((Algebra.norm ℤ A.det).natAbs : ℝ) ≠ 0 := by
    exact_mod_cast Int.natAbs_ne_zero.2 (Algebra.norm_ne_zero_iff.2 hdet)
  unfold RiemLat.nzOf
  rw [Finset.prod_congr rfl (fun τ _ => hnum τ), Finset.prod_mul_distrib, prod_normSq hσ, ← hmul, hidx]
  push_cast
  rw [mul_div_mul_left _ _ hN]

/- English proof (translation)
Use `haveI := R.free`. Use `haveI := R.fin`. Establish `hr` using `family_rank hv`. Establish `hr'` using `family_rank hw`. Take `rfl : r' = r` from `hr'.trans hr.symm`.

Use `set n : ℕ := (Submodule.span (𝓞 E) (Set.range v)).toAddSubgroup.relIndex I.toAddSubgroup with hn`. Establish `hn0 : (n : 𝓞 E) ≠ 0` using `Nat.cast_ne_zero.2 hv.2.2.2`. Set `f : Λ →ₗ[𝓞 E] Λ` to `(n : 𝓞 E) • LinearMap.id`. Establish `hf : LinearMap.ker f = ⊥`. Rewrite using `[LinearMap.ker_eq_bot']`.

Introduce `m hm`. Conclude with `eq_zero_of_smul hn0 (by simpa [f] using hm)`. Establish `hli : LinearIndependent (𝓞 E) (f ∘ w)` using `hw.2.2.1.map' f hf`. Establish `h1 : R.nzOf σ I (f ∘ w) = R.nzOf σ I v` using `nzOf_of_le R hσ hv hli (fun b => by simpa [f] using family_nsmul (v := v) (hw.2.1 b))`. Establish `h2 : R.nzOf σ I (f ∘ w) = R.nzOf σ I w` using `nzOf_of_le R hσ hw hli (fun b => by`.

Simplify `Submodule.smul_mem (Submodule.span (𝓞 E) (Set.range w)) (n : 𝓞 E) (Submodule.subset_span (Set.mem_range_self b)))` using `[f]`. Rewrite using `[← h2, h1]`.
-/
theorem nzOf_eq {σ : Ψ → (𝓞 E →+* ℂ)} (hσ : IsCMFam σ) {I : Submodule (𝓞 E) Λ} {r r' : ℕ} {v : Fin r → Λ}
    {w : Fin r' → Λ} (hv : IsNzFamily I r v) (hw : IsNzFamily I r' w) : R.nzOf σ I w = R.nzOf σ I v := by
  haveI := R.free
  haveI := R.fin
  have hr := family_rank hv
  have hr' := family_rank hw
  obtain rfl : r' = r := hr'.trans hr.symm
  set n : ℕ := (Submodule.span (𝓞 E) (Set.range v)).toAddSubgroup.relIndex I.toAddSubgroup with hn
  have hn0 : (n : 𝓞 E) ≠ 0 := Nat.cast_ne_zero.2 hv.2.2.2
  let f : Λ →ₗ[𝓞 E] Λ := (n : 𝓞 E) • LinearMap.id
  have hf : LinearMap.ker f = ⊥ := by
    rw [LinearMap.ker_eq_bot']
    intro m hm
    exact eq_zero_of_smul hn0 (by simpa [f] using hm)
  have hli : LinearIndependent (𝓞 E) (f ∘ w) := hw.2.2.1.map' f hf
  have h1 : R.nzOf σ I (f ∘ w) = R.nzOf σ I v :=
    nzOf_of_le R hσ hv hli (fun b => by simpa [f] using family_nsmul (v := v) (hw.2.1 b))
  have h2 : R.nzOf σ I (f ∘ w) = R.nzOf σ I w :=
    nzOf_of_le R hσ hw hli (fun b => by
      simpa [f] using Submodule.smul_mem (Submodule.span (𝓞 E) (Set.range w)) (n : 𝓞 E)
        (Submodule.subset_span (Set.mem_range_self b)))
  rw [← h2, h1]

/- English proof (translation)
Establish `h : ∃ r v, IsNzFamily I r v` using `⟨r, v, hv⟩`. Unfold `RiemLat.nz`. Rewrite using `[dif_pos h]`. Conclude with `nzOf_eq R hσ hv h.choose_spec.choose_spec`.
-/
theorem nz_eq {σ : Ψ → (𝓞 E →+* ℂ)} (hσ : IsCMFam σ) {I : Submodule (𝓞 E) Λ} {r : ℕ} {v : Fin r → Λ}
    (hv : IsNzFamily I r v) : R.nz σ I = R.nzOf σ I v := by
  have h : ∃ r v, IsNzFamily I r v := ⟨r, v, hv⟩
  unfold RiemLat.nz
  rw [dif_pos h]
  exact nzOf_eq R hσ hv h.choose_spec.choose_spec

/- English proof (translation)
Take `⟨_, hvI, hvli, hidx⟩` from `hv`. Unfold `RiemLat.nzOf`. Apply `div_pos` to reduce the goal to its premises. Apply `Finset.prod_pos` to reduce the goal to its premises. Introduce `τ _`.

Establish `hli` using `proj_indep R hI (σ τ) hvI hvli`. Simplify using `only [eigComp_eq]`. Conclude with `gram_det_pos R hli`. Conclude with `Nat.pos_of_ne_zero hidx` after adjusting the coercions.
-/
theorem nzOf_pos (σ : Ψ → (𝓞 E →+* ℂ)) {I : Submodule (𝓞 E) Λ} (hI : IsIsoSub R.form I) {r : ℕ} {v : Fin r → Λ}
    (hv : IsNzFamily I r v) : 0 < R.nzOf σ I v := by
  obtain ⟨_, hvI, hvli, hidx⟩ := hv
  unfold RiemLat.nzOf
  apply div_pos
  · apply Finset.prod_pos
    intro τ _
    have hli := proj_indep R hI (σ τ) hvI hvli
    simp only [eigComp_eq]
    exact gram_det_pos R hli
  · exact_mod_cast Nat.pos_of_ne_zero hidx

end Riem

end LevelTowerAlt

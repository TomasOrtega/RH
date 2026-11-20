import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.MkMemAdmissibleAtIffCocycle
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsSeriesOfExact

noncomputable section

namespace GlobalTheory.AdmLoc

open Formalism.WeaklyAdmissibleFiltrations
open scoped Pointwise

section Sub

variable {O G : Type} [CommRing O] [Group G] {M : Type} [AddCommGroup M] [Module O M]

def IsStab (π : Representation O G M) (X : Submodule O M) : Prop := ∀ g, ∀ x ∈ X, π g x ∈ X

variable {π : Representation O G M}

/- English proof (translation)
Introduce `g x hx`. Take `⟨y, hy, rfl⟩` from `(Submodule.mem_smul_pointwise_iff_exists x c X).mp hx`. Rewrite using `[map_smul]`. Conclude with `Submodule.smul_mem_pointwise_smul _ _ _ (h g y hy)`.
-/
theorem IsStab.smul {X : Submodule O M} (h : IsStab π X) (c : O) : IsStab π (c • X) := by
  intro g x hx
  obtain ⟨y, hy, rfl⟩ := (Submodule.mem_smul_pointwise_iff_exists x c X).mp hx
  rw [map_smul]
  exact Submodule.smul_mem_pointwise_smul _ _ _ (h g y hy)

/- English proof (translation)
Introduce `g x hx`. Take `⟨y, hy, z, hz, rfl⟩` from `Submodule.mem_sup.mp hx`. Rewrite using `[map_add]`. Conclude with `Submodule.add_mem_sup (h g y hy) (h' g z hz)`.
-/
theorem IsStab.sup {X Y : Submodule O M} (h : IsStab π X) (h' : IsStab π Y) : IsStab π (X ⊔ Y) := by
  intro g x hx
  obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.mp hx
  rw [map_add]
  exact Submodule.add_mem_sup (h g y hy) (h' g z hz)

def subquotRep {X Y : Submodule O M} (hX : IsStab π X) (hY : IsStab π Y) :
    Representation O G (↥Y ⧸ X.comap Y.subtype) :=
  (π.subrepresentation Y hY).quotient (X.comap Y.subtype) (fun g x hx => hX g x hx)

/- English proof (translation)
Use `SameSS.of_exact (f := Submodule.mapQ _ _ (Submodule.inclusion hYZ) (fun _ hx => hx)) (p := Submodule.mapQ _ _ LinearMap.id (fun _ hx => hXY hx)) ?_ ?_ ?_ ?_ ?_ h` and prove the remaining obligations. Introduce `g x`. Take `⟨x, rfl⟩` from `Submodule.Quotient.mk_surjective _ x`. Both sides reduce to the same expression. Introduce `g x`.

Take `⟨x, rfl⟩` from `Submodule.Quotient.mk_surjective _ x`. Both sides reduce to the same expression. Rewrite using `[injective_iff_map_eq_zero]`. Introduce `x hx`. Take `⟨x, rfl⟩` from `Submodule.Quotient.mk_surjective _ x`.

Establish `h1 : Submodule.inclusion hYZ x ∈ X.comap Z.subtype` using `(Submodule.Quotient.mk_eq_zero _).mp hx`. Conclude with `(Submodule.Quotient.mk_eq_zero _).mpr h1`. Introduce `x`. Take `⟨x, rfl⟩` from `Submodule.Quotient.mk_surjective _ x`. Conclude with `⟨Submodule.Quotient.mk x, rfl⟩`.

Introduce `x`. Take `⟨x, rfl⟩` from `Submodule.Quotient.mk_surjective _ x`. Prove the components needed by the constructor for the conclusion. Introduce `hx`. Establish `h1 : x ∈ Y.comap Z.subtype` using `(Submodule.Quotient.mk_eq_zero _).mp hx`.

Conclude with `⟨Submodule.Quotient.mk ⟨x, h1⟩, rfl⟩`. Introduce and unpack `⟨y, hy⟩`. Take `⟨y, rfl⟩` from `Submodule.Quotient.mk_surjective _ y`. Rewrite using `[← hy]`. Conclude with `(Submodule.Quotient.mk_eq_zero (Y.comap Z.subtype) (x := Submodule.inclusion hYZ y)).mpr y.2`.
-/
theorem subquot_sameSS_prod {X Y Z : Submodule O M} (hX : IsStab π X) (hY : IsStab π Y) (hZ : IsStab π Z)
    (hXY : X ≤ Y) (hYZ : Y ≤ Z) (h : IsFiniteLength O (↥Z ⧸ X.comap Z.subtype)) :
    SameSS (subquotRep hX hZ) ((subquotRep hX hY).prod (subquotRep hY hZ)) := by
  refine SameSS.of_exact
    (f := Submodule.mapQ _ _ (Submodule.inclusion hYZ) (fun _ hx => hx))
    (p := Submodule.mapQ _ _ LinearMap.id (fun _ hx => hXY hx)) ?_ ?_ ?_ ?_ ?_ h
  · intro g x
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    rfl
  · intro g x
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    rfl
  · rw [injective_iff_map_eq_zero]
    intro x hx
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    have h1 : Submodule.inclusion hYZ x ∈ X.comap Z.subtype := (Submodule.Quotient.mk_eq_zero _).mp hx
    exact (Submodule.Quotient.mk_eq_zero _).mpr h1
  · intro x
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    exact ⟨Submodule.Quotient.mk x, rfl⟩
  · intro x
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    constructor
    · intro hx
      have h1 : x ∈ Y.comap Z.subtype := (Submodule.Quotient.mk_eq_zero _).mp hx
      exact ⟨Submodule.Quotient.mk ⟨x, h1⟩, rfl⟩
    · rintro ⟨y, hy⟩
      obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ y
      rw [← hy]
      exact (Submodule.Quotient.mk_eq_zero (Y.comap Z.subtype) (x := Submodule.inclusion hYZ y)).mpr y.2

def smulEquiv {c : O} (hc : IsSMulRegular M c) (Y : Submodule O M) : ↥Y ≃ₗ[O] ↥(c • Y) :=
  Submodule.equivMapOfInjective (DistribSMul.toLinearMap O M c) hc Y

/- English proof (translation)
Use `SameSS.of_equiv h (Submodule.Quotient.equiv _ _ (smulEquiv hc Y) ?_) ?_` and prove the remaining obligations. Use extensionality with `z`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨x, hx, rfl⟩`. Conclude with `Submodule.smul_mem_pointwise_smul _ _ _ hx`.

Introduce `hz`. Take `⟨y, rfl⟩` from `(smulEquiv hc Y).surjective z`. Take `⟨x, hx, hxy⟩` from `(Submodule.mem_smul_pointwise_iff_exists _ c X).mp hz`. Establish `hxy' : x = (y : M)` using `hc hxy`. Conclude with `⟨y, (hxy' ▸ hx : (y : M) ∈ X), rfl⟩`.

Introduce `g x`. Take `⟨x, rfl⟩` from `Submodule.Quotient.mk_surjective _ x`. Use `congrArg Submodule.Quotient.mk (Subtype.ext ?_)` and prove the remaining obligations. Conclude with `(map_smul (π g) c (x : M)).symm`.
-/
theorem subquot_sameSS_smul {c : O} (hc : IsSMulRegular M c) {X Y : Submodule O M} (hX : IsStab π X)
    (hY : IsStab π Y) (h : IsFiniteLength O (↥Y ⧸ X.comap Y.subtype)) :
    SameSS (subquotRep hX hY) (subquotRep (hX.smul c) (hY.smul c)) := by
  refine SameSS.of_equiv h (Submodule.Quotient.equiv _ _ (smulEquiv hc Y) ?_) ?_
  · ext z
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact Submodule.smul_mem_pointwise_smul _ _ _ hx
    · intro hz
      obtain ⟨y, rfl⟩ := (smulEquiv hc Y).surjective z
      obtain ⟨x, hx, hxy⟩ := (Submodule.mem_smul_pointwise_iff_exists _ c X).mp hz
      have hxy' : x = (y : M) := hc hxy
      exact ⟨y, (hxy' ▸ hx : (y : M) ∈ X), rfl⟩
  · intro g x
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    refine congrArg Submodule.Quotient.mk (Subtype.ext ?_)
    exact (map_smul (π g) c (x : M)).symm

/- English proof (translation)
The claim follows from `((SameSS.refl α hA).prod (SameSS.refl γ hC)).congr_right (LinearEquiv.prodComm O A C) (fun _ _ => rfl)`.
-/
theorem SameSS.prod_comm {A C : Type} [AddCommGroup A] [Module O A] [AddCommGroup C] [Module O C]
    (α : Representation O G A) (γ : Representation O G C) (hA : IsFiniteLength O A) (hC : IsFiniteLength O C) :
    SameSS (α.prod γ) (γ.prod α) :=
  ((SameSS.refl α hA).prod (SameSS.refl γ hC)).congr_right (LinearEquiv.prodComm O A C) (fun _ _ => rfl)

variable [IsDomain O] [IsDiscreteValuationRing O]

/- English proof (translation)
Establish `hfl` using `isFiniteLength_quotient_span_singleton O (mem_nonZeroDivisors_of_ne_zero hc)`. Rewrite `hfl`, the goal using `[isFiniteLength_iff_isNoetherian_isArtinian]`. Use `⟨inferInstance, ?_⟩` and prove the remaining obligations. Establish `ht : Module.IsTorsionBySet O N (Ideal.span {c})` using `(Module.isTorsionBySet_span_singleton_iff c).mpr (fun x => h x)`. Use `letI := ht.module`.

Use `haveI : IsScalarTower O (O ⧸ Ideal.span {c}) N := ht.isScalarTower`. Use `haveI : IsArtinianRing (O ⧸ Ideal.span {c}) := isArtinian_of_tower O hfl.2`. Use `haveI : Module.Finite (O ⧸ Ideal.span {c}) N := Module.Finite.of_restrictScalars_finite O _ _`. Conclude with `isArtinian_of_surjective_algebraMap (R := O ⧸ Ideal.span {c}) Ideal.Quotient.mk_surjective`.
-/
theorem finiteLength_of_smul_eq_zero {N : Type} [AddCommGroup N] [Module O N] [Module.Finite O N] {c : O}
    (hc : c ≠ 0) (h : ∀ x : N, c • x = 0) : IsFiniteLength O N := by
  have hfl := isFiniteLength_quotient_span_singleton O (mem_nonZeroDivisors_of_ne_zero hc)
  rw [isFiniteLength_iff_isNoetherian_isArtinian] at hfl ⊢
  refine ⟨inferInstance, ?_⟩
  have ht : Module.IsTorsionBySet O N (Ideal.span {c}) :=
    (Module.isTorsionBySet_span_singleton_iff c).mpr (fun x => h x)
  letI := ht.module
  haveI : IsScalarTower O (O ⧸ Ideal.span {c}) N := ht.isScalarTower
  haveI : IsArtinianRing (O ⧸ Ideal.span {c}) := isArtinian_of_tower O hfl.2
  haveI : Module.Finite (O ⧸ Ideal.span {c}) N := Module.Finite.of_restrictScalars_finite O _ _
  exact isArtinian_of_surjective_algebraMap (R := O ⧸ Ideal.span {c}) Ideal.Quotient.mk_surjective

/- English proof (translation)
Use `haveI : Module.Finite O ↥Y := Module.Finite.iff_fg.mpr hY`. Use `finiteLength_of_smul_eq_zero hc fun x => ?_` and prove the remaining obligations. Take `⟨x, rfl⟩` from `Submodule.Quotient.mk_surjective _ x`. Rewrite using `[← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]`. Conclude with `h (Submodule.smul_mem_pointwise_smul _ _ _ x.2)`.
-/
theorem finiteLength_subquot {c : O} (hc : c ≠ 0) {X Y : Submodule O M} (hY : Y.FG) (h : c • Y ≤ X) :
    IsFiniteLength O (↥Y ⧸ X.comap Y.subtype) := by
  haveI : Module.Finite O ↥Y := Module.Finite.iff_fg.mpr hY
  refine finiteLength_of_smul_eq_zero hc fun x => ?_
  obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]
  exact h (Submodule.smul_mem_pointwise_smul _ _ _ x.2)

/- English proof (translation)
The claim follows from `hY.map _`.
-/
theorem fg_smul {Y : Submodule O M} (hY : Y.FG) (c : O) : (c • Y).FG := hY.map _

/- English proof (translation)
Establish `h3 : c • B ≤ c • A` using `Submodule.map_mono h2`. Establish `e1` using `subquot_sameSS_prod (hA.smul c) hB hA h1 h2 (finiteLength_subquot hc0 fA le_rfl)`. Establish `e2` using `subquot_sameSS_prod (hB.smul c) (hA.smul c) hB h3 h1 (finiteLength_subquot hc0 fB le_rfl)`. Establish `l1` using `finiteLength_subquot hc0 fB h3`. Establish `l2` using `finiteLength_subquot hc0 fA h1`.

Establish `e3` using `subquot_sameSS_smul hc hB hA l2`. Conclude with `(e1.trans (SameSS.prod_comm _ _ l1 l2)).trans ((e3.prod (SameSS.refl _ l1)).trans e2.symm)`.
-/
theorem red_sameSS_step {c : O} (hc0 : c ≠ 0) (hc : IsSMulRegular M c) {A B : Submodule O M} (hA : IsStab π A)
    (hB : IsStab π B) (fA : A.FG) (fB : B.FG) (h1 : c • A ≤ B) (h2 : B ≤ A) :
    SameSS (subquotRep (hA.smul c) hA) (subquotRep (hB.smul c) hB) := by
  have h3 : c • B ≤ c • A := Submodule.map_mono h2
  have e1 := subquot_sameSS_prod (hA.smul c) hB hA h1 h2 (finiteLength_subquot hc0 fA le_rfl)
  have e2 := subquot_sameSS_prod (hB.smul c) (hA.smul c) hB h3 h1 (finiteLength_subquot hc0 fB le_rfl)
  have l1 := finiteLength_subquot hc0 fB h3
  have l2 := finiteLength_subquot hc0 fA h1
  have e3 := subquot_sameSS_smul hc hB hA l2
  exact (e1.trans (SameSS.prod_comm _ _ l1 l2)).trans ((e3.prod (SameSS.refl _ l1)).trans e2.symm)

/- English proof (translation)
Proceed by induction on `n with`. Consider the case `zero`. Introduce `A hA fA h1 h2`. Rewrite `h1` using `[pow_zero, one_smul]`. Take `rfl : A = B` from `le_antisymm h1 h2`.

Conclude with `SameSS.refl _ (finiteLength_subquot hc0 fA le_rfl)`. Consider the case `succ n ih`. Introduce `A hA fA h1 h2`. Establish `fA' : (B ⊔ c • A).FG` using `fB.sup (fg_smul fA c)`. Use `(red_sameSS_step hc0 hc hA (hB.sup (hA.smul c)) fA fA' le_sup_right (sup_le h2 (Submodule.smul_le_self_of_tower c A))).trans (ih _ fA' ?_ le_sup_left)` and prove the remaining obligations.

Rewrite using `[Submodule.smul_sup', smul_smul, ← pow_succ]`. Conclude with `sup_le (Submodule.smul_le_self_of_tower _ B) h1`.
-/
theorem red_sameSS_of_pow {c : O} (hc0 : c ≠ 0) (hc : IsSMulRegular M c) {B : Submodule O M} (hB : IsStab π B)
    (fB : B.FG) (n : ℕ) : ∀ {A : Submodule O M} (hA : IsStab π A), A.FG → c ^ n • A ≤ B → B ≤ A →
      SameSS (subquotRep (hA.smul c) hA) (subquotRep (hB.smul c) hB) := by
  induction n with
  | zero =>
    intro A hA fA h1 h2
    rw [pow_zero, one_smul] at h1
    obtain rfl : A = B := le_antisymm h1 h2
    exact SameSS.refl _ (finiteLength_subquot hc0 fA le_rfl)
  | succ n ih =>
    intro A hA fA h1 h2
    have fA' : (B ⊔ c • A).FG := fB.sup (fg_smul fA c)
    refine (red_sameSS_step hc0 hc hA (hB.sup (hA.smul c)) fA fA' le_sup_right
      (sup_le h2 (Submodule.smul_le_self_of_tower c A))).trans (ih _ fA' ?_ le_sup_left)
    rw [Submodule.smul_sup', smul_smul, ← pow_succ]
    exact sup_le (Submodule.smul_le_self_of_tower _ B) h1

/- English proof (translation)
Establish `fS : (A ⊔ B).FG` using `fA.sup fB`. Use `(red_sameSS_of_pow hc0 hc hA fA n (hA.sup hB) fS ?_ le_sup_left).symm.trans (red_sameSS_of_pow hc0 hc hB fB m (hA.sup hB) fS ?_ le_sup_right)` and prove the remaining obligations. Rewrite using `[Submodule.smul_sup']`. Conclude with `sup_le (Submodule.smul_le_self_of_tower _ A) h2`. Rewrite using `[Submodule.smul_sup']`.

Conclude with `sup_le h1 (Submodule.smul_le_self_of_tower _ B)`.
-/
theorem red_sameSS_of_commensurable {c : O} (hc0 : c ≠ 0) (hc : IsSMulRegular M c) {A B : Submodule O M}
    (hA : IsStab π A) (hB : IsStab π B) (fA : A.FG) (fB : B.FG) {m n : ℕ} (h1 : c ^ m • A ≤ B)
    (h2 : c ^ n • B ≤ A) : SameSS (subquotRep (hA.smul c) hA) (subquotRep (hB.smul c) hB) := by
  have fS : (A ⊔ B).FG := fA.sup fB
  refine (red_sameSS_of_pow hc0 hc hA fA n (hA.sup hB) fS ?_ le_sup_left).symm.trans
    (red_sameSS_of_pow hc0 hc hB fB m (hA.sup hB) fS ?_ le_sup_right)
  · rw [Submodule.smul_sup']
    exact sup_le (Submodule.smul_le_self_of_tower _ A) h2
  · rw [Submodule.smul_sup']
    exact sup_le h1 (Submodule.smul_le_self_of_tower _ B)

end Sub

section Lat

variable {G : Type} [Group G] {LL O : Type} [Field LL] [CommRing O] [Algebra O LL]
  {V : Type} [AddCommGroup V] [Module LL V] [Module O V] [IsScalarTower O LL V]

def resScal (O : Type) [CommRing O] [Algebra O LL] [Module O V] [IsScalarTower O LL V]
    (ρ : Representation LL G V) : Representation O G V where
  toFun g := (ρ g).restrictScalars O
  map_one' := by ext x; simp
  map_mul' g h := by ext x; simp

variable {ρ : Representation LL G V}

/- English proof (translation)
The claim follows from `L.stable`.
-/
theorem isStab_lattice (L : Lattice (O := O) ρ) : IsStab (resScal O ρ) L.T := L.stable

variable [IsDomain O] [IsDiscreteValuationRing O]

/- English proof (translation)
Use `SameSS.of_equiv (finiteLength_subquot hc L.fg le_rfl) (Submodule.quotEquivOfEq _ _ ?_) ?_` and prove the remaining obligations. Use extensionality with `x`. Prove the components needed by the constructor for the conclusion. Introduce `hx`. Take `⟨y, hy, hxy⟩` from `(Submodule.mem_smul_pointwise_iff_exists _ c L.T).mp hx`.

Conclude with `(Submodule.mem_smul_pointwise_iff_exists _ c ⊤).mpr ⟨⟨y, hy⟩, trivial, Subtype.ext hxy⟩`. Introduce `hx`. Take `⟨y, -, rfl⟩` from `(Submodule.mem_smul_pointwise_iff_exists _ c ⊤).mp hx`. Conclude with `Submodule.smul_mem_pointwise_smul _ _ _ y.2`. Introduce `g x`.

Take `⟨x, rfl⟩` from `Submodule.Quotient.mk_surjective _ x`. Both sides reduce to the same expression.
-/
theorem modRep_sameSS_subquot (L : Lattice (O := O) ρ) {c : O} (hc : c ≠ 0) :
    SameSS (subquotRep ((isStab_lattice L).smul c) (isStab_lattice L)) (modRep (latRep L) c) := by
  refine SameSS.of_equiv (finiteLength_subquot hc L.fg le_rfl) (Submodule.quotEquivOfEq _ _ ?_) ?_
  · ext x
    constructor
    · intro hx
      obtain ⟨y, hy, hxy⟩ := (Submodule.mem_smul_pointwise_iff_exists _ c L.T).mp hx
      exact (Submodule.mem_smul_pointwise_iff_exists _ c ⊤).mpr ⟨⟨y, hy⟩, trivial, Subtype.ext hxy⟩
    · intro hx
      obtain ⟨y, -, rfl⟩ := (Submodule.mem_smul_pointwise_iff_exists _ c ⊤).mp hx
      exact Submodule.smul_mem_pointwise_smul _ _ _ y.2
  · intro g x
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    rfl

variable [IsFractionRing O LL]

/- English proof (translation)
Establish `hv : v ∈ Submodule.span LL (L.T : Set V)` using `by rw [L.span]; trivial`. Take `⟨s, hs⟩` from `multiple_mem_span_of_mem_localization_span (nonZeroDivisors O) LL (L.T : Set V) v hv`. Rewrite `hs` using `[Submodule.span_eq]`. Take `⟨n, u, hu⟩` from `IsDiscreteValuationRing.eq_unit_mul_pow_irreducible (nonZeroDivisors.ne_zero s.2) hlam`. Use `⟨n, ?_⟩` and prove the remaining obligations.

Establish `h` using `L.T.smul_mem ((u⁻¹ : Oˣ) : O) hs`. Rewrite `h` using `[Submonoid.smul_def, smul_smul, hu, Units.inv_mul_cancel_left]`. Then use the resulting hypothesis.
-/
theorem exists_pow_smul_mem (L : Lattice (O := O) ρ) {lam : O} (hlam : Irreducible lam) (v : V) :
    ∃ n : ℕ, lam ^ n • v ∈ L.T := by
  have hv : v ∈ Submodule.span LL (L.T : Set V) := by rw [L.span]; trivial
  obtain ⟨s, hs⟩ := multiple_mem_span_of_mem_localization_span (nonZeroDivisors O) LL (L.T : Set V) v hv
  rw [Submodule.span_eq] at hs
  obtain ⟨n, u, hu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible (nonZeroDivisors.ne_zero s.2) hlam
  refine ⟨n, ?_⟩
  have h := L.T.smul_mem ((u⁻¹ : Oˣ) : O) hs
  rwa [Submonoid.smul_def, smul_smul, hu, Units.inv_mul_cancel_left] at h

/- English proof (translation)
Proceed by induction on `A, hA using Submodule.fg_induction with`. Consider the case `singleton x`. Take `⟨n, hn⟩` from `exists_pow_smul_mem L hlam x`. Use `⟨n, ?_⟩` and prove the remaining obligations. Rewrite using `[Submodule.smul_span, Set.smul_set_singleton, Submodule.span_singleton_le_iff_mem]`.

Conclude with `hn`. Consider the case `sup A B _ _ hA hB`. Take `⟨m, hm⟩` from `hA`. Take `⟨n, hn⟩` from `hB`. Use `⟨m + n, ?_⟩` and prove the remaining obligations.

Rewrite using `[Submodule.smul_sup']`. Use `sup_le ?_ ?_` and prove the remaining obligations. Rewrite using `[pow_add, mul_comm, ← smul_smul]`. Conclude with `(Submodule.smul_le_self_of_tower _ _).trans hm`. Rewrite using `[pow_add, ← smul_smul]`.

Conclude with `(Submodule.smul_le_self_of_tower _ _).trans hn`.
-/
theorem exists_pow_smul_le (L : Lattice (O := O) ρ) {lam : O} (hlam : Irreducible lam) {A : Submodule O V}
    (hA : A.FG) : ∃ n : ℕ, lam ^ n • A ≤ L.T := by
  induction A, hA using Submodule.fg_induction with
  | singleton x =>
    obtain ⟨n, hn⟩ := exists_pow_smul_mem L hlam x
    refine ⟨n, ?_⟩
    rw [Submodule.smul_span, Set.smul_set_singleton, Submodule.span_singleton_le_iff_mem]
    exact hn
  | sup A B _ _ hA hB =>
    obtain ⟨m, hm⟩ := hA
    obtain ⟨n, hn⟩ := hB
    refine ⟨m + n, ?_⟩
    rw [Submodule.smul_sup']
    refine sup_le ?_ ?_
    · rw [pow_add, mul_comm, ← smul_smul]
      exact (Submodule.smul_le_self_of_tower _ _).trans hm
    · rw [pow_add, ← smul_smul]
      exact (Submodule.smul_le_self_of_tower _ _).trans hn

/- English proof (translation)
Establish `h0 : lam ≠ 0` using `hlam.ne_zero`. Establish `hreg : IsSMulRegular V lam`. Introduce `x y hxy`. Establish `h1 : algebraMap O LL lam ≠ 0` using `(map_ne_zero_iff _ (IsFractionRing.injective O LL)).mpr h0`. Establish `h2 : algebraMap O LL lam • x = algebraMap O LL lam • y`.

Rewrite using `[algebraMap_smul, algebraMap_smul]`. Conclude with `hxy`. Conclude with `smul_right_injective V h1 h2`. Take `⟨m, hm⟩` from `exists_pow_smul_le L' hlam L.fg`. Take `⟨n, hn⟩` from `exists_pow_smul_le L hlam L'.fg`.

Conclude with `((modRep_sameSS_subquot L h0).symm.trans (red_sameSS_of_commensurable h0 hreg (isStab_lattice L) (isStab_lattice L') L.fg L'.fg hm hn)).trans (modRep_sameSS_subquot L' h0)`.
-/
theorem lattice_reduction_sameSS {lam : O} (hlam : Irreducible lam) (L L' : Lattice (O := O) ρ) :
    SameSS (modRep (latRep L) lam) (modRep (latRep L') lam) := by
  have h0 : lam ≠ 0 := hlam.ne_zero
  have hreg : IsSMulRegular V lam := by
    intro x y hxy
    have h1 : algebraMap O LL lam ≠ 0 := (map_ne_zero_iff _ (IsFractionRing.injective O LL)).mpr h0
    have h2 : algebraMap O LL lam • x = algebraMap O LL lam • y := by
      rw [algebraMap_smul, algebraMap_smul]; exact hxy
    exact smul_right_injective V h1 h2
  obtain ⟨m, hm⟩ := exists_pow_smul_le L' hlam L.fg
  obtain ⟨n, hn⟩ := exists_pow_smul_le L hlam L'.fg
  exact ((modRep_sameSS_subquot L h0).symm.trans
    (red_sameSS_of_commensurable h0 hreg (isStab_lattice L) (isStab_lattice L') L.fg L'.fg hm hn)).trans
    (modRep_sameSS_subquot L' h0)

end Lat

end GlobalTheory.AdmLoc

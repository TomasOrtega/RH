import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.TwistedPieces.LocalTraceForms.TraceCompSmulRight
import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.TwistedPieces.TraceForm

noncomputable section

open Matrix

namespace PositivityTheory.RgUd.TP.Loc.Ptf

open PositivityTheory.RgUd.T PositivityTheory.RgUd.TP

variable {k : Type} [Field k] {n : ℕ}

def bSub (Z : Subalgebra k (Matrix (Fin n) (Fin n) k)) : Submodule k (Matrix (Fin n) (Fin n) k) where
  carrier := Bz Z
  add_mem' {x y} hx hy a ha := by rw [mul_add, add_mul, hx a ha, hy a ha]
  zero_mem' a _ := by simp
  smul_mem' c x hx a ha := by rw [mul_smul_comm, smul_mul_assoc, hx a ha]

/- English proof (translation)
Introduce `a ha`. Rewrite using `[← mul_assoc, hx a ha, mul_assoc, hy a ha, ← mul_assoc]`.
-/
theorem mul_mem_bz {Z : Subalgebra k (Matrix (Fin n) (Fin n) k)} {x y : Matrix (Fin n) (Fin n) k} (hx : x ∈ Bz Z)
    (hy : y ∈ Bz Z) : x * y ∈ Bz Z := by
  intro a ha
  rw [← mul_assoc, hx a ha, mul_assoc, hy a ha, ← mul_assoc]

def RZ (Z : Subalgebra k (Matrix (Fin n) (Fin n) k)) : Type := Z

section Inst

variable (Z : Subalgebra k (Matrix (Fin n) (Fin n) k)) (hZ : CR Z)

def crZ : CommRing (RZ Z) := { (inferInstance : Ring Z) with mul_comm := fun a b => Subtype.ext (hZ.1 _ a.2 _ b.2) }

def valZ : @RingHom (RZ Z) (Matrix (Fin n) (Fin n) k) (crZ Z hZ).toNonAssocSemiring _ :=
  letI := crZ Z hZ
  { toFun := fun z => (show Z from z).1
    map_one' := rfl
    map_mul' := fun _ _ => rfl
    map_zero' := rfl
    map_add' := fun _ _ => rfl }

def algZ : @RingHom k (RZ Z) _ (crZ Z hZ).toNonAssocSemiring :=
  letI := crZ Z hZ
  { toFun := fun c => (show RZ Z from (⟨algebraMap k _ c, Z.algebraMap_mem c⟩ : Z))
    map_one' := Subtype.ext (map_one _)
    map_mul' := fun a b => Subtype.ext (map_mul (algebraMap k (Matrix (Fin n) (Fin n) k)) a b)
    map_zero' := Subtype.ext (map_zero _)
    map_add' := fun a b => Subtype.ext (map_add (algebraMap k (Matrix (Fin n) (Fin n) k)) a b) }

end Inst

/- English proof (translation)
Use `letI : CommRing (RZ Z) := crZ Z hZ`. Use `letI : Algebra k (RZ Z) := (algZ Z hZ).toAlgebra`. Use `letI : Module (RZ Z) (Fin n → k) := Module.compHom (Fin n → k) ((Matrix.toLinAlgEquiv' (R := k) (n := Fin n)).toRingEquiv.toRingHom.comp (valZ Z hZ))`. Establish `hsmul : ∀ (r : RZ Z) (v : Fin n → k), r • v = (valZ Z hZ r) *ᵥ v` using `fun r v => rfl`. Establish `hval : ∀ (c : k) (r : RZ Z), valZ Z hZ (c • r) = c • valZ Z hZ r`.

Introduce `c r`. Rewrite using `[Algebra.smul_def, map_mul]`. Use `show algebraMap k (Matrix (Fin n) (Fin n) k) c * valZ Z hZ r = _`. Rewrite using `[Algebra.smul_def]`. Use `haveI : IsScalarTower k (RZ Z) (Fin n → k) := ⟨fun c r v => by`.

Rewrite using `[hsmul, hsmul, hval, Matrix.smul_mulVec]⟩`. Set `L : RZ Z →ₗ[k] Matrix (Fin n) (Fin n) k` to `{ toFun := valZ Z hZ map_add' := map_add _ map_smul' := hval }`. Establish `hLinj : Function.Injective L` using `fun a b h => Subtype.ext h`. Use `haveI : Module.Finite k (RZ Z) := Module.Finite.of_injective L hLinj`. Use `haveI : IsArtinianRing (RZ Z) := IsArtinianRing.of_finite k (RZ Z)`.

Use `haveI : IsReduced (RZ Z) := hZ.2`. Take `⟨τ0, hc, hnd, hnil⟩` from `exists_tau (k := k) (R := RZ Z) (V := Fin n → k)`. Establish `hcomm : ∀ x ∈ Bz Z, ∀ r : RZ Z, x * valZ Z hZ r = valZ Z hZ r * x` using `fun x hx r => (hx _ (show Z from r).2).symm`. Set `ψ : bSub Z →ₗ[k] ((Fin n → k) →ₗ[RZ Z] (Fin n → k))` to `{ toFun := fun x => { toFun := fun v => x.1 *ᵥ v map_add' := fun v w => Matrix.mulVec_add _ _ _ map_smul' := fun r v => by show x.1 *ᵥ (valZ Z hZ r *ᵥ v) = valZ Z hZ r *ᵥ (x.1 *ᵥ v)`. Rewrite using `[Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hcomm x.1 x.2 r] }`.

Use the proof step `map_add' := fun x y => LinearMap.ext fun v => by show (x.1 + y.1) *ᵥ v = x.1 *ᵥ v + y.1 *ᵥ v`. Conclude with `Matrix.add_mulVec _ _ _`. Use the proof step `map_smul' := fun c x => LinearMap.ext fun v => by show (c • x.1) *ᵥ v = c • (x.1 *ᵥ v)`. Conclude with `Matrix.smul_mulVec _ _ _ }`. Establish `hψ : ∀ (x : bSub Z) (v : Fin n → k), ψ x v = x.1 *ᵥ v` using `fun x v => rfl`.

Establish `hψmul : ∀ x (hx : x ∈ Bz Z) y (hy : y ∈ Bz Z), ψ ⟨x * y, mul_mem_bz hx hy⟩ = ψ ⟨x, hx⟩ * ψ ⟨y, hy⟩`. Introduce `x hx y hy`. Use `LinearMap.ext fun v => ?_` and prove the remaining obligations. Rewrite using `[Module.End.mul_apply, hψ, hψ, hψ, Matrix.mulVec_mulVec]`. Take `⟨τ, hτ⟩` from `LinearMap.exists_extend (τ0.comp ψ)`.

Establish `hτx : ∀ x (hx : x ∈ Bz Z), τ x = τ0 (ψ ⟨x, hx⟩)` using `fun x hx => LinearMap.congr_fun hτ ⟨x, hx⟩`. Use `⟨τ, ?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `x hx y hy`. Rewrite using `[hτx _ (mul_mem_bz hx hy), hτx _ (mul_mem_bz hy hx), hψmul x hx y hy, hψmul y hy x hx, hc]`. Introduce `x hx H`.

Establish `hsurj : ∀ g : (Fin n → k) →ₗ[RZ Z] (Fin n → k), ∃ y : bSub Z, ψ y = g`. Introduce `g`. Set `y` to `LinearMap.toMatrix' (g.restrictScalars k)`. Establish `hy : ∀ v, y *ᵥ v = g v` using `fun v => LinearMap.toMatrix'_mulVec _ _`. Establish `hyB : y ∈ Bz Z`.

Introduce `a ha`. Apply `Matrix.toLin'.injective` to reduce the goal to its premises. Use `LinearMap.ext fun v => ?_` and prove the remaining obligations. Rewrite using `[Matrix.toLin'_apply, Matrix.toLin'_apply, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hy, hy]`. Conclude with `(g.map_smul (show RZ Z from (⟨a, ha⟩ : Z)) v).symm`.

Conclude with `⟨⟨y, hyB⟩, LinearMap.ext fun v => hy v⟩`. Establish `h0 : ψ ⟨x, hx⟩ = 0` using `hnd _ fun g => by`. Take `⟨y, rfl⟩` from `hsurj g`. Rewrite using `[← hψmul x hx y.1 y.2, ← hτx]`. Conclude with `H y.1 y.2`.

Apply `Matrix.toLin'.injective` to reduce the goal to its premises. Use `LinearMap.ext fun v => ?_` and prove the remaining obligations. Rewrite using `[Matrix.toLin'_apply, map_zero, LinearMap.zero_apply, ← hψ ⟨x, hx⟩, h0, LinearMap.zero_apply]`. Introduce and unpack `x ⟨hx, m, hm⟩`. Rewrite using `[hτx x hx]`.

Apply `hnil` to reduce the goal to its premises. Use `⟨m, LinearMap.ext fun v => ?_⟩` and prove the remaining obligations. Establish `hpow : ∀ j : ℕ, (ψ ⟨x, hx⟩ ^ j) v = (x ^ j) *ᵥ v`. Introduce `j`. Proceed by induction on `j with`.

Consider the case `zero => simp`. Consider the case `succ j ih`. Rewrite using `[pow_succ', Module.End.mul_apply, ih, hψ, Matrix.mulVec_mulVec, pow_succ']`. Rewrite using `[hpow, hm, LinearMap.zero_apply, Matrix.zero_mulVec]`.
-/
theorem traceForm_core (Z : Subalgebra k (Matrix (Fin n) (Fin n) k)) (hZ : CR Z) :
    ∃ τ : Matrix (Fin n) (Fin n) k →ₗ[k] k,
      (∀ x ∈ Bz Z, ∀ y ∈ Bz Z, τ (x * y) = τ (y * x)) ∧ (∀ x ∈ Bz Z, (∀ y ∈ Bz Z, τ (x * y) = 0) → x = 0) ∧
        ∀ x ∈ NB Z, τ x = 0 := by
  letI : CommRing (RZ Z) := crZ Z hZ
  letI : Algebra k (RZ Z) := (algZ Z hZ).toAlgebra
  letI : Module (RZ Z) (Fin n → k) := Module.compHom (Fin n → k)
    ((Matrix.toLinAlgEquiv' (R := k) (n := Fin n)).toRingEquiv.toRingHom.comp (valZ Z hZ))
  have hsmul : ∀ (r : RZ Z) (v : Fin n → k), r • v = (valZ Z hZ r) *ᵥ v := fun r v => rfl
  have hval : ∀ (c : k) (r : RZ Z), valZ Z hZ (c • r) = c • valZ Z hZ r := by
    intro c r
    rw [Algebra.smul_def, map_mul]
    show algebraMap k (Matrix (Fin n) (Fin n) k) c * valZ Z hZ r = _
    rw [Algebra.smul_def]
  haveI : IsScalarTower k (RZ Z) (Fin n → k) := ⟨fun c r v => by
    rw [hsmul, hsmul, hval, Matrix.smul_mulVec]⟩
  let L : RZ Z →ₗ[k] Matrix (Fin n) (Fin n) k :=
    { toFun := valZ Z hZ
      map_add' := map_add _
      map_smul' := hval }
  have hLinj : Function.Injective L := fun a b h => Subtype.ext h
  haveI : Module.Finite k (RZ Z) := Module.Finite.of_injective L hLinj
  haveI : IsArtinianRing (RZ Z) := IsArtinianRing.of_finite k (RZ Z)
  haveI : IsReduced (RZ Z) := hZ.2
  obtain ⟨τ0, hc, hnd, hnil⟩ := exists_tau (k := k) (R := RZ Z) (V := Fin n → k)
  have hcomm : ∀ x ∈ Bz Z, ∀ r : RZ Z, x * valZ Z hZ r = valZ Z hZ r * x :=
    fun x hx r => (hx _ (show Z from r).2).symm
  let ψ : bSub Z →ₗ[k] ((Fin n → k) →ₗ[RZ Z] (Fin n → k)) :=
    { toFun := fun x =>
        { toFun := fun v => x.1 *ᵥ v
          map_add' := fun v w => Matrix.mulVec_add _ _ _
          map_smul' := fun r v => by
            show x.1 *ᵥ (valZ Z hZ r *ᵥ v) = valZ Z hZ r *ᵥ (x.1 *ᵥ v)
            rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hcomm x.1 x.2 r] }
      map_add' := fun x y => LinearMap.ext fun v => by
        show (x.1 + y.1) *ᵥ v = x.1 *ᵥ v + y.1 *ᵥ v
        exact Matrix.add_mulVec _ _ _
      map_smul' := fun c x => LinearMap.ext fun v => by
        show (c • x.1) *ᵥ v = c • (x.1 *ᵥ v)
        exact Matrix.smul_mulVec _ _ _ }
  have hψ : ∀ (x : bSub Z) (v : Fin n → k), ψ x v = x.1 *ᵥ v := fun x v => rfl
  have hψmul : ∀ x (hx : x ∈ Bz Z) y (hy : y ∈ Bz Z),
      ψ ⟨x * y, mul_mem_bz hx hy⟩ = ψ ⟨x, hx⟩ * ψ ⟨y, hy⟩ := by
    intro x hx y hy
    refine LinearMap.ext fun v => ?_
    rw [Module.End.mul_apply, hψ, hψ, hψ, Matrix.mulVec_mulVec]
  obtain ⟨τ, hτ⟩ := LinearMap.exists_extend (τ0.comp ψ)
  have hτx : ∀ x (hx : x ∈ Bz Z), τ x = τ0 (ψ ⟨x, hx⟩) := fun x hx =>
    LinearMap.congr_fun hτ ⟨x, hx⟩
  refine ⟨τ, ?_, ?_, ?_⟩
  · intro x hx y hy
    rw [hτx _ (mul_mem_bz hx hy), hτx _ (mul_mem_bz hy hx), hψmul x hx y hy, hψmul y hy x hx, hc]
  · intro x hx H
    have hsurj : ∀ g : (Fin n → k) →ₗ[RZ Z] (Fin n → k), ∃ y : bSub Z, ψ y = g := by
      intro g
      let y := LinearMap.toMatrix' (g.restrictScalars k)
      have hy : ∀ v, y *ᵥ v = g v := fun v => LinearMap.toMatrix'_mulVec _ _
      have hyB : y ∈ Bz Z := by
        intro a ha
        apply Matrix.toLin'.injective
        refine LinearMap.ext fun v => ?_
        rw [Matrix.toLin'_apply, Matrix.toLin'_apply, ← Matrix.mulVec_mulVec,
          ← Matrix.mulVec_mulVec, hy, hy]
        exact (g.map_smul (show RZ Z from (⟨a, ha⟩ : Z)) v).symm
      exact ⟨⟨y, hyB⟩, LinearMap.ext fun v => hy v⟩
    have h0 : ψ ⟨x, hx⟩ = 0 := hnd _ fun g => by
      obtain ⟨y, rfl⟩ := hsurj g
      rw [← hψmul x hx y.1 y.2, ← hτx]
      exact H y.1 y.2
    apply Matrix.toLin'.injective
    refine LinearMap.ext fun v => ?_
    rw [Matrix.toLin'_apply, map_zero, LinearMap.zero_apply, ← hψ ⟨x, hx⟩, h0,
      LinearMap.zero_apply]
  · rintro x ⟨hx, m, hm⟩
    rw [hτx x hx]
    apply hnil
    refine ⟨m, LinearMap.ext fun v => ?_⟩
    have hpow : ∀ j : ℕ, (ψ ⟨x, hx⟩ ^ j) v = (x ^ j) *ᵥ v := by
      intro j
      induction j with
      | zero => simp
      | succ j ih =>
        rw [pow_succ', Module.End.mul_apply, ih, hψ, Matrix.mulVec_mulVec, pow_succ']
    rw [hpow, hm, LinearMap.zero_apply, Matrix.zero_mulVec]

/- English proof (translation)
Introduce `_ Z hZ` and use `traceForm_core Z hZ`.
-/
theorem traceForm (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] :
    TraceForm k := fun _ Z hZ => traceForm_core Z hZ

end PositivityTheory.RgUd.TP.Loc.Ptf

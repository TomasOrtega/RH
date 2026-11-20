import Mathlib

namespace GroundTheory.Global

open NumberField IsDedekindDomain Topology
open scoped NumberField.AdeleRing RestrictedProduct

noncomputable section

variable (K : Type*) [Field K] [NumberField K]

abbrev IdeleGroup : Type _ := (𝔸[K])ˣ

namespace IdeleGroup

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem isEmbedding_val_inv :
    IsEmbedding (fun x : IdeleGroup K ↦ ((x : 𝔸[K]), ((x⁻¹ : IdeleGroup K) : 𝔸[K]))) :=
  ((Homeomorph.refl (𝔸[K])).prodCongr MulOpposite.opHomeomorph.symm).isEmbedding.comp
    (Units.isEmbedding_embedProduct (M := 𝔸[K]))

/- English proof (translation)
A detailed English derivation is pending.
-/
example : IsTopologicalGroup (IdeleGroup K) := inferInstance

def prodEquiv :
    IdeleGroup K ≃ₜ* (InfiniteAdeleRing K)ˣ × (FiniteAdeleRing (𝓞 K) K)ˣ where
  toMulEquiv := MulEquiv.prodUnits
  continuous_toFun := (Homeomorph.prodUnits (α := InfiniteAdeleRing K)
    (β := FiniteAdeleRing (𝓞 K) K)).continuous_toFun
  continuous_invFun := (Homeomorph.prodUnits (α := InfiniteAdeleRing K)
    (β := FiniteAdeleRing (𝓞 K) K)).continuous_invFun

@[simp]
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem prodEquiv_apply_fst (x : IdeleGroup K) :
    ((prodEquiv K x).1 : InfiniteAdeleRing K) = (x : 𝔸[K]).1 := rfl

@[simp]
/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem prodEquiv_apply_snd (x : IdeleGroup K) :
    ((prodEquiv K x).2 : FiniteAdeleRing (𝓞 K) K) = (x : 𝔸[K]).2 := rfl

def toInfinite : IdeleGroup K →* (InfiniteAdeleRing K)ˣ :=
  (MonoidHom.fst _ _).comp (prodEquiv K).toMulEquiv.toMonoidHom

def toFinite : IdeleGroup K →* (FiniteAdeleRing (𝓞 K) K)ˣ :=
  (MonoidHom.snd _ _).comp (prodEquiv K).toMulEquiv.toMonoidHom

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem continuous_toInfinite : Continuous (toInfinite K) :=
  continuous_fst.comp (prodEquiv K).continuous

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem continuous_toFinite : Continuous (toFinite K) :=
  continuous_snd.comp (prodEquiv K).continuous

def diagonal : Kˣ →* IdeleGroup K :=
  Units.map (algebraMap K 𝔸[K]).toMonoidHom

@[simp]
/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem coe_diagonal (x : Kˣ) : ((diagonal K x : IdeleGroup K) : 𝔸[K]) = algebraMap K 𝔸[K] x :=
  rfl

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. By extensionality, compare the relevant components. A detailed English derivation is pending.
-/
theorem diagonal_injective : Function.Injective (diagonal K) := by
  intro x y h
  ext
  exact AdeleRing.algebraMap_injective (𝓞 K) K (congrArg Units.val h)

end IdeleGroup

abbrev IdeleClassGroup : Type _ := IdeleGroup K ⧸ (IdeleGroup.diagonal K).range

namespace IdeleClassGroup

/- English proof (translation)
A detailed English derivation is pending.
-/
example : CommGroup (IdeleClassGroup K) := inferInstance

/- English proof (translation)
A detailed English derivation is pending.
-/
example : IsTopologicalGroup (IdeleClassGroup K) := inferInstance

def mk : IdeleGroup K →* IdeleClassGroup K := QuotientGroup.mk' _

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem continuous_mk : Continuous (mk K) := QuotientGroup.continuous_mk

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem isOpenMap_mk : IsOpenMap (mk K) := QuotientGroup.isOpenMap_coe

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem mk_surjective : Function.Surjective (mk K) := QuotientGroup.mk'_surjective _

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem mk_diagonal (x : Kˣ) : mk K (IdeleGroup.diagonal K x) = 1 :=
  (QuotientGroup.eq_one_iff _).2 ⟨x, rfl⟩

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem ker_mk : (mk K).ker = (IdeleGroup.diagonal K).range := QuotientGroup.ker_mk' _

end IdeleClassGroup

namespace IdeleGroup

section Finite

variable {K}

open Classical in

def finiteAdeleSingle (v : HeightOneSpectrum (𝓞 K)) :
    v.adicCompletion K →* FiniteAdeleRing (𝓞 K) K where
  toFun x := RestrictedProduct.mulSingle
    (fun w : HeightOneSpectrum (𝓞 K) ↦ w.adicCompletionIntegers K) v x
  map_one' := Subtype.ext (Pi.mulSingle_one (M := fun w : HeightOneSpectrum (𝓞 K) ↦
    w.adicCompletion K) v)
  map_mul' x y := Subtype.ext (Pi.mulSingle_mul v x y)

open Classical in
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem finiteAdeleSingle_apply (v w : HeightOneSpectrum (𝓞 K)) (x : v.adicCompletion K) :
    finiteAdeleSingle v x w = Pi.mulSingle (M := fun u : HeightOneSpectrum (𝓞 K) ↦
      u.adicCompletion K) v x w := rfl

@[simp]
/- English proof (translation)
Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem finiteAdeleSingle_apply_self (v : HeightOneSpectrum (𝓞 K)) (x : v.adicCompletion K) :
    finiteAdeleSingle v x v = x := by
  classical
  rw [finiteAdeleSingle_apply]
  exact Pi.mulSingle_eq_same v x

/- English proof (translation)
Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem finiteAdeleSingle_apply_of_ne {v w : HeightOneSpectrum (𝓞 K)} (h : w ≠ v)
    (x : v.adicCompletion K) : finiteAdeleSingle v x w = 1 := by
  classical
  rw [finiteAdeleSingle_apply]
  exact Pi.mulSingle_eq_of_ne h x

/- English proof (translation)
Establish an intermediate fact. Simplify using the standard rewrite rules. Introduce a local definition for the expression. Rewrite the conclusion using the stated equalities. Establish an intermediate fact.

Establish an intermediate fact. Both sides reduce to the same expression. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem continuous_finiteAdeleSingle (v : HeightOneSpectrum (𝓞 K)) :
    Continuous (finiteAdeleSingle (K := K) v) := by
  classical
  have hS : Filter.cofinite ≤ Filter.principal ({v}ᶜ : Set (HeightOneSpectrum (𝓞 K))) := by
    simp
  let g : v.adicCompletion K → Πʳ w : HeightOneSpectrum (𝓞 K),
      [w.adicCompletion K, w.adicCompletionIntegers K]_[Filter.principal {v}ᶜ] :=
    fun x ↦ ⟨Pi.mulSingle v x, Filter.eventually_principal.2 fun w hw ↦ by
      rw [Pi.mulSingle_eq_of_ne hw x]
      exact one_mem _⟩
  have hg : Continuous g :=
    RestrictedProduct.continuous_rng_of_principal.mpr (continuous_mulSingle v)
  have hfg : (finiteAdeleSingle (K := K) v : v.adicCompletion K → FiniteAdeleRing (𝓞 K) K) =
      RestrictedProduct.inclusion _ _ hS ∘ g := by
    rfl
  rw [hfg]
  exact (RestrictedProduct.continuous_inclusion hS).comp hg

def finiteEmbedding (v : HeightOneSpectrum (𝓞 K)) : (v.adicCompletion K)ˣ →* IdeleGroup K :=
  Units.map ((MonoidHom.prod 1 (finiteAdeleSingle v) :
    v.adicCompletion K →* InfiniteAdeleRing K × FiniteAdeleRing (𝓞 K) K))

def finiteProj (v : HeightOneSpectrum (𝓞 K)) : IdeleGroup K →* (v.adicCompletion K)ˣ :=
  Units.map (((RestrictedProduct.evalMonoidHom
      (fun w : HeightOneSpectrum (𝓞 K) ↦ w.adicCompletion K) v).comp
    (MonoidHom.snd (InfiniteAdeleRing K) (FiniteAdeleRing (𝓞 K) K))) :
    InfiniteAdeleRing K × FiniteAdeleRing (𝓞 K) K →* v.adicCompletion K)

@[simp]
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem coe_finiteEmbedding (v : HeightOneSpectrum (𝓞 K)) (x : (v.adicCompletion K)ˣ) :
    ((finiteEmbedding v x : IdeleGroup K) : 𝔸[K]) =
      (1, finiteAdeleSingle v (x : v.adicCompletion K)) :=
  rfl

@[simp]
/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem coe_finiteProj (v : HeightOneSpectrum (𝓞 K)) (x : IdeleGroup K) :
    ((finiteProj v x : (v.adicCompletion K)ˣ) : v.adicCompletion K) = (x : 𝔸[K]).2 v :=
  rfl

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem continuous_finiteEmbedding (v : HeightOneSpectrum (𝓞 K)) :
    Continuous (finiteEmbedding (K := K) v) :=
  Units.continuous_map (continuous_const.prodMk (continuous_finiteAdeleSingle v))

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem continuous_finiteProj (v : HeightOneSpectrum (𝓞 K)) :
    Continuous (finiteProj (K := K) v) :=
  Units.continuous_map ((RestrictedProduct.continuous_eval v).comp continuous_snd)

@[simp]
/- English proof (translation)
By extensionality, compare the relevant components. Simplify using the standard rewrite rules.
-/
theorem finiteProj_finiteEmbedding (v : HeightOneSpectrum (𝓞 K)) (x : (v.adicCompletion K)ˣ) :
    finiteProj v (finiteEmbedding v x) = x := by
  ext
  simp

/- English proof (translation)
By extensionality, compare the relevant components. Simplify using the standard rewrite rules. A detailed English derivation is pending.
-/
theorem finiteProj_finiteEmbedding_of_ne {v w : HeightOneSpectrum (𝓞 K)} (h : w ≠ v)
    (x : (v.adicCompletion K)ˣ) : finiteProj w (finiteEmbedding v x) = 1 := by
  ext
  simp [finiteAdeleSingle_apply_of_ne h]

@[simp]
/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem coe_finiteProj_diagonal (v : HeightOneSpectrum (𝓞 K)) (x : Kˣ) :
    ((finiteProj v (diagonal K x) : (v.adicCompletion K)ˣ) : v.adicCompletion K) =
      ((x : K) : v.adicCompletion K) :=
  rfl

end Finite

section Infinite

variable {K}

open Classical in

def infiniteAdeleSingle (w : InfinitePlace K) : w.Completion →* InfiniteAdeleRing K :=
  MonoidHom.mulSingle (fun u : InfinitePlace K ↦ u.Completion) w

omit [NumberField K] in
open Classical in
/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem infiniteAdeleSingle_apply (w u : InfinitePlace K) (x : w.Completion) :
    infiniteAdeleSingle w x u = Pi.mulSingle (M := fun u : InfinitePlace K ↦ u.Completion) w x u :=
  rfl

omit [NumberField K] in
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem continuous_infiniteAdeleSingle (w : InfinitePlace K) :
    Continuous (infiniteAdeleSingle w) := by
  classical
  exact continuous_mulSingle (A := fun u : InfinitePlace K ↦ u.Completion) w

def infiniteEmbedding (w : InfinitePlace K) : (w.Completion)ˣ →* IdeleGroup K :=
  Units.map ((MonoidHom.prod (infiniteAdeleSingle w) 1 :
    w.Completion →* InfiniteAdeleRing K × FiniteAdeleRing (𝓞 K) K))

def infiniteProj (w : InfinitePlace K) : IdeleGroup K →* (w.Completion)ˣ :=
  Units.map (((Pi.evalMonoidHom (fun u : InfinitePlace K ↦ u.Completion) w).comp
    (MonoidHom.fst (InfiniteAdeleRing K) (FiniteAdeleRing (𝓞 K) K))) :
    InfiniteAdeleRing K × FiniteAdeleRing (𝓞 K) K →* w.Completion)

@[simp]
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem coe_infiniteEmbedding (w : InfinitePlace K) (x : (w.Completion)ˣ) :
    ((infiniteEmbedding w x : IdeleGroup K) : 𝔸[K]) =
      (infiniteAdeleSingle w (x : w.Completion), 1) :=
  rfl

@[simp]
/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem coe_infiniteProj (w : InfinitePlace K) (x : IdeleGroup K) :
    ((infiniteProj w x : (w.Completion)ˣ) : w.Completion) = (x : 𝔸[K]).1 w :=
  rfl

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem continuous_infiniteEmbedding (w : InfinitePlace K) :
    Continuous (infiniteEmbedding (K := K) w) :=
  Units.continuous_map ((continuous_infiniteAdeleSingle w).prodMk continuous_const)

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem continuous_infiniteProj (w : InfinitePlace K) :
    Continuous (infiniteProj (K := K) w) :=
  Units.continuous_map ((continuous_apply w).comp continuous_fst)

@[simp]
/- English proof (translation)
By extensionality, compare the relevant components. Simplify using the standard rewrite rules.
-/
theorem infiniteProj_infiniteEmbedding (w : InfinitePlace K) (x : (w.Completion)ˣ) :
    infiniteProj w (infiniteEmbedding w x) = x := by
  classical
  ext
  simp [infiniteAdeleSingle_apply]

/- English proof (translation)
By extensionality, compare the relevant components. Simplify using the standard rewrite rules. A detailed English derivation is pending.
-/
theorem infiniteProj_infiniteEmbedding_of_ne {w u : InfinitePlace K} (h : u ≠ w)
    (x : (w.Completion)ˣ) : infiniteProj u (infiniteEmbedding w x) = 1 := by
  classical
  ext
  simp [infiniteAdeleSingle_apply, Pi.mulSingle_eq_of_ne h]

@[simp]
/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem coe_infiniteProj_diagonal (w : InfinitePlace K) (x : Kˣ) :
    ((infiniteProj w (diagonal K x) : (w.Completion)ˣ) : w.Completion) =
      ((x : K) : w.Completion) :=
  rfl

end Infinite

def integralAtFinite : Submonoid 𝔸[K] where
  carrier := {a | ∀ v : HeightOneSpectrum (𝓞 K), a.2 v ∈ v.adicCompletionIntegers K}
  one_mem' v := one_mem (v.adicCompletionIntegers K)
  mul_mem' ha hb v := mul_mem (ha v) (hb v)

/- English proof (translation)
Unfold both sides to obtain the same proposition, which implies itself.
-/
theorem mem_integralAtFinite {a : 𝔸[K]} :
    a ∈ integralAtFinite K ↔ ∀ v : HeightOneSpectrum (𝓞 K), a.2 v ∈ v.adicCompletionIntegers K :=
  Iff.rfl

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem isOpen_integralAtFinite : IsOpen (integralAtFinite K : Set 𝔸[K]) :=
  (RestrictedProduct.isOpen_forall_mem fun v : HeightOneSpectrum (𝓞 K) ↦
    Valued.isOpen_valuationSubring (v.adicCompletion K)).preimage continuous_snd

def standardOpenSubgroup : Subgroup (IdeleGroup K) := (integralAtFinite K).units

/- English proof (translation)
Rewrite the conclusion using the stated equalities.
-/
theorem mem_standardOpenSubgroup {x : IdeleGroup K} :
    x ∈ standardOpenSubgroup K ↔ ∀ v : HeightOneSpectrum (𝓞 K),
      (x : 𝔸[K]).2 v ∈ v.adicCompletionIntegers K ∧
        ((x⁻¹ : IdeleGroup K) : 𝔸[K]).2 v ∈ v.adicCompletionIntegers K := by
  rw [standardOpenSubgroup, Submonoid.mem_units_iff, mem_integralAtFinite, mem_integralAtFinite,
    ← forall_and]

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem isOpen_standardOpenSubgroup : IsOpen (standardOpenSubgroup K : Set (IdeleGroup K)) :=
  Submonoid.isOpen_units (isOpen_integralAtFinite K)

end IdeleGroup

end

end GroundTheory.Global

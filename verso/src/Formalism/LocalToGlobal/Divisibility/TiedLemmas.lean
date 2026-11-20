import Mathlib
import Formalism.LocalToGlobal.Divisibility.RowSideTie

open Module NumberField IsDedekindDomain

noncomputable section

namespace Formalism.L2.DIV

open Formalism.DivisionValues Formalism.L2.Indef

def PlConjEq (D : Formalism.BasicNotions.D7) : Prop :=
  ∀ w, D.plEq (D.what₂.places.conj w) = conjPl (D.plEq w)

section PlConj

open Formalism.BasicNotions

/- English proof (translation)
Distinguish the cases in `hx : x = 0`. Substitute `hx` using the available equality. Simplify using `[vAdd]`. Establish `h1` using `D.conj_val w x`. Rewrite `h1` using `[D.val_eq _ _ hx, D.val_eq _ _ (star_ne_zero.mpr hx)]`.

Conclude with `WithTop.coe_injective h1`.
-/
theorem plConj_vAdd (D : D7) (w : D.what₂.places.Pl) (x : D.what₂.LL) :
    vAdd (D.plEq (D.what₂.places.conj w)) x = vAdd (D.plEq w) (star x) := by
  by_cases hx : x = 0
  · subst hx
    simp [vAdd]
  · have h1 := D.conj_val w x
    rw [D.val_eq _ _ hx, D.val_eq _ _ (star_ne_zero.mpr hx)] at h1
    exact WithTop.coe_injective h1

/- English proof (translation)
Establish `hxK : (x : K) ≠ 0` using `fun h => hx (RingOfIntegers.ext (by rw [h]; simp))`. Establish `hv : w.valuation K (x : K) ≠ 0` using `(Valuation.ne_zero_iff _).mpr hxK`. Rewrite using `[← IsDedekindDomain.HeightOneSpectrum.valuation_lt_one_iff_mem (K := K) w x]`. Unfold `vAdd`. Rewrite using `[neg_pos]`.

Use `conv_rhs => rw [← WithZero.exp_lt_exp, WithZero.exp_log hv, WithZero.exp_zero]`.
-/
theorem mem_iff_vAdd_pos {K : Type} [Field K] [NumberField K] (w : HeightOneSpectrum (𝓞 K)) (x : 𝓞 K) (hx : x ≠ 0) :
    x ∈ w.asIdeal ↔ 0 < vAdd w (x : K) := by
  have hxK : (x : K) ≠ 0 := fun h => hx (RingOfIntegers.ext (by rw [h]; simp))
  have hv : w.valuation K (x : K) ≠ 0 := (Valuation.ne_zero_iff _).mpr hxK
  rw [← IsDedekindDomain.HeightOneSpectrum.valuation_lt_one_iff_mem (K := K) w x]
  unfold vAdd
  rw [neg_pos]
  conv_rhs => rw [← WithZero.exp_lt_exp, WithZero.exp_log hv, WithZero.exp_zero]

/- English proof (translation)
Unfold `PlConjEq`. Introduce `w`. Establish `hc : ∀ y : 𝓞 D.what₂.LL, ((cO D.what₂.LL y : 𝓞 D.what₂.LL) : D.what₂.LL) = star (y : D.what₂.LL)` using `fun y => rfl`. Establish `hcc : ∀ y : 𝓞 D.what₂.LL, cO D.what₂.LL (cO D.what₂.LL y) = y` using `fun y => RingOfIntegers.ext (by rw [hc, hc, star_star])`. Use extensionality with `x`.

Use `show x ∈ (D.plEq (D.what₂.places.conj w)).asIdeal ↔ x ∈ (D.plEq w).asIdeal.map (cO D.what₂.LL)`. Use `first`. Consider the case `rw [Ideal.mem_map_of_equiv]`. Consider the case `rw [Ideal.mem_map_iff_of_surjective _ (cO D.what₂.LL).surjective]`. Establish `hiff : (∃ y ∈ (D.plEq w).asIdeal, cO D.what₂.LL y = x) ↔ cO D.what₂.LL x ∈ (D.plEq w).asIdeal`.

Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨y, hy, rfl⟩`. Rewrite using `[hcc]` and apply the resulting hypothesis. Introduce `h`. Conclude with `⟨_, h, hcc x⟩`.

Rewrite using `[hiff]`. Distinguish the cases in `hx : x = 0`. Substitute `hx` using the available equality. Simplify using the standard rewrite rules. Establish `hne : cO D.what₂.LL x ≠ 0` using `fun h => hx (by rw [← hcc x, h, map_zero])`.

Rewrite using `[mem_iff_vAdd_pos _ x hx, mem_iff_vAdd_pos _ _ hne, plConj_vAdd, hc]`.
-/
theorem plConjEq (D : D7) : PlConjEq D := by
  unfold PlConjEq
  intro w
  have hc : ∀ y : 𝓞 D.what₂.LL, ((cO D.what₂.LL y : 𝓞 D.what₂.LL) : D.what₂.LL) = star (y : D.what₂.LL) :=
    fun y => rfl
  have hcc : ∀ y : 𝓞 D.what₂.LL, cO D.what₂.LL (cO D.what₂.LL y) = y := fun y =>
    RingOfIntegers.ext (by rw [hc, hc, star_star])
  ext x
  show x ∈ (D.plEq (D.what₂.places.conj w)).asIdeal ↔ x ∈ (D.plEq w).asIdeal.map (cO D.what₂.LL)
  first
    | rw [Ideal.mem_map_of_equiv]
    | rw [Ideal.mem_map_iff_of_surjective _ (cO D.what₂.LL).surjective]
  have hiff : (∃ y ∈ (D.plEq w).asIdeal, cO D.what₂.LL y = x) ↔ cO D.what₂.LL x ∈ (D.plEq w).asIdeal := by
    constructor
    · rintro ⟨y, hy, rfl⟩
      rwa [hcc]
    · intro h
      exact ⟨_, h, hcc x⟩
  rw [hiff]
  by_cases hx : x = 0
  · subst hx
    simp
  · have hne : cO D.what₂.LL x ≠ 0 := fun h => hx (by rw [← hcc x, h, map_zero])
    rw [mem_iff_vAdd_pos _ x hx, mem_iff_vAdd_pos _ _ hne, plConj_vAdd, hc]

end PlConj

section Cut

open TensorProduct Formalism.BasicNotions.Rows

section CutTensor

variable {O R W : Type} [CommRing O] [CommRing R] [Algebra O R] [AddCommGroup W] [Module O W] [Module R W]
  [IsScalarTower O R W]

/- English proof (translation)
Use `set K : Submodule O W := M ⊓ LinearMap.ker (p.restrictScalars O) with hK`. Set `q : M →ₗ[O] M` to `((p.restrictScalars O).comp M.subtype).codRestrict M (fun m => hp m m.2)`. Set `f : K →ₗ[O] M` to `Submodule.inclusion inf_le_left`. Establish `hex : Function.Exact f q`. Introduce `m`.

Prove the components needed by the constructor for the conclusion. Introduce `hm`. Use `⟨⟨m, m.2, ?_⟩, rfl⟩` and prove the remaining obligations. Use `congrArg Subtype.val hm` as an intermediate fact. Conclude with `LinearMap.mem_ker.mpr this`.

Introduce and unpack `⟨k, rfl⟩`. Apply `Subtype.ext` to reduce the goal to its premises. Establish `hk : p (k : W) = 0` using `LinearMap.mem_ker.mp k.2.2`. Conclude with `hk`. Establish `hex2` using `Module.Flat.lTensor_exact R hex`.

Use `set L := M.subtype.liftBaseChange R with hL`. Establish `hLq : ∀ z, L (q.lTensor R z) = p (L z)`. Introduce `z`. Proceed by induction on `z using TensorProduct.induction_on with`. Consider the case `zero => simp`.

Consider the case `tmul r m => first | (simp [L, q]; rfl) | simp [L, q] | rfl`. Consider the case `add a b ha hb => simp only [map_add, ha, hb]`. Establish `hLf : ∀ z, L (f.lTensor R z) = K.subtype.liftBaseChange R z`. Introduce `z`. Proceed by induction on `z using TensorProduct.induction_on with`.

Consider the case `zero => simp`. Consider the case `tmul r m => first | (simp [L, f]; rfl) | simp [L, f] | rfl`. Consider the case `add a b ha hb => simp only [map_add, ha, hb]`. Establish `hspan : ∀ z, K.subtype.liftBaseChange R z ∈ Submodule.span R (K : Set W)`. Introduce `z`.

Proceed by induction on `z using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `tmul r k => simpa using Submodule.smul_mem _ r (Submodule.subset_span k.2)`. Consider the case `add a b ha hb => simpa using Submodule.add_mem _ ha hb`. Apply `le_antisymm` to reduce the goal to its premises.

Rewrite using `[Submodule.span_le]`. Introduce `y hy`. Conclude with `⟨Submodule.subset_span hy.1, hy.2⟩`. Introduce and unpack `x ⟨hx, hpx⟩`. Establish `hxL : x ∈ LinearMap.range L`.

Establish `hle : Submodule.span R (M : Set W) ≤ LinearMap.range L`. Rewrite using `[Submodule.span_le]`. Introduce `m hm`. Conclude with `⟨1 ⊗ₜ ⟨m, hm⟩, by simp [L]⟩`. Conclude with `hle hx`.

Take `⟨z, rfl⟩` from `hxL`. Establish `hz : q.lTensor R z = 0`. Apply `hinj` to reduce the goal to its premises. Rewrite using `[hLq, map_zero]`. Conclude with `hpx`.

Take `⟨z', rfl⟩` from `(hex2 z).mp hz`. Rewrite using `[hLf]`. Conclude with `hspan z'`.
-/
theorem span_inf_ker_of_flat [Module.Flat O R] (M : Submodule O W)
    (hinj : Function.Injective (M.subtype.liftBaseChange R))
    (p : W →ₗ[R] W) (hp : ∀ x ∈ M, p x ∈ M) :
    Submodule.span R ((M ⊓ LinearMap.ker (p.restrictScalars O) : Submodule O W) : Set W) =
      Submodule.span R (M : Set W) ⊓ LinearMap.ker p := by
  set K : Submodule O W := M ⊓ LinearMap.ker (p.restrictScalars O) with hK
  let q : M →ₗ[O] M := ((p.restrictScalars O).comp M.subtype).codRestrict M (fun m => hp m m.2)
  let f : K →ₗ[O] M := Submodule.inclusion inf_le_left
  have hex : Function.Exact f q := by
    intro m
    constructor
    · intro hm
      refine ⟨⟨m, m.2, ?_⟩, rfl⟩
      have := congrArg Subtype.val hm
      exact LinearMap.mem_ker.mpr this
    · rintro ⟨k, rfl⟩
      apply Subtype.ext
      have hk : p (k : W) = 0 := LinearMap.mem_ker.mp k.2.2
      exact hk
  have hex2 := Module.Flat.lTensor_exact R hex
  set L := M.subtype.liftBaseChange R with hL
  have hLq : ∀ z, L (q.lTensor R z) = p (L z) := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul r m => first | (simp [L, q]; rfl) | simp [L, q] | rfl
    | add a b ha hb => simp only [map_add, ha, hb]
  have hLf : ∀ z, L (f.lTensor R z) = K.subtype.liftBaseChange R z := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul r m => first | (simp [L, f]; rfl) | simp [L, f] | rfl
    | add a b ha hb => simp only [map_add, ha, hb]
  have hspan : ∀ z, K.subtype.liftBaseChange R z ∈ Submodule.span R (K : Set W) := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul r k => simpa using Submodule.smul_mem _ r (Submodule.subset_span k.2)
    | add a b ha hb => simpa using Submodule.add_mem _ ha hb
  apply le_antisymm
  · rw [Submodule.span_le]
    intro y hy
    exact ⟨Submodule.subset_span hy.1, hy.2⟩
  · rintro x ⟨hx, hpx⟩
    have hxL : x ∈ LinearMap.range L := by
      have hle : Submodule.span R (M : Set W) ≤ LinearMap.range L := by
        rw [Submodule.span_le]
        intro m hm
        exact ⟨1 ⊗ₜ ⟨m, hm⟩, by simp [L]⟩
      exact hle hx
    obtain ⟨z, rfl⟩ := hxL
    have hz : q.lTensor R z = 0 := by
      apply hinj
      rw [hLq, map_zero]
      exact hpx
    obtain ⟨z', rfl⟩ := (hex2 z).mp hz
    rw [hLf]
    exact hspan z'

end CutTensor

section OForm

def OForm {O : Type} [CommRing O] {φ : O →+* ℂ} {W : Type} [AddCommGroup W] [Module ℂ W] (M : OLat O φ W) : Prop :=
  letI : Algebra O ℂ := φ.toAlgebra
  letI : Module O W := Module.compHom W φ
  haveI : IsScalarTower O ℂ W := ⟨fun a b w => mul_smul (φ a) b w⟩
  Function.Injective ((Submodule.span O (M.gen : Set W)).subtype.liftBaseChange ℂ)

/- English proof (translation)
Establish `hf : Function.Injective ((IsScalarTower.toAlgHom O R ℂ).toLinearMap)`. Introduce `a b h`. Conclude with `hR (by simpa using h)`. Establish `key : ∀ z, M.subtype.liftBaseChange R z = M.subtype.liftBaseChange ℂ (((IsScalarTower.toAlgHom O R ℂ).toLinearMap).rTensor M z)`. Introduce `z`.

Proceed by induction on `z using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `tmul r m => simp [algebraMap_smul]`. Consider the case `add a b ha hb => simp only [map_add, ha, hb]`. Introduce `a b hab`.

Apply `Module.Flat.rTensor_preserves_injective_linearMap _ hf` to reduce the goal to its premises. Apply `hC` to reduce the goal to its premises. Rewrite using `[← key, ← key, hab]`.
-/
theorem liftBaseChange_injective_of {O R W : Type} [CommRing O] [CommRing R] [Algebra O R] [Algebra O ℂ] [Algebra R ℂ]
    [IsScalarTower O R ℂ] [AddCommGroup W] [Module ℂ W] [Module O W] [Module R W] [IsScalarTower O ℂ W]
    [IsScalarTower R ℂ W] [IsScalarTower O R W] (M : Submodule O W) [Module.Flat O M]
    (hC : Function.Injective (M.subtype.liftBaseChange ℂ)) (hR : Function.Injective (algebraMap R ℂ)) :
    Function.Injective (M.subtype.liftBaseChange R) := by
  have hf : Function.Injective ((IsScalarTower.toAlgHom O R ℂ).toLinearMap) := by
    intro a b h
    exact hR (by simpa using h)
  have key : ∀ z, M.subtype.liftBaseChange R z =
      M.subtype.liftBaseChange ℂ (((IsScalarTower.toAlgHom O R ℂ).toLinearMap).rTensor M z) := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul r m => simp [algebraMap_smul]
    | add a b ha hb => simp only [map_add, ha, hb]
  intro a b hab
  apply Module.Flat.rTensor_preserves_injective_linearMap _ hf
  apply hC
  rw [← key, ← key, hab]

end OForm

section CutRec

set_option linter.style.haveILetI false in

/- English proof (translation)
Use `letI : Algebra O ℂ := φ.toAlgebra`. Use `letI : Module O W := Module.compHom W φ`. Use `haveI : IsScalarTower O ℂ W := ⟨fun a b w => mul_smul (φ a) b w⟩`. Use `letI : Algebra (𝓞 K) ℂ := (σ.comp (algebraMap (𝓞 K) K)).toAlgebra`. Use `letI : Module (𝓞 K) W := Module.compHom W (σ.comp (algebraMap (𝓞 K) K))`.

Use `haveI : IsScalarTower (𝓞 K) ℂ W := ⟨fun a b w => mul_smul (σ (a : K)) b w⟩`. Use `letI : Algebra O (𝓞 K) := ι.toAlgebra`. Establish `hsm : ∀ (a : O) (b : 𝓞 K), σ (((a • b : 𝓞 K)) : K) = φ a * σ (b : K)`. Introduce `a b`. Use `show σ (((ι a * b : 𝓞 K)) : K) = φ a * σ (b : K)`.

Rewrite using `[hφ]`. Use `push_cast`. Rewrite using `[map_mul]`. Use `haveI : IsScalarTower O (𝓞 K) W := ⟨fun a b w => by show σ (((a • b : 𝓞 K)) : K) • w = φ a • (σ (b : K) • w)`. Rewrite using `[hsm, mul_smul]⟩`.

Use `haveI : IsScalarTower O (𝓞 K) ℂ := ⟨fun a b c => by show σ (((a • b : 𝓞 K)) : K) * c = φ a * (σ (b : K) * c)`. Rewrite using `[hsm, mul_assoc]⟩`. Use `haveI : Module.IsTorsionFree O (𝓞 K) := (Module.isTorsionFree_iff_algebraMap_injective).2 hι`. Establish `hφi : Function.Injective φ`. Introduce `a b hab`.

Rewrite `hab` using `[hφ, hφ]`. Apply `hι` to reduce the goal to its premises. Conclude with `RingOfIntegers.ext (σ.injective hab)`. Use `set M' : Submodule O W := Submodule.span O (M.gen : Set W) with hM'`. Use `haveI : Module.IsTorsionFree O M' := ⟨fun r hr m1 m2 h => by`.

Establish `hr0 : r ≠ 0` using `hr.ne_zero`. Establish `h0 : φ r ≠ 0`. Introduce `h0`. Apply `hr0` to reduce the goal to its premises. Apply `hφi` to reduce the goal to its premises.

Rewrite using `[h0, map_zero]`. Apply `Subtype.ext` to reduce the goal to its premises. Establish `h'` using `congrArg Subtype.val h`. Conclude with `smul_right_injective W h0 h'⟩`. Establish `hC : Function.Injective (M'.subtype.liftBaseChange ℂ)` using `hF`.

Establish `hR : Function.Injective (algebraMap (𝓞 K) ℂ)` using `fun a b hab => RingOfIntegers.ext (σ.injective hab)`. Establish `hinj` using `liftBaseChange_injective_of M' hC hR`. Establish `hcar : ∀ y, y ∈ M.carrier ↔ y ∈ M'`. Introduce `y`. Rewrite using `[hM', Submodule.mem_span_finset]`.

Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨c, rfl⟩`. Use `⟨fun v => if v ∈ M.gen then c v else 0, ?_, ?_⟩` and prove the remaining obligations. Introduce `v hv`. Assume the negation of the conclusion as `h`.

Conclude with `hv (if_neg h)`. Use `Finset.sum_congr rfl fun v hv => ?_ dsimp only` and prove the remaining obligations. Rewrite using `[if_pos hv]`. Both sides reduce to the same expression. Introduce and unpack `⟨c, -, rfl⟩`.

Conclude with `⟨c, rfl⟩`. Set `p : W →ₗ[ℂ] W` to `(N : ℂ) • (LinearMap.id - e)`. Establish `hp : ∀ y ∈ M', p.restrictScalars (𝓞 K) y ∈ M'`. Introduce `y hy`. Establish `h1 : (N : ℂ) • y ∈ M'`.

Establish `: (N : O) • y = (N : ℂ) • y` using `by show φ (N : O) • y = _`. Rewrite using `[map_natCast]`. Rewrite using `[← this]`. Conclude with `M'.smul_mem _ hy`. Establish `h2 : (N : ℂ) • e y ∈ M'` using `(hcar _).1 (hA y ((hcar y).2 hy))`.

Use `show (N : ℂ) • (y - e y) ∈ M'`. Rewrite using `[smul_sub]`. Conclude with `M'.sub_mem h1 h2`. Establish `hmain` using `span_inf_ker_of_flat M' hinj (p.restrictScalars (𝓞 K)) hp`. Establish `hker : ∀ y, p y = 0 ↔ y ∈ Set.range e`.

Introduce `y`. Establish `hN' : (N : ℂ) ≠ 0` using `by exact_mod_cast hN`. Prove the components needed by the constructor for the conclusion. Introduce `h`. Establish `h' : (N : ℂ) • (y - e y) = 0` using `h`.

Rewrite `h'` using `[smul_eq_zero]`. Break down `h' with h' | h'` into its components or cases. Conclude with `absurd h' hN'`. Conclude with `⟨y, (sub_eq_zero.1 h').symm⟩`. Introduce and unpack `⟨z, rfl⟩ show (N : ℂ) • (e z - e (e z)) = 0`.

Establish `: e (e z) = e z`. Use `congrArg (fun f : W →ₗ[ℂ] W => f z) he` as an intermediate fact. Simplify using `using this`. Rewrite using `[this, sub_self, smul_zero]`. Establish `hL : x ∈ Submodule.span (𝓞 K) ((M' ⊓ LinearMap.ker ((p.restrictScalars (𝓞 K)).restrictScalars O) : Submodule O W) : Set W) ↔ ∃ (s : Finset W) (c : W → 𝓞 K), (s : Set W) ⊆ M.carrier ∩ Set.range e ∧ x = ∑ y ∈ s, σ (c y) • y`.

Rewrite using `[Submodule.mem_span_iff_exists_finset_subset]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨c, s, hs, -, rfl⟩`. Use `⟨s, c, fun y hy => ⟨(hcar y).2 (hs hy).1, (hker y).1 (hs hy).2⟩, rfl⟩` and prove the remaining obligations. Introduce and unpack `⟨s, c, hs, rfl⟩`.

Use `⟨fun y => if y ∈ s then c y else 0, s, fun y hy => ⟨(hcar y).1 (hs hy).1, (hker y).2 (hs hy).2⟩, ?_, ?_⟩` and prove the remaining obligations. Introduce `v hv`. Assume the negation of the conclusion as `h`. Conclude with `hv (if_neg h)`. Use `Finset.sum_congr rfl fun v hv => ?_ dsimp only` and prove the remaining obligations.

Rewrite using `[if_pos hv]`. Both sides reduce to the same expression. Establish `hRt : x ∈ Submodule.span (𝓞 K) (M' : Set W) ↔ ∃ c : W → 𝓞 K, x = ∑ v ∈ M.gen, σ (c v) • v`. Rewrite using `[hM', Submodule.span_span_of_tower, Submodule.mem_span_finset]`. Prove the components needed by the constructor for the conclusion.

Introduce and unpack `⟨c, -, rfl⟩`. Conclude with `⟨c, rfl⟩`. Introduce and unpack `⟨c, rfl⟩`. Use `⟨fun v => if v ∈ M.gen then c v else 0, ?_, ?_⟩` and prove the remaining obligations. Introduce `v hv`.

Assume the negation of the conclusion as `h`. Conclude with `hv (if_neg h)`. Use `Finset.sum_congr rfl fun v hv => ?_ dsimp only` and prove the remaining obligations. Rewrite using `[if_pos hv]`. Both sides reduce to the same expression.

Rewrite using `[← hL, hmain, Submodule.mem_inf, hRt]`. Conclude with `and_congr Iff.rfl (hker x)`.
-/
theorem cut_tensorUp {O : Type} [CommRing O] [IsDedekindDomain O] {K : Type} [Field K] [NumberField K]
    (σ : K →+* ℂ) (ι : O →+* 𝓞 K) (hι : Function.Injective ι) {φ : O →+* ℂ} (hφ : ∀ a, φ a = σ (ι a))
    {W : Type} [AddCommGroup W] [Module ℂ W] (M : OLat O φ W) (hF : OForm M)
    (e : W →ₗ[ℂ] W) (he : e ∘ₗ e = e) {N : ℕ} (hN : N ≠ 0)
    (hA : ∀ x ∈ M.carrier, (N : ℂ) • e x ∈ M.carrier) (x : W) :
    (∃ (s : Finset W) (c : W → 𝓞 K), (s : Set W) ⊆ M.carrier ∩ Set.range e ∧ x = ∑ y ∈ s, σ (c y) • y) ↔
      ((∃ c : W → 𝓞 K, x = ∑ v ∈ M.gen, σ (c v) • v) ∧ x ∈ Set.range e) := by
  classical
  letI : Algebra O ℂ := φ.toAlgebra
  letI : Module O W := Module.compHom W φ
  haveI : IsScalarTower O ℂ W := ⟨fun a b w => mul_smul (φ a) b w⟩
  letI : Algebra (𝓞 K) ℂ := (σ.comp (algebraMap (𝓞 K) K)).toAlgebra
  letI : Module (𝓞 K) W := Module.compHom W (σ.comp (algebraMap (𝓞 K) K))
  haveI : IsScalarTower (𝓞 K) ℂ W := ⟨fun a b w => mul_smul (σ (a : K)) b w⟩
  letI : Algebra O (𝓞 K) := ι.toAlgebra
  have hsm : ∀ (a : O) (b : 𝓞 K), σ (((a • b : 𝓞 K)) : K) = φ a * σ (b : K) := by
    intro a b
    show σ (((ι a * b : 𝓞 K)) : K) = φ a * σ (b : K)
    rw [hφ]; push_cast; rw [map_mul]
  haveI : IsScalarTower O (𝓞 K) W := ⟨fun a b w => by
    show σ (((a • b : 𝓞 K)) : K) • w = φ a • (σ (b : K) • w)
    rw [hsm, mul_smul]⟩
  haveI : IsScalarTower O (𝓞 K) ℂ := ⟨fun a b c => by
    show σ (((a • b : 𝓞 K)) : K) * c = φ a * (σ (b : K) * c)
    rw [hsm, mul_assoc]⟩
  haveI : Module.IsTorsionFree O (𝓞 K) := (Module.isTorsionFree_iff_algebraMap_injective).2 hι
  have hφi : Function.Injective φ := by
    intro a b hab
    rw [hφ, hφ] at hab
    apply hι
    exact RingOfIntegers.ext (σ.injective hab)
  set M' : Submodule O W := Submodule.span O (M.gen : Set W) with hM'
  haveI : Module.IsTorsionFree O M' := ⟨fun r hr m1 m2 h => by
    have hr0 : r ≠ 0 := hr.ne_zero
    have h0 : φ r ≠ 0 := by
      intro h0; apply hr0; apply hφi; rw [h0, map_zero]
    apply Subtype.ext
    have h' := congrArg Subtype.val h
    exact smul_right_injective W h0 h'⟩
  have hC : Function.Injective (M'.subtype.liftBaseChange ℂ) := hF
  have hR : Function.Injective (algebraMap (𝓞 K) ℂ) := fun a b hab =>
    RingOfIntegers.ext (σ.injective hab)
  have hinj := liftBaseChange_injective_of M' hC hR

  have hcar : ∀ y, y ∈ M.carrier ↔ y ∈ M' := by
    intro y
    rw [hM', Submodule.mem_span_finset]
    constructor
    · rintro ⟨c, rfl⟩
      refine ⟨fun v => if v ∈ M.gen then c v else 0, ?_, ?_⟩
      · intro v hv
        by_contra h
        exact hv (if_neg h)
      · refine Finset.sum_congr rfl fun v hv => ?_
        dsimp only
        rw [if_pos hv]; rfl
    · rintro ⟨c, -, rfl⟩
      exact ⟨c, rfl⟩
  let p : W →ₗ[ℂ] W := (N : ℂ) • (LinearMap.id - e)
  have hp : ∀ y ∈ M', p.restrictScalars (𝓞 K) y ∈ M' := by
    intro y hy
    have h1 : (N : ℂ) • y ∈ M' := by
      have : (N : O) • y = (N : ℂ) • y := by
        show φ (N : O) • y = _
        rw [map_natCast]
      rw [← this]; exact M'.smul_mem _ hy
    have h2 : (N : ℂ) • e y ∈ M' := (hcar _).1 (hA y ((hcar y).2 hy))
    show (N : ℂ) • (y - e y) ∈ M'
    rw [smul_sub]
    exact M'.sub_mem h1 h2
  have hmain := span_inf_ker_of_flat M' hinj (p.restrictScalars (𝓞 K)) hp
  have hker : ∀ y, p y = 0 ↔ y ∈ Set.range e := by
    intro y
    have hN' : (N : ℂ) ≠ 0 := by exact_mod_cast hN
    constructor
    · intro h
      have h' : (N : ℂ) • (y - e y) = 0 := h
      rw [smul_eq_zero] at h'
      rcases h' with h' | h'
      · exact absurd h' hN'
      · exact ⟨y, (sub_eq_zero.1 h').symm⟩
    · rintro ⟨z, rfl⟩
      show (N : ℂ) • (e z - e (e z)) = 0
      have : e (e z) = e z := by
        have := congrArg (fun f : W →ₗ[ℂ] W => f z) he
        simpa using this
      rw [this, sub_self, smul_zero]
  have hL : x ∈ Submodule.span (𝓞 K) ((M' ⊓ LinearMap.ker ((p.restrictScalars (𝓞 K)).restrictScalars O) :
      Submodule O W) : Set W) ↔
      ∃ (s : Finset W) (c : W → 𝓞 K), (s : Set W) ⊆ M.carrier ∩ Set.range e ∧ x = ∑ y ∈ s, σ (c y) • y := by
    rw [Submodule.mem_span_iff_exists_finset_subset]
    constructor
    · rintro ⟨c, s, hs, -, rfl⟩
      refine ⟨s, c, fun y hy => ⟨(hcar y).2 (hs hy).1, (hker y).1 (hs hy).2⟩, rfl⟩
    · rintro ⟨s, c, hs, rfl⟩
      refine ⟨fun y => if y ∈ s then c y else 0, s, fun y hy => ⟨(hcar y).1 (hs hy).1, (hker y).2 (hs hy).2⟩,
        ?_, ?_⟩
      · intro v hv
        by_contra h
        exact hv (if_neg h)
      · refine Finset.sum_congr rfl fun v hv => ?_
        dsimp only
        rw [if_pos hv]; rfl
  have hRt : x ∈ Submodule.span (𝓞 K) (M' : Set W) ↔ ∃ c : W → 𝓞 K, x = ∑ v ∈ M.gen, σ (c v) • v := by
    rw [hM', Submodule.span_span_of_tower, Submodule.mem_span_finset]
    constructor
    · rintro ⟨c, -, rfl⟩; exact ⟨c, rfl⟩
    · rintro ⟨c, rfl⟩
      refine ⟨fun v => if v ∈ M.gen then c v else 0, ?_, ?_⟩
      · intro v hv
        by_contra h
        exact hv (if_neg h)
      · refine Finset.sum_congr rfl fun v hv => ?_
        dsimp only
        rw [if_pos hv]; rfl
  rw [← hL, hmain, Submodule.mem_inf, hRt]
  exact and_congr Iff.rfl (hker x)

/- English proof (translation)
The claim follows from `D.what₂.restRowsFiniteGroupCard_pos`.
-/
theorem restRowsFiniteGroupCard_pos (D : Formalism.BasicNotions.D7) : 0 < D.what₂.restRowsFiniteGroupCard := D.what₂.restRowsFiniteGroupCard_pos

/- English proof (translation)
Use `haveI := hO`. Conclude with `cut_tensorUp D.what₂.embLL ι hι (fun a => by rw [hιO]; rfl) (X.Mtilde μ) hF (X.eOp μ) (X.eOp_idem μ) (restRowsFiniteGroupCard_pos D).ne' (fun y hy => hA μ y hy) x`.
-/
theorem cut_tensorUp_row {D : Formalism.BasicNotions.D7} {EE : Type} [NormedAddCommGroup EE] [InnerProductSpace ℂ EE] [FiniteDimensional ℂ EE]
    (X : Formalism.BasicNotions.RowSide D EE) (hO : IsDedekindDomain D.what₂.O) (ι : D.what₂.O →+* 𝓞 D.what₂.LL)
    (hι : Function.Injective ι) (hιO : ∀ a, ((ι a : 𝓞 D.what₂.LL) : D.what₂.LL) = D.what₂.OtoLL a)
    (hA : X.AIntegral) (μ : D.what₂.Tup) (hF : OForm (X.Mtilde μ)) (x : X.Amb μ) :
    (∃ (s : Finset (X.Amb μ)) (c : X.Amb μ → 𝓞 D.what₂.LL),
        (s : Set (X.Amb μ)) ⊆ (X.Mtilde μ).carrier ∩ (X.V0 μ : Set (X.Amb μ)) ∧
        x = ∑ y ∈ s, D.what₂.embLL (c y : D.what₂.LL) • y) ↔
      ((∃ c : X.Amb μ → 𝓞 D.what₂.LL, x = ∑ v ∈ (X.Mtilde μ).gen, D.what₂.embLL (c v : D.what₂.LL) • v) ∧
        x ∈ X.V0 μ) := by
  haveI := hO
  exact cut_tensorUp D.what₂.embLL ι hι (fun a => by rw [hιO]; rfl) (X.Mtilde μ) hF (X.eOp μ)
    (X.eOp_idem μ) (restRowsFiniteGroupCard_pos D).ne' (fun y hy => hA μ y hy) x

end CutRec

end Cut

section Fam

variable (D : Formalism.BasicNotions.D7) {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {m : ℕ}
  (A : FamIn D.what₂.LL G Pl0 T m)

/- English proof (translation)
Establish `h1` using `D.R.two_le_m`. Take `⟨j, hj⟩` from `D.R.m_even`. Unfold `Formalism.BasicNotions.Ranks.r Formalism.BasicNotions.Ranks.rS`. Use linear arithmetic over natural numbers and integers.
-/
theorem ranks_r_sym (D : Formalism.BasicNotions.D7) : D.R.r = D.R.k + 2 * D.R.rS + 1 := by
  have h1 := D.R.two_le_m
  obtain ⟨j, hj⟩ := D.R.m_even
  unfold Formalism.BasicNotions.Ranks.r Formalism.BasicNotions.Ranks.rS
  omega

variable {D A} in

/- English proof (translation)
The claim follows from `h.1.symm`.
-/
theorem column_tuple_of_level_link {P0 : Subgroup G} {ψ0 : P0 →* D.what₂.LLˣ} {Ps : Subgroup G} {ψs : Ps →* D.what₂.LLˣ}
    {Zs : DefSub A.fam.amb} {S0 : IndefData (A.side P0 ψ0 Zs)} {S1 : IndefData (A.side Ps ψs Zs)}
    (h : LevelLink S0 S1) : S1.μ = S0.μ := h.1.symm

def BuTie {P0 : Subgroup G} {ψ0 : P0 →* D.what₂.LLˣ} {Ps : Subgroup G} {ψs : Ps →* D.what₂.LLˣ}
    {Zs : DefSub A.fam.amb} {S0 : IndefData (A.side P0 ψ0 Zs)} {S1 : IndefData (A.side Ps ψs Zs)}
    {X0 : Formalism.BasicNotions.BaseLevelRowSide D} {Dc : DefCols (A.side Ps ψs Zs)} {Sp : SPer Dc} (C : ColData Dc Sp S1)
    (NuC : ∀ u, Submodule (𝓞 D.what₂.LL) (Fin (Dc.a u) → D.what₂.LL))
    (I : DivisionCompatibilityData D A P0 ψ0 Ps ψs Zs S0 S1 X0 Dc) : Prop :=
  DivisionCompatible D A P0 ψ0 Ps ψs Zs S0 S1 X0 C NuC I → D.BuRational →
    ∀ u x y, D.what₂.Bu u (D.jN u (I.eNu u x)) (D.jEE (I.eRR y)) = D.what₂.embLL (C.B (I.wU u) x y)

def JwIdxTie (P : Subgroup G) (ψ : P →* D.what₂.LLˣ) (Zs : DefSub A.fam.amb) (tup : T → D.what₂.Tup)
    (eMt : ∀ (i : Fin m) (t : T),
      (Fin (lDim D A P ψ i t) → D.what₂.LL) ≃ₗ[D.what₂.LL] D.what₂.MtL (tup t) ((i : ℕ) + 1)) : Prop :=
  ∀ s : ℕ, A.fam.Ok s → m ≤ D.R.m → MtTie D A P ψ Zs tup eMt → Formalism.BasicNotions.Idx.ProjectionIsSpectralProjector D →
    ∀ (i : Fin m) (t : T) w, Formalism.BasicNotions.Idx.jwIdx D (tup t) ((i : ℕ) + 1) w =
      Formalism.DivisionValues.jw ((A.side P ψ Zs).HT i t) (D.plEq w) ((A.side P ψ Zs).Tl i t)

structure MjXTie {P0 : Subgroup G} {ψ0 : P0 →* D.what₂.LLˣ} {Zs : DefSub A.fam.amb}
    (S0 : IndefData (A.side P0 ψ0 Zs)) (X : Formalism.BasicNotions.DivX D)
    (jW : ∀ i : Fin m, (Fin (S0.dW i) → D.what₂.LL) →ₛₗ[D.what₂.embLL] D.what₂.Mj ((i : ℕ) + 1))
    (eW : ∀ i : Fin m, (Fin (S0.dW i) → D.what₂.LL) ≃ₗ[D.what₂.LL] (X.MjH ((i : ℕ) + 1)).V) : Prop where

  lat : ∀ i : Fin m, HLatTie (X.MjH ((i : ℕ) + 1)) (S0.M i) (S0.XW i) (eW i)

  jM : ∀ (i : Fin m) y, X.jM ((i : ℕ) + 1) (eW i y) = jW i y

def IjIdxTie (X : Formalism.BasicNotions.DivX D) {P0 : Subgroup G} {ψ0 : P0 →* D.what₂.LLˣ} {Zs : DefSub A.fam.amb}
    (S0 : IndefData (A.side P0 ψ0 Zs)) (tup : T → D.what₂.Tup)
    (eMt : ∀ (i : Fin m) (t : T),
      (Fin (lDim D A P0 ψ0 i t) → D.what₂.LL) ≃ₗ[D.what₂.LL] D.what₂.MtL (tup t) ((i : ℕ) + 1))
    (jW : ∀ i : Fin m, (Fin (S0.dW i) → D.what₂.LL) →ₛₗ[D.what₂.embLL] D.what₂.Mj ((i : ℕ) + 1))
    (eW : ∀ i : Fin m, (Fin (S0.dW i) → D.what₂.LL) ≃ₗ[D.what₂.LL] (X.MjH ((i : ℕ) + 1)).V) : Prop :=
  ∀ s : ℕ, A.fam.Ok s → m ≤ D.R.m → MtTie D A P0 ψ0 Zs tup eMt → ThTie D A S0 tup eMt jW →
    MjXTie D A S0 X jW eW →
    ∀ (i : Fin m) (t : T) w, Formalism.BasicNotions.Idx.IjIdx X (tup t) ((i : ℕ) + 1) w = S0.Iw i t (D.plEq w)

def RRMuTie {EE : Type} [NormedAddCommGroup EE] [InnerProductSpace ℂ EE] [FiniteDimensional ℂ EE]
    (X : Formalism.BasicNotions.RowSide D EE) (P : Subgroup G) (ψ : P →* D.what₂.LLˣ) (Zs : DefSub A.fam.amb)
    (S : IndefData (A.side P ψ Zs)) (eRR : (Fin S.D → D.what₂.LL) ≃ₗ[D.what₂.LL] X.RR.V) : Prop :=
  HLatTie X.RR S.RR S.XE eRR → S.RR.FG →
    Submodule.span D.what₂.LL (S.RR : Set (Fin S.D → D.what₂.LL)) = ⊤ →
    X.RR.muMax = S.muMaxRR ∧ X.RR.muDual = S.muCC

def RRDefTie {EE : Type} [NormedAddCommGroup EE] [InnerProductSpace ℂ EE] [FiniteDimensional ℂ EE]
    (X : Formalism.BasicNotions.RowSide D EE) (P : Subgroup G) (ψ : P →* D.what₂.LLˣ) (Zs : DefSub A.fam.amb)
    (S : IndefData (A.side P ψ Zs)) (tup : T → D.what₂.Tup)
    (eRR : (Fin S.D → D.what₂.LL) ≃ₗ[D.what₂.LL] X.RR.V)
    (jA : ∀ t, (Fin (rDim D A P ψ t) → D.what₂.LL) →ₛₗ[D.what₂.embLL] X.Amb (tup t)) : Prop :=
  ∀ s : ℕ, A.fam.Ok s → IsDedekindDomain D.what₂.O →
    (∃ ι : D.what₂.O →+* 𝓞 D.what₂.LL, Function.Injective ι ∧
      ∀ a, ((ι a : 𝓞 D.what₂.LL) : D.what₂.LL) = D.what₂.OtoLL a) →
    X.AIntegral → (∀ t, OForm (X.Mtilde (tup t))) →
    RowSideTie D A X P ψ Zs S tup eRR jA → TupTie D A S tup → (A.side P ψ Zs).WF →
    X.RRDef

end Fam

section Inhabit

variable {K : Type} [Field K] [NumberField K] [StarRing K]

end Inhabit

noncomputable def jRat : (Fin 1 → ℚ) →ₛₗ[Rat.castHom ℂ] ℂ where
  toFun x := (x 0 : ℂ)
  map_add' x y := by simp
  map_smul' a x := by simp

noncomputable def oLatRat : Formalism.BasicNotions.Rows.OLat ℤ (Int.castRingHom ℂ) ℂ where
  gen := {1}
  span_top := by
    rw [eq_top_iff]
    intro z _
    have := Submodule.smul_mem (Submodule.span ℂ ({1} : Set ℂ)) z (Submodule.subset_span rfl)
    simpa using this

end Formalism.L2.DIV

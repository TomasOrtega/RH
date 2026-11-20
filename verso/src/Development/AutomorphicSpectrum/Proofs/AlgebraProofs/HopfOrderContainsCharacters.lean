import Mathlib
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.TranslateMemIndOrder
open GlobalTheory.CompanionTheory.Ar.BT TensorProduct

namespace GlobalTheory.CompanionTheory.Ar.BT.CharExt

variable {R : Type} [CommRing R] {T : Type} [CommGroup T] [Fintype T]
variable (K : Type) [Field K] [Algebra R K]

def dualOrder (A : Subalgebra R (T → R)) : Submodule R (T → K) where
  carrier := {l | ∀ f ∈ A, ∃ r : R, algebraMap R K r = ∑ t, l t * algebraMap R K (f t)}
  add_mem' := by
    rintro a b ha hb f hf
    obtain ⟨r, hr⟩ := ha f hf
    obtain ⟨s, hs⟩ := hb f hf
    exact ⟨r + s, by simp [add_mul, Finset.sum_add_distrib, hr, hs]⟩
  zero_mem' := fun f _ => ⟨0, by simp⟩
  smul_mem' := by
    rintro c a ha f hf
    obtain ⟨r, hr⟩ := ha f hf
    exact ⟨c * r, by simp [map_mul, hr, Finset.mul_sum, Algebra.smul_def, mul_assoc]⟩

variable {K}

def conv (l m : T → K) : T → K := fun t => ∑ x, l x * m (x⁻¹ * t)

/- English proof (translation)
Simplify using `only [conv, Finset.sum_mul]`. Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_congr rfl fun x _ => ?_` and prove the remaining obligations. Conclude with `Fintype.sum_equiv (Equiv.mulLeft x⁻¹) _ _ (fun t => by simp)`.
-/
lemma sum_conv_mul (l m g : T → K) :
    ∑ t, conv l m t * g t = ∑ x, ∑ y, l x * m y * g (x * y) := by
  simp only [conv, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun x _ => ?_
  exact Fintype.sum_equiv (Equiv.mulLeft x⁻¹) _ _ (fun t => by simp)

/- English proof (translation)
Introduce `f hf`. Establish `key : ∀ g ∈ prodSpan A, ∃ r : R, algebraMap R K r = ∑ x, ∑ y, l x * m y * algebraMap R K (g (x, y))`. Introduce `g hg`. Proceed by induction on `hg using Submodule.span_induction with`. Consider the case `mem g hg`.

Take `⟨a, ha, b, hb, rfl⟩` from `hg`. Take `⟨r, hr⟩` from `hl a ha`. Take `⟨s, hs⟩` from `hm b hb`. Use `⟨r * s, ?_⟩` and prove the remaining obligations. Rewrite using `[map_mul, hr, hs, Finset.sum_mul_sum]`.

Use `Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_` and prove the remaining obligations. Simplify using `only [map_mul]`. Expand and normalize the polynomial expressions, which then agree. Consider the case `zero => exact ⟨0, by simp⟩`. Consider the case `add g h _ _ hg hh`.

Take `⟨r, hr⟩` from `hg`. Take `⟨s, hs⟩` from `hh`. Use `⟨r + s, ?_⟩` and prove the remaining obligations. Simplify using `[hr, hs, mul_add, Finset.sum_add_distrib]`. Consider the case `smul c g _ hg`.

Take `⟨r, hr⟩` from `hg`. Use `⟨c * r, ?_⟩` and prove the remaining obligations. Simplify using `only [map_mul, hr, Finset.mul_sum, Pi.smul_apply, smul_eq_mul]`. Use `Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_` and prove the remaining obligations. Expand and normalize the polynomial expressions, which then agree.

Take `⟨r, hr⟩` from `key _ (hc f hf)`. Use `⟨r, ?_⟩` and prove the remaining obligations. Rewrite using `[hr, sum_conv_mul l m (fun t => algebraMap R K (f t))]`.
-/
lemma conv_mem {A : Subalgebra R (T → R)} (hc : ∀ f ∈ A, (fun z : T × T => f (z.1 * z.2)) ∈ prodSpan A)
    {l m : T → K} (hl : l ∈ dualOrder K A) (hm : m ∈ dualOrder K A) : conv l m ∈ dualOrder K A := by
  intro f hf
  have key : ∀ g ∈ prodSpan A, ∃ r : R, algebraMap R K r =
      ∑ x, ∑ y, l x * m y * algebraMap R K (g (x, y)) := by
    intro g hg
    induction hg using Submodule.span_induction with
    | mem g hg =>
      obtain ⟨a, ha, b, hb, rfl⟩ := hg
      obtain ⟨r, hr⟩ := hl a ha
      obtain ⟨s, hs⟩ := hm b hb
      refine ⟨r * s, ?_⟩
      rw [map_mul, hr, hs, Finset.sum_mul_sum]
      refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
      simp only [map_mul]; ring
    | zero => exact ⟨0, by simp⟩
    | add g h _ _ hg hh =>
      obtain ⟨r, hr⟩ := hg
      obtain ⟨s, hs⟩ := hh
      refine ⟨r + s, ?_⟩
      simp [hr, hs, mul_add, Finset.sum_add_distrib]
    | smul c g _ hg =>
      obtain ⟨r, hr⟩ := hg
      refine ⟨c * r, ?_⟩
      simp only [map_mul, hr, Finset.mul_sum, Pi.smul_apply, smul_eq_mul]
      refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
      ring
  obtain ⟨r, hr⟩ := key _ (hc f hf)
  refine ⟨r, ?_⟩
  rw [hr, sum_conv_mul l m (fun t => algebraMap R K (f t))]

open Classical in

noncomputable def psi {A : Subalgebra R (T → R)} (d : R) (hd : ∀ f : T → R, d • f ∈ A) :
    Module.Dual R A →ₗ[R] (T → K) where
  toFun l t := algebraMap R K (l ⟨d • Pi.single t 1, hd _⟩) / algebraMap R K d
  map_add' := by intros; ext; simp [add_div]
  map_smul' := by intros; ext; simp [mul_div_assoc, Algebra.smul_def]

/- English proof (translation)
Establish `hdK : algebraMap R K d ≠ 0`. Simplify using `using (FaithfulSMul.algebraMap_injective R K).ne hd0`. Establish `e : d • (⟨f, hf⟩ : A) = ∑ t, f t • (⟨d • Pi.single t 1, hd _⟩ : A)`. Apply `Subtype.ext` to reduce the goal to its premises. Use function extensionality and compare the values at `s`.

Simplify using `[Finset.sum_apply, Pi.single_apply, mul_comm]`. Establish `e2` using `congrArg (fun a => algebraMap R K (l a)) e`. Simplify using `only [map_smul, map_sum, smul_eq_mul, map_mul] at e2`. Simplify using `only [psi, LinearMap.coe_mk, AddHom.coe_mk]`. Rewrite using `[eq_comm, ← mul_right_inj' hdK, e2, Finset.mul_sum]`.

Use `Finset.sum_congr rfl fun t _ => ?_` and prove the remaining obligations. Clear the denominators using the available nonvanishing facts.
-/
lemma psi_pair [FaithfulSMul R K] {A : Subalgebra R (T → R)} {d : R} (hd0 : d ≠ 0) (hd : ∀ f : T → R, d • f ∈ A)
    (l : Module.Dual R A) (f : T → R) (hf : f ∈ A) :
    ∑ t, psi (K := K) d hd l t * algebraMap R K (f t) = algebraMap R K (l ⟨f, hf⟩) := by
  classical
  have hdK : algebraMap R K d ≠ 0 := by
    simpa using (FaithfulSMul.algebraMap_injective R K).ne hd0
  have e : d • (⟨f, hf⟩ : A) = ∑ t, f t • (⟨d • Pi.single t 1, hd _⟩ : A) := by
    apply Subtype.ext
    funext s
    simp [Finset.sum_apply, Pi.single_apply, mul_comm]
  have e2 := congrArg (fun a => algebraMap R K (l a)) e
  simp only [map_smul, map_sum, smul_eq_mul, map_mul] at e2
  simp only [psi, LinearMap.coe_mk, AddHom.coe_mk]
  rw [eq_comm, ← mul_right_inj' hdK, e2, Finset.mul_sum]
  refine Finset.sum_congr rfl fun t _ => ?_
  field_simp

/- English proof (translation)
Establish `hinj` using `FaithfulSMul.algebraMap_injective R K`. Establish `hdK : algebraMap R K d ≠ 0` using `by simpa using hinj.ne hd0`. Apply `le_antisymm` to reduce the goal to its premises. Introduce and unpack `_ ⟨l, rfl⟩ f hf`. Conclude with `⟨l ⟨f, hf⟩, (psi_pair hd0 hd l f hf).symm⟩`.

Introduce `l hl choose L hL using fun f : A => hl f.1 f.2`. Set `L' : Module.Dual R A` to `{ toFun := L map_add' := fun a b => hinj (by`. Simplify using `[hL, add_mul, mul_add, Finset.sum_add_distrib])`. Use the proof step `map_smul' := fun c a => hinj (by`. Simplify using `[hL, Finset.mul_sum, mul_left_comm]) }`.

Use `⟨L', ?_⟩` and prove the remaining obligations. Use function extensionality and compare the values at `t`. Simplify using `only [psi, LinearMap.coe_mk, AddHom.coe_mk]`. Express the relevant statement in the definitionally equal form `algebraMap R K (L _) / _ = _`. Rewrite using `[hL]`.

Simplify using `[Pi.single_apply, div_eq_iff hdK, apply_ite (algebraMap R K)]`.
-/
lemma range_psi [FaithfulSMul R K] {A : Subalgebra R (T → R)} {d : R} (hd0 : d ≠ 0) (hd : ∀ f : T → R, d • f ∈ A) :
    LinearMap.range (psi (K := K) d hd) = dualOrder K A := by
  classical
  have hinj := FaithfulSMul.algebraMap_injective R K
  have hdK : algebraMap R K d ≠ 0 := by simpa using hinj.ne hd0
  apply le_antisymm
  · rintro _ ⟨l, rfl⟩ f hf
    exact ⟨l ⟨f, hf⟩, (psi_pair hd0 hd l f hf).symm⟩
  · intro l hl
    choose L hL using fun f : A => hl f.1 f.2
    let L' : Module.Dual R A :=
      { toFun := L
        map_add' := fun a b => hinj (by
          simp [hL, add_mul, mul_add, Finset.sum_add_distrib])
        map_smul' := fun c a => hinj (by
          simp [hL, Finset.mul_sum, mul_left_comm]) }
    refine ⟨L', ?_⟩
    funext t
    simp only [psi, LinearMap.coe_mk, AddHom.coe_mk]
    change algebraMap R K (L _) / _ = _
    rw [hL]
    simp [Pi.single_apply, div_eq_iff hdK, apply_ite (algebraMap R K)]

def pairWith (c : T → K) : (T → K) →ₗ[R] K where
  toFun l := ∑ t, l t * c t
  map_add' := by intros; simp [add_mul, Finset.sum_add_distrib]
  map_smul' := by intros; simp [Finset.mul_sum, Algebra.smul_def, mul_assoc]

/- English proof (translation)
Simplify using `only [pairWith, LinearMap.coe_mk, AddHom.coe_mk]`. Rewrite using `[sum_conv_mul, Finset.sum_mul_sum]`. Use `Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_` and prove the remaining obligations. Rewrite using `[hc]`. Expand and normalize the polynomial expressions, which then agree.
-/
lemma pairWith_conv {c : T → K} (hc : ∀ x y, c (x * y) = c x * c y) (l m : T → K) :
    pairWith (R := R) c (conv l m) = pairWith (R := R) c l * pairWith (R := R) c m := by
  simp only [pairWith, LinearMap.coe_mk, AddHom.coe_mk]
  rw [sum_conv_mul, Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
  rw [hc]; ring

/- English proof (translation)
Take `⟨d, hd0, hd⟩` from `hA.full`. Use `haveI := hA.finite`. Use `haveI := hA.projective`. Establish `hfg : (dualOrder K A).FG`. Rewrite using `[← range_psi hd0 hd]`.

Rewrite using `[← Submodule.map_top]`. Conclude with `(Module.Finite.fg_top (R := R) (M := Module.Dual R A)).map _`. Set `M : Submodule R K` to `(dualOrder K A).map (pairWith (R := R) c)`. Establish `hone : (1 : K) ∈ M`. Use `⟨Pi.single 1 1, ?_, ?_⟩` and prove the remaining obligations.

Introduce `f _`. Conclude with `⟨f 1, by simp [Pi.single_apply]⟩`. Simplify using `[pairWith, Pi.single_apply, hc1]`. Establish `hmul : ∀ x ∈ M, ∀ y ∈ M, x * y ∈ M`. Introduce and unpack `_ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩`.

Conclude with `⟨conv a b, conv_mem hA.comul ha hb, pairWith_conv hc a b⟩`. Set `S : Subalgebra R K` to `M.toSubalgebra hone (fun x y hx hy => hmul x hx y hy)`. Conclude with `IsIntegral.of_mem_of_fg S (by simpa [S] using hfg.map _) _ ⟨l, hl, rfl⟩`.
-/
lemma isIntegral_pairWith [FaithfulSMul R K] {A : Subalgebra R (T → R)} (hA : IsHopfOrder A)
    {c : T → K} (hc : ∀ x y, c (x * y) = c x * c y) (hc1 : c 1 = 1)
    {l : T → K} (hl : l ∈ dualOrder K A) : IsIntegral R (pairWith (R := R) c l) := by
  classical
  obtain ⟨d, hd0, hd⟩ := hA.full
  haveI := hA.finite
  haveI := hA.projective
  have hfg : (dualOrder K A).FG := by
    rw [← range_psi hd0 hd]
    rw [← Submodule.map_top]
    exact (Module.Finite.fg_top (R := R) (M := Module.Dual R A)).map _
  let M : Submodule R K := (dualOrder K A).map (pairWith (R := R) c)
  have hone : (1 : K) ∈ M := by
    refine ⟨Pi.single 1 1, ?_, ?_⟩
    · intro f _
      exact ⟨f 1, by simp [Pi.single_apply]⟩
    · simp [pairWith, Pi.single_apply, hc1]
  have hmul : ∀ x ∈ M, ∀ y ∈ M, x * y ∈ M := by
    rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    exact ⟨conv a b, conv_mem hA.comul ha hb, pairWith_conv hc a b⟩
  let S : Subalgebra R K := M.toSubalgebra hone (fun x y hx hy => hmul x hx y hy)
  exact IsIntegral.of_mem_of_fg S (by simpa [S] using hfg.map _) _ ⟨l, hl, rfl⟩

end GlobalTheory.CompanionTheory.Ar.BT.CharExt

open GlobalTheory.CompanionTheory.Ar.BT.CharExt in

/- English proof (translation)
Introduce `R _ _ T _ _ _ A hA χ`. Consider the cases of `nonempty_fintype T`. Set `K` to `FractionRing R`. Establish `hinj` using `IsFractionRing.injective R K`. Use `haveI : FaithfulSMul R K := (faithfulSMul_iff_algebraMap_injective R K).2 hinj`.

Take `⟨d, hd0, hd⟩` from `hA.full`. Use `haveI := hA.finite`. Use `haveI := hA.projective`. Take `⟨n, p, g, hp, hg, hpg⟩` from `Module.Finite.exists_comp_eq_id_of_projective R A`. Use `set c : T → R := fun t => ((χ t : Rˣ) : R) with hcdef`.

Set `cK : T → K` to `fun t => algebraMap R K (c t)`. Establish `hmul : ∀ x y, cK (x * y) = cK x * cK y`. Introduce `x y`. Simplify using `[cK, c]`. Establish `h1 : cK 1 = 1` using `by simp [cK, c]`.

Set `x : A` to `⟨d • c, hd c⟩`. Establish `hr : ∀ i : Fin n, ∃ r : R, g x i = d * r`. Introduce `i`. Set `li : Module.Dual R A` to `(LinearMap.proj i).comp g`. Establish `hl : psi (K` using `K) d hd li ∈ dualOrder K A := by`.

Rewrite using `[← range_psi hd0 hd]`. Conclude with `⟨li, rfl⟩`. Take `⟨r, hr⟩` from `IsIntegrallyClosed.isIntegral_iff.1 (isIntegral_pairWith hA hmul h1 hl)`. Use `⟨r, hinj ?_⟩` and prove the remaining obligations. Use `psi_pair (K := K) hd0 hd li (d • c) (hd c)` as an intermediate fact.

Express the relevant statement in the definitionally equal form `_ = algebraMap R K (li x) at this`. Express the relevant statement in the definitionally equal form `algebraMap R K (li x) = _`. Rewrite using `[← this, map_mul, hr]`. Simplify using `only [pairWith, LinearMap.coe_mk, AddHom.coe_mk]`. Rewrite using `[Finset.mul_sum]`.

Apply `Finset.sum_congr rfl` to reduce the goal to its premises. Introduce `t _`. Simplify using `only [Pi.smul_apply, smul_eq_mul, map_mul, cK]`. Expand and normalize the polynomial expressions, which then agree. Use `choose r hr using hr`.

Establish `hx : p (g x) = x`. Use `LinearMap.congr_fun hpg x` as an intermediate fact. Simplify using `using this`. Rewrite `hx` using `[LinearMap.pi_apply_eq_sum_univ p (g x)]`. Simplify using `only [hr, mul_smul, ← Finset.smul_sum] at hx`.

Establish `hc : c = ((∑ i, r i • p (fun j => if i = j then 1 else 0) : A) : T → R)`. Use function extensionality and compare the values at `t`. Establish `e` using `congrArg (fun a : A => (a : T → R) t) hx`. Apply `mul_left_cancel₀ hd0` to reduce the goal to its premises. Conclude with `e.symm`.

Rewrite using `[hc]`. Conclude with `Subtype.property _`.
-/
theorem GlobalTheory.CompanionTheory.Ar.BT.char_mem_hopfOrder : ∀ (R : Type) [CommRing R] [IsDomain R] (T : Type) [CommGroup T] [Finite T]
    [IsIntegrallyClosed R] (A : Subalgebra R (T → R)), IsHopfOrder A →
    ∀ χ : T →* Rˣ, (fun t => ((χ t : Rˣ) : R)) ∈ A := by
  intro R _ _ T _ _ _ A hA χ
  classical
  cases nonempty_fintype T
  let K := FractionRing R
  have hinj := IsFractionRing.injective R K
  haveI : FaithfulSMul R K := (faithfulSMul_iff_algebraMap_injective R K).2 hinj
  obtain ⟨d, hd0, hd⟩ := hA.full
  haveI := hA.finite
  haveI := hA.projective
  obtain ⟨n, p, g, hp, hg, hpg⟩ := Module.Finite.exists_comp_eq_id_of_projective R A
  set c : T → R := fun t => ((χ t : Rˣ) : R) with hcdef
  let cK : T → K := fun t => algebraMap R K (c t)
  have hmul : ∀ x y, cK (x * y) = cK x * cK y := by
    intro x y; simp [cK, c]
  have h1 : cK 1 = 1 := by simp [cK, c]
  let x : A := ⟨d • c, hd c⟩
  have hr : ∀ i : Fin n, ∃ r : R, g x i = d * r := by
    intro i
    let li : Module.Dual R A := (LinearMap.proj i).comp g
    have hl : psi (K := K) d hd li ∈ dualOrder K A := by
      rw [← range_psi hd0 hd]; exact ⟨li, rfl⟩
    obtain ⟨r, hr⟩ := IsIntegrallyClosed.isIntegral_iff.1 (isIntegral_pairWith hA hmul h1 hl)
    refine ⟨r, hinj ?_⟩
    have := psi_pair (K := K) hd0 hd li (d • c) (hd c)
    change _ = algebraMap R K (li x) at this
    change algebraMap R K (li x) = _
    rw [← this, map_mul, hr]
    simp only [pairWith, LinearMap.coe_mk, AddHom.coe_mk]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro t _
    simp only [Pi.smul_apply, smul_eq_mul, map_mul, cK]
    ring
  choose r hr using hr
  have hx : p (g x) = x := by
    have := LinearMap.congr_fun hpg x
    simpa using this
  rw [LinearMap.pi_apply_eq_sum_univ p (g x)] at hx
  simp only [hr, mul_smul, ← Finset.smul_sum] at hx
  have hc : c = ((∑ i, r i • p (fun j => if i = j then 1 else 0) : A) : T → R) := by
    funext t
    have e := congrArg (fun a : A => (a : T → R) t) hx
    apply mul_left_cancel₀ hd0
    exact e.symm
  rw [hc]
  exact Subtype.property _

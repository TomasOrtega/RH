import Mathlib
import Development.DiscreteGroups.GlobalIrreducibility.LConvCut

open Module

set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedVariables false
set_option linter.style.longLine false

namespace DiscreteGroups.sglob.LConv.Comm

section Gen
variable {K M N N' : Type*} [Field K] [AddCommGroup M] [Module K M] [FiniteDimensional K M]
  [AddCommGroup N] [Module K N] [AddCommGroup N'] [Module K N']

/- English proof (translation)
Establish `h1` using `LinearMap.finrank_range_add_finrank_ker (f.domRestrict P)`. Establish `h2 : LinearMap.range (f.domRestrict P) = P.map f`. Apply `Submodule.ext` to reduce the goal to its premises. Introduce `y`. Prove the components needed by the constructor for the conclusion.

Introduce `hy`. Take `⟨z, rfl⟩` from `LinearMap.mem_range.1 hy`. Conclude with `Submodule.mem_map.2 ⟨z, z.2, rfl⟩`. Introduce `hy`. Take `⟨z, hz, rfl⟩` from `Submodule.mem_map.1 hy`.

Conclude with `LinearMap.mem_range.2 ⟨⟨z, hz⟩, rfl⟩`. Establish `h3 : finrank K (LinearMap.ker (f.domRestrict P)) = finrank K (P ⊓ LinearMap.ker f : Submodule K M)`. Establish `e` using `Submodule.equivMapOfInjective P.subtype (by intro u w h; exact Subtype.ext h) (LinearMap.ker (f.domRestrict P))`. Rewrite using `[e.finrank_eq]`. Establish `heq : Submodule.map P.subtype (LinearMap.ker (f.domRestrict P)) = (P ⊓ LinearMap.ker f : Submodule K M)`.

Apply `Submodule.ext` to reduce the goal to its premises. Introduce `x`. Prove the components needed by the constructor for the conclusion. Introduce `hx'`. Take `⟨y, hy, rfl⟩` from `Submodule.mem_map.1 hx'`.

Conclude with `Submodule.mem_inf.2 ⟨y.2, LinearMap.mem_ker.2 (by simpa using LinearMap.mem_ker.1 hy)⟩`. Introduce `hx`. Take `⟨hx1, hx2⟩` from `Submodule.mem_inf.1 hx`. Conclude with `Submodule.mem_map.2 ⟨⟨x, hx1⟩, LinearMap.mem_ker.2 (by simpa using LinearMap.mem_ker.1 hx2), rfl⟩`. Rewrite using `[heq]`.

Rewrite using `[← h2, ← h3]`. Conclude with `h1`.
-/
theorem finrank_map_add_inf_ker (P : Submodule K M) (f : M →ₗ[K] N) :
    finrank K (P.map f) + finrank K (P ⊓ LinearMap.ker f : Submodule K M) = finrank K P := by
  have h1 := LinearMap.finrank_range_add_finrank_ker (f.domRestrict P)
  have h2 : LinearMap.range (f.domRestrict P) = P.map f := by
    apply Submodule.ext; intro y
    constructor
    · intro hy
      obtain ⟨z, rfl⟩ := LinearMap.mem_range.1 hy
      exact Submodule.mem_map.2 ⟨z, z.2, rfl⟩
    · intro hy
      obtain ⟨z, hz, rfl⟩ := Submodule.mem_map.1 hy
      exact LinearMap.mem_range.2 ⟨⟨z, hz⟩, rfl⟩
  have h3 : finrank K (LinearMap.ker (f.domRestrict P)) =
      finrank K (P ⊓ LinearMap.ker f : Submodule K M) := by
    have e := Submodule.equivMapOfInjective P.subtype (by intro u w h; exact Subtype.ext h)
      (LinearMap.ker (f.domRestrict P))
    rw [e.finrank_eq]
    have heq : Submodule.map P.subtype (LinearMap.ker (f.domRestrict P)) =
        (P ⊓ LinearMap.ker f : Submodule K M) := by
      apply Submodule.ext; intro x
      constructor
      · intro hx'
        obtain ⟨y, hy, rfl⟩ := Submodule.mem_map.1 hx'
        exact Submodule.mem_inf.2 ⟨y.2, LinearMap.mem_ker.2 (by simpa using LinearMap.mem_ker.1 hy)⟩
      · intro hx
        obtain ⟨hx1, hx2⟩ := Submodule.mem_inf.1 hx
        exact Submodule.mem_map.2
          ⟨⟨x, hx1⟩, LinearMap.mem_ker.2 (by simpa using LinearMap.mem_ker.1 hx2), rfl⟩
    rw [heq]
  rw [← h2, ← h3]; exact h1

/- English proof (translation)
Establish `hf` using `finrank_map_add_inf_ker P f`. Establish `hg` using `finrank_map_add_inf_ker P g`. Establish `: finrank K (P ⊓ LinearMap.ker g : Submodule K M) ≤ finrank K (P ⊓ LinearMap.ker f : Submodule K M)`. Apply `Submodule.finrank_mono` to reduce the goal to its premises. Introduce `x hx`.

Take `⟨hx1, hx2⟩` from `Submodule.mem_inf.1 hx`. Conclude with `Submodule.mem_inf.2 ⟨hx1, LinearMap.mem_ker.2 (h x hx1 (LinearMap.mem_ker.1 hx2))⟩`. Use linear arithmetic over natural numbers and integers.
-/
theorem finrank_map_le_of_ker (P : Submodule K M) (f : M →ₗ[K] N) (g : M →ₗ[K] N')
    (h : ∀ x ∈ P, g x = 0 → f x = 0) : finrank K (P.map f) ≤ finrank K (P.map g) := by
  have hf := finrank_map_add_inf_ker P f
  have hg := finrank_map_add_inf_ker P g
  have : finrank K (P ⊓ LinearMap.ker g : Submodule K M) ≤
      finrank K (P ⊓ LinearMap.ker f : Submodule K M) := by
    apply Submodule.finrank_mono
    intro x hx
    obtain ⟨hx1, hx2⟩ := Submodule.mem_inf.1 hx
    exact Submodule.mem_inf.2 ⟨hx1, LinearMap.mem_ker.2 (h x hx1 (LinearMap.mem_ker.1 hx2))⟩
  omega

/- English proof (translation)
Establish `hf` using `finrank_map_add_inf_ker P f`. Establish `hQ` using `finrank_map_add_inf_ker (P ⊓ LinearMap.ker f) g`. Establish `h0 : (P ⊓ LinearMap.ker f) ⊓ LinearMap.ker g = ⊥`. Rewrite using `[eq_bot_iff]`. Introduce `x hx`.

Take `⟨hx1, hx2⟩` from `Submodule.mem_inf.1 hx`. Take `⟨hx3, hx4⟩` from `Submodule.mem_inf.1 hx1`. Conclude with `(Submodule.mem_bot K).2 (h x hx3 (LinearMap.mem_ker.1 hx4) (LinearMap.mem_ker.1 hx2))`. Rewrite `hQ` using `[h0]`. Simplify using `only [finrank_bot, add_zero] at hQ`.

Establish `: finrank K ((P ⊓ LinearMap.ker f).map g) ≤ finrank K (P.map g)` using `Submodule.finrank_mono (Submodule.map_mono inf_le_left)`. Use linear arithmetic over natural numbers and integers.
-/
theorem finrank_le_add_of_ker (P : Submodule K M) (f : M →ₗ[K] N) (g : M →ₗ[K] N')
    (h : ∀ x ∈ P, f x = 0 → g x = 0 → x = 0) :
    finrank K P ≤ finrank K (P.map f) + finrank K (P.map g) := by
  have hf := finrank_map_add_inf_ker P f
  have hQ := finrank_map_add_inf_ker (P ⊓ LinearMap.ker f) g
  have h0 : (P ⊓ LinearMap.ker f) ⊓ LinearMap.ker g = ⊥ := by
    rw [eq_bot_iff]; intro x hx
    obtain ⟨hx1, hx2⟩ := Submodule.mem_inf.1 hx
    obtain ⟨hx3, hx4⟩ := Submodule.mem_inf.1 hx1
    exact (Submodule.mem_bot K).2 (h x hx3 (LinearMap.mem_ker.1 hx4) (LinearMap.mem_ker.1 hx2))
  rw [h0] at hQ
  simp only [finrank_bot, add_zero] at hQ
  have : finrank K ((P ⊓ LinearMap.ker f).map g) ≤ finrank K (P.map g) :=
    Submodule.finrank_mono (Submodule.map_mono inf_le_left)
  omega

/- English proof (translation)
Establish `hf` using `finrank_map_add_inf_ker P f`. Establish `h0 : P ⊓ LinearMap.ker f = ⊥`. Rewrite using `[eq_bot_iff]`. Introduce `x hx`. Take `⟨hx1, hx2⟩` from `Submodule.mem_inf.1 hx`.

Conclude with `(Submodule.mem_bot K).2 (h x hx1 (LinearMap.mem_ker.1 hx2))`. Rewrite `hf` using `[h0]`. Simplify using `only [finrank_bot, add_zero] at hf`. Use `Submodule.finrank_le (P.map f)` as an intermediate fact. Use linear arithmetic over natural numbers and integers.
-/
theorem injective_bound (P : Submodule K M) (f : M →ₗ[K] N) [FiniteDimensional K N]
    (h : ∀ x ∈ P, f x = 0 → x = 0) : finrank K P ≤ finrank K N := by
  have hf := finrank_map_add_inf_ker P f
  have h0 : P ⊓ LinearMap.ker f = ⊥ := by
    rw [eq_bot_iff]; intro x hx
    obtain ⟨hx1, hx2⟩ := Submodule.mem_inf.1 hx
    exact (Submodule.mem_bot K).2 (h x hx1 (LinearMap.mem_ker.1 hx2))
  rw [h0] at hf
  simp only [finrank_bot, add_zero] at hf
  have := Submodule.finrank_le (P.map f)
  omega

end Gen

section Res
variable {V : Type*} [AddCommGroup V] [Module ℂ V]

def pre (W : Submodule ℂ V) : Module.End ℂ V →ₗ[ℂ] (W →ₗ[ℂ] V) where
  toFun x := x ∘ₗ W.subtype
  map_add' x y := by ext; simp
  map_smul' c x := by ext; simp

def post (W : Submodule ℂ V) : Module.End ℂ W →ₗ[ℂ] (W →ₗ[ℂ] V) where
  toFun y := W.subtype ∘ₗ y
  map_add' x y := by ext; simp
  map_smul' c x := by ext; simp

def rs (W : Submodule ℂ V) (x : Module.End ℂ V) (h : ∀ v ∈ W, x v ∈ W) : Module.End ℂ W :=
  LinearMap.codRestrict W (x.domRestrict W) (fun v => h v v.2)

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem rs_coe (W : Submodule ℂ V) (x : Module.End ℂ V) (h : ∀ v ∈ W, x v ∈ W) (v : W) :
    ((rs W x h v : W) : V) = x v := rfl

/- English proof (translation)
Apply `LinearMap.ext` to reduce the goal to its premises. Introduce `v`. Apply `Subtype.ext` to reduce the goal to its premises. Use `show a i (a j (v : V)) = a j (a i (v : V))`. Conclude with `LinearMap.congr_fun (ha i j) v`.
-/
theorem rs_comm (W : Submodule ℂ V) {ι : Type*} (a : ι → Module.End ℂ V)
    (ha : ∀ i j, a i * a j = a j * a i) (h : ∀ i, ∀ v ∈ W, a i v ∈ W) (i j : ι) :
    rs W (a i) (h i) * rs W (a j) (h j) = rs W (a j) (h j) * rs W (a i) (h i) := by
  apply LinearMap.ext; intro v; apply Subtype.ext
  show a i (a j (v : V)) = a j (a i (v : V))
  exact LinearMap.congr_fun (ha i j) v

/- English proof (translation)
Proceed by induction on `hx using Algebra.adjoin_induction with`. Consider the case `mem x hx => obtain ⟨j, rfl⟩ := hx`. Conclude with `hy j`. Consider the case `algebraMap r => exact Algebra.commutes r y`. Consider the case `add x z _ _ hx hz => rw [add_mul, mul_add, hx, hz]`.

Consider the case `mul x z _ _ hx hz => rw [mul_assoc, hz, ← mul_assoc, hx, mul_assoc]`.
-/
theorem comm_of_mem {ι : Type*} (a : ι → Module.End ℂ V) (y : Module.End ℂ V)
    (hy : ∀ i, a i * y = y * a i) {x : Module.End ℂ V} (hx : x ∈ Algebra.adjoin ℂ (Set.range a)) :
    x * y = y * x := by
  induction hx using Algebra.adjoin_induction with
  | mem x hx => obtain ⟨j, rfl⟩ := hx; exact hy j
  | algebraMap r => exact Algebra.commutes r y
  | add x z _ _ hx hz => rw [add_mul, mul_add, hx, hz]
  | mul x z _ _ hx hz => rw [mul_assoc, hz, ← mul_assoc, hx, mul_assoc]

/- English proof (translation)
Proceed by induction on `hx using Algebra.adjoin_induction with`. Consider the case `mem x hx`. Take `⟨i, rfl⟩` from `hx`. Conclude with `⟨rs W (a i) (h i), Algebra.subset_adjoin (Set.mem_range_self i), LinearMap.ext fun v => rfl⟩`. Consider the case `algebraMap r`.

Use `⟨algebraMap ℂ _ r, Subalgebra.algebraMap_mem _ r, LinearMap.ext fun v => ?_⟩` and prove the remaining obligations. Use `first`. Consider the case `rfl`. Consider the case `simp [pre, post]`. Consider the case `simp [pre, post, Module.algebraMap_end_apply]`.

Consider the case `add x z _ _ hx hz`. Take `⟨y1, h1, e1⟩` from `hx`. Take `⟨y2, h2, e2⟩` from `hz`. Conclude with `⟨y1 + y2, add_mem h1 h2, by rw [map_add, map_add, e1, e2]⟩`. Consider the case `mul x z _ _ hx hz`.

Take `⟨y1, h1, e1⟩` from `hx`. Take `⟨y2, h2, e2⟩` from `hz`. Use `⟨y1 * y2, mul_mem h1 h2, LinearMap.ext fun v => ?_⟩` and prove the remaining obligations. Establish `e1'` using `LinearMap.congr_fun e1 (y2 v)`. Establish `e2'` using `LinearMap.congr_fun e2 v`.

Express the relevant statement in the definitionally equal form `((y1 (y2 v) : W) : V) = x (z (v : V))`. Express the relevant statement in the definitionally equal form `((y1 (y2 v) : W) : V) = x ((y2 v : W) : V) at e1'`. Express the relevant statement in the definitionally equal form `((y2 v : W) : V) = z (v : V) at e2'`. Rewrite using `[e1', e2']`.
-/
theorem exists_post (W : Submodule ℂ V) {ι : Type*} (a : ι → Module.End ℂ V)
    (h : ∀ i, ∀ v ∈ W, a i v ∈ W) {x : Module.End ℂ V}
    (hx : x ∈ Algebra.adjoin ℂ (Set.range a)) :
    ∃ y ∈ Algebra.adjoin ℂ (Set.range (fun i => rs W (a i) (h i))), post W y = pre W x := by
  induction hx using Algebra.adjoin_induction with
  | mem x hx =>
    obtain ⟨i, rfl⟩ := hx
    exact ⟨rs W (a i) (h i), Algebra.subset_adjoin (Set.mem_range_self i), LinearMap.ext fun v => rfl⟩
  | algebraMap r =>
    refine ⟨algebraMap ℂ _ r, Subalgebra.algebraMap_mem _ r, LinearMap.ext fun v => ?_⟩
    first
    | rfl
    | simp [pre, post]
    | simp [pre, post, Module.algebraMap_end_apply]
  | add x z _ _ hx hz =>
    obtain ⟨y1, h1, e1⟩ := hx
    obtain ⟨y2, h2, e2⟩ := hz
    exact ⟨y1 + y2, add_mem h1 h2, by rw [map_add, map_add, e1, e2]⟩
  | mul x z _ _ hx hz =>
    obtain ⟨y1, h1, e1⟩ := hx
    obtain ⟨y2, h2, e2⟩ := hz
    refine ⟨y1 * y2, mul_mem h1 h2, LinearMap.ext fun v => ?_⟩
    have e1' := LinearMap.congr_fun e1 (y2 v)
    have e2' := LinearMap.congr_fun e2 v
    change ((y1 (y2 v) : W) : V) = x (z (v : V))
    change ((y1 (y2 v) : W) : V) = x ((y2 v : W) : V) at e1'
    change ((y2 v : W) : V) = z (v : V) at e2'
    rw [e1', e2']

/- English proof (translation)
Use `first`. Consider the case `exact Subalgebra.finrank_toSubmodule S`. Consider the case `rfl`.
-/
theorem sub_finrank (S : Subalgebra ℂ (Module.End ℂ V)) [FiniteDimensional ℂ V] :
    finrank ℂ (Subalgebra.toSubmodule S) = finrank ℂ S := by
  first
  | exact Subalgebra.finrank_toSubmodule S
  | rfl

/- English proof (translation)
Rewrite using `[← sub_finrank]`. Combine the equalities or inequalities in the displayed calculation. Apply `Submodule.finrank_mono` to reduce the goal to its premises. Introduce `u hu`. Take `⟨x, hx, rfl⟩` from `Submodule.mem_map.1 hu`.

Take `⟨y, hy, e⟩` from `exists_post W a h hx`. Conclude with `Submodule.mem_map.2 ⟨y, hy, e⟩`. Use `_ ≤ _ := Submodule.finrank_map_le _ _`.
-/
theorem finrank_map_pre_le [FiniteDimensional ℂ V] (W : Submodule ℂ V) {ι : Type*}
    (a : ι → Module.End ℂ V) (h : ∀ i, ∀ v ∈ W, a i v ∈ W) :
    finrank ℂ ((Subalgebra.toSubmodule (Algebra.adjoin ℂ (Set.range a))).map (pre W)) ≤
      finrank ℂ (Algebra.adjoin ℂ (Set.range (fun i => rs W (a i) (h i)))) := by
  rw [← sub_finrank]
  calc _ ≤ finrank ℂ ((Subalgebra.toSubmodule
          (Algebra.adjoin ℂ (Set.range (fun i => rs W (a i) (h i))))).map (post W)) := by
        apply Submodule.finrank_mono
        intro u hu
        obtain ⟨x, hx, rfl⟩ := Submodule.mem_map.1 hu
        obtain ⟨y, hy, e⟩ := exists_post W a h hx
        exact Submodule.mem_map.2 ⟨y, hy, e⟩
    _ ≤ _ := Submodule.finrank_map_le _ _

/- English proof (translation)
Use `first`. Consider the case `exact Module.finrank_linearMap ℂ ℂ W V`. Consider the case `exact Module.finrank_linearMap ℂ W V`. Consider the case `simp [Module.finrank_linearMap]`.
-/
theorem finrank_hom [FiniteDimensional ℂ V] (W : Submodule ℂ V) :
    finrank ℂ (W →ₗ[ℂ] V) = finrank ℂ W * finrank ℂ V := by
  first
  | exact Module.finrank_linearMap ℂ ℂ W V
  | exact Module.finrank_linearMap ℂ W V
  | simp [Module.finrank_linearMap]

/- English proof (translation)
Use `first`. Consider the case `exact Module.finrank_linearMap ℂ ℂ V V`. Consider the case `exact Module.finrank_linearMap ℂ V V`. Consider the case `simp [Module.finrank_linearMap]`.
-/
theorem finrank_end [FiniteDimensional ℂ V] :
    finrank ℂ (Module.End ℂ V) = finrank ℂ V * finrank ℂ V := by
  first
  | exact Module.finrank_linearMap ℂ ℂ V V
  | exact Module.finrank_linearMap ℂ V V
  | simp [Module.finrank_linearMap]

/- English proof (translation)
Rewrite using `[← sub_finrank, ← finrank_end]`. Conclude with `Submodule.finrank_le _`.
-/
theorem finrank_sub_le_sq [FiniteDimensional ℂ V] (S : Subalgebra ℂ (Module.End ℂ V)) :
    finrank ℂ S ≤ finrank ℂ V * finrank ℂ V := by
  rw [← sub_finrank, ← finrank_end]
  exact Submodule.finrank_le _

/- English proof (translation)
Establish `key : ∀ k : ℕ, U ⊔ LinearMap.range (c ^ k) = ⊤`. Introduce `k`. Proceed by induction on `k with`. Consider the case `zero`. Rewrite using `[eq_top_iff]`.

Introduce `v _`. Conclude with `Submodule.mem_sup_right (LinearMap.mem_range.2 ⟨v, by simp⟩)`. Consider the case `succ k ih`. Rewrite using `[eq_top_iff]`. Introduce `v _`.

Establish `hv : v ∈ U ⊔ LinearMap.range c` using `by rw [h]; exact Submodule.mem_top`. Take `⟨u, hu, w, hw, rfl⟩` from `Submodule.mem_sup.1 hv`. Take `⟨z, rfl⟩` from `LinearMap.mem_range.1 hw`. Establish `hz : z ∈ U ⊔ LinearMap.range (c ^ k)` using `by rw [ih]; exact Submodule.mem_top`. Take `⟨u', hu', w', hw', rfl⟩` from `Submodule.mem_sup.1 hz`.

Take `⟨z', rfl⟩` from `LinearMap.mem_range.1 hw'`. Rewrite using `[map_add, ← add_assoc]`. Apply `Submodule.add_mem_sup (U.add_mem hu (hU _ hu'))` to reduce the goal to its premises. Conclude with `LinearMap.mem_range.2 ⟨z', by rw [pow_succ']; rfl⟩`. Use `key N` as an intermediate fact.

Rewrite `this` using `[hc, LinearMap.range_zero, sup_bot_eq]`. Then use the resulting hypothesis.
-/
theorem nak_one (U : Submodule ℂ V) (c : Module.End ℂ V) (N : ℕ) (hc : c ^ N = 0)
    (hU : ∀ v ∈ U, c v ∈ U) (h : U ⊔ LinearMap.range c = ⊤) : U = ⊤ := by
  have key : ∀ k : ℕ, U ⊔ LinearMap.range (c ^ k) = ⊤ := by
    intro k
    induction k with
    | zero =>
      rw [eq_top_iff]; intro v _
      exact Submodule.mem_sup_right (LinearMap.mem_range.2 ⟨v, by simp⟩)
    | succ k ih =>
      rw [eq_top_iff]; intro v _
      have hv : v ∈ U ⊔ LinearMap.range c := by rw [h]; exact Submodule.mem_top
      obtain ⟨u, hu, w, hw, rfl⟩ := Submodule.mem_sup.1 hv
      obtain ⟨z, rfl⟩ := LinearMap.mem_range.1 hw
      have hz : z ∈ U ⊔ LinearMap.range (c ^ k) := by rw [ih]; exact Submodule.mem_top
      obtain ⟨u', hu', w', hw', rfl⟩ := Submodule.mem_sup.1 hz
      obtain ⟨z', rfl⟩ := LinearMap.mem_range.1 hw'
      rw [map_add, ← add_assoc]
      apply Submodule.add_mem_sup (U.add_mem hu (hU _ hu'))
      exact LinearMap.mem_range.2 ⟨z', by rw [pow_succ']; rfl⟩
  have := key N
  rwa [hc, LinearMap.range_zero, sup_bot_eq] at this

/- English proof (translation)
Establish `hle : (⨆ i ∈ s, LinearMap.range (b i)) ≤ (⨆ i ∈ s, LinearMap.range (b i)).comap x`. Use `iSup₂_le fun i hi => ?_` and prove the remaining obligations. Introduce `w hw`. Take `⟨z, rfl⟩` from `LinearMap.mem_range.1 hw`. Rewrite using `[Submodule.mem_comap]`.

Establish `e : x (b i z) = b i (x z)` using `LinearMap.congr_fun (hx i) z`. Rewrite using `[e]`. Conclude with `(le_iSup₂ (f := fun i (_ : i ∈ s) => LinearMap.range (b i)) i hi) (LinearMap.mem_range_self _ _)`. Introduce `v hv`. Conclude with `Submodule.mem_comap.1 (hle hv)`.
-/
theorem iSup_range_inv {ι : Type*} (s : Finset ι) (b : ι → Module.End ℂ V) (x : Module.End ℂ V)
    (hx : ∀ i, x * b i = b i * x) :
    ∀ v ∈ (⨆ i ∈ s, LinearMap.range (b i)), x v ∈ (⨆ i ∈ s, LinearMap.range (b i)) := by
  have hle : (⨆ i ∈ s, LinearMap.range (b i)) ≤ (⨆ i ∈ s, LinearMap.range (b i)).comap x := by
    refine iSup₂_le fun i hi => ?_
    intro w hw
    obtain ⟨z, rfl⟩ := LinearMap.mem_range.1 hw
    rw [Submodule.mem_comap]
    have e : x (b i z) = b i (x z) := LinearMap.congr_fun (hx i) z
    rw [e]
    exact (le_iSup₂ (f := fun i (_ : i ∈ s) => LinearMap.range (b i)) i hi)
      (LinearMap.mem_range_self _ _)
  intro v hv
  exact Submodule.mem_comap.1 (hle hv)

/- English proof (translation)
Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty => intro U _ h`. Simplify using `using h`. Consider the case `insert j s hj ih`. Introduce `U hU h`.

Rewrite `h` using `[Finset.iSup_insert]`. Apply `ih U hU` to reduce the goal to its premises. Take `⟨N, hN⟩` from `hnil j`. Apply `nak_one _ (b j) N hN` to reduce the goal to its premises. Introduce `v hv`.

Take `⟨u, hu, w, hw, rfl⟩` from `Submodule.mem_sup.1 hv`. Rewrite using `[map_add]`. Conclude with `Submodule.add_mem_sup (hU j u hu) (iSup_range_inv s b (b j) (fun i => hcomm j i) w hw)`. Rewrite using `[← h]`. Apply `le_antisymm` to reduce the goal to its premises.

Conclude with `sup_le (sup_le le_sup_left (le_sup_of_le_right le_sup_right)) (le_sup_of_le_right le_sup_left)`. Conclude with `sup_le (le_sup_of_le_left le_sup_left) (sup_le le_sup_right (le_sup_of_le_left le_sup_right))`.
-/
theorem nak {ι : Type*} [DecidableEq ι] (s : Finset ι) (b : ι → Module.End ℂ V)
    (hcomm : ∀ i j, b i * b j = b j * b i) (hnil : ∀ i, ∃ N : ℕ, b i ^ N = 0) :
    ∀ U : Submodule ℂ V, (∀ i, ∀ v ∈ U, b i v ∈ U) →
      U ⊔ (⨆ i ∈ s, LinearMap.range (b i)) = ⊤ → U = ⊤ := by
  induction s using Finset.induction_on with
  | empty => intro U _ h; simpa using h
  | insert j s hj ih =>
    intro U hU h
    rw [Finset.iSup_insert] at h
    apply ih U hU
    obtain ⟨N, hN⟩ := hnil j
    apply nak_one _ (b j) N hN
    · intro v hv
      obtain ⟨u, hu, w, hw, rfl⟩ := Submodule.mem_sup.1 hv
      rw [map_add]
      exact Submodule.add_mem_sup (hU j u hu)
        (iSup_range_inv s b (b j) (fun i => hcomm j i) w hw)
    · rw [← h]
      apply le_antisymm
      · exact sup_le (sup_le le_sup_left (le_sup_of_le_right le_sup_right))
          (le_sup_of_le_right le_sup_left)
      · exact sup_le (le_sup_of_le_left le_sup_left)
          (sup_le le_sup_right (le_sup_of_le_left le_sup_right))

end Res

def Pl (l t c : ℕ) : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (a : Fin l → Module.End ℂ V), (∀ i j, a i * a j = a j * a i) →
    t * Module.finrank ℂ (Algebra.adjoin ℂ (Set.range a)) ≤
      Module.finrank ℂ V ^ 2 + c * Module.finrank ℂ V

/- English proof (translation)
Introduce `V _ _ _ a _`. Rewrite using `[Set.range_eq_empty a, Algebra.adjoin_empty]`. Establish `hsq` using `finrank_sub_le_sq (V := V) ⊥`. Break down `Nat.eq_zero_or_pos (finrank ℂ V) with h0 | hpos` into its components or cases. Rewrite `hsq`, the goal using `[h0]`.

Establish `: finrank ℂ (⊥ : Subalgebra ℂ (Module.End ℂ V)) = 0` using `by omega`. Rewrite using `[this]`. Simplify using the standard rewrite rules. Use `haveI : Nontrivial V := Module.finrank_pos_iff.1 hpos`. Take `⟨v, hv⟩` from `exists_ne (0 : V)`.

Use `haveI : Nontrivial (Module.End ℂ V) := ⟨⟨1, 0, fun h => hv (by simpa using LinearMap.congr_fun h v)⟩⟩`. Establish `h1 : finrank ℂ (⊥ : Subalgebra ℂ (Module.End ℂ V)) ≤ 1` using `by first`. Consider the case `exact (Subalgebra.finrank_bot).le`. Consider the case `exact le_of_eq Subalgebra.finrank_bot`. Consider the case `simp`.

Establish `e1` using `Nat.mul_le_mul_left t h1`. Establish `e2` using `Nat.mul_le_mul_left t (show 1 ≤ finrank ℂ V from hpos)`. Use the polynomial consequences of the given equalities and inequalities.
-/
theorem base (t : ℕ) : Pl 0 t t := by
  intro V _ _ _ a _
  rw [Set.range_eq_empty a, Algebra.adjoin_empty]
  have hsq := finrank_sub_le_sq (V := V) ⊥
  rcases Nat.eq_zero_or_pos (finrank ℂ V) with h0 | hpos
  · rw [h0] at hsq ⊢
    have : finrank ℂ (⊥ : Subalgebra ℂ (Module.End ℂ V)) = 0 := by omega
    rw [this]; simp
  · haveI : Nontrivial V := Module.finrank_pos_iff.1 hpos
    obtain ⟨v, hv⟩ := exists_ne (0 : V)
    haveI : Nontrivial (Module.End ℂ V) :=
      ⟨⟨1, 0, fun h => hv (by simpa using LinearMap.congr_fun h v)⟩⟩
    have h1 : finrank ℂ (⊥ : Subalgebra ℂ (Module.End ℂ V)) ≤ 1 := by
      first
      | exact (Subalgebra.finrank_bot).le
      | exact le_of_eq Subalgebra.finrank_bot
      | simp
    have e1 := Nat.mul_le_mul_left t h1
    have e2 := Nat.mul_le_mul_left t (show 1 ≤ finrank ℂ V from hpos)
    nlinarith

def IHn (l t c n : ℕ) : Prop :=
  ∀ m < n, ∀ (V : Type) [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V],
    finrank ℂ V = m → ∀ (a : Fin (l + 1) → Module.End ℂ V), (∀ i j, a i * a j = a j * a i) →
    t * finrank ℂ (Algebra.adjoin ℂ (Set.range a)) ≤ m ^ 2 + c * m

/- English proof (translation)
Take `⟨i, hi⟩` from `hs`. Establish `hc` using `(hN i).1`. Establish `hfA : (a i - algebraMap ℂ (Module.End ℂ V) (μ i)) ^ N i ∈ Algebra.adjoin ℂ (Set.range a)` using `pow_mem (sub_mem (Algebra.subset_adjoin (Set.mem_range_self i)) (Subalgebra.algebraMap_mem _ _)) _`. Generalize the expression as in `hf : (a i - algebraMap ℂ (Module.End ℂ V) (μ i)) ^ N i = f at hc hi hfA`. Establish `hxa : ∀ j, f * a j = a j * f` using `fun j => comm_of_mem a (a j) (fun k => ha k j) hfA`.

Establish `hKinv : ∀ j, ∀ v ∈ LinearMap.ker f, a j v ∈ LinearMap.ker f`. Introduce `j v hv`. Rewrite `hv`, the goal using `[LinearMap.mem_ker]`. Establish `e : f (a j v) = a j (f v)` using `LinearMap.congr_fun (hxa j) v`. Rewrite using `[e, hv, map_zero]`.

Establish `hRinv : ∀ j, ∀ v ∈ LinearMap.range f, a j v ∈ LinearMap.range f`. Introduce `j v hv`. Take `⟨w, rfl⟩` from `LinearMap.mem_range.1 hv`. Establish `e : f (a j w) = a j (f w)` using `LinearMap.congr_fun (hxa j) w`. Conclude with `LinearMap.mem_range.2 ⟨a j w, e⟩`.

Establish `hKne : LinearMap.ker f ≠ ⊥`. Take `⟨v, hv⟩` from `(hμ i).exists_hasEigenvector`. Establish `hav : a i v = μ i • v` using `by first`. Consider the case `exact hv.apply_eq_smul`. Consider the case `exact Module.End.mem_eigenspace_iff.1 hv.1`.

Establish `hv0 : v ≠ 0` using `by first`. Consider the case `exact hv.2`. Consider the case `exact hv.right`. Consider the case `exact hv.ne_zero`. Establish `hbv : (a i - algebraMap ℂ (Module.End ℂ V) (μ i)) v = 0` using `by first`.

Consider the case `rw [LinearMap.sub_apply, Module.algebraMap_end_apply, hav, sub_self]`. Consider the case `simp [hav]`. Introduce `hK`. Apply `hv0` to reduce the goal to its premises. Establish `hvK : v ∈ LinearMap.ker f`.

Rewrite using `[LinearMap.mem_ker, ← hf]`. Take `⟨k, hk⟩ : ∃ k, N i = k + 1` from `⟨N i - 1, by have := (hN i).2; omega⟩`. Rewrite using `[hk, pow_succ]`. Use `show ((a i - algebraMap ℂ (Module.End ℂ V) (μ i)) ^ k) ((a i - algebraMap ℂ (Module.End ℂ V) (μ i)) v) = 0`. Rewrite using `[hbv, map_zero]`.

Rewrite `hvK` using `[hK]`. Conclude with `(Submodule.mem_bot ℂ).1 hvK`. Establish `hsum` using `Submodule.finrank_add_eq_of_isCompl hc`. Rewrite `hsum` using `[hn]`. Establish `hKpos : 0 < finrank ℂ (LinearMap.ker f)`.

Break down `Nat.eq_zero_or_pos (finrank ℂ (LinearMap.ker f)) with h | h` into its components or cases. Apply the tactic sequence `exact (hKne (by first | exact Submodule.finrank_eq_zero.1 h | exact finrank_eq_zero.1 h)).elim`. Conclude with `h`. Establish `hRpos : 0 < finrank ℂ (LinearMap.range f)`. Break down `Nat.eq_zero_or_pos (finrank ℂ (LinearMap.range f)) with h | h` into its components or cases.

Apply the tactic sequence `exact (hi (by first | exact Submodule.finrank_eq_zero.1 h | exact finrank_eq_zero.1 h)).elim`. Conclude with `h`. Establish `hK` using `IH _ (by omega) (LinearMap.ker f) rfl (fun j => rs _ (a j) (hKinv j)) (rs_comm _ a ha hKinv)`. Establish `hR` using `IH _ (by omega) (LinearMap.range f) rfl (fun j => rs _ (a j) (hRinv j)) (rs_comm _ a ha hRinv)`. Establish `h1` using `finrank_le_add_of_ker (Subalgebra.toSubmodule (Algebra.adjoin ℂ (Set.range a))) (pre (LinearMap.ker f)) (pre (LinearMap.range f)) (by`.

Introduce `x _ hx1 hx2`. Apply `LinearMap.ext` to reduce the goal to its premises. Introduce `v`. Establish `hv : v ∈ LinearMap.ker f ⊔ LinearMap.range f`. Rewrite using `[hc.sup_eq_top]`.

Conclude with `Submodule.mem_top`. Take `⟨k, hk, r, hr, rfl⟩` from `Submodule.mem_sup.1 hv`. Establish `e1` using `LinearMap.congr_fun hx1 ⟨k, hk⟩`. Establish `e2` using `LinearMap.congr_fun hx2 ⟨r, hr⟩`. Express the relevant statement in the definitionally equal form `x k = 0 at e1`.

Express the relevant statement in the definitionally equal form `x r = 0 at e2`. Rewrite using `[map_add, e1, e2, add_zero, LinearMap.zero_apply])`. Establish `h2` using `finrank_map_pre_le (LinearMap.ker f) a hKinv`. Establish `h3` using `finrank_map_pre_le (LinearMap.range f) a hRinv`. Rewrite `h1` using `[sub_finrank]`.

Establish `h4` using `Nat.mul_le_mul_left t (le_trans h1 (Nat.add_le_add h2 h3))`. Rewrite using `[← hsum]`. Use polynomial arithmetic with `[Nat.zero_le (finrank ℂ (LinearMap.ker f) * finrank ℂ (LinearMap.range f))]`.
-/
theorem split_case (l t c n : ℕ) (IH : IHn l t c n) (V : Type) [AddCommGroup V] [Module ℂ V]
    [FiniteDimensional ℂ V] (hn : finrank ℂ V = n) (a : Fin (l + 1) → Module.End ℂ V)
    (ha : ∀ i j, a i * a j = a j * a i) (μ : Fin (l + 1) → ℂ)
    (hμ : ∀ i, Module.End.HasEigenvalue (a i) (μ i)) (N : Fin (l + 1) → ℕ)
    (hN : ∀ i, IsCompl (LinearMap.ker ((a i - algebraMap ℂ (Module.End ℂ V) (μ i)) ^ N i))
      (LinearMap.range ((a i - algebraMap ℂ (Module.End ℂ V) (μ i)) ^ N i)) ∧ 1 ≤ N i)
    (hs : ∃ i, LinearMap.range ((a i - algebraMap ℂ (Module.End ℂ V) (μ i)) ^ N i) ≠ ⊥) :
    t * finrank ℂ (Algebra.adjoin ℂ (Set.range a)) ≤ n ^ 2 + c * n := by
  obtain ⟨i, hi⟩ := hs
  have hc := (hN i).1
  have hfA : (a i - algebraMap ℂ (Module.End ℂ V) (μ i)) ^ N i ∈ Algebra.adjoin ℂ (Set.range a) :=
    pow_mem (sub_mem (Algebra.subset_adjoin (Set.mem_range_self i)) (Subalgebra.algebraMap_mem _ _)) _
  generalize hf : (a i - algebraMap ℂ (Module.End ℂ V) (μ i)) ^ N i = f at hc hi hfA
  have hxa : ∀ j, f * a j = a j * f := fun j => comm_of_mem a (a j) (fun k => ha k j) hfA
  have hKinv : ∀ j, ∀ v ∈ LinearMap.ker f, a j v ∈ LinearMap.ker f := by
    intro j v hv
    rw [LinearMap.mem_ker] at hv ⊢
    have e : f (a j v) = a j (f v) := LinearMap.congr_fun (hxa j) v
    rw [e, hv, map_zero]
  have hRinv : ∀ j, ∀ v ∈ LinearMap.range f, a j v ∈ LinearMap.range f := by
    intro j v hv
    obtain ⟨w, rfl⟩ := LinearMap.mem_range.1 hv
    have e : f (a j w) = a j (f w) := LinearMap.congr_fun (hxa j) w
    exact LinearMap.mem_range.2 ⟨a j w, e⟩
  have hKne : LinearMap.ker f ≠ ⊥ := by
    obtain ⟨v, hv⟩ := (hμ i).exists_hasEigenvector
    have hav : a i v = μ i • v := by
      first
      | exact hv.apply_eq_smul
      | exact Module.End.mem_eigenspace_iff.1 hv.1
    have hv0 : v ≠ 0 := by
      first
      | exact hv.2
      | exact hv.right
      | exact hv.ne_zero
    have hbv : (a i - algebraMap ℂ (Module.End ℂ V) (μ i)) v = 0 := by
      first
      | rw [LinearMap.sub_apply, Module.algebraMap_end_apply, hav, sub_self]
      | simp [hav]
    intro hK
    apply hv0
    have hvK : v ∈ LinearMap.ker f := by
      rw [LinearMap.mem_ker, ← hf]
      obtain ⟨k, hk⟩ : ∃ k, N i = k + 1 := ⟨N i - 1, by have := (hN i).2; omega⟩
      rw [hk, pow_succ]
      show ((a i - algebraMap ℂ (Module.End ℂ V) (μ i)) ^ k)
        ((a i - algebraMap ℂ (Module.End ℂ V) (μ i)) v) = 0
      rw [hbv, map_zero]
    rw [hK] at hvK
    exact (Submodule.mem_bot ℂ).1 hvK
  have hsum := Submodule.finrank_add_eq_of_isCompl hc
  rw [hn] at hsum
  have hKpos : 0 < finrank ℂ (LinearMap.ker f) := by
    rcases Nat.eq_zero_or_pos (finrank ℂ (LinearMap.ker f)) with h | h
    · exact (hKne (by first | exact Submodule.finrank_eq_zero.1 h | exact finrank_eq_zero.1 h)).elim
    · exact h
  have hRpos : 0 < finrank ℂ (LinearMap.range f) := by
    rcases Nat.eq_zero_or_pos (finrank ℂ (LinearMap.range f)) with h | h
    · exact (hi (by first | exact Submodule.finrank_eq_zero.1 h | exact finrank_eq_zero.1 h)).elim
    · exact h
  have hK := IH _ (by omega) (LinearMap.ker f) rfl (fun j => rs _ (a j) (hKinv j))
    (rs_comm _ a ha hKinv)
  have hR := IH _ (by omega) (LinearMap.range f) rfl (fun j => rs _ (a j) (hRinv j))
    (rs_comm _ a ha hRinv)
  have h1 := finrank_le_add_of_ker (Subalgebra.toSubmodule (Algebra.adjoin ℂ (Set.range a)))
    (pre (LinearMap.ker f)) (pre (LinearMap.range f)) (by
      intro x _ hx1 hx2
      apply LinearMap.ext; intro v
      have hv : v ∈ LinearMap.ker f ⊔ LinearMap.range f := by
        rw [hc.sup_eq_top]; exact Submodule.mem_top
      obtain ⟨k, hk, r, hr, rfl⟩ := Submodule.mem_sup.1 hv
      have e1 := LinearMap.congr_fun hx1 ⟨k, hk⟩
      have e2 := LinearMap.congr_fun hx2 ⟨r, hr⟩
      change x k = 0 at e1
      change x r = 0 at e2
      rw [map_add, e1, e2, add_zero, LinearMap.zero_apply])
  have h2 := finrank_map_pre_le (LinearMap.ker f) a hKinv
  have h3 := finrank_map_pre_le (LinearMap.range f) a hRinv
  rw [sub_finrank] at h1
  have h4 := Nat.mul_le_mul_left t (le_trans h1 (Nat.add_le_add h2 h3))
  rw [← hsum]
  nlinarith [Nat.zero_le (finrank ℂ (LinearMap.ker f) * finrank ℂ (LinearMap.range f))]

/- English proof (translation)
Proceed by induction on `hx using Algebra.adjoin_induction with`. Consider the case `mem x hx`. Take `⟨i, rfl⟩` from `hx`. Break down `Fin.eq_zero_or_eq_succ i with rfl | ⟨j, rfl⟩` into its components or cases. Conclude with `⟨algebraMap ℂ _ μ0, Subalgebra.algebraMap_mem _ _, 1, one_mem _, by rw [hb0, mul_one]; abel⟩`.

Conclude with `⟨a j.succ, Algebra.subset_adjoin (Set.mem_range_self j), 0, zero_mem _, by rw [mul_zero, add_zero]⟩`. Consider the case `algebraMap r`. Conclude with `⟨algebraMap ℂ _ r, Subalgebra.algebraMap_mem _ _, 0, zero_mem _, by rw [mul_zero, add_zero]⟩`. Consider the case `add x1 x2 _ _ h1 h2`. Take `⟨y1, hy1, z1, hz1, rfl⟩` from `h1`.

Take `⟨y2, hy2, z2, hz2, rfl⟩` from `h2`. Conclude with `⟨y1 + y2, add_mem hy1 hy2, z1 + z2, add_mem hz1 hz2, by rw [mul_add]; abel⟩`. Consider the case `mul x1 x2 _ _ h1 h2`. Take `⟨y1, hy1, z1, hz1, rfl⟩` from `h1`. Take `⟨y2, hy2, z2, hz2, rfl⟩` from `h2`.

Establish `hc1 : y1 * b0 = b0 * y1` using `hxb y1 (hle hy1)`. Establish `e : y1 * (b0 * z2) = b0 * (y1 * z2)` using `by rw [← mul_assoc, hc1, mul_assoc]`. Use `⟨y1 * y2, mul_mem hy1 hy2, z1 * y2 + y1 * z2 + z1 * (b0 * z2), add_mem (add_mem (mul_mem hz1 (hle hy2)) (mul_mem (hle hy1) hz2)) (mul_mem hz1 (mul_mem hb0mem hz2)), ?_⟩` and prove the remaining obligations. Simplify using `only [add_mul, mul_add, mul_assoc]`. Rewrite using `[e]`.

Normalize the expressions using the abelian group laws.
-/
theorem decomp (l : ℕ) {V : Type} [AddCommGroup V] [Module ℂ V] (a : Fin (l + 1) → Module.End ℂ V)
    (b0 : Module.End ℂ V) (μ0 : ℂ) (hb0 : b0 = a 0 - algebraMap ℂ (Module.End ℂ V) μ0)
    (hxb : ∀ x ∈ Algebra.adjoin ℂ (Set.range a), x * b0 = b0 * x)
    (hb0mem : b0 ∈ Algebra.adjoin ℂ (Set.range a))
    (hle : Algebra.adjoin ℂ (Set.range fun j : Fin l => a j.succ) ≤ Algebra.adjoin ℂ (Set.range a))
    {x : Module.End ℂ V} (hx : x ∈ Algebra.adjoin ℂ (Set.range a)) :
    ∃ y ∈ Algebra.adjoin ℂ (Set.range fun j : Fin l => a j.succ),
      ∃ z ∈ Algebra.adjoin ℂ (Set.range a), x = y + b0 * z := by
  induction hx using Algebra.adjoin_induction with
  | mem x hx =>
    obtain ⟨i, rfl⟩ := hx
    rcases Fin.eq_zero_or_eq_succ i with rfl | ⟨j, rfl⟩
    · exact ⟨algebraMap ℂ _ μ0, Subalgebra.algebraMap_mem _ _, 1, one_mem _,
        by rw [hb0, mul_one]; abel⟩
    · exact ⟨a j.succ, Algebra.subset_adjoin (Set.mem_range_self j), 0, zero_mem _, by rw [mul_zero, add_zero]⟩
  | algebraMap r =>
    exact ⟨algebraMap ℂ _ r, Subalgebra.algebraMap_mem _ _, 0, zero_mem _,
      by rw [mul_zero, add_zero]⟩
  | add x1 x2 _ _ h1 h2 =>
    obtain ⟨y1, hy1, z1, hz1, rfl⟩ := h1
    obtain ⟨y2, hy2, z2, hz2, rfl⟩ := h2
    exact ⟨y1 + y2, add_mem hy1 hy2, z1 + z2, add_mem hz1 hz2, by rw [mul_add]; abel⟩
  | mul x1 x2 _ _ h1 h2 =>
    obtain ⟨y1, hy1, z1, hz1, rfl⟩ := h1
    obtain ⟨y2, hy2, z2, hz2, rfl⟩ := h2
    have hc1 : y1 * b0 = b0 * y1 := hxb y1 (hle hy1)
    have e : y1 * (b0 * z2) = b0 * (y1 * z2) := by rw [← mul_assoc, hc1, mul_assoc]
    refine ⟨y1 * y2, mul_mem hy1 hy2, z1 * y2 + y1 * z2 + z1 * (b0 * z2),
      add_mem (add_mem (mul_mem hz1 (hle hy2)) (mul_mem (hle hy1) hz2))
        (mul_mem hz1 (mul_mem hb0mem hz2)), ?_⟩
    simp only [add_mul, mul_add, mul_assoc]
    rw [e]; abel

/- English proof (translation)
Distinguish the cases in `hcase : t * m ≤ n + c`. Combine the equalities or inequalities in the displayed calculation. Rewrite `hcase` using `[not_le]`. Establish `hm : 1 ≤ m`. Break down `Nat.eq_zero_or_pos m with h | h` into its components or cases.

Rewrite `hcase` using `[h]`. Use linear arithmetic over natural numbers and integers. Conclude with `h`. Establish `htpos : 0 < t`. Break down `Nat.eq_zero_or_pos t with h | h` into its components or cases.

Rewrite `hcase` using `[h]`. Use linear arithmetic over natural numbers and integers. Conclude with `h`. Establish `hd1` using `h1 hm`. Substitute `hdim` using the available equality.

Establish `e3` using `Nat.mul_le_mul_left (t * t) hsum2`. Establish `h5` using `Nat.mul_le_mul_left t hd1`. Establish `h3 : (n1 + m) * (n1 + m + c) ≤ (t * m) * (n1 + m + c)` using `Nat.mul_le_mul_right _ (by omega)`. Establish `h4 : (t * m) * (n1 + m + c) ≤ (t * m) * (2 * n1 + m + c)` using `Nat.mul_le_mul_left _ (by omega)`. Establish `key : t * (t * dA) ≤ t * ((n1 + m) ^ 2 + c * (n1 + m))` using `by nlinarith`.

Assume the negation of the conclusion as `hlt`. Rewrite `hlt` using `[not_le]`. Use `Nat.mul_lt_mul_of_pos_left hlt htpos` as an intermediate fact. Use linear arithmetic over natural numbers and integers.
-/
theorem arith_local (t c n m n1 dA dA' d1 : ℕ) (hdim : n1 + m = n) (hI : dA ≤ m * n)
    (hsum2 : dA ≤ dA' + d1) (hA' : t * t * dA' ≤ n ^ 2 + c * n)
    (h1 : 1 ≤ m → t * d1 ≤ n1 ^ 2 + c * n1) : t * dA ≤ n ^ 2 + c * n := by
  by_cases hcase : t * m ≤ n + c
  · calc t * dA ≤ t * (m * n) := Nat.mul_le_mul_left _ hI
      _ = n * (t * m) := by ring
      _ ≤ n * (n + c) := Nat.mul_le_mul_left _ hcase
      _ = n ^ 2 + c * n := by ring
  · rw [not_le] at hcase
    have hm : 1 ≤ m := by
      rcases Nat.eq_zero_or_pos m with h | h
      · rw [h] at hcase; omega
      · exact h
    have htpos : 0 < t := by
      rcases Nat.eq_zero_or_pos t with h | h
      · rw [h] at hcase; omega
      · exact h
    have hd1 := h1 hm
    subst hdim
    have e3 := Nat.mul_le_mul_left (t * t) hsum2
    have h5 := Nat.mul_le_mul_left t hd1
    have h3 : (n1 + m) * (n1 + m + c) ≤ (t * m) * (n1 + m + c) := Nat.mul_le_mul_right _ (by omega)
    have h4 : (t * m) * (n1 + m + c) ≤ (t * m) * (2 * n1 + m + c) := Nat.mul_le_mul_left _ (by omega)
    have key : t * (t * dA) ≤ t * ((n1 + m) ^ 2 + c * (n1 + m)) := by nlinarith
    by_contra hlt
    rw [not_le] at hlt
    have := Nat.mul_lt_mul_of_pos_left hlt htpos
    omega

/- English proof (translation)
Simplify using `only [not_exists, not_not] at hs`. Set `b : Fin (l + 1) → Module.End ℂ V` to `fun i => a i - algebraMap ℂ (Module.End ℂ V) (μ i)`. Establish `hbmem : ∀ i, b i ∈ Algebra.adjoin ℂ (Set.range a)` using `fun i => sub_mem (Algebra.subset_adjoin (Set.mem_range_self i)) (Subalgebra.algebraMap_mem _ _)`. Establish `hab : ∀ i j, a j * b i = b i * a j`. Introduce `i j`.

Use `show a j * (a i - _) = (a i - _) * a j`. Rewrite using `[mul_sub, sub_mul, ha j i, Algebra.commutes]`. Establish `hxb : ∀ i, ∀ x ∈ Algebra.adjoin ℂ (Set.range a), x * b i = b i * x` using `fun i x hx => comm_of_mem a (b i) (fun j => hab i j) hx`. Establish `hbb : ∀ i j, b i * b j = b j * b i` using `fun i j => hxb j (b i) (hbmem i)`. Establish `hnil : ∀ i, ∃ M : ℕ, b i ^ M = 0` using `fun i => ⟨N i, LinearMap.range_eq_bot.1 (hs i)⟩`.

Take `⟨V1, hV1⟩ : ∃ V1 : Submodule ℂ V, V1 = ⨆ i ∈ (Finset.univ : Finset (Fin (l + 1))), LinearMap.range (b i)` from `⟨_, rfl⟩`. Take `⟨L, hL⟩` from `Submodule.exists_isCompl V1`. Establish `hdim` using `Submodule.finrank_add_eq_of_isCompl hL`. Rewrite `hdim` using `[hn]`. Establish `hV1inv : ∀ j, ∀ v ∈ V1, a j v ∈ V1`.

Rewrite using `[hV1]`. Conclude with `fun j => iSup_range_inv _ b (a j) (fun i => hab i j)`. Establish `hI : finrank ℂ (Algebra.adjoin ℂ (Set.range a)) ≤ finrank ℂ L * n`. Rewrite using `[← sub_finrank, ← hn, ← finrank_hom L]`. Apply `injective_bound _ (pre L)` to reduce the goal to its premises.

Introduce `x hx hx0`. Establish `hLk : L ≤ LinearMap.ker x`. Introduce `v hv`. Establish `e` using `LinearMap.congr_fun hx0 ⟨v, hv⟩`. Express the relevant statement in the definitionally equal form `x v = 0 at e`.

Conclude with `LinearMap.mem_ker.2 e`. Establish `hU : LinearMap.ker x = ⊤`. Apply `nak Finset.univ b hbb hnil` to reduce the goal to its premises. Introduce `i v hv`. Rewrite `hv`, the goal using `[LinearMap.mem_ker]`.

Establish `e : x (b i v) = b i (x v)` using `LinearMap.congr_fun (hxb i x hx) v`. Rewrite using `[e, hv, map_zero]`. Rewrite using `[← hV1, eq_top_iff, ← hL.sup_eq_top]`. Conclude with `sup_le le_sup_right (le_sup_of_le_left hLk)`. Conclude with `LinearMap.ker_eq_top.1 hU`.

Establish `hle : Algebra.adjoin ℂ (Set.range fun j : Fin l => a j.succ) ≤ Algebra.adjoin ℂ (Set.range a)` using `Algebra.adjoin_mono (by rintro _ ⟨j, rfl⟩; exact ⟨j.succ, rfl⟩)`. Establish `hAsup : Subalgebra.toSubmodule (Algebra.adjoin ℂ (Set.range a)) ≤ Subalgebra.toSubmodule (Algebra.adjoin ℂ (Set.range fun j : Fin l => a j.succ)) ⊔ (Subalgebra.toSubmodule (Algebra.adjoin ℂ (Set.range a))).map (LinearMap.mulLeft ℂ (b 0))`. Introduce `x hx`. Take `⟨y, hy, z, hz, rfl⟩` from `decomp l a (b 0) (μ 0) rfl (hxb 0) (hbmem 0) hle hx`. Conclude with `Submodule.add_mem_sup hy (Submodule.mem_map.2 ⟨z, hz, rfl⟩)`.

Establish `hmul : finrank ℂ ((Subalgebra.toSubmodule (Algebra.adjoin ℂ (Set.range a))).map (LinearMap.mulLeft ℂ (b 0))) ≤ finrank ℂ ((Subalgebra.toSubmodule (Algebra.adjoin ℂ (Set.range a))).map (pre V1))`. Apply `finrank_map_le_of_ker` to reduce the goal to its premises. Introduce `x hx hx0`. Apply `LinearMap.ext` to reduce the goal to its premises. Introduce `v`.

Establish `hbv : b 0 v ∈ V1`. Rewrite using `[hV1]`. Conclude with `(le_iSup₂ (f := fun i (_ : i ∈ (Finset.univ : Finset (Fin (l + 1)))) => LinearMap.range (b i)) 0 (Finset.mem_univ 0)) (LinearMap.mem_range_self _ _)`. Establish `e1` using `LinearMap.congr_fun hx0 ⟨b 0 v, hbv⟩`. Express the relevant statement in the definitionally equal form `x (b 0 v) = 0 at e1`.

Establish `e2 : (b 0 * x) v = (x * b 0) v` using `(LinearMap.congr_fun (hxb 0 x hx) v).symm`. Use `show (b 0 * x) v = 0`. Rewrite using `[e2]`. Conclude with `e1`. Establish `h3` using `finrank_map_pre_le V1 a hV1inv`.

Establish `h4` using `Submodule.finrank_mono hAsup`. Establish `h5` using `Submodule.finrank_add_le_finrank_add_finrank (Subalgebra.toSubmodule (Algebra.adjoin ℂ (Set.range fun j : Fin l => a j.succ))) ((Subalgebra.toSubmodule (Algebra.adjoin ℂ (Set.range a))).map (LinearMap.mulLeft ℂ (b 0)))`. Establish `eA` using `sub_finrank (Algebra.adjoin ℂ (Set.range a))`. Establish `eA'` using `sub_finrank (Algebra.adjoin ℂ (Set.range fun j : Fin l => a j.succ))`. Establish `hsum2 : finrank ℂ (Algebra.adjoin ℂ (Set.range a)) ≤ finrank ℂ (Algebra.adjoin ℂ (Set.range fun j : Fin l => a j.succ)) + finrank ℂ (Algebra.adjoin ℂ (Set.range fun j => rs V1 (a j) (hV1inv j)))`.

Use linear arithmetic over natural numbers and integers. Establish `hA'` using `hP V (fun j : Fin l => a j.succ) (fun i j => ha i.succ j.succ)`. Rewrite `hA'` using `[hn]`. Conclude with `arith_local t c n (finrank ℂ L) (finrank ℂ V1) _ _ _ hdim hI hsum2 hA' (fun hm => IH _ (by omega) V1 rfl (fun j => rs V1 (a j) (hV1inv j)) (rs_comm V1 a ha hV1inv))`.
-/
theorem local_case (l t c : ℕ) (hP : Pl l (t * t) c) (n : ℕ) (IH : IHn l t c n) (V : Type)
    [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V] (hn : finrank ℂ V = n)
    (a : Fin (l + 1) → Module.End ℂ V) (ha : ∀ i j, a i * a j = a j * a i) (μ : Fin (l + 1) → ℂ)
    (N : Fin (l + 1) → ℕ)
    (hs : ¬∃ i, LinearMap.range ((a i - algebraMap ℂ (Module.End ℂ V) (μ i)) ^ N i) ≠ ⊥) :
    t * finrank ℂ (Algebra.adjoin ℂ (Set.range a)) ≤ n ^ 2 + c * n := by
  simp only [not_exists, not_not] at hs
  let b : Fin (l + 1) → Module.End ℂ V := fun i => a i - algebraMap ℂ (Module.End ℂ V) (μ i)
  have hbmem : ∀ i, b i ∈ Algebra.adjoin ℂ (Set.range a) :=
    fun i => sub_mem (Algebra.subset_adjoin (Set.mem_range_self i)) (Subalgebra.algebraMap_mem _ _)
  have hab : ∀ i j, a j * b i = b i * a j := by
    intro i j; show a j * (a i - _) = (a i - _) * a j
    rw [mul_sub, sub_mul, ha j i, Algebra.commutes]
  have hxb : ∀ i, ∀ x ∈ Algebra.adjoin ℂ (Set.range a), x * b i = b i * x :=
    fun i x hx => comm_of_mem a (b i) (fun j => hab i j) hx
  have hbb : ∀ i j, b i * b j = b j * b i := fun i j => hxb j (b i) (hbmem i)
  have hnil : ∀ i, ∃ M : ℕ, b i ^ M = 0 := fun i => ⟨N i, LinearMap.range_eq_bot.1 (hs i)⟩
  obtain ⟨V1, hV1⟩ : ∃ V1 : Submodule ℂ V,
      V1 = ⨆ i ∈ (Finset.univ : Finset (Fin (l + 1))), LinearMap.range (b i) := ⟨_, rfl⟩
  obtain ⟨L, hL⟩ := Submodule.exists_isCompl V1
  have hdim := Submodule.finrank_add_eq_of_isCompl hL
  rw [hn] at hdim
  have hV1inv : ∀ j, ∀ v ∈ V1, a j v ∈ V1 := by
    rw [hV1]; exact fun j => iSup_range_inv _ b (a j) (fun i => hab i j)

  have hI : finrank ℂ (Algebra.adjoin ℂ (Set.range a)) ≤ finrank ℂ L * n := by
    rw [← sub_finrank, ← hn, ← finrank_hom L]
    apply injective_bound _ (pre L)
    intro x hx hx0
    have hLk : L ≤ LinearMap.ker x := by
      intro v hv
      have e := LinearMap.congr_fun hx0 ⟨v, hv⟩
      change x v = 0 at e
      exact LinearMap.mem_ker.2 e
    have hU : LinearMap.ker x = ⊤ := by
      apply nak Finset.univ b hbb hnil
      · intro i v hv
        rw [LinearMap.mem_ker] at hv ⊢
        have e : x (b i v) = b i (x v) := LinearMap.congr_fun (hxb i x hx) v
        rw [e, hv, map_zero]
      · rw [← hV1, eq_top_iff, ← hL.sup_eq_top]
        exact sup_le le_sup_right (le_sup_of_le_left hLk)
    exact LinearMap.ker_eq_top.1 hU
  have hle : Algebra.adjoin ℂ (Set.range fun j : Fin l => a j.succ) ≤
      Algebra.adjoin ℂ (Set.range a) :=
    Algebra.adjoin_mono (by rintro _ ⟨j, rfl⟩; exact ⟨j.succ, rfl⟩)
  have hAsup : Subalgebra.toSubmodule (Algebra.adjoin ℂ (Set.range a)) ≤
      Subalgebra.toSubmodule (Algebra.adjoin ℂ (Set.range fun j : Fin l => a j.succ)) ⊔
      (Subalgebra.toSubmodule (Algebra.adjoin ℂ (Set.range a))).map (LinearMap.mulLeft ℂ (b 0)) := by
    intro x hx
    obtain ⟨y, hy, z, hz, rfl⟩ := decomp l a (b 0) (μ 0) rfl (hxb 0) (hbmem 0) hle hx
    exact Submodule.add_mem_sup hy (Submodule.mem_map.2 ⟨z, hz, rfl⟩)
  have hmul : finrank ℂ ((Subalgebra.toSubmodule (Algebra.adjoin ℂ (Set.range a))).map
      (LinearMap.mulLeft ℂ (b 0))) ≤
      finrank ℂ ((Subalgebra.toSubmodule (Algebra.adjoin ℂ (Set.range a))).map (pre V1)) := by
    apply finrank_map_le_of_ker
    intro x hx hx0
    apply LinearMap.ext; intro v
    have hbv : b 0 v ∈ V1 := by
      rw [hV1]
      exact (le_iSup₂ (f := fun i (_ : i ∈ (Finset.univ : Finset (Fin (l + 1)))) =>
        LinearMap.range (b i)) 0 (Finset.mem_univ 0)) (LinearMap.mem_range_self _ _)
    have e1 := LinearMap.congr_fun hx0 ⟨b 0 v, hbv⟩
    change x (b 0 v) = 0 at e1
    have e2 : (b 0 * x) v = (x * b 0) v := (LinearMap.congr_fun (hxb 0 x hx) v).symm
    show (b 0 * x) v = 0
    rw [e2]; exact e1
  have h3 := finrank_map_pre_le V1 a hV1inv
  have h4 := Submodule.finrank_mono hAsup
  have h5 := Submodule.finrank_add_le_finrank_add_finrank
    (Subalgebra.toSubmodule (Algebra.adjoin ℂ (Set.range fun j : Fin l => a j.succ)))
    ((Subalgebra.toSubmodule (Algebra.adjoin ℂ (Set.range a))).map (LinearMap.mulLeft ℂ (b 0)))
  have eA := sub_finrank (Algebra.adjoin ℂ (Set.range a))
  have eA' := sub_finrank (Algebra.adjoin ℂ (Set.range fun j : Fin l => a j.succ))
  have hsum2 : finrank ℂ (Algebra.adjoin ℂ (Set.range a)) ≤
      finrank ℂ (Algebra.adjoin ℂ (Set.range fun j : Fin l => a j.succ)) +
      finrank ℂ (Algebra.adjoin ℂ (Set.range fun j => rs V1 (a j) (hV1inv j))) := by
    omega
  have hA' := hP V (fun j : Fin l => a j.succ) (fun i j => ha i.succ j.succ)
  rw [hn] at hA'
  exact arith_local t c n (finrank ℂ L) (finrank ℂ V1) _ _ _ hdim hI hsum2 hA'
    (fun hm => IH _ (by omega) V1 rfl (fun j => rs V1 (a j) (hV1inv j)) (rs_comm V1 a ha hV1inv))

/- English proof (translation)
It suffices to establish `H : ∀ n : ℕ, ∀ (V : Type) [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V], finrank ℂ V = n → ∀ (a : Fin (l + 1) → Module.End ℂ V), (∀ i j, a i * a j = a j * a i) → t * finrank ℂ (Algebra.adjoin ℂ (Set.range a)) ≤ n ^ 2 + c * n by`. Introduce `V _ _ _ a ha`. Conclude with `H _ V rfl a ha`. Introduce `n`. Use `Nat.strong_induction_on n ?_` and prove the remaining obligations.

Introduce `n IH V _ _ _ hn a ha`. Break down `Nat.eq_zero_or_pos n with hn0 | hnpos` into its components or cases. Substitute `hn0` using the available equality. Establish `h` using `finrank_sub_le_sq (Algebra.adjoin ℂ (Set.range a))`. Rewrite `h` using `[hn]`.

Establish `: finrank ℂ (Algebra.adjoin ℂ (Set.range a)) = 0` using `by omega`. Rewrite using `[this]`. Simplify using the standard rewrite rules. Use `haveI : Nontrivial V := Module.finrank_pos_iff.1 (show 0 < finrank ℂ V by omega)`. Use `choose μ hμ using fun i => Module.End.exists_eigenvalue (a i)`.

Set `b : Fin (l + 1) → Module.End ℂ V` to `fun i => a i - algebraMap ℂ (Module.End ℂ V) (μ i)`. Establish `hb : ∀ i, b i = a i - algebraMap ℂ (Module.End ℂ V) (μ i)` using `fun i => rfl`. Establish `hamem : ∀ i, a i ∈ Algebra.adjoin ℂ (Set.range a)` using `fun i => Algebra.subset_adjoin (Set.mem_range_self i)`. Establish `hbmem : ∀ i, b i ∈ Algebra.adjoin ℂ (Set.range a)` using `fun i => sub_mem (hamem i) (Subalgebra.algebraMap_mem _ _)`. Establish `hab : ∀ i j, a j * b i = b i * a j`.

Introduce `i j`. Rewrite using `[hb, mul_sub, sub_mul, ha j i, Algebra.commutes]`. Establish `hxa : ∀ i, ∀ x ∈ Algebra.adjoin ℂ (Set.range a), x * a i = a i * x` using `fun i x hx => comm_of_mem a (a i) (fun j => ha j i) hx`. Establish `hxb : ∀ i, ∀ x ∈ Algebra.adjoin ℂ (Set.range a), x * b i = b i * x` using `fun i x hx => comm_of_mem a (b i) (fun j => hab i j) hx`. Establish `hbb : ∀ i j, b i * b j = b j * b i` using `fun i j => hxb j (b i) (hbmem i)`.

Establish `hfit : ∀ i, ∃ N : ℕ, IsCompl (LinearMap.ker (b i ^ N)) (LinearMap.range (b i ^ N)) ∧ 1 ≤ N`. Introduce `i`. Use `first`. Consider the case `exact ((LinearMap.eventually_isCompl_ker_pow_range_pow (b i)).and (Filter.eventually_ge_atTop 1)).exists`. Consider the case `exact ((Module.End.eventually_isCompl_ker_pow_range_pow (b i)).and (Filter.eventually_ge_atTop 1)).exists`.

Use `choose N hN using hfit`. Distinguish the cases in `hs : ∃ i, LinearMap.range (b i ^ N i) ≠ ⊥`. Conclude with `split_case l t c n IH V hn a ha μ hμ N hN hs`. Conclude with `local_case l t c hP n IH V hn a ha μ N hs`.
-/
theorem step (l t c : ℕ) (hP : Pl l (t * t) c) : Pl (l + 1) t c := by
  suffices H : ∀ n : ℕ, ∀ (V : Type) [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V],
      finrank ℂ V = n → ∀ (a : Fin (l + 1) → Module.End ℂ V), (∀ i j, a i * a j = a j * a i) →
      t * finrank ℂ (Algebra.adjoin ℂ (Set.range a)) ≤ n ^ 2 + c * n by
    intro V _ _ _ a ha
    exact H _ V rfl a ha
  intro n
  refine Nat.strong_induction_on n ?_
  intro n IH V _ _ _ hn a ha
  rcases Nat.eq_zero_or_pos n with hn0 | hnpos
  · subst hn0
    have h := finrank_sub_le_sq (Algebra.adjoin ℂ (Set.range a))
    rw [hn] at h
    have : finrank ℂ (Algebra.adjoin ℂ (Set.range a)) = 0 := by omega
    rw [this]; simp
  haveI : Nontrivial V := Module.finrank_pos_iff.1 (show 0 < finrank ℂ V by omega)
  choose μ hμ using fun i => Module.End.exists_eigenvalue (a i)
  let b : Fin (l + 1) → Module.End ℂ V := fun i => a i - algebraMap ℂ (Module.End ℂ V) (μ i)
  have hb : ∀ i, b i = a i - algebraMap ℂ (Module.End ℂ V) (μ i) := fun i => rfl
  have hamem : ∀ i, a i ∈ Algebra.adjoin ℂ (Set.range a) := fun i => Algebra.subset_adjoin (Set.mem_range_self i)
  have hbmem : ∀ i, b i ∈ Algebra.adjoin ℂ (Set.range a) :=
    fun i => sub_mem (hamem i) (Subalgebra.algebraMap_mem _ _)
  have hab : ∀ i j, a j * b i = b i * a j := by
    intro i j; rw [hb, mul_sub, sub_mul, ha j i, Algebra.commutes]
  have hxa : ∀ i, ∀ x ∈ Algebra.adjoin ℂ (Set.range a), x * a i = a i * x :=
    fun i x hx => comm_of_mem a (a i) (fun j => ha j i) hx
  have hxb : ∀ i, ∀ x ∈ Algebra.adjoin ℂ (Set.range a), x * b i = b i * x :=
    fun i x hx => comm_of_mem a (b i) (fun j => hab i j) hx
  have hbb : ∀ i j, b i * b j = b j * b i := fun i j => hxb j (b i) (hbmem i)
  have hfit : ∀ i, ∃ N : ℕ, IsCompl (LinearMap.ker (b i ^ N)) (LinearMap.range (b i ^ N)) ∧ 1 ≤ N := by
    intro i
    first
    | exact ((LinearMap.eventually_isCompl_ker_pow_range_pow (b i)).and
        (Filter.eventually_ge_atTop 1)).exists
    | exact ((Module.End.eventually_isCompl_ker_pow_range_pow (b i)).and
        (Filter.eventually_ge_atTop 1)).exists
  choose N hN using hfit
  by_cases hs : ∃ i, LinearMap.range (b i ^ N i) ≠ ⊥
  · exact split_case l t c n IH V hn a ha μ hμ N hN hs
  · exact local_case l t c hP n IH V hn a ha μ N hs

/- English proof (translation)
Introduce `l`. Proceed by induction on `l with`. Consider the case `zero => intro t`. Conclude with `⟨t, base t⟩`. Consider the case `succ l ih => intro t`.

Take `⟨c, hc⟩` from `ih (t * t)`. Conclude with `⟨c, step l t c hc⟩`.
-/
theorem allP : ∀ l t : ℕ, ∃ c, Pl l t c := by
  intro l
  induction l with
  | zero => intro t; exact ⟨t, base t⟩
  | succ l ih => intro t; obtain ⟨c, hc⟩ := ih (t * t); exact ⟨c, step l t c hc⟩

end DiscreteGroups.sglob.LConv.Comm

namespace DiscreteGroups.sglob.LConv

/- English proof (translation)
Introduce `l t`. Take `⟨c, hc⟩` from `Comm.allP l t`. Conclude with `⟨c, hc⟩`.
-/
theorem commBound : CommBound := by
  intro l t
  obtain ⟨c, hc⟩ := Comm.allP l t
  exact ⟨c, hc⟩

end DiscreteGroups.sglob.LConv

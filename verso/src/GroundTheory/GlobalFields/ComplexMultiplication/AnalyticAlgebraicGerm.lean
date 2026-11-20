import Mathlib

open Filter Topology Set

noncomputable section

namespace GroundTheory.Global
namespace Elliptic

/- English proof (translation)
Express the relevant statement in the definitionally equal form `{z | f z = (0 : ℂ → ℂ) z} ∈ codiscreteWithin univ ↔ _`. Rewrite using `[mem_codiscreteWithin_iff_forall_mem_nhdsNE]`. Simplify using `only [compl_univ, union_empty, mem_univ, true_implies, Pi.zero_apply]`. Both sides reduce to the same expression.
-/
theorem eventuallyEq_zero_codiscrete_iff {f : ℂ → ℂ} :
    f =ᶠ[codiscrete ℂ] 0 ↔ ∀ x, ∀ᶠ z in 𝓝[≠] x, f z = 0 := by
  change {z | f z = (0 : ℂ → ℂ) z} ∈ codiscreteWithin univ ↔ _
  rw [mem_codiscreteWithin_iff_forall_mem_nhdsNE]
  simp only [compl_univ, union_empty, mem_univ, true_implies, Pi.zero_apply]
  rfl

/- English proof (translation)
Rewrite using `[eventuallyEq_zero_codiscrete_iff]`. Introduce `u`. Establish `hx : meromorphicOrderAt f x = ⊤` using `meromorphicOrderAt_eq_top_iff.2 h`. Assume the negation of the conclusion as `hu`. Establish `hu' : meromorphicOrderAt f u ≠ ⊤` using `fun ht ↦ hu (meromorphicOrderAt_eq_top_iff.1 ht)`.

Conclude with `(hf.meromorphicOn (s := univ)).meromorphicOrderAt_ne_top_of_isPreconnected isPreconnected_univ (mem_univ u) (mem_univ x) hu' hx`.
-/
theorem eventuallyEq_zero_codiscrete_of_nhdsNE {f : ℂ → ℂ} (hf : Meromorphic f) {x : ℂ}
    (h : ∀ᶠ z in 𝓝[≠] x, f z = 0) : f =ᶠ[codiscrete ℂ] 0 := by
  rw [eventuallyEq_zero_codiscrete_iff]
  intro u
  have hx : meromorphicOrderAt f x = ⊤ := meromorphicOrderAt_eq_top_iff.2 h
  by_contra hu
  have hu' : meromorphicOrderAt f u ≠ ⊤ := fun ht ↦ hu (meromorphicOrderAt_eq_top_iff.1 ht)
  exact (hf.meromorphicOn (s := univ)).meromorphicOrderAt_ne_top_of_isPreconnected
    isPreconnected_univ (mem_univ u) (mem_univ x) hu' hx

/- English proof (translation)
Establish `hall : ∀ u ∈ (univ : Set ℂ), meromorphicOrderAt f u ≠ ⊤` using `fun u _ ht ↦ h (eventuallyEq_zero_codiscrete_of_nhdsNE hf (meromorphicOrderAt_eq_top_iff.1 ht))`. Conclude with `MeromorphicAt.MeromorphicOn.codiscreteWithin_setOfPred_ne_zero (hf.meromorphicOn (s := univ)) hall`.
-/
theorem eventually_ne_zero_codiscrete {f : ℂ → ℂ} (hf : Meromorphic f)
    (h : ¬ f =ᶠ[codiscrete ℂ] 0) : ∀ᶠ z in codiscrete ℂ, f z ≠ 0 := by
  have hall : ∀ u ∈ (univ : Set ℂ), meromorphicOrderAt f u ≠ ⊤ := fun u _ ht ↦
    h (eventuallyEq_zero_codiscrete_of_nhdsNE hf (meromorphicOrderAt_eq_top_iff.1 ht))
  exact MeromorphicAt.MeromorphicOn.codiscreteWithin_setOfPred_ne_zero
    (hf.meromorphicOn (s := univ)) hall

/- English proof (translation)
Establish `h` using `(mem_codiscreteWithin_iff_forall_mem_nhdsNE.1 hS) 0 (mem_univ 0)`. Rewrite `h` using `[compl_univ, union_empty]`. Conclude with `Filter.nonempty_of_mem h`.
-/
theorem nonempty_of_mem_codiscrete {S : Set ℂ} (hS : S ∈ codiscrete ℂ) : S.Nonempty := by
  have h := (mem_codiscreteWithin_iff_forall_mem_nhdsNE.1 hS) 0 (mem_univ 0)
  rw [compl_univ, union_empty] at h
  exact Filter.nonempty_of_mem h

/- English proof (translation)
The claim follows from `(mem_codiscrete'.1 hS).1`.
-/
theorem isOpen_of_mem_codiscrete {S : Set ℂ} (hS : S ∈ codiscrete ℂ) : IsOpen S :=
  (mem_codiscrete'.1 hS).1

/- English proof (translation)
The claim follows from `(hf.meromorphicOn (s := univ)).analyticAt_mem_codiscreteWithin`.
-/
theorem eventually_analyticAt {f : ℂ → ℂ} (hf : Meromorphic f) :
    ∀ᶠ z in codiscrete ℂ, AnalyticAt ℂ f z :=
  (hf.meromorphicOn (s := univ)).analyticAt_mem_codiscreteWithin

/- English proof (translation)
Establish `hS` using `isOpen_of_mem_codiscrete h`. Use `filter_upwards [h] with z hz`. Conclude with `Filter.EventuallyEq.deriv_eq (Filter.mem_of_superset (hS.mem_nhds hz) fun w hw ↦ hw)`.
-/
theorem deriv_eventuallyEq_codiscrete {f g : ℂ → ℂ} (h : f =ᶠ[codiscrete ℂ] g) :
    deriv f =ᶠ[codiscrete ℂ] deriv g := by
  have hS := isOpen_of_mem_codiscrete h
  filter_upwards [h] with z hz
  exact Filter.EventuallyEq.deriv_eq (Filter.mem_of_superset (hS.mem_nhds hz) fun w hw ↦ hw)

def meroSubalgebra : Subalgebra ℂ (ℂ → ℂ) where
  carrier := {f | Meromorphic f}
  mul_mem' hf hg := Meromorphic.mul hf hg
  add_mem' hf hg := Meromorphic.add hf hg
  algebraMap_mem' c := Meromorphic.const c

def meroNull : Ideal meroSubalgebra where
  carrier := {f | (f : ℂ → ℂ) =ᶠ[codiscrete ℂ] 0}
  add_mem' {f g} hf hg := by
    change (fun z ↦ f.1 z + g.1 z) =ᶠ[codiscrete ℂ] 0
    filter_upwards [hf, hg] with z h1 h2
    simp only [Pi.zero_apply] at h1 h2 ⊢
    rw [h1, h2, add_zero]
  zero_mem' := by
    change ((0 : meroSubalgebra) : ℂ → ℂ) =ᶠ[codiscrete ℂ] 0
    exact Filter.EventuallyEq.rfl
  smul_mem' c f hf := by
    change (fun z ↦ c.1 z * f.1 z) =ᶠ[codiscrete ℂ] 0
    filter_upwards [hf] with z h
    simp only [Pi.zero_apply] at h ⊢
    rw [h, mul_zero]

/- English proof (translation)
Unfold both sides. The equivalence is reflexive.
-/
theorem mem_meroNull {f : meroSubalgebra} : f ∈ meroNull ↔ (f : ℂ → ℂ) =ᶠ[codiscrete ℂ] 0 :=
  Iff.rfl

instance meroNull_isMaximal : meroNull.IsMaximal := by
  rw [Ideal.isMaximal_iff]
  refine ⟨fun h1 ↦ ?_, fun J x hle hx hxJ ↦ ?_⟩
  · have h := (eventuallyEq_zero_codiscrete_iff.1 (mem_meroNull.1 h1)) 0
    obtain ⟨z, hz⟩ := h.exists
    exact one_ne_zero hz
  · have hf : Meromorphic (x : ℂ → ℂ) := x.2
    have hne := eventually_ne_zero_codiscrete hf hx
    let y : meroSubalgebra := ⟨(x : ℂ → ℂ)⁻¹, hf.inv⟩
    have hxy : x * y - 1 ∈ meroNull := by
      rw [mem_meroNull]
      change (fun z ↦ x.1 z * (x.1 z)⁻¹ - 1) =ᶠ[codiscrete ℂ] 0
      filter_upwards [hne] with z hz
      simp only [Pi.zero_apply]
      rw [mul_inv_cancel₀ hz, sub_self]
    have h1 : (1 : meroSubalgebra) = x * y - (x * y - 1) := by ring
    rw [h1]
    exact J.sub_mem (J.mul_mem_right y hxJ) (hle hxy)

abbrev MeroField : Type := meroSubalgebra ⧸ meroNull

noncomputable instance : Field MeroField := Ideal.Quotient.field _

noncomputable instance : DecidableEq MeroField := Classical.decEq _

open Classical in

def germ (f : ℂ → ℂ) : MeroField :=
  if h : Meromorphic f then Ideal.Quotient.mk meroNull ⟨f, h⟩ else 0

/- English proof (translation)
The claim follows from `dif_pos hf`.
-/
theorem germ_of {f : ℂ → ℂ} (hf : Meromorphic f) : germ f = Ideal.Quotient.mk meroNull ⟨f, hf⟩ :=
  dif_pos hf

/- English proof (translation)
Take `⟨⟨f, hf⟩, rfl⟩` from `Ideal.Quotient.mk_surjective u`. Conclude with `⟨f, hf, germ_of hf⟩`.
-/
theorem germ_surjective (u : MeroField) : ∃ f : ℂ → ℂ, Meromorphic f ∧ germ f = u := by
  obtain ⟨⟨f, hf⟩, rfl⟩ := Ideal.Quotient.mk_surjective u
  exact ⟨f, hf, germ_of hf⟩

/- English proof (translation)
Rewrite using `[germ_of hf, germ_of hg, Ideal.Quotient.eq, mem_meroNull]`. Express the relevant statement in the definitionally equal form `(f - g) =ᶠ[codiscrete ℂ] 0 ↔ _`. Conclude with `Filter.eventuallyEq_iff_sub.symm`.
-/
theorem germ_eq_germ_iff {f g : ℂ → ℂ} (hf : Meromorphic f) (hg : Meromorphic g) :
    germ f = germ g ↔ f =ᶠ[codiscrete ℂ] g := by
  rw [germ_of hf, germ_of hg, Ideal.Quotient.eq, mem_meroNull]
  change (f - g) =ᶠ[codiscrete ℂ] 0 ↔ _
  exact Filter.eventuallyEq_iff_sub.symm

/- English proof (translation)
The claim follows from `(germ_eq_germ_iff hf (hf.congr_codiscrete h)).2 h`.
-/
theorem germ_congr {f g : ℂ → ℂ} (hf : Meromorphic f) (h : f =ᶠ[codiscrete ℂ] g) :
    germ f = germ g :=
  (germ_eq_germ_iff hf (hf.congr_codiscrete h)).2 h

/- English proof (translation)
Rewrite using `[germ_of hf, Ideal.Quotient.eq_zero_iff_mem, mem_meroNull]`.
-/
theorem germ_eq_zero_iff {f : ℂ → ℂ} (hf : Meromorphic f) : germ f = 0 ↔ f =ᶠ[codiscrete ℂ] 0 := by
  rw [germ_of hf, Ideal.Quotient.eq_zero_iff_mem, mem_meroNull]

/- English proof (translation)
Rewrite using `[germ_of hf, germ_of hg, germ_of (hf.add hg), ← map_add]`. Both sides reduce to the same expression.
-/
theorem germ_add {f g : ℂ → ℂ} (hf : Meromorphic f) (hg : Meromorphic g) :
    germ (f + g) = germ f + germ g := by
  rw [germ_of hf, germ_of hg, germ_of (hf.add hg), ← map_add]
  rfl

/- English proof (translation)
Rewrite using `[germ_of hf, germ_of hg, germ_of (hf.mul hg), ← map_mul]`. Both sides reduce to the same expression.
-/
theorem germ_mul {f g : ℂ → ℂ} (hf : Meromorphic f) (hg : Meromorphic g) :
    germ (f * g) = germ f * germ g := by
  rw [germ_of hf, germ_of hg, germ_of (hf.mul hg), ← map_mul]
  rfl

/- English proof (translation)
Rewrite using `[germ_of hf, germ_of hf.neg, ← map_neg]`. Both sides reduce to the same expression.
-/
theorem germ_neg {f : ℂ → ℂ} (hf : Meromorphic f) : germ (-f) = -germ f := by
  rw [germ_of hf, germ_of hf.neg, ← map_neg]
  rfl

/- English proof (translation)
Rewrite using `[sub_eq_add_neg, germ_add hf hg.neg, germ_neg hg, ← sub_eq_add_neg]`.
-/
theorem germ_sub {f g : ℂ → ℂ} (hf : Meromorphic f) (hg : Meromorphic g) :
    germ (f - g) = germ f - germ g := by
  rw [sub_eq_add_neg, germ_add hf hg.neg, germ_neg hg, ← sub_eq_add_neg]

/- English proof (translation)
Rewrite using `[germ_of (Meromorphic.const c)]`. Both sides reduce to the same expression.
-/
theorem germ_const (c : ℂ) : germ (fun _ ↦ c) = algebraMap ℂ MeroField c := by
  rw [germ_of (Meromorphic.const c)]
  rfl

/- English proof (translation)
Use `germ_const 0` as an intermediate fact. Rewrite `this` using `[map_zero]`. Conclude with `this`.
-/
theorem germ_zero : germ (0 : ℂ → ℂ) = 0 := by
  have := germ_const 0
  rw [map_zero] at this
  exact this

/- English proof (translation)
Use `germ_const 1` as an intermediate fact. Rewrite `this` using `[map_one]`. Conclude with `this`.
-/
theorem germ_one : germ (1 : ℂ → ℂ) = 1 := by
  have := germ_const 1
  rw [map_one] at this
  exact this

/- English proof (translation)
Rewrite using `[germ_of hf, germ_of (hf.pow (n := n)), ← map_pow]`. Both sides reduce to the same expression.
-/
theorem germ_pow {f : ℂ → ℂ} (hf : Meromorphic f) (n : ℕ) : germ (f ^ n) = germ f ^ n := by
  rw [germ_of hf, germ_of (hf.pow (n := n)), ← map_pow]
  rfl

/- English proof (translation)
Distinguish the cases in `h0 : f =ᶠ[codiscrete ℂ] 0`. Rewrite using `[(germ_eq_zero_iff hf).2 h0, inv_zero, germ_eq_zero_iff hf.inv] filter_upwards [h0] with z hz`. Simplify using `only [Pi.inv_apply, Pi.zero_apply] at hz ⊢`. Rewrite using `[hz, inv_zero]`. Establish `hne` using `eventually_ne_zero_codiscrete hf h0`.

Establish `h1 : germ f * germ f⁻¹ = 1`. Rewrite using `[← germ_mul hf hf.inv, ← germ_one]`. Apply `germ_congr (hf.mul hf.inv)` to reduce the goal to its premises. Use `filter_upwards [hne] with z hz`. Simplify using `only [Pi.mul_apply, Pi.inv_apply, Pi.one_apply]`.

Conclude with `mul_inv_cancel₀ hz`. Conclude with `(eq_inv_of_mul_eq_one_right h1)`.
-/
theorem germ_inv {f : ℂ → ℂ} (hf : Meromorphic f) : germ f⁻¹ = (germ f)⁻¹ := by
  by_cases h0 : f =ᶠ[codiscrete ℂ] 0
  · rw [(germ_eq_zero_iff hf).2 h0, inv_zero, germ_eq_zero_iff hf.inv]
    filter_upwards [h0] with z hz
    simp only [Pi.inv_apply, Pi.zero_apply] at hz ⊢
    rw [hz, inv_zero]
  · have hne := eventually_ne_zero_codiscrete hf h0
    have h1 : germ f * germ f⁻¹ = 1 := by
      rw [← germ_mul hf hf.inv, ← germ_one]
      apply germ_congr (hf.mul hf.inv)
      filter_upwards [hne] with z hz
      simp only [Pi.mul_apply, Pi.inv_apply, Pi.one_apply]
      exact mul_inv_cancel₀ hz
    exact (eq_inv_of_mul_eq_one_right h1)

/- English proof (translation)
Rewrite using `[div_eq_mul_inv, germ_mul hf hg.inv, germ_inv hg, ← div_eq_mul_inv]`.
-/
theorem germ_div {f g : ℂ → ℂ} (hf : Meromorphic f) (hg : Meromorphic g) :
    germ (f / g) = germ f / germ g := by
  rw [div_eq_mul_inv, germ_mul hf hg.inv, germ_inv hg, ← div_eq_mul_inv]

/- English proof (translation)
Rewrite `h`, the goal using `[eventuallyEq_zero_codiscrete_iff]`. Introduce `x`. Establish `hc : Continuous fun z : ℂ ↦ t * z + s` using `by fun_prop`. Establish `hmaps : MapsTo (fun z : ℂ ↦ t * z + s) {x}ᶜ {t * x + s}ᶜ` using `fun z hz hz' ↦ hz (by`. Simplify using `only [mem_singleton_iff, add_left_inj] at hz' ⊢`.

Conclude with `mul_left_cancel₀ ht hz')`. Conclude with `(hc.continuousAt.continuousWithinAt.tendsto_nhdsWithin hmaps).eventually (h _)`.
-/
theorem comp_affine_eventuallyEq_zero {f : ℂ → ℂ} (h : f =ᶠ[codiscrete ℂ] 0) {t : ℂ} (ht : t ≠ 0)
    (s : ℂ) : (fun z ↦ f (t * z + s)) =ᶠ[codiscrete ℂ] 0 := by
  rw [eventuallyEq_zero_codiscrete_iff] at h ⊢
  intro x
  have hc : Continuous fun z : ℂ ↦ t * z + s := by fun_prop
  have hmaps : MapsTo (fun z : ℂ ↦ t * z + s) {x}ᶜ {t * x + s}ᶜ := fun z hz hz' ↦ hz (by
    simp only [mem_singleton_iff, add_left_inj] at hz' ⊢
    exact mul_left_cancel₀ ht hz')
  exact (hc.continuousAt.continuousWithinAt.tendsto_nhdsWithin hmaps).eventually (h _)

/- English proof (translation)
The claim follows from `fun x ↦ (hf (t * x + s)).comp_analyticAt (g := fun z ↦ t * z + s) (by fun_prop)`.
-/
theorem meromorphic_comp_affine {f : ℂ → ℂ} (hf : Meromorphic f) (t s : ℂ) :
    Meromorphic fun z ↦ f (t * z + s) := fun x ↦
  (hf (t * x + s)).comp_analyticAt (g := fun z ↦ t * z + s) (by fun_prop)

def compAffineSub (t s : ℂ) : meroSubalgebra →ₐ[ℂ] meroSubalgebra where
  toFun f := ⟨fun z ↦ f.1 (t * z + s), meromorphic_comp_affine f.2 t s⟩
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl
  commutes' _ := rfl

def affineComp (t s : ℂ) (ht : t ≠ 0) : MeroField →ₐ[ℂ] MeroField :=
  Ideal.Quotient.liftₐ meroNull ((Ideal.Quotient.mkₐ ℂ meroNull).comp (compAffineSub t s))
    fun f hf ↦ by
      rw [AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk, Ideal.Quotient.eq_zero_iff_mem]
      exact comp_affine_eventuallyEq_zero hf ht s

/- English proof (translation)
Rewrite using `[germ_of hf, germ_of (meromorphic_comp_affine hf t s)]`. Both sides reduce to the same expression.
-/
theorem affineComp_germ (t s : ℂ) (ht : t ≠ 0) {f : ℂ → ℂ} (hf : Meromorphic f) :
    affineComp t s ht (germ f) = germ fun z ↦ f (t * z + s) := by
  rw [germ_of hf, germ_of (meromorphic_comp_affine hf t s)]
  rfl

def rep (u : MeroField) : ℂ → ℂ := (germ_surjective u).choose

/- English proof (translation)
The claim follows from `(germ_surjective u).choose_spec.1`.
-/
theorem meromorphic_rep (u : MeroField) : Meromorphic (rep u) := (germ_surjective u).choose_spec.1

/- English proof (translation)
The claim follows from `(germ_surjective u).choose_spec.2`.
-/
theorem germ_rep (u : MeroField) : germ (rep u) = u := (germ_surjective u).choose_spec.2

/- English proof (translation)
The claim follows from `(germ_eq_germ_iff (meromorphic_rep _) hf).1 (germ_rep _)`.
-/
theorem rep_germ {f : ℂ → ℂ} (hf : Meromorphic f) : rep (germ f) =ᶠ[codiscrete ℂ] f :=
  (germ_eq_germ_iff (meromorphic_rep _) hf).1 (germ_rep _)

def derivFun (u : MeroField) : MeroField := germ (deriv (rep u))

/- English proof (translation)
The claim follows from `germ_congr (meromorphic_rep _).deriv (deriv_eventuallyEq_codiscrete (rep_germ hf))`.
-/
theorem derivFun_germ {f : ℂ → ℂ} (hf : Meromorphic f) : derivFun (germ f) = germ (deriv f) :=
  germ_congr (meromorphic_rep _).deriv (deriv_eventuallyEq_codiscrete (rep_germ hf))

/- English proof (translation)
Take `⟨f, hf, rfl⟩` from `germ_surjective u`. Take `⟨g, hg, rfl⟩` from `germ_surjective v`. Rewrite using `[← germ_add hf hg, derivFun_germ (hf.add hg), derivFun_germ hf, derivFun_germ hg, ← germ_add hf.deriv hg.deriv]`. Apply `germ_congr (hf.add hg).deriv` to reduce the goal to its premises. Use `filter_upwards [eventually_analyticAt hf, eventually_analyticAt hg] with z h1 h2`.

Conclude with `deriv_add h1.differentiableAt h2.differentiableAt`.
-/
theorem derivFun_add (u v : MeroField) : derivFun (u + v) = derivFun u + derivFun v := by
  obtain ⟨f, hf, rfl⟩ := germ_surjective u
  obtain ⟨g, hg, rfl⟩ := germ_surjective v
  rw [← germ_add hf hg, derivFun_germ (hf.add hg), derivFun_germ hf, derivFun_germ hg,
    ← germ_add hf.deriv hg.deriv]
  apply germ_congr (hf.add hg).deriv
  filter_upwards [eventually_analyticAt hf, eventually_analyticAt hg] with z h1 h2
  exact deriv_add h1.differentiableAt h2.differentiableAt

/- English proof (translation)
Take `⟨f, hf, rfl⟩` from `germ_surjective u`. Take `⟨g, hg, rfl⟩` from `germ_surjective v`. Rewrite using `[← germ_mul hf hg, derivFun_germ (hf.mul hg), derivFun_germ hf, derivFun_germ hg, ← germ_mul hf hg.deriv, ← germ_mul hg hf.deriv, ← germ_add (hf.mul hg.deriv) (hg.mul hf.deriv)]`. Apply `germ_congr (hf.mul hg).deriv` to reduce the goal to its premises. Use `filter_upwards [eventually_analyticAt hf, eventually_analyticAt hg] with z h1 h2`.

Rewrite using `[deriv_mul h1.differentiableAt h2.differentiableAt]`. Simplify using `only [Pi.add_apply, Pi.mul_apply]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem derivFun_mul (u v : MeroField) :
    derivFun (u * v) = u * derivFun v + v * derivFun u := by
  obtain ⟨f, hf, rfl⟩ := germ_surjective u
  obtain ⟨g, hg, rfl⟩ := germ_surjective v
  rw [← germ_mul hf hg, derivFun_germ (hf.mul hg), derivFun_germ hf, derivFun_germ hg,
    ← germ_mul hf hg.deriv, ← germ_mul hg hf.deriv, ← germ_add (hf.mul hg.deriv) (hg.mul hf.deriv)]
  apply germ_congr (hf.mul hg).deriv
  filter_upwards [eventually_analyticAt hf, eventually_analyticAt hg] with z h1 h2
  rw [deriv_mul h1.differentiableAt h2.differentiableAt]
  simp only [Pi.add_apply, Pi.mul_apply]
  ring

/- English proof (translation)
Rewrite using `[← germ_const, derivFun_germ (Meromorphic.const c)]`. Establish `: deriv (fun _ : ℂ ↦ c) = 0`. Use function extensionality and compare the values at `z`. Simplify using the standard rewrite rules. Rewrite using `[this, germ_zero]`.
-/
theorem derivFun_algebraMap (c : ℂ) : derivFun (algebraMap ℂ MeroField c) = 0 := by
  rw [← germ_const, derivFun_germ (Meromorphic.const c)]
  have : deriv (fun _ : ℂ ↦ c) = 0 := by
    funext z
    simp
  rw [this, germ_zero]

/- English proof (translation)
Rewrite using `[Algebra.smul_def, derivFun_mul, derivFun_algebraMap, mul_zero, add_zero, Algebra.smul_def]`.
-/
theorem derivFun_smul (c : ℂ) (u : MeroField) : derivFun (c • u) = c • derivFun u := by
  rw [Algebra.smul_def, derivFun_mul, derivFun_algebraMap, mul_zero, add_zero, Algebra.smul_def]

def germDeriv : Derivation ℂ MeroField MeroField :=
  Derivation.mk' { toFun := derivFun, map_add' := derivFun_add, map_smul' := derivFun_smul }
    fun u v ↦ by
      show derivFun (u * v) = u • derivFun v + v • derivFun u
      rw [derivFun_mul, smul_eq_mul, smul_eq_mul]

/- English proof (translation)
The claim follows from `derivFun_germ hf`.
-/
theorem germDeriv_germ {f : ℂ → ℂ} (hf : Meromorphic f) : germDeriv (germ f) = germ (deriv f) :=
  derivFun_germ hf

/- English proof (translation)
Take `⟨f, hf, rfl⟩` from `germ_surjective u`. Rewrite `hu` using `[germDeriv_germ hf, germ_eq_zero_iff hf.deriv]`. Take `⟨x₀, hx₀⟩` from `nonempty_of_mem_codiscrete (eventually_analyticAt hf)`. Establish `hd : deriv f =ᶠ[𝓝 x₀] 0`. Establish `hne : ∀ᶠ z in 𝓝[≠] x₀, deriv f z = 0` using `eventuallyEq_zero_codiscrete_iff.1 hu x₀`.

Establish `hcont : ContinuousAt (deriv f) x₀` using `hx₀.deriv.continuousAt`. Establish `h0 : deriv f x₀ = 0`. Establish `ht : Tendsto (deriv f) (𝓝[≠] x₀) (𝓝 (deriv f x₀))` using `hcont.tendsto.mono_left nhdsWithin_le_nhds`. Establish `hne' : deriv f =ᶠ[𝓝[≠] x₀] fun _ ↦ 0` using `hne`. Conclude with `tendsto_nhds_unique ht (tendsto_const_nhds.congr' hne'.symm)`.

Rewrite using `[← nhdsNE_sup_pure x₀]`. Conclude with `⟨hne, h0⟩`. Take `⟨ε, hε, hball⟩` from `Metric.eventually_nhds_iff_ball.1 ((hx₀.eventually_analyticAt).and hd)`. Establish `hconst : ∀ y ∈ Metric.ball x₀ ε, f x₀ = f y` using `fun y hy ↦ (Metric.isOpen_ball).is_const_of_deriv_eq_zero (convex_ball x₀ ε).isPreconnected (fun z hz ↦ (hball z hz).1.differentiableAt.differentiableWithinAt) (fun z hz ↦ (hball z hz).2) (Metric.mem_ball_self hε) hy`. Use `⟨f x₀, ?_⟩` and prove the remaining obligations.

Rewrite using `[← germ_const, germ_eq_germ_iff hf (Meromorphic.const _), Filter.eventuallyEq_iff_sub]`. Apply `eventuallyEq_zero_codiscrete_of_nhdsNE (hf.sub (Meromorphic.const _)) (x := x₀)` to reduce the goal to its premises. Use `filter_upwards [nhdsWithin_le_nhds (Metric.ball_mem_nhds x₀ hε)] with z hz`. Simplify using `only [Pi.sub_apply]`. Rewrite using `[← hconst z hz, sub_self]`.
-/
theorem exists_eq_algebraMap_of_germDeriv_eq_zero {u : MeroField} (hu : germDeriv u = 0) :
    ∃ c : ℂ, u = algebraMap ℂ MeroField c := by
  obtain ⟨f, hf, rfl⟩ := germ_surjective u
  rw [germDeriv_germ hf, germ_eq_zero_iff hf.deriv] at hu
  obtain ⟨x₀, hx₀⟩ := nonempty_of_mem_codiscrete (eventually_analyticAt hf)
  have hd : deriv f =ᶠ[𝓝 x₀] 0 := by
    have hne : ∀ᶠ z in 𝓝[≠] x₀, deriv f z = 0 := eventuallyEq_zero_codiscrete_iff.1 hu x₀
    have hcont : ContinuousAt (deriv f) x₀ := hx₀.deriv.continuousAt
    have h0 : deriv f x₀ = 0 := by
      have ht : Tendsto (deriv f) (𝓝[≠] x₀) (𝓝 (deriv f x₀)) := hcont.tendsto.mono_left nhdsWithin_le_nhds
      have hne' : deriv f =ᶠ[𝓝[≠] x₀] fun _ ↦ 0 := hne
      exact tendsto_nhds_unique ht (tendsto_const_nhds.congr' hne'.symm)
    rw [← nhdsNE_sup_pure x₀]
    exact ⟨hne, h0⟩
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff_ball.1
    ((hx₀.eventually_analyticAt).and hd)
  have hconst : ∀ y ∈ Metric.ball x₀ ε, f x₀ = f y := fun y hy ↦
    (Metric.isOpen_ball).is_const_of_deriv_eq_zero (convex_ball x₀ ε).isPreconnected
      (fun z hz ↦ (hball z hz).1.differentiableAt.differentiableWithinAt)
      (fun z hz ↦ (hball z hz).2) (Metric.mem_ball_self hε) hy
  refine ⟨f x₀, ?_⟩
  rw [← germ_const, germ_eq_germ_iff hf (Meromorphic.const _), Filter.eventuallyEq_iff_sub]
  apply eventuallyEq_zero_codiscrete_of_nhdsNE (hf.sub (Meromorphic.const _)) (x := x₀)
  filter_upwards [nhdsWithin_le_nhds (Metric.ball_mem_nhds x₀ hε)] with z hz
  simp only [Pi.sub_apply]
  rw [← hconst z hz, sub_self]

end Elliptic
end GroundTheory.Global

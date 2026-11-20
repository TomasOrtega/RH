import Formalism.SharpRestriction.GrowthBounds.RootWeights.WeightComponentsMemInvariant
import Formalism.SharpRestriction.GrowthBounds.RootWeights.HighestWeightDominantHolds

noncomputable section

open Finset

namespace Formalism.MainNotions.G.GLWeightTheory

open Formalism.MainNotions.G Formalism.MainNotions.CovariantDegrees

def raisingFunctional {n : ℕ} (mu : Fin n → ℤ) : ℤ := -∑ c : Fin n, (c.val : ℤ) * mu c

/- English proof (translation)
Unfold `raisingFunctional rootW`. Simplify using `only [Pi.add_apply, Pi.sub_apply, mul_add, mul_sub, Finset.sum_add_distrib, Finset.sum_sub_distrib, Pi.single_apply, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem raising_functional_add_root {n : ℕ} (mu : Fin n → ℤ) (a b : Fin n) :
    raisingFunctional (mu + rootW a b) = raisingFunctional mu + ((b.val : ℤ) - (a.val : ℤ)) := by
  unfold raisingFunctional rootW
  simp only [Pi.add_apply, Pi.sub_apply, mul_add, mul_sub, Finset.sum_add_distrib, Finset.sum_sub_distrib,
    Pi.single_apply, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
  ring

/- English proof (translation)
Use `set H : Module.End K V := ∑ c : Fin n, ((c.val : ℤ) : K) • E c c with hH`. Establish `hwH : ∀ (mu : Fin n → ℤ) (x : V), x ∈ weightSp E mu → H x = (-((raisingFunctional mu : ℤ) : K)) • x`. Introduce `mu x hx`. Rewrite `hx` using `[mem_weightSpace_iff_diagonal_rep]`. Simplify using `only [hH, LinearMap.sum_apply, LinearMap.smul_apply, hx, smul_smul]`.

Rewrite using `[← Finset.sum_smul]`. Use `congr 1`. Unfold `raisingFunctional`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.

Set `P : ℤ → Prop` to `fun z => ∃ mu : Fin n → ℤ, weightSp E mu ≠ ⊥ ∧ raisingFunctional mu = z`. Establish `hfin : {z | P z}.Finite`. Establish `hinj : Function.Injective (fun z : ℤ => (-(z : K)))` using `fun a b h => by simpa using h`. Use `((Module.End.finite_hasEigenvalue H).preimage hinj.injOn).subset ?_` and prove the remaining obligations. Introduce and unpack `z ⟨mu, hmu, rfl⟩`.

Take `⟨x, hx, hx0⟩` from `Submodule.exists_mem_ne_zero_of_ne_bot hmu`. Conclude with `Module.End.hasEigenvalue_of_hasEigenvector ⟨Module.End.mem_eigenspace_iff.2 (hwH mu x hx), hx0⟩`. Establish `hne : ∃ z, P z`. Assume the negation of the conclusion as `hcon`. Establish `hall : ∀ mu : Fin n → ℤ, weightSp E mu = ⊥` using `fun mu => by`.

Assume the negation of the conclusion as `h`. Conclude with `hcon ⟨_, mu, h, rfl⟩`. Establish `htop` using `hE.2.2`. Simplify using `only [hall, iSup_bot] at htop`. Conclude with `bot_ne_top htop`.

Take `⟨bd, hbd⟩` from `hfin.bddAbove`. Take `⟨z, ⟨mu, hmu, rfl⟩, hmax⟩` from `Int.exists_greatest_of_bdd ⟨bd, fun z hz => hbd hz⟩ hne`. Take `⟨v, hv, hv0⟩` from `Submodule.exists_mem_ne_zero_of_ne_bot hmu`. Use `⟨mu, v, hv0, hv, fun a b hab => ?_⟩` and prove the remaining obligations. Establish `hs` using `gl_rep_weight_shift hE hv a b`.

Assume the negation of the conclusion as `hne0`. Establish `hP : P (raisingFunctional (mu + rootW a b))` using `⟨_, fun h => hne0 (by rw [h, Submodule.mem_bot] at hs; exact hs), rfl⟩`. Establish `h1` using `hmax _ hP`. Rewrite `h1` using `[raising_functional_add_root]`. Establish `h2 : (a.val : ℤ) < b.val` using `by exact_mod_cast hab`.

Use linear arithmetic over natural numbers and integers.
-/
theorem exists_highest_weight_vector_findim {n : ℕ} {K V : Type*} [Field K] [CharZero K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] [Nontrivial V] {E : GLOps n K V} (hE : IsGLRep E) :
    ∃ mu v, IsHWV E mu v := by
  classical
  set H : Module.End K V := ∑ c : Fin n, ((c.val : ℤ) : K) • E c c with hH
  have hwH : ∀ (mu : Fin n → ℤ) (x : V), x ∈ weightSp E mu → H x = (-((raisingFunctional mu : ℤ) : K)) • x := by
    intro mu x hx
    rw [mem_weightSpace_iff_diagonal_rep] at hx
    simp only [hH, LinearMap.sum_apply, LinearMap.smul_apply, hx, smul_smul]
    rw [← Finset.sum_smul]
    congr 1
    unfold raisingFunctional
    push_cast
    ring
  let P : ℤ → Prop := fun z => ∃ mu : Fin n → ℤ, weightSp E mu ≠ ⊥ ∧ raisingFunctional mu = z
  have hfin : {z | P z}.Finite := by
    have hinj : Function.Injective (fun z : ℤ => (-(z : K))) := fun a b h => by simpa using h
    refine ((Module.End.finite_hasEigenvalue H).preimage hinj.injOn).subset ?_
    rintro z ⟨mu, hmu, rfl⟩
    obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hmu
    exact Module.End.hasEigenvalue_of_hasEigenvector ⟨Module.End.mem_eigenspace_iff.2 (hwH mu x hx), hx0⟩
  have hne : ∃ z, P z := by
    by_contra hcon
    have hall : ∀ mu : Fin n → ℤ, weightSp E mu = ⊥ := fun mu => by
      by_contra h
      exact hcon ⟨_, mu, h, rfl⟩
    have htop := hE.2.2
    simp only [hall, iSup_bot] at htop
    exact bot_ne_top htop
  obtain ⟨bd, hbd⟩ := hfin.bddAbove
  obtain ⟨z, ⟨mu, hmu, rfl⟩, hmax⟩ := Int.exists_greatest_of_bdd ⟨bd, fun z hz => hbd hz⟩ hne
  obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hmu
  refine ⟨mu, v, hv0, hv, fun a b hab => ?_⟩
  have hs := gl_rep_weight_shift hE hv a b
  by_contra hne0
  have hP : P (raisingFunctional (mu + rootW a b)) := ⟨_, fun h => hne0 (by rw [h, Submodule.mem_bot] at hs; exact hs), rfl⟩
  have h1 := hmax _ hP
  rw [raising_functional_add_root] at h1
  have h2 : (a.val : ℤ) < b.val := by exact_mod_cast hab
  omega

/- English proof (translation)
Establish `key : ∀ (mu : Fin n → ℤ), ∀ y ∈ isoSub E mu, E a b y ∈ isoSub E mu`. Introduce `mu y hy`. Unfold `isoSub at hy ⊢`. Proceed by induction on `hy using Submodule.span_induction with`. Consider the case `mem y hy`.

Take `⟨u, hu, v, hv, rfl⟩` from `hy`. Apply `Submodule.subset_span` to reduce the goal to its premises. Conclude with `⟨E a b * u, (Umon E).mul_mem (Submonoid.subset_closure ⟨(a, b), rfl⟩) hu, v, hv, rfl⟩`. Consider the case `zero => simp`. Consider the case `add x y _ _ hx hy => rw [map_add]`.

Conclude with `Submodule.add_mem _ hx hy`. Consider the case `smul c x _ hx => rw [map_smul]`. Conclude with `Submodule.smul_mem _ c hx`. Establish `hle : (⨆ mu : Fin n → ℤ, isoSub E mu) ≤ (⨆ mu : Fin n → ℤ, isoSub E mu).comap (E a b)` using `iSup_le fun mu y hy => Submodule.mem_comap.2 (Submodule.mem_iSup_of_mem mu (key mu y hy))`. Conclude with `hle hx`.
-/
theorem isotypic_sum_stable {n : ℕ} {K V : Type*} [Field K] [AddCommGroup V] [Module K V] (E : GLOps n K V)
    (a b : Fin n) {x : V} (hx : x ∈ ⨆ mu : Fin n → ℤ, isoSub E mu) : E a b x ∈ ⨆ mu : Fin n → ℤ, isoSub E mu := by
  have key : ∀ (mu : Fin n → ℤ), ∀ y ∈ isoSub E mu, E a b y ∈ isoSub E mu := by
    intro mu y hy
    unfold isoSub at hy ⊢
    induction hy using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨u, hu, v, hv, rfl⟩ := hy
      apply Submodule.subset_span
      exact ⟨E a b * u, (Umon E).mul_mem (Submonoid.subset_closure ⟨(a, b), rfl⟩) hu, v, hv, rfl⟩
    | zero => simp
    | add x y _ _ hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy
    | smul c x _ hx => rw [map_smul]; exact Submodule.smul_mem _ c hx
  have hle : (⨆ mu : Fin n → ℤ, isoSub E mu) ≤ (⨆ mu : Fin n → ℤ, isoSub E mu).comap (E a b) :=
    iSup_le fun mu y hy => Submodule.mem_comap.2 (Submodule.mem_iSup_of_mem mu (key mu y hy))
  exact hle hx

/- English proof (translation)
Take `⟨U', hc, hst⟩` from `h2 K V n E hE (⨆ mu : Fin n → ℤ, isoSub E mu) (fun a b x hx => isotypic_sum_stable E a b hx)`. Establish `hbot : U' = ⊥`. Assume the negation of the conclusion as `hne`. Establish `: Nontrivial U'` using `Submodule.nontrivial_iff_ne_bot.2 hne`. Take `⟨mu, v, hv⟩` from `exists_highest_weight_vector_findim (restricted_isGLRep E U' hst hE)`.

Establish `hv'` using `(restricted_isHWV_iff E U' hst mu v).1 hv`. Establish `h1 : (v : V) ∈ ⨆ mu : Fin n → ℤ, isoSub E mu` using `Submodule.mem_iSup_of_mem mu (Submodule.subset_span ⟨1, (Umon E).one_mem, (v : V), hv', rfl⟩)`. Establish `h3 : (v : V) ∈ (⨆ mu : Fin n → ℤ, isoSub E mu) ⊓ U'` using `⟨h1, v.2⟩`. Rewrite `h3` using `[hc.inf_eq_bot]`. Conclude with `hv'.1 ((Submodule.mem_bot K).1 h3)`.

Use `hc.sup_eq_top` as an intermediate fact. Rewrite `this` using `[hbot, sup_bot_eq]`. Then use the resulting hypothesis.
-/
theorem complete_reducibility_findim (D : Formalism.BasicNotions.D7) (h2 : adm2 D) (K V : Type) [Field K] [CharZero K] [AddCommGroup V]
    [Module K V] [FiniteDimensional K V] (n : ℕ) (E : GLOps n K V) (hE : IsGLRep E) :
    (⨆ mu : Fin n → ℤ, isoSub E mu) = ⊤ := by
  obtain ⟨U', hc, hst⟩ := h2 K V n E hE (⨆ mu : Fin n → ℤ, isoSub E mu)
    (fun a b x hx => isotypic_sum_stable E a b hx)
  have hbot : U' = ⊥ := by
    by_contra hne
    have : Nontrivial U' := Submodule.nontrivial_iff_ne_bot.2 hne
    obtain ⟨mu, v, hv⟩ := exists_highest_weight_vector_findim (restricted_isGLRep E U' hst hE)
    have hv' := (restricted_isHWV_iff E U' hst mu v).1 hv
    have h1 : (v : V) ∈ ⨆ mu : Fin n → ℤ, isoSub E mu :=
      Submodule.mem_iSup_of_mem mu (Submodule.subset_span ⟨1, (Umon E).one_mem, (v : V), hv', rfl⟩)
    have h3 : (v : V) ∈ (⨆ mu : Fin n → ℤ, isoSub E mu) ⊓ U' := ⟨h1, v.2⟩
    rw [hc.inf_eq_bot] at h3
    exact hv'.1 ((Submodule.mem_bot K).1 h3)
  have := hc.sup_eq_top
  rwa [hbot, sup_bot_eq] at this

/- English proof (translation)
Both sides reduce to the same expression.
-/
private theorem restrictStableOperators_apply_coe {n : ℕ} {K V : Type*} [Field K] [AddCommGroup V] [Module K V] (E : GLOps n K V)
    (W : Submodule K V) (h : ∀ a b, ∀ x ∈ W, E a b x ∈ W) (a b : Fin n) (x : W) :
    ((restrictStableOperators E W h a b x : W) : V) = E a b x := rfl

/- English proof (translation)
Rewrite using `[mem_weightSpace_iff_diagonal_rep, mem_weightSpace_iff_diagonal_rep]`. Use `forall_congr' fun a => ?_` and prove the remaining obligations. Rewrite using `[Subtype.ext_iff]`. Conclude with `Iff.rfl`.
-/
private theorem mem_weightSp_restrict_iff {n : ℕ} {K V : Type*} [Field K] [AddCommGroup V] [Module K V] (E : GLOps n K V)
    (W : Submodule K V) (h : ∀ a b, ∀ x ∈ W, E a b x ∈ W) (mu : Fin n → ℤ) (x : W) :
    x ∈ weightSp (restrictStableOperators E W h) mu ↔ (x : V) ∈ weightSp E mu := by
  rw [mem_weightSpace_iff_diagonal_rep, mem_weightSpace_iff_diagonal_rep]
  refine forall_congr' fun a => ?_
  rw [Subtype.ext_iff]
  exact Iff.rfl

/- English proof (translation)
Introduce `k`. Proceed by induction on `k with`. Consider the case `zero`. Introduce `f hk _ _ mu`. Establish `: f = 0` using `Finsupp.card_support_eq_zero.1 (Nat.le_zero.1 hk)`.

Simplify using `[this]`. Consider the case `succ k ih`. Introduce `f hk hw hs mu`. Distinguish the cases in `hmu : f mu = 0`. Rewrite using `[hmu]`.

Conclude with `p.zero_mem`. Distinguish the cases in `hone : f.support ⊆ {mu}`. Establish `hsum : (f.sum fun _ v => v) = f mu`. Rewrite using `[Finsupp.sum, Finset.sum_subset hone (fun x _ hx => by simpa using hx), Finset.sum_singleton]`. Rewrite using `[← hsum]`.

Conclude with `hs`. Choose the witnesses or unpack the hypotheses as in `⟨nu, hnu, hne⟩ : ∃ nu ∈ f.support, nu ≠ mu := by`. Assume the negation of the conclusion as `hc`. Use `push_neg at hc`. Conclude with `hone fun x hx => Finset.mem_singleton.2 (hc x hx)`.

Choose the witnesses or unpack the hypotheses as in `⟨a, ha⟩ : ∃ a, mu a ≠ nu a := by`. Assume the negation of the conclusion as `hc`. Use `push_neg at hc`. Conclude with `hne (funext fun a => (hc a).symm)`. Set `g : (Fin n → ℤ) →₀ V` to `Finsupp.onFinset f.support (fun mu' => (((mu' a : ℤ) : K) - ((nu a : ℤ) : K)) • f mu') (fun mu' hh => by`.

Rewrite using `[Finsupp.mem_support_iff]`. Introduce `h0`. Apply `hh` to reduce the goal to its premises. Rewrite using `[h0, smul_zero])`. Establish `hg : ∀ mu', g mu' = (((mu' a : ℤ) : K) - ((nu a : ℤ) : K)) • f mu'` using `fun mu' => Finsupp.onFinset_apply`.

Establish `hgs : g.support ⊆ f.support.erase nu`. Introduce `x hx`. Rewrite `hx` using `[Finsupp.mem_support_iff, hg]`. Use `Finset.mem_erase.2 ⟨fun hxn => hx (by rw [hxn, sub_self, zero_smul]), ?_⟩` and prove the remaining obligations. Rewrite using `[Finsupp.mem_support_iff]`.

Introduce `h0`. Apply `hx` to reduce the goal to its premises. Rewrite using `[h0, smul_zero]`. Establish `hcard : g.support.card ≤ k`. Use `Finset.card_le_card hgs` as an intermediate fact.

Rewrite `this` using `[Finset.card_erase_of_mem hnu]`. Use linear arithmetic over natural numbers and integers. Establish `hgw : ∀ mu', g mu' ∈ weightSp E mu'` using `fun mu' => by`. Rewrite using `[hg]`. Conclude with `Submodule.smul_mem _ _ (hw mu')`.

Establish `hgsum : (g.sum fun _ v => v) = (E a a - ((nu a : ℤ) : K) • (1 : Module.End K V)) (f.sum fun _ v => v)`. Rewrite using `[Finsupp.onFinset_sum _ (fun _ => rfl), Finsupp.sum, map_sum]`. Use `Finset.sum_congr rfl fun mu' _ => ?_` and prove the remaining obligations. Use `(mem_weightSpace_iff_diagonal_rep E mu' (f mu')).1 (hw mu') a` as an intermediate fact. Rewrite using `[LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply, this, sub_smul]`.

Establish `hgp : (g.sum fun _ v => v) ∈ p`. Rewrite using `[hgsum, LinearMap.sub_apply]`. Use `p.sub_mem (hp a _ hs) ?_` and prove the remaining obligations. Rewrite using `[LinearMap.smul_apply, Module.End.one_apply]`. Conclude with `p.smul_mem _ hs`.

Establish `h1` using `ih g hcard hgw hgp mu`. Rewrite `h1` using `[hg]`. Establish `hc : (((mu a : ℤ) : K) - ((nu a : ℤ) : K)) ≠ 0`. Rewrite using `[sub_ne_zero]`. Conclude with `ha` after adjusting the coercions.

Use `p.smul_mem (((mu a : ℤ) : K) - ((nu a : ℤ) : K))⁻¹ h1` as an intermediate fact. Rewrite `this` using `[smul_smul, inv_mul_cancel₀ hc, one_smul]`. Then use the resulting hypothesis.
-/
private theorem weight_components_mem_of_sum_mem {n : ℕ} {K V : Type*} [Field K] [CharZero K] [AddCommGroup V] [Module K V]
    (E : GLOps n K V) (p : Submodule K V) (hp : ∀ a, ∀ x ∈ p, E a a x ∈ p) :
    ∀ (k : ℕ) (f : (Fin n → ℤ) →₀ V), f.support.card ≤ k → (∀ mu, f mu ∈ weightSp E mu) →
      (f.sum fun _ v => v) ∈ p → ∀ mu, f mu ∈ p := by
  classical
  intro k
  induction k with
  | zero =>
    intro f hk _ _ mu
    have : f = 0 := Finsupp.card_support_eq_zero.1 (Nat.le_zero.1 hk)
    simp [this]
  | succ k ih =>
    intro f hk hw hs mu
    by_cases hmu : f mu = 0
    · rw [hmu]; exact p.zero_mem
    by_cases hone : f.support ⊆ {mu}
    · have hsum : (f.sum fun _ v => v) = f mu := by
        rw [Finsupp.sum, Finset.sum_subset hone (fun x _ hx => by simpa using hx), Finset.sum_singleton]
      rw [← hsum]; exact hs
    obtain ⟨nu, hnu, hne⟩ : ∃ nu ∈ f.support, nu ≠ mu := by
      by_contra hc
      push_neg at hc
      exact hone fun x hx => Finset.mem_singleton.2 (hc x hx)
    obtain ⟨a, ha⟩ : ∃ a, mu a ≠ nu a := by
      by_contra hc
      push_neg at hc
      exact hne (funext fun a => (hc a).symm)
    let g : (Fin n → ℤ) →₀ V := Finsupp.onFinset f.support
      (fun mu' => (((mu' a : ℤ) : K) - ((nu a : ℤ) : K)) • f mu')
      (fun mu' hh => by
        rw [Finsupp.mem_support_iff]
        intro h0; apply hh; rw [h0, smul_zero])
    have hg : ∀ mu', g mu' = (((mu' a : ℤ) : K) - ((nu a : ℤ) : K)) • f mu' := fun mu' => Finsupp.onFinset_apply
    have hgs : g.support ⊆ f.support.erase nu := by
      intro x hx
      rw [Finsupp.mem_support_iff, hg] at hx
      refine Finset.mem_erase.2 ⟨fun hxn => hx (by rw [hxn, sub_self, zero_smul]), ?_⟩
      rw [Finsupp.mem_support_iff]
      intro h0; apply hx; rw [h0, smul_zero]
    have hcard : g.support.card ≤ k := by
      have := Finset.card_le_card hgs
      rw [Finset.card_erase_of_mem hnu] at this
      omega
    have hgw : ∀ mu', g mu' ∈ weightSp E mu' := fun mu' => by
      rw [hg]; exact Submodule.smul_mem _ _ (hw mu')
    have hgsum : (g.sum fun _ v => v) =
        (E a a - ((nu a : ℤ) : K) • (1 : Module.End K V)) (f.sum fun _ v => v) := by
      rw [Finsupp.onFinset_sum _ (fun _ => rfl), Finsupp.sum, map_sum]
      refine Finset.sum_congr rfl fun mu' _ => ?_
      have := (mem_weightSpace_iff_diagonal_rep E mu' (f mu')).1 (hw mu') a
      rw [LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply, this, sub_smul]
    have hgp : (g.sum fun _ v => v) ∈ p := by
      rw [hgsum, LinearMap.sub_apply]
      refine p.sub_mem (hp a _ hs) ?_
      rw [LinearMap.smul_apply, Module.End.one_apply]
      exact p.smul_mem _ hs
    have h1 := ih g hcard hgw hgp mu
    rw [hg] at h1
    have hc : (((mu a : ℤ) : K) - ((nu a : ℤ) : K)) ≠ 0 := by
      rw [sub_ne_zero]; exact_mod_cast ha
    have := p.smul_mem (((mu a : ℤ) : K) - ((nu a : ℤ) : K))⁻¹ h1
    rwa [smul_smul, inv_mul_cancel₀ hc, one_smul] at this

/- English proof (translation)
Rewrite using `[eq_top_iff]`. Introduce and unpack `x -`. Establish `hx : (x : V) ∈ ⨆ mu : Fin n → ℤ, weightSp E mu` using `by rw [hE.2.2]; trivial`. Take `⟨f, hf, hfx⟩` from `(Submodule.mem_iSup_iff_exists_finsupp _ _).1 hx`. Establish `hmem : ∀ mu, f mu ∈ W` using `weight_components_mem_of_sum_mem E W (fun a => h a a) _ f le_rfl hf (by rw [hfx]; exact x.2)`.

Establish `hx' : x = ∑ mu ∈ f.support, (⟨f mu, hmem mu⟩ : W)`. Apply `Subtype.ext` to reduce the goal to its premises. Simplify using `only [Submodule.coe_sum, Submodule.coe_mk]`. Rewrite using `[← hfx, Finsupp.sum]`. Rewrite using `[hx']`.

Conclude with `Submodule.sum_mem _ fun mu _ => Submodule.mem_iSup_of_mem mu ((mem_weightSp_restrict_iff E W h mu _).2 (hf mu))`.
-/
private theorem iSup_weightSp_restrictStableOperators_eq_univ {n : ℕ} {K V : Type*} [Field K] [CharZero K] [AddCommGroup V] [Module K V]
    (E : GLOps n K V) (hE : IsGLRep E) (W : Submodule K V) (h : ∀ a b, ∀ x ∈ W, E a b x ∈ W) :
    (⨆ mu : Fin n → ℤ, weightSp (restrictStableOperators E W h) mu) = ⊤ := by
  classical
  rw [eq_top_iff]
  rintro x -
  have hx : (x : V) ∈ ⨆ mu : Fin n → ℤ, weightSp E mu := by rw [hE.2.2]; trivial
  obtain ⟨f, hf, hfx⟩ := (Submodule.mem_iSup_iff_exists_finsupp _ _).1 hx
  have hmem : ∀ mu, f mu ∈ W :=
    weight_components_mem_of_sum_mem E W (fun a => h a a) _ f le_rfl hf (by rw [hfx]; exact x.2)
  have hx' : x = ∑ mu ∈ f.support, (⟨f mu, hmem mu⟩ : W) := by
    apply Subtype.ext
    simp only [Submodule.coe_sum, Submodule.coe_mk]
    rw [← hfx, Finsupp.sum]
  rw [hx']
  exact Submodule.sum_mem _ fun mu _ => Submodule.mem_iSup_of_mem mu ((mem_weightSp_restrict_iff E W h mu _).2 (hf mu))

/- English proof (translation)
Introduce `x`. Take `⟨U, hU, hxU, hUs⟩` from `hE.2.1 x`. Use `haveI := hU`. Use `⟨U.comap W.subtype, ?_, hxU, fun a b y hy => hUs a b _ hy⟩` and prove the remaining obligations. Set `j : U.comap W.subtype →ₗ[K] U` to `{ toFun := fun y => ⟨((y : W) : V), y.2⟩ map_add' := fun _ _ => rfl map_smul' := fun _ _ => rfl }`.

Conclude with `FiniteDimensional.of_injective j (fun y z hyz => by`. Apply `Subtype.ext` to reduce the goal to its premises. Apply `Subtype.ext` to reduce the goal to its premises. Simplify `congrArg Subtype.val hyz)` using `[j]`.
-/
private theorem restrictStableOperators_locallyFinite {n : ℕ} {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    (E : GLOps n K V) (hE : IsGLRep E) (W : Submodule K V) (h : ∀ a b, ∀ x ∈ W, E a b x ∈ W) :
    ∀ x : W, ∃ U : Submodule K W, FiniteDimensional K U ∧ x ∈ U ∧
      ∀ a b, ∀ y ∈ U, restrictStableOperators E W h a b y ∈ U := by
  intro x
  obtain ⟨U, hU, hxU, hUs⟩ := hE.2.1 x
  haveI := hU
  refine ⟨U.comap W.subtype, ?_, hxU, fun a b y hy => hUs a b _ hy⟩
  let j : U.comap W.subtype →ₗ[K] U :=
    { toFun := fun y => ⟨((y : W) : V), y.2⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  exact FiniteDimensional.of_injective j (fun y z hyz => by
    apply Subtype.ext; apply Subtype.ext
    simpa [j] using congrArg Subtype.val hyz)

/- English proof (translation)
Introduce `a b c d`. Use extensionality with `x`. Use `LinearMap.congr_fun (hE.1 a b c d) (x : V)` as an intermediate fact. Apply the tactic sequence `split_ifs at this ⊢ <;> simpa [restrictStableOperators_apply_coe] using this`.
-/
private theorem restrictStableOperators_commutator {n : ℕ} {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    (E : GLOps n K V) (hE : IsGLRep E) (W : Submodule K V) (h : ∀ a b, ∀ x ∈ W, E a b x ∈ W) :
    ∀ a b c d, restrictStableOperators E W h a b * restrictStableOperators E W h c d - restrictStableOperators E W h c d * restrictStableOperators E W h a b =
      (if b = c then restrictStableOperators E W h a d else 0) - (if d = a then restrictStableOperators E W h c b else 0) := by
  intro a b c d
  ext x
  have := LinearMap.congr_fun (hE.1 a b c d) (x : V)
  split_ifs at this ⊢ <;> simpa [restrictStableOperators_apply_coe] using this

/- English proof (translation)
Assemble the required witnesses or components as `⟨restrictStableOperators_commutator E hE W h, restrictStableOperators_locallyFinite E hE W h, iSup_weightSp_restrictStableOperators_eq_univ E hE W h⟩`.
-/
private theorem isGLRep_restrictStableOperators {n : ℕ} {K V : Type*} [Field K] [CharZero K] [AddCommGroup V] [Module K V]
    (E : GLOps n K V) (hE : IsGLRep E) (W : Submodule K V) (h : ∀ a b, ∀ x ∈ W, E a b x ∈ W) :
    IsGLRep (restrictStableOperators E W h) :=
  ⟨restrictStableOperators_commutator E hE W h, restrictStableOperators_locallyFinite E hE W h, iSup_weightSp_restrictStableOperators_eq_univ E hE W h⟩

/- English proof (translation)
Unfold `Umon at hu`. Proceed by induction on `hu using Submonoid.closure_induction with`. Consider the case `mem x hx`. Take `⟨⟨a, b⟩, rfl⟩` from `hx`. Conclude with `⟨E a b, Submonoid.subset_closure ⟨(a, b), rfl⟩, fun y => rfl⟩`.

Consider the case `one => exact ⟨1, (Umon E).one_mem, fun y => rfl⟩`. Consider the case `mul x y _ _ hx hy`. Take `⟨x', hx', hx''⟩` from `hx`. Take `⟨y', hy', hy''⟩` from `hy`. Use `⟨x' * y', (Umon E).mul_mem hx' hy', fun z => ?_⟩` and prove the remaining obligations.

Use `show ((x (y z) : W) : V) = x' (y' z)`. Rewrite using `[hx'', hy'']`.
-/
private theorem exists_Umon_of_mem_Umon_restrict {n : ℕ} {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    (E : GLOps n K V) (W : Submodule K V) (h : ∀ a b, ∀ x ∈ W, E a b x ∈ W)
    (u : Module.End K W) (hu : u ∈ Umon (restrictStableOperators E W h)) :
    ∃ u' ∈ Umon E, ∀ y : W, ((u y : W) : V) = u' y := by
  unfold Umon at hu
  induction hu using Submonoid.closure_induction with
  | mem x hx =>
    obtain ⟨⟨a, b⟩, rfl⟩ := hx
    exact ⟨E a b, Submonoid.subset_closure ⟨(a, b), rfl⟩, fun y => rfl⟩
  | one => exact ⟨1, (Umon E).one_mem, fun y => rfl⟩
  | mul x y _ _ hx hy =>
    obtain ⟨x', hx', hx''⟩ := hx
    obtain ⟨y', hy', hy''⟩ := hy
    refine ⟨x' * y', (Umon E).mul_mem hx' hy', fun z => ?_⟩
    show ((x (y z) : W) : V) = x' (y' z)
    rw [hx'', hy'']

/- English proof (translation)
Unfold `isoSub at hx ⊢`. Proceed by induction on `hx using Submodule.span_induction with`. Consider the case `mem y hy`. Take `⟨u, hu, v, hv, rfl⟩` from `hy`. Take `⟨u', hu', hu''⟩` from `exists_Umon_of_mem_Umon_restrict E W h u hu`.

Apply `Submodule.subset_span` to reduce the goal to its premises. Use `⟨u', hu', (v : V), ⟨fun h0 => hv.1 (by ext; simpa using h0), (mem_weightSp_restrict_iff E W h mu v).1 hv.2.1, fun a b hab => ?_⟩, hu'' v⟩` and prove the remaining obligations. Use `congrArg Subtype.val (hv.2.2 a b hab)` as an intermediate fact. Simplify `this` using `[restrictStableOperators_apply_coe]`. Consider the case `zero => simp`.

Consider the case `add x y _ _ hx hy => rw [Submodule.coe_add]`. Conclude with `Submodule.add_mem _ hx hy`. Consider the case `smul c x _ hx => rw [Submodule.coe_smul]`. Conclude with `Submodule.smul_mem _ c hx`.
-/
private theorem coe_mem_isoSub_of_mem_isoSub_restrict {n : ℕ} {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    (E : GLOps n K V) (W : Submodule K V) (h : ∀ a b, ∀ x ∈ W, E a b x ∈ W)
    (mu : Fin n → ℤ) (x : W) (hx : x ∈ isoSub (restrictStableOperators E W h) mu) : (x : V) ∈ isoSub E mu := by
  unfold isoSub at hx ⊢
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨u, hu, v, hv, rfl⟩ := hy
    obtain ⟨u', hu', hu''⟩ := exists_Umon_of_mem_Umon_restrict E W h u hu
    apply Submodule.subset_span
    refine ⟨u', hu', (v : V), ⟨fun h0 => hv.1 (by ext; simpa using h0), (mem_weightSp_restrict_iff E W h mu v).1 hv.2.1,
      fun a b hab => ?_⟩, hu'' v⟩
    have := congrArg Subtype.val (hv.2.2 a b hab)
    simpa [restrictStableOperators_apply_coe] using this
  | zero => simp
  | add x y _ _ hx hy => rw [Submodule.coe_add]; exact Submodule.add_mem _ hx hy
  | smul c x _ hx => rw [Submodule.coe_smul]; exact Submodule.smul_mem _ c hx

/- English proof (translation)
Proceed by induction on `k generalizing x with`. Consider the case `zero => rfl`. Consider the case `succ k ih`. Rewrite using `[pow_succ, pow_succ]`. Conclude with `ih _`.
-/
private theorem restrictStableOperators_pow_apply_coe {n : ℕ} {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    (E : GLOps n K V) (W : Submodule K V) (h : ∀ a b, ∀ x ∈ W, E a b x ∈ W) (a b : Fin n) (k : ℕ) (x : W) :
    ((((restrictStableOperators E W h a b) ^ k) x : W) : V) = ((E a b) ^ k) x := by
  induction k generalizing x with
  | zero => rfl
  | succ k ih =>
    rw [pow_succ, pow_succ]
    exact ih _

/- English proof (translation)
Proceed by induction on `l generalizing x with`. Consider the case `nil => rfl`. Consider the case `cons j l ih`. Rewrite using `[List.map_cons, List.prod_cons, List.map_cons, List.prod_cons]`. Use `show ((((restrictStableOperators E W h a a - (j : K) • (1 : Module.End K W)) (((l.map fun j : ℕ => restrictStableOperators E W h a a - (j : K) • (1 : Module.End K W)).prod) x)) : W) : V) = (E a a - (j : K) • (1 : Module.End K V)) (((l.map fun j : ℕ => E a a - (j : K) • (1 : Modul …`.

Rewrite using `[← ih]`. Simplify using `[restrictStableOperators_apply_coe]`.
-/
private theorem restrictStableOperators_list_prod_sub_apply_coe {n : ℕ} {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    (E : GLOps n K V) (W : Submodule K V) (h : ∀ a b, ∀ x ∈ W, E a b x ∈ W) (a : Fin n) (l : List ℕ) (x : W) :
    ((((l.map fun j : ℕ => restrictStableOperators E W h a a - (j : K) • (1 : Module.End K W)).prod) x : W) : V) =
      ((l.map fun j : ℕ => E a a - (j : K) • (1 : Module.End K V)).prod) x := by
  induction l generalizing x with
  | nil => rfl
  | cons j l ih =>
    rw [List.map_cons, List.prod_cons, List.map_cons, List.prod_cons]
    show ((((restrictStableOperators E W h a a - (j : K) • (1 : Module.End K W))
        (((l.map fun j : ℕ => restrictStableOperators E W h a a - (j : K) • (1 : Module.End K W)).prod) x)) : W) : V) =
      (E a a - (j : K) • (1 : Module.End K V)) (((l.map fun j : ℕ => E a a - (j : K) • (1 : Module.End K V)).prod) x)
    rw [← ih]
    simp [restrictStableOperators_apply_coe]

/- English proof (translation)
Introduce `K V _ _ _ _ n E hE`. Rewrite using `[eq_top_iff]`. Introduce `x _`. Take `⟨U, hU, hxU, hUs⟩` from `hE.2.1 x`. Use `haveI := hU`.

Establish `hrep` using `isGLRep_restrictStableOperators E hE U hUs`. Establish `hcr` using `complete_reducibility_findim D h2 K U n (restrictStableOperators E U hUs) hrep`. Establish `hx' : (⟨x, hxU⟩ : U) ∈ ⨆ mu : Fin n → ℤ, isoSub (restrictStableOperators E U hUs) mu` using `by rw [hcr]; trivial`. Establish `key : (⨆ mu : Fin n → ℤ, isoSub (restrictStableOperators E U hUs) mu) ≤ (⨆ mu : Fin n → ℤ, isoSub E mu).comap U.subtype` using `iSup_le fun mu y hy => Submodule.mem_comap.2 (Submodule.mem_iSup_of_mem mu (coe_mem_isoSub_of_mem_isoSub_restrict E U hUs mu y hy))`. Conclude with `key hx'`.
-/
theorem complete_reducibility_of_semisimple (D : Formalism.BasicNotions.D7) (h2 : adm2 D) : CompleteReducibilityIsotypic := by
  intro K V _ _ _ _ n E hE
  rw [eq_top_iff]
  intro x _
  obtain ⟨U, hU, hxU, hUs⟩ := hE.2.1 x
  haveI := hU
  have hrep := isGLRep_restrictStableOperators E hE U hUs
  have hcr := complete_reducibility_findim D h2 K U n (restrictStableOperators E U hUs) hrep
  have hx' : (⟨x, hxU⟩ : U) ∈ ⨆ mu : Fin n → ℤ, isoSub (restrictStableOperators E U hUs) mu := by rw [hcr]; trivial
  have key : (⨆ mu : Fin n → ℤ, isoSub (restrictStableOperators E U hUs) mu) ≤
      (⨆ mu : Fin n → ℤ, isoSub E mu).comap U.subtype :=
    iSup_le fun mu y hy => Submodule.mem_comap.2 (Submodule.mem_iSup_of_mem mu (coe_mem_isoSub_of_mem_isoSub_restrict E U hUs mu y hy))
  exact key hx'

/- English proof (translation)
Introduce `K V _ _ _ _ n E hE W h`. Establish `hrep` using `isGLRep_restrictStableOperators E hE W h`. Establish `hcr : (⨆ mu : Fin n → ℤ, isoSub (restrictStableOperators E W h) mu) = ⊤` using `hCR K W n (restrictStableOperators E W h) hrep`. Establish `hstab : ∀ lam (e : Module.End K V), IsIsoProj E lam e → ∀ x ∈ W, e x ∈ W`. Introduce `lam e he x hx`.

Establish `hx' : (⟨x, hx⟩ : W) ∈ ⨆ mu : Fin n → ℤ, isoSub (restrictStableOperators E W h) mu` using `by rw [hcr]; trivial`. Establish `key : (⨆ mu : Fin n → ℤ, isoSub (restrictStableOperators E W h) mu) ≤ (W.comap e).comap W.subtype`. Use `iSup_le fun mu y hy => ?_` and prove the remaining obligations. Rewrite using `[Submodule.mem_comap, Submodule.mem_comap, Submodule.subtype_apply]`. Distinguish the cases in `hm : mu = lam`.

Substitute `hm` using the available equality. Rewrite using `[he.1 _ (coe_mem_isoSub_of_mem_isoSub_restrict E W h _ y hy)]`. Conclude with `y.2`. Rewrite using `[he.2 mu hm _ (coe_mem_isoSub_of_mem_isoSub_restrict E W h _ y hy)]`. Conclude with `W.zero_mem`.

Conclude with `key hx'`. Use `⟨hrep, fun mu x => mem_weightSp_restrict_iff E W h mu x, ?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `a b k x`. Unfold `divPowE`. Rewrite using `[LinearMap.smul_apply, LinearMap.smul_apply, Submodule.coe_smul, restrictStableOperators_pow_apply_coe]`.

Introduce `a k x`. Unfold `binomE`. Rewrite using `[LinearMap.smul_apply, LinearMap.smul_apply, Submodule.coe_smul, restrictStableOperators_list_prod_sub_apply_coe]`. Introduce `lam e he`. Use `⟨e.restrict (hstab lam e he), ⟨fun x hx => ?_, fun mu hm x hx => ?_⟩, fun x => rfl⟩` and prove the remaining obligations.

Apply `Subtype.ext show e (x : V) = x` to reduce the goal to its premises. Conclude with `he.1 _ (coe_mem_isoSub_of_mem_isoSub_restrict E W h _ x hx)`. Apply `Subtype.ext show e (x : V) = 0` to reduce the goal to its premises. Conclude with `he.2 mu hm _ (coe_mem_isoSub_of_mem_isoSub_restrict E W h _ x hx)`. Introduce `lam e he hno x hx`.

Establish `hx' : (⟨x, hx⟩ : W) ∈ ⨆ mu : Fin n → ℤ, isoSub (restrictStableOperators E W h) mu` using `by rw [hcr]; trivial`. Establish `key : (⨆ mu : Fin n → ℤ, isoSub (restrictStableOperators E W h) mu) ≤ (LinearMap.ker e).comap W.subtype`. Use `iSup_le fun mu y hy => ?_` and prove the remaining obligations. Rewrite using `[Submodule.mem_comap, LinearMap.mem_ker, Submodule.subtype_apply]`. Distinguish the cases in `hm : mu = lam`.

Substitute `hm` using the available equality. Establish `hbot : isoSub (restrictStableOperators E W h) mu = ⊥`. Unfold `isoSub`. Rewrite using `[Submodule.span_eq_bot]`. Introduce and unpack `_ ⟨u, _, v, hv, rfl⟩`.

Conclude with `absurd ⟨v, hv⟩ hno`. Rewrite `hy` using `[hbot, Submodule.mem_bot]`. Rewrite using `[hy]`. Simplify using the standard rewrite rules. Conclude with `he.2 mu hm _ (coe_mem_isoSub_of_mem_isoSub_restrict E W h _ y hy)`.

Conclude with `key hx'`.
-/
theorem subrep_restriction_of_reducibility (hCR : CompleteReducibilityIsotypic) : SubrepRestrictionRep := by
  intro K V _ _ _ _ n E hE W h
  have hrep := isGLRep_restrictStableOperators E hE W h
  have hcr : (⨆ mu : Fin n → ℤ, isoSub (restrictStableOperators E W h) mu) = ⊤ := hCR K W n (restrictStableOperators E W h) hrep
  have hstab : ∀ lam (e : Module.End K V), IsIsoProj E lam e → ∀ x ∈ W, e x ∈ W := by
    intro lam e he x hx
    have hx' : (⟨x, hx⟩ : W) ∈ ⨆ mu : Fin n → ℤ, isoSub (restrictStableOperators E W h) mu := by rw [hcr]; trivial
    have key : (⨆ mu : Fin n → ℤ, isoSub (restrictStableOperators E W h) mu) ≤ (W.comap e).comap W.subtype := by
      refine iSup_le fun mu y hy => ?_
      rw [Submodule.mem_comap, Submodule.mem_comap, Submodule.subtype_apply]
      by_cases hm : mu = lam
      · subst hm
        rw [he.1 _ (coe_mem_isoSub_of_mem_isoSub_restrict E W h _ y hy)]
        exact y.2
      · rw [he.2 mu hm _ (coe_mem_isoSub_of_mem_isoSub_restrict E W h _ y hy)]
        exact W.zero_mem
    exact key hx'
  refine ⟨hrep, fun mu x => mem_weightSp_restrict_iff E W h mu x, ?_, ?_, ?_, ?_⟩
  · intro a b k x
    unfold divPowE
    rw [LinearMap.smul_apply, LinearMap.smul_apply, Submodule.coe_smul, restrictStableOperators_pow_apply_coe]
  · intro a k x
    unfold binomE
    rw [LinearMap.smul_apply, LinearMap.smul_apply, Submodule.coe_smul, restrictStableOperators_list_prod_sub_apply_coe]
  · intro lam e he
    refine ⟨e.restrict (hstab lam e he), ⟨fun x hx => ?_, fun mu hm x hx => ?_⟩, fun x => rfl⟩
    · apply Subtype.ext
      show e (x : V) = x
      exact he.1 _ (coe_mem_isoSub_of_mem_isoSub_restrict E W h _ x hx)
    · apply Subtype.ext
      show e (x : V) = 0
      exact he.2 mu hm _ (coe_mem_isoSub_of_mem_isoSub_restrict E W h _ x hx)
  · intro lam e he hno x hx
    have hx' : (⟨x, hx⟩ : W) ∈ ⨆ mu : Fin n → ℤ, isoSub (restrictStableOperators E W h) mu := by rw [hcr]; trivial
    have key : (⨆ mu : Fin n → ℤ, isoSub (restrictStableOperators E W h) mu) ≤ (LinearMap.ker e).comap W.subtype := by
      refine iSup_le fun mu y hy => ?_
      rw [Submodule.mem_comap, LinearMap.mem_ker, Submodule.subtype_apply]
      by_cases hm : mu = lam
      · subst hm
        have hbot : isoSub (restrictStableOperators E W h) mu = ⊥ := by
          unfold isoSub
          rw [Submodule.span_eq_bot]
          rintro _ ⟨u, _, v, hv, rfl⟩
          exact absurd ⟨v, hv⟩ hno
        rw [hbot, Submodule.mem_bot] at hy
        rw [hy]
        simp
      · exact he.2 mu hm _ (coe_mem_isoSub_of_mem_isoSub_restrict E W h _ y hy)
    exact key hx'

end Formalism.MainNotions.G.GLWeightTheory

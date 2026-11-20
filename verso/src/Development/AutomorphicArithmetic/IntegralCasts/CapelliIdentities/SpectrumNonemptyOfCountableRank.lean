import Mathlib

open Polynomial in
/- English proof (translation)
Assume the negation of the conclusion as `hne`. Establish `hunit : ∀ a : ℂ, IsUnit (T - algebraMap ℂ (Module.End ℂ V) a)` using `fun a => by`. Establish `h : a ∉ spectrum ℂ T` using `fun h => hne ⟨a, h⟩`. Rewrite `h` using `[spectrum.notMem_iff]`. Conclude with `IsUnit.sub_iff.mp h`.

Establish `hR : ∀ a : ℂ, ∃ R : Module.End ℂ V, (T - algebraMap ℂ (Module.End ℂ V) a) * R = 1` using `fun a => (hunit a).exists_right_inv`. Use `choose R hR using hR`. Take `⟨v, hv⟩` from `exists_ne (0 : V)`. Establish `hdep : ¬ LinearIndependent ℂ (fun a : ℂ => R a v)`. Introduce `hli`.

Establish `h1` using `hli.cardinal_le_rank`. Rewrite `h1` using `[Cardinal.mk_complex]`. Conclude with `absurd (h1.trans hV) (not_le.mpr Cardinal.aleph0_lt_continuum)`. Rewrite `hdep` using `[linearIndependent_iff']`. Use `push_neg at hdep`.

Take `⟨s, m, hm, i, hi, hmi⟩` from `hdep`. Set `q : ℂ → ℂ[X]` to `fun a => ∏ j ∈ s.erase a, (X - C j)`. Set `p : ℂ[X]` to `∑ a ∈ s, C (m a) * q a`. Establish `key : ∀ a ∈ s, aeval T (∏ j ∈ s, (X - C j)) * R a = aeval T (q a)`. Introduce `a ha`.

Rewrite using `[← Finset.prod_erase_mul s _ ha, map_mul, mul_assoc]`. Establish `: aeval T (X - C a) = T - algebraMap ℂ (Module.End ℂ V) a` using `by simp`. Rewrite using `[this, hR, mul_one]`. Establish `hp : aeval T p v = 0`. Establish `h1` using `congrArg (aeval T (∏ j ∈ s, (X - C j))) hm`.

Rewrite `h1` using `[map_zero, map_sum]`. Rewrite using `[← h1]`. Simplify using `only [p, map_sum, LinearMap.sum_apply]`. Use `Finset.sum_congr rfl fun a ha => ?_` and prove the remaining obligations. Rewrite using `[map_mul, aeval_C, ← key a ha, map_smul]`.

Simplify using `[Module.End.mul_apply, Module.algebraMap_end_apply]`. Establish `hp0 : p ≠ 0`. Introduce `h0`. Establish `h1 : eval i p = m i * ∏ j ∈ s.erase i, (i - j)`. Simplify using `only [p, eval_finset_sum, eval_mul, eval_C]`.

Rewrite using `[Finset.sum_eq_single_of_mem i hi]`. Simplify using `[q, eval_prod]`. Introduce `b hb hbi`. Establish `: eval i (q b) = 0`. Simplify using `only [q, eval_prod]`.

Use `Finset.prod_eq_zero (Finset.mem_erase.mpr ⟨hbi.symm, hi⟩) (by simp)` and prove the remaining obligations. Rewrite using `[this, mul_zero]`. Rewrite `h1` using `[h0, eval_zero]`. Establish `h2 : ∏ j ∈ s.erase i, (i - j) ≠ 0` using `Finset.prod_ne_zero_iff.mpr fun j hj => sub_ne_zero.mpr (Finset.ne_of_mem_erase hj).symm`. Conclude with `(mul_ne_zero hmi h2) h1.symm`.

Establish `hnu : ¬ IsUnit (aeval T p)`. Introduce `hu`. Establish `hinj` using `((Module.End.isUnit_iff _).mp hu).injective`. Conclude with `hv (hinj (by rw [hp, map_zero]))`. Establish `hprod` using `(IsAlgClosed.splits p).eq_prod_roots`.

Establish `lead_ne` using `leadingCoeff_ne_zero.mpr hp0`. Establish `lead_unit : IsUnit (algebraMap ℂ (Module.End ℂ V) p.leadingCoeff)` using `(Units.map (algebraMap ℂ (Module.End ℂ V)).toMonoidHom (Units.mk0 _ lead_ne)).isUnit`. Rewrite `hnu` using `[hprod, aeval_mul, ((Commute.all _ _).map (aeval T : ℂ[X] →ₐ[ℂ] _)).isUnit_mul_iff, aeval_C]`. Take `⟨k, hk, -⟩` from `spectrum.exists_mem_of_not_isUnit_aeval_prod (not_and.mp hnu lead_unit)`. Conclude with `hne ⟨k, hk⟩`.
-/
private lemma spectrum_nonempty_of_countable_rank {V : Type} [AddCommGroup V] [_root_.Module ℂ V]
    [Nontrivial V] (hV : Module.rank ℂ V ≤ Cardinal.aleph0) (T : Module.End ℂ V) :
    (spectrum ℂ T).Nonempty := by
  classical
  by_contra hne
  have hunit : ∀ a : ℂ, IsUnit (T - algebraMap ℂ (Module.End ℂ V) a) := fun a => by
    have h : a ∉ spectrum ℂ T := fun h => hne ⟨a, h⟩
    rw [spectrum.notMem_iff] at h
    exact IsUnit.sub_iff.mp h
  have hR : ∀ a : ℂ, ∃ R : Module.End ℂ V, (T - algebraMap ℂ (Module.End ℂ V) a) * R = 1 :=
    fun a => (hunit a).exists_right_inv
  choose R hR using hR
  obtain ⟨v, hv⟩ := exists_ne (0 : V)
  have hdep : ¬ LinearIndependent ℂ (fun a : ℂ => R a v) := by
    intro hli
    have h1 := hli.cardinal_le_rank
    rw [Cardinal.mk_complex] at h1
    exact absurd (h1.trans hV) (not_le.mpr Cardinal.aleph0_lt_continuum)
  rw [linearIndependent_iff'] at hdep
  push_neg at hdep
  obtain ⟨s, m, hm, i, hi, hmi⟩ := hdep
  let q : ℂ → ℂ[X] := fun a => ∏ j ∈ s.erase a, (X - C j)
  let p : ℂ[X] := ∑ a ∈ s, C (m a) * q a
  have key : ∀ a ∈ s, aeval T (∏ j ∈ s, (X - C j)) * R a = aeval T (q a) := by
    intro a ha
    rw [← Finset.prod_erase_mul s _ ha, map_mul, mul_assoc]
    have : aeval T (X - C a) = T - algebraMap ℂ (Module.End ℂ V) a := by simp
    rw [this, hR, mul_one]
  have hp : aeval T p v = 0 := by
    have h1 := congrArg (aeval T (∏ j ∈ s, (X - C j))) hm
    rw [map_zero, map_sum] at h1
    rw [← h1]
    simp only [p, map_sum, LinearMap.sum_apply]
    refine Finset.sum_congr rfl fun a ha => ?_
    rw [map_mul, aeval_C, ← key a ha, map_smul]
    simp [Module.End.mul_apply, Module.algebraMap_end_apply]
  have hp0 : p ≠ 0 := by
    intro h0
    have h1 : eval i p = m i * ∏ j ∈ s.erase i, (i - j) := by
      simp only [p, eval_finset_sum, eval_mul, eval_C]
      rw [Finset.sum_eq_single_of_mem i hi]
      · simp [q, eval_prod]
      · intro b hb hbi
        have : eval i (q b) = 0 := by
          simp only [q, eval_prod]
          refine Finset.prod_eq_zero (Finset.mem_erase.mpr ⟨hbi.symm, hi⟩) (by simp)
        rw [this, mul_zero]
    rw [h0, eval_zero] at h1
    have h2 : ∏ j ∈ s.erase i, (i - j) ≠ 0 :=
      Finset.prod_ne_zero_iff.mpr fun j hj => sub_ne_zero.mpr (Finset.ne_of_mem_erase hj).symm
    exact (mul_ne_zero hmi h2) h1.symm
  have hnu : ¬ IsUnit (aeval T p) := by
    intro hu
    have hinj := ((Module.End.isUnit_iff _).mp hu).injective
    exact hv (hinj (by rw [hp, map_zero]))
  have hprod := (IsAlgClosed.splits p).eq_prod_roots
  have lead_ne := leadingCoeff_ne_zero.mpr hp0
  have lead_unit : IsUnit (algebraMap ℂ (Module.End ℂ V) p.leadingCoeff) :=
    (Units.map (algebraMap ℂ (Module.End ℂ V)).toMonoidHom (Units.mk0 _ lead_ne)).isUnit
  rw [hprod, aeval_mul, ((Commute.all _ _).map (aeval T : ℂ[X] →ₐ[ℂ] _)).isUnit_mul_iff,
    aeval_C] at hnu
  obtain ⟨k, hk, -⟩ := spectrum.exists_mem_of_not_isUnit_aeval_prod (not_and.mp hnu lead_unit)
  exact hne ⟨k, hk⟩

/- English proof (translation)
Introduce `V _ _ _ hV B hB f s`. Establish `hsc : ∀ (c : ℂ) (x : V), c • x = (algebraMap ℂ B c) • x` using `fun c x => by`. Express the relevant statement in the definitionally equal form `c • x = ((algebraMap ℂ (Module.End ℂ V) c : Module.End ℂ V)) x`. Simplify using `[Module.algebraMap_end_apply]`. Establish `hbc : ∀ (b : B) (c : ℂ) (x : V), b • (c • x) = c • (b • x)` using `fun b c x => (b : Module.End ℂ V).map_smul c x`.

Use `haveI hsimple : IsSimpleModule B V := { exists_pair_ne := ⟨⊥, ⊤, bot_ne_top⟩ eq_bot_or_eq_top := fun N => by`. Set `N' : Submodule ℂ V` to `{ carrier := N add_mem' := fun h1 h2 => N.add_mem h1 h2 zero_mem' := N.zero_mem smul_mem' := fun c x hx => by`. Rewrite using `[hsc]`. Conclude with `N.smul_mem _ hx }`. Break down `hB N' (fun b hb x hx => N.smul_mem (⟨b, hb⟩ : B) hx) with h | h` into its components or cases.

Use `left`. Rewrite using `[eq_bot_iff]`. Introduce `x hx`. Establish `: x ∈ N'` using `hx`. Rewrite `this` using `[h]`.

Simplify using `using this`. Use `right`. Rewrite using `[eq_top_iff]`. Introduce `x _`. Establish `: x ∈ N'` using `by rw [h]; trivial`.

Conclude with `this }`. Establish `hscal : ∀ d : Module.End B V, ∃ a : ℂ, ∀ x, d x = a • x`. Introduce `d`. Set `T : Module.End ℂ V` to `{ toFun := d map_add' := d.map_add map_smul' := fun c x => by`. Simplify using `only [RingHom.id_apply]`.

Rewrite using `[hsc, d.map_smul, ← hsc] }`. Take `⟨a, ha⟩` from `spectrum_nonempty_of_countable_rank hV T`. Set `e : V →ₗ[B] V` to `{ toFun := fun x => a • x - d x map_add' := fun x y => by`. Rewrite using `[smul_add, d.map_add]`. Normalize the expressions using the abelian group laws.

Use the proof step `map_smul' := fun b x => by`. Simplify using `only [RingHom.id_apply]`. Rewrite using `[d.map_smul, smul_sub, hbc] }`. Break down `LinearMap.bijective_or_eq_zero e with hb | h0` into its components or cases. It suffices to derive a contradiction.

Apply `ha` to reduce the goal to its premises. Rewrite using `[spectrum.mem_resolventSet_iff, Module.End.isUnit_iff]`. Establish `hfe : ⇑(algebraMap ℂ (Module.End ℂ V) a - T) = ⇑e`. Use function extensionality and compare the values at `x`. Simplify using `[T, e, Module.algebraMap_end_apply]`.

Rewrite using `[hfe]`. Conclude with `hb`. Use `⟨a, fun x => ?_⟩` and prove the remaining obligations. Establish `: a • x - d x = 0` using `congrArg (fun g : V →ₗ[B] V => g x) h0`. Conclude with `(sub_eq_zero.mp this).symm`.

Set `F : Module.End (Module.End B V) V` to `{ toFun := f map_add' := f.map_add map_smul' := fun d x => by`. Take `⟨a, ha⟩` from `hscal d`. Simplify using `only [RingHom.id_apply, Module.End.smul_def]`. Rewrite using `[ha, ha, f.map_smul] }`. Take `⟨r, hr⟩` from `jacobson_density F s`.

Conclude with `⟨r, r.2, fun m hm => hr m hm⟩`.
-/
theorem UpperTheory.Reformulated.B.DYhd6.main :
    ∀ {V : Type} [inst : AddCommGroup V] [inst_1 : _root_.Module ℂ V] [Nontrivial V],
      Module.rank ℂ V ≤ Cardinal.aleph0 →
        ∀ (B : Subalgebra ℂ (Module.End ℂ V)),
          (∀ (N : Submodule ℂ V), (∀ b ∈ B, ∀ x ∈ N, (b : V → V) x ∈ N) → N = ⊥ ∨ N = ⊤) →
            ∀ (f : Module.End ℂ V) (s : Finset V), ∃ b ∈ B, ∀ m ∈ s, (f : V → V) m = (b : V → V) m := by
  intro V _ _ _ hV B hB f s
  have hsc : ∀ (c : ℂ) (x : V), c • x = (algebraMap ℂ B c) • x := fun c x => by
    change c • x = ((algebraMap ℂ (Module.End ℂ V) c : Module.End ℂ V)) x
    simp [Module.algebraMap_end_apply]
  have hbc : ∀ (b : B) (c : ℂ) (x : V), b • (c • x) = c • (b • x) := fun b c x =>
    (b : Module.End ℂ V).map_smul c x
  haveI hsimple : IsSimpleModule B V :=
    { exists_pair_ne := ⟨⊥, ⊤, bot_ne_top⟩
      eq_bot_or_eq_top := fun N => by
        let N' : Submodule ℂ V :=
          { carrier := N
            add_mem' := fun h1 h2 => N.add_mem h1 h2
            zero_mem' := N.zero_mem
            smul_mem' := fun c x hx => by
              rw [hsc]
              exact N.smul_mem _ hx }
        rcases hB N' (fun b hb x hx => N.smul_mem (⟨b, hb⟩ : B) hx) with h | h
        · left
          rw [eq_bot_iff]
          intro x hx
          have : x ∈ N' := hx
          rw [h] at this
          simpa using this
        · right
          rw [eq_top_iff]
          intro x _
          have : x ∈ N' := by rw [h]; trivial
          exact this }
  have hscal : ∀ d : Module.End B V, ∃ a : ℂ, ∀ x, d x = a • x := by
    intro d
    let T : Module.End ℂ V :=
      { toFun := d
        map_add' := d.map_add
        map_smul' := fun c x => by
          simp only [RingHom.id_apply]
          rw [hsc, d.map_smul, ← hsc] }
    obtain ⟨a, ha⟩ := spectrum_nonempty_of_countable_rank hV T
    let e : V →ₗ[B] V :=
      { toFun := fun x => a • x - d x
        map_add' := fun x y => by
          rw [smul_add, d.map_add]
          abel
        map_smul' := fun b x => by
          simp only [RingHom.id_apply]
          rw [d.map_smul, smul_sub, hbc] }
    rcases LinearMap.bijective_or_eq_zero e with hb | h0
    · exfalso
      apply ha
      rw [spectrum.mem_resolventSet_iff, Module.End.isUnit_iff]
      have hfe : ⇑(algebraMap ℂ (Module.End ℂ V) a - T) = ⇑e := by
        funext x
        simp [T, e, Module.algebraMap_end_apply]
      rw [hfe]
      exact hb
    · refine ⟨a, fun x => ?_⟩
      have : a • x - d x = 0 := congrArg (fun g : V →ₗ[B] V => g x) h0
      exact (sub_eq_zero.mp this).symm
  let F : Module.End (Module.End B V) V :=
    { toFun := f
      map_add' := f.map_add
      map_smul' := fun d x => by
        obtain ⟨a, ha⟩ := hscal d
        simp only [RingHom.id_apply, Module.End.smul_def]
        rw [ha, ha, f.map_smul] }
  obtain ⟨r, hr⟩ := jacobson_density F s
  exact ⟨r, r.2, fun m hm => hr m hm⟩

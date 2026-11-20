import Mathlib

@[reducible] noncomputable def UpperTheory.Reformulated.B.HilbertNinetyCapelliIdentities.G.{u_1, u_2} :
    (F : Type u_1) → (Ω : Type u_2) → [inst : Field F] → [inst_1 : Field Ω] → [Algebra F Ω] → Type u_2 :=
    fun (F : Type u_1) (Ω : Type u_2) [Field F] [Field Ω] [Algebra F Ω] ↦ Gal(Ω/F)

/- English proof (translation)
Introduce `K Ω _ _ _ _ _ f hlc h0 hc`. Establish `h1 : f 1 = 1`. Establish `h` using `hc 1 1`. Rewrite `h` using `[mul_one, AlgEquiv.one_apply]`. Conclude with `(mul_eq_left₀ (h0 1)).1 h.symm`.

Establish `hU : f ⁻¹' {1} ∈ nhds (1 : Gal(Ω/K))` using `(hlc {1}).mem_nhds h1`. Take `⟨L, hL, hLU⟩` from `(krullTopology_mem_nhds_one_iff K Ω _).1 hU`. Establish `hH : ∀ (g h : Gal(Ω/K)), h ∈ L.fixingSubgroup → f (g * h) = f g`. Introduce `g h hh`. Establish `: f h = 1` using `hLU hh`.

Rewrite using `[hc, this, map_one, mul_one]`. Establish `hopen : IsOpen (L.fixingSubgroup : Set Gal(Ω/K))` using `L.fixingSubgroup_isOpen`. Use `haveI : Finite (Gal(Ω/K) ⧸ L.fixingSubgroup) := Subgroup.quotient_finite_of_isOpen _ hopen`. Use `letI : Fintype (Gal(Ω/K) ⧸ L.fixingSubgroup) := Fintype.ofFinite _`. Set `χ : (Gal(Ω/K) ⧸ L.fixingSubgroup) → (L →* Ω)` to `fun q => ((q.out : Gal(Ω/K)) : Ω →* Ω).comp (L.val : L →* Ω)`.

Establish `hχ : ∀ q (x : L), χ q x = (q.out : Gal(Ω/K)) (x : Ω)` using `fun q x => rfl`. Establish `hinj : Function.Injective χ`. Introduce `p q hpq`. Rewrite using `[← QuotientGroup.out_eq' p, ← QuotientGroup.out_eq' q, QuotientGroup.eq, IntermediateField.mem_fixingSubgroup_iff]`. Introduce `x hx`.

Establish `h` using `DFunLike.congr_fun hpq ⟨x, hx⟩`. Rewrite `h` using `[hχ, hχ]`. Rewrite using `[AlgEquiv.mul_apply]`. Express the relevant statement in the definitionally equal form `p.out.symm (q.out x) = x`. Rewrite using `[AlgEquiv.symm_apply_eq]`.

Conclude with `h.symm`. Establish `hli` using `(linearIndependent_monoidHom L Ω).comp χ hinj`. Establish `hex : ∃ x : L, ∑ q, f q.out * χ q x ≠ 0`. Assume the negation of the conclusion as `hne`. Use `push Not at hne`.

Use `Fintype.linearIndependent_iff.1 hli (fun q => f q.out) (by` as an intermediate fact. Use function extensionality and compare the values at `x`. Simplify `hne x) (QuotientGroup.mk 1)` using `[Finset.sum_apply]`. Conclude with `h0 _ this`. Take `⟨x, hx⟩` from `hex`.

Establish `key : ∀ g : Gal(Ω/K), f g * g (∑ q, f q.out * χ q x) = ∑ q, f q.out * χ q x`. Introduce `g`. Rewrite using `[map_sum, Finset.mul_sum]`. Use `Fintype.sum_equiv (MulAction.toPerm g) _ _ fun q => ?_` and prove the remaining obligations. Establish `hq : g • q = QuotientGroup.mk (g * q.out)` using `by conv_lhs => rw [← QuotientGroup.out_eq' q]`.

Both sides reduce to the same expression. Take `⟨h, hh⟩` from `QuotientGroup.mk_out_eq_mul L.fixingSubgroup (g * q.out)`. Establish `hfix : (h : Gal(Ω/K)) (x : Ω) = x` using `(IntermediateField.mem_fixingSubgroup_iff _ _).1 h.2 x x.2`. Rewrite using `[MulAction.toPerm_apply, hq, hχ, hχ, hh, hH _ _ h.2, hc, AlgEquiv.mul_apply, hfix, AlgEquiv.mul_apply, map_mul, mul_assoc]`. Use `⟨(∑ q, f q.out * χ q x)⁻¹, inv_ne_zero hx, fun g => ?_⟩` and prove the remaining obligations.

Establish `hk` using `key g`. Generalize the expression as in `(∑ q, f q.out * χ q x) = b at hx hk`. Establish `hg : g b ≠ 0` using `(map_ne_zero g).2 hx`. Rewrite using `[map_inv₀]`. Clear the denominators using the available nonvanishing facts.

Rewrite using `[mul_comm]`. Conclude with `hk.symm`.
-/
theorem UpperTheory.Reformulated.B.HilbertNinetyCapelliIdentities.h90 :
    ∀ (K Ω : Type) [inst : Field K] [NumberField K] [inst_2 : Field Ω] [inst_3 : Algebra K Ω] [IsAlgClosure K Ω]
      (f : UpperTheory.Reformulated.B.HilbertNinetyCapelliIdentities.G K Ω → Ω),
      IsLocallyConstant f →
        (∀ (g : UpperTheory.Reformulated.B.HilbertNinetyCapelliIdentities.G K Ω), f g ≠ (0 : Ω)) →
          (∀ (g h : UpperTheory.Reformulated.B.HilbertNinetyCapelliIdentities.G K Ω), f (g * h) = f g * (g : Ω → Ω) (f h)) →
            ∃ (β : Ω), β ≠ (0 : Ω) ∧ ∀ (g : UpperTheory.Reformulated.B.HilbertNinetyCapelliIdentities.G K Ω), (g : Ω → Ω) β = f g * β := by
  intro K Ω _ _ _ _ _ f hlc h0 hc
  classical
  have h1 : f 1 = 1 := by
    have h := hc 1 1
    rw [mul_one, AlgEquiv.one_apply] at h
    exact (mul_eq_left₀ (h0 1)).1 h.symm
  have hU : f ⁻¹' {1} ∈ nhds (1 : Gal(Ω/K)) :=
    (hlc {1}).mem_nhds h1
  obtain ⟨L, hL, hLU⟩ := (krullTopology_mem_nhds_one_iff K Ω _).1 hU
  have hH : ∀ (g h : Gal(Ω/K)), h ∈ L.fixingSubgroup → f (g * h) = f g := by
    intro g h hh
    have : f h = 1 := hLU hh
    rw [hc, this, map_one, mul_one]
  have hopen : IsOpen (L.fixingSubgroup : Set Gal(Ω/K)) := L.fixingSubgroup_isOpen
  haveI : Finite (Gal(Ω/K) ⧸ L.fixingSubgroup) :=
    Subgroup.quotient_finite_of_isOpen _ hopen
  letI : Fintype (Gal(Ω/K) ⧸ L.fixingSubgroup) := Fintype.ofFinite _
  let χ : (Gal(Ω/K) ⧸ L.fixingSubgroup) → (L →* Ω) := fun q =>
    ((q.out : Gal(Ω/K)) : Ω →* Ω).comp (L.val : L →* Ω)
  have hχ : ∀ q (x : L), χ q x = (q.out : Gal(Ω/K)) (x : Ω) := fun q x => rfl
  have hinj : Function.Injective χ := by
    intro p q hpq
    rw [← QuotientGroup.out_eq' p, ← QuotientGroup.out_eq' q, QuotientGroup.eq,
      IntermediateField.mem_fixingSubgroup_iff]
    intro x hx
    have h := DFunLike.congr_fun hpq ⟨x, hx⟩
    rw [hχ, hχ] at h
    rw [AlgEquiv.mul_apply]
    change p.out.symm (q.out x) = x
    rw [AlgEquiv.symm_apply_eq]
    exact h.symm
  have hli := (linearIndependent_monoidHom L Ω).comp χ hinj
  have hex : ∃ x : L, ∑ q, f q.out * χ q x ≠ 0 := by
    by_contra hne
    push Not at hne
    have := Fintype.linearIndependent_iff.1 hli (fun q => f q.out) (by
      funext x
      simpa [Finset.sum_apply] using hne x) (QuotientGroup.mk 1)
    exact h0 _ this
  obtain ⟨x, hx⟩ := hex
  have key : ∀ g : Gal(Ω/K),
      f g * g (∑ q, f q.out * χ q x) = ∑ q, f q.out * χ q x := by
    intro g
    rw [map_sum, Finset.mul_sum]
    refine Fintype.sum_equiv (MulAction.toPerm g) _ _ fun q => ?_
    have hq : g • q = QuotientGroup.mk (g * q.out) := by
      conv_lhs => rw [← QuotientGroup.out_eq' q]
      rfl
    obtain ⟨h, hh⟩ := QuotientGroup.mk_out_eq_mul L.fixingSubgroup (g * q.out)
    have hfix : (h : Gal(Ω/K)) (x : Ω) = x :=
      (IntermediateField.mem_fixingSubgroup_iff _ _).1 h.2 x x.2
    rw [MulAction.toPerm_apply, hq, hχ, hχ, hh, hH _ _ h.2, hc, AlgEquiv.mul_apply, hfix,
      AlgEquiv.mul_apply, map_mul, mul_assoc]
  refine ⟨(∑ q, f q.out * χ q x)⁻¹, inv_ne_zero hx, fun g => ?_⟩
  have hk := key g
  generalize (∑ q, f q.out * χ q x) = b at hx hk
  have hg : g b ≠ 0 := (map_ne_zero g).2 hx
  rw [map_inv₀]
  field_simp
  rw [mul_comm]
  exact hk.symm

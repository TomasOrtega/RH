import Development.AutomorphicArithmetic.AutomorphicVarieties.TorsionBoundsChains.FaceDSingle

open CategoryTheory UpperTheory.V.KH

/- English proof (translation)
Introduce `G X _ _`. Use `set q : X → MulAction.orbitRel.Quotient G X := Quotient.mk (MulAction.orbitRel G X) with hq`. Use `set K := Representation.Coinvariants.ker (perm G X) with hK`. Apply `le_antisymm` to reduce the goal to its premises. Introduce `f hf`.

Rewrite `hf` using `[LinearMap.mem_ker, Finsupp.lmapDomain_apply]`. Set `r : X → X` to `fun x => Quotient.out (q x)`. Establish `hstep : ∀ f : X →₀ ℤ, f - Finsupp.mapDomain r f ∈ K`. Introduce `f`. Proceed by induction on `f using Finsupp.induction_linear with`.

Consider the case `zero => simp`. Consider the case `add a b ha hb`. Rewrite using `[Finsupp.mapDomain_add]`. Use `K.add_mem ha hb` as an intermediate fact. Use `this using 1` and compare the differences between its conclusion and the goal.

Normalize the expressions using the abelian group laws. Consider the case `single x c`. Rewrite using `[Finsupp.mapDomain_single]`. Establish `hx : (MulAction.orbitRel G X) (r x) x` using `Quotient.mk_out (s := MulAction.orbitRel G X) x`. Take `⟨g, hg⟩` from `hx`.

Establish `hg' : g • x = r x` using `hg`. Establish `hmem` using `Representation.Coinvariants.mem_ker_of_eq (ρ := perm G X) g (Finsupp.single x c) _ rfl`. Establish `hneg` using `K.neg_mem hmem`. Use `hneg using 1` and compare the differences between its conclusion and the goal. Rewrite using `[perm_single, hg']`.

Normalize the expressions using the abelian group laws. Establish `h0 : Finsupp.mapDomain r f = 0`. Establish `: r = (fun c => Quotient.out c) ∘ q` using `rfl`. Rewrite using `[this, Finsupp.mapDomain_comp, hf, Finsupp.mapDomain_zero]`. Use `hstep f` as an intermediate fact.

Rewrite `this` using `[h0, sub_zero]`. Then use the resulting hypothesis. Use `Submodule.span_le.2 ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨⟨g, v⟩, rfl⟩`. Express the relevant statement in the definitionally equal form `Finsupp.lmapDomain ℤ ℤ q ((perm G X) g v - v) = 0`. Rewrite using `[map_sub, perm_apply, Finsupp.lmapDomain_apply, Finsupp.lmapDomain_apply, ← Finsupp.mapDomain_comp]`.

Establish `: q ∘ (fun x => g • x) = q`. Use function extensionality and compare the values at `x`. Conclude with `Quotient.sound ⟨g, rfl⟩`. Rewrite using `[this, sub_self]`.
-/
theorem UpperTheory.V.KH.kerOrb :
    ∀ (G X : Type) [Group G] [MulAction G X],
      LinearMap.ker (Finsupp.lmapDomain ℤ ℤ
        (Quotient.mk (MulAction.orbitRel G X) : X → MulAction.orbitRel.Quotient G X)) =
      Representation.Coinvariants.ker (perm G X) := by
  intro G X _ _
  set q : X → MulAction.orbitRel.Quotient G X := Quotient.mk (MulAction.orbitRel G X) with hq
  set K := Representation.Coinvariants.ker (perm G X) with hK
  apply le_antisymm
  · intro f hf
    rw [LinearMap.mem_ker, Finsupp.lmapDomain_apply] at hf
    let r : X → X := fun x => Quotient.out (q x)
    have hstep : ∀ f : X →₀ ℤ, f - Finsupp.mapDomain r f ∈ K := by
      intro f
      induction f using Finsupp.induction_linear with
      | zero => simp
      | add a b ha hb =>
        rw [Finsupp.mapDomain_add]
        have := K.add_mem ha hb
        convert this using 1
        abel
      | single x c =>
        rw [Finsupp.mapDomain_single]
        have hx : (MulAction.orbitRel G X) (r x) x := Quotient.mk_out (s := MulAction.orbitRel G X) x
        obtain ⟨g, hg⟩ := hx
        have hg' : g • x = r x := hg
        have hmem := Representation.Coinvariants.mem_ker_of_eq (ρ := perm G X) g
          (Finsupp.single x c) _ rfl
        have hneg := K.neg_mem hmem
        convert hneg using 1
        rw [perm_single, hg']
        abel
    have h0 : Finsupp.mapDomain r f = 0 := by
      have : r = (fun c => Quotient.out c) ∘ q := rfl
      rw [this, Finsupp.mapDomain_comp, hf, Finsupp.mapDomain_zero]
    have := hstep f
    rwa [h0, sub_zero] at this
  · refine Submodule.span_le.2 ?_
    rintro _ ⟨⟨g, v⟩, rfl⟩
    change Finsupp.lmapDomain ℤ ℤ q ((perm G X) g v - v) = 0
    rw [map_sub, perm_apply, Finsupp.lmapDomain_apply, Finsupp.lmapDomain_apply,
      ← Finsupp.mapDomain_comp]
    have : q ∘ (fun x => g • x) = q := by
      funext x
      exact Quotient.sound ⟨g, rfl⟩
    rw [this, sub_self]

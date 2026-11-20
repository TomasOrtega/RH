import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.AlgDefs

open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.U3 UpperTheory.V.Fr

/- English proof (translation)
Proceed by induction on `hx using Submodule.span_induction with`. Consider the case `mem y hy => exact hs y hy`. Consider the case `zero => rw [AddMonoidAlgebra.single_zero]`. Conclude with `A.zero_mem`. Consider the case `add y z _ _ hy hz => rw [AddMonoidAlgebra.single_add]`.

Conclude with `A.add_mem hy hz`. Consider the case `smul c y _ hy => rw [← AddMonoidAlgebra.smul_single]`. Conclude with `A.smul_mem hy c`.
-/
private theorem single_mem_of_span {C K : Type} [CommRing C] [CommRing K] [Algebra C K]
    (A : Subalgebra C (AddMonoidAlgebra K ℤ)) (j : ℤ) (s : Set K)
    (hs : ∀ x ∈ s, AddMonoidAlgebra.single j x ∈ A) {x : K} (hx : x ∈ Submodule.span C s) :
    AddMonoidAlgebra.single j x ∈ A := by
  induction hx using Submodule.span_induction with
  | mem y hy => exact hs y hy
  | zero => rw [AddMonoidAlgebra.single_zero]; exact A.zero_mem
  | add y z _ _ hy hz => rw [AddMonoidAlgebra.single_add]; exact A.add_mem hy hz
  | smul c y _ hy => rw [← AddMonoidAlgebra.smul_single]; exact A.smul_mem hy c

/- English proof (translation)
Introduce `l _ k _ F n C _ K _ _ ρ h`. Use `choose S hS using h`. Use `set G : Set (AddMonoidAlgebra K ℤ) := ⋃ i, ⋃ j, (fun x => AddMonoidAlgebra.single (w n i - w n j) x) '' (S i j : Set K) with hG`. Establish `hGfin : G.Finite` using `Set.finite_iUnion fun i => Set.finite_iUnion fun j => (S i j).finite_toSet.image _`. Establish `hGmem : ∀ i j x, x ∈ (S i j : Set K) → AddMonoidAlgebra.single (w n i - w n j) x ∈ Algebra.adjoin C G` using `fun i j x hx => Algebra.subset_adjoin (Set.mem_iUnion.2 ⟨i, Set.mem_iUnion.2 ⟨j, ⟨x, hx, rfl⟩⟩⟩)`.

Establish `hent : ∀ g i j, AddMonoidAlgebra.single (w n i - w n j) (ρ.r g i j) ∈ Algebra.adjoin C G` using `fun g i j => single_mem_of_span (Algebra.adjoin C G) _ (S i j) (hGmem i j) (by rw [hS i j]; exact Submodule.subset_span ⟨g, rfl⟩)`. Establish `hlist : ∀ L : List (F.G0 × Fin n × Fin n), AddMonoidAlgebra.single ((L.map fun s => w n s.2.1 - w n s.2.2).sum) ((L.map fun s => ρ.r s.1 s.2.1 s.2.2).prod) ∈ Algebra.adjoin C G`. Introduce `L`. Proceed by induction on `L with`. Consider the case `nil`.

Simplify using `only [List.map_nil, List.sum_nil, List.prod_nil]`. Rewrite using `[← AddMonoidAlgebra.one_def]`. Conclude with `(Algebra.adjoin C G).one_mem`. Consider the case `cons s L ih`. Simplify using `only [List.map_cons, List.sum_cons, List.prod_cons]`.

Rewrite using `[← AddMonoidAlgebra.single_mul_single]`. Conclude with `mul_mem (hent _ _ _) ih`. Establish `hmon : ∀ j, ∀ x ∈ ρ.mon j, AddMonoidAlgebra.single j x ∈ Algebra.adjoin C G`. Introduce and unpack `j x ⟨L, hL, rfl⟩`. Rewrite using `[← hL]`.

Conclude with `hlist L`. Establish `hpart : ∀ j x, x ∈ ρ.part C j → AddMonoidAlgebra.single j x ∈ Algebra.adjoin C G` using `fun j x hx => single_mem_of_span _ j _ (hmon j) hx`. Establish `heq : Algebra.adjoin C G = lauSub (ρ.part C)`. Apply `le_antisymm` to reduce the goal to its premises. Rewrite using `[Algebra.adjoin_le_iff]`.

Introduce `y hy`. Take `⟨i, hy⟩` from `Set.mem_iUnion.1 hy`. Take `⟨j, hy⟩` from `Set.mem_iUnion.1 hy`. Take `⟨x, hx, rfl⟩` from `hy`. Apply `single_mem_lauSub` to reduce the goal to its premises.

Establish `hx' : x ∈ Submodule.span C (Set.range fun g => ρ.r g i j)`. Rewrite using `[← hS i j]`. Conclude with `Submodule.subset_span hx`. Use `Submodule.span_le.mpr ?_ hx'` and prove the remaining obligations. Introduce and unpack `_ ⟨g, rfl⟩`.

Conclude with `NRep.r_mem_part C ρ g i j`. Introduce `p hp`. Establish `hp' : ∀ j, p.coeff j ∈ ρ.part C j` using `hp`. Establish `hsum : p = p.coeff.sum fun j x => AddMonoidAlgebra.single j x`. Apply `AddMonoidAlgebra.ext` to reduce the goal to its premises.

Rewrite using `[Finsupp.sum, AddMonoidAlgebra.coeff_sum]`. Conclude with `(Finsupp.sum_single _).symm`. Rewrite using `[hsum]`. Conclude with `Subalgebra.sum_mem _ fun j _ => hpart j _ (hp' j)`. Conclude with `⟨(Subalgebra.fg_top _).mpr ⟨hGfin.toFinset, by rw [Set.Finite.coe_toFinset]; exact heq⟩⟩`.
-/
theorem UpperTheory.V.Fr.alg_ft :
    ∀ {l : ℕ} [Fact l.Prime] {k : Type} [Field k] {F : Frame l k} {n : ℕ} (C : Type) [CommRing C] {K : Type} [CommRing K] [Algebra C K] (ρ : NRep F n K), (∀ i j, (Submodule.span C (Set.range fun g => ρ.r g i j)).FG) → Algebra.FiniteType C (lauSub (ρ.part C)) := by
  intro l _ k _ F n C _ K _ _ ρ h
  choose S hS using h
  set G : Set (AddMonoidAlgebra K ℤ) :=
    ⋃ i, ⋃ j, (fun x => AddMonoidAlgebra.single (w n i - w n j) x) '' (S i j : Set K) with hG
  have hGfin : G.Finite :=
    Set.finite_iUnion fun i => Set.finite_iUnion fun j => (S i j).finite_toSet.image _
  have hGmem : ∀ i j x, x ∈ (S i j : Set K) →
      AddMonoidAlgebra.single (w n i - w n j) x ∈ Algebra.adjoin C G := fun i j x hx =>
    Algebra.subset_adjoin (Set.mem_iUnion.2 ⟨i, Set.mem_iUnion.2 ⟨j, ⟨x, hx, rfl⟩⟩⟩)
  have hent : ∀ g i j, AddMonoidAlgebra.single (w n i - w n j) (ρ.r g i j) ∈ Algebra.adjoin C G :=
    fun g i j => single_mem_of_span (Algebra.adjoin C G) _ (S i j) (hGmem i j)
      (by rw [hS i j]; exact Submodule.subset_span ⟨g, rfl⟩)
  have hlist : ∀ L : List (F.G0 × Fin n × Fin n),
      AddMonoidAlgebra.single ((L.map fun s => w n s.2.1 - w n s.2.2).sum)
        ((L.map fun s => ρ.r s.1 s.2.1 s.2.2).prod) ∈ Algebra.adjoin C G := by
    intro L
    induction L with
    | nil =>
      simp only [List.map_nil, List.sum_nil, List.prod_nil]
      rw [← AddMonoidAlgebra.one_def]
      exact (Algebra.adjoin C G).one_mem
    | cons s L ih =>
      simp only [List.map_cons, List.sum_cons, List.prod_cons]
      rw [← AddMonoidAlgebra.single_mul_single]
      exact mul_mem (hent _ _ _) ih
  have hmon : ∀ j, ∀ x ∈ ρ.mon j, AddMonoidAlgebra.single j x ∈ Algebra.adjoin C G := by
    rintro j x ⟨L, hL, rfl⟩
    rw [← hL]
    exact hlist L
  have hpart : ∀ j x, x ∈ ρ.part C j → AddMonoidAlgebra.single j x ∈ Algebra.adjoin C G :=
    fun j x hx => single_mem_of_span _ j _ (hmon j) hx
  have heq : Algebra.adjoin C G = lauSub (ρ.part C) := by
    apply le_antisymm
    · rw [Algebra.adjoin_le_iff]
      intro y hy
      obtain ⟨i, hy⟩ := Set.mem_iUnion.1 hy
      obtain ⟨j, hy⟩ := Set.mem_iUnion.1 hy
      obtain ⟨x, hx, rfl⟩ := hy
      apply single_mem_lauSub
      have hx' : x ∈ Submodule.span C (Set.range fun g => ρ.r g i j) := by
        rw [← hS i j]
        exact Submodule.subset_span hx
      refine Submodule.span_le.mpr ?_ hx'
      rintro _ ⟨g, rfl⟩
      exact NRep.r_mem_part C ρ g i j
    · intro p hp
      have hp' : ∀ j, p.coeff j ∈ ρ.part C j := hp
      have hsum : p = p.coeff.sum fun j x => AddMonoidAlgebra.single j x := by
        apply AddMonoidAlgebra.ext
        rw [Finsupp.sum, AddMonoidAlgebra.coeff_sum]
        exact (Finsupp.sum_single _).symm
      rw [hsum]
      exact Subalgebra.sum_mem _ fun j _ => hpart j _ (hp' j)
  exact ⟨(Subalgebra.fg_top _).mpr ⟨hGfin.toFinset, by rw [Set.Finite.coe_toFinset]; exact heq⟩⟩

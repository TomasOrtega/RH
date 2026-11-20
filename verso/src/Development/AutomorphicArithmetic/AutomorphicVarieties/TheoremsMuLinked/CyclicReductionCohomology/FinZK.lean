import Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.CyclicReductionCohomology.DualPair
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.DegreeCountCohomology.PhiSub

open IsLocalRing Matrix Filter NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa UpperTheory.V.HV UpperTheory.V.Th GlobalTheory.GalOfCusp

/- English proof (translation)
Proceed by induction on `j with`. Consider the case `zero`. Apply `Set.Finite.subset (Set.finite_singleton 0)` to reduce the goal to its premises. Introduce `a ha`. Simplify using `only [Set.mem_setOf_eq, pow_zero, one_smul] at ha`.

Simplify using `[ha]`. Consider the case `succ j ih`. Establish `hsub : {a : A | l ^ (j + 1) • a = 0} ⊆ (fun a => l • a) ⁻¹' {a : A | l ^ j • a = 0}`. Introduce `a ha`. Simplify using `only [Set.mem_setOf_eq, Set.mem_preimage] at ha ⊢`.

Rewrite using `[smul_smul, ← pow_succ]`. Conclude with `ha`. Use `Set.Finite.subset (Set.Finite.preimage' ih ?_) hsub` and prove the remaining obligations. Introduce `b _`. Distinguish the cases in `hne : ((fun a : A => l • a) ⁻¹' {b}).Nonempty`.

Take `⟨a0, ha0⟩` from `hne`. Use `Set.Finite.subset (h1.image (fun x => x + a0)) ?_` and prove the remaining obligations. Introduce `a ha`. Use `⟨a - a0, ?_, by simp⟩` and prove the remaining obligations. Simplify using `only [Set.mem_preimage, Set.mem_singleton_iff] at ha ha0`.

Simplify using `only [Set.mem_setOf_eq, smul_sub, ha, ha0, sub_self]`. Rewrite `hne` using `[Set.not_nonempty_iff_eq_empty]`. Rewrite using `[hne]`. Conclude with `Set.finite_empty`.
-/
private theorem fin_step {A : Type} [AddCommGroup A] (l : ℕ) (h1 : {a : A | l • a = 0}.Finite) (j : ℕ) :
    {a : A | l ^ j • a = 0}.Finite := by
  induction j with
  | zero =>
    apply Set.Finite.subset (Set.finite_singleton 0)
    intro a ha
    simp only [Set.mem_setOf_eq, pow_zero, one_smul] at ha
    simp [ha]
  | succ j ih =>
    have hsub : {a : A | l ^ (j + 1) • a = 0} ⊆ (fun a => l • a) ⁻¹' {a : A | l ^ j • a = 0} := by
      intro a ha
      simp only [Set.mem_setOf_eq, Set.mem_preimage] at ha ⊢
      rw [smul_smul, ← pow_succ]; exact ha
    refine Set.Finite.subset (Set.Finite.preimage' ih ?_) hsub
    intro b _
    by_cases hne : ((fun a : A => l • a) ⁻¹' {b}).Nonempty
    · obtain ⟨a0, ha0⟩ := hne
      refine Set.Finite.subset (h1.image (fun x => x + a0)) ?_
      intro a ha
      refine ⟨a - a0, ?_, by simp⟩
      simp only [Set.mem_preimage, Set.mem_singleton_iff] at ha ha0
      simp only [Set.mem_setOf_eq, smul_sub, ha, ha0, sub_self]
    · rw [Set.not_nonempty_iff_eq_empty] at hne
      rw [hne]; exact Set.finite_empty

/- English proof (translation)
Introduce `l _ k R Γ M _ _ _ _ _ _ _ _ ρ hphi hlc htors`. Set `M1 : Submodule R M` to `{ carrier := {m | l • m = 0} add_mem' := fun {a b} ha hb => by`. Simplify using `only [Set.mem_setOf_eq] at *`. Rewrite using `[smul_add, ha, hb, add_zero]`. Use the proof step `zero_mem' := by simp`.

Use the proof step `smul_mem' := fun r {m} hm => by`. Simplify using `only [Set.mem_setOf_eq] at *`. Rewrite using `[smul_comm, hm, smul_zero] }`. Establish `hst : ∀ g, ∀ m ∈ M1, ρ g m ∈ M1`. Introduce `g m hm`.

Use `show l • ρ g m = 0`. Rewrite using `[← map_nsmul, show l • m = 0 from hm, map_zero]`. Set `ρ1 : Representation R Γ M1` to `{ toFun := fun g => (ρ g).restrict (hst g) map_one' := by`. Use `LinearMap.ext fun m => Subtype.ext ?_` and prove the remaining obligations. Simplify using the standard rewrite rules.

Use the proof step `map_mul' := fun g h => by`. Use `LinearMap.ext fun m => Subtype.ext ?_` and prove the remaining obligations. Simplify using `}`. Establish `hlc1 : LC ρ1` using `fun m => IsLocallyConstant.desc _ Subtype.val (hlc m.1) Subtype.val_injective`. Establish `htors1 : ∀ m : M1, l • m = 0`.

Introduce `m`. Establish `h : l • (m : M) = 0` using `m.2`. Apply `Subtype.ext` to reduce the goal to its premises. Simplify using `using h`. Establish `hfin1 : Finite (Zl ρ1)` using `(finZ l R Γ M1 ρ1 hphi hlc1 htors1).1`.

Establish `hl : {a : Zl ρ | l • a = 0}.Finite`. Establish `hval : ∀ a : {a : Zl ρ // l • a = 0}, ∀ g, (a.1 : Γ → M) g ∈ M1`. Introduce `a g`. Establish `h` using `congrArg (fun x : Zl ρ => (x : Γ → M) g) a.2`. Use `show l • (a.1 : Γ → M) g = 0`.

Simplify using `using h`. Establish `hmemF : ∀ a : {a : Zl ρ // l • a = 0}, (fun g => (⟨(a.1 : Γ → M) g, hval a g⟩ : M1)) ∈ Zl ρ1`. Introduce `a`. Take `⟨hlc', hcoc⟩` from `(mem_Zl ρ).mp a.1.2`. Conclude with `(mem_Zl ρ1).mpr ⟨IsLocallyConstant.desc _ Subtype.val hlc' Subtype.val_injective, fun g h => Subtype.ext (hcoc g h)⟩`.

Set `F : {a : Zl ρ // l • a = 0} → Zl ρ1` to `fun a => ⟨_, hmemF a⟩`. Establish `hF : Function.Injective F`. Introduce `a b hab`. Apply `Subtype.ext` to reduce the goal to its premises. Apply `Subtype.ext` to reduce the goal to its premises.

Use function extensionality and compare the values at `g`. Use `congrFun (congrArg Subtype.val hab) g` as an intermediate fact. Conclude with `congrArg Subtype.val this`. Use `haveI : Finite ↥{a : Zl ρ | l • a = 0} := Finite.of_injective F hF`. Conclude with `Set.toFinite _`.

Establish `hk` using `fin_step l hl k`. Establish `huniv : {a : Zl ρ | l ^ k • a = 0} = Set.univ`. Use extensionality with `a`. Simplify using `only [Set.mem_setOf_eq, Set.mem_univ, iff_true]`. Apply `Subtype.ext` to reduce the goal to its premises.

Use function extensionality and compare the values at `g`. Simplify using `[htors]`. Rewrite `hk` using `[huniv]`. Conclude with `Set.finite_univ_iff.mp hk`.
-/
theorem UpperTheory.V.Th.finZK :
    ∀ (l : ℕ) [Fact l.Prime] (k : ℕ) (R Γ M : Type) [CommRing R] [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [CompactSpace Γ] [AddCommGroup M] [Module R M] [Finite M] (ρ : Representation R Γ M), PhiCond Γ l → LC ρ → (∀ m : M, l ^ k • m = 0) → Finite (Zl ρ) := by
  intro l _ k R Γ M _ _ _ _ _ _ _ _ ρ hphi hlc htors
  classical
  let M1 : Submodule R M :=
    { carrier := {m | l • m = 0}
      add_mem' := fun {a b} ha hb => by
        simp only [Set.mem_setOf_eq] at *
        rw [smul_add, ha, hb, add_zero]
      zero_mem' := by simp
      smul_mem' := fun r {m} hm => by
        simp only [Set.mem_setOf_eq] at *
        rw [smul_comm, hm, smul_zero] }
  have hst : ∀ g, ∀ m ∈ M1, ρ g m ∈ M1 := by
    intro g m hm
    show l • ρ g m = 0
    rw [← map_nsmul, show l • m = 0 from hm, map_zero]
  let ρ1 : Representation R Γ M1 :=
    { toFun := fun g => (ρ g).restrict (hst g)
      map_one' := by
        refine LinearMap.ext fun m => Subtype.ext ?_
        simp
      map_mul' := fun g h => by
        refine LinearMap.ext fun m => Subtype.ext ?_
        simp }
  have hlc1 : LC ρ1 := fun m => IsLocallyConstant.desc _ Subtype.val (hlc m.1) Subtype.val_injective
  have htors1 : ∀ m : M1, l • m = 0 := by
    intro m
    have h : l • (m : M) = 0 := m.2
    apply Subtype.ext
    simpa using h
  have hfin1 : Finite (Zl ρ1) := (finZ l R Γ M1 ρ1 hphi hlc1 htors1).1
  have hl : {a : Zl ρ | l • a = 0}.Finite := by
    have hval : ∀ a : {a : Zl ρ // l • a = 0}, ∀ g, (a.1 : Γ → M) g ∈ M1 := by
      intro a g
      have h := congrArg (fun x : Zl ρ => (x : Γ → M) g) a.2
      show l • (a.1 : Γ → M) g = 0
      simpa using h
    have hmemF : ∀ a : {a : Zl ρ // l • a = 0},
        (fun g => (⟨(a.1 : Γ → M) g, hval a g⟩ : M1)) ∈ Zl ρ1 := by
      intro a
      obtain ⟨hlc', hcoc⟩ := (mem_Zl ρ).mp a.1.2
      exact (mem_Zl ρ1).mpr ⟨IsLocallyConstant.desc _ Subtype.val hlc' Subtype.val_injective,
        fun g h => Subtype.ext (hcoc g h)⟩
    let F : {a : Zl ρ // l • a = 0} → Zl ρ1 := fun a => ⟨_, hmemF a⟩
    have hF : Function.Injective F := by
      intro a b hab
      apply Subtype.ext; apply Subtype.ext; funext g
      have := congrFun (congrArg Subtype.val hab) g
      exact congrArg Subtype.val this
    haveI : Finite ↥{a : Zl ρ | l • a = 0} := Finite.of_injective F hF
    exact Set.toFinite _
  have hk := fin_step l hl k
  have huniv : {a : Zl ρ | l ^ k • a = 0} = Set.univ := by
    ext a
    simp only [Set.mem_setOf_eq, Set.mem_univ, iff_true]
    apply Subtype.ext
    funext g
    simp [htors]
  rw [huniv] at hk
  exact Set.finite_univ_iff.mp hk

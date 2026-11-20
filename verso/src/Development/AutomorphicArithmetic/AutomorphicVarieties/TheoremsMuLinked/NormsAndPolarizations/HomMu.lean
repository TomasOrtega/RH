import Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.NormsAndPolarizations.CjApply

open IsLocalRing Matrix NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal UpperTheory.V UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa UpperTheory.V.HV UpperTheory.V.Th UpperTheory.V.Th.Nm GlobalTheory.GalOfCusp

/- English proof (translation)
Introduce `l _ c G _ _ _ d hd hadd g hg`. Establish `hd1 : d 1 = 0`. Establish `h` using `hadd 1 1`. Rewrite `h` using `[mul_one]`. Simplify using `using h`.

Set `f : G →* Multiplicative c.O` to `{ toFun := fun x => Multiplicative.ofAdd (d x) map_one' := by simp [hd1] map_mul' := fun x y => by show Multiplicative.ofAdd (d (x * y)) = Multiplicative.ofAdd (d x) * Multiplicative.ofAdd (d y)`. Rewrite using `[hadd]`. Use `rfl }`. Establish `hcomm : ∀ x ∈ commutator G, d x = 0`. Introduce `x hx`.

Use `Abelianization.commutator_subset_ker f hx` as an intermediate fact. Rewrite `this` using `[MonoidHom.mem_ker]`. Conclude with `this`. Establish `hcl : ∀ x ∈ (commutator G).topologicalClosure, d x = 0`. Introduce `x hx`.

Establish `hmemN : ∀ N : ℕ, d x ∈ (maximalIdeal c.O) ^ N`. Introduce `N`. Establish `hclosed` using `(hd N).isClosed_fiber 0`. Establish `hsub : ((commutator G : Subgroup G) : Set G) ⊆ {y | Ideal.Quotient.mk ((maximalIdeal c.O) ^ N) (d y) = 0}`. Introduce `y hy`.

Simplify using `only [Set.mem_setOf_eq]`. Rewrite using `[hcomm y hy, map_zero]`. Establish `hx' : x ∈ closure ((commutator G : Subgroup G) : Set G)`. Rewrite using `[← Subgroup.topologicalClosure_coe]`. Conclude with `hx`.

Establish `hfib` using `closure_minimal hsub hclosed hx'`. Simplify using `only [Set.mem_setOf_eq] at hfib`. Conclude with `Ideal.Quotient.eq_zero_iff_mem.mp hfib`. Establish `hbot` using `Ideal.iInf_pow_eq_bot_of_isLocalRing (maximalIdeal c.O) (maximalIdeal.isMaximal c.O).ne_top`. Establish `hin : d x ∈ ⨅ i, (maximalIdeal c.O) ^ i` using `(Submodule.mem_iInf _).mpr hmemN`.

Rewrite `hin` using `[hbot]`. Conclude with `(Submodule.mem_bot _).mp hin`. Establish `hg' : (QuotientGroup.mk' (commutator G).topologicalClosure g : TopologicalAbelianization G) ∈ CommGroup.primaryComponent (TopologicalAbelianization G) l` using `hg`. Take `⟨k, hk⟩` from `hg'`. Rewrite `hk` using `[← map_pow, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]`.

Establish `h0` using `hcl _ hk`. Establish `hdp : d (g ^ (l ^ k)) = (l ^ k) • d g` using `map_pow f g (l ^ k)`. Rewrite `h0` using `[hdp]`. Conclude with `(smul_eq_zero.mp h0).resolve_left (pow_ne_zero _ (Fact.out : l.Prime).ne_zero)`.
-/
theorem UpperTheory.V.Th.Nm.homMu :
    ∀ {l : ℕ} [Fact l.Prime] (c : Coef l) (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (d : G → c.O), AdicCont (maximalIdeal c.O) d → (∀ g h, d (g * h) = d g + d h) → ∀ g ∈ muG l G, d g = 0 := by
  intro l _ c G _ _ _ d hd hadd g hg
  have hd1 : d 1 = 0 := by
    have h := hadd 1 1
    rw [mul_one] at h
    simpa using h
  let f : G →* Multiplicative c.O :=
    { toFun := fun x => Multiplicative.ofAdd (d x)
      map_one' := by simp [hd1]
      map_mul' := fun x y => by
        show Multiplicative.ofAdd (d (x * y)) = Multiplicative.ofAdd (d x) * Multiplicative.ofAdd (d y)
        rw [hadd]; rfl }
  have hcomm : ∀ x ∈ commutator G, d x = 0 := by
    intro x hx
    have := Abelianization.commutator_subset_ker f hx
    rw [MonoidHom.mem_ker] at this
    exact this
  have hcl : ∀ x ∈ (commutator G).topologicalClosure, d x = 0 := by
    intro x hx
    have hmemN : ∀ N : ℕ, d x ∈ (maximalIdeal c.O) ^ N := by
      intro N
      have hclosed := (hd N).isClosed_fiber 0
      have hsub : ((commutator G : Subgroup G) : Set G) ⊆
          {y | Ideal.Quotient.mk ((maximalIdeal c.O) ^ N) (d y) = 0} := by
        intro y hy
        simp only [Set.mem_setOf_eq]
        rw [hcomm y hy, map_zero]
      have hx' : x ∈ closure ((commutator G : Subgroup G) : Set G) := by
        rw [← Subgroup.topologicalClosure_coe]; exact hx
      have hfib := closure_minimal hsub hclosed hx'
      simp only [Set.mem_setOf_eq] at hfib
      exact Ideal.Quotient.eq_zero_iff_mem.mp hfib
    have hbot := Ideal.iInf_pow_eq_bot_of_isLocalRing (maximalIdeal c.O) (maximalIdeal.isMaximal c.O).ne_top
    have hin : d x ∈ ⨅ i, (maximalIdeal c.O) ^ i := (Submodule.mem_iInf _).mpr hmemN
    rw [hbot] at hin
    exact (Submodule.mem_bot _).mp hin
  have hg' : (QuotientGroup.mk' (commutator G).topologicalClosure g : TopologicalAbelianization G) ∈
      CommGroup.primaryComponent (TopologicalAbelianization G) l := hg
  obtain ⟨k, hk⟩ := hg'
  rw [← map_pow, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hk
  have h0 := hcl _ hk
  have hdp : d (g ^ (l ^ k)) = (l ^ k) • d g := map_pow f g (l ^ k)
  rw [hdp] at h0
  exact (smul_eq_zero.mp h0).resolve_left (pow_ne_zero _ (Fact.out : l.Prime).ne_zero)

import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.UnipotentIdempotents.TCont

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws GlobalTheory.GalOfCusp UpperTheory.V.Ws.Lk

/- English proof (translation)
Introduce `l _ L Ω _ _ _ _ _ _ s V`. Use `⟨fun x => ?_, fun t => ?_, fun O _ _ R _ _ g => ?_, fun v g hg => ?_⟩` and prove the remaining obligations. Take `⟨y, hy⟩ : ∃ y, toGS Ω V.S' y = x.1` from `QuotientGroup.mk'_surjective _ x.1`. Take `⟨t, rfl⟩ : y ∈ (W.resP L Ω).range` from `(V.hη y).1 (by rw [hy]; exact x.2)`. Conclude with `⟨t, Subtype.ext hy⟩`.

Choose the witnesses or unpack the hypotheses as in `⟨t', ht'⟩ : s.c * W.resP L Ω t * s.c⁻¹ ∈ (W.resP L Ω).range := by`. Rewrite using `[← V.hη, map_mul (toGS Ω V.S'), map_mul (toGS Ω V.S'), map_inv (toGS Ω V.S')]`. Conclude with `(V.frame.conj (V.pr t)).2`. Use `⟨t', ht', Subtype.ext ?_⟩` and prove the remaining obligations. Use `show toGS Ω V.S' s.c * toGS Ω V.S' (W.resP L Ω t) * (toGS Ω V.S' s.c)⁻¹ = toGS Ω V.S' (W.resP L Ω t')`.

Rewrite using `[ht', map_mul, map_mul, map_inv]`. Establish `h : V.ε (toGS Ω V.S' (W.resP L Ω g)) = cycZ L Ω l g` using `DFunLike.congr_fun V.hε (W.resP L Ω g) show algebraMap O R (algebraMap ℤ_[l] O (V.ε (toGS Ω V.S' (W.resP L Ω g)) : ℤ_[l]ˣ)) = _`. Rewrite using `[h]`. Both sides reduce to the same expression. Establish `hg' : (QuotientGroup.mk' _ g : TopologicalAbelianization (Dec (F` using `L) (s.A v))) ∈ CommGroup.primaryComponent (TopologicalAbelianization (Dec (F := L) (s.A v))) l := hg`.

Take `⟨a, ha⟩ : ∃ a : ℕ, (QuotientGroup.mk' _ g : TopologicalAbelianization (Dec (F` from `L) (s.A v))) ^ l ^ a = 1 := by first`. Consider the case `exact exists_orderOf_eq_prime_pow_iff.1 hg'`. Consider the case `exact hg'`. Consider the case `simpa using hg'`. Use `⟨a, ?_⟩` and prove the remaining obligations.

Rewrite `ha` using `[← map_pow, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]`. Establish `hle : (commutator (Dec (F` using `L) (s.A v))).topologicalClosure ≤ (commutator (G L Ω)).topologicalClosure.comap (Dec (F := L) (s.A v)).subtype := by`. Use `Subgroup.topologicalClosure_minimal _ ?_ ((Subgroup.isClosed_topologicalClosure _).preimage continuous_subtype_val)` and prove the remaining obligations. Rewrite using `[← Subgroup.map_le_iff_le_comap, commutator_def, Subgroup.map_commutator]`. Conclude with `(Subgroup.commutator_mono le_top le_top).trans (Subgroup.le_topologicalClosure _)`.

Conclude with `hle ha`.
-/
theorem UpperTheory.V.Ws.Lk.prFacts :
    ∀ (l : ℕ) [Fact l.Prime] (L Ω : Type) [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] (s : W.HidaSetting l L Ω) (V : s.Lev), Function.Surjective V.pr ∧ (∀ g : G L Ω, ∃ g' : G L Ω, W.resP L Ω g' = s.c * W.resP L Ω g * s.c⁻¹ ∧ V.frame.conj (V.pr g) = V.pr g') ∧ (∀ (O : Type) [CommRing O] [Algebra ℤ_[l] O] (R : Type) [CommRing R] [Algebra O R] (g : G L Ω), (V.frame.eps O R (V.pr g) : R) = algebraMap O R (chiO L Ω l O g)) ∧ ∀ (v : W.Vl l L) (g : Dec (F := L) (s.A v)), g ∈ V.frame.mu v → ∃ a : ℕ, (g : G L Ω) ^ l ^ a ∈ (commutator (G L Ω)).topologicalClosure := by
  intro l _ L Ω _ _ _ _ _ _ s V
  refine ⟨fun x => ?_, fun t => ?_, fun O _ _ R _ _ g => ?_, fun v g hg => ?_⟩
  · obtain ⟨y, hy⟩ : ∃ y, toGS Ω V.S' y = x.1 := QuotientGroup.mk'_surjective _ x.1
    obtain ⟨t, rfl⟩ : y ∈ (W.resP L Ω).range := (V.hη y).1 (by rw [hy]; exact x.2)
    exact ⟨t, Subtype.ext hy⟩
  · obtain ⟨t', ht'⟩ : s.c * W.resP L Ω t * s.c⁻¹ ∈ (W.resP L Ω).range := by
      rw [← V.hη, map_mul (toGS Ω V.S'), map_mul (toGS Ω V.S'), map_inv (toGS Ω V.S')]
      exact (V.frame.conj (V.pr t)).2
    refine ⟨t', ht', Subtype.ext ?_⟩
    show toGS Ω V.S' s.c * toGS Ω V.S' (W.resP L Ω t) * (toGS Ω V.S' s.c)⁻¹ = toGS Ω V.S' (W.resP L Ω t')
    rw [ht', map_mul, map_mul, map_inv]
  · have h : V.ε (toGS Ω V.S' (W.resP L Ω g)) = cycZ L Ω l g := DFunLike.congr_fun V.hε (W.resP L Ω g)
    show algebraMap O R (algebraMap ℤ_[l] O (V.ε (toGS Ω V.S' (W.resP L Ω g)) : ℤ_[l]ˣ)) = _
    rw [h]
    rfl
  · have hg' : (QuotientGroup.mk' _ g : TopologicalAbelianization (Dec (F := L) (s.A v))) ∈
        CommGroup.primaryComponent (TopologicalAbelianization (Dec (F := L) (s.A v))) l := hg
    obtain ⟨a, ha⟩ : ∃ a : ℕ, (QuotientGroup.mk' _ g : TopologicalAbelianization (Dec (F := L) (s.A v))) ^ l ^ a = 1 := by
      first
      | exact exists_orderOf_eq_prime_pow_iff.1 hg'
      | exact hg'
      | simpa using hg'
    refine ⟨a, ?_⟩
    rw [← map_pow, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at ha
    have hle : (commutator (Dec (F := L) (s.A v))).topologicalClosure ≤
        (commutator (G L Ω)).topologicalClosure.comap (Dec (F := L) (s.A v)).subtype := by
      refine Subgroup.topologicalClosure_minimal _ ?_
        ((Subgroup.isClosed_topologicalClosure _).preimage continuous_subtype_val)
      rw [← Subgroup.map_le_iff_le_comap, commutator_def, Subgroup.map_commutator]
      exact (Subgroup.commutator_mono le_top le_top).trans (Subgroup.le_topologicalClosure _)
    exact hle ha

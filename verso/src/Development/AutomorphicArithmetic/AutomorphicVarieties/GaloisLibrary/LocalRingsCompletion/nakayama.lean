import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.LocalRingsCompletion.IsCharOneOfSubsingleton

open PowerSeries IsLocalRing UpperTheory.V.abelian₂
open IsDiscreteValuationRing (addVal)
open scoped Pointwise TensorProduct Topology

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `hx`. Use `Submodule.smul_induction_on hx (fun a ha y _ i => ?_) (fun a b ha hb i => ?_)` and prove the remaining obligations. Conclude with `J.mul_mem_right _ ha`. Conclude with `J.add_mem (ha i) (hb i)`.

Introduce `hx`. Rewrite using `[pi_eq_sum_univ x]`. Conclude with `Submodule.sum_mem _ fun i _ => Submodule.smul_mem_smul (hx i) Submodule.mem_top`.
-/
private theorem mem_smul_top_pi {R : Type} [CommRing R] (J : Ideal R) {r : ℕ} (x : Fin r → R) :
    x ∈ J • (⊤ : Submodule R (Fin r → R)) ↔ ∀ i, x i ∈ J := by
  constructor
  · intro hx
    refine Submodule.smul_induction_on hx (fun a ha y _ i => ?_) (fun a b ha hb i => ?_)
    · exact J.mul_mem_right _ ha
    · exact J.add_mem (ha i) (hb i)
  · intro hx
    rw [pi_eq_sum_univ x]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem_smul (hx i) Submodule.mem_top

/- English proof (translation)
Use `⟨fun {f} hf => ?_⟩` and prove the remaining obligations. Establish `hc : ∀ i : Fin r, ∃ L : R, ∀ n, f n i ≡ L [SMOD (I ^ n • ⊤ : Submodule R R)]`. Introduce `i`. Use `IsPrecomplete.prec' (f := fun n => f n i) ?_` and prove the remaining obligations. Introduce `m n hmn`.

Establish `h` using `hf hmn`. Rewrite `h`, the goal using `[SModEq.sub_mem]`. Rewrite `h` using `[mem_smul_top_pi]`. Use `h i` as an intermediate fact. Simplify `this` using `[Ideal.smul_top_eq_map, smul_eq_mul, Ideal.mul_top]`.

Use `choose L hL using hc`. Use `⟨L, fun n => ?_⟩` and prove the remaining obligations. Rewrite using `[SModEq.sub_mem, mem_smul_top_pi]`. Introduce `i`. Use `hL i n` as an intermediate fact.

Rewrite `this` using `[SModEq.sub_mem]`. Simplify `this` using `[smul_eq_mul, Ideal.mul_top]`.
-/
private theorem isPrecomplete_pi {R : Type} [CommRing R] (I : Ideal R) [IsPrecomplete I R] (r : ℕ) :
    IsPrecomplete I (Fin r → R) := by
  refine ⟨fun {f} hf => ?_⟩
  have hc : ∀ i : Fin r, ∃ L : R, ∀ n, f n i ≡ L [SMOD (I ^ n • ⊤ : Submodule R R)] := by
    intro i
    refine IsPrecomplete.prec' (f := fun n => f n i) ?_
    intro m n hmn
    have h := hf hmn
    rw [SModEq.sub_mem] at h ⊢
    rw [mem_smul_top_pi] at h
    have := h i
    simpa [Ideal.smul_top_eq_map, smul_eq_mul, Ideal.mul_top] using this
  choose L hL using hc
  refine ⟨L, fun n => ?_⟩
  rw [SModEq.sub_mem, mem_smul_top_pi]
  intro i
  have := hL i n
  rw [SModEq.sub_mem] at this
  simpa [smul_eq_mul, Ideal.mul_top] using this

/- English proof (translation)
Introduce `R _ I _ M _ _ _`. Establish `part1 : ∀ (r : ℕ) (s : Fin r → M), Submodule.span R (Set.range s) ⊔ I • (⊤ : Submodule R M) = ⊤ → Submodule.span R (Set.range s) = ⊤`. Introduce `r s hs`. Establish `hsurj : Function.Surjective (Fintype.linearCombination R s)` using `by haveI := isPrecomplete_pi I r`. Apply `surjective_of_mkQ_comp_surjective (I := I)` to reduce the goal to its premises.

Introduce `q`. Take `⟨m, rfl⟩` from `Submodule.Quotient.mk_surjective _ q`. Establish `hm : m ∈ Submodule.span R (Set.range s) ⊔ I • (⊤ : Submodule R M)`. Rewrite using `[hs]`. Conclude with `Submodule.mem_top`.

Take `⟨a, ha, b, hb, rfl⟩` from `Submodule.mem_sup.mp hm`. Rewrite `ha` using `[← Fintype.range_linearCombination, LinearMap.mem_range]`. Take `⟨c, rfl⟩` from `ha`. Use `⟨c, ?_⟩` and prove the remaining obligations. Simplify using `only [LinearMap.coe_comp, Function.comp_apply, Submodule.mkQ_apply]`.

Rewrite using `[Submodule.Quotient.eq]`. Simplify using `using Submodule.neg_mem _ hb`. Rewrite using `[← Fintype.range_linearCombination, LinearMap.range_eq_top]`. Conclude with `hsurj`. Use `⟨part1, ?_⟩` and prove the remaining obligations.

Introduce `hfin`. Take `⟨r, s, hs⟩` from `Module.Finite.exists_fin (R := R) (M := M ⧸ I • (⊤ : Submodule R M))`. Use `choose t ht using fun i => Submodule.Quotient.mk_surjective (I • (⊤ : Submodule R M)) (s i)`. Establish `hsup : Submodule.span R (Set.range t) ⊔ I • (⊤ : Submodule R M) = ⊤`. Rewrite using `[sup_comm, ← Submodule.comap_map_mkQ, Submodule.map_span, ← Set.range_comp]`.

Establish `hcomp : (I • (⊤ : Submodule R M)).mkQ ∘ t = s` using `funext fun i => ht i`. Rewrite using `[hcomp, hs, Submodule.comap_top]`. Establish `htop` using `part1 r t hsup`. Conclude with `⟨Submodule.fg_def.2 ⟨Set.range t, Set.finite_range t, htop⟩⟩`.
-/
theorem UpperTheory.V.abelian₂.nakayama :
    ∀ (R : Type) [CommRing R] (I : Ideal R) [IsPrecomplete I R] (M : Type) [AddCommGroup M] [Module R M] [IsHausdorff I M],
      (∀ (r : ℕ) (s : Fin r → M), Submodule.span R (Set.range s) ⊔ I • (⊤ : Submodule R M) = ⊤ →
        Submodule.span R (Set.range s) = ⊤) ∧
      (Module.Finite R (M ⧸ I • (⊤ : Submodule R M)) → Module.Finite R M) := by
  intro R _ I _ M _ _ _
  have part1 : ∀ (r : ℕ) (s : Fin r → M), Submodule.span R (Set.range s) ⊔ I • (⊤ : Submodule R M) = ⊤ →
      Submodule.span R (Set.range s) = ⊤ := by
    intro r s hs
    have hsurj : Function.Surjective (Fintype.linearCombination R s) := by
      haveI := isPrecomplete_pi I r
      apply surjective_of_mkQ_comp_surjective (I := I)
      intro q
      obtain ⟨m, rfl⟩ := Submodule.Quotient.mk_surjective _ q
      have hm : m ∈ Submodule.span R (Set.range s) ⊔ I • (⊤ : Submodule R M) := by
        rw [hs]; exact Submodule.mem_top
      obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp hm
      rw [← Fintype.range_linearCombination, LinearMap.mem_range] at ha
      obtain ⟨c, rfl⟩ := ha
      refine ⟨c, ?_⟩
      simp only [LinearMap.coe_comp, Function.comp_apply, Submodule.mkQ_apply]
      rw [Submodule.Quotient.eq]
      simpa using Submodule.neg_mem _ hb
    rw [← Fintype.range_linearCombination, LinearMap.range_eq_top]
    exact hsurj
  refine ⟨part1, ?_⟩
  intro hfin
  obtain ⟨r, s, hs⟩ := Module.Finite.exists_fin (R := R) (M := M ⧸ I • (⊤ : Submodule R M))
  choose t ht using fun i => Submodule.Quotient.mk_surjective (I • (⊤ : Submodule R M)) (s i)
  have hsup : Submodule.span R (Set.range t) ⊔ I • (⊤ : Submodule R M) = ⊤ := by
    rw [sup_comm, ← Submodule.comap_map_mkQ, Submodule.map_span, ← Set.range_comp]
    have hcomp : (I • (⊤ : Submodule R M)).mkQ ∘ t = s := funext fun i => ht i
    rw [hcomp, hs, Submodule.comap_top]
  have htop := part1 r t hsup
  exact ⟨Submodule.fg_def.2 ⟨Set.range t, Set.finite_range t, htop⟩⟩

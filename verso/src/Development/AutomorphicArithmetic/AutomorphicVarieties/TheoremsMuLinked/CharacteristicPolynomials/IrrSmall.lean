import Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.OrdZero
import Development.AutomorphicArithmetic.AutomorphicVarieties.CurveDVRSpecialization.IsUnitOrIsUnitOfAddOne
import Development.AutomorphicArithmetic.AutomorphicVarieties.CurveDVRSpecialization.IrrNormal
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeilGroupCharacters.UniversalOrdinaryDeterminantRing

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing Polynomial Matrix UpperTheory.V UpperTheory.V.HV UpperTheory.V.Alg GlobalTheory.GalOfCusp

/- English proof (translation)
Take `⟨g, hg⟩` from `h`. Establish `h1` using `Matrix.charpoly_units_conj g (Pr.gm r s)`. Establish `h2 : ((g * r s * g⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k).BlockTriangular id` using `fun i j hij => (hg s).1 i j hij`. Establish `h3` using `Matrix.charpoly_of_upperTriangular _ h2`. Rewrite using `[← h1]`.

Simplify using `only [Units.val_mul, Matrix.coe_units_inv] at h3`. Rewrite using `[h3]`. Use `Finset.prod_congr rfl fun i _ => ?_` and prove the remaining obligations. Establish `h4` using `(hg s).2 i`. Simplify using `only [Units.val_mul, Matrix.coe_units_inv] at h4`.

Rewrite using `[h4]`.
-/
private theorem charpoly_flag {H k : Type} [Group H] [CommRing k] {n : ℕ} (r : H →* GL (Fin n) k)
    (κ : Fin n → H →* kˣ) (h : W.HasFlag r κ) (s : H) : (Pr.gm r s).charpoly = Pr.chPoly κ s := by
  obtain ⟨g, hg⟩ := h
  have h1 := Matrix.charpoly_units_conj g (Pr.gm r s)
  have h2 : ((g * r s * g⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k).BlockTriangular id :=
    fun i j hij => (hg s).1 i j hij
  have h3 := Matrix.charpoly_of_upperTriangular _ h2
  rw [← h1]
  simp only [Units.val_mul, Matrix.coe_units_inv] at h3
  rw [h3]
  refine Finset.prod_congr rfl fun i _ => ?_
  have h4 := (hg s).2 i
  simp only [Units.val_mul, Matrix.coe_units_inv] at h4
  rw [h4]

/- English proof (translation)
Establish `h3` using `congrArg (Polynomial.eval (x a)) h`. Rewrite `h3` using `[Polynomial.eval_prod, Polynomial.eval_prod, Finset.prod_eq_zero (f := fun i => Polynomial.eval (x a) (X - C (x i))) (Finset.mem_univ a) (by simp), eq_comm, Finset.prod_eq_zero_iff]`. Take `⟨i, _, h4⟩` from `h3`. Rewrite using `[← hy i]`. Simplify `h4` using `[sub_eq_zero]`.
-/
private theorem root_eq {k : Type} [Field k] {n : ℕ} (x y : Fin n → k) (c : k) (hy : ∀ i, y i = c)
    (h : ∏ i, (X - C (x i)) = ∏ i, (X - C (y i))) (a : Fin n) : x a = c := by
  have h3 := congrArg (Polynomial.eval (x a)) h
  rw [Polynomial.eval_prod, Polynomial.eval_prod,
    Finset.prod_eq_zero (f := fun i => Polynomial.eval (x a) (X - C (x i))) (Finset.mem_univ a) (by simp),
    eq_comm, Finset.prod_eq_zero_iff] at h3
  obtain ⟨i, _, h4⟩ := h3
  rw [← hy i]
  simpa [sub_eq_zero] using h4

/- English proof (translation)
Introduce `K k B G D _ _ _ _ _ _ _ _ _ n hn G' _ ρ j φ χ ι ψ ψb hirr hj hred hflag hlift hfree hne U hU`. Establish `hfi : U.FiniteIndex` using `by haveI := Subgroup.quotient_finite_of_isOpen U hU`. Conclude with `Subgroup.finiteIndex_of_finite_quotient`. Establish `hch : ∀ g, (Pr.gm ρ (ι g)).charpoly = Pr.chPoly ψ g` using `fun g => charpoly_flag _ _ hflag g`. Establish `key` using `Pr.irrNormal G K k B n hn ρ hirr j φ χ hj hred D ι ψ hch (U.normalCore ⊓ G') (fun a b hab => ?_) ?_`.

Introduce `W hW`. Conclude with `key W fun g hg => hW g ⟨U.normalCore_le hg.1, hg.2⟩`. Take `⟨g, hg, hfr⟩` from `hfree`. Establish `hpos : 0 < U.normalCore.index` using `Nat.pos_of_ne_zero Subgroup.FiniteIndex.index_ne_zero`. Use `⟨g ^ U.normalCore.index, ?_, ?_⟩` and prove the remaining obligations.

Rewrite using `[map_pow]`. Conclude with `⟨U.normalCore.pow_index_mem _, G'.pow_mem hg _⟩`. Rewrite using `[map_pow, map_pow]`. Conclude with `hfr a b hab _ hpos`. Take `⟨a, b, g, hab⟩` from `hne`.

Assume the negation of the conclusion as `hcon`. Use `push Not at hcon`. Apply `hab` to reduce the goal to its premises. Use `choose c hc1 hc2 using fun i => hlift i g`. Take `⟨p, hp1, hp2⟩` from `hred (ι g)`.

Establish `hp : p = ∏ i, (X - C (c i))`. Apply `Polynomial.map_injective j hj` to reduce the goal to its premises. Rewrite using `[hp1, hch, Pr.chPoly, Polynomial.map_prod]`. Simplify using `only [Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C, hc1]`. Rewrite `hp2` using `[hp, Pr.chPoly, Polynomial.map_prod]`.

Simplify using `only [Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C, hc2] at hp2`. Establish `h` using `root_eq (fun i => ((ψb i g : kˣ) : k)) (fun i => ((χ i (ι g) : kˣ) : k)) (χ a (ι g) : kˣ) (fun i => by rw [hcon i a g]) hp2`. Conclude with `Units.ext ((h a).trans (h b).symm)`.
-/
theorem UpperTheory.V.Th.Det.irrSmall :
    ∀ {K k B G D : Type} [Field K] [IsAlgClosed K] [Field k] [CommRing B] [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] [Group D] {n : ℕ}, n.Prime → ∀ (G' : Subgroup G) [G'.Normal] (ρ : G →* GL (Fin n) K) (j : B →+* K) (φ : B →+* k) (χ : Fin n → G →* kˣ) (ι : D →* G) (ψ : Fin n → D →* Kˣ) (ψb : Fin n → D →* kˣ), U3.MatIrr ⊤ (W.mat ρ) → Function.Injective j → Pr.RedTo ρ j φ χ → W.HasFlag (ρ.comp ι) ψ → (∀ i g, ∃ a : B, j a = (ψ i g : K) ∧ φ a = (ψb i g : k)) → (∃ g, ι g ∈ G' ∧ Pr.FreeRatios fun i => ψ i g) → (∃ a b g, ψb a g ≠ ψb b g) → ∀ U : Subgroup G, IsOpen (U : Set G) → U3.MatIrr (U ⊓ G') (W.mat ρ) := by
  intro K k B G D _ _ _ _ _ _ _ _ _ n hn G' _ ρ j φ χ ι ψ ψb hirr hj hred hflag hlift hfree hne U hU
  classical
  have hfi : U.FiniteIndex := by
    haveI := Subgroup.quotient_finite_of_isOpen U hU
    exact Subgroup.finiteIndex_of_finite_quotient
  have hch : ∀ g, (Pr.gm ρ (ι g)).charpoly = Pr.chPoly ψ g := fun g => charpoly_flag _ _ hflag g
  have key := Pr.irrNormal G K k B n hn ρ hirr j φ χ hj hred D ι ψ hch (U.normalCore ⊓ G') (fun a b hab => ?_) ?_
  · intro W hW
    exact key W fun g hg => hW g ⟨U.normalCore_le hg.1, hg.2⟩
  · obtain ⟨g, hg, hfr⟩ := hfree
    have hpos : 0 < U.normalCore.index := Nat.pos_of_ne_zero Subgroup.FiniteIndex.index_ne_zero
    refine ⟨g ^ U.normalCore.index, ?_, ?_⟩
    · rw [map_pow]
      exact ⟨U.normalCore.pow_index_mem _, G'.pow_mem hg _⟩
    · rw [map_pow, map_pow]
      exact hfr a b hab _ hpos
  · obtain ⟨a, b, g, hab⟩ := hne
    by_contra hcon
    push Not at hcon
    apply hab
    choose c hc1 hc2 using fun i => hlift i g
    obtain ⟨p, hp1, hp2⟩ := hred (ι g)
    have hp : p = ∏ i, (X - C (c i)) := by
      apply Polynomial.map_injective j hj
      rw [hp1, hch, Pr.chPoly, Polynomial.map_prod]
      simp only [Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C, hc1]
    rw [hp, Pr.chPoly, Polynomial.map_prod] at hp2
    simp only [Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C, hc2] at hp2
    have h := root_eq (fun i => ((ψb i g : kˣ) : k)) (fun i => ((χ i (ι g) : kˣ) : k)) (χ a (ι g) : kˣ)
      (fun i => by rw [hcon i a g]) hp2
    exact Units.ext ((h a).trans (h b).symm)

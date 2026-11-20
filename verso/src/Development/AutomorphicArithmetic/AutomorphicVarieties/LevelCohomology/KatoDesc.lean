import Mathlib
import Development.AutomorphicArithmetic.AutomorphicVarieties.PublishedTheorems.QuotRepMk
import Development.AutomorphicArithmetic.AutomorphicVarieties.LevelCohomology.KatoBkMap
import Development.AutomorphicArithmetic.AutomorphicVarieties.LevelCohomology.KatoFinExt
import Development.AutomorphicArithmetic.AutomorphicVarieties.LevelCohomology.KatoBasis

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published.Kato

/- English proof (translation)
Introduce `l _ F Ω _ _ _ _ _ E _ n r h c hc hbk`. Use `haveI : IsGalois F Ω := {}`. Take `⟨E', hE', hle, hmem⟩` from `UpperTheory.V.X.Kato.finExt l (G F Ω) E n r c hc`. Take `⟨d, ε, π, hsum, hcont⟩` from `UpperTheory.V.X.Kato.basis l E E' hle`. Take `⟨hcc, hcoc⟩` from `(mem_Z1_iff_cocycle _ _).1 hc`.

Set `f : Fin d → ((Fin n → Qbar l) →ₗ[ℚ_[l]] (Fin n → ↥E))` to `fun i => ((π i).restrictScalars ℚ_[l]).compLeft (Fin n)`. Establish `hf : ∀ i g x, f i (Loc.colRep (toBar r) g x) = Loc.colRep r g (f i x)`. Introduce `i g x`. Use function extensionality and compare the values at `j`. Use `show π i (∑ k, ((r g : Matrix (Fin n) (Fin n) ↥E) j k : Qbar l) * x k) = ∑ k, (r g : Matrix (Fin n) (Fin n) ↥E) j k * π i (x k)`.

Rewrite using `[map_sum]`. Use `Finset.sum_congr rfl fun k _ => ?_` and prove the remaining obligations. Conclude with `(π i).map_smul ((r g : Matrix (Fin n) (Fin n) ↥E) j k) (x k)`. Establish `hfc : ∀ i, Continuous fun g => f i (c g)` using `fun i => continuous_pi fun j => (hcont i).comp_continuous ((continuous_apply j).comp hcc) fun g => hmem g j`. Establish `hB : ∀ i, ∃ m : Fin n → ↥E, ∀ g, f i (c g) = Loc.colRep r g m - m` using `fun i => by`.

Use `(mem_coboundaries1 _ _).1 (h (fun g => f i (c g)) ((mem_Z1_iff_cocycle _ _).2 ⟨hfc i, fun g g' => ?_⟩) ?_)` and prove the remaining obligations. Rewrite using `[hcoc, map_add, hf]`. Conclude with `UpperTheory.V.X.Kato.bkMap l F Ω _ _ _ _ _ _ (f i) (hf i) c (hfc i) hbk`. Use `choose m hm using hB`. Use `(mem_coboundaries1 _ _).2 ⟨fun j => ∑ i, ε i * (m i j : Qbar l), fun g => ?_⟩` and prove the remaining obligations.

Use function extensionality and compare the values at `j`. Establish `h1 : ∀ i, (π i (c g j) : Qbar l) = (∑ k, ((r g : Matrix (Fin n) (Fin n) ↥E) j k : Qbar l) * (m i k : Qbar l)) - (m i j : Qbar l)` using `fun i => by`. Establish `h2 : π i (c g j) = (∑ k, (r g : Matrix (Fin n) (Fin n) ↥E) j k * m i k) - m i j` using `congrFun (hm i g) j`. Rewrite using `[h2]`. Use `push_cast`.

Both sides reduce to the same expression. Use `show c g j = (∑ k, ((r g : Matrix (Fin n) (Fin n) ↥E) j k : Qbar l) * ∑ i, ε i * (m i k : Qbar l)) - ∑ i, ε i * (m i j : Qbar l)`. Rewrite using `[hsum _ (hmem g j)]`. Simplify using `only [h1, mul_sub, Finset.sum_sub_distrib, Finset.mul_sum]`. Use `congr 1`.

Rewrite using `[Finset.sum_comm]`. Conclude with `Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun i _ => by ring`.
-/
theorem UpperTheory.V.X.Kato.desc :
    ∀ (l : ℕ) [Fact l.Prime] (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (E : IntermediateField ℚ_[l] (Qbar l)) [FiniteDimensional ℚ_[l] ↥E] (n : ℕ) (r : G F Ω →* GL (Fin n) ↥E), BlochKatoSelmerVanishes l (Loc.colRep r) → BlochKatoSelmerVanishes l (Loc.colRep (toBar r)) := by
  intro l _ F Ω _ _ _ _ _ E _ n r h c hc hbk
  haveI : IsGalois F Ω := {}
  obtain ⟨E', hE', hle, hmem⟩ := UpperTheory.V.X.Kato.finExt l (G F Ω) E n r c hc
  obtain ⟨d, ε, π, hsum, hcont⟩ := UpperTheory.V.X.Kato.basis l E E' hle
  obtain ⟨hcc, hcoc⟩ := (mem_Z1_iff_cocycle _ _).1 hc
  let f : Fin d → ((Fin n → Qbar l) →ₗ[ℚ_[l]] (Fin n → ↥E)) := fun i =>
    ((π i).restrictScalars ℚ_[l]).compLeft (Fin n)
  have hf : ∀ i g x, f i (Loc.colRep (toBar r) g x) = Loc.colRep r g (f i x) := by
    intro i g x
    funext j
    show π i (∑ k, ((r g : Matrix (Fin n) (Fin n) ↥E) j k : Qbar l) * x k) =
      ∑ k, (r g : Matrix (Fin n) (Fin n) ↥E) j k * π i (x k)
    rw [map_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    exact (π i).map_smul ((r g : Matrix (Fin n) (Fin n) ↥E) j k) (x k)
  have hfc : ∀ i, Continuous fun g => f i (c g) := fun i =>
    continuous_pi fun j =>
      (hcont i).comp_continuous ((continuous_apply j).comp hcc) fun g => hmem g j
  have hB : ∀ i, ∃ m : Fin n → ↥E, ∀ g, f i (c g) = Loc.colRep r g m - m := fun i => by
    refine (mem_coboundaries1 _ _).1 (h (fun g => f i (c g)) ((mem_Z1_iff_cocycle _ _).2 ⟨hfc i, fun g g' => ?_⟩) ?_)
    · rw [hcoc, map_add, hf]
    · exact UpperTheory.V.X.Kato.bkMap l F Ω _ _ _ _ _ _ (f i) (hf i) c (hfc i) hbk
  choose m hm using hB
  refine (mem_coboundaries1 _ _).2 ⟨fun j => ∑ i, ε i * (m i j : Qbar l), fun g => ?_⟩
  funext j
  have h1 : ∀ i, (π i (c g j) : Qbar l) =
      (∑ k, ((r g : Matrix (Fin n) (Fin n) ↥E) j k : Qbar l) * (m i k : Qbar l)) - (m i j : Qbar l) := fun i => by
    have h2 : π i (c g j) = (∑ k, (r g : Matrix (Fin n) (Fin n) ↥E) j k * m i k) - m i j := congrFun (hm i g) j
    rw [h2]
    push_cast
    rfl
  show c g j = (∑ k, ((r g : Matrix (Fin n) (Fin n) ↥E) j k : Qbar l) * ∑ i, ε i * (m i k : Qbar l)) -
    ∑ i, ε i * (m i j : Qbar l)
  rw [hsum _ (hmem g j)]
  simp only [h1, mul_sub, Finset.sum_sub_distrib, Finset.mul_sum]
  congr 1
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun i _ => by ring

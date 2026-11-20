import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.BlockMatrixPlaces.BlockDiagonalOrdinaryGSpRep

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws UpperTheory.V.Ws.Bl

/- English proof (translation)
Introduce `A _ _ _ T _ _ _ _ Γ _ _ ρ c N H P n z y hz`. Establish `eqv : ∀ (g : Γ) (w : T ⧸ lev A T (n + 1)), redn A T n (modRep ρ (n + 1) g w) = modRep ρ n g (redn A T n w)`. Introduce `g w`. Take `⟨x, rfl⟩` from `(lev A T (n + 1)).mkQ_surjective w`. Rewrite using `[modRep_mk, redn_mk, redn_mk, modRep_mk]`.

Establish `img : ∀ (Q : Submodule A T) (w : T ⧸ lev A T (n + 1)), w ∈ Q.map (lev A T (n + 1)).mkQ → redn A T n w ∈ Q.map (lev A T n).mkQ`. Introduce and unpack `Q _ ⟨x, hx, rfl⟩`. Conclude with `⟨x, hx, rfl⟩`. Use `⟨⟨hz.lc.comp (redn A T n), fun g h => ?_, ?_, fun g hg => ?_, fun h hh => ?_⟩, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[hz.coc, map_add, eqv]`.

Rewrite using `[hz.cz, map_zero]`. Rewrite using `[hz.kill g hg, map_zero]`. Use `img P _ (hz.loc h hh)` as an intermediate fact. Rewrite `this` using `[map_sub, map_sub, eqv]`. Conclude with `this`.

Introduce and unpack `⟨g, hg⟩ hn`. Use `⟨g, fun hm => hg ?_⟩` and prove the remaining obligations. Take `⟨x, hx⟩` from `(lev A T (n + 1)).mkQ_surjective (z g)`. Take `⟨x', hx', e⟩` from `hm`. Establish `e' : (lev A T n).mkQ x' = (lev A T n).mkQ x` using `by rw [e, ← redn_mk, hx]`.

Establish `hd : x' - x ∈ lev A T n` using `(Submodule.Quotient.eq _).1 e'`. Establish `hle : lev A T n ≤ lev A T 1` using `Submodule.smul_mono_left (Ideal.pow_le_pow_right hn)`. Use `⟨x, ?_, hx⟩` and prove the remaining obligations. Use `(lev A T 1).sub_mem hx' (hle hd)` as an intermediate fact. Rewrite `this` using `[sub_sub_cancel]`. Then use the resulting hypothesis.

Introduce and unpack `⟨g, hg⟩`. Conclude with `⟨g, fun hm => hg (img _ _ hm)⟩`.
-/
theorem UpperTheory.V.Ws.Bl.redMem :
    ∀ (A : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] (T : Type) [AddCommGroup T] [Module A T] [Module.Finite A T] [Module.Free A T] (Γ : Type) [Group Γ] [TopologicalSpace Γ] (ρ : Representation A Γ T) (c : Γ) (N : Set Γ) (H : Subgroup Γ) (P : Submodule A T) (n : ℕ) z y, IsZn ρ c N H P (n + 1) z y → IsZn ρ c N H P n (fun g => redn A T n (z g)) (redn A T n y) ∧
          (Prim z → 0 < n → Prim fun g => redn A T n (z g)) ∧ (Prim (fun g => redn A T n (z g)) → Prim z) := by
  intro A _ _ _ T _ _ _ _ Γ _ _ ρ c N H P n z y hz
  have eqv : ∀ (g : Γ) (w : T ⧸ lev A T (n + 1)),
      redn A T n (modRep ρ (n + 1) g w) = modRep ρ n g (redn A T n w) := by
    intro g w
    obtain ⟨x, rfl⟩ := (lev A T (n + 1)).mkQ_surjective w
    rw [modRep_mk, redn_mk, redn_mk, modRep_mk]
  have img : ∀ (Q : Submodule A T) (w : T ⧸ lev A T (n + 1)), w ∈ Q.map (lev A T (n + 1)).mkQ →
      redn A T n w ∈ Q.map (lev A T n).mkQ := by
    rintro Q _ ⟨x, hx, rfl⟩
    exact ⟨x, hx, rfl⟩
  refine ⟨⟨hz.lc.comp (redn A T n), fun g h => ?_, ?_, fun g hg => ?_, fun h hh => ?_⟩, ?_, ?_⟩
  · rw [hz.coc, map_add, eqv]
  · rw [hz.cz, map_zero]
  · rw [hz.kill g hg, map_zero]
  · have := img P _ (hz.loc h hh)
    rw [map_sub, map_sub, eqv] at this
    exact this
  · rintro ⟨g, hg⟩ hn
    refine ⟨g, fun hm => hg ?_⟩
    obtain ⟨x, hx⟩ := (lev A T (n + 1)).mkQ_surjective (z g)
    obtain ⟨x', hx', e⟩ := hm
    have e' : (lev A T n).mkQ x' = (lev A T n).mkQ x := by rw [e, ← redn_mk, hx]
    have hd : x' - x ∈ lev A T n := (Submodule.Quotient.eq _).1 e'
    have hle : lev A T n ≤ lev A T 1 := Submodule.smul_mono_left (Ideal.pow_le_pow_right hn)
    refine ⟨x, ?_, hx⟩
    have := (lev A T 1).sub_mem hx' (hle hd)
    rwa [sub_sub_cancel] at this
  · rintro ⟨g, hg⟩
    exact ⟨g, fun hm => hg (img _ _ hm)⟩

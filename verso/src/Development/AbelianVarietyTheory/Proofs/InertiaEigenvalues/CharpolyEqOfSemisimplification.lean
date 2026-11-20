import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.QuotientHomNonvanishingBound
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.SemisimplificationConstituents
import Development.AbelianVarietyTheory.Proofs.CharacterTheory.CharpolyBlockAndInvariantUnderStabilizerNilradic

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N

namespace GlobalTheory.SemisimplificationCharpoly

/- English proof (translation)
Proceed by induction on `n with`. Consider the case `zero`. Introduce `V _ _ _ G f g _ h0 hn _ _`. Establish `hV : ∀ x : V, x = 0`. Introduce `x`.

Establish `hx : x ∈ G 0` using `by rw [hn]; exact Submodule.mem_top`. Rewrite `hx` using `[h0]`. Conclude with `(Submodule.mem_bot k).mp hx`. Establish `hfg : f = g`. Use extensionality with `x`.

Rewrite using `[hV x, map_zero, map_zero]`. Rewrite using `[hfg]`. Consider the case `succ n ih`. Introduce `V _ _ _ G f g hmono h0 hn hf hd`. Establish `hg : ∀ i, ∀ x ∈ G i, g x ∈ G i`.

Introduce `i x hx`. Consider the cases of `i with`. Consider the case `zero`. Rewrite `hx` using `[h0]`. Rewrite using `[(Submodule.mem_bot k).mp hx, map_zero]`.

Conclude with `Submodule.zero_mem _`. Consider the case `succ j`. Establish `e : g x = f x + (g x - f x)` using `by abel`. Rewrite using `[e]`. Conclude with `Submodule.add_mem _ (hf _ x hx) (hmono (Nat.le_succ j) (hd j x hx))`.

Use `set A := G n with hA`. Rewrite using `[GlobalTheory.CuspGL.charpoly_eq_restrict_mul_mapQ A f (hf n), GlobalTheory.CuspGL.charpoly_eq_restrict_mul_mapQ A g (hg n)]`. Use `congr 1`. Use `ih (fun i => (G i).comap A.subtype) (f.restrict (hf n)) (g.restrict (hg n)) (fun i j hij => Submodule.comap_mono (hmono hij)) ?_ ?_ ?_ ?_` and prove the remaining obligations. Rewrite using `[h0, Submodule.comap_bot, Submodule.ker_subtype]`.

Conclude with `Submodule.comap_subtype_self A`. Introduce `i x hx`. Conclude with `hf i x hx`. Introduce `i x hx`. Conclude with `hd i x hx`.

Use `congr 1`. Use extensionality with `x`. Simplify using `only [LinearMap.coe_comp, Function.comp_apply, Submodule.mkQ_apply, Submodule.mapQ_apply]`. Rewrite using `[Submodule.Quotient.eq]`. Establish `hx : x ∈ G (n + 1)` using `by rw [hn]; exact Submodule.mem_top`.

Use `hd n x hx` as an intermediate fact. Rewrite `this` using `[← neg_mem_iff, neg_sub]`. Conclude with `this`.
-/
private theorem charpoly_eq_of_filtration_graded_eq {k : Type} [Field k] (n : ℕ) :
    ∀ {V : Type} [AddCommGroup V] [Module k V] [FiniteDimensional k V] (G : ℕ → Submodule k V)
      (f g : Module.End k V), Monotone G → G 0 = ⊥ → G n = ⊤ → (∀ i, ∀ x ∈ G i, f x ∈ G i) →
      (∀ i, ∀ x ∈ G (i + 1), g x - f x ∈ G i) → LinearMap.charpoly f = LinearMap.charpoly g := by
  induction n with
  | zero =>
    intro V _ _ _ G f g _ h0 hn _ _
    have hV : ∀ x : V, x = 0 := by
      intro x
      have hx : x ∈ G 0 := by rw [hn]; exact Submodule.mem_top
      rw [h0] at hx
      exact (Submodule.mem_bot k).mp hx
    have hfg : f = g := by
      ext x
      rw [hV x, map_zero, map_zero]
    rw [hfg]
  | succ n ih =>
    intro V _ _ _ G f g hmono h0 hn hf hd

    have hg : ∀ i, ∀ x ∈ G i, g x ∈ G i := by
      intro i x hx
      cases i with
      | zero =>
        rw [h0] at hx
        rw [(Submodule.mem_bot k).mp hx, map_zero]
        exact Submodule.zero_mem _
      | succ j =>
        have e : g x = f x + (g x - f x) := by abel
        rw [e]
        exact Submodule.add_mem _ (hf _ x hx) (hmono (Nat.le_succ j) (hd j x hx))
    set A := G n with hA
    rw [GlobalTheory.CuspGL.charpoly_eq_restrict_mul_mapQ A f (hf n),
      GlobalTheory.CuspGL.charpoly_eq_restrict_mul_mapQ A g (hg n)]
    congr 1
    ·
      refine ih (fun i => (G i).comap A.subtype) (f.restrict (hf n)) (g.restrict (hg n))
        (fun i j hij => Submodule.comap_mono (hmono hij)) ?_ ?_ ?_ ?_
      · rw [h0, Submodule.comap_bot, Submodule.ker_subtype]
      · exact Submodule.comap_subtype_self A
      · intro i x hx
        exact hf i x hx
      · intro i x hx
        exact hd i x hx
    ·
      congr 1
      ext x
      simp only [LinearMap.coe_comp, Function.comp_apply, Submodule.mkQ_apply,
        Submodule.mapQ_apply]
      rw [Submodule.Quotient.eq]
      have hx : x ∈ G (n + 1) := by rw [hn]; exact Submodule.mem_top
      have := hd n x hx
      rw [← neg_mem_iff, neg_sub] at this
      exact this

/- English proof (translation)
Introduce `V _ _ _ F f g h0 hn hf hd`. Use `charpoly_eq_of_filtration_graded_eq n (fun i => partialSups F i) f g (partialSups F).monotone ?_ ?_ ?_ ?_` and prove the remaining obligations. Simplify using `only [partialSups_zero, h0]`. Conclude with `eq_top_iff.mpr (hn ▸ le_partialSups F n)`. Introduce `i`.

Establish `hle : partialSups F i ≤ (partialSups F i).comap f`. Use `partialSups_le F i _ (fun j hj x hx => ?_)` and prove the remaining obligations. Conclude with `le_partialSups_of_le F hj (hf j x hx)`. Conclude with `fun x hx => hle hx`. Introduce `i`.

Establish `hle : partialSups F (i + 1) ≤ (partialSups F i).comap (g - f)`. Use `partialSups_le F (i + 1) _ (fun j hj x hx => ?_)` and prove the remaining obligations. Consider the cases of `j with`. Consider the case `zero`. Rewrite `hx` using `[h0]`.

Rewrite using `[(Submodule.mem_bot k).mp hx]`. Conclude with `Submodule.zero_mem _`. Consider the case `succ m`. Conclude with `le_partialSups_of_le F (Nat.succ_le_succ_iff.mp hj) (hd m x hx)`. Conclude with `fun x hx => hle hx`.
-/
theorem charpoly_eq_of_filtration {k : Type} [Field k] (n : ℕ) :
    ∀ {V : Type} [AddCommGroup V] [Module k V] [FiniteDimensional k V] (F : ℕ → Submodule k V)
      (f g : Module.End k V), F 0 = ⊥ → F n = ⊤ → (∀ i, ∀ x ∈ F i, f x ∈ F i) →
      (∀ i, ∀ x ∈ F (i + 1), g x - f x ∈ F i) → LinearMap.charpoly f = LinearMap.charpoly g := by
  intro V _ _ _ F f g h0 hn hf hd

  refine charpoly_eq_of_filtration_graded_eq n (fun i => partialSups F i) f g (partialSups F).monotone ?_ ?_ ?_ ?_
  · simp only [partialSups_zero, h0]
  · exact eq_top_iff.mpr (hn ▸ le_partialSups F n)
  · intro i
    have hle : partialSups F i ≤ (partialSups F i).comap f := by
      refine partialSups_le F i _ (fun j hj x hx => ?_)
      exact le_partialSups_of_le F hj (hf j x hx)
    exact fun x hx => hle hx
  · intro i
    have hle : partialSups F (i + 1) ≤ (partialSups F i).comap (g - f) := by
      refine partialSups_le F (i + 1) _ (fun j hj x hx => ?_)
      cases j with
      | zero =>
        rw [h0] at hx
        rw [(Submodule.mem_bot k).mp hx]
        exact Submodule.zero_mem _
      | succ m =>
        exact le_partialSups_of_le F (Nat.succ_le_succ_iff.mp hj) (hd m x hx)
    exact fun x hx => hle hx

/- English proof (translation)
Introduce `k Γ _ _ W _ _ _ V _ _ _ s ρ hss g`. Unfold `GlobalTheory.IndefiniteRowSideFullHecke.SemisimplificationConstituents.IsSemisimplificationOf at hss`. Take `⟨-, m, Ws, e, hst, hint, hρ⟩` from `hss`. Establish `hsj : ∀ j, ∀ x ∈ Ws j, s g x ∈ Ws j`. Introduce `j x hx`.

Establish `h` using `hst j`. Unfold `Stable at h`. Conclude with `h g x hx`. Set `H : ℕ → Submodule k W` to `fun i => ⨆ (j : Fin m) (_ : (j : ℕ) < i), Ws j`. Establish `hH : ∀ i, ∀ x ∈ H i, s g x ∈ H i`.

Introduce `i`. Establish `hle : H i ≤ (H i).comap (s g)` using `iSup₂_le fun j hj x hx => (le_iSup₂ (f := fun (j : Fin m) (_ : (j : ℕ) < i) => Ws j) j hj) (hsj j x hx)`. Conclude with `fun x hx => hle hx`. Rewrite using `[← e.charpoly_conj (s g)]`. Use `charpoly_eq_of_filtration m (fun i => (H i).map (e : W →ₗ[k] V)) (e.conj (s g)) (ρ g) ?_ ?_ ?_ ?_` and prove the remaining obligations.

Establish `h0 : H 0 = ⊥` using `by simp [H]`. Simplify using `only [h0, Submodule.map_bot]`. Establish `hm : H m = ⊤`. Rewrite using `[eq_top_iff, ← hint.submodule_iSup_eq_top]`. Conclude with `iSup_le fun j => le_iSup₂ (f := fun (j : Fin m) (_ : (j : ℕ) < m) => Ws j) j j.isLt`.

Simplify using `only [hm, Submodule.map_top, LinearEquiv.range]`. Introduce `i x hx`. Rewrite `hx`, the goal using `[Submodule.mem_map_equiv]`. Simplify `hH i _ hx` using `[LinearEquiv.conj_apply]`. Introduce `i x hx`.

Rewrite `hx` using `[Submodule.mem_map_equiv]`. Establish `hle : H (i + 1) ≤ ((H i).map (e : W →ₗ[k] V)).comap ((ρ g - e.conj (s g)) ∘ₗ (e : W →ₗ[k] V))`. Use `iSup₂_le fun j hj v hv => ?_` and prove the remaining obligations. Establish `hsub : (⨆ j' ∈ Set.Iio j, Ws j') ≤ H i` using `iSup₂_le fun j' hj' => le_iSup₂ (f := fun (j : Fin m) (_ : (j : ℕ) < i) => Ws j) j' (lt_of_lt_of_le (Fin.lt_def.mp (Set.mem_Iio.mp hj')) (Nat.lt_succ_iff.mp hj))`. Establish `h1` using `Submodule.map_mono (f := (e : W →ₗ[k] V)) hsub (hρ j g v hv)`.

Simplify `h1` using `[LinearEquiv.conj_apply]`. Establish `h2` using `hle hx`. Simplify using `using h2`.
-/
theorem charpoly_eq : ∀ {k Γ : Type} [Field k] [Group Γ] {W : Type} [AddCommGroup W] [Module k W]
    [FiniteDimensional k W] {V : Type} [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    (s : Representation k Γ W) (ρ : Representation k Γ V),
    GlobalTheory.IndefiniteRowSideFullHecke.SemisimplificationConstituents.IsSemisimplificationOf s ρ →
      ∀ g, LinearMap.charpoly (s g) = LinearMap.charpoly (ρ g) := by
  intro k Γ _ _ W _ _ _ V _ _ _ s ρ hss g
  unfold GlobalTheory.IndefiniteRowSideFullHecke.SemisimplificationConstituents.IsSemisimplificationOf at hss
  obtain ⟨-, m, Ws, e, hst, hint, hρ⟩ := hss
  have hsj : ∀ j, ∀ x ∈ Ws j, s g x ∈ Ws j := by
    intro j x hx
    have h := hst j
    unfold Stable at h
    exact h g x hx

  let H : ℕ → Submodule k W := fun i => ⨆ (j : Fin m) (_ : (j : ℕ) < i), Ws j
  have hH : ∀ i, ∀ x ∈ H i, s g x ∈ H i := by
    intro i
    have hle : H i ≤ (H i).comap (s g) :=
      iSup₂_le fun j hj x hx =>
        (le_iSup₂ (f := fun (j : Fin m) (_ : (j : ℕ) < i) => Ws j) j hj) (hsj j x hx)
    exact fun x hx => hle hx
  rw [← e.charpoly_conj (s g)]
  refine charpoly_eq_of_filtration m (fun i => (H i).map (e : W →ₗ[k] V)) (e.conj (s g)) (ρ g)
    ?_ ?_ ?_ ?_
  · have h0 : H 0 = ⊥ := by simp [H]
    simp only [h0, Submodule.map_bot]
  · have hm : H m = ⊤ := by
      rw [eq_top_iff, ← hint.submodule_iSup_eq_top]
      exact iSup_le fun j => le_iSup₂ (f := fun (j : Fin m) (_ : (j : ℕ) < m) => Ws j) j j.isLt
    simp only [hm, Submodule.map_top, LinearEquiv.range]
  · intro i x hx
    rw [Submodule.mem_map_equiv] at hx ⊢
    simpa [LinearEquiv.conj_apply] using hH i _ hx
  · intro i x hx
    rw [Submodule.mem_map_equiv] at hx
    have hle : H (i + 1) ≤ ((H i).map (e : W →ₗ[k] V)).comap
        ((ρ g - e.conj (s g)) ∘ₗ (e : W →ₗ[k] V)) := by
      refine iSup₂_le fun j hj v hv => ?_
      have hsub : (⨆ j' ∈ Set.Iio j, Ws j') ≤ H i :=
        iSup₂_le fun j' hj' => le_iSup₂ (f := fun (j : Fin m) (_ : (j : ℕ) < i) => Ws j) j'
          (lt_of_lt_of_le (Fin.lt_def.mp (Set.mem_Iio.mp hj')) (Nat.lt_succ_iff.mp hj))
      have h1 := Submodule.map_mono (f := (e : W →ₗ[k] V)) hsub (hρ j g v hv)
      simpa [LinearEquiv.conj_apply] using h1
    have h2 := hle hx
    simpa using h2

end GlobalTheory.SemisimplificationCharpoly

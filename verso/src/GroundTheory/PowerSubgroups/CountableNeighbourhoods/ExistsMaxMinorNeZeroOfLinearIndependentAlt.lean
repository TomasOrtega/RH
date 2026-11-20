import Mathlib

namespace GroundTheory.Variant₂.N1

def KSubset (n k : ℕ) : Type := { s : Finset (Fin n) // s.card = k }

def KSubset.emb {n k : ℕ} (s : KSubset n k) : Fin k ↪o Fin n :=
  (s.1).orderEmbOfFin s.2

def maxMinor {R : Type*} [CommRing R] {n k : ℕ} (B : Matrix (Fin n) (Fin k) R)
    (s : KSubset n k) : R :=
  (B.submatrix (⇑s.emb) id).det

/- English proof (translation)
Use `set K := FractionRing R`. Use `set B' : Matrix (Fin n) (Fin k) K := B.map (algebraMap R K) with hB'`. Establish `hinj : Function.Injective (algebraMap R K)` using `IsFractionRing.injective R K`. Establish `h1 : LinearIndependent R B'.col`. Establish `hker : LinearMap.ker ((Algebra.linearMap R K).compLeft (Fin n)) = ⊥`.

Rewrite using `[LinearMap.ker_eq_bot]`. Introduce `x y hxy`. Use function extensionality and compare the values at `i`. Conclude with `hinj (congr_fun hxy i)`. Use `hB.map' ((Algebra.linearMap R K).compLeft (Fin n)) hker` as an intermediate fact.

Establish `heq : B'.col = ((Algebra.linearMap R K).compLeft (Fin n)) ∘ B.col`. Use function extensionality and compare the values at `j i`. Both sides reduce to the same expression. Rewrite using `[heq]`. Conclude with `this`.

Establish `h2 : LinearIndependent K B'.col` using `(LinearIndependent.iff_fractionRing R K).mp h1`. Establish `hrank : B'.rank = k`. Rewrite using `[Matrix.rank_eq_finrank_span_cols, finrank_span_eq_card h2, Fintype.card_fin]`. Rewrite `hrank` using `[Matrix.rank_eq_finrank_span_row]`. Take `⟨κ, a, ha, hspan, hli⟩` from `exists_linearIndependent' K B'.row`.

Establish `: Finite κ` using `Finite.of_injective a ha`. Set `: Fintype κ` to `Fintype.ofFinite κ`. Establish `hcard : Fintype.card κ = k`. Rewrite using `[← hrank, ← hspan, finrank_span_eq_card hli]`. Set `t : Finset (Fin n)` to `Finset.univ.map ⟨a, ha⟩`.

Establish `ht : t.card = k` using `by simp [t, hcard]`. Set `s : KSubset n k` to `⟨t, ht⟩`. Use `⟨s, ?_⟩` and prove the remaining obligations. Establish `hmem : ∀ i : Fin k, ∃ c : κ, a c = s.emb i`. Introduce `i`.

Establish `h : s.emb i ∈ t` using `Finset.orderEmbOfFin_mem t ht i`. Simplify using `only [t, Finset.mem_map, Finset.mem_univ, true_and] at h`. Take `⟨c, hc⟩` from `h`. Conclude with `⟨c, hc⟩`. Use `choose e he using hmem`.

Establish `he_inj : Function.Injective e`. Introduce `i j hij`. Apply `s.emb.injective` to reduce the goal to its premises. Rewrite using `[← he i, ← he j, hij]`. Establish `hrows : LinearIndependent K (B'.submatrix s.emb id).row`.

Establish `hfam : (B'.submatrix s.emb id).row = (B'.row ∘ a) ∘ e`. Use function extensionality and compare the values at `i j`. Use `show B' (s.emb i) j = B' (a (e i)) j`. Rewrite using `[he i]`. Rewrite using `[hfam]`.

Conclude with `hli.comp e he_inj`. Establish `hdet : (B'.submatrix s.emb id).det ≠ 0`. Establish `hu` using `Matrix.linearIndependent_rows_iff_isUnit.mp hrows`. Conclude with `((Matrix.isUnit_iff_isUnit_det _).mp hu).ne_zero`. Introduce `h`.

Apply `hdet` to reduce the goal to its premises. Establish `hmap : B'.submatrix s.emb id = (B.submatrix s.emb id).map (algebraMap R K)` using `rfl`. Rewrite using `[hmap]`. Use `show ((algebraMap R K).mapMatrix (B.submatrix s.emb id)).det = 0`. Rewrite using `[← RingHom.map_det]`.

Unfold `maxMinor at h`. Rewrite using `[h, map_zero]`.
-/
theorem exists_maxMinor_ne_zero_of_linearIndependent_alt {R : Type*} [CommRing R] {n k : ℕ}
    [IsDomain R] (B : Matrix (Fin n) (Fin k) R) (hB : LinearIndependent R B.col) :
    ∃ s : KSubset n k, maxMinor B s ≠ 0 := by
  classical
  set K := FractionRing R
  set B' : Matrix (Fin n) (Fin k) K := B.map (algebraMap R K) with hB'
  have hinj : Function.Injective (algebraMap R K) := IsFractionRing.injective R K
  have h1 : LinearIndependent R B'.col := by
    have hker : LinearMap.ker ((Algebra.linearMap R K).compLeft (Fin n)) = ⊥ := by
      rw [LinearMap.ker_eq_bot]
      intro x y hxy
      funext i
      exact hinj (congr_fun hxy i)
    have := hB.map' ((Algebra.linearMap R K).compLeft (Fin n)) hker
    have heq : B'.col = ((Algebra.linearMap R K).compLeft (Fin n)) ∘ B.col := by
      funext j i
      rfl
    rw [heq]
    exact this
  have h2 : LinearIndependent K B'.col := (LinearIndependent.iff_fractionRing R K).mp h1
  have hrank : B'.rank = k := by
    rw [Matrix.rank_eq_finrank_span_cols, finrank_span_eq_card h2, Fintype.card_fin]
  rw [Matrix.rank_eq_finrank_span_row] at hrank
  obtain ⟨κ, a, ha, hspan, hli⟩ := exists_linearIndependent' K B'.row
  have : Finite κ := Finite.of_injective a ha
  let : Fintype κ := Fintype.ofFinite κ
  have hcard : Fintype.card κ = k := by
    rw [← hrank, ← hspan, finrank_span_eq_card hli]
  let t : Finset (Fin n) := Finset.univ.map ⟨a, ha⟩
  have ht : t.card = k := by simp [t, hcard]
  let s : KSubset n k := ⟨t, ht⟩
  refine ⟨s, ?_⟩
  have hmem : ∀ i : Fin k, ∃ c : κ, a c = s.emb i := by
    intro i
    have h : s.emb i ∈ t := Finset.orderEmbOfFin_mem t ht i
    simp only [t, Finset.mem_map, Finset.mem_univ, true_and] at h
    obtain ⟨c, hc⟩ := h
    exact ⟨c, hc⟩
  choose e he using hmem
  have he_inj : Function.Injective e := by
    intro i j hij
    apply s.emb.injective
    rw [← he i, ← he j, hij]
  have hrows : LinearIndependent K (B'.submatrix s.emb id).row := by
    have hfam : (B'.submatrix s.emb id).row = (B'.row ∘ a) ∘ e := by
      funext i j
      show B' (s.emb i) j = B' (a (e i)) j
      rw [he i]
    rw [hfam]
    exact hli.comp e he_inj
  have hdet : (B'.submatrix s.emb id).det ≠ 0 := by
    have hu := Matrix.linearIndependent_rows_iff_isUnit.mp hrows
    exact ((Matrix.isUnit_iff_isUnit_det _).mp hu).ne_zero
  intro h
  apply hdet
  have hmap : B'.submatrix s.emb id = (B.submatrix s.emb id).map (algebraMap R K) := rfl
  rw [hmap]
  show ((algebraMap R K).mapMatrix (B.submatrix s.emb id)).det = 0
  rw [← RingHom.map_det]
  unfold maxMinor at h
  rw [h, map_zero]

end GroundTheory.Variant₂.N1

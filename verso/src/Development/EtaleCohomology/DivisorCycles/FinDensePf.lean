import Development.EtaleCohomology.DivisorCycles.CycleCount

open Matrix PositivityTheory.AutomorphicGaloisHodgeTate.Div

namespace LateralTheory.DivDb.FinDensePf

/- English proof (translation)
Establish `h1 : Continuous (fun g => (fun p : Fin n × Fin n => x g p.1 p.2))` using `continuous_pi fun p => hx.matrix_elem p.1 p.2`. Conclude with `(MvPolynomial.continuous_eval f).comp h1`.
-/
theorem cont_ev {Γ K : Type} [TopologicalSpace Γ] [Field K] [TopologicalSpace K] [IsTopologicalRing K]
    (n : ℕ) (x : Γ → Matrix (Fin n) (Fin n) K) (hx : Continuous x) (f : LateralTheory.DivDb.MP K n) :
    Continuous (fun g => LateralTheory.DivDb.ev (x g) f) := by
  have h1 : Continuous (fun g => (fun p : Fin n × Fin n => x g p.1 p.2)) :=
    continuous_pi fun p => hx.matrix_elem p.1 p.2
  exact (MvPolynomial.continuous_eval f).comp h1

end LateralTheory.DivDb.FinDensePf

namespace LateralTheory.DivDb

/- English proof (translation)
Introduce `Γ K _ _ _ _ _ _ _ _ _ n r hr hU`. Take `⟨f, hf⟩` from `hSep K n`. Establish `hset : {g : Γ | (r g : Mat K n).charpoly.Separable} = {g | ev (r g : Mat K n) f ≠ 0}`. Use extensionality with `g`. Conclude with `hf _`.

Rewrite using `[hset]`. Establish `hc` using `LateralTheory.DivDb.FinDensePf.cont_ev n (fun g => (r g : Mat K n)) hr f`. Use `⟨isOpen_ne_fun hc continuous_const, ?_⟩` and prove the remaining obligations. Rewrite using `[dense_iff_inter_open]`. Introduce `O hO hne`.

Assume the negation of the conclusion as `hemp`. Establish `hz : ∀ g ∈ O, ev (r g : Mat K n) f = 0`. Introduce `g hg`. Assume the negation of the conclusion as `h`. Conclude with `hemp ⟨g, hg, h⟩`.

Take `⟨U, hUn, hUf, g, hg⟩` from `hOC Γ K n r f O hO hne hz`. Take `⟨u, hu, hs⟩` from `hU U hUn hUf g`. Conclude with `(hf _).1 hs (hg u hu)`.
-/
theorem FinDense_of (hSep : SepPoly) (hOC : OpenCoset) : FinDense := by
  intro Γ K _ _ _ _ _ _ _ _ _ n r hr hU
  obtain ⟨f, hf⟩ := hSep K n
  have hset : {g : Γ | (r g : Mat K n).charpoly.Separable} = {g | ev (r g : Mat K n) f ≠ 0} := by
    ext g; exact hf _
  rw [hset]
  have hc := LateralTheory.DivDb.FinDensePf.cont_ev n (fun g => (r g : Mat K n)) hr f
  refine ⟨isOpen_ne_fun hc continuous_const, ?_⟩
  rw [dense_iff_inter_open]
  intro O hO hne
  by_contra hemp
  have hz : ∀ g ∈ O, ev (r g : Mat K n) f = 0 := by
    intro g hg
    by_contra h
    exact hemp ⟨g, hg, h⟩
  obtain ⟨U, hUn, hUf, g, hg⟩ := hOC Γ K n r f O hO hne hz
  obtain ⟨u, hu, hs⟩ := hU U hUn hUf g
  exact (hf _).1 hs (hg u hu)

end LateralTheory.DivDb

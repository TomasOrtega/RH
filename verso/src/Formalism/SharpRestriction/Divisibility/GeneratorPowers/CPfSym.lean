import Formalism.SharpRestriction.Divisibility.GeneratorPowers.LegendreSumSt

set_option autoImplicit false

noncomputable section

namespace Formalism.MainNotions.ModuliIntegralCharts.H1

open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

namespace Sym

variable {k : Type} [CommRing k] {σ : Type}

def OrdGE (r : ℕ) (g : MvPowerSeries σ k) : Prop := ∀ e : σ →₀ ℕ, e.degree < r → coeff e g = 0

/- English proof (translation)
Introduce `e _`. Simplify using the standard rewrite rules.
-/
theorem ordGE_zero (r : ℕ) : OrdGE r (0 : MvPowerSeries σ k) := by
  intro e _
  simp

/- English proof (translation)
Introduce `e he`. Rewrite using `[map_add, hf e he, hg e he, add_zero]`.
-/
theorem ordGE_add {r : ℕ} {f g : MvPowerSeries σ k} (hf : OrdGE r f) (hg : OrdGE r g) : OrdGE r (f + g) := by
  intro e he
  rw [map_add, hf e he, hg e he, add_zero]

def op {d : ℕ} (a : Fin d → MvPowerSeries σ k) (cd : Fin d → σ) (g : MvPowerSeries σ k) : MvPowerSeries σ k :=
  ∑ j, a j * pderiv k (cd j) g

end Sym

namespace Sym

variable {k : Type} [CommRing k] {σ : Type}

structure GoodPair (D D₀ : MvPowerSeries σ k → MvPowerSeries σ k) : Prop where
  ord : ∀ r g, OrdGE (r + 1) g → OrdGE r (D g)
  ord₀ : ∀ r g, OrdGE (r + 1) g → OrdGE r (D₀ g)
  diff : ∀ r g, OrdGE (r + 1) g → OrdGE (r + 1) (D g - D₀ g)
  sub : ∀ f g, D (f - g) = D f - D g

/- English proof (translation)
Proceed by induction on `c with`. Consider the case `zero`. Introduce `r g hg`. Rewrite `hg` using `[zero_add]`. Use `⟨?_, hg, hg⟩` and prove the remaining obligations.

Establish `e : D^[0] g - D₀^[0] g = 0` using `sub_self g`. Rewrite using `[e]`. Conclude with `ordGE_zero _`. Consider the case `succ n ih`. Introduce `r g hg`.

Take `⟨h1, h2, h3⟩` from `ih (r + 1) g (by rwa [show n + (r + 1) = n + 1 + r by omega])`. Rewrite using `[Function.iterate_succ_apply', Function.iterate_succ_apply']`. Use `⟨?_, hP.ord r _ h2, hP.ord₀ r _ h3⟩` and prove the remaining obligations. Establish `e : D (D^[n] g) - D₀ (D₀^[n] g) = D (D^[n] g - D₀^[n] g) + (D (D₀^[n] g) - D₀ (D₀^[n] g))`. Rewrite using `[hP.sub]`.

Normalize the expressions using the abelian group laws. Rewrite using `[e]`. Conclude with `ordGE_add (hP.ord (r + 1) _ h1) (hP.diff r _ h3)`.
-/
theorem GoodPair.iter {D D₀ : MvPowerSeries σ k → MvPowerSeries σ k} (hP : GoodPair D D₀) (c : ℕ) :
    ∀ r g, OrdGE (c + r) g →
      OrdGE (r + 1) (D^[c] g - D₀^[c] g) ∧ OrdGE r (D^[c] g) ∧ OrdGE r (D₀^[c] g) := by
  induction c with
  | zero =>
    intro r g hg
    rw [zero_add] at hg
    refine ⟨?_, hg, hg⟩
    have e : D^[0] g - D₀^[0] g = 0 := sub_self g
    rw [e]
    exact ordGE_zero _
  | succ n ih =>
    intro r g hg
    obtain ⟨h1, h2, h3⟩ := ih (r + 1) g (by rwa [show n + (r + 1) = n + 1 + r by omega])
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
    refine ⟨?_, hP.ord r _ h2, hP.ord₀ r _ h3⟩
    have e : D (D^[n] g) - D₀ (D₀^[n] g) = D (D^[n] g - D₀^[n] g) + (D (D₀^[n] g) - D₀ (D₀^[n] g)) := by
      rw [hP.sub]
      abel
    rw [e]
    exact ordGE_add (hP.ord (r + 1) _ h1) (hP.diff r _ h3)

end Sym

namespace Sym

variable {k : Type} [CommRing k]

/- English proof (translation)
Establish `hA : HasSubst a` using `by first`. Consider the case `exact hasSubst_of_constantCoeff_zero ha`. Consider the case `exact HasSubst.of_constantCoeff_zero' ha`. Consider the case `exact hasSubst_of_constantCoeff_nilpotent fun s => by rw [ha s]; exact IsNilpotent.zero`. Consider the case `exact HasSubst.of_constantCoeff_nilpotent fun s => by rw [ha s]; exact IsNilpotent.zero`.

Rewrite using `[constantCoeff_subst hA, finsum_eq_single _ (0 : σ →₀ ℕ)]`. Simplify using the standard rewrite rules. Introduce `e he`. Choose the witnesses or unpack the hypotheses as in `⟨s, hs⟩ : ∃ s, e s ≠ 0 := by`. Assume the negation of the conclusion as `hc`.

Use `push_neg at hc`. Conclude with `he (Finsupp.ext fun t => by simpa using hc t)`. Rewrite using `[Finsupp.prod, map_prod, Finset.prod_eq_zero (Finsupp.mem_support_iff.mpr hs)]`. Simplify using the standard rewrite rules. Rewrite using `[map_pow, ha s, zero_pow hs]`.
-/
private theorem const_subst_lemma {σ τ : Type} [Finite σ] (a : σ → MvPowerSeries τ k)
    (ha : ∀ s, constantCoeff (a s) = 0) (g : MvPowerSeries σ k) :
    constantCoeff (subst a g) = constantCoeff g := by
  have hA : HasSubst a := by
    first
      | exact hasSubst_of_constantCoeff_zero ha
      | exact HasSubst.of_constantCoeff_zero' ha
      | exact hasSubst_of_constantCoeff_nilpotent fun s => by rw [ha s]; exact IsNilpotent.zero
      | exact HasSubst.of_constantCoeff_nilpotent fun s => by rw [ha s]; exact IsNilpotent.zero
  rw [constantCoeff_subst hA, finsum_eq_single _ (0 : σ →₀ ℕ)]
  · simp
  · intro e he
    obtain ⟨s, hs⟩ : ∃ s, e s ≠ 0 := by
      by_contra hc
      push_neg at hc
      exact he (Finsupp.ext fun t => by simpa using hc t)
    rw [Finsupp.prod, map_prod, Finset.prod_eq_zero (Finsupp.mem_support_iff.mpr hs)]
    · simp
    · rw [map_pow, ha s, zero_pow hs]

/- English proof (translation)
Unfold `ev`. Conclude with `const_subst_lemma (fun p : Fin m × Fin d => a p.1 p.2) (fun p => ha p.1 p.2) g`.
-/
theorem const_ev {m n d : ℕ} (a : Fin m → Pt k n d) (ha : ∀ p q, constantCoeff (a p q) = 0) (g : PS k m d) :
    constantCoeff (ev a g) = constantCoeff g := by
  unfold ev
  exact const_subst_lemma (fun p : Fin m × Fin d => a p.1 p.2) (fun p => ha p.1 p.2) g

end Sym

namespace Sym

variable {k : Type} [CommRing k]

/- English proof (translation)
Conclude with `const_subst_lemma a ha g`.
-/
theorem const_subst {σ τ : Type} [Finite σ] (a : σ → MvPowerSeries τ k) (ha : ∀ s, constantCoeff (a s) = 0)
    (g : MvPowerSeries σ k) : constantCoeff (subst a g) = constantCoeff g := by
  exact const_subst_lemma a ha g

end Sym

namespace Sym

variable {k : Type} [CommRing k]

end Sym

namespace Sym

variable {k : Type} [CommRing k]

end Sym

namespace Sym

variable {R : Type} [CommRing R] {d : ℕ} {O : Type} [CommRing O] [StarRing O] {k : Type} [CommRing k]
  [Algebra ℚ k] [Algebra R k]

end Sym

namespace Sym

variable {R : Type} [CommRing R] {d : ℕ} {O : Type} [CommRing O] [StarRing O] {k : Type} [CommRing k]
  [Algebra ℚ k] [Algebra R k]

end Sym

end Formalism.MainNotions.ModuliIntegralCharts.H1

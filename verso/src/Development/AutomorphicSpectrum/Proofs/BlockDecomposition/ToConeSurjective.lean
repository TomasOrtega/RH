import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.HodgeSurjectivity.NLeA
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AlgebraMapConeRing

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.CompanionTheory.SurjectionOntoH4.ChartBij
open CrystallineSemistableComparison.Onto GlobalTheory.CompanionTheory.SurjectionOntoH4

variable {n d : ℕ}

def coord (k : Fin d) (g : Gam n d) : E n d → ℤ
  | Sum.inl l => g (Sum.inl l)
  | Sum.inr j => if j = k then tdeg g else g (Sum.inr j)

/- English proof (translation)
Use function extensionality and compare the values at `e`. Break down `e with l | j` into its components or cases. Both sides reduce to the same expression. Distinguish the cases in `h : j = k`. Simplify using `[coord, h, tdeg_add]`.

Simplify using `[coord, h]`.
-/
theorem coord_add (k : Fin d) (g g' : Gam n d) : coord k (g + g') = coord k g + coord k g' := by
  funext e
  rcases e with l | j
  · rfl
  · by_cases h : j = k
    · simp [coord, h, tdeg_add]
    · simp [coord, h]

/- English proof (translation)
Use function extensionality and compare the values at `e`. Break down `e with l | j` into its components or cases. Both sides reduce to the same expression. Distinguish the cases in `h : j = k`. Simplify using `[coord, h, tdeg]`.

Simplify using `[coord, h]`.
-/
theorem coord_zero (k : Fin d) : coord k (0 : Gam n d) = 0 := by
  funext e
  rcases e with l | j
  · rfl
  · by_cases h : j = k
    · simp [coord, h, tdeg]
    · simp [coord, h]

/- English proof (translation)
Establish `h1` using `tdeg_add (ratE k j : Gam n d) (oneE (Sum.inr k))`. Establish `h2 : (ratE k j : Gam n d) + oneE (Sum.inr k) = oneE (Sum.inr j)` using `by simp [ratE]`. Rewrite `h1` using `[h2, tdeg_oneE_inr, tdeg_oneE_inr]`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem tdeg_ratE (k j : Fin d) : tdeg (ratE k j : Gam n d) = 0 := by
  have h1 := tdeg_add (ratE k j : Gam n d) (oneE (Sum.inr k))
  have h2 : (ratE k j : Gam n d) + oneE (Sum.inr k) = oneE (Sum.inr j) := by simp [ratE]
  rw [h2, tdeg_oneE_inr, tdeg_oneE_inr] at h1
  linarith

/- English proof (translation)
Apply the tactic sequence `rcases e with l | j <;> rcases e' with l' | j'`. Simplify using `[coord, wv, oneE, Pi.single_apply]`. Distinguish the cases in `h : j' = k`. Simplify using `[coord, wv, oneE, h, tdeg, Pi.single_apply]`. Simplify using `[coord, wv, oneE, h, Pi.single_apply]`.

Distinguish the cases in `h : j = k`. Simplify using `[coord, wv, oneE, h, Pi.single_apply]`. Simplify using `[coord, wv, ratE, oneE, h, Pi.single_apply]`. Distinguish the cases in `h : j = k`. Substitute `h` using the available equality.

Distinguish the cases in `h' : j' = j`. Simplify using `[coord, wv, h', tdeg_oneE_inr]`. Simplify using `[coord, wv, oneE, h', Pi.single_apply]`. Distinguish the cases in `h' : j' = k`. Substitute `h'` using the available equality.

Establish `hne : ¬ j' = j` using `fun e => h e.symm`. Simplify using `[coord, wv, h, hne, tdeg_ratE]`. Distinguish the cases in `h'' : j' = j`. Substitute `h''` using the available equality. Simplify using `[coord, wv, ratE, oneE, h, h', Pi.single_apply]`.

Simplify using `[coord, wv, ratE, oneE, h, h', h'', Pi.single_apply]`.
-/
theorem coord_wv (k : Fin d) (e e' : E n d) : coord k (wv k e) e' = if e' = e then 1 else 0 := by
  rcases e with l | j <;> rcases e' with l' | j'
  · simp [coord, wv, oneE, Pi.single_apply]
  · by_cases h : j' = k
    · simp [coord, wv, oneE, h, tdeg, Pi.single_apply]
    · simp [coord, wv, oneE, h, Pi.single_apply]
  · by_cases h : j = k
    · simp [coord, wv, oneE, h, Pi.single_apply]
    · simp [coord, wv, ratE, oneE, h, Pi.single_apply]
  · by_cases h : j = k
    · subst h
      by_cases h' : j' = j
      · simp [coord, wv, h', tdeg_oneE_inr]
      · simp [coord, wv, oneE, h', Pi.single_apply]
    · by_cases h' : j' = k
      · subst h'
        have hne : ¬ j' = j := fun e => h e.symm
        simp [coord, wv, h, hne, tdeg_ratE]
      · by_cases h'' : j' = j
        · subst h''
          simp [coord, wv, ratE, oneE, h, h', Pi.single_apply]
        · simp [coord, wv, ratE, oneE, h, h', h'', Pi.single_apply]

/- English proof (translation)
Establish `hj : ∀ j, j ≠ k → g (Sum.inr j) = g' (Sum.inr j)` using `fun j hj => by`. Use `congrFun h (Sum.inr j)` as an intermediate fact. Simplify `this` using `[coord, hj]`. Establish `ht : tdeg g = tdeg g'`. Use `congrFun h (Sum.inr k)` as an intermediate fact.

Simplify `this` using `[coord]`. Use function extensionality and compare the values at `e`. Break down `e with l | j` into its components or cases. Conclude with `congrFun h (Sum.inl l)`. Distinguish the cases in `hjk : j = k`.

Substitute `hjk` using the available equality. Unfold `tdeg at ht`. Rewrite `ht` using `[← Finset.add_sum_erase _ _ (Finset.mem_univ j), ← Finset.add_sum_erase _ _ (Finset.mem_univ j)]`. Establish `: ∑ x ∈ Finset.univ.erase j, g (Sum.inr x) = ∑ x ∈ Finset.univ.erase j, g' (Sum.inr x)` using `Finset.sum_congr rfl fun x hx => hj x (Finset.ne_of_mem_erase hx)`. Combine the linear equalities and inequalities to obtain the conclusion.

Conclude with `hj j hjk`.
-/
theorem coord_inj (k : Fin d) {g g' : Gam n d} (h : coord k g = coord k g') : g = g' := by
  have hj : ∀ j, j ≠ k → g (Sum.inr j) = g' (Sum.inr j) := fun j hj => by
    have := congrFun h (Sum.inr j)
    simpa [coord, hj] using this
  have ht : tdeg g = tdeg g' := by
    have := congrFun h (Sum.inr k)
    simpa [coord] using this
  funext e
  rcases e with l | j
  · exact congrFun h (Sum.inl l)
  · by_cases hjk : j = k
    · subst hjk
      unfold tdeg at ht
      rw [← Finset.add_sum_erase _ _ (Finset.mem_univ j), ← Finset.add_sum_erase _ _ (Finset.mem_univ j)] at ht
      have : ∑ x ∈ Finset.univ.erase j, g (Sum.inr x) = ∑ x ∈ Finset.univ.erase j, g' (Sum.inr x) :=
        Finset.sum_congr rfl fun x hx => hj x (Finset.ne_of_mem_erase hx)
      linarith
    · exact hj j hjk

def toCone (k : Fin d) : (E n d →₀ ℕ) →+ (cone {k} : AddSubmonoid (Gam n d)) :=
  Finsupp.liftAddHom fun e => multiplesHom _ ⟨wv k e, wv_mem (Finset.mem_singleton_self k) e⟩

/- English proof (translation)
Simplify using `[toCone]`.
-/
theorem toCone_single (k : Fin d) (e : E n d) :
    toCone k (Finsupp.single e 1) = ⟨wv k e, wv_mem (Finset.mem_singleton_self k) e⟩ := by
  simp [toCone]

/- English proof (translation)
Proceed by induction on `f using Finsupp.induction_linear with`. Consider the case `zero => simp [coord_zero]`. Consider the case `add f g hf hg`. Rewrite using `[map_add, AddSubmonoid.coe_add, coord_add, Pi.add_apply, hf, hg]`. Simplify using the standard rewrite rules.

Consider the case `single a b`. Proceed by induction on `b with`. Consider the case `zero => simp [coord_zero]`. Consider the case `succ b ih`. Rewrite using `[show Finsupp.single a (b + 1) = Finsupp.single a b + Finsupp.single a 1 by simp, map_add, AddSubmonoid.coe_add, coord_add, Pi.add_apply, ih, toCone_single]`.

Simplify using `only [coord_wv, Finsupp.add_apply, Finsupp.single_apply]`. Distinguish the cases in `h : e = a`. Simplify using `[h]`. Establish `: ¬ a = e` using `fun x => h x.symm`. Simplify using `[h, this]`.
-/
theorem coord_toCone (k : Fin d) (f : E n d →₀ ℕ) (e : E n d) :
    coord k (toCone k f : Gam n d) e = f e := by
  induction f using Finsupp.induction_linear with
  | zero => simp [coord_zero]
  | add f g hf hg =>
    rw [map_add, AddSubmonoid.coe_add, coord_add, Pi.add_apply, hf, hg]
    simp
  | single a b =>
    induction b with
    | zero => simp [coord_zero]
    | succ b ih =>
      rw [show Finsupp.single a (b + 1) = Finsupp.single a b + Finsupp.single a 1 by simp,
        map_add, AddSubmonoid.coe_add, coord_add, Pi.add_apply, ih, toCone_single]
      simp only [coord_wv, Finsupp.add_apply, Finsupp.single_apply]
      by_cases h : e = a
      · simp [h]
      · have : ¬ a = e := fun x => h x.symm
        simp [h, this]

/- English proof (translation)
Introduce `f f' h`. Use extensionality with `e`. Establish `h1` using `coord_toCone k f e`. Rewrite `h1` using `[h, coord_toCone]`. Conclude with `h1.symm` after adjusting the coercions.
-/
theorem toCone_injective (k : Fin d) : Function.Injective (toCone k : (E n d →₀ ℕ) → _) := by
  intro f f' h
  ext e
  have h1 := coord_toCone k f e
  rw [h, coord_toCone] at h1
  exact_mod_cast h1.symm

/- English proof (translation)
Break down `e with l | j` into its components or cases. Conclude with `hg.1 l`. Distinguish the cases in `h : j = k`. Simplify `hg.2.2` using `[coord, h]`. Simplify `hg.2.1 j (by simpa using h)` using `[coord, h]`.
-/
theorem coord_nonneg (k : Fin d) {g : Gam n d} (hg : g ∈ (cone {k} : AddSubmonoid (Gam n d))) (e : E n d) :
    0 ≤ coord k g e := by
  rcases e with l | j
  · exact hg.1 l
  · by_cases h : j = k
    · simpa [coord, h] using hg.2.2
    · simpa [coord, h] using hg.2.1 j (by simpa using h)

/- English proof (translation)
Introduce and unpack `⟨g, hg⟩`. Use `⟨Finsupp.equivFunOnFinite.symm fun e => (coord k g e).toNat, Subtype.ext (coord_inj k ?_)⟩` and prove the remaining obligations. Use function extensionality and compare the values at `e`. Rewrite using `[coord_toCone]`. Simplify using `using coord_nonneg k hg e`.
-/
theorem toCone_surjective (k : Fin d) : Function.Surjective (toCone k : (E n d →₀ ℕ) → _) := by
  rintro ⟨g, hg⟩
  refine ⟨Finsupp.equivFunOnFinite.symm fun e => (coord k g e).toNat, Subtype.ext (coord_inj k ?_)⟩
  funext e
  rw [coord_toCone]
  simpa using coord_nonneg k hg e

def coneEquiv (k : Fin d) : (E n d →₀ ℕ) ≃+ (cone {k} : AddSubmonoid (Gam n d)) :=
  AddEquiv.ofBijective (toCone k) ⟨toCone_injective k, toCone_surjective k⟩

/- English proof (translation)
Set `Φ : Bp K n d ≃ₐ[K] R0 K n d {k}` to `AddMonoidAlgebra.domCongr K K (coneEquiv k)`. Establish `h : (MvPolynomial.aeval (R` using `K) (fun e : E n d => mon K (wv k e) (wv_mem (Finset.mem_singleton_self k) e)) : Bp K n d →ₐ[K] R0 K n d {k}) = Φ.toAlgHom := by`. Apply `MvPolynomial.algHom_ext` to reduce the goal to its premises. Introduce `e`. Rewrite using `[MvPolynomial.aeval_X]`.

Express the relevant statement in the definitionally equal form `_ = AddMonoidAlgebra.domCongr K K (coneEquiv k) (AddMonoidAlgebra.single (Finsupp.single e 1) 1)`. Simplify using `only [mon, coneEquiv]`. Simplify using the standard rewrite rules. Conclude with `congrArg (fun m => AddMonoidAlgebra.single m (1 : K)) (toCone_single k e).symm`. Rewrite using `[h]`.

Conclude with `Φ.bijective`.
-/
theorem chart_bijective {K : Type} [Field K] {n d : ℕ} (k : Fin d) :
    Function.Bijective (MvPolynomial.aeval (R := K)
      (fun e : E n d => mon K (wv k e) (wv_mem (Finset.mem_singleton_self k) e)) : Bp K n d →ₐ[K] R0 K n d {k}) := by
  let Φ : Bp K n d ≃ₐ[K] R0 K n d {k} := AddMonoidAlgebra.domCongr K K (coneEquiv k)
  have h : (MvPolynomial.aeval (R := K)
      (fun e : E n d => mon K (wv k e) (wv_mem (Finset.mem_singleton_self k) e)) : Bp K n d →ₐ[K] R0 K n d {k}) = Φ.toAlgHom := by
    apply MvPolynomial.algHom_ext
    intro e
    rw [MvPolynomial.aeval_X]
    change _ = AddMonoidAlgebra.domCongr K K (coneEquiv k) (AddMonoidAlgebra.single (Finsupp.single e 1) 1)
    simp only [mon, coneEquiv]
    simp
    exact congrArg (fun m => AddMonoidAlgebra.single m (1 : K)) (toCone_single k e).symm
  rw [h]
  exact Φ.bijective

end GlobalTheory.CompanionTheory.SurjectionOntoH4.ChartBij

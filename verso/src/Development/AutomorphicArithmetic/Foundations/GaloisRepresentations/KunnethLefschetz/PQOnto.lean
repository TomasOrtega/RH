import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.BasisOne
import Development.EtaleCohomology.EtaleTrace.H0LimitCoherence
import Development.EtaleCohomology.EtaleTrace.LRingPf

noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC LateralTheory.EtaleTrace UpperTheory.Gal.KunnethLefschetz
open scoped TensorProduct DirectSum

/- English proof (translation)
Establish `hb' : (b : ℚ_[l]) ≠ 0` using `by rwa [Ne, PadicInt.coe_eq_zero]`. Establish `h1 : (1 : ℚ_[l]) ⊗ₜ[ℤ_[l]] w = 0`. Establish `h2` using `congrArg (fun t => (b : ℚ_[l]) • t) h`. Simplify `h2` using `[TensorProduct.smul_tmul', hb']`. Establish `hloc : IsLocalizedModule (nonZeroDivisors ℤ_[l]) (TensorProduct.mk ℤ_[l] ℚ_[l] M 1)` using `inferInstance`.

Take `⟨c, hc⟩` from `(IsLocalizedModule.eq_zero_iff (nonZeroDivisors ℤ_[l]) (TensorProduct.mk ℤ_[l] ℚ_[l] M 1)).1 h1`. Conclude with `⟨c, nonZeroDivisors.ne_zero c.2, hc⟩`.
-/
private theorem tors_of {l : ℕ} [Fact l.Prime] {M : Type*} [AddCommGroup M] [Module ℤ_[l] M] (b : ℤ_[l]) (hb : b ≠ 0)
    (w : M) (h : ((b : ℚ_[l]))⁻¹ ⊗ₜ[ℤ_[l]] w = 0) : ∃ c : ℤ_[l], c ≠ 0 ∧ c • w = 0 := by
  have hb' : (b : ℚ_[l]) ≠ 0 := by rwa [Ne, PadicInt.coe_eq_zero]
  have h1 : (1 : ℚ_[l]) ⊗ₜ[ℤ_[l]] w = 0 := by
    have h2 := congrArg (fun t => (b : ℚ_[l]) • t) h
    simpa [TensorProduct.smul_tmul', hb'] using h2
  have hloc : IsLocalizedModule (nonZeroDivisors ℤ_[l]) (TensorProduct.mk ℤ_[l] ℚ_[l] M 1) := inferInstance
  obtain ⟨c, hc⟩ := (IsLocalizedModule.eq_zero_iff (nonZeroDivisors ℤ_[l]) (TensorProduct.mk ℤ_[l] ℚ_[l] M 1)).1 h1
  exact ⟨c, nonZeroDivisors.ne_zero c.2, hc⟩

/- English proof (translation)
Unfold `QOnto`. Introduce `hI hLim l _ k _ _ hl G d e Z X p ι h n m hn U hU hprop z hz`. Take `⟨b, x, hb, rfl⟩` from `H0LimitCoherence.tensor_form l z`. Establish `hz' : ((b : ℚ_[l]))⁻¹ ⊗ₜ[ℤ_[l]] (pullHl l (sch.map U.ι) m 0 x) = 0`. Simplify `hz` using `[pb, pullHQ, LinearMap.baseChange_tmul]`.

Take `⟨c, hc, hcx⟩` from `tors_of b hb _ hz'`. Establish `hunit : ∀ j : ℕ, IsUnit (((l ^ j : ℕ)) : k)` using `fun j => by`. Use `push_cast`. Conclude with `(IsUnit.mk0 _ hl).pow j`. Establish `hne : ∀ j : ℕ, NeZero (l ^ j)` using `fun j => ⟨pow_ne_zero _ (Fact.out : l.Prime).ne_zero⟩`.

Establish `hfin : ∀ j : ℕ, Finite (Ht (l ^ j) (sch.obj Z) n 0)` using `fun j => by haveI := hne j haveI := hprop`. Conclude with `hI.e4 (l ^ j) k (hunit j) (ι ≫ p) n 0`. Use `set x' : Hl l (sch.obj X) m 0 := c • x with hx'`. Establish `hpull : pullHl l (sch.map U.ι) m 0 x' = 0`. Rewrite using `[hx', map_smul]`.

Conclude with `hcx`. Establish `hlev : ∀ j, ∃ a, G.g j h hn a = x'.1 j` using `fun j => by`. Establish `h0 : pull _ (sch.map U.ι) (tw (l ^ j) 0) m (x'.1 j) = 0`. Use `congrArg (fun t : Hl l (sch.obj U) m 0 => t.1 j) hpull` as an intermediate fact. Conclude with `this`.

Conclude with `(G.exact j h hn U hU _).1 h0`. Take `⟨a, ha, hfa⟩` from `hLim (fun j => Ht (l ^ j) (sch.obj Z) n 0) (fun j => Ht (l ^ j) (sch.obj X) m 0) (fun j => red (l ^ (j + 1)) (l ^ j) _ n 0) (fun j => red (l ^ (j + 1)) (l ^ j) _ m 0) (fun j => G.g j h hn) (fun j a => G.red j h hn a) (fun j => x'.1 j) (fun j => x'.2 j) hlev`. Set `a' : Hl l (sch.obj Z) n 0` to `⟨a, ha⟩`. Establish `hga : G.hl h hn a' = x'` using `Subtype.ext (funext hfa)`. Use `⟨(((b * c : ℤ_[l]) : ℚ_[l]))⁻¹ ⊗ₜ a', ?_⟩` and prove the remaining obligations.

Establish `hc' : (c : ℚ_[l]) ≠ 0` using `by rwa [Ne, PadicInt.coe_eq_zero]`. Establish `hb' : (b : ℚ_[l]) ≠ 0` using `by rwa [Ne, PadicInt.coe_eq_zero]`. Express the relevant statement in the definitionally equal form `(G.hl h hn).baseChange ℚ_[l] _ = _`. Rewrite using `[LinearMap.baseChange_tmul, hga, hx', ← TensorProduct.smul_tmul, Algebra.smul_def]`. Use `congr 1`.

Establish `hal : algebraMap ℤ_[l] ℚ_[l] c = (c : ℚ_[l])` using `rfl`. Rewrite using `[hal, PadicInt.coe_mul]`. Clear the denominators using the available nonvanishing facts.
-/
theorem UpperTheory.Gal.KunnethLefschetz.qOnto_holds :
    UpperTheory.Gal.KunnethLefschetz.QOnto := by
  unfold QOnto
  intro hI hLim l _ k _ _ hl G d e Z X p ι h n m hn U hU hprop z hz
  obtain ⟨b, x, hb, rfl⟩ := H0LimitCoherence.tensor_form l z
  have hz' : ((b : ℚ_[l]))⁻¹ ⊗ₜ[ℤ_[l]] (pullHl l (sch.map U.ι) m 0 x) = 0 := by
    simpa [pb, pullHQ, LinearMap.baseChange_tmul] using hz
  obtain ⟨c, hc, hcx⟩ := tors_of b hb _ hz'
  have hunit : ∀ j : ℕ, IsUnit (((l ^ j : ℕ)) : k) := fun j => by
    push_cast
    exact (IsUnit.mk0 _ hl).pow j
  have hne : ∀ j : ℕ, NeZero (l ^ j) := fun j => ⟨pow_ne_zero _ (Fact.out : l.Prime).ne_zero⟩
  have hfin : ∀ j : ℕ, Finite (Ht (l ^ j) (sch.obj Z) n 0) := fun j => by
    haveI := hne j
    haveI := hprop
    exact hI.e4 (l ^ j) k (hunit j) (ι ≫ p) n 0
  set x' : Hl l (sch.obj X) m 0 := c • x with hx'
  have hpull : pullHl l (sch.map U.ι) m 0 x' = 0 := by
    rw [hx', map_smul]; exact hcx
  have hlev : ∀ j, ∃ a, G.g j h hn a = x'.1 j := fun j => by
    have h0 : pull _ (sch.map U.ι) (tw (l ^ j) 0) m (x'.1 j) = 0 := by
      have := congrArg (fun t : Hl l (sch.obj U) m 0 => t.1 j) hpull
      exact this
    exact (G.exact j h hn U hU _).1 h0
  obtain ⟨a, ha, hfa⟩ := hLim (fun j => Ht (l ^ j) (sch.obj Z) n 0) (fun j => Ht (l ^ j) (sch.obj X) m 0)
    (fun j => red (l ^ (j + 1)) (l ^ j) _ n 0) (fun j => red (l ^ (j + 1)) (l ^ j) _ m 0)
    (fun j => G.g j h hn) (fun j a => G.red j h hn a) (fun j => x'.1 j) (fun j => x'.2 j) hlev
  let a' : Hl l (sch.obj Z) n 0 := ⟨a, ha⟩
  have hga : G.hl h hn a' = x' := Subtype.ext (funext hfa)
  refine ⟨(((b * c : ℤ_[l]) : ℚ_[l]))⁻¹ ⊗ₜ a', ?_⟩
  have hc' : (c : ℚ_[l]) ≠ 0 := by rwa [Ne, PadicInt.coe_eq_zero]
  have hb' : (b : ℚ_[l]) ≠ 0 := by rwa [Ne, PadicInt.coe_eq_zero]
  change (G.hl h hn).baseChange ℚ_[l] _ = _
  rw [LinearMap.baseChange_tmul, hga, hx', ← TensorProduct.smul_tmul, Algebra.smul_def]
  congr 1
  have hal : algebraMap ℤ_[l] ℚ_[l] c = (c : ℚ_[l]) := rfl
  rw [hal, PadicInt.coe_mul]
  field_simp

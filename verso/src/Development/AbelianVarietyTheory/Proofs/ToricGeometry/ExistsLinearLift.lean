import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaUnifAV
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj Complex Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped BigOperators Real

namespace GlobalTheory.EndoLinear

/- English proof (translation)
Establish `hc : ContinuousAt G 0` using `hG.continuousAt`. Establish `h2 : Tendsto (fun w : E => w + w) (𝓝 0) (𝓝 0)`. Establish `: Continuous (fun w : E => w + w)` using `by fun_prop`. Simplify using `using this.tendsto 0`. Establish `hG0 : Tendsto G (𝓝 0) (𝓝 0)` using `by simpa [h0] using hc.tendsto`.

Establish `hD : Tendsto (fun w : E => G (w + w) - (G w + G w)) (𝓝 0) (𝓝 0)`. Simplify using `using (hG0.comp h2).sub (hG0.add hG0)`. Establish `hmem : ∀ᶠ w in 𝓝 (0 : E), G (w + w) - (G w + G w) ∈ Λ` using `by filter_upwards [hev, h2.eventually hev] with w hw hw2`. Rewrite using `[← hker]`. Establish `h` using `hex (G (w + w) - (G w + G w)) (G w + G w)`.

Rewrite `h` using `[sub_add_cancel, hw2, hex (G w), hw, ha]`. Conclude with `(mul_eq_right.mp h.symm)`. Establish `hiso : ∀ᶠ y in 𝓝 (0 : E'), y ∈ Λ → y = 0`. Establish `ho : IsOpen ({0} : Set Λ)` using `isOpen_discrete _`. Take `⟨t, ht, hts⟩` from `isOpen_induced_iff.mp ho`.

Establish `h0t : (0 : E') ∈ t`. Establish `: (0 : Λ) ∈ Subtype.val ⁻¹' t` using `by rw [hts]; rfl`. Conclude with `this`. Use `filter_upwards [ht.mem_nhds h0t] with y hy hyΛ`. Establish `: (⟨y, hyΛ⟩ : Λ) ∈ Subtype.val ⁻¹' t` using `hy`.

Rewrite `this` using `[hts]`. Conclude with `congrArg Subtype.val this`. Establish `hdbl : ∀ᶠ w in 𝓝 (0 : E), G (w + w) = G w + G w` using `by filter_upwards [hmem, hD.eventually hiso] with w h1 h2`. Conclude with `sub_eq_zero.mp (h2 h1)`. Use `set c : ℕ → ℂ := fun n => (2 : ℂ) ^ n with hcdef`.

Establish `hcn : Tendsto (fun n => ‖c n‖) atTop atTop`. Simplify using `only [hcdef, norm_pow, Complex.norm_ofNat]`. Conclude with `tendsto_pow_atTop_atTop_of_one_lt one_lt_two`. Establish `hz : Tendsto (fun n => (c n)⁻¹ • z) atTop (𝓝 0)`. Establish `: Tendsto (fun n => (c n)⁻¹) atTop (𝓝 0)`.

Rewrite using `[tendsto_zero_iff_norm_tendsto_zero]`. Simplify using `only [norm_inv]`. Conclude with `hcn.inv_tendsto_atTop`. Simplify using `using this.smul_const z`. Establish `hhalf : ∀ n, (c n)⁻¹ • z = (c (n + 1))⁻¹ • z + (c (n + 1))⁻¹ • z`.

Introduce `n`. Rewrite using `[← add_smul]`. Use `congr 1`. Simplify using `only [hcdef, pow_succ]`. Clear the denominators using the available nonvanishing facts.

Evaluate the numerical expressions. Establish `hlim : Tendsto (fun n => c n • G ((c n)⁻¹ • z)) atTop (𝓝 (fderiv ℂ G 0 z))`. Use `hG.hasFDerivAt.lim z hcn` as an intermediate fact. Simplify `this` using `[h0]`. Take `⟨N, hN⟩` from `eventually_atTop.mp (hz.eventually (hdbl.and hev))`.

Establish `hconst : ∀ n, N ≤ n → c n • G ((c n)⁻¹ • z) = c N • G ((c N)⁻¹ • z)`. Introduce `n hn`. Proceed by induction on `n, hn using Nat.le_induction with`. Consider the case `base => rfl`. Consider the case `succ n hn ih`.

Rewrite using `[← ih, hhalf n, (hN (n + 1) (by omega)).1, ← two_smul ℂ, smul_smul]`. Simplify using `only [hcdef, pow_succ]`. Establish `hF : fderiv ℂ G 0 z = c N • G ((c N)⁻¹ • z)`. Use `tendsto_nhds_unique hlim ?_` and prove the remaining obligations. Use `tendsto_const_nhds.congr' ?_` and prove the remaining obligations.

Use `filter_upwards [eventually_ge_atTop N] with n hn using (hconst n hn).symm`. Establish `hpow : ∀ (n : ℕ) (x : E') (y : E), ex x = a y → ex (c n • x) = a (c n • y)`. Introduce `n x y h`. Proceed by induction on `n with`. Consider the case `zero => simpa [hcdef] using h`.

Consider the case `succ n ih`. Establish `e : c (n + 1) = c n + c n` using `by simp only [hcdef, pow_succ]; ring`. Rewrite using `[e, add_smul, add_smul, hex, ha, ih]`. Rewrite using `[hF, hpow N _ _ (hN N le_rfl).2, smul_smul, mul_inv_cancel₀ (pow_ne_zero _ two_ne_zero), one_smul]`.
-/
theorem fderiv_lifts {E E' M : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedAddCommGroup E']
    [NormedSpace ℂ E'] [Group M] (ex : E' → M) (hex : ∀ z w, ex (z + w) = ex z * ex w)
    (Λ : Submodule ℤ E') (hker : ∀ z, ex z = 1 ↔ z ∈ Λ) (hd : DiscreteTopology Λ)
    (a : E → M) (ha : ∀ z w, a (z + w) = a z * a w) (G : E → E') (h0 : G 0 = 0)
    (hG : DifferentiableAt ℂ G 0) (hev : ∀ᶠ w in 𝓝 0, ex (G w) = a w) (z : E) :
    ex (fderiv ℂ G 0 z) = a z := by
  have hc : ContinuousAt G 0 := hG.continuousAt
  have h2 : Tendsto (fun w : E => w + w) (𝓝 0) (𝓝 0) := by
    have : Continuous (fun w : E => w + w) := by fun_prop
    simpa using this.tendsto 0
  have hG0 : Tendsto G (𝓝 0) (𝓝 0) := by simpa [h0] using hc.tendsto
  have hD : Tendsto (fun w : E => G (w + w) - (G w + G w)) (𝓝 0) (𝓝 0) := by
    simpa using (hG0.comp h2).sub (hG0.add hG0)
  have hmem : ∀ᶠ w in 𝓝 (0 : E), G (w + w) - (G w + G w) ∈ Λ := by
    filter_upwards [hev, h2.eventually hev] with w hw hw2
    rw [← hker]
    have h := hex (G (w + w) - (G w + G w)) (G w + G w)
    rw [sub_add_cancel, hw2, hex (G w), hw, ha] at h
    exact (mul_eq_right.mp h.symm)
  have hiso : ∀ᶠ y in 𝓝 (0 : E'), y ∈ Λ → y = 0 := by
    have ho : IsOpen ({0} : Set Λ) := isOpen_discrete _
    obtain ⟨t, ht, hts⟩ := isOpen_induced_iff.mp ho
    have h0t : (0 : E') ∈ t := by
      have : (0 : Λ) ∈ Subtype.val ⁻¹' t := by rw [hts]; rfl
      exact this
    filter_upwards [ht.mem_nhds h0t] with y hy hyΛ
    have : (⟨y, hyΛ⟩ : Λ) ∈ Subtype.val ⁻¹' t := hy
    rw [hts] at this
    exact congrArg Subtype.val this
  have hdbl : ∀ᶠ w in 𝓝 (0 : E), G (w + w) = G w + G w := by
    filter_upwards [hmem, hD.eventually hiso] with w h1 h2
    exact sub_eq_zero.mp (h2 h1)
  set c : ℕ → ℂ := fun n => (2 : ℂ) ^ n with hcdef
  have hcn : Tendsto (fun n => ‖c n‖) atTop atTop := by
    simp only [hcdef, norm_pow, Complex.norm_ofNat]
    exact tendsto_pow_atTop_atTop_of_one_lt one_lt_two
  have hz : Tendsto (fun n => (c n)⁻¹ • z) atTop (𝓝 0) := by
    have : Tendsto (fun n => (c n)⁻¹) atTop (𝓝 0) := by
      rw [tendsto_zero_iff_norm_tendsto_zero]
      simp only [norm_inv]
      exact hcn.inv_tendsto_atTop
    simpa using this.smul_const z
  have hhalf : ∀ n, (c n)⁻¹ • z = (c (n + 1))⁻¹ • z + (c (n + 1))⁻¹ • z := by
    intro n
    rw [← add_smul]
    congr 1
    simp only [hcdef, pow_succ]
    field_simp
    norm_num
  have hlim : Tendsto (fun n => c n • G ((c n)⁻¹ • z)) atTop (𝓝 (fderiv ℂ G 0 z)) := by
    have := hG.hasFDerivAt.lim z hcn
    simpa [h0] using this
  obtain ⟨N, hN⟩ := eventually_atTop.mp (hz.eventually (hdbl.and hev))
  have hconst : ∀ n, N ≤ n → c n • G ((c n)⁻¹ • z) = c N • G ((c N)⁻¹ • z) := by
    intro n hn
    induction n, hn using Nat.le_induction with
    | base => rfl
    | succ n hn ih =>
      rw [← ih, hhalf n, (hN (n + 1) (by omega)).1, ← two_smul ℂ, smul_smul]
      simp only [hcdef, pow_succ]
  have hF : fderiv ℂ G 0 z = c N • G ((c N)⁻¹ • z) := by
    refine tendsto_nhds_unique hlim ?_
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_ge_atTop N] with n hn using (hconst n hn).symm
  have hpow : ∀ (n : ℕ) (x : E') (y : E), ex x = a y → ex (c n • x) = a (c n • y) := by
    intro n x y h
    induction n with
    | zero => simpa [hcdef] using h
    | succ n ih =>
      have e : c (n + 1) = c n + c n := by simp only [hcdef, pow_succ]; ring
      rw [e, add_smul, add_smul, hex, ha, ih]
  rw [hF, hpow N _ _ (hN N le_rfl).2, smul_smul, mul_inv_cancel₀ (pow_ne_zero _ two_ne_zero), one_smul]

/- English proof (translation)
Introduce `hval A _ L g u hlift f hf`. Establish `h0 : u.ex 0 = 1` using `(u.ker 0).mpr u.Λ.zero_mem`. Take `⟨G, hG0, hGa, hGe⟩` from `hlift g (fun z => u.ex z ≫ f) (by`. Introduce `U s`. Establish `hset : {w | w ∈ (Set.univ : Set (Fin g → ℂ)) ∧ ⊤ ≤ (u.ex w ≫ f).left ⁻¹ᵁ U} = {w | ⊤ ≤ (u.ex w).left ⁻¹ᵁ (f.left ⁻¹ᵁ U)}`.

Use extensionality with `w`. Simplify using the standard rewrite rules. Establish `hfun : (fun w => valAt' (u.ex w ≫ f).left U s) = fun w => valAt' (u.ex w).left (f.left ⁻¹ᵁ U) ((f.left.app U).hom s)`. Use function extensionality and compare the values at `w`. Conclude with `((hval A.left (u.ex w).left).2.2.2.1 A.left f.left U s).symm`.

Rewrite using `[hset, hfun]`. Conclude with `u.hol _ _) (by simp only [h0]; exact MonObj.one_comp f)`. Use `⟨(fderiv ℂ G 0).toLinearMap, fun z => ?_⟩` and prove the remaining obligations. Conclude with `fderiv_lifts u.ex u.ex_add u.Λ u.ker u.discrete (fun z => u.ex z ≫ f) (fun z w => by simp only [u.ex_add]; exact MonObj.mul_comp _ _ f) G hG0 hGa.differentiableAt hGe z`.
-/
theorem exists_linear_lift :
    (∀ (X : Scheme.{0}) (x : Sp ℂ ⟶ X), (∀ (U : X.Opens), ⊤ ≤ x ⁻¹ᵁ U ↔ x (default : PrimeSpectrum ℂ) ∈ U) ∧ (∀ (U : X.Opens), ⊤ ≤ x ⁻¹ᵁ U → ∃ e : Γ(X, U) →+* ℂ, ∀ f, valAt' x U f = e f) ∧ (∀ (U V : X.Opens) (h : V ≤ U) (f : Γ(X, U)), ⊤ ≤ x ⁻¹ᵁ V → valAt' x V (resG X h f) = valAt' x U f) ∧ (∀ (Y : Scheme.{0}) (φ : X ⟶ Y) (U : Y.Opens) (f : Γ(Y, U)), valAt' x (φ ⁻¹ᵁ U) ((φ.app U).hom f) = valAt' (x ≫ φ) U f) ∧ (∀ (U : X.Opens) (f : Γ(X, U)), ⊤ ≤ x ⁻¹ᵁ X.basicOpen f ↔ valAt' x U f ≠ 0) ∧ (∀ (p : X ⟶ Sp ℂ), x ≫ p = 𝟙 _ → ∀ (U : X.Opens) (a : ℂ), ⊤ ≤ x ⁻¹ᵁ U → valAt' x U (constFn p U a) = a)) → (∀ (A : Over (Sp ℂ)) [GrpObj A] (L : LB A.left) (g : ℕ) (u : HolUnif A L g), (∀ (n : ℕ) (a : (Fin n → ℂ) → (𝟙_ (Over (Sp ℂ)) ⟶ A)), (∀ (U : (A).left.Opens) (f : Γ((A).left, U)), IsOpen {w | w ∈ (Set.univ : Set (Fin n → ℂ)) ∧ ⊤ ≤ (a w).left ⁻¹ᵁ U} ∧ DifferentiableOn ℂ (fun w => valAt' (a w).left U f) {w | w ∈ (Set.univ : Set (Fin n → ℂ)) ∧ ⊤ ≤ (a w).left ⁻¹ᵁ U}) → a 0 = 1 → ∃ G : (Fin n → ℂ) → (Fin g → ℂ), G 0 = 0 ∧ AnalyticAt ℂ G 0 ∧ ∀ᶠ w in 𝓝 0, u.ex (G w) = a w) → ∀ f : A ⟶ A, IsMonHom f → ∃ F : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ), ∀ z, u.ex (F z) = u.ex z ≫ f) := by
  intro hval A _ L g u hlift f hf
  have h0 : u.ex 0 = 1 := (u.ker 0).mpr u.Λ.zero_mem
  obtain ⟨G, hG0, hGa, hGe⟩ := hlift g (fun z => u.ex z ≫ f) (by
    intro U s
    have hset : {w | w ∈ (Set.univ : Set (Fin g → ℂ)) ∧ ⊤ ≤ (u.ex w ≫ f).left ⁻¹ᵁ U} =
        {w | ⊤ ≤ (u.ex w).left ⁻¹ᵁ (f.left ⁻¹ᵁ U)} := by
      ext w
      simp
    have hfun : (fun w => valAt' (u.ex w ≫ f).left U s) =
        fun w => valAt' (u.ex w).left (f.left ⁻¹ᵁ U) ((f.left.app U).hom s) := by
      funext w
      exact ((hval A.left (u.ex w).left).2.2.2.1 A.left f.left U s).symm
    rw [hset, hfun]
    exact u.hol _ _) (by simp only [h0]; exact MonObj.one_comp f)
  refine ⟨(fderiv ℂ G 0).toLinearMap, fun z => ?_⟩
  exact fderiv_lifts u.ex u.ex_add u.Λ u.ker u.discrete (fun z => u.ex z ≫ f)
    (fun z w => by simp only [u.ex_add]; exact MonObj.mul_comp _ _ f) G hG0 hGa.differentiableAt hGe z

end GlobalTheory.EndoLinear

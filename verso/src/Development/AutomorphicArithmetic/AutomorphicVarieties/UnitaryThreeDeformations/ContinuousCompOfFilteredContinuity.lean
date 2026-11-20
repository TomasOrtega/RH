import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeDeformations.FiniteResidue
import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeDeformations.ExistsUniqueIsPtHom
import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeDeformations.UnivGr
import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeDeformations.Adjoin
import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.NormCob
import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.DefCoc
import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.ZetaReducibleRepEqSubInvAndIsUnit
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.GrInternal

open Matrix IsLocalRing ReciprocityTheory.Gal UpperTheory.V.HV UpperTheory.V.U3 UpperTheory.V.Alg UpperTheory.V.UnitaryThreeInertia

/- English proof (translation)
Take `⟨k, π, hπ⟩` from `Module.Finite.exists_fin' ℤ_[l] M`. Use `haveI : ContinuousSMul ℤ_[l] (PadicAlgCl l) := ⟨by`. Establish `: (fun p : ℤ_[l] × PadicAlgCl l => p.1 • p.2) = fun p => (p.1 : ℚ_[l]) • p.2`. Use function extensionality and compare the values at `p`. Conclude with `(algebraMap_smul ℚ_[l] p.1 p.2).symm`.

Rewrite using `[this]`. Conclude with `(continuous_subtype_val.comp continuous_fst).smul continuous_snd⟩`. Establish `hc : Continuous (φ ∘ₗ π)` using `LinearMap.continuous_on_pi _`. Establish `hcl : ∀ n, IsClosed {x | π x ∈ N n}` using `fun n => by`. Use `AddSubgroup.isClosed_of_isOpen ((N n).comap π.toAddMonoidHom) (AddSubgroup.isOpen_of_mem_nhds _ (g := 0) ?_)` and prove the remaining obligations.

Establish `hp : (0 : ℝ) < (l : ℝ) ^ (-n : ℤ)` using `zpow_pos (by exact_mod_cast (Fact.out : l.Prime).pos) _`. Use `Filter.mem_of_superset (Metric.closedBall_mem_nhds 0 hp) fun x hx => ?_` and prove the remaining obligations. Rewrite `hx` using `[mem_closedBall_zero_iff, pi_norm_le_iff_of_nonneg hp.le]`. Establish `h1 : ∀ i, ∃ y, x i = (l : ℤ_[l]) ^ n * y` using `fun i => Ideal.mem_span_singleton.1 ((PadicInt.norm_le_pow_iff_mem_span_pow _ _).1 (hx i))`. Use `choose y hy using h1`.

Establish `: x = ((l : ℤ_[l]) ^ n) • y` using `funext hy`. Use `show π x ∈ N n`. Rewrite using `[this, map_smul]`. Conclude with `hl _ _`. Rewrite using `[continuous_iff_continuousAt]`.

Introduce `g₀`. Rewrite using `[ContinuousAt, Metric.tendsto_nhds]`. Introduce `ε hε`. Establish `key : ∃ n, ∀ x, π x ∈ N n → ‖φ (π x)‖ < ε`. Assume the negation of the conclusion as `hcon`.

Use `push Not at hcon`. Establish `hc2 : ∀ n, IsClosed {x | π x ∈ N n ∧ ε ≤ ‖φ (π x)‖}` using `fun n => (hcl n).inter (isClosed_le continuous_const hc.norm)`. Take `⟨x, hx⟩` from `IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed (fun n => {x | π x ∈ N n ∧ ε ≤ ‖φ (π x)‖}) (fun n x hx => ⟨hN (Nat.le_succ n) hx.1, hx.2⟩) hcon (hc2 0).isCompact hc2`. Rewrite `hx` using `[Set.mem_iInter]`. Establish `h1` using `(hx 0).2`.

Rewrite `h1` using `[h0 _ fun n => (hx n).1, map_zero, norm_zero]`. Conclude with `absurd hε (not_lt.2 h1)`. Take `⟨n, hn⟩` from `key`. Use `filter_upwards [hf n g₀] with g hg`. Take `⟨x, hx⟩` from `hπ (f g - f g₀)`.

Use `hn x (hx ▸ hg)` as an intermediate fact. Rewrite `this` using `[hx, map_sub, ← dist_eq_norm]`. Then use the resulting hypothesis.
-/
private theorem continuous_comp_of_filtered_continuity {l : ℕ} [Fact l.Prime] {M Γ : Type} [AddCommGroup M] [Module ℤ_[l] M]
    [Module.Finite ℤ_[l] M] [TopologicalSpace Γ] (N : ℕ → AddSubgroup M) (hN : Antitone N)
    (h0 : ∀ x, (∀ n, x ∈ N n) → x = 0) (hl : ∀ n x, ((l : ℤ_[l]) ^ n) • x ∈ N n)
    (φ : M →ₗ[ℤ_[l]] PadicAlgCl l) (f : Γ → M) (hf : ∀ n g₀, ∀ᶠ g in nhds g₀, f g - f g₀ ∈ N n) :
    Continuous fun g => φ (f g) := by
  obtain ⟨k, π, hπ⟩ := Module.Finite.exists_fin' ℤ_[l] M
  haveI : ContinuousSMul ℤ_[l] (PadicAlgCl l) := ⟨by
    have : (fun p : ℤ_[l] × PadicAlgCl l => p.1 • p.2) = fun p => (p.1 : ℚ_[l]) • p.2 := by
      funext p
      exact (algebraMap_smul ℚ_[l] p.1 p.2).symm
    rw [this]
    exact (continuous_subtype_val.comp continuous_fst).smul continuous_snd⟩
  have hc : Continuous (φ ∘ₗ π) := LinearMap.continuous_on_pi _
  have hcl : ∀ n, IsClosed {x | π x ∈ N n} := fun n => by
    refine AddSubgroup.isClosed_of_isOpen ((N n).comap π.toAddMonoidHom) (AddSubgroup.isOpen_of_mem_nhds _ (g := 0) ?_)
    have hp : (0 : ℝ) < (l : ℝ) ^ (-n : ℤ) := zpow_pos (by exact_mod_cast (Fact.out : l.Prime).pos) _
    refine Filter.mem_of_superset (Metric.closedBall_mem_nhds 0 hp) fun x hx => ?_
    rw [mem_closedBall_zero_iff, pi_norm_le_iff_of_nonneg hp.le] at hx
    have h1 : ∀ i, ∃ y, x i = (l : ℤ_[l]) ^ n * y := fun i =>
      Ideal.mem_span_singleton.1 ((PadicInt.norm_le_pow_iff_mem_span_pow _ _).1 (hx i))
    choose y hy using h1
    have : x = ((l : ℤ_[l]) ^ n) • y := funext hy
    show π x ∈ N n
    rw [this, map_smul]
    exact hl _ _
  rw [continuous_iff_continuousAt]
  intro g₀
  rw [ContinuousAt, Metric.tendsto_nhds]
  intro ε hε
  have key : ∃ n, ∀ x, π x ∈ N n → ‖φ (π x)‖ < ε := by
    by_contra hcon
    push Not at hcon
    have hc2 : ∀ n, IsClosed {x | π x ∈ N n ∧ ε ≤ ‖φ (π x)‖} := fun n =>
      (hcl n).inter (isClosed_le continuous_const hc.norm)
    obtain ⟨x, hx⟩ := IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed
      (fun n => {x | π x ∈ N n ∧ ε ≤ ‖φ (π x)‖}) (fun n x hx => ⟨hN (Nat.le_succ n) hx.1, hx.2⟩)
      hcon (hc2 0).isCompact hc2
    rw [Set.mem_iInter] at hx
    have h1 := (hx 0).2
    rw [h0 _ fun n => (hx n).1, map_zero, norm_zero] at h1
    exact absurd hε (not_lt.2 h1)
  obtain ⟨n, hn⟩ := key
  filter_upwards [hf n g₀] with g hg
  obtain ⟨x, hx⟩ := hπ (f g - f g₀)
  have := hn x (hx ▸ hg)
  rwa [hx, map_sub, ← dist_eq_norm] at this

/- English proof (translation)
Use `letI : Module ℤ_[l] M := Module.compHom M (algebraMap ℤ_[l] O)`. Use `haveI : IsScalarTower ℤ_[l] O M := IsScalarTower.of_compHom ℤ_[l] O M`. Use `haveI : Module.Finite ℤ_[l] M := Module.Finite.trans O M`. Establish `hloc` using `(UpperTheory.V.Base.dvrFacts l O).2.2.1`. Establish `hlm : algebraMap O R (algebraMap ℤ_[l] O l) ∈ maximalIdeal R` using `fun h => PadicInt.irreducible_p.not_isUnit (IsLocalHom.map_nonunit _ (IsLocalHom.map_nonunit _ h))`.

Use `continuous_comp_of_filtered_continuity (fun n => (maximalIdeal R ^ n).toAddSubgroup.comap M.subtype.toAddMonoidHom) (fun a b hab x hx => Ideal.pow_le_pow_right hab hx) (fun x hx => ?_) (fun n x => ?_) (φ.restrictScalars ℤ_[l]) f fun n g₀ => ?_` and prove the remaining obligations. Establish `h1 : (x : R) ∈ ⨅ n, maximalIdeal R ^ n` using `Ideal.mem_iInf.2 hx`. Rewrite `h1` using `[Ideal.iInf_pow_eq_bot_of_isLocalRing _ (maximalIdeal.isMaximal R).ne_top]`. Conclude with `Subtype.ext h1`. Use `show (algebraMap ℤ_[l] O (l ^ n)) • (x : R) ∈ maximalIdeal R ^ n`.

Rewrite using `[Algebra.smul_def, map_pow, map_pow]`. Conclude with `Ideal.mul_mem_right _ _ (Ideal.pow_mem_pow hlm n)`. Use `filter_upwards [(hf n).eventually_eq g₀] with g hg`. Conclude with `Ideal.Quotient.eq.1 hg`.
-/
private theorem cont_sub {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [Algebra ℤ_[l] O] [Module.Finite ℤ_[l] O] [Algebra O (PadicAlgCl l)] [IsScalarTower ℤ_[l] O (PadicAlgCl l)]
    {R Γ : Type} [CommRing R] [Algebra O R] [IsCO O R] [TopologicalSpace Γ] (M : Submodule O R) [Module.Finite O M]
    (φ : M →ₗ[O] PadicAlgCl l) (f : Γ → M)
    (hf : ∀ n : ℕ, IsLocallyConstant fun g => Ideal.Quotient.mk (maximalIdeal R ^ n) (f g : R)) :
    Continuous fun g => φ (f g) := by
  letI : Module ℤ_[l] M := Module.compHom M (algebraMap ℤ_[l] O)
  haveI : IsScalarTower ℤ_[l] O M := IsScalarTower.of_compHom ℤ_[l] O M
  haveI : Module.Finite ℤ_[l] M := Module.Finite.trans O M
  have hloc := (UpperTheory.V.Base.dvrFacts l O).2.2.1
  have hlm : algebraMap O R (algebraMap ℤ_[l] O l) ∈ maximalIdeal R := fun h =>
    PadicInt.irreducible_p.not_isUnit (IsLocalHom.map_nonunit _ (IsLocalHom.map_nonunit _ h))
  refine continuous_comp_of_filtered_continuity (fun n => (maximalIdeal R ^ n).toAddSubgroup.comap M.subtype.toAddMonoidHom)
    (fun a b hab x hx => Ideal.pow_le_pow_right hab hx) (fun x hx => ?_) (fun n x => ?_)
    (φ.restrictScalars ℤ_[l]) f fun n g₀ => ?_
  · have h1 : (x : R) ∈ ⨅ n, maximalIdeal R ^ n := Ideal.mem_iInf.2 hx
    rw [Ideal.iInf_pow_eq_bot_of_isLocalRing _ (maximalIdeal.isMaximal R).ne_top] at h1
    exact Subtype.ext h1
  · show (algebraMap ℤ_[l] O (l ^ n)) • (x : R) ∈ maximalIdeal R ^ n
    rw [Algebra.smul_def, map_pow, map_pow]
    exact Ideal.mul_mem_right _ _ (Ideal.pow_mem_pow hlm n)
  · filter_upwards [(hf n).eventually_eq g₀] with g hg
    exact Ideal.Quotient.eq.1 hg

private noncomputable def dualPt {O A K : Type} [CommRing O] [CommRing A] [Algebra O A] [CommRing K] [Algebra O K]
    (ξ : A →ₐ[O] K) (D : A →ₗ[O] K) (hD : D ∈ PtDer ξ K) : A →ₐ[O] DualNumber K :=
  have h1 : D 1 = 0 := by
    have := hD 1 1
    simpa using this
  { toFun := fun x => TrivSqZeroExt.inl (ξ x) + TrivSqZeroExt.inr (D x)
    map_one' := by simp [h1]
    map_mul' := fun x y => by
      ext
      · simp
      · simp [hD x y, mul_comm]
    map_zero' := by simp
    map_add' := fun x y => by ext <;> simp
    commutes' := fun a => by
      rw [Algebra.algebraMap_eq_smul_one, map_smul, map_smul, h1, map_one, Algebra.algebraMap_eq_smul_one]
      simp }

/- English proof (translation)
Both sides reduce to the same expression.
-/
private theorem dualPt_apply {O A K : Type} [CommRing O] [CommRing A] [Algebra O A] [CommRing K] [Algebra O K]
    (ξ : A →ₐ[O] K) (D : A →ₗ[O] K) (hD : D ∈ PtDer ξ K) (x : A) :
    dualPt ξ D hD x = TrivSqZeroExt.inl (ξ x) + TrivSqZeroExt.inr (D x) := rfl

/- English proof (translation)
Use `letI : GradedAlgebra 𝒜 := { toDecomposition := h𝒜.chooseDecomposition }`. Set `t0 : Multiplicative ℤ →* DualNumber K` to `{ toFun := fun j => 1 + TrivSqZeroExt.inr (a * (j.toAdd : ℤ)) map_one' := by simp map_mul' := fun i j => by`. Use `ext`. Simplify using the standard rewrite rules. Simplify using `[mul_add, add_comm] }`.

Set `ξ0 : A →ₐ[O] DualNumber K` to `(TrivSqZeroExt.inlAlgHom O K K).comp ξ`. Establish `h1 : ∀ j, ∀ x ∈ 𝒜 j, act 𝒜 t0.toHomUnits ξ0 x = TrivSqZeroExt.inl (ξ x) + TrivSqZeroExt.inr (a * j * ξ x)` using `fun j x hx => by`. Rewrite using `[act_of_mem 𝒜 _ _ hx]`. Use `ext`. Simplify using `[t0, ξ0]`.

Simplify using `[t0, ξ0, mul_comm]`. Establish `h2 : dualPt ξ D hD = act 𝒜 t0.toHomUnits ξ0`. Use `AlgHom.ext_of_adjoin_eq_top hs fun x hx => ?_` and prove the remaining obligations. Take `⟨j, hj, e⟩` from `h x hx`. Rewrite using `[h1 j x hj, dualPt_apply, e]`.

Introduce `j x hx`. Use `congrArg TrivSqZeroExt.snd ((DFunLike.congr_fun h2 x).trans (h1 j x hx))` as an intermediate fact. Simplify `this` using `[dualPt_apply]`.
-/
private theorem euler {O A K : Type} [CommRing O] [CommRing A] [Algebra O A] [CommRing K] [Algebra O K]
    (𝒜 : ℤ → Submodule O A) [SetLike.GradedMonoid 𝒜] (h𝒜 : DirectSum.IsInternal 𝒜)
    (ξ : A →ₐ[O] K) (D : A →ₗ[O] K) (hD : D ∈ PtDer ξ K) (a : K) (s : Set A) (hs : Algebra.adjoin O s = ⊤)
    (h : ∀ x ∈ s, ∃ j, x ∈ 𝒜 j ∧ D x = a * j * ξ x) : ∀ j, ∀ x ∈ 𝒜 j, D x = a * j * ξ x := by
  letI : GradedAlgebra 𝒜 := { toDecomposition := h𝒜.chooseDecomposition }
  let t0 : Multiplicative ℤ →* DualNumber K :=
    { toFun := fun j => 1 + TrivSqZeroExt.inr (a * (j.toAdd : ℤ))
      map_one' := by simp
      map_mul' := fun i j => by
        ext
        · simp
        · simp [mul_add, add_comm] }
  let ξ0 : A →ₐ[O] DualNumber K := (TrivSqZeroExt.inlAlgHom O K K).comp ξ
  have h1 : ∀ j, ∀ x ∈ 𝒜 j, act 𝒜 t0.toHomUnits ξ0 x =
      TrivSqZeroExt.inl (ξ x) + TrivSqZeroExt.inr (a * j * ξ x) := fun j x hx => by
    rw [act_of_mem 𝒜 _ _ hx]
    ext
    · simp [t0, ξ0]
    · simp [t0, ξ0, mul_comm]
  have h2 : dualPt ξ D hD = act 𝒜 t0.toHomUnits ξ0 := by
    refine AlgHom.ext_of_adjoin_eq_top hs fun x hx => ?_
    obtain ⟨j, hj, e⟩ := h x hx
    rw [h1 j x hj, dualPt_apply, e]
  intro j x hx
  have := congrArg TrivSqZeroExt.snd ((DFunLike.congr_fun h2 x).trans (h1 j x hx))
  simpa [dualPt_apply] using this

/- English proof (translation)
Substitute `e` using the available equality. Conclude with `gr_internal O ℤ R W`.
-/
private theorem internal_of {O R : Type} [CommRing O] [CommRing R] [Algebra O R] (W : WPres O ℤ R)
    (𝒜 : ℤ → Submodule O R) [SetLike.GradedMonoid 𝒜] (e : W.part = 𝒜) :
    DirectSum.IsInternal fun j => (𝒜 j).comap (gradedSub 𝒜).val.toLinearMap := by
  subst e
  exact gr_internal O ℤ R W

/- English proof (translation)
The claim follows from `SemidirectProduct.ext (Units.ext h2) h1`.
-/
private theorem gg_ext {R : Type} [CommRing R] {x y : GG 3 R} (h1 : x.right = y.right) (h2 : x.mat = y.mat) :
    x = y := SemidirectProduct.ext (Units.ext h2) h1

section Push

variable {O A B D : Type} [CommRing O] [IsLocalRing O] [CommRing A] [CommRing B] [Algebra O A] [Algebra O B] [Group D]

omit [IsLocalRing O] in
/- English proof (translation)
Establish `e : ∀ k : GL (Fin 3) A, GG.map (f : A →+* B) (GG.ofGL k) = GG.ofGL (GeneralLinearGroup.map (f : A →+* B) k)` using `fun k => rfl`. Establish `: conjBy (GeneralLinearGroup.map (f : A →+* B) h)⁻¹ (push f r) g = GG.map (f : A →+* B) (conjBy h⁻¹ r g)` using `by show GG.ofGL _ * GG.map (f : A →+* B) (r g) * (GG.ofGL _)⁻¹ = GG.map (f : A →+* B) (GG.ofGL h⁻¹ * r g * (GG.ofGL h⁻¹)⁻¹)`. Rewrite using `[map_mul, map_mul, map_inv (GG.map (f : A →+* B)), e, map_inv (GeneralLinearGroup.map (f : A →+* B))]`. Rewrite using `[this]`. Both sides reduce to the same expression.
-/
private theorem conj_push (f : A →ₐ[O] B) (r : D →* GG 3 A) (h : GL (Fin 3) A) (g : D) (a b : Fin 3) :
    (conjBy (GeneralLinearGroup.map (f : A →+* B) h)⁻¹ (push f r) g).mat a b = f ((conjBy h⁻¹ r g).mat a b) := by
  have e : ∀ k : GL (Fin 3) A, GG.map (f : A →+* B) (GG.ofGL k) = GG.ofGL (GeneralLinearGroup.map (f : A →+* B) k) :=
    fun k => rfl
  have : conjBy (GeneralLinearGroup.map (f : A →+* B) h)⁻¹ (push f r) g = GG.map (f : A →+* B) (conjBy h⁻¹ r g) := by
    show GG.ofGL _ * GG.map (f : A →+* B) (r g) * (GG.ofGL _)⁻¹ = GG.map (f : A →+* B) (GG.ofGL h⁻¹ * r g * (GG.ofGL h⁻¹)⁻¹)
    rw [map_mul, map_mul, map_inv (GG.map (f : A →+* B)), e, map_inv (GeneralLinearGroup.map (f : A →+* B))]
  rw [this]
  rfl

/- English proof (translation)
Rewrite using `[conj_push, H.tri g hg a b hab, map_zero] ine s hs h1 a := by rw [conj_push, H.ine s hs h1 a, AlgHom.commutes]`.
-/
private theorem triIn_push {η : D →* ℤˣ} {Ψ : D →* Oˣ} {I : Subgroup D} (f : A →ₐ[O] B) {r : D →* GG 3 A}
    {h : GL (Fin 3) A} (H : TriIn η Ψ I r h) : TriIn η Ψ I (push f r) (GeneralLinearGroup.map (f : A →+* B) h) where
  tri g hg a b hab := by rw [conj_push, H.tri g hg a b hab, map_zero]
  ine s hs h1 a := by rw [conj_push, H.ine s hs h1 a, AlgHom.commutes]

/- English proof (translation)
The claim follows from `triIn_push f H.toTriIn low g hg a b hab := by rw [conj_push, H.low g hg a b hab, map_zero]`.
-/
private theorem diagIn_push {η : D →* ℤˣ} {Ψ : D →* Oˣ} {I : Subgroup D} (f : A →ₐ[O] B) {r : D →* GG 3 A}
    {h : GL (Fin 3) A} (H : DiagIn η Ψ I r h) : DiagIn η Ψ I (push f r) (GeneralLinearGroup.map (f : A →+* B) h) where
  toTriIn := triIn_push f H.toTriIn
  low g hg a b hab := by rw [conj_push, H.low g hg a b hab, map_zero]

/- English proof (translation)
The claim follows from `hf (by rw [← conj_push, H.tri g hg a b hab, map_zero]) ine s hs h1 a := hf (by rw [← conj_push, H.ine s hs h1 a, AlgHom.commutes])`.
-/
private theorem triIn_pull {η : D →* ℤˣ} {Ψ : D →* Oˣ} {I : Subgroup D} (f : A →ₐ[O] B) (hf : Function.Injective f)
    {r : D →* GG 3 A} {h : GL (Fin 3) A} (H : TriIn η Ψ I (push f r) (GeneralLinearGroup.map (f : A →+* B) h)) :
    TriIn η Ψ I r h where
  tri g hg a b hab := hf (by rw [← conj_push, H.tri g hg a b hab, map_zero])
  ine s hs h1 a := hf (by rw [← conj_push, H.ine s hs h1 a, AlgHom.commutes])

/- English proof (translation)
The claim follows from `triIn_pull f hf H.toTriIn low g hg a b hab := hf (by rw [← conj_push, H.low g hg a b hab, map_zero])`.
-/
private theorem diagIn_pull {η : D →* ℤˣ} {Ψ : D →* Oˣ} {I : Subgroup D} (f : A →ₐ[O] B) (hf : Function.Injective f)
    {r : D →* GG 3 A} {h : GL (Fin 3) A} (H : DiagIn η Ψ I (push f r) (GeneralLinearGroup.map (f : A →+* B) h)) :
    DiagIn η Ψ I r h where
  toTriIn := triIn_pull f hf H.toTriIn
  low g hg a b hab := hf (by rw [← conj_push, H.low g hg a b hab, map_zero])

omit [IsLocalRing O] in
/- English proof (translation)
Establish `inj : Function.Injective ((S.val : S →+* A).mapMatrix (m` using `Fin 3)) := fun X Y e => by`. Use extensionality with `a b`. Conclude with `congrFun (congrFun e a) b`. Set `X : Matrix (Fin 3) (Fin 3) S` to `fun a b => ⟨_, h1 a b⟩`. Set `Y : Matrix (Fin 3) (Fin 3) S` to `fun a b => ⟨_, h2 a b⟩`.

Establish `eX : (S.val : S →+* A).mapMatrix X = h.val` using `rfl`. Establish `eY : (S.val : S →+* A).mapMatrix Y = (h⁻¹).val` using `rfl`. Conclude with `⟨⟨X, Y, inj (by rw [map_mul, map_one, eX, eY]; simp), inj (by rw [map_mul, map_one, eX, eY]; simp)⟩, Units.ext rfl⟩`.
-/
private theorem exists_gl (S : Subalgebra O A) (h : GL (Fin 3) A) (h1 : ∀ a b, h.val a b ∈ S)
    (h2 : ∀ a b, (h⁻¹).val a b ∈ S) : ∃ k : GL (Fin 3) S, GeneralLinearGroup.map (S.val : S →+* A) k = h := by
  have inj : Function.Injective ((S.val : S →+* A).mapMatrix (m := Fin 3)) := fun X Y e => by
    ext a b
    exact congrFun (congrFun e a) b
  let X : Matrix (Fin 3) (Fin 3) S := fun a b => ⟨_, h1 a b⟩
  let Y : Matrix (Fin 3) (Fin 3) S := fun a b => ⟨_, h2 a b⟩
  have eX : (S.val : S →+* A).mapMatrix X = h.val := rfl
  have eY : (S.val : S →+* A).mapMatrix Y = (h⁻¹).val := rfl
  exact ⟨⟨X, Y, inj (by rw [map_mul, map_one, eX, eY]; simp), inj (by rw [map_mul, map_one, eX, eY]; simp)⟩,
    Units.ext rfl⟩

end Push

/- English proof (translation)
Establish `e : (((GG.map f x).left⁻¹ : GL (Fin 3) B) : Matrix (Fin 3) (Fin 3) B) = ((x.left⁻¹ : GL (Fin 3) A) : Matrix (Fin 3) (Fin 3) A).map f` using `rfl`. Unfold `GG.adFun`. Rewrite using `[e, GG.map_mat, GG.map_right, Matrix.map_mul, Matrix.map_mul]`. Use `split_ifs`. Both sides reduce to the same expression.

Simplify using `only [thetaLie, Matrix.map_neg _ (map_neg f), Matrix.map_mul, Jmat_map, Matrix.transpose_map]`.
-/
private theorem adFun_map {A B : Type} [CommRing A] [CommRing B] (f : A →+* B) (x : GG 3 A)
    (X : Matrix (Fin 3) (Fin 3) A) : (GG.map f x).adFun (X.map f) = (x.adFun X).map f := by
  have e : (((GG.map f x).left⁻¹ : GL (Fin 3) B) : Matrix (Fin 3) (Fin 3) B) =
      ((x.left⁻¹ : GL (Fin 3) A) : Matrix (Fin 3) (Fin 3) A).map f := rfl
  unfold GG.adFun
  rw [e, GG.map_mat, GG.map_right, Matrix.map_mul, Matrix.map_mul]
  split_ifs
  · rfl
  · simp only [thetaLie, Matrix.map_neg _ (map_neg f), Matrix.map_mul, Jmat_map, Matrix.transpose_map]

/- English proof (translation)
Establish `hI : TrivSqZeroExt.kerIdeal K K * TrivSqZeroExt.kerIdeal K K = ⊥`. Rewrite using `[← pow_two]`. Conclude with `TrivSqZeroExt.kerIdeal_sq K K`. Take `⟨γ, hγ, hc, hd⟩` from `exists_isCoc (TrivSqZeroExt.kerIdeal K K) ((GG.map (algebraMap K (DualNumber K))).comp r) r' hI (by`. Use `MonoidHom.ext fun g => gg_ext (h1 g) ?_` and prove the remaining obligations.

Use extensionality with `a b`. Use `Ideal.Quotient.eq.2 ?_` and prove the remaining obligations. Use `show TrivSqZeroExt.fst ((r' g).mat a b - algebraMap K (DualNumber K) ((r g).mat a b)) = 0`. Simplify using `[h2, TrivSqZeroExt.algebraMap_eq_inl])`. Establish `e : ∀ g, γ g = ((γ g).map TrivSqZeroExt.snd).map (TrivSqZeroExt.inr : K → DualNumber K)` using `fun g => by`.

Use `Matrix.ext fun a b => ?_` and prove the remaining obligations. Establish `: (γ g a b).fst = 0` using `hγ g a b`. Apply the tactic sequence `ext <;> simp [this]`. Establish `e2 : ∀ X : Matrix (Fin 3) (Fin 3) K, X.map (TrivSqZeroExt.inr : K → DualNumber K) = (DualNumber.eps : DualNumber K) • X.map (algebraMap K (DualNumber K))` using `fun X => by`. Use `Matrix.ext fun a b => ?_` and prove the remaining obligations.

Apply the tactic sequence `ext <;> simp [TrivSqZeroExt.algebraMap_eq_inl]`. Use `⟨fun g => (γ g).map TrivSqZeroExt.snd, fun g h => ?_, fun g => ?_, fun g => ?_⟩` and prove the remaining obligations. Establish `h3` using `hc g h`. Rewrite `h3` using `[e h, e2, map_smul]`. Establish `h4 : adRep ((GG.map (algebraMap K (DualNumber K))).comp r) g (((γ h).map TrivSqZeroExt.snd).map (algebraMap K (DualNumber K))) = (adRep r g ((γ h).map TrivSqZeroExt.snd)).map (algebraMap K (DualNumber K))` using `adFun_map _ _ _`.

Rewrite `h3` using `[h4, ← e2]`. Use `Matrix.ext fun a b => ?_` and prove the remaining obligations. Simplify using `[h3]`. Simplify using `only [← e]`. Conclude with `hd g`.

Rewrite using `[(hd g).2]`. Use `Matrix.ext fun a b => ?_` and prove the remaining obligations. Establish `: ∀ c, (γ g a c).fst = 0` using `hγ g a`. Simplify using `[Matrix.mul_apply, Fin.sum_univ_three, TrivSqZeroExt.algebraMap_eq_inl, this, Matrix.add_mul, mul_comm]`.
-/
private theorem exists_coc {K Γ : Type} [CommRing K] [Group Γ] (r : Γ →* GG 3 K) (r' : Γ →* GG 3 (DualNumber K))
    (h1 : ∀ g, (r' g).right = (r g).right) (h2 : ∀ g a b, ((r' g).mat a b).fst = (r g).mat a b) :
    ∃ y : Γ → Matrix (Fin 3) (Fin 3) K, IsCoc r y ∧
      IsDeform ((GG.map (algebraMap K (DualNumber K))).comp r)
        (fun g => (y g).map (TrivSqZeroExt.inr : K → DualNumber K)) r' ∧
      ∀ g, y g * (r g).mat = (r' g).mat.map TrivSqZeroExt.snd := by
  have hI : TrivSqZeroExt.kerIdeal K K * TrivSqZeroExt.kerIdeal K K = ⊥ := by
    rw [← pow_two]; exact TrivSqZeroExt.kerIdeal_sq K K
  obtain ⟨γ, hγ, hc, hd⟩ := exists_isCoc (TrivSqZeroExt.kerIdeal K K)
    ((GG.map (algebraMap K (DualNumber K))).comp r) r' hI (by
      refine MonoidHom.ext fun g => gg_ext (h1 g) ?_
      ext a b
      refine Ideal.Quotient.eq.2 ?_
      show TrivSqZeroExt.fst ((r' g).mat a b - algebraMap K (DualNumber K) ((r g).mat a b)) = 0
      simp [h2, TrivSqZeroExt.algebraMap_eq_inl])
  have e : ∀ g, γ g = ((γ g).map TrivSqZeroExt.snd).map (TrivSqZeroExt.inr : K → DualNumber K) := fun g => by
    refine Matrix.ext fun a b => ?_
    have : (γ g a b).fst = 0 := hγ g a b
    ext <;> simp [this]
  have e2 : ∀ X : Matrix (Fin 3) (Fin 3) K, X.map (TrivSqZeroExt.inr : K → DualNumber K) =
      (DualNumber.eps : DualNumber K) • X.map (algebraMap K (DualNumber K)) := fun X => by
    refine Matrix.ext fun a b => ?_
    ext <;> simp [TrivSqZeroExt.algebraMap_eq_inl]
  refine ⟨fun g => (γ g).map TrivSqZeroExt.snd, fun g h => ?_, fun g => ?_, fun g => ?_⟩
  · have h3 := hc g h
    rw [e h, e2, map_smul] at h3
    have h4 : adRep ((GG.map (algebraMap K (DualNumber K))).comp r) g
        (((γ h).map TrivSqZeroExt.snd).map (algebraMap K (DualNumber K))) =
        (adRep r g ((γ h).map TrivSqZeroExt.snd)).map (algebraMap K (DualNumber K)) := adFun_map _ _ _
    rw [h4, ← e2] at h3
    refine Matrix.ext fun a b => ?_
    simp [h3]
  · simp only [← e]
    exact hd g
  · rw [(hd g).2]
    refine Matrix.ext fun a b => ?_
    have : ∀ c, (γ g a c).fst = 0 := hγ g a
    simp [Matrix.mul_apply, Fin.sum_univ_three, TrivSqZeroExt.algebraMap_eq_inl, this, Matrix.add_mul, mul_comm]

/- English proof (translation)
Establish `e : ∀ X, cob r X g * (r g).mat = X * (r g).mat - (r g).mat * X` using `fun X => by show (X - (r g).adFun X) * _ = _`. Unfold `GG.adFun GG.mat`. Rewrite using `[if_pos hg, Matrix.sub_mul, Matrix.mul_assoc, Units.inv_mul, Matrix.mul_one]`. Rewrite using `[e, Matrix.smul_mul, Matrix.mul_smul, Matrix.sub_apply, Matrix.smul_apply, Matrix.smul_apply, Matrix.diagonal_mul, Matrix.mul_diagonal, wt]`. Simplify using `only [smul_eq_mul, Int.cast_sub]`.

Expand and normalize the polynomial expressions, which then agree.
-/
private theorem cob_lie {K Γ : Type} [CommRing K] [Group Γ] (r : Γ →* GG 3 K) (a : K) (g : Γ) (hg : (r g).right = 1)
    (i j : Fin 3) : (cob r (a • Matrix.diagonal fun i => ((wt1 i : ℤ) : K)) g * (r g).mat) i j =
      a * (wt i j : ℤ) * (r g).mat i j := by
  have e : ∀ X, cob r X g * (r g).mat = X * (r g).mat - (r g).mat * X := fun X => by
    show (X - (r g).adFun X) * _ = _
    unfold GG.adFun GG.mat
    rw [if_pos hg, Matrix.sub_mul, Matrix.mul_assoc, Units.inv_mul, Matrix.mul_one]
  rw [e, Matrix.smul_mul, Matrix.mul_smul, Matrix.sub_apply, Matrix.smul_apply, Matrix.smul_apply,
    Matrix.diagonal_mul, Matrix.mul_diagonal, wt]
  simp only [smul_eq_mul, Int.cast_sub]
  ring

/- English proof (translation)
Introduce `R' _ _ _ f f' t e` and use `by have h1 := hx R' f f' t e simp only [zpow_zero, Units.val_one, one_mul] at h1 ⊢ have h2 : f x * f y = 1 := by rw [← map_mul, h, map_one] have h3 : f x * f' y = 1 := by rw [← h1, ← map_mul, h, map_one] linear_combination f y * h3 - f' y * h2`.
-/
private theorem inv_wpart {O R Γ : Type} [CommRing O] [IsLocalRing O] [CommRing R] [Algebra O R] [Group Γ]
    (u : Γ →* GG 3 R) {x y : R} (hx : x ∈ wpart O u 0) (h : x * y = 1) : y ∈ wpart O u 0 :=
  fun R' _ _ _ f f' t e => by
    have h1 := hx R' f f' t e
    simp only [zpow_zero, Units.val_one, one_mul] at h1 ⊢
    have h2 : f x * f y = 1 := by rw [← map_mul, h, map_one]
    have h3 : f x * f' y = 1 := by rw [← h1, ← map_mul, h, map_one]
    linear_combination f y * h3 - f' y * h2

/- English proof (translation)
Introduce `l _ O _ _ _ _ _ _ _ _ _ _ _ G Γ ι _ _ _ _ _ _ _ _ _ _ _ _ _ F hF g₁ hg R _ _ _ u hu hfin ξ r hr hrig D hD`. Take `⟨hadj, hfinj⟩` from `sring_eq_adjoin F hF g₁ hg u hu hfin`. Take `⟨W, hW, -⟩` from `exists_adapted F hF g₁ hg u hu`. Take `⟨uS, huS, -⟩` from `existsUnique_isPtHom u (AlgHom.id O (Sring O u))`. Establish `hent : ∀ g a b, (uS g).mat a b = ⟨_, mem_Sring u (entry_mem u g a b)⟩` using `fun g a b => by`.

Rewrite using `[(huS g).2]`. Both sides reduce to the same expression. Establish `hval : push (Sring O u).val uS = u` using `MonoidHom.ext fun g => gg_ext (huS g).1 (Matrix.ext fun a b => congrArg Subtype.val (hent g a b))`. Establish `hrm : ∀ g a b, (r g).mat a b = ξ ((uS g).mat a b)` using `fun g a b => by`. Rewrite using `[(hr g).2, hent]`.

Both sides reduce to the same expression. Establish `hrr : ∀ g, (r g).right = F.η g` using `fun g => (hr g).1.trans (hu.pt.mult g)`. Take `⟨y, hy, hdef, hyD⟩` from `exists_coc r (push (dualPt ξ D hD) uS) (fun g => (huS g).1.trans (hr g).1.symm) (fun g a b => by`. Rewrite using `[hrm]`. Use `show (dualPt ξ D hD ((uS g).mat a b)).fst = _`.

Simplify using `[dualPt_apply])`. Establish `hyD' : ∀ g, y g * (r g).mat = (uS g).mat.map D` using `fun g => by`. Rewrite using `[hyD]`. Use `Matrix.ext fun a b => ?_` and prove the remaining obligations. Use `show (dualPt ξ D hD ((uS g).mat a b)).snd = _`.

Simplify using `[dualPt_apply]`. Establish `hD1 : D 1 = 0` using `by simpa using hD 1 1`. Establish `hone : ∀ g, (u g).mat = 1 → (r g).mat = 1 ∧ y g = 0` using `fun g h => by`. Establish `h1 : (uS g).mat = 1` using `Matrix.ext fun a b => Subtype.ext (by`. Rewrite using `[hent, Matrix.one_apply]`.

Use `show (u g).mat a b = _`. Rewrite using `[h, Matrix.one_apply]`. Apply the tactic sequence `split_ifs <;> rfl)`. Establish `h2 : (r g).mat = 1` using `Matrix.ext fun a b => by`. Rewrite using `[hrm, h1, Matrix.one_apply, Matrix.one_apply]`.

Apply the tactic sequence `split_ifs <;> simp`. Use `⟨h2, ?_⟩` and prove the remaining obligations. Establish `h3` using `hyD' g`. Rewrite `h3` using `[h2, h1, Matrix.mul_one]`. Rewrite using `[h3]`.

Use `Matrix.ext fun a b => ?_` and prove the remaining obligations. Rewrite using `[Matrix.map_apply, Matrix.one_apply]`. Apply the tactic sequence `split_ifs <;> simp [hD1]`. Establish `hcont : ∀ φ : Sring O u →ₗ[O] PadicAlgCl l, Continuous fun g => (uS g).mat.map φ` using `fun φ => by`. Use `continuous_matrix fun a b => ?_` and prove the remaining obligations.

Use `haveI := hfinj (wt a b)`. Use `cont_sub (wpart O u (wt a b)) (φ ∘ₗ Submodule.inclusion (p' := Subalgebra.toSubmodule (Sring O u)) fun x hx => mem_Sring u hx) (fun g => ⟨_, entry_mem u g a b⟩) fun n => (hu.pt.cont n).comp fun X => X a b` as an intermediate fact. Simplify using `only [Matrix.map_apply, hent]`. Conclude with `this`. Establish `hyc : Continuous y`.

Establish `hrc : Continuous fun g => (r g).mat`. Establish `: (fun g => (r g).mat) = fun g => (uS g).mat.map ξ.toLinearMap` using `funext fun g => Matrix.ext (hrm g)`. Rewrite using `[this]`. Conclude with `hcont _`. Establish `hdet : ∀ g, IsUnit (r g).mat.det` using `fun g => (Matrix.isUnit_iff_isUnit_det _).1 (r g).left.isUnit`.

Establish `: y = fun g => (uS g).mat.map D * (((r g).mat.det)⁻¹ • (r g).mat.adjugate)` using `funext fun g => by`. Rewrite using `[← hyD', ← Ring.inverse_eq_inv, ← Matrix.inv_def, Matrix.mul_nonsing_inv_cancel_right _ _ (hdet g)]`. Rewrite using `[this]`. Conclude with `(hcont D).matrix_mul ((hrc.matrix_det.inv₀ fun g => (hdet g).ne_zero).smul hrc.matrix_adjugate)`. Establish `hbas : ∀ v ∈ F.Tb, ∃ h : GL (Fin 3) (Sring O u), (v = F.vl → TriIn (F.ηv v) (F.Ψv v) (F.Iv v) (uS.comp (F.loc v)) h) ∧ (v ∈ F.Sb → DiagIn (F.ηv v) (F.Ψv v) (F.Iv v) (uS.comp (F.loc v)) h)` using `fun v hv => by`.

Take `⟨h, -, h1, h2, h3, h4⟩` from `exists_graded_basis F hF g₁ hg u hu v hv`. Take `⟨k, rfl⟩` from `exists_gl (Sring O u) h (fun a b => mem_Sring u (h1 a b)) fun a b => mem_Sring u (h2 a b)`. Establish `e : u.comp (F.loc v) = push (Sring O u).val (uS.comp (F.loc v))` using `by conv_lhs => rw [← hval]`. Both sides reduce to the same expression. Rewrite `h3`, `h4` using `[e]`.

Conclude with `⟨k, fun e => triIn_pull _ Subtype.val_injective (h3 e), fun e => diagIn_pull _ Subtype.val_injective (h4 e)⟩`. Take `⟨X, hX⟩` from `hrig y _ hyc hy hdef (fun v hv s hs => (hone _ (by`. Establish `: u (F.loc v s) = 1` using `(hu.pt.loc v).2.2 hv s hs`. Rewrite using `[this]`. Use the proof step `rfl)).2)`.

Use the proof step `(by`. Take `⟨k, h1, -⟩` from `hbas F.vl (Set.mem_insert _ _)`. Conclude with `⟨_, triIn_push (dualPt ξ D hD) (h1 rfl)⟩)`. Use the proof step `(fun v hv => by`. Take `⟨k, -, h1⟩` from `hbas v (Set.mem_insert_of_mem _ hv)`.

Conclude with `⟨_, diagIn_push (dualPt ξ D hD) (h1 hv)⟩)`. Establish `hz : ∀ a b, (zmat F.c g₁ uS a b).val = zmat F.c g₁ u a b` using `fun a b => by`. Simplify using `only [zmat, Matrix.sub_apply, hent]`. Both sides reduce to the same expression. Establish `hzr : ∀ a b, zmat F.c g₁ r a b = ξ (zmat F.c g₁ uS a b)` using `fun a b => by`.

Simplify using `only [zmat, Matrix.sub_apply, hrm, map_sub]`. Establish `hzy : ∀ a b, zvar F.c g₁ r y a b = D (zmat F.c g₁ uS a b)` using `fun a b => by`. Simplify using `only [zvar, zmat, Matrix.sub_apply, hyD', map_sub, Matrix.map_apply]`. Establish `z12 : zmat F.c g₁ uS 0 1 = 0` using `Subtype.ext ((hz 0 1).trans hu.pt.norm.z12)`. Establish `z21 : zmat F.c g₁ uS 1 0 = 0` using `Subtype.ext ((hz 1 0).trans hu.pt.norm.z21)`.

Establish `hn : Normalised F.c g₁ r` using `⟨(hone _ hu.pt.norm.atc).1, by rw [hzr, z12, map_zero], by rw [hzr, z21, map_zero]⟩`. Establish `hnc : NormCoc F.c g₁ r y` using `⟨(hone _ hu.pt.norm.atc).2, by rw [hzy, z12, map_zero], by rw [hzy, z21, map_zero]⟩`. Establish `hzu : IsUnit (zeta F.c g₁ r)`. Establish `h1` using `(zeta_reducible_rep_eq_sub_inv_and_isUnit F.η F.Ψ F.c g₁ ⟨hF.csq, hF.ηc, hF.Ψc, hg.1, hg.2⟩).2.map (algebraMap O R)`. Establish `h2 : IsUnit (zeta F.c g₁ u)`.

Assume the negation of the conclusion as `hn`. Establish `h3 : zeta F.c g₁ u ∈ maximalIdeal R` using `hn`. Establish `h4` using `Ideal.sub_mem _ h3 (Ideal.sub_mem _ (hu.pt.red g₁ 0 0) (hu.pt.red (gstar F.c g₁) 0 0))`. Use `h4 ?_` and prove the remaining obligations. Use `h1 using 1` and compare the differences between its conclusion and the goal.

Simplify using `only [zeta, zmat, Matrix.sub_apply, Matrix.map_apply, map_sub]`. Expand and normalize the polynomial expressions, which then agree. Take `⟨w, hw⟩` from `h2.exists_right_inv`. Establish `h5 : zeta F.c g₁ u ∈ wpart O u 0` using `sub_mem (entry_mem u g₁ 0 0) (entry_mem u (gstar F.c g₁) 0 0)`. Establish `h6 : zmat F.c g₁ uS 0 0 * ⟨w, mem_Sring u (inv_wpart u h5 hw)⟩ = 1` using `Subtype.ext (by`.

Rewrite using `[MulMemClass.coe_mul, hz]`. Conclude with `hw)`. Rewrite using `[zeta, hzr]`. Conclude with `(IsUnit.of_mul_eq_one _ h6).map ξ`. Establish `hy' : y = cob r X` using `funext hX`.

Rewrite `hnc` using `[hy']`. Take `⟨a, rfl⟩` from `Submodule.mem_span_singleton.1 ((normCoc_cob_iff r F.c g₁ X (isUnit_iff_ne_zero.2 two_ne_zero) ((hrr _).trans hF.ηc) ((hrr _).trans hg.1) hn hzu).1 hnc)`. Use `letI : SetLike.GradedMonoid fun j => (wpart O u j).comap (Sring O u).val.toLinearMap := { one_mem := (SetLike.GradedOne.one_mem : (1 : R) ∈ wpart O u 0) mul_mem := fun _ _ _ _ ha hb => (SetLike.GradedMul.mul_mem ha hb : _ ∈ wpart O u _) }`. Use `⟨a, fun j x hx => euler (fun j => (wpart O u j).comap (Sring O u).val.toLinearMap) (internal_of W _ (funext hW.part)) ξ D hD a {x | ∃ g a b, F.η g = 1 ∧ x = (uS g).mat a b} ?_ ?_ j _ hx⟩` and prove the remaining obligations. Use `Subalgebra.map_injective (f := (Sring O u).val) Subtype.val_injective ?_` and prove the remaining obligations.

Rewrite using `[AlgHom.map_adjoin, Algebra.map_top, Subalgebra.range_val]`. Use `Eq.trans ?_ hadj.symm` and prove the remaining obligations. Use `congr 1`. Use extensionality with `x`. Simplify using `only [hent]`.

Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨_, ⟨g, a, b, h, rfl⟩, rfl⟩`. Conclude with `⟨g, a, b, h, rfl⟩`. Introduce and unpack `⟨g, a, b, h, rfl⟩`. Conclude with `⟨_, ⟨g, a, b, h, rfl⟩, rfl⟩`.

Introduce and unpack `_ ⟨g, i, k, h, rfl⟩`. Use `⟨wt i k, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[hent]`. Conclude with `entry_mem u g i k`. Rewrite using `[← hrm, ← cob_lie r a g ((hrr g).trans h), ← hX, hyD']`.

Both sides reduce to the same expression.
-/
theorem UpperTheory.V.UnitaryThreeInertia.tangent_eq_orbit :
    ∀ {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsAdicComplete (maximalIdeal O) O] [CharZero O] [Finite (ResidueField O)]
      [Algebra ℤ_[l] O] [Module.Finite ℤ_[l] O] [Algebra O (PadicAlgCl l)] [IsScalarTower ℤ_[l] O (PadicAlgCl l)] [FaithfulSMul O (PadicAlgCl l)]
      {G Γ ι : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
      [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [CompactSpace Γ] [T2Space Γ] [TotallyDisconnectedSpace Γ] [Finite ι] (F : Frame O G Γ ι), F.Ok →
    ∀ (g₁ : Γ), F.Marked g₁ → ∀ {R : Type} [CommRing R] [Algebra O R] [IsCO O R] (u : Γ →* GG 3 R), F.IsUniv g₁ u →
    Module.Finite O (wpart O u 0) → ∀ (ξ : Sring O u →ₐ[O] (PadicAlgCl l)) (r : Γ →* GG 3 (PadicAlgCl l)), IsPtHom u ξ r → F.Rigid r → ∀ D ∈ PtDer ξ (PadicAlgCl l), ∃ a : (PadicAlgCl l), ∀ (j : ℤ) x (hx : x ∈ wpart O u j), D ⟨x, mem_Sring u hx⟩ = a * j * ξ ⟨x, mem_Sring u hx⟩ := by
  intro l _ O _ _ _ _ _ _ _ _ _ _ _ G Γ ι _ _ _ _ _ _ _ _ _ _ _ _ _ F hF g₁ hg R _ _ _ u hu hfin ξ r hr hrig D hD
  obtain ⟨hadj, hfinj⟩ := sring_eq_adjoin F hF g₁ hg u hu hfin
  obtain ⟨W, hW, -⟩ := exists_adapted F hF g₁ hg u hu
  obtain ⟨uS, huS, -⟩ := existsUnique_isPtHom u (AlgHom.id O (Sring O u))
  have hent : ∀ g a b, (uS g).mat a b = ⟨_, mem_Sring u (entry_mem u g a b)⟩ := fun g a b => by
    rw [(huS g).2]; rfl
  have hval : push (Sring O u).val uS = u :=
    MonoidHom.ext fun g => gg_ext (huS g).1 (Matrix.ext fun a b => congrArg Subtype.val (hent g a b))
  have hrm : ∀ g a b, (r g).mat a b = ξ ((uS g).mat a b) := fun g a b => by
    rw [(hr g).2, hent]; rfl
  have hrr : ∀ g, (r g).right = F.η g := fun g => (hr g).1.trans (hu.pt.mult g)
  obtain ⟨y, hy, hdef, hyD⟩ := exists_coc r (push (dualPt ξ D hD) uS) (fun g => (huS g).1.trans (hr g).1.symm)
    (fun g a b => by
      rw [hrm]
      show (dualPt ξ D hD ((uS g).mat a b)).fst = _
      simp [dualPt_apply])
  have hyD' : ∀ g, y g * (r g).mat = (uS g).mat.map D := fun g => by
    rw [hyD]
    refine Matrix.ext fun a b => ?_
    show (dualPt ξ D hD ((uS g).mat a b)).snd = _
    simp [dualPt_apply]
  have hD1 : D 1 = 0 := by simpa using hD 1 1
  have hone : ∀ g, (u g).mat = 1 → (r g).mat = 1 ∧ y g = 0 := fun g h => by
    have h1 : (uS g).mat = 1 := Matrix.ext fun a b => Subtype.ext (by
      rw [hent, Matrix.one_apply]
      show (u g).mat a b = _
      rw [h, Matrix.one_apply]
      split_ifs <;> rfl)
    have h2 : (r g).mat = 1 := Matrix.ext fun a b => by
      rw [hrm, h1, Matrix.one_apply, Matrix.one_apply]
      split_ifs <;> simp
    refine ⟨h2, ?_⟩
    have h3 := hyD' g
    rw [h2, h1, Matrix.mul_one] at h3
    rw [h3]
    refine Matrix.ext fun a b => ?_
    rw [Matrix.map_apply, Matrix.one_apply]
    split_ifs <;> simp [hD1]
  have hcont : ∀ φ : Sring O u →ₗ[O] PadicAlgCl l, Continuous fun g => (uS g).mat.map φ := fun φ => by
    refine continuous_matrix fun a b => ?_
    haveI := hfinj (wt a b)
    have := cont_sub (wpart O u (wt a b))
      (φ ∘ₗ Submodule.inclusion (p' := Subalgebra.toSubmodule (Sring O u)) fun x hx => mem_Sring u hx)
      (fun g => ⟨_, entry_mem u g a b⟩) fun n => (hu.pt.cont n).comp fun X => X a b
    simp only [Matrix.map_apply, hent]
    exact this
  have hyc : Continuous y := by
    have hrc : Continuous fun g => (r g).mat := by
      have : (fun g => (r g).mat) = fun g => (uS g).mat.map ξ.toLinearMap := funext fun g => Matrix.ext (hrm g)
      rw [this]
      exact hcont _
    have hdet : ∀ g, IsUnit (r g).mat.det := fun g => (Matrix.isUnit_iff_isUnit_det _).1 (r g).left.isUnit
    have : y = fun g => (uS g).mat.map D * (((r g).mat.det)⁻¹ • (r g).mat.adjugate) := funext fun g => by
      rw [← hyD', ← Ring.inverse_eq_inv, ← Matrix.inv_def, Matrix.mul_nonsing_inv_cancel_right _ _ (hdet g)]
    rw [this]
    exact (hcont D).matrix_mul ((hrc.matrix_det.inv₀ fun g => (hdet g).ne_zero).smul hrc.matrix_adjugate)
  have hbas : ∀ v ∈ F.Tb, ∃ h : GL (Fin 3) (Sring O u),
      (v = F.vl → TriIn (F.ηv v) (F.Ψv v) (F.Iv v) (uS.comp (F.loc v)) h) ∧
      (v ∈ F.Sb → DiagIn (F.ηv v) (F.Ψv v) (F.Iv v) (uS.comp (F.loc v)) h) := fun v hv => by
    obtain ⟨h, -, h1, h2, h3, h4⟩ := exists_graded_basis F hF g₁ hg u hu v hv
    obtain ⟨k, rfl⟩ := exists_gl (Sring O u) h (fun a b => mem_Sring u (h1 a b)) fun a b => mem_Sring u (h2 a b)
    have e : u.comp (F.loc v) = push (Sring O u).val (uS.comp (F.loc v)) := by
      conv_lhs => rw [← hval]
      rfl
    rw [e] at h3 h4
    exact ⟨k, fun e => triIn_pull _ Subtype.val_injective (h3 e), fun e => diagIn_pull _ Subtype.val_injective (h4 e)⟩
  obtain ⟨X, hX⟩ := hrig y _ hyc hy hdef
    (fun v hv s hs => (hone _ (by
      have : u (F.loc v s) = 1 := (hu.pt.loc v).2.2 hv s hs
      rw [this]; rfl)).2)
    (by
      obtain ⟨k, h1, -⟩ := hbas F.vl (Set.mem_insert _ _)
      exact ⟨_, triIn_push (dualPt ξ D hD) (h1 rfl)⟩)
    (fun v hv => by
      obtain ⟨k, -, h1⟩ := hbas v (Set.mem_insert_of_mem _ hv)
      exact ⟨_, diagIn_push (dualPt ξ D hD) (h1 hv)⟩)
  have hz : ∀ a b, (zmat F.c g₁ uS a b).val = zmat F.c g₁ u a b := fun a b => by
    simp only [zmat, Matrix.sub_apply, hent]
    rfl
  have hzr : ∀ a b, zmat F.c g₁ r a b = ξ (zmat F.c g₁ uS a b) := fun a b => by
    simp only [zmat, Matrix.sub_apply, hrm, map_sub]
  have hzy : ∀ a b, zvar F.c g₁ r y a b = D (zmat F.c g₁ uS a b) := fun a b => by
    simp only [zvar, zmat, Matrix.sub_apply, hyD', map_sub, Matrix.map_apply]
  have z12 : zmat F.c g₁ uS 0 1 = 0 := Subtype.ext ((hz 0 1).trans hu.pt.norm.z12)
  have z21 : zmat F.c g₁ uS 1 0 = 0 := Subtype.ext ((hz 1 0).trans hu.pt.norm.z21)
  have hn : Normalised F.c g₁ r :=
    ⟨(hone _ hu.pt.norm.atc).1, by rw [hzr, z12, map_zero], by rw [hzr, z21, map_zero]⟩
  have hnc : NormCoc F.c g₁ r y :=
    ⟨(hone _ hu.pt.norm.atc).2, by rw [hzy, z12, map_zero], by rw [hzy, z21, map_zero]⟩
  have hzu : IsUnit (zeta F.c g₁ r) := by
    have h1 := (zeta_reducible_rep_eq_sub_inv_and_isUnit F.η F.Ψ F.c g₁ ⟨hF.csq, hF.ηc, hF.Ψc, hg.1, hg.2⟩).2.map (algebraMap O R)
    have h2 : IsUnit (zeta F.c g₁ u) := by
      by_contra hn
      have h3 : zeta F.c g₁ u ∈ maximalIdeal R := hn
      have h4 := Ideal.sub_mem _ h3 (Ideal.sub_mem _ (hu.pt.red g₁ 0 0) (hu.pt.red (gstar F.c g₁) 0 0))
      refine h4 ?_
      convert h1 using 1
      simp only [zeta, zmat, Matrix.sub_apply, Matrix.map_apply, map_sub]
      ring
    obtain ⟨w, hw⟩ := h2.exists_right_inv
    have h5 : zeta F.c g₁ u ∈ wpart O u 0 := sub_mem (entry_mem u g₁ 0 0) (entry_mem u (gstar F.c g₁) 0 0)
    have h6 : zmat F.c g₁ uS 0 0 * ⟨w, mem_Sring u (inv_wpart u h5 hw)⟩ = 1 := Subtype.ext (by
      rw [MulMemClass.coe_mul, hz]; exact hw)
    rw [zeta, hzr]
    exact (IsUnit.of_mul_eq_one _ h6).map ξ
  have hy' : y = cob r X := funext hX
  rw [hy'] at hnc
  obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.1
    ((normCoc_cob_iff r F.c g₁ X (isUnit_iff_ne_zero.2 two_ne_zero) ((hrr _).trans hF.ηc) ((hrr _).trans hg.1) hn hzu).1 hnc)
  letI : SetLike.GradedMonoid fun j => (wpart O u j).comap (Sring O u).val.toLinearMap :=
    { one_mem := (SetLike.GradedOne.one_mem : (1 : R) ∈ wpart O u 0)
      mul_mem := fun _ _ _ _ ha hb => (SetLike.GradedMul.mul_mem ha hb : _ ∈ wpart O u _) }
  refine ⟨a, fun j x hx => euler (fun j => (wpart O u j).comap (Sring O u).val.toLinearMap)
    (internal_of W _ (funext hW.part)) ξ D hD a {x | ∃ g a b, F.η g = 1 ∧ x = (uS g).mat a b} ?_ ?_ j _ hx⟩
  · refine Subalgebra.map_injective (f := (Sring O u).val) Subtype.val_injective ?_
    rw [AlgHom.map_adjoin, Algebra.map_top, Subalgebra.range_val]
    refine Eq.trans ?_ hadj.symm
    congr 1
    ext x
    simp only [hent]
    constructor
    · rintro ⟨_, ⟨g, a, b, h, rfl⟩, rfl⟩
      exact ⟨g, a, b, h, rfl⟩
    · rintro ⟨g, a, b, h, rfl⟩
      exact ⟨_, ⟨g, a, b, h, rfl⟩, rfl⟩
  · rintro _ ⟨g, i, k, h, rfl⟩
    refine ⟨wt i k, ?_, ?_⟩
    · rw [hent]
      exact entry_mem u g i k
    · rw [← hrm, ← cob_lie r a g ((hrr g).trans h), ← hX, hyD']
      rfl

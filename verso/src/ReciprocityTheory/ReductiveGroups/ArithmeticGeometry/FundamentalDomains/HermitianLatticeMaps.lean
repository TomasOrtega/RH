import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.RealPlaceEmbeddings

namespace ReciprocityTheory.ChartRestriction.G.FD

namespace HermitianLatticeMaps

open Matrix NumberField Module

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)
variable {ι : Type} [Fintype ι] [DecidableEq ι]

noncomputable def ty (f : Basis ι ℤ X.Λ) :
    (ι → ι → E) × (Free.ChooseBasisIndex ℤ (𝓞 E) → ι → ι → ℤ) :=
  (fun i j => herm X.Gm (f i : Fin r → E) (f j : Fin r → E),
    fun k i j => f.repr (RingOfIntegers.basis E k • f i) j)

noncomputable def mulQ (α : E) : (Fin r → E) →ₗ[ℚ] (Fin r → E) :=
  (α • LinearMap.id : (Fin r → E) →ₗ[E] (Fin r → E)).restrictScalars ℚ

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem mulQ_apply (α : E) (v : Fin r → E) : mulQ α v = α • v := rfl

noncomputable def hL (y : Fin r → E) : (Fin r → E) →ₗ[ℚ] E where
  toFun x := herm X.Gm x y
  map_add' x x' := by simp [herm, add_mul, Finset.sum_add_distrib]
  map_smul' q x := by
    simp only [herm, Pi.smul_apply, Rat.smul_def, RingHom.id_apply, Finset.mul_sum]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by ring

noncomputable def hR (x : Fin r → E) : (Fin r → E) →ₗ[ℚ] E where
  toFun y := herm X.Gm x y
  map_add' y y' := by simp [herm, cc, mul_add, Finset.sum_add_distrib]
  map_smul' q y := by
    simp only [herm, cc, Pi.smul_apply, Rat.smul_def, RingHom.id_apply, Finset.mul_sum, map_mul,
      map_ratCast]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by ring

/- English proof (translation)
Use `first`. Consider the case `(conv_lhs => rw [← f.sum_repr v]`. Rewrite using `[Submodule.coe_sum]`. Use the proof step `rfl)`. Consider the case `(conv_lhs => rw [← f.sum_repr v]`.

Rewrite using `[Submodule.coe_sum]`. Conclude with `Finset.sum_congr rfl fun i _ => Submodule.coe_smul_of_tower _ _)`. Consider the case `(conv_lhs => rw [← f.sum_repr v]`. Use `push_cast`. Use the proof step `rfl)`.

Consider the case `(have e := congrArg (fun w : X.Λ => (w : Fin r → E)) (f.sum_repr v)`. Simplify using `only [Submodule.coe_sum, Submodule.coe_smul_of_tower] at e`. Conclude with `e.symm)`.
-/
theorem coe_expand (f : Basis ι ℤ X.Λ) (v : X.Λ) :
    (v : Fin r → E) = ∑ i, f.repr v i • (f i : Fin r → E) := by
  first
    | (conv_lhs => rw [← f.sum_repr v]
       rw [Submodule.coe_sum]
       rfl)
    | (conv_lhs => rw [← f.sum_repr v]
       rw [Submodule.coe_sum]
       exact Finset.sum_congr rfl fun i _ => Submodule.coe_smul_of_tower _ _)
    | (conv_lhs => rw [← f.sum_repr v]
       push_cast
       rfl)
    | (have e := congrArg (fun w : X.Λ => (w : Fin r → E)) (f.sum_repr v)
       simp only [Submodule.coe_sum, Submodule.coe_smul_of_tower] at e
       exact e.symm)

variable (f f' : Basis ι ℤ X.Λ)

noncomputable def phi : (Fin r → E) →ₗ[ℚ] (Fin r → E) :=
  (RealPlaceEmbeddings.qb X f).constr ℚ fun i => (f' i : Fin r → E)

/- English proof (translation)
Use `first`. Consider the case `(rw [← RealPlaceEmbeddings.qb_apply X f i]; unfold phi; rw [Basis.constr_basis])`. Consider the case `(rw [← RealPlaceEmbeddings.qb_apply (X := X) f i]; unfold phi; rw [Basis.constr_basis])`. Consider the case `(have e := (RealPlaceEmbeddings.qb X f).constr_basis ℚ (fun j => (f' j : Fin r → E)) i`. Rewrite `e` using `[RealPlaceEmbeddings.qb_apply]`.

Conclude with `e)`.
-/
theorem phi_f (i : ι) : phi X f f' (f i : Fin r → E) = f' i := by
  first
    | (rw [← RealPlaceEmbeddings.qb_apply X f i]; unfold phi; rw [Basis.constr_basis])
    | (rw [← RealPlaceEmbeddings.qb_apply (X := X) f i]; unfold phi; rw [Basis.constr_basis])
    | (have e := (RealPlaceEmbeddings.qb X f).constr_basis ℚ (fun j => (f' j : Fin r → E)) i
       rw [RealPlaceEmbeddings.qb_apply] at e
       exact e)

/- English proof (translation)
Rewrite using `[map_sum]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[map_zsmul, phi_f]`.
-/
theorem phi_zsum (n : ι → ℤ) :
    phi X f f' (∑ i, n i • (f i : Fin r → E)) = ∑ i, n i • (f' i : Fin r → E) := by
  rw [map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_zsmul, phi_f]

/- English proof (translation)
Establish `e : x = ∑ i, f.repr ⟨x, hx⟩ i • (f i : Fin r → E)` using `coe_expand X f ⟨x, hx⟩`. Rewrite using `[e, phi_zsum]`. Conclude with `Submodule.sum_mem _ fun i _ => zsmul_mem (f' i).2 _`.
-/
theorem phi_mem {x : Fin r → E} (hx : x ∈ X.Λ) : phi X f f' x ∈ X.Λ := by
  have e : x = ∑ i, f.repr ⟨x, hx⟩ i • (f i : Fin r → E) := coe_expand X f ⟨x, hx⟩
  rw [e, phi_zsum]
  exact Submodule.sum_mem _ fun i _ => zsmul_mem (f' i).2 _

/- English proof (translation)
Establish `e : (phi X f' f).comp (phi X f f') = LinearMap.id`. Use `(RealPlaceEmbeddings.qb X f).ext fun i => ?_` and prove the remaining obligations. Rewrite using `[LinearMap.comp_apply, RealPlaceEmbeddings.qb_apply, phi_f, phi_f, LinearMap.id_apply]`. Conclude with `LinearMap.congr_fun e x`.
-/
theorem phi_phi (x : Fin r → E) : phi X f' f (phi X f f' x) = x := by
  have e : (phi X f' f).comp (phi X f f') = LinearMap.id := by
    refine (RealPlaceEmbeddings.qb X f).ext fun i => ?_
    rw [LinearMap.comp_apply, RealPlaceEmbeddings.qb_apply, phi_f, phi_f, LinearMap.id_apply]
  exact LinearMap.congr_fun e x

/- English proof (translation)
Use `first`. Consider the case `rfl`. Consider the case `(rw [Submodule.coe_smul]; rfl)`. Consider the case `(rw [Submodule.coe_smul, Algebra.smul_def]; rfl)`.
-/
theorem smul_coe (ω : 𝓞 E) (v : X.Λ) : ((ω • v : X.Λ) : Fin r → E) = (ω : E) • (v : Fin r → E) := by
  first
    | rfl
    | (rw [Submodule.coe_smul]; rfl)
    | (rw [Submodule.coe_smul, Algebra.smul_def]; rfl)

variable {f f'}

/- English proof (translation)
Establish `h2` using `congrArg Prod.snd h`. Establish `hk : ∀ j, f.repr (RingOfIntegers.basis E k • f i) j = f'.repr (RingOfIntegers.basis E k • f' i) j` using `fun j => congrFun (congrFun (congrFun h2 k) i) j`. Establish `e1` using `coe_expand X f (RingOfIntegers.basis E k • f i)`. Establish `e2` using `coe_expand X f' (RingOfIntegers.basis E k • f' i)`. Rewrite `e1`, `e2` using `[smul_coe]`.

Rewrite using `[e1, phi_zsum, e2]`. Simplify using `only [hk]`.
-/
theorem phi_omega (h : ty X f = ty X f') (k : Free.ChooseBasisIndex ℤ (𝓞 E)) (i : ι) :
    phi X f f' ((RingOfIntegers.basis E k : E) • (f i : Fin r → E)) =
      (RingOfIntegers.basis E k : E) • (f' i : Fin r → E) := by
  have h2 := congrArg Prod.snd h
  have hk : ∀ j, f.repr (RingOfIntegers.basis E k • f i) j =
      f'.repr (RingOfIntegers.basis E k • f' i) j :=
    fun j => congrFun (congrFun (congrFun h2 k) i) j
  have e1 := coe_expand X f (RingOfIntegers.basis E k • f i)
  have e2 := coe_expand X f' (RingOfIntegers.basis E k • f' i)
  rw [smul_coe] at e1 e2
  rw [e1, phi_zsum, e2]
  simp only [hk]

/- English proof (translation)
Establish `key : ∀ i, phi X f f' (α • (f i : Fin r → E)) = α • (f' i : Fin r → E)`. Introduce `i`. Establish `hα` using `(NumberField.integralBasis E).sum_repr α`. Rewrite using `[← hα]`. Simplify using `only [Finset.sum_smul, map_sum, smul_assoc, map_smul, NumberField.integralBasis_apply]`.

Use `Finset.sum_congr rfl fun k _ => ?_` and prove the remaining obligations. Use `congr 1`. Conclude with `phi_omega X h k i`. Establish `e : (phi X f f').comp (mulQ α) = (mulQ α).comp (phi X f f')`. Use `(RealPlaceEmbeddings.qb X f).ext fun i => ?_` and prove the remaining obligations.

Rewrite using `[LinearMap.comp_apply, LinearMap.comp_apply, mulQ_apply, mulQ_apply, RealPlaceEmbeddings.qb_apply, key, phi_f]`. Use `LinearMap.congr_fun e v` as an intermediate fact. Rewrite `this` using `[LinearMap.comp_apply, LinearMap.comp_apply, mulQ_apply, mulQ_apply]`. Then use the resulting hypothesis.
-/
theorem phi_smul (h : ty X f = ty X f') (α : E) (v : Fin r → E) :
    phi X f f' (α • v) = α • phi X f f' v := by
  have key : ∀ i, phi X f f' (α • (f i : Fin r → E)) = α • (f' i : Fin r → E) := by
    intro i
    have hα := (NumberField.integralBasis E).sum_repr α
    rw [← hα]
    simp only [Finset.sum_smul, map_sum, smul_assoc, map_smul, NumberField.integralBasis_apply]
    refine Finset.sum_congr rfl fun k _ => ?_
    congr 1
    exact phi_omega X h k i
  have e : (phi X f f').comp (mulQ α) = (mulQ α).comp (phi X f f') := by
    refine (RealPlaceEmbeddings.qb X f).ext fun i => ?_
    rw [LinearMap.comp_apply, LinearMap.comp_apply, mulQ_apply, mulQ_apply, RealPlaceEmbeddings.qb_apply, key, phi_f]
  have := LinearMap.congr_fun e v
  rwa [LinearMap.comp_apply, LinearMap.comp_apply, mulQ_apply, mulQ_apply] at this

/- English proof (translation)
Establish `h1` using `congrArg Prod.fst h`. Establish `hb : ∀ i j, herm X.Gm (f' i : Fin r → E) (f' j) = herm X.Gm (f i : Fin r → E) (f j)` using `fun i j => (congrFun (congrFun h1 i) j).symm`. Establish `s1 : ∀ i y, herm X.Gm (phi X f f' (f i)) (phi X f f' y) = herm X.Gm (f i : Fin r → E) y`. Introduce `i y`. Establish `e : (hR X (phi X f f' (f i))).comp (phi X f f') = hR X (f i)`.

Use `(RealPlaceEmbeddings.qb X f).ext fun j => ?_` and prove the remaining obligations. Rewrite using `[LinearMap.comp_apply, RealPlaceEmbeddings.qb_apply, phi_f, phi_f]`. Conclude with `hb i j`. Conclude with `LinearMap.congr_fun e y`. Establish `e2 : (hL X (phi X f f' y)).comp (phi X f f') = hL X y`.

Use `(RealPlaceEmbeddings.qb X f).ext fun i => ?_` and prove the remaining obligations. Rewrite using `[LinearMap.comp_apply, RealPlaceEmbeddings.qb_apply]`. Conclude with `s1 i y`. Conclude with `LinearMap.congr_fun e2 x`.
-/
theorem phi_herm (h : ty X f = ty X f') (x y : Fin r → E) :
    herm X.Gm (phi X f f' x) (phi X f f' y) = herm X.Gm x y := by
  have h1 := congrArg Prod.fst h
  have hb : ∀ i j, herm X.Gm (f' i : Fin r → E) (f' j) = herm X.Gm (f i : Fin r → E) (f j) :=
    fun i j => (congrFun (congrFun h1 i) j).symm
  have s1 : ∀ i y, herm X.Gm (phi X f f' (f i)) (phi X f f' y) =
      herm X.Gm (f i : Fin r → E) y := by
    intro i y
    have e : (hR X (phi X f f' (f i))).comp (phi X f f') = hR X (f i) := by
      refine (RealPlaceEmbeddings.qb X f).ext fun j => ?_
      rw [LinearMap.comp_apply, RealPlaceEmbeddings.qb_apply, phi_f, phi_f]
      exact hb i j
    exact LinearMap.congr_fun e y
  have e2 : (hL X (phi X f f' y)).comp (phi X f f') = hL X y := by
    refine (RealPlaceEmbeddings.qb X f).ext fun i => ?_
    rw [LinearMap.comp_apply, RealPlaceEmbeddings.qb_apply]
    exact s1 i y
  exact LinearMap.congr_fun e2 x

noncomputable def phiE (h : ty X f = ty X f') : (Fin r → E) →ₗ[E] (Fin r → E) where
  toFun := phi X f f'
  map_add' := map_add _
  map_smul' := phi_smul X h

/- English proof (translation)
Establish `h' : ty X f' = ty X f` using `h.symm`. Establish `hc : (phiE X h).comp (phiE X h') = LinearMap.id` using `LinearMap.ext fun v => phi_phi X f' f v`. Establish `hc' : (phiE X h').comp (phiE X h) = LinearMap.id` using `LinearMap.ext fun v => phi_phi X f f' v`. Establish `hMM : LinearMap.toMatrix' (phiE X h) * LinearMap.toMatrix' (phiE X h') = 1`. Rewrite using `[← LinearMap.toMatrix'_comp, hc, LinearMap.toMatrix'_id]`.

Establish `hMM' : LinearMap.toMatrix' (phiE X h') * LinearMap.toMatrix' (phiE X h) = 1`. Rewrite using `[← LinearMap.toMatrix'_comp, hc', LinearMap.toMatrix'_id]`. Establish `hv : ∀ v, LinearMap.toMatrix' (phiE X h) *ᵥ v = phi X f f' v` using `fun v => LinearMap.toMatrix'_mulVec (phiE X h) v`. Establish `hv' : ∀ v, LinearMap.toMatrix' (phiE X h') *ᵥ v = phi X f' f v` using `fun v => LinearMap.toMatrix'_mulVec (phiE X h') v`. Use `⟨⟨LinearMap.toMatrix' (phiE X h), LinearMap.toMatrix' (phiE X h'), hMM, hMM'⟩, ⟨fun x y => ?_, fun x => ?_⟩, fun i => ?_, fun v => ?_⟩` and prove the remaining obligations.

Use `show herm X.Gm (LinearMap.toMatrix' (phiE X h) *ᵥ x) (LinearMap.toMatrix' (phiE X h) *ᵥ y) = _`. Rewrite using `[hv, hv, phi_herm X h]`. Use `show x ∈ X.Λ ↔ LinearMap.toMatrix' (phiE X h) *ᵥ x ∈ X.Λ`. Rewrite using `[hv]`. Use `⟨phi_mem X f f', fun hx => ?_⟩` and prove the remaining obligations.

Rewrite using `[← phi_phi X f f' x]`. Conclude with `phi_mem X f' f hx`. Use `show LinearMap.toMatrix' (phiE X h) *ᵥ _ = _`. Rewrite using `[hv, phi_f]`. Use `show LinearMap.toMatrix' (phiE X h') *ᵥ v = _`.

Rewrite using `[hv', phi, Basis.constr_apply_fintype]`. Simplify using `only [Basis.equivFun_apply]`.
-/
theorem exists_gl (h : ty X f = ty X f') :
    ∃ γ : GL (Fin r) E, IsUStab X.Gm X.Λ γ ∧
      (∀ i, (γ : Matrix (Fin r) (Fin r) E) *ᵥ (f i : Fin r → E) = f' i) ∧
      ∀ v, ((γ⁻¹ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E) *ᵥ v =
        ∑ i, (RealPlaceEmbeddings.qb X f').repr v i • (f i : Fin r → E) := by
  have h' : ty X f' = ty X f := h.symm
  have hc : (phiE X h).comp (phiE X h') = LinearMap.id :=
    LinearMap.ext fun v => phi_phi X f' f v
  have hc' : (phiE X h').comp (phiE X h) = LinearMap.id :=
    LinearMap.ext fun v => phi_phi X f f' v
  have hMM : LinearMap.toMatrix' (phiE X h) * LinearMap.toMatrix' (phiE X h') = 1 := by
    rw [← LinearMap.toMatrix'_comp, hc, LinearMap.toMatrix'_id]
  have hMM' : LinearMap.toMatrix' (phiE X h') * LinearMap.toMatrix' (phiE X h) = 1 := by
    rw [← LinearMap.toMatrix'_comp, hc', LinearMap.toMatrix'_id]
  have hv : ∀ v, LinearMap.toMatrix' (phiE X h) *ᵥ v = phi X f f' v := fun v =>
    LinearMap.toMatrix'_mulVec (phiE X h) v
  have hv' : ∀ v, LinearMap.toMatrix' (phiE X h') *ᵥ v = phi X f' f v := fun v =>
    LinearMap.toMatrix'_mulVec (phiE X h') v
  refine ⟨⟨LinearMap.toMatrix' (phiE X h), LinearMap.toMatrix' (phiE X h'), hMM, hMM'⟩,
    ⟨fun x y => ?_, fun x => ?_⟩, fun i => ?_, fun v => ?_⟩
  · show herm X.Gm (LinearMap.toMatrix' (phiE X h) *ᵥ x) (LinearMap.toMatrix' (phiE X h) *ᵥ y) = _
    rw [hv, hv, phi_herm X h]
  · show x ∈ X.Λ ↔ LinearMap.toMatrix' (phiE X h) *ᵥ x ∈ X.Λ
    rw [hv]
    refine ⟨phi_mem X f f', fun hx => ?_⟩
    rw [← phi_phi X f f' x]
    exact phi_mem X f' f hx
  · show LinearMap.toMatrix' (phiE X h) *ᵥ _ = _
    rw [hv, phi_f]
  · show LinearMap.toMatrix' (phiE X h') *ᵥ v = _
    rw [hv', phi, Basis.constr_apply_fintype]
    simp only [Basis.equivFun_apply]

end HermitianLatticeMaps

end ReciprocityTheory.ChartRestriction.G.FD

import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.LengthCommensurableMapIffOfInjective

universe u_1 u_2 u_3

namespace GlobalTheory.SignedLengthMapLogDet

open Module

section Order

variable {R : Type*} [CommRing R] [IsDomain R]

/- English proof (translation)
Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty => simp`. Consider the case `insert i s hi ih`. Rewrite using `[Finset.prod_insert hi, Finset.sum_insert hi, Ring.ord_mul' R (mem_nonZeroDivisors_of_ne_zero (ha i)), ih]`.
-/
theorem ord_prod {ι : Type*} (s : Finset ι) (a : ι → R) (ha : ∀ i, a i ≠ 0) :
    Ring.ord R (∏ i ∈ s, a i) = ∑ i ∈ s, Ring.ord R (a i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih =>
    rw [Finset.prod_insert hi, Finset.sum_insert hi,
      Ring.ord_mul' R (mem_nonZeroDivisors_of_ne_zero (ha i)), ih]

/- English proof (translation)
Use `set N := LinearMap.range f with hN`. Set `b` to `Module.Free.chooseBasis R M`. Set `e : M ≃ₗ[R] N` to `LinearEquiv.ofInjective f hf`. Establish `h : finrank R N = finrank R M` using `e.symm.finrank_eq`. Set `a` to `Submodule.smithNormalFormCoeffs b h`.

Set `top` to `Submodule.smithNormalFormTopBasis b h`. Set `bot` to `Submodule.smithNormalFormBotBasis b h`. Set `e' : M ≃ₗ[R] N` to `top.equiv bot (Equiv.refl _)`. Establish `hdiag : LinearMap.toMatrix top top (N.subtype ∘ₗ (e' : M →ₗ[R] N)) = Matrix.diagonal a`. Use extensionality with `i j`.

Establish `: ((e' (top j) : N) : M) = a j • top j`. Rewrite using `[Basis.equiv_apply, Equiv.refl_apply]`. Conclude with `Submodule.smithNormalFormBotBasis_def b h j`. Rewrite using `[LinearMap.toMatrix_apply, LinearMap.comp_apply, LinearEquiv.coe_coe, Submodule.subtype_apply, this, map_smul, Basis.repr_self, Matrix.diagonal_apply]`. Use `split_ifs with hij`.

Substitute `hij` using the available equality. Simplify using the standard rewrite rules. Simplify using `[Finsupp.single_eq_of_ne hij]`. Establish `hassoc : Associated (LinearMap.det f) (∏ i, a i)`. Rewrite using `[← Matrix.det_diagonal, ← hdiag, LinearMap.det_toMatrix]`.

Conclude with `LinearMap.associated_det_comp_equiv N.subtype e e'`. Rewrite using `[Ring.ord_eq_of_associated hassoc, ord_prod _ _ (Submodule.smithNormalFormCoeffs_ne_zero b h), (Submodule.quotientEquivPiSpan N b h).length_eq, Module.length_pi_of_fintype]`. Both sides reduce to the same expression.
-/
theorem length_coker_eq_ord_det [IsPrincipalIdealRing R] {M : Type*} [AddCommGroup M] [Module R M]
    [Module.Free R M] [Module.Finite R M] (f : M →ₗ[R] M) (hf : Function.Injective f) :
    Module.length R (M ⧸ LinearMap.range f) = Ring.ord R (LinearMap.det f) := by
  classical
  set N := LinearMap.range f with hN
  let b := Module.Free.chooseBasis R M
  let e : M ≃ₗ[R] N := LinearEquiv.ofInjective f hf
  have h : finrank R N = finrank R M := e.symm.finrank_eq
  let a := Submodule.smithNormalFormCoeffs b h
  let top := Submodule.smithNormalFormTopBasis b h
  let bot := Submodule.smithNormalFormBotBasis b h
  let e' : M ≃ₗ[R] N := top.equiv bot (Equiv.refl _)
  have hdiag : LinearMap.toMatrix top top (N.subtype ∘ₗ (e' : M →ₗ[R] N)) = Matrix.diagonal a := by
    ext i j
    have : ((e' (top j) : N) : M) = a j • top j := by
      rw [Basis.equiv_apply, Equiv.refl_apply]
      exact Submodule.smithNormalFormBotBasis_def b h j
    rw [LinearMap.toMatrix_apply, LinearMap.comp_apply, LinearEquiv.coe_coe,
      Submodule.subtype_apply, this, map_smul, Basis.repr_self, Matrix.diagonal_apply]
    split_ifs with hij
    · subst hij; simp
    · simp [Finsupp.single_eq_of_ne hij]
  have hassoc : Associated (LinearMap.det f) (∏ i, a i) := by
    rw [← Matrix.det_diagonal, ← hdiag, LinearMap.det_toMatrix]
    exact LinearMap.associated_det_comp_equiv N.subtype e e'
  rw [Ring.ord_eq_of_associated hassoc,
    ord_prod _ _ (Submodule.smithNormalFormCoeffs_ne_zero b h),
    (Submodule.quotientEquivPiSpan N b h).length_eq, Module.length_pi_of_fintype]
  rfl

end Order

section Chain

variable {R V : Type*} [Ring R] [AddCommGroup V] [Module R V]

/- English proof (translation)
Establish `hle : C.submoduleOf A ≤ B.submoduleOf A` using `Submodule.comap_mono hCB`. Set `i : B →ₗ[R] A ⧸ C.submoduleOf A` to `(C.submoduleOf A).mkQ ∘ₗ Submodule.inclusion hBA`. Establish `hker : LinearMap.ker i = C.submoduleOf B`. Use extensionality with `x`. Conclude with `Submodule.Quotient.mk_eq_zero (C.submoduleOf A)`.

Establish `hex : Function.Exact (LinearMap.range i).subtype (Submodule.factor hle)`. Introduce `y`. Take `⟨y, rfl⟩` from `Submodule.Quotient.mk_surjective _ y`. Prove the components needed by the constructor for the conclusion. Introduce `hy`.

Establish `hy' : (y : V) ∈ B` using `(Submodule.Quotient.mk_eq_zero (B.submoduleOf A)).mp hy`. Conclude with `⟨⟨_, ⟨⟨y, hy'⟩, rfl⟩⟩, rfl⟩`. Introduce and unpack `⟨⟨_, x, rfl⟩, hx⟩`. Rewrite using `[← hx]`. Conclude with `(Submodule.Quotient.mk_eq_zero (B.submoduleOf A)).mpr x.2`.

Rewrite using `[relLength_eq_length_range i hker, relLength_def, relLength_def, add_comm]`. Conclude with `Module.length_eq_add_of_exact _ _ (Submodule.injective_subtype _) (Submodule.factor_surjective hle) hex`.
-/
theorem relLength_chain {A B C : Submodule R V} (hBA : B ≤ A) (hCB : C ≤ B) :
    relLength A C = relLength A B + relLength B C := by
  have hle : C.submoduleOf A ≤ B.submoduleOf A := Submodule.comap_mono hCB
  let i : B →ₗ[R] A ⧸ C.submoduleOf A := (C.submoduleOf A).mkQ ∘ₗ Submodule.inclusion hBA
  have hker : LinearMap.ker i = C.submoduleOf B := by
    ext x
    exact Submodule.Quotient.mk_eq_zero (C.submoduleOf A)
  have hex : Function.Exact (LinearMap.range i).subtype (Submodule.factor hle) := by
    intro y
    obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ y
    constructor
    · intro hy
      have hy' : (y : V) ∈ B := (Submodule.Quotient.mk_eq_zero (B.submoduleOf A)).mp hy
      exact ⟨⟨_, ⟨⟨y, hy'⟩, rfl⟩⟩, rfl⟩
    · rintro ⟨⟨_, x, rfl⟩, hx⟩
      rw [← hx]
      exact (Submodule.Quotient.mk_eq_zero (B.submoduleOf A)).mpr x.2
  rw [relLength_eq_length_range i hker, relLength_def, relLength_def, add_comm]
  exact Module.length_eq_add_of_exact _ _ (Submodule.injective_subtype _)
    (Submodule.factor_surjective hle) hex

/- English proof (translation)
Rewrite `hm` using `[relLength_chain (inf_le_left : A ⊓ B ≤ A) (le_inf hA hB), relLength_inf_right]`. Rewrite `hn` using `[relLength_chain (inf_le_right : A ⊓ B ≤ B) (le_inf hA hB), relLength_inf_right']`. Unfold `LengthCommensurable signedLength`. Generalize the expression as in `relLength A B = x at *`. Generalize the expression as in `relLength B A = y at *`.

Generalize the expression as in `relLength (A ⊓ B) C = w at *`. Apply the tactic sequence `cases x <;> cases y <;> cases w <;> try simp at hm hn`. Normalize the coercions in `at hm hn`. Use `⟨by simp, ?_⟩` and prove the remaining obligations. Simplify using `only [ENat.toNat_coe]`.

Use linear arithmetic over natural numbers and integers.
-/
theorem signedLength_of_common {A B C : Submodule R V} (hA : C ≤ A) (hB : C ≤ B) {m n : ℕ}
    (hm : relLength A C = m) (hn : relLength B C = n) :
    LengthCommensurable A B ∧ signedLength A B = (m : ℤ) - n := by
  rw [relLength_chain (inf_le_left : A ⊓ B ≤ A) (le_inf hA hB), relLength_inf_right] at hm
  rw [relLength_chain (inf_le_right : A ⊓ B ≤ B) (le_inf hA hB), relLength_inf_right'] at hn
  unfold LengthCommensurable signedLength
  generalize relLength A B = x at *
  generalize relLength B A = y at *
  generalize relLength (A ⊓ B) C = w at *
  cases x <;> cases y <;> cases w <;> try simp at hm hn
  norm_cast at hm hn
  refine ⟨by simp, ?_⟩
  simp only [ENat.toNat_coe]
  omega

end Chain

section Lattice

variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]
  {V : Type*} [AddCommGroup V] [Module K V] [Module R V] [IsScalarTower R K V]

/- English proof (translation)
Set `b` to `Module.Free.chooseBasis R A`. Set `c` to `b.extendOfIsLattice K`. Establish `: Module.Finite K V` using `Module.Finite.of_basis c`. Set `f : A →ₗ[R] A` to `(φ.restrictScalars R).restrict hA`. Establish `hinj : Function.Injective φ` using `((LinearMap.isUnit_iff_isUnit_det φ).mpr hφ.isUnit |> (Module.End.isUnit_iff φ).mp).1`.

Establish `hf : Function.Injective f` using `fun x y h => Subtype.ext (hinj (congrArg Subtype.val h))`. Establish `hdet : LinearMap.det φ = algebraMap R K (LinearMap.det f)`. Rewrite using `[← LinearMap.det_toMatrix c, ← LinearMap.det_toMatrix b, RingHom.map_det]`. Use `congr 1`. Use extensionality with `i j`.

Establish `: φ (c j) = ∑ k, algebraMap R K (b.repr (f (b j)) k) • c k`. Establish `h1 : φ (c j) = (f (b j) : V)`. Rewrite using `[Basis.extendOfIsLattice_apply]`. Both sides reduce to the same expression. Establish `h2` using `congrArg Subtype.val (b.sum_repr (f (b j)))`.

Rewrite using `[h1, ← h2, Submodule.coe_sum]`. Use `Finset.sum_congr rfl fun k _ => ?_` and prove the remaining obligations. Rewrite using `[Basis.extendOfIsLattice_apply, algebraMap_smul, Submodule.coe_smul]`. Rewrite using `[LinearMap.toMatrix_apply, this, c.repr_sum_self]`. Simplify using `[LinearMap.toMatrix_apply]`.

Establish `hf0 : LinearMap.det f ≠ 0`. Introduce `h`. Rewrite `hdet` using `[h, map_zero]`. Conclude with `hφ hdet`. Establish `hnz` using `mem_nonZeroDivisors_of_ne_zero hf0`.

Take `⟨n, hn⟩` from `ENat.ne_top_iff_exists.mp (Ring.ord_ne_top hnz)`. Use `⟨n, ?_, ?_⟩` and prove the remaining obligations. Establish `: (A.map (φ.restrictScalars R)).submoduleOf A = LinearMap.range f`. Use extensionality with `x`. Prove the components needed by the constructor for the conclusion.

Introduce and unpack `⟨y, hy, h⟩`. Conclude with `⟨⟨y, hy⟩, Subtype.ext h⟩`. Introduce and unpack `⟨y, rfl⟩`. Conclude with `⟨y, y.2, rfl⟩`. Rewrite using `[relLength_def, this, length_coker_eq_ord_det f hf, hn]`.

Rewrite using `[hdet, Ring.ordFrac_eq_ord R hf0, Ring.ordMonoidWithZeroHom_eq_coe R hnz hn.symm]`. Both sides reduce to the same expression.
-/
theorem exists_relLength_map (A : Submodule R V) [Submodule.IsLattice K A] (φ : V →ₗ[K] V)
    (hφ : LinearMap.det φ ≠ 0) (hA : ∀ x ∈ A, φ x ∈ A) :
    ∃ n : ℕ, relLength A (A.map (φ.restrictScalars R)) = n ∧
      Ring.ordFrac R (LinearMap.det φ) = WithZero.exp (n : ℤ) := by
  classical
  let b := Module.Free.chooseBasis R A
  let c := b.extendOfIsLattice K
  have : Module.Finite K V := Module.Finite.of_basis c
  let f : A →ₗ[R] A := (φ.restrictScalars R).restrict hA
  have hinj : Function.Injective φ :=
    ((LinearMap.isUnit_iff_isUnit_det φ).mpr hφ.isUnit |> (Module.End.isUnit_iff φ).mp).1
  have hf : Function.Injective f := fun x y h => Subtype.ext (hinj (congrArg Subtype.val h))
  have hdet : LinearMap.det φ = algebraMap R K (LinearMap.det f) := by
    rw [← LinearMap.det_toMatrix c, ← LinearMap.det_toMatrix b, RingHom.map_det]
    congr 1
    ext i j
    have : φ (c j) = ∑ k, algebraMap R K (b.repr (f (b j)) k) • c k := by
      have h1 : φ (c j) = (f (b j) : V) := by
        rw [Basis.extendOfIsLattice_apply]; rfl
      have h2 := congrArg Subtype.val (b.sum_repr (f (b j)))
      rw [h1, ← h2, Submodule.coe_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [Basis.extendOfIsLattice_apply, algebraMap_smul, Submodule.coe_smul]
    rw [LinearMap.toMatrix_apply, this, c.repr_sum_self]
    simp [LinearMap.toMatrix_apply]
  have hf0 : LinearMap.det f ≠ 0 := by
    intro h
    rw [h, map_zero] at hdet
    exact hφ hdet
  have hnz := mem_nonZeroDivisors_of_ne_zero hf0
  obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.mp (Ring.ord_ne_top hnz)
  refine ⟨n, ?_, ?_⟩
  · have : (A.map (φ.restrictScalars R)).submoduleOf A = LinearMap.range f := by
      ext x
      constructor
      · rintro ⟨y, hy, h⟩
        exact ⟨⟨y, hy⟩, Subtype.ext h⟩
      · rintro ⟨y, rfl⟩
        exact ⟨y, y.2, rfl⟩
    rw [relLength_def, this, length_coker_eq_ord_det f hf, hn]
  · rw [hdet, Ring.ordFrac_eq_ord R hf0, Ring.ordMonoidWithZeroHom_eq_coe R hnz hn.symm]
    rfl

/- English proof (translation)
Establish `one : ∀ v : V, ∃ r : R, r ≠ 0 ∧ r • v ∈ A`. Introduce `v`. Establish `hv : v ∈ Submodule.span K (A : Set V)`. Rewrite using `[Submodule.IsLattice.span_eq_top]`. Discharge the goal by the elementary cases of `trivial`.

Proceed by induction on `hv using Submodule.span_induction with`. Consider the case `mem x hx => exact ⟨1, one_ne_zero, by simpa using hx⟩`. Consider the case `zero => exact ⟨1, one_ne_zero, by simp⟩`. Consider the case `add x y _ _ hx hy`. Take `⟨r, hr, hx⟩` from `hx`.

Take `⟨s, hs, hy⟩` from `hy`. Use `⟨r * s, mul_ne_zero hr hs, ?_⟩` and prove the remaining obligations. Rewrite using `[smul_add]`. Use `A.add_mem ?_ ?_` and prove the remaining obligations. Rewrite using `[mul_comm, mul_smul]`.

Conclude with `A.smul_mem _ hx`. Rewrite using `[mul_smul]`. Conclude with `A.smul_mem _ hy`. Consider the case `smul k x _ hx`. Take `⟨r, hr, hx⟩` from `hx`.

Take `⟨s, t, ht⟩` from `IsLocalization.exists_integer_multiple (nonZeroDivisors R) k`. Use `⟨r * s, mul_ne_zero hr (nonZeroDivisors.coe_ne_zero s), ?_⟩` and prove the remaining obligations. Rewrite using `[mul_smul, ← smul_assoc (s : R) k x, ← ht, algebraMap_smul, smul_comm]`. Conclude with `A.smul_mem _ hx`. Establish `key : ∀ B : Submodule R V, B.FG → ∃ r : R, r ≠ 0 ∧ ∀ x ∈ B, r • x ∈ A`.

Introduce `B hB`. Proceed by induction on `B, hB using Submodule.fg_sup_span_induction with`. Consider the case `bot => exact ⟨1, one_ne_zero, by simp⟩`. Consider the case `sup S v hS ih`. Take `⟨r, hr, hS⟩` from `ih`.

Take `⟨s, hs, hv⟩` from `one v`. Use `⟨r * s, mul_ne_zero hr hs, fun x hx => ?_⟩` and prove the remaining obligations. Take `⟨y, hy, w, hw, rfl⟩` from `Submodule.mem_sup.mp hx`. Take `⟨t, rfl⟩` from `Submodule.mem_span_singleton.mp hw`. Rewrite using `[smul_add]`.

Use `A.add_mem ?_ ?_` and prove the remaining obligations. Rewrite using `[mul_comm, mul_smul]`. Conclude with `A.smul_mem _ (hS y hy)`. Rewrite using `[smul_comm, mul_smul]`. Conclude with `A.smul_mem _ (A.smul_mem _ hv)`.

Take `⟨r, hr, h⟩` from `key (A.map (g.restrictScalars R)) ((Submodule.IsLattice.fg (A := K) (M := A)).map _)`. Conclude with `⟨r, hr, fun x hx => h _ ⟨x, hx, rfl⟩⟩`.
-/
theorem exists_smul_preserves (A : Submodule R V) [Submodule.IsLattice K A] (g : V →ₗ[K] V) :
    ∃ r : R, r ≠ 0 ∧ ∀ x ∈ A, r • g x ∈ A := by
  have one : ∀ v : V, ∃ r : R, r ≠ 0 ∧ r • v ∈ A := by
    intro v
    have hv : v ∈ Submodule.span K (A : Set V) := by
      rw [Submodule.IsLattice.span_eq_top]; trivial
    induction hv using Submodule.span_induction with
    | mem x hx => exact ⟨1, one_ne_zero, by simpa using hx⟩
    | zero => exact ⟨1, one_ne_zero, by simp⟩
    | add x y _ _ hx hy =>
      obtain ⟨r, hr, hx⟩ := hx
      obtain ⟨s, hs, hy⟩ := hy
      refine ⟨r * s, mul_ne_zero hr hs, ?_⟩
      rw [smul_add]
      refine A.add_mem ?_ ?_
      · rw [mul_comm, mul_smul]; exact A.smul_mem _ hx
      · rw [mul_smul]; exact A.smul_mem _ hy
    | smul k x _ hx =>
      obtain ⟨r, hr, hx⟩ := hx
      obtain ⟨s, t, ht⟩ := IsLocalization.exists_integer_multiple (nonZeroDivisors R) k
      refine ⟨r * s, mul_ne_zero hr (nonZeroDivisors.coe_ne_zero s), ?_⟩
      rw [mul_smul, ← smul_assoc (s : R) k x, ← ht, algebraMap_smul, smul_comm]
      exact A.smul_mem _ hx
  have key : ∀ B : Submodule R V, B.FG → ∃ r : R, r ≠ 0 ∧ ∀ x ∈ B, r • x ∈ A := by
    intro B hB
    induction B, hB using Submodule.fg_sup_span_induction with
    | bot => exact ⟨1, one_ne_zero, by simp⟩
    | sup S v hS ih =>
      obtain ⟨r, hr, hS⟩ := ih
      obtain ⟨s, hs, hv⟩ := one v
      refine ⟨r * s, mul_ne_zero hr hs, fun x hx => ?_⟩
      obtain ⟨y, hy, w, hw, rfl⟩ := Submodule.mem_sup.mp hx
      obtain ⟨t, rfl⟩ := Submodule.mem_span_singleton.mp hw
      rw [smul_add]
      refine A.add_mem ?_ ?_
      · rw [mul_comm, mul_smul]; exact A.smul_mem _ (hS y hy)
      · rw [smul_comm, mul_smul]; exact A.smul_mem _ (A.smul_mem _ hv)
  obtain ⟨r, hr, h⟩ := key (A.map (g.restrictScalars R))
    ((Submodule.IsLattice.fg (A := K) (M := A)).map _)
  exact ⟨r, hr, fun x hx => h _ ⟨x, hx, rfl⟩⟩

end Lattice

/- English proof (translation)
Establish `: Module.Finite K V` using `Module.Finite.of_basis ((Module.Free.chooseBasis R A).extendOfIsLattice K)`. Take `⟨r, hr, hrA⟩` from `exists_smul_preserves A g`. Establish `hrK : algebraMap R K r ≠ 0` using `by simpa using hr`. Set `μ : V →ₗ[K] V` to `algebraMap R K r • LinearMap.id`. Establish `hμx : ∀ x, μ x = r • x` using `fun x => by simp [μ]`.

Establish `hμ : LinearMap.det μ ≠ 0`. Rewrite using `[LinearMap.det_smul, LinearMap.det_id, mul_one]`. Conclude with `pow_ne_zero _ hrK`. Establish `hinj : Function.Injective g` using `((LinearMap.isUnit_iff_isUnit_det g).mpr hg.isUnit |> (Module.End.isUnit_iff g).mp).1`. Establish `hcomp : ∀ x ∈ A, (g ∘ₗ μ) x ∈ A` using `fun x hx => by`.

Rewrite using `[LinearMap.comp_apply, hμx, LinearMap.map_smul_of_tower]`. Conclude with `hrA x hx`. Establish `hμA : ∀ x ∈ A, μ x ∈ A` using `fun x hx => by`. Rewrite using `[hμx]`. Conclude with `A.smul_mem _ hx`.

Take `⟨m, hm, hm'⟩` from `exists_relLength_map A (g ∘ₗ μ) (by rw [LinearMap.det_comp]; exact mul_ne_zero hg hμ) hcomp`. Take `⟨n, hn, hn'⟩` from `exists_relLength_map A μ hμ hμA`. Establish `hmap : A.map ((g ∘ₗ μ).restrictScalars R) = (A.map (μ.restrictScalars R)).map (g.restrictScalars R)`. Rewrite using `[← Submodule.map_comp]`. Both sides reduce to the same expression.

Rewrite `hn` using `[← relLength_map_of_injective (g.restrictScalars R) hinj, ← hmap]`. Take `⟨h₁, h₂⟩` from `signedLength_of_common (A := A) (B := A.map (g.restrictScalars R)) (C := A.map ((g ∘ₗ μ).restrictScalars R)) (by rintro _ ⟨x, hx, rfl⟩; exact hcomp x hx) (by rintro _ ⟨x, hx, rfl⟩; exact ⟨μ x, hμA x hx, rfl⟩) hm hn`. Use `⟨h₁, ?_⟩` and prove the remaining obligations. Rewrite `hm'` using `[LinearMap.det_comp, map_mul, hn']`. Establish `: Ring.ordFrac R (LinearMap.det g) = WithZero.exp ((m : ℤ) - n)`.

Rewrite using `[WithZero.exp_sub, ← hm', mul_div_cancel_right₀ _ WithZero.exp_ne_zero]`. Rewrite using `[h₂, this, WithZero.log_exp]`.
-/
theorem signedLength_map_eq_log_ordFrac_det
    {R : Type u_1} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    {K : Type u_2} [Field K] [Algebra R K] [IsFractionRing R K]
    {V : Type u_3} [AddCommGroup V] [Module K V] [Module R V] [IsScalarTower R K V]
    (A : Submodule R V) [Submodule.IsLattice K A] (g : V →ₗ[K] V) (hg : LinearMap.det g ≠ 0) :
    LengthCommensurable A (A.map (g.restrictScalars R)) ∧
      signedLength A (A.map (g.restrictScalars R)) =
        WithZero.log (Ring.ordFrac R (LinearMap.det g)) := by
  have : Module.Finite K V :=
    Module.Finite.of_basis ((Module.Free.chooseBasis R A).extendOfIsLattice K)
  obtain ⟨r, hr, hrA⟩ := exists_smul_preserves A g
  have hrK : algebraMap R K r ≠ 0 := by simpa using hr
  let μ : V →ₗ[K] V := algebraMap R K r • LinearMap.id
  have hμx : ∀ x, μ x = r • x := fun x => by simp [μ]
  have hμ : LinearMap.det μ ≠ 0 := by
    rw [LinearMap.det_smul, LinearMap.det_id, mul_one]
    exact pow_ne_zero _ hrK
  have hinj : Function.Injective g :=
    ((LinearMap.isUnit_iff_isUnit_det g).mpr hg.isUnit |> (Module.End.isUnit_iff g).mp).1
  have hcomp : ∀ x ∈ A, (g ∘ₗ μ) x ∈ A := fun x hx => by
    rw [LinearMap.comp_apply, hμx, LinearMap.map_smul_of_tower]
    exact hrA x hx
  have hμA : ∀ x ∈ A, μ x ∈ A := fun x hx => by
    rw [hμx]; exact A.smul_mem _ hx
  obtain ⟨m, hm, hm'⟩ := exists_relLength_map A (g ∘ₗ μ)
    (by rw [LinearMap.det_comp]; exact mul_ne_zero hg hμ) hcomp
  obtain ⟨n, hn, hn'⟩ := exists_relLength_map A μ hμ hμA
  have hmap : A.map ((g ∘ₗ μ).restrictScalars R) =
      (A.map (μ.restrictScalars R)).map (g.restrictScalars R) := by
    rw [← Submodule.map_comp]; rfl
  rw [← relLength_map_of_injective (g.restrictScalars R) hinj, ← hmap] at hn
  obtain ⟨h₁, h₂⟩ := signedLength_of_common
    (A := A) (B := A.map (g.restrictScalars R)) (C := A.map ((g ∘ₗ μ).restrictScalars R))
    (by rintro _ ⟨x, hx, rfl⟩; exact hcomp x hx)
    (by rintro _ ⟨x, hx, rfl⟩; exact ⟨μ x, hμA x hx, rfl⟩) hm hn
  refine ⟨h₁, ?_⟩
  rw [LinearMap.det_comp, map_mul, hn'] at hm'
  have : Ring.ordFrac R (LinearMap.det g) = WithZero.exp ((m : ℤ) - n) := by
    rw [WithZero.exp_sub, ← hm', mul_div_cancel_right₀ _ WithZero.exp_ne_zero]
  rw [h₂, this, WithZero.log_exp]

end GlobalTheory.SignedLengthMapLogDet

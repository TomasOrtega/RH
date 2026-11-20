import Mathlib

noncomputable section

open Module

namespace PositivityTheory.RgUd.TP.Loc.Ptf

section Fibre

variable {R V : Type*} [CommRing R] [AddCommGroup V] [Module R V]

/- English proof (translation)
Proceed by induction on `w using Submodule.Quotient.induction_on with`. Consider the case `H v => rfl`.
-/
theorem mk_smul (I : Ideal R) (r : R) (w : V ⧸ (I • (⊤ : Submodule R V))) :
    (Ideal.Quotient.mk I r) • w = r • w := by
  induction w using Submodule.Quotient.induction_on with
  | H v => rfl

/- English proof (translation)
Rewrite using `[← Submodule.map_le_iff_le_comap, Submodule.map_smul'']`. Conclude with `Submodule.smul_mono le_rfl le_top`.
-/
theorem le_comap (I : Ideal R) (x : V →ₗ[R] V) :
    I • (⊤ : Submodule R V) ≤ (I • (⊤ : Submodule R V)).comap x := by
  rw [← Submodule.map_le_iff_le_comap, Submodule.map_smul'']
  exact Submodule.smul_mono le_rfl le_top

def xq (I : Ideal R) (x : V →ₗ[R] V) :
    (V ⧸ (I • (⊤ : Submodule R V))) →ₗ[R ⧸ I] (V ⧸ (I • (⊤ : Submodule R V))) where
  toFun := Submodule.mapQ _ _ x (le_comap I x)
  map_add' := map_add _
  map_smul' c w := by
    obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective c
    simp only [RingHom.id_apply, mk_smul]
    exact map_smul _ r w

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem xq_mk (I : Ideal R) (x : V →ₗ[R] V) (v : V) :
    xq I x (Submodule.Quotient.mk v) = Submodule.Quotient.mk (x v) := rfl

/- English proof (translation)
The claim follows from `LinearMap.ext fun w => by induction w using Submodule.Quotient.induction_on with | H v => exact h v`.
-/
theorem xq_ext (I : Ideal R) {f g : (V ⧸ (I • (⊤ : Submodule R V))) →ₗ[R ⧸ I] (V ⧸ (I • (⊤ : Submodule R V)))}
    (h : ∀ v : V, f (Submodule.Quotient.mk v) = g (Submodule.Quotient.mk v)) : f = g :=
  LinearMap.ext fun w => by
    induction w using Submodule.Quotient.induction_on with
    | H v => exact h v

/- English proof (translation)
The claim follows from `xq_ext I fun _ => rfl`.
-/
theorem xq_mul (I : Ideal R) (x y : V →ₗ[R] V) : xq I (x * y) = xq I x * xq I y :=
  xq_ext I fun _ => rfl

/- English proof (translation)
The claim follows from `xq_ext I fun _ => rfl`.
-/
theorem xq_one (I : Ideal R) : xq I (1 : V →ₗ[R] V) = 1 := xq_ext I fun _ => rfl

/- English proof (translation)
The claim follows from `xq_ext I fun _ => rfl`.
-/
theorem xq_zero (I : Ideal R) : xq I (0 : V →ₗ[R] V) = 0 := xq_ext I fun _ => rfl

/- English proof (translation)
The claim follows from `xq_ext I fun _ => rfl`.
-/
theorem xq_add (I : Ideal R) (x y : V →ₗ[R] V) : xq I (x + y) = xq I x + xq I y :=
  xq_ext I fun _ => rfl

/- English proof (translation)
Proceed by induction on `m with`. Consider the case `zero => simp [xq_one]`. Consider the case `succ m ih => rw [pow_succ, xq_mul, ih, pow_succ]`.
-/
theorem xq_pow (I : Ideal R) (x : V →ₗ[R] V) (m : ℕ) : xq I (x ^ m) = xq I x ^ m := by
  induction m with
  | zero => simp [xq_one]
  | succ m ih => rw [pow_succ, xq_mul, ih, pow_succ]

/- English proof (translation)
Use `xq_ext I fun v => ?_` and prove the remaining obligations. Rewrite using `[LinearMap.smul_apply, xq_mk, xq_mk, LinearMap.smul_apply, ← algebraMap_smul R c (x v), ← Ideal.Quotient.mk_algebraMap, mk_smul]`. Both sides reduce to the same expression.
-/
theorem xq_smul {k : Type*} [Field k] [Algebra k R] [Module k V] [IsScalarTower k R V] (I : Ideal R) (c : k)
    (x : V →ₗ[R] V) : xq I (c • x) = (algebraMap k (R ⧸ I) c) • xq I x := by
  refine xq_ext I fun v => ?_
  rw [LinearMap.smul_apply, xq_mk, xq_mk, LinearMap.smul_apply, ← algebraMap_smul R c (x v),
    ← Ideal.Quotient.mk_algebraMap, mk_smul]
  rfl

/- English proof (translation)
Establish `e : f * φ.smulRight w = φ.smulRight (f w)`. Use extensionality with `u`. Simplify using the standard rewrite rules. Establish `e2 : φ.smulRight (f w) = dualTensorHom K W W (φ ⊗ₜ f w)`. Use extensionality with `u`.

Simplify using `[dualTensorHom_apply]`. Rewrite using `[e, e2, LinearMap.trace_eq_contract_apply]`. Simplify using the standard rewrite rules.
-/
theorem trace_comp_smulRight {K W : Type*} [Field K] [AddCommGroup W] [Module K W] [FiniteDimensional K W]
    (f : W →ₗ[K] W) (φ : Module.Dual K W) (w : W) : LinearMap.trace K W (f * φ.smulRight w) = φ (f w) := by
  have e : f * φ.smulRight w = φ.smulRight (f w) := by
    ext u
    simp
  have e2 : φ.smulRight (f w) = dualTensorHom K W W (φ ⊗ₜ f w) := by
    ext u
    simp [dualTensorHom_apply]
  rw [e, e2, LinearMap.trace_eq_contract_apply]
  simp

end Fibre

open Classical

attribute [local instance] Ideal.Quotient.field

instance isMax {R : Type*} [CommRing R] (I : MaximalSpectrum R) : I.asIdeal.IsMaximal := I.isMaximal

/- English proof (translation)
Use `haveI : Module.Finite R V := Module.Finite.of_restrictScalars_finite k R V`. Conclude with `Module.Finite.of_restrictScalars_finite R _ _`.
-/
theorem finQ (k : Type*) {R V : Type*} [Field k] [CommRing R] [Algebra k R] [AddCommGroup V] [Module R V] [Module k V]
    [IsScalarTower k R V] [FiniteDimensional k V] (I : MaximalSpectrum R) :
    FiniteDimensional (R ⧸ I.asIdeal) (V ⧸ (I.asIdeal • (⊤ : Submodule R V))) := by
  haveI : Module.Finite R V := Module.Finite.of_restrictScalars_finite k R V
  exact Module.Finite.of_restrictScalars_finite R _ _

/- English proof (translation)
Set `b` to `Module.Free.chooseBasis k (R ⧸ I.asIdeal)`. Establish `h1 : b.repr 1 ≠ 0`. Introduce `h`. Conclude with `one_ne_zero (b.repr.injective (h.trans (map_zero _).symm))`. Choose the witnesses or unpack the hypotheses as in `⟨i, hi⟩ : ∃ i, b.repr 1 i ≠ 0 := by`.

Assume the negation of the conclusion as `hne`. Use `push_neg at hne`. Conclude with `h1 (Finsupp.ext hne)`. Conclude with `⟨b.coord i, hi⟩`.
-/
theorem exists_lam (k : Type*) {R : Type*} [Field k] [CommRing R] [Algebra k R] (I : MaximalSpectrum R) :
    ∃ l : (R ⧸ I.asIdeal) →ₗ[k] k, l 1 ≠ 0 := by
  let b := Module.Free.chooseBasis k (R ⧸ I.asIdeal)
  have h1 : b.repr 1 ≠ 0 := by
    intro h
    exact one_ne_zero (b.repr.injective (h.trans (map_zero _).symm))
  obtain ⟨i, hi⟩ : ∃ i, b.repr 1 i ≠ 0 := by
    by_contra hne
    push_neg at hne
    exact h1 (Finsupp.ext hne)
  exact ⟨b.coord i, hi⟩

variable {k R V : Type*} [Field k] [CommRing R] [IsArtinianRing R] [IsReduced R] [Algebra k R]
  [AddCommGroup V] [Module R V] [Module k V] [IsScalarTower k R V] [FiniteDimensional k V]

instance : Fintype (MaximalSpectrum R) := Fintype.ofFinite _

def lam (I : MaximalSpectrum R) : (R ⧸ I.asIdeal) →ₗ[k] k := (exists_lam k I).choose

/- English proof (translation)
The claim follows from `(exists_lam k I).choose_spec`.
-/
theorem lam_one (I : MaximalSpectrum R) : lam (k := k) I 1 ≠ 0 := (exists_lam k I).choose_spec

def tI (I : MaximalSpectrum R) (x : V →ₗ[R] V) : k :=
  haveI := finQ k (V := V) I
  lam (k := k) I (LinearMap.trace (R ⧸ I.asIdeal) _ (xq I.asIdeal x))

/- English proof (translation)
Simplify using `only [tI, xq_add, map_add]`.
-/
theorem tI_add (I : MaximalSpectrum R) (x y : V →ₗ[R] V) : tI (k := k) I (x + y) = tI I x + tI I y := by
  simp only [tI, xq_add, map_add]

/- English proof (translation)
Simplify using `only [tI, xq_smul, map_smul, smul_eq_mul]`. Rewrite using `[← Algebra.smul_def, map_smul, smul_eq_mul]`.
-/
theorem tI_smul (I : MaximalSpectrum R) (c : k) (x : V →ₗ[R] V) : tI (k := k) I (c • x) = c • tI I x := by
  simp only [tI, xq_smul, map_smul, smul_eq_mul]
  rw [← Algebra.smul_def, map_smul, smul_eq_mul]

def tau : (V →ₗ[R] V) →ₗ[k] k where
  toFun x := ∑ I : MaximalSpectrum R, tI (k := k) I x
  map_add' x y := by simp only [tI_add, Finset.sum_add_distrib]
  map_smul' c x := by simp only [tI_smul, RingHom.id_apply, Finset.smul_sum]

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem tau_apply (x : V →ₗ[R] V) : tau (k := k) x = ∑ I : MaximalSpectrum R, tI (k := k) I x := rfl

/- English proof (translation)
Simplify using `only [tau_apply, tI, xq_mul, LinearMap.trace_mul_comm]`.
-/
theorem tau_comm (x y : V →ₗ[R] V) : tau (k := k) (x * y) = tau (k := k) (y * x) := by
  simp only [tau_apply, tI, xq_mul, LinearMap.trace_mul_comm]

/- English proof (translation)
Rewrite using `[tau_apply]`. Use `Finset.sum_eq_zero fun I _ => ?_` and prove the remaining obligations. Use `haveI := finQ k (V := V) I`. Take `⟨m, hm⟩` from `hx`. Establish `h1 : IsNilpotent (xq I.asIdeal x)` using `⟨m, by rw [← xq_pow, hm, xq_zero]⟩`.

Establish `h2` using `(LinearMap.isNilpotent_trace_of_isNilpotent h1).eq_zero`. Simplify using `only [tI, h2, map_zero]`.
-/
theorem tau_nil (x : V →ₗ[R] V) (hx : IsNilpotent x) : tau (k := k) x = 0 := by
  rw [tau_apply]
  refine Finset.sum_eq_zero fun I _ => ?_
  haveI := finQ k (V := V) I
  obtain ⟨m, hm⟩ := hx
  have h1 : IsNilpotent (xq I.asIdeal x) := ⟨m, by rw [← xq_pow, hm, xq_zero]⟩
  have h2 := (LinearMap.isNilpotent_trace_of_isNilpotent h1).eq_zero
  simp only [tI, h2, map_zero]

def eI (I : MaximalSpectrum R) : R := (IsArtinianRing.equivPi R).symm (Pi.single I 1)

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem equivPi_apply' (r : R) (J : MaximalSpectrum R) :
    IsArtinianRing.equivPi R r J = Ideal.Quotient.mk J.asIdeal r := rfl

/- English proof (translation)
Rewrite using `[← Ideal.Quotient.eq_zero_iff_mem, ← equivPi_apply', eI, AlgEquiv.apply_symm_apply, Pi.single_eq_of_ne h]`.
-/
theorem eI_mem {I J : MaximalSpectrum R} (h : J ≠ I) : eI I ∈ J.asIdeal := by
  rw [← Ideal.Quotient.eq_zero_iff_mem, ← equivPi_apply', eI, AlgEquiv.apply_symm_apply, Pi.single_eq_of_ne h]

/- English proof (translation)
Rewrite using `[← Ideal.Quotient.eq_zero_iff_mem, map_sub, ← equivPi_apply', eI, AlgEquiv.apply_symm_apply, Pi.single_eq_same, map_one, sub_self]`.
-/
theorem eI_sub_one (I : MaximalSpectrum R) : eI I - 1 ∈ I.asIdeal := by
  rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, ← equivPi_apply', eI, AlgEquiv.apply_symm_apply, Pi.single_eq_same,
    map_one, sub_self]

/- English proof (translation)
Apply `(IsArtinianRing.equivPi R).injective` to reduce the goal to its premises. Rewrite using `[map_mul, map_zero, eI, AlgEquiv.apply_symm_apply]`. Use function extensionality and compare the values at `J`. Distinguish the cases in `h : J = I`. Substitute `h` using the available equality.

Simplify using `[equivPi_apply', Ideal.Quotient.eq_zero_iff_mem.2 hr]`. Simplify using `[Pi.single_eq_of_ne h]`.
-/
theorem eI_mul (I : MaximalSpectrum R) {r : R} (hr : r ∈ I.asIdeal) : eI I * r = 0 := by
  apply (IsArtinianRing.equivPi R).injective
  rw [map_mul, map_zero, eI, AlgEquiv.apply_symm_apply]
  funext J
  by_cases h : J = I
  · subst h
    simp [equivPi_apply', Ideal.Quotient.eq_zero_iff_mem.2 hr]
  · simp [Pi.single_eq_of_ne h]

/- English proof (translation)
Apply `(IsArtinianRing.equivPi R).injective` to reduce the goal to its premises. Rewrite using `[map_sum, map_one]`. Simplify using `only [eI, AlgEquiv.apply_symm_apply]`. Conclude with `Finset.univ_sum_single 1`.
-/
theorem sum_eI : ∑ I : MaximalSpectrum R, eI I = 1 := by
  apply (IsArtinianRing.equivPi R).injective
  rw [map_sum, map_one]
  simp only [eI, AlgEquiv.apply_symm_apply]
  exact Finset.univ_sum_single 1

/- English proof (translation)
Use `Submodule.smul_induction_on (p := fun w => eI I • w = 0) hw (fun r hr m _ => ?_) (fun a b ha hb => ?_)` and prove the remaining obligations. Rewrite using `[smul_smul, eI_mul I hr, zero_smul]`. Rewrite using `[smul_add, ha, hb, add_zero]`.
-/
theorem eI_smul_eq_zero (I : MaximalSpectrum R) {w : V} (hw : w ∈ I.asIdeal • (⊤ : Submodule R V)) :
    eI I • w = 0 := by
  refine Submodule.smul_induction_on (p := fun w => eI I • w = 0) hw (fun r hr m _ => ?_) (fun a b ha hb => ?_)
  · rw [smul_smul, eI_mul I hr, zero_smul]
  · rw [smul_add, ha, hb, add_zero]

/- English proof (translation)
Use extensionality with `v`. Establish `hv : ∀ I : MaximalSpectrum R, x v ∈ I.asIdeal • (⊤ : Submodule R V)` using `fun I => by`. Rewrite using `[← Submodule.Quotient.mk_eq_zero, ← xq_mk, h I, LinearMap.zero_apply]`. Rewrite using `[LinearMap.zero_apply, ← one_smul R (x v), ← sum_eI, Finset.sum_smul]`. Conclude with `Finset.sum_eq_zero fun I _ => eI_smul_eq_zero I (hv I)`.
-/
theorem eq_zero_of_xq (x : V →ₗ[R] V) (h : ∀ I : MaximalSpectrum R, xq I.asIdeal x = 0) : x = 0 := by
  ext v
  have hv : ∀ I : MaximalSpectrum R, x v ∈ I.asIdeal • (⊤ : Submodule R V) := fun I => by
    rw [← Submodule.Quotient.mk_eq_zero, ← xq_mk, h I, LinearMap.zero_apply]
  rw [LinearMap.zero_apply, ← one_smul R (x v), ← sum_eI, Finset.sum_smul]
  exact Finset.sum_eq_zero fun I _ => eI_smul_eq_zero I (hv I)

def sec (I : MaximalSpectrum R) : (V ⧸ (I.asIdeal • (⊤ : Submodule R V))) →ₗ[R] V :=
  (I.asIdeal • (⊤ : Submodule R V)).liftQ (eI I • LinearMap.id) fun w hw => by
    simp only [LinearMap.mem_ker, LinearMap.smul_apply, LinearMap.id_apply]
    exact eI_smul_eq_zero I hw

/- English proof (translation)
Use `⟨sec I ∘ₗ (g.restrictScalars R) ∘ₗ (I.asIdeal • (⊤ : Submodule R V)).mkQ, ?_, fun J hJ => ?_⟩` and prove the remaining obligations. Use `xq_ext _ fun v => ?_` and prove the remaining obligations. Take `⟨u, hu⟩` from `Submodule.Quotient.mk_surjective _ (g (Submodule.Quotient.mk v))`. Rewrite using `[xq_mk]`. Simplify using `only [LinearMap.comp_apply, Submodule.mkQ_apply, LinearMap.restrictScalars_apply]`.

Rewrite using `[← hu, sec, Submodule.liftQ_apply]`. Simplify using `only [LinearMap.smul_apply, LinearMap.id_apply]`. Rewrite using `[← sub_eq_zero, ← Submodule.Quotient.mk_sub, Submodule.Quotient.mk_eq_zero]`. Establish `e : eI I • u - u = (eI I - 1) • u` using `by rw [sub_smul, one_smul]`. Rewrite using `[e]`.

Conclude with `Submodule.smul_mem_smul (eI_sub_one I) (Submodule.mem_top : u ∈ (⊤ : Submodule R V))`. Use `xq_ext _ fun v => ?_` and prove the remaining obligations. Take `⟨u, hu⟩` from `Submodule.Quotient.mk_surjective _ (g (Submodule.Quotient.mk v))`. Rewrite using `[xq_mk]`. Simplify using `only [LinearMap.comp_apply, Submodule.mkQ_apply, LinearMap.restrictScalars_apply]`.

Rewrite using `[← hu, sec, Submodule.liftQ_apply]`. Simplify using `only [LinearMap.smul_apply, LinearMap.id_apply, LinearMap.zero_apply]`. Rewrite using `[Submodule.Quotient.mk_eq_zero]`. Conclude with `Submodule.smul_mem_smul (eI_mem hJ) (Submodule.mem_top : u ∈ (⊤ : Submodule R V))`.
-/
theorem exists_lift (I : MaximalSpectrum R)
    (g : (V ⧸ (I.asIdeal • (⊤ : Submodule R V))) →ₗ[R ⧸ I.asIdeal] (V ⧸ (I.asIdeal • (⊤ : Submodule R V)))) :
    ∃ y : V →ₗ[R] V, xq I.asIdeal y = g ∧ ∀ J ≠ I, xq J.asIdeal y = 0 := by
  refine ⟨sec I ∘ₗ (g.restrictScalars R) ∘ₗ (I.asIdeal • (⊤ : Submodule R V)).mkQ, ?_, fun J hJ => ?_⟩
  · refine xq_ext _ fun v => ?_
    obtain ⟨u, hu⟩ := Submodule.Quotient.mk_surjective _ (g (Submodule.Quotient.mk v))
    rw [xq_mk]
    simp only [LinearMap.comp_apply, Submodule.mkQ_apply, LinearMap.restrictScalars_apply]
    rw [← hu, sec, Submodule.liftQ_apply]
    simp only [LinearMap.smul_apply, LinearMap.id_apply]
    rw [← sub_eq_zero, ← Submodule.Quotient.mk_sub, Submodule.Quotient.mk_eq_zero]
    have e : eI I • u - u = (eI I - 1) • u := by rw [sub_smul, one_smul]
    rw [e]
    exact Submodule.smul_mem_smul (eI_sub_one I) (Submodule.mem_top : u ∈ (⊤ : Submodule R V))
  · refine xq_ext _ fun v => ?_
    obtain ⟨u, hu⟩ := Submodule.Quotient.mk_surjective _ (g (Submodule.Quotient.mk v))
    rw [xq_mk]
    simp only [LinearMap.comp_apply, Submodule.mkQ_apply, LinearMap.restrictScalars_apply]
    rw [← hu, sec, Submodule.liftQ_apply]
    simp only [LinearMap.smul_apply, LinearMap.id_apply, LinearMap.zero_apply]
    rw [Submodule.Quotient.mk_eq_zero]
    exact Submodule.smul_mem_smul (eI_mem hJ) (Submodule.mem_top : u ∈ (⊤ : Submodule R V))

/- English proof (translation)
Assume the negation of the conclusion as `hx`. Choose the witnesses or unpack the hypotheses as in `⟨I, hI⟩ : ∃ I : MaximalSpectrum R, xq I.asIdeal x ≠ 0 := by`. Assume the negation of the conclusion as `hne`. Use `push_neg at hne`. Conclude with `hx (eq_zero_of_xq x hne)`.

Use `haveI := finQ k (V := V) I`. Choose the witnesses or unpack the hypotheses as in `⟨w, hw⟩ : ∃ w, xq I.asIdeal x w ≠ 0 := by`. Assume the negation of the conclusion as `hne`. Use `push_neg at hne`. Conclude with `hI (LinearMap.ext hne)`.

Choose the witnesses or unpack the hypotheses as in `⟨φ, hφ⟩ : ∃ φ : Module.Dual (R ⧸ I.asIdeal) _, φ (xq I.asIdeal x w) ≠ 0 := by`. Assume the negation of the conclusion as `hne`. Use `push_neg at hne`. Conclude with `hw ((Module.forall_dual_apply_eq_zero_iff _ _).1 hne)`. Take `⟨y, hy1, hy2⟩` from `exists_lift I ((φ (xq I.asIdeal x w))⁻¹ • φ.smulRight w)`.

Use `h y` as an intermediate fact. Rewrite `this` using `[tau_apply, Finset.sum_eq_single I]`. Apply `lam_one (k := k) I` to reduce the goal to its premises. Simplify using `only [tI, xq_mul, hy1] at this`. Rewrite `this` using `[mul_smul_comm, map_smul, trace_comp_smulRight, smul_eq_mul, inv_mul_cancel₀ hφ]`. Then use the resulting hypothesis.

Introduce `J _ hJ`. Simplify using `only [tI, xq_mul, hy2 J hJ, mul_zero, map_zero]`. Introduce `hn`. Conclude with `absurd (Finset.mem_univ I) hn`.
-/
theorem tau_nondeg (x : V →ₗ[R] V) (h : ∀ y : V →ₗ[R] V, tau (k := k) (x * y) = 0) : x = 0 := by
  by_contra hx
  obtain ⟨I, hI⟩ : ∃ I : MaximalSpectrum R, xq I.asIdeal x ≠ 0 := by
    by_contra hne
    push_neg at hne
    exact hx (eq_zero_of_xq x hne)
  haveI := finQ k (V := V) I
  obtain ⟨w, hw⟩ : ∃ w, xq I.asIdeal x w ≠ 0 := by
    by_contra hne
    push_neg at hne
    exact hI (LinearMap.ext hne)
  obtain ⟨φ, hφ⟩ : ∃ φ : Module.Dual (R ⧸ I.asIdeal) _, φ (xq I.asIdeal x w) ≠ 0 := by
    by_contra hne
    push_neg at hne
    exact hw ((Module.forall_dual_apply_eq_zero_iff _ _).1 hne)
  obtain ⟨y, hy1, hy2⟩ := exists_lift I ((φ (xq I.asIdeal x w))⁻¹ • φ.smulRight w)
  have := h y
  rw [tau_apply, Finset.sum_eq_single I] at this
  · apply lam_one (k := k) I
    simp only [tI, xq_mul, hy1] at this
    rwa [mul_smul_comm, map_smul, trace_comp_smulRight, smul_eq_mul, inv_mul_cancel₀ hφ] at this
  · intro J _ hJ
    simp only [tI, xq_mul, hy2 J hJ, mul_zero, map_zero]
  · intro hn
    exact absurd (Finset.mem_univ I) hn

/- English proof (translation)
Assemble the required witnesses or components as `⟨tau, tau_comm, tau_nondeg, tau_nil⟩`.
-/
theorem exists_tau : ∃ τ : (V →ₗ[R] V) →ₗ[k] k, (∀ x y, τ (x * y) = τ (y * x)) ∧
    (∀ x, (∀ y, τ (x * y) = 0) → x = 0) ∧ ∀ x, IsNilpotent x → τ x = 0 :=
  ⟨tau, tau_comm, tau_nondeg, tau_nil⟩

end PositivityTheory.RgUd.TP.Loc.Ptf

import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LiftQMk
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ConstOneMem

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000

noncomputable section

open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pass GlobalTheory.Cut GlobalTheory.UseLoc Module TensorProduct GlobalTheory.UseLoc.Cases

namespace GlobalTheory.UseLoc.Cases.LiftW

section Gen

variable {O : Type} (LL : Type) [CommRing O] [Field LL] [Algebra O LL]

def basisVec (k : ℕ) (j : Fin k) : ↥(stdG O LL k) :=
  ⟨Pi.single j 1, ⟨Pi.single j 1, by
    funext j'
    simp [Pi.single_apply]⟩⟩

def coordQ (k : ℕ) (j : Fin k) : ((Fin k → LL) ⧸ stdG O LL k) →ₗ[O] (LL ⧸ intO (O := O) LL) :=
  (stdG O LL k).mapQ (intO LL) (LinearMap.proj j) (by
    rintro _ ⟨u, rfl⟩
    exact ⟨u j, rfl⟩)

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem coordQ_mk (k : ℕ) (j : Fin k) (v : Fin k → LL) :
    coordQ (O := O) LL k j (Submodule.Quotient.mk v) = Submodule.Quotient.mk (v j) := rfl

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem iotaW_tmul (lam : O) (a k : ℕ) (t : ↥(stdG O LL k)) (s : LL)
    (hs : (Submodule.Quotient.mk s : LL ⧸ intO (O := O) LL) ∈ Xq LL lam a) :
    iotaW LL lam a k (t ⊗ₜ ⟨Submodule.Quotient.mk s, hs⟩) = Submodule.Quotient.mk (s • (t : Fin k → LL)) := rfl

/- English proof (translation)
Proceed by induction on `u using TensorProduct.induction_on with`. Consider the case `zero => exact ⟨0, by simp⟩`. Consider the case `tmul t y`. Take `⟨_, c, rfl⟩` from `t`. Use `⟨fun j => c j • y, ?_⟩` and prove the remaining obligations.

Simplify using `only [← TensorProduct.smul_tmul, ← TensorProduct.sum_tmul]`. Use `congr 1`. Apply `Subtype.ext` to reduce the goal to its premises. Use function extensionality and compare the values at `j'`. Simplify using `[basisVec, Finset.sum_apply, Pi.single_apply, Algebra.smul_def]`.

Consider the case `add u v hu hv`. Take `⟨x, rfl⟩` from `hu`. Take `⟨y, rfl⟩` from `hv`. Conclude with `⟨x + y, by simp [TensorProduct.tmul_add, Finset.sum_add_distrib]⟩`.
-/
theorem exists_sum (k : ℕ) {X : Type} [AddCommGroup X] [Module O X] (u : ↥(stdG O LL k) ⊗[O] X) :
    ∃ x : Fin k → X, u = ∑ j, basisVec LL k j ⊗ₜ[O] x j := by
  induction u using TensorProduct.induction_on with
  | zero => exact ⟨0, by simp⟩
  | tmul t y =>
    obtain ⟨_, c, rfl⟩ := t
    refine ⟨fun j => c j • y, ?_⟩
    simp only [← TensorProduct.smul_tmul, ← TensorProduct.sum_tmul]
    congr 1
    apply Subtype.ext
    funext j'
    simp [basisVec, Finset.sum_apply, Pi.single_apply, Algebra.smul_def]
  | add u v hu hv =>
    obtain ⟨x, rfl⟩ := hu
    obtain ⟨y, rfl⟩ := hv
    exact ⟨x + y, by simp [TensorProduct.tmul_add, Finset.sum_add_distrib]⟩

/- English proof (translation)
Establish `h : ∀ j', coordQ LL k j (iotaW LL lam a k (basisVec LL k j' ⊗ₜ[O] x j')) = if j = j' then (x j' : LL ⧸ intO (O` using `O) LL) else 0 := by`. Introduce `j'`. Take `⟨y, hy⟩` from `x j'`. Take `⟨s, rfl⟩` from `Submodule.Quotient.mk_surjective _ y`. Rewrite using `[iotaW_tmul, coordQ_mk]`.

Apply the tactic sequence `by_cases hj : j = j' <;> simp [basisVec, hj]`. Simplify using `[map_sum, h]`.
-/
theorem coordQ_iotaW (lam : O) (a k : ℕ) (x : Fin k → ↥(Xq LL lam a)) (j : Fin k) :
    coordQ LL k j (iotaW LL lam a k (∑ j', basisVec LL k j' ⊗ₜ[O] x j')) = x j := by
  have h : ∀ j', coordQ LL k j (iotaW LL lam a k (basisVec LL k j' ⊗ₜ[O] x j')) =
      if j = j' then (x j' : LL ⧸ intO (O := O) LL) else 0 := by
    intro j'
    obtain ⟨y, hy⟩ := x j'
    obtain ⟨s, rfl⟩ := Submodule.Quotient.mk_surjective _ y
    rw [iotaW_tmul, coordQ_mk]
    by_cases hj : j = j' <;> simp [basisVec, hj]
  simp [map_sum, h]

/- English proof (translation)
Rewrite using `[injective_iff_map_eq_zero]`. Introduce `u hu`. Take `⟨x, rfl⟩` from `exists_sum LL k u`. Establish `: x = 0`. Use function extensionality and compare the values at `j`.

Apply `Subtype.ext` to reduce the goal to its premises. Rewrite using `[← coordQ_iotaW, hu]`. Simplify using the standard rewrite rules. Simplify using `[this]`.
-/
theorem iotaW_injective (lam : O) (a k : ℕ) : Function.Injective (iotaW LL lam a k) := by
  rw [injective_iff_map_eq_zero]
  intro u hu
  obtain ⟨x, rfl⟩ := exists_sum LL k u
  have : x = 0 := by
    funext j
    apply Subtype.ext
    rw [← coordQ_iotaW, hu]
    simp
  simp [this]

/- English proof (translation)
Take `⟨v, rfl⟩` from `Submodule.Quotient.mk_surjective _ q`. Establish `hx : ∀ j, (Submodule.Quotient.mk (v j) : LL ⧸ intO (O` using `O) LL) ∈ Xq LL lam a := by`. Introduce `j`. Use `congrArg (coordQ LL k j) hq` as an intermediate fact. Rewrite `this` using `[map_smul, map_zero, coordQ_mk]`.

Conclude with `this`. Use `⟨∑ j, basisVec LL k j ⊗ₜ[O] ⟨_, hx j⟩, ?_⟩` and prove the remaining obligations. Simplify using `only [map_sum, iotaW_tmul]`. Establish `: v = ∑ j, v j • (basisVec (O` using `O) LL k j : Fin k → LL) := by`. Use function extensionality and compare the values at `j'`.

Simplify using `[basisVec, Finset.sum_apply, Pi.single_apply]`. Use `conv_rhs => rw [this]`. Conclude with `(map_sum (stdG O LL k).mkQ _ _).symm`.
-/
theorem exists_iotaW (lam : O) (a k : ℕ) (q : (Fin k → LL) ⧸ stdG O LL k) (hq : lam ^ a • q = 0) :
    ∃ u, iotaW LL lam a k u = q := by
  obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective _ q
  have hx : ∀ j, (Submodule.Quotient.mk (v j) : LL ⧸ intO (O := O) LL) ∈ Xq LL lam a := by
    intro j
    have := congrArg (coordQ LL k j) hq
    rw [map_smul, map_zero, coordQ_mk] at this
    exact this
  refine ⟨∑ j, basisVec LL k j ⊗ₜ[O] ⟨_, hx j⟩, ?_⟩
  simp only [map_sum, iotaW_tmul]
  have : v = ∑ j, v j • (basisVec (O := O) LL k j : Fin k → LL) := by
    funext j'
    simp [basisVec, Finset.sum_apply, Pi.single_apply]
  conv_rhs => rw [this]
  exact (map_sum (stdG O LL k).mkQ _ _).symm

variable {LL}

/- English proof (translation)
Proceed by induction on `u using TensorProduct.induction_on with`. Consider the case `zero => exact (congrArg _ (map_zero _)).trans ((map_zero _).trans ((congrArg _ (map_zero _)).trans (map_zero _)).symm)`. Consider the case `add u v hu hv`. Establish `e1` using `map_add (tableLineDegreeTwo.actTw (stdLatG hinj (twistM N θ)) ↥(Xq LL lam a) θ g) u v`. Establish `e2` using `map_add (actD (stdLatG hinj N) g) (iotaW LL lam a k u) (iotaW LL lam a k v)`.

Use `(congrArg _ e1).trans ((map_add _ _ _).trans ?_)` and prove the remaining obligations. Rewrite using `[map_add]`. Conclude with `(congrArg₂ (· + ·) hu hv).trans e2.symm`. Consider the case `tmul t y`. Take `⟨y, hy⟩` from `y`.

Take `⟨s, rfl⟩` from `Submodule.Quotient.mk_surjective _ y`. Use `(map_smul (iotaW LL lam a k) (((θ g)⁻¹ : Oˣ) : O) ((show ↥(stdG O LL k) from actT (stdLatG hinj (twistM N θ)) g t) ⊗ₜ[O] ⟨Submodule.Quotient.mk s, hy⟩)).trans ?_` and prove the remaining obligations. Rewrite using `[iotaW_tmul, iotaW_tmul, ← Submodule.Quotient.mk_smul]`. Use `congrArg Submodule.Quotient.mk ?_` and prove the remaining obligations. Use `show (((θ g)⁻¹ : Oˣ) : O) • s • (((((θ g : Oˣ) : O) • N g).map (algebraMap O LL)).mulVec (t : Fin k → LL)) = ((N g).map (algebraMap O LL)).mulVec (s • (t : Fin k → LL))`.

Establish `e : (((θ g : Oˣ) : O) • N g).map (algebraMap O LL) = ((θ g : Oˣ) : O) • (N g).map (algebraMap O LL)`. Use extensionality with `p q`. Simplify using `only [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, map_mul]`. Rewrite using `[Algebra.smul_def]`. Rewrite using `[e, Matrix.smul_mulVec, Matrix.mulVec_smul, smul_comm s, smul_smul, Units.inv_mul, one_smul]`.
-/
theorem iotaW_actTw (hinj : Function.Injective (algebraMap O LL)) {G : Type} [Group G]
    (lam : O) (a : ℕ) {k : ℕ} (N : G →* Matrix (Fin k) (Fin k) O) (θ : G →* Oˣ) (g : G)
    (u : ↥(stdG O LL k) ⊗[O] ↥(Xq LL lam a)) :
    iotaW LL lam a k (tableLineDegreeTwo.actTw (stdLatG hinj (twistM N θ)) ↥(Xq LL lam a) θ g u) =
      actD (stdLatG hinj N) g (iotaW LL lam a k u) := by
  induction u using TensorProduct.induction_on with
  | zero => exact (congrArg _ (map_zero _)).trans ((map_zero _).trans
      ((congrArg _ (map_zero _)).trans (map_zero _)).symm)
  | add u v hu hv =>
    have e1 := map_add (tableLineDegreeTwo.actTw (stdLatG hinj (twistM N θ)) ↥(Xq LL lam a) θ g) u v
    have e2 := map_add (actD (stdLatG hinj N) g) (iotaW LL lam a k u) (iotaW LL lam a k v)
    refine (congrArg _ e1).trans ((map_add _ _ _).trans ?_)
    rw [map_add]
    exact (congrArg₂ (· + ·) hu hv).trans e2.symm
  | tmul t y =>
    obtain ⟨y, hy⟩ := y
    obtain ⟨s, rfl⟩ := Submodule.Quotient.mk_surjective _ y
    refine (map_smul (iotaW LL lam a k) (((θ g)⁻¹ : Oˣ) : O)
      ((show ↥(stdG O LL k) from actT (stdLatG hinj (twistM N θ)) g t) ⊗ₜ[O] ⟨Submodule.Quotient.mk s, hy⟩)).trans ?_
    rw [iotaW_tmul, iotaW_tmul, ← Submodule.Quotient.mk_smul]
    refine congrArg Submodule.Quotient.mk ?_
    show (((θ g)⁻¹ : Oˣ) : O) • s • (((((θ g : Oˣ) : O) • N g).map (algebraMap O LL)).mulVec (t : Fin k → LL)) =
      ((N g).map (algebraMap O LL)).mulVec (s • (t : Fin k → LL))
    have e : (((θ g : Oˣ) : O) • N g).map (algebraMap O LL) = ((θ g : Oˣ) : O) • (N g).map (algebraMap O LL) := by
      ext p q
      simp only [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, map_mul]
      rw [Algebra.smul_def]
    rw [e, Matrix.smul_mulVec, Matrix.mulVec_smul, smul_comm s, smul_smul, Units.inv_mul, one_smul]

/- English proof (translation)
Use `choose z hz using fun g => exists_iotaW LL lam a k (f g) (hk g)`. Use `⟨z, ⟨?_, fun g h => ?_⟩, hz⟩` and prove the remaining obligations. Use `IsLocallyConstant.desc z (iotaW LL lam a k) ?_ (iotaW_injective LL lam a k)` and prove the remaining obligations. Establish `: (iotaW LL lam a k) ∘ z = f` using `funext hz`. Rewrite using `[this]`.

Conclude with `hf.1`. Apply `iotaW_injective LL lam a k` to reduce the goal to its premises. Use `(hz _).trans ((hf.2 g h).trans ?_)` and prove the remaining obligations. Use `Eq.trans ?_ (map_add (iotaW LL lam a k) (z g) _).symm` and prove the remaining obligations. Rewrite using `[hz g, ← hz h]`.

Conclude with `congrArg _ (iotaW_actTw hinj lam a N θ g (z h)).symm`.
-/
theorem exists_twistedCocycle_lift_torsion (hinj : Function.Injective (algebraMap O LL)) {G : Type} [Group G] [TopologicalSpace G]
    (lam : O) (a : ℕ) {k : ℕ} (N : G →* Matrix (Fin k) (Fin k) O) (θ : G →* Oˣ)
    (f : G → (Fin k → LL) ⧸ stdG O LL k) (hf : f ∈ divisibleCocycles (stdLatG hinj N)) (hk : ∀ g, lam ^ a • f g = 0) :
    ∃ z' : G → ↥(stdLatG hinj (twistM N θ)).T ⊗[O] ↥(Xq LL lam a),
      tableLineDegreeTwo.IsCoc (stdLatG hinj (twistM N θ)) ↥(Xq LL lam a) θ z' ∧ ∀ g, iotaW LL lam a k (z' g) = f g := by
  choose z hz using fun g => exists_iotaW LL lam a k (f g) (hk g)
  refine ⟨z, ⟨?_, fun g h => ?_⟩, hz⟩
  · refine IsLocallyConstant.desc z (iotaW LL lam a k) ?_ (iotaW_injective LL lam a k)
    have : (iotaW LL lam a k) ∘ z = f := funext hz
    rw [this]
    exact hf.1
  · apply iotaW_injective LL lam a k
    refine (hz _).trans ((hf.2 g h).trans ?_)
    refine Eq.trans ?_ (map_add (iotaW LL lam a k) (z g) _).symm
    rw [hz g, ← hz h]
    exact congrArg _ (iotaW_actTw hinj lam a N θ g (z h)).symm

/- English proof (translation)
Substitute `hχ` using the available equality. Conclude with `exists_twistedCocycle_lift_torsion hinj lam a N χ f hf hk`.
-/
theorem lift_gen (hinj : Function.Injective (algebraMap O LL)) {G : Type} [Group G] [TopologicalSpace G]
    (lam : O) (a : ℕ) {k : ℕ} (N : G →* Matrix (Fin k) (Fin k) O) (θ χ : G →* Oˣ) (hχ : χ = θ)
    (f : G → (Fin k → LL) ⧸ stdG O LL k) (hf : f ∈ divisibleCocycles (stdLatG hinj N)) (hk : ∀ g, lam ^ a • f g = 0) :
    ∃ z' : G → ↥(stdLatG hinj (twistM N θ)).T ⊗[O] ↥(Xq LL lam a),
      tableLineDegreeTwo.IsCoc (stdLatG hinj (twistM N θ)) ↥(Xq LL lam a) χ z' ∧ ∀ g, iotaW LL lam a k (z' g) = f g := by
  subst hχ
  exact exists_twistedCocycle_lift_torsion hinj lam a N χ f hf hk

end Gen

/- English proof (translation)
Use extensionality with `g`. Simplify using `[chiT, chiOC]`.
-/
theorem chiT_one {D : D7} {i : D.nd.Loc} {w : HeightOneSpectrum (𝓞 D.host.E)}
    {hw : w ∈ placesOver D.host.E (D.nd.l i)} (C : TruncatedSeriesCountingIdentities.CoefExt D i w hw)
    (θ : Br.G D.nbr i w hw →* (↥(OL C.LL))ˣ) : chiT C θ 1 = θ := by
  ext g
  simp [chiT, chiOC]

/- English proof (translation)
Introduce `D i w hw C lam _ k N θ a f hf hk`. Conclude with `lift_gen Subtype.val_injective lam a N θ (chiT C θ 1) (chiT_one C θ) f hf hk`.
-/
theorem lift_cocycle : ∀ (D : D7) (i : D.nd.Loc) (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i))
    (C : TruncatedSeriesCountingIdentities.CoefExt D i w hw) (lam : ↥(OL C.LL)), Irreducible lam →
    ∀ {k : ℕ} (N : Br.G D.nbr i w hw →* Matrix (Fin k) (Fin k) ↥(OL C.LL)) (θ : Br.G D.nbr i w hw →* (↥(OL C.LL))ˣ) (a : ℕ)
      (f : Br.G D.nbr i w hw → (Fin k → ↥C.LL.1) ⧸ stdG ↥(OL C.LL) ↥C.LL.1 k),
    f ∈ divisibleCocycles (latC C N) → (∀ g, lam ^ a • f g = 0) →
    ∃ z' : Br.G D.nbr i w hw → ↥(latC C (twistM N θ)).T ⊗[↥(OL C.LL)] ↥(Xq ↥C.LL.1 lam a),
      tableLineDegreeTwo.IsCoc (latC C (twistM N θ)) ↥(Xq ↥C.LL.1 lam a) (chiT C θ 1) z' ∧ ∀ g, iotaW ↥C.LL.1 lam a k (z' g) = f g := by
  intro D i w hw C lam _ k N θ a f hf hk
  exact lift_gen Subtype.val_injective lam a N θ (chiT C θ 1) (chiT_one C θ) f hf hk

end GlobalTheory.UseLoc.Cases.LiftW

end

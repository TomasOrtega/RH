import Mathlib
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.ExistsFormOfEqRatioPowMul
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.VanIdealHomog
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MemVanishingIdealIffKillsForm
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ChartVanishingKillsFormMulPow
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ClosedImmersionPullbackKernelSup
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ThickeningSectionHomogeneousForm

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Out MvPolynomial GlobalTheory.CompanionTheory.GE
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (PSpace)
open GlobalTheory.ProjSpace

namespace GlobalTheory.CompanionTheory.GE.Family

variable {R : Type} [CommRing R] {N : ℕ}

instance isClosedImmersion_thickι (I : Ideal R) (e : ℕ) : IsClosedImmersion (thickι R I N e) := by
  have : IsClosedImmersion (thick R I e) :=
    IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective
  unfold thickι
  infer_instance

/- English proof (translation)
Conclude with `(pullback.lift_fst _ _ _).trans (Category.comp_id _)`.
-/
theorem thickMap_comp_thickι (I : Ideal R) (e : ℕ) :
    thickMap R I e (PO R N) ≫ thickι R I N (e + 1) = thickι R I N e := by
  exact (pullback.lift_fst _ _ _).trans (Category.comp_id _)

instance isClosedImmersion_thickMap (I : Ideal R) (e : ℕ) :
    IsClosedImmersion (thickMap R I e (PO R N)) := by
  have : IsClosedImmersion (thickMap R I e (PO R N) ≫ thickι R I N (e + 1)) := by
    rw [thickMap_comp_thickι]; infer_instance
  exact IsClosedImmersion.of_comp_isClosedImmersion _ (thickι R I N (e + 1))

/- English proof (translation)
Simplify using `only [formOn_eq_aeval, map_mul, map_pow, aeval_X, ratioOn_self, one_pow, one_mul]`.
-/
theorem formOn_X_pow_mul (k : Fin (N + 1)) {m n : ℕ} {f : MvPolynomial (Fin (N + 1)) R}
    (hf : f.IsHomogeneous n) (h : (X k ^ m * f : MvPolynomial (Fin (N + 1)) R).IsHomogeneous (m + n)) :
    formOn (chart R N k) k le_rfl (m + n) (X k ^ m * f) h = formOn (chart R N k) k le_rfl n f hf := by
  simp only [formOn_eq_aeval, map_mul, map_pow, aeval_X, ratioOn_self, one_pow, one_mul]

/- English proof (translation)
Introduce `k`. Take `⟨m, hm⟩` from `h k`. Establish `hh : (X k ^ m * f : MvPolynomial (Fin (N + 1)) R).IsHomogeneous (m + n)` using `(isHomogeneous_X_pow k m).mul hf`. Use `(GlobalTheory.CompanionTheory.GE.mem_vanIdeal_iff_killsForm φ (m + n) _ hh).1 hm k` as an intermediate fact. Rewrite `this` using `[formOn_X_pow_mul k hf hh]`. Then use the resulting hypothesis.
-/
theorem killsForm_of_X_pow_mul {Y : Scheme.{0}} (φ : Y ⟶ PSpace R N) {n : ℕ}
    {f : MvPolynomial (Fin (N + 1)) R} (hf : f.IsHomogeneous n)
    (h : ∀ k, ∃ m : ℕ, X k ^ m * f ∈ vanIdeal φ) : KillsForm φ n f hf := by
  intro k
  obtain ⟨m, hm⟩ := h k
  have hh : (X k ^ m * f : MvPolynomial (Fin (N + 1)) R).IsHomogeneous (m + n) :=
    (isHomogeneous_X_pow k m).mul hf
  have := (GlobalTheory.CompanionTheory.GE.mem_vanIdeal_iff_killsForm φ (m + n) _ hh).1 hm k
  rwa [formOn_X_pow_mul k hf hh] at this

attribute [local instance] MvPolynomial.gradedAlgebra in

/- English proof (translation)
Use `DirectSum.coe_decompose_mul_add_of_left_mem (homogeneousSubmodule (Fin (N + 1)) R) (a := X k ^ m) (b := f) (i := m) (j := d) (isHomogeneous_X_pow k m)` as an intermediate fact. Establish `h2 : ∀ (g : MvPolynomial (Fin (N + 1)) R) (d : ℕ), ((DirectSum.decompose (homogeneousSubmodule (Fin (N + 1)) R) g) d : MvPolynomial (Fin (N + 1)) R) = homogeneousComponent d g` using `fun g d => decomposition.decompose'_apply g d`. Rewrite `this` using `[h2, h2]`. Then use the resulting hypothesis.
-/
theorem homogeneousComponent_X_pow_mul (k : Fin (N + 1)) (m d : ℕ)
    (f : MvPolynomial (Fin (N + 1)) R) :
    homogeneousComponent (m + d) (X k ^ m * f) = X k ^ m * homogeneousComponent d f := by
  have := DirectSum.coe_decompose_mul_add_of_left_mem (homogeneousSubmodule (Fin (N + 1)) R)
    (a := X k ^ m) (b := f) (i := m) (j := d) (isHomogeneous_X_pow k m)
  have h2 : ∀ (g : MvPolynomial (Fin (N + 1)) R) (d : ℕ),
      ((DirectSum.decompose (homogeneousSubmodule (Fin (N + 1)) R) g) d :
        MvPolynomial (Fin (N + 1)) R) = homogeneousComponent d g :=
    fun g d => decomposition.decompose'_apply g d
  rwa [h2, h2] at this

/- English proof (translation)
Rewrite using `[← sum_homogeneousComponent f]`. Use `Ideal.sum_mem _ fun d _ => ?_` and prove the remaining obligations. Use `(GlobalTheory.CompanionTheory.GE.mem_vanIdeal_iff_killsForm φ d _ (homogeneousComponent_isHomogeneous d f)).2 (killsForm_of_X_pow_mul φ _ fun k => ?_)` and prove the remaining obligations. Take `⟨m, hm⟩` from `h k`. Conclude with `⟨m, homogeneousComponent_X_pow_mul k m d f ▸ vanIdeal_homog φ (m + d) _ hm⟩`.
-/
theorem mem_vanIdeal_of_X_pow_mul {Y : Scheme.{0}} (φ : Y ⟶ PSpace R N)
    (f : MvPolynomial (Fin (N + 1)) R) (h : ∀ k, ∃ m : ℕ, X k ^ m * f ∈ vanIdeal φ) :
    f ∈ vanIdeal φ := by
  rw [← sum_homogeneousComponent f]
  refine Ideal.sum_mem _ fun d _ => ?_
  refine (GlobalTheory.CompanionTheory.GE.mem_vanIdeal_iff_killsForm φ d _ (homogeneousComponent_isHomogeneous d f)).2
    (killsForm_of_X_pow_mul φ _ fun k => ?_)
  obtain ⟨m, hm⟩ := h k
  exact ⟨m, homogeneousComponent_X_pow_mul k m d f ▸ vanIdeal_homog φ (m + d) _ hm⟩

/- English proof (translation)
Introduce `k`. Use `h k` as an intermediate fact. Rewrite using `[Scheme.Hom.comp_app]`. Express the relevant statement in the definitionally equal form `(g.app _).hom ((φ.app _).hom _) = 0`. Rewrite using `[this, map_zero]`.
-/
theorem killsForm_comp {Y Z : Scheme.{0}} (g : Z ⟶ Y) (φ : Y ⟶ PSpace R N) {n : ℕ}
    {f : MvPolynomial (Fin (N + 1)) R} {hf : f.IsHomogeneous n} (h : KillsForm φ n f hf) :
    KillsForm (g ≫ φ) n f hf := by
  intro k
  have := h k
  rw [Scheme.Hom.comp_app]
  change (g.app _).hom ((φ.app _).hom _) = 0
  rw [this, map_zero]

/- English proof (translation)
The claim follows from `Ideal.span_mono fun _ ⟨n, hf, h⟩ => ⟨n, hf, killsForm_comp g φ h⟩`.
-/
theorem vanIdeal_le_comp {Y Z : Scheme.{0}} (g : Z ⟶ Y) (φ : Y ⟶ PSpace R N) :
    vanIdeal φ ≤ vanIdeal (g ≫ φ) :=
  Ideal.span_mono fun _ ⟨n, hf, h⟩ => ⟨n, hf, killsForm_comp g φ h⟩

/- English proof (translation)
Rewrite using `[Ideal.map_le_iff_le_comap]`. Introduce `r hr`. Use `(GlobalTheory.CompanionTheory.GE.mem_vanIdeal_iff_killsForm _ 0 (C r) (isHomogeneous_C _ r)).2 (killsForm_comp a _ fun k => ?_)` and prove the remaining obligations. Establish `h` using `(GlobalTheory.CompanionTheory.GE.ker_thickι_chart I N e k).2 0 (C r) (isHomogeneous_C _ r) (Ideal.mem_map_of_mem _ hr)`. Rewrite `h` using `[Scheme.Hom.ker_apply]`.

Conclude with `h`.
-/
theorem map_pow_le_vanIdeal {Y : Scheme.{0}} (I : Ideal R) (e : ℕ)
    (a : Y ⟶ (thickObj R I e (PO R N)).left) :
    (I ^ (e + 1)).map (C : R →+* MvPolynomial (Fin (N + 1)) R) ≤ vanIdeal (a ≫ thickι R I N e) := by
  rw [Ideal.map_le_iff_le_comap]
  intro r hr
  refine (GlobalTheory.CompanionTheory.GE.mem_vanIdeal_iff_killsForm _ 0 (C r) (isHomogeneous_C _ r)).2 (killsForm_comp a _ fun k => ?_)
  have h := (GlobalTheory.CompanionTheory.GE.ker_thickι_chart I N e k).2 0 (C r) (isHomogeneous_C _ r) (Ideal.mem_map_of_mem _ hr)
  rw [Scheme.Hom.ker_apply] at h
  exact h

/- English proof (translation)
Establish `h1 : formOn (chart R N k) k le_rfl n f hf ∈ (Scheme.Hom.ker ψ).ideal ⟨chart R N k, isAffineOpen_chart R N k⟩`. Rewrite using `[Scheme.Hom.ker_apply]`. Conclude with `hK k`. Rewrite `h1` using `[hker, Scheme.IdealSheafData.ideal_sup]`. Take `⟨s, hs, s', hs', hss⟩` from `Submodule.mem_sup.1 h1`.

Take `⟨c, t, ht, htm, rfl⟩` from `(GlobalTheory.CompanionTheory.GE.ker_thickι_chart I N e k).1 s' hs'`. Take `⟨a, b, hb, rfl⟩` from `GlobalTheory.ProjSpace.Model.exists_formOn k s`. Rewrite `hs` using `[Scheme.Hom.ker_apply]`. Take `⟨m, hm, hkill⟩` from `GlobalTheory.CompanionTheory.GE.exists_killsForm_X_pow_mul φ a b hb k hs`. Establish `hmem : X k ^ m * b ∈ vanIdeal φ` using `(GlobalTheory.CompanionTheory.GE.mem_vanIdeal_iff_killsForm φ _ _ hm).2 hkill`.

Establish `key : X k ^ (a + c) * f = X k ^ (n + c) * b + X k ^ (n + a) * t`. Establish `hL : (X k ^ (a + c) * f : MvPolynomial (Fin (N + 1)) R).IsHomogeneous (a + c + n)` using `(isHomogeneous_X_pow k _).mul hf`. Establish `hR : (X k ^ (n + c) * b + X k ^ (n + a) * t : MvPolynomial (Fin (N + 1)) R).IsHomogeneous (a + c + n)`. Use `IsHomogeneous.add ?_ ?_` and prove the remaining obligations. Use `(isHomogeneous_X_pow (R := R) k (n + c)).mul hb` as an intermediate fact.

Rewrite `this` using `[show n + c + a = a + c + n by ring]`. Then use the resulting hypothesis. Use `(isHomogeneous_X_pow (R := R) k (n + a)).mul ht` as an intermediate fact. Rewrite `this` using `[show n + a + c = a + c + n by ring]`. Then use the resulting hypothesis. Use `(formOn_chart_inj R N k hL hR).1 ?_` and prove the remaining obligations. Simplify using `only [formOn_eq_aeval, map_add, map_mul, map_pow, aeval_X, ratioOn_self, one_pow, one_mul] at hss ⊢`.

Conclude with `hss.symm`. Use `⟨m + a + c, ?_⟩` and prove the remaining obligations. Establish `e1 : X k ^ (m + a + c) * f = X k ^ (n + c) * (X k ^ m * b) + X k ^ (m + n + a) * t`. Establish `: X k ^ (m + a + c) * f = X k ^ m * (X k ^ (a + c) * f)` using `by ring`. Rewrite using `[this, key]`.

Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e1]`. Conclude with `Ideal.add_mem _ (Ideal.mul_mem_left _ _ (Ideal.mem_sup_left hmem)) (Ideal.mul_mem_left _ _ (Ideal.mem_sup_right htm))`.
-/
theorem exists_X_pow_mul_mem {Y Z : Scheme.{0}} (φ : Y ⟶ PSpace R N) [QuasiCompact φ]
    (ψ : Z ⟶ PSpace R N) [QuasiCompact ψ] (I : Ideal R) (e : ℕ)
    (hker : Scheme.Hom.ker ψ = Scheme.Hom.ker φ ⊔ Scheme.Hom.ker (thickι R I N e))
    {n : ℕ} {f : MvPolynomial (Fin (N + 1)) R} {hf : f.IsHomogeneous n}
    (hK : KillsForm ψ n f hf) (k : Fin (N + 1)) :
    ∃ m : ℕ, X k ^ m * f ∈ vanIdeal φ ⊔
      (I ^ (e + 1)).map (C : R →+* MvPolynomial (Fin (N + 1)) R) := by
  have h1 : formOn (chart R N k) k le_rfl n f hf ∈
      (Scheme.Hom.ker ψ).ideal ⟨chart R N k, isAffineOpen_chart R N k⟩ := by
    rw [Scheme.Hom.ker_apply]
    exact hK k
  rw [hker, Scheme.IdealSheafData.ideal_sup] at h1
  obtain ⟨s, hs, s', hs', hss⟩ := Submodule.mem_sup.1 h1
  obtain ⟨c, t, ht, htm, rfl⟩ := (GlobalTheory.CompanionTheory.GE.ker_thickι_chart I N e k).1 s' hs'
  obtain ⟨a, b, hb, rfl⟩ := GlobalTheory.ProjSpace.Model.exists_formOn k s
  rw [Scheme.Hom.ker_apply] at hs
  obtain ⟨m, hm, hkill⟩ := GlobalTheory.CompanionTheory.GE.exists_killsForm_X_pow_mul φ a b hb k hs
  have hmem : X k ^ m * b ∈ vanIdeal φ := (GlobalTheory.CompanionTheory.GE.mem_vanIdeal_iff_killsForm φ _ _ hm).2 hkill
  have key : X k ^ (a + c) * f = X k ^ (n + c) * b + X k ^ (n + a) * t := by
    have hL : (X k ^ (a + c) * f : MvPolynomial (Fin (N + 1)) R).IsHomogeneous (a + c + n) :=
      (isHomogeneous_X_pow k _).mul hf
    have hR : (X k ^ (n + c) * b + X k ^ (n + a) * t :
        MvPolynomial (Fin (N + 1)) R).IsHomogeneous (a + c + n) := by
      refine IsHomogeneous.add ?_ ?_
      · have := (isHomogeneous_X_pow (R := R) k (n + c)).mul hb
        rwa [show n + c + a = a + c + n by ring] at this
      · have := (isHomogeneous_X_pow (R := R) k (n + a)).mul ht
        rwa [show n + a + c = a + c + n by ring] at this
    refine (formOn_chart_inj R N k hL hR).1 ?_
    simp only [formOn_eq_aeval, map_add, map_mul, map_pow, aeval_X, ratioOn_self, one_pow,
      one_mul] at hss ⊢
    exact hss.symm
  refine ⟨m + a + c, ?_⟩
  have e1 : X k ^ (m + a + c) * f =
      X k ^ (n + c) * (X k ^ m * b) + X k ^ (m + n + a) * t := by
    have : X k ^ (m + a + c) * f = X k ^ m * (X k ^ (a + c) * f) := by ring
    rw [this, key]; ring
  rw [e1]
  exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ (Ideal.mem_sup_left hmem))
    (Ideal.mul_mem_left _ _ (Ideal.mem_sup_right htm))

/- English proof (translation)
Introduce `R _ _ I N Cs i β hi hβ`. Establish `hcomp : ∀ e, i e ≫ thickι R I N e = β e ≫ i (e + 1) ≫ thickι R I N (e + 1)` using `fun e => by`. Rewrite using `[← thickMap_comp_thickι I e, ← Category.assoc, ← Category.assoc, (hβ e).w]`. Use `⟨fun e => map_pow_le_vanIdeal I e (i e), fun e f h => mem_vanIdeal_of_X_pow_mul _ f h, fun e => ?_, fun e f hf k => ?_⟩` and prove the remaining obligations. Rewrite using `[hcomp e]`.

Conclude with `vanIdeal_le_comp _ _`. Establish `hker : Scheme.Hom.ker (i e ≫ thickι R I N e) = Scheme.Hom.ker (i (e + 1) ≫ thickι R I N (e + 1)) ⊔ Scheme.Hom.ker (thickι R I N e)`. Use `GlobalTheory.CompanionTheory.GE.ker_inter_eq_sup (thickι R I N (e + 1)) (i (e + 1)) (thickMap R I e (PO R N)) (β e) (i e) (hβ e)` as an intermediate fact. Rewrite `this` using `[thickMap_comp_thickι, Category.assoc, ← hcomp e]`. Then use the resulting hypothesis. Use `Submodule.span_induction (p := fun f _ => ∃ m : ℕ, X k ^ m * f ∈ vanIdeal (i (e + 1) ≫ thickι R I N (e + 1)) ⊔ (I ^ (e + 1)).map (C : R →+* MvPolynomial (Fin (N + 1)) R)) ?_ ?_ ?_ ?_ hf` and prove the remaining obligations.

Introduce and unpack `x ⟨n, hx, hK⟩`. Conclude with `exists_X_pow_mul_mem _ _ I e hker hK k`. Conclude with `⟨0, by simp⟩`. Introduce and unpack `x y _ _ ⟨a, ha⟩ ⟨b, hb⟩`. Use `⟨a + b, ?_⟩` and prove the remaining obligations.

Establish `e1 : X k ^ (a + b) * (x + y) = X k ^ b * (X k ^ a * x) + X k ^ a * (X k ^ b * y)`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e1]`. Conclude with `Ideal.add_mem _ (Ideal.mul_mem_left _ _ ha) (Ideal.mul_mem_left _ _ hb)`. Introduce and unpack `a x _ ⟨m, hm⟩`.

Use `⟨m, ?_⟩` and prove the remaining obligations. Rewrite using `[smul_eq_mul, mul_left_comm]`. Conclude with `Ideal.mul_mem_left _ _ hm`.
-/
theorem vanIdeal_family : ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (I : Ideal R) (N : ℕ)
    (Cs : ℕ → Scheme.{0}) (i : ∀ e, Cs e ⟶ (thickObj R I e (PO R N)).left)
    (β : ∀ e, Cs e ⟶ Cs (e + 1)),
    (∀ e, IsClosedImmersion (i e)) →
    (∀ e, IsPullback (β e) (i e) (i (e + 1)) (thickMap R I e (PO R N))) →
    (∀ e, (I ^ (e + 1)).map (C : R →+* MvPolynomial (Fin (N + 1)) R) ≤
        vanIdeal (i e ≫ thickι R I N e)) ∧
    (∀ e f, (∀ k, ∃ m : ℕ, X k ^ m * f ∈ vanIdeal (i e ≫ thickι R I N e)) →
        f ∈ vanIdeal (i e ≫ thickι R I N e)) ∧
    (∀ e, vanIdeal (i (e + 1) ≫ thickι R I N (e + 1)) ≤ vanIdeal (i e ≫ thickι R I N e)) ∧
    (∀ e, ∀ f ∈ vanIdeal (i e ≫ thickι R I N e), ∀ k, ∃ m : ℕ, X k ^ m * f ∈
        vanIdeal (i (e + 1) ≫ thickι R I N (e + 1)) ⊔
          (I ^ (e + 1)).map (C : R →+* MvPolynomial (Fin (N + 1)) R)) := by
  intro R _ _ I N Cs i β hi hβ
  have hcomp : ∀ e, i e ≫ thickι R I N e =
      β e ≫ i (e + 1) ≫ thickι R I N (e + 1) := fun e => by
    rw [← thickMap_comp_thickι I e, ← Category.assoc, ← Category.assoc, (hβ e).w]
  refine ⟨fun e => map_pow_le_vanIdeal I e (i e), fun e f h => mem_vanIdeal_of_X_pow_mul _ f h,
    fun e => ?_, fun e f hf k => ?_⟩
  · rw [hcomp e]
    exact vanIdeal_le_comp _ _
  · have hker : Scheme.Hom.ker (i e ≫ thickι R I N e) =
        Scheme.Hom.ker (i (e + 1) ≫ thickι R I N (e + 1)) ⊔ Scheme.Hom.ker (thickι R I N e) := by
      have := GlobalTheory.CompanionTheory.GE.ker_inter_eq_sup (thickι R I N (e + 1)) (i (e + 1)) (thickMap R I e (PO R N))
        (β e) (i e) (hβ e)
      rwa [thickMap_comp_thickι, Category.assoc, ← hcomp e] at this
    refine Submodule.span_induction (p := fun f _ => ∃ m : ℕ, X k ^ m * f ∈
        vanIdeal (i (e + 1) ≫ thickι R I N (e + 1)) ⊔
          (I ^ (e + 1)).map (C : R →+* MvPolynomial (Fin (N + 1)) R)) ?_ ?_ ?_ ?_ hf
    · rintro x ⟨n, hx, hK⟩
      exact exists_X_pow_mul_mem _ _ I e hker hK k
    · exact ⟨0, by simp⟩
    · rintro x y _ _ ⟨a, ha⟩ ⟨b, hb⟩
      refine ⟨a + b, ?_⟩
      have e1 : X k ^ (a + b) * (x + y) = X k ^ b * (X k ^ a * x) + X k ^ a * (X k ^ b * y) := by
        ring
      rw [e1]
      exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ ha) (Ideal.mul_mem_left _ _ hb)
    · rintro a x _ ⟨m, hm⟩
      refine ⟨m, ?_⟩
      rw [smul_eq_mul, mul_left_comm]
      exact Ideal.mul_mem_left _ _ hm

end GlobalTheory.CompanionTheory.GE.Family

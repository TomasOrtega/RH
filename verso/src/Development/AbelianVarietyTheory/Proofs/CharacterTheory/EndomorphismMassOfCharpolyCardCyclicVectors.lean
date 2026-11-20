import Mathlib
import Development.AbelianVarietyTheory.Definitions.CommutativeAlgebra.InvariantSubspaceMobiusInverseRecEqOfFinrankLt

open Polynomial GlobalTheory.CuspGL

noncomputable section

namespace GlobalTheory.CuspGL.CyclicMass

variable {F : Type} [Field F]

/- English proof (translation)
Establish `h` using `charpoly_leftMulMatrix (AdjoinRoot.powerBasis' hD)`. Rewrite `h` using `[AdjoinRoot.powerBasis'_gen]`. Establish `h2 : minpoly F (AdjoinRoot.root D) = D`. Rewrite using `[AdjoinRoot.minpoly_root hD.ne_zero, hD.leadingCoeff]`. Simplify using the standard rewrite rules.

Rewrite `h` using `[h2]`. Rewrite using `[← LinearMap.charpoly_toMatrix _ (AdjoinRoot.powerBasis' hD).basis]`. Conclude with `h`.
-/
theorem charpoly_mulLeft_root (D : F[X]) (hD : D.Monic) [FiniteDimensional F (AdjoinRoot D)] :
    LinearMap.charpoly (LinearMap.mulLeft F (AdjoinRoot.root D)) = D := by
  have h := charpoly_leftMulMatrix (AdjoinRoot.powerBasis' hD)
  rw [AdjoinRoot.powerBasis'_gen] at h
  have h2 : minpoly F (AdjoinRoot.root D) = D := by
    rw [AdjoinRoot.minpoly_root hD.ne_zero, hD.leadingCoeff]; simp
  rw [h2] at h
  rw [← LinearMap.charpoly_toMatrix _ (AdjoinRoot.powerBasis' hD).basis]
  exact h

/- English proof (translation)
Proceed by induction on `p using Polynomial.induction_on with`. Consider the case `C a`. Establish `: AdjoinRoot.mk D (C a) = a • (1 : AdjoinRoot D)`. Rewrite using `[Algebra.smul_def, mul_one]`. Both sides reduce to the same expression.

Rewrite using `[this, map_smul]`. Simplify using the standard rewrite rules. Consider the case `add p q hp hq => simp [hp, hq]`. Consider the case `monomial n a ih`. Establish `: C a * X ^ (n + 1) = X * (C a * X ^ n)` using `by ring`.

Rewrite using `[this, map_mul, AdjoinRoot.mk_X, h, ih, map_mul (aeval g) X, aeval_X, Module.End.mul_apply]`.
-/
theorem map_mk {V : Type} [AddCommGroup V] [Module F V] (D : F[X]) (f : AdjoinRoot D →ₗ[F] V)
    (g : Module.End F V) (h : ∀ a, f (AdjoinRoot.root D * a) = g (f a)) (p : F[X]) :
    f (AdjoinRoot.mk D p) = aeval g p (f 1) := by
  induction p using Polynomial.induction_on with
  | C a =>
    have : AdjoinRoot.mk D (C a) = a • (1 : AdjoinRoot D) := by
      rw [Algebra.smul_def, mul_one]; rfl
    rw [this, map_smul]; simp
  | add p q hp hq => simp [hp, hq]
  | monomial n a ih =>
    have : C a * X ^ (n + 1) = X * (C a * X ^ n) := by ring
    rw [this, map_mul, AdjoinRoot.mk_X, h, ih, map_mul (aeval g) X, aeval_X, Module.End.mul_apply]

/- English proof (translation)
Rewrite using `[eq_top_iff]`. Introduce `a _`. Take `⟨p, rfl⟩` from `AdjoinRoot.mk_surjective a`. Proceed by induction on `p using Polynomial.induction_on with`. Consider the case `C a`.

Establish `: AdjoinRoot.mk D (C a) = a • (1 : AdjoinRoot D)`. Rewrite using `[Algebra.smul_def, mul_one]`. Both sides reduce to the same expression. Rewrite using `[this]`. Conclude with `U.smul_mem _ h1`.

Consider the case `add p q hp hq => rw [map_add]`. Conclude with `U.add_mem (hp trivial) (hq trivial)`. Consider the case `monomial n a ih`. Establish `: C a * X ^ (n + 1) = X * (C a * X ^ n)` using `by ring`. Rewrite using `[this, map_mul, AdjoinRoot.mk_X]`.

Conclude with `hU _ (ih trivial)`.
-/
theorem cyclic_one (D : F[X]) (U : Submodule F (AdjoinRoot D))
    (hU : ∀ a ∈ U, AdjoinRoot.root D * a ∈ U) (h1 : (1 : AdjoinRoot D) ∈ U) : U = ⊤ := by
  rw [eq_top_iff]
  intro a _
  obtain ⟨p, rfl⟩ := AdjoinRoot.mk_surjective a
  induction p using Polynomial.induction_on with
  | C a =>
    have : AdjoinRoot.mk D (C a) = a • (1 : AdjoinRoot D) := by
      rw [Algebra.smul_def, mul_one]; rfl
    rw [this]; exact U.smul_mem _ h1
  | add p q hp hq => rw [map_add]; exact U.add_mem (hp trivial) (hq trivial)
  | monomial n a ih =>
    have : C a * X ^ (n + 1) = X * (C a * X ^ n) := by ring
    rw [this, map_mul, AdjoinRoot.mk_X]
    exact hU _ (ih trivial)

/- English proof (translation)
Use `haveI : FiniteDimensional F (AdjoinRoot D) := (AdjoinRoot.powerBasis' hD).finite`. Establish `hA : Module.finrank F (AdjoinRoot D) = D.natDegree` using `(AdjoinRoot.powerBasis' hD).finrank`. Set `Φ : (AdjoinRoot D ≃ₗ[F] V) → (Σ g : {g : Module.End F V // LinearMap.charpoly g = D}, {v : V // ∀ U : Submodule F V, (∀ x ∈ U, g.1 x ∈ U) → v ∈ U → U = ⊤})` to `fun e => ⟨⟨e.conj (LinearMap.mulLeft F (AdjoinRoot.root D)), by`. Rewrite using `[LinearEquiv.charpoly_conj, charpoly_mulLeft_root D hD]⟩,`. Use the proof step `⟨e 1, fun U hU h1 => by`.

Use `cyclic_one D (U.comap e.toLinearMap) (fun a ha => by` as an intermediate fact. Use `hU _ ha` as an intermediate fact. Simplify `this) h1` using `[LinearEquiv.conj_apply]`. Rewrite using `[eq_top_iff]`. Introduce `v _`.

Establish `h2 : e.symm v ∈ U.comap e.toLinearMap` using `this ▸ Submodule.mem_top`. Simplify using `using h2⟩⟩`. Establish `hΦ : ∀ (e : AdjoinRoot D ≃ₗ[F] V) (p : F[X]), e (AdjoinRoot.mk D p) = aeval (Φ e).1.1 p (Φ e).2.1` using `fun e p => map_mk D e.toLinearMap _ (fun a => by simp [Φ, LinearEquiv.conj_apply]) p`. Use `Nat.card_congr (Equiv.ofBijective Φ ⟨?_, ?_⟩)` and prove the remaining obligations. Introduce `e e' h`.

Use extensionality with `a`. Take `⟨p, rfl⟩` from `AdjoinRoot.mk_surjective a`. Rewrite using `[hΦ, hΦ, h]`. Introduce and unpack `⟨⟨g, hg⟩, ⟨v, hv⟩⟩`. Establish `h0 : aeval g D = 0` using `hg ▸ LinearMap.aeval_self_charpoly g`.

Set `f : AdjoinRoot D →ₗ[F] V` to `(LinearMap.applyₗ v) ∘ₗ (aeval g).toLinearMap ∘ₗ AdjoinRoot.modByMonicHom hD`. Establish `hf : ∀ p, f (AdjoinRoot.mk D p) = aeval g p v` using `fun p => by`. Simplify using `[f, AdjoinRoot.modByMonicHom_mk, Polynomial.aeval_modByMonic_eq_self_of_root h0]`. Establish `hf1 : f 1 = v` using `by simpa using hf 1`. Establish `hfx : ∀ a, f (AdjoinRoot.root D * a) = g (f a)` using `fun a => by`.

Take `⟨p, rfl⟩` from `AdjoinRoot.mk_surjective a`. Rewrite using `[← AdjoinRoot.mk_X, ← map_mul, hf, hf]`. Simplify using the standard rewrite rules. Establish `hs : Function.Surjective f`. Rewrite using `[← LinearMap.range_eq_top]`.

Use `hv _ ?_ ⟨1, hf1⟩` and prove the remaining obligations. Introduce and unpack `_ ⟨a, rfl⟩`. Conclude with `⟨_, hfx a⟩`. Establish `hi : Function.Injective f` using `(LinearMap.injective_iff_surjective_of_finrank_eq_finrank (hA.trans hV.symm)).2 hs`. Use `⟨LinearEquiv.ofBijective f ⟨hi, hs⟩, ?_⟩` and prove the remaining obligations.

Establish `hg' : (Φ (LinearEquiv.ofBijective f ⟨hi, hs⟩)).1 = ⟨g, hg⟩`. Apply `Subtype.ext` to reduce the goal to its premises. Use extensionality with `w`. Take `⟨a, rfl⟩` from `(LinearEquiv.ofBijective f ⟨hi, hs⟩).surjective w`. Simplify using `only [Φ, LinearEquiv.conj_apply, LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply]`.

Conclude with `hfx a`. Use `Sigma.ext hg' ?_` and prove the remaining obligations. Use `(Subtype.heq_iff_coe_eq ?_).2 hf1` and prove the remaining obligations. Introduce `w`. Rewrite using `[hg']`.
-/
theorem card_pairs {V : Type} [AddCommGroup V] [Module F V] [FiniteDimensional F V] (D : F[X]) (hD : D.Monic)
    (hV : Module.finrank F V = D.natDegree) :
    Nat.card (AdjoinRoot D ≃ₗ[F] V) =
      Nat.card (Σ g : {g : Module.End F V // LinearMap.charpoly g = D},
        {v : V // ∀ U : Submodule F V, (∀ x ∈ U, g.1 x ∈ U) → v ∈ U → U = ⊤}) := by
  haveI : FiniteDimensional F (AdjoinRoot D) := (AdjoinRoot.powerBasis' hD).finite
  have hA : Module.finrank F (AdjoinRoot D) = D.natDegree := (AdjoinRoot.powerBasis' hD).finrank
  let Φ : (AdjoinRoot D ≃ₗ[F] V) → (Σ g : {g : Module.End F V // LinearMap.charpoly g = D},
        {v : V // ∀ U : Submodule F V, (∀ x ∈ U, g.1 x ∈ U) → v ∈ U → U = ⊤}) := fun e =>
    ⟨⟨e.conj (LinearMap.mulLeft F (AdjoinRoot.root D)), by
        rw [LinearEquiv.charpoly_conj, charpoly_mulLeft_root D hD]⟩,
      ⟨e 1, fun U hU h1 => by
        have := cyclic_one D (U.comap e.toLinearMap) (fun a ha => by
          have := hU _ ha
          simpa [LinearEquiv.conj_apply] using this) h1
        rw [eq_top_iff]
        intro v _
        have h2 : e.symm v ∈ U.comap e.toLinearMap := this ▸ Submodule.mem_top
        simpa using h2⟩⟩
  have hΦ : ∀ (e : AdjoinRoot D ≃ₗ[F] V) (p : F[X]),
      e (AdjoinRoot.mk D p) = aeval (Φ e).1.1 p (Φ e).2.1 := fun e p =>
    map_mk D e.toLinearMap _ (fun a => by simp [Φ, LinearEquiv.conj_apply]) p
  refine Nat.card_congr (Equiv.ofBijective Φ ⟨?_, ?_⟩)
  · intro e e' h
    ext a
    obtain ⟨p, rfl⟩ := AdjoinRoot.mk_surjective a
    rw [hΦ, hΦ, h]
  · rintro ⟨⟨g, hg⟩, ⟨v, hv⟩⟩
    have h0 : aeval g D = 0 := hg ▸ LinearMap.aeval_self_charpoly g
    let f : AdjoinRoot D →ₗ[F] V :=
      (LinearMap.applyₗ v) ∘ₗ (aeval g).toLinearMap ∘ₗ AdjoinRoot.modByMonicHom hD
    have hf : ∀ p, f (AdjoinRoot.mk D p) = aeval g p v := fun p => by
      simp [f, AdjoinRoot.modByMonicHom_mk, Polynomial.aeval_modByMonic_eq_self_of_root h0]
    have hf1 : f 1 = v := by simpa using hf 1
    have hfx : ∀ a, f (AdjoinRoot.root D * a) = g (f a) := fun a => by
      obtain ⟨p, rfl⟩ := AdjoinRoot.mk_surjective a
      rw [← AdjoinRoot.mk_X, ← map_mul, hf, hf]; simp
    have hs : Function.Surjective f := by
      rw [← LinearMap.range_eq_top]
      refine hv _ ?_ ⟨1, hf1⟩
      rintro _ ⟨a, rfl⟩
      exact ⟨_, hfx a⟩
    have hi : Function.Injective f :=
      (LinearMap.injective_iff_surjective_of_finrank_eq_finrank (hA.trans hV.symm)).2 hs
    refine ⟨LinearEquiv.ofBijective f ⟨hi, hs⟩, ?_⟩
    have hg' : (Φ (LinearEquiv.ofBijective f ⟨hi, hs⟩)).1 = ⟨g, hg⟩ := by
      apply Subtype.ext
      ext w
      obtain ⟨a, rfl⟩ := (LinearEquiv.ofBijective f ⟨hi, hs⟩).surjective w
      simp only [Φ, LinearEquiv.conj_apply, LinearMap.comp_apply, LinearEquiv.coe_coe,
        LinearEquiv.symm_apply_apply]
      exact hfx a
    refine Sigma.ext hg' ?_
    refine (Subtype.heq_iff_coe_eq ?_).2 hf1
    intro w
    rw [hg']

end GlobalTheory.CuspGL.CyclicMass

namespace GlobalTheory.CuspGL

/- English proof (translation)
Use `haveI : FiniteDimensional F (AdjoinRoot D) := (AdjoinRoot.powerBasis' hD).finite`. Establish `hA : Module.finrank F (AdjoinRoot D) = D.natDegree` using `(AdjoinRoot.powerBasis' hD).finrank`. Establish `h` using `CyclicMass.card_pairs (V := Fin D.natDegree → F) D hD (by simp)`. Use `haveI : Finite (Module.End F (Fin D.natDegree → F)) := Finite.of_injective _ DFunLike.coe_injective`. Use `haveI := Fintype.ofFinite {g : Module.End F (Fin D.natDegree → F) // LinearMap.charpoly g = D}`.

Rewrite `h` using `[Nat.card_sigma]`. Set `e0 : AdjoinRoot D ≃ₗ[F] (Fin D.natDegree → F)` to `LinearEquiv.ofFinrankEq _ _ (by simp [hA])`. Establish `h2 : Nat.card (AdjoinRoot D ≃ₗ[F] (Fin D.natDegree → F)) = Nat.card (GL (Fin D.natDegree) F)`. Use `Nat.card_congr (Equiv.trans ?_ (Matrix.GeneralLinearGroup.toLin.trans (LinearMap.GeneralLinearGroup.generalLinearEquiv F _)).toEquiv.symm)` and prove the remaining obligations. Conclude with `⟨fun e => e0.symm.trans e, fun e => e0.trans e, fun e => by ext; simp, fun e => by ext; simp⟩`.

Rewrite using `[glCard, ← h2, h, mass, ← finsum_set_coe_eq_finsum_mem, Nat.cast_sum]`. Conclude with `finsum_eq_sum_of_fintype (α := {g : Module.End F (Fin D.natDegree → F) // LinearMap.charpoly g = D}) _`.
-/
theorem mass_card_cyclic (F : Type) [Field F] [Finite F] (D : F[X]) (hD : D.Monic) :
    mass (fun g : Module.End F (Fin D.natDegree → F) =>
      (Nat.card {v : Fin D.natDegree → F // ∀ U : Submodule F (Fin D.natDegree → F),
        (∀ x ∈ U, g x ∈ U) → v ∈ U → U = ⊤} : ℂ)) D = glCard F D.natDegree := by
  classical
  haveI : FiniteDimensional F (AdjoinRoot D) := (AdjoinRoot.powerBasis' hD).finite
  have hA : Module.finrank F (AdjoinRoot D) = D.natDegree := (AdjoinRoot.powerBasis' hD).finrank
  have h := CyclicMass.card_pairs (V := Fin D.natDegree → F) D hD (by simp)
  haveI : Finite (Module.End F (Fin D.natDegree → F)) :=
    Finite.of_injective _ DFunLike.coe_injective
  haveI := Fintype.ofFinite {g : Module.End F (Fin D.natDegree → F) // LinearMap.charpoly g = D}
  rw [Nat.card_sigma] at h
  let e0 : AdjoinRoot D ≃ₗ[F] (Fin D.natDegree → F) :=
    LinearEquiv.ofFinrankEq _ _ (by simp [hA])
  have h2 : Nat.card (AdjoinRoot D ≃ₗ[F] (Fin D.natDegree → F)) = Nat.card (GL (Fin D.natDegree) F) := by
    refine Nat.card_congr (Equiv.trans ?_ (Matrix.GeneralLinearGroup.toLin.trans
      (LinearMap.GeneralLinearGroup.generalLinearEquiv F _)).toEquiv.symm)
    exact ⟨fun e => e0.symm.trans e, fun e => e0.trans e, fun e => by ext; simp, fun e => by ext; simp⟩
  rw [glCard, ← h2, h, mass, ← finsum_set_coe_eq_finsum_mem, Nat.cast_sum]
  exact finsum_eq_sum_of_fintype (α := {g : Module.End F (Fin D.natDegree → F) // LinearMap.charpoly g = D}) _

end GlobalTheory.CuspGL

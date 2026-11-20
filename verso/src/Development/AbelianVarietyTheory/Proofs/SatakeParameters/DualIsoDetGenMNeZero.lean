import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.GlobSpecOfExists
import Formalism.GradedWeylDivisibility.FinalD
import Formalism.GradedWeylDivisibility.DualWeylDominanceOf
import Formalism.LocalToGlobal.Divisibility.CoefModLemmas
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.PosOkId
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsCofactorTwistDualWeylStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.WeylLatticeExistsCofactorTwistDualStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.CofactorTwistRelationDualWeightInvolutiveStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.CofactorTwistRelationRowActEquivariantStatement

noncomputable section

namespace GlobalTheory.ValCmp

open MvPolynomial Formalism.GradedWeylDivisibility Formalism.MainNotions.G

/- English proof (translation)
Introduce `h`. Establish `h1` using `congrArg (MvPolynomial.eval fun v : Fin n × Fin n => (1 : Matrix (Fin n) (Fin n) R) v.1 v.2) h`. Rewrite `h1` using `[RingHom.map_det, map_zero]`. Establish `h2 : (MvPolynomial.eval fun v : Fin n × Fin n => (1 : Matrix (Fin n) (Fin n) R) v.1 v.2).mapMatrix (genM R n) = 1`. Use extensionality with `a b`.

Simplify using `[genM]`. Rewrite `h1` using `[h2, Matrix.det_one]`. Conclude with `one_ne_zero h1`.
-/
theorem dualIso_det_genM_ne_zero (R : Type) [CommRing R] [Nontrivial R] (n : ℕ) : (genM R n).det ≠ 0 := by
  intro h
  have h1 := congrArg (MvPolynomial.eval fun v : Fin n × Fin n => (1 : Matrix (Fin n) (Fin n) R) v.1 v.2) h
  rw [RingHom.map_det, map_zero] at h1
  have h2 : (MvPolynomial.eval fun v : Fin n × Fin n => (1 : Matrix (Fin n) (Fin n) R) v.1 v.2).mapMatrix
      (genM R n) = 1 := by
    ext a b
    simp [genM]
  rw [h2, Matrix.det_one] at h1
  exact one_ne_zero h1

/- English proof (translation)
The claim follows from `mul_left_cancel₀ (pow_ne_zero _ (dualIso_det_genM_ne_zero R (m + 1))) (h.trans h'.symm)`.
-/
theorem dualIso_cofRel_unique {R : Type} [CommRing R] [IsDomain R] {m : ℕ} {ν : Fin (m + 1) → ℕ}
    {f g g' : MP R (m + 1)} (h : CofRel R m ν f g) (h' : CofRel R m ν f g') : g = g' :=
  mul_left_cancel₀ (pow_ne_zero _ (dualIso_det_genM_ne_zero R (m + 1))) (h.trans h'.symm)

/- English proof (translation)
Unfold `CofRel at *`. Rewrite using `[mul_add, map_add, h, h']`.
-/
theorem dualIso_cofRel_add {R : Type} [CommRing R] {m : ℕ} {ν : Fin (m + 1) → ℕ}
    {f g f' g' : MP R (m + 1)} (h : CofRel R m ν f g) (h' : CofRel R m ν f' g') :
    CofRel R m ν (f + f') (g + g') := by
  unfold CofRel at *
  rw [mul_add, map_add, h, h']

/- English proof (translation)
Unfold `CofRel at *`. Rewrite using `[mul_smul_comm, map_smul, h]`.
-/
theorem dualIso_cofRel_smul {R : Type} [CommRing R] {m : ℕ} {ν : Fin (m + 1) → ℕ}
    {f g : MP R (m + 1)} (c : R) (h : CofRel R m ν f g) : CofRel R m ν (c • f) (c • g) := by
  unfold CofRel at *
  rw [mul_smul_comm, map_smul, h]

/- English proof (translation)
Unfold `CofRel at *`. Rewrite using `[mul_smul_comm, map_zsmul, h]`.
-/
theorem dualIso_cofRel_zsmul {R : Type} [CommRing R] {m : ℕ} {ν : Fin (m + 1) → ℕ}
    {f g : MP R (m + 1)} (c : ℤ) (h : CofRel R m ν f g) : CofRel R m ν (c • f) (c • g) := by
  unfold CofRel at *
  rw [mul_smul_comm, map_zsmul, h]

/- English proof (translation)
Use `ext1 a b`. Simplify using `[genM]`.
-/
theorem dualIso_map_genM {R S : Type} [CommRing R] [CommRing S] (φ : R →+* S) (n : ℕ) :
    (MvPolynomial.map φ).mapMatrix (genM R n) = genM S n := by
  ext1 a b
  simp [genM]

/- English proof (translation)
Proceed by induction on `f using MvPolynomial.induction_on with`. Consider the case `C a => simp [cofAct]`. Consider the case `add p q hp hq => simp only [map_add, hp, hq]`. Consider the case `mul_X p v hp`. Simplify using `only [map_mul, hp, map_X]`.

Use `congr 1`. Simplify using `only [cofAct, aeval_X]`. Rewrite using `[← dualIso_map_genM φ n, ← RingHom.map_adjugate]`. Both sides reduce to the same expression.
-/
theorem dualIso_map_cofAct {R S : Type} [CommRing R] [CommRing S] (φ : R →+* S) (n : ℕ) (f : MP R n) :
    MvPolynomial.map φ (cofAct R n f) = cofAct S n (MvPolynomial.map φ f) := by
  induction f using MvPolynomial.induction_on with
  | C a => simp [cofAct]
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p v hp =>
    simp only [map_mul, hp, map_X]
    congr 1
    simp only [cofAct, aeval_X]
    rw [← dualIso_map_genM φ n, ← RingHom.map_adjugate]
    rfl

/- English proof (translation)
Unfold `CofRel at *`. Rewrite using `[← dualIso_map_cofAct, ← h, map_mul, map_pow, RingHom.map_det, dualIso_map_genM]`.
-/
theorem dualIso_cofRel_map {R S : Type} [CommRing R] [CommRing S] (φ : R →+* S) {m : ℕ} {ν : Fin (m + 1) → ℕ}
    {f g : MP R (m + 1)} (h : CofRel R m ν f g) :
    CofRel S m ν (MvPolynomial.map φ f) (MvPolynomial.map φ g) := by
  unfold CofRel at *
  rw [← dualIso_map_cofAct, ← h, map_mul, map_pow, RingHom.map_det, dualIso_map_genM]

/- English proof (translation)
Introduce `i j hij`. Use `hν (Fin.rev_le_rev.2 hij)` as an intermediate fact. Simplify using `only [nuDual]`. Use linear arithmetic over natural numbers and integers.
-/
theorem dualIso_nuDual_antitone {m : ℕ} {ν : Fin (m + 1) → ℕ} (hν : Antitone ν) : Antitone (nuDual ν) := by
  intro i j hij
  have := hν (Fin.rev_le_rev.2 hij)
  simp only [nuDual]
  omega

/- English proof (translation)
Simplify using `[nuDual]`.
-/
theorem dualIso_nuDual_last {m : ℕ} (ν : Fin (m + 1) → ℕ) : nuDual ν (Fin.last m) = 0 := by
  simp [nuDual]

/- English proof (translation)
Use function extensionality and compare the values at `i`. Use `hν (Fin.zero_le i)` as an intermediate fact. Simplify using `only [nuDual, Fin.rev_rev, Fin.rev_zero, hl]`. Use linear arithmetic over natural numbers and integers.
-/
theorem dualIso_nuDual_nuDual {m : ℕ} {ν : Fin (m + 1) → ℕ} (hν : Antitone ν) (hl : ν (Fin.last m) = 0) :
    nuDual (nuDual ν) = ν := by
  funext i
  have := hν (Fin.zero_le i)
  simp only [nuDual, Fin.rev_rev, Fin.rev_zero, hl]
  omega

/- English proof (translation)
Rewrite using `[smul_smul, ← Units.val_mul, Int.units_mul_self, Units.val_one, one_smul]`.
-/
theorem dualIso_units_smul_smul {M : Type} [AddCommGroup M] (ε : ℤˣ) (x : M) : (ε : ℤ) • (ε : ℤ) • x = x := by
  rw [smul_smul, ← Units.val_mul, Int.units_mul_self, Units.val_one, one_smul]

/- English proof (translation)
Use `choose G hG using GlobalTheory.T.exists_cofactorTwist_dualWeyl K m ν hν hl`. Set `Ψ₀ : dualWeyl K (m + 1) (m + 1) ν →ₗ[K] MP K (m + 1)` to `{ toFun := fun f => G f.1 f.2 map_add' := fun f g => dualIso_cofRel_unique (hG _ (f + g).2).2 (dualIso_cofRel_add (hG _ f.2).2 (hG _ g.2).2) map_smul' := fun c f => dualIso_cofRel_unique (hG _ (c • f).2).2 (dualIso_cofRel_smul c (hG _ f.2).2) }`. Take `⟨Ψ, hΨ⟩` from `LinearMap.exists_extend Ψ₀`. Use `⟨Ψ, fun f hf => ?_⟩` and prove the remaining obligations. Establish `h1 : Ψ f = G f hf` using `LinearMap.congr_fun hΨ ⟨f, hf⟩`.

Rewrite using `[h1]`. Conclude with `(hG f hf).2`.
-/
theorem dualIso_exists_map (K : Type) [Field K] (m : ℕ) (ν : Fin (m + 1) → ℕ) (hν : Antitone ν)
    (hl : ν (Fin.last m) = 0) :
    ∃ Ψ : MP K (m + 1) →ₗ[K] MP K (m + 1), ∀ f ∈ dualWeyl K (m + 1) (m + 1) ν, CofRel K m ν f (Ψ f) := by
  choose G hG using GlobalTheory.T.exists_cofactorTwist_dualWeyl K m ν hν hl
  let Ψ₀ : dualWeyl K (m + 1) (m + 1) ν →ₗ[K] MP K (m + 1) :=
    { toFun := fun f => G f.1 f.2
      map_add' := fun f g =>
        dualIso_cofRel_unique (hG _ (f + g).2).2 (dualIso_cofRel_add (hG _ f.2).2 (hG _ g.2).2)
      map_smul' := fun c f =>
        dualIso_cofRel_unique (hG _ (c • f).2).2 (dualIso_cofRel_smul c (hG _ f.2).2) }
  obtain ⟨Ψ, hΨ⟩ := LinearMap.exists_extend Ψ₀
  refine ⟨Ψ, fun f hf => ?_⟩
  have h1 : Ψ f = G f hf := LinearMap.congr_fun hΨ ⟨f, hf⟩
  rw [h1]
  exact (hG f hf).2

/- English proof (translation)
Establish `key : ∀ f ∈ A, ∀ g, CofRel O m ν f g → Ψ (MvPolynomial.map (algebraMap O Kf) f) = MvPolynomial.map (algebraMap O Kf) g` using `fun f hf g hfg => dualIso_cofRel_unique (hΨ _ (dualWeylMap O Kf _ _ _ _ _ (hA hf))) (dualIso_cofRel_map _ hfg)`. Apply `le_antisymm` to reduce the goal to its premises. Introduce and unpack `_ ⟨_, ⟨f, hf, rfl⟩, rfl⟩`. Take `⟨g, hg, hfg⟩` from `hAB f hf`. Conclude with `⟨g, hg, (key f hf g hfg).symm⟩`.

Introduce and unpack `_ ⟨g, hg, rfl⟩`. Take `⟨f, hf, hgf⟩` from `hBA g hg`. Take `⟨ε, hε⟩` from `GlobalTheory.T.cofactorTwistRelation_dualWeight_involutive O m (nuDual ν) (dualIso_nuDual_antitone hν) (dualIso_nuDual_last ν)`. Establish `h1` using `hε g (hB hg) f hgf`. Rewrite `h1` using `[dualIso_nuDual_nuDual hν hl]`.

Establish `h2` using `dualIso_cofRel_zsmul (ε : ℤ) h1`. Rewrite `h2` using `[dualIso_units_smul_smul]`. Establish `h3 : (ε : ℤ) • f ∈ A` using `A.toAddSubgroup.zsmul_mem hf _`. Conclude with `⟨_, ⟨_, h3, rfl⟩, key _ h3 g h2⟩`.
-/
theorem dualIso_lattice (O Kf : Type) [CommRing O] [IsDomain O] [Field Kf] [Algebra O Kf] (m : ℕ)
    (ν : Fin (m + 1) → ℕ) (hν : Antitone ν) (hl : ν (Fin.last m) = 0)
    (Ψ : MP Kf (m + 1) →ₗ[Kf] MP Kf (m + 1))
    (hΨ : ∀ f ∈ dualWeyl Kf (m + 1) (m + 1) ν, CofRel Kf m ν f (Ψ f))
    (A B : Submodule O (MP O (m + 1))) (hA : A ≤ dualWeyl O (m + 1) (m + 1) ν)
    (hB : B ≤ dualWeyl O (m + 1) (m + 1) (nuDual ν))
    (hAB : ∀ f ∈ A, ∃ g ∈ B, CofRel O m ν f g) (hBA : ∀ g ∈ B, ∃ f ∈ A, CofRel O m (nuDual ν) g f) :
    (A.map (mapAlgHom (Algebra.ofId O Kf)).toLinearMap).map (Ψ.restrictScalars O) =
      B.map (mapAlgHom (Algebra.ofId O Kf)).toLinearMap := by
  have key : ∀ f ∈ A, ∀ g, CofRel O m ν f g →
      Ψ (MvPolynomial.map (algebraMap O Kf) f) = MvPolynomial.map (algebraMap O Kf) g := fun f hf g hfg =>
    dualIso_cofRel_unique (hΨ _ (dualWeylMap O Kf _ _ _ _ _ (hA hf))) (dualIso_cofRel_map _ hfg)
  apply le_antisymm
  · rintro _ ⟨_, ⟨f, hf, rfl⟩, rfl⟩
    obtain ⟨g, hg, hfg⟩ := hAB f hf
    exact ⟨g, hg, (key f hf g hfg).symm⟩
  · rintro _ ⟨g, hg, rfl⟩
    obtain ⟨f, hf, hgf⟩ := hBA g hg
    obtain ⟨ε, hε⟩ := GlobalTheory.T.cofactorTwistRelation_dualWeight_involutive O m (nuDual ν) (dualIso_nuDual_antitone hν) (dualIso_nuDual_last ν)
    have h1 := hε g (hB hg) f hgf
    rw [dualIso_nuDual_nuDual hν hl] at h1
    have h2 := dualIso_cofRel_zsmul (ε : ℤ) h1
    rw [dualIso_units_smul_smul] at h2
    have h3 : (ε : ℤ) • f ∈ A := A.toAddSubgroup.zsmul_mem hf _
    exact ⟨_, ⟨_, h3, rfl⟩, key _ h3 g h2⟩

/- English proof (translation)
Take `⟨Ψ, hΨ⟩` from `dualIso_exists_map Kf m ν hν hl`. Establish `hν'` using `dualIso_nuDual_antitone hν`. Establish `hl'` using `dualIso_nuDual_last ν`. Establish `hdd` using `dualIso_nuDual_nuDual hν hl`. Use `⟨Ψ, fun f hf h0 => ?_, ?_, fun h hh f hf => ?_, ?_, ?_⟩` and prove the remaining obligations.

Take `⟨ε, hε⟩` from `GlobalTheory.T.cofactorTwistRelation_dualWeight_involutive Kf m ν hν hl`. Establish `h1` using `hε f hf _ (hΨ f hf)`. Rewrite `h1` using `[h0]`. Establish `h2 : CofRel Kf m (nuDual ν) 0 0` using `by simp [CofRel]`. Establish `h3` using `dualIso_cofRel_unique h1 h2`.

Rewrite using `[← dualIso_units_smul_smul ε f, h3, smul_zero]`. Apply `le_antisymm` to reduce the goal to its premises. Introduce and unpack `_ ⟨f, hf, rfl⟩`. Take `⟨g, hg, hfg⟩` from `GlobalTheory.T.exists_cofactorTwist_dualWeyl Kf m ν hν hl f hf`. Rewrite using `[dualIso_cofRel_unique (hΨ f hf) hfg]`.

Conclude with `hg`. Introduce `g hg`. Take `⟨f, hf, hgf⟩` from `GlobalTheory.T.exists_cofactorTwist_dualWeyl Kf m _ hν' hl' g hg`. Take `⟨ε, hε⟩` from `GlobalTheory.T.cofactorTwistRelation_dualWeight_involutive Kf m _ hν' hl'`. Establish `h1` using `hε g hg f hgf`.

Rewrite `h1`, `hf` using `[hdd]`. Establish `h2` using `dualIso_cofRel_zsmul (ε : ℤ) h1`. Rewrite `h2` using `[dualIso_units_smul_smul]`. Establish `h3 : (ε : ℤ) • f ∈ dualWeyl Kf (m + 1) (m + 1) ν` using `(dualWeyl Kf (m + 1) (m + 1) ν).toAddSubgroup.zsmul_mem hf _`. Conclude with `⟨_, h3, dualIso_cofRel_unique (hΨ _ h3) h2⟩`.

Establish `h1` using `GlobalTheory.T.cofactorTwistRelation_rowAct_equivariant Kf m ν h hh f hf _ (hΨ f hf)`. Establish `h2` using `dualIso_cofRel_unique (hΨ _ (dualWeylRowStable Kf _ _ _ h⁻¹ f hf)) h1`. Establish `h3 : (h⁻¹).transpose⁻¹ = h.transpose`. Rewrite using `[← Matrix.transpose_nonsing_inv, Matrix.nonsing_inv_nonsing_inv _ hh]`. Establish `h4 : (h⁻¹).transpose.det = (h.det)⁻¹`.

Rewrite using `[Matrix.det_transpose, Matrix.det_nonsing_inv, Ring.inverse_eq_inv']`. Simplify using `only [rnd, LinearMap.smul_apply, map_smul, AlgHom.toLinearMap_apply, h2, h3, h4, smul_smul, inv_zpow']`. Rewrite using `[← zpow_add₀ hh.ne_zero, ← zpow_add₀ hh.ne_zero]`. Use `congr 2`. Expand and normalize the polynomial expressions, which then agree.

Use `dualIso_lattice O Kf m ν hν hl Ψ hΨ _ _ le_rfl le_rfl (GlobalTheory.T.exists_cofactorTwist_dualWeyl O m ν hν hl) fun g hg => ?_` and prove the remaining obligations. Use `GlobalTheory.T.exists_cofactorTwist_dualWeyl O m _ hν' hl' g hg` as an intermediate fact. Rewrite `this` using `[hdd]`. Then use the resulting hypothesis. Use `dualIso_lattice O Kf m ν hν hl Ψ hΨ _ _ (weylLeDual O _ _ _ _ hν) (weylLeDual O _ _ _ _ hν') (GlobalTheory.T.weylLattice_exists_cofactorTwist_dual O m ν hν hl) fun g hg => ?_` and prove the remaining obligations. Use `GlobalTheory.T.weylLattice_exists_cofactorTwist_dual O m _ hν' hl' g hg` as an intermediate fact.

Rewrite `this` using `[hdd]`. Then use the resulting hypothesis.
-/
theorem exists_posOk_dual (O Kf : Type) [CommRing O] [IsDomain O] [Field Kf] [Algebra O Kf] (m : ℕ)
    (ν : Fin (m + 1) → ℕ) (hν : Antitone ν) (hl : ν (Fin.last m) = 0) (e c : ℤ) :
    ∃ Ψ : MP Kf (m + 1) →ₗ[Kf] MP Kf (m + 1),
      PosOk O Kf (m + 1) ν (nuDual ν) e (-(e + ν 0 + c)) c (fun h => (h⁻¹).transpose) Ψ := by
  obtain ⟨Ψ, hΨ⟩ := dualIso_exists_map Kf m ν hν hl
  have hν' := dualIso_nuDual_antitone hν
  have hl' := dualIso_nuDual_last ν
  have hdd := dualIso_nuDual_nuDual hν hl
  refine ⟨Ψ, fun f hf h0 => ?_, ?_, fun h hh f hf => ?_, ?_, ?_⟩
  · obtain ⟨ε, hε⟩ := GlobalTheory.T.cofactorTwistRelation_dualWeight_involutive Kf m ν hν hl
    have h1 := hε f hf _ (hΨ f hf)
    rw [h0] at h1
    have h2 : CofRel Kf m (nuDual ν) 0 0 := by simp [CofRel]
    have h3 := dualIso_cofRel_unique h1 h2
    rw [← dualIso_units_smul_smul ε f, h3, smul_zero]
  · apply le_antisymm
    · rintro _ ⟨f, hf, rfl⟩
      obtain ⟨g, hg, hfg⟩ := GlobalTheory.T.exists_cofactorTwist_dualWeyl Kf m ν hν hl f hf
      rw [dualIso_cofRel_unique (hΨ f hf) hfg]
      exact hg
    · intro g hg
      obtain ⟨f, hf, hgf⟩ := GlobalTheory.T.exists_cofactorTwist_dualWeyl Kf m _ hν' hl' g hg
      obtain ⟨ε, hε⟩ := GlobalTheory.T.cofactorTwistRelation_dualWeight_involutive Kf m _ hν' hl'
      have h1 := hε g hg f hgf
      rw [hdd] at h1 hf
      have h2 := dualIso_cofRel_zsmul (ε : ℤ) h1
      rw [dualIso_units_smul_smul] at h2
      have h3 : (ε : ℤ) • f ∈ dualWeyl Kf (m + 1) (m + 1) ν :=
        (dualWeyl Kf (m + 1) (m + 1) ν).toAddSubgroup.zsmul_mem hf _
      exact ⟨_, h3, dualIso_cofRel_unique (hΨ _ h3) h2⟩
  · have h1 := GlobalTheory.T.cofactorTwistRelation_rowAct_equivariant Kf m ν h hh f hf _ (hΨ f hf)
    have h2 := dualIso_cofRel_unique (hΨ _ (dualWeylRowStable Kf _ _ _ h⁻¹ f hf)) h1
    have h3 : (h⁻¹).transpose⁻¹ = h.transpose := by
      rw [← Matrix.transpose_nonsing_inv, Matrix.nonsing_inv_nonsing_inv _ hh]
    have h4 : (h⁻¹).transpose.det = (h.det)⁻¹ := by
      rw [Matrix.det_transpose, Matrix.det_nonsing_inv, Ring.inverse_eq_inv']
    simp only [rnd, LinearMap.smul_apply, map_smul, AlgHom.toLinearMap_apply, h2, h3, h4, smul_smul, inv_zpow']
    rw [← zpow_add₀ hh.ne_zero, ← zpow_add₀ hh.ne_zero]
    congr 2
    ring
  · refine dualIso_lattice O Kf m ν hν hl Ψ hΨ _ _ le_rfl le_rfl (GlobalTheory.T.exists_cofactorTwist_dualWeyl O m ν hν hl) fun g hg => ?_
    have := GlobalTheory.T.exists_cofactorTwist_dualWeyl O m _ hν' hl' g hg
    rwa [hdd] at this
  · refine dualIso_lattice O Kf m ν hν hl Ψ hΨ _ _ (weylLeDual O _ _ _ _ hν) (weylLeDual O _ _ _ _ hν')
      (GlobalTheory.T.weylLattice_exists_cofactorTwist_dual O m ν hν hl) fun g hg => ?_
    have := GlobalTheory.T.weylLattice_exists_cofactorTwist_dual O m _ hν' hl' g hg
    rwa [hdd] at this

end GlobalTheory.ValCmp

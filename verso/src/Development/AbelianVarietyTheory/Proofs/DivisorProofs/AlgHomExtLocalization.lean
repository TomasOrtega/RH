import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BijectiveResidueCompEtaleHenselianStatement
open IsLocalRing

namespace GlobalTheory.IndEtaleHensel

/- English proof (translation)
Apply `AlgHom.coe_ringHom_injective` to reduce the goal to its premises. Apply `IsLocalization.ringHom_ext q.primeCompl` to reduce the goal to its premises. Conclude with `RingHom.ext fun a => DFunLike.congr_fun h a`.
-/
theorem algHom_ext_localization {R A P : Type} [CommRing R] [CommRing A] [CommRing P]
    [Algebra R A] [Algebra R P] (q : Ideal A) [q.IsPrime]
    (φ₁ φ₂ : Localization.AtPrime q →ₐ[R] P)
    (h : φ₁.comp (IsScalarTower.toAlgHom R A (Localization.AtPrime q)) =
      φ₂.comp (IsScalarTower.toAlgHom R A (Localization.AtPrime q))) : φ₁ = φ₂ := by
  apply AlgHom.coe_ringHom_injective
  apply IsLocalization.ringHom_ext q.primeCompl
  exact RingHom.ext fun a => DFunLike.congr_fun h a

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `φ₁ φ₂ hφ`. Establish `hc : φ₁.comp (e : X →ₐ[R] Y) = φ₂.comp (e : X →ₐ[R] Y)`. Apply `h.1` to reduce the goal to its premises. Simplify using `only at hφ ⊢`.

Rewrite using `[← AlgHom.comp_assoc, ← AlgHom.comp_assoc, hφ]`. Use extensionality with `y`. Use `DFunLike.congr_fun hc (e.symm y)` as an intermediate fact. Simplify using `using this`. Introduce `ψ`.

Take `⟨φ, hφ⟩` from `h.2 (ψ.comp (e : X →ₐ[R] Y))`. Use `⟨φ.comp (e.symm : Y →ₐ[R] X), ?_⟩` and prove the remaining obligations. Simplify using `only at hφ ⊢`. Rewrite using `[← AlgHom.comp_assoc, hφ]`. Use extensionality with `y`.

Simplify using the standard rewrite rules.
-/
theorem bijective_of_algEquiv {R X Y T : Type} [CommRing R] [CommRing X] [CommRing Y] [CommRing T]
    [Algebra R X] [Algebra R Y] [Algebra R T] [IsLocalRing T] (e : X ≃ₐ[R] Y)
    (h : Function.Bijective
      (fun φ : X →ₐ[R] T => (IsScalarTower.toAlgHom R T (ResidueField T)).comp φ)) :
    Function.Bijective
      (fun φ : Y →ₐ[R] T => (IsScalarTower.toAlgHom R T (ResidueField T)).comp φ) := by
  constructor
  · intro φ₁ φ₂ hφ
    have hc : φ₁.comp (e : X →ₐ[R] Y) = φ₂.comp (e : X →ₐ[R] Y) := by
      apply h.1
      simp only at hφ ⊢
      rw [← AlgHom.comp_assoc, ← AlgHom.comp_assoc, hφ]
    ext y
    have := DFunLike.congr_fun hc (e.symm y)
    simpa using this
  · intro ψ
    obtain ⟨φ, hφ⟩ := h.2 (ψ.comp (e : X →ₐ[R] Y))
    refine ⟨φ.comp (e.symm : Y →ₐ[R] X), ?_⟩
    simp only at hφ ⊢
    rw [← AlgHom.comp_assoc, hφ]
    ext y; simp

/- English proof (translation)
Use `set π := IsScalarTower.toAlgHom R T (ResidueField T)`. Use `set ι := IsScalarTower.toAlgHom R A (Localization.AtPrime q)`. Prove the components needed by the constructor for the conclusion. Introduce `φ₁ φ₂ hφ`. Apply `algHom_ext_localization q` to reduce the goal to its premises.

Apply `hA.1` to reduce the goal to its premises. Simplify using `only at hφ ⊢`. Rewrite using `[← AlgHom.comp_assoc, ← AlgHom.comp_assoc, hφ]`. Introduce `ψ`. Take `⟨φ, hφ⟩` from `hA.2 (ψ.comp ι)`.

Simplify using `only at hφ`. Establish `hu : ∀ y : q.primeCompl, IsUnit (φ y)`. Introduce `y`. Establish `h1 : IsUnit (ψ (algebraMap A (Localization.AtPrime q) y))` using `(IsLocalization.map_units (Localization.AtPrime q) y).map ψ`. Establish `h2 : π (φ y) = ψ (algebraMap A (Localization.AtPrime q) y)` using `DFunLike.congr_fun hφ (y : A)`.

Rewrite `h1` using `[← h2]`. Establish `h3 : π (φ y) = residue T (φ y)`. Simplify using `[π, IsScalarTower.toAlgHom_apply, ResidueField.algebraMap_eq]`. Rewrite `h1` using `[h3]`. Conclude with `(IsLocalRing.residue_ne_zero_iff_isUnit _).mp h1.ne_zero`.

Use `⟨IsLocalization.liftAlgHom (M := q.primeCompl) (S := Localization.AtPrime q) hu, ?_⟩` and prove the remaining obligations. Apply `algHom_ext_localization q` to reduce the goal to its premises. Use extensionality with `a`. Use `DFunLike.congr_fun hφ a` as an intermediate fact. Simplify using `only [AlgHom.comp_apply] at this ⊢`.

Rewrite using `[← this]`. Use `congr 1`. Simplify using `[ι, IsLocalization.liftAlgHom_apply, IsLocalization.lift_eq]`.
-/
theorem bijective_localization {R A T : Type} [CommRing R] [CommRing A] [CommRing T]
    [Algebra R A] [Algebra R T] [IsLocalRing T] (q : Ideal A) [q.IsPrime]
    (hA : Function.Bijective
      (fun φ : A →ₐ[R] T => (IsScalarTower.toAlgHom R T (ResidueField T)).comp φ)) :
    Function.Bijective (fun φ : Localization.AtPrime q →ₐ[R] T =>
      (IsScalarTower.toAlgHom R T (ResidueField T)).comp φ) := by
  set π := IsScalarTower.toAlgHom R T (ResidueField T)
  set ι := IsScalarTower.toAlgHom R A (Localization.AtPrime q)
  constructor
  · intro φ₁ φ₂ hφ
    apply algHom_ext_localization q
    apply hA.1
    simp only at hφ ⊢
    rw [← AlgHom.comp_assoc, ← AlgHom.comp_assoc, hφ]
  · intro ψ
    obtain ⟨φ, hφ⟩ := hA.2 (ψ.comp ι)
    simp only at hφ
    have hu : ∀ y : q.primeCompl, IsUnit (φ y) := by
      intro y
      have h1 : IsUnit (ψ (algebraMap A (Localization.AtPrime q) y)) :=
        (IsLocalization.map_units (Localization.AtPrime q) y).map ψ
      have h2 : π (φ y) = ψ (algebraMap A (Localization.AtPrime q) y) := DFunLike.congr_fun hφ (y : A)
      rw [← h2] at h1
      have h3 : π (φ y) = residue T (φ y) := by
        simp [π, IsScalarTower.toAlgHom_apply, ResidueField.algebraMap_eq]
      rw [h3] at h1
      exact (IsLocalRing.residue_ne_zero_iff_isUnit _).mp h1.ne_zero
    refine ⟨IsLocalization.liftAlgHom (M := q.primeCompl) (S := Localization.AtPrime q) hu, ?_⟩
    apply algHom_ext_localization q
    ext a
    have := DFunLike.congr_fun hφ a
    simp only [AlgHom.comp_apply] at this ⊢
    rw [← this]
    congr 1
    simp [ι, IsLocalization.liftAlgHom_apply, IsLocalization.lift_eq]

/- English proof (translation)
Introduce `R S T _ _ _ _ _ _ hS`. Take `⟨ι, _, _, _, Si, hmono, hcov, hloc⟩` from `hS`. Establish `hbij : ∀ i, Function.Bijective (fun φ : Si i →ₐ[R] T => (IsScalarTower.toAlgHom R T (ResidueField T)).comp φ)`. Introduce `i`. Take `⟨A, _, _, _, q, _, ⟨e⟩⟩` from `hloc i`.

Conclude with `bijective_of_algEquiv e (bijective_localization q (GlobalTheory.T.bijective_residue_comp_etale_henselian R A T))`. Establish `dir : Directed (· ≤ ·) Si` using `hmono.directed_le`. Establish `htop : (⊤ : Subalgebra R S) ≤ iSup Si` using `fun s _ => by`. Take `⟨i, hi⟩` from `hcov s`. Conclude with `le_iSup Si i hi`.

Prove the components needed by the constructor for the conclusion. Introduce `φ₁ φ₂ h`. Simplify using `only at h`. Use extensionality with `s`. Take `⟨i, hi⟩` from `hcov s`.

Establish `hc : φ₁.comp (Si i).val = φ₂.comp (Si i).val`. Apply `(hbij i).1` to reduce the goal to its premises. Simplify using `only`. Rewrite using `[← AlgHom.comp_assoc, ← AlgHom.comp_assoc, h]`. Conclude with `DFunLike.congr_fun hc ⟨s, hi⟩`.

Introduce `ψ choose f hf using fun i => (hbij i).2 (ψ.comp (Si i).val)`. Simplify using `only at hf`. Establish `compat : ∀ i j (h : Si i ≤ Si j), f i = (f j).comp (Subalgebra.inclusion h)`. Introduce `i j h`. Apply `(hbij i).1` to reduce the goal to its premises.

Simplify using `only`. Rewrite using `[hf i, ← AlgHom.comp_assoc, hf j]`. Use extensionality with `x`. Both sides reduce to the same expression. Use `⟨(Subalgebra.iSupLift Si dir f compat ⊤ htop).comp (Subalgebra.topEquiv.symm : S ≃ₐ[R] (⊤ : Subalgebra R S)).toAlgHom, ?_⟩` and prove the remaining obligations.

Use extensionality with `s`. Take `⟨i, hi⟩` from `hcov s`. Establish `h1` using `DFunLike.congr_fun (hf i) ⟨s, hi⟩`. Simplify using `only [AlgHom.comp_apply] at h1 ⊢`. Use `Eq.trans ?_ h1` and prove the remaining obligations.

Use `congr 1`. Conclude with `Subalgebra.iSupLift_of_mem (K := Si) (dir := dir) (f := f) (hf := compat) (T := ⊤) (hT := htop) ⟨s, trivial⟩ hi`.
-/
theorem bijective_residue_comp : ∀ (R S T : Type) [CommRing R] [CommRing S] [CommRing T] [Algebra R S] [Algebra R T] [HenselianLocalRing T], (∃ (ι : Type) (_ : Preorder ι) (_ : IsDirected ι (· ≤ ·)) (_ : Nonempty ι) (Si : ι → Subalgebra R S), Monotone Si ∧ (∀ s : S, ∃ i, s ∈ Si i) ∧ ∀ i, ∃ (A : Type) (_ : CommRing A) (_ : Algebra R A) (_ : Algebra.Etale R A) (q : Ideal A) (_ : q.IsPrime), Nonempty (Localization.AtPrime q ≃ₐ[R] Si i)) → Function.Bijective (fun φ : S →ₐ[R] T => (IsScalarTower.toAlgHom R T (ResidueField T)).comp φ) := by
  intro R S T _ _ _ _ _ _ hS
  obtain ⟨ι, _, _, _, Si, hmono, hcov, hloc⟩ := hS
  have hbij : ∀ i, Function.Bijective (fun φ : Si i →ₐ[R] T =>
      (IsScalarTower.toAlgHom R T (ResidueField T)).comp φ) := by
    intro i
    obtain ⟨A, _, _, _, q, _, ⟨e⟩⟩ := hloc i
    exact bijective_of_algEquiv e (bijective_localization q (GlobalTheory.T.bijective_residue_comp_etale_henselian R A T))
  have dir : Directed (· ≤ ·) Si := hmono.directed_le
  have htop : (⊤ : Subalgebra R S) ≤ iSup Si := fun s _ => by
    obtain ⟨i, hi⟩ := hcov s
    exact le_iSup Si i hi
  constructor
  · intro φ₁ φ₂ h
    simp only at h
    ext s
    obtain ⟨i, hi⟩ := hcov s
    have hc : φ₁.comp (Si i).val = φ₂.comp (Si i).val := by
      apply (hbij i).1
      simp only
      rw [← AlgHom.comp_assoc, ← AlgHom.comp_assoc, h]
    exact DFunLike.congr_fun hc ⟨s, hi⟩
  · intro ψ
    choose f hf using fun i => (hbij i).2 (ψ.comp (Si i).val)
    simp only at hf
    have compat : ∀ i j (h : Si i ≤ Si j), f i = (f j).comp (Subalgebra.inclusion h) := by
      intro i j h
      apply (hbij i).1
      simp only
      rw [hf i, ← AlgHom.comp_assoc, hf j]
      ext x; rfl
    refine ⟨(Subalgebra.iSupLift Si dir f compat ⊤ htop).comp
      (Subalgebra.topEquiv.symm : S ≃ₐ[R] (⊤ : Subalgebra R S)).toAlgHom, ?_⟩
    ext s
    obtain ⟨i, hi⟩ := hcov s
    have h1 := DFunLike.congr_fun (hf i) ⟨s, hi⟩
    simp only [AlgHom.comp_apply] at h1 ⊢
    refine Eq.trans ?_ h1
    congr 1
    exact Subalgebra.iSupLift_of_mem (K := Si) (dir := dir) (f := f) (hf := compat)
      (T := ⊤) (hT := htop) ⟨s, trivial⟩ hi

end GlobalTheory.IndEtaleHensel

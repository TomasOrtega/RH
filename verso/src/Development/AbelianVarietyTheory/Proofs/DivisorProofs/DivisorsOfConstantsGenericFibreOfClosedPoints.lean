import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DivConstClosedPts
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMaximalOverClosedPointClosedFibreStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSpecialisationToStrictlyHenselianStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StrictHenselisationEtaleOverPolynomialStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEtaleFactorOfIndEtAtPrimeStatement

open IsLocalRing Polynomial

noncomputable section

namespace GlobalTheory.VertUnits

/- English proof (translation)
Introduce `T E _ _ _ _ _ Q _ hQ`. Use `set I : Ideal (Polynomial T) := (maximalIdeal T).map (Polynomial.C : T →+* Polynomial T) with hI`. Establish `hIQ : I ≤ Q.comap (algebraMap (Polynomial T) E)` using `hQ.ge`. Set `f : Polynomial T ⧸ I →+* E ⧸ Q` to `Ideal.quotientMap Q (algebraMap (Polynomial T) E) hIQ`. Set `K` to `T ⧸ maximalIdeal T`.

Set `_ : Field K` to `Ideal.Quotient.field _`. Set `e : Polynomial K ≃+* Polynomial T ⧸ I` to `Ideal.polynomialQuotientEquivQuotientPolynomial (maximalIdeal T)`. Establish `: IsJacobsonRing (Polynomial T ⧸ I)` using `isJacobsonRing_of_surjective ⟨e.toRingHom, e.surjective⟩`. Establish `hnf : ¬ IsField (Polynomial T ⧸ I)` using `fun h => Polynomial.not_isField K (MulEquiv.isField h e.toMulEquiv)`. Establish `hft : f.FiniteType`.

Establish `h1 : ((Ideal.Quotient.mk Q).comp (algebraMap (Polynomial T) E)).FiniteType` using `(RingHom.FiniteType.of_surjective _ Ideal.Quotient.mk_surjective).comp (RingHom.finiteType_algebraMap.mpr inferInstance)`. Rewrite `h1` using `[← Ideal.quotientMap_comp_mk hIQ]`. Conclude with `RingHom.FiniteType.of_comp_finiteType h1`. Take `⟨m, hm⟩` from `Ideal.exists_maximal (E ⧸ Q)`. Establish `hcm : (m.comap f).IsMaximal`.

Set `_` to `Ideal.Quotient.field m`. Set `g : Polynomial T ⧸ I →+* (E ⧸ Q) ⧸ m` to `(Ideal.Quotient.mk m).comp f`. Establish `hgft : g.FiniteType` using `(RingHom.FiniteType.of_surjective _ Ideal.Quotient.mk_surjective).comp hft`. Establish `hgint : g.IsIntegral` using `(RingHom.finite_iff_finiteType_of_isJacobsonRing.mpr hgft).to_isIntegral`. Use `Ideal.isMaximal_comap_of_isIntegral_of_isMaximal' g hgint ⊥` as an intermediate fact.

Establish `heq : m.comap f = (⊥ : Ideal ((E ⧸ Q) ⧸ m)).comap g`. Use extensionality with `a`. Simplify using `[g, Ideal.Quotient.eq_zero_iff_mem]`. Rewrite using `[heq]`. Conclude with `this`.

Establish `hcm0 : m.comap f ≠ ⊥`. Introduce `h`. Rewrite `hcm` using `[h]`. Conclude with `hnf (Ring.isField_iff_maximal_bot.mpr hcm)`. Use `⟨m.comap (Ideal.Quotient.mk Q), Ideal.comap_isMaximal_of_surjective _ Ideal.Quotient.mk_surjective, fun x hx => ?_, ?_, ?_⟩` and prove the remaining obligations.

Simplify using `[Ideal.Quotient.eq_zero_iff_mem.mpr hx]`. Introduce `hy`. Apply `hcm0` to reduce the goal to its premises. Rewrite using `[eq_bot_iff]`. Introduce `a ha`.

Take `⟨p, rfl⟩` from `Ideal.Quotient.mk_surjective a`. Establish `hp : p ∈ (m.comap (Ideal.Quotient.mk Q)).comap (algebraMap (Polynomial T) E)`. Simplify `ha` using `[f, Ideal.quotientMap_mk]`. Rewrite `hp` using `[hy]`. Simplify `hp` using `[Ideal.Quotient.eq_zero_iff_mem]`.

Establish `hle : maximalIdeal T ≤ ((m.comap (Ideal.Quotient.mk Q)).comap (algebraMap (Polynomial T) E)).comap (Polynomial.C : T →+* Polynomial T)`. Introduce `t ht`. Simplify using `only [Ideal.mem_comap]`. Establish `h1 : Polynomial.C t ∈ I` using `Ideal.mem_map_of_mem _ ht`. Establish `h2 : algebraMap (Polynomial T) E (Polynomial.C t) ∈ Q` using `hIQ h1`.

Simplify using `[Ideal.Quotient.eq_zero_iff_mem.mpr h2]`. Establish `hp : (((m.comap (Ideal.Quotient.mk Q)).comap (algebraMap (Polynomial T) E)).comap (Polynomial.C : T →+* Polynomial T)).IsPrime`. Establish `: (m.comap (Ideal.Quotient.mk Q)).IsPrime` using `Ideal.comap_isPrime _ _`. Conclude with `Ideal.comap_isPrime _ _`. Conclude with `((maximalIdeal.isMaximal T).eq_of_le hp.ne_top hle).symm`.
-/
private theorem exists_maximal_over_closedPt : ∀ (T E : Type) [CommRing T] [IsLocalRing T] [CommRing E] [Algebra (Polynomial T) E]
    [Algebra.FiniteType (Polynomial T) E] (Q : Ideal E) [Q.IsPrime],
    Q.comap (algebraMap (Polynomial T) E) =
      (IsLocalRing.maximalIdeal T).map (Polynomial.C : T →+* Polynomial T) →
    ∃ y : Ideal E, y.IsMaximal ∧ Q ≤ y ∧
      y.comap (algebraMap (Polynomial T) E) ≠
        (IsLocalRing.maximalIdeal T).map (Polynomial.C : T →+* Polynomial T) ∧
      (y.comap (algebraMap (Polynomial T) E)).comap (Polynomial.C : T →+* Polynomial T) =
        IsLocalRing.maximalIdeal T := by
  intro T E _ _ _ _ _ Q _ hQ
  set I : Ideal (Polynomial T) := (maximalIdeal T).map (Polynomial.C : T →+* Polynomial T)
    with hI
  have hIQ : I ≤ Q.comap (algebraMap (Polynomial T) E) := hQ.ge
  let f : Polynomial T ⧸ I →+* E ⧸ Q := Ideal.quotientMap Q (algebraMap (Polynomial T) E) hIQ
  let K := T ⧸ maximalIdeal T
  let _ : Field K := Ideal.Quotient.field _
  let e : Polynomial K ≃+* Polynomial T ⧸ I :=
    Ideal.polynomialQuotientEquivQuotientPolynomial (maximalIdeal T)
  have : IsJacobsonRing (Polynomial T ⧸ I) :=
    isJacobsonRing_of_surjective ⟨e.toRingHom, e.surjective⟩
  have hnf : ¬ IsField (Polynomial T ⧸ I) := fun h =>
    Polynomial.not_isField K (MulEquiv.isField h e.toMulEquiv)
  have hft : f.FiniteType := by
    have h1 : ((Ideal.Quotient.mk Q).comp (algebraMap (Polynomial T) E)).FiniteType :=
      (RingHom.FiniteType.of_surjective _ Ideal.Quotient.mk_surjective).comp
        (RingHom.finiteType_algebraMap.mpr inferInstance)
    rw [← Ideal.quotientMap_comp_mk hIQ] at h1
    exact RingHom.FiniteType.of_comp_finiteType h1
  obtain ⟨m, hm⟩ := Ideal.exists_maximal (E ⧸ Q)
  have hcm : (m.comap f).IsMaximal := by
    let _ := Ideal.Quotient.field m
    let g : Polynomial T ⧸ I →+* (E ⧸ Q) ⧸ m := (Ideal.Quotient.mk m).comp f
    have hgft : g.FiniteType :=
      (RingHom.FiniteType.of_surjective _ Ideal.Quotient.mk_surjective).comp hft
    have hgint : g.IsIntegral :=
      (RingHom.finite_iff_finiteType_of_isJacobsonRing.mpr hgft).to_isIntegral
    have := Ideal.isMaximal_comap_of_isIntegral_of_isMaximal' g hgint ⊥
    have heq : m.comap f = (⊥ : Ideal ((E ⧸ Q) ⧸ m)).comap g := by
      ext a
      simp [g, Ideal.Quotient.eq_zero_iff_mem]
    rw [heq]
    exact this
  have hcm0 : m.comap f ≠ ⊥ := by
    intro h
    rw [h] at hcm
    exact hnf (Ring.isField_iff_maximal_bot.mpr hcm)
  refine ⟨m.comap (Ideal.Quotient.mk Q), Ideal.comap_isMaximal_of_surjective _
    Ideal.Quotient.mk_surjective, fun x hx => ?_, ?_, ?_⟩
  · simp [Ideal.Quotient.eq_zero_iff_mem.mpr hx]
  · intro hy
    apply hcm0
    rw [eq_bot_iff]
    intro a ha
    obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective a
    have hp : p ∈ (m.comap (Ideal.Quotient.mk Q)).comap (algebraMap (Polynomial T) E) := by
      simpa [f, Ideal.quotientMap_mk] using ha
    rw [hy] at hp
    simpa [Ideal.Quotient.eq_zero_iff_mem] using hp
  · have hle : maximalIdeal T ≤
        ((m.comap (Ideal.Quotient.mk Q)).comap (algebraMap (Polynomial T) E)).comap
          (Polynomial.C : T →+* Polynomial T) := by
      intro t ht
      simp only [Ideal.mem_comap]
      have h1 : Polynomial.C t ∈ I := Ideal.mem_map_of_mem _ ht
      have h2 : algebraMap (Polynomial T) E (Polynomial.C t) ∈ Q := hIQ h1
      simp [Ideal.Quotient.eq_zero_iff_mem.mpr h2]
    have hp : (((m.comap (Ideal.Quotient.mk Q)).comap (algebraMap (Polynomial T) E)).comap
        (Polynomial.C : T →+* Polynomial T)).IsPrime := by
      have : (m.comap (Ideal.Quotient.mk Q)).IsPrime := Ideal.comap_isPrime _ _
      exact Ideal.comap_isPrime _ _
    exact ((maximalIdeal.isMaximal T).eq_of_le hp.ne_top hle).symm

/- English proof (translation)
Set `H : TensorProduct R K A →ₐ[K] L` to `Algebra.TensorProduct.lift (Algebra.ofId K L) h (fun _ _ => Commute.all _ _)`. Set `f` to `Ideal.kerLiftAlg H`. Establish `hf : Function.Injective f` using `Ideal.kerLiftAlg_injective H`. Establish `: (RingHom.ker H).IsPrime` using `RingHom.ker_isPrime (H : TensorProduct R K A →+* L)`. Establish `: Algebra.Etale K (TensorProduct R K A)` using `inferInstance`.

Establish `: Algebra.EssFiniteType K (TensorProduct R K A)` using `inferInstance`. Establish `hx : f (Ideal.Quotient.mk _ (Algebra.TensorProduct.includeRight a)) = h a`. Simplify using `[f, H]`. Rewrite using `[← hx]`. Use `show (minpoly K (f _)).Separable`.

Rewrite using `[minpoly.algHom_eq f hf]`. Conclude with `Algebra.IsSeparable.isSeparable K _`.
-/
private theorem isSeparable_apply_of_etale (R A K L : Type) [CommRing R] [CommRing A] [Field K]
    [Field L] [Algebra R A] [Algebra.Etale R A] [Algebra R K] [Algebra K L] [Algebra R L]
    [IsScalarTower R K L] (h : A →ₐ[R] L) (a : A) : IsSeparable K (h a) := by
  let H : TensorProduct R K A →ₐ[K] L :=
    Algebra.TensorProduct.lift (Algebra.ofId K L) h (fun _ _ => Commute.all _ _)
  let f := Ideal.kerLiftAlg H
  have hf : Function.Injective f := Ideal.kerLiftAlg_injective H
  have : (RingHom.ker H).IsPrime := RingHom.ker_isPrime (H : TensorProduct R K A →+* L)
  have : Algebra.Etale K (TensorProduct R K A) := inferInstance
  have : Algebra.EssFiniteType K (TensorProduct R K A) := inferInstance
  have hx : f (Ideal.Quotient.mk _ (Algebra.TensorProduct.includeRight a)) = h a := by
    simp [f, H]
  rw [← hx]
  show (minpoly K (f _)).Separable
  rw [minpoly.algHom_eq f hf]
  exact Algebra.IsSeparable.isSeparable K _

/- English proof (translation)
Introduce `R S O _ _ _ _ _ _ _ _ Q y _ _ hQy hSy hOQ hflat hpieces`. Establish `: (IsLocalRing.maximalIdeal S).LiesOver y` using `⟨hSy.symm⟩`. Take `⟨𝔭, -, _, h𝔭⟩` from `Ideal.exists_ideal_le_liesOver_of_le (p := Q) (q := y) (IsLocalRing.maximalIdeal S) hQy`. Establish `h𝔭Q : Q = 𝔭.comap (algebraMap R S)` using `h𝔭.over`. Set `F` to `IsLocalRing.ResidueField O`.

Establish `hF : Q ≤ RingHom.ker (algebraMap R F)` using `fun x hx => by`. Rewrite using `[RingHom.mem_ker, IsScalarTower.algebraMap_apply R O F, IsLocalRing.ResidueField.algebraMap_eq, IsLocalRing.residue_eq_zero_iff]`. Rewrite `hx` using `[← hOQ]`. Conclude with `hx`. Establish `hF' : Q.primeCompl ≤ (IsUnit.submonoid F).comap (algebraMap R F)` using `fun x hx => by`.

Simplify using `only [Submonoid.mem_comap, IsUnit.mem_submonoid_iff]`. Rewrite using `[isUnit_iff_ne_zero, IsScalarTower.algebraMap_apply R O F, ne_eq, IsLocalRing.ResidueField.algebraMap_eq, IsLocalRing.residue_eq_zero_iff]`. Introduce `h`. Apply `hx` to reduce the goal to its premises. Rewrite using `[← hOQ]`.

Conclude with `h`. Set `κQ` to `Q.ResidueField`. Set `κ𝔭` to `𝔭.ResidueField`. Set `_ : Algebra κQ F` to `(Ideal.ResidueField.lift Q (algebraMap R F) hF hF').toAlgebra`. Establish `hRQF : IsScalarTower R κQ F` using `IsScalarTower.of_algebraMap_eq (fun r => (Ideal.ResidueField.lift_algebraMap Q (algebraMap R F) hF hF' r).symm)`.

Set `_ : Algebra κQ κ𝔭` to `(Ideal.ResidueField.map Q 𝔭 (algebraMap R S) h𝔭Q).toAlgebra`. Establish `hRQP : IsScalarTower R κQ κ𝔭` using `IsScalarTower.of_algebraMap_eq (fun r => by`. Express the relevant statement in the definitionally equal form `_ = Ideal.ResidueField.map Q 𝔭 (algebraMap R S) h𝔭Q (algebraMap R κQ r)`. Rewrite using `[Ideal.ResidueField.map_algebraMap, ← IsScalarTower.algebraMap_apply])`. Establish `hsepS : ∀ s : S, algebraMap S κ𝔭 s ∈ separableClosure κQ κ𝔭`.

Introduce `s`. Take `⟨ι, _, _, _, Si, -, hcov, hpc⟩` from `hpieces`. Take `⟨i, hi⟩` from `hcov s`. Take `⟨A, _, _, _, q, _, ⟨e⟩⟩` from `hpc i`. Set `g : Localization.AtPrime q →ₐ[R] κ𝔭` to `(IsScalarTower.toAlgHom R S κ𝔭).comp ((Si i).val.comp e.toAlgHom)`.

Set `h : A →ₐ[R] κ𝔭` to `g.comp (IsScalarTower.toAlgHom R A (Localization.AtPrime q))`. Take `⟨z, hz⟩` from `e.surjective ⟨s, hi⟩`. Establish `hgz : g z = algebraMap S κ𝔭 s` using `by simp [g, hz]`. Take `⟨⟨a, t⟩, hat⟩` from `IsLocalization.mk'_surjective (M := q.primeCompl) (S := Localization.AtPrime q) z`. Establish `hat' : IsLocalization.mk' (Localization.AtPrime q) a t = z` using `hat`.

Rewrite `hgz` using `[← hat']`. Establish `hu : IsUnit (h t)` using `(IsLocalization.map_units (Localization.AtPrime q) t).map g`. Establish `hgz' : g (IsLocalization.mk' (Localization.AtPrime q) a t) = h a * (h t)⁻¹`. Rewrite using `[eq_mul_inv_iff_mul_eq₀ hu.ne_zero]`. Express the relevant statement in the definitionally equal form `_ = g (algebraMap A _ a)`.

Rewrite using `[← IsLocalization.mk'_spec (Localization.AtPrime q) a t, map_mul]`. Both sides reduce to the same expression. Rewrite using `[← hgz, hgz']`. Conclude with `(separableClosure κQ κ𝔭).mul_mem (mem_separableClosure_iff.mpr (isSeparable_apply_of_etale R A κQ κ𝔭 h a)) ((separableClosure κQ κ𝔭).inv_mem (mem_separableClosure_iff.mpr (isSeparable_apply_of_etale R A κQ κ𝔭 h t)))`. Establish `hsep : Algebra.IsSeparable κQ κ𝔭` using `⟨fun x => by`.

Take `⟨u, v, -, rfl⟩` from `IsFractionRing.div_surjective (S ⧸ 𝔭) x`. Take `⟨u, rfl⟩` from `Ideal.Quotient.mk_surjective u`. Take `⟨v, rfl⟩` from `Ideal.Quotient.mk_surjective v`. Rewrite using `[Ideal.algebraMap_quotient_residueField_mk, Ideal.algebraMap_quotient_residueField_mk]`. Conclude with `mem_separableClosure_iff.mp ((separableClosure κQ κ𝔭).div_mem (hsepS u) (hsepS v))⟩`.

Set `ι : κ𝔭 →ₐ[κQ] F` to `IsSepClosed.lift (K := κQ) (L := κ𝔭) (M := F)`. Set `χ : S →ₐ[R] F` to `{ toRingHom := (ι : κ𝔭 →+* F).comp (algebraMap S κ𝔭) commutes' := fun r => by show ι (algebraMap S κ𝔭 (algebraMap R S r)) = algebraMap R F r`. Rewrite using `[← IsScalarTower.algebraMap_apply R S κ𝔭, IsScalarTower.algebraMap_apply R κQ κ𝔭, ι.commutes, ← IsScalarTower.algebraMap_apply R κQ F] }`. Take `⟨φ, -⟩` from `(GlobalTheory.IndEtaleHensel.bijective_residue_comp R S O hpieces).2 χ`. Conclude with `⟨φ⟩`.
-/
private theorem specialisation_map : ∀ (R S O : Type) [CommRing R] [CommRing S] [IsLocalRing S] [CommRing O]
    [HenselianLocalRing O] [IsSepClosed (IsLocalRing.ResidueField O)] [Algebra R S] [Algebra R O]
    (Q y : Ideal R) [Q.IsPrime] [y.IsPrime], Q ≤ y →
    (IsLocalRing.maximalIdeal S).comap (algebraMap R S) = y →
    (IsLocalRing.maximalIdeal O).comap (algebraMap R O) = Q →
    Module.Flat R S → GlobalTheory.LocAcyc.LocPiecesEtale R S → Nonempty (S →ₐ[R] O) := by
  intro R S O _ _ _ _ _ _ _ _ Q y _ _ hQy hSy hOQ hflat hpieces
  have : (IsLocalRing.maximalIdeal S).LiesOver y := ⟨hSy.symm⟩
  obtain ⟨𝔭, -, _, h𝔭⟩ := Ideal.exists_ideal_le_liesOver_of_le (p := Q) (q := y)
    (IsLocalRing.maximalIdeal S) hQy
  have h𝔭Q : Q = 𝔭.comap (algebraMap R S) := h𝔭.over
  let F := IsLocalRing.ResidueField O
  have hF : Q ≤ RingHom.ker (algebraMap R F) := fun x hx => by
    rw [RingHom.mem_ker, IsScalarTower.algebraMap_apply R O F,
      IsLocalRing.ResidueField.algebraMap_eq, IsLocalRing.residue_eq_zero_iff]
    rw [← hOQ] at hx
    exact hx
  have hF' : Q.primeCompl ≤ (IsUnit.submonoid F).comap (algebraMap R F) := fun x hx => by
    simp only [Submonoid.mem_comap, IsUnit.mem_submonoid_iff]
    rw [isUnit_iff_ne_zero, IsScalarTower.algebraMap_apply R O F, ne_eq,
      IsLocalRing.ResidueField.algebraMap_eq, IsLocalRing.residue_eq_zero_iff]
    intro h
    apply hx
    rw [← hOQ]
    exact h
  let κQ := Q.ResidueField
  let κ𝔭 := 𝔭.ResidueField
  let _ : Algebra κQ F := (Ideal.ResidueField.lift Q (algebraMap R F) hF hF').toAlgebra
  have hRQF : IsScalarTower R κQ F := IsScalarTower.of_algebraMap_eq (fun r =>
    (Ideal.ResidueField.lift_algebraMap Q (algebraMap R F) hF hF' r).symm)
  let _ : Algebra κQ κ𝔭 := (Ideal.ResidueField.map Q 𝔭 (algebraMap R S) h𝔭Q).toAlgebra
  have hRQP : IsScalarTower R κQ κ𝔭 := IsScalarTower.of_algebraMap_eq (fun r => by
    change _ = Ideal.ResidueField.map Q 𝔭 (algebraMap R S) h𝔭Q (algebraMap R κQ r)
    rw [Ideal.ResidueField.map_algebraMap, ← IsScalarTower.algebraMap_apply])
  have hsepS : ∀ s : S, algebraMap S κ𝔭 s ∈ separableClosure κQ κ𝔭 := by
    intro s
    obtain ⟨ι, _, _, _, Si, -, hcov, hpc⟩ := hpieces
    obtain ⟨i, hi⟩ := hcov s
    obtain ⟨A, _, _, _, q, _, ⟨e⟩⟩ := hpc i
    let g : Localization.AtPrime q →ₐ[R] κ𝔭 :=
      (IsScalarTower.toAlgHom R S κ𝔭).comp ((Si i).val.comp e.toAlgHom)
    let h : A →ₐ[R] κ𝔭 := g.comp (IsScalarTower.toAlgHom R A (Localization.AtPrime q))
    obtain ⟨z, hz⟩ := e.surjective ⟨s, hi⟩
    have hgz : g z = algebraMap S κ𝔭 s := by simp [g, hz]
    obtain ⟨⟨a, t⟩, hat⟩ := IsLocalization.mk'_surjective (M := q.primeCompl)
      (S := Localization.AtPrime q) z
    have hat' : IsLocalization.mk' (Localization.AtPrime q) a t = z := hat
    rw [← hat'] at hgz
    have hu : IsUnit (h t) := (IsLocalization.map_units (Localization.AtPrime q) t).map g
    have hgz' : g (IsLocalization.mk' (Localization.AtPrime q) a t) = h a * (h t)⁻¹ := by
      rw [eq_mul_inv_iff_mul_eq₀ hu.ne_zero]
      change _ = g (algebraMap A _ a)
      rw [← IsLocalization.mk'_spec (Localization.AtPrime q) a t, map_mul]
      rfl
    rw [← hgz, hgz']
    exact (separableClosure κQ κ𝔭).mul_mem
      (mem_separableClosure_iff.mpr (isSeparable_apply_of_etale R A κQ κ𝔭 h a))
      ((separableClosure κQ κ𝔭).inv_mem
        (mem_separableClosure_iff.mpr (isSeparable_apply_of_etale R A κQ κ𝔭 h t)))
  have hsep : Algebra.IsSeparable κQ κ𝔭 := ⟨fun x => by
    obtain ⟨u, v, -, rfl⟩ := IsFractionRing.div_surjective (S ⧸ 𝔭) x
    obtain ⟨u, rfl⟩ := Ideal.Quotient.mk_surjective u
    obtain ⟨v, rfl⟩ := Ideal.Quotient.mk_surjective v
    rw [Ideal.algebraMap_quotient_residueField_mk, Ideal.algebraMap_quotient_residueField_mk]
    exact mem_separableClosure_iff.mp ((separableClosure κQ κ𝔭).div_mem (hsepS u) (hsepS v))⟩
  let ι : κ𝔭 →ₐ[κQ] F := IsSepClosed.lift (K := κQ) (L := κ𝔭) (M := F)
  let χ : S →ₐ[R] F :=
    { toRingHom := (ι : κ𝔭 →+* F).comp (algebraMap S κ𝔭)
      commutes' := fun r => by
        show ι (algebraMap S κ𝔭 (algebraMap R S r)) = algebraMap R F r
        rw [← IsScalarTower.algebraMap_apply R S κ𝔭, IsScalarTower.algebraMap_apply R κQ κ𝔭,
          ι.commutes, ← IsScalarTower.algebraMap_apply R κQ F] }
  obtain ⟨φ, -⟩ := (GlobalTheory.IndEtaleHensel.bijective_residue_comp R S O hpieces).2 χ
  exact ⟨φ⟩

/- English proof (translation)
Set `L` to `Localization.AtPrime y`. Set `Ω` to `SeparableClosure (IsLocalRing.ResidueField L)`. Take `⟨S, _, _, _, hloc, hsep, hflat, -, -, hpieces⟩` from `GlobalTheory.exists_strictHenselisation L Ω`. Establish `: IsSepClosed (IsLocalRing.ResidueField S)` using `hsep`. Set `_ : Algebra E S` to `((algebraMap L S).comp (algebraMap E L)).toAlgebra`.

Establish `hELS : IsScalarTower E L S` using `IsScalarTower.of_algebraMap_eq (fun _ => rfl)`. Set `_ : Algebra (Polynomial T) S` to `((algebraMap E S).comp (algebraMap (Polynomial T) E)).toAlgebra`. Set `_ : Algebra T S` to `((algebraMap E S).comp (algebraMap T E)).toAlgebra`. Establish `hTES : IsScalarTower T E S` using `IsScalarTower.of_algebraMap_eq (fun _ => rfl)`. Establish `hPES : IsScalarTower (Polynomial T) E S` using `IsScalarTower.of_algebraMap_eq (fun _ => rfl)`.

Establish `hTPS : IsScalarTower T (Polynomial T) S` using `IsScalarTower.of_algebraMap_eq (fun x => by`. Express the relevant statement in the definitionally equal form `algebraMap E S (algebraMap T E x) = algebraMap E S (algebraMap (Polynomial T) E (algebraMap T (Polynomial T) x))`. Rewrite using `[IsScalarTower.algebraMap_apply T (Polynomial T) E x])`. Establish `hPLS : IsScalarTower (Polynomial T) L S` using `IsScalarTower.of_algebraMap_eq (fun x => by`. Rewrite using `[IsScalarTower.algebraMap_apply (Polynomial T) E L x]`.

Use the proof step `rfl)`. Establish `hmax : (IsLocalRing.maximalIdeal S).comap (algebraMap E S) = y`. Rewrite using `[IsScalarTower.algebraMap_eq E L S, ← Ideal.comap_comap, IsLocalRing.maximalIdeal_comap (algebraMap L S)]`. Conclude with `IsLocalization.AtPrime.under_maximalIdeal L y`. Establish `hflatE : Module.Flat E S` using `Module.Flat.trans E L S`.

Establish `hLE : ∃ (ι : Type) (_ : Preorder ι) (_ : IsDirected ι (· ≤ ·)) (_ : Nonempty ι) (Si : ι → Subalgebra E L), Monotone Si ∧ (∀ s : L, ∃ i, s ∈ Si i) ∧ ∀ i, ∃ (A : Type) (_ : CommRing A) (_ : Algebra E A) (_ : Algebra.Etale E A) (q : Ideal A) (_ : q.IsPrime), Nonempty (Localization.A …` using `⟨Unit, inferInstance, inferInstance, inferInstance, fun _ => ⊤, monotone_const, fun _ => ⟨(), Algebra.mem_top⟩, fun _ => ⟨E, inferInstance, inferInstance, inferInstance, y, inferInstance, ⟨Subalgebra.topEquiv.symm⟩⟩⟩`. Establish `hLP : ∃ (ι : Type) (_ : Preorder ι) (_ : IsDirected ι (· ≤ ·)) (_ : Nonempty ι) (Si : ι → Subalgebra (Polynomial T) L), Monotone Si ∧ (∀ s : L, ∃ i, s ∈ Si i) ∧ ∀ i, ∃ (A : Type) (_ : CommRing A) (_ : Algebra (Polynomial T) A) (_ : Algebra.Etale (Polynomial T) A) (q : Ideal A) (_ …` using `⟨Unit, inferInstance, inferInstance, inferInstance, fun _ => ⊤, monotone_const, fun _ => ⟨(), Algebra.mem_top⟩, fun _ => ⟨E, inferInstance, inferInstance, inferInstance, y, inferInstance, ⟨Subalgebra.topEquiv.symm⟩⟩⟩`. Establish `hpE : GlobalTheory.LocAcyc.LocPiecesEtale E S` using `GlobalTheory.indEtale_localPieces_trans E L S hLE hpieces`. Take `⟨P, _, φ, hφ, hsh⟩` from `GlobalTheory.StrictHensUnion.isStrictHenselisation_of_directed_union T S (GlobalTheory.indEtale_localPieces_trans (Polynomial T) L S hLP hpieces)`. Establish `hP : P = y.comap (algebraMap (Polynomial T) E)`.

Establish `: IsLocalHom φ` using `hsh.2.2.1`. Rewrite using `[← hmax, Ideal.comap_comap, ← IsScalarTower.algebraMap_eq, ← hφ, ← Ideal.comap_comap, IsLocalRing.maximalIdeal_comap φ]`. Conclude with `(IsLocalization.AtPrime.under_maximalIdeal (Localization.AtPrime P) P).symm`. Substitute `hP` using the available equality. Conclude with `⟨S, inferInstance, inferInstance, inferInstance, inferInstance, hTES, inferInstance, hTPS, hPES, hmax, hflatE, hpE, φ, hφ, hsh⟩`.
-/
private theorem sh_at {T E : Type} [CommRing T] [IsDomain T] [IsLocalRing T] [CommRing E]
    [Algebra (Polynomial T) E] [Algebra T E] [IsScalarTower T (Polynomial T) E]
    [Algebra.Etale (Polynomial T) E] (y : Ideal E) [y.IsPrime] :
    ∃ (S : Type) (_ : CommRing S) (_ : IsLocalRing S) (_ : Algebra E S) (_ : Algebra T S)
      (_ : IsScalarTower T E S) (_ : Algebra (Polynomial T) S) (_ : IsScalarTower T (Polynomial T) S)
      (_ : IsScalarTower (Polynomial T) E S),
      (IsLocalRing.maximalIdeal S).comap (algebraMap E S) = y ∧ Module.Flat E S ∧
      GlobalTheory.LocAcyc.LocPiecesEtale E S ∧
      ∃ φ : Localization.AtPrime (y.comap (algebraMap (Polynomial T) E)) →+* S,
        φ.comp (algebraMap (Polynomial T) _) = algebraMap (Polynomial T) S ∧
        GlobalTheory.IndefiniteRowSideFullHecke.ProjectiveSpaceOverSpec.IsStrictHenselisation φ := by
  let L := Localization.AtPrime y
  let Ω := SeparableClosure (IsLocalRing.ResidueField L)
  obtain ⟨S, _, _, _, hloc, hsep, hflat, -, -, hpieces⟩ := GlobalTheory.exists_strictHenselisation L Ω
  have : IsSepClosed (IsLocalRing.ResidueField S) := hsep
  let _ : Algebra E S := ((algebraMap L S).comp (algebraMap E L)).toAlgebra
  have hELS : IsScalarTower E L S := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  let _ : Algebra (Polynomial T) S :=
    ((algebraMap E S).comp (algebraMap (Polynomial T) E)).toAlgebra
  let _ : Algebra T S := ((algebraMap E S).comp (algebraMap T E)).toAlgebra
  have hTES : IsScalarTower T E S := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  have hPES : IsScalarTower (Polynomial T) E S := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  have hTPS : IsScalarTower T (Polynomial T) S := IsScalarTower.of_algebraMap_eq (fun x => by
    change algebraMap E S (algebraMap T E x) =
      algebraMap E S (algebraMap (Polynomial T) E (algebraMap T (Polynomial T) x))
    rw [IsScalarTower.algebraMap_apply T (Polynomial T) E x])
  have hPLS : IsScalarTower (Polynomial T) L S := IsScalarTower.of_algebraMap_eq (fun x => by
    rw [IsScalarTower.algebraMap_apply (Polynomial T) E L x]
    rfl)
  have hmax : (IsLocalRing.maximalIdeal S).comap (algebraMap E S) = y := by
    rw [IsScalarTower.algebraMap_eq E L S, ← Ideal.comap_comap,
      IsLocalRing.maximalIdeal_comap (algebraMap L S)]
    exact IsLocalization.AtPrime.under_maximalIdeal L y
  have hflatE : Module.Flat E S := Module.Flat.trans E L S
  have hLE : ∃ (ι : Type) (_ : Preorder ι) (_ : IsDirected ι (· ≤ ·)) (_ : Nonempty ι)
      (Si : ι → Subalgebra E L), Monotone Si ∧ (∀ s : L, ∃ i, s ∈ Si i) ∧
      ∀ i, ∃ (A : Type) (_ : CommRing A) (_ : Algebra E A) (_ : Algebra.Etale E A) (q : Ideal A)
        (_ : q.IsPrime), Nonempty (Localization.AtPrime q ≃ₐ[E] Si i) :=
    ⟨Unit, inferInstance, inferInstance, inferInstance, fun _ => ⊤, monotone_const,
      fun _ => ⟨(), Algebra.mem_top⟩,
      fun _ => ⟨E, inferInstance, inferInstance, inferInstance, y, inferInstance,
        ⟨Subalgebra.topEquiv.symm⟩⟩⟩
  have hLP : ∃ (ι : Type) (_ : Preorder ι) (_ : IsDirected ι (· ≤ ·)) (_ : Nonempty ι)
      (Si : ι → Subalgebra (Polynomial T) L), Monotone Si ∧ (∀ s : L, ∃ i, s ∈ Si i) ∧
      ∀ i, ∃ (A : Type) (_ : CommRing A) (_ : Algebra (Polynomial T) A)
        (_ : Algebra.Etale (Polynomial T) A) (q : Ideal A)
        (_ : q.IsPrime), Nonempty (Localization.AtPrime q ≃ₐ[Polynomial T] Si i) :=
    ⟨Unit, inferInstance, inferInstance, inferInstance, fun _ => ⊤, monotone_const,
      fun _ => ⟨(), Algebra.mem_top⟩,
      fun _ => ⟨E, inferInstance, inferInstance, inferInstance, y, inferInstance,
        ⟨Subalgebra.topEquiv.symm⟩⟩⟩
  have hpE : GlobalTheory.LocAcyc.LocPiecesEtale E S := GlobalTheory.indEtale_localPieces_trans E L S hLE hpieces
  obtain ⟨P, _, φ, hφ, hsh⟩ := GlobalTheory.StrictHensUnion.isStrictHenselisation_of_directed_union T S
    (GlobalTheory.indEtale_localPieces_trans (Polynomial T) L S hLP hpieces)
  have hP : P = y.comap (algebraMap (Polynomial T) E) := by
    have : IsLocalHom φ := hsh.2.2.1
    rw [← hmax, Ideal.comap_comap, ← IsScalarTower.algebraMap_eq, ← hφ, ← Ideal.comap_comap,
      IsLocalRing.maximalIdeal_comap φ]
    exact (IsLocalization.AtPrime.under_maximalIdeal (Localization.AtPrime P) P).symm
  subst hP
  exact ⟨S, inferInstance, inferInstance, inferInstance, inferInstance, hTES, inferInstance, hTPS,
    hPES, hmax, hflatE, hpE, φ, hφ, hsh⟩

/- English proof (translation)
Introduce `T O _ _ _ _ _ P _ φ hφ hind b c s hbc`. Set `r : MvPolynomial (Fin 2) (Polynomial T)` to `MvPolynomial.X 0 * MvPolynomial.X 1 - MvPolynomial.C (Polynomial.C s)`. Set `Z` to `MvPolynomial (Fin 2) (Polynomial T) ⧸ Ideal.span {r}`. Establish `: Algebra.FinitePresentation (Polynomial T) Z` using `Algebra.FinitePresentation.quotient (Submodule.fg_span_singleton r)`. Set `g0 : MvPolynomial (Fin 2) (Polynomial T) →ₐ[Polynomial T] O` to `MvPolynomial.aeval ![b, c]`.

Establish `hg0 : ∀ a ∈ Ideal.span {r}, g0 a = 0`. Introduce `a ha`. Take `⟨q, rfl⟩` from `Ideal.mem_span_singleton'.mp ha`. Simplify using `only [g0, r, map_mul, map_sub, MvPolynomial.aeval_X, MvPolynomial.aeval_C, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one, hbc, IsScalarTower.algebraMap_apply T (Polynomial T) O s, Polynomial.algebraMap_eq, sub_self, mul_zero]`. Set `gZ : Z →ₐ[Polynomial T] O` to `Ideal.Quotient.liftₐ _ g0 hg0`.

Take `⟨W, _, _, _, u, v, huv⟩` from `GlobalTheory.T.exists_etale_factorization_of_isIndEtale (Polynomial T) O P φ hφ hind Z gZ`. Set `_ : Algebra T W` to `((algebraMap (Polynomial T) W).comp (algebraMap T (Polynomial T))).toAlgebra`. Establish `hW : IsScalarTower T (Polynomial T) W` using `IsScalarTower.of_algebraMap_eq (fun _ => rfl)`. Set `x₀ : Z` to `Ideal.Quotient.mk _ (MvPolynomial.X 0)`. Set `x₁ : Z` to `Ideal.Quotient.mk _ (MvPolynomial.X 1)`.

Establish `hv : ∀ z : Z, v (u z) = gZ z` using `fun z => by rw [← AlgHom.comp_apply, huv]`. Use `⟨W, inferInstance, inferInstance, inferInstance, hW, inferInstance, v, u x₀, u x₁, ?_, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[hv]`. Express the relevant statement in the definitionally equal form `g0 (MvPolynomial.X 0) = b`. Simplify using `[g0]`.

Rewrite using `[hv]`. Express the relevant statement in the definitionally equal form `g0 (MvPolynomial.X 1) = c`. Simplify using `[g0]`. Establish `hx : x₀ * x₁ = algebraMap (Polynomial T) Z (Polynomial.C s)`. Rewrite using `[← Ideal.Quotient.mk_algebraMap, ← map_mul]`.

Use `Ideal.Quotient.eq.mpr (Ideal.subset_span ?_)` and prove the remaining obligations. Rewrite using `[Set.mem_singleton_iff, MvPolynomial.algebraMap_eq]`. Rewrite using `[← map_mul, hx, u.commutes]`. Both sides reduce to the same expression.
-/
private theorem stage : ∀ (T O : Type) [CommRing T] [CommRing O] [Algebra T O]
    [Algebra (Polynomial T) O] [IsScalarTower T (Polynomial T) O]
    (P : Ideal (Polynomial T)) [P.IsPrime] (φ : Localization.AtPrime P →+* O),
    φ.comp (algebraMap (Polynomial T) _) = algebraMap (Polynomial T) O →
    GlobalTheory.IndefiniteRowSideFullHecke.ProjectiveSpaceOverSpec.IsIndEtale φ →
    ∀ (b c : O) (s : T), b * c = algebraMap T O s →
    ∃ (E : Type) (_ : CommRing E) (_ : Algebra (Polynomial T) E) (_ : Algebra T E)
      (_ : IsScalarTower T (Polynomial T) E) (_ : Algebra.Etale (Polynomial T) E)
      (ψ : E →ₐ[Polynomial T] O) (g g' : E),
      ψ g = b ∧ ψ g' = c ∧ g * g' = algebraMap T E s := by
  intro T O _ _ _ _ _ P _ φ hφ hind b c s hbc
  let r : MvPolynomial (Fin 2) (Polynomial T) :=
    MvPolynomial.X 0 * MvPolynomial.X 1 - MvPolynomial.C (Polynomial.C s)
  let Z := MvPolynomial (Fin 2) (Polynomial T) ⧸ Ideal.span {r}
  have : Algebra.FinitePresentation (Polynomial T) Z :=
    Algebra.FinitePresentation.quotient (Submodule.fg_span_singleton r)
  let g0 : MvPolynomial (Fin 2) (Polynomial T) →ₐ[Polynomial T] O := MvPolynomial.aeval ![b, c]
  have hg0 : ∀ a ∈ Ideal.span {r}, g0 a = 0 := by
    intro a ha
    obtain ⟨q, rfl⟩ := Ideal.mem_span_singleton'.mp ha
    simp only [g0, r, map_mul, map_sub, MvPolynomial.aeval_X, MvPolynomial.aeval_C,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one, hbc,
      IsScalarTower.algebraMap_apply T (Polynomial T) O s, Polynomial.algebraMap_eq, sub_self,
      mul_zero]
  let gZ : Z →ₐ[Polynomial T] O := Ideal.Quotient.liftₐ _ g0 hg0
  obtain ⟨W, _, _, _, u, v, huv⟩ := GlobalTheory.T.exists_etale_factorization_of_isIndEtale (Polynomial T) O P φ hφ hind Z gZ
  let _ : Algebra T W := ((algebraMap (Polynomial T) W).comp (algebraMap T (Polynomial T))).toAlgebra
  have hW : IsScalarTower T (Polynomial T) W := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  let x₀ : Z := Ideal.Quotient.mk _ (MvPolynomial.X 0)
  let x₁ : Z := Ideal.Quotient.mk _ (MvPolynomial.X 1)
  have hv : ∀ z : Z, v (u z) = gZ z := fun z => by rw [← AlgHom.comp_apply, huv]
  refine ⟨W, inferInstance, inferInstance, inferInstance, hW, inferInstance, v, u x₀, u x₁,
    ?_, ?_, ?_⟩
  · rw [hv]
    change g0 (MvPolynomial.X 0) = b
    simp [g0]
  · rw [hv]
    change g0 (MvPolynomial.X 1) = c
    simp [g0]
  · have hx : x₀ * x₁ = algebraMap (Polynomial T) Z (Polynomial.C s) := by
      rw [← Ideal.Quotient.mk_algebraMap, ← map_mul]
      refine Ideal.Quotient.eq.mpr (Ideal.subset_span ?_)
      rw [Set.mem_singleton_iff, MvPolynomial.algebraMap_eq]
    rw [← map_mul, hx, u.commutes]
    rfl

/- English proof (translation)
Introduce `hcl T O _ _ _ _ _ _ _ _ hT P _ φ hφ hsh hPm hPgen b c s hs hbc`. Take `⟨hHen, hSep, hloc, hind⟩` from `hsh`. Take `⟨E, _, _, _, _, _, ψ, g, g', hg, hg', hgg⟩` from `stage T O P φ hφ hind b c s hbc`. Set `_ : Algebra E O` to `ψ.toRingHom.toAlgebra`. Establish `hEO : ∀ e : E, algebraMap E O e = ψ e` using `fun _ => rfl`.

Set `Q : Ideal E` to `(maximalIdeal O).comap (algebraMap E O)`. Establish `: Q.IsPrime` using `Ideal.comap_isPrime _ _`. Establish `hQP : Q.comap (algebraMap (Polynomial T) E) = (maximalIdeal T).map (Polynomial.C : T →+* Polynomial T)`. Rewrite using `[← hPgen]`. Use extensionality with `p`.

Establish `h1 : algebraMap E O (algebraMap (Polynomial T) E p) = φ (algebraMap (Polynomial T) (Localization.AtPrime P) p)`. Rewrite using `[hEO, ψ.commutes, ← hφ, RingHom.comp_apply]`. Simplify using `only [Q, Ideal.mem_comap, h1, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, isUnit_map_iff φ]`. Rewrite using `[← mem_nonunits_iff, ← IsLocalRing.mem_maximalIdeal]`. Conclude with `IsLocalization.AtPrime.to_map_mem_maximal_iff (Localization.AtPrime P) P p`.

Take `⟨y, hymax, hQy, hyne, hyT⟩` from `exists_maximal_over_closedPt T E Q hQP`. Establish `: y.IsPrime` using `hymax.isPrime`. Take `⟨S, _, _, _, _, _, _, _, _, hSy, hflat, hpieces, φ', hφ', hsh'⟩` from `sh_at (T := T) (E := E) y`. Establish `hdiv : DivConst T S` using `hcl T S hT _ φ' hφ' hsh' hyT hyne`. Take `⟨a, w, ha⟩` from `hdiv (algebraMap E S g) (algebraMap E S g') s hs (by`.

Rewrite using `[← map_mul, hgg, ← IsScalarTower.algebraMap_apply])`. Establish `: HenselianLocalRing O` using `hHen`. Establish `: IsSepClosed (IsLocalRing.ResidueField O)` using `hSep`. Take `⟨χ⟩` from `specialisation_map E S O Q y hQy hSy rfl hflat hpieces`. Use `⟨a, Units.map χ.toRingHom.toMonoidHom w, ?_⟩` and prove the remaining obligations.

Establish `hχT : χ (algebraMap T S a) = algebraMap T O a`. Rewrite using `[IsScalarTower.algebraMap_apply T E S, χ.commutes, hEO, IsScalarTower.algebraMap_apply T (Polynomial T) E, ψ.commutes, ← IsScalarTower.algebraMap_apply]`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem divConstGeneric_of_divConstClosedPts : DivConstClosedPts → DivConstGeneric := by
  intro hcl T O _ _ _ _ _ _ _ _ hT P _ φ hφ hsh hPm hPgen b c s hs hbc
  obtain ⟨hHen, hSep, hloc, hind⟩ := hsh
  obtain ⟨E, _, _, _, _, _, ψ, g, g', hg, hg', hgg⟩ := stage T O P φ hφ hind b c s hbc
  let _ : Algebra E O := ψ.toRingHom.toAlgebra
  have hEO : ∀ e : E, algebraMap E O e = ψ e := fun _ => rfl
  let Q : Ideal E := (maximalIdeal O).comap (algebraMap E O)
  have : Q.IsPrime := Ideal.comap_isPrime _ _
  have hQP : Q.comap (algebraMap (Polynomial T) E) =
      (maximalIdeal T).map (Polynomial.C : T →+* Polynomial T) := by
    rw [← hPgen]
    ext p
    have h1 : algebraMap E O (algebraMap (Polynomial T) E p) =
        φ (algebraMap (Polynomial T) (Localization.AtPrime P) p) := by
      rw [hEO, ψ.commutes, ← hφ, RingHom.comp_apply]
    simp only [Q, Ideal.mem_comap, h1, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff,
      isUnit_map_iff φ]
    rw [← mem_nonunits_iff, ← IsLocalRing.mem_maximalIdeal]
    exact IsLocalization.AtPrime.to_map_mem_maximal_iff (Localization.AtPrime P) P p
  obtain ⟨y, hymax, hQy, hyne, hyT⟩ := exists_maximal_over_closedPt T E Q hQP
  have : y.IsPrime := hymax.isPrime
  obtain ⟨S, _, _, _, _, _, _, _, _, hSy, hflat, hpieces, φ', hφ', hsh'⟩ := sh_at (T := T) (E := E) y
  have hdiv : DivConst T S := hcl T S hT _ φ' hφ' hsh' hyT hyne
  obtain ⟨a, w, ha⟩ := hdiv (algebraMap E S g) (algebraMap E S g') s hs (by
    rw [← map_mul, hgg, ← IsScalarTower.algebraMap_apply])
  have : HenselianLocalRing O := hHen
  have : IsSepClosed (IsLocalRing.ResidueField O) := hSep
  obtain ⟨χ⟩ := specialisation_map E S O Q y hQy hSy rfl hflat hpieces
  refine ⟨a, Units.map χ.toRingHom.toMonoidHom w, ?_⟩
  have hχT : χ (algebraMap T S a) = algebraMap T O a := by
    rw [IsScalarTower.algebraMap_apply T E S, χ.commutes, hEO,
      IsScalarTower.algebraMap_apply T (Polynomial T) E, ψ.commutes,
      ← IsScalarTower.algebraMap_apply]
  calc b = ψ g := hg.symm
    _ = χ (algebraMap E S g) := by rw [χ.commutes, hEO]
    _ = algebraMap T O a * χ w := by rw [ha, map_mul, hχT]
    _ = _ := rfl

end GlobalTheory.VertUnits

import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.DivisorSupportCondition
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FiniteMaximalSpectrumOfFiniteOfIsLocalRing
import Development.AutomorphicArithmetic.CommutativeAlgebra.EtaleCohomologyFunctorialityAxiomsHold
import Development.AutomorphicArithmetic.CommutativeAlgebra.TwistedCohomologySpecProdBijectiveProd

open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace UpperTheory.Cb.AcycFin

/- English proof (translation)
Conclude with `Algebra.IsAlgebraic.isSepClosed (F := K)`.
-/
private theorem sepClosed_of_isAlgebraic (K L : Type) [Field K] [Field L] [Algebra K L]
    [Algebra.IsAlgebraic K L] [IsSepClosed K] : IsSepClosed L := by
  exact Algebra.IsAlgebraic.isSepClosed (F := K)

/- English proof (translation)
Take `⟨_, hk⟩` from `hO`. Use `haveI : IsLocalHom (algebraMap O T) := ((IsLocalRing.local_hom_TFAE (algebraMap O T)).out 0 4).mpr (GlobalTheory.comap_eq_maximalIdeal_of_finite (IsLocalRing.maximalIdeal T))`. Use `haveI : Algebra.IsAlgebraic (IsLocalRing.ResidueField O) (IsLocalRing.ResidueField T) := inferInstance`. Conclude with `⟨hT, sepClosed_of_isAlgebraic (IsLocalRing.ResidueField O) (IsLocalRing.ResidueField T)⟩`.
-/
private theorem sh_of_finite (O T : Type) [CommRing O] [CommRing T] [Algebra O T]
    [Module.Finite O T] (hO : SH O) (hT : HenselianLocalRing T) : SH T := by
  obtain ⟨_, hk⟩ := hO
  haveI : IsLocalHom (algebraMap O T) :=
    ((IsLocalRing.local_hom_TFAE (algebraMap O T)).out 0 4).mpr
      (GlobalTheory.comap_eq_maximalIdeal_of_finite (IsLocalRing.maximalIdeal T))
  haveI : Algebra.IsAlgebraic (IsLocalRing.ResidueField O) (IsLocalRing.ResidueField T) := inferInstance
  exact ⟨hT, sepClosed_of_isAlgebraic (IsLocalRing.ResidueField O) (IsLocalRing.ResidueField T)⟩

/- English proof (translation)
Introduce `n i hn`. Use `haveI := h n i hn`. Establish `hid : spMap (e : A →+* B) ≫ spMap (e.symm : B →+* A) = 𝟙 (sp B)`. Establish `h0 : CommRingCat.ofHom (e.symm : B →+* A) ≫ CommRingCat.ofHom (e : A →+* B) = 𝟙 _`. Use extensionality with `x`.

Simplify using the standard rewrite rules. Simplify using `only [spMap, ← Functor.map_comp, ← Spec.map_comp, h0, Spec.map_id]`. Conclude with `sch.map_id _`. Establish `key : Function.LeftInverse (pull (ZMod q) (spMap (e : A →+* B)) (tw q i) n) (pull (ZMod q) (spMap (e.symm : B →+* A)) (tw q i) n)` using `fun x => by`. Rewrite using `[← pull_comp, hid, pull_id]`.

Conclude with `key.injective.subsingleton`.
-/
private theorem acyc_of_equiv {q : ℕ} {A B : Type} [CommRing A] [CommRing B] (e : A ≃+* B)
    (h : Acyc q (sp A)) : Acyc q (sp B) := by
  intro n i hn
  haveI := h n i hn
  have hid : spMap (e : A →+* B) ≫ spMap (e.symm : B →+* A) = 𝟙 (sp B) := by
    have h0 : CommRingCat.ofHom (e.symm : B →+* A) ≫ CommRingCat.ofHom (e : A →+* B) = 𝟙 _ := by
      ext x
      simp
    simp only [spMap, ← Functor.map_comp, ← Spec.map_comp, h0, Spec.map_id]
    exact sch.map_id _
  have key : Function.LeftInverse (pull (ZMod q) (spMap (e : A →+* B)) (tw q i) n)
      (pull (ZMod q) (spMap (e.symm : B →+* A)) (tw q i) n) := fun x => by
    rw [← pull_comp, hid, pull_id]
  exact key.injective.subsingleton

/- English proof (translation)
Introduce `n i hn`. Use `haveI := hA n i hn`. Use `haveI := hB n i hn`. Conclude with `⟨fun x y => (UpperTheory.twistedCohomology_specProd_bijective_prod q A B n i).1 (Prod.ext (Subsingleton.elim _ _) (Subsingleton.elim _ _))⟩`.
-/
private theorem acyc_prod {q : ℕ} {A B : Type} [CommRing A] [CommRing B]
    (hA : Acyc q (sp A)) (hB : Acyc q (sp B)) : Acyc q (sp (A × B)) := by
  intro n i hn
  haveI := hA n i hn
  haveI := hB n i hn
  exact ⟨fun x y => (UpperTheory.twistedCohomology_specProd_bijective_prod q A B n i).1
    (Prod.ext (Subsingleton.elim _ _) (Subsingleton.elim _ _))⟩

/- English proof (translation)
Introduce `n i hn`. Establish `hfs : RingHom.fst A A = RingHom.snd A A`. Use extensionality with `x`. Conclude with `Subsingleton.elim _ _`. Take `⟨_, hsurj⟩` from `UpperTheory.twistedCohomology_specProd_bijective_prod q A A n i`.

Use `⟨fun u v => ?_⟩` and prove the remaining obligations. Take `⟨x, hx⟩` from `hsurj (u, v)`. Rewrite `hx` using `[hfs]`. Establish `h1` using `congrArg Prod.fst hx`. Establish `h2` using `congrArg Prod.snd hx`.

Simplify using `only at h1 h2`. Rewrite using `[← h1, ← h2]`.
-/
private theorem acyc_of_subsingleton {q : ℕ} {A : Type} [CommRing A] [Subsingleton A] :
    Acyc q (sp A) := by
  intro n i hn
  have hfs : RingHom.fst A A = RingHom.snd A A := by
    ext x
    exact Subsingleton.elim _ _
  obtain ⟨_, hsurj⟩ := UpperTheory.twistedCohomology_specProd_bijective_prod q A A n i
  refine ⟨fun u v => ?_⟩
  obtain ⟨x, hx⟩ := hsurj (u, v)
  rw [hfs] at hx
  have h1 := congrArg Prod.fst hx
  have h2 := congrArg Prod.snd hx
  simp only at h1 h2
  rw [← h1, ← h2]

/- English proof (translation)
Use `Finite.induction_empty_option (P := fun α => ∀ (T : α → Type) [∀ i, CommRing (T i)], (∀ i, Acyc q (sp (T i))) → Acyc q (sp (Π i, T i))) ?_ ?_ ?_ ι` and prove the remaining obligations. Introduce `α β e ih T _ hT`. Conclude with `acyc_of_equiv (RingEquiv.piCongrLeft T e) (ih (fun a => T (e a)) (fun a => hT (e a)))`. Introduce `T _ _`. Conclude with `acyc_of_subsingleton`.

Introduce `α _ ih T _ hT`. Conclude with `acyc_of_equiv RingEquiv.piOptionEquivProd.symm (acyc_prod (hT none) (ih (fun a => T (some a)) (fun a => hT (some a))))`.
-/
private theorem acyc_pi (q : ℕ) (ι : Type) [Finite ι] :
    ∀ (T : ι → Type) [∀ i, CommRing (T i)], (∀ i, Acyc q (sp (T i))) →
      Acyc q (sp (Π i, T i)) := by
  refine Finite.induction_empty_option (P := fun α => ∀ (T : α → Type) [∀ i, CommRing (T i)],
      (∀ i, Acyc q (sp (T i))) → Acyc q (sp (Π i, T i))) ?_ ?_ ?_ ι
  · intro α β e ih T _ hT
    exact acyc_of_equiv (RingEquiv.piCongrLeft T e) (ih (fun a => T (e a)) (fun a => hT (e a)))
  · intro T _ _
    exact acyc_of_subsingleton
  · intro α _ ih T _ hT
    exact acyc_of_equiv RingEquiv.piOptionEquivProd.symm
      (acyc_prod (hT none) (ih (fun a => T (some a)) (fun a => hT (some a))))

end UpperTheory.Cb.AcycFin

open UpperTheory.Cb.AcycFin in

/- English proof (translation)
Introduce `q O A _ _ _ _ hO _`. Take `⟨hH, hk⟩` from `hO`. Take `⟨ι, _, T, _, _, e, hT⟩` from `GlobalTheory.exists_algEquiv_pi_henselianLocalRing O A`. Use `acyc_of_equiv e.symm.toRingEquiv (acyc_pi q ι T fun j => ?_)` and prove the remaining obligations. Take `⟨h1, h2⟩` from `hT j`.

Use `haveI := h2`. Establish `hs : SH (T j)` using `sh_of_finite O (T j) ⟨hH, hk⟩ h1`. Introduce `n i hn`. Conclude with `UpperTheory.etaleCohomology_functorialityAxioms_hold (ZMod q) (T j) hs (tw q i) n hn`.
-/
theorem UpperTheory.acyclic_spec_finite_algebra_strictHenselian :
    ∀ (q : ℕ) (O A : Type) [CommRing O] [CommRing A] [Algebra O A] [Module.Finite O A], SH O → IsUnit (q : O) → Acyc q (sp A) := by
  intro q O A _ _ _ _ hO _
  obtain ⟨hH, hk⟩ := hO
  obtain ⟨ι, _, T, _, _, e, hT⟩ := GlobalTheory.exists_algEquiv_pi_henselianLocalRing O A
  refine acyc_of_equiv e.symm.toRingEquiv (acyc_pi q ι T fun j => ?_)
  obtain ⟨h1, h2⟩ := hT j
  haveI := h2
  have hs : SH (T j) := sh_of_finite O (T j) ⟨hH, hk⟩ h1
  intro n i hn
  exact UpperTheory.etaleCohomology_functorialityAxioms_hold (ZMod q) (T j) hs (tw q i) n hn

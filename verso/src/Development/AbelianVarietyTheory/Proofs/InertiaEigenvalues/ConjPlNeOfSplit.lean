import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ExistsIsScalar
import Formalism.LocalToGlobal.IndefiniteReal.ConcretePkgSpec
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ArtinPullbackIsGoodTwistOfAnticyclotomicTameStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ThetaVacuumHeckeIdentitySplitPlace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIdempotentSumAuxiliaryPlaces
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ThetaOfOfIsCharLab
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie
open Formalism.IndefR.Links
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.UnivGood

variable {D : D7}

/- English proof (translation)
Introduce `hP`. Take `⟨x, hx, hy⟩` from `h`. Use `hy (Formalism.DivisionValues.cO D.host.E x) ?_ ?_` and prove the remaining obligations. Use `show starRingAut (x : D.host.E) = D.host.conj (x : D.host.E)`. Rewrite using `[starRingAut_apply]`.

Conclude with `Formalism.BasicNotions.bridge_star_holds D.R D.host _`. Establish `: Formalism.DivisionValues.cO _ x ∈ (Formalism.DivisionValues.conjPl P).asIdeal` using `Ideal.mem_map_of_mem _ hx`. Rewrite `this` using `[hP]`. Then use the resulting hypothesis.
-/
theorem conjPl_ne_of_split {P : Pl D.host.E} (h : IsSplitPl D.host P) : Formalism.DivisionValues.conjPl P ≠ P := by
  intro hP
  obtain ⟨x, hx, hy⟩ := h
  refine hy (Formalism.DivisionValues.cO D.host.E x) ?_ ?_
  · show starRingAut (x : D.host.E) = D.host.conj (x : D.host.E)
    rw [starRingAut_apply]
    exact Formalism.BasicNotions.bridge_star_holds D.R D.host _
  · have : Formalism.DivisionValues.cO _ x ∈ (Formalism.DivisionValues.conjPl P).asIdeal := Ideal.mem_map_of_mem _ hx
    rwa [hP] at this

/- English proof (translation)
Use `GlobalTheory.GridIdem.exists_isIdemSum S (fun P hP => GlobalTheory.Hk3.SplitMatch.exists_isIdemAt (conjPl_ne_of_split (hs P hP))) fun P hP P' hP' h => ?_` and prove the remaining obligations. Break down `(GlobalTheory.Mem.TypePl.under_eq_iff P P').1 h.symm with e | e` into its components or cases. Conclude with `e.symm`. Conclude with `absurd e (hn P hP P' hP')`.
-/
theorem splitSet_of_split {S : Finset (Pl D.host.E)} (hs : ∀ P ∈ S, IsSplitPl D.host P)
    (hn : ∀ P ∈ S, ∀ P' ∈ S, ¬ IsConjPl D.host P P') : SplitSet S := by
  refine GlobalTheory.GridIdem.exists_isIdemSum S (fun P hP => GlobalTheory.Hk3.SplitMatch.exists_isIdemAt (conjPl_ne_of_split (hs P hP)))
    fun P hP P' hP' h => ?_
  rcases (GlobalTheory.Mem.TypePl.under_eq_iff P P').1 h.symm with e | e
  · exact e.symm
  · exact absurd e (hn P hP P' hP')

end GlobalTheory.UnivGood

namespace GlobalTheory.UnivGood

variable {D : D7}

/- English proof (translation)
Introduce `D N X ρ hρ Y i Q M`. Use `set A := admissibleConjugatePairPlaces X i Q M with hA`. Establish `hAconj : ∀ P ∈ A, ∀ P', IsConjPl D.host P P' → P' ∈ A` using `fun P hP P' hc => conj_mem_admissibleConjugatePairPlaces hP hc`. Establish `hsplit : SplitSet (half (ρ.ch i) A)`. Use `splitSet_of_split (fun P hP => isSplit_of_mem_admissibleConjugatePairPlaces (mem_half.1 hP).1) fun P hP P' hP' hc => ?_` and prove the remaining obligations.

Establish `hne : P ≠ P'` using `ne_of_split (isSplit_of_mem_admissibleConjugatePairPlaces (mem_half.1 hP).1) hc`. Conclude with `((hρ.ch i).pair P P' hc hne).1 (mem_half.1 hP).2 (mem_half.1 hP').2`. Use `⟨hsplit, fun PP hPP => ?_⟩` and prove the remaining obligations. Establish `hPA : PP ∈ A` using `(mem_half.1 hPP).1`. Take `⟨-, P', hP'Q, hc, hadm⟩` from `mem_admissibleConjugatePairPlaces_iff.1 hPA`.

Establish `hP'A : P' ∈ A` using `conj_mem_admissibleConjugatePairPlaces hPA hc`. Use `set φ := coord Y i A M PP with hφ`. Establish `hco : ∀ σ, Multiplicative.toAdd (φ σ) = Multiplicative.toAdd (Y.delU i A M σ) ⟨PP, hPA⟩` using `fun σ => coord_apply Y i A M hPA σ`. Establish `hord : ∀ σ, ∃ n : ℕ, φ σ ^ (X.l i ^ n) = 1` using `fun σ => ⟨M, by`. Rewrite using `[← ofAdd_toAdd (φ σ), ← ofAdd_nsmul, nsmul_eq_mul, ZMod.natCast_self, zero_mul, ofAdd_zero]⟩`.

Establish `hopen : IsOpen (φ.ker : Set (G D.host.E N.Om))`. Use `Subgroup.isOpen_mono (H₁ := (Y.delU i A M).ker) (fun g hg => ?_) (Y.delU_open i A M)` and prove the remaining obligations. Use `MonoidHom.mem_ker.2 (Multiplicative.toAdd.injective ?_)` and prove the remaining obligations. Rewrite using `[hco, MonoidHom.mem_ker.1 hg]`. Both sides reduce to the same expression.

Establish `hanti : AntiHom X.cc φ` using `fun g g' hg => by`. Use `Multiplicative.toAdd.injective ?_` and prove the remaining obligations. Rewrite using `[toAdd_inv, hco, hco, Y.delU_anti i A M g g' hg, toAdd_inv]`. Both sides reduce to the same expression. Establish `hpair : ∀ x ∈ ({PP, P'} : Finset (Pl D.host.E)), ∀ y, IsConjPl D.host x y → y ∈ ({PP, P'} : Finset (Pl D.host.E))`.

Introduce `x hx y hy`. Break down `Finset.mem_insert.1 hx with rfl | hx` into its components or cases. Rewrite using `[GlobalTheory.GalChar.isConjPl_unique hy hc]`. Simplify using the standard rewrite rules. Rewrite `hx` using `[Finset.mem_singleton]`.

Substitute `hx` using the available equality. Rewrite using `[GlobalTheory.GalChar.isConjPl_unique hy (GlobalTheory.GalChar.isConjPl_symm hc)]`. Simplify using the standard rewrite rules. Establish `hsub : ({PP, P'} : Finset (Pl D.host.E)) ⊆ A`. Introduce `x hx`.

Break down `Finset.mem_insert.1 hx with rfl | hx` into its components or cases. Conclude with `hPA`. Rewrite `hx` using `[Finset.mem_singleton]`. Substitute `hx` using the available equality. Conclude with `hP'A`.

Establish `hunr : ∀ v : Pl D.host.E, v ∉ ({PP} : Finset (Pl D.host.E)) → (∀ P ∈ ({PP} : Finset (Pl D.host.E)), ¬ IsConjPl D.host P v) → ∀ B : ValuationSubring N.Om, IsPlaceOver B v → ∀ σ ∈ Ine (F` using `D.host.E) B, φ σ = 1 := by`. Introduce `v hv hnc B hB σ hσ`. Establish `hv' : v ∉ ({PP, P'} : Finset (Pl D.host.E))`. Introduce `h`. Break down `Finset.mem_insert.1 h with rfl | h` into its components or cases.

Conclude with `hv (Finset.mem_singleton_self _)`. Rewrite `h` using `[Finset.mem_singleton]`. Substitute `h` using the available equality. Conclude with `hnc PP (Finset.mem_singleton_self _) hc`. Use `Multiplicative.toAdd.injective ?_` and prove the remaining obligations.

Rewrite using `[hco, ← Y.delU_res i M {PP, P'} A hsub hpair hAconj σ PP (by simp), Y.delU_unr i {PP, P'} M v hv' B hB σ hσ]`. Both sides reduce to the same expression. Establish `hl : ∀ P ∈ ({PP} : Finset (Pl D.host.E)), ((X.l i : ℕ) : 𝓞 D.host.E) ∉ P.asIdeal`. Introduce `P hP`. Rewrite `hP` using `[Finset.mem_singleton]`.

Substitute `hP` using the available equality. Conclude with `(hadm.1 P (by simp)).2`. Establish `hg` using `GlobalTheory.T.artinPullback_isGoodTwist_of_anticyclotomic_tame D N X ρ.rc hρ.rc (Multiplicative (ZMod (X.l i ^ M))) φ (X.l i) (X.lPrime i).out hord hopen hanti {PP} (hsplit.mono (Finset.singleton_subset_iff.2 hPP)) hl hunr`. Take `⟨h1, h2, h3, h4, h5, h6⟩` from `hg`. Use `⟨h1, h2, h3, h4, h5, fun P hP => ?_⟩` and prove the remaining obligations.

Rewrite `hP` using `[Finset.mem_singleton]`. Substitute `hP` using the available equality. Conclude with `h6 _ (Finset.mem_singleton_self _)`.
-/
theorem univOf_good : ∀ (D : D7) (N : NData D.R D.host D.what₂) (X : NTw D.R D.host D.what₂ D.LL0 N) (ρ : Setup X), ρ.Good →
    ∀ (Y : NExp D.R D.host D.what₂ D.LL0 N X) (i : X.Tw) (Q : Finset (Pl D.host.E)) (M : ℕ),
      (univOf Y i (admissibleConjugatePairPlaces X i Q M) M ρ.rc).Good (half (ρ.ch i) (admissibleConjugatePairPlaces X i Q M)) := by
  intro D N X ρ hρ Y i Q M
  classical
  set A := admissibleConjugatePairPlaces X i Q M with hA
  have hAconj : ∀ P ∈ A, ∀ P', IsConjPl D.host P P' → P' ∈ A := fun P hP P' hc => conj_mem_admissibleConjugatePairPlaces hP hc
  have hsplit : SplitSet (half (ρ.ch i) A) := by
    refine splitSet_of_split (fun P hP => isSplit_of_mem_admissibleConjugatePairPlaces (mem_half.1 hP).1) fun P hP P' hP' hc => ?_
    have hne : P ≠ P' := ne_of_split (isSplit_of_mem_admissibleConjugatePairPlaces (mem_half.1 hP).1) hc
    exact ((hρ.ch i).pair P P' hc hne).1 (mem_half.1 hP).2 (mem_half.1 hP').2
  refine ⟨hsplit, fun PP hPP => ?_⟩
  have hPA : PP ∈ A := (mem_half.1 hPP).1
  obtain ⟨-, P', hP'Q, hc, hadm⟩ := mem_admissibleConjugatePairPlaces_iff.1 hPA
  have hP'A : P' ∈ A := conj_mem_admissibleConjugatePairPlaces hPA hc
  set φ := coord Y i A M PP with hφ
  have hco : ∀ σ, Multiplicative.toAdd (φ σ) = Multiplicative.toAdd (Y.delU i A M σ) ⟨PP, hPA⟩ :=
    fun σ => coord_apply Y i A M hPA σ
  have hord : ∀ σ, ∃ n : ℕ, φ σ ^ (X.l i ^ n) = 1 := fun σ => ⟨M, by
    rw [← ofAdd_toAdd (φ σ), ← ofAdd_nsmul, nsmul_eq_mul, ZMod.natCast_self, zero_mul, ofAdd_zero]⟩
  have hopen : IsOpen (φ.ker : Set (G D.host.E N.Om)) := by
    refine Subgroup.isOpen_mono (H₁ := (Y.delU i A M).ker) (fun g hg => ?_) (Y.delU_open i A M)
    refine MonoidHom.mem_ker.2 (Multiplicative.toAdd.injective ?_)
    rw [hco, MonoidHom.mem_ker.1 hg]
    rfl
  have hanti : AntiHom X.cc φ := fun g g' hg => by
    refine Multiplicative.toAdd.injective ?_
    rw [toAdd_inv, hco, hco, Y.delU_anti i A M g g' hg, toAdd_inv]
    rfl

  have hpair : ∀ x ∈ ({PP, P'} : Finset (Pl D.host.E)), ∀ y, IsConjPl D.host x y → y ∈ ({PP, P'} : Finset (Pl D.host.E)) := by
    intro x hx y hy
    rcases Finset.mem_insert.1 hx with rfl | hx
    · rw [GlobalTheory.GalChar.isConjPl_unique hy hc]; simp
    · rw [Finset.mem_singleton] at hx
      subst hx
      rw [GlobalTheory.GalChar.isConjPl_unique hy (GlobalTheory.GalChar.isConjPl_symm hc)]; simp
  have hsub : ({PP, P'} : Finset (Pl D.host.E)) ⊆ A := by
    intro x hx
    rcases Finset.mem_insert.1 hx with rfl | hx
    · exact hPA
    · rw [Finset.mem_singleton] at hx; subst hx; exact hP'A
  have hunr : ∀ v : Pl D.host.E, v ∉ ({PP} : Finset (Pl D.host.E)) →
      (∀ P ∈ ({PP} : Finset (Pl D.host.E)), ¬ IsConjPl D.host P v) →
      ∀ B : ValuationSubring N.Om, IsPlaceOver B v → ∀ σ ∈ Ine (F := D.host.E) B, φ σ = 1 := by
    intro v hv hnc B hB σ hσ
    have hv' : v ∉ ({PP, P'} : Finset (Pl D.host.E)) := by
      intro h
      rcases Finset.mem_insert.1 h with rfl | h
      · exact hv (Finset.mem_singleton_self _)
      · rw [Finset.mem_singleton] at h
        subst h
        exact hnc PP (Finset.mem_singleton_self _) hc
    refine Multiplicative.toAdd.injective ?_
    rw [hco, ← Y.delU_res i M {PP, P'} A hsub hpair hAconj σ PP (by simp),
      Y.delU_unr i {PP, P'} M v hv' B hB σ hσ]
    rfl
  have hl : ∀ P ∈ ({PP} : Finset (Pl D.host.E)), ((X.l i : ℕ) : 𝓞 D.host.E) ∉ P.asIdeal := by
    intro P hP
    rw [Finset.mem_singleton] at hP
    subst hP
    exact (hadm.1 P (by simp)).2
  have hg := GlobalTheory.T.artinPullback_isGoodTwist_of_anticyclotomic_tame D N X ρ.rc hρ.rc (Multiplicative (ZMod (X.l i ^ M))) φ (X.l i) (X.lPrime i).out hord hopen
    hanti {PP} (hsplit.mono (Finset.singleton_subset_iff.2 hPP)) hl hunr
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hg
  refine ⟨h1, h2, h3, h4, h5, fun P hP => ?_⟩
  rw [Finset.mem_singleton] at hP
  subst hP
  exact h6 _ (Finset.mem_singleton_self _)

end GlobalTheory.UnivGood

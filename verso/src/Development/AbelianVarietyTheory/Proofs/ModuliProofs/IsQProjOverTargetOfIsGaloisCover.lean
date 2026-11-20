import Mathlib
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.GaloisCoverDescentAndCartesianSquares
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsAffineCoverOfQuotient
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverIffIsProperAndExistsIsAmpleLB
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

attribute [local instance] MvPolynomial.gradedAlgebra

namespace GlobalTheory.GaloisQuotient

open TopologicalSpace

/- English proof (translation)
Proceed by induction on `P using Finset.strongInduction with`. Consider the case `H P ih`. Break down `P.eq_empty_or_nonempty with rfl | hne` into its components or cases. Conclude with `⟨1, one_pos, 0, zero_mem _, zero_mem _, by simp⟩`. Take `⟨q, hqP, hqmin⟩` from `P.exists_minimal hne`.

Take `⟨d, hd, f, hf, hfJ, hfP⟩` from `ih (P.erase q) (Finset.erase_ssubset hqP) (fun p hp => hP p (Finset.mem_of_mem_erase hp))`. Distinguish the cases in `hfq : f ∉ q`. Use `⟨d, hd, f, hf, hfJ, fun p hp => ?_⟩` and prove the remaining obligations. Distinguish the cases in `hpq : p = q`. Rewrite using `[hpq]`.

Conclude with `hfq`. Conclude with `hfP p (Finset.mem_erase.2 ⟨hpq, hp⟩)`. Use `push Not at hfq`. Take `⟨hqprime, -, e, he, g, hg, hgJ, hgq⟩` from `hP q hqP`. Establish `hx : ∀ p ∈ P.erase q, ∃ c, ∃ x ∈ 𝒜 c, x ∈ p ∧ x ∉ q`.

Introduce `p hp`. Take `⟨hpne, hpP⟩` from `Finset.mem_erase.1 hp`. Take `⟨-, hphom, -⟩` from `hP p hpP`. Establish `hnle : ¬ p ≤ q` using `fun hle => hpne (le_antisymm hle (hqmin hpP hle))`. Take `⟨y, hyp, hyq⟩` from `Set.not_subset.1 hnle`.

Assume the negation of the conclusion as `hcon`. Use `push Not at hcon`. Apply `hyq` to reduce the goal to its premises. Rewrite using `[← DirectSum.sum_support_decompose 𝒜 y]`. Conclude with `Ideal.sum_mem _ fun c _ => hcon c _ (SetLike.coe_mem _) (hphom c hyp)`.

Use `choose! c x hx𝒜 hxp hxq using hx`. Use `set C := ∑ p ∈ P.erase q, c p`. Use `set h := ∏ p ∈ P.erase q, x p`. Establish `hh : h ∈ 𝒜 C` using `SetLike.prod_mem_graded 𝒜 c x hx𝒜`. Establish `hhq : h ∉ q`.

Introduce `hm`. Take `⟨p, hp, hpq⟩` from `(Ideal.IsPrime.prod_mem_iff (hp := hqprime)).1 hm`. Conclude with `hxq p hp hpq`. Establish `hhp : ∀ p ∈ P.erase q, h ∈ p` using `fun p hp => by`. Take `⟨k, hk⟩` from `Finset.dvd_prod_of_mem x hp`.

Establish `hk' : h = x p * k` using `hk`. Rewrite using `[hk']`. Conclude with `p.mul_mem_right _ (hxp p hp)`. Establish `hpos : 0 < e + C` using `Nat.add_pos_left he _`. Use `⟨d * (e + C), Nat.mul_pos hd hpos, f ^ (e + C) + (g * h) ^ d, ?_, ?_, ?_⟩` and prove the remaining obligations.

Use `Submodule.add_mem _ ?_ ?_` and prove the remaining obligations. Establish `h1` using `SetLike.pow_mem_graded (e + C) hf`. Rewrite `h1` using `[smul_eq_mul, mul_comm]`. Then use the resulting hypothesis. Establish `h1` using `SetLike.pow_mem_graded d (SetLike.mul_mem_graded hg hh)`. Rewrite `h1` using `[smul_eq_mul]`. Then use the resulting hypothesis.

Conclude with `J.add_mem (J.pow_mem_of_mem hfJ _ hpos) (J.pow_mem_of_mem (J.mul_mem_right _ hgJ) _ hd)`. Introduce `p hp hF`. Distinguish the cases in `hpq : p = q`. Rewrite `hF` using `[hpq]`. Establish `h1 : f ^ (e + C) ∈ q` using `q.pow_mem_of_mem hfq _ hpos`.

Establish `h2 : (g * h) ^ d ∈ q` using `(q.add_mem_iff_right h1).1 hF`. Break down `hqprime.mem_or_mem (hqprime.mem_of_pow_mem _ h2) with h3 | h3` into its components or cases. Conclude with `hgq h3`. Conclude with `hhq h3`. Establish `hp' : p ∈ P.erase q` using `Finset.mem_erase.2 ⟨hpq, hp⟩`.

Establish `hpprime` using `(hP p hp).1`. Establish `h2 : (g * h) ^ d ∈ p` using `p.pow_mem_of_mem (p.mul_mem_left _ (hhp p hp')) _ hd`. Establish `h1 : f ^ (e + C) ∈ p` using `(p.add_mem_iff_left h2).1 hF`. Conclude with `hfP p hp' (hpprime.mem_of_pow_mem _ h1)`.
-/
private theorem exists_homogeneous_mem_not_mem_finset_primes {R A : Type} [CommRing R] [CommRing A] [Algebra R A]
    (𝒜 : ℕ → Submodule R A) [GradedAlgebra 𝒜] (J : Ideal A) (P : Finset (Ideal A))
    (hP : ∀ p ∈ P, p.IsPrime ∧ p.IsHomogeneous 𝒜 ∧ ∃ d, 0 < d ∧ ∃ g ∈ 𝒜 d, g ∈ J ∧ g ∉ p) :
    ∃ d, 0 < d ∧ ∃ f ∈ 𝒜 d, f ∈ J ∧ ∀ p ∈ P, f ∉ p := by
  classical
  induction P using Finset.strongInduction with
  | H P ih =>
  rcases P.eq_empty_or_nonempty with rfl | hne
  · exact ⟨1, one_pos, 0, zero_mem _, zero_mem _, by simp⟩
  obtain ⟨q, hqP, hqmin⟩ := P.exists_minimal hne
  obtain ⟨d, hd, f, hf, hfJ, hfP⟩ := ih (P.erase q) (Finset.erase_ssubset hqP)
    (fun p hp => hP p (Finset.mem_of_mem_erase hp))
  by_cases hfq : f ∉ q
  · refine ⟨d, hd, f, hf, hfJ, fun p hp => ?_⟩
    by_cases hpq : p = q
    · rw [hpq]; exact hfq
    · exact hfP p (Finset.mem_erase.2 ⟨hpq, hp⟩)
  push Not at hfq
  obtain ⟨hqprime, -, e, he, g, hg, hgJ, hgq⟩ := hP q hqP
  have hx : ∀ p ∈ P.erase q, ∃ c, ∃ x ∈ 𝒜 c, x ∈ p ∧ x ∉ q := by
    intro p hp
    obtain ⟨hpne, hpP⟩ := Finset.mem_erase.1 hp
    obtain ⟨-, hphom, -⟩ := hP p hpP
    have hnle : ¬ p ≤ q := fun hle => hpne (le_antisymm hle (hqmin hpP hle))
    obtain ⟨y, hyp, hyq⟩ := Set.not_subset.1 hnle
    by_contra hcon
    push Not at hcon
    apply hyq
    rw [← DirectSum.sum_support_decompose 𝒜 y]
    exact Ideal.sum_mem _ fun c _ => hcon c _ (SetLike.coe_mem _) (hphom c hyp)
  choose! c x hx𝒜 hxp hxq using hx
  set C := ∑ p ∈ P.erase q, c p
  set h := ∏ p ∈ P.erase q, x p
  have hh : h ∈ 𝒜 C := SetLike.prod_mem_graded 𝒜 c x hx𝒜
  have hhq : h ∉ q := by
    intro hm
    obtain ⟨p, hp, hpq⟩ := (Ideal.IsPrime.prod_mem_iff (hp := hqprime)).1 hm
    exact hxq p hp hpq
  have hhp : ∀ p ∈ P.erase q, h ∈ p := fun p hp => by
    obtain ⟨k, hk⟩ := Finset.dvd_prod_of_mem x hp
    have hk' : h = x p * k := hk
    rw [hk']
    exact p.mul_mem_right _ (hxp p hp)
  have hpos : 0 < e + C := Nat.add_pos_left he _
  refine ⟨d * (e + C), Nat.mul_pos hd hpos, f ^ (e + C) + (g * h) ^ d, ?_, ?_, ?_⟩
  · refine Submodule.add_mem _ ?_ ?_
    · have h1 := SetLike.pow_mem_graded (e + C) hf
      rwa [smul_eq_mul, mul_comm] at h1
    · have h1 := SetLike.pow_mem_graded d (SetLike.mul_mem_graded hg hh)
      rwa [smul_eq_mul] at h1
  · exact J.add_mem (J.pow_mem_of_mem hfJ _ hpos) (J.pow_mem_of_mem (J.mul_mem_right _ hgJ) _ hd)
  · intro p hp hF
    by_cases hpq : p = q
    · rw [hpq] at hF
      have h1 : f ^ (e + C) ∈ q := q.pow_mem_of_mem hfq _ hpos
      have h2 : (g * h) ^ d ∈ q := (q.add_mem_iff_right h1).1 hF
      rcases hqprime.mem_or_mem (hqprime.mem_of_pow_mem _ h2) with h3 | h3
      · exact hgq h3
      · exact hhq h3
    · have hp' : p ∈ P.erase q := Finset.mem_erase.2 ⟨hpq, hp⟩
      have hpprime := (hP p hp).1
      have h2 : (g * h) ^ d ∈ p := p.pow_mem_of_mem (p.mul_mem_left _ (hhp p hp')) _ hd
      have h1 : f ^ (e + C) ∈ p := (p.add_mem_iff_left h2).1 hF
      exact hfP p hp' (hpprime.mem_of_pow_mem _ h1)

/- English proof (translation)
Set `J : Ideal (MvPolynomial (Fin (N + 1)) R)` to `(ProjectiveSpectrum.vanishingIdeal (𝒜 := ProjSpace.grading R N) {x | ¬ (x : PSpace R N) ∈ U}).toIdeal`. Establish `hJ1 : ∀ f ∈ J, Proj.basicOpen (ProjSpace.grading R N) f ≤ U` using `fun f hf x hx => by`. Assume the negation of the conclusion as `hxU`. Conclude with `hx ((ProjectiveSpectrum.mem_vanishingIdeal _ f).1 hf x hxU)`. Establish `hJ2 : ∀ g, Proj.basicOpen (ProjSpace.grading R N) g ≤ U → g ∈ J` using `fun g hg => (ProjectiveSpectrum.mem_vanishingIdeal _ g).2 fun x hxU => by`.

Assume the negation of the conclusion as `hgx`. Conclude with `hxU (hg hgx)`. Establish `hgen : ∀ x : PSpace R N, x ∈ U → ∃ d, 0 < d ∧ ∃ g ∈ ProjSpace.grading R N d, g ∈ J ∧ g ∉ (ProjectiveSpectrum.asHomogeneousIdeal (𝒜` using `ProjSpace.grading R N) x).toIdeal := by`. Introduce `x hxU`. Take `⟨_, ⟨r, rfl⟩, hxr, hrU⟩` from `TopologicalSpace.Opens.isBasis_iff_nbhd.1 (Proj.isBasis_basicOpen (ProjSpace.grading R N)) hxU`.

Rewrite `hxr` using `[Proj.basicOpen_eq_iSup_proj]`. Take `⟨k, hk⟩` from `TopologicalSpace.Opens.mem_iSup.1 hxr`. Establish `hkU : Proj.basicOpen (ProjSpace.grading R N) (GradedRing.proj (ProjSpace.grading R N) k r) ≤ U`. Use `le_trans ?_ hrU` and prove the remaining obligations. Rewrite using `[Proj.basicOpen_eq_iSup_proj (ProjSpace.grading R N) r]`.

Conclude with `le_iSup (fun k => Proj.basicOpen (ProjSpace.grading R N) (GradedRing.proj (ProjSpace.grading R N) k r)) k`. Take `⟨j, hj⟩` from `ProjSpace.exists_mem_chart R N x`. Use `⟨k + 1, Nat.succ_pos k, GradedRing.proj (ProjSpace.grading R N) k r * MvPolynomial.X j, ?_, ?_, ?_⟩` and prove the remaining obligations. Use `SetLike.mul_mem_graded ?_ (ProjSpace.X_mem R N j)` and prove the remaining obligations. Rewrite using `[GradedRing.proj_apply]`.

Conclude with `SetLike.coe_mem _`. Apply `hJ2` to reduce the goal to its premises. Rewrite using `[Proj.basicOpen_mul]`. Conclude with `inf_le_left.trans hkU`. Use `show x ∈ Proj.basicOpen (ProjSpace.grading R N) _`.

Rewrite using `[Proj.basicOpen_mul]`. Conclude with `⟨hk, hj⟩`. Take `⟨d, hd, f, hf, hfJ, hfP⟩` from `exists_homogeneous_mem_not_mem_finset_primes (ProjSpace.grading R N) J (hs.toFinset.image fun x : PSpace R N => (ProjectiveSpectrum.asHomogeneousIdeal (𝒜 := ProjSpace.grading R N) x).toIdeal) (by`. Introduce `p hp`. Take `⟨x, hx, rfl⟩` from `Finset.mem_image.1 hp`.

Conclude with `⟨ProjectiveSpectrum.isPrime _, HomogeneousIdeal.isHomogeneous _, hgen x (hU (hs.mem_toFinset.1 hx))⟩)`. Establish `hfh : f.IsHomogeneous d` using `(MvPolynomial.mem_homogeneousSubmodule d f).1 hf`. Use `⟨d, hd, ProjSpace.formSec d f hfh, ?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `x hx`. Rewrite using `[ProjSpace.nonzeroLocus_formSec]`.

Conclude with `hfP _ (Finset.mem_image_of_mem _ (hs.mem_toFinset.2 hx))`. Rewrite using `[ProjSpace.nonzeroLocus_formSec]`. Conclude with `hJ1 f hfJ`. Rewrite using `[ProjSpace.nonzeroLocus_formSec]`. Conclude with `Proj.isAffineOpen_basicOpen _ f hf hd`.
-/
theorem exists_sec_nonzeroLocus_le {R : Type} [CommRing R] {N : ℕ} {s : Set (PSpace R N)} (hs : s.Finite)
    (U : (PSpace R N).Opens) (hU : s ⊆ U) :
    ∃ n, 1 ≤ n ∧ ∃ t : (lbPow (ProjSpace.O1 R N) n).Sec,
      s ⊆ Out.nonzeroLocus t ∧ Out.nonzeroLocus t ≤ U ∧ IsAffineOpen (Out.nonzeroLocus t) := by
  classical
  let J : Ideal (MvPolynomial (Fin (N + 1)) R) :=
    (ProjectiveSpectrum.vanishingIdeal (𝒜 := ProjSpace.grading R N)
      {x | ¬ (x : PSpace R N) ∈ U}).toIdeal
  have hJ1 : ∀ f ∈ J, Proj.basicOpen (ProjSpace.grading R N) f ≤ U := fun f hf x hx => by
    by_contra hxU
    exact hx ((ProjectiveSpectrum.mem_vanishingIdeal _ f).1 hf x hxU)
  have hJ2 : ∀ g, Proj.basicOpen (ProjSpace.grading R N) g ≤ U → g ∈ J := fun g hg =>
    (ProjectiveSpectrum.mem_vanishingIdeal _ g).2 fun x hxU => by
      by_contra hgx
      exact hxU (hg hgx)
  have hgen : ∀ x : PSpace R N, x ∈ U → ∃ d, 0 < d ∧ ∃ g ∈ ProjSpace.grading R N d, g ∈ J ∧
      g ∉ (ProjectiveSpectrum.asHomogeneousIdeal (𝒜 := ProjSpace.grading R N) x).toIdeal := by
    intro x hxU
    obtain ⟨_, ⟨r, rfl⟩, hxr, hrU⟩ :=
      TopologicalSpace.Opens.isBasis_iff_nbhd.1 (Proj.isBasis_basicOpen (ProjSpace.grading R N)) hxU
    rw [Proj.basicOpen_eq_iSup_proj] at hxr
    obtain ⟨k, hk⟩ := TopologicalSpace.Opens.mem_iSup.1 hxr
    have hkU : Proj.basicOpen (ProjSpace.grading R N) (GradedRing.proj (ProjSpace.grading R N) k r) ≤ U := by
      refine le_trans ?_ hrU
      rw [Proj.basicOpen_eq_iSup_proj (ProjSpace.grading R N) r]
      exact le_iSup (fun k => Proj.basicOpen (ProjSpace.grading R N) (GradedRing.proj (ProjSpace.grading R N) k r)) k
    obtain ⟨j, hj⟩ := ProjSpace.exists_mem_chart R N x
    refine ⟨k + 1, Nat.succ_pos k, GradedRing.proj (ProjSpace.grading R N) k r * MvPolynomial.X j, ?_, ?_, ?_⟩
    · refine SetLike.mul_mem_graded ?_ (ProjSpace.X_mem R N j)
      rw [GradedRing.proj_apply]
      exact SetLike.coe_mem _
    · apply hJ2
      rw [Proj.basicOpen_mul]
      exact inf_le_left.trans hkU
    · show x ∈ Proj.basicOpen (ProjSpace.grading R N) _
      rw [Proj.basicOpen_mul]
      exact ⟨hk, hj⟩
  obtain ⟨d, hd, f, hf, hfJ, hfP⟩ := exists_homogeneous_mem_not_mem_finset_primes (ProjSpace.grading R N) J
    (hs.toFinset.image fun x : PSpace R N =>
      (ProjectiveSpectrum.asHomogeneousIdeal (𝒜 := ProjSpace.grading R N) x).toIdeal)
    (by
      intro p hp
      obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 hp
      exact ⟨ProjectiveSpectrum.isPrime _, HomogeneousIdeal.isHomogeneous _,
        hgen x (hU (hs.mem_toFinset.1 hx))⟩)
  have hfh : f.IsHomogeneous d := (MvPolynomial.mem_homogeneousSubmodule d f).1 hf
  refine ⟨d, hd, ProjSpace.formSec d f hfh, ?_, ?_, ?_⟩
  · intro x hx
    rw [ProjSpace.nonzeroLocus_formSec]
    exact hfP _ (Finset.mem_image_of_mem _ (hs.mem_toFinset.2 hx))
  · rw [ProjSpace.nonzeroLocus_formSec]
    exact hJ1 f hfJ
  · rw [ProjSpace.nonzeroLocus_formSec]
    exact Proj.isAffineOpen_basicOpen _ f hf hd

/- English proof (translation)
Take `⟨N, i, hi, hqc, he⟩` from `h`. Establish `: IsImmersion i` using `hi`. Establish `: QuasiCompact i` using `hqc`. Establish `hPc : CompactSpace (PSpace R N)`. Establish `hc : IsCompact (⋃ k, (ProjSpace.chart R N k : Set (PSpace R N)))` using `isCompact_iUnion fun k => (ProjSpace.isAffineOpen_chart R N k).isCompact`.

Rewrite `hc` using `[← TopologicalSpace.Opens.coe_iSup, ProjSpace.iSup_chart]`. Conclude with `⟨by simpa using hc⟩`. Establish `hXc : CompactSpace X` using `QuasiCompact.compactSpace_of_compactSpace i`. Establish `hmem : ∀ x, i x ∈ i.coborderRange` using `fun x => by`. Conclude with `subset_coborder (Set.mem_range_self x)`.

Establish `haffpre : ∀ D : (PSpace R N).Opens, D ≤ i.coborderRange → IsAffineOpen D → IsAffineOpen (i ⁻¹ᵁ D)`. Introduce `D hD hA`. Establish `h1 : IsAffineOpen (i.coborderRange.ι ⁻¹ᵁ D)` using `hA.preimage_of_isOpenImmersion _ (by rwa [Scheme.Opens.opensRange_ι])`. Establish `h2` using `h1.preimage i.liftCoborder`. Rewrite `h2` using `[← Scheme.Hom.comp_preimage, i.liftCoborder_ι]`. Then use the resulting hypothesis.

Establish `key : ∀ x : X, ∃ n, 1 ≤ n ∧ ∃ t : (lbPow (ProjSpace.O1 R N) n).Sec, Set.range (fun g => i ((ρ g).hom x)) ⊆ Out.nonzeroLocus t ∧ Out.nonzeroLocus t ≤ i.coborderRange ∧ IsAffineOpen (Out.nonzeroLocus t)` using `fun x => exists_sec_nonzeroLocus_le (Set.finite_range _) _ (by rintro _ ⟨g, rfl⟩; exact hmem _)`. Use `choose n hn t hts htU hta using key`. Set `W : X → Set X` to `fun x => {y | ∀ g, i ((ρ g).hom y) ∈ Out.nonzeroLocus (t x)}`. Establish `hWo : ∀ x, IsOpen (W x)` using `fun x => by`. Establish `hW : W x = ⋂ g, ((ρ g).hom ≫ i) ⁻¹' (Out.nonzeroLocus (t x) : Set (PSpace R N))`.

Use extensionality with `y`. Simplify using `[W]`. Rewrite using `[hW]`. Conclude with `isOpen_iInter_of_finite fun g => (Out.nonzeroLocus (t x)).isOpen.preimage ((ρ g).hom ≫ i).continuous`. Establish `hWx : ∀ x, x ∈ W x` using `fun x g => hts x ⟨g, rfl⟩`.

Take `⟨F, hF⟩` from `isCompact_univ.elim_finite_subcover W hWo (fun y _ => Set.mem_iUnion.2 ⟨y, hWx y⟩)`. Set `M` to `∏ x ∈ F, n x`. Establish `hdvd : ∀ x ∈ F, n x ∣ M` using `fun x hx => Finset.dvd_prod_of_mem n hx`. Establish `hMpos : 0 < M` using `Finset.prod_pos fun x _ => hn x`. Set `e` to `F.equivFin`.

Set `sec : F → (lbPow (ProjSpace.O1 R N) M).Sec` to `fun x => GlobalTheory.secCast (Nat.mul_div_cancel' (hdvd x x.2)) (GlobalTheory.secPow (t x) (M / n x))`. Establish `hloc : ∀ x : F, Out.nonzeroLocus (GlobalTheory.secPull (sec x) i) = i ⁻¹ᵁ Out.nonzeroLocus (t x)` using `fun x => by`. Rewrite using `[GlobalTheory.nonzeroLocus_secPull, GlobalTheory.nonzeroLocus_secCast, GlobalTheory.nonzeroLocus_secPow]`. Conclude with `Nat.div_pos (Nat.le_of_dvd hMpos (hdvd x x.2)) (hn x)`. Use `⟨(lbPow (ProjSpace.O1 R N) M).pull i, F.card, fun k => GlobalTheory.secPull (sec (e.symm k)) i, pull_isLB (GlobalTheory.isLB_lbPow (GlobalTheory.ProjSpace.O1_isLB R N) M) i, fun k => ?_, fun y => ?_⟩` and prove the remaining obligations.

Rewrite using `[hloc]`. Conclude with `haffpre _ (htU _) (hta _)`. Take `⟨x, hxF, hy⟩ : ∃ x ∈ F, y ∈ W x` from `by simpa using hF (Set.mem_univ y)`. Use `⟨e ⟨x, hxF⟩, fun g => ?_⟩` and prove the remaining obligations. Simplify using `only [Equiv.symm_apply_apply]`.

Rewrite using `[hloc]`. Conclude with `hy g`.
-/
theorem exists_sections_orbit_subset {Γ : Type} [Group Γ] [Finite Γ] {R : Type} [CommRing R] {X : Scheme.{0}}
    {s : X ⟶ Sp R} (ρ : Γ →* Aut X) (h : IsQProjOver s) :
    ∃ (L : LB X) (n : ℕ) (σ : Fin n → LB.Sec L), L.IsLB ∧ (∀ i, IsAffineOpen (Out.nonzeroLocus (σ i))) ∧
      ∀ x : X, ∃ i, ∀ g, (ρ g).hom x ∈ Out.nonzeroLocus (σ i) := by
  classical
  obtain ⟨N, i, hi, hqc, he⟩ := h
  have : IsImmersion i := hi
  have : QuasiCompact i := hqc
  have hPc : CompactSpace (PSpace R N) := by
    have hc : IsCompact (⋃ k, (ProjSpace.chart R N k : Set (PSpace R N))) :=
      isCompact_iUnion fun k => (ProjSpace.isAffineOpen_chart R N k).isCompact
    rw [← TopologicalSpace.Opens.coe_iSup, ProjSpace.iSup_chart] at hc
    exact ⟨by simpa using hc⟩
  have hXc : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace i
  have hmem : ∀ x, i x ∈ i.coborderRange := fun x => by
    exact subset_coborder (Set.mem_range_self x)
  have haffpre : ∀ D : (PSpace R N).Opens, D ≤ i.coborderRange → IsAffineOpen D →
      IsAffineOpen (i ⁻¹ᵁ D) := by
    intro D hD hA
    have h1 : IsAffineOpen (i.coborderRange.ι ⁻¹ᵁ D) :=
      hA.preimage_of_isOpenImmersion _ (by rwa [Scheme.Opens.opensRange_ι])
    have h2 := h1.preimage i.liftCoborder
    rwa [← Scheme.Hom.comp_preimage, i.liftCoborder_ι] at h2
  have key : ∀ x : X, ∃ n, 1 ≤ n ∧ ∃ t : (lbPow (ProjSpace.O1 R N) n).Sec,
      Set.range (fun g => i ((ρ g).hom x)) ⊆ Out.nonzeroLocus t ∧
        Out.nonzeroLocus t ≤ i.coborderRange ∧ IsAffineOpen (Out.nonzeroLocus t) :=
    fun x => exists_sec_nonzeroLocus_le (Set.finite_range _) _ (by rintro _ ⟨g, rfl⟩; exact hmem _)
  choose n hn t hts htU hta using key
  let W : X → Set X := fun x => {y | ∀ g, i ((ρ g).hom y) ∈ Out.nonzeroLocus (t x)}
  have hWo : ∀ x, IsOpen (W x) := fun x => by
    have hW : W x = ⋂ g, ((ρ g).hom ≫ i) ⁻¹' (Out.nonzeroLocus (t x) : Set (PSpace R N)) := by
      ext y
      simp [W]
    rw [hW]
    exact isOpen_iInter_of_finite fun g =>
      (Out.nonzeroLocus (t x)).isOpen.preimage ((ρ g).hom ≫ i).continuous
  have hWx : ∀ x, x ∈ W x := fun x g => hts x ⟨g, rfl⟩
  obtain ⟨F, hF⟩ := isCompact_univ.elim_finite_subcover W hWo
    (fun y _ => Set.mem_iUnion.2 ⟨y, hWx y⟩)
  let M := ∏ x ∈ F, n x
  have hdvd : ∀ x ∈ F, n x ∣ M := fun x hx => Finset.dvd_prod_of_mem n hx
  have hMpos : 0 < M := Finset.prod_pos fun x _ => hn x
  let e := F.equivFin
  let sec : F → (lbPow (ProjSpace.O1 R N) M).Sec := fun x =>
    GlobalTheory.secCast (Nat.mul_div_cancel' (hdvd x x.2)) (GlobalTheory.secPow (t x) (M / n x))
  have hloc : ∀ x : F, Out.nonzeroLocus (GlobalTheory.secPull (sec x) i) = i ⁻¹ᵁ Out.nonzeroLocus (t x) :=
    fun x => by
      rw [GlobalTheory.nonzeroLocus_secPull, GlobalTheory.nonzeroLocus_secCast, GlobalTheory.nonzeroLocus_secPow]
      exact Nat.div_pos (Nat.le_of_dvd hMpos (hdvd x x.2)) (hn x)
  refine ⟨(lbPow (ProjSpace.O1 R N) M).pull i, F.card, fun k => GlobalTheory.secPull (sec (e.symm k)) i,
    pull_isLB (GlobalTheory.isLB_lbPow (GlobalTheory.ProjSpace.O1_isLB R N) M) i, fun k => ?_, fun y => ?_⟩
  · rw [hloc]
    exact haffpre _ (htU _) (hta _)
  · obtain ⟨x, hxF, hy⟩ : ∃ x ∈ F, y ∈ W x := by simpa using hF (Set.mem_univ y)
    refine ⟨e ⟨x, hxF⟩, fun g => ?_⟩
    simp only [Equiv.symm_apply_apply]
    rw [hloc]
    exact hy g

/- English proof (translation)
Take `⟨L, n, σ, hL, haff, hcov⟩` from `exists_sections_orbit_subset ρ h`. Establish `hsep : X.IsSeparated`. Take `⟨N, i, hi, hqc, he⟩` from `h`. Establish `: IsImmersion i` using `hi`. Establish `hs : IsSeparated s`.

Rewrite using `[← he]`. Use `infer_instance`. Conclude with `⟨by rw [← terminal.comp_from s]; infer_instance⟩`. Take `⟨L', m, σ', hL', haff', hcov'⟩` from `GlobalTheory.QuotientNorm.exists_affine_cover_of_quotient Γ X Y ρ π ⟨hq.isAffineHom, hq.comp_eq, fun V => ⟨hq.app_injective V, fun f hf => hq.mem_range_app V f (fun g => ⟨hq.preimage_le V g, hf g _⟩)⟩⟩ hsep L n σ hL haff hcov`. Use `⟨L', ⟨hL', ?_, ?_⟩⟩` and prove the remaining obligations.

Establish `hc : IsCompact (⋃ i, (Out.nonzeroLocus (σ' i) : Set Y))` using `isCompact_iUnion fun i => (haff' i).isCompact`. Rewrite `hc` using `[← TopologicalSpace.Opens.coe_iSup, hcov']`. Conclude with `⟨by simpa using hc⟩`. Introduce `y`. Establish `hy : y ∈ ⨆ i, Out.nonzeroLocus (σ' i)` using `by rw [hcov']; trivial`.

Take `⟨i, hi⟩` from `TopologicalSpace.Opens.mem_iSup.mp hy`. Use `⟨1, le_rfl, GlobalTheory.secToPow (σ' i) 1, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[GlobalTheory.nonzeroLocus_secToPow (σ' i) le_rfl]`. Conclude with `hi`. Rewrite using `[GlobalTheory.nonzeroLocus_secToPow (σ' i) le_rfl]`.

Conclude with `haff' i`.
-/
theorem exists_isAmpleLB_of_isAffineQuotient {Γ : Type} [Group Γ] [Finite Γ] {R : Type} [CommRing R]
    {X Y : Scheme.{0}} {s : X ⟶ Sp R} {ρ : Γ →* Aut X} {π : X ⟶ Y} (hq : IsAffineQuotient ρ π)
    (h : IsQProjOver s) : ∃ L : LB Y, IsAmpleLB L := by
  obtain ⟨L, n, σ, hL, haff, hcov⟩ := exists_sections_orbit_subset ρ h
  have hsep : X.IsSeparated := by
    obtain ⟨N, i, hi, hqc, he⟩ := h
    have : IsImmersion i := hi
    have hs : IsSeparated s := by
      rw [← he]
      infer_instance
    exact ⟨by rw [← terminal.comp_from s]; infer_instance⟩
  obtain ⟨L', m, σ', hL', haff', hcov'⟩ := GlobalTheory.QuotientNorm.exists_affine_cover_of_quotient Γ X Y ρ π
    ⟨hq.isAffineHom, hq.comp_eq, fun V => ⟨hq.app_injective V, fun f hf => hq.mem_range_app V f
      (fun g => ⟨hq.preimage_le V g, hf g _⟩)⟩⟩ hsep L n σ hL haff hcov
  refine ⟨L', ⟨hL', ?_, ?_⟩⟩
  · have hc : IsCompact (⋃ i, (Out.nonzeroLocus (σ' i) : Set Y)) :=
      isCompact_iUnion fun i => (haff' i).isCompact
    rw [← TopologicalSpace.Opens.coe_iSup, hcov'] at hc
    exact ⟨by simpa using hc⟩
  · intro y
    have hy : y ∈ ⨆ i, Out.nonzeroLocus (σ' i) := by rw [hcov']; trivial
    obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.mp hy
    refine ⟨1, le_rfl, GlobalTheory.secToPow (σ' i) 1, ?_, ?_⟩
    · rw [GlobalTheory.nonzeroLocus_secToPow (σ' i) le_rfl]; exact hi
    · rw [GlobalTheory.nonzeroLocus_secToPow (σ' i) le_rfl]; exact haff' i

/- English proof (translation)
Introduce `K _ X Y π sY Ga _ ρ hG hs hl hq`. Establish `: Finite Ga` using `hG.finite`. Set `ρ' : Ga →* Aut X` to `{ toFun := fun a => ⟨ρ a⁻¹, ρ a, by rw [← hG.mul, inv_mul_cancel, hG.one], by rw [← hG.mul, mul_inv_cancel, hG.one]⟩ map_one' := by ext1 show ρ 1⁻¹ = _`. Rewrite using `[inv_one, hG.one]`. Both sides reduce to the same expression.

Use the proof step `map_mul' := fun a c => by ext1 show ρ (a * c)⁻¹ = ρ c⁻¹ ≫ ρ a⁻¹`. Rewrite using `[mul_inv_rev, hG.mul] }`. Establish `hρ' : ∀ a, (ρ' a).hom = ρ a⁻¹` using `fun a => rfl`. Establish `: OrbitsInAffineOpens ρ'` using `OrbitsInAffineOpens.of_isQProjOver hq ρ'`. Take `⟨Y', q, hQ⟩` from `(exists_isAffineQuotient_iff ρ').mpr inferInstance`.

Take `⟨L', hL'⟩` from `exists_isAmpleLB_of_isAffineQuotient hQ hq`. Establish `hqi : ∀ a, ρ a ≫ q = q` using `fun a => by`. Use `hQ.comp_eq a⁻¹` as an intermediate fact. Rewrite `this` using `[hρ', inv_inv]`. Then use the resulting hypothesis. Take `⟨f, hf, -⟩` from `GlobalTheory.ZM.IsGaloisCover.existsUnique_desc hG q hqi`.

Establish `hπi : ∀ a, (ρ' a).hom ≫ π = π` using `fun a => by rw [hρ']; exact hG.inv _`. Establish `hfg : f ≫ hQ.desc π hπi = 𝟙 Y`. Take `⟨u, -, hu⟩` from `GlobalTheory.ZM.IsGaloisCover.existsUnique_desc hG π hG.inv`. Establish `h1` using `hu (f ≫ hQ.desc π hπi) (by show π ≫ f ≫ hQ.desc π hπi = π`. Rewrite using `[← Category.assoc, hf, hQ.comp_desc])`.

Establish `h2` using `hu (𝟙 Y) (by show π ≫ 𝟙 Y = π`. Conclude with `Category.comp_id π)`. Rewrite using `[h1, h2]`. Establish `hgf : hQ.desc π hπi ≫ f = 𝟙 Y'` using `hQ.hom_ext (by rw [← Category.assoc, hQ.comp_desc, hf, Category.comp_id])`. Establish `: IsIso f` using `⟨⟨hQ.desc π hπi, hfg, hgf⟩⟩`.

Establish `hA : IsAmpleLB (L'.pull f)` using `GlobalTheory.IsAmpleLB.pull_of_isFinite hL' f`. Use `hl` as an intermediate fact. Conclude with `GlobalTheory.IsAmpleLB.isQProjOver hA sY`.
-/
theorem isQProjOver_of_isGaloisCover : ∀ (K : Type) [Field K] (X Y : Scheme.{0}) (π : X ⟶ Y) (sY : Y ⟶ Sp K) (Ga : Type) [Group Ga] (ρ : Ga → (X ⟶ X)), IsGaloisCover Ga ρ π → IsSeparated sY → LocallyOfFiniteType sY → IsQProjOver (π ≫ sY) → IsQProjOver sY := by
  intro K _ X Y π sY Ga _ ρ hG hs hl hq
  have : Finite Ga := hG.finite
  let ρ' : Ga →* Aut X :=
    { toFun := fun a => ⟨ρ a⁻¹, ρ a, by rw [← hG.mul, inv_mul_cancel, hG.one], by rw [← hG.mul, mul_inv_cancel, hG.one]⟩
      map_one' := by
        ext1
        show ρ 1⁻¹ = _
        rw [inv_one, hG.one]
        rfl
      map_mul' := fun a c => by
        ext1
        show ρ (a * c)⁻¹ = ρ c⁻¹ ≫ ρ a⁻¹
        rw [mul_inv_rev, hG.mul] }
  have hρ' : ∀ a, (ρ' a).hom = ρ a⁻¹ := fun a => rfl
  have : OrbitsInAffineOpens ρ' := OrbitsInAffineOpens.of_isQProjOver hq ρ'
  obtain ⟨Y', q, hQ⟩ := (exists_isAffineQuotient_iff ρ').mpr inferInstance
  obtain ⟨L', hL'⟩ := exists_isAmpleLB_of_isAffineQuotient hQ hq
  have hqi : ∀ a, ρ a ≫ q = q := fun a => by
    have := hQ.comp_eq a⁻¹
    rwa [hρ', inv_inv] at this
  obtain ⟨f, hf, -⟩ := GlobalTheory.ZM.IsGaloisCover.existsUnique_desc hG q hqi
  have hπi : ∀ a, (ρ' a).hom ≫ π = π := fun a => by rw [hρ']; exact hG.inv _
  have hfg : f ≫ hQ.desc π hπi = 𝟙 Y := by
    obtain ⟨u, -, hu⟩ := GlobalTheory.ZM.IsGaloisCover.existsUnique_desc hG π hG.inv
    have h1 := hu (f ≫ hQ.desc π hπi) (by
      show π ≫ f ≫ hQ.desc π hπi = π
      rw [← Category.assoc, hf, hQ.comp_desc])
    have h2 := hu (𝟙 Y) (by
      show π ≫ 𝟙 Y = π
      exact Category.comp_id π)
    rw [h1, h2]
  have hgf : hQ.desc π hπi ≫ f = 𝟙 Y' :=
    hQ.hom_ext (by rw [← Category.assoc, hQ.comp_desc, hf, Category.comp_id])
  have : IsIso f := ⟨⟨hQ.desc π hπi, hfg, hgf⟩⟩
  have hA : IsAmpleLB (L'.pull f) := GlobalTheory.IsAmpleLB.pull_of_isFinite hL' f
  have := hl
  exact GlobalTheory.IsAmpleLB.isQProjOver hA sY

end GlobalTheory.GaloisQuotient

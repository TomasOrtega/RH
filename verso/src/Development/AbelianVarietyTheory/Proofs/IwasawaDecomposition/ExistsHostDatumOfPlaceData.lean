import Mathlib
import Formalism.LocalToGlobal.UnitaryNorms.DatumS
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.HostPins
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RayFieldTopMaximalUnramified
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ClassGroupCoprimeRepresentative
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2 Formalism.L2.Host GlobalTheory.Published GlobalTheory.Mem.HD
open NumberField IsDedekindDomain
open scoped nonZeroDivisors

namespace GlobalTheory.HostDatumExists

/- English proof (translation)
Use `Fintype.ofFinite ι` as an intermediate fact. Use `set m : Ideal (𝓞 K) := (∏ i, Ideal.span {((n i : ℕ) : 𝓞 K)}) * ∏ 𝔭 ∈ hS.toFinset, 𝔭.asIdeal with hm`. Establish `hm0 : m ≠ ⊥`. Use `mul_ne_zero (Finset.prod_ne_zero_iff.mpr fun i _ => ?_) (Finset.prod_ne_zero_iff.mpr fun 𝔭 _ => 𝔭.ne_bot)` and prove the remaining obligations. Rewrite using `[Ideal.zero_eq_bot, Ne, Ideal.span_singleton_eq_bot]`.

Conclude with `hn i` after adjusting the coercions. Take `⟨I, hI, hsup⟩` from `GlobalTheory.exists_integral_ideal_in_class_coprime K m hm0 c`. Use `⟨I, hI, fun i => ?_, fun 𝔭 h𝔭 hle => 𝔭.isPrime.ne_top ?_⟩` and prove the remaining obligations. Rewrite using `[Ideal.isCoprime_iff_sup_eq, ← top_le_iff, ← hsup]`. Use `sup_le_sup_left (Ideal.le_of_dvd (Dvd.dvd.mul_right ?_ _)) _` and prove the remaining obligations.

Conclude with `Finset.dvd_prod_of_mem (fun i => Ideal.span {((n i : ℕ) : 𝓞 K)}) (Finset.mem_univ i)`. Establish `h : m ≤ 𝔭.asIdeal` using `Ideal.le_of_dvd (Dvd.dvd.mul_left (Finset.dvd_prod_of_mem (fun q : HeightOneSpectrum (𝓞 K) => q.asIdeal) (hS.mem_toFinset.mpr h𝔭)) _)`. Conclude with `top_le_iff.mp (hsup ▸ sup_le hle h)`.
-/
theorem exists_reps (K : Type) [Field K] [NumberField K] {ι : Type} [Finite ι] (n : ι → ℕ) (hn : ∀ i, n i ≠ 0)
    (S : Set (HeightOneSpectrum (𝓞 K))) (hS : S.Finite) (c : ClassGroup (𝓞 K)) :
    ∃ I : (Ideal (𝓞 K))⁰, ClassGroup.mk0 I = c ∧
      (∀ i, IsCoprime (I : Ideal (𝓞 K)) (Ideal.span {((n i : ℕ) : 𝓞 K)})) ∧
      ∀ 𝔭 ∈ S, ¬ (I : Ideal (𝓞 K)) ≤ 𝔭.asIdeal := by
  classical
  have := Fintype.ofFinite ι
  set m : Ideal (𝓞 K) := (∏ i, Ideal.span {((n i : ℕ) : 𝓞 K)}) * ∏ 𝔭 ∈ hS.toFinset, 𝔭.asIdeal with hm
  have hm0 : m ≠ ⊥ := by
    refine mul_ne_zero (Finset.prod_ne_zero_iff.mpr fun i _ => ?_) (Finset.prod_ne_zero_iff.mpr fun 𝔭 _ => 𝔭.ne_bot)
    rw [Ideal.zero_eq_bot, Ne, Ideal.span_singleton_eq_bot]
    exact_mod_cast hn i
  obtain ⟨I, hI, hsup⟩ := GlobalTheory.exists_integral_ideal_in_class_coprime K m hm0 c
  refine ⟨I, hI, fun i => ?_, fun 𝔭 h𝔭 hle => 𝔭.isPrime.ne_top ?_⟩
  · rw [Ideal.isCoprime_iff_sup_eq, ← top_le_iff, ← hsup]
    refine sup_le_sup_left (Ideal.le_of_dvd (Dvd.dvd.mul_right ?_ _)) _
    exact Finset.dvd_prod_of_mem (fun i => Ideal.span {((n i : ℕ) : 𝓞 K)}) (Finset.mem_univ i)
  · have h : m ≤ 𝔭.asIdeal :=
      Ideal.le_of_dvd (Dvd.dvd.mul_left
        (Finset.dvd_prod_of_mem (fun q : HeightOneSpectrum (𝓞 K) => q.asIdeal) (hS.mem_toFinset.mpr h𝔭)) _)
    exact top_le_iff.mp (hsup ▸ sup_le hle h)

/- English proof (translation)
Introduce `x hx`. Establish `: Algebra.IsAlgebraic ℚ Qb` using `AlgebraicClosure.isAlgebraic ℚ`. Establish `h1 : IsAlgebraic ℤ x` using `(IsFractionRing.isAlgebraic_iff ℤ ℚ Qb).mpr (Algebra.IsAlgebraic.isAlgebraic x)`. Take `⟨a, ha, hi⟩` from `h1.exists_integral_multiple`. Establish `h2 : a • x ∈ B` using `h _ (zsmul_mem hx a) hi`.

Establish `h3 : x = ((a : Qb))⁻¹ * (a • x)`. Establish `: (a : Qb) ≠ 0` using `by exact_mod_cast ha`. Rewrite using `[zsmul_eq_mul, inv_mul_cancel_left₀ this]`. Rewrite using `[h3]`. Conclude with `mul_mem (inv_mem (intCast_mem B a)) h2`.
-/
theorem le_of_integral {A B : Formalism.L2.Host.Fld} (h : ∀ x ∈ A, IsIntegral ℤ x → x ∈ B) : A ≤ B := by
  intro x hx
  have : Algebra.IsAlgebraic ℚ Qb := AlgebraicClosure.isAlgebraic ℚ
  have h1 : IsAlgebraic ℤ x := (IsFractionRing.isAlgebraic_iff ℤ ℚ Qb).mpr (Algebra.IsAlgebraic.isAlgebraic x)
  obtain ⟨a, ha, hi⟩ := h1.exists_integral_multiple
  have h2 : a • x ∈ B := h _ (zsmul_mem hx a) hi
  have h3 : x = ((a : Qb))⁻¹ * (a • x) := by
    have : (a : Qb) ≠ 0 := by exact_mod_cast ha
    rw [zsmul_eq_mul, inv_mul_cancel_left₀ this]
  rw [h3]
  exact mul_mem (inv_mem (intCast_mem B a)) h2

/- English proof (translation)
Introduce `hA D L hT Gi Gl K Y cX ex T hP B`. Take `⟨M, hM, hO⟩` from `hP.hilb`. Establish `hφ : T.host.fr.ι.comp T.host.fr.j.toRingHom = D.host.φ₀` using `RingHom.ext T.host.fr.phi0`. Establish `hE : IsTotallyComplex D.host.E` using `inferInstance`. Take `⟨nf, h1, h2, h3⟩` from `GlobalTheory.HilbertInClosure.rayField_top_maximal_unramified hA D.host.E T.host.fr.j T.host.fr.ι M (by rw [hφ]; exact hM)`.

Rewrite `h1`, `h3` using `[T.host.fr.range]`. Establish `hS : (⋃ w ∈ {w | D.what₂.muAt w ≠ D.what₂.mu0}, (fun v : HeightOneSpectrum (𝓞 D.host.E) => v.under (𝓞 D.host.K)) '' (ex.nch.Q w : Set (PlE D.host))).Finite` using `hP.fin.biUnion fun w _ => (ex.nch.Q w).finite_toSet.image _`. Use `choose rep hrep hcop hpr using exists_reps D.host.K (fun u => (D.mem u).A.T) (fun u => (D.mem u).A.T_prime.ne_zero) _ hS`. Establish `hgal : IsGalois ℚ T.host.LLQ`. Use `hP.gal` as an intermediate fact.

Conclude with `IsGalois.of_algEquiv (AlgEquiv.ofInjectiveField T.host.jLL.toRatAlgHom)`. Use `⟨{ d3b := B Tu_g := hP.Tu_g Qw_Tu := hP.Qw_Tu clsK := ⟨rep, hrep⟩ clsK_Tu := hcop clsK_Qw := fun w hw v hv c => hpr c _ (Set.mem_biUnion hw ⟨v, hv, rfl⟩) LLgal := hgal HE := qb T.host.fr.ι M HE_fd := inferInstance HE_hilb := ⟨h1, h2, fun L' _ hL hU => @h3 L' {} hL hU⟩ HE_le := le …` and prove the remaining obligations. Take `⟨y, hy⟩` from `hO (T.host.fr.ι x) hx (hi.map T.host.fr.ι.toIntAlgHom)`. Use `((T.what₂.O.range x).1 ⟨y, T.host.fr.ι.injective ?_⟩).1` and prove the remaining obligations. Rewrite using `[T.host.embLL, hy]`.
-/
theorem exists_hostDatum : GlobalArtinReciprocity → ∀ (D : D7) (L : SizeData₂ D) (hT : GatTies D) (Gi : G.Inst D L) (Gl : G.LatInst D) (K : G.Consts) (Y : DivX D) (cX : ExtraC) (ex : Extra D L hT Gi Gl K Y cX) (T : LinkedFamilyData ex), HostPins D ex.nch → ∀ B : PlacesOverCommonPrime D.host, ∃ hd : HostDatumC T, hd.d3b = B := by
  intro hA D L hT Gi Gl K Y cX ex T hP B
  obtain ⟨M, hM, hO⟩ := hP.hilb
  have hφ : T.host.fr.ι.comp T.host.fr.j.toRingHom = D.host.φ₀ := RingHom.ext T.host.fr.phi0
  have hE : IsTotallyComplex D.host.E := inferInstance
  obtain ⟨nf, h1, h2, h3⟩ := GlobalTheory.HilbertInClosure.rayField_top_maximal_unramified hA D.host.E T.host.fr.j T.host.fr.ι M
    (by rw [hφ]; exact hM)
  rw [T.host.fr.range] at h1 h3
  have hS : (⋃ w ∈ {w | D.what₂.muAt w ≠ D.what₂.mu0},
      (fun v : HeightOneSpectrum (𝓞 D.host.E) => v.under (𝓞 D.host.K)) '' (ex.nch.Q w : Set (PlE D.host))).Finite :=
    hP.fin.biUnion fun w _ => (ex.nch.Q w).finite_toSet.image _
  choose rep hrep hcop hpr using exists_reps D.host.K (fun u => (D.mem u).A.T) (fun u => (D.mem u).A.T_prime.ne_zero) _ hS
  have hgal : IsGalois ℚ T.host.LLQ := by
    have := hP.gal
    exact IsGalois.of_algEquiv (AlgEquiv.ofInjectiveField T.host.jLL.toRatAlgHom)
  refine ⟨{ d3b := B
            Tu_g := hP.Tu_g
            Qw_Tu := hP.Qw_Tu
            clsK := ⟨rep, hrep⟩
            clsK_Tu := hcop
            clsK_Qw := fun w hw v hv c => hpr c _ (Set.mem_biUnion hw ⟨v, hv, rfl⟩)
            LLgal := hgal
            HE := qb T.host.fr.ι M
            HE_fd := inferInstance
            HE_hilb := ⟨h1, h2, fun L' _ hL hU => @h3 L' {} hL hU⟩
            HE_le := le_of_integral fun x hx hi => ?_ }, rfl⟩
  obtain ⟨y, hy⟩ := hO (T.host.fr.ι x) hx (hi.map T.host.fr.ι.toIntAlgHom)
  refine ((T.what₂.O.range x).1 ⟨y, T.host.fr.ι.injective ?_⟩).1
  rw [T.host.embLL, hy]

end GlobalTheory.HostDatumExists

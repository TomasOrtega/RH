import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsPotential
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.OneSubPhiOntoOfFilZero
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BhattScholzeCrystallineLattices
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RestrictCrystallineDeRhamFiniteExt

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per GlobalTheory.IndefiniteRowSideFullHecke.CrystallineSubrepresentation GlobalTheory.RegularRing

namespace GlobalTheory.Per.DcrisSpan

open GlobalTheory.Per.TiedRestrict

variable {l : ℕ} [Fact l.Prime] {P : LocPrime l} {AI : LocAinf l P}
variable {K K' LL : FinExt l} (h : K.1 ≤ K'.1) {V : Type} [AddCommGroup V] [Module ↥LL.1 V] [Module ℚ_[l] V]
  [IsScalarTower ℚ_[l] ↥LL.1 V] [FiniteDimensional ↥LL.1 V] (ρ : Representation ↥LL.1 ↥(GK K) V)

/- English proof (translation)
Use `LL.2` as an intermediate fact. Establish `: IsDomain P.R.B` using `isDomain_of_tied T K`. Establish `: FiniteDimensional ℚ_[l] V` using `Module.Finite.trans ↥LL.1 V`. Establish `hc'` using `isCrys_restrict h ρ T hc`. Take `⟨h1, -⟩` from `finite_le₀ (P.PD K) (fracInv_of_tied T K) ρ`.

Take `⟨h2, -⟩` from `finite_le₀ (P.PD K') (fracInv_of_tied T K') (ρ.comp (Subgroup.inclusion (GK_le h)))`. Rewrite `hc`, `hc'` using `[isCrys_iff_finrank]`. Set `e` to `Module.finBasisOfFinrankEq ↥(K0 K) _ hc`. Establish `hB` using `indepB (P.PD K) (fracInv_of_tied T K) ρ e e.linearIndependent`. Set `d : Fin (Module.finrank ℚ_[l] V) → ↥(DcrisK₀ (P.PD K') (ρ.comp (Subgroup.inclusion (GK_le h))))` to `fun i => ⟨e i, dcris_le h ρ (e i).2⟩`.

Establish `hd : LinearIndependent ↥(K0 K') d` using `LinearIndependent.of_comp (DcrisK₀ (P.PD K') (ρ.comp (Subgroup.inclusion (GK_le h)))).subtype (hB.restrict_scalars' ↥(K0 K'))`. Establish `htop : Submodule.span ↥(K0 K') (Set.range d) = ⊤` using `Submodule.eq_top_of_finrank_eq (by rw [finrank_span_eq_card hd]; simpa using hc'.symm)`. Introduce `x hx`. Establish `hx' : (⟨x, hx⟩ : ↥(DcrisK₀ (P.PD K') (ρ.comp (Subgroup.inclusion (GK_le h))))) ∈ Submodule.span ↥(K0 K') (Set.range d)`. Rewrite using `[htop]`.

Discharge the goal by the elementary cases of `trivial`. Establish `hm` using `Submodule.apply_mem_span_image_of_mem_span (DcrisK₀ (P.PD K') (ρ.comp (Subgroup.inclusion (GK_le h)))).subtype hx'`. Use `Submodule.span_mono ?_ hm` and prove the remaining obligations. Introduce and unpack `_ ⟨_, ⟨i, rfl⟩, rfl⟩`. Conclude with `(e i).2`.
-/
theorem le_span_restrict (T : LocTied l P AI) (hc : IsCrys (P.PD K) ρ) :
    DcrisK₀ (P.PD K') (ρ.comp (Subgroup.inclusion (GK_le h))) ≤
      Submodule.span ↥(K0 K') (↑(DcrisK₀ (P.PD K) ρ) : Set (P.R.B ⊗[ℚ_[l]] V)) := by
  have := LL.2
  have : IsDomain P.R.B := isDomain_of_tied T K
  have : FiniteDimensional ℚ_[l] V := Module.Finite.trans ↥LL.1 V
  have hc' := isCrys_restrict h ρ T hc
  obtain ⟨h1, -⟩ := finite_le₀ (P.PD K) (fracInv_of_tied T K) ρ
  obtain ⟨h2, -⟩ := finite_le₀ (P.PD K') (fracInv_of_tied T K') (ρ.comp (Subgroup.inclusion (GK_le h)))
  rw [isCrys_iff_finrank] at hc hc'
  let e := Module.finBasisOfFinrankEq ↥(K0 K) _ hc
  have hB := indepB (P.PD K) (fracInv_of_tied T K) ρ e e.linearIndependent
  let d : Fin (Module.finrank ℚ_[l] V) → ↥(DcrisK₀ (P.PD K') (ρ.comp (Subgroup.inclusion (GK_le h)))) :=
    fun i => ⟨e i, dcris_le h ρ (e i).2⟩
  have hd : LinearIndependent ↥(K0 K') d :=
    LinearIndependent.of_comp (DcrisK₀ (P.PD K') (ρ.comp (Subgroup.inclusion (GK_le h)))).subtype
      (hB.restrict_scalars' ↥(K0 K'))
  have htop : Submodule.span ↥(K0 K') (Set.range d) = ⊤ :=
    Submodule.eq_top_of_finrank_eq (by rw [finrank_span_eq_card hd]; simpa using hc'.symm)
  intro x hx
  have hx' : (⟨x, hx⟩ : ↥(DcrisK₀ (P.PD K') (ρ.comp (Subgroup.inclusion (GK_le h))))) ∈
      Submodule.span ↥(K0 K') (Set.range d) := by
    rw [htop]; trivial
  have hm := Submodule.apply_mem_span_image_of_mem_span
    (DcrisK₀ (P.PD K') (ρ.comp (Subgroup.inclusion (GK_le h)))).subtype hx'
  refine Submodule.span_mono ?_ hm
  rintro _ ⟨_, ⟨i, rfl⟩, rfl⟩
  exact (e i).2

/- English proof (translation)
Introduce `l _ P AI hS LL T K K'' h hc`. Establish `eρ : T.ρ.comp (inclG K'') = (T.ρ.comp (inclG K)).comp (Subgroup.inclusion (GK_le h))` using `MonoidHom.ext fun _ => rfl`. Rewrite using `[eρ]`. Conclude with `le_span_restrict h _ hS.some hc`.
-/
theorem dcris_span : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), IsStd P AI →
    ∀ (LL : FinExt l) (T : QLat LL) (K K'' : FinExt l), K.1 ≤ K''.1 → IsCrys (P.PD K) (T.ρ.comp (inclG K)) →
      DcrisK₀ (P.PD K'') (T.ρ.comp (inclG K'')) ≤
        Submodule.span ↥(K0 K'') (↑(DcrisK₀ (P.PD K) (T.ρ.comp (inclG K))) : Set (P.R.B ⊗[ℚ_[l]] T.V)) := by
  intro l _ P AI hS LL T K K'' h hc
  have eρ : T.ρ.comp (inclG K'') = (T.ρ.comp (inclG K)).comp (Subgroup.inclusion (GK_le h)) :=
    MonoidHom.ext fun _ => rfl
  rw [eρ]
  exact le_span_restrict h _ hS.some hc

end GlobalTheory.Per.DcrisSpan

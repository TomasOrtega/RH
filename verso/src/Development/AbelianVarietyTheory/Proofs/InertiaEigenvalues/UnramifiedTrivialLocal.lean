import Mathlib
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NormSubLtOneOfFix
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsUnramifiedCharacter
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FiniteQuotientPow
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsCrystallineIffMemH1f
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FinrankH1fDeRhamStatement
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module

namespace GlobalTheory.UnramifiedTrivial

/- English proof (translation)
Introduce `c hc`. Take `⟨hZ, x, hx⟩` from `hc`. Use `⟨hZ, ?_⟩` and prove the remaining obligations. Take `⟨hcont, hadd⟩` from `hZ`. Use `haveI := LL.2`.

Set `v` to `Module.finBasis ℚ_[l] ↥LL.1`. Establish `hI : ∀ g ∈ IK K, c g = 0` using `fun g hg => by simpa using hx g hg`. Establish `hex : ∀ i, ∃ b : P.R.B, ∀ g : ↥(GK K), P.actQ g b - b = algebraMap ℚ_[l] _ (v.coord i (c g))` using `fun i => GlobalTheory.UnramifiedCrys.exists_rat AI T K (fun g => v.coord i (c g)) ((v.coord i).continuous_of_finiteDimensional.comp hcont) (fun g h => by rw [hadd, map_add]; rfl) (fun g hg => by rw [hI g hg, map_zero])`. Use `choose b hb using hex`. Use `⟨∑ i, v i ⊗ₜ[ℚ_[l]] b i, fun g => ?_⟩` and prove the remaining obligations.

Rewrite using `[map_sum, ← Finset.sum_sub_distrib]`. Use `conv_lhs => rw [← v.sum_repr (c g), TensorProduct.sum_tmul]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Establish `h1 : actVB (P.PD K) (1 : Representation ↥LL.1 ↥(GK K) ↥LL.1) g (v i ⊗ₜ[ℚ_[l]] b i) = v i ⊗ₜ[ℚ_[l]] P.actQ g (b i)`. Rewrite using `[← P.PD_actB]`.

Both sides reduce to the same expression. Rewrite using `[h1, ← TensorProduct.tmul_sub, hb, TensorProduct.smul_tmul, Algebra.algebraMap_eq_smul_one]`. Both sides reduce to the same expression.
-/
theorem unramifiedCocycles_le_blochKatoFinite_trivial {l : ℕ} [Fact l.Prime] {P : LocPrime l} (AI : LocAinf l P)
    (T : LocTied l P AI) (K LL : FinExt l) :
    Z1ur (1 : Representation ↥LL.1 ↥(GK K) ↥LL.1) (IK K) ≤
      finiteCocycles (P.PD K) (1 : Representation ↥LL.1 ↥(GK K) ↥LL.1) := by
  intro c hc
  obtain ⟨hZ, x, hx⟩ := hc
  refine ⟨hZ, ?_⟩
  obtain ⟨hcont, hadd⟩ := hZ
  haveI := LL.2
  let v := Module.finBasis ℚ_[l] ↥LL.1
  have hI : ∀ g ∈ IK K, c g = 0 := fun g hg => by simpa using hx g hg
  have hex : ∀ i, ∃ b : P.R.B, ∀ g : ↥(GK K),
      P.actQ g b - b = algebraMap ℚ_[l] _ (v.coord i (c g)) := fun i =>
    GlobalTheory.UnramifiedCrys.exists_rat AI T K (fun g => v.coord i (c g))
      ((v.coord i).continuous_of_finiteDimensional.comp hcont)
      (fun g h => by rw [hadd, map_add]; rfl) (fun g hg => by rw [hI g hg, map_zero])
  choose b hb using hex
  refine ⟨∑ i, v i ⊗ₜ[ℚ_[l]] b i, fun g => ?_⟩
  rw [map_sum, ← Finset.sum_sub_distrib]
  conv_lhs => rw [← v.sum_repr (c g), TensorProduct.sum_tmul]
  refine Finset.sum_congr rfl fun i _ => ?_
  have h1 : actVB (P.PD K) (1 : Representation ↥LL.1 ↥(GK K) ↥LL.1) g (v i ⊗ₜ[ℚ_[l]] b i) =
      v i ⊗ₜ[ℚ_[l]] P.actQ g (b i) := by
    rw [← P.PD_actB]
    rfl
  rw [h1, ← TensorProduct.tmul_sub, hb, TensorProduct.smul_tmul, Algebra.algebraMap_eq_smul_one]
  rfl

/- English proof (translation)
Take `⟨δ, hδc, hδa, hδI, g₀, hg₀⟩` from `GlobalTheory.UnramZl.exists_unramified_character l K`. Use `haveI := LL.2`. Set `c : ↥(GK K) → ↥LL.1` to `fun g => algebraMap ℚ_[l] ↥LL.1 (δ g)`. Establish `hcc : Continuous c` using `(Algebra.linearMap ℚ_[l] ↥LL.1).continuous_of_finiteDimensional.comp hδc`. Establish `hmem : c ∈ Z1ur (1 : Representation ↥LL.1 ↥(GK K) ↥LL.1) (IK K)`.

Use `⟨⟨hcc, fun g h => ?_⟩, 0, fun g hg => ?_⟩` and prove the remaining obligations. Simplify using `[c, hδa, map_add]`. Simplify using `[c, hδI g hg]`. Introduce `h`. Rewrite `hmem` using `[h]`.

Use `congrFun ((Submodule.mem_bot _).1 hmem) g₀` as an intermediate fact. Conclude with `hg₀ (by simpa [c] using this)`.
-/
theorem Z1ur_ne_bot {l : ℕ} [Fact l.Prime] (K LL : FinExt l) :
    Z1ur (1 : Representation ↥LL.1 ↥(GK K) ↥LL.1) (IK K) ≠ ⊥ := by
  obtain ⟨δ, hδc, hδa, hδI, g₀, hg₀⟩ := GlobalTheory.UnramZl.exists_unramified_character l K
  haveI := LL.2
  let c : ↥(GK K) → ↥LL.1 := fun g => algebraMap ℚ_[l] ↥LL.1 (δ g)
  have hcc : Continuous c :=
    (Algebra.linearMap ℚ_[l] ↥LL.1).continuous_of_finiteDimensional.comp hδc
  have hmem : c ∈ Z1ur (1 : Representation ↥LL.1 ↥(GK K) ↥LL.1) (IK K) := by
    refine ⟨⟨hcc, fun g h => ?_⟩, 0, fun g hg => ?_⟩
    · simp [c, hδa, map_add]
    · simp [c, hδI g hg]
  intro h
  rw [h] at hmem
  have := congrFun ((Submodule.mem_bot _).1 hmem) g₀
  exact hg₀ (by simpa [c] using this)

end GlobalTheory.UnramifiedTrivial

namespace GlobalTheory.UnramifiedTrivial
/- English proof (translation)
Establish `hB1 : B1 (1 : Representation ↥LL.1 ↥(GK K) ↥LL.1) = ⊥`. Rewrite using `[eq_bot_iff]`. Introduce and unpack `_ ⟨x, rfl⟩`. Use extensionality with `g`. Simplify using `[cob]`.

Establish `hc : (B1 (1 : Representation ↥LL.1 ↥(GK K) ↥LL.1)).comap (finiteCocycles (P.PD K) (1 : Representation ↥LL.1 ↥(GK K) ↥LL.1)).subtype = ⊥`. Rewrite using `[hB1, Submodule.comap_bot, Submodule.ker_subtype]`. Conclude with `(Submodule.quotEquivOfEqBot _ hc).finrank_eq.symm`.
-/
theorem finrank_Z1f_trivial {l : ℕ} [Fact l.Prime] (P : LocPrime l) (K LL : FinExt l) :
    finrank ↥LL.1 ↥(finiteCocycles (P.PD K) (1 : Representation ↥LL.1 ↥(GK K) ↥LL.1)) =
      finrank ↥LL.1 (FiniteCohomology (P.PD K) (1 : Representation ↥LL.1 ↥(GK K) ↥LL.1)) := by
  have hB1 : B1 (1 : Representation ↥LL.1 ↥(GK K) ↥LL.1) = ⊥ := by
    rw [eq_bot_iff]
    rintro _ ⟨x, rfl⟩
    ext g
    simp [cob]
  have hc : (B1 (1 : Representation ↥LL.1 ↥(GK K) ↥LL.1)).comap
      (finiteCocycles (P.PD K) (1 : Representation ↥LL.1 ↥(GK K) ↥LL.1)).subtype = ⊥ := by
    rw [hB1, Submodule.comap_bot, Submodule.ker_subtype]
  exact (Submodule.quotEquivOfEqBot _ hc).finrank_eq.symm
end GlobalTheory.UnramifiedTrivial

namespace GlobalTheory.UnramifiedTrivial
/- English proof (translation)
Establish `hZ : finrank ↥LL.1 ↥(finiteCocycles (P.PD K) (1 : Representation ↥LL.1 ↥(GK K) ↥LL.1)) = 1` using `(finrank_Z1f_trivial P K LL).trans h1`. Use `haveI : FiniteDimensional ↥LL.1 ↥(finiteCocycles (P.PD K) (1 : Representation ↥LL.1 ↥(GK K) ↥LL.1)) := Module.finite_of_finrank_eq_succ hZ`. Establish `hle` using `unramifiedCocycles_le_blochKatoFinite_trivial AI T K LL`. Use `haveI := Submodule.finiteDimensional_of_le hle`. Establish `hpos : 0 < finrank ↥LL.1 ↥(Z1ur (1 : Representation ↥LL.1 ↥(GK K) ↥LL.1) (IK K))`.

Use `Nat.pos_of_ne_zero fun h0 => Z1ur_ne_bot K LL ?_` and prove the remaining obligations. Conclude with `Submodule.finrank_eq_zero.1 h0`. Unfold `UnrTriv`. Conclude with `(Submodule.eq_of_le_of_finrank_le hle (by rw [hZ]; exact hpos)).symm`.
-/
theorem unrTriv_of_finrank {l : ℕ} [Fact l.Prime] {P : LocPrime l} (AI : LocAinf l P)
    (T : LocTied l P AI) (K LL : FinExt l)
    (h1 : finrank ↥LL.1 (FiniteCohomology (P.PD K) (1 : Representation ↥LL.1 ↥(GK K) ↥LL.1)) = 1) :
    UnrTriv (P.PD K) (LL := ↥LL.1) (IK K) := by
  have hZ : finrank ↥LL.1 ↥(finiteCocycles (P.PD K) (1 : Representation ↥LL.1 ↥(GK K) ↥LL.1)) = 1 :=
    (finrank_Z1f_trivial P K LL).trans h1
  haveI : FiniteDimensional ↥LL.1 ↥(finiteCocycles (P.PD K) (1 : Representation ↥LL.1 ↥(GK K) ↥LL.1)) :=
    Module.finite_of_finrank_eq_succ hZ
  have hle := unramifiedCocycles_le_blochKatoFinite_trivial AI T K LL
  haveI := Submodule.finiteDimensional_of_le hle
  have hpos : 0 < finrank ↥LL.1 ↥(Z1ur (1 : Representation ↥LL.1 ↥(GK K) ↥LL.1) (IK K)) := by
    refine Nat.pos_of_ne_zero fun h0 => Z1ur_ne_bot K LL ?_
    exact Submodule.finrank_eq_zero.1 h0
  unfold UnrTriv
  exact (Submodule.eq_of_le_of_finrank_le hle (by rw [hZ]; exact hpos)).symm
end GlobalTheory.UnramifiedTrivial

namespace GlobalTheory.UnramifiedTrivial

/- English proof (translation)
Introduce `l _ P AI T K LL`. Use `haveI := LL.2`. Take `⟨hgood, -⟩` from `GlobalTheory.LocalIntegers.good_integers l LL`. Set `A : GRep ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL)` to `{ V := ↥LL.1 ρ := 1 cont := fun x => (continuous_const : Continuous fun _ : ↥(GK K) => x) }`. Establish `hDR : IsDR (P.PD K) A.ρ` using `GlobalTheory.CrysExt.isDR_trivial (P.PD K)`.

Take `⟨hfin, hdim⟩` from `GlobalTheory.T.finrank_H1f_de_rham l P AI T K ↥LL.1 ↥(OL LL) hgood A hDR`. Establish `hH0 : H0V A.ρ = ⊤`. Use `eq_top_iff.2 fun x _ => (Submodule.mem_iInf _).2 fun g => ?_` and prove the remaining obligations. Simplify using `[A, H0V]`. Establish `hFil : DdR (P.PD K) A.ρ ⊓ FilV (P.PD K) (LL` using `↥LL.1) (V := A.V) 0 = DdR (P.PD K) A.ρ := by`.

Use `inf_eq_left.2 fun x hx => ?_` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `x ∈ DdR (P.PD K) (Representation.trivial ↥LL.1 ↥(GK K) ↥LL.1) at hx`. Rewrite `hx` using `[GlobalTheory.CrysExt.ddR_trivial]`. Take `⟨z, rfl⟩` from `hx`. Conclude with `GlobalTheory.CrysExt.incl_mem_FilV (P.PD K) le_rfl z`.

Establish `e1 : finrank ↥LL.1 ↥(H0V A.ρ) = 1` using `by rw [hH0, finrank_top]; exact Module.finrank_self _`. Establish `e2 : finrank ↥LL.1 ↥(DdR (P.PD K) A.ρ ⊓ FilV (P.PD K) (LL` using `↥LL.1) (V := A.V) 0) = finrank ↥LL.1 ↥(DdR (P.PD K) A.ρ) := by rw [hFil]`. Establish `h1' : finrank ↥LL.1 (FiniteCohomology (P.PD K) A.ρ) = 1` using `by omega`. Establish `h1 : finrank ↥LL.1 (FiniteCohomology (P.PD K) (1 : Representation ↥LL.1 ↥(GK K) ↥LL.1)) = 1` using `h1'`. Conclude with `unrTriv_of_finrank AI T K LL h1`.
-/
theorem unrTriv : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), LocTied l P AI →
    ∀ (K LL : FinExt l), UnrTriv (P.PD K) (LL := ↥LL.1) (IK K) := by
  intro l _ P AI T K LL
  haveI := LL.2
  obtain ⟨hgood, -⟩ := GlobalTheory.LocalIntegers.good_integers l LL
  let A : GRep ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL) :=
    { V := ↥LL.1
      ρ := 1
      cont := fun x => (continuous_const : Continuous fun _ : ↥(GK K) => x) }
  have hDR : IsDR (P.PD K) A.ρ := GlobalTheory.CrysExt.isDR_trivial (P.PD K)
  obtain ⟨hfin, hdim⟩ := GlobalTheory.T.finrank_H1f_de_rham l P AI T K ↥LL.1 ↥(OL LL) hgood A hDR
  have hH0 : H0V A.ρ = ⊤ := by
    refine eq_top_iff.2 fun x _ => (Submodule.mem_iInf _).2 fun g => ?_
    simp [A, H0V]
  have hFil : DdR (P.PD K) A.ρ ⊓ FilV (P.PD K) (LL := ↥LL.1) (V := A.V) 0 = DdR (P.PD K) A.ρ := by
    refine inf_eq_left.2 fun x hx => ?_
    change x ∈ DdR (P.PD K) (Representation.trivial ↥LL.1 ↥(GK K) ↥LL.1) at hx
    rw [GlobalTheory.CrysExt.ddR_trivial] at hx
    obtain ⟨z, rfl⟩ := hx
    exact GlobalTheory.CrysExt.incl_mem_FilV (P.PD K) le_rfl z
  have e1 : finrank ↥LL.1 ↥(H0V A.ρ) = 1 := by rw [hH0, finrank_top]; exact Module.finrank_self _
  have e2 : finrank ↥LL.1 ↥(DdR (P.PD K) A.ρ ⊓ FilV (P.PD K) (LL := ↥LL.1) (V := A.V) 0) = finrank ↥LL.1 ↥(DdR (P.PD K) A.ρ) := by rw [hFil]
  have h1' : finrank ↥LL.1 (FiniteCohomology (P.PD K) A.ρ) = 1 := by omega
  have h1 : finrank ↥LL.1 (FiniteCohomology (P.PD K) (1 : Representation ↥LL.1 ↥(GK K) ↥LL.1)) = 1 := h1'
  exact unrTriv_of_finrank AI T K LL h1

end GlobalTheory.UnramifiedTrivial

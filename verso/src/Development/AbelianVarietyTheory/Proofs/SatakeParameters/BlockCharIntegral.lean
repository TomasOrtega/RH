import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.BlockSplitAll
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.IsobaricDiscreteSelfDualStrongMultiplicityOne
import Formalism.SharpRestriction.LevelLetterCocycles.SumRepresentations
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ContinuousIotaOQOfData
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial NumberField IsDedekindDomain GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.RowTie GlobalTheory.SplitRead

noncomputable section

namespace GlobalTheory.SplitRead

open Formalism.MainNotions.SumRepresentations.At

/- English proof (translation)
Simplify using `[Matrix.charpoly, Matrix.det_fin_one, Matrix.charmatrix_apply]`.
-/
theorem charpoly_fin_one {k : Type} [CommRing k] (M : Matrix (Fin 1) (Fin 1) k) :
    M.charpoly = X - C (M 0 0) := by
  simp [Matrix.charpoly, Matrix.det_fin_one, Matrix.charmatrix_apply]

variable {R : Ranks} {H : Host R} {what₂ : Rows.Data R} (N : NData R H what₂) (A : NAut N)

def blockShift (R : Ranks) : ℝ := ((R.t : ℝ) - 1) / 2 + (1 - (R.nV : ℝ)) / 2

/- English proof (translation)
Take `⟨a, ha⟩` from `R.k_even`. Take `⟨b, hb⟩` from `R.m_even`. Establish `h2` using `R.two_le_m`. Take `⟨c, hc⟩ : ∃ c : ℕ, R.r = 2 * c + 1` from `⟨a + b - 1, by simp only [Ranks.r]; omega⟩`. Establish `hs : ((blockShift R : ℝ) : ℂ) = -(c : ℂ) - 1 / 2`.

Establish `: blockShift R = -(c : ℝ) - 1 / 2`. Simplify using `only [blockShift, Ranks.nV, hc]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[this]`.

Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Take `⟨h1, h3⟩` from `hAut.2.1 τ`. Break down `h1 with h1 | h1` into its components or cases. Establish `he : A.infG A.etaTinv τ = {-(1 / 2)}` using `by rw [h3, h1]; simp`.

Rewrite `hz` using `[A.infG_tw _ _ _ _ he, Multiset.mem_map]`. Take `⟨y, hy, rfl⟩` from `hz`. Take `⟨m, rfl⟩` from `hMu i τ y hy`. Conclude with `⟨m - c - 1, by rw [hs]; push_cast; ring⟩`. Establish `he : A.infG A.etaTinv τ = {1 / 2}` using `by rw [h3, h1]; simp`.

Rewrite `hz` using `[A.infG_tw _ _ _ _ he, Multiset.mem_map]`. Take `⟨y, hy, rfl⟩` from `hz`. Take `⟨m, rfl⟩` from `hMu i τ y hy`. Conclude with `⟨m - c, by rw [hs]; push_cast; ring⟩`.
-/
theorem blockChar_integral (hAut : TieAut N A) (hMu : MuInt N A) (i : N.Loc) (τ : H.E →+* ℂ) (z : ℂ)
    (hz : z ∈ A.infG (A.tw (A.muC i) A.etaTinv) τ) : ∃ k : ℤ, z + ((blockShift R : ℝ) : ℂ) = (k : ℂ) := by
  obtain ⟨a, ha⟩ := R.k_even
  obtain ⟨b, hb⟩ := R.m_even
  have h2 := R.two_le_m
  obtain ⟨c, hc⟩ : ∃ c : ℕ, R.r = 2 * c + 1 := ⟨a + b - 1, by simp only [Ranks.r]; omega⟩
  have hs : ((blockShift R : ℝ) : ℂ) = -(c : ℂ) - 1 / 2 := by
    have : blockShift R = -(c : ℝ) - 1 / 2 := by
      simp only [blockShift, Ranks.nV, hc]
      push_cast
      ring
    rw [this]
    push_cast
    ring
  obtain ⟨h1, h3⟩ := hAut.2.1 τ
  rcases h1 with h1 | h1
  · have he : A.infG A.etaTinv τ = {-(1 / 2)} := by rw [h3, h1]; simp
    rw [A.infG_tw _ _ _ _ he, Multiset.mem_map] at hz
    obtain ⟨y, hy, rfl⟩ := hz
    obtain ⟨m, rfl⟩ := hMu i τ y hy
    exact ⟨m - c - 1, by rw [hs]; push_cast; ring⟩
  · have he : A.infG A.etaTinv τ = {1 / 2} := by rw [h3, h1]; simp
    rw [A.infG_tw _ _ _ _ he, Multiset.mem_map] at hz
    obtain ⟨y, hy, rfl⟩ := hz
    obtain ⟨m, rfl⟩ := hMu i τ y hy
    exact ⟨m - c, by rw [hs]; push_cast; ring⟩

/- English proof (translation)
Establish `h0 : Ideal.span {((l : ℕ) : 𝓞 H.E)} ≠ 0`. Simplify using `using hl`. Conclude with `(Ideal.finite_factors h0).subset fun v hv => Ideal.dvd_span_singleton.2 hv`.
-/
theorem finite_placesOver (l : ℕ) (hl : l ≠ 0) : (placesOver H.E l).Finite := by
  have h0 : Ideal.span {((l : ℕ) : 𝓞 H.E)} ≠ 0 := by
    simpa using hl
  exact (Ideal.finite_factors h0).subset fun v hv => Ideal.dvd_span_singleton.2 hv

/- English proof (translation)
Establish `hl : N.l i ≠ 0` using `(Fact.out : (N.l i).Prime).ne_zero`. Establish `hfin : (placesOver H.E (N.l i) ∪ ((N.S i : Set _) ∪ (N.Q i : Set _))).Finite` using `(finite_placesOver (H := H) _ hl).union ((N.S i).finite_toSet.union (N.Q i).finite_toSet)`. Establish `hd` using `h5.2.2.1 _ hfin`. Establish `hc1 : Continuous fun g : G H.E N.Om => ((ρ g : GL (Fin 1) (Qbar (N.l i))) : Matrix (Fin 1) (Fin 1) (Qbar (N.l i))) 0 0` using `(continuous_apply_apply 0 0).comp hρ`. Establish `hc2 : Continuous fun g : G H.E N.Om => iotaOQ N A i (chi1 N i g)` using `(GlobalTheory.CoeffEmbedding.continuous_iotaOQ_of_data N A i).comp (N.chi_cont i 1)`.

Use `congrFun (Continuous.ext_on (dense_iff_closure_eq.2 hd) hc1 hc2 ?_) g` and prove the remaining obligations. Introduce and unpack `σ ⟨w, hw, hsp, B, hB, hσ⟩`. Simplify using `only [Set.mem_union, Finset.mem_coe, not_or] at hw`. Take `⟨hwl, hwS, hwQ⟩` from `hw`. Establish `hso : SplitOut N i w` using `⟨hsp, hwl, hwS, hwQ⟩`.

Take `⟨hu, hf⟩` from `A.chi_mu i w hso`. Establish `hun : A.unr (A.wdOf i ρ w)`. Rewrite using `[hwd w hwl]`. Conclude with `(A.unr_tw _ _).2 hu`. Establish `e` using `A.wdOf_frob i ρ w hwl hρ hun B σ hB hσ`.

Rewrite `e` using `[hwd w hwl, show blockShift R = ((R.t : ℝ) - 1) / 2 + (1 - (R.nV : ℝ)) / 2 from rfl, hf B σ hB hσ, charpoly_fin_one]`. Simplify using `only [Multiset.map_singleton, Multiset.prod_singleton, Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C] at e`. Establish `e2` using `C_injective (sub_right_injective e)`. Conclude with `(A.iotaQC i).injective e2`.
-/
theorem blockChar_eq (h5 : JacquetShalikaStrongMultOne N A) (i : N.Loc) (ρ : G H.E N.Om →* GL (Fin 1) (Qbar (N.l i)))
    (hρ : ContQ N i ρ)
    (hwd : ∀ w, w ∉ placesOver H.E (N.l i) →
      A.wdOf i ρ w = A.lpTw (A.locG (A.tw (A.muC i) A.etaTinv) w) (blockShift R))
    (g : G H.E N.Om) :
    ((ρ g : GL (Fin 1) (Qbar (N.l i))) : Matrix (Fin 1) (Fin 1) (Qbar (N.l i))) 0 0 =
      iotaOQ N A i (chi1 N i g) := by
  have hl : N.l i ≠ 0 := (Fact.out : (N.l i).Prime).ne_zero
  have hfin : (placesOver H.E (N.l i) ∪ ((N.S i : Set _) ∪ (N.Q i : Set _))).Finite :=
    (finite_placesOver (H := H) _ hl).union ((N.S i).finite_toSet.union (N.Q i).finite_toSet)
  have hd := h5.2.2.1 _ hfin
  have hc1 : Continuous fun g : G H.E N.Om =>
      ((ρ g : GL (Fin 1) (Qbar (N.l i))) : Matrix (Fin 1) (Fin 1) (Qbar (N.l i))) 0 0 :=
    (continuous_apply_apply 0 0).comp hρ
  have hc2 : Continuous fun g : G H.E N.Om => iotaOQ N A i (chi1 N i g) :=
    (GlobalTheory.CoeffEmbedding.continuous_iotaOQ_of_data N A i).comp (N.chi_cont i 1)
  refine congrFun (Continuous.ext_on (dense_iff_closure_eq.2 hd) hc1 hc2 ?_) g
  rintro σ ⟨w, hw, hsp, B, hB, hσ⟩
  simp only [Set.mem_union, Finset.mem_coe, not_or] at hw
  obtain ⟨hwl, hwS, hwQ⟩ := hw
  have hso : SplitOut N i w := ⟨hsp, hwl, hwS, hwQ⟩
  obtain ⟨hu, hf⟩ := A.chi_mu i w hso
  have hun : A.unr (A.wdOf i ρ w) := by
    rw [hwd w hwl]; exact (A.unr_tw _ _).2 hu
  have e := A.wdOf_frob i ρ w hwl hρ hun B σ hB hσ
  rw [hwd w hwl, show blockShift R = ((R.t : ℝ) - 1) / 2 + (1 - (R.nV : ℝ)) / 2 from rfl, hf B σ hB hσ,
    charpoly_fin_one] at e
  simp only [Multiset.map_singleton, Multiset.prod_singleton, Polynomial.map_sub, Polynomial.map_X,
    Polynomial.map_C] at e
  have e2 := C_injective (sub_right_injective e)
  exact (A.iotaQC i).injective e2

/- English proof (translation)
Introduce `i w hw σ hσ`. Take `⟨ρ, hρ, hwd, -⟩` from `(h2 i).2.2 (A.tw (A.muC i) A.etaTinv) (blockShift R) (fun τ z hz => blockChar_integral N A hAut hMu i τ z hz)`. Establish `hρσ` using `blockChar_eq N A h5 i ρ hρ hwd σ`. Establish `e` using `A.wdOf_ine i ρ w hw hρ σ hσ`. Rewrite `e` using `[hwd w hw, A.inePol_tw _ _ _ hσ, A.locG_tw, charpoly_fin_one, hρσ]`.

Establish `hdim : A.lpDim (A.locG A.etaTinv w) = 1` using `A.locG_dim _ _`. Establish `hine : A.inePol (A.locG A.etaTinv w) σ = X - C 1`. Use `((A.unr_iff_ine _).1 (A.etaTinv_def w).1).2 σ hσ` as an intermediate fact. Rewrite `this` using `[hdim, pow_one]`. Simplify using `using this`.

Establish `hs` using `((hLP w (A.locG (A.muC i) w) (A.locG (A.muC i) w) (A.locG A.etaTinv w) (A.locG A.etaTinv w) 0 hdim hdim).2.2.2.2.2 σ hσ).2 1 hine`. Rewrite `e` using `[hs, Polynomial.scaleRoots_one]`. Rewrite using `[← e]`. Simplify using `only [Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C]`. Both sides reduce to the same expression.
-/
theorem chiIne_of_data (hLP : TieLP N A) (hAut : TieAut N A) (h2 : exists_galois_rep_local_global_compatible N A) (h5 : JacquetShalikaStrongMultOne N A)
    (hMu : MuInt N A) : ChiIne N A := by
  intro i w hw σ hσ
  obtain ⟨ρ, hρ, hwd, -⟩ := (h2 i).2.2 (A.tw (A.muC i) A.etaTinv) (blockShift R)
    (fun τ z hz => blockChar_integral N A hAut hMu i τ z hz)
  have hρσ := blockChar_eq N A h5 i ρ hρ hwd σ
  have e := A.wdOf_ine i ρ w hw hρ σ hσ
  rw [hwd w hw, A.inePol_tw _ _ _ hσ, A.locG_tw, charpoly_fin_one, hρσ] at e
  have hdim : A.lpDim (A.locG A.etaTinv w) = 1 := A.locG_dim _ _
  have hine : A.inePol (A.locG A.etaTinv w) σ = X - C 1 := by
    have := ((A.unr_iff_ine _).1 (A.etaTinv_def w).1).2 σ hσ
    rw [hdim, pow_one] at this
    simpa using this
  have hs := ((hLP w (A.locG (A.muC i) w) (A.locG (A.muC i) w) (A.locG A.etaTinv w) (A.locG A.etaTinv w) 0
    hdim hdim).2.2.2.2.2 σ hσ).2 1 hine
  rw [hs, Polynomial.scaleRoots_one] at e
  rw [← e]
  simp only [Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C]
  rfl

/- English proof (translation)
Introduce `D h0 h2 h5 hMu` and use `chiIne_of_data D.nd D.naut h0.1 h0.2.1 h2 h5 hMu`.
-/
theorem chiIne_main : ∀ D : D7, Formalism.MainNotions.SumRepresentations.tie0 D → Formalism.MainNotions.SumRepresentations.adm2 D → Formalism.MainNotions.SumRepresentations.adm5 D → MuInt D.nd D.naut →
    ChiIne D.nd D.naut :=
  fun D h0 h2 h5 hMu => chiIne_of_data D.nd D.naut h0.1 h0.2.1 h2 h5 hMu

end GlobalTheory.SplitRead

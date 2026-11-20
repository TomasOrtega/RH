import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsPotential
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.OneSubPhiOntoOfFilZero
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BhattScholzeCrystallineLattices
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.ConductorExponents
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.InertiaCyclic
import Formalism.SharpRestriction.LevelLetterCocycles.ProdOneSubPrimitiveRoots
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

noncomputable section

namespace GlobalTheory.MinpolyKummerUr

open Polynomial

/- English proof (translation)
Use `set F := MaximalUnramifiedExtension l`. Establish `hl0 : (0 : ℝ) < l` using `by exact_mod_cast (Fact.out : l.Prime).pos`. Establish `hl1 : (1 : ℝ) < l` using `by exact_mod_cast (Fact.out : l.Prime).one_lt`. Establish `hQ : (Polynomial.X ^ M + Polynomial.C ((l : ℕ) : F)).Monic`. Apply `Polynomial.monic_X_pow_add_C _ hM.ne'` to reduce the goal to its premises.

Establish `hQdeg : (Polynomial.X ^ M + Polynomial.C ((l : ℕ) : F)).natDegree = M`. Rewrite using `[Polynomial.natDegree_X_pow_add_C]`. Establish `haeval : Polynomial.aeval ρ (Polynomial.X ^ M + Polynomial.C ((l : ℕ) : F)) = 0`. Simplify using `[hρ]`. Establish `hint : IsIntegral F ρ`.

Use `⟨_, hQ, ?_⟩` and prove the remaining obligations. Rewrite using `[← Polynomial.aeval_def]` and apply the resulting hypothesis. Establish `hdvd : minpoly F ρ ∣ Polynomial.X ^ M + Polynomial.C ((l : ℕ) : F)` using `minpoly.dvd _ _ haeval`. Establish `hmon` using `minpoly.monic hint`. Establish `hpos : 0 < (minpoly F ρ).natDegree` using `minpoly.natDegree_pos hint`.

Establish `hle : (minpoly F ρ).natDegree ≤ M`. Rewrite using `[← hQdeg]`. Conclude with `Polynomial.natDegree_le_of_dvd hdvd hQ.ne_zero`. Establish `hnρ : ‖ρ‖ ^ M = (l : ℝ)⁻¹`. Rewrite using `[← norm_pow, hρ, norm_neg, Formalism.MainNotions.N.PreambleDegrees.Loc.norm_l]`.

Use `set P := (minpoly F ρ).map (algebraMap F (Om l)) with hP`. Establish `hsp : P.Splits` using `IsAlgClosed.splits P`. Establish `hPm : P.Monic` using `hmon.map _`. Establish `hroots : ∀ a ∈ P.roots, ‖0 - a‖ = ‖ρ‖`. Introduce `a ha`.

Establish `h1 : P ∣ (Polynomial.X ^ M + Polynomial.C ((l : ℕ) : F)).map (algebraMap F (Om l))` using `Polynomial.map_dvd _ hdvd`. Establish `h2 : ((Polynomial.X ^ M + Polynomial.C ((l : ℕ) : F)).map (algebraMap F (Om l))).IsRoot a` using `(Polynomial.isRoot_of_mem_roots ha).dvd h1`. Establish `h3 : a ^ M = -(l : Om l)`. Simplify using `[Polynomial.IsRoot] at h2`. Take the linear combination `h2`.

Establish `h4 : ‖a‖ ^ M = ‖ρ‖ ^ M`. Rewrite using `[← norm_pow, ← norm_pow, h3, hρ]`. Rewrite using `[zero_sub, norm_neg]`. Conclude with `(pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) hM.ne').1 h4`. Establish `heval : ‖P.eval 0‖ = ‖ρ‖ ^ (minpoly F ρ).natDegree`.

Rewrite using `[hsp.eval_eq_prod_roots_of_monic hPm, ← Polynomial.natDegree_map (algebraMap F (Om l)), ← hP, hsp.natDegree_eq_card_roots]`. Establish `h3` using `map_multiset_prod (normHom : Om l →*₀ ℝ) (P.roots.map (fun a => 0 - a))`. Establish `h4 : ‖(P.roots.map (fun a => 0 - a)).prod‖ = ((P.roots.map (fun a => 0 - a)).map (normHom : Om l →*₀ ℝ)).prod` using `h3`. Establish `h5 : Multiset.map ((normHom : Om l →*₀ ℝ) ∘ fun a => 0 - a) P.roots = Multiset.map (fun _ => ‖ρ‖) P.roots` using `Multiset.map_congr rfl (fun a ha => by simpa using hroots a ha)`. Rewrite using `[h4, Multiset.map_map, h5, Multiset.map_const', Multiset.prod_replicate]`.

Establish `hy : P.eval 0 = (((minpoly F ρ).eval 0 : F) : Om l)`. Rewrite using `[hP, Polynomial.eval_map, Polynomial.eval₂_at_zero, Polynomial.coeff_zero_eq_eval_zero]`. Both sides reduce to the same expression. Establish `hρ0 : ρ ≠ 0`. Introduce and unpack `rfl`.

Rewrite `hρ` using `[zero_pow hM.ne']`. Establish `: ((l : ℕ) : Om l) ≠ 0`. Introduce `h`. Use `Formalism.MainNotions.N.PreambleDegrees.Loc.norm_l (l := l)` as an intermediate fact. Rewrite `this` using `[h, norm_zero]`.

Conclude with `(inv_pos.2 hl0).ne this`. Conclude with `this (neg_eq_zero.1 hρ.symm)`. Establish `hnρpos : 0 < ‖ρ‖` using `norm_pos_iff.2 hρ0`. Establish `hy0 : (((minpoly F ρ).eval 0 : F) : Om l) ≠ 0`. Rewrite using `[← hy, ← norm_pos_iff, heval]`.

Conclude with `pow_pos hnρpos _`. Take `⟨m, hm⟩` from `Formalism.MainNotions.N.PreambleDegrees.Loc.norm_Kur_zpow ((minpoly F ρ).eval 0 : F).2 hy0`. Rewrite `hm` using `[← hy, heval]`. Establish `h8 : (l : ℝ) ^ (m * (M : ℤ)) = (l : ℝ) ^ (-((minpoly F ρ).natDegree : ℤ))`. Rewrite using `[_root_.zpow_mul, ← hm, zpow_natCast, ← pow_mul, mul_comm, pow_mul, hnρ, _root_.zpow_neg, zpow_natCast, inv_pow]`.

Establish `h9 : m * (M : ℤ) = -((minpoly F ρ).natDegree : ℤ)` using `zpow_right_injective₀ hl0 hl1.ne' h8`. Establish `h10 : (M : ℤ) ∣ ((minpoly F ρ).natDegree : ℤ)` using `⟨-m, by linarith⟩`. Establish `hdeg : (minpoly F ρ).natDegree = M` using `le_antisymm hle (Nat.le_of_dvd hpos (Int.natCast_dvd_natCast.1 h10))`. Conclude with `(Polynomial.eq_of_monic_of_dvd_of_natDegree_le hmon hQ hdvd (by rw [hdeg, hQdeg])).symm`.
-/
theorem minpoly_eq {l : ℕ} [Fact l.Prime] {M : ℕ} (hM : 0 < M) {ρ : Om l}
    (hρ : ρ ^ M = -(l : Om l)) :
    minpoly (↥(MaximalUnramifiedExtension l)) ρ = Polynomial.X ^ M + Polynomial.C ((l : ℕ) : ↥(MaximalUnramifiedExtension l)) := by
  set F := MaximalUnramifiedExtension l
  have hl0 : (0 : ℝ) < l := by exact_mod_cast (Fact.out : l.Prime).pos
  have hl1 : (1 : ℝ) < l := by exact_mod_cast (Fact.out : l.Prime).one_lt
  have hQ : (Polynomial.X ^ M + Polynomial.C ((l : ℕ) : F)).Monic := by
    apply Polynomial.monic_X_pow_add_C _ hM.ne'
  have hQdeg : (Polynomial.X ^ M + Polynomial.C ((l : ℕ) : F)).natDegree = M := by
    rw [Polynomial.natDegree_X_pow_add_C]
  have haeval : Polynomial.aeval ρ (Polynomial.X ^ M + Polynomial.C ((l : ℕ) : F)) = 0 := by
    simp [hρ]
  have hint : IsIntegral F ρ := by
    refine ⟨_, hQ, ?_⟩
    rwa [← Polynomial.aeval_def]
  have hdvd : minpoly F ρ ∣ Polynomial.X ^ M + Polynomial.C ((l : ℕ) : F) := minpoly.dvd _ _ haeval
  have hmon := minpoly.monic hint
  have hpos : 0 < (minpoly F ρ).natDegree := minpoly.natDegree_pos hint
  have hle : (minpoly F ρ).natDegree ≤ M := by
    rw [← hQdeg]
    exact Polynomial.natDegree_le_of_dvd hdvd hQ.ne_zero

  have hnρ : ‖ρ‖ ^ M = (l : ℝ)⁻¹ := by
    rw [← norm_pow, hρ, norm_neg, Formalism.MainNotions.N.PreambleDegrees.Loc.norm_l]
  set P := (minpoly F ρ).map (algebraMap F (Om l)) with hP
  have hsp : P.Splits := IsAlgClosed.splits P
  have hPm : P.Monic := hmon.map _
  have hroots : ∀ a ∈ P.roots, ‖0 - a‖ = ‖ρ‖ := by
    intro a ha
    have h1 : P ∣ (Polynomial.X ^ M + Polynomial.C ((l : ℕ) : F)).map (algebraMap F (Om l)) := Polynomial.map_dvd _ hdvd
    have h2 : ((Polynomial.X ^ M + Polynomial.C ((l : ℕ) : F)).map (algebraMap F (Om l))).IsRoot a :=
      (Polynomial.isRoot_of_mem_roots ha).dvd h1
    have h3 : a ^ M = -(l : Om l) := by
      simp [Polynomial.IsRoot] at h2
      linear_combination h2
    have h4 : ‖a‖ ^ M = ‖ρ‖ ^ M := by
      rw [← norm_pow, ← norm_pow, h3, hρ]
    rw [zero_sub, norm_neg]
    exact (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) hM.ne').1 h4
  have heval : ‖P.eval 0‖ = ‖ρ‖ ^ (minpoly F ρ).natDegree := by
    rw [hsp.eval_eq_prod_roots_of_monic hPm, ← Polynomial.natDegree_map (algebraMap F (Om l)), ← hP,
      hsp.natDegree_eq_card_roots]
    have h3 := map_multiset_prod (normHom : Om l →*₀ ℝ) (P.roots.map (fun a => 0 - a))
    have h4 : ‖(P.roots.map (fun a => 0 - a)).prod‖
        = ((P.roots.map (fun a => 0 - a)).map (normHom : Om l →*₀ ℝ)).prod := h3
    have h5 : Multiset.map ((normHom : Om l →*₀ ℝ) ∘ fun a => 0 - a) P.roots
        = Multiset.map (fun _ => ‖ρ‖) P.roots :=
      Multiset.map_congr rfl (fun a ha => by simpa using hroots a ha)
    rw [h4, Multiset.map_map, h5, Multiset.map_const', Multiset.prod_replicate]
  have hy : P.eval 0 = (((minpoly F ρ).eval 0 : F) : Om l) := by
    rw [hP, Polynomial.eval_map, Polynomial.eval₂_at_zero, Polynomial.coeff_zero_eq_eval_zero]
    rfl
  have hρ0 : ρ ≠ 0 := by
    rintro rfl
    rw [zero_pow hM.ne'] at hρ
    have : ((l : ℕ) : Om l) ≠ 0 := by
      intro h
      have := Formalism.MainNotions.N.PreambleDegrees.Loc.norm_l (l := l)
      rw [h, norm_zero] at this
      exact (inv_pos.2 hl0).ne this
    exact this (neg_eq_zero.1 hρ.symm)
  have hnρpos : 0 < ‖ρ‖ := norm_pos_iff.2 hρ0
  have hy0 : (((minpoly F ρ).eval 0 : F) : Om l) ≠ 0 := by
    rw [← hy, ← norm_pos_iff, heval]
    exact pow_pos hnρpos _
  obtain ⟨m, hm⟩ := Formalism.MainNotions.N.PreambleDegrees.Loc.norm_Kur_zpow ((minpoly F ρ).eval 0 : F).2 hy0
  rw [← hy, heval] at hm
  have h8 : (l : ℝ) ^ (m * (M : ℤ)) = (l : ℝ) ^ (-((minpoly F ρ).natDegree : ℤ)) := by
    rw [_root_.zpow_mul, ← hm, zpow_natCast, ← pow_mul, mul_comm, pow_mul, hnρ, _root_.zpow_neg, zpow_natCast, inv_pow]
  have h9 : m * (M : ℤ) = -((minpoly F ρ).natDegree : ℤ) :=
    zpow_right_injective₀ hl0 hl1.ne' h8
  have h10 : (M : ℤ) ∣ ((minpoly F ρ).natDegree : ℤ) := ⟨-m, by linarith⟩
  have hdeg : (minpoly F ρ).natDegree = M :=
    le_antisymm hle (Nat.le_of_dvd hpos (Int.natCast_dvd_natCast.1 h10))
  exact (Polynomial.eq_of_monic_of_dvd_of_natDegree_le hmon hQ hdvd (by rw [hdeg, hQdeg])).symm

/- English proof (translation)
Introduce `hM ρ ξ hρ hξ`. Rewrite using `[minpoly_eq hM hρ]`. Simplify using `[mul_pow, hξ, hρ]`.
-/
theorem aeval_mul_root (l : ℕ) [Fact l.Prime] (M : ℕ) : 0 < M → ∀ (ρ ξ : Om l),
    ρ ^ M = -(l : Om l) → ξ ^ M = 1 → Polynomial.aeval (ξ * ρ) (minpoly ↥(MaximalUnramifiedExtension l) ρ) = 0 := by
  intro hM ρ ξ hρ hξ
  rw [minpoly_eq hM hρ]
  simp [mul_pow, hξ, hρ]

end GlobalTheory.MinpolyKummerUr

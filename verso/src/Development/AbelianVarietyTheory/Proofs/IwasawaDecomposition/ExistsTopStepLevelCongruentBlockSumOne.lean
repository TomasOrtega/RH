import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LiftsInvOne
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CongruenceLevelEqDepthSucc
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SymmetricFlagBasisVectorEqSingleOfNoExtra
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemHJsymIffJSymG
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.PhiTopTargetTwist

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.AdT Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Mem.Col2.AdT

open GlobalTheory.TopStep

section Local

variable {E : Type} [Field E] {N : ℕ}

/- English proof (translation)
Use `LinearMap.ext fun x => funext fun i => ?_` and prove the remaining obligations. Conclude with `congrFun (prH_sumE hN g 1 x) i`.
-/
theorem prXpG_sumE (hN : N = (N - 1) + 1) (g : Sp E (N - 1) ≃ₗ[E] Sp E (N - 1)) :
    prXpG E N ∘ₗ (sumE hN g 1).toLinearMap = (g.toLinearMap : Sp E ((N - 1) + 0) →ₗ[E] Sp E ((N - 1) + 0)) ∘ₗ prXpG E N := by
  refine LinearMap.ext fun x => funext fun i => ?_

  exact congrFun (prH_sumE hN g 1 x) i

/- English proof (translation)
Use `LinearMap.ext fun x => ?_` and prove the remaining obligations. Establish `hlt : N - 1 < N` using `by omega`. Establish `h` using `sumE_last hN g 1 x`. Rewrite `h` using `[Units.val_one, one_mul]`. Simplify using `only [LinearMap.comp_apply, atNL, dif_pos hlt, LinearMap.proj_apply]`.

Conclude with `h`.
-/
theorem atNL_sumE (hN : N = (N - 1) + 1) (g : Sp E (N - 1) ≃ₗ[E] Sp E (N - 1)) :
    atNL E N (N - 1) ∘ₗ (sumE hN g 1).toLinearMap = atNL E N (N - 1) := by
  refine LinearMap.ext fun x => ?_
  have hlt : N - 1 < N := by omega

  have h := sumE_last hN g 1 x
  rw [Units.val_one, one_mul] at h
  simp only [LinearMap.comp_apply, atNL, dif_pos hlt, LinearMap.proj_apply]
  exact h

end Local

end GlobalTheory.Mem.Col2.AdT

namespace GlobalTheory.Mem.Col2.AdT

open GlobalTheory.TopStep

/- English proof (translation)
Introduce `B X I hI u a i hi b κ P`. Substitute `hi` using the available equality. Break down `b with ⟨_ | b₀, hb⟩` into its components or cases. Use `swap`. Conclude with `absurd (hb.mp rfl) (lt_irrefl _)`.

Establish `hPr` using `(GlobalTheory.BasePrimes.primes_ok B X).1`. Establish `hq : ((qOf P.1 : ℕ) : 𝓞 B.fields.E) ∉ P.1.asIdeal ^ 2` using `Formalism.L2.Ker.mq_rowSG_unif (I.tup a) (GlobalTheory.Mem.FieldsLaws.fields_ok (B := B)) hPr hI.sel_ok P`. Establish `hN` using `N_m_succ B.R`. Distinguish the cases in `hP : P.1 ∈ (B.primes X).vGs`. Establish `hQn : P.1 ∉ I.Q a` using `QE_disj (I.tup a) hPr hI.sel_ok hI.g_mem P.1 hP`.

Establish `hmem : κ.2.1.1 ⟨P.1, hP⟩ ∈ (levGTop I.Ch I.Ps ⟨P.1, hP⟩).H`. Establish `h` using `κ.2.1.2`. Simplify using `only [LevFam.grp, Subgroup.mem_pi] at h`. Rewrite using `[← topLev_levG_m I.Ch I.sel (I.tup a) (I.cst a) I.Ps]`. Conclude with `h ⟨P.1, hP⟩ (Set.mem_univ _)`.

Take `⟨h₀, hh₀, hdiag⟩` from `(mem_levDiag _ _ _).mp hmem`. Rewrite `hh₀` using `[rowTyG_PsymF_H]`. Establish `hr : B.R.r = B.R.k + 2 * B.R.rS + 1`. Simplify using `only [Formalism.BasicNotions.Ranks.rS, Formalism.BasicNotions.Ranks.r]`. Take `⟨s, hs⟩` from `B.R.m_even`.

Use `B.R.two_le_m` as an intermediate fact. Use linear arithmetic over natural numbers and integers. Establish `hsym : rSym B.R.k B.R.rS = B.R.r` using `by rw [hr]; rfl`. Establish `hJ` using `(mem_HJsym_iff_JSymG (𝓞 B.fields.E ⧸ P.1.asIdeal) (B.R.N B.R.m - 1) B.R.k B.R.r B.R.t B.R.m B.R.rS (r_le_X' B.R) hr B.R.t_odd.pos (rank_X'_eq B.R) h₀⁻¹).mp (Subgroup.inv_mem _ hh₀)`. Take `⟨j, hj⟩` from `redGL_surjective (E := B.fields.E) (n := B.R.N B.R.m - 1) P.1 h₀⁻¹`.

Establish `hjinv : redGL _ P.1 j⁻¹ = h₀` using `by rw [map_inv, hj, inv_inv]`. Establish `hlev : j.1 ∈ GlobalTheory.TwU.rowLevTop (B.primes X) B.R (I.cst a).sharp (B.R.N B.R.m) P.1`. Establish `h` using `GlobalTheory.Mem.LastGrp.mem_JGsym0 (fun x hx h0 => intAt_div_of_redP hq hx h0) (hsym.symm ▸ r_le_X' B.R) j (fun x y hxy => by rw [← redGL_val, hj]; exact hJ.1.1 x y hxy) (fun x y hxy => by rw [← redGL_val, hjinv]; simpa using hJ.2.1 x y hxy) (fun x hx => by rw [← redGL_val, hj]; …`. Establish `e : GlobalTheory.CongLevel.extE 0 j.1 = j.1` using `LinearEquiv.ext (GlobalTheory.Mem.LastGrp.extE_zero j.1)`. Rewrite `h` using `[e, hsym]`.

Simplify using `only [GlobalTheory.TwU.rowLevTop, if_pos hP, hI.sharp a, if_true]`. Conclude with `h`. Use `⟨sumE hN j.1 1, sumE hN j.1 1, _, ⟨j.1, hlev, prXpG_sumE hN j.1, atNL_sumE hN j.1, rfl⟩, ⟨?_, ?_, ?_⟩, congE_refl _ _ _⟩` and prove the remaining obligations. Rewrite using `[← extI_val hN j]`. Conclude with `(extI hN P.1 j).2`.

Introduce `h x hx`. Rewrite using `[← extI_val hN j, redV_redGL _ hx, redGL_extI, hj, ← hdiag, ← map_inv]`. Conclude with `fun h => absurd h hQn`. Establish `hQ : P.1 ∈ I.Q a` using `by classical`. Establish `h` using `P.2`.

Simplify using `only [SBof, rowSG, uSG, Finset.mem_union] at h`. Conclude with `h.resolve_left hP`. Establish `hmem : κ.2.2.1 ⟨P.1, hQ⟩ ∈ (levQTop B.R I.sel (I.tup a) (topDep B.R (I.cst a).M) ⟨P.1, hQ⟩).H`. Establish `h` using `κ.2.2.2`. Simplify using `only [LevQFam.grp, Subgroup.mem_pi] at h`.

Rewrite using `[← topLev_levQ_m I.Ch I.sel (I.tup a) (I.cst a) I.Ps]`. Conclude with `h ⟨P.1, hQ⟩ (Set.mem_univ _)`. Simplify using `only [levQTop] at hmem`. Take `⟨j, hj, hjc⟩` from `(mem_levCong _ _ _ _).mp (Subgroup.inv_mem _ hmem)`. Establish `hlev : j.1 ∈ GlobalTheory.TwU.rowLevTop (B.primes X) B.R (I.cst a).sharp (B.R.N B.R.m) P.1`.

Simplify using `only [GlobalTheory.TwU.rowLevTop, if_neg hP]`. Conclude with `GlobalTheory.TopLaw.mem_JQ_of_red hq j ((mem_levRed _ _).mp hj)`. Use `⟨sumE hN j.1 1, ((κ.2.2.1 ⟨P.1, hQ⟩)⁻¹).1, _, ⟨j.1, hlev, prXpG_sumE hN j.1, atNL_sumE hN j.1, rfl⟩, ⟨((κ.2.2.1 ⟨P.1, hQ⟩)⁻¹).2, fun h => absurd h hP, fun h => rfl⟩, ?_⟩` and prove the remaining obligations. Establish `h2 : (extI hN P.1 j)⁻¹ * (κ.2.2.1 ⟨P.1, hQ⟩)⁻¹ ∈ prinCong _ P.1 (2 * (I.cst a).M)` using `prinCong_anti (by have := two_mul_le_topDep B.R (I.cst a).M; omega) hjc`. Establish `h3 : ((κ.2.2.1 ⟨P.1, hQ⟩)⁻¹)⁻¹ * extI hN P.1 j ∈ prinCong _ P.1 (2 * (I.cst a).M)`.

Use `Subgroup.inv_mem _ h2` as an intermediate fact. Rewrite `this` using `[_root_.mul_inv_rev, inv_inv]`. Then use the resulting hypothesis. Establish `h4` using `(inv_mul_mem_prinCong _ _ _).mp h3`. Introduce `x hx`. Simplify using `only [GlobalTheory.TwU.topDep, if_neg hP]`.

Use `h4 x hx` as an intermediate fact. Rewrite `this` using `[extI_val]`. Then use the resulting hypothesis.
-/
theorem exists_topLev_liftsInv : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → ∀ (u : B.Word) (a : I.ι) (i : ℕ), i = B.R.m →
    ∀ (b : (I.stp u a i).β) (κ : (I.stp u a i).G b) (P : SBof I a), ∃ g g' z,
      GlobalTheory.TwU.TopLev (R := B.R) I.Ch I.sel (I.tup a) (I.cst a) i P g z ∧ LiftsInv I κ P g' ∧
        CongE P.1 (GlobalTheory.TwU.topDep I.sel (I.tup a) (I.cst a) P) g g' := by
  intro B X I hI u a i hi b κ P
  subst hi

  rcases b with ⟨_ | b₀, hb⟩
  swap
  · exact absurd (hb.mp rfl) (lt_irrefl _)
  have hPr := (GlobalTheory.BasePrimes.primes_ok B X).1

  have hq : ((qOf P.1 : ℕ) : 𝓞 B.fields.E) ∉ P.1.asIdeal ^ 2 :=
    Formalism.L2.Ker.mq_rowSG_unif (I.tup a) (GlobalTheory.Mem.FieldsLaws.fields_ok (B := B)) hPr hI.sel_ok P
  have hN := N_m_succ B.R
  by_cases hP : P.1 ∈ (B.primes X).vGs
  ·
    have hQn : P.1 ∉ I.Q a := QE_disj (I.tup a) hPr hI.sel_ok hI.g_mem P.1 hP
    have hmem : κ.2.1.1 ⟨P.1, hP⟩ ∈ (levGTop I.Ch I.Ps ⟨P.1, hP⟩).H := by
      have h := κ.2.1.2
      simp only [LevFam.grp, Subgroup.mem_pi] at h
      rw [← topLev_levG_m I.Ch I.sel (I.tup a) (I.cst a) I.Ps]
      exact h ⟨P.1, hP⟩ (Set.mem_univ _)
    obtain ⟨h₀, hh₀, hdiag⟩ := (mem_levDiag _ _ _).mp hmem
    rw [rowTyG_PsymF_H] at hh₀
    have hr : B.R.r = B.R.k + 2 * B.R.rS + 1 := by
      simp only [Formalism.BasicNotions.Ranks.rS, Formalism.BasicNotions.Ranks.r]
      obtain ⟨s, hs⟩ := B.R.m_even
      have := B.R.two_le_m
      omega
    have hsym : rSym B.R.k B.R.rS = B.R.r := by rw [hr]; rfl

    have hJ := (mem_HJsym_iff_JSymG (𝓞 B.fields.E ⧸ P.1.asIdeal) (B.R.N B.R.m - 1) B.R.k B.R.r B.R.t B.R.m B.R.rS
      (r_le_X' B.R) hr B.R.t_odd.pos (rank_X'_eq B.R) h₀⁻¹).mp (Subgroup.inv_mem _ hh₀)

    obtain ⟨j, hj⟩ := redGL_surjective (E := B.fields.E) (n := B.R.N B.R.m - 1) P.1 h₀⁻¹
    have hjinv : redGL _ P.1 j⁻¹ = h₀ := by rw [map_inv, hj, inv_inv]
    have hlev : j.1 ∈ GlobalTheory.TwU.rowLevTop (B.primes X) B.R (I.cst a).sharp (B.R.N B.R.m) P.1 := by
      have h := GlobalTheory.Mem.LastGrp.mem_JGsym0 (fun x hx h0 => intAt_div_of_redP hq hx h0)
        (hsym.symm ▸ r_le_X' B.R) j
        (fun x y hxy => by rw [← redGL_val, hj]; exact hJ.1.1 x y hxy)
        (fun x y hxy => by rw [← redGL_val, hjinv]; simpa using hJ.2.1 x y hxy)
        (fun x hx => by rw [← redGL_val, hj]; exact hJ.1.2.1 x hx)
        (fun x y hx hy => by rw [← redGL_val, hj]; exact hJ.1.2.2.1 x y hx hy)
      have e : GlobalTheory.CongLevel.extE 0 j.1 = j.1 := LinearEquiv.ext (GlobalTheory.Mem.LastGrp.extE_zero j.1)
      rw [e, hsym] at h
      simp only [GlobalTheory.TwU.rowLevTop, if_pos hP, hI.sharp a, if_true]
      exact h
    refine ⟨sumE hN j.1 1, sumE hN j.1 1, _, ⟨j.1, hlev, prXpG_sumE hN j.1, atNL_sumE hN j.1, rfl⟩, ⟨?_, ?_, ?_⟩, congE_refl _ _ _⟩
    · rw [← extI_val hN j]
      exact (extI hN P.1 j).2
    · intro h x hx
      rw [← extI_val hN j, redV_redGL _ hx, redGL_extI, hj, ← hdiag, ← map_inv]
    · exact fun h => absurd h hQn
  ·
    have hQ : P.1 ∈ I.Q a := by
      classical
      have h := P.2
      simp only [SBof, rowSG, uSG, Finset.mem_union] at h
      exact h.resolve_left hP
    have hmem : κ.2.2.1 ⟨P.1, hQ⟩ ∈ (levQTop B.R I.sel (I.tup a) (topDep B.R (I.cst a).M) ⟨P.1, hQ⟩).H := by
      have h := κ.2.2.2
      simp only [LevQFam.grp, Subgroup.mem_pi] at h
      rw [← topLev_levQ_m I.Ch I.sel (I.tup a) (I.cst a) I.Ps]
      exact h ⟨P.1, hQ⟩ (Set.mem_univ _)
    simp only [levQTop] at hmem
    obtain ⟨j, hj, hjc⟩ := (mem_levCong _ _ _ _).mp (Subgroup.inv_mem _ hmem)
    have hlev : j.1 ∈ GlobalTheory.TwU.rowLevTop (B.primes X) B.R (I.cst a).sharp (B.R.N B.R.m) P.1 := by
      simp only [GlobalTheory.TwU.rowLevTop, if_neg hP]
      exact GlobalTheory.TopLaw.mem_JQ_of_red hq j ((mem_levRed _ _).mp hj)
    refine ⟨sumE hN j.1 1, ((κ.2.2.1 ⟨P.1, hQ⟩)⁻¹).1, _, ⟨j.1, hlev, prXpG_sumE hN j.1, atNL_sumE hN j.1, rfl⟩,
      ⟨((κ.2.2.1 ⟨P.1, hQ⟩)⁻¹).2, fun h => absurd h hP, fun h => rfl⟩, ?_⟩

    have h2 : (extI hN P.1 j)⁻¹ * (κ.2.2.1 ⟨P.1, hQ⟩)⁻¹ ∈ prinCong _ P.1 (2 * (I.cst a).M) :=
      prinCong_anti (by have := two_mul_le_topDep B.R (I.cst a).M; omega) hjc
    have h3 : ((κ.2.2.1 ⟨P.1, hQ⟩)⁻¹)⁻¹ * extI hN P.1 j ∈ prinCong _ P.1 (2 * (I.cst a).M) := by
      have := Subgroup.inv_mem _ h2
      rwa [_root_.mul_inv_rev, inv_inv] at this
    have h4 := (inv_mul_mem_prinCong _ _ _).mp h3
    intro x hx
    simp only [GlobalTheory.TwU.topDep, if_neg hP]
    have := h4 x hx
    rwa [extI_val] at this

end GlobalTheory.Mem.Col2.AdT

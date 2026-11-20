import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.PolynomialSiteTraces.AdmissibleMap
import Development.WeilBound.CoreStatements.AbelianHeightsDuality.DividedPowerAlgebras.ExistsDividedPowersAug
import Development.WeilBound.CoreStatements.AbelianHeightsDuality.DividedPowerAlgebras.FilIsSubDPIdeal
import Development.WeilBound.CoreStatements.AbelianHeightsDuality.DividedPowerAlgebras.RingTrunc
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DividedPowerPolynomialFiltrationStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EtaleLiftingOfNilIdealStatement
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry GlobalTheory.LogCris DividedPowers GlobalTheory.PDA CrystallineSemistableComparison CrystallineSemistableComparison.Pb CrystallineSemistableComparison.Pb.Site

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CompanionTheory.PDUniv

/- English proof (translation)
Introduce `B _ J δ C _ J'' δ'' f hf x hx`. Establish `hη : (pq B).IsStd δ (eta δ)`. Unfold `eta`. Conclude with `Classical.choose_spec (FubiniStudyChowHeightFormula₂.Adr.exists_std B J δ (pq B))`. Use `letI : Algebra B C := f.toAlgebra`.

Set `L : (pq B).P →ₗ[B] C` to `(pq B).e.constr ℕ fun n => δ''.dpow n x`. Establish `hL : ∀ n, L ((pq B).e n) = δ''.dpow n x` using `fun n => (pq B).e.constr_basis ℕ _ n`. Establish `h1 : L 1 = 1`. Rewrite using `[← (pq B).e_zero, hL, δ''.dpow_zero hx]`. Establish `hbil : (LinearMap.mul B (pq B).P).compr₂ L = (LinearMap.mul B C).compl₁₂ L L`.

Use `(pq B).e.ext fun m => (pq B).e.ext fun n => ?_` and prove the remaining obligations. Use `show L ((pq B).e m * (pq B).e n) = L ((pq B).e m) * L ((pq B).e n)`. Rewrite using `[(pq B).e_mul, ← nsmul_eq_mul, map_nsmul]`. Simplify using `only [hL]`. Rewrite using `[nsmul_eq_mul, δ''.mul_dpow hx]`.

Establish `hmul : ∀ a b, L (a * b) = L a * L b` using `fun a b => LinearMap.congr_fun₂ hbil a b`. Set `F : (pq B).P →+* C` to `(AlgHom.ofLinearMap L h1 hmul).toRingHom`. Establish `hFL : ∀ p, F p = L p` using `fun p => rfl`. Establish `hFe : ∀ n, F ((pq B).e n) = δ''.dpow n x` using `fun n => (hFL _).trans (hL n)`. Establish `hFa : ∀ b, F (algebraMap B (pq B).P b) = f b` using `fun b => (AlgHom.ofLinearMap L h1 hmul).commutes b`.

Establish `hcomp : F.comp (algebraMap B (pq B).P) = f` using `RingHom.ext hFa`. Establish `he1 : F ((pq B).e 1) = x` using `by rw [hFe, δ''.dpow_one hx]`. Establish `he1mem : (pq B).e 1 ∈ (pq B).ext J`. Unfold `PDPoly.ext PDPoly.aug`. Conclude with `Ideal.mem_sup_right (Ideal.subset_span ⟨0, rfl⟩)`.

Establish `hSspan : (pq B).ext J = Ideal.span ((algebraMap B (pq B).P '' (J : Set B)) ∪ Set.range fun n : ℕ => (pq B).e (n + 1))`. Rewrite using `[Ideal.span_union]`. Both sides reduce to the same expression. Establish `hS' : ∀ s ∈ (algebraMap B (pq B).P '' (J : Set B)) ∪ Set.range fun n : ℕ => (pq B).e (n + 1), F s ∈ J''`. Introduce and unpack `s (⟨j, hj, rfl⟩ | ⟨n, rfl⟩)`.

Rewrite using `[hFa]`. Conclude with `hf.ideal_comp (Ideal.mem_map_of_mem f hj)`. Rewrite using `[hFe]`. Conclude with `δ''.dpow_mem (Nat.succ_ne_zero n) hx`. Establish `hdpS : ∀ {n : ℕ}, ∀ a ∈ (algebraMap B (pq B).P '' (J : Set B)) ∪ Set.range fun n : ℕ => (pq B).e (n + 1), F ((eta δ).dpow n a) = δ''.dpow n (F a)`.

Introduce `n a ha`. Break down `ha with ⟨j, hj, rfl⟩ | ⟨m, rfl⟩` into its components or cases. Rewrite using `[hη.dp.dpow_comp j hj, hFa, hFa, hf.dpow_comp j hj]`. Simplify using `only`. Establish `hv : (pq B).e (m + 1) = (eta δ).dpow (m + 1) ((pq B).e 1)` using `(hη.var (m + 1)).symm`.

Rewrite using `[hv, (eta δ).dpow_comp (Nat.succ_ne_zero m) he1mem]`. Simplify using `only [hη.var, map_mul, map_natCast, hFe]`. Rewrite using `[δ''.dpow_comp (Nat.succ_ne_zero m) hx]`. Establish `hdp : IsDPMorphism (eta δ) δ'' F` using `IsDPMorphism.on_span (eta δ) δ'' hSspan hS' hdpS`. Use `⟨F, ⟨hcomp, he1, hdp⟩, ?_⟩` and prove the remaining obligations.

Introduce and unpack `G ⟨hG1, hG2, hG3⟩`. Establish `hGa : ∀ b, G (algebraMap B (pq B).P b) = f b` using `fun b => RingHom.congr_fun hG1 b`. Establish `hGe : ∀ n, G ((pq B).e n) = δ''.dpow n x`. Introduce `n`. Rewrite using `[← hη.var n, ← hG3.dpow_comp _ he1mem, hG2]`.

Set `Ga : (pq B).P →ₐ[B] C` to `{ G with commutes' := hGa }`. Establish `hlin : Ga.toLinearMap = L` using `(pq B).e.ext fun n => by show G ((pq B).e n) = L ((pq B).e n)`. Rewrite using `[hGe, hL]`. Use extensionality with `p`. Conclude with `LinearMap.congr_fun hlin p`.
-/
theorem pdPoly_universal : ∀ {B : Type} [CommRing B] {J : Ideal B} (δ : DividedPowers J) {C : Type} [CommRing C] {J'' : Ideal C} (δ'' : DividedPowers J'') (f : B →+* C), IsDPMorphism δ δ'' f → ∀ x ∈ J'', ∃! F : (pq B).P →+* C, F.comp (algebraMap B (pq B).P) = f ∧ F ((pq B).e 1) = x ∧ IsDPMorphism (eta δ) δ'' F := by
  intro B _ J δ C _ J'' δ'' f hf x hx
  have hη : (pq B).IsStd δ (eta δ) := by
    unfold eta
    exact Classical.choose_spec (FubiniStudyChowHeightFormula₂.Adr.exists_std B J δ (pq B))
  letI : Algebra B C := f.toAlgebra
  let L : (pq B).P →ₗ[B] C := (pq B).e.constr ℕ fun n => δ''.dpow n x
  have hL : ∀ n, L ((pq B).e n) = δ''.dpow n x := fun n => (pq B).e.constr_basis ℕ _ n
  have h1 : L 1 = 1 := by
    rw [← (pq B).e_zero, hL, δ''.dpow_zero hx]
  have hbil : (LinearMap.mul B (pq B).P).compr₂ L = (LinearMap.mul B C).compl₁₂ L L := by
    refine (pq B).e.ext fun m => (pq B).e.ext fun n => ?_
    show L ((pq B).e m * (pq B).e n) = L ((pq B).e m) * L ((pq B).e n)
    rw [(pq B).e_mul, ← nsmul_eq_mul, map_nsmul]
    simp only [hL]
    rw [nsmul_eq_mul, δ''.mul_dpow hx]
  have hmul : ∀ a b, L (a * b) = L a * L b := fun a b => LinearMap.congr_fun₂ hbil a b
  let F : (pq B).P →+* C := (AlgHom.ofLinearMap L h1 hmul).toRingHom
  have hFL : ∀ p, F p = L p := fun p => rfl
  have hFe : ∀ n, F ((pq B).e n) = δ''.dpow n x := fun n => (hFL _).trans (hL n)
  have hFa : ∀ b, F (algebraMap B (pq B).P b) = f b := fun b =>
    (AlgHom.ofLinearMap L h1 hmul).commutes b
  have hcomp : F.comp (algebraMap B (pq B).P) = f := RingHom.ext hFa
  have he1 : F ((pq B).e 1) = x := by rw [hFe, δ''.dpow_one hx]
  have he1mem : (pq B).e 1 ∈ (pq B).ext J := by
    unfold PDPoly.ext PDPoly.aug
    exact Ideal.mem_sup_right (Ideal.subset_span ⟨0, rfl⟩)
  have hSspan : (pq B).ext J = Ideal.span ((algebraMap B (pq B).P '' (J : Set B)) ∪
      Set.range fun n : ℕ => (pq B).e (n + 1)) := by
    rw [Ideal.span_union]
    rfl
  have hS' : ∀ s ∈ (algebraMap B (pq B).P '' (J : Set B)) ∪ Set.range fun n : ℕ => (pq B).e (n + 1),
      F s ∈ J'' := by
    rintro s (⟨j, hj, rfl⟩ | ⟨n, rfl⟩)
    · rw [hFa]
      exact hf.ideal_comp (Ideal.mem_map_of_mem f hj)
    · rw [hFe]
      exact δ''.dpow_mem (Nat.succ_ne_zero n) hx
  have hdpS : ∀ {n : ℕ}, ∀ a ∈ (algebraMap B (pq B).P '' (J : Set B)) ∪
      Set.range fun n : ℕ => (pq B).e (n + 1), F ((eta δ).dpow n a) = δ''.dpow n (F a) := by
    intro n a ha
    rcases ha with ⟨j, hj, rfl⟩ | ⟨m, rfl⟩
    · rw [hη.dp.dpow_comp j hj, hFa, hFa, hf.dpow_comp j hj]
    · dsimp only
      have hv : (pq B).e (m + 1) = (eta δ).dpow (m + 1) ((pq B).e 1) := (hη.var (m + 1)).symm
      rw [hv, (eta δ).dpow_comp (Nat.succ_ne_zero m) he1mem]
      simp only [hη.var, map_mul, map_natCast, hFe]
      rw [δ''.dpow_comp (Nat.succ_ne_zero m) hx]
  have hdp : IsDPMorphism (eta δ) δ'' F := IsDPMorphism.on_span (eta δ) δ'' hSspan hS' hdpS
  refine ⟨F, ⟨hcomp, he1, hdp⟩, ?_⟩
  rintro G ⟨hG1, hG2, hG3⟩
  have hGa : ∀ b, G (algebraMap B (pq B).P b) = f b := fun b => RingHom.congr_fun hG1 b
  have hGe : ∀ n, G ((pq B).e n) = δ''.dpow n x := by
    intro n
    rw [← hη.var n, ← hG3.dpow_comp _ he1mem, hG2]
  let Ga : (pq B).P →ₐ[B] C := { G with commutes' := hGa }
  have hlin : Ga.toLinearMap = L := (pq B).e.ext fun n => by
    show G ((pq B).e n) = L ((pq B).e n)
    rw [hGe, hL]
  ext p
  exact LinearMap.congr_fun hlin p

end GlobalTheory.CompanionTheory.PDUniv

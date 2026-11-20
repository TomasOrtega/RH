import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TopPairDForm
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsAffineStableLieEigenspaceFrame
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.HSApp GlobalTheory.Cartier
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW secZ ptF LiesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR levDet secRing move)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.OrbitSep

namespace GlobalTheory.LogKSDiv.SpreadFrame

open scoped Matrix

/- English proof (translation)
Use `choose u hu using fun i => IsLocalization.exists_of_eq (M := M) (S := L) (h i)`. Use `⟨∏ i, (u i : R), M.prod_mem fun i _ => (u i).2, fun S _ ψ hψ i => ?_⟩` and prove the remaining obligations. Establish `hp : IsUnit (ψ (u i))` using `isUnit_of_dvd_unit (map_dvd ψ (Finset.dvd_prod_of_mem (fun p => (u p : R)) (Finset.mem_univ i))) hψ`. Use `congrArg ψ (hu i)` as an intermediate fact. Rewrite `this` using `[map_mul, map_mul]`.

Conclude with `hp.mul_left_cancel this`.
-/
theorem clear_eq {R L : Type} [CommRing R] [CommRing L] [Algebra R L] (M : Submonoid R) [IsLocalization M L]
    {ι : Type} [Fintype ι] (X Y : ι → R) (h : ∀ i, algebraMap R L (X i) = algebraMap R L (Y i)) :
    ∃ u ∈ M, ∀ (S : Type) [CommRing S] (ψ : R →+* S), IsUnit (ψ u) → ∀ i, ψ (X i) = ψ (Y i) := by
  classical
  choose u hu using fun i => IsLocalization.exists_of_eq (M := M) (S := L) (h i)
  refine ⟨∏ i, (u i : R), M.prod_mem fun i _ => (u i).2, fun S _ ψ hψ i => ?_⟩
  have hp : IsUnit (ψ (u i)) :=
    isUnit_of_dvd_unit (map_dvd ψ (Finset.dvd_prod_of_mem (fun p => (u p : R)) (Finset.mem_univ i))) hψ
  have := congrArg ψ (hu i)
  rw [map_mul, map_mul] at this
  exact hp.mul_left_cancel this

/- English proof (translation)
Establish `hs : ∀ {S : Type} [CommRing S] (B : Fin N → Fin n → S) (a : Fin N → S), ∑ j, a j • B j = (Matrix.of B)ᵀ *ᵥ a` using `fun B a => by`. Use function extensionality and compare the values at `i`. Simplify using `[Matrix.mulVec, dotProduct, Finset.sum_apply, mul_comm]`. Use `choose A hA using fun k => (hu (Pi.single k 1)).exists`. Set `Bm : Matrix (Fin n) (Fin N) L` to `(Matrix.of B)ᵀ`.

Set `Am : Matrix (Fin N) (Fin n) L` to `(Matrix.of A)ᵀ`. Establish `h1 : Bm * Am = 1`. Use extensionality with `i k`. Use `congrFun (hA k) i` as an intermediate fact. Rewrite `this` using `[hs]`.

Simplify `this.symm` using `[Bm, Am, Matrix.mul_apply, Matrix.mulVec, dotProduct, Pi.single_apply, Matrix.one_apply, eq_comm]`. Establish `h2 : Am * Bm = 1`. Use extensionality with `i j`. Establish `e1 : B j = ∑ k, (Am *ᵥ B j) k • B k`. Rewrite using `[hs, Matrix.mulVec_mulVec, h1, Matrix.one_mulVec]`.

Establish `e2 : B j = ∑ k, (Pi.single j 1 : Fin N → L) k • B k`. Simplify using `[Pi.single_apply]`. Use `congrFun ((hu (B j)).unique e1 e2) i` as an intermediate fact. Simplify `this` using `[Bm, Matrix.mul_apply, Matrix.mulVec, dotProduct, Pi.single_apply, Matrix.one_apply]`. Take `⟨s, hsB⟩` from `IsLocalization.exist_integer_multiples M Finset.univ (fun p : Fin n × Fin N => Bm p.1 p.2)`.

Take `⟨s', hsA⟩` from `IsLocalization.exist_integer_multiples M Finset.univ (fun p : Fin N × Fin n => Am p.1 p.2)`. Use `choose B₁ hB₁ using fun i j => hsB (i, j) (Finset.mem_univ _)`. Use `choose A₁ hA₁ using fun i j => hsA (i, j) (Finset.mem_univ _)`. Establish `eB : (Matrix.of B₁).map (algebraMap R L) = (s : R) • Bm` using `by ext i j; exact hB₁ i j`. Establish `eA : (Matrix.of A₁).map (algebraMap R L) = (s' : R) • Am` using `by ext i j; exact hA₁ i j`.

Establish `sm : ∀ {S : Type} [CommRing S] (ψ : R →+* S) {a b : ℕ} (r : R) (X : Matrix (Fin a) (Fin b) R), (r • X).map ψ = ψ r • X.map ψ` using `fun ψ _ _ r X => by ext i j; simp`. Establish `cl : ∀ {a b : ℕ} (X Y : Matrix (Fin a) (Fin b) R), X.map (algebraMap R L) = Y.map (algebraMap R L) → ∃ u ∈ M, ∀ (S : Type) [CommRing S] (ψ : R →+* S), IsUnit (ψ u) → X.map ψ = Y.map ψ` using `fun {a b} X Y h => by`. Take `⟨u, hu, k⟩` from `clear_eq M (fun p : Fin a × Fin b => X p.1 p.2) (fun p => Y p.1 p.2) (fun p => congrFun (congrFun h p.1) p.2)`. Conclude with `⟨u, hu, fun S _ ψ hψ => Matrix.ext fun i j => k S ψ hψ (i, j)⟩`. Take `⟨u₁, hu₁, k₁⟩` from `cl (Matrix.of B₁ * Matrix.of A₁) (((s : R) * s') • 1) (by`.

Rewrite using `[Matrix.map_mul, eB, eA, Matrix.smul_mul, Matrix.mul_smul, h1, sm, algebraMap_smul, mul_smul, Matrix.map_one _ (map_zero _) (map_one _)])`. Take `⟨u₂, hu₂, k₂⟩` from `cl (Matrix.of A₁ * Matrix.of B₁) (((s : R) * s') • 1) (by`. Rewrite using `[Matrix.map_mul, eB, eA, Matrix.smul_mul, Matrix.mul_smul, h2, sm, algebraMap_smul, mul_comm, mul_smul, Matrix.map_one _ (map_zero _) (map_one _)])`. Take `⟨u₃, hu₃, k₃⟩` from `clear_eq M (fun p : Fin N × Fin n => (P p.1 *ᵥ fun i => B₁ i p.1) p.2) (fun p => B₁ p.2 p.1) (fun p => by`. Establish `e : (algebraMap R L ∘ fun i => B₁ i p.1) = algebraMap R L (s : R) • B p.1`.

Use function extensionality and compare the values at `i`. Simplify using `only [Function.comp_apply, Pi.smul_apply, smul_eq_mul]`. Rewrite using `[hB₁, Algebra.smul_def]`. Both sides reduce to the same expression. Use `congrFun (hP p.1) p.2` as an intermediate fact.

Rewrite using `[show (algebraMap R L ((P p.1 *ᵥ fun i => B₁ i p.1) p.2)) = ((P p.1).map (algebraMap R L) *ᵥ (algebraMap R L ∘ fun i => B₁ i p.1)) p.2 from (RingHom.map_mulVec _ _ _ _), e, Matrix.mulVec_smul, Pi.smul_apply, this, hB₁]`. Simplify using `only [smul_eq_mul, Algebra.smul_def]`. Use the proof step `rfl)`. Use `⟨u₁ * u₂ * u₃ * (s * s'), M.mul_mem (M.mul_mem (M.mul_mem hu₁ hu₂) hu₃) (M.mul_mem s.2 s'.2), s, fun j i => B₁ i j, fun j i => by rw [hB₁, Algebra.smul_def]; rfl, fun S _ ψ hψ => ?_⟩` and prove the remaining obligations. Rewrite `hψ` using `[map_mul, map_mul, map_mul, map_mul, IsUnit.mul_iff, IsUnit.mul_iff, IsUnit.mul_iff, IsUnit.mul_iff]`.

Take `⟨⟨⟨w₁, w₂⟩, w₃⟩, ws, ws'⟩` from `hψ`. Establish `q₁` using `k₁ S ψ w₁`. Establish `q₂` using `k₂ S ψ w₂`. Rewrite `q₁`, `q₂` using `[Matrix.map_mul, sm, Matrix.map_one _ (map_zero _) (map_one _)]`. Establish `hw : IsUnit (ψ ((s : R) * s'))` using `by rw [map_mul]; exact ws.mul ws'`.

Take `⟨w, hw'⟩` from `hw`. Rewrite `q₁`, `q₂` using `[← hw']`. Establish `eb : (Matrix.of fun j => ψ ∘ fun i => B₁ i j)ᵀ = (Matrix.of B₁).map ψ` using `rfl`. Generalize the expression as in `(Matrix.of A₁).map ψ = A' at q₁ q₂`. Establish `can : ∀ {a : ℕ} {x y : Fin a → S}, (w : S) • x = (w : S) • y → x = y` using `fun h => (MulAction.injective w : Function.Injective fun x => w • x) h`.

Use `⟨ws, fun j => ?_, fun v => ?_⟩` and prove the remaining obligations. Use function extensionality and compare the values at `i`. Use `k₃ S ψ w₃ (j, i)` as an intermediate fact. Simplify using `only at this`. Rewrite `this` using `[RingHom.map_mulVec]`.

Conclude with `this`. Simplify using `only [hs, eb]`. Use `⟨(↑w⁻¹ : S) • (A' *ᵥ v), can ?_, fun a ha => can ?_⟩` and prove the remaining obligations. Rewrite using `[Matrix.mulVec_smul, Matrix.mulVec_mulVec, q₁, Matrix.smul_mulVec, Matrix.one_mulVec, smul_smul, Units.mul_inv, one_smul]`. Rewrite using `[smul_smul, Units.mul_inv, one_smul, ha, Matrix.mulVec_mulVec, q₂, Matrix.smul_mulVec, Matrix.one_mulVec]`.
-/
theorem spread_exact {R L : Type} [CommRing R] [CommRing L] [Algebra R L] (M : Submonoid R) [IsLocalization M L]
    {n N : ℕ} (B : Fin N → Fin n → L) (hu : ∀ v, ∃! a : Fin N → L, v = ∑ j, a j • B j)
    (P : Fin N → Matrix (Fin n) (Fin n) R) (hP : ∀ j, (P j).map (algebraMap R L) *ᵥ B j = B j) :
    ∃ g ∈ M, ∃ (s : R) (B₀ : Fin N → Fin n → R), (∀ j i, algebraMap R L (B₀ j i) = algebraMap R L s * B j i) ∧
      ∀ (S : Type) [CommRing S] (ψ : R →+* S), IsUnit (ψ g) → IsUnit (ψ s) ∧
        (∀ j, (P j).map ψ *ᵥ (ψ ∘ B₀ j) = ψ ∘ B₀ j) ∧ ∀ v, ∃! a : Fin N → S, v = ∑ j, a j • (ψ ∘ B₀ j) := by
  classical
  have hs : ∀ {S : Type} [CommRing S] (B : Fin N → Fin n → S) (a : Fin N → S),
      ∑ j, a j • B j = (Matrix.of B)ᵀ *ᵥ a := fun B a => by
    funext i
    simp [Matrix.mulVec, dotProduct, Finset.sum_apply, mul_comm]
  choose A hA using fun k => (hu (Pi.single k 1)).exists
  let Bm : Matrix (Fin n) (Fin N) L := (Matrix.of B)ᵀ
  let Am : Matrix (Fin N) (Fin n) L := (Matrix.of A)ᵀ
  have h1 : Bm * Am = 1 := by
    ext i k
    have := congrFun (hA k) i
    rw [hs] at this
    simpa [Bm, Am, Matrix.mul_apply, Matrix.mulVec, dotProduct, Pi.single_apply, Matrix.one_apply, eq_comm] using
      this.symm
  have h2 : Am * Bm = 1 := by
    ext i j
    have e1 : B j = ∑ k, (Am *ᵥ B j) k • B k := by
      rw [hs, Matrix.mulVec_mulVec, h1, Matrix.one_mulVec]
    have e2 : B j = ∑ k, (Pi.single j 1 : Fin N → L) k • B k := by
      simp [Pi.single_apply]
    have := congrFun ((hu (B j)).unique e1 e2) i
    simpa [Bm, Matrix.mul_apply, Matrix.mulVec, dotProduct, Pi.single_apply, Matrix.one_apply] using this
  obtain ⟨s, hsB⟩ := IsLocalization.exist_integer_multiples M Finset.univ (fun p : Fin n × Fin N => Bm p.1 p.2)
  obtain ⟨s', hsA⟩ := IsLocalization.exist_integer_multiples M Finset.univ (fun p : Fin N × Fin n => Am p.1 p.2)
  choose B₁ hB₁ using fun i j => hsB (i, j) (Finset.mem_univ _)
  choose A₁ hA₁ using fun i j => hsA (i, j) (Finset.mem_univ _)
  have eB : (Matrix.of B₁).map (algebraMap R L) = (s : R) • Bm := by ext i j; exact hB₁ i j
  have eA : (Matrix.of A₁).map (algebraMap R L) = (s' : R) • Am := by ext i j; exact hA₁ i j
  have sm : ∀ {S : Type} [CommRing S] (ψ : R →+* S) {a b : ℕ} (r : R) (X : Matrix (Fin a) (Fin b) R),
      (r • X).map ψ = ψ r • X.map ψ := fun ψ _ _ r X => by ext i j; simp
  have cl : ∀ {a b : ℕ} (X Y : Matrix (Fin a) (Fin b) R), X.map (algebraMap R L) = Y.map (algebraMap R L) →
      ∃ u ∈ M, ∀ (S : Type) [CommRing S] (ψ : R →+* S), IsUnit (ψ u) → X.map ψ = Y.map ψ := fun {a b} X Y h => by
    obtain ⟨u, hu, k⟩ := clear_eq M (fun p : Fin a × Fin b => X p.1 p.2) (fun p => Y p.1 p.2)
      (fun p => congrFun (congrFun h p.1) p.2)
    exact ⟨u, hu, fun S _ ψ hψ => Matrix.ext fun i j => k S ψ hψ (i, j)⟩
  obtain ⟨u₁, hu₁, k₁⟩ := cl (Matrix.of B₁ * Matrix.of A₁) (((s : R) * s') • 1) (by
    rw [Matrix.map_mul, eB, eA, Matrix.smul_mul, Matrix.mul_smul, h1, sm, algebraMap_smul, mul_smul,
      Matrix.map_one _ (map_zero _) (map_one _)])
  obtain ⟨u₂, hu₂, k₂⟩ := cl (Matrix.of A₁ * Matrix.of B₁) (((s : R) * s') • 1) (by
    rw [Matrix.map_mul, eB, eA, Matrix.smul_mul, Matrix.mul_smul, h2, sm, algebraMap_smul, mul_comm, mul_smul,
      Matrix.map_one _ (map_zero _) (map_one _)])
  obtain ⟨u₃, hu₃, k₃⟩ := clear_eq M (fun p : Fin N × Fin n => (P p.1 *ᵥ fun i => B₁ i p.1) p.2)
    (fun p => B₁ p.2 p.1) (fun p => by
      have e : (algebraMap R L ∘ fun i => B₁ i p.1) = algebraMap R L (s : R) • B p.1 := by
        funext i; simp only [Function.comp_apply, Pi.smul_apply, smul_eq_mul]; rw [hB₁, Algebra.smul_def]; rfl
      have := congrFun (hP p.1) p.2
      rw [show (algebraMap R L ((P p.1 *ᵥ fun i => B₁ i p.1) p.2)) =
          ((P p.1).map (algebraMap R L) *ᵥ (algebraMap R L ∘ fun i => B₁ i p.1)) p.2 from
          (RingHom.map_mulVec _ _ _ _), e, Matrix.mulVec_smul, Pi.smul_apply, this, hB₁]
      simp only [smul_eq_mul, Algebra.smul_def]; rfl)
  refine ⟨u₁ * u₂ * u₃ * (s * s'), M.mul_mem (M.mul_mem (M.mul_mem hu₁ hu₂) hu₃) (M.mul_mem s.2 s'.2), s,
    fun j i => B₁ i j, fun j i => by rw [hB₁, Algebra.smul_def]; rfl, fun S _ ψ hψ => ?_⟩
  rw [map_mul, map_mul, map_mul, map_mul, IsUnit.mul_iff, IsUnit.mul_iff, IsUnit.mul_iff, IsUnit.mul_iff] at hψ
  obtain ⟨⟨⟨w₁, w₂⟩, w₃⟩, ws, ws'⟩ := hψ
  have q₁ := k₁ S ψ w₁
  have q₂ := k₂ S ψ w₂
  rw [Matrix.map_mul, sm, Matrix.map_one _ (map_zero _) (map_one _)] at q₁ q₂
  have hw : IsUnit (ψ ((s : R) * s')) := by rw [map_mul]; exact ws.mul ws'
  obtain ⟨w, hw'⟩ := hw
  rw [← hw'] at q₁ q₂
  have eb : (Matrix.of fun j => ψ ∘ fun i => B₁ i j)ᵀ = (Matrix.of B₁).map ψ := rfl
  generalize (Matrix.of A₁).map ψ = A' at q₁ q₂
  have can : ∀ {a : ℕ} {x y : Fin a → S}, (w : S) • x = (w : S) • y → x = y := fun h =>
    (MulAction.injective w : Function.Injective fun x => w • x) h
  refine ⟨ws, fun j => ?_, fun v => ?_⟩
  · funext i
    have := k₃ S ψ w₃ (j, i)
    simp only at this
    rw [RingHom.map_mulVec] at this
    exact this
  · simp only [hs, eb]
    refine ⟨(↑w⁻¹ : S) • (A' *ᵥ v), can ?_, fun a ha => can ?_⟩
    · rw [Matrix.mulVec_smul, Matrix.mulVec_mulVec, q₁, Matrix.smul_mulVec, Matrix.one_mulVec, smul_smul,
        Units.mul_inv, one_smul]
    · rw [smul_smul, Units.mul_inv, one_smul, ha, Matrix.mulVec_mulVec, q₂, Matrix.smul_mulVec, Matrix.one_mulVec]

/- English proof (translation)
Introduce `v`. Establish `split : ∀ a : (Σ τ, κ τ) → S, ∑ j, a j • b j.1 j.2 = ∑ τ, ∑ i, a ⟨τ, i⟩ • b τ i` using `fun a => Fintype.sum_sigma _`. Use `choose c hc hcu using fun τ => hbu τ (p τ v) (hp1 τ v)`. Use `⟨fun j => c j.1 j.2, ?_, fun a ha => ?_⟩` and prove the remaining obligations. Use `show v = _`.

Rewrite using `[split]`. Combine the equalities or inequalities in the displayed calculation. Use function extensionality and compare the values at `j`. Take `⟨τ, i⟩` from `j`. Establish `ha : v = _` using `ha`.

Rewrite `ha` using `[split]`. Establish `hm : ∀ σ, (∑ i, a ⟨σ, i⟩ • b σ i) ∈ W σ` using `fun σ => Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (hb σ i)`. Establish `e` using `hp2 _ hm τ`. Rewrite `e` using `[← ha]`. Conclude with `congrFun (hcu τ (fun i => a ⟨τ, i⟩) e) i`.
-/
theorem basis_of_split {S M ι : Type} [CommRing S] [AddCommGroup M] [Module S M] [Fintype ι] [DecidableEq ι]
    (p : ι → Module.End S M) (hsum : ∑ τ, p τ = 1) (W : ι → Submodule S M) (hp1 : ∀ τ m, p τ m ∈ W τ)
    (hp2 : ∀ mm : ι → M, (∀ σ, mm σ ∈ W σ) → ∀ τ, p τ (∑ σ, mm σ) = mm τ)
    {κ : ι → Type} [∀ τ, Fintype (κ τ)] (b : ∀ τ, κ τ → M) (hb : ∀ τ i, b τ i ∈ W τ)
    (hbu : ∀ τ w, w ∈ W τ → ∃! a : κ τ → S, w = ∑ i, a i • b τ i) :
    ∀ v, ∃! a : (Σ τ, κ τ) → S, v = ∑ j, a j • b j.1 j.2 := by
  intro v
  have split : ∀ a : (Σ τ, κ τ) → S, ∑ j, a j • b j.1 j.2 = ∑ τ, ∑ i, a ⟨τ, i⟩ • b τ i :=
    fun a => Fintype.sum_sigma _
  choose c hc hcu using fun τ => hbu τ (p τ v) (hp1 τ v)
  refine ⟨fun j => c j.1 j.2, ?_, fun a ha => ?_⟩
  · show v = _
    rw [split]
    calc v = (∑ τ, p τ) v := by rw [hsum]; rfl
      _ = _ := by rw [LinearMap.sum_apply]; exact Finset.sum_congr rfl fun τ _ => hc τ
  · funext j
    obtain ⟨τ, i⟩ := j
    have ha : v = _ := ha
    rw [split] at ha
    have hm : ∀ σ, (∑ i, a ⟨σ, i⟩ • b σ i) ∈ W σ := fun σ =>
      Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (hb σ i)
    have e := hp2 _ hm τ
    rw [← ha] at e
    exact congrFun (hcu τ (fun i => a ⟨τ, i⟩) e) i

end GlobalTheory.LogKSDiv.SpreadFrame

namespace GlobalTheory.LogKSDiv.SpreadFrame

/- English proof (translation)
Rewrite using `[ReciprocityTheory.ChartRestriction.G.PullbackSections.spMap_comp_spMap, ReciprocityTheory.ChartRestriction.G.PullbackSections.spMap_comp_spMap]`. Use `congr 1`. Use `RingHom.ext fun z => ?_` and prove the remaining obligations. Apply the tactic sequence `ext <;> simp [epsMul, dualMap, mul_comm]`.
-/
theorem eps_dual {R S : Type} [CommRing R] [CommRing S] (θ : R →+* S) (c : R) :
    spMap (epsMul (θ c)) ≫ spMap (dualMap θ) = spMap (dualMap θ) ≫ spMap (epsMul c) := by
  rw [ReciprocityTheory.ChartRestriction.G.PullbackSections.spMap_comp_spMap, ReciprocityTheory.ChartRestriction.G.PullbackSections.spMap_comp_spMap]
  congr 1
  refine RingHom.ext fun z => ?_
  ext <;> simp [epsMul, dualMap, mul_comm]

/- English proof (translation)
Rewrite using `[ReciprocityTheory.ChartRestriction.G.PullbackSections.spMap_comp_spMap]`. Use `congr 1`. Use `RingHom.ext fun z => ?_` and prove the remaining obligations. Apply the tactic sequence `ext <;> simp [dualMap]`.
-/
theorem dual_dual {R S T : Type} [CommRing R] [CommRing S] [CommRing T] (θ : S →+* T) (l : R →+* S) :
    spMap (dualMap θ) ≫ spMap (dualMap l) = spMap (dualMap (θ.comp l)) := by
  rw [ReciprocityTheory.ChartRestriction.G.PullbackSections.spMap_comp_spMap]
  congr 1
  refine RingHom.ext fun z => ?_
  ext <;> simp [dualMap]

/- English proof (translation)
Take `⟨u, rfl⟩` from `hu`. Establish `e : spMap (epsMul ((u⁻¹ : Rˣ) : R)) ≫ spMap (epsMul (u : R)) = 𝟙 _`. Rewrite using `[ReciprocityTheory.ChartRestriction.G.PullbackSections.spMap_comp_spMap, ← Spec.map_id]`. Use `congr 1`. Apply the tactic sequence `ext z <;> simp [epsMul]`.

Combine the equalities or inequalities in the displayed calculation.
-/
theorem cancel_eps {R : Type} [CommRing R] {T : Scheme.{0}} {a b : Sp (DualNumber R) ⟶ T} {u : R} (hu : IsUnit u)
    (h : spMap (epsMul u) ≫ a = spMap (epsMul u) ≫ b) : a = b := by
  obtain ⟨u, rfl⟩ := hu
  have e : spMap (epsMul ((u⁻¹ : Rˣ) : R)) ≫ spMap (epsMul (u : R)) = 𝟙 _ := by
    rw [ReciprocityTheory.ChartRestriction.G.PullbackSections.spMap_comp_spMap, ← Spec.map_id]
    congr 1
    ext z <;> simp [epsMul]
  calc a = (spMap (epsMul ((u⁻¹ : Rˣ) : R)) ≫ spMap (epsMul (u : R))) ≫ a := by rw [e, Category.id_comp]
    _ = (spMap (epsMul ((u⁻¹ : Rˣ) : R)) ≫ spMap (epsMul (u : R))) ≫ b := by rw [Category.assoc, h, Category.assoc]
    _ = b := by rw [e, Category.id_comp]

end GlobalTheory.LogKSDiv.SpreadFrame

section Spread

attribute [local instance] Over.cartesianMonoidalCategory

open MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj

set_option maxHeartbeats 400000 in
open GlobalTheory.LieLocBasis GlobalTheory.ShFam.EigLoc GlobalTheory.ShFam.EigSpread in

/- English proof (translation)
Introduce `E _ _ _ H Dw l Xo c TF Z _ x φ f hφ`. Set `y : TF.Y.X` to `(barComp TF.Y Z).ι x`. Establish `hyb : y ∈ barComp TF.Y Z` using `by show (barComp TF.Y Z).ι x ∈ _`. Use `Scheme.Opens.ι_apply (barComp TF.Y Z) x` as an intermediate fact. Conclude with `this ▸ x.2`.

Use `replace hφ : (X₀ TF.Y Z).fromSpecStalk x ≫ (barComp TF.Y Z).ι ≫ TF.Y.s = spMap φ := hφ`. Take `⟨f, rfl⟩ : ∃ f' : ShFam.EigFrame TF.Y φ ((X₀ TF.Y Z).fromSpecStalk x ≫ (barComp TF.Y Z).ι), f' = f` from `⟨f, rfl⟩`. Take `⟨U₀, hU₀, hy, x₀, hx₀, C, m, xc, hxc⟩` from `exists_affine_chart TF.Y.t (𝟙 TF.Y.X) y`. Set `lam : Γ(TF.Y.X, U₀) →+* (X₀ TF.Y Z).presheaf.stalk x` to `(TF.Y.X.presheaf.germ U₀ y hy ≫ (barComp TF.Y Z).ι.stalkMap x).hom`. Use `letI : Algebra Γ(TF.Y.X, U₀) ((X₀ TF.Y Z).presheaf.stalk x) := lam.toAlgebra`.

Use `letI : Algebra Γ(TF.Y.X, U₀) (TF.Y.X.presheaf.stalk y) := TopCat.Presheaf.algebra_section_stalk TF.Y.X.presheaf ⟨y, hy⟩`. Establish `hloc0` using `hU₀.isLocalization_stalk ⟨y, hy⟩`. Establish `hloc : IsLocalization (hU₀.primeIdealOf ⟨y, hy⟩).asIdeal.primeCompl ((X₀ TF.Y Z).presheaf.stalk x)`. Set `e` to `(asIso ((barComp TF.Y Z).ι.stalkMap x)).commRingCatIsoToRingEquiv`. Conclude with `IsLocalization.isLocalization_of_algEquiv (S := TF.Y.X.presheaf.stalk y) _ { e with commutes' := fun r => rfl }`.

Establish `hpt : (X₀ TF.Y Z).fromSpecStalk x ≫ (barComp TF.Y Z).ι = spMap lam ≫ x₀`. Rewrite using `[hx₀, Category.comp_id, ← Scheme.SpecMap_stalkMap_fromSpecStalk]`. Rewrite using `[show TF.Y.X.fromSpecStalk ((barComp TF.Y Z).ι x) = TF.Y.X.fromSpecStalk y from rfl, ← hU₀.fromSpecStalk_eq_fromSpecStalk hy]`. Simplify using `only [lam, spMap, CommRingCat.ofHom_hom, Spec.map_comp, Category.assoc, IsAffineOpen.fromSpecStalk]`. Set `φ₀ : c.F →+* Γ(TF.Y.X, U₀)` to `(Spec.preimage (x₀ ≫ TF.Y.s)).hom`.

Establish `hφ₀ : spMap φ₀ = x₀ ≫ TF.Y.s` using `Spec.map_preimage _`. Establish `hφl : φ = lam.comp φ₀` using `spMap_inj (by`. Rewrite using `[← hφ, ← ReciprocityTheory.ChartRestriction.G.PullbackSections.spMap_comp_spMap, hφ₀, ← Category.assoc, hpt, Category.assoc])`. Substitute `hφl` using the available equality. Take `⟨xL, hxL, hvL⟩` from `vec_bc_of_chart C hxc lam hpt`.

Use `choose B hB using fun τ i => vec_exists hxL _ (f.tan τ i)`. Take `⟨P, hP⟩` from `exists_projectors c φ₀ hxc`. Establish `hPL` using `hP lam hxL hvL`. Establish `hBe : ∀ τ i, B τ i ∈ eig c (lam.comp φ₀) hxL τ` using `fun τ i => (vec_eig_iff hxL _ _).1 fun a => by rw [← hB]; exact f.eig τ i a`. Establish `hBu : ∀ τ w, w ∈ eig c (lam.comp φ₀) hxL τ → ∃! a : Fin (Dw.mult τ) → (X₀ TF.Y Z).presheaf.stalk x, w = ∑ i, a i • B τ i` using `fun τ w hw => by`.

Use `f.basis τ _ (vec_tan hxL w) ((vec_eig_iff hxL _ _).2 hw)` as an intermediate fact. Rewrite `this` using `[show f.v τ = fun i => vec TF.Y.t _ xL (B τ i) from funext (hB τ)]`. Simplify `this` using `only [comb_iff hxL]`. Establish `: CharZero c.F` using `RingHom.charZero c.F.val.toRingHom`. Take `⟨α, hinj, ⟨fp, hf, hfs⟩, hN⟩` from `ReciprocityTheory.ChartRestriction.G.PullbackSections.exists_sepElt (E := E) (F := c.F) c.F.val.toRingHom (embK c) (fun τ a => embK_coe c τ a)`.

Establish `hbasK : ∀ v : Fin m → (X₀ TF.Y Z).presheaf.stalk x, ∃! a : (Σ τ : E →+* ℂ, Fin (Dw.mult τ)) → (X₀ TF.Y Z).presheaf.stalk x, v = ∑ j, a j • B j.1 j.2`. Use `letI : Algebra c.F ((X₀ TF.Y Z).presheaf.stalk x) := (lam.comp φ₀).toAlgebra`. Use `exact`. Use the proof step `SpreadFrame.basis_of_split (fun τ => ReciprocityTheory.ChartRestriction.G.PullbackSections.proj (rho hxL) (embK c) α τ) (ReciprocityTheory.ChartRestriction.G.PullbackSections.sum_proj _ _ _ hinj) (fun τ => eig c (lam.comp φ₀) hxL τ) (fun τ m' => by`. Rewrite using `[ReciprocityTheory.ChartRestriction.G.Chart.mem_eigLat_iff]`.

Conclude with `ReciprocityTheory.ChartRestriction.G.PullbackSections.eig_of_alpha (rho hxL) (embK c) α hN τ (ReciprocityTheory.ChartRestriction.G.PullbackSections.proj_eig_alpha (rho hxL) (embK c) α hinj fp hf hfs τ m'))`. Use the proof step `(fun mm hmm τ => ReciprocityTheory.ChartRestriction.G.PullbackSections.proj_sum_eig (rho hxL) (embK c) α hinj mm (fun σ => by have h := hmm σ; rw [ReciprocityTheory.ChartRestriction.G.Chart.mem_eigLat_iff] at h; exact h) τ) B hBe hBu`. Set `e` to `Fintype.equivFin (Σ τ : E →+* ℂ, Fin (Dw.mult τ))`. Set `Bf : Fin (Fintype.card (Σ τ : E →+* ℂ, Fin (Dw.mult τ))) → Fin m → (X₀ TF.Y Z).presheaf.stalk x` to `fun j => B (e.symm j).1 (e.symm j).2`. Establish `hsum : ∀ a : (Σ τ : E →+* ℂ, Fin (Dw.mult τ)) → (X₀ TF.Y Z).presheaf.stalk x, ∑ j, a (e.symm j) • Bf j = ∑ k, a k • B k.1 k.2` using `fun a => Fintype.sum_equiv e.symm _ (fun k => a k • B k.1 k.2) (fun j => rfl)`.

Establish `hbasF : ∀ v, ∃! a : Fin (Fintype.card (Σ τ : E →+* ℂ, Fin (Dw.mult τ))) → (X₀ TF.Y Z).presheaf.stalk x, v = ∑ j, a j • Bf j`. Introduce `v`. Take `⟨a, ha, hau⟩` from `hbasK v`. Use `⟨fun j => a (e.symm j), by show v = _; rw [hsum]; exact ha, fun a' ha' => funext fun j => ?_⟩` and prove the remaining obligations. Use `replace ha' : v = _ := ha'`.

Establish `h1 : v = ∑ k, (fun k => a' (e k)) k • B k.1 k.2`. Rewrite using `[ha', ← hsum]`. Simplify using `only [Equiv.apply_symm_apply]`. Use `congrFun (hau _ h1) (e.symm j)` as an intermediate fact. Simplify using `using this`.

Take `⟨g, hg, s, B₀, hB₀, hsp⟩` from `SpreadFrame.spread_exact (hU₀.primeIdealOf ⟨y, hy⟩).asIdeal.primeCompl Bf hbasF (fun j => P (e.symm j).1) (fun j => (hPL _ _).2 (hBe _ _))`. Establish `hlg : IsUnit (lam g)` using `IsLocalization.map_units (M := (hU₀.primeIdealOf ⟨y, hy⟩).asIdeal.primeCompl) ((X₀ TF.Y Z).presheaf.stalk x) ⟨g, hg⟩`. Establish `hls : IsUnit (lam s)` using `(hsp _ lam hlg).1`. Take `⟨g', hg'le, hyg'⟩` from `hU₀.exists_basicOpen_le (V := barComp TF.Y Z) ⟨y, hyb⟩ hy`. Establish `hU` using `hU₀.basicOpen (g' * g)`.

Set `U : TF.Y.X.affineOpens` to `⟨TF.Y.X.basicOpen (g' * g), hU⟩`. Set `ψ : Γ(TF.Y.X, U₀) →+* Γ(TF.Y.X, U.1)` to `(TF.Y.X.presheaf.map (homOfLE (TF.Y.X.basicOpen_le (g' * g))).op).hom`. Establish `hψg₀ : IsUnit (ψ (g' * g))` using `TF.Y.X.toRingedSpace.isUnit_res_basicOpen (g' * g)`. Establish `hψg : IsUnit (ψ g)` using `isUnit_of_mul_isUnit_right (by rw [← map_mul]; exact hψg₀)`. Establish `hchart : LogKS.chart U = spMap ψ ≫ x₀`.

Rewrite using `[hx₀, Category.comp_id]`. Conclude with `(hU₀.map_fromSpec hU _).symm`. Take `⟨xU, hxU, hvU⟩` from `vec_bc_of_chart C hxc ψ hchart`. Establish `hPU` using `hP ψ hxU hvU`. Take `⟨hsU, hPψ, hbasψ⟩` from `hsp _ ψ hψg`.

Establish `hyU : y ∈ U.1` using `by show y ∈ TF.Y.X.basicOpen (g' * g)`. Rewrite using `[Scheme.basicOpen_mul]`. Use `⟨hyg', (Scheme.mem_basicOpen _ _ _ hy).2 ?_⟩` and prove the remaining obligations. Conclude with `IsLocalization.map_units (M := (hU₀.primeIdealOf ⟨y, hy⟩).asIdeal.primeCompl) (TF.Y.X.presheaf.stalk y) ⟨g, hg⟩`. Establish `hκ : IsUnit (lam (g' * g))` using `((Scheme.mem_basicOpen _ _ _ hy).1 hyU).map ((barComp TF.Y Z).ι.stalkMap x).hom`.

Set `θ : (X₀ TF.Y Z).presheaf.stalk x →+* (X₀ TF.Y Z).functionField` to `algebraMap _ _`. Use `letI : Algebra Γ(TF.Y.X, U₀) Γ(TF.Y.X, U.1) := ψ.toAlgebra`. Use `haveI : IsLocalization.Away (g' * g) Γ(TF.Y.X, U.1) := hU₀.isLocalization_basicOpen (g' * g)`. Set `ρ : Γ(TF.Y.X, U.1) →+* (X₀ TF.Y Z).functionField` to `IsLocalization.Away.lift (g' * g) (g := θ.comp lam) (hκ.map θ)`. Establish `hρψ : ρ.comp ψ = θ.comp lam` using `IsLocalization.lift_comp _`.

Set `w : Γ(TF.Y.X, U.1)` to `↑hsU.unit⁻¹`. Set `cv : Fin (Fintype.card (Σ τ : E →+* ℂ, Fin (Dw.mult τ))) → Fin m → Γ(TF.Y.X, U.1)` to `fun j => w • (ψ ∘ B₀ j)`. Use `⟨U, le_trans (show TF.Y.X.basicOpen (g' * g) ≤ _ by rw [Scheme.basicOpen_mul]; exact inf_le_left) hg'le, hyU, ρ, _, e, fun j => vec TF.Y.t (LogKS.chart U) xU (cv j), ψ.comp φ₀, ?_, fun j => vec_tan hxU _, ?_, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[hchart, ← Category.assoc, ReciprocityTheory.ChartRestriction.G.PullbackSections.spMap_comp_spMap, hρψ, ← ReciprocityTheory.ChartRestriction.G.PullbackSections.spMap_comp_spMap, Category.assoc, ← hpt, ← Category.assoc]`. Use `congr 1`.

Conclude with `Scheme.SpecMap_stalkSpecializes_fromSpecStalk ((genericPoint_spec (X₀ TF.Y Z)).specializes trivial)`. Introduce `w' hw'`. Take `⟨cc, rfl⟩` from `vec_exists hxU w' hw'`. Simplify using `only [comb_iff hxU]`. Take `⟨a, ha, hau⟩` from `hbasψ cc`.

Use `⟨fun j => a j * ψ s, ?_, fun a' ha' => funext fun j => ?_⟩` and prove the remaining obligations. Use `show cc = _`. Rewrite using `[ha]`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Use `show _ = _ • ((↑hsU.unit⁻¹ : Γ(TF.Y.X, U.1)) • _)`.

Rewrite using `[smul_smul, _root_.mul_assoc, IsUnit.mul_val_inv, _root_.mul_one]`. Use `replace ha' : cc = _ := ha'`. Establish `h1 : cc = ∑ j, (fun j => a' j * w) j • (ψ ∘ B₀ j)`. Rewrite using `[ha']`. Conclude with `Finset.sum_congr rfl fun j _ => smul_smul _ _ _`.

Use `congrFun (hau _ h1) j` as an intermediate fact. Rewrite using `[← this, _root_.mul_assoc, show w * ψ s = 1 from hsU.val_inv_mul, _root_.mul_one]`. Introduce `a τ i`. Establish `hmem : cv (e ⟨τ, i⟩) ∈ eig c (ψ.comp φ₀) hxU τ`. Establish `h1` using `(hPU (e.symm (e ⟨τ, i⟩)).1 (ψ ∘ B₀ (e ⟨τ, i⟩))).1`.

Rewrite `h1` using `[hPψ]`. Simplify using `only [Equiv.symm_apply_apply] at h1`. Conclude with `Submodule.smul_mem _ w h1`. Establish `he` using `(vec_eig_iff hxU _ _).2 hmem a`. Rewrite `he` using `[← vec_smul hxU]`.

Rewrite using `[he, comb_iff hxU, Fintype.sum_eq_single (e ⟨τ, i⟩) (fun k hk => by rw [Pi.single_eq_of_ne hk, zero_smul]), Pi.single_eq_same]`. Introduce `τ i`. Establish `hBj : Bf (e ⟨τ, i⟩) = B τ i` using `by show B (e.symm (e ⟨τ, i⟩)).1 (e.symm (e ⟨τ, i⟩)).2 = B τ i`. Rewrite using `[Equiv.symm_apply_apply]`. Establish `eL : spMap (epsMul (lam s)) ≫ f.v τ i = spMap (dualMap lam) ≫ vec TF.Y.t x₀ xc (B₀ (e ⟨τ, i⟩))`.

Rewrite using `[hB, ← vec_smul hxL, ← hvL]`. Use `congr 1`. Use function extensionality and compare the values at `k`. Use `hB₀ (e ⟨τ, i⟩) k` as an intermediate fact. Rewrite `this` using `[hBj]`.

Conclude with `this.symm`. Establish `eU : spMap (epsMul (ψ s)) ≫ vec TF.Y.t (LogKS.chart U) xU (cv (e ⟨τ, i⟩)) = spMap (dualMap ψ) ≫ vec TF.Y.t x₀ xc (B₀ (e ⟨τ, i⟩))`. Rewrite using `[← vec_smul hxU, ← hvU]`. Use `congr 1`. Simplify using `only [cv, w, smul_smul, IsUnit.mul_val_inv, one_smul]`.

Establish `hθ : θ (lam s) = ρ (ψ s)` using `by show (θ.comp lam) s = (ρ.comp ψ) s`. Rewrite using `[hρψ]`. Establish `L1 : spMap (epsMul (θ (lam s))) ≫ spMap (dualMap θ) ≫ f.v τ i = spMap (dualMap (θ.comp lam)) ≫ vec TF.Y.t x₀ xc (B₀ (e ⟨τ, i⟩))`. Rewrite using `[← Category.assoc, SpreadFrame.eps_dual, Category.assoc, eL, ← Category.assoc, SpreadFrame.dual_dual]`. Use `SpreadFrame.cancel_eps (hls.map θ) (L1.trans ?_)` and prove the remaining obligations.

Rewrite using `[hθ, ← Category.assoc, SpreadFrame.eps_dual, Category.assoc, eU, ← Category.assoc, SpreadFrame.dual_dual, hρψ]`.
-/
theorem GlobalTheory.LogKSDiv.exists_spread_eigFrame : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (TF : TorFlag Xo c) (Z : Comp Xo c), ∀ [IsIntegral (X₀ TF.Y Z)], ∀ (x : X₀ TF.Y Z) (φ : c.F →+* (X₀ TF.Y Z).presheaf.stalk x) (f : GlobalTheory.ShFam.EigFrame TF.Y φ ((show Sp ((X₀ TF.Y Z).presheaf.stalk x) ⟶ X₀ TF.Y Z from (X₀ TF.Y Z).fromSpecStalk x) ≫ (barComp TF.Y Z).ι)), (show Sp ((X₀ TF.Y Z).presheaf.stalk x) ⟶ X₀ TF.Y Z from (X₀ TF.Y Z).fromSpecStalk x) ≫ s₀ TF.Y Z = spMap φ → ∃ (U : TF.Y.X.affineOpens) (_ : U.1 ≤ barComp TF.Y Z) (_ : (barComp TF.Y Z).ι x ∈ U.1) (ρ : Γ(TF.Y.X, U.1) →+* (X₀ TF.Y Z).functionField) (n : ℕ) (e : (Σ τ : E →+* ℂ, Fin (Dw.mult τ)) ≃ Fin n) (v : Fin n → (Sp (DualNumber Γ(TF.Y.X, U.1)) ⟶ TF.Y.t.G.left)) (φU : c.F →+* Γ(TF.Y.X, U.1)), spMap ρ ≫ LogKS.chart U = GlobalTheory.LogKSDiv.genPt TF Z ≫ (barComp TF.Y Z).ι ∧ (∀ i, IsTanAtG TF.Y.t (LogKS.chart U) (v i)) ∧ (∀ w', IsTanAtG TF.Y.t (LogKS.chart U) w' → ∃! cf : Fin n → Γ(TF.Y.X, U.1), IsCombAtG TF.Y.t (LogKS.chart U) v cf w') ∧ (∀ (a : 𝓞 E) (τ : E →+* ℂ) (i : Fin (Dw.mult τ)), IsCombAtG TF.Y.t (LogKS.chart U) v (Pi.single (e ⟨τ, i⟩) (φU (embK c τ a))) (v (e ⟨τ, i⟩) ≫ (TF.Y.t.act.act a).left)) ∧ (∀ (τ : E →+* ℂ) (i : Fin (Dw.mult τ)), spMap (dualMap (algebraMap ((X₀ TF.Y Z).presheaf.stalk x) (X₀ TF.Y Z).functionField)) ≫ f.v τ i = spMap (dualMap ρ) ≫ v (e ⟨τ, i⟩)) := by
  intro E _ _ _ H Dw l Xo c TF Z _ x φ f hφ
  classical
  let y : TF.Y.X := (barComp TF.Y Z).ι x
  have hyb : y ∈ barComp TF.Y Z := by
    show (barComp TF.Y Z).ι x ∈ _
    have := Scheme.Opens.ι_apply (barComp TF.Y Z) x
    exact this ▸ x.2
  replace hφ : (X₀ TF.Y Z).fromSpecStalk x ≫ (barComp TF.Y Z).ι ≫ TF.Y.s = spMap φ := hφ
  obtain ⟨f, rfl⟩ : ∃ f' : ShFam.EigFrame TF.Y φ ((X₀ TF.Y Z).fromSpecStalk x ≫ (barComp TF.Y Z).ι), f' = f :=
    ⟨f, rfl⟩
  obtain ⟨U₀, hU₀, hy, x₀, hx₀, C, m, xc, hxc⟩ := exists_affine_chart TF.Y.t (𝟙 TF.Y.X) y
  let lam : Γ(TF.Y.X, U₀) →+* (X₀ TF.Y Z).presheaf.stalk x := (TF.Y.X.presheaf.germ U₀ y hy ≫ (barComp TF.Y Z).ι.stalkMap x).hom
  letI : Algebra Γ(TF.Y.X, U₀) ((X₀ TF.Y Z).presheaf.stalk x) := lam.toAlgebra
  letI : Algebra Γ(TF.Y.X, U₀) (TF.Y.X.presheaf.stalk y) :=
    TopCat.Presheaf.algebra_section_stalk TF.Y.X.presheaf ⟨y, hy⟩
  have hloc0 := hU₀.isLocalization_stalk ⟨y, hy⟩
  have hloc : IsLocalization (hU₀.primeIdealOf ⟨y, hy⟩).asIdeal.primeCompl ((X₀ TF.Y Z).presheaf.stalk x) := by
    let e := (asIso ((barComp TF.Y Z).ι.stalkMap x)).commRingCatIsoToRingEquiv
    exact IsLocalization.isLocalization_of_algEquiv (S := TF.Y.X.presheaf.stalk y) _ { e with commutes' := fun r => rfl }
  have hpt : (X₀ TF.Y Z).fromSpecStalk x ≫ (barComp TF.Y Z).ι = spMap lam ≫ x₀ := by
    rw [hx₀, Category.comp_id, ← Scheme.SpecMap_stalkMap_fromSpecStalk]
    rw [show TF.Y.X.fromSpecStalk ((barComp TF.Y Z).ι x) = TF.Y.X.fromSpecStalk y from rfl, ← hU₀.fromSpecStalk_eq_fromSpecStalk hy]
    simp only [lam, spMap, CommRingCat.ofHom_hom, Spec.map_comp, Category.assoc, IsAffineOpen.fromSpecStalk]
  let φ₀ : c.F →+* Γ(TF.Y.X, U₀) := (Spec.preimage (x₀ ≫ TF.Y.s)).hom
  have hφ₀ : spMap φ₀ = x₀ ≫ TF.Y.s := Spec.map_preimage _
  have hφl : φ = lam.comp φ₀ := spMap_inj (by
    rw [← hφ, ← ReciprocityTheory.ChartRestriction.G.PullbackSections.spMap_comp_spMap, hφ₀, ← Category.assoc, hpt, Category.assoc])
  subst hφl
  obtain ⟨xL, hxL, hvL⟩ := vec_bc_of_chart C hxc lam hpt
  choose B hB using fun τ i => vec_exists hxL _ (f.tan τ i)
  obtain ⟨P, hP⟩ := exists_projectors c φ₀ hxc
  have hPL := hP lam hxL hvL
  have hBe : ∀ τ i, B τ i ∈ eig c (lam.comp φ₀) hxL τ := fun τ i =>
    (vec_eig_iff hxL _ _).1 fun a => by rw [← hB]; exact f.eig τ i a
  have hBu : ∀ τ w, w ∈ eig c (lam.comp φ₀) hxL τ → ∃! a : Fin (Dw.mult τ) → (X₀ TF.Y Z).presheaf.stalk x,
      w = ∑ i, a i • B τ i := fun τ w hw => by
    have := f.basis τ _ (vec_tan hxL w) ((vec_eig_iff hxL _ _).2 hw)
    rw [show f.v τ = fun i => vec TF.Y.t _ xL (B τ i) from funext (hB τ)] at this
    simpa only [comb_iff hxL] using this
  have : CharZero c.F := RingHom.charZero c.F.val.toRingHom
  obtain ⟨α, hinj, ⟨fp, hf, hfs⟩, hN⟩ := ReciprocityTheory.ChartRestriction.G.PullbackSections.exists_sepElt (E := E) (F := c.F)
    c.F.val.toRingHom (embK c) (fun τ a => embK_coe c τ a)
  have hbasK : ∀ v : Fin m → (X₀ TF.Y Z).presheaf.stalk x,
      ∃! a : (Σ τ : E →+* ℂ, Fin (Dw.mult τ)) → (X₀ TF.Y Z).presheaf.stalk x, v = ∑ j, a j • B j.1 j.2 := by
    letI : Algebra c.F ((X₀ TF.Y Z).presheaf.stalk x) := (lam.comp φ₀).toAlgebra
    exact
    SpreadFrame.basis_of_split (fun τ => ReciprocityTheory.ChartRestriction.G.PullbackSections.proj (rho hxL) (embK c) α τ)
      (ReciprocityTheory.ChartRestriction.G.PullbackSections.sum_proj _ _ _ hinj) (fun τ => eig c (lam.comp φ₀) hxL τ)
      (fun τ m' => by
        rw [ReciprocityTheory.ChartRestriction.G.Chart.mem_eigLat_iff]
        exact ReciprocityTheory.ChartRestriction.G.PullbackSections.eig_of_alpha (rho hxL) (embK c) α hN τ
          (ReciprocityTheory.ChartRestriction.G.PullbackSections.proj_eig_alpha (rho hxL) (embK c) α hinj fp hf hfs τ m'))
      (fun mm hmm τ => ReciprocityTheory.ChartRestriction.G.PullbackSections.proj_sum_eig (rho hxL) (embK c) α hinj mm
        (fun σ => by have h := hmm σ; rw [ReciprocityTheory.ChartRestriction.G.Chart.mem_eigLat_iff] at h; exact h) τ) B hBe hBu
  let e := Fintype.equivFin (Σ τ : E →+* ℂ, Fin (Dw.mult τ))
  let Bf : Fin (Fintype.card (Σ τ : E →+* ℂ, Fin (Dw.mult τ))) → Fin m → (X₀ TF.Y Z).presheaf.stalk x :=
    fun j => B (e.symm j).1 (e.symm j).2
  have hsum : ∀ a : (Σ τ : E →+* ℂ, Fin (Dw.mult τ)) → (X₀ TF.Y Z).presheaf.stalk x,
      ∑ j, a (e.symm j) • Bf j = ∑ k, a k • B k.1 k.2 := fun a =>
    Fintype.sum_equiv e.symm _ (fun k => a k • B k.1 k.2) (fun j => rfl)
  have hbasF : ∀ v, ∃! a : Fin (Fintype.card (Σ τ : E →+* ℂ, Fin (Dw.mult τ))) → (X₀ TF.Y Z).presheaf.stalk x,
      v = ∑ j, a j • Bf j := by
    intro v
    obtain ⟨a, ha, hau⟩ := hbasK v
    refine ⟨fun j => a (e.symm j), by show v = _; rw [hsum]; exact ha, fun a' ha' => funext fun j => ?_⟩
    replace ha' : v = _ := ha'
    have h1 : v = ∑ k, (fun k => a' (e k)) k • B k.1 k.2 := by
      rw [ha', ← hsum]; simp only [Equiv.apply_symm_apply]
    have := congrFun (hau _ h1) (e.symm j)
    simpa using this
  obtain ⟨g, hg, s, B₀, hB₀, hsp⟩ := SpreadFrame.spread_exact (hU₀.primeIdealOf ⟨y, hy⟩).asIdeal.primeCompl Bf hbasF
    (fun j => P (e.symm j).1) (fun j => (hPL _ _).2 (hBe _ _))
  have hlg : IsUnit (lam g) := IsLocalization.map_units (M := (hU₀.primeIdealOf ⟨y, hy⟩).asIdeal.primeCompl)
    ((X₀ TF.Y Z).presheaf.stalk x) ⟨g, hg⟩
  have hls : IsUnit (lam s) := (hsp _ lam hlg).1
  obtain ⟨g', hg'le, hyg'⟩ := hU₀.exists_basicOpen_le (V := barComp TF.Y Z) ⟨y, hyb⟩ hy
  have hU := hU₀.basicOpen (g' * g)
  let U : TF.Y.X.affineOpens := ⟨TF.Y.X.basicOpen (g' * g), hU⟩
  let ψ : Γ(TF.Y.X, U₀) →+* Γ(TF.Y.X, U.1) :=
    (TF.Y.X.presheaf.map (homOfLE (TF.Y.X.basicOpen_le (g' * g))).op).hom
  have hψg₀ : IsUnit (ψ (g' * g)) := TF.Y.X.toRingedSpace.isUnit_res_basicOpen (g' * g)
  have hψg : IsUnit (ψ g) := isUnit_of_mul_isUnit_right (by rw [← map_mul]; exact hψg₀)
  have hchart : LogKS.chart U = spMap ψ ≫ x₀ := by
    rw [hx₀, Category.comp_id]; exact (hU₀.map_fromSpec hU _).symm
  obtain ⟨xU, hxU, hvU⟩ := vec_bc_of_chart C hxc ψ hchart
  have hPU := hP ψ hxU hvU
  obtain ⟨hsU, hPψ, hbasψ⟩ := hsp _ ψ hψg
  have hyU : y ∈ U.1 := by
    show y ∈ TF.Y.X.basicOpen (g' * g)
    rw [Scheme.basicOpen_mul]
    refine ⟨hyg', (Scheme.mem_basicOpen _ _ _ hy).2 ?_⟩
    exact IsLocalization.map_units (M := (hU₀.primeIdealOf ⟨y, hy⟩).asIdeal.primeCompl)
      (TF.Y.X.presheaf.stalk y) ⟨g, hg⟩
  have hκ : IsUnit (lam (g' * g)) := ((Scheme.mem_basicOpen _ _ _ hy).1 hyU).map ((barComp TF.Y Z).ι.stalkMap x).hom
  let θ : (X₀ TF.Y Z).presheaf.stalk x →+* (X₀ TF.Y Z).functionField := algebraMap _ _
  letI : Algebra Γ(TF.Y.X, U₀) Γ(TF.Y.X, U.1) := ψ.toAlgebra
  haveI : IsLocalization.Away (g' * g) Γ(TF.Y.X, U.1) := hU₀.isLocalization_basicOpen (g' * g)
  let ρ : Γ(TF.Y.X, U.1) →+* (X₀ TF.Y Z).functionField := IsLocalization.Away.lift (g' * g) (g := θ.comp lam) (hκ.map θ)
  have hρψ : ρ.comp ψ = θ.comp lam := IsLocalization.lift_comp _
  let w : Γ(TF.Y.X, U.1) := ↑hsU.unit⁻¹
  let cv : Fin (Fintype.card (Σ τ : E →+* ℂ, Fin (Dw.mult τ))) → Fin m → Γ(TF.Y.X, U.1) := fun j => w • (ψ ∘ B₀ j)
  refine ⟨U, le_trans (show TF.Y.X.basicOpen (g' * g) ≤ _ by rw [Scheme.basicOpen_mul]; exact inf_le_left) hg'le, hyU, ρ, _, e,
    fun j => vec TF.Y.t (LogKS.chart U) xU (cv j), ψ.comp φ₀, ?_, fun j => vec_tan hxU _, ?_, ?_, ?_⟩
  · rw [hchart, ← Category.assoc, ReciprocityTheory.ChartRestriction.G.PullbackSections.spMap_comp_spMap, hρψ, ← ReciprocityTheory.ChartRestriction.G.PullbackSections.spMap_comp_spMap,
      Category.assoc, ← hpt, ← Category.assoc]
    congr 1
    exact Scheme.SpecMap_stalkSpecializes_fromSpecStalk ((genericPoint_spec (X₀ TF.Y Z)).specializes trivial)
  · intro w' hw'
    obtain ⟨cc, rfl⟩ := vec_exists hxU w' hw'
    simp only [comb_iff hxU]
    obtain ⟨a, ha, hau⟩ := hbasψ cc
    refine ⟨fun j => a j * ψ s, ?_, fun a' ha' => funext fun j => ?_⟩
    · show cc = _
      rw [ha]
      refine Finset.sum_congr rfl fun j _ => ?_
      show _ = _ • ((↑hsU.unit⁻¹ : Γ(TF.Y.X, U.1)) • _)
      rw [smul_smul, _root_.mul_assoc, IsUnit.mul_val_inv, _root_.mul_one]
    · replace ha' : cc = _ := ha'
      have h1 : cc = ∑ j, (fun j => a' j * w) j • (ψ ∘ B₀ j) := by
        rw [ha']; exact Finset.sum_congr rfl fun j _ => smul_smul _ _ _
      have := congrFun (hau _ h1) j
      rw [← this, _root_.mul_assoc, show w * ψ s = 1 from hsU.val_inv_mul, _root_.mul_one]
  · intro a τ i
    have hmem : cv (e ⟨τ, i⟩) ∈ eig c (ψ.comp φ₀) hxU τ := by
      have h1 := (hPU (e.symm (e ⟨τ, i⟩)).1 (ψ ∘ B₀ (e ⟨τ, i⟩))).1
      rw [hPψ] at h1
      simp only [Equiv.symm_apply_apply] at h1
      exact Submodule.smul_mem _ w h1
    have he := (vec_eig_iff hxU _ _).2 hmem a
    rw [← vec_smul hxU] at he
    rw [he, comb_iff hxU, Fintype.sum_eq_single (e ⟨τ, i⟩) (fun k hk => by rw [Pi.single_eq_of_ne hk, zero_smul]),
      Pi.single_eq_same]
  · intro τ i
    have hBj : Bf (e ⟨τ, i⟩) = B τ i := by
      show B (e.symm (e ⟨τ, i⟩)).1 (e.symm (e ⟨τ, i⟩)).2 = B τ i
      rw [Equiv.symm_apply_apply]
    have eL : spMap (epsMul (lam s)) ≫ f.v τ i =
        spMap (dualMap lam) ≫ vec TF.Y.t x₀ xc (B₀ (e ⟨τ, i⟩)) := by
      rw [hB, ← vec_smul hxL, ← hvL]
      congr 1
      funext k
      have := hB₀ (e ⟨τ, i⟩) k
      rw [hBj] at this
      exact this.symm
    have eU : spMap (epsMul (ψ s)) ≫ vec TF.Y.t (LogKS.chart U) xU (cv (e ⟨τ, i⟩)) =
        spMap (dualMap ψ) ≫ vec TF.Y.t x₀ xc (B₀ (e ⟨τ, i⟩)) := by
      rw [← vec_smul hxU, ← hvU]
      congr 1
      simp only [cv, w, smul_smul, IsUnit.mul_val_inv, one_smul]
    have hθ : θ (lam s) = ρ (ψ s) := by
      show (θ.comp lam) s = (ρ.comp ψ) s
      rw [hρψ]
    have L1 : spMap (epsMul (θ (lam s))) ≫ spMap (dualMap θ) ≫ f.v τ i =
        spMap (dualMap (θ.comp lam)) ≫ vec TF.Y.t x₀ xc (B₀ (e ⟨τ, i⟩)) := by
      rw [← Category.assoc, SpreadFrame.eps_dual, Category.assoc, eL, ← Category.assoc, SpreadFrame.dual_dual]
    refine SpreadFrame.cancel_eps (hls.map θ) (L1.trans ?_)
    rw [hθ, ← Category.assoc, SpreadFrame.eps_dual, Category.assoc, eU, ← Category.assoc, SpreadFrame.dual_dual, hρψ]

end Spread

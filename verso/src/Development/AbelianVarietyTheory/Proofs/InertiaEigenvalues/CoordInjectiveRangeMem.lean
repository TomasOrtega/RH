import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.MapCSmulMulVec
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.OneAddXMulDerivativeBin
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CoordApply
open PowerSeries Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.NB GlobalTheory.CycFr GlobalTheory.WachTie

noncomputable section

namespace GlobalTheory.WachTie

/- English proof (translation)
Introduce `G _ _ Qp K₀ K _ _ _ _ _ _ _ B BdR _ _ _ _ _ _ _ _ _ _ _ PD LL O _ _ _ _ _ v n W l R j jE T r b hF hE hb hc`. Take `⟨-, hFr, -⟩` from `hF`. Take `⟨hext, hinj, hEr, -⟩` from `hE`. Set `c : Module.Basis (Fin r) W.EE (W.DD T)` to `(W.N_base T hc).basis b`. Establish `hcb : ∀ k, c k = (b k : W.DD T)` using `fun k => IsBaseChange.basis_apply b (W.N_base T hc) k`.

Establish `huniq : ∀ y y' : Fin r → W.EE, ∑ k, y k • (b k : W.DD T) = ∑ k, y' k • (b k : W.DD T) → y = y'`. Introduce `y y' h`. Apply `c.equivFun.symm.injective` to reduce the goal to its premises. Simplify using `only [Module.Basis.equivFun_symm_apply, hcb]`. Conclude with `h`.

Establish `hex : ∀ m : W.DD T, ∃ y : Fin r → W.EE, ∑ k, y k • (b k : W.DD T) = m`. Introduce `m`. Use `⟨c.repr m, ?_⟩` and prove the remaining obligations. Simplify using `only [← hcb]`. Conclude with `c.sum_repr m`.

Establish `hγ : ∀ δ ∈ W.DelF, ∀ y : Fin r → W.EE, W.γD T δ (∑ k, y k • (b k : W.DD T)) = ∑ k, W.γE δ (y k) • (b k : W.DD T)`. Introduce `δ hδ y`. Rewrite using `[map_sum]`. Use `Finset.sum_congr rfl fun k _ => ?_` and prove the remaining obligations. Rewrite using `[W.γD_smul, (hb k).2 δ hδ]`.

Establish `hinv : ∀ x, ∀ δ ∈ W.DelF, W.γD T δ (coord W R jE T (fun k => (b k : W.DD T)) x) = coord W R jE T (fun k => (b k : W.DD T)) x`. Introduce `x δ hδ`. Rewrite using `[coord_apply, hγ δ hδ]`. Use `Finset.sum_congr rfl fun k _ => ?_` and prove the remaining obligations. Rewrite using `[(hEr _).1 ⟨_, rfl⟩ δ hδ]`.

Use `⟨?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `x x' h`. Use `huniq _ _ h` as an intermediate fact. Use function extensionality and compare the values at `i k`. Conclude with `congrFun (hinj (congrFun this k)) i`.

Apply `le_antisymm` to reduce the goal to its premises. Introduce and unpack `_ ⟨x, rfl⟩`. Conclude with `hinv x`. Introduce `m hm`. Take `⟨y, rfl⟩` from `hex m`.

Establish `hy : ∀ k, ∃ x, jE x = y k` using `fun k => (hEr _).2 fun δ hδ => congrFun (huniq _ _ ((hγ δ hδ y).symm.trans (hm δ hδ))) k`. Use `choose x hx using hy`. Use `⟨fun i k => x k i, ?_⟩` and prove the remaining obligations. Rewrite using `[coord_apply]`. Use `Finset.sum_congr rfl fun k _ => ?_` and prove the remaining obligations.

Rewrite using `[← hx k]`. Introduce `x`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨hN, -⟩ set a := b.repr ⟨_, hN⟩ with ha`. Establish `h1 : ∑ k, algebraMap (LetA O n) W.EE (a k) • (b k : W.DD T) = ∑ k, jE (fun i => x i k) • (b k : W.DD T)`.

Use `congrArg (W.N T).subtype (b.sum_repr ⟨_, hN⟩)` as an intermediate fact. Rewrite `this` using `[map_sum]`. Simplify using `only [algebraMap_smul]`. Conclude with `this`. Establish `h2` using `huniq _ _ h1`.

Introduce `i k _`. Establish `h3 : algebraMap (LetA O n) W.EE (a k) = jE (fun i => x i k)` using `congrFun h2 k`. Establish `h4 : ∀ i', ∃ a', j a' = a k i'` using `fun i' => (hFr _).2 fun δ hδ => by`. Establish `h5` using `(hEr _).1 ⟨_, h3.symm⟩ δ hδ`. Rewrite `h5` using `[W.γE_ext]`.

Conclude with `congrFun (W.EE_inj h5) i'`. Use `choose a' ha' using h4`. Establish `h6 : jE (fun i => R.ι (a' i)) = jE (fun i => x i k)`. Rewrite using `[hext, ← h3]`. Use `congr 1`.

Use function extensionality and compare the values at `i'`. Conclude with `ha' i'`. Conclude with `⟨a' i, congrFun (hinj h6) i⟩`. Introduce `hx`. Use `⟨?_, hinv x⟩` and prove the remaining obligations.

Rewrite using `[coord_apply]`. Use `Submodule.sum_mem _ fun k _ => ?_` and prove the remaining obligations. Establish `h4 : ∀ i, ∃ a', R.ι a' = x i k` using `fun i => hx i k (Set.mem_univ _)`. Use `choose a' ha' using h4`. Establish `: (fun i => x i k) = fun i => R.ι (a' i)` using `funext fun i => (ha' i).symm`.

Rewrite using `[this, hext, algebraMap_smul]`. Conclude with `(W.N T).smul_mem _ (b k).2`.
-/
theorem coord_injective_range_mem : ∀ {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K] [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K] {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B] [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR] [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR] {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL] [CommRing O] [Algebra O LL] [TopologicalSpace LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ} (W : LocWach PD LL O v n) {l : ℕ} (R : Fr l O) (j : O⟦X⟧ →ₐ[O] O⟦X⟧) (jE : (ZMod n → R.EE) →ₐ[O] W.EE) (T : LocLat G Qp LL O) {r : ℕ} (b : Module.Basis (Fin r) (LetA O n) ↥(W.N T)), FrTie W R j → EETie W R j jE → (∀ k, (b k : W.DD T) ∈ W.NΔ T) → IsCrys PD T.ρ → Function.Injective (coord W R jE T (fun k => (b k : W.DD T))) ∧ LinearMap.range (coord W R jE T (fun k => (b k : W.DD T))) = DDinv W T ∧ ∀ x, coord W R jE T (fun k => (b k : W.DD T)) x ∈ W.NΔ T ↔ ∀ i, x i ∈ R.N0 r := by
  intro G _ _ Qp K₀ K _ _ _ _ _ _ _ B BdR _ _ _ _ _ _ _ _ _ _ _ PD LL O _ _ _ _ _ v n W l R j jE T r b
    hF hE hb hc
  obtain ⟨-, hFr, -⟩ := hF
  obtain ⟨hext, hinj, hEr, -⟩ := hE
  let c : Module.Basis (Fin r) W.EE (W.DD T) := (W.N_base T hc).basis b
  have hcb : ∀ k, c k = (b k : W.DD T) := fun k => IsBaseChange.basis_apply b (W.N_base T hc) k
  have huniq : ∀ y y' : Fin r → W.EE,
      ∑ k, y k • (b k : W.DD T) = ∑ k, y' k • (b k : W.DD T) → y = y' := by
    intro y y' h
    apply c.equivFun.symm.injective
    simp only [Module.Basis.equivFun_symm_apply, hcb]
    exact h
  have hex : ∀ m : W.DD T, ∃ y : Fin r → W.EE, ∑ k, y k • (b k : W.DD T) = m := by
    intro m
    refine ⟨c.repr m, ?_⟩
    simp only [← hcb]
    exact c.sum_repr m
  have hγ : ∀ δ ∈ W.DelF, ∀ y : Fin r → W.EE, W.γD T δ (∑ k, y k • (b k : W.DD T)) =
      ∑ k, W.γE δ (y k) • (b k : W.DD T) := by
    intro δ hδ y
    rw [map_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [W.γD_smul, (hb k).2 δ hδ]
  have hinv : ∀ x, ∀ δ ∈ W.DelF, W.γD T δ (coord W R jE T (fun k => (b k : W.DD T)) x) =
      coord W R jE T (fun k => (b k : W.DD T)) x := by
    intro x δ hδ
    rw [coord_apply, hγ δ hδ]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [(hEr _).1 ⟨_, rfl⟩ δ hδ]
  refine ⟨?_, ?_, ?_⟩
  · intro x x' h
    have := huniq _ _ h
    funext i k
    exact congrFun (hinj (congrFun this k)) i
  · apply le_antisymm
    · rintro _ ⟨x, rfl⟩
      exact hinv x
    · intro m hm
      obtain ⟨y, rfl⟩ := hex m
      have hy : ∀ k, ∃ x, jE x = y k := fun k => (hEr _).2 fun δ hδ =>
        congrFun (huniq _ _ ((hγ δ hδ y).symm.trans (hm δ hδ))) k
      choose x hx using hy
      refine ⟨fun i k => x k i, ?_⟩
      rw [coord_apply]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [← hx k]
  · intro x
    constructor
    · rintro ⟨hN, -⟩
      set a := b.repr ⟨_, hN⟩ with ha
      have h1 : ∑ k, algebraMap (LetA O n) W.EE (a k) • (b k : W.DD T) =
          ∑ k, jE (fun i => x i k) • (b k : W.DD T) := by
        have := congrArg (W.N T).subtype (b.sum_repr ⟨_, hN⟩)
        rw [map_sum] at this
        simp only [algebraMap_smul]
        exact this
      have h2 := huniq _ _ h1
      intro i k _
      have h3 : algebraMap (LetA O n) W.EE (a k) = jE (fun i => x i k) := congrFun h2 k
      have h4 : ∀ i', ∃ a', j a' = a k i' := fun i' => (hFr _).2 fun δ hδ => by
        have h5 := (hEr _).1 ⟨_, h3.symm⟩ δ hδ
        rw [W.γE_ext] at h5
        exact congrFun (W.EE_inj h5) i'
      choose a' ha' using h4
      have h6 : jE (fun i => R.ι (a' i)) = jE (fun i => x i k) := by
        rw [hext, ← h3]
        congr 1
        funext i'
        exact ha' i'
      exact ⟨a' i, congrFun (hinj h6) i⟩
    · intro hx
      refine ⟨?_, hinv x⟩
      rw [coord_apply]
      refine Submodule.sum_mem _ fun k _ => ?_
      have h4 : ∀ i, ∃ a', R.ι a' = x i k := fun i => hx i k (Set.mem_univ _)
      choose a' ha' using h4
      have : (fun i => x i k) = fun i => R.ι (a' i) := funext fun i => (ha' i).symm
      rw [this, hext, algebraMap_smul]
      exact (W.N T).smul_mem _ (b k).2

end GlobalTheory.WachTie

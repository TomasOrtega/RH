import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SubPairRight
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsHomLocBijectiveGrSum
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsFinsetSum
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SmulEqZeroOfMem
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsHomogeneousFamilySaturating
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.CubeComplexGradedModuleExactAtOfLargeDegree
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsGradedMapGlueD
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.AbLaw PositivityTheory.FormalThickening
open GlobalTheory.ProjSpace GlobalTheory.QCoh.Qcqs GlobalTheory.Cartier GlobalTheory.CompanionTheory.FormalAlg GlobalTheory.CompanionTheory.FormalAlg.Lift
open GlobalTheory.CompanionTheory.FormalAlg.Lift.Glue

namespace GlobalTheory.CompanionTheory.FormalAlg.Lift.Glue

/- English proof (translation)
Introduce `ι _ _ A _ P _ _ res hid hcomp hker hext i f`. Establish `inj : ∀ (S S' : Finset ι) (h : S ⊆ S'), S = S' → Function.Injective (res S S' h)`. Introduce and unpack `S _ h rfl a b hab`. Rewrite `hab` using `[hid, hid]`. Then use the resulting hypothesis. Use `set x : MvPolynomial ι A := MvPolynomial.X i with hx`.

Establish `h1 : ∀ j : ι, ∃ (k : ℕ) (g : P {j}), res {j} {i, j} (sub_pair_right i j) g = x ^ k • res {i} {i, j} (sub_pair_left i j) f`. Introduce `j`. Take `⟨k, g, hg⟩` from `hext {j} i (res {i} {i, j} (sub_pair_left i j) f) (Finset.singleton_nonempty j)`. Conclude with `⟨k, g, hg⟩`. Use `choose k g hg using h1`.

Use `set K : ℕ := Finset.univ.sup k with hK`. Establish `hkK : ∀ j, k j ≤ K` using `fun j => Finset.le_sup (Finset.mem_univ j)`. Choose the witnesses or unpack the hypotheses as in `⟨f', hres⟩ : ∃ f' : ∀ j : ι, P {j}, ∀ j, res {j} {i, j} (sub_pair_right i j) (f' j) = x ^ K • res {i} {i, j} (sub_pair_left i j) f := by`. Use `⟨fun j => x ^ (K - k j) • g j, fun j => ?_⟩` and prove the remaining obligations. Simplify using `only [map_smul, hg, smul_smul, ← pow_add, Nat.sub_add_cancel (hkK j)]`.

Establish `htriple : ∀ (j : ι) (T : Finset ι) (hT : ({i, j} : Finset ι) ⊆ T), res {j} T ((sub_pair_right i j).trans hT) (f' j) = x ^ K • res {i} T ((sub_pair_left i j).trans hT) f`. Introduce `j T hT`. Rewrite using `[← hcomp _ _ _ (sub_pair_right i j) hT, hres, map_smul, hcomp]`. Establish `h2 : ∀ j l : ι, ∃ n : ℕ, x ^ n • (res {j} {j, l} (sub_pair_left j l) (f' j) - res {l} {j, l} (sub_pair_right j l) (f' l)) = 0`. Introduce `j l`.

Use `hker {j, l} i _ (Finset.insert_nonempty _ _) ?_` and prove the remaining obligations. Establish `hj : ({i, j} : Finset ι) ⊆ insert i {j, l}` using `Finset.insert_subset_insert i (sub_pair_left j l)`. Establish `hl : ({i, l} : Finset ι) ⊆ insert i {j, l}` using `Finset.insert_subset_insert i (sub_pair_right j l)`. Rewrite using `[map_sub, hcomp, hcomp, sub_eq_zero]`. Establish `e1` using `htriple j _ hj`.

Establish `e2` using `htriple l _ hl`. Conclude with `e1.trans e2.symm`. Use `choose n hn using h2`. Use `set N' : ℕ := Finset.univ.sup (fun p : ι × ι => n p.1 p.2) with hN'`. Establish `hnN : ∀ j l, n j l ≤ N'` using `fun j l => Finset.le_sup (f := fun p : ι × ι => n p.1 p.2) (Finset.mem_univ (j, l))`.

Use `⟨fun j => x ^ N' • f' j, N' + K, ?_, ?_⟩` and prove the remaining obligations. Introduce `j l`. Establish `h0 : x ^ N' • (res {j} {j, l} (sub_pair_left j l) (f' j) - res {l} {j, l} (sub_pair_right j l) (f' l)) = 0`. Rewrite using `[← Nat.sub_add_cancel (hnN j l), pow_add, mul_smul, hn, smul_zero]`. Use `show res {j} {j, l} (sub_pair_left j l) (x ^ N' • f' j) = res {l} {j, l} (sub_pair_right j l) (x ^ N' • f' l)`.

Rewrite using `[map_smul, map_smul, ← sub_eq_zero, ← smul_sub]`. Conclude with `h0`. Establish `hii : ({i} : Finset ι) ⊆ {i, i}` using `sub_pair_left i i`. Establish `hfi : f' i = x ^ K • f`. Apply `inj {i} {i, i} hii (Finset.pair_eq_singleton i).symm` to reduce the goal to its premises.

Rewrite using `[map_smul]`. Conclude with `hres i`. Use `show x ^ N' • f' i = x ^ (N' + K) • f`. Rewrite using `[hfi, smul_smul, ← pow_add]`.
-/
theorem exists_compatible_family_of_singleton : ∀ (ι : Type) [LinearOrder ι] [Fintype ι] (A : Type) [CommRing A] (P : Finset ι → Type) [∀ S, AddCommGroup (P S)] [∀ S, Module (MvPolynomial ι A) (P S)] (res : ∀ S S' : Finset ι, S ⊆ S' → P S →ₗ[MvPolynomial ι A] P S'), (∀ S (h : S ⊆ S) a, res S S h a = a) → (∀ S S' S'' (h : S ⊆ S') (h' : S' ⊆ S'') a, res S' S'' h' (res S S' h a) = res S S'' (h.trans h') a) → (∀ (S : Finset ι) (j : ι) (a : P S), S.Nonempty → res S (insert j S) (Finset.subset_insert j S) a = 0 → ∃ k : ℕ, (MvPolynomial.X j : MvPolynomial ι A) ^ k • a = 0) → (∀ (S : Finset ι) (j : ι) (b : P (insert j S)), S.Nonempty → ∃ k : ℕ, (MvPolynomial.X j : MvPolynomial ι A) ^ k • b ∈ LinearMap.range (res S (insert j S) (Finset.subset_insert j S))) → (∀ (i : ι) (f : P {i}), ∃ (c : ∀ j : ι, P {j}) (N : ℕ), (∀ j l, res {j} {j, l} (sub_pair_left j l) (c j) = res {l} {j, l} (sub_pair_right j l) (c l)) ∧ c i = (MvPolynomial.X i : MvPolynomial ι A) ^ N • f) := by
  intro ι _ _ A _ P _ _ res hid hcomp hker hext i f
  have inj : ∀ (S S' : Finset ι) (h : S ⊆ S'), S = S' → Function.Injective (res S S' h) := by
    rintro S _ h rfl a b hab
    rwa [hid, hid] at hab
  set x : MvPolynomial ι A := MvPolynomial.X i with hx

  have h1 : ∀ j : ι, ∃ (k : ℕ) (g : P {j}),
      res {j} {i, j} (sub_pair_right i j) g = x ^ k • res {i} {i, j} (sub_pair_left i j) f := by
    intro j
    obtain ⟨k, g, hg⟩ := hext {j} i (res {i} {i, j} (sub_pair_left i j) f)
      (Finset.singleton_nonempty j)
    exact ⟨k, g, hg⟩
  choose k g hg using h1
  set K : ℕ := Finset.univ.sup k with hK
  have hkK : ∀ j, k j ≤ K := fun j => Finset.le_sup (Finset.mem_univ j)
  obtain ⟨f', hres⟩ : ∃ f' : ∀ j : ι, P {j}, ∀ j, res {j} {i, j} (sub_pair_right i j) (f' j)
      = x ^ K • res {i} {i, j} (sub_pair_left i j) f := by
    refine ⟨fun j => x ^ (K - k j) • g j, fun j => ?_⟩
    simp only [map_smul, hg, smul_smul, ← pow_add, Nat.sub_add_cancel (hkK j)]

  have htriple : ∀ (j : ι) (T : Finset ι) (hT : ({i, j} : Finset ι) ⊆ T),
      res {j} T ((sub_pair_right i j).trans hT) (f' j)
        = x ^ K • res {i} T ((sub_pair_left i j).trans hT) f := by
    intro j T hT
    rw [← hcomp _ _ _ (sub_pair_right i j) hT, hres, map_smul, hcomp]
  have h2 : ∀ j l : ι, ∃ n : ℕ, x ^ n • (res {j} {j, l} (sub_pair_left j l) (f' j)
      - res {l} {j, l} (sub_pair_right j l) (f' l)) = 0 := by
    intro j l
    refine hker {j, l} i _ (Finset.insert_nonempty _ _) ?_
    have hj : ({i, j} : Finset ι) ⊆ insert i {j, l} :=
      Finset.insert_subset_insert i (sub_pair_left j l)
    have hl : ({i, l} : Finset ι) ⊆ insert i {j, l} :=
      Finset.insert_subset_insert i (sub_pair_right j l)
    rw [map_sub, hcomp, hcomp, sub_eq_zero]
    have e1 := htriple j _ hj
    have e2 := htriple l _ hl
    exact e1.trans e2.symm
  choose n hn using h2
  set N' : ℕ := Finset.univ.sup (fun p : ι × ι => n p.1 p.2) with hN'
  have hnN : ∀ j l, n j l ≤ N' := fun j l =>
    Finset.le_sup (f := fun p : ι × ι => n p.1 p.2) (Finset.mem_univ (j, l))
  refine ⟨fun j => x ^ N' • f' j, N' + K, ?_, ?_⟩
  · intro j l
    have h0 : x ^ N' • (res {j} {j, l} (sub_pair_left j l) (f' j)
        - res {l} {j, l} (sub_pair_right j l) (f' l)) = 0 := by
      rw [← Nat.sub_add_cancel (hnN j l), pow_add, mul_smul, hn, smul_zero]
    show res {j} {j, l} (sub_pair_left j l) (x ^ N' • f' j)
      = res {l} {j, l} (sub_pair_right j l) (x ^ N' • f' l)
    rw [map_smul, map_smul, ← sub_eq_zero, ← smul_sub]
    exact h0
  · have hii : ({i} : Finset ι) ⊆ {i, i} := sub_pair_left i i
    have hfi : f' i = x ^ K • f := by
      apply inj {i} {i, i} hii (Finset.pair_eq_singleton i).symm
      rw [map_smul]
      exact hres i
    show x ^ N' • f' i = x ^ (N' + K) • f
    rw [hfi, smul_smul, ← pow_add]

end GlobalTheory.CompanionTheory.FormalAlg.Lift.Glue

import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsTheta
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR
namespace GlobalTheory.Poinc.AdicTerm

/- English proof (translation)
Establish `hw : w ∈ N` using `Submodule.smul_le_right (h 0)`. Use `haveI : Module.Finite V N := Module.Finite.iff_fg.mpr hN`. Establish `hb` using `Ideal.iInf_pow_smul_eq_bot_of_isLocalRing (M := N) (maximalIdeal V) (maximalIdeal.isMaximal V).ne_top`. Establish `hm : (⟨w, hw⟩ : N) ∈ (⨅ n : ℕ, maximalIdeal V ^ n • ⊤ : Submodule V N)`. Rewrite using `[Submodule.mem_iInf]`.

Introduce `n`. Conclude with `(Submodule.mem_smul_top_iff _ N _).mpr (h n)`. Rewrite `hm` using `[hb, Submodule.mem_bot]`. Conclude with `congrArg Subtype.val hm`.
-/
theorem eq_zero_of_mem_pow_smul {V E : Type} [CommRing V] [IsLocalRing V] [IsNoetherianRing V]
    [AddCommGroup E] [Module V E] (N : Submodule V E) (hN : N.FG) (w : E)
    (h : ∀ n : ℕ, w ∈ maximalIdeal V ^ n • N) : w = 0 := by
  have hw : w ∈ N := Submodule.smul_le_right (h 0)
  haveI : Module.Finite V N := Module.Finite.iff_fg.mpr hN
  have hb := Ideal.iInf_pow_smul_eq_bot_of_isLocalRing (M := N) (maximalIdeal V)
    (maximalIdeal.isMaximal V).ne_top
  have hm : (⟨w, hw⟩ : N) ∈ (⨅ n : ℕ, maximalIdeal V ^ n • ⊤ : Submodule V N) := by
    rw [Submodule.mem_iInf]
    intro n
    exact (Submodule.mem_smul_top_iff _ N _).mpr (h n)
  rw [hb, Submodule.mem_bot] at hm
  exact congrArg Subtype.val hm

/- English proof (translation)
Take `⟨N, hN, -, -, hS⟩` from `hs`. Set `P : Submodule V E` to `Submodule.map (LinearMap.toSpanSingleton V E k) (maximalIdeal V)`. Establish `key : P.mkQ (v - y i₀ • k) = 0`. Use `eq_zero_of_mem_pow_smul (N.map P.mkQ) (hN.map _) _ fun n => ?_` and prove the remaining obligations. Take `⟨S, hS⟩` from `hS n`.

Establish `h1` using `hS (insert i₀ S) (Finset.subset_insert _ _)`. Establish `h2 : P.mkQ (v - ∑ i ∈ insert i₀ S, x i) ∈ maximalIdeal V ^ n • N.map P.mkQ`. Rewrite using `[← Submodule.map_smul'']`. Conclude with `Submodule.mem_map_of_mem h1`. Establish `h3 : ∑ i ∈ (insert i₀ S).erase i₀, x i ∈ P`.

Use `Submodule.sum_mem _ fun i hi => ?_` and prove the remaining obligations. Conclude with `⟨y i, hy i (Finset.ne_of_mem_erase hi), by simp [hx i]⟩`. Establish `h4 : P.mkQ (∑ i ∈ (insert i₀ S).erase i₀, x i) = 0` using `(Submodule.Quotient.mk_eq_zero P).mpr h3`. Establish `h5 : v - y i₀ • k = (v - ∑ i ∈ insert i₀ S, x i) + ∑ i ∈ (insert i₀ S).erase i₀, x i`. Rewrite using `[← Finset.add_sum_erase _ x (Finset.mem_insert_self i₀ S), hx i₀]`.

Normalize the expressions using the abelian group laws. Rewrite using `[h5, map_add, h4, add_zero]`. Conclude with `h2`. Take `⟨a, ha, hak⟩` from `(Submodule.Quotient.mk_eq_zero P).mp key`. Use `⟨y i₀ + a, ?_, by simpa using ha⟩` and prove the remaining obligations.

Establish `hak' : a • k = v - y i₀ • k` using `by simpa using hak`. Rewrite using `[add_smul, hak']`. Normalize the expressions using the abelian group laws.
-/
theorem sumI_smul {V E : Type} [CommRing V] [IsLocalRing V] [IsNoetherianRing V]
    [AddCommGroup E] [Module V E] {Ix : Type} (i₀ : Ix) (x : Ix → E) (y : Ix → V) (k v : E)
    (hx : ∀ i, x i = y i • k) (hy : ∀ i, i ≠ i₀ → y i ∈ maximalIdeal V)
    (hs : SumI (maximalIdeal V) x v) :
    ∃ S : V, v = S • k ∧ S - y i₀ ∈ maximalIdeal V := by
  classical
  obtain ⟨N, hN, -, -, hS⟩ := hs
  let P : Submodule V E := Submodule.map (LinearMap.toSpanSingleton V E k) (maximalIdeal V)
  have key : P.mkQ (v - y i₀ • k) = 0 := by
    refine eq_zero_of_mem_pow_smul (N.map P.mkQ) (hN.map _) _ fun n => ?_
    obtain ⟨S, hS⟩ := hS n
    have h1 := hS (insert i₀ S) (Finset.subset_insert _ _)
    have h2 : P.mkQ (v - ∑ i ∈ insert i₀ S, x i) ∈ maximalIdeal V ^ n • N.map P.mkQ := by
      rw [← Submodule.map_smul'']
      exact Submodule.mem_map_of_mem h1
    have h3 : ∑ i ∈ (insert i₀ S).erase i₀, x i ∈ P := by
      refine Submodule.sum_mem _ fun i hi => ?_
      exact ⟨y i, hy i (Finset.ne_of_mem_erase hi), by simp [hx i]⟩
    have h4 : P.mkQ (∑ i ∈ (insert i₀ S).erase i₀, x i) = 0 :=
      (Submodule.Quotient.mk_eq_zero P).mpr h3
    have h5 : v - y i₀ • k =
        (v - ∑ i ∈ insert i₀ S, x i) + ∑ i ∈ (insert i₀ S).erase i₀, x i := by
      rw [← Finset.add_sum_erase _ x (Finset.mem_insert_self i₀ S), hx i₀]
      abel
    rw [h5, map_add, h4, add_zero]
    exact h2
  obtain ⟨a, ha, hak⟩ := (Submodule.Quotient.mk_eq_zero P).mp key
  refine ⟨y i₀ + a, ?_, by simpa using ha⟩
  have hak' : a • k = v - y i₀ • k := by simpa using hak
  rw [add_smul, hak']
  abel

/- English proof (translation)
Introduce `V _ _ _ _ Ix i₀ x y κ v hx hy hs`. Establish `h` using `@sumI_smul V (FractionRing V) _ _ _ _ (Module.compHom (FractionRing V) (algebraMap V (FractionRing V))) Ix i₀ x y κ v (fun i => (hx i).trans (mul_comm _ _)) hy hs`. Take `⟨S, h1, h2⟩` from `h`. Conclude with `⟨S, h1.trans (mul_comm _ _), h2⟩`.
-/
theorem sumF_mul : ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] [IsNoetherianRing V] (Ix : Type) (i₀ : Ix) (x : Ix → FractionRing V) (y : Ix → V) (κ v : FractionRing V), (∀ i, x i = κ * algebraMap V (FractionRing V) (y i)) → (∀ i, i ≠ i₀ → y i ∈ maximalIdeal V) → SumF (maximalIdeal V) (FractionRing V) x v → ∃ S : V, v = κ * algebraMap V (FractionRing V) S ∧ S - y i₀ ∈ maximalIdeal V := by
  intro V _ _ _ _ Ix i₀ x y κ v hx hy hs
  have h := @sumI_smul V (FractionRing V) _ _ _ _
    (Module.compHom (FractionRing V) (algebraMap V (FractionRing V))) Ix i₀ x y κ v
    (fun i => (hx i).trans (mul_comm _ _)) hy hs
  obtain ⟨S, h1, h2⟩ := h
  exact ⟨S, h1.trans (mul_comm _ _), h2⟩

end GlobalTheory.Poinc.AdicTerm

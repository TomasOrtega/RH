import Formalism.LocalToGlobal.CharacterGerms.RowTiePAllSet
import Formalism.LocalToGlobal.CharacterGerms.RowTiePLimTy

noncomputable section

open scoped BigOperators
open Classical

namespace Formalism.L2.FormalSeriesBounds

open Formalism.IncomingBounds ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ RowTiePE0

variable {C : Type} [Field C]

namespace RawChart

variable {d : ℕ} {I : Fin 2 → Type} [∀ g, Fintype (I g)] {κ : Type} [Fintype κ] (X : RawChart C d I κ)

/- English proof (translation)
Introduce `hx hy`. Take `⟨γ, lam, hγ, hlam, h1, h2⟩` from `hx`. Take `⟨γ', lam', hγ', hlam', h1', h2'⟩` from `hy`. Take `⟨γ'', hγ'', hL, hS⟩` from `hA γ γ' hγ hγ'`. Establish `hty : ∀ n, PowerSeries.mk (fun m => (L + L') m n) = PowerSeries.mk (fun m => L m n) + PowerSeries.mk (fun m => L' m n)` using `fun n => by`.

Use extensionality with `m`. Simplify using `[PowerSeries.coeff_mk]`. Use `⟨γ'', fun q => lam q + lam' q + (alongCv γ'' (X.sg (X.u (1 - g) q)) - alongCv γ (X.sg (X.u (1 - g) q)) - alongCv γ' (X.sg (X.u (1 - g) q))), hγ'', ?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `q`. Take `⟨c0, cI⟩` from `hS (X.u (1 - g) q) (hu (1 - g) q)`.

Use `⟨?_, fun n => ?_⟩` and prove the remaining obligations. Rewrite using `[map_add, map_add, (hlam q).1, (hlam' q).1, c0]`. Simplify using the standard rewrite rules. Rewrite using `[map_add, map_add]`. Conclude with `(((hlam q).2 n).add ((hlam' q).2 n)).add (cI n)`.

Introduce `i`. Rewrite using `[hL i, h1 i, h1' i, ← Finset.sum_add_distrib]`. Use `Finset.sum_congr rfl fun c _ => ?_` and prove the remaining obligations. Rewrite using `[hty, smul_add]`. Introduce `q`.

Establish `hs : ∀ c : I g, (if X.ty g c = X.ty (1 - g) q then X.sg1 (X.u g c) (X.u (1 - g) q) • PowerSeries.mk (fun m => (L + L') m (Sum.inl c)) else 0) = (if X.ty g c = X.ty (1 - g) q then X.sg1 (X.u g c) (X.u (1 - g) q) • PowerSeries.mk (fun m => L m (Sum.inl c)) else 0) + (if X.ty g c = …`. Introduce `c`. Rewrite using `[hty]`. Use `split_ifs`. Rewrite using `[smul_add]`.

Rewrite using `[add_zero]`. Simplify using `only [hs]`. Rewrite using `[Finset.sum_add_distrib, hty, h2 q, h2' q]`. Normalize the expressions using the abelian group laws.
-/
theorem allSet_add (V : VF C) (g : Fin 2) (hA : X.AddCvSt V) (hu : ∀ g c i, V.Ge 0 (X.u g c i))
    {L L' : ℕ → I g ⊕ JJ I g → C} : L ∈ X.AllSet V g → L' ∈ X.AllSet V g → L + L' ∈ X.AllSet V g := by
  intro hx hy
  obtain ⟨γ, lam, hγ, hlam, h1, h2⟩ := hx
  obtain ⟨γ', lam', hγ', hlam', h1', h2'⟩ := hy
  obtain ⟨γ'', hγ'', hL, hS⟩ := hA γ γ' hγ hγ'
  have hty : ∀ n, PowerSeries.mk (fun m => (L + L') m n) =
      PowerSeries.mk (fun m => L m n) + PowerSeries.mk (fun m => L' m n) := fun n => by
    ext m
    simp [PowerSeries.coeff_mk]
  refine ⟨γ'', fun q => lam q + lam' q + (alongCv γ'' (X.sg (X.u (1 - g) q)) - alongCv γ (X.sg (X.u (1 - g) q)) -
    alongCv γ' (X.sg (X.u (1 - g) q))), hγ'', ?_, ?_, ?_⟩
  · intro q
    obtain ⟨c0, cI⟩ := hS (X.u (1 - g) q) (hu (1 - g) q)
    refine ⟨?_, fun n => ?_⟩
    · rw [map_add, map_add, (hlam q).1, (hlam' q).1, c0]
      simp
    · rw [map_add, map_add]
      exact (((hlam q).2 n).add ((hlam' q).2 n)).add (cI n)
  · intro i
    rw [hL i, h1 i, h1' i, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [hty, smul_add]
  · intro q
    have hs : ∀ c : I g, (if X.ty g c = X.ty (1 - g) q then
          X.sg1 (X.u g c) (X.u (1 - g) q) • PowerSeries.mk (fun m => (L + L') m (Sum.inl c)) else 0) =
        (if X.ty g c = X.ty (1 - g) q then
          X.sg1 (X.u g c) (X.u (1 - g) q) • PowerSeries.mk (fun m => L m (Sum.inl c)) else 0) +
        (if X.ty g c = X.ty (1 - g) q then
          X.sg1 (X.u g c) (X.u (1 - g) q) • PowerSeries.mk (fun m => L' m (Sum.inl c)) else 0) := by
      intro c
      rw [hty]
      split_ifs
      · rw [smul_add]
      · rw [add_zero]
    simp only [hs]
    rw [Finset.sum_add_distrib, hty, h2 q, h2' q]
    abel

/- English proof (translation)
Take `⟨γ, lam, hγ, hlam, h1, h2⟩` from `hx`. Establish `hS` using `PowerSeries.HasSubst.of_constantCoeff_zero' hτ`. Establish `hcv : ∀ {σ : Type} (δ : σ → PowerSeries C), IsCv V δ → IsCv V fun i => PowerSeries.subst τ (δ i)`. Introduce `σ δ hδ i`. Use `⟨?_, hint _ (hδ i).2⟩` and prove the remaining obligations.

Conclude with `constantCoeff_subst_zero (σ := Unit) (fun _ => hτ) (hδ i).1`. Use `⟨fun i => PowerSeries.subst τ (γ i), fun q => PowerSeries.subst τ (lam q), hcv γ hγ, hcv lam hlam, ?_, ?_⟩` and prove the remaining obligations. Introduce `i`. Rewrite using `[alongCv_repar (fun i => (hγ i).1) hτ, h1 i, ← PowerSeries.coe_substAlgHom hS, map_sum]`. Use `Finset.sum_congr rfl fun c _ => ?_` and prove the remaining obligations.

Rewrite using `[map_smul, PowerSeries.coe_substAlgHom hS, hxx]`. Introduce `q`. Rewrite using `[alongCv_repar (fun i => (hγ i).1) hτ, hxx, h2 q, ← PowerSeries.coe_substAlgHom hS, map_add, map_sub, map_sum]`. Use `congr 1`. Use `Finset.sum_congr rfl fun c _ => ?_` and prove the remaining obligations.

Use `split_ifs`. Rewrite using `[map_smul, PowerSeries.coe_substAlgHom hS, hxx]`. Rewrite using `[map_zero]`.
-/
theorem allSet_repar {V : VF C} {g : Fin 2} (τ : PowerSeries C) (hτ : PowerSeries.constantCoeff τ = 0)
    (hint : ∀ f : PowerSeries C, (∀ n, V.Ge 0 (PowerSeries.coeff n f)) →
      ∀ n, V.Ge 0 (PowerSeries.coeff n (PowerSeries.subst τ f)))
    {x x' : ℕ → I g ⊕ JJ I g → C} (hx : x ∈ X.AllSet V g)
    (hxx : ∀ n, PowerSeries.mk (fun m => x' m n) = PowerSeries.subst τ (PowerSeries.mk fun m => x m n)) :
    x' ∈ X.AllSet V g := by
  obtain ⟨γ, lam, hγ, hlam, h1, h2⟩ := hx
  have hS := PowerSeries.HasSubst.of_constantCoeff_zero' hτ
  have hcv : ∀ {σ : Type} (δ : σ → PowerSeries C), IsCv V δ → IsCv V fun i => PowerSeries.subst τ (δ i) := by
    intro σ δ hδ i
    refine ⟨?_, hint _ (hδ i).2⟩
    exact constantCoeff_subst_zero (σ := Unit) (fun _ => hτ) (hδ i).1
  refine ⟨fun i => PowerSeries.subst τ (γ i), fun q => PowerSeries.subst τ (lam q), hcv γ hγ, hcv lam hlam, ?_, ?_⟩
  · intro i
    rw [alongCv_repar (fun i => (hγ i).1) hτ, h1 i, ← PowerSeries.coe_substAlgHom hS, map_sum]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [map_smul, PowerSeries.coe_substAlgHom hS, hxx]
  · intro q
    rw [alongCv_repar (fun i => (hγ i).1) hτ, hxx, h2 q, ← PowerSeries.coe_substAlgHom hS, map_add, map_sub,
      map_sum]
    congr 1
    refine Finset.sum_congr rfl fun c _ => ?_
    split_ifs
    · rw [map_smul, PowerSeries.coe_substAlgHom hS, hxx]
    · rw [map_zero]

/- English proof (translation)
Introduce `hL`. Use `X.allSet_repar (c • PowerSeries.X) (by simp) ?_ hL ?_` and prove the remaining obligations. Introduce `f hf n`. Rewrite using `[← PowerSeries.rescale_eq_subst, PowerSeries.coeff_rescale]`. Conclude with `(hc.pow n).mul_int (hf n)`.

Introduce `n`. Rewrite using `[← PowerSeries.rescale_eq_subst]`. Use extensionality with `m`. Rewrite using `[PowerSeries.coeff_rescale, PowerSeries.coeff_mk, PowerSeries.coeff_mk]`.
-/
theorem allSet_teich (V : VF C) (g : Fin 2) (c : C) (hc : V.Ge 0 c) {L : ℕ → I g ⊕ JJ I g → C} :
    L ∈ X.AllSet V g → (fun n k => c ^ n * L n k) ∈ X.AllSet V g := by
  intro hL
  refine X.allSet_repar (c • PowerSeries.X) (by simp) ?_ hL ?_
  · intro f hf n
    rw [← PowerSeries.rescale_eq_subst, PowerSeries.coeff_rescale]
    exact (hc.pow n).mul_int (hf n)
  · intro n
    rw [← PowerSeries.rescale_eq_subst]
    ext m
    rw [PowerSeries.coeff_rescale, PowerSeries.coeff_mk, PowerSeries.coeff_mk]

/- English proof (translation)
Introduce `hx hlim`. Use `choose γ lam hγ hlam hL hM using hx`. Establish `hmk : ∀ n : I g ⊕ JJ I g, TendsS V (fun k => PowerSeries.mk (fun m => L k m n)) (PowerSeries.mk (fun m => L' m n))` using `fun n μ K => hlim K (μ ()) n`. Set `Lk : ℕ → κ → PowerSeries C` to `fun k j => ∑ c : I g, X.u g c j • PowerSeries.mk (fun m => L k m (Sum.inl c))`. Set `L1 : κ → PowerSeries C` to `fun j => ∑ c : I g, X.u g c j • PowerSeries.mk (fun m => L' m (Sum.inl c))`.

Establish `hLt : ∀ j, TendsS V (fun k => Lk k j) (L1 j)` using `fun j => LimTy.tendsS_sum _ fun c _ => LimTy.tendsS_smul _ (hmk (Sum.inl c))`. Establish `hγc : ∀ k i, MvPowerSeries.constantCoeff (γ k i) = 0` using `fun k i => (hγ k i).1`. Establish `hLkc : ∀ k j, MvPowerSeries.constantCoeff (Lk k j) = 0` using `fun k j => by show MvPowerSeries.constantCoeff (∑ c : I g, X.u g c j • PowerSeries.mk (fun m => L k m (Sum.inl c))) = 0`. Rewrite using `[← hL k j]`. Conclude with `constantCoeff_subst_zero (hγc k) (hlg0 j)`.

Establish `hL1c : ∀ j, MvPowerSeries.constantCoeff (L1 j) = 0` using `fun j => by`. Establish `h0` using `hLt j 0`. Establish `e : ∀ k, MvPowerSeries.coeff 0 (Lk k j) = 0` using `fun k => by`. Rewrite using `[MvPowerSeries.coeff_zero_eq_constantCoeff_apply]`. Conclude with `hLkc k j`.

Simplify using `only [e] at h0`. Rewrite using `[← MvPowerSeries.coeff_zero_eq_constantCoeff_apply]`. Conclude with `h0.unique (tends_const 0)`. Establish `hlgS` using `MvPowerSeries.hasSubst_of_constantCoeff_zero hlg0`. Establish `hexS` using `MvPowerSeries.hasSubst_of_constantCoeff_zero hex0`.

Establish `hγeq : ∀ k i, γ k i = MvPowerSeries.subst (Lk k) (X.ex i)`. Introduce `k i`. Establish `hS` using `MvPowerSeries.hasSubst_of_constantCoeff_zero (hγc k)`. Establish `e : Lk k = fun j => MvPowerSeries.subst (γ k) (X.lg j)` using `funext fun j => (hL k j).symm`. Rewrite using `[e, ← MvPowerSeries.subst_comp_subst_apply hlgS hS, hexlg, MvPowerSeries.subst_X hS]`.

Set `γ' : κ → PowerSeries C` to `fun i => MvPowerSeries.subst L1 (X.ex i)`. Establish `hγt : ∀ i, TendsS V (fun k => γ k i) (γ' i)`. Introduce `i`. Establish `e : (fun k => γ k i) = fun k => MvPowerSeries.subst (Lk k) (X.ex i)` using `funext fun k => hγeq k i`. Rewrite using `[e]`.

Conclude with `TendsS.subst (f := fun _ => X.ex i) hLkc hL1c hLt (TendsS.const _)`. Establish `hγ' : IsCv V γ'` using `LimTy.isCv_lim hγt hγ`. Establish `hγ'c : ∀ i, MvPowerSeries.constantCoeff (γ' i) = 0` using `fun i => (hγ' i).1`. Establish `hL1S` using `MvPowerSeries.hasSubst_of_constantCoeff_zero hL1c`. Establish `hlog' : ∀ i, alongCv γ' (X.lg i) = L1 i`.

Introduce `i`. Use `show MvPowerSeries.subst (fun j => MvPowerSeries.subst L1 (X.ex j)) (X.lg i) = L1 i`. Rewrite using `[← MvPowerSeries.subst_comp_subst_apply hexS hL1S, hlgex, MvPowerSeries.subst_X hL1S]`. Set `lam' : JJ I g → PowerSeries C` to `fun q => PowerSeries.mk (fun m => L' m (Sum.inr q)) + alongCv γ' (X.sg (X.u (1 - g) q)) - ∑ c : I g, if X.ty g c = X.ty (1 - g) q then X.sg1 (X.u g c) (X.u (1 - g) q) • PowerSeries.mk (fun m => L' m (Sum.inl c)) else 0`. Establish `hlamk : ∀ k q, lam k q = PowerSeries.mk (fun m => L k m (Sum.inr q)) + alongCv (γ k) (X.sg (X.u (1 - g) q)) - ∑ c : I g, if X.ty g c = X.ty (1 - g) q then X.sg1 (X.u g c) (X.u (1 - g) q) • PowerSeries.mk (fun m => L k m (Sum.inl c)) else 0`.

Introduce `k q`. Rewrite using `[hM k q]`. Expand and normalize the polynomial expressions, which then agree. Establish `hlamt : ∀ q, TendsS V (fun k => lam k q) (lam' q)`. Introduce `q`.

Establish `e : (fun k => lam k q) = fun k => PowerSeries.mk (fun m => L k m (Sum.inr q)) + alongCv (γ k) (X.sg (X.u (1 - g) q)) - ∑ c : I g, if X.ty g c = X.ty (1 - g) q then X.sg1 (X.u g c) (X.u (1 - g) q) • PowerSeries.mk (fun m => L k m (Sum.inl c)) else 0`. Use function extensionality and compare the values at `fun k => hlamk k q`. Rewrite using `[e]`. Use `((hmk (Sum.inr q)).add ?_).sub (LimTy.tendsS_sum _ fun c _ => LimTy.tendsS_ite _ (LimTy.tendsS_smul _ (hmk (Sum.inl c))))` and prove the remaining obligations. Conclude with `TendsS.subst (f := fun _ => X.sg (X.u (1 - g) q)) hγc hγ'c hγt (TendsS.const _)`.

Use `⟨γ', lam', hγ', LimTy.isCv_lim hlamt hlam, hlog', fun q => ?_⟩` and prove the remaining obligations. Simplify using `only [lam']`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem allSet_lim (hlg0 : ∀ i, MvPowerSeries.constantCoeff (X.lg i) = 0)
    (hex0 : ∀ i, MvPowerSeries.constantCoeff (X.ex i) = 0)
    (hlgex : ∀ i, MvPowerSeries.subst X.ex (X.lg i) = MvPowerSeries.X i)
    (hexlg : ∀ i, MvPowerSeries.subst X.lg (X.ex i) = MvPowerSeries.X i)
    {V : VF C} {g : Fin 2} {L : ℕ → ℕ → I g ⊕ JJ I g → C} {L' : ℕ → I g ⊕ JJ I g → C} :
    (∀ k, L k ∈ X.AllSet V g) → VLim V L L' → L' ∈ X.AllSet V g := by
  intro hx hlim
  choose γ lam hγ hlam hL hM using hx
  have hmk : ∀ n : I g ⊕ JJ I g,
      TendsS V (fun k => PowerSeries.mk (fun m => L k m n)) (PowerSeries.mk (fun m => L' m n)) :=
    fun n μ K => hlim K (μ ()) n
  let Lk : ℕ → κ → PowerSeries C := fun k j => ∑ c : I g, X.u g c j • PowerSeries.mk (fun m => L k m (Sum.inl c))
  let L1 : κ → PowerSeries C := fun j => ∑ c : I g, X.u g c j • PowerSeries.mk (fun m => L' m (Sum.inl c))
  have hLt : ∀ j, TendsS V (fun k => Lk k j) (L1 j) :=
    fun j => LimTy.tendsS_sum _ fun c _ => LimTy.tendsS_smul _ (hmk (Sum.inl c))
  have hγc : ∀ k i, MvPowerSeries.constantCoeff (γ k i) = 0 := fun k i => (hγ k i).1
  have hLkc : ∀ k j, MvPowerSeries.constantCoeff (Lk k j) = 0 := fun k j => by
    show MvPowerSeries.constantCoeff (∑ c : I g, X.u g c j • PowerSeries.mk (fun m => L k m (Sum.inl c))) = 0
    rw [← hL k j]
    exact constantCoeff_subst_zero (hγc k) (hlg0 j)
  have hL1c : ∀ j, MvPowerSeries.constantCoeff (L1 j) = 0 := fun j => by
    have h0 := hLt j 0
    have e : ∀ k, MvPowerSeries.coeff 0 (Lk k j) = 0 := fun k => by
      rw [MvPowerSeries.coeff_zero_eq_constantCoeff_apply]; exact hLkc k j
    simp only [e] at h0
    rw [← MvPowerSeries.coeff_zero_eq_constantCoeff_apply]
    exact h0.unique (tends_const 0)
  have hlgS := MvPowerSeries.hasSubst_of_constantCoeff_zero hlg0
  have hexS := MvPowerSeries.hasSubst_of_constantCoeff_zero hex0
  have hγeq : ∀ k i, γ k i = MvPowerSeries.subst (Lk k) (X.ex i) := by
    intro k i
    have hS := MvPowerSeries.hasSubst_of_constantCoeff_zero (hγc k)
    have e : Lk k = fun j => MvPowerSeries.subst (γ k) (X.lg j) := funext fun j => (hL k j).symm
    rw [e, ← MvPowerSeries.subst_comp_subst_apply hlgS hS, hexlg, MvPowerSeries.subst_X hS]
  let γ' : κ → PowerSeries C := fun i => MvPowerSeries.subst L1 (X.ex i)
  have hγt : ∀ i, TendsS V (fun k => γ k i) (γ' i) := by
    intro i
    have e : (fun k => γ k i) = fun k => MvPowerSeries.subst (Lk k) (X.ex i) := funext fun k => hγeq k i
    rw [e]
    exact TendsS.subst (f := fun _ => X.ex i) hLkc hL1c hLt (TendsS.const _)
  have hγ' : IsCv V γ' := LimTy.isCv_lim hγt hγ
  have hγ'c : ∀ i, MvPowerSeries.constantCoeff (γ' i) = 0 := fun i => (hγ' i).1
  have hL1S := MvPowerSeries.hasSubst_of_constantCoeff_zero hL1c
  have hlog' : ∀ i, alongCv γ' (X.lg i) = L1 i := by
    intro i
    show MvPowerSeries.subst (fun j => MvPowerSeries.subst L1 (X.ex j)) (X.lg i) = L1 i
    rw [← MvPowerSeries.subst_comp_subst_apply hexS hL1S, hlgex, MvPowerSeries.subst_X hL1S]
  let lam' : JJ I g → PowerSeries C := fun q =>
    PowerSeries.mk (fun m => L' m (Sum.inr q)) + alongCv γ' (X.sg (X.u (1 - g) q)) -
      ∑ c : I g, if X.ty g c = X.ty (1 - g) q then
        X.sg1 (X.u g c) (X.u (1 - g) q) • PowerSeries.mk (fun m => L' m (Sum.inl c)) else 0
  have hlamk : ∀ k q, lam k q = PowerSeries.mk (fun m => L k m (Sum.inr q)) +
      alongCv (γ k) (X.sg (X.u (1 - g) q)) -
      ∑ c : I g, if X.ty g c = X.ty (1 - g) q then
        X.sg1 (X.u g c) (X.u (1 - g) q) • PowerSeries.mk (fun m => L k m (Sum.inl c)) else 0 := by
    intro k q
    rw [hM k q]
    ring
  have hlamt : ∀ q, TendsS V (fun k => lam k q) (lam' q) := by
    intro q
    have e : (fun k => lam k q) = fun k => PowerSeries.mk (fun m => L k m (Sum.inr q)) +
        alongCv (γ k) (X.sg (X.u (1 - g) q)) -
        ∑ c : I g, if X.ty g c = X.ty (1 - g) q then
          X.sg1 (X.u g c) (X.u (1 - g) q) • PowerSeries.mk (fun m => L k m (Sum.inl c)) else 0 :=
      funext fun k => hlamk k q
    rw [e]
    refine ((hmk (Sum.inr q)).add ?_).sub
      (LimTy.tendsS_sum _ fun c _ => LimTy.tendsS_ite _ (LimTy.tendsS_smul _ (hmk (Sum.inl c))))
    exact TendsS.subst (f := fun _ => X.sg (X.u (1 - g) q)) hγc hγ'c hγt (TendsS.const _)
  refine ⟨γ', lam', hγ', LimTy.isCv_lim hlamt hlam, hlog', fun q => ?_⟩
  simp only [lam']
  ring

end RawChart

end Formalism.L2.FormalSeriesBounds

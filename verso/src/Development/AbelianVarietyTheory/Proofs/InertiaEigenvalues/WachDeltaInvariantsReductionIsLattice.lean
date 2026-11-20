import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.JSmul
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GammaActionReductionStatement

noncomputable section
namespace GlobalTheory.Present.RedLat
open scoped LaurentSeries PowerSeries
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions GlobalTheory.PhiGam GlobalTheory.AdmLoc GlobalTheory.Models

section General
variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL]
    [CommRing O] [Algebra O LL] [TopologicalSpace LL] {v : AddValuation LL (WithTop ℚ)} {n₀ : ℕ}
    (W : LocWach PD LL O v n₀) {k : Type} [Field k] [Algebra O k]

/- English proof (translation)
Rewrite using `[W.DelF_def, isOfFinOrder_iff_pow_eq_one]`.
-/
theorem mem_del (g : W.Gam) : g ∈ W.DelF ↔ IsOfFinOrder g := by
  rw [W.DelF_def, isOfFinOrder_iff_pow_eq_one]

/- English proof (translation)
The claim follows from `(mem_del W 1).2 IsOfFinOrder.one`.
-/
theorem one_mem_del : (1 : W.Gam) ∈ W.DelF := (mem_del W 1).2 IsOfFinOrder.one

/- English proof (translation)
Rewrite `hd` using `[mem_del]`. Use `Finset.prod_nbij' (fun δ => d * δ) (fun δ => d⁻¹ * δ) ?_ ?_ ?_ ?_ ?_` and prove the remaining obligations. Introduce `a ha`. Rewrite `ha`, the goal using `[mem_del]`. Conclude with `hd.mul ha`.

Introduce `a ha`. Rewrite `ha`, the goal using `[mem_del]`. Conclude with `hd.inv.mul ha`. Introduce `a _`. Simplify using the standard rewrite rules.

Introduce `a _`. Simplify using the standard rewrite rules. Introduce `a _`. Both sides reduce to the same expression.
-/
theorem prod_del {M : Type} [CommMonoid M] (f : W.Gam → M) {d : W.Gam} (hd : d ∈ W.DelF) :
    ∏ δ ∈ W.DelF, f (d * δ) = ∏ δ ∈ W.DelF, f δ := by
  rw [mem_del] at hd
  refine Finset.prod_nbij' (fun δ => d * δ) (fun δ => d⁻¹ * δ) ?_ ?_ ?_ ?_ ?_
  · intro a ha
    rw [mem_del] at ha ⊢
    exact hd.mul ha
  · intro a ha
    rw [mem_del] at ha ⊢
    exact hd.inv.mul ha
  · intro a _
    simp
  · intro a _
    simp
  · intro a _
    rfl

/- English proof (translation)
The claim follows from `prod_del W (M := Multiplicative M) f hd`.
-/
theorem sum_del {M : Type} [AddCommMonoid M] (f : W.Gam → M) {d : W.Gam} (hd : d ∈ W.DelF) :
    ∑ δ ∈ W.DelF, f (d * δ) = ∑ δ ∈ W.DelF, f δ :=
  prod_del W (M := Multiplicative M) f hd

/- English proof (translation)
Use `W.γD_smul T g (algebraMap (LetA O n₀) W.EE a) x` as an intermediate fact. Rewrite `this` using `[algebraMap_smul, W.γE_ext, algebraMap_smul]`. Conclude with `this`.
-/
theorem γD_smulA (T : LocLat G Qp LL O) (g : W.Gam) (a : LetA O n₀) (x : W.DD T) :
    W.γD T g (a • x) = W.γA g a • W.γD T g x := by
  have := W.γD_smul T g (algebraMap (LetA O n₀) W.EE a) x
  rw [algebraMap_smul, W.γE_ext, algebraMap_smul] at this
  exact this

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem γA_apply (g : W.Gam) (a : LetA O n₀) (i : ZMod n₀) : W.γA g a i = W.γ₀ g (a i) := rfl

/- English proof (translation)
Introduce `d hd`. Rewrite using `[map_sum]`. Repeatedly rewrite using `[← W.γD_mul]`. Conclude with `sum_del W (fun δ => W.γD T δ x) hd`.
-/
theorem trace_mem (T : LocLat G Qp LL O) (x : W.DD T) : ∑ δ ∈ W.DelF, W.γD T δ x ∈ DΔ W T := by
  intro d hd
  rw [map_sum]
  simp_rw [← W.γD_mul]
  exact sum_del W (fun δ => W.γD T δ x) hd

/- English proof (translation)
Introduce `d hd`. Rewrite using `[γD_smulA, hx d hd]`. Use `congr 1`. Use function extensionality and compare the values at `i`. Conclude with `ha i d hd`.
-/
theorem smul_mem_DΔ (T : LocLat G Qp LL O) {a : LetA O n₀} (ha : ∀ i, ∀ δ ∈ W.DelF, W.γ₀ δ (a i) = a i)
    {x : W.DD T} (hx : x ∈ DΔ W T) : a • x ∈ DΔ W T := by
  intro d hd
  rw [γD_smulA, hx d hd]
  congr 1
  funext i
  exact ha i d hd

/- English proof (translation)
Use `(W.N_base T hT).inductionOn x _ ⟨0, 0, 0, zero_mem _, by simp⟩ ?_ ?_ ?_` and prove the remaining obligations. Introduce `y`. Conclude with `⟨0, y, 0, y.2, by simp⟩`. Introduce and unpack `e x ⟨m, y, z, hy, h⟩`. Take `⟨a, m', ha⟩` from `W.EE_dense e 1`.

Rewrite `ha` using `[pow_one, Ideal.mem_span_singleton']`. Take `⟨e', he'⟩` from `ha`. Use `⟨m' + m, a • y, e' • y + (e * algebraMap (LetA O n₀) W.EE (letπ ^ m')) • z, (W.N T).smul_mem _ hy, ?_⟩` and prove the remaining obligations. Establish `h1 : ((letπ : LetA O n₀) ^ (m' + m)) • e • x = (e * algebraMap (LetA O n₀) W.EE (letπ ^ m')) • ((letπ : LetA O n₀) ^ m) • x`. Rewrite using `[← algebraMap_smul W.EE (letπ ^ (m' + m) : LetA O n₀), ← algebraMap_smul W.EE (letπ ^ m : LetA O n₀), smul_smul, smul_smul, pow_add, map_mul]`.

Use `congr 1`. Expand and normalize the polynomial expressions, which then agree. Establish `h2 : e * algebraMap (LetA O n₀) W.EE (letπ ^ m') = algebraMap (LetA O n₀) W.EE a + e' * (PD.p : W.EE)` using `by rw [he']; ring`. Rewrite using `[h1, h, smul_add, smul_add, smul_comm _ PD.p z, ← add_assoc]`. Use `congr 1`.

Rewrite using `[h2, add_smul, algebraMap_smul, mul_comm, mul_smul, Nat.cast_smul_eq_nsmul]`. Introduce and unpack `x x' ⟨m, y, z, hy, h⟩ ⟨m', y', z', hy', h'⟩`. Use `⟨m + m', ((letπ : LetA O n₀) ^ m') • y + ((letπ : LetA O n₀) ^ m) • y', ((letπ : LetA O n₀) ^ m') • z + ((letπ : LetA O n₀) ^ m) • z', add_mem ((W.N T).smul_mem _ hy) ((W.N T).smul_mem _ hy'), ?_⟩` and prove the remaining obligations. Rewrite using `[smul_add]`. Use `nth_rewrite 1 [add_comm m m']`.

Rewrite using `[pow_add, pow_add, mul_smul, mul_smul, h, h']`. Simplify using `only [smul_add, smul_comm _ PD.p]`. Normalize the expressions using the abelian group laws.
-/
theorem approx (T : LocLat G Qp LL O) (hT : IsCrys PD T.ρ) (x : W.DD T) :
    ∃ (m : ℕ) (y z : W.DD T), y ∈ W.N T ∧ ((letπ : LetA O n₀) ^ m) • x = y + PD.p • z := by
  refine (W.N_base T hT).inductionOn x _ ⟨0, 0, 0, zero_mem _, by simp⟩ ?_ ?_ ?_
  · intro y
    exact ⟨0, y, 0, y.2, by simp⟩
  · rintro e x ⟨m, y, z, hy, h⟩
    obtain ⟨a, m', ha⟩ := W.EE_dense e 1
    rw [pow_one, Ideal.mem_span_singleton'] at ha
    obtain ⟨e', he'⟩ := ha
    refine ⟨m' + m, a • y, e' • y + (e * algebraMap (LetA O n₀) W.EE (letπ ^ m')) • z,
      (W.N T).smul_mem _ hy, ?_⟩
    have h1 : ((letπ : LetA O n₀) ^ (m' + m)) • e • x =
        (e * algebraMap (LetA O n₀) W.EE (letπ ^ m')) • ((letπ : LetA O n₀) ^ m) • x := by
      rw [← algebraMap_smul W.EE (letπ ^ (m' + m) : LetA O n₀), ← algebraMap_smul W.EE (letπ ^ m : LetA O n₀),
        smul_smul, smul_smul, pow_add, map_mul]
      congr 1
      ring
    have h2 : e * algebraMap (LetA O n₀) W.EE (letπ ^ m') =
        algebraMap (LetA O n₀) W.EE a + e' * (PD.p : W.EE) := by rw [he']; ring
    rw [h1, h, smul_add, smul_add, smul_comm _ PD.p z, ← add_assoc]
    congr 1
    rw [h2, add_smul, algebraMap_smul, mul_comm, mul_smul, Nat.cast_smul_eq_nsmul]
  · rintro x x' ⟨m, y, z, hy, h⟩ ⟨m', y', z', hy', h'⟩
    refine ⟨m + m', ((letπ : LetA O n₀) ^ m') • y + ((letπ : LetA O n₀) ^ m) • y',
      ((letπ : LetA O n₀) ^ m') • z + ((letπ : LetA O n₀) ^ m) • z',
      add_mem ((W.N T).smul_mem _ hy) ((W.N T).smul_mem _ hy'), ?_⟩
    rw [smul_add]
    nth_rewrite 1 [add_comm m m']
    rw [pow_add, pow_add, mul_smul, mul_smul, h, h']
    simp only [smul_add, smul_comm _ PD.p]
    abel

/- English proof (translation)
Use `⟨∏ δ ∈ W.DelF, W.γ₀ δ PowerSeries.X, ∏ δ ∈ W.DelF.erase 1, W.γ₀ δ PowerSeries.X, ?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `d hd`. Rewrite using `[map_prod, ← prod_del W (fun δ => W.γ₀ δ PowerSeries.X) hd]`. Use `Finset.prod_congr rfl fun δ _ => ?_` and prove the remaining obligations. Rewrite using `[map_mul]`.

Both sides reduce to the same expression. Rewrite using `[← Finset.prod_erase_mul _ _ (one_mem_del W), map_one]`. Both sides reduce to the same expression. Rewrite using `[map_prod, Finset.prod_ne_zero_iff]`. Introduce `δ _ h`.

Use `congrArg (PowerSeries.coeff 1) h` as an intermediate fact. Rewrite `this` using `[PowerSeries.coeff_map, (W.γ₀_X δ).2, map_zero]`. Conclude with `((W.χΓ δ).isUnit.map (algebraMap O k)).ne_zero this`.
-/
theorem exists_norm : ∃ u u' : O⟦X⟧, (∀ δ ∈ W.DelF, W.γ₀ δ u = u) ∧ u = u' * PowerSeries.X ∧
    PowerSeries.map (algebraMap O k) u ≠ 0 := by
  classical
  refine ⟨∏ δ ∈ W.DelF, W.γ₀ δ PowerSeries.X, ∏ δ ∈ W.DelF.erase 1, W.γ₀ δ PowerSeries.X, ?_, ?_, ?_⟩
  · intro d hd
    rw [map_prod, ← prod_del W (fun δ => W.γ₀ δ PowerSeries.X) hd]
    refine Finset.prod_congr rfl fun δ _ => ?_
    rw [map_mul]
    rfl
  · rw [← Finset.prod_erase_mul _ _ (one_mem_del W), map_one]
    rfl
  · rw [map_prod, Finset.prod_ne_zero_iff]
    intro δ _ h
    have := congrArg (PowerSeries.coeff 1) h
    rw [PowerSeries.coeff_map, (W.γ₀_X δ).2, map_zero] at this
    exact ((W.χΓ δ).isUnit.map (algebraMap O k)).ne_zero this

/- English proof (translation)
Take `⟨b, hbΔ, hli, hsp⟩` from `hb T hT`. Set `b' : Fin (Module.finrank O ↥T.L.T) → ↥(DΔ W T)` to `fun j => ⟨b j, (hbΔ j).2⟩`. Establish `hmem : ∀ y, y ∈ Submodule.span k⟦X⟧ (Set.range fun j => p.j T A q i (b' j)) ↔ ∃ x : ↥(DΔ W T), (x : W.DD T) ∈ W.N T ∧ p.j T A q i x = y`. Introduce `y`. Rewrite using `[Submodule.mem_span_range_iff_exists_fun]`.

Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨c, rfl⟩ choose a ha hι using fun j => hlift (c j)`. Set `x : _ → ↥(DΔ W T)` to `fun j => ⟨((fun _ => a j) : LetA O n₀) • b j, smul_mem_DΔ W T (fun _ => ha j) (hbΔ j).2⟩`. Use `⟨∑ j, x j, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[AddSubgroup.val_finset_sum]`.

Conclude with `sum_mem fun j _ => (W.N T).smul_mem _ (hbΔ j).1`. Rewrite using `[map_sum]`. Conclude with `Finset.sum_congr rfl fun j _ => p.j_smul T A q hq i (fun _ => a j) (c j) (b' j) (x j) (hι j) rfl`. Introduce and unpack `⟨x, hx, rfl⟩`. Rewrite `hx` using `[hsp, Submodule.mem_span_range_iff_exists_fun]`.

Take `⟨a, ha⟩` from `hx`. Establish `hinv : ∀ j t, ∀ δ ∈ W.DelF, W.γ₀ δ (a j t) = a j t`. Introduce `j t δ hδ`. Establish `h1` using `x.2 δ hδ`. Rewrite `h1` using `[← ha, map_sum]`.

Rewrite `h1` using `[γD_smulA, (hbΔ _).2 δ hδ]`. Establish `h2` using `(Fintype.linearIndependent_iffₛ.1 hli) _ _ h1 j`. Conclude with `congrFun h2 t`. Use `choose c hc using fun j => hred (a j (τ i)) (hinv j (τ i))`. Set `x' : _ → ↥(DΔ W T)` to `fun j => ⟨a j • b j, smul_mem_DΔ W T (hinv j) (hbΔ j).2⟩`.

Establish `hx' : x = ∑ j, x' j`. Apply `Subtype.ext` to reduce the goal to its premises. Rewrite using `[AddSubgroup.val_finset_sum, ← ha]`. Use `⟨c, ?_⟩` and prove the remaining obligations. Rewrite using `[hx', map_sum]`.

Conclude with `Finset.sum_congr rfl fun j _ => (p.j_smul T A q hq i (a j) (c j) (b' j) (x' j) (hc j) rfl).symm`. Use `⟨_, hmem, Submodule.fg_span (Set.finite_range _), ?_⟩` and prove the remaining obligations. Rewrite using `[eq_top_iff]`. Introduce `y _`. Take `⟨x, rfl⟩` from `p.j_surj T A q hq i y`.

Take `⟨m, y, z, hy, h⟩` from `approx W T hT x`. Take `⟨u, u', hu, huu, hu0⟩` from `exists_norm W (k := k)`. Establish `hum : ∀ δ ∈ W.DelF, W.γ₀ δ (u ^ m) = u ^ m` using `fun δ hδ => by rw [map_pow, hu δ hδ]`. Take `⟨c, hc⟩` from `hred _ hum`. Set `a : LetA O n₀` to `fun _ => u ^ m`.

Set `a' : LetA O n₀` to `fun _ => u' ^ m`. Establish `haa : a = a' * letπ ^ m`. Use function extensionality and compare the values at `t`. Simplify using `[a, a', letπ, huu, mul_pow]`. Set `x₁ : ↥(DΔ W T)` to `⟨a • (x : W.DD T), smul_mem_DΔ W T (fun _ => hum) x.2⟩`.

Set `y₁ : ↥(DΔ W T)` to `⟨_, trace_mem W T (a' • y)⟩`. Set `z₁ : ↥(DΔ W T)` to `⟨_, trace_mem W T (a' • z)⟩`. Establish `hx₁ : (x₁ : W.DD T) = a' • y + PD.p • a' • z`. Express the relevant statement in the definitionally equal form `a • (x : W.DD T) = _`. Rewrite using `[haa, mul_smul, h, smul_add, smul_comm a' PD.p]`.

Establish `key : W.DelF.card • x₁ = y₁ + PD.p • z₁`. Apply `Subtype.ext` to reduce the goal to its premises. Express the relevant statement in the definitionally equal form `W.DelF.card • (x₁ : W.DD T) = ∑ δ ∈ W.DelF, W.γD T δ (a' • y) + PD.p • ∑ δ ∈ W.DelF, W.γD T δ (a' • z)`. Rewrite using `[Finset.smul_sum, ← Finset.sum_add_distrib, ← Finset.sum_const]`. Use `Finset.sum_congr rfl fun δ hδ => ?_` and prove the remaining obligations.

Rewrite using `[← map_nsmul, ← map_add, ← hx₁, x₁.2 δ hδ]`. Establish `hj` using `congrArg (p.j T A q i) key`. Rewrite `hj` using `[map_nsmul, map_add, map_nsmul, p.j_smul T A q hq i a c x x₁ hc rfl, ← Nat.cast_smul_eq_nsmul k PD.p, hp, zero_smul, add_zero]`. Establish `hy₁ : p.j T A q i y₁ ∈ Submodule.span k⟦X⟧ (Set.range fun j => p.j T A q i (b' j))` using `(hmem _).2 ⟨y₁, sum_mem fun δ _ => W.N_Γ T δ _ ((W.N T).smul_mem _ hy), rfl⟩`. Establish `hc0 : (c : k⸨X⸩) ≠ 0`.

Introduce `h0`. Rewrite `hc` using `[h0, map_zero, map_pow]`. Apply `pow_ne_zero m hu0` to reduce the goal to its premises. Apply `HahnSeries.ofPowerSeries_injective (Γ := ℤ)` to reduce the goal to its premises. Rewrite using `[map_zero]`.

Conclude with `hc.symm`. Establish `hcard' : ((W.DelF.card : ℕ) : k⸨X⸩) ≠ 0`. Rewrite using `[← map_natCast (algebraMap k k⸨X⸩)]`. Conclude with `(map_ne_zero _).2 hcard`. Establish `hj' : p.j T A q i x = (((W.DelF.card : ℕ) : k⸨X⸩) * (c : k⸨X⸩))⁻¹ • p.j T A q i y₁`.

Rewrite using `[← hj, ← Nat.cast_smul_eq_nsmul k⸨X⸩, ← algebraMap_smul k⸨X⸩ c, smul_smul, smul_smul]`. Express the relevant statement in the definitionally equal form `_ = ((((W.DelF.card : ℕ) : k⸨X⸩) * (c : k⸨X⸩))⁻¹ * _ * (c : k⸨X⸩)) • _`. Rewrite using `[mul_assoc, inv_mul_cancel₀ (mul_ne_zero hcard' hc0), one_smul]`. Rewrite using `[hj']`. Conclude with `Submodule.smul_mem _ _ (Submodule.subset_span hy₁)`.
-/
theorem exists_lat {l n : ℕ} {R : RingPG k l} {F : DFun R n G} {ι : k⸨X⸩ →ₐ[k] k⸨X⸩} {τ : ZMod n → ZMod n₀}
    {γ : W.Gam} (p : Pres W F ι τ γ)
    (hred : ∀ a : O⟦X⟧, (∀ δ ∈ W.DelF, W.γ₀ δ a = a) →
      ∃ c : k⟦X⟧, ι (c : k⸨X⸩) = ((PowerSeries.map (algebraMap O k) a : k⟦X⟧) : k⸨X⸩))
    (hlift : ∀ c : k⟦X⟧, ∃ a : O⟦X⟧, (∀ δ ∈ W.DelF, W.γ₀ δ a = a) ∧
      ι (c : k⸨X⸩) = ((PowerSeries.map (algebraMap O k) a : k⟦X⟧) : k⸨X⸩))
    (hcard : ((W.DelF.card : ℕ) : k) ≠ 0) (hp : ((PD.p : ℕ) : k) = 0) (hb : GlobalTheory.WachUse.InvBasis W)
    (T : LocLat G Qp LL O) (A : Ob k G) (q : ↥T.L.T →ₗ[O] (Fin A.m → k)) (hq : Onto T A q)
    (hT : IsCrys PD T.ρ) (i : ZMod n) :
    ∃ N : Submodule k⟦X⟧ (Vc k A.m),
      (∀ y, y ∈ N ↔ ∃ x : ↥(DΔ W T), (x : W.DD T) ∈ W.N T ∧ p.j T A q i x = y) ∧ IsLat N := by
  obtain ⟨b, hbΔ, hli, hsp⟩ := hb T hT
  let b' : Fin (Module.finrank O ↥T.L.T) → ↥(DΔ W T) := fun j => ⟨b j, (hbΔ j).2⟩
  have hmem : ∀ y, y ∈ Submodule.span k⟦X⟧ (Set.range fun j => p.j T A q i (b' j)) ↔
      ∃ x : ↥(DΔ W T), (x : W.DD T) ∈ W.N T ∧ p.j T A q i x = y := by
    intro y
    rw [Submodule.mem_span_range_iff_exists_fun]
    constructor
    · rintro ⟨c, rfl⟩
      choose a ha hι using fun j => hlift (c j)
      let x : _ → ↥(DΔ W T) := fun j => ⟨((fun _ => a j) : LetA O n₀) • b j,
        smul_mem_DΔ W T (fun _ => ha j) (hbΔ j).2⟩
      refine ⟨∑ j, x j, ?_, ?_⟩
      · rw [AddSubgroup.val_finset_sum]
        exact sum_mem fun j _ => (W.N T).smul_mem _ (hbΔ j).1
      · rw [map_sum]
        exact Finset.sum_congr rfl fun j _ =>
          p.j_smul T A q hq i (fun _ => a j) (c j) (b' j) (x j) (hι j) rfl
    · rintro ⟨x, hx, rfl⟩
      rw [hsp, Submodule.mem_span_range_iff_exists_fun] at hx
      obtain ⟨a, ha⟩ := hx
      have hinv : ∀ j t, ∀ δ ∈ W.DelF, W.γ₀ δ (a j t) = a j t := by
        intro j t δ hδ
        have h1 := x.2 δ hδ
        rw [← ha, map_sum] at h1
        simp_rw [γD_smulA, (hbΔ _).2 δ hδ] at h1
        have h2 := (Fintype.linearIndependent_iffₛ.1 hli) _ _ h1 j
        exact congrFun h2 t
      choose c hc using fun j => hred (a j (τ i)) (hinv j (τ i))
      let x' : _ → ↥(DΔ W T) := fun j => ⟨a j • b j, smul_mem_DΔ W T (hinv j) (hbΔ j).2⟩
      have hx' : x = ∑ j, x' j := by
        apply Subtype.ext
        rw [AddSubgroup.val_finset_sum, ← ha]
      refine ⟨c, ?_⟩
      rw [hx', map_sum]
      exact Finset.sum_congr rfl fun j _ =>
        (p.j_smul T A q hq i (a j) (c j) (b' j) (x' j) (hc j) rfl).symm
  refine ⟨_, hmem, Submodule.fg_span (Set.finite_range _), ?_⟩
  rw [eq_top_iff]
  intro y _
  obtain ⟨x, rfl⟩ := p.j_surj T A q hq i y
  obtain ⟨m, y, z, hy, h⟩ := approx W T hT x
  obtain ⟨u, u', hu, huu, hu0⟩ := exists_norm W (k := k)
  have hum : ∀ δ ∈ W.DelF, W.γ₀ δ (u ^ m) = u ^ m := fun δ hδ => by rw [map_pow, hu δ hδ]
  obtain ⟨c, hc⟩ := hred _ hum
  let a : LetA O n₀ := fun _ => u ^ m
  let a' : LetA O n₀ := fun _ => u' ^ m
  have haa : a = a' * letπ ^ m := by
    funext t
    simp [a, a', letπ, huu, mul_pow]
  let x₁ : ↥(DΔ W T) := ⟨a • (x : W.DD T), smul_mem_DΔ W T (fun _ => hum) x.2⟩
  let y₁ : ↥(DΔ W T) := ⟨_, trace_mem W T (a' • y)⟩
  let z₁ : ↥(DΔ W T) := ⟨_, trace_mem W T (a' • z)⟩
  have hx₁ : (x₁ : W.DD T) = a' • y + PD.p • a' • z := by
    change a • (x : W.DD T) = _
    rw [haa, mul_smul, h, smul_add, smul_comm a' PD.p]
  have key : W.DelF.card • x₁ = y₁ + PD.p • z₁ := by
    apply Subtype.ext
    change W.DelF.card • (x₁ : W.DD T) = ∑ δ ∈ W.DelF, W.γD T δ (a' • y) + PD.p • ∑ δ ∈ W.DelF, W.γD T δ (a' • z)
    rw [Finset.smul_sum, ← Finset.sum_add_distrib, ← Finset.sum_const]
    refine Finset.sum_congr rfl fun δ hδ => ?_
    rw [← map_nsmul, ← map_add, ← hx₁, x₁.2 δ hδ]
  have hj := congrArg (p.j T A q i) key
  rw [map_nsmul, map_add, map_nsmul, p.j_smul T A q hq i a c x x₁ hc rfl,
    ← Nat.cast_smul_eq_nsmul k PD.p, hp, zero_smul, add_zero] at hj
  have hy₁ : p.j T A q i y₁ ∈ Submodule.span k⟦X⟧ (Set.range fun j => p.j T A q i (b' j)) :=
    (hmem _).2 ⟨y₁, sum_mem fun δ _ => W.N_Γ T δ _ ((W.N T).smul_mem _ hy), rfl⟩
  have hc0 : (c : k⸨X⸩) ≠ 0 := by
    intro h0
    rw [h0, map_zero, map_pow] at hc
    apply pow_ne_zero m hu0
    apply HahnSeries.ofPowerSeries_injective (Γ := ℤ)
    rw [map_zero]
    exact hc.symm
  have hcard' : ((W.DelF.card : ℕ) : k⸨X⸩) ≠ 0 := by
    rw [← map_natCast (algebraMap k k⸨X⸩)]
    exact (map_ne_zero _).2 hcard
  have hj' : p.j T A q i x = (((W.DelF.card : ℕ) : k⸨X⸩) * (c : k⸨X⸩))⁻¹ • p.j T A q i y₁ := by
    rw [← hj, ← Nat.cast_smul_eq_nsmul k⸨X⸩, ← algebraMap_smul k⸨X⸩ c, smul_smul, smul_smul]
    change _ = ((((W.DelF.card : ℕ) : k⸨X⸩) * (c : k⸨X⸩))⁻¹ * _ * (c : k⸨X⸩)) • _
    rw [mul_assoc, inv_mul_cancel₀ (mul_ne_zero hcard' hc0), one_smul]
  rw [hj']
  exact Submodule.smul_mem _ _ (Submodule.subset_span hy₁)

/- English proof (translation)
Establish `hl : 2 ≤ l` using `(Fact.out : l.Prime).two_le`. Establish `hpos : 0 < W.DelF.card` using `Finset.card_pos.2 ⟨1, one_mem_del W⟩`. Establish `hle : W.DelF.card ≤ l - 1`. Rewrite using `[← Finset.card_attach]`. Use `le_trans (Finset.card_le_card_of_injOn (t := (Polynomial.nthRoots (l - 1) (1 : ℤ_[l])).toFinset) (fun δ => (e δ).1) ?_ ?_) ((Multiset.toFinset_card_le _).trans (Polynomial.card_nthRoots _ _))` and prove the remaining obligations.

Introduce `δ _`. Simplify using `only [Finset.mem_coe, Multiset.mem_toFinset]`. Rewrite using `[Polynomial.mem_nthRoots (by omega)]`. Conclude with `(e δ).2`. Introduce `a _ b _ h`.

Conclude with `e.injective (Subtype.ext h)`. Rewrite using `[Ne, CharP.cast_eq_zero_iff k l]`. Introduce `h`. Use `Nat.le_of_dvd hpos h` as an intermediate fact. Use linear arithmetic over natural numbers and integers.
-/
theorem card_ne_zero {l : ℕ} [Fact l.Prime] [CharP k l]
    (e : {δ // δ ∈ W.DelF} ≃ {z : ℤ_[l] // z ^ (l - 1) = 1}) : ((W.DelF.card : ℕ) : k) ≠ 0 := by
  classical
  have hl : 2 ≤ l := (Fact.out : l.Prime).two_le
  have hpos : 0 < W.DelF.card := Finset.card_pos.2 ⟨1, one_mem_del W⟩
  have hle : W.DelF.card ≤ l - 1 := by
    rw [← Finset.card_attach]
    refine le_trans (Finset.card_le_card_of_injOn (t := (Polynomial.nthRoots (l - 1) (1 : ℤ_[l])).toFinset)
      (fun δ => (e δ).1) ?_ ?_) ((Multiset.toFinset_card_le _).trans (Polynomial.card_nthRoots _ _))
    · intro δ _
      simp only [Finset.mem_coe, Multiset.mem_toFinset]
      rw [Polynomial.mem_nthRoots (by omega)]
      exact (e δ).2
    · intro a _ b _ h
      exact e.injective (Subtype.ext h)
  rw [Ne, CharP.cast_eq_zero_iff k l]
  intro h
  have := Nat.le_of_dvd hpos h
  omega

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `a ha`. Use `(hι.2.2.1 _).1 fun z hz => ?_` and prove the remaining obligations. Use `he (e.symm ⟨z, hz⟩) a` as an intermediate fact. Rewrite `this` using `[Equiv.apply_symm_apply, ha _ (e.symm ⟨z, hz⟩).2]`.

Conclude with `this.symm`. Introduce `c`. Take `⟨b, hb⟩` from `hι.2.1 c`. Establish `hinv` using `(hι.2.2.1 b).2 ⟨c, hb⟩`. Take `⟨b₀, rfl⟩` from `PowerSeries.map_surjective (algebraMap O k) hs b`.

Take `⟨d, hd⟩` from `hs ((W.DelF.card : ℕ) : k)⁻¹`. Use `⟨∑ δ ∈ W.DelF, W.γ₀ δ (d • b₀), ?_, ?_⟩` and prove the remaining obligations. Introduce `g hg`. Rewrite using `[map_sum, ← sum_del W (fun δ => W.γ₀ δ (d • b₀)) hg]`. Use `Finset.sum_congr rfl fun δ _ => ?_` and prove the remaining obligations.

Rewrite using `[map_mul]`. Both sides reduce to the same expression. Rewrite using `[hb, map_sum]`. Use `congr 1`. Establish `h1 : ∀ δ ∈ W.DelF, PowerSeries.map (algebraMap O k) (W.γ₀ δ (d • b₀)) = ((W.DelF.card : ℕ) : k)⁻¹ • PowerSeries.map (algebraMap O k) b₀`.

Introduce `δ hδ`. Rewrite using `[map_smul, PowerSeries.smul_eq_C_mul, map_mul, PowerSeries.map_C, hd, he ⟨δ, hδ⟩, hinv _ (e ⟨δ, hδ⟩).2, PowerSeries.smul_eq_C_mul]`. Rewrite using `[Finset.sum_congr rfl h1, Finset.sum_const, ← Nat.cast_smul_eq_nsmul k, smul_smul, mul_inv_cancel₀ (card_ne_zero W e), one_smul]`.
-/
theorem red_lift {l : ℕ} [Fact l.Prime] [CharP k l] {R : RingPG k l} {ι : k⸨X⸩ →ₐ[k] k⸨X⸩}
    (hι : GlobalTheory.IndefiniteRowSideFullHecke.OnePlusPowerCharacters.IsCyclotomic R ι) (hs : Function.Surjective (algebraMap O k))
    (e : {δ // δ ∈ W.DelF} ≃ {z : ℤ_[l] // z ^ (l - 1) = 1})
    (he : ∀ δ a, PowerSeries.map (algebraMap O k) (W.γ₀ δ.1 a) =
      GlobalTheory.IndefiniteRowSideFullHecke.OnePlusPowerCharacters.deltaPi k l (e δ).1 (PowerSeries.map (algebraMap O k) a)) :
    (∀ a : O⟦X⟧, (∀ δ ∈ W.DelF, W.γ₀ δ a = a) →
      ∃ c : k⟦X⟧, ι (c : k⸨X⸩) = ((PowerSeries.map (algebraMap O k) a : k⟦X⟧) : k⸨X⸩)) ∧
    (∀ c : k⟦X⟧, ∃ a : O⟦X⟧, (∀ δ ∈ W.DelF, W.γ₀ δ a = a) ∧
      ι (c : k⸨X⸩) = ((PowerSeries.map (algebraMap O k) a : k⟦X⟧) : k⸨X⸩)) := by
  constructor
  · intro a ha
    refine (hι.2.2.1 _).1 fun z hz => ?_
    have := he (e.symm ⟨z, hz⟩) a
    rw [Equiv.apply_symm_apply, ha _ (e.symm ⟨z, hz⟩).2] at this
    exact this.symm
  · intro c
    obtain ⟨b, hb⟩ := hι.2.1 c
    have hinv := (hι.2.2.1 b).2 ⟨c, hb⟩
    obtain ⟨b₀, rfl⟩ := PowerSeries.map_surjective (algebraMap O k) hs b
    obtain ⟨d, hd⟩ := hs ((W.DelF.card : ℕ) : k)⁻¹
    refine ⟨∑ δ ∈ W.DelF, W.γ₀ δ (d • b₀), ?_, ?_⟩
    · intro g hg
      rw [map_sum, ← sum_del W (fun δ => W.γ₀ δ (d • b₀)) hg]
      refine Finset.sum_congr rfl fun δ _ => ?_
      rw [map_mul]
      rfl
    · rw [hb, map_sum]
      congr 1
      have h1 : ∀ δ ∈ W.DelF, PowerSeries.map (algebraMap O k) (W.γ₀ δ (d • b₀)) =
          ((W.DelF.card : ℕ) : k)⁻¹ • PowerSeries.map (algebraMap O k) b₀ := by
        intro δ hδ
        rw [map_smul, PowerSeries.smul_eq_C_mul, map_mul, PowerSeries.map_C, hd, he ⟨δ, hδ⟩,
          hinv _ (e ⟨δ, hδ⟩).2, PowerSeries.smul_eq_C_mul]
      rw [Finset.sum_congr rfl h1, Finset.sum_const, ← Nat.cast_smul_eq_nsmul k, smul_smul,
        mul_inv_cancel₀ (card_ne_zero W e), one_smul]

end General

end GlobalTheory.Present.RedLat

open GlobalTheory.PhiGam GlobalTheory.AdmLoc GlobalTheory.Models GlobalTheory.TopSteps GlobalTheory.Present Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc
open scoped LaurentSeries PowerSeries

set_option maxHeartbeats 2000000 in

/- English proof (translation)
Introduce `l _ P H S k _ _ _ hres R ι F τ γ p hι _ _ hQ T A q U hq _ hT`. Take `⟨-, e, he⟩` from `GlobalTheory.T.map_gamma_eq_deltaPi_teichmuller H S k`. Take `⟨h1, h2⟩` from `GlobalTheory.Present.RedLat.red_lift (S.W H) hι hres.1 e he`. Establish `hp : (((P.PD S.K).p : ℕ) : k) = 0`. Rewrite using `[P.PD_p]`.

Conclude with `CharP.cast_eq_zero k l`. Use `choose N hN hL using GlobalTheory.Present.RedLat.exists_lat (S.W H) p h1 h2 (GlobalTheory.Present.RedLat.card_ne_zero (S.W H) e) hp hQ.1 T A q hq hT.1`. Conclude with `⟨N, hN, hL⟩`.
-/
theorem GlobalTheory.Present.RedLat.red_isLat : ∀ {l : ℕ} [Fact l.Prime] {P : LocPrime l} (H : LocHW l P) (S : TopSit P) (k : Type) [Field k] [Algebra S.O k] [CharP k l], S.IsRes k → ∀ {R : RingPG k l} (ι : k⸨X⸩ →ₐ[k] k⸨X⸩) (F : DFun R S.n S.G) (τ : ZMod S.n → ZMod (Module.finrank ℚ_[l] ↥(K0 S.K))) (γ : (S.W H).Gam) (p : Pres (S.W H) F ι τ γ), GlobalTheory.IndefiniteRowSideFullHecke.OnePlusPowerCharacters.IsCyclotomic R ι → (∀ i, (S.W H).emb (τ i) = S.emb i) → ((S.W H).χΓ γ : S.O) = 1 + (l : S.O) → GlobalTheory.WachUse.QN (S.W H) → ∀ (T : LocLat S.G ℚ_[l] ↥S.LL.1 S.O) (A : Ob k S.G) q (U : ZMod S.n → Multiset ℤ), Onto T A q → KerIs S.Γ.lam q → CrysWith (P.PD S.K) S.emb T.ρ U → ∃ N : Lats k S.n A.m, (∀ i y, y ∈ N i ↔ ∃ x : ↥(DΔ (S.W H) T), (x : (S.W H).DD T) ∈ (S.W H).N T ∧ p.j T A q i x = y) ∧ ∀ i, IsLat (N i) := by
  intro l _ P H S k _ _ _ hres R ι F τ γ p hι _ _ hQ T A q U hq _ hT
  obtain ⟨-, e, he⟩ := GlobalTheory.T.map_gamma_eq_deltaPi_teichmuller H S k
  obtain ⟨h1, h2⟩ := GlobalTheory.Present.RedLat.red_lift (S.W H) hι hres.1 e he
  have hp : (((P.PD S.K).p : ℕ) : k) = 0 := by
    rw [P.PD_p]
    exact CharP.cast_eq_zero k l
  choose N hN hL using GlobalTheory.Present.RedLat.exists_lat (S.W H) p h1 h2
    (GlobalTheory.Present.RedLat.card_ne_zero (S.W H) e) hp hQ.1 T A q hq hT.1
  exact ⟨N, hN, hL⟩

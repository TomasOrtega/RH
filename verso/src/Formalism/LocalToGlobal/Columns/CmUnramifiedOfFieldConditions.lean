import Mathlib
import Formalism.LocalToGlobal.Columns.ColFormsLemmas
import Formalism.LocalToGlobal.Columns.LevGCount
import Formalism.LocalToGlobal.Columns.AlgebraMapMemMaximalIdealPowIff
import Formalism.LocalToGlobal.Columns.Inputs
import Formalism.GL3MeanSquares.HookFormulaTorsion.DimensionMassJointBound
import Formalism.GL3MeanSquares.HookFormulaTorsion.OneAddInvPowLeExpOne
import Formalism.GL3MeanSquares.HookFormulaTorsion.FactorialProductRearrangement
import Formalism.GL3MeanSquares.HookFormulaTorsion.SumWeightsOverPrimeLeHalfDegree
import Formalism.HermitianLattices.FinalNeighbourConstruct
import Formalism.HermitianLattices.FinalMass

open NumberField IsDedekindDomain Module

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV

section Frame

variable {K : Type} [Field K] [NumberField K] {V : Type} [AddCommGroup V] [Module K V] [Module (𝓞 K) V]
  [IsScalarTower (𝓞 K) K V]

/- English proof (translation)
Use `haveI := w.isMaximal`. Establish `hs' : Ideal.Quotient.mk w.asIdeal s ≠ 0`. Rewrite using `[Ne, Ideal.Quotient.eq_zero_iff_mem]` and apply the resulting hypothesis. Take `⟨b, hb⟩` from `Ideal.Quotient.exists_inv hs'`. Take `⟨t, rfl⟩` from `Ideal.Quotient.mk_surjective b`.

Use `⟨t, ?_⟩` and prove the remaining obligations. Rewrite using `[← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_mul, map_one, mul_comm, hb, sub_self]`.
-/
theorem exists_mul_sub_one_mem (w : HeightOneSpectrum (𝓞 K)) {s : 𝓞 K} (hs : s ∉ w.asIdeal) :
    ∃ t : 𝓞 K, t * s - 1 ∈ w.asIdeal := by
  haveI := w.isMaximal
  have hs' : Ideal.Quotient.mk w.asIdeal s ≠ 0 := by
    rwa [Ne, Ideal.Quotient.eq_zero_iff_mem]
  obtain ⟨b, hb⟩ := Ideal.Quotient.exists_inv hs'
  obtain ⟨t, rfl⟩ := Ideal.Quotient.mk_surjective b
  refine ⟨t, ?_⟩
  rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_mul, map_one, mul_comm, hb, sub_self]

/- English proof (translation)
Take `⟨t, ht⟩` from `exists_mul_sub_one_mem w hs`. Establish `e : x = t • (s • x) - (t * s - 1) • x`. Rewrite using `[smul_smul, sub_smul, one_smul]`. Normalize the expressions using the abelian group laws. Rewrite using `[e]`.

Conclude with `Submodule.sub_mem _ (Submodule.smul_mem _ t hsx) (Submodule.smul_mem_smul ht hx)`.
-/
theorem mem_smul_of_smul_mem (w : HeightOneSpectrum (𝓞 K)) {N : Submodule (𝓞 K) V} {s : 𝓞 K} (hs : s ∉ w.asIdeal)
    {x : V} (hx : x ∈ N) (hsx : s • x ∈ w.asIdeal • N) : x ∈ w.asIdeal • N := by
  obtain ⟨t, ht⟩ := exists_mul_sub_one_mem w hs
  have e : x = t • (s • x) - (t * s - 1) • x := by
    rw [smul_smul, sub_smul, one_smul]
    abel
  rw [e]
  exact Submodule.sub_mem _ (Submodule.smul_mem _ t hsx) (Submodule.smul_mem_smul ht hx)

structure FrameAt (w : HeightOneSpectrum (𝓞 K)) (N : Submodule (𝓞 K) V) {n : ℕ}
    (β : V → (Fin n → 𝓞 K ⧸ w.asIdeal)) : Prop where
  add : ∀ x ∈ localization₂ w.asIdeal N, ∀ y ∈ localization₂ w.asIdeal N, β (x + y) = β x + β y
  smul : ∀ (a : 𝓞 K), ∀ x ∈ localization₂ w.asIdeal N, β (a • x) = Ideal.Quotient.mk w.asIdeal a • β x
  off : ∀ x, x ∉ localization₂ w.asIdeal N → β x = 0
  surj : ∀ c, ∃ x ∈ N, β x = c
  ker : ∀ x ∈ N, β x = 0 → x ∈ w.asIdeal • N

/- English proof (translation)
Use `atW_finite w hfg` as an intermediate fact. Use `atW_free w hfg` as an intermediate fact. Establish `hr : finrank (Ow w) (atW w N) = n` using `by rw [finrank_atW w hfg, hspan, finrank_top, hn]`. Set `b : Basis (Fin n) (Ow w) (atW w N)` to `Module.finBasisOfFinrankEq _ _ hr`. Establish `hunit : ∀ y : w.asIdeal.primeCompl, IsUnit (Ideal.Quotient.mk w.asIdeal (y : 𝓞 K))`.

Introduce `y`. Take `⟨t, ht⟩` from `exists_mul_sub_one_mem w y.2`. Use `isUnit_iff_exists_inv'.mpr ⟨Ideal.Quotient.mk w.asIdeal t, ?_⟩` and prove the remaining obligations. Rewrite using `[← map_mul, ← map_one (Ideal.Quotient.mk w.asIdeal)]`. Conclude with `Ideal.Quotient.eq.mpr ht`.

Set `ρ : Ow w →+* 𝓞 K ⧸ w.asIdeal` to `IsLocalization.lift (M := w.asIdeal.primeCompl) (g := Ideal.Quotient.mk w.asIdeal) hunit`. Establish `hρ : ∀ a : 𝓞 K, ρ (algebraMap (𝓞 K) (Ow w) a) = Ideal.Quotient.mk w.asIdeal a` using `fun a => IsLocalization.lift_eq hunit a`. Establish `hmem : ∀ x : V, x ∈ localization₂ w.asIdeal N ↔ x ∈ atW w N`. Introduce `x`. Rewrite using `[← atW_restrictScalars, Submodule.restrictScalars_mem]`.

Set `β : V → (Fin n → 𝓞 K ⧸ w.asIdeal)` to `fun x => if hx : x ∈ atW w N then fun i => ρ (b.repr ⟨x, hx⟩ i) else 0`. Establish `hβ : ∀ (x : V) (hx : x ∈ atW w N), β x = fun i => ρ (b.repr ⟨x, hx⟩ i)` using `fun x hx => dif_pos hx`. Establish `hsmul : ∀ (a : 𝓞 K), ∀ x ∈ localization₂ w.asIdeal N, β (a • x) = Ideal.Quotient.mk w.asIdeal a • β x`. Introduce `a x hx`. Establish `hx'` using `(hmem x).1 hx`.

Establish `hax : a • x ∈ atW w N` using `(hmem _).1 (Submodule.smul_mem _ a hx)`. Rewrite using `[hβ _ hax, hβ _ hx']`. Use function extensionality and compare the values at `i`. Establish `e : (⟨a • x, hax⟩ : atW w N) = algebraMap (𝓞 K) (Ow w) a • (⟨x, hx'⟩ : atW w N)` using `Subtype.ext (algebraMap_smul (Ow w) a x).symm`. Rewrite using `[e, map_smul, Finsupp.smul_apply, smul_eq_mul, map_mul, hρ]`.

Both sides reduce to the same expression. Use `⟨β, ⟨?_, hsmul, ?_, ?_, ?_⟩⟩` and prove the remaining obligations. Introduce `x hx y hy`. Establish `hx'` using `(hmem x).1 hx`. Establish `hy'` using `(hmem y).1 hy`.

Rewrite using `[hβ _ ((atW w N).add_mem hx' hy'), hβ _ hx', hβ _ hy']`. Use function extensionality and compare the values at `i`. Establish `e : (⟨x + y, (atW w N).add_mem hx' hy'⟩ : atW w N) = ⟨x, hx'⟩ + ⟨y, hy'⟩` using `rfl`. Rewrite using `[e, map_add, Finsupp.add_apply, map_add]`. Both sides reduce to the same expression.

Introduce `x hx`. Conclude with `dif_neg fun h => hx ((hmem x).2 h)`. Introduce `c choose a ha using fun i => Ideal.Quotient.mk_surjective (c i)`. Set `x' : atW w N` to `∑ i, algebraMap (𝓞 K) (Ow w) (a i) • b i`. Establish `h1 : β (x' : V) = c`.

Rewrite using `[hβ _ x'.2]`. Use function extensionality and compare the values at `i`. Establish `: b.repr ⟨(x' : V), x'.2⟩ = b.repr x'` using `rfl`. Rewrite using `[this, b.repr_sum_self, hρ, ha]`. Take `⟨s, hs, hsx⟩` from `mem_atW_iff.1 x'.2`.

Take `⟨t, ht⟩` from `exists_mul_sub_one_mem w hs`. Use `⟨(t * s) • (x' : V), ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[mul_smul]`. Conclude with `N.smul_mem t hsx`. Rewrite using `[hsmul _ _ ((hmem _).2 x'.2), h1]`.

Establish `: Ideal.Quotient.mk w.asIdeal (t * s) = 1`. Rewrite using `[← map_one (Ideal.Quotient.mk w.asIdeal)]`. Conclude with `Ideal.Quotient.eq.mpr ht`. Rewrite using `[this, one_smul]`. Introduce `x hx h0`.

Establish `hx' : x ∈ atW w N` using `le_atW w N hx`. Rewrite `h0` using `[hβ _ hx']`. Establish `hterm : ∀ i, ((b.repr ⟨x, hx'⟩ i • b i : atW w N) : V) ∈ localization₂ w.asIdeal (w.asIdeal • N)`. Introduce `i`. Take `⟨a, s, has⟩` from `IsLocalization.exists_mk'_eq w.asIdeal.primeCompl (b.repr ⟨x, hx'⟩ i)`.

Establish `ha : a ∈ w.asIdeal`. Establish `h1 : ρ (b.repr ⟨x, hx'⟩ i) = 0` using `congrFun h0 i`. Establish `h2 : b.repr ⟨x, hx'⟩ i * algebraMap (𝓞 K) (Ow w) (s : 𝓞 K) = algebraMap (𝓞 K) (Ow w) a`. Rewrite using `[← has]`. Conclude with `IsLocalization.mk'_spec _ _ _`.

Establish `h3` using `congrArg ρ h2`. Rewrite `h3` using `[map_mul, h1, zero_mul, hρ]`. Conclude with `Ideal.Quotient.eq_zero_iff_mem.mp h3.symm`. Take `⟨t, ht, htb⟩` from `mem_atW_iff.1 (b i).2`. Use `⟨(s : 𝓞 K) * t, fun h => (w.isPrime.mem_or_mem h).elim s.2 ht, ?_⟩` and prove the remaining obligations.

Rewrite using `[Submodule.coe_smul, ← has, mul_smul, smul_comm t, mk'_smul]`. Conclude with `Submodule.smul_mem_smul ha htb`. Establish `hsum : x ∈ localization₂ w.asIdeal (w.asIdeal • N)`. Establish `h1 : x = ((∑ i, b.repr ⟨x, hx'⟩ i • b i : atW w N) : V)` using `by rw [b.sum_repr]`. Rewrite using `[h1, Submodule.coe_sum]`.

Conclude with `Submodule.sum_mem _ fun i _ => hterm i`. Take `⟨s, hs, hsx⟩` from `hsum`. Conclude with `mem_smul_of_smul_mem w hs hx hsx`.
-/
theorem exists_frameAt (w : HeightOneSpectrum (𝓞 K)) (N : Submodule (𝓞 K) V) (hfg : N.FG)
    (hspan : Submodule.span K (N : Set V) = ⊤) {n : ℕ} (hn : finrank K V = n) :
    ∃ β : V → (Fin n → 𝓞 K ⧸ w.asIdeal), FrameAt w N β := by
  classical
  have := atW_finite w hfg
  have := atW_free w hfg
  have hr : finrank (Ow w) (atW w N) = n := by rw [finrank_atW w hfg, hspan, finrank_top, hn]
  let b : Basis (Fin n) (Ow w) (atW w N) := Module.finBasisOfFinrankEq _ _ hr
  have hunit : ∀ y : w.asIdeal.primeCompl, IsUnit (Ideal.Quotient.mk w.asIdeal (y : 𝓞 K)) := by
    intro y
    obtain ⟨t, ht⟩ := exists_mul_sub_one_mem w y.2
    refine isUnit_iff_exists_inv'.mpr ⟨Ideal.Quotient.mk w.asIdeal t, ?_⟩
    rw [← map_mul, ← map_one (Ideal.Quotient.mk w.asIdeal)]
    exact Ideal.Quotient.eq.mpr ht
  let ρ : Ow w →+* 𝓞 K ⧸ w.asIdeal :=
    IsLocalization.lift (M := w.asIdeal.primeCompl) (g := Ideal.Quotient.mk w.asIdeal) hunit
  have hρ : ∀ a : 𝓞 K, ρ (algebraMap (𝓞 K) (Ow w) a) = Ideal.Quotient.mk w.asIdeal a :=
    fun a => IsLocalization.lift_eq hunit a
  have hmem : ∀ x : V, x ∈ localization₂ w.asIdeal N ↔ x ∈ atW w N := by
    intro x
    rw [← atW_restrictScalars, Submodule.restrictScalars_mem]
  let β : V → (Fin n → 𝓞 K ⧸ w.asIdeal) := fun x =>
    if hx : x ∈ atW w N then fun i => ρ (b.repr ⟨x, hx⟩ i) else 0
  have hβ : ∀ (x : V) (hx : x ∈ atW w N), β x = fun i => ρ (b.repr ⟨x, hx⟩ i) := fun x hx => dif_pos hx
  have hsmul : ∀ (a : 𝓞 K), ∀ x ∈ localization₂ w.asIdeal N, β (a • x) = Ideal.Quotient.mk w.asIdeal a • β x := by
    intro a x hx
    have hx' := (hmem x).1 hx
    have hax : a • x ∈ atW w N := (hmem _).1 (Submodule.smul_mem _ a hx)
    rw [hβ _ hax, hβ _ hx']
    funext i
    have e : (⟨a • x, hax⟩ : atW w N) = algebraMap (𝓞 K) (Ow w) a • (⟨x, hx'⟩ : atW w N) :=
      Subtype.ext (algebraMap_smul (Ow w) a x).symm
    rw [e, map_smul, Finsupp.smul_apply, smul_eq_mul, map_mul, hρ]
    rfl
  refine ⟨β, ⟨?_, hsmul, ?_, ?_, ?_⟩⟩
  · intro x hx y hy
    have hx' := (hmem x).1 hx
    have hy' := (hmem y).1 hy
    rw [hβ _ ((atW w N).add_mem hx' hy'), hβ _ hx', hβ _ hy']
    funext i
    have e : (⟨x + y, (atW w N).add_mem hx' hy'⟩ : atW w N) = ⟨x, hx'⟩ + ⟨y, hy'⟩ := rfl
    rw [e, map_add, Finsupp.add_apply, map_add]
    rfl
  · intro x hx
    exact dif_neg fun h => hx ((hmem x).2 h)
  · intro c
    choose a ha using fun i => Ideal.Quotient.mk_surjective (c i)
    let x' : atW w N := ∑ i, algebraMap (𝓞 K) (Ow w) (a i) • b i
    have h1 : β (x' : V) = c := by
      rw [hβ _ x'.2]
      funext i
      have : b.repr ⟨(x' : V), x'.2⟩ = b.repr x' := rfl
      rw [this, b.repr_sum_self, hρ, ha]
    obtain ⟨s, hs, hsx⟩ := mem_atW_iff.1 x'.2
    obtain ⟨t, ht⟩ := exists_mul_sub_one_mem w hs
    refine ⟨(t * s) • (x' : V), ?_, ?_⟩
    · rw [mul_smul]
      exact N.smul_mem t hsx
    · rw [hsmul _ _ ((hmem _).2 x'.2), h1]
      have : Ideal.Quotient.mk w.asIdeal (t * s) = 1 := by
        rw [← map_one (Ideal.Quotient.mk w.asIdeal)]
        exact Ideal.Quotient.eq.mpr ht
      rw [this, one_smul]
  · intro x hx h0
    have hx' : x ∈ atW w N := le_atW w N hx
    rw [hβ _ hx'] at h0
    have hterm : ∀ i, ((b.repr ⟨x, hx'⟩ i • b i : atW w N) : V) ∈ localization₂ w.asIdeal (w.asIdeal • N) := by
      intro i
      obtain ⟨a, s, has⟩ := IsLocalization.exists_mk'_eq w.asIdeal.primeCompl (b.repr ⟨x, hx'⟩ i)
      have ha : a ∈ w.asIdeal := by
        have h1 : ρ (b.repr ⟨x, hx'⟩ i) = 0 := congrFun h0 i
        have h2 : b.repr ⟨x, hx'⟩ i * algebraMap (𝓞 K) (Ow w) (s : 𝓞 K) = algebraMap (𝓞 K) (Ow w) a := by
          rw [← has]; exact IsLocalization.mk'_spec _ _ _
        have h3 := congrArg ρ h2
        rw [map_mul, h1, zero_mul, hρ] at h3
        exact Ideal.Quotient.eq_zero_iff_mem.mp h3.symm
      obtain ⟨t, ht, htb⟩ := mem_atW_iff.1 (b i).2
      refine ⟨(s : 𝓞 K) * t, fun h => (w.isPrime.mem_or_mem h).elim s.2 ht, ?_⟩
      rw [Submodule.coe_smul, ← has, mul_smul, smul_comm t, mk'_smul]
      exact Submodule.smul_mem_smul ha htb
    have hsum : x ∈ localization₂ w.asIdeal (w.asIdeal • N) := by
      have h1 : x = ((∑ i, b.repr ⟨x, hx'⟩ i • b i : atW w N) : V) := by rw [b.sum_repr]
      rw [h1, Submodule.coe_sum]
      exact Submodule.sum_mem _ fun i _ => hterm i
    obtain ⟨s, hs, hsx⟩ := hsum
    exact mem_smul_of_smul_mem w hs hx hsx

structure LinOn (w : HeightOneSpectrum (𝓞 K)) (N : Submodule (𝓞 K) V) {A : Type} [AddCommGroup A]
    [Module (𝓞 K ⧸ w.asIdeal) A] (g : V → A) : Prop where
  add : ∀ x ∈ N, ∀ y ∈ N, g (x + y) = g x + g y
  smul : ∀ (a : 𝓞 K), ∀ x ∈ N, g (a • x) = Ideal.Quotient.mk w.asIdeal a • g x

namespace LinOn

variable {w : HeightOneSpectrum (𝓞 K)} {N : Submodule (𝓞 K) V} {A : Type} [AddCommGroup A]
  [Module (𝓞 K ⧸ w.asIdeal) A] {g : V → A}

/- English proof (translation)
Establish `h1` using `h.add 0 N.zero_mem 0 N.zero_mem`. Rewrite `h1` using `[add_zero]`. Simplify using `using h1`.
-/
theorem zero (h : LinOn w N g) : g 0 = 0 := by
  have h1 := h.add 0 N.zero_mem 0 N.zero_mem
  rw [add_zero] at h1
  simpa using h1

/- English proof (translation)
Use `Finset.induction_on s (by simp [h.zero]) (fun a s ha ih => ?_)` and prove the remaining obligations. Rewrite using `[Finset.sum_insert ha, Finset.sum_insert ha, h.add _ (N.smul_mem _ (hy a)) _ (N.sum_mem fun i _ => N.smul_mem _ (hy i)), h.smul _ _ (hy a), ih]`.
-/
theorem sum (h : LinOn w N g) {ι : Type} (s : Finset ι) (c : ι → 𝓞 K) (y : ι → V) (hy : ∀ i, y i ∈ N) :
    g (∑ i ∈ s, c i • y i) = ∑ i ∈ s, Ideal.Quotient.mk w.asIdeal (c i) • g (y i) := by
  classical
  refine Finset.induction_on s (by simp [h.zero]) (fun a s ha ih => ?_)
  rw [Finset.sum_insert ha, Finset.sum_insert ha,
    h.add _ (N.smul_mem _ (hy a)) _ (N.sum_mem fun i _ => N.smul_mem _ (hy i)), h.smul _ _ (hy a), ih]

/- English proof (translation)
Use `Submodule.smul_induction_on' hx (fun a ha n hn => ?_) (fun x hx y hy h1 h2 => ?_)` and prove the remaining obligations. Rewrite using `[h.smul a n hn, (Ideal.Quotient.eq_zero_iff_mem).2 ha, zero_smul]`. Rewrite using `[h.add x (Submodule.smul_le_right hx) y (Submodule.smul_le_right hy), h1, h2, add_zero]`.
-/
theorem kills (h : LinOn w N g) {x : V} (hx : x ∈ w.asIdeal • N) : g x = 0 := by
  refine Submodule.smul_induction_on' hx (fun a ha n hn => ?_) (fun x hx y hy h1 h2 => ?_)
  · rw [h.smul a n hn, (Ideal.Quotient.eq_zero_iff_mem).2 ha, zero_smul]
  · rw [h.add x (Submodule.smul_le_right hx) y (Submodule.smul_le_right hy), h1, h2, add_zero]

end LinOn

/- English proof (translation)
Establish `hle : ∀ x ∈ N, x ∈ localization₂ w.asIdeal N` using `fun x hx => ⟨1, Submonoid.one_mem _, by simpa using hx⟩`. Conclude with `⟨fun x hx y hy => h.add x (hle x hx) y (hle y hy), fun a x hx => h.smul a x (hle x hx)⟩`.
-/
theorem FrameAt.linOn {w : HeightOneSpectrum (𝓞 K)} {N : Submodule (𝓞 K) V} {n : ℕ}
    {β : V → (Fin n → 𝓞 K ⧸ w.asIdeal)} (h : FrameAt w N β) : LinOn w N β := by
  have hle : ∀ x ∈ N, x ∈ localization₂ w.asIdeal N := fun x hx => ⟨1, Submonoid.one_mem _, by simpa using hx⟩
  exact ⟨fun x hx y hy => h.add x (hle x hx) y (hle y hy), fun a x hx => h.smul a x (hle x hx)⟩

/- English proof (translation)
Use `choose c hc using fun i => Ideal.Quotient.mk_surjective (β x i)`. Establish `hsumN : ∑ i, c i • y i ∈ N` using `N.sum_mem fun i _ => N.smul_mem _ (hy i)`. Establish `hzN : x - ∑ i, c i • y i ∈ N` using `N.sub_mem hx hsumN`. Establish `hβ : LinOn w N β` using `h.linOn`. Establish `hβz : β (x - ∑ i, c i • y i) = 0`.

Establish `e1` using `hβ.add _ hzN _ hsumN`. Rewrite `e1` using `[sub_add_cancel, hβ.sum Finset.univ c y hy]`. Establish `e2 : ∑ i, Ideal.Quotient.mk w.asIdeal (c i) • β (y i) = β x`. Use extensionality with `j`. Simplify using `[hβy, hc, Finset.sum_apply, Pi.single_apply]`.

Rewrite `e1` using `[e2]`. Simplify using `using e1`. Establish `hgz : g (x - ∑ i, c i • y i) = 0` using `hg.kills (h.ker _ hzN hβz)`. Establish `e3` using `hg.add _ hzN _ hsumN`. Rewrite `e3` using `[sub_add_cancel, hgz, zero_add, hg.sum Finset.univ c y hy]`.

Rewrite using `[e3]`. Simplify using `only [hc]`.
-/
theorem FrameAt.expand {w : HeightOneSpectrum (𝓞 K)} {N : Submodule (𝓞 K) V} {n : ℕ}
    {β : V → (Fin n → 𝓞 K ⧸ w.asIdeal)} (h : FrameAt w N β) {A : Type} [AddCommGroup A]
    [Module (𝓞 K ⧸ w.asIdeal) A] {g : V → A} (hg : LinOn w N g) (y : Fin n → V) (hy : ∀ i, y i ∈ N)
    (hβy : ∀ i, β (y i) = Pi.single i 1) {x : V} (hx : x ∈ N) : g x = ∑ i, β x i • g (y i) := by
  classical
  choose c hc using fun i => Ideal.Quotient.mk_surjective (β x i)
  have hsumN : ∑ i, c i • y i ∈ N := N.sum_mem fun i _ => N.smul_mem _ (hy i)
  have hzN : x - ∑ i, c i • y i ∈ N := N.sub_mem hx hsumN
  have hβ : LinOn w N β := h.linOn
  have hβz : β (x - ∑ i, c i • y i) = 0 := by
    have e1 := hβ.add _ hzN _ hsumN
    rw [sub_add_cancel, hβ.sum Finset.univ c y hy] at e1
    have e2 : ∑ i, Ideal.Quotient.mk w.asIdeal (c i) • β (y i) = β x := by
      ext j
      simp [hβy, hc, Finset.sum_apply, Pi.single_apply]
    rw [e2] at e1
    simpa using e1
  have hgz : g (x - ∑ i, c i • y i) = 0 := hg.kills (h.ker _ hzN hβz)
  have e3 := hg.add _ hzN _ hsumN
  rw [sub_add_cancel, hgz, zero_add, hg.sum Finset.univ c y hy] at e3
  rw [e3]
  simp only [hc]

end Frame

section Fibre

variable {E : Type} [Field E] [NumberField E] [StarRing E] {n : ℕ} {ST SG : Finset (HeightOneSpectrum (𝓞 E))}

def Deco.ofFrames (N : Submodule (𝓞 E) (Sp E n))
    (β : ∀ P : HeightOneSpectrum (𝓞 E), Sp E n → (Fin n → 𝓞 E ⧸ P.asIdeal))
    (φ : ∀ P : ST, Fin n → 𝓞 E ⧸ P.1.asIdeal) (h : GLG E n SG) : Deco E n ST SG where
  N := N
  f P x := φ P ⬝ᵥ β P.1 x
  be w x := (h w).1.mulVec (β w.1 x)

/- English proof (translation)
The claim follows from `hlat uni := huni f_add P x hx y hy := by show φ P ⬝ᵥ β P.1 (x + y) = _ rw [(hβ P.1).add x hx y hy, dotProduct_add] rfl f_smul P a x hx := by show φ P ⬝ᵥ β P.1 (a • x) = _ rw [(hβ P.1).smul a x hx, dotProduct_smul] rfl f_off P x hx := by show φ P ⬝ᵥ β P.1 x = _ rw [(hβ P.1).off x …`.
-/
theorem Deco.ofFrames_ok {N : Submodule (𝓞 E) (Sp E n)} (hlat : Submodule.IsLattice E N)
    (huni : IsUnimodular (hStd E n) N) {β : ∀ P : HeightOneSpectrum (𝓞 E), Sp E n → (Fin n → 𝓞 E ⧸ P.asIdeal)}
    (hβ : ∀ P, FrameAt P N (β P)) {φ : ∀ P : ST, Fin n → 𝓞 E ⧸ P.1.asIdeal} (hφ : ∀ P, φ P ≠ 0)
    (h : GLG E n SG) : (Deco.ofFrames N β φ h).Ok where
  lat := hlat
  uni := huni
  f_add P x hx y hy := by
    show φ P ⬝ᵥ β P.1 (x + y) = _
    rw [(hβ P.1).add x hx y hy, dotProduct_add]
    rfl
  f_smul P a x hx := by
    show φ P ⬝ᵥ β P.1 (a • x) = _
    rw [(hβ P.1).smul a x hx, dotProduct_smul]
    rfl
  f_off P x hx := by
    show φ P ⬝ᵥ β P.1 x = _
    rw [(hβ P.1).off x hx, dotProduct_zero]
  f_ne P := by
    obtain ⟨i, hi⟩ : ∃ i, φ P i ≠ 0 := by
      by_contra hc
      exact hφ P (funext fun i => by_contra fun hi => hc ⟨i, hi⟩)
    obtain ⟨x, hx, hxβ⟩ := (hβ P.1).surj (Pi.single i 1)
    refine ⟨x, hx, ?_⟩
    show φ P ⬝ᵥ β P.1 x ≠ 0
    rw [hxβ, dotProduct_single_one]
    exact hi
  be_add w x hx y hy := by
    show (h w).1.mulVec (β w.1 (x + y)) = _
    rw [(hβ w.1).add x hx y hy, Matrix.mulVec_add]
    rfl
  be_smul w a x hx := by
    show (h w).1.mulVec (β w.1 (a • x)) = _
    rw [(hβ w.1).smul a x hx, Matrix.mulVec_smul]
    rfl
  be_off w x hx := by
    show (h w).1.mulVec (β w.1 x) = _
    rw [(hβ w.1).off x hx, Matrix.mulVec_zero]
  be_surj w c := by
    obtain ⟨x, hx, hxβ⟩ := (hβ w.1).surj ((h w)⁻¹.1.mulVec c)
    refine ⟨x, hx, ?_⟩
    show (h w).1.mulVec (β w.1 x) = c
    rw [hxβ, Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec]
  be_ker w x hx h0 := by
    apply (hβ w.1).ker x hx
    have h1 : (h w).1.mulVec (β w.1 x) = 0 := h0
    have h2 := congrArg (fun v => (h w)⁻¹.1.mulVec v) h1
    simp only [Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec, Matrix.mulVec_zero] at h2
    exact h2

/- English proof (translation)
Use `haveI := Fintype.ofFinite α`. Simplify using `only [ne_eq]`. Rewrite using `[Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, Fintype.card_subtype_compl (fun x => x = a), Fintype.card_subtype_eq]`.
-/
theorem card_subtype_ne {α : Type} [Finite α] (a : α) : Nat.card {x : α // x ≠ a} = Nat.card α - 1 := by
  classical
  haveI := Fintype.ofFinite α
  simp only [ne_eq]
  rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, Fintype.card_subtype_compl (fun x => x = a),
    Fintype.card_subtype_eq]

/- English proof (translation)
Use `choose β hβ using fun P : HeightOneSpectrum (𝓞 E) => exists_frameAt P N hlat.fg hlat.span_eq_top (n := n) (by simp)`. Use `choose y hyN hyβ using fun (P : HeightOneSpectrum (𝓞 E)) (i : Fin n) => (hβ P).surj (Pi.single i 1)`. Set `Ψ : (∀ P : ST, {φ : Fin n → 𝓞 E ⧸ P.1.asIdeal // φ ≠ 0}) × GLG E n SG → {d : DecoSet E n ST SG // d.1.N = N}` to `fun p => ⟨⟨Deco.ofFrames N β (fun P => (p.1 P).1) p.2, Deco.ofFrames_ok hlat huni hβ (fun P => (p.1 P).2) p.2⟩, rfl⟩`. Establish `hinj : Function.Injective Ψ`. Introduce `p q hpq`.

Establish `h0 : Deco.ofFrames N β (fun P => (p.1 P).1) p.2 = Deco.ofFrames N β (fun P => (q.1 P).1) q.2` using `congrArg (fun d : {d : DecoSet E n ST SG // d.1.N = N} => d.1.1) hpq`. Use `Prod.ext ?_ ?_` and prove the remaining obligations. Use function extensionality and compare the values at `P`. Apply `Subtype.ext` to reduce the goal to its premises. Apply `dotProduct_eq` to reduce the goal to its premises.

Introduce `c`. Take `⟨x, -, hx⟩` from `(hβ P.1).surj c`. Establish `h1 : (p.1 P).1 ⬝ᵥ β P.1 x = (q.1 P).1 ⬝ᵥ β P.1 x` using `congrFun (congrFun (congrArg Deco.f h0) P) x`. Rewrite `h1` using `[hx]`. Then use the resulting hypothesis. Use function extensionality and compare the values at `w`.

Apply `Units.ext` to reduce the goal to its premises. Apply `Matrix.mulVec_injective` to reduce the goal to its premises. Use function extensionality and compare the values at `c`. Take `⟨x, -, hx⟩` from `(hβ w.1).surj c`. Establish `h1 : (p.2 w).1.mulVec (β w.1 x) = (q.2 w).1.mulVec (β w.1 x)` using `congrFun (congrFun (congrArg Deco.be h0) w) x`.

Rewrite `h1` using `[hx]`. Then use the resulting hypothesis. Establish `hsurj : Function.Surjective Ψ`. Introduce and unpack `⟨d, hd⟩`. Establish `hle : ∀ (P : HeightOneSpectrum (𝓞 E)), ∀ x ∈ N, x ∈ d.1.at P`. Introduce `P x hx`.

Conclude with `le_locP P d.1.N (hd ▸ hx)`. Establish `hf : ∀ P : ST, LinOn P.1 N (d.1.f P)` using `fun P => ⟨fun x hx y hy => d.2.f_add P x (hle _ x hx) y (hle _ y hy), fun a x hx => d.2.f_smul P a x (hle _ x hx)⟩`. Establish `hb : ∀ w : SG, LinOn w.1 N (d.1.be w)` using `fun w => ⟨fun x hx y hy => d.2.be_add w x (hle _ x hx) y (hle _ y hy), fun a x hx => d.2.be_smul w a x (hle _ x hx)⟩`. Establish `hfx : ∀ (P : ST), ∀ x ∈ N, d.1.f P x = (fun i => d.1.f P (y P.1 i)) ⬝ᵥ β P.1 x`. Introduce `P x hx`.

Rewrite using `[(hβ P.1).expand (hf P) (y P.1) (hyN P.1) (hyβ P.1) hx]`. Conclude with `Finset.sum_congr rfl fun i _ => mul_comm _ _`. Establish `hbx : ∀ (w : SG), ∀ x ∈ N, d.1.be w x = (Matrix.of fun a i => d.1.be w (y w.1 i) a).mulVec (β w.1 x)`. Introduce `w x hx`. Rewrite using `[(hβ w.1).expand (hb w) (y w.1) (hyN w.1) (hyβ w.1) hx]`.

Use function extensionality and compare the values at `a`. Rewrite using `[Finset.sum_apply]`. Conclude with `Finset.sum_congr rfl fun i _ => mul_comm _ _`. Establish `hφ : ∀ P : ST, (fun i => d.1.f P (y P.1 i)) ≠ 0`. Introduce `P h0`.

Take `⟨x, hx, hne⟩` from `d.2.f_ne P`. Apply `hne` to reduce the goal to its premises. Rewrite using `[hfx P x (hd ▸ hx), h0, zero_dotProduct]`. Establish `hu : ∀ w : SG, IsUnit (Matrix.of fun a i => d.1.be w (y w.1 i) a)`. Introduce `w`.

Rewrite using `[← Matrix.mulVec_surjective_iff_isUnit]`. Introduce `c`. Take `⟨x, hx, hxc⟩` from `d.2.be_surj w c`. Conclude with `⟨β w.1 x, by rw [← hbx w x (hd ▸ hx), hxc]⟩`. Use `⟨(fun P => ⟨_, hφ P⟩, fun w => (hu w).unit), ?_⟩` and prove the remaining obligations.

Apply `Subtype.ext` to reduce the goal to its premises. Apply `Subtype.ext` to reduce the goal to its premises. Use `Deco.Ok.ext_on (Deco.ofFrames_ok hlat huni hβ hφ _) d.2 hd.symm ?_ ?_` and prove the remaining obligations. Introduce `P x hx`. Conclude with `(hfx P x hx).symm`.

Introduce `w x hx`. Conclude with `(hbx w x hx).symm`. Rewrite using `[← Nat.card_congr (Equiv.ofBijective Ψ ⟨hinj, hsurj⟩), Nat.card_prod, Nat.card_pi, Nat.card_pi]`. Use `congr 1`. Use `Finset.prod_congr rfl fun P _ => ?_` and prove the remaining obligations.

Rewrite using `[card_subtype_ne, Nat.card_fun, Nat.card_fin]`.
-/
theorem card_deco_fibre (N : Submodule (𝓞 E) (Sp E n)) (hlat : Submodule.IsLattice E N)
    (huni : IsUnimodular (hStd E n) N) :
    Nat.card {d : DecoSet E n ST SG // d.1.N = N} =
      (∏ P : ST, (Nat.card (𝓞 E ⧸ P.1.asIdeal) ^ n - 1)) * ∏ w : SG, Nat.card (GL (Fin n) (𝓞 E ⧸ w.1.asIdeal)) := by
  classical
  choose β hβ using fun P : HeightOneSpectrum (𝓞 E) =>
    exists_frameAt P N hlat.fg hlat.span_eq_top (n := n) (by simp)
  choose y hyN hyβ using fun (P : HeightOneSpectrum (𝓞 E)) (i : Fin n) => (hβ P).surj (Pi.single i 1)
  let Ψ : (∀ P : ST, {φ : Fin n → 𝓞 E ⧸ P.1.asIdeal // φ ≠ 0}) × GLG E n SG → {d : DecoSet E n ST SG // d.1.N = N} :=
    fun p => ⟨⟨Deco.ofFrames N β (fun P => (p.1 P).1) p.2, Deco.ofFrames_ok hlat huni hβ (fun P => (p.1 P).2) p.2⟩, rfl⟩
  have hinj : Function.Injective Ψ := by
    intro p q hpq
    have h0 : Deco.ofFrames N β (fun P => (p.1 P).1) p.2 = Deco.ofFrames N β (fun P => (q.1 P).1) q.2 :=
      congrArg (fun d : {d : DecoSet E n ST SG // d.1.N = N} => d.1.1) hpq
    refine Prod.ext ?_ ?_
    · funext P
      apply Subtype.ext
      apply dotProduct_eq
      intro c
      obtain ⟨x, -, hx⟩ := (hβ P.1).surj c
      have h1 : (p.1 P).1 ⬝ᵥ β P.1 x = (q.1 P).1 ⬝ᵥ β P.1 x := congrFun (congrFun (congrArg Deco.f h0) P) x
      rwa [hx] at h1
    · funext w
      apply Units.ext
      apply Matrix.mulVec_injective
      funext c
      obtain ⟨x, -, hx⟩ := (hβ w.1).surj c
      have h1 : (p.2 w).1.mulVec (β w.1 x) = (q.2 w).1.mulVec (β w.1 x) :=
        congrFun (congrFun (congrArg Deco.be h0) w) x
      rwa [hx] at h1
  have hsurj : Function.Surjective Ψ := by
    rintro ⟨d, hd⟩
    have hle : ∀ (P : HeightOneSpectrum (𝓞 E)), ∀ x ∈ N, x ∈ d.1.at P := by
      intro P x hx
      exact le_locP P d.1.N (hd ▸ hx)
    have hf : ∀ P : ST, LinOn P.1 N (d.1.f P) := fun P =>
      ⟨fun x hx y hy => d.2.f_add P x (hle _ x hx) y (hle _ y hy), fun a x hx => d.2.f_smul P a x (hle _ x hx)⟩
    have hb : ∀ w : SG, LinOn w.1 N (d.1.be w) := fun w =>
      ⟨fun x hx y hy => d.2.be_add w x (hle _ x hx) y (hle _ y hy), fun a x hx => d.2.be_smul w a x (hle _ x hx)⟩
    have hfx : ∀ (P : ST), ∀ x ∈ N, d.1.f P x = (fun i => d.1.f P (y P.1 i)) ⬝ᵥ β P.1 x := by
      intro P x hx
      rw [(hβ P.1).expand (hf P) (y P.1) (hyN P.1) (hyβ P.1) hx]
      exact Finset.sum_congr rfl fun i _ => mul_comm _ _
    have hbx : ∀ (w : SG), ∀ x ∈ N,
        d.1.be w x = (Matrix.of fun a i => d.1.be w (y w.1 i) a).mulVec (β w.1 x) := by
      intro w x hx
      rw [(hβ w.1).expand (hb w) (y w.1) (hyN w.1) (hyβ w.1) hx]
      funext a
      rw [Finset.sum_apply]
      exact Finset.sum_congr rfl fun i _ => mul_comm _ _
    have hφ : ∀ P : ST, (fun i => d.1.f P (y P.1 i)) ≠ 0 := by
      intro P h0
      obtain ⟨x, hx, hne⟩ := d.2.f_ne P
      apply hne
      rw [hfx P x (hd ▸ hx), h0, zero_dotProduct]
    have hu : ∀ w : SG, IsUnit (Matrix.of fun a i => d.1.be w (y w.1 i) a) := by
      intro w
      rw [← Matrix.mulVec_surjective_iff_isUnit]
      intro c
      obtain ⟨x, hx, hxc⟩ := d.2.be_surj w c
      exact ⟨β w.1 x, by rw [← hbx w x (hd ▸ hx), hxc]⟩
    refine ⟨(fun P => ⟨_, hφ P⟩, fun w => (hu w).unit), ?_⟩
    apply Subtype.ext
    apply Subtype.ext
    refine Deco.Ok.ext_on (Deco.ofFrames_ok hlat huni hβ hφ _) d.2 hd.symm ?_ ?_
    · intro P x hx
      exact (hfx P x hx).symm
    · intro w x hx
      exact (hbx w x hx).symm
  rw [← Nat.card_congr (Equiv.ofBijective Ψ ⟨hinj, hsurj⟩), Nat.card_prod, Nat.card_pi, Nat.card_pi]
  congr 1
  refine Finset.prod_congr rfl fun P _ => ?_
  rw [card_subtype_ne, Nat.card_fun, Nat.card_fin]

end Fibre

section Abstract

/- English proof (translation)
Use `haveI := Fintype.ofFinite Γ`. Use `haveI := Fintype.ofFinite Y`. Use `haveI : Fintype (MulAction.orbitRel.Quotient Γ Y) := Fintype.ofFinite _`. Establish `hB` using `MulAction.sum_card_fixedBy_eq_card_orbits_mul_card_group Γ Y`. Establish `hfix : ∀ g : Γ, g ≠ 1 → Fintype.card (MulAction.fixedBy Y g) = 0`.

Introduce `g hg`. Rewrite using `[Fintype.card_eq_zero_iff]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨y, hy⟩`. Apply `hg` to reduce the goal to its premises.

Establish `h1 : g ∈ MulAction.stabilizer Γ y` using `hy`. Rewrite `h1` using `[hfree y]`. Conclude with `h1`. Establish `hsum : ∑ g : Γ, Fintype.card (MulAction.fixedBy Y g) = Fintype.card Y`. Rewrite using `[Finset.sum_eq_single (1 : Γ)]`.

Conclude with `Fintype.card_congr (Equiv.subtypeUnivEquiv fun y => one_smul Γ y)`. Introduce `g _ hg`. Conclude with `hfix g hg`. Introduce `h`. Conclude with `absurd (Finset.mem_univ _) h`.

Rewrite `hB` using `[hsum]`. Establish `hΓ : (Fintype.card Γ : ℝ) ≠ 0` using `by exact_mod_cast Fintype.card_ne_zero`. Rewrite using `[Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, hB]`. Use `push_cast`. Clear the denominators using the available nonvanishing facts.
-/
theorem card_orbits_free (Γ Y : Type) [Group Γ] [Finite Γ] [Finite Y] [MulAction Γ Y]
    (hfree : ∀ y : Y, MulAction.stabilizer Γ y = ⊥) :
    (Nat.card (MulAction.orbitRel.Quotient Γ Y) : ℝ) = ((Nat.card Γ : ℕ) : ℝ)⁻¹ * (Nat.card Y : ℕ) := by
  classical
  haveI := Fintype.ofFinite Γ
  haveI := Fintype.ofFinite Y
  haveI : Fintype (MulAction.orbitRel.Quotient Γ Y) := Fintype.ofFinite _
  have hB := MulAction.sum_card_fixedBy_eq_card_orbits_mul_card_group Γ Y
  have hfix : ∀ g : Γ, g ≠ 1 → Fintype.card (MulAction.fixedBy Y g) = 0 := by
    intro g hg
    rw [Fintype.card_eq_zero_iff]
    constructor
    rintro ⟨y, hy⟩
    apply hg
    have h1 : g ∈ MulAction.stabilizer Γ y := hy
    rw [hfree y] at h1
    exact h1
  have hsum : ∑ g : Γ, Fintype.card (MulAction.fixedBy Y g) = Fintype.card Y := by
    rw [Finset.sum_eq_single (1 : Γ)]
    · exact Fintype.card_congr (Equiv.subtypeUnivEquiv fun y => one_smul Γ y)
    · intro g _ hg
      exact hfix g hg
    · intro h
      exact absurd (Finset.mem_univ _) h
  rw [hsum] at hB
  have hΓ : (Fintype.card Γ : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, hB]
  push_cast
  field_simp

variable {A H D D₀ : Type} [Group A] [Group H] [MulAction (A × H) D] [MulAction A D₀]

/- English proof (translation)
Set `_ : MulAction (A × H) D₀` to `MulAction.compHom D₀ (MonoidHom.fst A H)`. Establish `hsm : ∀ (g : A × H) (x : D₀), g • x = g.1 • x` using `fun _ _ => rfl`. Set `e : MulAction.orbitRel.Quotient (A × H) D₀ ≃ MulAction.orbitRel.Quotient A D₀` to `Quotient.congrRight (r := MulAction.orbitRel (A × H) D₀) (r' := MulAction.orbitRel A D₀) (by`. Introduce `a b`. Prove the components needed by the constructor for the conclusion.

Introduce and unpack `⟨g, hg⟩`. Conclude with `⟨g.1, hg⟩`. Introduce and unpack `⟨g, hg⟩`. Conclude with `⟨(g, 1), hg⟩)`. Establish `he : ∀ x : D₀, e (Quotient.mk'' x) = Quotient.mk'' x` using `fun _ => rfl`.

Establish `hfinq : Finite (MulAction.orbitRel.Quotient (A × H) D₀)` using `Finite.of_equiv _ e.symm`. Set `_ : Fintype (MulAction.orbitRel.Quotient (A × H) D₀)` to `Fintype.ofFinite _`. Set `_ : Fintype (MulAction.orbitRel.Quotient A D₀)` to `Fintype.ofFinite _`. Establish `hrep' : ∀ c : MulAction.orbitRel.Quotient (A × H) D₀, (Quotient.mk'' (rep (e c)) : MulAction.orbitRel.Quotient (A × H) D₀) = c`. Introduce `c`.

Apply `e.injective` to reduce the goal to its premises. Rewrite using `[he, hrep]`. Establish `hst : ∀ x : D₀, Nat.card (MulAction.stabilizer (A × H) x) = Nat.card (MulAction.stabilizer A x) * Nat.card H`. Introduce `x`. Rewrite using `[← Nat.card_prod]`.

Conclude with `Nat.card_congr { toFun := fun g => (⟨g.1.1, g.2⟩, g.1.2) invFun := fun p => ⟨(p.1.1, p.2), p.1.2⟩ left_inv := fun _ => rfl right_inv := fun _ => rfl }`. Establish `hstf : ∀ x : D₀, Finite (MulAction.stabilizer (A × H) x)`. Introduce `x`. Use `hstab x` as an intermediate fact. Use `Nat.finite_of_card_ne_zero ?_` and prove the remaining obligations.

Rewrite using `[hst]`. Conclude with `Nat.mul_ne_zero Nat.card_pos.ne' Nat.card_pos.ne'`. Establish `hfc : ∀ x : D₀, Nat.card (fibre pr hpr x) = F` using `fun x => hF x`. Establish `hff : ∀ x : D₀, Finite (fibre pr hpr x)` using `fun x => hfin x`. Establish `hone : ∀ c : MulAction.orbitRel.Quotient (A × H) D₀, (Nat.card (MulAction.orbitRel.Quotient (MulAction.stabilizer (A × H) (rep (e c))) (fibre pr hpr (rep (e c)))) : ℝ) = ((Nat.card (MulAction.stabilizer A (rep (e c))) : ℕ) : ℝ)⁻¹ * ((F : ℝ) / (Nat.card H : ℕ))`.

Introduce `c`. Use `hstf (rep (e c))` as an intermediate fact. Use `hff (rep (e c))` as an intermediate fact. Rewrite using `[card_orbits_free _ _ ?_, hst, hfc]`. Use `push_cast`.

Rewrite using `[mul_inv, div_eq_mul_inv]`. Expand and normalize the polynomial expressions, which then agree. Introduce `y`. Rewrite using `[eq_bot_iff]`. Introduce `γ hγ`.

Establish `h1 : (γ : A × H) • (y : D) = (y : D)` using `congrArg Subtype.val hγ`. Conclude with `Subtype.ext (hfree _ _ h1)`. Establish `hfo : ∀ c : MulAction.orbitRel.Quotient (A × H) D₀, Finite (MulAction.orbitRel.Quotient (MulAction.stabilizer (A × H) (rep (e c))) (fibre pr hpr (rep (e c))))`. Introduce `c`. Use `hff (rep (e c))` as an intermediate fact.

Conclude with `Quotient.finite _`. Rewrite using `[← Nat.card_congr (orbitsFib pr hpr (fun c => rep (e c)) hrep'), Nat.card_sigma, Nat.cast_sum, Finset.sum_congr rfl (fun c _ => hone c), ← Finset.sum_mul, finsum_eq_sum_of_fintype]`. Use `congr 1`. Conclude with `Fintype.sum_equiv e _ _ (fun _ => rfl)`.
-/
theorem card_orbits_fibred (pr : D → D₀) (hpr : ∀ (g : A × H) (d : D), pr (g • d) = g.1 • pr d)
    [Finite (MulAction.orbitRel.Quotient A D₀)] [Finite H] (hstab : ∀ x : D₀, Finite (MulAction.stabilizer A x))
    (hfree : ∀ (g : A × H) (d : D), g • d = d → g = 1) (F : ℕ)
    (hfin : ∀ x : D₀, Finite {d : D // pr d = x}) (hF : ∀ x : D₀, Nat.card {d : D // pr d = x} = F)
    (rep : MulAction.orbitRel.Quotient A D₀ → D₀)
    (hrep : ∀ c, (Quotient.mk'' (rep c) : MulAction.orbitRel.Quotient A D₀) = c) :
    (Nat.card (MulAction.orbitRel.Quotient (A × H) D) : ℝ) =
      (∑ᶠ c : MulAction.orbitRel.Quotient A D₀, ((Nat.card (MulAction.stabilizer A (rep c)) : ℕ) : ℝ)⁻¹) *
        ((F : ℝ) / (Nat.card H : ℕ)) := by
  classical
  let _ : MulAction (A × H) D₀ := MulAction.compHom D₀ (MonoidHom.fst A H)
  have hsm : ∀ (g : A × H) (x : D₀), g • x = g.1 • x := fun _ _ => rfl
  let e : MulAction.orbitRel.Quotient (A × H) D₀ ≃ MulAction.orbitRel.Quotient A D₀ :=
    Quotient.congrRight (r := MulAction.orbitRel (A × H) D₀) (r' := MulAction.orbitRel A D₀) (by
      intro a b
      constructor
      · rintro ⟨g, hg⟩
        exact ⟨g.1, hg⟩
      · rintro ⟨g, hg⟩
        exact ⟨(g, 1), hg⟩)
  have he : ∀ x : D₀, e (Quotient.mk'' x) = Quotient.mk'' x := fun _ => rfl
  have hfinq : Finite (MulAction.orbitRel.Quotient (A × H) D₀) := Finite.of_equiv _ e.symm
  let _ : Fintype (MulAction.orbitRel.Quotient (A × H) D₀) := Fintype.ofFinite _
  let _ : Fintype (MulAction.orbitRel.Quotient A D₀) := Fintype.ofFinite _
  have hrep' : ∀ c : MulAction.orbitRel.Quotient (A × H) D₀,
      (Quotient.mk'' (rep (e c)) : MulAction.orbitRel.Quotient (A × H) D₀) = c := by
    intro c
    apply e.injective
    rw [he, hrep]
  have hst : ∀ x : D₀, Nat.card (MulAction.stabilizer (A × H) x) = Nat.card (MulAction.stabilizer A x) * Nat.card H := by
    intro x
    rw [← Nat.card_prod]
    exact Nat.card_congr
      { toFun := fun g => (⟨g.1.1, g.2⟩, g.1.2)
        invFun := fun p => ⟨(p.1.1, p.2), p.1.2⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
  have hstf : ∀ x : D₀, Finite (MulAction.stabilizer (A × H) x) := by
    intro x
    have := hstab x
    refine Nat.finite_of_card_ne_zero ?_
    rw [hst]
    exact Nat.mul_ne_zero Nat.card_pos.ne' Nat.card_pos.ne'
  have hfc : ∀ x : D₀, Nat.card (fibre pr hpr x) = F := fun x => hF x
  have hff : ∀ x : D₀, Finite (fibre pr hpr x) := fun x => hfin x
  have hone : ∀ c : MulAction.orbitRel.Quotient (A × H) D₀,
      (Nat.card (MulAction.orbitRel.Quotient (MulAction.stabilizer (A × H) (rep (e c))) (fibre pr hpr (rep (e c)))) : ℝ) =
        ((Nat.card (MulAction.stabilizer A (rep (e c))) : ℕ) : ℝ)⁻¹ * ((F : ℝ) / (Nat.card H : ℕ)) := by
    intro c
    have := hstf (rep (e c))
    have := hff (rep (e c))
    rw [card_orbits_free _ _ ?_, hst, hfc]
    · push_cast
      rw [mul_inv, div_eq_mul_inv]
      ring
    · intro y
      rw [eq_bot_iff]
      intro γ hγ
      have h1 : (γ : A × H) • (y : D) = (y : D) := congrArg Subtype.val hγ
      exact Subtype.ext (hfree _ _ h1)
  have hfo : ∀ c : MulAction.orbitRel.Quotient (A × H) D₀,
      Finite (MulAction.orbitRel.Quotient (MulAction.stabilizer (A × H) (rep (e c))) (fibre pr hpr (rep (e c)))) := by
    intro c
    have := hff (rep (e c))
    exact Quotient.finite _
  rw [← Nat.card_congr (orbitsFib pr hpr (fun c => rep (e c)) hrep'), Nat.card_sigma, Nat.cast_sum,
    Finset.sum_congr rfl (fun c _ => hone c), ← Finset.sum_mul, finsum_eq_sum_of_fintype]
  congr 1
  exact Fintype.sum_equiv e _ _ (fun _ => rfl)

end Abstract

section Mass

variable (E : Type) [Field E] [NumberField E] [StarRing E] (n : ℕ)

abbrev UniLat : Type :=
  {N : Submodule (𝓞 E) (Sp E n) // Submodule.IsLattice E N ∧ IsUnimodular (hStd E n) N}

variable {E n}

/- English proof (translation)
Unfold `IsUnimodular at *`. Rewrite using `[dual_gmap g hg, hN]`.
-/
theorem gmap_unimodular {g : Sp E n ≃ₗ[E] Sp E n} (hg : g ∈ UF E n) {N : Submodule (𝓞 E) (Sp E n)}
    (hN : IsUnimodular (hStd E n) N) : IsUnimodular (hStd E n) (gmap g N) := by
  unfold IsUnimodular at *
  rw [dual_gmap g hg, hN]

instance : MulAction (UF E n) (UniLat E n) where
  smul g N := ⟨gmap g.1 N.1, gmap_lattice g.1 N.1 N.2.1, gmap_unimodular g.2 N.2.2⟩
  one_smul N := Subtype.ext (Submodule.map_id N.1)
  mul_smul a b N := Subtype.ext (by
    change N.1.map _ = (N.1.map _).map _
    rw [← Submodule.map_comp]
    rfl)

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem UniLat.smul_val (g : UF E n) (N : UniLat E n) : (g • N).1 = gmap g.1 N.1 := rfl

variable (E n)

abbrev UniCl : Type := MulAction.orbitRel.Quotient (UF E n) (UniLat E n)

abbrev autU (N : UniLat E n) : Subgroup (UF E n) := MulAction.stabilizer (UF E n) N

def massC : ℝ := ∑ᶠ c : UniCl E n, ((Nat.card (autU E n (Quotient.out c)) : ℕ) : ℝ)⁻¹

variable {E n}

/- English proof (translation)
Take `⟨s, hs1, hs2⟩` from `unimod_finite hE n`. Use `Finite.of_surjective (fun N : s => (Quotient.mk'' (⟨N.1, hs1 N.1 N.2⟩ : UniLat E n) : UniCl E n)) ?_` and prove the remaining obligations. Introduce `c`. Proceed by induction on `c using Quotient.inductionOn' with`. Consider the case `h M`.

Take `⟨N, hN, g, hg, hgN⟩` from `hs2 M.1 M.2.1 M.2.2`. Use `⟨⟨N, hN⟩, ?_⟩` and prove the remaining obligations. Apply `Quotient.sound'` to reduce the goal to its premises. Rewrite using `[MulAction.orbitRel_apply]`. Use `⟨(⟨g, hg⟩ : UF E n)⁻¹, ?_⟩` and prove the remaining obligations.

Establish `h1 : M = (⟨g, hg⟩ : UF E n) • (⟨N, hs1 N hN⟩ : UniLat E n)` using `Subtype.ext hgN.symm`. Rewrite using `[h1]`. Conclude with `inv_smul_smul _ _`.
-/
theorem finite_UniCl (hE : PosStar E) : Finite (UniCl E n) := by
  obtain ⟨s, hs1, hs2⟩ := unimod_finite hE n
  refine Finite.of_surjective
    (fun N : s => (Quotient.mk'' (⟨N.1, hs1 N.1 N.2⟩ : UniLat E n) : UniCl E n)) ?_
  intro c
  induction c using Quotient.inductionOn' with
  | h M =>
    obtain ⟨N, hN, g, hg, hgN⟩ := hs2 M.1 M.2.1 M.2.2
    refine ⟨⟨N, hN⟩, ?_⟩
    apply Quotient.sound'
    rw [MulAction.orbitRel_apply]
    refine ⟨(⟨g, hg⟩ : UF E n)⁻¹, ?_⟩
    have h1 : M = (⟨g, hg⟩ : UF E n) • (⟨N, hs1 N hN⟩ : UniLat E n) := Subtype.ext hgN.symm
    rw [h1]
    exact inv_smul_smul _ _

/- English proof (translation)
Establish `hA` using `final_autFinite E (Sp E n) (hStd E n) hStd_isSymm (hStd_pos hE) N.1 N.2.1`. Establish `: Finite {g : Sp E n ≃ₗ[E] Sp E n | g ∈ isom (hStd E n) ∧ gmap g N.1 = N.1}` using `hA`. Use `Finite.of_injective (fun a : autU E n N => (⟨a.1.1, a.1.2, congrArg Subtype.val a.2⟩ : {g : Sp E n ≃ₗ[E] Sp E n | g ∈ isom (hStd E n) ∧ gmap g N.1 = N.1})) ?_` and prove the remaining obligations. Introduce `a b hab`. Conclude with `Subtype.ext (Subtype.ext (show a.1.1 = b.1.1 from congrArg (fun g : {g : Sp E n ≃ₗ[E] Sp E n | g ∈ isom (hStd E n) ∧ gmap g N.1 = N.1} => g.1) hab))`.
-/
theorem finite_autU (hE : PosStar E) (N : UniLat E n) : Finite (autU E n N) := by
  have hA := final_autFinite E (Sp E n) (hStd E n) hStd_isSymm (hStd_pos hE) N.1 N.2.1
  have : Finite {g : Sp E n ≃ₗ[E] Sp E n | g ∈ isom (hStd E n) ∧ gmap g N.1 = N.1} := hA
  refine Finite.of_injective
    (fun a : autU E n N => (⟨a.1.1, a.1.2, congrArg Subtype.val a.2⟩ :
      {g : Sp E n ≃ₗ[E] Sp E n | g ∈ isom (hStd E n) ∧ gmap g N.1 = N.1})) ?_
  intro a b hab
  exact Subtype.ext (Subtype.ext (show a.1.1 = b.1.1 from
    congrArg (fun g : {g : Sp E n ≃ₗ[E] Sp E n | g ∈ isom (hStd E n) ∧ gmap g N.1 = N.1} => g.1) hab))

def UniLat.std (E : Type) [Field E] [NumberField E] [StarRing E] (n : ℕ) : UniLat E n :=
  ⟨stdLat E n, stdLat_lattice, stdLat_unimodular⟩

/- English proof (translation)
Use `finite_UniCl (n := n) hE` as an intermediate fact. Set `_ : Fintype (UniCl E n)` to `Fintype.ofFinite _`. Unfold `massC`. Rewrite using `[finsum_eq_sum_of_fintype]`. Establish `: Nonempty (UniCl E n)` using `⟨Quotient.mk'' (UniLat.std E n)⟩`.

Use `Finset.sum_pos (fun c _ => ?_) Finset.univ_nonempty` and prove the remaining obligations. Use `finite_autU hE (Quotient.out c)` as an intermediate fact. Conclude with `inv_pos.mpr (by exact_mod_cast Nat.card_pos)`.
-/
theorem massC_pos (hE : PosStar E) : 0 < massC E n := by
  classical
  have := finite_UniCl (n := n) hE
  let _ : Fintype (UniCl E n) := Fintype.ofFinite _
  unfold massC
  rw [finsum_eq_sum_of_fintype]
  have : Nonempty (UniCl E n) := ⟨Quotient.mk'' (UniLat.std E n)⟩
  refine Finset.sum_pos (fun c _ => ?_) Finset.univ_nonempty
  have := finite_autU hE (Quotient.out c)
  exact inv_pos.mpr (by exact_mod_cast Nat.card_pos)

end Mass

section MassGenus

variable {E : Type} [Field E] [NumberField E] [StarRing E] {n : ℕ}

end MassGenus

section Count

variable {E : Type} [Field E] [NumberField E] [StarRing E] {n : ℕ} {ST SG : Finset (HeightOneSpectrum (𝓞 E))}

def DecoSet.lat (d : DecoSet E n ST SG) : UniLat E n := ⟨d.1.N, d.2.lat, d.2.uni⟩

variable (E n ST SG) in

def decoCard : ℕ :=
  (∏ P : ST, (Nat.card (𝓞 E ⧸ P.1.asIdeal) ^ n - 1)) * ∏ w : SG, Nat.card (GL (Fin n) (𝓞 E ⧸ w.1.asIdeal))

/- English proof (translation)
Rewrite using `[decoCard, ← card_deco_fibre (ST := ST) (SG := SG) N.1 N.2.1 N.2.2]`. Conclude with `Nat.card_congr (Equiv.subtypeEquivRight fun d => ⟨fun h => congrArg Subtype.val h, fun h => Subtype.ext h⟩)`.
-/
theorem fibreCard (N : UniLat E n) : Nat.card {d : DecoSet E n ST SG // d.lat = N} = decoCard E n ST SG := by
  rw [decoCard, ← card_deco_fibre (ST := ST) (SG := SG) N.1 N.2.1 N.2.2]
  exact Nat.card_congr (Equiv.subtypeEquivRight fun d => ⟨fun h => congrArg Subtype.val h, fun h => Subtype.ext h⟩)

/- English proof (translation)
Establish `h` using `DecoSet.finite_fibre (ST := ST) (SG := SG) N.1 N.2.1.fg`. Establish `: Finite {d : DecoSet E n ST SG | d.1.N = N.1}` using `h`. Use `Finite.of_injective (fun d : {d : DecoSet E n ST SG // d.lat = N} => (⟨d.1, congrArg Subtype.val d.2⟩ : {d : DecoSet E n ST SG | d.1.N = N.1})) ?_` and prove the remaining obligations. Introduce `a b hab`. Conclude with `Subtype.ext (congrArg (fun d : {d : DecoSet E n ST SG | d.1.N = N.1} => d.1) hab)`.
-/
theorem DecoSet.finite_lat_fibre (N : UniLat E n) : Finite {d : DecoSet E n ST SG // d.lat = N} := by
  have h := DecoSet.finite_fibre (ST := ST) (SG := SG) N.1 N.2.1.fg
  have : Finite {d : DecoSet E n ST SG | d.1.N = N.1} := h
  refine Finite.of_injective
    (fun d : {d : DecoSet E n ST SG // d.lat = N} =>
      (⟨d.1, congrArg Subtype.val d.2⟩ : {d : DecoSet E n ST SG | d.1.N = N.1})) ?_
  intro a b hab
  exact Subtype.ext (congrArg (fun d : {d : DecoSet E n ST SG | d.1.N = N.1} => d.1) hab)

end Count

section Idx

variable {E K : Type} [Field E] [NumberField E] [Field K] {n : ℕ} {SG : Finset (HeightOneSpectrum (𝓞 E))}
  (Λ : LevFam E K n SG)

def LevFam.idx : ℕ := ∏ w : SG, (Λ w).H.index

/- English proof (translation)
Set `e : ↥Λ.grp ≃ ∀ w : SG, ↥(Λ w).H` to `{ toFun := fun x w => ⟨x.1 w, x.2 w (Set.mem_univ w)⟩ invFun := fun f => ⟨fun w => (f w).1, fun w _ => (f w).2⟩ left_inv := fun x => rfl right_inv := fun f => rfl }`. Rewrite using `[Nat.card_congr e, Nat.card_pi]`.
-/
theorem LevFam.card_grp : Nat.card ↥Λ.grp = ∏ w : SG, Nat.card ↥(Λ w).H := by
  let e : ↥Λ.grp ≃ ∀ w : SG, ↥(Λ w).H :=
    { toFun := fun x w => ⟨x.1 w, x.2 w (Set.mem_univ w)⟩
      invFun := fun f => ⟨fun w => (f w).1, fun w _ => (f w).2⟩
      left_inv := fun x => rfl
      right_inv := fun f => rfl }
  rw [Nat.card_congr e, Nat.card_pi]

/- English proof (translation)
Rewrite using `[LevFam.idx, LevFam.card_grp, ← Finset.prod_mul_distrib]`. Conclude with `Finset.prod_congr rfl fun w _ => (Λ w).H.index_mul_card`.
-/
theorem LevFam.idx_mul_card :
    Λ.idx * Nat.card ↥Λ.grp = ∏ w : SG, Nat.card (GL (Fin n) (𝓞 E ⧸ w.1.asIdeal)) := by
  rw [LevFam.idx, LevFam.card_grp, ← Finset.prod_mul_distrib]
  exact Finset.prod_congr rfl fun w _ => (Λ w).H.index_mul_card

/- English proof (translation)
Unfold `LevFam.idx`. Conclude with `Finset.prod_pos fun w _ => Nat.pos_of_ne_zero (Subgroup.index_ne_zero_of_finite)`.
-/
theorem LevFam.idx_pos : 0 < Λ.idx := by
  unfold LevFam.idx
  exact Finset.prod_pos fun w _ => Nat.pos_of_ne_zero (Subgroup.index_ne_zero_of_finite)

end Idx

section FormCount

variable {X : Fields} {n : ℕ} {ST SG : Finset (HeightOneSpectrum (𝓞 X.E))}
  (C : CoefPk X n (DecoSet X.E n ST SG)) (Λ : LevFam X.E X.K n SG)

/- English proof (translation)
Establish `hc : (Nat.card ↥Λ.grp : ℝ) ≠ 0` using `by exact_mod_cast Nat.card_pos.ne'`. Unfold `decoCard`. Rewrite using `[← Λ.idx_mul_card]`. Use `push_cast`. Clear the denominators using the available nonvanishing facts.

Rewrite using `[mul_comm]`. Use `congr 1`. Use `Finset.prod_congr rfl fun P _ => ?_` and prove the remaining obligations. Establish `h1 : 1 ≤ Nat.card (𝓞 X.E ⧸ P.1.asIdeal) ^ n` using `Nat.one_le_pow _ _ Nat.card_pos`. Move the coercions through the operations in `[Nat.cast_sub h1]`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem decoCard_div :
    ((decoCard X.E n ST SG : ℕ) : ℝ) / (Nat.card ↥Λ.grp : ℕ) =
      (Λ.idx : ℝ) * ∏ P : ST, ((Nat.card (𝓞 X.E ⧸ P.1.asIdeal) : ℝ) ^ n - 1) := by
  have hc : (Nat.card ↥Λ.grp : ℝ) ≠ 0 := by exact_mod_cast Nat.card_pos.ne'
  unfold decoCard
  rw [← Λ.idx_mul_card]
  push_cast
  field_simp
  rw [mul_comm]
  congr 1
  refine Finset.prod_congr rfl fun P _ => ?_
  have h1 : 1 ≤ Nat.card (𝓞 X.E ⧸ P.1.asIdeal) ^ n := Nat.one_le_pow _ _ Nat.card_pos
  push_cast [Nat.cast_sub h1]
  ring

/- English proof (translation)
Establish `hE : PosStar X.E` using `posStar_of_conj hX.conjE`. Use `finite_UniCl (n := n) hE` as an intermediate fact. Establish `hfinG : Finite (GLG X.E n SG)` using `inferInstance`. Establish `hfinH : Finite ↥Λ.grp` using `inferInstance`. Set `_ : MulAction (UF X.E n × ↥Λ.grp) (DecoSet X.E n ST SG)` to `MulAction.compHom _ (FormG.incl Λ)`.

Establish `h` using `card_orbits_fibred (A := UF X.E n) (H := ↥Λ.grp) (D := DecoSet X.E n ST SG) (D₀ := UniLat X.E n) DecoSet.lat (fun _ _ => rfl) (finite_autU hE) (fun g d hg => hfree d g hg) (decoCard X.E n ST SG) DecoSet.finite_lat_fibre fibreCard Quotient.out (fun c => Quotient.out_eq' c)`. Rewrite using `[mul_assoc, ← decoCard_div Λ]`. Conclude with `h`.
-/
theorem card_formCl (hX : X.Ok) (hfree : (formGSD C Λ).Free) :
    (Nat.card (formGSD C Λ).Cl : ℝ) =
      massC X.E n * (Λ.idx : ℝ) * ∏ P : ST, ((Nat.card (𝓞 X.E ⧸ P.1.asIdeal) : ℝ) ^ n - 1) := by
  have hE : PosStar X.E := posStar_of_conj hX.conjE
  have := finite_UniCl (n := n) hE
  have hfinG : Finite (GLG X.E n SG) := inferInstance
  have hfinH : Finite ↥Λ.grp := inferInstance
  let _ : MulAction (UF X.E n × ↥Λ.grp) (DecoSet X.E n ST SG) := MulAction.compHom _ (FormG.incl Λ)
  have h := card_orbits_fibred (A := UF X.E n) (H := ↥Λ.grp) (D := DecoSet X.E n ST SG) (D₀ := UniLat X.E n)
    DecoSet.lat (fun _ _ => rfl) (finite_autU hE) (fun g d hg => hfree d g hg) (decoCard X.E n ST SG)
    DecoSet.finite_lat_fibre fibreCard Quotient.out (fun c => Quotient.out_eq' c)
  rw [mul_assoc, ← decoCard_div Λ]
  exact h

end FormCount

section IdxQ

def idxQ (q n e : ℕ) : ℕ := (∏ i : Fin n, (q ^ n - q ^ (i : ℕ))) / q ^ e

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem card_res {E : Type} [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E)) :
    Nat.card (𝓞 E ⧸ w.asIdeal) = Ideal.absNorm w.asIdeal := rfl

end IdxQ

section Cols

variable {X : Fields} {Pr : Primes X} {R : Ranks}

/- English proof (translation)
Simplify using `[Ranks.N]`.
-/
theorem rankN_zero (R : Ranks) : R.N 0 = R.k := by
  simp [Ranks.N]

variable (X R) in

def massk : ℝ := massC X.E (R.N 0)

def IpiC (Ch : Chars X Pr R.m) : ℕ := (colLev Ch 0).idx

variable (Pr R) in

def IsigC : ℕ := ∏ w : Pr.vGs, (HPsym (𝓞 X.E ⧸ w.1.asIdeal) R.r R.k R.rS).index

variable (W : Wts X Pr.Word R) (Ch : Chars X Pr R.m)

def dimC (u : Pr.Word) (τ : X.Tau) : ℕ := Nat.card (Formalism.GradedWeylDivisibility.ssIdx (R.N 0) (R.N 0) (W.lamTrue u 0 τ).natW)

def dstarC (u : Pr.Word) : ℝ := massk X R * (IpiC Ch : ℝ) * ∏ τ, (dimC W u τ : ℝ)

/- English proof (translation)
Rewrite using `[Module.finrank_eq_nat_card_basis (bVV X.K (W.lamTrue u 0))]`. Conclude with `Nat.card_pi`.
-/
theorem finrank_colV (u : Pr.Word) : finrank X.K (VV X.K (W.lamTrue u 0)) = ∏ τ, dimC W u τ := by
  rw [Module.finrank_eq_nat_card_basis (bVV X.K (W.lamTrue u 0))]
  exact Nat.card_pi

/- English proof (translation)
Rewrite using `[← finrank_colV]`. Conclude with `(colVal W u 0 (Pr.vT u) Pr.vGs).finrank_pos`.
-/
theorem dimC_pos (u : Pr.Word) : 0 < ∏ τ, dimC W u τ := by
  rw [← finrank_colV]
  exact (colVal W u 0 (Pr.vT u) Pr.vGs).finrank_pos

/- English proof (translation)
The claim follows from `massC_pos (posStar_of_conj hX.conjE)`.
-/
theorem massk_pos (hX : X.Ok) : 0 < massk X R := massC_pos (posStar_of_conj hX.conjE)

/- English proof (translation)
The claim follows from `LevFam.idx_pos _`.
-/
theorem IpiC_pos : 0 < IpiC Ch := LevFam.idx_pos _

/- English proof (translation)
The claim follows from `mul_pos (mul_pos (massk_pos hX) (by exact_mod_cast IpiC_pos Ch)) (by exact_mod_cast dimC_pos W u)`.
-/
theorem dstarC_pos (hX : X.Ok) (u : Pr.Word) : 0 < dstarC W Ch u :=
  mul_pos (mul_pos (massk_pos hX) (by exact_mod_cast IpiC_pos Ch)) (by exact_mod_cast dimC_pos W u)

/- English proof (translation)
Rewrite using `[card_formCl _ _ hX (colFree W Ch hX hPr hbig u)]`. Establish `h : ∀ P : Pr.vT u, ((Nat.card (𝓞 X.E ⧸ P.1.asIdeal) : ℝ) ^ (R.N 0) - 1) = (Pr.T u : ℝ) ^ R.k - 1`. Introduce `P`. Rewrite using `[card_res, hPr.vT_norm u P.1 P.2, (rankN_zero R)]`. Rewrite using `[Finset.prod_congr rfl fun P _ => h P, Finset.prod_const, Finset.card_univ, Fintype.card_coe, hPr.vT_card]`.

Both sides reduce to the same expression.
-/
theorem card_colCl (hX : X.Ok) (hPr : Pr.Ok) (hbig : 2 * X.f * R.k < Pr.g 0 - 1) (u : Pr.Word) :
    (Nat.card (colGSD W Ch u 0).Cl : ℝ) = massk X R * (IpiC Ch : ℝ) * ((Pr.T u : ℝ) ^ R.k - 1) ^ X.f := by
  rw [card_formCl _ _ hX (colFree W Ch hX hPr hbig u)]
  have h : ∀ P : Pr.vT u, ((Nat.card (𝓞 X.E ⧸ P.1.asIdeal) : ℝ) ^ (R.N 0) - 1) = (Pr.T u : ℝ) ^ R.k - 1 := by
    intro P
    rw [card_res, hPr.vT_norm u P.1 P.2, (rankN_zero R)]
  rw [Finset.prod_congr rfl fun P _ => h P, Finset.prod_const, Finset.card_univ, Fintype.card_coe, hPr.vT_card]
  rfl

/- English proof (translation)
Rewrite using `[finrank_MfV W Ch hX hPr hbig u, Nat.cast_mul, card_colCl W Ch hX hPr hbig u, finrank_colV, dstarC]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem finrank_MfV_eq (hX : X.Ok) (hPr : Pr.Ok) (hbig : 2 * X.f * R.k < Pr.g 0 - 1) (u : Pr.Word) :
    (finrank X.K (MfV W Ch u) : ℝ) = dstarC W Ch u * ((Pr.T u : ℝ) ^ R.k - 1) ^ X.f := by
  rw [finrank_MfV W Ch hX hPr hbig u, Nat.cast_mul, card_colCl W Ch hX hPr hbig u, finrank_colV, dstarC]
  push_cast
  ring

end Cols

section Inst

open Finset Formalism.LogVandermondeBounds.StandardLattice

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) (Ch : Chars X Pr R.m)

/- English proof (translation)
Establish `hf : 1 ≤ X.f`. Rewrite using `[Fields.f, hX.card_Tau]`. Conclude with `Module.finrank_pos`. Establish `hk : 1 ≤ R.k` using `le_trans hf hfk`. Establish `h2 : 2 * X.f ≤ 2 ^ R.k`.

Take `⟨j, hj⟩ : ∃ j, R.k = j + 1` from `⟨R.k - 1, by omega⟩`. Use `Nat.lt_two_pow_self (n := j)` as an intermediate fact. Rewrite using `[hj, pow_succ]`. Use linear arithmetic over natural numbers and integers. Conclude with `Formalism.HermitianLattices.GenusMassVolumes.mass_corollary X.f R.k (Pr.T u) Xu Γ Dstar (dstarC W Ch u) _ lo hi hf hk h2 (by exact_mod_cast (hPr.T_prime u).two_le) hXu hΓ hD (dstarC_pos W Ch hX u) hXD hT1 hT2 (finrank_MfV_eq W Ch hX hPr hbig u) hlo hhi`.
-/
theorem level_col (hX : X.Ok) (hPr : Pr.Ok) (hbig : 2 * X.f * R.k < Pr.g 0 - 1) (hfk : X.f ≤ R.k) (u : Pr.Word)
    (Xu Γ Dstar lo hi : ℝ) (hXu : 0 < Xu) (hΓ : 1 ≤ Γ) (hD : 0 < Dstar)
    (hXD : Xu ^ (X.f * R.k) = Dstar / dstarC W Ch u)
    (hT1 : Xu * Γ ^ (-(2 : ℝ) / ((X.f : ℝ) * R.k)) ≤ Pr.T u)
    (hT2 : (Pr.T u : ℝ) ≤ Xu * Γ ^ (-(2 : ℝ) / ((X.f : ℝ) * R.k)) * (1 + 1 / ((X.f : ℝ) * R.k)))
    (hlo : lo ≤ Real.log Xu) (hhi : Real.log Xu ≤ hi) :
    Dstar * (Γ⁻¹) ^ 2 / 2 ≤ (finrank X.K (MfV W Ch u) : ℝ) ∧
      (finrank X.K (MfV W Ch u) : ℝ) ≤ Real.exp 1 * (Dstar * (Γ⁻¹) ^ 2) ∧
      Real.log (Pr.T u) ≤ hi + Real.log 2 ∧ lo - 2 * Real.log Γ / ((X.f : ℝ) * R.k) ≤ Real.log (Pr.T u) := by
  have hf : 1 ≤ X.f := by
    rw [Fields.f, hX.card_Tau]
    exact Module.finrank_pos
  have hk : 1 ≤ R.k := le_trans hf hfk
  have h2 : 2 * X.f ≤ 2 ^ R.k := by
    obtain ⟨j, hj⟩ : ∃ j, R.k = j + 1 := ⟨R.k - 1, by omega⟩
    have := Nat.lt_two_pow_self (n := j)
    rw [hj, pow_succ]
    omega
  exact Formalism.HermitianLattices.GenusMassVolumes.mass_corollary X.f R.k (Pr.T u) Xu Γ Dstar (dstarC W Ch u) _ lo hi hf hk h2
    (by exact_mod_cast (hPr.T_prime u).two_le) hXu hΓ hD (dstarC_pos W Ch hX u) hXD hT1 hT2
    (finrank_MfV_eq W Ch hX hPr hbig u) hlo hhi

def hcSeq (u : Pr.Word) (τ : X.Tau) : ℕ → ℝ := fun i => if h : i < R.k then (((W.hc u τ).u ⟨i, h⟩ : ℚ) : ℝ) else 0

/- English proof (translation)
Unfold `vandN`. Conclude with `Finset.prod_congr rfl fun i hi => Finset.prod_congr rfl fun j hj => h i j (Finset.mem_range.1 hi) (Finset.mem_Ico.1 hj).2`.
-/
theorem vandN_congr {x y : ℕ → ℝ} {N : ℕ} (h : ∀ i j, i < N → j < N → x i - x j = y i - y j) : vandN x N = vandN y N := by
  unfold vandN
  exact Finset.prod_congr rfl fun i hi => Finset.prod_congr rfl fun j hj =>
    h i j (Finset.mem_range.1 hi) (Finset.mem_Ico.1 hj).2

/- English proof (translation)
Establish `hi' : i < R.N 0` using `by rw [(rankN_zero R)]; exact hi`. Unfold `wSeq hcSeq`. Rewrite using `[dif_pos hi', dif_pos hi]`. Establish `h1 : (((W.lamTrue u 0 τ).w ⟨i, hi'⟩ : ℤ) : ℚ) = (W.hc u τ).u ⟨i, hi⟩ - (((R.k : ℚ) - 1) / 2 - i)`. Establish `h2 : (W.lamTrue u 0 τ).w ⟨i, hi'⟩ = (Examples₂.lamOf (W.hc u τ) 0).w ⟨i, hi'⟩`.

Simplify using `[Wts.lamTrue, Wts.lamN, shiftW]`. Rewrite using `[h2, Examples₂.lamOf_eq (W.hc u τ) 0 (Nat.zero_le _), Examples₂.wtQ, dif_pos hi]`. Both sides reduce to the same expression. Establish `h3 : (((W.lamTrue u 0 τ).w ⟨i, hi'⟩ : ℤ) : ℝ) = (((W.hc u τ).u ⟨i, hi⟩ : ℚ) : ℝ) - (((R.k : ℝ) - 1) / 2 - i)`. Use `congrArg (fun q : ℚ => (q : ℝ)) h1` as an intermediate fact.

Move the coercions through the operations in `at this`. Conclude with `this`. Rewrite using `[h3]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem wSeq_lamTrue (u : Pr.Word) (τ : X.Tau) {i : ℕ} (hi : i < R.k) :
    wSeq (W.lamTrue u 0 τ) i = hcSeq W u τ i - ((R.k : ℝ) - 1) / 2 := by
  have hi' : i < R.N 0 := by rw [(rankN_zero R)]; exact hi
  unfold wSeq hcSeq
  rw [dif_pos hi', dif_pos hi]
  have h1 : (((W.lamTrue u 0 τ).w ⟨i, hi'⟩ : ℤ) : ℚ) = (W.hc u τ).u ⟨i, hi⟩ - (((R.k : ℚ) - 1) / 2 - i) := by
    have h2 : (W.lamTrue u 0 τ).w ⟨i, hi'⟩ = (Examples₂.lamOf (W.hc u τ) 0).w ⟨i, hi'⟩ := by
      simp [Wts.lamTrue, Wts.lamN, shiftW]
    rw [h2, Examples₂.lamOf_eq (W.hc u τ) 0 (Nat.zero_le _), Examples₂.wtQ, dif_pos hi]
    rfl
  have h3 : (((W.lamTrue u 0 τ).w ⟨i, hi'⟩ : ℤ) : ℝ) = (((W.hc u τ).u ⟨i, hi⟩ : ℚ) : ℝ) - (((R.k : ℝ) - 1) / 2 - i) := by
    have := congrArg (fun q : ℚ => (q : ℝ)) h1
    push_cast at this
    exact this
  rw [h3]
  ring

/- English proof (translation)
Establish `key : ∀ (x : ℕ → ℝ) (N : ℕ), N = R.k → (∀ i, i < R.k → x i = hcSeq W u τ i - ((R.k : ℝ) - 1) / 2) → dimVN x N = dimVN (hcSeq W u τ) R.k`. Introduce `x N hN hx`. Substitute `hN` using the available equality. Unfold `dimVN`. Rewrite using `[vandN_congr (y := hcSeq W u τ) fun i j hi hj => by rw [hx i hi, hx j hj]; ring]`.

Conclude with `key _ _ (rankN_zero R) fun i hi => wSeq_lamTrue W u τ hi`.
-/
theorem dimVN_lamTrue (u : Pr.Word) (τ : X.Tau) :
    dimVN (wSeq (W.lamTrue u 0 τ)) (R.N 0) = dimVN (hcSeq W u τ) R.k := by
  have key : ∀ (x : ℕ → ℝ) (N : ℕ), N = R.k → (∀ i, i < R.k → x i = hcSeq W u τ i - ((R.k : ℝ) - 1) / 2) →
      dimVN x N = dimVN (hcSeq W u τ) R.k := by
    intro x N hN hx
    subst hN
    unfold dimVN
    rw [vandN_congr (y := hcSeq W u τ) fun i j hi hj => by rw [hx i hi, hx j hj]; ring]
  exact key _ _ (rankN_zero R) fun i hi => wSeq_lamTrue W u τ hi

/- English proof (translation)
Rewrite using `[← dimVN_lamTrue]`. Conclude with `hw`.
-/
theorem dimC_eq (u : Pr.Word) (τ : X.Tau) (hw : WeylDim (W.lamTrue u 0 τ)) :
    (dimC W u τ : ℝ) = dimVN (hcSeq W u τ) R.k := by
  rw [← dimVN_lamTrue]
  exact hw

def enumSeq {α : Type} [Zero α] (e : X.Tau ≃ Fin X.f) (F : X.Tau → α) : ℕ → α :=
  fun ρ => if h : ρ < X.f then F (e.symm ⟨ρ, h⟩) else 0

/- English proof (translation)
Rewrite using `[Finset.prod_range (fun ρ => G (enumSeq e F ρ))]`. Simplify using `only [enumSeq, Fin.is_lt, dif_pos, Fin.eta]`. Conclude with `Equiv.prod_comp e.symm (fun τ => G (F τ))`.
-/
theorem prod_enumSeq {α : Type} [Zero α] (e : X.Tau ≃ Fin X.f) (F : X.Tau → α) (G : α → ℝ) :
    ∏ ρ ∈ range X.f, G (enumSeq e F ρ) = ∏ τ, G (F τ) := by
  rw [Finset.prod_range (fun ρ => G (enumSeq e F ρ))]
  simp only [enumSeq, Fin.is_lt, dif_pos, Fin.eta]
  exact Equiv.prod_comp e.symm (fun τ => G (F τ))

/- English proof (translation)
Rewrite using `[prod_enumSeq e (hcSeq W u) fun x => dimVN x R.k, dstarC]`. Conclude with `congrArg _ (prod_congr rfl fun τ _ => dimC_eq W u τ (hw τ))`.
-/
theorem dstarC_eq (u : Pr.Word) (hw : ∀ τ, WeylDim (W.lamTrue u 0 τ)) (e : X.Tau ≃ Fin X.f) :
    dstarC W Ch u = massk X R * (IpiC Ch : ℝ) * ∏ ρ ∈ range X.f, dimVN (enumSeq e (hcSeq W u) ρ) R.k := by
  rw [prod_enumSeq e (hcSeq W u) fun x => dimVN x R.k, dstarC]
  exact congrArg _ (prod_congr rfl fun τ _ => dimC_eq W u τ (hw τ))

/- English proof (translation)
Establish `h1 : 0 < dimC W u τ`. Assume the negation of the conclusion as `h0`. Establish `h2` using `dimC_pos W u`. Rewrite `h2` using `[prod_eq_zero (mem_univ τ) (Nat.eq_zero_of_not_pos h0)]`. Conclude with `lt_irrefl _ h2`.

Establish `h2 : (0 : ℝ) < dimVN (hcSeq W u τ) R.k`. Rewrite using `[← dimC_eq W u τ hw]`. Conclude with `h1` after adjusting the coercions. Unfold `dimVN at h2`. Establish `h3 : (0 : ℝ) < ∏ i ∈ range R.k, ((i.factorial : ℕ) : ℝ)` using `prod_pos fun i _ => by exact_mod_cast i.factorial_pos`.

Conclude with `(div_pos_iff_of_pos_right h3).mp h2`.
-/
theorem vandN_hcSeq_pos (u : Pr.Word) (τ : X.Tau) (hw : WeylDim (W.lamTrue u 0 τ)) : 0 < vandN (hcSeq W u τ) R.k := by
  have h1 : 0 < dimC W u τ := by
    by_contra h0
    have h2 := dimC_pos W u
    rw [prod_eq_zero (mem_univ τ) (Nat.eq_zero_of_not_pos h0)] at h2
    exact lt_irrefl _ h2
  have h2 : (0 : ℝ) < dimVN (hcSeq W u τ) R.k := by
    rw [← dimC_eq W u τ hw]
    exact_mod_cast h1
  unfold dimVN at h2
  have h3 : (0 : ℝ) < ∏ i ∈ range R.k, ((i.factorial : ℕ) : ℝ) :=
    prod_pos fun i _ => by exact_mod_cast i.factorial_pos
  exact (div_pos_iff_of_pos_right h3).mp h2

/- English proof (translation)
The claim follows from `|(1 / ((X.f : ℝ) * R.k)) * Real.log (Dstar / dstarC W Ch u) - (1 / ((X.f : ℝ) * R.k)) * Real.log (Dstar / dstarC W Ch u')| ≤ V / R.k := by have hf : 1 ≤ X.f := by rw [Fields.f, hX.card_Tau] exact Module.finrank_pos let e : X.Tau ≃ Fin X.f := Fintype.equivFin X.Tau rw [dstarC_eq W …`.
-/
theorem variation_col (hX : X.Ok) (hk : 1 ≤ R.k) (u u' : Pr.Word) (hw : ∀ τ, WeylDim (W.lamTrue u 0 τ))
    (hw' : ∀ τ, WeylDim (W.lamTrue u' 0 τ)) (Dstar V : ℝ) (hD : 0 < Dstar)
    (hV : ∀ τ, |Real.log (vandN (hcSeq W u τ) R.k) - Real.log (vandN (hcSeq W u' τ) R.k)| ≤ V) :
    |(1 / ((X.f : ℝ) * R.k)) * Real.log (Dstar / dstarC W Ch u) -
      (1 / ((X.f : ℝ) * R.k)) * Real.log (Dstar / dstarC W Ch u')| ≤ V / R.k := by
  have hf : 1 ≤ X.f := by
    rw [Fields.f, hX.card_Tau]
    exact Module.finrank_pos
  let e : X.Tau ≃ Fin X.f := Fintype.equivFin X.Tau
  rw [dstarC_eq W Ch u hw e, dstarC_eq W Ch u' hw' e]
  refine Formalism.HermitianLattices.GenusMassVolumes.joint_variation_bound X.f R.k Dstar (massk X R) (IpiC Ch) V _ _ hf hk hD (massk_pos hX)
    (by exact_mod_cast IpiC_pos Ch) ?_
  intro ρ hρ
  unfold enumSeq
  rw [dif_pos hρ, dif_pos hρ]
  exact ⟨vandN_hcSeq_pos W u _ (hw _), vandN_hcSeq_pos W u' _ (hw' _), hV _⟩

end Inst

section Rows

open Finset Formalism.LogVandermondeBounds.StandardLattice

variable {X : Fields} {Pr : Primes X} {R : Ranks}

variable (X R) in

def massr : ℝ := massC X.E R.r

/- English proof (translation)
The claim follows from `massC_pos (posStar_of_conj hX.conjE)`.
-/
theorem massr_pos (hX : X.Ok) : 0 < massr X R := massC_pos (posStar_of_conj hX.conjE)

variable (Pr R) in

def DstarC (dsig : X.Tau → ℝ) : ℝ := massr X R * (IsigC Pr R : ℝ) * ∏ τ, dsig τ

/- English proof (translation)
Use `Finset.prod_pos fun w _ => ?_` and prove the remaining obligations. Establish `: Finite (GL (Fin R.r) (𝓞 X.E ⧸ w.1.asIdeal))` using `inferInstance`. Conclude with `Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite`.
-/
theorem IsigC_pos : 0 < IsigC Pr R := by
  refine Finset.prod_pos fun w _ => ?_
  have : Finite (GL (Fin R.r) (𝓞 X.E ⧸ w.1.asIdeal)) := inferInstance
  exact Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite

/- English proof (translation)
The claim follows from `mul_pos (mul_pos (massr_pos hX) (by exact_mod_cast IsigC_pos)) (prod_pos fun τ _ => hd τ)`.
-/
theorem DstarC_pos (hX : X.Ok) {dsig : X.Tau → ℝ} (hd : ∀ τ, 0 < dsig τ) : 0 < DstarC Pr R dsig :=
  mul_pos (mul_pos (massr_pos hX) (by exact_mod_cast IsigC_pos)) (prod_pos fun τ _ => hd τ)

variable (W : Wts X Pr.Word R) (Ch : Chars X Pr R.m)

def XuC (dsig : X.Tau → ℝ) (u : Pr.Word) : ℝ :=
  (DstarC Pr R dsig / dstarC W Ch u) ^ ((1 : ℝ) / ((X.f : ℝ) * R.k))

/- English proof (translation)
The claim follows from `Real.rpow_pos_of_pos (div_pos (DstarC_pos hX hd) (dstarC_pos W Ch hX u)) _`.
-/
theorem XuC_pos (hX : X.Ok) {dsig : X.Tau → ℝ} (hd : ∀ τ, 0 < dsig τ) (u : Pr.Word) : 0 < XuC W Ch dsig u :=
  Real.rpow_pos_of_pos (div_pos (DstarC_pos hX hd) (dstarC_pos W Ch hX u)) _

/- English proof (translation)
Establish `hf : (X.f : ℝ) ≠ 0`. Establish `: 0 < X.f`. Rewrite using `[Fields.f, hX.card_Tau]`. Conclude with `Module.finrank_pos`. Conclude with `this.ne'` after adjusting the coercions.

Establish `hk : (R.k : ℝ) ≠ 0`. Use `R.m_add_three_le_k` as an intermediate fact. Conclude with `(show R.k ≠ 0 by omega)` after adjusting the coercions. Establish `hx` using `(div_pos (DstarC_pos (Pr := Pr) (R := R) hX hd) (dstarC_pos W Ch hX u)).le`. Unfold `XuC`.

Rewrite using `[← Real.rpow_natCast, ← Real.rpow_mul hx]`. Establish `: (1 : ℝ) / ((X.f : ℝ) * R.k) * ((X.f * R.k : ℕ) : ℝ) = 1`. Use `push_cast`. Clear the denominators using the available nonvanishing facts. Rewrite using `[this, Real.rpow_one]`.
-/
theorem XuC_pow (hX : X.Ok) {dsig : X.Tau → ℝ} (hd : ∀ τ, 0 < dsig τ) (u : Pr.Word) :
    XuC W Ch dsig u ^ (X.f * R.k) = DstarC Pr R dsig / dstarC W Ch u := by
  have hf : (X.f : ℝ) ≠ 0 := by
    have : 0 < X.f := by
      rw [Fields.f, hX.card_Tau]
      exact Module.finrank_pos
    exact_mod_cast this.ne'
  have hk : (R.k : ℝ) ≠ 0 := by
    have := R.m_add_three_le_k
    exact_mod_cast (show R.k ≠ 0 by omega)
  have hx := (div_pos (DstarC_pos (Pr := Pr) (R := R) hX hd) (dstarC_pos W Ch hX u)).le
  unfold XuC
  rw [← Real.rpow_natCast, ← Real.rpow_mul hx]
  have : (1 : ℝ) / ((X.f : ℝ) * R.k) * ((X.f * R.k : ℕ) : ℝ) = 1 := by
    push_cast
    field_simp
  rw [this, Real.rpow_one]

def InWindow (dsig : X.Tau → ℝ) (Γ : ℝ) (u : Pr.Word) : Prop :=
  XuC W Ch dsig u * Γ ^ (-(2 : ℝ) / ((X.f : ℝ) * R.k)) ≤ Pr.T u ∧
    (Pr.T u : ℝ) ≤ XuC W Ch dsig u * Γ ^ (-(2 : ℝ) / ((X.f : ℝ) * R.k)) * (1 + 1 / ((X.f : ℝ) * R.k))

/- English proof (translation)
The claim follows from `level_col W Ch hX hPr hbig hfk u _ Γ _ lo hi (XuC_pos W Ch hX hd u) hΓ (DstarC_pos hX hd) (XuC_pow W Ch hX hd u) hT.1 hT.2 hlo hhi`.
-/
theorem level_window_col (hX : X.Ok) (hPr : Pr.Ok) (hbig : 2 * X.f * R.k < Pr.g 0 - 1) (hfk : X.f ≤ R.k) (u : Pr.Word)
    {dsig : X.Tau → ℝ} (hd : ∀ τ, 0 < dsig τ) {Γ : ℝ} (hΓ : 1 ≤ Γ) (hT : InWindow W Ch dsig Γ u) (lo hi : ℝ)
    (hlo : lo ≤ Real.log (XuC W Ch dsig u)) (hhi : Real.log (XuC W Ch dsig u) ≤ hi) :
    DstarC Pr R dsig * (Γ⁻¹) ^ 2 / 2 ≤ (finrank X.K (MfV W Ch u) : ℝ) ∧
      (finrank X.K (MfV W Ch u) : ℝ) ≤ Real.exp 1 * (DstarC Pr R dsig * (Γ⁻¹) ^ 2) ∧
      Real.log (Pr.T u) ≤ hi + Real.log 2 ∧ lo - 2 * Real.log Γ / ((X.f : ℝ) * R.k) ≤ Real.log (Pr.T u) :=
  level_col W Ch hX hPr hbig hfk u _ Γ _ lo hi (XuC_pos W Ch hX hd u) hΓ (DstarC_pos hX hd) (XuC_pow W Ch hX hd u) hT.1 hT.2
    hlo hhi

end Rows

section WeylTest

open Finset Formalism.LogVandermondeBounds.StandardLattice Formalism.GradedWeylDivisibility

end WeylTest

section Unram

/- English proof (translation)
Use `⟨hX.ok.cplxE, hX.ok.conjE, ?_⟩` and prove the remaining obligations. Introduce `P hP`. Assume the negation of the conclusion as `hcon`. Establish `hall : ∀ θ : 𝓞 X.E, θ - X.conjO θ ∈ P`. Introduce `θ`.

Assume the negation of the conclusion as `h`. Conclude with `hcon ⟨θ, X.conjO θ, rfl, h⟩`. Establish `hq : Algebra.IsQuadraticExtension X.F X.E` using `{ finrank_eq_two' := hX.ok.rankE }`. Set `c : Gal(X.E/X.F)` to `AlgEquiv.ofRingEquiv (f := starRingAut) (fun r => hX.ok.star_F r)`. Establish `hP0 : P ≠ ⊥` using `Ring.ne_bot_of_isMaximal_of_not_isField hP (RingOfIntegers.not_isField X.E)`.

Establish `hPp : P.IsPrime` using `hP.isPrime`. Establish `hun` using `hX.unram ⟨P, hPp, hP0⟩`. Establish `hlo : P.LiesOver (P.under (𝓞 X.F))` using `⟨rfl⟩`. Establish `hp0 : P.under (𝓞 X.F) ≠ ⊥` using `Ideal.IsIntegral.comap_ne_bot (𝓞 X.F) hP0`. Establish `hcard : Nat.card (P.inertia Gal(X.E/X.F)) = 1`.

Rewrite using `[Ideal.card_inertia_eq_ramificationIdxIn (G := Gal(X.E/X.F)) (P.under (𝓞 X.F)) P, Ideal.ramificationIdxIn_eq_ramificationIdx (P.under (𝓞 X.F)) P Gal(X.E/X.F), ← Ideal.ramificationIdx'_eq_ramificationIdx (P.under (𝓞 X.F)) P hp0]`. Assume the negation of the conclusion as `h`. Conclude with `hun ((Ideal.ramificationIdx'_ne_one_iff Ideal.map_comap_le).mp h)`. Establish `hc : c ∈ P.inertia Gal(X.E/X.F)`. Introduce `x`.

Establish `h1 : c • x - x = -(x - X.conjO x)`. Rewrite using `[neg_sub]`. Both sides reduce to the same expression. Rewrite using `[h1]`. Conclude with `P.neg_mem (hall x)`.

Establish `hc1 : c = 1`. Establish `hb` using `(Subgroup.card_eq_one (H := P.inertia Gal(X.E/X.F))).mp hcard`. Rewrite `hc` using `[hb]`. Conclude with `hc`. Establish `hτ : Nonempty X.Tau`.

Rewrite using `[← Fintype.card_pos_iff, hX.ok.card_Tau]`. Conclude with `Module.finrank_pos`. Take `⟨τ⟩` from `hτ`. Apply `hX.ok.emb_ne τ τ` to reduce the goal to its premises. Use extensionality with `x`.

Establish `h2 : star x = x` using `congrArg (fun s : Gal(X.E/X.F) => s x) hc1`. Use `show X.emb τ x = X.emb τ (star x)`. Rewrite using `[h2]`.
-/
theorem cm_unramified_of_field_conditions {X : Fields} (hX : X.AbelianUnramifiedExtensionConditions) : IsCMUnram X.E := by
  refine ⟨hX.ok.cplxE, hX.ok.conjE, ?_⟩
  intro P hP
  by_contra hcon
  have hall : ∀ θ : 𝓞 X.E, θ - X.conjO θ ∈ P := by
    intro θ
    by_contra h
    exact hcon ⟨θ, X.conjO θ, rfl, h⟩
  have hq : Algebra.IsQuadraticExtension X.F X.E := { finrank_eq_two' := hX.ok.rankE }
  let c : Gal(X.E/X.F) := AlgEquiv.ofRingEquiv (f := starRingAut) (fun r => hX.ok.star_F r)
  have hP0 : P ≠ ⊥ := Ring.ne_bot_of_isMaximal_of_not_isField hP (RingOfIntegers.not_isField X.E)
  have hPp : P.IsPrime := hP.isPrime
  have hun := hX.unram ⟨P, hPp, hP0⟩
  have hlo : P.LiesOver (P.under (𝓞 X.F)) := ⟨rfl⟩
  have hp0 : P.under (𝓞 X.F) ≠ ⊥ := Ideal.IsIntegral.comap_ne_bot (𝓞 X.F) hP0
  have hcard : Nat.card (P.inertia Gal(X.E/X.F)) = 1 := by
    rw [Ideal.card_inertia_eq_ramificationIdxIn (G := Gal(X.E/X.F)) (P.under (𝓞 X.F)) P,
      Ideal.ramificationIdxIn_eq_ramificationIdx (P.under (𝓞 X.F)) P Gal(X.E/X.F),
      ← Ideal.ramificationIdx'_eq_ramificationIdx (P.under (𝓞 X.F)) P hp0]
    by_contra h
    exact hun ((Ideal.ramificationIdx'_ne_one_iff Ideal.map_comap_le).mp h)
  have hc : c ∈ P.inertia Gal(X.E/X.F) := by
    intro x
    have h1 : c • x - x = -(x - X.conjO x) := by
      rw [neg_sub]
      rfl
    rw [h1]
    exact P.neg_mem (hall x)
  have hc1 : c = 1 := by
    have hb := (Subgroup.card_eq_one (H := P.inertia Gal(X.E/X.F))).mp hcard
    rw [hb] at hc
    exact hc
  have hτ : Nonempty X.Tau := by
    rw [← Fintype.card_pos_iff, hX.ok.card_Tau]
    exact Module.finrank_pos
  obtain ⟨τ⟩ := hτ
  apply hX.ok.emb_ne τ τ
  ext x
  have h2 : star x = x := congrArg (fun s : Gal(X.E/X.F) => s x) hc1
  show X.emb τ x = X.emb τ (star x)
  rw [h2]

end Unram

section Weighted

variable {A H D D₀ : Type} [Group A] [Group H] [MulAction (A × H) D] [MulAction A D₀]

variable {X : Fields} {n : ℕ} {ST SG : Finset (HeightOneSpectrum (𝓞 X.E))}
  (C : CoefPk X n (DecoSet X.E n ST SG)) (Λ : LevFam X.E X.K n SG)

end Weighted

section Whole

/- English proof (translation)
Establish `h1` using `hS.g_big i`. Establish `hf : 1 ≤ X.f`. Rewrite using `[Fields.f, hX.card_Tau]`. Conclude with `Module.finrank_pos`. Establish `hk : 1 ≤ R.k` using `le_trans (by omega) R.m_add_three_le_k`.

Establish `h2 : 1 ≤ X.f * R.k` using `Nat.mul_pos hf hk`. Rewrite `h1` using `[mul_assoc]`. Use linear arithmetic over natural numbers and integers.
-/
theorem Sizes.three_le_g {X : Fields} {Pr : Primes X} {R : Ranks} {W : Wts X Pr.Word R} {a : ℝ} (hS : Sizes Pr W a)
    (hX : X.Ok) (i : Fin 2) : 3 ≤ Pr.g i := by
  have h1 := hS.g_big i
  have hf : 1 ≤ X.f := by
    rw [Fields.f, hX.card_Tau]
    exact Module.finrank_pos
  have hk : 1 ≤ R.k := le_trans (by omega) R.m_add_three_le_k
  have h2 : 1 ≤ X.f * R.k := Nat.mul_pos hf hk
  rw [mul_assoc] at h1
  omega

/- English proof (translation)
Rewrite using `[hD.f_eq]`. Conclude with `D.R.f_le_k`.
-/
theorem Dat.Ok.f_le_k {D : Dat} (hD : D.Ok) : D.X.f ≤ D.R.k := by
  rw [hD.f_eq]
  exact D.R.f_le_k

/- English proof (translation)
The claim follows from `finrank_MfV_eq D.W D.Ch hD.fields hD.primes (hD.sizes.g_big 0) u`.
-/
theorem Dat.Ok.finrank_MfV {D : Dat} (hD : D.Ok) (u : D.Pr.Word) :
    (finrank D.X.K (MfV D.W D.Ch u) : ℝ) = dstarC D.W D.Ch u * ((D.Pr.T u : ℝ) ^ D.R.k - 1) ^ D.X.f :=
  finrank_MfV_eq D.W D.Ch hD.fields hD.primes (hD.sizes.g_big 0) u

end Whole

end Formalism.L2.Col

import Mathlib
import Formalism.LocalRingCardinality.Lemmas
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.FormsStable
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.ExistsBranchingCoordinatesIff

noncomputable section

namespace GlobalTheory.LvT

open Formalism.BasicNotions Classical NumberField
open Formalism.MainNotions.product_first_zeroth_parts (Ow tops wsum ten blk nfAll CSpan IntSpan Nm_succ wSh cTw)

/- English proof (translation)
Establish `h1 : (1 : 𝓞 D.what₂.LL) ∉ (D.plEq w).asIdeal` using `fun h => (D.plEq w).isPrime.ne_top ((Ideal.eq_top_iff_one _).2 h)`. Unfold `locW at hx`. Proceed by induction on `hx using Submodule.span_induction with`. Consider the case `mem y hy => exact ⟨1, h1, by simpa using hy⟩`. Consider the case `zero => exact ⟨1, h1, by simp⟩`.

Consider the case `add y z _ _ hy hz`. Take `⟨d, hd, hy⟩` from `hy`. Take `⟨e, he, hz⟩` from `hz`. Use `⟨d * e, fun h => ((D.plEq w).isPrime.mem_or_mem h).elim hd he, ?_⟩` and prove the remaining obligations. Rewrite using `[smul_add]`.

Use `L.add_mem ?_ ?_` and prove the remaining obligations. Rewrite using `[mul_comm, mul_smul]`. Conclude with `L.smul_mem _ hy`. Rewrite using `[mul_smul]`. Conclude with `L.smul_mem _ hz`.

Consider the case `smul r y _ hy`. Take `⟨d, hd, hy⟩` from `hy`. Establish `hr : (D.plEq w).valuation D.what₂.LL (r : D.what₂.LL) ≤ 1` using `(D.val_nonneg_iff w r).1 r.2`. Take `⟨n, e, hne⟩` from `(D.plEq w).exists_primeCompl_mul_eq_of_integer (r : D.what₂.LL) hr`. Use `⟨d * e, fun h => ((D.plEq w).isPrime.mem_or_mem h).elim hd e.2, ?_⟩` and prove the remaining obligations.

Establish `: (d * (e : 𝓞 D.what₂.LL)) • r • y = n • d • y`. Rewrite using `[Subring.smul_def, ← algebraMap_smul D.what₂.LL (d * (e : 𝓞 D.what₂.LL)), ← algebraMap_smul D.what₂.LL n, ← algebraMap_smul D.what₂.LL d y, smul_smul, smul_smul, ← hne, map_mul]`. Use `congr 1`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[this]`.

Conclude with `L.smul_mem _ hy`.
-/
theorem exists_smul_mem_of_mem_locW (D : D7) (w : D.what₂.places.Pl) {V : Type} [AddCommGroup V] [Module D.what₂.LL V]
    [Module (𝓞 D.what₂.LL) V] [IsScalarTower (𝓞 D.what₂.LL) D.what₂.LL V] (L : Submodule (𝓞 D.what₂.LL) V) {x : V}
    (hx : x ∈ locW D.what₂.places w L) : ∃ d : 𝓞 D.what₂.LL, d ∉ (D.plEq w).asIdeal ∧ d • x ∈ L := by
  have h1 : (1 : 𝓞 D.what₂.LL) ∉ (D.plEq w).asIdeal :=
    fun h => (D.plEq w).isPrime.ne_top ((Ideal.eq_top_iff_one _).2 h)
  unfold locW at hx
  induction hx using Submodule.span_induction with
  | mem y hy => exact ⟨1, h1, by simpa using hy⟩
  | zero => exact ⟨1, h1, by simp⟩
  | add y z _ _ hy hz =>
    obtain ⟨d, hd, hy⟩ := hy
    obtain ⟨e, he, hz⟩ := hz
    refine ⟨d * e, fun h => ((D.plEq w).isPrime.mem_or_mem h).elim hd he, ?_⟩
    rw [smul_add]
    refine L.add_mem ?_ ?_
    · rw [mul_comm, mul_smul]; exact L.smul_mem _ hy
    · rw [mul_smul]; exact L.smul_mem _ hz
  | smul r y _ hy =>
    obtain ⟨d, hd, hy⟩ := hy
    have hr : (D.plEq w).valuation D.what₂.LL (r : D.what₂.LL) ≤ 1 := (D.val_nonneg_iff w r).1 r.2
    obtain ⟨n, e, hne⟩ := (D.plEq w).exists_primeCompl_mul_eq_of_integer (r : D.what₂.LL) hr
    refine ⟨d * e, fun h => ((D.plEq w).isPrime.mem_or_mem h).elim hd e.2, ?_⟩
    have : (d * (e : 𝓞 D.what₂.LL)) • r • y = n • d • y := by
      rw [Subring.smul_def, ← algebraMap_smul D.what₂.LL (d * (e : 𝓞 D.what₂.LL)), ← algebraMap_smul D.what₂.LL n,
        ← algebraMap_smul D.what₂.LL d y, smul_smul, smul_smul, ← hne, map_mul]
      congr 1; ring
    rw [this]; exact L.smul_mem _ hy

/- English proof (translation)
Set `I : Ideal (𝓞 D.what₂.LL)` to `L.comap (LinearMap.toSpanSingleton (𝓞 D.what₂.LL) V x)`. Establish `hI : I = ⊤`. Assume the negation of the conclusion as `hne`. Take `⟨M, hM, hIM⟩` from `Ideal.exists_le_maximal I hne`. Set `v : IsDedekindDomain.HeightOneSpectrum (𝓞 D.what₂.LL)` to `⟨M, hM.isPrime, Ring.ne_bot_of_isMaximal_of_not_isField hM (RingOfIntegers.not_isField _)⟩`.

Take `⟨d, hd, hdx⟩` from `exists_smul_mem_of_mem_locW D (D.plEq.symm v) L (hx _)`. Rewrite `hd` using `[Equiv.apply_symm_apply]`. Conclude with `hd (hIM (show d ∈ I from hdx))`. Establish `h1 : (1 : 𝓞 D.what₂.LL) ∈ I` using `hI ▸ Submodule.mem_top`. Simplify `h1` using `[I]`.
-/
theorem mem_of_forall_locW (D : D7) {V : Type} [AddCommGroup V] [Module D.what₂.LL V]
    [Module (𝓞 D.what₂.LL) V] [IsScalarTower (𝓞 D.what₂.LL) D.what₂.LL V] (L : Submodule (𝓞 D.what₂.LL) V) {x : V}
    (hx : ∀ w, x ∈ locW D.what₂.places w L) : x ∈ L := by
  let I : Ideal (𝓞 D.what₂.LL) := L.comap (LinearMap.toSpanSingleton (𝓞 D.what₂.LL) V x)
  have hI : I = ⊤ := by
    by_contra hne
    obtain ⟨M, hM, hIM⟩ := Ideal.exists_le_maximal I hne
    let v : IsDedekindDomain.HeightOneSpectrum (𝓞 D.what₂.LL) :=
      ⟨M, hM.isPrime, Ring.ne_bot_of_isMaximal_of_not_isField hM (RingOfIntegers.not_isField _)⟩
    obtain ⟨d, hd, hdx⟩ := exists_smul_mem_of_mem_locW D (D.plEq.symm v) L (hx _)
    rw [Equiv.apply_symm_apply] at hd
    exact hd (hIM (show d ∈ I from hdx))
  have h1 : (1 : 𝓞 D.what₂.LL) ∈ I := hI ▸ Submodule.mem_top
  simpa [I] using h1

variable {D : D7} {u : D.what₂.Word} {X : Ch D u}

end GlobalTheory.LvT

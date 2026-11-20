import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.DlogRatioVolumeFormNeZero
open GlobalTheory.PD GlobalTheory.CechDR KaehlerDifferential

namespace GlobalTheory

open KaehlerDifferential in

/- English proof (translation)
Introduce `k F K _ _ _ _ _ _ B _ W _ _ _ _ S hS hspan`. Use `set M := Submodule.span F S with hM`. Set `T : Subalgebra F K` to `{ carrier := {y | ∀ m ∈ M, y • m ∈ M} mul_mem' := fun {a b} ha hb m hm => by rw [mul_smul]; exact ha _ (hb m hm) one_mem' := fun m hm => by rwa [one_smul] add_mem' := fun {a b} ha hb m hm => by rw [add_smul]; exact M.add_mem (ha m hm) (hb m hm) zero_mem' := fun m _ => by rw [zero …`. Establish `hmemT : ∀ y : K, y ∈ T ↔ ∀ m ∈ M, y • m ∈ M` using `fun y => Iff.rfl`. Establish `hB : ∀ c ∈ B, (c : K) ∈ T`.

Introduce `c hc m hm`. Proceed by induction on `hm using Submodule.span_induction with`. Consider the case `mem s hs => exact Submodule.subset_span (hS c hc s hs)`. Consider the case `zero => rw [smul_zero]`. Conclude with `M.zero_mem`.

Consider the case `add v w _ _ hv hw => rw [smul_add]`. Conclude with `M.add_mem hv hw`. Consider the case `smul f v _ hv => rw [smul_comm]`. Conclude with `M.smul_mem f hv`. Establish `hinv : ∀ y : K, y ∈ T → y⁻¹ ∈ T`.

Introduce `y hy`. Conclude with `T.inv_mem_of_algebraic (x := ⟨y, hy⟩) (Algebra.IsAlgebraic.isAlgebraic y)`. Establish `hall : ∀ y : K, y ∈ T`. Introduce `y`. Take `⟨a, b, _, rfl⟩` from `IsFractionRing.div_surjective (A := B) y`.

Rewrite using `[div_eq_mul_inv]`. Conclude with `T.mul_mem (hB _ a.2) (hinv _ (hB _ b.2))`. Set `MK : Submodule K W` to `{ carrier := M add_mem' := M.add_mem zero_mem' := M.zero_mem smul_mem' := fun c m hm => hall c m hm }`. Establish `hle : Submodule.span K S ≤ MK` using `Submodule.span_le.mpr fun s hs => Submodule.subset_span hs`. Rewrite `hle` using `[hspan]`.

Conclude with `eq_top_iff.mpr fun w _ => hle Submodule.mem_top`.
-/
theorem _root_.GlobalTheory.span_eq_top_of_stable_of_isFractionRing :
    ∀ (k F K : Type) [Field k] [Field F] [Field K] [Algebra k K] [Algebra F K] [FiniteDimensional F K] (B : Subalgebra k K) [IsFractionRing B K] (W : Type) [AddCommGroup W] [Module K W] [Module F W] [IsScalarTower F K W] (S : Set W), (∀ c ∈ B, ∀ w ∈ S, (c : K) • w ∈ S) → Submodule.span K S = ⊤ → Submodule.span F S = ⊤ := by
  intro k F K _ _ _ _ _ _ B _ W _ _ _ _ S hS hspan
  set M := Submodule.span F S with hM
  let T : Subalgebra F K :=
    { carrier := {y | ∀ m ∈ M, y • m ∈ M}
      mul_mem' := fun {a b} ha hb m hm => by rw [mul_smul]; exact ha _ (hb m hm)
      one_mem' := fun m hm => by rwa [one_smul]
      add_mem' := fun {a b} ha hb m hm => by rw [add_smul]; exact M.add_mem (ha m hm) (hb m hm)
      zero_mem' := fun m _ => by rw [zero_smul]; exact M.zero_mem
      algebraMap_mem' := fun f m hm => by rw [algebraMap_smul]; exact M.smul_mem f hm }
  have hmemT : ∀ y : K, y ∈ T ↔ ∀ m ∈ M, y • m ∈ M := fun y => Iff.rfl
  have hB : ∀ c ∈ B, (c : K) ∈ T := by
    intro c hc m hm
    induction hm using Submodule.span_induction with
    | mem s hs => exact Submodule.subset_span (hS c hc s hs)
    | zero => rw [smul_zero]; exact M.zero_mem
    | add v w _ _ hv hw => rw [smul_add]; exact M.add_mem hv hw
    | smul f v _ hv => rw [smul_comm]; exact M.smul_mem f hv
  have hinv : ∀ y : K, y ∈ T → y⁻¹ ∈ T := by
    intro y hy
    exact T.inv_mem_of_algebraic (x := ⟨y, hy⟩) (Algebra.IsAlgebraic.isAlgebraic y)
  have hall : ∀ y : K, y ∈ T := by
    intro y
    obtain ⟨a, b, _, rfl⟩ := IsFractionRing.div_surjective (A := B) y
    rw [div_eq_mul_inv]
    exact T.mul_mem (hB _ a.2) (hinv _ (hB _ b.2))
  let MK : Submodule K W :=
    { carrier := M
      add_mem' := M.add_mem
      zero_mem' := M.zero_mem
      smul_mem' := fun c m hm => hall c m hm }
  have hle : Submodule.span K S ≤ MK := Submodule.span_le.mpr fun s hs => Submodule.subset_span hs
  rw [hspan] at hle
  exact eq_top_iff.mpr fun w _ => hle Submodule.mem_top

end GlobalTheory

import Mathlib.Topology.KrullDimension
import Mathlib.Topology.NoetherianSpace
import Mathlib.Topology.Sober

open Set Topology TopologicalSpace

namespace LateralTheory.E.CurveKrullDim

variable {X : Type} [TopologicalSpace X]

/- English proof (translation)
Set `T : IrreducibleCloseds X` to `⟨univ, IrreducibleSpace.isIrreducible_univ X, isClosed_univ⟩`. Establish `h1 : A < B`. Rewrite using `[← SetLike.coe_ssubset_coe]`. Conclude with `hAB`. Establish `h2 : B < T`.

Rewrite using `[← SetLike.coe_ssubset_coe]`. Conclude with `ssubset_univ_iff.mpr hB`. Set `l : LTSeries (IrreducibleCloseds X)` to `⟨2, ![A, B, T], fun i => by fin_cases i`. Conclude with `h1`. Conclude with `h2⟩`.

Establish `hl : l.length = 2` using `rfl`. Unfold `topologicalKrullDim`. Conclude with `Order.le_krullDim_iff.mpr ⟨l, hl⟩`.
-/
theorem two_le_dim (A B : IrreducibleCloseds X) (hAB : (A : Set X) ⊂ B) (hB : (B : Set X) ≠ univ)
    [IrreducibleSpace X] : (2 : WithBot ℕ∞) ≤ topologicalKrullDim X := by
  let T : IrreducibleCloseds X := ⟨univ, IrreducibleSpace.isIrreducible_univ X, isClosed_univ⟩
  have h1 : A < B := by
    rw [← SetLike.coe_ssubset_coe]; exact hAB
  have h2 : B < T := by
    rw [← SetLike.coe_ssubset_coe]; exact ssubset_univ_iff.mpr hB
  let l : LTSeries (IrreducibleCloseds X) := ⟨2, ![A, B, T], fun i => by
    fin_cases i
    · exact h1
    · exact h2⟩
  have hl : l.length = 2 := rfl
  unfold topologicalKrullDim
  exact Order.le_krullDim_iff.mpr ⟨l, hl⟩

/- English proof (translation)
Rewrite using `[← closure_subset_iff_isClosed]`. Introduce `y hy`. Assume the negation of the conclusion as `hne`. Establish `hyz : closure ({y} : Set X) ⊂ closure {z}`. Use `⟨closure_minimal (by simpa using hy) isClosed_closure, fun h => hne ?_⟩` and prove the remaining obligations.

Establish `h1 : z ⤳ y` using `specializes_iff_mem_closure.mpr hy`. Establish `h2 : y ⤳ z` using `specializes_iff_mem_closure.mpr (h (subset_closure rfl))`. Conclude with `(h1.antisymm h2).eq.symm`. Use `two_le_dim ⟨closure {y}, isIrreducible_singleton.closure, isClosed_closure⟩ ⟨closure {z}, isIrreducible_singleton.closure, isClosed_closure⟩ hyz hz` as an intermediate fact. Establish `h3` using `this.trans hd`.

Normalize the coercions in `at h3`.
-/
theorem closed_of_ne_univ [IrreducibleSpace X] [T0Space X] (hd : topologicalKrullDim X ≤ 1) (z : X)
    (hz : closure ({z} : Set X) ≠ univ) : IsClosed ({z} : Set X) := by
  rw [← closure_subset_iff_isClosed]
  intro y hy
  by_contra hne
  have hyz : closure ({y} : Set X) ⊂ closure {z} := by
    refine ⟨closure_minimal (by simpa using hy) isClosed_closure, fun h => hne ?_⟩
    have h1 : z ⤳ y := specializes_iff_mem_closure.mpr hy
    have h2 : y ⤳ z := specializes_iff_mem_closure.mpr (h (subset_closure rfl))
    exact (h1.antisymm h2).eq.symm
  have := two_le_dim ⟨closure {y}, isIrreducible_singleton.closure, isClosed_closure⟩
    ⟨closure {z}, isIrreducible_singleton.closure, isClosed_closure⟩ hyz hz
  have h3 := this.trans hd
  norm_cast at h3

/- English proof (translation)
Establish `hpt : ∀ z ∈ Z, IsClosed ({z} : Set X)` using `fun z hz => closed_of_ne_univ hd z (fun h => hne (eq_univ_of_univ_subset (h ▸ closure_minimal (by simpa using hz) hZ)))`. Establish `hfin` using `NoetherianSpace.finite_irreducibleComponents (α := Z)`. Establish `hsub : ∀ S ∈ irreducibleComponents Z, (Subtype.val '' S).Subsingleton`. Introduce `S hS`. Establish `hirr : IsIrreducible (Subtype.val '' S)` using `hS.1.image _ continuous_subtype_val.continuousOn`.

Take `⟨g, hg⟩` from `QuasiSober.sober hirr.closure isClosed_closure`. Establish `hgZ : g ∈ Z` using `closure_minimal (by rintro _ ⟨x, -, rfl⟩; exact x.2) hZ (hg.mem)`. Establish `: closure (Subtype.val '' S) = {g}`. Rewrite using `[← hg.def, (hpt g hgZ).closure_eq]`. Introduce `a ha b hb`.

Establish `ha'` using `subset_closure ha`. Establish `hb'` using `subset_closure hb`. Rewrite `ha'`, `hb'` using `[this]`. Conclude with `ha'.trans hb'.symm`. Establish `: Z = ⋃ S ∈ irreducibleComponents Z, Subtype.val '' S`.

Use extensionality with `x`. Prove the components needed by the constructor for the conclusion. Introduce `hx`. Establish `: (⟨x, hx⟩ : Z) ∈ ⋃₀ irreducibleComponents Z` using `by rw [sUnion_irreducibleComponents]; trivial`. Take `⟨S, hS, hxS⟩` from `this`.

Conclude with `mem_iUnion₂.mpr ⟨S, hS, ⟨_, hxS, rfl⟩⟩`. Introduce `hx`. Take `⟨S, -, y, -, rfl⟩` from `mem_iUnion₂.mp hx`. Conclude with `y.2`. Rewrite using `[this]`.

Conclude with `hfin.biUnion fun S hS => (hsub S hS).finite`.
-/
theorem finite_of_closed [IrreducibleSpace X] [T0Space X] [QuasiSober X] [NoetherianSpace X]
    (hd : topologicalKrullDim X ≤ 1) (Z : Set X) (hZ : IsClosed Z) (hne : Z ≠ univ) : Z.Finite := by
  have hpt : ∀ z ∈ Z, IsClosed ({z} : Set X) := fun z hz => closed_of_ne_univ hd z
    (fun h => hne (eq_univ_of_univ_subset (h ▸ closure_minimal (by simpa using hz) hZ)))
  have hfin := NoetherianSpace.finite_irreducibleComponents (α := Z)
  have hsub : ∀ S ∈ irreducibleComponents Z, (Subtype.val '' S).Subsingleton := by
    intro S hS
    have hirr : IsIrreducible (Subtype.val '' S) := hS.1.image _ continuous_subtype_val.continuousOn
    obtain ⟨g, hg⟩ := QuasiSober.sober hirr.closure isClosed_closure
    have hgZ : g ∈ Z := closure_minimal (by rintro _ ⟨x, -, rfl⟩; exact x.2) hZ (hg.mem)
    have : closure (Subtype.val '' S) = {g} := by
      rw [← hg.def, (hpt g hgZ).closure_eq]
    intro a ha b hb
    have ha' := subset_closure ha; have hb' := subset_closure hb
    rw [this] at ha' hb'
    exact ha'.trans hb'.symm
  have : Z = ⋃ S ∈ irreducibleComponents Z, Subtype.val '' S := by
    ext x; constructor
    · intro hx
      have : (⟨x, hx⟩ : Z) ∈ ⋃₀ irreducibleComponents Z := by rw [sUnion_irreducibleComponents]; trivial
      obtain ⟨S, hS, hxS⟩ := this
      exact mem_iUnion₂.mpr ⟨S, hS, ⟨_, hxS, rfl⟩⟩
    · intro hx
      obtain ⟨S, -, y, -, rfl⟩ := mem_iUnion₂.mp hx
      exact y.2
  rw [this]
  exact hfin.biUnion fun S hS => (hsub S hS).finite

end LateralTheory.E.CurveKrullDim

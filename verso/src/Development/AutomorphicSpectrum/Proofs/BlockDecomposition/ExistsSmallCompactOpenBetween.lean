import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsBump
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsCIndValue

open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.BZPhiPG GlobalTheory.CompanionTheory.BZPhiPG.OntoO Topology
open scoped TensorProduct

namespace GlobalTheory.CompanionTheory.BZPhiPG.OntoO

/- English proof (translation)
Take `⟨K₆, hK₆o, -, hK₆s⟩` from `hbase ((K₀ : Set G) ∩ N) (Filter.inter_mem (hK₀o.mem_nhds K₀.one_mem) hN)`. Use `haveI : CompactSpace K₀ := isCompact_iff_compactSpace.mp hK₀c`. Use `set H : Subgroup K₀ := K₆.subgroupOf K₀ with hH`. Establish `hHo : IsOpen (H : Set K₀)` using `hK₆o.preimage continuous_subtype_val`. Use `haveI : Finite (K₀ ⧸ H) := H.quotient_finite_of_isOpen hHo`.

Use `haveI : H.FiniteIndex := Subgroup.finiteIndex_of_finite_quotient`. Use `set M : Subgroup K₀ := H.normalCore with hM`. Establish `hMH : M ≤ H` using `Subgroup.normalCore_le H`. Establish `hHc : IsClosed (H : Set K₀)` using `OpenSubgroup.isClosed ⟨H, hHo⟩`. Establish `hMc : IsClosed (M : Set K₀)`.

Establish `: (M : Set K₀) = ⋂ b : K₀, (fun a : K₀ => b * a * b⁻¹) ⁻¹' (H : Set K₀)`. Use extensionality with `a`. Simplify using `only [Set.mem_iInter, Set.mem_preimage, SetLike.mem_coe]`. Conclude with `Iff.rfl`. Rewrite using `[this]`.

Conclude with `isClosed_iInter fun b => hHc.preimage (by fun_prop)`. Use `haveI : M.FiniteIndex := Subgroup.finiteIndex_normalCore H`. Establish `hMo : IsOpen (M : Set K₀)` using `Subgroup.isOpen_of_isClosed_of_finiteIndex M hMc`. Use `set D : Subgroup K₀ := C.subgroupOf K₀ with hD`. Use `set L : Subgroup K₀ := M ⊔ D with hL`.

Establish `hLo : IsOpen (L : Set K₀)` using `Subgroup.isOpen_mono (le_sup_left : M ≤ L) hMo`. Establish `hLc : IsClosed (L : Set K₀)` using `OpenSubgroup.isClosed ⟨L, hLo⟩`. Establish `himg : ((L.map K₀.subtype : Subgroup G) : Set G) = Subtype.val '' (L : Set K₀)`. Use extensionality with `x`. Simplify using `[Subgroup.mem_map]`.

Use `⟨L.map K₀.subtype, ?_, ?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[himg]`. Conclude with `hK₀o.isOpenMap_subtype_val _ hLo`. Rewrite using `[himg]`. Conclude with `hLc.isCompact.image continuous_subtype_val`.

Introduce `c hc`. Use `⟨⟨c, hC hc⟩, ?_, rfl⟩` and prove the remaining obligations. Conclude with `(le_sup_right : D ≤ L) (by simpa [hD, Subgroup.mem_subgroupOf] using hc)`. Conclude with `Subgroup.map_subtype_le L`. Introduce and unpack `x ⟨y, hy, rfl⟩`.

Establish `hy' : y ∈ ((M ⊔ D : Subgroup K₀) : Set K₀)` using `hy`. Rewrite `hy'` using `[Subgroup.normal_mul]`. Take `⟨m, hm, d, hd, rfl⟩` from `Set.mem_mul.mp hy'`. Use `⟨(m : G), (hK₆s (hMH hm)).2, (d : G), hd, rfl⟩` and prove the remaining obligations.
-/
theorem exists_compactOpen_between_mul_small
    {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (hbase : ∀ O ∈ 𝓝 (1 : G), ∃ K : Subgroup G, IsOpen (K : Set G) ∧ IsCompact (K : Set G) ∧ (K : Set G) ⊆ O)
    (K₀ C : Subgroup G) (hK₀o : IsOpen (K₀ : Set G)) (hK₀c : IsCompact (K₀ : Set G)) (hC : C ≤ K₀)
    (N : Set G) (hN : N ∈ 𝓝 (1 : G)) :
    ∃ K : Subgroup G, IsOpen (K : Set G) ∧ IsCompact (K : Set G) ∧ C ≤ K ∧ K ≤ K₀ ∧
      ∀ x ∈ K, ∃ n ∈ N, ∃ c ∈ C, x = n * c := by
  obtain ⟨K₆, hK₆o, -, hK₆s⟩ := hbase ((K₀ : Set G) ∩ N)
    (Filter.inter_mem (hK₀o.mem_nhds K₀.one_mem) hN)
  haveI : CompactSpace K₀ := isCompact_iff_compactSpace.mp hK₀c

  set H : Subgroup K₀ := K₆.subgroupOf K₀ with hH
  have hHo : IsOpen (H : Set K₀) := hK₆o.preimage continuous_subtype_val
  haveI : Finite (K₀ ⧸ H) := H.quotient_finite_of_isOpen hHo
  haveI : H.FiniteIndex := Subgroup.finiteIndex_of_finite_quotient
  set M : Subgroup K₀ := H.normalCore with hM
  have hMH : M ≤ H := Subgroup.normalCore_le H
  have hHc : IsClosed (H : Set K₀) := OpenSubgroup.isClosed ⟨H, hHo⟩
  have hMc : IsClosed (M : Set K₀) := by
    have : (M : Set K₀) = ⋂ b : K₀, (fun a : K₀ => b * a * b⁻¹) ⁻¹' (H : Set K₀) := by
      ext a
      simp only [Set.mem_iInter, Set.mem_preimage, SetLike.mem_coe]
      exact Iff.rfl
    rw [this]
    exact isClosed_iInter fun b => hHc.preimage (by fun_prop)
  haveI : M.FiniteIndex := Subgroup.finiteIndex_normalCore H
  have hMo : IsOpen (M : Set K₀) := Subgroup.isOpen_of_isClosed_of_finiteIndex M hMc

  set D : Subgroup K₀ := C.subgroupOf K₀ with hD
  set L : Subgroup K₀ := M ⊔ D with hL
  have hLo : IsOpen (L : Set K₀) := Subgroup.isOpen_mono (le_sup_left : M ≤ L) hMo
  have hLc : IsClosed (L : Set K₀) := OpenSubgroup.isClosed ⟨L, hLo⟩
  have himg : ((L.map K₀.subtype : Subgroup G) : Set G) = Subtype.val '' (L : Set K₀) := by
    ext x; simp [Subgroup.mem_map]
  refine ⟨L.map K₀.subtype, ?_, ?_, ?_, ?_, ?_⟩
  · rw [himg]
    exact hK₀o.isOpenMap_subtype_val _ hLo
  · rw [himg]
    exact hLc.isCompact.image continuous_subtype_val
  · intro c hc
    refine ⟨⟨c, hC hc⟩, ?_, rfl⟩
    exact (le_sup_right : D ≤ L) (by simpa [hD, Subgroup.mem_subgroupOf] using hc)
  · exact Subgroup.map_subtype_le L
  · rintro x ⟨y, hy, rfl⟩
    have hy' : y ∈ ((M ⊔ D : Subgroup K₀) : Set K₀) := hy
    rw [Subgroup.normal_mul] at hy'
    obtain ⟨m, hm, d, hd, rfl⟩ := Set.mem_mul.mp hy'
    refine ⟨(m : G), (hK₆s (hMH hm)).2, (d : G), hd, rfl⟩

end GlobalTheory.CompanionTheory.BZPhiPG.OntoO

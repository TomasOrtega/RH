import Mathlib

namespace GlobalTheory

/- English proof (translation)
Introduce `h hh`. Use `set K : Submodule ℂ V := H0 ⊓ LinearMap.ker pr with hK`. Use `haveI : FiniteDimensional ℂ K := Submodule.finiteDimensional_of_le inf_le_left`. Use `set K' : Submodule ℂ H := K.map ι with hK'`. Use `haveI : FiniteDimensional ℂ K' := inferInstance`.

Use `haveI : CompleteSpace K' := FiniteDimensional.complete ℂ K'`. Take `⟨y, hy, e, he, hsum⟩` from `K'.exists_add_mem_mem_orthogonal (ι h)`. Take `⟨k, hk, rfl⟩` from `Submodule.mem_map.mp hy`. Establish `hkH0 : k ∈ H0` using `hk.1`. Establish `hkker : pr k = 0` using `hk.2`.

Use `⟨h - k, H0.sub_mem hh hkH0, by simp [hkker], ?_⟩` and prove the remaining obligations. Establish `horth : ∀ k' ∈ K, inner ℂ (ι k') (ι (h - k)) = 0`. Introduce `k' hk'`. Establish `: ι (h - k) = e` using `by rw [map_sub, hsum]; abel`. Rewrite using `[this]`.

Conclude with `(Submodule.mem_orthogonal K' e).mp he _ (Submodule.mem_map_of_mem hk')`. Introduce `a ha z hz`. Use `set c := h - k with hc`. Establish `hcH0 : c ∈ H0` using `H0.sub_mem hh hkH0`. Use `set d := a c - z • c with hd`.

Establish `hdK : d ∈ K`. Use `⟨H0.sub_mem (h1 a ha c hcH0) (H0.smul_mem z hcH0), ?_⟩` and prove the remaining obligations. Use `show pr d = 0`. Simplify using `[hd, hz]`. Take `⟨b, hb, hab⟩` from `h3 a ha`.

Establish `hdorth : ∀ k' ∈ K, inner ℂ (ι k') (ι d) = 0`. Introduce `k' hk'`. Establish `hbk : b k' ∈ K` using `⟨h1 b hb k' hk'.1, h2 b hb k' hk'.1 hk'.2⟩`. Establish `e1 : inner ℂ (ι k') (ι (a c)) = 0`. Rewrite using `[← inner_conj_symm, hab, inner_conj_symm]`.

Conclude with `horth _ hbk`. Rewrite using `[hd, map_sub, inner_sub_right, e1, map_smul, inner_smul_right, horth k' hk']`. Simplify using the standard rewrite rules. Establish `: ι d = 0` using `inner_self_eq_zero.mp (hdorth d hdK)`. Establish `hd0 : d = 0` using `hι (by rw [this, map_zero])`.

Conclude with `sub_eq_zero.mp hd0`.
-/
theorem stable_complement_of_kernel_exists
    (V W H : Type) [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] (ι : V →ₗ[ℂ] H)
    (hι : Function.Injective ι) (pr : V →ₗ[ℂ] W) (H0 : Submodule ℂ V)
    (hfin : FiniteDimensional ℂ H0) (A : Set (Module.End ℂ V))
    (h1 : ∀ a ∈ A, ∀ v ∈ H0, a v ∈ H0)
    (h2 : ∀ a ∈ A, ∀ v ∈ H0, pr v = 0 → pr (a v) = 0)
    (h3 : ∀ a ∈ A, ∃ b ∈ A, ∀ u v, inner ℂ (ι (a u)) (ι v) = inner ℂ (ι u) (ι (b v))) :
    ∀ h ∈ H0, ∃ c ∈ H0, pr c = pr h ∧
      ∀ a ∈ A, ∀ z : ℂ, pr (a c) = z • pr c → a c = z • c := by
  intro h hh
  set K : Submodule ℂ V := H0 ⊓ LinearMap.ker pr with hK
  haveI : FiniteDimensional ℂ K := Submodule.finiteDimensional_of_le inf_le_left
  set K' : Submodule ℂ H := K.map ι with hK'
  haveI : FiniteDimensional ℂ K' := inferInstance
  haveI : CompleteSpace K' := FiniteDimensional.complete ℂ K'
  obtain ⟨y, hy, e, he, hsum⟩ := K'.exists_add_mem_mem_orthogonal (ι h)
  obtain ⟨k, hk, rfl⟩ := Submodule.mem_map.mp hy
  have hkH0 : k ∈ H0 := hk.1
  have hkker : pr k = 0 := hk.2
  refine ⟨h - k, H0.sub_mem hh hkH0, by simp [hkker], ?_⟩
  have horth : ∀ k' ∈ K, inner ℂ (ι k') (ι (h - k)) = 0 := by
    intro k' hk'
    have : ι (h - k) = e := by rw [map_sub, hsum]; abel
    rw [this]
    exact (Submodule.mem_orthogonal K' e).mp he _ (Submodule.mem_map_of_mem hk')
  intro a ha z hz
  set c := h - k with hc
  have hcH0 : c ∈ H0 := H0.sub_mem hh hkH0
  set d := a c - z • c with hd
  have hdK : d ∈ K := by
    refine ⟨H0.sub_mem (h1 a ha c hcH0) (H0.smul_mem z hcH0), ?_⟩
    show pr d = 0
    simp [hd, hz]
  obtain ⟨b, hb, hab⟩ := h3 a ha
  have hdorth : ∀ k' ∈ K, inner ℂ (ι k') (ι d) = 0 := by
    intro k' hk'
    have hbk : b k' ∈ K := ⟨h1 b hb k' hk'.1, h2 b hb k' hk'.1 hk'.2⟩
    have e1 : inner ℂ (ι k') (ι (a c)) = 0 := by
      rw [← inner_conj_symm, hab, inner_conj_symm]
      exact horth _ hbk
    rw [hd, map_sub, inner_sub_right, e1, map_smul, inner_smul_right, horth k' hk']
    simp
  have : ι d = 0 := inner_self_eq_zero.mp (hdorth d hdK)
  have hd0 : d = 0 := hι (by rw [this, map_zero])
  exact sub_eq_zero.mp hd0

end GlobalTheory

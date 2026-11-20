import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCoords
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CanonicalOfAbelianDeRham
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.UPel.Sm GlobalTheory.Cris GlobalTheory.DeRham

noncomputable section

namespace GlobalTheory.HTRealise

variable {k : Type} [Field k]

def coordSub (A₀ : Over (Sp k)) [GrpObj A₀] (S : Submodule k (HdR A₀)) :
    Submodule (DualNumber k) (Crys (epsDP k) (GlobalTheory.DeRham.epsRed k) A₀) where
  carrier := {d | ∃ u ∈ S, ∃ v ∈ S, ∀ c : primDR A₀,
    d ((constMor A₀).pull c) = TrivSqZeroExt.inl (u c) + TrivSqZeroExt.inr (v c)}
  add_mem' := by
    rintro d d' ⟨x, hx, y, hy, e⟩ ⟨x', hx', y', hy', e'⟩
    refine ⟨x + x', add_mem hx hx', y + y', add_mem hy hy', fun c => ?_⟩
    rw [LinearMap.add_apply, e, e']
    ext <;> simp <;> ring
  zero_mem' := ⟨0, zero_mem _, 0, zero_mem _, fun c => by
    rw [LinearMap.zero_apply]
    ext <;> simp⟩
  smul_mem' := by
    rintro r d ⟨x, hx, y, hy, e⟩
    refine ⟨r.fst • x, Submodule.smul_mem _ _ hx, r.fst • y + r.snd • x,
      add_mem (Submodule.smul_mem _ _ hy) (Submodule.smul_mem _ _ hx), fun c => ?_⟩
    rw [LinearMap.smul_apply, e, smul_eq_mul]
    ext <;> simp <;> ring

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Use `LinearMap.ext fun c => ?_` and prove the remaining obligations. Use `congrArg TrivSqZeroExt.fst (h c)` as an intermediate fact. Simplify using `using this`. Use `LinearMap.ext fun c => ?_` and prove the remaining obligations.

Use `congrArg TrivSqZeroExt.snd (h c)` as an intermediate fact. Simplify using `using this`.
-/
theorem coords_unique {A₀ : Over (Sp k)} [GrpObj A₀] {u v u' v' : HdR A₀}
    (h : ∀ c : primDR A₀, TrivSqZeroExt.inl (u c) + TrivSqZeroExt.inr (v c)
      = (TrivSqZeroExt.inl (u' c) + TrivSqZeroExt.inr (v' c) : DualNumber k)) : u = u' ∧ v = v' := by
  constructor
  · refine LinearMap.ext fun c => ?_
    have := congrArg TrivSqZeroExt.fst (h c)
    simpa using this
  · refine LinearMap.ext fun c => ?_
    have := congrArg TrivSqZeroExt.snd (h c)
    simpa using this

/- English proof (translation)
Introduce `k _ A₀ _ hA f`. Take `⟨W, hW⟩` from `Submodule.exists_isCompl (Fil A₀)`. Use `⟨coordSub A₀ W, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[Submodule.disjoint_def]`. Introduce and unpack `d ⟨x, hx, y, hy, e⟩ ⟨u, hu, v, hv, e'⟩`.

Take `⟨h1, h2⟩` from `coords_unique (u := x) (v := f x + y) (u' := u) (v' := v) (fun c => by rw [LinearMap.add_apply]; exact (e c).symm.trans (e' c))`. Substitute `h1` using the available equality. Establish `hx0 : x = 0` using `(Submodule.disjoint_def.1 hW.disjoint) x hx hu`. Substitute `hx0` using the available equality. Rewrite `h2` using `[map_zero, zero_add]`.

Substitute `h2` using the available equality. Establish `hy0 : y = 0` using `(Submodule.disjoint_def.1 hW.disjoint) y hy hv`. Substitute `hy0` using the available equality. Use `crys_ext hA fun c => ?_` and prove the remaining obligations. Rewrite using `[e' c]`.

Apply the tactic sequence `ext <;> simp <;> rfl`. Rewrite using `[codisjoint_iff, eq_top_iff]`. Introduce `d _`. Take `⟨u, v, hd⟩` from `exists_coords d`. Establish `htop : Fil A₀ ⊔ W = ⊤` using `hW.sup_eq_top`.

Take `⟨x, hx, w, hw, hxw⟩` from `Submodule.mem_sup.1 (htop ▸ Submodule.mem_top : u ∈ Fil A₀ ⊔ W)`. Take `⟨y, hy, w', hw', hyw⟩` from `Submodule.mem_sup.1 (htop ▸ Submodule.mem_top : v - f x ∈ Fil A₀ ⊔ W)`. Take `⟨d₁, h₁⟩` from `exists_crys hA x (f x + y)`. Take `⟨d₂, h₂⟩` from `exists_crys hA w w'`. Establish `hsum : d = d₁ + d₂`.

Use `crys_ext hA fun c => ?_` and prove the remaining obligations. Rewrite using `[LinearMap.add_apply, hd c, h₁ c, h₂ c, ← hxw]`. Establish `hv : v = f x + (y + w')` using `by rw [hyw]; abel`. Rewrite using `[hv]`. Apply the tactic sequence `ext <;> simp <;> ring`.

Rewrite using `[hsum]`. Conclude with `Submodule.add_mem_sup ⟨x, hx, y, hy, h₁⟩ ⟨w, hw, w', hw', h₂⟩`.
-/
theorem graphFil_exists_isCompl : ∀ (k : Type) [Field k] (A₀ : Over (Sp k)) [GrpObj A₀], IsAbelianScheme A₀ →
    ∀ f : HdR A₀ →ₗ[k] HdR A₀, ∃ M : Submodule (DualNumber k) (Crys (epsDP k) (GlobalTheory.DeRham.epsRed k) A₀),
      IsCompl (GlobalTheory.HTRealise.graphFil A₀ f) M := by
  intro k _ A₀ _ hA f
  obtain ⟨W, hW⟩ := Submodule.exists_isCompl (Fil A₀)
  refine ⟨coordSub A₀ W, ?_, ?_⟩
  · rw [Submodule.disjoint_def]
    rintro d ⟨x, hx, y, hy, e⟩ ⟨u, hu, v, hv, e'⟩
    obtain ⟨h1, h2⟩ := coords_unique (u := x) (v := f x + y) (u' := u) (v' := v)
      (fun c => by rw [LinearMap.add_apply]; exact (e c).symm.trans (e' c))
    subst h1
    have hx0 : x = 0 := (Submodule.disjoint_def.1 hW.disjoint) x hx hu
    subst hx0
    rw [map_zero, zero_add] at h2
    subst h2
    have hy0 : y = 0 := (Submodule.disjoint_def.1 hW.disjoint) y hy hv
    subst hy0
    refine crys_ext hA fun c => ?_
    rw [e' c]
    ext <;> simp <;> rfl
  · rw [codisjoint_iff, eq_top_iff]
    intro d _
    obtain ⟨u, v, hd⟩ := exists_coords d
    have htop : Fil A₀ ⊔ W = ⊤ := hW.sup_eq_top
    obtain ⟨x, hx, w, hw, hxw⟩ := Submodule.mem_sup.1 (htop ▸ Submodule.mem_top : u ∈ Fil A₀ ⊔ W)
    obtain ⟨y, hy, w', hw', hyw⟩ :=
      Submodule.mem_sup.1 (htop ▸ Submodule.mem_top : v - f x ∈ Fil A₀ ⊔ W)
    obtain ⟨d₁, h₁⟩ := exists_crys hA x (f x + y)
    obtain ⟨d₂, h₂⟩ := exists_crys hA w w'
    have hsum : d = d₁ + d₂ := by
      refine crys_ext hA fun c => ?_
      rw [LinearMap.add_apply, hd c, h₁ c, h₂ c, ← hxw]
      have hv : v = f x + (y + w') := by rw [hyw]; abel
      rw [hv]
      ext <;> simp <;> ring
    rw [hsum]
    exact Submodule.add_mem_sup ⟨x, hx, y, hy, h₁⟩ ⟨w, hw, w', hw', h₂⟩

end GlobalTheory.HTRealise

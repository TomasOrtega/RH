import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.IsSatVecUOfIsSphericalU

noncomputable section

namespace GlobalTheory.LFun.SatCompare

open Formalism.UG GlobalTheory.PRep GlobalTheory.LFun

variable {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V] {ρ : Representation ℂ G V} {K : Subgroup G}
  {f f' : G → ℂ} {x : V}

/- English proof (translation)
Use `Eq.symm (((ρ g).toAddMonoidHom.map_finsum (finite_heckeVec hK hf ρ x)).trans (finsum_congr fun c => ?_))` and prove the remaining obligations. Simplify using the standard rewrite rules.
-/
theorem hAct_orbit (hK : IsCommensurated K) (hf : f ∈ Hecke ℂ K) (ρ : Representation ℂ G V) (x : V) (g : G) :
    hAct K f (fun y => ρ y x) g = ρ g (heckeVec ρ K f x) := by
  refine Eq.symm (((ρ g).toAddMonoidHom.map_finsum (finite_heckeVec hK hf ρ x)).trans (finsum_congr fun c => ?_))
  simp

/- English proof (translation)
Introduce `γ g κ`. Establish `: (γ : G) = 1` using `Subgroup.mem_bot.1 γ.2`. Simplify using `[this, GlobalTheory.LGrp.mem_fixed.1 hx κ κ.2]`.
-/
theorem orbit_mem_amf (hx : x ∈ fixed ρ K) :
    (fun y => ρ y x) ∈ AMF ℂ ⊥ K (Representation.trivial ℂ (⊥ : Subgroup G) V) := by
  intro γ g κ
  have : (γ : G) = 1 := Subgroup.mem_bot.1 γ.2
  simp [this, GlobalTheory.LGrp.mem_fixed.1 hx κ κ.2]

/- English proof (translation)
Use `GlobalTheory.LGrp.mem_fixed.2 fun k hk => ?_` and prove the remaining obligations. Use `Final.HeckeActMem G ⊥ K ℂ V _ hK f hf _ (orbit_mem_amf hx) 1 1 ⟨k, hk⟩` as an intermediate fact. Simplify `this` using `[hAct_orbit hK hf]`.
-/
theorem heckeVec_mem_fixed (hK : IsCommensurated K) (hf : f ∈ Hecke ℂ K) (hx : x ∈ fixed ρ K) :
    heckeVec ρ K f x ∈ fixed ρ K := by
  refine GlobalTheory.LGrp.mem_fixed.2 fun k hk => ?_
  have := Final.HeckeActMem G ⊥ K ℂ V _ hK f hf _ (orbit_mem_amf hx) 1 1 ⟨k, hk⟩
  simpa [hAct_orbit hK hf] using this

/- English proof (translation)
Use `congrFun (Final.HeckeActMul G ⊥ K ℂ V _ hK f hf f' hf' _ (orbit_mem_amf hx)) 1` as an intermediate fact. Rewrite `this` using `[funext (hAct_orbit hK hf' ρ x), hAct_orbit hK hf, hAct_orbit hK (Final.HeckeConvMem G K ℂ hK f hf f' hf')]`. Simplify using `using this`.
-/
theorem heckeVec_conv (hK : IsCommensurated K) (hf : f ∈ Hecke ℂ K) (hf' : f' ∈ Hecke ℂ K) (hx : x ∈ fixed ρ K) :
    heckeVec ρ K (conv K f f') x = heckeVec ρ K f (heckeVec ρ K f' x) := by
  have := congrFun (Final.HeckeActMul G ⊥ K ℂ V _ hK f hf f' hf' _ (orbit_mem_amf hx)) 1
  rw [funext (hAct_orbit hK hf' ρ x), hAct_orbit hK hf,
    hAct_orbit hK (Final.HeckeConvMem G K ℂ hK f hf f' hf')] at this
  simpa using this

/- English proof (translation)
Use `congrFun (Final.HeckeActOne G ⊥ K ℂ V _ _ (orbit_mem_amf hx)) 1` as an intermediate fact. Rewrite `this` using `[hAct_orbit hK (Final.DosetIndMem G K ℂ 1)]`. Simplify using `using this`.
-/
theorem heckeVec_one (hK : IsCommensurated K) (hx : x ∈ fixed ρ K) : heckeVec ρ K (dosetInd ℂ K 1) x = x := by
  have := congrFun (Final.HeckeActOne G ⊥ K ℂ V _ _ (orbit_mem_amf hx)) 1
  rw [hAct_orbit hK (Final.DosetIndMem G K ℂ 1)] at this
  simpa using this

/- English proof (translation)
Unfold `heckeVec`. Rewrite using `[← finsum_add_distrib (finite_heckeVec hK hf ρ x) (finite_heckeVec hK hf' ρ x)]`. Conclude with `finsum_congr fun c => by simp [add_smul]`.
-/
theorem heckeVec_add_left (hK : IsCommensurated K) (hf : f ∈ Hecke ℂ K) (hf' : f' ∈ Hecke ℂ K) (x : V) :
    heckeVec ρ K (f + f') x = heckeVec ρ K f x + heckeVec ρ K f' x := by
  unfold heckeVec
  rw [← finsum_add_distrib (finite_heckeVec hK hf ρ x) (finite_heckeVec hK hf' ρ x)]
  exact finsum_congr fun c => by simp [add_smul]

/- English proof (translation)
Unfold `heckeVec`. Rewrite using `[smul_finsum' c (finite_heckeVec hK hf ρ x)]`. Conclude with `finsum_congr fun c => by simp [mul_smul]`.
-/
theorem heckeVec_smul_left (hK : IsCommensurated K) (hf : f ∈ Hecke ℂ K) (c : ℂ) (x : V) :
    heckeVec ρ K (c • f) x = c • heckeVec ρ K f x := by
  unfold heckeVec
  rw [smul_finsum' c (finite_heckeVec hK hf ρ x)]
  exact finsum_congr fun c => by simp [mul_smul]

/- English proof (translation)
Simplify using `[heckeVec]`.
-/
theorem heckeVec_zero_left (x : V) : heckeVec ρ K 0 x = 0 := by simp [heckeVec]

def heckeLin (hK : IsCommensurated K) (hf : f ∈ Hecke ℂ K) (ρ : Representation ℂ G V) : V →ₗ[ℂ] V where
  toFun := heckeVec ρ K f
  map_add' x y := by
    unfold heckeVec
    rw [← finsum_add_distrib (finite_heckeVec hK hf ρ x) (finite_heckeVec hK hf ρ y)]
    exact finsum_congr fun c => by simp
  map_smul' c x := (map_heckeVec hK hf (c • LinearMap.id) (fun g y => by simp) x).symm

/- English proof (translation)
Both sides reduce to the same expression.
-/
@[simp] theorem heckeLin_apply (hK : IsCommensurated K) (hf : f ∈ Hecke ℂ K) (x : V) :
    heckeLin hK hf ρ x = heckeVec ρ K f x := rfl

/- English proof (translation)
The claim follows from `(heckeLin hK hf ρ).map_smul c x`.
-/
theorem heckeVec_smul (hK : IsCommensurated K) (hf : f ∈ Hecke ℂ K) (c : ℂ) (x : V) :
    heckeVec ρ K f (c • x) = c • heckeVec ρ K f x := (heckeLin hK hf ρ).map_smul c x

end GlobalTheory.LFun.SatCompare

end

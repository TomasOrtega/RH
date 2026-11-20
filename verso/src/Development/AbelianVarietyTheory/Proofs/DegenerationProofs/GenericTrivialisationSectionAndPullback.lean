import Mathlib
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.IsHomOpenPart
open CategoryTheory Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.ZH

noncomputable section
namespace GlobalTheory.ZH.RatModel

open GlobalTheory.Points

variable {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] {M : RatModel o Ω} {H : LB M.Z} {d : H.ι → Ω}

/- English proof (translation)
Establish `hf : ∀ k, ∃ f : Γ(M.Z, H.U k), (H.U k : Set M.Z).Nonempty → valF M.pt (H.U k) f = x / d k` using `fun k => by`. Distinguish the cases in `hk : (H.U k : Set M.Z).Nonempty`. Take `⟨f, hf⟩` from `(mem_ringOn_iff_exists hk).1 (mem_ringOn.2 (hx k))`. Conclude with `⟨f, fun _ => hf⟩`. Conclude with `⟨0, fun h => (hk h).elim⟩`.

Use `choose f hf using hf`. Use `⟨⟨f, fun i j => ?_⟩, hf⟩` and prove the remaining obligations. Distinguish the cases in `hij : ((H.U i ⊓ H.U j : M.Z.Opens) : Set M.Z).Nonempty`. Use `M.res_injective _ hij ?_` and prove the remaining obligations. Establish `h1` using `(M.res_apply _ hij _).trans ((M.valF_resG inf_le_left hij (f i)).trans (hf i (hij.mono (fun _ hz => hz.1))))`.

Establish `h2` using `(M.res_apply _ hij _).trans ((M.valF_resG inf_le_right hij (f j)).trans (hf j (hij.mono (fun _ hz => hz.2))))`. Establish `h3` using `(M.res_apply _ hij _).trans (h.g_eq i j hij)`. Rewrite using `[map_mul, h3]`. Use `h1.trans (Eq.trans ?_ (congrArg (d j / d i * ·) h2.symm))` and prove the remaining obligations. Use `h.ne i` as an intermediate fact.

Use `h.ne j` as an intermediate fact. Clear the denominators using the available nonvanishing facts. Establish `e : (H.U i ⊓ H.U j : M.Z.Opens) = ⊥` using `SetLike.coe_injective (Set.not_nonempty_iff_eq_empty.1 hij)`. Establish `: Subsingleton Γ(M.Z, H.U i ⊓ H.U j)`. Rewrite using `[e]`.

Use `infer_instance`. Conclude with `Subsingleton.elim _ _`.
-/
theorem GenTriv.exists_sec_hasVal (h : M.GenTriv H d) (x : Ω) (hx : ∀ k, ∀ z ∈ H.U k, x / d k ∈ M.O z) :
    ∃ σ : H.Sec, M.HasVal d σ x := by
  have hf : ∀ k, ∃ f : Γ(M.Z, H.U k), (H.U k : Set M.Z).Nonempty → valF M.pt (H.U k) f = x / d k := fun k => by
    by_cases hk : (H.U k : Set M.Z).Nonempty
    · obtain ⟨f, hf⟩ := (mem_ringOn_iff_exists hk).1 (mem_ringOn.2 (hx k))
      exact ⟨f, fun _ => hf⟩
    · exact ⟨0, fun h => (hk h).elim⟩
  choose f hf using hf
  refine ⟨⟨f, fun i j => ?_⟩, hf⟩
  by_cases hij : ((H.U i ⊓ H.U j : M.Z.Opens) : Set M.Z).Nonempty
  · refine M.res_injective _ hij ?_
    have h1 := (M.res_apply _ hij _).trans ((M.valF_resG inf_le_left hij (f i)).trans
      (hf i (hij.mono (fun _ hz => hz.1))))
    have h2 := (M.res_apply _ hij _).trans ((M.valF_resG inf_le_right hij (f j)).trans
      (hf j (hij.mono (fun _ hz => hz.2))))
    have h3 := (M.res_apply _ hij _).trans (h.g_eq i j hij)
    rw [map_mul, h3]
    refine h1.trans (Eq.trans ?_ (congrArg (d j / d i * ·) h2.symm))
    have := h.ne i
    have := h.ne j
    field_simp
  · have e : (H.U i ⊓ H.U j : M.Z.Opens) = ⊥ :=
      SetLike.coe_injective (Set.not_nonempty_iff_eq_empty.1 hij)
    have : Subsingleton Γ(M.Z, H.U i ⊓ H.U j) := by
      rw [e]; infer_instance
    exact Subsingleton.elim _ _

/- English proof (translation)
Use `⟨fun k => (map_ne_zero φ).2 (h.ne _), fun k k' hk => ?_⟩` and prove the remaining obligations. Establish `hle : (H.pull a).U k ⊓ (H.pull a).U k' ≤ a ⁻¹ᵁ (H.U (k PUnit.unit) ⊓ H.U (k' PUnit.unit))` using `le_inf (inf_le_left.trans (LB.wchart_le H (fun _ => a) k PUnit.unit)) (inf_le_right.trans (LB.wchart_le H (fun _ => a) k' PUnit.unit))`. Establish `hne : ((H.U (k PUnit.unit) ⊓ H.U (k' PUnit.unit) : M.Z.Opens) : Set M.Z).Nonempty`. Take `⟨z, hz⟩` from `hk`. Conclude with `⟨a z, hle hz⟩`.

Establish `e : ((H.pull a).g k k' : Γ(N.Z, (H.pull a).U k ⊓ (H.pull a).U k')) = resG N.Z hle (a.app _ (H.g (k PUnit.unit) (k' PUnit.unit) : Γ(M.Z, _)))`. Establish `e0 : (H.pull a).g k k' = Semi.res hle (pullU a _ (H.g (k PUnit.unit) (k' PUnit.unit)))` using `(Fintype.prod_unique (ι := PUnit) fun _ => Semi.res hle (pullU a _ (H.g (k PUnit.unit) (k' PUnit.unit))) ^ (1 : ℤ)).trans (zpow_one _)`. Conclude with `congrArg Units.val e0`. Rewrite using `[e, N.valF_resG hle hk, ha.valF_app hne, h.g_eq _ _ hne, map_div₀]`.
-/
theorem GenTriv.pull (h : M.GenTriv H d) {Ω' : Type} [Field Ω'] [Algebra o Ω'] {φ : Ω →ₐ[o] Ω'}
    {N : RatModel o Ω'} {a : N.Z ⟶ M.Z} (ha : M.IsHom N φ a) :
    N.GenTriv (H.pull a) fun k => φ (d (k PUnit.unit)) := by
  refine ⟨fun k => (map_ne_zero φ).2 (h.ne _), fun k k' hk => ?_⟩
  have hle : (H.pull a).U k ⊓ (H.pull a).U k' ≤ a ⁻¹ᵁ (H.U (k PUnit.unit) ⊓ H.U (k' PUnit.unit)) :=
    le_inf (inf_le_left.trans (LB.wchart_le H (fun _ => a) k PUnit.unit))
      (inf_le_right.trans (LB.wchart_le H (fun _ => a) k' PUnit.unit))
  have hne : ((H.U (k PUnit.unit) ⊓ H.U (k' PUnit.unit) : M.Z.Opens) : Set M.Z).Nonempty := by
    obtain ⟨z, hz⟩ := hk
    exact ⟨a z, hle hz⟩
  have e : ((H.pull a).g k k' : Γ(N.Z, (H.pull a).U k ⊓ (H.pull a).U k')) =
      resG N.Z hle (a.app _ (H.g (k PUnit.unit) (k' PUnit.unit) : Γ(M.Z, _))) := by
    have e0 : (H.pull a).g k k' = Semi.res hle (pullU a _ (H.g (k PUnit.unit) (k' PUnit.unit))) :=
      (Fintype.prod_unique (ι := PUnit) fun _ =>
        Semi.res hle (pullU a _ (H.g (k PUnit.unit) (k' PUnit.unit))) ^ (1 : ℤ)).trans (zpow_one _)
    exact congrArg Units.val e0
  rw [e, N.valF_resG hle hk, ha.valF_app hne, h.g_eq _ _ hne, map_div₀]

/- English proof (translation)
Introduce `_ _ _ _ _ _ _ _ h` and use `⟨h.exists_sec_hasVal, fun _ _ _ _ _ _ ha => h.pull ha⟩`.
-/
theorem genTriv_sec_and_pull : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] (M : RatModel o Ω) (H : LB M.Z)
    (d : H.ι → Ω), M.GenTriv H d →
    (∀ x : Ω, (∀ k, ∀ z ∈ H.U k, x / d k ∈ M.O z) → ∃ σ : H.Sec, M.HasVal d σ x) ∧
    ∀ (Ω' : Type) [Field Ω'] [Algebra o Ω'] (φ : Ω →ₐ[o] Ω') (N : RatModel o Ω') (a : N.Z ⟶ M.Z),
      M.IsHom N φ a → N.GenTriv (H.pull a) fun k => φ (d (k PUnit.unit)) :=
  fun _ _ _ _ _ _ _ _ h => ⟨h.exists_sec_hasVal, fun _ _ _ _ _ _ ha => h.pull ha⟩

end GlobalTheory.ZH.RatModel
end

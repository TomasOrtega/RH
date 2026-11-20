import Development.WeilBound.ThetaLifts.SphericalLattices.FunDefs
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HasSatakeGLOfIsSatVecGL

noncomputable section

namespace PositivityTheory.Sph

open scoped Matrix
open NumberField IsDedekindDomain Topology GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.LFun.InertChart GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.UG
  PositivityTheory.ThK

/- English proof (translation)
Establish `: (H.subgroupOf L).FiniteIndex` using `⟨h⟩`. Establish `: Finite (K ⧸ H.subgroupOf K)` using `Finite.of_injective _ (Subgroup.quotientSubgroupOfEmbeddingOfLE H hKL).injective`. Conclude with `Subgroup.index_ne_zero_of_finite`.
-/
theorem finSt_relIndex_le {G : Type} [Group G] {H K L : Subgroup G} (hKL : K ≤ L) (h : H.relIndex L ≠ 0) :
    H.relIndex K ≠ 0 := by
  have : (H.subgroupOf L).FiniteIndex := ⟨h⟩
  have : Finite (K ⧸ H.subgroupOf K) :=
    Finite.of_injective _ (Subgroup.quotientSubgroupOfEmbeddingOfLE H hKL).injective
  exact Subgroup.index_ne_zero_of_finite

/- English proof (translation)
Establish `: CompactSpace K` using `isCompact_iff_compactSpace.1 hK`. Establish `ho : IsOpen ((H.subgroupOf K : Subgroup K) : Set K)` using `(H.subgroupOf K).isOpen_of_mem_nhds (Filter.mem_of_superset (continuous_subtype_val.continuousAt (x := (1 : K)) hU) fun k hk => Subgroup.mem_subgroupOf.2 (hH k.1 k.2 hk))`. Establish `: Finite (K ⧸ H.subgroupOf K)` using `Subgroup.quotient_finite_of_isOpen _ ho`. Conclude with `Subgroup.index_ne_zero_of_finite`.
-/
theorem finSt_relIndex_nhds {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] {K H : Subgroup G}
    (hK : IsCompact (K : Set G)) {U : Set G} (hU : U ∈ 𝓝 (1 : G)) (hH : ∀ k ∈ K, k ∈ U → k ∈ H) : H.relIndex K ≠ 0 := by
  have : CompactSpace K := isCompact_iff_compactSpace.1 hK
  have ho : IsOpen ((H.subgroupOf K : Subgroup K) : Set K) :=
    (H.subgroupOf K).isOpen_of_mem_nhds (Filter.mem_of_superset (continuous_subtype_val.continuousAt (x := (1 : K)) hU)
      fun k hk => Subgroup.mem_subgroupOf.2 (hH k.1 k.2 hk))
  have : Finite (K ⧸ H.subgroupOf K) := Subgroup.quotient_finite_of_isOpen _ ho
  exact Subgroup.index_ne_zero_of_finite

/- English proof (translation)
Take `⟨ho, hc⟩` from `SatCompare.isOpen_isCompact_KGL w n`. Establish `hcont : Continuous fun x : GL (Fin n) (w.adicCompletion E) => b⁻¹ * x * b` using `(continuous_const.mul continuous_id).mul continuous_const`. Use `finSt_relIndex_nhds hc (U := (KGL w n : Set _) ∩ (fun x => b⁻¹ * x * b) ⁻¹' (KGL w n : Set _)) ((ho.inter (ho.preimage hcont)).mem_nhds ⟨one_mem _, by simp [one_mem]⟩) fun k _ hk => ⟨hk.1, ?_⟩` and prove the remaining obligations. Use `⟨b⁻¹ * k * b, hk.2, ?_⟩` and prove the remaining obligations. Simplify using `[MulAut.conj_apply, mul_assoc]`.
-/
theorem finSt_KGL {E : Type} [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E)) (n : ℕ)
    (b : GL (Fin n) (w.adicCompletion E)) :
    (KGL w n ⊓ (KGL w n).map (MulAut.conj b).toMonoidHom).relIndex (KGL w n) ≠ 0 := by
  obtain ⟨ho, hc⟩ := SatCompare.isOpen_isCompact_KGL w n
  have hcont : Continuous fun x : GL (Fin n) (w.adicCompletion E) => b⁻¹ * x * b :=
    (continuous_const.mul continuous_id).mul continuous_const
  refine finSt_relIndex_nhds hc (U := (KGL w n : Set _) ∩ (fun x => b⁻¹ * x * b) ⁻¹' (KGL w n : Set _))
    ((ho.inter (ho.preimage hcont)).mem_nhds ⟨one_mem _, by simp [one_mem]⟩) fun k _ hk => ⟨hk.1, ?_⟩
  refine ⟨b⁻¹ * k * b, hk.2, ?_⟩
  simp [MulAut.conj_apply, mul_assoc]

/- English proof (translation)
Introduce `F E _ _ _ _ _ σ d B W r s hB hW v w hw g hg`. Establish `hv : w.under (𝓞 F) = v` using `(under_eq_iff hw w).2 rfl`. Take `⟨c, hc, -⟩` from `existsUnique_isConjAt σ hw hv`. Take `⟨a, ha, -⟩` from `PositivityTheory.ThKH.Iwas.exists_frame hB.cm hw hv hc hW`. Set `Φ : UA σ W.J →* GL (Fin d) (w.adicCompletion E)` to `(MulAut.conj a⁻¹).toMonoidHom.comp ((Units.map (RingHom.mapMatrix (PositivityTheory.ThKH.Iwas.piE hv)).toMonoidHom).comp (Subgroup.subtype _))`.

Establish `hΦ : ∀ x, ((Φ x : GL (Fin d) (w.adicCompletion E)) : Matrix (Fin d) (Fin d) (w.adicCompletion E)) = (a⁻¹).1 * (mat x).map (PositivityTheory.ThKH.Iwas.piE hv) * a.1` using `fun x => by`. Simplify using `[Φ, mat]`. Establish `memK : ∀ x ∈ UAt σ W (evFin F v), x ∈ KSub σ W v ↔ Φ x ∈ KGL w d` using `fun x hx => by`. Rewrite using `[mem_GLint_iff, ← map_inv, hΦ, hΦ]`. Express the relevant statement in the definitionally equal form `(x ∈ UAt σ W (evFin F v) ∧ ∀ y ∈ latW W v, mat x *ᵥ y ∈ latW W v ∧ mat x⁻¹ *ᵥ y ∈ latW W v) ↔ _`.

Rewrite using `[← PositivityTheory.ThKH.Iwas.stab_iff hw hv ha, ← PositivityTheory.ThKH.Iwas.stab_iff hw hv ha]`. Conclude with `⟨fun H => ⟨fun y hy => (H.2 y hy).1, fun y hy => (H.2 y hy).2⟩, fun H => ⟨hx, fun y hy => ⟨H.1 y hy, H.2 y hy⟩⟩⟩`. Use `set K := KSub σ W v`. Use `set H' := KGL w d ⊓ (KGL w d).map (MulAut.conj (Φ g)).toMonoidHom`. Establish `h1 : (H'.comap Φ).relIndex K ≠ 0`.

Rewrite using `[Subgroup.relIndex_comap]`. Use `finSt_relIndex_le ?_ (finSt_KGL w d (Φ g))` and prove the remaining obligations. Introduce and unpack `_ ⟨k, hk, rfl⟩`. Conclude with `(memK k hk.1).1 hk`. Establish `h2 : H'.comap Φ ⊓ K ≤ conjInf K g`.

Introduce and unpack `k ⟨hk1, hk2⟩`. Use `⟨hk2, g⁻¹ * k * g, ?_, ?_⟩` and prove the remaining obligations. Establish `hx : g⁻¹ * k * g ∈ UAt σ W (evFin F v)` using `mul_mem_UAt (mul_mem_UAt (inv_mem_UAt hg) hk2.1) hg`. Use `(memK _ hx).2 ?_` and prove the remaining obligations. Take `⟨y, hy, ey⟩` from `hk1.2`.

Establish `: Φ (g⁻¹ * k * g) = y`. Rewrite using `[map_mul, map_mul, map_inv, ← ey]`. Simplify using `[MulAut.conj_apply, mul_assoc]`. Rewrite using `[this]`. Conclude with `hy`.

Simplify using `[MulAut.conj_apply, mul_assoc]`. Establish `h3 : (H'.comap Φ ⊓ K).relIndex K ≠ 0` using `by rwa [Subgroup.inf_relIndex_right]`. Introduce `h0`. Conclude with `h3 (Nat.eq_zero_of_zero_dvd (h0 ▸ Subgroup.relIndex_dvd_of_le_left K h2))`.
-/
theorem finSt : FinSt := by
  intro F E _ _ _ _ _ σ d B W r s hB hW v w hw g hg
  classical
  have hv : w.under (𝓞 F) = v := (under_eq_iff hw w).2 rfl
  obtain ⟨c, hc, -⟩ := existsUnique_isConjAt σ hw hv
  obtain ⟨a, ha, -⟩ := PositivityTheory.ThKH.Iwas.exists_frame hB.cm hw hv hc hW
  let Φ : UA σ W.J →* GL (Fin d) (w.adicCompletion E) :=
    (MulAut.conj a⁻¹).toMonoidHom.comp
      ((Units.map (RingHom.mapMatrix (PositivityTheory.ThKH.Iwas.piE hv)).toMonoidHom).comp (Subgroup.subtype _))
  have hΦ : ∀ x, ((Φ x : GL (Fin d) (w.adicCompletion E)) : Matrix (Fin d) (Fin d) (w.adicCompletion E)) =
      (a⁻¹).1 * (mat x).map (PositivityTheory.ThKH.Iwas.piE hv) * a.1 := fun x => by
    simp [Φ, mat]
  have memK : ∀ x ∈ UAt σ W (evFin F v), x ∈ KSub σ W v ↔ Φ x ∈ KGL w d := fun x hx => by
    rw [mem_GLint_iff, ← map_inv, hΦ, hΦ]
    change (x ∈ UAt σ W (evFin F v) ∧ ∀ y ∈ latW W v, mat x *ᵥ y ∈ latW W v ∧ mat x⁻¹ *ᵥ y ∈ latW W v) ↔ _
    rw [← PositivityTheory.ThKH.Iwas.stab_iff hw hv ha, ← PositivityTheory.ThKH.Iwas.stab_iff hw hv ha]
    exact ⟨fun H => ⟨fun y hy => (H.2 y hy).1, fun y hy => (H.2 y hy).2⟩, fun H => ⟨hx, fun y hy => ⟨H.1 y hy, H.2 y hy⟩⟩⟩
  set K := KSub σ W v
  set H' := KGL w d ⊓ (KGL w d).map (MulAut.conj (Φ g)).toMonoidHom
  have h1 : (H'.comap Φ).relIndex K ≠ 0 := by
    rw [Subgroup.relIndex_comap]
    refine finSt_relIndex_le ?_ (finSt_KGL w d (Φ g))
    rintro _ ⟨k, hk, rfl⟩
    exact (memK k hk.1).1 hk
  have h2 : H'.comap Φ ⊓ K ≤ conjInf K g := by
    rintro k ⟨hk1, hk2⟩
    refine ⟨hk2, g⁻¹ * k * g, ?_, ?_⟩
    · have hx : g⁻¹ * k * g ∈ UAt σ W (evFin F v) := mul_mem_UAt (mul_mem_UAt (inv_mem_UAt hg) hk2.1) hg
      refine (memK _ hx).2 ?_
      obtain ⟨y, hy, ey⟩ := hk1.2
      have : Φ (g⁻¹ * k * g) = y := by
        rw [map_mul, map_mul, map_inv, ← ey]
        simp [MulAut.conj_apply, mul_assoc]
      rw [this]; exact hy
    · simp [MulAut.conj_apply, mul_assoc]
  have h3 : (H'.comap Φ ⊓ K).relIndex K ≠ 0 := by rwa [Subgroup.inf_relIndex_right]
  intro h0
  exact h3 (Nat.eq_zero_of_zero_dvd (h0 ▸ Subgroup.relIndex_dvd_of_le_left K h2))

end PositivityTheory.Sph

end

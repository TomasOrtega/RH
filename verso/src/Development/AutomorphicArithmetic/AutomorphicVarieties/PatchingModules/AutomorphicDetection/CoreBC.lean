import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.AutomorphicDetection.LiftPt
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.PatchingBaseChange.Oprime
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.PatchingBaseChange.TilCo
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.PatchingBaseChange.ResidBc
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.PatchingBaseChange.PairBc
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.PatchingBaseChange.PairMf
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.PatchingBaseChange.MemSpanMapE0kerOfPairMaps
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.PatchingBaseChange.NonSSField
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.PatchingBaseChange.NonSSMono
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.PatchingBaseChange.DiscStMap
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.PatchingBaseChange.PtLift
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.PatchingBaseChange.GenBc
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.PatchingBaseChange.IsProLOfPL
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.PatchingBaseChange.AutBc
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.PatchingBaseChange.ChainTens
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.PatchingBaseChange.TilPrime
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.DGmap

open IsLocalRing UpperTheory.V.Alg UpperTheory.V.W
open scoped TensorProduct

namespace UpperTheory.V.Pa

/- English proof (translation)
Introduce `l _ L G0 T n O _ _ _ _ _ r B _ _ _ u J D A0 hl hP hAd hG h x hx`. Take `⟨O', _, _, _, _, α, P, hco, hfin, hfree, hloc, hcard, hα, hPm, hPα, hsplit⟩` from `BC.oprime l O (x 0).x.K`. Use `letI : Algebra ℤ_[l] O' := ((algebraMap O O').comp (algebraMap ℤ_[l] O)).toAlgebra`. Use `haveI : IsScalarTower ℤ_[l] O O' := IsScalarTower.of_algebraMap_eq (fun _ => rfl)`. Use `haveI : IsAdicComplete (maximalIdeal O) O := IsCoef.complete (l := l)`.

Use `haveI : Finite (ResidueField O) := IsCoef.finite (l := l)`. Use `haveI : CharP (ResidueField O) l := IsCoef.char`. Take `⟨⟨r', hr'⟩, hrr⟩` from `BC.resid_bc l G0.frame O O' n r`. Take `⟨hrIp, -, hrchi⟩` from `hrr r' hr'`. Take `⟨hTco, hιloc, hsm⟩` from `BC.til_co O O' B`.

Take `⟨-, u', hu'⟩` from `BC.pair_bc l G0.frame O O' n r r' hr' B (Til O O' B) (Til.ι O O' B) (Til.ι_algebraMap O O' B) u`. Take `⟨A', hA'⟩` from `BC.aut_bc l L G0 n O O' r r' B u u' J D T A0 hr' hu'`. Establish `hphi` using `BC.phi0 l L G0 T hP`. Establish `hAd' : Adapted (r` using `r') T := ⟨fun g hg i => (hrchi i g).2 (hAd.1 g hg i), fun w => (hrIp w).trans (hAd.2 w)⟩`. Establish `hG' : GenBy O' (pairVals u' ∪ {A'.b.lam (MvPowerSeries.X (Sum.inl ()))})`.

Use `BC.gen_bc O O' B (pairVals u) _ hιloc hsm ?_ ?_ hG` and prove the remaining obligations. Introduce and unpack `a (⟨i, g, rfl⟩ | ⟨v, i, g, rfl⟩)`. Use `left`. Use `left`. Use `⟨i, g, ?_⟩` and prove the remaining obligations.

Establish `h3` using `((CA.d_gmap u.D).2.2.1 (Til.ι O O' B) (MonoidAlgebra.single g 1)).2 i`. Rewrite `h3` using `[MonoidAlgebra.mapRingHom_single, map_one, hu'.1]`. Conclude with `h3.symm`. Use `left`. Use `right`.

Conclude with `⟨v, i, g, by rw [← hu'.2 v i]; rfl⟩`. Use `right`. Rewrite using `[hA']`. Both sides reduce to the same expression. Establish `hpr : ∀ i, (RingHom.ker (x i).f).IsPrime` using `fun i => RingHom.ker_isPrime _`.

Introduce `e he hq1 q hq hqle hst`. Take `⟨⟨Pt', Et, hPt, hEt⟩, hdown⟩` from `BC.chain_tens O O' B h (fun i => RingHom.ker (x i).f) e hpr (fun i => ⟨(he i).1, (he i).2.2⟩)`. Establish `hl1` using `fun i => BC.pt_lift l O O' α P B (x i).x.K (x i).f (Pt' i) hα hPm hPα (hsplit _ (hx i)) (hcard.trans (hx i).symm) (hPt i).1 (hPt i).2`. Use `choose inst f' hsurj hfι hfs hker using hl1`. Establish `hmaps : ∀ i, u'.Maps (f' i).toRingHom (GDet.ofRep (mat (x i).x.ρ)) (x i).x.ψ`.

Introduce `i`. Establish `hc : (f' i).toRingHom.comp (Til.ι O O' B) = (x i).f.toRingHom` using `RingHom.ext (hfι i)`. Use `⟨?_, fun v j => ?_⟩` and prove the remaining obligations. Rewrite using `[← hu'.1, (CA.d_gmap u.D).2.1, hc]`. Conclude with `(x i).maps.1`.

Rewrite using `[← hu'.2 v j, ← (x i).maps.2 v j, ← hc]`. Both sides reduce to the same expression. Set `x' : Fin (h + 1) → Pt T u' (D + n * T.q)` to `fun i => @Pt.mk _ _ _ _ T _ _ _ _ _ r' _ _ _ _ u' _ (x i).x (inst i) (x i).k (x i).al (x i).eig (x i).b1 (x i).b2 (f' i) (hmaps i)`. Establish `hmain` using `core l L G0 T n O' r' (Til O O' B) u' _ D A' hl hP hAd' hG' h x' (fun i => ⟨hsurj i, by rw [hA']; exact hfs i⟩)`. Establish `hup : ∀ Q : Ideal (O' ⊗[O] B), Q.IsPrime → (Ideal.map (Til.C O O' B) Q).IsPrime ∧ Ideal.comap (Til.ι O O' B) (Ideal.map (Til.C O O' B) Q) = Ideal.comap Algebra.TensorProduct.includeRight Q` using `fun Q hQ => BC.til_prime O O' B Q hQ`.

Establish `hle : ∀ (Q : Ideal (O' ⊗[O] B)) i, Q ≤ Pt' i → Ideal.map (Til.C O O' B) Q ≤ RingHom.ker (x' i).f`. Introduce `Q i hQi`. Rewrite using `[Ideal.map_le_iff_le_comap]`. Conclude with `hQi.trans (hker i).ge`. Establish `hfinI : ∃ s : Finset G0.frame.G₀, ∀ y : MonoidAlgebra B G0.frame.G₀, ∃ c : G0.frame.G₀ → B, y - ∑ g ∈ s, MonoidAlgebra.single g (c g) ∈ TwoSidedIdeal.span (augmentationIdealKernel u)`.

Take `⟨s, hs⟩` from `(BC.pair_mf l G0.frame O n r B u hphi).2.2 (pairGens u)`. Conclude with `⟨s, fun y => (hs y).imp fun c hc => TwoSidedIdeal.subset_span hc⟩`. Establish `hns : ∀ (E : Ideal (Til O O' B)) (e0 : Ideal B), E.IsPrime → Ideal.comap (Til.ι O O' B) E = e0 → NonSS (augmentationIdealKernel u) (RingHom.id B) e0 → NonSS (augmentationIdealKernel u') (RingHom.id _) E`. Introduce `E e0 hE hEe h0`. Establish `h1 : NonSS (augmentationIdealKernel u) (Til.ι O O' B) E` using `BC.nonSS_field B B (Til O O' B) G0.frame.G₀ (augmentationIdealKernel u) (RingHom.id B) (Til.ι O O' B) e0 E hE (by rw [hEe, Ideal.comap_id]) hfinI h0`.

Use `BC.nonSS_mono B (Til O O' B) (Til O O' B) G0.frame.G₀ G0.frame.G₀ (MonoidHom.id _) (augmentationIdealKernel u) (augmentationIdealKernel u') (Til.ι O O' B) (RingHom.id _) E (fun g => ⟨g, rfl⟩) ?_ h1` and prove the remaining obligations. Introduce `z hz`. Rewrite using `[MonoidAlgebra.mapRingHom_id, MonoidAlgebra.mapDomainRingHom_id]`. Conclude with `BC.mem_span_map_e0ker_of_pair_maps l G0.frame O O' n r r' B (Til O O' B) u u' (Til.ι O O' B) hphi hrIp (fun a => Til.ι_algebraMap O O' B _) hu' z hz`. Establish `hds : ∀ (E : Ideal (Til O O' B)), DiscSt u.D (Ideal.comap (Til.ι O O' B) E) → DiscSt u'.D E`.

Introduce `E hE`. Rewrite using `[← hu'.1]`. Conclude with `((BC.discSt_map n B (Til O O' B) G0.frame.G₀ u.D).1 (Til.ι O O' B) E).2 hE`. Take `⟨q₁, hq₁, hq₁d, hJq₁, hq₁le⟩` from `hq1`. Take `⟨Q₁, hQ₁, hQ₁c, hQ₁le⟩` from `hdown (Pt' 0) q₁ (hPt 0).1 hq₁ (by rw [(hPt 0).2]; exact hq₁le)`.

Take `⟨Q, hQ, hQc, hQle⟩` from `hdown (Pt' (Fin.last h)) q (hPt _).1 hq (by rw [(hPt _).2]; exact hqle)`. Establish `hEp : ∀ i, (Ideal.map (Til.C O O' B) (Et i)).IsPrime ∧ Ideal.comap (Til.ι O O' B) (Ideal.map (Til.C O O' B) (Et i)) = e i` using `fun i => ⟨(hup _ (hEt i).1).1, (hup _ (hEt i).1).2.trans (hEt i).2.1⟩`. Establish `hq'` using `(hup Q hQ).2.trans hQc`. Establish `hfin` using `hmain (fun i => Ideal.map (Til.C O O' B) (Et i)) (fun i => ⟨(hEp i).1, hns _ _ (hEp i).1 (hEp i).2 (he i).2.1, hle _ _ (hEt i).2.2.1, hle _ _ (hEt i).2.2.2⟩) ⟨Ideal.map (Til.C O O' B) Q₁, (hup _ hQ₁).1, hds _ (by rw [(hup _ hQ₁).2, hQ₁c]; exact hq₁d), by rw [Ideal.map_le_iff_le_c …`. Break down `hst with hd | hn` into its components or cases.

Conclude with `Or.inl (hds _ (by rw [hq']; exact hd))`. Conclude with `Or.inr (hns _ _ (hup _ hQ).1 hq' hn))`. Introduce `b hb`. Rewrite using `[← hq']`. Conclude with `hfin (Ideal.mem_map_of_mem _ hb)`.
-/
theorem coreBC : CoreBC := by
  intro l _ L G0 T n O _ _ _ _ _ r B _ _ _ u J D A0 hl hP hAd hG h x hx
  obtain ⟨O', _, _, _, _, α, P, hco, hfin, hfree, hloc, hcard, hα, hPm, hPα, hsplit⟩ :=
    BC.oprime l O (x 0).x.K
  letI : Algebra ℤ_[l] O' := ((algebraMap O O').comp (algebraMap ℤ_[l] O)).toAlgebra
  haveI : IsScalarTower ℤ_[l] O O' := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  haveI : IsAdicComplete (maximalIdeal O) O := IsCoef.complete (l := l)
  haveI : Finite (ResidueField O) := IsCoef.finite (l := l)
  haveI : CharP (ResidueField O) l := IsCoef.char
  obtain ⟨⟨r', hr'⟩, hrr⟩ := BC.resid_bc l G0.frame O O' n r
  obtain ⟨hrIp, -, hrchi⟩ := hrr r' hr'
  obtain ⟨hTco, hιloc, hsm⟩ := BC.til_co O O' B
  obtain ⟨-, u', hu'⟩ := BC.pair_bc l G0.frame O O' n r r' hr' B (Til O O' B) (Til.ι O O' B)
    (Til.ι_algebraMap O O' B) u
  obtain ⟨A', hA'⟩ := BC.aut_bc l L G0 n O O' r r' B u u' J D T A0 hr' hu'
  have hphi := BC.phi0 l L G0 T hP
  have hAd' : Adapted (r := r') T :=
    ⟨fun g hg i => (hrchi i g).2 (hAd.1 g hg i), fun w => (hrIp w).trans (hAd.2 w)⟩
  have hG' : GenBy O' (pairVals u' ∪ {A'.b.lam (MvPowerSeries.X (Sum.inl ()))}) := by
    refine BC.gen_bc O O' B (pairVals u) _ hιloc hsm ?_ ?_ hG
    · rintro a (⟨i, g, rfl⟩ | ⟨v, i, g, rfl⟩)
      · left; left
        refine ⟨i, g, ?_⟩
        have h3 := ((CA.d_gmap u.D).2.2.1 (Til.ι O O' B) (MonoidAlgebra.single g 1)).2 i
        rw [MonoidAlgebra.mapRingHom_single, map_one, hu'.1] at h3
        exact h3.symm
      · left; right
        exact ⟨v, i, g, by rw [← hu'.2 v i]; rfl⟩
    · right; rw [hA']; rfl
  have hpr : ∀ i, (RingHom.ker (x i).f).IsPrime := fun i => RingHom.ker_isPrime _
  intro e he hq1 q hq hqle hst
  obtain ⟨⟨Pt', Et, hPt, hEt⟩, hdown⟩ := BC.chain_tens O O' B h (fun i => RingHom.ker (x i).f) e hpr
    (fun i => ⟨(he i).1, (he i).2.2⟩)
  have hl1 := fun i => BC.pt_lift l O O' α P B (x i).x.K (x i).f (Pt' i) hα hPm hPα
    (hsplit _ (hx i)) (hcard.trans (hx i).symm) (hPt i).1 (hPt i).2
  choose inst f' hsurj hfι hfs hker using hl1
  have hmaps : ∀ i, u'.Maps (f' i).toRingHom (GDet.ofRep (mat (x i).x.ρ)) (x i).x.ψ := by
    intro i
    have hc : (f' i).toRingHom.comp (Til.ι O O' B) = (x i).f.toRingHom := RingHom.ext (hfι i)
    refine ⟨?_, fun v j => ?_⟩
    · rw [← hu'.1, (CA.d_gmap u.D).2.1, hc]
      exact (x i).maps.1
    · rw [← hu'.2 v j, ← (x i).maps.2 v j, ← hc]
      rfl
  let x' : Fin (h + 1) → Pt T u' (D + n * T.q) := fun i =>
    @Pt.mk _ _ _ _ T _ _ _ _ _ r' _ _ _ _ u' _ (x i).x (inst i) (x i).k (x i).al (x i).eig (x i).b1 (x i).b2
      (f' i) (hmaps i)
  have hmain := core l L G0 T n O' r' (Til O O' B) u' _ D A' hl hP hAd' hG' h x'
    (fun i => ⟨hsurj i, by rw [hA']; exact hfs i⟩)
  have hup : ∀ Q : Ideal (O' ⊗[O] B), Q.IsPrime →
      (Ideal.map (Til.C O O' B) Q).IsPrime ∧
        Ideal.comap (Til.ι O O' B) (Ideal.map (Til.C O O' B) Q) =
          Ideal.comap Algebra.TensorProduct.includeRight Q :=
    fun Q hQ => BC.til_prime O O' B Q hQ
  have hle : ∀ (Q : Ideal (O' ⊗[O] B)) i, Q ≤ Pt' i →
      Ideal.map (Til.C O O' B) Q ≤ RingHom.ker (x' i).f := by
    intro Q i hQi
    rw [Ideal.map_le_iff_le_comap]
    exact hQi.trans (hker i).ge
  have hfinI : ∃ s : Finset G0.frame.G₀, ∀ y : MonoidAlgebra B G0.frame.G₀, ∃ c : G0.frame.G₀ → B,
      y - ∑ g ∈ s, MonoidAlgebra.single g (c g) ∈ TwoSidedIdeal.span (augmentationIdealKernel u) := by
    obtain ⟨s, hs⟩ := (BC.pair_mf l G0.frame O n r B u hphi).2.2 (pairGens u)
    exact ⟨s, fun y => (hs y).imp fun c hc => TwoSidedIdeal.subset_span hc⟩
  have hns : ∀ (E : Ideal (Til O O' B)) (e0 : Ideal B), E.IsPrime →
      Ideal.comap (Til.ι O O' B) E = e0 → NonSS (augmentationIdealKernel u) (RingHom.id B) e0 →
        NonSS (augmentationIdealKernel u') (RingHom.id _) E := by
    intro E e0 hE hEe h0
    have h1 : NonSS (augmentationIdealKernel u) (Til.ι O O' B) E :=
      BC.nonSS_field B B (Til O O' B) G0.frame.G₀ (augmentationIdealKernel u) (RingHom.id B) (Til.ι O O' B) e0 E hE
        (by rw [hEe, Ideal.comap_id]) hfinI h0
    refine BC.nonSS_mono B (Til O O' B) (Til O O' B) G0.frame.G₀ G0.frame.G₀ (MonoidHom.id _)
      (augmentationIdealKernel u) (augmentationIdealKernel u') (Til.ι O O' B) (RingHom.id _) E (fun g => ⟨g, rfl⟩) ?_ h1
    intro z hz
    rw [MonoidAlgebra.mapRingHom_id, MonoidAlgebra.mapDomainRingHom_id]
    exact BC.mem_span_map_e0ker_of_pair_maps l G0.frame O O' n r r' B (Til O O' B) u u' (Til.ι O O' B) hphi hrIp
      (fun a => Til.ι_algebraMap O O' B _) hu' z hz
  have hds : ∀ (E : Ideal (Til O O' B)), DiscSt u.D (Ideal.comap (Til.ι O O' B) E) → DiscSt u'.D E := by
    intro E hE
    rw [← hu'.1]
    exact ((BC.discSt_map n B (Til O O' B) G0.frame.G₀ u.D).1 (Til.ι O O' B) E).2 hE
  obtain ⟨q₁, hq₁, hq₁d, hJq₁, hq₁le⟩ := hq1
  obtain ⟨Q₁, hQ₁, hQ₁c, hQ₁le⟩ := hdown (Pt' 0) q₁ (hPt 0).1 hq₁ (by rw [(hPt 0).2]; exact hq₁le)
  obtain ⟨Q, hQ, hQc, hQle⟩ := hdown (Pt' (Fin.last h)) q (hPt _).1 hq (by rw [(hPt _).2]; exact hqle)
  have hEp : ∀ i, (Ideal.map (Til.C O O' B) (Et i)).IsPrime ∧
      Ideal.comap (Til.ι O O' B) (Ideal.map (Til.C O O' B) (Et i)) = e i := fun i =>
    ⟨(hup _ (hEt i).1).1, (hup _ (hEt i).1).2.trans (hEt i).2.1⟩
  have hq' := (hup Q hQ).2.trans hQc
  have hfin := hmain (fun i => Ideal.map (Til.C O O' B) (Et i))
    (fun i => ⟨(hEp i).1, hns _ _ (hEp i).1 (hEp i).2 (he i).2.1, hle _ _ (hEt i).2.2.1,
      hle _ _ (hEt i).2.2.2⟩)
    ⟨Ideal.map (Til.C O O' B) Q₁, (hup _ hQ₁).1,
      hds _ (by rw [(hup _ hQ₁).2, hQ₁c]; exact hq₁d),
      by rw [Ideal.map_le_iff_le_comap, (hup _ hQ₁).2, hQ₁c]; exact hJq₁,
      hle _ _ hQ₁le⟩
    (Ideal.map (Til.C O O' B) Q) (hup _ hQ).1 (hle _ _ hQle)
    (by
      rcases hst with hd | hn
      · exact Or.inl (hds _ (by rw [hq']; exact hd))
      · exact Or.inr (hns _ _ (hup _ hQ).1 hq' hn))
  intro b hb
  rw [← hq']
  exact hfin (Ideal.mem_map_of_mem _ hb)

end UpperTheory.V.Pa

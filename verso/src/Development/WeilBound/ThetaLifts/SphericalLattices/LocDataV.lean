import Development.WeilBound.ThetaLifts.SphericalLattices.HoweDefs
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFinMapsOfForall
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InertPlaceLocalFieldDataExistsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InertPlaceUnimodularHermitianFrameCoordinatesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLocalSchroedingerFamilyAtPlaceStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLocalWeilOperatorsSupportedAtPlaceStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalWeilOperatorNormalisesSchroedingerOperatorStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InertPlaceLatticeVacuumFixedAndUniqueStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InertPlaceBothStabilisersFixVacuumStatement

noncomputable section

namespace PositivityTheory.Sph

open scoped Matrix TensorProduct
open NumberField IsDedekindDomain Topology GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.KFinLoc

/- English proof (translation)
Take `⟨L, iF, iC, iVl, iCS, ϖ, σL, q, δ, ψL, ι, hunr, hodd, hδ, hpi, hpn, hinj, him, hmul, hσ, hint, hψ⟩` from `GlobalTheory.T.inert_place_local_field_data_exists F E σ B hT.base v w hin`. Take `⟨JS, JT, Xm, iV, iW, hiS, hiT, hhS, hhT, hψ2, himX, hlat1, hlat2, hact, hUV, hUW, hKV, hKW⟩` from `GlobalTheory.T.inertPlace_unimodular_hermitianFrame_coordinates F E σ B a a' G hT.base hT.geo v w hin L ϖ σL q δ ψL ι hunr hodd hδ hinj him hmul hσ hint hψ`. Take `⟨ρ, hρ0, hρmul, hρA, hρspan⟩` from `GlobalTheory.T.exists_local_schroedinger_family_at_place F v B.ψ hT.base.std (hT.base.inert v w hin).2.2 G.M.co (Matrix (Fin (a + a')) (Fin a) L) Xm (fun x y => ψL ((GlobalTheory.Hk3.locH σL δ JS JT x y + σL (GlobalTheory.Hk3.locH σL δ JS JT x y)) / 2)) himX hψ2`. Set `j` to `iV.prodMap iW`. Take `⟨ω, hω⟩` from `GlobalTheory.T.exists_localWeilOperators_supportedAtPlace F E σ B a a' G X om om' hT v _ j (fun g => ⟨hUV g.1, hUW g.2⟩)`.

Establish `hnorm` using `GlobalTheory.T.localWeilOperator_normalises_schroedingerOperator F E σ B a a' G X om om' hT v _ Xm (fun y => (himX _).2 ⟨y, rfl⟩) ρ hρA _ j ω hω (fun g x => ((g.2 : GL (Fin (a + a')) L) : Matrix (Fin (a + a')) (Fin (a + a')) L) * x * (((g.1 : GL (Fin a) L)⁻¹ : GL (Fin a) L) : Mat …`. Take `⟨hvac, huniq⟩` from `GlobalTheory.T.inertPlace_latticeVacuum_fixed_and_unique F E σ B a a' G X om om' hT v w hin hvT _ Xm (fun u => ∀ i j, u i j ∈ Formalism.UG.intL L) hlat1 hlat2 ρ hρA`. Establish `hfix` using `GlobalTheory.T.inert_place_both_stabilisers_fix_vacuum F E σ B a a' G X om om' hT v w hin hvT`. Establish `hvSB` using `(hT.geo.hM.vac v).1`. Establish `hv0` using `(hT.geo.hM.vac v).2.1`.

Set `s : SB (Fin a × Fin (a + a') → Fv F v)` to `⟨G.M.vac v, hvSB⟩`. Establish `hs0 : s ≠ 0` using `fun h => hv0 (congrArg Subtype.val h)`. Establish `hspan` using `hρspan s hs0`. Establish `hωs : ∀ (g : Formalism.UG.UJ σL (JS : Matrix (Fin a) (Fin a) L)) (h : Formalism.UG.UJ σL (JT : Matrix (Fin (a + a')) (Fin (a + a')) L)), (g : GL (Fin a) L) ∈ Formalism.UG.GLint (Fin a) (Formalism.UG.intL L) → (h : GL (Fin (a + a')) L) ∈ Formalism.UG.GLint (Fin (a + a')) (Formalis …`. Introduce `g h hg hh`.

Conclude with `Subtype.ext ((hω (g, h) s (G.M.vac v)).1 (hfix _ (hKV g hg) _ (hKW h hh))).symm`. Use `⟨L, iF, iC, iVl, iCS, ϖ, σL, q, δ, JS, JT, ψL, ρ, ω, iV, iW, s, ?_, hs0, fun u hu => hvac s rfl u hu, hspan, rfl, hUV, hUW, hKV, hKW, fun g h m φ₁ _ => (hω (g, h) m φ₁).trans eq_comm⟩` and prove the remaining obligations. Conclude with `{ unr := hunr odd := hodd intS := hiS intT := hiT hermS := hhS hermT := hhT delta := hδ psi_int := hpi psi_ne := hpn rho_zero := hρ0 rho_mul := hρmul span := by`. Rewrite using `[eq_top_iff, ← hspan]`. Use `Submodule.span_mono ?_` and prove the remaining obligations.

Introduce and unpack `_ ⟨x, rfl⟩`. Conclude with `⟨x, s, fun u hu => hvac s rfl u hu, rfl⟩`. Use `norm := fun g h x => hnorm (g, h) x`. Use `fix := by`. Introduce `g h hg hh s' hs'`.

Take `⟨c, hc⟩` from `huniq s' hs'`. Establish `e : s' = c • s` using `Subtype.ext hc`. Rewrite using `[e, map_smul, hωs g h hg hh] }`.
-/
theorem locDataV {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
    {B : Base F E} {a a' : ℕ} {G : Geo σ a a'} {X : Chars F E} {om : Rep σ G.V G.W} {om' : Rep σ G.V' G.W}
    (hT : IsTriple B G X om om') {v : Pl F} {w : HeightOneSpectrum (𝓞 E)} (hin : Formalism.UG.IsInertAt F E v w)
    (hvT : v ∉ X.T) : LocData G.M om v := by
  obtain ⟨L, iF, iC, iVl, iCS, ϖ, σL, q, δ, ψL, ι, hunr, hodd, hδ, hpi, hpn, hinj, him, hmul, hσ, hint, hψ⟩ :=
    GlobalTheory.T.inert_place_local_field_data_exists F E σ B hT.base v w hin
  obtain ⟨JS, JT, Xm, iV, iW, hiS, hiT, hhS, hhT, hψ2, himX, hlat1, hlat2, hact, hUV, hUW, hKV, hKW⟩ :=
    GlobalTheory.T.inertPlace_unimodular_hermitianFrame_coordinates F E σ B a a' G hT.base hT.geo v w hin L ϖ σL q δ ψL ι hunr hodd hδ hinj him hmul hσ hint hψ
  obtain ⟨ρ, hρ0, hρmul, hρA, hρspan⟩ := GlobalTheory.T.exists_local_schroedinger_family_at_place F v B.ψ hT.base.std (hT.base.inert v w hin).2.2 G.M.co
    (Matrix (Fin (a + a')) (Fin a) L) Xm
    (fun x y => ψL ((GlobalTheory.Hk3.locH σL δ JS JT x y + σL (GlobalTheory.Hk3.locH σL δ JS JT x y)) / 2)) himX hψ2
  let j := iV.prodMap iW
  obtain ⟨ω, hω⟩ := GlobalTheory.T.exists_localWeilOperators_supportedAtPlace F E σ B a a' G X om om' hT v _ j (fun g => ⟨hUV g.1, hUW g.2⟩)
  have hnorm := GlobalTheory.T.localWeilOperator_normalises_schroedingerOperator F E σ B a a' G X om om' hT v _ Xm (fun y => (himX _).2 ⟨y, rfl⟩) ρ hρA _ j ω hω
    (fun g x => ((g.2 : GL (Fin (a + a')) L) : Matrix (Fin (a + a')) (Fin (a + a')) L) * x *
      (((g.1 : GL (Fin a) L)⁻¹ : GL (Fin a) L) : Matrix (Fin a) (Fin a) L)) (fun g x => hact g.1 g.2 x)
  obtain ⟨hvac, huniq⟩ := GlobalTheory.T.inertPlace_latticeVacuum_fixed_and_unique F E σ B a a' G X om om' hT v w hin hvT _ Xm
    (fun u => ∀ i j, u i j ∈ Formalism.UG.intL L) hlat1 hlat2 ρ hρA
  have hfix := GlobalTheory.T.inert_place_both_stabilisers_fix_vacuum F E σ B a a' G X om om' hT v w hin hvT
  have hvSB := (hT.geo.hM.vac v).1
  have hv0 := (hT.geo.hM.vac v).2.1
  let s : SB (Fin a × Fin (a + a') → Fv F v) := ⟨G.M.vac v, hvSB⟩
  have hs0 : s ≠ 0 := fun h => hv0 (congrArg Subtype.val h)
  have hspan := hρspan s hs0
  have hωs : ∀ (g : Formalism.UG.UJ σL (JS : Matrix (Fin a) (Fin a) L)) (h : Formalism.UG.UJ σL (JT : Matrix (Fin (a + a')) (Fin (a + a')) L)),
      (g : GL (Fin a) L) ∈ Formalism.UG.GLint (Fin a) (Formalism.UG.intL L) →
      (h : GL (Fin (a + a')) L) ∈ Formalism.UG.GLint (Fin (a + a')) (Formalism.UG.intL L) → ω (g, h) s = s := by
    intro g h hg hh
    exact Subtype.ext ((hω (g, h) s (G.M.vac v)).1 (hfix _ (hKV g hg) _ (hKW h hh))).symm
  refine ⟨L, iF, iC, iVl, iCS, ϖ, σL, q, δ, JS, JT, ψL, ρ, ω, iV, iW, s, ?_, hs0, fun u hu => hvac s rfl u hu, hspan, rfl,
    hUV, hUW, hKV, hKW, fun g h m φ₁ _ => (hω (g, h) m φ₁).trans eq_comm⟩
  exact
    { unr := hunr
      odd := hodd
      intS := hiS
      intT := hiT
      hermS := hhS
      hermT := hhT
      delta := hδ
      psi_int := hpi
      psi_ne := hpn
      rho_zero := hρ0
      rho_mul := hρmul
      span := by
        rw [eq_top_iff, ← hspan]
        refine Submodule.span_mono ?_
        rintro _ ⟨x, rfl⟩
        exact ⟨x, s, fun u hu => hvac s rfl u hu, rfl⟩
      norm := fun g h x => hnorm (g, h) x
      fix := by
        intro g h hg hh s' hs'
        obtain ⟨c, hc⟩ := huniq s' hs'
        have e : s' = c • s := Subtype.ext hc
        rw [e, map_smul, hωs g h hg hh] }

end PositivityTheory.Sph

end

import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SideEigenFrobenius
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.HeckeOpen
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ForcedByAutomorphicSemisimpleData
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.HeckeOpenWithLoc

set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial GlobalTheory.CoefDuty
noncomputable section
namespace GlobalTheory.EigOnto
set_option maxHeartbeats 2000000 in
set_option synthInstance.maxHeartbeats 400000 in
/- English proof (translation)
Introduce `hstdP D cf jE A low Pq S hL eig θ Bs M C tp hCh hMt hstar hexp hsplit hcheb big L hB j w h1 h2 hw c hc`. Take `⟨Sp, ⟨Au⟩, -⟩` from `hB`. Take `⟨-, y, hy, hcy⟩` from `hc`. Use `haveI := Formalism.L2.finite_chooseBasisIndex (D := D) j w`. Set `b` to `Module.Free.chooseBasis D.what₂.LL (D.what₂.MtL (D.what₂.muTw w) j)`.

Establish `hjb` using `D.what₂.jMt_basis (D.what₂.muTw w) j b`. Establish `hb` using `Sp.B.iV_basis j w b`. Choose the witnesses or unpack the hypotheses as in `⟨a⟩ : Nonempty (Module.Free.ChooseBasisIndex D.what₂.LL (D.what₂.MtL (D.what₂.muTw w) j)) := by`. Assume the negation of the conclusion as `hne`. Rewrite `hne` using `[not_nonempty_iff]`.

Apply `hy` to reduce the goal to its premises. Establish `hy' : y ∈ Submodule.span ℂ (Set.range fun a => D.what₂.jMt (D.what₂.muTw w) j (b a))`. Rewrite using `[hjb.2]`. Conclude with `Submodule.mem_top`. Rewrite `hy'` using `[Set.range_eq_empty, Submodule.span_empty, Submodule.mem_bot]`.

Conclude with `hy'`. Use `haveI : Nontrivial (Sp.B.V j w) := ⟨⟨Sp.B.iV j w (b a), 0, hb.1.ne_zero a⟩⟩`. Take `⟨I0, hI0⟩` from `Ideal.exists_maximal (heckeAlg Sp.B j w)`. Take `⟨i0, hi0, -⟩` from `Sp.mx_all j w h1 h2 hw I0 hI0`. Establish `hinjC : Function.Injective (Sp.iotaC j w)`.

Introduce `a1 a2 hab`. Take `⟨a1', rfl⟩` from `(Sp.phO j w i0 hi0).surjective a1`. Take `⟨a2', rfl⟩` from `(Sp.phO j w i0 hi0).surjective a2`. Rewrite `hab` using `[← Sp.iotaC_coh, ← Sp.iotaC_coh]`. Use `congr 1`.

Conclude with `IsFractionRing.injective _ _ ((Sp.iq i0).injective ((qCast _ _).injective hab))`. Set `φ : FractionRing (Sp.B.Oc j w) →+* ℂ` to `IsFractionRing.lift hinjC`. Establish `hφalg : ∀ z, φ (algebraMap _ _ z) = Sp.iotaC j w z` using `fun z => IsFractionRing.lift_algebraMap hinjC z`. Establish `hφK : φ.comp (Sp.phK j w i0 hi0).toRingHom = (qCast (L.X.nd.w_l i0) (A.pl.ι (L.X.nd.w i0))).toRingHom.comp (Sp.iq i0)`. Apply `IsLocalization.ringHom_ext (nonZeroDivisors (L.X.nd.O i0))` to reduce the goal to its premises.

Use extensionality with `z`. Simplify using `only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom, Sp.phK_alg, hφalg]`. Conclude with `(Sp.iotaC_coh j w i0 hi0 z).symm`. Establish `hφ : ∀ x, φ (Sp.B.ec j w x) = D.what₂.embLL x`. Introduce `x`.

Rewrite using `[← Sp.phK_emb j w i0 hi0 x, ← Sp.iq_LL i0 x]`. Conclude with `congrArg (fun f : FractionRing (L.X.nd.O i0) →+* ℂ => f (L.X.nd.embK i0 x)) hφK`. Take `⟨Hk, -⟩` from `_root_.GlobalTheory.FitHecke.heckeOpen_withLoc_alt D cf jE A low Pq S hL eig θ Bs M C tp hCh hMt hstar hexp hsplit hcheb big L Sp Au`. Take `⟨ej, ew⟩` from `(L.X.nd.locs_mem j w i0).1 hi0`. Establish `hμ0 : L.X.nd.mu i0 = D.what₂.muTw w` using `by rw [L.X.nd.mu_w i0, ew]`.

Establish `hQk : Hk.cover.B.Qc j w = C.Q w` using `(Hk.cover.Q_eq j w i0 hi0).symm.trans ((Sp.Q_eq j w i0 hi0).trans (Sp.Qc_eq j w))`. Establish `lin : ∀ v k (s : SplitPlace D.host.E) (ϖ : s.v.adicCompletion (maximalRealSubfield D.host.E)), GenAt D (D.what₂.places.resChar w) (C.Q w) v k → IsConjPl D.host v s.w → IsUnif D.host.E s.v ϖ → ∀ (z : ℂ) (f f' : GAf D.host.E D.R.nV → (M (D.what₂.muTw w) j h1 h2).wt.W), NG.tN (M (D. …`. Introduce `v k s ϖ hvk hc hu`. Establish `H` using `GlobalTheory.LiftPoint.tN_lin (withLoc L) (mtL L M) Hk.hecke Hk.cover (j := j) (w := w) (i := i0) hi0 v k s ϖ (by rw [hQk]; exact hvk) hc hu`. Conclude with `GlobalTheory.FitHecke.mt_transport M (fun μ jj m => ∀ (z : ℂ) (f f' : GAf D.host.E D.R.nV → m.wt.W), NG.tN m.J s ϖ k (z • f + f') = z • NG.tN m.J s ϖ k f + NG.tN m.J s ϖ k f') hμ0 ej (L.X.nd.j_range i0).1 (L.X.nd.j_range i0).2 h1 h2 H`.

Establish `hstd : HeckeStdTw Sp.B` using `heckeStdTw_of_std Sp.std`. Establish `hLoc : LocPl D j w` using `Or.inl hw`. Establish `hgen : ∀ v k, GenAt D (D.what₂.places.resChar w) (Sp.B.Qc j w) v k → GenAt D (D.what₂.places.resChar w) (C.Q w) v k` using `fun v k h => by rw [← Sp.Qc_eq j w]; exact h`. Establish `key : ∀ v k, GenAt D (D.what₂.places.resChar w) (Sp.B.Qc j w) v k → ∃ κ : Sp.B.Oc j w, φ (algebraMap _ _ κ) = c v k`. Introduce `v k hvk`.

Take `⟨s, ϖ, hc, hu⟩` from `GlobalTheory.SplitConjPlace.splitEx_all D v hvk.1`. Take `⟨tC, htC1, htC2⟩` from `GlobalTheory.LiftPoint.tC_exists D M Sp.B hstd j w (D.what₂.muTw w) rfl h1 h2 hLoc φ hφ v k hvk`. Establish `ht0 : tC y = c v k • y`. Apply `(M (D.what₂.muTw w) j h1 h2).real_inj` to reduce the goal to its premises. Rewrite using `[← htC2 s ϖ hc hu (lin v k s ϖ (hgen v k hvk) hc hu) y, hcy v k s ϖ (hgen v k hvk) hc hu, map_smul]`.

Conclude with `htC1 (c v k) y hy ht0`. Set `κF : PlE D.host → ℕ → Sp.B.Oc j w` to `fun v k => if hvk : GenAt D (D.what₂.places.resChar w) (Sp.B.Qc j w) v k then Classical.choose (key v k hvk) else 0`. Establish `hκF : ∀ v k (hvk : GenAt D (D.what₂.places.resChar w) (Sp.B.Qc j w) v k), φ (algebraMap _ _ (κF v k)) = c v k`. Introduce `v k hvk`. Simplify using `only [κF, dif_pos hvk]`.

Conclude with `Classical.choose_spec (key v k hvk)`. Take `⟨e, hene, he⟩` from `GlobalTheory.PtLocalEig.eig_descends D M Sp.B j w (D.what₂.muTw w) h1 h2 rfl φ hφ (fun v k => algebraMap _ _ (κF v k)) y hy (by`. Introduce `v k hvk`. Take `⟨s, ϖ, hc, hu⟩` from `GlobalTheory.SplitConjPlace.splitEx_all D v hvk.1`. Use `⟨s, ϖ, hc, hu, lin v k s ϖ (hgen v k hvk) hc hu, ?_⟩` and prove the remaining obligations.

Rewrite using `[hcy v k s ϖ (hgen v k hvk) hc hu, hκF v k hvk])`. Establish `hinjK : Function.Injective (algebraMap (Sp.B.Oc j w) (FractionRing (Sp.B.Oc j w)))` using `IsFractionRing.injective _ _`. Take `⟨ψ, hψ, hψW⟩` from `GlobalTheory.PtLocalEig.pt_of_eigvec (heckeGens Sp.B j w) e hene hinjK (by`. Introduce and unpack `_ ⟨v, k, hvk, rfl⟩`. Conclude with `⟨κF v k, he v k hvk⟩)`.

Establish `hψv : ∀ v k (hvk : GenAt D (D.what₂.places.resChar w) (Sp.B.Qc j w) v k), ψ ⟨Sp.B.hK j w v k, Algebra.subset_adjoin ⟨v, k, hvk, rfl⟩⟩ = κF v k`. Introduce `v k hvk`. Apply `hinjK` to reduce the goal to its premises. Establish `e1` using `hψ ⟨Sp.B.hK j w v k, Algebra.subset_adjoin ⟨v, k, hvk, rfl⟩⟩`. Establish `e2` using `he v k hvk`.

Express the relevant statement in the definitionally equal form `Sp.B.hK j w v k e = _ at e1`. Rewrite `e1` using `[e2]`. Conclude with `(smul_left_injective _ hene e1).symm`. Establish `hW : NCov.W (heckeAlg Sp.B j w) (NCov.pt ψ) ≠ ⊥`. Introduce `h0`.

Apply `hene` to reduce the goal to its premises. Establish `h3` using `hψW`. Rewrite `h3` using `[h0]`. Conclude with `(Submodule.mem_bot _).1 h3`. Take `⟨i, hi, hmx⟩` from `Sp.mx_all j w h1 h2 hw (NCov.cls ψ) (NCov.cls_isMaximal ψ)`.

Use `⟨i, hi, (Sp.ptX j w i hi).symm ⟨ψ, hmx.symm, hW⟩, fun v k hvk => ?_⟩` and prove the remaining obligations. Establish `hvk' : GenAt D (D.what₂.places.resChar w) (Sp.B.Qc j w) v k` using `by rw [Sp.Qc_eq j w]; exact hvk`. Establish `e1 : ∀ z, iotaO L.X.nd L.Y.naut i z = Sp.iotaC j w (Sp.phO j w i hi z)`. Introduce `z`. Unfold `iotaO`.

Rewrite using `[RingHom.comp_apply, RingHom.comp_apply, Au.iotaQ i, Au.iotaQC i]`. Conclude with `Sp.iotaC_coh j w i hi z`. Rewrite using `[e1, Sp.ptX_hT j w i hi _ v k hvk', Equiv.apply_symm_apply]`. Use `show Sp.iotaC j w (ψ ⟨Sp.B.hK j w v k, _⟩) = c v k`. Rewrite using `[hψv v k hvk', ← hφalg, hκF v k hvk']`.
-/
theorem main_alt_alt : HeckeStdPlain → ∀ (D : D7) (cf : CharFrame D) (jE : D.host.E →+* Qb) (A : _root_.GlobalTheory.HeightCounting.CharFrameHostEmbedding D cf jE) (low : Finset ℕ) (Pq : HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E)) → PlE D.host) (S : RatDat D.ntw) (hL : ∀ j, ℕ → PlE D.host → Module.End D.what₂.LL (S.WL j)) (eig : ℕ → D.what₂.FT → ℕ → PlE D.host → ↥D.LL0) (θ : ∀ kk : Fin 2, Multiplicative (ZMod (D.host.g kk)) →* (↥D.LL0)ˣ) (Bs : SideB D cf A.row low Pq S hL eig θ) (M : MtFam D) (C : NChoice D) (tp : TupTied D cf C), ChoiceSide D cf M Bs.exp C tp → MtInput D M tp.tup C.Q → (∀ x : D.LL0, star (x : D.what₂.LL) ∈ D.LL0) → (∀ j g, ∃ z : ℤ, eExp D j g = z) → (∀ v, v ∈ placesOver D.host.E D.host.pde ∨ v ∈ placesOver D.host.E D.host.pde' → IsSplitPl D.host v) → GlobalTheory.RowTie.ChebSplit D.nd → ∀ (big : D.what₂.places.Pl → Finset ℂ) (L : LocAll (lay0 D)), _root_.GlobalTheory.CoefDuty.BuiltAlt A M C tp.tup big L → ∀ (j : ℕ) (w : D.what₂.places.Pl) (h1 : 1 ≤ j) (h2 : j ≤ D.R.m), D.what₂.muAt w ≠ D.what₂.mu0 → ∀ c ∈ EigSet (M (D.what₂.muTw w) j h1 h2) (D.what₂.places.resChar w) (C.Q w), ∃ i ∈ L.X.nd.locs j w, ∃ x : L.X.nd.X i, ∀ (v : PlE D.host) (k : ℕ), GenAt D (D.what₂.places.resChar w) (C.Q w) v k → iotaO L.X.nd L.Y.naut i ((L.X.nd.hT i v k : L.X.nd.X i → L.X.nd.O i) x) = c v k := by
  intro hstdP D cf jE A low Pq S hL eig θ Bs M C tp hCh hMt hstar hexp hsplit hcheb big L hB j w h1 h2 hw c hc
  classical
  obtain ⟨Sp, ⟨Au⟩, -⟩ := hB
  obtain ⟨-, y, hy, hcy⟩ := hc
  haveI := Formalism.L2.finite_chooseBasisIndex (D := D) j w
  let b := Module.Free.chooseBasis D.what₂.LL (D.what₂.MtL (D.what₂.muTw w) j)
  have hjb := D.what₂.jMt_basis (D.what₂.muTw w) j b
  have hb := Sp.B.iV_basis j w b
  obtain ⟨a⟩ : Nonempty (Module.Free.ChooseBasisIndex D.what₂.LL (D.what₂.MtL (D.what₂.muTw w) j)) := by
    by_contra hne
    rw [not_nonempty_iff] at hne
    apply hy
    have hy' : y ∈ Submodule.span ℂ (Set.range fun a => D.what₂.jMt (D.what₂.muTw w) j (b a)) := by
      rw [hjb.2]; exact Submodule.mem_top
    rw [Set.range_eq_empty, Submodule.span_empty, Submodule.mem_bot] at hy'
    exact hy'
  haveI : Nontrivial (Sp.B.V j w) := ⟨⟨Sp.B.iV j w (b a), 0, hb.1.ne_zero a⟩⟩
  obtain ⟨I0, hI0⟩ := Ideal.exists_maximal (heckeAlg Sp.B j w)
  obtain ⟨i0, hi0, -⟩ := Sp.mx_all j w h1 h2 hw I0 hI0
  have hinjC : Function.Injective (Sp.iotaC j w) := by
    intro a1 a2 hab
    obtain ⟨a1', rfl⟩ := (Sp.phO j w i0 hi0).surjective a1
    obtain ⟨a2', rfl⟩ := (Sp.phO j w i0 hi0).surjective a2
    rw [← Sp.iotaC_coh, ← Sp.iotaC_coh] at hab
    congr 1
    exact IsFractionRing.injective _ _ ((Sp.iq i0).injective ((qCast _ _).injective hab))
  let φ : FractionRing (Sp.B.Oc j w) →+* ℂ := IsFractionRing.lift hinjC
  have hφalg : ∀ z, φ (algebraMap _ _ z) = Sp.iotaC j w z := fun z => IsFractionRing.lift_algebraMap hinjC z
  have hφK : φ.comp (Sp.phK j w i0 hi0).toRingHom =
      (qCast (L.X.nd.w_l i0) (A.pl.ι (L.X.nd.w i0))).toRingHom.comp (Sp.iq i0) := by
    apply IsLocalization.ringHom_ext (nonZeroDivisors (L.X.nd.O i0))
    ext z
    simp only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom, Sp.phK_alg, hφalg]
    exact (Sp.iotaC_coh j w i0 hi0 z).symm
  have hφ : ∀ x, φ (Sp.B.ec j w x) = D.what₂.embLL x := by
    intro x
    rw [← Sp.phK_emb j w i0 hi0 x, ← Sp.iq_LL i0 x]
    exact congrArg (fun f : FractionRing (L.X.nd.O i0) →+* ℂ => f (L.X.nd.embK i0 x)) hφK
  obtain ⟨Hk, -⟩ := _root_.GlobalTheory.FitHecke.heckeOpen_withLoc_alt D cf jE A low Pq S hL eig θ Bs M C tp hCh hMt hstar hexp hsplit hcheb
    big L Sp Au
  obtain ⟨ej, ew⟩ := (L.X.nd.locs_mem j w i0).1 hi0
  have hμ0 : L.X.nd.mu i0 = D.what₂.muTw w := by rw [L.X.nd.mu_w i0, ew]
  have hQk : Hk.cover.B.Qc j w = C.Q w :=
    (Hk.cover.Q_eq j w i0 hi0).symm.trans ((Sp.Q_eq j w i0 hi0).trans (Sp.Qc_eq j w))
  have lin : ∀ v k (s : SplitPlace D.host.E) (ϖ : s.v.adicCompletion (maximalRealSubfield D.host.E)),
      GenAt D (D.what₂.places.resChar w) (C.Q w) v k → IsConjPl D.host v s.w → IsUnif D.host.E s.v ϖ →
      ∀ (z : ℂ) (f f' : GAf D.host.E D.R.nV → (M (D.what₂.muTw w) j h1 h2).wt.W),
        NG.tN (M (D.what₂.muTw w) j h1 h2).J s ϖ k (z • f + f') =
          z • NG.tN (M (D.what₂.muTw w) j h1 h2).J s ϖ k f + NG.tN (M (D.what₂.muTw w) j h1 h2).J s ϖ k f' := by
    intro v k s ϖ hvk hc hu
    have H := GlobalTheory.LiftPoint.tN_lin (withLoc L) (mtL L M) Hk.hecke Hk.cover (j := j) (w := w) (i := i0) hi0 v k s ϖ
      (by rw [hQk]; exact hvk) hc hu
    exact GlobalTheory.FitHecke.mt_transport M (fun μ jj m => ∀ (z : ℂ) (f f' : GAf D.host.E D.R.nV → m.wt.W),
        NG.tN m.J s ϖ k (z • f + f') = z • NG.tN m.J s ϖ k f + NG.tN m.J s ϖ k f') hμ0 ej
      (L.X.nd.j_range i0).1 (L.X.nd.j_range i0).2 h1 h2 H
  have hstd : HeckeStdTw Sp.B := heckeStdTw_of_std Sp.std
  have hLoc : LocPl D j w := Or.inl hw
  have hgen : ∀ v k, GenAt D (D.what₂.places.resChar w) (Sp.B.Qc j w) v k →
      GenAt D (D.what₂.places.resChar w) (C.Q w) v k := fun v k h => by rw [← Sp.Qc_eq j w]; exact h
  have key : ∀ v k, GenAt D (D.what₂.places.resChar w) (Sp.B.Qc j w) v k →
      ∃ κ : Sp.B.Oc j w, φ (algebraMap _ _ κ) = c v k := by
    intro v k hvk
    obtain ⟨s, ϖ, hc, hu⟩ := GlobalTheory.SplitConjPlace.splitEx_all D v hvk.1
    obtain ⟨tC, htC1, htC2⟩ := GlobalTheory.LiftPoint.tC_exists D M Sp.B hstd j w (D.what₂.muTw w) rfl h1 h2 hLoc φ hφ v k hvk
    have ht0 : tC y = c v k • y := by
      apply (M (D.what₂.muTw w) j h1 h2).real_inj
      rw [← htC2 s ϖ hc hu (lin v k s ϖ (hgen v k hvk) hc hu) y, hcy v k s ϖ (hgen v k hvk) hc hu, map_smul]
    exact htC1 (c v k) y hy ht0
  let κF : PlE D.host → ℕ → Sp.B.Oc j w := fun v k =>
    if hvk : GenAt D (D.what₂.places.resChar w) (Sp.B.Qc j w) v k then Classical.choose (key v k hvk) else 0
  have hκF : ∀ v k (hvk : GenAt D (D.what₂.places.resChar w) (Sp.B.Qc j w) v k), φ (algebraMap _ _ (κF v k)) = c v k := by
    intro v k hvk
    simp only [κF, dif_pos hvk]
    exact Classical.choose_spec (key v k hvk)
  obtain ⟨e, hene, he⟩ := GlobalTheory.PtLocalEig.eig_descends D M Sp.B j w (D.what₂.muTw w) h1 h2 rfl φ hφ
    (fun v k => algebraMap _ _ (κF v k)) y hy (by
      intro v k hvk
      obtain ⟨s, ϖ, hc, hu⟩ := GlobalTheory.SplitConjPlace.splitEx_all D v hvk.1
      refine ⟨s, ϖ, hc, hu, lin v k s ϖ (hgen v k hvk) hc hu, ?_⟩
      rw [hcy v k s ϖ (hgen v k hvk) hc hu, hκF v k hvk])
  have hinjK : Function.Injective (algebraMap (Sp.B.Oc j w) (FractionRing (Sp.B.Oc j w))) :=
    IsFractionRing.injective _ _
  obtain ⟨ψ, hψ, hψW⟩ := GlobalTheory.PtLocalEig.pt_of_eigvec (heckeGens Sp.B j w) e hene hinjK (by
    rintro _ ⟨v, k, hvk, rfl⟩
    exact ⟨κF v k, he v k hvk⟩)
  have hψv : ∀ v k (hvk : GenAt D (D.what₂.places.resChar w) (Sp.B.Qc j w) v k),
      ψ ⟨Sp.B.hK j w v k, Algebra.subset_adjoin ⟨v, k, hvk, rfl⟩⟩ = κF v k := by
    intro v k hvk
    apply hinjK
    have e1 := hψ ⟨Sp.B.hK j w v k, Algebra.subset_adjoin ⟨v, k, hvk, rfl⟩⟩
    have e2 := he v k hvk
    change Sp.B.hK j w v k e = _ at e1
    rw [e2] at e1
    exact (smul_left_injective _ hene e1).symm
  have hW : NCov.W (heckeAlg Sp.B j w) (NCov.pt ψ) ≠ ⊥ := by
    intro h0
    apply hene
    have h3 := hψW
    rw [h0] at h3
    exact (Submodule.mem_bot _).1 h3
  obtain ⟨i, hi, hmx⟩ := Sp.mx_all j w h1 h2 hw (NCov.cls ψ) (NCov.cls_isMaximal ψ)
  refine ⟨i, hi, (Sp.ptX j w i hi).symm ⟨ψ, hmx.symm, hW⟩, fun v k hvk => ?_⟩
  have hvk' : GenAt D (D.what₂.places.resChar w) (Sp.B.Qc j w) v k := by rw [Sp.Qc_eq j w]; exact hvk
  have e1 : ∀ z, iotaO L.X.nd L.Y.naut i z = Sp.iotaC j w (Sp.phO j w i hi z) := by
    intro z
    unfold iotaO
    rw [RingHom.comp_apply, RingHom.comp_apply, Au.iotaQ i, Au.iotaQC i]
    exact Sp.iotaC_coh j w i hi z
  rw [e1, Sp.ptX_hT j w i hi _ v k hvk', Equiv.apply_symm_apply]
  show Sp.iotaC j w (ψ ⟨Sp.B.hK j w v k, _⟩) = c v k
  rw [hψv v k hvk', ← hφalg, hκF v k hvk']
end GlobalTheory.EigOnto
end
end

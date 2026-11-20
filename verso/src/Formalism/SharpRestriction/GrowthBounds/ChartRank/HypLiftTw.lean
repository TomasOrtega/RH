import Formalism.SharpRestriction.GrowthBounds.ChartRank.HypLiftDesc

noncomputable section

namespace Formalism.MainNotions.G.CmpJ.PCmpLiftTw

open Formalism.BasicNotions Formalism.MainNotions.G Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.UG NumberField IsDedekindDomain Module Formalism.MainNotions.G.CmpJ
  Formalism.MainNotions.G.CmpJ.PCard Formalism.MainNotions.G.CmpJ.PRankGe Formalism.MainNotions.G.CmpJ.PInvLe Formalism.MainNotions.G.CmpJ.PFormsCl Formalism.MainNotions.G.CmpJ.PCmpLift
  Formalism.MainNotions.G.CmpJ.PCmpLiftDesc

section Gen

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {T fT : ℕ} {bad : Set (HeightOneSpectrum (𝓞 F))}
  {Tau : Type} [Fintype Tau] {S : StepLevel F E σ J T fT bad} {emb : Tau → E →+* ℂ} {c : ℤ}

/- English proof (translation)
Set `xg : UPts σ J (FiniteAdeleRing (𝓞 F) F)` to `⟨bc (inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) γ, ratInU γ hγ⟩`. Set `xk : UPts σ J (FiniteAdeleRing (𝓞 F) F)` to `⟨κ.1, ((S.U_eq κ.1).1 κ.2).1⟩`. Establish `e1 : xg * y0 * xk = y0` using `Subtype.ext h.symm`. Establish `e2 : X.ch xg = 1`. Establish `h3` using `congrArg X.ch e1`.

Rewrite `h3` using `[map_mul, map_mul, X.ch_U xk κ.2, mul_one]`. Conclude with `mul_right_cancel (h3.trans (one_mul _).symm)`. Establish `h4` using `X.ch_rat γ hγ xg rfl`. Rewrite `h4` using `[e2, Units.val_one, one_mul]`. Then use the resulting hypothesis.
-/
theorem tw_triv (X : DetTw S emb c) {y0 : UPts σ J (FiniteAdeleRing (𝓞 F) F)} {γ : GL (Fin n) E}
    (hγ : γ ∈ UJ (σ : E →+* E) J) {κ : S.U}
    (h : y0.1 = bc (inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) γ * y0.1 * κ.1) :
    ∏ τ, (emb τ (γ : Matrix (Fin n) (Fin n) E).det) ^ c = 1 := by
  let xg : UPts σ J (FiniteAdeleRing (𝓞 F) F) := ⟨bc (inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) γ, ratInU γ hγ⟩
  let xk : UPts σ J (FiniteAdeleRing (𝓞 F) F) := ⟨κ.1, ((S.U_eq κ.1).1 κ.2).1⟩
  have e1 : xg * y0 * xk = y0 := Subtype.ext h.symm
  have e2 : X.ch xg = 1 := by
    have h3 := congrArg X.ch e1
    rw [map_mul, map_mul, X.ch_U xk κ.2, mul_one] at h3
    exact mul_right_cancel (h3.trans (one_mul _).symm)
  have h4 := X.ch_rat γ hγ xg rfl
  rwa [e2, Units.val_one, one_mul] at h4

/- English proof (translation)
Unfold `detF`. Rewrite using `[← Finset.prod_mul_distrib]`. Use `Finset.prod_congr rfl fun τ _ => ?_` and prove the remaining obligations. Rewrite using `[hy τ, Matrix.det_mul, mul_zpow]`. Use `congr 2`.

Simplify using `[atInf, RingHom.map_det]`.
-/
theorem detF_tr (γ : GL (Fin n) E) {y y' : Formalism.L2.Forms.Frames (gramC J emb)} (hy : IsTr (atInf emb γ) y' y) :
    detF c y = (∏ τ, (emb τ (γ : Matrix (Fin n) (Fin n) E).det) ^ c) * detF c y' := by
  unfold detF
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun τ _ => ?_
  rw [hy τ, Matrix.det_mul, mul_zpow]
  congr 2
  simp [atInf, RingHom.map_det]

/- English proof (translation)
Introduce `γ hγ κ hy0 y y' hy`. Simplify using `only`. Rewrite using `[hh γ hγ κ hy0 y y' hy, detF_tr γ hy, tw_triv X hγ hy0, one_mul]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem foInv_twist (X : DetTw S emb c) {y0 : UPts σ J (FiniteAdeleRing (𝓞 F) F)} {h : Formalism.L2.Forms.Frames (gramC J emb) → ℂ}
    (hh : FoInv S emb y0 h) : FoInv S emb y0 (fun z => (detF c z)⁻¹ * h z) := by
  intro γ hγ κ hy0 y y' hy
  simp only
  rw [hh γ hγ κ hy0 y y' hy, detF_tr γ hy, tw_triv X hγ hy0, one_mul]
  ring

end Gen

section Rec

variable {D : D7} {u : D.what₂.Word} {C : ColumnChain D.R D.what₂.Tau (D.hcW u)} {A : ColumnsAtT D.R C} {P : PeriodMap D.R C}
  {M : MemberForms D.what₂.LL D.what₂.embLL D.what₂.places D.what₂.Tau (D.hcW u) C A P} {p : ℕ} {i : ℕ} {hi : i ≤ D.R.m} {G : GAtP p}

def CmpInvRawOf (S : StepIn M i hi G) (e : D.what₂.LL →+* G.Kf) : Prop :=
  BlockRationalityField → (∀ β, S.Core e β) → KAat.ChX S → ∀ β rep, RepOk S β rep → ∀ c
    (g : ∀ v, GL (Fin ((Hc S β).P.m + 1)) ((Hc S β).P.Qq v)) (γ0 : GL (Fin (D.R.N i)) D.host.E) (κ0 : (S.K β).lev.U),
    γ0 ∈ UJ (sigD D : D.host.E →+* D.host.E) (gramN D i hi) →
    (∀ v, (rep c).2 v = colSpan ((Hc S β).P.W v) (g v : Matrix (Fin ((Hc S β).P.m + 1)) (Fin ((Hc S β).P.m + 1)) ((Hc S β).P.Qq v))) →
    (S.loc β).IsPt (rep c).1 g (bc (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) γ0 * ((S.K β).y c).1 * κ0.1) →
    ∀ Q ∈ YInv (Hc S β) e (rep c).1 (rep c).2,
      FoInv (S.K β).lev (embT D) ((S.K β).y c) (fun z =>
        evC (Hc S β).P (S.loc β).rk S.pos (gramC (gramN D i hi) (embT D)) (crdB (embT D) (S.loc β).B)
          (MvPolynomial.map D.what₂.embLL Q) (foTrR (embT D) γ0 z))

/- English proof (translation)
Introduce `hS H X β rep hok c g γ0 κ0 hγ0 hL hpt Q hQ`. Conclude with `foInv_twist (S.tw β) (hR hS H X β rep hok c g γ0 κ0 hγ0 hL hpt Q hQ)`.
-/
theorem cmpInvOf_of_raw (S : StepIn M i hi G) (e : D.what₂.LL →+* G.Kf) (hR : CmpInvRawOf S e) : CmpInvOf S e := by
  intro hS H X β rep hok c g γ0 κ0 hγ0 hL hpt Q hQ
  exact foInv_twist (S.tw β) (hR hS H X β rep hok c g γ0 κ0 hγ0 hL hpt Q hQ)

/- English proof (translation)
The claim follows from `cmpLiftOf_of_two S e hV (cmpInvOf_of_raw S e hR)`.
-/
theorem cmpLiftOf_of_raw (S : StepIn M i hi G) (e : D.what₂.LL →+* G.Kf) (hV : ∀ β, EvValLe S β) (hR : CmpInvRawOf S e) :
    CmpLiftOf S e :=
  cmpLiftOf_of_two S e hV (cmpInvOf_of_raw S e hR)

/- English proof (translation)
The claim follows from `invLeOf_of_cmp S e (cmpLiftOf_of_raw S e hV hR)`.
-/
theorem invLeOf_of_raw (S : StepIn M i hi G) (e : D.what₂.LL →+* G.Kf) (hV : ∀ β, EvValLe S β) (hR : CmpInvRawOf S e) :
    InvLeOf S e :=
  invLeOf_of_cmp S e (cmpLiftOf_of_raw S e hV hR)

end Rec

section Card

variable {D : D7} {Tw : TwForms D} {u : D.what₂.Word} {μ : D.what₂.Tup} {w : D.what₂.places.Pl}
  {h : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)} {Fl : Fills (D.gat u w h)} {Lv : Levels Fl}

/- English proof (translation)
The claim follows from `cmpJHyp_of_cmp c Gt hS core ok twUnit valIntN iwF hfin X fun j hj => cmpLiftOf_of_raw _ _ (hV j hj) (hR j hj)`.
-/
theorem cmpJHyp_of_raw (c : LatCmp D) {I : CmpJIn Tw u μ w h Lv} (Gt : GatTies D) (hS : BlockRationalityField)
    (core : ∀ j hj β, (I.at' j hj).st.Core (c.embW u w h) β) (ok : ∀ j hj, (I.at' j hj).st.okW w)
    (twUnit : ∀ j hj β, (I.at' j hj).st.TwUnit w β) (valIntN : ∀ j hj, (I.at' j hj).st.ValIntN (c.embW u w h) w)
    (iwF : ∀ j hj β, (I.at' j hj).st.IwF β) (hfin : ∀ j, j + 1 ≤ D.R.m → (gatJ Lv (j + 1)).FinClasses)
    (X : ∀ j hj, KAat.ChX (I.at' j hj).st) (hV : ∀ j hj β, EvValLe (I.at' j hj).st β)
    (hR : ∀ j hj, CmpInvRawOf (I.at' j hj).st (c.embW u w h)) : CmpJHyp c I :=
  cmpJHyp_of_cmp c Gt hS core ok twUnit valIntN iwF hfin X fun j hj => cmpLiftOf_of_raw _ _ (hV j hj) (hR j hj)

end Card

end Formalism.MainNotions.G.CmpJ.PCmpLiftTw

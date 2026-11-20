import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DualMapCompDualMap
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.CechKS
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CechKS.PrismDlog

noncomputable def dl {B : Type} [CommRing B] (a : DualNumber B) : B := a.snd * Ring.inverse a.fst

/- English proof (translation)
Take `⟨x, hx⟩` from `ha`. Take `⟨y, hy⟩` from `hb`. Establish `e : (a * b).fst = ((x * y : Bˣ) : B)` using `by simp [hx, hy]`. Establish `e2 : (a * b).snd = a.fst * b.snd + a.snd * b.fst`. Rewrite using `[TrivSqZeroExt.snd_mul, smul_eq_mul, MulOpposite.smul_eq_mul_unop, MulOpposite.unop_op]`.

Establish `h1 : (x : B) * ((x⁻¹ : Bˣ) : B) = 1` using `Units.mul_inv x`. Establish `h2 : (y : B) * ((y⁻¹ : Bˣ) : B) = 1` using `Units.mul_inv y`. Rewrite using `[dl, dl, dl, e, e2, Ring.inverse_unit, ← hx, ← hy, Ring.inverse_unit, Ring.inverse_unit, mul_inv_rev, Units.val_mul]`. Take the linear combination `(b.snd * ((y⁻¹ : Bˣ) : B)) * h1 + (a.snd * ((x⁻¹ : Bˣ) : B)) * h2`.
-/
theorem dl_mul {B : Type} [CommRing B] {a b : DualNumber B} (ha : IsUnit a.fst) (hb : IsUnit b.fst) :
    dl (a * b) = dl a + dl b := by
  obtain ⟨x, hx⟩ := ha
  obtain ⟨y, hy⟩ := hb
  have e : (a * b).fst = ((x * y : Bˣ) : B) := by simp [hx, hy]
  have e2 : (a * b).snd = a.fst * b.snd + a.snd * b.fst := by
    rw [TrivSqZeroExt.snd_mul, smul_eq_mul, MulOpposite.smul_eq_mul_unop, MulOpposite.unop_op]
  have h1 : (x : B) * ((x⁻¹ : Bˣ) : B) = 1 := Units.mul_inv x
  have h2 : (y : B) * ((y⁻¹ : Bˣ) : B) = 1 := Units.mul_inv y
  rw [dl, dl, dl, e, e2, Ring.inverse_unit, ← hx, ← hy, Ring.inverse_unit, Ring.inverse_unit, mul_inv_rev,
    Units.val_mul]
  linear_combination (b.snd * ((y⁻¹ : Bˣ) : B)) * h1 + (a.snd * ((x⁻¹ : Bˣ) : B)) * h2

/- English proof (translation)
Simplify using `[dl]`.
-/
theorem dl_inl {B : Type} [CommRing B] (b : B) : dl (TrivSqZeroExt.inl b : DualNumber B) = 0 := by
  simp [dl]

/- English proof (translation)
Simplify using `[dl, ha]`.
-/
theorem dl_one_add {B : Type} [CommRing B] {a : DualNumber B} (ha : a.fst = 0) : dl (1 + a) = a.snd := by
  simp [dl, ha]

/- English proof (translation)
Take `⟨x, hx⟩` from `ha`. Establish `e : (dualAlg ρ a).fst = ((Units.map (ρ : B →* B') x : B'ˣ) : B')` using `by simp [hx]`. Rewrite using `[dl, dl, e, ← hx, Ring.inverse_unit, Ring.inverse_unit, snd_dualAlg, map_mul]`. Simplify using the standard rewrite rules.
-/
theorem dl_map {R B B' : Type} [CommRing R] [CommRing B] [Algebra R B] [CommRing B'] [Algebra R B'] (ρ : B →ₐ[R] B')
    {a : DualNumber B} (ha : IsUnit a.fst) : dl (dualAlg ρ a) = ρ (dl a) := by
  obtain ⟨x, hx⟩ := ha
  have e : (dualAlg ρ a).fst = ((Units.map (ρ : B →* B') x : B'ˣ) : B') := by simp [hx]
  rw [dl, dl, e, ← hx, Ring.inverse_unit, Ring.inverse_unit, snd_dualAlg, map_mul]
  simp

/- English proof (translation)
Establish `h1 : IsUnit (1 + l).fst` using `by simp [hl]`. Use `congrArg dl h` as an intermediate fact. Rewrite `this` using `[dl_mul h1 hU, dl_mul hX hY, dl_one_add hl]`. Rewrite using `[← this]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem snd_eq_of_mul {B : Type} [CommRing B] {l U X Y : DualNumber B} (hl : l.fst = 0) (hU : IsUnit U.fst)
    (hX : IsUnit X.fst) (hY : IsUnit Y.fst) (h : (1 + l) * U = X * Y) : l.snd = dl X + dl Y - dl U := by
  have h1 : IsUnit (1 + l).fst := by simp [hl]
  have := congrArg dl h
  rw [dl_mul h1 hU, dl_mul hX hY, dl_one_add hl] at this
  rw [← this]; ring

/- English proof (translation)
The claim follows from `h.map (TrivSqZeroExt.fstHom B B B)`.
-/
theorem isUnit_fst {B : Type} [CommRing B] {a : DualNumber B} (h : IsUnit a) : IsUnit a.fst :=
  h.map (TrivSqZeroExt.fstHom B B B)

/- English proof (translation)
Use `congrArg (fun z ↦ valR w _ (z : Γ(X, L.U a ⊓ L.U b ⊓ L.U k)ˣ).val) (hL.cocycle a b k)` as an intermediate fact. Simplify using `only [Units.val_mul] at this`. Rewrite `this` using `[GlobalTheory.Points.valR_mul w _ h]`. Simplify using `only [res, Units.coe_map, MonoidHom.coe_coe] at this`. Rewrite `this` using `[GlobalTheory.Points.valR_res w _ h, GlobalTheory.Points.valR_res w _ h, GlobalTheory.Points.valR_res w _ h]`. Then use the resulting hypothesis.
-/
theorem valR_cocycle {X : Scheme.{0}} (L : LB X) (hL : L.IsLB) {C : Type} [CommRing C] (w : Sp C ⟶ X)
    (a b k : L.ι) (h : ⊤ ≤ w ⁻¹ᵁ (L.U a ⊓ L.U b ⊓ L.U k)) :
    valR w _ (L.g a b).val * valR w _ (L.g b k).val = valR w _ (L.g a k).val := by
  have := congrArg (fun z ↦ valR w _ (z : Γ(X, L.U a ⊓ L.U b ⊓ L.U k)ˣ).val) (hL.cocycle a b k)
  simp only [Units.val_mul] at this
  rw [GlobalTheory.Points.valR_mul w _ h] at this
  simp only [res, Units.coe_map, MonoidHom.coe_coe] at this
  rwa [GlobalTheory.Points.valR_res w _ h, GlobalTheory.Points.valR_res w _ h, GlobalTheory.Points.valR_res w _ h] at this

/- English proof (translation)
Rewrite using `[GlobalTheory.Points.valR_eq w U h]`. Conclude with `f.isUnit.map _`.
-/
theorem isUnit_valR {X : Scheme.{0}} {C : Type} [CommRing C] (w : Sp C ⟶ X) (U : X.Opens) (h : ⊤ ≤ w ⁻¹ᵁ U)
    (f : Γ(X, U)ˣ) : IsUnit (valR w U f.val) := by
  rw [GlobalTheory.Points.valR_eq w U h]; exact f.isUnit.map _

/- English proof (translation)
Rewrite using `[valR, dif_pos h]`. Both sides reduce to the same expression.
-/
theorem evalAt_eq_valR {X : Scheme.{0}} {C : Type} [CommRing C] (x : Sp C ⟶ X) (U : X.Opens) (h : ⊤ ≤ x ⁻¹ᵁ U)
    (f : Γ(X, U)) : evalAt x U h f = valR x U f := by
  rw [valR, dif_pos h]; rfl

variable {K : Type} [Field K] {A : Over (Sp K)} [GrpObj A]

/- English proof (translation)
Establish `e` using `GlobalTheory.Points.valR_spMap_comp (TrivSqZeroExt.fstHom P.B P.B P.B).toRingHom (P.trx v) U (h.tr hv) f`. Rewrite `e` using `[(P.isTransl_trx v).red hv]`. Rewrite using `[e]`. Both sides reduce to the same expression.
-/
theorem fst_valR_trx (P : GPt A) {v : epsR K ⟶ A} (hv : IsTangent v) (U : A.left.Opens) (h : P.In U)
    (f : Γ(A.left, U)) : (valR (P.trx v) U f).fst = valR P.x U f := by
  have e := GlobalTheory.Points.valR_spMap_comp (TrivSqZeroExt.fstHom P.B P.B P.B).toRingHom (P.trx v) U (h.tr hv) f
  rw [(P.isTransl_trx v).red hv] at e
  rw [e]; rfl

/- English proof (translation)
Establish `hunit : ∀ (T T' : Small L.U) (φ : T ⟶ T'), IsUnit (T'.obj.π (u T T' φ))` using `fun T T' φ ↦ by`. Rewrite using `[hu]`. Conclude with `(L.g _ _).isUnit.map _`. Take `⟨hmem, heq⟩` from `hl T T' ⟨R.ext, hR⟩ φ ψ`. Rewrite `heq` using `[dpExp_sqDP _ hmem]`.

Use `snd_eq_of_mul hmem (hunit T ⟨R.ext, hR⟩ (φ ≫ ψ)) ?_ (hunit T' ⟨R.ext, hR⟩ ψ) heq` and prove the remaining obligations. Establish `e` using `ψ.hom.comm (u T T' φ)`. Express the relevant statement in the definitionally equal form `_ = TrivSqZeroExt.fst _ at e`. Rewrite using `[← e]`. Conclude with `(hunit T T' φ).map _`.
-/
theorem snd_l (L : LB A.left) (c : Small L.U → L.ι) (hc : ∀ T, ⊤ ≤ T.obj.x ⁻¹ᵁ L.U (c T))
    (u : ∀ T T' : Small L.U, (T ⟶ T') → T'.obj.B) (l : C2 (OSmall L.U))
    (hu : ∀ T T' φ, T'.obj.π (u T T' φ) = evalAt T'.obj.x (L.U (c T') ⊓ L.U (c T))
      (le_inf (hc T') (φ.hom.le_preimage (hc T))) (L.g (c T') (c T)).val)
    (hl : ∀ T T' T'' φ ψ, (l T T' T'' φ ψ : T''.obj.B) ∈ T''.obj.J ∧
      dpExp T''.obj.δ (l T T' T'' φ ψ) * u T T'' (φ ≫ ψ) = ψ.hom.φ (u T T' φ) * u T' T'' ψ)
    (R : GPt A) (hR : ∃ i, R.In (L.U i)) {T T' : Small L.U} (φ : T ⟶ T') (ψ : T' ⟶ ⟨R.ext, hR⟩) :
    TrivSqZeroExt.snd (R := R.B) (l T T' ⟨R.ext, hR⟩ φ ψ : DualNumber R.B) =
      dl (ψ.hom.φ (u T T' φ) : DualNumber R.B) + dl (u T' ⟨R.ext, hR⟩ ψ : DualNumber R.B) -
        dl (u T ⟨R.ext, hR⟩ (φ ≫ ψ) : DualNumber R.B) := by
  have hunit : ∀ (T T' : Small L.U) (φ : T ⟶ T'), IsUnit (T'.obj.π (u T T' φ)) := fun T T' φ ↦ by
    rw [hu]; exact (L.g _ _).isUnit.map _
  obtain ⟨hmem, heq⟩ := hl T T' ⟨R.ext, hR⟩ φ ψ
  rw [dpExp_sqDP _ hmem] at heq
  refine snd_eq_of_mul hmem (hunit T ⟨R.ext, hR⟩ (φ ≫ ψ)) ?_ (hunit T' ⟨R.ext, hR⟩ ψ) heq
  have e := ψ.hom.comm (u T T' φ)
  change _ = TrivSqZeroExt.fst _ at e
  rw [← e]
  exact (hunit T T' φ).map _

/- English proof (translation)
Substitute `hχ` using the available equality. Conclude with `snd_l L c hc u l hu hl R hR φ ψ`.
-/
theorem snd_l' (L : LB A.left) (c : Small L.U → L.ι) (hc : ∀ T, ⊤ ≤ T.obj.x ⁻¹ᵁ L.U (c T))
    (u : ∀ T T' : Small L.U, (T ⟶ T') → T'.obj.B) (l : C2 (OSmall L.U))
    (hu : ∀ T T' φ, T'.obj.π (u T T' φ) = evalAt T'.obj.x (L.U (c T') ⊓ L.U (c T))
      (le_inf (hc T') (φ.hom.le_preimage (hc T))) (L.g (c T') (c T)).val)
    (hl : ∀ T T' T'' φ ψ, (l T T' T'' φ ψ : T''.obj.B) ∈ T''.obj.J ∧
      dpExp T''.obj.δ (l T T' T'' φ ψ) * u T T'' (φ ≫ ψ) = ψ.hom.φ (u T T' φ) * u T' T'' ψ)
    (R : GPt A) (hR : ∃ i, R.In (L.U i)) {T T' : Small L.U} (φ : T ⟶ T') (ψ : T' ⟶ ⟨R.ext, hR⟩)
    (χ : T ⟶ ⟨R.ext, hR⟩) (hχ : φ ≫ ψ = χ) :
    TrivSqZeroExt.snd (R := R.B) (l T T' ⟨R.ext, hR⟩ φ ψ : DualNumber R.B) =
      dl (ψ.hom.φ (u T T' φ) : DualNumber R.B) + dl (u T' ⟨R.ext, hR⟩ ψ : DualNumber R.B) -
        dl (u T ⟨R.ext, hR⟩ χ : DualNumber R.B) := by
  subst hχ; exact snd_l L c hc u l hu hl R hR φ ψ

open Classical in

noncomputable def Nf (L : LB A.left) (c : Small L.U → L.ι) (u : ∀ T T' : Small L.U, (T ⟶ T') → T'.obj.B)
    {v : epsR K ⟶ A} (hv : IsTangent v) (j : L.ι) : PtFn (A.hom ≫ 𝟙 (Sp K)) := fun P ↦
  if h : P.In (L.U j) then
    dl (u ⟨P.triv, ⟨j, h⟩⟩ ⟨P.ext, ⟨j, h⟩⟩ ⟨P.sec⟩ : DualNumber P.B) -
      dl (u ⟨(P.tr v).triv, ⟨j, h.tr hv⟩⟩ ⟨P.ext, ⟨j, h⟩⟩ ⟨P.tan hv⟩ : DualNumber P.B) -
      dl (valR (P.trx v) _ (L.g (c ⟨(P.tr v).triv, ⟨j, h.tr hv⟩⟩) j).val)
  else 0

end GlobalTheory.CechKS.PrismDlog

open GlobalTheory.CechKS.PrismDlog in

/- English proof (translation)
Introduce `K _ A _ L hL c hc u l hu hl v hv`. Establish `hunit : ∀ (T T' : Small L.U) (φ : T ⟶ T'), IsUnit (T'.obj.π (u T T' φ))` using `fun T T' φ ↦ by`. Rewrite using `[hu]`. Conclude with `(L.g _ _).isUnit.map _`. Use `⟨Nf L c u hv, ?_, ?_⟩` and prove the remaining obligations.

Introduce `j P Q φ hP`. Establish `hQ : Q.In (L.U j)` using `hP.map φ`. Establish `k1` using `snd_l' L c hc u l hu hl Q ⟨j, hQ⟩ (T := ⟨P.triv, ⟨j, hP⟩⟩) (T' := ⟨Q.triv, ⟨j, hQ⟩⟩) ⟨φ.triv⟩ ⟨Q.sec⟩ ⟨P.sec ≫ φ.dual⟩ (by`. Use extensionality with `b`. Use `show (TrivSqZeroExt.inl (φ.ρ b) : DualNumber Q.B).fst = (dualAlg φ.ρ (TrivSqZeroExt.inl b)).fst`.

Simplify using the standard rewrite rules. Use `show (TrivSqZeroExt.inl (φ.ρ b) : DualNumber Q.B).snd = (dualAlg φ.ρ (TrivSqZeroExt.inl b)).snd simp)`. Establish `k2` using `snd_l' L c hc u l hu hl Q ⟨j, hQ⟩ (T := ⟨P.triv, ⟨j, hP⟩⟩) (T' := ⟨P.ext, ⟨j, hP⟩⟩) ⟨P.sec⟩ ⟨φ.dual⟩ ⟨P.sec ≫ φ.dual⟩ rfl`. Apply the tactic sequence `have k3 := snd_l' L c hc u l hu hl Q ⟨j, hQ⟩ (T := ⟨(P.tr v).triv, ⟨j, hP.tr hv⟩⟩) (T' := ⟨(Q.tr v).triv, ⟨j, hQ.tr hv⟩⟩) ⟨(φ.tr v).triv⟩ ⟨Q.tan hv⟩ ⟨P.tan hv ≫ φ.dual⟩ (by ext b <;> rfl)`. Establish `k4` using `snd_l' L c hc u l hu hl Q ⟨j, hQ⟩ (T := ⟨(P.tr v).triv, ⟨j, hP.tr hv⟩⟩) (T' := ⟨P.ext, ⟨j, hP⟩⟩) ⟨P.tan hv⟩ ⟨φ.dual⟩ ⟨P.tan hv ≫ φ.dual⟩ rfl`.

Take `⟨a, ha⟩ : ∃ a, a = c ⟨(P.tr v).triv, ⟨j, hP.tr hv⟩⟩` from `⟨_, rfl⟩`. Take `⟨b, hb⟩ : ∃ b, b = c ⟨(Q.tr v).triv, ⟨j, hQ.tr hv⟩⟩` from `⟨_, rfl⟩`. Establish `hPa : (P.tr v).In (L.U a)` using `ha ▸ hc ⟨(P.tr v).triv, ⟨j, hP.tr hv⟩⟩`. Establish `hQb : (Q.tr v).In (L.U b)` using `hb ▸ hc ⟨(Q.tr v).triv, ⟨j, hQ.tr hv⟩⟩`. Establish `hQa : (Q.tr v).In (L.U a)` using `hPa.map (φ.tr v)`.

Establish `e1 : (u ⟨(P.tr v).triv, ⟨j, hP.tr hv⟩⟩ ⟨(Q.tr v).triv, ⟨j, hQ.tr hv⟩⟩ ⟨(φ.tr v).triv⟩ : DualNumber Q.B) = valR (Q.trx v) _ (L.g b a).val`. Substitute `ha hb` using the available equality. Conclude with `(hu ⟨(P.tr v).triv, ⟨j, hP.tr hv⟩⟩ ⟨(Q.tr v).triv, ⟨j, hQ.tr hv⟩⟩ ⟨(φ.tr v).triv⟩).trans (evalAt_eq_valR _ _ _ _)`. Establish `e2 : valR (Q.trx v) _ (L.g a j).val = dualAlg φ.ρ (valR (P.trx v) _ (L.g a j).val)`. Establish `e` using `GlobalTheory.Points.valR_spMap_comp (dualAlg φ.ρ : DualNumber P.B →+* DualNumber Q.B) (P.trx v) _ (hPa.inf (hP.tr hv)) (L.g a j).val`.

Establish `e' : spMap (dualAlg φ.ρ : DualNumber P.B →+* DualNumber Q.B) ≫ P.trx v = Q.trx v` using `(φ.tr v).pt`. Rewrite `e` using `[e']`. Conclude with `e`. Establish `e3` using `valR_cocycle L hL (Q.trx v) b a j ((hQb.inf hQa).inf (hQ.tr hv))`. Establish `e4 : dl (valR (Q.trx v) _ (L.g b j).val) = dl (valR (Q.trx v) _ (L.g b a).val) + φ.ρ (dl (valR (P.trx v) _ (L.g a j).val))`.

Rewrite using `[← e3, dl_mul (isUnit_fst (isUnit_valR _ _ (hQb.inf hQa) _)) (isUnit_fst (isUnit_valR _ _ (hQa.inf (hQ.tr hv)) _)), e2, dl_map _ (isUnit_fst (isUnit_valR _ _ (hPa.inf (hP.tr hv)) _))]`. Establish `d1 : dl (Q.sec.φ (u ⟨P.triv, ⟨j, hP⟩⟩ ⟨Q.triv, ⟨j, hQ⟩⟩ ⟨φ.triv⟩) : DualNumber Q.B) = 0` using `dl_inl _`. Establish `d2 : dl (φ.dual.φ (u ⟨P.triv, ⟨j, hP⟩⟩ ⟨P.ext, ⟨j, hP⟩⟩ ⟨P.sec⟩) : DualNumber Q.B) = φ.ρ (dl (u ⟨P.triv, ⟨j, hP⟩⟩ ⟨P.ext, ⟨j, hP⟩⟩ ⟨P.sec⟩ : DualNumber P.B))` using `dl_map φ.ρ (hunit ⟨P.triv, ⟨j, hP⟩⟩ ⟨P.ext, ⟨j, hP⟩⟩ ⟨P.sec⟩)`. Establish `d3 : dl ((Q.tan hv).φ (u ⟨(P.tr v).triv, ⟨j, hP.tr hv⟩⟩ ⟨(Q.tr v).triv, ⟨j, hQ.tr hv⟩⟩ ⟨(φ.tr v).triv⟩) : DualNumber Q.B) = dl (valR (Q.trx v) _ (L.g b a).val)` using `congrArg dl e1`. Establish `d4 : dl (φ.dual.φ (u ⟨(P.tr v).triv, ⟨j, hP.tr hv⟩⟩ ⟨P.ext, ⟨j, hP⟩⟩ ⟨P.tan hv⟩) : DualNumber Q.B) = φ.ρ (dl (u ⟨(P.tr v).triv, ⟨j, hP.tr hv⟩⟩ ⟨P.ext, ⟨j, hP⟩⟩ ⟨P.tan hv⟩ : DualNumber P.B))` using `dl_map φ.ρ (hunit ⟨(P.tr v).triv, ⟨j, hP.tr hv⟩⟩ ⟨P.ext, ⟨j, hP⟩⟩ ⟨P.tan hv⟩)`.

Establish `k1'` using `k1.trans (congrArg (fun z ↦ z + _ - _) d1)`. Establish `k2'` using `k2.trans (congrArg (fun z ↦ z + _ - _) d2)`. Establish `k3'` using `k3.trans (congrArg (fun z ↦ z + _ - _) d3)`. Establish `k4'` using `k4.trans (congrArg (fun z ↦ z + _ - _) d4)`. Establish `key : ∀ {x1 x2 x3 x4 : DualNumber Q.B} {y1 y2 y3 y4 : Q.B}, x1.snd = y1 → x2.snd = y2 → x3.snd = y3 → x4.snd = y4 → ((x1 - x2) - (x3 - x4)).snd = (y1 - y2) - (y3 - y4)`.

Introduce and unpack `x1 x2 x3 x4 _ _ _ _ rfl rfl rfl rfl`. Simplify using the standard rewrite rules. Use `(key k1' k2' k3' k4').trans ?_` and prove the remaining obligations. Simplify using `only [Nf, dif_pos hP, dif_pos hQ, map_sub]`. Rewrite using `[← ha, ← hb, e4]`.

Expand and normalize the polynomial expressions, which then agree. Introduce `j j' P hj hj'`. Take `⟨b, hb⟩ : ∃ b, b = c ⟨(P.tr v).triv, ⟨j, hj.tr hv⟩⟩` from `⟨_, rfl⟩`. Establish `hPb : (P.tr v).In (L.U b)` using `hb ▸ hc ⟨(P.tr v).triv, ⟨j, hj.tr hv⟩⟩`. Simplify using `only [Nf, dif_pos hj, dif_pos hj']`.

Rewrite using `[← hb]`. Establish `e3` using `valR_cocycle L hL (P.trx v) b j j' ((hPb.inf (hj.tr hv)).inf (hj'.tr hv))`. Establish `e4 : dl (valR (P.trx v) _ (L.g b j').val) = dl (valR (P.trx v) _ (L.g b j).val) + dl (valR (P.trx v) _ (L.g j j').val)`. Rewrite using `[← e3, dl_mul (isUnit_fst (isUnit_valR _ _ (hPb.inf (hj.tr hv)) _)) (isUnit_fst (isUnit_valR _ _ ((hj.inf hj').tr hv) _))]`. Establish `e5 : dl (valR (P.trx v) _ (L.g j j').val) = dlog L v j j' P`.

Rewrite using `[dl, dlog, fst_valR_trx P hv _ (hj.inf hj')]`. Establish `h1 : valR P.x _ (L.g j j').val * valR P.x _ (L.g j j')⁻¹.val = 1`. Rewrite using `[← GlobalTheory.Points.valR_mul _ _ (hj.inf hj'), Units.mul_inv, GlobalTheory.Points.valR_eq _ _ (hj.inf hj'), map_one]`. Establish `h2 : Ring.inverse (valR P.x _ (L.g j j').val) = valR P.x _ (L.g j j')⁻¹.val` using `Ring.inverse_unit (Units.mkOfMulEqOne _ _ h1)`. Rewrite using `[h2]`.

Rewrite using `[← e5, e4]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem GlobalTheory.CechKS.prism_trivialised : ∀ (K : Type) [Field K] (A : Over (Sp K)) [GrpObj A] (L : LB A.left), L.IsLB → ∀ (c : Small L.U → L.ι) (hc : ∀ T, ⊤ ≤ T.obj.x ⁻¹ᵁ L.U (c T)) (u : ∀ T T' : Small L.U, (T ⟶ T') → T'.obj.B) (l : C2 (OSmall L.U)), (∀ T T' φ, T'.obj.π (u T T' φ) = evalAt T'.obj.x (L.U (c T') ⊓ L.U (c T)) (le_inf (hc T') (φ.hom.le_preimage (hc T))) (L.g (c T') (c T)).val) → (∀ T T' T'' φ ψ, (l T T' T'' φ ψ : T''.obj.B) ∈ T''.obj.J ∧ dpExp T''.obj.δ (l T T' T'' φ ψ) * u T T'' (φ ≫ ψ) = ψ.hom.φ (u T T' φ) * u T' T'' ψ) → ∀ (v : epsR K ⟶ A) (hv : IsTangent v), ∃ N : L.ι → PtFn (A.hom ≫ 𝟙 (Sp K)), (∀ (j : L.ι) (P Q : GPt A) (φ : P.Hom Q) (hP : P.In (L.U j)), prism l hv φ ⟨j, hP⟩ = N j Q - φ.ρ (N j P)) ∧ ∀ (j j' : L.ι) (P : GPt A), P.In (L.U j) → P.In (L.U j') → N j P - N j' P = dlog L v j j' P := by
  intro K _ A _ L hL c hc u l hu hl v hv
  have hunit : ∀ (T T' : Small L.U) (φ : T ⟶ T'), IsUnit (T'.obj.π (u T T' φ)) := fun T T' φ ↦ by
    rw [hu]; exact (L.g _ _).isUnit.map _
  refine ⟨Nf L c u hv, ?_, ?_⟩
  · intro j P Q φ hP
    have hQ : Q.In (L.U j) := hP.map φ
    have k1 := snd_l' L c hc u l hu hl Q ⟨j, hQ⟩ (T := ⟨P.triv, ⟨j, hP⟩⟩) (T' := ⟨Q.triv, ⟨j, hQ⟩⟩) ⟨φ.triv⟩ ⟨Q.sec⟩
      ⟨P.sec ≫ φ.dual⟩ (by
        ext b
        · show (TrivSqZeroExt.inl (φ.ρ b) : DualNumber Q.B).fst = (dualAlg φ.ρ (TrivSqZeroExt.inl b)).fst
          simp
        · show (TrivSqZeroExt.inl (φ.ρ b) : DualNumber Q.B).snd = (dualAlg φ.ρ (TrivSqZeroExt.inl b)).snd
          simp)
    have k2 := snd_l' L c hc u l hu hl Q ⟨j, hQ⟩ (T := ⟨P.triv, ⟨j, hP⟩⟩) (T' := ⟨P.ext, ⟨j, hP⟩⟩) ⟨P.sec⟩ ⟨φ.dual⟩
      ⟨P.sec ≫ φ.dual⟩ rfl
    have k3 := snd_l' L c hc u l hu hl Q ⟨j, hQ⟩ (T := ⟨(P.tr v).triv, ⟨j, hP.tr hv⟩⟩)
      (T' := ⟨(Q.tr v).triv, ⟨j, hQ.tr hv⟩⟩) ⟨(φ.tr v).triv⟩ ⟨Q.tan hv⟩ ⟨P.tan hv ≫ φ.dual⟩ (by ext b <;> rfl)
    have k4 := snd_l' L c hc u l hu hl Q ⟨j, hQ⟩ (T := ⟨(P.tr v).triv, ⟨j, hP.tr hv⟩⟩)
      (T' := ⟨P.ext, ⟨j, hP⟩⟩) ⟨P.tan hv⟩ ⟨φ.dual⟩ ⟨P.tan hv ≫ φ.dual⟩ rfl
    obtain ⟨a, ha⟩ : ∃ a, a = c ⟨(P.tr v).triv, ⟨j, hP.tr hv⟩⟩ := ⟨_, rfl⟩
    obtain ⟨b, hb⟩ : ∃ b, b = c ⟨(Q.tr v).triv, ⟨j, hQ.tr hv⟩⟩ := ⟨_, rfl⟩
    have hPa : (P.tr v).In (L.U a) := ha ▸ hc ⟨(P.tr v).triv, ⟨j, hP.tr hv⟩⟩
    have hQb : (Q.tr v).In (L.U b) := hb ▸ hc ⟨(Q.tr v).triv, ⟨j, hQ.tr hv⟩⟩
    have hQa : (Q.tr v).In (L.U a) := hPa.map (φ.tr v)
    have e1 : (u ⟨(P.tr v).triv, ⟨j, hP.tr hv⟩⟩ ⟨(Q.tr v).triv, ⟨j, hQ.tr hv⟩⟩ ⟨(φ.tr v).triv⟩ : DualNumber Q.B) =
        valR (Q.trx v) _ (L.g b a).val := by
      subst ha hb
      exact (hu ⟨(P.tr v).triv, ⟨j, hP.tr hv⟩⟩ ⟨(Q.tr v).triv, ⟨j, hQ.tr hv⟩⟩ ⟨(φ.tr v).triv⟩).trans
        (evalAt_eq_valR _ _ _ _)
    have e2 : valR (Q.trx v) _ (L.g a j).val = dualAlg φ.ρ (valR (P.trx v) _ (L.g a j).val) := by
      have e := GlobalTheory.Points.valR_spMap_comp (dualAlg φ.ρ : DualNumber P.B →+* DualNumber Q.B) (P.trx v) _
        (hPa.inf (hP.tr hv)) (L.g a j).val
      have e' : spMap (dualAlg φ.ρ : DualNumber P.B →+* DualNumber Q.B) ≫ P.trx v = Q.trx v := (φ.tr v).pt
      rw [e'] at e
      exact e
    have e3 := valR_cocycle L hL (Q.trx v) b a j ((hQb.inf hQa).inf (hQ.tr hv))
    have e4 : dl (valR (Q.trx v) _ (L.g b j).val) =
        dl (valR (Q.trx v) _ (L.g b a).val) + φ.ρ (dl (valR (P.trx v) _ (L.g a j).val)) := by
      rw [← e3, dl_mul (isUnit_fst (isUnit_valR _ _ (hQb.inf hQa) _))
        (isUnit_fst (isUnit_valR _ _ (hQa.inf (hQ.tr hv)) _)), e2,
        dl_map _ (isUnit_fst (isUnit_valR _ _ (hPa.inf (hP.tr hv)) _))]
    have d1 : dl (Q.sec.φ (u ⟨P.triv, ⟨j, hP⟩⟩ ⟨Q.triv, ⟨j, hQ⟩⟩ ⟨φ.triv⟩) : DualNumber Q.B) = 0 := dl_inl _
    have d2 : dl (φ.dual.φ (u ⟨P.triv, ⟨j, hP⟩⟩ ⟨P.ext, ⟨j, hP⟩⟩ ⟨P.sec⟩) : DualNumber Q.B) =
        φ.ρ (dl (u ⟨P.triv, ⟨j, hP⟩⟩ ⟨P.ext, ⟨j, hP⟩⟩ ⟨P.sec⟩ : DualNumber P.B)) :=
      dl_map φ.ρ (hunit ⟨P.triv, ⟨j, hP⟩⟩ ⟨P.ext, ⟨j, hP⟩⟩ ⟨P.sec⟩)
    have d3 : dl ((Q.tan hv).φ (u ⟨(P.tr v).triv, ⟨j, hP.tr hv⟩⟩ ⟨(Q.tr v).triv, ⟨j, hQ.tr hv⟩⟩
        ⟨(φ.tr v).triv⟩) : DualNumber Q.B) = dl (valR (Q.trx v) _ (L.g b a).val) := congrArg dl e1
    have d4 : dl (φ.dual.φ (u ⟨(P.tr v).triv, ⟨j, hP.tr hv⟩⟩ ⟨P.ext, ⟨j, hP⟩⟩ ⟨P.tan hv⟩) : DualNumber Q.B) =
        φ.ρ (dl (u ⟨(P.tr v).triv, ⟨j, hP.tr hv⟩⟩ ⟨P.ext, ⟨j, hP⟩⟩ ⟨P.tan hv⟩ : DualNumber P.B)) :=
      dl_map φ.ρ (hunit ⟨(P.tr v).triv, ⟨j, hP.tr hv⟩⟩ ⟨P.ext, ⟨j, hP⟩⟩ ⟨P.tan hv⟩)
    have k1' := k1.trans (congrArg (fun z ↦ z + _ - _) d1)
    have k2' := k2.trans (congrArg (fun z ↦ z + _ - _) d2)
    have k3' := k3.trans (congrArg (fun z ↦ z + _ - _) d3)
    have k4' := k4.trans (congrArg (fun z ↦ z + _ - _) d4)
    have key : ∀ {x1 x2 x3 x4 : DualNumber Q.B} {y1 y2 y3 y4 : Q.B}, x1.snd = y1 → x2.snd = y2 → x3.snd = y3 →
        x4.snd = y4 → ((x1 - x2) - (x3 - x4)).snd = (y1 - y2) - (y3 - y4) := by
      rintro x1 x2 x3 x4 _ _ _ _ rfl rfl rfl rfl
      simp
    refine (key k1' k2' k3' k4').trans ?_
    simp only [Nf, dif_pos hP, dif_pos hQ, map_sub]
    rw [← ha, ← hb, e4]
    ring
  · intro j j' P hj hj'
    obtain ⟨b, hb⟩ : ∃ b, b = c ⟨(P.tr v).triv, ⟨j, hj.tr hv⟩⟩ := ⟨_, rfl⟩
    have hPb : (P.tr v).In (L.U b) := hb ▸ hc ⟨(P.tr v).triv, ⟨j, hj.tr hv⟩⟩
    simp only [Nf, dif_pos hj, dif_pos hj']
    rw [← hb]
    have e3 := valR_cocycle L hL (P.trx v) b j j' ((hPb.inf (hj.tr hv)).inf (hj'.tr hv))
    have e4 : dl (valR (P.trx v) _ (L.g b j').val) =
        dl (valR (P.trx v) _ (L.g b j).val) + dl (valR (P.trx v) _ (L.g j j').val) := by
      rw [← e3, dl_mul (isUnit_fst (isUnit_valR _ _ (hPb.inf (hj.tr hv)) _))
        (isUnit_fst (isUnit_valR _ _ ((hj.inf hj').tr hv) _))]
    have e5 : dl (valR (P.trx v) _ (L.g j j').val) = dlog L v j j' P := by
      rw [dl, dlog, fst_valR_trx P hv _ (hj.inf hj')]
      have h1 : valR P.x _ (L.g j j').val * valR P.x _ (L.g j j')⁻¹.val = 1 := by
        rw [← GlobalTheory.Points.valR_mul _ _ (hj.inf hj'), Units.mul_inv, GlobalTheory.Points.valR_eq _ _ (hj.inf hj'), map_one]
      have h2 : Ring.inverse (valR P.x _ (L.g j j').val) = valR P.x _ (L.g j j')⁻¹.val :=
        Ring.inverse_unit (Units.mkOfMulEqOne _ _ h1)
      rw [h2]
    rw [← e5, e4]
    ring

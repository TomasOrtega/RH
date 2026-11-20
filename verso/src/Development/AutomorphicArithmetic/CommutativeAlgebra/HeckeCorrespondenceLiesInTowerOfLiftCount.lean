import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.GeometricFlagBases.FinModel
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.InvMemLatMonoidOfMemAwaySupp
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLiftOfEtaleSurjectiveStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteEtaleSurjectiveProjStatement
import Development.AutomorphicArithmetic.CommutativeAlgebra.BijectiveSigmaSpecPointsCoproduct
import Development.AutomorphicArithmetic.CommutativeAlgebra.CardFiberEqRelIndexOfNormalQuotient

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.UPel.HT.EtLev GlobalTheory.LKTrip GlobalTheory.LKGeo
open GlobalTheory.GalV (HTower Splits)
open UpperTheory.Gal.crystallineComparison.Mod (Std TjD TjE KSOKE)
open UpperTheory.Gal.Int.Geo
open scoped TensorProduct
attribute [local instance] Ideal.Quotient.field

/- English proof (translation)
Establish `h` using `congrArg CommaMorphism.left (Pi.lift_π (fun i : Fin k => (Over.homMk ((GlobalTheory.KS.pr A i).left ≫ φ) (by`. Rewrite using `[Category.assoc, u, ← Category.assoc, Over.w]`. Use the proof step `rfl) : Over.mk ((GlobalTheory.KS.pow A k).hom ≫ f) ⟶ B)) i)`. Conclude with `h`.
-/
private theorem pow_pr {X Y : Scheme.{0}} {A : Over X} {B : Over Y} (f : X ⟶ Y) (φ : A.left ⟶ B.left)
    (u : φ ≫ B.hom = A.hom ≫ f) (k : ℕ) (i : Fin k) :
    GlobalTheory.KS.powMap f φ u k ≫ (GlobalTheory.KS.pr B i).left = (GlobalTheory.KS.pr A i).left ≫ φ := by
  have h := congrArg CommaMorphism.left (Pi.lift_π (fun i : Fin k => (Over.homMk ((GlobalTheory.KS.pr A i).left ≫ φ) (by
    rw [Category.assoc, u, ← Category.assoc, Over.w]; rfl) : Over.mk ((GlobalTheory.KS.pow A k).hom ≫ f) ⟶ B)) i)
  exact h

/- English proof (translation)
Substitute `hf` using the available equality. Substitute `hφ` using the available equality. Both sides reduce to the same expression.
-/
private theorem powMap_congr {X Y : Scheme.{0}} {A : Over X} {B : Over Y} {f f' : X ⟶ Y} {φ φ' : A.left ⟶ B.left}
    (hf : f = f') (hφ : φ = φ') (u : φ ≫ B.hom = A.hom ≫ f) (u' : φ' ≫ B.hom = A.hom ≫ f') (k : ℕ) :
    GlobalTheory.KS.powMap f φ u k = GlobalTheory.KS.powMap f' φ' u' k := by
  subst hf; subst hφ; rfl

/- English proof (translation)
The claim follows from `Over.w (Pi.lift (fun i : Fin k => (Over.homMk ((GlobalTheory.KS.pr A i).left ≫ φ) (by rw [Category.assoc, u, ← Category.assoc, Over.w]; rfl) : Over.mk ((GlobalTheory.KS.pow A k).hom ≫ f) ⟶ B)))`.
-/
private theorem pow_hom {X Y : Scheme.{0}} {A : Over X} {B : Over Y} (f : X ⟶ Y) (φ : A.left ⟶ B.left)
    (u : φ ≫ B.hom = A.hom ≫ f) (k : ℕ) :
    GlobalTheory.KS.powMap f φ u k ≫ (GlobalTheory.KS.pow B k).hom = (GlobalTheory.KS.pow A k).hom ≫ f :=
  Over.w (Pi.lift (fun i : Fin k => (Over.homMk ((GlobalTheory.KS.pr A i).left ≫ φ) (by
    rw [Category.assoc, u, ← Category.assoc, Over.w]; rfl) : Over.mk ((GlobalTheory.KS.pow A k).hom ≫ f) ⟶ B)))

/- English proof (translation)
Establish `h : (Limits.Pi.map fun _ : Fin k => ψ) = Over.homMk (GlobalTheory.KS.powMap (𝟙 X) ψ.left (by simp) k) (by`. Simplify using `using pow_hom (𝟙 X) ψ.left (by simp) k) := by`. Use `Pi.hom_ext _ _ fun i => ?_` and prove the remaining obligations. Rewrite using `[Limits.Pi.map_π]`. Apply `Over.OverMorphism.ext` to reduce the goal to its premises.

Use `pow_pr (𝟙 X) ψ.left (by simp) k i` as an intermediate fact. Simplify using `using this.symm`. Rewrite using `[h]`. Both sides reduce to the same expression.
-/
private theorem piMap_eq {X : Scheme.{0}} {A B : Over X} (ψ : A ⟶ B) (k : ℕ) :
    (Limits.Pi.map fun _ : Fin k => ψ).left = GlobalTheory.KS.powMap (𝟙 X) ψ.left (by simp) k := by
  have h : (Limits.Pi.map fun _ : Fin k => ψ) =
      Over.homMk (GlobalTheory.KS.powMap (𝟙 X) ψ.left (by simp) k) (by
        simpa using pow_hom (𝟙 X) ψ.left (by simp) k) := by
    refine Pi.hom_ext _ _ fun i => ?_
    rw [Limits.Pi.map_π]
    apply Over.OverMorphism.ext
    have := pow_pr (𝟙 X) ψ.left (by simp) k i
    simpa using this.symm
  rw [h]; rfl

/- English proof (translation)
Take `⟨n, ⟨e⟩⟩` from `Finite.exists_equiv_fin I`. Establish `h1` using `GlobalTheory.Et.TrivTors.isFinite_sigmaDesc_fin V n`. Establish `h2 : (Sigma.desc fun _ : I => 𝟙 V) = (Sigma.whiskerEquiv e (fun _ => Iso.refl V)).hom ≫ Sigma.desc fun _ : Fin n => 𝟙 V`. Use `Sigma.hom_ext _ _ fun i => ?_` and prove the remaining obligations. Simplify using the standard rewrite rules.

Rewrite using `[h2]`. Use `infer_instance`.
-/
private theorem fold_finite {I : Type} [Finite I] (V : Scheme.{0}) :
    IsFinite (Sigma.desc fun _ : I => 𝟙 V) := by
  obtain ⟨n, ⟨e⟩⟩ := Finite.exists_equiv_fin I
  have h1 := GlobalTheory.Et.TrivTors.isFinite_sigmaDesc_fin V n
  have h2 : (Sigma.desc fun _ : I => 𝟙 V) = (Sigma.whiskerEquiv e (fun _ => Iso.refl V)).hom ≫ Sigma.desc fun _ : Fin n => 𝟙 V := by
    refine Sigma.hom_ext _ _ fun i => ?_
    simp
  rw [h2]
  infer_instance

/- English proof (translation)
Use `fold_finite (I := I) V` as an intermediate fact. Establish `h2 : (Sigma.desc fun _ : I => s) = (Sigma.desc fun _ : I => 𝟙 V) ≫ s`. Use `Sigma.hom_ext _ _ fun i => ?_` and prove the remaining obligations. Simplify using the standard rewrite rules. Rewrite using `[h2]`.

Use `infer_instance`.
-/
private theorem desc_finite {I : Type} [Finite I] {V W : Scheme.{0}} (s : V ⟶ W) [IsFinite s] :
    IsFinite (Sigma.desc fun _ : I => s) := by
  have := fold_finite (I := I) V
  have h2 : (Sigma.desc fun _ : I => s) = (Sigma.desc fun _ : I => 𝟙 V) ≫ s := by
    refine Sigma.hom_ext _ _ fun i => ?_
    simp
  rw [h2]
  infer_instance

/- English proof (translation)
Use `HasRingHomProperty.instIsZariskiLocalAtSource (P := @Etale)` as an intermediate fact. Conclude with `IsZariskiLocalAtSource.sigmaDesc (P := @Etale) fun _ => inferInstance`.
-/
private theorem desc_etale {I : Type} {V W : Scheme.{0}} (s : V ⟶ W) [Etale s] :
    Etale (Sigma.desc fun _ : I => s) := by
  have := HasRingHomProperty.instIsZariskiLocalAtSource (P := @Etale)
  exact IsZariskiLocalAtSource.sigmaDesc (P := @Etale) fun _ => inferInstance

/- English proof (translation)
Establish `hf` using `desc_finite (I := I) s₁`. Establish `he` using `desc_etale (I := I) s₁`. Establish `h1 : pullback.lift (Sigma.desc fun _ : I => s₁) (Sigma.desc κ) e ≫ pullback.fst π f = Sigma.desc fun _ : I => s₁` using `pullback.lift_fst _ _ _`. Use `⟨?_, ?_, fun K _ _ x => ?_⟩` and prove the remaining obligations. Establish `: IsFinite (pullback.lift (Sigma.desc fun _ : I => s₁) (Sigma.desc κ) e ≫ pullback.fst π f)`.

Rewrite using `[h1]`. Conclude with `hf`. Conclude with `IsFinite.of_comp _ (pullback.fst π f)`. Establish `: Etale (pullback.lift (Sigma.desc fun _ : I => s₁) (Sigma.desc κ) e ≫ pullback.fst π f)`. Rewrite using `[h1]`.

Conclude with `he`. Conclude with `Etale.of_comp _ (pullback.fst π f)`. Establish `hb` using `UpperTheory.bijective_sigma_spec_points_coproduct (fun _ : I => ZM) K`. Rewrite using `[← hm K (x ≫ pullback.fst π f) (x ≫ pullback.snd π f) (by simp [pullback.condition])]`. Use `symm`.

Use `Nat.card_congr (Equiv.ofBijective (fun y => ⟨y.1.2.1 ≫ Sigma.ι (fun _ : I => ZM) y.1.1, ?_⟩) ⟨?_, ?_⟩)` and prove the remaining obligations. Apply `pullback.hom_ext` to reduce the goal to its premises. Rewrite using `[Category.assoc, Category.assoc, pullback.lift_fst, Sigma.ι_desc]`. Conclude with `y.1.2.2`. Rewrite using `[Category.assoc, Category.assoc, pullback.lift_snd, Sigma.ι_desc]`.

Conclude with `y.2`. Introduce and unpack `⟨⟨c, v, hv⟩, hk⟩ ⟨⟨c', v', hv'⟩, hk'⟩ h`. Establish `h'` using `hb.1 (a₁ := ⟨c, v⟩) (a₂ := ⟨c', v'⟩) (congrArg Subtype.val h)`. Take `⟨rfl, h2⟩` from `Sigma.mk.inj_iff.1 h'`. Take `rfl` from `eq_of_heq h2`.

Both sides reduce to the same expression. Introduce and unpack `⟨y, hy⟩`. Take `⟨⟨c, v⟩, rfl⟩` from `hb.2 y`. Establish `a1 : v ≫ s₁ = x ≫ pullback.fst π f`. Rewrite using `[← hy, Category.assoc, Category.assoc, pullback.lift_fst, Sigma.ι_desc]`.

Establish `a2 : v ≫ κ c = x ≫ pullback.snd π f`. Rewrite using `[← hy, Category.assoc, Category.assoc, pullback.lift_snd, Sigma.ι_desc]`. Conclude with `⟨⟨(c, ⟨v, a1⟩), a2⟩, rfl⟩`.
-/
private theorem fet_lift {I : Type} [Finite I] {ZM ZN Q Pw : Scheme.{0}} (s₁ : ZM ⟶ ZN) [IsFinite s₁] [Etale s₁]
    (π : ZN ⟶ Q) (f : Pw ⟶ Q) (κ : I → (ZM ⟶ Pw))
    [IsFinite (pullback.fst π f)] [Etale (pullback.fst π f)] (m : ℕ)
    (hκ : ∀ c, s₁ ≫ π = κ c ≫ f)
    (hm : ∀ (K : Type) [Field K] [IsAlgClosed K] (z : Spec (CommRingCat.of K) ⟶ ZN) (ζ : Spec (CommRingCat.of K) ⟶ Pw),
      z ≫ π = ζ ≫ f →
      Nat.card {x : I × {v : Spec (CommRingCat.of K) ⟶ ZM // v ≫ s₁ = z} // x.2.1 ≫ κ x.1 = ζ} = m)
    (e : (Sigma.desc fun _ : I => s₁) ≫ π = Sigma.desc κ ≫ f) :
    FEt (pullback.lift (Sigma.desc fun _ : I => s₁) (Sigma.desc κ) e) m := by
  have hf := desc_finite (I := I) s₁
  have he := desc_etale (I := I) s₁
  have h1 : pullback.lift (Sigma.desc fun _ : I => s₁) (Sigma.desc κ) e ≫ pullback.fst π f = Sigma.desc fun _ : I => s₁ :=
    pullback.lift_fst _ _ _
  refine ⟨?_, ?_, fun K _ _ x => ?_⟩
  · have : IsFinite (pullback.lift (Sigma.desc fun _ : I => s₁) (Sigma.desc κ) e ≫ pullback.fst π f) := by
      rw [h1]; exact hf
    exact IsFinite.of_comp _ (pullback.fst π f)
  · have : Etale (pullback.lift (Sigma.desc fun _ : I => s₁) (Sigma.desc κ) e ≫ pullback.fst π f) := by
      rw [h1]; exact he
    exact Etale.of_comp _ (pullback.fst π f)
  · have hb := UpperTheory.bijective_sigma_spec_points_coproduct (fun _ : I => ZM) K
    rw [← hm K (x ≫ pullback.fst π f) (x ≫ pullback.snd π f) (by simp [pullback.condition])]
    symm
    refine Nat.card_congr (Equiv.ofBijective
      (fun y => ⟨y.1.2.1 ≫ Sigma.ι (fun _ : I => ZM) y.1.1, ?_⟩) ⟨?_, ?_⟩)
    · apply pullback.hom_ext
      · rw [Category.assoc, Category.assoc, pullback.lift_fst, Sigma.ι_desc]
        exact y.1.2.2
      · rw [Category.assoc, Category.assoc, pullback.lift_snd, Sigma.ι_desc]
        exact y.2
    · rintro ⟨⟨c, v, hv⟩, hk⟩ ⟨⟨c', v', hv'⟩, hk'⟩ h
      have h' := hb.1 (a₁ := ⟨c, v⟩) (a₂ := ⟨c', v'⟩) (congrArg Subtype.val h)
      obtain ⟨rfl, h2⟩ := Sigma.mk.inj_iff.1 h'
      obtain rfl := eq_of_heq h2
      rfl
    · rintro ⟨y, hy⟩
      obtain ⟨⟨c, v⟩, rfl⟩ := hb.2 y
      have a1 : v ≫ s₁ = x ≫ pullback.fst π f := by
        rw [← hy, Category.assoc, Category.assoc, pullback.lift_fst, Sigma.ι_desc]
      have a2 : v ≫ κ c = x ≫ pullback.snd π f := by
        rw [← hy, Category.assoc, Category.assoc, pullback.lift_snd, Sigma.ι_desc]
      exact ⟨⟨(c, ⟨v, a1⟩), a2⟩, rfl⟩

/- English proof (translation)
Establish `key : ∀ v, L.CongOne n v → L.CongOne n (u * v * u⁻¹)` using `fun v hv x hx => by`. Establish `i1 : L.actG u⁻¹ x ∈ LaHat D` using `integ_of_mem (inv_mem hu) x hx`. Take `⟨y, hy, e⟩` from `hv _ i1`. Use `⟨L.actG u y, integ_of_mem hu y hy, ?_⟩` and prove the remaining obligations. Establish `e2 : L.actG u (L.actG u⁻¹ x) = x`.

Rewrite using `[← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]`. Rewrite using `[map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply, e, map_add, e2, map_nsmul]`. Use `⟨key _ hv.1, ?_⟩` and prove the remaining obligations. Establish `: (u * v * u⁻¹)⁻¹ = u * v⁻¹ * u⁻¹` using `by group`. Rewrite using `[this]`.

Conclude with `key _ hv.2`.
-/
private theorem KN_conj {p : ℕ} [Fact p.Prime] {D : Datum p} {G : HTGroup p} (L : Link D G) {n : ℕ} {u v : G.GAf}
    (hu : u ∈ L.KN 1) (hv : v ∈ L.KN n) : u * v * u⁻¹ ∈ L.KN n := by
  have key : ∀ v, L.CongOne n v → L.CongOne n (u * v * u⁻¹) := fun v hv x hx => by
    have i1 : L.actG u⁻¹ x ∈ LaHat D := integ_of_mem (inv_mem hu) x hx
    obtain ⟨y, hy, e⟩ := hv _ i1
    refine ⟨L.actG u y, integ_of_mem hu y hy, ?_⟩
    have e2 : L.actG u (L.actG u⁻¹ x) = x := by
      rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]
    rw [map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply, e, map_add, e2, map_nsmul]
  refine ⟨key _ hv.1, ?_⟩
  have : (u * v * u⁻¹)⁻¹ = u * v⁻¹ * u⁻¹ := by group
  rw [this]
  exact key _ hv.2

/- English proof (translation)
Take `⟨π, o, ψ, φ, hw, h1, h2, h3⟩` from `T.tr_eq N' N h a b`. Conclude with `⟨⟨π, o, ψ, φ, h1, h2⟩, hw, h3⟩`.
-/
private theorem wit_of {p : ℕ} [Fact p.Prime] {D : Datum p} {G : HTGroup p} {L : Link D G} {E : Type} [Field E] [NumberField E]
    {gb : GBase D.toG E} {k : ℕ} (T : KS L gb k) (N' N : Lv p) (h : G.GAf) (a) (b) :
    ∃ (W : Wit T h N' N) (hw : (W.ψ.left ≫ W.φ.φ) ≫ (T.M N).univ.A.hom = (T.M N').univ.A.hom ≫ W.π),
      T.X.tr (T.lev N') (T.lev N) h a b ≫ (T.e N).hom =
        (T.e N').hom ≫ GlobalTheory.KS.powMap W.π (W.ψ.left ≫ W.φ.φ) hw k := by
  obtain ⟨π, o, ψ, φ, hw, h1, h2, h3⟩ := T.tr_eq N' N h a b
  exact ⟨⟨π, o, ψ, φ, h1, h2⟩, hw, h3⟩

/- English proof (translation)
Establish `h1 : IsUnit ((q : ℕ) : E)` using `(Nat.cast_ne_zero.2 hq).isUnit`. Establish `h2 : IsUnit ((q : ℕ) : Γ(Z, ⊤))`. Use `h1.map ((Scheme.ΓSpecIso (CommRingCat.of E)).inv ≫ f.appTop).hom` as an intermediate fact. Simplify using `using this`. Conclude with `Scheme.basicOpen_of_isUnit _ h2`.
-/
private theorem basicOpen_top {E : Type} [Field E] [CharZero E] {Z : Scheme.{0}} (f : Z ⟶ Spec (CommRingCat.of E)) (q : ℕ) (hq : q ≠ 0) :
    Z.basicOpen ((q : ℕ) : Γ(Z, ⊤)) = ⊤ := by
  have h1 : IsUnit ((q : ℕ) : E) := (Nat.cast_ne_zero.2 hq).isUnit
  have h2 : IsUnit ((q : ℕ) : Γ(Z, ⊤)) := by
    have := h1.map ((Scheme.ΓSpecIso (CommRingCat.of E)).inv ≫ f.appTop).hom
    simpa using this
  exact Scheme.basicOpen_of_isUnit _ h2

/- English proof (translation)
Establish `h` using `(Spec.preimage f).hom`. Introduce `h0`. Establish `: h ((q : ℕ) : E) = 0` using `by rw [map_natCast]; exact h0`. Conclude with `(Nat.cast_ne_zero.2 hq) ((map_eq_zero h).1 this)`.
-/
private theorem natCast_ne {E K : Type} [Field E] [CharZero E] [Field K] (f : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of E)) (q : ℕ) (hq : q ≠ 0) :
    ((q : ℕ) : K) ≠ 0 := by
  have h := (Spec.preimage f).hom
  intro h0
  have : h ((q : ℕ) : E) = 0 := by rw [map_natCast]; exact h0
  exact (Nat.cast_ne_zero.2 hq) ((map_eq_zero h).1 this)

/- English proof (translation)
Substitute `hU` using the available equality. Establish `h2 : (f ⁻¹ᵁ ⊤).ι ≫ f = (f ∣_ ⊤) ≫ (⊤ : Y.Opens).ι` using `(morphismRestrict_ι f ⊤).symm`. Establish `h3 : Etale ((f ⁻¹ᵁ ⊤).ι ≫ f)` using `by rw [h2]; infer_instance`. Establish `h4 : Etale ((⊤ : X.Opens).ι ≫ f)` using `h3`. Establish `h5 : Etale ((Scheme.topIso X).inv ≫ (⊤ : X.Opens).ι ≫ f)` using `inferInstance`.

Establish `e : f = (Scheme.topIso X).inv ≫ (⊤ : X.Opens).ι ≫ f` using `by simp`. Rewrite using `[e]`. Conclude with `h5`.
-/
private theorem etale_of_restrict {X Y : Scheme.{0}} (f : X ⟶ Y) (U : Y.Opens) (hU : U = ⊤) (h : Etale (f ∣_ U)) : Etale f := by
  subst hU
  have h2 : (f ⁻¹ᵁ ⊤).ι ≫ f = (f ∣_ ⊤) ≫ (⊤ : Y.Opens).ι := (morphismRestrict_ι f ⊤).symm
  have h3 : Etale ((f ⁻¹ᵁ ⊤).ι ≫ f) := by rw [h2]; infer_instance
  have h4 : Etale ((⊤ : X.Opens).ι ≫ f) := h3
  have h5 : Etale ((Scheme.topIso X).inv ≫ (⊤ : X.Opens).ι ≫ f) := inferInstance
  have e : f = (Scheme.topIso X).inv ≫ (⊤ : X.Opens).ι ≫ f := by simp
  rw [e]
  exact h5

/- English proof (translation)
Substitute `e` using the available equality. Conclude with `X.tr_mul _ _ _ _ _ _ _ _ _ _ _`.
-/
private theorem tr_comp {B : Scheme.{0}} {Γ : Type} [Group Γ] (X : UpperTheory.Gal.G3.Tower B Γ) {i j m : X.ι} {h h' h'' : Γ}
    (a) (b) (a') (b') (e : h' * h = h'') (a'') (b'') :
    X.tr i j h a b ≫ X.tr j m h' a' b' = X.tr i m h'' a'' b'' := by
  subst e
  exact X.tr_mul _ _ _ _ _ _ _ _ _ _ _

/- English proof (translation)
Introduce `hM hNum hCls hPow hInv hFet hLift hSep hCount p _ D G L E _ _ gb w q _ r 𝔴 𝔫 S k T K₀ hLev N c a hNa C hKN _ J g j i hi hK hT hdiv hidx Tj Lj`. Substitute `hK` using the available equality. Take `⟨t, ht⟩` from `(g j).dvd`. Establish `hMpos : 0 < (g j).M.1` using `by have := (g j).M.2.1; omega`. Establish `hNpos : 0 < N.1` using `by have := N.2.1; omega`.

Establish `hnum' : S.Num (g j).M.1 (c * t) (t * a)`. Rewrite using `[ht]`. Conclude with `(hNum p D E gb w q r 𝔴 𝔫 S N.1 hNpos).2 c a t hNa`. Take `⟨⟨C'⟩, -⟩` from `hCls q (datAt S.atq S.sp) (Ow w) E S.b gb (algebraMap _ _) S.mat (g j).M.1 S.N₀ (c * t) (t * a) S.𝔞 hnum'.1 hMpos S.std.three S.std.cop hnum'.2 S.Y _ (T.M (g j).M).s (T.M (g j).M).univ`. Establish `hKm1 : L.KN (g j).M.1 ≤ L.KN 1` using `KN_anti (one_dvd _)`.

Establish `hKn1 : L.KN N.1 ≤ L.KN 1` using `KN_anti (one_dvd _)`. Establish `hmN : L.KN (g j).M.1 ≤ L.KN N.1` using `KN_anti (g j).dvd`. Establish `hidxM : (L.KN (g j).M.1).relIndex (g j).K ≠ 0` using `fun h0 => GlobalTheory.W2.relIndex_KN_ne_zero L one_pos hMpos (Subgroup.relIndex_eq_zero_of_le_right (g j).le_one h0)`. Establish `hidxN : (L.KN N.1).relIndex (g j).K ≠ 0` using `fun h0 => GlobalTheory.W2.relIndex_KN_ne_zero L one_pos hNpos (Subgroup.relIndex_eq_zero_of_le_right (g j).le_one h0)`. Establish `hfinI : Finite (g j).I`.

Establish `: ((L.KN N.1).subgroupOf (g j).K).FiniteIndex` using `⟨hidxN⟩`. Conclude with `Subgroup.finite_quotient_of_finiteIndex`. Establish `A1 : (1 : G.GAf) ∈ T.X.Δ` using `one_mem _`. Establish `B1 : ∀ u ∈ T.X.K (T.lev (g j).M), 1 * u * 1⁻¹ ∈ T.X.K (T.lev N)` using `fun u hu => by`. Rewrite `hu`, the goal using `[T.K_eq]`.

Simplify using `using hmN hu`. Establish `A2 : ∀ cc : (g j).I, (g j).h * (cc.out : G.GAf) ∈ T.X.Δ` using `fun cc => (T.Δ_eq _).2 ((g j).int.mul (integ_of_mem ((g j).le_one cc.out.2)))`. Establish `B2 : ∀ cc : (g j).I, ∀ u ∈ T.X.K (T.lev (g j).M), ((g j).h * (cc.out : G.GAf)) * u * ((g j).h * (cc.out : G.GAf))⁻¹ ∈ T.X.K (T.lev N)` using `fun cc u hu => by`. Rewrite `hu`, the goal using `[T.K_eq]`. Conclude with `(g j).adm _ cc.out.2 u hu`.

Establish `hW : ∀ cc : (g j).I, ∃ (W : Wit T ((g j).h * (cc.out : G.GAf)) (g j).M N) (_ : Lift S T Lj W C' C) (hw : (W.ψ.left ≫ W.φ.φ) ≫ (T.M N).univ.A.hom = (T.M (g j).M).univ.A.hom ≫ W.π), T.X.tr (T.lev (g j).M) (T.lev N) _ (A2 cc) (B2 cc) ≫ (T.e N).hom = (T.e (g j).M).hom ≫ GlobalTheory. …` using `fun cc => by`. Take `⟨W, hw, h3⟩` from `wit_of T (g j).M N _ (A2 cc) (B2 cc)`. Take `⟨l⟩` from `hLift p D G L E gb w q r 𝔴 𝔫 S k T (g j).K hLev i (g j).h hi hT (g j).int Tj Lj (g j).M N t c a ht hNa C' C cc.out cc.out.2 W`. Conclude with `⟨W, l, hw, h3⟩`. Use `choose W l hw htr using hW`.

Set `tr1 : T.X.Z (T.lev (g j).M) ⟶ T.X.Z (T.lev N)` to `T.X.tr _ _ 1 A1 B1`. Set `κc : (g j).I → (T.X.Z (T.lev (g j).M) ⟶ (GlobalTheory.KS.pow Lj.o.A k).left)` to `fun cc => (T.e (g j).M).hom ≫ GlobalTheory.KS.powMap (l cc).y (l cc).m.φ (l cc).m.cart.1.w k`. Establish `e1 : ∀ cc, tr1 ≫ S.pi T C = κc cc ≫ Lj.ksP k` using `fun cc => by`. Establish `h1 : tr1 ≫ S.pi T C = S.pi T C'` using `hInv p D G L E gb w q r 𝔴 𝔫 S k T (g j).K hLev (g j).M N t c a ht hNa C' C 1 (one_mem _) A1 B1`. Establish `h2` using `(hPow _ _ _ (T.M (g j).M).univ.A Lj.o.A S.Y.univ.A (l cc).y Lj.s (l cc).m.φ Lj.ms.φ (l cc).m.cart.1.w Lj.ms.cart.1.w k).2.2 (by`.

Rewrite using `[Category.assoc, Lj.ms.cart.1.w, ← Category.assoc, (l cc).m.cart.1.w, Category.assoc])`. Rewrite using `[h1]`. Simplify using `only [κc, Site.pi, Cls.pw, Category.assoc]`. Use `congr 1`. Rewrite using `[TjE.ksP, h2]`.

Conclude with `powMap_congr (l cc).ys.symm (l cc).ms.symm _ _ k`. Establish `e2 : ∀ cc, κc cc ≫ Lj.ksR k = T.X.tr (T.lev (g j).M) (T.lev N) _ (A2 cc) (B2 cc) ≫ S.pi T C` using `fun cc => by`. Establish `wψ : Lj.ψ.left ≫ Lj.o'.A.hom = Lj.o.A.hom ≫ 𝟙 _` using `by simp`. Establish `h2` using `(hPow _ _ _ (T.M (g j).M).univ.A Lj.o.A Lj.o'.A (l cc).y (𝟙 _) (l cc).m.φ Lj.ψ.left (l cc).m.cart.1.w wψ k).2.2 (by`. Rewrite using `[Category.assoc, wψ, ← Category.assoc, (l cc).m.cart.1.w, Category.assoc])`.

Establish `w2 : ((l cc).m.φ ≫ Lj.ψ.left) ≫ Lj.o'.A.hom = (T.M (g j).M).univ.A.hom ≫ ((l cc).y ≫ 𝟙 _)`. Rewrite using `[Category.assoc, wψ, ← Category.assoc, (l cc).m.cart.1.w, Category.assoc]`. Establish `h5` using `(hPow _ _ _ (T.M (g j).M).univ.A Lj.o'.A S.Y.univ.A ((l cc).y ≫ 𝟙 _) Lj.t ((l cc).m.φ ≫ Lj.ψ.left) Lj.mt.φ w2 Lj.mt.cart.1.w k).2.2 (by`. Rewrite using `[Category.assoc, Lj.mt.cart.1.w, ← Category.assoc, w2, Category.assoc])`. Establish `h6` using `(hPow _ _ _ (T.M (g j).M).univ.A (T.M N).univ.A S.Y.univ.A (W cc).π C.j ((W cc).ψ.left ≫ (W cc).φ.φ) C.m.φ (hw cc) C.m.cart.1.w k).2.2 (by`.

Rewrite using `[Category.assoc, C.m.cart.1.w, ← Category.assoc, hw cc, Category.assoc])`. Establish `h3` using `htr cc`. Simplify using `only [κc, Site.pi, Cls.pw, TjE.ksR, Category.assoc]`. Rewrite using `[reassoc_of% h3, h6, piMap_eq, ← Category.assoc (GlobalTheory.KS.powMap (l cc).y _ _ k), h2, h5]`. Use `congr 1`.

Use `powMap_congr ?_ ?_ _ _ k` and prove the remaining obligations. Rewrite using `[Category.comp_id]`. Conclude with `(l cc).yt`. Simplify using `using (l cc).mt`. Establish `hpb : IsPullback (pullback.fst (S.pi T C) (Lj.ksP k)) ((pullback.snd (S.pi T C) (Lj.ksP k) ≫ (GlobalTheory.KS.pow Lj.o.A k).hom) ≫ Lj.g) ((S.pi T C ≫ (GlobalTheory.KS.pow S.Y.univ.A k).hom) ≫ S.π) Tj.s` using `((IsPullback.of_hasPullback (S.pi T C) (Lj.ksP k)).paste_vert ((hPow _ _ _ Lj.o.A S.Y.univ.A S.Y.univ.A Lj.s (𝟙 _) Lj.ms.φ (𝟙 _) Lj.ms.cart.1.w (by simp) k).1 Lj.ms.cart.1)).paste_vert Lj.pb`.

Take `⟨bf, be, bd⟩` from `hM.corr q (datAt S.atq S.sp) (Ow w) S.f S.b S.N₀ r 𝔴 S.std S.M i hi Tj _ _ _ _ _ hpb`. Establish `hq0 : q ≠ 0` using `(Fact.out : q.Prime).ne_zero`. Establish `: IsFinite (pullback.fst (S.pi T C) (Lj.ksP k))` using `bf`. Establish `: Etale (pullback.fst (S.pi T C) (Lj.ksP k))` using `etale_of_restrict _ _ (basicOpen_top (T.X.q (T.lev N)) q hq0) be`. Establish `: IsFinite tr1` using `T.X.fin _ _ A1 B1`.

Establish `: Etale tr1` using `T.X.etale _ _ A1 B1`. Establish `hm : ∀ (K : Type) [Field K] [IsAlgClosed K] (z : Spec (CommRingCat.of K) ⟶ T.X.Z (T.lev N)) (ζ : Spec (CommRingCat.of K) ⟶ (GlobalTheory.KS.pow Lj.o.A k).left), z ≫ S.pi T C = ζ ≫ Lj.ksP k → Nat.card {x : (g j).I × {v : Spec (CommRingCat.of K) ⟶ T.X.Z (T.lev (g j).M) // v ≫ tr1 = …`. Introduce `K _ _ z ζ hz`. Establish `hqK : ((q : ℕ) : K) ≠ 0` using `natCast_ne (z ≫ T.X.q (T.lev N)) q hq0`. Establish `hcard` using `bd K hqK z`.

Take `⟨z₀, hz₀⟩` from `GlobalTheory.T.exists_lift_of_etale_surjective' K _ _ tr1 inferInstance (T.X.onto _ _ A1 B1) z`. Establish `Au : ∀ u : L.KN N.1, (u : G.GAf) ∈ T.X.Δ` using `fun u => (T.Δ_eq _).2 (integ_of_mem (hKn1 u.2))`. Establish `Bu : ∀ u : L.KN N.1, ∀ v ∈ T.X.K (T.lev (g j).M), (u : G.GAf) * v * (u : G.GAf)⁻¹ ∈ T.X.K (T.lev (g j).M)` using `fun u v hv => by`. Rewrite `hv`, the goal using `[T.K_eq]`. Conclude with `KN_conj L (hKn1 u.2) hv`.

Set `tu : L.KN N.1 → (T.X.Z (T.lev (g j).M) ⟶ T.X.Z (T.lev (g j).M))` to `fun u => T.X.tr _ _ u (Au u) (Bu u)`. Establish `htu : ∀ u, tu u ≫ tr1 = tr1` using `fun u => by`. Establish `bN : ∀ v ∈ T.X.K (T.lev N), (u : G.GAf) * v * (u : G.GAf)⁻¹ ∈ T.X.K (T.lev N)` using `fun v hv => by`. Rewrite `hv`, the goal using `[T.K_eq]`. Conclude with `KN_conj L (hKn1 u.2) hv`.

Establish `bM : ∀ v ∈ T.X.K (T.lev (g j).M), (u : G.GAf) * v * (u : G.GAf)⁻¹ ∈ T.X.K (T.lev N)` using `fun v hv => by`. Use `Bu u v hv` as an intermediate fact. Rewrite `this`, the goal using `[T.K_eq]`. Conclude with `hmN this`. Establish `h1 : tu u ≫ tr1 = T.X.tr _ _ (u : G.GAf) (Au u) bM` using `tr_comp T.X _ _ _ _ (one_mul _) _ _`.

Establish `h2 : tr1 ≫ T.X.tr (T.lev N) (T.lev N) (u : G.GAf) (Au u) bN = T.X.tr _ _ (u : G.GAf) (Au u) bM` using `tr_comp T.X _ _ _ _ (mul_one _) _ _`. Establish `h3 : T.X.tr (T.lev N) (T.lev N) (u : G.GAf) (Au u) bN = 𝟙 _` using `T.X.tr_self _ _ _ _ (by rw [T.K_eq]; exact u.2)`. Rewrite using `[h1, ← h2, h3, Category.comp_id]`. Set `act : L.KN N.1 → {v : Spec (CommRingCat.of K) ⟶ T.X.Z (T.lev (g j).M) // v ≫ tr1 = z}` to `fun u => ⟨z₀ ≫ tu u, by rw [Category.assoc, htu, hz₀]⟩`. Establish `hs : Function.Surjective act`.

Introduce and unpack `⟨v, hv⟩`. Take `⟨x, hx, a', b', hy⟩` from `T.X.trans _ _ A1 B1 (fun x hx u hu => by`. Rewrite `hx`, `hu`, the goal using `[T.K_eq]`. Conclude with `KN_conj L (hKn1 hx) hu) K z₀ v (by rw [show T.X.tr _ _ 1 A1 B1 = tr1 from rfl, hz₀, hv])`. Establish `hx' : x ∈ L.KN N.1` using `by rwa [T.K_eq] at hx`.

Conclude with `⟨⟨x, hx'⟩, Subtype.ext hy.symm⟩`. Establish `he : ∀ u u' : L.KN N.1, act u = act u' ↔ (u : G.GAf)⁻¹ * u' ∈ L.KN (g j).M.1`. Introduce `u u'`. Prove the components needed by the constructor for the conclusion. Introduce `h`.

Establish `h1 : z₀ ≫ tu u = z₀ ≫ tu u'` using `congrArg Subtype.val h`. Set `kk : L.KN N.1` to `u' * u⁻¹`. Establish `h2 : tu u ≫ tu kk = tu u'` using `tr_comp T.X _ _ _ _ (by simp [kk]) _ _`. Establish `h3 : (z₀ ≫ tu u) ≫ tu kk = z₀ ≫ tu u` using `by rw [Category.assoc, h2, ← h1]`. Establish `h4` using `T.X.free (T.lev (g j).M) (T.lev N) (by rw [T.K_eq, T.K_eq]; exact hmN) kk (by rw [T.K_eq]; exact kk.2) (Au kk) (Bu kk) K _ h3`.

Rewrite `h4` using `[T.K_eq]`. Establish `h5` using `KN_conj L (inv_mem (hKn1 u.2)) h4`. Establish `h6 : (u : G.GAf)⁻¹ * kk * (u : G.GAf)⁻¹⁻¹ = (u : G.GAf)⁻¹ * u'` using `by show (u : G.GAf)⁻¹ * ((u' : G.GAf) * (u : G.GAf)⁻¹) * (u : G.GAf)⁻¹⁻¹ = _ group`. Rewrite `h5` using `[h6]`. Then use the resulting hypothesis. Introduce `h`.

Use `Subtype.ext ?_` and prove the remaining obligations. Set `ww : L.KN N.1` to `u⁻¹ * u'`. Establish `h1 : tu ww ≫ tu u = tu u'` using `tr_comp T.X _ _ _ _ (by simp [ww]) _ _`. Establish `h2 : tu ww = 𝟙 _` using `T.X.tr_self _ _ _ _ (by rw [T.K_eq]; exact h)`. Use `show z₀ ≫ tu u = z₀ ≫ tu u'`.

Rewrite using `[← h1, h2, Category.id_comp]`. Set `κ' : (g j).I → {v : Spec (CommRingCat.of K) ⟶ T.X.Z (T.lev (g j).M) // v ≫ tr1 = z} → {y : Spec (CommRingCat.of K) ⟶ (GlobalTheory.KS.pow Lj.o.A k).left // y ≫ Lj.ksP k = z ≫ S.pi T C}` to `fun cc v => ⟨v.1 ≫ κc cc, by rw [Category.assoc, ← e1, ← Category.assoc, v.2]⟩`. Establish `hF : Nat.card {y : Spec (CommRingCat.of K) ⟶ (GlobalTheory.KS.pow Lj.o.A k).left // y ≫ Lj.ksP k = z ≫ S.pi T C} = ((g j).K ⊓ (g j).K.comap (MulAut.conj (g j).h).toMonoidHom).relIndex (g j).K`. Rewrite using `[hidx]`. Use `Eq.trans ?_ hcard` and prove the remaining obligations.

Use `Nat.card_congr ⟨fun y => ⟨pullback.lift z y.1 y.2.symm, pullback.lift_fst _ _ _⟩, fun y => ⟨y.1 ≫ pullback.snd _ _, ?_⟩, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[Category.assoc, ← pullback.condition, ← Category.assoc, y.2]`. Introduce `y`. Conclude with `Subtype.ext (pullback.lift_snd _ _ _)`. Introduce `y`.

Use `Subtype.ext (pullback.hom_ext ?_ ?_)` and prove the remaining obligations. Rewrite using `[pullback.lift_fst]`. Conclude with `y.2.symm`. Rewrite using `[pullback.lift_snd]`. Establish `hKmH : L.KN (g j).M.1 ≤ (g j).K ⊓ (g j).K.comap (MulAut.conj (g j).h).toMonoidHom` using `fun u hu => by`.

Use `⟨hKN (hmN hu), hKN ?_⟩` and prove the remaining obligations. Use `(g j).adm 1 (one_mem _) u hu` as an intermediate fact. Simplify using `using this`. Establish `sep : ∀ (c₁ c₂ : (g j).I) (u₁ u₂ : L.KN N.1), κ' c₁ (act u₁) = κ' c₂ (act u₂) → (((c₁.out : (g j).K) : G.GAf) * u₁) * (((c₂.out : (g j).K) : G.GAf) * u₂)⁻¹ ∈ (g j).K ⊓ (g j).K.comap (MulAut.conj (g j).h).toMonoidHom`. Introduce `c₁ c₂ u₁ u₂ hκ`.

Establish `hval : (z₀ ≫ tu u₁) ≫ κc c₁ = (z₀ ≫ tu u₂) ≫ κc c₂` using `congrArg Subtype.val hκ`. Take `⟨V₁, hv₁, ht₁⟩` from `wit_of T (g j).M (g j).M u₁ (Au u₁) (Bu u₁)`. Take `⟨V₂, hv₂, ht₂⟩` from `wit_of T (g j).M (g j).M u₂ (Au u₂) (Bu u₂)`. Establish `pt : ∀ (u : L.KN N.1) (cc : (g j).I) (V : Wit T (u : G.GAf) (g j).M (g j).M) (hv : (V.ψ.left ≫ V.φ.φ) ≫ (T.M (g j).M).univ.A.hom = (T.M (g j).M).univ.A.hom ≫ V.π), tu u ≫ (T.e (g j).M).hom = (T.e (g j).M).hom ≫ GlobalTheory.KS.powMap V.π (V.ψ.left ≫ V.φ.φ) hv k → tu u ≫ κc cc ≫ ( …`. Introduce `u cc V hv ht`.

Simplify using `only [κc, Category.assoc]`. Rewrite using `[pow_hom, reassoc_of% ht, reassoc_of% (pow_hom V.π _ hv k)]`. Establish `hz' : (z₀ ≫ (T.e (g j).M).hom ≫ (GlobalTheory.KS.pow (T.M (g j).M).univ.A k).hom) ≫ V₁.π ≫ (l c₁).y = (z₀ ≫ (T.e (g j).M).hom ≫ (GlobalTheory.KS.pow (T.M (g j).M).univ.A k).hom) ≫ V₂.π ≫ (l c₂).y`. Establish `h1` using `hval =≫ (GlobalTheory.KS.pow Lj.o.A k).hom`. Simplify using `only [Category.assoc] at h1`.

Rewrite `h1` using `[pt u₁ c₁ V₁ hv₁ ht₁, pt u₂ c₂ V₂ hv₂ ht₂]`. Simplify `h1` using `only [Category.assoc]`. Establish `hS` using `hSep p D G L E gb w q r 𝔴 𝔫 S k T (g j).K hLev i (g j).h hi hT (g j).int Tj Lj (g j).M N t c a ht hNa C' C hdiv c₁.out c₁.out.2 c₂.out c₂.out.2 u₁ (hKN u₁.2) u₂ (hKN u₂.2) (W c₁) (W c₂) V₁ V₂ (l c₁) (l c₂) K _ hz'`. Conclude with `⟨(g j).K.mul_mem ((g j).K.mul_mem c₁.out.2 (hKN u₁.2)) ((g j).K.inv_mem ((g j).K.mul_mem c₂.out.2 (hKN u₂.2))), hS⟩`. Establish `hres` using `UpperTheory.card_fiber_eq_relIndex_of_normal_quotient G.GAf (g j).K _ (L.KN N.1) (L.KN (g j).M.1) hCount hmN hKN hKmH inf_le_left (fun x hx u hu => KN_conj L ((g j).le_one hx) hu) hidxM _ _ act hs he κ' hF sep ⟨ζ, hz.symm⟩`.

Rewrite using `[← hres]`. Use `Nat.card_congr (Equiv.subtypeEquivRight fun x => ?_)` and prove the remaining obligations. Conclude with `⟨fun h => Subtype.ext h, fun h => congrArg Subtype.val h⟩`. Establish `e0 : (Sigma.desc fun _ : (g j).I => tr1) ≫ S.pi T C = Sigma.desc κc ≫ Lj.ksP k`. Use `Sigma.hom_ext _ _ fun cc => ?_` and prove the remaining obligations.

Rewrite using `[Sigma.ι_desc_assoc, Sigma.ι_desc_assoc]`. Conclude with `e1 cc`. Establish `e3 : Sigma.desc κc ≫ Lj.ksR k = (Sigma.desc fun c : (g j).I => T.X.tr (T.lev (g j).M) (T.lev N) _ (A2 c) (B2 c)) ≫ S.pi T C`. Use `Sigma.hom_ext _ _ fun cc => ?_` and prove the remaining obligations. Rewrite using `[Sigma.ι_desc_assoc, Sigma.ι_desc_assoc]`.

Conclude with `e2 cc`. Conclude with `⟨Nat.pos_of_ne_zero fun h0 => hidxM (Subgroup.relIndex_eq_zero_of_le_right inf_le_left h0), Sigma.desc κc, e0, e3, fet_lift tr1 (S.pi T C) (Lj.ksP k) κc _ e1 hm e0⟩`.
-/
theorem UpperTheory.heckeCorrespondence_lies_in_tower_of_lift_count :
    MIn → NumEx → ClsEx → PowCart → PiInv → PiFet → LiftEx → LiftSep → Count → TjLies := by
  intro hM hNum hCls hPow hInv hFet hLift hSep hCount p _ D G L E _ _ gb w q _ r 𝔴 𝔫 S k T K₀ hLev N c a hNa C hKN _ J g j i hi hK hT hdiv hidx Tj Lj
  subst hK
  obtain ⟨t, ht⟩ := (g j).dvd
  have hMpos : 0 < (g j).M.1 := by have := (g j).M.2.1; omega
  have hNpos : 0 < N.1 := by have := N.2.1; omega
  have hnum' : S.Num (g j).M.1 (c * t) (t * a) := by
    rw [ht]; exact (hNum p D E gb w q r 𝔴 𝔫 S N.1 hNpos).2 c a t hNa
  obtain ⟨⟨C'⟩, -⟩ := hCls q (datAt S.atq S.sp) (Ow w) E S.b gb (algebraMap _ _) S.mat (g j).M.1 S.N₀ (c * t) (t * a) S.𝔞
    hnum'.1 hMpos S.std.three S.std.cop hnum'.2 S.Y _ (T.M (g j).M).s (T.M (g j).M).univ
  have hKm1 : L.KN (g j).M.1 ≤ L.KN 1 := KN_anti (one_dvd _)
  have hKn1 : L.KN N.1 ≤ L.KN 1 := KN_anti (one_dvd _)
  have hmN : L.KN (g j).M.1 ≤ L.KN N.1 := KN_anti (g j).dvd
  have hidxM : (L.KN (g j).M.1).relIndex (g j).K ≠ 0 := fun h0 =>
    GlobalTheory.W2.relIndex_KN_ne_zero L one_pos hMpos (Subgroup.relIndex_eq_zero_of_le_right (g j).le_one h0)
  have hidxN : (L.KN N.1).relIndex (g j).K ≠ 0 := fun h0 =>
    GlobalTheory.W2.relIndex_KN_ne_zero L one_pos hNpos (Subgroup.relIndex_eq_zero_of_le_right (g j).le_one h0)
  have hfinI : Finite (g j).I := by
    have : ((L.KN N.1).subgroupOf (g j).K).FiniteIndex := ⟨hidxN⟩
    exact Subgroup.finite_quotient_of_finiteIndex
  have A1 : (1 : G.GAf) ∈ T.X.Δ := one_mem _
  have B1 : ∀ u ∈ T.X.K (T.lev (g j).M), 1 * u * 1⁻¹ ∈ T.X.K (T.lev N) := fun u hu => by
    rw [T.K_eq] at hu ⊢
    simpa using hmN hu
  have A2 : ∀ cc : (g j).I, (g j).h * (cc.out : G.GAf) ∈ T.X.Δ := fun cc =>
    (T.Δ_eq _).2 ((g j).int.mul (integ_of_mem ((g j).le_one cc.out.2)))
  have B2 : ∀ cc : (g j).I, ∀ u ∈ T.X.K (T.lev (g j).M), ((g j).h * (cc.out : G.GAf)) * u * ((g j).h * (cc.out : G.GAf))⁻¹ ∈ T.X.K (T.lev N) :=
    fun cc u hu => by
      rw [T.K_eq] at hu ⊢
      exact (g j).adm _ cc.out.2 u hu
  have hW : ∀ cc : (g j).I, ∃ (W : Wit T ((g j).h * (cc.out : G.GAf)) (g j).M N) (_ : Lift S T Lj W C' C)
      (hw : (W.ψ.left ≫ W.φ.φ) ≫ (T.M N).univ.A.hom = (T.M (g j).M).univ.A.hom ≫ W.π),
      T.X.tr (T.lev (g j).M) (T.lev N) _ (A2 cc) (B2 cc) ≫ (T.e N).hom =
        (T.e (g j).M).hom ≫ GlobalTheory.KS.powMap W.π (W.ψ.left ≫ W.φ.φ) hw k := fun cc => by
    obtain ⟨W, hw, h3⟩ := wit_of T (g j).M N _ (A2 cc) (B2 cc)
    obtain ⟨l⟩ := hLift p D G L E gb w q r 𝔴 𝔫 S k T (g j).K hLev i (g j).h hi hT (g j).int Tj Lj (g j).M N t c a ht hNa C' C
      cc.out cc.out.2 W
    exact ⟨W, l, hw, h3⟩
  choose W l hw htr using hW

  let tr1 : T.X.Z (T.lev (g j).M) ⟶ T.X.Z (T.lev N) := T.X.tr _ _ 1 A1 B1
  let κc : (g j).I → (T.X.Z (T.lev (g j).M) ⟶ (GlobalTheory.KS.pow Lj.o.A k).left) :=
    fun cc => (T.e (g j).M).hom ≫ GlobalTheory.KS.powMap (l cc).y (l cc).m.φ (l cc).m.cart.1.w k
  have e1 : ∀ cc, tr1 ≫ S.pi T C = κc cc ≫ Lj.ksP k := fun cc => by
    have h1 : tr1 ≫ S.pi T C = S.pi T C' :=
      hInv p D G L E gb w q r 𝔴 𝔫 S k T (g j).K hLev (g j).M N t c a ht hNa C' C 1 (one_mem _) A1 B1
    have h2 := (hPow _ _ _ (T.M (g j).M).univ.A Lj.o.A S.Y.univ.A (l cc).y Lj.s (l cc).m.φ Lj.ms.φ
      (l cc).m.cart.1.w Lj.ms.cart.1.w k).2.2 (by
        rw [Category.assoc, Lj.ms.cart.1.w, ← Category.assoc, (l cc).m.cart.1.w, Category.assoc])
    rw [h1]
    simp only [κc, Site.pi, Cls.pw, Category.assoc]
    congr 1
    rw [TjE.ksP, h2]
    exact powMap_congr (l cc).ys.symm (l cc).ms.symm _ _ k
  have e2 : ∀ cc, κc cc ≫ Lj.ksR k = T.X.tr (T.lev (g j).M) (T.lev N) _ (A2 cc) (B2 cc) ≫ S.pi T C := fun cc => by
    have wψ : Lj.ψ.left ≫ Lj.o'.A.hom = Lj.o.A.hom ≫ 𝟙 _ := by simp
    have h2 := (hPow _ _ _ (T.M (g j).M).univ.A Lj.o.A Lj.o'.A (l cc).y (𝟙 _) (l cc).m.φ Lj.ψ.left
      (l cc).m.cart.1.w wψ k).2.2 (by
        rw [Category.assoc, wψ, ← Category.assoc, (l cc).m.cart.1.w, Category.assoc])
    have w2 : ((l cc).m.φ ≫ Lj.ψ.left) ≫ Lj.o'.A.hom = (T.M (g j).M).univ.A.hom ≫ ((l cc).y ≫ 𝟙 _) := by
      rw [Category.assoc, wψ, ← Category.assoc, (l cc).m.cart.1.w, Category.assoc]
    have h5 := (hPow _ _ _ (T.M (g j).M).univ.A Lj.o'.A S.Y.univ.A ((l cc).y ≫ 𝟙 _) Lj.t ((l cc).m.φ ≫ Lj.ψ.left) Lj.mt.φ
      w2 Lj.mt.cart.1.w k).2.2 (by
        rw [Category.assoc, Lj.mt.cart.1.w, ← Category.assoc, w2, Category.assoc])
    have h6 := (hPow _ _ _ (T.M (g j).M).univ.A (T.M N).univ.A S.Y.univ.A (W cc).π C.j ((W cc).ψ.left ≫ (W cc).φ.φ) C.m.φ
      (hw cc) C.m.cart.1.w k).2.2 (by
        rw [Category.assoc, C.m.cart.1.w, ← Category.assoc, hw cc, Category.assoc])
    have h3 := htr cc
    simp only [κc, Site.pi, Cls.pw, TjE.ksR, Category.assoc]
    rw [reassoc_of% h3, h6, piMap_eq, ← Category.assoc (GlobalTheory.KS.powMap (l cc).y _ _ k), h2, h5]
    congr 1
    refine powMap_congr ?_ ?_ _ _ k
    · rw [Category.comp_id]; exact (l cc).yt
    · simpa using (l cc).mt
  have hpb : IsPullback (pullback.fst (S.pi T C) (Lj.ksP k))
      ((pullback.snd (S.pi T C) (Lj.ksP k) ≫ (GlobalTheory.KS.pow Lj.o.A k).hom) ≫ Lj.g)
      ((S.pi T C ≫ (GlobalTheory.KS.pow S.Y.univ.A k).hom) ≫ S.π) Tj.s :=
    ((IsPullback.of_hasPullback (S.pi T C) (Lj.ksP k)).paste_vert
      ((hPow _ _ _ Lj.o.A S.Y.univ.A S.Y.univ.A Lj.s (𝟙 _) Lj.ms.φ (𝟙 _) Lj.ms.cart.1.w (by simp) k).1 Lj.ms.cart.1)).paste_vert Lj.pb
  obtain ⟨bf, be, bd⟩ := hM.corr q (datAt S.atq S.sp) (Ow w) S.f S.b S.N₀ r 𝔴 S.std S.M i hi Tj _ _ _ _ _ hpb

  have hq0 : q ≠ 0 := (Fact.out : q.Prime).ne_zero
  have : IsFinite (pullback.fst (S.pi T C) (Lj.ksP k)) := bf
  have : Etale (pullback.fst (S.pi T C) (Lj.ksP k)) :=
    etale_of_restrict _ _ (basicOpen_top (T.X.q (T.lev N)) q hq0) be
  have : IsFinite tr1 := T.X.fin _ _ A1 B1
  have : Etale tr1 := T.X.etale _ _ A1 B1
  have hm : ∀ (K : Type) [Field K] [IsAlgClosed K] (z : Spec (CommRingCat.of K) ⟶ T.X.Z (T.lev N)) (ζ : Spec (CommRingCat.of K) ⟶ (GlobalTheory.KS.pow Lj.o.A k).left),
      z ≫ S.pi T C = ζ ≫ Lj.ksP k →
      Nat.card {x : (g j).I × {v : Spec (CommRingCat.of K) ⟶ T.X.Z (T.lev (g j).M) // v ≫ tr1 = z} // x.2.1 ≫ κc x.1 = ζ} =
        (L.KN (g j).M.1).relIndex ((g j).K ⊓ (g j).K.comap (MulAut.conj (g j).h).toMonoidHom) := by
    intro K _ _ z ζ hz
    have hqK : ((q : ℕ) : K) ≠ 0 := natCast_ne (z ≫ T.X.q (T.lev N)) q hq0
    have hcard := bd K hqK z
    obtain ⟨z₀, hz₀⟩ := GlobalTheory.T.exists_lift_of_etale_surjective' K _ _ tr1 inferInstance (T.X.onto _ _ A1 B1) z
    have Au : ∀ u : L.KN N.1, (u : G.GAf) ∈ T.X.Δ := fun u => (T.Δ_eq _).2 (integ_of_mem (hKn1 u.2))
    have Bu : ∀ u : L.KN N.1, ∀ v ∈ T.X.K (T.lev (g j).M), (u : G.GAf) * v * (u : G.GAf)⁻¹ ∈ T.X.K (T.lev (g j).M) := fun u v hv => by
      rw [T.K_eq] at hv ⊢
      exact KN_conj L (hKn1 u.2) hv
    let tu : L.KN N.1 → (T.X.Z (T.lev (g j).M) ⟶ T.X.Z (T.lev (g j).M)) := fun u => T.X.tr _ _ u (Au u) (Bu u)
    have htu : ∀ u, tu u ≫ tr1 = tr1 := fun u => by
      have bN : ∀ v ∈ T.X.K (T.lev N), (u : G.GAf) * v * (u : G.GAf)⁻¹ ∈ T.X.K (T.lev N) := fun v hv => by
        rw [T.K_eq] at hv ⊢
        exact KN_conj L (hKn1 u.2) hv
      have bM : ∀ v ∈ T.X.K (T.lev (g j).M), (u : G.GAf) * v * (u : G.GAf)⁻¹ ∈ T.X.K (T.lev N) := fun v hv => by
        have := Bu u v hv
        rw [T.K_eq] at this ⊢
        exact hmN this
      have h1 : tu u ≫ tr1 = T.X.tr _ _ (u : G.GAf) (Au u) bM := tr_comp T.X _ _ _ _ (one_mul _) _ _
      have h2 : tr1 ≫ T.X.tr (T.lev N) (T.lev N) (u : G.GAf) (Au u) bN = T.X.tr _ _ (u : G.GAf) (Au u) bM :=
        tr_comp T.X _ _ _ _ (mul_one _) _ _
      have h3 : T.X.tr (T.lev N) (T.lev N) (u : G.GAf) (Au u) bN = 𝟙 _ :=
        T.X.tr_self _ _ _ _ (by rw [T.K_eq]; exact u.2)
      rw [h1, ← h2, h3, Category.comp_id]
    let act : L.KN N.1 → {v : Spec (CommRingCat.of K) ⟶ T.X.Z (T.lev (g j).M) // v ≫ tr1 = z} :=
      fun u => ⟨z₀ ≫ tu u, by rw [Category.assoc, htu, hz₀]⟩
    have hs : Function.Surjective act := by
      rintro ⟨v, hv⟩
      obtain ⟨x, hx, a', b', hy⟩ := T.X.trans _ _ A1 B1 (fun x hx u hu => by
        rw [T.K_eq] at hx hu ⊢
        exact KN_conj L (hKn1 hx) hu) K z₀ v (by rw [show T.X.tr _ _ 1 A1 B1 = tr1 from rfl, hz₀, hv])
      have hx' : x ∈ L.KN N.1 := by rwa [T.K_eq] at hx
      exact ⟨⟨x, hx'⟩, Subtype.ext hy.symm⟩
    have he : ∀ u u' : L.KN N.1, act u = act u' ↔ (u : G.GAf)⁻¹ * u' ∈ L.KN (g j).M.1 := by
      intro u u'
      constructor
      · intro h
        have h1 : z₀ ≫ tu u = z₀ ≫ tu u' := congrArg Subtype.val h
        let kk : L.KN N.1 := u' * u⁻¹
        have h2 : tu u ≫ tu kk = tu u' := tr_comp T.X _ _ _ _ (by simp [kk]) _ _
        have h3 : (z₀ ≫ tu u) ≫ tu kk = z₀ ≫ tu u := by rw [Category.assoc, h2, ← h1]
        have h4 := T.X.free (T.lev (g j).M) (T.lev N) (by rw [T.K_eq, T.K_eq]; exact hmN) kk
          (by rw [T.K_eq]; exact kk.2) (Au kk) (Bu kk) K _ h3
        rw [T.K_eq] at h4
        have h5 := KN_conj L (inv_mem (hKn1 u.2)) h4
        have h6 : (u : G.GAf)⁻¹ * kk * (u : G.GAf)⁻¹⁻¹ = (u : G.GAf)⁻¹ * u' := by
          show (u : G.GAf)⁻¹ * ((u' : G.GAf) * (u : G.GAf)⁻¹) * (u : G.GAf)⁻¹⁻¹ = _
          group
        rwa [h6] at h5
      · intro h
        refine Subtype.ext ?_
        let ww : L.KN N.1 := u⁻¹ * u'
        have h1 : tu ww ≫ tu u = tu u' := tr_comp T.X _ _ _ _ (by simp [ww]) _ _
        have h2 : tu ww = 𝟙 _ := T.X.tr_self _ _ _ _ (by rw [T.K_eq]; exact h)
        show z₀ ≫ tu u = z₀ ≫ tu u'
        rw [← h1, h2, Category.id_comp]
    let κ' : (g j).I → {v : Spec (CommRingCat.of K) ⟶ T.X.Z (T.lev (g j).M) // v ≫ tr1 = z} →
        {y : Spec (CommRingCat.of K) ⟶ (GlobalTheory.KS.pow Lj.o.A k).left // y ≫ Lj.ksP k = z ≫ S.pi T C} :=
      fun cc v => ⟨v.1 ≫ κc cc, by rw [Category.assoc, ← e1, ← Category.assoc, v.2]⟩
    have hF : Nat.card {y : Spec (CommRingCat.of K) ⟶ (GlobalTheory.KS.pow Lj.o.A k).left // y ≫ Lj.ksP k = z ≫ S.pi T C} =
        ((g j).K ⊓ (g j).K.comap (MulAut.conj (g j).h).toMonoidHom).relIndex (g j).K := by
      rw [hidx]
      refine Eq.trans ?_ hcard
      refine Nat.card_congr ⟨fun y => ⟨pullback.lift z y.1 y.2.symm, pullback.lift_fst _ _ _⟩,
        fun y => ⟨y.1 ≫ pullback.snd _ _, ?_⟩, ?_, ?_⟩
      · rw [Category.assoc, ← pullback.condition, ← Category.assoc, y.2]
      · intro y
        exact Subtype.ext (pullback.lift_snd _ _ _)
      · intro y
        refine Subtype.ext (pullback.hom_ext ?_ ?_)
        · rw [pullback.lift_fst]; exact y.2.symm
        · rw [pullback.lift_snd]
    have hKmH : L.KN (g j).M.1 ≤ (g j).K ⊓ (g j).K.comap (MulAut.conj (g j).h).toMonoidHom := fun u hu => by
      refine ⟨hKN (hmN hu), hKN ?_⟩
      have := (g j).adm 1 (one_mem _) u hu
      simpa using this
    have sep : ∀ (c₁ c₂ : (g j).I) (u₁ u₂ : L.KN N.1), κ' c₁ (act u₁) = κ' c₂ (act u₂) →
        (((c₁.out : (g j).K) : G.GAf) * u₁) * (((c₂.out : (g j).K) : G.GAf) * u₂)⁻¹ ∈ (g j).K ⊓ (g j).K.comap (MulAut.conj (g j).h).toMonoidHom := by
      intro c₁ c₂ u₁ u₂ hκ
      have hval : (z₀ ≫ tu u₁) ≫ κc c₁ = (z₀ ≫ tu u₂) ≫ κc c₂ := congrArg Subtype.val hκ
      obtain ⟨V₁, hv₁, ht₁⟩ := wit_of T (g j).M (g j).M u₁ (Au u₁) (Bu u₁)
      obtain ⟨V₂, hv₂, ht₂⟩ := wit_of T (g j).M (g j).M u₂ (Au u₂) (Bu u₂)
      have pt : ∀ (u : L.KN N.1) (cc : (g j).I) (V : Wit T (u : G.GAf) (g j).M (g j).M)
          (hv : (V.ψ.left ≫ V.φ.φ) ≫ (T.M (g j).M).univ.A.hom = (T.M (g j).M).univ.A.hom ≫ V.π),
          tu u ≫ (T.e (g j).M).hom = (T.e (g j).M).hom ≫ GlobalTheory.KS.powMap V.π (V.ψ.left ≫ V.φ.φ) hv k →
          tu u ≫ κc cc ≫ (GlobalTheory.KS.pow Lj.o.A k).hom =
            ((T.e (g j).M).hom ≫ (GlobalTheory.KS.pow (T.M (g j).M).univ.A k).hom) ≫ V.π ≫ (l cc).y := by
        intro u cc V hv ht
        simp only [κc, Category.assoc]
        rw [pow_hom, reassoc_of% ht, reassoc_of% (pow_hom V.π _ hv k)]
      have hz' : (z₀ ≫ (T.e (g j).M).hom ≫ (GlobalTheory.KS.pow (T.M (g j).M).univ.A k).hom) ≫ V₁.π ≫ (l c₁).y =
          (z₀ ≫ (T.e (g j).M).hom ≫ (GlobalTheory.KS.pow (T.M (g j).M).univ.A k).hom) ≫ V₂.π ≫ (l c₂).y := by
        have h1 := hval =≫ (GlobalTheory.KS.pow Lj.o.A k).hom
        simp only [Category.assoc] at h1
        rw [pt u₁ c₁ V₁ hv₁ ht₁, pt u₂ c₂ V₂ hv₂ ht₂] at h1
        simpa only [Category.assoc] using h1
      have hS := hSep p D G L E gb w q r 𝔴 𝔫 S k T (g j).K hLev i (g j).h hi hT (g j).int Tj Lj (g j).M N t c a ht hNa C' C hdiv
        c₁.out c₁.out.2 c₂.out c₂.out.2 u₁ (hKN u₁.2) u₂ (hKN u₂.2) (W c₁) (W c₂) V₁ V₂ (l c₁) (l c₂) K _ hz'
      exact ⟨(g j).K.mul_mem ((g j).K.mul_mem c₁.out.2 (hKN u₁.2)) ((g j).K.inv_mem ((g j).K.mul_mem c₂.out.2 (hKN u₂.2))), hS⟩
    have hres := UpperTheory.card_fiber_eq_relIndex_of_normal_quotient G.GAf (g j).K _ (L.KN N.1) (L.KN (g j).M.1) hCount hmN hKN hKmH inf_le_left
      (fun x hx u hu => KN_conj L ((g j).le_one hx) hu) hidxM _ _ act hs he κ' hF sep ⟨ζ, hz.symm⟩
    rw [← hres]
    refine Nat.card_congr (Equiv.subtypeEquivRight fun x => ?_)
    exact ⟨fun h => Subtype.ext h, fun h => congrArg Subtype.val h⟩
  have e0 : (Sigma.desc fun _ : (g j).I => tr1) ≫ S.pi T C = Sigma.desc κc ≫ Lj.ksP k := by
    refine Sigma.hom_ext _ _ fun cc => ?_
    rw [Sigma.ι_desc_assoc, Sigma.ι_desc_assoc]
    exact e1 cc
  have e3 : Sigma.desc κc ≫ Lj.ksR k = (Sigma.desc fun c : (g j).I => T.X.tr (T.lev (g j).M) (T.lev N) _ (A2 c) (B2 c)) ≫ S.pi T C := by
    refine Sigma.hom_ext _ _ fun cc => ?_
    rw [Sigma.ι_desc_assoc, Sigma.ι_desc_assoc]
    exact e2 cc
  exact ⟨Nat.pos_of_ne_zero fun h0 => hidxM (Subgroup.relIndex_eq_zero_of_le_right inf_le_left h0), Sigma.desc κc, e0, e3,
    fet_lift tr1 (S.pi T C) (Lj.ksP k) κc _ e1 hm e0⟩

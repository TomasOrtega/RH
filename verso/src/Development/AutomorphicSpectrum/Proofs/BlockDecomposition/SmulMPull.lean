import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.GradedChartDegrees.LmLeStd
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.GradedChartDegrees.ChartGrConst
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.Imports
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FlatBaseChangeCohomology
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CoordinatesRestrictAffineOpenStatement
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry TensorProduct GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb CrystallineSemistableComparison.Pb.Diso

noncomputable section

namespace GlobalTheory.CompanionTheory.DisoHm

section Lift
variable {R R' : Type} [CommRing R] [CommRing R'] {C C' : Type 1} [Category.{0} C] [Category.{0} C']
  {F : C ⥤ ModuleCat.{0} R} {F' : C' ⥤ ModuleCat.{0} R'} {σ : R →+* R'}

def liftM (m : CH.Mor F F' σ) {P : ObjectProperty C} (hP : ∀ T, P (m.G.obj T)) : CH.Mor (P.ι ⋙ F) F' σ where
  G := P.lift m.G hP
  τ := m.τ
  nat φ x := m.nat φ x
end Lift

section Scal
variable {b : Base} (L : b.Fun) {Λ : Type} [CommRing Λ] (c : Λ →+* b.R)

def thPc : PDF Λ (Thick L) where
  A := B.OA L c
  J := ⟨fun T => T.J, fun φ _ hx => φ.hle hx⟩
  dp {T} k x := T.δ.dpow k x
  dp_zero {T} _ hx := T.δ.dpow_zero hx
  dp_one {T} _ hx := T.δ.dpow_one hx
  dp_zero_right {T} _ hk := T.δ.dpow_eval_zero hk
  dp_add {T} k _ _ hx hy := T.δ.dpow_add hx hy
  dp_map φ k x hx := (φ.dp.2 x hx).symm

variable {L}

abbrev sPc (Q : ObjectProperty (Thick L)) : PDF Λ Q.FullSubcategory := (thPc L c).res Q.ι

def polyC {Q : ObjectProperty (Thick L)} (P : Poly (sP Q)) : Poly (sPc c Q) where
  P := P.P
  j := P.j
  X := P.X
  X_mem := P.X_mem
  univ := P.univ
  span := P.span

def frameC {Q : ObjectProperty (Thick L)} {d : ℕ} (E : Frame (sP Q) d) : Frame (sPc c Q) d where
  D := E.D
  ne := E.ne
  τ := E.τ
  mem := E.mem
  add := E.add
  nat := E.nat
  bij := E.bij

/- English proof (translation)
The claim follows from `h`.
-/
theorem polyC_crit {Q : ObjectProperty (Thick L)} (P : Poly (sP Q)) (r : ℤ)
    (h : P.Crit (fun _ => IdF.bot _) r) : (polyC c P).Crit (fun _ => IdF.bot _) r := h

end Scal

section G
variable {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] {X : Scheme.{0}} {q : X ⟶ Spec (CommRingCat.of O)}

/- English proof (translation)
Express the relevant statement in the definitionally equal form `Ideal.span {(l : T.obj.B) ^ m} = Ideal.span {T.obj.i ((l : O) ^ m)}`. Rewrite using `[map_pow, map_natCast]`.
-/
theorem lm_eq_span (Q : ObjectProperty (Thick (smFun X q))) (m : ℕ) (T : Q.FullSubcategory) :
    lm (l := l) T.obj m = (IdF.span (sP Q).A ((l : O) ^ m)).S T := by
  change Ideal.span {(l : T.obj.B) ^ m} = Ideal.span {T.obj.i ((l : O) ^ m)}
  rw [map_pow, map_natCast]

def gρ (h : OL l O) (Q : ObjectProperty (Thick (smFun X q))) (m : ℕ) (hQ : ∀ T, Q T → Good (l := l) T m)
    (P : ObjectProperty (Thick (Lm h q m))) (hP : ∀ T, P ((GF h Q m hQ).obj T)) (T : Q.FullSubcategory) :
    (sPc (Ideal.Quotient.mk _) P).A.obj ((P.lift (GF h Q m hQ) hP).obj T) →ₐ[O]
      (sP Q).A.obj T ⧸ (IdF.span (sP Q).A ((l : O) ^ m)).S T :=
  { Ideal.Quotient.factor (lm_eq_span Q m T).le with
    commutes' := fun a => rfl }

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem gρ_mk (h : OL l O) (Q : ObjectProperty (Thick (smFun X q))) (m : ℕ) (hQ : ∀ T, Q T → Good (l := l) T m)
    (P : ObjectProperty (Thick (Lm h q m))) (hP : ∀ T, P ((GF h Q m hQ).obj T)) (T : Q.FullSubcategory) (a : T.obj.B) :
    gρ h Q m hQ P hP T (Ideal.Quotient.mk (lm (l := l) T.obj m) a) = Ideal.Quotient.mk _ a := rfl

/- English proof (translation)
Introduce `x y hxy`. Take `⟨a, rfl⟩` from `Ideal.Quotient.mk_surjective (show GB (l := l) T.obj m from x)`. Take `⟨b, rfl⟩` from `Ideal.Quotient.mk_surjective (show GB (l := l) T.obj m from y)`. Establish `e : Ideal.Quotient.mk ((IdF.span (sP Q).A ((l : O) ^ m)).S T) (show T.obj.B from a) = Ideal.Quotient.mk _ (show T.obj.B from b)` using `hxy`. Conclude with `Ideal.Quotient.eq.2 ((lm_eq_span Q m T).ge (Ideal.Quotient.eq.1 e))`.
-/
theorem gρ_inj (h : OL l O) (Q : ObjectProperty (Thick (smFun X q))) (m : ℕ) (hQ : ∀ T, Q T → Good (l := l) T m)
    (P : ObjectProperty (Thick (Lm h q m))) (hP : ∀ T, P ((GF h Q m hQ).obj T)) (T : Q.FullSubcategory) :
    Function.Injective (gρ h Q m hQ P hP T) := by
  intro x y hxy
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective (show GB (l := l) T.obj m from x)
  obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective (show GB (l := l) T.obj m from y)
  have e : Ideal.Quotient.mk ((IdF.span (sP Q).A ((l : O) ^ m)).S T) (show T.obj.B from a) = Ideal.Quotient.mk _ (show T.obj.B from b) := hxy
  exact Ideal.Quotient.eq.2 ((lm_eq_span Q m T).ge (Ideal.Quotient.eq.1 e))

def gQ (h : OL l O) (Q : ObjectProperty (Thick (smFun X q))) (m : ℕ) (hQ : ∀ T, Q T → Good (l := l) T m)
    (P : ObjectProperty (Thick (Lm h q m))) (hP : ∀ T, P ((GF h Q m hQ).obj T)) :
    QMor (sPc (Ideal.Quotient.mk _) P) (sP Q) (IdF.span (sP Q).A ((l : O) ^ m)) where
  G := P.lift (GF h Q m hQ) hP
  ρ := gρ h Q m hQ P hP
  inj := gρ_inj h Q m hQ P hP
  nat {T T'} φ x y hxy := by
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective (show GB (l := l) T.obj m from x)
    have e : Ideal.Quotient.mk ((IdF.span (sP Q).A ((l : O) ^ m)).S T) (show T.obj.B from a) = Ideal.Quotient.mk _ y := hxy
    have e' := (IdF.span (sP Q).A ((l : O) ^ m)).map_mem φ (Ideal.Quotient.eq.1 e)
    rw [map_sub] at e'
    exact Ideal.Quotient.eq.2 e'
  dp T k x y hx hy hxy := by
    have hT := hQ _ T.property
    have e : x = Ideal.Quotient.mk (lm (l := l) T.obj m) (show T.obj.B from y) := gρ_inj h Q m hQ P hP T hxy
    subst e
    have hy' : (show T.obj.B from y) ∈ T.obj.J := hy
    have := (GD_spec T.obj m hT).2 k (show T.obj.B from y) (T.obj.δ.dpow k y) (Ideal.mem_sup_left hy')
      (T.obj.δ.factorial_mul_dpow_eq_pow hy')
    exact congrArg (gρ h Q m hQ P hP T) this

def gP (h : OL l O) (Q : ObjectProperty (Thick (smFun X q))) (m : ℕ) (hQ : ∀ T, Q T → Good (l := l) T m)
    (P : ObjectProperty (Thick (Lm h q m))) (hP : ∀ T, P ((GF h Q m hQ).obj T)) :
    CH.Mor (P.ι ⋙ OMm h q m) (sq (IdF.top (sP Q).A) (stdI Q none ((l : O) ^ m))) (RingHom.id O) :=
  liftM (gMor h Q m hQ) hP

end G

section Gen
variable {R : Type} [CommRing R] {C : Type 1} [Category.{0} C] {A : C ⥤ CommAlgCat.{0} R}

/- English proof (translation)
Consider the cases of `a`. Consider the cases of `b`. Reduce the equality to equality of the corresponding arguments. Conclude with `funext h`.
-/
theorem IdF.ext' {a b : IdF A} (h : ∀ T, a.S T = b.S T) : a = b := by
  cases a
  cases b
  congr
  exact funext h

/- English proof (translation)
Use `CrystallineSemistableComparison.P.mapH_bij _ (fun n => ⟨fun x y hxy => ?_, fun y => ?_⟩) j` and prove the remaining obligations. Use function extensionality and compare the values at `s`. Use `(h _).1 ?_` and prove the remaining obligations. Use `congrFun hxy s` as an intermediate fact. Conclude with `this`.

Conclude with `⟨fun s => Function.surjInv (h _).2 (y s), funext fun s => Function.surjInv_eq (h _).2 (y s)⟩`.
-/
theorem idM_bij {R' : Type} [CommRing R'] {σ : R →+* R'} {F : C ⥤ ModuleCat.{0} R} {F' : C ⥤ ModuleCat.{0} R'}
    (τ : ∀ T, F.obj T →ₛₗ[σ] F'.obj T)
    (nat : ∀ {T T' : C} (φ : T ⟶ T') (x : F.obj T), τ T' ((F.map φ).hom x) = (F'.map φ).hom (τ T x))
    (h : ∀ T, Function.Bijective (τ T)) (j : ℕ) :
    Function.Bijective ((⟨𝟭 C, τ, nat⟩ : CH.Mor F F' σ).pull j) := by
  refine CrystallineSemistableComparison.P.mapH_bij _ (fun n => ⟨fun x y hxy => ?_, fun y => ?_⟩) j
  · funext s
    refine (h _).1 ?_
    have := congrFun hxy s
    exact this
  · exact ⟨fun s => Function.surjInv (h _).2 (y s), funext fun s => Function.surjInv_eq (h _).2 (y s)⟩

/- English proof (translation)
Take `rfl : a = a'` from `IdF.ext' ha`. Take `rfl : b = b'` from `IdF.ext' hb`. Use `idM_bij (sqLe (a := a) (b := b) (a' := a) (b' := b) (fun T => le_rfl) (fun T => le_rfl)).τ (sqLe (a := a) (b := b) (a' := a) (b' := b) (fun T => le_rfl) (fun T => le_rfl)).nat (fun T => ?_) j` and prove the remaining obligations. Establish `e : (sqLe (a` using `a) (b := b) (a' := a) (b' := b) (fun T => le_rfl) (fun T => le_rfl)).τ T = LinearMap.id := by`. Use extensionality with `⟨x, hx⟩`.

Take `⟨y, rfl⟩` from `Ideal.Quotient.mk_surjective x`. Both sides reduce to the same expression. Rewrite using `[e]`. Conclude with `Function.bijective_id`.
-/
theorem sqLe_bij {a b a' b' : IdF A} (ha : ∀ T, a.S T = a'.S T) (hb : ∀ T, b.S T = b'.S T) (j : ℕ) :
    Function.Bijective ((sqLe (a := a) (b := b) (a' := a') (b' := b') (fun T => (ha T).le) (fun T => (hb T).le)).pull j) := by
  obtain rfl : a = a' := IdF.ext' ha
  obtain rfl : b = b' := IdF.ext' hb
  refine idM_bij (sqLe (a := a) (b := b) (a' := a) (b' := b) (fun T => le_rfl) (fun T => le_rfl)).τ
    (sqLe (a := a) (b := b) (a' := a) (b' := b) (fun T => le_rfl) (fun T => le_rfl)).nat (fun T => ?_) j
  have e : (sqLe (a := a) (b := b) (a' := a) (b' := b) (fun T => le_rfl) (fun T => le_rfl)).τ T = LinearMap.id := by
    ext ⟨x, hx⟩
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective x
    rfl
  rw [e]
  exact Function.bijective_id
end Gen

section Lk
variable {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] {X : Scheme.{0}} {q : X ⟶ Spec (CommRingCat.of O)}

/- English proof (translation)
Use `(CrystallineSemistableComparison.P.prism (σ := RingHom.id O) ((gQ h Q m hQ P hP).o b hb) ((gP h Q m hQ P hP).comp (sqLe (a := IdF.top (sP Q).A) (a' := IdF.top (sP Q).A) (fun _ => le_rfl) hb')) (𝟙 _) (fun T y => ?_) j x).trans ((CrystallineSemistableComparison.P.pull_comp (σ'' := …` and prove the remaining obligations. Take `⟨a, rfl⟩` from `Ideal.Quotient.mk_surjective (show GB (l := l) T.obj m from y)`. Both sides reduce to the same expression.
-/
theorem gQ_o (h : OL l O) (Q : ObjectProperty (Thick (smFun X q))) (m : ℕ) (hQ : ∀ T, Q T → Good (l := l) T m)
    (P : ObjectProperty (Thick (Lm h q m))) (hP : ∀ T, P ((GF h Q m hQ).obj T)) (b : IdF (sP Q).A)
    (hb : ∀ T, (IdF.span (sP Q).A ((l : O) ^ m)).S T ≤ b.S T)
    (hb' : ∀ T, (stdI Q none ((l : O) ^ m)).S T ≤ b.S T) (j : ℕ) (x : CH.H (P.ι ⋙ OMm h q m) j) :
    ((gQ h Q m hQ P hP).o b hb).pull j x =
      (sqLe (a := IdF.top (sP Q).A) (a' := IdF.top (sP Q).A) (fun _ => le_rfl) hb').pull j ((gP h Q m hQ P hP).pull j x) := by
  refine (CrystallineSemistableComparison.P.prism (σ := RingHom.id O) ((gQ h Q m hQ P hP).o b hb)
    ((gP h Q m hQ P hP).comp (sqLe (a := IdF.top (sP Q).A) (a' := IdF.top (sP Q).A) (fun _ => le_rfl) hb')) (𝟙 _)
    (fun T y => ?_) j x).trans ((CrystallineSemistableComparison.P.pull_comp (σ'' := RingHom.id O) _ _ j x).1)
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective (show GB (l := l) T.obj m from y)
  rfl

end Lk
end GlobalTheory.CompanionTheory.DisoHm

namespace GlobalTheory.CompanionTheory.DisoHm
section Cover
variable {R : Type} [CommRing R] {C C' : Type 1} [Category.{0} C] [Category.{0} C']
  {F : C ⥤ ModuleCat.{0} R} {F' : C' ⥤ ModuleCat.{0} R}

def smulM (m : CH.Mor F F' (RingHom.id R)) (n : R) : CH.Mor F F' (RingHom.id R) where
  G := m.G
  τ T := n • m.τ T
  nat φ x := by
    change n • m.τ _ _ = (F'.map φ).hom (n • m.τ _ x)
    rw [m.nat, map_smul]

/- English proof (translation)
Take `⟨a, ha, rfl⟩` from `CrystallineSemistableComparison.CechClassBoundaries.clsSurj x`. Both sides reduce to the same expression.
-/
theorem smulM_pull (m : CH.Mor F F' (RingHom.id R)) (n : R) (j : ℕ) (x : CH.H F j) :
    (smulM m n).pull j x = n • m.pull j x := by
  obtain ⟨a, ha, rfl⟩ := CrystallineSemistableComparison.CechClassBoundaries.clsSurj x
  rfl

/- English proof (translation)
Set `e : (∀ _ : Unit, R ⊗[R] M) ≃+ M` to `(AddEquiv.piUnique (fun _ : Unit => R ⊗[R] M)).trans (TensorProduct.lid R M).toAddEquiv`. Establish `he : ∀ n x, e (Pi.single () (n ⊗ₜ x)) = n • x` using `fun n x => by simp [e]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨g, hg⟩`. Establish `: ∀ x, f x = g (e.symm x)` using `fun x => by`.

Establish `h2 : g (Pi.single () ((1 : R) ⊗ₜ x)) = f x` using `(hg () 1 x).trans (one_smul _ _)`. Establish `h3 : e.symm x = Pi.single () ((1 : R) ⊗ₜ x)`. Use `(AddEquiv.symm_apply_eq e).2 ?_` and prove the remaining obligations. Rewrite using `[he, one_smul]`. Rewrite using `[h3, h2]`.

Establish `e2 : (f : M → M') = (e.symm.trans g)` using `funext this`. Rewrite using `[e2]`. Conclude with `(e.symm.trans g).bijective`. Introduce `hf`. Use `⟨e.trans (AddEquiv.ofBijective f.toAddMonoidHom hf), fun _ n x => ?_⟩` and prove the remaining obligations.

Express the relevant statement in the definitionally equal form `f (e _) = _`. Rewrite using `[he, map_smul]`.
-/
theorem tens_iff {M M' : Type 1} [AddCommGroup M] [Module R M] [AddCommGroup M'] [Module R M'] (f : M →ₗ[R] M') :
    Tens R (N := fun _ : Unit => R) (M := fun _ => M) (M' := M') (fun _ n x => n • f x) ↔ Function.Bijective f := by
  let e : (∀ _ : Unit, R ⊗[R] M) ≃+ M :=
    (AddEquiv.piUnique (fun _ : Unit => R ⊗[R] M)).trans (TensorProduct.lid R M).toAddEquiv
  have he : ∀ n x, e (Pi.single () (n ⊗ₜ x)) = n • x := fun n x => by simp [e]
  constructor
  · rintro ⟨g, hg⟩
    have : ∀ x, f x = g (e.symm x) := fun x => by
      have h2 : g (Pi.single () ((1 : R) ⊗ₜ x)) = f x := (hg () 1 x).trans (one_smul _ _)
      have h3 : e.symm x = Pi.single () ((1 : R) ⊗ₜ x) := by
        refine (AddEquiv.symm_apply_eq e).2 ?_
        rw [he, one_smul]
      rw [h3, h2]
    have e2 : (f : M → M') = (e.symm.trans g) := funext this
    rw [e2]
    exact (e.symm.trans g).bijective
  · intro hf
    refine ⟨e.trans (AddEquiv.ofBijective f.toAddMonoidHom hf), fun _ n x => ?_⟩
    change f (e _) = _
    rw [he, map_smul]

/- English proof (translation)
Establish `key` using `GlobalTheory.CompanionTheory.CosieveBC.base_change_of_cover (σ := RingHom.id R) m.G (ι := Unit) (fun _ => R) (fun _ => F) F' (fun _ n T => (smulM m n).τ T) (fun _ n _ _ φ x => (smulM m n).nat φ x) (fun _ n n' T x => by simp [smulM, add_smul]) (fun _ r n T x => by simp [smulM, mul …`. Take `⟨g, hg⟩` from `key`. Conclude with `(tens_iff (m.pull j)).1 ⟨g, fun i n x => (hg i n x).trans (smulM_pull m n j x)⟩`. Take `⟨g, hg⟩` from `(tens_iff ((morU m (U := capS U S) (U' := capS U' S) fun T hT α hα => h α T (hT α hα)).pull j)).2 (H S hS j)`. Use `⟨g, fun i n x => (hg i n x).trans ?_⟩` and prove the remaining obligations.

Take `⟨a, ha, rfl⟩` from `CrystallineSemistableComparison.CechClassBoundaries.clsSurj x`. Both sides reduce to the same expression.
-/
theorem cover_bij (m : CH.Mor F F' (RingHom.id R)) {A : Type} [Fintype A] (U : A → ObjectProperty C)
    (U' : A → ObjectProperty C') (hU : ∀ α, Cosieve (U α)) (hU' : ∀ α, Cosieve (U' α)) (hc : ∀ T, ∃ α, U α T)
    (hc' : ∀ T, ∃ α, U' α T) (h : ∀ α T, U' α T → U α (m.G.obj T))
    (H : ∀ S : Finset A, S.Nonempty → ∀ j, Function.Bijective
      ((morU m (U := capS U S) (U' := capS U' S) fun T hT α hα => h α T (hT α hα)).pull j)) (j : ℕ) :
    Function.Bijective (m.pull j) := by
  have key := GlobalTheory.CompanionTheory.CosieveBC.base_change_of_cover (σ := RingHom.id R) m.G (ι := Unit) (fun _ => R) (fun _ => F) F'
    (fun _ n T => (smulM m n).τ T) (fun _ n _ _ φ x => (smulM m n).nat φ x)
    (fun _ n n' T x => by simp [smulM, add_smul]) (fun _ r n T x => by simp [smulM, mul_smul])
    U U' hU hU' hc hc' h (fun S hS j => ?_) j
  · obtain ⟨g, hg⟩ := key
    exact (tens_iff (m.pull j)).1 ⟨g, fun i n x => (hg i n x).trans (smulM_pull m n j x)⟩
  · obtain ⟨g, hg⟩ := (tens_iff ((morU m (U := capS U S) (U' := capS U' S) fun T hT α hα => h α T (hT α hα)).pull j)).2 (H S hS j)
    refine ⟨g, fun i n x => (hg i n x).trans ?_⟩
    obtain ⟨a, ha, rfl⟩ := CrystallineSemistableComparison.CechClassBoundaries.clsSurj x
    rfl
end Cover
end GlobalTheory.CompanionTheory.DisoHm

namespace GlobalTheory.CompanionTheory.DisoHm
section Ch
variable {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] {X : Scheme.{0}} {q : X ⟶ Spec (CommRingCat.of O)}

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem pt_G (h : OL l O) (T : Thick (smFun X q)) (m : ℕ) (hT : Good (l := l) T m) :
    pt (GObj h T m hT) = Spec.map (CommRingCat.ofHom (thG (l := l) T m)) ≫ pt T := rfl

/- English proof (translation)
Unfold `InU`. Rewrite using `[pt_G]`. Introduce `x _`. Conclude with `hV (show (Spec.map (CommRingCat.ofHom (thG (l := l) T m))) x ∈ ⊤ from trivial)`.
-/
theorem inU_G (h : OL l O) (T : Thick (smFun X q)) (m : ℕ) (hT : Good (l := l) T m) {V : X.Opens} (hV : InU V T) :
    InU V (GObj h T m hT) := by
  unfold InU
  rw [pt_G]
  intro x _
  exact hV (show (Spec.map (CommRingCat.ofHom (thG (l := l) T m))) x ∈ ⊤ from trivial)

/- English proof (translation)
The claim follows from `GlobalTheory.LogCris.evalAt_map _ (pt T) hV hV' f`.
-/
theorem ev_G (h : OL l O) (T : Thick (smFun X q)) (m : ℕ) (hT : Good (l := l) T m) {V : X.Opens} (hV : InU V T)
    (hV' : InU V (GObj h T m hT)) (f : Γ(X, V)) :
    ev (GObj h T m hT) hV' f = thG (l := l) T m (ev T hV f) :=
  GlobalTheory.LogCris.evalAt_map _ (pt T) hV hV' f

/- English proof (translation)
Establish `key : ∀ (y : Spec (CommRingCat.of (T'.B ⧸ T'.J)) ⟶ X) (hy : y = Spec.map (CommRingCat.ofHom (Ideal.quotientMap T'.J φ.φ φ.hle)) ≫ pt T) (hh : ⊤ ≤ y ⁻¹ᵁ V), GlobalTheory.Cris.evalAt y V hh f = Ideal.quotientMap T'.J φ.φ φ.hle (ev T h f)`. Introduce `y hy hh`. Substitute `hy` using the available equality. Conclude with `GlobalTheory.LogCris.evalAt_map (B := CommRingCat.of (T.B ⧸ T.J)) (B' := CommRingCat.of (T'.B ⧸ T'.J)) _ (pt T) h hh f`. Conclude with `key _ (Site.pt_hom φ) h'`.
-/
theorem ev_hom {R : Type} [CommRing R] {I : Ideal R} {γ : DividedPowers I} {p : ℕ} {κ : O →+* R ⧸ I} {V : X.Opens}
    {T T' : Thick (nlFun γ p X q κ)} (φ : T ⟶ T') (h : InU V T) (h' : InU V T') (f : Γ(X, V)) :
    ev T' h' f = Ideal.quotientMap T'.J φ.φ φ.hle (ev T h f) := by
  have key : ∀ (y : Spec (CommRingCat.of (T'.B ⧸ T'.J)) ⟶ X)
      (hy : y = Spec.map (CommRingCat.ofHom (Ideal.quotientMap T'.J φ.φ φ.hle)) ≫ pt T)
      (hh : ⊤ ≤ y ⁻¹ᵁ V), GlobalTheory.Cris.evalAt y V hh f = Ideal.quotientMap T'.J φ.φ φ.hle (ev T h f) := by
    intro y hy hh
    subst hy
    exact GlobalTheory.LogCris.evalAt_map (B := CommRingCat.of (T.B ⧸ T.J)) (B' := CommRingCat.of (T'.B ⧸ T'.J)) _ (pt T) h hh f
  exact key _ (Site.pt_hom φ) h'

/- English proof (translation)
Establish `hV` using `inU_G h cO.D m hT cO.inV`. Take `⟨σ₀⟩` from `hg.1 _ hV`. Establish `hy : ∀ i, ((show (GObj h cO.D m hT).B from Ideal.Quotient.mk (lm (l` using `l) cO.D m) (cO.t i)) - σ₀.φ (cL.t i)) ∈ (GObj h cO.D m hT).J := by`. Introduce `i`. Use `Ideal.Quotient.eq.1 ?_` and prove the remaining obligations.

Establish `a1` using `ev_G h cO.D m hT cO.inV hV (c.t i)`. Establish `a2` using `ev_hom σ₀ cL.inV hV (c.t i)`. Rewrite `a1` using `[ht i]`. Rewrite `a2` using `[hcL i]`. Conclude with `a1.symm.trans a2`.

Take `⟨σ, h1, -⟩` from `hg.2 _ σ₀ _ hy`. Conclude with `⟨σ, fun i => by simpa using h1 i⟩`.
-/
theorem exists_sig (h : OL l O) {W : X.Opens} {d : ℕ} (c : Coord q W d) (m : ℕ)
    (cL : Chart (pdm h m) l q (κm l O m) W d)
    (hg : cL.Good)
    (hcL : ∀ i, ev cL.D cL.inV (c.t i) = Ideal.Quotient.mk _ (cL.t i))
    (cO : Chart (dividedPowersBot O) 0 q (Ideal.Quotient.mk ⊥) W d)
    (ht : ∀ i, ev cO.D cO.inV (c.t i) = Ideal.Quotient.mk _ (cO.t i))
    (hT : Good (l := l) cO.D m) :
    ∃ σ : cL.D ⟶ GObj h cO.D m hT, ∀ i, σ.φ (cL.t i) = Ideal.Quotient.mk _ (cO.t i) := by
  have hV := inU_G h cO.D m hT cO.inV
  obtain ⟨σ₀⟩ := hg.1 _ hV
  have hy : ∀ i, ((show (GObj h cO.D m hT).B from Ideal.Quotient.mk (lm (l := l) cO.D m) (cO.t i)) - σ₀.φ (cL.t i)) ∈
      (GObj h cO.D m hT).J := by
    intro i
    refine Ideal.Quotient.eq.1 ?_
    have a1 := ev_G h cO.D m hT cO.inV hV (c.t i)
    have a2 := ev_hom σ₀ cL.inV hV (c.t i)
    rw [ht i] at a1
    rw [hcL i] at a2
    exact a1.symm.trans a2
  obtain ⟨σ, h1, -⟩ := hg.2 _ σ₀ _ hy
  exact ⟨σ, fun i => by simpa using h1 i⟩

end Ch
end GlobalTheory.CompanionTheory.DisoHm

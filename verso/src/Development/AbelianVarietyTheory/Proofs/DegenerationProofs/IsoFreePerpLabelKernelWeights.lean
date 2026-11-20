import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.UTorsSt
import Development.AbelianVarietyTheory.PublishedTheorems.SemistableReduction₂.SemistableReductionSt
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ThetaSysFFMemFinitePerpProj
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.TxFrameOfOne
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.GtOntoDivisibleKernel
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsUniqueWeilIs
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.WeilIsAlternatingSkewNatural
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.WeilIsIffOfIsGrpPullbackComm
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
open Classical
open ReciprocityTheory.ChartRestriction.G.Out
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.ZH.TorusPerp

section Pairing
open ReciprocityTheory.ChartRestriction.G.DVR GlobalTheory.UT GlobalTheory.UT.TorusWeight GlobalTheory.TorusExt

variable {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {F : Type} [Field F] [Algebra (FractionRing R) F]

/- English proof (translation)
Introduce `w w' hw hw' s s₁ s₂ s₃ s₄ h₁ h₂ h₃ h₄`. Rewrite `h₁`, `h₄` using `[phiRel_iff hG _ _ hw']`. Rewrite `h₂`, `h₃` using `[phiRel_iff hG _ _ hw]`. Establish `tr : DegPre.trPt D F p.g.b = 𝟙 _`. Apply `CartesianMonoidalCategory.hom_ext` to reduce the goal to its premises.

Rewrite using `[Category.id_comp]`. Conclude with `tr_fst D F _`. Rewrite using `[Category.id_comp]`. Use `(tr_pr D F _).trans ?_` and prove the remaining obligations. Rewrite using `[hτ.1, MonObj.comp_one, _root_.mul_one]`.

Establish `v : ∀ (α : D.X) (T : Over (Spec (CommRingCat.of R))) (ρ : T ⟶ DegPre.BF D F) (z : T.left) (J), Good D.P.L z J → (uVal D F k α p.g.b ρ z J * val (LB.mulGen D.P.L _ _ _ _ (p.g.s α) w) (ρ ≫ fst _ _).left z J).val = gs (ρ ≫ fst _ _).left z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of F)).inv. …`. Introduce `α T ρ z J hJ`. Establish `C : IsCub (th D z J)` using `isCub_cubV D.cub hJ`. Establish `hu : uVal D F k α p.g.b ρ z J = 1`. Rewrite using `[uVal, hτ.1]`.

Simplify using `only [MonObj.comp_one]`. Unfold `cubN`. Simplify using `only [C.face₃, C.face₂, Finset.prod_const_one, inv_one, _root_.mul_one]`. Establish `e` using `val_const (p.g.s α) _ (hτ.2 α) (ρ ≫ fst _ _).left z hJ`. Rewrite using `[hu, _root_.one_mul, val_mul hJ, Units.val_mul, e]`.

Introduce `β`. Take `⟨α, rfl⟩ : ∃ α, α + p'.y = β` from `⟨β - p'.y, sub_add_cancel _ _⟩`. Use `(sval_const _ _ _ _).2 fun T ρ z J hJ => ?_` and prove the remaining obligations. Establish `e₁` using `h₁ α _ rfl T ρ z J hJ`. Establish `e₂` using `h₂ (α + p'.y) (α + p'.y) (by rw [hy, add_zero]) T ρ z J hJ`.

Establish `e₃` using `h₃ α α (by rw [hy, add_zero]) T (ρ ≫ DegPre.trPt D F p'.g.b) z J hJ`. Establish `e₄` using `h₄ α _ rfl T ρ z J hJ`. Rewrite `e₂`, `e₃` using `[v _ T _ z J hJ, tr, Category.comp_id]`. Rewrite `e₃` using `[Category.assoc, tr_fst]`. Rewrite using `[e₂, e₄, e₃, e₁, ofAdd_add, map_mul, Units.val_mul (τ _), map_mul, gs_mul _ _ ⊤ trivial]`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem weilQkIs_tor (hG : GlobalFnsSt) {k : ℕ} (p p' : QkPt D F k) {τ : Multiplicative D.X →* Fˣ} (hy : p.y = 0)
    (hτ : IsTor τ p.g) : WeilQkIs D F k p p' (τ (Multiplicative.ofAdd p'.y)).val := by
  intro w w' hw hw' s s₁ s₂ s₃ s₄ h₁ h₂ h₃ h₄
  rw [phiRel_iff hG _ _ hw'] at h₁ h₄
  rw [phiRel_iff hG _ _ hw] at h₂ h₃
  have tr : DegPre.trPt D F p.g.b = 𝟙 _ := by
    apply CartesianMonoidalCategory.hom_ext
    · rw [Category.id_comp]; exact tr_fst D F _
    · rw [Category.id_comp]
      refine (tr_pr D F _).trans ?_
      rw [hτ.1, MonObj.comp_one, _root_.mul_one]
  have v : ∀ (α : D.X) (T : Over (Spec (CommRingCat.of R))) (ρ : T ⟶ DegPre.BF D F) (z : T.left) (J), Good D.P.L z J →
      (uVal D F k α p.g.b ρ z J * val (LB.mulGen D.P.L _ _ _ _ (p.g.s α) w) (ρ ≫ fst _ _).left z J).val =
        gs (ρ ≫ fst _ _).left z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom (τ (Multiplicative.ofAdd α)).val) *
          (val w (ρ ≫ fst _ _).left z J).val := by
    intro α T ρ z J hJ
    have C : IsCub (th D z J) := isCub_cubV D.cub hJ
    have hu : uVal D F k α p.g.b ρ z J = 1 := by
      rw [uVal, hτ.1]
      simp only [MonObj.comp_one]
      unfold cubN
      simp only [C.face₃, C.face₂, Finset.prod_const_one, inv_one, _root_.mul_one]
    have e := val_const (p.g.s α) _ (hτ.2 α) (ρ ≫ fst _ _).left z hJ
    rw [hu, _root_.one_mul, val_mul hJ, Units.val_mul, e]
  intro β
  obtain ⟨α, rfl⟩ : ∃ α, α + p'.y = β := ⟨β - p'.y, sub_add_cancel _ _⟩
  refine (sval_const _ _ _ _).2 fun T ρ z J hJ => ?_
  have e₁ := h₁ α _ rfl T ρ z J hJ
  have e₂ := h₂ (α + p'.y) (α + p'.y) (by rw [hy, add_zero]) T ρ z J hJ
  have e₃ := h₃ α α (by rw [hy, add_zero]) T (ρ ≫ DegPre.trPt D F p'.g.b) z J hJ
  have e₄ := h₄ α _ rfl T ρ z J hJ
  rw [v _ T _ z J hJ, tr, Category.comp_id] at e₂ e₃
  rw [Category.assoc, tr_fst] at e₃
  rw [e₂, e₄, e₃, e₁, ofAdd_add, map_mul, Units.val_mul (τ _), map_mul, gs_mul _ _ ⊤ trivial]
  ring

attribute [local instance] gtGroup in

/- English proof (translation)
Assemble the required witnesses or components as `⟨qkMk hB 0 (torusPt D F (Additive.ofMul τ)) (by rw [← map_nsmul, ← ofMul_pow, h, ofMul_one, map_zero, map_zero]), rfl, (isTor_iff _ _).2 (isTorusPtF_torusPt τ)⟩`.
-/
theorem exists_qkPt_tor (hB : D.TauBimult) {k : ℕ} (τ : Multiplicative D.X →* Fˣ) (h : τ ^ k = 1) :
    ∃ p : QkPt D F k, p.y = 0 ∧ IsTor τ p.g :=
  ⟨qkMk hB 0 (torusPt D F (Additive.ofMul τ)) (by rw [← map_nsmul, ← ofMul_pow, h, ofMul_one, map_zero, map_zero]),
    rfl, (isTor_iff _ _).2 (isTorusPtF_torusPt τ)⟩

end Pairing

section Algebra

/- English proof (translation)
Simplify using `only [eStd, Pi.add_apply]`. Rewrite using `[← Finset.sum_add_distrib]`. Conclude with `Finset.sum_congr rfl fun i _ => by ring`.
-/
theorem eStd_add_left (g n : ℕ) (a a' b : Fin g ⊕ Fin g → ZMod n) :
    eStd g n (a + a') b = eStd g n a b + eStd g n a' b := by
  simp only [eStd, Pi.add_apply]
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun i _ => by ring

/- English proof (translation)
Simplify using `only [eStd, Pi.add_apply]`. Rewrite using `[← Finset.sum_add_distrib]`. Conclude with `Finset.sum_congr rfl fun i _ => by ring`.
-/
theorem eStd_add_right (g n : ℕ) (a b b' : Fin g ⊕ Fin g → ZMod n) :
    eStd g n a (b + b') = eStd g n a b + eStd g n a b' := by
  simp only [eStd, Pi.add_apply]
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun i _ => by ring

/- English proof (translation)
Use function extensionality and compare the values at `j`. Break down `j with i | i` into its components or cases. Simplify `h (Pi.single (.inr i) 1)` using `[eStd, Pi.single_apply]`. Simplify `h (Pi.single (.inl i) 1)` using `[eStd, Pi.single_apply]`.
-/
theorem eq_zero_of_eStd (g n : ℕ) (a : Fin g ⊕ Fin g → ZMod n) (h : ∀ b, eStd g n a b = 0) : a = 0 := by
  funext j
  rcases j with i | i
  · simpa [eStd, Pi.single_apply] using h (Pi.single (.inr i) 1)
  · simpa [eStd, Pi.single_apply] using h (Pi.single (.inl i) 1)

variable {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] (S : ThetaSys o Ω)

/- English proof (translation)
Use `choose σ hσ using fun α : X => hs (QuotientAddGroup.mk α)`. Establish `ind : ∀ (t : S.perp yy.ker) (b b' : S.Gam), yy b = yy b' → eStd S.g _ t b = eStd S.g _ t b'`. Introduce `t b b' e`. Establish `h0 : eStd S.g _ t (b - b') = 0` using `t.2 _ (by rw [AddMonoidHom.mem_ker, map_sub, e, sub_self])`. Rewrite using `[← sub_add_cancel b b', eStd_add_right, h0, zero_add]`.

Set `Λ : S.perp yy.ker →+ X →+ ZMod (S.r * S.N)` to `AddMonoidHom.mk' (fun t => AddMonoidHom.mk' (fun α => eStd S.g _ t (σ α)) fun α β => by`. Rewrite using `[← eStd_add_right]`. Conclude with `ind t _ _ (by rw [map_add, hσ, hσ, hσ, QuotientAddGroup.mk_add]))`. Use `fun t t' => AddMonoidHom.ext fun α => eStd_add_left _ _ _ _ _`. Establish `hΛ : ∀ (t : S.perp yy.ker) b α, yy b = QuotientAddGroup.mk α → Λ t α = eStd S.g _ t b` using `fun t b α e => ind t _ _ ((hσ α).trans e.symm)`.

Establish `hbij : Function.Bijective Λ`. Use `⟨(injective_iff_map_eq_zero _).2 fun t ht => Subtype.ext (eq_zero_of_eStd _ _ _ fun b => ?_), fun l => ?_⟩` and prove the remaining obligations. Take `⟨α, e⟩` from `QuotientAddGroup.mk_surjective (yy b)`. Rewrite using `[← hΛ t b α e.symm, ht, AddMonoidHom.zero_apply]`. Take `⟨a, -, ha⟩` from `H l`.

Conclude with `⟨⟨a, fun h hh => (ha h 0 hh).trans (map_zero l)⟩, AddMonoidHom.ext fun α => ha _ _ (hσ α)⟩`. Use `⟨⟨fun s hs t ht => ?_, Module.finrank ℤ X, ⟨(AddEquiv.ofBijective Λ hbij).trans ((addMonoidHomLequivInt ℤ).toAddEquiv.trans ((Module.finBasis ℤ X).constr ℤ).symm.toAddEquiv)⟩⟩, Λ.flip.compr₂ (ZMod.castHom (dvd_mul_left S.N S.r) (ZMod S.N)).toAddMonoidHom, fun x α e t => ?_⟩` and prove the remaining obligations. Take `⟨a, ha, hl⟩` from `H (Λ ⟨s, hs⟩)`. Take `⟨α, e⟩` from `QuotientAddGroup.mk_surjective (yy t)`. Rewrite using `[← hΛ ⟨s, hs⟩ t α e.symm, ← hl t α e.symm, GlobalTheory.ThetaProj.eStd_swap, ht a ha, neg_zero]`.

Rewrite using `[← hΛ t x α e]`. Both sides reduce to the same expression.
-/
theorem isoFree_perp_ker {X : Type} [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X]
    (yy : S.Gam →+ X ⧸ (nsmulAddMonoidHom (S.r * S.N) : X →+ X).range) (hs : Function.Surjective yy)
    (H : ∀ l : X →+ ZMod (S.r * S.N), ∃ a ∈ yy.ker, ∀ b α, yy b = QuotientAddGroup.mk α → eStd S.g _ a b = l α) :
    S.IsoFree (S.perp yy.ker) ∧ ∃ wt : X →+ (S.perp yy.ker →+ ZMod S.N), ∀ (x : S.Gam) (α : X),
      yy x = QuotientAddGroup.mk α → ∀ t : S.perp yy.ker,
        wt α t = ZMod.castHom (dvd_mul_left S.N S.r) (ZMod S.N) (eStd S.g _ t x) := by
  choose σ hσ using fun α : X => hs (QuotientAddGroup.mk α)
  have ind : ∀ (t : S.perp yy.ker) (b b' : S.Gam), yy b = yy b' → eStd S.g _ t b = eStd S.g _ t b' := by
    intro t b b' e
    have h0 : eStd S.g _ t (b - b') = 0 := t.2 _ (by rw [AddMonoidHom.mem_ker, map_sub, e, sub_self])
    rw [← sub_add_cancel b b', eStd_add_right, h0, zero_add]
  let Λ : S.perp yy.ker →+ X →+ ZMod (S.r * S.N) := AddMonoidHom.mk'
    (fun t => AddMonoidHom.mk' (fun α => eStd S.g _ t (σ α)) fun α β => by
      rw [← eStd_add_right]
      exact ind t _ _ (by rw [map_add, hσ, hσ, hσ, QuotientAddGroup.mk_add]))
    fun t t' => AddMonoidHom.ext fun α => eStd_add_left _ _ _ _ _
  have hΛ : ∀ (t : S.perp yy.ker) b α, yy b = QuotientAddGroup.mk α → Λ t α = eStd S.g _ t b :=
    fun t b α e => ind t _ _ ((hσ α).trans e.symm)
  have hbij : Function.Bijective Λ := by
    refine ⟨(injective_iff_map_eq_zero _).2 fun t ht => Subtype.ext (eq_zero_of_eStd _ _ _ fun b => ?_), fun l => ?_⟩
    · obtain ⟨α, e⟩ := QuotientAddGroup.mk_surjective (yy b)
      rw [← hΛ t b α e.symm, ht, AddMonoidHom.zero_apply]
    · obtain ⟨a, -, ha⟩ := H l
      exact ⟨⟨a, fun h hh => (ha h 0 hh).trans (map_zero l)⟩, AddMonoidHom.ext fun α => ha _ _ (hσ α)⟩
  refine ⟨⟨fun s hs t ht => ?_, Module.finrank ℤ X, ⟨(AddEquiv.ofBijective Λ hbij).trans
    ((addMonoidHomLequivInt ℤ).toAddEquiv.trans ((Module.finBasis ℤ X).constr ℤ).symm.toAddEquiv)⟩⟩,
    Λ.flip.compr₂ (ZMod.castHom (dvd_mul_left S.N S.r) (ZMod S.N)).toAddMonoidHom, fun x α e t => ?_⟩
  · obtain ⟨a, ha, hl⟩ := H (Λ ⟨s, hs⟩)
    obtain ⟨α, e⟩ := QuotientAddGroup.mk_surjective (yy t)
    rw [← hΛ ⟨s, hs⟩ t α e.symm, ← hl t α e.symm, GlobalTheory.ThetaProj.eStd_swap, ht a ha, neg_zero]
  · rw [← hΛ t x α e]; rfl

end Algebra

section Points

def ptHom {S S' : Scheme.{0}} {G : Over S} {G' : Over S'} [GrpObj G] [GrpObj G'] {f : S' ⟶ S} {φ : G'.left ⟶ G.left}
    (h : IsGrpPullback G' G f φ) (T : Over S') : (T ⟶ G') →* (Over.mk (T.hom ≫ f) ⟶ G) :=
  MonoidHom.mk' (fun x => toBase h.1.w x) fun x y => Over.OverMorphism.ext (h.2 T x y _ _ rfl rfl).symm

/- English proof (translation)
Assemble the required witnesses or components as `⟨fun x y e => Over.OverMorphism.ext (h.1.hom_ext (congrArg (fun q => q.left) e) ((Over.w x).trans (Over.w y).symm)), fun z => ⟨Over.homMk (h.1.lift z.left T.hom (Over.w z)) (h.1.lift_snd _ _ _), Over.OverMorphism.ext (h.1.lift_fst _ _ _)⟩⟩`.
-/
theorem ptHom_bijective {S S' : Scheme.{0}} {G : Over S} {G' : Over S'} [GrpObj G] [GrpObj G'] {f : S' ⟶ S}
    {φ : G'.left ⟶ G.left} (h : IsGrpPullback G' G f φ) (T : Over S') : Function.Bijective (ptHom h T) :=
  ⟨fun x y e => Over.OverMorphism.ext (h.1.hom_ext (congrArg (fun q => q.left) e) ((Over.w x).trans (Over.w y).symm)),
    fun z => ⟨Over.homMk (h.1.lift z.left T.hom (Over.w z)) (h.1.lift_snd _ _ _),
      Over.OverMorphism.ext (h.1.lift_fst _ _ _)⟩⟩

/- English proof (translation)
The claim follows from `Units.ext (congrArg (fun q => q.hom c.val) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom β))).symm`.
-/
theorem map_unitOn {A B : Type} [CommRing A] [CommRing B] (β : A →+* B) (c : Aˣ) :
    Units.map (spMap β).appTop.hom.toMonoidHom (unitOn c) = unitOn (Units.map β.toMonoidHom c) :=
  Units.ext (congrArg (fun q => q.hom c.val) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom β))).symm

/- English proof (translation)
Introduce `_ _ h` and use `Units.ext ((ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of K)).inv).1 (congrArg Units.val h))`.
-/
theorem unitOn_injective {K : Type} [CommRing K] : Function.Injective (unitOn (R := K)) := fun _ _ h =>
  Units.ext ((ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of K)).inv).1 (congrArg Units.val h))

end Points

/- English proof (translation)
Introduce `hL _ hT o Ω _ _ _ hA S ρ p _ y₀ u yy hs hyy`. Establish `hG` using `hL.globalFns`. Establish `hN` using `S.N_ge`. Establish `hr` using `S.r_pos`. Establish `hn : NeZero (S.r * S.N)` using `⟨Nat.mul_ne_zero (by omega) (by omega)⟩`.

Establish `: IsDomain o` using `hA.inj.isDomain _`. Establish `: CharZero u.V` using `RingHom.charZero ((algebraMap (FractionRing u.V) (PadicAlgCl p)).comp (algebraMap u.V (FractionRing u.V)))`. Use `ρ.P.isAb.comm` as an intermediate fact. Take `⟨f, f₁, f₂, -, -, f₅⟩` from `hT u.V u.complete u.A u.G u.D u.U (PadicAlgCl p) (S.r * S.N) hn.pos`. Establish `hζ : IsPrimitiveRoot (S.ζ ^ (S.r * S.N)) (S.r * S.N)` using `S.prim.pow (pow_pos hn.pos 2) (pow_two _)`.

Set `c₀ : (S.R)ˣ` to `Units.map (algebraMap o S.R).toMonoidHom (hζ.isUnit hn.ne).unit`. Set `ω : (PadicAlgCl p)ˣ` to `Units.map y₀.toMonoidHom c₀`. Establish `hω : IsPrimitiveRoot ω (S.r * S.N)`. Establish `: NeZero ((S.r * S.N : ℕ) : PadicAlgCl p)` using `⟨Nat.cast_ne_zero.2 hn.ne⟩`. Rewrite using `[← IsPrimitiveRoot.coe_units_iff, ← Polynomial.isRoot_cyclotomic_iff, ← Polynomial.map_cyclotomic _ (y₀.comp (algebraMap o S.R))]`.

Conclude with `(hζ.isRoot_cyclotomic hn.pos).map`. Establish `hy : (TFK (R` using `u.V) (PadicAlgCl p)).hom ≫ spMap u.yK = spMap y₀ := (Spec.map_comp _ _).symm.trans (congrArg spMap u.fac)`. Set `h : Over.mk ((TFK (R` to `u.V) (PadicAlgCl p)).hom ≫ spMap u.yK) ⟶ baseOver (Sp S.R) := Over.homMk ((TFK (R := u.V) (PadicAlgCl p)).hom ≫ spMap u.yK) (by simp)`. Establish `hh : h.left = spMap y₀` using `hy`. Set `Φ` to `ptHom u.cart (TFK (R := u.V) (PadicAlgCl p))`.

Establish `hΦ : Function.Bijective Φ` using `ptHom_bijective _ _`. Establish `lab : ∀ a q, Φ (f q) = h ≫ ρ.pt a → yy a = QuotientAddGroup.mk q.y` using `fun a q e => hyy a q _ ((f₁ _ _).2 rfl) ((congrArg (fun z => z.left) e).trans (by rw [← hh]; rfl))`. Set `pt : Multiplicative S.Gam →* (baseOver (Sp S.R) ⟶ ρ.P.A)` to `MonoidHom.mk' (fun a => ρ.pt a.toAdd) fun _ _ => ρ.pt_add _ _`. Establish `onto : ∀ b, ∃ q, Φ (f q) = h ≫ ρ.pt b` using `fun b => by`. Take `⟨x, hx⟩` from `hΦ.2 (h ≫ ρ.pt b)`.

Take `⟨q, rfl⟩` from `f₂ x (hΦ.1 (by`. Establish `e : ρ.pt b ^ (S.r * S.N) = 1`. Use `(map_pow pt (Multiplicative.ofAdd b) _).symm.trans ?_` and prove the remaining obligations. Rewrite using `[← ofAdd_nsmul, ← Nat.cast_smul_eq_nsmul (ZMod (S.r * S.N)), ZMod.natCast_self, zero_smul, ofAdd_zero, map_one]`. Rewrite using `[map_pow, hx, map_one, ← MonObj.comp_pow, e, MonObj.comp_one]))`.

Conclude with `⟨q, hx⟩`. Establish `weil : ∀ a b q q', Φ (f q) = h ≫ ρ.pt a → Φ (f q') = h ≫ ρ.pt b → WeilIs u.A.A u.A.L (S.r * S.N : ℕ) (f q) (f q') (unitOn (ω ^ (eStd S.g _ a b).val))` using `fun a b q q' e e' => by`. Establish `w` using `GlobalTheory.CommPairing.weilIs_pull hG ρ.P.isAb ρ.P.isLB h (ρ.weil a b (c₀ ^ (eStd S.g _ a b).val) (by`. Rewrite using `[pow_mul, map_pow]`. Use the proof step `rfl))`.

Rewrite `w` using `[← e, ← e']`. Use `(GlobalTheory.weilIs_iff_of_isGrpPullback_comm _ _ _ _ _ _ _ _ ρ.P.isLB u.A.isLB u.cart u.lb _ _ _ _ (Φ (f q)) (Φ (f q')) _ rfl rfl).2 ?_` and prove the remaining obligations. Use `w using 1` and compare the differences between its conclusion and the goal. Rewrite using `[← map_pow, ← map_unitOn, ← hh]`. Use `isoFree_perp_ker S yy hs fun l => ?_` and prove the remaining obligations.

Set `χ` to `AddChar.zmodChar (S.r * S.N) hω.pow_eq_one`. Set `τ : Multiplicative u.D.toPre.X →* (PadicAlgCl p)ˣ` to `χ.toMonoidHom.comp l.toMultiplicative`. Establish `hτ : ∀ α, τ (Multiplicative.ofAdd α) = ω ^ (l α).val` using `fun _ => rfl`. Take `⟨q, hq, hqτ⟩` from `exists_qkPt_tor (F := PadicAlgCl p) (k := S.r * S.N) u.D.tau_bimult τ (MonoidHom.ext fun α => by show (ω ^ (l α.toAdd).val) ^ (S.r * S.N) = 1`. Rewrite using `[pow_right_comm, hω.pow_eq_one, one_pow])`.

Establish `hq1 : f q ^ (S.r * S.N) = 1`. Take `⟨w, hw⟩` from `u.U.ext`. Conclude with `((f₁ _ _).2 rfl w hw).1`. Take `⟨a, ha, -⟩` from `ρ.pt_bij (PadicAlgCl p) _ (Φ (f q)) (by rw [← map_pow, hq1, map_one])`. Use `⟨a, (lab a q ha.symm).trans (by rw [hq]; rfl), fun b α e => ?_⟩` and prove the remaining obligations.

Take `⟨q', hq'⟩` from `onto b`. Establish `e₁` using `unitOn_injective (GlobalTheory.CommutatorPairing.weilIs_unique hG u.A.isAb u.A.isLB (weil a b q q' ha.symm hq') ((f₅ q q' _).1 (weilQkIs_tor hG q q' hq hqτ)))`. Rewrite `e₁` using `[hτ]`. Rewrite using `[ZMod.val_injective _ (hω.pow_inj (ZMod.val_lt _) (ZMod.val_lt _) e₁)]`. Take `⟨z, hz⟩` from `QuotientAddGroup.eq.1 ((lab b q' hq').symm.trans e)`.

Establish `hz' : (S.r * S.N) • z = -q'.y + α` using `hz`. Use `congrArg l hz'` as an intermediate fact. Rewrite `this` using `[map_nsmul, nsmul_eq_mul, ZMod.natCast_self, zero_mul, map_add, map_neg]`. Conclude with `neg_add_eq_zero.1 this.symm`.
-/
theorem isoFree_perp_and_weights : Laws → Laws2 → UTorsSt → ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (p : ℕ) [Fact p.Prime] (y₀ : S.R →+* PadicAlgCl p) (u : ρ.UTest p y₀) (yy : S.Gam →+ u.D.toPre.X ⧸ (nsmulAddMonoidHom (S.r * S.N) : u.D.toPre.X →+ u.D.toPre.X).range), Function.Surjective yy → (∀ (a : S.Gam) (pk : QkPt u.D.toPre (PadicAlgCl p) (S.r * S.N)) (x : TFK (R := u.V) (PadicAlgCl p) ⟶ u.A.A), QkToAkU u.U.toUnifPre (PadicAlgCl p) (S.r * S.N) pk x → x.left ≫ u.φ = spMap y₀ ≫ (ρ.pt a).left → yy a = QuotientAddGroup.mk pk.y) → S.IsoFree (S.perp yy.ker) ∧ ∃ wt : u.D.toPre.X →+ (S.perp yy.ker →+ ZMod S.N), ∀ (x : S.Gam) (α : u.D.toPre.X), yy x = QuotientAddGroup.mk α → ∀ t : S.perp yy.ker, wt α t = ZMod.castHom (dvd_mul_left S.N S.r) (ZMod S.N) (eStd S.g _ t x) := by
  intro hL _ hT o Ω _ _ _ hA S ρ p _ y₀ u yy hs hyy
  have hG := hL.globalFns
  have hN := S.N_ge
  have hr := S.r_pos
  have hn : NeZero (S.r * S.N) := ⟨Nat.mul_ne_zero (by omega) (by omega)⟩
  have : IsDomain o := hA.inj.isDomain _
  have : CharZero u.V := RingHom.charZero
    ((algebraMap (FractionRing u.V) (PadicAlgCl p)).comp (algebraMap u.V (FractionRing u.V)))
  have := ρ.P.isAb.comm
  obtain ⟨f, f₁, f₂, -, -, f₅⟩ := hT u.V u.complete u.A u.G u.D u.U (PadicAlgCl p) (S.r * S.N) hn.pos

  have hζ : IsPrimitiveRoot (S.ζ ^ (S.r * S.N)) (S.r * S.N) := S.prim.pow (pow_pos hn.pos 2) (pow_two _)
  let c₀ : (S.R)ˣ := Units.map (algebraMap o S.R).toMonoidHom (hζ.isUnit hn.ne).unit
  let ω : (PadicAlgCl p)ˣ := Units.map y₀.toMonoidHom c₀
  have hω : IsPrimitiveRoot ω (S.r * S.N) := by
    have : NeZero ((S.r * S.N : ℕ) : PadicAlgCl p) := ⟨Nat.cast_ne_zero.2 hn.ne⟩
    rw [← IsPrimitiveRoot.coe_units_iff, ← Polynomial.isRoot_cyclotomic_iff,
      ← Polynomial.map_cyclotomic _ (y₀.comp (algebraMap o S.R))]
    exact (hζ.isRoot_cyclotomic hn.pos).map

  have hy : (TFK (R := u.V) (PadicAlgCl p)).hom ≫ spMap u.yK = spMap y₀ :=
    (Spec.map_comp _ _).symm.trans (congrArg spMap u.fac)
  let h : Over.mk ((TFK (R := u.V) (PadicAlgCl p)).hom ≫ spMap u.yK) ⟶ baseOver (Sp S.R) :=
    Over.homMk ((TFK (R := u.V) (PadicAlgCl p)).hom ≫ spMap u.yK) (by simp)
  have hh : h.left = spMap y₀ := hy
  let Φ := ptHom u.cart (TFK (R := u.V) (PadicAlgCl p))
  have hΦ : Function.Bijective Φ := ptHom_bijective _ _
  have lab : ∀ a q, Φ (f q) = h ≫ ρ.pt a → yy a = QuotientAddGroup.mk q.y := fun a q e =>
    hyy a q _ ((f₁ _ _).2 rfl) ((congrArg (fun z => z.left) e).trans (by rw [← hh]; rfl))
  let pt : Multiplicative S.Gam →* (baseOver (Sp S.R) ⟶ ρ.P.A) := MonoidHom.mk' (fun a => ρ.pt a.toAdd) fun _ _ => ρ.pt_add _ _
  have onto : ∀ b, ∃ q, Φ (f q) = h ≫ ρ.pt b := fun b => by
    obtain ⟨x, hx⟩ := hΦ.2 (h ≫ ρ.pt b)
    obtain ⟨q, rfl⟩ := f₂ x (hΦ.1 (by
      have e : ρ.pt b ^ (S.r * S.N) = 1 := by
        refine (map_pow pt (Multiplicative.ofAdd b) _).symm.trans ?_
        rw [← ofAdd_nsmul, ← Nat.cast_smul_eq_nsmul (ZMod (S.r * S.N)), ZMod.natCast_self, zero_smul, ofAdd_zero, map_one]
      rw [map_pow, hx, map_one, ← MonObj.comp_pow, e, MonObj.comp_one]))
    exact ⟨q, hx⟩
  have weil : ∀ a b q q', Φ (f q) = h ≫ ρ.pt a → Φ (f q') = h ≫ ρ.pt b →
      WeilIs u.A.A u.A.L (S.r * S.N : ℕ) (f q) (f q') (unitOn (ω ^ (eStd S.g _ a b).val)) := fun a b q q' e e' => by
    have w := GlobalTheory.CommPairing.weilIs_pull hG ρ.P.isAb ρ.P.isLB h (ρ.weil a b (c₀ ^ (eStd S.g _ a b).val) (by
      rw [pow_mul, map_pow]; rfl))
    rw [← e, ← e'] at w
    refine (GlobalTheory.weilIs_iff_of_isGrpPullback_comm _ _ _ _ _ _ _ _ ρ.P.isLB u.A.isLB u.cart u.lb _ _ _ _
      (Φ (f q)) (Φ (f q')) _ rfl rfl).2 ?_
    convert w using 1
    rw [← map_pow, ← map_unitOn, ← hh]
  refine isoFree_perp_ker S yy hs fun l => ?_
  let χ := AddChar.zmodChar (S.r * S.N) hω.pow_eq_one
  let τ : Multiplicative u.D.toPre.X →* (PadicAlgCl p)ˣ := χ.toMonoidHom.comp l.toMultiplicative
  have hτ : ∀ α, τ (Multiplicative.ofAdd α) = ω ^ (l α).val := fun _ => rfl
  obtain ⟨q, hq, hqτ⟩ := exists_qkPt_tor (F := PadicAlgCl p) (k := S.r * S.N) u.D.tau_bimult τ (MonoidHom.ext fun α => by
    show (ω ^ (l α.toAdd).val) ^ (S.r * S.N) = 1
    rw [pow_right_comm, hω.pow_eq_one, one_pow])
  have hq1 : f q ^ (S.r * S.N) = 1 := by
    obtain ⟨w, hw⟩ := u.U.ext
    exact ((f₁ _ _).2 rfl w hw).1
  obtain ⟨a, ha, -⟩ := ρ.pt_bij (PadicAlgCl p) _ (Φ (f q)) (by rw [← map_pow, hq1, map_one])
  refine ⟨a, (lab a q ha.symm).trans (by rw [hq]; rfl), fun b α e => ?_⟩
  obtain ⟨q', hq'⟩ := onto b
  have e₁ := unitOn_injective (GlobalTheory.CommutatorPairing.weilIs_unique hG u.A.isAb u.A.isLB (weil a b q q' ha.symm hq')
    ((f₅ q q' _).1 (weilQkIs_tor hG q q' hq hqτ)))
  rw [hτ] at e₁
  rw [ZMod.val_injective _ (hω.pow_inj (ZMod.val_lt _) (ZMod.val_lt _) e₁)]
  obtain ⟨z, hz⟩ := QuotientAddGroup.eq.1 ((lab b q' hq').symm.trans e)
  have hz' : (S.r * S.N) • z = -q'.y + α := hz
  have := congrArg l hz'
  rw [map_nsmul, nsmul_eq_mul, ZMod.natCast_self, zero_mul, map_add, map_neg] at this
  exact neg_add_eq_zero.1 this.symm

end GlobalTheory.ZH.TorusPerp
end

import Mathlib
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.FiniteHomogeneousInf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabComp
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.OneArc
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.WeilIsGrpPullbackOfCommute
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsPushEquiv
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsAlgClosedJoinOfTwoFieldExtensions
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsMonHomIffOfIsGrpPullback
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.OActDescendOfGenerators
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsTripleOfFieldExtension
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.DetCondIffOfFieldExtension
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsUnitOfPowEqOne

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

namespace GlobalTheory.PELDesc

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H}

def tateAlong {k : Type} [Field k]
    {Q Q' : Type} [Group Q] [Group Q'] {act : 𝓞 E → Q → Q} {act' : 𝓞 E → Q' → Q'}
    {e : ℕ → Q → Q → kˣ → Prop} {e' : ℕ → Q' → Q' → kˣ → Prop} (Φ : Q ≃* Q')
    (hact : ∀ c x, Φ (act c x) = act' c (Φ x)) (he : ∀ n x y c, e n x y c → e' n (Φ x) (Φ y) c)
    (I : TateIso D k Q act e) : TateIso D k Q' act' e' where
  ζ := I.ζ
  ζ_prim := I.ζ_prim
  ζ_pow := I.ζ_pow
  ev := fun n a => Φ (I.ev n a)
  add := fun n a b => by simp only [I.add, map_mul]
  lin := fun n c a => by rw [← hact, I.lin]
  ker := fun n hn a => (map_eq_one_iff _ Φ.injective).trans (I.ker n hn a)
  onto := fun n hn x => by
    rw [← map_eq_one_iff Φ.symm Φ.symm.injective, map_pow, I.onto n hn]
    exact exists_congr fun a => Φ.eq_symm_apply
  tower := fun n m hn hm a => by rw [← map_pow, I.tower n m hn hm a]
  isom := fun n hn a b => he _ _ _ _ (I.isom n hn a b)

/- English proof (translation)
Substitute `hy` using the available equality. Take `⟨Φ, hΦ⟩` from `GlobalTheory.LiePull.exists_pushEquiv h (Over.mk x) (x ≫ f) rfl`. Establish `hA : ∀ (c : 𝓞 E) (z : Over.mk x ⟶ G'), Φ (z ≫ act' c) = Φ z ≫ act c`. Introduce `c z`. Apply `Over.OverMorphism.ext` to reduce the goal to its premises.

Simplify using `only [Over.comp_left, hΦ, Category.assoc, hact]`. Establish `hA' : ∀ (c : 𝓞 E) (z : Over.mk (x ≫ f) ⟶ G), Φ.symm (z ≫ act c) = Φ.symm z ≫ act' c`. Introduce `c z`. Apply `Φ.injective` to reduce the goal to its premises. Rewrite using `[MulEquiv.apply_symm_apply, hA, MulEquiv.apply_symm_apply]`.

Establish `hW : ∀ (n : ℕ) (z z' : Over.mk x ⟶ G') (c : kˣ), (Out.WeilIs G' L' n z z' (unitOn c) ↔ Out.WeilIs G L n (Φ z) (Φ z') (unitOn c))` using `fun n z z' c => GlobalTheory.weilIs_grpPullback_of_comm S S' G G' f φ L L' hL hL' h hI (Over.mk x) n z z' (Φ z) (Φ z') (unitOn c) (hΦ z) (hΦ z')`. Use `⟨fun I' => ⟨tateAlong Φ hA (fun n z z' c hz => (hW n z z' c).1 hz) I', rfl, fun n v => hΦ _⟩, fun I => ⟨tateAlong Φ.symm hA' (fun n z z' c hz => ?_) I, rfl, fun n v => ?_⟩⟩` and prove the remaining obligations. Rewrite using `[hW, MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply]`. Conclude with `hz`. Use `show _ = (Φ.symm (I.ev n v)).left ≫ φ`.

Rewrite using `[← hΦ, MulEquiv.apply_symm_apply]`.
-/
theorem tate_pull {S S' : Scheme.{0}} {G : Over S} {G' : Over S'} [GrpObj G] [GrpObj G'] [IsCommMonObj G]
    {f : S' ⟶ S} {φ : G'.left ⟶ G.left} {L : LB G.left} {L' : LB G'.left} (hL : L.IsLB) (hL' : L'.IsLB)
    (h : IsGrpPullback G' G f φ) (hI : LBIso L' (L.pull φ)) (act : 𝓞 E → (G ⟶ G)) (act' : 𝓞 E → (G' ⟶ G'))
    (hact : ∀ c, (act' c).left ≫ φ = φ ≫ (act c).left) {k : Type} [Field k] (x : Sp k ⟶ S') (y : Sp k ⟶ S)
    (hy : y = x ≫ f) :
    (∀ I' : TateIso D k (Over.mk x ⟶ G') (fun c z => z ≫ act' c) (fun n z z' c => Out.WeilIs G' L' n z z' (unitOn c)),
      ∃ I : TateIso D k (Over.mk y ⟶ G) (fun c z => z ≫ act c) (fun n z z' c => Out.WeilIs G L n z z' (unitOn c)),
        I.ζ = I'.ζ ∧ ∀ n v, (I.ev n v).left = (I'.ev n v).left ≫ φ) ∧
    (∀ I : TateIso D k (Over.mk y ⟶ G) (fun c z => z ≫ act c) (fun n z z' c => Out.WeilIs G L n z z' (unitOn c)),
      ∃ I' : TateIso D k (Over.mk x ⟶ G') (fun c z => z ≫ act' c) (fun n z z' c => Out.WeilIs G' L' n z z' (unitOn c)),
        I'.ζ = I.ζ ∧ ∀ n v, (I.ev n v).left = (I'.ev n v).left ≫ φ) := by
  subst hy
  obtain ⟨Φ, hΦ⟩ := GlobalTheory.LiePull.exists_pushEquiv h (Over.mk x) (x ≫ f) rfl
  have hA : ∀ (c : 𝓞 E) (z : Over.mk x ⟶ G'), Φ (z ≫ act' c) = Φ z ≫ act c := by
    intro c z
    apply Over.OverMorphism.ext
    simp only [Over.comp_left, hΦ, Category.assoc, hact]
  have hA' : ∀ (c : 𝓞 E) (z : Over.mk (x ≫ f) ⟶ G), Φ.symm (z ≫ act c) = Φ.symm z ≫ act' c := by
    intro c z
    apply Φ.injective
    rw [MulEquiv.apply_symm_apply, hA, MulEquiv.apply_symm_apply]
  have hW : ∀ (n : ℕ) (z z' : Over.mk x ⟶ G') (c : kˣ),
      (Out.WeilIs G' L' n z z' (unitOn c) ↔ Out.WeilIs G L n (Φ z) (Φ z') (unitOn c)) := fun n z z' c =>
    GlobalTheory.weilIs_grpPullback_of_comm S S' G G' f φ L L' hL hL' h hI (Over.mk x) n z z' (Φ z) (Φ z') (unitOn c)
      (hΦ z) (hΦ z')
  refine ⟨fun I' => ⟨tateAlong Φ hA (fun n z z' c hz => (hW n z z' c).1 hz) I', rfl, fun n v => hΦ _⟩,
    fun I => ⟨tateAlong Φ.symm hA' (fun n z z' c hz => ?_) I, rfl, fun n v => ?_⟩⟩
  · rw [hW, MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply]
    exact hz
  · show _ = (Φ.symm (I.ev n v)).left ≫ φ
    rw [← hΦ, MulEquiv.apply_symm_apply]

/- English proof (translation)
Substitute `hy` using the available equality. Establish `key : ∀ (σ : 𝓞 E →+* k) (n : ℕ), LieMult a' x σ n ↔ LieMult a (x ≫ f) σ n` using `fun σ n => GlobalTheory.LiePull.lieMult_pull (𝓞 E) S S' G G' f φ a a' h hact k x σ n`. Conclude with `forall_congr' fun σ => and_congr (imp_congr_right fun _ => key σ _) (imp_congr_right fun _ => key σ _)`.
-/
theorem detCond_pull {S S' : Scheme.{0}} {G : Over S} {G' : Over S'} [GrpObj G] [GrpObj G']
    {f : S' ⟶ S} {φ : G'.left ⟶ G.left} (h : IsGrpPullback G' G f φ) (a : OAct (𝓞 E) G) (a' : OAct (𝓞 E) G')
    (hact : ∀ c, (a'.act c).left ≫ φ = φ ≫ (a.act c).left) {k : Type} [Field k] (x : Sp k ⟶ S') (y : Sp k ⟶ S)
    (hy : y = x ≫ f) (ρ : k) : DetCond D a' x ρ ↔ DetCond D a y ρ := by
  subst hy
  have key : ∀ (σ : 𝓞 E →+* k) (n : ℕ), LieMult a' x σ n ↔ LieMult a (x ≫ f) σ n := fun σ n =>
    GlobalTheory.LiePull.lieMult_pull (𝓞 E) S S' G G' f φ a a' h hact k x σ n
  exact forall_congr' fun σ => and_congr (imp_congr_right fun _ => key σ _) (imp_congr_right fun _ => key σ _)

/- English proof (translation)
Use `show Spec.map _ ≫ Spec.map _ = Spec.map _`. Rewrite using `[← Spec.map_comp]`. Both sides reduce to the same expression.
-/
private theorem spMap_comp_var2 {R R' R'' : Type} [CommRing R] [CommRing R'] [CommRing R''] (f : R →+* R')
    (g : R' →+* R'') : spMap g ≫ spMap f = spMap (g.comp f) := by
  show Spec.map _ ≫ Spec.map _ = Spec.map _
  rw [← Spec.map_comp]
  rfl

/- English proof (translation)
Set `` to `i.toAlgebra`. Set `` to `κ.toAlgebra`. Establish `: Nontrivial (K ⊗[K₀] K')` using `Algebra.TensorProduct.nontrivial_of_algebraMap_injective_of_isDomain K₀ K K' i.injective κ.injective`. Take `⟨m, hm⟩` from `Ideal.exists_maximal (K ⊗[K₀] K')`. Set `: Field (K ⊗[K₀] K' ⧸ m)` to `Ideal.Quotient.field m`.

Set `q : K ⊗[K₀] K' →+* AlgebraicClosure (K ⊗[K₀] K' ⧸ m)` to `(algebraMap (K ⊗[K₀] K' ⧸ m) (AlgebraicClosure (K ⊗[K₀] K' ⧸ m))).comp (Ideal.Quotient.mk m)`. Set `jL : K →+* K ⊗[K₀] K'` to `(Algebra.TensorProduct.includeLeft : K →ₐ[K₀] K ⊗[K₀] K').toRingHom`. Set `jR : K' →+* K ⊗[K₀] K'` to `(Algebra.TensorProduct.includeRight : K' →ₐ[K₀] K ⊗[K₀] K').toRingHom`. Use `⟨AlgebraicClosure (K ⊗[K₀] K' ⧸ m), inferInstance, inferInstance, charZero_of_injective_ringHom (q.comp jR).injective, q.comp jL, q.comp jR, ?_⟩` and prove the remaining obligations. Use extensionality with `a`.

Establish `hL` using `(Algebra.TensorProduct.includeLeft : K →ₐ[K₀] K ⊗[K₀] K').commutes a`. Establish `hR` using `(Algebra.TensorProduct.includeRight : K' →ₐ[K₀] K ⊗[K₀] K').commutes a`. Conclude with `congrArg q (hL.trans hR.symm)`.
-/
private theorem exists_algClosed_amalgam_of_charZero {K₀ K K' : Type} [Field K₀] [Field K] [Field K'] [CharZero K'] (i : K₀ →+* K)
    (κ : K₀ →+* K') : ∃ (Ω : Type) (_ : Field Ω) (_ : IsAlgClosed Ω) (_ : CharZero Ω) (iK : K →+* Ω) (iK' : K' →+* Ω),
      iK.comp i = iK'.comp κ := by
  let := i.toAlgebra
  let := κ.toAlgebra
  have : Nontrivial (K ⊗[K₀] K') :=
    Algebra.TensorProduct.nontrivial_of_algebraMap_injective_of_isDomain K₀ K K' i.injective κ.injective
  obtain ⟨m, hm⟩ := Ideal.exists_maximal (K ⊗[K₀] K')
  let : Field (K ⊗[K₀] K' ⧸ m) := Ideal.Quotient.field m
  let q : K ⊗[K₀] K' →+* AlgebraicClosure (K ⊗[K₀] K' ⧸ m) :=
    (algebraMap (K ⊗[K₀] K' ⧸ m) (AlgebraicClosure (K ⊗[K₀] K' ⧸ m))).comp (Ideal.Quotient.mk m)
  let jL : K →+* K ⊗[K₀] K' := (Algebra.TensorProduct.includeLeft : K →ₐ[K₀] K ⊗[K₀] K').toRingHom
  let jR : K' →+* K ⊗[K₀] K' := (Algebra.TensorProduct.includeRight : K' →ₐ[K₀] K ⊗[K₀] K').toRingHom
  refine ⟨AlgebraicClosure (K ⊗[K₀] K' ⧸ m), inferInstance, inferInstance,
    charZero_of_injective_ringHom (q.comp jR).injective, q.comp jL, q.comp jR, ?_⟩
  ext a
  have hL := (Algebra.TensorProduct.includeLeft : K →ₐ[K₀] K ⊗[K₀] K').commutes a
  have hR := (Algebra.TensorProduct.includeRight : K' →ₐ[K₀] K ⊗[K₀] K').commutes a
  exact congrArg q (hL.trans hR.symm)

/- English proof (translation)
Introduce `hL E _ _ _ H D g k J a bas o _ b ρ K₀ K _ _ i β₀ s t₀ t τ hcl hs hT hP`. Take `⟨φ, hφ, hLφ, hactφ, hgeo⟩` from `hP`. Take `⟨ψ, hψ, hLψ, hptψ, hactψ⟩` from `hT`. Use `t₀.ab.comm` as an intermediate fact. Use `hφ` as an intermediate fact.

Establish `hpb : IsGrpPullback τ.G t₀.A (spMap i) (φ.hom.left ≫ ψ)` using `IsGrpPullback.congr (IsGrpPullback.comp (isGrpPullback_of_iso φ) hψ) (Category.id_comp _) rfl`. Establish `hLc : LBIso τ.PP.L (t₀.L.pull (φ.hom.left ≫ ψ))`. Take `⟨w, hw⟩` from `hLψ`. Establish `h2 : LBIso (t.L.pull φ.hom.left) (t₀.L.pull (φ.hom.left ≫ ψ))` using `iso_linComb ((isGen_iff w).1 hw) (K := PUnit) (fun _ => φ.hom.left) (fun _ => 1)`. Conclude with `LBIso.trans τ.PP.isLB (pull_isLB t.isLB _) (pull_isLB t₀.isLB _) hLφ h2`.

Establish `hφl : ∀ j, (τ.act.act (a j)).left ≫ φ.hom.left = φ.hom.left ≫ (t.act j).left` using `fun j => by`. Rewrite using `[← Over.comp_left, hactφ j, Over.comp_left]`. Take `⟨r, hr1, hr2⟩` from `GlobalTheory.oAct_descend_of_generators (𝓞 E) J a K₀ K i t₀.A τ.G (φ.hom.left ≫ ψ) τ.act t₀.act hcl hpb (fun j => by rw [← Category.assoc, hφl j, Category.assoc, hactψ j, Category.assoc])`. Take `⟨τ₀, e, he, hLe, hacte⟩` from `GlobalTheory.exists_triple_of_fieldExtension hL E H K₀ K i τ t₀.A (φ.hom.left ≫ ψ) t₀.L r t₀.ab hpb t₀.isLB hLc hr2`. Use `he` as an intermediate fact.

Establish `hel : ∀ c, (τ₀.act.act c).left ≫ e.hom.left = e.hom.left ≫ (r.act c).left` using `fun c => by`. Rewrite using `[← Over.comp_left, hacte c, Over.comp_left]`. Establish `hpe : IsGrpPullback τ₀.G t₀.A (𝟙 _) e.hom.left` using `isGrpPullback_of_iso e`. Use `⟨τ₀, e, he, hLe, fun j => by rw [hacte, hr1], ?_⟩` and prove the remaining obligations. Introduce `K' _ _ _ x' β hx'`.

Use `set κ : K₀ →+* K' := (Spec.preimage x').hom with hκ`. Establish `hxκ : x' = spMap κ` using `by show x' = Spec.map (CommRingCat.ofHom (Spec.preimage x').hom)`. Rewrite using `[CommRingCat.ofHom_hom, Spec.map_preimage]`. Establish `hβ : κ.comp β₀ = β`. Establish `h1 : spMap (κ.comp β₀) = spMap β` using `by rw [← spMap_comp_var2, ← hxκ, hx']`.

Establish `h2` using `Spec.map_injective h1`. Conclude with `congrArg CommRingCat.Hom.hom h2`. Establish `hk : 0 < k`. Break down `Nat.eq_zero_or_pos k with h0 | h0` into its components or cases. It suffices to derive a contradiction.

Establish `hu` using `b.unit.map β`. Rewrite `hu` using `[h0, Nat.cast_zero, map_zero]`. Conclude with `not_isUnit_zero hu`. Conclude with `h0`. Take `⟨Ω, _, _, _, iK, iK', hΩ⟩` from `exists_algClosed_amalgam_of_charZero i κ`.

Establish `hsq : spMap iK' ≫ x' = spMap iK ≫ spMap i`. Rewrite using `[hxκ, spMap_comp_var2, spMap_comp_var2, hΩ]`. Establish `hsΩ : spMap iK ≫ s = spMap (iK.comp (i.comp β₀))`. Rewrite using `[hs, ← Category.assoc, spMap_comp_var2, spMap_comp_var2]`. Establish `hbr : ∀ z : o, iK (i (β₀ z)) = iK' (β z)` using `fun z => by`.

Rewrite using `[← hβ]`. Conclude with `congrArg (fun F : K₀ →+* Ω => F (β₀ z)) hΩ`. Take `⟨hdet, I₀, hI₀ζ, hI₀ev⟩` from `hgeo Ω (spMap iK) (iK.comp (i.comp β₀)) hsΩ`. Use `t₀.dim` as an intermediate fact. Establish `: Smooth t₀.A.hom` using `SmoothOfRelativeDimension.smooth g t₀.A.hom`.

Use `⟨?_, ?_⟩` and prove the remaining obligations. Establish `d1` using `(detCond_pull hpb r τ.act hr2 (spMap iK) (spMap iK' ≫ x') hsq ((iK.comp (i.comp β₀)) ρ)).1 hdet`. Establish `d2 : DetCond D r (spMap iK' ≫ x') (iK' (β ρ))`. Rewrite using `[← hbr ρ]`. Conclude with `d1`.

Establish `d3` using `(GlobalTheory.detCond_iff_of_field_extension E H D (Sp K₀) t₀.A K' Ω iK' x' r (β ρ) inferInstance).1 d2`. Conclude with `(detCond_pull hpe r τ₀.act hel x' x' (Category.comp_id _).symm (β ρ)).2 d3`. Take `⟨I₁, hI₁ζ, hI₁ev⟩` from `(tate_pull t₀.isLB τ.PP.isLB hpb hLc r.act τ.act.act hr2 (spMap iK) (spMap iK' ≫ x') hsq).1 I₀`. Take `⟨I, hI⟩` from `(GlobalTheory.TateIsoFieldExt.tateIso_fieldExt hL E H D (Sp K₀) t₀.pol r.act K' Ω iK' x').2 I₁ r.hom`. Take `⟨I', hI'ζ, hI'ev⟩` from `(tate_pull t₀.isLB τ₀.PP.isLB hpe hLe r.act τ₀.act.act hel x' x' (Category.comp_id _).symm).2 I`.

Use `⟨I', ?_, fun j => ?_⟩` and prove the remaining obligations. Rewrite using `[hI'ζ]`. Apply `iK'.injective` to reduce the goal to its premises. Rewrite using `[← (hI k hk).1, hI₁ζ, hI₀ζ]`. Simplify using `only [RingHom.comp_apply]`.

Conclude with `hbr _`. Apply `Over.OverMorphism.ext` to reduce the goal to its premises. Rewrite using `[Over.comp_left, ← hI'ev]`. Use `show (I.ev k (bas (Pi.single j 1))).left = x' ≫ (t₀.pt j).left`. Establish `ep` using `((GlobalTheory.FieldBaseChange.epi_and_isMonHom_iff K' Ω iK').1 (Sp K') (Sp Ω) (𝟙 _) (𝟙 _) (spMap iK') IsPullback.of_id_snd).1`.

Apply `ep.left_cancellation` to reduce the goal to its premises. Establish `e1 : (I₁.ev k (bas (Pi.single j 1))).left = spMap iK' ≫ (I.ev k (bas (Pi.single j 1))).left`. Rewrite using `[(hI k hk).2 (bas (Pi.single j 1)), Over.comp_left]`. Both sides reduce to the same expression. Establish `e2 : (I₀.ev k (bas (Pi.single j 1))).left ≫ φ.hom.left = spMap iK ≫ (t.pt j).left`.

Rewrite using `[← Over.comp_left, hI₀ev j, Over.comp_left]`. Both sides reduce to the same expression. Rewrite using `[← e1, hI₁ev, ← Category.assoc, e2, Category.assoc, hptψ j, ← Category.assoc, ← hsq, Category.assoc]`. Both sides reduce to the same expression.
-/
theorem isPEL_descends : Out.Laws → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (g k : ℕ) (J : Type) (a : J → 𝓞 E) (bas : (Fin (2 * g) → ℤ) ≃ₗ[ℤ] D.La) (o : Type) [CommRing o] (b : TBase o k) (ρ : o) (K₀ K : Type) [Field K₀] [Field K] (i : K₀ →+* K) (β₀ : o →+* K₀) (s : Sp K ⟶ Sp o) (t₀ : TObj g k J b (spMap β₀)) (t : TObj g k J b s) (τ : SAB H (Sp K)), Subring.closure (Set.range a) = ⊤ → s = spMap i ≫ spMap β₀ → TMap t t₀ (spMap i) → IsPEL D a bas ρ t τ → ∃ τ₀ : SAB H (Sp K₀), IsPEL D a bas ρ t₀ τ₀ := by
  intro hL E _ _ _ H D g k J a bas o _ b ρ K₀ K _ _ i β₀ s t₀ t τ hcl hs hT hP
  obtain ⟨φ, hφ, hLφ, hactφ, hgeo⟩ := hP
  obtain ⟨ψ, hψ, hLψ, hptψ, hactψ⟩ := hT
  have := t₀.ab.comm
  have := hφ

  have hpb : IsGrpPullback τ.G t₀.A (spMap i) (φ.hom.left ≫ ψ) :=
    IsGrpPullback.congr (IsGrpPullback.comp (isGrpPullback_of_iso φ) hψ) (Category.id_comp _) rfl
  have hLc : LBIso τ.PP.L (t₀.L.pull (φ.hom.left ≫ ψ)) := by
    obtain ⟨w, hw⟩ := hLψ
    have h2 : LBIso (t.L.pull φ.hom.left) (t₀.L.pull (φ.hom.left ≫ ψ)) :=
      iso_linComb ((isGen_iff w).1 hw) (K := PUnit) (fun _ => φ.hom.left) (fun _ => 1)
    exact LBIso.trans τ.PP.isLB (pull_isLB t.isLB _) (pull_isLB t₀.isLB _) hLφ h2
  have hφl : ∀ j, (τ.act.act (a j)).left ≫ φ.hom.left = φ.hom.left ≫ (t.act j).left := fun j => by
    rw [← Over.comp_left, hactφ j, Over.comp_left]
  obtain ⟨r, hr1, hr2⟩ := GlobalTheory.oAct_descend_of_generators (𝓞 E) J a K₀ K i t₀.A τ.G (φ.hom.left ≫ ψ) τ.act t₀.act
    hcl hpb (fun j => by rw [← Category.assoc, hφl j, Category.assoc, hactψ j, Category.assoc])
  obtain ⟨τ₀, e, he, hLe, hacte⟩ :=
    GlobalTheory.exists_triple_of_fieldExtension hL E H K₀ K i τ t₀.A (φ.hom.left ≫ ψ) t₀.L r t₀.ab hpb t₀.isLB hLc hr2
  have := he
  have hel : ∀ c, (τ₀.act.act c).left ≫ e.hom.left = e.hom.left ≫ (r.act c).left := fun c => by
    rw [← Over.comp_left, hacte c, Over.comp_left]
  have hpe : IsGrpPullback τ₀.G t₀.A (𝟙 _) e.hom.left := isGrpPullback_of_iso e
  refine ⟨τ₀, e, he, hLe, fun j => by rw [hacte, hr1], ?_⟩
  intro K' _ _ _ x' β hx'

  set κ : K₀ →+* K' := (Spec.preimage x').hom with hκ
  have hxκ : x' = spMap κ := by
    show x' = Spec.map (CommRingCat.ofHom (Spec.preimage x').hom)
    rw [CommRingCat.ofHom_hom, Spec.map_preimage]
  have hβ : κ.comp β₀ = β := by
    have h1 : spMap (κ.comp β₀) = spMap β := by rw [← spMap_comp_var2, ← hxκ, hx']
    have h2 := Spec.map_injective h1
    exact congrArg CommRingCat.Hom.hom h2
  have hk : 0 < k := by
    rcases Nat.eq_zero_or_pos k with h0 | h0
    · exfalso
      have hu := b.unit.map β
      rw [h0, Nat.cast_zero, map_zero] at hu
      exact not_isUnit_zero hu
    · exact h0

  obtain ⟨Ω, _, _, _, iK, iK', hΩ⟩ := exists_algClosed_amalgam_of_charZero i κ
  have hsq : spMap iK' ≫ x' = spMap iK ≫ spMap i := by
    rw [hxκ, spMap_comp_var2, spMap_comp_var2, hΩ]
  have hsΩ : spMap iK ≫ s = spMap (iK.comp (i.comp β₀)) := by
    rw [hs, ← Category.assoc, spMap_comp_var2, spMap_comp_var2]
  have hbr : ∀ z : o, iK (i (β₀ z)) = iK' (β z) := fun z => by
    rw [← hβ]
    exact congrArg (fun F : K₀ →+* Ω => F (β₀ z)) hΩ
  obtain ⟨hdet, I₀, hI₀ζ, hI₀ev⟩ := hgeo Ω (spMap iK) (iK.comp (i.comp β₀)) hsΩ
  have := t₀.dim
  have : Smooth t₀.A.hom := SmoothOfRelativeDimension.smooth g t₀.A.hom
  refine ⟨?_, ?_⟩
  ·
    have d1 := (detCond_pull hpb r τ.act hr2 (spMap iK) (spMap iK' ≫ x') hsq
      ((iK.comp (i.comp β₀)) ρ)).1 hdet
    have d2 : DetCond D r (spMap iK' ≫ x') (iK' (β ρ)) := by
      rw [← hbr ρ]
      exact d1
    have d3 := (GlobalTheory.detCond_iff_of_field_extension E H D (Sp K₀) t₀.A K' Ω iK' x' r (β ρ) inferInstance).1 d2
    exact (detCond_pull hpe r τ₀.act hel x' x' (Category.comp_id _).symm (β ρ)).2 d3
  ·
    obtain ⟨I₁, hI₁ζ, hI₁ev⟩ := (tate_pull t₀.isLB τ.PP.isLB hpb hLc r.act τ.act.act hr2 (spMap iK)
      (spMap iK' ≫ x') hsq).1 I₀
    obtain ⟨I, hI⟩ := (GlobalTheory.TateIsoFieldExt.tateIso_fieldExt hL E H D (Sp K₀) t₀.pol r.act K' Ω iK' x').2 I₁ r.hom
    obtain ⟨I', hI'ζ, hI'ev⟩ := (tate_pull t₀.isLB τ₀.PP.isLB hpe hLe r.act τ₀.act.act hel x' x'
      (Category.comp_id _).symm).2 I
    refine ⟨I', ?_, fun j => ?_⟩
    · rw [hI'ζ]
      apply iK'.injective
      rw [← (hI k hk).1, hI₁ζ, hI₀ζ]
      simp only [RingHom.comp_apply]
      exact hbr _
    · apply Over.OverMorphism.ext
      rw [Over.comp_left, ← hI'ev]
      show (I.ev k (bas (Pi.single j 1))).left = x' ≫ (t₀.pt j).left
      have ep := ((GlobalTheory.FieldBaseChange.epi_and_isMonHom_iff K' Ω iK').1 (Sp K') (Sp Ω) (𝟙 _) (𝟙 _) (spMap iK')
        IsPullback.of_id_snd).1
      apply ep.left_cancellation
      have e1 : (I₁.ev k (bas (Pi.single j 1))).left = spMap iK' ≫ (I.ev k (bas (Pi.single j 1))).left := by
        rw [(hI k hk).2 (bas (Pi.single j 1)), Over.comp_left]
        rfl
      have e2 : (I₀.ev k (bas (Pi.single j 1))).left ≫ φ.hom.left = spMap iK ≫ (t.pt j).left := by
        rw [← Over.comp_left, hI₀ev j, Over.comp_left]
        rfl
      rw [← e1, hI₁ev, ← Category.assoc, e2, Category.assoc, hptψ j, ← Category.assoc, ← hsq, Category.assoc]
      rfl

end GlobalTheory.PELDesc

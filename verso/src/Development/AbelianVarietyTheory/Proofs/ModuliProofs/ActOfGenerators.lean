import Mathlib
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.PushEquivSymmLeft
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsPELPull
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.EqOneOfSurjectiveAppTopOfSection
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.FormallyUnramifiedMulInvertibleInteger
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.BijectiveRestrictPointsOfEtaleOfHenselian

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

namespace GlobalTheory.UnderMap

/- English proof (translation)
Establish `hw : (Out.mulA G n).left ≫ G.hom = G.hom` using `Over.w _`. Establish `h₁ : FormallyUnramified (Out.mulA G n).left` using `formallyUnramified_mulA S G n hn`. Establish `h₂ : LocallyOfFiniteType ((Out.mulA G n).left ≫ G.hom)` using `by rw [hw]; infer_instance`. Establish `h₃ : LocallyOfFiniteType (Out.mulA G n).left` using `locallyOfFiniteType_of_comp _ G.hom`. Establish `e : ∀ w : 𝟙_ (Over S) ⟶ G, w ≫ Out.mulA G n = w ^ n` using `fun w => by`.

Rewrite using `[Out.mulA, MonObj.comp_pow, Category.comp_id]`. Apply `Over.OverMorphism.ext` to reduce the goal to its premises. Use `eq_of_range_equalizer_ι_eq_univ (Out.mulA G n).left (by rw [← Over.comp_left, ← Over.comp_left, e, e, h]) (Set.eq_univ_of_forall fun p => ?_)` and prove the remaining obligations. Set `k` to `AlgebraicClosure (S.residueField p)`. Set `x : Sp k ⟶ S` to `spMap (algebraMap (S.residueField p) k) ≫ S.fromSpecResidueField p`.

Establish `hx : x ≫ u.left = x ≫ v.left`. Use `congrArg (fun z => z.left) (hg k x)` as an intermediate fact. Simplify using `only [Over.comp_left, ObjPull.toUnit_left'] at this`. Conclude with `this`. Use `range_subset_range_equalizer_ι (T := S) x hx ⟨(default : PrimeSpectrum k), ?_⟩` and prove the remaining obligations.

Use `show S.fromSpecResidueField p _ = p`. Conclude with `Scheme.fromSpecResidueField_apply p _`.
-/
theorem sec_ext_of_pow_eq {S : Scheme.{0}} (G : Over S) [GrpObj G] [IsCommMonObj G] [LocallyOfFiniteType G.hom]
    (n : ℕ) (hn : IsUnit (n : Γ(S, ⊤))) (u v : 𝟙_ (Over S) ⟶ G) (h : u ^ n = v ^ n)
    (hg : ∀ (k : Type) [Field k] [IsAlgClosed k] (x : Sp k ⟶ S),
      toUnit (Over.mk x) ≫ u = toUnit (Over.mk x) ≫ v) : u = v := by
  have hw : (Out.mulA G n).left ≫ G.hom = G.hom := Over.w _
  have h₁ : FormallyUnramified (Out.mulA G n).left := formallyUnramified_mulA S G n hn
  have h₂ : LocallyOfFiniteType ((Out.mulA G n).left ≫ G.hom) := by rw [hw]; infer_instance
  have h₃ : LocallyOfFiniteType (Out.mulA G n).left := locallyOfFiniteType_of_comp _ G.hom
  have e : ∀ w : 𝟙_ (Over S) ⟶ G, w ≫ Out.mulA G n = w ^ n := fun w => by
    rw [Out.mulA, MonObj.comp_pow, Category.comp_id]
  apply Over.OverMorphism.ext
  refine eq_of_range_equalizer_ι_eq_univ (Out.mulA G n).left
    (by rw [← Over.comp_left, ← Over.comp_left, e, e, h]) (Set.eq_univ_of_forall fun p => ?_)
  let k := AlgebraicClosure (S.residueField p)
  let x : Sp k ⟶ S := spMap (algebraMap (S.residueField p) k) ≫ S.fromSpecResidueField p
  have hx : x ≫ u.left = x ≫ v.left := by
    have := congrArg (fun z => z.left) (hg k x)
    simp only [Over.comp_left, ObjPull.toUnit_left'] at this
    exact this
  refine range_subset_range_equalizer_ι (T := S) x hx ⟨(default : PrimeSpectrum k), ?_⟩
  show S.fromSpecResidueField p _ = p
  exact Scheme.fromSpecResidueField_apply p _

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}

/- English proof (translation)
Use `h 0 0` as an intermediate fact. Rewrite `this` using `[add_zero]`. Conclude with `mul_eq_left.1 this.symm`.
-/
theorem map_zero_of_add {A Q : Type} [AddGroup A] [Group Q] {F : A → Q} (h : ∀ a c, F (a + c) = F a * F c) :
    F 0 = 1 := by
  have := h 0 0
  rw [add_zero] at this
  exact mul_eq_left.1 this.symm

/- English proof (translation)
Proceed by induction on `n with`. Consider the case `zero => rw [zero_nsmul, pow_zero, map_zero_of_add h]`. Consider the case `succ n ih => rw [succ_nsmul, h, ih, pow_succ]`.
-/
theorem map_nsmul_of_add {A Q : Type} [AddGroup A] [Group Q] {F : A → Q} (h : ∀ a c, F (a + c) = F a * F c)
    (n : ℕ) (a : A) : F (n • a) = F a ^ n := by
  induction n with
  | zero => rw [zero_nsmul, pow_zero, map_zero_of_add h]
  | succ n ih => rw [succ_nsmul, h, ih, pow_succ]

def eqSub {A Q : Type} [AddGroup A] [Group Q] {F F' : A → Q} (h : ∀ a c, F (a + c) = F a * F c)
    (h' : ∀ a c, F' (a + c) = F' a * F' c) : AddSubgroup A :=
  AddMonoidHom.eqLocus (AddMonoidHom.mk' (fun a => Additive.ofMul (F a)) fun a c => congrArg Additive.ofMul (h a c))
    (AddMonoidHom.mk' (fun a => Additive.ofMul (F' a)) fun a c => congrArg Additive.ofMul (h' a c))

/- English proof (translation)
Unfold both sides. The equivalence is reflexive.
-/
theorem mem_eqSub {A Q : Type} [AddGroup A] [Group Q] {F F' : A → Q} (h : ∀ a c, F (a + c) = F a * F c)
    (h' : ∀ a c, F' (a + c) = F' a * F' c) (a : A) : a ∈ eqSub h h' ↔ F a = F' a := Iff.rfl

/- English proof (translation)
Establish `hM : 0 < l.M` using `lt_of_lt_of_le (by norm_num) l.three_le`. Establish `hq : 0 < l.A / l.M` using `Nat.div_pos (Nat.le_of_dvd l.A_pos hd) hM`. Establish `hA : l.M * (l.A / l.M) = l.A` using `Nat.mul_div_cancel' hd`. Establish `hp` using `ob.proper`. Establish `hn : IsUnit (l.M : Γ(S, ⊤))`.

Simplify using `using (bB.unit l.M hM).map (sB.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of B)).inv.hom)`. Use `sec_ext_of_pow_eq ob.t.G l.M hn _ _ ?_ fun k _ _ x => ?_` and prove the remaining obligations. Rewrite using `[← pow_mul, mul_comm, hA, ← map_nsmul_of_add ob.etaA_add, ob.etaA_ker, ← map_nsmul_of_add ob.eta_add]`. Apply `ob.eta_ker` to reduce the goal to its premises. Rewrite using `[← Nat.cast_smul_eq_nsmul (𝓞 E)]`.

Use `Submodule.smul_mem_smul ?_ trivial` and prove the remaining obligations. Establish `hle : l.Mb * l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) ≤ l.Mb` using `Ideal.mul_le_left`. Rewrite `hle` using `[l.prod]`. Conclude with `hle (Ideal.mem_span_singleton_self _)`. Take `⟨β, hβ⟩ : ∃ β : B →+* k, x ≫ sB = spMap β` from `⟨(Spec.preimage (x ≫ sB)).hom, (Spec.map_preimage _).symm⟩`.

Take `⟨-, I, -, h₁, h₂⟩` from `ob.geom k x β hβ`. Rewrite using `[h₂ a ha, MonObj.comp_pow, h₁ a, ← I.tower l.M (l.A / l.M) hM hq a, hA]`.
-/
theorem eta_eq_pow {B : Type} [CommRing B] {bB : Base l B} {S : Scheme.{0}} {sB : S ⟶ Sp B} (ob : Obj D l bB sB)
    (hd : l.M ∣ l.A) (a : D.La) (ha : a ∈ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) • (⊤ : Submodule (𝓞 E) D.La)) :
    ob.eta a = ob.etaA a ^ (l.A / l.M) := by
  have hM : 0 < l.M := lt_of_lt_of_le (by norm_num) l.three_le
  have hq : 0 < l.A / l.M := Nat.div_pos (Nat.le_of_dvd l.A_pos hd) hM
  have hA : l.M * (l.A / l.M) = l.A := Nat.mul_div_cancel' hd
  have hp := ob.proper
  have hn : IsUnit (l.M : Γ(S, ⊤)) := by
    simpa using (bB.unit l.M hM).map (sB.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of B)).inv.hom)
  refine sec_ext_of_pow_eq ob.t.G l.M hn _ _ ?_ fun k _ _ x => ?_
  · rw [← pow_mul, mul_comm, hA, ← map_nsmul_of_add ob.etaA_add, ob.etaA_ker, ← map_nsmul_of_add ob.eta_add]
    apply ob.eta_ker
    rw [← Nat.cast_smul_eq_nsmul (𝓞 E)]
    refine Submodule.smul_mem_smul ?_ trivial
    have hle : l.Mb * l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) ≤ l.Mb := Ideal.mul_le_left
    rw [l.prod] at hle
    exact hle (Ideal.mem_span_singleton_self _)
  · obtain ⟨β, hβ⟩ : ∃ β : B →+* k, x ≫ sB = spMap β := ⟨(Spec.preimage (x ≫ sB)).hom, (Spec.map_preimage _).symm⟩
    obtain ⟨-, I, -, h₁, h₂⟩ := ob.geom k x β hβ
    rw [h₂ a ha, MonObj.comp_pow, h₁ a, ← I.tower l.M (l.A / l.M) hM hq a, hA]

section Pull

variable {B B' : Type} [CommRing B] [CommRing B'] {bB : Base l B} {bB' : Base l B'} {S S' : Scheme.{0}}
  {sB : S ⟶ Sp B} {sB' : S' ⟶ Sp B'} {f : S' ⟶ S}

/- English proof (translation)
Use `⟨fun e => e ▸ ObjPull.secPull_left h u, fun e => ?_⟩` and prove the remaining obligations. Apply `Over.OverMorphism.ext` to reduce the goal to its premises. Apply `h.1.hom_ext` to reduce the goal to its premises. Rewrite using `[e, ObjPull.secPull_left]`. Rewrite using `[Over.w, Over.w]`.
-/
theorem eq_secPull {G : Over S} {G' : Over S'} [GrpObj G] [GrpObj G'] {φ : G'.left ⟶ G.left}
    (h : IsGrpPullback G' G f φ) (u' : 𝟙_ (Over S') ⟶ G') (u : 𝟙_ (Over S) ⟶ G) :
    u' = ObjPull.secPull h u ↔ u'.left ≫ φ = f ≫ u.left := by
  refine ⟨fun e => e ▸ ObjPull.secPull_left h u, fun e => ?_⟩
  apply Over.OverMorphism.ext
  apply h.1.hom_ext
  · rw [e, ObjPull.secPull_left]
  · rw [Over.w, Over.w]

/- English proof (translation)
Establish `hA : ∀ a, ob'.etaA a = ObjPull.secPull h (ob.etaA a)`. Introduce `a`. Establish `add : ∀ a c, ObjPull.secPull h (ob.etaA (a + c)) = ObjPull.secPull h (ob.etaA a) * ObjPull.secPull h (ob.etaA c)` using `fun a c => by rw [ob.etaA_add, map_mul]`. Use `(mem_eqSub (F' := fun a => ObjPull.secPull h (ob.etaA a)) ob'.etaA_add add a).1 ?_` and prove the remaining obligations. Take `⟨c, rfl⟩` from `bas.surjective a`.

Establish `hc : c = ∑ i, c i • (Pi.single i 1 : Fin n → ℤ)`. Use extensionality with `j`. Simplify using `[Pi.single_apply]`. Rewrite using `[hc, map_sum]`. Use `sum_mem fun i _ => ?_` and prove the remaining obligations.

Rewrite using `[map_smul]`. Use `zsmul_mem ?_ _` and prove the remaining obligations. Conclude with `(eq_secPull h _ _).2 (hb i)`. Use `⟨fun a => (eq_secPull h _ _).1 ?_, fun a => (eq_secPull h _ _).1 (hA a)⟩` and prove the remaining obligations. Establish `ha : a ∈ (l.Mb ⊔ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E)) • (⊤ : Submodule (𝓞 E) D.La)`.

Rewrite using `[l.coprime, Submodule.top_smul]`. Discharge the goal by the elementary cases of `trivial`. Rewrite `ha` using `[Submodule.sup_smul]`. Take `⟨a₁, h₁, a₂, h₂, rfl⟩` from `Submodule.mem_sup.1 ha`. Rewrite using `[ob.eta_add, ob'.eta_add, ob.eta_ker _ h₁, ob'.eta_ker _ h₁, _root_.one_mul, _root_.one_mul, eta_eq_pow ob hd _ h₂, eta_eq_pow ob' hd _ h₂, map_pow, hA]`.
-/
theorem levels_of_basis (ob : Obj D l bB sB) (ob' : Obj D l bB' sB') (hd : l.M ∣ l.A) {n : ℕ}
    (bas : (Fin n → ℤ) ≃ₗ[ℤ] D.La) {φ : ob'.t.G.left ⟶ ob.t.G.left} (h : IsGrpPullback ob'.t.G ob.t.G f φ)
    (hb : ∀ i, (ob'.etaA (bas (Pi.single i 1))).left ≫ φ = f ≫ (ob.etaA (bas (Pi.single i 1))).left) :
    (∀ a, (ob'.eta a).left ≫ φ = f ≫ (ob.eta a).left) ∧ ∀ a, (ob'.etaA a).left ≫ φ = f ≫ (ob.etaA a).left := by
  have hA : ∀ a, ob'.etaA a = ObjPull.secPull h (ob.etaA a) := by
    intro a
    have add : ∀ a c, ObjPull.secPull h (ob.etaA (a + c)) =
        ObjPull.secPull h (ob.etaA a) * ObjPull.secPull h (ob.etaA c) := fun a c => by rw [ob.etaA_add, map_mul]
    refine (mem_eqSub (F' := fun a => ObjPull.secPull h (ob.etaA a)) ob'.etaA_add add a).1 ?_
    obtain ⟨c, rfl⟩ := bas.surjective a
    have hc : c = ∑ i, c i • (Pi.single i 1 : Fin n → ℤ) := by
      ext j; simp [Pi.single_apply]
    rw [hc, map_sum]
    refine sum_mem fun i _ => ?_
    rw [map_smul]
    refine zsmul_mem ?_ _
    exact (eq_secPull h _ _).2 (hb i)
  refine ⟨fun a => (eq_secPull h _ _).1 ?_, fun a => (eq_secPull h _ _).1 (hA a)⟩
  have ha : a ∈ (l.Mb ⊔ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E)) • (⊤ : Submodule (𝓞 E) D.La) := by
    rw [l.coprime, Submodule.top_smul]; trivial
  rw [Submodule.sup_smul] at ha
  obtain ⟨a₁, h₁, a₂, h₂, rfl⟩ := Submodule.mem_sup.1 ha
  rw [ob.eta_add, ob'.eta_add, ob.eta_ker _ h₁, ob'.eta_ker _ h₁, _root_.one_mul, _root_.one_mul,
    eta_eq_pow ob hd _ h₂, eta_eq_pow ob' hd _ h₂, map_pow, hA]

/- English proof (translation)
Establish `add' : ∀ a c, pushHom h G' (α'.act (a + c)) = pushHom h G' (α'.act a) * pushHom h G' (α'.act c)` using `fun a c => by rw [α'.add, map_mul]`. Establish `add : ∀ a c, pushHom h G' (𝟙 _) ≫ α.act (a + c) = (pushHom h G' (𝟙 _) ≫ α.act a) * (pushHom h G' (𝟙 _) ≫ α.act c)` using `fun a c => by rw [α.add, MonObj.comp_mul]`. Establish `key : ∀ c, c ∈ eqSub (F` using `fun c => pushHom h G' (α'.act c)) (F' := fun c => pushHom h G' (𝟙 _) ≫ α.act c) add' add ↔ (α'.act c).left ≫ φ = φ ≫ (α.act c).left := fun c => by`. Rewrite using `[mem_eqSub]`. Establish `e : (pushHom h G' (𝟙 _) ≫ α.act c).left = φ ≫ (α.act c).left` using `congrArg (· ≫ (α.act c).left) (Category.id_comp φ)`.

Conclude with `⟨fun H => (congrArg (fun z => z.left) H).trans e, fun H => Over.OverMorphism.ext (H.trans e.symm)⟩`. Establish `hc : c ∈ Subring.closure (Set.range a)` using `by rw [ha]; trivial`. Rewrite using `[← key]`. Proceed by induction on `hc using Subring.closure_induction with`. Consider the case `mem x hx => obtain ⟨j, rfl⟩ := hx`.

Conclude with `(key _).2 (hj j)`. Consider the case `zero => exact zero_mem _`. Consider the case `one => rw [key, α.one, α'.one]`. Simplify using the standard rewrite rules. Consider the case `add x y _ _ hx hy => exact add_mem hx hy`.

Consider the case `neg x _ hx => exact neg_mem hx`. Consider the case `mul x y _ _ hx hy`. Rewrite `hx`, `hy`, the goal using `[key]`. Rewrite using `[α.mul, α'.mul, Over.comp_left, Over.comp_left, Category.assoc, hy, reassoc_of% hx]`.
-/
theorem act_of_generators {O : Type} [CommRing O] {G : Over S} {G' : Over S'} [GrpObj G] [GrpObj G']
    (α : OAct O G) (α' : OAct O G') {φ : G'.left ⟶ G.left} (h : IsGrpPullback G' G f φ) {J : Type} (a : J → O)
    (ha : Subring.closure (Set.range a) = ⊤)
    (hj : ∀ j, (α'.act (a j)).left ≫ φ = φ ≫ (α.act (a j)).left) (c : O) :
    (α'.act c).left ≫ φ = φ ≫ (α.act c).left := by
  have add' : ∀ a c, pushHom h G' (α'.act (a + c)) = pushHom h G' (α'.act a) * pushHom h G' (α'.act c) :=
    fun a c => by rw [α'.add, map_mul]
  have add : ∀ a c, pushHom h G' (𝟙 _) ≫ α.act (a + c) =
      (pushHom h G' (𝟙 _) ≫ α.act a) * (pushHom h G' (𝟙 _) ≫ α.act c) :=
    fun a c => by rw [α.add, MonObj.comp_mul]
  have key : ∀ c, c ∈ eqSub (F := fun c => pushHom h G' (α'.act c))
      (F' := fun c => pushHom h G' (𝟙 _) ≫ α.act c) add' add ↔ (α'.act c).left ≫ φ = φ ≫ (α.act c).left := fun c => by
    rw [mem_eqSub]
    have e : (pushHom h G' (𝟙 _) ≫ α.act c).left = φ ≫ (α.act c).left :=
      congrArg (· ≫ (α.act c).left) (Category.id_comp φ)
    exact ⟨fun H => (congrArg (fun z => z.left) H).trans e, fun H => Over.OverMorphism.ext (H.trans e.symm)⟩
  have hc : c ∈ Subring.closure (Set.range a) := by rw [ha]; trivial
  rw [← key]
  induction hc using Subring.closure_induction with
  | mem x hx => obtain ⟨j, rfl⟩ := hx; exact (key _).2 (hj j)
  | zero => exact zero_mem _
  | one => rw [key, α.one, α'.one]; simp
  | add x y _ _ hx hy => exact add_mem hx hy
  | neg x _ hx => exact neg_mem hx
  | mul x y _ _ hx hy =>
    rw [key] at hx hy ⊢
    rw [α.mul, α'.mul, Over.comp_left, Over.comp_left, Category.assoc, hy, reassoc_of% hx]

end Pull

/- English proof (translation)
Introduce `hL _ E _ _ _ H D g J a bas l B o _ _ bB b S S' sB sB' s s' ob ob' t t' f hd ha ⟨e, he, heL, hea, hep⟩ ⟨e', he', heL', hea', hep'⟩`. Establish `ih : e.inv.left ≫ e.hom.left = 𝟙 _` using `by rw [← Over.comp_left, e.inv_hom_id, Over.id_left]`. Establish `hi : e.hom.left ≫ e.inv.left = 𝟙 _` using `by rw [← Over.comp_left, e.hom_inv_id, Over.id_left]`. Establish `ih' : e'.inv.left ≫ e'.hom.left = 𝟙 _` using `by rw [← Over.comp_left, e'.inv_hom_id, Over.id_left]`. Establish `hi' : e'.hom.left ≫ e'.inv.left = 𝟙 _` using `by rw [← Over.comp_left, e'.hom_inv_id, Over.id_left]`.

Establish `m₁ : IsMonHom e.symm.hom` using `inferInstanceAs (IsMonHom e.inv)`. Establish `m₂ : IsMonHom e'.symm.hom` using `inferInstanceAs (IsMonHom e'.inv)`. Establish `a₁ : ∀ j, (ob.t.act.act (a j)).left ≫ e.hom.left = e.hom.left ≫ (t.act j).left` using `fun j => congrArg (fun z => z.left) (hea j)`. Establish `a₂ : ∀ j, (ob'.t.act.act (a j)).left ≫ e'.hom.left = e'.hom.left ≫ (t'.act j).left` using `fun j => congrArg (fun z => z.left) (hea' j)`. Establish `p₁ : ∀ i, (ob.etaA (bas (Pi.single i 1))).left ≫ e.hom.left = (t.pt i).left` using `hep`.

Establish `p₂ : ∀ i, (ob'.etaA (bas (Pi.single i 1))).left ≫ e'.hom.left = (t'.pt i).left` using `hep'`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨m⟩`. Establish `mL : LBIso ob'.t.PP.L (ob.t.PP.L.pull m.cm.F)`. Take `⟨w, hw, -⟩` from `m.lin`.

Conclude with `⟨w, hw⟩`. Use `⟨e'.inv.left ≫ m.cm.F ≫ e.hom.left, ?_, ?_, fun i => ?_, fun j => ?_⟩` and prove the remaining obligations. Conclude with `(IsGrpPullback.comp (isGrpPullback_of_iso e'.symm) (IsGrpPullback.comp m.cart (isGrpPullback_of_iso e))).congr (by simp) rfl`. Establish `k₁ : LBIso (ob'.t.PP.L.pull e'.inv.left) (t'.L.pull (𝟙 _))` using `PELPull.lbIso_pull heL' e'.inv.left ih'.symm`. Establish `k₂ : LBIso t'.L (ob'.t.PP.L.pull e'.inv.left)` using `k₁.symm.chartPull (chartPullUnpull t'.L _ rfl) (chartPullId _)`.

Establish `k₃ : LBIso ob'.t.PP.L (t.L.pull (m.cm.F ≫ e.hom.left))` using `mL.trans ob'.t.PP.isLB (pull_isLB ob.t.PP.isLB _) (pull_isLB t.isLB _) (PELPull.lbIso_pull heL m.cm.F rfl)`. Conclude with `k₂.trans t'.isLB (pull_isLB ob'.t.PP.isLB _) (pull_isLB t.isLB _) (PELPull.lbIso_pull k₃ e'.inv.left rfl)`. Use `m.etaA (bas (Pi.single i 1))` as an intermediate fact. Rewrite using `[← p₂, ← p₁, Category.assoc, reassoc_of% hi']`. Conclude with `(reassoc_of% this) _`.

Establish `h₂ : (t'.act j).left ≫ e'.inv.left = e'.inv.left ≫ (ob'.t.act.act (a j)).left`. Rewrite using `[← Category.id_comp (t'.act j).left, ← ih', Category.assoc, Category.assoc, ← reassoc_of% a₂ j, hi', Category.comp_id]`. Establish `h₃` using `m.act (a j)`. Rewrite using `[reassoc_of% h₂, reassoc_of% h₃, a₁, Category.assoc, Category.assoc]`. Introduce and unpack `⟨ψ, hψ, hψL, hpt, hact⟩`.

Establish `hc : IsGrpPullback ob'.t.G ob.t.G f (e'.hom.left ≫ ψ ≫ e.inv.left)` using `(IsGrpPullback.comp (isGrpPullback_of_iso e') (IsGrpPullback.comp hψ (isGrpPullback_of_iso e.symm))).congr (by simp) rfl`. Establish `kL : LBIso ob'.t.PP.L (ob.t.PP.L.pull (e'.hom.left ≫ ψ ≫ e.inv.left))`. Establish `k₁ : LBIso ob'.t.PP.L (t.L.pull (e'.hom.left ≫ ψ))` using `heL'.trans ob'.t.PP.isLB (pull_isLB t'.isLB _) (pull_isLB t.isLB _) (PELPull.lbIso_pull hψL e'.hom.left rfl)`. Use `k₁.trans ob'.t.PP.isLB (pull_isLB t.isLB _) (pull_isLB ob.t.PP.isLB _) (PELPull.lbIso_pull heL _ ?_).symm` and prove the remaining obligations. Rewrite using `[Category.assoc, Category.assoc, ih, Category.comp_id]`.

Take `⟨m, hm⟩` from `GlobalTheory.exists_sabMap_of_isProper_of_lbIso hL.globalFns E H S S' ob.t ob'.t f _ ob.proper hc kL (act_of_generators ob.t.act ob'.t.act hc a ha fun j => by`. Establish `h₂ : (t.act j).left ≫ e.inv.left = e.inv.left ≫ (ob.t.act.act (a j)).left`. Rewrite using `[← Category.id_comp (t.act j).left, ← ih, Category.assoc, Category.assoc, ← reassoc_of% a₁ j, hi, Category.comp_id]`. Rewrite using `[reassoc_of% a₂ j, reassoc_of% hact j, h₂, Category.assoc, Category.assoc])`. Take `⟨q₁, q₂⟩` from `levels_of_basis ob ob' hd bas hc fun i => by`.

Use `hpt i` as an intermediate fact. Rewrite using `[reassoc_of% p₂ i]`. Use `((reassoc_of% this) _).trans ?_` and prove the remaining obligations. Rewrite using `[← p₁]`. Conclude with `congrArg (f ≫ ·) (by rw [Category.assoc, hi, Category.comp_id])`.

Rewrite `q₁`, `q₂` using `[← hm]`. Conclude with `⟨⟨m, q₁, q₂⟩⟩`.
-/
theorem objMap_iff_tMap : Out.Laws → Out.Laws2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (g : ℕ) (J : Type) (a : J → 𝓞 E) (bas : (Fin (2 * g) → ℤ) ≃ₗ[ℤ] D.La) (l : Level H) (B o : Type) [CommRing B] [CommRing o] (bB : Base l B) (b : TBase o l.A) (S S' : Scheme.{0}) (sB : S ⟶ Sp B) (sB' : S' ⟶ Sp B) (s : S ⟶ Sp o) (s' : S' ⟶ Sp o) (ob : Obj D l bB sB) (ob' : Obj D l bB sB') (t : TObj g l.A J b s) (t' : TObj g l.A J b s') (f : S' ⟶ S), l.M ∣ l.A → Subring.closure (Set.range a) = ⊤ → ObjUnder ob a bas t → ObjUnder ob' a bas t' → (Nonempty (ObjMap ob' ob f) ↔ TMap t' t f) := by
  intro hL _ E _ _ _ H D g J a bas l B o _ _ bB b S S' sB sB' s s' ob ob' t t' f hd ha
    ⟨e, he, heL, hea, hep⟩ ⟨e', he', heL', hea', hep'⟩
  have ih : e.inv.left ≫ e.hom.left = 𝟙 _ := by rw [← Over.comp_left, e.inv_hom_id, Over.id_left]
  have hi : e.hom.left ≫ e.inv.left = 𝟙 _ := by rw [← Over.comp_left, e.hom_inv_id, Over.id_left]
  have ih' : e'.inv.left ≫ e'.hom.left = 𝟙 _ := by rw [← Over.comp_left, e'.inv_hom_id, Over.id_left]
  have hi' : e'.hom.left ≫ e'.inv.left = 𝟙 _ := by rw [← Over.comp_left, e'.hom_inv_id, Over.id_left]
  have m₁ : IsMonHom e.symm.hom := inferInstanceAs (IsMonHom e.inv)
  have m₂ : IsMonHom e'.symm.hom := inferInstanceAs (IsMonHom e'.inv)
  have a₁ : ∀ j, (ob.t.act.act (a j)).left ≫ e.hom.left = e.hom.left ≫ (t.act j).left := fun j =>
    congrArg (fun z => z.left) (hea j)
  have a₂ : ∀ j, (ob'.t.act.act (a j)).left ≫ e'.hom.left = e'.hom.left ≫ (t'.act j).left := fun j =>
    congrArg (fun z => z.left) (hea' j)
  have p₁ : ∀ i, (ob.etaA (bas (Pi.single i 1))).left ≫ e.hom.left = (t.pt i).left := hep
  have p₂ : ∀ i, (ob'.etaA (bas (Pi.single i 1))).left ≫ e'.hom.left = (t'.pt i).left := hep'
  constructor
  · rintro ⟨m⟩
    have mL : LBIso ob'.t.PP.L (ob.t.PP.L.pull m.cm.F) := by
      obtain ⟨w, hw, -⟩ := m.lin
      exact ⟨w, hw⟩
    refine ⟨e'.inv.left ≫ m.cm.F ≫ e.hom.left, ?_, ?_, fun i => ?_, fun j => ?_⟩
    · exact (IsGrpPullback.comp (isGrpPullback_of_iso e'.symm)
        (IsGrpPullback.comp m.cart (isGrpPullback_of_iso e))).congr (by simp) rfl
    · have k₁ : LBIso (ob'.t.PP.L.pull e'.inv.left) (t'.L.pull (𝟙 _)) := PELPull.lbIso_pull heL' e'.inv.left ih'.symm
      have k₂ : LBIso t'.L (ob'.t.PP.L.pull e'.inv.left) :=
        k₁.symm.chartPull (chartPullUnpull t'.L _ rfl) (chartPullId _)
      have k₃ : LBIso ob'.t.PP.L (t.L.pull (m.cm.F ≫ e.hom.left)) :=
        mL.trans ob'.t.PP.isLB (pull_isLB ob.t.PP.isLB _) (pull_isLB t.isLB _) (PELPull.lbIso_pull heL m.cm.F rfl)
      exact k₂.trans t'.isLB (pull_isLB ob'.t.PP.isLB _) (pull_isLB t.isLB _) (PELPull.lbIso_pull k₃ e'.inv.left rfl)
    · have := m.etaA (bas (Pi.single i 1))
      rw [← p₂, ← p₁, Category.assoc, reassoc_of% hi']
      exact (reassoc_of% this) _
    · have h₂ : (t'.act j).left ≫ e'.inv.left = e'.inv.left ≫ (ob'.t.act.act (a j)).left := by
        rw [← Category.id_comp (t'.act j).left, ← ih', Category.assoc, Category.assoc, ← reassoc_of% a₂ j, hi',
          Category.comp_id]
      have h₃ := m.act (a j)
      rw [reassoc_of% h₂, reassoc_of% h₃, a₁, Category.assoc, Category.assoc]
  · rintro ⟨ψ, hψ, hψL, hpt, hact⟩
    have hc : IsGrpPullback ob'.t.G ob.t.G f (e'.hom.left ≫ ψ ≫ e.inv.left) :=
      (IsGrpPullback.comp (isGrpPullback_of_iso e')
        (IsGrpPullback.comp hψ (isGrpPullback_of_iso e.symm))).congr (by simp) rfl
    have kL : LBIso ob'.t.PP.L (ob.t.PP.L.pull (e'.hom.left ≫ ψ ≫ e.inv.left)) := by
      have k₁ : LBIso ob'.t.PP.L (t.L.pull (e'.hom.left ≫ ψ)) :=
        heL'.trans ob'.t.PP.isLB (pull_isLB t'.isLB _) (pull_isLB t.isLB _) (PELPull.lbIso_pull hψL e'.hom.left rfl)
      refine k₁.trans ob'.t.PP.isLB (pull_isLB t.isLB _) (pull_isLB ob.t.PP.isLB _)
        (PELPull.lbIso_pull heL _ ?_).symm
      rw [Category.assoc, Category.assoc, ih, Category.comp_id]
    obtain ⟨m, hm⟩ := GlobalTheory.exists_sabMap_of_isProper_of_lbIso hL.globalFns E H S S' ob.t ob'.t f _ ob.proper hc kL
      (act_of_generators ob.t.act ob'.t.act hc a ha fun j => by
        have h₂ : (t.act j).left ≫ e.inv.left = e.inv.left ≫ (ob.t.act.act (a j)).left := by
          rw [← Category.id_comp (t.act j).left, ← ih, Category.assoc, Category.assoc, ← reassoc_of% a₁ j, hi,
            Category.comp_id]
        rw [reassoc_of% a₂ j, reassoc_of% hact j, h₂, Category.assoc, Category.assoc])
    obtain ⟨q₁, q₂⟩ := levels_of_basis ob ob' hd bas hc fun i => by
      have := hpt i
      rw [reassoc_of% p₂ i]
      refine ((reassoc_of% this) _).trans ?_
      rw [← p₁]
      exact congrArg (f ≫ ·) (by rw [Category.assoc, hi, Category.comp_id])
    rw [← hm] at q₁ q₂
    exact ⟨⟨m, q₁, q₂⟩⟩

end GlobalTheory.UnderMap

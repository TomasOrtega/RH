import Mathlib
import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.IsFramedPointChangedByLetters
import Development.AbelianVarietyTheory.Definitions.RegularCharts.ModelAt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabMapCubical
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AmplePt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabComp
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.CubePullbacks.CubePull
import Formalism.LocalToGlobal.ProjectiveLattices.ThetaFramePf
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.EqOfDominantGeometricPointsOfUnramified
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.IsoEqOfMapsAlongSection
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsPolAVPullbackOfIsLocalRing

set_option synthInstance.maxHeartbeats 400000
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.AutFin

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Frames
open scoped CategoryTheory.Obj

attribute [local instance] Over.cartesianMonoidalCategory

/- English proof (translation)
Use `isClosedImmersion_equalizer_ι_of_isSeparated s h` as an intermediate fact. Establish `hker : (equalizer.ι f g).ker = ⊥`. Apply `le_bot_iff.1` to reduce the goal to its premises. Combine the equalities or inequalities in the displayed calculation. Establish `: IsIso (equalizer.ι f g)` using `IsClosedImmersion.isIso_iff_ker_eq_bot.2 hker`.

Conclude with `(cancel_epi (equalizer.ι f g)).1 (equalizer.condition f g)`.
-/
theorem ext_of_schDom {W X Y Z : Scheme.{0}} {f g : X ⟶ Y} (s : Y ⟶ Z) [IsSeparated s] (h : f ≫ s = g ≫ s)
    (q : W ⟶ X) [IsSchemeTheoreticallyDominant q] (hU : q ≫ f = q ≫ g) : f = g := by
  have := isClosedImmersion_equalizer_ι_of_isSeparated s h
  have hker : (equalizer.ι f g).ker = ⊥ := by
    apply le_bot_iff.1
    calc _ ≤ (equalizer.lift q hU ≫ equalizer.ι f g).ker := Scheme.Hom.le_ker_comp _ _
      _ = ⊥ := by rw [equalizer.lift_ι]; exact q.ker_eq_bot
  have : IsIso (equalizer.ι f g) := IsClosedImmersion.isIso_iff_ker_eq_bot.2 hker
  exact (cancel_epi (equalizer.ι f g)).1 (equalizer.condition f g)

/- English proof (translation)
Establish `: IsDominant (spMap φ)` using `⟨(PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical φ).2 (by`. Rewrite using `[(RingHom.injective_iff_ker_eq_bot φ).1 hφ]`. Conclude with `bot_le)⟩`. Conclude with `IsSchemeTheoreticallyDominant.of_isDominant _`.
-/
theorem schDom_spec_map {A B : Type} [CommRing A] [CommRing B] [IsDomain A] (φ : A →+* B)
    (hφ : Function.Injective φ) : IsSchemeTheoreticallyDominant (spMap φ) := by
  have : IsDominant (spMap φ) :=
    ⟨(PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical φ).2 (by
      rw [(RingHom.injective_iff_ker_eq_bot φ).1 hφ]; exact bot_le)⟩
  exact IsSchemeTheoreticallyDominant.of_isDominant _

/- English proof (translation)
Establish `hsucc : ∀ n : ℕ, (θ ^ (n + 1)).hom = θ.hom ≫ (θ ^ n).hom` using `fun n => by rw [pow_succ]; rfl`. Establish `hQ : ∀ n : ℕ, IsMonHom (θ ^ (n + 1)).hom ∧ ∃ v : LB.Iso P.L (P.L.pull (θ ^ (n + 1)).hom.left), PGen v`. Introduce `n`. Proceed by induction on `n with`. Consider the case `zero => rw [zero_add, pow_one]`.

Conclude with `⟨inferInstance, w, hw⟩`. Consider the case `succ n ih`. Take `⟨h1, v, hv⟩` from `ih`. Rewrite using `[hsucc (n + 1)]`. Take `⟨u, T⟩` from `exists_comp P.isLB v w hv hw P.isLB P.isLB`.

Conclude with `⟨inferInstance, u, T.pgen_comp P.isLB hv hw⟩`. Take `⟨-, -, -, -, hcard⟩` from `hmul (Sp F) P 3 (by norm_num)`. Establish `hc` using `hcard F (𝟙 _) (by norm_num)`. Establish `hfin : Finite {x : Over.mk (𝟙 (Sp F)) ⟶ P.A // x ^ 3 = 1}` using `Nat.finite_of_card_ne_zero (by rw [hc]; positivity)`. Set `f : {x : Over.mk (𝟙 (Sp F)) ⟶ P.A // x ^ 3 = 1} → {x : Over.mk (𝟙 (Sp F)) ⟶ P.A // x ^ 3 = 1}` to `fun x => ⟨x.1 ≫ θ.hom, by rw [← MonObj.pow_comp, x.2, MonObj.one_comp]⟩`.

Establish `finj : Function.Injective f` using `fun a b h => Subtype.ext ((Iso.cancel_iso_hom_right _ _ θ).1 (congrArg Subtype.val h))`. Set `e` to `Equiv.ofBijective f (Finite.injective_iff_bijective.1 finj)`. Establish `he : ∀ (n : ℕ) x, ((e ^ n) x).1 = x.1 ≫ (θ ^ n).hom`. Introduce `n`. Proceed by induction on `n with`.

Consider the case `zero => intro x`. Conclude with `(Category.comp_id _).symm`. Consider the case `succ n ih => intro x`. Rewrite using `[pow_succ e, Equiv.Perm.mul_apply, ih, hsucc, ← Category.assoc]`. Both sides reduce to the same expression.

Establish `hN : 0 < orderOf e` using `orderOf_pos e`. Take `⟨n, hn⟩` from `Nat.exists_eq_succ_of_ne_zero hN.ne'`. Take `⟨h1, v, hv⟩` from `hQ n`. Use `⟨n + 1, n.succ_pos, Iso.ext ?_⟩` and prove the remaining obligations. Establish `hMu : IsUnit ((3 : ℕ) : Γ(Sp F, ⊤))`.

Establish `: IsUnit ((3 : ℕ) : F)` using `IsUnit.mk0 _ (by norm_num)`. Conclude with `map_natCast (Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom 3 ▸ this.map _`. Use `hS (Sp F) P 3 le_rfl (θ ^ (n + 1)) h1 (fun _ => ⟨⊤, trivial, ?_⟩) (fix_torsion_of_fix_geometric_of_isDominant hmul P 3 (by norm_num) hMu (𝟙 _) _ h1 fun y hy => ?_)` and prove the remaining obligations. Take `⟨t, ht⟩` from `gen_of_iso hv (P.A.hom ⁻¹ᵁ ⊤).ι`. Use `gen_chartPull (chartPullOut P.L _ _ _ _ fun n => ?_) t ht` and prove the remaining obligations.

Use `fin_cases n`. Use `exacts [rfl, (Category.comp_id _).symm]`. Use `he (n + 1) ⟨y, hy⟩` as an intermediate fact. Rewrite `this` using `[← Nat.succ_eq_add_one, ← hn, pow_orderOf_eq_one, hn]`. Conclude with `this.symm`.
-/
theorem exists_pow_eq_one_field (hmul : Out.MulNSt) (hS : Out.SerreSt) {F : Type} [Field F] [IsAlgClosed F] [CharZero F]
    (P : Out.PolAV (Sp F)) (θ : Aut P.A) [IsMonHom θ.hom] (w : LB.Iso P.L (P.L.pull θ.hom.left)) (hw : PGen w) :
    ∃ N : ℕ, 0 < N ∧ θ ^ N = 1 := by
  have hsucc : ∀ n : ℕ, (θ ^ (n + 1)).hom = θ.hom ≫ (θ ^ n).hom := fun n => by rw [pow_succ]; rfl
  have hQ : ∀ n : ℕ, IsMonHom (θ ^ (n + 1)).hom ∧ ∃ v : LB.Iso P.L (P.L.pull (θ ^ (n + 1)).hom.left), PGen v := by
    intro n
    induction n with
    | zero => rw [zero_add, pow_one]; exact ⟨inferInstance, w, hw⟩
    | succ n ih =>
      obtain ⟨h1, v, hv⟩ := ih
      rw [hsucc (n + 1)]
      obtain ⟨u, T⟩ := exists_comp P.isLB v w hv hw P.isLB P.isLB
      exact ⟨inferInstance, u, T.pgen_comp P.isLB hv hw⟩
  obtain ⟨-, -, -, -, hcard⟩ := hmul (Sp F) P 3 (by norm_num)
  have hc := hcard F (𝟙 _) (by norm_num)
  have hfin : Finite {x : Over.mk (𝟙 (Sp F)) ⟶ P.A // x ^ 3 = 1} :=
    Nat.finite_of_card_ne_zero (by rw [hc]; positivity)
  let f : {x : Over.mk (𝟙 (Sp F)) ⟶ P.A // x ^ 3 = 1} → {x : Over.mk (𝟙 (Sp F)) ⟶ P.A // x ^ 3 = 1} :=
    fun x => ⟨x.1 ≫ θ.hom, by rw [← MonObj.pow_comp, x.2, MonObj.one_comp]⟩
  have finj : Function.Injective f := fun a b h => Subtype.ext ((Iso.cancel_iso_hom_right _ _ θ).1 (congrArg Subtype.val h))
  let e := Equiv.ofBijective f (Finite.injective_iff_bijective.1 finj)
  have he : ∀ (n : ℕ) x, ((e ^ n) x).1 = x.1 ≫ (θ ^ n).hom := by
    intro n
    induction n with
    | zero => intro x; exact (Category.comp_id _).symm
    | succ n ih => intro x; rw [pow_succ e, Equiv.Perm.mul_apply, ih, hsucc, ← Category.assoc]; rfl
  have hN : 0 < orderOf e := orderOf_pos e
  obtain ⟨n, hn⟩ := Nat.exists_eq_succ_of_ne_zero hN.ne'
  obtain ⟨h1, v, hv⟩ := hQ n
  refine ⟨n + 1, n.succ_pos, Iso.ext ?_⟩
  have hMu : IsUnit ((3 : ℕ) : Γ(Sp F, ⊤)) := by
    have : IsUnit ((3 : ℕ) : F) := IsUnit.mk0 _ (by norm_num)
    exact map_natCast (Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom 3 ▸ this.map _
  refine hS (Sp F) P 3 le_rfl (θ ^ (n + 1)) h1 (fun _ => ⟨⊤, trivial, ?_⟩)
    (fix_torsion_of_fix_geometric_of_isDominant hmul P 3 (by norm_num) hMu (𝟙 _) _ h1 fun y hy => ?_)
  · obtain ⟨t, ht⟩ := gen_of_iso hv (P.A.hom ⁻¹ᵁ ⊤).ι
    refine gen_chartPull (chartPullOut P.L _ _ _ _ fun n => ?_) t ht
    fin_cases n
    exacts [rfl, (Category.comp_id _).symm]
  · have := he (n + 1) ⟨y, hy⟩
    rw [← Nat.succ_eq_add_one, ← hn, pow_orderOf_eq_one, hn] at this
    exact this.symm

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

/- English proof (translation)
Set `F` to `AlgebraicClosure (FractionRing S)`. Set `io : S →+* F` to `(algebraMap (FractionRing S) _).comp (algebraMap S _)`. Establish `hio : Function.Injective io` using `(algebraMap (FractionRing S) _).injective.comp (IsFractionRing.injective S _)`. Establish `: CharZero F` using `(RingHom.charZero_iff hio).1 inferInstance`. Choose the witnesses or unpack the hypotheses as in `⟨tF, ⟨n⟩⟩ : ∃ tF : SAB H (Sp F), Nonempty (SABMap tF t' (spMap io)) := by`.

Take `⟨_, _, _, _, _, n, -⟩` from `sabPull Out.CubePf.cubePull (spMap io) t'`. Conclude with `⟨_, ⟨n⟩⟩`. Take `⟨k, hk⟩` from `sabComp pullCubComp E H _ _ _ _ _ _ _ _ m n`. Take `⟨k', hk'⟩` from `sabComp pullCubComp E H _ _ _ _ _ _ _ _ m' n`. Take `⟨ψ, hψ, hφ, -, -, v, hv, -⟩` from `sabMap_iso k' k rfl rfl`.

Establish `hcomm : ψ.hom.left ≫ n.φ = n.φ ≫ θ.hom.left`. Apply `m.cart.1.hom_ext` to reduce the goal to its premises. Establish `e1 : k.φ = n.φ ≫ m.φ` using `hk`. Establish `e2 : k'.φ = n.φ ≫ m'.φ` using `hk'`. Use `show (ψ.hom.left ≫ n.φ) ≫ m.φ = (n.φ ≫ θ.hom.left) ≫ m.φ`.

Rewrite using `[Category.assoc, ← e1, hφ, e2, Category.assoc, hθ]`. Establish `e : n.φ ≫ t'.G.hom = tF.G.hom ≫ spMap io` using `n.cart.1.w`. Rewrite using `[Category.assoc, Category.assoc, Over.w, e, Over.w_assoc]`. Use `tF.semi.smooth` as an intermediate fact. Use `tF.semi.geomConnected` as an intermediate fact.

Take `⟨w, g, -⟩` from `k.lin`. Take `⟨U, hU, hc, -⟩` from `exists_isAffineOpen_mem_and_subset (X := X) (U := ⊤) (x := (spMap io ≫ x) (IsLocalRing.closedPoint F)) trivial`. Establish `hy : ∀ y, (spMap io ≫ x) y ∈ U` using `fun y => (congrArg (fun V => y ∈ V) (Scheme.preimage_eq_top_of_closedPoint_mem (spMap io ≫ x) hc)).mpr trivial`. Establish `am` using `relAmple_pull k.cart.1 t.PP.isLB tF.PP.isLB ((isGen_iff w).1 g) U hU hy hA`. Establish `kt` using `kTriv_pull k.cart t.PP.isLB tF.PP.isLB ((isGen_iff w).1 g) hK`.

Use `LocalFibre.connectedSpace_sp F` as an intermediate fact. Establish `: ConnectedSpace tF.G.left` using `GeometricallyConnected.connectedSpace tF.G.hom tF.G.hom.isOpenMap`. Take `⟨d, hd⟩` from `exists_dim_of_preconnected tF.G.hom (eSec tF.G (IsLocalRing.closedPoint F))`. Take `⟨-, ws, gs', -⟩` from `tF.sym`. Set `P : Out.PolAV (Sp F)` to `{ A := tF.G, g := d, smoothDim := hd, L := tF.PP.L, isLB := tF.PP.isLB, ample := am, ktriv := kt isAb := ⟨inferInstance, inferInstance, MorphismProperty.of_isPullback (P := @IsProper) k.cart.1 hp, ‹_›⟩ rigid := ⟨tF.PP.rig, tF.PP.rigGen⟩ sym := fun _ => ⟨⊤, trivial, gen_of_iso ((i …`.

Take `⟨N, hN, hψN⟩` from `@exists_pow_eq_one_field hmul hS F _ _ _ P ψ hψ v ((isGen_iff v).1 hv)`. Set `ψ' : Aut tF.G` to `ψ`. Establish `hψN' : ψ' ^ N = 1` using `hψN`. Establish `hit : ∀ a : ℕ, (ψ' ^ a).hom.left ≫ n.φ = n.φ ≫ (θ ^ a).hom.left`. Introduce `a`.

Proceed by induction on `a with`. Consider the case `zero => exact (Category.id_comp _).trans (Category.comp_id _).symm`. Consider the case `succ a ih`. Rewrite using `[pow_succ, pow_succ]`. Use `show (ψ.hom.left ≫ (ψ' ^ a).hom.left) ≫ n.φ = n.φ ≫ θ.hom.left ≫ (θ ^ a).hom.left`.

Rewrite using `[Category.assoc, ih, ← Category.assoc, hcomm, Category.assoc]`. Use `⟨N, hN, Iso.ext (Over.OverMorphism.ext ?_)⟩` and prove the remaining obligations. Use `t'.semi.smooth` as an intermediate fact. Establish `: IsProper t'.G.hom` using `MorphismProperty.of_isPullback (P := @IsProper) m.cart.1 hp`. Establish `: IsSchemeTheoreticallyDominant (spMap io)` using `schDom_spec_map io hio`.

Establish `: IsSchemeTheoreticallyDominant n.φ` using `IsSchemeTheoreticallyDominant.of_isPullback n.cart.1.flip`. Use `ext_of_schDom t'.G.hom ((Over.w _).trans (Over.w _).symm) n.φ ?_` and prove the remaining obligations. Rewrite using `[← hit, hψN']`. Conclude with `(Category.id_comp _).trans (Category.comp_id _).symm`.
-/
theorem exists_pow_eq_one (hmul : Out.MulNSt) (hS : Out.SerreSt) {X : Scheme.{0}} {t : SAB H X} (hp : IsProper t.G.hom)
    (hA : Out.RelAmple t.G t.PP.L) (hK : Out.KTriv t.G t.PP.L) {S : Type} [CommRing S] [IsDomain S] [CharZero S]
    {x : Sp S ⟶ X} {t' : SAB H (Sp S)} (m m' : SABMap t' t x) (θ : Aut t'.G) (hθ : θ.hom.left ≫ m.φ = m'.φ) :
    ∃ N : ℕ, 0 < N ∧ θ ^ N = 1 := by
  let F := AlgebraicClosure (FractionRing S)
  let io : S →+* F := (algebraMap (FractionRing S) _).comp (algebraMap S _)
  have hio : Function.Injective io := (algebraMap (FractionRing S) _).injective.comp (IsFractionRing.injective S _)
  have : CharZero F := (RingHom.charZero_iff hio).1 inferInstance
  obtain ⟨tF, ⟨n⟩⟩ : ∃ tF : SAB H (Sp F), Nonempty (SABMap tF t' (spMap io)) := by
    obtain ⟨_, _, _, _, _, n, -⟩ := sabPull Out.CubePf.cubePull (spMap io) t'
    exact ⟨_, ⟨n⟩⟩
  obtain ⟨k, hk⟩ := sabComp pullCubComp E H _ _ _ _ _ _ _ _ m n
  obtain ⟨k', hk'⟩ := sabComp pullCubComp E H _ _ _ _ _ _ _ _ m' n
  obtain ⟨ψ, hψ, hφ, -, -, v, hv, -⟩ := sabMap_iso k' k rfl rfl
  have hcomm : ψ.hom.left ≫ n.φ = n.φ ≫ θ.hom.left := by
    apply m.cart.1.hom_ext
    · have e1 : k.φ = n.φ ≫ m.φ := hk
      have e2 : k'.φ = n.φ ≫ m'.φ := hk'
      show (ψ.hom.left ≫ n.φ) ≫ m.φ = (n.φ ≫ θ.hom.left) ≫ m.φ
      rw [Category.assoc, ← e1, hφ, e2, Category.assoc, hθ]
    · have e : n.φ ≫ t'.G.hom = tF.G.hom ≫ spMap io := n.cart.1.w
      rw [Category.assoc, Category.assoc, Over.w, e, Over.w_assoc]
  have := tF.semi.smooth
  have := tF.semi.geomConnected
  obtain ⟨w, g, -⟩ := k.lin
  obtain ⟨U, hU, hc, -⟩ := exists_isAffineOpen_mem_and_subset (X := X) (U := ⊤)
    (x := (spMap io ≫ x) (IsLocalRing.closedPoint F)) trivial
  have hy : ∀ y, (spMap io ≫ x) y ∈ U := fun y =>
    (congrArg (fun V => y ∈ V) (Scheme.preimage_eq_top_of_closedPoint_mem (spMap io ≫ x) hc)).mpr trivial
  have am := relAmple_pull k.cart.1 t.PP.isLB tF.PP.isLB ((isGen_iff w).1 g) U hU hy hA
  have kt := kTriv_pull k.cart t.PP.isLB tF.PP.isLB ((isGen_iff w).1 g) hK
  have := LocalFibre.connectedSpace_sp F
  have : ConnectedSpace tF.G.left := GeometricallyConnected.connectedSpace tF.G.hom tF.G.hom.isOpenMap
  obtain ⟨d, hd⟩ := exists_dim_of_preconnected tF.G.hom (eSec tF.G (IsLocalRing.closedPoint F))
  obtain ⟨-, ws, gs', -⟩ := tF.sym
  let P : Out.PolAV (Sp F) :=
    { A := tF.G, g := d, smoothDim := hd, L := tF.PP.L, isLB := tF.PP.isLB, ample := am, ktriv := kt
      isAb := ⟨inferInstance, inferInstance, MorphismProperty.of_isPullback (P := @IsProper) k.cart.1 hp, ‹_›⟩
      rigid := ⟨tF.PP.rig, tF.PP.rigGen⟩
      sym := fun _ => ⟨⊤, trivial, gen_of_iso ((isGen_iff ws).1 gs') _⟩ }
  obtain ⟨N, hN, hψN⟩ := @exists_pow_eq_one_field hmul hS F _ _ _ P ψ hψ v ((isGen_iff v).1 hv)
  let ψ' : Aut tF.G := ψ
  have hψN' : ψ' ^ N = 1 := hψN
  have hit : ∀ a : ℕ, (ψ' ^ a).hom.left ≫ n.φ = n.φ ≫ (θ ^ a).hom.left := by
    intro a
    induction a with
    | zero => exact (Category.id_comp _).trans (Category.comp_id _).symm
    | succ a ih =>
      rw [pow_succ, pow_succ]
      show (ψ.hom.left ≫ (ψ' ^ a).hom.left) ≫ n.φ = n.φ ≫ θ.hom.left ≫ (θ ^ a).hom.left
      rw [Category.assoc, ih, ← Category.assoc, hcomm, Category.assoc]
  refine ⟨N, hN, Iso.ext (Over.OverMorphism.ext ?_)⟩
  have := t'.semi.smooth
  have : IsProper t'.G.hom := MorphismProperty.of_isPullback (P := @IsProper) m.cart.1 hp
  have : IsSchemeTheoreticallyDominant (spMap io) := schDom_spec_map io hio
  have : IsSchemeTheoreticallyDominant n.φ := IsSchemeTheoreticallyDominant.of_isPullback n.cart.1.flip
  refine ext_of_schDom t'.G.hom ((Over.w _).trans (Over.w _).symm) n.φ ?_
  rw [← hit, hψN']
  exact (Category.id_comp _).trans (Category.comp_id _).symm

section Acts

variable {S : Type} [CommRing S] {A : Scheme.{0}} {L : LB A} (p : A ⟶ Sp S) (e : Sp S ⟶ A) (rig : LB.Gen (L.pull e))
  (σ : LB.Sec L)

def Acts (θ : A ⟶ A) (ζ : S) : Prop :=
  ∃ v : LB.Iso L (L.pull θ), PGen v ∧
    PMaps v (K := PUnit) (fun _ => e) (fun _ => e) (fun _ => 1) rig rig (𝟙 _) ∧
    ∀ (Z : Scheme.{0}) (r : Z ⟶ A) (z : Z) (j k : L.ι), θ (r z) ∈ L.U j → r z ∈ L.U k →
      gs (r ≫ θ) z (L.U j) (σ.f j) = (gw v r z j k).val * (cst (r ≫ p) z ζ * gs r z (L.U k) (σ.f k))

variable {p e rig σ}

/- English proof (translation)
Simplify using `only [cst, gs_eq q z ⊤ trivial, map_mul]`.
-/
theorem cst_mul {Z : Scheme.{0}} (q : Z ⟶ Sp S) (z : Z) (a b : S) : cst q z (a * b) = cst q z a * cst q z b := by
  simp only [cst, gs_eq q z ⊤ trivial, map_mul]

/- English proof (translation)
Take `⟨v, g, m, a⟩` from `h`. Take `⟨v', g', m', a'⟩` from `h'`. Take `⟨u, T⟩` from `exists_comp hL v v' g g' hL hL`. Establish `M` using `T.pmaps_comp hL (fun _ => he.trans (Category.id_comp _).symm) m m'`. Rewrite `M` using `[Category.id_comp]`.

Use `⟨u, T.pgen_comp hL g g', M, fun Z r z j k hj hk => ?_⟩` and prove the remaining obligations. Take `⟨i, hi⟩` from `exists_chart hL (θ' (r z))`. Rewrite using `[← Category.assoc, a Z (r ≫ θ') z j i hj hi, a' Z r z i k hi hk, T Z r z j i k hj hi hk, Category.assoc, hp, cst_mul, Units.val_mul]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem Acts.comp (hL : L.IsLB) {θ θ' : A ⟶ A} {ζ ζ' : S} (hp : θ' ≫ p = p) (he : e ≫ θ' = e)
    (h : Acts p e rig σ θ ζ) (h' : Acts p e rig σ θ' ζ') : Acts p e rig σ (θ' ≫ θ) (ζ * ζ') := by
  obtain ⟨v, g, m, a⟩ := h
  obtain ⟨v', g', m', a'⟩ := h'
  obtain ⟨u, T⟩ := exists_comp hL v v' g g' hL hL
  have M := T.pmaps_comp hL (fun _ => he.trans (Category.id_comp _).symm) m m'
  rw [Category.id_comp] at M
  refine ⟨u, T.pgen_comp hL g g', M, fun Z r z j k hj hk => ?_⟩
  obtain ⟨i, hi⟩ := exists_chart hL (θ' (r z))
  rw [← Category.assoc, a Z (r ≫ θ') z j i hj hi, a' Z r z i k hi hk, T Z r z j i k hj hi hk, Category.assoc, hp,
    cst_mul, Units.val_mul]
  ring

/- English proof (translation)
Take `⟨v, g, m, a⟩` from `h`. Take `⟨v', g', m', a'⟩` from `h'`. Choose the witnesses or unpack the hypotheses as in `rfl : v = v' := by`. Use `gen_eq_of_eq_along_section (fun y => ?_) p e hep hp ((isGen_iff v).2 g) ((isGen_iff v').2 g') ?_` and prove the remaining obligations. Take `⟨i, hi⟩` from `exists_chart hL y`.

Take `⟨j, hj⟩` from `exists_chart hL (θ y)`. Conclude with `⟨(fun _ => j, i), mem_pull.2 hj, hi⟩`. Introduce and unpack `s ⟨j, i⟩ ⟨hj, hi⟩`. Establish `k₁` using `m _ (𝟙 _) s j (fun _ => i) (fun _ => mem_pull.1 hj) (fun _ => hi)`. Establish `k₂` using `m' _ (𝟙 _) s j (fun _ => i) (fun _ => mem_pull.1 hj) (fun _ => hi)`.

Establish `k₃` using `mul_right_cancel (k₁.symm.trans k₂)`. Rewrite `k₃` using `[Fintype.prod_unique, Fintype.prod_unique, zpow_one, zpow_one, Category.id_comp]`. Conclude with `k₃`. Use `fn_ext fun y hy => ?_` and prove the remaining obligations. Take `⟨j, hj⟩` from `exists_chart hL (θ y)`.

Rewrite using `[gs_mul _ y _ hy, gs_mul _ y _ hy, gs_constFn _ _ _ y hy, gs_constFn _ _ _ y hy]`. Conclude with `(Units.mul_right_inj _).1 ((a _ (𝟙 _) y j k hj hy).symm.trans (a' _ (𝟙 _) y j k hj hy))`.
-/
theorem Acts.unique (hL : L.IsLB) (hep : e ≫ p = 𝟙 _) (hp : Function.Surjective p.appTop.hom) {θ : A ⟶ A} {ζ ζ' : S}
    (he : e ≫ θ = e) (h : Acts p e rig σ θ ζ) (h' : Acts p e rig σ θ ζ') (k : L.ι) :
    constFn p _ ζ * σ.f k = constFn p _ ζ' * σ.f k := by
  obtain ⟨v, g, m, a⟩ := h
  obtain ⟨v', g', m', a'⟩ := h'
  obtain rfl : v = v' := by
    refine gen_eq_of_eq_along_section (fun y => ?_) p e hep hp ((isGen_iff v).2 g) ((isGen_iff v').2 g') ?_
    · obtain ⟨i, hi⟩ := exists_chart hL y
      obtain ⟨j, hj⟩ := exists_chart hL (θ y)
      exact ⟨(fun _ => j, i), mem_pull.2 hj, hi⟩
    · rintro s ⟨j, i⟩ ⟨hj, hi⟩
      have k₁ := m _ (𝟙 _) s j (fun _ => i) (fun _ => mem_pull.1 hj) (fun _ => hi)
      have k₂ := m' _ (𝟙 _) s j (fun _ => i) (fun _ => mem_pull.1 hj) (fun _ => hi)
      have k₃ := mul_right_cancel (k₁.symm.trans k₂)
      rw [Fintype.prod_unique, Fintype.prod_unique, zpow_one, zpow_one, Category.id_comp] at k₃
      exact k₃
  refine fn_ext fun y hy => ?_
  obtain ⟨j, hj⟩ := exists_chart hL (θ y)
  rw [gs_mul _ y _ hy, gs_mul _ y _ hy, gs_constFn _ _ _ y hy, gs_constFn _ _ _ y hy]
  exact (Units.mul_right_inj _).1 ((a _ (𝟙 _) y j k hj hy).symm.trans (a' _ (𝟙 _) y j k hj hy))

end Acts

variable {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {S : Type} [CommRing S] {x : Sp S ⟶ Xo.X}
  {t' : SAB H (Sp S)}

/- English proof (translation)
Set `a0 : Over.mk (t'.G.hom ≫ x) ⟶ Over.mk x` to `Over.homMk t'.G.hom rfl`. Set `b0 : Over.mk (t'.G.hom ≫ x) ⟶ Xo.univ.t.G` to `Over.homMk m.φ m.cart.1.w`. Set `g0 : t'.G.left ⟶ Gx x` to `(lift a0 b0).left`. Establish `g0f : g0 ≫ (fst (Over.mk x) Xo.univ.t.G).left = t'.G.hom` using `congrArg (fun q => q.left) (lift_fst a0 b0)`. Establish `g0s : g0 ≫ (snd (Over.mk x) Xo.univ.t.G).left = m.φ` using `congrArg (fun q => q.left) (lift_snd a0 b0)`.

Use `⟨g0, g0s, g0f, fun Z r z j k hj hk => ?_⟩` and prove the remaining obligations. Establish `le : (Xo.univ.t.PP.L.pull m.φ).U (fun _ => j) ≤ g0 ⁻¹ᵁ (PPx x).U (fun _ => j)` using `fun y hy => Set.mem_iInter.2 fun _ => (congrArg (fun q => q y ∈ Xo.univ.t.PP.L.U j) g0s).mpr (mem_pull.1 hy)`. Establish `hj' : r z ∈ (Xo.univ.t.PP.L.pull m.φ).U (fun _ => j)` using `mem_pull.2 hj`. Establish `hm : r z ∈ (Xo.univ.t.PP.L.pull m.φ).U (fun _ => j) ⊓ t'.PP.L.U k` using `⟨hj', hk⟩`. Use `(gs_appLE g0 _ _ le r z hj' _).symm.trans ((congrArg (gs r z _) (hs g0 g0s g0f (fun _ => j) le)).symm.trans ?_)` and prove the remaining obligations.

Conclude with `(gs_res r z _ hm _).symm.trans ((congrArg (gs r z _) (hI (fun _ => j) k)).trans ((gs_mul r z _ hm _ _).trans (congrArg₂ (· * ·) (gs_unit r z _ hm _) (gs_res r z _ hm _))))`.
-/
theorem exists_comparison (m : SABMap t' Xo.univ.t x) {w : LB.Iso t'.PP.L (Xo.univ.t.PP.L.pull m.φ)}
    {σ : LB.Sec t'.PP.L} {s1 : LB.Sec (Xo.univ.t.PP.L.pull m.φ)} {s : LB.Sec (PPx x)} (hI : IsoMaps w σ s1)
    (hs : ∀ g : t'.G.left ⟶ Gx x, g ≫ (snd (Over.mk x) Xo.univ.t.G).left = m.φ →
      g ≫ (fst (Over.mk x) Xo.univ.t.G).left = t'.G.hom →
      ∀ j (h : (Xo.univ.t.PP.L.pull m.φ).U j ≤ g ⁻¹ᵁ (PPx x).U (fun _ => j PUnit.unit)),
        s1.f j = (g.appLE _ _ h).hom (s.f (fun _ => j PUnit.unit))) :
    ∃ g : t'.G.left ⟶ Gx x, g ≫ (snd (Over.mk x) Xo.univ.t.G).left = m.φ ∧
      g ≫ (fst (Over.mk x) Xo.univ.t.G).left = t'.G.hom ∧
      ∀ (Z : Scheme.{0}) (r : Z ⟶ t'.G.left) (z : Z) (j : Xo.univ.t.PP.L.ι) (k : t'.PP.L.ι),
        m.φ (r z) ∈ Xo.univ.t.PP.L.U j → r z ∈ t'.PP.L.U k →
        gs (r ≫ g) z ((PPx x).U (fun _ => j)) (s.f (fun _ => j)) = (gw w r z j k).val * gs r z _ (σ.f k) := by
  let a0 : Over.mk (t'.G.hom ≫ x) ⟶ Over.mk x := Over.homMk t'.G.hom rfl
  let b0 : Over.mk (t'.G.hom ≫ x) ⟶ Xo.univ.t.G := Over.homMk m.φ m.cart.1.w
  let g0 : t'.G.left ⟶ Gx x := (lift a0 b0).left
  have g0f : g0 ≫ (fst (Over.mk x) Xo.univ.t.G).left = t'.G.hom := congrArg (fun q => q.left) (lift_fst a0 b0)
  have g0s : g0 ≫ (snd (Over.mk x) Xo.univ.t.G).left = m.φ := congrArg (fun q => q.left) (lift_snd a0 b0)
  refine ⟨g0, g0s, g0f, fun Z r z j k hj hk => ?_⟩
  have le : (Xo.univ.t.PP.L.pull m.φ).U (fun _ => j) ≤ g0 ⁻¹ᵁ (PPx x).U (fun _ => j) := fun y hy =>
    Set.mem_iInter.2 fun _ => (congrArg (fun q => q y ∈ Xo.univ.t.PP.L.U j) g0s).mpr (mem_pull.1 hy)
  have hj' : r z ∈ (Xo.univ.t.PP.L.pull m.φ).U (fun _ => j) := mem_pull.2 hj
  have hm : r z ∈ (Xo.univ.t.PP.L.pull m.φ).U (fun _ => j) ⊓ t'.PP.L.U k := ⟨hj', hk⟩
  refine (gs_appLE g0 _ _ le r z hj' _).symm.trans ((congrArg (gs r z _) (hs g0 g0s g0f (fun _ => j) le)).symm.trans ?_)
  exact (gs_res r z _ hm _).symm.trans ((congrArg (gs r z _) (hI (fun _ => j) k)).trans
    ((gs_mul r z _ hm _ _).trans (congrArg₂ (· * ·) (gs_unit r z _ hm _) (gs_res r z _ hm _))))

/- English proof (translation)
Establish `hL` using `Xo.univ.t.PP.isLB`. Establish `hL'` using `t'.PP.isLB`. Set `A` to `Xo.univ.t.G`. Establish `cond : (snd (Over.mk x) A).left ≫ A.hom = (fst (Over.mk x) A).left ≫ x` using `(Over.w (snd (Over.mk x) A)).trans (Over.w (fst (Over.mk x) A)).symm`. Set `h : Gx x ⟶ t'.G.left` to `m.cart.1.lift _ _ cond`.

Establish `hφ : h ≫ m.φ = (snd (Over.mk x) A).left` using `m.cart.1.lift_fst _ _ cond`. Establish `hh : h ≫ t'.G.hom = (fst (Over.mk x) A).left` using `m.cart.1.lift_snd _ _ cond`. Establish `hg0 : g ≫ h = 𝟙 _` using `m.cart.1.hom_ext (by rw [Category.assoc, hφ, gs', Category.id_comp]) (by rw [Category.assoc, hh, gf, Category.id_comp])`. Establish `h0g : h ≫ g = 𝟙 _`. Apply `pullback.hom_ext` to reduce the goal to its premises.

Rewrite using `[Category.assoc] show h ≫ g ≫ (fst (Over.mk x) A).left = 𝟙 _ ≫ (fst (Over.mk x) A).left`. Rewrite using `[gf, hh, Category.id_comp]`. Rewrite using `[Category.assoc] show h ≫ g ≫ (snd (Over.mk x) A).left = 𝟙 _ ≫ (snd (Over.mk x) A).left`. Rewrite using `[gs', hφ, Category.id_comp]`. Take `⟨t1, ht1⟩` from `thf_secUp hw hL hL' τ`.

Set `t : LB.Sec (PPx x)` to `thfPull1 Xo.univ.t.PP.L h hφ t1`. Establish `ht : ∀ (Z : Scheme.{0}) (r : Z ⟶ Gx x) (z : Z) (j : Xo.univ.t.PP.L.ι) (k : t'.PP.L.ι), r z ∈ (PPx x).U (fun _ => j) → h (r z) ∈ t'.PP.L.U k → gs r z ((PPx x).U (fun _ => j)) (t.f (fun _ => j)) = (gw w (r ≫ h) z j k).val * gs (r ≫ h) z _ (τ.f k)` using `fun Z r z j k hj hk => (gs_appLE h _ _ (chart_le_pullback_open _ h hφ _) r z hj _).trans (ht1 _ (r ≫ h) z (fun _ => j) k (chart_le_pullback_open _ h hφ _ hj) hk)`. Take `⟨a, ha, hu⟩` from `hgen t`. Use `⟨a, fun k => fn_ext fun y hy => ?_, fun a' ha' => hu a' fun (i : Fin 1 → Xo.univ.t.PP.L.ι) => ?_⟩` and prove the remaining obligations. Take `⟨j, hj⟩` from `exists_chart hL (m.φ y)`.

Establish `c2 : (𝟙 _ ≫ g) ≫ h = 𝟙 _` using `by rw [Category.id_comp, hg0]`. Establish `mg : (𝟙 _ ≫ g) y ∈ (PPx x).U (fun _ => j)` using `Set.mem_iInter.2 fun _ => (congrArg (fun q => q y ∈ Xo.univ.t.PP.L.U j) gs').mpr hj`. Establish `e1` using `ht _ (𝟙 _ ≫ g) y j k mg ((congrArg (fun q => q y ∈ t'.PP.L.U k) c2).mpr hy)`. Establish `e2 : gs (𝟙 _ ≫ g) y _ (scal x a (fun _ => j)) = cst (𝟙 _ ≫ t'.G.hom) y a` using `(gs_constFn (fst (Over.mk x) A).left _ _ y mg a).trans (by rw [Category.assoc, gf])`. Rewrite `e1` using `[c2, ha (fun _ => j), gs_mul _ y _ mg, e2, K _ (𝟙 _) y j k hj hy, mul_left_comm]`.

Rewrite using `[gs_mul _ y _ hy, gs_constFn _ _ _ y hy]`. Conclude with `((Units.mul_right_inj _).1 e1).symm`. Take `⟨j, rfl⟩ : ∃ j, i = fun _ => j` from `⟨i 0, funext fun k => congrArg i (Subsingleton.elim k 0)⟩`. Use `fn_ext fun y hy => ?_` and prove the remaining obligations. Establish `mφ : m.φ ((𝟙 _ ≫ h) y) ∈ Xo.univ.t.PP.L.U j` using `(congrArg (fun q => q y ∈ Xo.univ.t.PP.L.U j) (by rw [Category.id_comp, hφ] : (𝟙 _ ≫ h) ≫ m.φ = (snd (Over.mk x) A).left)).mpr (Set.mem_iInter.1 hy 0)`.

Take `⟨k, hk⟩` from `exists_chart hL' ((𝟙 _ ≫ h) y)`. Establish `e1` using `ht _ (𝟙 _) y j k hy hk`. Rewrite `e1` using `[ha' k, gs_mul _ y _ hk, gs_constFn _ _ _ y hk]`. Establish `e2` using `K _ (𝟙 _ ≫ h) y j k mφ hk`. Rewrite `e2` using `[show (𝟙 _ ≫ h) ≫ g = 𝟙 _ by rw [Category.id_comp, h0g]]`.

Establish `e3 : gs (𝟙 _) y _ (scal x a' (fun _ => j)) = cst ((𝟙 _ ≫ h) ≫ t'.G.hom) y a'`. Rewrite using `[show (𝟙 _ ≫ h) ≫ t'.G.hom = 𝟙 _ ≫ (fst (Over.mk x) A).left by rw [Category.assoc, hh]]`. Conclude with `gs_constFn (fst (Over.mk x) A).left _ (𝟙 _) y hy a'`. Conclude with `e1.trans ((mul_left_comm _ _ _).trans (Eq.symm ((gs_mul _ y _ hy _ _).trans (congrArg₂ (· * ·) e3 e2))))`.
-/
theorem gen_of_secGen (m : SABMap t' Xo.univ.t x) {w : LB.Iso t'.PP.L (Xo.univ.t.PP.L.pull m.φ)} (hw : PGen w)
    {σ : LB.Sec t'.PP.L} {s : LB.Sec (PPx x)} (hgen : SecGen x s) {g : t'.G.left ⟶ Gx x}
    (gs' : g ≫ (snd (Over.mk x) Xo.univ.t.G).left = m.φ) (gf : g ≫ (fst (Over.mk x) Xo.univ.t.G).left = t'.G.hom)
    (K : ∀ (Z : Scheme.{0}) (r : Z ⟶ t'.G.left) (z : Z) (j : Xo.univ.t.PP.L.ι) (k : t'.PP.L.ι),
        m.φ (r z) ∈ Xo.univ.t.PP.L.U j → r z ∈ t'.PP.L.U k →
        gs (r ≫ g) z ((PPx x).U (fun _ => j)) (s.f (fun _ => j)) = (gw w r z j k).val * gs r z _ (σ.f k))
    (τ : LB.Sec t'.PP.L) : ∃! a : S, ∀ i, τ.f i = constFn t'.G.hom _ a * σ.f i := by
  have hL := Xo.univ.t.PP.isLB
  have hL' := t'.PP.isLB
  let A := Xo.univ.t.G
  have cond : (snd (Over.mk x) A).left ≫ A.hom = (fst (Over.mk x) A).left ≫ x :=
    (Over.w (snd (Over.mk x) A)).trans (Over.w (fst (Over.mk x) A)).symm
  let h : Gx x ⟶ t'.G.left := m.cart.1.lift _ _ cond
  have hφ : h ≫ m.φ = (snd (Over.mk x) A).left := m.cart.1.lift_fst _ _ cond
  have hh : h ≫ t'.G.hom = (fst (Over.mk x) A).left := m.cart.1.lift_snd _ _ cond
  have hg0 : g ≫ h = 𝟙 _ := m.cart.1.hom_ext (by rw [Category.assoc, hφ, gs', Category.id_comp])
    (by rw [Category.assoc, hh, gf, Category.id_comp])
  have h0g : h ≫ g = 𝟙 _ := by
    apply pullback.hom_ext
    · rw [Category.assoc]
      show h ≫ g ≫ (fst (Over.mk x) A).left = 𝟙 _ ≫ (fst (Over.mk x) A).left
      rw [gf, hh, Category.id_comp]
    · rw [Category.assoc]
      show h ≫ g ≫ (snd (Over.mk x) A).left = 𝟙 _ ≫ (snd (Over.mk x) A).left
      rw [gs', hφ, Category.id_comp]
  obtain ⟨t1, ht1⟩ := thf_secUp hw hL hL' τ
  let t : LB.Sec (PPx x) := thfPull1 Xo.univ.t.PP.L h hφ t1
  have ht : ∀ (Z : Scheme.{0}) (r : Z ⟶ Gx x) (z : Z) (j : Xo.univ.t.PP.L.ι) (k : t'.PP.L.ι),
      r z ∈ (PPx x).U (fun _ => j) → h (r z) ∈ t'.PP.L.U k →
      gs r z ((PPx x).U (fun _ => j)) (t.f (fun _ => j)) = (gw w (r ≫ h) z j k).val * gs (r ≫ h) z _ (τ.f k) :=
    fun Z r z j k hj hk => (gs_appLE h _ _ (chart_le_pullback_open _ h hφ _) r z hj _).trans
      (ht1 _ (r ≫ h) z (fun _ => j) k (chart_le_pullback_open _ h hφ _ hj) hk)
  obtain ⟨a, ha, hu⟩ := hgen t
  refine ⟨a, fun k => fn_ext fun y hy => ?_, fun a' ha' => hu a' fun (i : Fin 1 → Xo.univ.t.PP.L.ι) => ?_⟩
  · obtain ⟨j, hj⟩ := exists_chart hL (m.φ y)
    have c2 : (𝟙 _ ≫ g) ≫ h = 𝟙 _ := by rw [Category.id_comp, hg0]
    have mg : (𝟙 _ ≫ g) y ∈ (PPx x).U (fun _ => j) :=
      Set.mem_iInter.2 fun _ => (congrArg (fun q => q y ∈ Xo.univ.t.PP.L.U j) gs').mpr hj
    have e1 := ht _ (𝟙 _ ≫ g) y j k mg ((congrArg (fun q => q y ∈ t'.PP.L.U k) c2).mpr hy)
    have e2 : gs (𝟙 _ ≫ g) y _ (scal x a (fun _ => j)) = cst (𝟙 _ ≫ t'.G.hom) y a :=
      (gs_constFn (fst (Over.mk x) A).left _ _ y mg a).trans (by rw [Category.assoc, gf])
    rw [c2, ha (fun _ => j), gs_mul _ y _ mg, e2, K _ (𝟙 _) y j k hj hy, mul_left_comm] at e1
    rw [gs_mul _ y _ hy, gs_constFn _ _ _ y hy]
    exact ((Units.mul_right_inj _).1 e1).symm
  · obtain ⟨j, rfl⟩ : ∃ j, i = fun _ => j := ⟨i 0, funext fun k => congrArg i (Subsingleton.elim k 0)⟩
    refine fn_ext fun y hy => ?_
    have mφ : m.φ ((𝟙 _ ≫ h) y) ∈ Xo.univ.t.PP.L.U j :=
      (congrArg (fun q => q y ∈ Xo.univ.t.PP.L.U j)
        (by rw [Category.id_comp, hφ] : (𝟙 _ ≫ h) ≫ m.φ = (snd (Over.mk x) A).left)).mpr (Set.mem_iInter.1 hy 0)
    obtain ⟨k, hk⟩ := exists_chart hL' ((𝟙 _ ≫ h) y)
    have e1 := ht _ (𝟙 _) y j k hy hk
    rw [ha' k, gs_mul _ y _ hk, gs_constFn _ _ _ y hk] at e1
    have e2 := K _ (𝟙 _ ≫ h) y j k mφ hk
    rw [show (𝟙 _ ≫ h) ≫ g = 𝟙 _ by rw [Category.id_comp, h0g]] at e2
    have e3 : gs (𝟙 _) y _ (scal x a' (fun _ => j)) = cst ((𝟙 _ ≫ h) ≫ t'.G.hom) y a' := by
      rw [show (𝟙 _ ≫ h) ≫ t'.G.hom = 𝟙 _ ≫ (fst (Over.mk x) A).left by rw [Category.assoc, hh]]
      exact gs_constFn (fst (Over.mk x) A).left _ (𝟙 _) y hy a'
    exact e1.trans ((mul_left_comm _ _ _).trans (Eq.symm ((gs_mul _ y _ hy _ _).trans (congrArg₂ (· * ·) e3 e2))))

/- English proof (translation)
The claim follows from `and_congr (isGen_iff w) (maps_iff w _ (fun _ => eSec t.G) _ t₁.PP.rig t.PP.rig m.cm.e _ (rigPull_le m.cm.F m.cm.e m.cm.e_comm t.PP.L) (fun _ => rfl))`.
-/
theorem rigIso_iff {X Y : Scheme.{0}} {t₁ : SAB H Y} {t : SAB H X} {f : Y ⟶ X} (m : SABMap t₁ t f)
    (w : LB.Iso t₁.PP.L (t.PP.L.pull m.φ)) : RigIso m w ↔ PGen w ∧
      PMaps w (K := PUnit) (fun _ => eSec t₁.G) (fun _ => eSec t.G) (fun _ => 1) t₁.PP.rig t.PP.rig m.cm.e :=
  and_congr (isGen_iff w)
    (maps_iff w _ (fun _ => eSec t.G) _ t₁.PP.rig t.PP.rig m.cm.e _ (rigPull_le m.cm.F m.cm.e m.cm.e_comm t.PP.L)
      (fun _ => rfl))

/- English proof (translation)
Substitute `hθ hb` using the available equality. Take `⟨v, T⟩` from `exists_cancel hM w w' hw hw' hL hL`. Use `⟨v, T.pgen_cancel hM hw hw', T.pmaps_cancel hM (fun _ => he.trans (Category.id_comp _).symm) r₁ (by rwa [Category.id_comp]), fun Z r z i k hi hk => ?_⟩` and prove the remaining obligations. Take `⟨j, hj⟩` from `exists_chart hM (φ (θ (r z)))`. Establish `e1` using `K Z (r ≫ θ) z j i hj hi`.

Establish `e2` using `K' Z r z j k hj hk`. Rewrite `e2` using `[← Category.assoc, e1, T Z r z j i k hj hi hk, hζ k, gs_mul _ z _ hk, gs_constFn _ _ _ z hk, Units.val_mul, _root_.mul_assoc]`. Conclude with `(Units.mul_right_inj _).1 e2`.
-/
theorem acts_of_cancel {A G B Y : Scheme.{0}} {L : LB A} {M : LB G} (hL : L.IsLB) (hM : M.IsLB) {p : A ⟶ Sp S}
    {e : Sp S ⟶ A} {rig : LB.Gen (L.pull e)} {e₀ : B ⟶ G} {rig₀ : LB.Gen (M.pull e₀)} {b b' : Sp S ⟶ B} (hb : b' = b)
    {φ φ' : A ⟶ G} {θ : A ⟶ A} (hθ : θ ≫ φ = φ') (he : e ≫ θ = e)
    {w : LB.Iso L (M.pull φ)} {w' : LB.Iso L (M.pull φ')} (hw : PGen w) (hw' : PGen w')
    (r₁ : PMaps w (K := PUnit) (fun _ => e) (fun _ => e₀) (fun _ => 1) rig rig₀ b)
    (r₂ : PMaps w' (K := PUnit) (fun _ => e) (fun _ => e₀) (fun _ => 1) rig rig₀ b')
    {σ σ' : LB.Sec L} {ζ : S} (hζ : ∀ i, σ'.f i = constFn p _ ζ * σ.f i) {g : A ⟶ Y} {V : M.ι → Y.Opens}
    {s : ∀ j, Γ(Y, V j)}
    (K : ∀ (Z : Scheme.{0}) (r : Z ⟶ A) (z : Z) (j : M.ι) (k : L.ι), φ (r z) ∈ M.U j → r z ∈ L.U k →
      gs (r ≫ g) z (V j) (s j) = (gw w r z j k).val * gs r z _ (σ.f k))
    (K' : ∀ (Z : Scheme.{0}) (r : Z ⟶ A) (z : Z) (j : M.ι) (k : L.ι), φ' (r z) ∈ M.U j → r z ∈ L.U k →
      gs (r ≫ θ ≫ g) z (V j) (s j) = (gw w' r z j k).val * gs r z _ (σ'.f k)) :
    Acts p e rig σ θ ζ := by
  subst hθ hb
  obtain ⟨v, T⟩ := exists_cancel hM w w' hw hw' hL hL
  refine ⟨v, T.pgen_cancel hM hw hw', T.pmaps_cancel hM (fun _ => he.trans (Category.id_comp _).symm) r₁
    (by rwa [Category.id_comp]), fun Z r z i k hi hk => ?_⟩
  obtain ⟨j, hj⟩ := exists_chart hM (φ (θ (r z)))
  have e1 := K Z (r ≫ θ) z j i hj hi
  have e2 := K' Z r z j k hj hk
  rw [← Category.assoc, e1, T Z r z j i k hj hi hk, hζ k, gs_mul _ z _ hk, gs_constFn _ _ _ z hk, Units.val_mul,
    _root_.mul_assoc] at e2
  exact (Units.mul_right_inj _).1 e2

end GlobalTheory.AutFin

namespace GlobalTheory

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.L2.Pj.QAt GlobalTheory.ArcQ GlobalTheory.Frames

/- English proof (translation)
Introduce `h₁ _ E _ _ _ H Dw l Xo _ S _ _ _ _ t' x m m' w w' σ σ' s1 s1' s hgen hw hw' hI hI' hs hs'`. Take `⟨g, gs₁, gf₁, K⟩` from `AutFin.exists_comparison m hI hs`. Take `⟨g', gs₂, gf₂, K'⟩` from `AutFin.exists_comparison m' hI' hs'`. Take `⟨pw, rw₁⟩` from `(AutFin.rigIso_iff m w).1 hw`. Take `⟨pw', rw₂⟩` from `(AutFin.rigIso_iff m' w').1 hw'`.

Establish `G` using `AutFin.gen_of_secGen m pw hgen gs₁ gf₁ K`. Establish `G'` using `AutFin.gen_of_secGen m' pw' hgen gs₂ gf₂ K'`. Take `⟨ψ, hψ, hφ, -⟩` from `sabMap_iso m' m rfl rfl`. Set `θ : Aut t'.G` to `ψ`. Take `⟨N, hN, hθN⟩` from `AutFin.exists_pow_eq_one h₁.mulN h₁.serre Xo.univ.proper Xo.univ.ample Xo.univ.ktriv m m' θ hφ`.

Take `⟨ζ, hζ, -⟩` from `G σ'`. Establish `hgg : g' = θ.hom.left ≫ g`. Apply `pullback.hom_ext` to reduce the goal to its premises. Rewrite using `[Category.assoc]`. Conclude with `gf₂.trans ((Over.w θ.hom).symm.trans (congrArg (θ.hom.left ≫ ·) gf₁.symm))`.

Rewrite using `[Category.assoc]`. Conclude with `gs₂.trans (hφ.symm.trans (congrArg (θ.hom.left ≫ ·) gs₁.symm))`. Substitute `hgg` using the available equality. Establish `he : eSec t'.G ≫ θ.hom.left = eSec t'.G` using `congrArg (fun q => q.left) (IsMonHom.one_hom ψ.hom)`. Establish `hL` using `t'.PP.isLB`.

Establish `act₁ : AutFin.Acts t'.G.hom (eSec t'.G) t'.PP.rig σ θ.hom.left ζ` using `AutFin.acts_of_cancel hL Xo.univ.t.PP.isLB (m'.base.trans m.base.symm) hφ he pw pw' rw₁ rw₂ hζ K K'`. Establish `actn : ∀ n : ℕ, AutFin.Acts t'.G.hom (eSec t'.G) t'.PP.rig σ (θ ^ (n + 1)).hom.left (ζ ^ (n + 1))`. Introduce `n`. Proceed by induction on `n with`. Consider the case `zero => rwa [zero_add, pow_one, pow_one]`.

Consider the case `succ n ih`. Rewrite using `[pow_succ θ (n + 1), pow_succ ζ (n + 1)]`. Conclude with `ih.comp hL (Over.w θ.hom) he act₁`. Establish `actN` using `actn N`. Rewrite `actN` using `[pow_succ θ, hθN, one_mul]`.

Use `t'.semi.smooth` as an intermediate fact. Use `t'.semi.geomConnected` as an intermediate fact. Establish `hab : IsAbelianScheme t'.G` using `⟨inferInstance, inferInstance, MorphismProperty.of_isPullback (P := @IsProper) m.cart.1 Xo.univ.proper, ‹_›⟩`. Establish `key` using `AutFin.Acts.unique hL (Over.w (MonObj.one (X := t'.G))) (h₁.globalFns _ _ hab).2 he act₁ actN`. Establish `hpow : ζ = ζ ^ (N + 1)` using `(G σ').unique hζ fun i => (hζ i).trans (key i)`.

Establish `hne : ζ ≠ 0`. Introduce and unpack `rfl`. Take `⟨a, ha, -⟩` from `G' σ`. Establish `h0 : ∀ U, constFn t'.G.hom U (0 : S) = 0` using `fun U => by simp [constFn]`. Establish `h1 : ∀ U, constFn t'.G.hom U (1 : S) = 1` using `fun U => by simp [constFn]`.

Use `zero_ne_one ((G σ).unique (fun i => ?_) fun i => ?_)` and prove the remaining obligations. Rewrite using `[h0, zero_mul, ha i, hζ i, h0, zero_mul, mul_zero]`. Rewrite using `[h1, one_mul]`. Use `⟨ζ, N, hN, mul_right_cancel₀ hne ?_, hζ⟩` and prove the remaining obligations. Rewrite using `[← pow_succ, one_mul]`.

Conclude with `hpow.symm`.
-/
theorem theta_generator_eq_rootOfUnity_mul : Out.Laws → Out.Laws2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (S : Type) [CommRing S] [IsDomain S] [CharZero S] [Algebra ℚ S] (t' : SAB H (Sp S)) (x : Sp S ⟶ Xo.X) (m m' : SABMap t' Xo.univ.t x) (w : LB.Iso t'.PP.L (Xo.univ.t.PP.L.pull m.φ)) (w' : LB.Iso t'.PP.L (Xo.univ.t.PP.L.pull m'.φ)) (σ σ' : LB.Sec t'.PP.L) (s1 : LB.Sec (Xo.univ.t.PP.L.pull m.φ)) (s1' : LB.Sec (Xo.univ.t.PP.L.pull m'.φ)) (s : LB.Sec (PPx x)), SecGen x s → RigIso m w → RigIso m' w' → IsoMaps w σ s1 → IsoMaps w' σ' s1' → (∀ g : t'.G.left ⟶ Gx x, g ≫ (CartesianMonoidalCategory.snd (Over.mk x) Xo.univ.t.G).left = m.φ → g ≫ (CartesianMonoidalCategory.fst (Over.mk x) Xo.univ.t.G).left = t'.G.hom → ∀ j (h : (Xo.univ.t.PP.L.pull m.φ).U j ≤ g ⁻¹ᵁ (PPx x).U (fun _ => j PUnit.unit)), s1.f j = (g.appLE _ _ h).hom (s.f (fun _ => j PUnit.unit))) → (∀ g : t'.G.left ⟶ Gx x, g ≫ (CartesianMonoidalCategory.snd (Over.mk x) Xo.univ.t.G).left = m'.φ → g ≫ (CartesianMonoidalCategory.fst (Over.mk x) Xo.univ.t.G).left = t'.G.hom → ∀ j (h : (Xo.univ.t.PP.L.pull m'.φ).U j ≤ g ⁻¹ᵁ (PPx x).U (fun _ => j PUnit.unit)), s1'.f j = (g.appLE _ _ h).hom (s.f (fun _ => j PUnit.unit))) → ∃ (ζ : S) (N : ℕ), 0 < N ∧ ζ ^ N = 1 ∧ ∀ i, σ'.f i = constFn t'.G.hom _ ζ * σ.f i := by
  intro h₁ _ E _ _ _ H Dw l Xo _ S _ _ _ _ t' x m m' w w' σ σ' s1 s1' s hgen hw hw' hI hI' hs hs'
  obtain ⟨g, gs₁, gf₁, K⟩ := AutFin.exists_comparison m hI hs
  obtain ⟨g', gs₂, gf₂, K'⟩ := AutFin.exists_comparison m' hI' hs'
  obtain ⟨pw, rw₁⟩ := (AutFin.rigIso_iff m w).1 hw
  obtain ⟨pw', rw₂⟩ := (AutFin.rigIso_iff m' w').1 hw'
  have G := AutFin.gen_of_secGen m pw hgen gs₁ gf₁ K
  have G' := AutFin.gen_of_secGen m' pw' hgen gs₂ gf₂ K'
  obtain ⟨ψ, hψ, hφ, -⟩ := sabMap_iso m' m rfl rfl
  let θ : Aut t'.G := ψ
  obtain ⟨N, hN, hθN⟩ := AutFin.exists_pow_eq_one h₁.mulN h₁.serre Xo.univ.proper Xo.univ.ample Xo.univ.ktriv m m' θ hφ
  obtain ⟨ζ, hζ, -⟩ := G σ'
  have hgg : g' = θ.hom.left ≫ g := by
    apply pullback.hom_ext
    · rw [Category.assoc]
      exact gf₂.trans ((Over.w θ.hom).symm.trans (congrArg (θ.hom.left ≫ ·) gf₁.symm))
    · rw [Category.assoc]
      exact gs₂.trans (hφ.symm.trans (congrArg (θ.hom.left ≫ ·) gs₁.symm))
  subst hgg
  have he : eSec t'.G ≫ θ.hom.left = eSec t'.G := congrArg (fun q => q.left) (IsMonHom.one_hom ψ.hom)
  have hL := t'.PP.isLB
  have act₁ : AutFin.Acts t'.G.hom (eSec t'.G) t'.PP.rig σ θ.hom.left ζ :=
    AutFin.acts_of_cancel hL Xo.univ.t.PP.isLB (m'.base.trans m.base.symm) hφ he pw pw' rw₁ rw₂ hζ K K'
  have actn : ∀ n : ℕ, AutFin.Acts t'.G.hom (eSec t'.G) t'.PP.rig σ (θ ^ (n + 1)).hom.left (ζ ^ (n + 1)) := by
    intro n
    induction n with
    | zero => rwa [zero_add, pow_one, pow_one]
    | succ n ih =>
      rw [pow_succ θ (n + 1), pow_succ ζ (n + 1)]
      exact ih.comp hL (Over.w θ.hom) he act₁
  have actN := actn N
  rw [pow_succ θ, hθN, one_mul] at actN
  have := t'.semi.smooth
  have := t'.semi.geomConnected
  have hab : IsAbelianScheme t'.G :=
    ⟨inferInstance, inferInstance, MorphismProperty.of_isPullback (P := @IsProper) m.cart.1 Xo.univ.proper, ‹_›⟩
  have key := AutFin.Acts.unique hL (Over.w (MonObj.one (X := t'.G))) (h₁.globalFns _ _ hab).2 he act₁ actN
  have hpow : ζ = ζ ^ (N + 1) := (G σ').unique hζ fun i => (hζ i).trans (key i)
  have hne : ζ ≠ 0 := by
    rintro rfl
    obtain ⟨a, ha, -⟩ := G' σ
    have h0 : ∀ U, constFn t'.G.hom U (0 : S) = 0 := fun U => by simp [constFn]
    have h1 : ∀ U, constFn t'.G.hom U (1 : S) = 1 := fun U => by simp [constFn]
    refine zero_ne_one ((G σ).unique (fun i => ?_) fun i => ?_)
    · rw [h0, zero_mul, ha i, hζ i, h0, zero_mul, mul_zero]
    · rw [h1, one_mul]
  refine ⟨ζ, N, hN, mul_right_cancel₀ hne ?_, hζ⟩
  rw [← pow_succ, one_mul]
  exact hpow.symm

end GlobalTheory

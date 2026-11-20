import Mathlib
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.TopLeAlgOverHom

set_option autoImplicit false
noncomputable section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF GlobalTheory.CubeFib
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.AddCurve

namespace GlobalTheory.StalkJet

variable {k : Type} [Field k]

/- English proof (translation)
Use `haveI : Nontrivial A := (aug : A →+* k).domain_nontrivial`. Establish `nil : ∀ a : A, aug a = 0 → IsNilpotent a` using `fun a ha => ⟨n, by rw [← Ideal.mem_bot, ← h]; exact Ideal.pow_mem_pow ha n⟩`. Use `IsLocalRing.of_isUnit_or_isUnit_one_sub_self fun a => ?_` and prove the remaining obligations. Distinguish the cases in `ha : aug a = 0`. Conclude with `Or.inr (nil a ha).isUnit_one_sub`.

Use `left`. Establish `h1 : IsNilpotent (a - algebraMap k A (aug a))` using `nil _ (by simp)`. Establish `h2 : IsUnit (algebraMap k A (aug a))` using `(IsUnit.mk0 _ ha).map _`. Use `h1.isUnit_add_right_of_commute h2 (Commute.all _ _)` as an intermediate fact. Simplify using `using this`.
-/
theorem isLocalRing_of_aug {A : Type} [CommRing A] [Algebra k A] (aug : A →ₐ[k] k) {n : ℕ}
    (h : RingHom.ker aug ^ n = ⊥) : IsLocalRing A := by
  haveI : Nontrivial A := (aug : A →+* k).domain_nontrivial
  have nil : ∀ a : A, aug a = 0 → IsNilpotent a := fun a ha =>
    ⟨n, by rw [← Ideal.mem_bot, ← h]; exact Ideal.pow_mem_pow ha n⟩
  refine IsLocalRing.of_isUnit_or_isUnit_one_sub_self fun a => ?_
  by_cases ha : aug a = 0
  · exact Or.inr (nil a ha).isUnit_one_sub
  · left
    have h1 : IsNilpotent (a - algebraMap k A (aug a)) := nil _ (by simp)
    have h2 : IsUnit (algebraMap k A (aug a)) := (IsUnit.mk0 _ ha).map _
    have := h1.isUnit_add_right_of_commute h2 (Commute.all _ _)
    simpa using this

/- English proof (translation)
Substitute `hy` using the available equality. Establish `e` using `Scheme.Spec_stalkClosedPointTo_fromSpecStalk (R := .of A) y.left`. Establish `w : y.left ≫ B.hom = spMap (algebraMap k A)` using `Over.w y`. Establish `e2 : CommRingCat.ofHom (algebraMap k (B.left.presheaf.stalk (y.left (closedPoint A)))) ≫ Scheme.stalkClosedPointTo (R` using `.of A) y.left = CommRingCat.ofHom (algebraMap k A) := by`. Apply `Spec.map_injective` to reduce the goal to its premises.

Rewrite using `[Spec.map_comp]`. Use `Eq.trans ?_ w` and prove the remaining obligations. Conclude with `(congrArg (Spec.map (Scheme.stalkClosedPointTo (R := .of A) y.left) ≫ ·) hb.symm).trans ((Category.assoc _ _ _).symm.trans (congrArg (· ≫ B.hom) e))`. Use `⟨⟨(Scheme.stalkClosedPointTo (R := .of A) y.left).hom, fun c => ?_⟩, ?_, e⟩` and prove the remaining obligations. Conclude with `congrArg (fun q => q.hom c) e2`.

Conclude with `⟨(Scheme.isLocalHom_stalkClosedPointTo' (R := A) y.left).1⟩`.
-/
theorem exists_factor {B : Over (Sp k)} (b : B.left) [Algebra k (B.left.presheaf.stalk b)]
    (hb : B.left.fromSpecStalk b ≫ B.hom = spMap (algebraMap k (B.left.presheaf.stalk b)))
    {A : Type} [CommRing A] [Algebra k A] [IsLocalRing A] (y : algOver k A ⟶ B)
    (hy : y.left (closedPoint A) = b) :
    ∃ τ : B.left.presheaf.stalk b →ₐ[k] A, IsLocalHom τ ∧
      spMap (τ : B.left.presheaf.stalk b →+* A) ≫ B.left.fromSpecStalk b = y.left := by
  subst hy
  have e := Scheme.Spec_stalkClosedPointTo_fromSpecStalk (R := .of A) y.left
  have w : y.left ≫ B.hom = spMap (algebraMap k A) := Over.w y
  have e2 : CommRingCat.ofHom (algebraMap k (B.left.presheaf.stalk (y.left (closedPoint A)))) ≫
      Scheme.stalkClosedPointTo (R := .of A) y.left = CommRingCat.ofHom (algebraMap k A) := by
    apply Spec.map_injective
    rw [Spec.map_comp]
    refine Eq.trans ?_ w
    exact (congrArg (Spec.map (Scheme.stalkClosedPointTo (R := .of A) y.left) ≫ ·) hb.symm).trans
      ((Category.assoc _ _ _).symm.trans (congrArg (· ≫ B.hom) e))
  refine ⟨⟨(Scheme.stalkClosedPointTo (R := .of A) y.left).hom, fun c => ?_⟩, ?_, e⟩
  · exact congrArg (fun q => q.hom c) e2
  · exact ⟨(Scheme.isLocalHom_stalkClosedPointTo' (R := A) y.left).1⟩

/- English proof (translation)
Establish `canc : ∀ {A : Type} [CommRing A] [Algebra k A] (f f' : O →ₐ[k] A), algOverHom f ≫ s = algOverHom f' ≫ s → f = f'`. Introduce `A _ _ f f' h`. Establish `h1 : (algOverHom f).left ≫ s.left = (algOverHom f').left ≫ s.left` using `congrArg (·.left) h`. Establish `h2 : spMap (f : O →+* A) = spMap (f' : O →+* A)` using `(cancel_mono s.left).1 h1`. Establish `h3` using `Spec.map_injective h2`.

Use extensionality with `a`. Conclude with `congrArg (fun q => q.hom a) h3`. Set `aJ : JetR k κ m →ₐ[k] k` to `Chart.jetAug k κ m`. Establish `hJ : RingHom.ker aJ ^ (m + 1) = ⊥` using `Chart.ker_jetAug_pow κ m`. Establish `hxa : algOverHom aJ ≫ x = 1`.

Establish `: aJ = (Chart.jetAug k κ 0).comp (jetZeroR k κ m)` using `GlobalTheory.ChartUniv.jetAug_eq κ m`. Rewrite using `[this, ← algOverHom_comp, Category.assoc, h0, MonObj.comp_one]`. Establish `haug : aJ.comp τ = ε` using `canc _ _ (by rw [← algOverHom_comp, Category.assoc, hτ, hxa, hε])`. Use `set I : Ideal O := RingHom.ker ε ^ (m + 1) with hI`. Establish `hkill : ∀ a ∈ I, τ a = 0`.

Introduce `a ha`. Establish `hle : RingHom.ker ε ≤ (RingHom.ker aJ).comap τ` using `fun c hc => by show aJ (τ c) = 0`. Rewrite using `[← AlgHom.comp_apply, haug]`. Conclude with `hc`. Establish `h2` using `Ideal.le_comap_pow τ (m + 1) (Ideal.pow_right_mono hle (m + 1) ha)`.

Rewrite `h2` using `[hJ]`. Simplify using `using h2`. Establish `hε0 : ∀ a ∈ I, ε a = 0` using `fun a ha => Ideal.pow_le_self (Nat.succ_ne_zero m) ha`. Set `aA : (O ⧸ I) →ₐ[k] k` to `Ideal.Quotient.liftₐ I ε hε0`. Establish `haA : aA.comp (Ideal.Quotient.mkₐ k I) = ε` using `by ext a; rfl`.

Establish `hA : RingHom.ker aA ^ (m + 1) = ⊥`. Establish `hle : RingHom.ker aA ≤ (RingHom.ker ε).map (Ideal.Quotient.mk I)`. Introduce `c hc`. Take `⟨a, rfl⟩` from `Ideal.Quotient.mk_surjective c`. Conclude with `Ideal.mem_map_of_mem _ hc`.

Rewrite using `[← le_bot_iff]`. Use `(Ideal.pow_right_mono hle _).trans ?_` and prove the remaining obligations. Rewrite using `[← Ideal.map_pow, ← hI, Ideal.map_quotient_self]`. Take `⟨ψ, ⟨h1, h2⟩, -⟩` from `GlobalTheory.ChartUniv.univ_all (G := B) x h0 hu (O ⧸ I) aA hA (algOverHom (Ideal.Quotient.mkₐ k I) ≫ s) (by show algOverHom aA ≫ algOverHom (Ideal.Quotient.mkₐ k I) ≫ s = 1`. Rewrite using `[← Category.assoc, algOverHom_comp, haA, hε])`.

Establish `h1' : aA.comp ψ = aJ` using `h1`. Establish `h2' : algOverHom (Ideal.Quotient.mkₐ k I) ≫ s = algOverHom ψ ≫ x` using `h2`. Establish `hψτ : ψ.comp τ = Ideal.Quotient.mkₐ k I` using `canc _ _ (by rw [← algOverHom_comp, Category.assoc, hτ, h2'])`. Set `τ' : (O ⧸ I) →ₐ[k] JetR k κ m` to `Ideal.Quotient.liftₐ I τ hkill`. Establish `hτ' : τ'.comp (Ideal.Quotient.mkₐ k I) = τ` using `by ext a; rfl`.

Establish `haτ' : aJ.comp τ' = aA`. Use `Ideal.Quotient.algHom_ext k ?_` and prove the remaining obligations. Rewrite using `[AlgHom.comp_assoc, hτ', haug, haA]`. Establish `hid : τ'.comp ψ = AlgHom.id k _`. Use `(GlobalTheory.ChartUniv.univ_all (G := B) x h0 hu (JetR k κ m) aJ hJ x hxa).unique ⟨?_, ?_⟩ ⟨rfl, ?_⟩` and prove the remaining obligations.

Use `show aJ.comp (τ'.comp ψ) = aJ`. Rewrite using `[← AlgHom.comp_assoc, haτ', h1']`. Use `show x = algOverHom (τ'.comp ψ) ≫ x`. Rewrite using `[← algOverHom_comp, Category.assoc, ← h2', ← Category.assoc, algOverHom_comp, hτ', hτ]`. Use `show x = algOverHom (AlgHom.id k _) ≫ x`.

Rewrite using `[algOverHom_id, Category.id_comp]`. Use `⟨fun c => ?_, fun a => ⟨fun ha => ?_, hkill a⟩⟩` and prove the remaining obligations. Take `⟨a, ha⟩` from `Ideal.Quotient.mk_surjective (ψ c)`. Use `⟨a, ?_⟩` and prove the remaining obligations. Use `AlgHom.congr_fun hid c` as an intermediate fact.

Rewrite `this` using `[AlgHom.comp_apply, ← ha]`. Conclude with `this`. Use `AlgHom.congr_fun hψτ a` as an intermediate fact. Rewrite `this` using `[AlgHom.comp_apply, ha, map_zero]`. Conclude with `Ideal.Quotient.eq_zero_iff_mem.1 this.symm`.
-/
theorem jet_of_mono {B : Over (Sp k)} [GrpObj B] [Smooth B.hom] {κ : Type} {m : ℕ}
    (x : algOver k (JetR k κ m) ⟶ B) (h0 : algOverHom (jetZeroR k κ m) ≫ x = 1)
    (hu : ∀ (κ' : Type) (y : algOver k (JetR k κ' m) ⟶ B), algOverHom (jetZeroR k κ' m) ≫ y = 1 →
      ∃! ψ : JetR k κ m →ₐ[k] JetR k κ' m, (∀ j, jetZeroR k κ' m (ψ (zR m j)) = 0) ∧ y = algOverHom ψ ≫ x)
    {O : Type} [CommRing O] [Algebra k O] (s : algOver k O ⟶ B) [Mono s.left]
    (ε : O →ₐ[k] k) (hε : algOverHom ε ≫ s = 1) (τ : O →ₐ[k] JetR k κ m) (hτ : algOverHom τ ≫ s = x) :
    Function.Surjective τ ∧ ∀ a, τ a = 0 ↔ a ∈ RingHom.ker ε ^ (m + 1) := by
  have canc : ∀ {A : Type} [CommRing A] [Algebra k A] (f f' : O →ₐ[k] A),
      algOverHom f ≫ s = algOverHom f' ≫ s → f = f' := by
    intro A _ _ f f' h
    have h1 : (algOverHom f).left ≫ s.left = (algOverHom f').left ≫ s.left := congrArg (·.left) h
    have h2 : spMap (f : O →+* A) = spMap (f' : O →+* A) := (cancel_mono s.left).1 h1
    have h3 := Spec.map_injective h2
    ext a
    exact congrArg (fun q => q.hom a) h3
  let aJ : JetR k κ m →ₐ[k] k := Chart.jetAug k κ m
  have hJ : RingHom.ker aJ ^ (m + 1) = ⊥ := Chart.ker_jetAug_pow κ m
  have hxa : algOverHom aJ ≫ x = 1 := by
    have : aJ = (Chart.jetAug k κ 0).comp (jetZeroR k κ m) := GlobalTheory.ChartUniv.jetAug_eq κ m
    rw [this, ← algOverHom_comp, Category.assoc, h0, MonObj.comp_one]
  have haug : aJ.comp τ = ε := canc _ _ (by rw [← algOverHom_comp, Category.assoc, hτ, hxa, hε])
  set I : Ideal O := RingHom.ker ε ^ (m + 1) with hI
  have hkill : ∀ a ∈ I, τ a = 0 := by
    intro a ha
    have hle : RingHom.ker ε ≤ (RingHom.ker aJ).comap τ := fun c hc => by
      show aJ (τ c) = 0
      rw [← AlgHom.comp_apply, haug]; exact hc
    have h2 := Ideal.le_comap_pow τ (m + 1) (Ideal.pow_right_mono hle (m + 1) ha)
    rw [hJ] at h2
    simpa using h2
  have hε0 : ∀ a ∈ I, ε a = 0 := fun a ha => Ideal.pow_le_self (Nat.succ_ne_zero m) ha
  let aA : (O ⧸ I) →ₐ[k] k := Ideal.Quotient.liftₐ I ε hε0
  have haA : aA.comp (Ideal.Quotient.mkₐ k I) = ε := by ext a; rfl
  have hA : RingHom.ker aA ^ (m + 1) = ⊥ := by
    have hle : RingHom.ker aA ≤ (RingHom.ker ε).map (Ideal.Quotient.mk I) := by
      intro c hc
      obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective c
      exact Ideal.mem_map_of_mem _ hc
    rw [← le_bot_iff]
    refine (Ideal.pow_right_mono hle _).trans ?_
    rw [← Ideal.map_pow, ← hI, Ideal.map_quotient_self]
  obtain ⟨ψ, ⟨h1, h2⟩, -⟩ := GlobalTheory.ChartUniv.univ_all (G := B) x h0 hu (O ⧸ I) aA hA
    (algOverHom (Ideal.Quotient.mkₐ k I) ≫ s) (by
      show algOverHom aA ≫ algOverHom (Ideal.Quotient.mkₐ k I) ≫ s = 1
      rw [← Category.assoc, algOverHom_comp, haA, hε])
  have h1' : aA.comp ψ = aJ := h1
  have h2' : algOverHom (Ideal.Quotient.mkₐ k I) ≫ s = algOverHom ψ ≫ x := h2
  have hψτ : ψ.comp τ = Ideal.Quotient.mkₐ k I :=
    canc _ _ (by rw [← algOverHom_comp, Category.assoc, hτ, h2'])
  let τ' : (O ⧸ I) →ₐ[k] JetR k κ m := Ideal.Quotient.liftₐ I τ hkill
  have hτ' : τ'.comp (Ideal.Quotient.mkₐ k I) = τ := by ext a; rfl
  have haτ' : aJ.comp τ' = aA := by
    refine Ideal.Quotient.algHom_ext k ?_
    rw [AlgHom.comp_assoc, hτ', haug, haA]
  have hid : τ'.comp ψ = AlgHom.id k _ := by
    refine (GlobalTheory.ChartUniv.univ_all (G := B) x h0 hu (JetR k κ m) aJ hJ x hxa).unique ⟨?_, ?_⟩ ⟨rfl, ?_⟩
    · show aJ.comp (τ'.comp ψ) = aJ
      rw [← AlgHom.comp_assoc, haτ', h1']
    · show x = algOverHom (τ'.comp ψ) ≫ x
      rw [← algOverHom_comp, Category.assoc, ← h2', ← Category.assoc, algOverHom_comp, hτ', hτ]
    · show x = algOverHom (AlgHom.id k _) ≫ x
      rw [algOverHom_id, Category.id_comp]
  refine ⟨fun c => ?_, fun a => ⟨fun ha => ?_, hkill a⟩⟩
  · obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective (ψ c)
    refine ⟨a, ?_⟩
    have := AlgHom.congr_fun hid c
    rw [AlgHom.comp_apply, ← ha] at this
    exact this
  · have := AlgHom.congr_fun hψτ a
    rw [AlgHom.comp_apply, ha, map_zero] at this
    exact Ideal.Quotient.eq_zero_iff_mem.1 this.symm

/- English proof (translation)
Introduce `k _ B _ _ hB g F x hx b hb _ hs m`. Use `haveI := hB`. Set `aJ : JetR k (Fin 1 × Fin g) m →ₐ[k] k` to `Chart.jetAug k _ m`. Establish `hJ : RingHom.ker aJ ^ (m + 1) = ⊥` using `Chart.ker_jetAug_pow _ m`. Use `haveI := isLocalRing_of_aug aJ hJ`.

Establish `h0 : algOverHom (jetZeroR k _ m) ≫ x m = 1` using `hx.zero m`. Establish `hxa : algOverHom aJ ≫ x m = 1`. Establish `: aJ = (Chart.jetAug k _ 0).comp (jetZeroR k _ m)` using `GlobalTheory.ChartUniv.jetAug_eq _ m`. Rewrite using `[this, ← algOverHom_comp, Category.assoc, h0, MonObj.comp_one]`. Establish `he : (1 : algOver k k ⟶ B).left (closedPoint k) = b`.

Rewrite using `[hb]`. Use `show η[B].left ((toUnit (algOver k k)).left (closedPoint k)) = _`. Conclude with `congrArg η[B].left (Subsingleton.elim (α := PrimeSpectrum k) _ _)`. Establish `hxb : (x m).left (closedPoint _) = b` using `by haveI : IsLocalHom (aJ : JetR k (Fin 1 × Fin g) m →+* k) := IsLocalHom.of_surjective _ (fun c => ⟨algebraMap _ _ c, aJ.commutes c⟩)`. Rewrite using `[← he, ← hxa, ← IsLocalRing.comap_closedPoint (aJ : JetR k (Fin 1 × Fin g) m →+* k)]`.

Both sides reduce to the same expression. Take `⟨ε, hεl, hε⟩` from `exists_factor b hs (1 : algOver k k ⟶ B) he`. Take `⟨τ, -, hτ⟩` from `exists_factor b hs (x m) hxb`. Set `s : algOver k (B.left.presheaf.stalk b) ⟶ B` to `Over.homMk (B.left.fromSpecStalk b) hs`. Use `haveI : Mono s.left := inferInstanceAs (Mono (B.left.fromSpecStalk b))`.

Establish `hker : RingHom.ker ε = maximalIdeal _` using `IsLocalRing.eq_maximalIdeal (RingHom.ker_isMaximal_of_surjective ε (fun c => ⟨algebraMap _ _ c, ε.commutes c⟩))`. Use `jet_of_mono (x m) h0 (fun κ' => hx.univ κ' m) s ε (Over.OverMorphism.ext hε) τ (Over.OverMorphism.ext hτ)` as an intermediate fact. Rewrite `this` using `[hker]`. Conclude with `⟨τ, hτ, this⟩`.
-/
theorem stalk_jet : ∀ (k : Type) [Field k] (B : Over (Sp k)) [GrpObj B] [IsCommMonObj B], Smooth B.hom → ∀ (g : ℕ) (F : FGLaw k g) (x : ∀ m : ℕ, algOver k (JetR k (Fin 1 × Fin g) m) ⟶ B), IsChartJ B F x → ∀ (b : B.left), b = η[B].left (closedPoint k) → ∀ [Algebra k (B.left.presheaf.stalk b)], B.left.fromSpecStalk b ≫ B.hom = spMap (algebraMap k (B.left.presheaf.stalk b)) → ∀ m : ℕ, ∃ τ : B.left.presheaf.stalk b →ₐ[k] JetR k (Fin 1 × Fin g) m, spMap (τ : B.left.presheaf.stalk b →+* JetR k (Fin 1 × Fin g) m) ≫ B.left.fromSpecStalk b = (x m).left ∧ Function.Surjective τ ∧ ∀ a, τ a = 0 ↔ a ∈ maximalIdeal (B.left.presheaf.stalk b) ^ (m + 1) := by
  intro k _ B _ _ hB g F x hx b hb _ hs m
  haveI := hB
  let aJ : JetR k (Fin 1 × Fin g) m →ₐ[k] k := Chart.jetAug k _ m
  have hJ : RingHom.ker aJ ^ (m + 1) = ⊥ := Chart.ker_jetAug_pow _ m
  haveI := isLocalRing_of_aug aJ hJ
  have h0 : algOverHom (jetZeroR k _ m) ≫ x m = 1 := hx.zero m
  have hxa : algOverHom aJ ≫ x m = 1 := by
    have : aJ = (Chart.jetAug k _ 0).comp (jetZeroR k _ m) := GlobalTheory.ChartUniv.jetAug_eq _ m
    rw [this, ← algOverHom_comp, Category.assoc, h0, MonObj.comp_one]
  have he : (1 : algOver k k ⟶ B).left (closedPoint k) = b := by
    rw [hb]
    show η[B].left ((toUnit (algOver k k)).left (closedPoint k)) = _
    exact congrArg η[B].left (Subsingleton.elim (α := PrimeSpectrum k) _ _)
  have hxb : (x m).left (closedPoint _) = b := by
    haveI : IsLocalHom (aJ : JetR k (Fin 1 × Fin g) m →+* k) :=
      IsLocalHom.of_surjective _ (fun c => ⟨algebraMap _ _ c, aJ.commutes c⟩)
    rw [← he, ← hxa, ← IsLocalRing.comap_closedPoint (aJ : JetR k (Fin 1 × Fin g) m →+* k)]
    rfl
  obtain ⟨ε, hεl, hε⟩ := exists_factor b hs (1 : algOver k k ⟶ B) he
  obtain ⟨τ, -, hτ⟩ := exists_factor b hs (x m) hxb
  let s : algOver k (B.left.presheaf.stalk b) ⟶ B := Over.homMk (B.left.fromSpecStalk b) hs
  haveI : Mono s.left := inferInstanceAs (Mono (B.left.fromSpecStalk b))
  have hker : RingHom.ker ε = maximalIdeal _ :=
    IsLocalRing.eq_maximalIdeal (RingHom.ker_isMaximal_of_surjective ε (fun c => ⟨algebraMap _ _ c, ε.commutes c⟩))
  have := jet_of_mono (x m) h0 (fun κ' => hx.univ κ' m) s ε (Over.OverMorphism.ext hε) τ (Over.OverMorphism.ext hτ)
  rw [hker] at this
  exact ⟨τ, hτ, this⟩

end GlobalTheory.StalkJet

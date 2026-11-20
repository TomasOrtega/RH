import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IsogenyEtaleTranslation.EtCancel

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.LKTrip GlobalTheory.LKMid GlobalTheory.LKGeo
open UpperTheory.Gal.Int.Geo (KS Lv Integ)

namespace UpperTheory.Gal.FixZ

/- English proof (translation)
Substitute `e` using the available equality. Conclude with `X.tr_mul i j m h h' a b a' b' c d`.
-/
private lemma tr_comp {B : Scheme.{0}} {Γ : Type} [Group Γ] (X : G3.Tower B Γ) {i j m : X.ι} {h h' g : Γ} (a b a' b')
    (e : h' * h = g) (c d) : X.tr i j h a b ≫ X.tr j m h' a' b' = X.tr i m g c d := by
  subst e
  exact X.tr_mul i j m h h' a b a' b' c d

/- English proof (translation)
Rewrite using `[HasRingHomProperty.iff_exists_appLE (P := @LocallyOfFinitePresentation) (RingHom.finitePresentation_stableUnderComposition.stableUnderCompositionWithLocalizationAway RingHom.finitePresentation_holdsForLocalizationAway).1]`. Introduce `x`. Take `⟨_, ⟨W, hW, rfl⟩, hxW, -⟩` from `S.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ (g (f x))) isOpen_univ`. Take `⟨_, ⟨U, hU, rfl⟩, hxU, hUW : U ≤ g ⁻¹ᵁ W⟩` from `B.isBasis_affineOpens.exists_subset_of_mem_open hxW (g ⁻¹ᵁ W).isOpen`. Take `⟨_, ⟨V, hV, rfl⟩, hxV, hVU : V ≤ f ⁻¹ᵁ U⟩` from `A.isBasis_affineOpens.exists_subset_of_mem_open hxU (f ⁻¹ᵁ U).isOpen`.

Use `⟨⟨U, hU⟩, ⟨V, hV⟩, hxV, hVU, RingHom.FinitePresentation.of_comp_finiteType (g.appLE W U hUW).hom ?_ (g.finiteType_appLE hW hU hUW)⟩` and prove the remaining obligations. Rewrite using `[← CommRingCat.hom_comp, Scheme.Hom.appLE_comp_appLE]`. Conclude with `(f ≫ g).finitePresentation_appLE hW hV _`.
-/
private lemma lofp_cancel {A B S : Scheme.{0}} (f : A ⟶ B) (g : B ⟶ S) [LocallyOfFinitePresentation (f ≫ g)]
    [LocallyOfFiniteType g] : LocallyOfFinitePresentation f := by
  rw [HasRingHomProperty.iff_exists_appLE (P := @LocallyOfFinitePresentation)
    (RingHom.finitePresentation_stableUnderComposition.stableUnderCompositionWithLocalizationAway
      RingHom.finitePresentation_holdsForLocalizationAway).1]
  intro x
  obtain ⟨_, ⟨W, hW, rfl⟩, hxW, -⟩ :=
    S.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ (g (f x))) isOpen_univ
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, hUW : U ≤ g ⁻¹ᵁ W⟩ :=
    B.isBasis_affineOpens.exists_subset_of_mem_open hxW (g ⁻¹ᵁ W).isOpen
  obtain ⟨_, ⟨V, hV, rfl⟩, hxV, hVU : V ≤ f ⁻¹ᵁ U⟩ :=
    A.isBasis_affineOpens.exists_subset_of_mem_open hxU (f ⁻¹ᵁ U).isOpen
  refine ⟨⟨U, hU⟩, ⟨V, hV⟩, hxV, hVU, RingHom.FinitePresentation.of_comp_finiteType
    (g.appLE W U hUW).hom ?_ (g.finiteType_appLE hW hU hUW)⟩
  rw [← CommRingCat.hom_comp, Scheme.Hom.appLE_comp_appLE]
  exact (f ≫ g).finitePresentation_appLE hW hV _

variable {p : ℕ} [Fact p.Prime] {D : Datum p} {G : HTGroup p} {L : Link D G} {gb : GBase D.toG ℂ} {k : ℕ}

/- English proof (translation)
Take `⟨h1, h2, -⟩` from `hP p D ℂ gb N (T.M N) k`. Rewrite using `[← T.e_q N]`. Conclude with `⟨inferInstance, inferInstance⟩`.
-/
private lemma q_props (hP : G3.PowSm) (T : KS L gb k) (N : Lv p) :
    Smooth (T.X.q (T.lev N)) ∧ IsSeparated (T.X.q (T.lev N)) := by
  obtain ⟨h1, h2, -⟩ := hP p D ℂ gb N (T.M N) k
  rw [← T.e_q N]
  exact ⟨inferInstance, inferInstance⟩

/- English proof (translation)
Take `⟨s1, s2⟩` from `q_props hP T N'`. Take `⟨s3, s4⟩` from `q_props hP T N`. Establish `e` using `T.X.tr_q (T.lev N') (T.lev N) h a b`. Prove the components needed by the constructor for the conclusion. Rewrite `s2` using `[← e]`.

Conclude with `IsSeparated.of_comp _ (T.X.q (T.lev N))`. Rewrite `s1` using `[← e]`. Conclude with `lofp_cancel _ (T.X.q (T.lev N))`.
-/
private lemma tr_props (hP : G3.PowSm) (T : KS L gb k) (N' N : Lv p) (h : G.GAf) (a b) :
    IsSeparated (T.X.tr (T.lev N') (T.lev N) h a b) ∧ LocallyOfFinitePresentation (T.X.tr (T.lev N') (T.lev N) h a b) := by
  obtain ⟨s1, s2⟩ := q_props hP T N'
  obtain ⟨s3, s4⟩ := q_props hP T N
  have e := T.X.tr_q (T.lev N') (T.lev N) h a b
  constructor
  · rw [← e] at s2
    exact IsSeparated.of_comp _ (T.X.q (T.lev N))
  · rw [← e] at s1
    exact lofp_cancel _ (T.X.q (T.lev N))

/- English proof (translation)
Establish `e` using `tr_comp T.X a₁ b₁ a₂ b₂ (mul_one z) a b`. Take `⟨f1, f2⟩` from `hS p D G L gb k T Q d z hd hc hz a₂ b₂`. Establish `f3` using `T.X.fin _ _ a₁ b₁`. Establish `f4` using `T.X.etale _ _ a₁ b₁`. Rewrite using `[← e]`.

Conclude with `⟨inferInstance, inferInstance⟩`.
-/
private lemma scal_fe (hS : TrScal) (T : KS L gb k) (P Q : Lv p) (d : ℕ) (z : G.GAf) (hd : 0 < d) (hc : d.Coprime p)
    (hz : IsScal L d z) (a b) (a₁ : (1 : G.GAf) ∈ T.X.Δ)
    (b₁ : ∀ u ∈ T.X.K (T.lev P), 1 * u * 1⁻¹ ∈ T.X.K (T.lev Q)) (a₂ : z ∈ T.X.Δ)
    (b₂ : ∀ u ∈ T.X.K (T.lev Q), z * u * z⁻¹ ∈ T.X.K (T.lev Q)) :
    IsFinite (T.X.tr (T.lev P) (T.lev Q) z a b) ∧ Etale (T.X.tr (T.lev P) (T.lev Q) z a b) := by
  have e := tr_comp T.X a₁ b₁ a₂ b₂ (mul_one z) a b
  obtain ⟨f1, f2⟩ := hS p D G L gb k T Q d z hd hc hz a₂ b₂
  have f3 := T.X.fin _ _ a₁ b₁
  have f4 := T.X.etale _ _ a₁ b₁
  rw [← e]
  exact ⟨inferInstance, inferInstance⟩

/- English proof (translation)
Introduce `hP hSc hTS hEC hDE hDF p _ D G L gb k T N' N h a b`. Take `⟨d, z, hd, hc, hz, hzi, hzh⟩` from `hSc p D G L h ((T.Δ_eq h).1 a)`. Establish `hcen` using `hz.1`. Establish `zΔ : z ∈ T.X.Δ` using `(T.Δ_eq z).2 hzi`. Establish `h'Δ : z * h⁻¹ ∈ T.X.Δ` using `(T.Δ_eq _).2 hzh`.

Establish `oΔ : (1 : G.GAf) ∈ T.X.Δ` using `one_mem _`. Establish `zc : ∀ u : G.GAf, z * u * z⁻¹ = u` using `fun u => by rw [hcen u, mul_inv_cancel_right]`. Establish `e1 : h * (z * h⁻¹) = z` using `by rw [← mul_assoc, ← hcen h, mul_inv_cancel_right]`. Establish `e2 : z * h⁻¹ * h = z` using `by rw [inv_mul_cancel_right]`. Take `⟨m, -, -, hm⟩` from `T.X.deep (T.lev N') {(T.lev N, 1), (T.lev N', z * h⁻¹)}`.

Take `⟨m', -, -, hm'⟩` from `T.X.deep (T.lev N') {(m, h), (T.lev N', 1)}`. Take `⟨M, rfl⟩` from `T.lev.surjective m`. Take `⟨M', rfl⟩` from `T.lev.surjective m'`. Establish `b1 : ∀ u ∈ T.X.K (T.lev M), 1 * u * 1⁻¹ ∈ T.X.K (T.lev N)` using `hm (T.lev N, 1) (by simp)`. Establish `b2 : ∀ u ∈ T.X.K (T.lev M), z * h⁻¹ * u * (z * h⁻¹)⁻¹ ∈ T.X.K (T.lev N')` using `hm (T.lev N', z * h⁻¹) (by simp)`.

Establish `b3 : ∀ u ∈ T.X.K (T.lev M'), h * u * h⁻¹ ∈ T.X.K (T.lev M)` using `hm' (T.lev M, h) (by simp)`. Establish `b4 : ∀ u ∈ T.X.K (T.lev M'), 1 * u * 1⁻¹ ∈ T.X.K (T.lev N')` using `hm' (T.lev N', 1) (by simp)`. Establish `b5 : ∀ u ∈ T.X.K (T.lev M), z * u * z⁻¹ ∈ T.X.K (T.lev N)` using `fun u hu => by`. Use `b1 u hu` as an intermediate fact. Simplify `this` using `[zc]`.

Establish `b6 : ∀ u ∈ T.X.K (T.lev M'), z * u * z⁻¹ ∈ T.X.K (T.lev N')` using `fun u hu => by`. Use `b4 u hu` as an intermediate fact. Simplify `this` using `[zc]`. Establish `b7 : ∀ u ∈ T.X.K (T.lev N), z * u * z⁻¹ ∈ T.X.K (T.lev N)` using `fun u hu => by rwa [zc]`. Establish `b8 : ∀ u ∈ T.X.K (T.lev N'), z * u * z⁻¹ ∈ T.X.K (T.lev N')` using `fun u hu => by rwa [zc]`.

Establish `b9 : ∀ u ∈ T.X.K (T.lev M'), h * u * h⁻¹ ∈ T.X.K (T.lev N)` using `fun u hu => by`. Use `b1 _ (b3 u hu)` as an intermediate fact. Simplify using `using this`. Establish `c1 : T.X.tr _ _ (z * h⁻¹) h'Δ b2 ≫ T.X.tr _ _ h a b = T.X.tr _ _ z zΔ b5` using `tr_comp T.X h'Δ b2 a b e1 zΔ b5`. Establish `c2 : T.X.tr _ _ h a b3 ≫ T.X.tr _ _ (z * h⁻¹) h'Δ b2 = T.X.tr _ _ z zΔ b6` using `tr_comp T.X a b3 h'Δ b2 e2 zΔ b6`.

Take `⟨f1, f2⟩` from `scal_fe hTS T M N d z hd hc hz zΔ b5 oΔ b1 zΔ b7`. Take `⟨f3, f4⟩` from `scal_fe hTS T M' N' d z hd hc hz zΔ b6 oΔ b4 zΔ b8`. Rewrite `f1`, `f2` using `[← c1]`. Rewrite `f3`, `f4` using `[← c2]`. Take `⟨-, s1⟩` from `tr_props hP T M N' (z * h⁻¹) h'Δ b2`.

Establish `t1 : LocallyOfFiniteType (T.X.tr _ _ (z * h⁻¹) h'Δ b2)` using `inferInstance`. Take `⟨f5, f6⟩` from `hEC _ _ _ _ (T.X.tr _ _ h a b3) (T.X.tr _ _ (z * h⁻¹) h'Δ b2) (T.X.tr _ _ h a b) t1 f3 f4 f1 f2`. Establish `c3 : T.X.tr _ _ 1 oΔ b4 ≫ T.X.tr _ _ h a b = T.X.tr _ _ h a b9` using `tr_comp T.X oΔ b4 a b (mul_one h) a b9`. Establish `c4 : T.X.tr _ _ h a b3 ≫ T.X.tr _ _ 1 oΔ b1 = T.X.tr _ _ h a b9` using `tr_comp T.X a b3 oΔ b1 (one_mul h) a b9`. Establish `g1` using `T.X.fin _ _ oΔ b1`.

Establish `g2` using `T.X.etale _ _ oΔ b1`. Establish `g3 : IsFinite (T.X.tr _ _ 1 oΔ b4 ≫ T.X.tr _ _ h a b)`. Rewrite using `[c3, ← c4]`. Use `infer_instance`. Establish `g4 : Etale (T.X.tr _ _ 1 oΔ b4 ≫ T.X.tr _ _ h a b)`.

Rewrite using `[c3, ← c4]`. Use `infer_instance`. Take `⟨s2, s3⟩` from `tr_props hP T N' N h a b`. Establish `g5` using `hDE _ _ _ _ _ (T.X.etale _ _ oΔ b4) (T.X.onto _ _ oΔ b4) s3 g4`. Conclude with `⟨hDF _ _ _ _ _ (T.X.onto _ _ oΔ b4) s2 g5 g3, g5⟩`.
-/
theorem trFEt_of : G3.PowSm → ScalEx → TrScal → EtCancel → DescEt → DescFin → TrFEt := by
  classical
  intro hP hSc hTS hEC hDE hDF p _ D G L gb k T N' N h a b
  obtain ⟨d, z, hd, hc, hz, hzi, hzh⟩ := hSc p D G L h ((T.Δ_eq h).1 a)
  have hcen := hz.1
  have zΔ : z ∈ T.X.Δ := (T.Δ_eq z).2 hzi
  have h'Δ : z * h⁻¹ ∈ T.X.Δ := (T.Δ_eq _).2 hzh
  have oΔ : (1 : G.GAf) ∈ T.X.Δ := one_mem _
  have zc : ∀ u : G.GAf, z * u * z⁻¹ = u := fun u => by rw [hcen u, mul_inv_cancel_right]
  have e1 : h * (z * h⁻¹) = z := by rw [← mul_assoc, ← hcen h, mul_inv_cancel_right]
  have e2 : z * h⁻¹ * h = z := by rw [inv_mul_cancel_right]

  obtain ⟨m, -, -, hm⟩ := T.X.deep (T.lev N') {(T.lev N, 1), (T.lev N', z * h⁻¹)}
  obtain ⟨m', -, -, hm'⟩ := T.X.deep (T.lev N') {(m, h), (T.lev N', 1)}
  obtain ⟨M, rfl⟩ := T.lev.surjective m
  obtain ⟨M', rfl⟩ := T.lev.surjective m'
  have b1 : ∀ u ∈ T.X.K (T.lev M), 1 * u * 1⁻¹ ∈ T.X.K (T.lev N) := hm (T.lev N, 1) (by simp)
  have b2 : ∀ u ∈ T.X.K (T.lev M), z * h⁻¹ * u * (z * h⁻¹)⁻¹ ∈ T.X.K (T.lev N') := hm (T.lev N', z * h⁻¹) (by simp)
  have b3 : ∀ u ∈ T.X.K (T.lev M'), h * u * h⁻¹ ∈ T.X.K (T.lev M) := hm' (T.lev M, h) (by simp)
  have b4 : ∀ u ∈ T.X.K (T.lev M'), 1 * u * 1⁻¹ ∈ T.X.K (T.lev N') := hm' (T.lev N', 1) (by simp)
  have b5 : ∀ u ∈ T.X.K (T.lev M), z * u * z⁻¹ ∈ T.X.K (T.lev N) := fun u hu => by
    have := b1 u hu
    simpa [zc] using this
  have b6 : ∀ u ∈ T.X.K (T.lev M'), z * u * z⁻¹ ∈ T.X.K (T.lev N') := fun u hu => by
    have := b4 u hu
    simpa [zc] using this
  have b7 : ∀ u ∈ T.X.K (T.lev N), z * u * z⁻¹ ∈ T.X.K (T.lev N) := fun u hu => by rwa [zc]
  have b8 : ∀ u ∈ T.X.K (T.lev N'), z * u * z⁻¹ ∈ T.X.K (T.lev N') := fun u hu => by rwa [zc]
  have b9 : ∀ u ∈ T.X.K (T.lev M'), h * u * h⁻¹ ∈ T.X.K (T.lev N) := fun u hu => by
    have := b1 _ (b3 u hu)
    simpa using this

  have c1 : T.X.tr _ _ (z * h⁻¹) h'Δ b2 ≫ T.X.tr _ _ h a b = T.X.tr _ _ z zΔ b5 :=
    tr_comp T.X h'Δ b2 a b e1 zΔ b5
  have c2 : T.X.tr _ _ h a b3 ≫ T.X.tr _ _ (z * h⁻¹) h'Δ b2 = T.X.tr _ _ z zΔ b6 :=
    tr_comp T.X a b3 h'Δ b2 e2 zΔ b6
  obtain ⟨f1, f2⟩ := scal_fe hTS T M N d z hd hc hz zΔ b5 oΔ b1 zΔ b7
  obtain ⟨f3, f4⟩ := scal_fe hTS T M' N' d z hd hc hz zΔ b6 oΔ b4 zΔ b8
  rw [← c1] at f1 f2
  rw [← c2] at f3 f4
  obtain ⟨-, s1⟩ := tr_props hP T M N' (z * h⁻¹) h'Δ b2
  have t1 : LocallyOfFiniteType (T.X.tr _ _ (z * h⁻¹) h'Δ b2) := inferInstance
  obtain ⟨f5, f6⟩ := hEC _ _ _ _ (T.X.tr _ _ h a b3) (T.X.tr _ _ (z * h⁻¹) h'Δ b2) (T.X.tr _ _ h a b) t1 f3 f4 f1 f2

  have c3 : T.X.tr _ _ 1 oΔ b4 ≫ T.X.tr _ _ h a b = T.X.tr _ _ h a b9 :=
    tr_comp T.X oΔ b4 a b (mul_one h) a b9
  have c4 : T.X.tr _ _ h a b3 ≫ T.X.tr _ _ 1 oΔ b1 = T.X.tr _ _ h a b9 :=
    tr_comp T.X a b3 oΔ b1 (one_mul h) a b9
  have g1 := T.X.fin _ _ oΔ b1
  have g2 := T.X.etale _ _ oΔ b1
  have g3 : IsFinite (T.X.tr _ _ 1 oΔ b4 ≫ T.X.tr _ _ h a b) := by
    rw [c3, ← c4]; infer_instance
  have g4 : Etale (T.X.tr _ _ 1 oΔ b4 ≫ T.X.tr _ _ h a b) := by
    rw [c3, ← c4]; infer_instance
  obtain ⟨s2, s3⟩ := tr_props hP T N' N h a b
  have g5 := hDE _ _ _ _ _ (T.X.etale _ _ oΔ b4) (T.X.onto _ _ oΔ b4) s3 g4
  exact ⟨hDF _ _ _ _ _ (T.X.onto _ _ oΔ b4) s2 g5 g3, g5⟩

end UpperTheory.Gal.FixZ

end

import Mathlib
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.MemNonzeroLocusVia
import Development.AbelianVarietyTheory.Definitions.KeyFormula.IsSquareDeterminantComparison
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SymplecticGenerators.IsPluriharmonicSiegel
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaUnifAV
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.MapsAtLeA
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SymplecticGenerators.SymplecticCharacters.OneEqSpTranslZero
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.AbLaw
open GlobalTheory.KeyKa

noncomputable section
namespace GlobalTheory.KeyKa
open EtBaseChange

/- English proof (translation)
Take `⟨⟨y, α⟩, rfl⟩` from `(Scheme.SpecToEquivOfField K X).symm.surjective a`. Take `⟨⟨y', β⟩, rfl⟩` from `(Scheme.SpecToEquivOfField K X).symm.surjective b`. Simplify using `only [Scheme.SpecToEquivOfField_symm_apply] at ha hb h ⊢`. Establish `hy : y = y'` using `by simpa using h`. Substitute `hy` using the available equality.

Take `⟨c, hc⟩` from `Spec.map_surjective (X.fromSpecResidueField y ≫ t)`. Rewrite `ha`, `hb` using `[Category.assoc, ← hc, ← Spec.map_comp, ← Spec.map_id]`. Establish `h₁` using `Spec.map_injective ha`. Establish `h₂` using `Spec.map_injective hb`. Establish `e₁ : ∀ k, α.hom (c.hom k) = k` using `fun k => congrArg (fun q => q.hom k) h₁`.

Establish `e₂ : ∀ k, β.hom (c.hom k) = k` using `fun k => congrArg (fun q => q.hom k) h₂`. Establish `: α = β`. Use extensionality with `k`. Establish `e₃ : c.hom (α.hom k) = k` using `α.hom.injective (e₁ _)`. Conclude with `(e₂ (α.hom k)).symm.trans (congrArg β.hom e₃)`.

Rewrite using `[this]`.
-/
theorem section_ext_of_apply_eq {K : Type} [Field K] {X : Scheme.{0}} (t : X ⟶ Sp K) (a b : Sp K ⟶ X)
    (ha : a ≫ t = 𝟙 _) (hb : b ≫ t = 𝟙 _) (p : Sp K) (h : a p = b p) : a = b := by
  obtain ⟨⟨y, α⟩, rfl⟩ := (Scheme.SpecToEquivOfField K X).symm.surjective a
  obtain ⟨⟨y', β⟩, rfl⟩ := (Scheme.SpecToEquivOfField K X).symm.surjective b
  simp only [Scheme.SpecToEquivOfField_symm_apply] at ha hb h ⊢
  have hy : y = y' := by simpa using h
  subst hy
  obtain ⟨c, hc⟩ := Spec.map_surjective (X.fromSpecResidueField y ≫ t)
  rw [Category.assoc, ← hc, ← Spec.map_comp, ← Spec.map_id] at ha hb
  have h₁ := Spec.map_injective ha
  have h₂ := Spec.map_injective hb
  have e₁ : ∀ k, α.hom (c.hom k) = k := fun k => congrArg (fun q => q.hom k) h₁
  have e₂ : ∀ k, β.hom (c.hom k) = k := fun k => congrArg (fun q => q.hom k) h₂
  have : α = β := by
    ext k
    have e₃ : c.hom (α.hom k) = k := α.hom.injective (e₁ _)
    exact (e₂ (α.hom k)).symm.trans (congrArg β.hom e₃)
  rw [this]

/- English proof (translation)
Introduce `O K _ _ _ x x' f φ w n d hg s s' z ch hf ⟨_, _, F, hp, _, _, _, hF₁, hF₂, hv⟩ hs hz₁ hz₂ hz₃ hz₄ hz₅`. Establish `hw : ∀ a, (spMap f ≫ (z a).left) ≫ x.P.A.hom = 𝟙 _ ≫ spMap f` using `fun a => (Category.assoc _ _ _).trans ((congrArg (spMap f ≫ ·) (Over.w (z a))).trans ((Category.comp_id _).trans (Category.id_comp _).symm))`. Set `z' : Fin d → Pt x'` to `fun a => Over.homMk (hp.1.lift (spMap f ≫ (z a).left) (𝟙 _) (hw a)) (hp.1.lift_snd _ _ _)`. Establish `hz' : ∀ a, (z' a).left ≫ φ = spMap f ≫ (z a).left` using `fun a => hp.1.lift_fst _ _ _`. Establish `hch : ∀ a, ∃ i, ⊤ ≤ (z' a).left ⁻¹ᵁ x'.P.L.U i` using `fun a => by`.

Take `⟨i, hi⟩` from `exists_chart x'.P.isLB ((z' a).left (IsLocalRing.closedPoint K))`. Conclude with `⟨i, fun p _ => ((IsLocalRing.specializes_closedPoint p).map (z' a).left.continuous).mem_open (x'.P.L.U i).isOpen hi⟩`. Use `choose ch' hch' using hch`. Establish `hφ : ∀ a, ⊤ ≤ ((z' a).left ≫ φ) ⁻¹ᵁ x.P.L.U (ch a)` using `fun a p _ => by`. Rewrite using `[hz' a]`.

Conclude with `hz₁ a (show spMap f p ∈ ⊤ from trivial)`. Establish `hW` using `fun a => le_inf_pull (T := K) (z' a).left (ch a) (ch' a) (hφ a) (hch' a)`. Set `u : Fin d → Kˣ` to `fun a => Units.map (valH (T := K) (z' a).left _ (hW a)).toMonoidHom (w.s (fun _ => ch a, ch' a))`. Establish `hu : ∀ a, valT (T` using `K) (z' a).left ((x.P.L.pull φ).U (fun _ => ch a) ⊓ x'.P.L.U (ch' a)) (w.s (fun _ => ch a, ch' a)).val = u a := fun a => valT_eq _ _ (hW a) _`. Establish `hval : ∀ (l : ℕ) (sg : RR x l) (sg' : RR x' l) (a), SecVia x' x φ w sg' sg → valT (T` using `K) (z' a).left (x'.P.L.U (ch' a)) (sg'.f (ch' a)) * (u a : K) ^ l = f (valT (T := O) (z a).left (x.P.L.U (ch a)) (sg.f (ch a))) := fun l sg sg' a h => by`.

Establish `e` using `valT_via (T := K) h (z' a).left (ch a) (ch' a) (hφ a) (hch' a)`. Rewrite `e` using `[hu]`. Use `(_root_.mul_comm _ _).trans (e.symm.trans ?_)` and prove the remaining obligations. Conclude with `(congrArg (fun q => valT (T := K) q (x.P.L.U (ch a)) (sg.f (ch a))) (hz' a)).trans (valT_spMap f (z a).left (hz₁ a) _)`. Establish `hzero : ∀ a i, valT (T` using `K) (z' a).left (x'.P.L.U (ch' a)) ((s' i).f (ch' a)) = 0 := fun a i => by`.

Establish `e` using `hval n _ _ a (hs i)`. Rewrite `e` using `[hz₂, map_zero]`. Conclude with `((u a).isUnit.pow n).mul_left_eq_zero.1 e`. Establish `hjac : ∀ a, jac x' s' (z' a) (ch' a) * (u a : K) ^ (x.P.g * n) = f (jac x s (z a) (ch a))` using `fun a => by`. Establish `ent : ∀ i k, f (TrivSqZeroExt.snd (valT (T` using `DualNumber O) ((toUnit (epsR O) ≫ z a) * x.v (k.cast hg)).left (x.P.L.U (ch a)) ((s (i.cast hg)).f (ch a)))) = (u a : K) ^ n * TrivSqZeroExt.snd (valT (T := DualNumber K) ((toUnit (epsR K) ≫ z' a) * x'.v k).left (x'.P.L.U (ch' a)) ((s' i).f (ch' a))) := fun i k => by`.

Establish `c` using `translate_comp hp F hF₁ (z a) (z' a) (hz' a) (x.v (k.cast hg)) (x'.v k) (hv k)`. Establish `l₁` using `translate_le (z a) (x.v (k.cast hg)) (x.basis.1 _) (hz₁ a)`. Establish `l₂` using `translate_le (z' a) (x'.v k) (x'.basis.1 _) (hch' a)`. Establish `l₃ : ⊤ ≤ (((toUnit (epsR K) ≫ z' a) * x'.v k).left ≫ φ) ⁻¹ᵁ x.P.L.U (ch a)` using `fun p _ => by`. Rewrite using `[c]`.

Conclude with `l₁ (show spMap F p ∈ ⊤ from trivial)`. Establish `e` using `valT_via (T := DualNumber K) (hs i) _ (ch a) (ch' a) l₃ l₂`. Establish `e₂` using `(congrArg (fun q => valT (T := DualNumber K) q (x.P.L.U (ch a)) ((s (i.cast hg)).f (ch a))) c).trans (valT_spMap F _ l₁ _)`. Use `(snd_map f F hF₁ hF₂ _).symm.trans ((congrArg TrivSqZeroExt.snd (e₂.symm.trans e)).trans ?_)` and prove the remaining obligations. Use `(snd_pow_mul _ _ _ ((fst_valT_translate (z' a) (x'.v k) (x'.basis.1 _) (hch' a) _).trans (hzero a i))).trans ?_` and prove the remaining obligations.

Conclude with `congrArg (· ^ n * _) ((fst_valT_translate (z' a) (x'.v k) (x'.basis.1 _) (hW a) _).trans (hu a))`. Unfold `jac`. Rewrite using `[RingHom.map_det, ← Matrix.det_submatrix_equiv_self (finCongr hg), _root_.mul_comm, _root_.mul_comm x.P.g n, pow_mul]`. Establish `hc : x.P.g = Fintype.card (Fin x'.P.g)` using `hg.symm.trans (Fintype.card_fin _).symm`. Use `(congrArg (fun m => ((u a : K) ^ n) ^ m * _) hc).trans ((Matrix.det_smul _ _).symm.trans ?_)` and prove the remaining obligations.

Use `congr 1`. Use extensionality with `i k`. Conclude with `(ent i k).symm`. Use `⟨z', ch', u, ⟨hch', hzero, fun a => ?_, fun a a' h p e => ?_, fun y hy => ?_⟩, hval⟩` and prove the remaining obligations. Establish `hne : f (jac x s (z a) (ch a)) ≠ 0` using `fun h => hz₃ a (hf (h.trans (map_zero f).symm))`.

Conclude with `isUnit_of_mul_isUnit_left (hjac a ▸ hne.isUnit)`. Establish `e₀ : (z' a).left = (z' a').left` using `section_ext_of_apply_eq x'.P.A.hom (z' a).left (z' a').left (Over.w (z' a)) (Over.w (z' a')) p e`. Establish `e₁ : spMap f ≫ (z a).left = spMap f ≫ (z a').left` using `(hz' a).symm.trans ((congrArg (· ≫ φ) e₀).trans (hz' a'))`. Establish `: IsDominant (spMap f)` using `⟨(PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical f).2 (by`. Rewrite using `[(RingHom.injective_iff_ker_eq_bot f).1 hf]`.

Conclude with `bot_le)⟩`. Establish `: IsProper x.P.A.hom` using `x.P.isAb.proper`. Conclude with `h (hz₄ (Over.OverMorphism.ext (ext_of_isDominant_of_isSeparated (X := Sp O) x.P.A.hom ((Over.w (z a)).trans (Over.w (z a')).symm) (spMap f) e₁)))`. Take `⟨a, p, hp'⟩` from `hz₅ (φ y) ⟨x'.P.A.hom y, (congrArg (fun q => q y) hp.1.w).symm⟩ fun i h => hy (i.cast hg.symm) (mem_nonzeroLocus_via (hs (i.cast hg.symm)) y h)`. Establish `sq : IsPullback (spMap f) (z' a).left (z a).left φ`.

Use `IsPullback.of_bot (t := hp.1) ?_ (hz' a).symm` and prove the remaining obligations. Establish `e₁ : (z' a).left ≫ x'.P.A.hom = 𝟙 _` using `Over.w (z' a)`. Establish `e₂ : (z a).left ≫ x.P.A.hom = 𝟙 _` using `Over.w (z a)`. Rewrite using `[e₁, e₂]`. Conclude with `IsPullback.of_vert_isIso (fst := spMap f) (snd := 𝟙 (Sp K)) (f := 𝟙 (Sp O)) (g := spMap f) ⟨by simp⟩`.

Take `⟨q, -, hq⟩` from `Scheme.exists_preimage_of_isPullback sq p y hp'`. Conclude with `⟨a, q, hq⟩`.
-/
theorem etZ_of_jac_ne_zero : ∀ (O K : Type) [CommRing O] [IsDomain O] [Field K] (x : KeyIn O) (x' : KeyIn K) (f : O →+* K) φ w (n d : ℕ) (hg : x'.P.g = x.P.g) (s : Fin x.P.g → RR x n) (s' : Fin x'.P.g → RR x' n) (z : Fin d → Pt x) (ch : Fin d → x.P.L.ι), Function.Injective f → KeyVia x' x f φ w → (∀ i, SecVia x' x φ w (s' i) (s (i.cast hg))) → (∀ a, ⊤ ≤ (z a).left ⁻¹ᵁ x.P.L.U (ch a)) → (∀ a i, valT (T := O) (z a).left (x.P.L.U (ch a)) ((s i).f (ch a)) = 0) → (∀ a, jac x s (z a) (ch a) ≠ 0) → Function.Injective z → (∀ y : x.P.A.left, (∃ q : Sp K, spMap f q = x.P.A.hom y) → (∀ i, y ∉ Out.nonzeroLocus (s i)) → ∃ a, ∃ p : Sp O, (z a).left p = y) → ∃ (z' : Fin d → Pt x') (ch' : Fin d → x'.P.L.ι) (u : Fin d → Kˣ), EtZ x' s' z' ch' ∧ ∀ (l : ℕ) (sg : RR x l) (sg' : RR x' l) (a), SecVia x' x φ w sg' sg → valT (T := K) (z' a).left (x'.P.L.U (ch' a)) (sg'.f (ch' a)) * (u a : K) ^ l = f (valT (T := O) (z a).left (x.P.L.U (ch a)) (sg.f (ch a))) := by
  intro O K _ _ _ x x' f φ w n d hg s s' z ch hf ⟨_, _, F, hp, _, _, _, hF₁, hF₂, hv⟩ hs hz₁ hz₂ hz₃ hz₄ hz₅
  have hw : ∀ a, (spMap f ≫ (z a).left) ≫ x.P.A.hom = 𝟙 _ ≫ spMap f := fun a =>
    (Category.assoc _ _ _).trans ((congrArg (spMap f ≫ ·) (Over.w (z a))).trans
      ((Category.comp_id _).trans (Category.id_comp _).symm))
  let z' : Fin d → Pt x' := fun a => Over.homMk (hp.1.lift (spMap f ≫ (z a).left) (𝟙 _) (hw a)) (hp.1.lift_snd _ _ _)
  have hz' : ∀ a, (z' a).left ≫ φ = spMap f ≫ (z a).left := fun a => hp.1.lift_fst _ _ _
  have hch : ∀ a, ∃ i, ⊤ ≤ (z' a).left ⁻¹ᵁ x'.P.L.U i := fun a => by
    obtain ⟨i, hi⟩ := exists_chart x'.P.isLB ((z' a).left (IsLocalRing.closedPoint K))
    exact ⟨i, fun p _ => ((IsLocalRing.specializes_closedPoint p).map (z' a).left.continuous).mem_open
      (x'.P.L.U i).isOpen hi⟩
  choose ch' hch' using hch
  have hφ : ∀ a, ⊤ ≤ ((z' a).left ≫ φ) ⁻¹ᵁ x.P.L.U (ch a) := fun a p _ => by
    rw [hz' a]
    exact hz₁ a (show spMap f p ∈ ⊤ from trivial)
  have hW := fun a => le_inf_pull (T := K) (z' a).left (ch a) (ch' a) (hφ a) (hch' a)
  let u : Fin d → Kˣ := fun a => Units.map (valH (T := K) (z' a).left _ (hW a)).toMonoidHom (w.s (fun _ => ch a, ch' a))
  have hu : ∀ a, valT (T := K) (z' a).left ((x.P.L.pull φ).U (fun _ => ch a) ⊓ x'.P.L.U (ch' a))
      (w.s (fun _ => ch a, ch' a)).val = u a := fun a => valT_eq _ _ (hW a) _
  have hval : ∀ (l : ℕ) (sg : RR x l) (sg' : RR x' l) (a), SecVia x' x φ w sg' sg →
      valT (T := K) (z' a).left (x'.P.L.U (ch' a)) (sg'.f (ch' a)) * (u a : K) ^ l =
        f (valT (T := O) (z a).left (x.P.L.U (ch a)) (sg.f (ch a))) := fun l sg sg' a h => by
    have e := valT_via (T := K) h (z' a).left (ch a) (ch' a) (hφ a) (hch' a)
    rw [hu] at e
    refine (_root_.mul_comm _ _).trans (e.symm.trans ?_)
    exact (congrArg (fun q => valT (T := K) q (x.P.L.U (ch a)) (sg.f (ch a))) (hz' a)).trans
      (valT_spMap f (z a).left (hz₁ a) _)
  have hzero : ∀ a i, valT (T := K) (z' a).left (x'.P.L.U (ch' a)) ((s' i).f (ch' a)) = 0 := fun a i => by
    have e := hval n _ _ a (hs i)
    rw [hz₂, map_zero] at e
    exact ((u a).isUnit.pow n).mul_left_eq_zero.1 e
  have hjac : ∀ a, jac x' s' (z' a) (ch' a) * (u a : K) ^ (x.P.g * n) = f (jac x s (z a) (ch a)) := fun a => by
    have ent : ∀ i k, f (TrivSqZeroExt.snd (valT (T := DualNumber O) ((toUnit (epsR O) ≫ z a) * x.v (k.cast hg)).left
        (x.P.L.U (ch a)) ((s (i.cast hg)).f (ch a)))) = (u a : K) ^ n * TrivSqZeroExt.snd (valT (T := DualNumber K)
          ((toUnit (epsR K) ≫ z' a) * x'.v k).left (x'.P.L.U (ch' a)) ((s' i).f (ch' a))) := fun i k => by
      have c := translate_comp hp F hF₁ (z a) (z' a) (hz' a) (x.v (k.cast hg)) (x'.v k) (hv k)
      have l₁ := translate_le (z a) (x.v (k.cast hg)) (x.basis.1 _) (hz₁ a)
      have l₂ := translate_le (z' a) (x'.v k) (x'.basis.1 _) (hch' a)
      have l₃ : ⊤ ≤ (((toUnit (epsR K) ≫ z' a) * x'.v k).left ≫ φ) ⁻¹ᵁ x.P.L.U (ch a) := fun p _ => by
        rw [c]
        exact l₁ (show spMap F p ∈ ⊤ from trivial)
      have e := valT_via (T := DualNumber K) (hs i) _ (ch a) (ch' a) l₃ l₂
      have e₂ := (congrArg (fun q => valT (T := DualNumber K) q (x.P.L.U (ch a)) ((s (i.cast hg)).f (ch a))) c).trans
        (valT_spMap F _ l₁ _)
      refine (snd_map f F hF₁ hF₂ _).symm.trans ((congrArg TrivSqZeroExt.snd (e₂.symm.trans e)).trans ?_)
      refine (snd_pow_mul _ _ _ ((fst_valT_translate (z' a) (x'.v k) (x'.basis.1 _) (hch' a) _).trans (hzero a i))).trans ?_
      exact congrArg (· ^ n * _) ((fst_valT_translate (z' a) (x'.v k) (x'.basis.1 _) (hW a) _).trans (hu a))
    unfold jac
    rw [RingHom.map_det, ← Matrix.det_submatrix_equiv_self (finCongr hg), _root_.mul_comm, _root_.mul_comm x.P.g n,
      pow_mul]
    have hc : x.P.g = Fintype.card (Fin x'.P.g) := hg.symm.trans (Fintype.card_fin _).symm
    refine (congrArg (fun m => ((u a : K) ^ n) ^ m * _) hc).trans ((Matrix.det_smul _ _).symm.trans ?_)
    congr 1
    ext i k
    exact (ent i k).symm
  refine ⟨z', ch', u, ⟨hch', hzero, fun a => ?_, fun a a' h p e => ?_, fun y hy => ?_⟩, hval⟩
  · have hne : f (jac x s (z a) (ch a)) ≠ 0 := fun h => hz₃ a (hf (h.trans (map_zero f).symm))
    exact isUnit_of_mul_isUnit_left (hjac a ▸ hne.isUnit)
  · have e₀ : (z' a).left = (z' a').left :=
      section_ext_of_apply_eq x'.P.A.hom (z' a).left (z' a').left (Over.w (z' a)) (Over.w (z' a')) p e
    have e₁ : spMap f ≫ (z a).left = spMap f ≫ (z a').left :=
      (hz' a).symm.trans ((congrArg (· ≫ φ) e₀).trans (hz' a'))
    have : IsDominant (spMap f) := ⟨(PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical f).2 (by
      rw [(RingHom.injective_iff_ker_eq_bot f).1 hf]; exact bot_le)⟩
    have : IsProper x.P.A.hom := x.P.isAb.proper
    exact h (hz₄ (Over.OverMorphism.ext (ext_of_isDominant_of_isSeparated (X := Sp O) x.P.A.hom
      ((Over.w (z a)).trans (Over.w (z a')).symm) (spMap f) e₁)))
  · obtain ⟨a, p, hp'⟩ := hz₅ (φ y) ⟨x'.P.A.hom y, (congrArg (fun q => q y) hp.1.w).symm⟩
      fun i h => hy (i.cast hg.symm) (mem_nonzeroLocus_via (hs (i.cast hg.symm)) y h)
    have sq : IsPullback (spMap f) (z' a).left (z a).left φ := by
      refine IsPullback.of_bot (t := hp.1) ?_ (hz' a).symm
      have e₁ : (z' a).left ≫ x'.P.A.hom = 𝟙 _ := Over.w (z' a)
      have e₂ : (z a).left ≫ x.P.A.hom = 𝟙 _ := Over.w (z a)
      rw [e₁, e₂]
      exact IsPullback.of_vert_isIso (fst := spMap f) (snd := 𝟙 (Sp K)) (f := 𝟙 (Sp O)) (g := spMap f) ⟨by simp⟩
    obtain ⟨q, -, hq⟩ := Scheme.exists_preimage_of_isPullback sq p y hp'
    exact ⟨a, q, hq⟩

end GlobalTheory.KeyKa
end

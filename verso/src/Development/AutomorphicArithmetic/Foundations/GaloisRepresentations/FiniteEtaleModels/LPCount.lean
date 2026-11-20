import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.FiniteEtaleModels.LSigFin
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.UPel.HT.EtLev GlobalTheory.LKTrip GlobalTheory.LKGeo
open UpperTheory.Gal.Int.Geo
open UpperTheory.Gal.G3 (sp)
open UpperTheory.Gal.FiniteEtaleModels

/- English proof (translation)
Introduce `hpt hfin I B _ _ W Z Y Y' cls f kc π s m hf he hs hes hm h`. Take `⟨hsF, hsE⟩` from `hfin B Y' Y s hs hes`. Take `⟨hdF, hdE⟩` from `hfin I W Z f hf he`. Use `set sB : (∐ fun _ : B => Y') ⟶ Y := Sigma.desc fun _ : B => s with hsB`. Use `set ℓ := pullback.lift _ _ h with hℓ`.

Establish `hℓ1 : ℓ ≫ pullback.fst π sB = Sigma.desc fun _ : I => f` using `pullback.lift_fst _ _ h`. Establish `hℓ2 : ℓ ≫ pullback.snd π sB = Sigma.desc fun c : I => kc c ≫ Sigma.ι (fun _ : B => Y') (cls c)` using `pullback.lift_snd _ _ h`. Use `haveI := hsF`. Use `haveI := hsE`. Use `haveI : IsFinite (pullback.fst π sB) := inferInstance`.

Use `haveI : Etale (pullback.fst π sB) := inferInstance`. Use `haveI : IsFinite (ℓ ≫ pullback.fst π sB) := by rw [hℓ1]; exact hdF`. Use `haveI : Etale (ℓ ≫ pullback.fst π sB) := by rw [hℓ1]; exact hdE`. Use `⟨IsFinite.of_comp ℓ (pullback.fst π sB), Etale.of_comp ℓ (pullback.fst π sB), ?_⟩` and prove the remaining obligations. Introduce `K _ _ x`.

Take `⟨⟨b, y'⟩, hb⟩` from `(hpt B Y' K).2 (x ≫ pullback.snd π sB)`. Use `replace hb : y' ≫ Sigma.ι (fun _ : B => Y') b = x ≫ pullback.snd π sB := hb`. Establish `hy : y' ≫ s = (x ≫ pullback.fst π sB) ≫ π`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[hb, Category.assoc, Category.assoc, pullback.condition]`.

Establish `key : ∀ (c : I) (v : sp K ⟶ W), (v ≫ Sigma.ι (fun _ : I => W) c) ≫ ℓ = x ↔ v ≫ f = x ≫ pullback.fst π sB ∧ cls c = b ∧ v ≫ kc c = y'`. Introduce `c v`. Establish `e1 : ((v ≫ Sigma.ι (fun _ : I => W) c) ≫ ℓ) ≫ pullback.fst π sB = v ≫ f`. Rewrite using `[Category.assoc, hℓ1]`. Simplify using the standard rewrite rules.

Establish `e2 : ((v ≫ Sigma.ι (fun _ : I => W) c) ≫ ℓ) ≫ pullback.snd π sB = (v ≫ kc c) ≫ Sigma.ι (fun _ : B => Y') (cls c)`. Rewrite using `[Category.assoc, hℓ2]`. Simplify using the standard rewrite rules. Prove the components needed by the constructor for the conclusion. Introduce `hx`.

Rewrite `e1`, `e2` using `[hx]`. Establish `h2 : (fun p : B × (sp K ⟶ Y') => p.2 ≫ Sigma.ι (fun _ : B => Y') p.1) (cls c, v ≫ kc c) = (fun p : B × (sp K ⟶ Y') => p.2 ≫ Sigma.ι (fun _ : B => Y') p.1) (b, y')` using `by show (v ≫ kc c) ≫ Sigma.ι (fun _ : B => Y') (cls c) = y' ≫ Sigma.ι (fun _ : B => Y') b`. Rewrite using `[← e2, hb]`. Take `⟨h3, h4⟩` from `Prod.mk.inj ((hpt B Y' K).1 h2)`. Conclude with `⟨e1.symm, h3, h4⟩`.

Introduce and unpack `⟨h1, h3, h4⟩`. Apply `pullback.hom_ext` to reduce the goal to its premises. Rewrite using `[e1, h1]`. Rewrite using `[e2, h3, h4, hb]`. Rewrite using `[← hm K (x ≫ pullback.fst π sB) b y' hy]`.

Set `F : {cx : I × (sp K ⟶ W) // cx.2 ≫ f = x ≫ pullback.fst π sB ∧ cls cx.1 = b ∧ cx.2 ≫ kc cx.1 = y'} → {y : sp K ⟶ ∐ (fun _ : I => W) // y ≫ ℓ = x}` to `fun p => ⟨p.1.2 ≫ Sigma.ι (fun _ : I => W) p.1.1, (key _ _).2 p.2⟩`. Establish `hF : Function.Bijective F`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨⟨c, v⟩, hv⟩ ⟨⟨c', v'⟩, hv'⟩ e`. Establish `e' : (fun p : I × (sp K ⟶ W) => p.2 ≫ Sigma.ι (fun _ : I => W) p.1) (c, v) = (fun p : I × (sp K ⟶ W) => p.2 ≫ Sigma.ι (fun _ : I => W) p.1) (c', v')` using `congrArg Subtype.val e`.

Conclude with `Subtype.ext ((hpt I W K).1 e')`. Introduce and unpack `⟨y, hy'⟩`. Take `⟨⟨c, v⟩, hv⟩` from `(hpt I W K).2 y`. Use `replace hv : v ≫ Sigma.ι (fun _ : I => W) c = y := hv`. Substitute `hv` using the available equality.

Conclude with `⟨⟨(c, v), (key c v).1 hy'⟩, rfl⟩`. Conclude with `(Nat.card_congr (Equiv.ofBijective F hF)).symm`.
-/
theorem UpperTheory.Gal.FiniteEtaleModels.lCount_holds :
    LSigPt → LSigFin → LCount := by
  intro hpt hfin I B _ _ W Z Y Y' cls f kc π s m hf he hs hes hm h
  obtain ⟨hsF, hsE⟩ := hfin B Y' Y s hs hes
  obtain ⟨hdF, hdE⟩ := hfin I W Z f hf he
  set sB : (∐ fun _ : B => Y') ⟶ Y := Sigma.desc fun _ : B => s with hsB
  set ℓ := pullback.lift _ _ h with hℓ
  have hℓ1 : ℓ ≫ pullback.fst π sB = Sigma.desc fun _ : I => f := pullback.lift_fst _ _ h
  have hℓ2 : ℓ ≫ pullback.snd π sB =
      Sigma.desc fun c : I => kc c ≫ Sigma.ι (fun _ : B => Y') (cls c) := pullback.lift_snd _ _ h
  haveI := hsF
  haveI := hsE
  haveI : IsFinite (pullback.fst π sB) := inferInstance
  haveI : Etale (pullback.fst π sB) := inferInstance
  haveI : IsFinite (ℓ ≫ pullback.fst π sB) := by rw [hℓ1]; exact hdF
  haveI : Etale (ℓ ≫ pullback.fst π sB) := by rw [hℓ1]; exact hdE
  refine ⟨IsFinite.of_comp ℓ (pullback.fst π sB), Etale.of_comp ℓ (pullback.fst π sB), ?_⟩
  intro K _ _ x
  obtain ⟨⟨b, y'⟩, hb⟩ := (hpt B Y' K).2 (x ≫ pullback.snd π sB)
  replace hb : y' ≫ Sigma.ι (fun _ : B => Y') b = x ≫ pullback.snd π sB := hb
  have hy : y' ≫ s = (x ≫ pullback.fst π sB) ≫ π := by
    calc y' ≫ s = (y' ≫ Sigma.ι (fun _ : B => Y') b) ≫ sB := by simp [hsB]
      _ = (x ≫ pullback.fst π sB) ≫ π := by
        rw [hb, Category.assoc, Category.assoc, pullback.condition]
  have key : ∀ (c : I) (v : sp K ⟶ W), (v ≫ Sigma.ι (fun _ : I => W) c) ≫ ℓ = x ↔
      v ≫ f = x ≫ pullback.fst π sB ∧ cls c = b ∧ v ≫ kc c = y' := by
    intro c v
    have e1 : ((v ≫ Sigma.ι (fun _ : I => W) c) ≫ ℓ) ≫ pullback.fst π sB = v ≫ f := by
      rw [Category.assoc, hℓ1]; simp
    have e2 : ((v ≫ Sigma.ι (fun _ : I => W) c) ≫ ℓ) ≫ pullback.snd π sB =
        (v ≫ kc c) ≫ Sigma.ι (fun _ : B => Y') (cls c) := by
      rw [Category.assoc, hℓ2]; simp
    constructor
    · intro hx
      rw [hx] at e1 e2
      have h2 : (fun p : B × (sp K ⟶ Y') => p.2 ≫ Sigma.ι (fun _ : B => Y') p.1) (cls c, v ≫ kc c) =
          (fun p : B × (sp K ⟶ Y') => p.2 ≫ Sigma.ι (fun _ : B => Y') p.1) (b, y') := by
        show (v ≫ kc c) ≫ Sigma.ι (fun _ : B => Y') (cls c) = y' ≫ Sigma.ι (fun _ : B => Y') b
        rw [← e2, hb]
      obtain ⟨h3, h4⟩ := Prod.mk.inj ((hpt B Y' K).1 h2)
      exact ⟨e1.symm, h3, h4⟩
    · rintro ⟨h1, h3, h4⟩
      apply pullback.hom_ext
      · rw [e1, h1]
      · rw [e2, h3, h4, hb]
  rw [← hm K (x ≫ pullback.fst π sB) b y' hy]
  let F : {cx : I × (sp K ⟶ W) // cx.2 ≫ f = x ≫ pullback.fst π sB ∧ cls cx.1 = b ∧ cx.2 ≫ kc cx.1 = y'} →
      {y : sp K ⟶ ∐ (fun _ : I => W) // y ≫ ℓ = x} :=
    fun p => ⟨p.1.2 ≫ Sigma.ι (fun _ : I => W) p.1.1, (key _ _).2 p.2⟩
  have hF : Function.Bijective F := by
    constructor
    · rintro ⟨⟨c, v⟩, hv⟩ ⟨⟨c', v'⟩, hv'⟩ e
      have e' : (fun p : I × (sp K ⟶ W) => p.2 ≫ Sigma.ι (fun _ : I => W) p.1) (c, v) =
          (fun p : I × (sp K ⟶ W) => p.2 ≫ Sigma.ι (fun _ : I => W) p.1) (c', v') :=
        congrArg Subtype.val e
      exact Subtype.ext ((hpt I W K).1 e')
    · rintro ⟨y, hy'⟩
      obtain ⟨⟨c, v⟩, hv⟩ := (hpt I W K).2 y
      replace hv : v ≫ Sigma.ι (fun _ : I => W) c = y := hv
      subst hv
      exact ⟨⟨(c, v), (key c v).1 hy'⟩, rfl⟩
  exact (Nat.card_congr (Equiv.ofBijective F hF)).symm

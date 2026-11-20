import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.MapHComp
set_option backward.isDefEq.respectTransparency false
open CategoryTheory Opposite CrystallineSemistableComparison CrystallineSemistableComparison.CH
universe w w' w'' t t' v u v' u' v'' u''

namespace GlobalTheory.CompanionTheory.CatPieces

variable {R : Type} [CommRing R] {C : Type u} [Category.{v} C] (F : C ⥤ ModuleCat.{w} R)
  {ι : Type t} (c : C → ι)

abbrev piece (i : ι) : ObjectProperty C := fun T => c T = i

abbrev res (i : ι) : Mor F ((ObjectProperty.ι (piece c i)) ⋙ F) (RingHom.id R) :=
  Mor.restrict F (ObjectProperty.ι (piece c i))

variable {c}

/- English proof (translation)
The claim follows from `(hc (s.map (homOfLE (Fin.zero_le k)))).symm`.
-/
theorem chain_piece (hc : ∀ {T T' : C}, (T ⟶ T') → c T = c T') {n : ℕ} (s : ComposableArrows C n)
    (k : Fin (n + 1)) : c (s.obj k) = c (s.obj 0) :=
  (hc (s.map (homOfLE (Fin.zero_le k)))).symm

variable {F}

def glue (hc : ∀ {T T' : C}, (T ⟶ T') → c T = c T') {n : ℕ}
    (g : ∀ i, Cn ((ObjectProperty.ι (piece c i)) ⋙ F) n) : Cn F n :=
  fun s => g (c (s.obj 0)) (ObjectProperty.lift (piece c (c (s.obj 0))) s (chain_piece hc s))

/- English proof (translation)
Substitute `e` using the available equality. Both sides reduce to the same expression.
-/
theorem val_congr {n : ℕ} (g : ∀ i, Cn ((ObjectProperty.ι (piece c i)) ⋙ F) n) {i j : ι} (e : i = j)
    (s : ComposableArrows C n) (h : ∀ k, piece c i (s.obj k)) (h' : ∀ k, piece c j (s.obj k)) :
    (g i (ObjectProperty.lift (piece c i) s h) : F.obj (s.obj (Fin.last n))) =
      g j (ObjectProperty.lift (piece c j) s h') := by
  subst e; rfl

/- English proof (translation)
Use function extensionality and compare the values at `s`. Establish `hi : ∀ k, piece c i ((s ⋙ ObjectProperty.ι (piece c i)).obj k)` using `fun k => (s.obj k).property`. Conclude with `val_congr g (hi 0) (s ⋙ ObjectProperty.ι (piece c i)) _ hi`.
-/
theorem pullC_glue (hc : ∀ {T T' : C}, (T ⟶ T') → c T = c T') {n : ℕ}
    (g : ∀ i, Cn ((ObjectProperty.ι (piece c i)) ⋙ F) n) (i : ι) :
    (res F c i).pullC n (glue hc g) = g i := by
  funext s
  have hi : ∀ k, piece c i ((s ⋙ ObjectProperty.ι (piece c i)).obj k) := fun k => (s.obj k).property
  exact val_congr g (hi 0) (s ⋙ ObjectProperty.ι (piece c i)) _ hi

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem glue_pullC (hc : ∀ {T T' : C}, (T ⟶ T') → c T = c T') {n : ℕ} (f : Cn F n) :
    glue hc (fun i => (res F c i).pullC n f) = f := rfl

/- English proof (translation)
Rewrite using `[← glue_pullC hc f, ← glue_pullC hc f']`. Conclude with `congrArg _ (funext h)`.
-/
theorem cochain_ext (hc : ∀ {T T' : C}, (T ⟶ T') → c T = c T') {n : ℕ} {f f' : Cn F n}
    (h : ∀ i, (res F c i).pullC n f = (res F c i).pullC n f') : f = f' := by
  rw [← glue_pullC hc f, ← glue_pullC hc f']
  exact congrArg _ (funext h)

/- English proof (translation)
Use `cochain_ext hc fun i => ?_` and prove the remaining obligations. Rewrite using `[← Mor.d_pullC, pullC_glue, pullC_glue]`.
-/
theorem d_glue (hc : ∀ {T T' : C}, (T ⟶ T') → c T = c T') {n : ℕ}
    (g : ∀ i, Cn ((ObjectProperty.ι (piece c i)) ⋙ F) n) :
    d F n (glue hc g) = glue hc (fun i => d _ n (g i)) := by
  refine cochain_ext hc fun i => ?_
  rw [← Mor.d_pullC, pullC_glue, pullC_glue]

end GlobalTheory.CompanionTheory.CatPieces

open GlobalTheory.CompanionTheory.CatPieces in

/- English proof (translation)
Establish `hz : ∀ (i : ι) (a : Cn F n), d F n a = 0 → d _ n ((res F c i).pullC n a) = 0` using `fun i a ha => by`. Rewrite using `[Mor.d_pullC, ha, map_zero]`. Establish `hp : ∀ (i : ι) (a : Cn F n) (ha : d F n a = 0), (res F c i).pull n ((cx F).cls a ha) = (cx _).cls ((res F c i).pullC n a) (hz i a ha)` using `fun i a ha => CrystallineSemistableComparison.P.mapH_cls (res F c i).hom n a ha (hz i a ha)`. Prove the components needed by the constructor for the conclusion. Introduce `x y hxy`.

Take `⟨a, ha, rfl⟩` from `(CrystallineSemistableComparison.P.cls_surj (cx F) n).1 x`. Take `⟨b, hb, rfl⟩` from `(CrystallineSemistableComparison.P.cls_surj (cx F) n).1 y`. Establish `hi : ∀ i, (res F c i).pullC n (a - b) ∈ (cx ((ObjectProperty.ι (piece c i)) ⋙ F)).B n` using `fun i => by`. Establish `h1` using `congrFun hxy i`. Express the relevant statement in the definitionally equal form `(res F c i).pull n _ = (res F c i).pull n _ at h1`.

Rewrite `h1` using `[hp i a ha, hp i b hb, (CrystallineSemistableComparison.P.cls_surj _ n).2.2.1]`. Rewrite using `[map_sub]` and apply the resulting hypothesis. Rewrite using `[(CrystallineSemistableComparison.P.cls_surj (cx F) n).2.2.1]`. Consider the cases of `n with`. Consider the case `zero`.

Establish `: a - b = 0` using `cochain_ext hc fun i => by`. Rewrite using `[map_zero]`. Conclude with `hi i`. Rewrite using `[this]`. Conclude with `Submodule.zero_mem _`.

Consider the case `succ n => choose h hh using hi`. Use `⟨glue hc h, ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `d F n (glue hc h) = a - b`. Rewrite using `[d_glue]`. Use `cochain_ext hc fun i => ?_` and prove the remaining obligations.

Rewrite using `[pullC_glue]`. Conclude with `hh i`. Introduce `y choose a ha hy using fun i => (CrystallineSemistableComparison.P.cls_surj (cx ((ObjectProperty.ι (piece c i)) ⋙ F)) n).1 (y i)`. Establish `hg : d F n (glue hc a) = 0`. Rewrite using `[d_glue]`.

Establish `: (fun i => d _ n (a i)) = fun i => (0 : Cn ((ObjectProperty.ι (piece c i)) ⋙ F) (n + 1))`. Use function extensionality and compare the values at `ha`. Rewrite using `[this]`. Conclude with `cochain_ext hc fun i => by rw [pullC_glue, map_zero]`. Use `⟨(cx F).cls _ hg, funext fun i => ?_⟩` and prove the remaining obligations.

Express the relevant statement in the definitionally equal form `(res F c i).pull n _ = _`. Rewrite using `[hp i _ hg, hy i, (CrystallineSemistableComparison.P.cls_surj _ n).2.2.1, pullC_glue, sub_self]`. Conclude with `Submodule.zero_mem _`.
-/
theorem GlobalTheory.CompanionTheory.CatPieces.sigmaH {R : Type} [CommRing R] {C : Type u} [Category.{v} C] (F : C ⥤ ModuleCat.{w} R) {ι : Type t} (c : C → ι) (hc : ∀ {T T' : C}, (T ⟶ T') → c T = c T') (n : ℕ) : Function.Bijective fun (x : H F n) (i : ι) => (Mor.restrict F (ObjectProperty.ι fun T => c T = i)).pull n x := by
  have hz : ∀ (i : ι) (a : Cn F n), d F n a = 0 →
      d _ n ((res F c i).pullC n a) = 0 := fun i a ha => by
    rw [Mor.d_pullC, ha, map_zero]
  have hp : ∀ (i : ι) (a : Cn F n) (ha : d F n a = 0),
      (res F c i).pull n ((cx F).cls a ha) = (cx _).cls ((res F c i).pullC n a) (hz i a ha) :=
    fun i a ha => CrystallineSemistableComparison.P.mapH_cls (res F c i).hom n a ha (hz i a ha)
  constructor
  · intro x y hxy
    obtain ⟨a, ha, rfl⟩ := (CrystallineSemistableComparison.P.cls_surj (cx F) n).1 x
    obtain ⟨b, hb, rfl⟩ := (CrystallineSemistableComparison.P.cls_surj (cx F) n).1 y
    have hi : ∀ i, (res F c i).pullC n (a - b) ∈ (cx ((ObjectProperty.ι (piece c i)) ⋙ F)).B n := fun i => by
      have h1 := congrFun hxy i
      change (res F c i).pull n _ = (res F c i).pull n _ at h1
      rw [hp i a ha, hp i b hb, (CrystallineSemistableComparison.P.cls_surj _ n).2.2.1] at h1
      rwa [map_sub]
    rw [(CrystallineSemistableComparison.P.cls_surj (cx F) n).2.2.1]
    cases n with
    | zero =>
      have : a - b = 0 := cochain_ext hc fun i => by
        rw [map_zero]; exact hi i
      rw [this]; exact Submodule.zero_mem _
    | succ n =>
      choose h hh using hi
      refine ⟨glue hc h, ?_⟩
      change d F n (glue hc h) = a - b
      rw [d_glue]
      refine cochain_ext hc fun i => ?_
      rw [pullC_glue]
      exact hh i
  · intro y
    choose a ha hy using fun i => (CrystallineSemistableComparison.P.cls_surj (cx ((ObjectProperty.ι (piece c i)) ⋙ F)) n).1 (y i)
    have hg : d F n (glue hc a) = 0 := by
      rw [d_glue]
      have : (fun i => d _ n (a i)) = fun i => (0 : Cn ((ObjectProperty.ι (piece c i)) ⋙ F) (n + 1)) :=
        funext ha
      rw [this]
      exact cochain_ext hc fun i => by rw [pullC_glue, map_zero]
    refine ⟨(cx F).cls _ hg, funext fun i => ?_⟩
    change (res F c i).pull n _ = _
    rw [hp i _ hg, hy i, (CrystallineSemistableComparison.P.cls_surj _ n).2.2.1, pullC_glue, sub_self]
    exact Submodule.zero_mem _
